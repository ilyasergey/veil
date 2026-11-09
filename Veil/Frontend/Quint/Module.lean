module

public meta import Veil.Frontend.Quint.Elab
public import Veil.Frontend.Quint.Prelude

/-!
# The `module M { ... }` command

See `Veil.Frontend.Quint.Elab` for the translation of declarations and expressions. This file
assembles a module: it expands imports, sorts definitions by dependency, and emits the Lean and
Veil commands.
-/

public meta section

namespace Veil.Quint
open Lean Elab Command Term Meta _root_.Lean.Parser

/-! ## Imports -/

/-- A declaration of the module being elaborated, after expanding imports. -/
structure Item where
  decl : Syntax
  /-- constants of the imported module replaced by expressions (`import M(c = e)`) -/
  subst : Std.HashMap String Syntax := {}
  /-- `import M as I`: prefix for the top-level names of `M` -/
  pfx? : Option String := none

/-- Top-level names declared by a list of declarations. -/
def declNames (decls : Array Syntax) : Std.HashSet String :=
  decls.foldl (fun acc dcl =>
    if dcl.isOfKind ``quintConst || dcl.isOfKind ``quintVar then acc.insert (qualIdParts dcl[1]).1
    else if dcl.isOfKind ``quintOper then acc.insert (parseOperDef dcl[0]).name
    else acc) {}

/-- Rename top-level names `x` to `I::x` (for `import M as I`). -/
partial def renameNames (names : Std.HashSet String) (pfx : String) (stx : Syntax) : Syntax :=
  if stx.isOfKind ``quintQualId then
    let (n, fields) := qualIdParts stx
    let base := if n.endsWith "'" then (n.dropEnd 1).toString else n
    if names.contains base && !n.contains ':' then
      let lastName := (Name.mkSimple n).appendCore
        (fields.foldl (fun acc f => Name.mkStr acc f) .anonymous)
      let lastId := mkIdentFrom stx lastName
      let sep := mkAtomFrom stx "::"
      Syntax.node .none ``quintQualId #[mkIdentFrom stx (Name.mkSimple pfx),
        mkNullNode #[Syntax.node .none groupKind #[sep, lastId]]]
    else stx
  else match stx with
    | .node info k args => .node info k (args.map (renameNames names pfx))
    | s => s

/-- Expand the imports of a module into the declarations they bring in. -/
partial def expandImports (decls : Array Syntax) (depth : Nat := 0) : CommandElabM (Array Item) := do
  if depth > 16 then throwError "imports nested too deeply"
  let mods := quintModuleExt.getState (← getEnv)
  let mut out : Array Item := #[]
  for dcl in decls do
    if dcl.isOfKind ``quintImport then
      -- `import M.*`, `import M.name`, `import M as I`
      let tgt := dcl[1]
      let qual := if tgt[0].isOfKind ``quintQualId then tgt[0] else tgt
      let (mname, fields) := qualIdParts qual
      let some mstx := mods.find? (Name.mkSimple mname)
        | throwErrorAt dcl "unknown Quint module `{mname}` (is it imported in Lean?)"
      let inner ← expandImports mstx[3].getArgs (depth + 1)
      let pfx? : Option String :=
        if dcl[2].getNumArgs > 0 then some (qualIdParts dcl[2][1]).1
        else if fields.isEmpty && !tgt[0].isOfKind ``quintQualId then some mname
        else none
      match pfx? with
      | some p =>
        let names := declNames (inner.map (·.decl))
        out := out ++ inner.map fun it => { it with decl := renameNames names p it.decl, pfx? := some p }
      | none => out := out ++ inner
    else if dcl.isOfKind ``quintInstance then
      -- `import M(c = e, ...).*` or `... as I`
      let (mname, _) := qualIdParts dcl[1]
      let some mstx := mods.find? (Name.mkSimple mname)
        | throwErrorAt dcl "unknown Quint module `{mname}` (is it imported in Lean?)"
      let inner ← expandImports mstx[3].getArgs (depth + 1)
      let mut subst : Std.HashMap String Syntax := {}
      for a in dcl[3].getSepArgs do
        subst := subst.insert (a[0].getId.toString (escape := false)) a[2]
      let asPart := dcl[5]
      let pfx? : Option String :=
        if asPart.getNumArgs == 2 && !asPart[0].isAtom then some (qualIdParts asPart[1]).1
        else if asPart.getNumArgs == 2 && asPart[0].isIdent then some (qualIdParts asPart[1]).1
        else none
      let pfx? := pfx?.filter (fun _ => !(asPart[0].isAtom && asPart[0].getAtomVal == "."))
      match pfx? with
      | some p =>
        let names := declNames (inner.map (·.decl))
        out := out ++ inner.map fun it =>
          { it with decl := renameNames names p it.decl, subst := it.subst.union subst, pfx? := some p }
      | none => out := out ++ inner.map fun it => { it with subst := it.subst.union subst }
    else if dcl.isOfKind ``quintExport then
      continue
    else
      out := out.push { decl := dcl }
  return out

/-! ## Collecting declarations -/

structure TypeDecl where
  name : String
  params : Array String
  /-- `none` for a sum type -/
  aliasTy : Option Syntax
  variants : Array (String × Option Syntax)
  ref : Syntax

structure Collected where
  mod : ModInfo
  typeDecls : Array TypeDecl := #[]
  defOrder : Array String := #[]
  assumes : Array (String × Syntax) := #[]
  constOrder : Array String := #[]

/-- Choose the alternative of an ambiguous `type T = ...` declaration. -/
def pickTypeDecl (dcl : Syntax) : Syntax :=
  if dcl.isOfKind choiceKind then
    let aliasTy := dcl.getArgs.find? (·.isOfKind ``quintTypeAlias)
    let sum? := dcl.getArgs.find? (·.isOfKind ``quintTypeSum)
    match aliasTy, sum? with
    | some a, some s =>
      -- a sum type needs `|`, two variants, or an argument
      let sd := s[3]
      let variants := #[sd[1]] ++ (sd[2].getArgs.filter (fun g => !g.isAtom) |>.map fun g => g[1])
      if sd[0].getNumArgs > 0 || variants.size > 1 || variants.any (fun v => v[1].getNumArgs > 0)
      then s else a
    | some a, none => a
    | none, some s => s
    | none, none => dcl[0]
  else dcl

def collect (modName : Name) (items : Array Item) : CommandElabM Collected := do
  let mut c : Collected := { mod := { name := modName } }
  for it in items do
    let dcl := pickTypeDecl it.decl
    if dcl.isOfKind ``quintConst then
      let (n, _) := qualIdParts dcl[1]
      if let some e := it.subst[n]? then
        -- `c = c`: the importing module defines `c`
        let same := match asQualId? e with
          | some q => (qualIdParts q).1 == n
          | none => false
        unless same do
          let qd : QDef := { kind := .pureVal, name := n, params := none, retType? := some dcl[3],
                             body := e, ref := dcl }
          c := { c with mod := { c.mod with defs := c.mod.defs.insert n qd },
                        defOrder := c.defOrder.push n }
      else
        c := { c with mod := { c.mod with consts := c.mod.consts.insert n dcl[3] },
                      constOrder := c.constOrder.push n }
    else if dcl.isOfKind ``quintVar then
      let (n, _) := qualIdParts dcl[1]
      c := { c with mod := { c.mod with vars := c.mod.vars.insert n dcl[3],
                                        varOrder := c.mod.varOrder.push n } }
    else if dcl.isOfKind ``quintAssume then
      c := { c with assumes := c.assumes.push (paramName dcl[1], dcl[3]) }
    else if dcl.isOfKind ``quintTypeAbstract then
      throwErrorAt dcl "uninterpreted types are not supported yet"
    else if dcl.isOfKind ``quintTypeAlias || dcl.isOfKind ``quintTypeSum then
      let head := dcl[1]
      let (n, _) := qualIdParts head[0]
      let params := if head[1].getNumArgs > 0 then
          (head[1][1].getSepArgs.map (·.getId.toString (escape := false))) else #[]
      if dcl.isOfKind ``quintTypeAlias then
        let td : TypeDecl := { name := n, params, aliasTy := Option.some (dcl[3]), variants := #[], ref := dcl }
        c := { c with typeDecls := c.typeDecls.push td }
      else
        let sd := dcl[3]
        let vs := #[sd[1]] ++ (sd[2].getArgs.map fun g => g[1])
        let variants := vs.map fun v =>
          (v[0].getId.toString (escape := false), if v[1].getNumArgs > 0 then some v[1][1] else none)
        c := { c with typeDecls := c.typeDecls.push { name := n, params, aliasTy := none, variants, ref := dcl } }
      c := { c with mod := { c.mod with types := c.mod.types.insert n (Name.mkSimple (typeLeanStr n)),
                                        typeParams := c.mod.typeParams.insert n params } }
    else if dcl.isOfKind ``quintOper then
      let qd := parseOperDef dcl[0]
      c := { c with mod := { c.mod with defs := c.mod.defs.insert qd.name qd },
                    defOrder := c.defOrder.push qd.name }
    else if dcl.isOfKind ``quintValDestr then
      throwErrorAt dcl "top-level destructuring `val` is not supported"
    else
      throwErrorAt dcl "unsupported Quint declaration"
  -- constructors and record fields
  let mut ctors : Std.HashMap String SumInfo := {}
  for td in c.typeDecls do
    if td.aliasTy.isNone then
      let tn := Name.mkSimple (typeLeanStr td.name)
      for (v, arg?) in td.variants do
        ctors := ctors.insert v { typeName := tn, ctorName := tn ++ Name.mkSimple v, hasArg := arg?.isSome }
  c := { c with mod := { c.mod with ctors := ctors } }
  return c

/-! ## Dependencies -/

/-- Names (Quint, unqualified heads) referenced in a syntax tree. -/
partial def referencedNames (stx : Syntax) (acc : Std.HashSet String := {}) : Std.HashSet String :=
  if stx.isOfKind ``quintQualId then
    let (n, fs) := qualIdParts stx
    let acc := acc.insert (if n.endsWith "'" then (n.dropEnd 1).toString else n)
    -- `x.f(...)` may call a user operator `f`
    fs.foldl (fun acc f => acc.insert f) acc
  else if stx.isIdent then acc.insert (stx.getId.toString (escape := false))
  else stx.getArgs.foldl (fun acc a => referencedNames a acc) acc

def defDeps (mod : ModInfo) (dcl : QDef) : Array String :=
  let refs := referencedNames dcl.body
  let refs := match dcl.retType? with | some t => referencedNames t refs | none => refs
  refs.toArray.filter fun r => r != dcl.name && mod.defs.contains r

/-- Topological order of the definitions (dependencies first), stable w.r.t. `order`. -/
partial def topoSort (mod : ModInfo) (order : Array String) : Array String := Id.run do
  let mut visited : Std.HashSet String := {}
  let mut out : Array String := #[]
  let rec visit (n : String) (visited : Std.HashSet String) (out : Array String) (fuel : Nat) :
      Std.HashSet String × Array String :=
    if visited.contains n || fuel == 0 then (visited, out) else
    let visited := visited.insert n
    match mod.defs[n]? with
    | none => (visited, out)
    | some dcl =>
      let (visited, out) := (defDeps mod dcl).foldl (fun (v, o) m => visit m v o (fuel - 1)) (visited, out)
      (visited, out.push n)
  for n in order do
    (visited, out) := visit n visited out 10000
  return out

/-- Whether a definition (transitively) depends on state variables or constants. -/
partial def dependsOnState (mod : ModInfo) (n : String) (visiting : Std.HashSet String := {}) : Bool :=
  if visiting.contains n then false else
  match mod.defs[n]? with
  | none => false
  | some dcl =>
    let refs := referencedNames dcl.body
    refs.toList.any fun r =>
      (mod.vars.contains r || mod.consts.contains r) &&
        !(dcl.params.getD #[]).any (·.name == r)
      || (mod.defs.contains r && dependsOnState mod r (visiting.insert n))

/-- A syntactic guess whether an expression is boolean. -/
partial def looksBoolean (mod : ModInfo) (stx : Syntax) : Bool :=
  let s := unwrap stx
  if isApp s then
    match asQualId? s[0] with
    | some q =>
      let (n, fs) := qualIdParts q
      let m := fs.getLast?.getD n
      ["forall", "exists", "contains", "in", "subseteq", "not", "and", "or", "iff", "implies",
       "isFinite", "eq", "neq", "assert"].contains m ||
      (fs.isEmpty && ((mod.defs[n]?.map fun dcl => dcl.retType?.any isBoolType).getD false))
    | none =>
      match dot? s[0] with
      | some (_, f) =>
        ["forall", "exists", "contains", "in", "subseteq", "not", "and", "or", "iff", "implies",
         "isFinite", "eq", "neq"].contains f
      | none => false
  else match s with
  | `(quint_expr| $_ == $_) | `(quint_expr| $_ != $_) | `(quint_expr| $_ < $_)
  | `(quint_expr| $_ <= $_) | `(quint_expr| $_ > $_) | `(quint_expr| $_ >= $_)
  | `(quint_expr| $_ and $_) | `(quint_expr| $_ or $_) | `(quint_expr| $_ iff $_)
  | `(quint_expr| $_ implies $_) | `(quint_expr| and { $_,* }) | `(quint_expr| or { $_,* }) => true
  | `(quint_expr| if ($_) $a else $b) => looksBoolean mod a && looksBoolean mod b
  | `(quint_expr| $_:quintOperDef $b) => looksBoolean mod b
  | `(quint_expr| $_:quintValTuple $b) => looksBoolean mod b
  | `(quint_expr| $q:quintQualId) =>
    let (n, fs) := qualIdParts q
    fs.isEmpty && (n == "true" || n == "false" ||
      (mod.defs[n]?.map fun dcl => dcl.retType?.any isBoolType || looksBoolean mod dcl.body).getD false)
  | _ => false
where
  isBoolType (t : Syntax) : Bool :=
    match t with
    | `(quint_type| $q:quintQualId) => (qualIdParts q).1 == "bool"
    | _ => false

/-! ## Emitting declarations -/

def instBinders (tv : String) : CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  let a := mkIdent (Name.mkSimple tv)
  return #[← `(bracketedBinder| {$a : Type}), ← `(bracketedBinder| [Ord $a]),
    ← `(bracketedBinder| [Std.TransOrd $a]), ← `(bracketedBinder| [Std.LawfulEqOrd $a]),
    ← `(bracketedBinder| [Inhabited $a]), ← `(bracketedBinder| [DecidableEq $a]),
    ← `(bracketedBinder| [Hashable $a]), ← `(bracketedBinder| [Repr $a])]

def runTr (mod : ModInfo) (x : TrM α) (tyVars : Std.HashSet String := {}) : CommandElabM α := do
  let (r, _) ← (x.run { mod, tyVars }).run 0
  return r

/-- Record field sets used anywhere in the declarations (types and literals). -/
partial def recordFieldSets (stx : Syntax) (acc : Array (Array String) := #[]) : Array (Array String) :=
  let acc := match stx with
    | `(quint_type| { $fs,* }) =>
      acc.push (fs.getElems.map fun f => f.raw[0].getId.toString (escape := false))
    | `(quint_expr| { $fs:quintRecElem,* }) =>
      let elems := fs.getElems.map (·.raw)
      let isSpread := elems.any fun e =>
        (e.getNumArgs == 2 && e[0].isAtom) || (e.getNumArgs == 1 && e[0].getNumArgs == 2 && e[0][0].isAtom)
      if isSpread then acc
      else acc.push (elems.map fun e =>
        let e' := if e.getNumArgs == 1 then e[0] else e
        e'[0].getId.toString (escape := false))
    | _ => acc
  stx.getArgs.foldl (fun acc a => recordFieldSets a acc) acc

def elabTypeDecl (mod : ModInfo) (td : TypeDecl) : CommandElabM Unit := withRef td.ref do
  let name := mkIdent (Name.mkSimple (typeLeanStr td.name))
  let ps := td.params.map fun p => mkIdent (Name.mkSimple p)
  let tyVars := td.params.foldl (·.insert ·) {}
  match td.aliasTy with
  | some t =>
    let t' ← runTr mod (trType t) tyVars
    elabCommand (← `(abbrev $name $[($ps : Type)]* := $t'))
  | none =>
    let ctors ← td.variants.mapM fun (v, arg?) => do
      let cid := mkIdent (Name.mkSimple v)
      match arg? with
      | some t =>
        let t' ← runTr mod (trType t) tyVars
        `(Lean.Parser.Command.ctor| | $cid:ident (value : $t'))
      | none => `(Lean.Parser.Command.ctor| | $cid:ident)
    elabCommand (← `(@[veil_decl] inductive $name $[($ps : Type)]* where $ctors:ctor*))

/-- Elaborate a pure definition as a Lean `def`. -/
def elabPureDef (mod : ModInfo) (qd : QDef) : CommandElabM Unit := withRef qd.ref do
  let name := mkId qd.name
  let ps := qd.params.getD #[]
  let tyVars : Std.HashSet String := ps.foldl (fun acc p =>
      match p.type? with | some t => acc.union (typeVarsOf mod t) | none => acc)
    (match qd.retType? with | some t => typeVarsOf mod t | none => {})
  let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for tv in tyVars.toArray.qsort (· < ·) do binders := binders ++ (← instBinders tv)
  let mut locals : Std.HashMap String Ident := {}
  for p in ps do
    let some t := p.type? | throwError "unannotated parameter"
    let t' ← runTr mod (trType t) tyVars
    let pid := if p.name == "_" then mkIdent `_x else mkId p.name
    binders := binders.push (← `(bracketedBinder| ($pid : $t')))
    locals := locals.insert p.name pid
  let (body, _) ← ((trExpr qd.body).run { mod, tyVars, locals }).run 0
  let isBool := match qd.retType? with
    | some t => match t with
      | `(quint_type| $q:quintQualId) => (qualIdParts q).1 == "bool"
      | _ => false
    | none => false
  let retTy? ← if isBool then some <$> `(Prop) else
    match qd.retType? with
    | some t => some <$> runTr mod (trType t) tyVars
    | none => pure none
  match retTy? with
  | some rt => elabCommand (← `(@[reducible] def $name $binders* : $rt := $body))
  | none => elabCommand (← `(@[reducible] def $name $binders* := $body))

/-- Elaborate a definition that reads the state or the constants as a Veil ghost definition. -/
def elabGhostDef (mod : ModInfo) (qd : QDef) (isRel : Bool) : CommandElabM Unit := withRef qd.ref do
  let name := mkId qd.name
  let ps := qd.params.getD #[]
  let mut binders : Array (TSyntax ``Lean.explicitBinders) := #[]
  let mut bs : Array (TSyntax ``Lean.bracketedExplicitBinders) := #[]
  let mut locals : Std.HashMap String Ident := {}
  for p in ps do
    let some t := p.type? | throwError "unannotated parameter"
    let t' ← runTr mod (trType t)
    let pid := if p.name == "_" then mkIdent `_x else mkId p.name
    let pidB : TSyntax `Lean.binderIdent := ⟨pid.raw⟩
    bs := bs.push (← `(Lean.bracketedExplicitBinders| ($pidB : $t')))
    locals := locals.insert p.name pid
  let (body, _) ← ((trExpr qd.body).run { mod, locals }).run 0
  let bindersOpt : Option (TSyntax ``Lean.explicitBinders) ←
    if bs.isEmpty then pure none else some <$> `(Lean.explicitBinders| $bs*)
  let _ := binders
  if isRel then
    elabCommand (← `(command| ghost relation $name $[$bindersOpt]? := $body))
  else
    let retTy? ← match qd.retType? with
      | some t => some <$> runTr mod (trType t)
      | none => pure none
    elabCommand (← `(command| ghost function $name $[$bindersOpt]? $[: $retTy?]? := $body))

/-- Register global copies of the scoped instances that `@[veil_decl]` derives. -/
def globalizeInstances (structName : Name) (nParams : Nat) : CommandElabM Unit := do
  let ps := (List.range nParams).toArray.map fun i => mkIdent (Name.mkSimple s!"α{i}")
  let ty ← `($(mkIdent structName) $ps*)
  let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for p in ps do
    binders := binders ++ #[← `(bracketedBinder| {$p : Type}), ← `(bracketedBinder| [Ord $p]),
      ← `(bracketedBinder| [Std.TransOrd $p]), ← `(bracketedBinder| [Std.LawfulEqOrd $p])]
  elabCommand (← `(instance $binders:bracketedBinder* : Std.TransOrd $ty := inferInstance))
  elabCommand (← `(instance $binders:bracketedBinder* : Std.LawfulEqOrd $ty := inferInstance))

/-- `ensureRecord`, outside of any module namespace. -/
def ensureRecordGlobal (fields : Array String) : CommandElabM Unit := do
  let fields := fields.qsort (· < ·)
  let key := recordKey fields
  if (quintRecordExt.getState (← getEnv)).contains key then return
  let name := recordStructName fields
  if (← getEnv).contains name then
    modifyEnv (quintRecordExt.addEntry · (key, name)); return
  withScope (fun sc => { sc with currNamespace := `QuintRecords }) do
    let tyParams := (List.range fields.size).toArray.map fun i => mkIdent (Name.mkSimple s!"α{i}")
    let fieldDecls ← fields.mapIdxM fun i f => do
      let fid := mkIdent (Name.mkSimple f)
      let ty := tyParams[i]!
      `(Lean.Parser.Command.structExplicitBinder| ($fid : $ty))
    let shortName := mkIdent (Name.mkSimple name.getString!)
    elabCommand (← `(@[veil_decl] structure $shortName $[($tyParams : Type)]* where
      $[$fieldDecls]*))
    globalizeInstances name fields.size
  modifyEnv (quintRecordExt.addEntry · (key, name))

/-! ## The module command -/

def elabQuintModuleCore (stx : Syntax) : CommandElabM Unit := do
  let (modStr, _) := qualIdParts stx[1]
  let modName := Name.mkSimple (leanStr modStr)
  modifyEnv (quintModuleExt.addEntry · (Name.mkSimple modStr, stx))
  let items ← expandImports stx[3].getArgs
  let c ← collect modName items
  let mut mod := c.mod
  -- a module whose constants are not all instantiated and that has no state is a library
  -- that is only used through `import`
  if mod.vars.isEmpty && !mod.consts.isEmpty then
    logInfo m!"Quint module `{modStr}` has constants and no state; it is elaborated where it is imported."
    return
  -- record structures
  for it in items do
    for fs in recordFieldSets it.decl do ensureRecordGlobal fs
  for f in (items.foldl (fun acc it => acc ++ recordFieldSets it.decl) #[]).flatten do
    mod := { mod with recordFields := mod.recordFields.insert f }
  let isVeil := !mod.vars.isEmpty
  mod := { mod with isVeil }
  let modId := mkIdent modName
  if isVeil then
    elabCommand (← `(veil module $modId))
  else
    elabCommand (← `(namespace $modId))
  -- types
  for td in c.typeDecls do elabTypeDecl mod td
  -- classify definitions
  let initName := quint.init.get (← getOptions)
  let stepName := quint.step.get (← getOptions)
  let order := topoSort mod c.defOrder
  let mut pureDefs : Array QDef := #[]
  let mut ghostDefs : Array (QDef × Bool) := #[]
  let mut invCandidates : Array QDef := #[]
  for n in order do
    let some qd := mod.defs[n]? | continue
    match qd.kind with
    | .action | .temporal | .run | .nondet => continue
    | _ => pure ()
    let ps := qd.params.getD #[]
    let annotated := ps.all (·.type?.isSome)
    let stateful := dependsOnState mod n
    let isBool := looksBoolean mod qd.body ||
      (qd.retType?.any fun t => match t with
        | `(quint_type| $q:quintQualId) => (qualIdParts q).1 == "bool"
        | _ => false)
    if !annotated then
      continue -- inlined
    if !stateful then
      pureDefs := pureDefs.push qd
      mod := { mod with defRepr := mod.defRepr.insert n (.named (mkId n)) }
    else if !isVeil then
      continue
    else if ps.isEmpty && isBool then
      invCandidates := invCandidates.push qd -- inlined, and available to `quint_invariant`
    else
      let tvs := ps.foldl (fun (acc : Std.HashSet String) p => match p.type? with
        | some t => acc.union (typeVarsOf mod t) | none => acc) {}
      if !tvs.isEmpty then continue
      ghostDefs := ghostDefs.push (qd, isBool)
      mod := { mod with defRepr := mod.defRepr.insert n (.named (mkId n)) }
  -- pure definitions; a definition that fails to elaborate is inlined instead
  for qd in pureDefs do
    try elabPureDef mod qd
    catch ex =>
      logWarning m!"`{qd.name}` is inlined: {ex.toMessageData}"
      mod := { mod with defRepr := mod.defRepr.erase qd.name }
  if !isVeil then
    elabCommand (← `(end $modId))
    return
  -- parameters and state
  for n in c.constOrder do
    let some t := mod.consts[n]? | continue
    let t' ← runTr mod (trType t)
    elabCommand (← `(command| param $(mkId n) : $t'))
  for n in mod.varOrder do
    let some t := mod.vars[n]? | continue
    let t' ← runTr mod (trType t)
    elabCommand (← `(command| individual $(mkId n) : $t'))
  elabCommand (← `(command| #gen_state))
  -- ghost definitions
  for (qd, isRel) in ghostDefs do
    try elabGhostDef mod qd isRel
    catch ex =>
      logWarning m!"`{qd.name}` is inlined: {ex.toMessageData}"
      mod := { mod with defRepr := mod.defRepr.erase qd.name }
  -- assumptions
  for (n, e) in c.assumes do
    if mod.consts.isEmpty then continue
    let t ← runTr mod (trExpr e)
    let nid := mkIdent (Name.mkSimple (if n == "_" then "assumption" else leanStr n))
    elabCommand (← `(command| assumption [$nid] $t))
  -- initial states and transitions
  if let some initDef := mod.defs[initName]? then
    let body ← runTr mod (trTopAction initDef.body)
    withRef initDef.ref <| elabCommand (← `(command| after_init { $body }))
  if let some stepDef := mod.defs[stepName]? then
    let branches := splitBranches mod stepDef.body
    let mut used : Std.HashMap String Nat := {}
    let mut idx := 0
    for b in branches do
      idx := idx + 1
      let base := if b.name.isEmpty || b.name == stepName then s!"{stepName}_{idx}" else b.name
      let cnt := used.getD base 0
      used := used.insert base (cnt + 1)
      let nm := if cnt == 0 then base else s!"{base}_{cnt + 1}"
      let body ← runTr mod (trTopBranch b)
      withRef stepDef.ref <| elabCommand (← `(command| action $(mkId nm) { $body }))
  -- candidate invariants
  let mut cands : Std.HashMap (Name × String) Syntax := quintInvCandidateExt.getState (← getEnv)
  for qd in mod.defs.values do
    if qd.kind == .action || qd.kind == .run || qd.kind == .temporal then continue
    if (qd.params.getD #[]).isEmpty && (looksBoolean mod qd.body ||
        qd.retType?.any fun t => match t with
          | `(quint_type| $q:quintQualId) => (qualIdParts q).1 == "bool"
          | _ => false) then
      try
        let t ← runTr mod (trExpr qd.body)
        cands := cands.insert (modName, qd.name) t
      catch ex => logWarningAt qd.ref m!"`{qd.name}` cannot be used as an invariant: {ex.toMessageData}"
  let _ := invCandidates
  modifyEnv (quintInvCandidateExt.setState · cands)
  for qd in mod.defs.values do
    trace[veil.debug] m!"def {qd.name}: kind {repr qd.kind}, params {qd.params.map (·.size)}, bool {looksBoolean mod qd.body}, body kind {(unwrap qd.body).getKind} / {(unwrap qd.body)[0].getKind}"

@[command_elab quintModule] def elabQuintModule : CommandElab := fun stx =>
  elabQuintModuleCore stx

/-- `quint_invariant inv_1, ..., inv_n` declares the boolean `val`s `inv_i` of the Quint module
elaborated last as Veil invariants (`invariant [inv_i] ...`). -/
syntax (name := quintInvariantCmd) "quint_invariant " ident,+ : command

@[command_elab quintInvariantCmd] def elabQuintInvariant : CommandElab := fun stx => do
  let cands := quintInvCandidateExt.getState (← getEnv)
  let modName ← getCurrNamespace
  for id in stx[1].getSepArgs do
    let n := id.getId.toString (escape := false)
    let some t := cands[(modName, n)]?
      | throwErrorAt id "`{n}` is not a boolean `val` of the Quint module `{modName}`"
    let t : Term := ⟨t⟩
    let nid := mkIdentFrom id (Name.mkSimple (leanStr n))
    withRef id <| elabCommand (← `(command| invariant [$nid] $t))

end Veil.Quint
