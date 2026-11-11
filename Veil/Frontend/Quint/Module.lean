module

public meta import Veil.Frontend.Quint.Elab
public meta import Veil.Frontend.Quint.Report
public meta import Veil.Frontend.DSL.Infra.TraceSyntax
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

/-- Top-level names declared by a list of declarations. -/
def declNames (decls : Array Syntax) : Std.HashSet String :=
  decls.foldl (fun acc dcl =>
    -- an ambiguous `type T = U` is an alias (see `pickTypeDecl`)
    let alts := #[pickTypeDecl dcl]
    alts.foldl (fun acc dcl =>
      if dcl.isOfKind ``quintConst || dcl.isOfKind ``quintVar then acc.insert (qualIdParts dcl[1]).1
      else if dcl.isOfKind ``quintOper then acc.insert (parseOperDef dcl[0]).name
      else if dcl.isOfKind ``quintTypeAlias then acc.insert (qualIdParts dcl[1][0]).1
      else if dcl.isOfKind ``quintTypeSum then
        -- the type and its constructors
        let sd := dcl[3]
        let vs := #[sd[1]] ++ (sd[2].getArgs.map fun g => g[1])
        vs.foldl (fun acc v => acc.insert (identStr v[0])) (acc.insert (qualIdParts dcl[1][0]).1)
      else acc) acc) {}

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

/-- The prefix `I` of an `as I` clause among the children of `stx`, if any. -/
def asPrefix? (stx : Syntax) : Option String :=
  (stx.getArgs.find? (·.isOfKind ``quintQualId)).map (qualIdParts · |>.1)

/-- Expand the imports of a module into the declarations they bring in. -/
partial def expandImports (decls : Array Syntax) (depth : Nat := 0) : CommandElabM (Array Item) := do
  if depth > 16 then throwError "imports nested too deeply"
  let mods := quintModuleExt.getState (← getEnv)
  -- `export I.*` makes the names of `import ... as I` available without the prefix
  let exported : Std.HashSet String := decls.foldl (fun acc dcl =>
    if dcl.isOfKind ``quintExport then
      let tgt := dcl[1][0]
      let qual := if tgt.isOfKind ``quintQualId then tgt else tgt[0]
      acc.insert (qualIdParts qual).1
    else acc) {}
  let mut out : Array Item := #[]
  for dcl in decls do
    if dcl.isOfKind ``quintImport then
      -- `import M.*`, `import M.name`, `import M`, `import M as I`
      let tgt := dcl[1][0]
      let star := !tgt.isOfKind ``quintQualId
      let qual := if star then tgt[0] else tgt
      let (mname, fields) := qualIdParts qual
      let some mstx := mods.find? (Name.mkSimple mname)
        | throwErrorAt dcl "unknown Quint module `{mname}` (is it imported in Lean, and defined before?)"
      let inner ← expandImports mstx[3].getArgs (depth + 1)
      let pfx? : Option String :=
        match asPrefix? dcl[2] with
        | some p => some p
        | none => if !star && fields.isEmpty then some mname else none
      let pfx? := pfx?.filter (!exported.contains ·)
      match pfx? with
      | some p =>
        let names := declNames (inner.map (·.decl))
        out := out ++ inner.map fun it =>
          { it with decl := renameNames names p it.decl, pfx? := it.pfx?.orElse fun _ => some p }
      | none => out := out ++ inner
    else if dcl.isOfKind ``quintInstance then
      -- `import M(c = e, ...).*` or `... as I`
      let (mname, _) := qualIdParts dcl[1]
      let some mstx := mods.find? (Name.mkSimple mname)
        | throwErrorAt dcl "unknown Quint module `{mname}` (is it imported in Lean, and defined before?)"
      let inner ← expandImports mstx[3].getArgs (depth + 1)
      let mut subst : Std.HashMap String Syntax := {}
      for a in dcl[3].getSepArgs do
        subst := subst.insert (identStr a[0]) a[2]
      match (asPrefix? dcl[5]).filter (!exported.contains ·) with
      | some p =>
        let names := declNames (inner.map (·.decl))
        -- the substituted expressions refer to the importing module: do not rename them
        out := out ++ inner.map fun it =>
          { it with decl := renameNames names p it.decl, subst := it.subst.union subst,
                    pfx? := it.pfx?.orElse fun _ => some p }
      | none => out := out ++ inner.map fun it => { it with subst := it.subst.union subst }
    else if dcl.isOfKind ``quintExport then
      continue
    else
      out := out.push { decl := dcl }
  return out

/-! ## Collecting declarations -/

structure TypeDecl where
  /-- the prefix of the `import ... as I` that brought the type in, if any -/
  pfx? : Option String := none
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

/-- Names (Quint, unqualified heads) referenced in a syntax tree. -/
partial def referencedNames (stx : Syntax) (acc : Std.HashSet String := {}) : Std.HashSet String :=
  if stx.isOfKind ``quintQualId then
    let (n, fs) := qualIdParts stx
    let acc := acc.insert (if n.endsWith "'" then (n.dropEnd 1).toString else n)
    -- `x.f(...)` may call a user operator `f`
    fs.foldl (fun acc f => acc.insert f) acc
  else if stx.isIdent then acc.insert (stx.getId.toString (escape := false))
  else stx.getArgs.foldl (fun acc a => referencedNames a acc) acc

/-- Whether a syntax tree assigns a variable (`x' = e`). -/
partial def assignsVars (stx : Syntax) : Bool :=
  if stx.isOfKind ``quintQualId then (qualIdParts stx).1.endsWith "'"
  else stx.getArgs.any assignsVars

def collect (modName : Name) (items : Array Item) : CommandElabM Collected := do
  let mut c : Collected := { mod := { name := modName } }
  for it in items do
    let dcl := pickTypeDecl it.decl
    -- the name of a declaration of an `import M(...) as I` instance, without the `I::` prefix
    let unpfx (n : String) : String :=
      match it.pfx? with
      | some p => if n.startsWith (p ++ "::") then (n.drop (p.length + 2)).toString else n
      | none => n
    if dcl.isOfKind ``quintConst then
      let (n, _) := qualIdParts dcl[1]
      if let some e := it.subst[unpfx n]? then
        -- `c = c` without a prefix: the importing module defines `c`
        let same := it.pfx?.isNone && match asQualId? e with
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
      -- a module imported along two paths declares its variables once
      if c.mod.vars.contains n then continue
      c := { c with mod := { c.mod with vars := c.mod.vars.insert n dcl[3],
                                        varOrder := c.mod.varOrder.push n } }
    else if dcl.isOfKind ``quintAssume then
      c := { c with assumes := c.assumes.push (paramName dcl[1], dcl[3]) }
    else if dcl.isOfKind ``quintTypeAbstract then
      throwErrorAt dcl "uninterpreted types are not supported yet"
    else if dcl.isOfKind ``quintTypeAlias || dcl.isOfKind ``quintTypeSum then
      let head := dcl[1]
      let (n, _) := qualIdParts head[0]
      -- a type imported twice (e.g. through two instances) is declared once
      if c.typeDecls.any (·.name == n) then continue
      let params := if head[1].getNumArgs > 0 then
          (head[1][1].getSepArgs.map identStr) else #[]
      if dcl.isOfKind ``quintTypeAlias then
        let td : TypeDecl := { name := n, params, aliasTy := Option.some (dcl[3]), variants := #[],
                               ref := dcl, pfx? := it.pfx? }
        c := { c with typeDecls := c.typeDecls.push td }
      else
        let sd := dcl[3]
        let vs := #[sd[1]] ++ (sd[2].getArgs.map fun g => g[1])
        let variants := vs.map fun v =>
          (identStr v[0], if v[1].getNumArgs > 0 then some v[1][1] else none)
        let td : TypeDecl := { name := n, params, aliasTy := none, variants, ref := dcl, pfx? := it.pfx? }
        c := { c with typeDecls := c.typeDecls.push td }
      c := { c with mod := { c.mod with types := c.mod.types.insert n (Name.mkSimple (typeLeanStr n)),
                                        typeParams := c.mod.typeParams.insert n params } }
    else if dcl.isOfKind ``quintOper then
      let qd := parseOperDef dcl[0]
      if c.mod.defs.contains qd.name then continue
      -- an instance may also replace a parameterless `val` (an extension of Quint, used to
      -- bound sets like `val Ballot = Nat` in copies for model checking)
      let qd := match it.subst[unpfx qd.name]? with
        | some e => if (qd.params.getD #[]).isEmpty && (qd.kind == .val || qd.kind == .pureVal) then
            { qd with body := e } else qd
        | none => qd
      c := { c with mod := { c.mod with defs := c.mod.defs.insert qd.name qd },
                    defOrder := c.defOrder.push qd.name }
    else if dcl.isOfKind ``quintValDestr then
      throwErrorAt dcl "top-level destructuring `val` is not supported"
    else
      throwErrorAt dcl "unsupported Quint declaration"
  -- a `def`/`val` that assigns variables (or calls an action) is an action: Quint infers its
  -- mode, the frontend needs it to inline the definition into actions
  let mut changed := true
  let mut fuel := 20
  while changed && fuel > 0 do
    changed := false
    fuel := fuel - 1
    for (n, qd) in c.mod.defs.toList do
      unless qd.kind == .def_ || qd.kind == .val do continue
      let callsAction := (referencedNames qd.body).toList.any fun r =>
        r != n && (c.mod.defs[r]?.map (·.kind == .action)).getD false
      if assignsVars qd.body || callsAction then
        c := { c with mod := { c.mod with defs := c.mod.defs.insert n { qd with kind := .action } } }
        changed := true
  -- constructors and record fields
  let mut ctors : Std.HashMap String SumInfo := {}
  for td in c.typeDecls do
    if td.aliasTy.isNone then
      let tn := Name.mkSimple (typeLeanStr td.name)
      for (v, arg?) in td.variants do
        let info : SumInfo := { typeName := tn, ctorName := tn ++ Name.mkSimple v, hasArg := arg?.isSome }
        match td.pfx? with
        | some p =>
          -- `I::C`, as the renamed references in the imported module write it
          ctors := ctors.insert (p ++ "::" ++ v) info
          unless ctors.contains v do ctors := ctors.insert v info
        | none => ctors := ctors.insert v info
  c := { c with mod := { c.mod with ctors := ctors } }
  return c

/-! ## Dependencies -/

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

/-- A `run` that asserts facts without executing actions: no assignment, no action call and no
`then`/`reps`/`expect`/`fail`. -/
partial def isPureRun (mod : ModInfo) (stx : Syntax) : Bool :=
  let refs := referencedNames stx
  !refs.toList.any (fun r => ["then", "reps", "expect", "fail", "oneOf"].contains r ||
      (mod.defs[r]?.map (·.kind == .action)).getD false || mod.vars.contains r) &&
    !hasAssignment stx
where
  hasAssignment (s : Syntax) : Bool :=
    match s with
    | `(quint_expr| $_ = $_) => true
    | _ => s.getArgs.any hasAssignment

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
      (fs.isEmpty && ((mod.defs[n]?.map fun dcl =>
        dcl.retType?.any isBoolType || looksBoolean mod dcl.body).getD false))
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
  | `(quint_expr| all { $es,* }) | `(quint_expr| any { $es,* }) =>
    -- `all`/`any` over boolean expressions (not actions)
    es.getElems.all fun e => looksBoolean mod e
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
      acc.push (fs.getElems.map fun f => identStr f.raw[0])
    | `(quint_expr| { $fs:quintRecElem,* }) =>
      let elems := fs.getElems.map (·.raw)
      let isSpread := elems.any fun e =>
        (e.getNumArgs == 2 && e[0].isAtom) || (e.getNumArgs == 1 && e[0].getNumArgs == 2 && e[0][0].isAtom)
      if isSpread then acc
      else acc.push (elems.map fun e =>
        let e' := if e.getNumArgs == 1 then e[0] else e
        identStr e'[0])
    | _ => acc
  stx.getArgs.foldl (fun acc a => recordFieldSets a acc) acc

/-- Type declarations with the types they refer to first. -/
partial def sortTypeDecls (tds : Array TypeDecl) : Array TypeDecl := Id.run do
  let names : Std.HashSet String := tds.foldl (·.insert ·.name) {}
  let deps (td : TypeDecl) : Array String :=
    let refs := match td.aliasTy with
      | some t => referencedNames t
      | none => td.variants.foldl (fun (acc : Std.HashSet String) (v : String × Option Syntax) =>
          match v.2 with
          | some t => referencedNames t acc | none => acc) {}
    refs.toArray.filter fun r => r != td.name && names.contains r
  let mut visited : Std.HashSet String := {}
  let mut out : Array TypeDecl := #[]
  let rec visit (n : String) (visited : Std.HashSet String) (out : Array TypeDecl) (fuel : Nat) :
      Std.HashSet String × Array TypeDecl :=
    if visited.contains n || fuel == 0 then (visited, out) else
    let visited := visited.insert n
    match tds.find? (·.name == n) with
    | none => (visited, out)
    | some td =>
      let (visited, out) := (deps td).foldl (fun (v, o) m => visit m v o (fuel - 1)) (visited, out)
      (visited, out.push td)
  for td in tds do
    (visited, out) := visit td.name visited out 1000
  return out

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
    -- discriminators and projections, used to compile `match` in actions
    let tyApp ← `($name $ps*)
    for (v, arg?) in td.variants do
      let cid := mkIdent (Name.mkSimple (typeLeanStr td.name) ++ Name.mkSimple v)
      let isId := mkIdent (Name.mkSimple (typeLeanStr td.name) ++ Name.mkSimple ("is" ++ v))
      let getId := mkIdent (Name.mkSimple (typeLeanStr td.name) ++ Name.mkSimple ("get" ++ v))
      let binders ← ps.mapM fun p => `(bracketedBinder| {$p : Type})
      match arg? with
      | some t =>
        let t' ← runTr mod (trType t) tyVars
        let instBs ← ps.mapM fun p => `(bracketedBinder| [Inhabited $p])
        elabCommand (← `(@[reducible] def $isId $binders* : $tyApp → Bool
          | $cid:ident _ => true
          | _ => false))
        elabCommand (← `(@[reducible] def $getId $binders* $instBs* : $tyApp → $t'
          | $cid:ident v => v
          | _ => default))
      | none =>
        elabCommand (← `(@[reducible] def $isId $binders* : $tyApp → Bool
          | $cid:ident => true
          | _ => false))

/-- Elaborate a generated command. With `quint.lenient`, errors become a warning that the
declaration is skipped. -/
def elabGenerated (what : String) (cmd : Syntax) : CommandElabM Bool := do
  unless quint.lenient.get (← getOptions) do
    elabCommand cmd
    return true
  let saved := (← get).messages
  modify fun st => { st with messages := {} }
  elabCommand cmd
  let msgs := (← get).messages
  if msgs.hasErrors then
    let errs ← msgs.toList.filter (·.severity == .error) |>.mapM (·.toString)
    modify fun st => { st with messages := saved }
    logWarning m!"{what} is skipped (quint.lenient): {errs.headD ""}"
    return false
  else
    modify fun st => { st with messages := saved ++ msgs }
    return true

/-- Elaborate a pure definition as a Lean `def`. -/
def elabPureDef (mod : ModInfo) (qd : QDef) : CommandElabM Bool := withRef qd.ref do
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
  | some rt => elabGenerated s!"definition `{qd.name}`" (← `(@[reducible] def $name $binders* : $rt := $body))
  | none => elabGenerated s!"definition `{qd.name}`" (← `(@[reducible] def $name $binders* := $body))

/-- Elaborate a definition that reads the state or the constants as a Veil ghost definition. -/
def elabGhostDef (mod : ModInfo) (qd : QDef) (isRel : Bool) : CommandElabM Bool := withRef qd.ref do
  let name := mkId qd.name
  let ps := qd.params.getD #[]
  let mut binders : Array (TSyntax ``Lean.explicitBinders) := #[]
  let mut bs : Array (TSyntax ``Lean.bracketedExplicitBinders) := #[]
  let mut locals : Std.HashMap String Ident := {}
  for p in ps do
    let some t := p.type? | throwError "unannotated parameter"
    let t' ← runTr mod (trType t)
    let pid := if p.name == "_" then mkIdent `_x else mkId p.name
    let pidB ← `(Lean.binderIdent| $pid:ident)
    bs := bs.push (← `(Lean.bracketedExplicitBinders| ($pidB : $t')))
    locals := locals.insert p.name pid
  let (body, _) ← ((trExpr qd.body).run { mod, locals }).run 0
  let bindersOpt : Option (TSyntax ``Lean.explicitBinders) ←
    if bs.isEmpty then pure none else some <$> `(Lean.explicitBinders| $bs*)
  let _ := binders
  if isRel then
    elabGenerated s!"definition `{qd.name}`" (← `(command| ghost relation $name $[$bindersOpt]? := $body))
  else
    let retTy? ← match qd.retType? with
      | some t => some <$> runTr mod (trType t)
      | none => pure none
    elabGenerated s!"definition `{qd.name}`" (← `(command| ghost function $name $[$bindersOpt]? $[: $retTy?]? := $body))

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

/-- Parse and elaborate a command given as a string. -/
def elabCommandString (src : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command src with
  | .ok stx => elabCommand stx
  | .error e => throwError "internal error in generated command: {e}\n{src}"

/-- The commands that declare a record structure with these (sorted) fields: the structure, its
order (by projection to nested pairs, whose lawfulness Lean proves), and a Quint-style `Repr`.
They are generated in the namespace `QuintRecords` and are public. -/
def recordCommands (short : String) (fields : Array String) : Array String :=
  if fields.isEmpty then
    #[s!"public structure {short} where\nderiving Inhabited, DecidableEq, Hashable, Lean.ToJson, Repr",
      s!"public instance : Ord {short} := ⟨fun _ _ => .eq⟩",
      s!"public instance : Std.TransOrd {short} where\n  eq_swap := rfl\n  isLE_trans := fun _ _ => rfl",
      s!"public instance : Std.LawfulEqOrd {short} where\n  compare_self := rfl\n  eq_of_compare := fun _ => rfl"]
  else
  let n := fields.size
  let tvs := (List.range n).toArray.map fun i => s!"α{i}"
  let tvBinders := " ".intercalate (tvs.map fun t => s!"{t}").toList
  let tyApp := s!"{short} {tvBinders}"
  let implicit := "{" ++ tvBinders ++ " : Type}"
  let cls (c : String) := " ".intercalate (tvs.map fun t => s!"[{c} {t}]").toList
  let prodTy := " × ".intercalate tvs.toList
  let prodVal := "(" ++ ", ".intercalate (fields.map fun f => s!"r.«{f}»").toList ++ ")"
  let reprBody := " ++ \", \" ++ ".intercalate (fields.map fun f => s!"\"{f}: \" ++ repr r.«{f}»").toList
  #[s!"public structure {short} ({tvBinders} : Type) where\n" ++
      "\n".intercalate (fields.zip tvs |>.map fun (f, t) => s!"  «{f}» : {t}").toList ++
      "\nderiving Inhabited, DecidableEq, Hashable, Lean.ToJson",
    s!"@[reducible, expose] public def {short}.toProd {implicit} (r : {tyApp}) : {prodTy} := {prodVal}",
    s!"attribute [local instance] lexOrd in\npublic instance {implicit} {cls "Ord"} : Ord ({tyApp}) := ⟨compareOn {short}.toProd⟩",
    s!"attribute [local instance] lexOrd in\npublic instance {implicit} {cls "Ord"} {cls "Std.TransOrd"} : Std.TransOrd ({tyApp}) :=\n  inferInstanceAs (Std.TransCmp (compareOn {short}.toProd))",
    s!"attribute [local instance] lexOrd in\npublic instance {implicit} {cls "Ord"} {cls "Std.LawfulEqOrd"} : Std.LawfulEqOrd ({tyApp}) where\n" ++
      s!"  compare_self := by intro x; exact Std.ReflCmp.compare_self (cmp := compare) (a := x.toProd)\n" ++
      s!"  eq_of_compare := by\n    intro x y h\n    have h' : x.toProd = y.toProd := Std.LawfulEqCmp.eq_of_compare (cmp := compare) h\n    cases x; cases y; simp_all [{short}.toProd]",
    s!"public instance {implicit} {cls "Repr"} : Repr ({tyApp}) where\n  reprPrec r _ := \"\{ \" ++ {reprBody} ++ \" }\"",
    s!"public instance {implicit} : Quint.FieldNames ({tyApp}) := ⟨Quint.Set.ofList [" ++
      ", ".intercalate (fields.map fun f => s!"\"{f}\"").toList ++ "]⟩"]

/-- Declare the record structure for these field names, unless it exists. -/
def ensureRecordGlobal (fields : Array String) : CommandElabM Unit := do
  let fields := fields.qsort (· < ·)
  let key := recordKey fields
  if (quintRecordExt.getState (← getEnv)).contains key then return
  let name := recordStructName fields
  if (← getEnv).contains name then
    modifyEnv (quintRecordExt.addEntry · (key, name)); return
  withScope (fun sc => { sc with currNamespace := `QuintRecords }) do
    for c in recordCommands name.getString! fields do elabCommandString c
  modifyEnv (quintRecordExt.addEntry · (key, name))

/-! ## Temporal properties -/

/-- Names of Quint's temporal operators. -/
def temporalOps : List String :=
  ["always", "eventually", "leadsTo", "weakFair", "strongFair", "enabled", "next", "orKeep",
   "mustChange", "guarantees"]

/-- `f(args)` or `r.f(args)` (the receiver first): the operator and its arguments. -/
def callOf? (stx : Syntax) : Option (String × Array Syntax) :=
  let s := unwrap stx
  if !isApp s then none else
  let args := sepArgs s[2]
  match asQualId? s[0] with
  | some q =>
    let (n, fs) := qualIdParts q
    match fs with
    | [] => some (n, args)
    | [m] => some (m, #[Syntax.node .none `Veil.Quint.quintName #[mkIdent (Name.mkSimple n)]] ++ args)
    | _ => none
  | none =>
    match dot? s[0] with
    | some (e, m) => some (m, #[e] ++ args)
    | none => none

/-- Whether an expression uses a temporal operator (or a temporal definition). -/
partial def isTemporalExpr (mod : ModInfo) (stx : Syntax) : Bool :=
  (stx.find? fun s => s.isAtom && s.getAtomVal.trimAscii.toString == "leadsTo").isSome ||
  (referencedNames stx).toList.any fun r =>
    temporalOps.contains r || (mod.defs[r]?.map (·.kind == .temporal)).getD false

/-- Translate a Quint temporal formula into Lentil's `tlfml`, for `#temporal_check`.
`weakFair(A, vars)` and `strongFair(A, vars)` refer to the Veil actions that implement the Quint
action `A` (`actions`): one action gives `𝒲ℱ a`; several (e.g. `step`, which the frontend splits
into one Veil action per branch) give fairness of their disjunction,
`(◇ □ (Enabled a_1 ∨ …)) → □ ◇ (⟨ a_1 ⟩ ∨ …)` (strong: `□ ◇` instead of `◇ □`). -/
partial def trTemporal (acts : Std.HashMap String (Array String))
    (subs : Array (String × Ident) := #[]) (stx : Syntax) :
    TrM (TSyntax `tlfml) := do
  let mod := (← read).mod
  let s := unwrap stx
  let disj (fs : Array (TSyntax `tlfml)) : TrM (TSyntax `tlfml) := do
    let mut r := fs.back!
    for f in fs.pop.reverse do r ← `(tlfml| $f ∨ $r)
    `(tlfml| ($r))
  let actionsOf (a : Syntax) : TrM (Array Ident) := do
    let uStx := unwrap a
    let (n, fs) ← if uStx.getKind == `Veil.Quint.quintName then
        pure (uStx[0].getId.toString (escape := false), ([] : List String))
      else match asQualId? uStx with
        | some q => pure (qualIdParts q)
        | none => throwErrorAt a "fairness is supported for actions without arguments"
    unless fs.isEmpty do throwErrorAt a "fairness is supported for actions without arguments"
    let some vs := acts[n]? | throwErrorAt a "`{n}` is not an action of the transitions (`step`)"
    return vs.map mkId
  let fair (strong : Bool) (a : Syntax) : TrM (TSyntax `tlfml) := do
    let vs ← actionsOf a
    if h : vs.size = 1 then
      if strong then `(tlfml| 𝒮ℱ $(vs[0])) else `(tlfml| 𝒲ℱ $(vs[0]))
    else
      let en ← disj (← vs.mapM fun a => `(tlfml| Enabled $a))
      let tk ← disj (← vs.mapM fun a => `(tlfml| ⟨ $a ⟩))
      if strong then `(tlfml| ((□ ◇ $en) → □ ◇ $tk)) else `(tlfml| ((◇ □ $en) → □ ◇ $tk))
  if !isTemporalExpr mod s then
    let mut t ← trExpr s
    -- the elements of the sets of enclosing quantifiers (of a subtype) as values of the element type
    let refs := referencedNames s
    for (q, x) in subs.reverse do
      if refs.contains q then t ← `(let $x:ident := ($x:ident).val; $t)
    return ← `(tlfml| ⌜ $t ⌝)
  if let some (op, args) := callOf? s then
    match op, args with
    | "always", #[p] => return ← `(tlfml| □ $(← trTemporal acts subs p))
    | "eventually", #[p] => return ← `(tlfml| ◇ $(← trTemporal acts subs p))
    | "weakFair", #[a, _] => return ← fair false a
    | "strongFair", #[a, _] => return ← fair true a
    | "enabled", #[a] => return ← disj (← (← actionsOf a).mapM fun a => `(tlfml| Enabled $a))
    | "not", #[p] => return ← `(tlfml| ¬ $(← trTemporal acts subs p))
    | "and", ps => return ← trConjT ps
    | "or", ps =>
      let fs ← ps.mapM (trTemporal acts subs)
      return ← disj fs
    | "implies", #[p, q] => return ← `(tlfml| ($(← trTemporal acts subs p) → $(← trTemporal acts subs q)))
    | "iff", #[p, q] => return ← `(tlfml| ($(← trTemporal acts subs p) ↔ $(← trTemporal acts subs q)))
    | "leadsTo", #[p, q] => return ← `(tlfml| ($(← trTemporal acts subs p) ↝ $(← trTemporal acts subs q)))
    | "forall", #[set, f] | "exists", #[set, f] =>
      -- a temporal formula for every (some) element of a set: `⋀ x ∈ S.toList, φ`
      match lambda? f with
      | some (#[p], false, body) =>
        -- over the elements of the set, which the model checker enumerates; the state predicates
        -- of the body read the element (of the subtype) as a value of the element type
        let sT ← trExpr set
        return ← bindLocal (paramName p) fun x => do
          let b ← trTemporal acts (subs.push (paramName p, x)) body
          if op == "forall" then `(tlfml| (∀ $x:ident : { y // y ∈ $sT }, $b))
          else `(tlfml| (∃ $x:ident : { y // y ∈ $sT }, $b))
      | _ => throwErrorAt s "a temporal quantifier needs a lambda"
    | _, _ => pure ()
  match s with
  | `(quint_expr| $p and $q) => `(tlfml| ($(← trTemporal acts subs p) ∧ $(← trTemporal acts subs q)))
  | `(quint_expr| $p or $q) => `(tlfml| ($(← trTemporal acts subs p) ∨ $(← trTemporal acts subs q)))
  | `(quint_expr| $p implies $q) => `(tlfml| ($(← trTemporal acts subs p) → $(← trTemporal acts subs q)))
  | `(quint_expr| $p iff $q) => `(tlfml| ($(← trTemporal acts subs p) ↔ $(← trTemporal acts subs q)))
  | `(quint_expr| $p leadsTo $q) => `(tlfml| ($(← trTemporal acts subs p) ↝ $(← trTemporal acts subs q)))
  | `(quint_expr| and { $es,* }) => trConjT (es.getElems.map (·.raw))
  | `(quint_expr| $q:quintQualId) =>
    let (n, fs) := qualIdParts q
    match mod.defs[n]? with
    | some td => if fs.isEmpty && td.kind == .temporal then trTemporal acts subs td.body
                 else throwErrorAt s "unsupported temporal formula"
    | none => throwErrorAt s "unsupported temporal formula"
  | _ => throwErrorAt s "unsupported temporal formula"
where
  trConjT (ps : Array Syntax) : TrM (TSyntax `tlfml) := do
    let fs ← ps.mapM (trTemporal acts subs)
    let mut r := fs.back!
    for f in fs.pop.reverse do r ← `(tlfml| $f ∧ $r)
    `(tlfml| ($r))

/-! ## The module command -/

/-- The Veil module of the Quint module elaborated last, while it is open. -/
initialize quintOpenModuleExt : EnvExtension (Option Name) ← registerEnvExtension (pure none)

def elabQuintModuleCore (stx : Syntax) : CommandElabM Unit := do
  -- close the previous Quint module if it is still open
  if let some prev := quintOpenModuleExt.getState (← getEnv) then
    if (← getCurrNamespace) == prev then
      elabCommand (← `(end $(mkIdent prev)))
    modifyEnv (quintOpenModuleExt.setState · none)
  let (modStr, _) := qualIdParts stx[1]
  let modName := Name.mkSimple (leanStr modStr)
  modifyEnv (quintModuleExt.addEntry · (Name.mkSimple modStr, stx))
  let items ← expandImports stx[3].getArgs
  let c ← collect modName items
  let mut mod := c.mod
  -- a module whose constants are not all instantiated and that has no state is a library
  -- that is only used through `import`
  if !mod.consts.isEmpty && quint.skipParametric.get (← getOptions) then
    logInfo m!"Quint module `{modStr}` has constants; with `quint.skipParametric` it is elaborated only where it is imported."
    return
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
    modifyEnv (quintOpenModuleExt.setState · (some modName))
  else
    elabCommand (← `(namespace $modId))
    elabCommandString "@[expose] public section"
  -- types, dependencies first
  for td in sortTypeDecls c.typeDecls do elabTypeDecl mod td
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
    if !annotated || (infSetIn? mod qd.body).isSome then
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
    try
      unless ← elabPureDef mod qd do mod := { mod with defRepr := mod.defRepr.erase qd.name }
    catch ex =>
      logWarning m!"`{qd.name}` is inlined: {ex.toMessageData}"
      mod := { mod with defRepr := mod.defRepr.erase qd.name }
  -- `run`s that only assert facts about pure definitions are `#guard` checks (`quint test`)
  for n in order do
    let some qd := mod.defs[n]? | continue
    unless qd.kind == .run && (qd.params.getD #[]).isEmpty do continue
    if !isPureRun mod qd.body || dependsOnState mod n then continue
    try
      let t ← runTr mod (trExpr qd.body)
      -- a test that does not elaborate (e.g. `Map()` without a type) is reported, not an error
      let saved := (← get).messages
      modify fun st => { st with messages := {} }
      withRef qd.ref <| elabCommand (← `(command| #guard (decide ($t) : Bool)))
      let msgs := (← get).messages
      if msgs.hasErrors then
        modify fun st => { st with messages := saved }
        logWarningAt qd.ref m!"test `{qd.name}` is not checked: it does not elaborate as a Lean term"
      else
        modify fun st => { st with messages := saved ++ msgs }
    catch ex => logWarning m!"test `{qd.name}` is not checked: {ex.toMessageData}"
  if !isVeil then
    elabCommandString "end"
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
  -- the variables, for Quint-style reports (`#quint_verify`, `#quint_run`)
  let varInfo := mod.varOrder.map fun v =>
    let isMap := match mod.vars[v]? with
      | some t => match t with
        | `(quint_type| $_ -> $_) => true
        | _ => false
      | none => false
    (leanStr v, v, isMap)
  modifyEnv (quintVarsExt.modifyState · (·.insert modName varInfo))
  -- ghost definitions
  for (qd, isRel) in ghostDefs do
    try
      unless ← elabGhostDef mod qd isRel do mod := { mod with defRepr := mod.defRepr.erase qd.name }
    catch ex =>
      logWarning m!"`{qd.name}` is inlined: {ex.toMessageData}"
      mod := { mod with defRepr := mod.defRepr.erase qd.name }
  -- assumptions
  let mut seenAssumes : Std.HashSet String := {}
  for (n, e) in c.assumes do
    if mod.consts.isEmpty || seenAssumes.contains n then continue
    seenAssumes := seenAssumes.insert n
    try
      let t ← runTr mod (trExpr e)
      let nid := mkIdent (Name.mkSimple (if n == "_" then "assumption" else leanStr n))
      elabCommand (← `(command| assumption [$nid] $t))
    catch ex => logWarning m!"assumption `{n}` is skipped: {ex.toMessageData}"
  -- initial states and transitions
  if let some initDef := (mod.defs[initName]?).filter (·.params.all (·.isEmpty)) then
    try
      let body ← runTr mod (trTopAction initDef.body)
      discard <| withRef initDef.ref <| elabGenerated "the initial action" (← `(command| after_init { $body }))
    catch ex =>
      if quint.lenient.get (← getOptions) then
        logWarning m!"the initial action is skipped (quint.lenient): {ex.toMessageData}"
      else throw ex
  -- Quint action names to the Veil actions that implement them (for temporal properties)
  let mut actionMap : Std.HashMap String (Array String) := {}
  if let some stepDef := (mod.defs[stepName]?).filter (·.params.all (·.isEmpty)) then
    let branches := splitBranches mod stepDef.body
    let mut used : Std.HashMap String Nat := {}
    let mut idx := 0
    for b in branches do
      idx := idx + 1
      let base := if b.name.isEmpty || b.name == stepName then s!"{stepName}_{idx}" else b.name
      let cnt := used.getD base 0
      used := used.insert base (cnt + 1)
      let nm := if cnt == 0 then base else s!"{base}_{cnt + 1}"
      for o in stepName :: (if b.name.isEmpty then b.owners else b.name :: b.owners) do
        actionMap := actionMap.insert o ((actionMap.getD o #[]).push nm)
      try
        let body ← runTr mod (trTopBranch b)
        let cmd ← `(command| action $(mkId nm) { $body })
        trace[veil.debug] m!"Quint action: {cmd}"
        discard <| withRef stepDef.ref <| elabGenerated s!"action `{nm}`" cmd
      catch ex =>
        if quint.lenient.get (← getOptions) then
          logWarning m!"action `{nm}` is skipped (quint.lenient): {ex.toMessageData}"
        else throw ex
  -- temporal properties
  for n in order do
    let some qd := mod.defs[n]? | continue
    unless qd.kind == .temporal && (qd.params.getD #[]).isEmpty do continue
    try
      let f ← runTr mod (trTemporal actionMap (stx := qd.body))
      let nid := mkIdentFrom qd.ref (Name.mkSimple (leanStr qd.name))
      let cmd ← `(command| temporal (only := $(mkIdent `check)) [$nid] $f)
      discard <| withRef qd.ref <| elabGenerated s!"temporal property `{qd.name}`" cmd
    catch ex =>
      logWarningAt qd.ref m!"temporal property `{qd.name}` is not translated: {ex.toMessageData}"
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
syntax (name := quintInvariantCmd) "quint_invariant " quint_ident,+ : command

@[command_elab quintInvariantCmd] def elabQuintInvariant : CommandElab := fun stx => do
  let cands := quintInvCandidateExt.getState (← getEnv)
  let modName ← getCurrNamespace
  for id in stx[1].getSepArgs do
    let n := identStr id
    let some t := cands[(modName, n)]?
      | throwErrorAt id "`{n}` is not a boolean `val` of the Quint module `{modName}`"
    let t : Term := ⟨t⟩
    let nid := mkIdentFrom id (Name.mkSimple (leanStr n))
    withRef id <| elabCommand (← `(command| invariant [$nid] $t))

end Veil.Quint

namespace Veil.Quint
open Lean Elab Command

/-- `quint_constraint c_1, ..., c_n` declares the boolean `val`s `c_i` of the Quint module as Veil
state constraints (`state_constraint [c_i] ...`): the model checker does not explore states that
violate them, like TLC's `CONSTRAINT`. -/
syntax (name := quintConstraintCmd) "quint_constraint " quint_ident,+ : command

@[command_elab quintConstraintCmd] def elabQuintConstraint : CommandElab := fun stx => do
  let cands := quintInvCandidateExt.getState (← getEnv)
  let modName ← getCurrNamespace
  for id in stx[1].getSepArgs do
    let n := identStr id
    let some t := cands[(modName, n)]?
      | throwErrorAt id "`{n}` is not a boolean `val` of the Quint module `{modName}`"
    let t : Term := ⟨t⟩
    let nid := mkIdentFrom id (Name.mkSimple (leanStr n))
    withRef id <| elabCommand (← `(command| state_constraint [$nid] $t))

end Veil.Quint

namespace Veil.Quint
open Lean Elab Command

/-- `quint_bmc k inv_1, ..., inv_n` checks with Veil's symbolic bounded model checker (SMT) that no
execution of at most `k` steps (`k ≥ 2`) violates the boolean `val`s `inv_i`, for every value of
the module's parameters: the counterpart of `quint verify --max-steps=k --invariant=...`
(Apalache). It needs a state that the SMT backend handles: integers, booleans, strings, sum types
and records of these, and finite sets of these with the set operators of
`Veil.Frontend.Quint.Smt` (not maps, `map`, `filter` or `powerset`). Proof reconstruction
(`veil.smt.trust false`) does not support the theory of sets. -/
syntax (name := quintBmcCmd) "quint_bmc " num quint_ident,+ : command

@[command_elab quintBmcCmd] def elabQuintBmc : CommandElab := fun stx => do
  let cands := quintInvCandidateExt.getState (← getEnv)
  let modName ← getCurrNamespace
  let k : TSyntax `num := ⟨stx[1]⟩
  for id in stx[2].getSepArgs do
    let n := identStr id
    let some t := cands[(modName, n)]?
      | throwErrorAt id "`{n}` is not a boolean `val` of the Quint module `{modName}`"
    let t : Term := ⟨t⟩
    let nid := mkIdentFrom id (Name.mkSimple (leanStr n ++ s!"_bmc{k.getNat}"))
    let cmd ← `(command| unsat trace [$nid] {
        any $k:num actions
        assert (¬ $t)
      })
    -- run it, keep Veil's messages, and report as `quint verify` (Apalache) does
    let (msgs, ms) ← withRef id <| elabCollecting cmd
    if msgs.hasErrors then
      let texts ← msgs.toList.mapM (·.data.toString)
      let vars := (quintVarsExt.getState (← getEnv))[modName]?.getD #[]
      let states := parseStates ("\n".intercalate texts)
      -- a counterexample has at least the initial state; otherwise Veil failed to check
      if states.isEmpty then
        logErrorAt id s!"[error] Veil could not check {n} ({ms}ms); see the errors above."
      else
        logInfoAt id (renderStates vars states ++ "\n" ++
          s!"[violation] Found an issue ({ms}ms).\n  violates: {n}")
    else
      logInfoAt id s!"[ok] No violation of {n} found up to {k.getNat} steps ({ms}ms)."

end Veil.Quint
