module

public meta import Lean
public meta import Veil.Frontend.Quint.Syntax
public meta import Veil.Frontend.DSL.Module.Syntax
public meta import Veil.Frontend.DSL.Action.Syntax
public import Veil.Frontend.Quint.Prelude

/-!
# Elaborating Quint modules into Veil modules

`module M { ... }` (see `Veil.Frontend.Quint.Syntax`) is translated declaration by declaration
into Lean and Veil commands:

| Quint                                   | Veil / Lean                                          |
| --------------------------------------- | ---------------------------------------------------- |
| `type T = A \| B(int)`                   | `@[veil_decl] inductive T`                           |
| `type T = { f: int }`, record literals  | a shared `@[veil_decl] structure QuintRecords.QRec_f` |
| `type T = int`                          | `abbrev T := Int`                                    |
| `const c: T`                            | `param c : T`                                        |
| `var x: T`                              | `individual x : T`                                   |
| `pure def f(x: T): U = e` (no `const`)  | `def f (x : T) : U := e`                             |
| other `def`s with annotated parameters  | `ghost function` / `ghost relation`                  |
| boolean `val`s without parameters       | inlined; `quint_invariant v` declares them as invariants |
| `action init = A`                       | `after_init { ⟦A⟧ }`                                 |
| `action step = any { A_1, ..., A_n }`    | one Veil `action` per branch `A_i`                   |
| other `action`s                         | inlined where they are used                          |

Quint's assignments are *delayed*: in `all { x' = y, y' = x }` both right-hand sides read the
current state. An action therefore assigns to local copies `x'` of the variables
(`let mut x' := x`) and copies them into the state at its end. Unassigned variables keep their
values (Quint would report a missing assignment instead).

Boolean Quint expressions become `Prop`s (`and` is `∧`, `S.forall(x => P)` is `∀ x ∈ S, P`);
Lean inserts `decide` where a `Bool` is stored.

A module with state is elaborated into `veil module M`, which stays open: the commands that
follow (`quint_invariant`, `#gen_spec`, `#model_check`, ...) are Veil commands about it, and
`end M` closes it. A module without state becomes `namespace M ... end M`.
-/

public meta section

namespace Veil.Quint
open Lean Elab Command Term Meta _root_.Lean.Parser

/-! ## Options -/

register_option quint.init : String := {
  defValue := "init"
  descr := "the name of the Quint action that defines the initial states"
}

register_option quint.step : String := {
  defValue := "step"
  descr := "the name of the Quint action that defines the transitions"
}

/-! ## Stored modules, for `import M(...)` -/

/-- Every Quint module elaborated so far (in this file or an imported one), by name. -/
initialize quintModuleExt : SimplePersistentEnvExtension (Name × Syntax) (NameMap Syntax) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, s) => m.insert n s
    addImportedFn := fun arrs => arrs.foldl (fun m arr => arr.foldl (fun m (n, s) => m.insert n s) m) {}
  }

/-- Record structures generated so far: sorted field names (joined by `,`) to structure name. -/
initialize quintRecordExt : SimplePersistentEnvExtension (String × Name) (Std.HashMap String Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (k, n) => m.insert k n
    addImportedFn := fun arrs => arrs.foldl (fun m arr => arr.foldl (fun m (k, n) => m.insert k n) m) {}
  }

/-- Zero-argument boolean `val`s of each Veil module, kept for `quint_invariant`:
module name and val name to the Lean term of its body. -/
initialize quintInvCandidateExt : EnvExtension (Std.HashMap (Name × String) Syntax) ←
  registerEnvExtension (pure {})

/-! ## Names -/

/-- The Lean name of a Quint name: `A::b` becomes `A_b`. -/
def leanStr (s : String) : String := s.replace "::" "_"

def mkId (s : String) : Ident := mkIdent (Name.mkSimple (leanStr s))

/-- Lean type names that a Quint type must not shadow inside a module. -/
def reservedTypeNames : List String :=
  ["Option", "List", "Set", "Map", "Nat", "Int", "String", "Bool", "Prod", "Sum", "Unit",
   "Result", "Except", "Array", "Type", "Prop", "State", "Theory", "Label"]

def typeLeanStr (s : String) : String :=
  let s := leanStr s
  if reservedTypeNames.contains s then s ++ "Q" else s

/-- The parts of a `quintQualId`: `A::b.c.d` gives `(["A", "b"], ["c", "d"])`, a qualified
name and the field/method names that follow it. -/
partial def identLeaves (stx : Syntax) : List Syntax :=
  if stx.isIdent then [stx] else stx.getArgs.toList.flatMap identLeaves

/-- The name of a `quint_ident` (or any node with one identifier). -/
def identStr (stx : Syntax) : String :=
  match identLeaves stx with
  | i :: _ => i.getId.toString (escape := false)
  | [] => "_"

def qualIdParts (stx : Syntax) : String × List String :=
  let ids := identLeaves stx
  match ids.reverse with
  | [] => ("", [])
  | last :: revInit =>
    let comps := last.getId.components.map (·.toString (escape := false))
    let lastHead := comps.headD ""
    let quals := revInit.reverse.map (·.getId.toString (escape := false))
    (String.intercalate "::" (quals ++ [lastHead]), comps.drop 1)

/-! ## Module information -/

inductive DefKind where
  | pureVal | pureDef | val | def_ | action | temporal | run | nondet
deriving BEq, Inhabited, Repr

structure QParam where
  name : String
  type? : Option Syntax
deriving Inhabited

structure QDef where
  kind : DefKind
  name : String
  /-- `none` for `val`s written without parentheses. -/
  params : Option (Array QParam)
  retType? : Option Syntax
  body : Syntax
  ref : Syntax
deriving Inhabited

/-- How references to a definition are translated. -/
inductive DefRepr where
  /-- a Lean `def` (or Veil ghost definition) with this name -/
  | named (id : Ident)
  /-- inlined at every use -/
  | inline
deriving Inhabited

structure SumInfo where
  /-- the Lean name of the inductive type -/
  typeName : Name
  /-- the full name of the constructor -/
  ctorName : Name
  hasArg : Bool
deriving Inhabited

structure ModInfo where
  name : Name
  vars : Std.HashMap String Syntax := {}
  varOrder : Array String := #[]
  consts : Std.HashMap String Syntax := {}
  defs : Std.HashMap String QDef := {}
  defRepr : Std.HashMap String DefRepr := {}
  ctors : Std.HashMap String SumInfo := {}
  /-- Quint type names (aliases, sum types) to their Lean names -/
  types : Std.HashMap String Name := {}
  /-- type parameters of polymorphic type definitions -/
  typeParams : Std.HashMap String (Array String) := {}
  /-- known record field names -/
  recordFields : Std.HashSet String := {}
  /-- whether the module is elaborated as a Veil module -/
  isVeil : Bool := false
deriving Inhabited

structure Ctx where
  mod : ModInfo
  /-- local Quint names to Lean identifiers -/
  locals : Std.HashMap String Ident := {}
  /-- the action being translated assigns these variables (Quint names) -/
  primed : Std.HashSet String := {}
  /-- type variables in scope -/
  tyVars : Std.HashSet String := {}

abbrev TrM := ReaderT Ctx (StateRefT Nat CommandElabM)

def freshName (base : String) : TrM Ident := do
  let n ← modifyGet fun n => (n, n + 1)
  return mkIdent (Name.mkSimple s!"{leanStr base}_{n}")

def withLocal (q : String) (id : Ident) (k : TrM α) : TrM α :=
  withReader (fun c => { c with locals := c.locals.insert q id }) k

/-- Bind a Quint local name to a Lean identifier with the same name, unless that would shadow
something the body may need (then a fresh name is used). -/
def bindLocal (q : String) (k : Ident → TrM α) : TrM α := do
  let ctx ← read
  let clash := ctx.locals.contains q || ctx.mod.vars.contains q || ctx.mod.consts.contains q
    || ctx.mod.defs.contains q
  let id ← if clash || q == "_" then freshName (if q == "_" then "x" else q) else pure (mkId q)
  withLocal q id (k id)

/-! ## Records -/

def recordKey (fields : Array String) : String :=
  String.intercalate "," (fields.qsort (· < ·)).toList

def recordStructName (fields : Array String) : Name :=
  `QuintRecords ++ Name.mkSimple ("QRec_" ++ String.intercalate "__" (fields.qsort (· < ·)).toList)

/-- Declare the record structure for these field names, unless it exists. -/
def ensureRecord (fields : Array String) : CommandElabM Name := do
  let fields := fields.qsort (· < ·)
  let key := recordKey fields
  if let some n := (quintRecordExt.getState (← getEnv))[key]? then return n
  let name := recordStructName fields
  if (← getEnv).contains name then
    modifyEnv (quintRecordExt.addEntry · (key, name))
    return name
  let tyParams := (List.range fields.size).toArray.map fun i => mkIdent (Name.mkSimple s!"α{i}")
  let fieldDecls ← fields.mapIdxM fun i f => do
    let fid := mkIdent (Name.mkSimple f)
    let ty := tyParams[i]!
    `(Lean.Parser.Command.structExplicitBinder| ($fid : $ty))
  let shortName := mkIdent (Name.mkSimple name.getString!)
  let cmd ← `(namespace QuintRecords
    @[veil_decl] structure $shortName $[($tyParams : Type)]* where
      $[$fieldDecls]*
    end QuintRecords)
  elabCommand cmd
  modifyEnv (quintRecordExt.addEntry · (key, name))
  return name

/-! ## Syntax helpers -/

def sepArgs (stx : Syntax) : Array Syntax := stx.getSepArgs

/-- Strip `(e)` and `{ e }` around an expression. -/
partial def unwrap (stx : Syntax) : Syntax :=
  match stx with
  | `(quint_expr| ($e)) => unwrap e
  | `(quint_expr| { $e:quint_expr }) => unwrap e
  | _ => stx

def isQualId (stx : Syntax) : Bool := stx.isOfKind ``quintQualId

/-- The string literal inside an expression, if it is one. -/
partial def strLitOf? (stx : Syntax) : Option String :=
  match stx.isStrLit? with
  | some v => some v
  | none => if stx.getNumArgs == 1 then strLitOf? stx[0] else
      match stx with
      | `(quint_expr| ($e)) => strLitOf? e
      | _ => none

/-- The qualified-identifier node of `quint_expr`, if `stx` is one. The keyword `assert` is
returned as the identifier `assert`. -/
def asQualId? (stx : Syntax) : Option Syntax :=
  if stx.getNumArgs == 1 && stx[0].isOfKind ``quintQualId then some stx[0]
  else none

/-- The kind name given to `syntax` declarations in `Syntax.lean` has no stable name; we match
with quotations and use these helpers for the hand-written parsers. -/
def isApp (stx : Syntax) : Bool := stx.isOfKind ``quintApp
def isSub (stx : Syntax) : Bool := stx.isOfKind ``quintSub

/-- `e.f` (a dot without a call): the receiver and the names after the dot (`e.f.g` reads
`f.g` as one identifier). -/
def dots? (stx : Syntax) : Option (Syntax × List String) :=
  if stx.getKind == `Veil.Quint.«quint_expr_.__» then
    some (stx[0], stx[2].getId.components.map (·.toString (escape := false)))
  else none

/-- `e.f`: the receiver and the last name, with any intermediate fields as a dotted receiver. -/
def dot? (stx : Syntax) : Option (Syntax × String) :=
  match dots? stx with
  | some (e, fs) => some (e, fs.getLastD "")
  | none => none

/-! ## Types -/

def typeVarLike (s : String) : Bool :=
  s.length > 0 && (s.front).isLower && !["int", "str", "bool"].contains s

partial def trType (stx : Syntax) : TrM Term := do
  match stx with
  | `(quint_type| $q:quintQualId) =>
    let (n, _) := qualIdParts q
    match n with
    | "int" => `(Int)
    | "str" => `(String)
    | "bool" => `(Bool)
    | "Bool" => `(Bool)
    | "Int" => `(Int)
    | _ =>
      if let some ln := (← read).mod.types[n]? then return mkIdent ln
      return mkIdent (Name.mkSimple (typeLeanStr n))
  | `(quint_type| $q:quintQualId[$args,*]) =>
    let (n, _) := qualIdParts q
    let args ← args.getElems.mapM trType
    match n, args with
    | "Set", #[a] => `(Quint.Set $a)
    | "List", #[a] => `(List $a)
    | _, _ =>
      let ln := (← read).mod.types[n]?.getD (Name.mkSimple (typeLeanStr n))
      `($(mkIdent ln) $args*)
  | `(quint_type| ()) => `(Unit)
  | `(quint_type| ($t)) => trType t
  | `(quint_type| ($t, $ts,*)) =>
    let all := #[t] ++ ts.getElems
    let tys ← all.mapM trType
    match tys with
    | #[a, b] => `($a × $b)
    | #[a, b, c] => `(Quint.Tuple.Tup3 $a $b $c)
    | #[a, b, c, dd] => `(Quint.Tuple.Tup4 $a $b $c $dd)
    | #[a, b, c, dd, e] => `(Quint.Tuple.Tup5 $a $b $c $dd $e)
    | _ => throwErrorAt stx "tuples with more than five components are not supported"
  | `(quint_type| { $fs,* }) =>
    let fs := fs.getElems
    let pairs := fs.map fun f => (identStr f.raw[0], f.raw[2])
    let sorted := pairs.qsort (fun a b => a.1 < b.1)
    let name ← liftM (m := CommandElabM) <| ensureRecord (sorted.map (·.1))
    let tys ← sorted.mapM (trType ·.2)
    `($(mkIdent name) $tys*)
  | `(quint_type| $a -> $b) => do `(Quint.Map $(← trType a) $(← trType b))
  | `(quint_type| $a => $b) => do `($(← trType a) → $(← trType b))
  | `(quint_type| ($ts,*) => $b) => do
    let mut r ← trType b
    for a in ts.getElems.reverse do
      r ← `($(← trType a) → $r)
    return r
  | _ => throwErrorAt stx "unsupported Quint type"

/-- Type variables (lowercase names that are not types of the module) in a type. -/
partial def typeVarsOf (mod : ModInfo) (stx : Syntax) : Std.HashSet String :=
  go stx {}
where
  go (s : Syntax) (acc : Std.HashSet String) : Std.HashSet String :=
    if s.isOfKind ``quintQualId then
      let (n, _) := qualIdParts s
      if typeVarLike n && !mod.types.contains n then acc.insert n else acc
    else s.getArgs.foldl (fun acc a => go a acc) acc

/-! ## Expressions -/

/-- Names of Quint builtin operators that take one argument and may be written without
parentheses after a dot in older specifications (`S.size`, `S.powerset`). -/
def nullaryMethods : List String :=
  ["size", "powerset", "flatten", "keys", "length", "head", "tail", "indices", "isFinite",
   "chooseSome", "getOnlyElement", "fieldNames", "last", "not"]

/-- `Int`, `Nat`, `Bool` used as sets. -/
inductive InfSet where | int | nat | bool

partial def infSetIn? (mod : ModInfo) (stx : Syntax) (fuel : Nat := 8) : Option InfSet :=
  match asQualId? (unwrap stx) with
  | some q => match (qualIdParts q) with
    | ("Int", []) => some .int
    | ("Nat", []) => some .nat
    | (n, []) =>
      -- an alias such as `pure val Ballot = Nat`
      match mod.defs[n]? with
      | some d => if fuel > 0 && (d.params.getD #[]).isEmpty then infSetIn? mod d.body (fuel - 1) else none
      | none => none
    | _ => none
  | none => none

/-- A lambda: parameter syntaxes (each a `quintParam`), whether it destructures a tuple, body. -/
def lambda? (stx : Syntax) : Option (Array Syntax × Bool × Syntax) :=
  match unwrap stx with
  | `(quint_expr| $p:quintParam => $b) => some (#[p], false, b)
  | `(quint_expr| ($ps:quintParam,*) => $b) => some (ps.getElems.map (·.raw), false, b)
  | `(quint_expr| (($ps:quintParam,*)) => $b) => some (ps.getElems.map (·.raw), true, b)
  | _ => none

def paramName (p : Syntax) : String :=
  if (identLeaves p).isEmpty then "_" else identStr p

mutual

partial def trExpr (stx : Syntax) : TrM Term := withRef stx do
  if let some (e, fs) := dots? stx then
    let mut acc ← trExpr e
    for f in fs do acc ← trField acc f e
    return acc
  if isApp stx then
    return ← trApp stx[0] (sepArgs stx[2])
  if isSub stx then
    return ← `($(← trExpr stx[0]) - $(← trExpr stx[2]))
  match stx with
  | `(quint_expr| $n:num) => `(($n : Int))
  | `(quint_expr| $s:str) => pure s
  | `(quint_expr| $q:quintQualId) => trName q
  | `(quint_expr| ()) => `(())
  | `(quint_expr| ($e)) => do `(($(← trExpr e)))
  | `(quint_expr| ($e, $es,*)) => trTuple (#[e] ++ es.getElems)
  | `(quint_expr| [ $es,* ]) => do
    let es ← es.getElems.mapM trExpr
    `([$es,*])
  | `(quint_expr| { $e:quint_expr }) => trExpr e
  | `(quint_expr| { $fs:quintRecElem,* }) => trRecord stx fs.getElems
  | `(quint_expr| and { $es,* }) => do trConj (← es.getElems.mapM trExpr)
  | `(quint_expr| all { $es,* }) => do trConj (← es.getElems.mapM trExpr)
  | `(quint_expr| or { $es,* }) => do trDisj (← es.getElems.mapM trExpr)
  | `(quint_expr| any { $es,* }) => do trDisj (← es.getElems.mapM trExpr)
  | `(quint_expr| and($es,*)) => do trConj (← es.getElems.mapM trExpr)
  | `(quint_expr| or($es,*)) => do trDisj (← es.getElems.mapM trExpr)
  | `(quint_expr| if ($c) $a else $b) => do
    let c' ← trExpr c
    let a' ← trExpr a
    let b' ← trExpr b
    `(if ($c' : Prop) then $a' else $b')
  | `(quint_expr| match $e { $[|]? $c:quintMatchCase $[| $cs:quintMatchCase]* }) =>
    trMatch e (#[c] ++ cs)
  | `(quint_expr| $_p:quintParam => $_b) => trLambda stx
  | `(quint_expr| ($_ps:quintParam,*) => $_b) => trLambda stx
  | `(quint_expr| (($_ps:quintParam,*)) => $_b) => trLambda stx
  | `(quint_expr| $dd:quintOperDef $body) => trLetDef dd body
  | `(quint_expr| $dd:quintValTuple $body) => trValTuple dd body
  | `(quint_expr| $l[$i]) => do `(Quint.List.nth $(← trExpr l) $(← trExpr i))
  | `(quint_expr| $a ^ $b) => do `(Quint.ipow $(← trExpr a) $(← trExpr b))
  | `(quint_expr| - $a) => do `(- $(← trExpr a))
  | `(quint_expr| $a * $b) => do `($(← trExpr a) * $(← trExpr b))
  | `(quint_expr| $a / $b) => do `($(← trExpr a) / $(← trExpr b))
  | `(quint_expr| $a % $b) => do `($(← trExpr a) % $(← trExpr b))
  | `(quint_expr| $a + $b) => do `($(← trExpr a) + $(← trExpr b))
  | `(quint_expr| $a == $b) => do `($(← trExpr a) = $(← trExpr b))
  | `(quint_expr| $a != $b) => do `($(← trExpr a) ≠ $(← trExpr b))
  | `(quint_expr| $a < $b) => do `($(← trExpr a) < $(← trExpr b))
  | `(quint_expr| $a <= $b) => do `($(← trExpr a) ≤ $(← trExpr b))
  | `(quint_expr| $a > $b) => do `($(← trExpr a) > $(← trExpr b))
  | `(quint_expr| $a >= $b) => do `($(← trExpr a) ≥ $(← trExpr b))
  | `(quint_expr| $a and $b) => do `($(← trExpr a) ∧ $(← trExpr b))
  | `(quint_expr| $a or $b) => do `($(← trExpr a) ∨ $(← trExpr b))
  | `(quint_expr| $a iff $b) => do `($(← trExpr a) ↔ $(← trExpr b))
  | `(quint_expr| $a implies $b) => do `($(← trExpr a) → $(← trExpr b))
  | `(quint_expr| $a -> $b) => do `(($(← trExpr a), $(← trExpr b)))
  | `(quint_expr| $_ = $_) =>
    throwErrorAt stx "an assignment `x' = e` can only appear in an action"
  | _ => throwErrorAt stx "unsupported Quint expression"

partial def trTuple (es : Array Syntax) : TrM Term := do
  let ts ← es.mapM trExpr
  match ts with
  | #[a, b] => `(($a, $b))
  | #[a, b, c] => `(Quint.Tuple.Tup3.mk $a $b $c)
  | #[a, b, c, dd] => `(Quint.Tuple.Tup4.mk $a $b $c $dd)
  | #[a, b, c, dd, e] => `(Quint.Tuple.Tup5.mk $a $b $c $dd $e)
  | _ => throwError "tuples with more than five components are not supported"

partial def trConj (ts : Array Term) : TrM Term := do
  if ts.isEmpty then return ← `(True)
  let mut r := ts.back!
  for t in ts.pop.reverse do r ← `($t ∧ $r)
  return r

partial def trDisj (ts : Array Term) : TrM Term := do
  if ts.isEmpty then return ← `(False)
  let mut r := ts.back!
  for t in ts.pop.reverse do r ← `($t ∨ $r)
  return r

partial def trRecord (stx : Syntax) (elems : Array Syntax) : TrM Term := do
  let mut spread : Option Syntax := none
  let mut fields : Array (String × Syntax) := #[]
  for e in elems do
    let e' := if e.getNumArgs == 1 then e[0] else e
    if e'[0].isAtom && e'[0].getAtomVal == "..." then
      spread := some e'[1]
    else
      fields := fields.push (identStr e'[0], e'[2])
  if let some r := spread then
    let mut acc ← trExpr r
    for (f, v) in fields do
      let fid := mkIdent (Name.mkSimple f)
      acc ← `({ $acc with $fid:ident := $(← trExpr v) })
    return acc
  let sorted := fields.qsort (fun a b => a.1 < b.1)
  let name ← liftM (m := CommandElabM) <| ensureRecord (sorted.map (·.1))
  let vals ← sorted.mapM (trExpr ·.2)
  withRef stx `($(mkIdent (name ++ `mk)) $vals*)

/-- Field access `e.f` (or a builtin called without parentheses). -/
partial def trField (e : Term) (f : String) (_eStx : Syntax) : TrM Term := do
  if f.startsWith "_" && (f.drop 1).all Char.isDigit then
    let fid := mkIdent (Name.mkSimple f)
    return ← `(($e).$fid:ident)
  if nullaryMethods.contains f && !(← read).mod.recordFields.contains f then
    return ← trBuiltin f #[e] #[]
  let fid := mkIdent (Name.mkSimple f)
  `(($e).$fid:ident)

/-- A qualified identifier, possibly followed by fields. -/
partial def trName (q : Syntax) : TrM Term := do
  let (n, fields) := qualIdParts q
  let mut acc ← withRef q (trBaseName q n)
  for f in fields do
    acc ← trField acc f q
  return acc

partial def trBaseName (ref : Syntax) (n : String) : TrM Term := do
  let ctx ← read
  if let some id := ctx.locals[n]? then return id
  if n == "true" then return ← `(true)
  if n == "false" then return ← `(false)
  if n == "Bool" then return ← `(Quint.Set.ofList [false, true])
  if n.endsWith "'" then
    throwErrorAt ref "a primed variable can only be assigned (`{n} = e`), not read"
  if ctx.mod.vars.contains n || ctx.mod.consts.contains n then return mkId n
  if let some dd := ctx.mod.defs[n]? then
    match ctx.mod.defRepr[n]?.getD .inline with
    | .named id => return id
    | .inline =>
      let ps := dd.params.getD #[]
      if ps.size > 0 then
        -- an operator used as a value: `fun p_1 ... p_n => body`
        return ← withReader (fun c => { c with locals := {} })
          (trLambdaNames (ps.map (·.name)).toList [] dd.body)
      return ← withReader (fun c => { c with locals := {} }) (trExpr dd.body)
  if let some info := ctx.mod.ctors[n]? then
    return mkIdent info.ctorName
  if n == "Int" || n == "Nat" then
    throwErrorAt ref "the infinite set `{n}` can only be used in `forall`, `exists`, `in` and `oneOf`"
  -- a Lean name (e.g. from another namespace)
  return mkIdent (Name.mkSimple (leanStr n))

/-- Translate the application `callee(args)`. -/
partial def trApp (callee : Syntax) (args : Array Syntax) : TrM Term := do
  -- method call via dot on an arbitrary expression: `(e).f(args)`
  if let some (e, fs) := dots? callee then
    if fs.length ≤ 1 then
      return ← trCall (fs.getLastD "") (#[e] ++ args)
    let mut recv ← trExpr e
    for f in fs.dropLast do recv ← trField recv f e
    return ← trCallT (fs.getLastD "") recv args
  match asQualId? callee with
  | some q =>
    let (n, fields) := qualIdParts q
    match fields.reverse with
    | [] => trCall n args
    | m :: revRest =>
      -- `a.b.m(args)`: the method `m` on the receiver `a.b`
      let ctx ← read
      let mut recv ← trBaseName q n
      for f in revRest.reverse do recv ← trField recv f q
      let isLocalFn := ctx.locals.contains n && fields.isEmpty
      if isLocalFn then trCall n args
      else trCallT m recv args
  | none =>
    -- e.g. `(f)(x)`
    let f ← trExpr callee
    let argTs ← args.mapM trExpr
    `($f $argTs*)

/-- Call of a named operator whose first argument is already translated. -/
partial def trCallT (name : String) (recv : Term) (args : Array Syntax) : TrM Term := do
  trCallCore name (some recv) args

partial def trCall (name : String) (args : Array Syntax) : TrM Term :=
  trCallCore name none args

/-- `recv?` is the receiver of a UFCS call `recv.name(args)`, already translated. -/
partial def trCallCore (name : String) (recv? : Option Term) (args : Array Syntax) : TrM Term := do
  let ctx ← read
  let allStx : Array (Option Syntax) := (if recv?.isSome then #[none] else #[]) ++ args.map some
  -- local operator (a lambda-bound or `def`-bound name)
  if let some id := ctx.locals[name]? then
    let argTs ← args.mapM trExpr
    let argTs := match recv? with | some r => #[r] ++ argTs | none => argTs
    return ← `($id $argTs*)
  -- user definitions
  if let some dd := ctx.mod.defs[name]? then
    let argTs ← args.mapM trExpr
    let argTs := match recv? with | some r => #[r] ++ argTs | none => argTs
    match ctx.mod.defRepr[name]?.getD .inline with
    | .named id => return ← `($id $argTs*)
    | .inline => return ← inlineDef dd argTs
  -- sum type constructors
  if let some info := ctx.mod.ctors[name]? then
    let argTs ← args.mapM trExpr
    let argTs := match recv? with | some r => #[r] ++ argTs | none => argTs
    if info.hasArg then
      match argTs with
      | #[a] => return ← `($(mkIdent info.ctorName) $a)
      | _ => throwError "variant `{name}` takes one argument" 
    else return mkIdent info.ctorName
  -- builtins: translate the arguments lazily, since some take lambdas or sets like `Int`
  trBuiltin name (match recv? with | some r => #[r] | none => #[]) args (allStx := allStx)

/-- Inline a definition applied to translated arguments. -/
partial def inlineDef (dd : QDef) (args : Array Term) : TrM Term := do
  let ps := dd.params.getD #[]
  if ps.size != args.size then
    throwError "operator `{dd.name}` expects {ps.size} arguments, got {args.size}"
  -- bind parameters with `let`, under fresh names, then translate the body in a context
  -- where only the parameters are local
  let mut binds : Array (Ident × Term) := #[]
  let mut locals : Std.HashMap String Ident := {}
  for p in ps, a in args do
    if p.name == "_" then continue
    let id ← freshName p.name
    binds := binds.push (id, a)
    locals := locals.insert p.name id
  let body ← withReader (fun c => { c with locals := locals }) (trExpr dd.body)
  let mut r := body
  for (id, a) in binds.reverse do
    r ← `(let $id:ident := $a; $r)
  `(($r))

partial def trLambda (stx : Syntax) : TrM Term := do
  let some (ps, tuple, body) := lambda? stx | throwErrorAt stx "expected a lambda"
  let names := ps.map paramName
  go names.toList [] tuple body
where
  go (names : List String) (acc : List Ident) (tuple : Bool) (body : Syntax) : TrM Term := do
    match names with
    | [] =>
      let b ← trExpr body
      let ids := acc.reverse.toArray
      if tuple then
        let x ← freshName "t"
        let pat ← match ids with
          | #[a, b'] => `(($a, $b'))
          | _ => `(⟨$ids,*⟩)
        `(fun $x:ident => match $x:ident with | $pat => $b)
      else `(fun $ids* => $b)
    | n :: ns => bindLocal n fun id => go ns (id :: acc) tuple body

/-- `S.forall(x => P)` and `S.exists(x => P)` as bounded quantifiers. -/
partial def trQuant (isForall : Bool) (setStx : Syntax) (f : Syntax) : TrM Term := do
  let mkQ (x : Ident) (body : Term) : TrM Term := do
    match infSetIn? (← read).mod setStx with
    | some .int => if isForall then `(∀ $x:ident : Int, $body) else `(∃ $x:ident : Int, $body)
    | some .nat =>
      if isForall then `(∀ $x:ident : Int, $x ≥ 0 → $body) else `(∃ $x:ident : Int, $x ≥ 0 ∧ $body)
    | _ =>
      let s ← trExpr setStx
      if isForall then `(∀ $x:ident, $x ∈ $s → $body) else `(∃ $x:ident, $x ∈ $s ∧ $body)
  match lambda? f with
  | some (#[p], false, body) =>
    bindLocal (paramName p) fun x => do mkQ x (← trExpr body)
  | some (ps, true, body) =>
    -- `((a, b)) => P`: bind the tuple and project its components
    let x ← freshName "t"
    let names := ps.map paramName
    let projs : Array Term ← match names.size with
      | 2 => pure #[← `(($x).1), ← `(($x).2)]
      | n => (List.range n).toArray.mapM fun i => do
          let fid := mkIdent (Name.mkSimple s!"_{i+1}")
          `(($x).$fid:ident)
    let rec bindAll (i : Nat) : TrM Term := do
      if h : i < names.size then
        bindLocal names[i] fun id => do
          let rest ← bindAll (i + 1)
          `(let $id:ident := $(projs[i]!); $rest)
      else trExpr body
    mkQ x (← bindAll 0)
  | some (ps, false, body) =>
    -- a multi-argument lambda over a set of tuples
    let x ← freshName "t"
    let names := ps.map paramName
    let projs : Array Term ← match names.size with
      | 2 => pure #[← `(($x).1), ← `(($x).2)]
      | n => (List.range n).toArray.mapM fun i => do
          let fid := mkIdent (Name.mkSimple s!"_{i+1}")
          `(($x).$fid:ident)
    let rec bindAll2 (i : Nat) : TrM Term := do
      if h : i < names.size then
        bindLocal names[i] fun id => do
          let rest ← bindAll2 (i + 1)
          `(let $id:ident := $(projs[i]!); $rest)
      else trExpr body
    mkQ x (← bindAll2 0)
  | none =>
    let p ← trExpr f
    let x ← freshName "x"
    mkQ x (← `($p $x))

/-- `match e { | A(x) => e1 | B => e2 | _ => e3 }` as
`if T.isA d then (let x := T.getA d; e1) else if T.isB d then e2 else e3`. Quint's variant
eliminator becomes a chain of conditionals over the discriminators that the frontend declares for
each sum type, which Veil's verification conditions and the SMT backend handle directly. -/
partial def trMatch (e : Syntax) (cases : Array Syntax) : TrM Term := do
  let dTerm ← trExpr e
  let dId ← freshName "m"
  let parsed := cases.map fun c =>
    let pat := c[0]
    let rhs := c[2]
    match identLeaves pat with
    | [] => (none, none, rhs)
    | l :: _ =>
      let inner := if pat.getNumArgs == 1 then pat[0] else pat
      let argOpt := if inner.getNumArgs ≥ 2 then inner[1] else Syntax.missing
      (some (l.getId.toString (escape := false)),
       (if argOpt.getNumArgs ≥ 3 then some argOpt[1] else none), rhs)
  let rec go (cs : List (Option String × Option Syntax × Syntax)) : TrM Term := do
    match cs with
    | [] => throwErrorAt e "a `match` needs at least one case"
    | (lbl?, arg?, rhs) :: rest =>
      let body ← match lbl? with
        | none => trExpr rhs
        | some lbl =>
          let some info := (← read).mod.ctors[lbl]?
            | throwErrorAt e "unknown variant `{lbl}`"
          let getId := mkIdent (info.typeName ++ Name.mkSimple ("get" ++ lbl))
          match arg? with
          | some p =>
            if paramName p == "_" then trExpr rhs
            else bindLocal (paramName p) fun x => do
              let b ← trExpr rhs
              `(let $x:ident := $getId $dId; $b)
          | none => trExpr rhs
      match lbl?, rest with
      | none, _ => return body
      | some _, [] => return body
      | some lbl, _ =>
        let some info := (← read).mod.ctors[lbl]? | throwErrorAt e "unknown variant `{lbl}`"
        let isId := mkIdent (info.typeName ++ Name.mkSimple ("is" ++ lbl))
        let restT ← go rest
        `(if $isId $dId = true then $body else $restT)
  let r ← go parsed.toList
  `(let $dId:ident := $dTerm; $r)

/-- `val x = e  body`, `def f(x) = e  body`, `pure val ...` (not `nondet`). -/
partial def trLetDef (dd : Syntax) (body : Syntax) : TrM Term := do
  let qd := parseOperDef dd
  match qd.kind with
  | .nondet => throwErrorAt dd "`nondet` can only be used in an action"
  | _ => pure ()
  let v ← match qd.params with
    | some ps =>
      if ps.isEmpty then trExpr qd.body
      else
        let names := ps.map (·.name)
        trLambdaNames names.toList [] qd.body
    | none => trExpr qd.body
  bindLocal qd.name fun id => do
    let b ← trExpr body
    `(let $id:ident := $v; $b)

partial def trLambdaNames (names : List String) (acc : List Ident) (body : Syntax) : TrM Term := do
  match names with
  | [] => let b ← trExpr body; let ids := acc.reverse.toArray; `(fun $ids* => $b)
  | n :: ns => bindLocal n fun id => trLambdaNames ns (id :: acc) body

partial def trValTuple (dStx : Syntax) (body : Syntax) : TrM Term := do
  -- `(pure)? val ( p,* ) = e` or `val { f,* } = e`
  let patStx := dStx[2]
  let rhsT ← trExpr dStx[4]
  let x ← freshName "v"
  if patStx[0].getAtomVal == "(" then
    let names := (sepArgs patStx[1]).map paramName
    let projs : Array Term ← match names.size with
      | 2 => pure #[← `(($x).1), ← `(($x).2)]
      | n => (List.range n).toArray.mapM fun i => do
          let fid := mkIdent (Name.mkSimple s!"_{i+1}")
          `(($x).$fid:ident)
    bindProjs x rhsT names projs body
  else
    let names := (sepArgs patStx[1]).map identStr
    let projs ← names.mapM fun f => do
      let fid := mkIdent (Name.mkSimple f)
      `(($x).$fid:ident)
    bindProjs x rhsT names projs body

partial def bindProjs (x : Ident) (rhs : Term) (names : Array String) (projs : Array Term)
    (body : Syntax) : TrM Term := do
  let rec go (i : Nat) : TrM Term := do
    if h : i < names.size then
      bindLocal names[i] fun id => do
        let rest ← go (i + 1)
        `(let $id:ident := $(projs[i]!); $rest)
    else trExpr body
  let b ← go 0
  `(let $x:ident := $rhs; $b)

/-- Builtin operators. `pre` holds already-translated leading arguments (the receiver of a
UFCS call), `args` the remaining argument syntaxes. -/
partial def trBuiltin (name : String) (pre : Array Term) (args : Array Syntax)
    (allStx : Array (Option Syntax) := #[]) : TrM Term := do
  -- the syntax of all arguments, when available (needed for lambdas and `Int`)
  let stxAt (i : Nat) : Option Syntax :=
    if i < pre.size then (allStx[i]?).join else args[i - pre.size]?
  let arg (i : Nat) : TrM Term := do
    if h : i < pre.size then return pre[i]
    match args[i - pre.size]? with
    | some a => trExpr a
    | none => throwError "builtin `{name}` is missing argument {i + 1}"
  let n := pre.size + args.size
  let all : TrM (Array Term) := (List.range n).toArray.mapM arg
  match name, n with
  -- sets
  | "Set", _ => do `(Quint.Set.ofList [$(← all),*])
  | "contains", 2 => do
    match (stxAt 0).bind (infSetIn? (← read).mod) with
    | some .int => `(True)
    | some .nat => `($(← arg 1) ≥ 0)
    | _ => `($(← arg 1) ∈ $(← arg 0))
  | "in", 2 => do
    match (stxAt 1).bind (infSetIn? (← read).mod) with
    | some .int => `(True)
    | some .nat => `($(← arg 0) ≥ 0)
    | _ => `($(← arg 0) ∈ $(← arg 1))
  | "union", 2 => do `($(← arg 0) ∪ $(← arg 1))
  | "intersect", 2 => do `($(← arg 0) ∩ $(← arg 1))
  | "exclude", 2 => do `($(← arg 0) \ $(← arg 1))
  | "subseteq", 2 => do `(Quint.Set.subseteq $(← arg 0) $(← arg 1))
  | "map", 2 => do `(Quint.Set.map $(← arg 0) $(← arg 1))
  | "filter", 2 => do `(Quint.Set.filter $(← arg 0) $(← arg 1))
  | "fold", 3 => do `(Quint.Set.fold $(← arg 0) $(← arg 1) $(← arg 2))
  | "forall", 2 | "exists", 2 =>
    let some f := stxAt 1 | throwError "`{name}` expects a lambda"
    match stxAt 0 with
    | some s => trQuant (name == "forall") s f
    | none =>
      -- the receiver was translated already; quantify over it
      let s := pre[0]!
      match lambda? f with
      | some (#[p], false, body) =>
        bindLocal (paramName p) fun x => do
          let b ← trExpr body
          if name == "forall" then `(∀ $x:ident, $x ∈ $s → $b) else `(∃ $x:ident, $x ∈ $s ∧ $b)
      | _ =>
        let p ← trExpr f
        let x ← freshName "x"
        if name == "forall" then `(∀ $x:ident, $x ∈ $s → $p $x) else `(∃ $x:ident, $x ∈ $s ∧ $p $x)
  | "powerset", 1 => do `(Quint.Set.powerset $(← arg 0))
  | "flatten", 1 => do `(Quint.Set.flatten $(← arg 0))
  | "size", 1 => do `(Quint.Set.size $(← arg 0))
  | "isFinite", 1 => `(True)
  | "chooseSome", 1 => do `(Quint.Set.chooseSome $(← arg 0))
  | "getOnlyElement", 1 => do `(Quint.Set.getOnlyElement $(← arg 0))
  | "oneOf", 1 => do `(Quint.Set.chooseSome $(← arg 0))
  | "to", 2 => do `(Quint.Set.range $(← arg 0) $(← arg 1))
  | "tuples", 2 => do `(Quint.Set.tuples2 $(← arg 0) $(← arg 1))
  | "tuples", 3 => do `(Quint.Set.tuples3 $(← arg 0) $(← arg 1) $(← arg 2))
  | "allListsUpTo", 2 => do `(Quint.Set.allListsUpTo $(← arg 0) $(← arg 1))
  | "setOfMaps", 2 => do `(Quint.Set.setOfMaps $(← arg 0) $(← arg 1))
  -- maps
  | "Map", _ => do `(Quint.Map.ofList [$(← all),*])
  | "get", 2 => do `(Quint.Map.get $(← arg 0) $(← arg 1))
  | "set", 3 | "put", 3 => do `(Quint.Map.set $(← arg 0) $(← arg 1) $(← arg 2))
  | "setBy", 3 => do `(Quint.Map.setBy $(← arg 0) $(← arg 1) $(← arg 2))
  | "keys", 1 => do `(Quint.Map.keys $(← arg 0))
  | "mapBy", 2 => do `(Quint.Map.mapBy $(← arg 0) $(← arg 1))
  | "setToMap", 1 => do `(Quint.Map.setToMap $(← arg 0))
  -- lists
  | "List", _ => do `([$(← all),*])
  | "append", 2 => do `(Quint.List.append $(← arg 0) $(← arg 1))
  | "concat", 2 => do `($(← arg 0) ++ $(← arg 1))
  | "head", 1 => do `(Quint.List.head $(← arg 0))
  | "last", 1 => do `(Quint.List.last $(← arg 0))
  | "tail", 1 => do `(List.tail $(← arg 0))
  | "length", 1 => do `(Quint.List.length $(← arg 0))
  | "nth", 2 => do `(Quint.List.nth $(← arg 0) $(← arg 1))
  | "indices", 1 => do `(Quint.List.indices $(← arg 0))
  | "replaceAt", 3 => do `(Quint.List.replaceAt $(← arg 0) $(← arg 1) $(← arg 2))
  | "slice", 3 => do `(Quint.List.slice $(← arg 0) $(← arg 1) $(← arg 2))
  | "select", 2 => do `(List.filter $(← arg 1) $(← arg 0))
  | "foldl", 3 => do `(List.foldl $(← arg 2) $(← arg 1) $(← arg 0))
  | "foldr", 3 => do `(Quint.List.foldr $(← arg 0) $(← arg 1) $(← arg 2))
  | "range", 2 => do `(Quint.List.range $(← arg 0) $(← arg 1))
  -- booleans
  | "not", 1 => do `(¬ $(← arg 0))
  | "iff", 2 => do `($(← arg 0) ↔ $(← arg 1))
  | "implies", 2 => do `($(← arg 0) → $(← arg 1))
  | "eq", 2 => do `($(← arg 0) = $(← arg 1))
  | "neq", 2 => do `($(← arg 0) ≠ $(← arg 1))
  | "ite", 3 => do
    let c ← arg 0
    let a ← arg 1
    let b ← arg 2
    `(if $c then $a else $b)
  | "assert", 1 => arg 0
  -- integers
  | "iadd", 2 => do `($(← arg 0) + $(← arg 1))
  | "isub", 2 => do `($(← arg 0) - $(← arg 1))
  | "imul", 2 => do `($(← arg 0) * $(← arg 1))
  | "idiv", 2 => do `($(← arg 0) / $(← arg 1))
  | "imod", 2 => do `($(← arg 0) % $(← arg 1))
  | "ipow", 2 => do `(Quint.ipow $(← arg 0) $(← arg 1))
  | "iuminus", 1 => do `(- $(← arg 0))
  | "ilt", 2 => do `($(← arg 0) < $(← arg 1))
  | "ilte", 2 => do `($(← arg 0) ≤ $(← arg 1))
  | "igt", 2 => do `($(← arg 0) > $(← arg 1))
  | "igte", 2 => do `($(← arg 0) ≥ $(← arg 1))
  -- records and tuples
  | "with", 3 => do
    let some fs := stxAt 1 | throwError "`with` expects a field name"
    let f := (strLitOf? fs).getD ""
    let fid := mkIdent (Name.mkSimple f)
    `({ $(← arg 0) with $fid:ident := $(← arg 2) })
  | "field", 2 => do
    let some fs := stxAt 1 | throwError "`field` expects a field name"
    let f := (strLitOf? fs).getD ""
    let fid := mkIdent (Name.mkSimple f)
    `(($(← arg 0)).$fid:ident)
  | "Tup", _ => do
    let ts ← all
    match ts with
    | #[a, b] => `(($a, $b))
    | #[a, b, c] => `(Quint.Tuple.Tup3.mk $a $b $c)
    | _ => throwError "`Tup` with {ts.size} components is not supported"
  | "q::debug", 2 => arg 1
  | _, _ =>
    -- an unknown operator: apply the Lean function of that name
    let argTs ← all
    let f := mkIdent (Name.mkSimple (leanStr name))
    `($f $argTs*)

/-- Parse a `quintOperDef`. -/
partial def parseOperDef (dd : Syntax) : QDef :=
  let qual := dd[0]
  let kind : DefKind :=
    let a := qual[0]
    let s := if a.isAtom then a.getAtomVal else if a.isIdent then a.getId.toString else
      (a[0].getAtomVal)
    match s with
    | "val" => .val
    | "def" => .def_
    | "pure" =>
      let b := a[1]
      let t := if b.isAtom then b.getAtomVal else if b.isIdent then b.getId.toString else b[0].getAtomVal
      if t == "val" then .pureVal else .pureDef
    | "action" => .action
    | "run" => .run
    | "temporal" => .temporal
    | "nondet" => .nondet
    | _ =>
      -- `&"pure" (&"val" <|> "def")` produces a group
      if a.getNumArgs == 2 then
        let t := a[1]
        let t := if t.isAtom then t.getAtomVal else t.getId.toString
        if t == "val" then .pureVal else .pureDef
      else .val
  let (name, _) := qualIdParts dd[1]
  let paramsOpt := dd[2]
  let params : Option (Array QParam) :=
    if paramsOpt.getNumArgs == 0 then none
    else some <| (sepArgs paramsOpt[1]).map fun p =>
      { name := paramName p[0], type? := if p[1].getNumArgs > 0 then some p[1][1] else none }
  let retType? := if dd[3].getNumArgs > 0 then some dd[3][1] else none
  let body := if dd[4].getNumArgs > 0 then dd[4][1] else Syntax.missing
  { kind, name, params, retType?, body, ref := dd }

end

/-! ## Actions -/

/-- Whether an expression is an action (it assigns, chooses, or calls an action). -/
partial def isAction (mod : ModInfo) (locals : Std.HashSet String) (stx : Syntax) : Bool :=
  if isApp stx then
    match asQualId? stx[0] with
    | some q =>
      let (n, fields) := qualIdParts q
      if fields.isEmpty then
        (match mod.defs[n]? with
          | some dd => dd.kind == .action && !locals.contains n
          | none => n == "assert")
        || (sepArgs stx[2]).any (isAction mod locals)
      else
        fields.getLast! == "then" || fields.getLast! == "reps" ||
          (mod.defs[fields.getLast!]?.map (·.kind == .action)).getD false
    | none =>
      match dot? stx[0] with
      | some (_, f) => (mod.defs[f]?.map (·.kind == .action)).getD false
      | none => false
  else
  match stx with
  | `(quint_expr| $_ = $_) => true
  | `(quint_expr| all { $_,* }) => true
  | `(quint_expr| any { $_,* }) => true
  | `(quint_expr| and { $es,* }) => es.getElems.any (isAction mod locals ·.raw)
  | `(quint_expr| or { $es,* }) => es.getElems.any (isAction mod locals ·.raw)
  | `(quint_expr| $a and $b) => isAction mod locals a || isAction mod locals b
  | `(quint_expr| $a or $b) => isAction mod locals a || isAction mod locals b
  | `(quint_expr| { $e:quint_expr }) => isAction mod locals e
  | `(quint_expr| ($e)) => isAction mod locals e
  | `(quint_expr| if ($_) $a else $b) => isAction mod locals a || isAction mod locals b
  | `(quint_expr| $dd:quintOperDef $b) =>
    let qd := parseOperDef dd
    qd.kind == .nondet || isAction mod (locals.insert qd.name) b
  | `(quint_expr| $_:quintValTuple $b) => isAction mod locals b
  | `(quint_expr| match $_ { $[|]? $c:quintMatchCase $[| $cs:quintMatchCase]* }) =>
    (#[c] ++ cs).any fun c => isAction mod locals c.raw[2]
  | `(quint_expr| $q:quintQualId) =>
    let (n, fields) := qualIdParts q
    fields.isEmpty && !locals.contains n && (mod.defs[n]?.map (·.kind == .action)).getD false
  | _ => false

/-- Variables (Quint names) assigned anywhere in an action, following calls of actions. -/
partial def assignedVars (mod : ModInfo) (stx : Syntax) (visited : Std.HashSet String := {}) :
    Std.HashSet String :=
  go stx {} visited
where
  go (s : Syntax) (acc : Std.HashSet String) (visited : Std.HashSet String) : Std.HashSet String :=
    let acc := match s with
      | `(quint_expr| $lhs = $_) =>
        match asQualId? lhs with
        | some q =>
          let (n, _) := qualIdParts q
          if n.endsWith "'" then acc.insert ((n.dropEnd 1).toString) else acc
        | none => acc
      | _ => acc
    let acc :=
      match asQualId? s with
      | some q =>
        let (n, fs) := qualIdParts q
        if fs.isEmpty && !visited.contains n then
          match mod.defs[n]? with
          | some dd => if dd.kind == .action then go dd.body acc (visited.insert n) else acc
          | none => acc
        else acc
      | none => acc
    s.getArgs.foldl (fun acc a => go a acc visited) acc

abbrev DoItems := Array (TSyntax ``Lean.Parser.Term.doSeqItem)

def mkDoSeq (items : DoItems) : TrM (TSyntax ``Lean.Parser.Term.doSeq) := do
  if items.isEmpty then
    `(Lean.Parser.Term.doSeq| pure ())
  else `(Lean.Parser.Term.doSeq| $items*)

def doItem (e : TSyntax `doElem) : TrM (TSyntax ``Lean.Parser.Term.doSeqItem) :=
  `(Lean.Parser.Term.doSeqItem| $e:doElem)

mutual

/-- Translate an action into `do` items. -/
partial def trAction (stx : Syntax) : TrM DoItems := withRef stx do
  let ctx ← read
  let localNames : Std.HashSet String := ctx.locals.fold (fun s k _ => s.insert k) {}
  if !isAction ctx.mod localNames stx then
    let c ← trExpr stx
    return #[← doItem (← `(doElem| require $c))]
  if isApp stx then
    match asQualId? stx[0] with
    | some q =>
      let (n, fields) := qualIdParts q
      if fields.isEmpty then
        if n == "assert" then
          let c ← trExpr (sepArgs stx[2])[0]!
          return #[← doItem (← `(doElem| assert $c))]
        if let some dd := ctx.mod.defs[n]? then
          if dd.kind == .action then
            let args ← (sepArgs stx[2]).mapM trExpr
            return ← inlineAction dd args
      else
        -- `r.f.A(args)`: the action `A` with the receiver as its first argument
        if let some dd := ctx.mod.defs[fields.getLast!]? then
          if dd.kind == .action then
            let mut recv ← trBaseName q n
            for f in fields.dropLast do recv ← trField recv f q
            let args ← (sepArgs stx[2]).mapM trExpr
            return ← inlineAction dd (#[recv] ++ args)
    | none =>
      if let some (e, f) := dot? stx[0] then
        if let some dd := ctx.mod.defs[f]? then
          if dd.kind == .action then
            let recv ← trExpr e
            let args ← (sepArgs stx[2]).mapM trExpr
            return ← inlineAction dd (#[recv] ++ args)
    throwErrorAt stx "unsupported action"
  match stx with
  | `(quint_expr| $lhs = $rhs) =>
    let some q := asQualId? lhs | throwErrorAt lhs "expected a primed variable"
    let (n, _) := qualIdParts q
    unless n.endsWith "'" do throwErrorAt lhs "expected a primed variable, e.g. `{n}'`"
    let v := (n.dropEnd 1).toString
    unless ctx.mod.vars.contains v do throwErrorAt lhs "`{v}` is not a state variable"
    let tgt := mkId n
    let r ← trExpr rhs
    return #[← doItem (← `(doElem| $tgt:ident := $r))]
  | `(quint_expr| all { $es,* }) | `(quint_expr| and { $es,* }) =>
    es.getElems.foldlM (fun acc e => return acc ++ (← trAction e)) #[]
  | `(quint_expr| $a and $b) => return (← trAction a) ++ (← trAction b)
  | `(quint_expr| any { $es,* }) | `(quint_expr| or { $es,* }) =>
    trChoice (es.getElems.map (·.raw))
  | `(quint_expr| $a or $b) => trChoice #[a, b]
  | `(quint_expr| { $e:quint_expr }) => trAction e
  | `(quint_expr| ($e)) => trAction e
  | `(quint_expr| if ($c) $a else $b) =>
    let c ← trExpr c
    let sa ← mkDoSeq (← trAction a)
    let sb ← mkDoSeq (← trAction b)
    return #[← doItem (← `(doElem| if $c then $sa else $sb))]
  | `(quint_expr| $dd:quintOperDef $body) =>
    let qd := parseOperDef dd
    if qd.kind == .nondet then
      trNondet qd (trAction body)
    else
      let v ← match qd.params with
        | some ps => if ps.isEmpty then trExpr qd.body else trLambdaNames (ps.map (·.name)).toList [] qd.body
        | none => trExpr qd.body
      bindLocal qd.name fun id => do
        let rest ← trAction body
        return #[← doItem (← `(doElem| let $id:ident := $v))] ++ rest
  | `(quint_expr| $q:quintQualId) =>
    let (n, _) := qualIdParts q
    match ctx.mod.defs[n]? with
    | some dd => inlineAction dd #[]
    | none => throwErrorAt stx "unknown action `{n}`"
  | `(quint_expr| $dd:quintValTuple $body) =>
    -- `val (a, b) = e` or `val { f, g } = e` before an action
    let patStx := dd.raw[2]
    let rhsT ← trExpr dd.raw[4]
    let x ← freshName "v"
    let names : Array String := if patStx[0].getAtomVal == "(" then (sepArgs patStx[1]).map paramName
      else (sepArgs patStx[1]).map identStr
    let isTuple := patStx[0].getAtomVal == "("
    let rec go (i : Nat) : TrM DoItems := do
      if h : i < names.size then
        let proj : Term ← if !isTuple then
            `(($x).$(mkIdent (Name.mkSimple names[i])):ident)
          else if names.size == 2 then (if i == 0 then `(($x).1) else `(($x).2))
          else `(($x).$(mkIdent (Name.mkSimple s!"_{i+1}")):ident)
        bindLocal names[i] fun id => do
          let rest ← go (i + 1)
          return #[← doItem (← `(doElem| let $id:ident := $proj))] ++ rest
      else trAction body
    return #[← doItem (← `(doElem| let $x:ident := $rhsT))] ++ (← go 0)
  | `(quint_expr| match $e { $[|]? $c:quintMatchCase $[| $cs:quintMatchCase]* }) =>
    -- compiled to `if T.isC e then (let x := T.getC e; ...) else ...`, which Veil's
    -- weakest-precondition machinery handles better than `match`
    let dTerm ← trExpr e
    let dId ← freshName "m"
    let rec goCases (cs : List Syntax) : TrM DoItems := do
      match cs with
      | [] => return #[← doItem (← `(doElem| assume False))]
      | c :: rest =>
        let pat := c[0]
        let rhs := c[2]
        let (lbl?, arg?) : Option String × Option Syntax :=
          match identLeaves pat with
          | [] => (none, none)
          | l :: _ =>
            let inner := if pat.getNumArgs == 1 then pat[0] else pat
            let argOpt := if inner.getNumArgs ≥ 2 then inner[1] else Syntax.missing
            (some (l.getId.toString (escape := false)),
             if argOpt.getNumArgs ≥ 3 then some argOpt[1] else none)
        match lbl? with
        | none => trAction rhs
        | some lbl =>
          let some info := (← read).mod.ctors[lbl]?
            | throwErrorAt pat "unknown variant `{lbl}`"
          let isId := mkIdent (info.typeName ++ Name.mkSimple ("is" ++ lbl))
          let getId := mkIdent (info.typeName ++ Name.mkSimple ("get" ++ lbl))
          let thenItems ← match arg? with
            | some p =>
              if paramName p == "_" then trAction rhs
              else bindLocal (paramName p) fun x => do
                return #[← doItem (← `(doElem| let $x:ident := $getId $dId))] ++ (← trAction rhs)
            | none => trAction rhs
          let elseItems ← goCases rest
          let t ← mkDoSeq thenItems
          let f ← mkDoSeq elseItems
          return #[← doItem (← `(doElem| if $isId $dId = true then $t else $f))]
    return #[← doItem (← `(doElem| let $dId:ident := $dTerm))] ++
      (← goCases ((#[c] ++ cs).toList.map (·.raw)))
  | _ => throwErrorAt stx "unsupported action"

/-- `nondet x = S.oneOf()`, followed by the items produced by `k`. -/
partial def trNondet (qd : QDef) (k : TrM DoItems) : TrM DoItems := do
  let rhs := unwrap qd.body
  -- `S.oneOf()` or `oneOf(S)`
  let setStx? : Option Syntax :=
    if isApp rhs then
      match asQualId? rhs[0] with
      | some q =>
        let (n, fs) := qualIdParts q
        if fs.getLast? == some "oneOf" then
          -- receiver is the qualified id without the last field
          some (Syntax.node .none `quintRecv #[q])
        else if n == "oneOf" && fs.isEmpty then (sepArgs rhs[2])[0]?
        else none
      | none =>
        match dot? rhs[0] with
        | some (e, f) => if f == "oneOf" then some e else none
        | none => none
    else none
  let some setStx := setStx? | throwErrorAt qd.body "`nondet` expects `S.oneOf()`"
  -- translate the set
  let (setT, inf?) ← match setStx with
    | .node _ `quintRecv #[q] =>
      let (n, fs) := qualIdParts q
      if fs.length == 1 && (n == "Int" || n == "Nat") then
        pure (← `(Int), some (if n == "Int" then InfSet.int else .nat))
      else if fs.length == 1 && n == "Bool" then
        pure (← `(Bool), some InfSet.bool)
      else
        let mut acc ← trBaseName q n
        for f in fs.dropLast do acc ← trField acc f q
        pure (acc, none)
    | s =>
      match infSetIn? (← read).mod s with
      | some i => pure (← `(Int), some i)
      | none =>
        match asQualId? (unwrap s) with
        | some q => if (qualIdParts q) == ("Bool", []) then pure (← `(Bool), some InfSet.bool)
                    else pure (← trExpr s, none)
        | none => pure (← trExpr s, none)
  bindLocal qd.name fun x => do
    let rest ← k
    match inf? with
    | some .bool => return #[← doItem (← `(doElem| let $x:ident ← pick Bool))] ++ rest
    | some .int => return #[← doItem (← `(doElem| let $x:ident ← pick Int))] ++ rest
    | some .nat =>
      return #[← doItem (← `(doElem| let $x:ident ← pick Int)),
               ← doItem (← `(doElem| assume $x ≥ 0))] ++ rest
    | none =>
      let sub ← freshName (qd.name ++ "_elem")
      let setId ← freshName (qd.name ++ "_set")
      return #[← doItem (← `(doElem| let $setId:ident := $setT)),
               ← doItem (← `(doElem| let $sub:ident : { y // y ∈ $setId } :| True)),
               ← doItem (← `(doElem| let $x:ident := ($sub).val))] ++ rest

/-- Non-deterministic choice between actions. -/
partial def trChoice (branches : Array Syntax) : TrM DoItems := do
  if h : branches.size = 1 then return ← trAction branches[0]
  let b ← freshName "choice"
  let first ← mkDoSeq (← trAction branches[0]!)
  let rest ← mkDoSeq (← trChoice branches[1:])
  return #[← doItem (← `(doElem| let $b:ident ← pick Bool)),
           ← doItem (← `(doElem| if $b:ident then $first else $rest))]

/-- Inline an action definition applied to translated arguments. -/
partial def inlineAction (dd : QDef) (args : Array Term) : TrM DoItems := do
  let ps := dd.params.getD #[]
  if ps.size != args.size then
    throwError "action `{dd.name}` expects {ps.size} arguments, got {args.size}"
  let mut items : DoItems := #[]
  let mut locals : Std.HashMap String Ident := {}
  for p in ps, a in args do
    if p.name == "_" then continue
    let id ← freshName p.name
    items := items.push (← doItem (← `(doElem| let $id:ident := $a)))
    locals := locals.insert p.name id
  let body ← withReader (fun c => { c with locals := locals }) (trAction dd.body)
  return items ++ body

end

/-- The body of a Veil action or `after_init` for a Quint action: local copies of the assigned
variables, the translated action, and the copy back into the state. -/
def trTopAction (stx : Syntax) : TrM (TSyntax ``Lean.Parser.Term.doSeq) := do
  let ctx ← read
  let assigned := assignedVars ctx.mod stx
  let vars := ctx.mod.varOrder.filter assigned.contains
  let mut pre : DoItems := #[]
  let mut post : DoItems := #[]
  for v in vars do
    let x := mkId v
    let x' := mkId (v ++ "'")
    pre := pre.push (← doItem (← `(doElem| let mut $x':ident := $x:ident)))
    post := post.push (← doItem (← `(doElem| $x:ident := $x':ident)))
  let body ← trAction stx
  mkDoSeq (pre ++ body ++ post)

/-! ## Splitting `step` into Veil actions -/

/-- A branch of the top-level choice in `step`: a prefix of `nondet`/`val` definitions and an
action. -/
structure Branch where
  prefix_ : Array Syntax
  act : Syntax
  name : String

/-- Split an action into the branches of its top-level `any` (through `nondet` and `val`
prefixes and through calls of action definitions without parameters). -/
partial def splitBranches (mod : ModInfo) (stx : Syntax) (prefix_ : Array Syntax := #[]) (depth := 0) :
    Array Branch :=
  let s := unwrap stx
  match s with
  | `(quint_expr| any { $es,* }) =>
    es.getElems.foldl (fun acc e => acc ++ splitBranches mod e prefix_ (depth + 1)) #[]
  | `(quint_expr| $dd:quintOperDef $body) =>
    splitBranches mod body (prefix_.push dd) depth
  | `(quint_expr| $q:quintQualId) =>
    let (n, fs) := qualIdParts q
    match mod.defs[n]? with
    | some dd =>
      if fs.isEmpty && dd.kind == .action && dd.params.all (·.isEmpty) && prefix_.isEmpty && depth ≤ 3 then
        let inner := splitBranches mod dd.body #[] (depth + 1)
        if inner.size > 1 then inner else #[{ prefix_, act := s, name := n }]
      else #[{ prefix_, act := s, name := n }]
    | none => #[{ prefix_, act := s, name := n }]
  | _ =>
    let name := if isApp s then
        match asQualId? s[0] with
        | some q => let (n, fs) := qualIdParts q; if fs.isEmpty then n else ""
        | none => ""
      else ""
    #[{ prefix_, act := s, name }]

/-! ## Declarations -/

/-- Translate the definitions `prefix_` (`nondet`, `val`, `def`) followed by the action. -/
partial def trPrefixed (prefix_ : List Syntax) (act : Syntax) : TrM DoItems := do
  match prefix_ with
  | [] => trAction act
  | dd :: ds =>
    let qd := parseOperDef dd
    if qd.kind == .nondet then trNondet qd (trPrefixed ds act)
    else
      let v ← match qd.params with
        | some ps => if ps.isEmpty then trExpr qd.body else trLambdaNames (ps.map (·.name)).toList [] qd.body
        | none => trExpr qd.body
      bindLocal qd.name fun id => do
        let rest ← trPrefixed ds act
        return #[← doItem (← `(doElem| let $id:ident := $v))] ++ rest

/-- `trTopAction` for a branch with a prefix. -/
def trTopBranch (b : Branch) : TrM (TSyntax ``Lean.Parser.Term.doSeq) := do
  let ctx ← read
  let assigned := b.prefix_.foldl (fun acc dd => acc.union (assignedVars ctx.mod dd))
    (assignedVars ctx.mod b.act)
  let vars := ctx.mod.varOrder.filter assigned.contains
  let mut pre : DoItems := #[]
  let mut post : DoItems := #[]
  for v in vars do
    let x := mkId v
    let x' := mkId (v ++ "'")
    pre := pre.push (← doItem (← `(doElem| let mut $x':ident := $x:ident)))
    post := post.push (← doItem (← `(doElem| $x:ident := $x':ident)))
  let body ← trPrefixed b.prefix_.toList b.act
  mkDoSeq (pre ++ body ++ post)

end Veil.Quint
