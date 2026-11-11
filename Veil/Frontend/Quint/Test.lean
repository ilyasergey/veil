module

public meta import Lean
public meta import Veil.Frontend.Quint.Module
public meta import Veil.Frontend.Quint.Report

/-!
# Quint tests: `#quint_test M`

`#quint_test M` runs the tests of the Quint module `M` (the `run`s whose names end with `Test`;
`#quint_test M "pattern"` selects those whose names contain `pattern`), as `quint test` does.

A run is a sequence of actions, `A_0.then(A_1)...then(A_n)`, possibly with `.expect(P)` after a
step, `n.reps(_ => A)` (`n` a number or an expression over constants), and calls of other runs. `#quint_test` decomposes it into its steps and
checks it with a generated Quint module that imports `M` and adds a step counter:

```
module M__run_r {
  import M.*
  var quint_pc: int
  action quint_run_init = all { A_0, quint_pc' = 1 }
  action quint_run_step = any {
    all { quint_pc == 1, A_1, quint_pc' = 2 },
    ...
  }
  val quint_run_ok = and { quint_pc != k or P, ... }   // the expectations
  val quint_run_unfinished = quint_pc != n + 1
}
```

Veil's model checker then explores *every* execution of the run (not one random sample, as
`quint test` does): the run **passes** if some execution reaches its end and no execution violates
an expectation or an `assert`. The report says which of these fails otherwise.

`X.fail()` passes if no execution of `X` completes. A run may bind values before its steps:
`val x = e` is re-evaluated in each step, and `nondet x = S.oneOf()` is chosen once and kept in a
state variable of the test module (whose type comes from the declarations of `S`); `if (c) R1 else
R2` branches on `c`. Runs with parameters are checked through the runs that call them.

`#quint_test M` also runs the tests of each instance `import N(c = e, ...) as I` in `M`, as
`I::test` (on a test module that imports `N(c = e, ...).*`).

Set the environment variable `QUINT_TEST_DUMP` to a directory to write the generated test modules
there.
-/

public meta section

namespace Veil.Quint
open Lean Elab Command

/-- The source text of a syntax tree (from the file it was parsed from). -/
def sourceOf (stx : Syntax) : CommandElabM String := do
  if stx.getKind == `Veil.Quint.quintName then
    return stx[0].getId.toString (escape := false)
  let some p := stx.getPos? | throwErrorAt stx "this expression has no source position"
  let some e := stx.getTailPos? | throwErrorAt stx "this expression has no source position"
  -- the syntax may come from a module of another file
  match stx.getHeadInfo with
  | .original lead _ _ _ => return String.Pos.Raw.extract lead.str p e
  | _ => return String.Pos.Raw.extract (← getFileMap).source p e

/-! ### Types of `nondet` values

A `nondet` binding of a run becomes a state variable of the test module, which needs a type. It is
found syntactically, from the declared types of the constants, variables and definitions of `M`. -/

/-- Quint text of a type. -/
partial def typeText (stx : Syntax) : String :=
  if stx.isOfKind ``quintQualId then (qualIdParts stx).1
  else if stx.isAtom then stx.getAtomVal.trimAscii.toString
  else if stx.isIdent then stx.getId.toString (escape := false)
  else
    let parts := stx.getArgs.map typeText |>.filter (!·.isEmpty)
    let txt := " ".intercalate parts.toList
    ((txt.replace " [ " "[").replace " ]" "]").replace " ," ","

/-- Declared types: of constants, variables and definitions with a return type. -/
abbrev TyEnv := Std.HashMap String Syntax

/-- The element type of `Set[T]` and `List[T]`, and the key and value types of `K -> V`. -/
def setElem? (ty : Syntax) : Option Syntax :=
  if ty.getNumArgs == 4 && ty[1].isAtom && ty[1].getAtomVal == "[" then
    let ts := ty[2].getSepArgs
    if ts.size == 1 then some ts[0]! else none
  else none

def mapParts? (ty : Syntax) : Option (Syntax × Syntax) :=
  if ty.getNumArgs == 3 && ty[1].isAtom && ty[1].getAtomVal.trimAscii.toString == "->" then
    some (ty[0], ty[2])
  else none

/-- The Quint type of an expression, as text, when it is evident from the declarations. -/
partial def typeOfExpr (env : TyEnv) (defs : Std.HashMap String QDef) (stx : Syntax)
    (fuel : Nat := 16) : Option String := do
  if fuel == 0 then none
  let s := unwrap stx
  let ty (e : Syntax) := typeOfExpr env defs e (fuel - 1)
  let declTy (e : Syntax) : Option Syntax := do
    let e := unwrap e
    if e.getKind == `Veil.Quint.quintName then return ← env[e[0].getId.toString (escape := false)]?
    let q ← asQualId? e
    let (n, fs) := qualIdParts q
    unless fs.isEmpty do none
    env[n]?
  let elemOf (e : Syntax) : Option String := do
    if let some t := declTy e then
      if let some el := setElem? t then return typeText el
    let t ← ty e
    if t.startsWith "Set[" && t.endsWith "]" then return ((t.drop 4).dropEnd 1).toString
    none
  let s : Syntax := if s.getKind == `Veil.Quint.quintName then Syntax.node .none ``quintQualId #[s[0]]
    else (asQualId? s).getD s
  if s.isOfKind ``quintQualId then
    let (n, fs) := qualIdParts s
    unless fs.isEmpty do none
    if let some t := env[n]? then return typeText t
    let d ← defs[n]?
    if (d.params.getD #[]).isEmpty then return ← ty d.body
    none
  if (s.find? (·.isNatLit?.isSome)).isSome && s.getNumArgs ≤ 1 then return "int"
  if (strLitOf? s).isSome then return "str"
  let (op, args) ← callOf? s
  match op, args with
  | "oneOf", #[x] | "chooseSome", #[x] => elemOf x
  | "get", #[m, _] =>
    let t ← declTy m
    let (_, v) ← mapParts? t
    return typeText v
  | "keys", #[m] =>
    let t ← declTy m
    let (k, _) ← mapParts? t
    return s!"Set[{typeText k}]"
  | "exclude", #[x, _] | "union", #[x, _] | "intersect", #[x, _] | "filter", #[x, _] => ty x
  | "to", _ => return "Set[int]"
  | "size", _ => return "int"
  | "Set", xs => if xs.isEmpty then none else return s!"Set[{← ty xs[0]!}]"
  | _, _ => none

/-- The value of an integer expression over numerals and constants (`subst`: the values of the
constants given by `import M(c = e).*`), e.g. the number of repetitions in `n.reps(...)`. -/
partial def evalInt? (subst : Std.HashMap String Syntax) (stx : Syntax) (fuel : Nat := 32) :
    Option Int := do
  if fuel == 0 then none
  let s := unwrap stx
  let ev (e : Syntax) := evalInt? subst e (fuel - 1)
  if let some n := s.isNatLit? then return n
  if s.getNumArgs == 1 && !s.isOfKind ``quintQualId then return ← ev s[0]
  if s.isOfKind ``quintQualId then
    let (n, fs) := qualIdParts s
    unless fs.isEmpty do none
    return ← ev (← subst[n]?)
  if s.getNumArgs == 2 && s[0].isAtom && s[0].getAtomVal == "-" then return - (← ev s[1])
  if s.getNumArgs == 3 && s[1].isAtom then
    let a ← ev s[0]
    let b ← ev s[2]
    match s[1].getAtomVal.trimAscii.toString with
    | "+" => return a + b
    | "-" => return a - b
    | "*" => return a * b
    | "/" => return a / b
    | "%" => return a % b
    | _ => none
  none

/-! ### Runs as control-flow graphs -/

/-- A binding in scope of a step: `val x = e;` (re-evaluated in each step) or `nondet x = e;`,
whose value is kept in the state variable `var` from the step that chooses it on. -/
structure Bind where
  src : String
  nd? : Option (String × String) := none

/-- A step: from location `src` to `dst`, under the bindings `binds`, if the conditions `guards`
hold, performs the Quint action `act`. -/
structure Trans where
  src : Nat
  dst : Nat
  binds : Array Bind
  guards : Array String
  act : String
  /-- the `nondet` variables this step chooses -/
  fresh : Array (String × String)
deriving Inhabited

structure Cfg where
  next : Nat := 1
  trans : Array Trans := #[]
  /-- expectations: at location `k`, under the bindings, the condition holds -/
  expects : Array (Nat × Array Bind × String) := #[]
  /-- state variables of `nondet` values, with their types -/
  ndVars : Array (String × String) := #[]
  expectFail : Bool := false

abbrev CfgM := StateT Cfg CommandElabM

def renameLoc (a b : Nat) : CfgM Unit :=
  let r (k : Nat) := if k == a then b else k
  modify fun c => { c with
    trans := c.trans.map fun t => { t with src := r t.src, dst := r t.dst }
    expects := c.expects.map fun (k, bs, p) => (r k, bs, p) }

/-- Compile a run into steps from location `entry`; returns the location after it and the
`nondet` variables assigned on the way. `guards` are conditions for its first step. -/
partial def compileRun (env : TyEnv) (consts : Std.HashMap String Syntax)
    (defs runs : Std.HashMap String QDef) (stx : Syntax)
    (binds : Array Bind) (entry : Nat) (guards : Array String) (assigned : Std.HashSet String)
    (top : Bool) : CfgM (Nat × Std.HashSet String) := do
  let s := unwrap stx
  let go (e : Syntax) (binds : Array Bind) (entry : Nat) (guards : Array String)
      (assigned : Std.HashSet String) (top := false) :=
    compileRun env consts defs runs e binds entry guards assigned top
  let step : CfgM (Nat × Std.HashSet String) := do
    let src ← sourceOf s
    let fresh := binds.filterMap fun b => match b.nd? with
      | some (x, v) => if assigned.contains v then none else some (x, v)
      | none => none
    let c ← get
    set { c with next := c.next + 1,
                 trans := c.trans.push { src := entry, dst := c.next, binds, guards, act := src, fresh } }
    return (c.next, fresh.foldl (fun a (_, v) => a.insert v) assigned)
  if let some (op, args) := callOf? s then
    match op, args with
    | "then", #[a, b] =>
      let (k, asg) ← go a binds entry guards assigned
      return ← go b binds k #[] asg
    | "expect", #[a, p] =>
      let (k, asg) ← go a binds entry guards assigned
      let src ← sourceOf p
      modify fun c => { c with expects := c.expects.push (k, binds, src) }
      return (k, asg)
    | "reps", #[n, f] =>
      let some k := (evalInt? consts n).bind fun (k : Int) => if k ≥ 0 then some k.toNat else none
        | throwErrorAt n "`reps` needs a number of repetitions that does not depend on the state"
      let body := match lambda? f with
        | some (#[_], false, b) => b
        | _ => f
      let mut loc := entry
      let mut asg := assigned
      let mut gs := guards
      for _ in [0:k] do
        (loc, asg) ← go body binds loc gs asg
        gs := #[]
      return (loc, asg)
    | "fail", #[x] =>
      unless top do throwErrorAt s "`fail()` is only supported at the end of a test"
      modify fun c => { c with expectFail := true }
      return ← go x binds entry guards assigned
    | name, args =>
      -- a call of another run
      if let some rd := runs[name]? then
        let ps := rd.params.getD #[]
        if ps.size != args.size then throwErrorAt s "run `{name}` expects {ps.size} arguments"
        let mut b := binds
        for p in ps, a in args do
          b := b.push { src := s!"val {p.name} = {← sourceOf a};" }
        return ← go rd.body b entry guards assigned top
      return ← step
  match s with
  | `(quint_expr| $dd:quintOperDef $body) =>
    let qd := parseOperDef dd.raw
    let src := (← sourceOf dd.raw).trimAscii.toString
    let src := if src.endsWith ";" then src else src ++ ";"
    if qd.kind == .nondet then
      let some ty := typeOfExpr env defs qd.body
        | throwErrorAt dd "cannot find the type of this `nondet` value"
      let c ← get
      let v := s!"quint_nd_{c.ndVars.size}_{leanStr qd.name}"
      set { c with ndVars := c.ndVars.push (v, ty) }
      go body (binds.push { src, nd? := some (qd.name, v) }) entry guards assigned top
    else
      go body (binds.push { src }) entry guards assigned top
  | `(quint_expr| if ($c) $a else $b) =>
    let cs ← sourceOf c
    let (k1, asg1) ← go a binds entry (guards.push cs) assigned top
    let (k2, asg2) ← go b binds entry (guards.push s!"not({cs})") assigned top
    if k1 == entry || k2 == entry then throwErrorAt s "a branch of this `if` has no actions"
    renameLoc k2 k1
    return (k1, asg1.fold (fun a v => if asg2.contains v then a else a.erase v) asg1)
  | `(quint_expr| $q:quintQualId) =>
    let (n, fs) := qualIdParts q
    if fs.isEmpty then
      if let some rd := runs[n]? then
        if (rd.params.getD #[]).isEmpty then return ← go rd.body binds entry guards assigned top
    step
  | _ => step

/-- Quint text of the bindings: the `nondet` values of `fresh` are chosen, the others are read
from their state variables. -/
def bindsText (binds : Array Bind) (fresh : Array (String × String)) : String :=
  " ".intercalate (binds.map fun b => match b.nd? with
    | some (x, v) => if fresh.any (·.2 == v) then b.src else s!"val {x} = {v};"
    | none => b.src).toList

/-- The text of the test module for a run. -/
def testModuleText (header testName : String) (cfg : Cfg) (final : Nat) : String := Id.run do
  let branch (t : Trans) : String :=
    let conj := (if t.src == 0 then #[] else #[s!"quint_pc == {t.src}"]) ++ t.guards ++ #[t.act] ++
      #[s!"quint_pc' = {t.dst}"] ++ t.fresh.map (fun (x, v) => s!"{v}' = {x}")
    let body := "all { " ++ ", ".intercalate conj.toList ++ " }"
    if t.binds.isEmpty then body else "{ " ++ bindsText t.binds t.fresh ++ " " ++ body ++ " }"
  let inits := cfg.trans.filter (·.src == 0)
  let steps := cfg.trans.filter (·.src != 0)
  let anyOf (ts : Array Trans) : String :=
    if ts.size == 1 then branch ts[0]! else
    "any {\n    " ++ ",\n    ".intercalate (ts.map branch).toList ++ "\n  }"
  let init := s!"  action quint_run_init = {anyOf inits}\n"
  let step := if steps.isEmpty then "  action quint_run_step = all { quint_pc == 0, quint_pc' = 0 }\n"
    else s!"  action quint_run_step = {anyOf steps}\n"
  let expects := cfg.expects.map fun (k, bs, p) =>
    let p := if bs.isEmpty then p else "{ " ++ bindsText bs #[] ++ " " ++ p ++ " }"
    s!"quint_pc != {k} or ({p})"
  let ok := if expects.isEmpty then "true" else "and {\n    " ++ ",\n    ".intercalate expects.toList ++ "\n  }"
  let vars := cfg.ndVars.foldl (fun acc (v, ty) => acc ++ s!"  var {v}: {ty}\n") ""
  return s!"module {testName} \{\n  {header}\n  var quint_pc: int\n" ++ vars ++ init ++ step ++
    s!"  val quint_run_ok = {ok}\n  val quint_run_unfinished = quint_pc != {final}\n}"

/-- Elaborate `cmd` and return its messages, which are dropped from the log. -/
def elabQuiet (cmd : Syntax) : CommandElabM MessageLog := do
  let saved := (← get).messages
  let savedTasks := (← get).snapshotTasks
  modify fun st => { st with messages := {}, snapshotTasks := #[] }
  withReader ({ · with snap? := none }) do elabCommand cmd
  let msgs := (← get).messages ++
    (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) .empty) .empty
  modify fun st => { st with messages := saved, snapshotTasks := savedTasks }
  return msgs

def elabQuietString (src : String) : CommandElabM MessageLog := do
  match Parser.runParserCategory (← getEnv) `command src with
  | .ok stx => elabQuiet stx
  | .error e => throwError "internal error in a generated test: {e}\n{src}"

/-- The outcome of one run. -/
inductive RunOutcome where
  | passed (states : Nat)
  | failed (why : String)
  | notChecked (why : String)

/-- Check one run, on a test module with this `import`. -/
def checkRun (header testName : String) (env : TyEnv) (consts : Std.HashMap String Syntax)
    (defs runs : Std.HashMap String QDef) (rd : QDef) :
    CommandElabM RunOutcome := do
  let r ← try
      let ((final, _), cfg) ← (compileRun env consts defs runs rd.body #[] 0 #[] {} true).run {}
      pure (Except.ok (final, cfg))
    catch ex => pure (Except.error (← ex.toMessageData.toString))
  let (final, cfg) ← match r with
    | .ok v => pure v
    | .error e => return .notChecked e
  let expectFail := cfg.expectFail
  if cfg.trans.isEmpty then
    return .notChecked "the run has no steps"
  let text := testModuleText header testName cfg final
  trace[veil.debug] m!"Quint test module:\n{text}"
  if let some f ← IO.getEnv "QUINT_TEST_DUMP" then IO.FS.writeFile (f ++ "/" ++ testName ++ ".lean") text
  -- elaborate the test module with its own initial and step actions
  let opts ← getOptions
  let opts := ((((opts.set `quint.init "quint_run_init").set `quint.step "quint_run_step").set
    `quint.skipParametric false).set `veil.violationIsError false : Options)
  withScope (fun sc => { sc with opts }) do
    let msgs ← elabQuietString text
    if msgs.hasErrors then
      let errs ← msgs.toList.filter (·.severity == .error) |>.mapM (·.toString)
      let _ ← elabQuietString s!"end {leanStr testName}"
      modifyEnv (quintOpenModuleExt.setState · none)
      return .notChecked s!"the test module does not elaborate: {errs.headD ""}"
    -- 1. no execution violates an expectation or an assertion
    let _ ← elabQuietString "quint_invariant quint_run_ok"
    let _ ← elabQuietString "#gen_spec"
    let m1 ← elabQuietString "#model_check interpreted { } { }"
    let t1 ← m1.toList.mapM (·.data.toString)
    let r1 := t1.find? (fun t => t.contains '✅' || t.contains '❌') |>.getD (t1.headD "no result")
    if !(r1.contains '✅' || r1.contains '❌') then
      let _ ← elabQuietString s!"end {leanStr testName}"
      modifyEnv (quintOpenModuleExt.setState · none)
      return .notChecked s!"the model checker stopped: {(r1.splitOn "\n").headD r1}"
    if r1.contains '❌' then
      let _ ← elabQuietString s!"end {leanStr testName}"
      modifyEnv (quintOpenModuleExt.setState · none)
      let what := if (r1.splitOn "assertion").length > 1 then "an assertion fails"
        else "an expectation does not hold"
      return .failed s!"on some execution, {what}"
    let states := match r1.splitOn "explored " with
      | _ :: rest :: _ => (rest.takeWhile Char.isDigit).toString.toNat!
      | _ => 0
    let _ ← elabQuietString s!"end {leanStr testName}"
    modifyEnv (quintOpenModuleExt.setState · none)
    -- 2. some execution reaches the end of the run: `quint_run_unfinished` is violated
    let text2 := text.replace s!"module {testName} " s!"module {testName}_end "
    let _ ← elabQuietString text2
    let _ ← elabQuietString "quint_invariant quint_run_unfinished"
    let _ ← elabQuietString "#gen_spec"
    let m2 ← elabQuietString "#model_check interpreted { } { }"
    let _ ← elabQuietString s!"end {leanStr testName}_end"
    modifyEnv (quintOpenModuleExt.setState · none)
    let t2 ← m2.toList.mapM (·.data.toString)
    let completes := t2.any (·.contains "violates: quint_run_unfinished")
    if expectFail then
      if completes then return .failed "an execution completes the run, but `fail()` expects none to"
      return .passed states
    if completes then return .passed states
    -- the model checker may have stopped with an error instead of a verdict
    if let some err := t2.find? (fun t => t.contains "💥" || t.contains "could not" || t.contains "rror") then
      return .notChecked s!"the model checker stopped: {(err.splitOn "\n").headD err}"
    if m2.hasErrors then
      let errs ← m2.toList.filter (·.severity == .error) |>.mapM (·.toString)
      return .notChecked s!"the model checker stopped: {((errs.headD "").splitOn "\n").headD ""}"
    return .failed "no execution reaches the end of the run (a step is never enabled)"

/-- `#quint_test M` runs the `run`s of the Quint module `M` (see the module docstring). -/
syntax (name := quintTestCmd) "#quint_test " quintQualId (str)? : command

/-- Whether a run is a test: by default, its name ends with `Test` (as for `quint test`); with a
pattern, the name contains it (`^p` and `p$` anchor it at the start or the end). -/
def isTestName (pat? : Option String) (n : String) : Bool :=
  match pat? with
  | none => n.endsWith "Test"
  | some p =>
    if p.startsWith "^" && p.endsWith "$" then n == ((p.drop 1).dropEnd 1).toString
    else if p.startsWith "^" then n.startsWith (p.drop 1).toString
    else if p.endsWith "$" then n.endsWith (p.dropEnd 1).toString
    else (n.splitOn p).length > 1

@[command_elab quintTestCmd] def elabQuintTest : CommandElab := fun stx => do
  -- close the Quint module that is still open, so that the test modules are top-level
  if let some prev := quintOpenModuleExt.getState (← getEnv) then
    if (← getCurrNamespace) == prev then
      elabCommand (← `(end $(mkIdent prev)))
    modifyEnv (quintOpenModuleExt.setState · none)
  let (modStr, _) := qualIdParts stx[1]
  let some mstx := (quintModuleExt.getState (← getEnv)).find? (Name.mkSimple modStr)
    | throwErrorAt stx[1] "unknown Quint module `{modStr}`"
  -- the runs of `M` (with those of the modules it imports), and those of the instances that `M`
  -- imports with `import N(c = e, ...) as I`, tested on a module that imports the instance
  let isInstanceAs (dcl : Syntax) := dcl.isOfKind ``quintInstance && (asPrefix? dcl[5]).isSome
  let own := mstx[3].getArgs.filter (!isInstanceAs ·)
  let mut targets : Array (String × String × Array Syntax) := #[("", s!"import {modStr}.*", own)]
  for dcl in mstx[3].getArgs do
    unless isInstanceAs dcl do continue
    let (n, _) := qualIdParts dcl[1]
    let some nstx := (quintModuleExt.getState (← getEnv)).find? (Name.mkSimple n) | continue
    let some i := asPrefix? dcl[5] | continue
    let args ← dcl[3].getSepArgs.mapM fun a => return s!"{← sourceOf a}"
    targets := targets.push (i ++ "::", s!"import {n}({", ".intercalate args.toList}).*",
      nstx[3].getArgs.filter (!isInstanceAs ·))
  let t0 ← IO.monoMsNow
  let mut lines : Array String := #[s!"  {modStr}"]
  let mut passing := 0
  let mut failing := 0
  let mut skipped := 0
  let pat? := (stx[2].getOptional?).bind (·.isStrLit?)
  for (pfx, header, decls) in targets do
    let items ← expandImports decls
    -- the values of the constants: from the instances, and `pure val`s without parameters
    let consts : Std.HashMap String Syntax := items.foldl (fun m it => m.union it.subst) {}
    let defs := items.map (·.decl) |>.filter (·.isOfKind ``quintOper) |>.map (parseOperDef ·[0])
    let runs : Std.HashMap String QDef := defs.foldl (fun m d =>
      if d.kind == .run then m.insert d.name d else m) {}
    let defMap : Std.HashMap String QDef := defs.foldl (fun m d => m.insert d.name d) {}
    let consts := defs.foldl (fun m d =>
      if d.kind == .pureVal && (d.params.getD #[]).isEmpty && !m.contains d.name then
        m.insert d.name d.body else m) consts
    let env : TyEnv := items.foldl (fun m it =>
      let dcl := it.decl
      if dcl.isOfKind ``quintConst || dcl.isOfKind ``quintVar then
        m.insert (qualIdParts (dcl.getArg 1)).1 (dcl.getArg 3)
      else m) {}
    let env := defs.foldl (fun m d => match d.retType? with
      | some t => if (d.params.getD #[]).isEmpty then m.insert d.name t else m
      | none => m) env
    for d in defs do
      unless d.kind == .run && (d.params.getD #[]).isEmpty && isTestName pat? d.name do continue
      let name := pfx ++ d.name
      let testName := s!"{leanStr modStr}__run_{leanStr (pfx.replace "::" "_")}{leanStr d.name}"
      match ← checkRun header testName env consts defMap runs d with
      | .passed n =>
        passing := passing + 1
        lines := lines.push s!"    ok {name} passed (every execution, {n} states)"
      | .failed why =>
        failing := failing + 1
        lines := lines.push s!"    ✗ {name} failed: {why}"
      | .notChecked why =>
        skipped := skipped + 1
        lines := lines.push s!"    - {name} not checked: {why}"
  let ms := (← IO.monoMsNow) - t0
  lines := lines.push ""
  lines := lines.push s!"  {passing} passing, {failing} failing, {skipped} not checked ({ms}ms)"
  logInfoAt stx ("\n".intercalate lines.toList)

end Veil.Quint
