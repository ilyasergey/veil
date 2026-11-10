module

public meta import Lean
public meta import Veil.Frontend.Quint.Module
public meta import Veil.Frontend.Quint.Report

/-!
# Quint tests: `#quint_test M`

`#quint_test M` runs the tests of the Quint module `M` (the `run`s whose names end with `Test`;
`#quint_test M "pattern"` selects those whose names contain `pattern`), as `quint test` does.

A run is a sequence of actions, `A_0.then(A_1)...then(A_n)`, possibly with `.expect(P)` after a
step, `n.reps(_ => A)`, and calls of other runs. `#quint_test` decomposes it into its steps and
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

`X.fail()` passes if no execution of `X` completes. Runs with parameters are checked through the
runs that call them; runs that start with `nondet`, and `fail()` inside a run, are reported as not
checked.
-/

public meta section

namespace Veil.Quint
open Lean Elab Command

/-- A step of a run: an action (as Quint source text) or an expectation after the last step. -/
inductive RunStep where
  | act (src : String)
  | expect (src : String)

/-- The source text of a syntax tree in the current file. -/
def sourceOf (stx : Syntax) : CommandElabM String := do
  if stx.getKind == `Veil.Quint.quintName then
    return stx[0].getId.toString (escape := false)
  let some p := stx.getPos? | throwErrorAt stx "this expression has no source position"
  let some e := stx.getTailPos? | throwErrorAt stx "this expression has no source position"
  return (String.Pos.Raw.extract (← getFileMap).source p e)

/-- Decompose a run into its steps. `runs` gives the other runs of the module (for calls), with
their parameters; `binds` are `val` bindings of parameters to prepend to each step. -/
partial def runSteps (runs : Std.HashMap String QDef) (stx : Syntax) (binds : String := "") :
    CommandElabM (Array RunStep) := do
  let s := unwrap stx
  let wrap (src : String) : String := if binds.isEmpty then src else "{ " ++ binds ++ " " ++ src ++ " }"
  if let some (op, args) := callOf? s then
    match op, args with
    | "then", #[a, b] => return (← runSteps runs a binds) ++ (← runSteps runs b binds)
    | "expect", #[a, p] => return (← runSteps runs a binds).push (.expect (wrap (← sourceOf p)))
    | "reps", #[n, f] =>
      let some k := ((unwrap n).find? (·.isNatLit?.isSome)).bind (·.isNatLit?)
        | throwErrorAt n "`reps` needs a literal number of repetitions"
      return ← repeatBody runs f k binds
    | "fail", _ => throwErrorAt s "`fail()` is not supported by `#quint_test`"
    | name, args =>
      -- a call of another run
      if let some rd := runs[name]? then
        let ps := rd.params.getD #[]
        if ps.size != args.size then throwErrorAt s "run `{name}` expects {ps.size} arguments"
        let mut b := binds
        for p in ps, a in args do
          b := b ++ s!"val {p.name} = {← sourceOf a}; "
        return ← runSteps runs rd.body b
      return #[.act (wrap (← sourceOf s))]
  match s with
  | `(quint_expr| $_:quintOperDef $_) => throwErrorAt s "runs that start with definitions (e.g. `nondet`) are not supported by `#quint_test`"
  | `(quint_expr| $q:quintQualId) =>
    let (n, fs) := qualIdParts q
    if fs.isEmpty then
      if let some rd := runs[n]? then
        if (rd.params.getD #[]).isEmpty then return ← runSteps runs rd.body binds
    return #[.act (wrap (← sourceOf s))]
  | _ => return #[.act (wrap (← sourceOf s))]
where
  repeatBody (runs : Std.HashMap String QDef) (f : Syntax) (k : Nat) (binds : String) :
      CommandElabM (Array RunStep) := do
    let body := match lambda? f with
      | some (#[_], false, b) => b
      | _ => f
    let one ← runSteps runs body binds
    return (List.replicate k one).foldl (· ++ ·) #[]

/-- The text of the test module for a run with these steps. -/
def testModuleText (modName testName : String) (steps : Array RunStep) : String := Id.run do
  let acts := steps.filterMap fun | .act a => some a | _ => none
  let mut expects : Array String := #[]
  let mut k := 0
  for st in steps do
    match st with
    | .act _ => k := k + 1
    | .expect p => expects := expects.push s!"quint_pc != {k} or ({p})"
  let init := s!"  action quint_run_init = all \{ {acts[0]!}, quint_pc' = 1 }\n"
  let stepBranches := (List.range (acts.size - 1)).map fun i =>
    s!"    all \{ quint_pc == {i + 1}, {acts[i + 1]!}, quint_pc' = {i + 2} },"
  let step := if acts.size ≤ 1 then "  action quint_run_step = all { quint_pc == 0, quint_pc' = 0 }\n"
    else "  action quint_run_step = any {\n" ++ "\n".intercalate stepBranches ++ "\n  }\n"
  let ok := if expects.isEmpty then "true" else "and {\n    " ++ ",\n    ".intercalate expects.toList ++ "\n  }"
  return s!"module {testName} \{\n  import {modName}.*\n  var quint_pc: int\n" ++ init ++ step ++
    s!"  val quint_run_ok = {ok}\n  val quint_run_unfinished = quint_pc != {acts.size}\n}"

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

/-- Check one run of module `modName`. -/
def checkRun (modName : String) (runs : Std.HashMap String QDef) (rd : QDef) :
    CommandElabM RunOutcome := do
  -- `X.fail()`: the run passes iff no execution of `X` completes
  let (body, expectFail) := match callOf? (unwrap rd.body) with
    | some ("fail", #[x]) => (x, true)
    | _ => (rd.body, false)
  let steps ← try runSteps runs body
    catch ex => return .notChecked (← ex.toMessageData.toString)
  if steps.isEmpty || !(steps.any fun | .act _ => true | _ => false) then
    return .notChecked "the run has no steps"
  let testName := s!"{leanStr modName}__run_{leanStr rd.name}"
  let text := testModuleText modName testName steps
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
  let (modStr, _) := qualIdParts stx[1]
  let some mstx := (quintModuleExt.getState (← getEnv)).find? (Name.mkSimple modStr)
    | throwErrorAt stx[1] "unknown Quint module `{modStr}`"
  let decls := mstx[3].getArgs.filter (·.isOfKind ``quintOper)
  let defs := decls.map (parseOperDef ·[0])
  let runs : Std.HashMap String QDef := defs.foldl (fun m d =>
    if d.kind == .run then m.insert d.name d else m) {}
  let t0 ← IO.monoMsNow
  let mut lines : Array String := #[s!"  {modStr}"]
  let mut passing := 0
  let mut failing := 0
  let mut skipped := 0
  let pat? := (stx[2].getOptional?).bind (·.isStrLit?)
  for d in defs do
    unless d.kind == .run && (d.params.getD #[]).isEmpty && isTestName pat? d.name do continue
    match ← checkRun modStr runs d with
    | .passed n =>
      passing := passing + 1
      lines := lines.push s!"    ok {d.name} passed (every execution, {n} states)"
    | .failed why =>
      failing := failing + 1
      lines := lines.push s!"    ✗ {d.name} failed: {why}"
    | .notChecked why =>
      skipped := skipped + 1
      lines := lines.push s!"    - {d.name} not checked: {why}"
  let ms := (← IO.monoMsNow) - t0
  lines := lines.push ""
  lines := lines.push s!"  {passing} passing, {failing} failing, {skipped} not checked ({ms}ms)"
  logInfoAt stx ("\n".intercalate lines.toList)

end Veil.Quint
