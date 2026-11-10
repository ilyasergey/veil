module

public meta import Lean
public meta import Veil.Frontend.Quint.Elab
public meta import Veil.Frontend.DSL.Module.Syntax

/-!
# Quint-style reports

`#quint_verify` and `#quint_run` run Veil's explicit-state model checker (`#model_check`) and
random simulator (`#simulate`) on the Quint module that is open, with the same arguments, and
report the result the way the quint tool does:

```
An example execution:

[State 0]
{
  bowl: Set("Gabriela", "Igor"),
  recipient_for_santa: Map()
}

[violation] Found an issue (412ms).
```

or `[ok] No violation found (288 distinct states, 95ms).` Variables appear under their Quint names,
sorted, with Quint's notation for values (`Set(…)`, `Map(k -> v)`, records `{ f: v }`). Veil's own
message and trace widget are kept as well.
-/

public meta section

namespace Veil.Quint
open Lean Elab Command

/-! ## Values in Quint notation -/

/-- A tiny parser for the values Veil prints: strings, `{…}` (sets, maps with `↦`, records with
`:`), `[…]`, `(…)`, and atoms. It rewrites sets and maps into Quint's notation. -/
partial def quintValue (s : String) (emptyBraces : String := "Set()") : String := Id.run do
  let cs := s.toList.toArray
  let rec go (i : Nat) (fuel : Nat) : String × Nat := Id.run do
    if fuel = 0 then return ("", i)
    -- skip spaces
    let mut i := i
    while i < cs.size && cs[i]! == ' ' do i := i + 1
    if i ≥ cs.size then return ("", i)
    let c := cs[i]!
    if c == '"' then
      let mut j := i + 1
      while j < cs.size && cs[j]! != '"' do
        j := if cs[j]! == '\\' then j + 2 else j + 1
      return (String.ofList (cs.extract i (j + 1)).toList, j + 1)
    if c == '{' || c == '[' || c == '(' then
      let close := if c == '{' then '}' else if c == '[' then ']' else ')'
      let mut items : Array String := #[]
      let mut j := i + 1
      let mut cur := ""
      let mut kind := ' '  -- '↦' map, ':' record, ' ' set/list/tuple
      while j < cs.size && cs[j]! != close do
        let ch := cs[j]!
        if ch == ' ' then j := j + 1
        else if ch == ',' then
          items := items.push cur; cur := ""; j := j + 1
        else if ch == '↦' then
          kind := '↦'; cur := cur ++ " -> "; j := j + 1
        else if ch == ':' && c == '{' then
          kind := ':'; cur := cur ++ ": "; j := j + 1
        else
          let (v, j') := go j (fuel - 1)
          cur := cur ++ v
          j := if j' == j then j + 1 else j'
      if cur != "" then items := items.push cur
      let body := ", ".intercalate items.toList
      let out :=
        if c == '{' then
          if items.isEmpty then emptyBraces
          else if kind == '↦' then s!"Map({body})"
          else if kind == ':' then "{ " ++ body ++ " }"
          else s!"Set({body})"
        else if c == '[' then s!"[{body}]" else s!"({body})"
      return (out, j + 1)
    -- an atom: up to a delimiter
    let mut j := i
    while j < cs.size && !(" ,{}[]()↦:".contains cs[j]!) do j := j + 1
    -- a constructor applied to a value: `Some("x")` or `Some 3`
    let atom := String.ofList (cs.extract i j).toList
    if j < cs.size && cs[j]! == '(' then
      let (arg, j') := go j (fuel - 1)
      return (atom ++ arg, j')
    return (atom, j)
  (go 0 10000).1

/-! ## Variables of the open module -/

/-- The variables of each Quint module: Lean field name, Quint name, and whether it is a map
(so that `{}` prints as `Map()`). Set by the module command. -/
initialize quintVarsExt : EnvExtension (Std.HashMap Name (Array (String × String × Bool))) ←
  registerEnvExtension (pure {})

/-! ## Reformatting Veil's result messages -/

structure StateDump where
  index : Nat
  fields : Array (String × String)

/-- Parse Veil's trace text (`State k (via a):` followed by `field = value` lines). -/
def parseStates (text : String) : Array StateDump := Id.run do
  let mut out : Array StateDump := #[]
  let mut cur : Option StateDump := none
  for line in text.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.startsWith "State " then
      if let some st := cur then out := out.push st
      let idx := ((t.drop 6).takeWhile Char.isDigit).toString.toNat!
      cur := some { index := idx, fields := #[] }
    else if let some st := cur then
      if t.startsWith "choices:" then continue
      match t.splitOn " = " with
      | f :: rest =>
        if rest.isEmpty then continue
        cur := some { st with fields := st.fields.push (f, " = ".intercalate rest) }
      | [] => pure ()
  if let some st := cur then out := out.push st
  return out

def renderStates (vars : Array (String × String × Bool)) (states : Array StateDump) : String := Id.run do
  let mut s := "An example execution:\n"
  for st in states do
    let fields := st.fields.map fun (f, v) =>
      match vars.find? (·.1 == f) with
      | some (_, q, isMap) => (q, quintValue v (if isMap then "Map()" else "Set()"))
      | none => (f, quintValue v)
    let fields := fields.qsort (fun (a b : String × String) => a.1 < b.1)
    s := s ++ s!"\n[State {st.index}]\n" ++ "{\n" ++
      ",\n".intercalate (fields.toList.map fun (f, v) => s!"  {f}: {v}") ++ "\n}\n"
  return s

/-- The Quint-style report of a Veil model-checking or simulation message. -/
def quintReport (vars : Array (String × String × Bool)) (msg : String) (ms : Nat) (depth? : Option Nat) :
    String := Id.run do
  if msg.contains '❌' then
    let violates := match msg.splitOn "violates: " with
      | _ :: rest :: _ => (rest.takeWhile (· != ')')).toString
      | _ => ""
    let states := parseStates msg
    let exec := if states.isEmpty then "" else renderStates vars states ++ "\n"
    return exec ++ s!"[violation] Found an issue ({ms}ms)." ++
      (if violates.isEmpty then "" else s!"\n  violates: {violates}")
  -- `✅ No liveness violation (checked N properties, …)` from `#temporal_check`
  if msg.contains '✅' && (msg.splitOn "No liveness violation").length > 1 then
    let n := match msg.splitOn "checked " with
      | _ :: rest :: _ => (rest.takeWhile Char.isDigit).toString
      | _ => "?"
    return s!"[ok] No violation found ({n} temporal properties, {ms}ms)."
  -- `✅ No violation (explored N states)` or `✅ No violation in N traces`
  match msg.splitOn "explored " with
  | _ :: rest :: _ =>
    let n := (rest.takeWhile Char.isDigit).toString
    let scope := match depth? with
      | some d => s!" up to {d} steps"
      | none => ""
    return s!"[ok] No violation found{scope} ({n} distinct states, {ms}ms)."
  | _ =>
  match msg.splitOn "No violation in " with
  | _ :: rest :: _ =>
    let n := (rest.takeWhile Char.isDigit).toString.toNat!
    let rate := if ms == 0 then n else n * 1000 / ms
    return s!"[ok] No violation found ({ms}ms at {rate} traces/second)."
  | _ => return s!"[error] {msg.take 300}"

/-- Elaborate `cmd` synchronously (as `#guard_msgs` does: Veil's checkers otherwise report
asynchronously) and return its messages, which stay in the message log, and the elapsed time. -/
def elabCollecting (cmd : Syntax) : CommandElabM (MessageLog × Nat) := do
  let saved := (← get).messages
  let savedTasks := (← get).snapshotTasks
  modify fun st => { st with messages := {}, snapshotTasks := #[] }
  let t0 ← IO.monoMsNow
  withReader ({ · with snap? := none }) do elabCommand cmd
  let ms := (← IO.monoMsNow) - t0
  let msgs := (← get).messages ++
    (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) .empty) .empty
  modify fun st => { st with messages := saved ++ msgs, snapshotTasks := savedTasks }
  return (msgs, ms)

/-- Elaborate `cmd`, keep its messages, and add a Quint-style report of its result. -/
def elabWithQuintReport (ref : Syntax) (cmd : Syntax) (depth? : Option Nat) : CommandElabM Unit := do
  let (msgs, ms) ← elabCollecting cmd
  let texts ← msgs.toList.mapM (·.data.toString)
  let some result := texts.reverse.find? (fun t => t.contains '✅' || t.contains '❌')
    | return
  let vars := (quintVarsExt.getState (← getEnv))[← getCurrNamespace]?.getD #[]
  logInfoAt ref (quintReport vars result ms depth?)

/-- The `maxDepth` set in a configuration, if any. -/
partial def maxDepthOf? (cfg : Syntax) : Option Nat :=
  let rec find (s : Syntax) : Option Nat :=
    if s.isIdent && s.getId == `maxDepth then none
    else
      let args := s.getArgs
      match args.findIdx? (fun a => a.isIdent && a.getId == `maxDepth) with
      | some i => (args[i + 2]?.bind (·.isNatLit?)).orElse fun _ =>
          (args[i + 2]?.bind fun a => (a.find? (·.isNatLit?.isSome)).bind (·.isNatLit?))
      | none => args.foldl (fun acc a => acc.orElse fun _ => find a) none
  find cfg

/-- `#quint_verify` takes the arguments of `#model_check`, runs it, and reports the result as
`quint verify` does. -/
syntax (name := quintVerify) "#quint_verify " (modelCheckMode)? term:max (term:max)?
  Lean.Parser.Tactic.optConfig : command

/-- `#quint_run` takes the arguments of `#simulate`, runs it, and reports the result as
`quint run` does. -/
syntax (name := quintRun) "#quint_run " (modelCheckMode)? term:max (term:max)?
  Lean.Parser.Tactic.optConfig : command

/-- `#quint_temporal [p_1] … [p_n]` takes the arguments of `#temporal_check`, runs it, and reports
the result as `quint verify --temporal=p_1,…` (with the TLC backend) does. -/
syntax (name := quintTemporal) "#quint_temporal " ("[" quint_ident "]")* (modelCheckMode)? term:max
  (term:max)? Lean.Parser.Tactic.optConfig : command

@[command_elab quintTemporal] def elabQuintTemporal : CommandElab := fun stx => do
  -- property names may be Veil keywords (e.g. `safety`)
  let names := stx[1].getArgs.map fun g =>
    let n := identStr g[1]
    Syntax.node .none ``Veil.propertyName
      #[mkAtomFrom g "[", mkIdentFrom g[1] (Name.mkSimple (leanStr n)), mkAtomFrom g "]"]
  let cmd := Syntax.node stx.getHeadInfo ``Veil.livenessCheck
    #[mkAtomFrom stx[0] "#temporal_check ", mkNullNode names, stx[2], stx[3], stx[4], stx[5],
      mkNullNode, mkNullNode]
  elabWithQuintReport stx cmd none

@[command_elab quintVerify] def elabQuintVerify : CommandElab := fun stx => do
  let cmd := Syntax.node stx.getHeadInfo ``Veil.modelCheck
    #[mkAtomFrom stx[0] "#model_check ", stx[1], stx[2], stx[3], stx[4], mkNullNode]
  elabWithQuintReport stx cmd (maxDepthOf? stx[4])

@[command_elab quintRun] def elabQuintRun : CommandElab := fun stx => do
  let cmd := Syntax.node stx.getHeadInfo ``Veil.simulate
    #[mkAtomFrom stx[0] "#simulate ", stx[1], stx[2], stx[3], stx[4], mkNullNode]
  elabWithQuintReport stx cmd none

end Veil.Quint
