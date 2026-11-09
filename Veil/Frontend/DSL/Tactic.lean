module

public meta import Veil.Frontend.DSL.Tactic.Core
public meta import Smt

public meta section

open Lean Elab Tactic Meta Simp Tactic.TryThis Parser.Tactic
namespace Veil

private def mkVeilSmtTactic : TacticM (TSyntax `tactic) := do
  let idents ← getPropsInContext
  let opts ← getOptions
  let fmfEnabled := veil.smt.finiteModelFind.get opts
  let timeout := veil.smt.timeout.get opts
  let trustEnabled := veil.smt.trust.get opts
  let fmfValue := if fmfEnabled then "true" else "false"
  let trustSmt := mkIdent <| if trustEnabled then ``true else ``false
  let embedBool := mkIdent <| if trustEnabled then ``false else ``true
  let solverOptions ← `(term| [("finite-model-find", $(Syntax.mkStrLit fmfValue)), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")])
  let smtTac ← `(tactic|
    open $(mkIdent `Classical):ident in
    smt
      ($(mkIdent `trust):ident := $trustSmt:ident)
      ($(mkIdent `embedBool):ident := $embedBool:ident)
      ($(mkIdent `model):ident := $(mkIdent ``true))
      ($(mkIdent `timeout):ident := $(mkIdent ``Option.some) $(quote timeout))
      ($(mkIdent `extraSolverOptions):ident := $solverOptions)
      [$[$idents:ident],*])
  if trustEnabled then
    return smtTac
  else
    return ← `(tactic| (veil_infer_nonempty; $smtTac:tactic))

/-- Unfold `CanonicalField` and `IteratedArrow` in the goal and the hypotheses. lean-smt
recognises numerals and arithmetic by their type argument (e.g. `@OfNat.ofNat Int 0 _`), so it
cannot translate them when the type is still written as `CanonicalField [] Int` (an `Int`-valued
`individual`, as in `x := 0`). The synthesizer does the same before calling the solver. -/
def unfoldCanonicalFieldTypes (g : MVarId) : MetaM MVarId := g.withContext do
  let unfold (e : Expr) : MetaM Expr := Meta.transform e (post := fun e ↦ do
    if e.isAppOfArity ``Veil.CanonicalField 2 || e.isAppOfArity ``Veil.IteratedArrow 2 then
      let e' ← whnfR e
      if e' != e then return .visit e'
    return .continue)
  let ty ← instantiateMVars (← g.getType)
  let ty' ← unfold ty
  let mut g ← if ty' != ty then g.replaceTargetDefEq ty' else pure g
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let dty ← instantiateMVars decl.type
    let dty' ← unfold dty
    if dty' != dty then g ← g.replaceLocalDeclDefEq decl.fvarId dty'
  return g

def elabVeilSmt (stx : Syntax) (trace : Bool := false) : DesugarTacticM Unit := withBackwardsCompatibility <| veilWithMainContext do
  liftMetaTactic1 fun g => some <$> unfoldCanonicalFieldTypes g
  -- It's necessary to `open Classical` to make proof reconstruction work.
  -- Otherwise, sometimes it fails due to failing to infer `Decidable` instances.
  let auto_tac ← mkVeilSmtTactic
  if trace then
    addSuggestion stx auto_tac
  else
    veilEvalTactic auto_tac

@[tactic veil_smt, tactic veil_smt_trace]
def elabVeilSmtTactics : Tactic := fun stx => do
  let res : DesugarTacticM Unit :=
  match stx with
  | `(tactic| veil_smt%$tk) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_smt") $ elabVeilSmt tk
  | `(tactic| veil_smt?%$tk) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_smt?") $ elabVeilSmt tk true
  | _ => throwUnsupportedSyntax
  res.runByOption stx

end Veil
