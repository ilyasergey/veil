module

public import Veil.Quint

/-!
# Quint example `language-features/weakFairness.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/weakFairness.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

Weak fairness. Quint checks the temporal properties with TLC
(`quint verify --backend tlc --temporal ...`); the frontend translates them into Veil's temporal
logic (`weakFair(finish, vars)` is `𝒲ℱ finish`, `p leadsTo q` is `p ↝ q`), and `#quint_temporal`
checks them with Lasso, Veil's verified LTL model checker. As with TLC, the property without
fairness fails (the system may take `noop` forever).

Beyond model checking, the two properties that hold are proved deductively with Veil's temporal
proof mode (`prove_temporal_by`), by the rule WF1 of TLA: `not(done)` is stable until `done`, a
`finish` step establishes `done`, and `finish` is enabled while `not(done)`. The three premises
are first-order and discharged by SMT. The SMT answers are trusted (`veil.smt.trust`, Veil's
default); with proof reconstruction cvc5 currently rejects the query.
-/

-- A non-deterministic spec used to test weak fairness with leadsTo.
--
-- `step` can either finish (set done=true) or stutter. Without fairness,
-- the stutter branch can be chosen forever, so liveness doesn't hold.
-- With weak fairness for `finish`, since finish is continuously enabled when
-- done=false, it must eventually fire.
module weakFairness {
  var done: bool

  action init = done' = false

  -- Only enabled when done=false; sets done to true
  action finish = all { not(done), done' = true }

  -- Stutter: always enabled
  action noop = done' = done

  action step = any { finish, noop }

  val vars = done

  -- Holds with fairness: finish is constantly enabled when done=false, so weak
  -- fairness forces it to eventually fire.
  temporal eventuallyDone = weakFair(finish, vars) implies eventually(done)

  -- Holds with fairness: not(done) always leads to done
  temporal notDoneLeadsToDone = weakFair(finish, vars) implies (not(done) leadsTo done)

  -- Does NOT hold without fairness: there is an infinite stutter path
  temporal notDoneLeadsToDoneNoFairness = not(done) leadsTo done
}

ghost relation isDone := done = true
ghost relation notDone := done = false
#gen_spec
#quint_verify interpreted { } { }
#quint_temporal [eventuallyDone] [notDoneLeadsToDone] interpreted { } { }
set_option veil.violationIsError false in
#quint_temporal [notDoneLeadsToDoneNoFairness] interpreted { } { }

/-! ### Proofs of the two liveness properties (for every execution, by WF1) -/

open Lentil

temporal (only := verify) [notDoneLeadsToDoneProof]
  𝒲ℱ finish → (⌜ notDone ⌝ ↝ ⌜ isDone ⌝)

prove_temporal_by [notDoneLeadsToDoneProof]
  -- hInit : ⌜ Init ⌝, hNext : □⟨ NextStep ⟩, hInv : □⌜ Invariants ⌝
  tclear hInit hInv
  tintro hwf
  -- WF1 with p = notDone, q = isDone, a = finish
  trevert hNext hwf ; trewrite [← Lentil.and_imp]
  tapply wf1_original
  tsplit_ands
  -- (1) notDone is stable until isDone, (2) a `finish` step establishes isDone,
  -- (3) `finish` is enabled while notDone: each is about one transition
  all_goals tmonotone ; veil_solve_temporal

temporal (only := verify) [eventuallyDoneProof] 𝒲ℱ finish → ◇ ⌜ isDone ⌝

prove_temporal_by [eventuallyDoneProof]
  tclear hInv
  tintro hwf
  -- it suffices that notDone leads to isDone, since notDone holds initially
  tsuffices hleadsto :
   ⌜fun st => (veil_term% notDone) st⌝ ↝ ⌜fun st => (veil_term% isDone) st⌝ by
    tunfold leads_to at hleadsto
    thave himp := always_weaken hleadsto
    tapply himp
    tclear *- hInit
    veil_solve_temporal
  tclear hInit
  trevert hNext hwf ; trewrite [← Lentil.and_imp]
  tapply wf1_original
  tsplit_ands
  all_goals tmonotone ; veil_solve_temporal
end weakFairness
