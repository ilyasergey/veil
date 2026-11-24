module
public import Veil.Quint

/-! `invariant` and `observation` definitions (Quint 0.34): the invariants of a module are Veil
invariants without a `quint_invariant` command, and naming one in `quint_invariant` again is
accepted. `Rec("f", e, ...)` is the record `{ f: e, ... }`. -/

module counter {
  var t: int
  val r = Rec("name", "igor", "year", 1981)
  action init = t' = 0
  action step = all { t < 5, t' = t + 1 }
  invariant nonNegative = t >= 0
  invariant bounded = t <= 5 and r.year == 1981 and r == { name: "igor", year: 1981 }
  observation advanced = t > 3
  val other = t < 100
}
quint_invariant other, bounded
#gen_spec

/-- info: ✅ No violation (explored 6 states) -/
#guard_msgs (info, drop warning) in
#model_check { } { }
end counter

/-! A declared invariant that does not hold is reported. -/

module counter2 {
  var t: int
  action init = t' = 0
  action step = all { t < 5, t' = t + 1 }
  invariant small = t <= 3
}
#gen_spec

/--
error: ❌ Violation: safety_failure (violates: small)
  State 0 (via init):
    t = 0
  State 1 (via step_1):
    t = 1
  State 2 (via step_1):
    t = 2
  State 3 (via step_1):
    t = 3
  State 4 (via step_1):
    t = 4
-/
#guard_msgs (error, drop info, drop warning) in
#model_check { } { }
end counter2

/-! `quint.declaredInvariants false` is `--no-invariant`. -/

set_option quint.declaredInvariants false
module counter3 {
  var t: int
  action init = t' = 0
  action step = all { t < 5, t' = t + 1 }
  invariant small = t <= 3
}
#gen_spec

/-- info: ✅ No violation (explored 6 states) -/
#guard_msgs (info, drop warning) in
#model_check { } { }
end counter3
