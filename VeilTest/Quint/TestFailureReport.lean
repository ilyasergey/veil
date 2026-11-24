module
public import Veil.Quint

/-! `#quint_test` reports a failing run as an error, at the run and at `#quint_test`, with the
expectation that does not hold and an execution that violates it, in Quint's format. -/

module counterRuns {
  var t: int
  action init = t' = 0
  action step = all { t < 5, t' = t + 1 }
  run goodTest = init.then(step).then(step).expect(t == 2)
  run badTest = init.then(step).then(step).expect(t == 3)
}
#gen_spec
end counterRuns

/--
error: [test] badTest failed: on some execution, this expectation does not hold:
      .expect(t == 3)

An example execution:

[State 0]
{
  t: 0
}

[State 1]
{
  t: 1
}

[State 2]
{
  t: 2
}
---
error:   counterRuns
    ok goodTest passed (every execution, 3 states)
    ✗ badTest failed: on some execution, this expectation does not hold:
      .expect(t == 3)
-/
#guard_msgs (substring := true) in
#quint_test counterRuns

/-! With `veil.violationIsError false`, the same report is information. -/

module counterRuns2 {
  var t: int
  action init = t' = 0
  action step = all { t < 5, t' = t + 1 }
  run badTest = init.then(step).expect(t == 3)
}
#gen_spec
end counterRuns2

/--
info: [test] badTest failed
-/
#guard_msgs (substring := true) in
set_option veil.violationIsError false in
#quint_test counterRuns2
