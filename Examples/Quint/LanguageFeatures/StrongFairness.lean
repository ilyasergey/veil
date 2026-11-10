module

public import Veil.Quint

/-!
# Quint example `language-features/strongFairness.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/strongFairness.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

Strong fairness. `weakFair(step, vars)` is fairness of the whole step, which
the frontend splits into one Veil action per branch: it becomes weak fairness of their
disjunction, `(◇ □ (Enabled a_1 ∨ …)) → □ ◇ (⟨ a_1 ⟩ ∨ …)`. As with TLC,
`eventuallyHundredDegrees` holds and `eventuallyHundredDegreesWeakOnly` does not.
-/

module strongFairness {
  type KettleState = RoomTemperature | Heating | Cooling | HundredDegrees

  var kettle: KettleState

  action init = kettle' = RoomTemperature

  action turnOn = all { kettle == RoomTemperature, kettle' = Heating }

  action turnOff = all { kettle == Heating, kettle' = Cooling }

  action turnOffBySensor = all { kettle == Heating, kettle' = HundredDegrees }

  action stabilize = any {
    all { kettle == HundredDegrees, kettle' = Cooling },
    all { kettle == Cooling, kettle' = RoomTemperature },
  }

  action step = any { turnOn, turnOff, turnOffBySensor, stabilize }

  val vars = kettle

  -- Holds with weak fairness over step and strong fairness on turnOffBySensor.
  -- turnOffBySensors is infinitely often enabled, but not constantly, so it needs strong fairness.
  temporal eventuallyHundredDegrees =
    (weakFair(step, vars) and strongFair(turnOffBySensor, vars)) implies eventually(kettle == HundredDegrees)

  -- Does NOT hold with weak fairness alone,
  -- as whe can choose turnOff instead of turnOffBySensor every single time.
  temporal eventuallyHundredDegreesWeakOnly =
    weakFair(step, vars) implies eventually(kettle == HundredDegrees)
}

#gen_spec
#quint_verify interpreted { } { }
#quint_temporal [eventuallyHundredDegrees] interpreted { } { }
set_option veil.violationIsError false in
#quint_temporal [eventuallyHundredDegreesWeakOnly] interpreted { } { }
end strongFairness
