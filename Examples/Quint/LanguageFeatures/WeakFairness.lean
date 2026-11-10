module

public import Veil.Quint

/-!
# Quint example `language-features/weakFairness.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/weakFairness.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The module elaborates into a Veil module; no Veil checks are configured for it.
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

#gen_spec
#quint_verify interpreted { } { }
end weakFairness
