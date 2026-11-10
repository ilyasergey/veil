module

public import Veil.Quint

/-!
# Quint example `language-features/nondetEx.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/nondetEx.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

Nondeterminism. `mirrorInv` is checked by depth-bounded model checking, by
simulation, and by Veil's symbolic bounded model checker (`quint_bmc`, SMT) for every execution of
up to three steps.
-/

-- demonstrating non-trivial behavior of nondet and oneOf
module nondetEx {
  var x: int
  var y: int
  var delta: int
  var oldDelta: int

  action init = {
    nondet v = Set(1, 2, 3).oneOf()
    all {
      x' = v,
      y' = -v,
      delta' = v,
      oldDelta' = v,
    }
  }

  action step =
    nondet v = Set(1, 2, 3).oneOf()
    all {
      x' = x + v,
      y' = y - v,
      delta' = v,
      oldDelta' = delta,
    }

  -- this must be an invariant
  val mirrorInv = all {
    y == -x
  }

  -- this invariant must be false, unless the value of v is frozen
  val falseInv = all {
    oldDelta == delta
  }

  run mirrorTest =
    init.then(step)
        .then(step)
        .then(all {
          assert(mirrorInv),
          x' = x,
          y' = y,
          delta' = delta,
          oldDelta' = oldDelta,
        })
}

quint_invariant mirrorInv
#gen_spec
#quint_verify interpreted { } { } (maxDepth := 3)
#quint_run { } { } (numTraces := 1000) (maxSteps := 20) (seed := 42)
quint_bmc 3 mirrorInv
end nondetEx

/-! ## Tests (`quint test`) -/

#quint_test nondetEx
