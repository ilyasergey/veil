module

public import Veil.Quint

/-!
# Quint example `language-features/nondetEx.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/nondetEx.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The module elaborates into a Veil module; no Veil checks are configured for it.
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

#gen_spec
#model_check { } { } (maxDepth := 3)
#simulate { } { } (numTraces := 1000) (maxSteps := 20) (seed := 42)
end nondetEx
