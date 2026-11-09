module

public import Veil.Quint

/-!
# Quint example `language-features/tuples.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/tuples.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The module elaborates into a Veil module; no Veil checks are configured for it.
-/

module tuples {
  var myTup: (int, str)

  def combineTuples(t1, t2) = (t1._1, t2._2)
  val combined = combineTuples((true, 1, 2), (false, 2, 2))

  action init = myTup' = (0, "hello")

  action step = myTup' = combineTuples(myTup, (1, "world"))

  -- Unpacking
  pure val a = Set((1, 4), (2, 3)).map( ((p, g)) => p + g)
  pure val s = Set(1, 2, 3)
  pure val m = tuples(s, s).mapBy( ((j, k)) => j+k )
  pure val n = tuples(s, s, s).mapBy( ((j, k, i)) => j+k+i )
}

#gen_spec
#model_check { } { } (maxDepth := 3)
#simulate { } { } (numTraces := 1000) (maxSteps := 20) (seed := 42)
end tuples
