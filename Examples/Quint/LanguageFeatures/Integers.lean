module

public import Veil.Quint

/-!
# Quint example `language-features/integers.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/integers.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The module elaborates into a Veil module; no Veil checks are configured for it.
-/

module integers {
  var n: int

  action init = {
    n' = 0
  }

  action step = all {
    n' = n + 1,
    n == n - 0,
    n == n * 1,
    n == n / 1,
    n == n.ipow(1),
    0 == n % n,
    0 == (-n) + n,
    n + 1 > n,
    n - 1 < n,
    n >= n,
    n <= n,
  }
}

#gen_spec
#model_check interpreted { } { } (maxDepth := 3)
#simulate { } { } (numTraces := 1000) (maxSteps := 20) (seed := 42)
end integers
