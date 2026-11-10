module

public import Veil.Quint

/-!
# Quint example `language-features/maps.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/maps.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The module elaborates into a Veil module; no Veil checks are configured for it.
-/

module maps {
  var n: int
  var m: int -> int

  action init = all {
    n' = 0,
    m' = Map((0, 1)),
  }

  action step = {
    val nextN = m.get(n)
    val mKeys = m.keys()
    all {
        n' = nextN,
        m' = m.put(nextN, nextN + 1),
        mKeys.mapBy(x => x + 1) == m,
        mKeys.map(x => (x, x + 1)).setToMap() == m,
        setOfMaps(mKeys, mKeys.map(x => x + 1)).contains(m),
        m.set(n, n).get(n) == n,
        m.setBy(n, x => x + 1).get(n) == nextN + 1,
    }
  }}

#gen_spec
#quint_verify interpreted { } { } (maxDepth := 3)
#quint_run { } { } (numTraces := 1000) (maxSteps := 20) (seed := 42)
end maps
