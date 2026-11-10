module

public import Veil.Quint
public import Examples.Quint.Cryptography.Hashes.Hashes
public meta import Examples.Quint.Cryptography.Hashes.Hashes

/-!
# Quint example `cryptography/hashes/hashesTest.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/cryptography/hashes/hashesTest.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The module elaborates into a Veil module; no Veil checks are configured for it.
-/

module hashesTest {
  import hashes(HASH_LEN = 32).* from "./hashes"

  pure def hplainTest = and {
    assert(hplain([ 2, 3, 4 ]) == hplain([ 2, 3, 4 ])),
    assert(hplain([ 2, 3, 4 ]) != hplain([ 3, 4, 5 ])),
  }

  pure def hashTest = and {
    assert(hash(hplain([ 2, 3, 4 ])) == hash(hplain([ 2, 3, 4 ]))),
    assert(hash(hplain([ 2, 3, 4 ])) != hash(hplain([ 3, 4, 5 ]))),
    assert(hash(hplain([ 2, 3, 4 ])) != hplain([ 2, 3, 4 ])),
    assert(hash(hash(hplain([ 2, 3, 4 ]))) != hash(hplain([ 2, 3, 4 ]))),
  }

  pure def hconcatTest = and {
    pure val t234then567 = hplain([ 2, 3, 4 ]).hconcat(hplain([ 5, 6, 7 ]))
    pure val t234567 = hplain([ 2, 3, 4, 5, 6, 7 ])
    assert(t234then567 == t234567),
    pure val h234then567 = hash(hplain([ 2, 3, 4 ])).hconcat(hplain([ 5, 6, 7 ]))
    assert(h234then567 != hplain([ 2, 3, 4, 5, 6, 7 ])),
    pure def l =
      (hash(hplain([ 2, 3, 4 ])).hconcat(hplain([ 5, 6, 7 ]))).hconcat(hplain([ 8, 9 ]))
    pure def r =
      hash(hplain([ 2, 3, 4 ])).hconcat((hplain([ 5, 6, 7 ])).hconcat(hplain([ 8, 9 ])))
    assert(l == r),
  }

  pure def hlenTest = and {
    assert(hlen(hash(hplain([ 2, 3, 4 ]))) == 32),
    assert(hlen(hash(hash(hplain([ 2, 3, 4 ])))) == 32),
    assert(hlen(hplain([ 2, 3, 4, 5, 6, 7 ])) == 6),
    pure def l =
      (hash(hplain([ 2, 3, 4 ])).hconcat(hplain([ 5, 6, 7 ]))).hconcat(hplain([ 8, 9 ]))
    assert(hlen(l) == 37)
  }
}
