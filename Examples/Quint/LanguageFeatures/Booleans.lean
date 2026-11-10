module

public import Veil.Quint

/-!
# Quint example `language-features/booleans.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/booleans.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The module elaborates into a Veil module; no Veil checks are configured for it.
-/

-- basic boolean builtin operators
module booleans {
  var b: bool

  action init = {
    b' = true
  }

  action step = all {
    b.or(true),
    not(b.and(false)),
    b.implies(b),
    b.iff(b),
    b == b,
    b != not(b),
    b' = not(b)
  }
}

#gen_spec
#model_check interpreted { } { }
end booleans
