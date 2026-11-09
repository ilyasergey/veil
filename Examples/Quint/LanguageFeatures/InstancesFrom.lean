module

public import Veil.Quint
public import Examples.Quint.LanguageFeatures.Instances

/-!
# Quint example `language-features/instancesFrom.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/instancesFrom.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The module elaborates into a Veil module; no Veil checks are configured for it.
-/

module instancesFrom {
  pure val MyY = true
  pure val z = "world"

  import A(x = 33, y = MyY, z = "hello") as A1 from "./instances"

  -- now, we can access F and G via A1::F and A1::G
  val test_F = A1::f(10)
  val test_x = A1::x

  -- If we want to omit identity bindings such as z = z, we write:
  -- import A(x = 15, y = MyY, *) as A2
  import A(x = 15, y = MyY, z = z) as A2 from "./instances"

  -- the above is equivalent to TLA+'s instance:
  -- A2 == INSTANCE A WITH x <- 15, y <- MyY

  action init = true
  action step = true
}
