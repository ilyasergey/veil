module

public import Veil.Quint
public import Examples.Quint.LanguageFeatures.Imports
public meta import Examples.Quint.LanguageFeatures.Imports

/-!
# Quint example `language-features/importFrom.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/importFrom.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The module elaborates into a Veil module; no Veil checks are configured for it.
-/

/-*
 * This example demonstrates how to import modules from other files.
 -/
module importFrom {
  import Math.* from "./imports"

  run importTest = {
    assert(pow(5, 2) == sqr(5))
  }

  action init = true
  action step = true
}

/-! ## Tests (`quint test`) -/

#quint_test importFrom
