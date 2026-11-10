module

public import Veil.Quint

/-!
# Quint example `language-features/generate.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/generate.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

This file uses constructs that the frontend does not translate (see the warnings
it reports, and the gaps in `.agents/skills/quint-to-veil/references/frontend.md`); it is
elaborated with `quint.lenient`, which skips the definitions and actions that do not elaborate
and reports each of them as a warning.
-/

-- demonstrating the use of 'apalache::generate'
set_option quint.lenient true
module gen {
  var S: Set[int]
  var T: Set[{ x: int, y: bool }]

  action init = {
    nondet iS: Set[int] = apalache::generate(10)
    nondet iT: Set[{ x: int, y: bool }] = apalache::generate(20)
    all {
      S' = iS,
      T' = iT,
    }
  }

  action step =
    all {
      S' = S,
      T' = T,
    }
}
