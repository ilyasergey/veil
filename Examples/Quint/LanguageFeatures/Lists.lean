module

public import Veil.Quint

/-!
# Quint example `language-features/lists.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/lists.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

This file uses constructs that the frontend does not translate (see the warnings
it reports, and the gaps in `.agents/skills/quint-to-veil/references/frontend.md`); it is
elaborated with `quint.lenient`, which skips the definitions and actions that do not elaborate
and reports each of them as a warning.
-/

set_option quint.lenient true
module lists {
  var n: int
  var l: List[int]

  action init = all {
    n' = 0,
    l' = List(0),
  }

  def test(x) = x < 1

  action step = all {
    n' = n + 1,
    l' = l.append(n + 1),
    List(1, 2, 3).length() + l.length() == List(1, 2, 3).concat(l).length(),
    0 == l.head(),
    l.tail().length() == n,
    n == l.nth(n),
    List().indices() == Set(),
    { val idxs = l.indices()
      val elems = l.foldl(Set(), (acc, j) => acc.union(Set(j)))
      idxs == elems },
    l.replaceAt(0, n).head() == n,
    l.slice(1, l.length()) == l.tail(),
    -- Not currently supported by Apalache
    -- <unknown>: Input error (see the manual): Expected a constant integer expression. Found: n E@10:54:45.506
    -- range(0, n) == l
    range(0, 3) == List(0, 1, 2),
    l.select(x => x < 1) == List(0),
    l.select(test) == List(0),
    (l.foldl(Set(), (acc, x) => acc.union(Set(x))).size()) == n + 1,
  }
}

#gen_spec
#quint_verify interpreted { } { } (maxDepth := 3)
#quint_run { } { } (numTraces := 1000) (maxSteps := 20) (seed := 42)
end lists
