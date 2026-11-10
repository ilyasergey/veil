module

public import Veil.Quint

/-!
# Quint example `language-features/sets.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/sets.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The module elaborates into a Veil module; no Veil checks are configured for it.
-/

module sets {
  var n: int
  var s: Set[int]

  action init = all {
    n' = 0,
    s' = Set(0)
  }

  -- Test using a predicate by name
  def gte0(x) = x >= 0
  def eqn(x) = x == n

  action step = all {
    n' = n + 1,
    s' = s.union(Set(n + 1)),
    s.exists(x => x == n),
    s.forall(x => x >= 0),
    s.exists(eqn),
    s.forall(gte0),
    n.in(s),
    s.contains(n),
    (n + 1).in(union(s, Set(n + 1))),
    Set(n) == s.intersect(Set(n)),
    not(n.in(s.exclude(Set(n)))),
    Set(n).subseteq(s),
    Set() == s.filter(x => x > n),
    s == s.map(x => x),
    n <= s.fold(0, (x, y) => x + y),
    s.in(powerset(s)),
    s == flatten(Set(s)),
    chooseSome(s).in(s),
    s.isFinite(),
    n + 1 == size(s),
    Set(0, 1, 2, 3) == (0).to(3),
  }

}

#gen_spec
#quint_verify interpreted { } { } (maxDepth := 3)
#quint_run { } { } (numTraces := 1000) (maxSteps := 20) (seed := 42)
end sets
