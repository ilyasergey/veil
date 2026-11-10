module

public import Veil.Quint

/-!
# Quint example `language-features/option.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/option.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The module elaborates into a Veil module; no Veil checks are configured for it.
-/

module option {
  -- A demonstration of sum types, specifying an option type.

  -- A polymorphic option type
  type Option[a] =
    | Some(a)
    | None

  -- `o.optionMap(f)` is `Some(f(v))` if `o = Some(v)` or `None` of `o = None`
  def optionMap(o: Option[a], f: a => b): Option[b] =
    match o {
    | Some(x) => Some(f(x))
    | None    => None
    }

  -- `o.getOr(v)` is `x` or `Some(x) = o` or `v` if `o = None`
  def getOr(o: Option[a], default: a): a =
    match o {
    | Some(x) => x
    | None    => default
    }

  var votes: List[Option[int]]
  var outcome: int

  action init = all {
    votes' = [],
    outcome' = 0
  }

  action vote(v) = {
    votes' = votes.append(Some(v))
  }

  action incrVote(i, n) = {
    val vote0 = votes[i]
    val vote1 = vote0.optionMap(x => x + n)
    votes' = votes.replaceAt(i, vote1)
  }

  action unvote(i) = all {
    votes' = votes.replaceAt(i, None),
  }

  val sumVotes =
    votes.foldl(0, (sum, v) => v.getOr(0) + sum)

  action step = all {
    any {
      nondet v = oneOf((0).to(5)); vote(v),
      all {
          votes.length() > 0,
          nondet i = oneOf(votes.indices()); unvote(i),
      },
      all {
          votes.length() > 0,
          nondet i = oneOf(votes.indices()); nondet v = oneOf((0).to(5)) incrVote(i, v),
      }

    },
    outcome' = sumVotes
  }

  run matchWithDefaultTest = {
    val expected = match Some(42) { _ => "default" }
    assert(expected == "default")
  }
}

#gen_spec
#model_check interpreted { } { } (maxDepth := 3)
#simulate { } { } (numTraces := 1000) (maxSteps := 20) (seed := 42)
end option
