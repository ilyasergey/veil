module

public import Veil.Quint

/-!
# Quint example `puzzles/river/river.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/puzzles/river/river.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The river crossing puzzle.
-/

/-*
 * This is an example of a river-crossing puzzle [1].
 * The specification itself is quite simple, so it can serve as a good
 * starting example.
 *
 * [1]: https://en.wikipedia.org/wiki/River_crossing_puzzle
 *
 * "The fox, goose and bag of beans puzzle, in which a farmer must transport a
 * fox, goose and bag of beans from one side of a river to another using a boat
 * which can only hold one item in addition to the farmer, subject to the
 * constraints that the fox cannot be left alone with the goose, and the goose
 * cannot be left alone with the beans. Equivalent puzzles have also been stated
 * involving a fox, chicken, and bag of grain, or a wolf, goat, and cabbage, etc."
 *
 * We are using the collection of items from the last sentence, namely,
 * a wolf, goat, and cabbage. The wolf wants to eat the goat. The goat wants to
 * eat the cabbage. The wolf does not eat the cabbage.
 *
 * Igor Konnov, Informal Systems, 2023.
 -/
module river {
  -- who is on the origin bank, a subset of "wolf", "goat", "cabbage", "farmer"
  var origin: Set[str]
  -- who is on the boat
  var boat: Set[str]
  -- who is on the destination bank
  var destination: Set[str]

  -- the safety property that must be enforced in the puzzle
  pure def isSafe(location: Set[str]): bool = and {
    Set("goat", "cabbage").subseteq(location) implies location.contains("farmer"),
    Set("goat", "wolf").subseteq(location) implies location.contains("farmer"),
  }

  -- we start with everybody on the origin bank and empty boat
  action init = all {
    origin' = Set("wolf", "goat", "cabbage", "farmer"),
    boat' = Set(),
    destination' = Set(),
  }

  -- when the farmer is on the origin bank, they can bring at most one item
  action embarkOrigin = all {
    origin.contains("farmer"),
    nondet toEmbark =
      powerset(origin)
        .filter(s => size(s) <= 2 and "farmer".in(s))
        .oneOf()
    all {
      isSafe(origin.exclude(toEmbark)),
      boat' = boat.union(toEmbark),
      origin' = origin.exclude(toEmbark),
      destination' = destination,
    }
  }

  -- the farmer on the boat, disembarks the boat at the destination bank
  action disembarkDestination = all {
    boat.contains("farmer"),
    boat' = Set(),
    destination' = destination.union(boat),
    origin' = origin,
  }

  -- when the farmer is on the destination bank, they can bring at most one item
  action embarkDestination = all {
    destination.contains("farmer"),
    nondet toEmbark =
      powerset(destination)
        .filter(s => size(s) <= 2 and "farmer".in(s))
        .oneOf()
    all {
      isSafe(destination.exclude(toEmbark)),
      boat' = boat.union(toEmbark),
      destination' = destination.exclude(toEmbark),
      origin' = origin,
    }
  }

  -- the farmer on the boat, disembarks the boat at the origin bank
  action disembarkOrigin = all {
    boat.contains("farmer"),
    boat' = Set(),
    origin' = origin.union(boat),
    destination' = destination,
  }

  -- the four possible steps
  action step = any {
    embarkOrigin,
    disembarkDestination,
    embarkDestination,
    disembarkOrigin,
  }

  -- the property that should be enforced in the puzzle
  val safety = and {
    isSafe(origin),
    isSafe(boat),
    isSafe(destination)
  }

  -- check this invariant to see a solution
  val noSolution = or {
    origin != Set(),
    boat != Set(),
  }

  -- we cannot replicate the farmer, wolf, goat, and cabbage
  val consistency = and {
    origin.intersect(destination) == Set(),
    origin.intersect(boat) == Set(),
    boat.intersect(destination) == Set(),
  }
}

quint_invariant safety
#gen_spec
#model_check interpreted { } { }
end river
