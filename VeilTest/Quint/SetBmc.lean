module
public import Veil.Quint

/-! `quint_bmc` on a state with a finite set: the SMT translation of `Quint.Set`
(`Veil.Frontend.Quint.Smt`) and the reconstruction of set values in a counterexample. -/

-- lean-smt does not reconstruct proofs in the theory of sets
set_option veil.smt.trust true

module S {
  var s: Set[int]
  action init = s' = Set()
  action step = {
    nondet x = Set(1, 2, 3).oneOf()
    s' = s.union(Set(x))
  }
  val Small = s.size() <= 3
  val Sub = s.subseteq(Set(1, 2, 3))
  val No2 = not((2).in(s))
}
#gen_spec

quint_bmc 3 Small, Sub

-- a state with `2 ∈ s` is reachable in two steps (the set values of the trace are read back)
sat trace [reach2] {
  any 2 actions
  assert ((2 : Int) ∈ s)
}

end S
