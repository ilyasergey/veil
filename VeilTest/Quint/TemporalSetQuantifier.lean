module
public import Veil.Quint

/-! A temporal formula quantified over a set (`S.forall(x => ...)`) whose body reads a set-valued
state variable. The quantified element has a subtype (`{y // y ∈ S}`); the state predicates of the
body read it as a value of the element type. -/

module L {
  var readers: Set[int]
  action init = all { readers' = Set() }
  action step = all { readers' = readers.union(Set(1)) }
  temporal Live = Set(1, 2).forall(actor => always(eventually(actor.in(readers))))
}
#gen_spec
end L
