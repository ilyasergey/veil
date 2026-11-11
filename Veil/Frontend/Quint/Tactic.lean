module

public import Veil.Frontend.Quint.Prelude
public meta import Lean
public import Veil.Frontend.DSL.Infra.SmtSimp

/-!
# Tactics for proofs about Quint specifications

`quint_grind` closes verification conditions whose state is made of Quint sets, maps, records and
sum types: it rewrites membership in set literals, map updates and Cartesian products with the
lemmas of `Veil.Frontend.Quint.Prelude`, then calls `grind`. To use it for every verification
condition of `#check_invariants`:

```lean
macro_rules | `(tactic| veil_solve) => `(tactic| quint_grind)
set_option veil.solver "custom" in
#check_invariants
```
-/

public meta section

/-- Close a verification condition about Quint sets and maps (see the module docstring). -/
syntax (name := quintGrind) "quint_grind" : tactic

macro_rules
  | `(tactic| quint_grind) => `(tactic| (
      try simp only [Quint.Set.mem_ofList_iff, Quint.Map.get_set_eq, Quint.Set.mem_tuples2_iff,
        Quint.Set.mem_filter_iff, Quint.Set.empty'_eq, Quint.Map.empty'_eq, Quint.List.empty'_eq,
        List.mem_cons, List.not_mem_nil, or_false] at *
      first
        | done
        | grind [Quint.Map.get_mapBy]
        | (simp_all [Quint.Map.get_mapBy]; done)
        | (simp_all [Quint.Map.get_mapBy]; grind [Quint.Map.get_mapBy])))

/- Membership in a set literal is a disjunction of equalities, which the SMT backend translates
(it cannot translate the set itself). -/
attribute [smtSimp] Quint.Set.mem_ofList_iff List.mem_cons List.not_mem_nil
  Quint.Set.empty'_eq Quint.Map.empty'_eq Quint.List.empty'_eq
