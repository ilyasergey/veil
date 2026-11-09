module

public import Veil

/-!
# Quint runtime library

The values of the Quint frontend (`Veil.Frontend.Quint`) and the operators of Quint's
standard library ("builtins"), as Lean definitions.

| Quint type      | Lean type                     |
| --------------- | ----------------------------- |
| `int`           | `Int`                         |
| `bool`          | `Bool` (stored) / `Prop` (conditions) |
| `str`           | `String`                      |
| `Set[T]`        | `Quint.Set T` = `Std.ExtTreeSet T` |
| `T -> U`        | `Quint.Map T U` = `Std.ExtTreeMap T U` |
| `List[T]`       | `List T`                      |
| `(A, B)`        | `A × B`                       |
| `(A, B, C)`     | `Quint.Tup3 A B C` (also `Tup4`, `Tup5`) |
| `{ f: T, ... }` | a generated `@[veil_decl]` structure |
| sum types       | a generated `@[veil_decl]` inductive |

Sets and maps are *extensional* (`Std.ExtTreeSet`/`Std.ExtTreeMap`): two sets with the same
elements are equal, so the model checker never distinguishes states that Quint considers equal.
They need a lawful order on the elements (`Std.TransOrd`, `Std.LawfulEqOrd`), which Veil derives
for every `@[veil_decl]` structure and inductive.

Quint's operators that can fail at run time (`get` of a missing key, `head` of an empty list,
`nth` out of bounds, `chooseSome` of an empty set) return the `default` value of the result type
instead of failing. -/

@[expose] public section

namespace Quint

/-- `Set[T]`. -/
abbrev Set (α : Type) [Ord α] := Std.ExtTreeSet α compare
/-- `T -> U`. -/
abbrev Map (α β : Type) [Ord α] := Std.ExtTreeMap α β compare

/-! ## Tuples of arity three to five. Pairs are `Prod`. -/

@[veil_decl] structure Tup3 (α β γ : Type) where
  _1 : α
  _2 : β
  _3 : γ

@[veil_decl] structure Tup4 (α β γ δ : Type) where
  _1 : α
  _2 : β
  _3 : γ
  _4 : δ

@[veil_decl] structure Tup5 (α β γ δ ε : Type) where
  _1 : α
  _2 : β
  _3 : γ
  _4 : δ
  _5 : ε

instance [Repr α] [Repr β] [Repr γ] : Repr (Tup3 α β γ) where
  reprPrec t _ := s!"({repr t._1}, {repr t._2}, {repr t._3})"
instance [Repr α] [Repr β] [Repr γ] [Repr δ] : Repr (Tup4 α β γ δ) where
  reprPrec t _ := s!"({repr t._1}, {repr t._2}, {repr t._3}, {repr t._4})"
instance [Repr α] [Repr β] [Repr γ] [Repr δ] [Repr ε] : Repr (Tup5 α β γ δ ε) where
  reprPrec t _ := s!"({repr t._1}, {repr t._2}, {repr t._3}, {repr t._4}, {repr t._5})"

end Quint

/-- `t._1` on a pair. -/
@[reducible] def Prod._1 (p : α × β) : α := p.1
/-- `t._2` on a pair. -/
@[reducible] def Prod._2 (p : α × β) : β := p.2

namespace Quint
open Std

variable {α β γ : Type} [Ord α] [TransOrd α] [LawfulEqOrd α]

/-! ## Sets -/

namespace Set

/-- `Set(e_1, ..., e_n)` -/
@[inline] def ofList (l : List α) : Quint.Set α := ExtTreeSet.ofList l compare

/-- `S.size()` -/
@[inline] def size (s : Quint.Set α) : Int := (ExtTreeSet.size s : Int)

/-- `S.map(f)` -/
@[inline] def map [Ord β] (s : Quint.Set α) (f : α → β) : Quint.Set β :=
  ExtTreeSet.ofList (s.toList.map f) compare

/-- `S.filter(p)` -/
@[inline] def filter (s : Quint.Set α) (p : α → Bool) : Quint.Set α := ExtTreeSet.filter p s

/-- `S.fold(init, (acc, x) => e)` -/
@[inline] def fold (s : Quint.Set α) (init : β) (f : β → α → β) : β := s.toList.foldl f init

/-- `S.union(T)` -/
@[inline] def union (s t : Quint.Set α) : Quint.Set α := s ∪ t
/-- `S.intersect(T)` -/
@[inline] def intersect (s t : Quint.Set α) : Quint.Set α := s ∩ t
/-- `S.exclude(T)` -/
@[inline] def exclude (s t : Quint.Set α) : Quint.Set α := s \ t

/-- `S.subseteq(T)` -/
def subseteq (s t : Quint.Set α) : Prop := ∀ x, x ∈ s → x ∈ t

instance (s t : Quint.Set α) : Decidable (subseteq s t) :=
  decidable_of_iff (s.toList.all (fun x => t.contains x)) (by
    simp [subseteq, List.all_eq_true, ExtTreeSet.mem_toList, ExtTreeSet.contains_iff_mem])

/-- All sublists of `l`, i.e. the elements of its powerset. -/
def sublists : List α → List (List α)
  | [] => [[]]
  | x :: xs => let r := sublists xs; r ++ r.map (x :: ·)

/-- `S.powerset()` -/
def powerset (s : Quint.Set α) : Quint.Set (Quint.Set α) :=
  ExtTreeSet.ofList ((sublists s.toList).map (fun l => ExtTreeSet.ofList l compare)) compare

/-- `S.flatten()` -/
def flatten (s : Quint.Set (Quint.Set α)) : Quint.Set α :=
  s.toList.foldl (· ∪ ·) ∅

/-- `S.chooseSome()`: the least element (Quint leaves the choice to the tool). -/
def chooseSome [Inhabited α] (s : Quint.Set α) : α := s.toList.headD default

/-- `S.getOnlyElement()` -/
def getOnlyElement [Inhabited α] (s : Quint.Set α) : α := s.toList.headD default

/-- `S.isFinite()` -/
def isFinite (_ : Quint.Set α) : Bool := true

/-- `a.to(b)`: the integers from `a` to `b`, inclusive. -/
def range (a b : Int) : Quint.Set Int :=
  ExtTreeSet.ofList ((_root_.List.range (b - a + 1).toNat).map (fun (i : Nat) => a + Int.ofNat i)) compare

/-- `tuples(S, T)` -/
def tuples2 [Ord β] [TransOrd β] (s : Quint.Set α) (t : Quint.Set β) : Quint.Set (α × β) :=
  ExtTreeSet.ofList (s.toList.flatMap fun a => t.toList.map fun b => (a, b)) compare

/-- `tuples(S, T, U)` -/
def tuples3 [Ord β] [TransOrd β] [Ord γ] [TransOrd γ] (s : Quint.Set α) (t : Quint.Set β)
    (u : Quint.Set γ) : Quint.Set (Tup3 α β γ) :=
  ExtTreeSet.ofList (s.toList.flatMap fun a => t.toList.flatMap fun b =>
    u.toList.map fun c => ⟨a, b, c⟩) compare

/-- All lists of length exactly `n` over `l`. -/
def listsOfLength (l : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => (listsOfLength l n).flatMap fun xs => l.map fun x => xs ++ [x]

/-- `S.allListsUpTo(n)` -/
def allListsUpTo [Ord (List α)] (s : Quint.Set α) (n : Int) : Quint.Set (List α) :=
  ExtTreeSet.ofList ((List.range (n.toNat + 1)).flatMap (listsOfLength s.toList)) compare

/-- `S.setOfMaps(T)`: all maps with domain `S` and values in `T`. -/
def setOfMaps [Ord β] [TransOrd β] [Ord (Quint.Map α β)] (s : Quint.Set α) (t : Quint.Set β) :
    Quint.Set (Quint.Map α β) :=
  let maps := s.toList.foldl (fun (acc : List (List (α × β))) a =>
    acc.flatMap fun m => t.toList.map fun b => m ++ [(a, b)]) [[]]
  ExtTreeSet.ofList (maps.map fun l => ExtTreeMap.ofList l compare) compare

end Set

/-! ## Quantifiers over sets are decided by enumerating the set. -/

instance instDecidableForallSet (s : Quint.Set α) (p : α → Prop) [DecidablePred p] :
    Decidable (∀ x, x ∈ s → p x) :=
  decidable_of_iff (s.toList.all (fun x => decide (p x))) (by
    simp [List.all_eq_true, ExtTreeSet.mem_toList])

instance instDecidableExistsSet (s : Quint.Set α) (p : α → Prop) [DecidablePred p] :
    Decidable (∃ x, x ∈ s ∧ p x) :=
  decidable_of_iff (s.toList.any (fun x => decide (p x))) (by
    simp [List.any_eq_true, ExtTreeSet.mem_toList])

/-! ## Maps -/

namespace Map

/-- `Map(k_1 -> v_1, ...)` -/
@[inline] def ofList (l : List (α × β)) : Quint.Map α β := ExtTreeMap.ofList l compare

/-- `m.get(k)`; the `default` value if `k` is not a key. -/
@[inline] def get [Inhabited β] (m : Quint.Map α β) (k : α) : β := m.getD k default

/-- `m.set(k, v)` and `m.put(k, v)` -/
@[inline] def set (m : Quint.Map α β) (k : α) (v : β) : Quint.Map α β := m.insert k v

/-- `m.setBy(k, f)` -/
@[inline] def setBy [Inhabited β] (m : Quint.Map α β) (k : α) (f : β → β) : Quint.Map α β :=
  m.insert k (f (m.getD k default))

/-- `m.keys()` -/
@[inline] def keys (m : Quint.Map α β) : Quint.Set α := ExtTreeSet.ofList (ExtTreeMap.keys m) compare

/-- `S.mapBy(f)` -/
@[inline] def mapBy (s : Quint.Set α) (f : α → β) : Quint.Map α β :=
  ExtTreeMap.ofList (s.toList.map fun x => (x, f x)) compare

/-- `S.setToMap()` -/
@[inline] def setToMap [Ord β] [TransOrd β] (s : Quint.Set (α × β)) : Quint.Map α β :=
  ExtTreeMap.ofList s.toList compare

end Map

/-! ## Lists -/

namespace List

/-- `l.length()` -/
@[inline] def length (l : _root_.List α) : Int := (l.length : Int)
/-- `l[i]`, `l.nth(i)` -/
@[inline] def nth [Inhabited α] (l : _root_.List α) (i : Int) : α := l.getD i.toNat default
/-- `l.head()` -/
@[inline] def head [Inhabited α] (l : _root_.List α) : α := l.headD default
/-- `l.last()` -/
@[inline] def last [Inhabited α] (l : _root_.List α) : α := l.getLastD default
/-- `l.append(e)` -/
@[inline] def append (l : _root_.List α) (e : α) : _root_.List α := l ++ [e]
/-- `l.replaceAt(i, e)` -/
@[inline] def replaceAt (l : _root_.List α) (i : Int) (e : α) : _root_.List α := l.set i.toNat e
/-- `l.slice(s, e)` -/
@[inline] def slice (l : _root_.List α) (s e : Int) : _root_.List α :=
  (l.drop s.toNat).take (e - s).toNat
/-- `range(s, e)` -/
def range (s e : Int) : _root_.List Int :=
  (_root_.List.range (e - s).toNat).map (fun (i : Nat) => s + Int.ofNat i)
/-- `l.indices()` -/
@[inline] def indices (l : _root_.List α) : Quint.Set Int :=
  ExtTreeSet.ofList (range 0 (l.length : Int)) compare
/-- `l.foldr(init, f)` -/
@[inline] def foldr (l : _root_.List α) (init : β) (f : α → β → β) : β := l.foldr f init

end List

/-! ## Integers -/

/-- `i^j`; Quint requires `j ≥ 0`. -/
@[inline] def ipow (i j : Int) : Int := i ^ j.toNat

end Quint
