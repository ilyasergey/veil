module

public import Smt.Translate
public meta import Smt.Translate
public import Smt.Reconstruct
public meta import Smt.Reconstruct
public import Veil.Frontend.Quint.Prelude

/-!
# Quint sets in SMT

Translators from the frontend's finite sets (`Quint.Set α`, i.e. `Std.ExtTreeSet α compare`) to
cvc5's theory of finite sets, so that Veil's SMT-based checks (`quint_bmc`, `#check_invariants`)
apply to Quint specifications whose state has sets:

| Lean | SMT-LIB |
| --- | --- |
| `Std.ExtTreeSet α cmp`, `Quint.Set α` | `(Set α)` |
| `a ∈ s` | `(set.member a s)` |
| `∅`, `Quint.Set.empty'` | `(as set.empty (Set α))` |
| `s ∪ t`, `s ∩ t`, `s \ t` | `set.union`, `set.inter`, `set.minus` |
| `s.insert a`, `s.erase a` | `(set.insert a s)`, `(set.minus s (set.singleton a))` |
| `Quint.Set.ofList [a, b]` | `(set.insert a b (as set.empty (Set α)))` |
| `Quint.Set.subseteq s t` | `(set.subset s t)` |
| `Quint.Set.size s` | `(set.card s)` |

Maps are not translated. The reconstructors at the end read set values of cvc5's models back into
Lean (`Quint.Set.ofList [a]` for `(set.singleton a)`, `∪` for `set.union`, ...), for the states of a
counterexample.
-/

public meta section

namespace Veil.Quint.SmtSets

open Lean Meta Smt Translator Term

/-- The element type of a set type, if `ty` is one. -/
def setElemType? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnfR ty
  match ty.getAppFn with
  | .const ``Std.ExtTreeSet _ => return ty.getAppArgs[0]?
  | .const ``Quint.Set _ => return ty.getAppArgs[0]?
  | _ => return none

@[smt_translate] def translateSetType : Translator := fun e => do
  match e.getAppFn with
  | .const ``Std.ExtTreeSet _ | .const ``Quint.Set _ =>
    let some α := e.getAppArgs[0]? | return none
    return appT (symbolT "Set") (← applyTranslators! α)
  | _ => return none

def emptySet (setTy : Expr) : TranslationM (Option Smt.Term) := do
  let some _ ← setElemType? setTy | return none
  return mkApp2 (literalT "as") (literalT "set.empty") (← applyTranslators! (← whnfR setTy))

/-- The SMT term of a list literal of set elements, inserted into `base`. -/
partial def insertList (l : Expr) (base : Smt.Term) : TranslationM (Option Smt.Term) := do
  match_expr l with
  | List.nil _ => return base
  | List.cons _ a rest =>
    let some r ← insertList rest base | return none
    return mkApp2 (literalT "set.insert") (← applyTranslators! a) r
  | _ => return none

/-- The constants that `translateSetOps` translates. -/
def setOps : Std.HashSet Name := .ofList [``Membership.mem, ``Union.union, ``Inter.inter,
  ``SDiff.sdiff, ``EmptyCollection.emptyCollection, ``Quint.Set.empty', ``Std.ExtTreeSet.insert,
  ``Std.ExtTreeSet.erase, ``Quint.Set.ofList, ``Quint.Set.union, ``Quint.Set.intersect,
  ``Quint.Set.exclude, ``Quint.Set.subseteq, ``Quint.Set.size]

@[smt_translate] def translateSetOps : Translator := fun e => do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let Expr.const n _ := fn | return none
  unless setOps.contains n do return none
  -- only full applications (e.g. not `Quint.Set.union s` passed to a fold)
  if (← whnfR (← inferType e)).isForall then return none
  -- whether the type argument `args[i]` is a set type
  let isSet (i : Nat) : MetaM Bool := do
    let some x := args[i]? | return false
    return (← setElemType? x).isSome
  let tr (i : Nat) : TranslationM Smt.Term := applyTranslators! args[i]!
  match n, args.size with
  | ``Membership.mem, 5 =>
    unless (← isSet 1) do return none
    return mkApp2 (literalT "set.member") (← tr 4) (← tr 3)
  | ``Union.union, 4 =>
    unless (← isSet 0) do return none
    return mkApp2 (literalT "set.union") (← tr 2) (← tr 3)
  | ``Inter.inter, 4 =>
    unless (← isSet 0) do return none
    return mkApp2 (literalT "set.inter") (← tr 2) (← tr 3)
  | ``SDiff.sdiff, 4 =>
    unless (← isSet 0) do return none
    return mkApp2 (literalT "set.minus") (← tr 2) (← tr 3)
  | ``EmptyCollection.emptyCollection, 2 => emptySet args[0]!
  | ``Quint.Set.empty', _ => emptySet (← inferType e)
  | ``Std.ExtTreeSet.insert, _ =>
    let s := args[args.size - 2]!
    let a := args[args.size - 1]!
    return mkApp2 (literalT "set.insert") (← applyTranslators! a) (← applyTranslators! s)
  | ``Std.ExtTreeSet.erase, _ =>
    let s := args[args.size - 2]!
    let a := args[args.size - 1]!
    return mkApp2 (literalT "set.minus") (← applyTranslators! s)
      (appT (literalT "set.singleton") (← applyTranslators! a))
  | ``Quint.Set.ofList, _ =>
    let some base ← emptySet (← inferType e) | return none
    insertList args[args.size - 1]! base
  | ``Quint.Set.union, _ =>
    return mkApp2 (literalT "set.union") (← tr (args.size - 2)) (← tr (args.size - 1))
  | ``Quint.Set.intersect, _ =>
    return mkApp2 (literalT "set.inter") (← tr (args.size - 2)) (← tr (args.size - 1))
  | ``Quint.Set.exclude, _ =>
    return mkApp2 (literalT "set.minus") (← tr (args.size - 2)) (← tr (args.size - 1))
  | ``Quint.Set.subseteq, _ =>
    return mkApp2 (literalT "set.subset") (← tr (args.size - 2)) (← tr (args.size - 1))
  | ``Quint.Set.size, _ =>
    return appT (literalT "set.card") (← tr (args.size - 1))
  | _, _ => return none

/-! ## Set values in models -/

open Smt.Reconstruct in
@[smt_sort_reconstruct] def reconstructSetSort : SortReconstructor := fun s => do
  unless s.getKind! == .SET_SORT do return none
  let α ← reconstructSort s.getSetElementSort!
  return some (← mkAppOptM ``Quint.Set #[α, none])

open Smt.Reconstruct in
@[smt_term_reconstruct] def reconstructSetTerm : TermReconstructor := fun t => do
  unless t.getSort!.getKind! == .SET_SORT do return none
  let tr (i : Nat) : ReconstructM Expr := reconstructTerm t[i]!
  match t.getKind! with
  | .SET_EMPTY =>
    let ty ← reconstructSort t.getSort!
    return some (← mkAppOptM ``EmptyCollection.emptyCollection #[ty, none])
  | .SET_SINGLETON =>
    let a ← tr 0
    return some (← mkAppM ``Quint.Set.ofList #[← mkListLit (← inferType a) [a]])
  | .SET_UNION => return some (← mkAppM ``Union.union #[← tr 0, ← tr 1])
  | .SET_INTER => return some (← mkAppM ``Inter.inter #[← tr 0, ← tr 1])
  | .SET_MINUS => return some (← mkAppM ``SDiff.sdiff #[← tr 0, ← tr 1])
  | .SET_INSERT =>
    -- `(set.insert a_1 ... a_n s)`
    let n := t.getNumChildren
    let mut r ← tr (n - 1)
    for i in [0:n - 1] do
      r ← mkAppM ``Std.ExtTreeSet.insert #[r, ← tr i]
    return some r
  | _ => return none

end Veil.Quint.SmtSets
