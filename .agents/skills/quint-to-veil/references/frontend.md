# The Quint frontend

Source: `Veil/Frontend/Quint/` (`Syntax.lean` grammar, `Prelude.lean` runtime library,
`Elab.lean` expressions and actions, `Module.lean` modules and commands).

## Lexical differences from Quint

| Quint | In Lean | Why |
| --- | --- | --- |
| `// c`, `/* c */` | `-- c`, `/- c -/` | Lean's comment syntax (`quint2veil.py` rewrites them) |
| `0.to(10)` | `(0).to(10)` | Lean reads `0.t` as a malformed decimal |
| names that are Lean/Veil keywords (`from`, `end`, `trusted`, `assert`) | unchanged | accepted as identifiers |

Importing `Veil.Quint` makes `and`, `or`, `iff`, `implies` and `leadsTo` keywords in that file,
as they are in Quint.

## How Quint maps to Veil

| Quint | Veil / Lean |
| --- | --- |
| `int`, `bool`, `str` | `Int`, `Bool` (stored) or `Prop` (conditions), `String` |
| `Set[T]`, `T -> U`, `List[T]` | `Quint.Set T` (`Std.ExtTreeSet`), `Quint.Map T U` (`Std.ExtTreeMap`), `List T` |
| `(A, B)`, `(A, B, C)` | `A × B`, `Quint.Tuple.Tup3 A B C` (up to five) |
| record types and literals | `QuintRecords.QRec_<fields>`, one structure per set of field names |
| `type T = A \| B(int)` | `@[veil_decl] inductive T`, with `T.isA`, `T.getB` |
| `type T = U` | `abbrev T := U` (names clashing with Lean types get a `Q` suffix: `OptionQ`) |
| `const c: T` | `param c : T`; `import M(c = e)` replaces it by `e` |
| `var x: T` | `individual x : T` |
| `pure def f(x: T)...` | a Lean `def` |
| `def`/`val` reading state, with typed parameters | `ghost function` / `ghost relation` |
| boolean `val` without parameters | inlined; `quint_invariant v` / `quint_constraint v` |
| definitions with untyped parameters | inlined at each use |
| `action init` (or `quint.init`) | `after_init` |
| `action step` (or `quint.step`) | one Veil `action` per branch of its top-level `any` |
| other actions | inlined into the actions that call them |
| `x' = e` | assignment to a local copy `x'`, copied into the state when the action ends |
| `nondet x = S.oneOf()` | `let x : {y // y ∈ S} :\| True` (enumerates `S`); `Int`/`Nat`/`Bool` via `pick` |
| `any { A, B }` inside an action | `let b ← pick Bool; if b then A else B` |
| guards in `all { ... }` | `require` |
| `match` | conditionals over `T.isC` / `T.getC` |
| `Set()`, `Map()`, `List()` | empty collections; the element type is inferred, `int` when nothing determines it |
| `r.fieldNames()` | the set of field names of the record type of `r` |
| `nondet x: T = apalache::generate(n)` | `let x ← pick T` (every value of `T`) |
| a `def`/`val` that assigns variables or calls actions | an action, as Quint infers |
| `S.forall(x => P)`, `S.exists(...)` | `∀ x, x ∈ S → P`, `∃ x, x ∈ S ∧ P` (decided by enumerating `S`) |
| `import M.*`, `import M(...) as I`, `export I.*` | the declarations of `M` are copied in (renamed `I::x` → `I_x`) |
| `A::b` | `A_b` |

Quint's assignments are delayed: in `all { x' = y, y' = x }` both right-hand sides read the old
state, and so do they in Veil. A variable an action does not assign keeps its value (Quint would
report a missing assignment instead).

Operators that fail at run time in Quint (`get` of a missing key, `head` of `[]`, `nth` out of
range, `chooseSome` of `Set()`) return the type's `default` in Veil.

## Gaps and workarounds

| Construct | Status | Workaround |
| --- | --- | --- |
| Uninterpreted `type T` | not supported | instantiate it, e.g. `type T = str` |
| `run` with actions (`init.then(A).expect(P)`) | `#quint_test M`, including `nondet`/`val` bindings, `if`, `fail()`, `n.reps` with constant `n`, and the runs of instances `import N(...) as I`; a `val` binding is re-evaluated in each step | runs over huge ranges do not finish: sample with `#quint_run` instead |
| `temporal` definitions | translated (`always`, `eventually`, `leadsTo`, fairness, set quantifiers) | `orKeep`, `next` and fairness of actions with parameters are not; write those in Veil's `temporal` syntax |
| `Nat`, `Int` as values | only in `forall`/`exists`/`in`/`oneOf` | bound them, e.g. `(0).to(N)` |
| Huge nondeterministic ranges (`0.to(MAX_UINT).oneOf()`) | enumerated in full | model check a copy with a small range, or use `#simulate` |
| Polymorphic sum types (`Option[a]`) | supported for elaboration; instances limited | instantiate with concrete types |
| `export M as N`, re-export chains | partial | import the original module |
| Modules defined after the module that imports them | Lean elaborates in order | reorder the modules (`quint_examples.py` does) |

## Debugging

`set_option trace.veil.debug true` before a module prints each generated Veil action. Errors in
generated commands point at the Quint declaration they came from.
