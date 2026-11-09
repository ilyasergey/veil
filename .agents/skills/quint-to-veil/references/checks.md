# Checks: Quint commands and their Veil counterparts

| Quint | Veil (after the module, inside it) |
| --- | --- |
| `--invariant=a,b` | `quint_invariant a, b` |
| `--init=I --step=N` | `set_option quint.init "I"` and `set_option quint.step "N"` before the module |
| `quint verify --backend tlc` (TLC) | `#gen_spec` then `#model_check { } { }` (Veil's explicit-state checker, Lace) |
| TLC `CONSTRAINT` | `quint_constraint c` |
| `quint verify --max-steps=k` (Apalache, bounded) | `#model_check { } { } (maxDepth := k)` for finite branching; `unsat trace { any k actions; assert ¬ inv }` when the state is SMT-friendly (integers, booleans, sum types; not sets or maps) |
| `quint verify --inductive-invariant=I` (Apalache) | `quint_invariant` of the conjuncts and `#check_invariants` (SMT), or `prove_veil_invariant_goal` (interactive) |
| `quint run --max-samples=n --max-steps=k` | `#simulate { } { } (numTraces := n) (maxSteps := k) (seed := s)` |
| `quint verify --temporal=p --backend tlc` | a Veil `temporal` property and `#temporal_check` |
| `quint test` | pure `run`s: `#guard decide (P)`; runs with actions: see frontend.md |

The instantiation argument of `#model_check` (`{ }`) gives values for remaining `param`s, i.e.
Quint constants that no `import M(c = e)` fixed: `#model_check { N := 3 } { }`. A model check
that needs the frontend's runtime library at instantiation time needs the meta import that
`Veil.Quint` already provides.

## Validating

Get Quint's numbers with the quint CLI (npm package `@informalsystems/quint`); the TLC and
Apalache backends need Java 21 (`JAVA_HOME`):

```bash
quint verify --backend tlc --main=M --invariant=inv spec.qnt     # distinct states, verdict
quint verify --max-steps=3 --main=M --invariant=inv spec.qnt     # Apalache, bounded
quint run --main=M --invariant=inv --max-samples=1000 spec.qnt   # simulator
```

- **Distinct states.** TLC's `distinct states found` equals Veil's `explored N states` for a
  complete run of the same instance: the frontend encodes each Quint state one-to-one (sets and
  maps are extensional). Compare only complete runs (no `maxDepth`, no violation).
- **Verdicts.** Each invariant holds or fails on both sides. A violation reported by Veil should
  be reproducible with `quint run --invariant` (the simulator may need more samples) or TLC.
- **Deadlocks.** TLC (through Quint) does not report deadlocks by default; neither does Veil
  without a `termination` clause.

Mismatches usually come from: a variable an action leaves unassigned (Veil keeps it, Quint
errors), a runtime error in Quint that Veil turns into a default value, or a bounded range in the
Veil copy. Report the cause; do not tune the spec until the numbers agree.
