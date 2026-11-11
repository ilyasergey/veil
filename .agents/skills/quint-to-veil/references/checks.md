# Checks: Quint commands and their Veil counterparts

| Quint | Veil (after the module, inside it) |
| --- | --- |
| `--invariant=a,b` | `quint_invariant a, b` |
| `--init=I --step=N` | `set_option quint.init "I"` and `set_option quint.step "N"` before the module |
| `quint verify --backend tlc` (TLC) | `#gen_spec` then `#quint_verify { } { }`: Veil's explicit-state checker (Lace, `#model_check`), reported as Quint reports |
| TLC `CONSTRAINT` | `quint_constraint c` |
| `quint verify --max-steps=k` (Apalache, bounded) | `quint_bmc k inv` (Veil's symbolic BMC, SMT) when the state is SMT-friendly (integers, booleans, strings, sum types, records, finite sets with `in`/`union`/`intersect`/`exclude`/`subseteq`/`size`; no maps, `map`, `filter` or `powerset`; set `veil.smt.trust true` where it is off, as in `VeilTest`), otherwise `#quint_verify { } { } (maxDepth := k)` |
| `quint verify --inductive-invariant=I` (Apalache) | `quint_invariant` of the conjuncts and `#check_invariants` (SMT), or `quint_grind` for every VC (`macro_rules \| \`(tactic\| veil_solve) => \`(tactic\| quint_grind)` and `set_option veil.solver "custom" in #check_invariants`) |
| `quint run --max-samples=n --max-steps=k` | `#quint_run { } { } (numTraces := n) (maxSteps := k) (seed := s)` |
| `quint verify --temporal=p --backend tlc` | `#quint_temporal [p] { } { }` (Lasso, `#temporal_check`); the frontend translates the module's `temporal` definitions |
| `quint test` | `#quint_test M` after the module (every execution of each `...Test` run, also those of the instances `M` imports with `as`); `#quint_test M "pattern"` selects runs; pure `run`s also become `#guard` checks |
| a property expected to fail | `set_option veil.violationIsError false in` before the check |

`#quint_verify` and `#quint_run` take exactly the arguments of `#model_check` and `#simulate`,
run them, keep Veil's message and trace widget, and add a report in Quint's format:
`[ok] No violation found (288 distinct states, 95ms).`, or an example execution
(`[State k] { var: value }`, with Quint names and `Set(…)`/`Map(k -> v)` values) followed by
`[violation] Found an issue (…ms).`

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
