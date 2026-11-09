---
name: quint-to-veil
description: Bring a Quint specification (.qnt) into Veil with Veil's Quint frontend, push-button where possible: rewrite the source mechanically, add the Veil checks that correspond to the Quint commands (quint run, quint verify, quint test, TLC backend), fix the few constructs the frontend does not accept, and validate the result against the quint tool (TLC distinct-state counts, Apalache verdicts, simulator results). Use whenever the user wants to port, check, verify, prove, or cross-check a Quint spec in Veil, or asks about the Quint frontend (`module M { ... }` in Lean, `quint_invariant`, `Veil.Quint`). Not for TLA+ (use tla-to-veil) or for Quint-only work.
---

# Quint to Veil

Veil parses Quint modules directly: a Lean file that does `public import Veil.Quint` can contain
Quint modules almost verbatim, and each module with state becomes a Veil module that Veil's
explicit-state model checker, simulator, symbolic bounded model checker and interactive proofs
work on. The job is therefore mostly mechanical; the judgement is in choosing the checks and in
validating them against Quint.

Read before working:

- [frontend.md](references/frontend.md): what the frontend accepts, how Quint maps to Veil, and
  the known gaps with their workarounds.
- [checks.md](references/checks.md): which Veil command reproduces which Quint command, and how
  to validate against the quint tool.

Examples: `Examples/Quint/` (all of Quint's examples; its README indexes them and records the
Quint and Veil results). The frontend's source is `Veil/Frontend/Quint/`.

## 1. Convert the source

```bash
python3 scripts/quint2veil.py path/to/spec.qnt --lean > Spec.lean
```

This rewrites exactly what Lean's tokenizer needs: comments (`//` → `--`, `/* */` → `/- -/`,
same length so positions agree) and methods on numerals (`0.to(9)` → `(0).to(9)`). Nothing else
changes. For a Quint file that imports another file (`import M.* from "./m"`), convert that file
too and add `public import` of its Lean module to the header; the `from` clause itself is ignored.

To regenerate all of Quint's examples, use `scripts/quint_examples.py QUINT_CHECKOUT` with the
per-example checks in `scripts/quint_examples_config.py`.

## 2. Elaborate and fix

`lake env lean Spec.lean` (or `lake lean`, which also loads the SMT solver). Fix what the
frontend reports; frontend.md lists the gaps (e.g. uninterpreted `type T`, `run` tests with
actions, temporal formulas). Keep the Quint text as it is wherever possible; if you must change
it, say so in a comment next to the change.

## 3. Add the checks

A module with `var`s stays open as a Veil module after its closing `}`. Add the checks there and
close it with `end <module>`:

```lean
module two_phase_commit_3 {
  import two_phase_commit(resourceManagers = Set("rm1", "rm2", "rm3")).*
}

quint_invariant consistencyInv   -- quint ... --invariant=consistencyInv
#gen_spec
#model_check { } { }             -- quint verify --backend tlc
end two_phase_commit_3
```

checks.md gives the correspondence for `--init`/`--step` (`set_option quint.init "Init"` before
the module), `--max-steps`, `quint run`, constraints, and Apalache's inductive invariants.

## 4. Validate against Quint

Run the corresponding quint command and compare (checks.md, "Validating"):

1. invariant verdicts agree (holds / violated, the same invariant);
2. for finite instances, Veil's `explored N states` equals TLC's `distinct states found`
   (`quint verify --backend tlc`);
3. known violations reproduce, with a counterexample of the same shape.

Report each as passed, failed, or not run, with the commands. Investigate any mismatch; do not
change the spec to make numbers agree.

## 5. Go beyond Quint where it pays

Quint checks fixed instances. In Veil you can keep constants as `param`s and prove the invariant
for every instance (`#check_invariants`, or `prove_veil_invariant_goal` with Lean tactics). See
`Examples/Quint/Classic/Distributed/TwoPhaseCommit/TwoPhaseCommitProof.lean` for a proof over
all sets of resource managers.
