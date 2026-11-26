# Assignment: the Alternating Bit Protocol in Veil

In this assignment you formalise a small distributed protocol in
[Veil](https://github.com/verse-lab/veil), a verifier for transition systems
embedded in the Lean 4 proof assistant, and check that your formalisation
says what you intend it to say.

We assume you have not used Veil before. Part of what we want to see is how
you get productive with an unfamiliar formal-methods tool. You may use any
tools you like, including AI coding agents, and you may let them write as
much of the code as you wish. You are responsible for every modelling
decision in what you submit.

**Time cap: 3 to 4 hours**, including setup and reading. Stop when you reach
the cap and submit what you have, with a note on what is missing. A smaller
model that you understand fully is worth more than a larger one you cannot
explain.

The submission is followed by a discussion of about 45 minutes. It is about
your design choices: why the model looks the way it does, why you picked
these properties, and what each check does and does not establish. Have the
file open and ready to edit during the discussion.

| File | What it is |
| --- | --- |
| [AlternatingBit.lean](AlternatingBit.lean) | The skeleton you complete |
| [NOTES.md](NOTES.md) | A one-page template for your design notes |
| [JobQueue.lean](JobQueue.lean) | A small worked Veil example, used by the tutorial below |

## 1. Setup

Follow the [build instructions](../../README.md#build) in the repository
README: install the system dependencies and Lean (through `elan`), clone the
repository, and run `lake build`. The first build compiles Veil and its
dependencies and takes a while, so start it before you read on.

Check a single file from the repository root with

```bash
lake lean Examples/Assignment/JobQueue.lean
```

or open the repository in VS Code with the
[Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4),
put the cursor on a command such as `#model_check`, and read the result in
the InfoView panel. The editor shows counterexample traces as interactive
widgets; the command line prints them as text.

If you cannot build locally, the [online playground](https://try.veil.dev/)
runs Veil in the browser.

## 2. The protocol

The Alternating Bit Protocol (ABP) transmits a sequence of data items from a
*sender* to a *receiver* over links that may lose what is sent on them. It
was published by Bartlett, Scantlebury and Wilkinson in 1969 and is the
simplest retransmission protocol that is still interesting.

- The sender has one item to transmit at a time. It attaches a one-bit
  sequence number to the item and sends the resulting frame on the *data
  link*. It keeps resending the same frame until it receives an
  acknowledgement carrying the same bit. Then it flips its bit and moves on
  to the next item.
- The receiver remembers which bit it expects next. When a frame with the
  expected bit arrives, it delivers the item to its client and flips the
  expected bit. When a frame with the other bit arrives, it does not deliver
  it: the frame is a retransmission of something it already has.
- The receiver sends acknowledgements on the *ack link*, each carrying the
  bit of the last frame it accepted. It may send them repeatedly.
- Either link may lose frames at any time.

This description leaves a number of things open, and so do the sources
below. What is in transit on a link, and how much of it? Can a link do
anything to frames other than lose them? Where do the data items come from,
and how many are there? What does it mean, precisely, for the transmission
to be correct? Settling such questions is the main part of the assignment.

Sources:

- K. A. Bartlett, R. A. Scantlebury, P. T. Wilkinson.
  [A note on reliable full-duplex transmission over half-duplex links](https://doi.org/10.1145/362946.362970).
  Communications of the ACM 12(5), 1969. The original paper.
- [Alternating bit protocol](https://en.wikipedia.org/wiki/Alternating_bit_protocol)
  on Wikipedia.
- A [TLA+ specification](https://github.com/tlaplus/Examples/tree/master/specifications/SpecifyingSystems/TLC)
  (`AlternatingBit.tla`, with `ABCorrectness.tla`) from Lamport's
  *Specifying Systems*. You may consult it. If your model
  differs from it, be ready to say where and why.

## 3. The task

Complete [AlternatingBit.lean](AlternatingBit.lean). The skeleton fixes
nothing except the module name and one type; change anything else.

**Part 1: the model.** Declare the state and the actions of the protocol and
of its environment (the links, and whoever supplies the data). Every `Nat`,
`List` or bound in the state is a decision, and so is every `require`. Keep
the model small enough for exhaustive checking on a small instance.

**Part 2: safety.** State, as `safety` clauses, what the protocol
guarantees in every reachable state. Choose the properties yourself. Aim for
a set that a wrong protocol would violate: ask what a client of the receiver
relies on, and whether your clauses would notice a lost, duplicated,
reordered or invented item. Check them with `#model_check`.

**Part 3: reachability.** A model in which nothing can happen satisfies
every safety property. Show that yours is not vacuous: give witnesses, found
by Veil, that the interesting behaviours occur. At least:

- several items are delivered, one after another;
- a link loses a frame, and the transmission still continues;
- a retransmitted frame reaches the receiver and is not delivered a second
  time.

Add any other witness that you would want to see before trusting the model.

**Part 4: liveness.** State, as a `temporal` property, that the
transmission makes progress, and check it with `#temporal_check`. You will
need fairness assumptions. Find a set of assumptions under which the
property holds, and keep at least one check in the file that shows a weaker
set under which it fails. Be ready to say what each assumption means for a
real sender, receiver or link, and whether it is reasonable to assume.

**Part 5: notes.** Fill in [NOTES.md](NOTES.md): one page at most, in your
own words. It is the starting point of the discussion.

### What to submit

- `AlternatingBit.lean`, such that `lake lean
  Examples/Assignment/AlternatingBit.lean` terminates in a few minutes at
  most and reports no error. Checks that are expected to find a violation
  stay in the file, marked as such (see the tutorial for how).
- `NOTES.md`.
- If you used an AI agent, say which one and roughly how. This is not held
  against you.

### What is not required

- A proof for all instances. Veil can prove safety for unboundedly many
  states by checking an inductive invariant (`#check_invariants`), and can
  prove temporal properties (`prove_temporal_by`). Both are out of scope
  here. If you finish early, an inductive invariant for one of your safety
  properties is a good optional extension, and may require a different
  encoding of the state.
- Large instances. Two data values and a handful of items are enough.
- Covering every variant of the protocol in the literature.

## 4. Veil in fifteen minutes

Open [JobQueue.lean](JobQueue.lean) next to this section. It is a complete
module with every construct you need.

### A module

A Veil module describes a transition system: a state, a set of initial
states, and atomic actions. A run starts in an initial state and repeatedly
takes one enabled action; the actions of different components interleave in
any order.

```lean
veil module JobQueue

type job                           -- an abstract type
immutable individual maxJobs : Nat -- a constant of the model

individual queue : List job        -- mutable state
individual submitted : Nat
individual finished : List job

#gen_state                         -- closes the state declaration

after_init {                       -- the initial states
  queue := []
  submitted := 0
  finished := []
}

action submit (j : job) {          -- one action per kind of step
  require submitted < maxJobs
  queue := queue ++ [j]
  submitted := submitted + 1
}
```

The order of the sections is fixed: types and state, `#gen_state`,
`after_init`, actions, properties, `#gen_spec`, and then the checks.

State components are `individual`s (one value), `relation`s (Boolean-valued,
e.g. `relation pending (n : node) (m : msg) : Bool`) and `function`s. An
`immutable` component is a constant. Values can have any Lean type with
decidable equality: `Bool`, `Nat`, `List`, pairs, and structures marked
`@[veil_decl]`. You can also declare finite enumerations with
`enum phase = {idle, waiting}`.

Inside an action:

| Statement | Meaning |
| --- | --- |
| `require P` | The action is enabled only in states where `P` holds |
| `x := e` | Update a state component |
| `let x := e` | A local name |
| `let x :\| P` | Choose any `x` satisfying `P`; one run per choice |
| `if P then ... else ...` | Conditional |

An action's parameters are chosen by the environment: `submit (j : job)`
stands for one action per job. Whatever an action does not assign stays
unchanged. The full list is in the
[DSL reference](../../docs/DSL-Reference.md#imperative-dsl-keywords).

### Properties

```lean
safety [no_job_lost_or_invented] finished.length + queue.length = submitted

temporal [drains] 𝒲ℱ work → □ ◇ ⌜ queue = [] ⌝
```

A `safety` clause is a predicate on states that must hold in every
reachable state. A `temporal` clause is a formula of linear temporal logic
over runs:

| Syntax | Meaning |
| --- | --- |
| `⌜ P ⌝` | The state predicate `P` holds now |
| `□ φ`, `◇ φ` | `φ` holds always, eventually |
| `φ ↝ ψ` | Whenever `φ` holds, `ψ` holds then or later |
| `𝒲ℱ a` | Weak fairness: if `a` stays enabled forever, it is taken |
| `𝒮ℱ a` | Strong fairness: if `a` is enabled again and again, it is taken |
| `∀ x, φ` | Quantification, e.g. `∀ j, 𝒲ℱ (submit j)` |

The symbols are Unicode; copy them from here or from the examples. Declare
all properties before `#gen_spec`.

### Checks

```lean
#gen_spec

#model_check { job := Fin 2 } { maxJobs := 3 }

set_option veil.violationIsError false in
#temporal_check [probe_two_finished] { job := Fin 2 } { maxJobs := 2 }

#temporal_check [drains] { job := Fin 2 } { maxJobs := 2 }
```

- `#model_check` enumerates every reachable state of one finite instance
  and checks all `safety` clauses in each. The first argument instantiates
  the types, the second the `immutable` constants. It prints the number of
  states explored, or a trace from an initial state to a violation. See the
  [Model Checker Guide](../../docs/ModelChecker-Guide.md).
- `#temporal_check [name]` checks the named `temporal` properties on every
  infinite run of the instance. A violation is a *lasso*: a stem followed by
  a loop that repeats forever. See the
  [Temporal Checker Guide](../../docs/TemporalChecker-Guide.md).
- A **reachability probe** is a property you expect to fail, whose
  counterexample is the run you are looking for. In `JobQueue.lean`,
  `□ ⌜ finished.length < 2 ⌝` fails with a run in which two jobs finish.
  The line `set_option veil.violationIsError false in`, directly above a
  check, turns the expected violation from an error into a report.
- `sat trace { ... }` and `unsat trace { ... }` ask an SMT solver whether a
  run of a given shape exists, for all instances at once
  ([reference](../../docs/DSL-Reference.md#symbolic-bounded-model-checking)).
  `#check_invariants` asks it to prove the safety clauses inductive. Both
  need state that the solver can express: relations and functions over
  abstract types work well, while `List`-valued state often does not
  translate. You do not need either for this assignment.

A passing check on one instance is a test of that instance. It says nothing
about other sizes, and nothing at all if the instance cannot do anything
interesting; that is what the probes are for.

### Things that cost time

- **Every check re-runs on every edit** in the editor. Keep instances tiny
  (`Fin 2`, bounds of 2 or 3) while you work, and comment out slow checks.
- **Unbounded state.** A counter or a list that can grow forever makes the
  state space infinite, and the checker will not terminate. Bound growth
  with a `require` against a constant, as `submit` does. Then ask what the
  bound does to your properties, in particular the temporal ones.
- **Runs do not idle.** A run of `#temporal_check` takes a step whenever
  some action is enabled, and repeats a state forever only when none is. A
  liveness property can therefore hold with no fairness assumption simply
  because nothing else can happen. `drains_unfair` in `JobQueue.lean` fails
  only because `requeue` offers an alternative.
- **Reading a list head.** `q.head h` needs a proof `h : q ≠ []`. The idiom
  is to copy the field into a local first: `let q := queue`, then
  `require h : q ≠ []`, as in `work`.
- **`Bool` and `Prop`.** Declare relations with result type `Bool`, and
  phrase properties so that they can be evaluated: prefer list functions
  and bounded quantifiers to `∃ xs : List _, ...`.
- **Comments.** Use `--` above Veil declarations. A doc comment `/-- ... -/`
  before `type` or `individual` is a syntax error.
- **Order of commands.** `set_option ... in` must be directly above the
  check it applies to. Put any `sat trace` and `unsat trace` queries at the
  end of the module, after all other checks.
- **Names.** Give every property a name in brackets; results refer to it.

## 5. References

Veil:

- [Repository README](../../README.md): overview and build instructions.
- [Examples/Tutorial/Ring.lean](../Tutorial/Ring.lean): a commented
  walkthrough of a leader-election protocol and the main commands. Read this
  one if you read only one.
- [Examples/Tutorial/FloodSet.lean](../Tutorial/FloodSet.lean): the full
  workflow, from modelling to an interactive proof.
- [Examples/Demo/FloodSet/FloodSetLiveness.lean](../Demo/FloodSet/FloodSetLiveness.lean):
  temporal properties and `#temporal_check` on a real protocol.
- [Examples/LivenessMC/](../LivenessMC/): more temporal examples, including
  fairness assumptions of both kinds.
- [DSL reference](../../docs/DSL-Reference.md),
  [Model Checker Guide](../../docs/ModelChecker-Guide.md),
  [Temporal Checker Guide](../../docs/TemporalChecker-Guide.md).
- [Website](https://veil.dev/), [online playground](https://try.veil.dev/),
  and the paper
  [Veil: A Framework for Automated and Interactive Verification of Transition Systems](https://ilyasergey.net/assets/pdf/papers/veil-cav25.pdf)
  (CAV 2025).
- A [blog walkthrough](https://proofsandintuitions.net/2026/02/09/distributed-verification-veil/)
  of verifying a distributed protocol in Veil.
- For AI agents: [AGENTS.md](../../AGENTS.md) and the skills in
  [.agents/skills/](../../.agents/skills/).

Background:

- L. Lamport. [Specifying Systems](https://lamport.azurewebsites.net/tla/book.html),
  Chapter 8 (liveness and fairness) and Chapter 14 (model checking, with
  the Alternating Bit Protocol as the running example).
- Lean 4: [documentation](https://lean-lang.org/learn/). You need very
  little Lean for this assignment beyond `List` functions such as `++`,
  `head`, `tail`, `take` and `length`.

Questions about the task or the tools are welcome before and during the
assignment. Asking a good question is not held against you either.
