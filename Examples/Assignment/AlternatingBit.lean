module

public import Veil

/-! # Assignment: the Alternating Bit Protocol

This file is a skeleton. The task is described in `README.md` in this directory.
Everything below the module header is yours to change, including the parts that are given.

Check the file from the repository root with

    lake lean Examples/Assignment/AlternatingBit.lean

or open it in VS Code with the Lean 4 extension and read the results in the InfoView.
-/

veil module AlternatingBit

-- Needed for the temporal operators (`□`, `◇`, `𝒲ℱ`, ...) used in Part 4.
open Lentil

/-! ## Part 1: types, parameters and state

Decide what the sender, the receiver and the two links consist of, and what
(if anything) you must add to the state to be able to say what the protocol
is supposed to achieve. -/

-- The payloads handed to the sender.
type data

-- TODO: bounds or other constants of the model, e.g.
-- immutable individual maxItems : Nat

-- TODO: replace this placeholder with your state.
individual placeholder : Bool

#gen_state

/-! ## Initial state -/

after_init {
  -- TODO
  placeholder := false
}

/-! ## Part 1, continued: actions

One action per event of the protocol or of its environment. Each action is atomic.
Decide which events exist: what the sender and the receiver do, and what the
links may do to the frames in transit. -/

-- TODO: actions. A stub with the expected shape:
--
-- action sendFrame {
--   require ...        -- when is this step possible?
--   ...                -- what does it change?
-- }

/-! ## Part 2: safety

State what must hold in every reachable state. `safety` clauses are checked by
`#model_check` and `#check_invariants`; give each one a name. -/

-- TODO: safety [name] ...

/-! ## Part 3 and Part 4: reachability probes and temporal properties

Temporal properties must be declared before `#gen_spec`. A probe is a property
you expect to FAIL, whose counterexample is the witness you are after. -/

-- TODO: temporal [name] ...

#gen_spec

/-! ## Checks

Keep the instances small: every command here is re-run whenever the file is
elaborated. A check that is expected to report a violation must be preceded by
`set_option veil.violationIsError false in`, on the line directly above it. -/

-- TODO: #model_check { data := Fin 2 } { maxItems := ... }

-- TODO: set_option veil.violationIsError false in
--       #temporal_check [probe] { data := Fin 2 } { maxItems := ... }

-- TODO: #temporal_check [liveness] { data := Fin 2 } { maxItems := ... }

end AlternatingBit
