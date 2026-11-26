module

public import Veil

/-! # A ten-minute Veil example: a job queue

A client submits jobs to a queue; a worker completes the job at the head or
puts it back at the end.
This file accompanies the tutorial in `README.md` and shows every Veil
construct the assignment needs. It is unrelated to the protocol you will model.

    lake lean Examples/Assignment/JobQueue.lean
-/

veil module JobQueue

open Lentil  -- temporal operators

-- Typing the temporal symbols in VS Code (Lean 4 extension): type the
-- abbreviation, then a space or Tab.
--   □  \square      ◇  \Diamond     ↝  \leadsto
--   ⌜  \ulcorner    ⌝  \urcorner    ⟨ ⟩  \<  \>
--   𝒲ℱ  \McW\McF   𝒮ℱ  \McS\McF

/-! ## Types, constants and state -/

-- An uninterpreted type: verification quantifies over it, model checking
-- instantiates it (`job := Fin 2` below).
type job

-- A constant of the model (part of the "theory"), fixed per check.
immutable individual maxJobs : Nat

individual queue : List job      -- jobs waiting for the worker
individual submitted : Nat       -- history: how many jobs were ever submitted
individual finished : List job   -- history: the jobs the worker completed

#gen_state

/-! ## Initial state -/

after_init {
  queue := []
  submitted := 0
  finished := []
}

/-! ## Actions: atomic steps, interleaved in any order -/

action submit (j : job) {
  require submitted < maxJobs    -- the step is enabled only if this holds
  queue := queue ++ [j]
  submitted := submitted + 1
}

action work {
  let q := queue                 -- read the field once, so that `h` talks about `q`
  require h : q ≠ []
  finished := finished ++ [q.head h]
  queue := q.tail
}

-- The worker may give up on the job at the head and put it back at the end.
action requeue {
  let q := queue
  require h : q ≠ []
  queue := q.tail ++ [q.head h]
}

/-! ## Properties -/

-- Safety: holds in every reachable state.
safety [no_job_lost_or_invented] finished.length + queue.length = submitted

-- A reachability probe: a claim that is meant to FAIL. Its counterexample is
-- a run in which two jobs get finished, which shows that the model can do it.
temporal [probe_two_finished] □ ⌜ finished.length < 2 ⌝

-- Liveness without fairness: FAILS, because a run may `requeue` forever.
temporal [drains_unfair] □ ◇ ⌜ queue = [] ⌝

-- Liveness under weak fairness of `work`: HOLDS.
temporal [drains] 𝒲ℱ work → □ ◇ ⌜ queue = [] ⌝

#gen_spec

/-! ## Checks -/

-- Every reachable state of one finite instance, against the safety clauses.
#model_check { job := Fin 2 } { maxJobs := 3 }

-- Expected violations: the option turns the error into a report.
set_option veil.violationIsError false in
#temporal_check [probe_two_finished] { job := Fin 2 } { maxJobs := 2 }

set_option veil.violationIsError false in
#temporal_check [drains_unfair] { job := Fin 2 } { maxJobs := 2 }

-- Every infinite run of the instance, against the named property.
#temporal_check [drains] { job := Fin 2 } { maxJobs := 2 }

end JobQueue
