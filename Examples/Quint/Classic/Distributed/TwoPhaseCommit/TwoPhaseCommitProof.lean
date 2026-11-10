module

public import Veil.Quint

/-!
# Two-phase commit: consistency for every set of resource managers

Quint checks `consistencyInv` of `two_phase_commit.qnt` on one instance, three resource
managers, by exploring its 288 states (`quint verify --backend tlc`, or Apalache up to a bound).
Here the constant `resourceManagers` stays a parameter of the Veil module, and the invariant is
*proved* for every set of resource managers, of any size.

The Quint module below is `two_phase_commit` from
https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/classic/distributed/TwoPhaseCommit/two_phase_commit.qnt
with comments written in Lean syntax.

`consistencyInv` is not inductive by itself. The seven Veil invariants after the module
strengthen it, following the reasoning of Lamport's TwoPhase proof: a `Commit` message exists
exactly when the transaction manager has committed, it requires a `Prepared` message from every
resource manager, and a resource manager that has sent `Prepared` can only abort after an
`Abort` message, which a committing transaction manager never sends.

Every verification condition is closed by `quint_grind` (Lean's `grind` with the frontend's
lemmas about sets and maps), so the result is a Lean proof; no SMT solver is trusted.
-/

macro_rules | `(tactic| veil_solve) => `(tactic| quint_grind)

module two_phase_commit {
  const resourceManagers: Set[str]

  type ResourceManagerState = Working | Prepared | Committed | Aborted
  type TransactionManagerState = Init | TMCommitted | TMAborted
  type Message =
    | Abort
    | Commit
    | RMPrepared(str)

  var RM::states: str -> ResourceManagerState
  var TM::state: TransactionManagerState
  --/ The set of resource managers from which the transaction manager has
  --/ received RMPrepared messages
  var TM::preparedRMs: Set[str]
  var messages: Set[Message]

  action init = all {
    RM::states' = resourceManagers.mapBy(r => Working),
    TM::state' = Init,
    TM::preparedRMs' = Set(),
    messages' = Set(),
  }

  /- Transaction Manager (TM) actions -/

  --/ The transaction manager receives a RMPrepared(rm) message from the resource manager rm
  action TM::addPreparedResourceManager(resourceManager: str): bool = all {
    TM::state == Init,
    messages.contains(RMPrepared(resourceManager)),
    TM::preparedRMs' = TM::preparedRMs.union(Set(resourceManager))
  }

  --/ The transaction manager commits the transaction; enabled iff the
  --/ transaction manager is in its initial state and every resource manager has
  --/ sent an RMPrepared message.
  action TM::decideOnCommit = all {
    TM::state == Init,
    TM::preparedRMs == resourceManagers,
    TM::state' = TMCommitted,
    messages' = messages.union(Set(Commit))
  }

  --/ The transaction manager spontaneously aborts the transaction
  action TM::decideOnAbort = all {
    TM::state == Init,
    TM::state' = TMAborted,
    messages' = messages.union(Set(Abort))
  }

  /- Resource Manager (RM) actions -/

  --/ A resource manager prepares
  action RM::prepare(resourceManager: str): bool = all {
    RM::states.get(resourceManager) == Working,
    RM::states' = RM::states.set(resourceManager, Prepared),
    messages' = messages.union(Set(RMPrepared(resourceManager)))
  }

  --/ A resource manager aborts, either spontaneously or because of an Abort message
  action RM::abort(resourceManager: str): bool = all {
    or {
      -- Resource manager chooses to abort
      RM::states.get(resourceManager) == Working,
      -- Resource manager receives an abort message from the transaction manager
      messages.contains(Abort),
    },
    RM::states' = RM::states.set(resourceManager, Aborted),
    -- There is no need to let others know that this resource manager aborted
    messages' = messages
  }

  -- A resource manager commits due to a Commit message
  action RM::commit(resourceManager: str): bool = all {
    messages.contains(Commit),
    RM::states' = RM::states.set(resourceManager, Committed),
    messages' = messages
  }

  action step = any {
    -- Resource manager actions
    all {
      nondet rm = resourceManagers.oneOf()
      any { RM::prepare(rm), RM::abort(rm), RM::commit(rm) },
      TM::state' = TM::state,
      TM::preparedRMs' = TM::preparedRMs,
    },
    -- Transaction manager decisions (commit or abort)
    all {
      any { TM::decideOnCommit, TM::decideOnAbort },
      TM::preparedRMs' = TM::preparedRMs,
      RM::states' = RM::states,
    },
    -- Transaction managers message consumption
    all {
      nondet rm = resourceManagers.oneOf()
      TM::addPreparedResourceManager(rm),
      TM::state' = TM::state,
      RM::states' = RM::states,
      messages' = messages,
    }
  }

  --/ Two resource managers have not arrived at conflicting decisions
  val consistencyInv = tuples(resourceManagers, resourceManagers).forall(((r1, r2)) =>
    not(RM::states.get(r1) == Committed and RM::states.get(r2) == Aborted)
  )
}

open ResourceManagerState TransactionManagerState Message

quint_invariant consistencyInv
-- The transaction manager has committed iff the `Commit` message was sent.
invariant [commit_iff] TM_state = TMCommitted ↔ Commit ∈ messages
-- An `Abort` message comes from an aborted transaction manager.
invariant [abort_tm] Abort ∈ messages → TM_state = TMAborted
-- The transaction manager records only resource managers that sent `Prepared`.
invariant [prepared_sent] ∀ r, r ∈ TM_preparedRMs → RMPrepared r ∈ messages
-- A resource manager that sent `Prepared` is no longer working.
invariant [prepared_not_working] ∀ r, r ∈ resourceManagers → RMPrepared r ∈ messages →
  Quint.Map.get RM_states r ≠ Working
-- A resource manager commits only after the `Commit` message.
invariant [committed_msg] ∀ r, r ∈ resourceManagers → Quint.Map.get RM_states r = Committed →
  Commit ∈ messages
-- `Commit` is sent only when every resource manager has sent `Prepared`.
invariant [commit_all_prepared] Commit ∈ messages → ∀ r, r ∈ resourceManagers → RMPrepared r ∈ messages
-- A resource manager that aborts after sending `Prepared` received an `Abort` message.
invariant [aborted_unprepared] ∀ r, r ∈ resourceManagers → Quint.Map.get RM_states r = Aborted →
  RMPrepared r ∉ messages ∨ Abort ∈ messages

#gen_spec

/- A sanity check that the strengthened invariant holds on Quint's instance (288 states, as for
`consistencyInv` alone). -/
#model_check interpreted { resourceManagers := Quint.Set.ofList ["rm1", "rm2", "rm3"] } { }

/- The proof: every invariant holds initially and is preserved by every action, for every value
of `resourceManagers`. -/
set_option veil.solver "custom" in
#check_invariants

end two_phase_commit
