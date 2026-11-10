"""Per-example configuration for `quint_examples.py`.

For each Quint file (path relative to `examples/` in the Quint repository):

- `tails`: Veil commands to insert after a module (by its Quint name). A module with state is
  still open there, so these are Veil commands about it; they end with `end <module>`.
- `notes`: text for the header of the Lean file (what is checked, how it relates to Quint's own
  checks, deviations).
- `footer`: Lean code after the last module (e.g. proofs about a module).

Quint's reference results come from `quint verify --backend tlc` (TLC) and `quint verify`
(Apalache), and from `quint run`/`quint test`; see Examples/Quint/README.md.
"""

DEFAULT_NOTES = """The module elaborates into a Veil module; no Veil checks are configured for it."""


SIM = '(numTraces := 1000) (maxSteps := 20) (seed := 42)'


EXPECT = 'set_option veil.violationIsError false in\n'


def sim(module, invariants=(), inst='{ }', theory='{ }', opts=SIM, extra='', end=True):
    """A Veil section that declares invariants and runs random simulation (like `quint run`)."""
    s = ''
    if invariants:
        s += 'quint_invariant ' + ', '.join(invariants) + '\n'
    s += extra
    s += '#gen_spec\n'
    s += f'#simulate {inst} {theory} {opts}\n'
    if end:
        s += f'end {module}\n'
    return s


def both(module, invariants=(), depth=3, extra='', inst='{ }', violation=False):
    """Depth-bounded model checking (like `quint verify --max-steps`) and simulation.
    With `violation`, a violation is expected and reported as information."""
    s = ''
    if invariants:
        s += 'quint_invariant ' + ', '.join(invariants) + '\n'
    s += extra
    s += '#gen_spec\n'
    s += (EXPECT if violation else '') + f'#model_check interpreted {inst} {{ }} (maxDepth := {depth})\n'
    s += (EXPECT if violation else '') + f'#simulate {inst} {{ }} {SIM}\n'
    s += f'end {module}\n'
    return s


LENIENT = 'set_option quint.lenient true\n'
LENIENT_NOTE = """This file uses constructs that the frontend does not translate (see the warnings
it reports, and the gaps in `.agents/skills/quint-to-veil/references/frontend.md`); it is
elaborated with `quint.lenient`, which skips the definitions and actions that do not elaborate
and reports each of them as a warning."""

INIT_NEXT = ""'set_option quint.init "Init"\nset_option quint.step "Next"\n'


def mc(module, invariants=(), inst='{ }', theory='{ }', opts='', extra='', end=True, mode='interpreted',
       violation=False):
    """A Veil section that declares invariants, generates the specification and model checks it."""
    s = ''
    if invariants:
        s += 'quint_invariant ' + ', '.join(invariants) + '\n'
    s += extra
    s += '#gen_spec\n'
    s += (EXPECT if violation else '') + f'#model_check{(" " + mode) if mode else ""} {inst} {theory}{(" " + opts) if opts else ""}\n'
    if end:
        s += f'end {module}\n'
    return s


CONFIG = {
    'classic/distributed/TwoPhaseCommit/two_phase_commit.qnt': {
        'notes': """Two-phase commit (Lamport's TwoPhase). Checked with Veil's explicit-state
model checker on the instance `two_phase_commit_3` (three resource managers), as Quint's dashboard
does: 288 reachable states, the same count as `quint verify --backend tlc`, and `consistencyInv`
holds.""",
        'tails': {
            'two_phase_commit_3': mc('two_phase_commit_3', ['consistencyInv']),
        },
    },
    'classic/distributed/TeachingConcurrency/teaching.qnt': {
        'notes': """The algorithm from Lamport's "Teaching Concurrency". `correctness` is checked
by explicit-state model checking for the configured number of processes.""",
        'tails': {
            'teaching': mc('teaching', ['correctness'], mode=''),
        },
    },
    'classic/distributed/TeachingConcurrency/mutex.qnt': {
        'notes': """Mutual exclusion from "Teaching Concurrency". `correctness` and the inductive
invariant `inv` are model checked.""",
        'tails': {
            'mutex': mc('mutex', ['correctness', 'inv']),
        },
    },
    'classic/distributed/ewd840/ewd840.qnt': {
        'notes': """Dijkstra's termination detection (EWD 840), instance `ewd840_3`.""",
        'tails': {
            'ewd840_3': mc('ewd840_3', ['TypeOK', 'Inv', 'TerminationDetection']),
        },
    },
    'classic/distributed/ewd426/ewd426.qnt': {
        'notes': """Dijkstra's self-stabilizing token ring (EWD 426), K-state version.""",
        'tails': {'ewd426': mc('ewd426', mode='')},
    },
    'classic/distributed/ewd426/ewd426_3.qnt': {
        'notes': """EWD 426, three-state version.""",
        'tails': {'ewd426_3': mc('ewd426_3')},
    },
    'classic/distributed/ewd426/ewd426_4.qnt': {
        'notes': """EWD 426, four-state version.""",
        'tails': {'ewd426_4': mc('ewd426_4')},
    },
    'classic/distributed/DiningPhilosophers/DiningPhilosophers5.qnt': {
        'notes': """Dining philosophers with five philosophers.""",
        'tails': {'DiningPhilosophers5': mc('DiningPhilosophers5', ['TypeOk', 'Safety'])},
    },
    'classic/distributed/ReadersWriters/ReadersWriters.qnt': {
        'notes': """Readers and writers, instance `ReadersWriters_5`, with `Init`/`Next` as the
initial and step actions (`quint verify --init=Init --step=Next`).""",
        'pre': {'ReadersWriters': INIT_NEXT},
        'tails': {'ReadersWriters_5': both('ReadersWriters_5', ['Safety'], depth=6)},
    },
    'classic/distributed/LamportMutex/LamportMutex.qnt': {
        'notes': """Lamport's mutual exclusion, instance `LamportMutex_3_10`, with `Init`/`Next`.
As in the TLA+ original, `ClockConstraint` and `BoundedNetwork` bound the state space (they are
state constraints, TLC's `CONSTRAINT`).""",
        'pre': {'LamportMutex': INIT_NEXT},
        'tails': {'LamportMutex_3_10': both('LamportMutex_3_10', ['Mutex'], depth=12,
                                            extra='quint_constraint ClockConstraint, BoundedNetwork\n')},
    },
    'classic/distributed/Paxos/Paxos.qnt': {
        'notes': """Single-decree Paxos, instance `Paxos_val2_accept3_quorum2`, with `Init`/`Next`.""",
        'pre': {'Paxos': INIT_NEXT + 'set_option quint.skipParametric true\n'},
        'copies': {
            'Paxos': [('Paxos_small', [('val Ballot = Nat', 'val Ballot = (0).to(2)'),
                                       ('import Voting(Value = Value, Acceptor = Acceptor, Quorum = Quorum)',
                                        'import Voting(Value = Value, Acceptor = Acceptor, Quorum = Quorum, Ballot = Ballot)')], '')],
            'Paxos_val2_accept3_quorum2': [('Paxos_small_val2_accept3_quorum2',
                                            [('import Paxos(', 'import Paxos_small(')],
                                            mc('Paxos_small_val2_accept3_quorum2', ['Inv'], violation=True))],
        },
    },
    'classic/distributed/ReliableBroadcast/reliablebc.qnt': {
        'notes': """Folklore reliable broadcast.""",
        'tails': {'reliablebc': mc('reliablebc')},
    },
    'classic/distributed/TwoLayeredCache/two_layered_cache.qnt': {
        'notes': """A two-layered cache.""",
        'tails': {'two_layered_cache': mc('two_layered_cache', mode='')},
    },
    'classic/sequential/BinSearch/BinSearch.qnt': {
        'notes': """Binary search, instance `BinSearch10`.""",
        'tails': {'BinSearch10': mc('BinSearch10')},
    },
    'puzzles/river/river.qnt': {
        'notes': """The river crossing puzzle.""",
        'tails': {'river': mc('river', ['safety'])},
    },
    'puzzles/prisoners/prisoners.qnt': {
        'notes': """The prisoners and the switch room, instance `prisoners3`.""",
        'tails': {'prisoners3': mc('prisoners3', ['safetyInv', 'countInv'])},
    },
    'classic/distributed/ConsensusAlgorithm/ConsensusAlg.qnt': {
        'notes': """A synchronous consensus algorithm with crash faults. With proper values
(`properValues`: at most `MAX_FAULTS` crashes) `agreement` holds; with `badValues` (more crashes
than tolerated) it is violated, which Quint's README documents.""",
        'tails': {
            'properValues': both('properValues', ['agreement', 'validity'], depth=2),
            'badValues': both('badValues', ['agreement'], depth=2, violation=True),
        },
    },
    'classic/distributed/ConsensusAlgorithm/KSetAgreementConsensus.qnt': {
        'notes': """k-set agreement, on top of `ConsensusAlg`.""",
        'tails': {
            'KSetProperValues': both('KSetProperValues', ['kSetAgreement'], depth=2),
            'KSetBadValues': both('KSetBadValues', ['kSetAgreement'], depth=2, violation=True),
        },
    },
    'classic/distributed/Bakery/bakery.qnt': {
        'notes': """Lamport's bakery algorithm, instance `verification`. Quint checks the inductive
invariant `IndInv` with Apalache; here `correctness` and `IndInv` are model checked.""",
        'tails': {'verification': both('verification', ['correctness', 'IndInv'], depth=5)},
    },
    'classic/distributed/ClockSync/clockSync6.qnt': {
        'notes': """Clock synchronization, instance `clock_sync4`, invariant `skew_inv`.""",
        'copies': {
            'clock_sync': [('clock_sync_small', [('nondet delta = oneOf(Int)', 'nondet delta = oneOf((0).to(2))')], '')],
            'clock_sync4': [('clock_sync4_small', [('import clock_sync(', 'import clock_sync_small(')],
                             both('clock_sync4_small', ['skew_inv'], depth=4))],
        },
    },
    'classic/distributed/TwoPhaseCommit/two_phase_commit_modules.qnt': {
        'notes': """Two-phase commit, split into modules for the messages, the resource managers
and the transaction manager.""",
        'tails': {'two_phase_commit_tests': mc('two_phase_commit_tests', ['inv'])},
    },
    'classic/distributed/Paxos/Voting.qnt': {
        'notes': """The voting algorithm underlying Paxos; it is parameterized by constants and
instantiated by `Paxos.qnt`.""",
    },
    'games/tictactoe/tictactoe.qnt': {
        'notes': """Tic-tac-toe with a strategy for X. `NotStalemate` is violated (the game can
end in a stalemate), as Quint's comment says.""",
        'tails': {'tictactoe': mc('tictactoe', ['inv'])},
    },
    'games/secret-santa/secret_santa.qnt': {
        'notes': """Secret Santa, instance `quint_team_secret_santa`.""",
        'tails': {'quint_team_secret_santa': mc('quint_team_secret_santa', ['inv'], violation=True)},
    },
    'games/rock_paper_scissors/play_rock_paper_scissors.qnt': {
        'notes': """Rock, paper, scissors.""",
        'tails': {'play_rock_paper_scissors': mc('play_rock_paper_scissors', ['winInv'])},
    },
    'games/mafia_werewolf/play_mafia.qnt': {
        'notes': """Mafia (Werewolf).""",
        'tails': {'play_mafia': both('play_mafia', ['correct_game_status'], depth=3, violation=True)},
    },
    'tutorials/hello.qnt': {
        'notes': """The hello-world state machine of Quint's tutorial.""",
        'tails': {'hello': mc('hello')},
    },
    'tutorials/repl/kettle.qnt': {
        'notes': """The kettle from Quint's REPL tutorial.""",
        'tails': {'kettle': both('kettle', depth=5)},
    },
    'tutorials/coin.qnt': {
        'notes': """The Solidity coin contract. Amounts range over `0.to(MAX_UINT)`, so the
model checker and the simulator use the bounded copy below.""",
        'copies': {'coin': [('coin_small', [('nondet amount = (0).to(MAX_UINT).oneOf()', 'nondet amount = (0).to(10).oneOf()')],
                             both('coin_small', ['balancesRangeInv', 'totalSupplyDoesNotOverflowInv'], depth=3))]},
    },
    'language-features/booleans.qnt': {'tails': {'booleans': mc('booleans')}},
    'language-features/counters.qnt': {'tails': {'counters': both('counters', depth=5)}},
    'language-features/integers.qnt': {'tails': {'integers': both('integers', depth=3)}},
    'language-features/lists.qnt': {
        'notes': LENIENT_NOTE,
        'pre': {'lists': LENIENT},
        'tails': {'lists': both('lists', depth=3)}},
    'language-features/maps.qnt': {'tails': {'maps': both('maps', depth=3)}},
    'language-features/sets.qnt': {'tails': {'sets': both('sets', depth=3)}},
    'language-features/tuples.qnt': {'tails': {'tuples': both('tuples', depth=3)}},
    'language-features/records.qnt': {
        'notes': LENIENT_NOTE,
        'pre': {'records': LENIENT},
        'tails': {'records': both('records', depth=3)}},
    'language-features/generate.qnt': {'notes': LENIENT_NOTE, 'pre': {'gen': LENIENT}},
    'language-features/imports.qnt': {'notes': LENIENT_NOTE, 'pre': {'Math': LENIENT}},
    'cosmos/ics23/ics23.qnt': {'notes': LENIENT_NOTE, 'pre': {'basics': LENIENT}},
    'language-features/option.qnt': {'tails': {'option': both('option', depth=3)}},
    'language-features/nondetEx.qnt': {'tails': {'nondetEx': both('nondetEx', depth=3)}},
    'language-features/weakFairness.qnt': {'tails': {'weakFairness': mc('weakFairness')}},
    'language-features/strongFairness.qnt': {'tails': {'strongFairness': mc('strongFairness')}},
    'verification/defaultOpNames.qnt': {
        'notes': """A module without state variables, used to test Quint's options for operator
names; it elaborates into a namespace with its definitions.""",
    },
}
