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
SIM_SMALL = '(numTraces := 100) (maxSteps := 10) (seed := 42)'


EXPECT = 'set_option veil.violationIsError false in\n'


def sim(module, invariants=(), inst='{ }', theory='{ }', opts=SIM, extra='', end=True, violation=False):
    """A Veil section that declares invariants and runs random simulation (like `quint run`)."""
    s = ''
    if invariants:
        s += 'quint_invariant ' + ', '.join(invariants) + '\n'
    s += extra
    s += '#gen_spec\n'
    s += (EXPECT if violation else '') + f'#quint_run {inst} {theory} {opts}\n'
    if end:
        s += f'end {module}\n'
    return s


def both(module, invariants=(), depth=3, extra='', inst='{ }', violation=False, mode='interpreted',
         bmc=None):
    """Depth-bounded model checking (like `quint verify --max-steps`) and simulation.
    With `violation`, a violation is expected and reported as information."""
    s = ''
    if invariants:
        s += 'quint_invariant ' + ', '.join(invariants) + '\n'
    s += extra
    s += '#gen_spec\n'
    s += (EXPECT if violation else '') + f'#quint_verify{(" " + mode) if mode else ""} {inst} {{ }} (maxDepth := {depth})\n'
    s += (EXPECT if violation else '') + f'#quint_run {inst} {{ }} {SIM}\n'
    if bmc:
        s += f'quint_bmc {bmc[0]} ' + ', '.join(bmc[1]) + '\n'
    s += f'end {module}\n'
    return s


LENIENT = 'set_option quint.lenient true\n'
LENIENT_NOTE = """This file uses constructs that the frontend does not translate (see the warnings
it reports, and the gaps in `.agents/skills/quint-to-veil/references/frontend.md`); it is
elaborated with `quint.lenient`, which skips the definitions and actions that do not elaborate
and reports each of them as a warning."""

def temporal(holds=(), violated=(), mode='interpreted', inst='{ }'):
    """`#quint_temporal` checks of Quint's temporal properties (the frontend translates them);
    `violated` ones are expected to fail, as with TLC."""
    s = ''
    if holds:
        s += '#quint_temporal ' + ' '.join(f'[{p}]' for p in holds) + f' {mode} {inst} {{ }}\n'
    for p in violated:
        s += EXPECT + f'#quint_temporal [{p}] {mode} {inst} {{ }}\n'
    return s


INIT_NEXT = ""'set_option quint.init "Init"\nset_option quint.step "Next"\n'


def mc(module, invariants=(), inst='{ }', theory='{ }', opts='', extra='', end=True, mode='interpreted',
       violation=False, bmc=None):
    """A Veil section that declares invariants, generates the specification and model checks it."""
    s = ''
    if invariants:
        s += 'quint_invariant ' + ', '.join(invariants) + '\n'
    s += extra
    s += '#gen_spec\n'
    s += (EXPECT if violation else '') + f'#quint_verify{(" " + mode) if mode else ""} {inst} {theory}{(" " + opts) if opts else ""}\n'
    if bmc:
        s += f'quint_bmc {bmc[0]} ' + ', '.join(bmc[1]) + '\n'
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
            'ewd840_3': mc('ewd840_3', ['TypeOK', 'Inv', 'TerminationDetection'], end=False) + temporal(
                ['liveness'], ['falseLiveness']) + 'end ewd840_3\n',
        },
    },
    'classic/distributed/ewd426/ewd426.qnt': {
        'notes': """Dijkstra's self-stabilizing token ring (EWD 426), K-state version.""",
        'tails': {'ewd426': mc('ewd426', mode='', end=False) + temporal(
            ['convergence', 'closure', 'persistence'], mode='') + 'end ewd426\n'},
    },
    'classic/distributed/ewd426/ewd426_3.qnt': {
        'notes': """EWD 426, three-state version.""",
        'tails': {'ewd426_3': mc('ewd426_3', end=False) + temporal(
            ['convergence', 'closure', 'persistence']) + 'end ewd426_3\n'},
    },
    'classic/distributed/ewd426/ewd426_4.qnt': {
        'notes': """EWD 426, four-state version.""",
        'tails': {'ewd426_4': mc('ewd426_4', end=False) + temporal(
            ['convergence', 'closure', 'persistence']) + 'end ewd426_4\n'},
    },
    'classic/distributed/DiningPhilosophers/DiningPhilosophers5.qnt': {
        'notes': """Dining philosophers with five philosophers.""",
        'tails': {'DiningPhilosophers5': mc('DiningPhilosophers5', ['TypeOk', 'Safety'], end=False) + temporal(
            ['DeadlockFreedom', 'LivelockFreedom'], ['DeadlockProperty']) + 'end DiningPhilosophers5\n'},
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
        'notes': """Single-decree Paxos, instance `Paxos_val2_accept3_quorum2`, with `Init`/`Next`.
Quint's own tools do not check this example (Apalache: quint issue #1284). `Ballot = Nat` makes
the state space infinite, so the checks run on a copy with three ballots. `import Voting(...) as V`
adds Voting's variables `V::votes` and `V::maxBal`, which no action of Paxos assigns; `Inv`
refers to them through `V::Inv`, so it fails in the initial state (where `V::maxBal` is the empty
map). Quint would report the missing assignment instead. The violation is therefore expected and
reported as information.""",
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
        'tails': {'BinSearch10': mc('BinSearch10', ['Postcondition', 'InBounds'])},
    },
    'puzzles/river/river.qnt': {
        'notes': """The river crossing puzzle.""",
        'tails': {'river': mc('river', ['safety'])},
    },
    'puzzles/prisoners/prisoners.qnt': {
        'notes': """The prisoners and the switch room, instance `prisoners3`.""",
        'tails': {'prisoners3': mc('prisoners3', ['safetyInv', 'countInv'], end=False) + temporal(
            ['safety'], ['liveness']) + 'end prisoners3\n'},
    },
    'classic/distributed/ConsensusAlgorithm/ConsensusAlg.qnt': {
        'notes': """A synchronous consensus algorithm with crash faults. With proper values
(`properValues`: at most `MAX_FAULTS` crashes) `agreement` holds; with `badValues` (more crashes
than tolerated) it is violated, which Quint's comments document. The initial states alone number
7^5 (every process proposes one of seven values), so, as with `quint run`, the instances are
checked by random simulation.""",
        'tails': {
            'properValues': sim('properValues', ['agreement', 'validity']),
            'badValues': sim('badValues', ['agreement'], violation=True),
        },
    },
    'classic/distributed/ConsensusAlgorithm/KSetAgreementConsensus.qnt': {
        'notes': """k-set agreement, on top of `ConsensusAlg` (imported from its Lean file). The
initial action picks the processes' proposals from `Procs.setOfMaps(...)`: millions of maps for
the eight processes of Quint's instances, which Veil's simulator and model checker enumerate
(Quint's simulator samples one instead). So the instances of the Quint file only elaborate, and
copies with four processes are checked instead: `KSetProperValues_small` (at most `MAX_FAULTS = 2`
crashes, `K = 2`) satisfies `kSetAgreement` and `validity`, and `KSetBadValues_small` (two
crashes, one tolerated, `K = 1`) violates `kSetAgreement`, like Quint's `KSetBadValues`. Their
`consensusRunTest` runs are tested; `consensusDisagreementTest` is not, since its scenario names
the processes of the eight-process instance.""",
        'copies': {
            'KSetProperValues': [('KSetProperValues_small', [(
                'NUM_PPROCESSES = 8, MAX_FAULTS = 3, ACTUAL_FAULTS = 3, K = 2, MAX_ROUNDS = (3/2 + 1)',
                'NUM_PPROCESSES = 5, MAX_FAULTS = 2, ACTUAL_FAULTS = 2, K = 2, MAX_ROUNDS = (2/2 + 1)')],
                sim('KSetProperValues_small', ['kSetAgreement', 'validity']))],
            'KSetBadValues': [('KSetBadValues_small', [(
                'NUM_PPROCESSES = 8, MAX_FAULTS = 3, ACTUAL_FAULTS = 4, K = 2, MAX_ROUNDS = (3/2 + 1)',
                'NUM_PPROCESSES = 5, MAX_FAULTS = 1, ACTUAL_FAULTS = 2, K = 1, MAX_ROUNDS = (1/1 + 1)')],
                sim('KSetBadValues_small', ['kSetAgreement'], violation=True))],
        },
        'no_tests': ['KSetProperValues', 'KSetBadValues'],
        # the scenario of `consensusDisagreementTest` names the processes of the large instance
        'test_patterns': {'KSetBadValues_small': 'consensusRunTest'},
    },
    'cosmos/tendermint/TendermintModels.qnt': {
        'notes': """Three instances of `TendermintTest`. The file elaborates; Veil does not check
it: the Tendermint actions over its record-valued state do not elaborate within Lean's default
heartbeat limit, so neither the instances nor their tests (`#quint_test` would run them through
the instances) are checked.""",
        'no_tests': True,
    },
    'classic/distributed/Bakery/bakery.qnt': {
        'notes': """Lamport's bakery algorithm, instance `verification`. Quint checks the inductive
invariant `IndInv` with Apalache; here `correctness` and `IndInv` are model checked.""",
        'tails': {'verification': both('verification', ['correctness', 'IndInv'], depth=5, mode='')},
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
        'tails': {'tictactoe': mc('tictactoe', ['inv'], end=False) + temporal(
            violated=['XMustEventuallyWin']) + 'end tictactoe\n'},
    },
    'games/secret-santa/secret_santa.qnt': {
        'notes': """Secret Santa, instance `quint_team_secret_santa`.""",
        'tails': {'quint_team_secret_santa': mc('quint_team_secret_santa', ['inv'], violation=True)},
    },
    'games/rock_paper_scissors/play_rock_paper_scissors.qnt': {
        'notes': """Rock, paper, scissors.""",
        'tails': {'play_rock_paper_scissors': mc('play_rock_paper_scissors', ['winInv'],
                                                 bmc=(3, ['winInv']))},
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
    'language-features/lists.qnt': {'tails': {'lists': both('lists', depth=3)}},
    'language-features/maps.qnt': {'tails': {'maps': both('maps', depth=3)}},
    'language-features/sets.qnt': {'tails': {'sets': both('sets', depth=3)}},
    'language-features/tuples.qnt': {'tails': {'tuples': both('tuples', depth=3)}},
    'language-features/records.qnt': {'tails': {'records': both('records', depth=3)}},
    'language-features/generate.qnt': {'notes': """`apalache::generate(n)` in `nondet x: T = apalache::generate(n)`
picks any value of type `T` (`pick T`); there is no bound `n` on its size, so the module elaborates
but is not model checked."""},
    'language-features/imports.qnt': {'notes': LENIENT_NOTE, 'pre': {'Math': LENIENT}},
    'cosmos/ics23/ics23.qnt': {'notes': LENIENT_NOTE, 'pre': {'basics': LENIENT}},
    'language-features/option.qnt': {'tails': {'option': both('option', depth=3)}},
    'language-features/nondetEx.qnt': {
        'notes': """Nondeterminism. `mirrorInv` is checked by depth-bounded model checking, by
simulation, and by Veil's symbolic bounded model checker (`quint_bmc`, SMT) for every execution of
up to three steps.""",
        'tails': {'nondetEx': both('nondetEx', ['mirrorInv'], depth=3, bmc=(3, ['mirrorInv']))}},
    'language-features/weakFairness.qnt': {
        'notes': """Weak fairness. Quint checks the temporal properties with TLC
(`quint verify --backend tlc --temporal ...`); the frontend translates them into Veil's temporal
logic (`weakFair(finish, vars)` is `𝒲ℱ finish`, `p leadsTo q` is `p ↝ q`), and `#quint_temporal`
checks them with Lasso, Veil's verified LTL model checker. As with TLC, the property without
fairness fails (the system may take `noop` forever).""",
        'tails': {'weakFairness': mc('weakFairness', end=False) + temporal(
            ['eventuallyDone', 'notDoneLeadsToDone'], ['notDoneLeadsToDoneNoFairness']) + 'end weakFairness\n'}},
    'language-features/strongFairness.qnt': {
        'notes': """Strong fairness. `weakFair(step, vars)` is fairness of the whole step, which
the frontend splits into one Veil action per branch: it becomes weak fairness of their
disjunction, `(◇ □ (Enabled a_1 ∨ …)) → □ ◇ (⟨ a_1 ⟩ ∨ …)`. As with TLC,
`eventuallyHundredDegrees` holds and `eventuallyHundredDegreesWeakOnly` does not.""",
        'tails': {'strongFairness': mc('strongFairness', end=False) + temporal(
            ['eventuallyHundredDegrees'], ['eventuallyHundredDegreesWeakOnly']) + 'end strongFairness\n'}},
    'verification/defaultOpNames.qnt': {
        'notes': """A module without state variables, used to test Quint's options for operator
names; it elaborates into a namespace with its definitions.""",
    },
}

def small(module, subs, holds=(), violated=(), depth=3, suffix='_small'):
    """Copies of `module` with the substitutions `subs` (smaller domains), for checks like
    `quint verify --max-steps=depth`: one copy checks the invariants `holds`, and one copy per
    invariant of `violated` expects its violation (a model checks all its invariants together)."""
    name = module + suffix
    out = [(name, subs, both(name, list(holds), depth=depth))]
    for v in violated:
        out.append((f'{name}_{v}', subs, both(f'{name}_{v}', [v], depth=depth, violation=True)))
    return out


def copy_names(copies):
    return [c[0] for cs in copies.values() for c in cs]


SMALL_NOTE = """Quint checks this file with `quint verify --max-steps=3` (Apalache, symbolic). Veil's
explicit-state model checker enumerates every value of a `nondet`, so it checks copies of the
modules with smaller domains (`..._small`, described above each copy) to the same depth, and runs
the simulator on them. """

CONFIG['language-features/instances.qnt'] = {
    'notes': """Instances of parametric modules, two of them with state (`V1`, `V2`). `inv` is
checked to depth 3, as `quint verify --max-steps=3` does.""",
    'tails': {'instances': both('instances', ['inv'], depth=3)},
}

_small_configs = {
    'solidity/ERC20/erc20.qnt': ({
        'erc20Tests': small('erc20Tests', [('pure val ADDR = Set("0", "alice", "bob", "eve")',
                                            'pure val ADDR = Set("0", "alice", "bob")'),
                                           ('pure val AMOUNTS = (0).to(100)', 'pure val AMOUNTS = (0).to(2)')],
                            ['totalSupplyInv', 'zeroAddressInv', 'noOverflowsInv'])
                      + [('erc20Tests_tiny', [('pure val ADDR = Set("0", "alice", "bob", "eve")',
                                               'pure val ADDR = Set("0", "alice", "bob")'),
                                              ('pure val AMOUNTS = (0).to(100)', 'pure val AMOUNTS = (0).to(1)')], '')],
    }, """`totalSupplyInv`, `zeroAddressInv` and `noOverflowsInv` hold. `transferTest` starts in
any state of `initArbitrary` (every map of balances and allowances), which Veil enumerates and
`quint test` samples; it is run on `erc20Tests_tiny` (three addresses, amounts `0` and `1`)."""),
    'solidity/SimplePonzi/simplePonzi.qnt': ({
        'simplePonziTest': small('simplePonziTest', [('addr.mapBy(a => 10000)', 'addr.mapBy(a => 10)')],
                                 ['noNegativeInv'], ['progressInv']),
    }, """`noNegativeInv` holds; `progressInv` is violated, as the Quint file says."""),
    'solidity/GradualPonzi/gradualPonzi.qnt': ({
        'gradualPonzi': [('gradualPonzi_small', [('pure val MINIMUM_INVESTMENT = 10^15',
                                                  'pure val MINIMUM_INVESTMENT = 1')], '')],
        'gradualPonziTest': small('gradualPonziTest', [
            ('import gradualPonzi(ADDR = addr).*', 'import gradualPonzi_small(ADDR = addr).*'),
            ('100 * MINIMUM_INVESTMENT', '3 * MINIMUM_INVESTMENT'),
            ('(-10).to(evmState.balances.get(investor) + 10)', '(-1).to(evmState.balances.get(investor) + 1)')],
            ['noNegativeInv'], ['noBrokeInv', 'progressInv', 'noLeftoversInv']),
    }, """`noNegativeInv` holds; `noBrokeInv`, `progressInv` and `noLeftoversInv` are violated, as
the Quint file says (with `MINIMUM_INVESTMENT = 1`, which the file suggests for the simulator)."""),
    'cryptography/utxo/utxo.qnt': ({
        'utxo': small('utxo', [('amount: 100, lockingCode: "Alice"', 'amount: 3, lockingCode: "Alice"'),
                               ('val INITIAL_SUPPLY = 100', 'val INITIAL_SUPPLY = 3'),
                               ('(1).to(100).oneOf()', '(1).to(3).oneOf()')],
                      ['constant_supply'], ['constant_supply_bad']),
    }, """`constant_supply` holds; `constant_supply_bad` is violated, as the Quint file says."""),
    'cosmos/bank/bankTest.qnt': ({
        'bankTest': small('bankTest', [('mapBy(d => 10_000)', 'mapBy(d => 3)'),
                                       ('(-10).to(supply.get(denom))', '(-1).to(supply.get(denom))')],
                          [], ['totalSupplyInv']),
    }, """`totalSupplyInv` is violated in three steps, which Quint's dashboard does not check
(it runs `quint verify` without an invariant). `step` sends amounts from `-10` on, and
`SendCoins` accepts a negative amount: sending `-1` burger to an account gives it a balance of
`-1` burger, and when that account then sends another denomination, `SendCoins` keeps only the
denominations with a positive remainder (`positiveDenoms`), so the `-1` disappears and the sum of
the balances no longer equals the supply. The same execution exists with the file's amounts:
from `init`, `send("king", "donkeykong", Map("banana" -> 1))`, then
`send("king", "donkeykong", Map("burger" -> -1))`, then
`send("donkeykong", "peaches", Map("banana" -> 1))`; Quint confirms it (`quint test` of this run
with `assert(not(totalSupplyInv))` passes)."""),
    'cosmos/ics20/bank.qnt': ({
        'bankTests': small('bankTests', [('nondet amount = Int.oneOf()', 'nondet amount = (-1).to(2).oneOf()')],
                           ['BalanceNonNegative', 'NonExistantAccountsOrCoinsAreZero']),
    }, """`BalanceNonNegative` and `NonExistantAccountsOrCoinsAreZero` hold (the file's own
`quint verify --max-steps=3` command)."""),
    'cosmwasm/zero-to-hero/vote.qnt': ({
        'state': small('state', [('Set("alice", "bob", "charlie", "eve")', 'Set("alice", "bob")'),
                                 ('Set("p1", "p2", "p3", "p4")', 'Set("p1", "p2")'),
                                 ('Set("q1", "q2", "q3", "q4")', 'Set("q1")'),
                                 ('Set("o1", "o2", "o3")', 'Set("o1", "o2")')],
                       ['alwaysAdmin'], ['invBallotsMatchPolls', 'invAllBallotsPositive'], depth=4),
    }, """`alwaysAdmin` holds; `invBallotsMatchPolls` and `invAllBallotsPositive` are violated, as
the Quint file says (to depth 4: the violation of `invAllBallotsPositive` needs four steps)."""),
}

for _p, (_copies, _what) in _small_configs.items():
    _c = CONFIG.setdefault(_p, {})
    _c.setdefault('copies', {}).update(_copies)
    _c['notes'] = (_c.get('notes', '') + '\n\n' if 'notes' in _c else '') + SMALL_NOTE + _what
    # the copies' tests would check values of the large instances
    _nt = _c.get('no_tests', [])
    if _nt is not True:
        _c['no_tests'] = list(_nt) + copy_names(_copies)

# `transferTest` enumerates every initial state of `initArbitrary`: test the tiny copy only
_c = CONFIG['solidity/ERC20/erc20.qnt']
_c['no_tests'] = [m for m in _c['no_tests'] if m != 'erc20Tests_tiny'] + ['erc20Tests']

# Tests that Veil's model checker does not finish (it enumerates every execution of a run, where
# quint test samples one): they are not run.
for _p in []:
    CONFIG.setdefault(_p, {})['no_tests'] = True
