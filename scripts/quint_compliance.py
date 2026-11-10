#!/usr/bin/env python3
"""Compare Veil's results on Examples/Quint with the quint tool's.

For every finite instance listed in CHECKS, run `quint verify --backend tlc` (TLC through Quint)
and elaborate the Veil file (`lake env lean`), and compare

- the verdict (all invariants hold / some invariant is violated), and
- the number of distinct reachable states (TLC's `distinct states found`, Veil's
  `explored N states`), for complete runs without a violation.

Requires the quint CLI (`npx quint`, from npm package @informalsystems/quint) and Java 21 for
TLC (set JAVA_HOME). Results go to Examples/Quint/compliance.json; the Markdown table is printed.

Usage:
    scripts/quint_compliance.py QUINT_CHECKOUT [--quint-dir DIR_WITH_NODE_MODULES] [--only NAME]
        [--veil-log BUILD_LOG]

With --veil-log, Veil's results are read from a build log of Examples/Quint
(scripts/quint_build_all.sh) instead of elaborating each file again.
"""
import json
import os
import re
import signal
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, 'Examples', 'Quint', 'compliance.json')

# (name, quint file, --main, --invariant, extra quint args, Lean file under Examples/Quint)
CHECKS = [
    ('two_phase_commit_3', 'classic/distributed/TwoPhaseCommit/two_phase_commit.qnt',
     'two_phase_commit_3', 'consistencyInv', '', 'Classic/Distributed/TwoPhaseCommit/TwoPhaseCommit.lean'),
    ('teaching', 'classic/distributed/TeachingConcurrency/teaching.qnt',
     '', 'correctness', '', 'Classic/Distributed/TeachingConcurrency/Teaching.lean'),
    ('mutex', 'classic/distributed/TeachingConcurrency/mutex.qnt',
     '', 'correctness,inv', '', 'Classic/Distributed/TeachingConcurrency/Mutex.lean'),
    ('ewd840_3', 'classic/distributed/ewd840/ewd840.qnt',
     'ewd840_3', 'TypeOK,Inv,TerminationDetection', '', 'Classic/Distributed/Ewd840/Ewd840.lean'),
    ('ewd426', 'classic/distributed/ewd426/ewd426.qnt', '', '', '', 'Classic/Distributed/Ewd426/Ewd426.lean'),
    ('ewd426_3', 'classic/distributed/ewd426/ewd426_3.qnt', '', '', '', 'Classic/Distributed/Ewd426/Ewd4263.lean'),
    ('ewd426_4', 'classic/distributed/ewd426/ewd426_4.qnt', '', '', '', 'Classic/Distributed/Ewd426/Ewd4264.lean'),
    ('DiningPhilosophers5', 'classic/distributed/DiningPhilosophers/DiningPhilosophers5.qnt',
     '', 'TypeOk,Safety', '', 'Classic/Distributed/DiningPhilosophers/DiningPhilosophers5.lean'),
    ('reliablebc', 'classic/distributed/ReliableBroadcast/reliablebc.qnt',
     '', '', '', 'Classic/Distributed/ReliableBroadcast/Reliablebc.lean'),
    ('two_layered_cache', 'classic/distributed/TwoLayeredCache/two_layered_cache.qnt',
     '', '', '', 'Classic/Distributed/TwoLayeredCache/TwoLayeredCache.lean'),
    ('BinSearch10', 'classic/sequential/BinSearch/BinSearch.qnt',
     'BinSearch10', '', '', 'Classic/Sequential/BinSearch/BinSearch.lean'),
    ('river', 'puzzles/river/river.qnt', '', 'safety', '', 'Puzzles/River/River.lean'),
    ('prisoners3', 'puzzles/prisoners/prisoners.qnt',
     'prisoners3', 'safetyInv,countInv', '', 'Puzzles/Prisoners/Prisoners.lean'),
    ('tictactoe', 'games/tictactoe/tictactoe.qnt', '', 'inv', '', 'Games/Tictactoe/Tictactoe.lean'),
    ('secret_santa', 'games/secret-santa/secret_santa.qnt',
     'quint_team_secret_santa', 'inv', '', 'Games/SecretSanta/SecretSanta.lean'),
    ('rock_paper_scissors', 'games/rock_paper_scissors/play_rock_paper_scissors.qnt',
     '', 'winInv', '', 'Games/RockPaperScissors/PlayRockPaperScissors.lean'),
    ('hello', 'tutorials/hello.qnt', '', '', '', 'Tutorials/Hello.lean'),
    ('booleans', 'language-features/booleans.qnt', '', '', '', 'LanguageFeatures/Booleans.lean'),
    ('weakFairness', 'language-features/weakFairness.qnt', '', '', '', 'LanguageFeatures/WeakFairness.lean'),
    ('strongFairness', 'language-features/strongFairness.qnt', '', '', '', 'LanguageFeatures/StrongFairness.lean'),
]

TLC_DISTINCT = re.compile(r'([\d,]+) distinct states found')
TLC_MS = re.compile(r'\((\d+)ms\)')
VEIL_OK = re.compile(r'No violation \(explored (\d+) states\)')
VEIL_BAD = re.compile(r'Violation: (\w+)')


def run_group(args, cwd, env, timeout):
    """Run a command in its own process group; kill the group on timeout (TLC runs in a JVM
    that a plain timeout would leave behind)."""
    t0 = time.time()
    p = subprocess.Popen(args, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         text=True, start_new_session=True)
    try:
        out, _ = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        out, _ = p.communicate()
        return out + '\nTIMEOUT', time.time() - t0
    return out, time.time() - t0


def run_tlc(quint, qdir, f, main, inv, extra, timeout=600):
    args = ['npx', 'quint', 'verify', '--backend', 'tlc']
    if main:
        args.append('--main=' + main)
    if inv:
        args.append('--invariant=' + inv)
    args += extra.split() + [os.path.join(quint, 'examples', f)]
    out, wall = run_group(args, qdir, os.environ.copy(), timeout)
    # the last count is the final one (TLC also prints progress lines)
    found = TLC_DISTINCT.findall(out)
    ms = TLC_MS.findall(out)
    if 'TIMEOUT' in out:
        verdict = 'timeout'
    elif '[ok] No violation' in out:
        verdict = 'holds'
    elif re.search(r'violat', out, re.I) and 'Invariant' in out:
        verdict = 'violated'
    else:
        verdict = 'error'
    distinct = int(found[-1].replace(',', '')) if found else None
    return {'distinct': distinct if verdict == 'holds' else None, 'verdict': verdict,
            'time_ms': int(ms[-1]) if ms else None, 'wall_s': round(wall, 2)}


def veil_from_log(lean_rel, log):
    """Veil's result for a file, from a build log of Examples/Quint (the first model check)."""
    pat = re.compile(re.escape('Examples/Quint/' + lean_rel) + r':\d+:\d+: (?:error: )?(✅|❌)(.*)')
    for line in open(log, errors='replace'):
        m = pat.search(line)
        if not m:
            continue
        ok = VEIL_OK.search(line)
        if ok:
            return {'distinct': int(ok.group(1)), 'verdict': 'holds'}
        if VEIL_BAD.search(line):
            return {'distinct': None, 'verdict': 'violated'}
    return {'distinct': None, 'verdict': 'error'}


def run_veil(lean_rel, timeout=3600):
    path = os.path.join('Examples', 'Quint', lean_rel)
    out, wall = run_group(['lake', 'env', 'lean', path], ROOT, os.environ.copy(), timeout)
    m = VEIL_OK.search(out)
    b = VEIL_BAD.search(out)
    if m:
        return {'distinct': int(m.group(1)), 'verdict': 'holds', 'wall_s': round(wall, 2)}
    if b:
        return {'distinct': None, 'verdict': 'violated', 'wall_s': round(wall, 2)}
    return {'distinct': None, 'verdict': 'error', 'wall_s': round(wall, 2), 'tail': out[-500:]}


def main():
    quint = sys.argv[1]
    qdir = sys.argv[sys.argv.index('--quint-dir') + 1] if '--quint-dir' in sys.argv else quint
    only = sys.argv[sys.argv.index('--only') + 1] if '--only' in sys.argv else None
    log = sys.argv[sys.argv.index('--veil-log') + 1] if '--veil-log' in sys.argv else None
    results = json.load(open(OUT)) if os.path.exists(OUT) else {}
    for name, f, main_, inv, extra, lean in CHECKS:
        if only and only != name:
            continue
        tlc = run_tlc(quint, qdir, f, main_, inv, extra)
        veil = veil_from_log(lean, log) if log else run_veil(lean)
        agree = tlc['verdict'] == veil['verdict'] and (tlc['distinct'] == veil['distinct'])
        results[name] = {'quint_file': f, 'main': main_, 'invariants': inv, 'tlc': tlc, 'veil': veil,
                         'agree': agree}
        print(name, tlc, veil, 'AGREE' if agree else 'DIFFER', flush=True)
        json.dump(results, open(OUT, 'w'), indent=1)
    print()
    print('| Instance | Invariants | TLC (via Quint) | Veil `#model_check` | Agree |')
    print('| --- | --- | --- | --- | --- |')
    for name, r in results.items():
        def fmt(x):
            return f"{x['verdict']}, {x['distinct']} states" if x['distinct'] is not None else x['verdict']
        print(f"| {name} | {r['invariants'] or '–'} | {fmt(r['tlc'])} | {fmt(r['veil'])} | "
              f"{'yes' if r['agree'] else 'no'} |")


if __name__ == '__main__':
    main()
