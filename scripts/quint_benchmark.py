#!/usr/bin/env python3
"""Benchmark Veil's explicit-state model checker against TLC (through Quint) on the finite Quint
examples, and plot the results next to Examples/Quint/README.md.

Steps:
1. TLC: `quint verify --backend tlc` on each instance, `--repeat` times; the time is the one quint
   reports for the check (`[ok] No violation found (…ms)`), and the wall time of the command
   (which includes starting the JVM and translating the spec to TLA+ with Apalache).
2. Veil: `scripts/bench-model-check.py` on copies of the Lean files that use `#model_check`
   (`--veil-specs`, e.g. made by `--make-copies DIR`): it builds each model checker binary, then
   times the search at the given thread counts.
3. Write Examples/Quint/benchmark.json and Examples/Quint/benchmark.png.

Usage:
    scripts/quint_benchmark.py QUINT_CHECKOUT --quint-dir DIR --veil-results BENCH_OUT/results.json
        [--tlc-cache tlc.json] [--repeat N] [--python-with-matplotlib PATH]
"""
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from quint_compliance import CHECKS, run_tlc  # noqa: E402

ROOT = os.path.dirname(HERE)
OUT_JSON = os.path.join(ROOT, 'Examples', 'Quint', 'benchmark.json')
OUT_PNG = os.path.join(ROOT, 'Examples', 'Quint', 'benchmark.png')

# benchmark copy (Scratch/QuintBench/<name>.lean) -> compliance instance
SPECS = {
    'TwoPhaseCommit': 'two_phase_commit_3', 'Teaching': 'teaching', 'Mutex': 'mutex',
    'Ewd840': 'ewd840_3', 'Ewd426': 'ewd426', 'Ewd4263': 'ewd426_3', 'Ewd4264': 'ewd426_4',
    'DiningPhilosophers5': 'DiningPhilosophers5', 'Reliablebc': 'reliablebc',
    'TwoLayeredCache': 'two_layered_cache', 'River': 'river', 'Prisoners': 'prisoners3',
    'Tictactoe': 'tictactoe',
}


def tlc_times(quint, qdir, repeat):
    by_name = {c[0]: c for c in CHECKS}
    out = {}
    for spec, inst in SPECS.items():
        name, f, main, inv, extra, _ = by_name[inst]
        runs = [run_tlc(quint, qdir, f, main, inv, extra) for _ in range(repeat)]
        ok = [r for r in runs if r['time_ms'] is not None]
        out[spec] = {
            'instance': inst, 'distinct': runs[0]['distinct'],
            'time_ms': min(r['time_ms'] for r in ok) if ok else None,
            'wall_s': min(r['wall_s'] for r in runs),
        }
        print('TLC', spec, out[spec], flush=True)
    return out


def veil_times(results_path):
    """Search times (ms) per spec and thread count from bench-model-check.py's results.json."""
    data = json.load(open(results_path))
    out = {}
    specs = data.get('specs', data)
    for name, entry in (specs.items() if isinstance(specs, dict) else []):
        runs = entry.get('runs', []) if isinstance(entry, dict) else []
        for r in runs:
            t = r.get('threads')
            ms = r.get('search_ms') or r.get('elapsed_ms') or r.get('checker_elapsed_ms')
            if ms is None and isinstance(r.get('progress'), dict):
                ms = r['progress'].get('checker_elapsed_ms')
            if t is None or ms is None:
                continue
            cur = out.setdefault(name, {}).get(t)
            out[name][t] = ms if cur is None else min(cur, ms)
            out[name]['states'] = r.get('explored_states') or (r.get('result') or {}).get('explored_states')
    return out


def plot(bench, python):
    script = f'''
import json, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
b = json.load(open({OUT_JSON!r}))
names = [n for n in b if b[n]["tlc_ms"] and b[n]["veil"]]
names.sort(key=lambda n: b[n]["states"] or 0)
threads = sorted({{int(t) for n in names for t in b[n]["veil"]}})
fig, ax = plt.subplots(figsize=(10, 4.8))
w = 0.8 / (1 + len(threads))
xs = range(len(names))
ax.bar([x - 0.4 + w / 2 for x in xs], [b[n]["tlc_ms"] for n in names], w, label="TLC (quint verify --backend tlc)", color="#888888")
cols = ["#1f77b4", "#ff7f0e", "#2ca02c"]
for i, t in enumerate(threads):
    ax.bar([x - 0.4 + w * (i + 1.5) for x in xs], [b[n]["veil"].get(str(t)) or 0 for n in names], w,
           label=f"Veil #model_check, {{t}} thread{{'s' if t > 1 else ''}}", color=cols[i % 3])
ax.set_yscale("log")
ax.set_ylabel("time (ms, log scale)")
ax.set_xticks(list(xs))
ax.set_xticklabels([f"{{n}}\\n{{b[n]['states']:,}} states" for n in names], rotation=45, ha="right", fontsize=8)
ax.legend(fontsize=8)
ax.set_title("Explicit-state model checking of Quint examples: TLC vs. Veil (search time)")
fig.tight_layout()
fig.savefig({OUT_PNG!r}, dpi=150)
'''
    subprocess.run([python, '-c', script], check=True)


def main():
    quint = sys.argv[1]
    arg = lambda k, d=None: sys.argv[sys.argv.index(k) + 1] if k in sys.argv else d
    qdir = arg('--quint-dir', quint)
    repeat = int(arg('--repeat', '1'))
    cache = arg('--tlc-cache')
    if cache and os.path.exists(cache):
        tlc = json.load(open(cache))
    else:
        tlc = tlc_times(quint, qdir, repeat)
        if cache:
            json.dump(tlc, open(cache, 'w'), indent=1)
    veil = veil_times(arg('--veil-results'))
    bench = {}
    for spec in SPECS:
        v = veil.get(spec, {})
        bench[spec] = {
            'instance': tlc[spec]['instance'], 'states': tlc[spec]['distinct'] or v.get('states'),
            'tlc_ms': tlc[spec]['time_ms'], 'tlc_wall_s': tlc[spec]['wall_s'],
            'veil': {str(t): ms for t, ms in v.items() if t != 'states'},
        }
    json.dump(bench, open(OUT_JSON, 'w'), indent=1)
    print(json.dumps(bench, indent=1))
    plot(bench, arg('--python-with-matplotlib', sys.executable))


if __name__ == '__main__':
    main()
