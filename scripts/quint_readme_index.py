#!/usr/bin/env python3
"""Print the index table of Examples/Quint/README.md.

For every Quint example: its Lean file, the Veil checks that run on it and their results (parsed
from a build log of Examples/Quint), and Quint's reference result (Examples/Quint/compliance.json,
written by quint_compliance.py, and Quint's own dashboard).

Usage:
    scripts/quint_readme_index.py QUINT_CHECKOUT BUILD_LOG
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from quint_examples import lean_rel  # noqa: E402

ROOT = os.path.dirname(HERE)
RESULT = re.compile(r'Examples/Quint/(\S+\.lean):(\d+):\d+: (?:error: )?(✅|❌)\s*(.*)')


def results_by_file(log: str):
    out = {}
    for line in open(log, errors='replace'):
        m = RESULT.search(line)
        if not m:
            continue
        f, ln, mark, rest = m.group(1), int(m.group(2)), m.group(3), m.group(4).strip()
        out.setdefault(f, {})[ln] = (mark, rest)
    return out


def describe(src_line: str, mark: str, rest: str) -> str:
    """Describe one result: which command produced it and what it says."""
    depth = re.search(r'maxDepth := (\d+)', src_line)
    if '#simulate' in src_line or '#quint_run' in src_line:
        kind = 'simulation'
    elif '#temporal_check' in src_line:
        kind = 'temporal'
    elif 'quint_bmc' in src_line:
        kind = 'BMC'
    elif '#model_check' in src_line or '#quint_verify' in src_line:
        kind = f'model checking, depth ≤ {depth.group(1)}' if depth else 'model checking'
    else:
        kind = 'check'
    expected = 'violationIsError false' in src_line
    m = re.search(r'explored (\d+) states', rest)
    if m:
        what = f'{int(m.group(1)):,} states'
    elif 'traces' in rest:
        what = re.sub(r'No violation in ', '', rest)
    elif 'liveness' in rest.lower():
        what = re.sub(r'No liveness violation ', '', rest)
    elif 'violates:' in rest:
        what = 'violates ' + re.search(r'violates: ([^)]*)', rest).group(1) + (' (expected)' if expected else '')
    else:
        what = rest[:60]
    return f'{mark} {kind}: {what}'


def dashboard(quint):
    """Quint's own results from examples/README.md: (tests, verify) per example."""
    out = {}
    path = os.path.join(quint, 'examples', 'README.md')
    sym = {':white_check_mark:': '✅', ':x:': '❌'}
    for line in open(path):
        m = re.match(r'\| \[([^\]]+)\]\([^)]*\) \| ([^|]*) \| ([^|]*) \| ([^|]*) \| ([^|]*) \|', line)
        if not m:
            continue
        def norm(x):
            x = x.strip()
            for k, v in sym.items():
                x = x.replace(k, v)
            x = re.sub(r'<sup>.*?</sup>', '', x)
            x = re.sub(r'\[\^\w+\]', '', x)
            return x.strip()
        out[m.group(1)] = (norm(m.group(4)), norm(m.group(5)))
    return out


def main():
    quint, log = sys.argv[1], sys.argv[2]
    dash = dashboard(quint)
    res = results_by_file(log)
    comp_path = os.path.join(ROOT, 'Examples', 'Quint', 'compliance.json')
    comp = json.load(open(comp_path)) if os.path.exists(comp_path) else {}
    by_file = {}
    for name, r in comp.items():
        by_file.setdefault(r['quint_file'], []).append((name, r))
    rows = []
    ex = os.path.join(quint, 'examples')
    for root, _, files in os.walk(ex):
        for f in sorted(files):
            if not f.endswith('.qnt'):
                continue
            rel = os.path.relpath(os.path.join(root, f), ex)
            lr = lean_rel(rel)
            lines = open(os.path.join(ROOT, 'Examples', 'Quint', lr)).read().split('\n')
            rs = res.get(lr, {})
            checks = []
            for ln in sorted(rs):
                prev = '\n'.join(lines[max(0, ln - 2):ln])
                checks.append(describe(prev, *rs[ln]))
            ref = []
            for name, r in by_file.get(rel, []):
                t = r['tlc']
                if t['distinct'] is not None:
                    ref.append(f"TLC `{name}`: {t['distinct']:,} states, {t['verdict']}")
                else:
                    ref.append(f"TLC `{name}`: {t['verdict']}")
            if rel in dash:
                t, v = dash[rel]
                ref.append(f'Quint dashboard: test {t}, Apalache verify {v}')
            rows.append((rel, lr, checks, ref))
    rows.sort()
    print('| Quint example | Lean file | Veil checks and results | Quint reference |')
    print('| --- | --- | --- | --- |')
    for rel, lr, checks, ref in rows:
        c = '<br>'.join(checks) if checks else 'elaborates'
        r = '<br>'.join(ref) if ref else ''
        print(f'| `{rel}` | [{lr}]({lr}) | {c} | {r} |')


if __name__ == '__main__':
    main()
