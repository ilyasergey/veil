#!/usr/bin/env python3
"""Generate `Examples/Quint` from a checkout of https://github.com/quint-co/quint.

Every `.qnt` file under `examples/` becomes a Lean file that contains the Quint source, rewritten
mechanically by `quint2veil.py` (comments, methods on numerals), followed by the Veil checks
configured in `quint_examples_config.py` for its modules.

Usage:
    scripts/quint_examples.py QUINT_CHECKOUT [--only PATH_SUBSTRING]
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import quint2veil  # noqa: E402
from quint_examples_config import CONFIG, DEFAULT_NOTES  # noqa: E402

ROOT = os.path.dirname(HERE)
OUT = os.path.join(ROOT, 'Examples', 'Quint')


def camel(s: str) -> str:
    """`two_phase_commit` -> `TwoPhaseCommit`, `icse23-fig7` -> `Icse23Fig7`."""
    parts = re.split(r'[_\-.]', s)
    return ''.join(p[:1].upper() + p[1:] for p in parts if p)


def lean_rel(qnt_rel: str) -> str:
    """Path of the Lean file (relative to Examples/Quint) for a Quint file."""
    parts = qnt_rel[:-len('.qnt')].split('/')
    return '/'.join(camel(p) for p in parts) + '.lean'


def lean_module(qnt_rel: str) -> str:
    return 'Examples.Quint.' + lean_rel(qnt_rel)[:-len('.lean')].replace('/', '.')


def deps(qnt_rel: str, src: str):
    """Quint files imported with `from "..."`."""
    out = []
    for m in re.finditer(r'from\s+"([^"]+)"', src):
        d = os.path.normpath(os.path.join(os.path.dirname(qnt_rel), m.group(1)))
        if not d.endswith('.qnt'):
            d += '.qnt'
        if d not in out:
            out.append(d)
    return out


def split_modules(text: str):
    """Split converted text into (prefix, [(name, chunk)]) at top-level `module` lines."""
    lines = text.split('\n')
    starts = [i for i, l in enumerate(lines) if re.match(r'module\s+([A-Za-z0-9_:]+)\s*\{', l)]
    if not starts:
        return text, []
    prefix = '\n'.join(lines[:starts[0]])
    chunks = []
    for k, st in enumerate(starts):
        en = starts[k + 1] if k + 1 < len(starts) else len(lines)
        name = re.match(r'module\s+([A-Za-z0-9_:]+)', lines[st]).group(1)
        chunks.append((name, '\n'.join(lines[st:en])))
    return prefix, chunks


def module_imports(chunk: str):
    return set(re.findall(r'^\s*import\s+([A-Za-z0-9_]+)', chunk, re.M))


def order_modules(chunks):
    """Put modules that are imported by a module of the same file before it (Quint allows any
    order; Lean elaborates top to bottom)."""
    names = [n for n, _ in chunks]
    by = dict(chunks)
    out, seen = [], set()

    def visit(n, stack=()):
        if n in seen or n in stack:
            return
        for d in module_imports(by[n]):
            if d in by:
                visit(d, stack + (n,))
        seen.add(n)
        out.append(n)
    for n in names:
        visit(n)
    return [(n, by[n]) for n in out], out != names


def insert_tail(chunk: str, tail: str) -> str:
    """Insert `tail` after the closing brace of the module in `chunk`."""
    # the module ends at the last `}` at column 0
    idx = None
    for m in re.finditer(r'^\}', chunk, re.M):
        idx = m.end()
    if idx is None:
        return chunk + '\n' + tail
    return chunk[:idx] + '\n\n' + tail.rstrip() + '\n' + chunk[idx:]


def generate(quint: str, only=None):
    examples = os.path.join(quint, 'examples')
    commit = subprocess.run(['git', '-C', quint, 'rev-parse', 'HEAD'],
                            capture_output=True, text=True).stdout.strip()
    generated = []
    for root, _, files in os.walk(examples):
        for f in sorted(files):
            if not f.endswith('.qnt'):
                continue
            rel = os.path.relpath(os.path.join(root, f), examples)
            if only and only not in rel:
                continue
            cfg = CONFIG.get(rel, {})
            src = open(os.path.join(root, f)).read()
            text = quint2veil.convert(src)
            prefix, chunks = split_modules(text)
            chunks, reordered = order_modules(chunks)
            tails = cfg.get('tails', {})
            pres = cfg.get('pre', {})
            body = prefix
            for name, chunk in chunks:
                if name in tails:
                    chunk = insert_tail(chunk, tails[name])
                if name in pres:
                    chunk = pres[name].rstrip() + '\n' + chunk
                body += ('\n' if body and not body.endswith('\n') else '') + chunk
            imports = ['public import Veil.Quint']
            for d in deps(rel, src):
                imports.append('public import ' + lean_module(d))
            notes = cfg.get('notes', DEFAULT_NOTES)
            if reordered:
                notes += ('\n\nThe modules appear in dependency order (Quint accepts any order; '
                          'Lean elaborates from top to bottom).')
            header = (
                'module\n\n' + '\n'.join(imports) + '\n\n'
                + '/-!\n'
                + f'# Quint example `{rel}`\n\n'
                + f'Source: https://github.com/quint-co/quint/blob/{commit}/examples/{rel}\n'
                + '(Apache-2.0). The Quint text below is the original, with the comment markers\n'
                + '`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;\n'
                + '`scripts/quint2veil.py` does this rewrite.\n\n'
                + notes.strip() + '\n-/\n\n')
            footer = cfg.get('footer', '')
            out_path = os.path.join(OUT, lean_rel(rel))
            os.makedirs(os.path.dirname(out_path), exist_ok=True)
            with open(out_path, 'w') as fh:
                fh.write(header + body.rstrip() + '\n' + (('\n' + footer.rstrip() + '\n') if footer else ''))
            generated.append((rel, out_path))
    return generated


if __name__ == '__main__':
    only = None
    if '--only' in sys.argv:
        only = sys.argv[sys.argv.index('--only') + 1]
    for rel, path in generate(sys.argv[1], only):
        print(rel, '->', os.path.relpath(path, ROOT))
