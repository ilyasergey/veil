#!/usr/bin/env python3
"""Mechanical rewrite of a Quint source (.qnt) into text that the Veil Quint frontend parses.

Lean's tokenizer differs from Quint's in two places; this script rewrites exactly those:

1. comments: `//` -> `--`, `/*` -> `/-`, `*/` -> `-/` (same length, so line/column positions
   agree with the original file);
2. a method called on a numeral: `0.to(10)` -> `(0).to(10)`;

Usage:
    quint2veil.py FILE.qnt              # print the converted module text
    quint2veil.py FILE.qnt --lean NAME  # print a complete Lean file (header + module text)
"""
import re
import sys

# Lean keywords that are plain identifiers in Quint.
LEAN_KEYWORDS = {
    "at", "by", "do", "end", "from", "fun", "have", "in", "let", "local", "mut", "namespace",
    "open", "section", "show", "then", "where", "with", "deriving", "instance", "structure",
    "class", "theorem", "example", "abbrev", "variable", "universe", "macro", "syntax",
    "calc", "suffices", "obtain", "for", "unless", "return", "break", "continue", "try",
    "catch", "finally", "notation", "infix", "prefix", "postfix", "attribute", "private",
    "protected", "partial", "unsafe", "noncomputable", "opaque", "axiom", "inductive",
    "mutual", "export", "Type", "Sort", "Prop", "forall", "exists", "fun",
}
# Quint keywords that must stay as they are.
QUINT_KEYWORDS = {"module", "import", "export", "from", "as", "match", "if", "else", "def"}


def convert(src: str) -> str:
    out = []
    i, n = 0, len(src)
    in_str = False
    while i < n:
        c = src[i]
        if in_str:
            out.append(c)
            if c == '\\' and i + 1 < n:
                out.append(src[i + 1]); i += 2; continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True; out.append(c); i += 1; continue
        if src.startswith('//', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            out.append('--' + src[i + 2:j]); i = j; continue
        if src.startswith('/*', i):
            j = src.find('*/', i + 2)
            j = n if j < 0 else j
            body = src[i + 2:j]
            # a block comment starting with '-' would become a Lean doc comment `/--`
            if body.startswith('-'):
                body = ' ' + body[1:]
            out.append('/-' + body.replace('/-', '/ -').replace('-/', '- /') + '-/'); i = j + 2; continue
        out.append(c); i += 1
    text = ''.join(out)
    # 2. methods on numerals: 0.to(10) -> (0).to(10); skip decimals like 1.5 (not Quint anyway)
    text = re.sub(r'(?<![\w.])(\d[\d_]*|0x[0-9a-fA-F_]+)\.([A-Za-z_])', r'(\1).\2', text)
    return text


def main():
    path = sys.argv[1]
    with open(path) as f:
        text = convert(f.read())
    if '--lean' in sys.argv:
        print("module\n\npublic import Veil.Quint\n")
    print(text)


if __name__ == '__main__':
    main()
