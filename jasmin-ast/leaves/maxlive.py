#!/usr/bin/env python3
"""Register pressure of straight-line Jasmin functions, from a jast294c/jasminc
`-pXXX` printout (e.g. -pslhlowering, the last pass printed before register
allocation).  Backward liveness over the body (no control flow expected), counting
only non-bool variables (u64 registers): pressure at an instruction =
|live-out U defs|.  Prints, per function, the number of instructions, the
maximal pressure and where it is reached.  Diagnostic only.

usage: maxlive.py printout.txt
"""
import re, sys

VAR = re.compile(r'(?<![\w$])([A-Za-z_$][\w$]*\.\d+)')

def funcs(text):
    # split into functions: header "fn NAME (" ... "{" body "}"
    for m in re.finditer(r'fn\s+(\w+)\s*\((.*?)\)\s*->[^{]*\{(.*?)\n\}', text, re.S):
        yield m.group(1), m.group(2), m.group(3)

def analyse(name, params, body):
    bools = set(re.findall(r'reg bool ([^;\s]+);', body))
    lines = [l for l in body.split('\n') if not re.match(r'\s*reg ', l)]
    stmts = [s.strip() for s in ' '.join(lines).split(';') if s.strip()]
    if any(re.match(r'(if|while|for)\b', s) for s in stmts):
        print(f'{name}: has control flow, skipped'); return
    insns = []
    for s in stmts:
        s = re.sub(r'/\*.*?\*/', '', s)
        m = re.search(r'\s=\s', s)
        if not m:
            continue
        lhs, rhs = s[:m.start()], s[m.end():]
        mem = ''.join(re.findall(r'\[[^\]]*\]', lhs))
        lhs_nomem = re.sub(r'\[[^\]]*\]', '', lhs)
        isbool = lambda v: v in bools or v.startswith('__')
        defs = {v for v in VAR.findall(lhs_nomem) if not isbool(v)}
        uses = {v for v in VAR.findall(rhs) + VAR.findall(mem) if not isbool(v)}
        insns.append((s, defs, uses))
    live = set(); best = (0, -1); prof = []
    for k in range(len(insns) - 1, -1, -1):
        s, d, u = insns[k]
        p = len(live | d)
        if p >= best[0]: best = (p, k)
        live = (live - d) | u
        prof.append(p)
    p_in = len(live)
    print(f'{name}: {len(insns)} instructions, max register pressure {max(best[0], p_in)} '
          f'u64 values (x86-64 has 15 allocatable GPRs; params live at entry: {p_in})')
    s, d, u = insns[best[1]]
    print(f'   reached at instruction #{best[1]}: {s[:110]}')

text = open(sys.argv[1]).read()
for f in funcs(text):
    analyse(*f)
