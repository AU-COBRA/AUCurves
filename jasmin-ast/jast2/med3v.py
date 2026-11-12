#!/usr/bin/env python3
"""med3.py for bench_variants: run the binary three times pinned to core 3 (taskset -c 3),
median per (op, label) of the three per-run medians.  Also prints each run's value.
usage: med3v.py ./bench_variants [runs=3]"""
import subprocess, sys, statistics
exe = sys.argv[1]; nrun = int(sys.argv[2]) if len(sys.argv) > 2 else 3
vals = {}; order = []
for _ in range(nrun):
    out = subprocess.run(['taskset', '-c', '3', exe], capture_output=True, text=True, check=True).stdout
    for l in out.splitlines():
        op, lab, c = l.split('\t')
        if (op, lab) not in vals: vals[(op, lab)] = []; order.append((op, lab))
        vals[(op, lab)].append(float(c))
print('%-7s %-28s %8s   %s' % ('op', 'variant', 'median', 'runs'))
for k in order:
    print('%-7s %-28s %8.1f   %s' % (k[0], k[1], statistics.median(vals[k]), ' '.join('%.1f' % v for v in vals[k])))
