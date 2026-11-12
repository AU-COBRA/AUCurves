import subprocess, sys, re, statistics
exe = sys.argv[1]; runs = [subprocess.run(['taskset','-c','3',exe],capture_output=True,text=True).stdout for _ in range(3)]
rows = {}; order = []; hdr = None
for out in runs:
    for l in out.splitlines():
        if l.startswith('crosscheck'): print(l); continue
        m = re.match(r'^(.{34}) +(\S+) +(\S+) +(\S+) +(\S+)$', l)
        if not m: continue
        lab = m.group(1).rstrip(); vals = m.groups()[1:]
        if vals[0] == 'mul': hdr = lab; continue
        if lab not in rows: rows[lab] = []; order.append(lab)
        rows[lab].append(vals)
print('%-36s %9s %9s %9s %9s' % (hdr, 'mul', 'square', 'add', 'sub'))
for lab in order:
    cells = []
    for i in range(4):
        v = [r[i] for r in rows[lab]]
        cells.append('-' if v[0] == '-' else '%.1f' % statistics.median(float(x) for x in v))
    print('%-36s %9s %9s %9s %9s' % (lab, *cells))
