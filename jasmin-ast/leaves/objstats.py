#!/usr/bin/env python3
"""Per-function statistics from objdump -d (AT&T): instructions, stack loads/stores
(memory operands based on %rsp; lea excluded), conditional jumps, and a few mnemonics.
usage: objstats.py file.o ..."""
import re, subprocess, sys

def stats(obj):
    out = subprocess.run(['objdump', '-d', '--no-show-raw-insn', obj], capture_output=True, text=True, check=True).stdout
    funcs = {}; cur = None
    for l in out.splitlines():
        m = re.match(r'^[0-9a-f]+ <([^>]+)>:$', l)
        if m:
            # 294b46e prints local labels as "Lf$n" (not .L), which become symbols: keep them
            # in the current function
            if not (cur and re.search(r'(^|_)L\w*\$\d+$', m.group(1))):
                cur = m.group(1); funcs[cur] = []
            continue
        m = re.match(r'^\s+[0-9a-f]+:\s+(\S+)\s*(.*)$', l)
        if m and cur: funcs[cur].append((m.group(1), m.group(2).split('#')[0].strip()))
    for f, ins in funcs.items():
        if not ins: continue
        ld = st = jcc = 0; cnt = {}
        for mn, ops in ins:
            cnt[mn] = cnt.get(mn, 0) + 1
            if re.match(r'j(?!mp)', mn): jcc += 1
            if mn.startswith('lea') or '(%rsp' not in ops: continue
            # split operands at top-level commas
            parts = re.split(r',(?![^()]*\))', ops)
            if '(%rsp' in parts[-1] and len(parts) > 1: st += 1
            else: ld += 1
        yield f, len(ins), ld, st, jcc, cnt

print('%-34s %6s %6s %6s %5s %5s %5s %5s %5s %5s %5s %5s' % ('function', 'insns', 'stkld', 'stkst', 'jcc',
      'cmov', 'adc', 'adcx', 'adox', 'sbb', 'mulx', 'imul'))
for o in sys.argv[1:]:
    for f, n, ld, st, jcc, c in stats(o):
        g = lambda pre: sum(v for k, v in c.items() if k.startswith(pre))
        print('%-34s %6d %6d %6d %5d %5d %5d %5d %5d %5d %5d %5d' % (o.split('/')[-1] + ':' + f, n, ld, st, jcc,
              g('cmov'), g('adc') - g('adcx'), g('adcx'), g('adox'), g('sbb'), g('mulx'), g('imul')))
