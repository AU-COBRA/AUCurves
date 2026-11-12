#!/usr/bin/env python3
"""ct_sanitize.py IN OUT: turn the program printed by `jast294c -bls12-leaves -pcstexp` (Jasmin 294b46e
pretty-printer, debug names `x.N`, temporaries `$..`) into a .jazz file that jasmin-ct 2026.09.0 parses,
and add explicit CT contracts (pointers public; memory, hence the field elements, secret)."""
import re, sys
s = open(sys.argv[1]).read(); s = s[s.index('export'):]
s = re.sub(r'\$([A-Za-z]*)\.(\d+)', lambda m: 'T' + m.group(1) + '_' + m.group(2), s)
s = re.sub(r'\b([A-Za-z_][A-Za-z0-9_]*)\.(\d+)\b', r'\1_\2', s)
s = re.sub(r'export\s*\nfn (bls12_square)', r'#[ct = "public × public → ()"]\nexport\nfn \1', s)
s = re.sub(r'export\s*\nfn (bls12_(mul|add|sub))', r'#[ct = "public × public × public → ()"]\nexport\nfn \1', s)
open(sys.argv[2], 'w').write(s)
