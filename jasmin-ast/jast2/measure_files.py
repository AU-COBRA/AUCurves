import subprocess, sys, re, os, shlex
import os
A=os.environ.get('AUCURVES', os.path.expanduser('~/AUCurves'))
env=dict(os.environ)
res=[]
for f in sys.argv[1:]:
    out=subprocess.run(['dune','rules',f+'o'],cwd=A,capture_output=True,text=True).stdout
    i=out.rindex('(action')
    act=out[i:]
    m=re.search(r'\(run\s+(.*?)\)\)\)', act, re.S)
    toks=re.findall(r'"(?:[^"\\]|\\.)*"|[^\s()]+', m.group(1))
    toks=[t.strip('"') for t in toks]
    r=subprocess.run(['python3',A+'/jasmin-ast/leaves/measure.py']+toks,cwd=A+'/_build/default',capture_output=True,text=True)
    line=[l for l in r.stderr.splitlines() if '[measure]' in l]
    print(f, line[-1] if line else r.stderr[-500:], flush=True)
