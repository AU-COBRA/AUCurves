import subprocess, sys, time, resource, os, threading
t0=time.time()
p=subprocess.Popen(sys.argv[1:])
peak=[0]
def watch():
    while p.poll() is None:
        try:
            # sum RSS of process tree
            tot=0
            for pid in [p.pid]+[int(x) for x in os.popen(f'pgrep -P {p.pid}').read().split()]:
                with open(f'/proc/{pid}/status') as fh:
                    for l in fh:
                        if l.startswith('VmRSS'): tot+=int(l.split()[1])
            peak[0]=max(peak[0],tot)
            if tot>12*1024*1024: p.kill(); print('KILLED >12GB',file=sys.stderr)
        except Exception: pass
        time.sleep(0.5)
th=threading.Thread(target=watch,daemon=True); th.start()
rc=p.wait()
ru=resource.getrusage(resource.RUSAGE_CHILDREN)
print(f'[measure] rc={rc} wall={time.time()-t0:.1f}s maxrss={max(ru.ru_maxrss//1024, peak[0]//1024)}MB', file=sys.stderr)
sys.exit(rc)
