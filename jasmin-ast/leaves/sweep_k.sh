#!/bin/bash
# For each leaf and K, compile BLS12Leaves.bls12_leaves_prog ... K with jast294c -bls12-leaves
# -spill-K K -leaves-only <leaf> (no -auto-spill); record ok/error, time, and the .s.
# Output: sweep/<leaf>_K<k>.s or sweep/<leaf>_K<k>.err, and sweep/summary.tsv
. $HOME/rocq92-env.sh
J=${JAST_TOOLS:-$HOME/tools}/jast; cd $J/sweep
# requested K list plus the largest K that compiles for add (15) and mul/square (29), from a finer sweep
KS="${KS:-0 1 2 4 8 12 15 16 24 29 32 64 100000}"
echo -e "leaf\tK\tresult\tseconds\tdetail" > summary.tsv
for f in add sub mul square; do for k in $KS; do
  rm -f bls12_${f}_K$k.s bls12_${f}_K$k.err
  t0=$(date +%s.%N)
  if timeout 300 ${JAST_TOOLS:-$HOME/tools}/bin/jast294c -bls12-leaves -spill-K $k -leaves-only bls12_$f -o bls12_${f}_K$k.s > bls12_${f}_K$k.err 2>&1; then
    r=ok; d="$(grep -c . bls12_${f}_K$k.s) lines"; [ -s bls12_${f}_K$k.err ] || rm -f bls12_${f}_K$k.err
  else
    r=FAIL; rm -f bls12_${f}_K$k.s; d="$(sed -n 2,3p bls12_${f}_K$k.err | tr -s ' \n' ' ')"
  fi
  t=$(echo "$(date +%s.%N) - $t0" | bc)
  printf '%s\t%s\t%s\t%.1f\t%s\n' bls12_$f $k $r $t "$d" | tee -a summary.tsv
done; done
