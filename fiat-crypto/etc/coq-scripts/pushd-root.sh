#!/usr/bin/env bash

# This is a helper script for make-pretty-timed.sh and
# make-pretty-timed-diff.sh.

# in case we're run from out of git repo
PUSHD_ROOT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$PUSHD_ROOT_DIR" 1>/dev/null

# now change to the git root; use `cd` so we only need one `popd`
ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

# We assume that we're a git submodule, so we need to do this once more
cd ..
# now change to the git root; use `cd` so we only need one `popd`
ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

# Now find a makefile.  We assume that the top-level makefile is last
# in git ls-files; we want to pick up everything, whether it is cached
# or just laying around
MAKEFILE="$(git ls-files --cached --others *GNUmakefile *makefile *Makefile | tail -1)"
if [ ! -z "$MAKEFILE" ]; then
    cd "$(dirname "$MAKEFILE")"
else
    echo "WARNING: No GNUmakefile,makefile,Makefile, found in git ls-files"
fi

MAKEFILE="$((git ls-files --cached --others *Makefile; git ls-files --cached --others *makefile; git ls-files --cached --others *GNUmakefile) | tail -1)"


function relpath() {
    SRC="$(readlink -f "$(pwd)")/"
    TGT="$(readlink -f "$1")"
    RET=""
    while [ ! -z "$SRC$TGT" ]; do
	# strip the first component off both paths
	NEXT_SRC="${SRC#*/}"
	NEXT_TGT="${TGT#*/}"
	CUR_SRC="${SRC%$NEXT_SRC}"
	CUR_TGT="${TGT%$NEXT_TGT}"
	# if they match, and there's something there, then keep going
	if [ "$CUR_SRC" == "$CUR_TGT" ] && [ ! -z "$CUR_SRC" ]; then
	    SRC="$NEXT_SRC"
	    TGT="$NEXT_TGT"
	else
	    # if they don't match, then the entirety of the target goes into the return (only relevant the first time)
	    RET="$TGT"
	    TGT=""
	    # and then if we've actually stripped something off of SRC, we add a ../ to the beginning of ret
	    if [ ! -z "$CUR_SRC" ]; then
		RET="../$RET"
		SRC="$NEXT_SRC"
	    fi
	fi
    done
    echo "$RET"
}
