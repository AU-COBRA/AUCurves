#!/usr/bin/env bash

if [ -z "$1" ] || [ "$1" == "-h" ] || [ "$1" == "--help" ]
then
    cat <<EOF
Make a Makefile Coq library dependency graphs

USAGE: $0 MAKEFILE_NAME [DepsToDot Options]

This script creates a file (MAKEFILE_NAME) to make library wide
dependency graphs.  The makefile depends on having the "dot" program,
as well as Haskell and the GraphViz package installed.  The contents
of the HASKELL environment variable, if it is non-empty, is used to
run haskell.  The contents of the DOT environment variable, if set, is
used to run the "dot" program.

EOF
    exit 1
fi

OUTPUT_FILE="$(readlink -f "$1")"
OUTPUT_DIR="$( cd "$( dirname "$OUTPUT_FILE" )" && pwd )"

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source "$DIR/../../pushd-root.sh"

shift

MAKEFILE="$(readlink -f "$MAKEFILE")"

cd "$OUTPUT_DIR"

MAKEFILE="$(relpath "$MAKEFILE")"

DEPSTODOT="$(relpath "$DIR/DepsToDot.hs")"

# exit immediately if killed
trap "exit 1" SIGHUP SIGINT SIGTERM

if [ -z "$DOT" ]
then
    DOT=dot
fi

if [ -z "$HASKELL" ]
then
    HASKELL=runhaskell
fi

type runhaskell 2>&1 >/dev/null
if [ $? -ne 0 ]
then
    echo "WARNING: runhaskell not found; you'll probably need to install Haskell"
fi

type dot 2>&1 >/dev/null
if [ $? -ne 0 ]
then
    echo "WARNING: dot not found; you'll probably need to install GraphViz"
fi

cat > "$OUTPUT_FILE" <<EOF
all: library.deps library.svg library.dot

-include $MAKEFILE

V = 0

Q_0 := @
Q_1 :=
Q = \$(Q_\$(V))

VECHO_0 := @echo
VECHO_1 := @true
VECHO = \$(VECHO_\$(V))

DOT := $DOT
HASKELL := $HASKELL

.PHONY: all

all: library.deps library.svg library.dot

library.deps: \$(VFILES)
	\$(VECHO) "COQDEP > \$@"
	\$(Q) \$(COQDEP) \$(COQLIBS) \$(VFILES) | sed s'#\\\\#/#g' > "\$@"

%.dot: %.deps
	\$(VECHO) "DEPSTODOT \$< -o \$@"
	\$(Q) \$(HASKELL) "$DEPSTODOT" $@ -i "\$<" -o "\$@"

%.svg: %.dot
	\$(VECHO) "DOT \$< -o \$@"
	\$(Q) \$(DOT) -Tsvg "\$<" -o "\$@"

EOF
