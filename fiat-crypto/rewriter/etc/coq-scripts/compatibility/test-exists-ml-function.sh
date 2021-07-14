#!/bin/bash

set -x

FILE="conftest.ml"
MAKEFILE=""

function cleanup () {
    PREFILE="${FILE%.ml}"
    rm -f "$PREFILE.cmi" "$PREFILE.cmo" "$PREFILE.cmx" "$PREFILE.cmxs" "$PREFILE.ml.d" "$PREFILE.o" "$FILE" "$MAKEFILE" "$MAKEFILE.conf"
}

trap cleanup EXIT

cat > "$FILE" <<EOF
let test = $FUNCTION
EOF

cat "$FILE"

MAKEFILE="$(mktemp)"
(("${COQBIN}coq_makefile" "$FILE" -R . Top -o "$MAKEFILE" || "${COQBIN}coq_makefile" "$FILE" -R . Top > "$MAKEFILE")
     && make -f "$MAKEFILE" || exit 1)

exit 0
