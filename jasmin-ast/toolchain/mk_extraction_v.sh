#!/bin/bash
# Generates jasmin294_extraction.v from jasmin 294b46e's proofs/lang/extraction.v:
#  - line 1  "Require jasmin_compiler."  ->  "From Jasmin Require jasmin_compiler."
#    (the library is installed under the logical name Jasmin in the switch)
#  - lines 5-7 "From Coq Require ExtrOcamlBasic/ExtrOcamlNativeString/ExtrOCamlInt63."
#    -> contents of prelude_stdlib_extraction.v (patched plugin + inlined directives)
#  - everything else (all Extract / Extraction Inline / Blacklist directives,
#    the output directory and the Separate Extraction list) is kept verbatim.
set -euo pipefail
cd "$(dirname "$0")"
J=${JAST_TOOLS:-$HOME/tools}/src/jasmin-git
git -C $J show 294b46e:proofs/lang/extraction.v > extraction.v.294b46e
test "$(sed -n 1p extraction.v.294b46e)" = "Require jasmin_compiler."
test "$(sed -n 5,7p extraction.v.294b46e)" = "$(printf 'From Coq Require ExtrOcamlBasic.\nFrom Coq Require ExtrOcamlNativeString.\nFrom Coq Require ExtrOCamlInt63.')"
{
  echo "From Jasmin Require jasmin_compiler."
  sed -n 2,4p extraction.v.294b46e
  cat prelude_stdlib_extraction.v
  sed -n '8,$p' extraction.v.294b46e
} > jasmin294_extraction.v
