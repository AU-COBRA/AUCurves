#!/usr/bin/env bash
# Strip the Rocq `Redirect ... Eval ... : string` wrapper from a *_rocq.out
# file, producing clean Jasmin source on stdout.
#
# The wrapper format is:
#       = "<jazz line 1>
#   <jazz line 2>
#   ...
#   <jazz line N>"
#       : string
#
# i.e. the first line is prefixed with `     = "`, the final jazz content is
# followed by a line that is just `"` and then `     : string`.  No `"`
# characters occur inside emitted Jasmin, so the de-escaping is trivial.
set -euo pipefail
in="$1"
# Drop the final two wrapper lines ('"' and '     : string'), then strip the
# leading `     = "` from the first remaining line.
nlines=$(wc -l < "$in")
body_lines=$((nlines - 2))
first=1
head -n "$body_lines" "$in" | while IFS= read -r line; do
  if [ "$first" = 1 ]; then
    printf '%s\n' "${line#*= \"}"
    first=0
  else
    printf '%s\n' "$line"
  fi
done
