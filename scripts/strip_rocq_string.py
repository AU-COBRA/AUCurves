#!/usr/bin/env python3
"""Strip Rocq Eval output framing to recover the underlying string.
Input: file with `     = "..."` followed by `     : string`
Output: bare string content with Rocq escaping (\n, \\) decoded.
"""
import sys

def strip(path_in, path_out):
    with open(path_in) as f:
        content = f.read()
    # Find the opening `= "` and the trailing `"\n     : string`
    start = content.find('= "')
    if start == -1:
        sys.stderr.write(f"No `= \"` found in {path_in}\n")
        sys.exit(1)
    start += 3
    end = content.rfind('"\n     : string')
    if end == -1:
        end = content.rfind('"')
    body = content[start:end]
    # Rocq's pretty-printer escapes embedded `"` as `""` inside string literals.
    # Decode that back to a single `"`.
    body = body.replace('""', '"')
    with open(path_out, "w") as f:
        f.write(body)
    print(f"Wrote {path_out} ({len(body)} bytes)")

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: strip_rocq_string.py <input.out> <output.rs>")
        sys.exit(1)
    strip(sys.argv[1], sys.argv[2])
