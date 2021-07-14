#!/usr/bin/env bash
script="$1"
shift
"$@" 2> >("$script" >&2)
