#!/bin/bash

set -e

PREV_TIME=$(date +%s.%N)

while read i
do
    NEXT="$(date +%s.%N)"
    DIFF="$(echo "$NEXT - $PREV_TIME" | bc)"
    echo "$DIFF: $i"
    PREV_TIME="$NEXT"
done
