#!/usr/bin/env bash

set -e

curerr=""

while read i
do
    # ^File \"([^ \"]+)\", line (\\d+), characters (\\d+-\\d+):
    if [[ "$i" == "File "*:* ]]; then # first line of error
        if [ ! -z "$curerr" ]; then
            echo "$curerr"
        fi
        curerr="$i"
    elif [ ! -z "$curerr" ]; then
        curerr+="%0A$i"
    else # not part of a recognized error
        echo "$i"
    fi
done
if [ ! -z "$curerr" ]; then
    echo "$curerr"
fi
