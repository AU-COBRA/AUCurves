#!/usr/bin/env bash

# This is a helper script for make-pretty-timed-diff.sh.

# This script is used to combine the outputs of make-each-time-file.sh
# into a single prettified table of compilation performance.

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source "$DIR/../pushd-root.sh"

V=""
if [ "$1" == "-v" ]; then V=1; fi
if [ "$1" == "--verbose" ]; then V=1; fi

# from http://stackoverflow.com/questions/18973057/list-all-text-non-binary-files-in-repo, list non-binary files
for i in $(git grep --cached -I -l -e '')
do
    if [ ! -z "$V" ]; then echo "$i"; fi
    if [ ! -z "$(grep ' $' "$i")" ]
    then
	sed -i s'/\s\+$//g' "$i"
    fi
    # command subsitution strips trailing newlines
    if [ "$(echo "$(cat "$i")" | wc -l)" -ne "$(cat "$i" | wc -l)" ]
    then
	echo "$(cat "$i")" > "$i"
    fi
done
	
	
