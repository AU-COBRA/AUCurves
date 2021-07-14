#!/usr/bin/env bash

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source "$DIR/../pushd-root.sh"

# exit immediately if killed
trap "exit 1" SIGHUP SIGINT SIGTERM

if [ -z "$(find . -name "*.timing")" ]
then
    exit 0 # no timing files exist
fi

for i in $(find . -name "*.timing")
do
    echo "$i"
    cat "$i"
    # echo a final new line, because `cat` doesn't
    echo
    # and another for whitespace
    echo
done
