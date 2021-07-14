#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

CUR_VERSION="$(grep -m 1 '^ALL_VERSIONS=' generate-compat-files.sh | sed 's/ALL_VERSIONS=\|"\|trunk\|master//g' | grep -o '[^ ]\+\s*$' | sed 's/ //g')"
MAJOR="$(echo "${CUR_VERSION}" | grep -o '^[0-9]*')"
MINOR="$(echo "${CUR_VERSION}" | grep -o '[0-9]*$')"
NEXT_MINOR="$((${MINOR} + 1))"
sed "s/${MAJOR}_${MINOR}/${MAJOR}_${MINOR} ${MAJOR}_${NEXT_MINOR}/g" -i generate-compat-files.sh
cp "Coq__${MAJOR}_${MINOR}__Compat.v.in" "Coq__${MAJOR}_${NEXT_MINOR}__Compat.v.in"
./generate-compat-files.sh
git add "Coq__${MAJOR}_${NEXT_MINOR}__Compat.v.in" "Coq__${MAJOR}_${NEXT_MINOR}__Compat.v"
