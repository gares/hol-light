#!/bin/sh

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
MNTPATH=$(dirname "${DIR}")

exec docker run --rm -it -h holelpi \
       -v "${MNTPATH}:/home/opam/work" \
       holelpi
