#!/bin/sh

exec docker run --rm -it -v "$PWD:/home/opam/work" elpi "$@"
