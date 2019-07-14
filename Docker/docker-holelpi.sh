#!/bin/sh

# MNTPATH='/Users/maggesi/Devel/HOL/hol-light-elpi'
MNTPATH="$PWD"

exec docker run --rm -it -m 6G -h holelpi \
       -v "$MNTPATH:/home/opam/work" \
       holelpi
