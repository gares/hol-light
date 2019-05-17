### ===========================================================================
### Dockerfile for a debian image with all ready to run HOL Light.
### Marco Maggesi (University of Florence, Italy)
### ===========================================================================

### ---------------------------------------------------------------------------
### Usage
###
### To build the container:
### docker build --target holelpi -t holelpi Stack
### or
### docker build --pull --no-cache --target holelpi -t holelpi Stack
###
### To start the container:
### docker run --rm -it -v 'path-to-hol-dir:/home/opam/work'
### ---------------------------------------------------------------------------

### ---------------------------------------------------------------------------
### Target: holelpi
### Debian image with elpi, dmtcp and minimal software installed (OCaml).
### ---------------------------------------------------------------------------

FROM ocaml/opam2:debian-stable AS holelpi

USER root

RUN apt-get update && \
    apt-get -y install build-essential git curl make m4 rlwrap screen tmux

USER opam

RUN eval `opam config env` && \
    opam update && \
    opam switch create 4.07.0 ocaml-base-compiler.4.07.0 && \
    opam pin camlp5 7.06 && \
    opam pin add elpi git+https://github.com/lpcic/elpi && \
    opam install num camlp5 elpi

## ----------------------------------------------------------------------------
## Install Dmtcp (version 2018-11-12).
## ----------------------------------------------------------------------------

USER opam

RUN mkdir -p src/dmtcp

WORKDIR src/dmtcp

ARG DMTCP_VERSION=cfe168e2539b60e29bbac27da9a8b78b77add2a6

RUN curl -sL https://github.com/dmtcp/dmtcp/archive/$DMTCP_VERSION.tar.gz | \
    tar xz --strip-components=1

RUN ./configure --prefix=/usr/local && make -j 2

USER root

RUN make install

USER opam

RUN mkdir -p /home/opam/work

WORKDIR /home/opam/work
