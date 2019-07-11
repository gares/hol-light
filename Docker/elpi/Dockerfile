### ===========================================================================
### Elpi lambda prolog interpreter on docker.
### ===========================================================================

FROM ocaml/opam2:debian-stable

USER root

RUN apt-get update && \
    apt-get -y install m4 rlwrap

USER opam

WORKDIR /home/opam/opam-repository

RUN git pull && \
    opam update && \
    opam switch create 4.07.1 ocaml-base-compiler.4.07.1 && \
    eval `opam config env` && \
    opam pin add elpi git+https://github.com/lpcic/elpi && \
    opam install elpi

RUN mkdir -p /home/opam/work

WORKDIR /home/opam/work

CMD rlwrap elpi
