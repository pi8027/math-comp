#!/bin/bash
shopt -s globstar # not needed in zsh
BEFORE=upstream/master
AFTER=upstream/split-order

git checkout $(git merge-base $BEFORE $AFTER) -- .
make clean
make Makefile.coq
TIMING=before make -f Makefile.coq make-pretty-timed-before

git checkout $AFTER -- .
touch **/*.v
make Makefile.coq
TIMING=after make -f Makefile.coq make-pretty-timed-after

make -f Makefile.coq print-pretty-timed-diff

git reset --hard
