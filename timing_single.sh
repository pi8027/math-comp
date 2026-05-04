#!/bin/bash
shopt -s globstar # not needed in zsh
BEFORE=upstream/master
AFTER=upstream/split-order

git checkout $(git merge-base $BEFORE $AFTER) -- .
make clean
make Makefile.coq
echo '***** BEFORE *****'
time make -j 8

git checkout $AFTER -- .
touch **/*.v
make clean
make Makefile.coq
echo '***** AFTER *****'
time make -j 8

git reset --hard
