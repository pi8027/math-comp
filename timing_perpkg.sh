#!/bin/bash
shopt -s globstar # not needed in zsh
BEFORE=upstream/master
AFTER=upstream/split-order

git checkout $(git merge-base $BEFORE $AFTER) -- .
make clean
make Makefile.coq
echo '***** BEFORE *****'
time make -j 8 boot/all_boot.vo
time make -j 8 fingroup/all_fingroup.vo
time make -j 8 order/all_order.vo
time make -j 8 algebra/all_algebra.vo
time make -j 8 solvable/all_solvable.vo
time make -j 8 field/all_field.vo
time make -j 8 character/all_character.vo

git checkout $AFTER -- .
touch **/*.v
make clean
make Makefile.coq
echo '***** AFTER *****'
time make -j 8 boot/all_boot.vo
time make -j 8 fingroup/all_fingroup.vo
time make -j 8 order/all_order.vo
time make -j 8 algebra/all_algebra.vo
time make -j 8 solvable/all_solvable.vo
time make -j 8 field/all_field.vo
time make -j 8 character/all_character.vo

git reset --hard
