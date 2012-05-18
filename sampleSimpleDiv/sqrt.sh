#!/bin/sh

gcc -m32 -c -g sqrt.c -o sqrt.o
~/Downloads/bap-0.4/utils/toil -bin sqrt.o -o sqrt.il
./sqrt.py
~/Downloads/bap-0.4/utils/topredicate -il sqrt.il  -post goal
~/Downloads/bap-0.4/utils/topredicate -il sqrt.il -stp-out sqrt.stp -post goal