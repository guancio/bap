#!/bin/sh

as -g --32 --march=i386 test.s -o test.o
~/Downloads/bap-0.4/utils/toil -bin test.o -o test.il

# gcc -c test.c -o test.o
# arm-none-eabi-as -mcpu=arm926ej-s -g startup.s -o startup.o
# arm-none-eabi-ld -T test.ld test.o startup.o -o test.elf