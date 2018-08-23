#!/bin/sh

if [ ! -d "bin" ]; then
    mkdir bin
fi

coq_makefile -arg "-w -notation-overridden,extraction" -f Make -o Makefile
