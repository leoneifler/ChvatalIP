#!/bin/sh

mkdir bin
coq_makefile -arg "-w -notation-overridden,extraction" -f Make -o Makefile
