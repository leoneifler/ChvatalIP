#!/usr/bin/python
# usage: python create_cmatrix.py probname sdname ncluster

import sys
import matplotlib.pyplot as plt
import numpy as np
import re
import glob, os
from itertools import chain, combinations

def createSetNumber(Set):
    ret = 0
    for s in Set:
        ret = ret + 2 ** (s - 1)
    return ret - 1

def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

def createConversion( size ):
    powS = list(powerset(range(1,size+1)))[1:]
    c = 0
    #print powS
    convtbl = []
    for s in powS:
        #print (s)
        #print createSetNumber(s)
        convtbl.append( createSetNumber(s) )
        c = c + 1
    #print convtbl
    return convtbl

vipfile = sys.argv[1]
size =  int( sys.argv[2] )
outputname = vipfile + 'conv'
table = createConversion(size)



with open(vipfile, 'r') as file:
    outfile = open(outputname, 'w')
    vartablestarted = False
    for line in file.readlines():
        if line.strip() == '':
            continue
        if not vartablestarted:
            if line.split()[0] == 'VAR':
                vartablestarted = True
            outfile.write(line)
        else:
            if line.split()[0] == 'INT':
                vartablestarted = False
                outfile.write(line)
            else:
                elems = re.split('\$|#', line)
                if len(elems) < 3:
                    outfile.write(line)
                else:
                    #print elems
                    varIsX = (elems[1] == 'x')
                    index =  int(elems[2])
                    #print varIsX
                    #print index
                    chgIndex = str(table[index])
                    elems[2] = chgIndex
                    outfile.write( elems[0] + '$' + elems[1] + '#' + elems[2] + '\n')
file.close()
outfile.close()




