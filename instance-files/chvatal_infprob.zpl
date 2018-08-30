# n is the cardinality of the set. It can be set via input-parameter with -D n=...
# To generate an MPS file, call "zimpl -o outputname -t mps -D n=cardinality chvatal_infprob.zpl"
param n := 6;

set N             := { 1 .. n };
set P[]           := subsets(N,1,n);
set I             := indexset(P);

var x[I] binary;
var y[I] binary;

# objective function
maximize cost: sum <i> in I: x[i];


#################################
#
# model constraints
#
#################################

#ideal inequality
subto ideal: forall <t> in I do
    forall <s> in I with card(P[s] union P[t]) == card(P[t]) do
        x[t] - x[s] <= 0;

# intersecting family
subto intersect: forall <t,s> in I * I 
    with card(P[t] inter P[s]) == 0 do
        y[t]+y[s] <= 1;

# the size of y has to be greater than every star
subto smallerstar: forall <i> in N do
    (sum <s> in I with <i> in P[s]: x[s]) - (sum <s> in I: y[s]) <= -1;

#containment inequality
subto containment: forall <t> in I do
      y[t] <= x[t];


