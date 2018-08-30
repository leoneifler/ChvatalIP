# n is the cardinality of the set. It can be set via input-parameter with -D n=...
# To generate an MPS file, call "zimpl -o outputname -t mps -D n=cardinality chvatal_infprob_red.zpl"
param n :=6;

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


#generating inequality
subto ideal: forall <t> in I do
    forall <s> in I with card(P[s] union P[t]) == card(P[t]) do
        y[t] - x[s] <= 0;

# intersecting family
subto intersect: forall <t,s> in I * I 
    with card(P[t] inter P[s]) == 0 do
        y[t]+y[s] <= 1;

# the size of y has to be greater than every star
subto smallerstar: forall <i> in N do
    (sum <s> in I with <i> in P[s]: x[s]) - (sum <s> in I: y[s]) <= -1;


##################################
#
# additional inequalities to strengthen the formulation
#
#################################

# if the intersecting family contains the whole groundset then the ideal is
# the powerset and the conjecture holds
subto notps: forall <i> in I with card(P[i]) == n do
      y[i] <= 0;

# the singletons in the ideal can all be fixed to one, since then the other cases are
# covered by a smaller n
subto singleton_ideal: forall <s> in I
      with card(P[s]) == 1 do
           x[s] == 1; 

# if a singleton is in an intersecting family it must be a star so these can be set to
# 0. The same holds for 2-sets
subto twoset_intersect: forall <s> in I
      with card(P[s]) <= 2 do
           y[s] == 0;

# berge's inequality is valid 
subto berge:
    sum <i> in I: (2 * y[i] - x[i]) <= 0; 

# we know that the conjecture holds for 3sets. Therefore we know at least one 4-set has to be part
# of the ideal. Wlog we assume this to be {1,2,3,4}.
subto fix4set:
      forall <t> in I with card(P[t] union {1 to 4}) == 4 do
                   x[t] == 1;
