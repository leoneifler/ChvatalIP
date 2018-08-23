extfold='bin'
execf='checkvipr.native'
cmd='ocamlbuild checkvipr.native -use-ocamlfind -package io-system'

cd $extfold
eval $cmd


