# Integer programming proofs for Chvátal's conjecture over finite ground sets

Chvátal's Conjecture states that there can exist no intersecting family in a downset that has more elements than a maximal-sized star. A collection of work on the subject is available on [Chvátal's Website](http://users.encs.concordia.ca/~chvatal/conjecture.html).
We present a computational framework that is able to prove the conjecture for ground sets of seven or fewer elements.

> Leon Eifler, Ambros Gleixner, and Jonad Pulaj: [Chvátal’s Conjecture Holds for Ground Sets of Seven Elements](https://opus4.kobv.de/opus4-zib/frontdoor/index/index/docId/7024). Preprint. Takustr. 7, 14195 Berlin: ZIB, 2018.

This repository provides:
- MPS and ZIMPL files that model the Integer Programs described in the paper.
- Certificate files that show the correctness of the computational proofs
- Links to external software
- An input-checker written in Coq.

## Solving Mixed Integer Programs Exactly

Exact SCIP is the exact rational variant of SCIP. A version that supports automatic certificate generation is available on the [SCIP website](http://scip.zib.de/#exact). It interfaces [QSopt\_Ex](http://www.dii.uchile.cl/~daespino/ESolver_doc/main.html) as an exact rational LP solver. There is a small patch-file in this repository to enable correct printing of certificates in QSopt\_Ex. The correctness of exact SCIP can be verified using [VIPR](https://github.com/ambros-gleixner/VIPR), an independant certificate format for integer programming results.

## An Input checker for VIPR certificates for Chvàtal's Conjecture

This small program written with the [Coq proof assistant](https://coq.inria.fr/)
checks the input for certain [VIPR](https://github.com/ambros-gleixner/VIPR) certificate files
that certify correctness for [Chàtal's Conjecture](http://users.encs.concordia.ca/~chvatal/conjecture.html) for small ground sets,
as proposed in

reference

This repository contains source code, several compilation scripts, as well as some example certificate files.


### Installation instructions

This program needs a working installation of coq.
It uses the Coq.io library which can be installed with opam via


``` bash
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam install -j4 -v coq-io-system
```




To create the Makefile simply run:

``` bash
    ./configure.sh
```

Then run

     make && ./build.sh

to create the executable binary that does the typechecking.
If you run the binary it will ask you for the filename of a vipr-file that should be checked, as well as the size of the groundset as input.

Use the python-script `transvipr.py` on a vipr file to rename the variables so that the order is correct. This does not change the validity of the VIPR certificate.
