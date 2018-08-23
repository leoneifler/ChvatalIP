# An Input checker for VIPR certificates for Chvàtal's Conjecture

This small program written with the [Coq proof assistant](https://coq.inria.fr/)
checks the input for certain [VIPR](https://github.com/ambros-gleixner/VIPR) certificate files
that certify correctness for [Chàtal's Conjecture](http://users.encs.concordia.ca/~chvatal/conjecture.html) for small ground sets,
as proposed in

reference

This repository contains source code, several compilation scripts, as well as some example certificate files.


## Installation instructions

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
