# Q3B

[![Build Status](https://travis-ci.org/martinjonas/Q3B.svg?branch=dev)](https://travis-ci.org/martinjonas/Q3B)
[![Coverage Status](https://coveralls.io/repos/github/martinjonas/Q3B/badge.svg?branch=dev)](https://coveralls.io/github/martinjonas/Q3B?branch=dev)

Q3B is an SMT solver for the quantified bit-vector formulas which uses
BDDs. In a nutshell, it simplifies the input formula, converts it to
the equivalent BDD, and answers `sat` if there is a satisfying path in
the BDD. Q3B can also use approximations of formulas to solve some
formulas containing complicated arithmetic, which can be hard to solve
using BDDS.

Details of the approach can be found in the paper [*Solving Quantified
Bit-Vector Formulas Using Binary Decision
Diagrams*](https://link.springer.com/chapter/10.1007/978-3-319-40970-2_17).

## Requirements
* Z3 API is used to parse the formula and to perform some of
  simplifications
* CUDD BDD library

## Compilation
Q3B can be compiled by running

```
mkdir build
cd build
cmake ..
make
```

## Usage
To process the file `file.smt2` in the SMT-LIB 2.5 format, run

```
./Q3B file.smt2
```

## Approximations

If the input formula contains non-linear multiplication, you might
want to try underapproximations or overapproximations, since otherwise
the conversion to BDD is unlikely to terminate in reasonable time.

To run the solver in parallel with underapproximations and
overapproximations, run

```
./Q3B -A file.smt2
```

To run only underapproximations or only approximations, run

```
./Q3B -U file.smt2
```
or
```
./Q3B -O file.smt2
```

## Unconstrained variables

Q3B also employs simplifications of formulas with unconstrained
variables (i.e. variables that occur only once in the formula), as
described in the paper [On Simplification of Formulas with
Unconstrained Variables and
Quantifiers](https://link.springer.com/chapter/10.1007/978-3-319-66263-3_23).
To enable these simplifications, use the parameter
`--propagate-unconstrained`.
