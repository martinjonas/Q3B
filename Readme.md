# Q3B-pBDD

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

Q3B-pBBD is a version of Q3B utilizing partial BDDs instead of pairs of BDDs.

## Requirements
* ANTLR 4 (for formula parser)
* Z3 API >= 4.7 (to perform some of simplifications)
* CUDD BDD library (for BDD operations)

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
./q3b file.smt2
```

## Abstractions

If the input formula contains non-linear multiplication or division,
abstractions of variables may be necessary, since otherwise the
conversion to BDD is unlikely to terminate in reasonable time. By
default, Q3B runs underapproximations and overapproximations in
parallel with the base solver. To run only underapproximations or only
overapproximations, run

```
./q3b --abstractions=under file.smt2
```
or
```
./q3b --abstractions=over file.smt2
```

To run the solver without abstractions, run
```
./q3b --abstractions=none file.smt2
```

Q3B supports two types of abstractions, which are both enabled by default:

### Variable bit-width abstractions

If variable abstractions are enabled, Q3B will fix some bits of chosen
variables, which can result in smaller BDDs. To use only these
approximations, run
```
./q3b --abstract:method=variables file.smt2
```

### Abstractions of bit-vector operations

In addition to the mentioned variable approximations, Q3B also offers
abstractions of bit-vector operations. If these abstractions are
enabled, Q3B will compute only several bits of results of operations
like addition or multiplication. It may be the case that only several
result bits are necessary to decide satisfiability of the formula. To use only these
approximations, run
```
./q3b --abstract:method=operations file.smt2
```

## Unconstrained variables

Q3B also employs simplifications of formulas with unconstrained
variables (i.e. variables that occur only once in the formula), as
described in the paper [On Simplification of Formulas with
Unconstrained Variables and
Quantifiers](https://link.springer.com/chapter/10.1007/978-3-319-66263-3_23).
These simplifications are enabled by default; to disable them, use the
parameter `--simpl:unconstrained=0`.

For unconstrained variables, Q3B takes their context into the account.
For each term, Q3B keeps track of its goal: whether we want to
minimize or maximize its signed or unsigned value. This information is
used during the unconstrained variables simplification. To disable it,
use the parameter `--uc:goal=0`.
