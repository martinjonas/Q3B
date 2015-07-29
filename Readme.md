# QuantifiedBvecToBdd
QuantifiedBvecToBdd is a prototype implementation of SMT solver for the quantified bit-vector logic which uses BDDs. In a nutshell, it simplifies input formula, converts it to the equivalent BDD, and answers `sat` if there is satisfying path in the BDD.

The tool is still mostly test of a concept.

## Requirements
* Z3 API is used for parsing and to perform some of simplifications
* Buddy BDD library

## Usage
To process file `file.smt2` in smt-lib format, run

``` 
./QuantifiedBvecToBdd file.smt2
```

If the input formula contains non-linear multiplication, you might want to try underapproximation or overapproximation, since otherwise the conversion to BDD is unlikely to terminate in a reasonable time. During underapproximation, effective bit-width of all _existentially quantified_ variables is reduced to a given number. Similarly, during overapproximation, effective bit-width of all _universally quantified_ variables is reduced to a given number.

#### Approximations

##### Underapproximation
For example, to use just two least-significant bits from each existentially quantified variable, use the following command (remaining bits are sign-extension). 
```
./QuantifiedBvecToBdd file.smt2 -u 2
```

To use just two most-significant bits from each existentially quantified variable, use the following command (remaining bits are zeroes). 
```
./QuantifiedBvecToBdd file.smt2 -u -2
```

##### Overapproximation
To use just two least-significant bits from each universally quantified variable, use the following command (remaining bits are zeroes). 
```
./QuantifiedBvecToBdd file.smt2 -o 2
```

To use just two most-significant bits from each universally quantified variable, use the following command (remaining bits are zeroes). 
```
./QuantifiedBvecToBdd file.smt2 -o -2
```

##### Try several approximations
To try underapproximations and overapproximations using several values, you can use command
```
./QuantifiedBvecToBdd file.smt2 --try-approximations
```
which basically performs
```
./QuantifiedBvecToBdd file.smt2 -o 1
./QuantifiedBvecToBdd file.smt2 -o -1
./QuantifiedBvecToBdd file.smt2 -u 1
./QuantifiedBvecToBdd file.smt2 -u -1

./QuantifiedBvecToBdd file.smt2 -o 2
./QuantifiedBvecToBdd file.smt2 -o -2
./QuantifiedBvecToBdd file.smt2 -u 2
./QuantifiedBvecToBdd file.smt2 -u -2

./QuantifiedBvecToBdd file.smt2 -o 4
./QuantifiedBvecToBdd file.smt2 -o -4
./QuantifiedBvecToBdd file.smt2 -u 4
./QuantifiedBvecToBdd file.smt2 -u -4

...

./QuantifiedBvecToBdd file.smt2 -o 16
./QuantifiedBvecToBdd file.smt2 -o -16
./QuantifiedBvecToBdd file.smt2 -u 16
./QuantifiedBvecToBdd file.smt2 -u -16

./QuantifiedBvecToBdd file.smt2
```
