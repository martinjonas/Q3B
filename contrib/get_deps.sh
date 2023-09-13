#!/usr/bin/env bash

set -x

pushd contrib

git clone -b z3-4.11.2 https://github.com/Z3Prover/z3.git
pushd z3
cmake -S . -B build -DZ3_BUILD_LIBZ3_SHARED=False -DCMAKE_BUILD_TYPE=Release
cmake --build build -j4
popd

git clone https://github.com/martinjonas/cudd.git
pushd cudd
./configure --enable-silent-rules --enable-obj --enable-shared && make -j4
popd

mkdir antlr
wget https://www.antlr.org/download/antlr-4.11.1-complete.jar -P antlr

popd
