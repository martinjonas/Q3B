# News

## 1.1 (dev)

– Fix unsoundness issues caused by variable polarities.
– Fix abstractions for Boolean =.
– Disable (incorrect) DAG counting in unconstrained variable simplifier.
– Terminate threads during BDD operations using CUDD termination handler.
– Add support for Boolean “distinct” operator.
– Add support for n-ary bitwise connectives.
– Several improvements to formula rewriting.
– Update ANTLR version to v4.10.
– Update Catch to v2.13.9.

## 1.0 (commit 9630b6ccf6c116d42f00da8a9c88086206d71d57)

This is the version described in the CAV 2019 paper “Q3B: an efficient bdd-based
SMT solver for quantified bit-vectors”.
