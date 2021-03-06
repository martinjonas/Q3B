(set-info :smt-lib-version 2.6)
(set-logic BV)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: ETCS-essentials, node 3023 For more info see: @see "Andre Platzer. Differential dynamic logic for hybrid systems. Journal of Automated Reasoning, 41(2), pages 143-189, 2008."

Translated to BV by Mathias Preiner.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun v () (_ BitVec 32))
(declare-fun vuscore2dollarskuscore0 () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun A () (_ BitVec 32))
(declare-fun t1uscore0dollarskuscore0 () (_ BitVec 32))
(declare-fun ep () (_ BitVec 32))
(declare-fun m () (_ BitVec 32))
(declare-fun zuscore2dollarskuscore0 () (_ BitVec 32))
(declare-fun ts1uscore0 () (_ BitVec 32))
(declare-fun z () (_ BitVec 32))
(assert (not (exists ((ts1uscore0 (_ BitVec 32))) (let ((?v_3 (bvneg b)) (?v_1 (bvmul (_ bv2 32) b)) (?v_0 (bvmul vuscore2dollarskuscore0 vuscore2dollarskuscore0)) (?v_2 (bvsub m zuscore2dollarskuscore0))) (let ((?v_4 (bvadd (bvmul ?v_3 t1uscore0dollarskuscore0) vuscore2dollarskuscore0))) (=> (and (and (and (and (and (and (=> (and (bvsle (_ bv0 32) ts1uscore0) (bvsle ts1uscore0 t1uscore0dollarskuscore0)) (and (bvsge (bvadd (bvmul ?v_3 ts1uscore0) vuscore2dollarskuscore0) (_ bv0 32)) (bvsle ts1uscore0 ep))) (bvsge t1uscore0dollarskuscore0 (_ bv0 32))) (bvsle ?v_2 (bvadd (bvsdiv ?v_0 ?v_1) (bvmul (bvadd (bvsdiv A b) (_ bv1 32)) (bvadd (bvmul (bvsdiv A (_ bv2 32)) (bvmul ep ep)) (bvmul ep vuscore2dollarskuscore0)))))) (bvsle ?v_0 (bvmul ?v_1 ?v_2))) (bvsle (bvmul v v) (bvmul ?v_1 (bvsub m z)))) (bvsgt b (_ bv0 32))) (bvsge A (_ bv0 32))) (bvsle (bvmul ?v_4 ?v_4) (bvmul ?v_1 (bvsub m (bvmul (bvsdiv (_ bv1 32) (_ bv2 32)) (bvadd (bvadd (bvmul ?v_3 (bvmul t1uscore0dollarskuscore0 t1uscore0dollarskuscore0)) (bvmul (bvmul (_ bv2 32) t1uscore0dollarskuscore0) vuscore2dollarskuscore0)) (bvmul (_ bv2 32) zuscore2dollarskuscore0))))))))))))
(check-sat)
(exit)
