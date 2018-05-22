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

 KeYmaera example: binary_driver-2007-10-09, node 11383 For more info see: No further information available.

Translated to BV by Mathias Preiner.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun ts4uscore0 () (_ BitVec 32))
(declare-fun vuscore2dollarskuscore5 () (_ BitVec 32))
(declare-fun duscore2dollarskuscore5 () (_ BitVec 32))
(declare-fun d () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun vdesuscore2dollarskuscore4 () (_ BitVec 32))
(declare-fun stateuscore2dollarskuscore2 () (_ BitVec 32))
(declare-fun m () (_ BitVec 32))
(declare-fun zuscore2dollarskuscore5 () (_ BitVec 32))
(declare-fun v () (_ BitVec 32))
(declare-fun ep () (_ BitVec 32))
(declare-fun muscore2dollarskuscore5 () (_ BitVec 32))
(declare-fun t4uscore0dollarskuscore0 () (_ BitVec 32))
(declare-fun z () (_ BitVec 32))
(declare-fun amax () (_ BitVec 32))
(assert (not (exists ((ts4uscore0 (_ BitVec 32))) (let ((?v_1 (bvneg b)) (?v_0 (bvmul (_ bv2 32) b)) (?v_3 (bvmul duscore2dollarskuscore5 duscore2dollarskuscore5))) (let ((?v_2 (bvadd (bvmul ?v_1 t4uscore0dollarskuscore0) vuscore2dollarskuscore5))) (=> (and (and (and (and (and (and (and (and (and (and (and (and (=> (and (bvsle (_ bv0 32) ts4uscore0) (bvsle ts4uscore0 t4uscore0dollarskuscore0)) (and (bvsge (bvadd (bvmul ?v_1 ts4uscore0) vuscore2dollarskuscore5) (_ bv0 32)) (bvsle ts4uscore0 ep))) (bvsge t4uscore0dollarskuscore0 (_ bv0 32))) (= stateuscore2dollarskuscore2 (_ bv1 32))) (bvsge vuscore2dollarskuscore5 vdesuscore2dollarskuscore4)) (bvsle (bvsub (bvmul vuscore2dollarskuscore5 vuscore2dollarskuscore5) ?v_3) (bvmul ?v_0 (bvsub muscore2dollarskuscore5 zuscore2dollarskuscore5)))) (bvsge vuscore2dollarskuscore5 (_ bv0 32))) (bvsge duscore2dollarskuscore5 (_ bv0 32))) (bvsle (bvsub (bvmul v v) (bvmul d d)) (bvmul ?v_0 (bvsub m z)))) (bvsge v (_ bv0 32))) (bvsgt ep (_ bv0 32))) (bvsgt b (_ bv0 32))) (bvsgt amax (_ bv0 32))) (bvsge d (_ bv0 32))) (bvsle (bvsub (bvmul ?v_2 ?v_2) ?v_3) (bvmul ?v_0 (bvsub muscore2dollarskuscore5 (bvmul (bvsdiv (_ bv1 32) (_ bv2 32)) (bvadd (bvadd (bvmul ?v_1 (bvmul t4uscore0dollarskuscore0 t4uscore0dollarskuscore0)) (bvmul (bvmul (_ bv2 32) t4uscore0dollarskuscore0) vuscore2dollarskuscore5)) (bvmul (_ bv2 32) zuscore2dollarskuscore5))))))))))))
(check-sat)
(exit)
