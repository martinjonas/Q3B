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

 KeYmaera example: intersection-example-onelane.proof, node 1469 For more info see: @see "Sarah M. Loos and Andre Platzer. Safe intersections: At the crossing of hybrid systems and verification. In Kyongsu Yi, editor, 14th International IEEE Conference on Intelligent Transportation Systems, ITSC 2011, Washington, DC, USA, Proceedings. 2011."

Translated to BV by Mathias Preiner.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun xI () (_ BitVec 32))
(declare-fun xuscore2dollarskuscore0 () (_ BitVec 32))
(declare-fun ts0uscore0 () (_ BitVec 32))
(declare-fun vuscore2dollarskuscore0 () (_ BitVec 32))
(declare-fun A () (_ BitVec 32))
(declare-fun B () (_ BitVec 32))
(declare-fun t1uscore0dollarskuscore0 () (_ BitVec 32))
(declare-fun I1 () (_ BitVec 32))
(declare-fun v () (_ BitVec 32))
(declare-fun V () (_ BitVec 32))
(declare-fun ep () (_ BitVec 32))
(declare-fun I1uscore2dollarskuscore0 () (_ BitVec 32))
(declare-fun x () (_ BitVec 32))
(assert (not (exists ((ts0uscore0 (_ BitVec 32))) (let ((?v_0 (bvadd (bvmul A ts0uscore0) vuscore2dollarskuscore0))) (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (=> (and (bvsle (_ bv0 32) ts0uscore0) (bvsle ts0uscore0 t1uscore0dollarskuscore0)) (and (and (bvsge ?v_0 (_ bv0 32)) (bvsle ?v_0 V)) (bvsle ts0uscore0 ep))) (bvsge t1uscore0dollarskuscore0 (_ bv0 32))) (= xI xuscore2dollarskuscore0)) (= I1uscore2dollarskuscore0 (_ bv0 32))) (bvsge vuscore2dollarskuscore0 (_ bv0 32))) (bvsle vuscore2dollarskuscore0 V)) (= I1 (_ bv2 32))) (bvslt xI x)) (bvsgt B (_ bv0 32))) (bvsge v (_ bv0 32))) (bvsle v V)) (bvsge A (_ bv0 32))) (bvsgt V (_ bv0 32))) (bvsgt ep (_ bv0 32))) (or (= I1uscore2dollarskuscore0 (_ bv2 32)) (bvsge (bvadd (bvmul A t1uscore0dollarskuscore0) vuscore2dollarskuscore0) (_ bv0 32))))))))
(check-sat)
(exit)
