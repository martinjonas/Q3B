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

 KeYmaera example: magnetic_field, node 118398 For more info see: @see "Sriram Sankaranarayanan, Henny B. Sima, Zohar Manna: Constructing invariants for hybrid systems"

Translated to BV by Mathias Preiner.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun stateuscore2dollarskuscore35 () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun ts17uscore0 () (_ BitVec 32))
(declare-fun a () (_ BitVec 32))
(declare-fun vyuscore2dollarskuscore27 () (_ BitVec 32))
(declare-fun t17uscore0dollarskuscore0 () (_ BitVec 32))
(declare-fun vy () (_ BitVec 32))
(declare-fun vx () (_ BitVec 32))
(declare-fun yuscore2dollarskuscore21 () (_ BitVec 32))
(declare-fun xuscore2dollarskuscore22 () (_ BitVec 32))
(declare-fun vxuscore2dollarskuscore26 () (_ BitVec 32))
(declare-fun buscore2dollarskuscore35 () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(declare-fun x () (_ BitVec 32))
(assert (not (exists ((ts17uscore0 (_ BitVec 32))) (let ((?v_0 (bvadd vyuscore2dollarskuscore27 (_ bv2 32)))) (=> (and (and (and (and (and (and (and (and (and (and (and (= ?v_0 (bvmul a (bvsub (bvadd (bvmul t17uscore0dollarskuscore0 vxuscore2dollarskuscore26) xuscore2dollarskuscore22) (_ bv2 32)))) (= (bvadd (bvmul vxuscore2dollarskuscore26 vxuscore2dollarskuscore26) (bvmul vyuscore2dollarskuscore27 vyuscore2dollarskuscore27)) (_ bv8 32))) (= (bvsub vxuscore2dollarskuscore26 (_ bv2 32)) (bvadd (bvmul (bvneg a) (bvadd (bvadd (bvmul t17uscore0dollarskuscore0 vyuscore2dollarskuscore27) yuscore2dollarskuscore21) (_ bv2 32))) (bvmul (bvmul (_ bv4 32) buscore2dollarskuscore35) (bvsub (_ bv1 32) a))))) (= stateuscore2dollarskuscore35 (_ bv1 32))) (=> (and (bvsle (_ bv0 32) ts17uscore0) (bvsle ts17uscore0 t17uscore0dollarskuscore0)) (bvsle vxuscore2dollarskuscore26 (_ bv0 32)))) (bvsge t17uscore0dollarskuscore0 (_ bv0 32))) (= stateuscore2dollarskuscore35 (_ bv2 32))) (= vx (_ bv2 32))) (= vy (bvneg (_ bv2 32)))) (= x (_ bv0 32))) (= y (_ bv0 32))) (= b (_ bv0 32))) (or (or (= stateuscore2dollarskuscore35 (_ bv0 32)) (= ?v_0 (bvmul a (bvsub xuscore2dollarskuscore22 (_ bv2 32))))) (= ?v_0 (_ bv0 32))))))))
(check-sat)
(exit)
