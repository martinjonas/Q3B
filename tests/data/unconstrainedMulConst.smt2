(set-info :smt-lib-version 2.6)
(set-logic BV)
(set-info :status sat)

(declare-const x (_ BitVec 32))

(assert (bvugt (bvmul #x00000002 x) #x00000004))
(check-sat)