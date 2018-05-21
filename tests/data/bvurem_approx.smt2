(set-info :smt-lib-version 2.6)
(set-logic BV)

(assert (forall ((x (_ BitVec 32)))
  (bvsle (ite (= x #x00000000) #x8b4feb20 (bvurem #x8b4feb20 x)) #x45a421af))
)

(check-sat)
(exit)
