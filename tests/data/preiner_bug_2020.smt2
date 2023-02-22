(set-logic BV)

(declare-const s (_ BitVec 1))
(declare-const t (_ BitVec 1))
(declare-const y (_ BitVec 1))
(declare-const z (_ BitVec 1))

(assert (= (bvor (bvnot y) z) #b1))

(assert
 (distinct
  (and
   (= (bvand z s) s)
   (= (bvor y s) s)
  )
  (exists ((x (_ BitVec 1)))
   (and
    (= (bvand z x) x)
    (= (bvor y x) x)
    (= x s)
   )
  )
 )
)

(check-sat)
(exit)