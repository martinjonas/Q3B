(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))

(assert (= (ite (= (bvmul x y) x)
		       #b0
		       #b1)
	   (ite (= (bvmul x y) y)
		       #b1
		       #b0)))
(check-sat)
