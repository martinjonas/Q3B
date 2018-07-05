(set-logic QF_BV)
(set-info :source |
Number of leading zeros nlz(x) algorithm, working both ends at the same time
From the book "Hacker's delight" by Henry S. Warren, Jr., page 79
We cross-check it with an obvious method of counting leading zeros:

s = 0;
for (i = BW - 1; i >= 0; i--)
  if (x & (1 << i))
    break;
  else
    s++;

Contributed by Robert Brummayer (robert.brummayer@gmail.com)
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun result1init () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
(assert (let ((?v_9 (ite (= x (_ bv0 8)) (_ bv1 1) (_ bv0 1))) (?v_8 (ite (bvslt x (_ bv0 8)) (_ bv1 1) (_ bv0 1)))) (let ((?v_13 (ite (= (_ bv1 1) (_ bv0 1)) result1init (ite (= (_ bv1 1) ?v_8) (_ bv0 8) (ite (= (_ bv1 1) ?v_9) (bvsub (_ bv8 8) (_ bv0 8)) result1init)))) (?v_7 (bvor (_ bv0 1) (bvor ?v_8 ?v_9))) (?v_12 (bvadd (_ bv0 8) (_ bv1 8))) (?v_0 ((_ zero_extend 5) (_ bv1 3)))) (let ((?v_1 (bvshl x ?v_0)) (?v_2 (bvashr x ?v_0))) (let ((?v_11 (ite (= ?v_2 (_ bv0 8)) (_ bv1 1) (_ bv0 1))) (?v_10 (ite (bvslt ?v_1 (_ bv0 8)) (_ bv1 1) (_ bv0 1)))) (let ((?v_17 (ite (= (_ bv1 1) ?v_7) ?v_13 (ite (= (_ bv1 1) ?v_10) ?v_12 (ite (= (_ bv1 1) ?v_11) (bvsub (_ bv8 8) ?v_12) ?v_13)))) (?v_6 (bvor ?v_7 (bvor ?v_10 ?v_11))) (?v_16 (bvadd ?v_12 (_ bv1 8))) (?v_3 (bvshl ?v_1 ?v_0)) (?v_4 (bvashr ?v_2 ?v_0))) (let ((?v_15 (ite (= ?v_4 (_ bv0 8)) (_ bv1 1) (_ bv0 1))) (?v_14 (ite (bvslt ?v_3 (_ bv0 8)) (_ bv1 1) (_ bv0 1)))) (let ((?v_21 (ite (= (_ bv1 1) ?v_6) ?v_17 (ite (= (_ bv1 1) ?v_14) ?v_16 (ite (= (_ bv1 1) ?v_15) (bvsub (_ bv8 8) ?v_16) ?v_17)))) (?v_5 (bvor ?v_6 (bvor ?v_14 ?v_15))) (?v_20 (bvadd ?v_16 (_ bv1 8))) (?v_22 (bvshl ?v_3 ?v_0)) (?v_23 (bvashr ?v_4 ?v_0))) (let ((?v_19 (ite (= ?v_23 (_ bv0 8)) (_ bv1 1) (_ bv0 1))) (?v_18 (ite (bvslt ?v_22 (_ bv0 8)) (_ bv1 1) (_ bv0 1)))) (let ((?v_25 (ite (= (_ bv1 1) ?v_5) ?v_21 (ite (= (_ bv1 1) ?v_18) ?v_20 (ite (= (_ bv1 1) ?v_19) (bvsub (_ bv8 8) ?v_20) ?v_21)))) (?v_24 (bvadd ?v_20 (_ bv1 8))) (?v_39 (ite (= (bvand x (bvshl (_ bv1 8) ((_ zero_extend 5) (_ bv7 3)))) (_ bv0 8)) (_ bv1 1) (_ bv0 1)))) (let ((?v_40 (bvor (_ bv0 1) (bvnot ?v_39)))) (let ((?v_41 (ite (= (_ bv1 1) ?v_39) (ite (= (_ bv1 1) ?v_40) (_ bv0 8) ?v_12) (_ bv0 8))) (?v_37 (ite (= (bvand x (bvshl (_ bv1 8) ((_ zero_extend 5) (_ bv6 3)))) (_ bv0 8)) (_ bv1 1) (_ bv0 1)))) (let ((?v_38 (bvor ?v_40 (bvnot ?v_37)))) (let ((?v_42 (ite (= (_ bv1 1) ?v_37) (ite (= (_ bv1 1) ?v_38) ?v_41 (bvadd ?v_41 (_ bv1 8))) ?v_41)) (?v_35 (ite (= (bvand x (bvshl (_ bv1 8) ((_ zero_extend 5) (_ bv5 3)))) (_ bv0 8)) (_ bv1 1) (_ bv0 1)))) (let ((?v_36 (bvor ?v_38 (bvnot ?v_35)))) (let ((?v_43 (ite (= (_ bv1 1) ?v_35) (ite (= (_ bv1 1) ?v_36) ?v_42 (bvadd ?v_42 (_ bv1 8))) ?v_42)) (?v_33 (ite (= (bvand x (bvshl (_ bv1 8) ((_ zero_extend 5) (_ bv4 3)))) (_ bv0 8)) (_ bv1 1) (_ bv0 1)))) (let ((?v_34 (bvor ?v_36 (bvnot ?v_33)))) (let ((?v_44 (ite (= (_ bv1 1) ?v_33) (ite (= (_ bv1 1) ?v_34) ?v_43 (bvadd ?v_43 (_ bv1 8))) ?v_43)) (?v_31 (ite (= (bvand x (bvshl (_ bv1 8) ((_ zero_extend 5) (_ bv3 3)))) (_ bv0 8)) (_ bv1 1) (_ bv0 1)))) (let ((?v_32 (bvor ?v_34 (bvnot ?v_31)))) (let ((?v_45 (ite (= (_ bv1 1) ?v_31) (ite (= (_ bv1 1) ?v_32) ?v_44 (bvadd ?v_44 (_ bv1 8))) ?v_44)) (?v_29 (ite (= (bvand x (bvshl (_ bv1 8) ((_ zero_extend 5) (_ bv2 3)))) (_ bv0 8)) (_ bv1 1) (_ bv0 1)))) (let ((?v_30 (bvor ?v_32 (bvnot ?v_29)))) (let ((?v_46 (ite (= (_ bv1 1) ?v_29) (ite (= (_ bv1 1) ?v_30) ?v_45 (bvadd ?v_45 (_ bv1 8))) ?v_45)) (?v_27 (ite (= (bvand x (bvshl (_ bv1 8) ?v_0)) (_ bv0 8)) (_ bv1 1) (_ bv0 1)))) (let ((?v_28 (bvor ?v_30 (bvnot ?v_27)))) (let ((?v_47 (ite (= (_ bv1 1) ?v_27) (ite (= (_ bv1 1) ?v_28) ?v_46 (bvadd ?v_46 (_ bv1 8))) ?v_46)) (?v_26 (ite (= (bvand x (bvshl (_ bv1 8) ((_ zero_extend 5) (_ bv0 3)))) (_ bv0 8)) (_ bv1 1) (_ bv0 1)))) (not (= (bvnot (ite (= (ite (= (_ bv1 1) (bvor ?v_5 (bvor ?v_18 ?v_19))) ?v_25 (ite (= (_ bv1 1) (ite (bvslt (bvshl ?v_22 ?v_0) (_ bv0 8)) (_ bv1 1) (_ bv0 1))) ?v_24 (ite (= (_ bv1 1) (ite (= (bvashr ?v_23 ?v_0) (_ bv0 8)) (_ bv1 1) (_ bv0 1))) (bvsub (_ bv8 8) ?v_24) ?v_25))) (ite (= (_ bv1 1) ?v_26) (ite (= (_ bv1 1) (bvor ?v_28 (bvnot ?v_26))) ?v_47 (bvadd ?v_47 (_ bv1 8))) ?v_47)) (_ bv1 1) (_ bv0 1))) (_ bv0 1)))))))))))))))))))))))))))
(check-sat)
(exit)
