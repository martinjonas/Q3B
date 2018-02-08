(set-info :smt-lib-version 2.6)
(set-logic BV)
(set-info :source | Software ranking function synthesis problems.
These benchmarks stem from an evaluation described in Wintersteiger, Hamadi, de Moura: Efficiently solving quantified bit-vector formulas, FMSD 42(1), 2013.
The software models that were used are from a previous evaluation of termination proving tools described in Cook, Kroening, Ruemmer, Wintersteiger: Ranking Function Synthesis for Bit-Vector Relations, TACAS 2010.
 |)
(set-info :category "industrial")
(set-info :status unsat)
(assert (exists ((cpp__main__c__main__1__1__i_36_C (_ BitVec 32))) (forall ((termination__pre__0__cpp__main__c__main__1__1__i (_ BitVec 32))) (forall ((cpp__main__c__main__1__1__i_35_0 (_ BitVec 32))) (forall ((cpp__main__c__main__1__nCurrentIndex (_ BitVec 8))) (forall ((cpp__main__c__main__1__1__i (_ BitVec 32))) (=> (and (= termination__pre__0__cpp__main__c__main__1__1__i cpp__main__c__main__1__1__i_35_0) (not (= cpp__main__c__main__1__1__i_35_0 ((_ zero_extend 24) cpp__main__c__main__1__nCurrentIndex))) (= cpp__main__c__main__1__1__i (bvand (bvadd cpp__main__c__main__1__1__i_35_0 (_ bv1 32)) (_ bv31 32)))) (bvslt (bvmul ((_ sign_extend 32) cpp__main__c__main__1__1__i_36_C) ((_ sign_extend 32) cpp__main__c__main__1__1__i)) (bvmul ((_ sign_extend 32) cpp__main__c__main__1__1__i_36_C) ((_ sign_extend 32) termination__pre__0__cpp__main__c__main__1__1__i)))) ) ) ) ) ))
(check-sat)
(exit)
