(set-option :produce-proofs true)
(set-option :print-terms-cse false)
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x () U)
(declare-fun y () U)
(declare-fun z () U)
(declare-fun f (U) U)
(assert (not (= (f x) (f z))))
(assert (= x y))
(assert (= y z))
(check-sat)
(get-proof)
(exit)
