(set-option :proof-transformation NONE)
(set-option :simplify-interpolants false)
(set-option :simplify-repeatedly false)
(set-option :produce-proofs true)
(set-option :print-terms-cse false)
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x () U)
(declare-fun y () U)
(declare-fun z () U)
(declare-fun f (U U) U)
(assert (= x y))
(assert (not (= (f z x) (f z y))))
(check-sat)
(get-proof)
(exit)
