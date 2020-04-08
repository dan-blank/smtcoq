(set-option :produce-proofs true)
(set-option :print-terms-cse false)
(set-logic QF_UF)
(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (not x))
(assert y)
(assert (and x y))
(check-sat)
(get-proof)
