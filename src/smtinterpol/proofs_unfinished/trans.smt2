(set-option :produce-proofs true)
(set-option :print-terms-cse false)
(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)


(assert (not (or (not
(and (or (not a) b) (or (not b) c)))
(or (not a) c))))

(check-sat)

(get-proof)