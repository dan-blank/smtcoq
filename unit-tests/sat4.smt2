(set-logic QF_UF)
(declare-fun a () Bool)
(assert (not (or a (not a))))
(check-sat)
(exit)
