(let ((.cse96 (to_real x))) (let ((.cse61 (to_real z)) (.cse90 (* 2450000000001.0 y)) (.cse93 (* 2730000000000.0 .cse96)) (.cse94 (* (- 2450000000001.0) y)) (.cse82 (* 2450000000000.0 y)) (.cse32 (* 2730000000001.0 .cse96)) (.cse33 (* (- 2450000000000.0) y))) (let ((.cse30 (<= (+ .cse32 .cse33 (- 10000000000.0)) 0.0)) (.cse14 (<= (+ (* (- 2730000000001.0) .cse96) .cse82 1.0) 0.0)) (.cse36 (<= (+ .cse93 .cse94 (- 9999999999.0)) 0.0)) (.cse25 (<= (+ (* (- 2730000000000.0) .cse96) .cse90) 0.0)) (.cse46 (to_real 2450000000000)) (.cse51 (to_real 1)) (.cse60 (to_real 0)) (.cse95 (- .cse61))) (let ((.cse53 (<= (+ y .cse95 (/ (- 119999999969.0) 4900000000000.0)) 0.0)) (.cse27 (* 910000000000.0 .cse96)) (.cse28 (* (- 816666666667.0) y)) (.cse54 (- y z)) (.cse52 (+ y .cse95)) (.cse58 (@rewrite (! (= .cse60 0.0) :canonicalSum))) (.cse49 (@rewrite (! (= .cse51 1.0) :canonicalSum))) (.cse45 (@rewrite (! (= .cse46 2450000000000.0) :canonicalSum))) (.cse26 (not .cse25)) (.cse37 (not .cse36)) (.cse15 (not .cse14)) (.cse31 (not .cse30))) (let ((.cse12 (! (let ((.cse89 (* 2730000000000 x)) (.cse86 (* 2450000000001 y)) (.cse81 (* 2730000000001 x)) (.cse79 (* 2450000000000 y))) (let ((.cse78 (- .cse81 .cse79)) (.cse85 (- .cse89 .cse86))) (let ((.cse64 (<= 0 .cse85)) (.cse68 (<= .cse85 9999999999)) (.cse71 (<= 1 .cse78)) (.cse75 (<= .cse78 10000000000))) (let ((.cse63 (and .cse64 .cse68 .cse71 .cse75))) (@eq (@asserted .cse63) (@trans (let ((.cse73 (+ .cse32 .cse33)) (.cse66 (+ .cse93 .cse94))) (let ((.cse65 (let ((.cse92 (to_real .cse89))) (let ((.cse91 (- .cse92 .cse90))) (@trans (@trans (@cong (@refl .cse85) (let ((.cse88 (to_real 2450000000001))) (let ((.cse87 (* .cse88 y))) (@trans (@rewrite (! (= .cse86 .cse87) :expandDef)) (@cong (@refl .cse87) (@rewrite (! (= .cse88 2450000000001.0) :canonicalSum))))))) (@rewrite (! (= (- .cse89 .cse90) .cse91) :expandDef))) (@trans (@cong (@refl .cse91) (@rewrite (! (= .cse92 .cse93) :canonicalSum))) (@rewrite (! (= (- .cse93 .cse90) .cse66) :canonicalSum))))))) (.cse72 (let ((.cse84 (to_real .cse81))) (let ((.cse83 (- .cse84 .cse82))) (@trans (@trans (@cong (@refl .cse78) (let ((.cse80 (* .cse46 y))) (@trans (@rewrite (! (= .cse79 .cse80) :expandDef)) (@cong (@refl .cse80) .cse45)))) (@rewrite (! (= (- .cse81 .cse82) .cse83) :expandDef))) (@trans (@cong (@refl .cse83) (@rewrite (! (= .cse84 .cse32) :canonicalSum))) (@rewrite (! (= (- .cse32 .cse82) .cse73) :canonicalSum)))))))) (@cong (@refl .cse63) (let ((.cse67 (<= .cse60 .cse66))) (@trans (@trans (@cong (@refl .cse64) .cse65) (@rewrite (! (= (<= 0 .cse66) .cse67) :expandDef))) (@trans (@cong (@refl .cse67) .cse58) (@rewrite (! (= (<= 0.0 .cse66) .cse25) :leqToLeq0))))) (let ((.cse70 (to_real 9999999999))) (let ((.cse69 (<= .cse66 .cse70))) (@trans (@trans (@cong (@refl .cse68) .cse65) (@rewrite (! (= (<= .cse66 9999999999) .cse69) :expandDef))) (@trans (@cong (@refl .cse69) (@rewrite (! (= .cse70 9999999999.0) :canonicalSum))) (@rewrite (! (= (<= .cse66 9999999999.0) .cse36) :leqToLeq0)))))) (let ((.cse74 (<= .cse51 .cse73))) (@trans (@trans (@cong (@refl .cse71) .cse72) (@rewrite (! (= (<= 1 .cse73) .cse74) :expandDef))) (@trans (@cong (@refl .cse74) .cse49) (@rewrite (! (= (<= 1.0 .cse73) .cse14) :leqToLeq0))))) (let ((.cse77 (to_real 10000000000))) (let ((.cse76 (<= .cse73 .cse77))) (@trans (@trans (@cong (@refl .cse75) .cse72) (@rewrite (! (= (<= .cse73 10000000000) .cse76) :expandDef))) (@trans (@cong (@refl .cse76) (@rewrite (! (= .cse77 10000000000.0) :canonicalSum))) (@rewrite (! (= (<= .cse73 10000000000.0) .cse30) :leqToLeq0))))))))) (@rewrite (! (= (and .cse25 .cse36 .cse14 .cse30) (not (or .cse26 .cse37 .cse15 .cse31))) :andToOr)))))))) :notOr)) (.cse40 (let ((.cse62 (- y .cse61))) (@trans (@rewrite (! (= .cse54 .cse62) :expandDef)) (@rewrite (! (= .cse62 .cse52) :canonicalSum))))) (.cse1 (! (< .cse52 0.0) :quotedLA)) (.cse16 (! (<= (+ (* 39 x) (* (- 35) z)) 0) :quotedLA)) (.cse34 (! (<= (+ .cse27 .cse28 (- 3333333333.0)) 0.0) :quotedLA)) (.cse38 (! .cse53 :quotedLA))) (let ((.cse5 (not .cse38)) (.cse6 (not .cse34)) (.cse3 (not .cse16)) (.cse10 (let ((.cse55 (not .cse1))) (! (@clause (let ((.cse59 (<= (+ (- y) .cse61) 0.0))) (@eq (let ((.cse56 (<= 0 .cse54))) (@eq (@asserted .cse56) (let ((.cse57 (<= .cse60 .cse52))) (@trans (@trans (@cong (@refl .cse56) .cse40) (@rewrite (! (= (<= 0 .cse52) .cse57) :expandDef))) (@trans (@cong (@refl .cse57) .cse58) (@rewrite (! (= (<= 0.0 .cse52) .cse59) :leqToLeq0))))))) (@rewrite (! (= .cse59 .cse55) :intern)))) (! .cse55 :input)) :pivot .cse55))) (.cse8 (! (@clause (@eq (let ((.cse42 (/ 60000000009 2450000000000)) (.cse47 (/ 1 100000000000))) (let ((.cse41 (- .cse42 .cse47))) (let ((.cse39 (<= .cse54 .cse41))) (@eq (@asserted .cse39) (@trans (@cong (@refl .cse39) .cse40 (@trans (@cong (@refl .cse41) (let ((.cse44 (to_real 60000000009))) (let ((.cse43 (/ .cse44 .cse46))) (@trans (@rewrite (! (= .cse42 .cse43) :expandDef)) (@trans (@cong (@refl .cse43) (@rewrite (! (= .cse44 60000000009.0) :canonicalSum)) .cse45) (@rewrite (! (= (/ 60000000009.0 2450000000000.0) (/ 60000000009.0 2450000000000.0)) :canonicalSum)))))) (let ((.cse50 (to_real 100000000000))) (let ((.cse48 (/ .cse51 .cse50))) (@trans (@rewrite (! (= .cse47 .cse48) :expandDef)) (@trans (@cong (@refl .cse48) .cse49 (@rewrite (! (= .cse50 100000000000.0) :canonicalSum))) (@rewrite (! (= (/ 1.0 100000000000.0) (/ 1.0 100000000000.0)) :canonicalSum))))))) (@rewrite (! (= (- (/ 60000000009.0 2450000000000.0) (/ 1.0 100000000000.0)) (/ 119999999969.0 4900000000000.0)) :canonicalSum)))) (@rewrite (! (= (<= .cse52 (/ 119999999969.0 4900000000000.0)) .cse53) :leqToLeq0))))))) (@rewrite (! (= .cse53 .cse38) :intern))) (! .cse38 :input)) :pivot .cse38)) (.cse9 (! (@clause (@eq (let ((.cse35 (not .cse37))) (@eq (@split .cse12 .cse35) (@rewrite (! (= .cse35 .cse36) :notSimp)))) (@rewrite (! (= .cse36 .cse34) :intern))) (! .cse34 :input)) :pivot .cse34)) (.cse4 (! (<= (+ x (- z) 1) 0) :quotedLA))) (let ((.cse0 (! (<= x 0) :quotedLA)) (.cse2 (! (< (+ .cse32 .cse33 (- 1.0)) 0.0) :quotedLA)) (.cse7 (let ((.cse17 (not .cse4))) (! (let ((.cse20 (! (<= (+ (* 10 x) (* (- 9) z) 1) 0) :quotedLA))) (let ((.cse19 (not .cse20)) (.cse18 (! .cse30 :quotedLA))) (@res (@lemma (! (or (not .cse18) .cse19 .cse5 .cse16) :LA (1 35 2450000000000 (- 70000000009)))) (! (@lemma (! (or .cse20 .cse17 .cse5 .cse6) :LA ((- 93333333333) 23333333330 816666666667 1))) :pivot .cse20) (! (let ((.cse21 (! (< (+ .cse27 .cse28) 0.0) :quotedLA))) (let ((.cse22 (let ((.cse23 (not .cse21))) (! (@clause (@eq (let ((.cse24 (not .cse26))) (@eq (@split .cse12 .cse24) (@rewrite (! (= .cse24 .cse25) :notSimp)))) (@rewrite (! (= .cse25 .cse23) :intern))) (! .cse23 :input)) :pivot .cse23)))) (@res (@lemma (! (or .cse20 .cse17 .cse1 .cse21 .cse3) :LA ((- 816666666667) 204166666670 (- 816666666667) (- 1) 227500000000))) (! (@res (@lemma (! (or .cse19 .cse1 .cse21 .cse3) :LA (13 (- 816666666667) (- 1) 23333333330))) .cse10 .cse22) :pivot .cse19) .cse10 .cse22))) :pivot .cse3) (! (@clause (@eq (let ((.cse29 (not .cse31))) (@eq (@split .cse12 .cse29) (@rewrite (! (= .cse29 .cse30) :notSimp)))) (@rewrite (! (= .cse30 .cse18) :intern))) (! .cse18 :input)) :pivot .cse18) .cse8 .cse9))) :pivot .cse17)))) (@res (@lemma (! (or (not .cse0) .cse1 .cse2 .cse3) :LA (1 (- 2450000000000) (- 1) 70000000000))) (! (@res (@lemma (! (or .cse0 .cse4 .cse5 .cse6) :LA ((- 93333333333) (- 816666666667) 816666666667 1))) .cse7 .cse8 .cse9) :pivot .cse0) .cse10 (let ((.cse11 (not .cse2))) (! (@clause (@eq (let ((.cse13 (not .cse15))) (@eq (@split .cse12 .cse13) (@rewrite (! (= .cse13 .cse14) :notSimp)))) (@rewrite (! (= .cse14 .cse11) :intern))) (! .cse11 :input)) :pivot .cse11)) (! (@res (@lemma (! (or .cse4 .cse5 .cse16 .cse6) :LA ((- 13) 3266666666668 (- 93333333333) 4))) .cse7 .cse8 .cse9) :pivot .cse16)))))))))