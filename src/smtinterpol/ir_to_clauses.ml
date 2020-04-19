open Ir
open SmtAtom
open SmtForm
open SmtTrace
open SmtCertif

(**
   Final step in the translation, where the intermediate representation is translated to a certificate.
*)

(** A table to cache translated clause proofs. *)
let clause_proof_table : (Ir.clause_proof, SmtAtom.Form.t clause) Hashtbl.t = Hashtbl.create 17
(** A table to cache translated equality proofs. *)
let equality_proof_table : (Ir.equality_proof, SmtAtom.Form.t clause) Hashtbl.t = Hashtbl.create 17
(** A table to cache translated formula proofs. *)
let formula_proof_table : (Ir.formula_proof, SmtAtom.Form.t clause) Hashtbl.t = Hashtbl.create 17

(** List of clauses that have the SmtCertif.clause_kind Root. *)
let roots : SmtAtom.Form.t clause list ref = ref []
(** List of clauses that do not have the SmtCertif.clause_kind Root. *)
let clauses : SmtAtom.Form.t clause list ref = ref []


(** Debugging function, print the id of the clause that was generated last along with a string argument. *)
(* let deb message = () *)
let deb message =
  let print_latest_clause () =
    let get_last_id ls = if (0 != List.length ls) then (List.hd (List.rev ls)).id else (-1) in
    let last = max (get_last_id !clauses) (get_last_id !roots) in
    Printf.printf " last clause: %i" last in
  Printf.printf "\n §§§ %s" message;
  print_latest_clause ()

(** Helper to get the first clause of a certificate. *)
let rec get_first c =
  match c.prev with
  | Some p -> get_first p
  | None -> c

(** Helper to get the last clause of a certificate. *)
let rec get_last c =
  match c.next with
  | Some n -> get_last n
  | None -> c

(** Given a formula with the constructor Fapp and an integer n, return the nth argument to Fapp. *)
let get_subformula form index =
  let formula = Form.pform form in
  match formula with
  | Fapp (_, ar) -> Array.get ar index

(** Check whether a formula is a boolean equality as opposed to an atomic equality. *)
let isBooleanEqualityInLemma f = false

(** Check whether a formula is one that applies an operator to subformulas. *)
let isLogicalOperatorFormula f =
  let form_pos = Form.pform f in
  match form_pos with
  | Fapp (_, _) -> true 
  | _           -> false

(** Add the two clause lists roots and clauses together by linking them together in the correct order and adjusting the clause.pos value of the root clauses. *)
let add_roots_and_non_roots () =
  let rec adjust_root_positions c pos =
    let new_pos = pos + 1 in
    if (isRoot c.kind) then c.pos <- Some (pos + 1);
    match c.next with
    | Some n -> adjust_root_positions n new_pos
    | None -> ()in
  clauses := List.append !roots !clauses;
  let (head_c :: tail_cs) = !clauses in
  let _ = List.fold_left (fun l r -> link l r; r) head_c tail_cs in
  adjust_root_positions (List.hd !clauses) (-1)

(** Wrapper to store a newly created clause with kind Other into clauses. *)
let lmkOther rule value =
  let clause = mkOther rule value in
  clauses := List.append !clauses [clause];
  clause


(** Wrapper to store a newly created clause with kind Res into clauses. *)
let lmkRes r l tl =
  let clause = mkRes r l tl in
  clauses := List.append !clauses [clause];
  clause

(** Wrapper to store a newly created clause with kind Res and a value into clauses. *)
let mkResV c1 c2 tl v = mk_scertif (Res { rc1 = c1; rc2 = c2; rtail = tl }) v
let lmkResV r l tl v =
  let clause = mkResV r l tl v in
  clauses := List.append !clauses [clause];
  clause

(** Wrapper to store a newly created clause with kind Root and a value into roots. *)
let lmkRootV v =
  let clause = mkRootV v in
  roots := List.append !roots [clause];
  clause

(** Two convenience functions to build clauses of kind Other with either BuildDef or BuildDef2. *)
let aux_bd1 f = lmkOther (BuildDef f) None
let aux_bd2 f = lmkOther (BuildDef2 f) None

(** Given two formulas, build a new formula that is the equality between the two input formulas. *)
let mkEquality f g =
  let form_pos = Fapp (Fiff, Array.of_list [f; g]) in
  Form.get VeritSyntax.rf form_pos

(** Check whether a given formula is of kind (= x true). The symetric case is not yet accounted for. *)
let isEqualToTrueFormula f =
  let isTrueFormula fapp =
    match fapp with
    | Fapp (Ftrue, _) -> true
    | _ -> false in
  match Form.pform (get_subformula f 1) with
  | Fapp (Fiff, far) -> isTrueFormula (Form.pform (Array.get far 1))
  | _ -> false

(**
   Given a formula of kind (= x (= x true)), return the clause { (= x (= x true)) }.
   The symetric cases are not covered yet.
*)
let create_intern_true_eq iixt =
  deb "create_intern_true_eq BEG";
  let ixt = get_subformula iixt 1 in
  let iixt_x_nixt = aux_bd2 iixt in
  let ixt_nx_ntrue = aux_bd1 ixt in
  let iixt_ixt_ntrue = lmkRes iixt_x_nixt ixt_nx_ntrue [] in
  let iixt_nx_nixt = aux_bd1 iixt in
  let nixt_x_ntrue = aux_bd1 (Form.neg ixt) in
  let iixt_nixt_ntrue = lmkRes iixt_nx_nixt nixt_x_ntrue [] in
  let iixt_ntrue = lmkRes iixt_ixt_ntrue iixt_nixt_ntrue [] in
  let cl_true = lmkOther True None in
  let iixt_c = lmkResV iixt_ntrue cl_true [] (Some [iixt]) in
  deb "create_intern_true_eq END";
  iixt_c

(**
   Given a clause, a rewrite rule and a rewrite formula, produce a certificate whose last clause proves the rewritten clause.
   So far, this only works for rewriting on the formula level, no on the atomic level.

   Examples:
   handle_rewrite_bool _ Rewrite_eqToXor (= (= x y) (not (xor x y)))
       => { (= (= x y) (not (xor x y))) }
   handle_rewrite_bool { (not (not x)) } Rewrite_notSimp _
       => { x }
*)
let handle_rewrite_bool hackForRewrite_c rewrite_rule rewrite_f =
  let left_f = get_subformula rewrite_f 0 in
  let right_f = get_subformula rewrite_f 1 in
  match rewrite_rule with
   | Rewrite_eqToXor ->
     let base_pos = lmkOther (BuildDef2 rewrite_f) None in
     let base_neg = lmkOther (BuildDef rewrite_f) None in
     (* Resolve to (iff a b) x (not y) *)
     let choose_nx_y_1 = lmkOther (BuildDef (Form.neg left_f)) None in
     let choose_nx_y_2 = lmkOther (BuildDef (Form.neg right_f)) None in
     let res_nx_y = lmkRes base_pos choose_nx_y_1 [choose_nx_y_2] in
     (* Resolve to (iff a b) x y *)
     let choose_x_y_1 = lmkOther (BuildDef2 left_f) None in
     let choose_x_y_2 = lmkOther (BuildDef right_f) None in
     let res_x_y = lmkRes base_neg choose_x_y_1 [choose_x_y_2] in
     (* Resolve to (iff a b) x *)
     let res_x = lmkRes res_x_y res_nx_y [] in
     (* Resolve to (iff a b) (not x) (not y) *)
     let choose_x_ny_1 = lmkOther (BuildDef left_f) None in
     let choose_x_ny_2 = lmkOther (BuildDef2 right_f) None in
     let res_x_ny = lmkRes base_neg choose_x_ny_1 [choose_x_ny_2] in
     (* Resolve to (iff a b) (not x) y *)
     let choose_nx_ny_1 = lmkOther (BuildDef2 (Form.neg left_f)) None in
     let choose_nx_ny_2 = lmkOther (BuildDef2 (Form.neg right_f)) None in
     let res_nx_ny = lmkRes base_pos choose_nx_ny_1 [choose_nx_ny_2] in
     (* Resolve to (iff a b) (not x) *)
     let res_nx = lmkRes res_x_ny res_nx_ny [] in
     let res = lmkResV res_x res_nx [] (Some [rewrite_f]) in
     res
   | Rewrite_andToOr ->
     let base_1 = lmkOther (BuildDef2 rewrite_f) None in
     (* Resolve to (iff a b) x *)
     let prod_and_1 = lmkOther (BuildProj (left_f, 0)) None in
     let prod_or_1 = lmkOther (BuildProj (right_f, 0)) None in
     let res_x = lmkRes base_1 prod_and_1 [prod_or_1] in
     (* Resolve to (iff a b) y *)
     let prod_and_2 = lmkOther (BuildProj (left_f, 1)) None in
     let prod_or_2 = lmkOther (BuildProj (right_f, 1)) None in
     let res_y = lmkRes base_1 prod_and_2 [prod_or_2] in
     (* Resolve to (iff a b) (not x) (not y) *)
     let base2 = lmkOther (BuildDef rewrite_f) None in
     let sum_and = lmkOther (BuildDef left_f) None in
     let sum_or = lmkOther (BuildDef right_f) None in
     let res_nx_ny = lmkRes base2 sum_and [sum_or] in
     (* Resolve to (iff a b) *)
     let res = lmkResV res_nx_ny res_x [res_y] (Some [rewrite_f]) in
     res
   | Rewrite_notSimp ->
     let simpl1 = lmkOther (ImmFlatten (hackForRewrite_c, right_f)) hackForRewrite_c.value in
     simpl1
   | Rewrite_intern ->
     if (isEqualToTrueFormula rewrite_f)
     then (create_intern_true_eq rewrite_f) 
     else (
       deb "Rewrite_intern true eq BEG";
     let formula_l = get_subformula rewrite_f 0 in
     let formula_r = get_subformula rewrite_f 1 in
     let refl_formula = mkEquality formula_l formula_r in
     let na = aux_bd1 refl_formula in
     let a = aux_bd2 refl_formula in
     let refl_cl = lmkResV na a [] (Some [refl_formula]) in
     deb "Rewrite_intern true eq END";
     refl_cl)

(**
   Given a clause, a rewrite rule and a rewrite formula, produce a certificate whose last clause proves the rewritten clause.
   This wrapper makes sure that the rewrite happens on the formula level. Rewrite on the atomic level are not supported.

   hackForRewrite_c is a clause that was proven before and that is potentially being rewritten by the current rewrite. This can be necessary if the SMTCoq construct for the rewrite needs a clause as an argument.
*)
let handle_rewrite hackForRewrite_c rewrite_rule rewrite_f =
  if (isLogicalOperatorFormula rewrite_f)
  then handle_rewrite_bool hackForRewrite_c rewrite_rule rewrite_f
  else assert false 


(** Create the congruence clause for the logical operator 'not'.*)
let create_congruent_not x y =
  deb "create_congruent_clause_not BEG";
  let inxny = mkEquality (Form.neg x) (Form.neg y) in
  let nixy = Form.neg (mkEquality x y) in
  let inxny_x_y = aux_bd1 inxny in
  let nixy_x_ny = aux_bd1 nixy in
  let inxny_nixy_x = lmkRes inxny_x_y nixy_x_ny [] in
  let inxny_nx_ny = aux_bd2 inxny in
  let nixy_nx_y = aux_bd2 nixy in
  let inxny_nixy_nx = lmkRes inxny_nx_ny nixy_nx_y [] in
  let res = lmkResV inxny_nixy_x inxny_nixy_nx [] (Some [inxny; nixy]) in
  deb "create_congruent_clause_not END";
  res

(** Given a congruence in the form of an equality and a list of negated equalities, return a clause that proves that congruence.  *)
let create_congruent f equalities =
  match f, equalities with
  (* Special case: negation is not represented as an Fop in SMTCoq, so we have to have to check for that case in a different way. *)
  | f, [e] when (Form.is_neg f) -> create_congruent_not (Form.neg f) e
  | _ -> assert false

(**
   Given a transitivity in the form of three formulas a,b and c, return a clause that proves that transitivity.

   This derivation will produce potentially problematic clauses when a, b and c are not distinct:
   Consider the clause 'niab_a_nb': If a and b were equal, then niab_a_nb would evaluate to true (since then nb = na and { (na a) } == { true }.

   Example:
   create_transitive  x y z => { (= x z) (not (= x y)) (not (= y z)) }
*)
let create_transitive a b c =
  deb "create_transitive  BEG";
  assert (not (a == b));
  assert (not (b == c));
  assert (not (a == c));
  let niab = Form.neg (mkEquality a b) in
  let nibc = Form.neg (mkEquality b c) in
  let iac = mkEquality a c in
  let niab_a_nb = aux_bd1 niab in
  let nibc_b_nc = aux_bd2 nibc in
  let niab_nibc_a_nc = lmkRes niab_a_nb nibc_b_nc [] in
  let iac_a_c = aux_bd2 iac in
  let niab_nibc_iac_a = lmkRes niab_nibc_a_nc iac_a_c [] in
  let niab_na_b = aux_bd2 niab in
  let nibc_nb_c = aux_bd2 nibc in
  let niab_nibc_na_c = lmkRes niab_na_b nibc_nb_c [] in
  let iac_na_nc = aux_bd1 iac in
  let niab_nibc_iac_na = lmkRes niab_nibc_na_c iac_na_nc [] in
  let res = lmkResV niab_nibc_iac_a niab_nibc_iac_na [] (Some [iac; niab; nibc]) in
  deb "create_transitive  END";
  res

(**
   Walk an equality proof and return the equivalent certificate.
   The purpose of hackForRewrite_c is explained in the comment of 'handle_rewrite'.
*)
let rec walk_equality_proof ep hackForRewrite_c =
  if Hashtbl.mem equality_proof_table ep
  then Hashtbl.find equality_proof_table ep
  else
    let c =
    (match ep with
      | Rewrite (form, rewrite_rule) ->
        deb "Rewrite BEG";
        let c = handle_rewrite hackForRewrite_c rewrite_rule form in
        deb "Rewrite END";
        c
      | Congruence (lep, rep) ->
        deb "Congruence BEG";
        let c1 = walk_equality_proof lep hackForRewrite_c in
        let c2 = walk_equality_proof rep hackForRewrite_c in
        let (Some [form1]) = (get_last c1).value in
        let (Some [form2]) = (get_last c2).value in
        let sub1_form = get_subformula form1 1 in
        let sub2_form = get_subformula form2 1 in
        let cong_cl_raw = create_congruent sub1_form [sub2_form] in
        let (Some [cong_formula; _]) = (get_last cong_cl_raw).value in
        let cong_cl = lmkResV c2 cong_cl_raw [] (Some [cong_formula]) in
        let cong_sub0 = get_subformula cong_formula 0 in
        let cong_sub1 = get_subformula cong_formula 1 in
        let l_sub0 = get_subformula form1 0 in
        if ((Form.equal cong_sub0 cong_sub1) && (Form.equal cong_sub0 l_sub0))
        then (
          let trans_cl_raw = create_transitive  l_sub0 cong_sub0 cong_sub1 in
          let res1 = lmkRes trans_cl_raw c1 [] in
          let res = lmkRes res1 cong_cl [] in
          deb "Congruence END";
          res)
        else (
          let res = cong_cl in
          deb "Congruence END";
          res)
      | Transitivity (lep, rep) ->
        deb "Transitivity BEG";
        let c1 = walk_equality_proof lep hackForRewrite_c in
        let c2 = walk_equality_proof rep hackForRewrite_c in
        let (Some [form1]) = (get_last c1).value in
        let (Some [form2]) = (get_last c2).value in
        let a = get_subformula form1 0 in
        let (b : SmtAtom.Form.t) = get_subformula form1 1 in
        let (c : SmtAtom.Form.t) = get_subformula form2 1 in
        let eq_to_show = mkEquality a c in
        let first_neg = Form.neg (mkEquality a b) in
        let second_neg = Form.neg (mkEquality b c) in
        let first_neg_clause = lmkOther (EqTr (first_neg, [])) None in
        let second_neg_clause = lmkOther (EqTr (second_neg, [])) None in
        let trans = lmkOther (EqTr (eq_to_show, [first_neg; second_neg])) None  in
        let res = lmkResV trans first_neg_clause [second_neg_clause] (Some [eq_to_show]) in
        deb "Transitivity END";
        res
      | Reflexivity form ->
        deb "Reflexivity BEG";
        let refl_formula = mkEquality form form in
        let na = aux_bd1 refl_formula in
        let a = aux_bd2 refl_formula in
        let refl_cl = lmkResV na a [] (Some [refl_formula]) in
        deb "Reflexivity END";
        refl_cl) in
    Hashtbl.add equality_proof_table ep c;
    c

(**
   Given a unit clause with a formula to be split, a split rule and a formula that should result after the split, return a clause that proves that the split formula.

   There is a small mismatch between how splitting works in SMTInterpol and SMTCoq: The former just mentions the split rule and the resulting formula, the later needs the clause with the formula to be split and optionally a index that tells where the split should happen.
*)
let handle_split unsplit_clause split_rule form =
  let deduce_split_index heap_form needle_form =
    let first_sub_form = get_subformula heap_form 0 in
    if Form.pform first_sub_form = Form.pform needle_form then 0 else 1 in
  match split_rule with
  | Split_xor_plus_1 | Split_xor_minus_1 ->
    let split_clause = lmkOther (ImmBuildDef unsplit_clause) None in
    split_clause
  | Split_xor_plus_2 | Split_xor_minus_2 -> 
    let split_clause = lmkOther (ImmBuildDef2 unsplit_clause) None in
    split_clause
  | Split_notOr ->
    let Some [unsplit_formula] = unsplit_clause.value in
    let index = deduce_split_index unsplit_formula form in
    let split_clause = lmkOther (ImmBuildProj (unsplit_clause, index)) None in
    split_clause

(** Walk an formula proof and return the equivalent certificate. *)
let rec walk_formula_proof fp =
  if Hashtbl.mem formula_proof_table fp
  then Hashtbl.find formula_proof_table fp
  else let last_c = (match fp with
      | Asserted (f) ->
        (* deb "Asserted BEG"; *)
        let c = lmkRootV [f] in
        (* deb "Asserted END"; *)
        c
      | Equality (fp, ep) ->
        (* deb "Equality BEG"; *)
        let x_c = walk_formula_proof fp in
        let ixy_c = walk_equality_proof ep x_c in
        let c = (match ep with
            | Rewrite (_, Rewrite_notSimp) -> ixy_c
            | _ ->
              let nx_y_c = lmkOther (ImmBuildDef2 ixy_c) ixy_c.value in (* Check: ixy_c.value is not the correct value! *)
              let Some [form] = ixy_c.value in
              let y_c = lmkResV nx_y_c x_c [] (Some [get_subformula form 1]) in
              y_c) in
        (* deb "Equality END"; *)
        c
      | Split (fp, f, split_rule) ->
        (* deb "Split BEG"; *)
        let c1 = walk_formula_proof fp in
        let c2 = handle_split c1 split_rule f in
        (* deb "Split END"; *)
        c2) in
    Hashtbl.add formula_proof_table fp last_c;
    last_c


(**
   Make sure that SMTInterpol gave the correct inequalities for a transitivity or congruence and wrap them into the form that SMTCoq requires.
   This is only intended for atomic congruence/transivity.
   SMTInterpol does not give trivial inequalities, i.e. (not (= x x)). This might be problematic, maybe those inequalities have to be generated by oneself.

   Example:
   (= (a x) (a y)) (not (= x y)) => one-element-array of Some (not (= x y))
     where
       a is some atomic operator
       = is some atomic equality
*)
let generate_subpath form negated_equality_forms =
  let wrap_equality_formula_in_option hatom1 hatom2 hatoms =
    let do_hatoms_appear_in_atomic_binary_operation atom hatom1 hatom2 =
      match atom with
      | Abop (_, x, y) when x == hatom1 && y == hatom2 -> true
      | Abop (_, x, y) when x == hatom2 && y == hatom1 -> true
      | _ -> false in
    let matching_hatoms = List.find_all (fun gpform ->
        let Fatom hatom = Form.pform gpform in
        let atom = Atom.atom hatom in
        do_hatoms_appear_in_atomic_binary_operation atom hatom1 hatom2) hatoms in
    match matching_hatoms with
    | [inequalitiy_hatom] -> Some inequalitiy_hatom
    | _ -> None in
  let gpform = Form.pform form in
  let Fatom (atom) = gpform in
  let Abop(_, left_atom, right_atom) = Atom.atom atom in
  let Aapp (_, hatoms1) = Atom.atom left_atom in
  let Aapp (_, hatoms2) = Atom.atom right_atom in
  Array.map2 (fun x y -> wrap_equality_formula_in_option x y negated_equality_forms) hatoms1 hatoms2 

(** Given a lemma, produce a equivalent clause. *)
let handle_lemma = function
  | L_CC_Congruence (form, negated_equality_forms)->
    if (isBooleanEqualityInLemma form)
    then (assert false)
    else
      let option_wrapped_forms = generate_subpath form negated_equality_forms in
      let lemma_c = lmkOther (EqCgr (form, Array.to_list option_wrapped_forms)) None in
      lemma_c
  | L_CC_Transitivity (form, negated_equality_forms) ->
    if (isBooleanEqualityInLemma form)
    then (assert false)
    else
      let lemma_c = lmkOther (EqTr (form, negated_equality_forms)) None in
      lemma_c

(** Walk an formula proof and return the equivalent certificate. *)
let rec walk_clause_proof  cp =
  if Hashtbl.mem clause_proof_table cp
  then Hashtbl.find clause_proof_table cp
  else
    let new_c =
      (match cp with
       | Resolution (cp1, cp2) ->
         (* deb "Resolution BEG"; *)
         let c1 = walk_clause_proof cp1 in
         let c2 = walk_clause_proof cp2 in
         let res = lmkRes c1 c2 [] in
         (* deb "Resolution END"; *)
         res
       | Clause (fp, _) ->
         walk_formula_proof fp
       | Lemma l -> handle_lemma l) in
    Hashtbl.add clause_proof_table cp new_c;
    new_c
