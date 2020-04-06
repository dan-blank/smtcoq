open Prooftree_ast
open SmtAtom
open SmtForm
open SmtTrace
open Printexc
open SmtCertif
open VeritSyntax

exception ProofrulesToSMTCoqExpection of string

let clause_proof_table : (Prooftree_ast.clause_proof, SmtAtom.Form.t clause) Hashtbl.t = Hashtbl.create 17
let equality_proof_table : (Prooftree_ast.equality_proof, SmtAtom.Form.t clause) Hashtbl.t = Hashtbl.create 17
let formula_proof_table : (Prooftree_ast.formula_proof, SmtAtom.Form.t clause) Hashtbl.t = Hashtbl.create 17

let clauses : SmtAtom.Form.t clause list ref = ref []
let roots : SmtAtom.Form.t clause list ref = ref []

let print_latest_clause () =
  let get_last_id ls = if (0 != List.length ls) then (List.hd (List.rev ls)).id else (-1) in
  (* let get_last_id ls = List.length ls in *)
  let last = max (get_last_id !clauses) (get_last_id !roots) in
  Printf.printf " last clause or root: %i" last

let deb s =
  Printf.printf "\n §§§ %s" s;
  print_latest_clause ()

let isSome option =
  match option with
  | None -> false
  | _ -> true

let rec get_first c =
  match c.prev with
  | Some p -> get_first p
  | None -> c

let rec get_last c =
  match c.next with
  | Some n -> get_last n
  | None -> c

let rec adjust_root_pos_values c pos =
  let new_pos = pos + 1 in
  if (isRoot c.kind) then c.pos <- Some (pos + 1);
  match c.next with
  | Some n -> adjust_root_pos_values n new_pos
  | None -> ()

let form_op_to_string = function
  | Ftrue -> "Ftrue"
  | Ffalse -> "Ffalse"
  | Fand -> "Fand"
  | For -> "For"
  | Fxor -> "Fxor"
  | Fimp -> "Fimp"
  | Fiff -> "Fiff"
  | Fite -> "Fite"
  | Fnot2 (i)-> "Fnot2" ^ (string_of_int i)
  | _ -> "Not supported yet"

(* let pp_form_op op = Printf.printf (form_op_to_string op) *)

let rec pp_form = function
  | Fatom (a) ->
    Printf.printf "(";
    Printf.printf "Fatom ";
    Atom.to_smt Format.std_formatter a;
    Printf.printf ")"
  | Fapp (fop, farray) ->
    Printf.printf "(";
    Printf.printf "Fapp ";
    Printf.printf "%s" (form_op_to_string fop);
    Array.iter (fun f -> pp_form (Form.pform f)) farray;
    Printf.printf ")"

(* let visit_formula = function
 *   | _ -> SmtTrace.mkRoot *)

(* Get subformula OR return the atom *)
let get_subformula f i =
  let formula = Form.pform f in
  match formula with
  | Fapp (_, ar) -> Array.get ar i
  (* | Fatom form -> f *)

let get_subformula_raw f i =
  let formula = f in
  match formula with
  | Fapp (_, ar) -> Array.get ar i

let negate_formula f =
  let reif = Form.create () in
  let formula = Form.get reif f in 
  SmtAtom.Form.neg (formula)

let mkResV c1 c2 tl v =
  (* Printf.printf "\mmkResV-------------"; *)
  match v with | (Some vs) -> List.iter (fun t -> pp_form (Form.pform t)) vs;
  mk_scertif (Res { rc1 = c1; rc2 = c2; rtail = tl }) v

(* TODO Hack: for now, lemmas are always assumed to be atomic equalities*)
let isBooleanEquality f = false

let isPredicateFormula f = assert false

let isFunctionFormula f = assert false

let isLogicalOperatorFormula f =
  let form_pos = Form.pform f in
  match form_pos with
  | Fapp (_, _) -> true 
  | _           -> false

let link_list_of_clauses ls =
  match ls with
  | [] -> ()
  | h :: tl -> let _ = List.fold_left (fun l r -> link l r; r) h tl in ()

let add_roots_and_non_roots () =
  clauses := List.append !roots !clauses;
  link_list_of_clauses !clauses;
  adjust_root_pos_values (List.hd !clauses) (-1)


let lmkOther rule value =
  let clause = mkOther rule value in
  clauses := List.append !clauses [clause];
  clause

let lmkRes r l tl =
  let clause = mkRes r l tl in
  clauses := List.append !clauses [clause];
  clause

let lmkResV r l tl v =
  let clause = mkResV r l tl v in
  clauses := List.append !clauses [clause];
  clause

let lmkRootV v =
  let clause = mkRootV v in
  roots := List.append !roots [clause];
  (* clauses := List.append !clauses [clause]; *)
  clause

let aux_bd1 f = lmkOther (BuildDef f) None
let aux_bd2 f = lmkOther (BuildDef2 f) None

let mkEquality f g =
  let form_pos = Fapp (Fiff, Array.of_list [f; g]) in
  Form.get VeritSyntax.rf form_pos

let isTrueFop fapp =
  match fapp with
  | Fapp (Ftrue, _) ->
    (* assert false; *)
    true
  | _ -> false

let isTrueEqIntern f =
  let r_sub = Form.pform (get_subformula f 1) in
  match r_sub with
  | Fapp (Fiff, far) ->
    let pot_true = Array.get far 1 in
    isTrueFop (Form.pform pot_true)
  | _ -> false

(* TODO consider symmetric case*)
let create_intern_true_eq (iixt : SmtAtom.Form.t) =
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
  let iixt = lmkResV iixt_ntrue cl_true [] (Some [iixt]) in
  deb "create_intern_true_eq END";
  iixt

(* Given a boolean equality, return a clause that proves it.*)
let handle_rewrite_bool rewritee_clause rewrite_rule rewrite_formula =
  (* let lhs_raw = get_subformula_raw rewrite_formula 0 in *)
  let rcl = mkRootV [rewrite_formula] in
  (* print_certif Form.to_smt Atom.to_smt rcl ".cert_debug2"; *)
  let lhs = get_subformula rewrite_formula 0 in
  let rhs = get_subformula rewrite_formula 1 in
  match rewrite_rule with
   | Rewrite_eqToXor ->
     let base_pos = lmkOther (BuildDef2 rewrite_formula) None in
     Printf.printf "\n# translate_rewrite eqToXor first %i" base_pos.id;
     let base_neg = lmkOther (BuildDef rewrite_formula) None in
     (* Resolve to (iff a b) x (not y) *)
     let choose_nx_y_1 = lmkOther (BuildDef (Form.neg lhs)) None in
     let choose_nx_y_2 = lmkOther (BuildDef (Form.neg rhs)) None in
     let res_nx_y = lmkRes base_pos choose_nx_y_1 [choose_nx_y_2] in
     (* Resolve to (iff a b) x y *)
     let choose_x_y_1 = lmkOther (BuildDef2 lhs) None in
     let choose_x_y_2 = lmkOther (BuildDef rhs) None in
     let res_x_y = lmkRes base_neg choose_x_y_1 [choose_x_y_2] in
     (* Resolve to (iff a b) x *)
     let res_x = lmkRes res_x_y res_nx_y [] in

     (* Resolve to (iff a b) (not x) (not y) *)
     let choose_x_ny_1 = lmkOther (BuildDef lhs) None in
     let choose_x_ny_2 = lmkOther (BuildDef2 rhs) None in
     let res_x_ny = lmkRes base_neg choose_x_ny_1 [choose_x_ny_2] in
     (* Resolve to (iff a b) (not x) y *)
     let choose_nx_ny_1 = lmkOther (BuildDef2 (Form.neg lhs)) None in
     let choose_nx_ny_2 = lmkOther (BuildDef2 (Form.neg rhs)) None in
     let res_nx_ny = lmkRes base_pos choose_nx_ny_1 [choose_nx_ny_2] in
     (* Resolve to (iff a b) (not x) *)
     let res_nx = lmkRes res_x_ny res_nx_ny [] in

     let res = lmkResV res_x res_nx [] (Some [rewrite_formula]) in
     (* Printf.printf "\n# translate_rewrite eqToXor last %i" res.id; *)
     res
     (* clauses := List.append !clauses [base_pos; base_neg; choose_nx_y_1; choose_nx_y_2; res_nx_y; choose_x_y_1; choose_x_y_2; res_x_y; res_x; choose_x_ny_1; choose_x_ny_2; res_x_ny; choose_nx_ny_1; choose_nx_ny_2; res_nx_ny; res_nx; res]; *)
   | Rewrite_andToOr ->
     let base_1 = lmkOther (BuildDef2 rewrite_formula) None in
     Printf.printf "\n# translate_rewrite andToOr first %i" base_1.id;
     (* Resolve to (iff a b) x *)
     let prod_and_1 = lmkOther (BuildProj (lhs, 0)) None in
     let prod_or_1 = lmkOther (BuildProj (rhs, 0)) None in
     let res_x = lmkRes base_1 prod_and_1 [prod_or_1] in
     (* Resolve to (iff a b) y *)
     let prod_and_2 = lmkOther (BuildProj (lhs, 1)) None in
     let prod_or_2 = lmkOther (BuildProj (rhs, 1)) None in
     let res_y = lmkRes base_1 prod_and_2 [prod_or_2] in
     (* Resolve to (iff a b) (not x) (not y) *)
     let base2 = lmkOther (BuildDef rewrite_formula) None in
     let sum_and = lmkOther (BuildDef lhs) None in
     let sum_or = lmkOther (BuildDef rhs) None in
     let res_nx_ny = lmkRes base2 sum_and [sum_or] in
     (* Resolve to (iff a b) *)
     let res = lmkResV res_nx_ny res_x [res_y] (Some [rewrite_formula]) in
     (* Printf.printf "\n# translate_rewrite andToOr last %i" res.id; *)
     res
   (* TODO Rewrite_notSimp has to return an iff formula. *)
   | Rewrite_notSimp ->
     let simpl1 = lmkOther (ImmFlatten (rewritee_clause, rhs)) rewritee_clause.value in
     (* Printf.printf "\n# translate_rewrite notSimpl %i" simpl1.id; *)
     pp_form (Form.pform lhs);
     if (Form.equal lhs rhs) then Printf.printf "\n lhs and rhs are equal!";
     simpl1
   (* TODO Rewrite_intern has to return an iff formula. *)
   | Rewrite_intern ->
     if (isTrueEqIntern rewrite_formula)
     then (create_intern_true_eq rewrite_formula) 
     else (
       deb "Rewrite_intern true eq BEG";
     let formula_l = get_subformula rewrite_formula 0 in
     let formula_r = get_subformula rewrite_formula 1 in
     let refl_formula = mkEquality formula_l formula_r in
     let na = aux_bd1 refl_formula in
     let a = aux_bd2 refl_formula in
     let refl_cl = lmkResV na a [] (Some [refl_formula]) in
     deb "Rewrite_intern true eq END";
     refl_cl)
  
let handle_rewrite_nonbool _ = assert false

let translate_rewrite rewritee_clause rewrite_rule rewrite_formula =
  (* Printf.printf "\n translate_rewrite: formula "; *)
  (* Form.to_smt Atom.to_smt Format.std_formatter rewrite_formula; *)
  if (isLogicalOperatorFormula rewrite_formula)
  then handle_rewrite_bool rewritee_clause rewrite_rule rewrite_formula
  else handle_rewrite_nonbool rewritee_clause rewrite_rule rewrite_formula



let translate_split unsplit_clause split_rule =
  match split_rule with
  | Split_xor_2 -> 
    let split_clause = lmkOther (ImmBuildDef2 unsplit_clause) None in
    split_clause
  | Split_notOr ->
    (*  TODO: remove hardcoded index... need to detect correct index instead *)
    let split_clause = lmkOther (ImmBuildProj (unsplit_clause, 1)) None in
    split_clause

let handle_refl_bool dummy = assert false
let handle_ref_nonbool dummy = assert false
let translate_refl dummy = assert false

let handle_cong_bool dummy = assert false
let handle_cong_nonbool dummy = assert false
let translate_cong f cs = assert false

let handle_trans_bool dummy = assert false
let handle_trans_nonbool dummy = assert false
let translate_trans f ts = assert false

let get_single_atom_type_from_formula f =
  let Fatom a = f in
  match Atom.atom a with
  | Acop _ -> Printf.printf "\n acop"; assert false
  | Auop _ -> Printf.printf "\n auop"; assert false
  | Abop (typed_op, _, _) -> typed_op
  | Atop _ -> Printf.printf "\n atop"; assert false
  | Anop _ -> Printf.printf "\n anop"; assert false
  | Aapp _ -> Printf.printf "\n aapp"; assert false


(*
Input: l = (not x) r = y
   TODO proper
*)
let create_congruent_not x y =
  deb "create_congruent_clause_not BEG";
  assert (not (Form.is_neg x));
  assert (not (Form.is_neg y));
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

let create_congruent_clause f equalities =
  match f, equalities with
  (* Special case: negation is not represented as an Fop in SMTCoq. *)
  | f, [e] when (Form.is_neg f) -> create_congruent_not (Form.neg f) e
  | _ -> assert false

(* TODO a b c positiv negativ? *)
let create_transitive_clause_not a b c =
  deb "create_transitive_clause_not BEG";
  (* This derivation only works when a, b and c are distinct.
  For example, if a and b were equal, then niab_a_nb would evaluate to true (since then nb = na and { (na a) } == { true })*)
  let niab = Form.neg (mkEquality a b) in
  let nibc = Form.neg (mkEquality b c) in
  let iac = mkEquality a c in
  let niab_a_nb = aux_bd1 niab in
  let nibc_b_nc = aux_bd1 nibc in
  let niab_nibc_a_nc = lmkRes niab_a_nb nibc_b_nc [] in
  let iac_a_c = aux_bd2 iac in
  let niab_nibc_iac_a = lmkRes niab_nibc_a_nc iac_a_c [] in
  let niab_na_b = aux_bd2 niab in
  let nibc_nb_c = aux_bd2 nibc in
  let niab_nibc_na_c = lmkRes niab_na_b nibc_nb_c [] in
  let iac_na_nc = aux_bd1 iac in
  let niab_nibc_iac_na = lmkRes niab_nibc_na_c iac_na_nc [] in
  let res = lmkResV niab_nibc_iac_a niab_nibc_iac_na [] (Some [iac; niab; nibc]) in
  deb "create_transitive_clause_not END";
  res


let rec visit_equality_proof ep existsclause =
  if Hashtbl.mem equality_proof_table ep then Hashtbl.find equality_proof_table ep else
    let new_c =
    (match ep with
      | Rewrite (formula, rule) ->
        deb "Rewrite BEG";
        let c = translate_rewrite existsclause rule formula in
        deb "Rewrite END";
        c
      | Congruence (lep, rep) ->
        deb "Congruence BEG";
        let lecl = visit_equality_proof lep existsclause in
        let recl = visit_equality_proof rep existsclause in
        let (Some [le_formula]) = (get_last lecl).value in
        let (Some [re_formula]) = (get_last recl).value in
        (* Printf.printf "\nCongruence left and right BEGIN"; *)
        let l_sub = get_subformula le_formula 1 in
        let r_sub = get_subformula re_formula 1 in
        (* Form.to_smt Atom.to_smt Format.std_formatter l_sub; *)
        (* Printf.printf "\n";
         * Form.to_smt Atom.to_smt Format.std_formatter r_sub;
         * Printf.printf "\nCongruence left and right END"; *)
        let cong_cl_raw = create_congruent_clause l_sub [r_sub] in
        (* print_certif Form.to_smt Atom.to_smt (get_last cong_cl_raw) ".cert_cong"; *)
        let (Some [cong_formula; _]) = (get_last cong_cl_raw).value in
        let cong_cl = lmkResV recl cong_cl_raw [] (Some [cong_formula]) in
        let cong_sub0 = get_subformula cong_formula 0 in
        let cong_sub1 = get_subformula cong_formula 1 in
        let l_sub0 = get_subformula le_formula 0 in
        if ((Form.equal cong_sub0 cong_sub1) && (Form.equal cong_sub0 l_sub0))
        then (
          let trans_cl_raw = create_transitive_clause_not l_sub0 cong_sub0 cong_sub1 in
          let res1 = lmkRes trans_cl_raw lecl [] in
          let res = lmkRes res1 cong_cl [] in
          deb "Congruence END";
          res)
        else (
          let res = cong_cl in
          deb "Congruence END";
          res)
      | Transitivity (lep, rep) ->
        deb "Transitivity BEG";
        let lecl = visit_equality_proof lep existsclause in
        let recl = visit_equality_proof rep existsclause in
        let (Some [le_formula]) = (get_last lecl).value in
        let (Some [re_formula]) = (get_last recl).value in
        let a = get_subformula le_formula 0 in
        let (b : SmtAtom.Form.t) = get_subformula le_formula 1 in
        let (c : SmtAtom.Form.t) = get_subformula re_formula 1 in
        let eq_to_show = mkEquality a c in
        let first_neg = Form.neg (mkEquality a b) in
        let second_neg = Form.neg (mkEquality b c) in
        let first_neg_clause = lmkOther (EqTr (first_neg, [])) None in
        let second_neg_clause = lmkOther (EqTr (second_neg, [])) None in
        let trans = lmkOther (EqTr (eq_to_show, [first_neg; second_neg])) None  in
        let res = lmkResV trans first_neg_clause [second_neg_clause] (Some [eq_to_show]) in
        deb "Transitivity END";
        res
      | Reflexivity formula ->
        deb "Reflexivity BEG";
        let refl_formula = mkEquality formula formula in
        let na = aux_bd1 refl_formula in
        let a = aux_bd2 refl_formula in
        let refl_cl = lmkResV na a [] (Some [refl_formula]) in
        deb "Reflexivity END";
        refl_cl) in
    Hashtbl.add equality_proof_table ep new_c;
    new_c

let is_simplification_rewrite pr =
  match pr with
  | Rewrite (_, Rewrite_notSimp) -> true
  | _ -> false

let get_whole_and_sub_formulas cv =
  match cv with
  | Some [form] ->
    let lhs = get_subformula form 0 in
    let rhs = get_subformula form 1 in
    (form, lhs, rhs)
  | None -> assert false
  | Some _ -> assert false

let rec walk_formula_proof form =
  if Hashtbl.mem formula_proof_table form then Hashtbl.find formula_proof_table form else
    let new_c =
      (match form with
      (* | Tautology (f, _) -> visit_formula f *)
       | Asserted (f) ->
         (* Printf.printf ("\n hey Asserted ------------------ \n"); *)
         (* pp_form (Form.pform f); *)
         deb "Asserted BEG";
         let r = lmkRootV [f] in
         deb "Asserted END";
         r
       | Equality (fp, ep) ->
         deb "Equality BEG";
         let fproof_clause = walk_formula_proof fp in
         (* let imm_clause = lmkOther (ImmBuildDef2 fproof_clause) None in
          * link fproof_clause imm_clause; *)
         let ep_cl = visit_equality_proof ep fproof_clause in
         let retval = (match ep with
          | Rewrite (_, Rewrite_notSimp) ->
            (* print_latest_clause(); *)
            ep_cl
          | _ ->
            (* let (a,b,c) = get_whole_and_sub_formulas ep_cl.value in *)
            (* print_latest_clause(); *)
            let ib1 = lmkOther (ImmBuildDef2 ep_cl) ep_cl.value in
            let res1 = lmkRes ib1 fproof_clause [] in
            (* let (Some [iff_formula]) = ep_cl.value in
             * let ninab = aux_bd2 (Form.neg iff_formula) in
             * let res2 = lmkRes ninab ep_cl [] in
             * let res1 = lmkRes res2 fproof_clause [] in *)
            res1
         ) in
         deb "Equality END";
         retval
       | Split (fp, f, rule) ->
         deb "Split BEG";
         let unsplit_clause = walk_formula_proof fp in
         let retval = translate_split unsplit_clause rule in
         deb "Split END";
         retval) in
    Hashtbl.add formula_proof_table form new_c;
    new_c
(* let hack_replace_atom_op a op = *)



let generate_subpath f negated_equalities_fs =
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
  let gpform = Form.pform f in
  let Fatom (atom) = gpform in
  let Abop(_, left_atom, right_atom) = Atom.atom atom in
  let Aapp (_, hatoms1) = Atom.atom left_atom in
  let Aapp (_, hatoms2) = Atom.atom right_atom in
  Array.map2 (fun x y -> wrap_equality_formula_in_option x y negated_equalities_fs) hatoms1 hatoms2 


let handle_lemma = function
  | L_CC_Congruence (f, ns)->
    if (isBooleanEquality f)
    then (assert false)
    else
      deb "handle_lemma CC_Cong BEG";
      let nfs = generate_subpath f ns in
      let nfs = Array.to_list nfs in
      let lemma_cl = lmkOther (EqCgr (f, nfs)) None in
      deb "handle_lemma CC_Cong END";
      lemma_cl
  | L_CC_Transitivity (f, ns) ->
    if (isBooleanEquality f)
    then (assert false)
    else
      let nfs = generate_subpath f ns in
      (* let nfs = List.map (fun (Some x) -> x) (List.filter isSome (Array.to_list nfs)) in *)
      let lemma_cl = lmkOther (EqTr (f, ns)) None in
      lemma_cl

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
