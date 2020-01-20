open Prooftree_ast
open SmtAtom
open SmtForm
open SmtTrace
open Printexc
open SmtCertif
open VeritSyntax

exception ProofrulesToSMTCoqExpection of string

let clause_table : (Prooftree_ast.clause_proof, SmtAtom.Form.t clause) Hashtbl.t = Hashtbl.create 17
let equality_table : (Prooftree_ast.equality_proof, SmtAtom.Form.t clause) Hashtbl.t = Hashtbl.create 17
let formula_table : (Prooftree_ast.formula_proof, SmtAtom.Form.t clause) Hashtbl.t = Hashtbl.create 17

let clauses : SmtAtom.Form.t clause list ref = ref []
let roots : SmtAtom.Form.t clause list ref = ref []

let print_latest_clause () =
  let get_last_id ls = if (0 != List.length ls) then (List.hd (List.rev ls)).id else 0 in
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
  Printf.printf "\mmkResV-------------";
  match v with | (Some vs) -> List.iter (fun t -> pp_form (Form.pform t)) vs;
  mk_scertif (Res { rc1 = c1; rc2 = c2; rtail = tl }) v

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
  let ixt_nx_false = aux_bd1 ixt in
  let iixt_ixt = lmkRes iixt_x_nixt ixt_nx_false [] in
  let iixt_nx_nixt = aux_bd1 iixt in
  let nixt_x_false = aux_bd1 (Form.neg ixt) in
  let iixt_nixt = lmkRes iixt_nx_nixt nixt_x_false [] in
  let iixt = lmkResV iixt_ixt iixt_nixt [] (Some [iixt]) in
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
     let formula_l = get_subformula rewrite_formula 0 in
     let formula_r = get_subformula rewrite_formula 1 in
     let refl_formula = mkEquality formula_l formula_r in
     let na = aux_bd1 refl_formula in
     let a = aux_bd2 refl_formula in
     let refl_cl = lmkResV na a [] (Some [refl_formula]) in
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

let generate_cong_subpath f typed_op =
  let BO_eq typ = typed_op in
  let f_pos = Form.pform f in
  let Fatom (raw_atom) = f_pos in
  (* let hatom = Atom.get VeritSyntax.ra raw_atom in *)
  (* Atom.to_smt Format.std_formatter raw_atom; *)
  let Abop(_, l, r) = Atom.atom raw_atom in
  let Aapp (_, lhs) = Atom.atom l in
  (* Array.iter (fun x -> Atom.to_smt Format.std_formatter x) lhs; *)
  let Aapp (_, rhs) = Atom.atom r in
  (* Array.iter (fun x -> Atom.to_smt Format.std_formatter x) rhs; *)
  (* print_string ("\nfinds " ^ (string_of_int (Array.length lhs))); *)
  Array.map2 (fun x y -> Atom.mk_eq VeritSyntax.ra typ x y) lhs rhs 

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
let create_transitive_clause_not a b_pos c_pos =
  deb "create_transitive_clause_not BEG";
  (* let a = if (Form.is_neg a_pos) then Form.neg a_pos else a_pos in *)
  let b = Form.neg b_pos in
  let c = Form.neg c_pos in
  let neq_ab = Form.neg (mkEquality a b) in
  let neq_bc = Form.neg (mkEquality b c) in
  let eq_ac = mkEquality a c in
  let a_nb = aux_bd1 neq_ab in
  let b_nc = aux_bd1 neq_bc in
  let a_nc = lmkRes a_nb b_nc [] in
  let a_c = aux_bd2 eq_ac in
  let a = lmkRes a_nc a_c [] in
  let na_b = aux_bd2 neq_ab in
  let nb_c = aux_bd2 neq_bc in
  let na_c = lmkRes na_b nb_c [] in
  let na_nc = aux_bd1 eq_ac in
  let na = lmkRes na_c na_nc [] in
  let res = lmkResV na a [] (Some [eq_ac; neq_ab; neq_bc]) in
  deb "create_transitive_clause_not END";
  res


let rec visit_equality_proof ep existsclause =
  if Hashtbl.mem equality_table ep then Hashtbl.find equality_table ep else
    let new_clause =
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
        let cong_cl = lmkRes recl cong_cl_raw [] in
        (* Might not work, when value is set incorrectly. *)
        let cong_sub0 = get_subformula cong_formula 0 in
        let cong_sub1 = get_subformula cong_formula 1 in
        let l_sub0 = get_subformula le_formula 0 in
        let trans_cl_raw = create_transitive_clause_not l_sub0 cong_sub0 cong_sub1 in
        let res1 = lmkRes trans_cl_raw lecl [] in
        let res = lmkRes res1 cong_cl [] in
        (* let res = lmkRes trans_cl_raw lecl [] in *)
        (* Printf.printf "\n# Congruence %i" res.id; *)
        deb "Congruence END";
        res
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
    Hashtbl.add equality_table ep new_clause;
    new_clause

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

let rec visit_formula_proof form =
  if Hashtbl.mem formula_table form then Hashtbl.find formula_table form else
    let new_clause =
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
         let fproof_clause = visit_formula_proof fp in
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
            let ib1 = lmkOther (ImmBuildDef2 ep_cl) None in
            let res1 = lmkRes ib1 fproof_clause [] in
            res1
         ) in
         deb "Equality END";
         retval
       | Split (fp, f, rule) ->
         deb "Split BEG";
         let unsplit_clause = visit_formula_proof fp in
         let retval = translate_split unsplit_clause rule in
         deb "Split END";
         retval) in
    Hashtbl.add formula_table form new_clause;
    new_clause
(* let hack_replace_atom_op a op = *)


let rec hack_replace_level1_by_op f op =
  pp_form (Form.pform f);
  match Form.pform f with
  (* | Fatom formu -> hack_replace_level1_by_op formu op *)
  | Fapp (fo, _) ->
    negate_formula (Fapp (fo, Array.of_list [op; op]))
let do_args_appear_in_eq eq a b =
  begin match eq with
    | Abop (_, x, y) when x == a && y == b->
      (* print_string "\n finds true1"; *)
      true
    | Abop (_, y, x) when x == a && y == b->
      (* print_string "\n finds true2"; *)
      true
    | _ ->
      (* print_string "\n finds false"; *)
      false end
let pair_to_option a b ns =
  begin let finds = List.find_all (fun fatom ->
      (* pp_form (Form.pform fatom);
       * print_string "\npait_to_option";
       * Atom.to_smt Format.std_formatter a;
       * Atom.to_smt Format.std_formatter b; *)
      let Fatom atom = Form.pform fatom in
      let aatom = Atom.atom atom in
      do_args_appear_in_eq aatom a b) ns in
    match finds with
    | [nf] ->
      print_string "\nfinds Some";
      Some nf
    | _ ->
      print_string "\nfinds None";
      None end 

let generate_subpath_from_arg f (raw_ns: SmtAtom.Form.t list) =
  let ns = raw_ns in
  let f_pos = Form.pform f in
  let Fatom (raw_atom) = f_pos in
  (* let hatom = Atom.get VeritSyntax.ra raw_atom in *)
  (* Atom.to_smt Format.std_formatter raw_atom; *)
  let Abop(_, l, r) = Atom.atom raw_atom in
  let Aapp (_, lhs) = Atom.atom l in
  (* Array.iter (fun x -> Atom.to_smt Format.std_formatter x) lhs; *)
  let Aapp (_, rhs) = Atom.atom r in
  (* Array.iter (fun x -> Atom.to_smt Format.std_formatter x) rhs; *)
  (* print_string ("\nfinds " ^ (string_of_int (Array.length lhs))); *)
  Array.map2 (fun x y -> pair_to_option x y ns) lhs rhs 


(* TODO Add transitivity *)
let handle_lemma = function
  | L_CC_Congruence (f, ns)->
    let nfs = generate_subpath_from_arg f ns in
    let nfs = Array.to_list nfs in
    let lemma_cl = lmkOther (EqCgr (f, nfs)) None in
    Printf.printf "\n# handle_lemma Congruence %i" lemma_cl.id;
    lemma_cl

let rec visit_clause_proof  (f : Prooftree_ast.clause_proof) : SmtAtom.Form.t SmtCertif.clause =
  (* print_string "\npt_to_smtcoq: visit_clause_proof: Begin"; *)
  if Hashtbl.mem clause_table f then Hashtbl.find clause_table f else
    let new_clause =
      (match f with
       | Resolution (cp1, cp2) ->
         (* print_string "\n---- RESO!"; *)
         let (cl1 : SmtAtom.Form.t SmtCertif.clause) = visit_clause_proof cp1 in
         let cl2 = visit_clause_proof cp2 in
         let res = lmkRes cl1 cl2 [] in
         res
       | Clause (fp, f) ->
         (* print_string "\n----- handle_clause: will return root!"; *)
         visit_formula_proof fp
       | Lemma l -> handle_lemma l) in
    Hashtbl.add clause_table f new_clause;
    new_clause
