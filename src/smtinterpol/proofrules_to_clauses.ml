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


let negate_formula f =
  let reif = Form.create () in
  let formula = Form.get reif f in 
  SmtAtom.Form.neg (formula)

let mkResV c1 c2 tl v =
  mk_scertif (Res { rc1 = c1; rc2 = c2; rtail = tl }) v

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

let mkEquality f g =
  let form_pos = Fapp (Fiff, Array.of_list [f; g]) in
  Form.get VeritSyntax.rf form_pos

(* Given an iff formula, return a clause that proves this formula.*)
let translate_rewrite_iff rewritee_clause rewrite_rule rewrite_formula =
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
     Printf.printf "\n# translate_rewrite eqToXor last %i" res.id;
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
     Printf.printf "\n# translate_rewrite andToOr last %i" res.id;
     res
   (* TODO Rewrite_notSimp has to return an iff formula. *)
   | Rewrite_notSimp ->
     let simpl1 = lmkOther (ImmFlatten (rewritee_clause, rhs)) (Some [rhs]) in
     Printf.printf "\n# translate_rewrite notSimpl %i" simpl1.id;
     simpl1
   (* TODO Rewrite_intern has to return an iff formula. *)
   | Rewrite_intern ->
     (* let refl = lmkOther (ImmFlatten (rewritee_clause, [])) None in *)
     let Some [formula] = rewritee_clause.value in
     let refl_formula = mkEquality formula formula in
     let refl_cl = lmkOther (EqTr (refl_formula, [])) (Some [refl_formula]) in
     refl_cl
  
let translate_rewrite_equality dummy = assert false

let translate_rewrite rewritee_clause rewrite_rule rewrite_formula =
  let form_pos = Form.pform rewrite_formula in
  match form_pos with
  | Fapp (Fiff, _) -> translate_rewrite_iff rewritee_clause rewrite_rule rewrite_formula
  | Fatom (_) -> translate_rewrite_equality rewritee_clause rewrite_rule rewrite_formula

    (* rewritee_clause *)

let translate_split unsplit_clause split_rule =
  match split_rule with
  | Split_xor_2 -> 
    let split_clause = lmkOther (ImmBuildDef2 unsplit_clause) None in
    split_clause
  | Split_notOr ->
    (*  TODO: remove hardcoded index... need to detect correct index instead *)
    let split_clause = lmkOther (ImmBuildProj (unsplit_clause, 1)) None in
    split_clause

let substitute_sub_formula f a b =
  (* print_string "\n subst_sub_form f";
   * pp_form f;
   * print_string "\n subst_sub_form a";
   * pp_form (Form.pform a);
   * print_string "\n subst_sub_form b";
   * pp_form (Form.pform b); *)
  let pa = Form.pform a in
  let pb = Form.pform b in
  let ret = ref f in
  (match f with
  | Fapp (fop, far) ->
    ret := Fapp (fop, Array.map (fun orig -> if (Form.equal orig a) then b else orig) far)
  | f when f == pa ->
    ret :=  pb
  | _ ->
    ret := f);
  Form.get VeritSyntax.rf !ret

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
  | Abop (typed_op, _, _) -> typed_op

let rec visit_equality_proof ep existsclause =
  if Hashtbl.mem equality_table ep then Hashtbl.find equality_table ep else
    let new_clause = 
    (match ep with
  | Rewrite (formula, rule) -> translate_rewrite existsclause rule formula
  (* | Congruence (lep, Rewrite (_, Rewrite_intern)) -> visit_equality_proof lep existsclause *)
  (* | Congruence (lep, rep) -> assert false; visit_equality_proof lep existsclause *)
  | Congruence (lep, rep) ->
    let lecl = visit_equality_proof lep existsclause in
    let recl = visit_equality_proof rep existsclause in
    let (Some [le_formula]) = (get_last lecl).value in
    let (Some [re_formula]) = (get_last recl).value in
    let f = get_subformula le_formula 0 in
    Printf.printf "\n f ";
    Form.to_smt Atom.to_smt Format.std_formatter f;
    let t_ti = get_subformula re_formula 0 in
    let typ = get_single_atom_type_from_formula (Form.pform t_ti) in
    Printf.printf "\n t_ti ";
    Form.to_smt Atom.to_smt Format.std_formatter t_ti;
    let t_ti_formu = t_ti in
    let neq_equalities = generate_cong_subpath t_ti typ in
    let n_e = Array.map
        (fun x ->
           let formu = Form.get VeritSyntax.rf (Fatom x) in
           formu)
        neq_equalities in
    let cong = lmkOther
        (EqCgr (Form.neg t_ti, Array.to_list (Array.map (fun x -> Some x) n_e)))
        (Some ((t_ti_formu) :: (Array.to_list n_e))) in
    let res = lmkResV cong recl [] (Some [re_formula]) in
    res
  | Transitivity (lep, rep) ->
    let lecl = visit_equality_proof lep existsclause in
    Printf.printf "\n# visit_equality_proof Transitivity first %i" lecl.id;
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
    Printf.printf "\n# visit_equality_proof Transitivity last %i" res.id;
    res
  | Reflexivity formula ->
    let refl_formula = mkEquality formula formula in
    let refl_cl = lmkOther (EqTr (refl_formula, [])) (Some [refl_formula]) in
    Printf.printf "\n# visit_equality_proof Reflexivity %i" refl_cl.id;
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
    lmkRootV [f]
  | Equality (fp, ep) ->
    let fproof_clause = visit_formula_proof fp in
    Printf.printf "\n# visit_formula_proof first %i" fproof_clause.id;
    (* let imm_clause = lmkOther (ImmBuildDef2 fproof_clause) None in
     * link fproof_clause imm_clause; *)
    let ep_cl = visit_equality_proof ep fproof_clause in
    (match ep with
     | Rewrite (_, Rewrite_notSimp) ->
       Printf.printf "\n# visit_formula_proof Rewrite notSimpl no new cl";
       ep_cl
     (* | Rewrite(_, Rewrite_intern) ->
      *   (\* link fproof_clause ep_cl; *\)
      *   ep_cl *)
     | _ ->
       let (a,b,c) = get_whole_and_sub_formulas ep_cl.value in
       (* let ib1 = lmkOther (ImmBuildDef2 ep_cl) (Some [Form.neg b;c]) in *)
       let ib1 = lmkOther (ImmBuildDef2 ep_cl) (Some [Form.neg b; c]) in
       Printf.printf "\n# visit_formula_proof Rewrite first %i" ib1.id;
       let res1 = lmkResV ib1 fproof_clause [] (Some [c]) in
       Printf.printf "\n# visit_formula_proof Rewrite last %i" res1.id;
       res1
    )
  | Split (fp, f, rule) ->
    let unsplit_clause = visit_formula_proof fp in
    Printf.printf "\n# visit_formula_proof Split %i" unsplit_clause.id;
    translate_split unsplit_clause rule) in
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
