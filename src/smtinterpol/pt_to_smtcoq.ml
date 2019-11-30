open Prooftree_ast
open SmtAtom
open SmtForm
open SmtTrace
open Printexc
open SmtCertif
open VeritSyntax

exception ProofrulesToSMTCoqExpection of string

let isSome option =
  match option with
  | None -> false
  | _ -> true

let remove_clause (c : 'a) : unit =
  let lco = c.prev in
  let rco = c.next in
  (match rco with
   | Some (rc) ->
    c.next <- None;
    rc.prev <- None
   | _ -> assert false);
  (match lco with
   | Some (lc) ->
     c.prev <- None;
     lc.next <- None
   | _ -> ());
  (if isSome lco && isSome rco then
     let Some lc = lco in
     let Some rc = rco in
     link lc rc)
  
let move_before_clause move_clause until_clause =
  (* print_string "pt_to_smtcoq: move_before_clause BEGIN"; *)
  remove_clause move_clause;
  let prev_until_clause_o = until_clause.prev in
  (if isSome prev_until_clause_o then
     let Some prev_until_clause = prev_until_clause_o in
     link prev_until_clause move_clause);
  link move_clause until_clause

let rec find_first_non_root c =
  if (not (isRoot c.kind))
  then c
  else
    let Some n = c.next in
    find_first_non_root n

(* Traverse list backwards!
we want all roots after the first non root
*)
let rec take_while_cert goal c acc =
  let newacc = 
  (match c.kind with
  | Root -> c :: acc
  | _ -> acc) in
  if (eq_clause goal c)
  then newacc
  else
  (match c.prev with
  | Some n -> take_while_cert goal n newacc
  | None -> newacc)


let rec get_first c =
  match c.prev with
  | Some p -> get_first p
  | None -> c

let rec get_last c =
  match c.next with
  | Some n -> get_last n
  | None -> c

(* Assumption: The first clause of the certificate is given. *)
let move_roots_to_beginning c =

  let first_non_root = find_first_non_root c in
  let last_clause = get_last c in
  let roots = take_while_cert first_non_root last_clause [] in
  List.iter (fun root_to_move ->
(* print_string ("\n ****** pt_to_smtcoq: and another root: " ^ (string_of_int root_to_move.id) ^ " is moved before: " ^ (string_of_int !first_non_root.id) ); *)
      move_before_clause root_to_move first_non_root) roots


let increment_root c new_pos =
  (* print_string ("\n pt_to_smtcoq increment_root id: " ^ (string_of_int c.id) ^ " new_pos: " ^ (string_of_int new_pos)); *)
  match c.kind with
   | Root ->
     c.pos <- Some new_pos;
     (* print_string ("\n pt_to_smtcoq Middle Root! " ^ (string_of_int new_pos)) *)
   | _ -> ()

let rec reposition_roots c pos =
  let new_pos = pos + 1 in
  increment_root c new_pos;
  match c.next with
  | Some n ->
    reposition_roots n new_pos
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
  | Fatom form -> f

let get_first_subatom a i =
  let rif = Atom.create () in
  Atom.to_smt Format.std_formatter (Atom.get rif a) 
  (* let atom = a in
   * match atom with
   * | Abop (_, a1, a2) -> a1 *)

(* | Reflexivity (f) -> visit_formula f *)
(* | Transitivity (ep1, ep2) ->
 *   let cl1 = visit_equality_proof ep1 in
 *   let cl2 = visit_equality_proof ep2 in
 *   mkRes cl1 cl2 [] *)
(* | Congruence (ep1, ep2) ->
 *   (\* visit_equality_proof ep1;
 *    * visit_equality_proof ep2 *\)
 *     mkRoot *)

(* (iff x y) => (not (xor x y)) *)

(* let tailref = ref [] *)

let negate_formula f =
  let reif = Form.create () in
  let formula = Form.get reif f in 
  SmtAtom.Form.neg (formula)

let replace_fop_and_negate f =
  match f with
  | Fapp (Fiff, ar) ->
    let dings = Fapp (Fxor, ar) in
    negate_formula dings

let link_link_of_clauses ls =
  match ls with
  | [] -> ()
  | h :: tl -> let _ = List.fold_left (fun l r -> link l r; r) h tl in ()

let mkSame r ov = mk_scertif (Same r) ov

let translate_rewrite rewritee_clause rewrite_rule rewrite_formula =
  let lhs = get_subformula rewrite_formula 0 in
  let rhs = get_subformula rewrite_formula 1 in
  let clauses = ref [] in
  (match rewrite_rule with
   | Rewrite_eqToXor ->
     let base_pos = mkOther (BuildDef2 rewrite_formula) None in
     let base_neg = mkOther (BuildDef rewrite_formula) None in
     (* Resolve to (iff a b) x (not y) *)
     let choose_nx_y_1 = mkOther (BuildDef (Form.neg lhs)) None in
     let choose_nx_y_2 = mkOther (BuildDef (Form.neg rhs)) None in
     let res_nx_y = mkRes base_pos choose_nx_y_1 [choose_nx_y_2] in
     (* Resolve to (iff a b) x y *)
     let choose_x_y_1 = mkOther (BuildDef2 lhs) None in
     let choose_x_y_2 = mkOther (BuildDef rhs) None in
     let res_x_y = mkRes base_neg choose_x_y_1 [choose_x_y_2] in
     (* Resolve to (iff a b) x *)
     let res_x = mkRes res_x_y res_nx_y [] in

     (* Resolve to (iff a b) (not x) (not y) *)
     let choose_x_ny_1 = mkOther (BuildDef lhs) None in
     let choose_x_ny_2 = mkOther (BuildDef2 rhs) None in
     let res_x_ny = mkRes base_neg choose_x_ny_1 [choose_x_ny_2] in
     (* Resolve to (iff a b) (not x) y *)
     let choose_nx_ny_1 = mkOther (BuildDef2 (Form.neg lhs)) None in
     let choose_nx_ny_2 = mkOther (BuildDef2 (Form.neg rhs)) None in
     let res_nx_ny = mkRes base_pos choose_nx_ny_1 [choose_nx_ny_2] in
     (* Resolve to (iff a b) (not x) *)
     let res_nx = mkRes res_x_ny res_nx_ny [] in

     let res = mkRes res_x res_nx [] in

     clauses := List.append !clauses [base_pos; base_neg; choose_nx_y_1; choose_nx_y_2; res_nx_y; choose_x_y_1; choose_x_y_2; res_x_y; res_x; choose_x_ny_1; choose_x_ny_2; res_x_ny; choose_nx_ny_1; choose_nx_ny_2; res_nx_ny; res_nx; res]

     (* Resolve to (iff a b) (not x) y *)
     (* Resolve to (iff a b) (not x) y *)





    (* (\* TODO: Das hier ist nur über IMplication, muss aber in beide Richtungen und damit unabhängig von rewritee_clause funktioniertn -> ImmBuildDefs nur benutzbar bei lokalen Clausen, falls überhaupt notwendig  *\)
     * let bd1 = mkOther (BuildDef rhs) None in
     * let bd2 = mkOther (BuildDef2 rhs) None in
     * let id1 = mkOther (ImmBuildDef rewritee_clause) None in 
     * let id2 = mkOther (ImmBuildDef2 rewritee_clause) None in
     * let res1 = mkRes bd1 id1 [] in
     * let res2 = mkRes bd2 id2 [res1] in
     * clauses := List.append !clauses [bd1; bd2; id1; id2; res1; res2;] *)
    (* res2 *)
   | Rewrite_andToOr ->
     let base_1 = mkOther (BuildDef2 rewrite_formula) None in
     (* Resolve to (iff a b) x *)
     let prod_and_1 = mkOther (BuildProj (lhs, 0)) None in
     let prod_or_1 = mkOther (BuildProj (rhs, 0)) None in
     let res_x = mkRes base_1 prod_and_1 [prod_or_1] in
     (* Resolve to (iff a b) y *)
     let prod_and_2 = mkOther (BuildProj (lhs, 1)) None in
     let prod_or_2 = mkOther (BuildProj (rhs, 1)) None in
     let res_y = mkRes base_1 prod_and_2 [prod_or_2] in
     (* Resolve to (iff a b) (not x) (not y) *)
     let base2 = mkOther (BuildDef rewrite_formula) None in
     let sum_and = mkOther (BuildDef lhs) None in
     let sum_or = mkOther (BuildDef rhs) None in
     let res_nx_ny = mkRes base2 sum_and [sum_or] in
     (* Resolve to (iff a b) *)
     let res = mkRes res_nx_ny res_x [res_y] in
     clauses := List.append !clauses [base_1; prod_and_1; prod_or_1; res_x; prod_and_2; prod_or_2; res_y; base2; sum_and; sum_or; res_nx_ny; res]
   | Rewrite_notSimp ->
     let simpl1 = mkOther (ImmFlatten (rewritee_clause, rhs)) None in
     clauses := List.append !clauses [simpl1]
   | Rewrite_intern -> ()
  );
  link_link_of_clauses !clauses;
  List.hd !clauses




    (* rewritee_clause *)

let translate_split unsplit_clause split_rule =
  match split_rule with
  | Split_xor_2 -> 
    let split_clause = mkOther (ImmBuildDef2 unsplit_clause) None in
    link unsplit_clause split_clause;
    split_clause
  | Split_notOr ->
    (*  TODO: remove hardcoded index... need to detect correct index instead *)
    let split_clause = mkOther (ImmBuildProj (unsplit_clause, 1)) None in
    link unsplit_clause split_clause;
    split_clause


let rec visit_equality_proof ep existsclause =
  match ep with
  | Rewrite (formula, rule) -> translate_rewrite existsclause rule formula
  | Congruence (lep, rep) -> visit_equality_proof lep existsclause
  | Reflexivity formula -> mkRootV [formula]

let is_simplification_rewrite pr =
  match pr with
  | Rewrite (_, Rewrite_notSimp) -> true
  | _ -> false

let get_whole_and_sub_formulas rewrite_proof_rule =
  match rewrite_proof_rule with
  | Rewrite (r_formula, _) ->
    let lhs = get_subformula r_formula 0 in
    let rhs = get_subformula r_formula 1 in
    (r_formula, lhs, rhs)

let rec visit_formula_proof = function
  (* | Tautology (f, _) -> visit_formula f *)
  | Asserted (f) ->
    (* Printf.printf ("\n hey Asserted ------------------ \n"); *)
    pp_form (Form.pform f);
    mkRootV [f]
  | Equality (fp, ep) ->
    let fproof_clause = visit_formula_proof fp in
    (* let imm_clause = mkOther (ImmBuildDef2 fproof_clause) None in
     * link fproof_clause imm_clause; *)
    let ep_cl = visit_equality_proof ep fproof_clause in
    let first_cl = get_first ep_cl in
    let last_cl = get_last ep_cl in
    (if (is_simplification_rewrite ep)
     then (
       (* let res = mkRes last_cl fproof_clause [] in *)
       (* link fproof_clause first_cl; *)
       link fproof_clause last_cl;
       last_cl)
     else
       let (a,b,c) = get_whole_and_sub_formulas ep in
       let ib1 = mkOther (ImmBuildDef2 last_cl) (Some [Form.neg b;c]) in
       let res1 = mkRes ib1 fproof_clause [] in
       link fproof_clause first_cl;
       link last_cl ib1;
       link ib1 res1;
       res1)
  | Split (fp, f, rule) ->
    let unsplit_clause = visit_formula_proof fp in
    translate_split unsplit_clause rule
(* let hack_replace_atom_op a op = *)


let rec hack_replace_level1_by_op f op =
  pp_form (Form.pform f);
  match Form.pform f with
  (* | Fatom formu -> hack_replace_level1_by_op formu op *)
  | Fapp (fo, _) ->
    negate_formula (Fapp (fo, Array.of_list [op; op]))

(* let handle_lemma = function
 *   | L_CC_Congruence (f, ns)->
 *     (\* let ra = VeritSyntax.ra in
 *      * let rf = VeritSyntax.rf in
 *      * let fakestring = "(= (f z x) (f z y)) (not (= x y)) (not (= z z))" in
 *      * let faketerm = Smtlib2_parse.term Smtlib2_lex.token (Lexing.from_string fakestring) in
 *      * let fakeform = Smtlib2_genConstr.make_root ra rf faketerm in *\)
 *     print_string "\n----- handle_lemma: returned root!";
 *     let (Fatom subform1) = Form.pform (get_subformula f 0) in
 *     let reif = Atom.create () in
 *     let subatom1 = get_first_subatom (Atom.atom subform1) in
 *     (\* let op2 = get_first_subatom subatom1 () in *\)
 *     Atom.to_smt Format.std_formatter subatom1 ;
 *     (\* let subform2 = get_subformula f 9 in
 *      * let changed = hack_replace_level1_by_op subform2 op2 in
 *      * let newns = changed :: ns in *\)
 *     pp_form (Form.pform f);
 *     pp_form (Form.pform f);
 *     pp_form (Form.pform f);
 *     (\* mkOther (EqCgr (f, List.map (fun x -> Some x) newns)) None *\)
 *     mkOther (EqCgr (f, List.map (fun x -> Some x) ns)) None *)

let rec visit_clause_proof  (f : Prooftree_ast.clause_proof) : SmtAtom.Form.t SmtCertif.clause =
  print_string "\npt_to_smtcoq: visit_clause_proof: Begin";
  match f with
  | Resolution (cp1, cp2) ->
    print_string "\n---- RESO!";
    let (cl1 : SmtAtom.Form.t SmtCertif.clause) = visit_clause_proof cp1 in
    let cl2 = visit_clause_proof cp2 in
    let res = mkRes cl1 cl2 [] in
    link cl1 cl2;
    link cl2 res;
    res
  | Clause (fp, f) ->
    print_string "\n----- handle_clause: will return root!";
    visit_formula_proof fp
  (* | Lemma l -> handle_lemma l *)
