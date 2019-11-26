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
   | _ -> assert false);
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

let move_roots_to_beginning c =

  let encountered = ref false in
  let roots = ref [] in
  let first_non_root = ref c in
  (* let scan_clause non_root_was_encountered roots_after_non_root first_non_root *)
  let rec scan_clause cl =
    (* print_string "\n+#+# scan is called!"; *)
    (match cl.kind with
     | Root -> if !encountered then roots := cl :: !roots else encountered := true
     | _ -> if not !encountered then first_non_root := cl);
    (match cl.next with
     | None ->
       (* print_string "None in scan"; *)
       ()
     | Some ncl -> scan_clause ncl) in
  scan_clause c;
  (* print_string ("pt_to_smtcoq: move_roots_to_beginning " ^ (string_of_int (List.length !roots))) ; *)
  List.iter (fun root_to_move -> move_before_clause root_to_move !first_non_root) !roots

let rec get_first c =
  match c.prev with
  | Some p -> get_first p
  | None -> c

let rec get_last c =
  match c.next with
  | Some n -> get_last n
  | None -> c

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

let translate_rewrite rewritee_clause rewrite_rule rewrite_formula =
  let eq_as_iff = get_subformula rewrite_formula 0 in
  let eq_as_target = get_subformula rewrite_formula 1 in
  let a = get_subformula eq_as_iff 0 in
  let b = get_subformula eq_as_iff 1 in
  let clauses = ref [rewritee_clause] in
  (match rewrite_rule with
  | Rewrite_eqToXor ->
    let bd1 = mkOther (BuildDef eq_as_target) None in
    let bd2 = mkOther (BuildDef2 eq_as_target) None in
    let id1 = mkOther (ImmBuildDef rewritee_clause) None in 
    let id2 = mkOther (ImmBuildDef2 rewritee_clause) None in
    let res1 = mkRes bd1 id1 [] in
    let res2 = mkRes bd2 id2 [res1] in
    clauses := List.append !clauses [bd1; bd2; id1; id2; res1; res2;]
    (* res2 *)
  | Rewrite_andToOr ->
    let bd1 = mkOther (BuildDef eq_as_target) None in
    let id1 = mkOther (ImmBuildProj (rewritee_clause, 0)) None in
    let id2 = mkOther (ImmBuildProj (rewritee_clause, 1)) None in
    let res = mkRes bd1 id1 [id2] in
    clauses := List.append !clauses [bd1; id1; id2; res]
  | Rewrite_notSimp ->
    let simpl1 = mkOther (ImmFlatten (rewritee_clause, eq_as_target)) None in
    clauses := List.append !clauses [simpl1]
  | Rewrite_intern -> ()
  );
    (* simpl1 *)
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
    let eproof_clause = visit_equality_proof ep fproof_clause in
    eproof_clause
  | Split (fp, f, rule) ->
    let unsplit_clause = visit_formula_proof fp in
    translate_split unsplit_clause rule

let handle_lemma = function
  | L_CC_Congruence (f, _)->
    (* let ra = VeritSyntax.ra in
     * let rf = VeritSyntax.rf in
     * let fakestring = "(= (f z x) (f z y)) (not (= x y)) (not (= z z))" in
     * let faketerm = Smtlib2_parse.term Smtlib2_lex.token (Lexing.from_string fakestring) in
     * let fakeform = Smtlib2_genConstr.make_root ra rf faketerm in *)
    print_string "\n----- handle_lemma: returned root!";
    pp_form (Form.pform f);
    mkRootV [f]

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
  | Lemma l -> handle_lemma l
