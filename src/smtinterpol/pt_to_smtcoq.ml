open Prooftree_ast
open SmtAtom
open SmtForm
open SmtTrace
open Printexc
open SmtCertif

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
  print_string "pt_to_smtcoq: move_before_clause BEGIN";
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
    print_string "\n+#+# scan is called!";
    (match cl.kind with
     | Root -> if !encountered then roots := cl :: !roots else encountered := true
     | _ -> if not !encountered then first_non_root := cl);
    (match cl.next with
     | None ->
       print_string "None in scan";
       ()
     | Some ncl -> scan_clause ncl) in
  scan_clause c;
  print_string ("pt_to_smtcoq: move_roots_to_beginning " ^ (string_of_int (List.length !roots))) ;
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
  print_string ("\n pt_to_smtcoq increment_root id: " ^ (string_of_int c.id) ^ " new_pos: " ^ (string_of_int new_pos));
  match c.kind with
   | Root ->
     c.pos <- Some new_pos;
     print_string ("\n pt_to_smtcoq Middle Root! " ^ (string_of_int new_pos))
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

let rec visit_equality_proof = function
  (* | Reflexivity (f) -> visit_formula f *)
  (* | Transitivity (ep1, ep2) ->
   *   let cl1 = visit_equality_proof ep1 in
   *   let cl2 = visit_equality_proof ep2 in
   *   mkRes cl1 cl2 [] *)
  (* | Congruence (ep1, ep2) ->
   *   (\* visit_equality_proof ep1;
   *    * visit_equality_proof ep2 *\)
   *     mkRoot *)
  | Rewrite (formula, rule) ->
    Printf.printf ("\n hey ho ------------------ \n");
    (* Atom.print_atoms VeritSyntax.ra ".atomsoutput"; *)
    pp_form (Form.pform formula);
    mkOther (BuildDef formula) None
      (* mkRoot *)
  (* | EDummy -> mkRoot *)

let rec visit_formula_proof = function
  (* | Tautology (f, _) -> visit_formula f *)
  | Asserted (f) ->
    Printf.printf ("\n hey Asserted ------------------ \n");
    pp_form (Form.pform f);
    mkRootV [f]
  | Equality (fp, ep) ->
    let fproof_clause = visit_formula_proof fp in
    let eproof_clause = visit_equality_proof ep in
    link fproof_clause eproof_clause;
    eproof_clause
  | Split (fp, _, rule) ->
    Printf.printf ("\n hey hey ------------------ \n");
    (* pp_form (Form.pform f); *)
    (* Visit formula proof *)
    let not_xor1_clause = visit_formula_proof fp in
    let split_clause = mkOther (ImmBuildDef not_xor1_clause) None in
    link not_xor1_clause split_clause;
    split_clause
  (* | FDummy -> mkRoot  *)


(* let visit_lemma = function
 *   | L_CC_Transitivity (f, _, fl) ->
 *     (\* visit_formula f;
 *      * List.iter visit_formula fl; *\)
 *     mkRoot
 *   | L_CC_Congruence (f1, f2, f3, _) ->
 *     (\* visit_formula f1;
 *      * visit_formula f2;
 *      * visit_formula f3; *\)
 *     mkRoot *)
    

let rec visit_clause_proof  (f : Prooftree_ast.clause_proof) : SmtAtom.Form.t SmtCertif.clause =
  print_string "\npt_to_smtcoq: visit_clause_proof: Begin";
  match f with
  | Resolution (cp1, cp2) ->
    let (cl1 : SmtAtom.Form.t SmtCertif.clause) = visit_clause_proof cp1 in
    let cl2 = visit_clause_proof cp2 in
    let res = mkRes cl1 cl2 [] in
    link cl1 cl2;
    link cl2 res;
    res
  | Clause (fp, f) ->
    visit_formula_proof fp
    (* visit_formula f *)
  (* | Lemma (l) -> visit_lemma l *)
  (* | CDummy -> () *)

