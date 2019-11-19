open Prooftree_ast
open SmtAtom
open SmtForm
open SmtTrace
open Printexc
open SmtCertif

exception ProofrulesToSMTCoqExpection of string

let last_root_clause = ref None
let non_root_clauses = ref ([] : SmtAtom.Form.t SmtCertif.clause list)

let store_root_clause cl =
  print_string "\n pt_to_smtcoq: store_root_clauses: BEGIN";
  (match !last_root_clause with
  | Some lcl -> link lcl cl
  | None -> ());
  last_root_clause := Some cl;
  cl

let store_non_root_clause cl =
  print_string "\n pt_to_smtcoq: store_non_root_clause: BEGIN";
  non_root_clauses := cl :: !non_root_clauses;
  cl

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
    (* mkOther (BuildDef formula) None *)
    store_root_clause (mkRootV [formula])
      (* mkRoot *)
  (* | EDummy -> mkRoot *)

let rec visit_formula_proof = function
  (* | Tautology (f, _) -> visit_formula f *)
  | Asserted (f) ->
    Printf.printf ("\n hey Asserted ------------------ \n");
    pp_form (Form.pform f);
    store_root_clause  (mkRootV [f])
  | Equality (fp, ep) ->
    let fproof_clause = visit_formula_proof fp in
    let eproof_clause = visit_equality_proof ep in
    (* link fproof_clause eproof_clause;
     * add_scertifs [(fproof_clause.kind, fproof_clause.value, fproof_clause)] eproof_clause *)
    eproof_clause
  | Split (fp, _, rule) ->
    Printf.printf ("\n hey hey ------------------ \n");
    (* pp_form (Form.pform f); *)
    (* Visit formula proof *)
    let not_xor1_clause = visit_formula_proof fp in
    let split_clause = mkOther (ImmBuildDef not_xor1_clause) None in
    store_non_root_clause split_clause
    (* link not_xor1_clause split_clause;
     * add_scertifs [(not_xor1_clause.kind, not_xor1_clause.value, not_xor1_clause)] split_clause *)
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
    (* add_scertifs [(cl1.kind, cl1.value, cl1); (cl2.kind, cl2.value, cl2)] res *)
    store_non_root_clause res
  | Clause (fp, f) ->
    visit_formula_proof fp
    (* visit_formula f *)
  (* | Lemma (l) -> visit_lemma l *)
  (* | CDummy -> () *)

let add_clauses_after_roots () =
  print_string "pt_to_smtcoq: add_clauses_after_roots: Begin";
  let (Some last_root) = !last_root_clause in
  print_certif Form.to_smt Atom.to_smt last_root ".rootoutput";
  let h :: tl = !non_root_clauses in
  let _ = List.fold_left (fun oc nc -> link oc nc; nc) h tl in
  let prepared_list = List.map (fun cl -> (cl.kind, cl.value, cl)) (h::tl) in
  (* add_scertifs prepared_list last_root *)
  last_root
