open Prooftree_ast
open SmtAtom
open SmtForm
open SmtTrace

let visit_formula = function
  | _ -> SmtTrace.mkRoot

let rec visit_equality_proof = function
  | Reflexivity (f, _) -> visit_formula f
  | Transitivity (ep1, ep2, _) ->
    let cl1 = visit_equality_proof ep1 in
    let cl2 = visit_equality_proof ep2 in
    mkRes cl1 cl2 []
  | Congruence (ep1, ep2, _) ->
    (* visit_equality_proof ep1;
     * visit_equality_proof ep2 *)
    mkRoot
  | Rewrite (f, _, _) -> visit_formula f
  | EDummy -> mkRoot

let rec visit_formula_proof = function
  | Tautology (f, _, _) -> visit_formula f
  | Asserted (f, _) -> mkRootV [f]
  | Equality (fp, ep, _) ->
    (* visit_formula_proof fp;
     * visit_equality_proof ep *)
    mkRoot
  | Split (fp, f, _, _) ->
    (* visit_formula_proof fp;
     * visit_formula f *)
    mkRoot
  | FDummy -> mkRoot 


let visit_lemma = function
  | L_CC_Transitivity (f, _, fl, _) ->
    (* visit_formula f;
     * List.iter visit_formula fl; *)
    mkRoot
  | L_CC_Congruence (f1, f2, f3, _, _) ->
    (* visit_formula f1;
     * visit_formula f2;
     * visit_formula f3; *)
    mkRoot
    

let rec visit_clause_proof  (f : Prooftree_ast.clause_proof) : SmtAtom.Form.t SmtCertif.clause =
  match f with
  | Resolution (cp1, cp2, _) ->
    let cl1 = visit_clause_proof cp1 in
    let cl2 = visit_clause_proof cp2 in
    let res = mkRes cl1 cl2 [] in
    link cl1 cl2;
    link cl2 res;
    res
  | Clause (fp, f, _) ->
    visit_formula_proof fp
    (* visit_formula f *)
  | Lemma (l, _) -> visit_lemma l
  (* | CDummy -> () *)
