open Prooftree_ast
open SmtAtom
open SmtForm


let visit_formula = function
  | DummyFormula -> ()

let rec visit_equality_proof = function
  | Reflexivity (f, _) -> visit_formula f
  | Transitivity (ep1, ep2, _) ->
    visit_equality_proof ep1;
    visit_equality_proof ep2
  | Congruence (ep1, ep2, _) ->
    visit_equality_proof ep1;
    visit_equality_proof ep2
  | Rewrite (f, _, _) -> visit_formula f
  | EDummy -> ()

let rec visit_formula_proof = function
  | Tautology (f, _, _) -> visit_formula f
  | Asserted (f, _) -> visit_formula f
  | Equality (fp, ep, _) ->
    visit_formula_proof fp;
    visit_equality_proof ep
  | Split (fp, f, _, _) ->
    visit_formula_proof fp;
    visit_formula f
  | FDummy -> ()


let visit_lemma = function
  | L_CC_Transitivity (f, _, fl, _) ->
    visit_formula f;
    List.iter visit_formula fl
  | L_CC_Congruence (f1, f2, f3, _, _) ->
    visit_formula f1;
    visit_formula f2;
    visit_formula f3
    

let rec visit_clause_proof = function
  | Resolution (cp1, cp2, _) ->
    visit_clause_proof cp1;
    visit_clause_proof cp2
  | Clause (fp, f, _) ->
    visit_formula_proof fp;
    visit_formula f
  | Lemma (l, _) -> visit_lemma l
  | CDummy -> ()
