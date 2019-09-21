open Smtlib2_ast
open SmtAtom

type formula = DummyFormula

type tautology_rule = IteRed | ExcludedMiddle1

type rewrite_rule = AndToOr | EqFalse

type split_rule = XXX

type equality_proof =
    | Reflexivity          of formula * string
    | Transitivity         of equality_proof * equality_proof * string
    | Congruence           of equality_proof * equality_proof * string
    | Rewrite              of formula * rewrite_rule * string
    | EDummy        
    
type formula_proof =
  | Tautology          of formula  * tautology_rule * string
  | Asserted           of formula  * string
  | Equality           of formula_proof * equality_proof * string
  | Split              of formula_proof * formula  * split_rule * string
  | FDummy         

type lemma =
  | L_CC_Transitivity of formula * formula * formula list * string
  | L_CC_Congruence of formula * formula * formula * formula * string

type clause_proof =
  | Resolution        of clause_proof * clause_proof * string
  | Clause            of formula_proof * formula * string
  | Lemma             of lemma  * string
  | CDummy        
