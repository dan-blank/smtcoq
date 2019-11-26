open Smtlib2_ast
open SmtAtom

type formula = SmtAtom.Form.t

type tautology_rule = IteRed | ExcludedMiddle1

type rewrite_rule =
  | Rewrite_andToOr
  | EqFalse
  | Rewrite_eqToXor
  | Rewrite_notSimp
  | Rewrite_intern

type split_rule =
  | Split_xor_1
  | Split_xor_2
  | Split_notOr

type equality_proof =
    | Reflexivity          of formula
    | Transitivity         of equality_proof * equality_proof
    | Congruence           of equality_proof * equality_proof
    | Rewrite              of formula * rewrite_rule
    | EDummy

type formula_proof =
  | Tautology          of formula  * tautology_rule
  | Asserted           of formula
  | Equality           of formula_proof * equality_proof
  | Split              of formula_proof * formula  * split_rule
  | FDummy

type lemma =
  | L_CC_Transitivity of formula * formula list
  | L_CC_Congruence of formula * formula list
  (* | L_CC_Congruence of formula *)

type clause_proof =
  | Resolution        of clause_proof * clause_proof
  | Clause            of formula_proof * formula
  | Lemma             of lemma
  | CDummy
