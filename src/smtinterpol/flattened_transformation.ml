open Smtlib2_ast
open Smtlib2_genConstr
open Prooftree_ast

exception FlattenTransformationExpection of string

let translate_specconstant = function
  | SpecConstsDec (_, s)
  | SpecConstNum (_, s)
  | SpecConstString (_, s)
  | SpecConstsHex (_, s)
  | SpecConstsBinary (_, s) -> ()


let translate_symbol = function
  | Symbol (_, s)
  | SymbolWithOr (_, s) -> ()


let translate_identifier = function
  | IdSymbol (_, s) -> translate_symbol s
  | IdUnderscoreSymNum (_, s, (_, l)) ->
    translate_symbol s

let rec translate_sort = function
  | SortIdentifier (_, i) -> translate_identifier i
  | SortIdSortMulti (_, i, (_, ls)) ->
    translate_identifier i

let translate_qualidentifier = function
  | QualIdentifierId (_, i) -> translate_identifier i
  | QualIdentifierAs (_, i, s) ->
    translate_identifier i 

let translate_sortedvar = function
  | SortedVarSymSort (_, v, s) ->
    translate_symbol v

let translate_annotation = function
  | _ -> ()


(* let rec get_first_literal = function
 *   | TermExclamationPt (_, t, _) -> get_first_literal t
 *   | TermQualIdTerm (_, _, t) -> t *)

(* let is_first_literal_function_application? = function
 *     | TermQualIdTerm (_, ) *)

(* let translate_lemma = function
 *   | TermExclimationPt (_, _, _) ->  *)


let rec translate_annotated_proof_term = function
  | TermExclimationPt (_, t, a) ->
    let translated_pt = translate_annotated_proof_term t in 
    let translated_a = translate_annotation a in
    CDummy 
  | TermQualIdTerm (_, i, (_, tl)) ->
    let translated_pt = translate_proof_term (string_of_qualidentifier i,tl) in
    CDummy

and translate_proof_term = function
  | "@res", cps ->
    print_string "Visiting a @res!";
    let translated_cps = List.map translate_annotated_proof_term cps in
    CDummy
  | _, _ ->
    print_string " SOMETHING DIFFERENT! ";
    CDummy

let rec translate_varbinding = function
  | VarBindingSymTerm (_, s, t) ->
    translate_symbol s;
    translate_term t

and translate_term = function
  | TermSpecConst (_, c) ->
    translate_specconstant c;
    CDummy
  | TermQualIdentifier (_, i) ->
    translate_qualidentifier i;
    CDummy
  | TermQualIdTerm (_, i, (_, tl)) ->
    CDummy
  | TermLetTerm (_, (_, vb), t) ->
    raise (FlattenTransformationExpection "Translate Flattened: LetTerms should be eliminated!")
  | TermForAllTerm (_, (_, sv), t) ->
    CDummy
  | TermExistsTerm (_, (_, sv), t) ->
    CDummy
  | TermExclimationPt (_, t, _) -> translate_term t

