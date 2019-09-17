open Smtlib2_ast

let flattened_table : (symbol, term) Hashtbl.t = Hashtbl.create 17 

(* let visit_qualidentifier fmt = function
 *   | QualIdentifierId (_, i) -> visit_identifier fmt i
 *   | QualIdentifierAs (_, i, s) ->
 *     Format.fprintf fmt "(%a as %a)"
 *       visit_identifier i visit_sort s
 * 
 * let visit_sortedvar fmt = function
 *   | SortedVarSymSort (_, v, s) ->
 *     Format.fprintf fmt "(%a %a)" visit_symbol v visit_sort s *)

(* let sexpr_to_term = function
 *   | s -> s
 * 
 * let flatten_sexpr sexpr = function
 *   | ":pivot" ->
 *     let transformed_sexpr = sexpr_to_term sexpr in
 *     let fresh_attribute_symbol = fresh_attribute_symbol in
 *     Hashtbl.add flattened_table fresh_attribute_symbol transformed_sexpr;
 *     fresh_attribute_symbol *)

let visit_attribute_value annotation_name = function
  | AttributeValSpecConst (_, _) as wav -> wav
  | AttributeValSymbol (_, _) as wav -> wav
  | AttributeValSexpr (l1, (l2, sl)) ->
    (* let flattened_sexpr = flatten annotation_name sexpr in *)
    AttributeValSexpr (l1, (l2, sl))

let visit_attribute = function
  | AttributeKeyword (_, _) as wa -> wa
  | AttributeKeywordValue (l1, an, av) ->
    let flattened_attribute_value = visit_attribute_value an in
    (* AttributeKeywordValue (l1, an, flattened_attribute_value) *)
    AttributeKeywordValue (l1, an, av)


let rec visit_varbinding = function
  | VarBindingSymTerm (_, s, t) -> Hashtbl.add flattened_table s t

and visit_term = function
  | TermSpecConst (_, c) as wt -> wt
  | TermQualIdTerm (l1, i, (l2, tl)) as wt ->
    let flattened_terms = List.map visit_term tl in
    TermQualIdTerm (l1, i, (l2, flattened_terms))
  | TermQualIdentifier (_, i) as wt -> wt
  | TermLetTerm (_, (_, vb), t) ->
    List.iter (visit_varbinding) vb;
    visit_term t
  (* Format.fprintf fmt "(let (";
     * List.iter (Format.fprintf fmt " %a" visit_varbinding) vb;
     * Format.fprintf fmt ") %a)" visit_term t *)
  | TermExistsTerm (_, (_, sv), t) as wt -> wt
  | TermExclimationPt (loc, t, (loc2, al)) as wt ->
    let flattened_subterm = visit_term t in
    let flattened_attributes = List.map visit_attribute al in
    TermExclimationPt (loc, flattened_subterm, (loc2, flattened_attributes))
