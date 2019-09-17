open Smtlib2_ast
open Format
open Modified_smtlib2_printing

(* This table holds smt terms that were either introduced by a let-term or a contained in an attribute. *)
let flattened_table : (symbol, term) Hashtbl.t = Hashtbl.create 17 
(* A counter to ensure that terms in flattened_table introduced by attributes have a unique name. *)
let attribute_counter = ref 0


let fresh_attribute_symbol_string () =
  let attribute_counter_string = string_of_int !attribute_counter in
  incr attribute_counter;
  String.concat "" [".ats" ; attribute_counter_string]

let dummyloc = (Lexing.dummy_pos, Lexing.dummy_pos)

let fresh_attribute_symbol () = Symbol (dummyloc, fresh_attribute_symbol_string ())

let fresh_attribute_sexpr () = SexprSymbol (dummyloc, fresh_attribute_symbol ())


let sexpr_to_string sexpr =
  let strformater = Format.str_formatter in
  print_sexpr strformater sexpr;
  flush_str_formatter ()

let parse_sexpr_as_term = function
  | s ->
    let strformater = Format.str_formatter in
    print_sexpr strformater s;
    let sexpr_string = flush_str_formatter () in
    Smtlib2_parse.term Smtlib2_lex.token (Lexing.from_string sexpr_string)

let transform_sexpr_to_term_and_return_symbol sexpr =
  let transformed_sexpr = parse_sexpr_as_term sexpr in
  let SexprSymbol(l, s) = fresh_attribute_sexpr () in
  Hashtbl.add flattened_table s transformed_sexpr;
  SexprSymbol(l,s)

let transform_sexpr_list = function
  | sl -> List.map transform_sexpr_to_term_and_return_symbol sl

(* Given a tuple of a String keyword and a sexpr attribute-value, transform any term in that attribute-value into a symbol. Any term transformed this way is put into the termtable. Return an attribute-value where every occurrence of an term is replaced by the corresponding symbol.*)
let flatten_attribute_keyword_value_sexpr = function
  | ":CC", AttributeValSexpr (l1, (l2, at :: a :: sl)) ->
    let flattened_annotated_term = transform_sexpr_to_term_and_return_symbol at in
    let flattened_sexpr_list = transform_sexpr_list sl in
    AttributeValSexpr (l1, (l2, at :: a :: flattened_sexpr_list))


let visit_attribute_value annotation_name = function
  | AttributeValSpecConst (_, _) as wav -> wav
  | AttributeValSymbol (_, _) as wav -> wav
  | AttributeValSexpr (l1, (l2, sl)) as avs ->
    flatten_attribute_keyword_value_sexpr (annotation_name, avs)

let visit_attribute = function
  | AttributeKeyword (_, _) as wa -> wa
  | AttributeKeywordValue (l1, an, av) ->
    let flattened_attribute_value = visit_attribute_value an av in
    AttributeKeywordValue (l1, an, flattened_attribute_value)


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
  | TermExistsTerm (_, (_, sv), t) as wt -> wt
  | TermExclimationPt (loc, t, (loc2, al)) as wt ->
    let flattened_subterm = visit_term t in
    let flattened_attributes = List.map visit_attribute al in
    TermExclimationPt (loc, flattened_subterm, (loc2, flattened_attributes))
