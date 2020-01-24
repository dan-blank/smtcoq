open Smtlib2_ast
open Format
open Modified_smtlib2_printing

(* This table contains terms that result from tabulating the initial SMTInterpol proof. It contains no let terms and no SexprInParens.   *)
let term_table : (string, term) Hashtbl.t = Hashtbl.create 17 

(* A counter to ensure that terms in term_table introduced by attributes have a unique name. *)
let attribute_counter = ref 0


(******************************************************************************)
(* Helper functions.                                                           *)
(******************************************************************************)

let string_of_symbol = function
  | Symbol (_, s) -> s
let get_corresponding_term_default symbol default =
  let result = Hashtbl.find_all term_table (string_of_symbol symbol) in
  match result with
   | [t] -> t
   | [] -> default

let fresh_attribute_symbol_string () =
  let attribute_counter_string = string_of_int !attribute_counter in
  incr attribute_counter;
  String.concat "" [".ats" ; attribute_counter_string]

let dummyloc = (Lexing.dummy_pos, Lexing.dummy_pos)

let fresh_attribute_symbol () = Symbol (dummyloc, fresh_attribute_symbol_string ())

let fresh_attribute_sexpr () = SexprSymbol (dummyloc, fresh_attribute_symbol ())

let string_of_identifier = function
  | IdSymbol (_, (Symbol (_, s))) -> s
let symbol_of_identifier = function
  | IdSymbol (_, s) -> s
let string_of_qualidentifier = function
  | QualIdentifierId (_, i) -> string_of_identifier i
let symbol_of_qualidentifier = function
  | QualIdentifierId (_, i) -> symbol_of_identifier i
let sexpr_to_string sexpr =
  let strformater = Format.str_formatter in
  print_sexpr strformater sexpr;
  flush_str_formatter ()

let parse_sexpr_as_term (sexpr : Smtlib2_ast.sexpr) : Smtlib2_ast.term =
  match sexpr with
  | s ->
    let sexpr_string = sexpr_to_string s in
    (* Printf.printf "\n woah so: %s" sexpr_string; *)
    Smtlib2_parse.term Smtlib2_lex.token (Lexing.from_string sexpr_string)

let transform_sexpr_to_term_and_return_symbol sexpr =
  let transformed_sexpr = parse_sexpr_as_term sexpr in
  let SexprSymbol(l, s) = fresh_attribute_sexpr () in
  Hashtbl.add term_table (string_of_symbol s) transformed_sexpr;
  SexprSymbol(l,s)

let transform_sexpr_in_paren = function
  | SexprInParen (l1, (l2, sl)) ->
    (* Printf.printf "\n: transform sepr list %i" (List.length sl); *)
    SexprInParen (l1, (l2, List.map transform_sexpr_to_term_and_return_symbol sl))

(* Given a tuple of a String keyword and a sexpr attribute-value, transform any term in that attribute-value into a symbol. Any term transformed this way is put into the termtable. Return an attribute-value where every occurrence of an term is replaced by the corresponding symbol.*)
let flatten_attribute_keyword_value_sexpr = function
  | ":CC", AttributeValSexpr (l1, (l2, [at ; a; sl])) ->
    let tabulated_annotated_term = transform_sexpr_to_term_and_return_symbol at in
    let tabulated_sexpr_list = transform_sexpr_in_paren sl in
    AttributeValSexpr (l1, (l2, [tabulated_annotated_term  ; a ; tabulated_sexpr_list]))
  | ":pivot", AttributeValSexpr (l1, (l2, _ :: t :: _)) ->
    let tabulated_annotated_term = transform_sexpr_to_term_and_return_symbol t in
    AttributeValSexpr (l1, (l2, [tabulated_annotated_term]))
  | s, _ -> Printf.printf "\nFailing at: %s" s; assert false

(******************************************************************************)
(* Tabulate functions that visit values defined in SmtLib2_ast.                *)
(******************************************************************************)

let tabulate_attribute_value annotation_name = function
  | AttributeValSpecConst (_, _) as wav -> wav
  | AttributeValSymbol (_, _) as wav -> wav
  | AttributeValSexpr (l1, (l2, sl)) as avs ->
    flatten_attribute_keyword_value_sexpr (annotation_name, avs)

let tabulate_attribute = function
  | AttributeKeyword (_, _) as wa -> wa
  | AttributeKeywordValue (l1, an, av) ->
    let tabulated_attribute_value = tabulate_attribute_value an av in
    AttributeKeywordValue (l1, an, tabulated_attribute_value)


let rec tabulate_varbinding = function
  | VarBindingSymTerm (_, s, t) ->
    (* let tabulate_term t 
     * let tabulated_term = get_corresponding_term_default s t in *)
    Hashtbl.add term_table (string_of_symbol s) (tabulate_term t)
(*TODO Apply to subterms too!*)
and tabulate_term = function
  | TermSpecConst (_, c) as wt -> wt
  | TermQualIdTerm (l1, i, (l2, tl)) as wt ->
    let tabulated_terms = List.map tabulate_term tl in
    TermQualIdTerm (l1, i, (l2, tabulated_terms))
  | TermQualIdentifier (l, i) when String.get (string_of_qualidentifier i) 0 == '.'->
    get_corresponding_term_default (symbol_of_qualidentifier i) (TermQualIdentifier (l,i))
  | TermQualIdentifier (_, _) as wt -> wt
  | TermLetTerm (_, (_, vb), t) ->
    List.iter (tabulate_varbinding) vb;
    tabulate_term t
  | TermExistsTerm (_, (_, sv), t) as wt -> wt
  | TermExclimationPt (loc, t, (loc2, al)) as wt ->
    let tabulated_subterm = tabulate_term t in
    let tabulated_attributes = List.map tabulate_attribute al in
    TermExclimationPt (loc, tabulated_subterm, (loc2, tabulated_attributes))


(* Given an proof of type term, create two tables containg the preprocessed terms and term lists. *)
let tabulate_proof proof =
  let main_term = tabulate_term proof in
  Hashtbl.add term_table ".mainproof" main_term
