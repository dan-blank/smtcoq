open Smtlib2_ast
open Format
open Smtinterpol_util

(* TODO
   X check for further inlining
   X revisit newly created terms
   commenting function
   variable names
   module purpose
   import

*)

(* This table contains terms that result from tabulating the initial SMTInterpol proof. It contains no let terms and no SexprInParens.   *)
let term_table : (string, term) Hashtbl.t = Hashtbl.create 17 

(* A counter to ensure that terms in term_table introduced by attributes have a unique name. *)
let attribute_counter = ref 0

(******************************************************************************)
(* Helper functions.                                                          *)
(******************************************************************************)



(******************************************************************************)
(* Tabulate functions that visit values defined in SmtLib2_ast.                *)
(******************************************************************************)



(** Transform an sexpr into a term and return the symbol that represents that term in term_table. *)
let rec sexpr_to_term sexpr =
  let attribute_counter_string = string_of_int !attribute_counter in
  incr attribute_counter;
  let fresh_attribute_symbol_string = String.concat "" [".ats" ; attribute_counter_string] in
  let dummyloc = (Lexing.dummy_pos, Lexing.dummy_pos) in
  let fresh_attribute_symbol () = Symbol (dummyloc, fresh_attribute_symbol_string) in
  let fresh_attribute_sexpr () = SexprSymbol (dummyloc, fresh_attribute_symbol ()) in
  let strformater = Format.str_formatter in
  print_sexpr strformater sexpr;
  let sexpr_string = flush_str_formatter () in
  let transformed_sexpr = Smtlib2_parse.term Smtlib2_lex.token (Lexing.from_string sexpr_string) in
  let SexprSymbol(l, s) = fresh_attribute_sexpr () in
  Hashtbl.add term_table (string_of_symbol s) (tabulate_term transformed_sexpr);
  SexprSymbol(l,s)

(** Given an attribute value that contains sexprs that represent terms, add those terms to term_table and replace their
sexpr representation with the symbol that map to the term in term_table. *)
and tabulate_attribute_value_sexpr =
  let tabulate_sexprs_in_paren (SexprInParen (l1, (l2, sexpr))) = SexprInParen (l1, (l2, List.map sexpr_to_term sexpr)) in
  function
  | ":CC", AttributeValSexpr (l1, (l2, [at ; a; sexpr])) ->
    let annotated_term = sexpr_to_term at in
    let tabulated_sexpr = tabulate_sexprs_in_paren sexpr in
    AttributeValSexpr (l1, (l2, [annotated_term; a; tabulated_sexpr]))
  | ":pivot", AttributeValSexpr (l1, (l2, _ :: t :: _)) ->
    let annotated_term = sexpr_to_term t in
    AttributeValSexpr (l1, (l2, [annotated_term]))
  | s, _ -> Printf.printf "\nFailing at: %s" s; assert false
and tabulate_attribute_value annotation_name = function
  | AttributeValSpecConst (_, _) as wav -> wav
  | AttributeValSymbol (_, _) as wav -> wav
  | AttributeValSexpr (l1, (l2, sexpr)) as avs ->
    tabulate_attribute_value_sexpr (annotation_name, avs)
and tabulate_attribute = function
  | AttributeKeyword (_, _) as wa -> wa
  | AttributeKeywordValue (l1, an, av) ->
    let tabulated_attribute_value = tabulate_attribute_value an av in
    AttributeKeywordValue (l1, an, tabulated_attribute_value)
and tabulate_varbinding = function
  | VarBindingSymTerm (_, s, t) ->
    Hashtbl.add term_table (string_of_symbol s) (tabulate_term t)
and tabulate_term = function
  | TermSpecConst (_, c) as wt -> wt
  | TermQualIdTerm (l1, i, (l2, tl)) as wt ->
    let tabulated_terms = List.map tabulate_term tl in
    TermQualIdTerm (l1, i, (l2, tabulated_terms))
  | TermQualIdentifier (l, i) when String.get (string_of_qualidentifier i) 0 == '.'->
    Hashtbl.find term_table (string_of_symbol (symbol_of_qualidentifier i)) 
  | TermQualIdentifier (_, _) as wt -> wt
  | TermLetTerm (_, (_, vb), t) ->
    List.iter (tabulate_varbinding) vb;
    tabulate_term t
  | TermExistsTerm (_, (_, sv), t) as wt -> wt
  | TermExclimationPt (loc, t, (loc2, al)) as wt ->
    let tabulated_subterm = tabulate_term t in
    let tabulated_attributes = List.map tabulate_attribute al in
    TermExclimationPt (loc, tabulated_subterm, (loc2, tabulated_attributes))

(* Given a tuple of a String keyword and a sexpr attribute-value, transform any term in that attribute-value into a symbol. Any term transformed this way is put into the termtable. Return an attribute-value where every occurrence of an term is replaced by the corresponding symbol.*)

(* Given an proof of type term, create two tables containg the preprocessed terms and term lists. *)
let tabulate_proof proof =
  let main_term = tabulate_term proof in
  Hashtbl.add term_table ".mainproof" main_term
