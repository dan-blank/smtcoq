open Smtlib2_ast
open Smtlib2_genConstr
open Prooftree_ast
open SmtForm
open SmtAtom
open Tabulation

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
  | _ -> ""


(* let rec get_first_literal = function
 *   | TermExclamationPt (_, t, _) -> get_first_literal t
 *   | TermQualIdTerm (_, _, t) -> t *)

(* let is_first_literal_function_application? = function
 *     | TermQualIdTerm (_, ) *)

(* let translate_lemma = function
 *   | TermExclimationPt (_, _, _) ->  *)

let string_of_single_atttribute = function
  | (_, [AttributeKeyword (_, s)]) -> s

let translate_split_annotation = function
  | ":xor-1" -> Split_xor_1
  | ":xor-2" -> Split_xor_2
  | ":notOr" -> Split_notOr

let translate_rewrite_annotation = function
  | ":eqToXor" -> Rewrite_eqToXor
  | ":andToOr" -> Rewrite_andToOr
  | ":notSimp" -> Rewrite_notSimp
  | ":intern" -> Rewrite_intern

let translate_annotated_formula_term term annotation =
  match term with
  | t ->
    let ra = VeritSyntax.ra in
    let rf = VeritSyntax.rf in
    Smtlib2_genConstr.make_root ra rf t

let get_execption pv =
  print_string "\n FT: get_execption";
  match pv with
  | Some v -> v
  | None -> raise (FlattenTransformationExpection "term_to_proofrules: Invalid Option!")

let rec translate_annotated_eproof_term term (closest_annotation: (Smtlib2_ast.loc * Smtlib2_ast.attribute list) option) =
  match term with
  | TermExclimationPt (_, t, a) ->
    print_string "\n FT: translate_annotated_eproof_term => TermExplimationPt";
    translate_annotated_eproof_term t (Some a)
  | TermQualIdTerm (_, i, (_, tl)) ->
    print_string "\n FT: translate_annotated_eproof_term => TermQualIdTerm";
    translate_eproof_term (string_of_qualidentifier i,tl) closest_annotation

and translate_eproof_term termcontext (annotation : (Smtlib2_ast.loc * Smtlib2_ast.attribute list) option) =
  let (str,_) = termcontext in
  print_string ("\n new eproof: " ^ str);
  match termcontext with
  (* | "@rewrite", [TermExclimationPt (_, TermQualIdTerm (_, _, (_, from :: goal :: _)), rewrite_annotation)] -> *)
  | "@rewrite", [TermExclimationPt (_, g, rewrite_annotation)] ->
    print_string "\n FT: translate_eproof_term => @rewrite";
    (* Format.fprintf Format.std_formatter "\n ACHTUNG ACHTUNG HIER IST DIE ANNOTATION!! \n";
     * print_string (string_of_single_atttribute (get_execption annotation)); *)
    (* print_term Format.std_formatter annotation; *)
    let f = translate_annotated_formula_term g None in
    (* let g = translate_annotated_formula_term goal None in *)
    print_string "\n FT: AFTER f";
    let a = translate_rewrite_annotation (string_of_single_atttribute rewrite_annotation) in
    print_string "\n FT: AFTER a";
    (* let reif = Form.create () in
     * let new_form = Form.get reif (Fapp (For, Array.of_list [g ; f])) in
     * Form.to_smt Atom.to_smt Format.std_formatter new_form; *)
    Rewrite (f, a)
  | "@cong", [ep1_term; ep2_term] ->
    let ep1 = translate_annotated_eproof_term ep1_term None in
    let ep2 = translate_annotated_eproof_term ep2_term None in
    Congruence (ep1, ep2)
  | "@refl", [formula_term] ->
    let formula = translate_annotated_formula_term formula_term None in
    Reflexivity formula


let rec translate_annotated_fproof_term term (closest_annotation: (Smtlib2_ast.loc * Smtlib2_ast.attribute list) option) =
  match term with
  | TermExclimationPt (_, t, a) ->
    print_string "\n FT: translate_annotated_fproof_term => TermExplimationPt";
    translate_annotated_fproof_term t (Some a)
  | TermQualIdTerm (_, i, (_, tl)) ->
    print_string "\n FT: translate_annotated_fproof_term => TermQualIdTerm";
    translate_fproof_term (string_of_qualidentifier i,tl) closest_annotation

and translate_fproof_term termcontext (annotation : (Smtlib2_ast.loc * Smtlib2_ast.attribute list) option) =
  match termcontext with
  | "@asserted", [formula_term] ->
    print_string "\n FT: translate_fproof_term => @asserted";
    (* print_string "Visiting a @asserted!"; *)
    let f = translate_annotated_formula_term formula_term None in
    Asserted f
  | "@split", [TermExclimationPt (_, formula_proof_term, split_annotation); formula_term] ->
    print_string "\n FT: translate_fproof_term => @split";
    let fp = translate_annotated_fproof_term formula_proof_term annotation in
    let f = translate_annotated_formula_term formula_term None in
    let a = translate_split_annotation (string_of_single_atttribute split_annotation) in
    Split (fp, f, a)
  | "@eq", [formula_proof_term; equality_proof_term] ->
    print_string "\n FT: translate_fproof_term => @eq";
    let fp = translate_annotated_fproof_term formula_proof_term annotation in
    let ep = translate_annotated_eproof_term equality_proof_term annotation in
    Equality (fp, ep)
  | _, _ ->
    (* print_string " SOMETHING DIFFERENT! "; *)
    raise (FlattenTransformationExpection "Formulaproof not supported yet!")
    (* FDummy *)

let is_equality_term t =
  Hashtbl.clear term_table; false

let attribute_value_to_termlist av = []

let construct_cc_lemma t _ =
  match t with
  | TermQualIdTerm (_, _, (_, h::tl)) ->
    let main_form = translate_annotated_formula_term h None in
    let neg_forms = List.map (fun fterm -> translate_annotated_formula_term fterm None) tl in
    L_CC_Congruence (main_form, neg_forms)
  (*   match attribute_value_to_termlist av with
   * | h :: tl ->
   *   let congruence_formula = translate_annotated_formula_term h h in
   *   let path_formulas = List.map (fun lt -> translate_annotated_formula_term lt lt) tl in
   *   if is_equality_term h
   *   then
   *     L_CC_Transitivity (congruence_formula, path_formulas)
   *   else
   *     L_CC_Congruence (congruence_formula, path_formulas)
   * | [] -> raise (FlattenTransformationExpection "Error: CCLemma has no attibutes!") *)


let handle_lemma_term t a =
  match a with
  | [AttributeKeywordValue (_, ":CC", av)] -> construct_cc_lemma t av


let rec translate_annotated_clause_proof_term (term : Smtlib2_ast.term) (closest_annotation : (Smtlib2_ast.loc * (Smtlib2_ast.attribute list)) option) =
  match term with
  | TermExclimationPt (_, t, a) ->
    print_string "\n FT: translate_annotated_clause_proof_term => TermExplimationPt";
    translate_annotated_clause_proof_term t (Some a)
  | TermQualIdTerm (_, i, (_, tl)) ->
    print_string "\n FT: translate_annotated_clause_proof_term => TermQualIdTerm";
    translate_clause_proof_term (string_of_qualidentifier i,tl) closest_annotation 

and translate_clause_proof_term termcontext annotation =
  match termcontext with
  | "@res", clause_proof_terms ->
    (* print_string "Visiting a @res!"; *)
    let head_clause :: cls = List.map (fun clp -> translate_annotated_clause_proof_term clp None) clause_proof_terms in
    List.fold_left (fun acc cl -> Resolution (acc, cl)) head_clause cls
  | "@clause", [fpterm; fterm] ->
    (* print_string "Visiting a @clause!"; *)
    let fp = translate_annotated_fproof_term fpterm annotation in
    let f = translate_annotated_formula_term fterm annotation in
    Clause (fp, f)
  | "@lemma", [TermExclimationPt (_, t, (_, al))] ->
    Lemma (handle_lemma_term t al)

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

