open Smtlib2_ast
open Prooftree_ast
open Tabulation

let string_of_single_atttribute = function
  | (_, [AttributeKeyword (_, s)]) -> s

let from_split_annotation = function
  | ":xor-1" -> Split_xor_1
  | ":xor-2" -> Split_xor_2
  | ":notOr" -> Split_notOr

let from_rewrite_annotation = function
  | ":eqToXor" -> Rewrite_eqToXor
  | ":andToOr" -> Rewrite_andToOr
  | ":notSimp" -> Rewrite_notSimp
  | ":intern" -> Rewrite_intern

let from_annotated_formula term annotation =
  match term with
  | t ->
    let ra = VeritSyntax.ra in
    let rf = VeritSyntax.rf in
    Smtlib2_genConstr.make_root ra rf t


let rec from_annotated_eproof term (closest_annotation: (Smtlib2_ast.loc * Smtlib2_ast.attribute list) option) =
  match term with
  | TermExclimationPt (_, t, a) ->
    from_annotated_eproof t (Some a)
  | TermQualIdTerm (_, i, (_, tl)) ->
    from_eproof (string_of_qualidentifier i,tl) closest_annotation

and from_eproof termcontext (annotation : (Smtlib2_ast.loc * Smtlib2_ast.attribute list) option) =
  let (str,_) = termcontext in
  match termcontext with
  | "@rewrite", [TermExclimationPt (_, g, rewrite_annotation)] ->
    let f = from_annotated_formula g None in
    let a = from_rewrite_annotation (string_of_single_atttribute rewrite_annotation) in
    Rewrite (f, a)
  | "@cong", [ep1_term; ep2_term] ->
    let ep1 = from_annotated_eproof ep1_term None in
    let ep2 = from_annotated_eproof ep2_term None in
    Congruence (ep1, ep2)
  | "@trans", [ep1_term; ep2_term] ->
    let ep1 = from_annotated_eproof ep1_term None in
    let ep2 = from_annotated_eproof ep2_term None in
    Transitivity (ep1, ep2)
  | "@refl", [formula_term] ->
    let formula = from_annotated_formula formula_term None in
    Reflexivity formula


let rec from_annotated_fproof term closest_annotation =
  match term with
  | TermExclimationPt (_, t, a) ->
    from_annotated_fproof t (Some a)
  | TermQualIdTerm (_, i, (_, tl)) ->
    from_fproof (string_of_qualidentifier i,tl) closest_annotation

and from_fproof termcontext annotation =
  match termcontext with
  | "@asserted", [formula_term] ->
    let f = from_annotated_formula formula_term None in
    Asserted f
  | "@split", [TermExclimationPt (_, formula_proof_term, split_annotation); formula_term] ->
    let fp = from_annotated_fproof formula_proof_term annotation in
    let f = from_annotated_formula formula_term None in
    let a = from_split_annotation (string_of_single_atttribute split_annotation) in
    Split (fp, f, a)
  | "@eq", [formula_proof; equality_proof] ->
    let fp = from_annotated_fproof formula_proof annotation in
    let ep = from_annotated_eproof equality_proof annotation in
    Equality (fp, ep)


let construct_cc_lemma t _ =
  match t with
  | TermQualIdTerm (_, _, (_, h::tl)) ->
    let main_form = from_annotated_formula h None in
    let neg_forms = List.map (fun fterm -> from_annotated_formula fterm None) tl in
    L_CC_Congruence (main_form, neg_forms)

let handle_lemma t a =
  match a with
  | [AttributeKeywordValue (_, ":CC", av)] -> construct_cc_lemma t av

let rec from_annotated_clause_proof term closest_annotation =
  match term with
  | TermExclimationPt (_, t, a) ->
    from_annotated_clause_proof t (Some a)
  | TermQualIdTerm (_, i, (_, tl)) ->
    from_clause_proof (string_of_qualidentifier i,tl) closest_annotation 

and from_clause_proof termcontext annotation =
  match termcontext with
  | "@res", clause_proof_terms ->
    let head_clause :: cls = List.map (fun clp -> from_annotated_clause_proof clp None) clause_proof_terms in
    List.fold_left (fun acc cl -> Resolution (acc, cl)) head_clause cls
  | "@clause", [fpterm; fterm] ->
    let fp = from_annotated_fproof fpterm annotation in
    let f = from_annotated_formula fterm annotation in
    Clause (fp, f)
  | "@lemma", [TermExclimationPt (_, t, (_, al))] ->
    Lemma (handle_lemma t al)

