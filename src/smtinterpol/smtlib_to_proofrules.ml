open Smtlib2_ast
open Prooftree_ast
open Tabulation
open Proofrules_to_clauses
open SmtAtom

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

let from_formula term =
    let ra = VeritSyntax.ra in
    let rf = VeritSyntax.rf in
    let r = Smtlib2_genConstr.make_root ra rf term in
    (* Printf.printf "\n ";
     * Form.to_smt Atom.to_smt Format.std_formatter r; *)
    r


(** Given a term that represents an equality proof, return the corresponding term in the IR format. *)
let rec from_eproof rulename bodyterm =
  let eproof_from_qualidterm = (fun (TermQualIdTerm (_, i, (_, t))) -> from_eproof (string_of_qualidentifier i) t) in
  match rulename, bodyterm with
  | "@rewrite", [TermExclimationPt (_, g, rewrite_annotation)] ->
    (* Printf.printf "Rewrite Formula"; *)
    let f = from_formula g in
    (* Printf.printf "\n rewrite formula";
     * Form.to_smt Atom.to_smt Format.std_formatter f; *)
    let a = from_rewrite_annotation (string_of_single_atttribute rewrite_annotation) in
    Rewrite (f, a)
  | "@cong", equality_proof_terms ->
    let h :: es = List.map eproof_from_qualidterm equality_proof_terms in
    List.fold_left (fun acc el -> Congruence (acc, el)) h es
  | "@trans", equality_proof_terms ->
    let h :: es = List.map eproof_from_qualidterm equality_proof_terms in
    List.fold_left (fun acc el -> Transitivity (acc, el)) h es
  | "@refl", [formula_term] ->
    let formula = from_formula formula_term in
    Reflexivity formula

and from_fproof rulename bodyterm =
  match rulename, bodyterm with
  | "@asserted", [formula_term] ->
    let f = from_formula formula_term in
    Asserted f
  | "@split", [TermExclimationPt (_, TermQualIdTerm (_, i, (_, targs)), split_annotation); formula_term] ->
    let fp = from_fproof (string_of_qualidentifier i) targs in
    let f = from_formula formula_term in
    let a = from_split_annotation (string_of_single_atttribute split_annotation) in
    Split (fp, f, a)
  | "@eq", [TermQualIdTerm (_, i1, (_, targs1)); TermQualIdTerm (_, i2, (_, targs2))] ->
    let fp = from_fproof (string_of_qualidentifier i1) targs1 in
    let ep = from_eproof (string_of_qualidentifier i2) targs2 in
    Equality (fp, ep)


let construct_cc_lemma_cong t _ =
  match t with
  | TermQualIdTerm (_, _, (_, h::tl)) ->
    let main_form = from_formula h in
    let neg_forms = List.map from_formula tl in
    L_CC_Congruence (main_form, neg_forms)

let construct_cc_lemma_trans t _ =
  match t with
  | TermQualIdTerm (_, _, (_, h::tl)) ->
    let main_form = from_formula h in
    let neg_forms = List.map from_formula tl in
    L_CC_Transitivity (main_form, neg_forms)

let string_of_symbol sy =
  match sy with
  | Symbol (_, s) -> s

let is_congruence_lemma av =
  match av with
  | AttributeValSexpr (_, (_, [_;_; SexprInParen (_, (_, [_;_]))])) -> true
  | _ -> false

let handle_lemma t a =
  match a with
  | [AttributeKeywordValue (_, ":CC", av)] ->
    if (is_congruence_lemma av)
    then construct_cc_lemma_cong t av
    else construct_cc_lemma_trans t av

let rec from_clause_proof rulename bodyterm =
  match rulename, bodyterm with
  | "@res", clause_proof_terms ->
    let rec discard_clause_annotation term = (match term with
        | TermExclimationPt (_, t, a) -> discard_clause_annotation t 
        | TermQualIdTerm (_, i, (_, tl)) -> from_clause_proof (string_of_qualidentifier i) tl) in
    let head_clause :: cls = List.map discard_clause_annotation clause_proof_terms in
    List.fold_left (fun acc cl -> Resolution (acc, cl)) head_clause cls
  | "@clause", [TermQualIdTerm (_, i, (_, tl)); fterm] ->
    let fp = from_fproof (string_of_qualidentifier i) tl in
    let f = from_formula fterm in
    Clause (fp, f)
  | "@lemma", [TermExclimationPt (_, t, (_, al))] ->
    Lemma (handle_lemma t al)

