open Smtlib2_ast
open Prooftree_ast
open Smtinterpol_util

(**
   This module translates SMTLib terms into the intermediate representation proofrules.

   We simply walk the SMTlib term and construct the corresponding intermediate representation depending on the context.

   Errors that might occur in this module might be due to:
   - Not having parsed the SMT input problem with Smtlib2_genConstr.import_smtlib2 beforehand.
   - Unexpected annotations.
   - Unsupported SMTInterpol constructs: Proofrules, split rules, rewrite rules, lemmas, ...
*)

(**
   Walk an SMTLib term that represents a formula, return the SmtAtom.Form.t equivalent.

   The function Smtlib2_genConstr.make_root is invoked to create a SMTCoq formula walk the term.
   Note that the input smt problem has to be parsed (by Smtlib2_genConstr.import_smtlib2) at this point, otherwise
   SMTCoq will be missing information (e.g. type of an uninterpreted function) necessary to correctly handle
   the SMTLib term.
*)
let walk_formula term =
    let root_atoms = VeritSyntax.ra in
    let root_formulas = VeritSyntax.rf in
    Smtlib2_genConstr.make_root root_atoms root_formulas term

(**
   Walk an SMTLib term that represents an equality proof, return the IR equivalent.
   List.fold_left is employed to turn n-ary congruence and transitivity terms into their binary IR equivalents.
*)
let rec walk_equality_proof term =
  let handle_rewrite_annotation = function
    | ":eqToXor" -> Rewrite_eqToXor
    | ":andToOr" -> Rewrite_andToOr
    | ":notSimp" -> Rewrite_notSimp
    | ":intern" -> Rewrite_intern in
  match (deconstruct_qualidterm term) with
  | "@rewrite", [TermExclimationPt (_, ft, at)] ->
    let f = walk_formula ft in
    let a = handle_rewrite_annotation (string_of_single_atttribute at) in
    Rewrite (f, a)
  | "@cong", epts ->
    let ep :: eps = List.map walk_equality_proof epts in
    List.fold_left (fun acc new_ep -> Congruence (acc, new_ep)) ep eps
  | "@trans", epts ->
    let ep :: eps = List.map walk_equality_proof epts in
    List.fold_left (fun acc new_ep -> Transitivity (acc, new_ep)) ep eps
  | "@refl", [ft] ->
    let f = walk_formula ft in
    Reflexivity f

(**
   Walk an SMTLib term that represents a formula proof, return the IR equivalent.
*)
let rec walk_fproof term =
  let handle_split_annotation = function
    | ":xor-1" -> Split_xor_1
    | ":xor-2" -> Split_xor_2
    | ":notOr" -> Split_notOr in
  match (deconstruct_qualidterm term) with
  | "@asserted", [ft] ->
    let f = walk_formula ft in
    Asserted f
  | "@split", [TermExclimationPt (_, fpt, sa); ft] ->
    let fp = walk_fproof fpt in
    let f = walk_formula ft in
    let a = handle_split_annotation (string_of_single_atttribute sa) in
    Split (fp, f, a)
  | "@eq", [fpt; ept] ->
    let fp = walk_fproof fpt in
    let ep = walk_equality_proof ept in
    Equality (fp, ep)

(**
   Given an SMTLib term that represents an congruence closure lemma and the corresponding SMTLib annotation, return
   the IR equivalent.

   In order to know whether the lemma relies on congruence or transitivity, the function 'is_congruence' pattern matches
   on the annotation: If there are exactly two terms in its subpath, then it is has to be a congruence lemma.
   To give an example: the following term is a congruence lemma:
   (@lemma (!
     (or (! (= (f x) (f z)) :quotedCC) (not (! (= x z) :quotedCC)))
     :CC ((! (= (f x) (f z)) :quotedCC) :subpath ((f x) (f z)))))
   Note how the attribute value "subpath" contains exactly two terms.
*)
let construct_cc_lemma term attribute_value =
  let is_congruence lt = (match lt with
      | AttributeValSexpr (_, (_, [_;_; SexprInParen (_, (_, [_;_]))])) -> true
      | _ -> false) in
  match term with
  | TermQualIdTerm (_, _, (_, ft::fts)) ->
    let equality = walk_formula ft in
    let inequalities = List.map walk_formula fts in
    if (is_congruence attribute_value)
    then L_CC_Congruence (equality, inequalities)
    else L_CC_Transitivity (equality, inequalities)

(**
   Given an SMTLib term that represents an lemma and the corresponding SMTLib annotation, return the IR equivalent.
   At the moment, only congruence closure lemmas are supported.
*)
let construct_lemma term at =
  match at with
  | [AttributeKeywordValue (_, ":CC", av)] -> construct_cc_lemma term av

(**
   Given an SMTLib term that represents a clause proof, return the IR equivalent.
   "@clause" rules are stripped of their annotations, since we don't need the annotated complementary literal.
   List.fold_left is employed to turn n-ary resolution terms into their binary IR equivalent.
*)
let rec walk_clause_proof term =
  match (deconstruct_qualidterm term) with
  | "@res", cpts ->
    let rec discard_clause_annotation = (function
        | TermExclimationPt (_, t, a) -> discard_clause_annotation t 
        | t -> walk_clause_proof t) in
    let cp :: cps = List.map discard_clause_annotation cpts in
    List.fold_left (fun acc new_cp -> Resolution (acc, new_cp)) cp cps
  | "@clause", [fpt; ft] ->
    let fp = walk_fproof fpt in
    let f = walk_formula ft in
    Clause (fp, f)
  | "@lemma", [TermExclimationPt (_, lt, (_, la))] -> Lemma (construct_lemma lt la)

