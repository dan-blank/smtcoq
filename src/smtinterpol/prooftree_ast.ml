open Smtlib2_ast
open SmtAtom

type clause = Clause of literal list

type theory = LA | CC | EQ | ReadOverXXX

type tautology_rule = IteRed | ExcludedMiddle1

type rewrite_rule = AndToOr | EqFalse

type split_rule = XXX

type sexpr =
    | SexprSymbol       of string
    | SexprSpecConst    of string
    | SexprKeyword      of string
    | SexprList         of sexpr list

type varbindings = Varbinding

type equality_proof =
    | Reflexivity          of term 
    | Transitivity         of equality_proof * equality_proof
    | Congruenve           of equality_proof * equality_proof
    | Rewrite              of term * rewrite_rule
    | LettedEqualityProof  of varbindings * equality_proof
    
type formula_proof =
    | Tautology          of term  * tautology_rule
    | Asserted           of term 
    | Equality           of formula_proof * equality_proof
    | Split              of formula_proof * term  * split_rule
    | LettedFormulaProof of varbindings * formula_proof
type clause_proof =
    | Resolution        of clause_proof * clause_proof (* clause_proof can term sein, bspw. ein let-term*)
    | ClauseRule        of formula_proof * clause
    | Lemma             of clause * theory * sexpr
    | LettedClauseProof of varbindings * clause_proof
    | Dummy

(* let print_formula_proof fmt = function
 *   | Asserted t ->
 *     Format.fprintf fmt "Asserted (";
 *     print_term fmt t;
 *     Format.fprintf fmt ")"
 * 
 * let print_literal fmt = function
 *   | PosLiteral a -> print_term fmt a
 *   | NegLiteral a -> 
 *     Format.fprintf fmt "(not";
 *     print_term fmt a;
 *     Format.fprintf fmt ")"
 * 
 * let print_clause fmt = function
 *   | Clause ls -> List.iter (print_literal fmt) ls
 * 
 * let rec print_clause_proof fmt =
 *   function
 *   | Resolution (clause1, clause2) ->
 *     Printf.printf "PRINT Resolution";
 *     Format.fprintf fmt "Resolution (";
 *     Printf.printf "PRINT Resolution SUB1";
 *     print_clause_proof fmt clause1;
 *     Printf.printf "PRINT Resolution SUB2";
 *     print_clause_proof fmt clause2;
 *     Format.fprintf fmt ")"
 *   | ClauseRule (_, clause) ->
 *     Printf.printf "PRINT ClauseRule";
 *     Format.fprintf fmt "Clause (";
 *     print_clause fmt clause;
 *     Format.fprintf fmt ")"
 * 
 * let smt_to_internal_formula_proof = function
 *   | TermQualIdTerm (_, _, (_, [term])) -> Asserted term
 * 
 * let rec smt_to_internal_clause_proof =
 *   (\* Printf.printf "CURRENTLY in RESOLUTION"; *\)
 *   function
 *   | TermQualIdTerm
 *       (_,
 *        QualIdentifierId (_,IdSymbol (_, (Symbol (_, "@res")))),
 *        (_,t1::t2::lls)) ->
 *     let clause_proof_1 = smt_to_internal_clause_proof t1 in
 *     let clause_proof_2 = smt_to_internal_clause_proof t2 in
 *     Printf.printf " MATCHED Res ";
 *     Resolution (clause_proof_1, clause_proof_2)
 *     (\* Dummy *\)
 *   | TermLetTerm (_, (_, _),_ ) ->
 *     Printf.printf " MATCHED Let ";
 *     Dummy
 *   | TermExclimationPt (_, _, (_,_ )) ->
 *     Printf.printf " MATCHED Annotation ";
 *     Dummy
 *   | TermSpecConst (_, _) ->
 *     Printf.printf " MATCHED Const ";
 *     Dummy *)
