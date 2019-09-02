(* Is the difference between ProvedFormula and Formula purely contextual? *)


type atom =
    | EqualAtom of term * term (*What is the :quoted good for again, can we do without?*)
    | NonEqualAtom of term * term

type literal = 
    | PosLiteral of Atom
    | NegLiteral of Atom

type clause = Clause of literal list

type proved_clause = ProvedClause of clause * proof_rule

type formula = ?

type term = SMTLIBTerm

type proved_formula = ProvedFormula of formula * proof_rule

type proved_equality = ProvedEquality of atom * proof_rule (* Equality is a subcategory of atom? *)

type theory = LA | CC | ...

type tautology_rule = IteRed | ExcludedMiddle1 | ...

type rewrite_rule = AndToOr | EqFalse | ...

type top_proof_rule =
    | Resolution    of proved_clause * proved_clause * (proved_clause * literal)
    | Clause        of proved_clause * proved_formula * clause
    | Lemma         of proved_clause * (clause * theory)

type split_proof_rule =
    | Tautology of proved_formula (* can we leave the annotated clause? *)
    | Asserted  of proved_formula
    | Equality  of proved_formula * proved_equality
    | Split     of proved_formula * XXX

type simplification_proof_rule =
    | Reflexivity   of proved_equality * term
    | Transitivity  of proved_equality * proved_equality * proved_equality
    | Congruenve    of proved_equality * proved_equality * proved_equality
    | Rewrite       of proved_equality
    
type proof_rule = 
    | ProperRuleTop             of top_proof_rule
    | ProperRuleSplit           of split_proof_rule
    | ProperRuleSimplification  of simplification_proof_rule
    | tautology_rule
    | rewrite_rule
