type typ = | Dummy

type identifier =
  | IndexedIdentifier of string * string list
  | SimpleIdentifier of string

type sort =
  | AppliedSort of identifier * sort list
  | SimpleSort of identifier                 
  | Placeholdersort
  (* Placeholders for proper sorts that could be support later on when typechecking.  *)

type spec_constant =
  | Numerical of string
  | Decimal of string
  | Hexadecimal of string 
  | Binary of string 
  | String of string



type sorted_var = SortedVar of string * sort

type keyword =
  | KWQuotedLA
  | KWPivot
  | KWImpToOr

type atom =
  | ConstantAtom of spec_constant
  | SymbolAtom of string
  | KeywordAtom of keyword



type sexpr =
  | AtomSexpr of atom
  | NestedSexpr of sexpr list

type attribute_value =
  | ConstantValue of spec_constant
  | SymbolValue of string
  | NestedSexprValue of sexpr list

type attribute =
  | EmptyAttribute of keyword
  | NonEmptyAttribute of keyword * attribute_value

type quantifier = ForallQuantifier | ExistsQuantifier

type qualified_identifier =
  | QualifiedIdentifier of identifier * sort option

type term =
  | ConstantTerm of spec_constant
  | AnnotatedTerm of term * attribute list
  | ApplicationTerm of qualified_identifier * term list 
  | LetTerm of var_binding list * term
(* Note: According to the specification, "To simplify sort checking, a function symbolin a term can be annotated with one of its result sorts", so this should rather be an optional sort *)
  | VariableTerm of qualified_identifier 
  | QuantifiedFormula of quantifier * sorted_var list * term
  | PlaceholderTerm (* TODO For development purposes, delete when confl_number is treated correctly *)
and
  var_binding = VarBinding of string * term
