open SmtAtom
open SmtForm
open SmtCertif
open SmtTrace

type typ = | Dummy

(*
Represents
attribute ::= keywordNoAttr:k attributeValue?:v
*)
type annotation = Annotation of string * string

(*
A SMTLib-Sort. Since we don't do typechecking yet, we currently ignore proper parsing and handling of sorts.

Represents
sort ::= identifier:id {: ... :}
      | LPAR identifier:id sort+:sorts RPAR
*)
type sort =
  | Sort of string * sort list * int list option
  (* Placeholders for proper sorts that could be support later on when typechecking.  *)
  | Placeholdersort

(*
A constant term that is either numerical (which kind of number is encoded in the sort) or a string.

Represents
constantTerm ::= NUMERAL:n {: ... :}
             | DECIMAL:n {: ... :}
             | HEXADECIMAL:n {: ... :}
             | BINARY:n {: ... :}
             | STRING:n {: ... :}
*)
type constant_term =
  | Numerical of Big_int.big_int
  | Decimal of string
  | Hexadecimal of string 
  | Binary of string 
  | String of string

(*
Represents many types of variables, i.e.
sortedVar ::= LPAR symbol:sym sort:s RPAR
term ::= ... | LPAR LET LPAR varBinding+:bindings RPAR term:t RPAR
*)
type term_variable = Variable of string * sort option

(*
Represents
terminal EXISTS, ..., FORALL
*)
type quantifier = Forall | Exists

(*
Represents

term ::= constantTerm
       | qualIdentifier:fun
       | LPAR qualIdentifier:fun term+:args RPAR
       | LPAR LET LPAR varBinding+:bindings RPAR term:t RPAR
       | LPAR FORALL:sym LPAR sortedVar+:vars RPAR term:t RPAR
       | LPAR EXISTS:sym LPAR sortedVar+:vars RPAR term:t RPAR
       | LPAR BANG term:t attribute+:attr RPAR
*)
type term =
  | ConstantTerm of constant_term * sort
  | AnnotatedTerm of term * annotation list
  | ApplicationTerm of function_symbol * term list
  | LetTerm of term_variable list * term list * term * sort
  | TermVariable of string * sort
  | QuantifiedFormula of quantifier * term_variable list * term
  | PlaceholderTerm (* TODO For development purposes, delete when confl_number is treated correctly *)
(*
Represents
qualIdentifier ::= identifier:i
       | LPAR AS identifier:i sort:s RPAR
*)
and function_symbol = string * int list * sort list * sort * term_variable list * term
