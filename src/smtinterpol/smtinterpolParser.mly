%{
    open SmtinterpolSyntax
%}

%token EOL
%token COLON
%token LPAR RPAR
%token <string> NUMERAL HEXADECIMAL BINARY DECIMAL STRING SYMBOL

%token UNDERSCORE
%token FORALL EXISTS
%token LET AS

%type <SmtinterpolSyntax.term> line

%start line

%%

line:
  | term EOL { $1 }
;

index:
  | NUMERAL { $1 }
  | SYMBOL { $1 }
;

index_list:
  | index {[$1]}
  | index index_list { $1 :: $2 }
;

identifier:
  | SYMBOL { SmtinterpolSyntax.SimpleIdentifier $1 }
  | LPAR UNDERSCORE SYMBOL index_list RPAR { SmtinterpolSyntax.IndexedIdentifier ($3, $4) }
;

constant_term:
  | NUMERAL { SmtinterpolSyntax.Numerical $1 }
  | HEXADECIMAL { SmtinterpolSyntax.Hexadecimal $1}
  | BINARY { SmtinterpolSyntax.Binary $1 }
  | DECIMAL { SmtinterpolSyntax.Decimal $1 }
  | STRING { SmtinterpolSyntax.String $1 }
;

sort_list:
  | sort {[$1]}
  | sort sort_list { $1 :: $2 }
;
sort:
  | identifier { SmtinterpolSyntax.SimpleSort $1 }
  | LPAR identifier sort_list RPAR {SmtinterpolSyntax.AppliedSort ($2, $3) }
;

var_binding:
  | LPAR SYMBOL term RPAR { SmtinterpolSyntax.VarBinding ($2, $3) }
;

var_binding_list:
  | var_binding var_binding_list { $1 :: $2 }
  | var_binding { [$1] }
;

qual_identifier:
  | identifier { SmtinterpolSyntax.QualifiedIdentifier ($1, None) }
  | LPAR AS identifier sort RPAR { SmtinterpolSyntax.QualifiedIdentifier ($3, (Some $4)) }
;

sorted_var:
  | LPAR SYMBOL sort RPAR { SmtinterpolSyntax.SortedVar ($2, $3) }
;

sorted_var_list:
  | sorted_var { [$1] }
  | sorted_var sorted_var_list { $1 :: $2 }
;

quantifier:
  | FORALL { SmtinterpolSyntax.ForallQuantifier }
  | EXISTS { SmtinterpolSyntax.ExistsQuantifier }
;

term :
  | constant_term { SmtinterpolSyntax.ConstantTerm $1 }
  | LPAR LET LPAR var_binding_list RPAR term RPAR { SmtinterpolSyntax.LetTerm ($4, $6) }
  | qual_identifier { SmtinterpolSyntax.VariableTerm $1 }
  | LPAR qual_identifier term_list RPAR { SmtinterpolSyntax.ApplicationTerm ($2, $3) }
  | LPAR quantifier LPAR sorted_var_list RPAR term RPAR { SmtinterpolSyntax.QuantifiedFormula ($2, $4, $6) }
;

term_list:
  | term { [$1] }
  | term term_list { $1 :: $2 }


