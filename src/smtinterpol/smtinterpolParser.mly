%{
    open SmtBtype
    open SmtAtom
    open SmtForm
    open SmtinterpolSyntax
%}

%token EOL
%token COLON
%token LPAR RPAR
%token <string> NUMERAL HEXADECIMAL BINARY STRING SYMBOL

%token UNDERSCORE

%type <SmtinterpolSyntax.term> line
%type <string> index
%type <string list> index_list

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

term :
  | constant_term { SmtinterpolSyntax.ConstantTerm $1 }
;



