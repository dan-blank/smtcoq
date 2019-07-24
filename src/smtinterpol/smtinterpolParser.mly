%{
    open SmtBtype
    open SmtAtom
    open SmtForm
    open SmtinterpolSyntax
%}

%token EOL
%token COLON
%token LPAR RPAR
/* TODO support DECIMAL -> how to represent in OCaml? */
%token <Big_int.big_int> NUMERAL
%token <string> HEXADECIMAL BINARY STRING

%type <SmtinterpolSyntax.term> line

%start line

%%

line:
  | term EOL { $1 }
;

constant_term:
  | NUMERAL { SmtinterpolSyntax.Numerical $1 }
  | HEXADECIMAL { SmtinterpolSyntax.Hexadecimal $1}
  | BINARY { SmtinterpolSyntax.Binary $1 }
  | STRING { SmtinterpolSyntax.String $1 }
;

term :
  | constant_term { SmtinterpolSyntax.ConstantTerm ($1, SmtinterpolSyntax.Placeholdersort) }
;



