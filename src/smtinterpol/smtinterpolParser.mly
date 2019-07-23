%{
    open SmtBtype
    open SmtAtom
    open SmtForm
    open SmtinterpolSyntax
%}

%token EOL
%token COLON


%type <SmtinterpolSyntax.typ> line

%start line

%%

line:
  | COLON EOL { Dummy }
;
