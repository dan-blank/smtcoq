{
  open SmtinterpolParser
  exception Eof
  (*
      todo is problematic? : indentifier = symbol

  *)
}
let alpha = [ 'a'-'z' 'A' - 'Z' ]
let ws = [' ' '\t']
let newline = ['\n' '\r']
let non_zero_leading_digit = [ '1' -'9' ]
let digit = '0' | non_zero_leading_digit
let numeral = '0' | non_zero_leading_digit digit*
let decimal = numeral '.' '0'* numeral
let hexadecimal = "#x" [ '0' - '9' 'a'-'f' 'A'-'F']+
let binary = "#b" [ '0' '1' ]+
let string = (alpha|digit|ws)*
let symbolchars = ['~''!''@''$''%''^''&''*''_''-''+''=''<''>''.''?''/']
let symbol = (alpha|digit|symbolchars)+
let index = numeral|symbol
let identifier = symbol

rule token = parse
  | ws +   { token lexbuf }
  | newline + { EOL }
  | ":"       { COLON }
  | "("       { LPAR }
  | ")"       { RPAR }
  | (numeral as n){ NUMERAL n}
  | (hexadecimal as h) { HEXADECIMAL h} 
  | (decimal as d) { DECIMAL d} 
  | (binary as b) { BINARY b}
  | "let" { LET }
  | "as" { AS }
  | "!" { EXCLAMATIONMARK }
  | "exists" { EXISTS }
  | "forall" { FORALL }
  | "QuotedLA" { QUOTEDLA }
  | '"' (string as s) '"' { STRING s }
  | symbol as s { SYMBOL s }
  | eof       { raise Eof }
