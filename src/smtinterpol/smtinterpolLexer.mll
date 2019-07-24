{
  open SmtinterpolParser
  exception Eof
}

let alpha = [ 'a'-'z' 'A' - 'Z' ]
let blank = [' ' '\t']
let newline = ['\n' '\r']
let non_zero_leading_digit = [ '1' -'9' ]
let digit = '0' | non_zero_leading_digit
let numeral = '0' | non_zero_leading_digit digit*
let hexadecimal = "#x" [ '0' - '9' 'a'-'f' 'A'-'F']+
let binary = "#b" [ '0' '1' ]+
(* TODO add proper string handling *)
let string = (alpha|digit|blank)*

rule token = parse
  | blank +   { token lexbuf }
  | newline + { EOL }
  | ":"       { COLON }
  | "("       { LPAR }
  | ")"       { RPAR }
  | (numeral as n){ NUMERAL (Big_int.big_int_of_string n)}
  | (hexadecimal as h) { HEXADECIMAL h} 
  | (binary as b) { BINARY b}
  | '"' (string as s) '"' { STRING s }
  | eof       { raise Eof }
