{
  open SmtinterpolParser
  exception Eof
}

let newline = ['\n' '\r']

rule token = parse
  | newline + { EOL }
  | ":"       { COLON }
  | eof       { raise Eof }
