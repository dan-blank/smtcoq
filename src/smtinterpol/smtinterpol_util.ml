open Smtlib2_ast


let string_of_single_atttribute = function
  | (_, [AttributeKeyword (_, s)]) -> s

let string_of_symbol sy =
  match sy with
  | Symbol (_, s) -> s
