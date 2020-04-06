open Smtlib2_ast

let string_of_identifier = function
  | IdSymbol (_, (Symbol (_, s))) -> s
let symbol_of_identifier = function
  | IdSymbol (_, s) -> s
let string_of_qualidentifier = function
  | QualIdentifierId (_, i) -> string_of_identifier i
let symbol_of_qualidentifier = function
  | QualIdentifierId (_, i) -> symbol_of_identifier i

let string_of_single_atttribute = function
  | (_, [AttributeKeyword (_, s)]) -> s

let string_of_symbol sy =
  match sy with
  | Symbol (_, s) -> s


let string_of_symbol = function
  | Symbol (_, s) -> s

let rec deconstruct_qualidterm wterm =
  let TermQualIdTerm (_, i, (_ , bodyterm)) = wterm in
  let rulename = string_of_qualidentifier i in
  (rulename, bodyterm)

let print_specconstant fmt = function
  | SpecConstsDec (_, s)
  | SpecConstNum (_, s)
  | SpecConstString (_, s)
  | SpecConstsHex (_, s)
  | SpecConstsBinary (_, s) -> Format.pp_print_string fmt s
let rec print_sexpr fmt = function
  | SexprSpecConst (_, c) ->
    print_specconstant fmt c;
  | SexprSymbol (_, s) ->
    print_symbol fmt s;
  | SexprKeyword (_, s) ->
    Format.pp_print_string fmt s;
  | SexprInParen (_, (_,sl)) ->
    Format.fprintf fmt "(";
    List.iter (fun s ->
        print_sexpr fmt s;
        Format.fprintf fmt " ";
      ) sl;
    Format.fprintf fmt ") "
