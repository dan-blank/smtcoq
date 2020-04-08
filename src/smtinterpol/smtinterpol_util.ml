open Smtlib2_ast
open SmtAtom
open SmtForm

(**
   Functions for accessing Smtlib2_ast.
*)

let string_of_identifier (IdSymbol (_, (Symbol (_, s)))) = s
let symbol_of_identifier (IdSymbol (_, s)) = s
let string_of_qualidentifier (QualIdentifierId (_, i)) = string_of_identifier i
let symbol_of_qualidentifier (QualIdentifierId (_, i)) = symbol_of_identifier i
let string_of_single_atttribute (_, [AttributeKeyword (_, s)]) = s
let string_of_symbol (Symbol (_, s)) = s

(** Helper function to make pattern matching bit cleaner. *)
let deconstruct_qualidterm qualid_t =
  let TermQualIdTerm (_, i, (_ , bodyterm)) = qualid_t in
  let rulename = string_of_qualidentifier i in
  (rulename, bodyterm)

(**
   Functions related to printing Smtlib2_ast.
*)

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

let form_op_to_string = function
  | Ftrue -> "Ftrue"
  | Ffalse -> "Ffalse"
  | Fand -> "Fand"
  | For -> "For"
  | Fxor -> "Fxor"
  | Fimp -> "Fimp"
  | Fiff -> "Fiff"
  | Fite -> "Fite"
  | Fnot2 (i)-> "Fnot2" ^ (string_of_int i)
  | _ -> "Not supported yet"

let rec pp_form = function
  | Fatom (a) ->
    Printf.printf "(";
    Printf.printf "Fatom ";
    Atom.to_smt Format.std_formatter a;
    Printf.printf ")"
  | Fapp (fop, farray) ->
    Printf.printf "(";
    Printf.printf "Fapp ";
    Printf.printf "%s" (form_op_to_string fop);
    Array.iter (fun f -> pp_form (Form.pform f)) farray;
    Printf.printf ")"
