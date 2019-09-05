open Smtlib2_ast
open CoqTerms
open SmtForm
open SmtCertif
open SmtTrace
open SatAtom
open SmtMisc

let print_specconstant fmt = function
  | SpecConstsDec (_, s)
  | SpecConstNum (_, s)
  | SpecConstString (_, s)
  | SpecConstsHex (_, s)
  | SpecConstsBinary (_, s) -> Format.pp_print_string fmt s


let print_symbol fmt = function
  | Symbol (_, s)
  | SymbolWithOr (_, s) -> Format.pp_print_string fmt s


let print_identifier fmt = function
  | IdSymbol (_, s) -> print_symbol fmt s
  | IdUnderscoreSymNum (_, s, (_, l)) ->
    Format.fprintf fmt "(_ %a" print_symbol s;
    List.iter (Format.fprintf fmt " %s") l;
    Format.fprintf fmt ")"

let rec print_sort fmt = function
  | SortIdentifier (_, i) -> print_identifier fmt i
  | SortIdSortMulti (_, i, (_, ls)) ->
    Format.fprintf fmt "(%a" print_identifier i;
    List.iter (Format.fprintf fmt " %a" print_sort) ls;
    Format.fprintf fmt ")"

let print_qualidentifier fmt = function
  | QualIdentifierId (_, i) -> print_identifier fmt i
  | QualIdentifierAs (_, i, s) ->
    Format.fprintf fmt "(%a as %a)"
      print_identifier i print_sort s

let print_sortedvar fmt = function
  | SortedVarSymSort (_, v, s) ->
    Format.fprintf fmt "(%a %a)" print_symbol v print_sort s

let rec print_varbinding fmt = function
  | VarBindingSymTerm (_, s, t) ->
    Format.fprintf fmt "(%a %a)" print_symbol s print_term t

and print_term fmt = function
  | TermSpecConst (_, c) -> print_specconstant fmt c
  | TermQualIdentifier (_, i) -> print_qualidentifier fmt i
  | TermQualIdTerm (_, i, (_, tl)) ->
    Format.fprintf fmt "(%a" print_qualidentifier i;
    List.iter (Format.fprintf fmt " %a" print_term) tl;
    Format.fprintf fmt ")"
  | TermLetTerm (_, (_, vb), t) ->
    Format.fprintf fmt "(let (";
    List.iter (Format.fprintf fmt " %a" print_varbinding) vb;
    Format.fprintf fmt ") %a)" print_term t
  | TermForAllTerm (_, (_, sv), t) ->
    Format.fprintf fmt "(forall (";
    List.iter (Format.fprintf fmt " %a" print_sortedvar) sv;
    Format.fprintf fmt ") %a)" print_term t
  | TermExistsTerm (_, (_, sv), t) ->
    Format.fprintf fmt "(exists (";
    List.iter (Format.fprintf fmt " %a" print_sortedvar) sv;
    Format.fprintf fmt ") %a)" print_term t
  | TermExclimationPt (_, t, _) -> print_term fmt t

let import_trace proof =
  let chan = open_in proof in
  let lexbuf = Lexing.from_channel chan in
  let is_first = ref true in
  let confl_num = ref None in
  let first_num = ref (Smtlib2_parse.mainterm Smtlib2_lex.token lexbuf) in
  let line = ref (1) in
  (Smtlib2_ast.print_term (Format.std_formatter)) !first_num

let import_all fsmt proof =
  import_trace proof

let simple_constant_tests =
  import_trace "../examples/parsertest_simple_string.smt2";
  import_trace "../examples/parsertest_simple_numerical.smt2";
  import_trace "../examples/parsertest_simple_decimal.smt2";
  import_trace "../examples/parsertest_simple_hexadecimal.smt2";
  import_trace "../examples/parsertest_simple_binary.smt2";
  Printf.printf "Simple constant term parser tests completed successfully. \n"

let simple_let_tests =
  import_trace "../examples/parsertest_simple_let_one_binding.smt2";
  import_trace "../examples/parsertest_simple_let_onelevelnested.smt2";
  Printf.printf "Simple let term parser tests completed successfully. \n"

let simple_variable_tests =
  import_trace "../examples/parsertest_simple_variable_withsort.smt2";
  import_trace "../examples/parsertest_simple_variable_withoutsort.smt2";
  Printf.printf "Simple variable term parser tests completed successfully. \n"
let simple_application_tests =
  import_trace "../examples/parsertest_simple_application_oneterm.smt2";
  import_trace "../examples/parsertest_simple_application_twoterms.smt2";
  Printf.printf "Simple application term parser tests completed successfully. \n"
let simple_quantified_tests =
  import_trace "../examples/parsertest_simple_quantified_forall.smt2";
  import_trace "../examples/parsertest_simple_quantified_exists.smt2";
  Printf.printf "Simple quantified term parser tests completed successfully. \n"
let simple_annotated_tests =
  import_trace "../examples/parsertest_simple_annotated_onesimpleannotation.smt2";
  import_trace "../examples/parsertest_simple_annotated_onecomplexannotation.smt2";
  import_trace "../examples/parsertest_simple_annotated_nested.smt2";
  Printf.printf "Simple annotated term parser tests completed successfully. \n"
(*
Take an SMT2-formula and an SMTInterpol-proof and check whether the proof proves the formula unsatisfiable.
This function is called when Coq calls the vernacular command 'Smtinterpol.checker'.
*)
let checker formula proof=
  import_all None proof;
  let dummy = SmtBtype.create () in (* Make sure that we can use other modules. *)
  let rt = SmtBtype.create () in
  let ro = SmtAtom.Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  Printf.printf "When this line is printed, it means that the solver stub is 1) integrated correctly and 2) linked to the vernacular command 'Smtinterpol.checker'."
  (*SmtCommands.checker (SmtBtype.create (), SmtAtom.Op.create (),VeritSyntax.ra,VeritSyntax.rf,  Smtlib2_genConstr.import_smtlib2 rt ro ra rf formula, 12, SmtTrace.mkRootV []) *)

