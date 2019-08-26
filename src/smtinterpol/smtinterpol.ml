open CoqTerms
open SmtForm
open SmtCertif
open SmtTrace
open SatAtom
open SmtMisc


let import_trace proof =
  let chan = open_in proof in
  let lexbuf = Lexing.from_channel chan in
  let is_first = ref true in
  let confl_num = ref SmtinterpolSyntax.PlaceholderTerm in
  let first_num = ref (-1) in
  let line = ref (1) in
  try
    while true do
      confl_num := SmtinterpolParser.line SmtinterpolLexer.token lexbuf;
      if !is_first then (
        is_first := false;
      );
      incr line
    done;
    raise SmtinterpolLexer.Eof
  with
    | SmtinterpolLexer.Eof ->
      close_in chan;
      (* Printf.printf "Parsing was successfull!"*)
    | Parsing.Parse_error -> failwith ("Smtinterpol.import_trace: parsing error line "^(string_of_int !line)^" File was "^proof)

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
(*
Take an SMT2-formula and an SMTInterpol-proof and check whether the proof proves the formula unsatisfiable.
This function is called when Coq calls the vernacular command 'Smtinterpol.checker'.
*)
let checker formula proof=
  simple_constant_tests;
  simple_let_tests;
  import_all None proof;
  let dummy = SmtBtype.create () in (* Make sure that we can use other modules. *)
  let rt = SmtBtype.create () in
  let ro = SmtAtom.Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  Printf.printf "When this line is printed, it means that the solver stub is 1) integrated correctly and 2) linked to the vernacular command 'Smtinterpol.checker'."
  (*SmtCommands.checker (SmtBtype.create (), SmtAtom.Op.create (),VeritSyntax.ra,VeritSyntax.rf,  Smtlib2_genConstr.import_smtlib2 rt ro ra rf formula, 12, SmtTrace.mkRootV []) *)

