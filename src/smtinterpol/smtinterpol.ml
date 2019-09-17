open CoqTerms
open SmtForm
open SmtCertif
open SmtTrace
open SatAtom
open SmtMisc
open Format
open Smttransformation
open Smtlib2_ast
open Modified_smtlib2_printing

let import_trace proof =
  let chan = open_in proof in
  let lexbuf = Lexing.from_channel chan in
  let first_num = ref (Smtlib2_parse.mainterm Smtlib2_lex.token lexbuf) in
  !first_num


let simple_constant_tests =
  (* let smt_term = import_trace "../examples/rl_full_trivial.smt2" in *)
  let smt_term = import_trace "smtinterpol/rl_full_complex.scm" in
  (* let smt_term = import_trace "../examples/rl_full_trivial.smt2" in *)
  (* let translated_term = smt_to_internal_clause_proof smt_term in *)
  (* let visited_term = visit_term smt_term in *)
  visit_main_term smt_term;
  (* let formater = Format.str_formatter in
   * print_term formater visited_term;
   * let flushed = flush_str_formatter () in *)
  Printf.printf "\nORIGINAL \n";
  print_term Format.std_formatter smt_term;
  (* Printf.printf "\nFLATTENED \n%s" flushed; *)
  (* Printf.printf "test"; *)
  Printf.printf "\nHASHTABLE";
  Hashtbl.iter
    (fun x y ->
       printf "\n";
       print_symbol Format.std_formatter x;
       printf " -> ";
       print_term Format.std_formatter y)
    flattened_table
  (* print_clause_proof Format.std_formatter translated_term *)
(* print_term (Format.std_formatter) smt_term *)
(*
Take an SMT2-formula and an SMTInterpol-proof and check whether the proof proves the formula unsatisfiable.
This function is called when Coq calls the vernacular command 'Smtinterpol.checker'.
*)
let checker formula proof=
  (* import_all None proof; *)
  let dummy = SmtBtype.create () in (* Make sure that we can use other modules. *)
  let rt = SmtBtype.create () in
  let ro = SmtAtom.Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  Printf.printf "When this line is printed, it means that the solver stub is 1) integrated correctly and 2) linked to the vernacular command 'Smtinterpol.checker'."
  (*SmtCommands.checker (SmtBtype.create (), SmtAtom.Op.create (),VeritSyntax.ra,VeritSyntax.rf,  Smtlib2_genConstr.import_smtlib2 rt ro ra rf formula, 12, SmtTrace.mkRootV []) *)

