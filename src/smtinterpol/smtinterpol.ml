open CoqTerms
open SmtForm
open SmtCertif
open SmtTrace
open SatAtom
open SmtAtom
open SmtBtype
open SmtMisc
open Format
open Smttransformation
open Smtlib2_ast
open Modified_smtlib2_printing
open Flattened_transformation
open Pt_to_smtcoq

let import_trace proof =
  let chan = open_in proof in
  let lexbuf = Lexing.from_channel chan in
  (* Lexing.flush_input lexbuf; *)
  let first_num = ref (Smtlib2_parse.mainterm Smtlib2_lex.token lexbuf) in
  !first_num


let simple_constant_tests fsmt fproof =
  let rt : SmtBtype.reify_tbl = SmtBtype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let ra' = VeritSyntax.ra' in
  let rf' = VeritSyntax.rf' in
  let roots = Smtlib2_genConstr.import_smtlib2 rt ro ra rf fsmt in
  (* let smt_term = import_trace "../examples/rl_full_trivial.smt2" in *)
  (* let smt_term = import_trace "smtinterpol/rl_full_complex.scm" in *)
  let smt_term = import_trace fproof in
  Printf.printf "\nORIGINAL \n";
  print_term Format.std_formatter smt_term;
  visit_main_term smt_term;
  Printf.printf "\nFLATTENED\n";
  Hashtbl.iter
    (fun x y ->
       printf "\n";
       print_string Format.std_formatter x;
       printf " -> ";
       print_term Format.std_formatter y)
    flattened_table;
  let prooftree = translate_annotated_proof_term (Hashtbl.find flattened_table ".mainproof" ) "" in
  let confl = visit_clause_proof prooftree in
  SmtTrace.select confl;
  occur confl;
  let max_id = alloc confl in
  (rt, ro, ra, rf, roots, max_id, confl)


let clear_all () =
  SmtTrace.clear ();
  VeritSyntax.clear ()

(*
Take an SMT2-formula and an SMTInterpol-proof and check whether the proof proves the formula unsatisfiable.
This function is called when Coq calls the vernacular command 'Smtinterpol.checker'.
*)
let checker formula proof=
  (* import_all None proof; *)
  Printf.printf "When this line is printed, it means that the solver stub is 1) integrated correctly and 2) linked to the vernacular command 'Smtinterpol.checker'.";
  SmtCommands.checker (simple_constant_tests formula proof)

(*SmtCommands.checker (SmtBtype.create (), SmtAtom.Op.create (),VeritSyntax.ra,VeritSyntax.rf,  Smtlib2_genConstr.import_smtlib2 rt ro ra rf formula, 12, SmtTrace.mkRootV []) *)

