open CoqTerms
open SmtForm
open SmtCertif
open SmtTrace
open SatAtom
open SmtAtom
open SmtBtype
open SmtMisc
open Format
open Tabulation
open Smtlib2_ast
open Modified_smtlib2_printing
open Flattened_transformation
open Pt_to_smtcoq

let import_trace proof =
  let chan = open_in proof in
  let lexbuf = Lexing.from_channel chan in
  Smtlib2_parse.mainterm Smtlib2_lex.token lexbuf


(* Given a path to an SMT problem statement and an unsatisfiability proof produced by SMTInterpol, generate a SMTCoq certificate. *)
let generate_certificate fsmt fproof =
  let rt : SmtBtype.reify_tbl = SmtBtype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let ra' = VeritSyntax.ra' in
  let rf' = VeritSyntax.rf' in
  let roots = Smtlib2_genConstr.import_smtlib2 rt ro ra rf fsmt in
  let proof_term = import_trace fproof in
  Printf.printf "\nORIGINAL \n";
  print_term Format.std_formatter proof_term;

  tabulate_proof proof_term;
  Printf.printf "\nFLATTENED\n";
  Hashtbl.iter
    (fun x y ->
       printf "\n";
       print_string Format.std_formatter x;
       printf " -> ";
       print_term Format.std_formatter y)
    term_table;
  let prooftree = translate_annotated_clause_proof_term (Hashtbl.find term_table ".mainproof" ) None in
  Printf.printf "\nConverted To proofrules\n";
  let confl = visit_clause_proof prooftree in
  Printf.printf "\nConverted To SMTCoq proof\n";
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
  SmtCommands.checker (generate_certificate formula proof)

(*SmtCommands.checker (SmtBtype.create (), SmtAtom.Op.create (),VeritSyntax.ra,VeritSyntax.rf,  Smtlib2_genConstr.import_smtlib2 rt ro ra rf formula, 12, SmtTrace.mkRootV []) *)

