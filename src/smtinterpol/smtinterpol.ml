open SmtAtom
open SmtCertif
open Format
open Tabulation
open Modified_smtlib2_printing
open Smtlib_to_proofrules
open Proofrules_to_clauses



(* Given a path to an SMT problem statement and an unsatisfiability proof produced by SMTInterpol, generate a SMTCoq certificate. *)
let import_trace ra' rf' fsmt fproof =
  let chan = open_in fproof in
  let lexbuf = Lexing.from_channel chan in
  let proof_term = Smtlib2_parse.mainterm Smtlib2_lex.token lexbuf in

  Printf.printf "\n Tabulating smtlib terms ...";
  tabulate_proof proof_term;

  Printf.printf "\n Translating smtlib terms to proofrules ...";
  let prooftree = from_annotated_clause_proof (Hashtbl.find term_table ".mainproof" ) None in

  Printf.printf "\n Translating proofrules to clauses ...";
  let certif_after_translation = visit_clause_proof prooftree in

  Printf.printf "\n Linking all clauses together ...";
  link_list_of_clauses !clauses;
  let certif = get_first certif_after_translation in

  Printf.printf "\n Moving all non-root clauses behind the root clauses ...";
  move_roots_to_beginning certif;
  print_certif Form.to_smt Atom.to_smt certif ".certoutput41";

  Printf.printf "\n Adjusting root positions ...";
  let certif = get_first certif in
  reposition_roots certif (-1);

  Printf.printf "\n Calling select ...";
  let certif = get_last certif in
  SmtTrace.select certif;
  
  Printf.printf "\n Calling occur ...";
  SmtTrace.occur certif;
  
  Printf.printf "\n Calling alloc ...";
  let max_id = SmtTrace.alloc (get_first certif) in
  (* print_certif Form.to_smt Atom.to_smt certif ".cert_debug"; *)
  (max_id, certif)

let clear_all () =
  SmtTrace.clear ();
  VeritSyntax.clear ()

let import_all fsmt fproof =
  clear_all ();
  let rt = SmtBtype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let ra' = VeritSyntax.ra' in
  let rf' = VeritSyntax.rf' in
  let roots = Smtlib2_genConstr.import_smtlib2 rt ro ra rf fsmt in
  let (max_id, confl) = import_trace ra' rf' fsmt fproof in
  (rt, ro, ra, rf, roots, max_id, confl)
(*
Take an SMT2-formula and an SMTInterpol-proof and check whether the proof proves the formula unsatisfiable.
This function is called when Coq calls the vernacular command 'Smtinterpol.checker'.
*)
let checkerdebug fsmt fproof = SmtCommands.checker_debug (import_all fsmt fproof)

let checker formula proof= SmtCommands.checker (import_all formula proof)
