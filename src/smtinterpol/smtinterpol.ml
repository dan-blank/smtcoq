open Smtlib2_ast (* Needed for debugging. *)
open SmtAtom
open SmtCertif   (* Needed for debugging. *)
open Tabulation
module STI = Smtlib_to_ir
module ITC = Ir_to_clauses
open Format      (* Needed for debugging. *)

(** This module ties together all other modules of the SMTInterpol extension and interfaces with the rest of SMTCoq. *)

let import_trace fsmt fproof =
  let chan = open_in fproof in
  let lexbuf = Lexing.from_channel chan in
  let proof_term = Smtlib2_parse.mainterm Smtlib2_lex.token lexbuf in

  Printf.printf "\n Tabulating smtlib terms ...";

  tabulate_proof proof_term;
  (* Outcomment the following to print the term_table. *)
  (* Hashtbl.iter
   *   (fun x y ->
   *      printf "\n";
   *      Format.pp_print_string Format.std_formatter x;
   *      printf " -> ";
   *      print_term Format.std_formatter y)
   *   term_table; *)

  Printf.printf "\n Translating smtlib terms to the intermediate representation ...";

  let mainproof_as_ir = STI.walk_clause_proof (Hashtbl.find term_table ".mainproof") in

  Printf.printf "\n Translating the intermediate representation to clauses ...";
  ignore (ITC.walk_clause_proof mainproof_as_ir);

  Printf.printf "\n Linking the clauses together ...";

  ITC.add_roots_and_non_roots();

  Printf.printf "\n Calling SMTCoq preprocessing select, occur and alloc ...";

  let last_clause_of_certificate = ITC.get_last (List.hd !ITC.clauses) in
  SmtTrace.select last_clause_of_certificate;
  SmtTrace.occur last_clause_of_certificate;
  let max_id = SmtTrace.alloc (ITC.get_first last_clause_of_certificate) in

  (* Outcomment the following to write the certificate into a file .cert_debug. *)
  (* print_certif Form.to_smt Atom.to_smt last_clause_of_certificate ".cert_debug"; *)

  (max_id, last_clause_of_certificate)

let clear_all () =
  SmtTrace.clear ();
  VeritSyntax.clear ()

let import_all fsmt fproof =
  clear_all ();
  let rt = SmtBtype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let roots = Smtlib2_genConstr.import_smtlib2 rt ro ra rf fsmt in
  let (max_id, conflicting_clause) = import_trace fsmt fproof in
  (rt, ro, ra, rf, roots, max_id, conflicting_clause)
let checkerdebug fsmt fproof = SmtCommands.checker_debug (import_all fsmt fproof)

(*
Take an SMT2-formula and an SMTInterpol-proof and check whether the proof proves the formula unsatisfiable.
This function is called when Coq calls the vernacular command 'Smtinterpol.checker'.
*)
let checker formula proof= SmtCommands.checker (import_all formula proof)
