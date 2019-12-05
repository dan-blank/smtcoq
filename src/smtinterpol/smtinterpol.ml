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
open Smtlib_to_proofrules
open Pt_to_smtcoq


let rec print_certif_by_id c =
  Printf.printf "%s" ("\n id is: " ^ (string_of_int c.id));
  match c.next with
  | Some n -> assert false; print_certif_by_id n
  | _ -> ()

(* Given a path to an SMT problem statement and an unsatisfiability proof produced by SMTInterpol, generate a SMTCoq certificate. *)
let import_trace ra' rf' fsmt fproof =
  let chan = open_in fproof in
  let lexbuf = Lexing.from_channel chan in
  let proof_term = Smtlib2_parse.mainterm Smtlib2_lex.token lexbuf in
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
  let prooftree = from_annotated_clause_proof (Hashtbl.find term_table ".mainproof" ) None in

  Printf.printf "\nConverted To proofrules\n";


  Printf.printf "\n --- to SMTCoq: raw\n";
  let certif = visit_clause_proof prooftree in
  link_list_of_clauses !clauses;
  let certif = get_first certif in

  print_certif Form.to_smt Atom.to_smt certif ".certoutput40";
  Printf.printf "\n --- to SMTCoq: move roots to beginning\n";
  move_roots_to_beginning certif;
  print_certif Form.to_smt Atom.to_smt certif ".certoutput41";
  (* print_certif_by_id certif; *)
  (* assert false; *)

  Printf.printf "\n --- to SMTCoq: adjust root positions\n";
  let certif = get_first certif in
  reposition_roots certif (-1);

  Printf.printf "\n --- to SMTCoq: select\n";
  let certif = get_last certif in
  SmtTrace.select certif;
  (* print_certif Form.to_smt Atom.to_smt certif ".certoutput_after_select"; *)
  
  Printf.printf "\n --- to SMTCoq: occur\n";
  SmtTrace.occur certif;
  
  Printf.printf "\n --- to SMTCoq: alloc\n";
  let max_id = SmtTrace.alloc (get_first certif) in
  Atom.print_atoms VeritSyntax.ra ".atoms_output_smtinterpol"; 
  print_certif Form.to_smt Atom.to_smt certif ".certoutput42";
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
  let re_hash = Form.hash_hform (Atom.hash_hatom ra') rf' in
  Printf.printf "%s" "Hi ol";
  (* print_certif Form.to_smt Atom.to_smt confl ".certoutputverit"; *)
  (rt, ro, ra, rf, roots, max_id, confl)
(*
Take an SMT2-formula and an SMTInterpol-proof and check whether the proof proves the formula unsatisfiable.
This function is called when Coq calls the vernacular command 'Smtinterpol.checker'.
*)
let checkerdebug fsmt fproof =
  SmtCommands.checker_debug (import_all fsmt fproof)

let checker formula proof=
  (* import_all None proof; *)
  Printf.printf "When this line is printed, it means that the solver stub is 1) integrated correctly and 2) linked to the vernacular command 'Smtinterpol.checker'.";
  SmtCommands.checker (import_all formula proof)

(*SmtCommands.checker (SmtBtype.create (), SmtAtom.Op.create (),VeritSyntax.ra,VeritSyntax.rf,  Smtlib2_genConstr.import_smtlib2 rt ro ra rf formula, 12, SmtTrace.mkRootV []) *)

