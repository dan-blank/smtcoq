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
  let confl_num = ref SmtinterpolSyntax.Dummy in
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
      Printf.printf "We are in import_trace and parsing was successfull!"
    | Parsing.Parse_error -> failwith ("Smtinterpol.import_trace: parsing error line "^(string_of_int !line)^" File was "^proof)

let import_all fsmt proof =
  import_trace proof

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

