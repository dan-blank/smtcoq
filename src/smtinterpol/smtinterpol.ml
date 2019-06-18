open CoqTerms
open SmtForm
open SmtCertif
open SmtTrace
open SatAtom
open SmtMisc

(*
Take an SMT2-formula and an SMTInterpol-proof and check whether the proof proves the formula unsatisfiable.
This function is called when Coq calls the vernacular command 'Smtinterpol.checker'.
*)
let checker formula proof=
  let dummy = SmtBtype.create () in (* Make sure that we can use other modules. *)
  Printf.printf "When this line is printed, it means that the solver stub is 1) integrated correctly and 2) linked to the vernacular command 'Smtinterpol.checker'."
