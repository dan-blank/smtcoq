open Smtlib2_ast
open SmtAtom
open SmtCertif
open Tabulation
open Smtlib_to_ir
module C = Ir_to_clauses
open Ir
open Format



(* let print_specconstant fmt = function
 *   | SpecConstsDec (_, s)
 *   | SpecConstNum (_, s)
 *   | SpecConstString (_, s)
 *   | SpecConstsHex (_, s)
 *   | SpecConstsBinary (_, s) -> Format.pp_print_string fmt s
 * 
 * 
 * let print_symbol fmt = function
 *   | Symbol (_, s)
 *   | SymbolWithOr (_, s) -> Format.pp_print_string fmt s
 * 
 * 
 * let print_identifier fmt = function
 *   | IdSymbol (_, s) ->
 *     Format.fprintf fmt "IDSYMB: ";
 *     print_symbol fmt s
 *   | IdUnderscoreSymNum (_, s, (_, l)) ->
 *     Format.fprintf fmt "IDUNDERSCORESYM: (_ %a" print_symbol s;
 *     List.iter (Format.fprintf fmt " %s") l;
 *     Format.fprintf fmt ")"
 * 
 * let rec print_sort fmt = function
 *   | SortIdentifier (_, i) -> print_identifier fmt i
 *   | SortIdSortMulti (_, i, (_, ls)) ->
 *     Format.fprintf fmt "(%a" print_identifier i;
 *     List.iter (Format.fprintf fmt " %a" print_sort) ls;
 *     Format.fprintf fmt ")"
 * 
 * let print_qualidentifier fmt = function
 *   | QualIdentifierId (_, i) ->
 *     Format.fprintf fmt "QUALID: ";
 *     print_identifier fmt i
 *   | QualIdentifierAs (_, i, s) ->
 *     Format.fprintf fmt "(%a as %a)"
 *       print_identifier i print_sort s
 * 
 * let print_sortedvar fmt = function
 *   | SortedVarSymSort (_, v, s) ->
 *     Format.fprintf fmt "(%a %a)" print_symbol v print_sort s
 * 
 * let print_string fmt s = Format.pp_print_string fmt s
 * 
 * let rec print_sexpr fmt = function
 *   | SexprSpecConst (_, c) ->
 *     Format.fprintf fmt "SEXPRSPECCONST: ";
 *     print_specconstant fmt c;
 *   Format.fprintf fmt " "
 *   | SexprSymbol (_, s) ->
 *     Format.fprintf fmt "SEXPRSYMBOL: ";
 *     print_symbol fmt s;
 *   Format.fprintf fmt " "
 *   | SexprKeyword (_, s) ->
 *     Format.fprintf fmt "SEXPRKEYORD: ";
 *     print_string fmt s;
 *   Format.fprintf fmt " "
 *   | SexprInParen (_, (_,sl)) ->
 *     Format.fprintf fmt "SEXPRINPAREN: (";
 *     List.iter (print_sexpr fmt) sl;
 *     Format.fprintf fmt ") "
 * 
 * 
 * let print_attribute_value fmt = function
 *   | AttributeValSpecConst (_, c) ->
 *     Format.fprintf fmt "AVSPECCONST: ";
 *     print_specconstant fmt c
 *   | AttributeValSymbol (_, s) ->
 *     Format.fprintf fmt "AVSYMBOL: ";
 *     print_symbol fmt s
 *   | AttributeValSexpr (_, (_, sl)) ->
 *     Format.fprintf fmt "AVSEXPR: (";
 *     List.iter (print_sexpr fmt) sl;
 *     Format.fprintf fmt ")"
 * 
 * let print_attribute fmt = function
 *   | AttributeKeyword (_, s) ->
 *     Format.fprintf fmt "AKey: %a " print_string s
 *   | AttributeKeywordValue (_, s, av) ->
 *     Format.fprintf fmt "AKeyVal: %a " print_string s;
 *     print_attribute_value fmt av
 * 
 * let rec print_varbinding fmt = function
 *   | VarBindingSymTerm (_, s, t) ->
 *     Format.fprintf fmt "VB: (%a %a)" print_symbol s print_term t
 * 
 * and print_term fmt = function
 *   | TermSpecConst (_, c) ->
 *     Format.fprintf fmt "CT: ";
 *     print_specconstant fmt c
 *   | TermQualIdentifier (_, i) ->
 *     Format.fprintf fmt "SAPPT: ";
 *     print_qualidentifier fmt i
 *   | TermQualIdTerm (_, i, (_, tl)) ->
 *     Format.fprintf fmt "\n potential APPT: (%a" print_qualidentifier i;
 *     List.iter (Format.fprintf fmt " %a" print_term) tl;
 *     Format.fprintf fmt ")"
 *   | TermLetTerm (_, (_, vb), t) ->
 *     Format.fprintf fmt "LETT: (let (";
 *     List.iter (Format.fprintf fmt " %a" print_varbinding) vb;
 *     Format.fprintf fmt ") %a)" print_term t
 *   | TermForAllTerm (_, (_, sv), t) ->
 *     Format.fprintf fmt "FORALLT: (forall (";
 *     List.iter (Format.fprintf fmt " %a" print_sortedvar) sv;
 *     Format.fprintf fmt ") %a)" print_term t
 *   | TermExistsTerm (_, (_, sv), t) ->
 *     Format.fprintf fmt "EXISTST: (exists (";
 *     List.iter (Format.fprintf fmt " %a" print_sortedvar) sv;
 *     Format.fprintf fmt ") %a)" print_term t
 *   | TermExclimationPt (_, t, (_, al)) ->
 *     Format.fprintf fmt "ANNOTT: (! ";
 *     print_term fmt t;
 *     List.iter (print_attribute fmt) al;
 *     Format.fprintf fmt ")" *)
(* Given a path to an SMT problem statement and an unsatisfiability proof produced by SMTInterpol, generate a SMTCoq certificate. *)
let import_trace fsmt fproof =
  let chan = open_in fproof in
  let lexbuf = Lexing.from_channel chan in
  let proof_term = Smtlib2_parse.mainterm Smtlib2_lex.token lexbuf in

  Printf.printf "\n Tabulating smtlib terms ...";
  (* print_term Format.std_formatter proof_term; *)
  tabulate_proof proof_term;
  Printf.printf "\nFLATTENED\n";
  Hashtbl.iter
    (fun x y ->
       printf "\n";
       Format.pp_print_string Format.std_formatter x;
       printf " -> ";
       print_term Format.std_formatter y)
    term_table;

  Printf.printf "\n Translating smtlib terms to proofrules ...";
  let xy = Hashtbl.find term_table ".mainproof" in
  let TermQualIdTerm (_, i, (_, tl)) = xy in
  (* Printf.printf "\n* %s %i" (string_of_qualidentifier i) (List.length tl);
   * print_term Format.std_formatter xy; *)
  let prooftree = walk_clause_proof xy in

  Printf.printf "\n Translating proofrules to clauses ...";
  let certif_after_translation = C.walk_clause_proof prooftree in

  Printf.printf "\n Linking roots and clauses together ...";
  C.add_roots_and_non_roots();

  Printf.printf "\n Calling select ...";
  let certif = C.get_last (List.hd !C.clauses) in
  SmtTrace.select certif;
  
  Printf.printf "\n Calling occur ...";
  SmtTrace.occur certif;
  
  Printf.printf "\n Calling alloc ...";
  let max_id = SmtTrace.alloc (C.get_first certif) in
  print_certif Form.to_smt Atom.to_smt certif ".cert_debug";
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
  let roots = Smtlib2_genConstr.import_smtlib2 rt ro ra rf fsmt in
  let (max_id, conflicting_clause) = import_trace fsmt fproof in
  (rt, ro, ra, rf, roots, max_id, conflicting_clause)
let checkerdebug fsmt fproof = SmtCommands.checker_debug (import_all fsmt fproof)

(*
Take an SMT2-formula and an SMTInterpol-proof and check whether the proof proves the formula unsatisfiable.
This function is called when Coq calls the vernacular command 'Smtinterpol.checker'.
*)
let checker formula proof= SmtCommands.checker (import_all formula proof)open Smtlib2_ast
