(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2019                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


val pp_symbol : Smtlib2_ast.symbol -> string
val string_of_identifier : Smtlib2_ast.identifier -> string
val string_of_qualidentifier : Smtlib2_ast.qualidentifier -> string
val parse_smt2bv : string -> bool list
val bigint_bv : Big_int.big_int -> int -> string
val import_smtlib2 :
  SmtBtype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  SmtAtom.Atom.reify_tbl ->
  SmtAtom.Form.reify -> string -> SmtAtom.Form.t list
