(*
 * Copyright © 2009 The Regents of the University of California. All rights reserved.
 *
 * Permission is hereby granted, without written agreement and without
 * license or royalty fees, to use, copy, modify, and distribute this
 * software and its documentation for any purpose, provided that the
 * above copyright notice and the following two paragraphs appear in
 * all copies of this software.
 *
 * IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY
 * FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES
 * ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN
 * IF THE UNIVERSITY OF CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 *
 * THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS
 * ON AN "AS IS" BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION
 * TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 *)

(* Theories API *)

module type THEORY = sig
  type context
  type sort
  type ast
  type appDef
  type sortDef

  val sym_sort    : appDef  -> Sort.t
  val sym_name    : appDef  -> Symbol.t
  val sort_name   : sortDef -> Sort.tycon
  val mk_thy_sort : sortDef -> context -> sort list -> sort
  val mk_thy_app  : appDef  -> context -> sort list -> ast list -> ast
  val theories    : unit -> sortDef list * appDef list
end

module type SMTSOLVER = sig

  (* Types *)
  type context
  type symbol
  type ast
  type sort
  type fun_decl

  (* Sorts *)
  val mkIntSort      : context -> sort
  val mkRealSort     : context -> sort
  val mkBoolSort     : context -> sort

  (* Expression *)
  val mkAll : context -> sort array -> symbol array -> ast -> ast
  val mkApp : context -> fun_decl -> ast list -> ast
  val mkMul : context -> ast -> ast -> ast
  val mkDiv : context -> ast -> ast -> ast
  val mkAdd : context -> ast -> ast -> ast
  val mkSub : context -> ast -> ast -> ast
  val mkMod : context -> ast -> ast -> ast

  (* Predicates *)
  val mkIte     : context -> ast -> ast -> ast -> ast
  val mkInt     : context -> int -> sort -> ast
  val mkReal    : context -> float -> sort -> ast
  val mkLit     : context -> string -> sort -> ast
  val mkTrue    : context -> ast
  val mkFalse   : context -> ast
  val mkNot     : context -> ast -> ast
  val mkAnd     : context -> ast list -> ast
  val mkOr      : context -> ast list -> ast
  val mkImp     : context -> ast -> ast -> ast
  val mkIff     : context -> ast -> ast -> ast
  val mkRel     : context -> Prims.brel   -> ast -> ast -> ast

  (* Conversions *)
  val astString     : context -> ast -> string
  val sortString    : context -> sort -> string

  (* Set Theory Operations *)
  val mkSetSort     : context -> sort   -> sort
  val mkEmptySet    : context -> sort -> ast
  val mkSetAdd      : context -> ast -> ast -> ast
  val mkSetMem      : context -> ast -> ast -> ast
  val mkSetCup      : context -> ast -> ast -> ast
  val mkSetCap      : context -> ast -> ast -> ast
  val mkSetDif      : context -> ast -> ast -> ast
  val mkSetSub      : context -> ast -> ast -> ast

  (* Map Theory Operations *)

  val mkMapSort     : context -> sort -> sort -> sort
  val mkMapSelect   : context -> ast -> ast -> ast
  val mkMapStore    : context -> ast -> ast -> ast -> ast


  (* BitVector Theory Operations *)
  val mkSizeSort    : context -> int  -> sort
  val mkBitSort     : context -> sort -> sort
  val mkBitAnd      : context -> ast  -> ast -> ast
  val mkBitOr       : context -> ast  -> ast -> ast



  (* Constructors *)
  val mkContext      : (string * string) array -> context

  val stringSymbol   : context -> string -> symbol
  val isBool         : context -> ast -> bool
  val boundVar       : context -> int    -> sort -> ast

  (* Declarations *)
  val var            : context -> symbol -> sort -> ast
  val funcDecl       : context -> symbol -> sort array -> sort -> fun_decl

  (* Queries *)
  val bracket        : context -> (unit -> 'a) -> 'a
  val assertAxiom    : context -> ast -> unit
  val assertPreds    : context -> ast list -> unit
  val assertDistinct : context -> ast list -> unit
  val unsat          : context -> bool

  (* Stats *)
  val print_stats    : Format.formatter -> unit -> unit
end

class type prover =
  object
       (* AST/TC Interface *)
       method interp_syms :  unit -> (Symbol.t * Sort.t) list

       (* Query Interface *)
       method set_filter  :  'a . Sort.t Symbol.SMap.t
                          -> Symbol.t
                          -> Ast.pred list
                          -> ('a * Ast.pred) list
                          -> 'a list

       method print_stats : Format.formatter -> unit

       (* Counterexample Interface *)
       method is_contra   :  Sort.t Symbol.SMap.t
                          -> Ast.pred
                          -> bool


       method unsat_suffix :  Sort.t Symbol.SMap.t
                           -> Ast.pred                     (* background predicate   *)
                           -> Ast.pred list                (* [p0,...,pn] *)
                           -> int option                   (* max j st. p /\i=j..n pi unsat *)
end

module type PROVER = sig
  val mkProver :  Sort.t list                      (* sorts        *)
               -> Sort.t Symbol.SMap.t         (* environment  *)
               -> Ast.pred list                        (* axioms       *)
               -> Symbol.t list                    (* distinct constants, sorts in env *)
               -> prover
end
