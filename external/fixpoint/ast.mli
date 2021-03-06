(*
 * Copyright � 2009 The Regents of the University of California. All rights reserved.
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
 *)

(**
 * This module implements a DAG representation for expressions and
 * predicates: each sub-predicate or sub-expression is paired with
 * a unique int ID, which enables constant time hashing.
 * However, one must take care when using DAGS:
 * (1) they can only be constructed using the appropriate functions
 * (2) when destructed via pattern-matching, one must discard the ID
 *)

(*******************************************************)
(********************** Base Logic  ********************)
(*******************************************************)

module Cone : sig
  type 'a t = Empty | Cone of ('a * 'a t) list
  val map : ('a -> 'b) -> 'a t -> 'b t
end

module Constant :
  sig
    type t = Int  of int
           | Real of float
           | Lit  of string * Sort.t

    val to_string : t -> string
    val print : Format.formatter -> t -> unit
  end

type tag  (* externally opaque *)

type expr = expr_int * tag

and expr_int =
  | Con  of Constant.t
  | Var  of Symbol.t
  | App  of Symbol.t * expr list
  | Bin  of expr * Prims.bop * expr
  | Ite  of pred * expr * expr
  | Fld  of Symbol.t * expr             (* NOTE: Fld (s, e) == App ("field"^s,[e]) *)
  | Cst  of expr * Sort.t
  | Bot
  | MExp of expr list
  | MBin of expr * Prims.bop list * expr

and pred = pred_int * tag

and pred_int =
  | True
  | False
  | And  of pred list
  | Or   of pred list
  | Not  of pred
  | Imp  of pred * pred
  | Iff  of pred * pred
  | Bexp of expr
  | Atom of expr * Prims.brel * expr
  | MAtom of expr * Prims.brel list * expr
  | Forall of ((Symbol.t * Sort.t) list) * pred

(* Constructors : expressions *)
val eTim : expr * expr -> expr
val eInt : int -> expr
val eCon : Constant.t -> expr
val eMExp : expr list -> expr
val eMod : expr * expr -> expr
val eModExp : expr * expr -> expr
val eVar : Symbol.t -> expr
val eApp : Symbol.t * expr list -> expr
val eBin : expr * Prims.bop * expr -> expr
val eMBin : expr * Prims.bop list * expr -> expr
val eIte : pred * expr * expr -> expr
val eFld : Symbol.t * expr -> expr
val eCst : expr * Sort.t -> expr
(* Constructors : predicates *)
val pTrue  : pred
val pFalse : pred
val pAtom  : expr * Prims.brel * expr -> pred
val pMAtom : expr * Prims.brel list * expr -> pred
val pAnd   : pred list -> pred
val pOr    : pred list -> pred
val pNot   : pred -> pred
val pImp   : (pred * pred) -> pred
val pIff   : (pred * pred) -> pred
val pBexp  : expr -> pred
val pForall: ((Symbol.t * Sort. t) list) * pred -> pred
val pEqual : expr * expr -> pred
val pUequal : expr * expr -> pred
val neg_brel : Prims.brel -> Prims.brel

module Expression :
sig
  module Hash : Hashtbl.S with type key = expr

  val print     : Format.formatter -> expr -> unit
  val show      : expr -> unit
  val to_string : expr -> string

  val unwrap    : expr -> expr_int
  val support   : expr -> Symbol.t list
  val subst     : expr -> Symbol.t -> expr -> expr
  val map       : (pred -> pred) -> (expr -> expr) -> expr -> expr
  val iter      : (pred -> unit) -> (expr -> unit) -> expr -> unit
end


module Predicate :
sig
  module Hash : Hashtbl.S with type key = pred

  val print     : Format.formatter -> pred -> unit
  val show      : pred -> unit
  val to_string : pred -> string

  val unwrap    : pred -> pred_int
  val support   : pred -> Symbol.t list
  val subst     : pred -> Symbol.t -> expr -> pred
  val map       : (pred -> pred) -> (expr -> expr) -> pred -> pred
  val iter      : (pred -> unit) -> (expr -> unit) -> pred -> unit
  val is_contra : pred -> bool
  val is_tauto  : pred -> bool
end

module Subst :
  sig
    type t
    val empty                : t
    val is_empty             : t -> bool
    val extend               : t -> (Symbol.t * expr) -> t
    val compose               : t -> t -> t
    val of_list              : (Symbol.t * expr) list -> t
    val simultaneous_of_list : (Symbol.t * expr) list -> t
    val to_list              : t -> (Symbol.t * expr) list
    val print                : Format.formatter -> t -> unit
    val apply                : t -> Symbol.t -> expr option
  end


module Horn :
  sig
    type pr = string * string list
    type gd = C of pred | K of pr
    type t  = pr * gd list
    val print: Format.formatter -> t -> unit
    val support: t -> string list
  end

val print_stats    : unit -> unit
val fixdiv         : pred -> pred
val zero           : expr
val one            : expr
val bot            : expr

val symm_pred      : pred -> pred
val unify_pred     : pred -> pred -> Subst.t option
val substs_expr    : expr -> Subst.t -> expr
val substs_pred    : pred -> Subst.t -> pred
val simplify_pred  : pred -> pred
val conjuncts      : pred -> pred list


val sortcheck_expr : (Sort.tycon -> bool) -> (Symbol.t -> Sort.t option) -> expr -> Sort.t option
val sortcheck_pred : (Sort.tycon -> bool) -> (Symbol.t -> Sort.t option) -> pred -> bool
val sortcheck_app  : (Sort.tycon -> bool) -> (Symbol.t -> Sort.t option) -> Sort.t option -> Symbol.t -> expr list -> (Sort.sub * Sort.t) option

val into_of_expr   : expr -> int option
