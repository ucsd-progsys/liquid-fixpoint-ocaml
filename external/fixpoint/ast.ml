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
 * ON AN "AS IS" BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION
 * TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 *
 *)

(**
 * This module implements a DAG representation for expressions and
 * predicates: each sub-predicate or sub-expression is paired with
 * a unique int ID, which enables constant time hashing.
 * However, one must take care when using DAGS:
 * (1) they can only be constructed using the appropriate functions
 * (2) when destructed via pattern-matching, one must discard the ID
 *)


module F  = Format
module Misc = FixMisc
module SM = Misc.StringMap
module IS = Misc.IntSet
open Misc.Ops
open Prims
type tag  = int

let mydebug = false

module Cone = struct
  type 'a t = Empty | Cone of ('a * 'a t) list

  let rec map f = function
    | Empty    -> Empty
    | Cone xcs -> Cone (List.map (f <**> map f) xcs)
end

module Constant =
  struct

    type t = Int  of int
           | Real of float
           | Lit  of string * Sort.t

    let to_string = function
      | Int i     -> string_of_int i
      | Real i    -> string_of_float i ^ "0"
      | Lit (s,t) -> Printf.sprintf "(lit \"%s\" %s)" s (Sort.to_string t)

    let print fmt s =
      to_string s |> Format.fprintf fmt "%s"
  end

type expr = expr_int * tag

and expr_int =
  | Con  of Constant.t
  | Var  of Symbol.t
  | App  of Symbol.t * expr list
  | Bin  of expr * bop * expr
  | Ite  of pred * expr * expr
  | Fld  of Symbol.t * expr             (* NOTE: Fld (s, e) == App ("field"^s,[e]) *)
  | Cst  of expr * Sort.t
  | Bot
  | MExp of expr list
  | MBin of expr * bop list * expr

and pred = pred_int * tag

and pred_int =
  | True
  | False
  | And   of pred list
  | Or    of pred list
  | Not   of pred
  | Imp   of pred * pred
  | Iff   of pred * pred
  | Bexp  of expr
  | Atom  of expr * brel * expr
  | MAtom of expr * brel list * expr
  | Forall of ((Symbol.t * Sort.t) list) * pred

let list_hash b xs =
  List.fold_left (fun v (_,id) -> 2*v + id) b xs

module ExprHashconsStruct = struct
  type t = expr_int
  let sub_equal e1 e2 =
    match e1, e2 with
      | Con c1, Con c2 ->
          c1 = c2
      | MExp es1, MExp es2 ->
          es1 = es2
      | Var x1, Var x2 ->
          x1 = x2
      | App (s1, e1s), App (s2, e2s) ->
	  (s1 = s2) &&
          (try List.for_all2 (==) e1s e2s with _ -> false)
      | Bin (e1, op1, e1'), Bin (e2, op2, e2') ->
          op1 = op2 && e1 == e2 && e1' == e2'
      | MBin (e1, ops1, e1'), MBin (e2, ops2, e2') ->
          ops1 = ops2 && e1 == e2 && e1' == e2'
      | Ite (ip1,te1,ee1), Ite (ip2,te2,ee2) ->
	      ip1 == ip2 && te1 == te2 && ee1 == ee2
      | Fld (s1, e1), Fld (s2, e2) ->
          s1 = s2 && e1 == e2
      | Cst (e1, s1), Cst (e2, s2) ->
          s1 = s2 && e1 == e2
      | _ ->
          false

  let hash = function
    | Con (Constant.Int x) ->
        x
    | Con (Constant.Real x) ->
        64 + int_of_float x
    | Con (Constant.Lit (s,_)) ->
        32 + Hashtbl.hash s
    | MExp es ->
        list_hash 6 es
    | Var x ->
        Hashtbl.hash x
    | App (s, es) ->
        list_hash ((Hashtbl.hash s) + 1) es
    | Bin ((_,id1), op, (_,id2)) ->
        (Hashtbl.hash op) + 1 + (2 * id1) + id2
    | MBin ((_,id1), op::_ , (_,id2)) ->
        (Hashtbl.hash op) + 1 + (2 * id1) + id2
    | Ite ((_,id1), (_,id2), (_,id3)) ->
        32 + (4 * id1) + (2 * id2) + id3
    | Fld (s, (_,id)) ->
        (Hashtbl.hash s) + 12 + id
    | Cst ((_, id), t) ->
        id + Hashtbl.hash (Sort.to_string t)
    | Bot ->
        0
    | _ -> assertf "pattern error in A.pred hash"

end

module ExprHashcons = Hashcons.Make(ExprHashconsStruct)

module PredHashconsStruct = struct

  type t = pred_int

  let sub_equal p1 p2 =
    match p1, p2 with
      | True, True | False, False ->
          true
      | And p1s, And p2s  | Or  p1s, Or p2s ->
          (try List.for_all2 (==) p1s p2s with _ -> false)
      | Not p1, Not p2 ->
          p1 == p2
      | Imp (p1, p1'), Imp (p2, p2') ->
          p1 == p2 && p1' == p2'
      | Iff (p1,p1'), Iff (p2,p2') ->
          p1 == p2 && p1' == p2'
      | Bexp e1, Bexp e2 ->
          e1 == e2
      | Atom (e1, r1, e1'), Atom (e2, r2, e2') ->
          r1 = r2 && e1 == e2 && e1' == e2'
      | MAtom (e1, r1, e1'), MAtom (e2, r2, e2') ->
          r1 = r2 && e1 == e2 && e1' == e2'
      | Forall(q1s,p1), Forall(q2s,p2) ->
          q1s = q2s && p1 == p2
      | _ ->
          false

 let hash = function
   | True ->
       0
   | False ->
       1
   | And ps ->
       list_hash 2 ps
   | Or ps ->
       list_hash 3 ps
   | Not (_,id) ->
       8 + id
   | Imp ((_,id1), (_,id2)) ->
       20 + (2 * id1) + id2
   | Iff ((_,id1), (_,id2)) ->
       28 + (2 * id1) + id2
   | Bexp (_, id) ->
       32 + id
   | Atom ((_,id1), r, (_,id2)) ->
       36 + (Hashtbl.hash r) + (2 * id1) + id2
   | MAtom ((_,id1), r, (_,id2)) ->
       42 + (Hashtbl.hash r) + (2 * id1) + id2
   | Forall(qs,(_,id)) ->
       50 + (2 * (Hashtbl.hash qs)) + id
end

module PredHashcons = Hashcons.Make(PredHashconsStruct)

let ewr = ExprHashcons.wrap
let euw = ExprHashcons.unwrap
let pwr = PredHashcons.wrap
let puw = PredHashcons.unwrap

(* Constructors: Expressions *)
let eCon  = fun c  -> ewr  (Con c)
let eMExp = fun es -> ewr  (MExp es)
let eInt  = fun i  -> eCon (Constant.Int i)
let zero  = eInt 0
let one   = eInt 1
let bot  = ewr Bot
let eMod = fun (e, e') -> ewr (Bin (e, Mod, e'))

(* let eMod = fun (e, m) -> ewr (Bin (e, Mod, eInt m)) *)

let eModExp = fun (e, m) -> ewr (Bin (e, Mod, m))
let eVar = fun s -> ewr (Var s)
let eApp = fun (s, es) -> ewr (App (s, es))
let eBin = fun (e1, op, e2) -> ewr (Bin (e1, op, e2))

let eMBin = fun (e1, ops, e2) -> ewr (MBin (e1, ops, e2))
let eIte = fun (ip,te,ee) -> ewr (Ite(ip,te,ee))
let eFld = fun (s,e) -> ewr (Fld (s,e))
let eCst = fun (e,t) -> ewr (Cst (e, t))

let eTim = function
  | (Con (Constant.Int n1), _), (Con (Constant.Int n2), _) ->
      ewr (Con (Constant.Int (n1 * n2)))
  | (Con (Constant.Int 1), _), e2 ->
      e2
  | (Con (Constant.Int (-1)), _), e2 ->
      eBin (zero, Minus, e2)
  | (e1, e2) -> eBin (e1, Times, e2)


let rec conjuncts = function
  | And ps, _ -> Misc.flap conjuncts ps
  | True, _   -> []
  | p         -> [p]


(* Constructors: Predicates *)
let pTrue   = pwr True
let pFalse  = pwr False
let pAtom   = fun (e1, r, e2) -> pwr (Atom (e1, r, e2))
let pMAtom  = fun (e1, r, e2) -> pwr (MAtom (e1, r, e2))
let pOr     = fun ps -> pwr (Or ps)
let pNot    = fun p  -> pwr (Not p)
let pBexp   = fun e  -> pwr (Bexp e)
let pImp    = fun (p1,p2) -> pwr (Imp (p1,p2))
let pIff    = fun (p1,p2) -> pwr (Iff (p1,p2))
let pForall = fun (qs, p) -> pwr (Forall (qs, p))
let pEqual  = fun (e1,e2) -> pAtom (e1, Eq, e2)
let pUequal = fun (e1,e2) -> pAtom (e1, Ueq, e2)


let pAnd   = fun ps -> match Misc.flap conjuncts ps with
                       | []  -> pTrue
                       | [p] -> p
                       | ps  -> pwr (And (Misc.flap conjuncts ps))



module ExprHash = Hashtbl.Make(struct
  type t = expr
  let equal (_,x) (_,y) = (x = y)
  let hash (_,x) = x
end)

module PredHash = Hashtbl.Make(struct
  type t = pred
  let equal (_,x) (_,y) = (x = y)
  let hash (_,x) = x
end)

let bop_to_string = function
  | Plus  -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Div   -> "/"
  | Mod   -> "mod"

let brel_to_string = function
  | Eq  -> "="
  | Ne  -> "!="
  | Gt  -> ">"
  | Ge  -> ">="
  | Lt  -> "<"
  | Le  -> "<="
  | Ueq -> "~~"
  | Une -> "!~"

let print_brel ppf r =
  F.fprintf ppf "%s" (brel_to_string r)

let print_binding ppf (s,t) =
  F.fprintf ppf "%a:%a" Symbol.print s Sort.print t

let bind_to_string  (s,t) =
  Printf.sprintf "%s:%s" (Symbol.to_string s) (Sort.to_string t)

let rec print_expr ppf e = match euw e with
  | Con c ->
      F.fprintf ppf "%a" Constant.print c
  | MExp es ->
      F.fprintf ppf "[%a]" (Misc.pprint_many false " ; " print_expr) es
  | Var s ->
      F.fprintf ppf "%a" Symbol.print s
  | App (s, es) ->
      F.fprintf ppf "%a([%a])"
        Symbol.print s
        (Misc.pprint_many false "; " print_expr) es
  | Bin (e1, op, e2) ->
      F.fprintf ppf "(%a %s %a)"
        print_expr e1
        (bop_to_string op)
        print_expr e2
  | MBin (e1, ops, e2) ->
      F.fprintf ppf "(%a [%s] %a)"
        print_expr e1
        (ops |>: bop_to_string |> String.concat " ; ")
        print_expr e2

  | Ite (ip, te, ee) ->
      F.fprintf ppf "if %a then %a else %a"
        print_pred ip
        print_expr te
        print_expr ee

  (* DEPRECATED TO HELP HS Parser
  | Ite(ip,te,ee) ->
      F.fprintf ppf "(%a ? %a : %a)"
        print_pred ip
        print_expr te
        print_expr ee
  *)

  | Fld(s, e) ->
      F.fprintf ppf "%a.%s" print_expr e (Symbol.to_string s)
  | Cst(e,t) ->
      F.fprintf ppf "(%a : %a)"
        print_expr e
        Sort.print t
  | Bot ->
      F.fprintf ppf "_|_"

and print_pred ppf p = match puw p with
  | True ->
      F.fprintf ppf "true"
  | False ->
      F.fprintf ppf "false"
  | Bexp (App (s, es), _) ->
      F.fprintf ppf "%a(%a)" Symbol.print s (Misc.pprint_many false ", " print_expr) es
  | Bexp e ->
      F.fprintf ppf "(Bexp %a)" print_expr e
  | Not p ->
      F.fprintf ppf "(~ (%a))" print_pred p
  | Imp (p1, p2) ->
      F.fprintf ppf "(%a => %a)" print_pred p1 print_pred p2
  | Iff (p1, p2) ->
      F.fprintf ppf "(%a <=> %a)" print_pred p1 print_pred p2
  | And ps -> begin match ps with [] -> F.fprintf ppf "true" | _ ->
      F.fprintf ppf "&& %a" (Misc.pprint_many_brackets true print_pred) ps
    end
  | Or ps -> begin match ps with [] -> F.fprintf ppf "false" | _ ->
      F.fprintf ppf "|| %a" (Misc.pprint_many_brackets true print_pred) ps
    end

  | Atom (e1, r, e2) ->
      (* F.fprintf ppf "@[(%a %s %a)@]" *)
      F.fprintf ppf "(%a %s %a)"
        print_expr e1
        (brel_to_string r)
        print_expr e2
  | MAtom (e1, rs, e2) ->
      F.fprintf ppf "(%a [%a] %a)"
      (* F.fprintf ppf "@[(%a [%a] %a)@]"  *)
        print_expr e1
        (Misc.pprint_many false " ; " print_brel) rs
        print_expr e2
  | Forall (qs, p) ->
      F.fprintf ppf "forall [%a] . %a"
        (Misc.pprint_many false "; " print_binding) qs
        print_pred p

let rec expr_to_string e =
  match euw e with
  | Con c ->
      Constant.to_string c
  | MExp es ->
      Printf.sprintf "[%s]" (es |>: expr_to_string |> String.concat " ; ")
  | Var s ->
      Symbol.to_string s
  | App (s, es) ->
      Printf.sprintf "%s([%s])"
        (Symbol.to_string s)
        (es |> List.map expr_to_string |> String.concat "; ")
  | Bin (e1, op, e2) ->
      Printf.sprintf "(%s %s %s)"
        (expr_to_string e1) (bop_to_string op) (expr_to_string e2)
  | MBin (e1, ops, e2) ->
      Printf.sprintf "(%s [%s] %s)"
        (expr_to_string e1)
        (ops |> List.map bop_to_string |> String.concat "; ")
        (expr_to_string e2)
  | Ite(ip,te,ee) ->
      Printf.sprintf "(%s ? %s : %s)"
        (pred_to_string ip) (expr_to_string te) (expr_to_string ee)
  | Fld(s,e) ->
      Printf.sprintf "%s.%s" (expr_to_string e) (Symbol.to_string s)
  | Cst(e,t) ->
      Printf.sprintf "(%s : %s)" (expr_to_string e) (Sort.to_string t)
  | Bot ->
      Printf.sprintf "_|_"


and pred_to_string p =
  match puw p with
    | True ->
        "true"
    | False ->
        "false"
    | Bexp e ->
        Printf.sprintf "(Bexp %s)" (expr_to_string e)
    | Not p ->
        Printf.sprintf "(~ (%s))" (pred_to_string p)
    | Imp (p1, p2) ->
        Printf.sprintf "(%s => %s)" (pred_to_string p1) (pred_to_string p2)
    | Iff (p1, p2) ->
        Printf.sprintf "(%s <=> %s)" (pred_to_string p1) (pred_to_string p2)
    | And ps ->
        Printf.sprintf "&& [%s]" (List.map pred_to_string ps |> String.concat " ; ")
    | Or ps ->
        Printf.sprintf "|| [%s]" (List.map pred_to_string ps |> String.concat ";")
    | Atom (e1, r, e2) ->
        Printf.sprintf "(%s %s %s)"
        (expr_to_string e1) (brel_to_string r) (expr_to_string e2)
    | MAtom (e1, rs, e2) ->
        Printf.sprintf "(%s [%s] %s)"
        (expr_to_string e1)
        (List.map brel_to_string rs |> String.concat " ; ")
        (expr_to_string e2)
    | Forall (qs,p) ->
        Printf.sprintf "forall [%s] . %s"
        (List.map bind_to_string qs |> String.concat "; ") (pred_to_string p)

let rec pred_map hp he fp fe p =
  let rec pm p =
    try PredHash.find hp p with Not_found -> begin
      let p' =
        match puw p with
        | True | False as p1 ->
            p1
        | And ps ->
            And (List.map pm ps)
        | Or ps ->
            Or (List.map pm ps)
        | Not p ->
            Not (pm p)
        | Imp (p1, p2) ->
            Imp (pm p1, pm p2)
        | Iff (p1, p2) ->
            Iff (pm p1, pm p2)
        | Bexp e ->
            Bexp (expr_map hp he fp fe e)
        | Atom (e1, r, e2) ->
            Atom (expr_map hp he fp fe e1, r, expr_map hp he fp fe e2)
        | MAtom (e1, rs, e2) ->
            MAtom (expr_map hp he fp fe e1, rs, expr_map hp he fp fe e2)
        | Forall (qs, p) ->
            Forall (qs, pm p) in
      let rv = fp (pwr p') in
      let _  = PredHash.add hp p rv in
      rv
    end in pm p

and expr_map hp he fp fe e =
  let rec em e =
    try ExprHash.find he e with Not_found -> begin
      let e' =
        match euw e with
        | Con _ | Var _ | Bot as e1 ->
            e1
        | MExp es ->
            MExp (List.map em es)
        | App (f, es) ->
            App (f, List.map em es)
        | Bin (e1, op, e2) ->
            Bin (em e1, op, em e2)
        | MBin (e1, ops, e2) ->
            MBin (em e1, ops, em e2)
        | Ite (ip, te, ee) ->
            Ite (pred_map hp he fp fe ip, em te, em ee)
        | Fld (s, e1) ->
            Fld (s, em e1)
        | Cst (e1, t) ->
            Cst (em e1, t)
      in
      let rv = fe (ewr e') in
      let _  = ExprHash.add he e rv in
      rv
    end in em e

let rec pred_iter fp fe pw =
  begin match puw pw with
    | True | False -> ()
    | Bexp e -> expr_iter fp fe e
    | Not p -> pred_iter fp fe p
    | Imp (p1, p2) -> pred_iter fp fe p1; pred_iter fp fe p2
    | Iff (p1, p2) -> pred_iter fp fe p1; pred_iter fp fe p2
    | And ps | Or ps -> List.iter (pred_iter fp fe) ps
    | Atom (e1, _, e2) -> expr_iter fp fe e1; expr_iter fp fe e2
    | MAtom (e1, _, e2) -> expr_iter fp fe e1; expr_iter fp fe e2
    | Forall (_, p) -> pred_iter fp fe p (* pmr: looks wrong, but so does pred_map *)
  end;
  fp pw

and expr_iter fp fe ew =
  begin match puw ew with
    | Con _ | Var _ | Bot ->
        ()
    | MExp es ->
        List.iter (expr_iter fp fe) es
    | App (_, es)  ->
        List.iter (expr_iter fp fe) es
    | Bin (e1, _, e2)  ->
        expr_iter fp fe e1; expr_iter fp fe e2
    | MBin (e1, _, e2)  ->
        expr_iter fp fe e1; expr_iter fp fe e2
    | Ite (ip, te, ee) ->
        pred_iter fp fe ip; expr_iter fp fe te; expr_iter fp fe ee
    | Fld (_, e1) | Cst (e1, _) ->
        expr_iter fp fe e1
  end;
  fe ew

let esub x e = function
  | (Var y), _ when x = y -> e
  | _ as e1 -> e1

let expr_subst hp he e x e' =
  expr_map hp he id (esub x e') e

let pred_subst hp he p x e' =
  pred_map hp he id (esub x e') p

module Expression =
  struct

    module Hash   = ExprHash

    let to_string = expr_to_string

    (* let print     = fun fmt e -> Format.pp_print_string fmt (to_string e)
     *)
    let print = print_expr

    let show      = print Format.std_formatter

    let map fp fe e =
      let hp = PredHash.create 251 in
      let he = ExprHash.create 251 in
      expr_map hp he fp fe e

    let iter fp fe e =
      expr_iter fp fe e

    let subst e x e' =
      map id (esub x e') e

    let substs e xes =
      map id (fun e -> List.fold_left (esub |> Misc.uncurry |> Misc.flip) e xes) e

    let support e =
      let xs = ref Symbol.SSet.empty in
      iter un begin function
        | (Var x), _
        | (App (x,_)),_ -> xs := Symbol.SSet.add x !xs
        | _               -> ()
      end e;
      Symbol.SSet.elements !xs |> List.sort compare

    let unwrap = euw

    let has_bot p =
      let r = ref false in
      iter un begin function
        | Bot, _ -> r := true
        | _      -> ()
      end p;
      !r

  end

module Predicate = struct
  module Hash = PredHash

  let to_string = pred_to_string
  let print     = print_pred
  let show      = print Format.std_formatter

  let map fp fe p =
	let hp = PredHash.create 251 in
	let he = ExprHash.create 251 in
    pred_map hp he fp fe p

  let iter fp fe p =
    pred_iter fp fe p

  let subst p x e' =
    map id (esub x e') p

  let substs p xes =
    map id (fun e -> List.fold_left (esub |> Misc.uncurry |> Misc.flip) e xes) p

  let support p =
    let xs = ref Symbol.SSet.empty in
    iter un begin function
      | (Var x), _
      | (App (x,_)),_ -> xs := Symbol.SSet.add x !xs;
      | _               -> ()
    end p;
    Symbol.SSet.elements !xs |> List.sort compare

  (*
  let size p =
	let c = ref 0           in
    let f = fun _ -> incr c in
    let _ = iter f f p      in
    !c

  let size p =
	let c = ref 0                    in
    let _ = iter (fun _ -> incr c) p in
    !c
  *)

  let unwrap = puw

  let is_contra =
    let t = PredHash.create 17 in
    let _ = [pFalse; pNot pTrue; pAtom (zero, Eq, one); pAtom (one, Eq, zero)]
            |> List.iter (fun p-> PredHash.replace t p ()) in
    fun p -> PredHash.mem t p


  let rec is_tauto  = function
    | Atom(e1, Eq,  e2), _ -> snd e1 == snd e2
    | Atom(e1, Ueq, e2), _ -> snd e1 == snd e2
    | Imp (p1, p2), _      -> snd p1 == snd p2
    | And ps, _            -> List.for_all is_tauto ps
    | Or  ps, _            -> List.exists is_tauto ps
    | True, _              -> true
    | _                    -> false

  let has_bot p =
    let r = ref false in
    iter un begin function
      | Bot, _ -> r := true
      | _      -> ()
    end p;
    !r

  end

let print_stats _ =
  Printf.printf "Ast Stats. [none] \n"


(********************************************************************************)
(************************** Rationalizing Division ******************************)
(********************************************************************************)

let expr_isdiv = function
  | Bin (_, Div, _), _ -> true
  | _                  -> false

let pull_divisor = function
  | Bin (_, Div, (Con (Constant.Int i),_)), _ -> i
  | _ -> 1

let calc_cm e1 e2 =
    pull_divisor e1 * pull_divisor e2

let rec apply_mult m = function
  | Bin (e, Div,  (Con (Constant.Int d),_)), _ ->
      let _   = assert ((m/d) * d = m) in
      eTim ((eCon (Constant.Int (m/d))), e)
  | Bin (e1, op, e2), _ ->
      eBin (apply_mult m e1, op, apply_mult m e2)
  | Con (Constant.Int i), _ ->
      eCon (Constant.Int (i*m))
  | e ->
      eTim (eCon (Constant.Int m), e)

let rec pred_isdiv = function
  | True,_ | False,_ ->
      false
  | And ps,_ | Or ps,_ ->
      List.exists pred_isdiv ps
  | Not p, _ | Forall (_, p), _ ->
      pred_isdiv p
  | Imp (p1, p2), _ ->
      pred_isdiv p1 || pred_isdiv p2
  | Iff (p1, p2), _ ->
      pred_isdiv p1 || pred_isdiv p2
  | Bexp e, _ ->
      expr_isdiv e
  | Atom (e1, _, e2), _ ->
      expr_isdiv e1 || expr_isdiv e2
  | _ -> failwith "Unexpected: pred_isdiv"

let bound m e e1 e2 =
  pAnd [pAtom (apply_mult m e, Gt, apply_mult m e2);
        pAtom(apply_mult m e, Le, apply_mult m e1)]

let rec fixdiv = function
  | p when not (pred_isdiv p) ->
      p
  | Atom ((Var _,_) as e, Eq, e1), _ | Atom ((Con _, _) as e, Eq, e1), _ ->
      bound (calc_cm e e1) e e1 (eBin (e1, Minus, one))
  | And ps, _ ->
      pAnd (List.map fixdiv ps)
  | Or ps, _ ->
      pOr (List.map fixdiv ps)
  | Imp (p1, p2), _ ->
      pImp (fixdiv p1, fixdiv p2)
  | Iff (p1, p2), _ ->
      pIff (fixdiv p1, fixdiv p2)
  | Not p, _ ->
      pNot (fixdiv p)
  | p -> p

(***************************************************************************)
(*********** New Type Checking Expressions and Predicates ******************)
(***************************************************************************)

let solved_app f uf z = Misc.maybe_map snd (Sort.checkArity f uf z)

let splitArgs t = match Sort.func_of_t t with
  | None              -> ([], t)
  | Some (_, its, ot) -> (its, ot)

let rec ti_pred_list g f preds =
  (* logf "ti_pred_list" ; *)
  List.fold_left (fun (s, t) p ->
    let (s1, t1) = ti_pred g f p in
    let s2       = Sort.mgu 1 (Sort.apply_ty s1 t1) Sort.t_bool in
    (Sort.sub_compose s2 (Sort.sub_compose s1 s), Sort.t_bool)
  ) (Sort.sub_empty, Sort.t_bool) preds

and ti_pred g f p =
  (* logf ("ti_pred " ^ pred_to_string p) ; *)
 match puw p with
  | True
  | False  -> (Sort.sub_empty, Sort.t_bool)
  | And ps
  | Or  ps -> ti_pred_list g f ps
  | Not p  -> ti_pred g f p
  | Imp (p1, p2)
  | Iff (p1, p2) -> (ti_pred g f p1; ti_pred g f p2)
  | Bexp e       -> let (s1, t) = ti_expr g f e in
                    let tt = Sort.apply_ty s1 t in
                    (* let _  = logf ("will call mgu with t_bool in " ^
                     * Sort.to_string tt) in *)
                    let s2 = Sort.mgu 2 tt Sort.t_bool in
                    (Sort.sub_compose s2 s1, Sort.t_bool)
  | Atom (e1, brel, e2) -> ti_brel g f brel p e1 e2 (ti_expr g f e1) (ti_expr g f e2)

  | MAtom (e1, brels, e2) -> ti_brel_list g f brels p e1 e2 (ti_expr g f e1) (ti_expr g f e2)
  | Forall (qs, p) ->
     let f' = fun x -> match Misc.list_assoc_maybe x qs with None -> f x | y -> y
     in ti_pred g f' p

and ti_brel_list g f brels p e1 e2 st1 st2 =
  (* logf "ti_brel_list"; *)
  List.fold_left (fun (s, t) brel ->
    let (s1, t1) = ti_brel g f brel p e1 e2 st1 st2 in
    let tt = Sort.apply_ty s1 t1 in
    (* let _ =  logf ("ti_brel_list: will call mgu on " ^ Sort.to_string tt ^ " and " ^ Sort.to_string Sort.t_bool)  in *)
    let s2       = Sort.mgu 3 (Sort.apply_ty s1 t1) Sort.t_bool in
    (Sort.sub_compose s1 s |> Sort.sub_compose s2, Sort.t_bool)
  ) (Sort.sub_empty, Sort.t_bool) brels

(* NIKI TODO: check old implementation for pointer manipulation etc. *)
and ti_brel g f brel p e1 e2 (s1, t1) (s2, t2) =
  (* logf ("ti_brel " ^ pred_to_string p) ; *)
  let s        = Sort.sub_compose s1 s2        in
  let (so', t) = Sort.compat_brel f brel t1 t2 in
  match so' with
    | None    -> (s, t)
    | Some s' -> (Sort.sub_compose s' s, t)

(* This check is too strict, i.e., disallows x < y where, x, y :: Var @0 *)
(*            if unifiable (apply_ty s t1) Sort.t_bool
               then raise (UnificationError "ti_brel on bool")
               else (s, Sort.t_bool)
 *)

and ti_expr g f e =
  (* if mydebug then logf ("ti_expr " ^ Expression.to_string e) ;  *)
  match euw e with
  | Bot ->
      raise <| Sort.UnificationError "ti on Bot"
  | Con (Constant.Int _) ->
      (* logf ("ti_expr " ^ Expression.to_string e ^ " sort = " ^ Sort.to_string (Sort.t_int)); *)
      (Sort.sub_empty, Sort.t_int)
  | Con (Constant.Real _) ->
      (Sort.sub_empty, Sort.t_real)
  | Con (Constant.Lit (_, t)) ->
      (Sort.sub_empty, t)
  | Var x ->
      begin
        match f x with
        | Some t ->  let _, tt = Sort.instantiate_ty t in
                     (* logf ("ti_symbol " ^ Symbol.to_string x ^ " : " ^ Sort.to_string tt) ; *)
                     (Sort.sub_empty, tt)
        | None -> Sort.UnificationError (String.concat " " ["unbound variable"; Symbol.to_string x])
                  |> raise
      end
  | Ite (p, e1, e2) ->
       begin
         let (s1, tp) = ti_pred g f p in
         (* let _ = logf "will call ite" in *)
         let s2       = Sort.mgu 6 (Sort.apply_ty s1 tp) Sort.t_bool in
         let (s3, t1) = ti_expr g f e1 in
         let (s4, t2) = ti_expr g f e2 in
         let s        = Sort.sub_compose s1 s2
                     |> Sort.sub_compose s3
                     |> Sort.sub_compose s4 in
         let t1' = Sort.apply_ty s t1 in
         let t2' = Sort.apply_ty s t1 in
         (* let _ = logf "will call ite2" in *)
         let s5 = Sort.mgu 7 t1' t2'    in
         (Sort.sub_compose s s5, t1')
       end
   | Fld (x, e) -> raise (Sort.UnificationError "ti_expr on Fld")
   | Cst (e, t') ->
        let (s1, t) = ti_expr g f e in
        (* let _ = logf "will call Cst" in *)
        let s2 = Sort.mgu 8 t' (Sort.apply_ty s1 t) in
        (Sort.sub_compose s1 s2, t')
   | MExp [] -> raise (Sort.UnificationError "ti_expr on empty expression")

   | MExp (e::es) ->
        let st = ti_expr g f e in
        List.fold_left (fun (s1, _) e ->
          let (s2, t) = ti_expr g f e in
          let s = Sort.sub_compose s1 s2 in
          (s, Sort.apply_ty s t)
        ) st es
   | Bin (e1, op, e2) -> ti_op g f (ti_expr g f e1) (ti_expr g f e2) op
   | MBin (e1, ops, e2) -> ti_op_list g f (ti_expr g f e1) (ti_expr g f e2) ops
   | App (uf, es) -> let (s, t) = ti_app g f uf es |> snd in
                     (* logf ("ti_expr " ^ Expression.to_string e ^ " sort = " ^ Sort.to_string t); *)
                     (s, t)


and ti_op g f (s1, t1) (s2, t2) op
  = (* let _ = logf "ti_op" in *)
    let s12 = Sort.sub_compose s1 s2 in
    let s3 = Sort.mgu 9 (Sort.apply_ty s12 t1) (Sort.apply_ty s12 t2) in
    let s  = Sort.sub_compose s3 s12 in
    (s, Sort.apply_ty s t1)

and ti_op_list g f st1 st2 ops
  = (* let _ = logf "ti_op_list" in *)
    match ops with
  | [] -> Sort.UnificationError "ti_op_list: empty list" |>  raise
  | (op::_) -> ti_op g f st1 st2 op

and ti_app g f uf es =
    (* let _ = logf "ti_app" in *)
    let tf = match f uf with | None -> raise (Sort.UnificationError "unfound") |  Some t -> t in
    let (sf, rf) = Sort.instantiate_ty tf in
    let (t_is, t_o) = splitArgs rf in
    let sts =    List.combine es t_is
              |> List.fold_left begin fun s0 (e, t) ->
                   let (s1, t1) = ti_expr g f e in
                   let s12 = Sort.sub_compose s1 s0 in
                   let s3 = Sort.mgu 10 t (Sort.apply_ty s12 t1) in
                   Sort.sub_compose s3 s12
                 end Sort.sub_empty
    in
      (Sort.sub_apply sts sf, (sts, Sort.apply_ty sts t_o))

(* Interface *)
let check_pred g f p =
  (* logf ("\n\n check_pred " ^ Predicate.to_string p) ; *)
  try
    Sort.init_ti ();
    let t = Misc.uncurry Sort.apply_ty (ti_pred g f p) in
    Sort.unifiable t Sort.t_bool
  with
   | Sort.UnificationError _ -> false

let check_expr g f tExp e  =
  (* logf ("\n\n check_expr " ^ Expression.to_string e) ; *)
  Sort.init_ti ();
  try
    let t = ti_expr g f e |> Misc.uncurry Sort.apply_ty in
    match tExp with
     | None -> Some t
     | Some t' ->  if Sort.unifiable t t' then Some t else None
  with
    Sort.UnificationError _ -> None

let check_app g f tExp uf es =
  (* logf ("\n\n check_app " ^ Symbol.to_string uf ^ String.concat " " (List.map Expression.to_string es)) ; *)
  Sort.init_ti ();
  try
    let (s, (ss, t)) = ti_app g f uf es in
    let sub = {Sort.empty_sub with Sort.vars = s} in
    match tExp with
     | None -> Some (sub, t)
     | Some t' when Sort.unifiable t t' -> Some (sub, t)

     |_ -> None
  with
    Sort.UnificationError _ -> None


(***************************************************************************)
(************* Type Checking Expressions and Predicates ********************)
(***************************************************************************)

let rec sortcheck_expr g f expected_t e =
  match euw e with
  | Bot   ->
      None
  | Con (Constant.Int _) ->
      Some Sort.t_int
  | Con (Constant.Real _) ->
      Some Sort.t_real
  | Con (Constant.Lit (_, t)) ->
      Some t
  | Var s ->
      f s
  | Bin (e1, op, e2) ->
      sortcheck_op g f (e1, op, e2)
  | Ite (p, e1, e2) ->
      if sortcheck_pred g f p then
        match Misc.map_pair (sortcheck_expr g f None) (e1, e2) with
        | (Some t1, Some t2) ->
          begin
          match Sort.unify [t1] [t2] with
            | Some s -> Some (Sort.apply s t1)
            | None -> None
          end
        | _ -> None
      else None
  | Cst (e1, t) ->
      begin match euw e1 with
        | App (uf, es) -> sortcheck_app g f (Some t) uf es
        | _            ->
            match sortcheck_expr g f None e1 with
              | Some t1 when Sort.compat t t1 -> Some t
              | _                             -> None
      end

  | App (uf, es) ->
      sortcheck_app g f expected_t uf es

  | _ -> assertf "Ast.sortcheck_expr: unhandled expr = %s" (Expression.to_string e)


and sortcheck_app_sub g f so_expected uf es =
  f uf
  |> function None -> None | Some t ->
       Sort.func_of_t t
       |> function None -> None | Some tfun  ->
              let (tyArity, i_ts, o_t) = Sort.refresh_tfun tfun in
              let _  = asserts (List.length es = List.length i_ts)
                         "ERROR: uf arg-arity error: uf=%s" (Symbol.to_string uf) in
              let e_ts = (List.map some i_ts, es)
                       |> Misc.zipWith (sortcheck_expr g f)
                       |> Misc.map_partial id in
              if List.length e_ts <> List.length i_ts then
                  None
              else
                  match Sort.unify e_ts i_ts with
                    | None   -> None
                    | Some s ->
                        let t = Sort.apply s o_t in
                          match so_expected with
                            | None    -> Some (s, t)
                            | Some t' ->
                                match Sort.unifyWith s [t] [t'] with
                                  | None    -> None
                                  | Some s' -> Some (s', Sort.apply s' t)

and sortcheck_app g f tExp uf es =
  sortcheck_app_sub g f tExp uf es
  |> Misc.maybe_map snd
                    (*
  >> begin function
       | Some t -> Format.printf "sortcheck_app: e = %s , t = %s \n"
                     (expr_to_string (eApp (uf, es))) (Sort.to_string t)
       | None   -> Format.printf "sortcheck_app: e = %s FAILS\n"
                     (expr_to_string (eApp (uf, es)))
     end
                     *)

and sortcheck_op g f (e1, op, e2) =
  let (t1o, t2o) = Misc.map_pair (sortcheck_expr g f None) (e1, e2) in
  Sort.sortcheck_op f op t1o t2o

and sortcheck_rel g f p (e1, r, e2) =
  let t1o, t2o = (e1,e2) |> Misc.map_pair (sortcheck_expr g f None) in
  Sort.sortcheck_rel g f r t1o t2o

and sortcheck_pred g f p =
  match puw p with
    | True
    | False ->
        true
    | Bexp e ->
        sortcheck_expr g f (Some Sort.t_bool) e = Some Sort.t_bool
    | Not p ->
        sortcheck_pred g f p
    | Imp (p1, p2) | Iff (p1, p2) ->
        List.for_all (sortcheck_pred g f) [p1; p2]
    | And ps
    | Or ps ->
        List.for_all (sortcheck_pred g f) ps
    | Atom (e1, Ueq, e2)
      when !Constants.ueq_all_sorts
      -> (not (None = sortcheck_expr g f None e1)) &&
         (not (None = sortcheck_expr g f None e2))

    | Atom ((Con (Constant.Int(0)),_), _, e)
    | Atom (e, _, (Con (Constant.Int(0)),_))
      when not (!Constants.strictsortcheck)
      -> not (None = sortcheck_expr g f None e)

    | Atom (((Con _, _) as e), Eq, (App (uf, es), _))
    | Atom ((App (uf, es), _), Eq, ((Con _, _) as e))
    | Atom (((Var _, _) as e), Eq, (App (uf, es), _))
    | Atom ((App (uf, es), _), Eq, ((Var _, _) as e))
      -> begin match sortcheck_expr g f None e with
         | None   -> false
         | Some t -> not (None = sortcheck_app g f (Some t) uf es)
         end

    | Atom (((App (uf1, e1s), _) as e1), Eq, ((App (uf2, e2s), _) as e2))
      -> let t1o = solved_app f uf1 <| sortcheck_app_sub g f None uf1 e1s in
         let t2o = solved_app f uf2 <| sortcheck_app_sub g f None uf2 e2s in
         begin match t1o, t2o with
               | (Some t1, Some t2) -> (* let _ = F.printf "sortcheck Eq App1 %s" (Predicate.to_string p) in *) Sort.unifiable t1 t2
               | (None, None)       -> (* let _ = F.printf "sortcheck Eq App2 %s" (Predicate.to_string p) in *) false
               | (None, Some t2)    -> (* let _ = F.printf "sortcheck Eq App3 %s" (Predicate.to_string p) in *) not (None = sortcheck_app g f (Some t2) uf1 e1s)
               | (Some t1, None)    -> (* let _ = F.printf "sortcheck Eq App4 %s :: %s"
                   (Predicate.to_string p) (Sort.to_string t1) in *)
                   not (None = sortcheck_app g f (Some t1) uf2 e2s)
         end

    | Atom (e1, r, e2) ->
        sortcheck_rel g f p (e1, r, e2)
    | Forall (qs,p) ->
        (* let f' = fun x -> try List.assoc x qs with _ -> f x in *)
        let f' = fun x -> match Misc.list_assoc_maybe x qs with None -> f x | y -> y
        in sortcheck_pred g f' p
    | _ -> failwith "Unexpected: sortcheck_pred"

(* and sortcheck_pred f p =
  sortcheck_pred' f p
  >> (fun b -> if not b then F.eprintf "WARNING: Malformed Lhs Pred (%a)\n" Predicate.print p)
 *)

let opt_to_string p = function
  | None   -> "none"
  | Some x -> p x


(* API *)
let sortcheck_app g f tExp uf es =
  if (!Constants.newcheck)
   then check_app g f tExp uf es
   else (sortcheck_app_sub g f tExp uf es
         |> Sort.checkArity f uf)

let sortcheck_expr g f e
  = if (!Constants.newcheck)
     then check_expr g f None e
     else sortcheck_expr g f None e

                (*
  match uf_arity f uf, sortcheck_app_sub g f tExp uf es with
    | (Some n, Some (s, t)) ->
        if Sort.check_arity n s then
           Some (s, t)
        else
          None
          (*
          let msg = Printf.sprintf  "Ast.sortcheck_app: type params not instantiated %s: n = %d, s = %s, t = %s, tExp = %s"
                      (expr_to_string (eApp (uf, es)))
                      n
                      (Sort.sub_to_string s)
                      (Sort.to_string t)
                      (opt_to_string Sort.to_string tExp)
          in
             assertf "%s" msg
          *)
    | _ -> None
                 *)


let sortcheck_pred g f p =
  if (!Constants.newcheck)
   then check_pred g f p
   else sortcheck_pred g f p

(*   >> (fun b -> ignore <| F.printf "DEBUG: sortcheck_pred: p = %a, res = %b\n" Predicate.print p b)
*)

(***************************************************************************)
(************* Simplifying Expressions and Predicates **********************)
(***************************************************************************)

let pred_of_bool = function true -> pTrue | false -> pFalse

let rec remove_bot pol ((p, _) as pred) =
  match p with
  | Not p  ->
      pNot (remove_bot (not pol) p)
  | Imp (p, q) ->
      pImp (remove_bot (not pol) p, remove_bot pol q)
  | Forall (qs, p) ->
      pForall (qs, remove_bot pol p)
  | And ps ->
      ps |> List.map (remove_bot pol) |> pAnd
  | Or ps ->
      ps |> List.map (remove_bot pol) |> pOr
  | Bexp e when Expression.has_bot e ->
      pred_of_bool pol
  | Atom (e1, _, e2) when Expression.has_bot e1 || Expression.has_bot e2 ->
      pred_of_bool pol
  | _ ->
      pred

let remove_bot p =
  if Predicate.has_bot p
  then remove_bot true p
  else p

let symm_brel = function
  | Eq  -> Eq
  | Ueq -> Ueq
  | Ne  -> Ne
  | Une -> Une
  | Gt  -> Lt
  | Ge  -> Le
  | Lt  -> Gt
  | Le  -> Ge

let neg_brel = function
  | Eq  -> Ne
  | Ueq -> Une
  | Ne  -> Eq
  | Une -> Ueq
  | Gt  -> Le
  | Ge  -> Lt
  | Lt  -> Ge
  | Le  -> Gt

let rec push_neg ?(neg=false) ((p, _) as pred) =
  match p with
    | True   ->
        if neg then pFalse else pred
    | False  ->
        if neg then pTrue else pred
    | Bexp _ ->
        if neg then pNot pred else pred
    | Not p  ->
        push_neg ~neg:(not neg) p
    | Imp (p, q) ->
	if neg then pAnd [push_neg p; push_neg ~neg:true q]
	else pImp (push_neg p, push_neg q)
    | Iff (p, q) ->
        if neg then pIff (p, push_neg ~neg:true q)
        else pIff (push_neg p, push_neg q)
    | Forall (qs, p) ->
	let pred' = pForall (qs, push_neg ~neg:false p) in
	if neg then pNot pred' else pred'
    | And ps ->
        List.map (push_neg ~neg:neg) ps
        |> if neg then pOr else pAnd
    | Or ps ->
        List.map (push_neg ~neg:neg) ps
        |> if neg then pAnd else pOr
    | Atom (e1, brel, e2) ->
        if neg then pAtom (e1, neg_brel brel, e2) else pred
    | _ -> failwith "Unexpected: push_neg"

(* Andrey: TODO flatten nested conjunctions/disjunctions *)
let rec simplify_pred ((p, _) as pred) =
  match p with
    | Not p -> pNot (simplify_pred p)
    | Imp (p, q) -> pImp (simplify_pred p, simplify_pred q)
    | Forall (qs, p) -> pForall (qs, simplify_pred p)
    | And ps -> ps |> List.map simplify_pred
                   |> List.filter (not <.> Predicate.is_tauto)
                   |> (function | []  -> pTrue
                                | [p] -> p
                                | _ when List.exists Predicate.is_contra ps -> pFalse
                                | _   -> pAnd ps)
    | Or ps -> ps |> List.map simplify_pred
                  |> List.filter (not <.> Predicate.is_contra)
                  |> (function []  -> pFalse
                             | [p] -> p
                             | ps when List.exists Predicate.is_tauto ps -> pTrue
                             | ps  -> pOr ps)
    | _ -> pred


(**************************************************************************)
(*************************** Substitutions ********************************)
(**************************************************************************)

module Subst = struct

  type t = expr Symbol.SMap.t

  let valid xes =
    xes |> List.split
        |> Misc.app_snd (Misc.flap Expression.support)
        |> Misc.uncurry Misc.disjoint


  let extend s (x, e) =
    let s = Symbol.SMap.map (esub x e) s in
      if Symbol.SMap.mem x s then
        s
      else
        match e with
        | Var x', _ when x = x' -> s
        | _                     -> Symbol.SMap.add x e s

  let empty     = Symbol.SMap.empty
  let is_empty  = Symbol.SMap.is_empty
  let to_list   = Symbol.SMap.to_list
  let apply     = Misc.flip Symbol.SMap.maybe_find
  let of_list   = fun xes -> List.fold_left extend empty xes
  let simultaneous_of_list = Symbol.SMap.of_list
  let compose s t =
    let s' = Symbol.SMap.fold (fun x e s -> Symbol.SMap.map (esub x e) s) t s
    in Symbol.SMap.fold (fun x e s -> if Symbol.SMap.mem x s
                                         then s else Symbol.SMap.add x e s)
                        t s'
  let print_sub = fun ppf (x,e) -> F.fprintf ppf "[%a:=%a]" Symbol.print x Expression.print e
  let print     = fun ppf -> to_list <+> F.fprintf ppf "%a" (Misc.pprint_many false "" print_sub)

(* fun s1 s2 -> Symbol.SMap.fold (fun x e s -> extend s (x, e)) s2 s1 *)
(*   let apply     = Misc.flip Symbol.SMap.maybe_find *)

end


(**************************************************************************)
(******************* Horn Clauses: Parsing ARMC files *********************)
(**************************************************************************)

module Horn = struct

  type pr = string * string list
  type gd = C of pred | K of pr
  type t  = pr * gd list

  let print_pr ppf (x, xs) =
    Format.fprintf ppf "%s(%s)" x (String.concat "," xs)

  let print_gd ppf = function
    | C p -> Predicate.print ppf p
    | K x -> print_pr ppf x

  let print ppf (hd, gds) =
    Format.fprintf ppf "%a :- %a."
      print_pr hd
      (Misc.pprint_many false "," print_gd) gds

  let support_pr = snd
  let support_gd = function K pr -> support_pr pr | C p  -> p |> Predicate.support |> List.map Symbol.to_string
  let support    = fun (hd, gds) -> (support_pr hd) ++ (Misc.flap support_gd gds)
end

(* API *)
let simplify_pred = remove_bot <+> simplify_pred


let esub_su su e = match e with
  | ((Var y), _) -> Misc.maybe_default (Subst.apply su y) e
  | _            -> e

(* ORIG
   let substs_pred   = fun p su -> su |> Subst.to_list |> Predicate.substs p |> simplify_pred
*)

let substs_pred p su = Predicate.map  id (esub_su su) p
let substs_expr e su = Expression.map id (esub_su su) e

(****************************************************************************)
(******************** Unification of Predicates *****************************)
(****************************************************************************)

exception DoesNotUnify

let rec pUnify (p1, p2) =
  let res =
    match p1, p2 with
  | (Atom (e1, r1, e1'), _), (Atom (e2, r2, e2'), _) when r1 = r2 ->
      let s1       = eUnify (e1, e2) in
      let e1', e2' = Misc.map_pair ((Misc.flip Expression.substs) s1) (e1', e2') in
      let s2       = eUnify (e1', e2') in
      s1 ++ s2
  | (Bexp e1, _), (Bexp e2, _) ->
      eUnify (e1, e2)
  | (Not p1, _), (Not p2, _) ->
      pUnify (p1, p2)
  | (Imp (p1, p1'), _), (Imp (p2, p2'), _) ->
      psUnify ([p1; p1'], [p2; p2'])

  | (And p1s, _), (And p2s, _)
  | (Or p1s, _), (Or p2s, _)
    when List.length p1s = List.length p2s ->
      psUnify (p1s, p2s)
  | _, _ -> raise DoesNotUnify
  in
  let _ = if mydebug then
          (Format.printf "pUnify: p1 is %a, p2 is %a, subst = %a \n"
          Predicate.print p1 Predicate.print p2 Subst.print (Subst.of_list res)) in
  res

and psUnify (p1s, p2s) =
  let _ = asserts (List.length p1s = List.length p2s) "psUnify" in
  List.fold_left2 begin fun s p1 p2 ->
    (p1, p2)
    |> Misc.map_pair (fun p -> Predicate.substs p s)
    |> pUnify
    |> (fun s' -> s' ++ s)
  end [] p1s p2s

and eUnify = function
  | (Con c1, _), (Con c2, _) when c1 = c2 ->
      []
  | (Var x1, _), (Var x2, _) when x1 = x2 ->
      []
  | (Bin (e1, op1, e1'),_), (Bin (e2, op2, e2'), _) when op1 = op2 ->
      esUnify ([e1; e1'], [e2; e2'])
  | (Ite (p1, e1, e1'),_), (Ite (p2, e2, e2'), _) ->
      let s = pUnify (p1, p2) in
      let [e1; e1'; e2; e2'] = List.map ((Misc.flip Expression.substs) s) [e1; e1'; e2; e2'] in
      esUnify ([e1; e1'], [e2; e2'])
  | (Cst (e1, t1),_), (Cst (e2, t2),_) when t1 = t2 ->
      eUnify (e1, e2)
  | (App (uf1, e1s), _), (App (uf2, e2s),_) when uf1 = uf2 ->
      esUnify (e1s, e2s)
  | e, (Var x, _) | (Var x, _), e when Symbol.is_wild x ->
      [(x, e)]
  | _, _ -> raise DoesNotUnify

and esUnify (e1s, e2s) =
  let _ = asserts (List.length e1s = List.length e2s) "esUnify" in
  List.fold_left2 begin fun s e1 e2 ->
    (e1, e2)
    |> Misc.map_pair (fun e -> Expression.substs e s)
    |> eUnify
    |> (fun s' -> s' ++ s)
  end [] e1s e2s

(* API *)
let unify_pred p1 p2 = try pUnify (p1, p2) |> Subst.of_list |> some with DoesNotUnify -> None
let into_of_expr = function Con (Constant.Int i), _  -> Some i | _ -> None

let symm_pred = function
  | Atom (e1, r, e2), _ -> pAtom (e2, symm_brel r, e1)
  | p                   -> p

(* {{{
let rec expr_subst hp he e x e' =
  let rec esub e =
    try ExprHash.find he e with Not_found -> begin
      let rv =
        match euw e with
        | Var y when x = y ->
            e'
        | Con _ | Var _ ->
            e
        | App (s, es) ->
            App (s, List.map esub es) |> ewr
        | Bin (e1, op, e2) ->
            Bin (esub e1, op, esub e2) |> ewr
        | Ite (ip, te, ee) ->
            Ite (pred_subst hp he ip x e', esub te, esub ee) |> ewr
        | Fld (s, e1) ->
            Fld (s, esub e1) |> ewr in
      let _  = ExprHash.add he e rv in
      rv
    end in esub e

and pred_subst hp he e x e' =
  let rec s e =
    try PredHash.find h e with
	Not_found -> (let foo = s1 e in PredHash.add h e foo; foo)
  and s1 e =
    match puw e with
	True -> e
      | False -> e
      | And plist -> pwr (And(List.map s plist))
      | Or plist -> pwr (Or(List.map s plist))
      | Not p -> pwr (Not(s p))
      | Implies (p1, p2) -> pwr (Implies (s p1, s p2))
      | Equality (x,y) -> pwr (Equality(expr_subst h he x v vv,expr_subst h he y v vv))
      | Atom (_) -> e
      | Leq(x,y) -> pwr (Leq(expr_subst h he x v vv, expr_subst h he y v vv))
  in s e
}}} *)
(** {{{
      let rec support pred =
        let h = Hash.create 251 in
        let eh = Expression.Hash.create 251 in
        let sh = Hashtbl.create 251 in
        let res = ref [] in
        let add s = if not(Hashtbl.mem sh s) then Hashtbl.add sh s (); res := s :: !res in

        let se exp =
          let rec s exp =
            try Expression.Hash.find eh exp with
                Not_found -> Expression.Hash.add eh exp (); s1 exp
          and s1 exp =
            match euw exp with
                Constant(_) -> ()
              | Application (func, args) ->
                  add func; List.iter s args
              | Variable(sym) -> add sym
              | Sum(args) -> List.iter s args
              | Coeff(c,t) -> s t
              | Ite _ -> failwith "ite not supported"
          in s exp in

        let rec s exp =
          try Hash.find h exp with
              Not_found -> Hash.add h exp (); s1 exp
        and s1 pred =
          match puw pred with
              True -> ()
            | False -> ()
            | And plist -> List.iter s plist
            | Or plist -> List.iter s plist
            | Not p -> s p
            | Implies (p1, p2) -> s p1; s p2
            | Equality (x,y) -> se x; se y
            | Leq (x,y) -> se x; se y
            | Atom (s) -> ()
        in s pred; List.rev !res

      let h = PredHash.create 251 in
        let rec ip p =
          let _ = f p in
          if not (PredHash.mem h p) then begin
            let _ = PredHash.add h p () in
            match puw p with
            | And ps | Or ps ->
                List.iter ip plist
            | Not p  | Forall (_,p) ->
                ip p
            | Imp (p1, p2) ->
                ip p1; ip p2
            | _ -> ()
          end in
        ip p
   }}} *)
(* {{{

      (* Translate predicate to a satisfiability-equivalent predicate without Ite *)

      let temp_ctr = ref 0
      let new_temp () =
	let n = "$$$" ^ (string_of_int !temp_ctr) in
	  (temp_ctr := !temp_ctr + 1; n)

      let elim_ite sp =
	let cnsts = ref [] in
	let he = Expression.Hash.create 251 in
	let hp = Hash.create 251 in
	let rec te e =
	  try Expression.Hash.find he e
	  with Not_found -> (let foo = te1 e in Expression.Hash.add he e foo; foo)
	and te1 e =
	  match euw e with
	      Constant(c) -> e
	    | Application (func, args) ->
		ewr (Application (func, List.map te args))
	    | Variable(v) -> ewr (Variable(v))
	    | Sum(args) -> ewr (Sum(List.map te args))
	    | Coeff(c,t) -> ewr (Coeff(c,te t))
	    | Ite(si,st,se) ->
		let temp = ewr (Variable(new_temp())) in
		let i = tp si in
		let tv = te st and ev = te se in
		  begin
		    cnsts := pwr (Or [pwr (Not i); pwr (Equality(temp,(tv)))]) :: (!cnsts);
		    cnsts := pwr (Or [i; pwr (Equality(temp,(ev)))]) :: (!cnsts);
		    temp
		  end
	and tp p =
	  try Hash.find hp p
	  with Not_found -> (let foo = tp1 p in Hash.add hp p foo; foo)
	and tp1 p =
	  match puw p with
	      True -> p
	    | False -> p
	    | And plist -> pwr (And (List.map tp plist))
	    | Or plist -> pwr (Or (List.map tp plist))
	    | Not p -> pwr (Not (tp p))
	    | Implies (p1, p2) -> pwr (Implies((tp p1),(tp p2)))
	    | Equality (x,y) -> pwr(Equality((te x),(te y)))
	    | Leq (x,y) -> pwr(Leq((te x),(te y)))
	    | Atom (s) -> p
	in
	let foo = tp sp in
	  pwr (And(foo :: !cnsts))
    }}} *)
