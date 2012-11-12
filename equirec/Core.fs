(*
Copyright (c) 2003, Benjamin C. Pierce
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

/// Core typechecking and evaluation functions.
module Core

open Ast

(* ------------------------   EVALUATION  ------------------------ *)
let rec isval ctx t = match t with | TmAbs (_, _, _, _) -> true | _ -> false
  
exception NoRuleApplies
  
let rec eval1 ctx t =
  match t with
  | TmApp (fi, (TmAbs (_, x, tyT11, t12)), v2) when isval ctx v2 ->
      termSubstTop v2 t12
  | TmApp (fi, v1, t2) when isval ctx v1 ->
      let t2' = eval1 ctx t2 in TmApp (fi, v1, t2')
  | TmApp (fi, t1, t2) -> let t1' = eval1 ctx t1 in TmApp (fi, t1', t2)
  | _ -> raise NoRuleApplies
  
let rec eval ctx t =
  try let t' = eval1 ctx t in eval ctx t' with | NoRuleApplies -> t
  
let rec computety ctx tyT =
  match tyT with
  | (TyRec (x, tyS1) as tyS) -> typeSubstTop tyS tyS1
  | _ -> raise NoRuleApplies
  
let rec simplifyty ctx tyT =
  try let tyT' = computety ctx tyT in simplifyty ctx tyT'
  with | NoRuleApplies -> tyT
  
let rec private tyeqv' seen ctx tyS tyT =
  (List.mem (tyS, tyT) seen) ||
    (match (tyS, tyT) with
     | (TyRec (x, tyS1), _) ->
         tyeqv' ((tyS, tyT) :: seen) ctx (typeSubstTop tyS tyS1) tyT
     | (_, TyRec (x, tyT1)) ->
         tyeqv' ((tyS, tyT) :: seen) ctx tyS (typeSubstTop tyT tyT1)
     | (TyId b1, TyId b2) -> b1 = b2
     | (TyArr (tyS1, tyS2), TyArr (tyT1, tyT2)) ->
         (tyeqv' seen ctx tyS1 tyT1) && (tyeqv' seen ctx tyS2 tyT2)
     | _ -> false)
  
let tyeqv ctx tyS tyT = tyeqv' [] ctx tyS tyT
  
(* ------------------------   TYPING  ------------------------ *)
let rec typeof ctx t =
  match t with
  | TmVar (fi, i, _) -> getTypeFromContext fi ctx i
  | TmAbs (fi, x, tyT1, t2) ->
      let ctx' = addbinding ctx x (VarBind tyT1) in
      let tyT2 = typeof ctx' t2 in TyArr (tyT1, typeShift (-1) tyT2)
  | TmApp (fi, t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2
      in
        (match simplifyty ctx tyT1 with
         | TyArr (tyT11, tyT12) ->
             if tyeqv ctx tyT2 tyT11
             then tyT12
             else error fi "parameter type mismatch"
         | _ -> error fi "arrow type expected")
  
