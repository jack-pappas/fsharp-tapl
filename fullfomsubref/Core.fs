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
exception NoRuleApplies
  
let rec isnumericval ctx t =
  match t with
  | TmZero _ -> true
  | TmSucc (_, t1) -> isnumericval ctx t1
  | _ -> false
  
let rec isval ctx t =
  match t with
  | TmTrue _ -> true
  | TmFalse _ -> true
  | TmFloat _ -> true
  | TmString _ -> true
  | TmUnit _ -> true
  | TmTag (_, l, t1, _) -> isval ctx t1
  | TmLoc (_, _) -> true
  | t when isnumericval ctx t -> true
  | TmAbs (_, _, _, _) -> true
  | TmRecord (_, fields) -> List.for_all (fun (l, ti) -> isval ctx ti) fields
  | TmPack (_, _, v1, _) when isval ctx v1 -> true
  | TmTAbs (_, _, _, _) -> true
  | _ -> false
  
exception ErrorEncountered
  
type store = term list

let emptystore = []
  
let extendstore store v = ((List.length store), (List.append store [ v ]))
  
let lookuploc store l = List.nth store l
  
let updatestore store n v =
  let rec f s =
    match s with
    | (0, v' :: rest) -> v :: rest
    | (n, v' :: rest) -> v' :: (f ((n - 1), rest))
    | _ -> error dummyinfo "updatestore: bad index"
  in f (n, store)
  
let shiftstore i store = List.map (fun t -> termShift i t) store
  
let rec eval1 ctx store t =
  match t with
  | TmIf (_, (TmTrue _), t2, t3) -> (t2, store)
  | TmIf (_, (TmFalse _), t2, t3) -> (t3, store)
  | TmLet (fi, x, v1, t2) when isval ctx v1 -> ((termSubstTop v1 t2), store)
  | TmLet (fi, x, t1, t2) ->
      let (t1', store') = eval1 ctx store t1
      in ((TmLet (fi, x, t1', t2)), store')
  | (TmFix (fi, v1) as t) when isval ctx v1 ->
      (match v1 with
       | TmAbs (_, _, _, t12) -> ((termSubstTop t t12), store)
       | _ -> raise NoRuleApplies)
  | TmFix (fi, t1) ->
      let (t1', store') = eval1 ctx store t1 in ((TmFix (fi, t1')), store')
  | TmRecord (fi, fields) ->
      let rec evalafield l =
        (match l with
         | [] -> raise NoRuleApplies
         | (l, vi) :: rest when isval ctx vi ->
             let (rest', store') = evalafield rest
             in (((l, vi) :: rest'), store')
         | (l, ti) :: rest ->
             let (ti', store') = eval1 ctx store ti
             in (((l, ti') :: rest), store')) in
      let (fields', store') = evalafield fields
      in ((TmRecord (fi, fields')), store')
  | TmProj (fi, ((TmRecord (_, fields) as v1)), l) when isval ctx v1 ->
      (try ((List.assoc l fields), store)
       with | Not_found -> raise NoRuleApplies)
  | TmProj (fi, t1, l) ->
      let (t1', store') = eval1 ctx store t1
      in ((TmProj (fi, t1', l)), store')
  | TmTag (fi, l, t1, tyT) ->
      let (t1', store') = eval1 ctx store t1
      in ((TmTag (fi, l, t1', tyT)), store')
  | TmCase (fi, (TmTag (_, li, v11, _)), branches) when isval ctx v11 ->
      (try
         let (x, body) = List.assoc li branches
         in ((termSubstTop v11 body), store)
       with | Not_found -> raise NoRuleApplies)
  | TmCase (fi, t1, branches) ->
      let (t1', store') = eval1 ctx store t1
      in ((TmCase (fi, t1', branches)), store')
  | TmAscribe (fi, v1, tyT) when isval ctx v1 -> (v1, store)
  | TmAscribe (fi, t1, tyT) ->
      let (t1', store') = eval1 ctx store t1
      in ((TmAscribe (fi, t1', tyT)), store')
  | TmVar (fi, n, _) ->
      (match getbinding fi ctx n with
       | TmAbbBind (t, _) -> (t, store)
       | _ -> raise NoRuleApplies)
  | TmRef (fi, t1) ->
      if not (isval ctx t1)
      then
        (let (t1', store') = eval1 ctx store t1
         in ((TmRef (fi, t1')), store'))
      else
        (let (l, store') = extendstore store t1
         in ((TmLoc (dummyinfo, l)), store'))
  | TmDeref (fi, t1) ->
      if not (isval ctx t1)
      then
        (let (t1', store') = eval1 ctx store t1
         in ((TmDeref (fi, t1')), store'))
      else
        (match t1 with
         | TmLoc (_, l) -> ((lookuploc store l), store)
         | _ -> raise NoRuleApplies)
  | TmAssign (fi, t1, t2) ->
      if not (isval ctx t1)
      then
        (let (t1', store') = eval1 ctx store t1
         in ((TmAssign (fi, t1', t2)), store'))
      else
        if not (isval ctx t2)
        then
          (let (t2', store') = eval1 ctx store t2
           in ((TmAssign (fi, t1, t2')), store'))
        else
          (match t1 with
           | TmLoc (_, l) -> ((TmUnit dummyinfo), (updatestore store l t2))
           | _ -> raise NoRuleApplies)
  | TmError fi -> raise ErrorEncountered
  | TmTimesfloat (fi, (TmFloat (_, f1)), (TmFloat (_, f2))) ->
      ((TmFloat (fi, f1 *. f2)), store)
  | TmTimesfloat (fi, ((TmFloat (_, f1) as t1)), t2) ->
      let (t2', store') = eval1 ctx store t2
      in ((TmTimesfloat (fi, t1, t2')), store')
  | TmTimesfloat (fi, t1, t2) ->
      let (t1', store') = eval1 ctx store t1
      in ((TmTimesfloat (fi, t1', t2)), store')
  | TmSucc (fi, t1) ->
      let (t1', store') = eval1 ctx store t1 in ((TmSucc (fi, t1')), store')
  | TmPred (_, (TmZero _)) -> ((TmZero dummyinfo), store)
  | TmPred (_, (TmSucc (_, nv1))) when isnumericval ctx nv1 -> (nv1, store)
  | TmPred (fi, t1) ->
      let (t1', store') = eval1 ctx store t1 in ((TmPred (fi, t1')), store')
  | TmIsZero (_, (TmZero _)) -> ((TmTrue dummyinfo), store)
  | TmIsZero (_, (TmSucc (_, nv1))) when isnumericval ctx nv1 ->
      ((TmFalse dummyinfo), store)
  | TmIsZero (fi, t1) ->
      let (t1', store') = eval1 ctx store t1
      in ((TmIsZero (fi, t1')), store')
  | TmTApp (fi, (TmTAbs (_, x, _, t11)), tyT2) ->
      ((tytermSubstTop tyT2 t11), store)
  | TmTApp (fi, t1, tyT2) ->
      let (t1', store') = eval1 ctx store t1
      in ((TmTApp (fi, t1', tyT2)), store')
  | TmApp (fi, (TmAbs (_, x, tyT11, t12)), v2) when isval ctx v2 ->
      ((termSubstTop v2 t12), store)
  | TmApp (fi, v1, t2) when isval ctx v1 ->
      let (t2', store') = eval1 ctx store t2
      in ((TmApp (fi, v1, t2')), store')
  | TmApp (fi, t1, t2) ->
      let (t1', store') = eval1 ctx store t1
      in ((TmApp (fi, t1', t2)), store')
  | TmIf (fi, t1, t2, t3) ->
      let (t1', store') = eval1 ctx store t1
      in ((TmIf (fi, t1', t2, t3)), store')
  | TmUnpack (fi, _, _, (TmPack (_, tyT11, v12, _)), t2) when isval ctx v12
      -> ((tytermSubstTop tyT11 (termSubstTop (termShift 1 v12) t2)), store)
  | TmUnpack (fi, tyX, x, t1, t2) ->
      let (t1', store') = eval1 ctx store t1
      in ((TmUnpack (fi, tyX, x, t1', t2)), store')
  | TmPack (fi, tyT1, t2, tyT3) ->
      let (t2', store') = eval1 ctx store t2
      in ((TmPack (fi, tyT1, t2', tyT3)), store')
  | _ -> raise NoRuleApplies
  
let rec eval ctx store t =
    try let (t', store') = eval1 ctx store t
        eval ctx store' t'
    with
    | NoRuleApplies ->
        (t, store)
    | ErrorEncountered ->
        (TmError dummyinfo), store
  
(* ------------------------   KINDING  ------------------------ *)
let istyabb ctx i =
  match getbinding dummyinfo ctx i with
  | TyAbbBind (tyT, _) -> true
  | _ -> false
  
let gettyabb ctx i =
  match getbinding dummyinfo ctx i with
  | TyAbbBind (tyT, _) -> tyT
  | _ -> raise NoRuleApplies
  
let rec computety ctx tyT =
  match tyT with
  | TyVar (i, _) when istyabb ctx i -> gettyabb ctx i
  | TyApp ((TyAbs (_, _, tyT12)), tyT2) -> typeSubstTop tyT2 tyT12
  | _ -> raise NoRuleApplies
  
let rec simplifyty ctx tyT =
  let tyT =
    match tyT with
    | TyApp (tyT1, tyT2) -> TyApp (simplifyty ctx tyT1, tyT2)
    | tyT -> tyT
  in
    try let tyT' = computety ctx tyT in simplifyty ctx tyT'
    with | NoRuleApplies -> tyT
  
let rec tyeqv ctx tyS tyT =
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT
  in
    match (tyS, tyT) with
    | (TyArr (tyS1, tyS2), TyArr (tyT1, tyT2)) ->
        (tyeqv ctx tyS1 tyT1) && (tyeqv ctx tyS2 tyT2)
    | (TyTop, TyTop) -> true
    | (TyId b1, TyId b2) -> b1 = b2
    | (TyString, TyString) -> true
    | (TyUnit, TyUnit) -> true
    | (TyFloat, TyFloat) -> true
    | (TyVar (i, _), _) when istyabb ctx i -> tyeqv ctx (gettyabb ctx i) tyT
    | (_, TyVar (i, _)) when istyabb ctx i -> tyeqv ctx tyS (gettyabb ctx i)
    | (TyVar (i, _), TyVar (j, _)) -> i = j
    | (TyBool, TyBool) -> true
    | (TyNat, TyNat) -> true
    | (TyRecord fields1, TyRecord fields2) ->
        ((List.length fields1) = (List.length fields2)) &&
          (List.for_all
             (fun (li2, tyTi2) ->
                try
                  let tyTi1 = List.assoc li2 fields1 in tyeqv ctx tyTi1 tyTi2
                with | Not_found -> false)
             fields2)
    | (TyVariant fields1, TyVariant fields2) ->
        ((List.length fields1) = (List.length fields2)) &&
          (List.for_all
             (fun (li2, tyTi2) ->
                try
                  let tyTi1 = List.assoc li2 fields1 in tyeqv ctx tyTi1 tyTi2
                with | Not_found -> false)
             fields2)
    | (TyAll (tyX1, tyS1, tyS2), TyAll (_, tyT1, tyT2)) ->
        let ctx1 = addname ctx tyX1
        in (tyeqv ctx tyS1 tyT1) && (tyeqv ctx1 tyS2 tyT2)
    | (TySome (tyX1, tyS1, tyS2), TySome (_, tyT1, tyT2)) ->
        let ctx1 = addname ctx tyX1
        in (tyeqv ctx tyS1 tyT1) && (tyeqv ctx1 tyS2 tyT2)
    | (TyAbs (tyX1, knKS1, tyS2), TyAbs (_, knKT1, tyT2)) ->
        (knKS1 = knKT1) &&
          (let ctx = addname ctx tyX1 in tyeqv ctx tyS2 tyT2)
    | (TyApp (tyS1, tyS2), TyApp (tyT1, tyT2)) ->
        (tyeqv ctx tyS1 tyT1) && (tyeqv ctx tyS2 tyT2)
    | (TyRef tyS, TyRef tyT) -> tyeqv ctx tyS tyT
    | (TySource tyS, TySource tyT) -> tyeqv ctx tyS tyT
    | (TySink tyS, TySink tyT) -> tyeqv ctx tyS tyT
    | _ -> false
  
let rec getkind fi ctx i =
  match getbinding fi ctx i with
  | TyVarBind tyT -> kindof ctx tyT
  | TyAbbBind (_, (Some knK)) -> knK
  | TyAbbBind (_, None) ->
      error fi ("No kind recorded for variable " ^ (index2name fi ctx i))
  | _ ->
      error fi
        ("getkind: Wrong kind of binding for variable " ^
           (index2name fi ctx i))
and kindof ctx tyT =
  match tyT with
  | TyRecord fldtys ->
      (List.iter
         (fun (l, tyS) ->
            if (kindof ctx tyS) <> KnStar
            then error dummyinfo "Kind * expected"
            else ())
         fldtys;
       KnStar)
  | TyVariant fldtys ->
      (List.iter
         (fun (l, tyS) ->
            if (kindof ctx tyS) <> KnStar
            then error dummyinfo "Kind * expected"
            else ())
         fldtys;
       KnStar)
  | TyVar (i, _) -> let knK = getkind dummyinfo ctx i in knK
  | TyAll (tyX, tyT1, tyT2) ->
      let ctx' = addbinding ctx tyX (TyVarBind tyT1)
      in
        (if (kindof ctx' tyT2) <> KnStar
         then error dummyinfo "Kind * expected"
         else ();
         KnStar)
  | TyAbs (tyX, knK1, tyT2) ->
      let ctx' = addbinding ctx tyX (TyVarBind (maketop knK1)) in
      let knK2 = kindof ctx' tyT2 in KnArr (knK1, knK2)
  | TyApp (tyT1, tyT2) ->
      let knK1 = kindof ctx tyT1 in
      let knK2 = kindof ctx tyT2
      in
        (match knK1 with
         | KnArr (knK11, knK12) ->
             if knK2 = knK11
             then knK12
             else error dummyinfo "parameter kind mismatch"
         | _ -> error dummyinfo "arrow kind expected")
  | TySome (tyX, tyT1, tyT2) ->
      let ctx' = addbinding ctx tyX (TyVarBind tyT1)
      in
        (if (kindof ctx' tyT2) <> KnStar
         then error dummyinfo "Kind * expected"
         else ();
         KnStar)
  | TyArr (tyT1, tyT2) ->
      (if (kindof ctx tyT1) <> KnStar
       then error dummyinfo "star kind expected"
       else ();
       if (kindof ctx tyT2) <> KnStar
       then error dummyinfo "star kind expected"
       else ();
       KnStar)
  | TyRef tyT ->
      (if (kindof ctx tyT) <> KnStar
       then error dummyinfo "star kind expected"
       else ();
       KnStar)
  | TySource tyT ->
      (if (kindof ctx tyT) <> KnStar
       then error dummyinfo "star kind expected"
       else ();
       KnStar)
  | TySink tyT ->
      (if (kindof ctx tyT) <> KnStar
       then error dummyinfo "star kind expected"
       else ();
       KnStar)
  | _ -> KnStar
  
let checkkindstar fi ctx tyT =
  let k = kindof ctx tyT
  in if k = KnStar then () else error fi "Kind * expected"
  
(* ------------------------   SUBTYPING  ------------------------ *)
let rec promote ctx t =
  match t with
  | TyVar (i, _) ->
      (match getbinding dummyinfo ctx i with
       | TyVarBind tyT -> tyT
       | _ -> raise NoRuleApplies)
  | TyApp (tyS, tyT) -> TyApp (promote ctx tyS, tyT)
  | _ -> raise NoRuleApplies
  
let rec subtype ctx tyS tyT =
  (tyeqv ctx tyS tyT) ||
    (let tyS = simplifyty ctx tyS in
     let tyT = simplifyty ctx tyT
     in
       match (tyS, tyT) with
       | (_, TyTop) -> true
       | (TyBot, _) -> true
       | (TyArr (tyS1, tyS2), TyArr (tyT1, tyT2)) ->
           (subtype ctx tyT1 tyS1) && (subtype ctx tyS2 tyT2)
       | (TyRecord fS, TyRecord fT) ->
           List.for_all
             (fun (li, tyTi) ->
                try let tySi = List.assoc li fS in subtype ctx tySi tyTi
                with | Not_found -> false)
             fT
       | (TyVariant fS, TyVariant fT) ->
           List.for_all
             (fun (li, tySi) ->
                try let tyTi = List.assoc li fT in subtype ctx tySi tyTi
                with | Not_found -> false)
             fS
       | (TyVar (_, _), _) -> subtype ctx (promote ctx tyS) tyT
       | (TyAll (tyX1, tyS1, tyS2), TyAll (_, tyT1, tyT2)) ->
           ((subtype ctx tyS1 tyT1) && (subtype ctx tyT1 tyS1)) &&
             (let ctx1 = addbinding ctx tyX1 (TyVarBind tyT1)
              in subtype ctx1 tyS2 tyT2)
       | (TyAbs (tyX, knKS1, tyS2), TyAbs (_, knKT1, tyT2)) ->
           (knKS1 = knKT1) &&
             (let ctx = addbinding ctx tyX (TyVarBind (maketop knKS1))
              in subtype ctx tyS2 tyT2)
       | (TyApp (_, _), _) -> subtype ctx (promote ctx tyS) tyT
       | (TySome (tyX1, tyS1, tyS2), TySome (_, tyT1, tyT2)) ->
           ((subtype ctx tyS1 tyT1) && (subtype ctx tyT1 tyS1)) &&
             (let ctx1 = addbinding ctx tyX1 (TyVarBind tyT1)
              in subtype ctx1 tyS2 tyT2)
       | (TyRef tyT1, TyRef tyT2) ->
           (subtype ctx tyT1 tyT2) && (subtype ctx tyT2 tyT1)
       | (TyRef tyT1, TySource tyT2) -> subtype ctx tyT1 tyT2
       | (TySource tyT1, TySource tyT2) -> subtype ctx tyT1 tyT2
       | (TyRef tyT1, TySink tyT2) -> subtype ctx tyT2 tyT1
       | (TySink tyT1, TySink tyT2) -> subtype ctx tyT2 tyT1
       | (_, _) -> false)
  
let rec join ctx tyS tyT =
  if subtype ctx tyS tyT
  then tyT
  else
    if subtype ctx tyT tyS
    then tyS
    else
      (let tyS = simplifyty ctx tyS in
       let tyT = simplifyty ctx tyT
       in
         match (tyS, tyT) with
         | (TyRecord fS, TyRecord fT) ->
             let labelsS = List.map (fun (li, _) -> li) fS in
             let labelsT = List.map (fun (li, _) -> li) fT in
             let commonLabels =
               List.find_all (fun l -> List.mem l labelsT) labelsS in
             let commonFields =
               List.map
                 (fun li ->
                    let tySi = List.assoc li fS in
                    let tyTi = List.assoc li fT in (li, (join ctx tySi tyTi)))
                 commonLabels
             in TyRecord commonFields
         | (TyAll (tyX, tyS1, tyS2), TyAll (_, tyT1, tyT2)) ->
             if not ((subtype ctx tyS1 tyT1) && (subtype ctx tyT1 tyS1))
             then TyTop
             else
               (let ctx' = addbinding ctx tyX (TyVarBind tyT1)
                in TyAll (tyX, tyS1, join ctx' tyT1 tyT2))
         | (TyArr (tyS1, tyS2), TyArr (tyT1, tyT2)) ->
             TyArr (meet ctx tyS1 tyT1, join ctx tyS2 tyT2)
         | (TyRef tyT1, TyRef tyT2) ->
             if (subtype ctx tyT1 tyT2) && (subtype ctx tyT2 tyT1)
             then TyRef tyT1
             else (* Warning: this is incomplete... *)
               TySource (join ctx tyT1 tyT2)
         | (TySource tyT1, TySource tyT2) -> TySource (join ctx tyT1 tyT2)
         | (TyRef tyT1, TySource tyT2) -> TySource (join ctx tyT1 tyT2)
         | (TySource tyT1, TyRef tyT2) -> TySource (join ctx tyT1 tyT2)
         | (TySink tyT1, TySink tyT2) -> TySink (meet ctx tyT1 tyT2)
         | (TyRef tyT1, TySink tyT2) -> TySink (meet ctx tyT1 tyT2)
         | (TySink tyT1, TyRef tyT2) -> TySink (meet ctx tyT1 tyT2)
         | _ -> TyTop)
and meet ctx tyS tyT =
  if subtype ctx tyS tyT
  then tyS
  else
    if subtype ctx tyT tyS
    then tyT
    else
      (let tyS = simplifyty ctx tyS in
       let tyT = simplifyty ctx tyT
       in
         match (tyS, tyT) with
         | (TyRecord fS, TyRecord fT) ->
             let labelsS = List.map (fun (li, _) -> li) fS in
             let labelsT = List.map (fun (li, _) -> li) fT in
             let allLabels =
               List.append labelsS
                 (List.find_all (fun l -> not (List.mem l labelsS)) labelsT) in
             let allFields =
               List.map
                 (fun li ->
                    if List.mem li allLabels
                    then
                      (let tySi = List.assoc li fS in
                       let tyTi = List.assoc li fT
                       in (li, (meet ctx tySi tyTi)))
                    else
                      if List.mem li labelsS
                      then (li, (List.assoc li fS))
                      else (li, (List.assoc li fT)))
                 allLabels
             in TyRecord allFields
         | (TyAll (tyX, tyS1, tyS2), TyAll (_, tyT1, tyT2)) ->
             if not ((subtype ctx tyS1 tyT1) && (subtype ctx tyT1 tyS1))
             then raise Not_found
             else
               (let ctx' = addbinding ctx tyX (TyVarBind tyT1)
                in TyAll (tyX, tyS1, meet ctx' tyT1 tyT2))
         | (TyArr (tyS1, tyS2), TyArr (tyT1, tyT2)) ->
             TyArr (join ctx tyS1 tyT1, meet ctx tyS2 tyT2)
         | (TyRef tyT1, TyRef tyT2) ->
             if (subtype ctx tyT1 tyT2) && (subtype ctx tyT2 tyT1)
             then TyRef tyT1
             else (* Warning: this is incomplete... *)
               TySource (meet ctx tyT1 tyT2)
         | (TySource tyT1, TySource tyT2) -> TySource (meet ctx tyT1 tyT2)
         | (TyRef tyT1, TySource tyT2) -> TySource (meet ctx tyT1 tyT2)
         | (TySource tyT1, TyRef tyT2) -> TySource (meet ctx tyT1 tyT2)
         | (TySink tyT1, TySink tyT2) -> TySink (join ctx tyT1 tyT2)
         | (TyRef tyT1, TySink tyT2) -> TySink (join ctx tyT1 tyT2)
         | (TySink tyT1, TyRef tyT2) -> TySink (join ctx tyT1 tyT2)
         | _ -> TyBot)
  
(* ------------------------   TYPING  ------------------------ *)
let rec lcst ctx tyS =
  let tyS = simplifyty ctx tyS
  in try lcst ctx (promote ctx tyS) with | NoRuleApplies -> tyS
  
let rec typeof ctx t =
  match t with
  | TmVar (fi, i, _) -> getTypeFromContext fi ctx i
  | TmAbs (fi, x, tyT1, t2) ->
      (checkkindstar fi ctx tyT1;
       let ctx' = addbinding ctx x (VarBind tyT1) in
       let tyT2 = typeof ctx' t2 in TyArr (tyT1, typeShift (-1) tyT2))
  | TmApp (fi, t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2
      in
        (match lcst ctx tyT1 with
         | TyArr (tyT11, tyT12) ->
             if subtype ctx tyT2 tyT11
             then tyT12
             else error fi "parameter type mismatch"
         | TyBot -> TyBot
         | _ -> error fi "arrow type expected")
  | TmTrue fi -> TyBool
  | TmFalse fi -> TyBool
  | TmIf (fi, t1, t2, t3) ->
      if subtype ctx (typeof ctx t1) TyBool
      then join ctx (typeof ctx t2) (typeof ctx t3)
      else error fi "guard of conditional not a boolean"
  | TmRecord (fi, fields) ->
      let fieldtys = List.map (fun (li, ti) -> (li, (typeof ctx ti))) fields
      in TyRecord fieldtys
  | TmProj (fi, t1, l) ->
      (match lcst ctx (typeof ctx t1) with
       | TyRecord fieldtys ->
           (try List.assoc l fieldtys
            with | Not_found -> error fi ("label " ^ (l ^ " not found")))
       | TyBot -> TyBot
       | _ -> error fi "Expected record type")
  | TmLet (fi, x, t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let ctx' = addbinding ctx x (VarBind tyT1)
      in typeShift (-1) (typeof ctx' t2)
  | TmFloat _ -> TyFloat
  | TmTimesfloat (fi, t1, t2) ->
      if
        (subtype ctx (typeof ctx t1) TyFloat) &&
          (subtype ctx (typeof ctx t2) TyFloat)
      then TyFloat
      else error fi "argument of timesfloat is not a number"
  | TmCase (fi, t, cases) ->
      (match lcst ctx (typeof ctx t) with
       | TyVariant fieldtys ->
           (List.iter
              (fun (li, (xi, ti)) ->
                 try let _ = List.assoc li fieldtys in ()
                 with
                 | Not_found -> error fi ("label " ^ (li ^ " not in type")))
              cases;
            let casetypes =
              List.map
                (fun (li, (xi, ti)) ->
                   let tyTi =
                     try List.assoc li fieldtys
                     with
                     | Not_found -> error fi ("label " ^ (li ^ " not found")) in
                   let ctx' = addbinding ctx xi (VarBind tyTi)
                   in typeShift (-1) (typeof ctx' ti))
                cases
            in List.fold_left (join ctx) TyBot casetypes)
       | TyBot -> TyBot
       | _ -> error fi "Expected variant type")
  | TmTag (fi, li, ti, tyT) ->
      (match simplifyty ctx tyT with
       | TyVariant fieldtys ->
           (try
              let tyTiExpected = List.assoc li fieldtys in
              let tyTi = typeof ctx ti
              in
                if subtype ctx tyTi tyTiExpected
                then tyT
                else error fi "field does not have expected type"
            with | Not_found -> error fi ("label " ^ (li ^ " not found")))
       | _ -> error fi "Annotation is not a variant type")
  | TmAscribe (fi, t1, tyT) ->
      (checkkindstar fi ctx tyT;
       if subtype ctx (typeof ctx t1) tyT
       then tyT
       else error fi "body of as-term does not have the expected type")
  | TmString _ -> TyString
  | TmUnit fi -> TyUnit
  | TmInert (fi, tyT) -> tyT
  | TmFix (fi, t1) ->
      let tyT1 = typeof ctx t1
      in
        (match lcst ctx tyT1 with
         | TyArr (tyT11, tyT12) ->
             if subtype ctx tyT12 tyT11
             then tyT12
             else error fi "result of body not compatible with domain"
         | TyBot -> TyBot
         | _ -> error fi "arrow type expected")
  | TmRef (fi, t1) -> TyRef (typeof ctx t1)
  | TmLoc (fi, l) ->
      error fi "locations are not supposed to occur in source programs!"
  | TmDeref (fi, t1) ->
      (match lcst ctx (typeof ctx t1) with
       | TyRef tyT1 -> tyT1
       | TyBot -> TyBot
       | TySource tyT1 -> tyT1
       | _ -> error fi "argument of ! is not a Ref or Source")
  | TmAssign (fi, t1, t2) ->
      (match lcst ctx (typeof ctx t1) with
       | TyRef tyT1 ->
           if subtype ctx (typeof ctx t2) tyT1
           then TyUnit
           else error fi "arguments of := are incompatible"
       | TyBot -> let _ = typeof ctx t2 in TyBot
       | TySink tyT1 ->
           if subtype ctx (typeof ctx t2) tyT1
           then TyUnit
           else error fi "arguments of := are incompatible"
       | _ -> error fi "argument of ! is not a Ref or Sink")
  | TmError fi -> TyBot
  | TmTAbs (fi, tyX, tyT1, t2) ->
      let ctx = addbinding ctx tyX (TyVarBind tyT1) in
      let tyT2 = typeof ctx t2 in TyAll (tyX, tyT1, tyT2)
  | TmTApp (fi, t1, tyT2) ->
      let tyT1 = typeof ctx t1
      in
        (match lcst ctx tyT1 with
         | TyAll (_, tyT11, tyT12) ->
             (if not (subtype ctx tyT2 tyT11)
              then error fi "type parameter type mismatch"
              else ();
              typeSubstTop tyT2 tyT12)
         | _ -> error fi "universal type expected")
  | TmTry (fi, t1, t2) -> join ctx (typeof ctx t1) (typeof ctx t2)
  | TmZero fi -> TyNat
  | TmSucc (fi, t1) ->
      if subtype ctx (typeof ctx t1) TyNat
      then TyNat
      else error fi "argument of succ is not a number"
  | TmPred (fi, t1) ->
      if subtype ctx (typeof ctx t1) TyNat
      then TyNat
      else error fi "argument of pred is not a number"
  | TmIsZero (fi, t1) ->
      if subtype ctx (typeof ctx t1) TyNat
      then TyBool
      else error fi "argument of iszero is not a number"
  | TmPack (fi, tyT1, t2, tyT) ->
      (checkkindstar fi ctx tyT;
       (match simplifyty ctx tyT with
        | TySome (tyY, tyBound, tyT2) ->
            (if not (subtype ctx tyT1 tyBound)
             then error fi "hidden type not a subtype of bound"
             else ();
             let tyU = typeof ctx t2 in
             let tyU' = typeSubstTop tyT1 tyT2
             in
               if subtype ctx tyU tyU'
               then tyT
               else error fi "doesn't match declared type")
        | _ -> error fi "existential type expected"))
  | TmUnpack (fi, tyX, x, t1, t2) ->
      let tyT1 = typeof ctx t1
      in
        (match lcst ctx tyT1 with
         | TySome (tyY, tyBound, tyT11) ->
             let ctx' = addbinding ctx tyX (TyVarBind tyBound) in
             let ctx'' = addbinding ctx' x (VarBind tyT11) in
             let tyT2 = typeof ctx'' t2 in typeShift (-2) tyT2
         | _ -> error fi "existential type expected")
  
let evalbinding ctx store b =
  match b with
  | TmAbbBind (t, tyT) ->
      let (t', store') = eval ctx store t in ((TmAbbBind (t', tyT)), store')
  | bind -> (bind, store)
  

