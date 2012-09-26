//
module Ast


(* ---------------------------------------------------------------------- *)
(* Datatypes *)

type term =
    | TmTrue of info
    | TmFalse of info
    | TmIf of info * term * term * term
    | TmZero of info
    | TmSucc of info * term
    | TmPred of info * term
    | TmIsZero of info * term

type command =
    | Eval of info * term

(* ---------------------------------------------------------------------- *)
(* Extracting file info *)

let tmInfo = function
    | TmTrue fi -> fi
    | TmFalse fi -> fi
    | TmIf (fi,_,_,_) -> fi
    | TmZero fi -> fi
    | TmSucc (fi,_) -> fi
    | TmPred (fi,_) -> fi
    | TmIsZero (fi,_) -> fi


