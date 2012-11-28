(*
Copyright (c) 2003, Benjamin C. Pierce
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

[<AutoOpen>]
module Support.Error

open System
open FSharp.Compatibility.OCaml.Format

//
exception Exit of int

//
type info =
    | FI of string * int * int
    | UNKNOWN
    
//
type withinfo<'a> = {i : info; v : 'a}

let dummyinfo = UNKNOWN
let createInfo f l c = FI (f, l, c)

let errf f =
    print_flush ()
    open_vbox 0
    open_hvbox 0; f(); print_cut(); close_box(); print_newline();
    raise (Exit 1)

let printInfo = function
    (* In the text of the book, file positions in error messages are replaced
        with the string "Error:" *)
    | FI (f, l, c) ->
        print_string f;
        print_string ":";
        print_int l; print_string ".";
        print_int c; print_string ":"
    | UNKNOWN ->
        print_string "<Unknown file and line>: "

let errfAt fi f = errf(fun()-> printInfo fi; print_space(); f())

let err s = errf (fun()-> print_string "Error: "; print_string s; print_newline())

let error fi s = errfAt fi (fun()-> print_string s; print_newline())

let warning s =
  print_string "Warning: "; print_string s;
  print_newline()

let warningAt fi s =
  printInfo fi; print_string " Warning: ";
  print_string s; print_newline()
