(*
Copyright (c) 2003, Benjamin C. Pierce
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

[<AutoOpen>]
module Support.Pervasives

open FSharpx.Compatibility.OCaml


type info = Error.info

let pr = Format.print_string


