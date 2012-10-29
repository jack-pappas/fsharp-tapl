﻿// TODO : Add copyright header

(* Module Main: The main program.  Deals with processing the command
   line, reading files, building and connecting lexers and parsers, etc.
   
   For most experiments with the implementation, it should not be
   necessary to change this file.
*)

module Main

open System
open Microsoft.FSharp.Text
open Microsoft.FSharp.Text.Lexing
open FSharpx.Compatibility.OCaml.Format
open Ast
open Lexer
open Parser
open Core

let searchpath = ref [ "" ]
  
let argDefs =
  [ ("-I", (Arg.String (fun f -> searchpath := f :: !searchpath)),
     "Append a directory to the search path") ]
  
let parseArgs () =
  let inFile = ref (None : string option)
  in
    (Arg.parse argDefs
       (fun s ->
          match !inFile with
          | Some _ -> err "You must specify exactly one input file"
          | None -> inFile := Some s)
       "";
     match !inFile with
     | None -> err "You must specify an input file"
     | Some s -> s)
  
let openfile infile =
  let rec trynext l =
    match l with
    | [] -> err ("Could not find " ^ infile)
    | d :: rest ->
        let name = if d = "" then infile else d ^ ("/" ^ infile)
        in (try open_in name with | Sys_error m -> trynext rest)
  in trynext !searchpath
  
let parseFile inFile =
  let pi = openfile inFile in
  let lexbuf = Lexer.create inFile pi in
  let result =
    try Parser.toplevel Lexer.main lexbuf
    with | Parsing.Parse_error -> error (Lexer.info lexbuf) "Parse error"
  in (Parsing.clear_parser (); close_in pi; result)
  
let alreadyImported = ref ([] : string list)
  
let rec process_command ctx cmd =
  match cmd with
  | Eval (fi, t) ->
      let t' = eval ctx t
      in (printtm_ATerm true ctx t'; force_newline (); ctx)
  | Bind (fi, x, bind) ->
      let bind' = evalbinding ctx bind
      in
        (pr x;
         pr " ";
         prbinding ctx bind';
         force_newline ();
         addbinding ctx x bind')
  
let process_file f ctx =
  (alreadyImported := f :: !alreadyImported;
   let (cmds, _) = parseFile f ctx in
   let g ctx c =
     (open_hvbox 0;
      let results = process_command ctx c in (print_flush (); results))
   in List.fold_left g ctx cmds)
  
let main () =
  let inFile = parseArgs () in let _ = process_file inFile emptycontext in ()
  
let () = set_max_boxes 1000
  
let () = set_margin 67
  
let res = Printexc.catch (fun () -> try (main (); 0) with | Exit x -> x) ()
  
let () = print_flush ()
  
let () = exit res
  

