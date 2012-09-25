// Learn more about F# at http://fsharp.net

module Support

//
[<AutoOpen>]
module Error =
    open System

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
        (*
        print_flush(); 
        open_vbox 0; 
        open_hvbox 0; f(); print_cut(); close_box(); print_newline();
        *)
        f ()
        Console.WriteLine ()
        raise (Exit 1)

    let printInfo = function
        (* In the text of the book, file positions in error messages are replaced
         with the string "Error:" *)
        | FI(f,l,c) ->
            printf "%s: %i.%i:" f l c
        | UNKNOWN ->
            printf "<Unknown file and line>: "

    let errfAt fi f =
        errf <| fun () ->
            printInfo fi
            printf " "
            f ()

    let err s =
        errf <| fun () ->
            printfn "Error: %s" s

    let error fi s =
        errfAt fi <| fun () ->
            printfn "%s" s

    let warning s =
        printfn "Warning: %s" s

    let warningAt fi s =
        printInfo fi
        printfn "Warning: %s" s


//
[<AutoOpen>]
module Pervasive =
    type info = Error.info


    let pr (s : string) =
        System.Console.WriteLine s




//
module internal Assembly =
    // Automatically opens the Support module whenever
    // this assembly is referenced.
    [<assembly : AutoOpen("Support")>]



    do ()
