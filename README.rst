#####################################
Types and Programming Languages in F#
#####################################

Code and Examples from Benjamin Pierce's "`Types and Programming Languages`_".

.. _`Types and Programming Languages`: http://www.cis.upenn.edu/~bcpierce/tapl/


Overview
========

"`Types and Programming Languages`_" provides a comprehensive introduction to type systems and programming language theory. The code which accompanies the book is written in OCaml; this repository contains an F# port of that code.

**NOTE:** The ported F# code is not a fresh implementation -- it is the *original* OCaml code with some trivial modifications which allow it to compile with F#. The output of each of the F# projects has been verified to match the `output of the original OCaml programs`_.

.. _`Types and Programming Languages`: http://www.cis.upenn.edu/~bcpierce/tapl/
.. _`output of the original OCaml programs`: fsharp-tapl/blob/master/expected-output.rst

Prerequisites
=============

- F# compiler

  - Windows

    - Visual Studio 2010 or 2012

  - Mac OS X / FreeBSD / Linux

    - Mono 3.0 (or newer)
    - `fsharp 3.0`_
    - MonoDevelop 3.0 (or newer)

      - fsharpbinding_
  
- NuGet_ is used to manage external packages. The easiest way to `install NuGet`_ is by downloading it (for free) from the `Visual Studio Extension Gallery`_. If you do not have NuGet, or are running a version prior to 2.0, you *must* install it (or upgrade) before you will be able to build the projects.

  The solution uses the *Package Restore* feature of NuGet to automatically download any missing packages when the project is built. This requires that you have the `Allow NuGet to download missing packages during build`_ setting enabled; in Visual Studio, you can find the setting under ``Options -> Package Manager -> General``.

  Once NuGet is installed and configured, you should be able to build the solution.

- `F# PowerPack 2.0`_

  The F# PowerPack 2.0 is required (for now) because the projects use ``fslex`` and ``fsyacc``. **Mono:** The PowerPack should work on Mono, though I haven't tested it. I'm working on new versions of ``fslex`` and ``fsyacc`` now, and when complete I'll create install scripts to make them easy to use on Mac OS X / FreeBSD / Linux.

.. _`fsharp 3.0`: https://github.com/fsharp/fsharp
.. _fsharpbinding: https://github.com/fsharp/fsharpbinding
.. _NuGet: http://nuget.org
.. _`install NuGet`: http://visualstudiogallery.msdn.microsoft.com/27077b70-9dad-4c64-adcf-c7cf6bc9970c
.. _`Visual Studio Extension Gallery`: http://visualstudiogallery.msdn.microsoft.com/27077b70-9dad-4c64-adcf-c7cf6bc9970c
.. _`Allow NuGet to download missing packages during build`: http://docs.nuget.org/docs/workflows/using-nuget-without-committing-packages
.. _`F# PowerPack 2.0`: https://fsharppowerpack.codeplex.com/releases/view/45593

