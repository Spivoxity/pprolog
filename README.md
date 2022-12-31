# PicoProlog #

## The book ##
My book, ''An introduction to logic programming through Prolog'' was published by Prentice-Hall in 1996, but is long out of print.  The book gives a simple introduction to the theory of logic programming, and also describes in detail an implementation of a small Prolog dialect called picoProlog by an interpreter written in Pascal.

I have reclaimed the copyright, and I am delighted to make available here the full text of the book in PDF format.

* https://github.com/Spivoxity/pprolog/blob/master/logic.pdf

This repository also contains code for the interpreter, together with a translator from the Pascal subset used by the interpreter into C.  The interpreter source itself uses macros to overcome some of the drawbacks of Pascal for this kind of systems programming, and a simple macro processor &ndash; also written in Pascal &ndash; is provided also.  See below for instructions for compiling the software.

Text and software copyright &copy; 1996, 2002, 2010 J. M. Spivey.

Please note that I have **not** placed the copyright of this
work in the public domain. Nevertheless, I freely grant permission to
make copies of the whole work for any purpose except direct commercial
gain. I retain all other rights, including but not limited to the
right to make translations and derivative works, and the right to make
extracts and copies of parts of the work.  Fair quotation is permitted
according to usual scholarly conventions.

## Building PicoProlog ##
You can fetch the interpreter code by cloning the Git repository.
````
$ git clone https://github.com/Spivoxity/pprolog.git
````
On a Linux machine, building PicoProlog should be straightforward; a Makefile is provided.  Running 
````
$ make
````
you will see the following.  First, the Pascal-to-C translator is built, using Bison and Flex to generate the parser and lexer.
````
bison -d -o parse.c parse.y
gcc -g -O2   -c -o main.o main.c
gcc -g -O2   -c -o sem.o sem.c
gcc -g -O2   -c -o expr.o expr.c
gcc -g -O2   -c -o type.o type.c
gcc -g -O2   -c -o symtab.o symtab.c
gcc -g -O2   -c -o emit.o emit.c
gcc -g -O2   -c -o library.o library.c
gcc -g -O2   -c -o parse.o parse.c
flex -t scan.l >scan.c
gcc -g -O2   -c -o scan.o scan.c
gcc -g -O2 -o ptc main.o sem.o expr.o type.o symtab.o emit.o library.o parse.o scan.o
````
Now the translator is used on the source of the macro processor `ppp.p`, and the resulting C code is compiled.
````
./ptc ppp.p >ppp.c
gcc -g -O2 -o ppp ppp.c
````
Finally, the macro processor is used on the source code of the Prolog interpreter, the resulting Pascal code is translated to C, and the C code is compiled into a working interpreter.
````
(echo "define(ptc)"; cat pprolog.x) | ./ppp >pprolog.p
./ptc pprolog.p >pprolog.c
gcc -g -O2 -o pprolog pprolog.c
````

## Using the Free Pascal Compiler ##
Instead of using the supplied Pascal-to-C translator, it's possible to build picoProlog using the compiler from the [http://www.freepascal.com Free Pascal] project.  You will need the file @pplib.inc@ containing Free Pascal implementations of some system procedures.  On Linux, you can just say
````
$ make fp-pprolog
````
to perform these steps:
````
fpc -ofp-ppp ppp.p
Free Pascal Compiler version 3.0.0+dfsg-8 [2016/09/03] for x86_64
Copyright (c) 1993-2015 by Florian Klaempfl and others
Target OS: Linux for x86-64
Compiling ppp.p
Linking fp-ppp
394 lines compiled, 0.1 sec
(echo "define(fpc)"; cat pprolog.x) | ./fp-ppp >fp-pprolog.p
fpc -ofp-pprolog fp-pprolog.p
Free Pascal Compiler version 3.0.0+dfsg-8 [2016/09/03] for x86_64
Copyright (c) 1993-2015 by Florian Klaempfl and others
Target OS: Linux for x86-64
Compiling fp-pprolog.p
fp-pprolog.p(537,19) Note: Local variable "dummy" is assigned but never used
Linking fp-pprolog
2136 lines compiled, 0.1 sec
1 note(s) issued
````
The result is called `fp-pprolog` so that it can coexist with the standard version in the same Makefile, but it can be renamed if you like.

Note that with version 3.0.0 of Free Pascal, the spurious message
````
/usr/bin/ld.bfd: warning: link.res contains output sections; did you forget -T?
````
appears a couple of times; it can safely be ignored.

On other machines, it may be simpler to work manually.  First, edit the file `pprolog.x` and add the single line
````
define(fpc)
````
at the top.  This will activate conditional code in the rest of the source that adapts it to Free Pascal.  Then issue the following commands.
````
$ fpc -oppp ppp.p
$ ppp <pprolog.x >pprolog.p
$ fpc -opprolog pprolog.p
````
The resulting binary can be invoked as `pprolog`.

## About PTC ##
The Pascal-to-C translater PTC provided with PicoProlog implements only the subset of constructs that are used in PicoProlog.  Since that subset is more-or-less the intersection of Pascal and C, the job is not too difficult.
The following is a (no doubt incomplete) list of features of Pascal that aren't implemented:
* Nested procedures
* Procedures as parameters
* Array parameters passed by value
* Arrays indexed by other than integer ranges
* Sets
* Typed file I/O
* Width specifications for write (they're ignored)
* Reading other than characters
* Writing other than integers, characters or string constants
Some other Pascal features are implemented especially badly (in that errors in the Pascal source may result in a bad C program as the output):
* Check for assignment to a non-variable
* Check that labels are declared and placed exactly once
* Check bounds of constant string parameters
* Multiple declarations
* Type check for case labels
* Check forward procedures get defined
* Check that the real definition of a forward procedure has the same heading as the forward definition.
* The 'string' type is bogus: use array of char instead
* Var parameters
* For loop bounds
