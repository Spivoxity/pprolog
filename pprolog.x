{T pprolog.p -- picoProlog interpreter }

{ Copyright (C) J. M. Spivey 1992 }

{ This is the `picoProlog' interpreter described in the book `An
  Introduction to Logic Programming through Prolog' by Michael Spivey
  (Prentice Hall, 1995).  Copyright is retained by the author, but
  permission is granted to copy and modify the program for any purpose
  other than direct commercial gain.

  The text of this program must be processed by the `ppp'
  macro processor before it can be compiled. }

program &picoProlog(input, output);

ifdef(fpc,uses sysutils;)

ifdef(fpc,type integer = longint;)

{ tunable parameters }
const
  &MAXSYMBOLS = 511;  { max no. of symbols }
  &HASHFACTOR = 90;  { percent loading factor for hash table }
  &MAXCHARS = 2048;  { max chars in symbols }
  &MAXSTRING = 128;  { max string length }
  &MAXARITY = 63;  { max arity of function, vars in clause }
  &MEMSIZE = 1000000;  { size of |mem| array }
  &GCLOW = 10000;  { call GC when this much space left }
  &GCHIGH = 50000;  { GC must find this much space }

{ special character values }
define(&ENDSTR, chr(0))  { end of string }
define(&TAB, chr(9))  { tab character }
define(&ENDLINE, chr(10))  { newline character }
define(&ENDFILE, chr(127))  { end of file }

{S Coding conventions }

{ We ignore Pascal's stupid rule that all global variables must be
  declared together at the start of the program; likewise all global
  types and all global constants.  Many Pascal compilers relax the
  rule to make large programs easier to read and write; but if your
  Pascal compiler enforces it, you know what to do, and a text
  editor is the tool for the job. }

{ Most Pascal compilers implement a `default' part in case
  statements.  The macro |default| should be defined as the text that
  comes between the ordinary cases and the default part.  If the
  default part is like an ordinary case, but labelled with a keyword
  (say `others'), then the definition of |default| should include the
  semicolon that separates it from the preceding case, like this:
  `; others:'.  If your Pascal doesn't have default parts for case
  statements, most of them can be deleted, since they are only calls
  to |bad_tag| put there for robustness.  The only other one (in
  |Scan|) will need a little more work. }
define(&default, else)

{ Some Pascal implementations buffer terminal output, but provide a
  special procedure to flush the buffer; the |flush_out| macro
  should be defined to call whatever procedure is necessary.  A call
  to |flush_out| follows each prompt for input from the terminal, and
  the progress messages from the garbage collector. }
define(&flush_out)
ifdef(ptc,define(&flush_out,flush))

{ In Free Pascal, a function name acts as a variable throughout the function
  body, and that means that a recursive call to a paramaterless function
  must have empty parentheses if we are to avoid a horrendous bug. }
define(funcall)
ifdef(fpc,define(funcall,()))

{ Pascal's numeric labels make code that uses |goto| statements
  unnecessarily obscure, so we define a few macros that have
  meaningful names but expand to plain integers that can be used
  as labels. }
define(&end_of_pp, 999)
define(&found, 1)
define(&exit, 2)
define(&done, 3)
define(&found2, 4)

{ When something goes drastically wrong, picoProlog sometimes needs
  to stop immediately.  In standard Pascal, this is achieved by a
  non-local jump to the label |end_of_pp|, located at the end of the
  main program.  But some Pascal compilers don't allow non-local
  jumps; they often provide a |halt| procedure instead.  The macro
  |abort| should be defined to do whatever is needed. }
label &end_of_pp;
define(&abort, halt)

{ Here are a few convenient abbreviations: }
define(&incr, $1 := $1+1)  { increment a variable }
define(&decr, $1 := $1-1)  { decrement a variable }
define(&return, goto exit)  { return from procedure }
define(&skip)  { empty statement }

{S Error handling }

{ These macros print an error message, then either arrange for
  execution of a goal to abandoned (by clearing the |run| flag), or
  abandon the whole run of picoProlog.  They use the |$0| feature to
  allow for a list of arguments.

  Errors during execution of a goal are reported by |exec_error|; it
  sets the |run| flag to false, so the main execution mechanism will
  stop execution before starting on another resolution step. }

var &run: boolean;  { whether execution should continue }
  &dflag: boolean;  { switch for debugging code }

define(&exec_error,
  begin writeln; write('Error: ', $0); run := false end)
define(&panic, begin writeln; writeln('Panic: ', $0); abort end)
define(&bad_tag, panic('bad tag ', $2:1, ' in ', $1))

{S String buffer }

{ The strings that are the names of function symbols, variables,
  etc. are saved in the array |charbuf|: each string is
  represented elsewhere by an index |k| into this array, and the
  characters of the string are |charbuf[k]|,
  |charbuf[k+1]|,~\dots, terminated by the character |ENDSTR|.
  |charptr| is the last occupied location in |charbuf|.

  In addition to these `permanent' strings, there are `temporary'
  strings put together for some short-term purpose.  These are
  kept in arrays of size |MAXSTRING|, and are also terminated by
  |ENDSTR|. }

type
  &permstring = 1..MAXCHARS;
  &tempstring = array [1..MAXSTRING] of char;

var
  &charptr: 0..MAXCHARS;
  &charbuf: array [1..MAXCHARS] of char;

{ |StringLength| -- length of a tempstring }
function &StringLength(var s: tempstring): integer;
  var i: 0..MAXSTRING;
begin
  i := 0;
  while s[i+1] <> ENDSTR do incr(i);
  StringLength := i
end;

{ |SaveString| -- make a tempstring permanent }
function &SaveString(var s: tempstring): permstring;
  var i: 0..MAXSTRING;
begin
  if charptr + StringLength(s) + 1 > MAXCHARS then
    panic('out of string space');
  SaveString := charptr+1; i := 0;
  repeat
    incr(i); incr(charptr); charbuf[charptr] := s[i]
  until s[i] = ENDSTR
end;

{ |StringEqual| -- compare a tempstring to a permstring }
function &StringEqual(var &s1: tempstring; &s2: permstring): boolean;
  var i: integer;
begin
  i := 1;
  while (s1[i] <> ENDSTR) and (s1[i] = charbuf[s2+i-1]) do incr(i);
  StringEqual := (s1[i] = charbuf[s2+i-1])
end;

{ |WriteString| -- print a permstring }
procedure &WriteString(s: permstring);
  var i: 1..MAXCHARS;
begin
  i := s;
  while charbuf[i] <> ENDSTR do
    begin write(charbuf[i]); incr(i) end
end;

{S Representation of terms }

{ It is now time to give the details of how terms are
  represented.  Each `term' is an index into the |mem| array that
  points to a small block of contiguous words.  The first word
  indicates the number and layout of the words that follow. It packs
  together the size of the node, and an integer code that determines
  the kind of term: |FUNC| for a compound term, |INT| for an
  integer, and so on.  Macros |t_kind(t)| and |t_size(t)| extract
  these from the first word of a term |t|.  There is also a bit in
  the first word that is used by the garbage collector for marking.
  The second word of the node, |t_shift(t) = mem[t+1]| is also
  reserved for the garbage collector.

  The layout of the remaining elements of |mem| that make up the
  term depends on the |t_kind| field.  For a |FUNC| term, there is
  the function symbol |t_func(t)|, and a variable number of
  arguments, which may be referred to as |t_arg(t, 1)|, |t_arg(t, 2)|,
  \dots, |t_arg(t, n)| where |n| is the arity of |t_func(t)|.

  For an |INT| term, there is just the integer value |t_ival(t)|,
  and for a |CHRCTR| term there is the character value |t_cval(t)|,
  which is actually the code |ord(c)|.  |CELL| nodes represent
  variables and have a |t_val| field that points to the value. |REF|
  nodes are the numeric markers in program clauses that refer to a
  slot in the frame for a clause; the |t_index| field is the
  index of the slot. |UNDO| nodes do not represent terms at all,
  but items on the trail stack; they share some of the layout of
  terms, so that they can be treated the same by the garbage
  collector. }

type
  &pointer = integer;  { index into |mem| array }
define(&NULL, 0)  { null pointer }

type &term = pointer;
define(&t_tag, mem[$1])
  define(&t_kind, t_tag($1) div 256)  { one of |FUNC|, |INT|, \dots }
  define(&t_size, t_tag($1) mod 128)  { size in words }
  define(&marked, (t_tag($1) mod 256 >= 128))  { GC mark }
  define(&add_mark, t_tag($1) := t_tag($1) + 128)
  define(&rem_mark, t_tag($1) := t_tag($1) - 128)
  define(&make_tag, 256 * $1 + $2)
define(&t_shift, mem[$1+1])  { for use by gc }
define(&FUNC, 1)  { compound term }
  define(&t_func, mem[$1+2])  { \quad function symbol }
  define(&t_arg, mem[$1+$2+2])  { \quad arguments (start from 1) }
define(&INT, 2)  { integer }
  define(&t_ival, mem[$1+2])  { \quad integer value }
define(&CHRCTR, 3)  { character }
  define(&t_cval, mem[$1+2])  { \quad character value }
define(&CELL, 4)  { variable cell }
  define(&t_val, mem[$1+2])  { \quad value or |NULL| if unbound }
define(&REF, 5)  { variable reference }
  define(&t_index, mem[$1+2])  { \quad index in frame }
define(&UNDO, 6)  { trail item }
  { see later }
define(&TERM_SIZE, 3)  { \dots\ plus no. of args }

{S Memory allocation }

{ Storage for most things is allocated from the big array |mem|.
  This array is in three parts: the heap and local stack, which grow
  upwards from the bottom of |mem|, and the global stack, which
  grows downwards from the top of |mem|.

  The heap stores the clauses that make up the program and running
  goal; it grows only while clauses are being input and not during
  execution, so there is no need for free space between the heap and
  local stack.  Program clauses become a permanent part of the heap,
  but goal clauses (and clauses that contain errors) can be
  discarded; so there is an extra variable |hmark| that indicates
  the beginning of the present clause.

  The local stack holds activation records for clauses during
  execution of goals, and the global stack other longer-lived data
  structures.  Both stacks expand and contract during execution of
  goals.  Also, there is a garbage collector that can reclaim
  inaccessible portions of the global stack. }

var
  &lsp, &gsp, &hp, &hmark: pointer;
  &mem: array [1..MEMSIZE] of integer;

{ |LocAlloc| -- allocate space on local stack }
function &LocAlloc(&size: integer): pointer;
begin
  if lsp + size >= gsp then panic('out of stack space');
  LocAlloc := lsp + 1; lsp := lsp + size
end;

{ |GloAlloc| -- allocate space on global stack }
function &GloAlloc(&kind, &size: integer): pointer;
  var p: pointer;
begin
  if gsp - size <= lsp then
    panic('out of stack space');
  gsp := gsp - size; p := gsp;
  t_tag(p) := make_tag(kind, size);
  GloAlloc := p
end;

{ |HeapAlloc| -- allocate space on heap }
function &HeapAlloc(&size: integer): pointer;
begin
  if hp + size > MEMSIZE then panic('out of heap space');
  HeapAlloc := hp + 1; hp := hp + size
end;

define(&is_heap, ($1 <= hp))  { test if a pointer is in the heap }
define(&is_glob, ($1 >= gsp))  { test if it is in the global stack }

{S Character input }

{ Pascal's I/O facilities view text files as sequences of lines,
  but it is more convenient for picoProlog to deal with a uniform
  sequence of characters, with the end of a line indicated by an
  |ENDLINE| character, and the end of a file by an |ENDFILE|
  character.  The routines here perform the translation (probably
  reversing a translation done by the Pascal run-time library).
  They also allow a single character to be `pushed back' on the
  input, so that the scanner can avoid reading too far. }

var
  &interacting: boolean;  { whether input is from terminal }
  &pbchar: char;  { pushed-back char, else |ENDFILE| }
  &infile: text;  { the current input file }
  &lineno: integer;  { line number in current file }
  &filename: permstring;  { name of current file }

{ |FGetChar| -- get a character from a file }
function &FGetChar(var f: text): char;
  var &ch: char;
begin
  if eof(f) then
    FGetChar := ENDFILE
  else if eoln(f) then
    begin readln(f); incr(lineno); FGetChar := ENDLINE end
  else
    begin read(f, ch); FGetChar := ch end
end;

{ |GetChar| -- get a character }
function &GetChar: char;
begin
  if pbchar <> ENDFILE then
    begin GetChar := pbchar; pbchar := ENDFILE end
  else if interacting then
    GetChar := FGetChar(input)
  else
    GetChar := FGetChar(infile)
end;

{ |PushBack| -- push back a character on the input }
procedure &PushBack(&ch: char);
begin
  pbchar := ch
end;

{S Representation of clauses }

{ Clauses in the picoProlog program (and goals to be executed) have
  head and body literals in which the variables are replaced by |REF|
  nodes.  The clause itself is a segment of |mem| that has some
  fields at fixed offsets, followed by a variable-length sequence of
  pointers to the literals in the body of the clause, terminated by
  |NULL|.  Goal clauses have the same representation, but with |head
  = NULL|.  Macros |c_rhs| and |c_body| are defined so that
  |c_rhs(c)| is a pointer to the beginning of the sequence of
  pointers that makes up the clause body, and |c_body(c, i)| is the
  |i|'th literal in the body itself.

  Partially executed clause bodies are represented in the execution
  mechanism by the address of the pointer |p| to the first unsolved
  literal.  For cleanliness, we provide macros |g_first(p)| and
  |g_rest(p)| that respectively return the first literal itself, and
  a pointer that represents the remaining literals after the first
  one.  The test for the empty list is |g_first(p) = NULL|.

  The number of clauses tried against a goal literal is reduced by
  using associating each literal with a `key', calculated so that
  unifiable literals have matching keys. }

type &clause = pointer;
define(&c_nvars, mem[$1])  { no. of variables }
define(&c_key, mem[$1+1])  { unification key }
define(&c_next, mem[$1+2])  { next clause for same relation }
define(&c_head, mem[$1+3])  { clause head }
define(&c_rhs, ($1+4))  { clause body (ends with NULL) }
define(&c_body, mem[c_rhs($1)+$2-1])
define(&CLAUSE_SIZE, 4)  { ... plus size of body + 1 }

define(&g_first, mem[$1])  { first of a list of literals }
define(&g_rest, ($1)+1)  { rest of the list }

{S Stack frames and interpreter registers }

{ The local stack is organized as a sequence of frames, each
  corresponding to an active copy of a program clause.  Most fields
  in a frame are copies of the values of the interpreter's
  `registers' when it was created, so here also is the declaration
  of those global registers.  The |tp| register that points to the
  top of the trail stack is declared later.

  The last part of a frame is a variable-length array of cells,
  containing the actual variables for the clause being used in the
  frame. The variables are numbered from 1, and each cell is of
  length |TERM_SIZE|, so the |f_local| macro contains the right
  formula so that |f_local(f, i)| is a pointer to the |i|'th cell. }

type &frame = pointer;
define(&f_goal, mem[$1])  { the goal }
define(&f_parent, mem[$1+1])  { parent frame }
define(&f_retry, mem[$1+2])  { untried clauses }
define(&f_choice, mem[$1+3])  { previous choice-point }
define(&f_glotop, mem[$1+4])  { global stack at creation }
define(&f_trail, mem[$1+5])  { trail state at creation }
define(&f_nvars, mem[$1+6])  { no. of local variables }
define(&f_local, ($1+7+($2-1)*TERM_SIZE))
define(&FRAME_SIZE, 7)  { \dots plus space for local variables }

{ |frame_size| -- compute size of a frame with |n| variables }
define(&frame_size, (FRAME_SIZE + ($1)*TERM_SIZE))

var
  &current: pointer;  { current goal }
  &call: term;  { |Deref|'ed first literal of goal }
  &goalframe: frame;  { current stack frame }
  &choice: frame;  { last choice point }
  &base: frame;  { frame for original goal }
  &proc: clause;  { clauses left to try on current goal }

{ |Deref| is a function that resolves the indirection in the
  representation of terms.  It looks up references in the frame, and
  following the chain of pointers from variable cells to their
  values.  The result is an explicit representation of the argument
  term; if the frame is non-|NULL|, the result is never a |REF|
  node, and if it is a |CELL| node, the |t_val| field is empty. }

{ |Deref| -- follow |VAR| and |CELL| pointers }
function &Deref(t: term; e: frame): term;
begin
  if t = NULL then panic('Deref');
  if (t_kind(t) = REF) and (e <> NULL) then
    t := f_local(e, t_index(t));
  while (t_kind(t) = CELL) and (t_val(t) <> NULL) do
    t := t_val(t);
  Deref := t
end;

{ This is a good place to put the forward declarations of a few
  procedures and functions. }
procedure PrintTerm(t: term; e: frame; prio: integer); forward;
function ParseTerm: term; forward;
function DoBuiltin(action: integer): boolean; forward;
procedure Collect; forward;
function Key(t: term; e: frame): integer; forward;

{ In the actual definition of a procedure or function that
  has been declared forward, we repeat the parameter list
  in a call to the macro |\it f w d|.  Standard Pascal requires this
  to be replaced by the empty string, but some implementations
  allow the parameter list to be repeated and check that the
  two lists agree. }
define(&fwd)
ifdef(fpc,define(&fwd,$1))


{S Symbol table }

{ The names of relations, functions, constants and variables are
  held in a hash table.  It is organized as a `closed' hash table
  with sequential search: this is simple but leaves much room for
  improvement. The symbol table is not allowed to become more full
  than |HASHFACTOR| per cent, since nearly full hash tables of this kind
  perform rather badly.

  Each symbol has an |s_action| code that has a different non-zero
  value for each built-in relation, and is zero for everything
  else. User-defined relations have a chain of clauses that starts
  at the |s_proc| field and is linked together by the |c_next| fields
  of the clauses. }

type &symbol = 1..MAXSYMBOLS;  { index in |symtab| }

var
  &nsymbols: 0..MAXSYMBOLS;  { number of symbols }
  &symtab: array [1..MAXSYMBOLS] of record
      &name: integer;  { print name: index in |charbuf| }
      &arity: integer;  { number of arguments or -1 }
      &action: integer;  { code if built-in, 0 otherwise }
      &proc: clause  { clause chain }
    end;
  &cons, &eqsym, &cutsym, &nilsym, &notsym: symbol;

{ We define selector macros for symbols, just as for terms }
define(&s_name, symtab[$1].name)
define(&s_arity, symtab[$1].arity)
define(&s_action, symtab[$1].action)
define(&s_proc, symtab[$1].proc)

{ |Lookup| -- convert string to internal symbol }
function &Lookup(var &name: tempstring): symbol;
  label &found;
  var h, i: integer; p: symbol;
begin
  { Compute the hash function in |h| }
  h := 0; i := 1;
  while name[i] <> ENDSTR do
    begin h := (5 * h + ord(name[i])) mod MAXSYMBOLS; incr(i) end;

  { Search the hash table }
  p := h+1;
  while s_name(p) <> -1 do begin
    if StringEqual(name, s_name(p)) then goto found;
    if p = 1 then p := MAXSYMBOLS else decr(p)
  end;

  { Not found: enter a new symbol }
  { Be careful to avoid overflow on 16 bit machines: }
  if nsymbols >= (MAXSYMBOLS div 10) * (HASHFACTOR div 10) then
    panic('out of symbol space');
  incr(nsymbols);
  s_name(p) := SaveString(name);
  s_arity(p) := -1;
  s_action(p) := 0; s_proc(p) := NULL;

found:
  Lookup := p
end;

type &keyword = array [1..8] of char;

{ |Enter| -- define a built-in symbol }
function &Enter(&name: keyword; &arity: integer; &action: integer): symbol;
  var s: symbol; i: integer; &temp: tempstring;
begin
  i := 1;
  while name[i] <> ' ' do
    begin temp[i] := name[i]; incr(i) end;
  temp[i] := ENDSTR; s := Lookup(temp);
  s_arity(s) := arity; s_action(s) := action;
  Enter := s
end;

{ Codes for built-in relations }
define(&CUT, 1)  { $!/0$ }
define(&CALL, 2)  { |call/1| }
define(&PLUS, 3)  { |plus/3| }
define(&TIMES, 4)  { |times/3| }
define(&ISINT, 5)  { |integer/1| }
define(&ISCHAR, 6)  { |char/1| }
define(&NAFF, 7)  { |not/1| }
define(&EQUALITY, 8)  { |=/2| }
define(&FAIL, 9)  { |false/0| }
define(&PRINT, 10)  { |print/1| }
define(&NL, 11)  { |nl/0| }

{ |InitSymbols| -- initialize and define standard symbols }
procedure &InitSymbols;
  var i: integer; &dummy: symbol;
begin
  nsymbols := 0;
  for i := 1 to MAXSYMBOLS do s_name(i) := -1;
  cons   := Enter(':       ', 2, 0);
  cutsym := Enter('!       ', 0, CUT);
  eqsym  := Enter('=       ', 2, EQUALITY);
  nilsym := Enter('nil     ', 0, 0);
  notsym := Enter('not     ', 1, NAFF);
  dummy  := Enter('call    ', 1, CALL);
  dummy  := Enter('plus    ', 3, PLUS);
  dummy  := Enter('times   ', 3, TIMES);
  dummy  := Enter('integer ', 1, ISINT);
  dummy  := Enter('char    ', 1, ISCHAR);
  dummy  := Enter('false   ', 0, FAIL);
  dummy  := Enter('print   ', 1, PRINT);
  dummy  := Enter('nl      ', 0, NL)
end;

{ |AddClause| -- insert a clause at the end of its chain }
procedure &AddClause(c: clause);
  var s: symbol; p: clause;
begin
  s := t_func(c_head(c));
  if s_action(s) <> 0 then begin
    exec_error('can''t add clauses to built-in relation ');
    WriteString(s_name(s))
  end
  else if s_proc(s) = NULL then
    s_proc(s) := c
  else begin
    p := s_proc(s);
    while c_next(p) <> NULL do p := c_next(p);
    c_next(p) := c
  end
end;

{S Building terms on the heap }

{ Next, some convenient routines that construct various kinds of
  term in the heap area: they are used by the parsing routines to
  construct the internal representation of the input terms they
  read.  The routine |MakeRef| that is supposed to construct a |REF|
  node in fact returns a pointer to one from a fixed collection.
  This saves space, since all clauses can share the same small
  number of |REF| nodes. }

type &argbuf = array [1..MAXARITY] of term;

{ |MakeCompound| -- construct a compound term on the heap }
function &MakeCompound(&fun: symbol; var &arg: argbuf): term;
  var p: term; i, n: integer;
begin
  n := s_arity(fun);
  p := HeapAlloc(TERM_SIZE+n);
  t_tag(p) := make_tag(FUNC, TERM_SIZE+n);
  t_func(p) := fun;
  for i := 1 to n do t_arg(p, i) := arg[i];
  MakeCompound := p
end;

{ |MakeNode| -- construct a compound term with up to 2 arguments }
function &MakeNode(&fun: symbol; &a1, &a2: term): term;
  var &arg: argbuf;
begin
  arg[1] := a1; arg[2] := a2;
  MakeNode := MakeCompound(fun, arg)
end;

var &refnode: array [1..MAXARITY] of term;

{ |MakeRef| -- return a reference cell prepared earlier }
function &MakeRef(&offset: integer): term;
begin
  MakeRef := refnode[offset]
end;

{ |MakeInt| -- construct an integer node on the heap }
function &MakeInt(i: integer): term;
  var p: term;
begin
  p := HeapAlloc(TERM_SIZE);
  t_tag(p) := make_tag(INT, TERM_SIZE);
  t_ival(p) := i; MakeInt := p
end;

{ |MakeChar| -- construct a character node on the heap }
function &MakeChar(c: char): term;
  var p: term;
begin
  p := HeapAlloc(TERM_SIZE);
  t_tag(p) := make_tag(CHRCTR, TERM_SIZE);
  t_cval(p) := ord(c); MakeChar := p
end;

{ |MakeString| -- construct a string as a Prolog list of chars }
function &MakeString(var s: tempstring): term;
  var p: term; i: integer;
begin
  i := StringLength(s);
  p := MakeNode(nilsym, NULL, NULL);
  while i > 0 do
    begin p := MakeNode(cons, MakeChar(s[i]), p); decr(i) end;
  MakeString := p
end;

{ |MakeClause| -- construct a clause on the heap }
function &MakeClause(&nvars: integer; &head: term;
		    var &body: argbuf; &nbody: integer): clause;
  var p: clause; i: integer;
begin
  p := HeapAlloc(CLAUSE_SIZE + nbody + 1);
  c_nvars(p) := nvars; c_next(p) := NULL; c_head(p) := head;
  for i := 1 to nbody do c_body(p, i) := body[i];
  c_body(p, nbody+1) := NULL;
  if head = NULL then c_key(p) := 0
  else c_key(p) := Key(head, NULL);
  MakeClause := p
end;

{S Printing terms }

{ These routines print terms on the user's terminal.  The main
  routine is |PrintTerm|, which prints a term by recursively
  traversing it.  Unbound cells are printed in the form |'L123'|
  (for local cells) or |'G234'| (for global cells): the number is
  computed from the address of the cell.  If the frame is
  |NULL|, reference nodes are printed in the form |'@3'|. }

{ operator priorities }
define(&MAXPRIO, 2)  { isolated term }
define(&ARGPRIO, 2)  { function arguments }
define(&EQPRIO, 2)  { equals sign }
define(&CONSPRIO, 1)  { colon }

{ |IsString| -- check if a list represents a string }
function &IsString(t: term; e: frame): boolean;
  label &done;
  const &limit = 128;
  var i: integer;
begin
  i := 0; t := Deref(t, e);
  while i < limit do begin
    if (t_kind(t) <> FUNC) or (t_func(t) <> cons) then
      goto done
    else if t_kind(Deref(t_arg(t, 1), e)) <> CHRCTR then
      goto done
    else
      begin incr(i); t := Deref(t_arg(t, 2), e) end
  end;
done:
  IsString := (t_kind(t) = FUNC) and (t_func(t) = nilsym)
end;

{ |ShowString| -- print a list as a string }
procedure &ShowString(t: term; e: frame);
begin
  t := Deref(t, e);
  write('"');
  while t_func(t) <> nilsym do begin
    write(chr(t_cval(Deref(t_arg(t, 1), e))));
    t := Deref(t_arg(t, 2), e)
  end;
  write('"')
end;

{ |PrintCompound| -- print a compound term }
procedure &PrintCompound(t: term; e: frame; &prio: integer);
  var f: symbol; i: integer;
begin
  f := t_func(t);
  if f = cons then begin
    { |t| is a list: try printing as a string, or use infix : }
    if IsString(t, e) then
      ShowString(t, e)
    else begin
      if prio < CONSPRIO then write('(');
      PrintTerm(t_arg(t, 1), e, CONSPRIO-1);
      write(':');
      PrintTerm(t_arg(t, 2), e, CONSPRIO);
      if prio < CONSPRIO then write(')')
    end
  end
  else if f = eqsym then begin
    { |t| is an equation: use infix = }
    if prio < EQPRIO then write('(');
    PrintTerm(t_arg(t, 1), e, EQPRIO-1);
    write(' = ');
    PrintTerm(t_arg(t, 2), e, EQPRIO-1);
    if prio < EQPRIO then write(')')
  end
  else if f = notsym then begin
    { |t| is a literal 'not P' }
    write('not ');
    PrintTerm(t_arg(t, 1), e, MAXPRIO)
  end
  else begin
    { use ordinary notation }
    WriteString(s_name(f));
    if s_arity(f) > 0 then begin
      write('(');
      PrintTerm(t_arg(t, 1), e, ARGPRIO);
      for i := 2 to s_arity(f) do begin
        write(', ');
        PrintTerm(t_arg(t, i), e, ARGPRIO)
      end;
      write(')')
    end
  end
end;

{ |PrintTerm| -- print a term }
procedure &PrintTerm fwd((t: term; e: frame; &prio: integer));
begin
  t := Deref(t, e);
  if t = NULL then
    write('*null-term*')
  else begin
    case t_kind(t) of
    FUNC:
      PrintCompound(t, e, prio);
    INT:
      write(t_ival(t):1);
    CHRCTR:
      write('''', chr(t_cval(t)), '''');
    CELL:
      if is_glob(t) then
        write('G', (MEMSIZE - t) div TERM_SIZE:1)
      else
        write('L', (t - hp) div TERM_SIZE:1);
    REF:
      write('@', t_index(t))
    default
      write('*unknown-term(tag=', t_kind(t):1, ')*')
    end
  end
end;

{ |PrintClause| -- print a clause }
procedure &PrintClause(c: clause);
  var i: integer;
begin
  if c = NULL then
    writeln('*null-clause*')
  else begin
    if c_head(c) <> NULL then begin
      PrintTerm(c_head(c), NULL, MAXPRIO);
      write(' ')
    end;
    write(':- ');
    if c_body(c, 1) <> NULL then begin
      PrintTerm(c_body(c, 1), NULL, MAXPRIO);
      i := 2;
      while c_body(c, i) <> NULL do begin
	write(', ');
	PrintTerm(c_body(c, i), NULL, MAXPRIO);
	incr(i)
      end
    end;
    writeln('.')
  end
end;

{S Scanner }

{ The |Scan| procedure that reads the next token of a
  clause or goal from the input, together with some procedures that
  implement a crude form of recovery from syntax errors.

  |Scan| puts an integer code into the global variable |token|; if
  the token is an identifier, a number, or a string, there is another
  global variable that contains its actual value.

  The recovery mechanism skips input text until it finds a full stop
  or (if the input was from the terminal) the end of a line.  It
  then sets |token| to |DOT|, the code for a full stop.  The parser
  routines are designed so that they will never read past a full
  stop, and final recovery from the error is achieved when control
  reaches |ReadClause| again. }

var
  &token: integer;  { last token from input }
  &tokval: symbol;  { if |token = IDENT|, the identifier}
  &tokival: integer;  { if |token = NUMBER|, the number }
  &toksval: tempstring;  { if |token = STRCON|, the string }
  &errflag: boolean;  { whether recovering from an error }
  &errcount: integer;  { number of errors found so far }

{ Possible values for |token|: }
define(&IDENT, 1)  { identifier: see |tokval| }
define(&VARIABLE, 2)  { variable: see |tokval| }
define(&NUMBER, 3)  { number: see |tokival| }
define(&CHCON, 4)  { char constant: see |tokival| }
define(&STRCON, 5)  { string constant: see |toksval| }
define(&ARROW, 6)  { |':-'| }
define(&LPAR, 7)  { |'('| }
define(&RPAR, 8)  { |')'| }
define(&COMMA, 9)  { |','| }
define(&DOT, 10)  { |'.'| }
define(&COLON, 11)  { |':'| }
define(&EQUAL, 12)  { |'='| }
define(&NEGATE, 13)  { |'not'| }
define(&EOFTOK, 14)  { end of file }

{ |syntax_error| -- report a syntax error }
define(&syntax_error,
  begin if not errflag then
    begin ShowError; writeln($0); Recover end end)

{ |ShowError| -- report error location }
procedure &ShowError;
begin
  errflag := true; incr(errcount);
  if not interacting then begin
    write('"'); WriteString(filename);
    write('", line ', lineno:1, ' ')
  end;
  write('Syntax error - ')
end;

{ |Recover| -- discard rest of input clause }
procedure &Recover;
  var &ch: char;
begin
  if not interacting and (errcount >= 20) then
    begin writeln('Too many errors: I''m giving up'); abort end;
  if token <> DOT then begin
    repeat
      ch := GetChar
    until (ch = '.') or (ch = ENDFILE)
	or (interacting and (ch = ENDLINE));
    token := DOT
  end
end;

define(&is_upper, ((($1 >= 'A') and ($1 <= 'Z')) or ($1 = '_')))
define(&is_letter, (is_upper($1) 
  or (($1 >= 'a') and ($1 <= 'z'))))
define(&is_digit, (($1 >= '0') and ($1 <= '9')))

{ |Scan| -- read one symbol from |infile| into |token|. }
procedure &Scan;
  var &ch, &ch2: char; i: integer;
begin
  ch := GetChar; token := 0;
  while token = 0 do begin
    { Loop after white-space or comment }
    if ch = ENDFILE then
      token := EOFTOK
    else if (ch = ' ') or (ch = TAB) or (ch = ENDLINE) then
      ch := GetChar
    else if is_letter(ch) then begin
      if is_upper(ch) then token := VARIABLE
      else token := IDENT;
      i := 1;
      while is_letter(ch) or is_digit(ch) do begin
        if i > MAXSTRING then
          panic('identifier too long');
        toksval[i] := ch; ch := GetChar; incr(i)
      end;
      PushBack(ch);
      toksval[i] := ENDSTR; tokval := Lookup(toksval);
      if tokval = notsym then token := NEGATE
    end
    else if is_digit(ch) then begin
      token := NUMBER; tokival := 0;
      while is_digit(ch) do begin
        tokival := 10 * tokival + (ord(ch) - ord('0'));
        ch := GetChar
      end;
      PushBack(ch)
    end
    else begin
      case ch of
      '(': token := LPAR;
      ')': token := RPAR;
      ',': token := COMMA;
      '.': token := DOT;
      '=': token := EQUAL;
      '!': begin token := IDENT; tokval := cutsym end;
      '/':
	begin
	  ch := GetChar;
	  if ch <> '*' then
	    syntax_error('bad token "/"')
	  else begin
	    ch2 := ' '; ch := GetChar;
	    while (ch <> ENDFILE) and not ((ch2 = '*') and (ch = '/')) do
	      begin ch2 := ch; ch := GetChar end;
	    if ch = ENDFILE then
	      syntax_error('end of file in comment')
	    else
	      ch := GetChar
	  end
	end;
      ':':
        begin
	  ch := GetChar;
	  if ch = '-' then
	    token := ARROW
	  else
	    begin PushBack(ch); token := COLON end
        end;
      '''':
	begin
	  token := CHCON; tokival := ord(GetChar); ch := GetChar;
	  if ch <> '''' then
            syntax_error('missing quote')
	end;
      '"':
	begin
	  token := STRCON; i := 1; ch := GetChar;
	  while (ch <> '"') and (ch <> ENDLINE) do
	    begin toksval[i] := ch; ch := GetChar; incr(i) end;
	  toksval[i] := ENDSTR;
	  if ch = ENDLINE then begin
	    syntax_error('unterminated string');
	    PushBack(ch)
	  end
	end
      default
	syntax_error('illegal character "', ch, '"')
      end
    end
  end
end;

{ |PrintToken| -- print a token as a string }
procedure &PrintToken(t: integer);
begin
  case t of
  IDENT:
    begin write('identifier '); WriteString(s_name(tokval)); end;
  VARIABLE:
    begin write('variable '); WriteString(s_name(tokval)); end;
  NUMBER: write('number');
  CHCON:  write('char constant');
  ARROW:  write('":-"');
  LPAR:   write('"("');
  RPAR:   write('")"');
  COMMA:  write('","');
  DOT:    write('"."');
  COLON:  write('":"');
  EQUAL:  write('"="');
  STRCON: write('string constant')
  default
    write('unknown token')
  end
end;

{S Variable names }

{ As the parser reads an input clause, the routines here maintain a
  table of variable names and the corresponding run-time offsets in
  a frame for the clause: for each |i|, the name of the variable at
  offset |i| is |vartable[i]|.  Each clause contains only a few
  variables, so linear search is good enough.

  If the input clause turns out to be a goal, the table is saved and
  used again to display the answer when execution succeeds. }

var
  &nvars: 0..MAXARITY;  { no. of variables so far }
  &vartable: array [1..MAXARITY] of symbol;  { names of the variables }

{ |VarRep| -- look up a variable name }
function &VarRep(&name: symbol): term;
  var i: integer;
begin
  if nvars = MAXARITY then panic('too many variables');
  i := 1; vartable[nvars+1] := name;  { sentinel }
  while name <> vartable[i] do incr(i);
  if i = nvars+1 then incr(nvars);
  VarRep := MakeRef(i)
end;

{ |ShowAnswer| -- display answer and get response }
function &ShowAnswer(&bindings: frame): boolean;
  var i: integer; &ch: char;
begin
  if nvars = 0 then ShowAnswer := true
  else begin
    for i := 1 to nvars do begin
      writeln;
      WriteString(s_name(vartable[i])); write(' = ');
      PrintTerm(f_local(bindings, i), NULL, EQPRIO-1)
    end;
    if not interacting then
      begin writeln; ShowAnswer := false end
    else begin
      write(' ? '); flush_out;
      if eoln then
	begin readln; ShowAnswer := false end
      else
	begin readln(ch); ShowAnswer := (ch = '.') end
    end
  end
end;

{S Parser }

{ Here are the routines that parse input clauses.  They use the
  method of recursive descent, with each class of phrase recognized
  by a single function that consumes the tokens of the phrase and
  returns its value.  Each of these functions follows the convention
  that the first token of its phrase is in the global |token|
  variable when the function is called, and the first token after
  the phrase is in |token| on return.  The value of the function is
  the internal data structure for the term; this is built directly
  in the heap, with variables replaced by |REF| nodes.  Syntax
  errors are handled by skipping to the next full stop, then trying
  again to find a clause. }

{ |Eat| -- check for an expected token and discard it }
procedure &Eat(&expected: integer);
begin
  if token = expected then
    begin if token <> DOT then Scan end
  else if not errflag then begin
    ShowError;
    write('expected '); PrintToken(expected);
    write(', found '); PrintToken(token); writeln;
    Recover
  end
end;

{ |ParseCompound| -- parse a compound term }
function &ParseCompound: term;
  var &fun: symbol; &arg: argbuf; n: integer;
begin
  fun := tokval; n := 0; Eat(IDENT);
  if token = LPAR then begin
    Eat(LPAR); n := 1; arg[1] := ParseTerm;
    while token = COMMA do
      begin Eat(COMMA); incr(n); arg[n] := ParseTerm end;
    Eat(RPAR)
  end;
  if s_arity(fun) = -1 then
    s_arity(fun) := n
  else if s_arity(fun) <> n then
    syntax_error('wrong number of args');
  ParseCompound := MakeCompound(fun, arg)
end;

{ |ParsePrimary| -- parse a primary }
function &ParsePrimary: term;
  var t: term;
begin
  if token = IDENT then t := ParseCompound
  else if token = VARIABLE then
    begin t := VarRep(tokval); Eat(VARIABLE) end
  else if token = NUMBER then
    begin t := MakeInt(tokival); Eat(NUMBER) end
  else if token = CHCON then
    begin t := MakeChar(chr(tokival)); Eat(CHCON) end
  else if token = STRCON then
    begin t := MakeString(toksval); Eat(STRCON) end
  else if token = LPAR then
    begin Eat(LPAR); t := ParseTerm; Eat(RPAR) end
  else begin
    syntax_error('expected a term'); t := NULL
  end;
  ParsePrimary := t
end;

{ |ParseFactor| -- parse a factor }
function &ParseFactor: term;
  var t: term;
begin
  t := ParsePrimary;
  if token <> COLON then
    ParseFactor := t
  else begin
    Eat(COLON);
    ParseFactor := MakeNode(cons, t, ParseFactor funcall)
  end
end;

{ |ParseTerm| -- parse a term }
function &ParseTerm fwd(: term);
  var t: term;
 begin
  t := ParseFactor;
  if token <> EQUAL then
    ParseTerm := t
  else begin
    Eat(EQUAL);
    ParseTerm := MakeNode(eqsym, t, ParseFactor)
  end
end;

{ |CheckAtom| -- check that a literal is a compound term }
procedure &CheckAtom(a: term);
begin
  if t_kind(a) <> FUNC then
    syntax_error('literal must be a compound term')
end;

{ |ParseClause| -- parse a clause }
function &ParseClause(&isgoal: boolean): clause;
  label &done;
  var &head, t: term; 
    &body: argbuf; 
    n: integer;
    &minus: boolean;
begin
  if isgoal then 
    head := NULL
  else begin
    head := ParseTerm; 
    CheckAtom(head);
    Eat(ARROW)
  end;

  n := 0;
  if token <> DOT then begin
    while true do begin
      n := n+1; minus := false;
      if token = NEGATE then
	begin Eat(NEGATE); minus := true end;
      t := ParseTerm; CheckAtom(t);
      if minus then body[n] := MakeNode(notsym, t, NULL)
      else body[n] := t;
      if token <> COMMA then goto done;
      Eat(COMMA)
    end
  end;
done:
  Eat(DOT);

  if errflag then ParseClause := NULL
  else ParseClause := MakeClause(nvars, head, body, n)
end;

{ |ReadClause| -- read a clause from |infile| }
function &ReadClause: clause;
  var c: clause;
begin
  repeat
    hp := hmark; nvars := 0; errflag := false;
    if interacting then
      begin writeln; write('# :- '); flush_out end;
    Scan;
    if token = EOFTOK then c := NULL
    else c := ParseClause(interacting)
  until (not errflag) or (token = EOFTOK);
  ReadClause := c
end;

{S Trail }

{ The trail stack records assignments made to variables, so that
  they can be undone on backtracking.  It is a linked list of nodes
  with a |t_kind| of |UNDO| allocated from the global stack.  The
  variables for which bindings are actually kept in the trail are the
  `critical' ones that will not be destroyed on backtracking. }

type &trail = pointer;
{ Nodes on the trail share the |t_tag| and |t_shift| fields of
  other nodes on the global stack, plus: }
define(&x_reset, mem[$1+2])  { variable to reset }
define(&x_next, mem[$1+3])  { next trail entry }
define(&TRAIL_SIZE, 4)

var &trhead: trail;  { start of the trail }

{ |critical| -- test if a variable will survive backtracking }
define(&critical, (($1 < choice) or ($1 >= f_glotop(choice))))

{ |Save| -- add a variable to the trail if it is critical }
procedure &Save(v: term);
  var p: trail;
begin
  if critical(v) then begin
    p := GloAlloc(UNDO, TRAIL_SIZE);
    x_reset(p) := v; x_next(p) := trhead; trhead := p
  end
end;

{ |Restore| -- undo bindings back to previous state }
procedure &Restore;
  var v: term;
begin
  while (trhead <> f_trail(choice)) do begin
    v := x_reset(trhead);
    if v <> NULL then t_val(v) := NULL;
    trhead := x_next(trhead)
  end
end;

{ |Commit| -- blank out trail entries not needed after cut }
procedure &Commit;
  var p: trail;
begin
  p := trhead;
  if choice = NULL then exec_error('Commit');
  while (p <> NULL) and (p < f_glotop(choice)) do begin
    if (x_reset(p) <> NULL) and not critical(x_reset(p)) then
      x_reset(p) := NULL;
    p := x_next(p)
  end
end;

{S Unification }

{ The unification algorithm is the naive one that is traditional in
  Prolog implementations.  Tradition is also followed in omitting
  the `occur check'.

  Nodes of type |CELL| may only point to terms that are independent
  of any frame: i.e., they may not point to terms in the heap
  that may contain |REF| nodes.  So there is a function |GloCopy|
  that copies out enough of a term onto the global stack so that any
  cell can point to it.  No copy is needed if the term is already on
  the global stack, or if it is a simple term that cannot contain
  any |REF|'s. }

{ |GloCopy| -- copy a term onto the global stack }
function &GloCopy(t: term; e: frame): term;
  var &tt: term; i, n: integer;
begin
  t := Deref(t, e);
  if is_glob(t) then
    GloCopy := t
  else begin
    case t_kind(t) of
    FUNC:
      begin
	n := s_arity(t_func(t));
	if is_heap(t) and (n = 0) then GloCopy := t
	else begin
	  tt := GloAlloc(FUNC, TERM_SIZE+n);
	  t_func(tt) := t_func(t);
	  for i := 1 to n do
	    t_arg(tt, i) := GloCopy(t_arg(t, i), e);
	  GloCopy := tt
	end
      end;
    CELL:
      begin
        tt := GloAlloc(CELL, TERM_SIZE);
        t_val(tt) := NULL;
	Save(t); t_val(t) := tt;
        GloCopy := tt
      end;
    INT, CHRCTR:
      GloCopy := t
    default
      bad_tag('GloCopy', t_kind(t))
    end
  end
end;

{ When two variables are made to `share', there is a choice of which
  variable is made to point to the other.  The code takes care to
  obey some rules about what may point to what: (1) Nothing on the
  global stack may point to anything on the local stack; (2) Nothing
  on the local stack may point to anything nearer the top of the
  local stack.  Both these rules are necessary, since the top part
  of the local stack may be reclaimed without warning.  There is
  another rule that makes for better performance: (3) Avoid pointers
  from items nearer the bottom of the global stack to items nearer
  the top.

  The tricky |lifetime| macro implements these rules by
  computing a numerical measure of the lifetime of an object,
  defined so that anything on the local stack is shorter-lived than
  anything on the global stack, and within each stack items near the
  top are shorter-lived than items near the bottom. }

{ |lifetime| -- measure of potential lifetime }
define(&lifetime, ($1 * (2 * ord(is_glob($1)) - 1)))

{ |Share| -- bind two variables together }
procedure &Share(&v1, &v2: term);
begin
  if lifetime(v1) <= lifetime(v2) then
    begin Save(v1); t_val(v1) := v2 end
  else
    begin Save(v2); t_val(v2) := v1 end
end;

{ |Unify| -- find and apply unifier for two terms }
function &Unify(&t1: term; &e1: frame; &t2: term; &e2: frame): boolean;
  var i: integer; &match: boolean;
begin
  t1 := Deref(t1, e1); t2 := Deref(t2, e2);
  if t1 = t2 then  { Includes unifying a var with itself }
    Unify := true
  else if (t_kind(t1) = CELL) and (t_kind(t2) = CELL) then
    begin Share(t1, t2); Unify := true end
  else if t_kind(t1) = CELL then
    begin Save(t1); t_val(t1) := GloCopy(t2, e2); Unify := true end
  else if t_kind(t2) = CELL then
    begin Save(t2); t_val(t2) := GloCopy(t1, e1); Unify := true end
  else if t_kind(t1) <> t_kind(t2) then
    Unify := false
  else begin
    case t_kind(t1) of
    FUNC:
      if (t_func(t1) <> t_func(t2)) then
        Unify := false
      else begin
        i := 1; match := true;
        while match and (i <= s_arity(t_func(t1))) do begin
          match := Unify(t_arg(t1, i), e1, t_arg(t2, i), e2);
          incr(i)
        end;
        Unify := match
      end;
    INT:
      Unify := (t_ival(t1) = t_ival(t2));
    CHRCTR:
      Unify := (t_cval(t1) = t_cval(t2))
    default
      bad_tag('Unify', t_kind(t1))
    end
  end
end;

{ |Key| -- unification key of a term }
function &Key fwd((t: term; e: frame): integer);
  var &t0: term;
begin
  { The argument |t| must be a direct pointer to a compound term.
    The value returned is |key(t)|: if |t1| and |t2| are unifiable,
    then |key(t1) = 0| or |key(t2) = 0| or |key(t1) = key(t2)|. }

  if t = NULL then panic('Key');
  if t_kind(t) <> FUNC then bad_tag('Key1', t_kind(t));

  if s_arity(t_func(t)) = 0 then
    Key := 0
  else begin
    t0 := Deref(t_arg(t, 1), e);
    case t_kind(t0) of
      FUNC:      Key := t_func(t0);
      INT:       Key := t_ival(t0) + 1;
      CHRCTR:    Key := t_cval(t0) + 1;
      REF, CELL: Key := 0
    default
      bad_tag('Key2', t_kind(t0))
    end
  end
end;

{ |Search| -- find the first clause that might match }
function &Search(t: term; e: frame; p: clause): clause;
  var k: integer;
begin
  k := Key(t, e);
  if k <> 0 then
    while (p <> NULL) and (c_key(p) <> 0) and (c_key(p) <> k) do
      p := c_next(p);
  Search := p
end;

{S Interpreter }

{ The main control of the interpreter uses a depth-first search
  procedure with an explicit stack of activation records.  It
  includes the tail-recursion optimization and an indexing scheme
  that uses the hash codes computed by |Key|. }

var &ok: boolean;  { whether execution succeeded }

define(&debug_point, if dflag then begin write($1, ': ');
    PrintTerm($2, $3, MAXPRIO); writeln end)

{ |PushFrame| -- create a new local stack frame }
procedure &PushFrame(&nvars: integer; &retry: clause);
  var f: frame; i: integer;
begin
  f := LocAlloc(frame_size(nvars));
  f_goal(f) := current; f_parent(f) := goalframe;
  f_retry(f) := retry; f_choice(f) := choice;
  f_glotop(f) := gsp; f_trail(f) := trhead;
  f_nvars(f) := nvars;
  for i := 1 to nvars do begin
    t_tag(f_local(f, i)) := make_tag(CELL, TERM_SIZE);
    t_val(f_local(f, i)) := NULL
  end;
  goalframe := f;
  if retry <> NULL then choice := goalframe
end;

{ Tail recursion can be used only under rather stringent conditions:
  the goal literal must be the last one in the body of the calling
  clause, both the calling clause and the called clause must be
  determinate, and the calling clause must not be the original goal
  (lest the answer variables be lost).  The macro |tro_test(p)|
  checks that these conditions are satisfied, where |p| is the
  untried part of the procedure for the current goal literal. }

{ |tro_test| -- test if a resolution step can use TRO }
define(&tro_test, (g_first(g_rest(current)) = NULL) and (choice < goalframe)
    and ($1 = NULL) and (goalframe <> base))

{ If the |tro_test| macro returns true, then it is safe to discard
  the calling frame in a resolution step before solving the subgoals
  in the newly-created frame.  |TroStep| implements this manoeuvre:
  read it after you understand the normal case covered by |Step|.

  Because the calling frame is to be discarded, it is important that
  no pointers from the new frame to the calling frame are created
  during unification.  |TroStep| uses the trick of swapping the two
  frames so that |Unify| will make pointers go the right way.  The
  idea is simple, but the details are made complicated by the need
  to adjust internal pointers in the relocated frame. }

{ |TroStep| -- perform a resolution step with tail-recursion }
procedure &TroStep;
  var &temp: frame; &oldsize, &newsize, i: integer;
begin
  if dflag then writeln('(TRO)');

  oldsize := frame_size(f_nvars(goalframe)); { size of old frame }
  newsize := frame_size(c_nvars(proc)); { size of new frame }
  temp := LocAlloc(newsize);
  temp := goalframe + newsize; { copy old frame here }

  { Copy the old frame: in reverse order in case of overlap }
  for i := oldsize-1 downto 0 do mem[temp+i] := mem[goalframe+i];

  { Adjust internal pointers in the copy }
  for i := 1 to f_nvars(goalframe) do begin
    if (t_kind(f_local(temp, i)) = CELL)
        and (t_val(f_local(temp, i)) <> NULL)
        and (goalframe <= t_val(f_local(temp, i)))
        and (t_val(f_local(temp, i)) < goalframe + oldsize) then
      t_val(f_local(temp, i)) := t_val(f_local(temp, i)) + newsize
  end;

  { Overwrite the old frame with the new one }
  f_nvars(goalframe) := c_nvars(proc);
  for i := 1 to f_nvars(goalframe) do begin
    t_tag(f_local(goalframe, i)) := make_tag(CELL, TERM_SIZE);
    t_val(f_local(goalframe, i)) := NULL
  end;

  { Perform the resolution step }
  ok := Unify(call, temp, c_head(proc), goalframe);
  current := c_rhs(proc);
  lsp := temp-1
end;

{ The |Step| procedure carries out a single resolution step.
  Built-in relations are treated as a special case; so are
  resolution steps that can use the tail-recursion optimization.
  Otherwise, we allocate a frame for the first clause for the
  current goal literal, unify the clause head with the literal, and adopt
  the clause body as the new goal.  The step can fail (and |Step|
  returns |false|) if there are no clauses to try, or if the first
  clause fails to match. }

{ |Step| -- perform a resolution step }
procedure &Step;
  var &retry: clause;
begin
  if s_action(t_func(call)) <> 0 then
    ok := DoBuiltin(s_action(t_func(call)))
  else if proc = NULL then
    ok := false
  else begin
    retry := Search(call, goalframe, c_next(proc));
    if tro_test(retry) then
      TroStep
    else begin
      PushFrame(c_nvars(proc), retry);
      ok := Unify(call, f_parent(goalframe), c_head(proc), goalframe);
      current := c_rhs(proc);
    end
  end
end;

{ The |Unwind| procedure returns from completed clauses until it
  finds one where there is still work to do, or it finds that the
  original goal is completed.  At this point, completed frames are
  discarded if they cannot take part in future backtracking. }

{ |Unwind| -- return from completed clauses }
procedure &Unwind;
begin
  while (g_first(current) = NULL) and (goalframe <> base) do begin
    debug_point('Exit', g_first(f_goal(goalframe)), f_parent(goalframe));
    current := g_rest(f_goal(goalframe));
    if goalframe > choice then lsp := goalframe-1;
    goalframe := f_parent(goalframe)
  end
end;

{ The |Backtrack| procedure undoes all the work that has been done
  since the last non-deterministic choice (indicated by the |choice|
  register).  The trail shows what assignments must be undone, and
  the stacks are returned to the state they were in when the choice
  was made.  The |proc| register is set from the |f_retry| field of
  the |choice| frame: this is the list of clauses for that goal that
  remain to be tried }

{ |Backtrack| -- roll back to the last choice-point }
procedure &Backtrack;
begin
  Restore;
  current := f_goal(choice); goalframe := f_parent(choice);
  call := Deref(g_first(current), goalframe);
  proc := f_retry(choice); gsp := f_glotop(choice);
  lsp := choice-1; choice := f_choice(choice);
  debug_point('Redo', call, goalframe);
end;

{ |Resume| is called with |ok = true| when the interpreter starts to
  execute a goal; it either returns with |ok = true| when the goal
  succeeds, or returns with |ok = false| when it has completely
  failed.  After |Resume| has returned |true|, it can be called
  again with |ok = false| to find another solution; in this case,
  the first action is to backtrack to the most recent choice-point. }

{ |Resume| -- continue execution }
procedure &Resume;
  label &exit;
begin
  while run do begin
    if ok then begin
      if g_first(current) = NULL then return;
      call := Deref(g_first(current), goalframe);
      debug_point('Call', call, goalframe);
      if (s_proc(t_func(call)) = NULL)
	  and (s_action(t_func(call)) = 0) then begin
	exec_error('call to undefined relation ');
	WriteString(s_name(t_func(call)));
	return
      end;
      proc := Search(call, goalframe, s_proc(t_func(call)))
    end
    else begin
      if choice <= base then return;
      Backtrack
    end;
    Step;
    if ok then Unwind;
    if gsp - lsp <= GCLOW then Collect
  end;
exit:
end;

{ |Execute| -- solve a goal by SLD-resolution }
procedure &Execute(g: clause);
  label &exit;
begin
  lsp := hp; gsp := MEMSIZE+1;
  current := NULL; goalframe := NULL; choice := NULL; trhead := NULL;
  PushFrame(c_nvars(g), NULL);
  choice := goalframe; base := goalframe; current := c_rhs(g);
  f_choice(base) := base;
  run := true; ok := true;
  repeat
    Resume;
    if not run then return;
    if not ok then
      begin writeln; write('no'); return end;
    ok := ShowAnswer(base)
  until ok;
  writeln; write('yes');
exit:
end;

{S Built-in relations }

{ Each built-in relation is a parameterless boolean-valued
  function: it finds its arguments from the call in |call|, carries
  out whatever side-effect is desired, and returns |true| exactly if
  the call succeeds.

  Two routines help in defining built-in relations: |GetArgs|
  dereferences the argument of the literal |call| and puts them in
  the global array |av|; and |NewInt| makes a new integer node on 
  the global stack. }

var
  &av: argbuf;  { |GetArgs| puts arguments here }
  &callbody: pointer;  { dummy clause body used by |call/1| }

{ |GetArgs| -- set up |av| array }
procedure &GetArgs;
  var i: integer;
begin
  for i := 1 to s_arity(t_func(call)) do
    av[i] := Deref(t_arg(call, i), goalframe)
end;

{ A couple of macros that abbreviate accesses to the |av| array: }
define(&a_kind, (t_kind(av[$1]) = $2))
define(&a_ival, t_ival(av[$1]))

function &NewInt(n: integer): term;
  var t: term;
begin
  t := GloAlloc(INT, TERM_SIZE);
  t_ival(t) := n;
  NewInt := t
end;

{ |DoCut| -- built-in relation !/0 }
function &DoCut: boolean;
begin
  choice := f_choice(goalframe);
  lsp := goalframe + frame_size(f_nvars(goalframe)) - 1;
  Commit;
  current := g_rest(current);
  DoCut := true
end;

{ |DoCall| -- built-in relation |call/1| }
function &DoCall: boolean;
begin
  GetArgs;
  if not a_kind(1, FUNC) then begin
    exec_error('bad argument to call/1');
    DoCall := false
  end
  else begin
    PushFrame(1, NULL);
    t_val(f_local(goalframe, 1)) :=
      GloCopy(av[1], f_parent(goalframe));
    current := callbody;
    DoCall := true
  end
end;

{ |DoNot| -- built-in relation |not/1| }
function &DoNot: boolean;
  var &savebase: frame;
begin
  GetArgs;
  if not a_kind(1, FUNC) then begin
    exec_error('bad argument to call/1');
    DoNot := false
  end
  else begin
    PushFrame(1, NULL);
    savebase := base; base := goalframe; choice := goalframe;
    t_val(f_local(goalframe, 1)) :=
      GloCopy(av[1], f_parent(goalframe));
    current := callbody; ok := true;
    Resume;
    choice := f_choice(base); goalframe := f_parent(base);
    if not ok then begin
      current := g_rest(f_goal(base));
      DoNot := true
    end
    else begin
      Commit;
      DoNot := false
    end;
    lsp := base-1; base := savebase
  end
end;

{ Procedures |DoPlus| and |DoTimes| implement the |plus/3| and
  |times/3| relations: they both involve a case analysis of which
  arguments are known, followed by a call to |Unify| to unify the
  remaining argument with the result.  The |times/3| relation fails
  on divide-by-zero, even in the case |times(X, 0, 0)|, which
  actually has infinitely many solutions. }

{ |DoPlus| -- built-in relation |plus/3| }
function &DoPlus: boolean;
  var &result: boolean;
begin
  GetArgs;
  result := false;
  if a_kind(1, INT) and a_kind(2, INT) then
    result := Unify(av[3], goalframe, NewInt(a_ival(1) + a_ival(2)), NULL)
  else if a_kind(1, INT) and a_kind(3, INT) then begin
    if a_ival(1) <= a_ival(3) then
      result := Unify(av[2], goalframe, 
		      NewInt(a_ival(3) - a_ival(1)), NULL)
  end
  else if a_kind(2, INT) and a_kind(3, INT) then begin
    if a_ival(2) <= a_ival(3) then
      result := Unify(av[1], goalframe, NewInt(a_ival(3) - a_ival(2)), NULL)
  end
  else
    exec_error('plus/3 needs at least two integers');
  current := g_rest(current);
  DoPlus := result
end;

{ |DoTimes| -- built-in relation |times/3| }
function &DoTimes: boolean;
  var &result: boolean;
begin
  GetArgs;
  result := false;
  if a_kind(1, INT) and a_kind(2, INT) then
    result := Unify(av[3], goalframe, 
		    NewInt(t_ival(av[1]) * t_ival(av[2])), NULL)
  else if a_kind(1, INT) and a_kind(3, INT) then begin
    if a_ival(1) <> 0 then
      if a_ival(3) mod a_ival(1) = 0 then
        result := Unify(av[2], goalframe, 
		        NewInt(a_ival(3) div a_ival(1)), NULL)
  end
  else if a_kind(2, INT) and a_kind(3, INT) then begin
    if a_ival(2) <> 0 then
      if a_ival(3) mod a_ival(2) = 0 then
        result := Unify(av[1], goalframe, 
			NewInt(a_ival(3) div a_ival(2)), NULL)
  end
  else
    exec_error('times/3 needs at least two integers');
  current := g_rest(current);
  DoTimes := result
end;

{ |DoEqual| -- built-in relation |=/2| }
function &DoEqual: boolean;
begin
  GetArgs;
  current := g_rest(current);
  DoEqual := Unify(av[1], goalframe, av[2], goalframe)
end;

{ |DoInteger| -- built-in relation |integer/1| }
function &DoInteger: boolean;
begin
  GetArgs;
  current := g_rest(current);
  DoInteger := a_kind(1, INT)
end;

{ |DoChar| -- built-in relation |char/1| }
function &DoChar: boolean;
begin
  GetArgs;
  current := g_rest(current);
  DoChar := a_kind(1, CHRCTR)
end;

{ |DoPrint| -- built-in relation |print/1| }
function DoPrint: boolean;
begin
  GetArgs;
  PrintTerm(av[1], goalframe, MAXPRIO);
  current := g_rest(current);
  DoPrint := true
end;

{ |DoNl| -- built-in relation |nl/0| }
function DoNl: boolean;
begin
  writeln;
  current := g_rest(current);
  DoNl := true
end;  

{ |DoBuiltin| -- switch for built-in relations }
function &DoBuiltin fwd((&action: integer): boolean);
begin
  case action of
  CUT:      DoBuiltin := DoCut;
  CALL:     DoBuiltin := DoCall;
  PLUS:     DoBuiltin := DoPlus;
  TIMES:    DoBuiltin := DoTimes;
  ISINT:    DoBuiltin := DoInteger;
  ISCHAR:   DoBuiltin := DoChar;
  NAFF:     DoBuiltin := DoNot;
  EQUALITY: DoBuiltin := DoEqual;
  FAIL:	    DoBuiltin := false;
  PRINT:    DoBuiltin := DoPrint;
  NL:	    DoBuiltin := DoNl
  default
    bad_tag('DoBuiltin', action)
  end
end;

{S Garbage collection }

{ Finally, here is the garbage collector, which reclaims space in the
  global stack that is no longer accessible.  It must work well with
  the stack-like expansion and contraction of the stack, so it is a
  compacting collector that does not alter the order in memory of
  the accessible nodes.

  The garbage collector operates in four phases: (1) Find and mark
  all accessible storage.  (2) Compute the new positions of the
  marked items after the global stack is compacted.  (3) Adjust all
  pointers to marked items.  (4) Compact the global stack and move
  it to the top of |mem|.  That may seem complicated, and it is; the
  garbage collector must know about all the run-time data
  structures, and is that one piece of the system that cuts across
  every abstraction boundary.

  Because of the relocation, |Collect| should only be called at
  `quiet' times, when the only pointers into the global stack are
  from interpreter registers and the local stack.  An example of a
  `non-quiet' time is in the middle of unification, when many
  recursive copies of the unification procedure are keeping pointers
  to bits of term structure.  To avoid the need to collect garbage
  at such times, the main control of the interpreter calls |Collect|
  before each resolution step if the space left is less than
  |GCLOW|.  If space runs out in the subsequent resolution step,
  execution is abandoned without much grace.  This plan works
  because the amount of space consumed in a resolution step is
  bounded by the maximum size of a program clause; this size is not
  checked, though. }

var &shift: integer;  { amount global stack will shift }

{ |Visit| -- recursively mark a term and all its sub-terms }
procedure &Visit(t: term);
  label &exit;
  var i, n: integer;
begin
  { We reduce the depth of recursion when marking long lists by
    treating the last argument of a function iteratively, making
    recursive calls only for the other arguments. }
  while t <> NULL do begin
    if not is_glob(t) or marked(t) then return;
    add_mark(t);
    case t_kind(t) of
    FUNC:
      begin
	n := s_arity(t_func(t));
	if n = 0 then return;
        for i := 1 to n-1 do Visit(t_arg(t, i));
        t := t_arg(t, n)
      end;
    CELL:
      t := t_val(t);
    INT, CHRCTR:
      return
    default
      bad_tag('Visit', t_kind(t))
    end
  end;
exit:
end;

{ |MarkStack| -- mark from each frame on the local stack }
procedure &MarkStack;
  var f: frame; i: integer;
begin
  f := hp+1;
  while f <= lsp do begin
    for i := 1 to f_nvars(f) do
      if t_kind(f_local(f, i)) = CELL then
	Visit(t_val(f_local(f, i)));
    f := f + frame_size(f_nvars(f))
  end
end;

{ |CullTrail| -- delete an initial segment of unwanted trail }
procedure &CullTrail(var p: trail);
  label &exit;
begin
  while p <> NULL do begin
    if x_reset(p) <> NULL then
      if not is_glob(x_reset(p)) or marked(x_reset(p)) then
	return;
    p := x_next(p)
  end;
exit:
end;

{ |MarkTrail| -- remove dead trail nodes, mark the rest. }
procedure &MarkTrail;
  var p: trail;
begin
  CullTrail(trhead); p := trhead;
  while p <> NULL do
    begin add_mark(p); CullTrail(x_next(p)); p := x_next(p) end
end;

{ |Relocate| -- compute shifts }
procedure &Relocate;
  var p: pointer; &step: integer;
begin
  shift := 0; p := gsp;
  while p <= MEMSIZE do begin
    step := t_size(p); t_shift(p) := shift;
    if not marked(p) then
      shift := shift + step;
    p := p + step
  end
end;

{ |AdjustPointer| -- update a pointer}
procedure &AdjustPointer(var p: term);
begin
  if (p <> NULL) and is_glob(p) then begin
    if not marked(p) then
      panic('adjusting pointer to unmarked block');
    p := p + shift - t_shift(p)
  end
end;

{ |AdjustStack| -- adjust pointers in local stack }
procedure &AdjustStack;
  var f: frame; i: integer; q: pointer;
  label &found, &found2;
begin
  f := hp+1;
  while f <= lsp do begin
    q := f_glotop(f);
    while q <= MEMSIZE do begin
      if marked(q) then goto found;
      q := q + t_size(q)
    end;
  found:
    if q <= MEMSIZE then AdjustPointer(q);
    f_glotop(f) := q;

    q := f_trail(f);
    while q <> NULL do begin
      if marked(q) then goto found2;
      q := x_next(q)
    end;
  found2:
    AdjustPointer(q);
    f_trail(f) := q;

    for i := 1 to f_nvars(f) do
      if t_kind(f_local(f, i)) = CELL then
	AdjustPointer(t_val(f_local(f, i)));
    f := f + frame_size(f_nvars(f));
  end
end;

{ |AdjustInternal| -- update internal pointers }
procedure &AdjustInternal;
  var p, i: integer;
begin
  p := gsp;
  while p <= MEMSIZE do begin
    if marked(p) then begin
      case t_kind(p) of
      FUNC:
        for i := 1 to s_arity(t_func(p)) do
	  AdjustPointer(t_arg(p, i));
      CELL:
        AdjustPointer(t_val(p));
      UNDO:
	begin
	  AdjustPointer(x_reset(p));
	  AdjustPointer(x_next(p))
	end;
      INT, CHRCTR:
        skip
      default
	bad_tag('Adjust', t_kind(p))
      end
    end;
    p := p + t_size(p)
  end
end;

{ |Compact| -- compact marked blocks and un-mark }
procedure &Compact;
  var p, q, &step, i: integer;
begin
  p := gsp; q := gsp;
  while p <= MEMSIZE do begin
    step := t_size(p);
    if marked(p) then begin rem_mark(p);
      for i := 0 to step-1 do mem[q+i] := mem[p+i];
      q := q + step
    end;
    p := p + step
  end;
  gsp := gsp+shift;
  for i := MEMSIZE downto gsp do mem[i] := mem[i-shift];
end;

{ |Collect| -- collect garbage }
procedure &Collect;
begin
  write('[gc'); flush_out;

  { Phase 1: marking }
  Visit(call); MarkStack; MarkTrail;

  { Phase 2: compute new locations }
  Relocate;

  { Phase 3: adjust pointers }
  AdjustPointer(call); AdjustPointer(trhead);
  AdjustStack; AdjustInternal;

  { Phase 4: compact }
  Compact;

  write(']'); flush_out;
  if gsp - lsp <= GCHIGH then exec_error('out of memory space')
end;

{S Main program }

{ |Initialize| -- initialize everything }
procedure &Initialize;
  var i: integer; p: term;
begin
  dflag := false; errcount := 0;
  pbchar := ENDFILE; charptr := 0;
  hp := 0; InitSymbols;

  { Set up the |refnode| array }
  for i := 1 to MAXARITY do begin
    p := HeapAlloc(TERM_SIZE);
    t_tag(p) := make_tag(REF, TERM_SIZE);
    t_index(p) := i; refnode[i] := p
  end;

  { The dummy clause $\it call(\sci p) \IF p$ is used by |call/1|. }
  callbody := HeapAlloc(2);
  g_first(callbody) := MakeRef(1);
  g_first(g_rest(callbody)) := NULL
end;

{ |ReadFile| -- read and process clauses from an open file }
procedure &ReadFile;
  var c: clause;
begin
  lineno := 1;
  repeat
    hmark := hp;
    c := ReadClause;
    if c <> NULL then begin
      if dflag then PrintClause(c);	
      if c_head(c) <> NULL then
        AddClause(c)
      else begin
        if interacting then
	  begin pbchar := ENDFILE; readln end;
        Execute(c);
	writeln;
	hp := hmark
      end
    end
  until c = NULL
end;

ifdef(fpc,define(argc,paramcount+1)
  define(argv,$2 := paramstr($1))
  define(closein,close($1)))

ifdef(fpc,function openin(var f: text; s: tempstring): boolean;
  begin
    if not fileexists(s) then
      openin := false
    else begin
      assign(f, s); reset(f); openin := true
    end
  end;)

{ |ReadProgram| -- read files listed on command line }
procedure &ReadProgram;
  var &i0, i: integer;
    &arg: tempstring;
begin
  i0 := 1;
  if argc > 1 then begin
    argv(1, arg);
    if (arg[1] = '-') and (arg[2] = 'd')
	and (arg[3] = ENDSTR) then begin
      dflag := true;
      incr(i0)
    end
  end;
  for i := i0 to argc-1 do begin
    argv(i, arg);
    filename := SaveString(arg);
    if not openin(infile, arg) then begin
      write('Can''t read '); WriteString(filename); writeln;
      abort
    end;
    write('Reading '); WriteString(filename); writeln;
    ReadFile;
    closein(infile);
    if errcount > 0 then abort
  end
end;

begin  { main program }
  writeln('Welcome to picoProlog');
  Initialize;
  interacting := false; ReadProgram;
  interacting := true; lineno := 1; ReadFile;
  writeln;
end_of_pp:
end.
