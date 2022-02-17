MODULE obProlog;

{ Copyright (C) J. M. Spivey 1992 }

define(bitops)

IMPORT Out, Files, Args, Bit;

{ This is the `picoProlog' interpreter described in the book `An
  Introduction to Logic Programming through Prolog' by Michael Spivey
  (Prentice Hall, 1995).  Copyright is retained by the author, but
  permission is granted to copy and modify the program for any purpose
  other than direct commercial gain.

  The text of this program must be processed by the `ppp'
  macro processor before it can be compiled. }

{ tunable parameters }
CONST
  MAXSYMBOLS = 511;  { max no. of symbols }
  HASHFACTOR = 90;  { percent loading factor for hash table }
  MAXCHARS = 2048;  { max chars in symbols }
  MAXSTRING = 128;  { max string length }
  MAXARITY = 63;  { max arity of function, vars in clause }
  MEMSIZE = 25000;  { size of |mem| array }
  GCLOW = 500;  { call GC when this much space left }
  GCHIGH = 1000;  { GC must find this much space }

{ special character values }
define(TAB, CHR(9))  { tab character }
define(ENDLINE, CHR(10))  { newline character }
define(ENDFILE, CHR(127))  { end of file }
define(QUOTE, 27X) { single quote }

VAR curin: Files.File;

PROCEDURE ReadChar(VAR ch: CHAR);
BEGIN
  IF Files.Eof(curin) THEN
    ch := ENDFILE
  ELSE
    Files.ReadChar(curin, ch)
  END
END ReadChar;

PROCEDURE OpenIn(VAR fname: ARRAY OF CHAR): BOOLEAN;
  VAR f: Files.File;
BEGIN
  f := Files.Open(fname, 'r');
  IF f = NIL THEN RETURN FALSE END;
  curin := f;
  RETURN TRUE
END OpenIn;

PROCEDURE CloseIn();
BEGIN
  Files.Close(curin);
  curin := Files.stdin
END CloseIn;


{S Error handling }

{ These macros print an error message, then either arrange for
  execution of a goal to abandoned (by clearing the |run| flag), or
  abandon the whole run of picoProlog.  They use the |$0| feature to
  allow for a list of arguments.

  Errors during execution of a goal are reported by |exec_error|; it
  sets the |run| flag to FALSE, so the main execution mechanism will
  stop execution before starting on another resolution step. }

VAR run: BOOLEAN;  { whether execution should continue }
  dflag: BOOLEAN;  { switch for debugging code }

define(exec_error,
  Out.Ln; Out.String('Error: '); Out.String($0); run := FALSE)
define(panic, 
  Out.Ln; Out.String('Panic: '); Out.String($0); Out.Ln; HALT(2))
define(bad_tag, panic('bad tag' {$2 in $1}))

{S String buffer }

{ The strings that are the names of function symbols, variables,
  etc. are saved in the array |charbuf|: each string is
  represented elsewhere by an index |k| into this array, and the
  characters of the string are |charbuf[k]|,
  |charbuf[k+1]|,~\dots, terminated by the character |0X|.
  |charptr| is the first unoccupied location in |charbuf|.

  In addition to these `permanent' strings, there are `temporary'
  strings put together for some short-term purpose.  These are
  kept in arrays of size |MAXSTRING|, and are also terminated by |0X|. }

TYPE
  permstring = INTEGER;
  tempstring = ARRAY MAXSTRING OF CHAR;

VAR
  charptr: INTEGER;
  charbuf: ARRAY MAXCHARS OF CHAR;

{ |StringLength| -- length of a tempstring }
PROCEDURE StringLength(VAR s: tempstring): INTEGER; 
  VAR i: INTEGER;
BEGIN
  i := 0;
  WHILE s[i] # 0X DO INC(i) END;
  RETURN i
END StringLength;

{ |SaveString| -- make a tempstring permanent }
PROCEDURE SaveString(VAR s: tempstring): permstring; 
  VAR p, i: INTEGER;
BEGIN
  IF charptr + StringLength(s) + 1 > MAXCHARS THEN
    panic('out of string space')
  END;
  p := charptr; i := 0;
  REPEAT
    charbuf[charptr] := s[i]; INC(charptr); INC(i)
  UNTIL charbuf[charptr-1] = 0X;
  RETURN p
END SaveString;

{ |StringEqual| -- compare a tempstring to a permstring }
PROCEDURE StringEqual(VAR s1: tempstring; s2: permstring): BOOLEAN; 
  VAR i: INTEGER;
BEGIN
  i := 0;
  WHILE (s1[i] # 0X) && (s1[i] = charbuf[s2+i]) DO INC(i) END;
  RETURN (s1[i] = charbuf[s2+i])
END StringEqual;

{ |WriteString| -- print a permstring }
PROCEDURE WriteString(s: permstring); 
  VAR i: INTEGER;
BEGIN
  i := s;
  WHILE charbuf[i] # 0X DO
    Out.Char(charbuf[i]); INC(i)
  END
END WriteString;

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
  which is actually the code |ORD(c)|.  |CELL| nodes represent
  variables and have a |t_val| field that points to the value. |REF|
  nodes are the numeric markers in program clauses that refer to a
  slot in the frame for a clause; the |t_index| field is the
  index of the slot. |UNDO| nodes do not represent terms at all,
  but items on the trail stack; they share some of the layout of
  terms, so that they can be treated the same by the garbage
  collector. }

TYPE
  ptr = INTEGER;  { index into |mem| array }
define(NULL, 0)  { null pointer }

TYPE term = ptr;
define(t_tag, mem[$1])
ifdef(bitops,
  define(t_kind, LSR(t_tag($1), 8))  { one of |FUNC|; |INT|; \dots }
  define(t_size, Bit.And(t_tag($1), 127))  { size in words }
  define(marked, (Bit.And(t_tag($1), 128) # 0))  { GC mark }
  define(add_mark, t_tag($1) := Bit.Or(t_tag($1), 128))
  define(rem_mark, t_tag($1) := Bit.And(t_tag($1), Bit.Not(128)))
  define(make_tag, LSL($1, 8) + $2),
{ else }
  define(t_kind, t_tag($1) DIV 256)  { one of |FUNC|; |INT|; \dots }
  define(t_size, t_tag($1) MOD 128)  { size in words }
  define(marked, (t_tag($1) MOD 256 >= 128))  { GC mark }
  define(add_mark, t_tag($1) := t_tag($1) + 128)
  define(rem_mark, t_tag($1) := t_tag($1) - 128)
  define(make_tag, 256 * $1 + $2)
)
define(t_shift, mem[$1+1])  { for use by gc }
define(FUNC, 1)  { compound term }
  define(t_func, mem[$1+2])  { \quad function symbol }
  define(t_arg, mem[$1+$2+2])  { \quad arguments (start from 1) }
define(INT, 2)  { integer }
  define(t_ival, mem[$1+2])  { \quad integer value }
define(CHRCTR, 3)  { character }
  define(t_cval, mem[$1+2])  { \quad character value }
define(CELL, 4)  { variable cell }
  define(t_val, mem[$1+2])  { \quad value or |NULL| if unbound }
define(REF, 5)  { variable reference }
  define(t_index, mem[$1+2])  { \quad index in frame }
define(UNDO, 6)  { trail item }
  { see later }
define(TERM_SIZE, 3)  { \dots\ plus no. of args }

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

VAR
  lsp, gsp, hp, hmark: ptr;
  mem: ARRAY MEMSIZE+1 OF INTEGER;

{ |LocAlloc| -- allocate space on local stack }
PROCEDURE LocAlloc(size: INTEGER): ptr; 
  VAR p: ptr;
BEGIN
  IF lsp + size >= gsp THEN panic('out of stack space') END;
  p := lsp + 1; lsp := lsp + size; RETURN p
END LocAlloc;

{ |GloAlloc| -- allocate space on global stack }
PROCEDURE GloAlloc(kind, size: INTEGER): ptr; 
  VAR p: ptr;
BEGIN
  IF gsp - size <= lsp THEN
    panic('out of stack space')
  END;
  gsp := gsp - size; p := gsp;
  t_tag(p) := make_tag(kind, size);
  RETURN p
END GloAlloc;

{ |HeapAlloc| -- allocate space on heap }
PROCEDURE HeapAlloc(size: INTEGER): ptr; 
  VAR p: ptr;
BEGIN
  IF hp + size > MEMSIZE THEN panic('out of heap space') END;
  p := hp + 1; hp := hp + size; RETURN p
END HeapAlloc;

define(is_heap, ($1 <= hp))  { test if a pointer is in the heap }
define(is_glob, ($1 >= gsp))  { test if it is in the global stack }

{S Character input }

{ Pascal's I/O facilities view text files as sequences of lines,
  but it is more convenient for picoProlog to deal with a uniform
  sequence of characters, with the end of a line indicated by an
  |ENDLINE| character, and the end of a file by an |ENDFILE|
  character.  The routines here perform the translation (probably
  reversing a translation done by the Pascal run-time library).
  They also allow a single character to be `pushed back' on the
  input, so that the scanner can avoid reading too far. }

VAR
  interacting: BOOLEAN;  { whether input is from terminal }
  pbchar: CHAR;  { pushed-back char, else |ENDFILE| }
  lineno: INTEGER;  { line number in current file }
  filename: permstring;  { name of current file }

{ |GetChar| -- get a character }
PROCEDURE GetChar(): CHAR; 
  VAR ch: CHAR;
BEGIN
  IF pbchar # ENDFILE THEN
    ch := pbchar; pbchar := ENDFILE
  ELSE
    ReadChar(ch);
    IF ch = ENDLINE THEN INC(lineno) END
  END;
  RETURN ch
END GetChar;

{ |PushBack| -- push back a character on the input }
PROCEDURE PushBack(ch: CHAR); 
BEGIN
  pbchar := ch
END PushBack;

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

TYPE clause = ptr;
define(c_nvars, mem[$1])  { no. of variables }
define(c_key, mem[$1+1])  { unification key }
define(c_next, mem[$1+2])  { next clause for same relation }
define(c_head, mem[$1+3])  { clause head }
define(c_rhs, ($1+4))  { clause body (ends with NULL) }
define(c_body, mem[c_rhs($1)+$2-1])
define(CLAUSE_SIZE, 4)  { ... plus size of body + 1 }

define(g_first, mem[$1])  { first of a list of literals }
define(g_rest, ($1)+1)  { rest of the list }

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

TYPE frame = ptr;
define(f_goal, mem[$1])  { the goal }
define(f_parent, mem[$1+1])  { parent frame }
define(f_retry, mem[$1+2])  { untried clauses }
define(f_choice, mem[$1+3])  { previous choice-point }
define(f_glotop, mem[$1+4])  { global stack at creation }
define(f_trail, mem[$1+5])  { trail state at creation }
define(f_nvars, mem[$1+6])  { no. of local variables }
define(f_local, ($1+7+($2-1)*TERM_SIZE))
define(FRAME_SIZE, 7)  { \dots plus space for local variables }

{ |frame_size| -- compute size of a frame with |n| variables }
define(frame_size, (FRAME_SIZE + ($1)*TERM_SIZE))

VAR
  current: ptr;  { current goal }
  call: term;  { |Deref|'ed first literal of goal }
  goalframe: frame;  { current stack frame }
  choice: frame;  { last choice point }
  base: frame;  { frame for original goal }
  prok: clause;  { clauses left to try on current goal }

{ |Deref| is a function that resolves the indirection in the
  representation of terms.  It looks up references in the frame, and
  following the chain of pointers from variable cells to their
  values.  The result is an explicit representation of the argument
  term; if the frame is non-|NULL|, the result is never a |REF|
  node, and if it is a |CELL| node, the |t_val| field is empty. }

{ |Deref| -- follow |VAR| and |CELL| pointers }
PROCEDURE Deref(t: term; e: frame): term; 
BEGIN
  IF t = NULL THEN panic('Deref') END;
  IF (t_kind(t) = REF) && (e # NULL) THEN
    t := f_local(e, t_index(t))
  END;
  WHILE (t_kind(t) = CELL) && (t_val(t) # NULL) DO
    t := t_val(t)
  END;
  RETURN t
END Deref;

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
  at the |s_prok| field and is linked together by the |c_next| fields
  of the clauses. }

TYPE symbol = INTEGER;  { index in |symtab| }

VAR
  nsymbols: INTEGER;  { number of symbols }
  symtab: ARRAY MAXSYMBOLS+1 OF RECORD
      name: INTEGER;  { print name: index in |charbuf| }
      arity: INTEGER;  { number of arguments or -1 }
      action: INTEGER;  { code if built-in, 0 otherwise }
      prok: clause;  { clause chain }
    END;
  cons, eqsym, cutsym, nilsym, notsym: symbol;
  node: symbol;

{ We define selector macros for symbols, just as for terms }
define(s_name, symtab[$1].name)
define(s_arity, symtab[$1].arity)
define(s_action, symtab[$1].action)
define(s_prok, symtab[$1].prok)

{ |Lookup| -- convert string to internal symbol }
PROCEDURE Lookup(VAR name: tempstring): symbol; 
  VAR h, i: INTEGER; p: symbol;
BEGIN
  { Compute the hash function in |h| }
  h := 0; i := 0;
  WHILE name[i] # 0X DO
    h := (5 * h + ORD(name[i])) MOD MAXSYMBOLS; INC(i) 
  END;

  { Search the hash table }
  p := h+1;
  WHILE s_name(p) # -1 DO
    IF StringEqual(name, s_name(p)) THEN RETURN p END;
    DEC(p);
    IF p = 0 THEN p := MAXSYMBOLS END
  END;

  { Not found: enter a new symbol }
  { Be careful to avoid overflow on 16 bit machines: }
  IF nsymbols >= (MAXSYMBOLS DIV 10) * (HASHFACTOR DIV 10) THEN
    panic('out of symbol space')
  END;
  s_name(p) := SaveString(name);
  s_arity(p) := -1;
  s_action(p) := 0; s_prok(p) := NULL;
  RETURN p
END Lookup;

TYPE keyword = ARRAY OF CHAR;

{ |Enter| -- define a built-in symbol }
PROCEDURE Enter(name: keyword; arity: INTEGER; action: INTEGER): symbol; 
  VAR s: symbol; i: INTEGER; temp: tempstring;
BEGIN
  i := 0;
  WHILE name[i] # ' ' DO
    temp[i] := name[i]; INC(i) 
  END;
  temp[i] := 0X; s := Lookup(temp);
  s_arity(s) := arity; s_action(s) := action;
  RETURN s
END Enter;

{ Codes for built-in relations }
define(CUT, 1)  { $!/0$ }
define(CALL, 2)  { |call/1| }
define(PLUS, 3)  { |plus/3| }
define(TIMES, 4)  { |times/3| }
define(ISINT, 5)  { |integer/1| }
define(ISCHAR, 6)  { |char/1| }
define(NAFF, 7)  { |not/1| }
define(EQUALITY, 8)  { |=/2| }
define(FAIL, 9)  { |false/0| }
define(PRINT, 10)  { |print/1| }
define(NL, 11)  { |nl/0| }

{ |InitSymbols| -- initialize and define standard symbols }
PROCEDURE InitSymbols(); 
  VAR i: INTEGER; dummy: symbol;
BEGIN
  nsymbols := 0;
  FOR i := 1 TO MAXSYMBOLS DO s_name(i) := -1 END;
  cons   := Enter(':       ', 2, 0);
  cutsym := Enter('!       ', 0, CUT);
  eqsym  := Enter('=       ', 2, EQUALITY);
  nilsym := Enter('nil     ', 0, 0);
  notsym := Enter('not     ', 1, NAFF);
  node   := Enter('node    ', 2, 0);
  dummy  := Enter('call    ', 1, CALL);
  dummy  := Enter('plus    ', 3, PLUS);
  dummy  := Enter('times   ', 3, TIMES);
  dummy  := Enter('integer ', 1, ISINT);
  dummy  := Enter('char    ', 1, ISCHAR);
  dummy  := Enter('false   ', 0, FAIL);
  dummy  := Enter('print   ', 1, PRINT);
  dummy  := Enter('nl      ', 0, NL)
END InitSymbols;

{ |AddClause| -- insert a clause at the end of its chain }
PROCEDURE AddClause(c: clause); 
  VAR s: symbol; p: clause;
BEGIN
  s := t_func(c_head(c));
  IF s_action(s) # 0 THEN
    exec_error('cannot add clauses to built-in relation ');
    WriteString(s_name(s))
  ELSIF s_prok(s) = NULL THEN
    s_prok(s) := c
  ELSE
    p := s_prok(s);
    WHILE c_next(p) # NULL DO p := c_next(p) END;
    c_next(p) := c
  END
END AddClause;

{S Building terms on the heap }

{ Next, some convenient routines that construct various kinds of
  term in the heap area: they are used by the parsing routines to
  construct the internal representation of the input terms they
  read.  The routine |MakeRef| that is supposed to construct a |REF|
  node in fact returns a pointer to one from a fixed collection.
  This saves space, since all clauses can share the same small
  number of |REF| nodes. }

TYPE argbuf = ARRAY MAXARITY+1 OF term;

{ |MakeCompound| -- construct a compound term on the heap }
PROCEDURE MakeCompound(fun: symbol; VAR arg: argbuf): term; 
  VAR p: term; i, n: INTEGER;
BEGIN
  n := s_arity(fun);
  p := HeapAlloc(TERM_SIZE+n);
  t_tag(p) := make_tag(FUNC, TERM_SIZE+n);
  t_func(p) := fun;
  FOR i := 1 TO n DO t_arg(p, i) := arg[i] END;
  RETURN p
END MakeCompound;

{ |MakeNode| -- construct a compound term with up to 2 arguments }
PROCEDURE MakeNode(fun: symbol; a1, a2: term): term; 
  VAR arg: argbuf;
BEGIN
  arg[1] := a1; arg[2] := a2;
  RETURN MakeCompound(fun, arg)
END MakeNode;

VAR refnode: ARRAY MAXARITY+1 OF term;

{ |MakeRef| -- return a reference cell prepared earlier }
PROCEDURE MakeRef(offset: INTEGER): term; 
BEGIN
  RETURN refnode[offset]
END MakeRef;

{ |MakeInt| -- construct an integer node on the heap }
PROCEDURE MakeInt(i: INTEGER): term; 
  VAR p: term;
BEGIN
  p := HeapAlloc(TERM_SIZE);
  t_tag(p) := make_tag(INT, TERM_SIZE);
  t_ival(p) := i; RETURN p
END MakeInt;

{ |MakeChar| -- construct a character node on the heap }
PROCEDURE MakeChar(c: CHAR): term; 
  VAR p: term;
BEGIN
  p := HeapAlloc(TERM_SIZE);
  t_tag(p) := make_tag(CHRCTR, TERM_SIZE);
  t_cval(p) := ORD(c); RETURN p
END MakeChar;

{ |MakeString| -- construct a string as a Prolog list of chars }
PROCEDURE MakeString(VAR s: tempstring): term; 
  VAR p: term; i: INTEGER;
BEGIN
  i := StringLength(s);
  p := MakeNode(nilsym, NULL, NULL);
  WHILE i > 0 DO
    DEC(i); p := MakeNode(cons, MakeChar(s[i]), p)
  END;
  RETURN p
END MakeString;

{ |MakeClause| -- construct a clause on the heap }
PROCEDURE MakeClause(nvars: INTEGER; head: term; 
		    VAR body: argbuf; nbody: INTEGER): clause;
  VAR p: clause; i: INTEGER;
BEGIN
  p := HeapAlloc(CLAUSE_SIZE + nbody + 1);
  c_nvars(p) := nvars; c_next(p) := NULL; c_head(p) := head;
  FOR i := 1 TO nbody DO c_body(p, i) := body[i] END;
  c_body(p, nbody+1) := NULL;
  IF head = NULL THEN 
    c_key(p) := 0
  ELSE 
    c_key(p) := Key(head, NULL)
  END;
  RETURN p
END MakeClause;

{S Printing terms }

{ These routines print terms on the user's terminal.  The main
  routine is |PrintTerm|, which prints a term by recursively
  traversing it.  Unbound cells are printed in the form |'L123'|
  (for local cells) or |'G234'| (for global cells): the number is
  computed from the address of the cell.  If the frame is
  |NULL|, reference nodes are printed in the form |'@3'|. }

{ operator priorities }
define(MAXPRIO, 2)  { isolated term }
define(ARGPRIO, 2)  { function arguments }
define(EQPRIO, 2)  { equals sign }
define(CONSPRIO, 1)  { colon }

{ |IsString| -- check if a list represents a string }
PROCEDURE IsString(t: term; e: frame): BOOLEAN; 
  CONST limit = 128;
  VAR i: INTEGER;
BEGIN
  i := 0; t := Deref(t, e);
  WHILE i < limit DO
    IF (t_kind(t) # FUNC) OR (t_func(t) # cons) THEN
      RETURN (t_kind(t) = FUNC) && (t_func(t) = nilsym)
    ELSIF t_kind(Deref(t_arg(t, 1), e)) # CHRCTR THEN
      RETURN FALSE
    ELSE
      INC(i); t := Deref(t_arg(t, 2), e) 
    END
  END;
  RETURN FALSE
END IsString;

{ |IsList| -- check if a term is a proper list }
PROCEDURE IsList(t: term; e: frame): BOOLEAN; 
  CONST limit = 128;
  VAR i: INTEGER;
BEGIN
  i := 0; t := Deref(t, e);
  WHILE i < limit DO
    IF (t_kind(t) # FUNC) OR (t_func(t) # cons) THEN
      RETURN (t_kind(t) = FUNC) && (t_func(t) = nilsym)
    ELSE
      INC(i); t := Deref(t_arg(t, 2), e)
    END
  END;
  RETURN FALSE
END IsList;

{ |ShowString| -- print a list as a string }
PROCEDURE ShowString(t: term; e: frame); 
BEGIN
  t := Deref(t, e);
  Out.Char('"');
  WHILE t_func(t) # nilsym DO
    Out.Char(CHR(t_cval(Deref(t_arg(t, 1), e))));
    t := Deref(t_arg(t, 2), e)
  END;
  Out.Char('"')
END ShowString;

{ |PrintCompound| -- print a compound term }
PROCEDURE PrintCompound(t: term; e: frame; prio: INTEGER); 
  VAR f: symbol; i: INTEGER;
BEGIN
  f := t_func(t);
  IF f = cons THEN
    { |t| is a list: try printing as a string, or use infix : }
    IF IsString(t, e) THEN
      ShowString(t, e)
    ELSE
      IF prio < CONSPRIO THEN Out.Char('(') END;
      PrintTerm(t_arg(t, 1), e, CONSPRIO-1);
      Out.Char(':');
      PrintTerm(t_arg(t, 2), e, CONSPRIO);
      IF prio < CONSPRIO THEN Out.Char(')') END
    END
  ELSIF f = eqsym THEN
    { |t| is an equation: use infix = }
    IF prio < EQPRIO THEN Out.Char('(') END;
    PrintTerm(t_arg(t, 1), e, EQPRIO-1);
    Out.String(' = ');
    PrintTerm(t_arg(t, 2), e, EQPRIO-1);
    IF prio < EQPRIO THEN Out.Char(')') END
  ELSIF f = notsym THEN
    { |t| is a literal 'not P' }
    Out.String('not ');
    PrintTerm(t_arg(t, 1), e, MAXPRIO)
  ELSIF (f = node) && IsList(t_arg(t, 2), e) THEN
    PrintNode(t, e)
  ELSE
    { use ordinary notation }
    WriteString(s_name(f));
    IF s_arity(f) > 0 THEN
      Out.Char('(');
      PrintTerm(t_arg(t, 1), e, ARGPRIO);
      FOR i := 2 TO s_arity(f) DO
        Out.String(', ');
        PrintTerm(t_arg(t, i), e, ARGPRIO)
      END;
      Out.Char(')')
    END
  END
END PrintCompound;

{ |PrintNode| -- print and optree node }
PROCEDURE PrintNode(t: term; e: frame); 
  VAR u: term;
BEGIN
  Out.Char('<');
  PrintTerm(t_arg(t, 1), e, MAXPRIO);
  u := Deref(t_arg(t, 2), e);
  WHILE t_func(u) # nilsym DO
    Out.String(', ');
    PrintTerm(t_arg(u, 1), e, MAXPRIO);
    u := Deref(t_arg(u, 2), e)
  END;
  Out.Char('>');
END PrintNode;

{ |PrintTerm| -- print a term }
PROCEDURE PrintTerm(t: term; e: frame; prio: INTEGER); 
BEGIN
  t := Deref(t, e);
  IF t = NULL THEN
    Out.String('*null-term*')
  ELSE
    CASE t_kind(t) OF
      FUNC:
        PrintCompound(t, e, prio)
    | INT:
        Out.Int(t_ival(t), 0)
    | CHRCTR:
        Out.Char(QUOTE); Out.Char(CHR(t_cval(t))); Out.Char(QUOTE)
    | CELL:
        IF is_glob(t) THEN
          Out.Char('G'); Out.Int((MEMSIZE - t) DIV TERM_SIZE, 0)
        ELSE
          Out.Char('L'); Out.Int((t - hp) DIV TERM_SIZE, 0)
        END
    | REF:
        Out.Char('@'); Out.Int(t_index(t), 0)
    ELSE
      Out.String('*unknown-term(tag='); 
      Out.Int(t_kind(t), 0); Out.String(')*')
    END
  END
END PrintTerm;

{ |PrintClause| -- print a clause }
PROCEDURE PrintClause(c: clause); 
  VAR i: INTEGER;
BEGIN
  IF c = NULL THEN
    Out.String('*null-clause*'); Out.Ln;
  ELSE
    IF c_head(c) # NULL THEN
      PrintTerm(c_head(c), NULL, MAXPRIO);
      Out.Char(' ')
    END;
    Out.String(':- ');
    IF c_body(c, 1) # NULL THEN
      PrintTerm(c_body(c, 1), NULL, MAXPRIO);
      i := 2;
      WHILE c_body(c, i) # NULL DO
	Out.String(', ');
	PrintTerm(c_body(c, i), NULL, MAXPRIO);
	INC(i)
      END
    END;
    Out.Char('.'); Out.Ln
  END
END PrintClause;

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

VAR
  token: INTEGER;  { last token from input }
  tokval: symbol;  { if |token = IDENT|, the identifier}
  tokival: INTEGER;  { if |token = NUMBER|, the number }
  toksval: tempstring;  { if |token = STRCON|, the string }
  errflag: BOOLEAN;  { whether recovering from an error }
  errcount: INTEGER;  { number of errors found so far }

{ Possible values for |token|: }
define(IDENT, 1)  { identifier: see |tokval| }
define(VARIABLE, 2)  { variable: see |tokval| }
define(NUMBER, 3)  { number: see |tokival| }
define(CHCON, 4)  { char constant: see |tokival| }
define(STRCON, 5)  { string constant: see |toksval| }
define(ARROW, 6)  { |':-'| }
define(LPAR, 7)  { |'('| }
define(RPAR, 8)  { |')'| }
define(COMMA, 9)  { |','| }
define(DOT, 10)  { |'.'| }
define(COLON, 11)  { |':'| }
define(EQUAL, 12)  { |'='| }
define(NEGATE, 13)  { |'not'| }
define(EOFTOK, 14)  { end of file }
define(LANGLE, 15)  { |'<'| }
define(RANGLE, 16)  { |'>'| }
define(HASH, 17)  { |'#'| }

{ |syntax_error| -- report a syntax error }
define(syntax_error,
  IF ~errflag THEN ShowError(); Out.String($0); Out.Ln; Recover() END)

{ |ShowError| -- report error location }
PROCEDURE ShowError(); 
BEGIN
  errflag := TRUE; INC(errcount);
  IF ~interacting THEN
    Out.Char('"'); WriteString(filename); Out.Char('"');
    Out.String(', line '); Out.Int(lineno, 0); Out.Char(' ')
  END;
  Out.String('Syntax error - ')
END ShowError;

{ |Recover| -- discard rest of input clause }
PROCEDURE Recover(); 
  VAR ch: CHAR;
BEGIN
  IF ~interacting && (errcount >= 20) THEN
    Out.String('Too many errors: I am giving up'); Out.Ln; HALT(2) 
  END;
  IF token # DOT THEN
    REPEAT
      ch := GetChar()
    UNTIL (ch = '.') OR (ch = ENDFILE)
	OR (interacting && (ch = ENDLINE));
    token := DOT
  END
END Recover;

define(is_upper, ((($1 >= 'A') && ($1 <= 'Z')) OR ($1 = '_')))
define(is_letter, (is_upper($1) OR (($1 >= 'a') && ($1 <= 'z'))))
define(is_digit, (($1 >= '0') && ($1 <= '9')))

{ |Scan| -- read one symbol from |infile| into |token|. }
PROCEDURE Scan(); 
  VAR ch, ch2: CHAR; i: INTEGER;
BEGIN
  ch := GetChar(); token := 0;
  WHILE token = 0 DO
    { Loop after white-space or comment }
    IF ch = ENDFILE THEN
      token := EOFTOK
    ELSIF (ch = ' ') OR (ch = TAB) OR (ch = ENDLINE) THEN
      ch := GetChar()
    ELSIF is_letter(ch) THEN
      IF is_upper(ch) THEN 
	 token := VARIABLE
      ELSE 
	 token := IDENT
      END;
      i := 0;
      WHILE is_letter(ch) OR is_digit(ch) DO
        IF i > MAXSTRING THEN
          panic('identifier too long')
	END;
        toksval[i] := ch; ch := GetChar(); INC(i)
      END;
      PushBack(ch);
      toksval[i] := 0X; tokval := Lookup(toksval);
      IF tokval = notsym THEN token := NEGATE END
    ELSIF is_digit(ch) THEN
      token := NUMBER; tokival := 0;
      WHILE is_digit(ch) DO
        tokival := 10 * tokival + (ORD(ch) - ORD('0'));
        ch := GetChar()
      END;
      PushBack(ch)
    ELSE
      CASE ch OF
        '(': token := LPAR
      | ')': token := RPAR
      | ',': token := COMMA
      | '.': token := DOT
      | '=': token := EQUAL
      | '<': token := LANGLE
      | '>': token := RANGLE
      | '#': token := HASH
      | '!': token := IDENT; tokval := cutsym
      | '/':
	  ch := GetChar();
	  IF ch # '*' THEN
	    syntax_error('bad token /')
	  ELSE
	    ch2 := ' '; ch := GetChar();
	    WHILE (ch # ENDFILE) && ~((ch2 = '*') && (ch = '/')) DO
	      ch2 := ch; ch := GetChar() 
	    END;
	    IF ch = ENDFILE THEN
	      syntax_error('end of file in comment')
	    ELSE
	      ch := GetChar()
	    END
	  END
      | ':':
	  ch := GetChar();
	  IF ch = '-' THEN
	    token := ARROW
	  ELSE
	    PushBack(ch); token := COLON 
	  END
      | QUOTE:
	  token := CHCON; tokival := ORD(GetChar()); ch := GetChar();
	  IF ch # QUOTE THEN syntax_error('missing quote') END
      | '"':
	  token := STRCON; i := 0; ch := GetChar();
	  WHILE (ch # '"') && (ch # ENDLINE) DO
	    toksval[i] := ch; ch := GetChar(); INC(i) 
	  END;
	  toksval[i] := 0X;
	  IF ch = ENDLINE THEN
	    syntax_error('unterminated string');
	    PushBack(ch)
	  END
      ELSE
	syntax_error('illegal character')
      END
    END
  END
END Scan;

{ |PrintToken| -- print a token as a string }
PROCEDURE PrintToken(t: INTEGER); 
BEGIN
  CASE t OF
    IDENT:
      Out.String('identifier '); WriteString(s_name(tokval))
  | VARIABLE:
      Out.String('variable '); WriteString(s_name(tokval))
  | NUMBER: Out.String('number');
  | CHCON:  Out.String('char constant');
  | ARROW:  Out.String(':-');
  | LPAR:   Out.String('(');
  | RPAR:   Out.String(')');
  | COMMA:  Out.String(',');
  | DOT:    Out.String('.');
  | COLON:  Out.String(':');
  | EQUAL:  Out.String('=');
  | STRCON: Out.String('string constant')
  | LANGLE: Out.String('<')
  | RANGLE: Out.String('>')
  | HASH:   Out.String('#')
  ELSE
    Out.String('unknown token')
  END
END PrintToken;

{S Variable names }

{ As the parser reads an input clause, the routines here maintain a
  table of variable names and the corresponding run-time offsets in
  a frame for the clause: for each |i|, the name of the variable at
  offset |i| is |vartable[i]|.  Each clause contains only a few
  variables, so linear search is good enough.

  If the input clause turns out to be a goal, the table is saved and
  used again to display the answer when execution succeeds. }

VAR
  nvars: INTEGER;  { no. of variables so far }
  vartable: ARRAY MAXARITY+1 OF symbol;  { names of the variables }

{ |VarRep| -- look up a variable name }
PROCEDURE VarRep(name: symbol): term; 
  VAR i: INTEGER;
BEGIN
  IF nvars = MAXARITY THEN panic('too many variables') END;
  i := 1; vartable[nvars+1] := name;  { sentinel }
  WHILE name # vartable[i] DO INC(i) END;
  IF i = nvars+1 THEN INC(nvars) END;
  RETURN MakeRef(i)
END VarRep;

{ |ShowAnswer| -- display answer and get response }
PROCEDURE ShowAnswer(bindings: frame): BOOLEAN; 
  VAR i: INTEGER; ch, ch2: CHAR;
BEGIN
  IF nvars = 0 THEN RETURN TRUE
  ELSE
    FOR i := 1 TO nvars DO
      Out.Ln;
      WriteString(s_name(vartable[i])); Out.String(' = ');
      PrintTerm(f_local(bindings, i), NULL, EQPRIO-1)
    END;
    IF ~interacting THEN
      Out.Ln; RETURN FALSE
    ELSE
      Out.String(' ? ');
      ch := GetChar(); ch2 := ch; 
      WHILE ch2 # ENDLINE DO ch2 := GetChar() END;
      RETURN (ch = '.') 
    END
  END
END ShowAnswer;

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
PROCEDURE Eat(expected: INTEGER); 
BEGIN
  IF token = expected THEN
    IF token # DOT THEN Scan() END
  ELSIF ~errflag THEN
    ShowError();
    Out.String('expected '); PrintToken(expected);
    Out.String(', found '); PrintToken(token); Out.Ln;
    Recover()
  END
END Eat;

{ |ParseCompound| -- parse a compound term }
PROCEDURE ParseCompound(): term; 
  VAR fun: symbol; arg: argbuf; n: INTEGER;
BEGIN
  fun := tokval; n := 0; Eat(IDENT);
  IF token = LPAR THEN
    Eat(LPAR); n := 1; arg[1] := ParseTerm();
    WHILE token = COMMA DO
      Eat(COMMA); INC(n); arg[n] := ParseTerm()
    END;
    Eat(RPAR)
  END;
  IF s_arity(fun) = -1 THEN
    s_arity(fun) := n
  ELSIF s_arity(fun) # n THEN
    syntax_error('wrong number of args')
  END;
  RETURN MakeCompound(fun, arg)
END ParseCompound;

{ |ParsePrimary| -- parse a primary }
PROCEDURE ParsePrimary(): term; 
  VAR t: term;
BEGIN
  IF token = IDENT THEN t := ParseCompound()
  ELSIF token = VARIABLE THEN
    t := VarRep(tokval); Eat(VARIABLE)
  ELSIF token = NUMBER THEN
    t := MakeInt(tokival); Eat(NUMBER)
  ELSIF token = CHCON THEN
    t := MakeChar(CHR(tokival)); Eat(CHCON)
  ELSIF token = STRCON THEN
    t := MakeString(toksval); Eat(STRCON)
  ELSIF token = LPAR THEN
    Eat(LPAR); t := ParseTerm(); Eat(RPAR)
  ELSIF token = LANGLE THEN
    t := ParseNode()
  ELSE
    syntax_error('expected a term'); t := NULL
  END;
  RETURN t
END ParsePrimary;

{ |ParseNode| -- parse an optree node }
PROCEDURE ParseNode(): term; 
  VAR tag, kids: term;
BEGIN
  Eat(LANGLE);
  tag := ParseTerm();
  kids := ParseKids();
  Eat(RANGLE);
  RETURN MakeNode(node, tag, kids)
END ParseNode;

{ |ParseKids| -- parse children of an optree node }
PROCEDURE ParseKids(): term; 
  VAR head, tail: term;
BEGIN
  IF token # COMMA THEN
    RETURN MakeNode(nilsym, NULL, NULL)
  ELSE
    Eat(COMMA);
    head := ParseTerm();
    tail := ParseKids();
    RETURN MakeNode(cons, head, tail)
  END
END ParseKids;

{ |ParseFactor| -- parse a factor }
PROCEDURE ParseFactor(): term; 
  VAR t: term;
BEGIN
  t := ParsePrimary();
  IF token # COLON THEN
    RETURN t
  ELSE
    Eat(COLON);
    RETURN MakeNode(cons, t, ParseFactor())
  END
END ParseFactor;

{ |ParseTerm| -- parse a term }
PROCEDURE ParseTerm(): term; 
  VAR t: term;
 BEGIN
  t := ParseFactor();
  IF token # EQUAL THEN
    RETURN t
  ELSE
    Eat(EQUAL);
    RETURN MakeNode(eqsym, t, ParseFactor())
  END
END ParseTerm;

{ |CheckAtom| -- check that a literal is a compound term }
PROCEDURE CheckAtom(a: term); 
BEGIN
  IF t_kind(a) # FUNC THEN
    syntax_error('literal must be a compound term')
  END
END CheckAtom;

{ |ParseClause| -- parse a clause }
PROCEDURE ParseClause(isgoal: BOOLEAN): clause; 
  VAR head, t: term; 
    body: argbuf; 
    n: INTEGER;
    minus, more: BOOLEAN;
BEGIN
  IF isgoal THEN 
    head := NULL
  ELSE
    IF token = HASH THEN
      Eat(HASH); head := NULL
    ELSE
      head := ParseTerm();
      CheckAtom(head)
    END;
    Eat(ARROW)
  END;

  n := 0;
  IF token # DOT THEN
    more := TRUE;
    WHILE more DO
      n := n+1; minus := FALSE;
      IF token = NEGATE THEN
	Eat(NEGATE); minus := TRUE 
      END;
      t := ParseTerm(); CheckAtom(t);
      IF minus THEN 
	body[n] := MakeNode(notsym, t, NULL)
      ELSE 
        body[n] := t
      END;
      IF token = COMMA THEN Eat(COMMA) ELSE more := FALSE END
    END
  END;
  Eat(DOT);

  IF errflag THEN 
    RETURN NULL
  ELSE 
    RETURN MakeClause(nvars, head, body, n)
  END
END ParseClause;

{ |ReadClause| -- read a clause from |infile| }
PROCEDURE ReadClause(): clause; 
  VAR c: clause;
BEGIN
  REPEAT
    hp := hmark; nvars := 0; errflag := FALSE;
    IF interacting THEN
      Out.Ln; Out.String('# :- ');
    END;
    Scan();
    IF token = EOFTOK THEN 
      c := NULL
    ELSE 
      c := ParseClause(interacting)
    END
  UNTIL (~errflag) OR (token = EOFTOK);
  RETURN c
END ReadClause;

{S Trail }

{ The trail stack records assignments made to variables, so that
  they can be undone on backtracking.  It is a linked list of nodes
  with a |t_kind| of |UNDO| allocated from the global stack.  The
  variables for which bindings are actually kept in the trail are the
  `critical' ones that will not be destroyed on backtracking. }

TYPE trail = ptr;
{ Nodes on the trail share the |t_tag| and |t_shift| fields of
  other nodes on the global stack, plus: }
define(x_reset, mem[$1+2])  { variable to reset }
define(x_next, mem[$1+3])  { next trail entry }
define(TRAIL_SIZE, 4)

VAR trhead: trail;  { start of the trail }

{ |critical| -- test if a variable will survive backtracking }
define(critical, (($1 < choice) OR ($1 >= f_glotop(choice))))

{ |Save| -- add a variable to the trail if it is critical }
PROCEDURE Save(v: term); 
  VAR p: trail;
BEGIN
  IF critical(v) THEN
    p := GloAlloc(UNDO, TRAIL_SIZE);
    x_reset(p) := v; x_next(p) := trhead; trhead := p
  END
END Save;

{ |Restore| -- undo bindings back to previous state }
PROCEDURE Restore(); 
  VAR v: term;
BEGIN
  WHILE (trhead # f_trail(choice)) DO
    v := x_reset(trhead);
    IF v # NULL THEN t_val(v) := NULL END;
    trhead := x_next(trhead)
  END
END Restore;

{ |Commit| -- blank out trail entries not needed after cut }
PROCEDURE Commit(); 
  VAR p: trail;
BEGIN
  p := trhead;
  WHILE (p # NULL) && (p < f_glotop(choice)) DO
    IF (x_reset(p) # NULL) && ~critical(x_reset(p)) THEN
      x_reset(p) := NULL
    END;
    p := x_next(p)
  END
END Commit;

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
PROCEDURE GloCopy(t: term; e: frame): term; 
  VAR tt: term; i, n: INTEGER;
BEGIN
  t := Deref(t, e);
  IF is_glob(t) THEN
    RETURN t
  ELSE
    CASE t_kind(t) OF
      FUNC:
	n := s_arity(t_func(t));
	IF is_heap(t) && (n = 0) THEN 
	  RETURN t
	ELSE
	  tt := GloAlloc(FUNC, TERM_SIZE+n);
	  t_func(tt) := t_func(t);
	  FOR i := 1 TO n DO
	    t_arg(tt, i) := GloCopy(t_arg(t, i), e)
	  END;
	  RETURN tt
	END
    | CELL:
        tt := GloAlloc(CELL, TERM_SIZE);
        t_val(tt) := NULL;
	Save(t); t_val(t) := tt;
        RETURN tt
    ELSE
      RETURN t
    END
  END
END GloCopy;

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
define(lifetime, ($1 * (2 * ORD(is_glob($1)) - 1)))

{ |Share| -- bind two variables together }
PROCEDURE Share(v1, v2: term); 
BEGIN
  IF lifetime(v1) <= lifetime(v2) THEN
    Save(v1); t_val(v1) := v2
  ELSE
    Save(v2); t_val(v2) := v1 
  END
END Share;

{ |Unify| -- find and apply unifier for two terms }
PROCEDURE Unify(t1: term; e1: frame; t2: term; e2: frame): BOOLEAN; 
  VAR i: INTEGER; match: BOOLEAN;
BEGIN
  t1 := Deref(t1, e1); t2 := Deref(t2, e2);
  IF t1 = t2 THEN  { Includes unifying a var with itself }
    RETURN TRUE
  ELSIF (t_kind(t1) = CELL) && (t_kind(t2) = CELL) THEN
    Share(t1, t2); RETURN TRUE
  ELSIF t_kind(t1) = CELL THEN
    Save(t1); t_val(t1) := GloCopy(t2, e2); RETURN TRUE
  ELSIF t_kind(t2) = CELL THEN
    Save(t2); t_val(t2) := GloCopy(t1, e1); RETURN TRUE
  ELSIF t_kind(t1) # t_kind(t2) THEN
    RETURN FALSE
  ELSE
    CASE t_kind(t1) OF
      FUNC:
        IF (t_func(t1) # t_func(t2)) THEN
          RETURN FALSE
        ELSE
          i := 1; match := TRUE;
          WHILE match && (i <= s_arity(t_func(t1))) DO
            match := Unify(t_arg(t1, i), e1, t_arg(t2, i), e2);
            INC(i)
          END;
          RETURN match
        END
    | INT:
        RETURN (t_ival(t1) = t_ival(t2))
    | CHRCTR:
        RETURN (t_cval(t1) = t_cval(t2))
    ELSE
      bad_tag('Unify', t_kind(t1))
    END
  END
END Unify;

{ |Key| -- unification key of a term }
PROCEDURE Key(t: term; e: frame): INTEGER; 
  VAR t0: term;
BEGIN
  { The argument |t| must be a direct pointer to a compound term.
    The value returned is |key(t)|: if |t1| and |t2| are unifiable,
    then |key(t1) = 0| or |key(t2) = 0| or |key(t1) = key(t2)|. }

  IF t = NULL THEN panic('Key') END;
  IF t_kind(t) # FUNC THEN bad_tag('Key1', t_kind(t)) END;

  IF s_arity(t_func(t)) = 0 THEN
    RETURN 0
  ELSE
    t0 := Deref(t_arg(t, 1), e);
    CASE t_kind(t0) OF
        FUNC:      RETURN t_func(t0)
      | INT:       RETURN t_ival(t0) + 1
      | CHRCTR:    RETURN t_cval(t0) + 1
    ELSE
      RETURN 0
    END
  END
END Key;

{ |Search| -- find the first clause that might match }
PROCEDURE Search(t: term; e: frame; p: clause): clause; 
  VAR k: INTEGER;
BEGIN
  k := Key(t, e);
  IF k # 0 THEN
    WHILE (p # NULL) && (c_key(p) # 0) && (c_key(p) # k) DO
      p := c_next(p)
    END
  END;
  RETURN p
END Search;

{S Interpreter }

{ The main control of the interpreter uses a depth-first search
  procedure with an explicit stack of activation records.  It
  includes the tail-recursion optimization and an indexing scheme
  that uses the hash codes computed by |Key|. }

VAR ok: BOOLEAN;  { whether execution succeeded }

define(debug_point, 
  IF dflag THEN 
    Out.String($1); Out.String(': '); 
    PrintTerm($2, $3, MAXPRIO); Out.Ln
  END)

{ |PushFrame| -- create a new local stack frame }
PROCEDURE PushFrame(nvars: INTEGER; retry: clause); 
  VAR f: frame; i: INTEGER;
BEGIN
  f := LocAlloc(frame_size(nvars));
  f_goal(f) := current; f_parent(f) := goalframe;
  f_retry(f) := retry; f_choice(f) := choice;
  f_glotop(f) := gsp; f_trail(f) := trhead;
  f_nvars(f) := nvars;
  FOR i := 1 TO nvars DO
    t_tag(f_local(f, i)) := make_tag(CELL, TERM_SIZE);
    t_val(f_local(f, i)) := NULL
  END;
  goalframe := f;
  IF retry # NULL THEN choice := goalframe END
END PushFrame;

{ Tail recursion can be used only under rather stringent conditions:
  the goal literal must be the last one in the body of the calling
  clause, both the calling clause and the called clause must be
  determinate, and the calling clause must not be the original goal
  (lest the answer variables be lost).  The macro |tro_test(p)|
  checks that these conditions are satisfied, where |p| is the
  untried part of the procedure for the current goal literal. }

{ |tro_test| -- test if a resolution step can use TRO }
define(tro_test, (g_first(g_rest(current)) = NULL) && (choice < goalframe)
    && ($1 = NULL) && (goalframe # base))

{ If the |tro_test| macro returns TRUE, then it is safe to discard
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
PROCEDURE TroStep(); 
  VAR temp: frame; oldsize, newsize, i: INTEGER;
BEGIN
  IF dflag THEN Out.String('(TRO)'); Out.Ln END;

  oldsize := frame_size(f_nvars(goalframe)); { size of old frame }
  newsize := frame_size(c_nvars(prok)); { size of new frame }
  temp := LocAlloc(newsize);
  temp := goalframe + newsize; { copy old frame here }

  { Copy the old frame: in reverse order in case of overlap }
  FOR i := 1 TO oldsize DO 
    mem[temp+oldsize-i] := mem[goalframe+oldsize-i]
  END;

  { Adjust internal pointers in the copy }
  FOR i := 1 TO f_nvars(goalframe) DO
    IF (t_kind(f_local(temp, i)) = CELL)
        && (t_val(f_local(temp, i)) # NULL)
        && (goalframe <= t_val(f_local(temp, i)))
        && (t_val(f_local(temp, i)) < goalframe + oldsize) THEN
      t_val(f_local(temp, i)) := t_val(f_local(temp, i)) + newsize
    END
  END;

  { Overwrite the old frame with the new one }
  f_nvars(goalframe) := c_nvars(prok);
  FOR i := 1 TO f_nvars(goalframe) DO
    t_tag(f_local(goalframe, i)) := make_tag(CELL, TERM_SIZE);
    t_val(f_local(goalframe, i)) := NULL
  END;

  { Perform the resolution step }
  ok := Unify(call, temp, c_head(prok), goalframe);
  current := c_rhs(prok);
  lsp := temp-1
END TroStep;

{ The |Step| procedure carries out a single resolution step.
  Built-in relations are treated as a special case; so are
  resolution steps that can use the tail-recursion optimization.
  Otherwise, we allocate a frame for the first clause for the
  current goal literal, unify the clause head with the literal, and adopt
  the clause body as the new goal.  The step can fail (and |Step|
  returns |FALSE|) if there are no clauses to try, or if the first
  clause fails to match. }

{ |Step| -- perform a resolution step }
PROCEDURE Step(); 
  VAR retry: clause;
BEGIN
  IF s_action(t_func(call)) # 0 THEN
    ok := DoBuiltin(s_action(t_func(call)))
  ELSIF prok = NULL THEN
    ok := FALSE
  ELSE
    retry := Search(call, goalframe, c_next(prok));
    IF tro_test(retry) THEN
      TroStep()
    ELSE
      PushFrame(c_nvars(prok), retry);
      ok := Unify(call, f_parent(goalframe), c_head(prok), goalframe);
      current := c_rhs(prok);
    END
  END
END Step;

{ The |Unwind| procedure returns from completed clauses until it
  finds one where there is still work to do, or it finds that the
  original goal is completed.  At this point, completed frames are
  discarded if they cannot take part in future backtracking. }

{ |Unwind| -- return from completed clauses }
PROCEDURE Unwind(); 
BEGIN
  WHILE (g_first(current) = NULL) && (goalframe # base) DO
    debug_point('Exit', g_first(f_goal(goalframe)), f_parent(goalframe));
    current := g_rest(f_goal(goalframe));
    IF goalframe > choice THEN lsp := goalframe-1 END;
    goalframe := f_parent(goalframe)
  END
END Unwind;

{ The |Backtrack| procedure undoes all the work that has been done
  since the last non-deterministic choice (indicated by the |choice|
  register).  The trail shows what assignments must be undone, and
  the stacks are returned to the state they were in when the choice
  was made.  The |prok| register is set from the |f_retry| field of
  the |choice| frame: this is the list of clauses for that goal that
  remain to be tried }

{ |Backtrack| -- roll back to the last choice-point }
PROCEDURE Backtrack(); 
BEGIN
  Restore();
  current := f_goal(choice); goalframe := f_parent(choice);
  call := Deref(g_first(current), goalframe);
  prok := f_retry(choice); gsp := f_glotop(choice);
  lsp := choice-1; choice := f_choice(choice);
  debug_point('Redo', call, goalframe);
END Backtrack;

{ |Resume| is called with |flag = TRUE| when the interpreter starts to
  execute a goal; it either returns with |ok = TRUE| when the goal
  succeeds, or returns with |ok = FALSE| when it has completely
  failed.  After |Resume| has returned |TRUE|, it can be called
  again with |ok = FALSE| to find another solution; in this case,
  the first action is to backtrack to the most recent choice-point. }

{ |Resume| -- continue execution }
PROCEDURE Resume(flag: BOOLEAN); 
BEGIN
  ok := flag;
  WHILE run DO
    IF ok THEN
      IF g_first(current) = NULL THEN RETURN END;
      call := Deref(g_first(current), goalframe);
      debug_point('Call', call, goalframe);
      IF (s_prok(t_func(call)) = NULL)
	  && (s_action(t_func(call)) = 0) THEN
	exec_error('call to undefined relation ');
	WriteString(s_name(t_func(call)));
	RETURN
      END;
      prok := Search(call, goalframe, s_prok(t_func(call)))
    ELSE
      IF choice <= base THEN RETURN END;
      Backtrack()
    END;
    Step();
    IF ok THEN Unwind() END;
    IF gsp - lsp <= GCLOW THEN Collect() END
  END;
END Resume;

{ |Execute| -- solve a goal by SLD-resolution }
PROCEDURE Execute(g: clause); 
BEGIN
  lsp := hp; gsp := MEMSIZE+1;
  current := NULL; goalframe := NULL; choice := NULL; trhead := NULL;
  PushFrame(c_nvars(g), NULL);
  choice := goalframe; base := goalframe; current := c_rhs(g);
  run := TRUE;
  Resume(TRUE);
  IF ~run THEN RETURN END;
  WHILE ok DO
    IF ShowAnswer(base) THEN
      Out.Ln; Out.String('yes'); RETURN
    END;
    Resume(FALSE);
    IF ~run THEN RETURN END;
  END;
  Out.Ln; Out.String('no')
END Execute;

{S Built-in relations }

{ Each built-in relation is a parameterless boolean-valued
  function: it finds its arguments from the call in |call|, carries
  out whatever side-effect is desired, and returns |TRUE| exactly if
  the call succeeds.

  Two routines help in defining built-in relations: |GetArgs|
  dereferences the argument of the literal |call| and puts them in
  the global array |av|; and |NewInt| makes a new integer node on 
  the global stack. }

VAR
  av: argbuf;  { |GetArgs| puts arguments here }
  callbody: ptr;  { dummy clause body used by |call/1| }

{ |GetArgs| -- set up |av| array }
PROCEDURE GetArgs(); 
  VAR i: INTEGER;
BEGIN
  FOR i := 1 TO s_arity(t_func(call)) DO
    av[i] := Deref(t_arg(call, i), goalframe)
  END
END GetArgs;

{ A couple of macros that abbreviate accesses to the |av| array: }
define(a_kind, (t_kind(av[$1]) = $2))
define(a_ival, t_ival(av[$1]))

PROCEDURE NewInt(n: INTEGER): term; 
  VAR t: term;
BEGIN
  t := GloAlloc(INT, TERM_SIZE);
  t_ival(t) := n;
  RETURN t
END NewInt;

{ |DoCut| -- built-in relation !/0 }
PROCEDURE DoCut(): BOOLEAN; 
BEGIN
  choice := f_choice(goalframe);
  lsp := goalframe + frame_size(f_nvars(goalframe)) - 1;
  Commit();
  current := g_rest(current);
  RETURN TRUE
END DoCut;

{ |DoCall| -- built-in relation |call/1| }
PROCEDURE DoCall(): BOOLEAN; 
BEGIN
  GetArgs();
  IF ~a_kind(1, FUNC) THEN
    exec_error('bad argument to call/1');
    RETURN FALSE
  ELSE
    PushFrame(1, NULL);
    t_val(f_local(goalframe, 1)) :=
      GloCopy(av[1], f_parent(goalframe));
    current := callbody;
    RETURN TRUE
  END
END DoCall;

{ |DoNot| -- built-in relation |not/1| }
PROCEDURE DoNot(): BOOLEAN; 
  VAR savebase: frame;
BEGIN
  GetArgs();
  IF ~a_kind(1, FUNC) THEN
    exec_error('bad argument to call/1');
    RETURN FALSE
  ELSE
    PushFrame(1, NULL);
    savebase := base; base := goalframe; choice := goalframe;
    t_val(f_local(goalframe, 1)) :=
      GloCopy(av[1], f_parent(goalframe));
    current := callbody;
    Resume(TRUE);
    choice := f_choice(base); goalframe := f_parent(base);
    IF ~ok THEN
      current := g_rest(f_goal(base));
      RETURN TRUE
    ELSE
      Commit();
      RETURN FALSE
    END;
    lsp := base-1; base := savebase
  END
END DoNot;

{ Procedures |DoPlus| and |DoTimes| implement the |plus/3| and
  |times/3| relations: they both involve a case analysis of which
  arguments are known, followed by a call to |Unify| to unify the
  remaining argument with the result.  The |times/3| relation fails
  on divide-by-zero, even in the case |times(X, 0, 0)|, which
  actually has infinitely many solutions. }

{ |DoPlus| -- built-in relation |plus/3| }
PROCEDURE DoPlus(): BOOLEAN; 
  VAR result: BOOLEAN;
BEGIN
  GetArgs();
  result := FALSE;
  IF a_kind(1, INT) && a_kind(2, INT) THEN
    result := Unify(av[3], goalframe, NewInt(a_ival(1) + a_ival(2)), NULL)
  ELSIF a_kind(1, INT) && a_kind(3, INT) THEN
    IF a_ival(1) <= a_ival(3) THEN
      result := Unify(av[2], goalframe, 
		      NewInt(a_ival(3) - a_ival(1)), NULL)
    END
  ELSIF a_kind(2, INT) && a_kind(3, INT) THEN
    IF a_ival(2) <= a_ival(3) THEN
      result := Unify(av[1], goalframe, NewInt(a_ival(3) - a_ival(2)), NULL)
    END
  ELSE
    exec_error('plus/3 needs at least two integers')
  END;
  current := g_rest(current);
  RETURN result
END DoPlus;

{ |DoTimes| -- built-in relation |times/3| }
PROCEDURE DoTimes(): BOOLEAN; 
  VAR result: BOOLEAN;
BEGIN
  GetArgs();
  result := FALSE;
  IF a_kind(1, INT) && a_kind(2, INT) THEN
    result := Unify(av[3], goalframe, 
		    NewInt(t_ival(av[1]) * t_ival(av[2])), NULL)
  ELSIF a_kind(1, INT) && a_kind(3, INT) THEN
    IF a_ival(1) # 0 THEN
      IF a_ival(3) MOD a_ival(1) = 0 THEN
        result := Unify(av[2], goalframe, 
		        NewInt(a_ival(3) DIV a_ival(1)), NULL)
      END
    END
  ELSIF a_kind(2, INT) && a_kind(3, INT) THEN
    IF a_ival(2) # 0 THEN
      IF a_ival(3) MOD a_ival(2) = 0 THEN
        result := Unify(av[1], goalframe, 
			NewInt(a_ival(3) DIV a_ival(2)), NULL)
      END
    END
  ELSE
    exec_error('times/3 needs at least two integers')
  END;
  current := g_rest(current);
  RETURN result
END DoTimes;

{ |DoEqual| -- built-in relation |=/2| }
PROCEDURE DoEqual(): BOOLEAN; 
BEGIN
  GetArgs();
  current := g_rest(current);
  RETURN Unify(av[1], goalframe, av[2], goalframe)
END DoEqual;

{ |DoInteger| -- built-in relation |integer/1| }
PROCEDURE DoInteger(): BOOLEAN; 
BEGIN
  GetArgs();
  current := g_rest(current);
  RETURN a_kind(1, INT)
END DoInteger;

{ |DoChar| -- built-in relation |char/1| }
PROCEDURE DoChar(): BOOLEAN; 
BEGIN
  GetArgs();
  current := g_rest(current);
  RETURN a_kind(1, CHRCTR)
END DoChar;

{ |DoPrint| -- built-in relation |print/1| }
PROCEDURE DoPrint(): BOOLEAN; 
BEGIN
  GetArgs();
  PrintTerm(av[1], goalframe, MAXPRIO);
  current := g_rest(current);
  RETURN TRUE
END DoPrint;

{ |DoNl| -- built-in relation |nl/0| }
PROCEDURE DoNl(): BOOLEAN; 
BEGIN
  Out.Ln;
  current := g_rest(current);
  RETURN TRUE
END DoNl;

{ |DoBuiltin| -- switch for built-in relations }
PROCEDURE DoBuiltin(action: INTEGER): BOOLEAN; 
BEGIN
  CASE action OF
    CUT:      RETURN DoCut()
  | CALL:     RETURN DoCall()
  | PLUS:     RETURN DoPlus()
  | TIMES:    RETURN DoTimes()
  | ISINT:    RETURN DoInteger()
  | ISCHAR:   RETURN DoChar()
  | NAFF:     RETURN DoNot()
  | EQUALITY: RETURN DoEqual()
  | FAIL:     RETURN FALSE
  | PRINT:    RETURN DoPrint()
  | NL:	      RETURN DoNl()
  ELSE
    bad_tag('DoBuiltin', action)
  END
END DoBuiltin;

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

VAR shift: INTEGER;  { amount global stack will shift }

{ |Visit| -- recursively mark a term and all its sub-terms }
PROCEDURE Visit(t: term); 
  VAR i, n: INTEGER;
BEGIN
  { We reduce the depth of recursion when marking long lists by
    treating the last argument of a function iteratively, making
    recursive calls only for the other arguments. }
  WHILE t # NULL DO
    IF ~is_glob(t) OR marked(t) THEN RETURN END;
    add_mark(t);
    CASE t_kind(t) OF
      FUNC:
	n := s_arity(t_func(t));
	IF n = 0 THEN RETURN END;
        FOR i := 1 TO n-1 DO Visit(t_arg(t, i)) END;
        t := t_arg(t, n)
    | CELL:
        t := t_val(t)
    ELSE
      RETURN
    END
  END
END Visit;

{ |MarkStack| -- mark from each frame on the local stack }
PROCEDURE MarkStack(); 
  VAR f: frame; i: INTEGER;
BEGIN
  f := hp+1;
  WHILE f <= lsp DO
    FOR i := 1 TO f_nvars(f) DO
      IF t_kind(f_local(f, i)) = CELL THEN
	Visit(t_val(f_local(f, i)))
      END
    END;
    f := f + frame_size(f_nvars(f))
  END
END MarkStack;

{ |CullTrail| -- delete an initial segment of unwanted trail }
PROCEDURE CullTrail(VAR p: trail); 
BEGIN
  WHILE p # NULL DO
    IF x_reset(p) # NULL THEN
      IF ~is_glob(x_reset(p)) OR marked(x_reset(p)) THEN
	RETURN
      END
    END;
    p := x_next(p)
  END
END CullTrail;

{ |MarkTrail| -- remove dead trail nodes, mark the rest. }
PROCEDURE MarkTrail(); 
  VAR p: trail;
BEGIN
  CullTrail(trhead); p := trhead;
  WHILE p # NULL DO
    add_mark(p); CullTrail(x_next(p)); p := x_next(p) 
  END
END MarkTrail;

{ |Relocate| -- compute shifts }
PROCEDURE Relocate(); 
  VAR p: ptr; step: INTEGER;
BEGIN
  shift := 0; p := gsp;
  WHILE p <= MEMSIZE DO
    step := t_size(p); t_shift(p) := shift;
    IF ~marked(p) THEN
      shift := shift + step
    END;
    p := p + step
  END
END Relocate;

{ |AdjustPointer| -- update a pointer}
PROCEDURE AdjustPointer(VAR p: term); 
BEGIN
  IF (p # NULL) && is_glob(p) THEN
    IF ~marked(p) THEN
      panic('adjusting pointer to unmarked block')
    END;
    p := p + shift - t_shift(p)
  END
END AdjustPointer;

{ |AdjustStack| -- adjust pointers in local stack }
PROCEDURE AdjustStack(); 
  VAR f: frame; i: INTEGER; q: ptr;
BEGIN
  f := hp+1;
  WHILE f <= lsp DO
    q := f_glotop(f);
    WHILE (q <= MEMSIZE) && ~marked(q) DO
      q := q + t_size(q)
    END;
    IF q <= MEMSIZE THEN AdjustPointer(q) END;
    f_glotop(f) := q;

    q := f_trail(f);
    WHILE (q # NULL) && ~marked(q) DO
      q := x_next(q)
    END;
    AdjustPointer(q);
    f_trail(f) := q;

    FOR i := 1 TO f_nvars(f) DO
      IF t_kind(f_local(f, i)) = CELL THEN
	AdjustPointer(t_val(f_local(f, i)))
      END
    END;
    f := f + frame_size(f_nvars(f));
  END
END AdjustStack;

{ |AdjustInternal| -- update internal pointers }
PROCEDURE AdjustInternal(); 
  VAR p, i: INTEGER;
BEGIN
  p := gsp;
  WHILE p <= MEMSIZE DO
    IF marked(p) THEN
      CASE t_kind(p) OF
        FUNC:
          FOR i := 1 TO s_arity(t_func(p)) DO
	    AdjustPointer(t_arg(p, i))
	  END
      | CELL:
          AdjustPointer(t_val(p))
      | UNDO:
	  AdjustPointer(x_reset(p));
	  AdjustPointer(x_next(p))
      ELSE
	{ skip }
      END
    END;
    p := p + t_size(p)
  END
END AdjustInternal;

{ |Compact| -- compact marked blocks and un-mark }
PROCEDURE Compact(); 
  VAR p, q, step, i: INTEGER;
BEGIN
  p := gsp; q := gsp;
  WHILE p <= MEMSIZE DO
    step := t_size(p);
    IF marked(p) THEN
      rem_mark(p);
      FOR i := 0 TO step-1 DO mem[q+i] := mem[p+i] END;
      q := q + step
    END;
    p := p + step
  END;
  gsp := gsp+shift;
  FOR i := 0 TO MEMSIZE-gsp DO mem[MEMSIZE-i] := mem[MEMSIZE-i-shift] END
END Compact;

{ |Collect| -- collect garbage }
PROCEDURE Collect(); 
BEGIN
  Out.String('[gc');

  { Phase 1: marking }
  Visit(call); MarkStack(); MarkTrail();

  { Phase 2: compute new locations }
  Relocate();

  { Phase 3: adjust pointers }
  AdjustPointer(call); AdjustPointer(trhead);
  AdjustStack(); AdjustInternal();

  { Phase 4: compact }
  Compact();

  Out.Char(']');
  IF gsp - lsp <= GCHIGH THEN exec_error('out of memory space') END
END Collect;

{S Main program }

{ |Initialize| -- initialize everything }
PROCEDURE Initialize(); 
  VAR i: INTEGER; p: term;
BEGIN
  dflag := FALSE; errcount := 0;
  pbchar := ENDFILE; charptr := 0;
  hp := 0; InitSymbols();

  { Set up the |refnode| array }
  FOR i := 1 TO MAXARITY DO
    p := HeapAlloc(TERM_SIZE);
    t_tag(p) := make_tag(REF, TERM_SIZE);
    t_index(p) := i; refnode[i] := p
  END;

  { The dummy clause $\it call(\sci p) \IF p$ is used by |call/1|. }
  callbody := HeapAlloc(2);
  g_first(callbody) := MakeRef(1);
  g_first(g_rest(callbody)) := NULL
END Initialize;

{ |ReadFile| -- read and process clauses from an open file }
PROCEDURE ReadFile(); 
  VAR c: clause;
    ch: CHAR;
BEGIN
  lineno := 1;
  REPEAT
    hmark := hp;
    c := ReadClause();
    IF c # NULL THEN
      IF dflag THEN PrintClause(c) END;	
      IF c_head(c) # NULL THEN
        AddClause(c)
      ELSE
        IF interacting THEN 
	  pbchar := ENDFILE; 
	  REPEAT ch := GetChar() UNTIL ch = ENDLINE
	END;
        Execute(c);
	Out.Ln;
	hp := hmark
      END
    END
  UNTIL c = NULL
END ReadFile;

ifdef(turbo, {$I pplib.inc})

{ |ReadProgram| -- read files listed on command line }
PROCEDURE ReadProgram(); 
  VAR i0, i: INTEGER;
    arg: tempstring;
BEGIN
  i0 := 1;
  IF Args.argc > 1 THEN
    Args.GetArg(1, arg);
    IF arg = '-d' THEN
      dflag := TRUE;
      INC(i0)
    END
  END;
  FOR i := i0 TO Args.argc-1 DO
    Args.GetArg(i, arg);
    filename := SaveString(arg);
    IF ~OpenIn(arg) THEN
      Out.String('Cannot read '); WriteString(filename); Out.Ln;
      HALT(2)
    END;
    Out.String('Reading '); WriteString(filename); Out.Ln;
    ReadFile();
    CloseIn();
    IF errcount > 0 THEN HALT(2) END
  END
END ReadProgram;

BEGIN  { main program }
  curin := Files.stdin;
  Out.String('Welcome to picoProlog'); Out.Ln;
  Initialize();
  interacting := FALSE; ReadProgram();
  interacting := TRUE; lineno := 1; ReadFile();
  Out.Ln;
END obProlog.
