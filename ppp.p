{ ppp -- trivial macro processor }

program ppp(input, output);

const
  ARGMAX = 128;           { Max no. of args }
  DEFMAX = 512;           { Max no. of macros }
  STRMAX = 1024;          { Max size of string }
  BUFMAX = 8192;          { Size of pushback, arg, def buffers }
  HASHSIZE = 127;         { Size of hash table }

type
  tempstring = array [1..STRMAX] of char;
  charbuf = array [1..BUFMAX] of char;

var
  ndefs: integer;
  deftab: array [1..DEFMAX] of 
    record name, body, next: integer end;
  hashtab: array [1..HASHSIZE] of integer;
  defhwm: integer;
  defbuf: charbuf;

  nargs: integer;
  arghwm: integer;
  arg: array [1..ARGMAX] of integer;
  argbuf: charbuf;

  pbp: integer;
  pshbuf: charbuf;

  DEFINE, IFDEF: integer;
  ENDSTR, TAB, ENDLINE, ENDFILE: char;
  emptystr: tempstring;

{ isletter -- test if character is a letter }
function isletter(c: char): boolean;
begin
  isletter := (c >= 'A') and (c <= 'Z') 
    or (c >= 'a') and (c <= 'z') or (c = '_')
end;

{ isalphanum -- test if character is alphanumeric }
function isalphanum(c: char): boolean;
begin
  isalphanum := isletter(c) or (c >= '0') and (c <= '9')
end;

{ getchar -- read one character }
function getchar: char;
  var ch: char;
begin
  if eof then
    getchar := ENDFILE
  else if eoln then begin
    readln;
    getchar := ENDLINE
  end
  else begin
    read(ch);
    if ch = '&' then read(ch);
    getchar := ch
  end
end;

{ outchar -- write one character }
procedure outchar(ch: char);
begin
  if ch = ENDLINE then
    writeln
  else if ch <> ENDFILE then
    write(ch)
end;

{ putstring -- write a string }
procedure putstring(var s: tempstring);
  var i: integer;
begin
  i := 1;
  while s[i] <> ENDSTR do begin
    write(s[i]);
    i := i+1
  end
end;    

{ length -- length of a string }
function length(var s: tempstring): integer;
  var i: integer;
begin
  i := 0;
  while s[i+1] <> ENDSTR do i := i+1;
  length := i
end;

{ eqstr -- string equality test }
function eqstr(var s, t: tempstring): boolean;
  var i: integer;
begin
  i := 1;
  while (s[i] <> ENDSTR) and (s[i] = t[i]) do i := i+1;
  eqstr := (s[i] = t[i])
end;

{ loadstr -- copy a string out of a buffer }
procedure loadstr(var s: tempstring; var b: charbuf; k: integer);
  var i: integer;
begin
  i := 1;
  repeat
    s[i] := b[k];
    i := i+1; k := k+1
  until (s[i-1] = ENDSTR);
end;

{ savestr -- copy a string into a buffer }
procedure savestr(var s: tempstring; var b: charbuf; k: integer);
  var i: integer;
begin
  i := 1;
  repeat
    b[k] := s[i];
    i := i+1; k := k+1
  until (b[k-1] = ENDSTR);
end;

{ pbchar -- push back a character }
procedure pbchar(ch: char);
begin
  if pbp >= BUFMAX then begin
    writeln('Too many chars pushed back');
    halt
  end;
  pbp := pbp+1;
  pshbuf[pbp] := ch
end;

{ pbstring -- push back a string }
procedure pbstring(var s: tempstring);
  var i: integer;
begin
  for i := length(s) downto 1 do pbchar(s[i])
end;            

{ getpbc -- get pushed-back character }
function getpbc: char;
begin
  if pbp = 0 then
    getpbc := getchar
  else begin
    getpbc := pshbuf[pbp];
    pbp := pbp-1
  end
end;

{ skipws -- skip over white space }
procedure skipws;
  var ch: char;
begin
  repeat
    ch := getpbc
  until (ch <> ' ') and (ch <> TAB) and (ch <> ENDLINE);
  pbchar(ch)
end;

{ hash -- hash function }
function hash(var s: tempstring): integer;
  var h, i: integer;
begin
  h := 0;
  for i := 1 to length(s) do
    h := (5 * h + ord(s[i])) mod HASHSIZE;
  hash := h+1
end;

{ lookup -- look up a name in the hash table }
function lookup(var key: tempstring): integer;
  var
    p: integer;
    found: boolean;
    name: tempstring;
begin
  p := hashtab[hash(key)];
  found := false;
  while (p <> 0) and (not found) do begin
    loadstr(name, defbuf, deftab[p].name);
    if eqstr(key, name) then
      found := true
    else
      p := deftab[p].next
  end;
  lookup := p
end;

{ install -- define a macro }
procedure install(var name, body: tempstring);
  var h: integer;
begin
  h := hash(name);
  ndefs := ndefs+1;
  deftab[ndefs].name := defhwm;
  savestr(name, defbuf, defhwm);
  defhwm := defhwm + length(name) + 1;
  deftab[ndefs].body := defhwm;
  savestr(body, defbuf, defhwm);
  defhwm := defhwm + length(body) + 1;
  deftab[ndefs].next := hashtab[h];
  hashtab[h] := ndefs
end;

{ getargs -- scan macro arguments and put in argbuf }
procedure getargs;
  var
    ch: char;
    level: integer;
begin
  nargs := 0;
  arghwm := 1;
  ch := getpbc;
  if ch <> '(' then
    pbchar(ch)
  else begin
    repeat
      nargs := nargs+1;
      arg[nargs] := arghwm;
      skipws;
      level := 0;
      ch := getpbc;
      while (ch <> ',') and (ch <> ')') or (level > 0) do begin
        if ch = ENDFILE then begin
          writeln('End of file reached in macro call');
          halt
        end;
        argbuf[arghwm] := ch;
        arghwm := arghwm+1;
        if ch = '(' then
          level := level+1
        else if ch = ')' then
          level := level-1;
        ch := getpbc
      end;
      argbuf[arghwm] := ENDSTR;
      arghwm := arghwm+1
    until (ch = ')')
  end
end;

{ expand -- push back a macro expansion }
procedure expand(def: integer);
  var 
    body, i, j, k: integer;
    s, t: tempstring;
begin
  if deftab[def].name = DEFINE then begin
    if nargs >= 1 then begin
      loadstr(s, argbuf, arg[1]);
      if nargs = 1 then
        install(s, emptystr)
      else begin
        loadstr(t, argbuf, arg[2]);
        install(s, t)
      end
    end
  end
  else if deftab[def].name = IFDEF then begin
    if nargs >= 2 then begin
      loadstr(s, argbuf, arg[1]);
      if lookup(s) <> 0 then begin
        loadstr(t, argbuf, arg[2]);
        pbstring(t)
      end
      else if nargs >= 3 then begin
        loadstr(t, argbuf, arg[3]);
        pbstring(t)
      end
    end
  end
  else begin
    body := deftab[def].body;
    i := body-1;
    while defbuf[i+1] <> ENDSTR do i := i+1;
    while i >= body do begin
      if defbuf[i-1] <> '$' then
        pbchar(defbuf[i])
      else if defbuf[i] = '$' then
        pbchar('$')
      else begin
        k := ord(defbuf[i]) - ord('0');
        if (k > 0) and (k <= nargs) then begin
          loadstr(s, argbuf, arg[k]);
          pbstring(s)
        end
        else if (k = 0) and (nargs > 0) then begin
          loadstr(s, argbuf, arg[nargs]);
          pbstring(s);
          for j := nargs-1 downto 1 do begin
            pbchar(' '); pbchar(',');
            loadstr(s, argbuf, arg[j]);
            pbstring(s)
          end
        end;
        i := i-1
      end;
      i := i-1
    end
  end
end;

{ copyquote -- copy quoted text }
procedure copyquote(open, close: char);
  var ch: char;
begin
  outchar(open);
  repeat
    ch := getpbc;
    outchar(ch)
  until (ch = close) or (ch = ENDFILE)
end;

{ scan -- copy input to output, expanding macros }
procedure scan;
  var
    ch: char;
    name: tempstring;
    def: integer;
    i: integer;
begin
  ch := getpbc;
  while ch <> ENDFILE do begin
    if isletter(ch) then begin
      i := 1;
      while isalphanum(ch) do begin
        name[i] := ch;
        i := i+1;
        ch := getpbc
      end;
      pbchar(ch);
      name[i] := ENDSTR;
      def := lookup(name);
      if def = 0 then
        putstring(name)
      else begin
        getargs;
        expand(def)
      end
    end
    else if ch = '{' then
      copyquote('{', '}')
    else if ch = '''' then
      copyquote('''', '''')
    else
      outchar(ch);
    ch := getpbc
  end
end;

procedure init;
  var i: integer;
    s: tempstring;
begin
  ENDSTR := chr(0);
  TAB := chr(9);
  ENDLINE := chr(10);
  ENDFILE := chr(127);

  ndefs := 0;
  defhwm := 1;
  pbp := 0;
  emptystr[1] := ENDSTR;
  for i := 1 to HASHSIZE do hashtab[i] := 0;

  s[1] := 'd';
  s[2] := 'e';
  s[3] := 'f';
  s[4] := 'i';
  s[5] := 'n';
  s[6] := 'e';
  s[7] := ENDSTR;
  install(s, emptystr);
  DEFINE := deftab[ndefs].name;

  s[1] := 'i';
  s[2] := 'f';
  s[3] := 'd';
  s[4] := 'e';
  s[5] := 'f';
  s[6] := ENDSTR;
  install(s, emptystr);
  IFDEF := deftab[ndefs].name
end;

begin
  init;
  scan;
end.
