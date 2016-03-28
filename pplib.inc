{ pplib.inc -- interface routines for picoProlog }

{ argc -- return number of arguments, counting the program name }
function argc: integer;
begin
  argc := ParamCount+1
end;

{ argv -- fetch |i|'th argument; program name is number 0 }
procedure argv(i: integer; var arg: tempstring);
  var j, k: integer; temp: string;
begin
  temp := ParamStr(i);
  k := length(temp);
  for j := 1 to k do arg[j] := temp[j];
  arg[k+1] := chr(0)
end;

{ openin -- open input file, return true if successful }
function openin(var f: text; var name: tempstring): boolean;
  var j, k: integer; temp: string;
begin
  k := StringLength(name);
  temp := '';
  for j := 1 to k do temp := temp + name[j];
  {$I-} assign(f, temp); reset(f); {$I-} {%ASSIGN%}
  openin := IOresult = 0
end;

{ closein -- close input file }
procedure closein(var f: text);
begin
  close(f)
end;
