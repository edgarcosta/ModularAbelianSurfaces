AttachSpec("~/projects/CHIMP/CHIMP.spec");
AttachSpec("~/projects/ModularAbelianSurfaces/spec");

SetNthreads(1);

s := Split(input, ":");
label := s[1];
prec := StringToInteger(prec);
start := Time();

if assigned profile then
  SetProfile(true);
end if;

if assigned outfile then
    try
      labels := {elt[1] : elt in getrecs(outfile)};
    catch e
      WriteStderr(e);
      labels := {};
    end try;
    if label in labels then
      WriteStderr("Already computed " cat label);
      exit 0;
    end if;
end if;

if assigned verbose then
  try
    verbose := StringToInteger(verbose);
  catch e
    verbose := 1;
  end try;
  SetVerbose("ModAbVarRec", verbose);
  SetVerbose("CurveRec", verbose);
  SetVerbose("HomologyModularSymbols", verbose);
  SetVerbose("ModularSymbols", 3);
end if;
if assigned debug then
  SetDebugOnError(true);
end if;

function Core(label, prec : debug := false);
  f := LMFDBNewform(label);
  QQ := RationalsExtra(prec);
  res := [* *];
  for quosat in CartesianPower([false, true], 2) do
    Quotient, MaximalEnd := Explode(quosat);
    R := IsogenyFromSub(f : Quotient:=Quotient, MaximalEnd:=MaximalEnd);
    if debug then
      localres := RationalGenus2Curves(f : prec:=prec, Quotient:=Quotient, MaximalEnd:=MaximalEnd, OnlyOne:=true);
    else
      try
        localres := RationalGenus2Curves(f : prec:=prec, Quotient:=Quotient, MaximalEnd:=MaximalEnd, OnlyOne:=true);
      catch er
        WriteStderr(er);
        Append(~res, <quosat, Sprint(er)>);
        continue;
      end try;
    end if;

    localres_fromsub := [* *];
    for elt in localres do
      b, isog, C, e := Explode(elt);
      isogeny_from_sub := R*isog;
      if b then
        // we found a curve, we go home early
        return b, <isogeny_from_sub, C>;
      end if;
      Append(~localres_fromsub, <isogeny_from_sub, C, e>);
    end for;
    Append(~res, <quosat, localres_fromsub>);
  end for;
  return false, res;
end function;

function WriteOutput(label, elt)
  columns := [label];
  if Type(elt) eq Tup then
    columns cat:= [Sprint(Eltseq(x)) : x in elt];
  else
    columns cat:= ["NOTFOUND", Sprint(elt)];
  end if;
  mb := Sprintf("%.2o", GetMaximumMemoryUsage()*1.0*2^-20);
  wt := Time(start);
  columns cat:= [mb, wt];
  return StripWhiteSpace(Join(columns, ":"));
end function;

b, res := Core(label, prec : debug:= assigned debug);
WriteOutput(label, res);

if assigned profile then
  SetProfile(false);
  ProfilePrintByTotalTime(ProfileGraph());
end if;
exit 0;


