AttachSpec("~/projects/CHIMP/CHIMP.spec");
AttachSpec("~/projects/ModularCurves/abelian-varieties/spec");

s := Split(input, ":");
label := s[1];
prec := StringToInteger(prec);

if assigned verbose then
  try
    verbose := StringToInteger(verbose);
  catch e
    verbose := 1;
  end try;
  SetVerbose("ModAbVarRec", verbose);
  SetVerbose("CurveRec", verbose);
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
    isogeny_from_sub := R*F;

    if b then
      // we found a curve, we go home early
      return b, <isogeny_from_sub, C>;
    end if;
    Append(~res, <quosat, F, C, e>);
  end for;
  return false, res;
end function;
b, res := Core(label, prec : debug:= assigned debug);



function WriteOutput(elt)
  if Type(elt) eq Tup then
    r := Join([label] cat [Sprint(Eltseq(x)) : x in elt], ":");
  else
    r := Join([label, "NOTFOUND", Sprint(elt)], ":");
  end if;
  return StripWhiteSpace(r);
end function;

print WriteOutput(res);
exit 0;


