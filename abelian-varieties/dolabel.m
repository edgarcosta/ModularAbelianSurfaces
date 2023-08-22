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
  euler_factors := function(p)
    return Reverse(CharpolyOfFrobenius(f, p));
  end function;
  _ := NewformLattices(f);
  Hquo_in_Hsub := Transpose(f`integral_homology_subquo[3]);
  res := [* *];
  for quosat in CartesianPower([false,true], 2) do
    quotient, saturate := Explode(quosat);
    Omega, E := PeriodMatrix(f : prec:=prec, Quotient:=false);
    if saturate then
      if debug then
        Omega, E, R, _, EndQQ  := PeriodMatrixWithMaximalOrder(Omega, E);
      else
        try
          Omega, E, R, _, EndQQ  := PeriodMatrixWithMaximalOrder(Omega, E);
        catch er
          WriteStderr(er);
          Append(~res, <quosat, 0, 0, Sprint(er)>);
          continue;
        end try;
      end if;
    else
      R := 1;
    end if;
    if quotient then
      R := Hquo_in_Hsub*R;
    end if;
    // F, C can be zero if no PPs
    if debug then
      b, F, C, e := RationalGenus2CurvesWithPolarization(Omega, E, f);
    else
      try
        b, F, C, e := RationalGenus2CurvesWithPolarization(Omega, E, f);
      catch er
        WriteStderr(er);
        Append(~res, <quosat, 0, 0, Sprint(er)>);
        continue;
      end try;
    end if;
    isogeny_from_sub := R*F;

    if saturate and NarrowClassNumber(EndQQ) eq 1 then
      assert C cmpne 0;
    end if;
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


