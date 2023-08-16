AttachSpec("~/projects/CHIMP/CHIMP.spec");
AttachSpec("~/projects/ModularCurves/abelian-varieties/spec");

s := Split(input, ":");
label := s[1];
prec := StringToInteger(prec);

if assigned verbose then
  verbose := StringToInteger(verbose);
  SetVerbose("ModAbVarRec", verbose);
  SetVerbose("CurveRec", verbose);
end if;

function Core(label, prec);
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
      Omega, E, R, _, EndQQ  := PeriodMatrixWithMaximalOrder(Omega, E);
    else
      R := 1;
    end if;
    if quotient then
      R := Hquo_in_Hsub*R;
    end if;
    // F, C can be zero if no PPs
    b, F, C, e := RationalGenus2CurvesWithPolarization(Omega, E, f);
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
if assigned debug then
  SetDebugOnError(true);
  b, res := Core(label, prec);
else
try
  b, res := Core(label, prec);
catch e
  WriteStderr(e);
  print Join([label, "FAILED", Join(Split(Join(Split(Sprint(e), "\n"),"\\n"), "  "), " ")], ":");
  exit 1;
end try;
end if;



function WriteOutput(elt)
  if Type(elt) eq Tup then
    r := Join([label] cat [Sprint(Eltseq(x)) : x in elt], ":");
  else
    r := Join([label, "NOTFOUND"] cat Sprint(elt));
  end if;
  return StripWhiteSpace(r);
end function;

print WriteOutput(res);
exit 0;


