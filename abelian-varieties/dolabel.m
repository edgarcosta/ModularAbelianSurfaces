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
  Omega, E := PeriodMatrix(f : prec:=prec, Quotient:=false);
  CC := BaseRing(Omega);
  euler_factors := function(p)
    return Reverse(CharpolyOfFrobenius(f, p));
  end function;
  res_sub := RationalGenus2CurvesFromPolarization(Omega, E, f);
  Hquo_in_Hsub := Transpose(f`integral_homology_subquo[3]);
  Omega_quo, E_quo := PeriodMatrix(f : prec:=prec, Quotient:=true);
  res_quo := RationalGenus2CurvesFromPolarization(Omega_quo, E_quo, f);
  res_quo_from_sub := [* res_quo[1], [* <Hquo_in_Hsub*elt[1], elt[2]> : elt in res_quo[2] *], [* <Hquo_in_Hsub*elt[1], elt[2]> : elt in res_quo[3] *] *];
  return res_sub, res_quo_from_sub;
end function;
if assigned debug then
  SetDebugOnError(true);
  res_sub, res_quo_from_sub := Core(label, prec);
else
try
  res_sub, res_quo_from_sub := Core(label, prec);
catch e
  WriteStderr(e);
  print Join([label, "FAILED", Join(Split(Join(Split(Sprint(e), "\n"),"\\n"), "  "), " ")], ":");
  exit 1;
end try;
end if;

function TupleIsogCurve(elt)
    coeffs := elt[2] cmpeq false select [] else Eltseq(elt[2]);
    return <Eltseq(elt[1]), coeffs>;
end function;
function MachinePrintRes(res)
    return [Sprint(res[1]), Sprint([TupleIsogCurve(elt) : elt in res[2]]), Sprint([TupleIsogCurve(elt) : elt in res[3]])];
end function;

print StripWhiteSpace(Join([label] cat MachinePrintRes(res_sub) cat MachinePrintRes(res_quo_from_sub), ":"));

exit 0;
