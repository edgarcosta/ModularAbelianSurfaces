AttachSpec("~/projects/CHIMP/CHIMP.spec");
AttachSpec("~/projects/ModularCurves/abelian-varieties/spec");
s := Split(input, ":");
label := s[1];
level := StringToInteger(s[2]);
hc := eval s[3];
inner_twist_count := StringToInteger(s[4]);
if inner_twist_count gt 1 then
  WriteStderr("Toolazyerror: Non trivial inner twist\n");
  exit 2; // skipping these for now
end if;
prec := StringToInteger(prec);
ncoeffs := Ceiling(20*Sqrt(level)*Log(10)*prec/(2*Pi(ComplexField())));
f := MakeNewformModSym(level, hc);
try
  b, H := ReconstructGenus2Curve(f : prec:=prec, ncoeffs:=ncoeffs);
  f, g := HyperellipticPolynomials(MinimalWeierstrassModel(H));
catch e
  WriteStderr(e);
  exit 1;
end try;
StripWhiteSpace(Sprintf("%o:[%o,%o]", label, Eltseq(f), Eltseq(g)));
exit;
