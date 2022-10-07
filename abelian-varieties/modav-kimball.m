function PerMat(f : prec := 80, ncoeffs := 10000)
  SetDefaultRealFieldPrecision(prec + 10);
  C:=ComplexFieldExtra(prec);
  Pi := Matrix(Periods(f, ncoeffs));
  Pi := Transpose(ChangeRing(Pi, C));
  g := #Rows(Pi);
  P1 := Submatrix(Pi,1,1,g,g);
  P2 := Submatrix(Pi,1,g+1,g,g);
  Pi := HorizontalJoin(P2,P1);
  return Pi;
end function;

function NicePerMat(P : B := 100)
  pp := SomePrincipalPolarizations(P : D := [-B..B]);
  assert #pp ge 1;
  pol := pp[1];
  E, F:= FrobeniusFormAlternating(Matrix(Integers(), pol));
  P2 := P*Matrix(BaseRing(P),Transpose(F)); 
  return P2;
end function;

function Pinvts(P : denomd := 50)
  tau := SmallPeriodMatrix(P);
  S := RosenhainInvariants(tau);
  R<x> := PolynomialRing(BaseRing(P));
  f := x*(x-1)*&*{x-a : a in S};
  IC := IgusaClebschInvariants(f);
  ICp := [BestApproximation(Re(r),10^denomd) : r in [IC[1]/IC[1], IC[2]/IC[1]^2, IC[3]/IC[1]^3, IC[4]/IC[1]^5]];
  return ICp;
end function;

// given integral (f,h) poly coefficients of genus 2 curve compute order
// of rational torsion subgroup of Jacobian
function coeffs2curve(coeffs);
  f := Polynomial(coeffs[1]);
  h := Polynomial(coeffs[2]);
  return HyperellipticCurve(4*f+h^2);
end function;

// given integral (f,h) poly coefficients of genus 2 curve compute order
// of rational torsion subgroup of Jacobian
function torsord(coeffs);
  f := Polynomial(coeffs[1]);
  h := Polynomial(coeffs[2]);
  C := HyperellipticCurve(4*f+h^2);
  J := Jacobian(C);
  T := TorsionSubgroup(J);
  return Order(T);
end function;

// code for reading in the list of coefficients of curves we've computed
function readcurves(fname)
  lines := Split(Read(fname),"\n");
  dat := [];
  for ln in lines do
    lab := Split(ln,":")[1];
    s1 := Split(ln,"[")[2];
    s1 := Split(s1,"]")[1];
    fs := Split(s1,",");
    flist := [StringToInteger(s) : s in fs];

    s2 := Split(ln,"[")[3];
    if #s2 gt 2 then
      s2 := Split(s2,"]")[1];
      hs := Split(s2,",");
      hlist := [StringToInteger(s) : s in hs];
    else
      hlist := [];
    end if;

    Append(~dat, <lab, flist, hlist>);
  end for;
  return dat;
end function;
