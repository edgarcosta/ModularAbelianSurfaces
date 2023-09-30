// Aims to improve the functionality of Geometry/ModAbVar/periods.m
// in particular the number of Fourier coefficients is adaptive and
// and uses IntegralHomology(f::ModSym) instead of calling the magma builtin IntegralHomology(A::ModAbVar)

import !"Geometry/ModSym/analytic.m" : PeriodGenerators;

function GoodPeriodGenerators(f : tries:=50)
  // Stein: "extremely important to choose γ in Proposition 3.57 with d small, otherwise the series will converge very slowly."
  ds := [];

  // we need to waste one, so that SetSeed works
  _ := PeriodGenerators(f, true);
  delete f`PeriodGens;
  for _ in [1..tries] do
    seed, step := GetSeed();
    // compute f`PeriodGens
    _, fast := PeriodGenerators(f, true);
    if not fast then delete f`PeriodGens; continue; end if;
    assert assigned f`PeriodGens;
    Append(~ds, <Max([elt[2,4] : elt in f`PeriodGens]), seed, step>); // elt = [a,b,c,d]
    delete f`PeriodGens;
  end for;
  vprint ModAbVarRec: "GoodPeriodGenerators: ds found", {* elt[1] : elt in ds *};
  d, seed, step := Explode(Min(ds));
  SetSeed(seed, step);
  _, fast := PeriodGenerators(f, true);
  assert fast and d eq Max([elt[2,4] : elt in f`PeriodGens]);
  return d;
end function;


function bisection(f, a, b)
  if b cmpeq Infinity then
     assert f(a) lt 0;
     b := a;
     while f(b) lt 0 do
        b *:= 2;
     end while;
  end if;
  if b - a le 1 then
     return b;
  end if;

  c := (a + b) div 2;
  if f(c) lt 0 then
     return $$(f, c, b);
  else
     return $$(f, a, c);
  end if;
end function;


// compute a upper bound on the number of coefficients in the q-expansion
// so that all digits are correct
function BoundNumberOfCoefficients(f, d, prec)
  e := AtkinLehnerSign(f);
  N := Level(f);
  q := Exp(- 2 * Pi(RealField()) / Sqrt(N));
  qd := q^(1/d);
  //prec := Precision(GetDefaultRealField());
  err := 10^-prec;
  Mf := Matrix([pi_f(b) : b in Basis(f)]) where pi_f := PeriodMapping(f, 50);
  Mfabs := [Abs(elt) : elt in Eltseq(Mf)];
  eps := ComplexFieldExtra(prec)`epscomp;
  min_entry := Min([elt : elt in Mfabs | elt gt eps]);
  /*
  We are summing
    ((e-1)*q^n + qd^n*(Exp(2*PI*i*n*b/d)-e*Exp(2*PI*i*n*c/d))) an/n
  |Exp(2*PI*i*n*b/d)-e*Exp(2*PI*i*n*c/d))| <= 2
  |an| < d(n) sqrt(n)
  d(n) < Exp(Log(2)Log(n)/(Log(Log(n)) - 1.3918))
  */
  g := func<n|
    err - min_entry*Abs((e - 1) * q^n /(1 - q) + 2 * qd^n /(1 - qd))*
    Exp(Log(2)*Log(n)/(Log(Log(n)) - 1.3918))
  >;
  return bisection(g, 2, Infinity);
end function;

intrinsic PeriodMappingMatrix(f::ModSym : prec:=80) -> ModMatFldElt, RngIntElt, FldElt
  { Compute the normalized period matrix associated to f }
  // clear cache
  extra_prec := Ceiling(prec/0.95 + 10); // equality is checked at 95% of the digits or at extra 10 digits
  if assigned f`PeriodMap and Precision(BaseRing(Codomain(f`PeriodMap))) lt extra_prec then
    delete f`PeriodMap;
  end if;

  vprint ModAbVarRec: Sprintf("Computing period map, prec:=%o, for ", prec);
  vprint ModAbVarRec: Sprintf("%o...", f);
  default_prec := Precision(GetDefaultRealField());
  // this is how we control the precision of the output of Periods
  SetDefaultRealFieldPrecision(extra_prec);

  CC := ComplexFieldExtra(extra_prec);
  B := Basis(f);

  function matrix_helper(ncoeffs)
    vprintf ModAbVarRec: "Computing PeriodMapping with n = %o...", ncoeffs;
    vtime ModAbVarRec:
    return ChangeRing(Matrix([pi_f(b) : b in B]), CC) where pi_f := PeriodMapping(f, ncoeffs);
  end function;

  k  := Weight(f);
  fast := (Level(f) gt 1) and (k mod 2 eq 0)
         and IsTrivial(DirichletCharacter(f))
         and IsScalar(AtkinLehner(f,Level(f)));
  if fast then
    // Stein: "extremely important to choose γ in Proposition 3.57 with d small, otherwise the series will converge very slowly."
    d := GoodPeriodGenerators(f);
  end if;
  // for k = 2 we can easily compute an upper bound on the number of fourier coefficients necessary
  if fast and k eq 2 then
    ncoeffs := BoundNumberOfCoefficients(f, d, prec);
    vprint ModAbVarRec: Sprintf("target ncoeffs = %o", ncoeffs);
    P0 := matrix_helper(ncoeffs);
    P1 := matrix_helper(ncoeffs + Min(100, ncoeffs div 10));
    _, e := AlmostEqualMatrix(P0, P1);
    assert e lt 10^-prec;
  else
    ncoeffs := 0;
    // FIXME this guess comes from weight 2
    // before we defaulted to this guess with the first 2 replaced by 20
    ncoeffs_inc := Ceiling(2*Sqrt(Level(f))*Log(10)*prec/(2*Pi(ComplexField())));
    ncoeffs +:= 3*ncoeffs_inc;
    P0 := matrix_helper(ncoeffs);
    ncoeffs +:= ncoeffs_inc;
    P1 := matrix_helper(ncoeffs);
    // P0 and P1 live in rings with extra_prec
    // this checks if they agree up to prec
    t, e := AlmostEqualMatrix(P0, P1);
    while not t do
      // FIXME: we could do this much better
      // we could check that the errors are getting smaller and we could even estimate how much we should increase the number of coefficients
      vprint ModAbVarRec: Sprintf("Current error: %o, by using ncoeffs = %o", ComplexField(8)!e, ncoeffs);
      P0 := P1;
      ncoeffs +:= ncoeffs_inc;
      P1 := matrix_helper(ncoeffs);
      t, e := AlmostEqualMatrix(P0, P1);
      assert ncoeffs lt 50*ncoeffs_inc; // sanity check that we are converging
    end while;
  end if;
  vprint ModAbVarRec: Sprintf("Final error: %o", ComplexField(8)!e);
  vprint ModAbVarRec: Sprintf("Final ncoeffs: %o", ncoeffs);
  P1 := ChangeRing(P1, ComplexFieldExtra(prec));
  // undo the default_prec
  SetDefaultRealFieldPrecision(default_prec);
  vprint ModAbVarRec: "Done with PeriodMappingMatrix";
  return Transpose(P1), ncoeffs, e;
end intrinsic;


intrinsic PeriodMatrix(f::ModSym : prec:=80, Quotient:=false, MaximalEnd:=false) -> ModMatFldElt, ModMatRngElt
  { Compute the period matrix associated to f A_f^sub or A_f^quo }
  vprintf ModAbVarRec: "Comuting the lattices...";
  vtime ModAbVarRec:
  basis, E := IntegralHomology(f : Quotient:=Quotient, MaximalEnd:=MaximalEnd);
  P := PeriodMappingMatrix(f : prec := prec);
  return P*Matrix(BaseRing(P),  Transpose(basis)), E;
end intrinsic;

intrinsic PeriodMatrixSubMagma(f::ModSym : prec:=80) -> ModMatFldElt
  { Compute the period matrix associated to f A_f^sub via Magma's computation of integral homology }
  _, ncoeffs, _ := PeriodMappingMatrix(f : prec:=prec);
  P := Matrix(Periods(f, ncoeffs)); // this should use the cached map
  assert Precision(BaseRing(P)) gt prec;
  CC := ComplexFieldExtra(prec);
  // Change convention
  P := Transpose(ChangeRing(P, CC));
  g := #Rows(P);
  P1 := Submatrix(P, 1, 1, g, g);
  P2 := Submatrix(P, 1, g + 1,g, g);
  P := HorizontalJoin(P2, P1);
  return P;
end intrinsic;

