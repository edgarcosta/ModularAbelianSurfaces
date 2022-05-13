declare verbose ModAbVarRec, 3;

import "reconstructiongenus2.m" : AlgebraizedInvariantsG2, ReconstructCurveG2, ReconstructCurveG2CC;


intrinsic WriteStderr(s::MonStgElt)
{ write to stderr }
  E := Open("/dev/stderr", "w");
  Write(E, s);
  Flush(E);
end intrinsic;


intrinsic WriteStderr(e::Err)
{ write to stderr }
  WriteStderr(Sprint(e) cat "\n");
end intrinsic;

intrinsic Eltseq(C::CrvHyp) -> SeqEnum
  {retunrns both hyperelliptic polynomials as SeqEnum}
  if BaseRing(C) eq Rationals() then
    f, g := HyperellipticPolynomials(MinimalWeierstrassModel(C));
  else 
    f, g := HyperellipticPolynomials(C);
  end if;
  return [Eltseq(f), Eltseq(g)];
end intrinsic;

intrinsic MachinePrint(v::ModTupRngElt) -> MonStgElt
  { return "F:V" where F is list...}
  F := BaseRing(v);
  v := Eltseq(v);
  if Type(F) eq FldRat then
    return Sprint(v);
  end if;
  voverQQ := [Eltseq(elt) : elt in v];
  f := DefiningPolynomial(F);
  return Sprintf("%o:%o", Eltseq(f), voverQQ);
end intrinsic;

intrinsic MachinePrint(C::CrvHyp) -> MonStgElt
  { .. }
  F := BaseRing(C);
  f := DefiningPolynomial(F);
  return Sprintf("%o:%o", Eltseq(f), Eltseq(C));
end intrinsic;

/*
 * No Longer need this
intrinsic NormalizedPeriodMatrix(P::ModMatFldElt) -> ModMatFldElt
{ this normalizes  }
    CC := ComplexFieldExtra(Precision(BaseRing(P)));
    // Change convention
    P := Transpose(ChangeRing(P, CC));
    g := #Rows(P);
    P1 := Submatrix(P, 1, 1, g, g);
    P2 := Submatrix(P, 1, g + 1,g, g);
    P := HorizontalJoin(P2, P1);
    return P;
end intrinsic;
*/

// use hecke to get the number of correct digits
intrinsic PeriodMatrix(f::ModSym : prec:=80, ncoeffs:=10000) -> ModMatFldElt
{ Compute the normalized period matrix associated to f}
  vprint ModAbVarRec: Sprintf("Computing periods, prec:=%o, ncoeffs:=%o", prec, ncoeffs);
  vprintf ModAbVarRec: Sprintf("%o...", f);
  default_prec := Precision(GetDefaultRealField());
  // this is how we control the precision of the output of Periods
  SetDefaultRealFieldPrecision(prec + 10);
  vtime ModAbVarRec:
  // PeriodMapping gives the periods up to isogeny
  pi_f := PeriodMapping(f, ncoeffs);
  // Apply it to the whole space
  Pfull := Transpose(Matrix([pi_f(b) : b in Basis(CuspidalSubspace(AmbientSpace(f)))]));
  CC := ComplexFieldExtra(Precision(BaseRing(Pfull)));
  Pfull := Matrix(CC, Pfull);

  // figure out the relations
  kernel, b := IntegralRightKernel(Pfull);
  S, P, Q := SmithForm(Matrix(Integers(), kernel));

  // extract the correct period matrix
  CC := BaseRing(Pfull);
  PfullNew := Pfull*Matrix(CC, P^-1);
  PNew := Submatrix(PfullNew, 1, 1+ Ncols(PfullNew) - Dimension(f), 2, Dimension(f));
  // undo the default_prec
  SetDefaultRealFieldPrecision(default_prec);
  vprint ModAbVarRec: "Done";
  return PNew;
end intrinsic;




intrinsic PeriodMatrixWithMaximalOrder(P::ModMatFldElt) -> ModMatFldElt, SeqEnum
{
  Given a period matrix P for a dim 2 modular forms space with trivial character
  such that the coefficient ring index is > 1, return a period matrix for an isogenous abelian variety
  such that the isogenous abelian variety has endomorphism ring equal to the maximal order
}
  vprintf ModAbVarRec: "Extending lattice...";
  QQ := RationalsExtra(Precision(BaseRing(P)));
  vprint ModAbVarRec: "\nComputing GeometricEndomorphismRepresentation...";
  vtime ModAbVarRec:
  GeoEndoRep := GeometricEndomorphismRepresentation(P, QQ);
  F, h := InclusionOfBaseExtra(BaseRing(GeoEndoRep[1][1]));
  GeoEndoRepBase := EndomorphismRepresentation(GeoEndoRep, F, h);
  vprint ModAbVarRec:GeoEndoRep;
  vprint ModAbVarRec:GeoEndoRepBase;
  vprint ModAbVarRec: "Done";
  require #GeoEndoRepBase eq 2: Sprintf("This does not seem to be GL2-type, dim End A = %o", #GeoEndoRepBase);
  one := GeoEndoRepBase[1][2];
  gen := GeoEndoRepBase[2][2];
  assert one eq 1;
  minpoly := MinimalPolynomial(gen); //need to make (D + sqrt(D)) where D is the discriminant
  K<a> := NumberField(minpoly);
  if IsMaximal(EquationOrder(K)) then // nothing to do
    return P, GeoEndoRepBase;
  end if;
  D:= Discriminant(Integers(K));
  x := Parent(minpoly).1;
  sqrtDpoly := x^2 - D;
  rts := Roots(sqrtDpoly, K);
  rt := rts[1][1];
  sqrtD := &+[c*gen^(i-1) : i->c in Eltseq(rt)];
  DpSqrtD := D*one + sqrtD;
  CC := BaseRing(P);
  AuxP := Transpose(Matrix(Rows(Transpose(2*P)) cat Rows(Transpose(P*Matrix(CC, DpSqrtD)))));
  kernel, bool := IntegralRightKernel(AuxP);
  assert bool;
  S, P, Q := SmithForm(Matrix(Integers(), kernel));
  P2 := Submatrix(AuxP*Matrix(CC, P^-1), 1, 5, 2, 4);
  vprintf ModAbVarRec: "Computing GeometricEndomorphismRepresentation...";
  vtime ModAbVarRec:
  GeoEndoRep2 := GeometricEndomorphismRepresentation(P2, QQ);
  vprint ModAbVarRec: "Done";
  require #GeoEndoRep2 ge 2: Sprintf("This does not seem to be GL2-type, dim End newA_bar = %o", #GeoEndoRep2);
  F, h := InclusionOfBaseExtra(BaseRing(GeoEndoRep2[1][1]));
  GeoEndoRepBase2 := EndomorphismRepresentation(GeoEndoRep2, F, h);
  vprint ModAbVarRec:GeoEndoRep2;
  vprint ModAbVarRec:GeoEndoRepBase2;
  require #GeoEndoRepBase2 ge 2: Sprintf("This does not seem to be GL2-type, dim End newA = %o", #GeoEndoRepBase2);
  minpoly2 := MinimalPolynomial(GeoEndoRepBase2[2][1]);
  K2<a> := NumberField(minpoly2);
  require IsMaximal(EquationOrder(K2)) : "something went wrong, we didn't get the maximal order...";
  //exp := MinimalPolynomial(Integers(K).2);
  //exp2 := MinimalPolynomial(-Integers(K).2);
  //require comp in {exp, exp2} : Sprintf("%o \noin {%o, %o}", comp, exp, exp2);
  vprint ModAbVarRec: "Done";
  return P2, GeoEndoRepBase2;
end intrinsic;

intrinsic SomeIsogenousPrincipallyPolarized(P::ModMatFldElt: D:= [-10..10]) -> Assoc
{
    Returns period matrix for the d-isogenous abelian variety which is principally polarized
    for several d by using SomePolarizations
}
  polarizations := SomePolarizations(P : D := D);
  CC := BaseRing(P);
  res := AssociativeArray();
  for pol in polarizations do //find the (1,d) polarization with the smallest d
    Zpol:= Matrix(Integers(), pol);
    E, F:= FrobeniusFormAlternating(Zpol);
    d := E[2, 4]/E[1, 3];
    key := <d, E[1, 3]>;
    Dscalar := Matrix([
                 [1, 0, 0, 0],
                 [0, 1/d, 0, 0],
                 [0, 0, 1, 0],
                 [0, 0, 0, 1]]);
    Pnew := P * Transpose(ChangeRing(Dscalar * F, CC) );
    b := IsDefined(res, key);
    if not b then
      res[key] := [];
    end if;
    Append(~res[key], Pnew);
  end for;
  return res;
end intrinsic;

intrinsic FindPrincipalPolarizations(P::ModMatFldElt : D:=[-10..10]) -> SeqEnum
{ TODO: fill in doc }
  vprintf ModAbVarRec: "Finding a polarizations %o...", D;
  vtime ModAbVarRec:
  polarizations := SomePrincipalPolarizations(P : D:=D);
  vprintf ModAbVarRec: "Done, found %o polarizations\n", #polarizations;
  if #polarizations eq 0 then
    b := D[1]; e := D[#D];
    if (e - b + 1) eq #D then
      vprintf ModAbVarRec: "increasing D = %o ", D;
      D := [b - #D div 2 .. e + #D div 2];
      vprintf ModAbVarRec: "to D = %o\n", D;
      vprintf ModAbVarRec: "Finding a polarizations %o...", D;
      vtime ModAbVarRec:
      polarizations := SomePrincipalPolarizations(P : D:=D);
      vprintf ModAbVarRec: "Done, found %o polarizations\n", #polarizations;
    end if;
  end if;
  return polarizations;
end intrinsic;


function PrettyCurve(Y)
  if Type(BaseRing(Y)) eq FldRat then
    Y := ReducedMinimalWeierstrassModel(Y);
    f, h := HyperellipticPolynomials(Y);
    g := 4*f + h^2;
    coeffs := Coefficients(g);
    d := LCM([ Denominator(coeff) : coeff in coeffs ]);
    coeffs := [ Integers() ! (d*coeff) : coeff in coeffs ];
    e := GCD(coeffs);
    coeffs := [ coeff div e : coeff in coeffs ];
    Y := HyperellipticCurve(Polynomial(coeffs));
    Y := ReducedMinimalWeierstrassModel(Y);
  end if;
  return Y;
end function;

intrinsic ReconstructModularCurve(f::ModSym : ncoeffs:=ncoeffs) -> BoolElt, Crv
{ TODO: fill in doc }
    vprintf ModAbVarRec: "Trying to see if there is a modular curve...";
    require Dimension(f) in [2, 4]: "Expected a galois orbit of dimension 2";
    f1, f2 := Explode(qExpansionBasis(f, ncoeffs));
    R<q> := Parent(f1);
    xq := f2/f1;
    yq := Derivative(xq)*q/f1;
    function PaddedCoefficients(elt, start, e)
        return [Coefficient(elt, i) : i in [start..e]];
    end function;
    R<q> := Parent(xq);
    monomials := [<i,j> : i in [0..6], j in [0..2] | 3*j + i le 6];
    M := Matrix(
    [PaddedCoefficients(xq^i*yq^j, 0, 100) where i,j := Explode(elt) : elt in monomials]
    );
    B := Basis(Kernel(M));
    if #B eq 0 then
        return false, _;
    end if;
    b := B[1];
    S1<x> := PolynomialRing(Rationals());
    S2<y> := PolynomialRing(S1);
    fxy := &+[c*x^i*y^j where i, j := Explode(monomials[k]) : k->c in Eltseq(b) ];
    fxy /:= Coefficient(fxy, 2);
    Cf := -Coefficient(fxy, 0);
    Cg := Coefficient(fxy, 1);
    assert y^2 + Cg*y - Cf eq fxy;
    vprint ModAbVarRec: "Done!";
    return true, HyperellipticCurve(Cf, Cg);
end intrinsic;


//TODO check isogenity?

intrinsic ReconstructIsomorphicGenus2Curve(P::ModMatFldElt) -> BoolElt, .
{ TODO: fill in doc
  return Curve or IgusaInvariants if not rational}
  // assume that P is a big period matrix
  require IsBigPeriodMatrix(P) : "Expects a big period matrix";
  CC := BaseRing(P);
  QQ := RationalsExtra(Precision(CC));
  G2CC := ReconstructCurveG2CC(P);
  try
    vprintf ModAbVarRec: "Reconstructing curve by matching tangent representation...";
    // First tries ReconstructCurve as it tries to match tangent representation
    vtime ModAbVarRec:
    C, hL, b := ReconstructCurveG2(P, QQ : G2CC:=G2CC);
    vprintf ModAbVarRec: "Done\n C = %o\n" , C;
    igusa := IgusaInvariants(C);
    ratIgusa := &and[elt in Rationals() : elt in igusa];
    // try to descend C
    if Type(BaseRing(C)) ne FldRat and ratIgusa then
      C := HyperellipticCurveFromIgusaInvariants(igusa);
    end if;
    return true, C;
  catch e
    WriteStderr(e);
    vprint ModAbVarRec: "Failed :(";
  end try;

  try
    vprintf ModAbVarRec: "Reconstructing curve by recognizing igusa invariants...";
    //FIXME check if J10 is 0
    vtime ModAbVarRec:
    igusa := AlgebraizedInvariantsG2(P, QQ : G2CC:=G2CC);
    vprintf ModAbVarRec: "Done\n igusa = %o\n" , igusa;
    if Universe(igusa) cmpeq Rationals() then
      vprint ModAbVarRec: "Descending C";
      C := HyperellipticCurveFromIgusaInvariants(igusa);
      return true, C;
    else
      // if the igusa invariants are not rational, we don't try to reconstruct the curve
      return true, Vector(igusa);
    end if;
  catch e
    WriteStderr(e);
    vprint ModAbVarRec: "Failed :(";
  end try;
  return false, _;
end intrinsic;




intrinsic FindCorrectQuadraticTwist(C::CrvHyp, f::ModSym : Bound:=200) -> RngIntElt
{ Find a quadratic twist such that C and f have the same L-function }
    vprintf ModAbVarRec: "Find correct quadratic twist...";
    D := Integers()!Discriminant(C) * Level(f);
    N := Level(f);
    badprimes := IndexedSet(PrimeDivisors(D) cat [-1]);
    primes := IndexedSet(PrimesUpTo(Bound)) diff badprimes;
    skipp := [];
    twistdata := [];
    splittingdata := [];
    // this could be written without Bound and with a while loop
    for p in primes do
      vprintf ModAbVarRec: "p = %o\nEuler factor C ", p;
      vtime ModAbVarRec:
      efc := EulerFactor(C, p);
      if IsZero(Coefficient(efc, 1)) then
        // useless prime, as efc(x) = efc(-x)
        Append(~skipp, p);
        continue;
      end if;
      vprintf ModAbVarRec: "Euler factor f ", p;
      vtime ModAbVarRec:
      eff := Reverse(CharpolyOfFrobenius(f, p));
      if efc eq eff then
        Append(~twistdata, 0);
      else
        require Evaluate(efc, -Parent(efc).1) eq eff : Sprintf("is not a local quadratic twist at p=%o\nefc = %o != %o = eff\n C = %o", p, efc, eff, C);
        Append(~twistdata, 1);
      end if;
      Append(~splittingdata, [(KroneckerSymbol(q, p) eq -1) select 1 else 0 : q in badprimes]);
      if Rank(Matrix(GF(2), splittingdata)) eq #badprimes then
        break p;
      end if;
    end for;
    sol := Solution(Transpose(Matrix(GF(2), splittingdata)), Vector(GF(2), twistdata));
    vprint ModAbVarRec: "Done";
    if IsZero(sol) then
      return 1;
    else
      return &*[badprimes[i]: i->e in Eltseq(sol) | not IsZero(e)];
    end if;
end intrinsic;



// FIXME, the output might not be a curve, but just igusa invariants over some numberfield
intrinsic ReconstructGenus2Curve(f::ModSym : prec:=80, ncoeffs:=10000, D:=[-10..10]) -> BoolElt, Any
{
TODO: add documentation
}


  function ReconstructIsogeneousPPs(P)
    //this returns a list of curves and vectors of igusa invariants
    polarizations := SomeIsogenousPrincipallyPolarized(P : D:=D);
    res := [* *];
    for key in Sort(SetToSequence(Keys(polarizations))) do
      vprintf ModAbVarRec: "Trying polarization type = %o, %o of them.\n", key, #polarizations[key];
      for elt in polarizations[key] do
        // C is either a curve, or a vector of Igusa invariants over a number field
        b, C := ReconstructIsomorphicGenus2Curve(elt);
        if b then
          // both Curves and Vectors have BaseRing
          if Type(BaseRing(C)) eq FldRat then
            return [* C *]; // found a rational curve nothing else to do
          else
            Append(~res, C);
          end if;
        end if;
      end for;
    end for;
    return res;
  end function;


  procedure SortResults(~lst)
    // sort on field
    // then on curve, as false < true
    // and then on size
    degdisc := [<Degree(R), Discriminant(R), not Type(elt) eq Crv, #StripWhiteSpace(Sprint(Eltseq(elt)))> where R:=BaseRing(elt) : elt in lst];
    positions := [1..#lst];
    ParallelSort(~degdisc, ~positions);
    lst := [* lst[j] : j in positions *];
  end procedure;

  function DoWeHaveARationalCurve(lst)
    // returns a boolean
    return #lst ge 1 and Type(lst[1]) eq Crv and Type(BaseRing(lst[1])) eq FldRat;
  end function;


  // The work starts here:
  //
  res := [* *];

  // just use the modular forms as potential differential forms on the curve
  b, C := ReconstructModularCurve(f: ncoeffs:=ncoeffs);
  if b then
    res := [* C *];
  end if;

  if not DoWeHaveARationalCurve(res) then
    P := PeriodMatrix(f : prec:=prec, ncoeffs:=ncoeffs);
    vprint ModAbVarRec: "Trying SomeIsogenousPrincipallyPolarized with original period matrix";
    vtime ModAbVarRec:
    res cat:= ReconstructIsogeneousPPs(P);
    SortResults(~res);
    vprint ModAbVarRec: "^ looping over SomeIsogenousPrincipallyPolarized with original period matrix";
  end if;
  if not DoWeHaveARationalCurve(res) then
    // FIXME?: this might not know what P is
    P2, G2 := PeriodMatrixWithMaximalOrder(P);
    // if P == P2, then P was already maximal order
    if P ne P2 then
      vprint ModAbVarRec: "Trying SomeIsogenousPrincipallyPolarized with maximal order period matrix";
      vtime ModAbVarRec:
      res cat:= ReconstructIsogeneousPPs(P2);
      SortResults(~res);
      vprint ModAbVarRec: "^ looping over SomeIsogenousPrincipallyPolarized with maximal order period matrix";
    end if;
  end if;

  if DoWeHaveARationalCurve(res) then
    C := res[1];
    vprintf ModAbVarRec: "Found curve %o\n", C;
    D := FindCorrectQuadraticTwist(C, f);
    vprintf ModAbVarRec: "Twisted by %o\n", D;
    vtime ModAbVarRec:
    C := PrettyCurve(QuadraticTwist(C, D));
    return true, C;
  elif #res gt 0 then
    return true, res[1];
  end if;
  return false, _;
end intrinsic;

intrinsic MakeNewformModSym(level::RngIntElt, hecke_cutters::SeqEnum[Tup]) -> ModSym
{ FIXME }
    R<x> := PolynomialRing(Rationals());
    // SetVerbose("ModularSymbols", true);
    chi := DirichletGroup(level)!1;
    hecke_cutters := [<elt[1], R!elt[2]> : elt in hecke_cutters];
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,2)));
    f := Kernel(hecke_cutters ,Snew);
    return f;
end intrinsic;





