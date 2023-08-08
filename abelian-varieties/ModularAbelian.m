declare verbose ModAbVarRec, 3;

declare attributes ModSym:
  integral_homology_subquo; // SeqEnum[Tup]


intrinsic LMFDBNewform(label::MonStgElt) -> ModSym
{ Return modular form given label }
    filenames := GetFilenames(MakeNewformModSym);
    assert #filenames eq 1;

    dirname := "/" cat Join(s[1..(#s - 1)], "/") where s := Split(filenames[1,1],"/");
    for elt in getrecs(dirname cat "/labelswithhecke.txt") do
        if elt[1] eq label then
            level := StringToInteger(elt[2]);
            hc := eval elt[3];
            break;
        end if;
    end for;
    return MakeNewformModSym(level, hc);
end intrinsic;

import "reconstructiongenus2.m" : AlgebraizedInvariantsG2, ReconstructCurveG2, IgusaInvariantsG2;

// One can do better than this for trivial character, N square free, and when cond(chi) is a proper divisor of N, see Stein 9.19,9.21,9.22,
// but this bound (due to Buzzard) works for all spaces M_k(N,chi) and is best possible in some cases, see Stein 9.20
intrinsic SturmBound (N::RngIntElt, k::RngIntElt) -> RngIntElt
{ Sturm bound for space of modular forms of level N weight k and any character. }
    require N ge 1 and k ge 1: "Level N and weight k must be positive integers";
    m := Index(Gamma0(N));
    return Integers()!Floor(k*m/12);
end intrinsic;



intrinsic Eltseq(C::CrvHyp) -> SeqEnum
  {retunrns both hyperelliptic polynomials as SeqEnum}
  if BaseRing(C) eq Rationals() then
    f, g := HyperellipticPolynomials(MinimalWeierstrassModel(C));
    return [Eltseq(f), Eltseq(g)];
  else
    f, g := HyperellipticPolynomials(C);
    df := LCM([Denominator(elt) : elt in Eltseq(f)]);
    f *:= df^2;
    g *:= df;
    if g ne 0 then // I don't think this ever runs
      dg := LCM([Denominator(elt) : elt in Eltseq(g)]);
      f *:= dg^2;
      g *:= dg;
    end if;
    return [[Eltseq(elt) : elt in Eltseq(pol)] : pol in [f, g]];
  end if;
end intrinsic;

intrinsic MachinePrint(v::ModTupRngElt) -> MonStgElt
{ return "V:F" where F is list of the coefficients of the defining polynomial}
  F := BaseRing(v);
  v := Eltseq(v);
  if Type(F) eq FldRat then
    return Sprint(v);
  end if;
  voverQQ := [Eltseq(elt) : elt in v];
  f := DefiningPolynomial(F);
  return Sprintf("%o:%o", voverQQ,  Eltseq(f));
end intrinsic;

intrinsic MachinePrint(C::CrvHyp) -> MonStgElt
  { .. }
  F := BaseRing(C);
  if BaseRing(C) eq Rationals() then
    return Sprintf("%o", Eltseq(C));
  else
    f := DefiningPolynomial(F);
    return Sprintf("%o:%o", Eltseq(C), Eltseq(f));
  end if;
end intrinsic;





intrinsic PeriodMappingMatrix(f::ModSym : prec:=80) -> ModMatFldElt, RngIntElt, FldElt
  { Compute the normalized period matrix associated to f }
  // before we defaulted to this guess with the first 2 replaced by 20
  // clear cache
  if assigned f`PeriodMap and Precision(BaseRing(Codomain(f`PeriodMap))) lt prec + 10 then
    delete f`PeriodMap;
  end if;

  vprint ModAbVarRec: Sprintf("Computing period map, prec:=%o, for ", prec);
  vprint ModAbVarRec: Sprintf("%o...", f);
  default_prec := Precision(GetDefaultRealField());
  // this is how we control the precision of the output of Periods
  SetDefaultRealFieldPrecision(prec + 10);

  CC := ComplexFieldExtra(prec + 10);
  B := Basis(f);

  function matrix_helper(ncoeffs)
    return ChangeRing(Matrix([pi_f(b) : b in B]), CC) where pi_f := PeriodMapping(f, ncoeffs);
  end function;


  ncoeffs := 0;
  ncoeffs_inc := Ceiling(2*Sqrt(Level(f))*Log(10)*prec/(2*Pi(ComplexField())));
  ncoeffs +:= 3*ncoeffs_inc;
  vtime ModAbVarRec:
  P0 := matrix_helper(ncoeffs);
  ncoeffs +:= ncoeffs_inc;
  vtime ModAbVarRec:
  P1 := matrix_helper(ncoeffs);
  // P0 and P1 live in rings with prec + 10
  // this checks if they agree up to prec
  t, e := AlmostEqualMatrix(P0, P1);
  while not t do
    vprint ModAbVarRec: Sprintf("Current error: %o", ComplexField(8)!e);
    P0 := P1;
    ncoeffs +:= ncoeffs_inc;
    vprintf ModAbVarRec: "ncoeffs increased to %o\n", ncoeffs;
    vtime ModAbVarRec:
    P1 := matrix_helper(ncoeffs);
    t, e := AlmostEqualMatrix(P0, P1);
    assert ncoeffs lt 20*ncoeffs_inc; // sanity
  end while;
  P1 := ChangeRing(P1, ComplexFieldExtra(prec));
  // undo the default_prec
  SetDefaultRealFieldPrecision(default_prec);
  vprint ModAbVarRec: "Done";
  return Transpose(P1), ncoeffs, e;
end intrinsic;


intrinsic PeriodMatrix(f::ModSym : prec:=80, Quotient:=false) -> ModMatFldElt, ModMatRngElt
  { Compute the period matrix associated to f A_f^sub or A_f^quo }
  basis, E := Explode(NewformLattices(f)[Quotient select 2 else 1]);
  P := PeriodMappingMatrix(f : prec := prec);
  return P*Matrix(BaseRing(P),  Transpose(basis)), E;
end intrinsic;

intrinsic PeriodMatrixSubMagma(f::ModSym : prec:=80) -> ModMatFldElt
  { Compute the period matrix associated to f A_f^sub via Magma }
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


intrinsic PeriodMatrixWithMaximalOrder(P::ModMatFldElt, E::AlgMatElt) -> ModMatFldElt, AlgMatElt, AlgMatElt, SeqEnum, RngOrd
{
  Given a period matrix P for a dim 2 modular forms space with trivial character
  such that the coefficient ring index is > 1, return a period matrix for an isogenous abelian variety
  such that the isogenous abelian variety has endomorphism ring equal to the maximal order
}
  vprint ModAbVarRec: "Extending lattice...";
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
  assert one eq 1 or one eq -1;
  minpoly := MinimalPolynomial(gen); //need to make (D + sqrt(D)) where D is the discriminant
  K<a> := NumberField(minpoly);

  if IsMaximal(EquationOrder(K)) then // nothing to do
    return P, E, IdentityMatrix(Integers(), Ncols(P)),  GeoEndoRepBase, EquationOrder(K);
  end if;

  // Now we compute the isogeny R, such that P*R is an abelian variety with maximal order
  D:= Discriminant(Integers(K));
  x := Parent(minpoly).1;
  sqrtDpoly := x^2 - D;
  rts := Roots(sqrtDpoly, K);
  rt := rts[1][1];
  sqrtD := &+[c*gen^(i-1) : i->c in Eltseq(rt)];
  DpSqrtD := D*one + sqrtD;
  CC := BaseRing(P);
  // We now compute the intersection of 2*Lambda with (D + Sqrt(D))*Lambda
  kernel, bool := IntegralRightKernel(HorizontalJoin(P*2, P*Matrix(CC, DpSqrtD)));
  assert bool;

  S, T, _ := SmithForm(Matrix(Integers(), kernel));
  assert Submatrix(S, 1, 1, 4, 4) eq 1;
  assert Submatrix(S, 5, 1, 4, 4) eq 0;
  Tinv := T^-1;

  // we now should compute a matrix R in M_2g(ZZ)
  // such that P2 = P*R, where End(P2) = ZZ[(D + Sqrt(D))/2]
  A := Submatrix(Tinv, 1, 5, 4, 4);
  B := Submatrix(Tinv, 5, 5, 4, 4);
  R := 2*A + DpSqrtD*B;

  P2 := P*Matrix(CC, R);
  E2 := Transpose(R)*E*R;
  vprint ModAbVarRec: "Computing GeometricEndomorphismRepresentation...";
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
  vprint ModAbVarRec: "Done";
  return P2, E2, R, GeoEndoRepBase2, EquationOrder(K2);
end intrinsic;

intrinsic ReconstructRationalGenus2Curves(Omega::ModMatFldElt, E::AlgMatElt : Saturate:=true) -> List
  {From a period matrix Omega and a pairing E, return curves associated to the abelian variety 
  and the abelian variety with the maximal endomorphism order (if Saturate)}
    function Auxiliar(Omega, E)
        PPs := RationalPrincipalPolarizations(Omega, E);
        QQ := RationalsExtra(Precision(BaseRing(Omega)));
        res := [* *];
        for pp in PPs do
            newOmega, F := Explode(pp); // newOmega == Omega * F
            C, h, b, e := ReconstructCurveG2(newOmega, QQ);
            if b then
                Append(~res, <F, C>);
            else
                Append(~res, <F, false>);
            end if;
        end for;
        return res;
    end function;
    res := Auxiliar(Omega, E);
    if not Saturate then
        return res;
    end if;
    Omega_max, E_max, R, _, EndQQ  := PeriodMatrixWithMaximalOrder(Omega, E);
    if R eq 1 then
        res_max := res;
    else
        res_max := [* <R*elt[1], elt[2]> : elt in Auxiliar(Omega_max, E_max) *];
    end if;
    if NarrowClassNumber(EndQQ) eq 1 then
        assert #res_max ge 1; // maybe we should just check that #RationalPrincipalPolarizations > 1
    end if;
    return [* R eq 1, res, res_max *];
end intrinsic;

intrinsic NewformLattices(f::ModSym) -> SeqEnum[Tup]
{Find the homology for the abelian subvariety associated to f and the quotient variety of J0N, and the intersection pairing}
  if not assigned f`integral_homology_subquo then
    A := AmbientSpace(f);
    L, phi := Lattice(A);

    CS := CuspidalSubspace(A);
    // compute an integral basis for CS
    delta := Matrix(Basis(L)) * Matrix(Integers(), BoundaryMap(A));
    // B is an integral basis for CS
    B := [phi(b) : b in Basis(Kernel(delta))];
    fromCS := Matrix(Integers(), [Eltseq(elt) : elt in B]);


    // S: B -> Basis(CS)
    S, K := Solution(
      Matrix([Eltseq(elt) : elt in B]),
      Matrix([Eltseq(elt) : elt in Basis(CS)])
      );
    assert Dimension(K) eq 0;
    assert Abs(Determinant(S)) eq 1;
    if S eq 1 then
      S := 1;
    else
      S := Matrix(Integers(), S);
    end if;
    S1 := S^-1;


    p := 1;
    desired_rank := Dimension(CS) - Dimension(f); // rank of If*H
    H := ZeroMatrix(Integers(), Dimension(CS), 0);
    V := ZeroMatrix(Integers(), 0, Dimension(CS));
    // we are going this method as NewSubspace basis is not always equipped with an integral, e.g., 285.2.a.d
    while Rank(H) ne desired_rank do
        p := NextPrime(p);
        while Level(f) mod p eq 0 do
            p := NextPrime(p);
        end while;
        // Hecke operator with respect to the integral basis
        Tp := Matrix(Integers(), S*HeckeOperator(CS, p)*S1);
        h := ChangeRing(MinimalPolynomial(HeckeOperator(f, p)), Integers()); //degree 2
        hp := Evaluate(h, Tp);
        H := HorizontalJoin(H, hp);
        V := VerticalJoin(V, hp);
    end while;
    Hsub := KernelMatrix(H);//this is supposed to be H[If], and If = (hp)_p, dim 4
    //If := Ker (TT -> Z[...an(f)...]) T_n -> an(f), and min poly of an(f) is h
    // FIXME: replace unused with _ when bug in SmithForm is fixed
    D, unused, Q := SmithForm(V);
    if Nrows(D) gt 0 then
      assert Diagonal(D)[Ncols(D)-Dimension(f)+1..Ncols(D)] eq [0 : _ in [1..Dimension(f)]];
    end if;

    // this basis projects down to the standard basis of (H/If H)_free
    // these are basis for Hquo
    Hquo := Submatrix(Q^-1, Nrows(Q) - Dimension(f) + 1, 1, Dimension(f), Ncols(Q));

    assert Rank(VerticalJoin(V, Hquo)) eq Dimension(CS);

    //this is the projection of H_sub in (H/If H)_free
    Hsub_in_Hquo := Hsub*Submatrix(Q, 1, Ncols(Q) - Dimension(f) + 1, Nrows(Q), Dimension(f));

    //we now invert Hsub_in_Hquo not caring about rescaling
    Hquo_in_Hsub := Matrix(Rationals(), Hsub_in_Hquo)^-1;
    //Denominator(Hquo_in_Hsub);
    Hquo_in_Hsub *:= Denominator(Hquo_in_Hsub);
    Hquo_in_Hsub := Matrix(Integers(), Hquo_in_Hsub);

    S := Matrix(Integers(), KernelMatrix(VerticalJoin( Matrix(Rationals(), Hsub*fromCS), -Matrix([Eltseq(b) : b in Basis(f)]))));
    assert Submatrix(S, 1,1, Dimension(f), Dimension(f)) eq 1;
    // how to write Hsub basis in terms of Basis(f)
    Hsub_in_Bf := Submatrix(S, 1,1 + Dimension(f), Dimension(f), Dimension(f));

    // how to write Hquo in terms of Basis(f)
    Hquo_in_Bf := Hquo_in_Hsub*Hsub_in_Bf;

    Ef := IntersectionPairing(f);
    Esub, Equo := Explode([Matrix(Integers(), A*Denominator(A)) where A := S*Ef*Transpose(S) where S:=Matrix(Rationals(), elt) : elt in [Hsub_in_Bf, Hquo_in_Bf]]);
    // Esub div:= GCD(Eltseq(Esub)); //???
    // Equo div:= GCD(Eltseq(Equo));
    f`integral_homology_subquo := [* <Hsub_in_Bf, Esub>, <Hquo_in_Bf, Equo>, Hquo_in_Hsub *];
  end if;
  return f`integral_homology_subquo;
end intrinsic;



/*
intrinsic SomeIsogenousPrincipallyPolarized(P::ModMatFldElt: D:= [-10..10]) -> Assoc
{
    Returns period matrix for the d-isogenous abelian variety which is principally polarized
    for several d by using SomePolarizations
}
// FIXME: Use IsogenousPPLattices
  vprintf ModAbVarRec: "SomeIsogenousPrincipallyPolarized(P : D:=%o)...\n", D;
  polarizations := SomePolarizations(P : D:=D);
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
  vprintf ModAbVarRec: "Polarizations counts: %o\n", [<key, #res[key]> : key in Sort(SetToSequence(Keys(res)))];
  vprint ModAbVarRec: "SomeIsogenousPrincipallyPolarized: Done";
  return res;
end intrinsic;
*/

intrinsic FindPrincipalPolarizations(P::ModMatFldElt : D:=[-10..10]) -> SeqEnum
{ TODO: fill in doc }
  vprintf ModAbVarRec: "Finding a polarizations %o...", D;
  vtime ModAbVarRec:
  polarizations := SomePrincipalPolarizations(P : D:=D);
  vprint ModAbVarRec: "Done, found %o polarizations\n", #polarizations;
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



intrinsic ReconstructModularCurve(f::ModSym) -> BoolElt, Crv
{ TODO: fill in doc }
    ncoeffs := SturmBound(Level(f), Weight(f)) + 100;
    vprintf ModAbVarRec: "ReconstructModularCurve(%o, %o) ", Level(f), ncoeffs;
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


/*
//TODO check isogenity?
intrinsic ReconstructIsomorphicGenus2Curve(P::ModMatFldElt : UpperBound:=16, tau:=false) -> BoolElt, .
{ return Curve or Igusa Invariants }
  // assume that P is a big period matrix
  require IsBigPeriodMatrix(P) : "Expects a big period matrix";
  if tau cmpeq false then
    tau := ReduceSmallPeriodMatrix(SmallPeriodMatrix(P));
  end if;
  CC := BaseRing(P);
  QQ := RationalsExtra(Precision(CC));

  J := false;
  JCC := IgusaInvariantsG2(taunew : Reduce:=false);
  _, _, _, _, J10 := Explode(J);

  if not Abs(J10)^2 lt CC`epscomp then //not a product of elliptic curves
    // over a number field this is sometimes suprisingly successful
    vprintf ModAbVarRec: "Reconstructing curve by matching tangent representation...";
    vtime ModAbVarRec:
    C, hL, b, e := ReconstructCurveG2(P, QQ : UpperBound:=UpperBound);
    if b then
      vprintf ModAbVarRec: "Done\n C = %o\n" , C;
      igusa := IgusaInvariants(C);
      ratIgusa := &and[elt in Rationals() : elt in igusa];
      // try to descend C
      if Type(BaseRing(C)) ne FldRat and ratIgusa then
        C := HyperellipticCurveFromIgusaInvariants(igusa);
      end if;
      return true, C;
    end if;
    e := Sprintf("ReconstructCurveG2 failed : %o\n", e);
    vprint ModAbVarRec: e;
    WriteStderr(e);
  end if;

  vprintf ModAbVarRec: "Recognizing igusa invariants...";
  // one would like to go for Modular invariants directly
  // but it hard to normalize them, one should instead use rational functions
  // e.g. recognize h4*h6/h10, h6^2/h12, etc
  J, _, b, e := AlgebraizedInvariantsG2(P, QQ : UpperBound:=UpperBound, type:="Igusa");
  if b then
    vprintf ModAbVarRec: "Done\n J = %o over %o\n" , J, Universe(J);
    if Universe(J) cmpeq Rationals() then
      vprint ModAbVarRec: "Descending C";
      C := HyperellipticCurveFromIgusaInvariants(J);
      return true, C;
    else
      return true, Vector(J);
    end if;
  end if;
  e := Sprintf("AlgebraizedInvariantsG2 failed : %o\n", e);
  vprint ModAbVarRec: e;
  WriteStderr(e);

  return false, _; // we failed at everything
end intrinsic;
*/


intrinsic PossibleQuadraticTwists(C::CrvHyp, euler_factors::UserProgram, BadPrimes: Bound:=200) -> RngIntElt
{ Find a quadratic twist such that C and it matches the given Euler factors, returns 0 if no quadratic twist is found}
  vprintf ModAbVarRec: "Find correct quadratic twist...";
  orderG := #GeometricAutomorphismGroup(C);
  vprintf ModAbVarRec: "The geometric automorphism group is of size %o.\n", orderG;
  oktofail := orderG ne 2;
  disc := Discriminant(C);
  D := Integers()! (Numerator(disc) * Denominator(disc));
  badprimes := IndexedSet(PrimeDivisors(D) cat BadPrimes cat [-1]);
  primes := Sort(SetToSequence(IndexedSet(PrimesUpTo(Bound)) diff badprimes));
  twistdata := [];
  splittingdata := [];
  usedprimes := []; // not used for anything
  // this could be written without Bound and with a while loop
  for p in primes do

    // Compute euler factor of the curve
    vprintf ModAbVarRec: "p = %o\nEuler factor C ", p;
    vtime ModAbVarRec:
    efc := EulerFactor(C, p);
    vprint ModAbVarRec: "Euler factor C = ", Coefficients(efc);

    // Compute euler factor of the original object
    vprintf ModAbVarRec: "Euler factor original ", p;
    vtime ModAbVarRec:
    eff := euler_factors(p);
    vprint ModAbVarRec: "Euler factor f = ", Coefficients(eff);


    efctwist := Evaluate(efc, -Parent(efc).1);
    if eff notin [efc, efctwist] then
        require oktofail : Sprintf("is not a local quadratic twist at p=%o\nefc = %o != %o = eff\n C = %o, and #G = %o", p, Eltseq(efc), Eltseq(eff), C, orderG);
        return [];
    end if;

    if efc eq efctwist then
      continue; // we cannot distinguish between either
    end if;

    Append(~usedprimes, p);
    if efc eq eff then
      Append(~twistdata, 0);
    else
      Append(~twistdata, 1);
    end if;
    Append(~splittingdata, [(KroneckerSymbol(q, p) eq -1) select 1 else 0 : q in badprimes]);
    if Rank(Matrix(GF(2), splittingdata)) eq #badprimes then
      break p;
    end if;
  end for;
  M := Transpose(Matrix(GF(2), splittingdata));
  v := Vector(GF(2), twistdata);
  vprint ModAbVarRec: badprimes, usedprimes, Rank(M), #badprimes;
  vprint ModAbVarRec: M;
  vprint ModAbVarRec: Vector(GF(2), twistdata);
  k := Nrows(M);
  solutions := [Eltseq(elt)[1..k] : elt in Kernel(VerticalJoin(M, Matrix(v))) | elt[k + 1] eq 1];
  return [#r gt 0 select &*r else 1
          where r := [badprimes[i]: i->e in sol | not IsZero(e)]
    : sol in solutions];
  vprint ModAbVarRec: "Done";
end intrinsic;


intrinsic PossibleQuadraticTwists(C::CrvHyp, f::ModSym : Bound:=200) -> RngIntElt
{ Find a quadratic twist such that C and f have the same L-function, returns 0 if no quadratic twist is found}
  euler_factors := function(p)
    return Reverse(CharpolyOfFrobenius(f, p));
  end function;
  return PossibleQuadraticTwists(C, euler_factors, PrimeDivisors(Level(f)) : Bound:=Bound);
end intrinsic;



// FIXME, the output might not be a curve, but just igusa invariants over some numberfield
intrinsic ReconstructGenus2Curve(f::ModSym : prec:=80, D:=[-4..4], UpperBound:=12) -> BoolElt, Any
{
TODO: add documentation
}

  procedure InLats(~res, ~Lats, F)
    L := Lattice(F);
    d := Determinant(F);
    // decide if we already seen this lattice
    if not d in Keys(Lats) then
      Lats[d] := {L};
      res := false;
    else
      res := L in Lats[d];
      if not res then
        Include(~Lats[d], L);
      end if;
    end if;
  end procedure;

  procedure AddToBins(~newbin, ~bins, key, value, compare)
    placed := false;
    for y in Keys(bins) do
      if compare(key,y) then
        Append(~bins[y], value);
        placed := true;
        break y;
      end if;
    end for;
    if not placed then
      bins[key] := [value];
    end if;
    newbin := not placed;
  end procedure;

  function CompareIgusaCC(x, y)
    return Abs(Norm(Vector(x) - Vector(y))) lt Universe(x)`epscomp;
  end function;

  procedure SortResults(~lst)
    // sort on field
    // then on curve < Igusa < G2
    // and then on size
    function TypeRank(elt)
      if ISA(Type(elt), Crv) then
        return 0;
      end if;
      assert Type(elt) eq ModTupFldElt; //aka a  vector
      if #Eltseq(elt) eq 5 then // igusa invariants
        return 1;
      end if;
      return 2;
    end function;
    degdisc := [<Degree(R), Discriminant(R), TypeRank(elt), #StripWhiteSpace(Sprint(Eltseq(elt)))> where R:=BaseRing(elt) : elt in lst];
    positions := [1..#lst];
    vprintf ModAbVarRec: "UnSorted: %o\n%o\n", degdisc, lst;
    ParallelSort(~degdisc, ~positions);
    lst := [* lst[j] : j in positions *];
    vprintf ModAbVarRec: "Sorted: %o\n%o\n", degdisc, lst;
  end procedure;

  function DoWeHaveARationalCurve(lst)
    // returns a boolean
    return #lst ge 1 and ISA(Type(lst[1]), Crv) and Type(BaseRing(lst[1])) eq FldRat;
  end function;




  function ReconstructIsogeneousPPs(P, bins, Js)
    /*
    We first look at minimal index PP lattices for small polarizations given by SomePolarizations
    For each PP lattice we:
      - put them in Bins according to igusa invariants over CC
      - try to immediately recognize each new igusa invariant over QQ

    If we have not succeeded so far, then after colleign all the lattices we:
      - try to recognize each new igusa invariant over a number field
      - finally loop over twists and try to match tangent representation
    */

    Lats := AssociativeArray(); // Det -> Lats
    CC := BaseRing(P);
    QQ := RationalsExtra(Precision(CC));
    res := [* *];
    polarizations := SomePolarizations(P : D:=D);
    for i->polarisation in polarizations do
      vprintf ModAbVarRec: "Looping over polarizations: %o of %o.\n", i, #polarizations;
      vprint ModAbVarRec: "Computing isogenous PP lattices...";
      vtime ModAbVarRec: isogenous := IsogenousPPLattices(polarisation : ProjToPP:=false);
      detL := [Determinant(elt) : elt in isogenous];
      ParallelSort(~detL, ~isogenous);
      for j->F in isogenous do
        vprintf ModAbVarRec: "Looping over isogenous PP lattices: %o of %o.\n", j, #isogenous;
        vprintf ModAbVarRec: "Det(L) = %o.\n", Determinant(F);
        // decide if we already seen this lattice
        b := false;
        InLats(~b, ~Lats, F);
        if b then
          continue F;
        end if;

        // Compute new period matrix
        Pnew := P*Transpose(ChangeRing(F, CC) );
        try // Reduce might fail
          taunew := ReduceSmallPeriodMatrix(SmallPeriodMatrix(Pnew));
        catch e
          continue F;
        end try;
        JCC := IgusaInvariantsG2(taunew : Reduce:=false);

        AddToBins(~b, ~bins, JCC, <taunew, Pnew, F>, CompareIgusaCC);


        if not b then // not new
          continue F;
        end if;
        vprint ModAbVarRec: "Recognizing igusa invariants over QQ...";
        vtime ModAbVarRec: b, J := AlgebraizeElementsExtra(JCC, QQ);

        if not b then // failed to recognize
          vprint ModAbVarRec: "Could not recognize igusa invariants over QQ\n";
          continue F;
        end if;

        Js[JCC] := J;
        vprintf ModAbVarRec: "Done\n J = %o\n", J;
        _, _, _, _, J10 := Explode(J);
        if J10 eq 0 then
          vprint ModAbVarRec: "We got a product of elliptic curves";
          vprintf ModAbVarRec: "Recognizing j-invariants...";
          jpair, _, b, e := AlgebraizedInvariantsG2(taunew, QQ : UpperBound:=UpperBound, type:="j", Reduce:=false);
          if b then
            vprintf ModAbVarRec: "Done\n j invariants = %o over %o\n" , jpair, Universe(jpair);
            Append(~res, Vector(jpair));
          else
            vprint ModAbVarRec: e;
            WriteStderr(e);
          end if;
        else
          C := HyperellipticCurveFromIgusaInvariants(J);
          vprintf ModAbVarRec: "C = %o\n", C;
          C := CurveExtra(C : prec := Precision(CC)-10);
          assert #GeometricHomomorphismRepresentationCC(ChangeRing(PeriodMatrix(C), CC), P) gt 0;
          Append(~res, C);
          if BaseRing(C) eq Rationals() then
            break polarisation;
          end if;
        end if;
      end for;
    end for;


    SortResults(~res);
    if DoWeHaveARationalCurve(res) then
      return res, bins, Js;
    end if;

    countbin := 0;
    for JCC->B in bins do
      countbin +:= 1;
      vprintf ModAbVarRec: "Looping over isomorphism classes: %o of %o.\n", countbin, #bins;
      _, _, _, _, J10 := Explode(JCC);

      b, val := IsDefined(Js, JCC);

      if  Abs(J10)^2 lt CC`epscomp
          or
          (b and Universe(val) eq Rationals())
          or
          #B eq 0
        then
        // is not a genus 2 curve
        // we already tried to tackle this isomorphism class via invariants
        // no twists
        continue JCC;
      end if;


      vprint ModAbVarRec: "Recognizing igusa invariants over a number field...";
      try
        vtime ModAbVarRec:
        L, J, _ := NumberFieldExtra(JCC, QQ : UpperBound:=UpperBound);
        b := true;
      catch e
        b := false;
        vprint CurveRec : "Failed to algebraize igusa invariants.";
        WriteStderr(e);
      end try;

      if b then
        vprintf ModAbVarRec: "Done\n J = %o over %o\n" , J, L;
        Js[JCC] := J;
        if L cmpeq Rationals() then
          vprint ModAbVarRec: "Constructing curve...";
          C := HyperellipticCurveFromIgusaInvariants(J);
          vprint ModAbVarRec: "C = %o\n", C;
          C := CurveExtra(C : prec := Precision(CC)-10);
          assert #GeometricHomomorphismRepresentationCC(ChangeRing(PeriodMatrix(C), CC), P) gt 0;
          Append(~res, C);
          if BaseRing(C) eq Rationals() then
            break JCC;
          end if;
          continue JCC; // no point on looping over twists over a numberfield
        else
          // we will still try to loop over twists and match tagent representation
          Append(~res, Vector(J));
        end if;
      end if;

      detB := [Determinant(elt[3]) : elt in B];
      idxB := [i : i in [1..#B]];
      ParallelSort(~detB, ~idxB);

      //for i->idx in idxB do
      for i->tuple in B do
        //tuple := B[idx];
        vprintf ModAbVarRec: "Looping over twists: %o of %o.\n", i, #B;
        _, Pnew, F := Explode(tuple);
        vprintf ModAbVarRec: "Det(Lattice) = %o.\n", Determinant(F);
        try
          vprint ModAbVarRec: "Reconstructing curve by matching tangent representation...";
          // over a number field this is sometimes suprisingly successful
          // and if the igusa invariants are over a NumberField there is not much u
          vtime ModAbVarRec:
          C, _, b := ReconstructCurveG2(Pnew, QQ : UpperBound:=UpperBound);
          if b then
            vprintf ModAbVarRec: "Done\n C = %o\n" , C;
          else
            vprint ModAbVarRec: "ReconstructCurveG2 was not successful";
          end if;
        catch e
          b := false;
          vprint ModAbVarRec: "ReconstructCurveG2: Failed :(";
          WriteStderr(e);
        end try;
        if b then
          igusa := IgusaInvariants(C);
          ratIgusa := &and[elt in Rationals() : elt in igusa];
          // try to descend C
          if Type(BaseRing(C)) ne FldRat and ratIgusa then
            C := HyperellipticCurveFromIgusaInvariants(igusa);
          end if;
          C := CurveExtra(C : prec := Precision(CC)-10);
          assert #GeometricHomomorphismRepresentationCC(ChangeRing(PeriodMatrix(C), CC), P) gt 0;
          Append(~res, C);
          if BaseRing(C) eq Rationals() then
            break JCC;
          end if;
        end if;
      end for; // loop over elements of a bin
    end for; // loop over bins
    return res, bins, Js;
  end function;


  // The work starts here:
  bins := AssociativeArray(); // JCC -> <reduced small period matrix, big period matrix?
  Js := AssociativeArray(); // JCC -> JQbar
  res := [* *];

  // just use the modular forms as potential differential forms on the curve
  b, C := ReconstructModularCurve(f);
  if b then
    res := [* C *];
  end if;

  if not DoWeHaveARationalCurve(res) then
    P := PeriodMatrix(f : prec:=prec);
    vprint ModAbVarRec: "Looping over isogenous PP lattices with original period matrix";
    vtime ModAbVarRec:
    newres, bins, Js := ReconstructIsogeneousPPs(P, bins, Js);
    res cat:= newres;
    SortResults(~res);
    vprint ModAbVarRec: "Done looping over SomeIsogenousPrincipallyPolarized with original period matrix";
  end if;
  if not DoWeHaveARationalCurve(res) then
    P2, G2 := PeriodMatrixWithMaximalOrder(P);
    // if P == P2, then P was already maximal order
    if P ne P2 then
      vprint ModAbVarRec: "Looping over isogenous PP lattices with maximal order period matrix";
      // drop previous isomorphism classes, but keep the buckets
      for k in Keys(bins) do
        bins[k] := [];
      end for;
      vtime ModAbVarRec:
      newres, bins, Js := ReconstructIsogeneousPPs(P, bins, Js);
      res cat:= newres;
      SortResults(~res);
      vprint ModAbVarRec: "Done looping over SomeIsogenousPrincipallyPolarized with maximal order period matrix";
    else
      vprint ModAbVarRec: "Order already maximal";
    end if;
  end if;

  vprintf ModAbVarRec: "all the curves %o\m", res;
  if DoWeHaveARationalCurve(res) then
    C := res[1];
    vprintf ModAbVarRec: "Found curve %o\n", C;
    D := PossibleQuadraticTwists(C, f);
    vprintf ModAbVarRec: "Possible twisted by %o\n", D;
    if #D eq 1 then
      C := QuadraticTwist(C, D[1]);
    else
      e := "The curve has more than quadratic twists";
      vprint ModAbVarRec: e;
      WriteStderr(e);
    end if;
    vtime ModAbVarRec:
    C := ReducedMinimalWeierstrassModel(C);
    return true, C;
  elif #res gt 0 then
    return true, res[1];
  end if;
  return false, _;
end intrinsic;

intrinsic MakeNewformModSym(level::RngIntElt, hecke_cutters::SeqEnum[Tup]) -> ModSym
{ "TODO: add documentation" }
    vprintf ModAbVarRec: "MakeNewformModSym(%o, %o)\n", level, &cat Split(Sprint(hecke_cutters), "\n");
    R<x> := PolynomialRing(Rationals());
    // SetVerbose("ModularSymbols", true);
    chi := DirichletGroup(level)!1;
    Rhecke_cutters := [<elt[1], R!elt[2]> : elt in hecke_cutters];
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,2)));
    f := Kernel(Rhecke_cutters ,Snew);
    vprintf ModAbVarRec: "Done MakeNewformModSym(%o, %o)\n", level, &cat Split(Sprint(hecke_cutters), "\n");
    return f;
end intrinsic;





