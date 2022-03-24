

intrinsic GetDimension2Factors(N) -> SeqEnum
{ FIXME }
  return [A : A in Decomposition(JZero(N))];
end intrinsic;

intrinsic NormalizePeriods(A::ModAbVar : prec:=80, ncoeffs:=10000) -> ModMatFldElt
{ FIXME }
    default_prec := Precision(GetDefaultRealField());
    // this is how we control the precision of the output of Periods
    SetDefaultRealFieldPrecision(prec + 10);
    C := ComplexFieldExtra(prec);
    P := Matrix(Periods(A, ncoeffs));
    // Change convention
    P := Transpose(ChangeRing(P, C));
    g := #Rows(P);
    P1 := Submatrix(P, 1, 1, g, g);
    P2 := Submatrix(P, 1, g + 1,g, g);
    P := HorizontalJoin(P2, P1);
    // undo the default_prec
    SetDefaultRealFieldPrecision(default_prec);
    return P;
end intrinsic;


intrinsic PeriodsWithMaximalOrder(P::ModMatFldElt) -> ModMatFldElt, SeqEnum
{
    Given a period matrix P for a dim 2 modular forms space with trivial character
    such that the coefficient ring index is > 1, return a period matrix for an isogenous abelian variety
    such that the isogenous abelian variety has endomorphism ring equal to the maximal order
}
    QQ := RationalsExtra(Precision(BaseRing(P)); // do we need to use RationalsExtra?
    GeoRep := GeometricEndomorphismRepresentation(P, QQ : UpperBound:=1);
    one := GeoRep[1][2];
    gen := GeoRep[2][2];
    assert one eq 1;
    minpoly := MinimalPolynomial(gen); //need to make (D + sqrt(D)) where D is the discriminant
    K<a> := NumberField(minpoly);
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
    GeoRep2 := GeometricEndomorphismRepresentation(P2, QQ : UpperBound:=1);
    comp := MinimalPolynomial(GeoRep2[2][2]);
    exp := MinimalPolynomial(Integers(K).2);
    exp2 := MinimalPolynomial(-Integers(K).2);
    require comp in {exp, exp2} : Sprintf("%o \noin {%o, %o}", comp, exp, exp2);
    return P2, GeoRep2;
end intrinsic;


intrinsic ReconstructGenus2Curve(P::ModMatFldElt) -> ModMatFldElt, SeqEnum
{ FIXME }
    bool, pol := SomePrincipalPolarization(P);
    assert bool;
    E, F := FrobeniusFormAlternating(Matrix(Integers(), pol));
    H := ReconstructCurve(P*Transpose(ChangeRing(F, C)), Q);
    H := ReducedMinimalWeierstrassModel(H);
    return H;
end intrinsic;






