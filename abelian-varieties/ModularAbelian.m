

intrinsic GetDimension2Factors(N) -> SeqEnum
{ FIXME }
  return [A : A in Decomposition(JZero(N))];
end intrinsic;


intrinsic NormalizedPeriods(P::ModMatFldElt : prec:=80) -> ModMatFldElt
{ FIXME }
    CC := ComplexFieldExtra(prec);
    // Change convention
    P := Transpose(ChangeRing(P, CC));
    g := #Rows(P);
    P1 := Submatrix(P, 1, 1, g, g);
    P2 := Submatrix(P, 1, g + 1,g, g);
    P := HorizontalJoin(P2, P1);
    return P;
end intrinsic;

intrinsic PeriodsFromModSymb(f::ModSym : prec:=80, ncoeffs:=10000) -> ModMatFldElt
{ FIXME }
    default_prec := Precision(GetDefaultRealField());
    // this is how we control the precision of the output of Periods
    SetDefaultRealFieldPrecision(prec + 10);
    pi_f := PeriodMapping(f, ncoeffs);
    P:= [pi_f(b) : b in Basis(f)];
    // undo the default_prec
    SetDefaultRealFieldPrecision(default_prec);
    return NormalizedPeriods(Matrix(P) : prec:=prec);
end intrinsic;





intrinsic PeriodsWithMaximalOrder(P::ModMatFldElt) -> ModMatFldElt, SeqEnum
{
    Given a period matrix P for a dim 2 modular forms space with trivial character
    such that the coefficient ring index is > 1, return a period matrix for an isogenous abelian variety
    such that the isogenous abelian variety has endomorphism ring equal to the maximal order
}
    QQ := RationalsExtra(Precision(BaseRing(P)));
    GeoEndoRep := GeometricEndomorphismRepresentation(P, QQ);
    F, h := InclusionOfBaseExtra(BaseRing(GeoEndoRep[1][1]));
    GeoEndoRepBase := EndomorphismRepresentation(GeoEndoRep, F, h);
    one := GeoEndoRepBase[1][2];
    gen := GeoEndoRepBase[2][2];
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
    GeoEndoRep2 := GeometricEndomorphismRepresentation(P2, QQ);
    GeoEndoRepBase2 := EndomorphismRepresentation(GeoEndoRep2, F, h);
    //comp := MinimalPolynomial(GeoEndoRepBase2[2][1]);
    //exp := MinimalPolynomial(Integers(K).2);
    //exp2 := MinimalPolynomial(-Integers(K).2);
    //require comp in {exp, exp2} : Sprintf("%o \noin {%o, %o}", comp, exp, exp2);
    return P2, GeoEndoRepBase2;
end intrinsic;


intrinsic ReconstructGenus2Curve(P::ModMatFldElt) -> ModMatFldElt, SeqEnum
{ FIXME }
    bool, pol := SomePrincipalPolarization(P);
    assert bool;
    CC := BaseRing(P);
    QQ := RationalsExtra(Precision(CC));
    E, F := FrobeniusFormAlternating(Matrix(Integers(), pol));
    H := ReconstructCurve(P*Transpose(ChangeRing(F, CC)), QQ);
    H := ReducedMinimalWeierstrassModel(H);
    return H;
end intrinsic;






