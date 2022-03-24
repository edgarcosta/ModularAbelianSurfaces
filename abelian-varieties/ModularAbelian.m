declare verbose ModAbVarRec, 3;

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

// use hecke to get the number of correct digits
intrinsic PeriodsFromModSymb(f::ModSym : prec:=80, ncoeffs:=10000) -> ModMatFldElt
{ FIXME }
    vprint ModAbVarRec: Sprintf("Computing periods, prec:=%o, ncoeffs:=%o", prec, ncoeffs);
    vprintf ModAbVarRec: Sprintf("%o...", f);
    default_prec := Precision(GetDefaultRealField());
    // this is how we control the precision of the output of Periods
    SetDefaultRealFieldPrecision(prec + 10);
    vtime ModAbVarRec:
    pi_f := PeriodMapping(f, ncoeffs);
    P:= [pi_f(b) : b in Basis(f)];
    // undo the default_prec
    SetDefaultRealFieldPrecision(default_prec);
    vprint ModAbVarRec: "Done";
    return NormalizedPeriods(Matrix(P) : prec:=prec);
end intrinsic;





intrinsic PeriodsWithMaximalOrder(P::ModMatFldElt) -> ModMatFldElt, SeqEnum
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
    //comp := MinimalPolynomial(GeoEndoRepBase2[2][1]);
    //exp := MinimalPolynomial(Integers(K).2);
    //exp2 := MinimalPolynomial(-Integers(K).2);
    //require comp in {exp, exp2} : Sprintf("%o \noin {%o, %o}", comp, exp, exp2);
    vprint ModAbVarRec: "Done";
    return P2, GeoEndoRepBase2;
end intrinsic;


intrinsic ReconstructGenus2Curve(P::ModMatFldElt : tries:=10) -> ModMatFldElt, SeqEnum
{ FIXME }
    for i in [1..tries] do
        vprintf ModAbVarRec: "Finding a polarization...";
        vtime ModAbVarRec:
        bool, pol := SomePrincipalPolarization(P);
        vprint ModAbVarRec: "Done";
        assert bool;
        CC := BaseRing(P);
        QQ := RationalsExtra(Precision(CC));
        E, F := FrobeniusFormAlternating(Matrix(Integers(), pol));
        vprintf ModAbVarRec: "Reconstructing curve...";
        vtime ModAbVarRec:
        C := ReconstructCurve(P*Transpose(ChangeRing(F, CC)), QQ);
        vprint ModAbVarRec: "Done";
        if BaseField(C) cmpeq Rationals() then
            return true, C;
        else
            vprint ModAbVarRec: "Not over QQ";
        end if;
    end for;
    return false;
end intrinsic;



intrinsic ReconstructGenus2Curve(f::ModSym : prec:=80, ncoeffs:=10000) -> ModMatFldElt, SeqEnum
{
    FIXME
}
    P := PeriodsFromModSymb(f : prec:=prec, ncoeffs:=ncoeffs);
    P2, G2 := PeriodsWithMaximalOrder(P);
    return ReconstructGenus2Curve(P2);
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





