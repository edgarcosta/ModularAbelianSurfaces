// One can do better than this for trivial character, N square free, and when cond(chi) is a proper divisor of N, see Stein 9.19,9.21,9.22,
// but this bound (due to Buzzard) works for all spaces M_k(N,chi) and is best possible in some cases, see Stein 9.20
intrinsic SturmBound (N::RngIntElt, k::RngIntElt) -> RngIntElt
{ Sturm bound for space of modular forms of level N weight k and any character. }
    require N ge 1 and k ge 1: "Level N and weight k must be positive integers";
    m := Index(Gamma0(N));
    return Integers()!Floor(k*m/12);
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
