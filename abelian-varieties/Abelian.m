
intrinsic DualLattice(Omega::ModMatFldElt) -> ModMatFldElt
{
}
    CC<I> := BaseRing(Omega);
    g := Nrows(Omega);
    B := HorizontalJoin(IdentityMatrix(CC, g), I*IdentityMatrix(CC, g));
    P := ImaginaryPart(Transpose(B) * Conjugate(Omega));
    Bprime := B * ChangeRing(Transpose(Inverse(P)), CC);
    return Bprime;
end intrinsic;

intrinsic DualLatticeWithRespectToPairing(Omega::ModMatFldElt, E::AlgMatElt) -> ModMatFldElt
{ 
}
    CC<I> := BaseRing(Omega);
    OmegaDualCC := DualLattice(Omega);
    ECC := TangentRepresentation(E, Omega, OmegaDualCC);
    return Inverse(ECC)*OmegaDualCC;
end intrinsic;


intrinsic SelfDualHomomorphismsg(Omega::ModMatFldElt, E::AlgMatElt) -> SeqEnum, Map
{
}
    pairs, hToL := GeometricHomomorphismRepresentation(Omega, DualLatticeWithRespectToPairing(Omega, E), RationalsExtra(Precision(BaseRing(Omega))));
    skewZZ := [* elt : elt in pairs | elt[2] + Transpose(elt[2]) eq 0 *];
    return skewZZ, hToL;
end intrinsic;

intrinsic RationalPolarizationBasis(Omega::ModMatFldElt, E::AlgMatElt) -> SeqEnum
{
}
    basis, hToL := SelfDualHomomorphisms(Omega, E);
    L := Codomain(hToL);
    Gp, Gf, Gphi := AutomorphismGroupPari(L);
    // this works even though it is called "EndomorphismRepresentation" instead of "HomomorphismRepresentation"
    basisQQ, _ := EndomorphismRepresentation([elt : elt in basis], [* Generators(Gp), Gphi *]);
    return basisQQ;
end intrinsic;


// To show up at some point in Endomorpisms package
intrinsic AdjugateMatrix(M::AlgMatElt) -> AlgMatElt
{The adjugate matrix, i.e., Adj(A)*A = det(A) = A*Adj(A)}
    return Matrix(BaseRing(M), [[Cofactor(M, j, i) : j in [1..Ncols(M)]] : i in [1..Nrows(M)]]);
end intrinsic;

// To show up at some point in Endomorpisms package
intrinsic PrincipalMinors(M::ModMatFldElt) -> SeqEnum[FldElt]
{Return the principal minors of M}
    require Nrows(M) eq Ncols(M): "the matrix needs to be square";
    return [Minor(M, I, I) where I := [j..n] : j  in [1..n]] where n:=Nrows(M);
end intrinsic;


function RealPolynomial(f)
    coeff, mon := CoefficientsAndMonomials(f);
    return &+[Real(c)*mon[i] : i->c in coeff];
end function;



function PfaffianAndMinors(Es, P)
    CC<I> := BaseRing(P);
    n := #Es;
    R<[x]> := PolynomialRing(Integers(), n);
    RCC<[y]> := PolynomialRing(CC, n);
    ER := &+[R.i * ChangeRing(Ei, R) : i->Ei in Es];
    pf := Pfaffian(ER);
    PRCC := ChangeRing(P, RCC);
    PRCC_star := ChangeRing(Conjugate(Transpose(P)), RCC);
    ERCC_inverse := ChangeRing(AdjugateMatrix(ER), RCC);
    M := I*PRCC*ERCC_inverse*PRCC_star;
    minors := PrincipalMinors(M);
    return pf, [RealPolynomial(elt) : elt in minors];
end function;


function _IsPolarization(coord, pf, minors : Principal:=false)
// Tests whether or not &+[ coord[i]*Es[i] : i in [1..n] ] defines a polarization on P.

// check determinant
det := Evaluate(pf, coord)^2;
if det eq 0 or (Principal and det ne 1) then
    return false;
end if;
// check positivity
CC := BaseRing(Parent(minors[1]));
for m in minors do
    if Evaluate(m, coord) lt CC`epsinv then
        return false;
    end if;
end for;

return true;
end function;


intrinsic PrincipalPolarizations(Omega::ModMatFldElt, B::SeqEnum[AlgMatElt]) -> SeqEnum[AlgMatElt]
{
    Return all principal polarizations on Omega in the span of B := [B_1, B_2] up to automorphism, where Omega is the period matrix of A, and B_i are self-dual homomorphisms A to A^v linearly independent.

}
    require #B eq 2: "Only implemented for combinations of two polarizations, as we rely on computing integral points on a conic in A^2";
    pf, minors := PfaffianAndMinors(B, Omega);
    // extract conic
    abc := [MonomialCoefficient(pf, [2-i,i]) : i in [0..2]];
    // extract combinations with determinant 1
    solutions := &cat [SetToSequence(elt) : elt in IntegralPointsConic(abc, [1,-1])];
    // check the positivity condition
    ppols := [&+[ tup[i]*B[i] : i in [1..n] ] : tup in solutions | _IsPolarization(tup, pf, minors : Principal:=true)];
    return ppols;
end intrinsic;
