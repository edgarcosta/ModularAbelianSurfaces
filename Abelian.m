
intrinsic Imaginary(M::Mtrx[FldCom]) -> Mtrx[FldRe]
{ The imaginary part of M }
    return Matrix([[Imaginary(elt) : elt in Eltseq(row)] : row in Rows(M)]);
end intrinsic;


intrinsic DualLattice(Omega::ModMatFldElt) -> ModMatFldElt
{
    Input: Omega, g by 2g complex matrix, representing a complex torus A
    Output: Omega^v, g by 2g complex matrix, representing the dual torus A^v with the dual basis for the lattice.
}
    CC<I> := BaseRing(Omega);
    g := Nrows(Omega);
    B := HorizontalJoin(IdentityMatrix(CC, g), I*IdentityMatrix(CC, g));
    P := Imaginary(Transpose(B) * Conjugate(Omega));
    Bprime := B * ChangeRing(Transpose(Inverse(P)), CC);
    return Bprime;
end intrinsic;

intrinsic DualLatticeWithRespectToPairing(Omega::ModMatFldElt, E::AlgMatElt) -> ModMatFldElt
{
    Input: Omega g by 2g complex matrix arising from an abelian variety A/Q with a Q-basis of H^0(A,Omega^1), together with an (alternating) 2g by 2g integer matrix E representing a polarization A to A^v (defined over Q) with respect to the Z-bases of homology given by Omega and the Omega^v given by the DualLattice function.

Output: Omega^v_Q, g by 2g complex matrix arising from the dual abelian variety A^v together with the Q-basis of H^0(A^v,\Omega^1) that pulls back under A to A^v to the specified Q-basis of H^0(A,\Omega^1)
}
    CC<I> := BaseRing(Omega);
    OmegaDualCC := DualLattice(Omega);
    ECC := TangentRepresentation(E, Omega, OmegaDualCC);
    return Inverse(ECC)*OmegaDualCC;
end intrinsic;


intrinsic SelfDualHomomorphisms(Omega::ModMatFldElt, E::AlgMatElt) -> SeqEnum, Map
{
    Input: Omega, 2g by 2g complex matrix representing a complex torus A, together with an (alternating) 2g by 2g integer matrix E irepresenting a polarization A to A^v (defined over Q)

    Output: A Z-basis of self-dual homomorphisms from A to A^v represented as 2g by 2g integer matrices, along with their g by g tangent representation
}
    function SkewSymmetricHomomorphisms(HomRep)
        if #HomRep eq 0 then
            return HomRep;
        end if;
        Rs := [elt[2] : elt in HomRep];
        M := Matrix(Integers(), [Eltseq(Ri + Transpose(Ri)) : Ri in Rs]);
        rows := Rows(KernelMatrix(M));
        PA := Parent(HomRep[1][1]);
        PR := Parent(HomRep[1][2]);
        return [ [* &+[PA | row[i]*HomRep[i][1] : i->_ in HomRep], &+[PR | row[i]*HomRep[i][2] : i->_ in HomRep] *] : row in rows ];
    end function;

    pairs, hToL := GeometricHomomorphismRepresentation(Omega, DualLatticeWithRespectToPairing(Omega, E), RationalsExtra(Precision(BaseRing(Omega))));
    skewZZ := SkewSymmetricHomomorphisms(pairs);
    return skewZZ, hToL;
end intrinsic;

intrinsic RationalSelfDualHomomorphisms(Omega::ModMatFldElt, E::AlgMatElt) -> SeqEnum
{
    Input: Omega, 2g by 2g complex matrix representing a complex torus A, together with an (alternating) 2g by 2g integer matrix E irepresenting a polarization A to A^v (defined over Q)

    Output: A basis of self-dual homomorphisms from A -> A^v defined over Q, given as 2g by 2g integer matrices, along with their g by g tangent representation
}
    basis, hToL := SelfDualHomomorphisms(Omega, E);
    L := Codomain(hToL);
    Gp, Gf, Gphi := AutomorphismGroupPari(L);
    // this works even though it is called "EndomorphismRepresentation" instead of "HomomorphismRepresentation"
    basisQQ, _ := EndomorphismRepresentation([elt : elt in basis], [* Generators(Gp), Gphi *]);
    return basisQQ;
end intrinsic;


// To show up at some point in Endomorpisms package
intrinsic AdjugateMatrix(M::Mtrx) -> Mtrx
{
    The adjugate matrix, i.e., Adj(A)*A = det(A) = A*Adj(A)
}
    return Matrix(BaseRing(M), [[Cofactor(M, j, i) : j in [1..Ncols(M)]] : i in [1..Nrows(M)]]);
end intrinsic;

// To show up at some point in Endomorpisms package
intrinsic PrincipalMinors(M::Mtrx) -> SeqEnum[FldElt]
{Return the principal minors of M}
    require Nrows(M) eq Ncols(M): "the matrix needs to be square";
    return [Minor(M, I, I) where I := [j..n] : j  in [1..n]] where n:=Nrows(M);
end intrinsic;


function PfaffianAndMinors(Es, P)

    CC<I> := BaseRing(P);
    n := #Es;
    R := PolynomialRing(Integers(), n);
    RCC := PolynomialRing(CC, n);


    ER := &+[R.i * ChangeRing(Ei, R) : i->Ei in Es];
    pf := Pfaffian(ER);
    PRCC := ChangeRing(P, RCC);
    PRCC_star := ChangeRing(Conjugate(Transpose(P)), RCC);
    ERCC_inverse := ChangeRing(AdjugateMatrix(ER), RCC);
    M := I*PRCC*ERCC_inverse*PRCC_star;
    minors := PrincipalMinors(M);

    RRR := PolynomialRing(RealField(CC), n);
    function RealPolynomial(f)
        coeff, mon := CoefficientsAndMonomials(f);
        return &+[Real(c)*RRR!mon[i] : i->c in coeff];
    end function;
    return pf, [RealPolynomial(elt) : elt in minors];
end function;


intrinsic PrincipalPolarizations(Omega::ModMatFldElt, B::SeqEnum[AlgMatElt]) -> SeqEnum[AlgMatElt]
{
    Return all principal polarizations on Omega in the span of B := [B_1, B_2] up to automorphism, where Omega is the period matrix of A, and B_i are self-dual homomorphisms A to A^v linearly independent.

}
    n := #B;
    require n eq 2: Sprintf("Expected #B = 2, got #B = %o. We have only implemented for combinations of two polarizations, as we rely on computing integral points on a conic in A^2", n);
    pf, minors := PfaffianAndMinors(B, Omega);
    CC := BaseRing(Parent(minors[1]));
    // extract conic
    abc := [MonomialCoefficient(pf, [2-i,i]) : i in [0..2]];
    // extract combinations with determinant 1
    sols := IntegralPointsConic(abc, [1,-1]);
    solutions := &cat [SetToSequence(elt) : elt in sols];
    // for each connic there are 2 connected components, the action by tau moves along component, and the action by -1 swaps them
    // tau is (the square of) the fundamental unit (if its norm is -1) with both embeddings positive
    solutions cat:= [[-elt[1], -elt[2]] : elt in solutions];
    // the positivity condition is picking one of the 4 connected components of the two conics
    ppols := [&+[ coord[i]*B[i] : i in [1..n] ] : coord in solutions | &and[ Evaluate(m, coord) gt CC`epsinv : m in minors]];
    return ppols;
end intrinsic;


intrinsic RationalPrincipalPolarizations(Omega, E) -> SeqEnum
{
    Returns all rational principal polarizations for Omega with the pairing E, together with the change of basis.
}
    self_dual_homomorphisms := [elt[2] : elt in RationalSelfDualHomomorphisms(Omega, E)];
    PPs := PrincipalPolarizations(Omega, self_dual_homomorphisms);
    PPs := [Matrix(Integers(), elt) : elt in PPs];
    CC := BaseRing(Omega);
    return [<Omega*Transpose(Matrix(CC, F)), Transpose(F)> where _, F := FrobeniusFormAlternating(elt) : elt in PPs];
end intrinsic;

