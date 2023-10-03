// Improving the computation of the integral homology for the sub/quo modular abelian varieties
// instead of calling IntegralHomology in Geometry/ModAbVar/homology.m

import "ComplexTori.m" : SkewSymmetricHomomorphismsRepresentation;

declare verbose HomologyModularSymbols, 2;

declare attributes ModSym:
  integral_homology_subquo, // SeqEnum[Tup<AlgMatElt, AlgMatElt>]
  homology_quo_in_sub,
  hecke_ring_subquo, // SeqEnum[SeqEnum[AlgMatElt]]
  maxend_subquo; // SeqEnum[Tup<AlgMatElt,SeqEnum[AlgMatElt]>] the second entry is the hecke ring

intrinsic IsogenyFromSub(f : Quotient:=false, MaximalEnd:=false) -> AlgMAtElt
{ The isogeny between subvariety and A', where A' can be the subvariaty/quotient variety of J_0(N) associated to f (with maximal endomorphism ring), i.e., how to write the (integral homology) basis for the quotient in terms of the basis for the subvariety}
  if not assigned f`integral_homology_subquo then
    _ := IntegralHomology(f);
  end if;
  R := IdentityMatrix(Integers(), Dimension(f));
  if Quotient then
    // sub to quotient
    R := f`homology_quo_in_sub;
  end if;
  if MaximalEnd then
    // Af to Af^max
    Rtomax := IsogenyToMaximalEndomomorphism(f : Quotient:=Quotient);
    R := Rtomax*R;
  end if;
  return R;
end intrinsic;

intrinsic IntegralHomology(f::ModSym : Quotient:=false, MaximalEnd:=false) -> AlgMatElt, AlgMatElt
{ Change of basis matrix from Basis(f)  to the integral homology basis for the abelian subvariety (or quotient) of J_0(N) associated to f and the intersection pairing with the respect to the integral basis}
  if not assigned f`integral_homology_subquo then
    A := AmbientSpace(f);
    vprintf HomologyModularSymbols: "IntegralHomology: Computing Lattice(AmbientSpace(f))...";
    vtime HomologyModularSymbols:
    L, phi := Lattice(A);

    CS := CuspidalSubspace(A);
    // compute an integral basis for CS
    vprintf HomologyModularSymbols: "IntegralHomology: Computing BoundaryMap...";
    vtime HomologyModularSymbols:
    delta := Matrix(Basis(L)) * Matrix(Integers(), BoundaryMap(A));
    // B is an integral basis for CS
    B := [phi(b) : b in Basis(Kernel(delta))];
    fromCS := Matrix(Integers(), [Eltseq(elt) : elt in B]);

    vprintf HomologyModularSymbols: "IntegralHomology: Computing S: B -> Basis(CS)...";
    vtime HomologyModularSymbols:
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
        vprintf HomologyModularSymbols: "IntegralHomology: Rank(H) = %o, desired_rank = %o\n", Rank(H), desired_rank;
        vprintf HomologyModularSymbols: "IntegralHomology: H = %o x %o matrix\n", Nrows(H), Ncols(H);
        vprintf HomologyModularSymbols: "IntegralHomology: V = %o x %o matrix\n", Nrows(V), Ncols(V);
        p := NextPrime(p);
        while Level(f) mod p eq 0 do
            p := NextPrime(p);
        end while;
        // Hecke operator with respect to the integral basis
        vprintf HomologyModularSymbols: "p = %o\n", p;
        Tp := Matrix(Integers(), S*HeckeOperator(CS, p)*S1);
        h := ChangeRing(MinimalPolynomial(HeckeOperator(f, p)), Integers()); //degree d/2
        hp := Evaluate(h, Tp);
        H := HorizontalJoin(H, hp);
        V := VerticalJoin(V, hp);
    end while;
    vprintf HomologyModularSymbols: "IntegralHomology: Rank(H) = %o, desired_rank = %o\n", Rank(H), desired_rank;
    vprintf HomologyModularSymbols: "IntegralHomology: H = %o x %o matrix\n", Nrows(H), Ncols(H);
    vprintf HomologyModularSymbols: "IntegralHomology: V = %o x %o matrix\n", Nrows(V), Ncols(V);

    vprintf HomologyModularSymbols: "IntegralHomology: Computing Hsub: Kernel(H)...";
    vtime HomologyModularSymbols:
    // Hsub represents the Z^d = H[If] \hookrightarrow H = Z^#B = CuspdalSubspace(A)
    // where If := Ker (TT -> Z[...an(f)...]) T_n -> an(f), and min poly of an(f) is h
    Hsub := KernelMatrix(H);

    // TODO: can one avoid the SmithForm?
    vprintf HomologyModularSymbols: "IntegralHomology: Computing Hquo: SmithForm(V)...";
    vtime HomologyModularSymbols:
    // D = VerticalJoin(DiagonalMatrix([1,1,...,k,0,0,0,0]), ZeroMatrix(Ncold(D), Ncols(D)))
    D, _, Q := SmithForm(V);
    if Nrows(D) gt 0 then
      assert Diagonal(D)[Ncols(D)-Dimension(f)+1..Ncols(D)] eq [0 : _ in [1..Dimension(f)]];
    end if;

    // this basis projects down to the standard basis of (H/If H)_free
    // these are basis for Hquo
    vprintf HomologyModularSymbols: "IntegralHomology: Computing Hquo: Q^-1 (%o x %o)...", Nrows(Q), Ncols(Q);
    vtime HomologyModularSymbols:
    // Hquo: Z^d = (H/If)_free -> H = Z^#B = CuspdalSubspace(A)
    // that projects down to a basis of (H/If)_free
    Hquo := Solution(Q, HorizontalJoin(ZeroMatrix(Integers(), Dimension(f), Nrows(Q) - Dimension(f)), IdentityMatrix(Integers(), Dimension(f))));
    // Alternatively:
    // Hquo := Submatrix(Q^-1, Nrows(Q) - Dimension(f) + 1, 1, Dimension(f), Ncols(Q));
    // but we dont need to invert the full matrix

    if Nrows(V) + Ncols(V) lt 2000 then // as this gets expensive
      vprintf HomologyModularSymbols: "IntegralHomology: Asserting that the basis of (H/If H) is correct...";
      vtime HomologyModularSymbols:
      assert Rank(VerticalJoin(V, Hquo)) eq Dimension(CS);
    end if;

    //this is the projection of H_sub in (H/If H)_free
    Hsub_in_Hquo := Hsub*Submatrix(Q, 1, Ncols(Q) - Dimension(f) + 1, Nrows(Q), Dimension(f));

    //we now invert Hsub_in_Hquo not caring about rescaling
    Hquo_in_Hsub := Matrix(Rationals(), Hsub_in_Hquo)^-1;

    //Denominator(Hquo_in_Hsub);
    Hquo_in_Hsub *:= Denominator(Hquo_in_Hsub);
    Hquo_in_Hsub := Matrix(Integers(), Hquo_in_Hsub);

    vprintf HomologyModularSymbols: "IntegralHomology: H[If] in terms of Basis(f)...";
    vtime HomologyModularSymbols:
    S := Matrix(Integers(), KernelMatrix(VerticalJoin( Matrix(Rationals(), Hsub*fromCS), -Matrix([Eltseq(b) : b in Basis(f)]))));
    assert Submatrix(S, 1,1, Dimension(f), Dimension(f)) eq 1;
    // how to write Hsub basis in terms of Basis(f)
    Hsub_in_Bf := Submatrix(S, 1,1 + Dimension(f), Dimension(f), Dimension(f));

    // how to write Hquo in terms of Basis(f)
    Hquo_in_Bf := Hquo_in_Hsub*Hsub_in_Bf;

    vprintf HomologyModularSymbols: "IntegralHomology: Computing IntersectionPairing(f)...";
    vtime HomologyModularSymbols:
    Ef := IntersectionPairing(f);
    Esub, Equo := Explode([Matrix(Integers(), A*Denominator(A)) where A := S*Ef*Transpose(S) where S:=Matrix(Rationals(), elt) : elt in [Hsub_in_Bf, Hquo_in_Bf]]);
    // Esub div:= GCD(Eltseq(Esub)); //???
    // Equo div:= GCD(Eltseq(Equo));
    f`integral_homology_subquo := [ <Hsub_in_Bf, Esub>, <Hquo_in_Bf, Equo> ];
    f`homology_quo_in_sub := Hquo_in_Hsub;
  end if;
  basis_in_Bf, Einbasis := Explode(f`integral_homology_subquo[Quotient select 2 else 1]);
  if MaximalEnd then
    Rtomax := IsogenyToMaximalEndomomorphism(f : Quotient:=Quotient);
    basis_in_Bf := Rtomax*basis_in_Bf;
    Einbasis := Rtomax*Einbasis*Transpose(Rtomax);
  end if;
  return basis_in_Bf, Einbasis;
end intrinsic;



intrinsic IntegralHeckeOperatorNew(f, n : Quotient:=false) -> AlgMatElt
{ A matrix representing the nth Hecke operator with respect to the integral homology basis M }
  S := Matrix(Rationals(), IntegralHomology(f : Quotient:=Quotient));
  Tn := HeckeOperator(f, n);
  return Matrix(Integers(),Transpose(S*Tn*S^-1));
end intrinsic;

intrinsic PrimitiveHeckeOperator(f) -> RngIntElt, FldNumElt
{ return n and an, such that an is a primitive element for the hecke algebra, i.e., Q(an) = Q[a1,a2,a3,...] }
  for n->an in Eltseq(PowerSeries(f, HeckeBound(f))) do
    if IsPrimitive(an) then
      return n, an;
    end if;
  end for;
  assert false;
end intrinsic;

intrinsic HeckeAlgebraIntegralBasis(f : Quotient:=false, MaximalEnd:=false) -> SeqEnum[AlgMatElt]
{ A sequence of matrices that form Z-basis for the Hecke ring associated to A_f ^quo/sub }
  if not assigned f`hecke_ring_subquo then
    OH, HtoOH := HeckeEigenvalueRing(f);
    n, an := PrimitiveHeckeOperator(f);
    Tns := [IntegralHeckeOperatorNew(f, n : Quotient:=q) : q in [false, true]];
    // this is a primitive element for the field, but perhaps not for the ring, see for example 94.2.a.b where a3 = 2sqrt(2)
    require Degree(OH) eq 2: "At the moment only implemented for dimension 2"; // we could also check for the order to be monogenic for higher degree, but further changes are needed below
    // an = a + b*OH.2
    a, b := Explode(ChangeUniverse(Eltseq(HtoOH(an)), Integers()));
    assert (HtoOH(an) - a) div b eq OH.2;
    assert &and[&and[elt mod b eq 0 : elt in Eltseq(Tn - a)] : Tn in Tns];
    Rs := [(Tn - a) div b : Tn in Tns];
    f`hecke_ring_subquo := [[IdentityMatrix(Integers(), Nrows(R)), R] : R in Rs];
  end if;
  if not MaximalEnd then
    return f`hecke_ring_subquo[Quotient select 2 else 1];
  else
    _, H := IsogenyToMaximalEndomomorphism(f : Quotient:=Quotient);
    return H;
  end if;
end intrinsic;

intrinsic IsogenyToMaximalEndomomorphism(f : Quotient:=false) -> AlgMatElt, SeqEnum[AlgMatElt]
{
  Retun the isogeny A -> A_max where End(A_max) := MaximalOrder(End(A) = HeckeAlgebraIntegralBasis(A) ) and A is the subvariety (or quotient) of J_0(N) associated to f, and the HeckeAlgebraIntegralBasis
}
  if not assigned f`maxend_subquo then
    OH := HeckeEigenvalueRing(f);
    require Degree(OH) eq 2 : "Only implemented for the case that the hecke ring has dimension two";
    g := 2;
    Hs := [HeckeAlgebraIntegralBasis(f : Quotient:=q) : q in [false, true]];
    if IsMaximal(OH) then
      f`maxend_subquo := [ <IdentityMatrix(Integers(), 2*g), elt> : elt in Hs];
    else
      gens := [elt[2] : elt in Hs];
      minpoly := MinimalPolynomial(gens[1]); // gens have the same minimal polynomial
      K<a> := NumberField(minpoly);


      // Now we compute the isogeny R, such that P*R is an abelian variety with maximal order
      D:= Discriminant(Integers(K));
      x := Parent(minpoly).1;
      sqrtDpoly := x^2 - D;
      rts := Roots(sqrtDpoly, K);
      rt := rts[1][1];
      f`maxend_subquo := [];
      for gen in gens do // now we handle the subvariety/quotient independently
        sqrtD := &+[c*gen^(i-1) : i->c in Eltseq(rt)];
        DpSqrtD := D*gen^0 + sqrtD;

        // right kernel of [2, D+Sqrt(D)]
        kernel := Transpose(KernelMatrix(Transpose(HorizontalJoin(2*gen^0, DpSqrtD))));
        // REMOVE: unused when when 2.28-3 arrives
        S, T, unused := SmithForm(Matrix(Integers(), kernel));
        assert Submatrix(S, 1, 1, 4, 4) eq 1;
        assert Submatrix(S, 5, 1, 4, 4) eq 0;
        Tinv := T^-1;

        // we now should compute a matrix R in M_2g(ZZ)
        // such that P2 = P*R, where End(P2) = ZZ[(D + Sqrt(D))/2]
        A := Submatrix(Tinv, 1, 5, 4, 4);
        B := Submatrix(Tinv, 5, 5, 4, 4);
        // The columns of Rtomax tell us how to write
        // the integral homology of A_max in terms of the integral homology of A
        // thus for consistency we store and return the transpose
        Rtomax := 2*A + DpSqrtD*B;

        newDpSqrtD := Matrix(Integers(), R^-1*DpSqrtD*R) where R:=Matrix(Rationals(), Rtomax);
        assert &and[elt mod 2 eq 0 : elt in Eltseq(newDpSqrtD)];
        newgen := Matrix(Integers(), newDpSqrtD div 2);
        assert IsMaximal(EquationOrder(MinimalPolynomial(newgen)));
        newH := LLL([IdentityMatrix(Integers(), 2*g), newgen]);
        Append(~f`maxend_subquo, <Transpose(Rtomax), newH>);
      end for;
    end if;
  end if;
  return Explode(f`maxend_subquo[Quotient select 2 else 1]);
end intrinsic;



intrinsic RationalSelfDualHomomorphisms(f::ModSym : Quotient:=false, MaximalEnd:=false) -> SeqEnum
  {
  A basis of self-dual homomorphisms from A -> A^v defined over Q, given as 2g by 2g where A is the subvariety (or quotient) of J_0(N) associated to f
    }
  Rs := HeckeAlgebraIntegralBasis(f : Quotient:=Quotient, MaximalEnd:=MaximalEnd);
  _, E := IntegralHomology(f : Quotient:=Quotient, MaximalEnd:=MaximalEnd);
  g := Nrows(E) div 2;
  //maps Omega to Omega dual are just E composed with endomorphisms, then saturated
  ERs := [E*elt : elt in Rs];
  // now we saturate
  M := Matrix([Eltseq(elt) : elt in ERs]);
  sERs := [Matrix(Integers(), 2*g, 2*g, Eltseq(elt)) : elt in Rows(Saturation(M))];
  pairs := [<1, elt> : elt in sERs]; // SkewSymmetricHomomorphismsRepresentation expects pairs
  pairs_skewZZ := SkewSymmetricHomomorphismsRepresentation(pairs);
  skewZZ := [elt[2] : elt in pairs_skewZZ];
  return LLL(skewZZ); // improve it by applying LLL
end intrinsic;
