// Improving the computation of the integral homology for the sub/quo modular abelian varieties
// instead of calling IntegralHomology in Geometry/ModAbVar/homology.m

import "ComplexTori.m" : SkewSymmetricHomomorphismsRepresentation;

declare verbose HomologyModularSymbols, 2;

declare attributes ModSym:
  prime_cutters,
  integral_homology_sub,
  integral_homology_quo,
  integral_cuspidal_ambient,
  homology_quo_in_sub,
  hecke_ring_subquo, // SeqEnum[SeqEnum[AlgMatElt]]
  maxend_subquo; // SeqEnum[Tup<AlgMatElt,SeqEnum[AlgMatElt]>] the second entry is the hecke ring

intrinsic IsogenyFromSub(f : Quotient:=false, MaximalEnd:=false) -> AlgMatElt
{ The isogeny between subvariety and A', where A' can be the subvariaty/quotient variety of J_0(N) associated to f (with maximal endomorphism ring), i.e., how to write the (integral homology) basis for the quotient in terms of the basis for the subvariety}
  R := IdentityMatrix(Integers(), Dimension(f));
  if Quotient and not assigned f`homology_quo_in_sub then
    // sub to quotient
    _ := IntegralHomologyQuo(f);
    R := f`homology_quo_in_sub;
  end if;
  if MaximalEnd then
    // Af to Af^max
    Rtomax := IsogenyToMaximalEndomomorphism(f : Quotient:=Quotient);
    R := Rtomax*R;
  end if;
  return R;
end intrinsic;



intrinsic IntegralBasisCuspidalAmbient(f::ModSym) -> Tup
  {returns tripe <S, S^-1, fromCStoAmbient> as matrices where S: IntegralBasis(CS) -> Basis(CS),
  and fromCStoAmbient: IntegralBasis(CS) -> AmbientSpace(f)}
  if not assigned f`integral_cuspidal_ambient then
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
    fromCStoAmbient := Matrix(Integers(), [Eltseq(elt) : elt in B]);

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
    f`integral_cuspidal_ambient := <S, S1, fromCStoAmbient>;
  end if;
  return f`integral_cuspidal_ambient;
end intrinsic;

intrinsic IntegralHomologySub(f::ModSym) -> AlgMatElt, AlgMatElt, AlgMatElt
{ Change of basis matrix from Basis(f)  to the integral homology basis for the abelian subvariety of J_0(N) associated to f and the intersection pairing with the respect to the integral basis}
  if not assigned f`integral_homology_sub then
    S, S1, fromCStoAmbient := Explode(IntegralBasisCuspidalAmbient(f));
    A := AmbientSpace(f);
    CS := CuspidalSubspace(A);
    // compute the set of primes that pins down the Vf
    f`prime_cutters := [];
    p := 1;
    desired_rank := Dimension(CS) - Dimension(f); // rank of If*H
    H := ZeroMatrix(Integers(), Dimension(CS), 0);
    // we are doing this method as NewSubspace basis is not always equipped with an integral, e.g., 285.2.a.d
    while Rank(H) ne desired_rank do
      vprintf HomologyModularSymbols: "IntegralHomology: Rank(H) = %o, desired_rank = %o\n", Rank(H), desired_rank;
      vprintf HomologyModularSymbols: "IntegralHomology: H = %o x %o matrix\n", Nrows(H), Ncols(H);
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
      Append(~f`prime_cutters, p);
    end while;
    vprintf HomologyModularSymbols: "IntegralHomologySub: Rank(H) = %o, desired_rank = %o\n", Rank(H), desired_rank;
    vprintf HomologyModularSymbols: "IntegralHomologySub: H = %o x %o matrix\n", Nrows(H), Ncols(H);

    vprintf HomologyModularSymbols: "IntegralHomologySub: Computing Hsub inside the CuspidalSubspace: Kernel(H)...";
    vtime HomologyModularSymbols:
    // Hsub represents the Z^d = H[If] \hookrightarrow H = Z^#B = CuspidalSubspace(A)
    // where If := Ker (TT -> Z[...an(f)...]) T_n -> an(f), and min poly of an(f) is h
    Hsub := KernelMatrix(H);

    vprintf HomologyModularSymbols: "IntegralHomologySub: H[If] in terms of Basis(f)...";
    vtime HomologyModularSymbols:
    // Hsub*fromCStoAmbient = IntegralBasis(f) -> AmbientSpace(f);
    // the other matrix is the Basis(f) in the coordinates of AmbientSpace(f)
    S := KernelMatrix(VerticalJoin( Matrix(Rationals(), Hsub*fromCStoAmbient), -Matrix([Eltseq(b) : b in Basis(f)])));
    // make it integral
    S := Matrix(Integers(), S);
    assert Submatrix(S, 1,1, Dimension(f), Dimension(f)) eq 1;
    // how to write Hsub basis in terms of Basis(f)
    // IntegralBasis(f) -> Basis(f)
    Hsub_in_Bf := Submatrix(S, 1,1 + Dimension(f), Dimension(f), Dimension(f));


    // now compute the polarization
    vprintf HomologyModularSymbols: "IntegralHomologySub: Computing IntersectionPairing(f)...";
    vtime HomologyModularSymbols:
    Ef := IntersectionPairing(f);
    Esub := S*Ef*Transpose(S) where S:=Matrix(Rationals(), Hsub_in_Bf);
    // make it inte/gral
    Esub := Matrix(Integers(), Esub*Denominator(Esub));

    f`integral_homology_sub := <Hsub_in_Bf, Esub, Hsub>;
  end if;

  return Explode(f`integral_homology_sub);
end intrinsic;






intrinsic IntegralHomologyQuo(f::ModSym) -> AlgMatElt, AlgMatElt
{ Change of basis matrix from Basis(f) to the integral homology basis for the abelian quotient of J_0(N) associated to f and the intersection pairing with the respect to the integral basis}
  if not assigned f`integral_homology_quo then
    Hsub_in_Bf, Esub, Hsub := IntegralHomologySub(f);
    S, S1, fromCStoAmbient := Explode(IntegralBasisCuspidalAmbient(f));
    A := AmbientSpace(f);
    CS := CuspidalSubspace(A);
    desired_rank := Dimension(CS) - Dimension(f); // rank of If*H
    M := ZeroMatrix(Integers(), 0, Dimension(CS));
    for p in f`prime_cutters do // these are computed in IntegralHomologySub
      vprintf HomologyModularSymbols: "IntegralHomologyQuo: M = %o x %o matrix\n", Nrows(M), Ncols(M);
      // Hecke operator with respect to the integral basis
      vprintf HomologyModularSymbols: "p = %o\n", p;
      Tp := Matrix(Integers(), S*HeckeOperator(CS, p)*S1);
      h := ChangeRing(MinimalPolynomial(HeckeOperator(f, p)), Integers()); //degree d/2
      hp := Evaluate(h, Tp);
      M := VerticalJoin(M, hp);
    end for;
    vprintf HomologyModularSymbols: "IntegralHomologyQuo: Rank(M) = %o, desired_rank = %o\n", Rank(M), desired_rank;
    assert Rank(M) eq desired_rank;
    vprintf HomologyModularSymbols: "IntegralHomologyQuo: M = %o x %o matrix\n", Nrows(M), Ncols(M);


    vprintf HomologyModularSymbols: "IntegralHomologyQuo: Computing Hquo: HermiteForm(Transpose(M))...";
    vtime HomologyModularSymbols:
    H, Q := HermiteForm(Transpose(M));
    H := Transpose(H);
    Q := Transpose(Q);
    // Q is a 2g(N) x 2g(N) matrix
    // M * Q = H, a matrix where the last 2g columns are zero
    assert IsZero(Submatrix(H, 1, Ncols(H) - Dimension(f)+1, Nrows(H), Dimension(f)));
    //this is the projection of H_sub in (H/If H)_free
    Hsub_in_Hquo := Hsub*Submatrix(Q, 1, Ncols(Q) - Dimension(f) + 1, Nrows(Q), Dimension(f));

    //we now invert Hsub_in_Hquo not caring about rescaling
    Hquo_in_Hsub := Matrix(Rationals(), Hsub_in_Hquo)^-1;

    //Denominator(Hquo_in_Hsub);
    Hquo_in_Hsub *:= Denominator(Hquo_in_Hsub);
    Hquo_in_Hsub := Matrix(Integers(), Hquo_in_Hsub);

    Equo := S*Esub*Transpose(S) where S:=Matrix(Rationals(), Hquo_in_Hsub);
    // make it integral
    Equo := Matrix(Integers(), Equo*Denominator(Equo));
    f`integral_homology_quo := <Hquo_in_Hsub*Hsub_in_Bf, Equo, Hquo_in_Hsub*Hsub>;
    f`homology_quo_in_sub := Hsub_in_Hquo;
  end if;
  return Explode(f`integral_homology_quo);
end intrinsic;


// TODO: clarify that in the paper we write things with a right action, i.e. the map F^m -> F^n is represented by a n x m matrix
// However, for purposes of efficiency Magma prefers the other way around
intrinsic IntegralHomology(f::ModSym : Quotient:=false, MaximalEnd:=false) -> AlgMatElt, AlgMatElt
{ Change of basis matrix from Basis(f)  to the integral homology basis for the abelian subvariety (or quotient) of J_0(N) associated to f and the intersection pairing with the respect to the integral basis}
  sic := Quotient select IntegralHomologyQuo else IntegralHomologySub;
  basis_in_Bf, Einbasis, basis_in_CS := sic(f);
  if MaximalEnd then
    Rtomax := IsogenyToMaximalEndomomorphism(f : Quotient:=Quotient);
    basis_in_Bf := Rtomax*basis_in_Bf;
    basis_in_CS := Rtomax*basis_in_CS;
    Einbasis := Rtomax*Einbasis*Transpose(Rtomax);
  end if;
  return basis_in_Bf, Einbasis, basis_in_CS;
end intrinsic;


intrinsic HomologyLattice(f::ModSym : Quotient:=false, MaximalEnd:=false) -> Lat, Map
{ A basis over the integers for the integral modular symbols H_1(A_f, \Z)for the abelian subvariety (or quotient) of J_0(N) associated to f.
The default behaviour of this intrinsic returns the same lattice as Lattice(f), but via a different algorithm }
  _, _, basis_in_CS := IntegralHomologySub(f : Quotient:=Quotient, MaximalEnd:=MaximalEnd);
  fromCStoAmbient := IntegralBasisCuspidalAmbient(f)[3];
  L := Lattice(basis_in_CS*fromCStoAmbient);
  return L, hom<L->AmbientSpace(f) | x :-> f!x>;
end intrinsic;

intrinsic IntersectionPairingIntegral(f::ModSym : Quotient:=false, MaximalEnd:=false) -> AlgMatElt
{ The intersection pairing matrix on the basis for the integral homology of A_f.}
  return E where _, E := IntegralHomology(f : Quotient:=Quotient, MaximalEnd:=MaximalEnd);
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
  idx := Quotient select 2 else 1;
  if not assigned f`hecke_ring_subquo then
    f`hecke_ring_subquo := [];
  end if;
  if not IsDefined(f`hecke_ring_subquo, idx) then
    OH, HtoOH := HeckeEigenvalueRing(f);
    n, an := PrimitiveHeckeOperator(f);
    Tn := IntegralHeckeOperatorNew(f, n : Quotient:=Quotient);
    // this is a primitive element for the field, but perhaps not for the ring, see for example 94.2.a.b where a3 = 2sqrt(2)
    require Degree(OH) eq 2: "At the moment only implemented for dimension 2"; // we could also check for the order to be monogenic for higher degree, but further changes are needed below
    // an = a + b*OH.2
    a, b := Explode(ChangeUniverse(Eltseq(HtoOH(an)), Integers()));
    assert (HtoOH(an) - a) div b eq OH.2;
    assert &and[elt mod b eq 0 : elt in Eltseq(Tn - a)];
    R := (Tn - a) div b;
    f`hecke_ring_subquo[idx] := [IdentityMatrix(Integers(), Nrows(R)), R];
  end if;
  if not MaximalEnd then
    return f`hecke_ring_subquo[idx];
  else
    // IsogenyToMaximalEndomomorphism computes the new HeckeRing
    _, H := IsogenyToMaximalEndomomorphism(f : Quotient:=Quotient);
    return H;
  end if;
end intrinsic;

intrinsic IsogenyToMaximalEndomomorphism(f : Quotient:=false) -> AlgMatElt, SeqEnum[AlgMatElt]
{
  Retun the isogeny A -> A_max where End(A_max) := MaximalOrder(End(A) = HeckeAlgebraIntegralBasis(A) ) and A is the subvariety (or quotient) of J_0(N) associated to f, and the HeckeAlgebraIntegralBasis
}
  idx := Quotient select 2 else 1;
  if not assigned f`maxend_subquo then
    f`maxend_subquo := [];
    OH := HeckeEigenvalueRing(f);
  end if;
  if not IsDefined(f`maxend_subquo, idx) then
    OH := HeckeEigenvalueRing(f);
    require Degree(OH) eq 2 : "Only implemented for the case that the hecke ring has dimension two";
    g := 2;
    H := HeckeAlgebraIntegralBasis(f : Quotient:=Quotient);
    if IsMaximal(OH) then
      f`maxend_subquo[idx] := <IdentityMatrix(Integers(), 2*g), H>;
    else
      gen := H[2];
      minpoly := MinimalPolynomial(gen);
      K<a> := NumberField(minpoly);

      // Now we compute the isogeny R, such that P*R is an abelian variety with maximal order
      D:= Discriminant(Integers(K));
      x := Parent(minpoly).1;
      sqrtDpoly := x^2 - D;
      rts := Roots(sqrtDpoly, K);
      rt := rts[1][1];

      den := LCM([Denominator(c) : c in Eltseq(rt)]);
      // den * Sqrt(D)
      sqrtD := &+[Numerator(c)*(den div Denominator(c))*gen^(i-1) : i->c in Eltseq(rt)];
      // den(D + Sqrt(D))
      DpSqrtD := den*D*gen^0 + sqrtD;
      assert BaseRing(DpSqrtD) cmpeq Integers();

      // right kernel of [2, D+Sqrt(D)] = right kernel of [den*2, den*(D+Sqrt(D))]
      kernel := Transpose(KernelMatrix(Transpose(HorizontalJoin(den*2*gen^0, DpSqrtD))));
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
      Rtomax := den*2*A + DpSqrtD*B;

      newDpSqrtD := Matrix(Integers(), R^-1*DpSqrtD*R) where R:=Matrix(Rationals(), Rtomax);
      assert &and[elt mod 2 eq 0 : elt in Eltseq(newDpSqrtD)];
      newgen := Matrix(Integers(), newDpSqrtD div (2*den));
      assert IsMaximal(EquationOrder(MinimalPolynomial(newgen)));
      newH := LLL([IdentityMatrix(Integers(), 2*g), newgen]);
      f`maxend_subquo[idx] := <Transpose(Rtomax), newH>;
    end if;
  end if;
  return Explode(f`maxend_subquo[idx]);
end intrinsic;



intrinsic RationalSelfDualHomomorphisms(f::ModSym : Quotient:=false, MaximalEnd:=false) -> SeqEnum
  {
  A basis of self-dual homomorphisms from A -> A^v defined over Q, given as 2g by 2g where A is the subvariety (or quotient) of J_0(N) associated to f
    }
  Rs := HeckeAlgebraIntegralBasis(f : Quotient:=Quotient, MaximalEnd:=MaximalEnd);
  // this is a QQ-polarization
  _, E := IntegralHomology(f : Quotient:=Quotient, MaximalEnd:=MaximalEnd);
  g := Nrows(E) div 2;
  //maps Omega to Omega dual are just E composed with endomorphisms, then saturated
  ERs := [E*elt : elt in Rs];
  // now we saturate
  M := Saturation(Matrix([Eltseq(elt) : elt in ERs]));
  sERs := [Matrix(Integers(), 2*g, 2*g, Eltseq(elt)) : elt in Rows(M)];
  pairs := [<1, elt> : elt in sERs]; // SkewSymmetricHomomorphismsRepresentation expects pairs
  pairs_skewZZ := SkewSymmetricHomomorphismsRepresentation(pairs);
  skewZZ := [elt[2] : elt in pairs_skewZZ];
  return LLL(skewZZ); // improve it by applying LLL
end intrinsic;
