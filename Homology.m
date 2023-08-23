// Improving the computation of the integral homology for the sub/quo modular abelian varieties
// instead of calling IntegralHomology in Geometry/ModAbVar/homology.m

declare attributes ModSym:
  integral_homology_subquo; // SeqEnum[Tup]

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

