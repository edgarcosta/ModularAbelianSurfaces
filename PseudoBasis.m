intrinsic PseudoBasis(R::AlgMatElt[RngInt] : TryPrincipalize := false) -> SeqEnum
  {R is a square matrix of size d*n, describing the action of an element alpha
   on ZZ^(d*n) acting on rows on the right, with irreducible minimal polynomial
   of degree d.  Returns a ZZ[alpha]-pseudo basis for Lambda, in the form
   <RngOrdFracIdl, ModRngElt>, supposing that ZZ[alpha] is Dedekind.
   if TryPrincipalize, it will try to make the coefficient ideals trivial.}

  dn := Nrows(R);
  assert dn eq Ncols(R);  // square
  f := MinimalPolynomial(R);
  d := Degree(f);
  assert dn mod d eq 0;
  n := dn div d;
  assert CharacteristicPolynomial(R) eq f^n;

  K<alpha> := NumberField(f);
  ZZK := EquationOrder(K);
  assert IsMaximal(ZZK);
     // sorry, only currently implemented for monogenic
     // to get general case, work with an integral basis of ZZK

  // write Lambda tensor QQ = K^n
  N := EchelonForm(ChangeRing(R,K) - alpha*IdentityMatrix(K,dn));
  assert &and[IsZero(N[i]) : i in [dn-n+1..dn]];
  N := RowSubmatrix(N,[1..dn-n]);
  pivots := [PivotColumn(N,i) : i in [1..Nrows(N)] | not IsZero(N[i])];
  assert #pivots eq n;  // otherwise, huh?
  inds := [j : j in [1..dn] | j notin pivots];

  // the only step with content, just compute the row span
  A := -ColumnSubmatrix(N,inds);
  U := VerticalJoin([A,IdentityMatrix(K,n)]);
  E, T := HermiteForm(PseudoMatrix([1*ZZK : i in [1..Nrows(U)]], U));

  Emat := Matrix(E);
  basind := [i : i in [1..Nrows(Emat)] | not IsZero(Emat[i])];

  CI := [CoefficientIdeals(E)[k] : k in basind];
  // convert from K-linear combo back to ZZ-linear combo, can this be described
  // more simply by a matrix calculation?  
  Lambdabas := 
    [&+[&+[Eltseq(K!T[k][i])[j]*(R^(j-1))[i] : j in [1..d]] : i in [1..dn]] : k in basind];
  assert #Lambdabas eq n;
  if TryPrincipalize then
    RQQ := ChangeRing(R,Rationals());
    for k := 1 to n do
      bl, nu := IsPrincipal(CI[k]);
      if bl then
        CI[k] := 1*ZZK;
        Lambdabas[k] := ChangeRing(Lambdabas[k],Rationals())*&+[Eltseq(K!nu)[j]*RQQ^(j-1) : j in [1..d]];
      end if;
    end for;  
  end if;
  return [<CI[k], Lambdabas[k]> : k in [1..n]];
end intrinsic;

CheckPseudoBasis := function(P, R);
  ZZK := Order(P[1][1]);
  K := NumberField(ZZK);
  d := Degree(K);
  assert MinimalPolynomial(R) eq MinimalPolynomial(K.1);
  ZZspan := [];
  RQQ := ChangeRing(R,Rationals());
  for aav in P do
    aa := aav[1];
    v := ChangeRing(aav[2],Rationals());
    ZZspan cat:= [Parent(aav[2]) | v*&+[Eltseq(K!beta)[j]*RQQ^(j-1) : j in [1..d]]
                : beta in Basis(aa)];
  end for;
  return Determinant(Matrix(ZZspan)) in [-1,1];
end function;

/*
R := Matrix(4, 4, [ -3, -2, 0, 0, -2, 2, 0, 0, -16, -6, 3, -1, -4, -4, 2, -4 ]);
P := PseudoBasis(R);
P;
CheckPseudoBasis(P, R : TryPrincipalize := true);

R := Matrix(2, 2, [ 0, 1, 15, 0 ]);
P := PseudoBasis(R);
P;
CheckPseudoBasis(P, R);
*/
