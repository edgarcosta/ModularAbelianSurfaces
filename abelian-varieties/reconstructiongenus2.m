/***
 *  Reconstruction algorithms
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */

/* The conventions on period matrices are different in these programs, since
 * Guardia uses the current ones. We therefore leave the more elegant
 * conventions of Birkenhake--Lange, but only locally */


intrinsic ModularToIgusaClebshInvariants(H::SeqEnum) -> SeqEnum
{ Convert Modular invariants to Igusa-Clebsh invariants. }
  assert #H eq 4;
  h4, h6, h10, h12 := Explode(H);
  if Abs(h10) gt  10^(-Precision(Parent(h10))/2) then
    I2 := h12/h10;
    I4 := h4;
    I6 := (I2*I4 - 2*h6)/3;
    I10 := h10;
  else
    // Same as above, but we avoid dividing by h10
    I2 := h12;
    I4 := h4 * h10^2; // usually h4
    I6 := (I2*I4 - 2*h6*h10^3)/3;
    I10 := h10^6;
  end if;
  return WPSNormalize([2,4,6,10], [I2, I4, I6, I10]);
end intrinsic;

intrinsic ModularToIgusaInvariants(H::SeqEnum) -> SeqEnum
{ Convert Modular invariants to Igusa invariants. }
  I2, I4, I6, I10 := Explode(ModularToIgusaClebshInvariants(H));
  J2  := (1/8)*I2;
  J4  := (1/96)*(4*J2^2 - I4);
  J6  := (1/576)*(8*J2^3 - 160*J2*J4 - I6);
  J8  := (1/4)*(J2*J6 - J4^2);
  J10 := (1/4096)*I10;
  return WPSNormalize([2,4,6,8,10], [J2, J4, J6, J8, J10]);
end intrinsic;




function BigAndSmallPeriodMatrix(inp)
  CC := BaseRing(Parent(inp));
  g := Nrows(inp);
  assert Ncols(inp) in [g, 2*g];
  if Ncols(inp) eq g then
    tau := inp;
    assert IsSmallPeriodMatrix(tau);
    P := HorizontalJoin(tau, IdentityMatrix(CC, g));
  else
    P := inp;
    assert IsBigPeriodMatrix(P);
    tau := SmallPeriodMatrix(P);
  end if;
  return P, tau;
end function;

function ReconstructCurveG2CC(inp)
  // Reconstruct curve from a small/big period matrix P, returned over CC
  CC := BaseRing(Parent(inp));
  g := Nrows(inp);
  assert g eq 2;
  P, tau := BigAndSmallPeriodMatrix(inp);


  /* Reduce small period matrix */
  taunew, gamma := ReduceSmallPeriodMatrix(tau);
  Imtaunew := Matrix([ [ Im(c) : c in Eltseq(row) ] : row in Rows(taunew) ]);

  vprint CurveRec, 2 : "Eigenvalues of imaginary part of reduced tau:";
  vprint CurveRec, 2 : [ ComplexField(5) ! tup[1] : tup in Eigenvalues(Imtaunew) ];

  g := Nrows(P);
  /* Calculate corresponding big period matrix */
  A := Submatrix(gamma, 1,1, g,g);
  B := Submatrix(gamma, 1,g+1, g,g);
  C := Submatrix(gamma, g+1,1, 2,2);
  D := Submatrix(gamma, g+1,g+1, g,g);
  Pnew := P * Transpose(BlockMatrix([[A, B], [C, D]]));
  P2new := Submatrix(Pnew, 1,3, 2,2);
  P2inew := P2new^(-1);

  /* Jeroen from the future:
   * There is an alternative, even in the arithmetic case. Take a Rosenhain model using fast theta calculations. Then determine the period matrix of that model, which is also fast. An invocation of the endomorphism/automorphism functionality will give you a matrix that you can use to transform to a curve which has exactly the given big period matrix, and then one algebraizes as usual. So there is no real need for theta derivatives. It was fun while it lasted, however.
   * Edgar from the future:
   * look into genus 3
  */

  /* Calculation of theta derivatives at odd two-torsion points */
  w1 := (1/2)*taunew*Transpose(Matrix(CC, [[0,1]])) + (1/2)*Transpose(Matrix(CC, [[0,1]]));
  w2 := (1/2)*taunew*Transpose(Matrix(CC, [[0,1]])) + (1/2)*Transpose(Matrix(CC, [[1,1]]));
  w3 := (1/2)*taunew*Transpose(Matrix(CC, [[1,0]])) + (1/2)*Transpose(Matrix(CC, [[1,0]]));
  w4 := (1/2)*taunew*Transpose(Matrix(CC, [[1,0]])) + (1/2)*Transpose(Matrix(CC, [[1,1]]));
  w5 := (1/2)*taunew*Transpose(Matrix(CC, [[1,1]])) + (1/2)*Transpose(Matrix(CC, [[0,1]]));
  w6 := (1/2)*taunew*Transpose(Matrix(CC, [[1,1]])) + (1/2)*Transpose(Matrix(CC, [[1,0]]));
  ws := [ w1, w2, w3, w4, w5, w6 ];

  vprint CurveRec : "Calculating theta derivatives...";
  theta_derss := [ ThetaDerivatives(taunew, w) : w in ws ];
  vprint CurveRec : "done calculating theta derivatives.";

  /* Determination of ratios = roots */
  Hs := [ Matrix(CC, [ theta_ders ]) * P2inew : theta_ders in theta_derss ];
  rats := [ ];
  for H in Hs do
    seq := Eltseq(H);
    add := true;
    if Abs(seq[2]) lt Abs(seq[1]) then
      if Abs(seq[2]/seq[1])^2 lt CC`epscomp then
        add := false;
      end if;
    end if;
    if add then
      Append(~rats, -seq[1]/seq[2]);
    end if;
  end for;

  /* Recover polynomial over CC up to a constant */
  RCC := PolynomialRing(CC);
  fCC := &*[ RCC.1 - rat : rat in rats ];
  return <fCC, tau, P>;
end function;


function ModularInvariantsG2(inp : Reduce:=true)
  CC := BaseRing(Parent(inp));
  g := Nrows(inp);
  assert g eq 2;
  _, tau := BigAndSmallPeriodMatrix(inp);
  if Reduce then // this speeds up the Theta computations
      tau := ReduceSmallPeriodMatrix(tau);
  end if;

  z := Matrix(CC,g,1,[]);
  // Cseq := Sort([[elt: elt in a] cat [elt: elt in b] : a, b in CartesianPower([0, 1], 2) ]);
  Cseq := [[0,0,0,0],[0,0,0,1],[0,0,1,0],[0,0,1,1],[0,1,0,0],[0,1,0,1],[0,1,1,0],[0,1,1,1],[1,0,0,0],[1,0,0,1],[1,0,1,0],[1,0,1,1],[1,1,0,0],[1,1,0,1],[1,1,1,0],[1,1,1,1]];
  // make an array starting from zero, to match folklore indexing
  C := AssociativeArray();
  for i->elt in Cseq do
    C[i-1] := elt;
  end for;
  // evenC := [i : i->elt in C  | ((elt[1]*elt[3] + elt[2]*elt[4]) mod 2) eq 0];
  evenC := [0,1,2,3,4,6,8,9,12,15];
  SevenC := Set(evenC);
  t := AssociativeArray();
  s := AssociativeArray();
  vprint CurveRec : "Computing theta functions...";
  for i in evenC do
    vprintf CurveRec : "theta_%o...", i;
    vtime CurveRec: t[i] := Theta(Matrix(Rationals(), 4, 1, C[i])/2, z, tau);
    s[i] := t[i]^4;
  end for;
  vprint CurveRec: "Done computing theta functions";
  //GopelQuad := [ elt : elt in Subsets(Set(evenC), 4) | &+[Vector(GF(2), C[j]) : j in elt] eq 0];
  //syzygous := SetToSequence(&join [Subsets(elt, 3)  : elt in GopelQuad]);
  GopelQuad := [{2,4,9,15},{1,2,12,15},{0,3,12,15},{1,4,9,12},{3,6,9,12},{0,1,2,3},{3,4,8,15},{2,6,8,12},{0,1,8,9},{0,6,9,15},{1,3,4,6},{1,6,8,15},{0,2,4,6},{0,4,8,12},{2,3,8,9}];

  h4 := &+[t[i]^8 : i in evenC];
  // copy pasted from Streng -- Computing Igusa class polynomials
  h6 :=s[0]*s[1]*s[2]+s[0]*s[1]*s[3]+s[0]*s[2]*s[3]+s[1]*s[2]*s[3]-s[0]*s[2]*s[4]+s[1]*s[3]*s[4]-s[0]*s[2]*s[6]+s[1]*s[3]*s[6]-s[0]*s[4]*s[6]-s[1]*s[4]*s[6]-s[2]*s[4]*s[6]-s[3]*s[4]*s[6]-s[0]*s[1]*s[8]+s[2]*s[3]*s[8]+s[0]*s[4]*s[8]+s[3]*s[4]*s[8]-s[1]*s[6]*s[8]-s[2]*s[6]*s[8]-s[0]*s[1]*s[9]+s[2]*s[3]*s[9]-s[1]*s[4]*s[9]-s[2]*s[4]*s[9]+s[0]*s[6]*s[9]+s[3]*s[6]*s[9]-s[0]*s[8]*s[9]-s[1]*s[8]*s[9]-s[2]*s[8]*s[9]-s[3]*s[8]*s[9]+s[1]*s[2]*s[12]-s[0]*s[3]*s[12]+s[0]*s[4]*s[12]+s[1]*s[4]*s[12]-s[2]*s[6]*s[12]-s[3]*s[6]*s[12]+s[0]*s[8]*s[12]+s[2]*s[8]*s[12]+s[4]*s[8]*s[12]+s[6]*s[8]*s[12]-s[1]*s[9]*s[12]-s[3]*s[9]*s[12]+s[4]*s[9]*s[12]+s[6]*s[9]*s[12]+s[1]*s[2]*s[15]-s[0]*s[3]*s[15]-s[2]*s[4]*s[15]-s[3]*s[4]*s[15]+s[0]*s[6]*s[15]+s[1]*s[6]*s[15]-s[1]*s[8]*s[15]-s[3]*s[8]*s[15]+s[4]*s[8]*s[15]+s[6]*s[8]*s[15]+s[0]*s[9]*s[15]+s[2]*s[9]*s[15]+s[4]*s[9]*s[15]+s[6]*s[9]*s[15]-s[0]*s[12]*s[15]-s[1]*s[12]*s[15]-s[2]*s[12]*s[15]-s[3]*s[12]*s[15];
  h10 := (&*[t[i] : i in evenC])^2;
  h12 := &+[ &*[t[j]^4 : j in SevenC diff c] : c in GopelQuad];
  // we don't really need to compute h16, but is a good sanity check
  h16 := &+[ (&+[t[d]^8 : d in c]) * &*[t[j]^4 : j in evenC | not j in c] : c in GopelQuad];
  i6 := [(h12*h4-3*h16), 2*h10*h6];
  m := Max([Abs(elt) : elt in i6]);
  if not (m^2 lt CC`epscomp or (Abs(i6[1] -i6[2])/m)^2 lt CC`epscomp) then
    error "Not small enough", ComplexField(5)!m^2,  ComplexField(5)!(Abs(i6[1] -i6[2])/m)^2;
  end if;


  return WPSNormalizeCC([4, 6, 10, 12], [h4, h6, h10, h12]);
end function;



function IgusaInvariantsG2(inp : G2CC := false, Reduce:=true)
  if G2CC cmpeq false then
    // quicker to use RosenhainInvariants
    _, tau := BigAndSmallPeriodMatrix(inp);
    if Reduce then // this speeds up the Theta computations
        tau := ReduceSmallPeriodMatrix(tau);
    end if;
    CC := BaseRing(tau);
    R<x> := PolynomialRing(CC);
    fCC := x * (x - 1) * &*[x - r: r in RosenhainInvariants(tau)];
  else
    fCC := G2CC[1];
  end if;
  JCC := IgusaInvariants(fCC);
  return WPSNormalizeCC([2,4,6,8,10], JCC);
end function;

function AlgebraizedInvariantsG2(inp, K : Base:=false, UpperBound:=16, G2CC:=false, type:="Igusa", Reduce:=true)

  vprintf CurveRec : "Algebraizing %o invariants...\n", type;
  // We only support Igusa, Modular invariants, jInvariants
  assert type in ["Igusa", "Modular", "j"];

  CC := BaseRing(Parent(inp));
  g := Nrows(inp);
  assert g eq 2;
  P, tau := BigAndSmallPeriodMatrix(inp);
  if Reduce then // this speeds up the Theta computations
    tau := ReduceSmallPeriodMatrix(tau);
  end if;



  vprintf CurveRec : "Computing %o invariants over CC...\n", type;
  if type eq "Igusa" then
    // if we already did the work with Theta derivatives
    vtime CurveRec: invCC := IgusaInvariantsG2(tau : G2CC:=G2CC, Reduce:=false);
  elif type eq "Modular" then
    vtime CurveRec: invCC := ModularInvariantsG2(tau : Reduce:=false);
  elif type eq "j" then
    vprintf CurveRec : "Computing Igusa invariants over CC...";
    vtime CurveRec: _, _, _, _, J10 := Explode(IgusaInvariantsG2(tau : G2CC:=G2CC, Reduce:=false));
    assert Abs(J10)^2 lt CC`epscomp;
    vprintf CurveRec : "Computing endomorphism representation...";
    try
      vtime CurveRec: G := GeometricEndomorphismRepresentation(P, K : UpperBound:=UpperBound);
    catch e
      vprintf CurveRec : "Failed to algebraize %o invariants.\n", type;
      return 0, 0, false, e;
    end try;
    vprintf CurveRec : "And the factors ...";
    try
      vtime CurveRec: facs, b, hML := SplittingFactorsOverClosure(P, G);
    catch e
      vprintf CurveRec : "Failed to algebraize %o invariants.\n", type;
      return 0, 0, false, e;
    end try;
    assert #facs ge 1;
    invCC := [];
    for f in facs do
      PE, morphism, exponent := Explode(f);
      j := jInvariant(SmallPeriodMatrix(PE)[1][1]);
      Append(~invCC, j);
    end for;
  end if;
  vprintf CurveRec : "Done computing %o invariants over CC...\n", type;

  // for  Modular one perhaps should use rational functions to bound the height
  if Base then
    test, I := AlgebraizeElementsExtra(invCC, K : UpperBound:=UpperBound);
    if not test then
      vprintf CurveRec : "Failed to algebraize %o invariants.\n", type;
      return 0, 0, false, Sprintf("Failed to algebraize %o invariants over base", type);
    end if;
    L := K; hKL := CanonicalInclusionMap(K, L);
  else
    try
      L, I, hKL := NumberFieldExtra(invCC, K : UpperBound:=UpperBound);
    catch e
      vprintf CurveRec : "Failed to algebraize %o invariants.\n", type;
      return 0, 0, false, e;
    end try;
  end if;
  if type eq "j" and #I eq 1 then
    I := [I[1], I[1]];
  end if;
  return I, hKL, true, _;

end function;


intrinsic IntegralReconstructionIgusaInvariants(inp : G2CC:=false, Reduce:=true) -> BoolElt, SeqEnum[RntIntElt], FldComElt
  { reconstructs the Igusa invariants in ZZ, the third argument is the error }
  vprintf CurveRec : "IntegralReconstructionIgusaInvariants...\n";

  CC := BaseRing(Parent(inp));
  g := Nrows(inp);
  assert g eq 2;
  P, tau := BigAndSmallPeriodMatrix(inp);
  if Reduce then // this speeds up the Theta computations
    tau := ReduceSmallPeriodMatrix(tau);
  end if;

  vprintf CurveRec : "Computing Igusa invariants over CC...\n";
  vtime CurveRec: JCC := IgusaInvariantsG2(tau : G2CC:=G2CC, Reduce:=false);

  weights := [1,2,3,4,5];
  JQQ := [];
  maxe := 0;
  for i->w in weights do
      _, q := RationalReconstruction(JCC[i]);
      Append(~JQQ, q);
      _, e := AlmostEqual(JCC[i], q);
      maxe := Max(e, maxe);
      if e^2 gt CC`epscomp then
        return false, JQQ, maxe;
      end if;
      f, p := PowerFreePart(Rationals()!Denominator(q), w);
      s := &*PrimeDivisors(Integers()!f);
      JCC := WPSMultiply(weights, JCC, s * p);
      JQQ := WPSMultiply(weights[1..i], JQQ, s * p);
  end for;

  vprintf CurveRec : "IntegralReconstructionIgusaInvariants... done";
  return true, JQQ, maxe;
end intrinsic;

function ReconstructCurveGeometricG2(inp, K : Base:=false, UpperBound:=16, G2CC:=false)
/* Alternative: implement variant of BILV */
/* TODO: Add check of not being product of elliptic curves */
  I, hKL, b, e := AlgebraizedInvariantsG2(inp, K : Base:=Base, UpperBound:=UpperBound, G2CC:=G2CC, type:="Igusa");
  if not b then
    return 0, 0, false, e;
  end if;

  g2 := IgusaToG2Invariants(I);
  Y := HyperellipticCurveFromG2Invariants(g2);
  if Type(BaseRing(Y)) eq FldRat then
    Y := ReducedMinimalWeierstrassModel(Y);
    f, h := HyperellipticPolynomials(Y);
    g := 4*f + h^2;
    coeffs := Coefficients(g);
    d := LCM([ Denominator(coeff) : coeff in coeffs ]);
    coeffs := [ Integers() ! (d*coeff) : coeff in coeffs ];
    e := GCD(coeffs);
    coeffs := [ coeff div e : coeff in coeffs ];
    Y := HyperellipticCurve(Polynomial(coeffs));
    if Type(K) eq FldRat then
      Y := ReducedMinimalWeierstrassModel(Y);
    end if;
  end if;
  return Y, hKL, true;
end function;


intrinsic ReconstructGenus2Curve(P::., K::Fld : Base:=false, Dom:=[-5..5], UpperBound:=16, G2CC:=false) -> CrvHyp, Map, BoolElt, .
{ Reconstruct curve from period matrix P, returned over an extension of the base field K.}

  CC := BaseRing(Parent(P));
  assert IsBigPeriodMatrix(P);
  if G2CC cmpeq false then
    G2CC := ReconstructCurveG2CC(P);
  end if;
  fCC, tau, P := Explode(G2CC);

  // one could directly call them from JCC, but the function below also normalizes them
  JCC := IgusaInvariantsG2(P : G2CC:=G2CC); //Edgar: is this really worth it to pass G2CC?
  _, _, _, _, J10 := Explode(JCC);

  if Abs(J10)^2 lt CC`epscomp then
    e := "Cannot reconstruct curve, it is a product of elliptic curves.";
    vprint ModAbVarRec: e;
    return 0, 0, false, e;
  end if;

  /* Finding homomorphisms to original matrix */
  vprint CurveRec : "Identifying correct twist...";
  YCC := RiemannSurface(fCC, 2 : Precision := Precision(CC) + 10);
  Q := ChangeRing(YCC`BigPeriodMatrix, CC) / 2;
  homs := GeometricHomomorphismRepresentationCC(P, Q);
  As := [ hom[1] : hom in homs ]; Rs := [ hom[2] : hom in homs ];
  if #As eq 0 then
    //: increase precision or bound in calculating theta derivatives";
    e := "No geometric homomorphism to original matrix found. Try increasing the precision.";
    vprint ModAbVarRec: e;
    return 0, 0, false, e;
  end if;

  /*  Identify correct twist */
  M := Matrix([ [ Re(A[1,1] - A[2,2]), Im(A[1,1] - A[2,2]), Re(A[1,2]), Im(A[1,2]), Re(A[2,1]), Im(A[2,1]) ] : A in As ]);
  Ker := IntegralLeftKernel(M); rows := Rows(Ker);
  if #rows eq 1 then
    row := Eltseq(rows[1]);
    Lambda := &+[ row[i]*As[i] : i in [1..#As] ];
    R := &+[ row[i]*Rs[i] : i in [1..#Rs] ];
    assert Abs(Determinant(R)) eq 1;
    lam := Lambda[1,1];
  else
    found := false;
    CP := CartesianPower(Dom, #rows);
    for tup in CP do
      row := &+[ tup[i]*rows[i] : i in [1..#rows] ];
      Lambda := &+[ row[i]*As[i] : i in [1..#As] ];
      R := &+[ row[i]*Rs[i] : i in [1..#Rs] ];
      if Abs(Determinant(R)) eq 1 then
        lam := Lambda[1,1];
        found := true;
        break;
      end if;
    end for;

    if not found then
      e := "Failed to identify correct twist. Try increasing the precision.";
      vprint ModAbVarRec: e;
      return 0, 0, false, e;
    end if;
  end if;
  vprint CurveRec : "done identifying correct twist.";

  /* Recover twisted polynomial over number field */
  fCC := lam^2*fCC; coeffsCC := Coefficients(fCC);
  coeffsCC := ChangeUniverse(coeffsCC, K`CC);

  vprint CurveRec : "Algebraizing...";
  if Base then
      test, coeffs := AlgebraizeElementsExtra(coeffsCC, K : UpperBound:=UpperBound);
      if not test then
          e := "Failed to algebraize coefficients.";
          vprint CurveRec : e;
          return 0, 0, false, e;
      end if;
      L := K; hKL := CanonicalInclusionMap(K, L);
  else
    try
      L, coeffs, hKL := NumberFieldExtra(coeffsCC, K : UpperBound:=UpperBound);
    catch e
      vprint CurveRec : e;
      return 0, 0, false, e;
    end try;
  end if;
  vprint CurveRec : "done.";

  // The next lines functions as an assertion
  vprint CurveRec, 2 : "Check for isomorphism...";
  /*
  //Edgar to Jeroen: A doesnt necessarily need to be the identity...
  A := IdentityMatrix(CC, 2);
  R := HomologyRepresentation(A, P, Q);
  */
  // instead check that we have an isomorphism defined over K associated to R
  // R is the solution we found for the twist and Determinant(R) eq 1
  b, _ := AlgebraizeElementsExtra(Eltseq(TangentRepresentation(R, P, Q)), K);
  assert b;
  vprint CurveRec, 2 : "done.";

  f := PolynomialRing(L)!coeffs;
  Y := HyperellipticCurve(f);
  return Y, hKL, true, _;
end intrinsic;


