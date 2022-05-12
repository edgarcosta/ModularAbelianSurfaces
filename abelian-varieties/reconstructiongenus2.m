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


function ReconstructCurveG2CC(inp)
// Reconstruct curve from a small/big period matrix P, returned over CC

CC := BaseRing(Parent(inp));
g := Nrows(inp);
assert g eq 2;
assert Ncols(inp) in [g, 2*g];
if Ncols(inp) eq g then
    tau := inp;
    assert IsSmallPeriodMatrix(tau);
    P := HorizontalJoin(tau, IdentityMatrix(CC, 2));
else
    P := inp;
    assert IsBigPeriodMatrix(P);
    tau := SmallPeriodMatrix(P);
end if;


/* Reduce small period matrix */
taunew, gamma := ReduceSmallPeriodMatrix(tau);
Imtaunew := Matrix([ [ Im(c) : c in Eltseq(row) ] : row in Rows(taunew) ]);

vprint CurveRec, 2 : "";
vprint CurveRec, 2 : "Eigenvalues of imaginary part of reduced tau:";
vprint CurveRec, 2 : [ ComplexField(5) ! tup[1] : tup in Eigenvalues(Imtaunew) ];

/* Calculate corresponding big period matrix */
A := Submatrix(gamma, 1,1, 2,2);
B := Submatrix(gamma, 1,3, 2,2);
C := Submatrix(gamma, 3,1, 2,2);
D := Submatrix(gamma, 3,3, 2,2);
Pnew := P * Transpose(BlockMatrix([[A, B], [C, D]]));
P1new := Submatrix(Pnew, 1,1, 2,2);
P2new := Submatrix(Pnew, 1,3, 2,2);
P2inew := P2new^(-1);

/* Calculation of theta derivatives at odd two-torsion points */
w1 := (1/2)*taunew*Transpose(Matrix(CC, [[0,1]])) + (1/2)*Transpose(Matrix(CC, [[0,1]]));
w2 := (1/2)*taunew*Transpose(Matrix(CC, [[0,1]])) + (1/2)*Transpose(Matrix(CC, [[1,1]]));
w3 := (1/2)*taunew*Transpose(Matrix(CC, [[1,0]])) + (1/2)*Transpose(Matrix(CC, [[1,0]]));
w4 := (1/2)*taunew*Transpose(Matrix(CC, [[1,0]])) + (1/2)*Transpose(Matrix(CC, [[1,1]]));
w5 := (1/2)*taunew*Transpose(Matrix(CC, [[1,1]])) + (1/2)*Transpose(Matrix(CC, [[0,1]]));
w6 := (1/2)*taunew*Transpose(Matrix(CC, [[1,1]])) + (1/2)*Transpose(Matrix(CC, [[1,0]]));
ws := [ w1, w2, w3, w4, w5, w6 ];

vprint CurveRec : "";
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




function AlgebraizedInvariantsG2(inp, K : Base:=false, G2CC:=false)

CC := BaseRing(Parent(inp));
g := Nrows(inp);
assert g eq 2;
assert Ncols(inp) in [g, 2*g];
if Ncols(inp) eq g then
    tau := inp;
    assert IsSmallPeriodMatrix(inp);
    P := HorizontalJoin(tau, IdentityMatrix(CC, 2));
else
    P := inp;
    assert IsBigPeriodMatrix(P);
    tau := SmallPeriodMatrix(P);
end if;

if G2CC cmpeq false then
    fCC := ReconstructCurveG2CC(inp)[1];
else
    fCC := G2CC[1];
end if;


ICC := IgusaInvariants(fCC); W := [ 2, 4, 6, 8, 10 ];
ICC := WPSNormalizeCC(W, ICC);
if Base then
    test, I := AlgebraizeElementsExtra(ICC, K);
    if not test then
        vprint CurveRec : "";
        vprint CurveRec : "Failed to algebraize Igusa invariants.";
        return 0, 0, false;
    end if;
    L := K; hKL := CanonicalInclusionMap(K, L);
else
    L, I, hKL := NumberFieldExtra(ICC, K);
end if;
return I, hKL, true;

end function;

function ReconstructCurveGeometricG2(inp, K : Base:=false, G2CC:=false)
/* Alternative: implement variant of BILV */
/* TODO: Add check of not being product of elliptic curves */

I, hKL, b := AlgebraizedInvariantsG2(inp, K : Base:=Base, G2CC:=G2CC);
if not b then
    return 0, 0, false;
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


function ReconstructCurveG2(P, K : Base:=false, Dom:= [-5..5], G2CC:=false)
// Reconstruct curve from period matrix P, returned over an extension of the
// base field K.
/* TODO: Add check of not being product of elliptic curves */

CC := BaseRing(Parent(P));
assert IsBigPeriodMatrix(P);
if G2CC cmpeq false then
    fCC, tau, P := ReconstructCurveG2CC(P);
else
    fCC, tau, P := Explode(G2CC);
end if;

/* Finding homomorphisms to original matrix */
vprint CurveRec : "";
vprint CurveRec : "Identifying correct twist...";
YCC := RiemannSurface(fCC, 2 : Precision := Precision(CC) + 10);
Q := ChangeRing(YCC`BigPeriodMatrix, CC) / 2;
homs := GeometricHomomorphismRepresentationCC(P, Q);
As := [ hom[1] : hom in homs ]; Rs := [ hom[2] : hom in homs ];
if #As eq 0 then
    error "No geometric homomorphism to original matrix found. Try increasing the precision.";
    //: increase precision or bound in calculating theta derivatives";
end if;

/*  Identify correct twist */
M := Matrix([ [ Re(A[1,1] - A[2,2]), Im(A[1,1] - A[2,2]), Re(A[1,2]), Im(A[1,2]), Re(A[2,1]), Im(A[2,1]) ] : A in As ]);
Ker := IntegralLeftKernel(M); rows := Rows(Ker);
if #rows eq 1 then
    row := Eltseq(rows[1]);
    Lambda := &+[ row[i]*As[i] : i in [1..#As] ];
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
        error "Failed to identify correct twist. Try increasing the precision.";
    end if;
end if;
vprint CurveRec, 2 : "";
vprint CurveRec : "done identifying correct twist.";

/* Recover twisted polynomial over number field */
fCC := lam^2*fCC; coeffsCC := Coefficients(fCC);
coeffsCC := ChangeUniverse(coeffsCC, K`CC);

vprint CurveRec : "";
vprint CurveRec : "Algebraizing...";
if Base then
    test, coeffs := AlgebraizeElementsExtra(coeffsCC, K);
    if not test then
        vprint CurveRec : "Failed to algebraize coefficients.";
        return 0, 0, false;
    end if;
    L := K; hKL := CanonicalInclusionMap(K, L);
else
    L, coeffs, hKL := NumberFieldExtra(coeffsCC, K);
end if;
vprint CurveRec : "done.";

R := PolynomialRing(L);
f := &+[ coeffs[i]*R.1^(i - 1) : i in [1..#coeffs] ];
Y := HyperellipticCurve(f);
YCC := RiemannSurface(fCC, 2 : Precision := Precision(CC) + 10);
Q := ChangeRing(YCC`BigPeriodMatrix, CC) / 2;

/* The next line functions as an assertion */
vprint CurveRec, 2 : "";
vprint CurveRec, 2 : "Check for isomorphism...";
A := IdentityMatrix(CC, 2);
R := HomologyRepresentation(A, P, Q);
vprint CurveRec, 2 : "done.";
return Y, hKL, true;

end function;


