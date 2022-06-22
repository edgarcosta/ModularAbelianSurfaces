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


function ModularInvariantsG2(inp)

CC := BaseRing(Parent(inp));
g := Nrows(inp);
assert g eq 2;
_, tau := BigAndSmallPeriodMatrix(inp);

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
for i in evenC do
    t[i] := Theta(Matrix(Rationals(), 4, 1, C[i])/2, z, tau);
    s[i] := t[i]^4;
end for;
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



function IgusaInvariantsG2(inp : G2CC := false)

if G2CC cmpeq false then
    // quicker to use ModularInvariantsG2
    return ModularToIgusaInvariants(ModularInvariantsG2(inp));
else
    fCC := G2CC[1];
    JCC := IgusaInvariants(fCC);
    return WPSNormalizeCC([2,4,6,8,10], JCC);
end if;

end function;

function AlgebraizedInvariantsG2(inp, K : Base:=false, UpperBound:=16, G2CC:=false, type:="Igusa")


// We only support Igusa or Modular invariants
assert type in ["Igusa", "Modular"];

CC := BaseRing(Parent(inp));
g := Nrows(inp);
assert g eq 2;
_, tau := BigAndSmallPeriodMatrix(inp);



if type eq "Igusa" then
    // if we already did the work with Theta derivatives
    invCC := IgusaInvariantsG2(inp : G2CC:=G2CC);
else
    invCC := ModularInvariantsG2(tau);
end if;

if Base then
    test, I := AlgebraizeElementsExtra(invCC, K : UpperBound:=UpperBound);
    if not test then
        vprint CurveRec : "";
        vprintf CurveRec : "Failed to algebraize %o invariants.\n", type;
        return 0, 0, false;
    end if;
    L := K; hKL := CanonicalInclusionMap(K, L);
else
    L, I, hKL := NumberFieldExtra(invCC, K : UpperBound:=UpperBound);
end if;
return I, hKL, true;

end function;

function ReconstructCurveGeometricG2(inp, K : Base:=false, UpperBound:=16, G2CC:=false)
/* Alternative: implement variant of BILV */
/* TODO: Add check of not being product of elliptic curves */

    I, hKL, b := AlgebraizedInvariantsG2(inp, K : Base:=Base, UpperBound:=UpperBound, G2CC:=G2CC, type:="Igusa");
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


function ReconstructCurveG2(P, K : Base:=false, Dom:=[-5..5], UpperBound:=16, G2CC:=false)
// Reconstruct curve from period matrix P, returned over an extension of the
// base field K.

CC := BaseRing(Parent(P));
assert IsBigPeriodMatrix(P);
if G2CC cmpeq false then
    fCC, tau, P := ReconstructCurveG2CC(P);
else
    fCC, tau, P := Explode(G2CC);
end if;

// one could directly call them from JCC, but the function below also normalizes them
JCC := IgusaInvariantsG2(P : G2CC:=G2CC);
_, _, _, _, J10 := Explode(JCC);

if Abs(J10) lt CC`epscomp then
    error "Cannot reconstruct curve, it is a product of elliptic curves.";
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
    test, coeffs := AlgebraizeElementsExtra(coeffsCC, K : UpperBound:=UpperBound);
    if not test then
        vprint CurveRec : "Failed to algebraize coefficients.";
        return 0, 0, false;
    end if;
    L := K; hKL := CanonicalInclusionMap(K, L);
else
    L, coeffs, hKL := NumberFieldExtra(coeffsCC, K : UpperBound:=UpperBound);
end if;
vprint CurveRec : "done.";

R := PolynomialRing(L);
f := R!coeffs;
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


