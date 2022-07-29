//Initialising...

AttachSpec("~/CHIMP/CHIMP.spec");
AttachSpec("~/ModularCurves/abelian-varieties/spec");
input := "456.2.a.e:456:[<5,[-10,1,1]>]";

// Finding Period Matrix

//The relevant material is in Goren pg 53-55 for the trace pairing implemented here. Code is just for one example and very non-modular. Will try it for other examples soon.

s := Split(input, ":");
label := s[1];
level := StringToInteger(s[2]);
hc := eval s[3];
prec := 100;

// figure out the right number of qexp coeffs
ncoeffs := Ceiling(20*Sqrt(level)*Log(10)*prec/(2*Pi(ComplexField())));

time f := MakeNewformModSym(level, hc);

time P := PeriodMatrix(f : prec:=prec, ncoeffs:=ncoeffs);

time Pmax, G2 := PeriodMatrixWithMaximalOrder(P);
//G2[2][2];

// Finding generators of endomorphism ring and relations to find structure of lattice as an OK module 

function Columns(M)
    return Rows(Transpose(M));
end function;
alpha := G[2][2];
alphaCC := ChangeRing(alpha, BaseRing(P));
// columns of new period matrix
e1, e2, e3, e4 := Explode(Columns(Pmax));

//The above is just expressing the columns e3,e4 in temrs of e1,e2,alpha*e1,alpha*e2 where alpha is the generator of the Endomorphism ring.

// writing e3,e4 in terms of e1 and e2
function CoordinatesZF(input)
    M := Matrix([e1, e1alpha, e2, e2alpha, input]);
    K := IntegralLeftKernel(M);
    assert Nrows(K) eq 1 and Ncols(K) eq 5;
    den := K[1,5];
    assert den ne 0;
    c1, c2, c3, c4 := Explode(Eltseq(ChangeRing(K, Rationals())/-den));
    return [c1,c2,c3,c4];
end function;

K<a> := NumberField(MinimalPolynomial(alpha));
OK := MaximalOrder(K);

a1, b1 := Explode([K!c[1..2], K!c[3..4]]) where c := CoordinatesZF(e3);
a2, b2 := Explode([K!c[1..2], K!c[3..4]]) where c := CoordinatesZF(e4);

function LCMlist(l)
    d := 1;
    for elt in l do
        d := LCM(d, elt);
    end for;
    return d;
end function;
d := LCM([Denominator(elt) : elt in [a1, a2, b1, b2]]);

_, gen := IsPrincipal(Different(OK));
different := gen*OK;


Id := (1/d)*OK;
M := Module(
[<Id,A![d*a1,d*b1]> ,<Id,A![d*a2,d*b2]> ,<Id,A![d,0]> ,<Id,A![0,d]>]
);
B := PseudoBasis(M);

prod := B[1][1]*B[2][1]*different;

// there is some overlap with below


Id := (1/d)*OK;
M := Module(
[<Id,A![d*a1,d*b1]> ,<Id,A![d*a2,d*b2]> ,<Id,A![d,0]> ,<Id,A![0,d]>]
);
B := PseudoBasis(M);

OK:=MaximalOrder(K);
I1:=1/d*OK;
A:=RModule(OK,2);
//M:=Module([<I1,A![d*a1,20*a3] ,<I1,A![20*a2,20*a4]>]);
//PseudoGenerators(M);
M1:=Module([<I1,A![d*a1,d*a3]> ,<I1,A![d*a2,d*a4]> ,<I1,A![d,0]> ,<I1,A![0,d]> ]);
Basis:=PseudoBasis(M1);
aa:=2*a+1;
Different:=aa*OK;
//Better way of doing this? Somehwo in conjungtion with the code I have written Different does not quite work.
J1:=Basis[1][1];
J2:=Basis[2][1];
ProductOfIdeals:=J1*J2*Different;
ProductOfIdeals;
//HERE?!?!?! what are we trying to do?

OK:=1*OK;
Inverse:=OK/ProductOfIdeals;
OK:=MaximalOrder(K);
NormOfInverse:=Norm(Inverse);
DOfInverse:=Denominator(NormOfInverse);
s:=DOfInverse^2*NormOfInverse;
s:=Integers()!s;   //It was illegal to do s!IntegerRing()
_,x:=NormEquation(OK,s);

for i in [1..8] do;
if x[i] in Inverse then
r:=x[i];
break;
end if;
end for;
r;

r:=r/DOfInverse;

assert r*OK eq Inverse;

//aa:=2*a+1;
//Different:=aa*OK;
//J1:=(1/2*OK.1+1/2*OK.2)*OK;
//J2:=(-17/2*OK.1-6/5*OK.2)*OK;
//J1*J2*Different;
//r:=-395/4*OK.1-519/20*OK.2;
//r:=1/r;

gen1:=Generators(J1)[2];
gen2:=Generators(J2)[2];
b1:=gen1;
b2:=OK.2*gen1;
b3:=gen2;
b4:=OK.2*gen2;


a11:=0;
a12:=0;
a13:=Trace(r*b1*b3);
a14:=Trace(r*b1*b4);
a21:=-a12;
a22:=0;
a23:=Trace(r*b2*b3);
a24:=Trace(r*b2*b4);
a31:=-a13;
a32:=-a23;
a33:=0;
a34:=0;
a41:=-a14;
a42:=-a24;
a43:=-a34;
a44:=0;
E:=Matrix(IntegerRing(),4,4,[a11,a12,a13,a14,a21,a22,a23,a24,a31,a32,a33,a34,a41,a42,a43,a44]);

/* This was to check the behaviour as we change the generator of the ideal r*OK
Noticed the determinant is actually invariant.

K:=QuadraticField(Discriminant(OK)); \\Redefine K to find fundamental unit
OK:=MaximalOrder(K);

u:=FundamentalUnit(OK);

for i in [-10..10] do
a11:=0;
a12:=0;
a13:=Trace(u^i*r*b1*b3);
a14:=Trace(u^i*r*b1*b4);
a21:=0;
a22:=0;
a23:=Trace(u^i*r*b2*b3);
a24:=Trace(u^i*r*b2*b4);
a31:=-a13;
a32:=-a23;
a33:=0;
a34:=0;
a41:=-a14;
a42:=-a24;
a44:=-a34;
a34:=-a34;
a44:=0;
E:=Matrix(IntegerRing(),4,4,[a11,a12,a13,a14,a21,a22,a23,a24,a31,a32,a33,a34,a41,a42,a43,a44]);
//if Determinant(E) eq 1 then
Determinant(E);
//end if;
end for;

*/


