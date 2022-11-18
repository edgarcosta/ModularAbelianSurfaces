FindZFStructure:=function(Pmax,alpha)

alphaCC:=ChangeRing(alpha[2][2],BaseRing(Pmax));  

function Columns(M)
    return Rows(Transpose(M));
end function;

PmaxColumns:= Columns(Pmax);

e1, e2, e3, e4 := Explode(Columns(Pmax));
e1alpha,e2alpha:=Explode(Columns(Pmax*alphaCC));

//add a check that e1,e2,e1alpha,e2alpha generate the lattice 

CoordinatesZF:=function(input)
    M := Matrix([e1, e1alpha, e2, e2alpha, input]);
    Kern := IntegralLeftKernel(M);
    assert Nrows(Kern) eq 1 and Ncols(Kern) eq 5;
    den := Kern[1,5];
    assert den ne 0;
    c1, c2, c3, c4 := Explode(Eltseq(ChangeRing(Kern, Rationals())/-den));
    return [c1,c2,c3,c4];
end function;



g:=MinimalPolynomial(alpha[2][2]);
K<a> := NumberField(g);
OK := MaximalOrder(K);

//a+1 eq OK.2;
a1, b1 := Explode([K!c[1..2], K!c[3..4]]) where c := CoordinatesZF(e3);
a2, b2 := Explode([K!c[1..2], K!c[3..4]]) where c := CoordinatesZF(e4);

d := LCM([Denominator(elt) : elt in [a1, a2, b1, b2]]);

A:=RModule(OK,2);
denIdeal := (1/d)*OK;

M,map := Module(
[<denIdeal,A![d*a1,d*b1]> ,<denIdeal,A![d*a2,d*b2]> ,<denIdeal,A![d,0]> ,<denIdeal,A![0,d]>]
);

Basis:=PseudoBasis(M);
J1:=Basis[1][1];
J2:=Basis[2][1];

_,gen1:=IsPrincipal(J1);
_,gen2:=IsPrincipal(J2);

//This is the change of basis from original lattice to our new lattice

s1:=ElementToSequence(map(A.1))[1];
s2:=ElementToSequence(map(A.1))[2];
s3:=ElementToSequence(map(A.2))[1];
s4:=ElementToSequence(map(A.2))[2];

s1:=s1/gen1;
s2:=s2/gen2;
s3:=s3/gen1;
s4:=s4/gen2;

S:=Matrix(2,2,[s1,s2,s3,s4]);
Sinv:=S^(-1);
if alpha[1][1] eq 1 then
    id2x2 := ChangeRing(alpha[1][1], BaseRing(Pmax));
elif alpha[1][1] eq -1 then
    id2x2 := ChangeRing(-alpha[1][1], BaseRing(Pmax));
end if;
amatrix := ChangeRing(alpha[2][1], BaseRing(Pmax));

//printf "This was amarix %o", amatrix;

if a eq OK.2 then
amatrix:=amatrix;
elif a eq OK.2-1 then
amatrix:=amatrix+id2x2;
else
printf "Check the minimal polynomial of generator of endomorphism ring";
end if;
//amatrix^2-amatrix-1;
//printf "This is new amatrix %o", amatrix;
foo := hom<K->Parent(id2x2) | [ amatrix]>;

s11:=foo(Sinv[1,1]);
s12:=foo(Sinv[1,2]);
s21:=foo(Sinv[2,1]);
s22:=foo(Sinv[2,2]);

vectore1:=ChangeRing(Matrix(2,1,[e1[1],e1[2]]),BaseRing(Pmax));
vectore2:=ChangeRing(Matrix(2,1,[e2[1],e2[2]]),BaseRing(Pmax));

f1:=s11*vectore1+s12*vectore2;
f2:=s21*vectore1+s22*vectore2;
f1alpha:=amatrix*f1; 
f2alpha:=amatrix*f2;

Piprime:=HorizontalJoin(HorizontalJoin(HorizontalJoin(f1,f1alpha),f2),f2alpha);

return Piprime,M,map;

end function;


TracePrincipalPolarization:=function(Piprime,M,g)

/*When the order considered has narrow class number 1, we can construct a principal polarization via the trace pairing.
The input is a period matrix with maximal order Piprime, the OK module structure on Pirprime, M (where OK is the ring of integers of a 
real quadratic field) and the defining polynomial of a generator of OK which was used to calculate the OK structure on Piprime*/

K:=FieldOfFractions(BaseRing(M));
K1<a>:=NumberField(g);
b,m1:=IsIsomorphic(K1,K);
a:=m1(a);

OK:=Integers(K);
b, L := IsQuadratic(K);
b, m := IsIsomorphic(L, K);
u := m(FundamentalUnit(L));

Basis:=PseudoBasis(M);
J1:=Basis[1][1];
J2:=Basis[2][1];
_,gen1:=IsPrincipal(J1);
_,gen2:=IsPrincipal(J2);

b1:=gen1;
b2:=a*gen1;
b3:=gen2;
b4:=a*gen2;

ProductOfIdeals:=J1*J2*Different(OK);
One:=1*OK;
InverseIdeal:=One/ProductOfIdeals;
_,r:=IsPrincipal(InverseIdeal);
assert r*OK eq InverseIdeal;

TotallyPositive:=function(r1,u1)

ListOfUnits:=[*r1,u1*r1,-u1*r1,-r1*];

for i in [1..4] do
    if IsTotallyPositive(ListOfUnits[i])
    then r1:=ListOfUnits[i];
    return r1;
    
    else
    r1:=r1;
    
    end if;
end for;
return r1;

end function;    

r:=TotallyPositive(r,u);
assert IsTotallyPositive(r);

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
pol:=Matrix(IntegerRing(),4,4,[a11,a12,a13,a14,a21,a22,a23,a24,a31,a32,a33,a34,a41,a42,a43,a44]);

assert(Determinant(pol)) eq 1;

E, F := FrobeniusFormAlternating(Matrix(Integers(), pol));

assert IsBigPeriodMatrix(Piprime * Transpose(ChangeRing(F, BaseRing(Piprime))));
return Piprime*Transpose(ChangeRing(F,BaseRing(Piprime))),E,pol;

end function;

