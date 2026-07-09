AttachSpec("~/GitHub/CHIMP/CHIMP.spec");
AttachSpec("/Users/aashrayajha/Documents/GitHub/ModularAbelianSurfaces/spec");
labels:=["625.2.a.a", "625.2.a.b","625.2.a.c"];
// "625.2.a.e"? This factor can't be done without the modular form presumably

prec := 110;
SetDefaultRealFieldPrecision(prec);
CC := ComplexFieldExtra(prec);

PeriodsM:=[];
Isogs:=[];

for label in labels do
    printf "Computing modular data for %o\n", label;
    t := Cputime();
    f := LMFDBNewform(label);
    piM := ChangeRing(PeriodMatrix(f : Precision := prec), CC);
    res := RationalGenus2Curves(f : Precision:=prec, OnlyOne:=true);
    assert #res ge 1;
    b, isog, C, e := Explode(res[1]);
    assert b;
    assert Abs(Determinant(isog)) eq 1;
    Append(~PeriodsM, piM);
    Append(~Isogs, isog);
    printf "Modular data time: %o seconds\n", Cputime(t);
end for;

PeriodsMTransformed := [
    PeriodsM[i] * Transpose(Matrix(CC, Isogs[i]))
    : i in [1..#PeriodsM]
];
PiM := ChangeRing(DiagonalJoin(PeriodsMTransformed), CC);
// print ModularPi;
R<x>:=PolynomialRing(Rationals());
C1:= HyperellipticCurve(6*x^6 - 5*x^5 + 12*x^4 - 13*x^3 + 6*x^2 - 13*x - 4, x^3 + x + 1);
C2 := HyperellipticCurve(x^6 - 13*x^4 - 38*x^3 + 6*x^2 + 22*x + 6, x^3+x+1);
C3 := HyperellipticCurve(-3*x^4 - 8*x^3 + x^2 + 4*x + 1, x^3+x+1);

curves:=[C1,C2,C3];
PeriodsC:=[];

for curve in curves do
    t := Cputime();
    f, h := HyperellipticPolynomials(curve);
    YCC := RiemannSurface(ChangeRing(4*f + h^2, CC), 2 : Precision := Precision(CC) + 10);
    piC := ChangeRing(YCC`BigPeriodMatrix, CC) / 2;
    Append(~PeriodsC, piC);
    printf "Curve period time: %o seconds\n", Cputime(t);
end for;

PiC := ChangeRing(DiagonalJoin(PeriodsC), CC);

t := Cputime();
homs := GeometricHomomorphismRepresentationCC(PiC, PiM);
printf "#homs = %o\n", #homs;
printf "Hom search time: %o seconds\n", Cputime(t);

datafile := "/Users/aashrayajha/Documents/GitHub/ModularAbelianSurfaces/examples/NS25/625.2.a.period-data.dat";
WriteObject(Open(datafile, "w"), <
    labels,
    prec,
    curves,
    PeriodsC,
    PiC,
    PeriodsM,
    PeriodsMTransformed,
    PiM,
    Isogs,
    homs
>);
printf "Saved period and hom data to %o\n", datafile;
