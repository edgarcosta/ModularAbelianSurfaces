AttachSpec("~/projects/CHIMP/CHIMP.spec");
AttachSpec("spec");

function doline(line)
    label, curve, nf:= Explode(Split(line, ":"));
    nf := eval nf;
    curve := eval curve;
    prec := 100;
    R<x>:= PolynomialRing(Rationals());
    K<a> := NumberField(R!nf);
    S<t>:= PolynomialRing(K);
    g:= S![K!elt : elt in curve[1]];
    h := S![K!elt : elt in curve[2]];
    H := HyperellipticCurve(g, h);

    PeriodCurve := PeriodMatrix(CurveExtra(H : prec := prec));

    for elt in getrecs("labelswithhecke.txt") do
        if elt[1] eq label then
            level := StringToInteger(elt[2]);
            hc := eval elt[3];
            break;
        end if;
    end for;
    ncoeffs := Ceiling(20*Sqrt(level)*Log(10)*prec/(2*Pi(ComplexField())));
    f := MakeNewformModSym(level, hc);

    Periodf := PeriodMatrix(f : prec := prec, ncoeffs:= ncoeffs);

    G, iota:= GeometricHomomorphismRepresentation(PeriodCurve, Periodf, RationalsExtra(prec));

    if #G eq 0 then
        return line cat ":false";
    end if;
    K := Codomain(iota);
    f := DefiningPolynomial(K);
    degrees := [Determinant(elt[2]) : elt in G];

    return StripWhiteSpace(Sprintf("%o:true:%o:%o", line, degrees, Coefficients(f)));

end function;


if assigned seq then
    seq := eval seq;
    SetColumns(0);
    SetAutoColumns(false);
    data := Split(Read("label_to_curve_notQQ.txt"), "\n");
    line := data[seq];
    print(doline(line)); // What do we actually want to print here?
end if;
