AttachSpec("spec");

function doline(label, curve, nf)
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
    time f := MakeNewformModSym(level, hc);

    Periodf := PeriodMatrix(f : prec := prec, ncoeffs:= ncoeffs);

    G, iota:= GeometricHomomorphismRepresentation(PeriodCurve, Periodf, RationalsExtra(prec));

    return G; //if G is empty then our data is bad

end function;


if assigned seq then
    seq := eval seq;
    SetColumns(0);
    SetAutoColumns(false);
    data := Split(Read("label_to_curve_notQQ.txt"), "\n");
    line := data[seq];
    label, curve, nf:= Explode(Split(line, ":"));
    nf := eval nf;
    curve := eval curve;
    print(doline(label, curve, nf)); // What do we actually want to print here?
end if;
