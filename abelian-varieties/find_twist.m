AttachSpec("~/projects/CHIMP/CHIMP.spec");
AttachSpec("~/projects/ModularCurves/abelian-varieties/spec");
function ReadHashDatabase()
    ZZt := PolynomialRing(Integers());
    hash_database := AssociativeArray();
    for line in Split(Read("label_to_hash.txt")) do
        label, hash_str := Explode(Split(line, ":"));
        hash_database[label] := StringToInteger(hash_str);
    end for;
    return hash_database;
end function;
label, eqns := Explode(Split(input, ":"));

for elt in getrecs("labelswithhecke.txt") do
    if elt[1] eq label then
        level := StringToInteger(elt[2]);
        hc := eval elt[3];
        break;
    end if;
end for;
if assigned prec then
  prec := StringToInteger(prec);
else
  prec := 300;
end if;
QQ := RationalsExtra(prec);
f := MakeNewformModSym(level, hc);

Periodf := PeriodMatrix(f : prec := prec);

C := Genus2Curve(eqns: prec:=prec);
PeriodC := PeriodMatrix(C);


G, hToK := GeometricHomomorphismRepresentation(PeriodC, Periodf, QQ);
K := Codomain(hToK);

aut, phi, hToL := GeometricAutomorphismGroupViaPeriods(C);
L := Codomain(hToL);

KL := Polredabs(Compositum(L, K));

if Degree(KL) ne 1 then
    expected_t := ReadHashDatabase()[label];
    time twists := AllTwists(C, KL : AutGrp:=<aut,phi>);
    print twists;
    found := false;
    for Cprime in twists do
        if expected_t eq TraceHash(TracesOfFrobenius(Cprime, 2^12, 2^13)) then
            print StripWhiteSpace(Join([label, MachinePrint(C)],":"));
            found := true;
            break;
        end if;
    end for;
    if not found then
    	WriteStderr(Sprintf("no twist found for %o over %o\n", label, DefiningPolynomial(K)));
    end if;
else
    WriteStderr(Sprintf("skipping %o\n", label));
end if;
exit;
