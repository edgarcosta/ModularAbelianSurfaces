AttachSpec("~/projects/CHIMP/CHIMP.spec");
AttachSpec("~/projects/ModularCurves/abelian-varieties/spec");

if assigned verbose then
    verbose := eval verbose;
    SetVerbose("ModAbVarRec", verbose);
    SetVerbose("EndoFind", verbose);
    SetVerbose("Twists", verbose);
end if;

if assigned debug then
    debug := eval debug;
    SetDebugOnError(debug);
end if;

function ReadHashDatabase()
    ZZt := PolynomialRing(Integers());
    hash_database := AssociativeArray();
    for line in Split(Read("label_to_hash.txt")) do
        label, hash_str := Explode(Split(line, ":"));
        hash_database[label] := StringToInteger(hash_str);
    end for;
    return hash_database;
end function;

function GetLevelHeckeCutters(label)
    for elt in getrecs("labelswithhecke.txt") do
        if elt[1] eq label then
            level := StringToInteger(elt[2]);
            hc := eval elt[3];
            return level, hc;
        end if;
    end for;
    return false, false;
end function;

if assigned prec then
  if Type(prec) eq MonStgElt then
      prec := StringToInteger(prec);
  end if;
else
  prec := 300;
end if;



label, eqns := Explode(Split(input, ":"));
level, hc := GetLevelHeckeCutters(label);

QQ := RationalsExtra(prec);
f := MakeNewformModSym(level, hc);

function ComputeKL(f, eqns, prec : AutGrp:=false)
    C := Genus2Curve(eqns: prec:=prec);
    PeriodC := PeriodMatrix(C);
    if AutGrp cmpeq false then
        try
            aut, phi, hToL := GeometricAutomorphismGroupViaPeriods(C);
        catch e
            WriteStderr(e);
            WriteStderr(Sprintf("Increasing prec to %o", prec + 100));
            return ComputeKL(f, eqns, prec + 100);
        end try;
    else
        aut, phi, hToL := Explode(AutGrp);
    end if;
    Periodf := PeriodMatrix(f : prec := prec);
    try
        G, hToK := GeometricHomomorphismRepresentation(PeriodC, Periodf, QQ);
    catch e
        WriteStderr(e);
        WriteStderr(Sprintf("Increasing prec to %o", prec + 100));
        return ComputeKL(f, eqns, prec + 100 : AutGrp:=<aut, phi, hToL>);
    end try;
    L := Codomain(hToL);
    K := Codomain(hToK);
    KL := Polredabs(Compositum(L, K));
    return C, KL, aut, phi;
end function;

C, KL, aut, phi := ComputeKL(f, eqns, prec);

if Degree(KL) ne 1 then
    expected_t := ReadHashDatabase()[label];
    twists := AllTwists(C, KL : AutGrp:=<aut,phi>);
    found := false;
    for Cprime in twists do
        if expected_t eq TraceHash(TracesOfFrobenius(Cprime, 2^12, 2^13)) then
            print StripWhiteSpace(Join([label, MachinePrint(Cprime)],":"));
            found := true;
            break;
        end if;
    end for;
    if not found then
    	WriteStderr(Sprintf("no twist found for %o over %o\n", label, DefiningPolynomial(KL)));
    end if;
else
    WriteStderr(Sprintf("skipping %o\n", label));
end if;
//exit;
//catch e
//    WriteStderr(e);
//    exit 1;
//end try;

