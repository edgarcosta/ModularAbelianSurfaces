intrinsic Imaginary(M::Mtrx[FldCom]) -> Mtrx[FldRe]
{ The imaginary part of M }
    return Matrix([[Imaginary(elt) : elt in Eltseq(row)] : row in Rows(M)]);
end intrinsic;


intrinsic LMFDBNewform(label::MonStgElt) -> ModSym
{ Return modular form given label }
    filenames := GetFilenames(MakeNewformModSym);
    assert #filenames eq 1;

    dirname := "/" cat Join(s[1..(#s - 1)], "/") where s := Split(filenames[1,1],"/");
    for elt in getrecs(dirname cat "/data/labelswithhecke.txt") do
        if elt[1] eq label then
            level := StringToInteger(elt[2]);
            hc := eval elt[3];
            break;
        end if;
    end for;
    require assigned hc: "label not found in the database";
    return MakeNewformModSym(level, hc);
end intrinsic;

intrinsic MakeNewformModSym(level::RngIntElt, hecke_cutters::SeqEnum[Tup]) -> ModSym
{ "TODO: add documentation" }
    vprintf ModAbVarRec: "MakeNewformModSym(%o, %o)\n", level, &cat Split(Sprint(hecke_cutters), "\n");
    R<x> := PolynomialRing(Rationals());
    // SetVerbose("ModularSymbols", true);
    chi := DirichletGroup(level)!1;
    Rhecke_cutters := [<elt[1], R!elt[2]> : elt in hecke_cutters];
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,2)));
    f := Kernel(Rhecke_cutters ,Snew);
    vprintf ModAbVarRec: "Done MakeNewformModSym(%o, %o)\n", level, &cat Split(Sprint(hecke_cutters), "\n");
    return f;
end intrinsic;

intrinsic MachinePrint(v::ModTupRngElt) -> MonStgElt
{ return "V:F" where F is list of the coefficients of the defining polynomial}
  F := BaseRing(v);
  v := Eltseq(v);
  if Type(F) eq FldRat then
    return Sprint(v);
  end if;
  voverQQ := [Eltseq(elt) : elt in v];
  f := DefiningPolynomial(F);
  return Sprintf("%o:%o", voverQQ,  Eltseq(f));
end intrinsic;

intrinsic MachinePrint(C::CrvHyp) -> MonStgElt
  { .. }
  F := BaseRing(C);
  if BaseRing(C) eq Rationals() then
    return Sprintf("%o", Eltseq(C));
  else
    f := DefiningPolynomial(F);
    return Sprintf("%o:%o", Eltseq(C), Eltseq(f));
  end if;
end intrinsic;


intrinsic Eltseq(C::CrvHyp) -> SeqEnum
  {retunrns both hyperelliptic polynomials as SeqEnum}
  if BaseRing(C) eq Rationals() then
    f, g := HyperellipticPolynomials(MinimalWeierstrassModel(C));
    return [Eltseq(f), Eltseq(g)];
  else
    f, g := HyperellipticPolynomials(C);
    df := LCM([Denominator(elt) : elt in Eltseq(f)]);
    f *:= df^2;
    g *:= df;
    if g ne 0 then // I don't think this ever runs
      dg := LCM([Denominator(elt) : elt in Eltseq(g)]);
      f *:= dg^2;
      g *:= dg;
    end if;
    return [[Eltseq(elt) : elt in Eltseq(pol)] : pol in [f, g]];
  end if;
end intrinsic;



