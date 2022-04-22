declare verbose ModAbVarRec, 3;

intrinsic GetDimension2Factors(N) -> SeqEnum
{ FIXME }
  return [A : A in Decomposition(JZero(N))];
end intrinsic;


intrinsic WriteStderr(s::MonStgElt)
{ write to stderr }
  E := Open("/dev/stderr", "w");
  Write(E, s);
  Flush(E);
end intrinsic;


intrinsic WriteStderr(e::Err)
{ write to stderr }
  WriteStderr(Sprint(e) cat "\n");
end intrinsic;

/* 
 * No Longer need this
intrinsic NormalizedPeriodMatrix(P::ModMatFldElt) -> ModMatFldElt
{ this normalizes  }
    CC := ComplexFieldExtra(Precision(BaseRing(P)));
    // Change convention
    P := Transpose(ChangeRing(P, CC));
    g := #Rows(P);
    P1 := Submatrix(P, 1, 1, g, g);
    P2 := Submatrix(P, 1, g + 1,g, g);
    P := HorizontalJoin(P2, P1);
    return P;
end intrinsic;
*/

// use hecke to get the number of correct digits
intrinsic PeriodMatrix(f::ModSym : prec:=80, ncoeffs:=10000) -> ModMatFldElt
{ Compute the normalized period matrix associated to f}
  vprint ModAbVarRec: Sprintf("Computing periods, prec:=%o, ncoeffs:=%o", prec, ncoeffs);
  vprintf ModAbVarRec: Sprintf("%o...", f);
  default_prec := Precision(GetDefaultRealField());
  // this is how we control the precision of the output of Periods
  SetDefaultRealFieldPrecision(prec + 10);
  vtime ModAbVarRec:
  // PeriodMapping gives the periods up to isogeny
  pi_f := PeriodMapping(f, ncoeffs);
  // Apply it to the whole space
  Pfull := Transpose(Matrix([pi_f(b) : b in Basis(CuspidalSubspace(AmbientSpace(f)))]));
  CC := ComplexFieldExtra(Precision(BaseRing(Pfull)));
  Pfull := Matrix(CC, Pfull);

  // figure out the relations
  kernel, b := IntegralRightKernel(Pfull);
  S, P, Q := SmithForm(Matrix(Integers(), kernel));

  // extract the correct period matrix
  CC := BaseRing(Pfull);
  PfullNew := Pfull*Matrix(CC, P^-1);
  PNew := Submatrix(PfullNew, 1, 1+ Ncols(PfullNew) - Dimension(f), 2, Dimension(f));
  // undo the default_prec
  SetDefaultRealFieldPrecision(default_prec);
  vprint ModAbVarRec: "Done";
  return PNew;
end intrinsic;






intrinsic PeriodMatrixWithMaximalOrder(P::ModMatFldElt) -> ModMatFldElt, SeqEnum
{
  Given a period matrix P for a dim 2 modular forms space with trivial character
  such that the coefficient ring index is > 1, return a period matrix for an isogenous abelian variety
  such that the isogenous abelian variety has endomorphism ring equal to the maximal order
}
  vprintf ModAbVarRec: "Extending lattice...";
  QQ := RationalsExtra(Precision(BaseRing(P)));
  vprint ModAbVarRec: "\nComputing GeometricEndomorphismRepresentation...";
  vtime ModAbVarRec:
  GeoEndoRep := GeometricEndomorphismRepresentation(P, QQ);
  F, h := InclusionOfBaseExtra(BaseRing(GeoEndoRep[1][1]));
  GeoEndoRepBase := EndomorphismRepresentation(GeoEndoRep, F, h);
  vprint ModAbVarRec:GeoEndoRep;
  vprint ModAbVarRec:GeoEndoRepBase;
  vprint ModAbVarRec: "Done";
  require #GeoEndoRepBase eq 2: Sprintf("This does not seem to be GL2-type, dim End A = %o", #GeoEndoRepBase);
  one := GeoEndoRepBase[1][2];
  gen := GeoEndoRepBase[2][2];
  assert one eq 1;
  minpoly := MinimalPolynomial(gen); //need to make (D + sqrt(D)) where D is the discriminant
  K<a> := NumberField(minpoly);
  if IsMaximal(EquationOrder(K)) then // nothing to do
    return P, GeoEndoRepBase;
  end if;
  D:= Discriminant(Integers(K));
  x := Parent(minpoly).1;
  sqrtDpoly := x^2 - D;
  rts := Roots(sqrtDpoly, K);
  rt := rts[1][1];
  sqrtD := &+[c*gen^(i-1) : i->c in Eltseq(rt)];
  DpSqrtD := D*one + sqrtD;
  CC := BaseRing(P);
  AuxP := Transpose(Matrix(Rows(Transpose(2*P)) cat Rows(Transpose(P*Matrix(CC, DpSqrtD)))));
  kernel, bool := IntegralRightKernel(AuxP);
  assert bool;
  S, P, Q := SmithForm(Matrix(Integers(), kernel));
  P2 := Submatrix(AuxP*Matrix(CC, P^-1), 1, 5, 2, 4);
  vprintf ModAbVarRec: "Computing GeometricEndomorphismRepresentation...";
  vtime ModAbVarRec:
  GeoEndoRep2 := GeometricEndomorphismRepresentation(P2, QQ);
  vprint ModAbVarRec: "Done";
  require #GeoEndoRep2 ge 2: Sprintf("This does not seem to be GL2-type, dim End newA_bar = %o", #GeoEndoRep2);
  F, h := InclusionOfBaseExtra(BaseRing(GeoEndoRep2[1][1]));
  GeoEndoRepBase2 := EndomorphismRepresentation(GeoEndoRep2, F, h);
  vprint ModAbVarRec:GeoEndoRep2;
  vprint ModAbVarRec:GeoEndoRepBase2;
  require #GeoEndoRepBase2 ge 2: Sprintf("This does not seem to be GL2-type, dim End newA = %o", #GeoEndoRepBase2);
  minpoly2 := MinimalPolynomial(GeoEndoRepBase2[2][1]);
  K2<a> := NumberField(minpoly2);
  require IsMaximal(EquationOrder(K2)) : "something went wrong, we didn't get the maximal order...";
  //exp := MinimalPolynomial(Integers(K).2);
  //exp2 := MinimalPolynomial(-Integers(K).2);
  //require comp in {exp, exp2} : Sprintf("%o \noin {%o, %o}", comp, exp, exp2);
  vprint ModAbVarRec: "Done";
  return P2, GeoEndoRepBase2;
end intrinsic;


intrinsic FindPrincipalPolarizations(P::ModMatFldElt : D:=[-10..10]) -> SeqEnum
{ FXIME: fill in doc }
  vprintf ModAbVarRec: "Finding a polarizations %o...", D;
  vtime ModAbVarRec:
  polarizations := SomePrincipalPolarizations(P : D:=D);
  vprintf ModAbVarRec: "Done, found %o polarizations\n", #polarizations;
  if #polarizations eq 0 then
    b := D[1]; e := D[#D];
    if (e - b + 1) eq #D then
      vprintf ModAbVarRec: "increasing D = %o", D;
      D := [b - #D div 2 .. e + #D div 2];
      vprintf ModAbVarRec: "to D = %o\n", D;
      vprintf ModAbVarRec: "Finding a polarizations %o...", D;
      vtime ModAbVarRec:
      polarizations := SomePrincipalPolarizations(P : D:=D);
      vprintf ModAbVarRec: "Done, found %o polarizations\n", #polarizations;
    end if;
  end if;
  return polarizations;
end intrinsic;

intrinsic ReconstructIsomorphicGenus2Curve(P::ModMatFldElt, polarizations:SeqEnum, Rational:=true) -> BoolElt, Crv
{ FIXME }
  CC := BaseRing(P);
  QQ := RationalsExtra(Precision(CC));
  for pol in polarizations do
    E, F := FrobeniusFormAlternating(Matrix(Integers(), pol));
    newP := P*Transpose(ChangeRing(F, CC));
    try
      vprintf ModAbVarRec: "Reconstructing curve...";
      vtime ModAbVarRec:
      // ReconstructCurve tries to match tangent representation, we don't really care about
      // and many times fails due to precision issues
      // perhaps, because we have modified our period matrix in a nonstandard way
      // C := ReconstructCurve(newP, QQ);
      tau := SmallPeriodMatrix(newP);
      igusa :=  AlgebraizedInvariants(tau, QQ);
      C := HyperellipticCurveFromIgusaInvariants(igusa);
      vprint ModAbVarRec: "Done";
      if Rational then
        if BaseField(C) cmpeq Rationals() then
            return true, C;
        else
            vprint ModAbVarRec: "Not over QQ";
            vprint ModAbVarRec: IgusaInvariants(C);
        end if;
      else
        return true, C;
      end if;
    catch e
      WriteStderr(e);
      vprint ModAbVarRec: "Failed :(";
    end try;
  end for;
  return false, _;
end intrinsic;



// EDGAR: we should use linear algebra over GF(2) to find the quadratic twist instead of what we do below

function BigCRT(moduli)
    oldmod := 1;
    oldvals := [0];
    for E in moduli do
        m, sols := Explode(E);
        print m;
        newvals := [];
        for sol in sols do
            for ov in oldvals do
                Append(~newvals,CRT([ov, sol], [oldmod, m]));
            end for;
        end for;
        oldmod *:= m;
        oldvals := newvals;
    end for;
    return [oldval - oldmod * (oldval div (oldmod div 2)) : oldval in oldvals];
end function;

// given two lists of primes find integers that are squares mod the first and non-squares mod the second
function SquaresMod(mods, nonmods)
    inp := [];
    for m in mods do
       Append(~inp, <m, [i : i in [0.. m-1] | KroneckerSymbol(i, m) eq 1 ]>);
    end for;
    for m in nonmods do
       Append(~inp, <m, [i : i in [0.. m-1] | KroneckerSymbol(i, m) eq -1 ]>);
    end for;
    return BigCRT(inp);
end function;

function SmallestSquareMod(mods,nonmods)
    L := SquaresMod(mods, nonmods);
    L2 := [<Abs(l), l> : l in L];
    return Sort(L2)[1][2];
end function;

intrinsic FindCorrectTwist(C::CrvHyp, f::ModSym : Bound:=100) -> RngIntElt
{ ... }
    M := ModularAbelianVariety(f);
    D := Discriminant(C);
    N := Level(f);
    sqps := [];
    nsqps := [];
    for p in PrimesUpTo(Bound) do
        if (Numerator(D) mod p eq 0) or (N mod p eq 0) then 
            print "skipping";
            print p;
            continue;
        end if;
        if EulerFactor(C,p) ne Reverse(FrobeniusPolynomial(M, p)) then
            Append(~nsqps, p);
        else
            Append(~sqps, p);
        end if;
    end for;
    return SmallestSquareMod(sqps, nsqps);
end intrinsic;



intrinsic ReconstructGenus2Curve(f::ModSym : prec:=80, ncoeffs:=10000, D:=[-10..10]) -> BoolElt, Crv
{
    FIXME
    It fails if to find PP we throw a runtime error
}
    P := PeriodMatrix(f : prec:=prec, ncoeffs:=ncoeffs);
    P2, G2 := PeriodMatrixWithMaximalOrder(P);
    polarizations := FindPrincipalPolarizations(P2 : D:=D);
    require #polarizations gt 0 : "No principal polarizations were found, perhaps increasing the D list might help you or not...";
    b, f := ReconstructIsomorphicGenus2Curve(P2, polarizations);
    require b : "No curve over rationals was found";
    return b, f;
end intrinsic;


intrinsic MakeNewformModSym(level::RngIntElt, hecke_cutters::SeqEnum[Tup]) -> ModSym
{ FIXME }
    R<x> := PolynomialRing(Rationals());
    // SetVerbose("ModularSymbols", true);
    chi := DirichletGroup(level)!1;
    hecke_cutters := [<elt[1], R!elt[2]> : elt in hecke_cutters];
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,2)));
    f := Kernel(hecke_cutters ,Snew);
    return f;
end intrinsic;





