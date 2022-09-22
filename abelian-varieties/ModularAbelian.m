declare verbose ModAbVarRec, 3;

import "reconstructiongenus2.m" : AlgebraizedInvariantsG2, ReconstructCurveG2, IgusaInvariantsG2;

// One can do better than this for trivial character, N square free, and when cond(chi) is a proper divisor of N, see Stein 9.19,9.21,9.22,
// but this bound (due to Buzzard) works for all spaces M_k(N,chi) and is best possible in some cases, see Stein 9.20
intrinsic SturmBound (N::RngIntElt, k::RngIntElt) -> RngIntElt
{ Sturm bound for space of modular forms of level N weight k and any character. }
    require N ge 1 and k ge 1: "Level N and weight k must be positive integers";
    m := Index(Gamma0(N));
    return Integers()!Floor(k*m/12);
end intrinsic;

intrinsic WriteStderr(s::MonStgElt)
{ write to stderr }
  E := Open("/dev/stderr", "w");
  Write(E, s);
  Flush(E);
end intrinsic;

intrinsic Strip(s::MonStgElt) -> MonStgElt
{ Removes all white space, including newlines, from the string }
 return Join(Split(Join(Split(s," "),""),"\n"),"");
end intrinsic;


intrinsic WriteStderr(e::Err)
{ write to stderr }
  WriteStderr(Sprint(e) cat "\n");
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
  vprint ModAbVarRec: Sprintf("%o...", f);
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
  PNew := Submatrix(PfullNew, 1, 1+ Ncols(PfullNew) - Dimension(f), Dimension(f) div 2, Dimension(f));
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
  vprint ModAbVarRec: "Extending lattice...";
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
  vprint ModAbVarRec: "Computing GeometricEndomorphismRepresentation...";
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

/*
intrinsic SomeIsogenousPrincipallyPolarized(P::ModMatFldElt: D:= [-10..10]) -> Assoc
{
    Returns period matrix for the d-isogenous abelian variety which is principally polarized
    for several d by using SomePolarizations
}
// FIXME: Use IsogenousPPLattices
  vprintf ModAbVarRec: "SomeIsogenousPrincipallyPolarized(P : D:=%o)...\n", D;
  polarizations := SomePolarizations(P : D:=D);
  CC := BaseRing(P);
  res := AssociativeArray();
  for pol in polarizations do //find the (1,d) polarization with the smallest d
    Zpol:= Matrix(Integers(), pol);
    E, F:= FrobeniusFormAlternating(Zpol);
    d := E[2, 4]/E[1, 3];
    key := <d, E[1, 3]>;
    Dscalar := Matrix([
                 [1, 0, 0, 0],
                 [0, 1/d, 0, 0],
                 [0, 0, 1, 0],
                 [0, 0, 0, 1]]);
    Pnew := P * Transpose(ChangeRing(Dscalar * F, CC) );
    b := IsDefined(res, key);
    if not b then
      res[key] := [];
    end if;
    Append(~res[key], Pnew);
  end for;
  vprintf ModAbVarRec: "Polarizations counts: %o\n", [<key, #res[key]> : key in Sort(SetToSequence(Keys(res)))];
  vprint ModAbVarRec: "SomeIsogenousPrincipallyPolarized: Done";
  return res;
end intrinsic;
*/

intrinsic FindPrincipalPolarizations(P::ModMatFldElt : D:=[-10..10]) -> SeqEnum
{ TODO: fill in doc }
  vprint ModAbVarRec: "Finding a polarizations %o...", D;
  vtime ModAbVarRec:
  polarizations := SomePrincipalPolarizations(P : D:=D);
  vprint ModAbVarRec: "Done, found %o polarizations\n", #polarizations;
  if #polarizations eq 0 then
    b := D[1]; e := D[#D];
    if (e - b + 1) eq #D then
      vprintf ModAbVarRec: "increasing D = %o ", D;
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


function PrettyCurve(Y)
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
    Y := ReducedMinimalWeierstrassModel(Y);
  end if;
  return Y;
end function;

intrinsic ReconstructModularCurve(f::ModSym) -> BoolElt, Crv
{ TODO: fill in doc }
    ncoeffs := SturmBound(Level(f), Weight(f)) + 100;
    vprintf ModAbVarRec: "ReconstructModularCurve(%o, %o) ", Level(f), ncoeffs;
    vprintf ModAbVarRec: "Trying to see if there is a modular curve...";
    require Dimension(f) in [2, 4]: "Expected a galois orbit of dimension 2";
    f1, f2 := Explode(qExpansionBasis(f, ncoeffs));
    R<q> := Parent(f1);
    xq := f2/f1;
    yq := Derivative(xq)*q/f1;
    function PaddedCoefficients(elt, start, e)
        return [Coefficient(elt, i) : i in [start..e]];
    end function;
    R<q> := Parent(xq);
    monomials := [<i,j> : i in [0..6], j in [0..2] | 3*j + i le 6];
    M := Matrix(
    [PaddedCoefficients(xq^i*yq^j, 0, 100) where i,j := Explode(elt) : elt in monomials]
    );
    B := Basis(Kernel(M));
    if #B eq 0 then
        return false, _;
    end if;
    b := B[1];
    S1<x> := PolynomialRing(Rationals());
    S2<y> := PolynomialRing(S1);
    fxy := &+[c*x^i*y^j where i, j := Explode(monomials[k]) : k->c in Eltseq(b) ];
    fxy /:= Coefficient(fxy, 2);
    Cf := -Coefficient(fxy, 0);
    Cg := Coefficient(fxy, 1);
    assert y^2 + Cg*y - Cf eq fxy;
    vprint ModAbVarRec: "Done!";
    return true, HyperellipticCurve(Cf, Cg);
end intrinsic;


/*
//TODO check isogenity?
intrinsic ReconstructIsomorphicGenus2Curve(P::ModMatFldElt : UpperBound:=16, tau:=false) -> BoolElt, .
{ return Curve or Igusa Invariants }
  // assume that P is a big period matrix
  require IsBigPeriodMatrix(P) : "Expects a big period matrix";
  if tau cmpeq false then
    tau := ReduceSmallPeriodMatrix(SmallPeriodMatrix(P));
  end if;
  CC := BaseRing(P);
  QQ := RationalsExtra(Precision(CC));

  J := false;
  JCC := IgusaInvariantsG2(taunew : Reduce:=false);
  _, _, _, _, J10 := Explode(J);

  if not Abs(J10)^2 lt CC`epscomp then //not a product of elliptic curves
    // over a number field this is sometimes suprisingly successful
    vprintf ModAbVarRec: "Reconstructing curve by matching tangent representation...";
    vtime ModAbVarRec:
    C, hL, b, e := ReconstructCurveG2(P, QQ : UpperBound:=UpperBound);
    if b then
      vprintf ModAbVarRec: "Done\n C = %o\n" , C;
      igusa := IgusaInvariants(C);
      ratIgusa := &and[elt in Rationals() : elt in igusa];
      // try to descend C
      if Type(BaseRing(C)) ne FldRat and ratIgusa then
        C := HyperellipticCurveFromIgusaInvariants(igusa);
      end if;
      return true, C;
    end if;
    e := Sprintf("ReconstructCurveG2 failed : %o\n", e);
    vprint ModAbVarRec: e;
    WriteStderr(e);
  end if;

  vprintf ModAbVarRec: "Recognizing igusa invariants...";
  // one would like to go for Modular invariants directly
  // but it hard to normalize them, one should instead use rational functions
  // e.g. recognize h4*h6/h10, h6^2/h12, etc
  J, _, b, e := AlgebraizedInvariantsG2(P, QQ : UpperBound:=UpperBound, type:="Igusa");
  if b then
    vprintf ModAbVarRec: "Done\n J = %o over %o\n" , J, Universe(J);
    if Universe(J) cmpeq Rationals() then
      vprint ModAbVarRec: "Descending C";
      C := HyperellipticCurveFromIgusaInvariants(J);
      return true, C;
    else
      return true, Vector(J);
    end if;
  end if;
  e := Sprintf("AlgebraizedInvariantsG2 failed : %o\n", e);
  vprint ModAbVarRec: e;
  WriteStderr(e);

  return false, _; // we failed at everything
end intrinsic;
*/


intrinsic FindCorrectQuadraticTwist(C::CrvHyp, euler_factors::UserProgram, BadPrimes: Bound:=200) -> RngIntElt
{ Find a quadratic twist such that C and it matches the given Euler factors, returns 0 if no quadratic twist is found}
  vprintf ModAbVarRec: "Find correct quadratic twist...";
  orderG := #GeometricAutomorphismGroup(C);
  vprintf ModAbVarRec: "The geometric automorphism group is of size %o.\n", orderG;
  oktofail := orderG ne 2;
  disc := Discriminant(C);
  D := Integers()! (Numerator(disc) * Denominator(disc));
  badprimes := IndexedSet(PrimeDivisors(D) cat BadPrimes cat [-1]);
  primes := Sort(SetToSequence(IndexedSet(PrimesUpTo(Bound)) diff badprimes));
  twistdata := [];
  splittingdata := [];
  // this could be written without Bound and with a while loop
  for p in primes do
    vprintf ModAbVarRec: "p = %o\nEuler factor C ", p;
    vtime ModAbVarRec:
    efc := EulerFactor(C, p);
    if IsZero(Coefficient(efc, 1)) then
      // useless prime, as efc(x) = efc(-x)
      continue;
    end if;
    vprintf ModAbVarRec: "Euler factor f ", p;
    vtime ModAbVarRec:
    eff := euler_factors(p);
    if efc eq eff then
      Append(~twistdata, 0);
    else
      if Evaluate(efc, -Parent(efc).1) ne eff then
        require oktofail : Sprintf("is not a local quadratic twist at p=%o\nefc = %o != %o = eff\n C = %o, and #G = %o", p, Eltseq(efc), Eltseq(eff), C, orderG);
        return 0;
      end if;
      Append(~twistdata, 1);
    end if;
    Append(~splittingdata, [(KroneckerSymbol(q, p) eq -1) select 1 else 0 : q in badprimes]);
    if Rank(Matrix(GF(2), splittingdata)) eq #badprimes then
      break p;
    end if;
  end for;
  try
    sol := Solution(Transpose(Matrix(GF(2), splittingdata)), Vector(GF(2), twistdata));
  catch e
    require oktofail: Sprintf("There is no quadratic twist");
    return 0;
  end try;
  vprint ModAbVarRec: "Done";
  if IsZero(sol) then
    return 1;
  else
    return &*[badprimes[i]: i->e in Eltseq(sol) | not IsZero(e)];
  end if;
end intrinsic;


intrinsic FindCorrectQuadraticTwist(C::CrvHyp, f::ModSym : Bound:=200) -> RngIntElt
{ Find a quadratic twist such that C and f have the same L-function, returns 0 if no quadratic twist is found}
  euler_factors := function(p)
    return Reverse(CharpolyOfFrobenius(f, p));
  end function;
  return FindCorrectQuadraticTwist(C, euler_factors, PrimeDivisors(Level(f)) : Bound:=Bound);
end intrinsic;



// FIXME, the output might not be a curve, but just igusa invariants over some numberfield
intrinsic ReconstructGenus2Curve(f::ModSym : prec:=80, ncoeffs:=10000, D:=[-4..4], UpperBound:=12) -> BoolElt, Any
{
TODO: add documentation
}

  procedure InLats(~res, ~Lats, F)
    L := Lattice(F);
    d := Determinant(F);
    // decide if we already seen this lattice
    if not d in Keys(Lats) then
      Lats[d] := {L};
      res := false;
    else
      res := L in Lats[d];
      if not res then
        Include(~Lats[d], L);
      end if;
    end if;
  end procedure;

  procedure AddToBins(~newbin, ~bins, key, value, compare)
    placed := false;
    for y in Keys(bins) do
      if compare(key,y) then
        Append(~bins[y], value);
        placed := true;
        break y;
      end if;
    end for;
    if not placed then
      bins[key] := [value];
    end if;
    newbin := not placed;
  end procedure;

  function CompareIgusaCC(x, y)
    return Abs(Norm(Vector(x) - Vector(y))) lt Universe(x)`epscomp;
  end function;

  procedure SortResults(~lst)
    // sort on field
    // then on curve < Igusa < G2
    // and then on size
    function TypeRank(elt)
      if ISA(Type(elt), Crv) then
        return 0;
      end if;
      assert Type(elt) eq ModTupFldElt; //aka a  vector
      if #Eltseq(elt) eq 5 then // igusa invariants
        return 1;
      end if;
      return 2;
    end function;
    degdisc := [<Degree(R), Discriminant(R), TypeRank(elt), #Strip(Sprint(Eltseq(elt)))> where R:=BaseRing(elt) : elt in lst];
    positions := [1..#lst];
    vprintf ModAbVarRec: "UnSorted: %o\n%o\n", degdisc, lst;
    ParallelSort(~degdisc, ~positions);
    lst := [* lst[j] : j in positions *];
    vprintf ModAbVarRec: "Sorted: %o\n%o\n", degdisc, lst;
  end procedure;

  function DoWeHaveARationalCurve(lst)
    // returns a boolean
    return #lst ge 1 and ISA(Type(lst[1]), Crv) and Type(BaseRing(lst[1])) eq FldRat;
  end function;




  function ReconstructIsogeneousPPs(P, bins, Js)
    /*
    We first look at minimal index PP lattices for small polarizations given by SomePolarizations
    For each PP lattice we:
      - put them in Bins according to igusa invariants over CC
      - try to immediately recognize each new igusa invariant over QQ

    If we have not succeeded so far, then after colleign all the lattices we:
      - try to recognize each new igusa invariant over a number field
      - finally loop over twists and try to match tangent representation
    */

    Lats := AssociativeArray(); // Det -> Lats
    CC := BaseRing(P);
    QQ := RationalsExtra(Precision(CC));
    res := [* *];
    polarizations := SomePolarizations(P : D:=D);
    for i->polarisation in polarizations do
      vprintf ModAbVarRec: "Looping over polarizations: %o of %o.\n", i, #polarizations;
      vprint ModAbVarRec: "Computing isogenous PP lattices...";
      vtime ModAbVarRec: isogenous := IsogenousPPLattices(polarisation : ProjToPP:=false);
      detL := [Determinant(elt) : elt in isogenous];
      ParallelSort(~detL, ~isogenous);
      for j->F in isogenous do
        vprintf ModAbVarRec: "Looping over isogenous PP lattices: %o of %o.\n", j, #isogenous;
        vprintf ModAbVarRec: "Det(L) = %o.\n", Determinant(F);
        // decide if we already seen this lattice
        b := false;
        InLats(~b, ~Lats, F);
        if b then
          continue F;
        end if;

        // Compute new period matrix
        Pnew := P*Transpose(ChangeRing(F, CC) );
        try // Reduce might fail
          taunew := ReduceSmallPeriodMatrix(SmallPeriodMatrix(Pnew));
        catch e
          continue F;
        end try;
        JCC := IgusaInvariantsG2(taunew : Reduce:=false);

        AddToBins(~b, ~bins, JCC, <taunew, Pnew, F>, CompareIgusaCC);


        if not b then // not new
          continue F;
        end if;
        vprint ModAbVarRec: "Recognizing igusa invariants over QQ...";
        vtime ModAbVarRec: b, J := AlgebraizeElementsExtra(JCC, QQ);

        if not b then // failed to recognize
          vprint ModAbVarRec: "Could not recognize igusa invariants over QQ\n";
          continue F;
        end if;

        Js[JCC] := J;
        vprintf ModAbVarRec: "Done\n J = %o\n", J;
        _, _, _, _, J10 := Explode(J);
        if J10 eq 0 then
          vprint ModAbVarRec: "We got a product of elliptic curves";
          vprintf ModAbVarRec: "Recognizing j-invariants...";
          jpair, _, b, e := AlgebraizedInvariantsG2(taunew, QQ : UpperBound:=UpperBound, type:="j", Reduce:=false);
          if b then
            vprintf ModAbVarRec: "Done\n j invariants = %o over %o\n" , jpair, Universe(jpair);
            Append(~res, Vector(jpair));
          else
            vprint ModAbVarRec: e;
            WriteStderr(e);
          end if;
        else
          C := HyperellipticCurveFromIgusaInvariants(J);
          vprintf ModAbVarRec: "C = %o\n", C;
          C := CurveExtra(C : prec := Precision(CC)-10);
          assert #GeometricHomomorphismRepresentationCC(ChangeRing(PeriodMatrix(C), CC), P) gt 0;
          Append(~res, C);
          if BaseRing(C) eq Rationals() then
            break polarisation;
          end if;
        end if;
      end for;
    end for;


    SortResults(~res);
    if DoWeHaveARationalCurve(res) then
      return res, bins, Js;
    end if;

    countbin := 0;
    for JCC->B in bins do
      countbin +:= 1;
      vprintf ModAbVarRec: "Looping over isomorphism classes: %o of %o.\n", countbin, #bins;
      _, _, _, _, J10 := Explode(JCC);

      b, val := IsDefined(Js, JCC);

      if  Abs(J10)^2 lt CC`epscomp
          or
          (b and Universe(val) eq Rationals())
          or
          #B eq 0
        then
        // is not a genus 2 curve
        // we already tried to tackle this isomorphism class via invariants
        // no twists
        continue JCC;
      end if;


      vprint ModAbVarRec: "Recognizing igusa invariants over a number field...";
      try
        vtime ModAbVarRec:
        L, J, _ := NumberFieldExtra(JCC, QQ : UpperBound:=UpperBound);
        b := true;
      catch e
        b := false;
        vprint CurveRec : "Failed to algebraize igusa invariants.";
        WriteStderr(e);
      end try;

      if b then
        vprintf ModAbVarRec: "Done\n J = %o over %o\n" , J, L;
        Js[JCC] := J;
        if L cmpeq Rationals() then
          vprint ModAbVarRec: "Constructing curve...";
          C := HyperellipticCurveFromIgusaInvariants(J);
          vprint ModAbVarRec: "C = %o\n", C;
          C := CurveExtra(C : prec := Precision(CC)-10);
          assert #GeometricHomomorphismRepresentationCC(ChangeRing(PeriodMatrix(C), CC), P) gt 0;
          Append(~res, C);
          if BaseRing(C) eq Rationals() then
            break JCC;
          end if;
          continue JCC; // no point on looping over twists over a numberfield
        else
          // we will still try to loop over twists and match tagent representation
          Append(~res, Vector(J));
        end if;
      end if;

      detB := [Determinant(elt[3]) : elt in B];
      idxB := [i : i in [1..#B]];
      ParallelSort(~detB, ~idxB);

      //for i->idx in idxB do
      for i->tuple in B do
        //tuple := B[idx];
        vprintf ModAbVarRec: "Looping over twists: %o of %o.\n", i, #B;
        _, Pnew, F := Explode(tuple);
        vprintf ModAbVarRec: "Det(Lattice) = %o.\n", Determinant(F);
        try
          vprint ModAbVarRec: "Reconstructing curve by matching tangent representation...";
          // over a number field this is sometimes suprisingly successful
          // and if the igusa invariants are over a NumberField there is not much u
          vtime ModAbVarRec:
          C, _, b := ReconstructCurveG2(Pnew, QQ : UpperBound:=UpperBound);
          if b then
            vprintf ModAbVarRec: "Done\n C = %o\n" , C;
          else
            vprint ModAbVarRec: "ReconstructCurveG2 was not successful";
          end if;
        catch e
          b := false;
          vprint ModAbVarRec: "ReconstructCurveG2: Failed :(";
          WriteStderr(e);
        end try;
        if b then
          igusa := IgusaInvariants(C);
          ratIgusa := &and[elt in Rationals() : elt in igusa];
          // try to descend C
          if Type(BaseRing(C)) ne FldRat and ratIgusa then
            C := HyperellipticCurveFromIgusaInvariants(igusa);
          end if;
          C := CurveExtra(C : prec := Precision(CC)-10);
          assert #GeometricHomomorphismRepresentationCC(ChangeRing(PeriodMatrix(C), CC), P) gt 0;
          Append(~res, C);
          if BaseRing(C) eq Rationals() then
            break JCC;
          end if;
        end if;
      end for; // loop over elements of a bin
    end for; // loop over bins
    return res, bins, Js;
  end function;


  // The work starts here:
  bins := AssociativeArray(); // JCC -> <reduced small period matrix, big period matrix?
  Js := AssociativeArray(); // JCC -> JQbar
  res := [* *];

  // just use the modular forms as potential differential forms on the curve
  b, C := ReconstructModularCurve(f);
  if b then
    res := [* C *];
  end if;

  if not DoWeHaveARationalCurve(res) then
    P := PeriodMatrix(f : prec:=prec, ncoeffs:=ncoeffs);
    vprint ModAbVarRec: "Looping over isogenous PP lattices with original period matrix";
    vtime ModAbVarRec:
    newres, bins, Js := ReconstructIsogeneousPPs(P, bins, Js);
    res cat:= newres;
    SortResults(~res);
    vprint ModAbVarRec: "Done looping over SomeIsogenousPrincipallyPolarized with original period matrix";
  end if;
  if not DoWeHaveARationalCurve(res) then
    P2, G2 := PeriodMatrixWithMaximalOrder(P);
    // if P == P2, then P was already maximal order
    if P ne P2 then
      vprint ModAbVarRec: "Looping over isogenous PP lattices with maximal order period matrix";
      // drop previous isomorphism classes, but keep the buckets
      for k in Keys(bins) do
        bins[k] := [];
      end for;
      vtime ModAbVarRec:
      newres, bins, Js := ReconstructIsogeneousPPs(P, bins, Js);
      res cat:= newres;
      SortResults(~res);
      vprint ModAbVarRec: "Done looping over SomeIsogenousPrincipallyPolarized with maximal order period matrix";
    else
      vprint ModAbVarRec: "Order already maximal";
    end if;
  end if;

  vprintf ModAbVarRec: "all the curves %o\m", res;
  if DoWeHaveARationalCurve(res) then
    C := res[1];
    vprintf ModAbVarRec: "Found curve %o\n", C;
    if #GeometricAutomorphismGroup(C) eq 2 then
      D := FindCorrectQuadraticTwist(C, f);
      vprintf ModAbVarRec: "Twisted by %o\n", D;
      C := QuadraticTwist(C, D);
    else
      e := "The curve has more than quadratic twists";
      vprint ModAbVarRec: e;
      WriteStderr(e);
    end if;
    vtime ModAbVarRec:
    C := PrettyCurve(C);
    return true, C;
  elif #res gt 0 then
    return true, res[1];
  end if;
  return false, _;
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





