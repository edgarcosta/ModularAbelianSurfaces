intrinsic PossibleQuadraticTwists(C::CrvHyp, euler_factors::UserProgram, BadPrimes: Bound:=200) -> RngIntElt
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
  usedprimes := []; // not used for anything
  // this could be written without Bound and with a while loop
  for p in primes do

    // Compute euler factor of the curve
    vprintf ModAbVarRec: "p = %o\nEuler factor C ", p;
    vtime ModAbVarRec:
    efc := EulerFactor(C, p);
    vprint ModAbVarRec: "Euler factor C = ", Coefficients(efc);

    // Compute euler factor of the original object
    vprintf ModAbVarRec: "Euler factor original ", p;
    vtime ModAbVarRec:
    eff := euler_factors(p);
    vprint ModAbVarRec: "Euler factor f = ", Coefficients(eff);


    efctwist := Evaluate(efc, -Parent(efc).1);
    if eff notin [efc, efctwist] then
        require oktofail : Sprintf("is not a local quadratic twist at p=%o\nefc = %o != %o = eff\n C = %o, and #G = %o", p, Eltseq(efc), Eltseq(eff), C, orderG);
        return [];
    end if;

    if efc eq efctwist then
      continue; // we cannot distinguish between either
    end if;

    Append(~usedprimes, p);
    if efc eq eff then
      Append(~twistdata, 0);
    else
      Append(~twistdata, 1);
    end if;
    Append(~splittingdata, [(KroneckerSymbol(q, p) eq -1) select 1 else 0 : q in badprimes]);
    if Rank(Matrix(GF(2), splittingdata)) eq #badprimes then
      break p;
    end if;
  end for;
  M := Transpose(Matrix(GF(2), splittingdata));
  v := Vector(GF(2), twistdata);
  vprint ModAbVarRec: badprimes, usedprimes, Rank(M), #badprimes;
  vprint ModAbVarRec: M;
  vprint ModAbVarRec: Vector(GF(2), twistdata);
  k := Nrows(M);
  solutions := [Eltseq(elt)[1..k] : elt in Kernel(VerticalJoin(M, Matrix(v))) | elt[k + 1] eq 1];
  vprint ModAbVarRec: "PossibleQuadraticTwists: Done";
  return [#r gt 0 select &*r else 1
          where r := [badprimes[i]: i->e in sol | not IsZero(e)]
    : sol in solutions];
end intrinsic;

intrinsic PossibleQuadraticTwists(C::CrvHyp, f::ModSym : Bound:=200) -> RngIntElt
{ Find a quadratic twist such that C and f have the same L-function, returns 0 if no quadratic twist is found}
  euler_factors := function(p)
    return Reverse(CharpolyOfFrobenius(f, p));
  end function;
  return PossibleQuadraticTwists(C, euler_factors, PrimeDivisors(Level(f)) : Bound:=Bound);
end intrinsic;


intrinsic RationalGenus2Curve(Omega::ModMatFldElt, f::ModSym) -> BoolElt, CrvHyp, .
{ Given a period matrix with the standard symplectic polarization we reconstruct a RationalGenus2Curve isomorphic as torus to Omega and isogeneous to it (we use the euler factors to fix quadratic twists)}
  vprint ModAbVarRec : "RationalGenus2Curve...";
  // First we try ReconstructGenus2Curve
  // if that fails we try to reconstruct from IgusaInvariants
  QQ := RationalsExtra(Precision(BaseRing(Omega)));
  try
    vprint ModAbVarRec : "RationalGenus2Curve calling ReconstructGenus2Curve...";
    C, _, b, e := ReconstructGenus2Curve(Omega, QQ : Base:=true);
    vprint ModAbVarRec : "done calling ReconstructGenus2Curve";
    if not b then
      vprint ModAbVarRec : "error in ReconstructGenus2Curve: " cat Sprint(e);
    end if;
  catch er
    vprint ModAbVarRec : "Exception raised in ReconstructGenus2Curve";
    b := false;
    vprint ModAbVarRec : Sprint("Exception raised in ReconstructGenus2Curve: %o", Sprint(er
    ));
  end try;
  if b then
    return true, ReducedMinimalWeierstrassModel(C), "";
  end if;
  b, J := IntegralReconstructionIgusaInvariants(Omega);
  require b : "Failed to run IntegralReconstructionIgusaInvariants";
  if J[5] eq 0 then
    jCC := ModularTojEquation(IgusaModularInvariants(Omega));
    // now we reconstruct jCC as rational numbers
    b0, a0 := RationalReconstruction(jCC[1]);
    require b0 : Sprintf("Failed to RationalReconstruction %m", jCC[1]);
    b1, a1 := RationalReconstruction(jCC[2]);
    require b1 : Sprintf("Failed to RationalReconstruction %m", jCC[2]);
    return true, [a0, a1, 1], "";
  end if;
  C := HyperellipticCurveFromIgusaInvariants(J);
  if Type(BaseRing(C)) ne FldRat then
    return false, J, "No curve with given Igusa invariants defined over QQ";
  end if;
  D := PossibleQuadraticTwists(C, f);
  vprintf ModAbVarRec: "Possible twisted by %o\n", D;
  if #D eq 1 then
    C := QuadraticTwist(C, D[1]);
    return true, ReducedMinimalWeierstrassModel(C), _;
  else
    return false, J, "The curve is off by more than quadratic twists";
  end if;
end intrinsic;


intrinsic RationalGenus2Curves(f::ModSym : prec:=80, Quotient:=false, MaximalEnd:=false, OnlyOne:=false) -> List
{
  Return a boolean, an isomorphsim and Curve/Igusa invariants/j-invariants assobiated to each rational principal polarizations for Af (or quotient) of J_0(N) associated to f.
  (If MaximalEnd is true, then it is replaced by the isogenous variety such that End(Af) is maximal.)
  }
  vprintf ModAbVarRec : "RationalGenus2Curves <prec, Quotient, MaximalEnd> = %o...\n", <prec, Quotient, MaximalEnd>;
  // to compute the principal polarizations we don't need the full precision
  PPs := RationalPrincipalPolarizations(f : prec:=prec div 2, Quotient:=Quotient, MaximalEnd:=MaximalEnd);
  vprintf ModAbVarRec: "RationalGenus2Curves: #PPSs = %o\n", #PPs;

  res := [* *];
  if #pps eq 0 then
    return res;
  end if;
  Omega := PeriodMatrix(f : prec:=prec, Quotient:=Quotient, MaximalEnd:=MaximalEnd);
  CC := BaseRing(Omega);
  for i->pp in PPs do
    vprintf ModAbVarRec: "Trying polarization = %o\n", i;
      _, F := FrobeniusFormAlternating(pp);
      newOmega := Omega*Transpose(Matrix(CC, F));
      b, C, e := RationalGenus2Curve(newOmega, f);
      Append(~res, <b, F, C, e>);
      if b then
        vprint ModAbVarRec : "RationalGenus2Curves: found curve!";
        vprintf ModAbVarRec: "C = %o\n", C;
        if OnlyOne then
          return res;
        end if;
      end if;
  end for;
  return res;

  // sorting doesnt really make sense anymore
  vprint ModAbVarRec : "RationalGenus2Curves: sorting results";
  // no curves were found
  if #res eq 0 then
    return true, [], [], _;
  else
    for r in res do
      if "twists" in r[3] then
        return false, r[1], r[2], r[3];
      end if;
    end for;
    // no twist has been mentioned
    return false, r[1], r[2], r[3] where r := res[1];
  end if;
end intrinsic;

