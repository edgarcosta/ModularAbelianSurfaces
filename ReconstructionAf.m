
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
    return true, (C), "";
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

