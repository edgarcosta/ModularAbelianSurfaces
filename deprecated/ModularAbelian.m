declare verbose ModAbVarRec, 3;



import "reconstructiongenus2.m" : AlgebraizedInvariantsG2, IgusaInvariantsG2;



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


intrinsic PeriodMatrixWithMaximalOrder(P::ModMatFldElt, E::AlgMatElt) -> ModMatFldElt, AlgMatElt, AlgMatElt, SeqEnum, RngOrd
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
  vprint ModAbVarRec: "Done computing GeometricEndomorphismRepresentation";
  require #GeoEndoRepBase eq 2: Sprintf("This does not seem to be GL2-type, dim End A = %o", #GeoEndoRepBase);
  one := GeoEndoRepBase[1][2];
  gen := GeoEndoRepBase[2][2];
  assert one eq 1 or one eq -1;
  minpoly := MinimalPolynomial(gen); //need to make (D + sqrt(D)) where D is the discriminant
  K<a> := NumberField(minpoly);

  if IsMaximal(EquationOrder(K)) then // nothing to do
    return P, E, IdentityMatrix(Integers(), Ncols(P)),  GeoEndoRepBase, EquationOrder(K);
  end if;

  // Now we compute the isogeny R, such that P*R is an abelian variety with maximal order
  D:= Discriminant(Integers(K));
  x := Parent(minpoly).1;
  sqrtDpoly := x^2 - D;
  rts := Roots(sqrtDpoly, K);
  rt := rts[1][1];
  sqrtD := &+[c*gen^(i-1) : i->c in Eltseq(rt)];
  DpSqrtD := D*one + sqrtD;
  CC := BaseRing(P);
  // We now compute the intersection of 2*Lambda with (D + Sqrt(D))*Lambda
  kernel, bool := IntegralRightKernel(HorizontalJoin(P*2, P*Matrix(CC, DpSqrtD)));
  assert bool;

  // FIXME remove unused when 2.28-3 arrives
  S, T, unused := SmithForm(Matrix(Integers(), kernel));
  assert Submatrix(S, 1, 1, 4, 4) eq 1;
  assert Submatrix(S, 5, 1, 4, 4) eq 0;
  Tinv := T^-1;

  // we now should compute a matrix R in M_2g(ZZ)
  // such that P2 = P*R, where End(P2) = ZZ[(D + Sqrt(D))/2]
  A := Submatrix(Tinv, 1, 5, 4, 4);
  B := Submatrix(Tinv, 5, 5, 4, 4);
  R := 2*A + DpSqrtD*B;

  P2 := P*Matrix(CC, R);
  E2 := Transpose(R)*E*R;
  vprint ModAbVarRec: "Computing GeometricEndomorphismRepresentation...";
  vtime ModAbVarRec:
  GeoEndoRep2 := GeometricEndomorphismRepresentation(P2, QQ);
  vprint ModAbVarRec: "Done computing GeometricEndomorphismRepresentation";
  require #GeoEndoRep2 ge 2: Sprintf("This does not seem to be GL2-type, dim End newA_bar = %o", #GeoEndoRep2);
  F, h := InclusionOfBaseExtra(BaseRing(GeoEndoRep2[1][1]));
  GeoEndoRepBase2 := EndomorphismRepresentation(GeoEndoRep2, F, h);
  vprint ModAbVarRec: GeoEndoRep2;
  vprint ModAbVarRec: GeoEndoRepBase2;
  require #GeoEndoRepBase2 ge 2: Sprintf("This does not seem to be GL2-type, dim End newA = %o", #GeoEndoRepBase2);
  minpoly2 := MinimalPolynomial(GeoEndoRepBase2[2][1]);
  K2<a> := NumberField(minpoly2);
  require IsMaximal(EquationOrder(K2)) : "something went wrong, we didn't get the maximal order...";
  vprint ModAbVarRec: "Done computing GeometricEndomorphismRepresentation";
  return P2, E2, R, GeoEndoRepBase2, EquationOrder(K2);
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
    vprint ModAbVarRec : Sprint("Exception raised in ReconstructGenus2Curve: %o", er);
  end try;
  if b then
    return true, ReducedMinimalWeierstrassModel(C), _;
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
    return true, [a0, a1, 1], _;
  end if;
  C := HyperellipticCurveFromIgusaInvariants(J);
  if Type(BaseRing(C)) ne FldRat then
    return false, J, "no curve with given Igusa invariants defined over QQ";
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
*/

// intrinsic RationalGenus2CurvesWithPolarization(Omega::ModMatFldElt, E::AlgMatElt, f::ModSym) -> BoolElt, AlgMatElt, CrvHyp, .
// { From a period matrix Omega and a pairing E associated to f, return a boolean, an isomorphsim and Curve/Igusa invariants/j-invariants assobiated to one ot the principal polarizations }
//   vprint ModAbVarRec : "RationalGenus2CurvesWithPolarization...";
//   PPs := RationalPrincipalPolarizations(Omega, E);
//   QQ := RationalsExtra(Precision(BaseRing(Omega)));
//   vprintf ModAbVarRec: "#PPSs = %o\n", #PPs;
//   res := [* *];
//   for i->pp in PPs do
//     vprintf ModAbVarRec: "Trying polarization = %o\n", i;
//       newOmega, F := Explode(pp); // newOmega == Omega * F
//       b, C, e := RationalGenus2Curve(newOmega, f);
//       if b then
//         vprint ModAbVarRec : "RationalGenus2CurvesWithPolarization: found curve!";
//         return b, F, C, _;
//       else
//           Append(~res, <F, C, e>);
//       end if;
//   end for;
//   vprint ModAbVarRec : "RationalGenus2CurvesWithPolarization: sorting results";
//   // no curves were found
//   if #res eq 0 then
//     return true, [], [], _;
//   else
//     for r in res do
//       if "twists" in r[3] then
//         return false, r[1], r[2], r[3];
//       end if;
//     end for;
//     // no twist has been mentioned
//     return false, r[1], r[2], r[3] where r := res[1];
//   end if;
// end intrinsic;




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

// intrinsic FindPrincipalPolarizations(P::ModMatFldElt : D:=[-10..10]) -> SeqEnum
// { TODO: fill in doc }
//   vprintf ModAbVarRec: "Finding a polarizations %o...", D;
//   vtime ModAbVarRec:
//   polarizations := SomePrincipalPolarizations(P : D:=D);
//   vprint ModAbVarRec: "Done, found %o polarizations\n", #polarizations;
//   if #polarizations eq 0 then
//     b := D[1]; e := D[#D];
//     if (e - b + 1) eq #D then
//       vprintf ModAbVarRec: "increasing D = %o ", D;
//       D := [b - #D div 2 .. e + #D div 2];
//       vprintf ModAbVarRec: "to D = %o\n", D;
//       vprintf ModAbVarRec: "Finding a polarizations %o...", D;
//       vtime ModAbVarRec:
//       polarizations := SomePrincipalPolarizations(P : D:=D);
//       vprintf ModAbVarRec: "Done, found %o polarizations\n", #polarizations;
//     end if;
//   end if;
//   return polarizations;
// end intrinsic;






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
    C, hL, b, e := ReconstructGenus2Curve(P, QQ : UpperBound:=UpperBound);
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






// // FIXME, the output might not be a curve, but just igusa invariants over some numberfield
// intrinsic ReconstructGenus2Curve(f::ModSym : prec:=80, D:=[-4..4], UpperBound:=12) -> BoolElt, Any
// {
// TODO: add documentation
// }

//   procedure InLats(~res, ~Lats, F)
//     L := Lattice(F);
//     d := Determinant(F);
//     // decide if we already seen this lattice
//     if not d in Keys(Lats) then
//       Lats[d] := {L};
//       res := false;
//     else
//       res := L in Lats[d];
//       if not res then
//         Include(~Lats[d], L);
//       end if;
//     end if;
//   end procedure;

//   procedure AddToBins(~newbin, ~bins, key, value, compare)
//     placed := false;
//     for y in Keys(bins) do
//       if compare(key,y) then
//         Append(~bins[y], value);
//         placed := true;
//         break y;
//       end if;
//     end for;
//     if not placed then
//       bins[key] := [value];
//     end if;
//     newbin := not placed;
//   end procedure;

//   function CompareIgusaCC(x, y)
//     return Abs(Norm(Vector(x) - Vector(y))) lt Universe(x)`epscomp;
//   end function;

//   procedure SortResults(~lst)
//     // sort on field
//     // then on curve < Igusa < G2
//     // and then on size
//     function TypeRank(elt)
//       if ISA(Type(elt), Crv) then
//         return 0;
//       end if;
//       assert Type(elt) eq ModTupFldElt; //aka a  vector
//       if #Eltseq(elt) eq 5 then // igusa invariants
//         return 1;
//       end if;
//       return 2;
//     end function;
//     degdisc := [<Degree(R), Discriminant(R), TypeRank(elt), #StripWhiteSpace(Sprint(Eltseq(elt)))> where R:=BaseRing(elt) : elt in lst];
//     positions := [1..#lst];
//     vprintf ModAbVarRec: "UnSorted: %o\n%o\n", degdisc, lst;
//     ParallelSort(~degdisc, ~positions);
//     lst := [* lst[j] : j in positions *];
//     vprintf ModAbVarRec: "Sorted: %o\n%o\n", degdisc, lst;
//   end procedure;

//   function DoWeHaveARationalCurve(lst)
//     // returns a boolean
//     return #lst ge 1 and ISA(Type(lst[1]), Crv) and Type(BaseRing(lst[1])) eq FldRat;
//   end function;




//   function ReconstructIsogeneousPPs(P, bins, Js)
//     /*
//     We first look at minimal index PP lattices for small polarizations given by SomePolarizations
//     For each PP lattice we:
//       - put them in Bins according to igusa invariants over CC
//       - try to immediately recognize each new igusa invariant over QQ

//     If we have not succeeded so far, then after colleign all the lattices we:
//       - try to recognize each new igusa invariant over a number field
//       - finally loop over twists and try to match tangent representation
//     */

//     Lats := AssociativeArray(); // Det -> Lats
//     CC := BaseRing(P);
//     QQ := RationalsExtra(Precision(CC));
//     res := [* *];
//     polarizations := SomePolarizations(P : D:=D);
//     for i->polarisation in polarizations do
//       vprintf ModAbVarRec: "Looping over polarizations: %o of %o.\n", i, #polarizations;
//       vprint ModAbVarRec: "Computing isogenous PP lattices...";
//       vtime ModAbVarRec: isogenous := IsogenousPPLattices(polarisation : ProjToPP:=false);
//       detL := [Determinant(elt) : elt in isogenous];
//       ParallelSort(~detL, ~isogenous);
//       for j->F in isogenous do
//         vprintf ModAbVarRec: "Looping over isogenous PP lattices: %o of %o.\n", j, #isogenous;
//         vprintf ModAbVarRec: "Det(L) = %o.\n", Determinant(F);
//         // decide if we already seen this lattice
//         b := false;
//         InLats(~b, ~Lats, F);
//         if b then
//           continue F;
//         end if;

//         // Compute new period matrix
//         Pnew := P*Transpose(ChangeRing(F, CC) );
//         try // Reduce might fail
//           taunew := ReduceSmallPeriodMatrix(SmallPeriodMatrix(Pnew));
//         catch e
//           continue F;
//         end try;
//         JCC := IgusaInvariantsG2(taunew : Reduce:=false);

//         AddToBins(~b, ~bins, JCC, <taunew, Pnew, F>, CompareIgusaCC);


//         if not b then // not new
//           continue F;
//         end if;
//         vprint ModAbVarRec: "Recognizing igusa invariants over QQ...";
//         vtime ModAbVarRec: b, J := AlgebraizeElementsExtra(JCC, QQ);

//         if not b then // failed to recognize
//           vprint ModAbVarRec: "Could not recognize igusa invariants over QQ\n";
//           continue F;
//         end if;

//         Js[JCC] := J;
//         vprintf ModAbVarRec: "Done\n J = %o\n", J;
//         _, _, _, _, J10 := Explode(J);
//         if J10 eq 0 then
//           vprint ModAbVarRec: "We got a product of elliptic curves";
//           vprintf ModAbVarRec: "Recognizing j-invariants...";
//           jpair, _, b, e := AlgebraizedInvariantsG2(taunew, QQ : UpperBound:=UpperBound, type:="j", Reduce:=false);
//           if b then
//             vprintf ModAbVarRec: "Done\n j invariants = %o over %o\n" , jpair, Universe(jpair);
//             Append(~res, Vector(jpair));
//           else
//             vprint ModAbVarRec: e;
//             WriteStderr(e);
//           end if;
//         else
//           C := HyperellipticCurveFromIgusaInvariants(J);
//           vprintf ModAbVarRec: "C = %o\n", C;
//           C := CurveExtra(C : prec := Precision(CC)-10);
//           assert #GeometricHomomorphismRepresentationCC(ChangeRing(PeriodMatrix(C), CC), P) gt 0;
//           Append(~res, C);
//           if BaseRing(C) eq Rationals() then
//             break polarisation;
//           end if;
//         end if;
//       end for;
//     end for;


//     SortResults(~res);
//     if DoWeHaveARationalCurve(res) then
//       return res, bins, Js;
//     end if;

//     countbin := 0;
//     for JCC->B in bins do
//       countbin +:= 1;
//       vprintf ModAbVarRec: "Looping over isomorphism classes: %o of %o.\n", countbin, #bins;
//       _, _, _, _, J10 := Explode(JCC);

//       b, val := IsDefined(Js, JCC);

//       if  Abs(J10)^2 lt CC`epscomp
//           or
//           (b and Universe(val) eq Rationals())
//           or
//           #B eq 0
//         then
//         // is not a genus 2 curve
//         // we already tried to tackle this isomorphism class via invariants
//         // no twists
//         continue JCC;
//       end if;


//       vprint ModAbVarRec: "Recognizing igusa invariants over a number field...";
//       try
//         vtime ModAbVarRec:
//         L, J, _ := NumberFieldExtra(JCC, QQ : UpperBound:=UpperBound);
//         b := true;
//       catch e
//         b := false;
//         vprint CurveRec : "Failed to algebraize igusa invariants.";
//         WriteStderr(e);
//       end try;

//       if b then
//         vprintf ModAbVarRec: "Done\n J = %o over %o\n" , J, L;
//         Js[JCC] := J;
//         if L cmpeq Rationals() then
//           vprint ModAbVarRec: "Constructing curve...";
//           C := HyperellipticCurveFromIgusaInvariants(J);
//           vprint ModAbVarRec: "C = %o\n", C;
//           C := CurveExtra(C : prec := Precision(CC)-10);
//           assert #GeometricHomomorphismRepresentationCC(ChangeRing(PeriodMatrix(C), CC), P) gt 0;
//           Append(~res, C);
//           if BaseRing(C) eq Rationals() then
//             break JCC;
//           end if;
//           continue JCC; // no point on looping over twists over a numberfield
//         else
//           // we will still try to loop over twists and match tagent representation
//           Append(~res, Vector(J));
//         end if;
//       end if;

//       detB := [Determinant(elt[3]) : elt in B];
//       idxB := [i : i in [1..#B]];
//       ParallelSort(~detB, ~idxB);

//       //for i->idx in idxB do
//       for i->tuple in B do
//         //tuple := B[idx];
//         vprintf ModAbVarRec: "Looping over twists: %o of %o.\n", i, #B;
//         _, Pnew, F := Explode(tuple);
//         vprintf ModAbVarRec: "Det(Lattice) = %o.\n", Determinant(F);
//         try
//           vprint ModAbVarRec: "Reconstructing curve by matching tangent representation...";
//           // over a number field this is sometimes suprisingly successful
//           // and if the igusa invariants are over a NumberField there is not much u
//           vtime ModAbVarRec:
//           C, _, b := ReconstructGenus2Curve(Pnew, QQ : UpperBound:=UpperBound);
//           if b then
//             vprintf ModAbVarRec: "Done\n C = %o\n" , C;
//           else
//             vprint ModAbVarRec: "ReconstructCurveG2 was not successful";
//           end if;
//         catch e
//           b := false;
//           vprint ModAbVarRec: "ReconstructCurveG2: Failed :(";
//           WriteStderr(e);
//         end try;
//         if b then
//           igusa := IgusaInvariants(C);
//           ratIgusa := &and[elt in Rationals() : elt in igusa];
//           // try to descend C
//           if Type(BaseRing(C)) ne FldRat and ratIgusa then
//             C := HyperellipticCurveFromIgusaInvariants(igusa);
//           end if;
//           C := CurveExtra(C : prec := Precision(CC)-10);
//           assert #GeometricHomomorphismRepresentationCC(ChangeRing(PeriodMatrix(C), CC), P) gt 0;
//           Append(~res, C);
//           if BaseRing(C) eq Rationals() then
//             break JCC;
//           end if;
//         end if;
//       end for; // loop over elements of a bin
//     end for; // loop over bins
//     return res, bins, Js;
//   end function;


//   // The work starts here:
//   bins := AssociativeArray(); // JCC -> <reduced small period matrix, big period matrix?
//   Js := AssociativeArray(); // JCC -> JQbar
//   res := [* *];

//   // just use the modular forms as potential differential forms on the curve
//   b, C := ReconstructModularCurve(f);
//   if b then
//     res := [* C *];
//   end if;

//   if not DoWeHaveARationalCurve(res) then
//     P := PeriodMatrix(f : prec:=prec);
//     vprint ModAbVarRec: "Looping over isogenous PP lattices with original period matrix";
//     vtime ModAbVarRec:
//     newres, bins, Js := ReconstructIsogeneousPPs(P, bins, Js);
//     res cat:= newres;
//     SortResults(~res);
//     vprint ModAbVarRec: "Done looping over SomeIsogenousPrincipallyPolarized with original period matrix";
//   end if;
//   if not DoWeHaveARationalCurve(res) then
//     P2, G2 := PeriodMatrixWithMaximalOrder(P);
//     // if P == P2, then P was already maximal order
//     if P ne P2 then
//       vprint ModAbVarRec: "Looping over isogenous PP lattices with maximal order period matrix";
//       // drop previous isomorphism classes, but keep the buckets
//       for k in Keys(bins) do
//         bins[k] := [];
//       end for;
//       vtime ModAbVarRec:
//       newres, bins, Js := ReconstructIsogeneousPPs(P, bins, Js);
//       res cat:= newres;
//       SortResults(~res);
//       vprint ModAbVarRec: "Done looping over SomeIsogenousPrincipallyPolarized with maximal order period matrix";
//     else
//       vprint ModAbVarRec: "Order already maximal";
//     end if;
//   end if;

//   vprintf ModAbVarRec: "all the curves %o\m", res;
//   if DoWeHaveARationalCurve(res) then
//     C := res[1];
//     vprintf ModAbVarRec: "Found curve %o\n", C;
//     D := PossibleQuadraticTwists(C, f);
//     vprintf ModAbVarRec: "Possible twisted by %o\n", D;
//     if #D eq 1 then
//       C := QuadraticTwist(C, D[1]);
//     else
//       e := "The curve has more than quadratic twists";
//       vprint ModAbVarRec: e;
//       WriteStderr(e);
//     end if;
//     vtime ModAbVarRec:
//     C := ReducedMinimalWeierstrassModel(C);
//     return true, C;
//   elif #res gt 0 then
//     return true, res[1];
//   end if;
//   return false, _;
// end intrinsic;







