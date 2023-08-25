// Aims to improve the functionality of Geometry/ModAbVar/periods.m
// in particular the number of Fourier coefficients is adaptive and
// and uses IntegralHomology(f::ModSym) instead of calling the magma builtin IntegralHomology(A::ModAbVar)

intrinsic PeriodMappingMatrix(f::ModSym : prec:=80) -> ModMatFldElt, RngIntElt, FldElt
  { Compute the normalized period matrix associated to f }
  // clear cache
  extra_prec := Ceiling(prec/0.95 + 10); // equality is checked at 95% of the digits or at extra 10 digits
  if assigned f`PeriodMap and Precision(BaseRing(Codomain(f`PeriodMap))) lt extra_prec then
    delete f`PeriodMap;
  end if;

  vprint ModAbVarRec: Sprintf("Computing period map, prec:=%o, for ", prec);
  vprint ModAbVarRec: Sprintf("%o...", f);
  default_prec := Precision(GetDefaultRealField());
  // this is how we control the precision of the output of Periods
  SetDefaultRealFieldPrecision(extra_prec);

  CC := ComplexFieldExtra(extra_prec);
  B := Basis(f);

  function matrix_helper(ncoeffs)
    vprintf ModAbVarRec: "Computing PeriodMapping with n = %o...", ncoeffs;
    vtime ModAbVarRec:
    return ChangeRing(Matrix([pi_f(b) : b in B]), CC) where pi_f := PeriodMapping(f, ncoeffs);
  end function;


  // before we defaulted to this guess with the first 2 replaced by 20
  ncoeffs := 0;
  ncoeffs_inc := Ceiling(2*Sqrt(Level(f))*Log(10)*prec/(2*Pi(ComplexField())));
  ncoeffs +:= 3*ncoeffs_inc;
  P0 := matrix_helper(ncoeffs);
  ncoeffs +:= ncoeffs_inc;
  P1 := matrix_helper(ncoeffs);
  // P0 and P1 live in rings with extra_prec
  // this checks if they agree up to prec
  t, e := AlmostEqualMatrix(P0, P1);
  while not t do
    // FIXME: we could do this much better
    // we could check that the errors are getting smaller and we could even estimate how much we should increase the number of coefficients
    vprint ModAbVarRec: Sprintf("Current error: %o, by using ncoeffs = %o", ComplexField(8)!e, ncoeffs);
    P0 := P1;
    ncoeffs +:= ncoeffs_inc;
    P1 := matrix_helper(ncoeffs);
    t, e := AlmostEqualMatrix(P0, P1);
    assert ncoeffs lt 50*ncoeffs_inc; // sanity check that we are converging
  end while;
  vprint ModAbVarRec: Sprintf("Final error: %o", ComplexField(8)!e);
  vprint ModAbVarRec: Sprintf("Final ncoeffs: %o", ncoeffs);
  P1 := ChangeRing(P1, ComplexFieldExtra(prec));
  // undo the default_prec
  SetDefaultRealFieldPrecision(default_prec);
  vprint ModAbVarRec: "Done with PeriodMappingMatrix";
  return Transpose(P1), ncoeffs, e;
end intrinsic;


intrinsic PeriodMatrix(f::ModSym : prec:=80, Quotient:=false) -> ModMatFldElt, ModMatRngElt
  { Compute the period matrix associated to f A_f^sub or A_f^quo }
  vprintf ModAbVarRec: "Comuting the lattices...";
  vtime ModAbVarRec:
  basis, E := IntegralHomology(f : Quotient:=Quotient);
  P := PeriodMappingMatrix(f : prec := prec);
  return P*Matrix(BaseRing(P),  Transpose(basis)), E;
end intrinsic;

intrinsic PeriodMatrixSubMagma(f::ModSym : prec:=80) -> ModMatFldElt
  { Compute the period matrix associated to f A_f^sub via Magma }
  _, ncoeffs, _ := PeriodMappingMatrix(f : prec:=prec);
  P := Matrix(Periods(f, ncoeffs)); // this should use the cached map
  assert Precision(BaseRing(P)) gt prec;
  CC := ComplexFieldExtra(prec);
  // Change convention
  P := Transpose(ChangeRing(P, CC));
  g := #Rows(P);
  P1 := Submatrix(P, 1, 1, g, g);
  P2 := Submatrix(P, 1, g + 1,g, g);
  P := HorizontalJoin(P2, P1);
  return P;
end intrinsic;

