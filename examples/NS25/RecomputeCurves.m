AttachSpec("spec");
labels:=["625.2.a.a", "625.2.a.b","625.2.a.c"];


prec := 100;
    f := LMFDBNewform(label);
    res := RationalGenus2Curves(f : Precision:=prec);
    assert #res eq 1;
    b, isog, C := Explode(res[1]);
    assert b;
    assert Abs(Determinant(isog)) eq 1;
    print "A_sub = Jac(C)";
    printf "where C = %o\n", C;
    printf "Isogeny = %o\n", isog;

