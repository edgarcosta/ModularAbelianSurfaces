AttachSpec("~/projects/CHIMP/CHIMP.spec");
function ReadLine(line)
    s := Split(line, ":");
    label := s[1];
    out := <eval s[i] : i in [2..#s]>;
    return <label> cat out;
end function;
function ReadHashDatabase()
    ZZt := PolynomialRing(Integers());
    hash_database := AssociativeArray();
    for line in Split(Read("label_to_hash.txt")) do
        label, hash_str := Explode(Split(line, ":"));
        hash_database[label] := StringToInteger(hash_str);
    end for;
    return hash_database;
end function;
procedure CheckLine(line)
    hash_database := ReadHashDatabase();
    input := ReadLine(line);
    QQt<t> := PolynomialRing(Rationals());
    f, g := Explode([QQt!elt  : elt in input[2]]);
    C := HyperellipticCurve(f, g);
    t := TraceHash(TracesOfFrobenius(C, 2^12, 2^13));
    expected_t := hash_database[input[1]];
    if t ne expected_t  then
        printf "%o: %o != %o", input[1], expected_t, t;
    end if;
end procedure;

CheckLine(input);
exit;
