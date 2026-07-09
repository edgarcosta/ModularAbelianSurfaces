AttachSpec("/Users/aashrayajha/Documents/GitHub/ModularAbelianSurfaces/spec");

R<x> := PolynomialRing(Rationals());
C2 := HyperellipticCurve(x^6 - 13*x^4 - 38*x^3 + 6*x^2 + 22*x + 6, x^3 + x + 1);
C3 := HyperellipticCurve(-3*x^4 - 8*x^3 + x^2 + 4*x + 1, x^3 + x + 1);

K<a> := NumberField(x^2 - x - 1);
C2K := ChangeRing(C2, K);
C3K := ChangeRing(C3, K);

b, phi23 := IsIsomorphic(C2K, C3K);
assert b;
assert Domain(phi23) eq C2K;
assert Codomain(phi23) eq C3K;
assert Codomain(Inverse(phi23)) eq C2K;

print "Isomorphism C2 -> C3 over K = QQ(a), a^2 - a - 1 = 0:";
print phi23;
print "Defining equations:";
print DefiningEquations(phi23);
print "Inverse defining equations:";
print DefiningEquations(Inverse(phi23));
