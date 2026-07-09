load "examples/NS25/Load625PeriodData.m";

QQ := RationalsExtra(prec);

time homsAlg, hQQ := GeometricHomomorphismRepresentation(PiC, PiM, QQ);
printf "#geometric/algebraized homs = %o\n", #homsAlg;

time homsQQ, hBase := EndomorphismRepresentation(homsAlg, QQ, hQQ);
printf "#QQ-defined homs = %o\n", #homsQQ;

function BlockRank(H, i, j)
    blocks := [ Eltseq(Submatrix(h[2], 4*(i-1)+1, 4*(j-1)+1, 4, 4)) : h in H ];
    return Rank(Matrix(Rationals(), blocks));
end function;

function FullRankBlockDegrees(H, i, j)
    blocks := [ Submatrix(h[2], 4*(i-1)+1, 4*(j-1)+1, 4, 4) : h in H ];
    return Sort([ Abs(Determinant(B)) : B in blocks | Rank(B) eq 4 ]);
end function;

print "Geometric block ranks:";
print Matrix(Integers(), 3, 3, [BlockRank(homs, i, j) : i, j in [1..3]]);

print "Geometric full-rank block degrees from the returned basis:";
print [ <i, j, FullRankBlockDegrees(homs, i, j)> : i, j in [1..3] ];

print "QQ-defined block ranks:";
print Matrix(Integers(), 3, 3, [BlockRank(homsQQ, i, j) : i, j in [1..3]]);

print "QQ-defined full-rank block degrees from the returned basis:";
print [ <i, j, FullRankBlockDegrees(homsQQ, i, j)> : i, j in [1..3] ];
