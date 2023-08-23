intrinsic Imaginary(M::Mtrx[FldCom]) -> Mtrx[FldRe]
{ The imaginary part of M }
    return Matrix([[Imaginary(elt) : elt in Eltseq(row)] : row in Rows(M)]);
end intrinsic;


