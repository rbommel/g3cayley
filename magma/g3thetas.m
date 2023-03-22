/***
 * Exported intrinsics.
 *
 * intrinsic G3ThetaCharParity(i::RngIntElt) -> BoolElt
 * {The parity of the i-th thetaconstant (in the Aronhold numbering)}
 *
 * intrinsic G3ThetaFromOctad(i::RngIntElt, Plck::SeqEnum) -> Any
 * {On input Plucker coordinates, return the i-th thetaconstant (in the Aronhold numbering)}
 *
 ********************************************************************/

import "bblocks.m" : KeySets;

ThetaIdx := [
    [ 1, 6, 7, 8, 2, 3, 4, 5 ],
    [ 1, 3, 5, 6, 2, 4, 7, 8 ],
    [ 1, 2, 4, 6, 3, 5, 7, 8 ],
    [ 1, 3, 4, 8, 2, 5, 6, 7 ],
    [ 1, 2, 5, 8, 3, 4, 6, 7 ],
    [ 1, 2, 3, 7, 4, 5, 6, 8 ],
    [ 1, 4, 5, 7, 2, 3, 6, 8 ],
    [ 1, 5, 7, 8, 2, 3, 4, 6 ],
    [],
    [ 1, 2, 4, 5, 3, 6, 7, 8 ],
    [],
    [ 1, 2, 6, 8, 3, 4, 5, 7 ],
    [],
    [ 1, 4, 6, 7, 2, 3, 5, 8 ],
    [],
    [ 1, 4, 5, 6, 2, 3, 7, 8 ],
    [ 1, 2, 3, 6, 4, 5, 7, 8 ],
    [],
    [],
    [ 1, 2, 4, 7, 3, 5, 6, 8 ],
    [ 1, 3, 5, 7, 2, 4, 6, 8 ],
    [],
    [],
    [ 1, 2, 3, 5, 4, 6, 7, 8 ],
    [],
    [],
    [ 1, 2, 7, 8, 3, 4, 5, 6 ],
    [ 1, 3, 6, 7, 2, 4, 5, 8 ],
    [],
    [],
    [ 1, 5, 6, 8, 2, 3, 4, 7 ],
    [ 1, 3, 4, 7, 2, 5, 6, 8 ],
    [ 1, 2, 5, 7, 3, 4, 6, 8 ],
    [ 1, 2, 3, 8, 4, 5, 6, 7 ],
    [ 1, 4, 5, 8, 2, 3, 6, 7 ],
    [],
    [],
    [],
    [],
    [ 1, 2, 6, 7, 3, 4, 5, 8 ],
    [],
    [ 1, 4, 6, 8, 2, 3, 5, 7 ],
    [],
    [],
    [ 1, 2, 3, 4, 5, 6, 7, 8 ],
    [],
    [ 1, 3, 7, 8, 2, 4, 5, 6 ],
    [ 1, 2, 4, 8, 3, 5, 6, 7 ],
    [ 1, 3, 5, 8, 2, 4, 6, 7 ],
    [],
    [],
    [],
    [],
    [ 1, 2, 5, 6, 3, 4, 7, 8 ],
    [ 1, 3, 4, 6, 2, 5, 7, 8 ],
    [ 1, 3, 6, 8, 2, 4, 5, 7 ],
    [],
    [],
    [ 1, 5, 6, 7, 2, 3, 4, 8 ],
    [],
    [ 1, 4, 7, 8, 2, 3, 5, 6 ],
    [ 1, 3, 4, 5, 2, 6, 7, 8 ],
    [],
    []
];

intrinsic G3ThetaCharParity(i::RngIntElt) -> BoolElt
    {The parity of the i-th thetaconstant (in the Aronhold numbering)}

    return (i eq 64) or (#ThetaIdx[i] ne 0);
end intrinsic;

intrinsic G3ThetaFromOctad(i::RngIntElt, Plck::SeqEnum) -> Any
    {On input Plucker coordinates, return the i-th thetaconstant (in the Aronhold numbering)}

    BF := Universe(Plck);

    /* Easy cases */
    if i eq 64 then return One(BF); end if;

    if #ThetaIdx[i] eq 0 then return Zero(BF); end if;

    L := ThetaIdx[i];

    /* Decode Plucker coordinates */
    p := AssociativeArray(); for j := 1 to #KeySets do p[KeySets[j]] := Plck[j]; end for;

    /* Adjust the signs */
    for S in KeySets do
        sgn :=  Sign(SymmetricGroup({L[e]:e in S})![L[e] : e in S]);
        p[{L[e]:e in S}] *:= sgn;
    end for;

    /* Theta formula */
    D1 :=
        p[{L[1],L[2],L[3],L[4]}] * p[{L[1],L[2],L[6],L[7]}] * p[{L[1],L[3],L[5],L[7]}] * p[{L[1],L[4],L[5],L[6]}] -
        p[{L[1],L[5],L[6],L[7]}] * p[{L[1],L[2],L[3],L[7]}] * p[{L[1],L[2],L[4],L[6]}] * p[{L[1],L[3],L[4],L[5]}];
    D2 :=
        p[{L[1],L[2],L[3],L[4]}] * p[{L[1],L[2],L[6],L[7]}] * p[{L[2],L[3],L[5],L[7]}] * p[{L[2],L[4],L[5],L[6]}] -
        p[{L[2],L[5],L[6],L[7]}] * p[{L[1],L[2],L[3],L[7]}] * p[{L[1],L[2],L[4],L[6]}] * p[{L[2],L[3],L[4],L[5]}];
    D3 :=
        p[{L[1],L[2],L[3],L[4]}] * p[{L[2],L[3],L[6],L[7]}] * p[{L[1],L[3],L[5],L[7]}] * p[{L[3],L[4],L[5],L[6]}] -
        p[{L[3],L[5],L[6],L[7]}] * p[{L[1],L[2],L[3],L[7]}] * p[{L[2],L[3],L[4],L[6]}] * p[{L[1],L[3],L[4],L[5]}];
    D4 :=
        p[{L[1],L[2],L[3],L[4]}] * p[{L[2],L[4],L[6],L[7]}] * p[{L[3],L[4],L[5],L[7]}] * p[{L[1],L[4],L[5],L[6]}] -
        p[{L[4],L[5],L[6],L[7]}] * p[{L[2],L[3],L[4],L[7]}] * p[{L[1],L[2],L[4],L[6]}] * p[{L[1],L[3],L[4],L[5]}];

    T := (1 / (D1 * D2 * D3 * D4 )) *
        p[{L[1],L[3],L[4],L[5]}] * p[{L[2],L[3],L[4],L[5]}] * p[{L[1],L[2],L[3],L[5]}] * p[{L[1],L[2],L[4],L[5]}] *
        p[{L[1],L[3],L[4],L[6]}] * p[{L[2],L[3],L[4],L[6]}] * p[{L[1],L[2],L[3],L[6]}] * p[{L[1],L[2],L[4],L[6]}] *
        p[{L[1],L[3],L[4],L[7]}] * p[{L[1],L[2],L[3],L[7]}] * p[{L[1],L[2],L[4],L[7]}] * p[{L[2],L[3],L[4],L[7]}] *
        p[{L[1],L[5],L[6],L[7]}] * p[{L[2],L[5],L[6],L[7]}] * p[{L[3],L[5],L[6],L[7]}] * p[{L[4],L[5],L[6],L[7]}];

    return T;

end intrinsic;
