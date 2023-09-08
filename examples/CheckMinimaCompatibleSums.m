/*
	Computational proof of a statement in [Bom+23] R. van Bommel, J. Docking, V. Dokchitser, R. Lercier and E. Lorenzo García, Reduction of plane quartics and Cayley octads, arXiv:xxx.

   This script assumes that the spec file "g3cayley/magma/spec" is loaded
   at magma startup (in the .magmarc file).
*/

// Building Block Precomputations
_, KeySets        := PluckerCoordinates([ [0,0,0,0] : i in [1..8] ]);

_, BuildingBlocks, IsBBCompatible := CayleyOctadDiagram(
    Vector([Rationals()|0 : i in [1..#KeySets]]));

Tw,  Pl,  TA, TB,  CA, CB, CC,  Ln := Explode(BuildingBlocks);

Things := [* *];
for key in Keys(Tw) do Append(~Things, <"Tw", key>); end for;
for key in Keys(Pl) do Append(~Things, <"Pl", key>); end for;
for key in Keys(TA) do Append(~Things, <"TA", key>); end for;
for key in Keys(TB) do Append(~Things, <"TB", key>); end for;
for key in Keys(CA) do Append(~Things, <"CA", key>); end for;
for key in Keys(CB) do Append(~Things, <"CB", key>); end for;
for key in Keys(CC) do Append(~Things, <"CC", key>); end for;
for key in Keys(Ln) do Append(~Things, <"Ln", key>); end for;


// We only list the building block vector for which the first five points are in standard position.
I5 := [i : i in [1..70] | KeySets[i] subset {1..5}];
V := [* < t, [v : v in (eval t[1])[t[2]] | {true} eq {v[i] eq 0 : i in I5} ] > : t in Things *];
assert({1} eq {#v[2] : v in V});
CompatibilityMatrix := [ [ IsBBCompatible(Things[i], Things[j]) : i in [1..#Things] ] : j in [1..#Things] ];

// We construct all compatible sets of blocks
Queue := { <{Integers()| }, {1..#Things}> };
AllCompatibleSubsets := { Universe({{0}}) | };
while #Queue gt 0 do
    S := Representative(Queue);
    Exclude(~Queue, S);
    Include(~AllCompatibleSubsets, S[1]);
    for i in S[2] do
        Include(~Queue, <Include(S[1], i), {j : j in S[2] | (i gt j) and CompatibilityMatrix[i][j]}>);
    end for;
end while;

// For each compatible set of blocks, we check that their sum is still normalised in the sense that the three minima are still zero.
for S in AllCompatibleSubsets do
    if #S eq 0 then
        continue;
    end if;
    w := &+[V[i][2][1] : i in S];
    if w ne NormaliseValuationData(w) then
        print S;
        break;
    end if;
end for;
