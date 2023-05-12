// In this file, we verify the claimed equivalence relations between different valuation data for chi and phi blocks.
// Moreover, we also check that that the equivalence classes are exhaustive for the situation in which 5 points are in standard position.

AttachSpec("magma/spec");
import "magma/bblocks.m" : CayleyBuildingBlocks, V70;

Things, L, W := CayleyBuildingBlocks();
Tw,  Pl,  TA, TB,  CA, CB, CC,  Ln := Explode(L);

KeySets := [
    {1,6,7,8}, {5,6,7,8},

    {2,5,7,8}, {4,6,7,8}, {4,5,6,8}, {3,5,6,8}, {1,3,6,8}, {1,2,6,8},
    {1,5,7,8}, {1,2,7,8}, {3,5,7,8}, {1,3,6,7}, {3,6,7,8}, {2,5,6,7},
    {1,5,6,8}, {1,4,6,8}, {1,2,6,7}, {4,5,7,8}, {1,3,7,8}, {2,6,7,8},
    {4,5,6,7}, {2,5,6,8}, {1,4,6,7}, {1,5,6,7}, {1,4,7,8}, {3,5,6,7},

    {1,2,3,8}, {2,4,5,8}, {1,3,5,7}, {1,3,4,7}, {2,3,5,8}, {1,4,5,8},
    {1,3,5,6}, {1,4,5,6}, {3,4,7,8}, {3,4,6,7}, {1,2,3,7}, {2,3,6,8},
    {3,4,5,7}, {2,4,6,8}, {1,2,3,6}, {2,3,7,8}, {1,2,5,8}, {1,4,5,7},
    {2,3,5,6}, {3,4,6,8}, {1,2,4,8}, {1,2,4,6}, {1,3,4,8}, {1,3,5,8},
    {1,3,4,6}, {2,4,5,7}, {2,3,5,7}, {1,2,5,7}, {2,3,6,7}, {1,2,4,7},
    {3,4,5,6}, {2,4,6,7}, {1,2,5,6}, {3,4,5,8}, {2,4,7,8}, {2,4,5,6},

    {1,3,4,5}, {1,2,3,5}, {1,2,3,4}, {2,3,4,5},
    {1,2,4,5}, {2,3,4,7}, {2,3,4,6}, {2,3,4,8}

    ];
    
v := AssociativeArray();
v := AssociativeArray(); for i := 1 to #KeySets do v[KeySets[i]] := V70.i; end for;
vPt := AssociativeArray();
vLn := AssociativeArray();
vPl := AssociativeArray();
for S in Subsets({1..8}) do
	vPt[S] := &+[ Max(0, #(s meet S) - 1)*v[s] : s in KeySets ];
	vLn[S] := &+[ Max(0, #(s meet S) - 2)*v[s] : s in KeySets ];
	vPl[S] := &+[ Max(0, #(s meet S) - 3)*v[s] : s in KeySets ];
end for;

// These are chi blocks
TA1, TA2, TA3 := Explode(TA[<{1,2}, {{3,4,5},{6,7,8}}>]);
assert(TA2 - vPt[{1,2}] + vPl[{3..8}] eq TA1);
assert(TA3 - vPt[{3,4,5}] + vPl[{1,2,6,7,8}] eq TA2);

TB1, TB2, TB3 := Explode(TB[{1,2,3}]);
assert(TB2 - vPt[{1,2,3}] + vPl[{4..8}] eq TB3);
assert(TB3 + vPl[{2..8}] - vPt[{2,3}] + vPl[{1,4,5,6,7,8}] eq TB1);

// These are phi blocks.
CA1 := vLn[{1,2,5,6}] + vLn[{1,2,7,8}] + vPl[{1,2,3,4}] + vPl[{5,6,7,8}];
_,_,_,_,CA2,_ := Explode(CA[{{{1,2},{3,4}},{{5,6},{7,8}}}]);
assert(CA1 eq CA2 - vPt[{3,4}] + vPl[{1,2,5,6,7,8}]);

CB1 := Explode(CB[<{4,5},{{1,2,3},{6,7,8}}>]);
CB2 := vPt[{4,5}] + vLn[{1,2,3,4}] + vLn[{1,2,3,5}];
CB3 := vLn[{1,2,3,4}] + vLn[{1,2,3,5}] + vPl[{1,2,3,6,7,8}];
assert(CB2 - vPt[{4,5}] + vPl[{1,2,3,6,7,8}] eq CB3);
assert(CB3 - vPt[{1,2,3}] + vPl[{4..8}] eq CB1);

CC1 := vLn[{1,2,3,4}] + vPl[{1,2,3,4}] + vPl[{5,6,7,8}];
CC2 := vPt[{1,2,3,4}] + vLn[{1,2,3,4}] + vPl[{1,2,3,4}];
assert(CC2 - vPt[{1,2,3,4}] + vPl[{5,6,7,8}] eq CC1);

// For all permutations of the blocks, we check the 5-tuples of points that are in general position.
// For each block, each 5-tuple should be in general position for exactly one of the valuation data corresponding to that block.
function IndependentFives(v1)
	return {* s : s in Subsets({1..8}, 5) | {0} eq {v1[Index(KeySets,t)] : t in Subsets(s,4)} *};
end function;

assert(&join[IndependentFives(v) : v in TA[<{1,2}, {{3,4,5},{6,7,8}}>] ] eq {* S : S in Subsets({1..8},5) *});
assert(&join[IndependentFives(v) : v in TB[{1,2,3}] ] eq {* S : S in Subsets({1..8},5) *});
assert(&join[IndependentFives(v) : v in CA[{{{1,2},{3,4}},{{5,6},{7,8}}}] ] eq {* S : S in Subsets({1..8},5) *});
assert(&join[IndependentFives(v) : v in CB[<{1,2}, {{3,4,5},{6,7,8}}>] ] eq {* S : S in Subsets({1..8},5) *});
assert(&join[IndependentFives(v) : v in CC[{{1,2,3,4},{5,6,7,8}}] ] eq {* S : S in Subsets({1..8},5) *});
