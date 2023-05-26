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


/*
 * Check that building blocks of octads on a twisted cubic curve remain twisted on a PGL orbit
 ***/
function SystemInAdditiveForm(SYS)
    M := Matrix(Rationals(),  #KeySets, #SYS,[]);
    for i := 1 to #SYS do
        Cf, Mn := CoefficientsAndMonomials(SYS[i]);
        for j := 1 to #KeySets do
            if Exponents(Mn[1])[j] eq 1 then M[j,i] := Cf[1]; end if;
            if Exponents(Mn[2])[j] eq 1 then M[j,i] := Cf[2]; end if;
        end for;
    end for;
    return M;
end function;

/*  Plucker coordinates, uniformising element */
Fpl<[pl]> := PolynomialRing(Rationals(), [ 1 : i in [1..70+1] ] );

pi := pl[70+1]; AssignNames(~Fpl,
    [ "p" cat &cat[IntegerToString(j) : j in KeySets[i] ] :
    i in [1..70]] cat ["pi"]
    );

/* Cayley relations of a regular octad, in additive form */
CayleyRels := SystemInAdditiveForm(CayleyOctadRelations([ pl[i]  : i in [1..70] ]));

/* Twisted cubic relations of a regular octad, in additive form */
TwistedRels := SystemInAdditiveForm(CayleyOctadTwistedCubicRelations([ pl[i]  : i in [1..70] ]));

/* Let's go */
for t := 1 to #[ Tw,  Pl,  TA, TB,  CA, CB, CC ] do

    type := [ Tw,  Pl,  TA, TB,  CA, CB, CC ][t];

    "Checking Building Blocks",
        [ "alpha_1", "alpha_2",  "chi_a", "chi_b", "chi_c",  "phi_a", "phi_b" ][t], "...";

    KerDims := {**};

    for key in Keys(type) do
        lst := [];

        for vO in type[key] do
            /* Plucker coordinates with this valuation data */
            PlO := [ pl[i]*pi^(Integers()!vO[i]) : i in [1..70] ];

            /* Its Twisted cubic relations*/
            TwO := CayleyOctadTwistedCubicRelations(PlO);

            /* Is this system homogenous in pi,
               otherwise skip it (no twisted cubic octad exists with this block) */
            TermDegrees :=  [ [Degree(T, pi) : T in Terms(E) ] : E in TwO ];

            if t in [ 2, 3, 5, 6 ] then
                assert { L[1] eq L[2] : L in TermDegrees } ne {true};
            else
                assert { L[1] eq L[2] : L in TermDegrees } eq {true};

                dmin := Min([ Degree(E, pi) : E in TwO ]);

                /* Restriction to the relations of valuation dmin */
                TwOValMin := Transpose(Matrix([ Transpose(TwistedRels)[i] : i in [1..#TwO] | Degree(TwO[i], pi) eq dmin ]));
                /* Let us extract a basis */
                Krn := Kernel(HorizontalJoin(CayleyRels, TwOValMin));

                Append(~lst, Krn);
                Include(~KerDims, Dimension(Krn));
            end if;

        end for;


        if #lst gt 0 then
            /* Check that these subspaces are the same for each entry */
            assert { lst[i] eq lst[j] : i, j in [1..#lst] | j gt i} eq {true};
        end if;

    end for;

    "Dimensions are", KerDims;
    "... done"; "";

end for;
