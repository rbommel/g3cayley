/*
   Computational proof of a statement in [Bom+23] R. van Bommel, J. Docking, V. Dokchitser, R. Lercier and E. Lorenzo García, Reduction of plane quartics and Cayley octads, arXiv:xxx.

   This file describes a proof of the unicity of the block decomposition (if it exists).

   This script assumes that the spec file "g3cayley/magma/spec" is loaded
   at magma startup (in the .magmarc file).
*/

// Building Block Precomputations
_, KeySets        := PluckerCoordinates([ [0,0,0,0] : i in [1..8] ]);

_, _, BuildingBlocks, IsBBCompatible := CayleyOctadDiagram(
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

V := [* < t, (eval t[1])[t[2]] > : t in Things *];

CompatibilityMatrix := [ [ IsBBCompatible(Things[i], Things[j]) : i in [1..#Things] ] : j in [1..#Things] ];

// Computing all 2626648 compatible sets of building blocks.
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

// Creating a fast way to look up permutations applied to building blocks.
function ApplyPermutation(T, sigma)
	if Type(T) eq Tup then
		return <ApplyPermutation(t, sigma) : t in T>;
	elif Type(T) eq SetEnum then
		return {ApplyPermutation(t, sigma) : t in T};
	elif Type(T) eq MonStgElt then
		return T;
	elif Type(T) eq RngIntElt then
		return sigma[T];
	elif Type(T) eq List then
		return [* ApplyPermutation(t, sigma) : t in T *];
	end if;
	assert false;
end function;

LookupTable := AssociativeArray();
for S in {t[1] : t in Things} do
	LookupTable[S] := AssociativeArray();
end for;
for i->t in Things do
	LookupTable[t[1]][t[2]] := i;
end for;

function FindThing(T)
	return LookupTable[T[1]][T[2]];
end function;

ThingsPermutations := AssociativeArray();
for sigma in Permutations({1..8}) do
	ThingsPermutations[sigma] := [];
	for t in Things do
		sigma_t := ApplyPermutation(t, sigma);
		Append(~ThingsPermutations[sigma], FindThing(sigma_t));
	end for;
end for;

// Find one representative for each of the 507 S8 equivalence class of sets of compatible building blocks.
S8Reps := {};
C := AllCompatibleSubsets;
while #C gt 1 do
	S := Representative(C);
	Include(~S8Reps, S);
	for sigma in Permutations({1..8}) do
		Ssigma := {ThingsPermutations[sigma][i] : i in S};
		Exclude(~C, Ssigma);
	end for;
end while;

// Create the quotient space in which the computations will take place.
V70 := Parent(V[1,2,1]);
W8 := sub< V70 | [ &+[V70.j : j in [1..70] | i in KeySets[j]] : i in [1..8] ] >;
Wquo, phi := V70 / W8;
Vquo := [sub<Wquo | [ phi(x) : x in y[2]]> : y in V];
vquo := [ phi(y[2][1]) : y in V];

// We will compare the compatible sets R1 and R2 of building blocks against each other, w.l.o.g. we take R1 in the set of S8 representatives.
for R1 in S8Reps do
	for R2 in AllCompatibleSubsets do
		if #R2 eq 0 then
			continue;
		end if;
		R12 := [x : x in R1 | x in R2];	// Intersection of R1 and R2
		R11 := [x : x in R1 | not(x in R2)];	// Part of R1 not in R2
		R22 := [x : x in R2 | not(x in R1)];	// Part of R2 not in R1
		K := Kernel(Matrix([vquo[i] : i in R11 cat R22 cat R12]));
		if Dimension(K) eq 0 then
			continue;	// If there is no relation, we are done with this pair (R1, R2).
		end if;
		if Dimension(K) eq 1 then
			b := Basis(K)[1];	// If there is exactly one relation, we will check whether this relation has opposite signs on R11 and R22, as this would give a vector with non-unique decomposition.
			if {-1,1} subset {Sign(b[i]) : i in [1..#R11]} or {-1,1} subset {Sign(b[i]) : i in [#R11+1..#R11+#R22]} or not({-1,1} subset {Sign(b[i]) : i in [1..#R11+#R22]}) then
				continue;	// If there is no + on R11 and - on R22, or vice versa, then we are done with this pair (R1, R2).
			end if;
		end if;
		print R1, R2;	// If the above tests fial, we print R1 and R2 for further manual inspection. This turned out to never happen.
		print "";
	end for;
end for;
