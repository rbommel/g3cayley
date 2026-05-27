/***
 * Exported intrinsics.
 *
 * intrinsic CayleyOctadGeometry(VlOctad::SeqEnum) -> SetEnum
 *   {On input Plucker valuations, return colliding points, maximal lines and maximal planes
 *	 (taking care of point multiplicities, i.e. scheme-thoretically).}
 *
 ****************************************************************************/

import "bblocks.m" : KeySets;

// Collision
function AreCollidingPoints(SigTable, points : silent := false)

	if #points gt 2 then return &and{ $$(SigTable, S) : S in Subsets(points, 2) }; end if;

	sig2 := SigTable[3];

	/* 1 pair? */
	ret := sig2[points] gt 0;
	vprintf G3Cayley: silent or not ret select "" else "Point: Pts^2 -> " * Sprintf("%o", points) * "\n";

    return ret;
end function;


// Collinearity
function AreCollinearPoints(SigTable, points : silent := false)

	if #points gt 3 then return &and{ $$(SigTable, S) : S in Subsets(points, 3) }; end if;

	sig3 := SigTable[2]; sig2 := SigTable[3];

	Pairs := { pair : pair in Subsets(points, 2) | AreCollidingPoints(SigTable, pair : silent := true) };

	/* 3 distinct points? */
    if #Pairs eq 0 then
		ret := sig3[points] gt 0;
		vprintf G3Cayley: silent or not ret select "" else "Line: Pts^3 -> " * Sprintf("%o", points) * "\n";
		return ret;
	end if;

	/* 1 pair? */
	if #Pairs eq 1 then
		ret := sig3[points] gt sig2[Representative(Pairs)];
		vprintf G3Cayley: silent or not ret select "" else "Line: Pair + Pts -> " * Sprintf("%o", points) * "\n", Representative(Pairs), points diff Representative(Pairs);
		return ret;
	end if;

	/* So, 1 triple */
	assert #Pairs eq 3;

	ret := sig3[points] gt &+[ sig2[pair] : pair in Pairs ];
	vprintf G3Cayley: silent or not ret select "" else "Line: Triple -> " * Sprintf("%o", points) * "\n";
	return ret;

end function;

// Coplanarity
function AreCoplanarPoints(SigTable, points : silent := false)

	if #points gt 4 then return &and{ $$(SigTable, S) : S in Subsets(points, 4) }; end if;

	sig4 := SigTable[1]; sig3 := SigTable[2]; sig2 := SigTable[3];

	/* Collinear points */
	Lines := { triple : triple in Subsets(points, 3) | AreCollinearPoints(SigTable, triple) };

	/* 4 collinear points? */
	if #Lines eq 4 then
		vprintf G3Cayley: silent select "" else "Plane: Line -> " * Sprintf("%o", points) * "\n";
		return true;
	end if;

	/* 3 collinear points? */
	if #Lines gt 0 then
		vprintf G3Cayley: silent select "" else "Plane: Line + Pts -> " * Sprintf("%o + %o", Representative(Lines), points diff Representative(Lines)) * "\n";
		return true;
	end if;

	/* From now, the only possible degeneracies are colliding points */
	Pairs := { pair : pair in Subsets(points, 2) | AreCollidingPoints(SigTable, pair : silent := true) };

	/* 4 distinct points? */
    if #Pairs eq 0 then
		ret := sig4[points] gt 0;
		vprintf G3Cayley: silent or not ret select "" else "Plane: Pts^4 -> " * Sprintf("%o", points) * "\n";
		return ret;
	end if;

	/* One pair + 2 distinct points? */
    if #Pairs eq 1 then
		ret := sig4[points] gt sig2[Representative(Pairs)];
		vprintf G3Cayley: silent or not ret select "" else "Plane: Pair + Pts^2 -> " * Sprintf("%o + %o", Representative(Pairs), points diff Representative(Pairs)) * "\n";
		return ret;
	end if;

	/* Two distinct pairs? */
    if #Pairs eq 2 then
		ret := sig4[points] gt &+[ sig2[pair] : pair in Pairs ];
		vprintf G3Cayley: silent or not ret select "" else "Plane: Pair + Pair -> " * Sprintf("%o", Pairs) * "\n";
		return ret;
	end if;

	/* One triple + 1 point? */
    if #Pairs eq 3 then
		triple := &join Pairs; point := Representative(points diff triple);
		ret := sig4[points] gt sig3[triple];
		vprintf G3Cayley: silent or not ret select "" else "Plane: Triple + Pts -> " * Sprintf("%o + %o", triple, point) * "\n";
		return ret;
	end if;

	/* So, one quadruple point */
	assert #Pairs eq 6;

	// Order them in HNF form => pair subset triple subset points
	pair := Representative(Pairs);
	for S in Pairs do
		if sig2[S] gt sig2[pair] then pair := S; end if;
	end for;

	triple := Include(pair, Representative(points diff pair));
	for pt in points diff pair do
		if sig3[Include(pair, pt)] gt sig3[triple] then
			triple := Include(pair, pt);
		end if;
	end for;

	ret :=
		(sig3[triple] gt &+[sig2[S] : S in Subsets(triple, 2)])
		or
		(sig4[points] gt
		 (&+[sig3[Include(pair, pt)] : pt in points diff pair]
		 - sig2[pair] + sig2[points diff pair]));

	if ret eq false then
		/* Partial result here, we can not cover all the P3 reduction types */
		printf "Warning: Uncertainty in the non-coplanar reduction of the points %o\n", points;
	end if;

	vprintf G3Cayley: silent or not ret select "" else "Plane: Quadruple -> " * Sprintf("%o", points) * "\n";
	return ret;

end function;

/* Maximal closure */
function MaximalPointClosure(PointTuples)

	if #PointTuples lt 2 then return PointTuples; end if;

	d := #Representative(PointTuples);

	MaxPointTuplesCurrent := PointTuples;
	repeat
		MaxPointTuples := MaxPointTuplesCurrent; MaxPointTuplesCurrent := {};
		for T in Subsets(MaxPointTuples, 2) do
			if Subsets(&join T, d) subset PointTuples then
				Include(~MaxPointTuplesCurrent, &join T);
			else
				MaxPointTuplesCurrent join:= T;
			end if;
		end for;

		MPTC := {};
		for T in MaxPointTuplesCurrent do
			if { S : S in MaxPointTuplesCurrent | T subset S and T ne S } eq {} then
				Include(~MPTC, T);
			end if;
		end for;

		MaxPointTuplesCurrent := MPTC;

	until #MaxPointTuplesCurrent lt 2 or
		  MaxPointTuples eq MaxPointTuplesCurrent ;

	return MaxPointTuplesCurrent;

end function;

/* Precomputations */
function PluckerValuationMinima(VlOctad)

	AllPoints := {1..8};

	sig4 := AssociativeArray();
	for i->XYZW in KeySets do sig4[XYZW] := VlOctad[i]; end for;

	sig3 := AssociativeArray();
	for XYZ in Subsets(AllPoints, 3) do
		sig3[XYZ] := Min([ sig4[XYZW] : XYZW in Keys(sig4) | XYZ subset XYZW ]);
	end for;

	sig2 := AssociativeArray();
	for XY in Subsets(AllPoints, 2) do
		sig2[XY] := Min([ sig3[XYZ] : XYZ in Keys(sig3) | XY subset XYZ ]);
	end for;

	sig1 := AssociativeArray();
	for X in Subsets(AllPoints, 1) do
		sig1[X] := Min([ sig2[XY] : XY in Keys(sig2) | X subset XY ]);
	end for;

	return <sig4, sig3, sig2, sig1>;

end function;

intrinsic CayleyOctadGeometry(VlOctad::ModTupFldElt) -> SetEnum
    {On input Plucker valuations, return colliding points, maximal lines and maximal planes
	 (taking care of point multiplicities, i.e. scheme-thoretically).}

	assert Min(Eltseq(VlOctad)) eq 0;

	SigTable := PluckerValuationMinima(VlOctad);

	Points := {1..8};


	// Colliding pairs
	CollidingPairs := { pair :
						pair in Subsets(Points, 2) | AreCollidingPoints(SigTable, pair) };

	// Colliding closure
	CollidingPoints := MaximalPointClosure(CollidingPairs);


	// Collinear triples
	CollinearTriples := { triple :
						 triple in Subsets(Points, 3) | AreCollinearPoints(SigTable, triple) };

	// Collinear closure
	CollinearPoints := MaximalPointClosure(CollinearTriples);


	// Coplanar quadruples
	CoplanarQuadruples := { quadruple :
						    quadruple in Subsets(Points, 4) | AreCoplanarPoints(SigTable, quadruple) };

	// Coplanar closure
	CoplanarPoints := MaximalPointClosure(CoplanarQuadruples);

	return
		CollidingPoints, CollinearPoints, CoplanarPoints;

end intrinsic;
