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
function AreCollidingPoints(ValPrc, points : silent := false)

	if #points gt 2 then return &and{ $$(ValPrc, S) : S in Subsets(points, 2) }; end if;

	vm2 := ValPrc[3];

	/* 1 pair? */
	ret := vm2[points] gt 0;
	vprintf G3Cayley: silent or not ret select "" else "Point: Pts^2 -> " * Sprintf("%o", points) * "\n";

    return ret;
end function;


// Collinearity
function AreCollinearPoints(ValPrc, points : silent := false)

	if #points gt 3 then return &and{ $$(ValPrc, S) : S in Subsets(points, 3) }; end if;

	vm3 := ValPrc[2]; vm2 := ValPrc[3];

	Pairs := { pair : pair in Subsets(points, 2) | AreCollidingPoints(ValPrc, pair : silent := true) };

	/* 3 distinct points? */
    if #Pairs eq 0 then
		ret := vm3[points] gt 0;
		vprintf G3Cayley: silent or not ret select "" else "Line: Pts^3 -> " * Sprintf("%o", points) * "\n";
		return ret;
	end if;

	/* 1 pair? */
	if #Pairs eq 1 then
		ret := vm3[points] gt vm2[Representative(Pairs)];
		vprintf G3Cayley: silent or not ret select "" else "Line: Pair + Pts -> " * Sprintf("%o", points) * "\n", Representative(Pairs), points diff Representative(Pairs);
		return ret;
	end if;

	/* So, 1 triple */
	assert #Pairs eq 3;

	basepoint := Representative(points); otherpoints := points diff {basepoint};
	ret := vm3[points] gt &+[vm2[{basepoint, pt}] : pt in otherpoints];
	vprintf G3Cayley: silent or not ret select "" else "Line: Triple -> " * Sprintf("%o", points) * "\n";
	return ret;

end function;

// Coplanarity
function AreCoplanarPoints(ValPrc, points : silent := false)

	if #points gt 4 then return &and{ $$(ValPrc, S) : S in Subsets(points, 4) }; end if;

	vm4 := ValPrc[1]; vm3 := ValPrc[2]; vm2 := ValPrc[3];

	/* Collinear points */
	Lines := { triple : triple in Subsets(points, 3) | AreCollinearPoints(ValPrc, triple) };

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
	Pairs := { pair : pair in Subsets(points, 2) | AreCollidingPoints(ValPrc, pair : silent := true) };

	/* 4 distinct points? */
    if #Pairs eq 0 then
		ret := vm4[points] gt 0;
		vprintf G3Cayley: silent or not ret select "" else "Plane: Pts^4 -> " * Sprintf("%o", points) * "\n";
		return ret;
	end if;

	/* One pair + 2 distinct points? */
    if #Pairs eq 1 then
		ret := vm4[points] gt vm2[Representative(Pairs)];
		vprintf G3Cayley: silent or not ret select "" else "Plane: Pair + Pts^2 -> " * Sprintf("%o + %o", Representative(Pairs), points diff Representative(Pairs)) * "\n";
		return ret;
	end if;

	/* Two distinct pairs? */
    if #Pairs eq 2 then
		ret := vm4[&join Pairs] gt &+[ vm2[pair] : pair in Pairs ];
		vprintf G3Cayley: silent or not ret select "" else "Plane: Pair + Pair -> " * Sprintf("%o", Pairs) * "\n";
		return ret;
	end if;

	/* One triple + 1 point? */
    if #Pairs eq 3 then
		triple := &join Pairs; point := points diff triple;
		basepoint := Representative(&join Pairs); otherpoints := (&join Pairs) diff { basepoint };
		ret := vm4[points] gt &+[ vm2[{pt, basepoint}] : pt in otherpoints];
		vprintf G3Cayley: silent or not ret select "" else "Plane: Triple + Pts -> " * Sprintf("%o + %o", &join Pairs, point) * "\n";
		return ret;
	end if;

	/* So, one quadruple point */
	assert #Pairs eq 6;

	basepoint := Representative(points); otherpoints := points diff { basepoint };

	ret := vm4[points] gt &+[ vm2[{basepoint, pt}] : pt in otherpoints];
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

	vm4 := AssociativeArray();
	for i->XYZW in KeySets do vm4[XYZW] := VlOctad[i]; end for;

	vm3 := AssociativeArray();
	for XYZ in Subsets(AllPoints, 3) do
		vm3[XYZ] := Min([ vm4[XYZW] : XYZW in Keys(vm4) | XYZ subset XYZW ]);
	end for;

	vm2 := AssociativeArray();
	for XY in Subsets(AllPoints, 2) do
		vm2[XY] := Min([ vm3[XYZ] : XYZ in Keys(vm3) | XY subset XYZ ]);
	end for;

/*
	vm1 := AssociativeArray();
	for X in Subsets(AllPoints, 1) do
		vm1[X] := Min([ vm2[XY] : XY in Keys(vm2) | X subset XY ]);
	end for;
*/

	return <vm4, vm3, vm2 /*, vm1 */>;

end function;

intrinsic CayleyOctadGeometry(VlOctad::ModTupFldElt) -> SetEnum
    {On input Plucker valuations, return colliding points, maximal lines and maximal planes
	 (taking care of point multiplicities, i.e. scheme-thoretically).}

	assert Min(Eltseq(VlOctad)) eq 0;

	ValPrc := PluckerValuationMinima(VlOctad);

	Points := {1..8};


	// Colliding pairs
	CollidingPairs := { pair :
						pair in Subsets(Points, 2) | AreCollidingPoints(ValPrc, pair) };

	// Colliding closure
	CollidingPoints := MaximalPointClosure(CollidingPairs);


	// Collinear triples
	CollinearTriples := { triple :
						 triple in Subsets(Points, 3) | AreCollinearPoints(ValPrc, triple) };

	// Collinear closure
	CollinearPoints := MaximalPointClosure(CollinearTriples);


	// Coplanar quadruples
	CoplanarQuadruples := { quadruple :
						    quadruple in Subsets(Points, 4) | AreCoplanarPoints(ValPrc, quadruple) };

	// Coplanar closure
	CoplanarPoints := MaximalPointClosure(CoplanarQuadruples);

	return
		CollidingPoints, CollinearPoints, CoplanarPoints;

end intrinsic;
