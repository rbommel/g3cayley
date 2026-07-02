// Code to produce models of the plane quartic curve
// In development, not included in package yet

function GoodCremonaTransform(Octad : Diagram := 0)
// Find an octad with only blocks that are good for making models.
	if Type(Diagram) eq RngIntElt then
		Diagram := CayleyOctadDiagram(Octad);
	end if;
	if {x[1] : x in Diagram} subset {"Pl", "TA", "CA", "Ln"} then
		return Octad, Diagram;
	end if;
	for S in Subsets({1..7}, 4) do
		DiagramS := CremonaAction(Diagram, S);
		if {x[1] : x in DiagramS} subset {"Pl", "TA", "CA", "Ln"} then
			OctadS := CremonaAction(Octad, S);
			return OctadS, DiagramS;
		end if;
	end for;
	assert false;	// nothing found, this should not happen
end function;
