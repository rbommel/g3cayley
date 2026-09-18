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

function MainComponentOctads(Octad : Diagram := 0, Multiplicities := 0)
// Find one or two Cayley octads that should exhibit the main component of a stable model.
	if Type(Diagram) eq RngIntElt or Type(Multiplicities) eq RngIntElt then
		Diagram, Multiplicities := CayleyOctadDiagram(Octad);
	end if;
	assert {x[1] : x in Diagram} subset {"Pl", "TA", "CA", "Ln"}; // Input octad needs to be processed with GoodCremonaTransform first.
	TargetValuationData := Vector([ Rationals() | 0 : i in [1..70]]);
	for i->B in Diagram do
		case B[1]:
		when "Pl":
			TargetValuationData +:= Multiplicities[i] * CayleyOctadBlock("alpha2a", Random(B[2]));
		when "TA":
			TargetValuationData +:= Multiplicities[i] * CayleyOctadBlock("chi1b", <S : S in B[2,2]>);
		when "CA":
			assert(false); // Phi case still to be implemented. Requires special care.
		when "Ln":
			assert(false); // Line case still to be implemented. Requires special care.
		else:
			assert(false);
		end case;
	end for;
	OutputOctad := OctadWithValuationData(Octad, TargetValuationData);
	return OutputOctad, Diagram, Multiplicities;
end function;
