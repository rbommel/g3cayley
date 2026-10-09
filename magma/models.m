// Code to produce models of the plane quartic curve
// In development, not included in package yet

procedure AddToAllEntries(~L, x)
	// This function adds the same element x to all entries of a list L.
	for i in [1..#L] do
		L[i] +:= x;
	end for;
end procedure;

function ABCFromOctad(Octad)
	// This function computes the matrices A, B and C of a determinantal model corresponding to a Cayley octad.
	AR := Universe(Octad[1]);
	P<a,b,c,d> := PolynomialRing(AR, 4);
	P2 := [a^2, a*b, a*c, a*d, b^2, b*c, b*d, c^2, c*d, d^2];
	M := Matrix([ [Evaluate(Mon, Pt) : Pt in Octad ] : Mon in P2]);
	K := Kernel(M);
	ABC := [ ChangeRing(Matrix([
		[ v[1], v[2]/2, v[3]/2, v[4]/2 ],
		[ v[2]/2, v[5], v[6]/2, v[7]/2 ],
		[ v[3]/2, v[6]/2, v[8], v[9]/2 ],
		[ v[4]/2, v[7]/2, v[9]/2, v[10] ]
	]), AR) : v in Basis(K)];
	return ABC;
end function;

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
	TargetValuationData := [Vector([ Rationals() | 0 : i in [1..70]])];
	for i->B in Diagram do
		case B[1]:
		when "Pl":
			AddToAllEntries(~TargetValuationData, Multiplicities[i] * CayleyOctadBlock("alpha2a", Random(B[2])));
		when "TA":
			AddToAllEntries(~TargetValuationData, Multiplicities[i] * CayleyOctadBlock("chi1b", <S : S in B[2,2]>));
		when "CA":
			assert(false); // Phi case still to be implemented. Requires special care.
		when "Ln":
			assert(false); // Line case still to be implemented. Requires special care.
		else:
			assert(false);
		end case;
	end for;
	OutputOctads := [OctadWithValuationData(Octad, v) : v in TargetValuationData];
	return OutputOctads, Diagram, Multiplicities;
end function;

function NormalisedDeterminantalModel(ONrm : ABC := 0)
	if Type(ABC) eq RngIntElt then
		ABC := ABCFromOctad(ONrm);
	end if;
	QF := Universe(ONrm[1]);
	c := UniformizingElement(QF)^(-Min([ Valuation(x) : x in &cat[Eltseq(M) : M in ABC]]));
	ABCNrm := [c*M : M in ABC];
	RF<r,s,t> := PolynomialRing(QF, 3);
	Fp,phi := ResidueClassField(RingOfIntegers(QF));

	//{ (Matrix(ONrm[i..i]) * ABCNrm[j] * Transpose(Matrix(ONrm[i..i])))[1,1] : i in [1..8], j in [1..3] };

	MatLat := Matrix([[RingOfIntegers(QF) | e : e in Eltseq(M)] : M in ABCNrm]);
	ABCrst := &+ [ [r, s, t][i] * ChangeRing(ABCNrm[i], RF) : i in [1..3] ];

	SF, SP, SQ := SmithForm(MatLat);

	Sandreas := ChangeRing(Submatrix(SF, 1, 1, 3, 3), QF)^-1 * SP;
	SNFMatLat := Sandreas * ChangeRing(MatLat, QF);
	SNFABC := [ Matrix(4, 4, [ e  : e in Eltseq(SNFMatLat[i]) ]) : i in [1..3] ];

	SNFABCrst := &+ [ [r, s, t][i] * ChangeRing(SNFABC[i], RF) : i in [1..3] ];
	Fdet := Determinant(SNFABCrst);
	Sandreas /:= Gcd([RingOfIntegers(QF)!e: e in Coefficients(Fdet)]) / c;
	Fdet /:= Gcd([RingOfIntegers(QF)!e: e in Coefficients(Fdet)]);
	return Fdet, SNFABC, Sandreas;
end function;