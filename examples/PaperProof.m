/* Computational proofs of some results of [Bom+23].

  [Bom+23] R. van Bommel, J. Docking, V. Dokchitser, R. Lercier and E. Lorenzo García, Reduction of plane quartics and Cayley octads, arXiv:xxx.
*/

"";

/* Toolbox */
function AdHocVal(pol, P)

    if pol eq 0 then return Infinity(), 0; end if;

    p := Numerator(P);

    nc := Coefficients(Numerator(pol), p);
    dc := Coefficients(Denominator(pol), p);

    nidx := Min([ i: i in [1..#nc] | nc[i] ne 0]);
    didx := Min([ i: i in [1..#dc] | dc[i] ne 0]);

    return nidx - didx, nc[nidx]/dc[didx];

end function;

function AdHocNormalize(Octad, P)
    Oct := [];
    for Pt in Octad do
        v := Min([ AdHocVal(e, P) : e in Pt ]);
        Append(~Oct, [ P^(-v)*e : e in Pt ]);
    end for;
    return Oct;
end function;

/*
 * Theorem 4.4 - Cremona action on alpha blocks
 ************************************************/

/* Ring definitions  */
Fld := Rationals();

Poctad<
    a0, a1, a2, a3,
    b0, b1, b2, b3,
    c0, c1, c2, c3,
    p > := PolynomialRing(Fld, [ 1 : i in [1..3*4+1] ]);

Foctad<
    A0, A1, A2, A3,
    B0, B1, B2, B3,
    C0, C1, C2, C3,
    P > := FieldOfFractions(Poctad);


/*** Alpha_{1a} case ***/
/***********************/

"Cremona action on Alpha_{1a}";

/* The octad */
O := [
    [ a0,      a1,      a2,      a3 ],
    [ a0+p*b0, a1+p*b1, a2+p*b2, a3+p*b3 ],
    [ c0,      c1,      c2,      c3 ],
    [ 1, 1, 1, 1 ],
    [ 1, 0, 0, 0 ],
    [ 0, 1, 0, 0 ],
    [ 0, 0, 1, 0 ],
    [ 0, 0, 0, 1 ]
    ];
O := AdHocNormalize(O, P);


/* It's valuation data */
PlckO, KeySets := PluckerCoordinates(O);
VPlO := Vector([ AdHocVal(e, P) : e in PlckO ]);
"\t_ Valuation data of O  equal to Alpha^AB_1a:",
    VPlO eq Vector([ Max(0, #(K meet {1,2}) - 1) : K in KeySets ]);

/* Relations among the coefficients, mod p */
OctadRels := Setseq({ Coefficient(Numerator(e),p,0) : e in CayleyOctadRelations(PlckO) });
OctadRels := GroebnerBasis(OctadRels);

/* It's Cremona image */
Oc := [
    [ 1/e : e in O[1] ],
    [ 1/e : e in O[2] ],
    [ 1/e : e in O[3] ],
    [ 1, 1, 1, 1 ],
    [ 1, 0, 0, 0 ],
    [ 0, 1, 0, 0 ],
    [ 0, 0, 1, 0 ],
    [ 0, 0, 0, 1 ]
    ];
Oc := AdHocNormalize(Oc, P);

/* It's valuation data */
PlckOc, KeySets := PluckerCoordinates(Oc);
VPlOc := Vector([ AdHocVal(e, P) : e in PlckOc ]);
"\t_ Valuation data of O' equal to Alpha^AB_1a:",
    VPlOc eq Vector([ Max(0, #(K meet {1,2}) - 1) : K in KeySets ]);

/* Relations that make O degenerate */
ODegenerate :=
    &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Coefficient(Numerator(PlckO[i]),p,0)]>)} : i in [1..70] | PlckO[i] ne 0 }
    join
    &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Coefficient(Denominator(PlckO[i]),p,0)]>)} : i in [1..70] | PlckO[i] ne 0 };

/* Make the Cayley octad relation enter in the game */
ODegenerate := &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|sys cat OctadRels>)} : sys in ODegenerate };

/* Relations that make Oc degenerate */
OcDegenerate :=
    &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Coefficient(Numerator(PlckOc[i]),p,0)]>)} : i in [1..70] | PlckOc[i] ne 0 }
    join
    &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Coefficient(Denominator(PlckOc[i]),p,0)]>)} : i in [1..70] | PlckO[i] ne 0 };

/* Make the Cayley octad relation enter in the game too */
OcDegenerate := &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|sys cat OctadRels>)} : sys in OcDegenerate };

/* When PclkOc degenerate while Plck does not ? */
BadCases := OcDegenerate diff ODegenerate;
"\t_ Degeneracy case(s):", BadCases;

/* Does it correspond to hyperelliptic  degeneracy, as expected ? */
TwCubO  := {* e : e in CayleyOctadTwistedCubicRelations(PlckO) *};

"\t_ Do they correspond to hyperelliptic reduction:",
    [ { NormalForm(Coefficient(Numerator(e), p, 0), sys) : e in TwCubO } eq {0} : sys in BadCases ];
