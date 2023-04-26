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

/*** Alpha_{1a} case ***/
/***********************/

/* ABCD|EFGH
 ***/
"Cremona action ABCD|EFGH on Alpha_{1a}";

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
PlckOc := [
    NormalForm(Numerator(e), OctadRels) / NormalForm(Denominator(e), OctadRels)
    : e in PlckOc
    ];
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

"";

/*
    [
        a0*a2*c0*c1 - a1*a2*c0*c1 - a0*a1*c0*c2 + a1*a2*c0*c2 + a0*a1*c1*c2 - a0*a2*c1*c2,
        a0*a3*c0*c1 - a1*a3*c0*c1 - a0*a1*c0*c3 + a1*a3*c0*c3 + a0*a1*c1*c3 - a0*a3*c1*c3,
        a0*a3*c0*c2 - a2*a3*c0*c2 - a0*a2*c0*c3 + a2*a3*c0*c3 + a0*a2*c2*c3 - a0*a3*c2*c3,
        a1*a3*c1*c2 - a2*a3*c1*c2 - a1*a2*c1*c3 + a2*a3*c1*c3 + a1*a2*c2*c3 - a1*a3*c2*c3
    ]
*/


/* ACDE|BFGH
 ***/

/* Ring definitions  */
Fld := Rationals();

Poctad<
    b0, b1, b2, b3,
    g0, g1, g2, g3,
    h0, h1, h2, h3,
    p > := PolynomialRing(Fld, [ 1 : i in [1..3*4+1] ]);

Foctad<
    B0, B1, B2, B3,
    G0, G1, G2, G3,
    H0, H1, H2, H3,
    P > := FieldOfFractions(Poctad);

 "Cremona action ACDE|BFGH on Alpha_{1a}";

/* The octad */
O := [
    [ 1, 0, 0, 0 ],
    [ 1+p*b0, 0+p*b1, 0+p*b2, 0+p*b3 ],
    [ 0, 1, 0, 0 ],
    [ 0, 0, 1, 0 ],
    [ 0, 0, 0, 1 ],
    [ 1, 1, 1, 1 ],
    [ g0,     g1,      g2,    g3 ],
    [ h0,     h1,      h2,    h3 ]
    ];
O := AdHocNormalize(O, P);

/* It's valuation data */
PlckO, KeySets := PluckerCoordinates(O);
VPlO := Vector([ AdHocVal(e, P) : e in PlckO ]);
"\t_ Valuation data of O  equal to Alpha^AB_1a:",
    VPlO eq Vector([ Max(0, #(K meet {1,2}) - 1) : K in KeySets ]);

/* Relations among the coefficients, mod p */
ORels := Setseq({ Coefficient(Numerator(e),p,0) : e in CayleyOctadRelations(PlckO) });
ORels := GroebnerBasis(ORels);

/* It's Cremona image */
Oc := [
    [ 1, 0, 0, 0 ],
    [ 1/e : e in O[2] ],
    [ 0, 1, 0, 0 ],
    [ 0, 0, 1, 0 ],
    [ 0, 0, 0, 1 ],
    [ 1, 1, 1, 1 ],
    [ 1/e : e in O[7] ],
    [ 1/e : e in O[8] ]
    ];
Oc := AdHocNormalize(Oc, P);

/* It's valuation data */
PlckOc, KeySets := PluckerCoordinates(Oc);
PlckOc := [
    NormalForm(Numerator(e), ORels) / NormalForm(Denominator(e), ORels)
    : e in PlckOc
    ];
VPlOc := Vector([ AdHocVal(e, P) eq Infinity() select 1 else  AdHocVal(e, P) : e in PlckOc ]);
"\t_ Valuation data of O' equal to Alpha^BCDE_2a:",
    VPlOc eq Vector([ Max(0, #(K meet {2,3,4,5}) - 3) + Max(0, #(K meet {1,6,7,8}) - 3) : K in KeySets ]);

/* Relations among the coefficients, mod p */
OcRels := Setseq({ Coefficient(Numerator(e),p,0) : e in CayleyOctadRelations(PlckOc) });
OcRels := GroebnerBasis(OcRels);

/* Relations that make O degenerate */
OEquations := [];
for i := 1 to #KeySets do
    v, e := AdHocVal(PlckO[i], P);
    Append(~OEquations, v eq Infinity() select 1 else e);
end for;

ODegenerate :=
    &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Numerator(OEquations[i])]>)} : i in [1..70] | PlckO[i] ne 0 }
    join
    &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Denominator(OEquations[i])]>)} : i in [1..70] | PlckO[i] ne 0 };

/* Make the Cayley octad relation enter in the game */
ODegenerate := &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|sys cat ORels cat OcRels>)} : sys in ODegenerate };

/* Relations that make Oc degenerate */
OcEquations := [];
for i := 1 to #KeySets do
    v, e := AdHocVal(PlckOc[i], P);
    i, v, e;
    Append(~OcEquations, v eq Infinity() select Foctad!1 else e);
end for;

OcDegenerate :=
    &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Numerator(OcEquations[i])]>)} : i in [1..70] | PlckOc[i] ne 0 }
    join
    &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Denominator(OcEquations[i])]>)} : i in [1..70] | PlckOc[i] ne 0 };

/* Make the Cayley octad relation enter in the game too */
OcDegenerate := &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|sys cat ORels cat OcRels>)} : sys in OcDegenerate };

/* When PclkOc degenerate while Plck does not ? */
BadCases := Setseq(OcDegenerate diff ODegenerate);
"\t_ Degeneracy case(s):", BadCases;

/* Does it correspond to hyperelliptic  degeneracy, as expected ? */
TwCubO  := {* e : e in CayleyOctadTwistedCubicRelations(PlckO) *};

"\t_ Do they correspond to hyperelliptic reduction:",
    [ { NormalForm(Coefficient(Numerator(e), p, 0), sys) : e in TwCubO } eq {0} : sys in BadCases ];

/*
    [
        b1*g1*g3*h0*h2 - b1*g2*g3*h0*h2 - b1*g1*g2*h0*h3 + b2*g1*g2*h0*h3 - b2*g1*g3*h0*h3 + b1*g2*g3*h0*h3 + b1*g1*g2*h2*h3 - b2*g1*g2*h2*h3 - b1*g1*g3*h2*h3 + b2*g1*g3*h2*h3,
        b1*g0*g3*h1*h2 - b2*g0*g3*h1*h2 - b1*g2*g3*h1*h2 + b2*g2*g3*h1*h2 - b1*g0*g2*h1*h3 + b2*g0*g3*h1*h3 + b1*g2*g3*h1*h3 - b2*g2*g3*h1*h3 + b1*g0*g2*h2*h3 - b1*g0*g3*h2*h3,
        b1*b3*g1*g2 - b2*b3*g1*g2 - b1*b2*g1*g3 + b2*b3*g1*g3 + b1*b2*g2*g3 - b1*b3*g2*g3,

        g0*g2*h0*h1 - g1*g2*h0*h1 - g0*g1*h0*h2 + g1*g2*h0*h2 + g0*g1*h1*h2 - g0*g2*h1*h2,
        g0*g3*h0*h1 - g1*g3*h0*h1 - g0*g1*h0*h3 + g1*g3*h0*h3 + g0*g1*h1*h3 - g0*g3*h1*h3,
        g0*g3*h0*h2 - g2*g3*h0*h2 - g0*g2*h0*h3 + g2*g3*h0*h3 + g0*g2*h2*h3 - g0*g3*h2*h3,
        b1*b3*h1*h2 - b2*b3*h1*h2 - b1*b2*h1*h3 + b2*b3*h1*h3 + b1*b2*h2*h3 - b1*b3*h2*h3,
        g1*g3*h1*h2 - g2*g3*h1*h2 - g1*g2*h1*h3 + g2*g3*h1*h3 + g1*g2*h2*h3 - g1*g3*h2*h3,

        b2*g0*g1 - b1*g0*g2 + b1*g1*g2 - b2*g1*g2,
        b3*g0*g1 - b1*g0*g3 + b1*g1*g3 - b3*g1*g3,
        b3*g0*g2 - b2*g0*g3 + b2*g2*g3 - b3*g2*g3,
        b2*h0*h1 - b1*h0*h2 + b1*h1*h2 - b2*h1*h2,
        b3*h0*h1 - b1*h0*h3 + b1*h1*h3 - b3*h1*h3,
        b3*h0*h2 - b2*h0*h3 + b2*h2*h3 - b3*h2*h3
    ]
*/
