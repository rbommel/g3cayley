/* Computational proofs of some results of [Bom+23].

  [Bom+23] R. van Bommel, J. Docking, V. Dokchitser, R. Lercier and E. Lorenzo García, Reduction of plane quartics and Cayley octads, arXiv:xxx.

   This script assumes that the spec file "g3cayley/magma/spec" is loaded
   at magma startup (in the .magmarc file)
*/

/* Checking flags, set the one you want to true.
   By default, they are all set to true.
 */
ByDefault := true;

RegularCase     := false;

Alpha1av1Case   := false; Alpha1av2Case   := false;
Alpha2bv1Case   := false; Alpha2bv2Case   := false;

Chi1av1Case   := false; Chi1av2Case   := false; Chi1av3Case   := false;
Chi2av1Case   := false; Chi2av2Case   := false;

Phi1av1Case := false; Phi1av2Case := false; Phi1av3Case := false; Phi1av4Case := false; Phi1av5Case := false;
Phi2av1Case := false; Phi2av2Case := false; Phi2av3Case := false;
Phi3av1Case := false;

if ByDefault then

    RegularCase     := true;

    Alpha1av1Case   := true; Alpha1av2Case   := true;
    Alpha2bv1Case   := true; Alpha2bv2Case   := true;

    Chi1av1Case   := true; Chi1av2Case   := true; Chi1av3Case   := true;
    Chi2av1Case   := true; Chi2av2Case   := true;

    Phi1av1Case := true; Phi1av2Case := true; Phi1av3Case := true; Phi1av4Case := true; Phi1av5Case := true;
    Phi2av1Case := true; Phi2av2Case := true; Phi2av3Case := true;
    Phi3av1Case := true;

end if;

"";

/* Toolbox
 *********/
_, KeySets := PluckerCoordinates([ [0,0,0,0] : i in [1..8] ]);

function vPt(S : KS := KeySets)
    return Vector([ Max(0, #(K meet S) - 1) : K in KS]);
end function;

function vLn(S : KS := KeySets)
    return Vector([ Max(0, #(K meet S) - 2) : K in KS]);
end function;

function vPl(S : KS := KeySets)
    return Vector([ Max(0, #(K meet S) - 3) : K in KS]);
end function;

function vmax(v1, v2)
    w := v1;
    for i := 1 to #Eltseq(v1) do w[i] := Max(v1[i], v2[i]); end for;
    return w;
end function;

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


function CremonaImage(_O, ijklm)

    OL := [_O[i] : i in ijklm];
    M5 := Matrix(OL);
    K5 := KernelMatrix(M5); assert(Nrows(K5) eq 1);
    N := Matrix(4, 4, [ OL[i,j] * K5[1,i] : i,j in [1..4] ]);
    O2 := Matrix(_O) * N^(-1);

    ijk := Setseq({1..8} diff Seqset(ijklm));

    for i in ijk do
        for l := 1 to 4 do O2[i,l] := 1/O2[i,l]; end for;
    end for;

    return [ Eltseq(O2[i]) : i in [1..8] ];

end function;

procedure ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc)

    Foctad := Universe(_O[1]); P := Foctad.Rank(Foctad);
    Poctad := RingOfIntegers(Foctad); p := Numerator(P);

    /* The first octad */
    O := AdHocNormalize(_O, P);

    /* It's valuation data */
    PlckO, KeySets := PluckerCoordinates(O);

    VPlO := Vector([ AdHocVal(e, P) eq Infinity() select 1000 else AdHocVal(e, P): e in PlckO ]);
    "\t_ Valuation data of O  equal to a " cat tpO cat "-block:", VPlO eq vO;
    assert VPlO eq vO;

    /* It's Cremona image */
    Oc := AdHocNormalize(_Oc, P);

    /* It's valuation data */
    PlckOc, KeySets := PluckerCoordinates(Oc);

    VPlOc := Vector([ AdHocVal(e, P) eq Infinity() select 1000 else AdHocVal(e, P): e in PlckOc ]);
    "\t_ Valuation data of O' equal to a " cat tpOc cat "-block:", VPlOc eq vOc;
    assert VPlOc eq vOc;

    /* Relations that would lead to higher valuation data for O */
    OEquations := [];
    for i := 1 to #KeySets do
        v, e := AdHocVal(PlckO[i], P);
        Append(~OEquations, v eq Infinity() select Foctad!1 else Foctad!e);
    end for;

    ODegenerate :=
        &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Numerator(OEquations[i])]>)} : i in [1..70] | PlckO[i] ne 0 }
        join
        &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Denominator(OEquations[i])]>)} : i in [1..70] | PlckO[i] ne 0 };

    /* Relations that would lead to higher valuation data for Oc */
    OcEquations := [];
    for i := 1 to #KeySets do
        v, e := AdHocVal(PlckOc[i], P);
        Append(~OcEquations, v eq Infinity() select Foctad!1 else Foctad!e);
    end for;

    OcDegenerate :=
        &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Numerator(OcEquations[i])]>)} : i in [1..70] | PlckOc[i] ne 0 }
        join
        &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Denominator(OcEquations[i])]>)} : i in [1..70] | PlckOc[i] ne 0 };

    /* Can we have higher valuations for Oc, but not for O ? */
    BadCases := Sort(Setseq(OcDegenerate diff ODegenerate));

    "\t_ Number of bad cases to examine:", #BadCases;
    assert #BadCases eq 0;

    "\t=> Everything's fine!";
    "";

end procedure;

/* Ring definitions  */
Fld := Rationals();

Poctad<
    a0, a1, a2, a3,
    b0, b1, b2, b3,
    p > := PolynomialRing(Fld, [ 1 : i in [1..2*4+1] ]);
Foctad<
    A0, A1, A2, A3,
    B0, B1, B2, B3,
    P > := FieldOfFractions(Poctad);

/*
 * Generic check - Cremona action on a regular octad
 ***************************************************/

if RegularCase then

    "Cremona action ABCD | EFGH on a regular octad";

    /* The octad */
    tpO := "regular";
    vO  := Vector([ 0 : K in KeySets ]);
    O6 := [ 1, a1, a2, a3 ]; O7 := [ b0, b1, b2, b3 ]; O8 := CayleyOctadEighthPoint(O6, O7);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ],
        [ 1, 1, 1, 1 ],
        O6,
        O7,
        O8
        ];

    /* It's Cremona image */
    tpOc := "regular";
    vOc  := Vector([ 0 : K in KeySets ]);
    _Oc := CremonaImage(_O, [ 1,2,3,4, 5]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

    "++++++++++++++++++++++";
    "";

end if;

/*
 * Section 4.1 - Cremona action on alpha blocks
 **********************************************/

/*** Alpha_{1} case ***/
/**********************/

if Alpha1av1Case then

    "Cremona action ABCD | EFGH on Alpha^AB_{1a}";

    /* The octad */
    tpO := "Alpha^AB_1a";
    vO  := vPt({1,2});
    O1 := [ 1, a1, a2, a3 ];
    O2 := [ 1, a1+p*b1, a2+p*b2, a3+p*b3 ];
    O3 := CayleyOctadEighthPoint(O1, O2);
    _O := Parent([[Foctad|]])![
        O1,
        O2,
        O3,
        [ 1, 1, 1, 1 ],
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ]
        ];

    /* It's Cremona image */
    tpOc := "Alpha^AB_1a";
    vOc  := vPt({1,2});
    _Oc := CremonaImage(_O, [ 5,6,7,8, 4 ]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

if Alpha1av2Case then

    "Cremona action ACDE | BFGH on Alpha^AB_{1a}";

    /* The octad */
    tpO := "Alpha^AB_1a";
    vO  := vPt({1,2});
    O2 := [ 1, p*a1, p*a2, p*a3 ];
    O7 := [ 1, b1, b2, b3 ];
    O8 := CayleyOctadEighthPoint(O2, O7);
    _O := Parent([[Foctad|]])![
        [ 1, 0,  0,  0 ],
        O2,
        [ 0, 1,  0,  0 ],
        [ 0, 0,  1,  0 ],
        [ 0, 0,  0,  1 ],
        [ 1, 1,  1,  1 ],
        O7,
        O8
        ];

    /* It's Cremona image */
    tpOc := "Alpha^BCDE_2a";
    vOc  := vPl({2,3,4,5}) + vPl({1,6,7,8});
    _Oc := CremonaImage(_O, [ 1,3,4,5, 6]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

    "--------";
    "";

end if;

/*** Alpha_{2} case ***/
/***********************/

if Alpha2bv1Case then

    "Cremona action ABCD | EFGH on Alpha^ABCD_{2b}";

    /* The octad */
    tpO := "Alpha^ABCD_2b";
    vO  := vPt({1,2,3,4}) + vPl({1,2,3,4});
    O1 := [ 1, a1*p+1, a2*p+1, a3*p+1 ];
    O2 := [ 1, b1*p+1, b2*p+1, b3*p+1 ];
    O3 := CayleyOctadEighthPoint(O1, O2);
    _O := Parent([[Foctad|]])![
        O1,
        O2,
        O3,
        [ 1, 1, 1, 1 ],
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ]
        ];

    /* It's Cremona image */
    tpOc := "Alpha^ABCD_2b";
    vOc  := vPt({1,2,3,4}) + vPl({1,2,3,4});
    _Oc := CremonaImage(_O, [ 5,6,7,8, 4 ]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

if Alpha2bv2Case then

    "Cremona action ABEF | CDGH on Alpha^ABCD_{2b}";

    /* The octad */
    tpO := "Alpha^ABCD_2b";
    vO  := vPt({1,2,3,4}) + vPl({1,2,3,4});
    O1 := [ 1, a1*p+1, a2*p+1, a3*p+1 ];
    O2 := [ 1, b1*p+1, b2*p+1, b3*p+1 ];
    O3 := CayleyOctadEighthPoint(O1, O2);
    _O := Parent([[Foctad|]])![
        O1,
        O2,
        O3,
        [ 1, 1, 1, 1 ],
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ]
        ];

    /* It's Cremona image */
    tpOc := "Alpha^ABCD_2a";
    vOc  := vPl({1,2,3,4}) +  vPl({5,6,7,8});
    _Oc := CremonaImage(_O, [ 1,2,5,6, 4 ]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

    "++++++++++++++++++++++";
    "";

end if;

/*
 * Section 4.2 - Cremona action on chi blocks
 ********************************************/

/*** Chi_{1} case ***/
/********************/

if Chi1av1Case then

    "Cremona action ABCH | DEFG on Chi^AB|CDE|FGH_1a";

    /* The octad */
    tpO := "Chi^AB|CDE|FGH_1a";
    vO  := vmax( vLn({3,4,5}) + vLn({6,7,8}), vPl({3,4,5,6,7,8}) );
    O3 := [ 1, 1+p*a1, a2, a3 ];
    O4 := [ 1, 1+p*b1, b2, a3+p*b3];
    O8 := CayleyOctadEighthPoint(O3, O4);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        O3,
        O4,
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ],
        [ 1, 1, 1, 1 ],
        O8
        ];

    /* It's Cremona image */
    tpOc := "Chi^AB|CDE|FGH_1a";
    vOc  := vmax( vLn({3,4,5}) + vLn({6,7,8}), vPl({3,4,5,6,7,8}) );
    _Oc := CremonaImage(_O, [ 1,2,3,8, 7]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

if Chi1av2Case then

    "Cremona action BCDE | AFGH on Chi^AB|CDE|FGH_1a";

    /* The octad */
    tpO := "Chi^AB|CDE|FGH_1a";
    vO  := vmax( vLn({3,4,5}) + vLn({6,7,8}), vPl({3,4,5,6,7,8}) );
    O3 := [ 1, 1+p*a1, a2, a3 ];
    O4 := [ 1, 1+p*b1, b2, a3+p*b3];
    O8 := CayleyOctadEighthPoint(O3, O4);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        O3,
        O4,
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ],
        [ 1, 1, 1, 1 ],
        O8
        ];

    /* It's Cremona image */
    tpOc := "Chi^AB|CDE|FGH_1c";
    vOc  := vmax( vLn({1,2,6,7,8}) + vLn({6,7,8}), vPt({6,7,8}) );
    _Oc := CremonaImage(_O, [2,3,4,5, 6]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

if Chi1av3Case then

    "Cremona action ACDF | BEGH on Chi^AB|CDE|FGH_1a";

    /* The octad */
    tpO := "Chi^AB|CDE|FGH_1a";
    vO  := vmax( vLn({3,4,5}) + vLn({6,7,8}), vPl({3,4,5,6,7,8}) );
    O3 := [ 1, 1+p*a1, a2, a3 ];
    O4 := [ 1, 1+p*b1, b2, a3+p*b3];
    O8 := CayleyOctadEighthPoint(O3, O4);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        O3,
        O4,
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ],
        [ 1, 1, 1, 1 ],
        O8
        ];

    /* It's Cremona image */
    tpOc := "Chi^EF|BCD|AGH_1b";
    vOc  := vmax( vPt({5,6}), vPl({5,6,2,3,4})+ vPl({5,6,1,7,8}) );
    _Oc := CremonaImage(_O, [ 1,3,4,6, 7]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

    "--------";
    "";

end if;

/*** Chi_{2} case ***/
/********************/

if Chi2av1Case then

    "Cremona action ABCD | EFGH on Chi^ABC_2a";

    /* The octad */
    tpO := "Chi^ABC_2a";
    vO  := vLn({4,5,6,7,8}) + vPl({4,5,6,7,8});
    O6 := [ 1, 1+a1*p, 1+a2*p, a3 ];
    O7 := [ 1, 1+p*a1*b1, 1 + p*a2*b1 + p^2*b2, b3 ];
    O8 := CayleyOctadEighthPoint(O6, O7);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ],
        [ 1, 1, 1, 1 ],
        O6,
        O7,
        O8
        ];

    /* It's Cremona image */
    tpOc := "Chi^ABC_2a";
    vOc  := vLn({4,5,6,7,8}) + vPl({4,5,6,7,8});
    _Oc := CremonaImage(_O, [ 1,2,3,4, 5 ]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;


if Chi2av2Case then

    "Cremona action ABDE | CFGH on Chi^ABC_2a";

    /* The octad */
    tpO := "Chi^ABC_2a";
    vO  := vLn({4,5,6,7,8}) + vPl({4,5,6,7,8});
    O6 := [ 1, 1+a1*p, 1+a2*p, a3 ];
    O7 := [ 1, 1+p*b1, 1 + p*(a2*b1/a1) + p^2*b2, b3 ];
    O8 := CayleyOctadEighthPoint(O6, O7);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ],
        [ 1, 1, 1, 1 ],
        O6,
        O7,
        O8
        ];

    /* It's Cremona image */
    tpOc := "Chi^AB|CDE|FGH_1c";
    vOc  := vmax( vLn({1,2,6,7,8}) + vLn({6,7,8}), vPt({6,7,8}) );
    _Oc := CremonaImage(_O, [ 1,2,4,5, 3]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

    "++++++++++++++++++++++";
    "";

end if;

/*
 * Section 4.3 - Cremona action on phi blocks
 ********************************************/

/*** Phi_{1} case ***/
/********************/

if Phi1av1Case then

    "Cremona action ABEF | CDGH on Phi^AB|CD||EF|GH_1a";

    /* The octad */
    tpO := "Phi^AB|CD||EF|GH_1a";
    vO  :=
        vLn({3,4,5,6}) + vLn({3,4,7,8}) +
        vPl({1,2,3,4}) + vPl({5,6,7,8}) ;
    O8 := [ 1, 1+a1*p, a2, a2*b3-b3+1+p*a3 ];
    O3 := [ 0+p*b1, 0+p*b2, 1, b3];
    O4 := CayleyOctadEighthPoint(O8, O3);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        O3,
        O4,
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ],
        [ 1, 1, 1, 1 ],
        O8
        ];

    /* It's Cremona image */
    tpOc := "Phi^ABCD_3a";
    vOc  := vLn({1,2,3,4}) + vPl({1,2,3,4}) + vPl({5,6,7,8});
    _Oc := CremonaImage(_O, [ 1,2,5,6, 7 ]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

if Phi1av2Case then

    "Cremona action ABCD | EFGH on Phi^AB|CD||EF|GH_1a";

    /* The octad */
    tpO := "Phi^AB|CD||EF|GH_1a";
    vO  :=
        vLn({3,4,5,6}) + vLn({3,4,7,8}) +
        vPl({1,2,3,4}) + vPl({5,6,7,8}) ;
    O8 := [ 1, 1+a1*p, a2, a2*b3-b3+1+p*a3 ];
    O3 := [ 0+p*b1, 0+p*b2, 1, b3];
    O4 := CayleyOctadEighthPoint(O8, O3);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        O3,
        O4,
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ],
        [ 1, 1, 1, 1 ],
        O8
        ];

    /* It's Cremona image */
    tpOc := "Phi^AB|CD||EF|GH_1b";
    vOc  := vmax(
        vPt({5, 6}) + vPt({7, 8}),
        vPl({5, 6, 7, 8, 1, 2}) + vPl({5, 6, 7, 8, 3, 4})
        );
    _Oc := CremonaImage(_O, [1,2,3,4, 7]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

if Phi1av3Case then

    "Cremona action ABEH | CDFG on Phi^AB|CD||EF|GH_1a";

    /* The octad */
    tpO := "Phi^AB|CD||EF|GH_1a";
    vO  :=
        vLn({3,4,5,6}) + vLn({3,4,7,8}) +
        vPl({1,2,3,4}) + vPl({5,6,7,8}) ;
    O8 := [ 1, 1+a1*p, a2, a2*b3-b3+1+p*a3 ];
    O3 := [ 0+p*b1, 0+p*b2, 1, b3];
    O4 := CayleyOctadEighthPoint(O8, O3);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        O3,
        O4,
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ],
        [ 1, 1, 1, 1 ],
        O8
        ];

    /* It's Cremona image */
    tpOc := "Phi^AB|CD||EF|GH_1a";
    vOc  :=
        vLn({3,4,5,6}) + vLn({3,4,7,8}) +
        vPl({1,2,3,4}) + vPl({5,6,7,8}) ;
    _Oc := CremonaImage(_O, [1,2,5,8, 7]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

if Phi1av4Case then

    "Cremona action ACEG | BDFH on Phi^AB|CD||EF|GH_1a";

    /* The octad */
    tpO := "Phi^AB|CD||EF|GH_1a";
    vO  :=
        vLn({3,4,5,6}) + vLn({3,4,7,8}) +
        vPl({1,2,3,4}) + vPl({5,6,7,8}) ;
    O8 := [ 1, 1+a1*p, a2, a2*b3-b3+1+p*a3 ];
    O3 := [ 0+p*b1, 0+p*b2, 1, b3];
    O4 := CayleyOctadEighthPoint(O8, O3);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        O3,
        O4,
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ],
        [ 1, 1, 1, 1 ],
        O8
        ];

    /* It's Cremona image */
    tpOc := "Phi^AD|BC||EH|FG_1a";
    vOc  :=
        vLn({1,4,5,8}) + vLn({1,4,6,7}) +
        vPl({1,2,3,4}) + vPl({5,6,7,8});
    _Oc := CremonaImage(_O, [ 1,3,5,7, 2]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

if Phi1av5Case then

    "Cremona action ABCE | DFGH on Phi^AB|CD||EF|GH_1a";

    /* The octad */
    tpO := "Phi^AB|CD||EF|GH_1a";
    vO  :=
        vLn({3,4,5,6}) + vLn({3,4,7,8}) +
        vPl({1,2,3,4}) + vPl({5,6,7,8}) ;
    O8 := [ 1, 1+a1*p, a2, a2*b3-b3+1+p*a3 ];
    O3 := [ 0+p*b1, 0+p*b2, 1, b3];
    O4 := CayleyOctadEighthPoint(O8, O3);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        O3,
        O4,
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ],
        [ 1, 1, 1, 1 ],
        O8
        ];

    /* It's Cremona image */
    tpOc := "Phi^ABF||CGH_2a";
    vOc  := vmax(
        vLn({ 3, 7, 8 })       + vLn({ 1, 2, 6}),
        vPl({ 3, 7, 8, 4, 5 }) + vPl({ 1, 2, 6, 4, 5 })
        );
    _Oc := CremonaImage(_O, [ 1,2,3,5, 7]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

    "--------";
    "";

end if;


/*** Phi_{2} case ***/
/********************/

if Phi2av1Case then

    "Cremona action ACDE | BFGH on Phi^CDE|FGH_2a";

    /* The octad */
    tpO := "Phi^CDE|FGH_2a";
    vO  := vmax(
        vLn({ 3, 4, 5 })       + vLn({ 6, 7, 8}),
        vPl({ 1, 2, 3, 4, 5 }) + vPl({ 1, 2, 6, 7, 8 })
        );
    O5 := [ 0+p*a1, 1, a2*p, a3 ];
    O8 := [ 1, 1+p*b1, b2, 1+p*b3];
    O2 := CayleyOctadEighthPoint(O5, O8);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        O2,
        [ 0, 1, 0, 0 ],
        [ 0, 0, 0, 1 ],
        O5,
        [ 0, 0, 1, 0 ],
        [ 1, 1, 1, 1 ],
        O8
        ];

    /* It's Cremona image */
    tpOc := "Phi^AFGH_3a";
    vOc  := vLn({1,6,7,8}) + vPl({1,6,7,8}) + vPl({2,3,4,5});
    _Oc := CremonaImage(_O, [1,3,4,5, 7]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

if Phi2av2Case then

    "Cremona action ABCD | EFGH on Phi^CDE|FGH_2a";

    /* The octad */
    tpO := "Phi^CDE|FGH_2a";
    vO  := vmax(
        vLn({ 3, 4, 5 })       + vLn({ 6, 7, 8}),
        vPl({ 1, 2, 3, 4, 5 }) + vPl({ 1, 2, 6, 7, 8 })
        );
    O5 := [ 0+p*a1, 1, a2*p, a3 ];
    O8 := [ 1, 1+p*b1, b2, 1+p*b3];
    O2 := CayleyOctadEighthPoint(O5, O8);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        O2,
        [ 0, 1, 0, 0 ],
        [ 0, 0, 0, 1 ],
        O5,
        [ 0, 0, 1, 0 ],
        [ 1, 1, 1, 1 ],
        O8
        ];

    /* It's Cremona image */
    tpOc := "Phi^CDE|FGH_2c";
    vOc  := vLn({ 6,7,8, 1}) + vLn({ 6,7,8, 2 }) + vPl({ 3, 4, 5, 6, 7, 8 });
    _Oc := CremonaImage(_O, [1,2,3,4, 7]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

if Phi2av3Case then

    "Cremona action ABCG | DEFH on Phi^CDE|FGH_2a";

    /* The octad */
    tpO := "Phi^CDE|FGH_2a";
    vO  := vmax(
        vLn({ 3, 4, 5 })       + vLn({ 6, 7, 8}),
        vPl({ 1, 2, 3, 4, 5 }) + vPl({ 1, 2, 6, 7, 8 })
        );
    O5 := [ 0+p*a1, 1, a2*p, a3 ];
    O8 := [ 1, 1+p*b1, b2, 1+p*b3];
    O2 := CayleyOctadEighthPoint(O5, O8);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        O2,
        [ 0, 1, 0, 0 ],
        [ 0, 0, 0, 1 ],
        O5,
        [ 0, 0, 1, 0 ],
        [ 1, 1, 1, 1 ],
        O8
        ];

    /* It's Cremona image */
    tpOc := "Phi^DEG|CFH_2c";
    vOc  := vLn({ 3,6,8, 1}) + vLn({ 3,6,8, 2 }) + vPl({ 3, 4, 5, 6, 7, 8 });
    _Oc := CremonaImage(_O, [1,2,3,7, 4]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

    "--------";
    "";

end if;

/*** Phi_{3} case ***/
/********************/

if Phi3av1Case then

    "Cremona action ABCD | EFGH on Phi^ABCD_3a";

    /* The octad */
    tpO := "Phi^ABCD_3a";
    vO  := ( vLn({1, 2, 3, 4}) + vPl({1, 2, 3, 4}) + vPl({5, 6, 7, 8}) );
    O8 := [ a3, a3+p*a1, a2, 1 ];
    O3 := [ b3, b1, p*b2*a2*(a3-1), p*b2*(a3-a2) ];
    O4 := CayleyOctadEighthPoint(O8, O3);
    _O := Parent([[Foctad|]])![
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        O3,
        O4,
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ],
        [ 1, 1, 1, 1 ],
        O8
        ];

    /* It's Cremona image */
    tpOc := "Phi^ABCD_3b";
    vOc  := vPt({5, 6, 7, 8}) + vLn({5, 6, 7, 8}) + vPl({5, 6, 7, 8});
    _Oc := CremonaImage(_O, [ 1,2,3,4, 7]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;
