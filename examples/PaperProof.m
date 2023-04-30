/* Computational proofs of some results of [Bom+23].

  [Bom+23] R. van Bommel, J. Docking, V. Dokchitser, R. Lercier and E. Lorenzo García, Reduction of plane quartics and Cayley octads, arXiv:xxx.
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

if ByDefault then
    RegularCase     := true;

    Alpha1av1Case   := true; Alpha1av2Case   := true;
    Alpha2bv1Case   := true; Alpha2bv2Case   := true;

    Chi1av1Case   := true; Chi1av2Case   := true; Chi1av3Case   := true;
    Chi2av1Case   := true; Chi2av2Case   := true;
end if;

"";

/* Toolbox */
_, KeySets := PluckerCoordinates([ [0,0,0,0] : i in [1..8] ]);

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

    VPlO := Vector([ AdHocVal(e, P) eq Infinity() select 1 else AdHocVal(e, P): e in PlckO ]);
    "\t_ Valuation data of O  equal to a " cat tpO cat "-block:", VPlO eq vO;

    /* It's Cremona image */
    Oc := AdHocNormalize(_Oc, P);

    /* It's valuation data */
    PlckOc, KeySets := PluckerCoordinates(Oc);

    VPlOc := Vector([ AdHocVal(e, P) eq Infinity() select 1 else AdHocVal(e, P): e in PlckOc ]);
    "\t_ Valuation data of O' equal to a " cat tpOc cat "-block:", VPlOc eq vOc;

    /* Relations that make O degenerate */
    OEquations := [];
    for i := 1 to #KeySets do
        v, e := AdHocVal(PlckO[i], P);
        Append(~OEquations, v eq Infinity() select Foctad!1 else Foctad!e);
    end for;

    ODegenerate :=
        &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Numerator(OEquations[i])]>)} : i in [1..70] | PlckO[i] ne 0 }
        join
        &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Denominator(OEquations[i])]>)} : i in [1..70] | PlckO[i] ne 0 };

    /* Relations that make Oc degenerate */
    OcEquations := [];
    for i := 1 to #KeySets do
        v, e := AdHocVal(PlckOc[i], P);
        Append(~OcEquations, v eq Infinity() select Foctad!1 else Foctad!e);
    end for;

    OcDegenerate :=
        &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Numerator(OcEquations[i])]>)} : i in [1..70] | PlckOc[i] ne 0 }
        join
        &join{ { Basis(rd) : rd in  RadicalDecomposition(ideal<Poctad|[Denominator(OcEquations[i])]>)} : i in [1..70] | PlckOc[i] ne 0 };

    /* When PclkOc degenerate while Plck does not ? */
    BadCases := Sort(Setseq(OcDegenerate diff ODegenerate));

    "\t_ Number of bad cases to examine:", #BadCases;

    if #BadCases gt 0 then

        /* Does it correspond to hyperelliptic  degeneracy, as expected ? */

        /* The hyperelliptic locus, mod p */
        TwCubO  := Setseq({ Coefficient(Numerator(e),p,0) : e in CayleyOctadTwistedCubicRelations(PlckO) });

        "\t_Do they correspond to hyperelliptic reduction?!",
            [ { NormalForm(Coefficient(Numerator(e), p, 0), sys) : e in TwCubO } eq {0} : sys in BadCases ];
    else
        "\t=> Everything's fine!";
    end if;
    "";

end procedure;

/* Ring definitions  */
Fld := Rationals();

Poctad<
    a1, a2, a3,
    b1, b2, b3,
    p > := PolynomialRing(Fld, [ 1 : i in [1..2*3+1] ]);
Foctad<
    A1, A2, A3,
    B1, B2, B3,
    P > := FieldOfFractions(Poctad);

/*
 * Generic check - Cremona action on a regular octad
 ***************************************************/

if RegularCase then

    /*** ABCD | EFGH ***/
    "Cremona action ABCD | EFGH on a regular octad";

    /* The octad */
    tpO := "regular";
    vO  := Vector([ 0 : K in KeySets ]);
    O6 := [ 1, a1, a2, a3 ]; O7 := [ 1, b1, b2, b3 ]; O8 := CayleyOctadEighthPoint(O6, O7);
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
    _Oc := CremonaImage(_O, [1, 2, 3, 4, 5]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

    "----------------------";
    "";

end if;

/*
 * Section 4.1 - Cremona action on alpha blocks
 **********************************************/

/*** Alpha_{1} case ***/
/**********************/

if Alpha1av1Case then

    /*** ABCD | EFGH ***/
    "Cremona action ABCD | EFGH on Alpha_{1a}";

    /* The octad */
    tpO := "Alpha^AB_1a";
    vO  := Vector([ Max(0, #(K meet {1,2}) - 1) : K in KeySets ]);
    O6 := [ 1, a1, a2, a3 ]; O7 := [ 1, a1+p*b1, a2+p*b2, a3+p*b3 ]; O8 := CayleyOctadEighthPoint(O6, O7);
    _O := Parent([[Foctad|]])![
        O6,
        O7,
        O8,
        [ 1, 1, 1, 1 ],
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ]
        ];

    /* It's Cremona image */
    tpOc := "Alpha^AB_1a";
    vOc  := Vector([ Max(0, #(K meet {1,2}) - 1) : K in KeySets ]);
    _Oc := CremonaImage(_O, [5,6,7,8, 4]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

if Alpha1av2Case then

    /*** ACDE | BFGH ***/
    "Cremona action ACDE | BFGH on Alpha_{1a}";

    /* The octad */
    tpO := "Alpha^AB_1a";
    vO  := Vector([ Max(0, #(K meet {1,2}) - 1) : K in KeySets ]);
    O6 := [ 1, p*a1, p*a2, p*a3 ]; O7 := [ 1, b1, b2, b3 ]; O8 := CayleyOctadEighthPoint(O6, O7);
    _O := Parent([[Foctad|]])![
        [ 1, 0,  0,  0 ],
        O6,
        [ 0, 1,  0,  0 ],
        [ 0, 0,  1,  0 ],
        [ 0, 0,  0,  1 ],
        [ 1, 1,  1,  1 ],
        O7,
        O8
        ];

    /* It's Cremona image */
    tpOc := "Alpha^BCDE_2a";
    vOc  := Vector([ Max(0, #(K meet {2,3,4,5}) - 3) + Max(0, #(K meet {1,6,7,8}) - 3) : K in KeySets ]);
    _Oc := CremonaImage(_O, [1,3,4,5, 6]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

    "----------------------";
    "";

end if;

/*** Alpha_{2} case ***/
/***********************/

if Alpha2bv1Case then

    /*** ABCD | EFGH ***/
    "Cremona action ABCD | EFGH on Alpha_{2b}";

    /* The octad */
    tpO := "Alpha^ABCD_2b";
    vO  := Vector([ Max(0, #(K meet {1,2,3,4}) - 1) + Max(0, #(K meet {1,2,3,4}) - 3) : K in KeySets ]);
    O6 := [ 1, a1*p+1, a2*p+1, a3*p+1 ]; O7 := [ 1, b1*p+1, b2*p+1, b3*p+1 ]; O8 := CayleyOctadEighthPoint(O6, O7);
    _O := Parent([[Foctad|]])![
        O6,
        O7,
        O8,
        [ 1, 1, 1, 1 ],
        [ 1, 0, 0, 0 ],
        [ 0, 1, 0, 0 ],
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ]
        ];

    /* It's Cremona image */
    tpOc := "Alpha^ABCD_2b";
    vOc  := Vector([ Max(0, #(K meet {1,2,3,4}) - 1) + Max(0, #(K meet {1,2,3,4}) - 3) : K in KeySets ]);
    _Oc := CremonaImage(_O, [5,6,7,8, 4]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

if Alpha2bv2Case then

    /* ABEF | CDGH ***/
    "Cremona action ABEF | CDGH on Alpha_{2b}";

    /* The octad */
    tpO := "Alpha^ABCD_2b";
    vO  := Vector([ Max(0, #(K meet {1,2,3,4}) - 3) + Max(0, #(K meet {5,6,7,8}) - 3) : K in KeySets ]);
    O6 :=  [ 0+p, a1, a2, a3 ]; O7 := [ 1, b1, b2, b3 ]; O8 := CayleyOctadEighthPoint(O6, O7);
    _O := Parent([[Foctad|]])![
        O6,
        [ 0, 1, 0, 0 ],
        [ 0, 0, 1, 0 ],
        [ 0, 0, 0, 1 ],
        [ 1, 1, 1, 1 ],
        [ 1, 0, 0, 0 ],
        O7,
        O8
        ];

    /* It's Cremona image */
    tpOc := "Alpha^AF_2a";
    vOc  := Vector([ Max(0, #(K meet {1,6}) - 1) : K in KeySets ]);
    _Oc := CremonaImage(_O, [6,2,3,4, 5]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

    "----------------------";
    "";

end if;

/*
 * Section 4.2 - Cremona action on chi blocks
 ********************************************/

/*** Chi_{1} case ***/
/********************/

if Chi1av1Case then

    /*** ABCH | DEFG ***/
    "Cremona action ABCD | EFGH on Chi_{1a}";

    /* The octad */
    tpO := "Chi^AB|CFG|DEH_1a";
    vO  := Vector([
        Max(
          Max(0, #(K meet {3,6,7}) - 2) + Max(0, #(K meet {4,5,8}) - 2),
          Max(0, #(K meet {3,4,5,6,7,8}) - 3)
        )
        : K in KeySets ]);
    O6 := [ 1, 1+a1*p, a2, a3 ]; O7 := [ 1, 1+p*b1, b2, a3 + p*b3]; O8 := CayleyOctadEighthPoint(O6, O7);
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
    tpOc := "Chi^AB|CFG|DEH_1a";
    vOc  := Vector([
        Max(
          Max(0, #(K meet {3,6,7}) - 2) + Max(0, #(K meet {4,5,8}) - 2),
          Max(0, #(K meet {3,4,5,6,7,8}) - 3)
        )
        : K in KeySets ]);
    _Oc := CremonaImage(_O, [1,2,3,8,5]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

if Chi1av2Case then

    /*** BCFG | ADEH ***/
    "Cremona action BCDE | AFGH on Chi_{1a}";

    /* The octad */
    tpO := "Chi^AB|CFG|DEH_1a";
    vO  := Vector([
        Max(
          Max(0, #(K meet {3,6,7}) - 2) + Max(0, #(K meet {4,5,8}) - 2),
          Max(0, #(K meet {3,4,5,6,7,8}) - 3)
        )
        : K in KeySets ]);
    O6 := [ 1, 1+a1*p, a2, a3 ]; O7 := [ 1, 1+p*b1, b2, a3 + p*b3]; O8 := CayleyOctadEighthPoint(O6, O7);
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
    tpOc := "Chi^AB|CFG|DEH_1c";
    vOc  := Vector([
        Max(
          Max(0, #(K meet {1,2,4,5,8}) - 2) + Max(0, #(K meet {4,5,8}) - 2),
          Max(0, #(K meet {4,5,8}) - 1)
        )
        : K in KeySets ]);
    _Oc := CremonaImage(_O, [2,3,6,7,5]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

if Chi1av3Case then

    /*** ACFH | BDEG ***/
    "Cremona action ACFH | BDEG on Chi_{1a}";

    /* The octad */
    tpO := "Chi^AB|CFG|DEH_1a";
    vO  := Vector([
        Max(
          Max(0, #(K meet {3,6,7}) - 2) + Max(0, #(K meet {4,5,8}) - 2),
          Max(0, #(K meet {3,4,5,6,7,8}) - 3)
        )
        : K in KeySets ]);
    O6 := [ 1, 1+a1*p, a2, a3 ]; O7 := [ 1, 1+p*b1, b2, a3 + p*b3]; O8 := CayleyOctadEighthPoint(O6, O7);
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
    tpOc := "Chi^GH|ADE|BCF_1c";
    vOc  := Vector([
        Max(
          Max(0, #(K meet {7,8,2,3,6}) - 2) + Max(0, #(K meet {2,3,6}) - 2),
          Max(0, #(K meet {2,3,6}) - 1)
        )
        : K in KeySets ]);
    _Oc := CremonaImage(_O, [2,4,5,7,1]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;

/*** Chi_{2} case ***/
/********************/

if Chi2av1Case then

    /*** ABCD | EFGH ***/
    "Cremona action ABCD | EFGH on Chi_{2a}";

    /* The octad */
    tpO := "Chi^ABC_2a";
    vO  := Vector([ Max(0, #(K meet {4,5,6,7,8}) - 2) + Max(0, #(K meet {4,5,6,7,8}) - 3) : K in KeySets ]);

    O6 := [ 1, 1+a1*p, 1+a2*p, a3 ]; O7 := [ 1, 1+p*b1, 1 + p*(a2*b1/a1) + p^2*b2, b3 ]; O8 := CayleyOctadEighthPoint(O6, O7);

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
    vOc  := Vector([ Max(0, #(K meet {4,5,6,7,8}) - 2) + Max(0, #(K meet {4,5,6,7,8}) - 3) : K in KeySets ]);
    _Oc := CremonaImage(_O, [1,2,3,4,5]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

end if;


if Chi2av2Case then

    /*** ABDE | CFGH ***/
    "Cremona action ABDE | CFGH on Chi_{2a}";

    /* The octad */
    tpO := "Chi^ABC_2a";
    vO  := Vector([ Max(0, #(K meet {4,5,6,7,8}) - 2) + Max(0, #(K meet {4,5,6,7,8}) - 3) : K in KeySets ]);

    O6 := [ 1, 1+a1*p, 1+a2*p, a3 ]; O7 := [ 1, 1+p*b1, 1 + p*(a2*b1/a1) + p^2*b2, b3 ]; O8 := CayleyOctadEighthPoint(O6, O7);

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
    tpOc := "Chi^AB|CFG|DEH_1a";
    vOc  := Vector([
        Max(
          Max(0, #(K meet {3,6,7}) - 2) + Max(0, #(K meet {4,5,8}) - 2),
          Max(0, #(K meet {3,4,5,6,7,8}) - 3)
        )
        : K in KeySets ]);
    _Oc := CremonaImage(_O, [1,2,6,7,5]);

    /* Check */
    ResultChecking(tpO, vO, _O, tpOc, vOc, _Oc);

    "----------------------";
    "";

end if;
