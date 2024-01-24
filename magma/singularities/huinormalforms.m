/* Normal forms for non smooth quartics, following [Hui1979]

  The function defined here, HuiNormalForms(type), returns normal forms as listed p. 107 in [Hui1979].

  [Hui1979] Chung-man HUI, Plane quartic curves, phd, University of Liverpool, April 1979
 */

/***
 * Exported intrinsics.
 *
 * intrinsic HuiNormalForms(type::MonStgElt :
 *     Domain := [-1000..1000], Monic := false) -> RngMPolElt
 *
 *     {
 *     Returns a normal form for the given singularity type,
 *     as listed p. 107 in Hui 1979 Phd thesis.
 *     }
 *
 ********************************************************************/


/* Argument "type" can be either

     any of these 21 Irreducible types :

[ "(A1)", "(A2)", "(A1^2)", "(A3)", "(A4)", "(A1A2)", "(A1^3)", "(D4)", "(A2^2)", "(A1A3)", "(A1^2A2)", "(A5)", "(D5)", "(A2A3)", "(A1A4)", "(A1A2^2)", "(A6)", "(E6_1)", "(E6_0)", "(A2A4)", "(A2^3)" ]

	among which 17 are not unstable :

[ "(A1"), "(A2"), "(A1^2"), "(A3"), "(A4"), "(A1A2"), "(A1^3"), "(A2^2"), "(A1A3"), "(A1^2A2"), "(A5"), "(A2A3"), "(A1A4"), "(A1A2^2"), "(A6"), "(A2A4"), "(A2^3") ]

	in other words, "(D4)", "(D5)", "(E6_1)", "(E6_0)" are the only unstable cases.


    or any of these 35 reducible types :

  [ "(rA1^3)", "(rA1A3)", "(rA1^4_cub)", "(rA1^4_con)", "(rA5)", "(rX9)", "(rA1D4)", "(rA3^2)", "(rA1^2A3_cub)", "(rA1^2A3_con)", "(rA1^3A2)", "(rA1^5)", "(rD6)", "(rA7)", "(rE7)", "(rA1A5_con)", "(rA1A5_cub)", "(rA1D6)", "(rA2A5)", "(rA1^2D4)", "(rA1A2A3)", "(rA1A3^2)", "(rA1^3A3)", "(rA1^3D4)", "(rA1^6)", "(rA1D5_cub)", "(rA1D5_con)", "(l^2c_sec)", "(l^2c_tan)", "(lll^2_sec)", "(lll^2_3rd)", "(c^2)", "(l^2l^2)", "(ll^3)", "(l^4)" ];

	among which 16 are not unstable :

  [ "(rA1^3)", "(rA1A3)", "(rA1^4_cub)", "(rA1^4_con)", "(rA3^2)", "(rA1^2A3_cub)", "(rA1^2A3_con)", "(rA1^3A2)", "(rA1^5)", "(rA7)", "(rA1A5_con)", "(rA1A2A3)", "(rA1A3^2)", "(rA1^3A3)", "(rA1^6)", "(c^2)" ]

	in other words, "(rA5)", "(rX9)", "(rA1D4)", "(rD6)", "(rE7)", "(rA1A5_cub)", "(rA1D6)", "(rA2A5)", "(rA1^2D4)", "(rA1^3D4)", "(rA1D5_cub)", "(rA1D5_con)", "(l^2c_sec)", "(l^2c_tan)", "(lll^2_sec)", "(lll^2_3rd)", "(l^2l^2)", "(ll^3)", "(l^4)" are the only unstable cases.

 */

intrinsic HuiNormalForms(type::MonStgElt :
    Domain := [-1000..1000], Monic := false) -> RngMPolElt

    {
    Returns an irreducible normal form for the given singularity type,
    as listed p. 107 in Hui 1979 Phd thesis.
    }

    if Type(Domain) eq SeqEnum and Domain eq [] then
        K := FunctionField(Universe(Domain), 15);
        a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 :=
            Explode([K.i : i in [1..Rank(K)]]);
    else
        k := Type(Domain) ne SeqEnum select Domain else Universe(Domain);
        K := IsField(k) select k else FieldOfFractions(k);
        a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 :=
            Explode( [K| Random(Domain) : i in [1..15] ] );
    end if;

    Pxyz := PolynomialRing(K, 3); X := Pxyz.1; Y := Pxyz.2; Z := Pxyz.3;

    f := Pxyz!0;

    case type:

    // +++++++++++++++++
    // Irreducible cases
    // +++++++++++++++++

        // Dimension 5
        // -----------

    when "(A1)" :               /* 1 node */
        if Monic then a01 := K!1; end if;
        a20 := a01; a21 := a01;

        f :=
           (          a01*Y                                        )*Z^3 +
           (a20*X^2             + a02*Y^2                          )*Z^2 +
           (          a21*X^2*Y + a12*X*Y^2   + a03*Y^3            )*Z   +
                                                a13*X*Y^3 + a04*Y^4;

        // Dimension 4
        // -----------


    when "(A2)" :               /* 1 cusp */
        if Monic then a01 := K!1; end if;
        a20 := a01; a13 := a01;

        f :=
           (          a01*Y                                        )*Z^3 +
           (a20*X^2 + a11*X*Y   + a02*Y^2                          )*Z^2 +
           (                      a12*X*Y^2   + a03*Y^3            )*Z   +
                                                a13*X*Y^3          ;

    when "(A1^2)" :               /* 2 nodes */
        if Monic then a22 := K!1; end if;
        a20 := a22; a02 := a22;

        f :=
            a00*Z^4 +
           (a10*X   + a01*Y                                        )*Z^3 +
           (a20*X^2 + a11*X*Y   + a02*Y^2                          )*Z^2 +
                                  a22*X^2*Y^2                      ;

        // Dimension 3
        // -----------

    when "(A3)" :               /* 1 tacnode */
        if Monic then a20 := K!1; end if;
        a04 := a20; a31 := a20;

        f :=
           (a20*X^2                                                )*Z^2 +
           (                      a12*X*Y^2                        )*Z   +
                      a31*X^3*Y + a22*X^2*Y^2 + a13*X*Y^3 + a04*Y^4;

    when "(A1A2)" :               /* 1 node & 1 cusp */
        if Monic then a22 := K!1; end if;
        a02 := a22; a10 := a22;

        f :=
            a00*Z^4 +
           (a10*X   + a01*Y                                        )*Z^3 +
           (          a11*X*Y   + a02*Y^2                          )*Z^2 +
                                  a22*X^2*Y^2                      ;

    when "(A1^3)" :               /* 3 nodes */
        if Monic then a22 := K!1; end if;
        a20 := a22; a02 := a22;

        f :=
           (a20*X^2 + a11*X*Y   + a02*Y^2                          )*Z^2 +
           (          a21*X^2*Y + a12*X*Y^2                        )*Z   +
                                  a22*X^2*Y^2                      ;

        // Dimension 2
        // -----------

    when "(A4)" :               /* Ramphoid cusp */
        if Monic then a20 := K!1; end if;
        a12  := 2*a20; a04 := a20; a31 := a20;

        f :=
           (a20*X^2                                                )*Z^2 +
           (                      a12*X*Y^2                        )*Z   +
                      a31*X^3*Y + a22*X^2*Y^2 + a13*X*Y^3 + a04*Y^4;

   when "(D4)" :               /* 1 triple point (unstable) */
        if Monic then a21 := K!1; end if;
        a12 := a21; a40 := -a21;

        f :=
           (          a21*X^2*Y + a12*X*Y^2                        )*Z   +
            a40*X^4             + a22*X^2*Y^2             + a04*Y^4;

    when "(A2^2)" :               /* 2 cusps */
        if Monic then a22 := K!1; end if;
        a10 := a22; a01 := a22;

        f :=
            a00*Z^4 +
           (a10*X   + a01*Y                                        )*Z^3 +
           (          a11*X*Y                                      )*Z^2 +
                                  a22*X^2*Y^2                      ;

    when "(A1A3)" :               /* 1 node & 1 tacnode */
        if Monic then a04 := K!1; end if;
        a20 := a04;
        a21 := a04;

        f :=
           (a20*X^2                                                )*Z^2 +
           (          a21*X^2*Y + a12*X*Y^2                        )*Z   +
                                                a13*X*Y^3 + a04*Y^4;

    when "(A1^2A2)" :               /* 2 nodes & 1 cusp */
        if Monic then a22 := K!1; end if;
        a20 := a22; a02 := a22; a21 := -2*a22;

        f :=
           (a20*X^2 + a11*X*Y   + a02*Y^2                          )*Z^2 +
           (          a21*X^2*Y + a12*X*Y^2                        )*Z   +
                                  a22*X^2*Y^2                      ;


        // Dimension 1
        // -----------

    when "(A5)" :               /* 1 osnode  */
        if Monic then a20 := K!1; end if;
        a12 := 2*a20; a04 := a20; a22 := -a20;

        f :=
           (a20*X^2                                                )*Z^2 +
           (                      a12*X*Y^2                        )*Z   +
                      a31*X^3*Y + a22*X^2*Y^2             + a04*Y^4;

    when "(D5)" :               /* 1 triple point (unstable) */
        if Monic then a21 := K!1; end if;
        a40 := -a21; a04 := -a21;

        f :=
           (          a21*X^2*Y                                    )*Z   +
            a40*X^4 +                           a13*X*Y^3 + a04*Y^4;

    when "(A2A3)" :               /* 1 cusp & 1 tacnode */
        if Monic then a04 := K!1; end if;
        a20 := a04; a13 := a04;

        f :=
           (a20*X^2                                                )*Z^2 +
           (                      a12*X*Y^2                        )*Z   +
                                                a13*X*Y^3 + a04*Y^4;

    when "(A1A4)" :               /* 1 cusp & 1 Ramphoid cusp */
        if Monic then a20 := K!1; end if;
        a12 := 2*a20; a04 := a20; a13 := -a20;

        f :=
           (a20*X^2                                                )*Z^2 +
           (                      a12*X*Y^2                        )*Z   +
                                  a22*X^2*Y^2 + a13*X*Y^3 + a04*Y^4;

    when "(A1A2^2)" :               /* 1 node & 2 cusps */
        if Monic then a22 := K!1; end if;
        a20 := a22; a02 := a22; a21 := -2*a22; a12 := -2*a22;

        f :=
           (a20*X^2 + a11*X*Y   + a02*Y^2                          )*Z^2 +
           (          a21*X^2*Y + a12*X*Y^2                        )*Z   +
                                  a22*X^2*Y^2                      ;

        // Dimension 0
        // -----------

    when "(A6)" :               /* ? */
        if Monic then a20 := K!1; end if;
        a12 := 2*a20; a04 := a20; a31 := -a20;

        f :=
           (a20*X^2                                                )*Z^2 +
           (                      a12*X*Y^2                        )*Z   +
                      a31*X^3*Y                           + a04*Y^4;


    when "(E6_1)" :               /* 1 triple point (unstable) */
        if Monic then a30 := K!1; end if;
        a22 := -a30; a04 := -a30;

        f :=
           (a30*X^3                                                )*Z   +
                                  a22*X^2*Y^2             + a04*Y^4;

    when "(E6_0)" :               /* 1 triple point (unstable) */
        if Monic then a30 := K!1; end if;
        a04 := -a30;

        f :=
           (a30*X^3                                                )*Z   +
                                                            a04*Y^4;

    when "(A2A4)" :               /* 1 cusp & 1 Ramphoid cusp */
        if Monic then a20 := K!1; end if;
        a12 := 2*a20; a04 := a20; a13 := -a20;

        f :=
           (a20*X^2                                                )*Z^2 +
           (                      a12*X*Y^2                        )*Z   +
                                                a13*X*Y^3 + a04*Y^4;

    when "(A2^3)" :               /* 3 cusps */
        if Monic then a22 := K!1; end if;
        a20 := a22; a02 := a22; a21 := -2*a22; a12 := -2*a22; a11 := -2*a22;

        f :=
           (a20*X^2 + a11*X*Y   + a02*Y^2                          )*Z^2 +
           (          a21*X^2*Y + a12*X*Y^2                        )*Z   +
                                  a22*X^2*Y^2                      ;


    // +++++++++++++++
    // Reducible cases
    // +++++++++++++++

        // Dimension 3
        // -----------

    when "(rA1^3)" :             /* 1 line that intersects a cubic 3 times  */
        if Monic then a22 := K!1; end if;
        a12 := a22; a11 := a22;

        f :=
           (a20*X^2 + a11*X*Y                                      )*Z^2 +
           (a30*X^3 + a21*X^2*Y + a12*X*Y^2                        )*Z   +
                                  a22*X^2*Y^2                      ;

        // Dimension 2
        // -----------

    when "(rA1A3)" :             /* 1 line tangent at a cubic that further intersects it  */
        if Monic then a30 := K!1; end if;
        a22 := a30; a12 := a30;

        f :=
           (a20*X^2                                                )*Z^2 +
           (a30*X^3 + a21*X^2*Y + a12*X*Y^2                        )*Z   +
                                  a22*X^2*Y^2                      ;

    when "(rA1^4_cub)" :             /* A line that instersects a singular cubic three times   */
        if Monic then a22 := K!1; end if;
        a12 := a22; a11 := a22;

        f :=
           (a20*X^2 + a11*X*Y                                      )*Z^2 +
           (          a21*X^2*Y + a12*X*Y^2                        )*Z   +
                                  a22*X^2*Y^2                      ;

    when "(rA1^4_con)" :             /* two conics that instersects 4 times   */
        if Monic then a02 := K!1; end if;
        a21 := a20 + a22;
        a12 := a02 + a22;
        a11 := a02 + a20;

        f :=
           (a20*X^2 + a11*X*Y   + a02*Y^2                          )*Z^2 +
           (          a21*X^2*Y + a12*X*Y^2                        )*Z   +
                                 a22*X^2*Y^2                      ;

        // Dimension 1
        // -----------

    when "(rA5)" :               /* 1 line tangent at a cubic at a flex (unstable)*/
        if Monic then a30 := K!1; end if;
        a20 := a30; a13 := a30;

        f :=
           (a20*X^2                                                )*Z^2 +
           (a30*X^3 + a21*X^2*Y                                    )*Z   +
                                                a13*X*Y^3          ;

    when "(rX9)" :               /* 4 lines (unstable) */
        if Monic then a00 := K!1; end if;
        a40 := a00;

        f :=
            a00*Z^4 +
           (a20*X^2                                                )*Z^2 +
            a40*X^4                                                ;

    when "(rA1D4)" :             /* 1 line tangent at a cubic that further intersects it at a node (unstable) */
        if Monic then a40 := K!1; end if;
        a11 := a40; a21 := a40;

        f :=
           (          a11*X*Y                                      )*Z^2 +
           (a30*X^3 + a21*X^2*Y                                    )*Z   +
            a40*X^4                                                ;

    when "(rA3^2)" :             /* 2 bi-tangent conics  */
        if Monic then a02 := K!1; end if;
        a21 := a40+a02;

        f :=
           (                      a02*Y^2                          )*Z^2 +
           (          a21*X^2*Y                                    )*Z   +
            a40*X^4                                                ;

    when "(rA1^2A3_cub)" :             /* a line that intersects 2 times a singular cubic, one intersection is a tangent  */
        if Monic then a20 := K!1; end if;
        a22 := a20; a12 := a20;

        f :=
           (a20*X^2                                                )*Z^2 +
           (          a21*X^2*Y + a12*X*Y^2                        )*Z   +
                                  a22*X^2*Y^2                      ;

    when "(rA1^2A3_con)" :             /* two conics that intersects 3 times, one at a tangent */
        if Monic then a22 := K!1; end if;
        a12 := a02 + a22; a11 := a02 + a22;
        a21 := 2*a22; a20 := a22;

        f :=
           (a20*X^2 + a11*X*Y   + a02*Y^2                          )*Z^2 +
           (          a21*X^2*Y + a12*X*Y^2                        )*Z   +
                                  a22*X^2*Y^2                      ;

    when "(rA1^3A2)" :              /* a line that intersects 3 times a singular cubic with  a cusp  */
        if Monic then a10 := K!1; end if;
        a22 := a10; a12 := a10;

        f :=
           (a10*X                                                  )*Z^3 +
           (          a11*X*Y                                      )*Z^2 +
           (                      a12*X*Y^2                        )*Z   +
                                  a22*X^2*Y^2                      ;




    when "(rA1^5)" :              /* two lines that intersects a conic  */
        if Monic then a21 := K!1; end if;
        a11 := a21; a12 := a21;

        f :=
           (          a11*X*Y   + a02*Y^2                          )*Z^2 +
           (          a21*X^2*Y + a12*X*Y^2                        )*Z
                                                                   ;
    // ++++++++++++++++++
    // Non isolated cases
    // +++++++++++++µ++++

        // Dimension 0
        // -----------

    when "(rD6)" :               /* 1 line tange,t at 1 cubic with a node (unstable)*/
        if Monic then a40 := K!1; end if;
        a10 := a40; a21 := a40;

        f :=
           (a10*X                                                  )*Z^3 +
           (          a21*X^2*Y                                    )*Z   +
            a40*X^4                                                ;

    when "(rA7)" :               /* 2 tangent conics */
        if Monic then a40 := K!1; end if;
        a22 := a40; a21 := 2*a40; a03 := a40; a02 := a40;

        f :=
           (                      a02*Y^2                          )*Z^2 +
           (          a21*X^2*Y               + a03*Y^3            )*Z   +
            a40*X^4             + a22*X^2*Y^2                      ;

    when "(rE7)" :               /* line tangent at a cusp of cubic (unstable) */
        if Monic then a10 := K!1; end if;
        a31 := a10; a20 := a10;

        f :=
           (a10*X                                                  )*Z^3 +
           (a20*X^2                                                )*Z^2 +
                      a31*X^3*Y                                    ;

    when "(rA1A5_con)" :             /* 2 conics that intersects at 2 points (one is a flex) */
        if Monic then a22 := K!1; end if;
        a12 := a22; a11 := 2*a22; a01 := a22; a00 := a22;

        f :=
            a00*Z^4 +
           (          a01*Y                                        )*Z^3 +
           (          a11*X*Y                                      )*Z^2 +
           (                      a12*X*Y^2                        )*Z   +
                                  a22*X^2*Y^2                      ;

    when "(rA1A5_cub)" :             /* a line tangent at a flex of a cubic that has a node (unstable)*/
        if Monic then a11 := K!1; end if;
        a22 := a10; a21 := a10;

        f :=
           (a10*X                                                  )*Z^3 +
           (          a21*X^2*Y                                    )*Z   +
                                  a22*X^2*Y^2                      ;

    when "(rA1D6)" :             /* two lines that intersects a conic at one common point, one line is tangent to the conic (unstable) */
        if Monic then a03 := K!1; end if;
        a11 := a03;

        f :=
           (          a11*X*Y                                      )*Z^2 +
           (                                    a03*Y^3            )*Z;

    when "(rA2A5)" :             /* a line that intersects a cubic at a flex, the cubic has a cusp (unstable) */
        if Monic then a10 := K!1; end if;
        a22 := a10;

        f :=
           (a10*X                                                  )*Z^3 +
                                  a22*X^2*Y^2                      ;

    when "(rA1^2D4)" :           /* two lines that intersects a conic three times, one time at a common point (unstable) */
        if Monic then a02 := K!1; end if;
        a11 := a02; a12 := a02;

        f :=
           (          a11*X*Y   + a02*Y^2                          )*Z^2 +
           (                      a12*X*Y^2                        )*Z;

   when "(rA1A2A3)" :           /* a line that intersects a singular cubic (cups) two times, one time tangently */
        if Monic then a20 := K!1; end if;
        a21 := 2*a20; a22 := a20; a12 := a20;

        f :=
           (a20*X^2                                                )*Z^2 +
           (          a21*X^2*Y + a12*X*Y^2                        )*Z   +
                                  a22*X^2*Y^2                      ;

   when "(rA1A3^2)" :           /* two lines both tangent to a conic  */
       if Monic then a21 := K!1; end if;
       a02 := a21;

        f :=
           (                      a02*Y^2                          )*Z^2 +
           (          a21*X^2*Y                                    )*Z;

   when "(rA1^3A3)" :           /* two lines that intersects a conic, one is a tagent  */
       if Monic then a21 := K!1; end if;
       a02 := a21; a11 := a21;

        f :=
           (          a11*X*Y   + a02*Y^2                          )*Z^2 +
           (          a21*X^2*Y                                    )*Z
           ;

   when "(rA1^3D4)" :           /* 4 lines, 3 of them intersects at the same point (unstable) */
       if Monic then a21 := K!1; end if;
       a11 := a21;

       f :=
           (          a11*X*Y                                      )*Z^2 +
           (          a21*X^2*Y                                    )*Z
                                                                   ;
                                         ;
   when "(rA1^6)" :           /* 4 lines in general position */
       if Monic then a21 := K!1; end if;
       a12 := a21; a11 := a21;

        f :=
           (          a11*X*Y                                      )*Z^2 +
           (          a21*X^2*Y + a12*X*Y^2                        )*Z
                                                                   ;

    when "(rA1D5_cub)" :             /* a line that intersects two times a cubic, one time at a cusp (unstable) */
        if Monic then a40 := K!1; end if;
        a11 := a40; a30 := a40;

        f :=
           (          a11*X*Y                                      )*Z^2 +
           (a30*X^3                                                )*Z   +
            a40*X^4                                                ;


    when "(rA1D5_con)" :             /* a line that intersects two times a cubic, one time at a cusp (unstable) */
        if Monic then a40 := K!1; end if;
        a11 := a40;

        f :=
           (          a11*X*Y                                      )*Z^2 +
            a40*X^4                                                ;

        // Not isolated
        // -----------

   when "(l^2c_sec)" :               /* a double line instersect a conic (unstable) */
       if Monic then a21 := K!1; end if;
       a30 := a21; a31 := a21;

        f :=
           (a30*X^3 + a21*X^2*Y                                    )*Z   +
                      a31*X^3*Y                                    ;

   when "(l^2c_tan)" :               /* a double line tangent to a conic (unstable) */
       if Monic then a02 := K!1; end if;
       a10 := a02;

        f :=
           (a10*X                                                  )*Z^3 +
           (                      a02*Y^2                          )*Z^2 ;

   when "(lll^2_sec)" :               /* a double line intersect two others (unstable) */
        if Monic then a11 := K!1; end if;
        f :=
           (          a11*X*Y                                      )*Z^2 ;

   when "(lll^2_3rd)" :               /* a double line intersects two others at the same point (unstable) */
       if Monic then a20 := K!1; end if;
       a10 := a20;

       f :=
           (a10*X                                                  )*Z^3 +
           (a20*X^2                                                )*Z^2 ;

   when "(c^2)" :               /* a double conic */
        if Monic then a22 := K!1; end if;
       a11 := 2*a22; a00 := a22;

        f :=
            a00*Z^4 +
           (          a11*X*Y                                      )*Z^2 +
                                  a22*X^2*Y^2                      ;

   when "(l^2l^2)" :               /* two double lines that instersects (unstable) */
        if Monic then a20 := K!1; end if;
        f :=
           (a20*X^2                                                )*Z^2 ;

   when "(ll^3)" :               /* A triple lines that instersects another one (unstable) */
        if Monic then a10 := K!1; end if;
        f :=
           (a10*X                                                  )*Z^3 ;

   when "(l^4)" :               /* A fourfold line (unstable) */
        if Monic then a00 := K!1; end if;
        f :=
            a00*Z^4 ;

        // Unknown type
   else:
       error
       "Unknown type \"" cat type cat "\"\n\n" cat
       "Available types are\n\n" cat
       "Irreducible:", [ "(A1)", "(A2)", "(A1^2)", "(A3)", "(A4)", "(A1A2)", "(A1^3)", "(D4)", "(A2^2)", "(A1A3)", "(A1^2A2)", "(A5)", "(D5)", "(A2A3)", "(A1A4)", "(A1A2^2)", "(A6)", "(E6_1)", "(E6_0)", "(A2A4)", "(A2^3)" ],
       "\n",
       "Reducible:", [ "(rA1^3)", "(rA1A3)", "(rA1^4_cub)", "(rA1^4_con)", "(rA5)", "(rX9)", "(rA1D4)", "(rA3^2)", "(rA1^2A3_cub)", "(rA1^2A3_con)", "(rA1^3A2)", "(rA1^5)", "(rD6)", "(rA7)", "(rE7)", "(rA1A5_con)", "(rA1A5_cub)", "(rA1D6)", "(rA2A5)", "(rA1^2D4)", "(rA1A2A3)", "(rA1A3^2)", "(rA1^3A3)", "(rA1^3D4)", "(rA1^6)", "(rA1D5_cub)", "(rA1D5_con)"],
       "\n",
       "Not isolated:", [ "(l^2c_sec)", "(l^2c_tan)", "(lll^2_sec)", "(lll^2_3rd)", "(c^2)", "(l^2l^2)", "(ll^3)", "(l^4)" ];

   end case;

   return f;

end intrinsic;


/* In general :

        f :=
            a00*Z^4 +
           (a10*X   + a01*Y                                        )*Z^3 +
           (a20*X^2 + a11*X*Y   + a02*Y^2                          )*Z^2 +
           (a30*X^3 + a21*X^2*Y + a12*X*Y^2   + a03*Y^3            )*Z   +
            a40*X^4 + a31*X^3*Y + a22*X^2*Y^2 + a13*X*Y^3 + a04*Y^4;
*/
