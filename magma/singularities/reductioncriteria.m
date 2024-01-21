/***
 * Exported intrinsics.
 *
 * intrinsic QuarticTypeFromDO(DO::SeqEnum :
 *     Prime := 0) -> SeqEnum
 *
 *     {
 *       Given Dixmier-Ohno invariants, it returns the reduction type at prime if
 *       they are defined over Q and Prime is non-zero. Otherwise, it returns two
 *       lists of compatible singularity types of these Dixmier-Ohno invariants
 *       (in Arnold classification).
 *     }
 *
 * intrinsic  DixmierOhnoSingularityRelations(type::MonStgElt, DOinv::SeqEnum) -> SeqEnum
 *
 *     {
 *       Given a singularity type, it evaluates its stratum relations at the
 *       Dixmier-Ohno invariants in input.
 *     }
 *
 ********************************************************************/

forward HasQuarticReduc, HasHyperReduc, CuspStratum, CuspZeroStratum, CuspNodeStratum, IgusaFromDO, MinimizedValuationsModp, WPSMinimizePPowers, CuspGenus1Stratum, G1G2InvariantsFromDO, Genus1FromCuspDO, CuspDihedInvsFromDO, IgusaFromCuspDihedInvs, NodeDihedInvsFromDO, IgusaFromNodeDihedInvs, NodeGenus1Stratum, NodeGenus1FromDO, TwoCuspsStratum;

forward A4Stratum, RedA1A3Stratum, RedA1p6Stratum, A2p3Stratum, A3Stratum, RedA1p5Stratum, RedA1p3A2Stratum, A1A2p2Stratum, RedA1p4_aStratum, RedA1p4_bStratum, A1p2A2Stratum, RedA1p3Stratum, A1p3Stratum, A1A2Stratum;

forward IsInStratumByValues, IsInStratumByValuations;

/* Redefinitions */
A1p2Stratum := NodeGenus1Stratum;
A2Stratum   := CuspStratum;
A2p2Stratum := TwoCuspsStratum;

/* Basic functions */
function IsInStratumByValues(DO, DOWeight, CS, CSWeight, p)
    return Seqset(CS) eq {0};
end function;

function IsInStratumByValuations(DO, DOWeight, CS, CSWeight, p)
    VminII := MinimizedValuationsModp(DO cat CS, DOWeight cat CSWeight, p);
    return Min(VminII[#DO+1..(#DO+#CS)]) ne 0;
end function;


/***
 * The main routines
 *******************/

intrinsic QuarticTypeFromDO(DO::SeqEnum :
    Prime := 0) -> SeqEnum

    {
      Given Dixmier-Ohno invariants, it returns the reduction type at prime if
      they are defined over Q and Prime is non-zero. Otherwise, it returns two
      lists of compatible singularity types of these Dixmier-Ohno invariants
      (in Arnold classification).
    }

    FF := Universe(DO); p := Prime;

    if Characteristic(FF) in {2, 3, 5, 7 } then
        error "Error, Hui singularity type not available for p = " cat IntegerToString(Characteristic(FF)) cat "\n";
        return [];
    end if;

    IsInStratum := IsInStratumByValues;
    WG := [ 1, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 9 ];
    reduction := Characteristic(FF) eq 0 and Prime ne 0;

    DiscQ := DiscriminantFromDixmierOhnoInvariants(DO);

    _DO := DO;
    if reduction then
        /* Hyperelliptic reduction */
        if HasHyperReduc(DiscQ, DO, Prime : DOWeight := WG) then return "(3 hyper)";  end if;

        IsInStratum := IsInStratumByValuations;
        _DO := WPSMinimizePPowers(WG, DO, p);
    end if;

    /* Unstable quartics */
    if Seqset(_DO) eq {0} then
        return reduction select [] else &cat[
            [ "(D4)", "(D5)", "(E6_a)", "(E6_b)" ],
            [ "(rA5)", "(rA1D4)", "(rX9)", "(rD6)", "(rE7)", "(rA1A5_b)", "(rA1D6)", "(rA2A5)", "(rA1^2D4)", "(rA1^3D4)", "(rA1D5_a)", "(rA1D5_b)", "(l^2c_a)", "(l^2c_b)", "(lll^2_a)", "(lll^2_b)", "(l^2l^2)", "(ll^3)", "(l^4)" ]
            ];
    end if;

    /* Smooth quartics */
    if not IsInStratum(_DO, WG, [DiscQ], [27], p) then
        return reduction select [ "(3)" ] else &cat[ [ "(A0)" ], [] ];
    end if;


    /* Dimension 0
     *************/
    CS, CSWght := A4Stratum(_DO);
    if IsInStratum(_DO, WG, CS, CSWght, p) then
        return reduction select ["(singular hyper)"] else &cat[
            [ "(A4)", "(A5)", "(A1A4)", "(A6)", "(A2A4)" ],
            [ "(rA7)", "(rA1A5_a)", "(c^2)" ]
            ];
    end if;

    CS, CSWght := RedA1A3Stratum(_DO);
    if IsInStratum(_DO, WG, CS, CSWght, p) then
        return reduction select
            [ "(0e=0e)", "(0m=0e)", "(0m=0m)", "(0n=0e)", "(0n=0m)", "(0n=0n)", "(1=0e)", "(1=0m)", "(1=0n)", "(1=1)", "(Z=0e)", "(Z=0m)", "(Z=0n)", "(Z=1)", "(Z=Z)" ]
            else &cat[
            [],
            [ "(rA1A3)", "(rA1^2A3_a)", "(rA1A2A3)", "(rA1A3^2)", "(rA1^3A3)" ]
            ];
    end if;

    CS, CSWght := RedA1p6Stratum(_DO);
    if IsInStratum(_DO, WG, CS, CSWght, p) then
        return reduction select [ "(BRAID)" ] else &cat[
            [],
            [ "(rA1^6)" ]
            ];
    end if;

    CS, CSWght := A2p3Stratum(_DO);
    if IsInStratum(_DO, WG, CS, CSWght, p) then
        return reduction select [ "(0eee)", "(0mee)", "(0mme)", "(0mmm)" ] else &cat[
            [ "(A2^3)" ],
            []
            ];
    end if;

    /* Dimension 1
     *************/

    CS, CSWght := A3Stratum(_DO);
    if IsInStratum(_DO, WG, CS, CSWght, p) then
        return reduction select
            [ "(0e=0e)", "(0m=0e)", "(0m=0m)", "(0n=0e)", "(0n=0m)", "(0n=0n)", "(1=0e)", "(1=0m)", "(1=0n)", "(1=1)", "(Z=0e)", "(Z=0m)", "(Z=0n)", "(Z=1)", "(Z=Z)" ]
            else &cat[
            [ "(A3)", "(A1A3)", "(A2A3)" ],
            [ "(rA3^2)", "(rA1^2A3_b)" ]
            ];
    end if;

    CS, CSWght := RedA1p5Stratum(_DO);
    if IsInStratum(_DO, WG, CS, CSWght, p) then
        return reduction select [ "(CAVE)" ] else &cat[
            [],
            [ "(rA1^5)" ]
            ];
    end if;

    CS, CSWght := RedA1p3A2Stratum(_DO);
    if IsInStratum(_DO, WG, CS, CSWght, p) then
        return reduction select [ "(0---0e)", "(0---0m)" ] else &cat[
            [],
            [ "(rA1^3A2)" ]
            ];
    end if;

    CS, CSWght := A1A2p2Stratum(_DO);
    if IsInStratum(_DO, WG, CS, CSWght, p) then
        return reduction select [ "(0nee)", "(0nme)", "(0nmm)" ] else &cat[
            [ "(rA1A2^2)" ],
            []
            ];
    end if;

    /* Dimension 2
     *************/

     CS, CSWght := RedA1p4_aStratum(_DO);
     if IsInStratum(_DO, WG, CS, CSWght, p) then
        return reduction select [ "(0---0n)" ] else &cat[
            [],
            [ "(rA1^4_a)" ]
            ];
    end if;

    CS, CSWght := RedA1p4_bStratum(_DO);
    if IsInStratum(_DO, WG, CS, CSWght, p) then
        return reduction select [ "(0----0)" ] else &cat[
            [],
            [ "(rA1^4_b)" ]
            ];
    end if;

    CS, CSWght := A1p2A2Stratum(_DO);
    if IsInStratum(_DO, WG, CS, CSWght, p) then
        return reduction select [ "(0nne)", "(0nnm)" ] else &cat[
            [ "(A1^2A2)" ],
            []
            ];
    end if;

    /* Dimension 3
     *************/

    CS, CSWght := RedA1p3Stratum(_DO);
    if IsInStratum(_DO, WG, CS, CSWght, p) then
        return reduction select [ "(1---0)" ] else &cat[
            [],
            [ "(rA1^3)" ]
            ];
    end if;

    CS, CSWght := A1p3Stratum(_DO);
    if IsInStratum(_DO, WG, CS, CSWght, p) then
        return reduction select [ "(0nnn)" ] else &cat[
            [ "(A1^3)" ],
            []
            ];
    end if;


    /* A1^iA2^j cases (0 <= i, j <= 2)
     *********************************/
    CS, CSWght := CuspStratum(_DO);
    if IsInStratum(_DO, WG, CS, CSWght, p) then

        CS, CSWght := TwoCuspsStratum(_DO);
        if IsInStratum(_DO, WG, CS, CSWght, p) then
            return reduction select [ "(1ee)", "(1me)", "(1mm)" ] else &cat[
                [ "(A2^2)" ],
                []
                ];
        end if;

        CS, CSWght := A1A2Stratum(_DO);
        if IsInStratum(_DO, WG, CS, CSWght, p) then
            return reduction select [ "(1ne)", "(1nm)" ] else &cat[
                [ "(A1A2)" ],
                []
                ];
        end if;

        return reduction select [ "(2e)", "(2m)" ] else &cat[ [ "(A2)" ], [] ];

    end if;

    CS, CSWght := NodeGenus1Stratum(_DO);
    if IsInStratum(_DO, WG, CS, CSWght, p) then
        return reduction select [ "(1nn)" ] else &cat[
            [ "(A1^2)" ],
            []
            ];
    end if;

    /* default */
    return reduction select [ "(2n)" ] else &cat[
        [ "(A1)" ],
        []
        ];

end intrinsic;


intrinsic  DixmierOhnoSingularityRelations(type::MonStgElt, DOinv::SeqEnum) -> SeqEnum

    {
      Given a singularity type, it evaluates its stratum relations at the
      Dixmier-Ohno invariants in input.
    }

    FF := Universe(DOinv);

    require IsUnit(FF!(2*3*5*7)) :
        "Argument must be a sequence over a ring in which 2, 3 5 and 7 are units.";

    I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27 := Explode(DOinv);

    /* Smooth quartics */
    if type in [ "(3)" ] then return [], 0; end if;

    /* Dimension 0
     *************/
     if type in &cat[
            [ "(A4)", "(A5)", "(A1A4)", "(A6)", "(A2A4)" ],
            [ "(rA7)", "(rA1A5_a)", "(c^2)" ]
            ] then
            CS, CSWght := A4Stratum(DOinv);
            return CS, CSWght;
     end if;

     if type in &cat[
            [],
            [ "(rA1A3)", "(rA1^2A3_a)", "(rA1A2A3)", "(rA1A3^2)", "(rA1^3A3)" ]
            ] then
            CS, CSWght := RedA1A3Stratum(DOinv);
            return CS, CSWght;
     end if;

     if type in &cat[
            [],
            [ "(rA1^6)" ]
            ] then
            CS, CSWght := RedA1p6Stratum(DOinv);
            return CS, CSWght;
     end if;

     if type in &cat[
            [ "(A2^3)" ],
            []
            ] then
            CS, CSWght := A2p3Stratum(DOinv);
            return CS, CSWght;
     end if;

    /* Dimension 1
     *************/

     if type in &cat[
            [ "(A3)", "(A1A3)", "(A2A3)" ],
            [ "(rA3^2)", "(rA1^2A3_b)" ]
            ] then
            CS, CSWght := A3Stratum(DOinv);
            return CS, CSWght;
     end if;

     if type in &cat[
            [],
            [ "(rA1^5)" ]
            ] then
            CS, CSWght := RedA1p5Stratum(DOinv);
            return CS, CSWght;
     end if;

     if type in &cat[
            [],
            [ "(rA1^3A2)" ]
            ] then
            CS, CSWght := RedA1p3A2Stratum(DOinv);
            return CS, CSWght;
     end if;

     if type in &cat[
            [ "(A1A2^2)" ],
            []
            ] then
            CS, CSWght := A1A2p2Stratum(DOinv);
            return CS, CSWght;
     end if;

    /* Dimension 2
     *************/

     if type in &cat[
            [],
            [ "(rA1^4_a)" ]
            ] then
            CS, CSWght := RedA1p4_aStratum(DOinv);
            return CS, CSWght;
     end if;

     if type in &cat[
            [],
            [ "(rA1^4_b)" ]
            ] then
            CS, CSWght := RedA1p4_bStratum(DOinv);
            return CS, CSWght;
     end if;

     if type in &cat[
            [ "(A1^2A2)" ],
            []
            ] then
            CS, CSWght := A1p2A2Stratum(DOinv);
            return CS, CSWght;
     end if;

    /* Dimension 3
     *************/

     if type in &cat[
            [],
            [ "(rA1^3)" ]
            ] then
            CS, CSWght := RedA1p3Stratum(DOinv);
            return CS, CSWght;
     end if;

     if type in &cat[
            [ "(A1^3)" ],
            []
            ] then
            CS, CSWght := A1p3Stratum(DOinv);
            return CS, CSWght;
     end if;


    /* A1^iA2^j cases (0 <= i, j <= 2)
     *********************************/
     if type in &cat[
         [ "(A2^2)" ],
         []
         ] then
         CS, CSWght := TwoCuspsStratum(DOinv);
         return CS, CSWght;
     end if;

     if type in &cat[
         [ "(A1A2)" ],
         []
         ] then
         CS, CSWght := A1A2Stratum(DOinv);
         return CS, CSWght;
     end if;

     if type in &cat[
            [ "(A2)" ],
            []
            ] then
            CS, CSWght := CuspStratum(DOinv);
            return CS, CSWght;
     end if;

    if type in &cat[
            [ "(A1^2)" ],
            []
            ] then
            CS, CSWght := NodeGenus1Stratum(DOinv);
            return CS, CSWght;
    end if;

    /* default, A1 */
    if type in &cat[
        [ "(A1)" ],
        []
        ] then
        return [DiscriminantFromDixmierOhnoInvariants(DOinv)], 27;
    end if;

    /* Unknonw type */
    error
        "Unknown type \"" cat type cat "\"\n\n" cat
        "Available types are\n\n",
        [ "(3)", "(A1)", "(A1A2)", "(A1A2^2)", "(A1A3)", "(A1A4)", "(A1^2)", "(A1^2A2)", "(A1^3)", "(A2)", "(A2A3)", "(A2A4)", "(A2^2)", "(A2^3)", "(A3)", "(A4)", "(A5)", "(A6)", "(c^2)", "(rA1A2A3)", "(rA1A3)", "(rA1A3^2)", "(rA1A5_a)", "(rA1^2A3_a)", "(rA1^2A3_b)", "(rA1^3)", "(rA1^3A2)", "(rA1^3A3)", "(rA1^4_a)", "(rA1^4_b)", "(rA1^5)", "(rA1^6)", "(rA3^2)", "(rA7)" ];

    return [], 0;

end intrinsic;




/*
 * A quartic reduction criterion (type (3))
 ******************************************/

function HasQuarticReduc(DiscX, DO, p : DOWeight := [ 1, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 9 ])

    VminDO := MinimizedValuationsModp(DO cat [DiscX], DOWeight cat [9], p);
    if VminDO[#VminDO] ne 0 then return false; end if;

    return true;

end function;

/*
 * An hyperelliptic reduction criterion for p > 7 (see [LLLR20])
 ***************************************************************/

function ShiodaFromDO(DO)

    I3, I6, I9, J9, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);


    iota6 := 3^2/(2^5*5*7)*(I3^2-180*I6);
    iota9 := 3^5/(2^9*5^2*7^3)*(14*I3^3-2520*I3*I6-81*I9+135*J9);
    iota12 := 3^3/(2^14*5*7^3)*I3*(-32*I3^3+14580*I3*I6+261*I9-495*J9)+5^2/(2*3*7^2)*iota6^2;
    iota15 := 3^4/(2^16*5^2*7^5)*I3*(-592*I3^4+30780*I3^2*I6+2601*I3*I9-45*I3*J9+7290000*I6^2-2430*J12)+5^2/(3^2*7)*iota6*iota9;
    iota18 := 3^8/(2^24*5^2*7^4)*I3^2*(-8*I3^4-14418*I3^2*I6-117*I3*I9+423*I3*J9+155520*I6^2-486*I12)+17^3/(2^6*3^2*7^3)*iota6^3+3*5/2^5*iota9^2-17/(2^3*7)*iota6*iota12;
    iota21 := 3^7/(2^44*5^7*7^5)*I3^2*(-128*I3^5+213912*I3^3*I6+2961*I3^2*I9-8541*I3^2*J9-18057600*I3*I6^2+12204*I3*I12+810*I3*J12-45360*I6*I9+285120*I6*J9-4860*I15-540*J15)+2*5^3/(3^3*7^2)*iota6^2*iota9-13/(2*3^2)*iota9*iota12-17/(2^2*3*7)*iota6*iota15;

    iota42 := 3^10/(2^18*5^5)*I3^5*I27;

    return
	[iota6, iota9, iota12, iota15, iota18, iota21, iota42],
	[2, 3, 4, 5, 6, 7, 14];

end function;


function WPSMinimizePPowers(W, I, p);

    dens := [ Integers() ! Denominator(i) : i in I ];

    lambda := LCM(dens);

    Inorm := [Integers() | lambda^(W[k]) * I[k] : k in [1..#I] ];

    Imin := Inorm;
    while Seqset([Valuation(Imin[k], p) ge W[k] : k in [1..#Imin] ]) eq {true} do
        Imin := [ Imin[k] div p^W[k] : k in [1..#Imin] ];
    end while;

    return ChangeUniverse(Imin, Rationals());
end function;


function MinimizedValuationsModp(DO, DOWeight, p)

    DS := [ Valuation(DO[i], p) : i in [1..#DO] ];

    dmin := Min([ DS[i] / DOWeight[i]  : i in [1..#DO] ]);

    return [ DS[i] - dmin * DOWeight[i]	: i in [1..#DO] ];

end function;


function HasHyperReduc(DiscX, DO, p : DOWeight := [ 3, 6, 9, 9, 12, 12, 15, 15, 18, 18, 21, 21, 27 ])

    VminDO := MinimizedValuationsModp(DO cat [DiscX], DOWeight cat [27], p);
    if VminDO[#VminDO] eq 0 then return false; end if;

    SH, SHWeight := ShiodaFromDO(DO);

    VminSH := MinimizedValuationsModp(SH, SHWeight, p);
    if VminSH[#SH] ne 0 then return false; end if;

    return true;

end function;

/*
 * Locus of quartics with a cusp
 *********************************/

/* Equations for the locus of quartics with a cusp.

   Up to some linear change of variables, quatics in this locus can be rewritten as :

     f :=
	x^2*a20*z^2+
	(x^3*a30+x^2*y*a21+x*y^2*a12+y^3*a03)*z+
	a40*x^4+a31*x^3*y+a22*x^2*y^2+a13*x*y^3+a04*y^4;


   Dimension 4 (vs 4)
 */
function CuspStratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
        I27,
        13286025*J12^2 - 1003045680*I15*J09 - 77157360*I15*I09 + 58364720505*J09^2*I06 -
        5603553270*J09*I09*I06 - 776395935*I09^2*I06 - 44003314800*J12*I06^2 +
        36434744654400*I06^4 + 92575710*J12*J09*I03 + 16796160*J12*I09*I03 +
        52775634240*I15*I06*I03 - 5855427173160*J09*I06^2*I03 + 300837333960*I09*I06^2*I03 +
        531834255*J09^2*I03^2 + 22938876*J09*I09*I03^2 + 378918*I09^2*I03^2 -
        6048979560*J12*I06*I03^2 + 148460792671440*I06^3*I03^2 + 137168640*I15*I03^3 -
        68380380792*J09*I06*I03^3 - 596660256*I09*I06*I03^3 - 18837360*J12*I03^4 +
        2122728968880*I06^2*I03^4 - 136117872*J09*I03^5 - 4667616*I09*I03^5 +
        8042068800*I06*I03^6 + 9386560*I03^8,
        1102248000*J21 - 4233157200*J12*J09 - 249318000*J12*I09 - 7870050720000*I15*I06 +
        464228751312000*J09*I06^2 - 81624361737600*I09*I06^2 + 7163255655*J09^2*I03 -
        1133586090*J09*I09*I03 - 47536065*I09^2*I03 + 1044600429600*J12*I06*I03 -
        22516130457273600*I06^3*I03 - 27468020160*I15*I03^2 + 5262731160840*J09*I06*I03^2 -
        311423755320*I09*I06*I03^2 + 3218797440*J12*I03^3 - 330803613383760*I06^2*I03^3 +
        14030218368*J09*I03^4 - 171657216*I09*I03^4 - 1426451938560*I06*I03^5 -
        1839011840*I03^7,
        3968092800*I21 + 24538140*J12*J09 - 165993300*J12*I09 - 2955435517440*I15*I06 +
        171755385400800*J09*I06^2 - 29477522190240*I09*I06^2 - 968897295*J09^2*I03 +
        334009494*J09*I09*I03 - 20933883*I09^2*I03 + 367100547120*J12*I06*I03 -
        8360086183286400*I06^3*I03 - 12962436480*I15*I03^2 + 2300125199400*J09*I06*I03^2 -
        154941689160*I09*I06*I03^2 + 1617796800*J12*I03^3 - 133524847632240*I06^2*I03^3 +
        6574736448*J09*I03^4 - 70085376*I09*I03^4 - 622640183040*I06*I03^5 - 879157760*I03^7,
        22044960*J18 - 3064635*J09^2 - 3815910*J09*I09 + 1289925*I09^2 - 47239200*J12*I06 -
        112240339200*I06^3 + 198404640*I15*I03 - 11840038920*J09*I06*I03 +
        2097274680*I09*I06*I03 - 32673780*J12*I03^2 + 585714116880*I06^2*I03^2 -
        86498514*J09*I03^3 - 483102*I09*I03^3 + 6114498840*I06*I03^4 + 13438240*I03^6,
        7348320*I18 - 17721585*J09^2 + 7966350*J09*I09 - 847665*I09^2 - 57736800*J12*I06 +
        144992851200*I06^3 + 7348320*I15*I03 + 1100022120*J09*I06*I03 - 498645720*I09*I06*I03 -
        1443420*J12*I03^2 - 1085276880*I06^2*I03^2 - 2388726*J09*I03^3 - 2446938*I09*I03^3 +
        354048840*I06*I03^4 + 1259360*I03^6,
        4860*J15 + 43740*I15 - 2566080*J09*I06 + 408240*I09*I06 - 7290*J12*I03 +
        127370880*I06^2*I03 - 18729*J09*I03^2 - 207*I09*I03^2 + 1333260*I06*I03^3 + 2960*I03^5,
        486*I12 - 155520*I06^2 - 423*J09*I03 + 117*I09*I03 + 14418*I06*I03^2 + 8*I03^4
        ],
        [ w div 3 : w in [ 27, 24, 21, 21, 18, 18, 15, 12 ]];

end function;


/* Equations for the locus of quartics with a cusp AND a node.

   Dimension 3 (vs 3)
 */

function CuspNodeStratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
        71980619288739840000*I15^3 + 242246283361920000*I15*J12*J09^2 -
        104770876896000*J09^5 - 245965520056320000*I15*J12*J09*I09 +
        729864535680000*J09^4*I09 + 65210616708480000*I15*J12*I09^2 -
        1889142847200000*J09^3*I09^2 + 2199778378560000*J09^2*I09^3 -
        1103394337920000*J09*I09^4 + 195653428992000*I09^5 -
        12092744040508293120000*I15^2*J09*I06 - 13842849173967720000*J12*J09^3*I06
        + 1835505791862865920000*I15^2*I09*I06 +
        15988518147819240000*J12*J09^2*I09*I06 -
        5694073895028600000*J12*J09*I09^2*I06 + 527351604020280000*J12*I09^3*I06 +
        676315759786782105600000*I15*J09^2*I06^2 -
        204848166260392888320000*I15*J09*I09*I06^2 +
        15391962871925667840000*I15*I09^2*I06^2 +
        6940988288557056000000*I15*J12*I06^3 -
        12589161859787218585920000*J09^3*I06^3 +
        5705724582621143887680000*J09^2*I09*I06^3 -
        855590062157009334720000*J09*I09^2*I06^3 +
        42527297954565236160000*I09^3*I06^3 -
        365269508685315072000000*J12*J09*I06^4 +
        51189788628108288000000*J12*I09*I06^4 -
        15692186322769792204800000*I15*I06^5 +
        827530999517268733132800000*J09*I06^6 -
        116565569120369487052800000*I09*I06^6 - 31491520938823680000*I15^2*J12*I03
        - 2482171888065120000*I15*J09^3*I03 +
        2286889309467936000*I15*J09^2*I09*I03 -
        425131253256096000*I15*J09*I09^2*I03 - 71497657272096000*I15*I09^3*I03 +
        3514491226678602240000*I15*J12*J09*I06*I03 +
        144187710347415870000*J09^4*I06*I03 -
        526867070128704000000*I15*J12*I09*I06*I03 -
        157366743171969456000*J09^3*I09*I06*I03 +
        47383381475503452000*J09^2*I09^2*I06*I03 -
        175808335550400000*J09*I09^3*I06*I03 - 669190053349386000*I09^4*I06*I03 +
        596755324213297643520000*I15^2*I06^2*I03 -
        97355804840016397920000*J12*J09^2*I06^2*I03 +
        28732704347687826240000*J12*J09*I09*I06^2*I03 -
        2028040199681931360000*J12*I09^2*I06^2*I03 -
        66891714399969520619520000*I15*J09*I06^3*I03 +
        10115510765774268026880000*I15*I09*I06^3*I03 +
        1872002282615789442428160000*J09^2*I06^4*I03 -
        564953260878781349598720000*J09*I09*I06^4*I03 +
        42293569038128865619200000*I09^2*I06^4*I03 +
        17398975342925972275200000*J12*I06^5*I03 -
        38994033534653703802060800000*I06^7*I03 +
        242612454611939328000*I15^2*J09*I03^2 + 113793124505719500*J12*J09^3*I03^2
        + 26437326220247040000*I15^2*I09*I03^2 -
        71740266200167500*J12*J09^2*I09*I03^2 -
        14869262937901500*J12*J09*I09^2*I03^2 + 13154453760145500*J12*I09^3*I03^2
        - 27690181066783476288000*I15*J09^2*I06*I03^2 +
        1445329205212828032000*I15*J09*I09*I06*I03^2 +
        515565370485627840000*I15*I09^2*I06*I03^2 -
        158509678567115427840000*I15*J12*I06^2*I03^2 +
        782893075790475612828000*J09^3*I06^2*I03^2 -
        161565453621340239132000*J09^2*I09*I06^2*I03^2 -
        10333144682571095244000*J09*I09^2*I06^2*I03^2 +
        2306222653975132140000*I09^3*I06^2*I03^2 +
        8849095258070359094400000*J12*J09*I06^3*I03^2 -
        1323729085007912641920000*J12*I09*I06^3*I03^2 +
        1640600704438232753848320000*I15*I06^4*I03^2 -
        92020813440141479814282240000*J09*I06^5*I03^2 +
        13869489929149706648785920000*I09*I06^5*I03^2 -
        18466404151286592000*I15*J12*J09*I03^3 + 1310104020929545575*J09^4*I03^3 -
        7032214277195328000*I15*J12*I09*I03^3 -
        1246016262711745800*J09^3*I09*I03^3 + 264469716087749550*J09^2*I09^2*I03^3
        + 26669098246597200*J09*I09^3*I03^3 - 13569437400525*I09^4*I03^3 -
        11301557066826227712000*I15^2*I06*I03^3 +
        1059985898972783298000*J12*J09^2*I06*I03^3 +
        221926105058463252000*J12*J09*I09*I06*I03^3 -
        61889349962995470000*J12*I09^2*I06*I03^3 +
        2585167998627128025600000*I15*J09*I06^2*I03^3 -
        68768801726203703808000*I15*I09*I06^2*I03^3 -
        110614964821173143491248000*J09^2*I06^3*I03^3 +
        15780073137292074690720000*J09*I09*I06^3*I03^3 +
        407445643833006900816000*I09^2*I06^3*I03^3 -
        199812690459107367068160000*J12*I06^4*I03^3 +
        1497280045748888305612615680000*I06^6*I03^3 -
        183259701609428217600*I15*J09^2*I03^4 +
        8956459271625062400*I15*J09*I09*I03^4 +
        1574089886414995200*I15*I09^2*I03^4 +
        954183662380065024000*I15*J12*I06*I03^4 +
        10163701666365442812000*J09^3*I06*I03^4 -
        1990215931775346867600*J09^2*I09*I06*I03^4 -
        18917112454422782400*J09*I09^2*I06*I03^4 +
        14051252261588151600*I09^3*I06*I03^4 -
        103119612401935353528000*J12*J09*I06^2*I03^4 -
        8561649822680153880000*J12*I09*I06^2*I03^4 -
        60221362772518373698560000*I15*I06^3*I03^4 +
        5156088637445728143128640000*J09*I06^4*I03^4 -
        370543229860968223231680000*I09*I06^4*I03^4 -
        32540250914983526400*I15^2*I03^5 + 6185792686959201600*J12*J09^2*I03^5 -
        703395592414358400*J12*J09*I09*I03^5 - 352247457555576000*J12*I09^2*I03^5
        + 23996761197622348492800*I15*J09*I06*I03^5 -
        777658837998638131200*I15*I09*I06*I03^5 -
        1719524779043857871580000*J09^2*I06^2*I03^5 +
        244439204772133949040000*J09*I09*I06^2*I03^5 +
        21631772834389317600*I09^2*I06^2*I03^5 +
        2481617073250781526240000*J12*I06^3*I03^5 -
        79955088428380498718079744000*I06^5*I03^5 +
        4481529977956147200*I15*J12*I03^6 + 18083062380700473120*J09^3*I03^6 -
        9639423782835452640*J09^2*I09*I03^6 - 538563172352758560*J09*I09^2*I03^6 -
        12226143419016480*I09^3*I03^6 - 912534347133167731200*J12*J09*I06*I03^6 +
        77391741898070668800*J12*I09*I06*I03^6 -
        733069439853150808166400*I15*I06^2*I03^6 +
        94051896726020932473868800*J09*I06^3*I03^6 -
        7092390937056646930041600*I09*I06^3*I03^6 +
        39475797366214287360*I15*J09*I03^7 - 1278283491000483840*I15*I09*I03^7 -
        5415177268972359054720*J09^2*I06*I03^7 +
        1478203124668458888960*J09*I09*I06*I03^7 +
        29433848152050967680*I09^2*I06*I03^7 +
        28901410555650973516800*J12*I06^2*I03^7 -
        1682191479799092665396793600*I06^4*I03^7 -
        1127160947822054400*J12*J09*I03^8 + 319385734086804480*J12*I09*I03^8 -
        2293145176516744642560*I15*I06*I03^8 +
        416710329944916109800960*J09*I06^2*I03^8 -
        53010194810628308590080*I09*I06^2*I03^8 - 3265042649062070016*J09^2*I03^9
        + 2592275733841927680*J09*I09*I03^9 + 103891355135218944*I09^2*I03^9 +
        60389900285622128640*J12*I06*I03^9 - 9473459346697536495912960*I06^3*I03^9
        - 2212009181969448960*I15*I03^10 + 527239199777544603648*J09*I06*I03^10
        - 170305342967625025536*I09*I06*I03^10 + 7436179772375040*J12*I03^11 -
        17788649424269858795520*I06^2*I03^11 - 34857679187976192*J09*I03^12 -
        196749351885643776*I09*I03^12 + 1063677688079155200*I06*I03^13 +
        24074171839938560*I03^15,
    I27,
    13286025*J12^2 - 1003045680*I15*J09 - 77157360*I15*I09 + 58364720505*J09^2*I06
        - 5603553270*J09*I09*I06 - 776395935*I09^2*I06 - 44003314800*J12*I06^2 +
        36434744654400*I06^4 + 92575710*J12*J09*I03 + 16796160*J12*I09*I03 +
        52775634240*I15*I06*I03 - 5855427173160*J09*I06^2*I03 +
        300837333960*I09*I06^2*I03 + 531834255*J09^2*I03^2 +
        22938876*J09*I09*I03^2 + 378918*I09^2*I03^2 - 6048979560*J12*I06*I03^2 +
        148460792671440*I06^3*I03^2 + 137168640*I15*I03^3 -
        68380380792*J09*I06*I03^3 - 596660256*I09*I06*I03^3 - 18837360*J12*I03^4 +
        2122728968880*I06^2*I03^4 - 136117872*J09*I03^5 - 4667616*I09*I03^5 +
        8042068800*I06*I03^6 + 9386560*I03^8,
    1102248000*J21 - 4233157200*J12*J09 - 249318000*J12*I09 -
        7870050720000*I15*I06 + 464228751312000*J09*I06^2 -
        81624361737600*I09*I06^2 + 7163255655*J09^2*I03 - 1133586090*J09*I09*I03 -
        47536065*I09^2*I03 + 1044600429600*J12*I06*I03 -
        22516130457273600*I06^3*I03 - 27468020160*I15*I03^2 +
        5262731160840*J09*I06*I03^2 - 311423755320*I09*I06*I03^2 +
        3218797440*J12*I03^3 - 330803613383760*I06^2*I03^3 + 14030218368*J09*I03^4
        - 171657216*I09*I03^4 - 1426451938560*I06*I03^5 - 1839011840*I03^7,
    3968092800*I21 + 24538140*J12*J09 - 165993300*J12*I09 - 2955435517440*I15*I06
        + 171755385400800*J09*I06^2 - 29477522190240*I09*I06^2 -
        968897295*J09^2*I03 + 334009494*J09*I09*I03 - 20933883*I09^2*I03 +
        367100547120*J12*I06*I03 - 8360086183286400*I06^3*I03 -
        12962436480*I15*I03^2 + 2300125199400*J09*I06*I03^2 -
        154941689160*I09*I06*I03^2 + 1617796800*J12*I03^3 -
        133524847632240*I06^2*I03^3 + 6574736448*J09*I03^4 - 70085376*I09*I03^4 -
        622640183040*I06*I03^5 - 879157760*I03^7,
    22044960*J18 - 3064635*J09^2 - 3815910*J09*I09 + 1289925*I09^2 -
        47239200*J12*I06 - 112240339200*I06^3 + 198404640*I15*I03 -
        11840038920*J09*I06*I03 + 2097274680*I09*I06*I03 - 32673780*J12*I03^2 +
        585714116880*I06^2*I03^2 - 86498514*J09*I03^3 - 483102*I09*I03^3 +
        6114498840*I06*I03^4 + 13438240*I03^6,
    7348320*I18 - 17721585*J09^2 + 7966350*J09*I09 - 847665*I09^2 -
        57736800*J12*I06 + 144992851200*I06^3 + 7348320*I15*I03 +
        1100022120*J09*I06*I03 - 498645720*I09*I06*I03 - 1443420*J12*I03^2 -
        1085276880*I06^2*I03^2 - 2388726*J09*I03^3 - 2446938*I09*I03^3 +
        354048840*I06*I03^4 + 1259360*I03^6,
    4860*J15 + 43740*I15 - 2566080*J09*I06 + 408240*I09*I06 - 7290*J12*I03 +
        127370880*I06^2*I03 - 18729*J09*I03^2 - 207*I09*I03^2 + 1333260*I06*I03^3
        + 2960*I03^5,
    486*I12 - 155520*I06^2 - 423*J09*I03 + 117*I09*I03 + 14418*I06*I03^2 + 8*I03^4
    ],
    [ w div 3 : w in [45, 27, 24, 21, 21, 18, 18, 15, 12]];

end function;

/* Equations for the stratum defined by (aka A3Stratum)

        (a02*Y^2)*Z^2+
        (a03*Y^3 + a12*X*Y^2 + a21*X^2*Y)*Z+
        a40*X^4 + a31*X^3*Y + a22*X^2*Y^2 + a13*X*Y^3 + a04*Y^4

 */
function CuspGenus1Stratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
        I27,
        22275*J21 - 106531200*I09*I06^2 - 11813526000*I06^3*I03 - 10606545*I09*I06*I03^2 +
        342211050*I06^2*I03^3 - 27528*I09*I03^4 + 5427800*I06*I03^5 + 9176*I03^7,
        4455*I21 + 194400*I09*I06^2 - 205254000*I06^3*I03 - 129600*I09*I06*I03^2 +
        3160800*I06^2*I03^3 - 384*I09*I03^4 + 64960*I06*I03^5 + 128*I03^7,
        2475*J18 + 14256000*I06^3 - 91170*I09*I06*I03 + 3731625*I06^2*I03^2 - 204*I09*I03^3 +
        41620*I06*I03^4 + 68*I03^6,
        27*I18 + 1296000*I06^3 - 2250*I09*I06*I03 + 126225*I06^2*I03^2 - 12*I09*I03^3 + 1540*I06*I03^4 + 4*I03^6,
        81*I09^2 + 19602000*I06^3 - 24030*I09*I06*I03 + 1455525*I06^2*I03^2 - 87*I09*I03^3 + 14720*I06*I03^4 + 20*I03^6,
        825*J15 - 8505*I09*I06 + 184950*I06^2*I03 - 24*I09*I03^2 + 840*I06*I03^3 + 8*I03^5,
        297*I15 - 6075*I09*I06 + 195750*I06^2*I03 - 120*I09*I03^2 + 5800*I06*I03^3 + 40*I03^5,
        33*J12 - 99000*I06^2 - 35*I09*I03 - 400*I06*I03^2 + 8*I03^4,
        165*I12 - 52800*I06^2 - 36*I09*I03 + 665*I06*I03^2 + 12*I03^4,
        495*J09 - 261*I09 - 14580*I06*I03 + 32*I03^3
        ],
        [ w div 3 : w in [ 27, 21, 21, 18, 18, 18, 15, 15, 12, 12, 9 ]];

end function;


/*
 * Locus of quartics with two cusps
 *********************************/

 /*
     Dimension 2 (vs 2)
  */
function TwoCuspsStratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
    486*I12 - 155520*I06^2 - 423*J09*I03 + 117*I09*I03 + 14418*I06*I03^2 +
        8*I03^4,
    4860*J15 + 43740*I15 - 2566080*J09*I06 + 408240*I09*I06 - 7290*J12*I03 +
        127370880*I06^2*I03 - 18729*J09*I03^2 - 207*I09*I03^2 +
        1333260*I06*I03^3 + 2960*I03^5,
    11858805*J09^2 - 9009630*J09*I09 + 1584765*I09^2 + 94478400*J12*I06 -
        251690457600*I06^3 - 117573120*I15*I03 + 5369493240*J09*I06*I03 -
        668376360*I09*I06*I03 + 18720720*J12*I03^2 - 300885885360*I06^2*I03^2 +
        52098408*J09*I03^3 + 264024*I09*I03^3 - 3618470880*I06*I03^4 -
        7945600*I03^6,
    7266672*I18 - 5436396*J09*I09 + 1503684*I09^2 + 82522800*J12*I06 -
        228560745600*I06^3 - 166480272*I15*I03 + 9022717440*J09*I06*I03 -
        1480816944*I09*I06*I03 + 26237682*J12*I03^2 - 445715693280*I06^2*I03^2 +
        74627685*J09*I03^3 - 2029581*I09*I03^3 - 4997180892*I06*I03^4 -
        10496464*I03^6,
    109000080*J18 - 30379860*J09*I09 + 8402940*I09^2 - 112849200*J12*I06 -
        876570595200*I06^3 + 830768400*I15*I03 - 51681395520*J09*I06*I03 +
        9515821680*I09*I06*I03 - 137632770*J12*I03^2 + 2511565613280*I06^2*I03^2
        - 361116909*J09*I03^3 - 2051307*I09*I03^3 + 25609198140*I06*I03^4 +
        56291920*I03^6,
    5016274515*J12*J09 - 1387480185*J12*I09 - 5163987790080*I15*I06 +
        264308571487800*J09*I06^2 - 37508072028840*I09*I06^2 -
        2034248013*J09*I09*I03 - 138646809*I09^2*I03 + 599194216260*J12*I06*I03
        - 13399838483292000*I06^3*I03 - 81039559104*I15*I03^2 +
        6405539575500*J09*I06*I03^2 - 417238369056*I09*I06*I03^2 +
        12424524552*J12*I03^3 - 368998351012080*I06^2*I03^3 +
        35291701260*J09*I03^4 + 1343156868*I09*I03^4 - 2846826546768*I06*I03^5 -
        5669315264*I03^7,
    10835152952400*I21 - 434723461920*J12*I09 - 8001045796322880*I15*I06 +
        465459599946474000*J09*I06^2 - 79989420714217200*I09*I06^2 -
        1070796492504*J09*I09*I03 + 298243818288*I09^2*I03 +
        1015467682842180*J12*I06*I03 - 22704963237225770400*I06^3*I03 -
        60542363580048*I15*I03^2 + 7392999539718180*J09*I06*I03^2 -
        566617423909752*I09*I06*I03^2 + 8428051357074*J12*I03^3 -
        426796273565343000*I06^2*I03^3 + 29104277966145*J09*I03^4 -
        150411262329*I09*I03^4 - 2469399931305036*I06*I03^5 -
        4097499929968*I03^7,
    66883660200*J21 - 86176241820*J12*I09 - 741978295904160*I15*I06 +
        41703362422394400*J09*I06^2 - 6873562280653920*I09*I06^2 +
        157278859110*J09*I09*I03 - 68070539430*I09^2*I03 +
        90605270603700*J12*I06*I03 - 2043195090699261600*I06^3*I03 -
        1507066173144*I15*I03^2 + 450534892742820*J09*I06*I03^2 -
        15764196926736*I09*I06*I03^2 + 145357315722*J12*I03^3 -
        27939608700040440*I06^2*I03^3 + 748937237085*J09*I03^4 +
        48684828843*I09*I03^4 - 99703699670428*I06*I03^5 - 110664374704*I03^7,
    1414589413230*I15*J09 - 391269412170*I15*I09 - 26303544749160*J09*I09*I06 +
        7434370664280*I09^2*I06 + 610420679062200*J12*I06^2 -
        1633181868134856000*I06^4 - 7410059010*J12*I09*I03 -
        1035838809051480*I15*I06*I03 + 52890859352731950*J09*I06^2*I03 -
        7412091906084930*I09*I06^2*I03 - 406738782693*J09*I09*I03^2 +
        91272570741*I09^2*I03^2 + 160523929808820*J12*I06*I03^2 -
        2684430357952015800*I06^3*I03^2 - 9901779170976*I15*I03^3 +
        975359250335160*J09*I06*I03^3 - 65651634112104*I09*I06*I03^3 +
        1560328239438*J12*I03^4 - 57421131284843640*I06^2*I03^4 +
        4462130746215*J09*I03^5 + 36550316817*I09*I03^5 -
        375000039164052*I06*I03^6 - 676148099216*I03^8,
    19096957078605*J12^2 - 509685594880896*I15*I09 +
        28873146731284800*J09*I09*I06 - 4749835969315584*I09^2*I06 -
        109469394559450800*J12*I06^2 + 168345093648041352000*I06^4 +
        53395403214258*J12*I09*I03 - 11146467644887680*I15*I06*I03 +
        493698749347440000*J09*I06^2*I03 - 1398778148404410480*I09*I06^2*I03 +
        253165333211280*J09*I09*I03^2 - 4909782020283*I09^2*I03^2 +
        491875031217600*J12*I06*I03^2 - 22365656784244785600*I06^3*I03^2 -
        165999982538880*I15*I03^3 + 11195191057615200*J09*I06*I03^3 -
        15484585991200992*I09*I06*I03^3 + 26850350396160*J12*I03^4 -
        690522578576124480*I06^2*I03^4 + 57602707882200*J09*I03^5 -
        22106213003016*I09*I03^5 - 5660222032657440*I06*I03^6 -
        13059270390080*I03^8,
    10770683792333220*I15*J12 - 151881756510267*J09*I09^2 + 73381073370129*I09^3
        - 79778147673225960*J12*I09*I06 - 629250359184417045600*I15*I06^2 +
        32299174339473380220000*J09*I06^3 - 4582659441380614927200*I09*I06^3 -
        46514336460887484*I15*I09*I03 + 2405710642261280130*J09*I09*I06*I03 -
        440948011127328306*I09^2*I06*I03 + 94278699557465744700*J12*I06^2*I03 -
        1623110991475759161876000*I06^4*I03 + 3498576862914522*J12*I09*I03^2 -
        15995731720502293200*I15*I06*I03^2 +
        1089329587357580607825*J09*I06^2*I03^2 -
        217840582090191649455*I09*I06^2*I03^2 + 21184910145759330*J09*I09*I03^3
        - 518174234490852*I09^2*I03^3 + 2507770022804953560*J12*I06*I03^3 -
        60396878853066835678500*I06^3*I03^3 - 95614439234181840*I15*I03^4 +
        11694848707309326750*J09*I06*I03^4 - 1699090889973328098*I09*I06*I03^4 +
        15588817335593730*J12*I03^5 - 776557041039643091040*I06^2*I03^5 +
        40375453648522725*J09*I03^6 - 846434683858869*I09*I03^6 -
        4030533015952163580*I06*I03^7 - 6793578478667440*I03^9,
    I27,
    2429866263550374432*I15^2 + 265174889720058*J12*I09^2 -
        34748517548916400320*I15*I09*I06 - 1539952197359104418400*J09*I09*I06^2
        + 578773077611602168080*I09^2*I06^2 + 56780451228875501700000*J12*I06^3
        - 152564855000364512448480000*I06^5 - 9654574035193911*J09*I09^2*I03 +
        4377544971576471*I09^3*I03 - 1588416396152914800*J12*I09*I06*I03 -
        110766126632888020492800*I15*I06^2*I03 +
        6002252759076947231940000*J09*I06^3*I03 -
        888534292065883494580800*I09*I06^3*I03 -
        2339191635959037888*I15*I09*I03^2 + 55040239478638250730*J09*I09*I06*I0\
        3^2 - 2814737263780643514*I09^2*I06*I03^2 +
        18607604461942719268350*J12*I06^2*I03^2 -
        305467128882411945967242000*I06^4*I03^2 +
        169634904656783796*J12*I09*I03^3 - 2191747411715217340320*I15*I06*I03^3
        + 168683112192897695800125*J09*I06^2*I03^3 -
        21082822950433761590985*I09*I06^2*I03^3 +
        606549123954324198*J09*I09*I03^4 + 64561104620264898*I09^2*I03^4 +
        356019640769948461560*J12*I06*I03^4 -
        9470392253507444841056700*I06^3*I03^4 - 10783366621599148416*I15*I03^5 +
        1570526483062205847870*J09*I06*I03^5 -
        122317427745485456202*I09*I06*I03^5 + 1749890134934379882*J12*I03^6 -
        105855008329255717356480*I06^2*I03^6 + 4842682965513487845*J09*I03^7 -
        39923615254309677*I09*I03^7 - 491078297276149035420*I06*I03^8 -
        755167475991968048*I03^10
        ],
        [ 4, 5, 6, 6, 6, 7, 7, 7, 8, 8, 9, 9, 10 ];

end function;

/*
	Dimension 0 (vs 0)
 */
function ThreeCuspStratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return
        [
        I27,
        104976*J21 - 23653224*I06*I03^5 - 218659*I03^7,
        52488*I21 - 721476*I06*I03^5 - 7105*I03^7,
        58320*J18 - 764352*I06*I03^4 - 8719*I03^6,
        34992*I18 - 1422720*I06*I03^4 - 13705*I03^6,
        2160*J15 - 13104*I06*I03^3 - 133*I03^5,
        3888*I15 - 113040*I06*I03^3 - 1087*I03^5,
        54*J12 - 5490*I06*I03^2 - 43*I03^4,
        243*I12 - 5301*I06*I03^2 - 22*I03^4,
        19440*I06^2 + 72*I06*I03^2 - I03^4,
        27*J09 - 2169*I06*I03 - 10*I03^3,
        27*I09 - 1935*I06*I03 - 26*I03^3
        ], [ w div 3 : w in [ 27, 21, 21, 18, 18, 15, 15, 12, 12, 12, 9, 9 ]];

end function;

/*
	Dimension 0 (vs 0)
 */
function A2p3Stratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
        108*I06 + I03^2,
        324*I09 - 97*I03^3,
        324*J09 + 121*I03^3,
        2916*I12 + 325*I03^4,
        324*J12 + 47*I03^4,
        11664*I15 - 121*I03^5,
        1296*J15 - 7*I03^5,
        104976*I18 - 1595*I03^6,
        34992*J18 - 985*I03^6,
        78732*I21 - 637*I03^7,
        314928*J21 + 1057*I03^7,
        I27
        ],
        [ 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 9 ];

end function;



/*
 * Invariant stuff for quartics without cusp, and at least one node
 ********************************************************************/


 /* Up to some linear change of variables, quartics with a node
    can be rewritten modulo p as

    f := a11*x*y*z^2 +
    	( a03*y^3 + a30*x^3 ) * z +
    	a40*x^4  + a31*x^3*y + a22*x^2*y^2 + a13*x*y^3  + a04*y^4;

    The subgroup of GL(3) that stabilize them corresponds to x,y,z diagonal scaling
    and permutations of x,y,z

    Invariants for this action are generated by

    j3, k3, j6, k6, j9, k9, j12, k12, j15 := Explode(
    [
    a03*a11*a30,
    a11^2*a22,
    a11^4*a13*a31,
    a04*a11^4*a40,
    a03^2*a11^5*a31*a40 + a04*a11^5*a13*a30^2,
    a04*a11^6*a31^2 + a11^6*a13^2*a40,
    a03^2*a11^7*a31^3 + a11^7*a13^3*a30^2,
    a03^2*a11^7*a13*a40^2 + a04^2*a11^7*a30^2*a31,
    a03^4*a11^8*a40^3 + a04^3*a11^8*a30^4
    ]
    );

    We call these invariants "Node Dihedral Invariants".

    And relations are
	[
	    j15*j12 - j9^3 - k12*k9*j3^2 + 4*j9*k6*j6*j3^2,
	    k12^2 - j15*k9 + j9^2*k6 - 4*k6^2*j6*j3^2,
	    k12*j12 - j9^2*j6 - k9^2*j3^2 + 4*k6*j6^2*j3^2,
	    k12*j9 - j15*j6 - k9*k6*j3^2,
	    k9*j9 - j12*k6 - k12*j6
	];


*/

/* Locus of quartics without a cusp that degenerates to an elliptic curve

   A1^2 stratum ? Dim 4 thus ?
*/
function NodeGenus1Stratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return
        [
        -2564110596556360754342391488703200287590567678663720960000000*J21*I15*I06 + 550016028414934593726344585516228034187925508570975436800000*J21*I15*I03^2 -
        2354804485133369014865228815880691424362163687190446080000*J21*J12*J09 - 1518800788941933146428750649624603780977772571650457600000*J21*J12*I09 +
        9186015342436401466117465735397391883628221864657210859520000*J21*J12*I06*I03 + 20133592311692841175819053994122430511014769768109020160000*J21*J12*I03^3 -
        3602929569377161479108012371627681139517242230602407936000*J21*I12*J09 + 10015270567765438754806737009534400906644725206547546112000*J21*I12*I09 -
        24782023219823288877838635509814372252104328703473213050880000*J21*I12*I06*I03 - 21408733724217870506197502079783804910665967579857738240000*J21*I12*I03^3 -
        6729227110593270296816725730139747029926679387142545393664000*J21*J09^2*I03 + 2080221159550372862209534341828497225606760337998304069632000*J21*J09*I09*I03 +
        3748848170582035909800738852369360905599080208775756643778560000*J21*J09*I06^2 + 351162654928081451549573692416523999027999438207617067226112000*J21*J09*I06*I03^2 +
        174887450072640426148725921698062509795130187082947493888000*J21*J09*I03^4 - 27622644721676303328845166144645466513233146150051155968000*J21*I09^2*I03 -
        1253780195139269829368057674745943548640530840040494766735360000*J21*I09*I06^2 - 64364433794384606048000932032887682054068396931131042233344000*J21*I09*I06*I03^2 -
        73648782612060258038009701090710519105322551749955081216000*J21*I09*I03^4 - 62555468809597809551689016184990590276804285235383894938091520000*J21*I06^3*I03 -
        4083028878263611441266587530351910123954316998322986878894080000*J21*I06^2*I03^3 - 4216865973672127755659712263995577717158944781860370229760000*J21*I06*I03^5 -
        1018963421174226810474451553611665087790097791677696000000*J21*I03^7 - 196175945095762825369665513714792253452380257749722726400000*I21*I18*I03 -
        14321608737333864812100947067143981912245153398764077056000000*I21*J15*I06 + 391628322611851438918886622054964232241229974888549580800000*I21*J15*I03^2 +
        4014032819123529287345946083957246110539573203183861760000000*I21*I15*I06 - 2166031690835221629156539404600611644196339182815061606400000*I21*I15*I03^2 +
        20783260500758341735862130154513719448722667259585495040000*I21*J12*J09 + 10177654859281017116566955718473671084665614342415974400000*I21*J12*I09 -
        51955039846133670690981683737733956718115275065437702389760000*I21*J12*I06*I03 - 351736920773333289179771016395944398473410093284681768960000*I21*J12*I03^3 +
        41489967968094827681690418417315552092546625864699936768000*I21*I12*J09 - 70008704161960776584525368015426563091808191843408674816000*I21*I12*I09 +
        102199612377372948145545927239186801626103279075314204508160000*I21*I12*I06*I03 + 93039832849344061550040956252707801466134361255148810240000*I21*I12*I03^3 +
        47857950084713095181918486970948299467589656473775081439232000*I21*J09^2*I03 - 13905885378639291360749808005065053454063747173205494644736000*I21*J09*I09*I03 -
        25496948697237404732624796310988083799864608302698721000161280000*I21*J09*I06^2 - 2557404286129193661478905149790288688211199614486707987931136000*I21*J09*I06*I03^2 -
        1118368474046848926184137387584161726518470694341522915328000*I21*J09*I03^4 + 447508547687854474666226810359858227114695942934197796864000*I21*I09^2*I03 +
        6778790424857036760816757272363576922785444838708330465198080000*I21*I09*I06^2 + 438099572526986188680606739894157236352514078474231769178112000*I21*I09*I06*I03^2 +
        515004958872683177918328815098334495993839365529611165696000*I21*I09*I03^4 + 420571714091878887495912990092048326768918439262014872627445760000*I21*I06^3*I03 +
        31400512243781552159368853892115179303527157527510780136652800000*I21*I06^2*I03^3 + 29155864497894370594016807486362362089671085042421422223360000*I21*I06*I03^5 +
        8036027469752739196367382050279229190340640698706739200000*I21*I03^7 - 162545783079346341020579997077970724289115070706913116160000*J18*I15*J09 +
        72865351035569049423018619379779979853741238592754155520000*J18*I15*I09 - 85494498367964393788943717754540520335950849005365630074880000*J18*I15*I06*I03 -
        6116976040067821004541287638342286770825741932446398218240000*J18*I15*I03^3 - 4138086341863747097641381929921399096261146061908213760000*J18*J12^2 -
        20040160998454432372863263917762204194750407356955492352000*J18*J12*I12 - 10461049681882663396986954657889274338695080658228167417856000*J18*J12*J09*I03 -
        199024366172940033181331927075655711546367271354157121536000*J18*J12*I09*I03 + 10219872102741660079432121257204059336490631803112623775416320000*J18*J12*I06^2 +
        359317873025587021900065764047726093621544570859085935513600000*J18*J12*I06*I03^2 + 550910496794962617545645293614891564021226726982314126848000*J18*J12*I03^4 +
        359658818627129104886430966594882744309325894866422464512000*J18*I12^2 + 81608292987926733692399622400451466520687424070393062043648000*J18*I12*J09*I03 -
        3474258290048772330248313970049684144525903125934003232768000*J18*I12*I09*I03 - 56810245628470702741906076823495458774631768865942300273410048000*J18*I12*I06^2 -
        2849318168477021789543960674778835200294870670157552722057216000*J18*I12*I06*I03^2 - 2517225612081213682973527997715608010506186252806359389952000*J18*I12*I03^4 +
        68773705176871468673180044122715521200151299756609942126592000*J18*J09^2*I06 + 10275614126834457611030586057150407456287368396681152138649600*J18*J09^2*I03^2 -
        53168810410489189807754609280148109271227228799226533642240000*J18*J09*I09*I06 - 936132777848216073732224209652121064237653603112711325491200*J18*J09*I09*I03^2 -
        20156406948462567448074687953449604276173297815782282892091392000*J18*J09*I06^2*I03 - 329129827567563397804454502780325300225426067414513845181337600*J18*J09*I06*I03^3 -
        250161211880568958453782652894494327185500633809430434201600*J18*J09*I03^5 + 10699072982766260960822429578912141379549768061785027837952000*J18*I09^2*I06 -
        762339403918869177473457649066851200017836774319820666880000*J18*I09^2*I03^2 + 7258021631877263123769393312861590258621278750363765451415552000*J18*I09*I06^2*I03 -
        26245295980706271917661648607066687928680624162966412838604800*J18*I09*I06*I03^3 + 62385162294950506930691335639058787981439806208014511411200*J18*I09*I03^5 +
        2389144563483302634468336901623790218640787434226364589528842240000*J18*I06^4 + 403421241772170800557804898161706309187982627859070896670965760000*J18*I06^3*I03^2 -
        673469445630430708149878877878425747450639672622289440538624000*J18*I06^2*I03^4 + 5623092686068486206093139324279054837424872306450711433472000*J18*I06*I03^6 +
        13966287459815879618132269411790205937647620453088015360000*J18*I03^8 + 392351890191525650739331027429584506904760515499445452800000*I18^2*I06 +
        2724665904107817019023132134927670186838614690968371200000*I18^2*I03^2 - 9514268377070942382243246598371206456888678534170835681280000*I18*I15*I06*I03 +
        578478426722128894779556230637304033728341099224289116160000*I18*I15*I03^3 + 985258652824701689914614745219380737205034776644812800000*I18*J12^2 +
        13892147004828293827796067907593268394590990350691860480000*I18*J12*I12 + 2966542088122344755737402634900779878451294417698994618368000*I18*J12*J09*I03 +
        66544683593936836768779353663605148057745935949874987008000*I18*J12*I09*I03 - 2130118728559855089094613232491583278273561780851720794931200000*I18*J12*I06^2 -
        104776529211775414587035220290788626714588159691602393587712000*I18*J12*I06*I03^2 - 150440190408740526437340095672782663274791883897194447872000*I18*J12*I03^4 -
        58642595016126244583717869635457541478443669905899257856000*I18*I12^2 - 11737387261571062040402765695259921901881370800342031738470400*I18*I12*J09*I03 +
        307768436614783219115747348434665729944347091647678532812800*I18*I12*I09*I03 + 7338120506908564704115094796499143641410557410812017353687040000*I18*I12*I06^2 +
        401792323171114834817782435507481630398373373438564220538880000*I18*I12*I06*I03^2 + 362480175683706518050588309417602407186043270081419401728000*I18*I12*I03^4 -
        8508347828705128977358642888312633578575254955851885117440000*I18*J09^2*I06 - 962158129439624230274366495294163719246728877471618183577600*I18*J09^2*I03^2 +
        5605642914522574635877351978823375874564261345787091877888000*I18*J09*I09*I06 - 530354542188024253624083051206059485877010863681635325132800*I18*J09*I09*I03^2 +
        7409541646509348802971214398388351070645043634277511428358144000*I18*J09*I06^2*I03 + 45529440078212402817000774683583948908975410595742979274956800*I18*J09*I06*I03^3 +
        54404149298908811716868629511005026390112305777695506022400*I18*J09*I03^5 - 812419283048309748545850669965389243699152120509693362176000*I18*I09^2*I06 +
        49852660391806695085098624600443645305353445603615617024000*I18*I09^2*I03^2 - 990388882542341076472522002781344767768865005521501813358592000*I18*I09*I06^2*I03 +
        20282100842470427567483149460003489103023281795389441835622400*I18*I09*I06*I03^3 + 18690937011055039189989481228897399783020484245986152243200*I18*I09*I03^5 -
        2473231122978113766554440323206825598301058279149178478762393600000*I18*I06^4 - 216653058459212368812331077201248862468360555542066769259266048000*I18*I06^3*I03^2 -
        348138989727000689649711151598561619946304973481309442015232000*I18*I06^2*I03^4 - 278007766416991581584529483312622778610741269681549342208000*I18*I06*I03^6 +
        539008094483181305342758589471906236884430433768540160000*I18*I03^8 - 117705567057457695221799308228875352071428154649833635840000*J15*I15*I12 -
        12001662276645219248073135883871710859987763359317374271488000*J15*I15*J09*I03 - 1056863126730261867136606736674935117955625488963784933376000*J15*I15*I09*I03 +
        8996235212956334689514515571779246476849854442466679822745600000*J15*I15*I06^2 + 754907262342610938418968401522432758475008686993227428921344000*J15*I15*I06*I03^2 +
        7088674002290517285509095832420213437181949248294649987072000*J15*I15*I03^4 + 167473218953758192247698960359932014955586862391215718400000*J15*J12^2*I03 -
        1685192720268333042712549156586842786167361347294272716800000*J15*J12*I12*I03 + 516967578401024553191135497067566003099862954918138413056000*J15*J12*J09*I06 +
        11431146211197364575387199699259144364833125285553419748966400*J15*J12*J09*I03^2 + 528074115312625018844858095142468362732525944700998451200000*J15*J12*I09*I06 -
        96853037519011581096860788082250430241181380414678301081600*J15*J12*I09*I03^2 - 8284858465808849083476928193227377421758109569899529320792064000*J15*J12*I06^2*I03 -
        388652735804666716725046066904590931618612415694670650095206400*J15*J12*I06*I03^3 - 561910253779290417538455267185127311276633326870310702592000*J15*J12*I03^5 +
        4777971848756685298240694544530472253421390138709011202048000*J15*I12^2*I03 + 47060381432644443899655198364890621779978264581120685093683200*J15*I12*J09*I06 -
        80960800420661832263647704706791517424547687651668168153333760*J15*I12*J09*I03^2 - 5468473103330684602340897335852650593932121677275163321958400*J15*I12*I09*I06 +
        5437938678460199691037496051197086032657349100356215366123520*J15*I12*I09*I03^2 + 41924165088009292948811080711967338632727958220079368342994944000*J15*I12*I06^2*I03 +
        2740139019278611743513127315564725978167735029764223191865344000*J15*I12*I06*I03^3 + 2117484795795680966137535064270374219188737491373993699072000*J15*I12*I03^5 -
        1881582732876598459570407315379887239690524095924535296000*J15*J09^3 + 7353193460231756947855056332832545416567113598944686899200*J15*J09^2*I09 -
        1500473883146986344440029178902922367494265688544888645143756800*J15*J09^2*I06*I03 - 9682695080695861288913551235939550568588627940677656915271680*J15*J09^2*I03^3 +
        2895368385433428983691136937095281523782297424067611852800*J15*J09*I09^2 + 440740741503472722240219676301504589485614571024695809864499200*J15*J09*I09*I06*I03 +
        479183507691873887976250120191014612162328313009189078302720*J15*J09*I09*I03^3 + 842158090347718134949706611050935195771985984397656207870394368000*J15*J09*I06^3 +
        93007453602546494419856325089693622912425858473784699648070451200*J15*J09*I06^2*I03^2 + 335741515167731132751593446704295888684998418688187270687805440*J15*J09*I06*I03^4 +
        319741895373894454568130575986670693173688782472522774323200*J15*J09*I03^6 + 263820010930368121868234017880057565328042432760237260800*J15*I09^3 -
        13604027253726647961970060757587352053697961625065549860044800*J15*I09^2*I06*I03 + 963059594419624878894334964560381687566401495987442833940480*J15*I09^2*I03^3 -
        301185051460139844743354327922335572433905619431868567404412928000*J15*I09*I06^3 - 18705758994950988613062475788733046971991143689791520527710617600*J15*I09*I06^2*I03^2 +
        27376978096255541773315037410719652972972997543562882791608320*J15*I09*I06*I03^4 - 88611312352584688435002177536956122683476799378270859571200*J15*I09*I03^6 -
        17057115108167145097867728448387317244679467809950403340718309376000*J15*I06^4*I03 - 1183660356411420373099483139645940378630994219207456778285206732800*J15*I06^3*I03^3 +
        487924851952684273688521559117461767547916697369694733962444800*J15*I06^2*I03^5 - 7407349960759157191891158745205922449015022572001939068774400*J15*I06*I03^7 -
        14362611599533525667487878486166017408933544830077449216000*J15*I03^9 + 188328907291932312354878893166200563314285047439733817344000*I15^2*J09*I03 -
        94164453645966156177439446583100281657142523719866908672000*I15^2*I09*I03 - 55384788885617392293795656155989126211956261859136372736000000*I15^2*I06^2 +
        22520392060672312959911964326314610894986394293695876169728000*I15^2*I06*I03^2 - 1542367889477421430818743565988085891958379163541717712896000*I15^2*I03^4 +
        6184847743369648619923969125584165449220170179769466880000*I15*J12^2*I03 - 30489376884854280444589787393654709966371708428534185984000*I15*J12*I12*I03 +
        6735482087483133189565425305319901454543568982812185198592000*I15*J12*J09*I06 - 5361903546664911591684148677008756726980686534001423053619200*I15*J12*J09*I03^2 +
        2090689528306417018403615204757500792763919745589678243840000*I15*J12*I09*I06 + 28714726073810582197059867564960891921857524802352164044800*I15*J12*I09*I03^2 +
        2728028997108999156954182573406403488494110802061226222190592000*I15*J12*I06^2*I03 + 52621399809803737492258222353607921865634107198555190502195200*I15*J12*I06*I03^3 -
        45924534579811920707019435228658827678790167510869323776000*I15*J12*I03^5 - 307735153667163726496925669509753019406706924478385881088000*I15*I12^2*I03 +
        12550895167450047001107184861132900046830143860778507789926400*I15*I12*J09*I06 + 23343472695857978653138352876203152792303995557016311369236480*I15*I12*J09*I03^2 -
        13049256149916492114945423027986487136451204187381911145676800*I15*I12*I09*I06 - 1682548814272010106874042077249447776661089994348705852456960*I15*I12*I09*I03^2 -
        10716905903658826039941001921547877972136514284375320697356288000*I15*I12*I06^2*I03 - 285553875631768774761535004744669073535935695620892455753728000*I15*I12*I06*I03^3 +
        1704164672032255315188811263665203663539672911025999286272000*I15*I12*I03^5 + 27702918943145510441943632449192491639405416717979353088000*I15*J09^3 +
        21747614243799640401485291271227391012326732624880952934400*I15*J09^2*I09 - 428853835142095316757764087024042803109071315722858740480409600*I15*J09^2*I06*I03 +
        3096598984450197916648769250524605445494396128230790477987840*I15*J09^2*I03^3 - 26154457251517236682320048667761410076347696506418390630400*I15*J09*I09^2 +
        338929956587676573231664289545124248218864034366410608281190400*I15*J09*I09*I06*I03 + 2125687113169764115298424316246945916189141534495576141783040*I15*J09*I09*I03^3 +
        215523178473623230598982966851988344209563515881807326730715136000*I15*J09*I06^3 + 15276221019174358688848874231049434939215713923487042310149734400*I15*J09*I06^2*I03^2 -
        64398755130902169598665434527720623902260187797021753366609920*I15*J09*I06*I03^4 - 274452397553452162007619191526036786002303654117660229427200*I15*J09*I03^6 +
        4702931478422027003500208657375132223342506554785438105600*I15*I09^3 - 7706749581828174881164972523783355921674307217514461043097600*I15*I09^2*I06*I03 -
        663291080969175406748364624095977569272507338923727630295040*I15*I09^2*I03^3 - 173731174957992876686711670386900354519156982325463582462509056000*I15*I09*I06^3 -
        12149363796595270200154573642393645020098151697480119182148403200*I15*I09*I06^2*I03^2 - 88381495296783370351421924286736180401676172919847617927413760*I15*I09*I06*I03^4 +
        138542356008268869853412262499034249075913522289269735628800*I15*I09*I03^6 - 1742317112197129987817744879941840700955462470157249600620593152000*I15*I06^4*I03 -
        53947325997210211077766171326203048606093545273248968204196249600*I15*I06^3*I03^3 - 92405148119172760959552792805848325290864215429944160517734400*I15*I06^2*I03^5 +
        5166409010000422232637417856166847913591605336641769214771200*I15*I06*I03^7 - 435402892814089114254873798680397542591855064345280512000*I15*I03^9 +
        137142798314900412967260309606382172731781315949153484800000*J12^3*I06 - 115791491252892989237968702386641098909338233843453165568000*J12^3*I03^2 +
        2856083464312748551229531119658001047612979510936781455360000*J12^2*I12*I06 + 1265998394950869078422749880861729644607077947460986519552000*J12^2*I12*I03^2 +
        7079316609597383179993161905657559605581090460906840064000*J12^2*J09^2 + 8192984234888655720398476603520250252046488337176133632000*J12^2*J09*I09 -
        116461649360097009306915546288282936835118516374179080687616000*J12^2*J09*I06*I03 - 680583199648177910574409272556440910877807132609636438937600*J12^2*J09*I03^3 -
        104798231876133094148911091068884584876292899740286976000*J12^2*I09^2 - 6861337170100349714953743544468534141946320833959228891136000*J12^2*I09*I06*I03 +
        151789928827147846890636798309099232478096359177981289472000*J12^2*I09*I03^3 + 63573851350608801869781676036697566972164957874438617327206400000*J12^2*I06^3 +
        3062895407243842046277388965268713588199547903433760279732224000*J12^2*I06^2*I03^2 + 26132047126117129844756551875586628917879510979273143503974400*J12^2*I06*I03^4 +
        21165905832156073851797781486372587148922905139900476096000*J12^2*I03^6 - 23066027347373831091287428706385512120587495220789106180096000*J12*I12^2*I06 -
        4705605003644123272315199180635391813109975982686922309632000*J12*I12^2*I03^2 - 35825572568720406361292564926564164957708465178282001203200*J12*I12*J09^2 -
        37882043498534879447237002749827682336984768124742801817600*J12*I12*J09*I09 + 1359838871604604573850135015436186591316850114397535220869939200*J12*I12*J09*I06*I03 +
        8969220173971376615664765005303876123275985038400501553653760*J12*I12*J09*I03^3 - 2229351567893597900028651934971550207024509003980587008000*J12*I12*I09^2 +
        25902972980475670778169127813398615596083277298048385427865600*J12*I12*I09*I06*I03 - 1157913101286688227448045154407942385000499413955278712606720*J12*I12*I09*I03^3 -
        942025787328539113555438977319637006264822632013056221558865920000*J12*I12*I06^3 - 45853405396634019356263773606455136696747622410121388850819072000*J12*I12*I06^2*I03^2 -
        346284258462956912226764114523798712911105667197833823865497600*J12*I12*I06*I03^4 - 318060754097753149863043878494569092381066768596241611232000*J12*I12*I03^6 +
        20433584831211328882507545950575707695343451437872893495910400*J12*J09^3*I03 - 3643674765346448791741461717541827734209590415434047400960000*J12*J09^2*I09*I03 -
        10741331319571779167186239429248287917686399980459245005889536000*J12*J09^2*I06^2 - 709365770616527838617216442848359283867386271220125218102579200*J12*J09^2*I06*I03^2 -
        214776450331846343002911175717971624473667410487796758681600*J12*J09^2*I03^4 - 639154482226545327103228118158080802706413694736201250406400*J12*J09*I09^2*I03 +
        928290992066533055016930914481088931694013553590466296307712000*J12*J09*I09*I06^2 - 75333631560983145023514621386229737791825966906484124170956800*J12*J09*I09*I06*I03^2 +
        403117272225605508260729807651689163720860296543181668464640*J12*J09*I09*I03^4 - 94875378568138314716501414947328237028007916343411232105709568000*J12*J09*I06^3*I03 -
        3157485849268459713647245139648445726703956079136598310351257600*J12*J09*I06^2*I03^3 - 1282692519888980530400196507278852736066234662922903470891520*J12*J09*I06*I03^5 -
        15215688377466119906659310264197310291137968387324477331200*J12*J09*I03^7 - 30838358852576686148318548148700703307611877282466228633600*J12*I09^3*I03 +
        848371475696968270710981408591106431755410054408370239291392000*J12*I09^2*I06^2 + 22582510822348638862963162323952927413121093864465510462464000*J12*I09^2*I06*I03^2 -
        64325909221568930313887943620915353618226367670723623137280*J12*I09^2*I03^4 + 164516772853341107786748303426025918887338825029406291270418432000*J12*I09*I06^3*I03 +
        5576572773972646233876398576331182263472438438065123496370585600*J12*I09*I06^2*I03^3 - 4861027016124296584870652227240771556096949202458122675458560*J12*I09*I06*I03^5 -
        2879091520968239144672712421778049075477730847233212844800*J12*I09*I03^7 + 12955920718867788622206176347215977243798081169939342379764940800000*J12*I06^5 +
        4224646368942673672319213972767662921228979261451113931916312576000*J12*I06^4*I03^2 + 101981873129558535447574006231920388517093352037062398673012326400*J12*I06^3*I03^4 -
        188625532158064307703248053463942051253765312888584064504115200*J12*I06^2*I03^6 + 321935546326932280713923632874127756228968119320174298118400*J12*I06*I03^8 +
        489940001459747456820753593247712915397382372906170496000*J12*I03^10 + 12150791636636584415768598438921765388840367797472624246784000*I12^3*I06 +
        5021930527670845259057261609819314807829250898131994165248000*I12^3*I03^2 + 68775149530248992352822940224469490486665213569108128563200*I12^2*J09^2 -
        45521604299025778655441218344977668579384902483304297267200*I12^2*J09*I09 - 4715782324895086451251876007833658669187968715815220684462489600*I12^2*J09*I06*I03 -
        29731585926362867317340873575905154948145688408152370923888640*I12^2*J09*I03^3 + 24892847323812603943880426376434513494770586204435945881600*I12^2*I09^2 +
        161104080749051630275806685835015410231919546400648653173555200*I12^2*I09*I06*I03 + 3326595093598891659798028586023573396707573401158737414881280*I12^2*I09*I03^3 +
        3107216924100086626942185881169151927613719391829192514895609856000*I12^2*I06^3 + 175001878493648503538285074410118539102668911608189744778567680000*I12^2*I06^2*I03^2 +
        1140023865264710202764377011110996208091962791238426647321088000*I12^2*I06*I03^4 + 734945498778193625326161123371963493366724899447750689472000*I12^2*I03^6 -
        29305844395767951940130870255756982678962021060836747373813760*I12*J09^3*I03 - 10472754364583268074331600165776593149088608805350682119413760*I12*J09^2*I09*I03 +
        11165726398393193793282304180190580418289860281017847221020262400*I12*J09^2*I06^2 + 308927789270219233575838643301080209115085828645651259778641920*I12*J09^2*I06*I03^2 -
        1595265416773061672051139444915897533071740101218342182461952*I12*J09^2*I03^4 + 6977209305747517168430221280783444572731054657527398525992960*I12*J09*I09^2*I03 +
        11341476254709777902817955878310221581092865389715674374261964800*I12*J09*I09*I06^2 + 1174273671040767649704108358185665625024186654811879555453931520*I12*J09*I09*I06*I03^2 -
        2012535424555682572292971504982605975803726061378511111327232*I12*J09*I09*I03^4 + 1359766406519997266882099589406517934423147608980510146442120396800*I12*J09*I06^3*I03 +
        27786145499333564845477742265241221016582093605609566716595159040*I12*J09*I06^2*I03^3 + 45517371686312079319204344511246093656195551119023468903475200*I12*J09*I06*I03^5 +
        124058940378952793048056435535281412402422800210287241801600*I12*J09*I03^7 - 209558583857409714660262244873721003899611690362467217408000*I12*I09^3*I03 -
        4884048418995664086230110125446743128678189390354767089906483200*I12*I09^2*I06^2 - 222479312653366847116458069857160650461966841972966781413253120*I12*I09^2*I06*I03^2 +
        416939696297093131890692010794706165717615759780995569923072*I12*I09^2*I03^4 - 872387882136633375562986667372208567041902759009151014302456217600*I12*I09*I06^3*I03 -
        23837702165899502263434468485347106036385179213119539637705850880*I12*I09*I06^2*I03^3 + 70517322269913172593181759170081197785533785262446224749158400*I12*I09*I06*I03^5 +
        15882928379490054906334003869506302491366890127855723945600*I12*I09*I03^7 - 149777503486961546222822848289887841128692811210984780916525629440000*I12*I06^5 -
        27585891312196121118004685894564012826654501563855399683463577600000*I12*I06^4*I03^2 - 42504292183652001526964599544784386075552641301929101843166003200*I12*I06^3*I03^4 +
        1798599098224193993892356388135917550347941527591846797794099200*I12*I06^2*I03^6 - 1341168743739190303895593310591343593513066492408378514777600*I12*I06*I03^8 -
        1352050267038327665121987038498970912219014370328168704000*I12*I03^10 + 8387473503041132066391981879210755321651948212948283817984000*J09^4*I06 -
        14172439134952672920870604351175999664295947487287174051440640*J09^4*I03^2 - 25389973074411189294567833539172799332867974141391480369971200*J09^3*I09*I06 +
        774984770003470419347363652115828953287415567164551208325120*J09^3*I09*I03^2 + 2973418048607458813701801352307063706775032398140322656728268800*J09^3*I06^2*I03 +
        1018791657532104895658388252414585369332035890372487973392327680*J09^3*I06*I03^3 + 529997691729979346246024448550659609616753929587256544685568*J09^3*I03^5 +
        20290033561865364622332516470966501782868026979646526429593600*J09^2*I09^2*I06 + 831139424269424023213787611099067156763904556752059935692800*J09^2*I09^2*I03^2 +
        25317988944304240372612948326981136420861849878035606742245376000*J09^2*I09*I06^2*I03 + 881839677280200668127624903812878963233753974755859903262720*J09^2*I09*I06*I03^3 -
        221765797557789880854158346599306211274180108678136233986048*J09^2*I09*I03^5 + 1861549821941293941484321898680228215048873354806043091652837376000*J09^2*I06^4 -
        4890285371146405664150147082421243678276999282572173213835264000*J09^2*I06^3*I03^2 - 24608463056137187261707116883162537815433659644964947823028838400*J09^2*I06^2*I03^4 -
        24690198237160137938655860956097134249514466853495641534519552*J09^2*I06*I03^6 - 6478574843318945274484680182388334761854853165601552151347200*J09*I09^3*I06 +
        190846515278478269402092294716331545930799023226903673978880*J09*I09^3*I03^2 - 10105914535789646303061387070856032382909067420921321667821158400*J09*I09^2*I06^2*I03 -
        10979152974892033635854374466483608066897059081697752321653760*J09*I09^2*I06*I03^3 - 87107360587812451050247848688756601834697409698717013277184*J09*I09^2*I03^5 -
        12512438276596602617921818558392019393195290856772512915272499200000*J09*I09*I06^4 - 1319884746238393144465834357078809778045827544364579551741191782400*J09*I09*I06^3*I03^2 -
        831015396305234465341663532508277672201366547522038487577968640*J09*I09*I06^2*I03^4 - 536515834059785831902626197346997769152983721688348221281792*J09*I09*I06*I03^6 +
        3603989480282975733114853370035813303628616850370445623040*J09*I09*I03^8 - 29189088590703804418716019542399406232103815250856971889919655936000*J09*I06^5*I03 -
        918388107755914779741344609455507949047155505740164910491212185600*J09*I06^4*I03^3 + 222172028149050230452719750407697755742104644811902444515382394880*J09*I06^3*I03^5 +
        291948380999295602190481095798630273146470336287159687289651200*J09*I06^2*I03^7 + 18341527131422155139645334905196971852858455005801935080320*J09*I06*I03^9 +
        335450941633824833290871706293539648190404367057504908800*J09*I03^11 + 717223985807833353910252726920971908750220136576300456345600*I09^4*I06 -
        44223925843045787082562565093910164395699196510681038970880*I09^4*I03^2 + 589237680763029914528573364964057935819417499009516625906073600*I09^3*I06^2*I03 -
        11203334926131954889956478462980576040582616749700862915840000*I09^3*I06*I03^3 + 29470922658081340491042966195562084198752232691778427554816*I09^3*I03^5 +
        4523412605034425155025018015542248878654963514602109131953274880000*I09^2*I06^4 + 280690456542501632934355713999606411123755399803591043733459763200*I09^2*I06^3*I03^2 -
        268135992135886162468859018954704322501980420095119518118584320*I09^2*I06^2*I03^4 + 4000135090302546908047666522579088605232692401084243297921792*I09^2*I06*I03^6 -
        340015696641364272131455409157347879687724249337220033280*I09^2*I03^8 + 202656488168984662603939743290269221511169013311218466883181215744000*I09*I06^5*I03 +
        14554228430322175437067804143339594588145266500322921627588624384000*I09*I06^4*I03^3 + 8302206554885370197122417514310908710823347984943329501447127040*I09*I06^3*I03^5 +
        197373376527995359048032284512390930145839630246932286685491200*I09*I06^2*I03^7 - 69386079571658049043331407278927558486165432640587909575040*I09*I06*I03^9 -
        323951241196042246657288997302106689594463885930010201600*I09*I03^11 - 924923242561774235058104869881710130089048317918424403743342592000000*I06^7 -
        424621555518007182342390960962771977942708081369855001249848492032000*I06^6*I03^2 + 3417496532606610524841769929267488882525790699211448221828330291200*I06^5*I03^4 +
        789270890944180847978802342648212212582970800875526865507942400*I06^3*I03^8 - 1572490310266793492525735061073086979720200427470188029670400*I06^2*I03^10 -
        9928855926031511485318426631479338893302310298960247296000*I06*I03^12 - 2284516439318755380772159857357234536557085877862400000*I03^14,
        -1331073244442543167822233600000*J21*I15*I03 - 8478145905326999091517320806400000*J21*J12*I06 + 214354117510311251834348682240000*J21*J12*I03^2 + 41598099189447831785842298265600000*J21*I12*I06
        - 2267185817357192359529736629760000*J21*I12*I03^2 + 5661420008672961723399169185792000*J21*J09^2 - 1831679024043404241588846458880000*J21*J09*I09 -
        631350346505405601662688549851136000*J21*J09*I06*I03 - 1840427711977232138269898237184000*J21*J09*I03^3 + 50286385012022736522528264192000*J21*I09^2 +
        170320388981862339029036251164672000*J21*I09*I06*I03 + 461669178465923640414910219008000*J21*I09*I03^3 - 15192661761172863239934256732569600000*J21*I06^3 +
        10590264426964497719603607065640960000*J21*I06^2*I03^2 + 38139788399456821126350340892160000*J21*I06*I03^4 + 1927648839480978480159283200000*J21*I03^6 +
        1046206063023932663586865152000000*I21*J15*I03 + 3993219733327629503466700800000*I21*I15*I03 + 55674158055374064017656509235200000*I21*J12*I06 -
        1698318718431529924649865093120000*I21*J12*I03^2 - 256374646650736675301903936716800000*I21*I12*I06 + 15769283996593930068392112967680000*I21*I12*I03^2 -
        40265203996826408671507293290496000*I21*J09^2 + 12281164390792743117352926658560000*I21*J09*I09 + 4432113513518961883087558543638528000*I21*J09*I06*I03 +
        12712677606572686400066000320512000*I21*J09*I03^3 - 536293069922691806655567200256000*I21*I09^2 - 998812629871523363661380598398976000*I21*I09*I06*I03 -
        2451074416798655445746092591104000*I21*I09*I03^3 + 114944941154859680758147671313612800000*I21*I06^3 - 75849482382702821930377158813941760000*I21*I06^2*I03^2 -
        270984477047931771777940033474560000*I21*I06*I03^4 - 12799971178250606203211366400000*I21*I03^6 + 101931961153430285640523579392000000*J18*I15*I06 +
        723966827601020644834284994560000*J18*I15*I03^2 + 9140828250778511982224608641024000*J18*J12*J09 - 105913678385986156173356531712000*J18*J12*I09 -
        1228534051650154502321725049659392000*J18*J12*I06*I03 - 5094133615578315048954685871616000*J18*J12*I03^3 - 69655962180470771307853026238464000*J18*I12*J09 +
        4133420659116249200133887803392000*J18*I12*I09 + 7438804523228658969833647820746752000*J18*I12*I06*I03 + 36075034461775507318456450345728000*J18*I12*I03^3 -
        14971541590722176160164488313856000*J18*J09^2*I03 + 5977160492564225334965679737856000*J18*J09*I09*I03 + 7454367138868793950998572286345216000*J18*J09*I06^2 +
        1278296614593284189600373528692736000*J18*J09*I06*I03^2 + 3607101346193065262274911298892800*J18*J09*I03^4 - 456402039117431259176366966784000*J18*I09^2*I03 -
        1756392808008543296568288062865408000*J18*I09*I06^2 - 446904936122534415401022441068544000*J18*I09*I06*I03^2 - 833992331072143401587694048537600*J18*I09*I03^4 -
        417236639598025335761404497914953728000*J18*I06^3*I03 - 14603107539696556336164332170960896000*J18*I06^2*I03^3 - 45142309072032227888701206820608000*J18*I06*I03^5 -
        283456866613886174499978240000*J18*I03^7 - 1863502542219560434951127040000*I18*I15*I03^2 - 2529054062211737100104396881920000*I18*J12*J09 - 6636195387593117554721587200000*I18*J12*I09 +
        276189779574276911031338005708800000*I18*J12*I06*I03 + 1041022070063395191564544152576000*I18*J12*I03^3 + 10009661071573494909547274575872000*I18*I12*J09 -
        431662389311640319876123508736000*I18*I12*I09 - 964249095421085677769886566916096000*I18*I12*I06*I03 - 4341375747563222022841173496320000*I18*I12*I03^3 +
        1516507725181666388902153655500800*I18*J09^2*I03 - 85607585068634826375470745600000*I18*J09*I09*I03 - 5307317612226784383282423842734080000*I18*J09*I06^2 -
        135332324191005581804865853707878400*I18*J09*I06*I03^2 - 354500446578703302774557125785600*I18*J09*I03^4 + 31487113132617555820966190284800*I18*I09^2*I03 +
        717992099634991365303844257792000000*I18*I09*I06^2 + 1773653652684351005968452287692800*I18*I09*I06*I03^2 - 69757152262423987846775183308800*I18*I09*I03^4 +
        389678248801610201877213730376908800000*I18*I06^3*I03 + 2882054739784447625290805926379520000*I18*I06^2*I03^3 + 4952548465661959050225730337280000*I18*I06*I03^5 -
        574806633854428012028221440000*I18*I03^7 + 10306453849957951103652939694080000*J15*I15*J09 + 792804142304457777204072284160000*J15*I15*I09 -
        1424152988462128597387216599121920000*J15*I15*I06*I03 - 5552502562320308659549919379456000*J15*I15*I03^3 - 134619963576888956110066483200000*J15*J12^2 +
        1617398820608528298503620362240000*J15*J12*I12 - 10012364521716703541329143595008000*J15*J12*J09*I03 + 302386753483696862420897931264000*J15*J12*I09*I03 -
        2180912895877169683041173813329920000*J15*J12*I06^2 + 1355555834458062424607912591941632000*J15*J12*I06*I03^2 + 5357960529866748247595241368678400*J15*J12*I03^4 -
        4854661334398119482031186247680000*J15*I12^2 + 64727711128421451531063115038720000*J15*I12*J09*I03 - 5230553769280452272106379161600000*J15*I12*I09*I03 +
        13205589345666186973624842580131840000*J15*I12*I06^2 - 7555895141827801557387338826412032000*J15*I12*I06*I03^2 - 34934261170161236078543751312537600*J15*I12*I03^4 +
        1199232754879189406527442611018137600*J15*J09^2*I06 + 15131172639840937888408775218667520*J15*J09^2*I03^2 - 337575815358060449136328844525568000*J15*J09*I09*I06 -
        6274522249681120184032980738048000*J15*J09*I09*I03^2 - 144000945383373125606984230780718284800*J15*J09*I06^2*I03 - 1708136298797131305716909363201064960*J15*J09*I06*I03^3 -
        3665315333252871682695579392087040*J15*J09*I03^5 + 6456764789706641184207324109209600*J15*I09^2*I06 + 425665563318202173133788972933120*J15*I09^2*I03^2 +
        38965227972238576926651045229992345600*J15*I09*I06^2*I03 + 588111996580922098047951816139653120*J15*I09*I06*I03^3 + 952311256896376811467084711726080*J15*I09*I03^5 -
        2942066609126495587494749361332551680000*J15*I06^4 + 2681569696241423177512184777927491584000*J15*I06^3*I03^2 + 23536182458559637991929076564395622400*J15*I06^2*I03^4 +
        48005101092857739966122780843366400*J15*I06*I03^6 + 1231686059810668163658464256000*J15*I03^8 - 28751182079958932424960245760000*I15^2*I06*I03 + 4765242215104304540803596288000*I15^2*I03^3 +
        17064502425239445140712652800000*I15*J12^2 - 214443913810509027268289003520000*I15*J12*I12 + 3370044543317280951433202368512000*I15*J12*J09*I03 -
        433356790657271281645179396096000*I15*J12*I09*I03 - 121331700105796069707206709411840000*I15*J12*I06^2 - 283989972027137340698121558159360000*I15*J12*I06*I03^2 -
        1146894993741344077555254661939200*I15*J12*I03^4 + 673479029049450101553459363840000*I15*I12^2 - 20096313006534204593612154028032000*I15*I12*J09*I03 +
        3235596784370950628982674313216000*I15*I12*I09*I03 - 2759022799858028610957631031377920000*I15*I12*I06^2 + 1525108633046788676911176472492032000*I15*I12*I06*I03^2 +
        8022291767296012945726995242188800*I15*I12*I03^4 + 380113746355764242939145460536115200*I15*J09^2*I06 - 4443514045672950295952831673384960*I15*J09^2*I03^2 -
        311934563279676118453214847983616000*I15*J09*I09*I06 + 1118807887272026696961437813760000*I15*J09*I09*I03^2 - 34706135720372059862402165313395097600*I15*J09*I06^2*I03 +
        237782472968197747794509131234222080*I15*J09*I06*I03^3 + 865510497943476468630605314744320*I15*J09*I03^5 + 12929538376681624284096038318899200*I15*I09^2*I06 +
        82100606570306861937057327882240*I15*I09^2*I03^2 + 26612289566223941896733120251458355200*I15*I09*I06^2*I03 - 17263754751635441252764695524597760*I15*I09*I06*I03^3 -
        190602137614742422284148568432640*I15*I09*I03^5 - 331675598402098355080036995823042560000*I15*I06^4 + 273641773284424190325359555051323392000*I15*I06^3*I03^2 -
        3001738906282671170745885705767731200*I15*I06^2*I03^4 - 12267029903628854226265283719987200*I15*I06*I03^6 - 1326088547083147611719467008000*I15*I03^8 +
        98105586826612619581092495360000*J12^3*I03 - 1609312323446172000347008942080000*J12^2*I12*I03 + 103225606184706205624744454184960000*J12^2*J09*I06 -
        255807127190578073230189287936000*J12^2*J09*I03^2 + 3425102958607524536136008417280000*J12^2*I09*I06 - 103033112934146727967741504512000*J12^2*I09*I03^2 -
        7975461045610594301771453201694720000*J12^2*I06^2*I03 - 94004844981332591437566579247104000*J12^2*I06*I03^3 - 236739214522176692416493366822400*J12^2*I03^5 +
        7784560574388020124097641676800000*J12*I12^2*I03 - 1254733302577649141605643040043008000*J12*I12*J09*I06 + 2706616596200038321395722704128000*J12*I12*J09*I03^2 -
        2619550549530941449637529133056000*J12*I12*I09*I06 + 1345406268607666460678021137920000*J12*I12*I09*I03^2 + 118058041685980353812098761359253504000*J12*I12*I06^2*I03 +
        1328687054275711544813666687413248000*J12*I12*I06*I03^3 + 3396188944097865409176916978579200*J12*I12*I03^5 - 17163081875871057049826450029977600*J12*J09^3 +
        3221000631106765199635022502912000*J12*J09^2*I09 + 1558123527357369100382268323454566400*J12*J09^2*I06*I03 + 5262776847990599810215827399367680*J12*J09^2*I03^3 +
        541861083637896787584628786790400*J12*J09*I09^2 - 21774044444662425934059367289241600*J12*J09*I09*I06*I03 + 57187375821226891417668911539200*J12*J09*I09*I03^3 +
        81626436769084410136047074878095360000*J12*J09*I06^3 + 2430238540353536726556816019702579200*J12*J09*I06^2*I03^2 + 24278305567946974692158723938191360*J12*J09*I06*I03^4 +
        87920901330376071246796234984320*J12*J09*I03^6 + 5628067187045792721254313984000*J12*I09^3 - 99356530878870239741666703210086400*J12*I09^2*I06*I03 -
        361856664826414601973640674232320*J12*I09^2*I03^3 + 21959681967003496498166615921786880000*J12*I09*I06^3 - 22555740008619903077486082258908774400*J12*I09*I06^2*I03^2 -
        73968558196939506626716683372625920*J12*I09*I06*I03^4 + 63237094585354817192596435608960*J12*I09*I03^6 - 1803289622121489818384678768134717440000*J12*I06^4*I03 -
        391366036414707433167483516061753344000*J12*I06^3*I03^3 - 1557113375597850600659388046287360000*J12*I06^2*I03^5 - 175839752694052605535954869600000*J12*I06*I03^7 -
        345344919242678172085435776000*J12*I03^9 - 8874754850356054916723916226560000*I12^3*I03 + 4163010764546360092107423767887872000*I12^2*J09*I06 +
        10548897504318699174284791965696000*I12^2*J09*I03^2 - 190680842984102898893002344923136000*I12^2*I09*I06 - 4106841147008919272715115272192000*I12^2*I09*I03^2 -
        406199950697865948409216266614194176000*I12^2*I06^2*I03 - 4521367137656851930536592754792448000*I12^2*I06*I03^3 - 12369228999626057870650368207398400*I12^2*I03^5 +
        24509779235470725929274364836249600*I12*J09^3 + 8782436668239654102305016584601600*I12*J09^2*I09 - 1223475521489011323512039595115929600*I12*J09^2*I06*I03 -
        7543146598719285700189089643691520*I12*J09^2*I03^3 - 6110397501640073322695587219046400*I12*J09*I09^2 - 1995121005271078433232167505987379200*I12*J09*I09*I06*I03 -
        8037009004343880559105127002636800*I12*J09*I09*I03^3 - 532342484857768541152566999633887232000*I12*J09*I06^3 - 86516479545687329911223296494086553600*I12*J09*I06^2*I03^2 -
        491416949228683594820371430932131840*I12*J09*I06*I03^4 - 706672024503331668117754842276480*I12*J09*I03^6 + 268462887584267214742408681881600*I12*I09^3 +
        634750754978939662513069643416780800*I12*I09^2*I06*I03 + 2502073274721313525341924945300480*I12*I09^2*I03^3 - 23272523508939618652897145658015744000*I12*I09*I06^3 +
        101550541122714595313647240648475443200*I12*I09*I06^2*I03^2 + 386205336490658518986577369618452480*I12*I09*I06*I03^4 - 451343392454707301922742973485440*I12*I09*I03^6 +
        25814284192128730994673488962641985536000*I12*I06^4*I03 + 1182955476018245593921550299778236416000*I12*I06^3*I03^3 + 5485942029404464337903567335234560000*I12*I06^2*I03^5 +
        2176199076483232087874951198016000*I12*I06*I03^7 + 3311337336547378434507719424000*I12*I03^9 + 11132898289860798430324595106232320*J09^4*I03 +
        1578880089403034401409748049244160*J09^3*I09*I03 + 3073203324808174869782654485345075200*J09^3*I06^2 - 1446715735842144653396767066922496000*J09^3*I06*I03^2 -
        4008433614634882493018350326049536*J09^3*I03^4 - 2624609004175459480061479441582080*J09^2*I09^2*I03 - 19132070129144403576195874943611699200*J09^2*I09*I06^2 -
        234323177018645438618923693604782080*J09^2*I09*I06*I03^2 + 63162101223132001596742008056832*J09^2*I09*I03^4 - 380752966062503786488581274418705203200*J09^2*I06^3*I03 +
        42692387020737508924180954892725616640*J09^2*I06^2*I03^3 + 170310967551948843579156482672322048*J09^2*I06*I03^5 + 54820503124613855104780651557312*J09^2*I03^7 +
        483357421977652242925161648168960*J09*I09^3*I03 + 6433607326775228184798508604011315200*J09*I09^2*I06^2 + 265110517380600102483213327271710720*J09*I09^2*I06*I03^2 +
        327722804482472917015952708676864*J09*I09^2*I03^4 + 2107932573384176314582060108405279948800*J09*I09*I06^3*I03 + 19929988556058020015995479882701291520*J09*I09*I06^2*I03^3 +
        4800318457729198866180470388453888*J09*I09*I06*I03^5 - 81244039433580332151451076683008*J09*I09*I03^7 - 8171918987487201192135580932762501120000*J09*I06^5 +
        6599062875043518178526231536165965004800*J09*I06^4*I03^2 - 412502269876316015637935821311783567360*J09*I06^3*I03^4 - 2392300959084325967530409073429534720*J09*I06^2*I03^6 -
        2379153171250362257203482124421760*J09*I06*I03^8 - 55581585958887214070328332800*J09*I03^10 - 35260482456094543192716530688000*I09^4*I03 - 244407022529359987764161972482867200*I09^3*I06^2 -
        28349839284034281678067680620421120*I09^3*I06*I03^2 - 30787492233228939103414470547968*I09^3*I03^4 - 609045892887757660473537684744457420800*I09^2*I06^3*I03 -
        6246215577168854716005590486683238400*I09^2*I06^2*I03^3 + 466086204673321402899886986796032*I09^2*I06*I03^5 + 16308299583474045352094362344768*I09^2*I03^7 +
        42336436375033111697245528344955453440000*I09*I06^5 - 33476677573126367211110555018093435289600*I09*I06^4*I03^2 - 251634580818878672483783910561634222080*I09*I06^3*I03^4 +
        46664253003506918091269516424714240*I09*I06^2*I03^6 + 1339251005241000651492431822805120*I09*I06*I03^8 + 153410186496945643099524569600*I09*I03^10 +
        197368900159426647655901195071704268800000*I06^6*I03 + 20540109575659653769975234614565797888000*I06^5*I03^3 + 327931499878292747503375385697150566400*I06^4*I03^5 +
        7787501403508398027910338161683660800*I06^3*I03^7 + 22257603351586585820690955733478400*I06^2*I03^9 + 1375328740743608286102437376000*I06*I03^11 - 735105154760141753548800000*I03^13,
        3064560938679144931872005732400866009727173599689600000*J21*I15 - 88667945063934053953840339653033155981343798501566808000*J21*J12*I03 +
        177270632690340298856811614961621420660630203414158992000*J21*I12*I03 - 3685540198202651389942263755474159609519084732112251424000*J21*J09*I06 +
        324672897170127024403689416695909472758449447062419788000*J21*J09*I03^2 + 921919944069992233802729649782077222626627732109309248000*J21*I09*I06 +
        15777774057730516813583072988753145049288938046714436000*J21*I09*I03^2 + 232397242666916162306657553954069301219780919269387542528000*J21*I06^2*I03 -
        10957984794229358663234671535732914222009555336636297152000*J21*I06*I03^3 - 111665659591759574546138535307230303708219564102230400000*J21*I03^5 +
        1437833161565428997429549864634080785908725778816000000*I21*J15 - 8881869548813182054486355774290648468614967909324800000*I21*I15 +
        629753947645819728477769066634065202001739109637109824000*I21*J12*I03 - 2286588130467490350967035743613456904359052286326217856000*I21*I12*I03 +
        20842401664007909220263984399447781351173728734287469312000*I21*J09*I06 - 1345444384712325398492503728568228109893463047671053088000*I21*J09*I03^2 -
        6604771298970951676251850935702193812992716827748222464000*I21*I09*I06 - 350912353508708546707814819956465864180712405695941216000*I21*I09*I03^2 -
        1064745976546626605262337891816307679190411175758347669504000*I21*I06^2*I03 + 43069572939163068163115762440480728483692811981883362048000*I21*I06*I03^3 +
        750394317001106843678656125725830699990869441016243200000*I21*I03^5 - 80777997535492403152647345880510697532580417303157568000*J18*I15*I03 +
        6253371616066942035633326980830254852034001299755027712000*J18*J12*I06 + 240685762821402876326485479832715453715317058175788693600*J18*J12*I03^2 +
        15705537556862299815489140285708147647665350821660881408000*J18*I12*I06 - 886301482885729507451110614564528634431749797764775080000*J18*I12*I03^2 -
        52221284936207059370133566043071725635008540140972032000*J18*J09^2 + 34309622197451406798788464003727878166517061077135360000*J18*J09*I09 +
        3165410982750099342315299216841190613849652460973384016000*J18*J09*I06*I03 - 2222659971072739625899510340553143493864449268507563286960*J18*J09*I03^3 -
        5213702606221935018497497308968040770930877829343232000*J18*I09^2 + 3700848291142672349520585892641959741970505233365641824000*J18*I09*I06*I03 +
        273565159075875109051553001473312424687034830659461207920*J18*I09*I03^3 - 17829943290142697913245631364934375465709430680322283569152000*J18*I06^3 -
        349024277686438894230120173470711867207082751331319447961600*J18*I06^2*I03^2 + 92329819450903652595934986965201894910831070153095764832000*J18*I06*I03^4 +
        575580052370541167030539043753074659193118253337414080000*J18*I03^6 + 9145586444981330624287038749634570059716000455889152000*I18*I15*I03 +
        354151189082289435686080479577100995338734706039079680000*I18*J12*I06 - 71814392851754034858031113849194641649957208367798939200*I18*J12*I03^2 -
        2807640257821297670122186861505994435833234334645763584000*I18*I12*I06 + 172092353140365305911056146025200288275502088023007523200*I18*I12*I03^2 +
        5718270366241901133131410667287979694419510179522560000*I18*J09^2 - 3475801737481290012331664872645360513953918552895488000*I18*J09*I09 -
        9295641202058094495842233150004126303954132342378863353600*I18*J09*I06*I03 + 189988422347846282080749639036965425501268798677743597600*I18*J09*I03^3 +
        242921782900237592299335239894267469999898192029696000*I18*I09^2 - 745717262105140392651324031932966285121375671409599628800*I18*I09*I06*I03 -
        11458365853333617053222338891669391337716153572662756000*I18*I09*I03^3 + 4614916571679495541444434228528193244534666950821652316160000*I18*I06^3 +
        540457010592695782928569342367459193798325318376325816115200*I18*I06^2*I03^2 - 2077372630281495546719167348101558053396483749916877427200*I18*I06*I03^4 -
        37976530915344107720432003916560717380923252005627520000*I18*I03^6 + 625296157067517018201658277337259778436024529151024640000*J15*I15*I06 +
        79523737593906940606542902171203863229521128098749120000*J15*I15*I03^2 + 431470601982741102607806627322475391800797690348800000*J15*J12*J09 -
        422513285169276275755177200032149568268717704643840000*J15*J12*I09 - 24894647485665892061897033109786338118327159349753143398400*J15*J12*I06*I03 -
        230069038462770620639780048617756739478861892369452269280*J15*J12*I03^3 - 31052302331522791202760481755196179476017265055123456000*J15*I12*J09 +
        2482332932733668938383514125171042457021410929733120000*J15*I12*I09 - 62547141540793370979413386307193430340558719811288682086400*J15*I12*I06*I03 +
        315795168336275209818372991174915535864727954610709632320*J15*I12*I03^3 + 629517336984198871573812136677253236519690786315060687360*J15*J09^2*I03 +
        28281040017847374062143886989305155734262990016603728640*J15*J09*I09*I03 - 1217978525843738093958944516797728319370586886688384958259200*J15*J09*I06^2 +
        83796566156160810703802031132762031877997274163873626262400*J15*J09*I06*I03^2 + 2389224623480938335381580173866025954790776835827547403760*J15*J09*I03^4 +
        7575251154729700542233672414725343413760535725117283840*J15*I09^2*I03 + 184281491016358475375634978533471235032114362725184226918400*J15*I09*I06^2 -
        23764208765209053619970386872100852347736149927223972688640*J15*I09*I06*I03^2 - 406416128612791025560402265563720137776821632949707123120*J15*I09*I03^4 +
        114606755179465570581810088192946807255791207763112967235174400*J15*I06^3*I03 - 3061982524493999930323175580115805981728242652647553716756480*J15*I06^2*I03^3 -
        121036964597989248193937136128207453714725623881022543156480*J15*I06*I03^5 - 566299837321441928167481771991573390022253183204680128000*J15*I03^7 -
        7225209478358783423819142602631759527026668753733632000*I15^2*I03^2 - 5886315442713791007695332254861361357549447833783360000*I15*J12*J09 -
        3418707536842802391430211664581984878035055176558720000*I15*J12*I09 - 5038890100090210830499843570012439786578531603978877932800*I15*J12*I06*I03 +
        167502400455485355432431019935796830847330647286805736640*I15*J12*I03^3 - 8186248874241528430511598721116590587135707422019072000*I15*I12*J09 +
        13260650347894557812043353531216406746757010793763840000*I15*I12*I09 + 26879604621620619403906305759684284213078627542755889651200*I15*I12*I06*I03 -
        257651992805705703793289586922894724397130625840835788160*I15*I12*I03^3 + 284142295541146777960853151884946214369880423449726619520*I15*J09^2*I03 -
        98879577296180473352977241026535228429700477212390267520*I15*J09*I09*I03 - 281154484546346220981909495231361683280244099786324529638400*I15*J09*I06^2 -
        7936278569369498973252358852597767974242031164747564272000*I15*J09*I06*I03^2 - 856504722698655661899009305139407329949710738920282223200*I15*J09*I03^4 -
        16460496465458282627624730294883763505078743347940133120*I15*I09^2*I03 + 116246560519157977349355180135433680712197705281180254156800*I15*I09*I06^2 +
        9204755579982154140865394758871195180245200130783642677120*I15*I09*I06*I03^2 + 142103238884480141006680446141944772435848884566296536800*I15*I09*I03^4 +
        5623403930055930195181976107513557233106818012526478044364800*I15*I06^3*I03 - 485380969279421949699406430062688900563819585513405988136960*I15*I06^2*I03^3 +
        21399284826296271164163097042105065976055889256456402295040*I15*I06*I03^5 + 140862128156991707419422404152121741675290389497032704000*I15*I03^7 -
        28276472954845536807712736710071105334361515929600000*J12^3 - 4399517650060413690675610031231078279187953747988480000*J12^2*I12 +
        409615395444910397473438623760435294225124025223038084000*J12^2*J09*I03 - 1678250690695537424132979479238391418669272021503220800*J12^2*I09*I03 -
        21643031165377031985737832836846857091848097221600972800000*J12^2*I06^2 - 1242552033608712528774928067091511985865782696131597147200*J12^2*I06*I03^2 -
        24679279444700464091044032412534843980764350273637292420*J12^2*I03^4 + 29810396689704809944055803486809227085321381087237120000*J12*I12^2 -
        1766036825754438014152114613092804070626119142252572100800*J12*I12*J09*I03 + 28517766925672492642846734663098690490358204596989712000*J12*I12*I09*I03 +
        29721635112198727134723370683450015466172774362458187776000*J12*I12*I06^2 + 33913728373697816602903445774592998834230901626660544832000*J12*I12*I06*I03^2 +
        270482478569038746335605537513913780410483796139117987360*J12*I12*I03^4 + 12279333526009204584684834908116751715118043393788108387200*J12*J09^2*I06 -
        1333195831626527381087541500529240614368228268243310436680*J12*J09^2*I03^2 - 4125660016057327803841693902086346479399036277940810790400*J12*J09*I09*I06 -
        268012081647356259146070398273304092474265521832213281880*J12*J09*I09*I03^2 - 579498069603005269559469539287160466692005460964752136825600*J12*J09*I06^2*I03 +
        4656921796573902914318720713087744377543047696306147176080*J12*J09*I06*I03^3 + 212654501831861901831838802078237187002126947671765686724*J12*J09*I03^5 +
        373291350357484166260044859242044939130393576315354816000*J12*I09^2*I06 + 29484069998223862721911288036004179003474398358195090320*J12*I09^2*I03^2 +
        302550142292412488405526489230363158158963112566429059980800*J12*I09*I06^2*I03 + 15835262520479006868731467480676026495322546117019801490080*J12*I09*I06*I03^3 +
        64451311212680499329908927680272835132952893509490784332*J12*I09*I03^5 - 16197495721110952487013139004992523720106796182324714700800000*J12*I06^4 -
        25956496042035289255504217736886830251093757653570206664601600*J12*I06^3*I03^2 + 1178945422210900157151073590714691649337742991620267523251200*J12*I06^2*I03^4 +
        10913316248930404758972691151585553821416467953164690110000*J12*I06*I03^6 + 20125944322210074639097053447231452672861650921505688000*J12*I03^8 -
        34721247225698680425337552173547424519305705581619200000*I12^3 + 1921135524902465399632897029594189892220993816073830899200*I12^2*J09*I03 -
        84984832074554175446506299490436620150704103880499955200*I12^2*I09*I03 - 1014489099468614560331350833971948482389467474150524882944000*I12^2*I06^2 -
        52010452921584909884047070430711231723400667508198588076800*I12^2*I06*I03^2 - 334081115433758856030735287933825725498186118874796092720*I12^2*I03^4 -
        15797996847368952984850128631480979875439985026646091699200*I12*J09^2*I06 + 2254513137583566252615811010760712221231109387243613453520*I12*J09^2*I03^2 -
        969339859722985422276800431270832199148338220578965836800*I12*J09*I09*I06 + 708438554193391713192193710155382977904055429723609836720*I12*J09*I09*I03^2 +
        55120423567873866161906347546872441922311700155538399680000*I12*J09*I06^2*I03 + 83065379903162684168667146409405507691671744764440671324000*I12*J09*I06*I03^3 +
        303244308718022598665317115562259859693918666395855153584*I12*J09*I03^5 + 1614036868319411070982216083415108113210034288061111654400*I12*I09^2*I06 -
        114294888442742080963279681392759930768541893252837643680*I12*I09^2*I03^2 + 69334810701548728340705135297391816183536711952370786329600*I12*I09*I06^2*I03 -
        54387170124750493643986417310734227918256792521697266183360*I12*I09*I06*I03^3 - 262411366483396135513378245560964387724379808435386336688*I12*I09*I03^5 +
        786214615157052261478913085200213707065530296450687872466944000*I12*I06^4 + 78237505960642033241068747791755445718135933661987796759552000*I12*I06^3*I03^2 -
        5538952893153402957815367919481200267763063577356801530982400*I12*I06^2*I03^4 - 67219218244718875387225547994673114819295972511745390615200*I12*I06*I03^6 -
        192228693764440259959370693236277641786871922993262512000*I12*I03^8 - 6530801846977178597029187159348115714763997235621888000*J09^4 +
        18851321643402210560219001233011936850418062942539776000*J09^3*I09 - 5494882797938583617618595528913234435469073196982899293600*J09^3*I06*I03 +
        498781661694081520260995491393437992552185656853150608156*J09^3*I03^3 - 13283337572869381365528355774989173339264209859506176000*J09^2*I09^2 -
        2452755242541381723970582134875180149185834421850743395360*J09^2*I09*I06*I03 + 734594748760102835794909704439735890403814473799167880856*J09^2*I09*I03^3 -
        1209355592411967479279996998105990385780734193986453813862400*J09^2*I06^3 + 649388427219961045534017391572529334632716853542452433025920*J09^2*I06^2*I03^2 -
        9374765647309594081900745700683566664475058155906675126072*J09^2*I06*I03^4 - 227554323760633156621923559719741283449268761024183817665*J09^2*I03^6 +
        3574350128110189644096101075442223584947792058789888000*J09*I09^3 - 803910099845830104878142631125267832473391711992226859520*J09*I09^2*I06*I03 -
        183341055436523549144129284711487603850602078965617908364*J09*I09^2*I03^3 + 18008657782430325889280743952848253120588041024738534046515200*J09*I09*I06^3 -
        1143685185504133362506267299023195488647642536103289285427840*J09*I09*I06^2*I03^2 - 50750262528782228900864657940281825525294749459761771438600*J09*I09*I06*I03^4 -
        104577488679873528486063667298962031141464795832131778310*J09*I09*I03^6 + 60266983404432607763264035049455242107257482219880942137753600*J09*I06^4*I03 +
        7825205318900384869358808760491942387099154802777766375444480*J09*I06^3*I03^3 - 286961358499969177006852749201574070587803902128415728504896*J09*I06^2*I03^5 +
        4531621393367289028587270034291678971050839494470377674024*J09*I06*I03^7 + 11172422063009604595711725227004597728326025764095866400*J09*I03^9 -
        333093560325680755363794365453397179959292449923072000*I09^4 + 159676601216049601768660620557180190743530407453998033280*I09^3*I06*I03 +
        11508829273058280628863946467741074230217807703829517496*I09^3*I03^3 - 4018811872029494415280166786559632660695093956327214935244800*I09^2*I06^3 +
        137955402164598924900461027379410975661902795723166370210560*I09^2*I06^2*I03^2 + 6676543834389218869537781095731554272888869005575865184288*I09^2*I06*I03^4 +
        21628191910800489299452242971524391997489179151557067255*I09^2*I03^6 - 1249863542234087614112700706745477824067786733028897617752064000*I09*I06^4*I03 +
        34978180532212506727303078864362779665159790398006583908915200*I09*I06^3*I03^3 + 1104828698008312906256619847208917215696651945361830191586432*I09*I06^2*I03^5 +
        2525449994109169467884898460157121724640462704477437199032*I09*I06*I03^7 - 11717829292190026313287266144508794560542586368164784800*I09*I03^9 -
        27136105072799118919836960583105622584919924884198025173401600000*I06^6 + 11796996749420220148407032808593652037107114640325713794878668800*I06^5*I03^2 -
        453144983083330650272024482864695008038975547921242464858439680*I06^4*I03^4 - 754367770984196024864932344912989533633666728452036540866560*I06^3*I03^6 -
        50801151819054333371051810415612433116805517418677959006080*I06^2*I03^8 - 228961331221841216520613190298674906273362101619685088000*I06*I03^10 +
        142782277457422211298259991084827158534817867366400000*I03^12,
        -5732119183962931200000*J21*I15 - 3389635526395345920000*J21*J12*I03 + 35659583448590062080000*J21*I12*I03 + 6001838747686420531200000*J21*J09*I06 + 28768859223698047104000*J21*J09*I03^2 -
        2013840279096678144000000*J21*I09*I06 - 7090437366666476928000*J21*I09*I03^2 - 127574556294294301409280000*J21*I06^2*I03 - 587436110058411694080000*J21*I06*I03^3 -
        18201433569177600000*J21*I03^5 - 23008345491898368000000*I21*J15 + 17196357551888793600000*I21*I15 + 30304058768846069760000*I21*J12*I03 - 250078017218849648640000*I21*I12*I03 -
        40798774050969670041600000*I21*J09*I06 - 200062041390204521472000*I21*J09*I03^2 + 10872415589429186150400000*I21*I09*I06 + 36246281659226440704000*I21*I09*I03^2 +
        881958847474108933079040000*I21*I06^2*I03 + 4185263724187670691840000*I21*I06*I03^3 + 102872266179379200000*I21*I03^5 + 69358642125951467520000*J18*I15*I03 +
        16414962805856552878080000*J18*J12*I06 + 77954719907229967872000*J18*J12*I03^2 - 91048573557020718858240000*J18*I12*I06 - 569134263994506540288000*J18*I12*I03^2 +
        107068157554402566144000*J18*J09^2 - 84083317667799367680000*J18*J09*I09 - 17676913865616388002816000*J18*J09*I06*I03 - 57582360748757723558400*J18*J09*I03^3 +
        17208338505269796864000*J18*I09^2 + 8015296499573176138752000*J18*I09*I06*I03 + 14219365294109539468800*J18*I09*I03^3 + 3776166578698155007672320000*J18*I06^3 +
        266761751970331527856128000*J18*I06^2*I03^2 + 677259784255605562368000*J18*I06*I03^4 - 196171696478177280000*J18*I03^6 - 8024966857548103680000*I18*I15*I03 -
        3362330251427748249600000*I18*J12*I06 - 15625558231551894528000*I18*J12*I03^2 + 11450342817108243578880000*I18*I12*I06 + 68618909490968858112000*I18*I12*I03^2 -
        11736160123538350080000*I18*J09^2 + 8701383544174411776000*I18*J09*I09 + 1708727964353586247680000*I18*J09*I06*I03 + 5257883261182320921600*I18*J09*I03^3 - 1270830303893348352000*I18*I09^2 -
        294719511524369541120000*I18*I09*I06*I03 + 891370834778706508800*I18*I09*I03^3 - 3944608723560445142630400000*I18*I06^3 - 45266839704113501601792000*I18*I06^2*I03^2 -
        79936628306236434432000*I18*I06*I03^4 + 2232212217016320000*I18*I03^6 + 13998471539785665085440000*J15*I15*I06 - 656234466348367872000*J15*I15*I03^2 + 932814379431567360000*J15*J12*J09 +
        1517629026570854400000*J15*J12*I09 - 18072789272454563168256000*J15*J12*I06*I03 - 82357094720304365875200*J15*J12*I03^3 + 73799873260687429632000*J15*I12*J09 -
        11378582646922874880000*J15*I12*I09 + 93675461444971977424896000*J15*I12*I06*I03 + 555313865096958050764800*J15*I12*I03^3 - 118374186717939098419200*J15*J09^2*I03 +
        95462112366553979289600*J15*J09*I09*I03 + 1350295031666646162800640000*J15*J09*I06^2 + 24891913013049917988249600*J15*J09*I06*I03^2 + 57612768299909126115840*J15*J09*I03^4 -
        19635532260025651200000*J15*I09^2*I03 - 485381425848378974208000000*J15*I09*I06^2 - 10497694111838119672012800*J15*I09*I06*I03^2 - 15838556245045290247680*J15*I09*I03^4 -
        32597029738860868339236864000*J15*I06^3*I03 - 416195258091183596106547200*J15*I06^2*I03^3 - 701655483244677250867200*J15*I06*I03^5 + 185710347183900672000*J15*I03^7 -
        123813774373599313920000*I15^2*I06 + 20520986678587293696000*I15^2*I03^2 + 15279401811058237440000*I15*J12*J09 + 4302958030843207680000*I15*J12*I09 +
        4155169268776040460288000*I15*J12*I06*I03 + 19687183398477910425600*I15*J12*I03^3 + 7420507248309571584000*I15*I12*J09 - 21236627052102389760000*I15*I12*I09 -
        22965832606969525045248000*I15*I12*I06*I03 - 156764537791567611494400*I15*I12*I03^3 + 35277067387548035481600*I15*J09^2*I03 - 46210684939195288780800*I15*J09*I09*I03 +
        343539674017161758760960000*I15*J09*I06^2 - 3326343913588154547916800*I15*J09*I06*I03^2 - 10842711726320858603520*I15*J09*I03^4 + 7671462602161139712000*I15*I09^2*I03 -
        272615711999520646471680000*I15*I09*I06^2 + 1467418218694755470438400*I15*I09*I06*I03^2 + 1602244580602267607040*I15*I09*I03^4 - 3389871094422383250505728000*I15*I06^3*I03 +
        54696805566595004561817600*I15*I06^2*I03^3 + 135863171441060784537600*I15*I06*I03^5 + 28578942610735104000*I15*I03^7 + 218777073323212800000*J12^3 + 5751072340691189760000*J12^2*I12 +
        12622527811763956224000*J12^2*J09*I03 - 912011504634270720000*J12^2*I09*I03 + 101309737760952208588800000*J12^2*I06^2 + 1230415946313471654912000*J12^2*I06*I03^2 +
        3679259798414247667200*J12^2*I03^4 - 50031756511777751040000*J12*I12^2 - 163795822208652632832000*J12*I12*J09*I03 - 1152135527799458304000*J12*I12*I09*I03 -
        1504303809285531020820480000*J12*I12*I06^2 - 17865390610460333541888000*J12*I12*I06*I03^2 - 52483857852981454905600*J12*I12*I03^4 - 17219206264264358538240000*J12*J09^2*I06 -
        85082661679207495334400*J12*J09^2*I03^2 + 1480710861374216371200000*J12*J09*I09*I06 - 5468932962774301478400*J12*J09*I09*I03^2 + 115905833475299997696000*J12*J09*I06^2*I03 -
        437643046441124423424000*J12*J09*I06*I03^3 - 1276784859434756374080*J12*J09*I03^5 + 1356010221021609646080000*J12*I09^2*I06 + 7169913004575717504000*J12*I09^2*I03^2 +
        312705916739848961021952000*J12*I09*I06^2*I03 + 1324278853463159487129600*J12*I09*I06*I03^3 - 979294437288221624640*J12*I09*I03^5 + 20691879029775082192896000000*J12*I06^4 +
        5503555480209818792656896000*J12*I06^3*I03^2 + 29286516257415032426496000*J12*I06^2*I03^4 - 1532835146953611648000*J12*I06*I03^6 - 1086024292883712000*J12*I03^8 +
        61369349378645606400000*I12^3 + 236228511972674267136000*I12^2*J09*I03 + 9967264044211279872000*I12^2*I09*I03 + 4961794354288361523118080000*I12^2*I06^2 +
        61826950778243648578560000*I12^2*I06*I03^2 + 196912836811485626227200*I12^2*I03^4 + 18110665393596148359168000*I12*J09^2*I06 + 144148622084994362227200*I12*J09^2*I03^2 +
        18149177044765014441984000*I12*J09*I09*I06 + 160357959498027782592000*I12*J09*I09*I03^2 + 1145525892164725653098496000*I12*J09*I06^2*I03 + 7946039254466000020838400*I12*J09*I06*I03^3 +
        10282989056030192113920*I12*J09*I03^5 - 7778232498123083243520000*I12*I09^2*I06 - 48426822845557423027200*I12*I09^2*I03^2 - 1439474758401177350221824000*I12*I09*I06^2*I03 -
        7469213233556435871283200*I12*I09*I06*I03^3 + 6963486369913634319360*I12*I09*I03^5 - 238026790815911728832839680000*I12*I06^4 - 20784670029629150012669952000*I12*I06^3*I03^2 -
        120001009315428337324032000*I12*I06^2*I03^4 - 19512319455289600128000*I12*I06*I03^6 - 37388704991565312000*I12*I03^8 + 13419178559722930176000*J09^4 - 40552025349108252672000*J09^3*I09 +
        10630083651624968596531200*J09^3*I06*I03 + 60515493538443141525120*J09^3*I03^3 + 32279041016079040512000*J09^2*I09^2 + 4106774167990044687360000*J09^2*I09*I06*I03 +
        1550722823477458076160*J09^2*I09*I03^3 + 2982427500345794701885440000*J09^2*I06^3 - 398681799933675344705740800*J09^2*I06^2*I03^2 - 2550879622973017783802880*J09^2*I06*I03^4 -
        931132562220049426272*J09^2*I03^6 - 10280166366755045376000*J09*I09^3 - 4346427568230321228748800*J09*I09^2*I06*I03 - 4716719829253226736000*J09*I09^2*I03^3 -
        20041968027697642537943040000*J09*I09*I06^3 - 330021655457078739706675200*J09*I09*I06^2*I03^2 - 50813424686040068505600*J09*I09*I06*I03^4 + 1341797551371407950848*J09*I09*I03^6 -
        61560224542273042523750400000*J09*I06^4*I03 + 4181773492654055468074598400*J09*I06^3*I03^3 + 36944163495523181650636800*J09*I06^2*I03^5 + 39986362062969463008000*J09*I06*I03^7 -
        3888884526649113600*J09*I03^9 + 1153514506493067264000*I09^4 + 626818033452109782528000*I09^3*I06*I03 + 174935337074212320000*I09^3*I03^3 + 7270703130307724771328000000*I09^2*I06^3 +
        109697539431647038233600000*I09^2*I06^2*I03^2 - 57337076473222972769280*I09^2*I06*I03^4 - 290730396697477960608*I09^2*I03^6 + 400550183924447168017072128000*I09*I06^4*I03 +
        4144596880206200257231257600*I09*I06^3*I03^3 - 3908510229819677852160000*I09*I06^2*I03^5 - 22029816338484780268800*I09*I06*I03^7 + 2099445836074675200*I09*I03^9 -
        1476490984040259458275737600000*I06^6 - 466615063327421106600542208000*I06^5*I03^2 - 6976545505531495595193139200*I06^4*I03^4 - 147977656090609496688230400*I06^3*I03^6 -
        352169221485089956147200*I06^2*I03^8 + 118708280309670912000*I06*I03^10 + 45245425254400000*I03^12,
        78784589597301414463490280000*J21*J12 - 170112170022053858200692720000*J21*I12 + 81956922548961269402420436000*J21*J09*I03 - 98174102358705673359835692000*J21*I09*I03 -
        204635994483204159448408980480000*J21*I06^2 + 11122340913847708708690336320000*J21*I06*I03^2 - 61725354891235978256496000000*J21*I03^4 - 561286838307029492584059840000*I21*J12 +
        2088377112486985915007064960000*I21*I12 - 925351273134289646816034528000*I21*J09*I03 + 942244479611725373098587936000*I21*I09*I03 + 1208285275196016878775932989440000*I21*I06^2 -
        76180440193642261968468768000000*I21*I06*I03^2 + 373799536031299963923072000000*I21*I03^4 + 36291693525899861627383680000*J18*I15 - 960095015436246779564457444000*J18*J12*I03 -
        103386223590326074764738792000*J18*I12*I03 + 21479306020143695881688563200000*J18*J09*I06 - 507894247302734763946114088400*J18*J09*I03^2 - 12086478080921909472349409280000*J18*I09*I06 +
        634533784662723930629904394800*J18*I09*I03^2 + 1376360662530079143672443426304000*J18*I06^2*I03 - 11973144479133529867107185568000*J18*I06*I03^3 + 394548895778667223418112960000*J18*I03^5 -
        4032410391766651291931520000*I18*I15 + 32926769131710742096038552000*I18*J12*I03 + 119227746739283373062463984000*I18*I12*I03 + 5390884648192927593835560960000*I18*J09*I06 +
        91557881115170236673431442400*I18*J09*I03^2 + 1299332237347032082955712000000*I18*I09*I06 - 42405519823895698150782880800*I18*I09*I03^2 - 888102837484729926554461381632000*I18*I06^2*I03 +
        1038471404240345107011005376000*I18*I06*I03^3 - 28807802891170076156826240000*I18*I03^5 - 35495596890047430461162880000*J15*I15*I03 + 16456981853000692929472372224000*J15*J12*I06 +
        957745795362316648527652192800*J15*J12*I03^2 + 41590072302320850768180209664000*J15*I12*I06 + 122710906762451349479747668800*J15*I12*I03^2 - 488172894824881461058528089600*J15*J09^2 -
        58783748542790548160704262400*J15*J09*I09 + 19128986753043571888111242854400*J15*J09*I06*I03 + 499496256870933129067464921360*J15*J09*I03^3 - 1647148376488715256119846400*J15*I09^2 +
        14800803778445675242703725209600*J15*I09*I06*I03 - 601051202197629846366290494320*J15*I09*I03^3 - 64617193240260153347135492112384000*J15*I06^3 -
        115952731400580177063908770099200*J15*I06^2*I03^2 - 7870906762173173335020765984000*J15*I06*I03^4 - 403220459413138504266789004800*J15*I03^6 + 3132459330905229204055680000*I15^2*I03 +
        3591219433158084300630730848000*I15*J12*I06 - 117745177547405900226337142400*I15*J12*I03^2 - 16896120488451817687479569472000*I15*I12*I06 - 127443499841000981353361990400*I15*I12*I03^2 -
        256314939353991195564396787200*I15*J09^2 + 100372668592393086435867283200*I15*J09*I09 + 44414180637077028005618437756800*I15*J09*I06*I03 - 351372709403648660378077318080*I15*J09*I03^3 +
        12548263745045705242521715200*I15*I09^2 - 23086631726082751108247018524800*I15*I09*I06*I03 + 190868444710036034852908992960*I15*I09*I03^3 - 4525947929517166773985917063168000*I15*I06^3 +
        227142687472714611830195779737600*I15*I06^2*I03^2 - 3225920872530683153213021376000*I15*I06*I03^4 + 94752516255124209747613286400*I15*I03^6 - 360779860618974325952666460000*J12^2*J09 +
        1391798790831703877036568000*J12^2*I09 + 3235785452142244685168251032000*J12^2*I06*I03 - 33476029370687978737398987300*J12^2*I03^3 + 1596604434580675933457187528000*J12*I12*J09 -
        19870593724734476391788400000*J12*I12*I09 - 27835402902219503132097455424000*J12*I12*I06*I03 + 345725013186919677524268938400*J12*I12*I03^3 - 76287960471674012744731041000*J12*J09^2*I03 +
        664615628710441432045533527400*J12*J09*I09*I03 + 785815556310047841915088813824000*J12*J09*I06^2 - 36806063177973009811380291849600*J12*J09*I06*I03^2 +
        177023735549776599029221687200*J12*J09*I03^4 - 73563080833435853291347321200*J12*I09^2*I03 - 265940512047084431950526536704000*J12*I09*I06^2 -
        17063113431507261294647748715200*J12*I09*I06*I03^2 + 31109514801743011784372730900*J12*I09*I03^4 + 16551135278124273585968870739456000*J12*I06^3*I03 -
        351929559984621851150748777024000*J12*I06^2*I03^3 + 3657903785713238233991205466800*J12*I06*I03^5 + 15945122831912788740109732800*J12*I03^7 - 1757135172325762484085563712000*I12^2*J09 +
        63029043246001596418170432000*I12^2*I09 + 113747686150701644302482706464000*I12^2*I06*I03 - 82448335463406706964804986800*I12^2*I03^3 - 65293882730443683552535412400*I12*J09^2*I03 -
        871876037186061253846032834000*I12*J09*I09*I03 - 1834120993256416612444418717184000*I12*J09*I06^2 + 102278023300659499117531663824000*I12*J09*I06*I03^2 -
        51653285519098678700776835400*I12*J09*I03^4 + 10415023351236532993269967200*I12*I09^2*I03 + 538388796811761336866058289152000*I12*I09*I06^2 +
        5322573738553572222318163929600*I12*I09*I06*I03^2 - 230688789466259054744208158400*I12*I09*I03^4 - 96252390323277606980935280280576000*I12*I06^3*I03 +
        396240891496553699043131730816000*I12*I06^2*I03^3 - 20532224419812418146787407031200*I12*I06*I03^5 - 134904270086065061952817507200*I12*I03^7 + 1304931811678710020453446041600*J09^3*I06 +
        42625163707500647728438445700*J09^3*I03^2 - 4956471583202575966210855372800*J09^2*I09*I06 - 642924231703771521201499897804800*J09^2*I06^2*I03 +
        29883760281114760814173835026320*J09^2*I06*I03^3 - 129395052697175642676638608983*J09^2*I03^5 + 5066254702861088189606152473600*J09*I09^2*I06 - 245553424870452251832799149420*J09*I09^2*I03^2
        - 320744129117172975894680714649600*J09*I09*I06^2*I03 - 728732390916558570625969905600*J09*I09*I06*I03^3 - 73249532189416119040719112548*J09*I09*I03^5 -
        182059884716108961588179802292224000*J09*I06^4 + 16230834033659522626987757323008000*J09*I06^3*I03^2 - 696805703284720323691912903476480*J09*I06^2*I03^4 +
        957173259174935806540007384760*J09*I06*I03^6 + 5894284981711582141198359840*J09*I03^8 - 746077566341552677996451788800*I09^3*I06 + 45739840651872676691574066840*I09^3*I03^2 +
        113086850689829800268430165964800*I09^2*I06^2*I03 + 7811940278850172081375354207920*I09^2*I06*I03^3 + 13714645357669555226208606003*I09^2*I03^5 +
        831456693472262375406297190957056000*I09*I06^4 - 12552139252081966617403527701145600*I09*I06^3*I03^2 + 173357838331368084600896220168960*I09*I06^2*I03^4 +
        3353111544246189756603757553880*I09*I06*I03^6 - 7693299254094036696807230880*I09*I03^8 - 1283166943034812231824571635007488000*I06^5*I03 - 299439261847107741913158809633587200*I06^4*I03^3 +
        1088447760091449524562533024716800*I06^3*I03^5 - 5045267910167428895019144316800*I06^2*I03^7 - 154275759830228851961164972800*I06*I03^9 + 45944072172508859596800000*I03^11,
        32112640000*I03^10 - 66555486224640*I03^8*I06 - 9076774934162880*I03^6*I06^2 + 22583006106716160*I03^4*I06^3 -
        130223370389369241600*I03^2*I06^4 + 531784836556259328000*I06^5 - 3382315506144*I03^7*I09 + 1077956992533816*I03^5*I06*I09 +
        205661983727664000*I03^3*I06^2*I09 + 1185269145351782400*I03*I06^3*I09 + 7058426435424*I03^4*I09^2 +
        2135254291594560*I03^2*I06*I09^2 - 2138201220556800*I06^2*I09^2 + 8122334875200*I03*I09^3 + 2950199325792*I03^7*J09 +
        867619576549872*I03^5*I06*J09 - 226091839022720640*I03^3*I06^2*J09 + 3563426243991398400*I03*I06^3*J09 -
        34355530329993*I03^4*I09*J09 - 7315112489298480*I03^2*I06*I09*J09 - 118476834029568000*I06^2*I09*J09 -
        54430601437800*I03*I09^2*J09 - 60049454252427*I03^4*J09^2 + 8685718929802800*I03^2*I06*J09^2 - 10597393208908800*I06^2*J09^2
        + 115042393802700*I03*I09*J09^2 - 44376658080300*I03*J09^3 - 57147479199360*I03^6*I12 - 15159547534923360*I03^4*I06*I12 -
        844564511894054400*I03^2*I06^2*I12 - 11562417152778240000*I06^3*I12 - 88392339534240*I03^3*I09*I12 +
        1606205443392000*I03*I06*I09*I12 + 46707097651200*I09^2*I12 + 6279516435060*I03^3*J09*I12 + 26402654032430400*I03*I06*J09*I12
        - 152683833859200*I09*J09*I12 + 80282894428800*J09^2*I12 - 356524891632000*I03^2*I12^2 - 32643904670208000*I06*I12^2 +
        6329705912640*I03^6*J12 + 2522034688209840*I03^4*I06*J12 + 102066292602028800*I03^2*I06^2*J12 + 18464999583744000*I06^3*J12 +
        17536397039280*I03^3*I09*J12 - 3099722006131200*I03*I06*I09*J12 - 20576765664000*I09^2*J12 + 72494830948950*I03^3*J09*J12 -
        6073634354580000*I03*I06*J09*J12 + 56809310796000*I09*J09*J12 - 38825307990000*J09^2*J12 + 202735053964800*I03^2*I12*J12 +
        14849862969600000*I06*I12*J12 - 17710443223200*I03^2*J12^2 - 637384038912000*I06*J12^2 + 41096038072320*I03^5*I15 +
        2815074492894720*I03^3*I06*I15 + 30559394894515200*I03*I06^2*I15 + 48584490534720*I03^2*I09*I15 + 797646615091200*I06*I09*I15
        - 176367483915840*I03^2*J09*I15 + 1328192526729600*I06*J09*I15 + 107043565305600*I03*I12*I15 - 27324727920000*I03*J12*I15 +
        1249949232000*I15^2 - 169426911306240*I03^5*J15 - 21111323405639040*I03^3*I06*J15 - 407975116643942400*I03*I06^2*J15 -
        130462741160640*I03^2*I09*J15 + 1701486447897600*I06*I09*J15 + 358208149657680*I03^2*J09*J15 + 8244751158604800*I06*J09*J15 -
        729525565843200*I03*I12*J15 + 299242940976000*I03*J12*J15 - 154180980576000*I15*J15 - 17146651536000*J15^2 -
        11700484992000*I03^4*I18 - 56510050464000*I03^2*I06*I18 - 39672462735360000*I06^2*I18 - 11049668784000*I03*I09*I18 +
        36338360940000*I03*J09*I18 - 66584597184000*I12*I18 + 27384249312000*J12*I18 + 169298434368000*I03^4*J18 +
        12699076365360000*I03^2*I06*J18 + 284717324795904000*I06^2*J18 + 116139609734400*I03*I09*J18 - 335414782861200*I03*J09*J18 +
        648941896512000*I12*J18 - 279578591712000*J12*J18 + 193995648000000*I03^3*I21 - 15350170187520000*I03*I06*I21 +
        61836112800000*J09*I21 - 30030134400000*I03^3*J21 + 1394498034720000*I03*I06*J21 + 4680879840000*I09*J21 +
        3133139940000*J09*J21
        ],
        [ 14, 13, 12, 12, 11, 10];

end function;

/* Genus 1 invariant in the (1nn)  or lower types */
/* (4*a02*a22-a12^2)*(4*a02*a20-a11^2) <> 0 */

function NodeGenus1FromDO(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    q2 := 2^19*3^3*(8*I03^4+14418*I03^2*I06+117*I03*I09-423*I03*J09-155520*I06^2+486*I12);

    q3 := 2^26 * 3^4 / 5 / 7 * (62720*I03^6+36764280*I03^4*I06+266481*I03^3*I09-1527453*I03^3*J09+7357573440*I03^2*I06^2+6206220*I03^2*I12-400950*I03^2*J12-289325520*I03*I06*I09-247160160*I03*I06*J09-135992908800*I06^3-2143260*I03*I15+40041540*I03*J15+1143538560*I06*I12+76982400*I06*J12-2506140*I09^2+8323560*I09*J09+2664900*J09^2+1224720*I18-40415760*J18);

    d6 := (4*q2^3 - q3^2) / 27;

    return [q2, q3, d6], [2, 3, 6];

end function;

/* Retreive so-called Node Dihedral Invariants from Dixmier-Ohno invariants */

function NodeDihedInvsFromDOByGroebner(DO : p := 0)

    K := Universe(DO); FF := K; _DO := DO;
    if Type(K) in {RngInt, FldRat} then

        K := Integers(); FF := GF(p);

        WG := [ 1, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 9 ];
        _DO := WPSMinimizePPowers(WG, DO, p);

        _DO := ChangeUniverse(_DO, K);

        assert Valuation(_DO[#_DO], p) gt 0;

    end if;

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(_DO);


    Pj6j3 := PolynomialRing(K, [6, 3]);
    j6 := Pj6j3.1; j3 := Pj6j3.2;

    SYSDO := [
        55636875*j3^5-2576448000*j3^4*I03-3074400*j3^3*j6+(45287424000*I03^2+496419840000*I06)*j3^3+59351040*j6*j3^2*I03+(-377348751360*I03^3-8695185408000*I03*I06+71066419200*I09-148403404800*J09)*j3^2-62720*j3*j6^2+(-330301440*I03^2-17464688640*I06)*j3*j6+(1498247331840*I03^4+43609699123200*I03^2*I06-1181971906560*I03*I09+2057223536640*I03*J09+288947699712000*I06^2+34398535680*I12+257989017600*J12)*j3+(550502400*I03^3+107017666560*I03*I06+693633024*I09-346816512*J09)*j6-2283043553280*I03^5-60786034606080*I06*I03^3+4448877281280*I03^2*I09-6833842421760*I03^2*J09-1684886142320640*I03*I06^2-183458856960*I03*I12-1375941427200*I03*J12+215747615784960*I06*I09-107873807892480*I06*J09-17978967982080*J15,
        10583409375*j3^6-523950525000*I03*j3^5-1568133000*j3^4*j6+(10140144084000*I03^2+41978502720000*I06)*j3^4+47364307200*I03*j3^3*j6+65049600*j3^2*j6^2+(-98296121548800*I03^3-1178991894528000*I03*I06+5857754112000*I09-177666048000*J09)*j3^3+(-505191859200*I03^2-3682215936000*I06)*j3^2*j6-784680960*I03*j3*j6^2-501760*j6^3+(508731516518400*I03^4+13472888802508800*I03^2*I06-132171595776000*I03*I09-35626372300800*I03*J09+69564158705664000*I06^2-375116031590400*I12+30958682112000*J12)*j3^2+(2350796636160*I03^3+57744949248000*I03*I06-373447065600*I09-69115576320*J09)*j3*j6+(2361139200*I03^2+59082670080*I06)*j6^2+(-1346900569620480*I03^5-66057724860825600*I06*I03^3+900981734768640*I03^2*I09+324370547343360*I03^2*J09-1388335907576217600*I03*I06^2+6125691233894400*I03*I12-577895399424000*I03*J12-12675172427366400*I06*I09+17259809262796800*I06*J09+1213580338790400*I15)*j3+(-4176331407360*I03^4-150573856849920*I03^2*I06+4242825805824*I03*I09-2293405581312*I03*J09-1987960174018560*I06^2+13209037701120*I12-2063912140800*J12)*j6-4386868187627520*J09^2-7766914168258560*I18+112753813487616000*I03^4*I06-26523747703848960*I03^2*I12+2688039172177920*I03^2*J12-728935037927424*J09*I03^3-1287088633597132800*I06*I12+210816241709875200*I06*J12-3883457084129280*I03*I15+2283102912412385280*I03^2*I06^2-2013644413992960*I09^2+9780558582251520*I09*J09-1977580479578112*I09*I03^3-189734617538887680*I09*I03*I06+109846357522513920*J09*I03*I06+1439332124590080*I03^6-11805709535753011200*I06^3,
        -1993359375*j3^6+606848760000*I03*j3^5+85050000*j3^4*j6+(-25031439720000*I03^2+27423930240000*I06)*j3^4-22904985600*I03*j3^3*j6+18144000*j3^2*j6^2+(417454597324800*I03^3+1548579078144000*I03*I06-28123490304000*I09+50885646336000*J09)*j3^3+(298217687040*I03^2-5806544486400*I06)*j3^2*j6-1439907840*I03*j3*j6^2-1003520*j6^3+(-3361063722024960*I03^4-17363950829568000*I03^2*I06+1376242414387200*I03*I09-2528034383462400*I03*J09+263953723686912000*I06^2-599050498867200*I12+58047528960000*J12)*j3^2+(-396114001920*I03^3+108194860892160*I03*I06+1999892643840*I09-3618534850560*J09)*j3*j6+(5806080000*I03^2+274232770560*I06)*j6^2+(13001362275041280*I03^5-6819165713203200*I06*I03^3-16108421476515840*I03^2*I09+25792297241149440*I03^2*J09-8005469389140787200*I03*I06^2+12750023641006080*I03*I12+965910881894400*I03*J12-93619054706688000*I06*I09+168514298472038400*I06*J09)*j3+(-4019107921920*I03^4+62284281937920*I03^2*I06+4057498386432*I03*I09-2372734550016*I03*J09-15996144656056320*I06^2+26418075402240*I12-4127824281600*J12)*j6-139804455028654080*J18+326765174650306560*I03^4*I06-51594501260574720*I03^2*I12-76713687955537920*J09*I03^3-456504342950707200*I06*I12+770351078729318400*I06*J12-8321693751705600*I03^2*J12+10032633987056271360*I03^2*I06^2-31067656673034240*I09^2+100969884187361280*I09*J09+54953999849226240*I09*I03^3-42718027925422080*J09^2-906351330900049920*I09*I03*I06+796980498734776320*J09*I03*I06-19369341506027520*I03^6-43139660408841830400*I06^3,
        2441174203125*j3^7-152692476300000*I03*j3^6-999030847500*j3^5*j6+(3888661475160000*I03^2+10066169635200000*I06)*j3^5+38254349952000*I03*j3^4*j6+101651088000*j3^3*j6^2+(-51972010425216000*I03^3-347054373550080000*I03*I06+2031977041920000*I09+1270338370560000*J09)*j3^4+(-540634639104000*I03^2-2603316215808000*I06)*j3^3*j6-1861141094400*I03*j3^2*j6^2-3054464000*j3*j6^3+(389621184351436800*I03^4+2802895022850048000*I03^2*I06-80361476849664000*I03*I09-29538858663936000*I03*J09-62724766653480960000*I06^2-97430842441728000*I12+9268255457280000*J12)*j3^3+(3606042530119680*I03^3+22668816560947200*I03*I06-674365508812800*I09+253909632614400*J09)*j3^2*j6+(10405223055360*I03^2+121689243648000*I06)*j3*j6^2+(-1633279583736299520*I03^5+4403124171177984000*I06*I03^3+1187677438790860800*I03^2*I09+271277057271398400*I03^2*J09+442376616677474304000*I03*I06^2+2570833729526169600*I03*I12-286718674599936000*I03*J12+1307392025296896000*I06*I09+41680320419856384000*I06*J09+145629640654848000*I15)*j3^2+(-11204291230433280*I03^4-29064357300142080*I03^2*I06+9499979069521920*I03*I09-3274951659356160*I03*J09+2431038997816934400*I06^2+21781840763289600*I12-840356226662400*J12)*j3*j6+(-9575301120000*I03^3-33195294720000*I03*I06+33641201664000*I09-16820600832000*J09)*j6^2+(3559402896862740480*I03^6-98997505785593856000*I03^4*I06-6845074180669440000*I09*I03^3-1506214990766407680*J09*I03^3-4035507373829888409600*I03^2*I06^2-16565480599049994240*I03^2*I12+1702644959674368000*I03^2*J12-13824226616986828800*I09*I03*I06-181051172274674073600*J09*I03*I06-22216925110553542656000*I06^3-6058193051241676800*I03*I15-544999611933130752000*I06*I12-43653227794661376000*I06*J12-354853459486310400*I09^2+2793109728736051200*I09*J09-5052603687763968000*J09^2)*j3+(11124129713356800*I03^5-223110811751546880*I06*I03^3-36109061216796672*I03^2*I09+13906984499675136*I03^2*J09-9827406635964825600*I03*I06^2+55488965876121600*I03*I12-5978924148326400*I03*J12+326224093328179200*I06*I09-440501838387609600*I06*J09-124054879076352000*I15)*j6-216725132479619609395200*I03*I06^3-27085924348408627200*I09*I12+18057282898939084800*I09*J12-3127619494462095360*I03^7+10315730083066675200*J09*J12+7825498892270567424000*J09*I06^2+63005207732913438720*I03^2*I15-9848329751683399680*I03*I09^2+13041537449057058816*I03^4*I09+2157709941509455872*I03^4*J09+7859257106638967930880*I03^3*I06^2-6856898121938711347200*I09*I06^2-8483372373167308800*J09*I12-7585063878556385280*I03*I09*J09-449163076813329530880*I09*I03^2*I06+358552882386504253440*J09*I03^2*I06-55921782011461632000*I21+14856868089676431360*I03*J09^2-20418847495296122880*I03^3*I12+2089916333020938240*I03^3*J12+234518069306091110400*I03^5*I06-306162246005607628800*I03*I06*I12+738471858779927347200*I03*I06*J12,
        47106191671875*j3^7-2687665932393750*I03*j3^6-18267174371250*j3^5*j6+(63662883923520000*I03^2+435539041459200000*I06)*j3^5+668416225932000*I03*j3^4*j6+1819406433600*j3^3*j6^2+(-813705582861360000*I03^3-14660780492332800000*I03*I06+34127871160320000*I09+4619839795200000*J09)*j3^4+(-9038056495104000*I03^2-68490940815360000*I06)*j3^3*j6-32306668853760*I03*j3^2*j6^2-53945848320*j3*j6^3+(6007716470181888000*I03^4+161579666549145600000*I03^2*I06-1241730926899200000*I03*I09-62876178616320000*I03*J09-2530098295603200000*I06^2-2170716369223680000*I12+361558708715520000*J12)*j3^3+(57313396199485440*I03^3+665965629923328000*I03*I06-11826614299852800*I09+5863719510835200*J09)*j3^2*j6+(172407731650560*I03^2+2432206114652160*I06)*j3*j6^2+250880000*I03*j6^3+(-25470451718317670400*I03^5-655976422006456320000*I06*I03^3+18906122578467225600*I03^2*I09-986159063944396800*I03^2*J09+80192521944170496000*I03*I06^2+49420969586196480000*I03*I12-9575651951640576000*I03*J12+219149782317268992000*I06*I09+342858694681165824000*I06*J09+546111152455680000*I15)*j3^2+(-169061179061698560*I03^4-1447792782763622400*I03^2*I06+163448236293488640*I03*I09-63748893871964160*I03*J09+17391762045665280000*I06^2+406116198336430080*I12-29121972299366400*J12)*j3*j6+(-171372824985600*I03^3-839781006704640*I03*I06+592436127596544*I09-296218063798272*J09)*j6^2+(57423908614805913600*I03^6+524969555584352256000*I03^4*I06-114916297766495846400*I09*I03^3+9283862378682777600*J09*I03^3-43447452121738248192000*I03^2*I06^2-313271350096350412800*I03^2*I12+65853822571905024000*I03^2*J12-2540295358993819238400*I09*I03*I06-1505177309148925132800*J09*I03*I06-506323803157775253504000*I06^3-38009336210915328000*I03*I15-15999835261190012928000*I06*I12+773061573265588224000*I06*J12-11062921315693363200*I09^2+38122295498322739200*I09*J09-49998277114645708800*J09^2)*j3+(165891826589368320*I03^5-2151823484701900800*I06*I03^3-489672864455196672*I03^2*I09+188967064411570176*I03^2*J09-150424230741525135360*I03*I06^2+960815495601192960*I03*I12-99340769537556480*I03*J12+4900368060587704320*I06*I09-4946692155805532160*I06*J09-2178295802772848640*I15)*j6+440507669933142835200*I09*J12-611829945639685324800*I09*I12+105186157242130995609600*I03^3*I06^2-53235492085510963200*I03^7-221080227589254021120*I03*I09^2+180328725972674150400*J09*J12+136472581997571185049600*J09*I06^2-424638057291033083904000*I03*I06^3+1499161348326555648000*I03^5*I06+229595181793117470720*I03^4*I09-29274344389355765760*I03^4*J09-428201778169774080*I03*I09*J09-49385857165322040115200*I09*I06^2-294958868589025689600*J09*I12-1362542883837994598400*I09*I03^2*I06+8845804063056671539200*J09*I03^2*I06+535451062759745126400*I03^2*I15-69902227514327040000*J21-33462860285403463680*I03*J09^2+70506144718022246400*I03^3*I12-86531217166644019200*I03^3*J12-1509888114309464064000*I06*I15+10859667688368635904000*I03*I06*I12+7700657635149742080000*I03*I06*J12
        ];

    SYSj3 := [
        (172000678263750000*I03^4+309988222400843437500*I03^2*I06+2515509919607343750*I03*I09-9094535863195781250*I03*J09-3343693185447300000000*I06^2+10449041204522812500*I12)*j3^6+
        (-8256032556660000000*I03^5-12011753366888113125000*I06*I03^3-89571503214326109375*I03^2*I09+337794282050656921875*I03^2*J09+27975566318242410000000*I03*I06^2-372682469627980312500*I03*I12+5224520602261406250*I03*J12-292573153726638750000*I06*I09+1839031251996015000000*I06*J09-31347123613568437500*I15-3483013734840937500*J15)*j3^5+
        (163591756215300000000*I03^6+192382483436919153000000*I03^4*I06+1244795445842262300000*I09*I03^3-5112632686759308900000*J09*I03^3+492280802049454488000000*I03^2*I06^2+5061714588827127000000*I03^2*I12-105087500114058000000*I03^2*J12-10152089404958088000000*I09*I03*I06+4216237883364024000000*J09*I03*I06-6355692006898227840000000*I06^3+1203729546761028000000*I03*I15-1292894698372956000000*I03*J15+105756238751147460000000*I06*I12-10317681829380240000000*I06*J12-173067082468985250000*I09^2+983912679939955500000*I09*J09-1295061906919079250000*J09^2)*j3^4+
        (-1703988904302720000000*I03^7-1609251598592237779200000*I03^5*I06-7720030185448180320000*I03^4*I09+39154377736901921760000*I03^4*J09-4799457108061445491200000*I03^3*I06^2-24033364489746460800000*I03^3*I12-381490286456260800000*I03^3*J12+199696749434880352200000*I09*I03^2*I06-678215030981407302600000*J09*I03^2*I06+340370275686223781376000000*I03*I06^3-22456724188243262400000*I03^2*I15+63857105634346516800000*I03^2*J15-798081851640352356000000*I03*I06*I12-19904787124055946000000*I03*I06*J12+2156978636032059000000*I03*I09^2-16571327692780551600000*I03*I09*J09+28371624684508387800000*I03*J09^2-1768012893217308528000000*I09*I06^2-4949727810776415072000000*J09*I06^2+2599504661445300000000*I03*I18-28619133958002420000000*I03*J18-182084560381964772000000*I06*I15+787413298833790524000000*I06*J15+1323062936517294000000*I09*I12-801186908357556000000*I09*J12-3731821486189146000000*J09*I12+1841040596227644000000*J09*J12+7276954438857600000000*I21)*j3^3+
        (9823854822001920000000*I03^8+7370724158000264819520000*I03^6*I06+16441732056681879192000*I03^5*I09-154295151904965904056000*I03^5*J09-5573411543767614382080000*I03^4*I06^2-24416789376475127520000*I03^4*I12+13739114486336586480000*I03^4*J12-1564000144156046066400000*I03^3*I06*I09+7369372906992605426400000*I03^3*I06*J09-3463938425532072383078400000*I03^2*I06^3+190288983237447558240000*I03^3*I15-740629813686290347680000*I03^3*J15-2899941221096182569600000*I03^2*I06*I12+1848853243990104206400000*I03^2*I06*J12-5159574802426800960000*I03^2*I09^2+92193362594241312960000*I03^2*I09*J09-219017949528922122240000*I03^2*J09^2+20886172865533855756800000*I03*I06^2*I09+41923521524114079897600000*I03*I06^2*J09+4546838807822807580672000000*I06^4-38599988193187344000000*I03^2*I18+418333468252661136000000*I03^2*J18+3002482170118599235200000*I03*I06*I15-7220243901724848086400000*I03*I06*J15-6081806875147228800000*I03*I09*I12+15572312961726772800000*I03*I09*J12-7191733199464425600000*I03*I12*J09-26931445662688574400000*I03*J09*J12+131521724766151501824000000*I06^2*I12-30314082685523696640000000*I06^2*J12-343754523475151443200000*I06*I09^2+467438492420934451200000*I06*I09*J09+173951732786312275200000*I06*J09^2-95735911585466880000000*I21*I03+233169791230861632000000*I06*I18+3602723116619212992000000*I06*J18-11186835107172681600000*I09*I15+142965532449905155200000*I09*J15-43066204443353376000000*I12^2+37059994361267712000000*I12*J12+24628717539898012800000*I15*J09-341267092748588361600000*J09*J15-5566127599354752000000*J12^2)*j3^2+
        (-29704642955796480000000*I03^9-17619416331248487854700000*I03^7*I06+17983665179438195317500*I03^6*I09+279978569544754332472500*I03^6*J09+144727619614111975069440000*I03^5*I06^2+337417865178265188450000*I03^5*I12-53593507035888118425000*I03^5*J12+11123979164497140273864000*I03^4*I06*I09-30151248783324190675272000*I03^4*I06*J09+12995538218112735922775040000*I03^3*I06^3-622102834479926822400000*I03^4*I15+2810476186098394501800000*I03^4*J15+22877714861671429761120000*I03^3*I06*I12-8958357234549243969840000*I03^3*I06*J12-14507231002787897748000*I03^3*I09^2-246528769037733278514000*I03^3*I09*J09+560919685361625135954000*I03^3*J09^2-154758301306691111205120000*I03^2*I06^2*I09+150006632002108910058240000*I03^2*I06^2*J09-29611635061347789366067200000*I03*I06^4+164486292058039014000000*I03^3*I18-1623065393239124121000000*I03^3*J18-21891561530381693075520000*I03^2*I06*I15+28708439300666020304640000*I03^2*I06*J15-279762987427508965824000*I03^2*I09*I12-53431930217055828240000*I03^2*I09*J12+79932547419938799552000*I03^2*I12*J09+337015893462330876840000*I03^2*J09*J12-153863305234710597872640000*I03*I06^2*I12+228433005155241077184000000*I03*I06^2*J12+3909285627206316658560000*I03*I06*I09^2-698825377745623598400000*I03*I06*I09*J09-5044600578618974197440000*I03*I06*J09^2+1891259613149308054732800000*I06^3*I09+518479972243288138137600000*I06^3*J09+762942256049489040000000*I21*I03^2-62515373806504710000000*J21*I03^2+5303011955381187264000000*I03*I06*I18-64531374076898852256000000*I03*I06*J18+283387278707598078720000*I03*I09*I15-1953531536100985693440000*I03*I09*J15-12824606606298485760000*I03*I12^2-14651203591747906560000*I03*I12*J12-485943092808066835200000*I03*I15*J09+3653244222269646009600000*I03*J09*J15+22062910109435827200000*I03*J12^2-47995803076081838745600000*I06^2*I15-50181831812822840524800000*I06^2*J15-16965923852947719444480000*I06*I09*I12+1184939064313337894400000*I06*I09*J12+11036535334695377418240000*I06*I12*J09+1758735238336618348800000*I06*J09*J12+21931392429087805440000*I09^3-112337713634822645760000*I09^2*J09+134020410572620615680000*I09*J09^2-41667200931240622080000*J09^3+18467940105228741120000000*I21*I06-1516382546642389440000000*J21*I06-34741797592092595200000*I09*I18+312676178328833356800000*I09*J18+56797391742891448320000*I12*I15-226224481102874634240000*I12*J15-45779666896493107200000*I15*J12+36436519425853209600000*I18*J09-327928674832678886400000*J09*J18+206219494210541414400000*J12*J15)*j3
        -10064400510139679680537559040000*I06^5+2404637536671447121981440*I03*I09*J09^2+36799636983316480000000*I03^10-88482185252717804126208000*I03*J12*J15-1742418687801726403235020800*I06*I09*I15-2308269713240206749951590400*I06*I09*J15-7840900518893354545053696000*I06*I12*J12+2191932731194101662131814400*I06*I15*J09+7711040287473844359344947200*I06*J09*J15+62819818057697364511948800*I09*I12*J09-118642628730539201762112307200*I06^2*I09*J09+844055411832059948236800*I03*I09*I18-102082136434670320975872000*I03*I12*I15+461835982546047785926656000*I03*I12*J15+18829496741293145456640000*I03*I15*J12+6733853291700749994393600*I03*I18*J09+9736054256110928319696568320*I03^3*I06^2*I09+28668230133226157750706339840*I03^3*I06^2*J09+295279800845103294409728000*I03^3*I06*I15-993054268095081633681408000*I03^3*I06*J15+2768489297323265563361280*I03^3*I09*I12-706834003115036918200320*I03^3*I09*J12+19501320980795214417039360*I03^3*I12*J09-3657510686926221058851840*I03^3*J09*J12-70607161832588221772316672000*I03^2*I06^2*I12+24890944922745358002610176000*I03^2*I06^2*J12+263349294341366193921146880*I03^2*I06*I09^2-2773966456159351626931937280*I03^2*I06*J09^2+2243483063019481187038946918400*I03*I06^3*I09-421041638912947399570961203200*I03*I06^3*J09-142328547811357172342784000*I03^2*I06*I18+4727930606662687346442240*I03^2*I09*I15-21518611137327540046970880*I03^2*I09*J15-53525446070995658096640000*I03^2*I12*J12-15642567068716802141061120*I03^2*I15*J09+63530173124262580707901440*I03^2*J09*J15-19527748972399922634326016000*I03*I06^2*I15-176076536504451214745272320000*I03*I06^2*J15-11705086570164805389680640*I03*I09^2*J09-788669185935593580380282880*I03^2*I06*I09*J09-5724329618312840653376716800*I03*I06*I09*I12+1433420539079195093424537600*I03*I06*I09*J12+4088990566445989614044774400*I03*I06*I12*J09+157859166789457269232435200*I03*I06*J09*J12+17521014511351118537280000*I03^8*I06-69181875420084051912000*I03^7*I09-157191652973299200984000*I03^7*J09-754898797764734114451456000*I03^6*I06^2-160513175158582589280000*I03^6*I12+11805871360322556720000*I03^6*J12+13761743391352835098214400*I09*J09*J12-67300615422758990133550080*I03^5*I06*I09+87942757747639144124759040*I03^5*I06*J09-129683851747096817189376000*I03^4*I06*I12+12781041319632419705088000*I03^4*I06*J12+2302912158629098821550848*I03^4*I09*J09-161433425444495904000000*I03^4*I18+165647730788821302976512000*I03^2*I12^2+4157215920274085019648000*I03^2*J12^2+1234532845907115890688000*I03*I09^3+75497196764123449595965440*I03*J09^3-1837949975542384895453036544000*I06^3*I12+148860859792647915023892480000*I06^3*J12+38371555061884906904538316800*I06^2*I09^2+17642621864675182993499750400*I06^2*J09^2-25719994893997364069007360000*I06^2*I18+26176664950285769037840384000*I06*I12^2+551081748007460599234560000*I06*J12^2-36312573333154048435814400*I09^2*I12+6394611506343812849664000*I09^2*J12+156585355504011527779123200*I12*J09^2-109120405247021450844979200*J09^2*J12+66884743354929505173504000*I12*I18+88354133925714418728960000*I15*J15-18497748728348797501440000*I18*J12+1115228241992906630443008000*I03^2*I06*J18+25405460296553145102336000*I03*I09*J18-69029539072680258680832000*I03*J09*J18+31416890770062635792596992000*I06^2*J18-467774849294686773116928000*I12*J18+77021177955353328549888000*J12*J18+1026650003276375856000000*I03^4*J18+36825417465124491915264000*J21*J09-257600094964486863224832000*I21*J09-11526834513731033161728000*J21*I09+67907386930044481634304000*I21*I09+366993568090789920000000*J21*I03^3-2691574823307928320000000*I21*I03^3-716982670787098305945600000*J21*I06*I03+5122008638896955604664320000*I21*I06*I03-33452691433484966283755520000*I03^4*I06^3+448765742129759631360000*I03^5*I15-2448712315271862299520000*I03^5*J15-460109414778122553758208*I03^4*I09^2-997347954596304767023872*I03^4*J09^2-749708081026838689513734144000*I03^2*I06^4,

        (-96278017500000*I03^4-173517057039375000*I03^2*I06-1408066005937500*I03*I09+5090700175312500*I03*J09+1871644660200000000*I06^2-5848889563125000*I12)*j3^6+
        (4621344840000000*I03^5+6723623491121250000*I06*I03^3+50137981088343750*I03^2*I09-189081602043468750*I03^2*J09-15659426990340000000*I03*I06^2+208610394418125000*I03*I12-2924444781562500*I03*J12+163768907767500000*I06*I09-1029404563110000000*I06*J09+17546668689375000*I15+1949629854375000*J15)*j3^5+
        (-92170155420000000*I03^6-108037958528248875000*I03^4*I06-699324131095340625*I09*I03^3+2876404406202928125*J09*I03^3-345831062483277000000*I03^2*I06^2-2892591543322687500*I03^2*I12+62652747963093750*I03^2*J12+8446130751413250000*I09*I03*I06+668444521500000*J09*I03*I06+4856543564286960000000*I06^3-653320964201062500*I03*I15+341250212177437500*I03*J15-70119830305350000000*I06*I12+5040071692110000000*I06*J12+120812063309437500*I09^2-630250344257625000*I09*J09+699462204087937500*J09^2-11697779126250000*I18+386026711166250000*J18)*j3^4+
        (967965705840000000*I03^7+910147583439429300000*I03^5*I06+4521738570906217500*I03^4*I09-22284937666901227500*I03^4*J09+2901881164285504800000*I03^3*I06^2+17572794713154450000*I03^3*I12-274327762777425000*I03^3*J12-250493830080612300000*I09*I03^2*I06+491864952670200900000*J09*I03^2*I06-86242055089647744000000*I03*I06^3+10306896237631350000*I03^2*I15-19144643711139450000*I03^2*J15+1215892898357634000000*I03*I06*I12-92661653529711000000*I03*I06*J12-2252251621352250000*I03*I09^2+13477363931259900000*I03*I09*J09-17449480124505450000*I03*J09^2-967091273556408000000*I09*I06^2+1072776808702368000000*J09*I06^2-397180048671000000*I03*I18+529489489599000000*I03*J18+101237259670218000000*I06*I15-103745263514886000000*I06*J15-719691934815000000*I09*I12+278072920944000000*I09*J12+2290982190021000000*J09*I12-1005340560336000000*J09*J12)*j3^3+
        (-5641336915200000000*I03^8-4234832863998569280000*I03^6*I06-12928377643371288000*I03^5*I09+89968167331318584000*I03^5*J09+3040234685469868320000*I03^4*I06^2-57637663018578720000*I03^4*I12+2446926771275280000*I03^4*J12+2739984112245122820000*I03^3*I06*I09-6271984114820185860000*I03^3*I06*J09-345254670929861683200000*I03^2*I06^3-65453844729843360000*I03^3*I15+166637228236103520000*I03^3*J15-13038306425376850800000*I03^2*I06*I12+1509846091442854200000*I03^2*I06*J12+16085120996225745000*I03^2*I09^2-113428652793471000000*I03^2*I09*J09+149799527357022495000*I03^2*J09^2+75303376521576033600000*I03*I06^2*I09-13981085007902409600000*I03*I06^2*J09+9230814908911991808000000*I06^4+3482350844616000000*I03^2*I18-9327082590504000000*I03^2*J18-1034861510837624400000*I03*I06*I15-7806736310742709200000*I03*I06*J15-15118889964938100000*I03*I09*I12+405244985038650000*I03*I09*J12-3400418132280900000*I03*I12*J09+21423411556898850000*I03*J09*J12-254853061997087232000000*I06^2*I12+13839817616731008000000*I06^2*J12+632926588161193200000*I06*I09^2-1448754035806450800000*I06*I09*J09-30792297949610400000*I06*J09^2-46353672852480000000*I21*I03-243463537398816000000*I06*I18+4185596386498464000000*I06*J18+10568241573819300000*I09*I15-83261048531327100000*I09*J15-8828051303376000000*I12^2+9845614849248000000*I12*J12-21425652247639500000*I15*J09+141894060801412500000*J09*J15-2640164875776000000*J12^2)*j3^2+
        (17302110801920000000*I03^9+10627149605486170680000*I03^7*I06+23386017141133353000*I03^6*I09-178457773008304629000*I03^6*J09-66339920893829171400000*I03^5*I06^2+413461743962219820000*I03^5*I12-59746500510455430000*I03^5*J12-20410138978984225863000*I03^4*I06*I09+25385560742673117819000*I03^4*I06*J09+4827340123168870782720000*I03^3*I06^3-21125742573075840000*I03^4*I15+328588718756240880000*I03^4*J15+98222533303627112940000*I03^3*I06*I12-17612041057344020070000*I03^3*I06*J12-59184089354267856000*I03^3*I09^2+607952619519265332000*I03^3*I09*J09-177404824132555932000*I03^3*J09^2-701177153579046169200000*I03^2*I06^2*I09+346489010354148626160000*I03^2*I06^2*J09-146815430759750633932800000*I03*I06^4+36240058850436000000*I03^3*I18-875737838267334000000*I03^3*J18+16917298165808288640000*I03^2*I06*I15+61799789605001681520000*I03^2*I06*J15+806580638280472896000*I03^2*I09*I12-153523940770486800000*I03^2*I09*J12+545329438794698112000*I03^2*I12*J09-667096395307378560000*I03^2*J09*J12-871804214483285240640000*I03*I06^2*I12+535093354043420407200000*I03*I06^2*J12-9406769089515005880000*I03*I06*I09^2+10066633957698160500000*I03*I06*I09*J09-24001276358779401780000*I03*I06*J09^2+40120670285112769228800000*I06^3*I09-9967113090474951398400000*I06^3*J09-592354181653920000000*I21*I03^2+169064243103420000000*J21*I03^2-12290005631762460000000*I03*I06*I18+14504542856147610000000*I03*I06*J18-493082802884740320000*I03*I09*I15+1738496278236241440000*I03*I09*J15+1367977853449779840000*I03*I12^2-982825140425578560000*I03*I12*J12+826412759179973280000*I03*I15*J09-2040511311446398560000*I03*J09*J15+112000481595129600000*I03*J12^2-208661817231282441600000*I06^2*I15-3149131201126010956800000*I06^2*J15+25212042656883573120000*I06*I09*I12-43303440369621600000*I06*I09*J12-88773499164717682560000*I06*I12*J09+35838417192995314800000*I06*J09*J12-40096562428258560000*I09^3+207141319728282240000*I09^2*J09-247817066062648320000*I09*J09^2+77135273402785920000*J09^3+55021861062695520000000*I21*I06-9587499771874500000000*J21*I06+62782448481748800000*I09*I18-565042036335739200000*I09*J18-235103381981758080000*I12*I15+980402125176754560000*I12*J15+79006933907596800000*I15*J12-66765308318654400000*I18*J09+600887774867889600000*J09*J18-109500838222809600000*J12*J15)*j3+
        6211199174697200186818560000*I06^5-660710793601972834560*I03*I09*J09^2-21809540300800000000*I03^10+47899547866625236992000*I03*J12*J15+996636259270930463539200*I06*I09*I15+1245646425262962452889600*I06*I09*J15+4320625341487794683904000*I06*I12*J12-1268141512210778019225600*I06*I15*J09-4247902901317276576972800*I06*J09*J15-33996749165862987571200*I09*I12*J09+66001904862451582471372800*I06^2*I09*J09-697448756732384563200*I03*I09*I18+58003367532982437888000*I03*I12*I15-259967670135771838464000*I03*I12*J15-10743813990622863360000*I03*I15*J12-3671863023478709606400*I03*I18*J09-3170394508651145839687680*I03^3*I06^2*I09-17305535725391659023452160*I03^3*I06^2*J09-212642048380757409792000*I03^3*I06*I15+410516771455662988032000*I03^3*I06*J15-4632975720631442142720*I03^3*I09*I12+1207644204319856167680*I03^3*I09*J12-15170305711057121168640*I03^3*I12*J09+4870115021078673644160*I03^3*J09*J12+49351195740120141708288000*I03^2*I06^2*I12-16685571811174861561344000*I03^2*I06^2*J12-127736206156642028037120*I03^2*I06*I09^2+1637973303030406524510720*I03^2*I06*J09^2-1408310677957894037707161600*I03*I06^3*I09+278887847755200112970956800*I03*I06^3*J09+139699867562509718016000*I03^2*I06*I18-865786992618529013760*I03^2*I09*I15+8665799786209876101120*I03^2*I09*J15+33986325599434183680000*I03^2*I12*J12+6465330863486352506880*I03^2*I15*J09-35802817544430542914560*I03^2*J09*J15+12048815616191798298624000*I03*I06^2*I15+110402385147545573376000000*I03*I06^2*J15+5934740357085121935360*I03*I09^2*J09+433621084365428961093120*I03^2*I06*I09*J09+3043416871390650441523200*I03*I06*I09*I12-770792731914662243942400*I03*I06*I09*J12-1971336932481364845465600*I03*I06*I12*J09-237309254766642749644800*I03*I06*J09*J12-12018809052413251200000*I03^8*I06-67268337735881520000*I03^7*I09+149023686907413360000*I03^7*J09+372455818535250463104000*I03^6*I06^2-1749025519326388800000*I03^6*I12+265176201835591200000*I03^6*J12-8372781878457269145600*I09*J09*J12+81537457533354117025920*I03^5*I06*I09-48773936087115700728960*I03^5*I06*J09-220189361751175311936000*I03^4*I06*I12+61616093840171746848000*I03^4*I06*J12-2741862939637680620352*I03^4*I09*J09-233547722718912000000*I03^4*I18-98418668564607879168000*I03^2*I12^2-2787869186633060352000*I03^2*J12^2-561382551189113472000*I03*I09^3-42464383011638467810560*I03*J09^3+1143924267862295215865856000*I06^3*I12-93836525422229488926720000*I06^3*J12-21303092504548548358963200*I06^2*I09^2-9715031678375420918169600*I06^2*J09^2+15267006427576414371840000*I06^2*I18-14557861774809849839616000*I06*I12^2-304959742044754083840000*I06*J12^2+20070137478258446745600*I09^2*I12-3429260971851649536000*I09^2*J12-88168681868677169356800*I12*J09^2+61377812353341325900800*J09^2*J12-37167966544027447296000*I12*I18-49456554114589655040000*I15*J15+10173505725720207360000*I18*J12-691591259115119284992000*I03^2*I06*J18-12173972762799961344000*I03*I09*J18+37751634848467387008000*I03*J09*J18-19346244831640412356608000*I06^2*J18+259399557334713987072000*I12*J18-41486790490459840512000*J12*J18+4790070477124128000000*I03^4*J18-20635121350295214336000*J21*J09+144719585119930963968000*I21*J09+6496103088769577472000*J21*I09-39065365034751799296000*I21*I09-1045689318354240000000*J21*I03^3+5514622931381760000000*I21*I03^3+436431022895928614400000*J21*I06*I03-3067593299278414663680000*I21*I06*I03+1944145127152006410240000*I03^4*I06^3+944192657482905600000*I03^5*I15-4155116076248659200000*I03^5*J15+375085319167743748992*I03^4*I09^2-911998273179753675072*I03^4*J09^2+985910593651834981810176000*I03^2*I06^4,

        (4741632000*I03^6+2779379568000*I03^4*I06+20145963600*I09*I03^3-115475446800*J09*I03^3+556232552064000*I03^2*I06^2+469190232000*I03^2*I12-30311820000*I03^2*J12-21873009312000*I09*I03*I06-18685308096000*J09*I03*I06-10281063905280000*I06^3-162030456000*I03*I15+3027140424000*I03*J15+86451515136000*I06*I12+5819869440000*I06*J12-189464184000*I09^2+629261136000*I09*J09+201466440000*J09^2+92588832000*I18-3055431456000*J18)*j3^3+
        (-94832640000*I03^7-11205893863080*I03^5*I06+1348311597957*I03^4*I09+337415096799*I03^4*J09-4531524138650880*I03^3*I06^2+17753830547580*I03^3*I12-2675362370670*I03^3*J12-233451087027120*I09*I03^2*I06+337044431334960*J09*I03^2*I06+368604008185190400*I03*I06^3-14215824725760*I03^2*I15+33058047622320*I03^2*J15+3190149581745600*I03*I06*I12-789563877746400*I03*I06*J12-1886163715800*I03*I09^2+8234569338660*I03*I09*J09+6876618785820*I03*J09^2-31933912847155200*I09*I06^2+5934527922355200*J09*I06^2+4674964442400*I03*I18-26068110087600*I03*J18+66620310019200*I06*I15+2946121374873600*I06*J15+1354001443200*I09*I12-550572876000*I09*J12+27657165916800*J09*I12-20634578571600*J09*J12-15753328416000*I21+5347556172000*J21)*j3^2+
        (606928896000*I03^8-98851221897120*I03^6*I06-15053006149452*I03^5*I09+6001902502236*I03^5*J09+4411171675008000*I03^4*I06^2-204111305012880*I03^4*I12+28232395818120*I03^4*J12+3657146536740672*I03^3*I06*I09-1553630888160576*I03^3*I06*J09-2731734275728711680*I03^2*I06^3+147592829583360*I03^3*I15-526379572595520*I03^3*J15-37112564936229120*I03^2*I06*I12+7775326411620480*I03^2*I06*J12+28823952251808*I03^2*I09^2-138144334988016*I03^2*I09*J09-92788495897104*I03^2*J09^2+288124488467988480*I03*I06^2*I09-51693483718840320*I03*I06^2*J09+4334302179989913600*I06^4-47890030204800*I03^2*I18+477391765435200*I03^2*J18-488484921576960*I03*I06*I15-26739695126753280*I03*I06*J15-64227256128000*I03*I09*I12+29724454085760*I03*I09*J12-361803176824320*I03*I12*J09+226078780536000*I03*J09*J12-129473852394700800*I06^2*I12+2616782605516800*I06^2*J12+341398479421440*I06*I09^2+171647349350400*I06*I09*J09-171173294530560*I06*J09^2+215070629760000*I21*I03-61304829264000*J21*I03+807078330777600*I06*I18+3829177807257600*I06*J18+14251273021440*I09*I15-10215222958080*I09*J15-162279123148800*I12^2+135613539532800*I12*J12-28058119649280*I15*J09-156500639447040*J09*J15-18284971622400*J12^2)*j3+
        98731275186401280*I03^3*I06*I12-21472183196743680*I03^3*I06*J12+427404243071232*I03^3*I09*J09-833589080134778880*I03^2*I06^2*I09+58261482925056*I03^4*I06*J09-10048690350738432*I03^4*I06*I09+258946197703557120*I03^2*I06^2*J09+794160336936960*I03^2*I06*I15+72747895826350080*I03^2*I06*J15+477041741438976*I03^2*I09*I12-1258815488000*I03^9-8521281699840*I09^3+7701927690240*J09^3+88935418885570560*I03*I06^2*I12+107143354987315200*I03*I06^2*J12-4626052672389120*I03*I06*I09^2-6654871857070080*I03*I06*J09^2-7641763695820800*I03*I06*I18-186676015841280*I03*I09*I15+380413943562240*I03*I09*J15-956778070671360*I03*I12*J12+346737239654400*I03*I15*J09+262701616988160*I03*J09*J15-179309824727040*I03^2*I09*J12+1230549620170752*I03^2*I12*J09-727767971804160*I03^2*J09*J12+6913073715609600*I06*J09*J12+5307337170616320*I03*I06*I09*J09+454060957754880*I03^7*I06+40417660784448*I03^6*I09-25126890790464*I03^6*J09+19245589369896960*I03^5*I06^2+535793819109120*I03^5*I12-73062793514880*I03^5*J12+5408050162239406080*I03^3*I06^3-376538733527040*I03^4*I15+1459319472737280*I03^4*J15-65980368889344*I03^3*I09^2+350224351706880*I03^3*J09^2-26326602816159744000*I03*I06^4+106283749017600*I03^3*I18+9313015519877529600*I06^3*I09-2417972140729958400*I06^3*J09+1319362285731840*I03*I12^2+117836483788800*I03*J12^2-48174805234483200*I06^2*I15-705184084839628800*I06^2*J15+39328992460800*I09^2*J09-32938031185920*I09*J09^2+13273534955520*I09*I18-156031757844480*I12*I15+832169375170560*I12*J15+24379962163200*I15*J12-6636767477760*I18*J09-11948890344652800*I03*I06*J18-1402126472678400*I03^3*J18-119461814599680*I09*J18+59730907299840*J09*J18-2167107747840000*J21*I06+15603175784448000*I21*I06+214982449920000*J21*I03^2-987896383488000*I21*I03^2+2708884684800*J12*J15-2312303966945280*I06*I09*I12+216710774784000*I06*I09*J12-11326388644085760*I06*I12*J09
    ];



     if Type(K) in {RngInt, FldRat} then
         /* To be done : take care of the case where j3 =0 is solution (2, 3, or 4 solutions in j6... ) */

        GB := GroebnerBasis(SYSj3);

        Px := PolynomialRing(Rationals()); x := Px.1;

        EQj3 := [ E : E in GB | Degree(E, j3) eq 1 and Degree(E, j6) eq 0];
        if #EQj3 eq 0 then
            GB := GroebnerBasis(SYSj3 cat SYSDO);

            EQj3 := [ E : E in GB | Degree(E, j3) eq 1 and Degree(E, j6) eq 0];
        end if;

        EQj3 := EQj3[#EQj3];
        j3 := Roots(Evaluate(EQj3, [0, x]))[1, 1];

        GB := GroebnerBasis([ Resultant(E, EQj3, 2) : E in SYSDO]);

        EQj6 := [ E : E in GB | Degree(E, j6) eq 1]; EQj6 := EQj6[#EQj6];
        j6 := Roots(Evaluate(EQj6, [x, j3]))[1, 1];

        j15 := 1719926784/125*I15-6771/700*j3^3*j6+42/125*j3*j6^2+10098432/175*j3^2*I09-1876608/175*j3^2*J09-76896/35*j3^4*I03+928908/35*j3^3*I03^2-62208/7*j3^3*I06-132049728/875*j3^2*I03^3-2322432/625*j6*I09+1161216/625*j6*J09+175104/175*j6*I03^3-11878244352/6125*j3*I12-259780608/1225*j3*J12+3726508032/35*j3*I06^2+377413632/875*j3*I03^4+47279407104/30625*I03^2*I09-15338668032/30625*I03^2*J09-9937354752/125*I06*I09+4968677376/125*I06*J09+6412566528/175*I06*I03^3-40418279424/6125*I03*I12+5876416512/6125*I03*J12-55037657088/875*I03*I06^2-3981312/875*I03*j6*I06+73903104/35*j3^2*I03*I06-779712/875*j6*j3*I03^2+20256/125*j6*j3^2*I03-4534272/875*j6*j3*I06-3106584576/6125*j3*I03*I09+1068816384/6125*j3*I03*J09-2882469888/175*j3*I03^2*I06+56295/896*j3^5-431161344/875*I03^5;
        j12 := -573308928/49*I12+89579520/49*J12-1395/56*j3^2*j6-45225/7*j3^3*I03+563760/7*j3^2*I03^2-2985984/7*j3*I03^3-6912/7*j6*I03^2+3304800/7*j3^2*I06+147308544/7*I03^2*I06-124416/7*j6*I06+622080/7*j3*I09+622080/7*j3*J09-94556160/49*I03*I09+54743040/49*I03*J09-716636160/7*I06^2+320625/1792*j3^4+1/3*j6^2+5750784/7*I03^4+2448/7*j3*j6*I03-12441600*j3*I03*I06;
        k12 := 107495424/245*I12-71663616/245*J12+9/7*j3^2*j6+7992/7*j3^3*I03-89748/7*j3^2*I03^2+405504/7*j3*I03^3+192/7*j6*I03^2-2161728/7*j3^2*I06-123420672/35*I03^2*I06+27648/7*j6*I06-1078272/35*j3*I09+2405376/35*j3*J09+248168448/1225*I03*I09-153944064/1225*I03*J09+573308928/35*I06^2-3915/112*j3^4-589824/7*I03^4-96/7*j3*j6*I03+1990656*j3*I03*I06;
        j9 := -55296/5*I09+27648/5*J09+j3*j6+126*j3^2*I03-1152*j3*I03^2+20736*j3*I06-45/16*j3^3+3072*I03^3;
        k9 := -62208*I09+124416*J09+3/4*j3*j6+6075/4*j3^2*I03-12960*j3*I03^2-388800*j3*I06-3375/64*j3^3+34560*I03^3+12*j6*I03+248832*I03*I06;
        k6:= 9/4*j3^2-36*j3*I03+144*I03^2+20736*I06;
        k3 := 72*I03-9/2*j3;

        return [ [j3, k3, j6, k6, j9, k9, j12, k12, j15] ], [ w div 3 : w in [3, 3, 6, 6, 9, 9, 12, 12, 15]];

    end if;

    PJ6J3 := PolynomialRing(FF, [6, 3]); J6 := PJ6J3.1; J3 := PJ6J3.2;
    GBp := GroebnerBasis(ChangeUniverse(SYSDO, PJ6J3));
    V := Variety(ideal<PJ6J3|GBp>);

    RES := [];
    for v in V do
        j6, j3 := Explode(v);

        j15 := 1719926784/125*I15-6771/700*j3^3*j6+42/125*j3*j6^2+10098432/175*j3^2*I09-1876608/175*j3^2*J09-76896/35*j3^4*I03+928908/35*j3^3*I03^2-62208/7*j3^3*I06-132049728/875*j3^2*I03^3-2322432/625*j6*I09+1161216/625*j6*J09+175104/175*j6*I03^3-11878244352/6125*j3*I12-259780608/1225*j3*J12+3726508032/35*j3*I06^2+377413632/875*j3*I03^4+47279407104/30625*I03^2*I09-15338668032/30625*I03^2*J09-9937354752/125*I06*I09+4968677376/125*I06*J09+6412566528/175*I06*I03^3-40418279424/6125*I03*I12+5876416512/6125*I03*J12-55037657088/875*I03*I06^2-3981312/875*I03*j6*I06+73903104/35*j3^2*I03*I06-779712/875*j6*j3*I03^2+20256/125*j6*j3^2*I03-4534272/875*j6*j3*I06-3106584576/6125*j3*I03*I09+1068816384/6125*j3*I03*J09-2882469888/175*j3*I03^2*I06+56295/896*j3^5-431161344/875*I03^5;
        j12 := -573308928/49*I12+89579520/49*J12-1395/56*j3^2*j6-45225/7*j3^3*I03+563760/7*j3^2*I03^2-2985984/7*j3*I03^3-6912/7*j6*I03^2+3304800/7*j3^2*I06+147308544/7*I03^2*I06-124416/7*j6*I06+622080/7*j3*I09+622080/7*j3*J09-94556160/49*I03*I09+54743040/49*I03*J09-716636160/7*I06^2+320625/1792*j3^4+1/3*j6^2+5750784/7*I03^4+2448/7*j3*j6*I03-12441600*j3*I03*I06;
        k12 := 107495424/245*I12-71663616/245*J12+9/7*j3^2*j6+7992/7*j3^3*I03-89748/7*j3^2*I03^2+405504/7*j3*I03^3+192/7*j6*I03^2-2161728/7*j3^2*I06-123420672/35*I03^2*I06+27648/7*j6*I06-1078272/35*j3*I09+2405376/35*j3*J09+248168448/1225*I03*I09-153944064/1225*I03*J09+573308928/35*I06^2-3915/112*j3^4-589824/7*I03^4-96/7*j3*j6*I03+1990656*j3*I03*I06;
        j9 := -55296/5*I09+27648/5*J09+j3*j6+126*j3^2*I03-1152*j3*I03^2+20736*j3*I06-45/16*j3^3+3072*I03^3;
        k9 := -62208*I09+124416*J09+3/4*j3*j6+6075/4*j3^2*I03-12960*j3*I03^2-388800*j3*I06-3375/64*j3^3+34560*I03^3+12*j6*I03+248832*I03*I06;
        k6:= 9/4*j3^2-36*j3*I03+144*I03^2+20736*I06;
        k3 := 72*I03-9/2*j3;

        Append(~RES, [j3, k3, j6, k6, j9, k9, j12, k12, j15]);
    end for;

    return RES, [ w div 3 : w in [3, 3, 6, 6, 9, 9, 12, 12, 15]];

end function;

/* Retreive so-called Node Dihedral Invariants from Dixmier-Ohno invariants.
   In this function, we make use of degree 1 equations to get first j6, then j3,
   and finally the other ones. But these equations can yield nothing (i.e 0=0).
   In these cases, NodeDihedInvsFromDOByGroebner is called (and we can have several solutions)
   */
function NodeDihedInvsFromDO(DO : p := 0)

    K := Universe(DO);

    WG := [ 1, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 9 ];
    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);
    assert p eq 0 or Valuation(I27, p) gt 0;

    Pj6j3 := PolynomialRing(K, [6, 3]);
    j6 := Pj6j3.1; j3 := Pj6j3.2;

    SYSj6 := [

        (-2827839078400000*I03^10+5860876116941798400*I03^8*I06+297846703471040640*I03^7*I09-259794552629243520*I03^7*J09+866255594313005164800*I03^6*I06^2+5032407018295641600*I03^6*I12-557393902667078400*I03^6*J12-90157884329502435600*I03^5*I06*I09-83541606275855637000*I03^5*I06*J09+623957944265297510400*I03^4*I06^3-3618917112648499200*I03^5*I15+14919733809627494400*I03^5*J15+1354726811585925993600*I03^4*I06*I12-223181225018305646400*I03^4*I06*J12-544568213331787554*I03^4*I09^2+2740507496847965439*I03^4*I09*J09+5448248412859306719*I03^4*J09^2-19535115946330575037440*I03^3*I06^2*I09+15063742017821910309120*I03^3*I06^2*J09+11586061431339955789824000*I03^2*I06^4+1030344708395520000*I03^4*I18-14908420130446080000*I03^4*J18-284392724918140339200*I03^3*I06*I15+2002118613077907878400*I03^3*I06*J15+7562589401860937640*I03^3*I09*I12-1439520776142259860*I03^3*I09*J12-3416000003531825220*I03^3*I12*J09-6045104304958111470*I03^3*J09*J12+85130033813336832768000*I03^2*I06^2*I12-13049397049857033600000*I03^2*I06^2*J12-229511511306650230560*I03^2*I06*I09^2+763412780266332683760*I03^2*I06*I09*J09-319089628295295132240*I03^2*I06*J09^2-467351439547229727436800*I03*I06^3*I09-246776914381330500249600*I03*I06^3*J09-45326092985159299891200000*I06^5-17083256762880000000*I03^3*I21+2644453635264000000*I03^3*J21+21283563693869568000*I03^2*I06*I18-1255727811926540736000*I03^2*I06*J18-5198547238880849280*I03^2*I09*I15+15782046697374723360*I03^2*I09*J15+5600360247130656000*I03^2*I12^2-9555914859292368000*I03^2*I12*J12+18175031007594733440*I03^2*I15*J09-42674666613087635280*I03^2*J09*J15+907844753916576000*I03^2*J12^2+433726805952760320000*I03*I06^2*I15+64302696661693077504000*I03*I06^2*J15+777509317612276905600*I03*I06*I09*I12+43551526070035972800*I03*I06*I09*J12-2954740212961458868800*I03*I06*I12*J09+500814562938161421600*I03*I06*J09*J12-921520597093866000*I03*I09^3+6688881068176298880*I03*I09^2*J09-10583087657907772980*I03*I09*J09^2-7865107489610938980*I03*J09^3+1291477975346500558848000*I06^3*I12-23617571414214758400000*I06^3*J12-6038919959668149657600*I06^2*I09^2+29230559285265447782400*I06^2*I09*J09-1895409251000892748800*I06^2*J09^2+513075427569653760000*I03*I06*I21-6318863723088000000*I03*I06*J21+866259919339214400*I03*I09*I18-14425410188645316000*I03*I09*J18+6492763511817408000*I03*I12*I15-8321099066864640000*I03*I12*J15-505800289723680000*I03*I15*J12-4262841842457391200*I03*I18*J09+40420284944723586000*I03*J09*J18-12503080322417664000*I03*J12*J15+7407306344478136320000*I06^2*I18-29768706752730107904000*I06^2*J18+196849331035585401600*I06*I09*I15+252102941743139020800*I06*I09*J15-1226827251123522048000*I06*I12^2-74315428267546368000*I06*I12*J12-453181981677044860800*I06*I15*J09-1956948349665726950400*I06*J09*J15-30400431921216000000*I06*J12^2+1594524008338732800*I09^2*I12+792784443746232000*I09^2*J12+3486244269813782400*I09*I12*J09-7070159148250564800*I09*J09*J12-31472404341807542400*I12*J09^2+20432409110471156400*J09^2*J12-10483256989291968000*I09*I21+1383544816677576000*I09*J21-4619817361268928000*I12*I18+16236975518197056000*I12*J18-110070529369920000*I15^2-12230058818880000*I15*J15+500558835944160000*I18*J12+34740530365784544000*I21*J09-6027135568075188000*J09*J21+12389224298651424000*J12*J18)*j6 +
        626818033452109782528000*I03*I06*I09^3+881958847474108933079040000*I03*I06^2*I21-32597029738860868339236864000*I03*I06^3*J15-3389871094422383250505728000*I03*I06^3*I15-127574556294294301409280000*I03*I06^2*J21+400550183924447168017072128000*I03*I06^4*I09-656234466348367872000*I03^2*I15*J15+77954719907229967872000*I03^2*J12*J18-61560224542273042523750400000*I03*I06^4*J09-569134263994506540288000*I03^2*I12*J18+68618909490968858112000*I03^2*I12*I18+28768859223698047104000*I03^2*J09*J21-200062041390204521472000*I03^2*I21*J09-85082661679207495334400*I03^2*J09^2*J12+144148622084994362227200*I03^2*I12*J09^2-7090437366666476928000*I03^2*I09*J21+36246281659226440704000*I03^2*I09*I21+7169913004575717504000*I03^2*I09^2*J12-48426822845557423027200*I03^2*I09^2*I12+1230415946313471654912000*I03^2*I06*J12^2+61826950778243648578560000*I03^2*I06*I12^2+266761751970331527856128000*I03^2*I06^2*J18-45266839704113501601792000*I03^2*I06^2*I18-398681799933675344705740800*I03^2*I06^2*J09^2+109697539431647038233600000*I03^2*I06^2*I09^2+20520986678587293696000*I03^2*I15^2-466615063327421106600542208000*I03^2*I06^5+60515493538443141525120*I03^3*J09^3+174935337074212320000*I03^3*I09^3+3679259798414247667200*I03^4*J12^2+196912836811485626227200*I03^4*I12^2-6976545505531495595193139200*I03^4*I06^4-18201433569177600000*I03^5*J21+102872266179379200000*I03^5*I21-196171696478177280000*I03^6*J18+2232212217016320000*I03^6*I18-931132562220049426272*I03^6*J09^2-290730396697477960608*I03^6*I09^2-147977656090609496688230400*I03^6*I06^3+185710347183900672000*I03^7*J15+28578942610735104000*I03^7*I15-1086024292883712000*I03^8*J12-37388704991565312000*I03^8*I12-352169221485089956147200*I03^8*I06^2-3888884526649113600*I03^9*J09+2099445836074675200*I03^9*I09+118708280309670912000*I03^10*I06-23008345491898368000000*I21*J15-5732119183962931200000*I15*J21+17196357551888793600000*I15*I21+5751072340691189760000*I12*J12^2-50031756511777751040000*I12^2*J12+107068157554402566144000*J09^2*J18-11736160123538350080000*I18*J09^2-40552025349108252672000*I09*J09^3+17208338505269796864000*I09^2*J18-1270830303893348352000*I09^2*I18+32279041016079040512000*I09^2*J09^2-10280166366755045376000*I09^3*J09-123813774373599313920000*I06*I15^2+101309737760952208588800000*I06^2*J12^2+4961794354288361523118080000*I06^2*I12^2+3776166578698155007672320000*I06^3*J18-3944608723560445142630400000*I06^3*I18+2982427500345794701885440000*I06^3*J09^2+7270703130307724771328000000*I06^3*I09^2+20691879029775082192896000000*I06^4*J12-238026790815911728832839680000*I06^4*I12+45245425254400000*I03^12+115905833475299997696000*I03*I06^2*J09*J12+1145525892164725653098496000*I03*I06^2*I12*J09+312705916739848961021952000*I03*I06^2*I09*J12-1439474758401177350221824000*I03*I06^2*I09*I12-5468932962774301478400*I03^2*I09*J09*J12+160357959498027782592000*I03^2*I09*I12*J09-17865390610460333541888000*I03^2*I06*I12*J12+24891913013049917988249600*I03^2*I06*J09*J15-3326343913588154547916800*I03^2*I06*I15*J09-10497694111838119672012800*I03^2*I06*I09*J15+1467418218694755470438400*I03^2*I06*I09*I15-330021655457078739706675200*I03^2*I06^2*I09*J09-437643046441124423424000*I03^3*I06*J09*J12+7946039254466000020838400*I03^3*I06*I12*J09+1324278853463159487129600*I03^3*I06*I09*J12-7469213233556435871283200*I03^3*I06*I09*I12-50813424686040068505600*I03^4*I06*I09*J09+5503555480209818792656896000*I03^2*I06^3*J12-20784670029629150012669952000*I03^2*I06^3*I12-82357094720304365875200*I03^3*J12*J15+19687183398477910425600*I03^3*I15*J12+555313865096958050764800*I03^3*I12*J15-156764537791567611494400*I03^3*I12*I15-57582360748757723558400*I03^3*J09*J18+5257883261182320921600*I03^3*I18*J09+14219365294109539468800*I03^3*I09*J18+891370834778706508800*I03^3*I09*I18+1550722823477458076160*I03^3*I09*J09^2-4716719829253226736000*I03^3*I09^2*J09-587436110058411694080000*I03^3*I06*J21+4185263724187670691840000*I03^3*I06*I21-416195258091183596106547200*I03^3*I06^2*J15+54696805566595004561817600*I03^3*I06^2*I15+4181773492654055468074598400*I03^3*I06^3*J09+4144596880206200257231257600*I03^3*I06^3*I09-52483857852981454905600*I03^4*I12*J12+57612768299909126115840*I03^4*J09*J15-10842711726320858603520*I03^4*I15*J09-15838556245045290247680*I03^4*I09*J15+1602244580602267607040*I03^4*I09*I15+677259784255605562368000*I03^4*I06*J18-79936628306236434432000*I03^4*I06*I18-2550879622973017783802880*I03^4*I06*J09^2-57337076473222972769280*I03^4*I06*I09^2+29286516257415032426496000*I03^4*I06^2*J12-120001009315428337324032000*I03^4*I06^2*I12-1276784859434756374080*I03^5*J09*J12+10282989056030192113920*I03^5*I12*J09-979294437288221624640*I03^5*I09*J12+6963486369913634319360*I03^5*I09*I12-701655483244677250867200*I03^5*I06*J15+135863171441060784537600*I03^5*I06*I15+36944163495523181650636800*I03^5*I06^2*J09-3908510229819677852160000*I03^5*I06^2*I09+1341797551371407950848*I03^6*I09*J09-1532835146953611648000*I03^6*I06*J12-19512319455289600128000*I03^6*I06*I12+39986362062969463008000*I03^7*I06*J09-22029816338484780268800*I03^7*I06*I09+932814379431567360000*J09*J12*J15-15625558231551894528000*I03^2*I18*J12+15279401811058237440000*I15*J09*J12+73799873260687429632000*I12*J09*J15+7420507248309571584000*I12*I15*J09+1517629026570854400000*I09*J12*J15+4302958030843207680000*I09*I15*J12-11378582646922874880000*I09*I12*J15-21236627052102389760000*I09*I12*I15-84083317667799367680000*I09*J09*J18+8701383544174411776000*I09*I18*J09+13998471539785665085440000*I06*I15*J15+16414962805856552878080000*I06*J12*J18-3362330251427748249600000*I06*I18*J12-91048573557020718858240000*I06*I12*J18+11450342817108243578880000*I06*I12*I18+6001838747686420531200000*I06*J09*J21-40798774050969670041600000*I06*I21*J09-17219206264264358538240000*I06*J09^2*J12+18110665393596148359168000*I06*I12*J09^2-2013840279096678144000000*I06*I09*J21+10872415589429186150400000*I06*I09*I21+1356010221021609646080000*I06*I09^2*J12-7778232498123083243520000*I06*I09^2*I12-1504303809285531020820480000*I06^2*I12*J12+1350295031666646162800640000*I06^2*J09*J15+343539674017161758760960000*I06^2*I15*J09-485381425848378974208000000*I06^2*I09*J15-272615711999520646471680000*I06^2*I09*I15-20041968027697642537943040000*I06^3*I09*J09+69358642125951467520000*I03*I15*J18-8024966857548103680000*I03*I15*I18-3389635526395345920000*I03*J12*J21+30304058768846069760000*I03*I21*J12+35659583448590062080000*I03*I12*J21-250078017218849648640000*I03*I12*I21+12622527811763956224000*I03*J09*J12^2+236228511972674267136000*I03*I12^2*J09-118374186717939098419200*I03*J09^2*J15+35277067387548035481600*I03*I15*J09^2-912011504634270720000*I03*I09*J12^2+9967264044211279872000*I03*I09*I12^2-19635532260025651200000*I03*I09^2*J15+7671462602161139712000*I03*I09^2*I15+10630083651624968596531200*I03*I06*J09^3+1480710861374216371200000*I06*I09*J09*J12+18149177044765014441984000*I06*I09*I12*J09-163795822208652632832000*I03*I12*J09*J12-1152135527799458304000*I03*I09*I12*J12+95462112366553979289600*I03*I09*J09*J15-46210684939195288780800*I03*I09*I15*J09-18072789272454563168256000*I03*I06*J12*J15+4155169268776040460288000*I03*I06*I15*J12+93675461444971977424896000*I03*I06*I12*J15-22965832606969525045248000*I03*I06*I12*I15-17676913865616388002816000*I03*I06*J09*J18+1708727964353586247680000*I03*I06*I18*J09+8015296499573176138752000*I03*I06*I09*J18-294719511524369541120000*I03*I06*I09*I18+4106774167990044687360000*I03*I06*I09*J09^2-4346427568230321228748800*I03*I06*I09^2*J09+218777073323212800000*J12^3+61369349378645606400000*I12^3+13419178559722930176000*J09^4+1153514506493067264000*I09^4-1476490984040259458275737600000*I06^6,

        (45944072172508859596800000*I03^11-154275759830228851961164972800*I03^9*I06-7693299254094036696807230880*I03^8*I09+5894284981711582141198359840*I03^8*J09-5045267910167428895019144316800*I03^7*I06^2-134904270086065061952817507200*I03^7*I12+15945122831912788740109732800*I03^7*J12+3353111544246189756603757553880*I03^6*I06*I09+957173259174935806540007384760*I03^6*I06*J09+1088447760091449524562533024716800*I03^5*I06^3+94752516255124209747613286400*I03^6*I15-403220459413138504266789004800*I03^6*J15-20532224419812418146787407031200*I03^5*I06*I12+3657903785713238233991205466800*I03^5*I06*J12+13714645357669555226208606003*I03^5*I09^2-73249532189416119040719112548*I03^5*I09*J09-129395052697175642676638608983*I03^5*J09^2+173357838331368084600896220168960*I03^4*I06^2*I09-696805703284720323691912903476480*I03^4*I06^2*J09-299439261847107741913158809633587200*I03^3*I06^4-28807802891170076156826240000*I03^5*I18+394548895778667223418112960000*I03^5*J18-3225920872530683153213021376000*I03^4*I06*I15-7870906762173173335020765984000*I03^4*I06*J15-230688789466259054744208158400*I03^4*I09*I12+31109514801743011784372730900*I03^4*I09*J12-51653285519098678700776835400*I03^4*I12*J09+177023735549776599029221687200*I03^4*J09*J12+396240891496553699043131730816000*I03^3*I06^2*I12-351929559984621851150748777024000*I03^3*I06^2*J12+7811940278850172081375354207920*I03^3*I06*I09^2-728732390916558570625969905600*I03^3*I06*I09*J09+29883760281114760814173835026320*I03^3*I06*J09^2-12552139252081966617403527701145600*I03^2*I06^3*I09+16230834033659522626987757323008000*I03^2*I06^3*J09-1283166943034812231824571635007488000*I03*I06^5+373799536031299963923072000000*I03^4*I21-61725354891235978256496000000*I03^4*J21+1038471404240345107011005376000*I03^3*I06*I18-11973144479133529867107185568000*I03^3*I06*J18+190868444710036034852908992960*I03^3*I09*I15-601051202197629846366290494320*I03^3*I09*J15-82448335463406706964804986800*I03^3*I12^2+345725013186919677524268938400*I03^3*I12*J12-351372709403648660378077318080*I03^3*I15*J09+499496256870933129067464921360*I03^3*J09*J15-33476029370687978737398987300*I03^3*J12^2+227142687472714611830195779737600*I03^2*I06^2*I15-115952731400580177063908770099200*I03^2*I06^2*J15+5322573738553572222318163929600*I03^2*I06*I09*I12-17063113431507261294647748715200*I03^2*I06*I09*J12+102278023300659499117531663824000*I03^2*I06*I12*J09-36806063177973009811380291849600*I03^2*I06*J09*J12+45739840651872676691574066840*I03^2*I09^3-245553424870452251832799149420*I03^2*I09^2*J09+42625163707500647728438445700*I03^2*J09^3-96252390323277606980935280280576000*I03*I06^3*I12+16551135278124273585968870739456000*I03*I06^3*J12+113086850689829800268430165964800*I03*I06^2*I09^2-320744129117172975894680714649600*I03*I06^2*I09*J09-642924231703771521201499897804800*I03*I06^2*J09^2+831456693472262375406297190957056000*I06^4*I09-182059884716108961588179802292224000*I06^4*J09-76180440193642261968468768000000*I03^2*I06*I21+11122340913847708708690336320000*I03^2*I06*J21-42405519823895698150782880800*I03^2*I09*I18+634533784662723930629904394800*I03^2*I09*J18-127443499841000981353361990400*I03^2*I12*I15+122710906762451349479747668800*I03^2*I12*J15-117745177547405900226337142400*I03^2*I15*J12+91557881115170236673431442400*I03^2*I18*J09-507894247302734763946114088400*I03^2*J09*J18+957745795362316648527652192800*I03^2*J12*J15-888102837484729926554461381632000*I03*I06^2*I18+1376360662530079143672443426304000*I03*I06^2*J18-23086631726082751108247018524800*I03*I06*I09*I15+14800803778445675242703725209600*I03*I06*I09*J15+113747686150701644302482706464000*I03*I06*I12^2-27835402902219503132097455424000*I03*I06*I12*J12+44414180637077028005618437756800*I03*I06*I15*J09+19128986753043571888111242854400*I03*I06*J09*J15+3235785452142244685168251032000*I03*I06*J12^2+10415023351236532993269967200*I03*I09^2*I12-73563080833435853291347321200*I03*I09^2*J12-871876037186061253846032834000*I03*I09*I12*J09+664615628710441432045533527400*I03*I09*J09*J12-65293882730443683552535412400*I03*I12*J09^2-76287960471674012744731041000*I03*J09^2*J12-4525947929517166773985917063168000*I06^3*I15-64617193240260153347135492112384000*I06^3*J15+538388796811761336866058289152000*I06^2*I09*I12-265940512047084431950526536704000*I06^2*I09*J12-1834120993256416612444418717184000*I06^2*I12*J09+785815556310047841915088813824000*I06^2*J09*J12-746077566341552677996451788800*I06*I09^3+5066254702861088189606152473600*I06*I09^2*J09-4956471583202575966210855372800*I06*I09*J09^2+1304931811678710020453446041600*I06*J09^3+942244479611725373098587936000*I03*I09*I21-98174102358705673359835692000*I03*I09*J21+119227746739283373062463984000*I03*I12*I18-103386223590326074764738792000*I03*I12*J18+3132459330905229204055680000*I03*I15^2-35495596890047430461162880000*I03*I15*J15+32926769131710742096038552000*I03*I18*J12-925351273134289646816034528000*I03*I21*J09+81956922548961269402420436000*I03*J09*J21-960095015436246779564457444000*I03*J12*J18+1208285275196016878775932989440000*I06^2*I21-204635994483204159448408980480000*I06^2*J21+1299332237347032082955712000000*I06*I09*I18-12086478080921909472349409280000*I06*I09*J18-16896120488451817687479569472000*I06*I12*I15+41590072302320850768180209664000*I06*I12*J15+3591219433158084300630730848000*I06*I15*J12+5390884648192927593835560960000*I06*I18*J09+21479306020143695881688563200000*I06*J09*J18+16456981853000692929472372224000*I06*J12*J15+12548263745045705242521715200*I09^2*I15-1647148376488715256119846400*I09^2*J15+63029043246001596418170432000*I09*I12^2-19870593724734476391788400000*I09*I12*J12+100372668592393086435867283200*I09*I15*J09-58783748542790548160704262400*I09*J09*J15+1391798790831703877036568000*I09*J12^2-1757135172325762484085563712000*I12^2*J09+1596604434580675933457187528000*I12*J09*J12-256314939353991195564396787200*I15*J09^2-488172894824881461058528089600*J09^2*J15-360779860618974325952666460000*J09*J12^2+2088377112486985915007064960000*I12*I21-170112170022053858200692720000*I12*J21-4032410391766651291931520000*I15*I18+36291693525899861627383680000*I15*J18-561286838307029492584059840000*I21*J12+78784589597301414463490280000*J12*J21)*j6
        -1995121005271078433232167505987379200*I03*I06*I09*I12*J09-134619963576888956110066483200000*J12^2*J15+17064502425239445140712652800000*I15*J12^2-21774044444662425934059367289241600*I03*I06*I09*J09*J12+673479029049450101553459363840000*I12^2*I15+5661420008672961723399169185792000*J09^2*J21-40265203996826408671507293290496000*I21*J09^2-4854661334398119482031186247680000*I12^2*J15+24509779235470725929274364836249600*I12*J09^3+50286385012022736522528264192000*I09^2*J21-536293069922691806655567200256000*I09^2*I21+5628067187045792721254313984000*I09^3*J12+268462887584267214742408681881600*I09^3*I12+3073203324808174869782654485345075200*I06^2*J09^3-244407022529359987764161972482867200*I06^2*I09^3-15192661761172863239934256732569600000*I06^3*J21+114944941154859680758147671313612800000*I06^3*I21-2942066609126495587494749361332551680000*I06^4*J15-735105154760141753548800000*I03^13-1254733302577649141605643040043008000*I06*I12*J09*J12-17163081875871057049826450029977600*J09^3*J12-337575815358060449136328844525568000*I06*I09*J09*J15-311934563279676118453214847983616000*I06*I09*I15*J09-10012364521716703541329143595008000*I03*J09*J12*J15+3370044543317280951433202368512000*I03*I15*J09*J12+64727711128421451531063115038720000*I03*I12*J09*J15-20096313006534204593612154028032000*I03*I12*I15*J09+302386753483696862420897931264000*I03*I09*J12*J15-433356790657271281645179396096000*I03*I09*I15*J12-5230553769280452272106379161600000*I03*I09*I12*J15+3235596784370950628982674313216000*I03*I09*I12*I15+5977160492564225334965679737856000*I03*I09*J09*J18-85607585068634826375470745600000*I03*I09*I18*J09-2619550549530941449637529133056000*I06*I09*I12*J12-1228534051650154502321725049659392000*I03*I06*J12*J18+276189779574276911031338005708800000*I03*I06*I18*J12+7438804523228658969833647820746752000*I03*I06*I12*J18-964249095421085677769886566916096000*I03*I06*I12*I18-631350346505405601662688549851136000*I03*I06*J09*J21+4432113513518961883087558543638528000*I03*I06*I21*J09+1558123527357369100382268323454566400*I03*I06*J09^2*J12-1223475521489011323512039595115929600*I03*I06*I12*J09^2+170320388981862339029036251164672000*I03*I06*I09*J21-998812629871523363661380598398976000*I03*I06*I09*I21-99356530878870239741666703210086400*I03*I06*I09^2*J12+634750754978939662513069643416780800*I03*I06*I09^2*I12+118058041685980353812098761359253504000*I03*I06^2*I12*J12-144000945383373125606984230780718284800*I03*I06^2*J09*J15-34706135720372059862402165313395097600*I03*I06^2*I15*J09+38965227972238576926651045229992345600*I03*I06^2*I09*J15+26612289566223941896733120251458355200*I03*I06^2*I09*I15+2107932573384176314582060108405279948800*I03*I06^3*I09*J09+2706616596200038321395722704128000*I03^2*I12*J09*J12+1345406268607666460678021137920000*I03^2*I09*I12*J12-6274522249681120184032980738048000*I03^2*I09*J09*J15+1118807887272026696961437813760000*I03^2*I09*I15*J09+1355555834458062424607912591941632000*I03^2*I06*J12*J15-283989972027137340698121558159360000*I03^2*I06*I15*J12-7555895141827801557387338826412032000*I03^2*I06*I12*J15+1525108633046788676911176472492032000*I03^2*I06*I12*I15+1278296614593284189600373528692736000*I03^2*I06*J09*J18-135332324191005581804865853707878400*I03^2*I06*I18*J09-446904936122534415401022441068544000*I03^2*I06*I09*J18+1773653652684351005968452287692800*I03^2*I06*I09*I18-234323177018645438618923693604782080*I03^2*I06*I09*J09^2+265110517380600102483213327271710720*I03^2*I06*I09^2*J09+2430238540353536726556816019702579200*I03^2*I06^2*J09*J12-86516479545687329911223296494086553600*I03^2*I06^2*I12*J09-22555740008619903077486082258908774400*I03^2*I06^2*I09*J12+101550541122714595313647240648475443200*I03^2*I06^2*I09*I12+57187375821226891417668911539200*I03^3*I09*J09*J12-8037009004343880559105127002636800*I03^3*I09*I12*J09+1328687054275711544813666687413248000*I03^3*I06*I12*J12-1424152988462128597387216599121920000*I03*I06*I15*J15+237782472968197747794509131234222080*I03^3*I06*I15*J09+588111996580922098047951816139653120*I03^3*I06*I09*J15-17263754751635441252764695524597760*I03^3*I06*I09*I15+19929988556058020015995479882701291520*I03^3*I06^2*I09*J09+24278305567946974692158723938191360*I03^4*I06*J09*J12-491416949228683594820371430932131840*I03^4*I06*I12*J09-73968558196939506626716683372625920*I03^4*I06*I09*J12+386205336490658518986577369618452480*I03^4*I06*I09*I12+4800318457729198866180470388453888*I03^5*I06*I09*J09-331675598402098355080036995823042560000*I06^4*I15-8171918987487201192135580932762501120000*I06^5*J09+42336436375033111697245528344955453440000*I06^5*I09+98105586826612619581092495360000*I03*J12^3-8874754850356054916723916226560000*I03*I12^3+11132898289860798430324595106232320*I03*J09^4-35260482456094543192716530688000*I03*I09^4+197368900159426647655901195071704268800000*I03*I06^6+4765242215104304540803596288000*I03^3*I15^2+20540109575659653769975234614565797888000*I03^3*I06^5-4008433614634882493018350326049536*I03^4*J09^3-30787492233228939103414470547968*I03^4*I09^3-236739214522176692416493366822400*I03^5*J12^2-12369228999626057870650368207398400*I03^5*I12^2+327931499878292747503375385697150566400*I03^5*I06^4+1927648839480978480159283200000*I03^6*J21-12799971178250606203211366400000*I03^6*I21-283456866613886174499978240000*I03^7*J18-574806633854428012028221440000*I03^7*I18+54820503124613855104780651557312*I03^7*J09^2+16308299583474045352094362344768*I03^7*I09^2+7787501403508398027910338161683660800*I03^7*I06^3+1231686059810668163658464256000*I03^8*J15-1326088547083147611719467008000*I03^8*I15-345344919242678172085435776000*I03^9*J12+3311337336547378434507719424000*I03^9*I12+22257603351586585820690955733478400*I03^9*I06^2-55581585958887214070328332800*I03^10*J09+153410186496945643099524569600*I03^10*I09+1375328740743608286102437376000*I03^11*I06-1708136298797131305716909363201064960*I03^3*I06*J09*J15+1617398820608528298503620362240000*I12*J12*J15-214443913810509027268289003520000*I12*I15*J12+10306453849957951103652939694080000*I15*J09*J15+9140828250778511982224608641024000*J09*J12*J18-2529054062211737100104396881920000*I18*J09*J12-69655962180470771307853026238464000*I12*J09*J18+10009661071573494909547274575872000*I12*I18*J09+792804142304457777204072284160000*I09*I15*J15-105913678385986156173356531712000*I09*J12*J18-6636195387593117554721587200000*I09*I18*J12+4133420659116249200133887803392000*I09*I12*J18-431662389311640319876123508736000*I09*I12*I18-1831679024043404241588846458880000*I09*J09*J21+12281164390792743117352926658560000*I09*I21*J09+3221000631106765199635022502912000*I09*J09^2*J12+8782436668239654102305016584601600*I09*I12*J09^2+541861083637896787584628786790400*I09^2*J09*J12-6110397501640073322695587219046400*I09^2*I12*J09+101931961153430285640523579392000000*I06*I15*J18-8478145905326999091517320806400000*I06*J12*J21+55674158055374064017656509235200000*I06*I21*J12+41598099189447831785842298265600000*I06*I12*J21-256374646650736675301903936716800000*I06*I12*I21+103225606184706205624744454184960000*I06*J09*J12^2+4163010764546360092107423767887872000*I06*I12^2*J09+1199232754879189406527442611018137600*I06*J09^2*J15+380113746355764242939145460536115200*I06*I15*J09^2+3425102958607524536136008417280000*I06*I09*J12^2-190680842984102898893002344923136000*I06*I09*I12^2+6456764789706641184207324109209600*I06*I09^2*J15+12929538376681624284096038318899200*I06*I09^2*I15-2180912895877169683041173813329920000*I06^2*J12*J15-121331700105796069707206709411840000*I06^2*I15*J12+13205589345666186973624842580131840000*I06^2*I12*J15-2759022799858028610957631031377920000*I06^2*I12*I15+7454367138868793950998572286345216000*I06^2*J09*J18-5307317612226784383282423842734080000*I06^2*I18*J09-1756392808008543296568288062865408000*I06^2*I09*J18+717992099634991365303844257792000000*I06^2*I09*I18-19132070129144403576195874943611699200*I06^2*I09*J09^2+6433607326775228184798508604011315200*I06^2*I09^2*J09+81626436769084410136047074878095360000*I06^3*J09*J12-532342484857768541152566999633887232000*I06^3*I12*J09+21959681967003496498166615921786880000*I06^3*I09*J12-23272523508939618652897145658015744000*I06^3*I09*I12+1046206063023932663586865152000000*I03*I21*J15-1331073244442543167822233600000*I03*I15*J21+3993219733327629503466700800000*I03*I15*I21-1609312323446172000347008942080000*I03*I12*J12^2+7784560574388020124097641676800000*I03*I12^2*J12-14971541590722176160164488313856000*I03*J09^2*J18+1516507725181666388902153655500800*I03*I18*J09^2+1578880089403034401409748049244160*I03*I09*J09^3-456402039117431259176366966784000*I03*I09^2*J18+31487113132617555820966190284800*I03*I09^2*I18-2624609004175459480061479441582080*I03*I09^2*J09^2+483357421977652242925161648168960*I03*I09^3*J09-28751182079958932424960245760000*I03*I06*I15^2-7975461045610594301771453201694720000*I03*I06^2*J12^2-406199950697865948409216266614194176000*I03*I06^2*I12^2-417236639598025335761404497914953728000*I03*I06^3*J18+389678248801610201877213730376908800000*I03*I06^3*I18-380752966062503786488581274418705203200*I03*I06^3*J09^2-609045892887757660473537684744457420800*I03*I06^3*I09^2-1803289622121489818384678768134717440000*I03*I06^4*J12+25814284192128730994673488962641985536000*I03*I06^4*I12+723966827601020644834284994560000*I03^2*I15*J18-1863502542219560434951127040000*I03^2*I15*I18+214354117510311251834348682240000*I03^2*J12*J21-1698318718431529924649865093120000*I03^2*I21*J12-2267185817357192359529736629760000*I03^2*I12*J21+15769283996593930068392112967680000*I03^2*I12*I21-255807127190578073230189287936000*I03^2*J09*J12^2+10548897504318699174284791965696000*I03^2*I12^2*J09+15131172639840937888408775218667520*I03^2*J09^2*J15-4443514045672950295952831673384960*I03^2*I15*J09^2-103033112934146727967741504512000*I03^2*I09*J12^2-4106841147008919272715115272192000*I03^2*I09*I12^2+425665563318202173133788972933120*I03^2*I09^2*J15+82100606570306861937057327882240*I03^2*I09^2*I15-1446715735842144653396767066922496000*I03^2*I06*J09^3-28349839284034281678067680620421120*I03^2*I06*I09^3+10590264426964497719603607065640960000*I03^2*I06^2*J21-75849482382702821930377158813941760000*I03^2*I06^2*I21+2681569696241423177512184777927491584000*I03^2*I06^3*J15+273641773284424190325359555051323392000*I03^2*I06^3*I15+6599062875043518178526231536165965004800*I03^2*I06^4*J09-33476677573126367211110555018093435289600*I03^2*I06^4*I09-5552502562320308659549919379456000*I03^3*I15*J15-5094133615578315048954685871616000*I03^3*J12*J18+1041022070063395191564544152576000*I03^3*I18*J12+36075034461775507318456450345728000*I03^3*I12*J18-4341375747563222022841173496320000*I03^3*I12*I18-1840427711977232138269898237184000*I03^3*J09*J21+12712677606572686400066000320512000*I03^3*I21*J09+5262776847990599810215827399367680*I03^3*J09^2*J12-7543146598719285700189089643691520*I03^3*I12*J09^2+461669178465923640414910219008000*I03^3*I09*J21-2451074416798655445746092591104000*I03^3*I09*I21-361856664826414601973640674232320*I03^3*I09^2*J12+2502073274721313525341924945300480*I03^3*I09^2*I12-94004844981332591437566579247104000*I03^3*I06*J12^2-4521367137656851930536592754792448000*I03^3*I06*I12^2-14603107539696556336164332170960896000*I03^3*I06^2*J18+2882054739784447625290805926379520000*I03^3*I06^2*I18+42692387020737508924180954892725616640*I03^3*I06^2*J09^2-6246215577168854716005590486683238400*I03^3*I06^2*I09^2-391366036414707433167483516061753344000*I03^3*I06^3*J12+1182955476018245593921550299778236416000*I03^3*I06^3*I12+5357960529866748247595241368678400*I03^4*J12*J15-1146894993741344077555254661939200*I03^4*I15*J12-34934261170161236078543751312537600*I03^4*I12*J15+8022291767296012945726995242188800*I03^4*I12*I15+3607101346193065262274911298892800*I03^4*J09*J18-354500446578703302774557125785600*I03^4*I18*J09-833992331072143401587694048537600*I03^4*I09*J18-69757152262423987846775183308800*I03^4*I09*I18+63162101223132001596742008056832*I03^4*I09*J09^2+327722804482472917015952708676864*I03^4*I09^2*J09+38139788399456821126350340892160000*I03^4*I06*J21-270984477047931771777940033474560000*I03^4*I06*I21+23536182458559637991929076564395622400*I03^4*I06^2*J15-3001738906282671170745885705767731200*I03^4*I06^2*I15-412502269876316015637935821311783567360*I03^4*I06^3*J09-251634580818878672483783910561634222080*I03^4*I06^3*I09+3396188944097865409176916978579200*I03^5*I12*J12-3665315333252871682695579392087040*I03^5*J09*J15+865510497943476468630605314744320*I03^5*I15*J09+952311256896376811467084711726080*I03^5*I09*J15-190602137614742422284148568432640*I03^5*I09*I15-45142309072032227888701206820608000*I03^5*I06*J18+4952548465661959050225730337280000*I03^5*I06*I18+170310967551948843579156482672322048*I03^5*I06*J09^2+466086204673321402899886986796032*I03^5*I06*I09^2-1557113375597850600659388046287360000*I03^5*I06^2*J12+5485942029404464337903567335234560000*I03^5*I06^2*I12+87920901330376071246796234984320*I03^6*J09*J12-706672024503331668117754842276480*I03^6*I12*J09+63237094585354817192596435608960*I03^6*I09*J12-451343392454707301922742973485440*I03^6*I09*I12+48005101092857739966122780843366400*I03^6*I06*J15-12267029903628854226265283719987200*I03^6*I06*I15-2392300959084325967530409073429534720*I03^6*I06^2*J09+46664253003506918091269516424714240*I03^6*I06^2*I09-81244039433580332151451076683008*I03^7*I09*J09-175839752694052605535954869600000*I03^7*I06*J12+2176199076483232087874951198016000*I03^7*I06*I12-2379153171250362257203482124421760*I03^8*I06*J09+1339251005241000651492431822805120*I03^8*I06*I09,

        (142782277457422211298259991084827158534817867366400000*I03^12-228961331221841216520613190298674906273362101619685088000*I03^10*I06-11717829292190026313287266144508794560542586368164784800*I03^9*I09+11172422063009604595711725227004597728326025764095866400*I03^9*J09-50801151819054333371051810415612433116805517418677959006080*I03^8*I06^2-192228693764440259959370693236277641786871922993262512000*I03^8*I12+20125944322210074639097053447231452672861650921505688000*I03^8*J12+2525449994109169467884898460157121724640462704477437199032*I03^7*I06*I09+4531621393367289028587270034291678971050839494470377674024*I03^7*I06*J09-754367770984196024864932344912989533633666728452036540866560*I03^6*I06^3+140862128156991707419422404152121741675290389497032704000*I03^7*I15-566299837321441928167481771991573390022253183204680128000*I03^7*J15-67219218244718875387225547994673114819295972511745390615200*I03^6*I06*I12+10913316248930404758972691151585553821416467953164690110000*I03^6*I06*J12+21628191910800489299452242971524391997489179151557067255*I03^6*I09^2-104577488679873528486063667298962031141464795832131778310*I03^6*I09*J09-227554323760633156621923559719741283449268761024183817665*I03^6*J09^2+1104828698008312906256619847208917215696651945361830191586432*I03^5*I06^2*I09-286961358499969177006852749201574070587803902128415728504896*I03^5*I06^2*J09-453144983083330650272024482864695008038975547921242464858439680*I03^4*I06^4-37976530915344107720432003916560717380923252005627520000*I03^6*I18+575580052370541167030539043753074659193118253337414080000*I03^6*J18+21399284826296271164163097042105065976055889256456402295040*I03^5*I06*I15-121036964597989248193937136128207453714725623881022543156480*I03^5*I06*J15-262411366483396135513378245560964387724379808435386336688*I03^5*I09*I12+64451311212680499329908927680272835132952893509490784332*I03^5*I09*J12+303244308718022598665317115562259859693918666395855153584*I03^5*I12*J09+212654501831861901831838802078237187002126947671765686724*I03^5*J09*J12-5538952893153402957815367919481200267763063577356801530982400*I03^4*I06^2*I12+1178945422210900157151073590714691649337742991620267523251200*I03^4*I06^2*J12+6676543834389218869537781095731554272888869005575865184288*I03^4*I06*I09^2-50750262528782228900864657940281825525294749459761771438600*I03^4*I06*I09*J09-9374765647309594081900745700683566664475058155906675126072*I03^4*I06*J09^2+34978180532212506727303078864362779665159790398006583908915200*I03^3*I06^3*I09+7825205318900384869358808760491942387099154802777766375444480*I03^3*I06^3*J09+11796996749420220148407032808593652037107114640325713794878668800*I03^2*I06^5+750394317001106843678656125725830699990869441016243200000*I03^5*I21-111665659591759574546138535307230303708219564102230400000*I03^5*J21-2077372630281495546719167348101558053396483749916877427200*I03^4*I06*I18+92329819450903652595934986965201894910831070153095764832000*I03^4*I06*J18+142103238884480141006680446141944772435848884566296536800*I03^4*I09*I15-406416128612791025560402265563720137776821632949707123120*I03^4*I09*J15-334081115433758856030735287933825725498186118874796092720*I03^4*I12^2+270482478569038746335605537513913780410483796139117987360*I03^4*I12*J12-856504722698655661899009305139407329949710738920282223200*I03^4*I15*J09+2389224623480938335381580173866025954790776835827547403760*I03^4*J09*J15-24679279444700464091044032412534843980764350273637292420*I03^4*J12^2-485380969279421949699406430062688900563819585513405988136960*I03^3*I06^2*I15-3061982524493999930323175580115805981728242652647553716756480*I03^3*I06^2*J15-54387170124750493643986417310734227918256792521697266183360*I03^3*I06*I09*I12+15835262520479006868731467480676026495322546117019801490080*I03^3*I06*I09*J12+83065379903162684168667146409405507691671744764440671324000*I03^3*I06*I12*J09+4656921796573902914318720713087744377543047696306147176080*I03^3*I06*J09*J12+11508829273058280628863946467741074230217807703829517496*I03^3*I09^3-183341055436523549144129284711487603850602078965617908364*I03^3*I09^2*J09+734594748760102835794909704439735890403814473799167880856*I03^3*I09*J09^2+498781661694081520260995491393437992552185656853150608156*I03^3*J09^3+78237505960642033241068747791755445718135933661987796759552000*I03^2*I06^3*I12-25956496042035289255504217736886830251093757653570206664601600*I03^2*I06^3*J12+137955402164598924900461027379410975661902795723166370210560*I03^2*I06^2*I09^2-1143685185504133362506267299023195488647642536103289285427840*I03^2*I06^2*I09*J09+649388427219961045534017391572529334632716853542452433025920*I03^2*I06^2*J09^2-1249863542234087614112700706745477824067786733028897617752064000*I03*I06^4*I09+60266983404432607763264035049455242107257482219880942137753600*I03*I06^4*J09-27136105072799118919836960583105622584919924884198025173401600000*I06^6+43069572939163068163115762440480728483692811981883362048000*I03^3*I06*I21-10957984794229358663234671535732914222009555336636297152000*I03^3*I06*J21-11458365853333617053222338891669391337716153572662756000*I03^3*I09*I18+273565159075875109051553001473312424687034830659461207920*I03^3*I09*J18-257651992805705703793289586922894724397130625840835788160*I03^3*I12*I15+315795168336275209818372991174915535864727954610709632320*I03^3*I12*J15+167502400455485355432431019935796830847330647286805736640*I03^3*I15*J12+189988422347846282080749639036965425501268798677743597600*I03^3*I18*J09-2222659971072739625899510340553143493864449268507563286960*I03^3*J09*J18-230069038462770620639780048617756739478861892369452269280*I03^3*J12*J15+540457010592695782928569342367459193798325318376325816115200*I03^2*I06^2*I18-349024277686438894230120173470711867207082751331319447961600*I03^2*I06^2*J18+9204755579982154140865394758871195180245200130783642677120*I03^2*I06*I09*I15-23764208765209053619970386872100852347736149927223972688640*I03^2*I06*I09*J15-52010452921584909884047070430711231723400667508198588076800*I03^2*I06*I12^2+33913728373697816602903445774592998834230901626660544832000*I03^2*I06*I12*J12-7936278569369498973252358852597767974242031164747564272000*I03^2*I06*I15*J09+83796566156160810703802031132762031877997274163873626262400*I03^2*I06*J09*J15-1242552033608712528774928067091511985865782696131597147200*I03^2*I06*J12^2-114294888442742080963279681392759930768541893252837643680*I03^2*I09^2*I12+29484069998223862721911288036004179003474398358195090320*I03^2*I09^2*J12+708438554193391713192193710155382977904055429723609836720*I03^2*I09*I12*J09-268012081647356259146070398273304092474265521832213281880*I03^2*I09*J09*J12+2254513137583566252615811010760712221231109387243613453520*I03^2*I12*J09^2-1333195831626527381087541500529240614368228268243310436680*I03^2*J09^2*J12+5623403930055930195181976107513557233106818012526478044364800*I03*I06^3*I15+114606755179465570581810088192946807255791207763112967235174400*I03*I06^3*J15+69334810701548728340705135297391816183536711952370786329600*I03*I06^2*I09*I12+302550142292412488405526489230363158158963112566429059980800*I03*I06^2*I09*J12+55120423567873866161906347546872441922311700155538399680000*I03*I06^2*I12*J09-579498069603005269559469539287160466692005460964752136825600*I03*I06^2*J09*J12+159676601216049601768660620557180190743530407453998033280*I03*I06*I09^3-803910099845830104878142631125267832473391711992226859520*I03*I06*I09^2*J09-2452755242541381723970582134875180149185834421850743395360*I03*I06*I09*J09^2-5494882797938583617618595528913234435469073196982899293600*I03*I06*J09^3+786214615157052261478913085200213707065530296450687872466944000*I06^4*I12-16197495721110952487013139004992523720106796182324714700800000*I06^4*J12-4018811872029494415280166786559632660695093956327214935244800*I06^3*I09^2+18008657782430325889280743952848253120588041024738534046515200*I06^3*I09*J09-1209355592411967479279996998105990385780734193986453813862400*I06^3*J09^2-350912353508708546707814819956465864180712405695941216000*I03^2*I09*I21+15777774057730516813583072988753145049288938046714436000*I03^2*I09*J21+172092353140365305911056146025200288275502088023007523200*I03^2*I12*I18-886301482885729507451110614564528634431749797764775080000*I03^2*I12*J18-7225209478358783423819142602631759527026668753733632000*I03^2*I15^2+79523737593906940606542902171203863229521128098749120000*I03^2*I15*J15-71814392851754034858031113849194641649957208367798939200*I03^2*I18*J12-1345444384712325398492503728568228109893463047671053088000*I03^2*I21*J09+324672897170127024403689416695909472758449447062419788000*I03^2*J09*J21+240685762821402876326485479832715453715317058175788693600*I03^2*J12*J18-1064745976546626605262337891816307679190411175758347669504000*I03*I06^2*I21+232397242666916162306657553954069301219780919269387542528000*I03*I06^2*J21-745717262105140392651324031932966285121375671409599628800*I03*I06*I09*I18+3700848291142672349520585892641959741970505233365641824000*I03*I06*I09*J18+26879604621620619403906305759684284213078627542755889651200*I03*I06*I12*I15-62547141540793370979413386307193430340558719811288682086400*I03*I06*I12*J15-5038890100090210830499843570012439786578531603978877932800*I03*I06*I15*J12-9295641202058094495842233150004126303954132342378863353600*I03*I06*I18*J09+3165410982750099342315299216841190613849652460973384016000*I03*I06*J09*J18-24894647485665892061897033109786338118327159349753143398400*I03*I06*J12*J15-16460496465458282627624730294883763505078743347940133120*I03*I09^2*I15+7575251154729700542233672414725343413760535725117283840*I03*I09^2*J15-84984832074554175446506299490436620150704103880499955200*I03*I09*I12^2+28517766925672492642846734663098690490358204596989712000*I03*I09*I12*J12-98879577296180473352977241026535228429700477212390267520*I03*I09*I15*J09+28281040017847374062143886989305155734262990016603728640*I03*I09*J09*J15-1678250690695537424132979479238391418669272021503220800*I03*I09*J12^2+1921135524902465399632897029594189892220993816073830899200*I03*I12^2*J09-1766036825754438014152114613092804070626119142252572100800*I03*I12*J09*J12+284142295541146777960853151884946214369880423449726619520*I03*I15*J09^2+629517336984198871573812136677253236519690786315060687360*I03*J09^2*J15+409615395444910397473438623760435294225124025223038084000*I03*J09*J12^2+4614916571679495541444434228528193244534666950821652316160000*I06^3*I18-17829943290142697913245631364934375465709430680322283569152000*I06^3*J18+116246560519157977349355180135433680712197705281180254156800*I06^2*I09*I15+184281491016358475375634978533471235032114362725184226918400*I06^2*I09*J15-1014489099468614560331350833971948482389467474150524882944000*I06^2*I12^2+29721635112198727134723370683450015466172774362458187776000*I06^2*I12*J12-281154484546346220981909495231361683280244099786324529638400*I06^2*I15*J09-1217978525843738093958944516797728319370586886688384958259200*I06^2*J09*J15-21643031165377031985737832836846857091848097221600972800000*I06^2*J12^2+1614036868319411070982216083415108113210034288061111654400*I06*I09^2*I12+373291350357484166260044859242044939130393576315354816000*I06*I09^2*J12-969339859722985422276800431270832199148338220578965836800*I06*I09*I12*J09-4125660016057327803841693902086346479399036277940810790400*I06*I09*J09*J12-15797996847368952984850128631480979875439985026646091699200*I06*I12*J09^2+12279333526009204584684834908116751715118043393788108387200*I06*J09^2*J12-333093560325680755363794365453397179959292449923072000*I09^4+3574350128110189644096101075442223584947792058789888000*I09^3*J09-13283337572869381365528355774989173339264209859506176000*I09^2*J09^2+18851321643402210560219001233011936850418062942539776000*I09*J09^3-6530801846977178597029187159348115714763997235621888000*J09^4-2286588130467490350967035743613456904359052286326217856000*I03*I12*I21+177270632690340298856811614961621420660630203414158992000*I03*I12*J21+9145586444981330624287038749634570059716000455889152000*I03*I15*I18-80777997535492403152647345880510697532580417303157568000*I03*I15*J18+629753947645819728477769066634065202001739109637109824000*I03*I21*J12-88667945063934053953840339653033155981343798501566808000*I03*J12*J21-6604771298970951676251850935702193812992716827748222464000*I06*I09*I21+921919944069992233802729649782077222626627732109309248000*I06*I09*J21-2807640257821297670122186861505994435833234334645763584000*I06*I12*I18+15705537556862299815489140285708147647665350821660881408000*I06*I12*J18+625296157067517018201658277337259778436024529151024640000*I06*I15*J15+354151189082289435686080479577100995338734706039079680000*I06*I18*J12+20842401664007909220263984399447781351173728734287469312000*I06*I21*J09-3685540198202651389942263755474159609519084732112251424000*I06*J09*J21+6253371616066942035633326980830254852034001299755027712000*I06*J12*J18+242921782900237592299335239894267469999898192029696000*I09^2*I18-5213702606221935018497497308968040770930877829343232000*I09^2*J18+13260650347894557812043353531216406746757010793763840000*I09*I12*I15+2482332932733668938383514125171042457021410929733120000*I09*I12*J15-3418707536842802391430211664581984878035055176558720000*I09*I15*J12-3475801737481290012331664872645360513953918552895488000*I09*I18*J09+34309622197451406798788464003727878166517061077135360000*I09*J09*J18-422513285169276275755177200032149568268717704643840000*I09*J12*J15-34721247225698680425337552173547424519305705581619200000*I12^3+29810396689704809944055803486809227085321381087237120000*I12^2*J12-8186248874241528430511598721116590587135707422019072000*I12*I15*J09-31052302331522791202760481755196179476017265055123456000*I12*J09*J15-4399517650060413690675610031231078279187953747988480000*I12*J12^2-5886315442713791007695332254861361357549447833783360000*I15*J09*J12+5718270366241901133131410667287979694419510179522560000*I18*J09^2-52221284936207059370133566043071725635008540140972032000*J09^2*J18+431470601982741102607806627322475391800797690348800000*J09*J12*J15-28276472954845536807712736710071105334361515929600000*J12^3-8881869548813182054486355774290648468614967909324800000*I15*I21+3064560938679144931872005732400866009727173599689600000*I15*J21+1437833161565428997429549864634080785908725778816000000*I21*J15)*j6
        -10979152974892033635854374466483608066897059081697752321653760*I03^3*I06*I09^2*J09-3157485849268459713647245139648445726703956079136598310351257600*I03^3*I06^2*J09*J12+27786145499333564845477742265241221016582093605609566716595159040*I03^3*I06^2*I12*J09+5576572773972646233876398576331182263472438438065123496370585600*I03^3*I06^2*I09*J12-23837702165899502263434468485347106036385179213119539637705850880*I03^3*I06^2*I09*I12+403117272225605508260729807651689163720860296543181668464640*I03^4*I09*J09*J12-2012535424555682572292971504982605975803726061378511111327232*I03^4*I09*I12*J09-346284258462956912226764114523798712911105667197833823865497600*I03^4*I06*I12*J12+335741515167731132751593446704295888684998418688187270687805440*I03^4*I06*J09*J15-64398755130902169598665434527720623902260187797021753366609920*I03^4*I06*I15*J09+27376978096255541773315037410719652972972997543562882791608320*I03^4*I06*I09*J15-88381495296783370351421924286736180401676172919847617927413760*I03^4*I06*I09*I15+881839677280200668127624903812878963233753974755859903262720*I03^3*I06*I09*J09^2-1282692519888980530400196507278852736066234662922903470891520*I03^5*I06*J09*J12+45517371686312079319204344511246093656195551119023468903475200*I03^5*I06*I12*J09-4861027016124296584870652227240771556096949202458122675458560*I03^5*I06*I09*J12+70517322269913172593181759170081197785533785262446224749158400*I03^5*I06*I09*I12-536515834059785831902626197346997769152983721688348221281792*I03^6*I06*I09*J09+1704164672032255315188811263665203663539672911025999286272000*I03^5*I12*I15-250161211880568958453782652894494327185500633809430434201600*I03^5*J09*J18+54404149298908811716868629511005026390112305777695506022400*I03^5*I18*J09+62385162294950506930691335639058787981439806208014511411200*I03^5*I09*J18+18690937011055039189989481228897399783020484245986152243200*I03^5*I09*I18-221765797557789880854158346599306211274180108678136233986048*I03^5*I09*J09^2-87107360587812451050247848688756601834697409698717013277184*I03^5*I09^2*J09-831015396305234465341663532508277672201366547522038487577968640*I03^4*I06^2*I09*J09+29155864497894370594016807486362362089671085042421422223360000*I03^5*I06*I21+487924851952684273688521559117461767547916697369694733962444800*I03^5*I06^2*J15-92405148119172760959552792805848325290864215429944160517734400*I03^5*I06^2*I15+222172028149050230452719750407697755742104644811902444515382394880*I03^5*I06^3*J09+8302206554885370197122417514310908710823347984943329501447127040*I03^5*I06^3*I09-318060754097753149863043878494569092381066768596241611232000*I03^6*I12*J12+319741895373894454568130575986670693173688782472522774323200*I03^6*J09*J15-274452397553452162007619191526036786002303654117660229427200*I03^6*I15*J09-88611312352584688435002177536956122683476799378270859571200*I03^6*I09*J15+138542356008268869853412262499034249075913522289269735628800*I03^6*I09*I15+5623092686068486206093139324279054837424872306450711433472000*I03^6*I06*J18-278007766416991581584529483312622778610741269681549342208000*I03^6*I06*I18-24690198237160137938655860956097134249514466853495641534519552*I03^6*I06*J09^2+4000135090302546908047666522579088605232692401084243297921792*I03^6*I06*I09^2-188625532158064307703248053463942051253765312888584064504115200*I03^6*I06^2*J12+1798599098224193993892356388135917550347941527591846797794099200*I03^6*I06^2*I12-15215688377466119906659310264197310291137968387324477331200*I03^7*J09*J12+124058940378952793048056435535281412402422800210287241801600*I03^7*I12*J09-2879091520968239144672712421778049075477730847233212844800*I03^7*I09*J12+15882928379490054906334003869506302491366890127855723945600*I03^7*I09*I12-7407349960759157191891158745205922449015022572001939068774400*I03^7*I06*J15+5166409010000422232637417856166847913591605336641769214771200*I03^7*I06*I15+291948380999295602190481095798630273146470336287159687289651200*I03^7*I06^2*J09+197373376527995359048032284512390930145839630246932286685491200*I03^7*I06^2*I09+3603989480282975733114853370035813303628616850370445623040*I03^8*I09*J09+321935546326932280713923632874127756228968119320174298118400*I03^8*I06*J12-1341168743739190303895593310591343593513066492408378514777600*I03^8*I06*I12+18341527131422155139645334905196971852858455005801935080320*I03^9*I06*J09-69386079571658049043331407278927558486165432640587909575040*I03^9*I06*I09+1265998394950869078422749880861729644607077947460986519552000*I03^2*I12*J12^2-4705605003644123272315199180635391813109975982686922309632000*I03^2*I12^2*J12+10275614126834457611030586057150407456287368396681152138649600*I03^2*J09^2*J18-962158129439624230274366495294163719246728877471618183577600*I03^2*I18*J09^2+774984770003470419347363652115828953287415567164551208325120*I03^2*I09*J09^3-762339403918869177473457649066851200017836774319820666880000*I03^2*I09^2*J18+49852660391806695085098624600443645305353445603615617024000*I03^2*I09^2*I18+831139424269424023213787611099067156763904556752059935692800*I03^2*I09^2*J09^2+190846515278478269402092294716331545930799023226903673978880*I03^2*I09^3*J09+22520392060672312959911964326314610894986394293695876169728000*I03^2*I06*I15^2+3062895407243842046277388965268713588199547903433760279732224000*I03^2*I06^2*J12^2+175001878493648503538285074410118539102668911608189744778567680000*I03^2*I06^2*I12^2+403421241772170800557804898161706309187982627859070896670965760000*I03^2*I06^3*J18-216653058459212368812331077201248862468360555542066769259266048000*I03^2*I06^3*I18-4890285371146405664150147082421243678276999282572173213835264000*I03^2*I06^3*J09^2+280690456542501632934355713999606411123755399803591043733459763200*I03^2*I06^3*I09^2+4224646368942673672319213972767662921228979261451113931916312576000*I03^2*I06^4*J12-27585891312196121118004685894564012826654501563855399683463577600000*I03^2*I06^4*I12-6116976040067821004541287638342286770825741932446398218240000*I03^3*I15*J18+578478426722128894779556230637304033728341099224289116160000*I03^3*I15*I18+20133592311692841175819053994122430511014769768109020160000*I03^3*J12*J21-351736920773333289179771016395944398473410093284681768960000*I03^3*I21*J12-21408733724217870506197502079783804910665967579857738240000*I03^3*I12*J21+93039832849344061550040956252707801466134361255148810240000*I03^3*I12*I21-680583199648177910574409272556440910877807132609636438937600*I03^3*J09*J12^2-29731585926362867317340873575905154948145688408152370923888640*I03^3*I12^2*J09-9682695080695861288913551235939550568588627940677656915271680*I03^3*J09^2*J15+3096598984450197916648769250524605445494396128230790477987840*I03^3*I15*J09^2+151789928827147846890636798309099232478096359177981289472000*I03^3*I09*J12^2+3326595093598891659798028586023573396707573401158737414881280*I03^3*I09*I12^2+963059594419624878894334964560381687566401495987442833940480*I03^3*I09^2*J15-663291080969175406748364624095977569272507338923727630295040*I03^3*I09^2*I15+1018791657532104895658388252414585369332035890372487973392327680*I03^3*I06*J09^3-11203334926131954889956478462980576040582616749700862915840000*I03^3*I06*I09^3-4083028878263611441266587530351910123954316998322986878894080000*I03^3*I06^2*J21+31400512243781552159368853892115179303527157527510780136652800000*I03^3*I06^2*I21-1183660356411420373099483139645940378630994219207456778285206732800*I03^3*I06^3*J15-53947325997210211077766171326203048606093545273248968204196249600*I03^3*I06^3*I15-918388107755914779741344609455507949047155505740164910491212185600*I03^3*I06^4*J09+14554228430322175437067804143339594588145266500322921627588624384000*I03^3*I06^4*I09+7088674002290517285509095832420213437181949248294649987072000*I03^4*I15*J15+550910496794962617545645293614891564021226726982314126848000*I03^4*J12*J18-150440190408740526437340095672782663274791883897194447872000*I03^4*I18*J12-2517225612081213682973527997715608010506186252806359389952000*I03^4*I12*J18+362480175683706518050588309417602407186043270081419401728000*I03^4*I12*I18+174887450072640426148725921698062509795130187082947493888000*I03^4*J09*J21-1118368474046848926184137387584161726518470694341522915328000*I03^4*I21*J09-214776450331846343002911175717971624473667410487796758681600*I03^4*J09^2*J12-1595265416773061672051139444915897533071740101218342182461952*I03^4*I12*J09^2-73648782612060258038009701090710519105322551749955081216000*I03^4*I09*J21+515004958872683177918328815098334495993839365529611165696000*I03^4*I09*I21-64325909221568930313887943620915353618226367670723623137280*I03^4*I09^2*J12+416939696297093131890692010794706165717615759780995569923072*I03^4*I09^2*I12+26132047126117129844756551875586628917879510979273143503974400*I03^4*I06*J12^2+1140023865264710202764377011110996208091962791238426647321088000*I03^4*I06*I12^2-673469445630430708149878877878425747450639672622289440538624000*I03^4*I06^2*J18-348138989727000689649711151598561619946304973481309442015232000*I03^4*I06^2*I18-24608463056137187261707116883162537815433659644964947823028838400*I03^4*I06^2*J09^2-268135992135886162468859018954704322501980420095119518118584320*I03^4*I06^2*I09^2+101981873129558535447574006231920388517093352037062398673012326400*I03^4*I06^3*J12-42504292183652001526964599544784386075552641301929101843166003200*I03^4*I06^3*I12-561910253779290417538455267185127311276633326870310702592000*I03^5*J12*J15-45924534579811920707019435228658827678790167510869323776000*I03^5*I15*J12+2117484795795680966137535064270374219188737491373993699072000*I03^5*I12*J15-75333631560983145023514621386229737791825966906484124170956800*I03^2*I06*I09*J09*J12+1174273671040767649704108358185665625024186654811879555453931520*I03^2*I06*I09*I12*J09+1359838871604604573850135015436186591316850114397535220869939200*I03*I06*I12*J09*J12+25902972980475670778169127813398615596083277298048385427865600*I03*I06*I09*I12*J12+440740741503472722240219676301504589485614571024695809864499200*I03*I06*I09*J09*J15+338929956587676573231664289545124248218864034366410608281190400*I03*I06*I09*I15*J09-924923242561774235058104869881710130089048317918424403743342592000000*I06^7-37882043498534879447237002749827682336984768124742801817600*I09*I12*J09*J12+516967578401024553191135497067566003099862954918138413056000*I06*J09*J12*J15+6735482087483133189565425305319901454543568982812185198592000*I06*I15*J09*J12+47060381432644443899655198364890621779978264581120685093683200*I06*I12*J09*J15+12550895167450047001107184861132900046830143860778507789926400*I06*I12*I15*J09+528074115312625018844858095142468362732525944700998451200000*I06*I09*J12*J15+2090689528306417018403615204757500792763919745589678243840000*I06*I09*I15*J12-5468473103330684602340897335852650593932121677275163321958400*I06*I09*I12*J15-13049256149916492114945423027986487136451204187381911145676800*I06*I09*I12*I15-53168810410489189807754609280148109271227228799226533642240000*I06*I09*J09*J18+5605642914522574635877351978823375874564261345787091877888000*I06*I09*I18*J09+928290992066533055016930914481088931694013553590466296307712000*I06^2*I09*J09*J12+11341476254709777902817955878310221581092865389715674374261964800*I06^2*I09*I12*J09-1685192720268333042712549156586842786167361347294272716800000*I03*I12*J12*J15-30489376884854280444589787393654709966371708428534185984000*I03*I12*I15*J12-12001662276645219248073135883871710859987763359317374271488000*I03*I15*J09*J15-10461049681882663396986954657889274338695080658228167417856000*I03*J09*J12*J18+2966542088122344755737402634900779878451294417698994618368000*I03*I18*J09*J12+81608292987926733692399622400451466520687424070393062043648000*I03*I12*J09*J18-11737387261571062040402765695259921901881370800342031738470400*I03*I12*I18*J09-4216865973672127755659712263995577717158944781860370229760000*I03^5*I06*J21-199024366172940033181331927075655711546367271354157121536000*I03*I09*J12*J18+66544683593936836768779353663605148057745935949874987008000*I03*I09*I18*J12-3474258290048772330248313970049684144525903125934003232768000*I03*I09*I12*J18+307768436614783219115747348434665729944347091647678532812800*I03*I09*I12*I18+2080221159550372862209534341828497225606760337998304069632000*I03*I09*J09*J21-13905885378639291360749808005065053454063747173205494644736000*I03*I09*I21*J09-3643674765346448791741461717541827734209590415434047400960000*I03*I09*J09^2*J12-10472754364583268074331600165776593149088608805350682119413760*I03*I09*I12*J09^2-639154482226545327103228118158080802706413694736201250406400*I03*I09^2*J09*J12+6977209305747517168430221280783444572731054657527398525992960*I03*I09^2*I12*J09-85494498367964393788943717754540520335950849005365630074880000*I03*I06*I15*J18-9514268377070942382243246598371206456888678534170835681280000*I03*I06*I15*I18+9186015342436401466117465735397391883628221864657210859520000*I03*I06*J12*J21-51955039846133670690981683737733956718115275065437702389760000*I03*I06*I21*J12-24782023219823288877838635509814372252104328703473213050880000*I03*I06*I12*J21+102199612377372948145545927239186801626103279075314204508160000*I03*I06*I12*I21-116461649360097009306915546288282936835118516374179080687616000*I03*I06*J09*J12^2-4715782324895086451251876007833658669187968715815220684462489600*I03*I06*I12^2*J09-1500473883146986344440029178902922367494265688544888645143756800*I03*I06*J09^2*J15-428853835142095316757764087024042803109071315722858740480409600*I03*I06*I15*J09^2-6861337170100349714953743544468534141946320833959228891136000*I03*I06*I09*J12^2+161104080749051630275806685835015410231919546400648653173555200*I03*I06*I09*I12^2-13604027253726647961970060757587352053697961625065549860044800*I03*I06*I09^2*J15-7706749581828174881164972523783355921674307217514461043097600*I03*I06*I09^2*I15-8284858465808849083476928193227377421758109569899529320792064000*I03*I06^2*J12*J15+2728028997108999156954182573406403488494110802061226222190592000*I03*I06^2*I15*J12+41924165088009292948811080711967338632727958220079368342994944000*I03*I06^2*I12*J15-10716905903658826039941001921547877972136514284375320697356288000*I03*I06^2*I12*I15-20156406948462567448074687953449604276173297815782282892091392000*I03*I06^2*J09*J18+7409541646509348802971214398388351070645043634277511428358144000*I03*I06^2*I18*J09+7258021631877263123769393312861590258621278750363765451415552000*I03*I06^2*I09*J18-990388882542341076472522002781344767768865005521501813358592000*I03*I06^2*I09*I18+25317988944304240372612948326981136420861849878035606742245376000*I03*I06^2*I09*J09^2-10105914535789646303061387070856032382909067420921321667821158400*I03*I06^2*I09^2*J09-94875378568138314716501414947328237028007916343411232105709568000*I03*I06^3*J09*J12+1359766406519997266882099589406517934423147608980510146442120396800*I03*I06^3*I12*J09+164516772853341107786748303426025918887338825029406291270418432000*I03*I06^3*I09*J12-872387882136633375562986667372208567041902759009151014302456217600*I03*I06^3*I09*I12+11431146211197364575387199699259144364833125285553419748966400*I03^2*J09*J12*J15-5361903546664911591684148677008756726980686534001423053619200*I03^2*I15*J09*J12-80960800420661832263647704706791517424547687651668168153333760*I03^2*I12*J09*J15+23343472695857978653138352876203152792303995557016311369236480*I03^2*I12*I15*J09-96853037519011581096860788082250430241181380414678301081600*I03^2*I09*J12*J15+28714726073810582197059867564960891921857524802352164044800*I03^2*I09*I15*J12+5437938678460199691037496051197086032657349100356215366123520*I03^2*I09*I12*J15-1682548814272010106874042077249447776661089994348705852456960*I03^2*I09*I12*I15-936132777848216073732224209652121064237653603112711325491200*I03^2*I09*J09*J18-530354542188024253624083051206059485877010863681635325132800*I03^2*I09*I18*J09+754907262342610938418968401522432758475008686993227428921344000*I03^2*I06*I15*J15+359317873025587021900065764047726093621544570859085935513600000*I03^2*I06*J12*J18-104776529211775414587035220290788626714588159691602393587712000*I03^2*I06*I18*J12-2849318168477021789543960674778835200294870670157552722057216000*I03^2*I06*I12*J18+401792323171114834817782435507481630398373373438564220538880000*I03^2*I06*I12*I18+351162654928081451549573692416523999027999438207617067226112000*I03^2*I06*J09*J21-2557404286129193661478905149790288688211199614486707987931136000*I03^2*I06*I21*J09-709365770616527838617216442848359283867386271220125218102579200*I03^2*I06*J09^2*J12+308927789270219233575838643301080209115085828645651259778641920*I03^2*I06*I12*J09^2-64364433794384606048000932032887682054068396931131042233344000*I03^2*I06*I09*J21+438099572526986188680606739894157236352514078474231769178112000*I03^2*I06*I09*I21+22582510822348638862963162323952927413121093864465510462464000*I03^2*I06*I09^2*J12-222479312653366847116458069857160650461966841972966781413253120*I03^2*I06*I09^2*I12-45853405396634019356263773606455136696747622410121388850819072000*I03^2*I06^2*I12*J12+93007453602546494419856325089693622912425858473784699648070451200*I03^2*I06^2*J09*J15+15276221019174358688848874231049434939215713923487042310149734400*I03^2*I06^2*I15*J09-18705758994950988613062475788733046971991143689791520527710617600*I03^2*I06^2*I09*J15-12149363796595270200154573642393645020098151697480119182148403200*I03^2*I06^2*I09*I15-1319884746238393144465834357078809778045827544364579551741191782400*I03^2*I06^3*I09*J09-2284516439318755380772159857357234536557085877862400000*I03^14-4138086341863747097641381929921399096261146061908213760000*J12^2*J18+985258652824701689914614745219380737205034776644812800000*I18*J12^2+359658818627129104886430966594882744309325894866422464512000*I12^2*J18-58642595016126244583717869635457541478443669905899257856000*I12^2*I18+7079316609597383179993161905657559605581090460906840064000*J09^2*J12^2+68775149530248992352822940224469490486665213569108128563200*I12^2*J09^2-1881582732876598459570407315379887239690524095924535296000*J09^3*J15+27702918943145510441943632449192491639405416717979353088000*I15*J09^3-104798231876133094148911091068884584876292899740286976000*I09^2*J12^2+24892847323812603943880426376434513494770586204435945881600*I09^2*I12^2+263820010930368121868234017880057565328042432760237260800*I09^3*J15+4702931478422027003500208657375132223342506554785438105600*I09^3*I15+392351890191525650739331027429584506904760515499445452800000*I06*I18^2+137142798314900412967260309606382172731781315949153484800000*I06*J12^3+12150791636636584415768598438921765388840367797472624246784000*I06*I12^3+8387473503041132066391981879210755321651948212948283817984000*I06*J09^4+717223985807833353910252726920971908750220136576300456345600*I06*I09^4-55384788885617392293795656155989126211956261859136372736000000*I06^2*I15^2+63573851350608801869781676036697566972164957874438617327206400000*I06^3*J12^2+3107216924100086626942185881169151927613719391829192514895609856000*I06^3*I12^2+2389144563483302634468336901623790218640787434226364589528842240000*I06^4*J18-2473231122978113766554440323206825598301058279149178478762393600000*I06^4*I18+1861549821941293941484321898680228215048873354806043091652837376000*I06^4*J09^2+4523412605034425155025018015542248878654963514602109131953274880000*I06^4*I09^2+12955920718867788622206176347215977243798081169939342379764940800000*I06^5*J12-149777503486961546222822848289887841128692811210984780916525629440000*I06^5*I12+2724665904107817019023132134927670186838614690968371200000*I03^2*I18^2-115791491252892989237968702386641098909338233843453165568000*I03^2*J12^3+5021930527670845259057261609819314807829250898131994165248000*I03^2*I12^3-14172439134952672920870604351175999664295947487287174051440640*I03^2*J09^4-44223925843045787082562565093910164395699196510681038970880*I03^2*I09^4-424621555518007182342390960962771977942708081369855001249848492032000*I03^2*I06^6-1542367889477421430818743565988085891958379163541717712896000*I03^4*I15^2+3417496532606610524841769929267488882525790699211448221828330291200*I03^4*I06^5+529997691729979346246024448550659609616753929587256544685568*I03^5*J09^3+29470922658081340491042966195562084198752232691778427554816*I03^5*I09^3+21165905832156073851797781486372587148922905139900476096000*I03^6*J12^2+734945498778193625326161123371963493366724899447750689472000*I03^6*I12^2-1018963421174226810474451553611665087790097791677696000000*I03^7*J21+8036027469752739196367382050279229190340640698706739200000*I03^7*I21+13966287459815879618132269411790205937647620453088015360000*I03^8*J18+539008094483181305342758589471906236884430433768540160000*I03^8*I18-340015696641364272131455409157347879687724249337220033280*I03^8*I09^2+789270890944180847978802342648212212582970800875526865507942400*I03^8*I06^3-14362611599533525667487878486166017408933544830077449216000*I03^9*J15-435402892814089114254873798680397542591855064345280512000*I03^9*I15+489940001459747456820753593247712915397382372906170496000*I03^10*J12-1352050267038327665121987038498970912219014370328168704000*I03^10*I12-1572490310266793492525735061073086979720200427470188029670400*I03^10*I06^2+335450941633824833290871706293539648190404367057504908800*I03^11*J09-323951241196042246657288997302106689594463885930010201600*I03^11*I09-9928855926031511485318426631479338893302310298960247296000*I03^12*I06-1056863126730261867136606736674935117955625488963784933376000*I03*I09*I15*J15+8969220173971376615664765005303876123275985038400501553653760*I03^3*I12*J09*J12-1157913101286688227448045154407942385000499413955278712606720*I03^3*I09*I12*J12+479183507691873887976250120191014612162328313009189078302720*I03^3*I09*J09*J15+2125687113169764115298424316246945916189141534495576141783040*I03^3*I09*I15*J09-388652735804666716725046066904590931618612415694670650095206400*I03^3*I06*J12*J15+52621399809803737492258222353607921865634107198555190502195200*I03^3*I06*I15*J12+2740139019278611743513127315564725978167735029764223191865344000*I03^3*I06*I12*J15-285553875631768774761535004744669073535935695620892455753728000*I03^3*I06*I12*I15-329129827567563397804454502780325300225426067414513845181337600*I03^3*I06*J09*J18+45529440078212402817000774683583948908975410595742979274956800*I03^3*I06*I18*J09-26245295980706271917661648607066687928680624162966412838604800*I03^3*I06*I09*J18+20282100842470427567483149460003489103023281795389441835622400*I03^3*I06*I09*I18-117705567057457695221799308228875352071428154649833635840000*I12*I15*J15-20040160998454432372863263917762204194750407356955492352000*I12*J12*J18+13892147004828293827796067907593268394590990350691860480000*I12*I18*J12-162545783079346341020579997077970724289115070706913116160000*I15*J09*J18-2354804485133369014865228815880691424362163687190446080000*J09*J12*J21+20783260500758341735862130154513719448722667259585495040000*I21*J09*J12-3602929569377161479108012371627681139517242230602407936000*I12*J09*J21+41489967968094827681690418417315552092546625864699936768000*I12*I21*J09-35825572568720406361292564926564164957708465178282001203200*I12*J09^2*J12+72865351035569049423018619379779979853741238592754155520000*I09*I15*J18-1518800788941933146428750649624603780977772571650457600000*I09*J12*J21+10177654859281017116566955718473671084665614342415974400000*I09*I21*J12+10015270567765438754806737009534400906644725206547546112000*I09*I12*J21-70008704161960776584525368015426563091808191843408674816000*I09*I12*I21+8192984234888655720398476603520250252046488337176133632000*I09*J09*J12^2-45521604299025778655441218344977668579384902483304297267200*I09*I12^2*J09+7353193460231756947855056332832545416567113598944686899200*I09*J09^2*J15+21747614243799640401485291271227391012326732624880952934400*I09*I15*J09^2-2229351567893597900028651934971550207024509003980587008000*I09^2*I12*J12+2895368385433428983691136937095281523782297424067611852800*I09^2*J09*J15-26154457251517236682320048667761410076347696506418390630400*I09^2*I15*J09-14321608737333864812100947067143981912245153398764077056000000*I06*I21*J15-2564110596556360754342391488703200287590567678663720960000000*I06*I15*J21+4014032819123529287345946083957246110539573203183861760000000*I06*I15*I21+2856083464312748551229531119658001047612979510936781455360000*I06*I12*J12^2-23066027347373831091287428706385512120587495220789106180096000*I06*I12^2*J12+68773705176871468673180044122715521200151299756609942126592000*I06*J09^2*J18-8508347828705128977358642888312633578575254955851885117440000*I06*I18*J09^2-25389973074411189294567833539172799332867974141391480369971200*I06*I09*J09^3+10699072982766260960822429578912141379549768061785027837952000*I06*I09^2*J18-812419283048309748545850669965389243699152120509693362176000*I06*I09^2*I18+20290033561865364622332516470966501782868026979646526429593600*I06*I09^2*J09^2-6478574843318945274484680182388334761854853165601552151347200*I06*I09^3*J09+8996235212956334689514515571779246476849854442466679822745600000*I06^2*I15*J15+10219872102741660079432121257204059336490631803112623775416320000*I06^2*J12*J18-2130118728559855089094613232491583278273561780851720794931200000*I06^2*I18*J12-56810245628470702741906076823495458774631768865942300273410048000*I06^2*I12*J18+7338120506908564704115094796499143641410557410812017353687040000*I06^2*I12*I18+3748848170582035909800738852369360905599080208775756643778560000*I06^2*J09*J21-25496948697237404732624796310988083799864608302698721000161280000*I06^2*I21*J09-10741331319571779167186239429248287917686399980459245005889536000*I06^2*J09^2*J12+11165726398393193793282304180190580418289860281017847221020262400*I06^2*I12*J09^2-1253780195139269829368057674745943548640530840040494766735360000*I06^2*I09*J21+6778790424857036760816757272363576922785444838708330465198080000*I06^2*I09*I21+848371475696968270710981408591106431755410054408370239291392000*I06^2*I09^2*J12-4884048418995664086230110125446743128678189390354767089906483200*I06^2*I09^2*I12-942025787328539113555438977319637006264822632013056221558865920000*I06^3*I12*J12+842158090347718134949706611050935195771985984397656207870394368000*I06^3*J09*J15+215523178473623230598982966851988344209563515881807326730715136000*I06^3*I15*J09-301185051460139844743354327922335572433905619431868567404412928000*I06^3*I09*J15-173731174957992876686711670386900354519156982325463582462509056000*I06^3*I09*I15-12512438276596602617921818558392019393195290856772512915272499200000*I06^4*I09*J09-196175945095762825369665513714792253452380257749722726400000*I03*I18*I21+167473218953758192247698960359932014955586862391215718400000*I03*J12^2*J15+6184847743369648619923969125584165449220170179769466880000*I03*I15*J12^2+4777971848756685298240694544530472253421390138709011202048000*I03*I12^2*J15-307735153667163726496925669509753019406706924478385881088000*I03*I12^2*I15+188328907291932312354878893166200563314285047439733817344000*I03*I15^2*J09-6729227110593270296816725730139747029926679387142545393664000*I03*J09^2*J21+47857950084713095181918486970948299467589656473775081439232000*I03*I21*J09^2+20433584831211328882507545950575707695343451437872893495910400*I03*J09^3*J12-29305844395767951940130870255756982678962021060836747373813760*I03*I12*J09^3-94164453645966156177439446583100281657142523719866908672000*I03*I09*I15^2-27622644721676303328845166144645466513233146150051155968000*I03*I09^2*J21+447508547687854474666226810359858227114695942934197796864000*I03*I09^2*I21-30838358852576686148318548148700703307611877282466228633600*I03*I09^3*J12-209558583857409714660262244873721003899611690362467217408000*I03*I09^3*I12+2973418048607458813701801352307063706775032398140322656728268800*I03*I06^2*J09^3+589237680763029914528573364964057935819417499009516625906073600*I03*I06^2*I09^3-62555468809597809551689016184990590276804285235383894938091520000*I03*I06^3*J21+420571714091878887495912990092048326768918439262014872627445760000*I03*I06^3*I21-17057115108167145097867728448387317244679467809950403340718309376000*I03*I06^4*J15-1742317112197129987817744879941840700955462470157249600620593152000*I03*I06^4*I15-29189088590703804418716019542399406232103815250856971889919655936000*I03*I06^5*J09+202656488168984662603939743290269221511169013311218466883181215744000*I03*I06^5*I09+391628322611851438918886622054964232241229974888549580800000*I03^2*I21*J15+550016028414934593726344585516228034187925508570975436800000*I03^2*I15*J21-2166031690835221629156539404600611644196339182815061606400000*I03^2*I15*I21
        ];
    SYSj6_deg := [ [36, 30], [39, 33], [42, 36] ];

    SYSj6j3 := [

        ((-13921272058366643712000*I03^8+77375546515744993519605000*I03^6*I06+2320785120164913120689775*I03^5*I09-2988377416704887216763075*I03^5*J09+31747185686247131480762592000*I03^4*I06^2+36102979075052411619520500*I03^4*I12-3723395046739252558490250*I03^4*J12-408901107250677240365670000*I03^3*I06*I09-1687460950339005072881034000*I03^3*I06*J09-84291854339240701052578560000*I03^2*I06^3-24912836115212585104992000*I03^3*I15+105380330740623245439594000*I03^3*J15+8631398286371568646417752000*I03^2*I06*I12-975301838279514926803980000*I03^2*I06*J12-4785710253894516334122000*I03^2*I09^2+13785274305035321660995500*I03^2*I09*J09+42616767298336306576609500*I03^2*J09^2-73172350930455085780497600000*I03*I06^2*I09+15413464304007161995169280000*I03*I06^2*J09-5745339022535518893071155200000*I06^4+8767555933277950932060000*I03^2*I18-99760088319679289818890000*I03^2*J18+52060079755236719910240000*I03*I06*I15+6040702480330336749099120000*I03*I06*J15+21440495876933649393108000*I03*I09*I12-1083267951798274694550000*I03*I09*J12-5527278689657806710972000*I03*I12*J09-38779017109724498609520000*I03*J09*J12+21661544879140681971832320000*I06^2*I12+8648231828192329427712000000*I06^2*J12-151380934200235493485200000*I06*I09^2+599438997667436771401200000*I06*I09*J09+40564927556701350264000000*I06*J09^2-61163481679649698255200000*I03*I21+11399008052053577484900000*I03*J21-199136917096533901296000000*I06*I18-2031196554384645793219200000*I06*J18-5946449607743720663700000*I09*I15-660716623082635629300000*I09*J15+51035947038740259846432000*I12^2-8534439304137167198400000*I12*J12+12307767792771886955100000*I15*J09+1367529754752431883900000*J09*J15)*j6
        +34076957954414688332305435800*I03^8*I06+2289509161855794979042235805*I03^7*I09-1946978953796176602236171865*I03^7*J09-5265086159872413877964581065600*I03^6*I06^2+42338146194611722367649740700*I03^6*I12-4292615688748106700844583550*I03^6*J12-2922349318661357619903099879782400*I03^4*I06^3-31780187484506667856979078400*I03^5*I15+118939435980244958819720170800*I03^5*J15-7799911089732865830867085404*I03^4*I09^2+61339832942165599730315708574*I03^4*J09^2-198116178347122463897339906101248000*I03^2*I06^4+7925510829353336115316308000*I03^4*I18-125058569898727640974587390000*I03^4*J18-204909236094123217141339680000*I03^3*I21+29384703407128705711569900000*I03^3*J21+251293160662941288401753760000*I03^2*I12^2+8874661096972428425274528000*I03^2*J12^2-1442948209693823260692260078400*I03*I06*J09*J12+1362655633214836456791361027200*I03*I06*I12*J09+3022194087230979037052202364800*I03*I06*I09*J12-11151047621625894918487553990400*I03*I06*I09*I12+1639333729435740047700480000*I15^2+651655113521784148839043576627200000*I06^5-34911011065195842232320000*I03^10+3872797282222609143830254990560*I03^2*I06*I09*J09+10181079988707529413812563200*I09*J09*J12+157428350099913385602989510400*I09*I12*J09+627237862999430513463585792000*I06*I12*J12+17393756872184347456182023193600*I06*J09*J15-172798413649944961165531372800*I06*I15*J09-8343372426098382475740482227200*I06*I09*J15+8298044803768861557222105600*I06*I09*I15-173965943179348923717857872281600*I06^2*I09*J09-18726423285702232913448384000*I03*J12*J15+1693019202434781107906880000*I03*I15*J12+678625634780585979873363936000*I03*I12*J15-59339116870053495136750368000*I03*I12*I15+54323674374687226277055084000*I03*J09*J18-2603748334968881970699211200*I03*I18*J09+19322760746856254529205224000*I03*I09*J18-123576434471994687448473600*I03*I09*I18-73047528758777044257946210680*I03*I09*J09^2+18717544185425122322677906080*I03*I09^2*J09-1113484836949312782600717120000*I03*I06*J21+2542952856551935821194718720000*I03*I06*I21-1307187444669078700496238742080*I03^5*I06*I09-719201734163144405292449442960*I03^5*I06*J09+6462563543554922413887302294400*I03^4*I06*I12-777589987671359478343739505600*I03^4*I06*J12+38702872223406590459289298254*I03^4*I09*J09-173716180370682896525560874346240*I03^3*I06^2*I09+185390663269336846999676181745920*I03^3*I06^2*J09+680596466730478431383413699200*I03^3*I06*I15+2935011906160707270997033401600*I03^3*I06*J15+30547658219546592428117441040*I03^3*I09*I12-3554271728675595902391991560*I03^3*I09*J12+157852836020567666109644356680*I03^3*I12*J09-108298511201308459098851764020*I03^3*J09*J12-302890712391160456917289094784000*I03^2*I06^2*I12+194069722651384652722527600960000*I03^2*I06^2*J12-911431281859122471590758196160*I03^2*I06*I09^2-5179826138433078644167173006240*I03^2*I06*J09^2+5348605796116940170409757144883200*I03*I06^3*I09+6516930886482826537364558876774400*I03*I06^3*J09-1154558706684048391867319808000*I03^2*I06*I18+292639625065426754462306400000*I03^2*I06*J18-25622422664181886212713023680*I03^2*I09*I15-27182310092516527159975827840*I03^2*I09*J15-110546849526289146032272848000*I03^2*I12*J12+58212501085580551120413253440*I03^2*I15*J09+17970122794414105061711082720*I03^2*J09*J15+6848199227556211043742789888000*I03*I06^2*I15-883232135940180015805988293632000*I03*I06^2*J15+411754744962135601407360000*I18*J12+18899144035225781303942784000*J12*J18+182148192159526671966720000*I15*J15-596155736295311046488073216000*I12*J18+18426136927307306010541056000*I12*I18+10747314355119757183703592000*J09*J21+111676729713208838661155904000*I21*J09-44204531759298767472843477600*J09^2*J12+19722862025139771168133881600*I12*J09^2-5315707236601746342260784000*I09*J21-49511214176303734498159488000*I09*I21+4331870735689689308312112000*I09^2*J12-48753988056814830645956083200*I09^2*I12-87341040953685387938764800000*I06*J12^2+19476933549281709205277551104000*I06*I12^2+201209776284917057171468645376000*I06^2*J18-5191689315133502597809935360000*I06^2*I18-24705894072388290657630152140800*I06^2*J09^2+79278829326064471262717743718400*I06^2*I09^2-172294710763801029465677414400000*I06^3*J12-8765406064344999442187239391232000*I06^3*I12+57593050450412184890516605320*I03*J09^3-1192244463671203080784548000*I03*I09^3)*j3
        + (-277888168345311297536000*I03^9+91070271908573623638260400*I03^7*I06+16780146586365107601543690*I03^6*I09-8346620915170956553231170*I03^6*J09-108419568598715975634386505600*I03^5*I06^2+314221882826059958894052600*I03^5*I12-36112646599727327606151900*I03^5*J12-8982263948794028699053518000*I03^4*I06*I09+5278317628074397084471878000*I03^4*I06*J09-296432541291714377869283328000*I03^3*I06^3-230852628710841263154739200*I03^4*I15+958001542040060154128066400*I03^4*J15+63401053265823768544325592000*I03^3*I06*I12-9962874256199207177735820000*I03^3*I06*J12-56545844266023349415288400*I03^3*I09^2+262741860088664998994685000*I03^3*I09*J09+159891086369783911279728600*I03^3*J09^2-976330773364804851383656992000*I03^2*I06^2*I09+477745373512460411835619104000*I03^2*I06^2*J09-37732140672273658961407733760000*I03*I06^4+74746857475123469606376000*I03^3*I18-908649708205707810996444000*I03^3*J18-8114292896706107091225504000*I03^2*I06*I15+83837276643449391127077600000*I03^2*I06*J15+199515844303005658159324800*I03^2*I09*I12-12698936971445598324768000*I03^2*I09*J12+527054075746047630454377600*I03^2*I12*J09-438904857802947143215500000*I03^2*J09*J12+1343812700518040257833817728000*I03*I06^2*I12-19987023698514421350361920000*I03*I06^2*J12-7330317908076177719099472000*I03*I06*I09^2+21572730823810490161817112000*I03*I06*I09*J09-10786369600806581683918296000*I03*I06*J09^2-4250603232549040708605358080000*I06^3*I09+2989251232689359062503106560000*I06^3*J09-770815739294532030496320000*I03^2*I21+131049680249729321279640000*I03^2*J21-1015654549322905817855040000*I03*I06*I18-34660372917052889333379360000*I03*I06*J18-222482328347654550079632000*I03*I09*I15+450630758871443309452272000*I03*I09*J15+325291575976849284822144000*I03*I12^2-153334120633092748603584000*I03*I12*J12+420952050135216950375088000*I03*I15*J09-740360622290076780946128000*I03*J09*J15-536675011920875649600000*I03*J12^2-36424621984157194771226880000*I06^2*I15+391519227082387939483898880000*I06^2*J15+17698629891705281369512704000*I06*I09*I12+389443046884001880235200000*I06*I09*J12-26810816386499941768051968000*I06*I12*J09+739775898295500934778400000*I06*J09*J12-28930688447576604998400000*I09^3+159563873976249429106560000*I09^2*J09-218983057172425994757120000*I09*J09^2+73216896148097715726720000*J09^3+13455264187510442144064000000*I06*I21-784112378233244776632000000*I06*J21+45065110851032788555200000*I09*I18-405585997659295096996800000*I09*J18-198604869603491954203776000*I12*I15+277523320233904002873216000*I12*J15+27848058240294076579200000*I15*J12-63091155191445903977280000*I18*J09+567820396723013135795520000*J09*J18+3094228693366008508800000*J12*J15)*j6
        -1378556299387095186560441886720*I03*I09*J09*J12+3115233314548791860189882787840*I03*I09*I12*J09-116746289851789302207067361894400*I03*I06*I12*J12-269939663109908932508614931005440*I03*I06*J09*J15-31522102561988066560592928430080*I03*I06*I15*J09+60084655181452937011083303813120*I03*I06*I09*J15+9860965141435683809496387747840*I03*I06*I09*I15+5641020838191734859011111093329920*I03*I06^2*I09*J09-29708688459957558214039567050240*I03^2*I06*J09*J12-118371293970288849184793480524800*I03^2*I06*I12*J09-13913842255470822843995783362560*I03^2*I06*I09*J12+24369910920621661137082459176960*I03^2*I06*I09*I12+71977373612562138556673405129472*I03^3*I06*I09*J09-725036846687689721489609932800*I12*J09*J12-783583367799342184238094336000*I09*I12*J12+696998901666727774844776488960*I09*J09*J15+828906717775623581545085214720*I09*I15*J09-2318652964542440361983990169600*I06*J12*J15+1785710365311839334037021900800*I06*I15*J12+252319709386203185505967276032000*I06*I12*J15+28289360290691366053756047360000*I06*J09*J18+22894598590768546695267250176000*I06*I18*J09-11084954441715069807007162368000*I06*I09*J18-9515176134927499696779141120000*I06*I09*I18-5158740550993482310378681466880*I06*I09*J09^2+6335903978650640965883647426560*I06*I09^2*J09+604389203259245738373492323942400*I06^2*J09*J12+446485910002894536408091577548800*I06^2*I12*J09+95064004343088570667842271641600*I06^2*I09*J12-3360675126467585075213020594176000*I06^2*I09*I12-93842748600588141397254144000*I03*I15*J15+1239577390891241592762084710400*I03*J12*J18+55115157195124796758954291200*I03*I18*J12-2714835990530477869500920832000*I03*I12*J18+48833404708602518189105356800*I03*I12*I18-1396568668152219434072391744000*I03*J09*J21+8536965321844763547607696896000*I03*I21*J09+4904884239818851058057166977280*I03*J09^2*J12-7364267058736123359018681600000*I03*I12*J09^2+405006311237149726510629888000*I03*I09*J21-2842410541288921179118166016000*I03*I09*I21-29590311884930280626470917120*I03*I09^2*J12+16553045063318180179723591680*I03*I09^2*I12+4331045742413434089640397107200*I03*I06*J12^2+220251253644380919509296334438400*I03*I06*I12^2-2224814547353303565725834229350400*I03*I06^2*J18-277593447817067612790957052723200*I03*I06^2*I18-1695453567581025311653592514109440*I03*I06^2*J09^2-1423193753154484420785519422423040*I03*I06^2*I09^2+30369679804243382886424550537625600*I03*I06^3*J12-33948642209269656538646076742041600*I03*I06^3*I12-1267986325677468013723270993920*I03^2*J12*J15-86149345919939994159557591040*I03^2*I15*J12+3016097296323076592574132326400*I03^2*I12*J15-615117549963852249906938572800*I03^2*I12*I15+5307174142036719824247278434560*I03^2*J09*J18-428631275495071981979191641600*I03^2*I18*J09-1220878538631347614024253829120*I03^2*I09*J18-744602300508839274998883631296*I03^2*I09*J09^2+681603871068335019152648605824*I03^2*I09^2*J09+30881074958564716482431159808000*I03^2*I06*J21-174257720165933701172576096256000*I03^2*I06*I21+8776184520878334122945955357818880*I03^2*I06^2*J15+1323132961271416901850265006325760*I03^2*I06^2*I15+20918821027867258615116944151674880*I03^2*I06^3*J09-125917667945377775597570775776133120*I03^2*I06^3*I09-99831362774814984177166394880*I03^3*I12*J12-5545177532460623230689900222720*I03^3*J09*J15+1482828336461546180626366586880*I03^3*I15*J09+1095445459532050865627253903360*I03^3*I09*J15-107798950012550908863090769920*I03^3*I09*I15-143991542370201733434511113984000*I03^3*I06*J18+13088687032039468954093136179200*I03^3*I06*I18+94680339206475405624446537581824*I03^3*I06*J09^2-17446876542214470397753763466240*I03^3*I06*I09^2-2065022394987594868439971932979200*I03^3*I06^2*J12+7220537326843739061620299727339520*I03^3*I06^2*I12+671394523817673174790261790496*I03^4*J09*J12-2691005561052527649118719032640*I03^4*I12*J09-49375089006411787567254628992*I03^4*I09*J12+301135878383175904797756149760*I03^4*I09*I12+137543074533135798656700564080640*I03^4*I06*J15-38423554181862407727687409489920*I03^4*I06*I15-1021039081878275580465255406178304*I03^4*I06^2*J09-801978772588026575434427173773312*I03^4*I06^2*I09-245837133879481974684342963888*I03^5*I09*J09-6134329191671709793294653077760*I03^5*I06*J12+34260139253431875445416133839360*I03^5*I06*I12-521142536711970239902627456512*I03^6*I06*J09+7132372431998222721604477279104*I03^6*I06*I09+191826218256883426263040000*I03^11+94425622815498626747547648000*I15*J18-10491735868388736305283072000*I15*I18+1822985784272166600780288000*J12*J21-48052646480503031255691264000*I21*J12+653436241959575629278904320000*I12*J21-2990799162671889279252971520000*I12*I21-219199348307781661763632896000*J09*J12^2+2193273322495718157182678630400*I12^2*J09-1877345052699402674974603100160*J09^2*J15-886184377490320409509892997120*I15*J09^2+89641325073047883619721932800*I09*J12^2+514362565839466822786714828800*I09*I12^2+34240521458702814760084930560*I09^2*J15-196404509804694600496830382080*I09^2*I15+1222868612725590540839481999360*I06*J09^3-1819794655132077016968424980480*I06*I09^3-209219379860192112833619714048000*I06^2*J21+713871562186143284095892127744000*I06^2*I21-310719544224654743996044136310374400*I06^4*J09-101398748263800458849555796747878400*I06^3*J15-4616933301832957027191955213516800*I06^3*I15+1213136620017592077919943541758361600*I06^4*I09-5245867934194368152641536000*I03*I15^2-9414083247929514373250229763099852800*I03*I06^5-2806348860201034386336858636096*I03^2*J09^3-56097224371409083039488116736*I03^2*I09^3+12327067661143161921669861120*I03^3*J12^2+725300853594123265702700544000*I03^3*I12^2+577723364224035445985809067027988480*I03^3*I06^4-103548325721622855003209664000*I03^4*J21+790147476786968642366986752000*I03^4*I21-20667113334565614951547968000*I03^5*I18+292705194711058103988125280000*I03^5*J18-154363070587721137174835630352*I03^5*J09^2+13253561214297920758253447161528320*I03^5*I06^3+38046694815809844951734043264*I03^5*I09^2+90989713264118159073366045158400*I03^7*I06^2-254604022090650524407328720640*I03^6*J15+89646741252981190365241835520*I03^6*I15+6459500294073189363967532640*I03^7*J12-104898607812390129637125447360*I03^7*I12+5532439505584260621187136592*I03^8*J09-4603903574184431290048377744*I03^8*I09-24608525043441076505328032640*I03^9*I06,

        ((20189072461939906560000*I03^8-112212483804577015164900000*I03^6*I06-3365676553346425540939500*I03^5*I09+4333840180446732862693500*I03^5*J09-46040780583488268900120960000*I03^4*I06^2-52357690991325406669290000*I03^4*I12+5399786175277625442045000*I03^4*J12+593001418939295316564600000*I03^3*I06*I09+2447209655859948536014920000*I03^3*I06*J09+122242733858753435936332800000*I03^2*I06^3+36129388999346409432960000*I03^3*I15-152825914504486404747720000*I03^3*J15-12517528909772999623361760000*I03^2*I06*I12+1414413812382498953852400000*I03^2*I06*J12+6940389548644547292360000*I03^2*I09^2-19991844185302862354790000*I03^2*I09*J09-61804194291472739650110000*I03^2*J09^2+106116875595259384449888000000*I03*I06^2*I09-22353097218303721182566400000*I03*I06^2*J09+8332073775878052182040576000000*I06^4-12714989069169001162800000*I03^2*I18+144675259807532008048200000*I03^2*J18-75499187010081459811200000*I03*I06*I15-8760419276707833956625600000*I03*I06*J15-31093690509351652145040000*I03*I09*I12+1570989711490386579000000*I03*I09*J12+8015835730742154045360000*I03*I12*J09+56238566644526373777600000*I03*J09*J12-31414262818008976370841600000*I06^2*I12-12541941448669269826560000000*I06^2*J12+219537455852528915976000000*I06*I09^2-869325540775361152056000000*I06*I09*J09-58828550898363412320000000*I06*J09^2+88701230640259638576000000*I03*I21-16531204806017380962000000*I03*J21+288794704410147660480000000*I06*I18+2945705984983506136896000000*I06*J18+8623730756691909306000000*I09*I15+958192306299101034000000*I09*J15-74013957101686414700160000*I12^2+12376915903292042592000000*I12*J12-17849117147571626238000000*I15*J09-1983235238619069582000000*J09*J15)*j6
        +31318654384289600804906047800*I03^8*I06+688661409012129752134706505*I03^7*I09-698923747831676635634722965*I03^7*J09+21990606898272939860366943417600*I03^6*I06^2+5559582128747300487967574700*I03^6*I12-1265459253391287206461556550*I03^6*J12+4585259992816168404765940772812800*I03^4*I06^3-1719687298483367984313446400*I03^5*I15+26638230468122783015346514800*I03^5*J15+4501137461408392675755246012*I03^4*I09^2-19178187168696347512873376532*I03^4*J09^2+477776392842963370861442421669888000*I03^2*I06^4+2245433791997219874567300000*I03^4*I18-16885404693760324428035910000*I03^4*J18+79549794536746749305378400000*I03^3*I21-8567140600731033984946500000*I03^3*J21-323921420571818273421960288000*I03^2*I12^2+60456937201515528825312000*I03^2*J12^2+8909145242701318655590610995200*I03*I06*J09*J12-45660276312691372557487334553600*I03*I06*I12*J09-4083017003188508674927864598400*I03*I06*I09*J12+28753812080095779920084527123200*I03*I06*I09*I12-4436116288548708531882240000*I15^2-1869463604625009800823107577446400000*I06^5+15101873697898599628800000*I03^10+5940090679633452747887163030720*I03^2*I06*I09*J09-127899375022776262930860225600*I09*J09*J12-187945701708997389347989747200*I09*I12*J09-2660690298924661864433642496000*I06*I12*J12-58422330298501351277946796108800*I06*J09*J15-6629807471490760498905869337600*I06*I15*J09+16969489487147665588189010457600*I06*I09*J15+2947136473336126021137486835200*I06*I09*I15+753729763412428177928312593612800*I06^2*I09*J09-178196370720369962873951808000*I03*J12*J15-12562483439347297452077760000*I03*I15*J12-1179830538107754027915641760000*I03*I12*J15+208264721625402587062325856000*I03*I12*I15+524970790343803668152830752000*I03*J09*J18-59450382473882472395447846400*I03*I18*J09-234918333889039273920054552000*I03*I09*J18+10863525919188847130255836800*I03*I09*I18-47568746879955738306818620560*I03*I09*J09^2+68594998268176449083329185360*I03*I09^2*J09+2106112825660826222837049600000*I03*I06*J21+608884380164079930865489920000*I03*I06*I21+827497367962182890167878673200*I03^5*I06*I09-109186150988514000257915461200*I03^5*I06*J09+10171100538538465795026626635200*I03^4*I06*I12-2132976412625465636804722744800*I03^4*I06*J12-22501607053029673172699086992*I03^4*I09*J09-26867850581262488042283616327680*I03^3*I06^2*I09-72513728968995489765665265039360*I03^3*I06^2*J09-5754348465137986719805432214400*I03^3*I06*I15+26378235515680108053431612428800*I03^3*I06*J15+59525763949124973636660604080*I03^3*I09*I12-16195429720039308928599112920*I03^3*I09*J12-317022877467959408346884955840*I03^3*I12*J09+89200026024795227038805930160*I03^3*J09*J12+1876533920961924188991770989056000*I03^2*I06^2*I12-526117860950037269550920236800000*I03^2*I06^2*J12-1978540280067707277416197456320*I03^2*I06*I09^2+4080310362299539340564616702720*I03^2*I06*J09^2-17339912255498662254653400182169600*I03*I06^3*I09-13477092890546900803016404161331200*I03*I06^3*J09+2284827699964025451784723776000*I03^2*I06*I18-20743840895455262401374382272000*I03^2*I06*J18-31425808891310325947282708160*I03^2*I09*I15+266701675215189745751935921920*I03^2*I09*J15+30679189721903409551739504000*I03^2*I12*J12+181016118122835203628407023680*I03^2*I15*J09-674409142121077792745612372160*I03^2*J09*J15+2497060084587656874723636691968000*I03*I06^2*J15+8073753693433757692715520000*I18*J12+175821305181754499181347328000*J12*J18-492901809838745392431360000*I15*J15+1166768407914312485755795392000*I12*J18-107178347716223673573222336000*I12*I18-114916745314058774065955136000*J09*J21+393380172186383150825107968000*I21*J09+399854318588058698560493740800*J09^2*J12-539200963095409671396320332800*I12*J09^2+30000069594742264500882672000*I09*J21-87440335965870920232391296000*I09*I21+6228625545756886393561104000*I09^2*J12+100667930094693487249209561600*I09^2*I12-326216199836879677092096000000*I06*J12^2-49356259670134177925382844416000*I06*I12^2-822684035737307787769622873088000*I06^2*J18+120476461447135146578222269440000*I06^2*I18+3024543717021788258174580326400*I06^2*J09^2-221691104688625332698176604467200*I06^2*I09^2+23743784875337847013968691200000*I06^3*J12+35075721271968261284349221830656000*I06^3*I12-219376453210153675266456682560*I03*J09^3-11008810476025386002047692000*I03*I09^3)*j3
        +(477715069588368711680000*I03^9-226032009174410862344292000*I03^7*I06-29348767548460033757678700*I03^6*I09+16847950222100395629359100*I03^6*J09+152569105610981648599096128000*I03^5*I06^2-541161904393842204377898000*I03^5*I12+61055492704583739169437000*I03^5*J12+14998822199557325423585424000*I03^4*I06*I09-6445062110221184195977392000*I03^4*I06*J09+1204232276433388599401518080000*I03^3*I06^3+398415415466109887145216000*I03^4*I15-1639071405642038315846472000*I03^4*J15-109667135066760013478904000000*I03^3*I06*I12+17400926064182710643667360000*I03^3*I06*J12+93454938511533287429076000*I03^3*I09^2-446291762516582863266918000*I03^3*I09*J09-330065758758990409373610000*I03^3*J09^2+1658906687446024555066792320000*I03^2*I06^2*I09-888642755344022770319437440000*I03^2*I06^2*J09-20294183957746639072359628800000*I03*I06^4-125825019817568371256880000*I03^3*I18+1571478387362638810299720000*I03^3*J18+12807930738750093375004800000*I03^2*I06*I15-141271560780324718345680960000*I03^2*I06*J15-390697972690901189079024000*I03^2*I09*I12+36201913093797127402320000*I03^2*I09*J12-968498391430881966948048000*I03^2*I12*J09+794768713692537974355000000*I03^2*J09*J12-2406239878007493167135408640000*I03*I06^2*I12+68604675266402279692934400000*I03*I06^2*J12+12684299682533242170214080000*I03*I06*I09^2-36607066028284397685973920000*I03*I06*I09*J09+20959999492759528422725280000*I03*I06*J09^2+5068990137902423702686617600000*I06^3*I09-3231439036809417870105600000000*I06^3*J09+1466465864364749187273600000*I03^2*I21-241341899338887714133200000*I03^2*J21+2605274929113593804524800000*I03*I06*I18+58247894113588239239894400000*I03*I06*J18+399567124013844196428480000*I03*I09*I15-802814228979916063982400000*I03*I09*J15-676662270908455161933120000*I03*I12^2+359921955880468305868320000*I03*I12*J12-748554273596167813414080000*I03*I15*J09+1241684064618709381427520000*I03*J09*J15-9041140242436144651200000*I03*J12^2+83841659454802221058867200000*I06^2*I15-614459459049174542305152000000*I06^2*J15-31685169908181902904933120000*I06*I09*I12-549026592567853141728000000*I06*I09*J12+54051899585774928841866240000*I06*I12*J09-4618762974482537343254400000*I06*J09*J12+50806870462778504256000000*I09^3-280219431706247596550400000*I09^2*J09+384568927195184986060800000*I09*J09^2-128580464478877906924800000*J09^3-30668590929107546843904000000*I06*I21+2190179253118577057568000000*I06*J21-79141471297789593168000000*I09*I18+712273241680106338512000000*I09*J18+313429867007929364105280000*I12*I15-517295940414149374994880000*I12*J15-46294689316630439664000000*I15*J12+110798059816905430435200000*I18*J09-997182538352148873916800000*J09*J18-5143854368514493296000000*J12*J15)*j6
        +49307034438404719514948087193600*I06*I12*I15+1379996453358133169015700956160*I03*I09*J09*J12-2749578191183747709442232835840*I03*I09*I12*J09+248292722382522185269377361152000*I03*I06*I12*J12+624993693692945615389402088325120*I03*I06*J09*J15-1060832040403750885235697500160*I03*I06*I15*J09-163419917449664609209409006223360*I03*I06*I09*J15+16436757564727728441882958356480*I03*I06*I09*I15-11710912695335088543644561363496960*I03*I06^2*I09*J09+84595791753241197768504411909120*I03^2*I06*J09*J12+301651065865996939081433793530880*I03^2*I06*I12*J09+64872454618499354543956371886080*I03^2*I06*I09*J12-169542404588685928916217959562240*I03^2*I06*I09*I12-215430992655205819574748445053696*I03^3*I06*I09*J09-3824573574404810823316250342400*I12*J09*J12+1271208594398865918019257600000*I09*I12*J12-897975663945284492349829447680*I09*J09*J15-1662479199283060884575484149760*I09*I15*J09-47288997788581746474235409203200*I06*J12*J15-13104180405498485991236109926400*I06*I15*J12-465060518052906913379128767283200*I06*I12*J15-71783544875608738388087746560000*I06*J09*J18-56476529598688598539287318528000*I06*I18*J09+35873010101754975762120904704000*I06*I09*J18+13918926245901637312732262400000*I06*I09*I18+11851951726031376827896579031040*I06*I09*J09^2-18286853708575520542145777172480*I06*I09^2*J09-2766346965240611485981906254643200*I06^2*J09*J12+2126689312381854143041619317555200*I06^2*I12*J09+645638613481732128577605174067200*I06^2*I09*J12+4165959483137647075866343155302400*I06^2*I09*I12+253943012428921626180636672000*I03*I15*J15-891437934198114407778418483200*I03*J12*J18-268862102256268560246733209600*I03*I18*J12+1296740983120320312128776320000*I03*I12*J18+363139366842808512426444441600*I03*I12*I18+2881460438244081299711314944000*I03*J09*J21-16243630514419973699841859584000*I03*I21*J09-10623380638990225901821742499840*I03*J09^2*J12+16632430402983791265580627848960*I03*I12*J09^2-586880558361110297148302592000*I03*I09*J21+3505581792757975871049725952000*I03*I09*I21+143024789541780844886092584960*I03*I09^2*J12-361398415474227090781210314240*I03*I09^2*I12-9721019748229600158307893657600*I03*I06*J12^2-423576725887342020872606928998400*I03*I06*I12^2+2883272126725250708812743768883200*I03*I06^2*J18+1966418128652466814623793719705600*I03*I06^2*I18+4239253702355968729825972938731520*I03*I06^2*J09^2+2689224377639897819224953016197120*I03*I06^2*I09^2-92655083222461123930508325846220800*I03*I06^3*J12+199087989296971560396523075215360000*I03*I06^3*I12+955217440422808222235839119360*I03^2*J12*J15+585278012525086717218409144320*I03^2*I15*J12-2794900614871279491983572669440*I03^2*I12*J15+95779532901403681551700254720*I03^2*I12*I15-12566554107397897567237452564480*I03^2*J09*J18+1002365650370299855227140044800*I03^2*I18*J09+2208974730241404849558634920960*I03^2*I09*J18+2585456889875608835813177058048*I03^2*I09*J09^2-1330762454257570072265682392832*I03^2*I09^2*J09-80410282161760439570201216256000*I03^2*I06*J21+433254052673486971751554136064000*I03^2*I06*I21-21446702119360273221866488617123840*I03^2*I06^2*J15-3014956322655742792020916366663680*I03^2*I06^2*I15-36356649788497132952593036866109440*I03^2*I06^3*J09+293773087922468945621138146652405760*I03^2*I06^3*I09+345122518689456277226476337280*I03^3*I12*J12+13280610345511152180903191239680*I03^3*J09*J15-3832023917962113170491622937600*I03^3*I15*J09-2286027827920399906448697231360*I03^3*I09*J15+338504621527591106172326784000*I03^3*I09*I15+424451145554311360032654374016000*I03^3*I06*J18-26828475964528079310913321113600*I03^3*I06*I18-196043394022562065448534469841152*I03^3*I06*J09^2+37728021769236725409778289241600*I03^3*I06*I09^2+5917368054174122644434378562867200*I03^3*I06^2*J12-23473563043722388391851937595187200*I03^3*I06^2*I12-841478937006908555340120684288*I03^4*J09*J12+5063791475136974320257677134272*I03^4*I12*J09+184454010623392680489891532416*I03^4*I09*J12-841592323060028333559930285504*I03^4*I09*I12-453407980099043276409262615741440*I03^4*I06*J15+107901380476968408375513496197120*I03^4*I06*I15+1628580196997561673130075869284352*I03^4*I06^2*J09+3329891383237085482922444813346816*I03^4*I06^2*I09+266104895751204139914463342080*I03^5*I09*J09+28067926932753754614949847491200*I03^5*I06*J12-169877057445014909320511431776000*I03^5*I06*I12+8803093178037494680768578555072*I03^6*I06*J09-9607332771874790683723258951104*I03^6*I06*I09-89909568352291969433600000*I03^11-255520298220405611436417024000*I15*J18+28391144246711734604046336000*I15*I18-237636816640712638638741504000*J12*J21+1724697289665565826299379712000*I21*J12-447144769141331544105387264000*I12*J21-1697155231313917528980277248000*I12*I21+1405410258195111190380438528000*J09*J12^2+2182190944834321979587564953600*I12^2*J09+4291455274557506514497747681280*J09^2*J15+2192899752693177896384470056960*I15*J09^2-139515974854388116255608422400*I09*J12^2-1030381952304245264009317785600*I09*I12^2-43631788597646117937419796480*I09^2*J15+292478376217139879726306672640*I09^2*I15-1842541755399035927304041594880*I06*J09^3+3906234556217821191137570979840*I06*I09^3+794526346253720461195691864064000*I06^2*J21-3560370922214829272732263022592000*I06^2*I21+994334034494012716784404337865523200*I06^4*J09+329547092351194193586977995436851200*I06^3*J15+17608157688379671169638744696422400*I06^3*I15-4044347507539440760825189811670220800*I06^4*I09+14195572123355867302023168000*I03*I15^2+26319076992278906973697200988776038400*I03*I06^5+5565187115377085408130922687488*I03^2*J09^3+92208580035539593787640396288*I03^2*I09^3-42537621253713056801793192960*I03^3*J12^2-1174077283875284977816204949760*I03^3*I12^2-1511575434408024614056923582417469440*I03^3*I06^4+6786848344259023018614720000*I03^4*J21-174876331636010509374159360000*I03^4*I21-15897439652759944959314880000*I03^5*I18+309274926312475485361752480000*I03^5*J18-77735180352609824701833817920*I03^5*J09^2-23438089740396952319193263645614080*I03^5*I06^3-34875456004924058784688476480*I03^5*I09^2-242876112383526418935311508195840*I03^7*I06^2-349094952726775293510284601600*I03^6*J15+47035766265783481278805708800*I03^6*I15+15955833177673813665899229600*I03^7*J12-90823336848745961213755310400*I03^7*I12+7378027706712754522824104880*I03^8*J09-8781617542140625446884738160*I03^8*I09-272847420791097624752964969600*I03^9*I06,

        ((12138877523668243409029479168000*I03^8-81682199770763452685061769988916600*I03^6*I06-2348158596142264459492439364795585*I03^5*I09+3271972610984908498682844894111405*I03^5*J09-33211715083488840312884352351316377600*I03^4*I06^2-36597627135301383850548078328077900*I03^4*I12+3554003382015856498431942575251350*I03^4*J12+452418755150356575546075952609490400*I03^3*I06*I09+1931908713910632830846733953000032800*I03^3*I06*J09+324822212940538626801139270368804096000*I03^2*I06^3+25514212577354839103251547979388800*I03^3*I15-109081870665376793277487665741951600*I03^3*J15-8643116679430298087789353715809824000*I03^2*I06*I12+900107001006190344999467649270144000*I03^2*I06*J12+4982764154736664444649544377894700*I03^2*I09^2-15518153959478723223398835985115700*I03^2*I09*J09-49144261893693845246638803579967200*I03^2*J09^2+82125036642526305251115962197448928000*I03*I06^2*I09-21506890558655975555715043056899904000*I03*I06^2*J09+7754462610133568629562737811657072640000*I06^4-8566359138947041246708355671524000*I03^2*I18+105771259220067615964064598371286000*I03^2*J18-24495233729409108034860714529320000*I03*I06*I15-6377764092921873290995331017676760000*I03*I06*J15-23665052476029112854944024047338000*I03*I09*I12+1840337188857378203068077270129000*I03*I09*J12-11079941863622715467593105684914000*I03*I12*J09+47137867799651773347165702923043000*I03*J09*J12-37535690461182249060656059281995520000*I06^2*I12-10181133845279593599862945438202880000*I06^2*J12+203451059994283535072194637211816000*I06*I09^2-755551618721919959546103467264280000*I06*I09*J09-3964809824978190504739618868064000*I06*J09^2+83108596460973172046681296517280000*I03*I21-13798093239159416198029108365660000*I03*J21+276026000377561640701723045702080000*I06*I18+2638288593435794443033861606178880000*I06*J18+8296816500511719835491354302946000*I09*I15+391598061103369417939103833938000*I09*J15-58426951853216096379619575223248000*I12^2+15876971473952648185497262211040000*I12*J12-17024209187550889136674558036662000*I15*J09-8785094505012113899909668378246000*J09*J15-821783907306745325249134786560000*J12^2)*j6
        -39736772718201663128638747895499670800*I03^8*I06-2810405872382195498525750056514690430*I03^7*I09+2377275613513877708009423029926765990*I03^7*J09+8644196603116521544137915494544189753600*I03^6*I06^2-52686158516751338356897219241488228200*I03^6*I12+5268290882080631932121017002716697300*I03^6*J12+3869516957740378217038413489779190115430400*I03^4*I06^3+39935929491535718339487252523386230400*I03^5*I15-148708896804041737186810385530188112800*I03^5*J15+9757944799168447604550815741616174234*I03^4*I09^2-79061754492664232421053460047776461549*I03^4*J09^2+287466867438808076033806406876342988791808000*I03^2*I06^4-9951501382909081585306539928056504000*I03^4*I18+156913754656321912842436489438357908000*I03^4*J18+261044926278119804641934050209397440000*I03^3*I21-37272996888407468437624703531952840000*I03^3*J21-331238158272980945512259336030217744000*I03^2*I12^2-10076480837667678541251576497156496000*I03^2*J12^2+2209325723362163392750552873109526122400*I03*I06*J09*J12-4576706174903675013861804320234816059200*I03*I06*I12*J09-3726998220408258405997190728759968100800*I03*I06*I09*J12+13903629102232136104440809755695426134400*I03*I06*I09*I12-2342980652528135443914269914533120000*I15^2-909538413054949030958533840227145234513920000*I06^5+45371694673638615150941328936960000*I03^10-4188378480268270709351741266448000505360*I03^2*I06*I09*J09-25603430923928092324707497810667139200*I09*J09*J12-184354144194460869451757956824091094400*I09*I12*J09-760525821554283084486328149786803712000*I06*I12*J12-26277827174760268252287299950151142873600*I06*J09*J15-917880241839519403884933288369916387200*I06*I15*J09+10828464612903065234582909596973176819200*I06*I09*J15+465108432101368275766889894200407878400*I06*I09*I15+278137609880152511253693740976120228249600*I06^2*I09*J09-15282008616501175014254488570317216000*I03*J12*J15-6206473327668946716870886737849120000*I03*I15*J12-824765235007978896596191899348547248000*I03*I12*J15+109835085373610079981928819547599056000*I03*I12*I15-58194684981851395532616096583694958000*I03*J09*J18+4762498937350033147220653294140271200*I03*I18*J09-21733982054344033663784988059347716000*I03*I09*J18-3344175268576095742748899893592934400*I03*I09*I18+85355260282316011081442915801628617580*I03*I09*J09^2-23474504588299809484352075780763822480*I03*I09^2*J09+1707359148983670132339625571118564480000*I03*I06*J21-4221289942097188848023461776367795200000*I03*I06*I21+1717477084576657216237848868048237818480*I03^5*I06*I09+894107901598456753784434033010123255160*I03^5*I06*J09-7029694054205427711801335886233580902400*I03^4*I06*I12+724000999549856664660838368240908937600*I03^4*I06*J12-49334323291098406327799470578103254369*I03^4*I09*J09+207702899378579933827116684411115785047040*I03^3*I06^2*I09-219084235216782789737761441049760418609920*I03^3*I06^2*J09-1347433517864113771652318416514295283200*I03^3*I06*I15-1510717095742857007906941262844292921600*I03^3*I06*J15-40868004739415086156547714664248830440*I03^3*I09*I12+3043079111075280721066428101300217060*I03^3*I09*J12-218100500911083175392038243083799155380*I03^3*I12*J09+143306863060128459257910661833326165370*I03^3*J09*J12+609646186780860942997154927359334067456000*I03^2*I06^2*I12-300147786425937701105151348046361046912000*I03^2*I06^2*J12+1106180493117281567775742750397070464160*I03^2*I06*I09^2+6587056630777882311103641361537827878640*I03^2*I06*J09^2-8635290886478277229454807843797780614451200*I03*I06^3*I09-9063317343659594223069039138052241863526400*I03*I06^3*J09+1546891974365339068326556894337888160000*I03^2*I06*I18-2105271963830654004964097431098974304000*I03^2*I06*J18+37741828814052059468837308837925126880*I03^2*I09*I15+31351148931102646989973968800360821440*I03^2*I09*J15+132621692659428713209757524014565896000*I03^2*I12*J12-65975314393157981410611946546323006240*I03^2*I15*J09-39149072592837208587941903555935299120*I03^2*J09*J15+1338699123116813520946588941908475019776000*I03*I06^2*J15+2108012110252019508444752968925760000*I18*J12+14314788370574250332850634715591616000*J12*J18-260331183614237271546029990503680000*I15*J15+723856879715911875930566065282472448000*I12*J18-43973852702143428573710225791882752000*I12*I18-27533089477293266264960235045695652000*J09*J21-56400300737290012732076703482200224000*I21*J09+98317606933599268155827645591041935600*J09^2*J12-84373612405281800366584915107208713600*I12*J09^2+8923901432247645426533571832512504000*I09*J21+44321143942375310278703018613774528000*I09*I21-3278107111085667165995801038142712000*I09^2*J12+62311078002840873638930974806761491200*I09^2*I12-5538852043139302473949878870328320000*I06*J12^2-26635845489357857145945149694191821056000*I06*I12^2-316223921828170348862651335691099214336000*I06^2*J18+25270301787046445678163374214192407040000*I06^2*I18+32401618047882388218848223375646206796800*I06^2*J09^2-109110775896713030095291758710686524518400*I06^2*I09^2+167247857570455682760867612390505635840000*I06^3*J12+13759527956703010512431841897359766700032000*I06^3*I12-90400810672768795028448143133243558420*I03*J09^3+2078348553589701335349110053356090000*I03*I09^3)*j3
        +(451593882645775667841005555712000*I03^9-241599791416781755689014703256051320*I03^7*I06-27016872506647715072941429503569697*I03^6*I09+15804853773967537842494219065755021*I03^6*J09+105547296268958504098249126060089428160*I03^5*I06^2-491567805198028054595850643167039180*I03^5*I12+55898573492152434145517975026010070*I03^5*J12+12648423673398884525839771090372952568*I03^4*I06*I09-3818956529399525151542324677610224344*I03^4*I06*J09+748349837284537136005650742621277306880*I03^3*I06^3+361728420376852924348161444915893760*I03^4*I15-1455049336560897581101823369221390320*I03^4*J15-103156422179137630178196057988854480480*I03^3*I06*I12+16696167692467994418995339981987110320*I03^3*I06*J12+76212388786345650738604384881721992*I03^3*I09^2-378789576064042383625710381756875604*I03^3*I09*J09-336346810272166049328723518598845436*I03^3*J09^2+1521210952817919112377719152427947297920*I03^2*I06^2*I09-882165681713739569939243289186163966080*I03^2*I06^2*J09+28781897820406677575094859715089874534400*I03*I06^4-113311905972932122899057682307402400*I03^3*I18+1401760535646520532535487679476335600*I03^3*J18+12265588846769108436657604483278572160*I03^2*I06*I15-129463986608033223255186040604594997120*I03^2*I06*J15-445491869035584827309932493805234240*I03^2*I09*I12+51870740883358830756358528185287040*I03^2*I09*J12-747097368929860308523672178719460160*I03^2*I12*J09+711531073281825179407514103582394800*I03^2*J09*J12-2592006041463166469407724073134684121600*I03*I06^2*I12+39970387398736508704577489584915027200*I03*I06^2*J12+12846703494167857618797084887222141760*I03*I06*I09^2-38540914370557006048236119703235240800*I03*I06*I09*J09+25200852967984442657452923540318564960*I03*I06*J09^2+787906687596010971690665991592212480000*I06^3*I09-3681193592104571931204051695129822208000*I06^3*J09+1347338912793136399062576238407840000*I03^2*I21-222620470735165126026555259483740000*I03^2*J21+1669326269355921576151258004567865600*I03*I06*I18+55733384811959322527702157277801449600*I03*I06*J18+393973359567178614259929054379076160*I03*I09*I15-845422170004970072823727146668713920*I03*I09*J15-754432349868697766829091562641420800*I03*I12^2+442940534319558672117213770373753600*I03*I12*J12-764882302545753502471543439415587520*I03*I15*J09+1481350975164630642579812594910815040*I03*J09*J15-21827145458825697248921138701305600*I03*J12^2+89245993561448083618416721184845440000*I06^2*I15-203581303402463397082059469876118016000*I06^2*J15-35205195521645527242469628480249318400*I06*I09*I12-445170520341726235170948006649056000*I06*I09*J12+78347616724994230173094417753208755200*I06*I12*J09-8696563958920748719850425228935888000*I06*J09*J12+53150873044228984977113541660134400*I09^3-314034860072779307532433625034124800*I09^2*J09+488270713164411544666109695690444800*I09*J09^2-172270500694539568572085634294208000*J09^3-34808828861886464839170706109164800000*I06*I21+3119949976150115879302336528251360000*I06*J21-86968585794884639596442124524179200*I09*I18+736901906228380363657200690661574400*I09*J18+225823238218311505220591193544819200*I12*I15-574802689655462949641707627217702400*I12*J15-32125707446920810522323104903616000*I15*J12+145701707459880645219011763167827200*I18*J09-1288407684176135110615716653482425600*J09*J18-3569523049657867835813678322624000*J12*J15)*j6
        +(-50513492508143608211394560000*I03^7+18751820460959774086186777604640*I03^5*I06+2404805205824932577539102094844*I03^4*I09-745131013518984702631909730892*I03^4*J09-10357769941445761312204456012200960*I03^3*I06^2+39546161549986449589785271665360*I03^3*I12-5560041738809228082180294473640*I03^3*J12-913110386066259311361066958002240*I03^2*I06*I09+1382650637299174719151868299705920*I03^2*I06*J09+1236538004838999848050517530599628800*I03*I06^3-27146769012049676593029288952320*I03^2*I15+108236395484987433157644106098240*I03^2*J15+7284997148582440293610986341971200*I03*I06*I12-1556076785377117804251613038172800*I03*I06*J12-6649911581216871754019344557600*I03*I09^2+29186960067696062537415056095920*I03*I09*J09-7882656918363711919960048586160*I03*J09^2-43407054348667633159527056176742400*I06^2*I09-6868817098152425545798766122905600*I06^2*J09+10650288438616611547606778121600*I03*I18-93405174953030636838625456142400*I03*J18+56015733311325526259651672102400*I06*I15+5138362638414774528790502294323200*I06*J15+1390776262880242860118134489600*I09*I12-1738470328600303575147668112000*I09*J12+26779840806523825285253440704000*I12*J09-18705200961131351445790973707200*J09*J12+15091402001466465077877629568000*I21+4894841989037734179671093904000*J21)*j6^2
        +1763011690252098420658101879571532190720*I03*I09*J09*J12-3247823357770973033853318022569952404480*I03*I09*I12*J09+122930521519530380959509277215023083008000*I03*I06*I12*J12+415344602259464450294680222712613361459200*I03*I06*J09*J15+40956890545956300659072573344309177113600*I03*I06*I15*J09-95041890431858142672723346143234410496000*I03*I06*I09*J15-8283455164155605817694128664282310246400*I03*I06*I09*I15-8389536073096868223041479876115366673100800*I03*I06^2*I09*J09+45363387462964697358889376976498643511040*I03^2*I06*J09*J12+200298973182501091522221402704642189836800*I03^2*I06*I12*J09+26857262324882413739676099491706436254720*I03^2*I06*I09*J12-78387152721562821094931222589343708569600*I03^2*I06*I09*I12-113106938397780346384354194674168884614528*I03^3*I06*I09*J09-525465566779597029847559336508258508800*I12*J09*J12+962713336951570894111634191110061056000*I09*I12*J12-806967106060144441419274642662672322560*I09*J09*J15-1313327820662230737093624503905163857920*I09*I15*J09-15894992595544963365835357194875815526400*I06*J12*J15-4497036298825433301700313544830470348800*I06*I15*J12-258591468199497401376167258577942872064000*I06*I12*J15-35601463480646034792023125337626414694400*I06*J09*J18-36300516834517440455640168343048181760000*I06*I18*J09+12495971444469684099062086523375117107200*I06*I09*J18+13605672370403247293588816308877719142400*I06*I09*I18+9095461420320328562845502701114682081280*I06*I09*J09^2-9475231792825388856372426028683083612160*I06*I09^2*J09-811542370217272318779367126248316658073600*I06^2*J09*J12-809627503936856785758225029917002321100800*I06^2*I12*J09+115683024013132360802593696231493858918400*I06^2*I09*J12+3656044077233178846336684816530566221004800*I06^2*I09*I12-205172884142250586003307322336079872000*I03*I15*J15-1310943025396075874368004273597016038400*I03*J12*J18-134360672823747182280198016344931891200*I03*I18*J12+1059526531834037674662787227954794188800*I03*I12*J18+249066928165275601557529522771865088000*I03*I12*I18+2045728144077020510979527505277446816000*I03*J09*J21-12424236488260744908314945730005597952000*I03*I21*J09-7280540737407956885562777974716573476480*I03*J09^2*J12+11050313310835667151106555235229884421120*I03*I12*J09^2-553985115613885160222613590845702656000*I03*I09*J21+3799213248031019895029198168080281600000*I03*I09*I21+50837612327444437583940175287253086720*I03*I09^2*J12-219573795699436650629867708768949473280*I03*I09^2*I12-2615555967365623645224230626400931993600*I03*I06*J12^2-166763718016301710802398163609248011878400*I03*I06*I12^2+3027056846224961106601772199066793691136000*I03*I06^2*J18+534568925879406529561795803698842811596800*I03*I06^2*I18+2440816894277480484971003115203971299102720*I03*I06^2*J09^2+2065414508200581762042345193098346545684480*I03*I06^2*I09^2-42676310475998555983114379041426511219097600*I03*I06^3*J12+52097592058946428095529258283500517528371200*I03*I06^3*I12+1334622550721874884349692479106871352320*I03^2*J12*J15+272730077567476190876861829684589731840*I03^2*I15*J12-1424305828760856744300812322879090862080*I03^2*I12*J15+38344896505362106474873974439254743040*I03^2*I12*I15-7833698535247732624589157051238405944960*I03^2*J09*J18+620201055558546051025988796419399212800*I03^2*I18*J09+1772457670801609200488170018101733816320*I03^2*I09*J18+1214805888623075539515478440757330454496*I03^2*I09*J09^2-981752067559746984060631485390575248704*I03^2*I09^2*J09-47205135993000479085082926178592599296000*I03^2*I06*J21+265710237575874384084798509897602553856000*I03^2*I06*I21-13664846760056984748083875301998639543173120*I03^2*I06^2*J15-1930514313395069747682307531141336462909440*I03^2*I06^2*I15-28794916713350476294923801171587211757486080*I03^2*I06^3*J09+191533564811849108273245920077660335588392960*I03^2*I06^3*I09-40880746196188628664490635355992080640*I03^3*I12*J12+8225146317800544929762855857221366564480*I03^3*J09*J15-2214337045461150563473652992726283612160*I03^3*I15*J09-1654850415515162855501649303152261775360*I03^3*I09*J15+168872447233242245068813014424497285120*I03^3*I09*I15+221619674813570015397590926698467064652800*I03^3*I06*J18-18826074124411599518375123606358389606400*I03^3*I06*I18-136433987660231542784862871529375509112448*I03^3*I06*J09^2+25921114146387172708493628588251330769408*I03^3*I06*I09^2+3266712901945469438518804258600050095370240*I03^3*I06^2*J12-12093253956667605178830559619481201775042560*I03^3*I06^2*I12-919263393084966977826496005298652659536*I03^4*J09*J12+3834853182197399321448509720024683347744*I03^4*I12*J09+79963459527870031529092562919813586752*I03^4*I09*J12-433977618662964470022595416074628062208*I03^4*I09*I12-217647957657233364262669802624292193950720*I03^4*I06*J15+58926611581443752962526416768241041551360*I03^4*I06*I15+1373745750024621527300749873500691637354496*I03^4*I06^2*J09+1341815807561472743542145898165584809187328*I03^4*I06^2*I09+333274381172290645125238193814216855000*I03^5*I09*J09+10771130096751768781196524277543339687040*I03^5*I06*J12-60697443661506088063102413644101679842560*I03^5*I06*I12+1601241930785318605446364971240744377856*I03^6*I06*J09-9993376858161572199383797145011108358592*I03^6*I06*I09-250230793143009296831011575103488000*I03^11+204339824354685026734360026366468096000*I15*J18+14995076176180066841051327453011968000*I15*I18-65375094427162424275488641659554048000*J12*J21+439936342160314010909146036956370944000*I21*J12-605775197690392509667153953729036288000*I12*J21+2354180557411882896795968763326275584000*I12*I21+534321535797324874541463718966939008000*J09*J12^2-1037128982972027313220050760934757580800*I12^2*J09+2513831306989587818007210633335118274560*J09^2*J15+1380971061089023814110265314255166545920*I15*J09^2-104252124893030280935714917608547276800*I09*J12^2-716816236886242906805821880693003059200*I09*I12^2-33271905507143106172466218266417807360*I09^2*J15+295213534412983668863940825866237460480*I09^2*I15-2459888422686831878481029817698859663360*I06*J09^3+2247725285864118489211079794498316206080*I06*I09^3+275213210341000616291730918459839311872000*I06^2*J21-864191419827810847426705264102670893056000*I06^2*I21+428522258635936448971871851887219540413644800*I06^4*J09+138887628379693396329565153632484893170073600*I06^3*J15+6117361661880741908392974336291638899507200*I06^3*I15-1653862041570256128429659695608153595969536000*I06^4*I09+7497538088090033420525663726505984000*I03*I15^2+13263352671942979993222932455915133360616243200*I03*I06^5+4053632099578105689715730799152454836256*I03^2*J09^3+83483701259788711663483297467055113216*I03^2*I09^3-9436017919545916242118692311831541120*I03^3*J12^2-150657458886150102830801490825438443520*I03^3*I12^2-893235478907638239674072494691330558516920320*I03^3*I06^4+128049471919151014107357111612919104000*I03^4*J21-987327930252459050913970555783884288000*I03^4*I21+24848219387579781427664230353628454400*I03^5*I18-341042069224965826780145779628315577600*I03^5*J18+184278433158469466014430511215496744840*I03^5*J09^2-18439434965298579505445334140831012501053440*I03^5*I06^3-52443572100816731118922965148186268160*I03^5*I09^2-139207526289018658439737390854220858329600*I03^7*I06^2+290392721817290399472838996589365720320*I03^6*J15-108169851512779259746530372474618869760*I03^6*I15-6287217139741031726513912663538431520*I03^7*J12+121377696479862211915144411785725436480*I03^7*I12-6135584926589752781295896487714431856*I03^8*J09+4835483788529951082074277407393919792*I03^8*I09+1115973154374996828295599235431419520*I03^9*I06,

        ((-37761582049519426560000*I03^8+209881901318400315808650000*I03^6*I06+6295151575731319631970750*I03^5*I09-8106001990530202581099750*I03^5*J09+86114541265074988069440960000*I03^4*I06^2+97929672005463893083665000*I03^4*I12-10099744259772406636732500*I03^4*J12-1109148118566215677577100000*I03^3*I06*I09-4577253778564733595342420000*I03^3*I06*J09-228642451666218814433932800000*I03^2*I06^3-67576303451769982752960000*I03^3*I15+285845143244361386675220000*I03^3*J15+23412749440308167282531760000*I03^2*I06*I12-2645515455400136680277400000*I03^2*I06*J12-12981284300744230099860000*I03^2*I09^2+37392686858085781175415000*I03^2*I09*J09+115598384132880463973235000*I03^2*J09^2-198480693562481715195888000000*I03*I06^2*I09+41809167620806812731366400000*I03*I06^2*J09-15584286406599788164632576000000*I06^4+23782078344575561887800000*I03^2*I18-270600182552057717135700000*I03^2*J18+141213458435388735211200000*I03*I06*I15+16385462577799289084325600000*I03*I06*J15+58157547733048539200040000*I03*I09*I12-2938374558872374891500000*I03*I09*J12-14992795692447811290360000*I03*I12*J09-105188450469833685477600000*I03*J09*J12+58757145241006775158041600000*I06^2*I12+23458410581616489346560000000*I06^2*J12-410622214950505495476000000*I06*I09^2+1625983947386228216556000000*I06*I09*J09+110032749438625102320000000*I06*J09^2-165906522205511355576000000*I03*I21+30919917090626631837000000*I03*J21-540160769971432320480000000*I06*I18-5509639853708609668896000000*I06*J18-16129800769980270681000000*I09*I15-1792200085553363409000000*I09*J15+138435488761249940420160000*I12^2-23149747284489956592000000*I12*J12+33384936477401025363000000*I15*J09+3709437386377891707000000*J09*J15)*j6
        +211134718240597784634082137000*I03^8*I06+12893268667906961958998202075*I03^7*I09-10932694838002400367438582975*I03^7*J09-13483413285834755260101841632000*I03^6*I06^2+233122862052701064189838570500*I03^6*I12-24231276272984029937751863250*I03^6*J12-10255592932602527927253200603904000*I03^4*I06^3-173640203501144486609232576000*I03^5*I15+669072107485555123580466642000*I03^5*J15-36967007642393976498422892270*I03^4*I09^2+313206474938769912026689897095*I03^4*J09^2-516105118274989413658964214251520000*I03^2*I06^4+45508862843067623940693900000*I03^4*I18-690439496193666454464660690000*I03^4*J18-1024336335553487181114674400000*I03^3*I21+149735862367974095169064500000*I03^3*J21+1048412183046528577788299520000*I03^2*I12^2+39523735613708680530444480000*I03^2*J12^2+6800038130257400742460921188000*I03*I06*J09*J12-35537419109415173349668447304000*I03*I06*I12*J09+11154952729794255069505460904000*I03*I06*I09*J12-27441437065495821681288919632000*I03*I06*I09*I12+5968178337501268382692800000*I15^2+2924241123589243457194513524326400000*I06^5-175677407158448352460800000*I03^10+18775128722038899840320115826800*I03^2*I06*I09*J09-6749167759295575598034624000*I09*J09*J12+550629409781051353334281392000*I09*I12*J09+5225632500843216053478063360000*I06*I12*J12+50689110513675364536226917888000*I06*J09*J15-5238847058043956070519744624000*I06*I15*J09-27184340432373673429024050816000*I06*I09*J15+2298384041595420258884724768000*I06*I09*I15-562849922011278069346794271488000*I06^2*I09*J09-75031004907326028607542720000*I03*J12*J15+16057845091601641481680800000*I03*I15*J12+2232628473537477355797061920000*I03*I12*J15-256043483838247642211273760000*I03*I12*I15+641448381122999307311110650000*I03*J09*J18-62263226557200519898844076000*I03*I18*J09-183217242302991761433933420000*I03*I09*J18+25846874411459850461196792000*I03*I09*I18-359136487933247537390012454900*I03*I09*J09^2+161380367089393960091000264400*I03*I09^2*J09-7147676845714825523324793600000*I03*I06*J21+36452766485364747349010457600000*I03*I06*I21-6573358695091059880520951181600*I03^5*I06*I09-3633516383099420323121921350200*I03^5*I06*J09+38875600851737906865002903784000*I03^4*I06*I12-5341954499687415848048946036000*I03^4*I06*J12+189018098651912375124587631195*I03^4*I09*J09-799878649913842749991222013683200*I03^3*I06^2*I09+885196514165640811659534833913600*I03^3*I06^2*J09+1961361865985582373425651952000*I03^3*I06*I15+27391877405874167551677297216000*I03^3*I06*J15+238471702087478009232727798200*I03^3*I09*I12-28288655236166443755322614300*I03^3*I09*J12+642801165740446971672658053900*I03^3*I12*J09-522810890147887848823623877350*I03^3*J09*J12-926777516142707752775823567360000*I03^2*I06^2*I12+710960629839215987249219255040000*I03^2*I06^2*J12-6161952586255971183495600040800*I03^2*I06*I09^2-27179545453118948795647990093200*I03^2*I06*J09^2+26791390926390864860110600644096000*I03*I06^3*I09+17011496251040522385421945504512000*I03*I06^3*J09-4894536591101631542936172480000*I03^2*I06*I18-3749188733559169231780895040000*I03^2*I06*J18-195738905956731053026706366400*I03^2*I09*I15+177643022731713232632881056800*I03^2*I09*J15-507231749660240411304122880000*I03^2*I12*J12+421842612436404808353058267200*I03^2*I15*J09-397379893602210420550388216400*I03^2*J09*J15-3377857158469472272247592852480000*I03*I06^2*J15-1021742477113276517709600000*I18*J12+77039258680470302244191520000*J12*J18+663130926389029820299200000*I15*J15-1831257095404936004261890560000*I12*J18+72690828124112022947472000000*I12*I18+19815887906694062870628060000*J09*J21+475724287085000694342426720000*I21*J09-81406349995709319069439818000*J09^2*J12-51162719779999533476654352000*I12*J09^2-8745211004677578333078120000*I09*J21-244079775528789898809195840000*I09*I21+16814121227949315107433960000*I09^2*J12-155255688446860502241836256000*I09^2*I12-616869170779121398917849600000*I06*J12^2+57094928578291380196477432320000*I06*I12^2+778197317865242544715229844480000*I06^2*J18+60522419929804109800316236800000*I06^2*I18-59112943681562945534955014784000*I06^2*J09^2+255434463970548782818430633472000*I06^2*I09^2-1631847334232836275725457100800000*I06^3*J12-29240947248316412948436856872960000*I06^3*I12+187131338768647415203599365100*I03*J09^3-21599016662108334463986510000*I03*I09^3)*j3
        +(-1270423528148596039680000*I03^9+896768396465853978357984000*I03^7*I06+80186484717916469814794400*I03^6*I09-55441653450585498680839200*I03^6*J09-261834076899858103532625888000*I03^5*I06^2+1443348087795712866887856000*I03^5*I12-158005441711883075220504000*I03^5*J12-38004285984826804006775479200*I03^4*I06*I09+5952089637234296438145357600*I03^4*I06*J09-6158718709979784157930355712000*I03^3*I06^3-1066169559919318707992832000*I03^4*I15+4325623405248586048622784000*I03^4*J15+294518469380469079318757712000*I03^3*I06*I12-47440977300489363577461288000*I03^3*I06*J12-232561905192916937469691200*I03^3*I09^2+1163938083807072876639638400*I03^3*I09*J09+1112680018163457306365457600*I03^3*J09^2-4328689652839848621394859328000*I03^2*I06^2*I09+2649881039664911112490199616000*I03^2*I06^2*J09+416387075195488963084442542080000*I03*I06^4+323246068478077368919680000*I03^3*I18-4219268547441601012201920000*I03^3*J18-29204083823406555367934784000*I03^2*I06*I15+363555123094436429076738048000*I03^2*I06*J15+1242063668287716191915184000*I03^2*I09*I12-157435239306244607010864000*I03^2*I09*J12+2841349142556431482439376000*I03^2*I12*J09-2284888018349829164382000000*I03^2*J09*J12+6808087782988346463752183040000*I03*I06^2*I12-328184843989100350286643840000*I03*I06^2*J12-34084753424532383557080096000*I03*I06*I09^2+95315862732824868445423728000*I03*I06*I09*J09-66027732583758349943412720000*I03*I06*J09^2-3955165858091963902591733760000*I06^3*I09+476353252673435346704732160000*I06^3*J09-4501491837027241511347200000*I03^2*I21+710147292631279509283200000*I03^2*J21-10585262020789877367703680000*I03*I06*I18-149215408407550123108303680000*I03*I06*J18-1135371267791836700508576000*I03*I09*I15+2254736659119290258486112000*I03*I09*J15+2299365438915080620751040000*I03*I12^2-1367110785466340214236640000*I03*I12*J12+2096652323115973746379872000*I03*I15*J09-3169905679686621240487584000*I03*J09*J15+66447068917193284224960000*I03*J12^2-313292500011944708160407040000*I06^2*I15+1384700021222992405332065280000*I06^2*J15+89623364942487404779027200000*I06*I09*I12+947412155700129897993600000*I06*I09*J12-177627227676781371540226560000*I06*I12*J09+26527149699956430416781120000*I06*J09*J12-139678327040319702835200000*I09^3+770379696060840207175680000*I09^2*J09-1057257490828266058383360000*I09*J09^2+353493612278962940252160000*J09^3+113638230751965721383859200000*I06*I21-9408790882409238224150400000*I06*J21+217575855582036460185600000*I09*I18-1958182700238328141670400000*I09*J18-714408797804604060312000000*I12*I15+1546799950467277330144320000*I12*J15+116396542533934153814400000*I15*J12-304606197814851044259840000*I18*J09+2741455780333659398338560000*J09*J18+12932949170437128201600000*J12*J15)*j6
        +38045551264201172465237721600*I03^2*I09*I18-6195444187869072436808602684800*I03*I09*J09*J12+10526230820053756959518813644800*I03*I09*I12*J09-230987361231678597216993817344000*I03*I06*I12*J12-885801664444936819476746362060800*I03*I06*J09*J15-230550061121214067450627348377600*I03*I06*I15*J09+153836907580582789754269299916800*I03*I06*I09*J15+94269448381824592619604377241600*I03*I06*I09*I15+18593246179750655700253600742707200*I03*I06^2*I09*J09-97633403744457150435922474636800*I03^2*I06*J09*J12-494817539774618656462509660211200*I03^2*I06*I12*J09-43583021367915779518577634201600*I03^2*I06*I09*J12+152782519234122792114080104627200*I03^2*I06*I09*I12+257232286666878624890557518297600*I03^3*I06*I09*J09-467738733514177390399732224000*I12*J09*J12-2656862345503549386922452480000*I09*I12*J12+2296611280623503750050716364800*I09*J09*J15+3406427172386086142814447513600*I09*I15*J09+11870214752431917020530040832000*I06*J12*J15+5081809236360317412291454464000*I06*I15*J12+530684844922993227641477775360000*I06*I12*J15-144027049797524999548416798720000*I06*J09*J18+114256655513640102322953031680000*I06*I18*J09+76937209438962640760161505280000*I06*I09*J18-52858466682826747373064990720000*I06*I09*I18+55805649063559809332036544921600*I06*I09*J09^2-22135025468265377998665620275200*I06*I09^2*J09-1149882384353627166240435591168000*I06^2*J09*J12+19039834725559290304591942139904000*I06^2*I12*J09+206526432343449810674122887168000*I06^2*I09*J12-15086062510102385596566322790400000*I06^2*I09*I12-341645053275628163418147840000*I03*I15*J15+4775665925594482717328607168000*I03*J12*J18+319029446375447257196724096000*I03*I18*J12-2345738862183255551801650176000*I03*I12*J18-913601461451183614935641088000*I03*I12*I18-5672956214212498989198029952000*I03*J09*J21+35750669385989392715054877696000*I03*I21*J09+19830238246159957996875341712000*I03*J09^2*J12-30112423081942262889744738201600*I03*I12*J09^2+1770487607201939238664384704000*I03*I09*J21-12565334865835941345729925632000*I03*I09*I21-36387977458553549635335033600*I03*I09^2*J12+662699630642931599315146905600*I03*I09^2*I12-1066007018406846405285777024000*I03*I06*J12^2+180343358921380724357414952960000*I03*I06*I12^2-3336447147075815772187867650048000*I03*I06^2*J18-637269717501111641195709444096000*I03*I06^2*I18-2147592969590721122607685290086400*I03*I06^2*J09^2-4765907474031054232979208037785600*I03*I06^2*I09^2+106827316446891037845612528119808000*I03*I06^3*J12-405053886973641787313345144365056000*I03*I06^3*I12-4853987838478154199735224409600*I03^2*J12*J15-563452308458132516009708083200*I03^2*I15*J12+2639560084832594485833675264000*I03^2*I12*J15+280911719697710605873915392000*I03^2*I12*I15+20166789268811371909344529420800*I03^2*J09*J18-1619371811372913089090147404800*I03^2*I18*J09-5531521187358000914268709497600*I03^2*I09*J18-2441404762577188442631054705600*I03^2*I09*J09^2+2857118278978319163757467589440*I03^2*I09^2*J09+111635892109598162192811267840000*I03^2*I06*J21-668122062267583389334951434240000*I03^2*I06*I21+25741735350695450463868662734438400*I03^2*I06^2*J15+6175569988392973460141442027724800*I03^2*I06^2*I15+3772429083404433043292665239552000*I03^2*I06^3*J09-415805509537255526772744769156300800*I03^2*I06^3*I09+387294187896545160262141929600*I03^3*I12*J12-21065861055394373667283444216320*I03^3*J09*J15+5585050383402552136101866280960*I03^3*I15*J09+5025757939406204031918096618240*I03^3*I09*J15-496745477563464426998393118720*I03^3*I09*I15-454733981178729616556128266624000*I03^3*I06*J18+48718278668882089626828956928000*I03^3*I06*I18+361127888895699564035018914863360*I03^3*I06*J09^2-74251847709253232502924162320640*I03^3*I06*I09^2-6391756168999395678577922406912000*I03^3*I06^2*J12+21142995004808793251478721111449600*I03^3*I06^2*I12+3040879619600645800298383317600*I03^4*J09*J12-11062421314577456436746755850880*I03^4*I12*J09-183259749790527397107943651200*I03^4*I09*J12+1133258683534858734948065972160*I03^4*I09*I12+398054976554838220616872756915200*I03^4*I06*J15-131494365368251649622843976857600*I03^4*I06*I15-3949630178977392178854911180912640*I03^4*I06^2*J09-2217662797568415946747448636344320*I03^4*I06^2*I09-1150301720827952876846482262064*I03^5*I09*J09-12360730764751980946825075804800*I03^5*I06*J12+59630016501437757102239105836800*I03^5*I06*I12+2480877503977197039227969123520*I03^6*I06*J09+31693247226569748060834795783360*I03^6*I06*I09+960495269630327740825600000*I03^11+343767072240073058843105280000*I15*J18-38196341360008117649233920000*I15*I18+40075554113395816564967040000*J12*J21-248155024771297186382085120000*I21*J12+1744375467262614199005081600000*I12*J21-8526721738563993917449728000000*I12*I21-834369799965690699258079680000*J09*J12^2+4322880514110635394406520832000*I12^2*J09-6089901519900533248341833932800*J09^2*J15-3508386182757258858762306969600*I15*J09^2+280865730833923117060024704000*I09*J12^2+2090203464976101520301850624000*I09*I12^2+84454249741854026356443340800*I09^2*J15-838849154290397729266391654400*I09^2*I15-22538748993531306991271637811200*I06*J09^3+1357446630541974599358163353600*I06*I09^3+165968199738283073353320591360000*I06^2*J21-4985544648143541521126438830080000*I06^2*I21-928737388213429569475539695173632000*I06^4*J09-233046222755870616479446708518912000*I06^3*J15+3348807187366300189060387454976000*I06^3*I15+2313003262153194079330533927026688000*I06^4*I09-19098170680004058824616960000*I03*I15^2-44446500077403089618109864885878784000*I03*I06^5-11388621937192942063908212726400*I03^2*J09^3-280394685762359140230621828480*I03^2*I09^3+22562173251315579680769585600*I03^3*J12^2-810040088445914045908371456000*I03^3*I12^2+1332215006423940623966209935320678400*I03^3*I06^4-539962100822331560764278720000*I03^4*J21+4010877598819875153154767360000*I03^4*I21-130109735808010129030655040000*I03^5*I18+1830566716907337581262703200000*I03^5*J18-864763776673838787607503299424*I03^5*J09^2+42560049866804874800230981889433600*I03^5*I06^3+200096697730115575476560566224*I03^5*I09^2+297954097182743991516639209664000*I03^7*I06^2-1669642291256644859992395667200*I03^6*J15+522824415531695995218168729600*I03^6*I15+46780162752589867268985967200*I03^7*J12-632434120030104039838105732800*I03^7*I12+34788781541219150470345454160*I03^8*J09-31490837624119516854185247120*I03^8*I09-352228684636591516005722467200*I03^9*I06

        ];
    SYSj6j3_deg := [ [33, 30], [33, 30], [33, 30], [33, 30] ];

    for i := 1 to #SYSj6 do
        if p gt 0 and Min(MinimizedValuationsModp(
            DO cat [MonomialCoefficient(SYSj6[i], j6^k) : k in [0, 1]],
            WG cat SYSj6_deg[i], p)[14..15]) gt 0 then
            continue;
        end if;
        if Degree(SYSj6[i], j6) eq 1 then
            _j6 := -MonomialCoefficient(SYSj6[i], 1)/MonomialCoefficient(SYSj6[i], j6);
            break;
        end if;
    end for;
    if not assigned(_j6) then
        // "Hum hum, Groebner approach (j6 case)...";
        return NodeDihedInvsFromDOByGroebner(DO: p := p);
    end if;
   assert p eq 0 or Valuation(_j6, p) ge 0;

   for i := 1 to #SYSj6j3 do
       E := Evaluate(SYSj6j3[i], j6, _j6);
       if p gt 0 and Min(MinimizedValuationsModp(
           DO cat [ MonomialCoefficient(E, j3^k) : k in [0, 1] ],
           WG cat SYSj6j3_deg[i], p)[14..15]) gt 0 then
           continue;
       end if;
       if Degree(E, j3) eq 1 then
           _j3 := -MonomialCoefficient(E, 1)/MonomialCoefficient(E, j3);
           break;
       end if;
   end for;
   if not assigned(_j3) then
       // "Hum hum, Groebner approach (j3 case)...";
       return NodeDihedInvsFromDOByGroebner(DO: p := p);
   end if;
   assert p eq 0 or Valuation(_j3, p) ge 0;

   j3 := _j3;
   j6 := _j6;

   j15 := 1719926784/125*I15-6771/700*j3^3*j6+42/125*j3*j6^2+10098432/175*j3^2*I09-1876608/175*j3^2*J09-76896/35*j3^4*I03+928908/35*j3^3*I03^2-62208/7*j3^3*I06-132049728/875*j3^2*I03^3-2322432/625*j6*I09+1161216/625*j6*J09+175104/175*j6*I03^3-11878244352/6125*j3*I12-259780608/1225*j3*J12+3726508032/35*j3*I06^2+377413632/875*j3*I03^4+47279407104/30625*I03^2*I09-15338668032/30625*I03^2*J09-9937354752/125*I06*I09+4968677376/125*I06*J09+6412566528/175*I06*I03^3-40418279424/6125*I03*I12+5876416512/6125*I03*J12-55037657088/875*I03*I06^2-3981312/875*I03*j6*I06+73903104/35*j3^2*I03*I06-779712/875*j6*j3*I03^2+20256/125*j6*j3^2*I03-4534272/875*j6*j3*I06-3106584576/6125*j3*I03*I09+1068816384/6125*j3*I03*J09-2882469888/175*j3*I03^2*I06+56295/896*j3^5-431161344/875*I03^5;
   j12 := -573308928/49*I12+89579520/49*J12-1395/56*j3^2*j6-45225/7*j3^3*I03+563760/7*j3^2*I03^2-2985984/7*j3*I03^3-6912/7*j6*I03^2+3304800/7*j3^2*I06+147308544/7*I03^2*I06-124416/7*j6*I06+622080/7*j3*I09+622080/7*j3*J09-94556160/49*I03*I09+54743040/49*I03*J09-716636160/7*I06^2+320625/1792*j3^4+1/3*j6^2+5750784/7*I03^4+2448/7*j3*j6*I03-12441600*j3*I03*I06;
   k12 := 107495424/245*I12-71663616/245*J12+9/7*j3^2*j6+7992/7*j3^3*I03-89748/7*j3^2*I03^2+405504/7*j3*I03^3+192/7*j6*I03^2-2161728/7*j3^2*I06-123420672/35*I03^2*I06+27648/7*j6*I06-1078272/35*j3*I09+2405376/35*j3*J09+248168448/1225*I03*I09-153944064/1225*I03*J09+573308928/35*I06^2-3915/112*j3^4-589824/7*I03^4-96/7*j3*j6*I03+1990656*j3*I03*I06;
   j9 := -55296/5*I09+27648/5*J09+j3*j6+126*j3^2*I03-1152*j3*I03^2+20736*j3*I06-45/16*j3^3+3072*I03^3;
   k9 := -62208*I09+124416*J09+3/4*j3*j6+6075/4*j3^2*I03-12960*j3*I03^2-388800*j3*I06-3375/64*j3^3+34560*I03^3+12*j6*I03+248832*I03*I06;
   k6:= 9/4*j3^2-36*j3*I03+144*I03^2+20736*I06;
   k3 := 72*I03-9/2*j3;

   return [[j3, k3, j6, k6, j9, k9, j12, k12, j15]], [ w div 3 : w in [3, 3, 6, 6, 9, 9, 12, 12, 15]];

end function;

/* Retreive Dixmier-Ohno invariants from so-called Node Dihedral Invariants
   (the easy way)  */
function DOFromNodeDihedInvs(DH)

    j3, k3, j6, k6, j9, k9, j12, k12, j15 := Explode(DH);

    I03 := 1/16*j3 + 1/72*k3;

    I06 := -1/36864*j3^2 + 1/82944*j3*k3 - 1/746496*k3^2 + 1/20736*k6;

    I09 := 1/27648*j3^3 + 31/497664*j3^2*k3 - 29/2239488*j3*k3^2 + 7/13436928*k3^3 +
        7/62208*j3*j6 - 1/1119744*k3*j6 + 1/4608*j3*k6 - 1/1119744*k3*k6 - 5/41472*j9 +
        1/186624*k9;

    J09 := -7/110592*j3^3 + 17/497664*j3^2*k3 - 7/8957952*j3*k3^2 - 1/2239488*k3^3 +
        11/248832*j3*j6 - 1/559872*k3*j6 + 7/27648*j3*k6 - 1/559872*k3*k6 - 5/82944*j9 +
        1/93312*k9;

    I12 := -1/1327104*j3^4 - 7/11943936*j3^3*k3 + 11/47775744*j3^2*k3^2 -
        19/967458816*j3*k3^3 + 17/34828517376*k3^4 + 5/11943936*j3^2*j6 +
        1/13436928*j3*k3*j6 - 1/53747712*k3^2*j6 + 1/26873856*j6^2 + 23/5971968*j3^2*k6
        - 7/35831808*j3*k3*k6 - 1/967458816*k3^2*k6 + 1/26873856*j6*k6 - 5/2985984*j3*j9
        + 5/53747712*k3*j9 + 5/8957952*j3*k9 - 1/8957952*j12 - 25/35831808*k12;

    J12 := -5/5308416*j3^4 - 1/1492992*j3^3*k3 + 565/859963392*j3^2*k3^2 -
        253/3869835264*j3*k3^3 + 7/7739670528*k3^4 + 103/23887872*j3^2*j6 +
        31/107495424*j3*k3*j6 - 25/967458816*k3^2*j6 + 1/17915904*j6^2 +
        97/7962624*j3^2*k6 + 385/107495424*j3*k3*k6 - 115/967458816*k3^2*k6 +
        19/26873856*j6*k6 + 7/53747712*k6^2 - 181/23887872*j3*j9 - 71/107495424*k3*j9 +
        49/17915904*j3*k9 - 1/80621568*k3*k9 - 1/5971968*j12 - 5/1119744*k12;

    I15 := -1/509607936*j3^5 - 95/9172942848*j3^4*k3 - 251/20639121408*j3^3*k3^2 +
        1463/371504185344*j3^2*k3^3 - 1225/3343537668096*j3*k3^4 +
        625/60183678025728*k3^5 + 67/1146617856*j3^3*j6 + 25/3439853568*j3^2*k3*j6 -
        5/30958682112*j3*k3^2*j6 - 77/835884417024*k3^3*j6 + 1/143327232*j3*j6^2 +
        1/5159780352*k3*j6^2 + 41/382205952*j3^3*k6 + 503/10319560704*j3^2*k3*k6 -
        551/92876046336*j3*k3^2*k6 - 25/835884417024*k3^3*k6 + 107/1289945088*j3*j6*k6 -
        5/23219011584*k3*j6*k6 + 1/107495424*j3*k6^2 + 1/46438023168*k3*k6^2 -
        95/1146617856*j3^2*j9 - 85/2579890176*j3*k3*j9 + 385/92876046336*k3^2*j9 -
        7/286654464*j6*j9 - 65/2579890176*k6*j9 + 197/1719926784*j3^2*k9 +
        11/7739670528*j3*k3*k9 - 1/34828517376*k3^2*k9 - 1/47775744*j3*j12 -
        1/1719926784*k3*j12 - 145/859963392*j3*k12 - 5/15479341056*k3*k12 +
        125/1719926784*j15;

    J15 := 1/113246208*j3^5 - 5/339738624*j3^4*k3 + 41/4586471424*j3^3*k3^2 -
        11/4586471424*j3^2*k3^3 + 205/743008370688*j3*k3^4 - 25/2229025112064*k3^5 -
        1/47775744*j3^3*j6 + 5/382205952*j3^2*k3*j6 - 35/15479341056*j3*k3^2*j6 +
        11/92876046336*k3^3*j6 + 1/1719926784*j3*j6^2 - 1/15479341056*k3*j6^2 -
        1/11943936*j3^3*k6 + 71/1146617856*j3^2*k3*k6 - 143/15479341056*j3*k3^2*k6 +
        35/92876046336*k3^3*k6 + 29/859963392*j3*j6*k6 + 25/7739670528*k3*j6*k6 +
        133/1719926784*j3*k6^2 - 49/15479341056*k3*k6^2 + 5/382205952*j3^2*j9 -
        5/573308928*j3*k3*j9 + 25/30958682112*k3^2*j9 - 1/286654464*j6*j9 -
        5/95551488*k6*j9 + 1/286654464*j3^2*k9 + 11/2579890176*j3*k3*k9 -
        1/1934917632*k3^2*k9 - 1/573308928*j3*j12 + 1/5159780352*k3*j12 -
        25/573308928*j3*k12 + 25/5159780352*k3*k12;

    I18 := 5/12230590464*j3^6 + 19/12230590464*j3^5*k3 +
        3805/3962711310336*j3^4*k3^2 - 2357/4458050224128*j3^3*k3^3 +
        4159/53496602689536*j3^2*k3^4 - 3233/722204136308736*j3*k3^5 +
        775/8666449635704832*k3^6 - 145/110075314176*j3^4*j6 +
        511/247669456896*j3^3*k3*j6 - 47/92876046336*j3^2*k3^2*j6 +
        833/20061226008576*j3*k3^3*j6 - 947/722204136308736*k3^4*j6 +
        283/123834728448*j3^2*j6^2 - 11/139314069504*j3*k3*j6^2 +
        167/20061226008576*k3^2*j6^2 - 1/61917364224*j6^3 - 115/27518828544*j3^4*k6 +
        319/165112971264*j3^3*k3*k6 - 583/4458050224128*j3^2*k3^2*k6 +
        299/40122452017152*j3*k3^3*k6 - 109/361102068154368*k3^4*k6 +
        1783/123834728448*j3^2*j6*k6 - 239/1114512556032*j3*k3*j6*k6 +
        1/417942208512*k3^2*j6*k6 + 5/278628139008*j6^2*k6 + 605/61917364224*j3^2*k6^2 +
        5/371504185344*j3*k3*k6^2 + 5/20061226008576*k3^2*k6^2 - 1/557256278016*j6*k6^2
        + 85/27518828544*j3^3*j9 - 175/165112971264*j3^2*k3*j9 +
        5/82556485632*j3*k3^2*j9 - 25/40122452017152*k3^3*j9 - 119/20639121408*j3*j6*j9
        - 1/371504185344*k3*j6*j9 - 895/61917364224*j3*k6*j9 +
        145/1114512556032*k3*k6*j9 + 275/82556485632*j9^2 + 719/82556485632*j3^3*k9 +
        91/92876046336*j3^2*k3*k9 - 1373/6687075336192*j3*k3^2*k9 +
        1/940369969152*k3^3*k9 + 17/20639121408*j3*j6*k9 + 163/185752092672*j3*k6*k9 -
        1/417942208512*k3*k6*k9 - 5/5159780352*j9*k9 - 143/82556485632*j3^2*j12 -
        23/92876046336*j3*k3*j12 + 319/6687075336192*k3^2*j12 - 1/6879707136*j6*j12 +
        125/185752092672*k6*j12 - 635/41278242816*j3^2*k12 - 95/185752092672*j3*k3*k12 +
        1145/6687075336192*k3^2*k12 - 25/92876046336*k6*k12 + 125/13759414272*j3*j15 -
        125/247669456896*k3*j15;

    J18 := 5/4076863488*j3^6 - 7/6115295232*j3^5*k3 + 175/1320903770112*j3^4*k3^2 +
        383/2972033482752*j3^3*k3^3 - 703/17832200896512*j3^2*k3^4 +
        901/240734712102912*j3*k3^5 - 35/320979616137216*k3^6 - 265/110075314176*j3^4*j6
        + 17/20639121408*j3^3*k3*j6 + 1/46438023168*j3^2*k3^2*j6 -
        523/20061226008576*j3*k3^3*j6 + 439/240734712102912*k3^4*j6 +
        47/123834728448*j3^2*j6^2 - 1/34828517376*j3*k3*j6^2 -
        17/20061226008576*k3^2*j6^2 - 1/557256278016*j6^3 - 575/55037657088*j3^4*k6 +
        247/55037657088*j3^3*k3*k6 - 79/247669456896*j3^2*k3^2*k6 -
        749/40122452017152*j3*k3^3*k6 + 233/120367356051456*k3^4*k6 +
        401/61917364224*j3^2*j6*k6 - 37/371504185344*j3*k3*j6*k6 -
        1/2507653251072*k3^2*j6*k6 + 25/278628139008*j6^2*k6 +
        2095/123834728448*j3^2*k6^2 - 275/371504185344*j3*k3*k6^2 -
        35/20061226008576*k3^2*k6^2 - 49/557256278016*j6*k6^2 + 35/13759414272*j3^3*j9 -
        235/165112971264*j3^2*k3*j9 + 55/247669456896*j3*k3^2*j9 -
        505/40122452017152*k3^3*j9 - 31/20639121408*j3*j6*j9 + 31/371504185344*k3*j6*j9
        - 655/61917364224*j3*k6*j9 + 205/1114512556032*k3*k6*j9 + 25/27518828544*j9^2 -
        19/82556485632*j3^3*k9 + 59/92876046336*j3^2*k3*k9 -
        277/6687075336192*j3*k3^2*k9 - 1/156728328192*k3^3*k9 + 19/61917364224*j3*j6*k9
        + 307/185752092672*j3*k6*k9 + 1/69657034752*k3*k6*k9 - 5/10319560704*j9*k9 -
        7/82556485632*j3^2*j12 - 7/92876046336*j3*k3*j12 + 71/6687075336192*k3^2*j12 -
        1/61917364224*j6*j12 - 5/185752092672*k6*j12 - 175/82556485632*j3^2*k12 -
        125/185752092672*j3*k3*k12 + 875/6687075336192*k3^2*k12 - 25/23219011584*k6*k12;

    I21 := 1/97844723712*j3^7 - 7/587068342272*j3^6*k3 +
        409/126806761930752*j3^5*k3^2 + 11/17832200896512*j3^4*k3^3 -
        1343/5135673858195456*j3^3*k3^4 - 37/23110532361879552*j3^2*k3^5 +
        103/277326388342554624*j3*k3^6 - 1/207994791256915968*k3^7 -
        185/3522410053632*j3^5*j6 + 509/23776267862016*j3^4*k3*j6 +
        7/2641807540224*j3^3*k3^2*j6 - 1091/1925877696823296*j3^2*k3^3*j6 +
        125/23110532361879552*j3*k3^4*j6 + 13/17332899271409664*k3^5*j6 +
        155/11888133931008*j3^3*j6^2 + 11/8916100448256*j3^2*k3*j6^2 -
        67/213986410758144*j3*k3^2*j6^2 + 13/1444408272617472*k3^3*j6^2 +
        5/53496602689536*j3*j6^3 - 1/120367356051456*k3*j6^3 - 179/1174136684544*j3^5*k6
        + 1247/23776267862016*j3^4*k3*k6 + 7/2641807540224*j3^3*k3^2*k6 +
        1723/481469424205824*j3^2*k3^3*k6 - 1543/23110532361879552*j3*k3^4*k6 +
        1/17332899271409664*k3^5*k6 + 1163/2972033482752*j3^3*j6*k6 +
        6439/53496602689536*j3^2*k3*j6*k6 - 8521/962938848411648*j3*k3^2*j6*k6 +
        11/80244904034304*k3^3*j6*k6 + 119/53496602689536*j3*j6^2*k6 -
        11/120367356051456*k3*j6^2*k6 + 631/1320903770112*j3^3*k6^2 +
        2351/53496602689536*j3^2*k3*k6^2 + 2191/641959232274432*j3*k3^2*k6^2 +
        133/1444408272617472*k3^3*k6^2 + 3515/53496602689536*j3*j6*k6^2 -
        23/120367356051456*k3*j6*k6^2 - 637/17832200896512*j3*k6^3 -
        637/120367356051456*k3*k6^3 + 233/3522410053632*j3^4*j9 -
        127/11888133931008*j3^3*k3*j9 - 713/71328803586048*j3^2*k3^2*j9 +
        155/1925877696823296*j3*k3^3*j9 + 491/23110532361879552*k3^4*j9 -
        151/1486016741376*j3^2*j6*j9 - 1/417942208512*j3*k3*j6*j9 +
        445/962938848411648*k3^2*j6*j9 - 1/1981355655168*j6^2*j9 -
        379/990677827584*j3^2*k6*j9 - 5485/53496602689536*j3*k3*k6*j9 -
        917/962938848411648*k3^2*k6*j9 + 107/8916100448256*j6*k6*j9 +
        49/5944066965504*k6^2*j9 + 125/2641807540224*j3*j9^2 +
        125/35664401793024*k3*j9^2 + 37/2641807540224*j3^4*k9 +
        839/17832200896512*j3^3*k3*k9 + 709/641959232274432*j3^2*k3^2*k9 -
        161/962938848411648*j3*k3^3*k9 - 7/2888816545234944*k3^4*k9 +
        167/17832200896512*j3^2*j6*k9 + 127/80244904034304*j3*k3*j6*k9 -
        11/120367356051456*k3^2*j6*k9 + 1/20061226008576*j6^2*k9 +
        1771/80244904034304*j3*k3*k6*k9 - 59/120367356051456*k3^2*k6*k9 -
        1/10030613004288*j6*k6*k9 + 49/20061226008576*k6^2*k9 -
        413/5944066965504*j3*j9*k9 - 7/8916100448256*k3*j9*k9 + 1/835884417024*j3*k9^2 +
        1/5015306502144*k3*k9^2 - 5/293534171136*j3^3*j12 -
        41/35664401793024*j3^2*k3*j12 + 49/641959232274432*j3*k3^2*j12 +
        1/481469424205824*k3^3*j12 - 17/17832200896512*j3*j6*j12 +
        1/40122452017152*k3*j6*j12 + 899/17832200896512*j3*k6*j12 -
        7/6687075336192*k3*k6*j12 + 5/5944066965504*j9*j12 - 1/6687075336192*k9*j12 -
        53/2641807540224*j3^3*k12 - 2021/35664401793024*j3^2*k3*k12 -
        3773/160489808068608*j3*k3^2*k12 + 451/481469424205824*k3^3*k12 -
        17/185752092672*j3*k6*k12 - 1391/40122452017152*k3*k6*k12 +
        3145/17832200896512*j9*k12 - 91/6687075336192*k9*k12 + 5/293534171136*j3^2*j15 +
        65/1981355655168*j3*k3*j15 + 845/53496602689536*k3^2*j15 -
        2875/17832200896512*j6*j15;

    J21 := -65/1565515579392*j3^7 + 4283/28179280429056*j3^6*k3 -
        2153/14089640214528*j3^5*k3^2 + 70597/1141260857376768*j3^4*k3^3 -
        104669/10271347716390912*j3^3*k3^4 + 36665/61628086298345472*j3^2*k3^5 -
        2725/92442129447518208*j3*k3^6 + 1/2567836929097728*k3^7 -
        251/587068342272*j3^5*j6 + 1385/10567230160896*j3^4*k3*j6 +
        3581/95105071448064*j3^3*k3^2*j6 - 4153/855945643032576*j3^2*k3^3*j6 +
        25/2567836929097728*j3*k3^4*j6 + 13/11555266180939776*k3^5*j6 +
        175/495338913792*j3^3*j6^2 - 6485/142657607172096*j3^2*k3*j6^2 +
        2281/641959232274432*j3*k3^2*j6^2 - 11/120367356051456*k3^3*j6^2 -
        5/17832200896512*j3*j6^3 + 1/80244904034304*k3*j6^3 - 55/880602513408*j3^5*k6 -
        40927/31701690482688*j3^4*k3*k6 + 177607/285315214344192*j3^3*k3^2*k6 +
        36085/2567836929097728*j3^2*k3^3*k6 - 40631/7703510787293184*j3*k3^4*k6 -
        133/5777633090469888*k3^5*k6 + 15757/3962711310336*j3^3*j6*k6 +
        105613/71328803586048*j3^2*k3*j6*k6 - 22289/320979616137216*j3*k3^2*j6*k6 -
        85/160489808068608*k3^3*j6*k6 + 785/5944066965504*j3*j6^2*k6 -
        5/1253826625536*k3*j6^2*k6 + 6079/3962711310336*j3^3*k6^2 +
        150169/47552535724032*j3^2*k3*k6^2 + 60353/641959232274432*j3*k3^2*k6^2 -
        1147/481469424205824*k3^3*k6^2 + 2681/1981355655168*j3*j6*k6^2 -
        2251/80244904034304*k3*j6*k6^2 + 5425/17832200896512*j3*k6^3 -
        35/4458050224128*k3*k6^3 + 1855/3522410053632*j3^4*j9 +
        25/440301256704*j3^3*k3*j9 - 1603/10567230160896*j3^2*k3^2*j9 +
        83/20061226008576*j3*k3^3*j9 + 2291/3851755393646592*k3^4*j9 -
        12469/7925422620672*j3^2*j6*j9 + 127/4458050224128*j3*k3*j6*j9 -
        61/40122452017152*k3^2*j6*j9 - 23/2972033482752*j6^2*j9 -
        31699/7925422620672*j3^2*k6*j9 - 7783/4458050224128*j3*k3*k6*j9 -
        1151/53496602689536*k3^2*k6*j9 + 23/2229025112064*j6*k6*j9 -
        167/990677827584*k6^2*j9 + 1085/1320903770112*j3*j9^2 +
        125/1981355655168*k3*j9^2 + 299/1761205026816*j3^4*k9 +
        539/880602513408*j3^3*k3*k9 - 187/17832200896512*j3^2*k3^2*k9 -
        289/160489808068608*j3*k3^3*k9 + 5/240734712102912*k3^4*k9 +
        575/1486016741376*j3^2*j6*k9 - 13/557256278016*j3*k3*j6*k9 +
        7/7522959753216*k3^2*j6*k9 + 2191/13374150672384*j3*k3*k6*k9 +
        43/20061226008576*k3^2*k6*k9 + 1/46438023168*j6*k6*k9 + 5/104485552128*k6^2*k9 -
        3053/1981355655168*j3*j9*k9 + 247/8916100448256*k3*j9*k9 +
        29/557256278016*j3*k9^2 - 7/2507653251072*k3*k9^2 - 95/440301256704*j3^3*j12 -
        767/47552535724032*j3^2*k3*j12 + 217/213986410758144*j3*k3^2*j12 -
        7/481469424205824*k3^3*j12 - 29/1981355655168*j3*j6*j12 +
        1/8916100448256*k3*j6*j12 + 65/61917364224*j3*k6*j12 -
        625/26748301344768*k3*k6*j12 + 7/990677827584*j9*j12 - 79/2641807540224*j3^3*k12
        - 44371/47552535724032*j3^2*k3*k12 - 41869/213986410758144*j3*k3^2*k12 +
        2561/160489808068608*k3^3*k12 - 19415/5944066965504*j3*k6*k12 -
        545/1486016741376*k3*k6*k12 + 9431/2972033482752*j9*k12 - 13/61917364224*k9*k12
        + 185/587068342272*j3^2*j15 + 395/990677827584*j3*k3*j15 +
        3905/35664401793024*k3^2*j15 - 6731/2972033482752*j6*j15 -
        25/330225942528*k6*j15;

    I27 := 0;

    return
        [I03, I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27],
        [ 1, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 9 ];

end function;

/* Retreive Igusa invariants of the genus 2 component of the reduced quartic
   from so-called Node Dihedral Invariants
*/

function IgusaFromNodeDihedInvs(DH)

    j3, k3, j6, k6, j9, k9, j12, k12, j15 := Explode(DH);

    i2 := -27*j3^2-12*j3*k3+12*k3^2-32*j6+80*k6;

    i4 := 81*j3^3*k3-75*j3^2*k3^2-12*j3*k3^3+6*k3^4+156*j3^2*j6-114*j3^2*k6+32*j3*j6*k3+16*j3*k3*k6-32*j6*k3^2-16*k3^2*k6+60*j3*j9-16*j3*k9+32*j6^2-224*j6*k6-120*j9*k3+32*k3*k9+480*k6^2+32*j12+200*k12;

    i6 := 81*j3^4*k3^2-166*j3^3*k3^3+93*j3^2*k3^4-12*j3*k3^5+4*k3^6-324*j3^4*j6-324*j3^4*k6+408*j3^3*j6*k3+1164*j3^3*k3*k6-440*j3^2*j6*k3^2-1276*j3^2*k3^2*k6+64*j3*j6*k3^3+224*j3*k3^3*k6-32*j6*k3^4-112*k3^4*k6+324*j3^3*j9-336*j3^3*k9+272*j3^2*j6^2-2320*j3^2*j6*k6-624*j3^2*j9*k3+704*j3^2*k3*k9-384*j3^2*k6^2-64*j3*j6^2*k3-448*j3*j6*k3*k6-72*j3*j9*k3^2-96*j3*k3^2*k9-704*j3*k3*k6^2+64*j6^2*k3^2+448*j6*k3^2*k6+48*j9*k3^3+64*k3^3*k9+704*k3^2*k6^2+256*j12*j3^2-420*j3^2*k12+96*j3*j6*j9+128*j3*j6*k9+320*j3*j9*k6+80*j3*k12*k3+448*j3*k6*k9-192*j6*j9*k3-256*j6*k3*k9+256*j6*k6^2-640*j9*k3*k6-80*k12*k3^2-896*k3*k6*k9-1280*k6^3+384*j12*k6+500*j15*j3-1000*j15*k3+640*j6*k12+400*j9^2-1600*k12*k6+256*k9^2;

    i8 := (i2*i6-i4^2) / 4;

    i10 := 3125*j15^2 - 6912*k12*k9^2 - 1024*j12*j9^2 + 36000*j15*k9*k6 + 10000*j15*j9*k6 -
        6912*k9^2*k6^2 - 36800*j9^2*k6^2 + 102400*k12*k6^3 + 2304*j12*k6^3 +
        65536*k6^5 - 14400*j15*k9*j6 - 8000*j15*j9*j6 + 16960*j9^2*k6*j6 -
        65280*k12*k6^2*j6 - 2304*j12*k6^2*j6 - 49152*k6^4*j6 - 2048*j9^2*j6^2 +
        12288*k12*k6*j6^2 + 12288*k6^3*j6^2 - 1024*k12*j6^3 - 1024*k6^2*j6^3 +
        15000*j15*k12*k3 + 6400*j9^3*k3 + 40320*k12*k9*k6*k3 - 3072*j12*j9*k6*k3 +
        32000*j15*k6^2*k3 + 36864*k9*k6^3*k3 - 10240*j9*k6^3*k3 + 4608*k12*k9*j6*k3
        - 32800*j15*k6*j6*k3 + 4608*k9*k6^2*j6*k3 + 7424*j9*k6^2*j6*k3 +
        8960*j15*j6^2*k3 + 512*j9*k6*j6^2*k3 + 13200*j15*k9*k3^2 - 9000*j15*j9*k3^2
        + 3120*j9^2*k6*k3^2 - 35840*k12*k6^2*k3^2 + 384*j12*k6^2*k3^2 -
        32768*k6^4*k3^2 + 2304*j9^2*j6*k3^2 - 22784*k12*k6*j6*k3^2 -
        20480*k6^3*j6*k3^2 + 256*k12*j6^2*k3^2 + 256*k6^2*j6^2*k3^2 -
        1024*k12*k9*k3^3 - 14400*j15*k6*k3^3 - 1024*k9*k6^2*k3^3 - 1536*j9*k6^2*k3^3
        - 10080*j15*j6*k3^3 - 128*j9*k6*j6*k3^3 - 432*j9^2*k3^4 + 4608*k12*k6*k3^4 +
        4096*k6^3*k3^4 + 1728*j15*k3^5 - 7500*j15*k12*j3 - 3200*j9^3*j3 -
        20160*k12*k9*k6*j3 + 1536*j12*j9*k6*j3 - 16000*j15*k6^2*j3 -
        18432*k9*k6^3*j3 + 5120*j9*k6^3*j3 - 2304*k12*k9*j6*j3 + 16400*j15*k6*j6*j3
        - 2304*k9*k6^2*j6*j3 - 3712*j9*k6^2*j6*j3 - 4480*j15*j6^2*j3 -
        256*j9*k6*j6^2*j3 - 13200*j15*k9*k3*j3 + 9000*j15*j9*k3*j3 -
        3120*j9^2*k6*k3*j3 + 35840*k12*k6^2*k3*j3 - 384*j12*k6^2*k3*j3 +
        32768*k6^4*k3*j3 - 2304*j9^2*j6*k3*j3 + 22784*k12*k6*j6*k3*j3 +
        20480*k6^3*j6*k3*j3 - 256*k12*j6^2*k3*j3 - 256*k6^2*j6^2*k3*j3 +
        1536*k12*k9*k3^2*j3 + 21600*j15*k6*k3^2*j3 + 1536*k9*k6^2*k3^2*j3 +
        2304*j9*k6^2*k3^2*j3 + 15120*j15*j6*k3^2*j3 + 192*j9*k6*j6*k3^2*j3 +
        864*j9^2*k3^3*j3 - 9216*k12*k6*k3^3*j3 - 8192*k6^3*k3^3*j3 -
        4320*j15*k3^4*j3 - 1024*j12^2*j3^2 + 4800*j15*k9*j3^2 + 3375*j15*j9*j3^2 +
        2304*k9^2*k6*j3^2 + 14880*j9^2*k6*j3^2 - 12160*k12*k6^2*j3^2 -
        896*j12*k6^2*j3^2 - 3072*k6^4*j3^2 - 9216*k9^2*j6*j3^2 - 9984*j9^2*j6*j3^2 +
        54464*k12*k6*j6*j3^2 + 4608*j12*k6*j6*j3^2 + 224768*k6^3*j6*j3^2 -
        18176*k12*j6^2*j3^2 - 2048*j12*j6^2*j3^2 - 125312*k6^2*j6^2*j3^2 +
        20992*k6*j6^3*j3^2 - 1024*j6^4*j3^2 - 288*k12*k9*k3*j3^2 -
        3072*j12*k9*k3*j3^2 + 6912*j12*j9*k3*j3^2 - 8550*j15*k6*k3*j3^2 -
        11680*k9*k6^2*k3*j3^2 + 33168*j9*k6^2*k3*j3^2 + 12240*j15*j6*k3*j3^2 +
        55424*k9*k6*j6*k3*j3^2 - 60384*j9*k6*j6*k3*j3^2 + 5120*k9*j6^2*k3*j3^2 +
        13056*j9*j6^2*k3*j3^2 + 384*k9^2*k3^2*j3^2 - 10368*j9^2*k3^2*j3^2 +
        7992*k12*k6*k3^2*j3^2 + 17856*j12*k6*k3^2*j3^2 + 2816*k6^3*k3^2*j3^2 +
        18144*k12*j6*k3^2*j3^2 + 2304*j12*j6*k3^2*j3^2 - 44832*k6^2*j6*k3^2*j3^2 -
        30720*k6*j6^2*k3^2*j3^2 + 256*j6^3*k3^2*j3^2 + 2970*j15*k3^3*j3^2 -
        1728*k9*k6*k3^3*j3^2 - 15768*j9*k6*k3^3*j3^2 - 1152*k9*j6*k3^3*j3^2 -
        11232*j9*j6*k3^3*j3^2 - 648*k12*k3^4*j3^2 - 432*j12*k3^4*j3^2 +
        6048*k6*j6*k3^4*j3^2 + 1944*j9*k3^5*j3^2 - 112*k12*k9*j3^3 +
        1536*j12*k9*j3^3 - 3456*j12*j9*j3^3 + 675*j15*k6*j3^3 + 5584*k9*k6^2*j3^3 -
        16968*j9*k6^2*j3^3 - 8640*j15*j6*j3^3 - 27712*k9*k6*j6*j3^3 +
        30160*j9*k6*j6*j3^3 - 2560*k9*j6^2*j3^3 - 6528*j9*j6^2*j3^3 -
        384*k9^2*k3*j3^3 + 9936*j9^2*k3*j3^3 - 3384*k12*k6*k3*j3^3 -
        17856*j12*k6*k3*j3^3 + 1280*k6^3*k3*j3^3 - 18144*k12*j6*k3*j3^3 -
        2304*j12*j6*k3*j3^3 + 44832*k6^2*j6*k3*j3^3 + 30720*k6*j6^2*k3*j3^3 -
        256*j6^3*k3*j3^3 - 135*j15*k3^2*j3^3 + 2592*k9*k6*k3^2*j3^3 +
        23652*j9*k6*k3^2*j3^3 + 1728*k9*j6*k3^2*j3^3 + 16848*j9*j6*k3^2*j3^3 +
        1296*k12*k3^3*j3^3 + 864*j12*k3^3*j3^3 - 12096*k6*j6*k3^3*j3^3 -
        4860*j9*k3^4*j3^3 - 96*k9^2*j3^4 + 243*j9^2*j3^4 - 4617*k12*k6*j3^4 +
        9936*j12*k6*j3^4 - 6416*k6^3*j3^4 + 6156*k12*j6*j3^4 - 1728*j12*j6*j3^4 -
        30660*k6^2*j6*j3^4 + 29088*k6*j6^2*j3^4 - 2240*j6^3*j3^4 + 1215*j15*k3*j3^4
        + 15336*k9*k6*k3*j3^4 - 3996*j9*k6*k3*j3^4 - 13536*k9*j6*k3*j3^4 -
        7560*j9*j6*k3*j3^4 + 5913*k12*k3^2*j3^4 + 1512*j12*k3^2*j3^4 +
        15417*k6^2*k3^2*j3^4 + 5616*k6*j6*k3^2*j3^4 + 8208*j6^2*k3^2*j3^4 +
        5832*k9*k3^3*j3^4 - 486*j9*k3^3*j3^4 - 6318*k6*k3^4*j3^4 - 4860*j6*k3^4*j3^4
        + 729*k3^6*j3^4 - 729*j15*j3^5 - 8100*k9*k6*j3^5 - 1944*j9*k6*j3^5 +
        6480*k9*j6*j3^5 + 972*j9*j6*j3^5 - 6561*k12*k3*j3^5 - 1944*j12*k3*j3^5 -
        15417*k6^2*k3*j3^5 + 432*k6*j6*k3*j3^5 - 8208*j6^2*k3*j3^5 -
        8748*k9*k3^2*j3^5 + 5589*j9*k3^2*j3^5 + 12636*k6*k3^3*j3^5 +
        9720*j6*k3^3*j3^5 - 2187*k3^5*j3^5 + 2187*k12*j3^6 + 729*j12*j3^6 +
        3888*k6^2*j3^6 - 3888*k6*j6*j3^6 + 972*j6^2*j3^6 + 7290*k9*k3*j3^6 -
        2187*j9*k3*j3^6 - 8505*k6*k3^2*j3^6 - 7047*j6*k3^2*j3^6 + 2187*k3^4*j3^6 -
        2187*k9*j3^7 + 2187*k6*k3*j3^7 + 2187*j6*k3*j3^7 - 729*k3^3*j3^7;

    return [i2, i4, i6, i8, i10], [1, 2, 3, 4, 5];

end function;

/* Igusa invariants from DO, in the node case */
function IgusaFromDO(DO : p := 0)

    I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,_ := Explode(DO);

    i2 := PolynomialRing(Parent(I03)).1;

    e33 :=
        (1406890045685320000*I03^5+580869727612326495000*I03^3*I06-672669303093293625*I03^2*I09-7082812073747032875*I03^2*J09+62980839785149035120000*I03*I06^2-2374126952093977500*I03*I12-3561190428140966250*I03*J12+199426663975894110000*I06*I09-1253539030705620120000*I06*J09+21367142568845797500*I15+2374126952093977500*J15)*i2^3+
        (-69151459525524848640000*I03^7-49748480040516224173113600*I03^5*I06+79401196395627788881440*I03^4*I09+1252590952081340519722080*I03^4*J09-8433154658404828453944729600*I03^3*I06^2+404183589872483627913600*I03^3*I12-246068269808776610846400*I03^3*J12-54835346450578454969126400*I03^2*I06*I09-25020823618482464790028800*I03^2*I06*J09-480444510737934460031311872000*I03*I06^3-2639847706030724642611200*I03^2*I15-3154479852425804517081600*I03^2*J15-280855688677668305826048000*I03*I06*I12+25557550053111214987392000*I03*I06*J12-222667603199729737056000*I03*I09^2+722245559822418688963200*I03*I09*J09+11024101511207872341206400*I03*J09^2-16570861922538099283451904000*I06^2*I09+15011033751140064117387264000*I06^2*J09-9845979295724143488000*I03*I18+2434066738750090043712000*I03*J18+9165200155848359852544000*I06*I15+663442714616798114998272000*I06*J15-1490962579066798871040000*I09*I12+485266122432118500480000*I09*J12+32367953650457712849408000*I12*J09-18243896350741429015872000*J09*J12-36964619413090070123520000*I21+4690905850177145504640000*J21)*i2^2+
        (849733134649649340088320000*I03^9+1869449818959527606931986841600*I03^7*I06+30237798747471451968660111360*I03^6*I09-66378242353262443954949652480*I03^6*J09+260644186046403735425434858291200*I03^5*I06^2+501568819637643182542808678400*I03^5*I12-47277948524692444133415321600*I03^5*J12-19442932503628927154131801866240*I03^4*I06*I09+7176400926398536023447245291520*I03^4*I06*J09+27891831213890839881438874671513600*I03^3*I06^3-291240853839878040014605516800*I03^4*I15+1844484406369179045899245977600*I03^4*J15+31236508671094402447400592998400*I03^3*I06*I12-4795828028898913924445837721600*I03^3*I06*J12-186119668859737309813101035520*I03^3*I09^2+663275572658754944059594506240*I03^3*I09*J09-291777854740221884406296739840*I03^3*J09^2+1150322866416950875966973568614400*I03^2*I06^2*I09-1990156882696838714035565494272000*I03^2*I06^2*J09+759435190393588828062629090033664000*I03*I06^4+141615744192247111098826752000*I03^3*I18-1693309313779275954858098688000*I03^3*J18+56499584906653958813381767987200*I03^2*I06*I15-120975445216546003205453669990400*I03^2*I06*J15-1377252340580125508973782630400*I03^2*I09*I12+106267919134373876779293081600*I03^2*I09*J12+1693517338022329190770016256000*I03^2*I12*J09-65490599604549151557550080000*I03^2*J09*J12-8665433103246867266052497080320000*I03*I06^2*I12+361073555198047171145831546880000*I03*I06^2*J12+45705787056828139127688423014400*I03*I06*I09^2-108012991114379263222753512652800*I03*I06*I09*J09+60639893206262112142710787276800*I03*I06*J09^2+24381232434751559210720607338496000*I06^3*I09-38654904785237974506056561197056000*I06^3*J09+587998732827271217377443840000*I03^2*I21-24499947201136300724060160000*I03^2*J21-16245098324166776466766823424000*I03*I06*I18+122526102615526536020127645696000*I03*I06*J18+873411451078984770193352294400*I03*I09*I15-4098990672600748493146737868800*I03*I09*J15-1498130104772612108492734464000*I03*I12^2+823064892912187125821079552000*I03*I12*J12-1791622805611475918853557452800*I03*I15*J09+6717925275552323297684855193600*I03*J09*J15-69799849577114848593444864000*I03*J12^2+44368704382766379574109405184000*I06^2*I15-609206509345456097983891243008000*I06^2*J15-150046698862537536779807883264000*I06*I09*I12-4651878863809403639066787840000*I06*I09*J12+287114492362065496497947934720000*I06*I12*J09-874453671055160092192407552000*I06*J09*J12+251653778658585212375531520000*I09^3-1387967379216966132871200768000*I09^2*J09+1904825524615752684442484736000*I09*J09^2-636877639835957960550383616000*J09^3-42503908401514176570426654720000*I06*I21+2816327263978239521327677440000*I06*J21-315777097259090098221219840000*I09*I18+3678258739797263282038898688000*I09*J18+503998913851946757752094720000*I12*I15-2034662281846748022036234240000*I12*J15-41999909487662229812674560000*I15*J12+598887598249998462143692800000*I18*J09-5808120816482712358317195264000*J09*J18-4666656609740247756963840000*J12*J15)*i2+
        19628925950395856025477716115456000*J18*J15-578989697166294261648511205376000000*I21*J12+283366276534257217209321180364800000*I18*J15-268041983653783710553214495490048000*J18*I15+84845915686888807446875838873600000*J21*J12-732843207441648216465428875051008000*I12^2*J09+5720214032083073801128881055334400*J15*J09^2-40477861885383839187058608517939200*I15*J09^2-38354095677254951240407594303488000*J12^2*I09-18233854724314827534876027125760000*I12^2*I09-60499303751264061281694436137369600*J15*I09^2-24382364621512465760334713664307200*I15*I09^2+777065519416319083681865864419737600*J09^3*I06+290749142098457410800312497523916800*I09^3*I06-34145738742422004766563566931148800000*J21*I06^2+269177528774275637525214228224409600000*I21*I06^2-4742246540952693734154924335761981440000*J15*I06^3-538562411902164552832821862103777280000*I15*I06^3+23304449250214404080603267734683254784000*J09*I06^4+54103898149664884816915261853943201792000*I09*I06^4-50385602699373225766019898802176000*J15^2*I03-388212654448582920146692424770309324800000*I06^5*I03-1844893143067238275506442359275520*J09^3*I03^2-13885776222497143421606604035850240*I09^3*I03^2+3720490964389162540875682676736000*J12^2*I03^3+202237209555910123012050800502374400*I12^2*I03^3-21903271821024303189950908095994527744000*I06^4*I03^3-4100087164064903757286374113280000*J21*I03^4+21331922028421597170776659722240000*I21*I03^4+42920935769461716278781765746688000*J18*I03^5-3331679220030362353822913789952000*I18*I03^5-4118214842235482684030710198566912*J09^2*I03^5+6827064098606640546910145108508672*I09^2*I03^5-306250833646676799156092448309195571200*I06^3*I03^5-45138119052532600882635647798476800*J15*I03^6+9203564734651860418531502220902400*I15*I03^6+1515897130187304594718698818764800*J12*I03^7-13653868499040598896384740111155200*I12*I03^7-2851488266896745373810138185465856000*I06^2*I03^7+1025659286531273548816323119677440*J09*I03^8-847185472239526047845007312814080*I09*I03^8-25942070911891849037998315064524800*I06*I03^9-141932406135209991548549977866240000*J21*I12+700185681379815493772785924177920000*I21*I12-245925586711819963831482650198016000*J12^2*J09+86713775867979401032231776210124800*J12*J09*I09*I03-102051347433604596205461140668416000*I12*J09*I09*I03+5707532191433048447968198287949824000*J12*I12*I06*I03-9455422355568777253233567624855552000*J15*J09*I06*I03+3762609789294426928448849773068288000*I15*J09*I06*I03+1382506144852588698572848587866112000*J15*I09*I06*I03-4408749982290707434226256445440000000*I15*I09*I06*I03+127109207967995408492020879410698649600*J09*I09*I06^2*I03-5096819104626346559516433373043097600*J12*J09*I06*I03^2-683628889410217199116828839562444800*J12*I09*I06*I03^2+6543356429348363634663218164531200000*I12*I09*I06*I03^2+3081878679928344041700126446038548480*J09*I09*I06*I03^3+868053932785159666194253181091840000*J12*I12*J09+76530028547701476060372311998464000*J12*I12*I09+102508908142439814933350543523840000*I15*J09*I09+17244554169633843604669328554721280000*J15*J12*I06+1623653349284118881477569397391360000*I15*J12*I06-37659531111935064668904628823261184000*J15*I12*I06+6459153718372689349420618541432832000*I15*I12*I06+5978889875356430501438740909522944000*J18*J09*I06-28292765172059255532610199224320000*I18*J09*I06-1613558851302966088457856208601088000*J18*I09*I06-2450174715322878218340606840668160000*I18*I09*I06-2209571887957799483449522357744435200*J09^2*I09*I06+1165507127201093926771425009047961600*J09*I09^2*I06+111894827748772170433451742065590272000*J12*J09*I06^2-451048649197247254843354018983444480000*I12*J09*I06^2-203593481747651654201708896881475584000*J12*I09*I06^2+451908098327831245267286503609860096000*I12*I09*I06^2+274598169447244600097656031674368000*J15*I15*I03+27681337639739198416755414269952000*J18*J12*I03-90583824965517805667613168107520000*I18*J12*I03-234542928851051116721027017605120000*J18*I12*I03+203369690426500227582297781567488000*I18*I12*I03-6237015531195186951569629249536000*J21*J09*I03+27159006222867294273344328695808000*I21*J09*I03+198265121100834664952581914938572800*J12*J09^2*I03-322071494439009015521175670043443200*I12*J09^2*I03-13844167853213928093739005247488000*J21*I09*I03+118542900606802578424631031496704000*I21*I09*I03+15978968878083104140759036801843200*J12*I09^2*I03-41867056293210697032701572231987200*I12*I09^2*I03-2772245666252414130630038818652160000*J12^2*I06*I03+9971322407417888768885524009058304000*I12^2*I06*I03-111053312797393666211529989126356992000*J18*I06^2*I03+32064816483156832344912064822640640000*I18*I06^2*I03-142522340202727573351470296453244518400*J09^2*I06^2*I03-13994248739876611450881987145472409600*I09^2*I06^2*I03+888599315308147326656870645036482560000*J12*I06^3*I03+4951166818509019513733763225643646976000*I12*I06^3*I03+13349186048877627602123750375424000*I15*J12*I03^2+268195286657542660498232404711833600*J15*I12*I03^2-111791043394887083764029043035340800*I15*I12*I03^2+115375738037243867138663822603059200*J18*J09*I03^2+41676574381380618658893883087257600*I18*J09*I03^2-174206517808841836733817386591846400*J18*I09*I03^2+26051597554215366039791945436364800*I18*I09*I03^2-77755134558259155917383079433338880*J09^2*I09*I03^2+40977439995703510071958983105576960*J09*I09^2*I03^2+569343688616833136416592788193280000*J21*I06*I03^2-3928814969783378235576868059217920000*I21*I06*I03^2+260540476663684114041391631881469952000*J15*I06^2*I03^2-37687680767391448522104813020774400000*I15*I06^2*I03^2+3910052931256630913944710286327519641600*J09*I06^3*I03^2-3130852360406323861088499101401822003200*I09*I06^3*I03^2-56612996479261362369673213614489600*J12*I12*I03^3-134156153888930296912368423099432960*J15*J09*I03^3+30706198923010522678964162899476480*I15*J09*I03^3+197579258444107137571439006523064320*J15*I09*I03^3-43572035322087996466676218629980160*I15*I09*I03^3-1470099339633766233528057194348544000*J18*I06*I03^3-856500418579130353251201960640512000*I18*I06*I03^3+708012139692564141553437650064506880*J09^2*I06*I03^3-1658890836939871778991896456048148480*I09^2*I06*I03^3-36053652283896937333446370343780352000*J12*I06^2*I03^3+269394879333282216905403005811661209600*I12*I06^2*I03^3+18062481844821096374521068005621760*J12*J09*I03^4-67401094464895304495135969740062720*I12*J09*I03^4-8538004067294621527503779313745920*J12*I09*I03^4+78154361787767901395354251627069440*I12*I09*I03^4+246393483210183736302754381745356800*J15*I06*I03^4-1044371227680232175596052274374246400*I15*I06*I03^4-12009866928622615050268686715044495360*J09*I06^2*I03^4+13413008463199339658780191736589189120*I09*I06^2*I03^4-17831440884183558857015336173043712*J09*I09*I03^5+232037248041810749462014940361523200*J12*I06*I03^5-1216574282194616087423170710287155200*I12*I06*I03^5-29892038648624979835610257057382400*J09*I06*I03^6+516557382638713322051821975791206400*I09*I06*I03^6;

    e36 :=
        (43486933690593367073486954160132595099682278323023865000*I03^4+78374326243871895808191863135098969518402386107669760696250*I03^2*I06+635996405224927993449746704591939203332853320474224025625*I03*I09-2299371618890124284010622701217010965895700466329886861875*I03*J09-845385990945135055908586388872977648737823490599583935600000*I06^2+2641831221703547049714332465228055152305698408123699798750*I12)*i2^4+
        (-3000998811948481306422180250689631369552599391584122648320000*I03^6-5434943592210134633310789321461260270349415489300165864700320000*I03^4*I06-48668672659915711505614709018380235329763989416052306162308000*I03^3*I09+168622838057424726356210393735177762785837665234565066478964000*I03^3*J09-191863956876549191753410615886074396190835182445407425633351680000*I03^2*I06^2-241044785595909839466346692854214839588607300554820278953200000*I03^2*I12+15329353384538754316124477564205724138941588332655978045720000*I03^2*J12+3092130181865745172761928536272311607309080015545021518124480000*I03*I06*I09+10545313686564814569757716807940005506682026884971890928015360000*I03*I06*J09+1252879277753895522214947035166599615081689753272922812439142400000*I06^3-17724177974508767605921763994797835262226611351967793866640000*I03*I15-725567159375893987434745823700067593842099334334467326561040000*I03*J15-14337166476594898130717624500328576258593575067562765212032000000*I06*I12-1681622489840004753586132122458118552369274252568589984537600000*I06*J12+40244088679138691856579957830457964489098177533584762975200000*I09^2-106273806845953058638834754264924745994508829271200347657280000*I09*J09-141810034966509180371935455571672329903982127141925023630880000*J09^2+17201068778733838929842633281821481582321389472807493433600000*I18+721686576403311475597438668447109891970482889798381183527680000*J18)*i2^3+
        (87769119199785515030811335596526871347130200286887617599897600000*I03^8+122169471624699825707751753581631573709404942068652500971317156249600*I03^6*I06+954686056359333276638851046945008776982289946541329504459335516160*I03^5*I09-3756528157771186629887240113904616641461875103034059460022783098880*I03^5*J09+4978000386421470023546635546605995124387718212529075122280584157593600*I03^4*I06^2+6484507747938528206209963207386978344745304812103392904745420390400*I03^4*I12-687374156902952470583917067667893373733338341753906170153380249600*I03^4*J12-407221277196765550074373742814721986063905644943481939249453337804800*I03^3*I06*I09+472873699488474324644099533220605867243246522487880919404685600358400*I03^3*I06*J09-278822860915602702413256803449609742588117160310623542178363337605120000*I03^2*I06^3+1120213458208893845448219409811581879384509272539137927936226099200*I03^3*I15+39943631020700875832789962728794159328882025101698513981886765465600*I03^3*J15-967869477155704850838612544391125595435406444315369762591226920960000*I03^2*I06*I12+356080148492326886307410646418996543946242675931201274141441884160000*I03^2*I06*J12-3933675157762035819084765290186194315177462980076480842603793612800*I03^2*I09^2+11682692597457624667120012232296546307820245449529251325717628518400*I03^2*I09*J09-20186453498130641444802234469392387419285436112405019855892701184000*I03^2*J09^2+10109647735655920271119301249926594062459249474106618345784289263616000*I03*I06^2*I09+18745205524921980517460439211015745788966722560621134443120084123648000*I03*I06^2*J09+296503023114466460091486794936028158318925799578042544280188055715840000*I06^4+754477380845950241820687791476956506003322423461402934303522816000*I03^2*I18-34456434056795111828285279689051359709140841224949112448006979584000*I03^2*J18-296266458075146861691935971181251937242993238204915907631062908928000*I03*I06*I15-308168665597441213980886133142013763974916947178057498787119038464000*I03*I06*J15-30690746220331817011258178242899945539794379053711042806474866688000*I03*I09*I12+4880771818910605575663828166000484568809662252879135477424553984000*I03*I09*J12+24611356698863026598346958447543459512167001209550948243347079168000*I03*I12*J09+15104322088754831654700852331931867390036727756313034474907697152000*I03*J09*J12+27398944177115647562491793740925523522902412507099852691004215787520000*I06^2*I12-7757286652285871220901118487639001447513032745086312558270747770880000*I06^2*J12+55432991590944276805532815773016747372389879085267203961451053056000*I06*I09^2-359197940125676720496100817215373951039434529313838973799431798784000*I06*J09^2+64684374578119621615502840441618204922528266270219932167603486720000*I03*I21-7380488569529115140295176955837965162991317525417356580684759040000*I03*J21+416360417270668620484380001284982777499568639094700675668582072320000*I06*I18+651838449650498104502745835108787020149924477262671405647108505600000*I06*J18+6047762110399465271466731073131782273910767599007362366333321216000*I09*I15-680434023548486220544323771915348795065240257270991941865766912000*I09*J15-96828066012486088544991125635398126192928507506385430398131240960000*I12^2+31345823939232975374618504005574459108570297181402463475513425920000*I12*J12-11245155146373613376730690901389008789603534081534766748719316992000*I15*J09-18830760370748838856609341796244220819230735885481837189927469056000*J09*J15-2095886764687931848991533262436147184926301707206950419415695360000*J12^2)*i2^2+
        (-1105036906809648168172314362869521087344060442806271968192747274240000*I03^10-777490129860712560836410725371752064568007631184125772212897662894080000*I03^8*I06+9836191926064239081152246750924838725593554822187067112053884846080000*I03^7*I09+26297508375272640240460957438765462178807581476613664984714088284160000*I03^7*J09-32608288790629092185355468327740371750583962451940396811499230791204864000*I03^6*I06^2+145263499405493579887689540141354043731639373859075500615264653803520000*I03^6*I12-25970087669604856943265209894062908997298613987405523179671566417920000*I03^6*J12-3644431887193416402172340858396786898497795894984106893413618243055124480*I03^5*I06*I09-33776009502440908452761549881719398790571049563066130666471760356085596160*I03^5*I06*J09+33662821990849137372090508326482283867513968181474283542802506160948641792000*I03^4*I06^3-161690993945760197193777603395553890555599328385113602534229095219200000*I03^5*I15-7438481865163279510238074175414090576996294820813628938320336734126080000*I03^4*I06*J12-31678284221871628515876129744665424910181036071392043653762778103021568*I03^4*I09^2+21104740200551152917365847376441045748756507909972990199381694315757568*I03^4*I09*J09+1457434140831510299401961859798294592297776339354564421456700711588855808*I03^4*J09^2-413799622900340600731166495109887487854321476327323066904389541629819617280*I03^3*I06^2*I09+3443284048880354561673228016884716169011377477236232117475934808333080330240*I03^3*I06^2*J09+238119596711523527232302796798964929390988875158922532708175306119452819456000*I03^2*I06^4-39042868392566927927093614735628505982143627440081086886690238234624000*I03^4*I18-216727321808402737777495419940233266589912428638992680843453235462144000*I03^4*J18+88157019638555466505968189989716230610794750231978021764934403255959552000*I03^3*I06*I15+70885089644806909430595227385511919091383595556166582576664702766546944000*I03^3*I06*J15+1147205377536292022068699704317837104009054129757595480383260378980679680*I03^3*I09*I12-188019788126305990471461998783401649301093234759574175423217617149624320*I03^3*I09*J12+2104268213057718178338426043661848559068399457980088056298170907948482560*I03^3*I12*J09-1553165072672668268616663543033986638370316421500392578558453481409085440*I03^3*J09*J12-7040608623246187192596977583001100272048852651065410396504509249260355584000*I03^2*I06^2*I12+6187554071689691007858726458574162034995579329173495635492156366221475840000*I03^2*I06^2*J12-5027864348822208220357222476052548258391382005526097099858191859182469120*I03^2*I06*I09^2+37792037299760484977892731545906058427968909535162381420000651929525944320*I03^2*I06*I09*J09-456300632019478713110869022982061768097827914544970860406154672995177594880*I03^2*I06*J09^2+563607710316540680793130559109059663233250985640261964724395500893209257574400*I03*I06^3*I09-164514510270307046247266997809342936335010155973921313545414891070618284851200*I03*I06^3*J09+16263517547257651235744398846682846224678908552922500592614935197301656780800000*I06^5-3732615653782230992317874986671279245196541872627029915081402084229120000*I03^3*I21+473663125014729275217488335410559327331477599738962680431950409236480000*I03^3*J21-57931334163939321421461195110946218383337990306004346756704332427558912000*I03^2*I06*I18+604991170457386646855601098954862976770109964109500874560315059957923840*I03^2*I09*I15+252399084947333823445098312734686306534967213513813467289175279450193920*I03^2*I09*J15+21222376547420635226954636648712055916551511999739452825742733071089664000*I03^2*I12^2-7735701048622471190527967933249717514395098806523687524504516377444352000*I03^2*I12*J12-903226728529466564165129066092621230588453749074349049847699747865886720*I03^2*I15*J09-2945235778559496678172223131223727095427285397302225377151214981333647360*I03^2*J09*J15+613056665260522633654002914981269056696572899735236017386287953608704000*I03^2*J12^2-2098026711459375933158344581222749143916222189508298181747212113886052352000*I03*I06^2*I15-42213572164956148606971909464382926892244788888622523432477373309741170688000*I03*I06^2*J15-787068672344984405238910943325769476601271474884255052095719585555991756800*I03*I06*I09*I12+221301193496983229909295022638324289172723581169611965377690964883773849600*I03*I06*I09*J12-496264787177780232280320372944888628219333060209110133715734859366373785600*I03*I06*I12*J09+272978282235055120346614109515108972858199728971170896929926665804657459200*I03*I06*J09*J12+37110362536760342017732233936740414113167083208966653653076255346524160*I03*I09^2*J09-4036560049226000503526224133111714317756393968948238343541839350632284160*I03*I09*J09^2+9730854686482251793449513624045125253480218639102728428496653243163607040*I03*J09^3-258601593726373973334064980222128496006128313998788858721496287753791340544000*I06^3*I12+1661813392937302937887708025896195982311131472331568810182687433582182400000*I06^3*J12+7611758794746969109879742771360614646235502771994462938090930893558172876800*I06^2*I09^2-19582879428409452857563017816803554732814395057147390708359894665000071987200*I06^2*I09*J09+5205813640448640888020492886357404904980289169432882760888913226442892902400*I06^2*J09^2+1004523994427752699043444522650037858094393262263935069613759932745646080000*I03*I06*I21-151180009377716769830085146381199505592613749814933091665828589464453120000*I03*I06*J21-213354876490072927804947002522477109777950037916156935241962414617395200*I03*I09*I18-8573262214089128269112310947570608562724915612508732614088923480588288000*I03*I12*I15+72292173689319153143591847220861997491457249861815215553011833873891328000*I03*I12*J15+1471881650811924630257853528675934635101655675427366888991124514406400000*I03*I15*J12+994339327498640350337187238427902730368250198125886648678981438118297600*I03*I18*J09+2591873342038238466295726390638653768489443733889907278356423947321344000*I03*J09*J18-11333865194777564670401617957775521811064189728239264628822693545771008000*I03*J12*J15-830651571290498008648417238073992146464137798210275546791357775934914560000*I06^2*I18+5114465963630405915820171149055347977237984677337194388584061131231854592000*I06^2*J18-117962672382696352847021424215376840434553777266878754796997968741059788800*I06*I09*I15-532886570597892909424421233675684357868079608361218169378866771561703014400*I06*I09*J15+2767348163962035724967279734111858992864424804612235316712995769773195264000*I06*I12^2-608495606134225909573483582227877625474335304831005261534231652431036416000*I06*I12*J12+121976825136751613016580481585422324469364495583743473712853729157736038400*I06*I15*J09+1139696285472713553324927254168935827881880470583130539647773116086825779200*I06*J09*J15+31745952355302000392504344090877937852655968621819843631423746264268800000*I06*J12^2-4755921646911101496899061109762113092569600050796305631145954657068646400*I09^2*I12+782937894621757713243677370524394079913757207694810498095883311120384000*I09^2*J12+6688794153762294537753804670703268907142556856556673912433199968734412800*I09*I12*J09+3507455896072659872402631630183731450407099759363282067597386009962086400*I09*J09*J12+23603415183317744760082692268571301339084301799068523409359210080842547200*I12*J09^2-14718404636384658882833805384879506225000834565676081701591416556434227200*J09^2*J12+9130942776370948070033902537758017463088356046447395279252650327015424000*I09*I21-1725918889635363129849663854869558040837822923452453683776824979488768000*I09*J21+4622205709936055734671575021300833334201332175799072501942484922793984000*I12*I18-68555377288759945156125380044674623438431247129163933431554322127126528000*I12*J18+41963609820014668415698353715191939084431417846105100487627647221760000*I15^2+7074842163676771762968757771047769106043062281203313367758930591088640000*I15*J15-1400579394247355836781751377275892328428625185295662013029174067855360000*I18*J12-26881756627737924265226265925941656934368528536072247214554324309901312000*I21*J09+4289470939360801264891384957589255594378248638867566114390545136615424000*J09*J21+10475441380275801082852547702288696324119059866557793578883187461849088000*J12*J18+785575504484826311090161994885367037225964556950416237152379600896000000*J15^2)*i2+
        180548452379450337261686406667238957324087751368120114890346563411642417152000*J09^4+18218216418787298396595741334794837528932746808272099971198317474290335744000*I09^4-28775502079980625695395852641183127565000318481630666950537919642538973529846579200000*I06^6+2827993957401153293583812600221786646797744699169960612506790233374720000*I03^12+2461493430043951466461311099573949217889626901831848864231689696821777530880000*J18*I18+2939090733632138424588965732591123522009501848079037820850160478387489996800000*J21*J15-21193646918925255460498743020077408374907881307643718792158852944379668070400000*I21*J15-1371379197925699426611621108628718194021166847884665062332454475472987750400000*J21*I15+7382791782403299983502286784829058363028308840285778470455668666103182131200000*I21*I15+2149139455234108979926134234262343272652174237641467637431704886525233725440000*J18^2-349429920042997358759429987676254821124117124867796292781073845026574827520000*I18^2+256722531976327306936172301866570435681502093435800774343874758879844761600000*J12^3-1042197390300125189450879892114758999805538507258359779392370946274712616960000*I12^3-621178598811319184156690811455899557786069546054708918241990271618789670912000*J09^3*I09+470719422530067200154577573193255707445213175794233258954409448513736802304000*J18*I09^2+201389688589267673529230578909303079147330455097210647000566245329886773248000*I18*I09^2+611220911091381040987860345928803878628278384448702325130584444511855837184000*J09^2*I09^2-191224154182481692640746570039318603469446969027665946401579468578837495808000*J09*I09^3+616017311851810507715095623889100504723405168199311099424154980593645849149440000*J15^2*I06-29691403268253333547952449631391370594765585504745312175477932421639768637440000*I15^2*I06+938037598727969813966365651260249151575422044968798502092781194966086556057600000*J12^2*I06^2+43262828321530139988041991144491873992517903995794501141551103034892354165145600000*I12^2*I06^2-16374569912725972699311816949273558545949571921948443439982475724973028587601920000*J18*I06^3-9673818246078805128456330772128577003382393321275013526271759078871055885926400000*I18*I06^3+12046296748129623783663078064392652896342367003783042573357897659509252888199168000*J09^2*I06^3+133675597411808470901020476753049528655036872481490076238601157278520183697178624000*I09^2*I06^3+523792461533640314218647470716681968376035102266833903276395911716665916611624960000*I12*I06^4-6169384177986189110623326525418051600274696700824051058400028550244010557440000*J15^2*I03^2+2271082834922412257982679469884925644519789083049882070433064568395778752512000*I15^2*I03^2-4749266569184049047058082335430676059596503438867817080602750394569479432437760*J09^3*I03^3+96832057169311251294906260921240050762629784384253902215061986434701999472640*I09^3*I03^3-475321889874934197721083210679236899106209698079739024538369945877354643456000*J12^2*I03^4-29224881687730345032070515989098367945957367552927109380432996955631922236620800*I12^2*I03^4+64546028908522037453982741045584718048857647666689943627825696499544555087986688000*I06^4*I03^4-2863898131456056567221113199848076041715723191386618191656518925858897920000*J21*I03^5+27275099138035256075497709777138685129069657275200191779455679594496000000000*I21*I03^5-11112970087886427816969563983928622673873832564676878757097805382760267776000*J18*I03^6+2161175174208105621527028311671800844856718060394799874358143806638915584000*I18*I03^6+72580442392043002893963018588957440156228584479227324983688421199893221081088*J09^2*I03^6-20910363213571595452306147367273292613814900257903921636712362923490088583168*I09^2*I03^6+1219477458355247044073698161961683619052032726691921909532483963481650593424998400*I06^3*I03^6+14771161279280337202194993487615600915467518949487000040253770445802910515200*J15*I03^7-2745691745927493193327904781696709048668141099710867668950807045329230233600*I15*I03^7-355862164263212491776703939060187916840371693905247140868174385236882227200*J12*I03^8+4057438603886849324540862397627464831087436325232550309120918516476464332800*I12*I03^8+32672763549547398138955908275911545396819061696162639885136057439390961080729600*I06^2*I03^8-345317392758087091964137133700222587098182612640117799644950500458270556160*J09*I03^9+148546990965849507893465119303438085511393314857080418716983574100306821120*I09*I03^9+7552687677375015082633860879568386936643126727966240911432772810165138227200*I06*I03^10-2252863196559605954376182432091882787157928909602638124479896994831222702080000*J12^2*I12+3496467358092755950591805897014546700323872659012311964041041248950325084160000*J12*I12^2+1264647687730802688036550657275506841320837941121267671656728012395860983808000*J18*J09^2+335525680018385124555593856275831646071724537469108237715035086606512947200000*I18*J09^2-9259642678908127377639384432608829378002375023845941959993857322428735160320000*J15*J12*J09+5361118106952080155304462247568398803474766298803018855003954827334915194880000*I15*J12*J09+14627868544508100877931520003607507600407033864368710749172693736617414754304000*J15*I12*J09-6834552617898642265996813504237571539886724759402432102633832008010665295872000*I15*I12*J09+387282578909658578542369187792694335494525264565072603333109213800913960960000*J15*J12*I09-1004652414071472873366479324822673230990041266396751359042323207475941081088000*J15*I12*I09-255148606648071788048418860095646784360577050724892622368969539066313834496000*I15*I12*I09-2547850661943589018185617114383393539952348436217632178447547302428930998272000*J18*J09*I09-608277309963489368012914650663425085676676225484387206473248069791879528448000*I18*J09*I09-136216645909840116465715799667258825574963623019311284367706302346013850992640000*J15*I15*I06+204729965368430030856734998261277808088480112788470044350462505779312742891520000*J18*J12*I06-40882533275390705171302253226076562402849348266220550733590016444742605209600000*I18*J12*I06-910373661146348083855667615039185196086206334823665128799663372086832665722880000*J18*I12*I06-79096303875291439103154450434015111615372991830266290944584673224073108520960000*I18*I12*I06+36896262705815386201061881809262072254995064835950702722762837915746990817280000*J21*J09*I06-250324508610987768796401399555519274154115676812579268001498546786162851184640000*I21*J09*I06-94052170560110528389082179400713605291933293970401659371880165765437921951744000*J12*J09^2*I06+49422698123865785502195107986417348412313442488464829366745976208428378357760000*I12*J09^2*I06-41372151369001343577815661203758370851190875179598173889761094357119286640640000*J21*I09*I06+265861586349576765949429921062575109841677380035508964151864692645696550993920000*I21*I09*I06+12936683142441930675012660336821658393838156055893200690453337669435203256320000*J12*I09^2*I06-58048738947105072540533263027809038568016923991876379776408121191261450272768000*I12*I09^2*I06-14816465865936988330787674344186205208671972370715383928221346778865325708410880000*J12*I12*I06^2+9647584000024375410154460648661664383998414754081772935000855521438815500632064000*J15*J09*I06^2+879702821266585926291016543669312022471164580142011021069768050956596441776128000*I15*J09*I06^2-18684101707314783143394456775228174429503448061768772093415701668527437735002112000*J15*I09*I06^2+1884799376802445542108230108021319572449373426154601687404762977454490675838976000*I15*I09*I06^2-123830785986980013220893316350030737150935394260575598393631251424462767204073472000*J09*I09*I06^3+5565280762879277007621618162555657345924378573421711064473750650407897530368000*J18*J15*I03-18343026862317495020470908629417516997914222939256762525276104285237626798080000*I18*J15*I03+27911035665572342627224595989831054833163266043931378217341519535995036368896000*J18*I15*I03-5531466467163421062771842252733614870943358371111118492990033937265013555200000*J21*J12*I03+39886377735760746907213653148201172538727825574533999406224871714923216896000000*I21*J12*I03+10642840459315992832159449945897177600266579237056962796411502660101739642880000*J21*I12*I03-75876460054514185831923090240843328916021465576343114260761116894882630205440000*I21*I12*I03+16867722586525912079173074542853909203240214156556518777095182945641792798720000*J12^2*J09*I03+58236430045770575881426531100196465961131250942703891974348958629895029653504000*I12^2*J09*I03+5311069922829870406061440409929262774968729299650787308988612445728820690944000*J15*J09^2*I03+839988478762333628875400007463213531929509525669215928330987558269190406144000*I15*J09^2*I03+1810901903464232504376898624562420094059639435180620079772722289845855059968000*J12^2*I09*I03+232444634706977827081372093875594202642068774961191887487655755309014581248000*I12^2*I09*I03+3471101985347028804018004747740307042068880915288085311930936153668044036505600*J15*I09^2*I03+2026787078730795396893477771716881724951007267628414946079568370458271363891200*I15*I09^2*I03+69705833117356669740134088756494396600937567955016505372176063521545691909324800*J09^3*I06*I03-39373798439630661900503472670227172001722343898697662504748290057321753398476800*I09^3*I06*I03-37971220729102432914261784914456306581545234737040265962814516399504464281600000*I21*I06^2*I03+12505687084984761805298514412773963402524663295795365641735733330659421234135040000*J15*I06^3*I03-10044253031599038116464130315572619448187429249253023883481499944533690060636160000*I15*I06^3*I03+240301047956952003908945525790644864625748723803640636443793124912667598170095616000*J09*I06^4*I03-435892058776556210750042258547242835110592403409813913822919425310651734514728960000*I09*I06^4*I03-34800805536426121347504849724812722916588049058309123961983903024667829469184000*J15*I15*I03^2-7914304851404092844017246141529422290032662925281601003145577965857884078080000*J18*J12*I03^2+6216007039910886461634886515375297969283381869773609730855912362277548851200000*I18*J12*I03^2+63484902356677737832860791981241720887693290693609721184029941324183058251776000*J18*I12*I03^2-19039764630944219478539965700564523087634607169005905334371862226328400953344000*I18*I12*I03^2-2294140711101339142691710546463618119819192594686002118957373980787360137216000*J21*J09*I03^2+16489424734667035891448863690058226005366342499598498567210164212090491895808000*I21*J09*I03^2-4592529415532092710957352873204957957786448726429329769894116147133406196531200*J12*J09^2*I03^2+15971675888507271035437174299886942873470839755951737440522119922346378028646400*I12*J09^2*I03^2+2685680110546496498913635202691550432748311485785346733856056087800071585792000*J21*I09*I03^2-19006082331245953105905007861400589347684544069640670559247336124474537803776000*I21*I09*I03^2-1294732933664081953728291134470395631444918449199652795395643769782935958323200*J12*I09^2*I03^2+6078271377347895110836055295149260104380289617492554438238478801647811585638400*I12*I09^2*I03^2+127240433938821367632750205277631264731548031713545759711919345411974255083520000*J12^2*I06*I03^2-3265123824754293632705792061830744269924807932711005873881603997622476199690240000*I12^2*I06*I03^2-1807592830730866081140308748143389689909462469881848289936970483751539326320640000*J18*I06^2*I03^2+1477248330637470545724469859606571405668657703594680994937296925152760603607040000*I18*I06^2*I03^2-2893778105418422530625996011651734157792931758382777547874717365515334735573811200*J09^2*I06^2*I03^2-10125478984108842895863824615692061012761420229131596348003689195509194263258726400*I09^2*I06^2*I03^2-11987236034720186409326560832035989856151665157541390897622015580643915013816320000*J12*I06^3*I03^2+122422806809789874919365932795543754570891696904851771608143194332942033454366720000*I12*I06^3*I03^2+6793091181394259636209992244638707525287402201837562662114773207024106733568000*J15*J12*I03^3-1279667645676109259377380213102499838771235312139612822134304692400337977344000*I15*J12*I03^3-68387597085550428945640539152452678106863334796141358876531761015249603605299200*J15*I12*I03^3+13788337187045171107135663317671563112550414704199791089136118042122964801945600*I15*I12*I03^3+6156034008022093482576286125737749108031858202204851797380292631109534587289600*J18*J09*I03^3-3325663683842540226252533161292102722473431934643212390725587332319089682022400*I18*J09*I03^3-558870528838234240676121028109670107102791937180175080278116645158876558131200*J18*I09*I03^3-866371898737990747538788037406629372306961911190570130646627778889155556147200*I18*I09*I03^3+4269744022325153761320348661611915389940398452574351771172640082773488980459520*J09^2*I09*I03^3+1540346160803563659519006668267400968051156633228734189434577234516586350510080*J09*I09^2*I03^3+34591485216760540932615618174196574361796891808748518364522288916069770854400000*J21*I06*I03^3-251505028082664950924619457723364201142498111309899828759145364081123975495680000*I21*I06*I03^3+8458190304122190558377655221632238928960589427502946690532753123685236547256320000*J15*I06^2*I03^3+15822240878266219478942109670628781399337049175508122019138432043564087822096793600*J09*I06^3*I03^3-98318610652878606567003934716002648053061906910523107302535808073703374711055974400*I09*I06^3*I03^3+7479508580896876125635911359701013951844297433924860047228182445060577768243200*J12*I12*I03^4-5475852612533889593755306164812739642151110076793639751082426375464682688348160*J15*J09*I03^4+1433430841496841438538291599853356787626213661848906130756566589254719640698880*I15*J09*I03^4-383116095752717287476127738329514593607080681383132391056021602327957528903680*J15*I09*I03^4-134195220856628354140613399056896005345787938123756219847046135960427047157760*I15*I09*I03^4-79159679260709215476068116666124932474489210639318217623991559341351217659904000*J18*I06*I03^4+71490995054924606866694526875076657520595477831506713822240435857329263476736000*I18*I06*I03^4+148685211578675992674127187757984714778314130394682578185257758956673768179630080*J09^2*I06*I03^4-3887076619211117530784380002734092023772428584482464736991727604782105781862400*I09^2*I06*I03^4-1354622461135673423914777537565812614471349142663755675971313650824698461683712000*J12*I06^2*I03^4+4823295678194975716970942692702545755481923186734046230184923501864662644608204800*I12*I06^2*I03^4+155878541827963043667327706461186326549944251432522333160753587532454858588160*J12*J09*I03^5-934038109270914360513513430652836329650252279124262371181855252964204378849280*I12*J09*I03^5+254344072786646768633194122966287317901822200889317545735235043870180565319680*J12*I09*I03^5-2067967069869341215247444496863451452657677688779573042134510872183364114186240*I12*I09*I03^5+69159359138263786419367857165598650876174225542610257384347705259392841967206400*J15*I06*I03^5-19877551955672902545726751432345353015068402716422089783164784337313894445875200*I15*I06*I03^5-1318061770531744654687118966113842443062468826065565954840645397141013815424450560*J09*I06^2*I03^5-486247386296852138659659074384235495747950828199518884268868965611601599219630080*I09*I06^2*I03^5-107483635691607825849361418529021459137173744776441079153755175265300058734592*J09*I09*I03^6+742974861752510544827076707731336400474193506128876505167592021933436803481600*J12*I06*I03^6-10213277690758783976453732821188210294687386280667554502586354441555461904793600*I12*I06*I03^6-3306683493391880184929963738728450538229283395130955622310399546225771130388480*J09*I06*I03^7+993573770762428509686833390687782724004739423199484427719808955368614720962560*I09*I06*I03^7+73649502962366114032998222638097511170140917729062537715642691983828857126912000*J12*J09*I09*I06+131195764117555679045587988166774040749081414473743933217992453018445653475328000*I12*J09*I09*I06-63576765277959550897392227233433727568696189769052641669325711117852050718720000*J12*I12*J09*I03-2819937635889565080233490995682642105883317119567332186912067843533314195456000*J12*I12*I09*I03+1805524078859961827271153024163902674893726748321910675284344353469789686988800*J15*J09*I09*I03-9909572846396502371247160959465369611717555275995469933292827187743237236326400*I15*J09*I09*I03-1401527420731314698522482175766113842274050114834271191863731460709327747153920000*J15*J12*I06*I03+2609038902430776605093367846687520730219567932210338837509383386929827216883712000*J15*I12*I06*I03-1058237764814602015301036551713205406997113789723920141145048256338205339549696000*I15*I12*I06*I03+70843476029162466849514584871761483106842757700769543165156704329277846323200000*J18*J09*I06*I03-81745096555562790000756971925541692245069880228031665754692171200993477787648000*I18*J09*I06*I03-261455047292977964893912147262385750023544147207276566762101449946969273270272000*J18*I09*I06*I03+183411964218029711282365575150424132839599658806192185830217817631852419088384000*I18*I09*I06*I03-69066605457009461910421774772895713618726162290104053512784037237537542819020800*J09^2*I09*I06*I03+32408956664384350018586708106741950399243899381645800634314222055045773184204800*J09*I09^2*I06*I03-4435580595305336620548673470782047857585194141703715811680252534954596872749056000*J12*J09*I06^2*I03+4770083155514117803483429655811027021269262437553749231163181602714240656867328000*I12*J09*I06^2*I03+18398252496469175750020113672471988359368596848221489954001201774133844631355392000*J12*I09*I06^2*I03-23608831052758212383588811981134634341157236515587627637413972403133823911460864000*I12*I09*I06^2*I03-10298391504721167847950323285759487133993721368490276334981073939360116218265600*J12*J09*I09*I03^2+4206320371918420012399232245545799716044489669698907340256758120862378780262400*I12*J09*I09*I03^2+300757718164747195226072145710226294743733521015564087468655531082847166136320000*J12*I12*I06*I03^2-719324672533061852227436609832622233546682735185564717094376530205911308828672000*J15*J09*I06*I03^2-224326833335134898263319152389951862873500493591547930274641825982710959570944000*I15*J09*I06*I03^2+836537309085678934059270740730982609140356970991408765177936238551274303048908800*J15*I09*I06*I03^2+452271701440283226435000887172234616243155065429393758165684951330238456502681600*I15*I09*I06*I03^2+11404004847620862025151904417101470298469274695527059281064067459504256459158323200*J09*I09*I06^2*I03^2+293594434054682351427620090219414707029791209546112149557072200296665203500646400*J12*J09*I06*I03^3-1206558560940630761793487892892578117743685205003034229160863508240225731503718400*I12*J09*I06*I03^3-122219375488629930242100941989023857164851570136520757860805604823213182392729600*J12*I09*I06*I03^3+801657499078785507135130493807474429518435071357365378246219548719494612385792000*I12*I09*I06*I03^3-67292064905901632502915216644775154787090004696182919172662936056329074911477760*J09*I09*I06*I03^4;


    assert Degree(e36) eq 4;
    //[ Valuation(e, 17) : e in Coefficients(e36) ];
    //e36;

    assert Degree(e33) eq 3;
    //[ Valuation(e, 17) : e in Coefficients(e33) ];
    //e33;

/*
    if p ne 0 then
        INVs := DO cat Coefficients(e33);
        WGTs := [ 3, 6, 9, 9, 12, 12, 15, 15, 18, 18, 21, 21, 27 ] cat [15, 21, 27, 33];
        VminINVs := MinimizedValuationsModp(INVs, WGTs, p);
        if Min(VminINVs[13..17]) ne 0 then return []; end if;

        INVs := DO cat Coefficients(e36);
        WGTs := [ 3, 6, 9, 9, 12, 12, 15, 15, 18, 18, 21, 21, 27 ] cat [12, 18, 24, 30, 36];
        VminINVs := MinimizedValuationsModp(INVs, WGTs, p);
        if Min(VminINVs[13..18]) ne 0 then return []; end if;

    end if;
*/

    /*e1 := GCD(e36, e33);*/
    e2 := e36 mod e33;
    //[ Valuation(e, 17) : e in Coefficients(e2) ];
    //e2;
    assert Degree(e2) eq 2;

    e1 := e33 mod e2;
    //[ Valuation(e, 17) : e in Coefficients(e1) ];
    //e1;
    assert Degree(e1) eq 1;

    ig2  := Roots(e1)[1,1];

    /* 2 and 3 invertible */
    ig4  := 1/24*ig2^2-4718592*I03^4-69009408*I03*I09+249495552*I03*J09+91729428480*I06^2-8504082432*I03^2*I06-286654464*I12;

    /* 2, 3, 5, 7 invertible */
    ig6 := -1/216*ig2^3+22208*I06*ig2^2+1/6*ig2*ig4-532992*I06*ig4+22548578304*I03^6-19219806683136/35*I03^3*J09-1887473642766336*I03^2*I06^2+10702219640832*I03^4*I06-985581748224000/7*I03*I06*I09+308855024123904/7*I03*I06*J09+15618464022528/7*I03^2*I12-770527199232*I03*I15+14395404976128*I03*J15+1808317261283328/7*I06*I12+193732552949760/7*I06*J12+3353106972672/35*I03^3*I09-900986830848*I09^2+2992417800192*I09*J09+958062919680*J09^2-1009023713280/7*I03^2*J12+440301256704*I18-14529941471232*J18;

    /* 2, 3, 5, 7 invertible */
    ig8 := 3611/420*I03^2*ig2^3+39216/7*I06*ig2^3-1/192*ig2^2*ig4+5197824*I03*J09*ig2^2-7222/35*I03^2*ig2*ig4-941184/7*I06*ig2*ig4+5/32*ig2*ig6-40252890415104/35*I06*I03^4*ig2+41278242816*I18*ig2+39909851136/35*I03^6*ig2-84467515392*I09^2*ig2-1362182012928*J18*ig2-133211004862464/7*I09*I06*I03*ig2-184032165888/35*I09*I03^3*ig2+1349569216512*J15*I03*ig2+18162426839040/7*J12*I06*ig2+176508823928832/7*J09*I06*I03*ig2+280539168768*J09*I09*ig2+89818398720*J09^2*ig2-94595973120/7*J12*I03^2*ig2-72236924928*I15*I03*ig2-6135542974513152/7*I06^2*I03^2*ig2+54249517838499840/7*I06^3*ig2+5250936471552/35*I12*I03^2*ig2-124747776*J09*I03*ig4-5566277615616*I03^8-20063647665487872*I03^6*I06-2103572012316858777600*I06^4-1218866595678388224*I03^2*I06*I12+3165096777791569920*I03*I06^2*I09-20542695432781824*I12^2-17863437628867608576*I03^4*I06^2-676302730297344*I03^4*I12-9890927430598656*I03*I09*I12-162813620256768*I03^5*I09+15562007616946176*I03^2*J09^2+13147325076980367360*I06^2*I12+390037310617084231680*I03^2*I06^3-1190574598127616*I03^2*I09^2-293430847107760128*I03^3*I06*I09;

    /* 2, 3, 5, 7, 11, 13, 47, 367 invertible */

    ig10 := 2223358534741/9518167985356800*ig2^5-2223358534741/158636133089280*ig2^3*ig4+1436518121472/29425*I06^2*ig2^3+534361536/12845*J12*ig2^3+1630455975584/2474789625*I09*I03*ig2^3+7899136427222272/289550386125*I03^4*ig2^3+878527848004/6358275*J09*I03*ig2^3-124930836224/3089625*I06*I03^2*ig2^3+58061611684898849/1363343021040*I06*ig2^2*ig4+2223358534741/44065592524800*ig2^2*ig6+2223358534741/11016398131200*ig2*ig4^2+10780148377124912761223477255072219136/18687781624661145621625*I06^2*I03^2*ig2^2+7045415026991095255198101504/614730851769125*I09*I06*I03*ig2^2-74279215071934194880512/2936187307625*I18*ig2^2+41687898087360053943296/87460898525*J09^2*ig2^2+10756900454683962518528/225860562125*I09^2*ig2^2-2852380525817338079232/75539839375*J09*I03^3*ig2^2+689975176085823856853745664/248965994966495625*I03^6*ig2^2+720574836643825533762965798696704/64688474854596273305625*I09*I03^3*ig2^2-562552982622555565211487721726449205248/18687781624661145621625*I06^3*ig2^2+32852444012923033495036369554225152/13348415446186532586875*I06*I03^4*ig2^2-6193162043034609281493844992/33810196847301875*I12*I03^2*ig2^2-2343986616782355456/3018575*J15*I03*ig2^2+109782240580418265944064/143729448625*J18*ig2^2-550415865927794688/603715*J12*I06*ig2^2-3514111392016/706475*J09*I03*ig2*ig4-19237015296/12845*J12*ig2*ig4+174184835054696547/227223836840*I06*ig2*ig6-464254642873915703/511253632890000*I03^2*ig4^2-58061611684898849/28402979605*I06*ig4^2-2223358534741/1836066355200*ig4*ig6-88765974274724354422996992/120863743*J09^2*I06*ig2-177531948549448708845993984/77392315*J09*I09*I06*ig2-4258581306001079213588742144/3550372450625*I18*I03^2*ig2-9586725221670230277683675136/28402979605*I18*I06*ig2-1024382928509071267526887866368/14490084363129375*I03^8*ig2+6375060293580446260208392470528/2600784372869375*I09^2*I03^2*ig2+1509021562670314025190948864/2184844585*I09^2*I06*ig2+28760175665010690833051025408/2582089055*J18*I06*ig2-26585362081996638646503034847232/379889852216875*I06*I03^6*ig2-33629654278884321967982632671117312/106369158620725*I12*I06^2*ig2-12657449992836540995944316928/322761131875*J15*I03^3*ig2-76693801773361842221469401088/3614924677*J12*I06^2*ig2+752597226887763453286964070772113408/9466855117244525*I09*I06^2*I03*ig2+12775743918003237640766226432/322761131875*J18*I03^2*ig2+2396681305417557569420918784/4057568515*I15*I06*I03*ig2-1246339956684342951936/91658875*I12*I09*I03*ig2+1064645326500269803397185536/507196064375*I15*I03^3*ig2-749918395264562700297770631168/92125876968125*J09*I09*I03^2*ig2-39431308388898881607303168/15107967875*J09^2*I03^2*ig2+1761195929764477429725278812766208/2659228965518125*J09*I06*I03^3*ig2+564515916243387937837484806766592/8182242970825*J09*I06^2*I03*ig2-146232640809743218315759924455407616/75977970443375*I06^3*I03^2*ig2+114882470575501868265084031057526784/3039118817735*I06^4*ig2-1571814894148814874482603279253504/236671377931113125*I12*I03^4*ig2-578797178051943358923979867815936/204556074270625*I12*I06*I03^2*ig2+4545804648465866595489079885824/2288891469353125*J09*I03^5*ig2-28493877742186517769782034432/2582089055*J15*I06*I03*ig2+557689671031176098101873542168576/2659228965518125*I09*I06*I03^3*ig2-579830403338432704717160131124527104/33810196847301875*I06^2*I03^4*ig2-469509589506378589185290374742016/1183356889655565625*I09*I03^5*ig2+177440887750044967232864256/451865584625*J12*I03^4*ig2+1220170006271062742632759296/34758891125*J12*I06*I03^2*ig2-45071800921073997338698448896/912875314877150625*I03^6*ig4-10274923716872275078585120073728/616080712900916888625*I09*I03^3*ig4-169089960647786286124754436096/614730851769125*I09*I06*I03*ig4-2632953216296989768149476087255482368/93438908123305728108125*I06*I03^4*ig4+13501271582941333565075705321434780925952/18687781624661145621625*I06^3*ig4+56255678802776530944/3018575*J15*I03*ig4-264950093821243112257354394881149370368/18687781624661145621625*I06^2*I03^2*ig4+183839421825407252400822411264/33810196847301875*I12*I03^2*ig4-1000509554096641294639104/87460898525*J09^2*ig4-2634773773930038382657536/143729448625*J18*ig4+1782701161726420677132288/2936187307625*I18*ig4-258165610912415100444672/225860562125*I09^2*ig4+13209980782267072512/603715*J12*I06*ig4-26087295609344/91658875*I09*I03*ig6+21084668352096/706475*J09*I03*ig6-126386182835556352/10724088375*I03^4*ig6+115422091776/12845*J12*ig6+17990040416256/1029875*I06*I03^2*ig6-620575828475904/29425*I06^2*ig6+464254642873915703/42604469407500*I03^2*ig8+19264268539272572807675904/202475*J15*I03^5+2661244369698966591485509632/21130025*I03^2*I12*J12-1035962728565232367684288512/3532375*I03^2*I15*J09-74344109179726638659536467001344/316204786975*I03*I09^2*J09+3285920681096835706749475356672/9680825*I06^2*I09*J09-180029436045884866990964736/321125*I03^2*J09*J15-5683014378567001561532052013056/4281302725*I03*I06*I09*J12-37665729992569935981189921767424/274690325*I03*I06*I12*J09-1171884562832879642598278302474960896/20553311153375*I03^2*I06*I09*J09-310431356914305314930541761396736/3552862775*I03*I06^2*I15+157799350522404377985024/12845*I03*J12*J15+9438610754153949954048/25*I06*I09*I15+20133813622887734575104/25*I06*I09*J15+899609691819380950660439370903846912/193201124841725*I03*I06*I09*I12+682925205661696124780544/175*I06*J09*J15-100517481444166158186971136/90475*I09*I12*J09+108832714952323580249499110580217900173361152/3737556324932229124325*I12*I06*I03^4+110016195398265301106688/175*I06*I15*J09+4620335235525261656064/7*I03*I06*J21+2112669666229280031199199232/6640865*I03*I12*I15-77193921168800961527808/12845*I03*I15*J12-50859112327790853095424/7*I03*I06*I21+1402668410700169099865694928896/3058073375*I03*J09*J18-8075032903645283214234927378743468293619712/1988061874963951661875*I03^5*I06*J09+37056119795475157467574513006804992/13079379824875*I03^4*I06*J12-7217002418261663433210986918673905614848/152927836535688589375*I03^4*I09*J09-1397119709982646018664930419566871416907235328/397612374992790332375*I03^3*I06^2*J09+164865438233892559507616622968832/17764313875*I03^3*I06*I15+25227548901595981852478900501741568/99616806664375*I03^3*I09*I12+19562938660616422935563492917248/1006106140375*I03^3*I09*J12-773363172002526223896399279393079296/719365890368125*I03^3*I12*J09-958087687610163712115583943365306180270292992/18687781624661145621625*I03^2*I06^2*I12-212343971919389654341561545129984/2260912675*I03^2*I06^2*J12+71091942901931513958790296990879961841664/1773179158625875*I03*I06^3*I09-572335523739457829853248618496/39754953875*I03*I18*J09+14880441392476347319713792/25025*I03^2*I06*I18+137812639066840114498707363201024/1581023934875*I03^2*I09*I15+1983801139596452022976512/77875*I03^2*I09*J15-40579516423301234688/5*J15^2-254859700230503174422811652801604435065176064/4610265812427275*I06^5+2958148142320582656/5*I15^2-103515703205790721802506018328936448/259003697327375*I03^8*I06-7123812482740371560040942570307584/1773179158625875*I03^7*I09+5731901898131191223918557636067328/719365890368125*I03^7*J09+25089083913966785622742413606912/13079379824875*I03^6*J12+303645521857075564731264248315904/20553311153375*I03^5*I15+88071856973695609155330666135552/136398396817375*I03^4*I09^2+117054767328057324087150603225582268116369408/23051329062136375*I03^2*I06^4-215174732817311238979584/2275*I03^4*J18+642758114874595737600/7*I03^3*I21-99497657681345249280/7*I03^3*J21+7622570426960698031845631066112/8340957625*I03^2*I12^2-3186360656502823556481024/449575*I03^2*J12^2+270600632222122840405200775151616/87460898525*I03*J09^3+441643627975914000340111054012955896143081897984/2669683089237306517375*I06^3*I12+20192589936818761097095963213824/9620905*I06^3*J12-279460539531947530954098081792/18331775*I06^2*I09^2+279052509154305333785383397228544/238313075*I06^2*J09^2-775817717602354662416383475712/47662615*I06^2*I18-34697567510664049799718764544/333305*I06^2*J18+1394102882308774984487552107413504/142014898025*I06*I12^2-49487336059967424197296128/89915*I06*J12^2+660247497264375162067746816/91658875*I09^2*I12-603128972863044845568/367*I09^2*J12-121667300075774717980003270656/34044725*I12*J09^2-69326602928126775263232/2569*J09^2*J12+2215567744454098944*I09*J21-12287048225275282861225672704/1191565375*I12*I18+799878736793156093302800384/8332625*I12*J18-364886964682786603008/5*I15*J15+3304890581052221816832/367*I18*J12+204879149116277391360/7*I21*J09+10380908758699081728/7*J09*J21-22714907438104751112192/12845*J12*J18-43758597463167033115627690895300743591354171392/397612374992790332375*I03*I06^3*J09;

    return [ig2, ig4, ig6, ig8, ig10];

end function;

/*
 * Invariant stuff for quartics with at least a cusp
 ******************************************************/

 /* Up to some linear change of variables, quartics with a node
    can be rewritten modulo p as

    f := a20*x^2*z^2 +
        a03*y^3*z +
        a04*y^4+a13*x*y^3+a22*x^2*y^2+a31*x^3*y+a40*x^4;

    Herea a03 and a20 are assumed to be non-zero.

    The subgroup of GL(3) that stabilize them corresponds to x,y,z diagonal scaling
    and permutations of x,y,z

    Invariants for this action are generated by

    l3, l6, l9, m9, l12, l15 := Explode(
    [
    a04*a20^2,
    a03^2*a20^3*a22,
    a03^2*a13^2*a20^5,
    a03^4*a20^4*a40,
    a03^4*a13*a20^6*a31,
    a03^6*a20^7*a31^2
    ]
    );

    We call these invariants "Cusp Dihedral Invariants".

    And relations are
	 [
            -l12^2 + l15*l9
	];


*/

/* Retreive so-called Cusp Dihedral Invariants from Dixmier-Ohno invariants */
function CuspDihedInvsFromDO(DO)

    I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,_ := Explode(DO);

    l3 := 12*I03;

    l6 := 20736*I06;

    l9 := -8192/9*I03^3-350208*I03*I06+512*I09+6656*J09;

    m9 := -4096/9*I03^3+350208*I03*I06-45568/5*J09+22016/5*I09;

    l12 := 1441792/105*I03^4+364511232/35*I03^2*I06-6593052672/35*I06^2+3293184/175*I03*I09-51412992/175*I03*J09+3981312/35*J12;

    l15 := 2^19 * 3^3 / 5^4 / 7 * (3040*I03^5+1392660*I03^3*I06-9*I03^2*I09-20043*I03^2*J09+131062860*I03*I06^2-7290*I03*J12+456435*I06*I09-2639385*I06*J09+45360*I15);

    return
        [l3, l6, l9, m9, l12, l15],
        [ w div 3 : w in [3, 6, 9, 9, 12, 15]];

end function;

/* Retreive Dixmier-Ohno invariants from so-called Cusp Dihedral Invariants
   (the easy way)  */
function DOFromCuspDihedInvs(DH)

    l3, l6, l9, m9, l12, l15 := Explode(DH);

    I03 := 1/12*l3;

    I06 := 1/20736*l6;

    I09 := 1/5184*l3^3 + 19/186624*l3*l6 + 89/331776*l9 + 65/331776*m9;

    J09 := 1/15552*l3^3 + 19/93312*l3*l6 + 43/331776*l9 - 5/331776*m9;

    I12 := 25/8957952*l3^2*l6 + 5/6718464*l6^2 + 1/248832*l3*l9 - 5/995328*l3*m9;

    J12 := 1/186624*l3^4 + 79/6718464*l3^2*l6 + 23/5971968*l6^2 + 289/11943936*l3*l9 - 71/11943936*l3*m9 + 35/3981312*l12;

    I15 := 1/80621568*l3^3*l6 + 35/2579890176*l3*l6^2 + 23/31850496*l3^2*l9 + 119/509607936*l6*l9 - 1/7962624*l3^2*m9 - 35/254803968*l6*m9 + 5/42467328*l3*l12 + 125/18345885696*l15;

    J15 := 1/26873856*l3^3*l6 + 5/95551488*l3*l6^2 + 7/95551488*l3^2*l9 + 19/169869312*l6*l9 + 1/23887872*l3^2*m9 + 5/84934656*l6*m9 + 5/127401984*l3*l12 - 125/2038431744*l15;

    I18 := -5/967458816*l3^4*l6 - 2819/557256278016*l3^2*l6^2 - 35/46438023168*l6^3
        + 95/1719926784*l3^3*l9 + 22271/495338913792*l3*l6*l9 + 17/1528823808*l9^2 +
        53/1719926784*l3^3*m9 + 2465/123834728448*l3*l6*m9 - 125/6115295232*l9*m9 +
        25/3057647616*m9^2 + 5/2293235712*l3^2*l12 + 275/82556485632*l6*l12 -
        125/220150628352*l3*l15;

    J18 := 5/967458816*l3^4*l6 + 2023/185752092672*l3^2*l6^2 + 5/5159780352*l6^3 +
        5/573308928*l3^3*l9 + 3373/165112971264*l3*l6*l9 + 19/4586471424*l9^2 -
        1/573308928*l3^3*m9 - 65/41278242816*l3*l6*m9 - 55/18345885696*l9*m9 -
        25/9172942848*m9^2 + 5/2293235712*l3^2*l12 + 25/27518828544*l6*l12 -
        125/24461180928*l3*l15;

    I21 := 49/417942208512*l3^5*l6 + 161/835884417024*l3^3*l6^2 +
        133/6687075336192*l3*l6^3 + 325/371504185344*l3^4*l9 +
        8347/5944066965504*l3^2*l6*l9 + 121/7925422620672*l6^2*l9 +
        3025/7925422620672*l3*l9^2 - 7/46438023168*l3^4*m9 - 7/30958682112*l3^2*l6*m9 -
        11/247669456896*l3*l9*m9 - 7/990677827584*l3*m9^2 + 329/495338913792*l3^3*l12 +
        2933/2972033482752*l3*l6*l12 + 121/1320903770112*l9*l12 +
        385/5283615080448*m9*l12 + 1225/7925422620672*l3^2*l15 +
        23275/95105071448064*l6*l15;

    J21 := 35/23219011584*l3^5*l6 + 11651/3343537668096*l3^3*l6^2 +
        14159/6687075336192*l3*l6^3 + 1427/123834728448*l3^4*l9 +
        110077/5944066965504*l3^2*l6*l9 + 42965/23776267862016*l6^2*l9 +
        10109/1320903770112*l3*l9^2 - 19/30958682112*l3^4*m9 +
        209/2972033482752*l3^2*l6*m9 + 3427/2972033482752*l6^2*m9 +
        223/330225942528*l3*l9*m9 - 13/82556485632*l3*m9^2 + 1333/165112971264*l3^3*l12
        + 389/27518828544*l3*l6*l12 + 1441/293534171136*l9*l12 - 35/293534171136*m9*l12
        + 3115/2641807540224*l3^2*l15 + 74375/31701690482688*l6*l15;

    I27 := 0;

    return
        [I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27],
        [ 1, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 9 ];

end function;


/* Retreive Igusa invariants of the genus 2 component of the reduced quartic
   from so-called Cusp Dihedral Invariants.

   We assume that 32*I03^3-14580*I03*I06-261*I09+495*J09 <> 0.
*/
function IgusaFromCuspDihedInvs(DH)

    l3, l6, l9, m9, l12, l15 := Explode(DH);

    i2 := 1/2^9*(8*l3*l6-3*l9-30*m9);

    i4 := 1/2^21*(-64*l3^3*m9+16*l3^2*l6^2+16*l12*l3^2-16*l3*l6*l9-328*l3*l6*m9+16*l6^3-60*l12*l6+100*l15*l3+3*l9^2+168*l9*m9+165*m9^2);

    i6 := 1/2^31*(64*l12*l3^3*l6-64*l15*l3^4-1024*l3^3*m9^2-16*l3^2*l6^2*l9+256*l3^2*l6^2*m9-16*l12*l3^2*l9+656*l12*l3^2*m9+48*l12*l3*l6^2-160*l15*l3^2*l6+8*l3*l6*l9^2-392*l3*l6*l9*m9+896*l3*l6*m9^2+256*l6^3*m9+4320*l12^2*l3-12*l12*l6*l9-660*l12*l6*m9-4300*l15*l3*l9-400*l15*l3*m9-100*l15*l6^2-l9^3+78*l9^2*m9+159*l9*m9^2+80*m9^3+250*l12*l15);

    i8 := (i2*i6-i4^2) / 4;

    i10 := 1/2^55/5^4*(-1289945088*l12^2*l3^7+1289945088*l15*l3^7*l9-40960000*l3^6*m9^3+20480000*l3^5*l6^2*m9^2-2560000*l3^4*l6^4*m9-2737152000*l12^2*l3^5*l6+30720000*l12*l3^5*m9^2+12800000*l12*l3^4*l6^2*m9+2737152000*l15*l3^5*l6*l9-23040000*l15*l3^5*l6*m9+640000*l15*l3^4*l6^3-23040000*l3^4*l6*l9*m9^2-92160000*l3^4*l6*m9^3+640000*l3^3*l6^3*l9*m9+43520000*l3^3*l6^3*m9^2-5120000*l3^2*l6^5*m9+128244142080*l12^2*l3^4*l9-1099008000*l12^2*l3^4*m9-1589760000*l12^2*l3^3*l6^2-2880000*l12*l15*l3^4*l6-2880000*l12*l3^3*l6*l9*m9+57600000*l12*l3^3*l6*m9^2+24960000*l12*l3^2*l6^3*m9+4320000*l15^2*l3^5-128244142080*l15*l3^4*l9^2+1099968000*l15*l3^4*l9*m9+1920000*l15*l3^4*m9^2+1589600000*l15*l3^3*l6^2*l9-48160000*l15*l3^3*l6^2*m9+1280000*l15*l3^2*l6^4+4320000*l3^3*l9^2*m9^2+86400000*l3^3*l9*m9^3-34560000*l3^3*m9^4-82080000*l3^2*l6^2*l9*m9^2-43200000*l3^2*l6^2*m9^3+5760000*l3*l6^4*l9*m9+23040000*l3*l6^4*m9^2-2560000*l6^6*m9+17356032000*l12^3*l3^3-1570752000*l12^2*l3^2*l6*l9-3343680000*l12^2*l3^2*l6*m9-69120000*l12^2*l3*l6^3-17355392000*l12*l15*l3^3*l9+1200000*l12*l15*l3^3*m9-5600000*l12*l15*l3^2*l6^2-58320000*l12*l3^2*l9*m9^2+116640000*l12*l3^2*m9^3-28080000*l12*l3*l6^2*l9*m9-8640000*l12*l3*l6^2*m9^2+17280000*l12*l6^4*m9+9000000*l15^2*l3^3*l6+1570752000*l15*l3^2*l6*l9^2+3389040000*l15*l3^2*l6*l9*m9-16200000*l15*l3^2*l6*m9^2+67680000*l15*l3*l6^3*l9-26400000*l15*l3*l6^3*m9+640000*l15*l6^5+48600000*l3*l6*l9^2*m9^2+9720000*l3*l6*l9*m9^3-38880000*l3*l6*m9^4-1080000*l6^3*l9^2*m9-21600000*l6^3*l9*m9^2+8640000*l6^3*m9^3+1425600000*l12^2*l15*l3^2-18662400*l12^2*l3*l9^2-58320000*l12^2*l3*l9*m9-291600000*l12^2*l3*m9^2+6300000*l12*l15*l3*l6*l9+49500000*l12*l15*l3*l6*m9-4000000*l12*l15*l6^3+4860000*l12*l6*l9^2*m9+53460000*l12*l6*l9*m9^2+48600000*l12*l6*m9^3-1433850000*l15^2*l3^2*l9+3750000*l15^2*l3^2*m9+5000000*l15^2*l3*l6^2+18662400*l15*l3*l9^3+56700000*l15*l3*l9^2*m9+222750000*l15*l3*l9*m9^2+20250000*l15*l3*m9^3+270000*l15*l6^2*l9^2-24300000*l15*l6^2*l9*m9-27000000*l15*l6^2*m9^2-7290000*l9^3*m9^2-21870000*l9^2*m9^3-21870000*l9*m9^4-7290000*m9^5-9375000*l12*l15^2*l3-1080000*l12*l15*l9^2-3375000*l12*l15*l9*m9-16875000*l12*l15*m9^2+5625000*l15^2*l6*l9+14062500*l15^2*l6*m9-1953125*l15^3);

    return [i2, i4, i6, i8, i10], [1, 2, 3, 4, 5];

end function;


/* Retreive invariants of the genus 1 component of the reduced quartic
   from Dixmier-Ohno Invariants.

   We assume that up to some change of variable, f can be written in (2e) form :

            a00*p^6*Z^4 +
            a10*p^4*X*Z^3 +  a01*p^3*Y*Z^3 +
            (a20*p^2*X^2 +  a11*p*X*Y +  a02*Y^2)*Z^2+
            ( a03*Y^3 + a12*X*Y^2 + a21*X^2*Y +  a30*X^3)*Z+
            a40*X^4  + a31*X^3*Y + a22*X^2*Y^2 + a13*X*Y^3  + a04*Y^4,

   with a02, a30 <> 0.

*/
function Genus1FromCuspDO(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);


    q2 := -1575/128 * /* a02^6*a30^4/p^4 * */
    (8*I03^4+14418*I03^2*I06+117*I03*I09-423*I03*J09-155520*I06^2+486*I12) /
        (7945600*I03^6+3618470880*I03^4*I06-264024*I03^3*I09-52098408*I03^3*J09+300885885360*I03^2*I06^2-18720720*I03^2*J12+668376360*I03*I06*I09-5369493240*I03*I06*J09+251690457600*I06^3+117573120*I03*I15-94478400*I06*J12-1584765*I09^2+9009630*I09*J09-11858805*J09^2);

    q3 := -125/8192 * /*a02^9*a30^6/p^6 * */
    (62720*I03^6+36764280*I03^4*I06+266481*I03^3*I09-1527453*I03^3*J09+7357573440*I03^2*I06^2+6206220*I03^2*I12-400950*I03^2*J12-289325520*I03*I06*I09-247160160*I03*I06*J09-135992908800*I06^3-2143260*I03*I15+40041540*I03*J15+1143538560*I06*I12+76982400*I06*J12-2506140*I09^2+8323560*I09*J09+2664900*J09^2+1224720*I18-40415760*J18) /
        (2432762880*I03^9+2330332600320*I03^7*I06+832746752*I03^6*I09-43548359296*I03^6*J09+655598260365120*I03^5*I06^2-3362186880*I03^5*J12+715633172640*I03^4*I06*I09-23065364278080*I03^4*I06*J09+45457393716619200*I03^3*I06^3+35644561920*I03^4*I15-1357764832800*I03^3*I06*J12-269656380*I03^3*I09^2-6301768320*I03^3*I09*J09+192057820380*I03^3*J09^2+175488058148400*I03^2*I06^2*I09-1976479284646800*I03^2*I06^2*J09-183560911827840000*I03*I06^4+17144176435200*I03^2*I06*I15+162275400*I03^2*I09*J12+31303405800*I03^2*J09*J12+60323513616000*I03*I06^2*J12-33293065500*I03*I06*I09^2-3539531633400*I03*I06*I09*J09+20991076265700*I03*I06*J09^2-515188825632000*I06^3*I09+3767834493792000*I06^3*J09+8454067200*I03*I09*I15-378361497600*I03*I15*J09-71833817088000*I06^2*I15+156597948000*I06*I09*J12-1178381844000*I06*J09*J12-48152475*I09^3+1480848075*I09^2*J09-5203571625*I09*J09^2+4853279025*J09^3+22674816000*I15*J12);

    d6 := (4*q2^3 - q3^2) / 27;

    return [q2, q3, d6], [2, 3, 6];

end function;

/*
 * Invariant stuff for quartics with at least a cusp and a03=a30=0
 ******************************************************************/

 /* Up to some linear change of variables, quartics in this sublocus of quartics with cusps
    can be rewritten modulo p as

    f :=
         a20*x^2*z^2 +
         a12*x*y^2*z +
         a04*y^4+a13*x*y^3+a22*x^2*y^2+a31*x^3*y+a40*x^4;

    Invariants for this action are generated by

    n3, o3 := Explode(
    [
    a04*a20^2,
    a12^2*a20
    ]
    );

    We call these invariants "Zero-Cusp Dihedral Invariants".

*/

/* Equations for the locus of such quartics (aka A3STratum)

Dimension 1 (vs 3 !)
*/
function CuspZeroStratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return
        [
        I27,
        22275*J21 - 106531200*I09*I06^2 - 11813526000*I06^3*I03 - 10606545*I09*I06*I03^2 +
        342211050*I06^2*I03^3 - 27528*I09*I03^4 + 5427800*I06*I03^5 + 9176*I03^7,
        4455*I21 + 194400*I09*I06^2 - 205254000*I06^3*I03 - 129600*I09*I06*I03^2 +
        3160800*I06^2*I03^3 - 384*I09*I03^4 + 64960*I06*I03^5 + 128*I03^7,
        2475*J18 + 14256000*I06^3 - 91170*I09*I06*I03 + 3731625*I06^2*I03^2 - 204*I09*I03^3 +
        41620*I06*I03^4 + 68*I03^6,
        27*I18 + 1296000*I06^3 - 2250*I09*I06*I03 + 126225*I06^2*I03^2 - 12*I09*I03^3 +
        1540*I06*I03^4 + 4*I03^6,
        81*I09^2 + 19602000*I06^3 - 24030*I09*I06*I03 + 1455525*I06^2*I03^2 - 87*I09*I03^3 +
        14720*I06*I03^4 + 20*I03^6,
        825*J15 - 8505*I09*I06 + 184950*I06^2*I03 - 24*I09*I03^2 + 840*I06*I03^3 + 8*I03^5,
        297*I15 - 6075*I09*I06 + 195750*I06^2*I03 - 120*I09*I03^2 + 5800*I06*I03^3 + 40*I03^5,
        33*J12 - 99000*I06^2 - 35*I09*I03 - 400*I06*I03^2 + 8*I03^4,
        165*I12 - 52800*I06^2 - 36*I09*I03 + 665*I06*I03^2 + 12*I03^4,
        495*J09 - 261*I09 - 14580*I06*I03 + 32*I03^3
        ],
        [ w div 3 : w in [27, 21, 21, 18, 18, 18, 15, 15, 12, 12, 9]];

end function;

/* Retreive Dixmier-Ohno invariants from so-called Zero-Cusp Dihedral Invariants
   (the easy way)  */
function DOFromCuspZeroDihedInvs(DH)

    n3, o3 := Explode(DH);

    I03 := 1/12*n3 + 1/72*o3;

    I06 := 1/31104*n3*o3 - 1/746496*o3^2;

    I09 := 1/5184*n3^3 + 359/559872*n3^2*o3 + 479/8957952*n3*o3^2 + 7/13436928*o3^3;

    J09 := 1/15552*n3^3 + 223/559872*n3^2*o3 + 313/8957952*n3*o3^2 - 1/2239488*o3^3;

    I12 := 121/13436928*n3^3*o3 + 2321/967458816*n3^2*o3^2 + 193/2902376448*n3*o3^3 + 17/34828517376*o3^4;

    J12 := 1/186624*n3^4 + 1097/20155392*n3^3*o3 + 15589/967458816*n3^2*o3^2 + 767/1934917632*n3*o3^3 + 7/7739670528*o3^4;

    I15 := 625/483729408*n3^4*o3 + 3125/3869835264*n3^3*o3^2 +
        55625/835884417024*n3^2*o3^3 + 34375/20061226008576*n3*o3^4 +
        625/60183678025728*o3^5;

    J15 := 25/161243136*n3^4*o3 + 875/3869835264*n3^3*o3^2 + 1075/92876046336*n3^2*o3^3 - 125/743008370688*n3*o3^4 - 25/2229025112064*o3^5;

    I18 := 275/2902376448*n3^5*o3 + 174775/1253826625536*n3^4*o3^2 +
        19775/835884417024*n3^3*o3^3 + 819275/722204136308736*n3^2*o3^4 +
        3275/180551034077184*n3*o3^5 + 775/8666449635704832*o3^6;

    J18 := 55/2902376448*n3^5*o3 + 22285/417942208512*n3^4*o3^2 +
        8005/835884417024*n3^3*o3^3 + 56585/240734712102912*n3^2*o3^4 -
        85/15045919506432*n3*o3^5 - 35/320979616137216*o3^6;

    I21 := 1/612220032*n3^6*o3 + 251/58773123072*n3^5*o3^2 +
        34385/22568879259648*n3^4*o3^3 + 26965/180551034077184*n3^3*o3^4 +
        2045/4333224817852416*n3^2*o3^5 - 17/11555266180939776*n3*o3^6 -
        1/207994791256915968*o3^7;

    J21 := 499/23219011584*n3^6*o3 + 975919/15045919506432*n3^5*o3^2 +
        3106025/120367356051456*n3^4*o3^3 + 2085125/962938848411648*n3^3*o3^4 -
        1985/361102068154368*n3^2*o3^5 + 101/722204136308736*n3*o3^6 +
        1/2567836929097728*o3^7;

    I27 := 0;

    return
        [I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27],
        [ 1, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 9 ];

end function;

/* Retreive so-called Zero-Cusp Dihedral Invariants from Dixmier-Ohno invariants
 */
function CuspZeroDihedInvsFromDO(DO)

    K := Universe(DO); Po3 := PolynomialRing(K); o3 := Po3.1;

    I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,_ := Explode(DO);

    SYSo3 := [
        55*(I03^2-180*I06)*o3+2592*I03^3+1438560*I03*I06-7776*I09,
        29*(I03^2-180*I06)*o3+864*I03^3+987552*I03*I06-7776*J09
        ];

    for E in SYSo3 do
        if Degree(E, o3) eq 1 then
            _o3 := -Coefficient(E, 0)/Coefficient(E, 1);
            break;
        end if;
    end for;

    _n3 := 12*I03-1/6*_o3;

    return
        [_n3, _o3],
        [1, 1];

end function;




// Old routines
//-------------

/* Invariants for the genus 1 and genus 2 components in the reduction of a plane quartic with a cusp (deprecated) */
function G1G2InvariantsFromDOOld(DO)

    K := Universe(DO);

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);


    /* Genus 1
    **********/

    q2 := -1575/128 * /* a02^6*a30^4/p^4 * */
    (8*I03^4+14418*I03^2*I06+117*I03*I09-423*I03*J09-155520*I06^2+486*I12) /
        (7945600*I03^6+3618470880*I03^4*I06-264024*I03^3*I09-52098408*I03^3*J09+300885885360*I03^2*I06^2-18720720*I03^2*J12+668376360*I03*I06*I09-5369493240*I03*I06*J09+251690457600*I06^3+117573120*I03*I15-94478400*I06*J12-1584765*I09^2+9009630*I09*J09-11858805*J09^2);

    q3 := -125/8192 * /*a02^9*a30^6/p^6 * */
    (62720*I03^6+36764280*I03^4*I06+266481*I03^3*I09-1527453*I03^3*J09+7357573440*I03^2*I06^2+6206220*I03^2*I12-400950*I03^2*J12-289325520*I03*I06*I09-247160160*I03*I06*J09-135992908800*I06^3-2143260*I03*I15+40041540*I03*J15+1143538560*I06*I12+76982400*I06*J12-2506140*I09^2+8323560*I09*J09+2664900*J09^2+1224720*I18-40415760*J18) /
        (2432762880*I03^9+2330332600320*I03^7*I06+832746752*I03^6*I09-43548359296*I03^6*J09+655598260365120*I03^5*I06^2-3362186880*I03^5*J12+715633172640*I03^4*I06*I09-23065364278080*I03^4*I06*J09+45457393716619200*I03^3*I06^3+35644561920*I03^4*I15-1357764832800*I03^3*I06*J12-269656380*I03^3*I09^2-6301768320*I03^3*I09*J09+192057820380*I03^3*J09^2+175488058148400*I03^2*I06^2*I09-1976479284646800*I03^2*I06^2*J09-183560911827840000*I03*I06^4+17144176435200*I03^2*I06*I15+162275400*I03^2*I09*J12+31303405800*I03^2*J09*J12+60323513616000*I03*I06^2*J12-33293065500*I03*I06*I09^2-3539531633400*I03*I06*I09*J09+20991076265700*I03*I06*J09^2-515188825632000*I06^3*I09+3767834493792000*I06^3*J09+8454067200*I03*I09*I15-378361497600*I03*I15*J09-71833817088000*I06^2*I15+156597948000*I06*I09*J12-1178381844000*I06*J09*J12-48152475*I09^3+1480848075*I09^2*J09-5203571625*I09*J09^2+4853279025*J09^3+22674816000*I15*J12);

    d6 := (4*q2^3 - q3^2) / 27;

    /* Genus 2
    **********/

    i2 := 32*I03^3-14580*I03*I06-261*I09+495*J09;

    i4 := (3002000*I03^6+1336514580*I03^4*I06-464409*I03^3*I09-18843903*I03^3*J09+117482315760*I03^2*I06^2-7020270*I03^2*J12+417126510*I03*I06*I09-2329308090*I03*I06*J09+94383921600*I06^3+44089920*I03*I15-35429400*I06*J12+895860*I09^2-2273670*I09*J09+912870*J09^2) / 525;

    i6 :=
        (28216204160*I03^9+23581585974240*I03^7*I06-21069324936*I03^6*I09-408646796472*I03^6*J09+6037011557493840*I03^5*I06^2-42466466160*I03^5*J12-5480448046020*I03^4*I06*I09-200462231667060*I03^4*I06*J09+397830880584284400*I03^3*I06^3+413809093440*I03^4*I15-9951551589600*I03^3*I06*J12-686188260*I03^3*I09^2+122845775310*I03^3*I09*J09+1583027113410*I03^3*J09^2+489920382690300*I03^2*I06^2*I09-16730173359890100*I03^2*I06^2*J09-1910158641391680000*I03*I06^4+149478622646400*I03^2*I06*I15+70353931050*I03^2*I09*J12+186633221850*I03^2*J09*J12+630146599812000*I03*I06^2*J12-3280053852000*I03*I06*I09^2-10234384489800*I03*I06*I09*J09+174658828667400*I03*I06*J09^2-6140069492184000*I06^3*I09+39901325794344000*I06^3*J09-345932661600*I03*I09*I15-3012491023200*I03*I15*J09-727317398016000*I06^2*I15+1932319476000*I06*I09*J12-12588774408000*I06*J09*J12+467434800*I09^3-1445169600*I09^2*J09+1094593500*I09*J09^2-244433700*J09^3+229582512000*I15*J12)/118125;

    i8 := (i2*i6-i4^2) / 4;

    i10 :=
        (-24074171839938560*I03^15-1063677688079155200*I03^13*I06+196749351885643776*I03^12*I09+34857679187976192*I03^12*J09+17788649424269858795520*I03^11*I06^2-7436179772375040*I03^11*J12+170305342967625025536*I03^10*I06*I09-527239199777544603648*I03^10*I06*J09+9473459346697536495912960*I03^9*I06^3+2212009181969448960*I03^10*I15-60389900285622128640*I03^9*I06*J12-103891355135218944*I03^9*I09^2-2592275733841927680*I03^9*I09*J09+3265042649062070016*I03^9*J09^2+53010194810628308590080*I03^8*I06^2*I09-416710329944916109800960*I03^8*I06^2*J09+1682191479799092665396793600*I03^7*I06^4+2293145176516744642560*I03^8*I06*I15-319385734086804480*I03^8*I09*J12+1127160947822054400*I03^8*J09*J12-28901410555650973516800*I03^7*I06^2*J12-29433848152050967680*I03^7*I06*I09^2-1478203124668458888960*I03^7*I06*I09*J09+5415177268972359054720*I03^7*I06*J09^2+7092390937056646930041600*I03^6*I06^3*I09-94051896726020932473868800*I03^6*I06^3*J09+79955088428380498718079744000*I03^5*I06^5+1278283491000483840*I03^7*I09*I15-39475797366214287360*I03^7*I15*J09+733069439853150808166400*I03^6*I06^2*I15-77391741898070668800*I03^6*I06*I09*J12+912534347133167731200*I03^6*I06*J09*J12+12226143419016480*I03^6*I09^3+538563172352758560*I03^6*I09^2*J09+9639423782835452640*I03^6*I09*J09^2-18083062380700473120*I03^6*J09^3-2481617073250781526240000*I03^5*I06^3*J12-21631772834389317600*I03^5*I06^2*I09^2-244439204772133949040000*I03^5*I06^2*I09*J09+1719524779043857871580000*I03^5*I06^2*J09^2+370543229860968223231680000*I03^4*I06^4*I09-5156088637445728143128640000*I03^4*I06^4*J09-1497280045748888305612615680000*I03^3*I06^6-4481529977956147200*I03^6*I15*J12+777658837998638131200*I03^5*I06*I09*I15-23996761197622348492800*I03^5*I06*I15*J09+352247457555576000*I03^5*I09^2*J12+703395592414358400*I03^5*I09*J09*J12-6185792686959201600*I03^5*J09^2*J12+60221362772518373698560000*I03^4*I06^3*I15+8561649822680153880000*I03^4*I06^2*I09*J12+103119612401935353528000*I03^4*I06^2*J09*J12-14051252261588151600*I03^4*I06*I09^3+18917112454422782400*I03^4*I06*I09^2*J09+1990215931775346867600*I03^4*I06*I09*J09^2-10163701666365442812000*I03^4*I06*J09^3+199812690459107367068160000*I03^3*I06^4*J12-407445643833006900816000*I03^3*I06^3*I09^2-15780073137292074690720000*I03^3*I06^3*I09*J09+110614964821173143491248000*I03^3*I06^3*J09^2-13869489929149706648785920000*I03^2*I06^5*I09+92020813440141479814282240000*I03^2*I06^5*J09+38994033534653703802060800000*I03*I06^7+32540250914983526400*I03^5*I15^2-954183662380065024000*I03^4*I06*I15*J12-1574089886414995200*I03^4*I09^2*I15-8956459271625062400*I03^4*I09*I15*J09+183259701609428217600*I03^4*I15*J09^2+68768801726203703808000*I03^3*I06^2*I09*I15-2585167998627128025600000*I03^3*I06^2*I15*J09+61889349962995470000*I03^3*I06*I09^2*J12-221926105058463252000*I03^3*I06*I09*J09*J12-1059985898972783298000*I03^3*I06*J09^2*J12+13569437400525*I03^3*I09^4-26669098246597200*I03^3*I09^3*J09-264469716087749550*I03^3*I09^2*J09^2+1246016262711745800*I03^3*I09*J09^3-1310104020929545575*I03^3*J09^4-1640600704438232753848320000*I03^2*I06^4*I15+1323729085007912641920000*I03^2*I06^3*I09*J12-8849095258070359094400000*I03^2*I06^3*J09*J12-2306222653975132140000*I03^2*I06^2*I09^3+10333144682571095244000*I03^2*I06^2*I09^2*J09+161565453621340239132000*I03^2*I06^2*I09*J09^2-782893075790475612828000*I03^2*I06^2*J09^3-17398975342925972275200000*I03*I06^5*J12-42293569038128865619200000*I03*I06^4*I09^2+564953260878781349598720000*I03*I06^4*I09*J09-1872002282615789442428160000*I03*I06^4*J09^2+116565569120369487052800000*I06^6*I09-827530999517268733132800000*I06^6*J09+11301557066826227712000*I03^3*I06*I15^2+7032214277195328000*I03^3*I09*I15*J12+18466404151286592000*I03^3*I15*J09*J12+158509678567115427840000*I03^2*I06^2*I15*J12-515565370485627840000*I03^2*I06*I09^2*I15-1445329205212828032000*I03^2*I06*I09*I15*J09+27690181066783476288000*I03^2*I06*I15*J09^2-13154453760145500*I03^2*I09^3*J12+14869262937901500*I03^2*I09^2*J09*J12+71740266200167500*I03^2*I09*J09^2*J12-113793124505719500*I03^2*J09^3*J12-10115510765774268026880000*I03*I06^3*I09*I15+66891714399969520619520000*I03*I06^3*I15*J09+2028040199681931360000*I03*I06^2*I09^2*J12-28732704347687826240000*I03*I06^2*I09*J09*J12+97355804840016397920000*I03*I06^2*J09^2*J12+669190053349386000*I03*I06*I09^4+175808335550400000*I03*I06*I09^3*J09-47383381475503452000*I03*I06*I09^2*J09^2+157366743171969456000*I03*I06*I09*J09^3-144187710347415870000*I03*I06*J09^4+15692186322769792204800000*I06^5*I15-51189788628108288000000*I06^4*I09*J12+365269508685315072000000*I06^4*J09*J12-42527297954565236160000*I06^3*I09^3+855590062157009334720000*I06^3*I09^2*J09-5705724582621143887680000*I06^3*I09*J09^2+12589161859787218585920000*I06^3*J09^3-26437326220247040000*I03^2*I09*I15^2-242612454611939328000*I03^2*I15^2*J09-596755324213297643520000*I03*I06^2*I15^2+526867070128704000000*I03*I06*I09*I15*J12-3514491226678602240000*I03*I06*I15*J09*J12+71497657272096000*I03*I09^3*I15+425131253256096000*I03*I09^2*I15*J09-2286889309467936000*I03*I09*I15*J09^2+2482171888065120000*I03*I15*J09^3-6940988288557056000000*I06^3*I15*J12-15391962871925667840000*I06^2*I09^2*I15+204848166260392888320000*I06^2*I09*I15*J09-676315759786782105600000*I06^2*I15*J09^2-527351604020280000*I06*I09^3*J12+5694073895028600000*I06*I09^2*J09*J12-15988518147819240000*I06*I09*J09^2*J12+13842849173967720000*I06*J09^3*J12-195653428992000*I09^5+1103394337920000*I09^4*J09-2199778378560000*I09^3*J09^2+1889142847200000*I09^2*J09^3-729864535680000*I09*J09^4+104770876896000*J09^5+31491520938823680000*I03*I15^2*J12-1835505791862865920000*I06*I09*I15^2+12092744040508293120000*I06*I15^2*J09-65210616708480000*I09^2*I15*J12+245965520056320000*I09*I15*J09*J12-242246283361920000*I15*J09^2*J12-71980619288739840000*I15^3) / 262500000;

    return [ [q2, q3, d6], [i2, i4, i6, i8, i10] ], [ [2, 3, 6] , [1, 2, 3, 4, 5] ];

end function;


/*
 * Locus of quartics with three nodes
 *********************************/


/*
	Dimension 2
 */
function FourNodesStratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
        117907211074867200*I18^2 - 596905256066515200*I12^3 +
        54944760360888115200*I18*I12*I06 + 9669452473038784204800*I12^2*I06^2 -
        6263231052296945664000*I18*I06^3 - 6410492442641011802112000*I12*I06^4 +
        1352423254153233872977920000*I06^6 - 950366799854922240*I12^2*I09*I03 -
        20205243342834278400*I18*I09*I06*I03 -
        2445348871588950835200*I12*I09*I06^2*I03 +
        4596482566178979840000*I15*I06^3*I03 -
        4111425975375814717440000*J09*I06^4*I03 +
        2647676395512775839744000*I09*I06^4*I03 +
        646813528989626880*I18*I12*I03^2 + 652574389306238542080*I12^2*I06*I03^\
        2 + 4593667919355957657600*I18*I06^2*I03^2 -
        496233798056371860480000*J12*I06^3*I03^2 +
        1010355025854785674752000*I12*I06^3*I03^2 +
        1416857459384027080433664000*I06^5*I03^2 -
        1350366220125296640*I18*I09*I03^3 - 548329984602150159360*I12*I09*I06*I\
        03^3 - 29454157619939482214400*I15*I06^2*I03^3 +
        1051920614707942396262400*J09*I06^3*I03^3 +
        70653631303072972339200*I09*I06^3*I03^3 +
        5084209882812574080*I12^2*I03^4 - 1855323377249247682560*I18*I06*I03^4 +
        639462783539835494092800*J12*I06^2*I03^4 -
        1701439320002895662699520*I12*I06^2*I03^4 -
        1533548490811137883289088000*I06^4*I03^4 +
        22516507377864045504*I12*I09*I03^5 +
        11083494084833344849920*I15*I06*I03^5 +
        570292376869244768446080*J09*I06^2*I03^5 -
        625001268025819677813120*I09*I06^2*I03^5 -
        16953737505601071168*I18*I03^6 - 6608545148226629665440*J12*I06*I03^6 +
        213531089587599871728*I12*I06*I03^6 -
        16640500915415561703079680*I06^3*I03^6 + 13573922986039635072*I15*I03^7
        - 1009298959836255797112*J09*I06*I03^7 +
        3834773826350376448008*I09*I06*I03^7 + 7107490415168413236*J12*I03^8 -
        22727738435047181982*I12*I03^8 + 247523098472121542447664*I06^2*I03^8 +
        4161779905768068627*J09*I03^9 - 6036709288553102421*I09*I03^9 -
        657172382973704315130*I06*I03^10 + 760095282746980600*I03^12,
        393024036916224000*I18*I15 - 491569034407718400*I12^2*I09 +
        19903063616181043200*I18*I09*I06 + 6541078663224599961600*I12*I09*I06^2
        + 258071062503084687360000*I15*I06^3 -
        29026348566722106163200000*J09*I06^4 +
        9324492388876293931008000*I09*I06^4 - 74558971709107200*I18*I12*I03 +
        545813389216313164800*I12^2*I06*I03 +
        44580452836931356262400*I18*I06^2*I03 -
        13338810453959680296960000*J12*I06^3*I03 +
        35841876533051766130483200*I12*I06^3*I03 +
        32534731151125956724801536000*I06^5*I03 -
        1305151078807941120*I18*I09*I03^2 - 991074670662022571520*I12*I09*I06*I\
        03^2 - 258536139080780007014400*I15*I06^2*I03^2 -
        10693636827367493367705600*J09*I06^3*I03^2 +
        12699513957634493454028800*I09*I06^3*I03^2 +
        4974138078494437440*I12^2*I03^3 - 1369520260038758661120*I18*I06*I03^3 +
        728151394310931455308800*J12*I06^2*I03^3 -
        1577747539689225096476160*I12*I06^2*I03^3 -
        1085498358636468541272883200*I06^4*I03^3 +
        21037143844877783616*I12*I09*I03^4 +
        9997983731835892638720*I15*I06*I03^4 +
        547991246575695535246080*J09*I06^2*I03^4 -
        656897938354317704382720*I09*I06^2*I03^4 -
        15808038903975068352*I18*I03^5 - 6282634920359168917440*J12*I06*I03^5 +
        680392035073332536544*I12*I06*I03^5 -
        20415402622594888467471360*I06^3*I03^5 + 12722175886769177472*I15*I03^6
        - 1026403244433120763152*J09*I06*I03^6 +
        3688013836294863278256*I09*I06*I03^6 + 6597331856208548316*J12*I03^7 -
        21210575343230800602*I12*I03^7 + 243030364011127509449472*I06^2*I03^7 +
        3882867345652878297*J09*I03^8 - 5616693645382714527*I09*I03^8 -
        626736389258102286254*I06*I03^9 + 707764637142968552*I03^11,
        34678591492608000*I15^2 + 15484424583843129600*I12^2*I06 +
        349560202245488640000*I18*I06^2 - 76796236268830310400000*J12*I06^3 +
        211466355174887371776000*I12*I06^3 + 181423967169551450480640000*I06^5 -
        46907894786618880*I18*I09*I03 - 19325307482352829440*I12*I09*I06*I03 -
        2178763376444992512000*I15*I06^2*I03 -
        19596936953893178880000*J09*I06^3*I03 +
        59481958099666888396800*I09*I06^3*I03 + 137834970438004560*I12^2*I03^2 -
        56372182651300239360*I18*I06*I03^2 +
        20886039901824465024000*J12*I06^2*I03^2 -
        53620957966411598446080*I12*I06^2*I03^2 -
        47024505883464279090278400*I06^4*I03^2 +
        705947792189459904*I12*I09*I03^3 + 347793461120876520960*I15*I06*I03^3 +
        18078683169589695671040*J09*I06^2*I03^3 -
        20139157905824594269440*I09*I06^2*I03^3 - 531146675438805888*I18*I03^4 -
        211190338682493217920*J12*I06*I03^4 + 14694434756584106976*I12*I06*I03^4
        - 544534357812549272098560*I06^3*I03^4 + 405724433006870208*I15*I03^5 -
        34261020803869778448*J09*I06*I03^5 + 123764660775562229424*I09*I06*I03^5
        + 233672973270789924*J12*I03^6 - 705639226894684578*I12*I03^6 +
        7958158226344057053168*I06^2*I03^6 + 129877541229165993*J09*I03^7 -
        193851317824677063*I09*I03^7 - 21332627117486982486*I06*I03^8 +
        24222604330452808*I03^10,
        48164710406400*I18*J12 - 72247065609600*I18*I12 + 3034376755603200*I12^2*I06
        - 261031323864729600*I18*I06^2 + 27649540688587776000*J12*I06^3 -
        82807167662934220800*I12*I06^3 - 63464548768147021824000*I06^5 -
        42687155105280*I18*I09*I03 + 2451600425675520*I12*I09*I06*I03 +
        642625760338329600*I15*I06^2*I03 + 14933961781398374400*J09*I06^3*I03 -
        22200926584973875200*I09*I06^3*I03 + 59108015932560*I12^2*I03^2 -
        4894421989806720*I18*I06*I03^2 + 115694686230451200*J12*I06^2*I03^2 -
        1831581261062760960*I12*I06^2*I03^2 - 1274392217489390899200*I06^4*I03^2
        + 42386056223616*I12*I09*I03^3 + 17629473639697920*I15*I06*I03^3 +
        283504543763143680*J09*I06^2*I03^3 - 156263294379018240*I09*I06^2*I03^3
        - 25272179991072*I18*I03^4 - 12854036094723360*J12*I06*I03^4 +
        5516129320022304*I12*I06*I03^4 + 20747168812652163840*I06^3*I03^4 +
        10802328741792*I15*I03^5 - 4879982125386072*J09*I06*I03^5 +
        9538133063229576*I09*I06*I03^5 + 17530832687256*J12*I03^6 -
        28250820635562*I12*I03^6 + 401044800141920592*I06^2*I03^6 +
        4398069923415*J09*I03^7 - 10598233956093*I09*I03^7 -
        1741809750977254*I06*I03^8 + 1096199917512*I03^10,
        I27,
        577976524876800*I15*J12 - 214191300395520*I18*I09 -
        46913294567301120*I12*I09*I06 - 3762863040384000000*I15*I06^2 +
        196129299258385920000*J09*I06^3 - 57181646876001177600*I09*I06^3 -
        164468319946560*I12^2*I03 - 70719349881600000*I18*I06*I03 +
        38840902470748339200*J12*I06^2*I03 - 101122876332457228800*I12*I06^2*I03
        - 98417394942142381056000*I06^4*I03 + 447515157035520*I12*I09*I03^2 +
        593077779248371200*I15*I06*I03^2 + 32542586488538092800*J09*I06^2*I03^2
        - 38146533617331843840*I09*I06^2*I03^2 - 589698888266880*I18*I03^3 -
        532050653582951040*J12*I06*I03^3 + 448598299071795840*I12*I06*I03^3 -
        595778384054495577600*I06^3*I03^3 - 1235030328181440*I15*I03^4 -
        208097684074275120*J09*I06*I03^4 + 385060968529909200*I09*I06*I03^4 +
        1152486275289660*J12*I03^5 - 165351326875470*I12*I03^5 +
        20419759950938056800*I06^2*I03^5 + 109307215920591*J09*I03^6 -
        608275338600897*I09*I03^6 - 77522527833755130*I06*I03^7 +
        62559169399160*I03^9,
        288988262438400*I15*I12 - 71397100131840*I18*I09 -
        18636443061304320*I12*I09*I06 - 835978744258560000*I15*I06^2 +
        81424900602339840000*J09*I06^3 - 25188522747707289600*I09*I06^3 -
        54822773315520*I12^2*I03 - 84985200088750080*I18*I06*I03 +
        28894644471132288000*J12*I06^2*I03 - 77252106530354250240*I12*I06^2*I03
        - 71037042640228069171200*I06^4*I03 + 993215770610112*I12*I09*I03^2 +
        502347097409633280*I15*I06*I03^2 + 25956051685199205120*J09*I06^2*I03^2
        - 28434439564115109120*I09*I06^2*I03^2 - 752951599150464*I18*I03^3 -
        303681676801656960*J12*I06*I03^3 + 20884993905463488*I12*I06*I03^3 -
        740777927030483489280*I06^3*I03^3 + 556566445681344*I15*I03^4 -
        49793845007462544*J09*I06*I03^4 + 178274608730986032*I09*I06*I03^4 +
        342590177792772*J12*I03^5 - 996285063518514*I12*I03^5 +
        11407369144748469984*I06^2*I03^5 + 182726567723889*J09*I03^6 -
        278889044708799*I09*I03^6 - 30801522909942918*I06*I03^7 +
        34594487623304*I03^9,
        89193908160*I18*J09 - 36726903360*I18*I09 - 299987815680*I12*I09*I06 +
        62868698726400*I15*I06^2 - 5031451531008000*J09*I06^3 +
        1957517985024000*I09*I06^3 - 106245684720*I12^2*I03 +
        1345624358400*I18*I06*I03 - 1567054938124800*J12*I06^2*I03 +
        4183174464837120*I12*I06^2*I03 + 3945687769968537600*I06^4*I03 -
        76663552896*I12*I09*I03^2 - 28158448711680*I15*I06*I03^2 -
        1467060756629760*J09*I06^2*I03^2 + 1593415090103040*I09*I06^2*I03^2 +
        65281984992*I18*I03^3 + 20059796072160*J12*I06*I03^3 -
        7717787510976*I12*I06*I03^3 + 34942850265415680*I06^3*I03^3 -
        25333904736*I15*I03^4 + 4609707056568*J09*I06*I03^4 -
        12529856932776*I09*I06*I03^4 - 40944607704*J12*I03^5 +
        71738637390*I12*I03^5 - 702208216897488*I06^2*I03^5 -
        18601002693*J09*I03^6 + 32425023015*I09*I03^6 + 2760471631554*I06*I03^7
        - 4192162072*I03^9,
        15740101440*J12^2 - 35415228240*I12^2 + 587630453760*I18*I06 -
        201053562393600*J12*I06^2 + 307162832901120*I12*I06^2 +
        395040448844697600*I06^4 - 41850152064*I12*I09*I03 -
        459919918080*I15*I06*I03 - 290196805973760*J09*I06^2*I03 +
        177845411600640*I09*I06^2*I03 + 11446723008*I18*I03^2 -
        19885187352960*J12*I06*I03^2 + 51058967007456*I12*I06*I03^2 +
        58963815299773440*I06^3*I03^2 - 217047164544*I15*I03^3 -
        17369331206688*J09*I06*I03^3 + 19839562633440*I09*I06*I03^3 +
        108653584356*J12*I03^4 + 71998750422*I12*I03^4 +
        642554604085968*I06^2*I03^4 - 1070840727*J09*I03^5 -
        51247215207*I09*I03^5 - 5420874202366*I06*I03^6 + 4934444648*I03^8,
        141660912960*J12*I12 - 212491369440*I12^2 + 1762891361280*I18*I06 -
        365170353408000*J12*I06^2 + 601523716631040*I12*I06^2 +
        873406896032563200*I06^4 - 125550456192*I12*I09*I03 -
        5595775073280*I15*I06*I03 - 454256832395520*J09*I06^2*I03 +
        392174318995200*I09*I06^2*I03 + 34340169024*I18*I03^2 -
        5983509528000*J12*I06*I03^2 + 21314817487872*I12*I06*I03^2 +
        37033350525319680*I06^3*I03^2 - 121630045824*I15*I03^3 -
        7867640077056*J09*I06*I03^3 + 7701206626944*I09*I06*I03^3 +
        36145854396*J12*I03^4 + 82907972982*I12*I03^4 +
        210140292128256*I06^2*I03^4 - 11717847567*J09*I03^5 -
        8743281543*I09*I03^5 - 1824919355070*I06*I03^6 + 200204200*I03^8,
        755524869120*I15*J09 + 111062155760640*I18*I06 - 28155713568998400*J12*I06^2
        + 78598493353981440*I12*I06^2 + 66618526218635059200*I06^4 -
        1866590853120*I12*I09*I03 - 596747700541440*I15*I06*I03 -
        26933349775691520*J09*I06^2*I03 + 27852916445948160*I09*I06^2*I03 +
        963849741120*I18*I03^2 + 298452244014720*J12*I06*I03^2 +
        79615126276416*I12*I06*I03^2 + 804187935730368000*I06^3*I03^2 -
        1098379191168*I15*I03^3 + 13966940620512*J09*I06*I03^3 -
        150798793259808*I09*I06*I03^3 - 288352251540*J12*I03^4 +
        1606586119902*I12*I03^4 - 10287300216346272*I06^2*I03^4 -
        284282009091*J09*I03^5 + 322784586693*I09*I03^5 +
        26293305789114*I06*I03^6 - 43968833272*I03^8,
        755524869120*I15*I09 + 269722378275840*I18*I06 - 66379875340262400*J12*I06^2
        + 185681515493214720*I12*I06^2 + 156408063322342809600*I06^4 -
        3993171146496*I12*I09*I03 - 1338155957053440*I15*I06*I03 -
        62236557216610560*J09*I06^2*I03 + 64791825752989440*I09*I06^2*I03 +
        2422679378112*I18*I03^2 + 623392394866560*J12*I06*I03^2 +
        417261395342016*I12*I06*I03^2 + 2018412722028003840*I06^3*I03^2 -
        3879745091712*I15*I03^3 - 21535351456608*J09*I06*I03^3 -
        292628800128096*I09*I06*I03^3 - 30407419116*J12*I03^4 +
        3958898198562*I12*I03^4 - 22368335306601312*I06^2*I03^4 -
        594957445821*J09*I03^5 + 392263473915*I09*I03^5 +
        37042193318214*I06*I03^6 - 61269506312*I03^8,
        78700507200*J21 - 68747207760*I12*I09 + 18084097946880*I15*I06 -
        136350625017600*J09*I06^2 - 652397684037120*I09*I06^2 +
        14557021920*I18*I03 - 176244290380800*J12*I06*I03 +
        411095495122848*I12*I06*I03 + 368447664976151040*I06^3*I03 -
        1643397717024*I15*I03^2 - 122379639217344*J09*I06*I03^2 +
        153553235481360*I09*I06*I03^2 + 771662086992*J12*I03^3 +
        604912231278*I12*I03^3 + 5158006751951424*I06^2*I03^3 -
        20887586469*J09*I03^4 - 368016979761*I09*I03^4 -
        39415825207710*I06*I03^5 + 39252937640*I03^7,
        157401014400*I21 - 10184771520*I12*I09 + 2285151160320*I15*I06 +
        239979311712000*J09*I06^2 - 163148739667200*I09*I06^2 -
        4320812160*I18*I03 - 15440685393600*J12*I06*I03 +
        33352042743072*I12*I06*I03 + 22089994384872960*I06^3*I03 -
        121293982656*I15*I03^2 - 9524553124896*J09*I06*I03^2 +
        12078746015904*I09*I06*I03^2 + 50015849220*J12*I03^3 +
        41662281474*I12*I03^3 + 470481418443456*I06^2*I03^3 -
        577252017*J09*I03^4 - 22825866969*I09*I03^4 - 2770748500842*I06*I03^5 +
        2115444856*I03^7,
        47220304320*J12*J09 - 29165482080*I12*I09 + 788915635200*I15*I06 -
        263047582425600*J09*I06^2 + 57199923809280*I09*I06^2 -
        16665989760*I18*I03 - 27092328552000*J12*I06*I03 +
        59391875760480*I12*I06*I03 + 70417517931532800*I06^3*I03 -
        246219341760*I15*I03^2 - 22833657187920*J09*I06*I03^2 +
        26081263572624*I09*I06*I03^2 + 152809112412*J12*I03^3 +
        15208600662*I12*I03^3 + 887697787152960*I06^2*I03^3 +
        7960842909*J09*I03^4 - 77072274315*I09*I03^4 - 7385950391022*I06*I03^5 +
        7244463016*I03^7,
        145741680*I12*J09 - 60011280*I12*I09 - 391910400*I15*I06 -
        25136697600*J09*I06^2 + 15883257600*I09*I06^2 - 34292160*I18*I03 +
        4963032000*J12*I06*I03 - 21151614240*I12*I06*I03 -
        9769346496000*I06^3*I03 + 120839040*I15*I03^2 + 3511270080*J09*I06*I03^2
        - 3914395200*I09*I06*I03^2 - 44376660*J12*I03^3 - 37808370*I12*I03^3 -
        107233156800*I06^2*I03^3 + 4371669*J09*I03^4 + 18762237*I09*I03^4 +
        1441425930*I06*I03^5 - 1809080*I03^7,
        79361856*J12*I09 - 119042784*I12*I09 + 3997486080*I15*I06 -
        468267609600*J09*I06^2 - 34853898240*I09*I06^2 - 98269433280*J12*I06*I03
        + 248281886880*I12*I06*I03 + 245869496409600*I06^3*I03 -
        1081999296*I15*I03^2 - 82230364080*J09*I06*I03^2 +
        95221696176*I09*I06*I03^2 + 611398692*J12*I03^3 + 201071322*I12*I03^3 +
        3095770829760*I06^2*I03^3 + 39321459*J09*I03^4 - 327813093*I09*I03^4 -
        28855856610*I06*I03^5 + 34029464*I03^7,
        115736040*J18 - 12859560*I18 - 6099105600*J12*I06 + 9045781920*I12*I06 +
        15452047296000*I06^3 - 66951360*I15*I03 - 8124293520*J09*I06*I03 +
        6956636400*I09*I06*I03 + 43414380*J12*I03^2 - 12152430*I12*I03^2 +
        293581713600*I06^2*I03^2 + 13896423*J09*I03^3 - 27494361*I09*I03^3 -
        2425131450*I06*I03^4 + 2796920*I03^6,
        16533720*J09^2 - 4794778800*J12*I06 + 11242929600*I12*I06 +
        11898987609600*I06^3 - 59194800*I15*I03 - 5466288240*J09*I06*I03 +
        4848167520*I09*I06*I03 + 36327285*J12*I03^2 - 11510910*I12*I03^2 +
        188379898560*I06^2*I03^2 + 3844737*J09*I03^3 - 17937594*I09*I03^3 -
        1555733970*I06*I03^4 + 1311520*I03^6,
        46294416*J09*I09 - 29033212320*J12*I06 + 71094996000*I12*I06 +
        70256405721600*I06^3 - 358434720*I15*I03 - 24550510320*J09*I06*I03 +
        26952449328*I09*I06*I03 + 219967974*J12*I03^2 - 14540634*I12*I03^2 +
        908714479680*I06^2*I03^2 + 13697217*J09*I03^3 - 115752069*I09*I03^3 -
        9147024558*I06*I03^4 + 10906616*I03^6,
        23147208*I09^2 - 30918056400*J12*I06 + 79824800160*I12*I06 +
        72811857484800*I06^3 - 381704400*I15*I03 - 25336644480*J09*I06*I03 +
        29675464560*I09*I06*I03 + 234248355*J12*I03^2 + 21470508*I12*I03^2 +
        897510741120*I06^2*I03^2 + 25142976*J09*I03^3 - 137024721*I09*I03^3 -
        10068842196*I06*I03^4 + 14281736*I03^6,
        714420*J15 - 102060*I15 - 18869760*J09*I06 + 4672080*I09*I06 - 2430*J12*I03
        + 131220*I12*I03 + 613992960*I06^2*I03 + 88227*J09*I03^2 -
        52119*I09*I03^2 - 4525920*I06*I03^3 + 7840*I03^5
        ],
        [ w div 3 : w in [ 36, 33, 30, 30, 27, 27, 27, 27, 24, 24, 24, 24, 21, 21, 21, 21, 21, 18, 18, 18, 18, 15 ] ];

end function;

/*  Quartics in the singularity strata
	_ Irreducible : [ "(A4)", "(A5)", "(A1A4)", "(A6)", "(A2A4)" ],
        _ Reducible   : [ "(A7)", "(A1A5_a)", "(c^2)" ]

    Dimension 0 (vs 2 !)
*/

function A4Stratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
        180*I06 - I03^2,
        I09 - 245*I06*I03,
        J09 - 147*I06*I03,
        45*I12 - 7*I09*I03,
        J12 - I09*I03,
        108*I15 - 35*I09*I03^2,
        100*J15 - 7*I09*I03^2,
        3*J18 - 7*J15*I03,
        27*I18 - 175*J15*I03,
        3*I21 - 140*J09*I06*I03^2,
        J21 - 735*J09*I06*I03^2,
        I27
        ],
        [ 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 9 ];

end function;

/*  Quartics in the singularity strata
	_ Irreducible :
        _ Reducible   : [ "(A1A3)", "(A1^2A3_a)", "(A1A2A3)", "(A1A3^2)", "(A1^3A3)" ];

    Dimension 0 (vs 2!)
*/

function RedA1A3Stratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
        144*I06 + I03^2,
        36*I09 - 7*I03^3,
        6*J09 + I03^3,
        1296*I12 - 17*I03^4,
        288*J12 - 7*I03^4,
        31104*I15 - 625*I03^5,
        1152*J15 + 25*I03^5,
        62208*I18 - 775*I03^6,
        2304*J18 + 35*I03^6,
        20736*I21 + I03^7,
        256*J21 - I03^7,
        I27
        ],
        [ 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 9 ];

end function;

/*  Quartics in the singularity strata
	_ Irreducible : [ "(A3)", "(A1A3)", "(A2A3)" ] + A4Stratum
        _ Reducible   : [ "(A3^2)", "(A1^2A3_b)" ] + RedA1A3Stratum + RedA4Stratum

    Dimension 1 (vs 3!)
*/

function A3Stratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    if Characteristic(Universe(DO)) eq 11 then
        return [
            8*I09 + 5*I06*I03 + I03^3,
            I12 + 10*I06^2 + 3*J09*I03 + 7*I09*I03 + I03^4,
            J12 + 3*I06^2 + 10*J09*I03 + 4*I09*I03 + 6*I03^4,
            8*J15 + J09*I06 + 5*I06^2*I03 + J09*I03^2 + 7*I09*I03^2,
            5*J15 + I15 + 5*I12*I03 + 5*I06^2*I03 + 3*J09*I03^2 + 10*I09*I03^2,
            2*J09^2 + J12*I06 + 6*I15*I03 + 10*I09*I06*I03 + 7*J12*I03^2 + 9*J09*I03^3 + 2*I03^6,
            J18 + J09^2 + 9*I15*I03 + 6*I09*I06*I03 + 6*J12*I03^2 + 2*J09*I03^3 + I03^6,
            I18 + J09^2 + 6*I15*I03 + 7*I09*I06*I03 + 7*J12*I03^2 + 3*J09*I03^3 + 2*I03^6,
            J21 + 6*I12*I09 + 2*J09*I06^2 + 6*J09*I09*I03 + 3*J12*I06*I03 + I06*I03^5 + I03^7,
            8*I12*I09 + 8*J09*I09*I03 + J12*I06*I03 + J12*I03^3 + 3*I06*I03^5,
            I21 + 4*I12*I09 + 5*J09*I06^2 + 5*J09*I09*I03 + J12*I06*I03 + 2*I06*I03^5 + 10*I03^7,
            6*J09*I09*I06 + 7*I12*J09*I03 + 5*J09*I09*I03^2 + 6*J12*I06*I03^2 + 4*J12*I03^4 + I03^8,
            I27
            ],
            [ 3, 4, 4, 5, 5, 6, 6, 6, 7, 7, 7, 8, 9 ];
    end if;

    return [
        -495*J09 + 261*I09 + 14580*I06*I03 - 32*I03^3,
        -9*J12 + 30*I12 + 17400*I06^2 + 3*I09*I03 + 230*I06*I03^2,
        -264*J12 + 2475*I12 - 260*I09*I03 + 13175*I06*I03^2 + 116*I03^4,
        -64670*J15 + 1264410*J09*I06 + 7260*I12*I03 - 54063660*I06^2*I03 + 1533*J09*I03^2 - 511*I09*I03^2,
        -27875*J15 + 14049*I15 - 26500*I12*I03 + 11490500*I06^2*I03 + 4725*J09*I03^2 - 1575*I09*I03^2,
        306*I18 + 45900*I12*I06 - 20875*J15*I03 - 127500*J09*I06*I03 +
        246915*I09*I06*I03 + 2160*I12*I03^2,
        -6364746*I18 + 5734800*J09^2 + 251029800*I12*I06 - 2410625*J15*I03 -
        285713625*J09*I06*I03 + 8769600*I12*I03^2 - 637200*J09*I03^3,
        39825*J18 - 10683*I18 - 885600*I12*I06 - 30625*J15*I03 - 128625*J09*I06*I03 + 10800*I12*I03^2,
        4825625*J21 + 14026323500*J15*I06 - 318008890500*J09*I06^2 -
        71908400*J18*I03 - 2719942*I09^2*I03 + 2959856615*J12*I06*I03 -
        4531445100*J09*I06*I03^2 + 2719942*J12*I03^3,
        -333642750*J21 + 3787107345*I21 + 3339670572000*J09*I06^2 +
        1031500000*J18*I03 + 64791732*I09^2*I03 - 24760891410*J12*I06*I03 +
        33647567800*J09*I06*I03^2 - 64791732*J12*I03^3,
        I27
        ],
        [ 3, 4, 4, 5, 5, 6, 6, 6, 7, 7, 9 ];

end function;

/*  Quartics in the singularity strata
	_ Irreducible :
        _ Reducible   : [ "(A1^6)" ]

    Dimension 0 (vs 0)
*/

function RedA1p6Stratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
        144*I06 + I03^2,
        9*I09 - I03^3,
        3*J09 + I03^3,
        81*I12 + 4*I03^4,
        18*J12 + I03^4,
        972*I15 + I03^5,
        36*J15 - I03^5,
        243*I18 - I03^6,
        27*J18 - I03^6,
        162*I21 - I03^7,
        144*J21 + 7*I03^7,
        I27
        ],
        [ 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 9 ];

end function;

/*  Quartics in the singularity strata
	_ Irreducible :
        _ Reducible   : [ "(A1^5)" ] + RedA1p6Stratum + RedA1A3Stratum

    Dimension 1 (vs 1)
*/

function RedA1p5Stratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
        144*I06 + I03^2,
        9*J09 - 18*I09 + 5*I03^3,
        54*J12 - 81*I12 + 9*I09*I03 - 2*I03^4,
        1944*I15 - 729*I12*I03 + 54*I09*I03^2 - 40*I03^5,
        648*J15 + 81*I12*I03 + 324*I09*I03^2 - 50*I03^5,
        729*I09^2 - 81*I12*I03^2 - 162*I09*I03^3 + 5*I03^6,
        6561*J18 - 729*I18 + 1620*I12*I03^2 + 2970*I09*I03^3 - 490*I03^6,
        19683*I12*I09 - 2916*I18*I03 - 3726*I12*I03^3 + 1188*I09*I03^4 - 196*I03^7,
        39366*I21 - 1458*I18*I03 - 1863*I12*I03^3 + 4482*I09*I03^4 - 827*I03^7,
        209952*J21 + 11664*I18*I03 + 178929*I12*I03^3 - 267678*I09*I03^4 +
        48736*I03^7,
        708588*I18*I09 - 531441*I12^2*I03 - 23328*I18*I03^3 - 29079*I12*I03^5 -
        7020*I09*I03^6 + 412*I03^9,
        I27,
        2834352*I18^2 - 14348907*I12^3 + 2991816*I18*I12*I03^2 - 1651185*I12^2*I03^4
        + 124416*I18*I03^6 - 72144*I12*I03^8 - 1216*I03^12
        ],
        [ 2, 3, 4, 5, 5, 6, 6, 7, 7, 7, 9, 9, 12 ];

end function;

/*  Quartics in the singularity strata
	_ Irreducible :
        _ Reducible   : [ "(A1^3A2)" ] + RedA1A3Stratum

    Dimension 1 (vs 1)
*/

function RedA1p3A2Stratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
        144*I06 + I03^2,
        9*J09 - 18*I09 + 5*I03^3,
        1296*I12 - 1944*I09*I03 + 361*I03^4,
        864*J12 - 1800*I09*I03 + 329*I03^4,
        31104*I15 - 16632*I09*I03^2 + 2609*I03^5,
        384*J15 + 264*I09*I03^2 - 43*I03^5,
        124416*I18 - 944784*I09^2 + 299232*I09*I03^3 - 24013*I03^6,
        41472*J18 - 34992*I09^2 + 45216*I09*I03^3 - 6839*I03^6,
        5184*I21 - 4536*I09^2*I03 + 1881*I09*I03^4 - 194*I03^7,
        82944*J21 + 615600*I09^2*I03 - 236592*I09*I03^4 + 22405*I03^7,
        I27
        ],
        [ 2, 3, 4, 4, 5, 5, 6, 6, 7, 7, 9 ];

end function;

/*  Quartics in the singularity strata
	_ Irreducible :
        _ Reducible   : [ "(A1^4_a)" ] + RedA1p5Stratum + RedA1p3A2Stratum;

    Dimension 2 (vs 2)
*/

function RedA1p4_aStratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
        144*I06 + I03^2,
        9*J09 - 18*I09 + 5*I03^3,
        54*J12 - 81*I12 + 9*I09*I03 - 2*I03^4,
        1944*I15 - 729*I12*I03 + 54*I09*I03^2 - 40*I03^5,
        648*J15 + 81*I12*I03 + 324*I09*I03^2 - 50*I03^5,
        6561*J18 - 729*I18 + 1620*I12*I03^2 + 2970*I09*I03^3 - 490*I03^6,
        2916*I21 - 729*I12*I09 - 1458*I09^2*I03 + 162*I12*I03^3 + 612*I09*I03^4 -
        64*I03^7,
        209952*J21 + 11664*I18*I03 + 1469664*I09^2*I03 + 15633*I12*I03^3 -
        594270*I09*I03^4 + 58816*I03^7,
        I27,
        544195584*I18^2 - 2754990144*I12^3 - 8264970432*I18*I09^2 +
        31381059609*I09^4 + 12397455648*I12^2*I09*I03 - 343901376*I18*I12*I03^2
        - 15984682398*I12*I09^2*I03^2 + 3133533600*I18*I09*I03^3 -
        14497179039*I09^3*I03^3 - 2247870771*I12^2*I03^4 +
        5916497661*I12*I09*I03^5 - 305859240*I18*I03^6 + 1653464583*I09^2*I03^6
        - 544634037*I12*I03^8 + 81331263*I09*I03^9 - 16566224*I03^12
        ],
        [ 2, 3, 4, 5, 5, 6, 7, 7, 9, 12 ];

end function;

/*  Quartics in the singularity strata
	_ Irreducible : A3Stratum
        _ Reducible   : [ "(A1^4_b)" ] + RedA3Stratum;

    Dimension 2 (vs 2)
*/
function RedA1p4_bStratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return
[
    714420*J15 - 102060*I15 - 18869760*J09*I06 + 4672080*I09*I06 - 2430*J12*I03
        + 131220*I12*I03 + 613992960*I06^2*I03 + 88227*J09*I03^2 -
        52119*I09*I03^2 - 4525920*I06*I03^3 + 7840*I03^5,
    23147208*I09^2 - 30918056400*J12*I06 + 79824800160*I12*I06 +
        72811857484800*I06^3 - 381704400*I15*I03 - 25336644480*J09*I06*I03 +
        29675464560*I09*I06*I03 + 234248355*J12*I03^2 + 21470508*I12*I03^2 +
        897510741120*I06^2*I03^2 + 25142976*J09*I03^3 - 137024721*I09*I03^3 -
        10068842196*I06*I03^4 + 14281736*I03^6,
    46294416*J09*I09 - 29033212320*J12*I06 + 71094996000*I12*I06 +
        70256405721600*I06^3 - 358434720*I15*I03 - 24550510320*J09*I06*I03 +
        26952449328*I09*I06*I03 + 219967974*J12*I03^2 - 14540634*I12*I03^2 +
        908714479680*I06^2*I03^2 + 13697217*J09*I03^3 - 115752069*I09*I03^3 -
        9147024558*I06*I03^4 + 10906616*I03^6,
    16533720*J09^2 - 4794778800*J12*I06 + 11242929600*I12*I06 +
        11898987609600*I06^3 - 59194800*I15*I03 - 5466288240*J09*I06*I03 +
        4848167520*I09*I06*I03 + 36327285*J12*I03^2 - 11510910*I12*I03^2 +
        188379898560*I06^2*I03^2 + 3844737*J09*I03^3 - 17937594*I09*I03^3 -
        1555733970*I06*I03^4 + 1311520*I03^6,
    115736040*J18 - 12859560*I18 - 6099105600*J12*I06 + 9045781920*I12*I06 +
        15452047296000*I06^3 - 66951360*I15*I03 - 8124293520*J09*I06*I03 +
        6956636400*I09*I06*I03 + 43414380*J12*I03^2 - 12152430*I12*I03^2 +
        293581713600*I06^2*I03^2 + 13896423*J09*I03^3 - 27494361*I09*I03^3 -
        2425131450*I06*I03^4 + 2796920*I03^6,
    79361856*J12*I09 - 119042784*I12*I09 + 3997486080*I15*I06 -
        468267609600*J09*I06^2 - 34853898240*I09*I06^2 - 98269433280*J12*I06*I03
        + 248281886880*I12*I06*I03 + 245869496409600*I06^3*I03 -
        1081999296*I15*I03^2 - 82230364080*J09*I06*I03^2 +
        95221696176*I09*I06*I03^2 + 611398692*J12*I03^3 + 201071322*I12*I03^3 +
        3095770829760*I06^2*I03^3 + 39321459*J09*I03^4 - 327813093*I09*I03^4 -
        28855856610*I06*I03^5 + 34029464*I03^7,
    145741680*I12*J09 - 60011280*I12*I09 - 391910400*I15*I06 -
        25136697600*J09*I06^2 + 15883257600*I09*I06^2 - 34292160*I18*I03 +
        4963032000*J12*I06*I03 - 21151614240*I12*I06*I03 -
        9769346496000*I06^3*I03 + 120839040*I15*I03^2 + 3511270080*J09*I06*I03^2
        - 3914395200*I09*I06*I03^2 - 44376660*J12*I03^3 - 37808370*I12*I03^3 -
        107233156800*I06^2*I03^3 + 4371669*J09*I03^4 + 18762237*I09*I03^4 +
        1441425930*I06*I03^5 - 1809080*I03^7,
    47220304320*J12*J09 - 29165482080*I12*I09 + 788915635200*I15*I06 -
        263047582425600*J09*I06^2 + 57199923809280*I09*I06^2 -
        16665989760*I18*I03 - 27092328552000*J12*I06*I03 +
        59391875760480*I12*I06*I03 + 70417517931532800*I06^3*I03 -
        246219341760*I15*I03^2 - 22833657187920*J09*I06*I03^2 +
        26081263572624*I09*I06*I03^2 + 152809112412*J12*I03^3 +
        15208600662*I12*I03^3 + 887697787152960*I06^2*I03^3 +
        7960842909*J09*I03^4 - 77072274315*I09*I03^4 - 7385950391022*I06*I03^5 +
        7244463016*I03^7,
    157401014400*I21 - 10184771520*I12*I09 + 2285151160320*I15*I06 +
        239979311712000*J09*I06^2 - 163148739667200*I09*I06^2 -
        4320812160*I18*I03 - 15440685393600*J12*I06*I03 +
        33352042743072*I12*I06*I03 + 22089994384872960*I06^3*I03 -
        121293982656*I15*I03^2 - 9524553124896*J09*I06*I03^2 +
        12078746015904*I09*I06*I03^2 + 50015849220*J12*I03^3 +
        41662281474*I12*I03^3 + 470481418443456*I06^2*I03^3 -
        577252017*J09*I03^4 - 22825866969*I09*I03^4 - 2770748500842*I06*I03^5 +
        2115444856*I03^7,
    78700507200*J21 - 68747207760*I12*I09 + 18084097946880*I15*I06 -
        136350625017600*J09*I06^2 - 652397684037120*I09*I06^2 +
        14557021920*I18*I03 - 176244290380800*J12*I06*I03 +
        411095495122848*I12*I06*I03 + 368447664976151040*I06^3*I03 -
        1643397717024*I15*I03^2 - 122379639217344*J09*I06*I03^2 +
        153553235481360*I09*I06*I03^2 + 771662086992*J12*I03^3 +
        604912231278*I12*I03^3 + 5158006751951424*I06^2*I03^3 -
        20887586469*J09*I03^4 - 368016979761*I09*I03^4 -
        39415825207710*I06*I03^5 + 39252937640*I03^7,
    755524869120*I15*I09 + 269722378275840*I18*I06 - 66379875340262400*J12*I06^2
        + 185681515493214720*I12*I06^2 + 156408063322342809600*I06^4 -
        3993171146496*I12*I09*I03 - 1338155957053440*I15*I06*I03 -
        62236557216610560*J09*I06^2*I03 + 64791825752989440*I09*I06^2*I03 +
        2422679378112*I18*I03^2 + 623392394866560*J12*I06*I03^2 +
        417261395342016*I12*I06*I03^2 + 2018412722028003840*I06^3*I03^2 -
        3879745091712*I15*I03^3 - 21535351456608*J09*I06*I03^3 -
        292628800128096*I09*I06*I03^3 - 30407419116*J12*I03^4 +
        3958898198562*I12*I03^4 - 22368335306601312*I06^2*I03^4 -
        594957445821*J09*I03^5 + 392263473915*I09*I03^5 +
        37042193318214*I06*I03^6 - 61269506312*I03^8,
    755524869120*I15*J09 + 111062155760640*I18*I06 - 28155713568998400*J12*I06^2
        + 78598493353981440*I12*I06^2 + 66618526218635059200*I06^4 -
        1866590853120*I12*I09*I03 - 596747700541440*I15*I06*I03 -
        26933349775691520*J09*I06^2*I03 + 27852916445948160*I09*I06^2*I03 +
        963849741120*I18*I03^2 + 298452244014720*J12*I06*I03^2 +
        79615126276416*I12*I06*I03^2 + 804187935730368000*I06^3*I03^2 -
        1098379191168*I15*I03^3 + 13966940620512*J09*I06*I03^3 -
        150798793259808*I09*I06*I03^3 - 288352251540*J12*I03^4 +
        1606586119902*I12*I03^4 - 10287300216346272*I06^2*I03^4 -
        284282009091*J09*I03^5 + 322784586693*I09*I03^5 +
        26293305789114*I06*I03^6 - 43968833272*I03^8,
    141660912960*J12*I12 - 212491369440*I12^2 + 1762891361280*I18*I06 -
        365170353408000*J12*I06^2 + 601523716631040*I12*I06^2 +
        873406896032563200*I06^4 - 125550456192*I12*I09*I03 -
        5595775073280*I15*I06*I03 - 454256832395520*J09*I06^2*I03 +
        392174318995200*I09*I06^2*I03 + 34340169024*I18*I03^2 -
        5983509528000*J12*I06*I03^2 + 21314817487872*I12*I06*I03^2 +
        37033350525319680*I06^3*I03^2 - 121630045824*I15*I03^3 -
        7867640077056*J09*I06*I03^3 + 7701206626944*I09*I06*I03^3 +
        36145854396*J12*I03^4 + 82907972982*I12*I03^4 +
        210140292128256*I06^2*I03^4 - 11717847567*J09*I03^5 -
        8743281543*I09*I03^5 - 1824919355070*I06*I03^6 + 200204200*I03^8,
    15740101440*J12^2 - 35415228240*I12^2 + 587630453760*I18*I06 -
        201053562393600*J12*I06^2 + 307162832901120*I12*I06^2 +
        395040448844697600*I06^4 - 41850152064*I12*I09*I03 -
        459919918080*I15*I06*I03 - 290196805973760*J09*I06^2*I03 +
        177845411600640*I09*I06^2*I03 + 11446723008*I18*I03^2 -
        19885187352960*J12*I06*I03^2 + 51058967007456*I12*I06*I03^2 +
        58963815299773440*I06^3*I03^2 - 217047164544*I15*I03^3 -
        17369331206688*J09*I06*I03^3 + 19839562633440*I09*I06*I03^3 +
        108653584356*J12*I03^4 + 71998750422*I12*I03^4 +
        642554604085968*I06^2*I03^4 - 1070840727*J09*I03^5 -
        51247215207*I09*I03^5 - 5420874202366*I06*I03^6 + 4934444648*I03^8,
    89193908160*I18*J09 - 36726903360*I18*I09 - 299987815680*I12*I09*I06 +
        62868698726400*I15*I06^2 - 5031451531008000*J09*I06^3 +
        1957517985024000*I09*I06^3 - 106245684720*I12^2*I03 +
        1345624358400*I18*I06*I03 - 1567054938124800*J12*I06^2*I03 +
        4183174464837120*I12*I06^2*I03 + 3945687769968537600*I06^4*I03 -
        76663552896*I12*I09*I03^2 - 28158448711680*I15*I06*I03^2 -
        1467060756629760*J09*I06^2*I03^2 + 1593415090103040*I09*I06^2*I03^2 +
        65281984992*I18*I03^3 + 20059796072160*J12*I06*I03^3 -
        7717787510976*I12*I06*I03^3 + 34942850265415680*I06^3*I03^3 -
        25333904736*I15*I03^4 + 4609707056568*J09*I06*I03^4 -
        12529856932776*I09*I06*I03^4 - 40944607704*J12*I03^5 +
        71738637390*I12*I03^5 - 702208216897488*I06^2*I03^5 -
        18601002693*J09*I03^6 + 32425023015*I09*I03^6 + 2760471631554*I06*I03^7
        - 4192162072*I03^9,
    288988262438400*I15*I12 - 71397100131840*I18*I09 -
        18636443061304320*I12*I09*I06 - 835978744258560000*I15*I06^2 +
        81424900602339840000*J09*I06^3 - 25188522747707289600*I09*I06^3 -
        54822773315520*I12^2*I03 - 84985200088750080*I18*I06*I03 +
        28894644471132288000*J12*I06^2*I03 - 77252106530354250240*I12*I06^2*I03
        - 71037042640228069171200*I06^4*I03 + 993215770610112*I12*I09*I03^2 +
        502347097409633280*I15*I06*I03^2 + 25956051685199205120*J09*I06^2*I03^2
        - 28434439564115109120*I09*I06^2*I03^2 - 752951599150464*I18*I03^3 -
        303681676801656960*J12*I06*I03^3 + 20884993905463488*I12*I06*I03^3 -
        740777927030483489280*I06^3*I03^3 + 556566445681344*I15*I03^4 -
        49793845007462544*J09*I06*I03^4 + 178274608730986032*I09*I06*I03^4 +
        342590177792772*J12*I03^5 - 996285063518514*I12*I03^5 +
        11407369144748469984*I06^2*I03^5 + 182726567723889*J09*I03^6 -
        278889044708799*I09*I03^6 - 30801522909942918*I06*I03^7 +
        34594487623304*I03^9,
    577976524876800*I15*J12 - 214191300395520*I18*I09 -
        46913294567301120*I12*I09*I06 - 3762863040384000000*I15*I06^2 +
        196129299258385920000*J09*I06^3 - 57181646876001177600*I09*I06^3 -
        164468319946560*I12^2*I03 - 70719349881600000*I18*I06*I03 +
        38840902470748339200*J12*I06^2*I03 - 101122876332457228800*I12*I06^2*I03
        - 98417394942142381056000*I06^4*I03 + 447515157035520*I12*I09*I03^2 +
        593077779248371200*I15*I06*I03^2 + 32542586488538092800*J09*I06^2*I03^2
        - 38146533617331843840*I09*I06^2*I03^2 - 589698888266880*I18*I03^3 -
        532050653582951040*J12*I06*I03^3 + 448598299071795840*I12*I06*I03^3 -
        595778384054495577600*I06^3*I03^3 - 1235030328181440*I15*I03^4 -
        208097684074275120*J09*I06*I03^4 + 385060968529909200*I09*I06*I03^4 +
        1152486275289660*J12*I03^5 - 165351326875470*I12*I03^5 +
        20419759950938056800*I06^2*I03^5 + 109307215920591*J09*I03^6 -
        608275338600897*I09*I03^6 - 77522527833755130*I06*I03^7 +
        62559169399160*I03^9,
    I27,
    48164710406400*I18*J12 - 72247065609600*I18*I12 + 3034376755603200*I12^2*I06
        - 261031323864729600*I18*I06^2 + 27649540688587776000*J12*I06^3 -
        82807167662934220800*I12*I06^3 - 63464548768147021824000*I06^5 -
        42687155105280*I18*I09*I03 + 2451600425675520*I12*I09*I06*I03 +
        642625760338329600*I15*I06^2*I03 + 14933961781398374400*J09*I06^3*I03 -
        22200926584973875200*I09*I06^3*I03 + 59108015932560*I12^2*I03^2 -
        4894421989806720*I18*I06*I03^2 + 115694686230451200*J12*I06^2*I03^2 -
        1831581261062760960*I12*I06^2*I03^2 - 1274392217489390899200*I06^4*I03^2
        + 42386056223616*I12*I09*I03^3 + 17629473639697920*I15*I06*I03^3 +
        283504543763143680*J09*I06^2*I03^3 - 156263294379018240*I09*I06^2*I03^3
        - 25272179991072*I18*I03^4 - 12854036094723360*J12*I06*I03^4 +
        5516129320022304*I12*I06*I03^4 + 20747168812652163840*I06^3*I03^4 +
        10802328741792*I15*I03^5 - 4879982125386072*J09*I06*I03^5 +
        9538133063229576*I09*I06*I03^5 + 17530832687256*J12*I03^6 -
        28250820635562*I12*I03^6 + 401044800141920592*I06^2*I03^6 +
        4398069923415*J09*I03^7 - 10598233956093*I09*I03^7 -
        1741809750977254*I06*I03^8 + 1096199917512*I03^10,
    34678591492608000*I15^2 + 15484424583843129600*I12^2*I06 +
        349560202245488640000*I18*I06^2 - 76796236268830310400000*J12*I06^3 +
        211466355174887371776000*I12*I06^3 + 181423967169551450480640000*I06^5 -
        46907894786618880*I18*I09*I03 - 19325307482352829440*I12*I09*I06*I03 -
        2178763376444992512000*I15*I06^2*I03 -
        19596936953893178880000*J09*I06^3*I03 +
        59481958099666888396800*I09*I06^3*I03 + 137834970438004560*I12^2*I03^2 -
        56372182651300239360*I18*I06*I03^2 +
        20886039901824465024000*J12*I06^2*I03^2 -
        53620957966411598446080*I12*I06^2*I03^2 -
        47024505883464279090278400*I06^4*I03^2 +
        705947792189459904*I12*I09*I03^3 + 347793461120876520960*I15*I06*I03^3 +
        18078683169589695671040*J09*I06^2*I03^3 -
        20139157905824594269440*I09*I06^2*I03^3 - 531146675438805888*I18*I03^4 -
        211190338682493217920*J12*I06*I03^4 + 14694434756584106976*I12*I06*I03^4
        - 544534357812549272098560*I06^3*I03^4 + 405724433006870208*I15*I03^5 -
        34261020803869778448*J09*I06*I03^5 + 123764660775562229424*I09*I06*I03^5
        + 233672973270789924*J12*I03^6 - 705639226894684578*I12*I03^6 +
        7958158226344057053168*I06^2*I03^6 + 129877541229165993*J09*I03^7 -
        193851317824677063*I09*I03^7 - 21332627117486982486*I06*I03^8 +
        24222604330452808*I03^10,
    393024036916224000*I18*I15 - 491569034407718400*I12^2*I09 +
        19903063616181043200*I18*I09*I06 + 6541078663224599961600*I12*I09*I06^2
        + 258071062503084687360000*I15*I06^3 -
        29026348566722106163200000*J09*I06^4 +
        9324492388876293931008000*I09*I06^4 - 74558971709107200*I18*I12*I03 +
        545813389216313164800*I12^2*I06*I03 +
        44580452836931356262400*I18*I06^2*I03 -
        13338810453959680296960000*J12*I06^3*I03 +
        35841876533051766130483200*I12*I06^3*I03 +
        32534731151125956724801536000*I06^5*I03 -
        1305151078807941120*I18*I09*I03^2 - 991074670662022571520*I12*I09*I06*I\
        03^2 - 258536139080780007014400*I15*I06^2*I03^2 -
        10693636827367493367705600*J09*I06^3*I03^2 +
        12699513957634493454028800*I09*I06^3*I03^2 +
        4974138078494437440*I12^2*I03^3 - 1369520260038758661120*I18*I06*I03^3 +
        728151394310931455308800*J12*I06^2*I03^3 -
        1577747539689225096476160*I12*I06^2*I03^3 -
        1085498358636468541272883200*I06^4*I03^3 +
        21037143844877783616*I12*I09*I03^4 +
        9997983731835892638720*I15*I06*I03^4 +
        547991246575695535246080*J09*I06^2*I03^4 -
        656897938354317704382720*I09*I06^2*I03^4 -
        15808038903975068352*I18*I03^5 - 6282634920359168917440*J12*I06*I03^5 +
        680392035073332536544*I12*I06*I03^5 -
        20415402622594888467471360*I06^3*I03^5 + 12722175886769177472*I15*I03^6
        - 1026403244433120763152*J09*I06*I03^6 +
        3688013836294863278256*I09*I06*I03^6 + 6597331856208548316*J12*I03^7 -
        21210575343230800602*I12*I03^7 + 243030364011127509449472*I06^2*I03^7 +
        3882867345652878297*J09*I03^8 - 5616693645382714527*I09*I03^8 -
        626736389258102286254*I06*I03^9 + 707764637142968552*I03^11,
    117907211074867200*I18^2 - 596905256066515200*I12^3 +
        54944760360888115200*I18*I12*I06 + 9669452473038784204800*I12^2*I06^2 -
        6263231052296945664000*I18*I06^3 - 6410492442641011802112000*I12*I06^4 +
        1352423254153233872977920000*I06^6 - 950366799854922240*I12^2*I09*I03 -
        20205243342834278400*I18*I09*I06*I03 -
        2445348871588950835200*I12*I09*I06^2*I03 +
        4596482566178979840000*I15*I06^3*I03 -
        4111425975375814717440000*J09*I06^4*I03 +
        2647676395512775839744000*I09*I06^4*I03 +
        646813528989626880*I18*I12*I03^2 + 652574389306238542080*I12^2*I06*I03^\
        2 + 4593667919355957657600*I18*I06^2*I03^2 -
        496233798056371860480000*J12*I06^3*I03^2 +
        1010355025854785674752000*I12*I06^3*I03^2 +
        1416857459384027080433664000*I06^5*I03^2 -
        1350366220125296640*I18*I09*I03^3 - 548329984602150159360*I12*I09*I06*I\
        03^3 - 29454157619939482214400*I15*I06^2*I03^3 +
        1051920614707942396262400*J09*I06^3*I03^3 +
        70653631303072972339200*I09*I06^3*I03^3 +
        5084209882812574080*I12^2*I03^4 - 1855323377249247682560*I18*I06*I03^4 +
        639462783539835494092800*J12*I06^2*I03^4 -
        1701439320002895662699520*I12*I06^2*I03^4 -
        1533548490811137883289088000*I06^4*I03^4 +
        22516507377864045504*I12*I09*I03^5 +
        11083494084833344849920*I15*I06*I03^5 +
        570292376869244768446080*J09*I06^2*I03^5 -
        625001268025819677813120*I09*I06^2*I03^5 -
        16953737505601071168*I18*I03^6 - 6608545148226629665440*J12*I06*I03^6 +
        213531089587599871728*I12*I06*I03^6 -
        16640500915415561703079680*I06^3*I03^6 + 13573922986039635072*I15*I03^7
        - 1009298959836255797112*J09*I06*I03^7 +
        3834773826350376448008*I09*I06*I03^7 + 7107490415168413236*J12*I03^8 -
        22727738435047181982*I12*I03^8 + 247523098472121542447664*I06^2*I03^8 +
        4161779905768068627*J09*I03^9 - 6036709288553102421*I09*I03^9 -
        657172382973704315130*I06*I03^10 + 760095282746980600*I03^12
],
[ 5, 6, 6, 6, 6, 7, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 11, 12 ];

end function;

/*
Quartics in the singularity strata
	_ Irreducible : [ "(A1A2^2)" ] + A4Stratum + A2p3Stratum
        _ Reducible   : [] + RedA1A3Stratum + RedA4Stratum;

Dimension 1 (vs 1)
 */
function A1A2p2Stratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
    486*I12 - 155520*I06^2 - 423*J09*I03 + 117*I09*I03 + 14418*I06*I03^2 +
        8*I03^4,
    163296*I15 - 9548280*J09*I06 + 1583064*I09*I06 - 20898*J12*I03 +
        461952720*I06^2*I03 - 82980*J09*I03^2 + 558*I09*I03^2 +
        5305212*I06*I03^3 + 11041*I03^5,
    272160*J15 - 476280*J09*I06 - 884520*I09*I06 - 94770*J12*I03 +
        203478480*I06^2*I03 + 195876*J09*I03^2 - 19962*I09*I03^2 -
        4915620*I06*I03^3 + 145*I03^5,
    2204496*I09^2 - 742810176*J12*I06 + 2073234009600*I06^3 +
        875953440*J09*I06*I03 - 70401312*I09*I06*I03 - 5269212*J12*I03^2 +
        17447594400*I06^2*I03^2 + 6288480*J09*I03^3 - 1526292*I09*I03^3 +
        104206752*I06*I03^4 + 731869*I03^6,
    2204496*J09*I09 - 408566592*J12*I06 + 1677180556800*I06^3 +
        730840320*J09*I06*I03 - 309464064*I09*I06*I03 - 1484244*J12*I03^2 +
        3172491360*I06^2*I03^2 + 3065940*J09*I03^3 - 1439064*I09*I03^3 +
        62283024*I06*I03^4 + 406823*I03^6,
    11022480*J09^2 - 967878720*J12*I06 + 4751885606400*I06^3 +
        791843040*J09*I06*I03 - 690340320*I09*I06*I03 + 1297620*J12*I03^2 +
        29876286240*I06^2*I03^2 + 336888*J09*I03^3 - 3827916*I09*I03^3 +
        354052800*I06*I03^4 + 1060025*I03^6,
    489888*I18 - 28203552*J12*I06 + 168087571200*I06^3 + 33239160*J09*I06*I03 -
        39237048*I09*I06*I03 + 328050*J12*I03^2 + 1427032080*I06^2*I03^2 -
        451620*J09*I03^3 - 267534*I09*I03^3 + 33303132*I06*I03^4 + 85205*I03^6,
    7348320*J18 - 196305120*J12*I06 + 966325075200*I06^3 + 244597320*J09*I06*I03
        - 170854920*I09*I06*I03 - 2135970*J12*I03^2 + 9343505520*I06^2*I03^2 +
        5347764*J09*I03^3 - 1274418*I09*I03^3 - 62019900*I06*I03^4 +
        198035*I03^6,
    6613488*J12*I09 - 113987139840*J09*I06^2 + 5919806592*I09*I06^2 -
        1275878304*J12*I06*I03 + 11995204412160*I06^3*I03 +
        794399400*J09*I06*I03^2 - 765839448*I09*I06*I03^2 - 5517072*J12*I03^3 +
        113597258976*I06^2*I03^3 + 5566950*J09*I03^4 - 4515066*I09*I03^4 +
        675645912*I06*I03^5 + 1998881*I03^7,
    6613488*J12*J09 - 81154846080*J09*I06^2 + 18188561664*I09*I06^2 -
        992863008*J12*I06*I03 + 7123746942720*I06^3*I03 - 80407080*J09*I06*I03^2
        - 85197096*I09*I06*I03^2 - 1061424*J12*I03^3 + 73676565792*I06^2*I03^3 -
        1973034*J09*I03^4 - 990234*I09*I03^4 + 449499384*I06*I03^5 +
        858067*I03^7,
    6613488*I21 - 6025622400*J09*I06^2 - 1241866080*I09*I06^2 -
        116155944*J12*I06*I03 + 764235777600*I06^3*I03 + 46309320*J09*I06*I03^2
        - 87579792*I09*I06*I03^2 + 188811*J12*I03^3 + 6751852200*I06^2*I03^3 -
        400617*J09*I03^4 - 447300*I09*I03^4 + 60466356*I06*I03^5 + 137921*I03^7,
    22044960*J21 - 1043865597600*J09*I06^2 + 130733961120*I09*I06^2 -
        4865900040*J12*I06*I03 + 51572829729600*I06^3*I03 -
        9680562720*J09*I06*I03^2 + 3726787320*I09*I06*I03^2 - 58079430*J12*I03^3
        + 732381860160*I06^2*I03^3 + 10246752*J09*I03^4 + 16658766*I09*I03^4 +
        2308560120*I06*I03^5 + 3577415*I03^7,
    19840464*J12^2 - 225705118464*J12*I06^2 + 722542081766400*I06^4 -
        134973941760*J09*I06^2*I03 + 38846158848*I09*I06^2*I03 -
        5750165376*J12*I06*I03^2 + 39344131399680*I06^3*I03^2 +
        1232152560*J09*I06*I03^3 - 44713296*I09*I06*I03^3 - 16379172*J12*I03^4 +
        410515343136*I06^2*I03^4 + 374940*J09*I03^5 - 1202832*I09*I03^5 +
        2200348944*I06*I03^6 + 4019989*I03^8,
    I27
    ],
    [ 4, 5, 5, 6, 6, 6, 6, 6, 7, 7, 7, 7, 8, 9 ];

end function;


/*
Quartics in the singularity strata
	_ Irreducible : [ "(A1^2A2)" ] + ...
        _ Reducible   : [] + ...

Dimension 2 (vs 2)
 */
 function A1p2A2Stratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
    486*I12 - 155520*I06^2 - 423*J09*I03 + 117*I09*I03 + 14418*I06*I03^2 +
        8*I03^4,
    4860*J15 + 43740*I15 - 2566080*J09*I06 + 408240*I09*I06 - 7290*J12*I03 +
        127370880*I06^2*I03 - 18729*J09*I03^2 - 207*I09*I03^2 +
        1333260*I06*I03^3 + 2960*I03^5,
    7348320*I18 - 17721585*J09^2 + 7966350*J09*I09 - 847665*I09^2 -
        57736800*J12*I06 + 144992851200*I06^3 + 7348320*I15*I03 +
        1100022120*J09*I06*I03 - 498645720*I09*I06*I03 - 1443420*J12*I03^2 -
        1085276880*I06^2*I03^2 - 2388726*J09*I03^3 - 2446938*I09*I03^3 +
        354048840*I06*I03^4 + 1259360*I03^6,
    22044960*J18 - 3064635*J09^2 - 3815910*J09*I09 + 1289925*I09^2 -
        47239200*J12*I06 - 112240339200*I06^3 + 198404640*I15*I03 -
        11840038920*J09*I06*I03 + 2097274680*I09*I06*I03 - 32673780*J12*I03^2 +
        585714116880*I06^2*I03^2 - 86498514*J09*I03^3 - 483102*I09*I03^3 +
        6114498840*I06*I03^4 + 13438240*I03^6,
    3968092800*I21 + 24538140*J12*J09 - 165993300*J12*I09 -
        2955435517440*I15*I06 + 171755385400800*J09*I06^2 -
        29477522190240*I09*I06^2 - 968897295*J09^2*I03 + 334009494*J09*I09*I03 -
        20933883*I09^2*I03 + 367100547120*J12*I06*I03 -
        8360086183286400*I06^3*I03 - 12962436480*I15*I03^2 +
        2300125199400*J09*I06*I03^2 - 154941689160*I09*I06*I03^2 +
        1617796800*J12*I03^3 - 133524847632240*I06^2*I03^3 +
        6574736448*J09*I03^4 - 70085376*I09*I03^4 - 622640183040*I06*I03^5 -
        879157760*I03^7,
    1102248000*J21 - 4233157200*J12*J09 - 249318000*J12*I09 -
        7870050720000*I15*I06 + 464228751312000*J09*I06^2 -
        81624361737600*I09*I06^2 + 7163255655*J09^2*I03 - 1133586090*J09*I09*I03
        - 47536065*I09^2*I03 + 1044600429600*J12*I06*I03 -
        22516130457273600*I06^3*I03 - 27468020160*I15*I03^2 +
        5262731160840*J09*I06*I03^2 - 311423755320*I09*I06*I03^2 +
        3218797440*J12*I03^3 - 330803613383760*I06^2*I03^3 +
        14030218368*J09*I03^4 - 171657216*I09*I03^4 - 1426451938560*I06*I03^5 -
        1839011840*I03^7,
    5584723200*I15*J09 - 3233260800*I15*I09 - 323242390800*J09^2*I06 +
        240212498400*J09*I09*I06 - 31171165200*I09^2*I06 +
        204073344000*J12*I06^2 - 680788675584000*I06^4 - 697653000*J12*J09*I03 +
        415092600*J12*I09*I03 - 264539520000*I15*I06*I03 +
        30352351233600*J09*I06^2*I03 - 11456986161600*I09*I06^2*I03 -
        2837194695*J09^2*I03^2 + 1650038850*J09*I09*I03^2 - 11979495*I09^2*I03^2
        + 35508132000*J12*I06*I03^2 - 731293049088000*I06^3*I03^2 +
        251475840*I15*I03^3 + 293244815160*J09*I06*I03^3 -
        101526141960*I09*I06*I03^3 - 25592760*J12*I03^4 -
        7663041722160*I06^2*I03^4 + 226437408*J09*I03^5 - 212943096*I09*I03^5 -
        8959080960*I06*I03^6 + 17149760*I03^8,
    20194758000*J12^2 - 999959385600*I15*I09 + 469202479200*J09^2*I06 +
        57060611092800*J09*I09*I06 - 9689849920800*I09^2*I06 -
        11173015584000*J12*I06^2 - 130474496559744000*I06^4 -
        49744189800*J12*J09*I03 + 138850443000*J12*I09*I03 +
        7999675084800*I15*I06*I03 - 614057416430400*J09*I06^2*I03 -
        2670484474497600*I09*I06^2*I03 + 33833915865*J09^2*I03^2 +
        485327697570*J09*I09*I03^2 - 2694446775*I09^2*I03^2 +
        499271104800*J12*I06*I03^2 + 26017402459564800*I06^3*I03^2 +
        277149237120*I15*I03^3 - 23882344265160*J09*I06*I03^3 -
        28623560344200*I09*I06*I03^3 - 35619610680*J12*I03^4 +
        1134537642547920*I06^2*I03^4 - 145081753056*J09*I03^5 -
        65228241528*I09*I03^5 + 9778115473920*I06*I03^6 + 18949455680*I03^8,
    5894985600*J09^3 - 26992828800*J09^2*I09 + 37231488000*J09*I09^2 -
        13651545600*I09^3 - 5089079016000*J12*J09*I06 +
        3635056440000*J12*I09*I06 - 5862619026432000*I15*I06^2 +
        339991190900928000*J09*I06^3 - 62365936329792000*I09*I06^3 -
        857108044800*I15*I09*I03 + 4279716680400*J09^2*I06*I03 +
        49072747557600*J09*I09*I06*I03 - 10511601174000*I09^2*I06*I03 +
        1155718365408000*J12*I06^2*I03 - 16838246301034752000*I06^4*I03 -
        42568424100*J12*J09*I03^2 + 145561689900*J12*I09*I03^2 -
        44712469670400*I15*I06*I03^2 + 4840591517877600*J09*I06^2*I03^2 -
        2926968844845600*I09*I06^2*I03^2 + 47131408845*J09^2*I03^3 +
        387853993710*J09*I09*I03^3 + 982807425*I09^2*I03^3 +
        9416921943600*J12*I06*I03^3 - 301511337133910400*I06^3*I03^3 +
        81742711680*I15*I03^4 + 9606838078440*J09*I06*I03^4 -
        25921082772360*I09*I06*I03^4 - 7881860520*J12*I03^5 -
        1380243248676720*I06^2*I03^5 - 53527586184*J09*I03^6 -
        58117254192*I09*I03^6 + 341625120480*I06*I03^7 + 6422979520*I03^9,
    257846670144000*I15*J12 + 175918780800*J09^2*I09 - 703675123200*J09*I09^2 +
        703675123200*I09^3 - 14852477108196000*J12*J09*I06 +
        2155224963276000*J12*I09*I06 - 160244920055808000*I15*I06^2 +
        10448116710202080000*J09*I06^3 - 933099601180320000*I09*I06^3 -
        1814331070944000*I15*I09*I03 + 654946000581600*J09^2*I06*I03 +
        104053810255668000*J09*I09*I06*I03 - 17555071839278400*I09^2*I06*I03 +
        724756609167984000*J12*I06^2*I03 - 752779654247901312000*I06^4*I03 -
        209778185659950*J12*J09*I03^2 + 248105754538650*J12*I09*I03^2 +
        6180471195897600*I15*I06*I03^2 - 506435972371945200*J09*I06^2*I03^2 -
        4929000862925185200*I09*I06^2*I03^2 + 53200591152435*J09^2*I03^3 +
        887948570248560*J09*I09*I03^3 - 5693688728235*I09^2*I03^3 +
        10050819300462600*J12*I06*I03^3 + 16331261666840769600*I06^3*I03^3 +
        476027138321280*I15*I03^4 - 36816297215052960*J09*I06*I03^4 -
        52379622340326360*I09*I06*I03^4 - 43180755289920*J12*I03^5 +
        1672087731917168880*I06^2*I03^5 - 249548109794964*J09*I03^6 -
        118216207992132*I09*I03^6 + 16222333836484080*I06*I03^7 +
        32402336177920*I03^9,
    I27,
    6720283584000*J12*J09^2 - 17331257664000*J12*J09*I09 +
        7781380992000*J12*I09^2 - 27358888790016000*I15*I09*I06 +
        130616008826688000*J09^2*I06^2 + 1537513725105792000*J09*I09*I06^2 -
        282791115552960000*I09^2*I06^2 + 3009477766901760000*J12*I06^3 -
        7544487172734812160000*I06^5 - 14469707548800*J09^2*I09*I03 +
        37983253795200*J09*I09^2*I03 - 18087677395200*I09^3*I03 -
        7425259482312000*J12*J09*I06*I03 + 9806272311384000*J12*I09*I06*I03 -
        8368128691098624000*I15*I06^2*I03 + 462895330686957504000*J09*I06^3*I03
        - 162433677041499456000*I09*I06^3*I03 - 1445401610956800*I15*I09*I03^2 +
        8504533725282000*J09^2*I06*I03^2 + 93753608585234400*J09*I09*I06*I03^2 -
        16883889777270000*I09^2*I06*I03^2 + 1696991942238048000*J12*I06^2*I03^2
        - 23534777215219343616000*I06^4*I03^2 - 55903871193300*J12*J09*I03^3 +
        237141736098300*J12*I09*I03^3 - 56387778534259200*I15*I06*I03^3 +
        6090612572380024800*J09*I06^2*I03^3 -
        5500790970377911200*I09*I06^2*I03^3 + 68102549871435*J09^2*I03^4 +
        662972297503050*J09*I09*I03^4 + 118696131135*I09^2*I03^4 +
        12500517254050800*J12*I06*I03^4 - 398504925755229283200*I06^3*I03^4 +
        172387207601280*I15*I03^5 + 5211890028692280*J09*I06*I03^5 -
        45067918714106040*I09*I06*I03^5 - 18318944284920*J12*I03^6 -
        1511287689908059920*I06^2*I03^6 - 107238040541064*J09*I03^7 -
        97019675197632*I09*I03^7 + 2942379575462880*I06*I03^8 +
        13015889753920*I03^10,
    1881249305370624000*I15^2 - 36835238592000*J12*J09*I09 +
        73670477184000*J12*I09^2 - 91122687527832576000*I15*I09*I06 -
        6302496274046370720000*J09^2*I06^2 +
        7343659283822009280000*J09*I09*I06^2 -
        1053952849554572448000*I09^2*I06^2 + 8100590088072038400000*J12*I06^3 -
        26880811415467090329600000*I06^5 + 379461597091200*J09^2*I09*I03 -
        1441106307964800*J09*I09^2*I03 + 1364366227564800*I09^3*I03 -
        27074852588349216000*J12*J09*I06*I03 +
        15737118660544032000*J12*I09*I06*I03 -
        74563394386618368000*I15*I06^2*I03 +
        592824874015923102720000*J09*I06^3*I03 -
        350555677178943656448000*I09*I06^3*I03 -
        2962460676550233600*I15*I09*I03^2 - 110124226137124936800*J09^2*I06*I03\
        ^2 + 235661265454642977600*J09*I09*I06*I03^2 -
        29077257373903202400*I09^2*I06*I03^2 +
        1479278875290936192000*J12*I06^2*I03^2 -
        15196791075530172931584000*I06^4*I03^2 -
        310077498860571600*J12*J09*I03^3 + 392629161895131600*J12*I09*I03^3 +
        41151994759016064000*I15*I06*I03^3 +
        9362693411904023913600*J09*I06^2*I03^3 -
        11852199469919356444800*I09*I06^2*I03^3 - 437761349044794045*J09^2*I03^4
        + 1479118050582506910*J09*I09*I03^4 - 10667046833444565*I09^2*I03^4 +
        13506068566478880000*J12*I06*I03^4 -
        215028671745744751680000*I06^3*I03^4 + 809391603752807040*I15*I03^5 -
        290806759029311640*J09*I06*I03^5 - 94583634731379032760*I09*I06*I03^5 -
        67891804847395560*J12*I03^6 + 1135325016921787421040*I06^2*I03^6 -
        297894375836543952*J09*I03^7 - 193643793119223576*I09*I03^7 +
        21352242679028274240*I06*I03^8 + 46249614823578560*I03^10
        ],
        [ 4, 5, 6, 6, 7, 7, 8, 8, 9, 9, 9, 10, 10 ];

end function;

/*
Quartics in the singularity strata
	_ Irreducible : [ "(A1A2)" ] + ...
        _ Reducible   : [] + ...

Dimension 3 (vs 3)
 */
 function A1A2Stratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
    486*I12 - 155520*I06^2 - 423*J09*I03 + 117*I09*I03 + 14418*I06*I03^2 +
        8*I03^4,
    4860*J15 + 43740*I15 - 2566080*J09*I06 + 408240*I09*I06 - 7290*J12*I03 +
        127370880*I06^2*I03 - 18729*J09*I03^2 - 207*I09*I03^2 +
        1333260*I06*I03^3 + 2960*I03^5,
    7348320*I18 - 17721585*J09^2 + 7966350*J09*I09 - 847665*I09^2 -
        57736800*J12*I06 + 144992851200*I06^3 + 7348320*I15*I03 +
        1100022120*J09*I06*I03 - 498645720*I09*I06*I03 - 1443420*J12*I03^2 -
        1085276880*I06^2*I03^2 - 2388726*J09*I03^3 - 2446938*I09*I03^3 +
        354048840*I06*I03^4 + 1259360*I03^6,
    22044960*J18 - 3064635*J09^2 - 3815910*J09*I09 + 1289925*I09^2 -
        47239200*J12*I06 - 112240339200*I06^3 + 198404640*I15*I03 -
        11840038920*J09*I06*I03 + 2097274680*I09*I06*I03 - 32673780*J12*I03^2 +
        585714116880*I06^2*I03^2 - 86498514*J09*I03^3 - 483102*I09*I03^3 +
        6114498840*I06*I03^4 + 13438240*I03^6,
    3968092800*I21 + 24538140*J12*J09 - 165993300*J12*I09 -
        2955435517440*I15*I06 + 171755385400800*J09*I06^2 -
        29477522190240*I09*I06^2 - 968897295*J09^2*I03 + 334009494*J09*I09*I03 -
        20933883*I09^2*I03 + 367100547120*J12*I06*I03 -
        8360086183286400*I06^3*I03 - 12962436480*I15*I03^2 +
        2300125199400*J09*I06*I03^2 - 154941689160*I09*I06*I03^2 +
        1617796800*J12*I03^3 - 133524847632240*I06^2*I03^3 +
        6574736448*J09*I03^4 - 70085376*I09*I03^4 - 622640183040*I06*I03^5 -
        879157760*I03^7,
    1102248000*J21 - 4233157200*J12*J09 - 249318000*J12*I09 -
        7870050720000*I15*I06 + 464228751312000*J09*I06^2 -
        81624361737600*I09*I06^2 + 7163255655*J09^2*I03 - 1133586090*J09*I09*I03
        - 47536065*I09^2*I03 + 1044600429600*J12*I06*I03 -
        22516130457273600*I06^3*I03 - 27468020160*I15*I03^2 +
        5262731160840*J09*I06*I03^2 - 311423755320*I09*I06*I03^2 +
        3218797440*J12*I03^3 - 330803613383760*I06^2*I03^3 +
        14030218368*J09*I03^4 - 171657216*I09*I03^4 - 1426451938560*I06*I03^5 -
        1839011840*I03^7,
    13286025*J12^2 - 1003045680*I15*J09 - 77157360*I15*I09 +
        58364720505*J09^2*I06 - 5603553270*J09*I09*I06 - 776395935*I09^2*I06 -
        44003314800*J12*I06^2 + 36434744654400*I06^4 + 92575710*J12*J09*I03 +
        16796160*J12*I09*I03 + 52775634240*I15*I06*I03 -
        5855427173160*J09*I06^2*I03 + 300837333960*I09*I06^2*I03 +
        531834255*J09^2*I03^2 + 22938876*J09*I09*I03^2 + 378918*I09^2*I03^2 -
        6048979560*J12*I06*I03^2 + 148460792671440*I06^3*I03^2 +
        137168640*I15*I03^3 - 68380380792*J09*I06*I03^3 -
        596660256*I09*I06*I03^3 - 18837360*J12*I03^4 + 2122728968880*I06^2*I03^4
        - 136117872*J09*I03^5 - 4667616*I09*I03^5 + 8042068800*I06*I03^6 +
        9386560*I03^8,
    I27,
    71980619288739840000*I15^3 + 242246283361920000*I15*J12*J09^2 -
        104770876896000*J09^5 - 245965520056320000*I15*J12*J09*I09 +
        729864535680000*J09^4*I09 + 65210616708480000*I15*J12*I09^2 -
        1889142847200000*J09^3*I09^2 + 2199778378560000*J09^2*I09^3 -
        1103394337920000*J09*I09^4 + 195653428992000*I09^5 -
        12092744040508293120000*I15^2*J09*I06 -
        13842849173967720000*J12*J09^3*I06 +
        1835505791862865920000*I15^2*I09*I06 +
        15988518147819240000*J12*J09^2*I09*I06 -
        5694073895028600000*J12*J09*I09^2*I06 + 527351604020280000*J12*I09^3*I06
        + 676315759786782105600000*I15*J09^2*I06^2 -
        204848166260392888320000*I15*J09*I09*I06^2 +
        15391962871925667840000*I15*I09^2*I06^2 +
        6940988288557056000000*I15*J12*I06^3 -
        12589161859787218585920000*J09^3*I06^3 +
        5705724582621143887680000*J09^2*I09*I06^3 -
        855590062157009334720000*J09*I09^2*I06^3 +
        42527297954565236160000*I09^3*I06^3 -
        365269508685315072000000*J12*J09*I06^4 +
        51189788628108288000000*J12*I09*I06^4 -
        15692186322769792204800000*I15*I06^5 +
        827530999517268733132800000*J09*I06^6 -
        116565569120369487052800000*I09*I06^6 -
        31491520938823680000*I15^2*J12*I03 - 2482171888065120000*I15*J09^3*I03 +
        2286889309467936000*I15*J09^2*I09*I03 -
        425131253256096000*I15*J09*I09^2*I03 - 71497657272096000*I15*I09^3*I03 +
        3514491226678602240000*I15*J12*J09*I06*I03 +
        144187710347415870000*J09^4*I06*I03 -
        526867070128704000000*I15*J12*I09*I06*I03 -
        157366743171969456000*J09^3*I09*I06*I03 +
        47383381475503452000*J09^2*I09^2*I06*I03 -
        175808335550400000*J09*I09^3*I06*I03 - 669190053349386000*I09^4*I06*I03
        + 596755324213297643520000*I15^2*I06^2*I03 -
        97355804840016397920000*J12*J09^2*I06^2*I03 +
        28732704347687826240000*J12*J09*I09*I06^2*I03 -
        2028040199681931360000*J12*I09^2*I06^2*I03 -
        66891714399969520619520000*I15*J09*I06^3*I03 +
        10115510765774268026880000*I15*I09*I06^3*I03 +
        1872002282615789442428160000*J09^2*I06^4*I03 -
        564953260878781349598720000*J09*I09*I06^4*I03 +
        42293569038128865619200000*I09^2*I06^4*I03 +
        17398975342925972275200000*J12*I06^5*I03 -
        38994033534653703802060800000*I06^7*I03 +
        242612454611939328000*I15^2*J09*I03^2 +
        113793124505719500*J12*J09^3*I03^2 +
        26437326220247040000*I15^2*I09*I03^2 -
        71740266200167500*J12*J09^2*I09*I03^2 -
        14869262937901500*J12*J09*I09^2*I03^2 +
        13154453760145500*J12*I09^3*I03^2 - 27690181066783476288000*I15*J09^2*I\
        06*I03^2 + 1445329205212828032000*I15*J09*I09*I06*I03^2 +
        515565370485627840000*I15*I09^2*I06*I03^2 -
        158509678567115427840000*I15*J12*I06^2*I03^2 +
        782893075790475612828000*J09^3*I06^2*I03^2 -
        161565453621340239132000*J09^2*I09*I06^2*I03^2 -
        10333144682571095244000*J09*I09^2*I06^2*I03^2 +
        2306222653975132140000*I09^3*I06^2*I03^2 +
        8849095258070359094400000*J12*J09*I06^3*I03^2 -
        1323729085007912641920000*J12*I09*I06^3*I03^2 +
        1640600704438232753848320000*I15*I06^4*I03^2 -
        92020813440141479814282240000*J09*I06^5*I03^2 +
        13869489929149706648785920000*I09*I06^5*I03^2 -
        18466404151286592000*I15*J12*J09*I03^3 + 1310104020929545575*J09^4*I03^3
        - 7032214277195328000*I15*J12*I09*I03^3 -
        1246016262711745800*J09^3*I09*I03^3 +
        264469716087749550*J09^2*I09^2*I03^3 + 26669098246597200*J09*I09^3*I03^3
        - 13569437400525*I09^4*I03^3 - 11301557066826227712000*I15^2*I06*I03^3 +
        1059985898972783298000*J12*J09^2*I06*I03^3 +
        221926105058463252000*J12*J09*I09*I06*I03^3 -
        61889349962995470000*J12*I09^2*I06*I03^3 +
        2585167998627128025600000*I15*J09*I06^2*I03^3 -
        68768801726203703808000*I15*I09*I06^2*I03^3 -
        110614964821173143491248000*J09^2*I06^3*I03^3 +
        15780073137292074690720000*J09*I09*I06^3*I03^3 +
        407445643833006900816000*I09^2*I06^3*I03^3 -
        199812690459107367068160000*J12*I06^4*I03^3 +
        1497280045748888305612615680000*I06^6*I03^3 -
        183259701609428217600*I15*J09^2*I03^4 +
        8956459271625062400*I15*J09*I09*I03^4 +
        1574089886414995200*I15*I09^2*I03^4 +
        954183662380065024000*I15*J12*I06*I03^4 +
        10163701666365442812000*J09^3*I06*I03^4 -
        1990215931775346867600*J09^2*I09*I06*I03^4 -
        18917112454422782400*J09*I09^2*I06*I03^4 +
        14051252261588151600*I09^3*I06*I03^4 -
        103119612401935353528000*J12*J09*I06^2*I03^4 -
        8561649822680153880000*J12*I09*I06^2*I03^4 -
        60221362772518373698560000*I15*I06^3*I03^4 +
        5156088637445728143128640000*J09*I06^4*I03^4 -
        370543229860968223231680000*I09*I06^4*I03^4 -
        32540250914983526400*I15^2*I03^5 + 6185792686959201600*J12*J09^2*I03^5 -
        703395592414358400*J12*J09*I09*I03^5 -
        352247457555576000*J12*I09^2*I03^5 +
        23996761197622348492800*I15*J09*I06*I03^5 -
        777658837998638131200*I15*I09*I06*I03^5 -
        1719524779043857871580000*J09^2*I06^2*I03^5 +
        244439204772133949040000*J09*I09*I06^2*I03^5 +
        21631772834389317600*I09^2*I06^2*I03^5 +
        2481617073250781526240000*J12*I06^3*I03^5 -
        79955088428380498718079744000*I06^5*I03^5 +
        4481529977956147200*I15*J12*I03^6 + 18083062380700473120*J09^3*I03^6 -
        9639423782835452640*J09^2*I09*I03^6 - 538563172352758560*J09*I09^2*I03^6
        - 12226143419016480*I09^3*I03^6 - 912534347133167731200*J12*J09*I06*I03\
        ^6 + 77391741898070668800*J12*I09*I06*I03^6 -
        733069439853150808166400*I15*I06^2*I03^6 +
        94051896726020932473868800*J09*I06^3*I03^6 -
        7092390937056646930041600*I09*I06^3*I03^6 +
        39475797366214287360*I15*J09*I03^7 - 1278283491000483840*I15*I09*I03^7 -
        5415177268972359054720*J09^2*I06*I03^7 +
        1478203124668458888960*J09*I09*I06*I03^7 +
        29433848152050967680*I09^2*I06*I03^7 +
        28901410555650973516800*J12*I06^2*I03^7 -
        1682191479799092665396793600*I06^4*I03^7 -
        1127160947822054400*J12*J09*I03^8 + 319385734086804480*J12*I09*I03^8 -
        2293145176516744642560*I15*I06*I03^8 +
        416710329944916109800960*J09*I06^2*I03^8 -
        53010194810628308590080*I09*I06^2*I03^8 -
        3265042649062070016*J09^2*I03^9 + 2592275733841927680*J09*I09*I03^9 +
        103891355135218944*I09^2*I03^9 + 60389900285622128640*J12*I06*I03^9 -
        9473459346697536495912960*I06^3*I03^9 - 2212009181969448960*I15*I03^10 +
        527239199777544603648*J09*I06*I03^10 -
        170305342967625025536*I09*I06*I03^10 + 7436179772375040*J12*I03^11 -
        17788649424269858795520*I06^2*I03^11 - 34857679187976192*J09*I03^12 -
        196749351885643776*I09*I03^12 + 1063677688079155200*I06*I03^13 +
        24074171839938560*I03^15
        ],
        [ 4, 5, 6, 6, 7, 7, 8, 9, 15 ];

end function;

/*  Quartics in the singularity strata
	_ Irreducible :
        _ Reducible   : [ "(A1^3)" ] + RedA1p5Stratum + RedA1p3A2Stratum;

    Dimension 3 (vs 3)
*/

function RedA1p3Stratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
        144*I06 + I03^2,
        9*J09 - 18*I09 + 5*I03^3,
        54*J12 - 81*I12 + 9*I09*I03 - 2*I03^4,
        1944*I15 - 729*I12*I03 + 54*I09*I03^2 - 40*I03^5,
        648*J15 + 81*I12*I03 + 324*I09*I03^2 - 50*I03^5,
        6561*J18 - 729*I18 + 1620*I12*I03^2 + 2970*I09*I03^3 - 490*I03^6,
        2916*I21 - 729*I12*I09 - 1458*I09^2*I03 + 162*I12*I03^3 + 612*I09*I03^4 - 64*I03^7,
        209952*J21 + 11664*I18*I03 + 1469664*I09^2*I03 + 15633*I12*I03^3 - 594270*I09*I03^4 + 58816*I03^7,
        I27
        ],
        [ 2, 3, 4, 5, 5, 6, 7, 7, 9 ];

end function;

/*
	Dimension 3 ? (vs 3)
 */
function A1p3Stratum(DO)

    I03, I06, I09, J09, I12, J12, I15, J15, I18, J18, I21, J21, I27 := Explode(DO);

    return [
        19252335960000*J12^2 - 147601242360000*J12*I12 + 178084107630000*I12^2 - 3225130682029200*J15*J09 + 589398771855600*I15*J09 + 1973286436690800*J15*I09 - 339575842544400*I15*I09 +
        253379315214648000*J18*I06 - 30948411207672000*I18*I06 + 28586809024200000*J09^2*I06 - 61981133062766400*J09*I09*I06 + 9615030028732800*I09^2*I06 + 818984390410368000*J12*I06^2 -
        13821912620857152000*I12*I06^2 - 1230524987355836928000*I06^4 + 187016045265000*J21*I03 - 3090808105560000*I21*I03 + 481769827350300*J12*J09*I03 - 933613731871200*I12*J09*I03 -
        574878778470000*J12*I09*I03 + 1167634132848000*I12*I09*I03 - 198358993838502000*J15*I06*I03 + 35757129862566000*I15*I06*I03 - 2926537712188070400*J09*I06^2*I03 +
        3395339620837819200*I09*I06^2*I03 + 3019646086758000*J18*I03^2 - 344537242969500*I18*I03^2 + 474283598974965*J09^2*I03^2 - 769429515793005*J09*I09*I03^2 + 345307281153750*I09^2*I03^2 -
        222683958858060000*I12*I06*I03^2 + 18768367248103872000*I06^3*I03^2 - 3684192485041215*J15*I03^3 + 708527565466245*I15*I03^3 - 23679497720864160*J09*I06*I03^3 +
        36382949793725220*I09*I06*I03^3 + 232314149826990*J12*I03^4 - 1362254657086260*I12*I03^4 - 134477400433173840*I06^2*I03^4 - 5580869501403*J09*I03^5 - 68777819408529*I09*I03^5 -
        892394506110240*I06*I03^6 - 2885738380000*I03^8,
        -712179690854400*J12^2 + 5460044296550400*J12*I12 - 6587662140403200*I12^2 + 7429553156309760*J15*J09 - 5820952464794880*I15*J09 - 8226360482215680*J15*I09 + 3308802646544640*I15*I09 -
        1196915237883187200*J18*I06 + 236388522288844800*I18*I06 - 135943786776591360*J09^2*I06 + 292336465725158400*J09*I09*I06 - 40897784343951360*I09^2*I06 - 3301790240002867200*J12*I06^2 +
        71088969634537881600*I12*I06^2 + 2146334713943054745600*I06^4 - 3538418097564000*J21*I03 + 33223064190624000*I21*I03 + 8732497566848400*J12*J09*I03 - 13950648070957440*I12*J09*I03 +
        2765363561940960*J12*I09*I03 - 6242083826924160*I12*I09*I03 + 732173594602705920*J15*I06*I03 - 265567230374866560*I15*I06*I03 + 7000420564764103680*J09*I06^2*I03 -
        7388853488107499520*I09*I06^2*I03 - 1187667596682000*J18*I03^2 + 653425535196000*I18*I03^2 - 8283042786246444*J09^2*I03^2 - 542365595086356*J09*I09*I03^2 - 687149372854152*I09^2*I03^2
        + 29150848407754080*J12*I06*I03^2 + 539416451971010880*I12*I06*I03^2 + 69326520304869918720*I06^3*I03^2 + 4825971532746000*J15*I03^3 + 189284540292714384*J09*I06*I03^3 -
        20318739502149648*I09*I06*I03^3 - 715736177411850*J12*I03^4 + 2226178564614900*I12*I03^4 + 1006281556959409920*I06^2*I03^4 + 195795118443645*J09*I03^5 + 114079902258735*I09*I03^5 +
        2031659900814600*I06*I03^6 + 17004784384000*I03^8,
        -10477492226888601600*J09^3 + 47975885459963596800*J09^2*I09 - 66173635117191168000*J09*I09^2 + 24263666209636761600*I09^3 + 7956345659793531840000*J21*I06 -
        30150362500270225920000*I21*I06 - 21697493013587323296000*J12*J09*I06 + 36419723591596257024000*I12*J09*I06 - 6999191294705588160000*J12*I09*I06 + 10289409424695394560000*I12*I09*I06 +
        2699685791876048080896000*J15*I06^2 + 364819386253269733632000*I15*I06^2 + 4531934487818395736064000*J09*I06^3 - 30884691329165696311296000*I09*I06^3 + 7915148083754496000*J12^2*I03 -
        60682801975451136000*J12*I12*I03 + 73215119774729088000*I12^2*I03 + 391247211129576076800*J15*J09*I03 + 25365614998275417600*I15*J09*I03 - 353917111898774592000*J15*I09*I03 -
        29873542883171904000*I15*I09*I03 - 120861676688165209440000*J18*I06*I03 + 12721932150587714880000*I18*I06*I03 + 1828962364319844062400*J09^2*I06*I03 +
        28316566788827746363200*J09*I09*I06*I03 - 1578411719891738928000*I09^2*I06*I03 - 1306399881967971844032000*J12*I06^2*I03 + 7986632991035701919616000*I12*I06^2*I03 +
        352758059168413274320896000*I06^4*I03 + 83900286837761940000*J21*I03^2 - 322345671349655520000*I21*I03^2 - 365393586458968945200*J12*J09*I03^2 + 622661766571970870400*I12*J09*I03^2 +
        46645084189293400800*J12*I09*I03^2 - 98929677373395638400*I12*I09*I03^2 + 139853378261939359046400*J15*I06*I03^2 - 26899954244440794115200*I15*I06*I03^2 +
        764891941253075527852800*J09*I06^2*I03^2 - 1295292025385573896800000*I09*I06^2*I03^2 - 1088276199294004434000*J18*I03^3 + 117600411410403516000*I18*I03^3 +
        91959072519376930500*J09^2*I03^3 + 284357406918096125820*J09*I09*I03^3 - 87451771676078811240*I09^2*I03^3 - 11672518332516132470400*J12*I06*I03^3 +
        108954606769937830137600*I12*I06*I03^3 - 22149988445113582233600*I06^3*I03^3 + 1181161579207597144080*J15*I03^4 - 278306228052935893440*I15*I03^4 - 7934648192527741876800*I09*I06*I03^4
        - 53206363619659940130*J12*I03^5 + 434781544050992947620*I12*I03^5 + 81845532660920485860480*I06^2*I03^5 - 17373231141250030039*J09*I03^6 + 24938852997698096723*I09*I03^6 +
        392954550646103227880*I06*I03^7,
        -1412051703738394278583296000*J15*J12 + 4712722561226890904771750400*J15*I12 - 370663572231328498128115200*I15*I12 - 1667986075040978241576518400*J18*J09 +
        185331786115664249064057600*I18*J09 - 172151520050336314401768960*J09^3 + 301761758211459676004206080*J09^2*I09 + 117444063295540072548172800*J09*I09^2 -
        64722999034228333899018240*I09^3 - 16659013257449249480055360000*J21*I06 + 22996896553558581691000320000*I21*I06 + 42712853194774441885809657600*J12*J09*I06 +
        14722284352309978162245811200*I12*J09*I06 + 16887130991222252528109888000*J12*I09*I06 - 25571077132381767020464819200*I12*I09*I06 - 7235175877367281293358721433600*J15*I06^2 -
        195233808118241254880406067200*I15*I06^2 + 1181430089806706927988240384000*J09*I06^3 + 89801239280115177189138187468800*I09*I06^3 + 552569475864744377816025600*J12^2*I03 -
        3362658989941575436716115200*J12*I12*I03 + 4264036629505848927648259200*I12^2*I03 + 1959977513046240929369197440*J15*J09*I03 + 168947168179399611577591680*I15*J09*I03 +
        570172259553233271103330560*J15*I09*I03 - 224792213117031591000641280*I15*I09*I03 + 243456439167966276789495840000*J18*I06*I03 - 45600159015000470894932800000*I18*I06*I03 +
        7907575957440120593637969600*J09^2*I06*I03 - 63816297515058819802341977280*J09*I09*I06*I03 - 1466112666622978994436512640*I09^2*I06*I03 + 2381249998125849231646177651200*J12*I06^2*I03
        - 15385452215023015463722572518400*I12*I06^2*I03 - 632765180817765586768522538188800*I06^4*I03 + 368278498708715593223316000*J21*I03^2 - 2643514100389151415355104000*I21*I03^2 -
        1530028944672697102983467760*J12*J09*I03^2 + 3299966600733437976631581120*I12*J09*I03^2 - 315397233807449098382860320*J12*I09*I03^2 + 984152542282385583472211520*I12*I09*I03^2 -
        189925091365282708273668748800*J15*I06*I03^2 + 94394915532712758768767222400*I15*I06*I03^2 - 889700367289759649512376382720*J09*I06^2*I03^2 +
        654086163152492340324062158080*I09*I06^2*I03^2 - 1891739227168772131739878800*J18*I03^3 + 108264672284735627436535200*I18*I03^3 + 666723295458635551555753188*J09^2*I03^3 +
        641754826202743385771512476*J09*I09*I03^3 - 90322290577854945764155944*I09^2*I03^3 - 4359793254001764912007718400*J12*I06*I03^3 - 14087064559409427986831386368000*I06^3*I03^3 +
        1885789684214500034043108000*J15*I03^4 - 415125920436821581792014000*I15*I03^4 - 23551387290067155853004415360*I09*I06*I03^4 - 89057397036842060623357050*J12*I03^5 +
        661873989781454087608607700*I12*I03^5 - 163210842426861781057252454400*I06^2*I03^5 - 25300491361409581445271115*J09*I03^6 + 43298171655209070231260055*I09*I03^6 +
        713875248788868648826297800*I06*I03^7,
        88554951933166393325683200*J15*J12 + 14935162251079170254246400*I15*J12 + 226290337137563185670400*J15*I12 - 41411131696174062977683200*I15*I12 - 379019036580383259970560*J09^3 +
        1201939425196342784179200*J09^2*I09 - 259529261820772017070080*J09*I09^2 - 1256546884500761022812160*I09^3 - 1764447201653521586668992000*J21*I06 +
        13374992202921528384877056000*I21*I06 + 5477380377824391715974355200*J12*J09*I06 - 9574885621651602992439168000*I12*J09*I06 + 507613068966729576560371200*J12*I09*I06 -
        1387537544350445624104550400*I12*I09*I06 - 405724493149339732866138009600*J15*I06^2 - 138190970585823690807198259200*I15*I06^2 - 500547706942646099164151808000*J09*I06^3 +
        4513181262283726799224821350400*I09*I06^3 - 18966920357262582315360000*J12^2*I03 - 16874830711475933572195200*J12*I12*I03 + 91748302270498845063244800*I12^2*I03 +
        6099271424251031405514240*J15*J09*I03 + 45133125761682333317537280*I15*J09*I03 + 4601472933151484734337280*J15*I09*I03 - 21595316755611631071594240*I15*I09*I03 +
        11361106382552871890409273600*J18*I06*I03 - 2290996087234901918360294400*I18*I06*I03 - 2639977096010166704516356800*J09^2*I06*I03 - 3551251260041134776438338880*J09*I09*I06*I03 +
        534180028523439906572146560*I09^2*I06*I03 + 156317659210600495509933964800*J12*I06^2*I03 - 760201079607499431663022464000*I12*I06^2*I03 - 162410052445386180582415564800*I06^4*I03 +
        13944486351486522616092000*J21*I03^2 - 70547271205725938919456000*I21*I03^2 - 25541426800949782756346640*J12*J09*I03^2 + 50565055977911059236748800*I12*J09*I03^2 +
        2622513246224037967487520*J12*I09*I03^2 + 18339586990585426695133440*I12*I09*I03^2 - 9018223171067372502740371200*J15*I06*I03^2 + 2252258262522670346858793600*I15*I06*I03^2 +
        10681261276630602376898484480*J09*I06^2*I03^2 + 44942861191159771855592774400*I09*I06^2*I03^2 - 72414843111670528828875600*J18*I03^3 + 2358106191090355862822400*I18*I03^3 +
        24998272555997743111480428*J09^2*I03^3 + 15959771923041871612705620*J09*I09*I03^3 - 3718648241452923082161912*I09^2*I03^3 - 510094394371891269144691200*J12*I06*I03^3 +
        23403615396706967978978150400*I06^3*I03^3 + 70608670079620438364635680*J15*I03^4 - 20192596520263561358652240*I15*I03^4 - 897869789005587846097789440*I09*I06*I03^4 -
        2568668968965489885117630*J12*I03^5 + 23636308275303729694798620*I12*I03^5 - 2806585530153568535070222720*I06^2*I03^5 - 1013599644392699650928089*J09*I03^6 +
        1227485461268934204644573*I09*I03^6 + 33632948342175009851833880*I06*I03^7,
        -53657964742058982586165248000*J15*J12 + 179083457326621854381326515200*J15*I12 - 14085215744790482928868377600*I15*I12 + 1770785076584482270984627200*J09^3 -
        36695693650901521314683404800*J18*I09 + 4077299294544613479409267200*I18*I09 - 12510533598398355329703936000*J09^2*I09 + 20638114885490407108181683200*J09*I09^2 -
        5400375990063251065424640000*I09^3 - 925141409494027795308423744000*J21*I06 + 3606129014927201765173366272000*I21*I06 + 2560746571583737578161896339200*J12*J09*I06 -
        4318251255788738990147088768000*I12*J09*I06 + 726190173171512287883701056000*J12*I09*I06 + 757456972936826303629672934400*I12*I09*I06 - 265760462345914965249033847603200*J15*I06^2 -
        13097413345913374368811089254400*I15*I06^2 - 406349679889082038771059742310400*J09*I06^3 + 3753705210452901494222020046438400*I09*I06^3 + 19565746853450188889260339200*J12^2*I03 -
        122522002925776282837401868800*J12*I12*I03 + 157366593649389602916352512000*I12^2*I03 - 21489531782324480477991118080*J15*J09*I03 + 26938652597992099144241591040*I15*J09*I03 +
        71790733246561528253569885440*J15*I09*I03 - 18752733083510834059542885120*I15*I09*I03 + 7583271251641979230326254227200*J18*I06*I03 - 1533721097576486481849722188800*I18*I06*I03 -
        1194274936072336481443537853760*J09^2*I06*I03 - 853015250211463973337405347520*J09*I09*I06*I03 - 671809269019721175683765147520*I09^2*I06*I03 +
        92889227054204187610703334566400*J12*I06^2*I03 - 488791734600452245618383420134400*I12*I06^2*I03 - 19583415047350142847225503590809600*I06^4*I03 +
        11568319273364046246193140000*J21*I03^2 - 86918005883892551942611296000*I21*I03^2 - 39483347850750425631445998000*J12*J09*I03^2 + 70220588233813072009632152640*I12*J09*I03^2 -
        14886384986967097695350914080*J12*I09*I03^2 + 55282852601308774241563285440*I12*I09*I03^2 - 4399379983420942202093738073600*J15*I06*I03^2 +
        2905939669694843296220131036800*I15*I06*I03^2 - 14194401803691324584061504994560*J09*I06^2*I03^2 + 11771233154615749666289396716800*I09*I06^2*I03^2 -
        47050858036431891893263446000*J18*I03^3 + 1427927949945230365500624000*I18*I03^3 + 20001275653501110922403296932*J09^2*I03^3 + 14109145682698337355889596828*J09*I09*I03^3 -
        222165433707914592563892264*I09^2*I03^3 - 393897771721052950894176211200*J12*I06*I03^3 - 170297622921798473155609640601600*I06^3*I03^3 + 46421096287033053262411983360*J15*I03^4 -
        9115685687709137472076950480*I15*I03^4 - 487657988436469600885487022720*I09*I06*I03^4 - 2419088108263116761485026810*J12*I03^5 + 15971399347328734767075977940*I12*I03^5 -
        4689500565901293181164952391040*I06^2*I03^5 - 772455693130229331950425643*J09*I03^6 + 1203994941701874385269140151*I09*I03^6 + 26062013879376093775634527560*I06*I03^7,
        I27,
        -289795242137116437488196811408451125080300620382543458400978675952464721920*J15*I15 - 59256677633412463473832116903805393748015211197794511743795899348581283840*I15^2 +
        304646470605506739565645173260763759120323371039134162403698771457107576960*J18*J12 - 39921129882920484618120405357143476845173962389854384057149493847799678080*I18*J12 -
        254096069845790554820338045256295476765693225474965053845977112904602028480*J18*I12 + 37340179706328554201832861965176308388339629019921999445771902518248479680*I18*I12 -
        46312640927991970333072276649372313513493795689113322190081301182409857440*J21*J09 + 840350518962924959307786125078696574142906664250843353749028630463882059520*I21*J09 +
        199612085821959953008057422891505730009174010679767105081232232352674212464*J12*J09^2 - 391733918353256689120607114959903535291383723366453844722178078395667008896*I12*J09^2 +
        89725343175756857036279667636902574969755148229761318656068718864809373280*J21*I09 - 973592695624660988195366119815362686572741304127040458828926203241471453440*I21*I09 -
        374968741849324302862603166886282448939750749839605136347400664643030223856*J12*J09*I09 + 671995568641767345084563750129860068706238447491406135750569211772259083264*I12*J09*I09 -
        309451921167393173276943551431481101999807136130155361328302338017179744*J12*I09^2 - 26134660947840885992370194368653423258002111466250443182907821063352130944*I12*I09^2 -
        1606625764916209071787623299878129430806124889688114994269667686292542156800*J12^2*I06 - 7259623401845093972586029157998059626140837489957172631408593317889303321600*I12^2*I06 +
        2859571710016886540328129604608549967209141827255581334382592368436339607040*J15*J09*I06 - 15026232542297793177839035670107918334457901696441877712585750303493923457920*I15*J09*I06 -
        9065274358193110183470731379525472414112811390691830748120467460105567102080*J15*I09*I06 + 11272567527137035482919421740663314778484974299247174782209948287203380835840*I15*I09*I06 +
        133197687513852129351311758318104765776006325051405071670564670855456999587840*I18*I06^2 - 21441369246061853254899496723819069429434297263556197894746514997665406528000*J09^2*I06^2 -
        4657102732538684252230429069068440195812843908986731974812574515940798266572800*J12*I06^3 + 16806807093372716956298767044314287307921177448044605875303700820309166237081600*I12*I06^3 +
        202594340149182362675345704791332283678825193302276453702573867869002767360*I15*J12*I03 + 104079806908743151049725469167949259041700947530160793411517398235896142080*J15*I12*I03 -
        256273856417377681912615045917852945787281346086698132317775713989640078080*I15*I12*I03 + 194676843132349985885319809494575983284691823410710766325695679209378517552*J18*J09*I03 -
        26025141455397695294565276700591155531923489821792668405992259083612256000*I18*J09*I03 - 136432388242245647012921967078658182756949644933296039511019349641504216116*J09^3*I03 -
        469773780706760312858541393001234597623473747439404482058325693410955743184*J18*I09*I03 + 59812820915812116026915322144394201761376627491602863203811882727966580480*I18*I09*I03 +
        98397478062818990743111857554671253510540923599187897446793454618943262080*J09^2*I09*I03 + 183349652235087241879122838968167532273477083768606941526351154923299332732*J09*I09^2*I03 -
        34650284750998685724183567289326454948151360710222895776810828235786838456*I09^3*I03 - 2952506083339106912840009063449939112086912345170043541008380499494009926400*J21*I06*I03 +
        10330133346080502804736034733010215307505159103878373708953171305664768179200*I21*I06*I03 + 289866219554083969666394324408383411907912720161848370690279366492077578400*J12*J09*I06*I03
        + 7159884788281981221597778032268160650862925827977039836047106941551275660000*J12*I09*I06*I03 -
        873202204671293921194801938119426808655146145237536980589650934585341100288000*J15*I06^2*I03 +
        189745680232914544417843585929604101482386492546323560283584692783680723747840*I15*I06^2*I03 +
        823168039362932672542430868794081774428872535195029174499641506954150097054720*J09*I06^3*I03 +
        8247514162029977477885710266732382436406094124599267024972204371307327209538560*I09*I06^3*I03 - 87692502139305891250951496082627917774222046429991166570462725744403915520*J12^2*I03^2 +
        107856653770686603014279734339834674079594412676991399631311597665142510080*J12*I12*I03^2 - 381179190183041673883764334817271024378178554536304375758011105097407379520*J15*J09*I03^2 +
        19362092685651418179255145522561776968637115777937416612130261337849778128*I15*J09*I03^2 + 385217852748273122432913824192462066300098005242263773666361634023503505320*J15*I09*I03^2 -
        172810637822699700585201837700162803832160755784953031198891304752786038536*I15*I09*I03^2 + 4127843528961073948006372576808221428848892665034857869798361481725155233120*J18*I06*I03^2 -
        134408497479692215835180048183818975258425234638789759025159488423457846240*I18*I06*I03^2 - 3102557149829316083495570846750410531711293172585100169959257483013587005744*J09^2*I06*I03^\
        2 - 1589080748192989840093309651272722497040219364970721738631529169718365400384*J09*I09*I06*I03^2 -
        5081253284404748452382486734029277437935398768981614179255098377892694942256*I09^2*I06*I03^2 +
        392469815825957220643011700463782429059928488274813292693605253718660610993920*J12*I06^2*I03^2 -
        856924768270433017477532110574129943228157716686129320794895892167044074188800*I12*I06^2*I03^2 -
        127813039679462446880533049825570845706663676920229792288066445823043836886220800*I06^4*I03^2 + 53194162706158625273954828998101758336613500725133275674657882831107515200*I21*I03^3 +
        122746141228933895301855354310153451461130573285420929741276069791797394714*J12*J09*I03^3 - 210203697984513635412212236614336716016038114774434288961213872059897292560*I12*J09*I03^3 +
        25577727606688693370477815893869122079325466665684913470769685596953946302*J12*I09*I03^3 + 118301939104706830707662751416652378438033490542468361658725584529484137920*I12*I09*I03^3 +
        4467854169314560265042640959938089483287840726992827250986069293187253630080*J15*I06*I03^3 + 34118064084847680073739772935220271477194323595586275366503450843637120270*J18*I03^4 -
        7610688508396303109916106266826358553929819143290767216956849598909289630*I18*I03^4 - 36608183518619902773054692189879098075568853586664943951653276208694110855*J09^2*I03^4 -
        54080185216484202431912048318354075202906325634821438904858449577060548530*J09*I09*I03^4 + 13148566485439158660903163659555004964649522959624766268689633331531555905*I09^2*I03^4 -
        3001380107942939709940088660937520436623004449155824543999089390396255677840*J12*I06*I03^4 + 2797165736945808718232261814119567263758948745329022231817578640640391777440*I12*I06*I03^4
        + 3255544817362972121500861504845297422614689582931628440595150573501119709122560*I06^3*I03^4 - 30432500793845135134995315517829843761345855319294832497389225110918234840*J15*I03^5 +
        4583788548899293258991215668408499397129859314436760849013615173825419720*I15*I03^5 + 857526791503656781569553173011827189551531491049936760692335704032590849652*J09*I06*I03^5 +
        1535569474904840636112661454267527970311154735242209201802934119896734043036*I09*I06*I03^5 - 7774504158375190618098432380718041974938971697971975563484696542943980200*I12*I03^6 +
        12261274648408111601204362060009108020186564597338577655111647263248768901760*I06^2*I03^6 - 1696009013368460677134468162686677982857933768442406021685898558655665550*J09*I03^7 -
        375835403517675757375875025945451281614423535144605561651963021164713350*I09*I03^7 + 81198010366973817302011977266757628576710455972732566615490251111366444800*I06*I03^8 +
        2685984052074090643123192625324899635128518190231202801613101391575200*I03^10,
        -128018915957590978653378558042077309727750613796085922426920088677220339200*J15*I15 - 17940191854907460824202642605400408216432890960633897026360079498507558400*I15^2 +
        38981498783190430472442014905926132080012899331437420173090667078764465600*J18*J12 - 7449493232056662307616309182546748805454281286940073552990729749912664000*I18*J12 -
        27136740730696666317323949514044354110002344629578595009915790493773616800*J18*I12 + 7692516798741773529053455679948473873735088111790384190628293499938653600*I18*I12 +
        2736213708399187780577364211725038017316565224461611697253834382871958400*J21*J09 + 10859603745469095301216657388187106696052070749424517783108960922480332800*I21*J09 -
        2834334218021941172382395673229439205261892052162302926795571659062898240*J12*J09^2 + 9382558710057919740587874323843634835017854686553596825602291904667295360*I12*J09^2 +
        12685287258419158715129740060972431017969157182850422244634890946126783200*J21*I09 - 130091722800764493112038268137577299015343335066145376527670513774613177600*I21*I09 -
        52702053629086304812906960803847835899358848952164327234210679485870207440*J12*J09*I09 + 79950721983108061806797833844627492543073425898628136249017039797821727360*I12*J09*I09 +
        37868621353892674147715081268681425566611289719238475690166017747723040*J12*I09^2 + 4716813284368495513247757184688367770889510083241366989790120153466919040*I12*I09^2 -
        533939251243243242687728083769864229195784038080061653241563314417549824000*J12^2*I06 - 821713781756811254377688808218736816924696358905447512870868299262729984000*I12^2*I06 +
        3291531427395233980768286016469204620008919151733982290675334058210703395200*J15*J09*I06 - 1339349347397177038991721164348529372859669252062487662293155918050432950400*I15*J09*I06 -
        2760325459958609087876827403209033042566585349808028807883714396056002145600*J15*I09*I06 + 2159921385238930556684651175204744566705410255891043044100058507639225902400*I15*I09*I06 +
        46657454445310584105830831842977748220705563012256047440225952064864267673600*I18*I06^2 - 37879038085443883137527228779233063370115394174525869880900659757101236012800*J09^2*I06^2 -
        351270451878093963063491337701164824626089280347252251470752532442920423424000*J12*I06^3 + 7409700491359689325260624681206865037647514285224097854369376817168600867328000*I12*I06^3 +
        56910998616872852469829796197409250204217156569175774262104986756572601600*I15*J12*I03 + 19598686737748367471007017362423497550153031377766150171909314388123812800*J15*I12*I03 -
        74237113107240470332122295352801511069895235353882409369129187136231156800*I15*I12*I03 - 45743728080001079601945337829380915150922346919240997127024061050788653920*J18*J09*I03 +
        4299183649178312711489176623793894667650882206240536714944800893454420000*I18*J09*I03 - 4467425855276315526273295753770066068414364910745903741434066630098782160*J09^3*I03 -
        46981514899949420815771022542242421479657092958824650529834649595503412560*J18*I09*I03 + 7276133258681199626109032436158477788360123576928881455608516891751288000*I18*I09*I03 +
        47067910165354282652320909904587265990978699119070182504161391291040864940*J09^2*I09*I03 + 5406593259701920587536510821785440519045178069223024263409832382423871620*J09*I09^2*I03 -
        1505755875325636658909170696757782140554398926572296607254062872007170520*I09^3*I03 - 650459877577730637498470890777997495376010064234595303485886267979176960000*J21*I06*I03 +
        6154297148361871345015727139360570775727335413028531581177462034056113280000*I21*I06*I03 + 1321518615322464407748638681877331286043224614309912088228867158860733262400*J12*J09*I06*I03
        + 1139191766942044893530576624382621049156021158097620444941941238763298003200*J12*I09*I06*I03 -
        107929228588227880250443961815200490910925581760933644221660858451374548019200*J15*I06^2*I03 -
        64090616251570072064586490413806477594181200424816623142024037432303419648000*I15*I06^2*I03 +
        1747146653326504022156611899987050672289397905879389822864211335920915271577600*J09*I06^3*I03 -
        641613422458206610360684763330474364498376201450324705771721997881148900403200*I09*I06^3*I03 - 14813775295260494051451093988418711335868628822157080860837680272998822400*J12^2*I03^2 +
        14544853045611175179352384542341438148541708825866110476298332685467509600*J12*I12*I03^2 + 39780932328859867326666548504718743437655485962708074595544416523581347160*J15*J09*I03^2 -
        37474700843011824045628774259763501302274672699454731094421604405764082600*I15*J09*I03^2 + 28814523960705154191405341876669090537657050192490633601796455963507318060*J15*I09*I03^2 -
        22158138069347964596890873593428874138707400804274773395373145616781765540*I15*I09*I03^2 + 1950548945662805364305459967013356561889143833727572182290918265650784500000*J18*I06*I03^2 +
        268116980697121046366422444666872536787919068645990243932314173564064965600*I18*I06*I03^2 - 933823187941506387411432381702464247257846590330386960685134369041371208640*J09^2*I06*I03^2
        - 2862504803816825924534147659714923797977065210150755683910532730424559117120*J09*I09*I06*I03^2 +
        1289629477952567085428992244895144136650173100892179898403412520117827600*I09^2*I06*I03^2 + 76185123762368499648070113047329242799492014907707845653045337363543439513600*I12*I06^2*I03\
        ^2 - 9946490579936031597193546588247778297894749573133893100357010097940433937817600*I06^4*I03^2 + 11260261899331650370260450351448339169522936267255698664463261776457864000*I21*I03^3
        + 15339206042649503688029564746926388546514316558273342127255920779962960260*J12*J09*I03^3 + 1546470251626848383780077946171723506864557245678945415625205410312745280*I12*J09*I03^3 +
        4078321257526088992310478714049174183611473286843158725364583526579803000*J12*I09*I03^3 + 11067946361618107852547107287153258084322229028146071377519688813222899360*I12*I09*I03^3 -
        917933943429894256426964177063825413550783254131955977942609126051373363200*J15*I06*I03^3 + 43607757313995246738112411162642492117769832030534810299289472635406734554880*I09*I06^2*I03\
        ^3 + 3357738213194715183148837999444857568914990727098031328044193032195682850*J18*I03^4 + 590560405988563561088489265334984608894922064304188816487232264798126350*I18*I03^4 -
        4751963325443126334249645888315467165426419068497486744006272480055278341*J09^2*I03^4 - 5622965188595621625732005278248018786727635454859648199088925624136714480*J09*I09*I03^4 +
        1482275522417661891214324778443610219928343473023023287422765971838660769*I09^2*I03^4 - 555851240166384012799112093782298965828064304294524469699983017994496600000*J12*I06*I03^4 +
        1135921760033485936316352647275746425318192551184543637885802665816665367600*I12*I06*I03^4 + 1065436495847284463437997472496712993692658507684448643954131126876713371468800*I06^3*I03^4
        - 2632079368130464802203562052998450497169679473471309485877380971147675600*J15*I03^5 - 2566011474648427754989870674460927816775471126352468580337549140647373200*I15*I03^5 +
        65665356232961290908709956910816303440376297935263009248599414023175368400*J09*I06*I03^5 + 201890216730272795549536824277429515627453213322585444236904529597916533880*I09*I06*I03^5 +
        1763720797782577365988103665301459268277266672933736387438324153886883000*I12*I03^6 + 4517583698078237954022187294735570317977161702273606976671325267726661722400*I06^2*I03^6 -
        329190742945208214973361709886910983481598121990248502080432214393962750*J09*I03^7 + 38496837784965555706905049387208605519662582138721513969823496179690250*I09*I03^7 +
        11710535962950308592047775173949659063217618618258123103767485404502412000*I06*I03^8 - 9809296582807617030275339290522880828562478897565920186844176565884000*I03^10,
        -206841997459168779137722086818234509563795362644446683127929983443003993600*J15*I15 - 25604957254809824702119473213189007730624477895364509839352654786229747200*I15^2 +
        56079732042805067832931181352578525584739632004332844682883285224023236800*J18*J12 - 11183992654390231720295448976465918973144828097917339607571493529745617600*I18*J12 -
        196199508927461051504744432102413793211049143947164443774714891211381466400*J18*I12 + 29229312410835730886592913472870656774599430584727695716956125114101383200*I18*I12 +
        2828461832969213184856635397281983341367456408288948450372705017444718400*J21*J09 + 35819799518789369142617600195737377509098654287932391576184201213703308800*I21*J09 -
        2001549291232367988356333510573417592442031112060668685742390444486095840*J12*J09^2 - 12656453157489355518833961881110892042152358086534890045136374463322248320*I12*J09^2 +
        22221994054598908747281651345711099083040714304641277447162085584324471200*J21*I09 - 220677936118892908512954971675904306371901115921020830007446470945521657600*I21*I09 -
        83541245908201386979672215444499576464990363227274789807014954218066104240*J12*J09*I09 + 178138996437044757874940166181654070792401641792599635566474985383543742080*I12*J09*I09 -
        3351417683183058104729744760880277627053753931524195055304419972419884960*J12*I09^2 - 732435977030595091365277479497534187563992151296025120179120504525015680*I12*I09^2 -
        778917860932913583623592178967595655888489021833450297727059034968854016000*J12^2*I06 + 6451943963651851408988730466149414643759896346433848938107339409737894400000*I12^2*I06 +
        3695898839194887596325984239914039089499132683674580673296774460787635286400*J15*J09*I06 - 2435296748916885024056791562044127498815225040656886088708199538565267888000*I15*J09*I06 -
        3611923880082018167893857357929578872005872050332598135236062594943658792000*J15*I09*I06 + 3506110441903698050335171925672141992276399938676420627970726494203363105600*I15*I09*I06 +
        52346552649493472233053965787407623664207740013534148211935222993214507622400*I18*I06^2 - 44353650982706033024866529770817107746624864302049913427310559601451915436800*J09^2*I06^2 -
        838490266884503943761345347583874452573140657978735927030366343180349075456000*J12*I06^3 + 10142775664662463528347857767194851607955915197178651683710150245533453199872000*I12*I06^3 +
        85210052743620998782849240835994234550965365945482759012727355552137452800*I15*J12*I03 + 125755757355914092242242665692287675579471527152022945527487542820712203200*J15*I12*I03 -
        148909789601275480889140672574007764463685828714672936310628633827352052800*I15*I12*I03 + 35389458333748634945659430259354915735220795511715830858704547341238616960*J18*J09*I03 -
        5260898663475125960905496710155371957400690396738702241010693532846939360*I18*J09*I03 + 3320209414077130447581947487960360036082736296647919081092653545994960040*J09^3*I03 -
        102508179147500624955065688831349570872270876386911484698684269479074433520*J18*I09*I03 + 14770614478708124478917250399219056665444691398433205392134597789648278720*I18*I09*I03 +
        39914072296583243838790820843829202627868032558498246241203108110859580940*J09^2*I09*I03 + 29532024076782225670774992926836618939953172389163135740021088120059236220*J09*I09^2*I03 -
        5350437845515256680794426790561542797226172670109773466088315155711013320*I09^3*I03 - 351196251790064132885264998968950767698729977832346344563243478177023232000*J21*I06*I03 +
        2209253009259560415129132831031482319893727592206143124025122659351309696000*I21*I06*I03 + 42804718511776956476947044583087657315430350436986021751061339633330211200*J12*J09*I06*I03 +
        1475450861202269647408993824586013213158052624742875966887346951774222577600*J12*I09*I06*I03 -
        85072643513413939831882090892629845516806802618965758996950970861446170572800*J15*I06^2*I03 -
        22677417241046645442413985483268040646918406652495926243519340269937210726400*I15*I06^2*I03 +
        2008586072659295340822226022280276560876029834722578859439474556379118434969600*J09*I06^3*I03 -
        1531671694586342803600784383278459907139839965104449035490776496808338002739200*I09*I06^3*I03 - 21006947387942949491410742252896821840645189329013961785550209005945241600*J12^2*I03^2 +
        46507412653188552042066124032786965478927739199408954084811348266931746400*J12*I12*I03^2 + 25232470897785914467919095875795423620492035842859856661865498078643757720*J15*J09*I03^2 -
        48807923970132629253512052354814842886990573025331861071889033405511102920*I15*J09*I03^2 + 52956829262300277836708419445694883163923139689418714330177052252564200220*J15*I09*I03^2 -
        36278768335494996567339137447835906915818863731135017485503302717652862740*I15*I09*I03^2 - 1084307353515927552387199015478732297883226982875502858177250205372324250400*J18*I06*I03^2 +
        737297758506192328555228602793463487479576021368495222565750406452148372000*I18*I06*I03^2 - 971020618687836720572838214129462592671047152419374627281886077745270278880*J09^2*I06*I03^2
        - 1662533414753707258659477854224932181038684979556814618228524557954566157440*J09*I09*I06*I03^2 -
        746770298043264959503051254606539781137399990734579381861019704588082926800*I09^2*I06*I03^2 +
        182449522317045327800024725149556622243247902772866528874599859962752521446400*I12*I06^2*I03^2 +
        9636664068789828356903149598648073095434688428594523828779559423917331643801600*I06^4*I03^2 + 13547560388948615054339807912483111411860522779415277220497548579392792000*I21*I03^3 -
        7394247671595236769758621307386486592179587346066178041926150654802481240*J12*J09*I03^3 + 15042484970940825273853541317460569519392395035377403120119664528136113440*I12*J09*I03^3 +
        15736764551470169606003254528572097731995319633224329940512350892156992420*J12*I09*I03^3 + 2921872326050733878528807525293145380281831145264380752670386144871104160*I12*I09*I03^3 -
        298209174750509322760070950503139277918760015992903066130575620527928857600*J15*I06*I03^3 + 43607757313995246738112411162642492117769832030534810299289472635406734554880*J09*I06^2*I03\
        ^3 + 466425714951249541187674540549851818090389205742685405223067493666449150*J18*I03^4 + 1200660998649677875329737297425373525636160811868618623153186044346309650*I18*I03^4 +
        7687456539735398073588137046702250033724805124360847811884255447122728717*J09^2*I03^4 - 5257566977801993736040848862844437638153829958126641007275111512035042916*J09*I09*I03^4 -
        55975428462054414886384706630553015327925239722131655935236816391903821*I09^2*I03^4 + 271863841230058905106409047180528925974865981411717995913103114777799790400*J12*I06*I03^4 +
        397411684218617587148472865681072023809453684298545514609304074474787354800*I12*I06*I03^4 - 26514813243800868675683449739240351560166842956210422199954804071296457395200*I06^3*I03^4 +
        73579121597374627304781668252689041426255202859419657235006101646030400*J15*I03^5 - 3977307703455265950306523334123436003388919520409210106468006865494587200*I15*I03^5 -
        202250946334757717306574656809779934940718659870428646866741814972175502200*J09*I06*I03^5 - 98763268150586561090242513605254954563381322238008046105486016014887703840*I09*I06*I03^5 +
        1859390238641032661063781608006268564229656058043854333840026166134945000*I12*I03^6 + 2241095811535317544802951843369587135155951634387971073981375710210222103200*I06^2*I03^6 +
        620731609651497364943556005335852293942808382783710563074341277470503750*J09*I03^7 - 460542525650466000451152339268472699533904586316968089935476512387369250*I09*I03^7 -
        10397003383337844115426835559057606732776797450050506450133946740211284000*I06*I03^8 + 11044060691950334162834140700783388551235919632136048069954152150412000*I03^10,
        5754366039547179759153816645212529293252234881762789290382523668072666696800*J15*I15 + 5574370498135412148277727470708493516203412672452257230855144290137065205600*I15^2 -
        50052503760802197785397863511624843534578600013089271261483213057925240100400*J18*J12 + 7850960618251563386427769700035682713062550775115243355443592770569034308400*I18*J12 +
        117423723244087247127236801572580087005871258849986509639690272624109278066400*J18*I12 - 16481437327697784018434988583958282036705310477156487560661550604433709008800*I18*I12 -
        12375972221725706474113538643043842172074371362821141464158780460769193430400*J21*J09 + 149680273720879217628820434550154734726167789652119584352084063178875173059200*I21*J09 +
        36942192362282019449475460634084537011297331920722714024765337325437873947840*J12*J09^2 - 72517024933228572613609549306450164887224021187026171059263840039807049600240*I12*J09^2 +
        4028393373470630777349651438375148691703634183933914274338836689856689648800*J21*I09 - 42400309469274844568523392956665457428470472204297375279618500031343747574400*I21*I09 -
        3212093493207203711527279973888642454773211402624817448903531633760912938160*J12*J09*I09 + 7853112445959123377743968782754484798237484315727814140753181948077378227760*I12*J09*I09 -
        2438085660582975090755848379378756879530301858814926361362032504719484326240*J12*I09^2 + 1762070144679103100533739310607527562285934813424165339573209387206513926240*I12*I09^2 -
        355321574836427355919850927262960847711591785445597133479510516979528632608000*J12^2*I06 + 6307550611488598188905545186025074752748850704416642204004370149049902676688000*J12*I12*I06 -
        10371443308431346093489809051311858461849021390893575086369557964895252710176000*I12^2*I06 - 1000403872459045752648045403710704150381212062142003190342058380274086583816000*J15*J09*I06
        - 2914627172409015085619726800841717642898441302207262604369120250129281339963200*I15*J09*I06 -
        387134890578882266639102311297536186579458147600478822543394466365881280804800*J15*I09*I06 + 1353960124421770263257356051612337346089036263107877340253098376417644548372800*I15*I09*I06
        + 45035010309657148471501436937934653617952181596105287300730409914835494017971200*I18*I06^2 +
        4938462936027452612081239690958486523498034651511917759862830360703059070092800*J09^2*I06^2 -
        593380954192131453048308517074453428841133901098345196184950655007734502490368000*J12*I06^3 +
        1424066656802267141909935996104611551309726869674403011156090318219607919678464000*I12*I06^3 - 24722398829579346784338964650820898531015703929628947497709798918548610480400*I15*J12*I03
        - 14343986032765259172519256554801650149389837133660548331446843267435175311600*J15*I12*I03 + 37521633796028247972607952363796724118073295412778962207843913280310625500400*I15*I12*I03
        + 33991626002502409053776795343029928501330023936204610733300523803210978117800*J18*J09*I03 - 3777529952480744498121993947549217702496878058747867309347464163381861581160*I18*J09*I03 -
        29919957249033216534499756996758473294178745584084733386866061019869923914560*J09^3*I03 - 17278036933175152106340810280188684447242822790906628608111322891754263233000*J18*I09*I03 +
        1151433945008554369809600928623095749311268725806980096928902417396034625720*I18*I09*I03 - 8572785158653214398910744379351739354059576210844949076800989572332065038780*J09^2*I09*I03 +
        12112950935381791312611223020646745286150665692665911903276106196320404620380*J09*I09^2*I03 - 968996919637147413600225854098151338995941374732588554563606474409973260360*I09^3*I03 -
        210556038339088178374268551069402242991237125897709795645569986072241344928000*J21*I06*I03 - 503902447403176604361974684177124916410484237457598491957686606110648897216000*I21*I06*I03
        + 105983540313469393500921418595549097181856025430384118449539215299548710978400*J12*J09*I06*I03 -
        193420677060875227544737753260328087768486818010959201035667067531355465692800*J12*I09*I06*I03 -
        63645270345809333737166067822056471291691287583427357747047725837673709504358400*J15*I06^2*I03 +
        83408038121091129095530353801647081985704037829562488853420804620013836920345600*I15*I06^2*I03 +
        63838662417867308711090585017619407740615683301817694127048390679278215996236800*J09*I06^3*I03 +
        2006026622798286802761894447067509059372965235462555271104274944991257685013478400*I09*I06^3*I03 +
        13838787601499722749950837163656680947694366528413386758265669975436936565200*J12^2*I03^2 - 23350203562793757732613036280707281308706000692840980993801214044834304188800*J12*I12*I03^2
        - 89433802616632184860458497834587049329941027544434105896894048220116778377940*J15*J09*I03^2 +
        11404520002237441146545740493399747601669587898656438600859544702051024142100*I15*J09*I03^2 +
        32600457816970565974486364080057848256332552863949153882555525074324864596380*J15*I09*I03^2 - 3458719722012230524523890789555952735975067481168399118682729818217349583100*I15*I09*I03^2
        - 1060201744953543819304148096369750902355019659966420638932599108271922386573600*J18*I06*I03^2 +
        565723201538117373374404692524331883053644819990911674096115434545854747941600*I18*I06*I03^2 -
        97999613241866032300214596673156637702378879410008590572626983677694917886240*J09^2*I06*I03^2 +
        1381542165934743176911891722785845668113507155122757228693502448150417017262960*J09*I09*I06*I03^2 -
        401391725676096549908352031829590310479708669591040403932025829639596241487760*I09^2*I06*I03^2 +
        52411842588523348427934458153493937247364308895382585372927303458109919168179200*I12*I06^2*I03^2 -
        29200735842164066144279608448017487436279563668182009508527183075994278898322227200*I06^4*I03^2 -
        16147074220481320512385612304394257340270262482055068479950411706918749416000*I21*I03^3 + 6579971997736342333321954340799129703359472219623379981907496824955761896470*J12*J09*I03^3 -
        19225840031305504626363838443902159445958059255014763602670217079011560815340*I12*J09*I03^3 -
        10566860957405394390176541360629359417800028112799604002362468862107775168540*J12*I09*I03^3 +
        23174339002103324281543071194012117578652195383550479260562840288604830112880*I12*I09*I03^3 +
        3115003400349088120870574375529987470637164674343183231622749476364574150220800*J15*I06*I03^3 + 4698527137958207749053531889622286182517622193241424768682524415334000124950*J18*I03^4 +
        794719919884869772514803396512147419008149177437490887039193108461345091450*I18*I03^4 - 8321270841735163332004654190174689339405620036080376582330042742124316551742*J09^2*I03^4 -
        2220078385860797452781007106210433700030351847736169691550100884380604813937*J09*I09*I03^4 + 2263689167591002001593655482459597721547861124096113189330644848134882940167*I09^2*I03^4 -
        551327210847177185149061691274760096848452752273319955696081425492927184613400*J12*I06*I03^4 +
        1527293710791632605783068841622623954838890044581887729517027516938067442016800*I12*I06*I03^4 +
        419300701949064279223880058861333952586037431627967841659170285029178411424000000*I06^3*I03^4 - 4525083592227688571830807437933584800494662846127404299255127262337274463600*J15*I03^5 +
        3136936145768181406560546889632542726145174299768137512208742457280459726800*I15*I03^5 + 120973970253477052996849540361450762552507717225572747607277421690225685416380*J09*I06*I03^5 +
        384650366881340358430005980199081699576683078821028294247861232428983375858340*I09*I06*I03^5 - 162537739662539840764125677540981365404937322273948398825679415471197187000*I12*I03^6 +
        1387412468951863511235564974496072910688067060019635550984256567622411003163200*I06^2*I03^6 - 893178109428397904876474676334451605831575948609866130455223214315721676450*J09*I03^7 +
        463901437675969158182975747984561757025251438134949062641501353576468360150*I09*I03^7 + 14078625341250558511277929295757989828686772967553292194648819690656787092000*I06*I03^8 -
        27363445015646485167720279243632027093116583041739253279201256145803940000*I03^10,
        -79740050391362133498365632113506276932758062571461886299886242239952176704000*J15*I15 - 3391873675521414237593975002337458288685316394783801603875006786211429440000*I15^2 -
        32197989354876033825210814662207751733887726388183966662599106252975807320000*J18*J12 + 1612554070433479830253437760753865572318064542074658784567945555005745457600*I18*J12 -
        127331212316644709249393000024885031079743492475783881560778142073229964399200*J18*I12 + 17095412933122975808754201360891052606031245637783548662556615162235123522400*I18*I12 +
        5525973670841328361653835984223541151104598800937013809649763665625349022400*J21*J09 - 57997288705519581957127304340003075144955789533951028676459780441259021043200*I21*J09 -
        25511169125219492993671194422784778758566483331690952465658172726059830609440*J12*J09^2 + 25406568088788766095182569545639073158034053687852180498987664061343706855680*I12*J09^2 +
        2704892388842543907232902435448628609026625581259175494049612138028287307200*J21*I09 - 7844544376860638767870637500223026444454813049654378683437830037729794009600*I21*I09 +
        9697117741609791753682493918739272454362894622828278622571280725478436665760*J12*J09*I09 + 30941308747212797450650709874948784962874831546002096959622693520018665694080*I12*J09*I09 -
        7556303681635698396107408446677067643845210082695790997879876596564196327360*J12*I09^2 + 2761007646335421683640411063109888279783751431680758516948313519419768363520*I12*I09^2 -
        45015717664320157446789224079994873110051009944235664135965363214044538368000*J12^2*I06 + 8378065194187868879398120465799701061178345404352105795619643870405174844672000*I12^2*I06 +
        525659025458962253633024275681778747165759268772738149694309384987540213584000*J15*J09*I06 + 855866889861838914597500689559555319449709197397931347468346893387190542422400*I15*J09*I06
        + 314954514133473683716869858737390950096347498010851120055884926979175422513600*J15*I09*I06 +
        261791925535451182726843297586407678165520976673983831728006696811410115422400*I15*I09*I06 - 29598837475019610285630816897396815026125997939734162385498864255580418035097600*I18*I06^2
        - 10199942869111469382189172506068549586379746635727105566680013813053047990393600*J09^2*I06^2 -
        235408560295647848534132639240005426656536982261469691795645101642007324356608000*J12*I06^3 +
        1419709083770588194123444117810191983040326177240504307365532575378046008424960000*I12*I06^3 +
        105125843524809969815092419767084579212480845073610703400072835817498377944800*J15*J12*I03 + 24535197519242378084414518057102407631459466034585417974104776181767420261600*I15*J12*I03 +
        30110083867272992520150534910444097527195175251151852346893107936811127754800*J15*I12*I03 - 88288007855693486731087374027692535751882089519594913279539322965284059448400*I15*I12*I03 +
        33113015473422420593935749370509075476578262895569153399175705696150395566560*J18*J09*I03 - 3961725494921574557665310424780465930659278571994917530533011415634994501760*I18*J09*I03 +
        17798324233623854388714924070280295491300460827707130309676627401023766241240*J09^3*I03 - 743013677548070454994294251954170685874234647860989912088585537440402213920*J18*I09*I03 +
        1084329005673153969801521247003159445522049313993977105899038887209813528320*I18*I09*I03 + 1348949092126123680909229570595970522695526465112252937231358959512784253600*J09^2*I09*I03 -
        2743805392464545441778779334881491106386005169484379964189131977490615715560*J09*I09^2*I03 + 888202105177718994476692025798361309189283836939504911100812978842339093200*I09^3*I03 +
        416154537303109478116085835084980278058524523309356752242243386708868179008000*J21*I06*I03 - 2412863224498236527694624404149187772187622222392768803739162093783802822784000*I21*I06*I03
        - 503739460510209090772236972679011946376965358761971850507519857146572107772800*J12*J09*I06*I03 -
        1005650094348189451833789000442330472722330987875934865916697892976139012178400*J12*I09*I06*I03 +
        50788987226921543962866507391215417914122052921546252837280696539031761594956800*J15*I06^2*I03 -
        37982927301372252111046545555076896263742461779980444764876389567091377894886400*I15*I06^2*I03 +
        652448767037312722919409478687821553977992980300771940552451569626158547981977600*J09*I06^3*I03 -
        1647524221456278872408521143269802310851201892559665096221858270980244823017523200*I09*I06^3*I03 -
        20959932409349954842844958877844521710291762132993958240378503730299618272400*J12^2*I03^2 + 67195651154547797514399416673124494397695670232328607767493250579217558024600*J12*I12*I03^2
        + 29455519381782068600932873290691076980132169372871651953335265408721669417240*J15*J09*I03^2 -
        13822954268587106962817229638538991911728442646980021790251727945216621165320*I15*J09*I03^2 -
        26628852569668727644365229556458906716658615894884758018567444634633754688580*J15*I09*I03^2 - 3906901260620082166847910911647051565336991716431837477024490705923496901060*I15*I09*I03^2
        - 50605845779599455859735623387068866243563608359310745748896571268301306381600*J18*I06*I03^2 -
        263453028425968681409556018004998714477682209576209786079914777531583796543200*I18*I06*I03^2 +
        555765388607191553513434377172605781464332541649756171466962860785176630636320*J09^2*I06*I03^2 -
        733162841631252757347970853948082292025722491235934330569517821884209913344880*J09*I09*I06*I03^2 +
        370067851868320431884201818494703632703397795389768422824829539243156739274080*I09^2*I06*I03^2 -
        2931406774666053408779262982755107930147229715699780290004612224047331332582400*I12*I06^2*I03^2 +
        16065661499979130459728193887045801908107616585243071881738777238022251291621478400*I06^4*I03^2 +
        16272340993870270977258331951590468253189624439068298906563248558480197208000*I21*I03^3 - 9166544564072165968420548654170746501174199240905489647992415798816935432040*J12*J09*I03^3 +
        8563392834193705582359351047955001145322086303041056055582316871982521043380*I12*J09*I03^3 + 15164478380552650331288284308620924669226469549295447540223209332186288114530*J12*I09*I03^3
        - 23064157616669985106516666357780950422447598548535858111656497698498513800160*I12*I09*I03^3 -
        2732592157388453869633139813366373651344986677156500306225389192977572607456000*J15*I06*I03^3 - 8222772524236363582105923517566232294801627227854525181991748964600537959250*J18*I03^4 +
        57196114677748187615770583658227112496816398920011479025312094383755809250*I18*I03^4 + 9869382199078682538201243632168518046077164879133617301584145751125415126109*J09^2*I03^4 +
        1129409564287270241169128676320651897703116500385859010774116933564518215149*J09*I09*I03^4 - 2373965169953275775981941753362777071235789572050042264036368279494478485634*I09^2*I03^4 +
        687217181229661715975133645807957457073794346848454200838229636206658549405600*J12*I06*I03^4 -
        1160785701651384682247102931422698091871832341931083232967054527101620459854800*I12*I06*I03^4 -
        609684975159755116491580285158226480113280805164590140203337826227308640245900800*I06^3*I03^4 + 7607034172409485002335573099468621175722511951770731062854200926083666256000*J15*I03^5 -
        4901458662150206133121627833320561441233173282158942244924844030735040832000*I15*I03^5 - 189906373813202494386020107846850309206023574764229119492127904178242477688120*J09*I06*I03^5 -
        395860250222180865960551595524094194220850679060101348058613754871114987483160*I09*I06*I03^5 + 2035175265731439757137246569689170663601532872709641243493940434043573003000*I12*I03^6 -
        1218482897814002343943276073208093487427482420238639775791848245153030107041200*I06^2*I03^6 + 801639919047805007283337476070912488402721891241538452063308138578059950350*J09*I03^7 -
        422173279783375521741344509854797531289787996642284489880630637708912115450*I09*I03^7 - 16551306628212567624817322575238469441184853397119302018124740424079027390000*I06*I03^8 +
        21425925907555757256855956217455477687734353022603939301011007149460324000*I03^10,
        -1328913867902565666682789443791503248848153381898142698587220900432373735142400*J15*I15 - 142605124972797443308916056520690607577574317544127330895640698702589012812800*I15^2 +
        387784723601294296839235765967489213058559547224549107319655519435041018597200*J18*J12 - 44090497129028651045938792165102057023468174318482986789137189577739404885200*I18*J12 -
        1302242142002933116067526320342360593059295955583798878837876835532149051821400*J18*I12 + 146198529760319828880982929513333838143141887560721726612416179519896609986200*I18*I12 -
        81105628333391036048924668827951780317991466407138750149522127349040716876800*J21*J09 + 874327299239579203650921875595348832065911517948392258986351201035780450086400*I21*J09 +
        301446720081454249798584001314910650858460159077237449933863317540575191541280*J12*J09^2 - 650520292168180584333545185255344356593637212172785933227077302505593077239280*I12*J09^2 +
        157258555606654524616121175856977988159134397836202199809148220944138617449600*J21*I09 - 1524442683169855704374545293634808756239827943935336612085107079723107679564800*I21*I09 -
        571735049582804954280431412369227309025158314676083687085407212367759883322720*J12*J09*I09 + 1241658202414496271913878214978265081272041608747180990470734418055489014995120*I12*J09*I09
        - 22142458247306967477923733809709213473887544293741375146097809016085909446080*J12*I09^2 + 2450300647053933041275526608656878993012164211858199867129988708238338704480*I12*I09^2 -
        4448400456762658203338985679110689349165081038692137911462383409538277406976000*J12^2*I06 + 45078505382298433629776870073326069430443422434844637688227800770526886891424000*I12^2*I06 -
        9386004007966244823062048825481071329067108355820370979866178246569842956648000*J15*J09*I06 -
        17471323855491975503990963298581646807078422112908882181303355325088937405454400*I15*J09*I06 -
        11669198846128886980234968513950743704570189477620753084588603171801428564977600*J15*I09*I06 +
        21768830374791978448001919542930405876775807225062403176931451361689592335425600*I15*I09*I06 +
        1192127065571345057703148040158739128269532783134745376556825958170431605894032000*J18*I06^2 +
        130733412870627752351612641079244558035580514857901455180543817818762902339414400*I18*I06^2 -
        127685437708834252774576024110333893658816288302484034168986498117391965491366400*J09^2*I06^2 -
        3769971587062522901125329539735533051424580081692607738063873250193645942900736000*J12*I06^3 -
        11076759763251851810510147371299051660617015844154536706747100631171198429437952000*I12*I06^3 +
        487226955685057068476106340053119231220147191609292533760928336549418775283200*I15*J12*I03 + 830588424341255489057031389752523876291020880670810472376397886198203434007600*J15*I12*I03
        - 937459349482253417425900907874990487125189540981733388425166998697800487403600*I15*I12*I03 +
        750359616841334040023638434753984128326026002880555364170498865856603448678600*J18*J09*I03 - 88180150686224291868929419802609867614535326952962674597781520617834210525320*I18*J09*I03 -
        135055160971845337388620544281004688348359924729027820899125190629479809950320*J09^3*I03 - 578240979964077489293904155454700666651952261820340232074443216872852852749200*J18*I09*I03 +
        73420349964080255042680429730501002681222541124061522290903886104769044348240*I18*I09*I03 + 144698177416271209531433421807319710112975039882954630867381399464269537303040*J09^2*I09*I0\
        3 + 193912815022983091370990541618096840367387912516308311871546980828730892122960*J09*I09^2*I03 -
        26256196526349151735238536469278680365461133782290127989597759195411929941920*I09^3*I03 + 4244828456717939187793538093438312560896854013642287580004019761971712287744000*J21*I06*I03 -
        46720990024498846070887811370805672875260571463265815619793670855548318572352000*I21*I06*I03 -
        11960667206334845062433562346440130973861217202868871729514873953986593963591200*J12*J09*I06*I03 +
        5526574286490521117574621309273184763654216903375295950232539470921017812042400*J12*I09*I06*I03 -
        1278725737694525855127250572447778190636913370702212437217572262531392885429260800*J15*I06^2*I03 +
        350365970319838512063271975783002986805639257725430353686430634606649460358131200*I15*I06^2*I03 +
        8651409725167001455093245524126353935104487360368489496720576335489472505930905600*J09*I06^3*I03 -
        5689517002966297373923375086221973519394998707254666173089508506437602154923187200*I09*I06^3*I03 -
        128305021737116664124634981485397908761849127427720483164439755162133973489600*J12^2*I03^2 +
        328916383185607175384904124939915260287073889745376187749076666731944636189400*J12*I12*I03^2 -
        216789676303338393036717759023620483356664099683716144181068214124525675591380*J15*J09*I03^2 -
        166840899914726727716261737744125232731247352751844878705077259671404553267700*I15*J09*I03^2 +
        207491343067535079490973547975271085042352762887906464283538402442780129054560*J15*I09*I03^2 -
        188439096265180616223656914260699540939693614983136849556762527001699410968800*I15*I09*I03^2 -
        7855226711560303330922918259147999609669991071119591603789191864709021119549800*J18*I06*I03^2 +
        4143745036536093424630122944471573575135943239958008835946470468869054432194600*I18*I06*I03^2 +
        10531656615685031959270445673050498809970098810706759128111933695964627184411520*J09^2*I06*I03^2 -
        6377163929488303908256211955994081954626725259608750672922980548879770916850880*J09*I09*I06*I03^2 -
        2879867480650728436353244115841138231151200328484084308615197914353776374887920*I09^2*I06*I03^2 +
        293539968563080988968181908493574549874106092180964647381456723178301683008214400*I12*I06^2*I03^2 -
        125045472084369486785816139168837717637690979742347613269958309306225417403789670400*I06^4*I03^2 +
        88147835598216115604379835057944113467565101136614265792240191690458509868000*I21*I03^3 - 83472021096824220766056536760528995990790822482979804142736285872151724426210*J12*J09*I03^3 -
        9756281248242223122028744088999725892422679339938373743137863604210183239280*I12*J09*I03^3 +
        115146390991638335018837306613741550160634377483134440129777971725555826349720*J12*I09*I03^3 -
        47569206492055041568443841813639560509311590296114404195185273322414489601040*I12*I09*I03^3 -
        15748571097886588891964804397056359883847296174782194763485136609525625567270400*J15*I06*I03^3 - 28886445755726493111220626243360163366703989480264789235590368730687965359325*J18*I03^4
        + 11464242864159858610005829575848375039496596014424046934802605183209012323925*I18*I03^4 + 86894985007265748434494590049260942849576008788585892310492154268461745031426*J09^2*I03^4 -
        27282184535335455684557499329075952438525805352351234994496028550827621498139*J09*I09*I03^4 - 8290242649232209502434032600599744225541941084147584539419631263663722025151*I09^2*I03^4 +
        5067708026003964169150090747284895339701054641464220936277061609324691701911600*J12*I06*I03^4 -
        4106483879559559090156133252633976463928109404218375909232658026208089993601000*I12*I06*I03^4 -
        4749163072541741633448884019592550693167175480175867531621898896989132409430214400*I06^3*I03^4 + 25113262592942871778378289505076409252197057207755803882656322135206760843700*J15*I03^5
        - 34166150870305694877623180006888289597921564698195854613941741550880106955100*I15*I03^5 - 2386728183846492777639653029735069101785114951610098262228548991827175037780320*J09*I06*I03\
        ^5 - 1917360944330414516199070411917343906495667310477676181778760287263687818486260*I09*I06*I03^5 +
        17924076517784211622467527324329539027162235810677233445336573607845298687500*I12*I03^6 + 2328383268882346550371475769613380581483585856644652669707146608201724896597000*I06^2*I03^6 +
        5675521693797580155914136925110855305275793553939675812141569435582798287375*J09*I03^7 - 3389046864563132953438835648335193559623194454475194309895196024514742151125*I09*I03^7 -
        146927196907827332957267351332933723416970009196321302193314930572308337249000*I06*I03^8 + 88667879587488442366030038945030340484273131827303711030225543166096202000*I03^10,
        -24798153038027946113626433233956683002864230797947739443772639652361866412800*J15*I15 - 2877520886963124541715729768336979471325267441857931671411900097004536953600*I15^2 +
        7172799278445945256656508418581005626086785499017060424530376564540433174400*J18*J12 - 1049872331423836236957063765602798893787108610997185965510184292906348771200*I18*J12 -
        21938319312896032371616249570630545259818962198933215979806031078935989312000*J18*I12 + 2816932985494322631727983086488535765201638910985515097488661576262338662400*I18*I12 -
        1851100595121068536009103039771463428852145484533584380805253520589194641600*J21*J09 + 35871081991184474307693734197283643516585077191807742764120427159445886732800*I21*J09 +
        6233339183160596412052678125177416748133785297876417668106328097068882832160*J12*J09^2 - 15468760637959579472721638726888385614728044960901657371829770975924207008640*I12*J09^2 +
        3583219423337237264484612825520504487437976989073318888814876089439554539200*J21*I09 - 42332665025684576348415466459846998603478045530924267155430753974964839001600*I21*I09 -
        10700231519645665361728703177231974475309163903063796613051458325829978419040*J12*J09*I09 + 25134221465236331058262359917448016142052764346654503811487401057743646168960*I12*J09*I09 -
        1538199119451485872532901981362184767000756729443551729663211848287611450560*J12*I09^2 + 1262183021345209129288228341652138155009538953223028696152980869735857520640*I12*I09^2 -
        59818911865741280894810391044200543235991294433592346501025344835859227776000*J12^2*I06 + 641296421749237758252725206849286461755258990051808453147024049864629734048000*I12^2*I06 +
        376175165383927336526682534756837266229269995285506179104004358230058872208000*J15*J09*I06 - 792044696764425233587913244856955659500281111004438378470526495103872978960000*I15*J09*I06
        - 895252374755915184405792795234615316124840727253103408904450261717414398812800*J15*I09*I06 +
        643111182895371098134333787428577136912912567923159534053529546508886226678400*I15*I09*I06 + 6940975823766723031780338866488750436766827259169428024026068726235723983257600*I18*I06^2 -
        10755998473443900340210888067634965910202601931115016886446080658177582999635200*J09^2*I06^2 +
        5887047237389358309645175506956736435898927324122199390404078805779909164908800*I09^2*I06^2 -
        442656914426619830358168012471626009481153763042532741815265267396675663397888000*J12*I06^3 +
        2288441151347173541657973801074930595268447525608752464382185154374886445382656000*I12*I06^3 + 9269828821678192021116726838734411498431489339928966597257181636191648054400*I15*J12*I03
        + 13850223209747730964783570330499487755273764767120346659273276862206287486400*J15*I12*I03 - 16652312409780246552556488387973728766831544185979176030304501725113677716800*I15*I12*I03
        + 19113180290451873496858377014104274500573630940927066657651728987181778732480*J18*J09*I03 - 2302394011035886891961116463949251282266540142575682536396971152106820864800*I18*J09*I03 -
        4511473889663706731167740445516804062033884302918109294919468744571361683800*J09^3*I03 - 17467882102938484746181470731809601450532557923941757110387308637944856363360*J18*I09*I03 +
        2249531209611128343482056168411370400968555142791857292924589138559096977600*I18*I09*I03 + 2114517803248959376331695064804924144776293978175387729784862442638823435440*J09^2*I09*I03 +
        6655430683767998685018214327381509555497390559896054656724405913536269420440*J09*I09^2*I03 - 882314214248737636872371734551461788053125452795589883097114493804255712240*I09^3*I03 +
        7703572407758649800347026287660852972000684139435490549654072859935586112000*J21*I06*I03 - 831832298369353643223791937645240666985988761603838181649893586143016379136000*I21*I06*I03 -
        182205358892580679126088679839867289850151408298142435974452753783817797337600*J12*J09*I06*I03 +
        176399870188900063283044387405824608353200941870499990762605604834743041171200*J12*I09*I06*I03 -
        23140298747224223059135460280081102807082731421002624419856027005837757067238400*J15*I06^2*I03 +
        20957049329978872130270868634593496424913049590068555862470656657087423738444800*I15*I06^2*I03 +
        519215649906123827079203726645243108364638847624235871543083384091567504764262400*J09*I06^3*I03 +
        113737376595844859301904485651523126640523243917081126118872771777233926220339200*I09*I06^3*I03 -
        2176598149184902503252937081138839947686125628314816858798054837600543868800*J12^2*I03^2 + 5106466909326203667019695970108946445989604565008250436319257273207635543200*J12*I12*I03^2 -
        16279369616803606438931587468496851935362193709459420449798636905243643101160*J15*J09*I03^2 - 3003138326324660310196478411670556995708506833839331536935527264911101675400*I15*J09*I03^2
        + 10266477217912079464062701466333631276121202160851213011731208545036235167320*J15*I09*I03^2 -
        4829152151958571149187278682273926229083282145065052554370302704767791793800*I15*I09*I03^2 -
        541654771402364754461369606280118019881804119110845857062526891053930909688000*J18*I06*I03^2 +
        132737701300968175445990251112197649791025718098789690464925868394666098609600*I18*I06*I03^2 +
        37508839863661552560576808482377004665432675117479081394537873128838100235680*J09^2*I06*I03^2 +
        11877668161243573418269551827075361664605424508534449751198226165196055376480*J09*I09*I06*I03^2 -
        149051228457650018421763217099200024459932805647957543367239063255461110735680*I09^2*I06*I03^2 +
        38330450086469648566501478051451739354592834101726224725960010587190577995187200*I12*I06^2*I03^2 -
        8487063978742828355670147772567830451285628514982906192764941949717027377547571200*I06^4*I03^2 + 532293466484393040840427481621369342179711177940925114766928759602185360000*I21*I03^3 +
        511754324949491935265462262613861418684118394266142405402728225468858727320*J12*J09*I03^3 - 4902600051776392136254118224511942026853027584579833268715799015186270500640*I12*J09*I03^3 +
        1895383099198357417721881339402788182499987828255101891924437509695757977760*J12*I09*I03^3 + 1442998806929971681460072883319615939894398311742247861316647309518539148480*I12*I09*I03^3
        + 514835242606429155256908778897765568701365776351846136273426602050365309715200*J15*I06*I03^3 + 2183469113151645729862463201347830001164195383265883003155985862344690488900*J18*I03^4
        - 109246979674640831753057069216740326530420335271894217893716283566962836100*I18*I03^4 + 533343964709483481108335690349154912508066239773343774591087470160713175623*J09^2*I03^4 -
        2144194625392569035010923780241448816760322908616182246193658097709054578622*J09*I09*I03^4 + 332022600085189565313293713151468864112391181373655378616787165233209225827*I09^2*I03^4 -
        26627898864388549005560627869142031621979054227377191446563291632800537403200*J12*I06*I03^4 +
        208834520622623003404068340820127132348415113775337466936859590352481623020000*I12*I06*I03^4 +
        72111871729207622165552407872589141189446860865519956856635877878177325936652800*I06^3*I03^4 - 2095971920811274743896950223511968986068910384712310198660261445785352669800*J15*I03^5 +
        223550511960427900787403574897817017541893324817584612022928378792215225400*I15*I03^5 - 37819775330466828781892528484971408098259032128134072696283601164955501440360*J09*I06*I03^5 +
        57503126620926523991385274728388403627395654876886216606209419518638603436520*I09*I06*I03^5 - 338611544153087968718286034789691210294802205965651217084389588289693788000*I12*I03^6 +
        633944991628387331990194257039042951921902203004372736064962164081205646314000*I06^2*I03^6 + 59559648270323940441856724628662636214964956303642118309495402742651037300*J09*I03^7 -
        55711021131675911882964352115428193710735610852772922822924707164122271100*I09*I03^7 - 640952439593674175206053003503817052502657130801537461185001703888357498000*I06*I03^8 +
        718383433111439271058796346256149115405780431694358636671052169393296000*I03^10,
        -43821701812289094282742186258838088827132315725179448028285569129572214963207282616776014997267438376419707464645405957999074238570180505600*J18*I15 +
        6212459564542450986489442230373171803134449975179745021856439282295431511260225818354137223119353205891374882935436785524569321100627046400*I18*I15 -
        11752981293110838529857923822544006988710968801439680745121663665598111380396860319570231189867883683612083284232223614567280154398392496000*J21*J12 +
        77029859295157777474722637796864719792338415839287658349846615667532416975331635887922866643873377972491250413659420811771061157823894528000*I21*J12 +
        8267571281152747470450275090908443385786374032802038751879283540276713862893181373946727829248457469962135043110599043428027805077807950000*J21*I12 +
        45666046951474517444765031208252129290556172535597239120289645335387241171645728518763649910735378870042882547905535027952065830227716976000*I21*I12 +
        51241058281059022690225703347774864098980773463725822093732486589748645888238639334811639209095162495700688972711627110967224508429864273600*J12^2*J09 -
        92127629566925323615047681677379649211893727783149257078962123865918202298429786121704805142668786844988166506804073526125006677915757491400*J12*I12*J09 -
        18227277181756925230947273941994645591171741094833104366207513162175473755991352533513940134610894590155134963326256566728341679240271092800*J15*J09^2 -
        52413666425159816199080781778612150922037447029414272700116689468670643227706858934972945574847966898350856037363159436753071934492522376000*I15*J09^2 -
        2357809093559802446043400260866058822328528249840581860839550930075677854326869620423194386130236688574967367459530499553319937225107027200*J12^2*I09 -
        21956747031701222853570906374067440821124522430133716484617644378548538994305153838997278964820229624921289377808334494443095637773679961200*J12*I12*I09 +
        43735608470518962608869143139314550527427725896391274067640745895207317403247873175248157333965144833792070244607677383279958669489004304000*I12^2*I09 +
        24728850847199875809760308900644519102215360825037369340583679839010040893344398314920250770228539537578538879331352853429413078816954786400*J15*J09*I09 +
        58933404739047702725739912638388251912241499677626829053423629542845323976765259826163549889819635058265963183623492557700502256671705999200*I15*J09*I09 -
        13157596179569329011458847984994943197338895599752848203112996704571523428080012840840068641191080041903011828032175333523704520084965715200*I15*I09^2 -
        3251378354688109850513684206748498580213472706305074359337259585501905282870411873848310208743847574206448133812530571909495779819362078912000*J15*J12*I06 -
        352789408456187357901364514113199874212845371740953801358175430395376857372766014842416386575908263418128204992825279197867392955138182912000*I15*J12*I06 +
        12208178422875582417715838245970102559085111405124997068360963968113988937454940941796675856693141274825170442241206451092745715117482290756000*J15*I12*I06 +
        4691161728252383715807739458763038097440211246770077583322369178219016973922117581056302424635882492751798869040703171631486101190423502636000*I15*I12*I06 -
        3915041381521517886585322306561078799294810853860930945925247280092120114390246711840425045273412978258792180927637357725682669487833287420800*J18*J09*I06 +
        1275042218039680164265295513131401174490691111855420232607207161667929188573025513098388674417066181165109729090965014383596817143638909500800*I18*J09*I06 +
        242603224552409940886538187481505451991862668127433796037576359497342130109617415422355218873681937041752197318349423757767319794682609344000*J09^3*I06 +
        1866663171210275060138333386633150012127915631363954140880120560319007726792849140800163979429197386542660280535601944932428286416730284128000*J18*I09*I06 -
        656979621109721835613878451514685176522617615663154028366771276655947630742416003343485819438298392258973608267918352397524030804467854419200*I18*I09*I06 -
        484964566552208899293222414436019371876267066630532157344825497985699357427814144149592420879043019469400028670543017895119624400408349750400*J09*I09^2*I06 +
        113629459055585703105477476518981547855322420625197143604147246648867593009186331512690945136445327505037680959159176599308843445082006700800*I09^3*I06 +
        33193199126379853746239788802119145039025314626245423316850373104428463236707392236816759241954033047828430559881187660657629725374705730176000*J21*I06^2 -
        188876627676784024431160217299152800471100995732722518938492456031038568447608805603656088531707962891635566238993216588138285725855801330688000*I21*I06^2 -
        137377967411218952491220641763130698897301279056434568044973485911536412406651291505975911818483510057153584683487889160781439812469885988185600*J12*J09*I06^2 +
        312471651902145341454614100132163152780877155079146152604143552454863224137848717146956500496845663054283164927633411518166698357002278765414400*I12*J09*I06^2 +
        55490976244264025448801839986450587973055494837205086344150464843769443368698919078356754895789286879962355557547713219908695223866844626355200*J12*I09*I06^2 -
        161659037408506440490603330255671546209683587952577518956038754863831782082092923433233090779569555985563149536126347384786985497285831534204800*I12*I09*I06^2 +
        9692508484455802988599818817984049232038240699305816414489612206284974958949900441804946479153749515791967362993326452684170845551816709329920000*J15*I06^3 -
        671206293716698686069576065972245726579755134340502222497855391391814726866534361825284969322438715116401847398982969788507292308489015397888000*I15*I06^3 +
        32351766725175034109472174947297640329383353131014884684929296114614335433318274222325850957430446024097129736162026121100146233429496046062592000*J09*I06^4 -
        149985623404685651043529982278950937867206481439950729738774397626520383100856698755912283370655852720095859842540017103459804183262809220512768000*I09*I06^4 +
        95890134105755040935789859153931991426879698527153724985160310606055362189371409847568072054938710957234326238062663131259605643107702260800*J15*I15*I03 -
        1244240852097023815588051943617190313847581341690123991767750883628349551871791815827081735413937027529923925762277254616494601682548478400*I15^2*I03 -
        61869917159846550478643663111293851644555002959278131837685910226421577101981078347219113180802591231210435550203268269114710109305388056000*J18*J12*I03 -
        1043581181902292981745438209982201638534658954445195344233319016366027160374365436308565066920206970950450496697236931837761439363440480000*I18*J12*I03 -
        104330141011830285008294829661453637676212944016619095169948945967664510019672873721910594814002208015997014904193790162141859868481343671000*J18*I12*I03 +
        22445388836366883232697987462361686909913239387397593605840846432780057221616315436060708445199964140465528340291939004390721070148353694000*I18*I12*I03 +
        18796649535786339243404811741698102865625039335172669561714397747562787776213769813459602985468098140723705923465052264007478946948669472000*I21*J09*I03 -
        29201441921807834502600600273359795371677790872569567630404752239734842860990749131899061105927700406489022952405431949413759217596580275600*J12*J09^2*I03 +
        8274500841880428992164091635881139096439747537868143176810457517405416228663669419968212659850704325492303619071743706404279902966801834390*I12*J09^2*I03 +
        3424812328095609898915472776229491993154609898990841499763658285673964901835280660105237622577952306398289964486141459706860394229563928000*J21*I09*I03 +
        25152359930151424817821561033816117982744081221301504926002531140919309257734393798514369281947384154769135160210887462337323402002093364490*I12*J09*I09*I03 -
        4138029075065523793515199633955392594056399199119638802365380334852692934694099780065803117331928907340370696980440939350429566346572848800*J12*I09^2*I03 -
        2197893126606604133620113901304200567210398932976585928163588128528119628437720635668739449843137177864873599075690994400905246556556251740*I12*I09^2*I03 +
        230192829086705596028526262075945641667332426030485995835920093005682631448535519651036264215292843954633274726338045979052519715323967920000*J12^2*I06*I03 -
        2927911376466357659463303240985784155466341340989822660596269549342470092812083818924179295429764169546150282685749502940749084545313718071200*J12*I12*I06*I03 +
        13231351028639179813777445313262707522921309581651484845060695006244837936712167420340112058058030021468565520522721540064321280387136353428800*I12^2*I06*I03 +
        4346243549398911464436876968684226604956539306999052084515798296851530750028819552231295180506099126106977932039705688137721420073314520800000*J15*J09*I06*I03 -
        157837152618090227592862639467674380848089817168352983667061283827986198798249126224439703839318402279099591972849295325385626658494892396800*I15*J09*I06*I03 -
        1055080207255988238887223290609641459572983408165475996291899131008949079867886955177158619876616599933669570463329046115726943360360114982400*I15*I09*I06*I03 +
        70438706574261739880095914944202720456777934964241171099427200870394078048425081554504576283708299782202242189971603000924864733062594330508800*J18*I06^2*I03 -
        30179611909361640262474524891106709594372841842369384503390508106524591556268632229128857244580130271848471621454871454222123068165114324915200*I18*I06^2*I03 +
        50856269199961145582376560611372636530463400558668275472037409396506687238913685240861157942455537317694568139918099247186430757339388282524800*J09^2*I06^2*I03 -
        9436909102860559487645419080617933546457737867928495468859737199573073762413384548439177282622706207779982147696487355301935563558393539408000*J09*I09*I06^2*I03 -
        1769520326704067136244919414208645044676661037362530861533830255674101461930772899800307139053040313736519039491542725903711805527259275296000*I09^2*I06^2*I03 -
        2252726037183556656618550941289351268726465448135183279990513360288770482112746891943241421263474848738812176809914949315609875768503369953664000*J12*I06^3*I03 +
        9154179438764498444727876239315255937005796471215122239291689023762799568085339886867884598706805822931812297131708557360441835953326657103155200*I12*I06^3*I03 +
        388865277475472441221779132671700417446042472613688078918865141510318694940419256511154799475379653162182658434012378826131811751078146201354240000*I06^5*I03 +
        77861195670036191570514464245925827447332854230630189921071441940036208361269419612040995746839778814888477935020971126765673839054486870800*J15*J12*I03^2 -
        7442140598662556612435837033975862830810829146003782971104181170120976889755320921550726417562137020342230162453858186155166030427435130000*I15*J12*I03^2 +
        102633957196222853540654765318936131574365420634052323121225908709761549453731309842170448133924942976826026485181263298097452533176571924890*J15*I12*I03^2 -
        1907025057741469988073673416489427296418728886659538762909071762968884920175128894549920829832565711565885215608296767443119187954425105870*I15*I12*I03^2 +
        28082384028515853812252312954724457039940239906438275415805040617654341559026958366527096531006541529805320236999594169597598054301390451000*J18*J09*I03^2 +
        660682714416972670990676523253599028451988569592816083351016924228543060804914980331516143853480106858966482229919193344468030271748321000*I18*J09*I03^2 -
        1141162763478515331774805801668063053200336086296241685275136312087789933915173327664811459439172849676910442821949217092049086566090929520*J09^3*I03^2 +
        2194675764313647448684123258043910340841652337558762603516619480591966918002824378663796733698361632608179196209161022760834123371321328480*J09*I09^2*I03^2 +
        38923960279475261940908122005979612780415667201227373512764557031363084098703000526953044352796475882144331831054874165232880028091586080000*J21*I06*I03^2 +
        1972031650974713839953377545330099315167430165562352057479251247678067921938255357670679161655935601930185125773356481128743080342925009394000*I12*J09*I06*I03^2 -
        867340722985651878442046880578840416433649293515181103353416664932785982145533711402926366851803381606903721945382722607411485836093240137600*J12*I09*I06*I03^2 +
        432131670136131745938095773366553669418602934243266374743915979624835722322499029674623159634634860615389559115291847300941018116879075498200*I12*I09*I06*I03^2 -
        7038072040629861511809625812153422901880301595151200597913331476565936711338295754460693992911073164913989641160830682513381706203288406566400*I15*I06^2*I03^2 -
        310657206569617664697084350959693458783371372441956951101221965048345873546474301906820716049651436082058176065968781476179985981105736220736000*J09*I06^3*I03^2 -
        129660211644854347438983669048434556051206773458340484966817287898979128210691521428720837724668547100725475798310080655236633086613627657766400*I09*I06^3*I03^2 -
        3654955070747643949920526563952246468975564737756272733110650077933429476134631109009799148784376247804534681536311960466409070259233646800*J12^2*I03^3 +
        11168926192273744192197679417419761037615823251002830188112757462481738406761910747908443690802991021708387397966315151323721797909721773610*J12*I12*I03^3 +
        40730870478029166130517144597641015250690221725822215231023725847873514078404460528712920417596943199793262241503002484407472369325464031660*I12^2*I03^3 -
        25683483665956573338745587966525864485493818805476981158950955140891753910498237588626185382592291555674028371428136010031419629496123113240*J15*J09*I03^3 -
        6258817872640435308958400373966060387270849709462977555551250551564914253048993939022838205219381641244384984523040109921184793002940070760*I15*J09*I03^3 -
        5854538945817345057504705640248829778427479382562204541743329430844478253908459243992063241160242702933544509836360207797835506407007440*I15*I09*I03^3 +
        344203129009361499849578968441821711315480170184633553631027628937232349026124345319450610330683240359325537419832163243052945411462233560800*J09*I09*I06*I03^3 -
        2159608944726088784943669588361489444343130838779760914160621222504780203873861043707595672175375160409752852045589447589092026058754697595200*J12*I06^2*I03^3 +
        75128469156953536609745590678240520368602459911707205487740923428807438454869608537866510159672022931275608759410022348243561709961271514144640*I12*I06^2*I03^3 +
        7498896468285736639635352104832056133544859718053104373529607165749513007245881968560598919450832825256782605282385748527850942354881906974720000*I06^4*I03^3 -
        682994352145664990998466612803623320926635359465723115267457229823906204265740205012027831580185093594896950666608436889237842139035070000*J21*I03^4 +
        7028909341704466384940611533126502692312110595656939944153686405836605645914264286380872320641185851834288706622591764248755295534500456000*I21*I03^4 -
        4923599128250448158969228546530570960766446516130999182124677941922465310174218594202452436851337820477828430394052815872964399756894905737*I12*J09*I03^4 +
        1658995003413955346204693973318805858336245047108472794036990561530371488649497899665282830698863035760705017878643823514907854125941866080*J12*I09*I03^4 +
        2892418804347608564044044949050706851680414294954137145109869846703767646002034177447820515144785335375767963683010242537074936155148451589*I12*I09*I03^4 -
        46088731682531585853300417237634278937482428766612959316099807849820633830383248389644993258508370123004231310034760300254580191191085802400*J15*I06*I03^4 -
        66866990601187216360330865584794420501406968631855250332356379216051650617089414404501573417280152039269565760968522851415027165484500487200*I15*I06*I03^4 +
        4967913233255340752032398043961352964383480663747946531272969737672268567142323909545176415619049673568204125966179725218572267594323916133760*J09*I06^2*I03^4 +
        1935269597125954408016241632521224874354374756918016675617373320152558814113162375249554237943518437002452501235719467912638902512156063000*J18*I03^5 -
        681748613878654072445615935584536300100071175288280744054723704807282815337821665385105213544780032021581490163602402879094674833620966018*J09^2*I03^5 -
        176414545135412688420218188331738484270953291744392286123492033764995576735132890946764056046698817696655719683550120847396695242924728474*J09*I09*I03^5 +
        67623010255099536365547137166197426668160917915961036816824572002277626184227276013032551668244103130795259415064283445540084652389764213800*J12*I06*I03^5 +
        165003645458250843724234095972013737641918983257103515743296492267061029250815734860139252835237285524120193618022270592759285134510866260840*I12*I06*I03^5 -
        1605185832317127835455042545098476123998074635430539471593472970956396083526385897940354868462322322213755027556139553222736707940448689850*J15*I03^6 -
        197643418479863625965710941409976135974692325760246177070545840083478556137065261059506286647417189491947908376909524345352525966363660450*I15*I03^6 +
        18547594138213491940924231956777400616754329408166592392071747633189583515458836086338593931513053208951817669425128877738488885398971594560*J09*I06*I03^6 +
        79360979770004407663953800287811444249058886993470663800498017255955578566323801489393676278112763302613003959505080035343769011874584000*J12*I03^7 +
        47593126842569200458348244111648667537661563325169051365701055313560827400860819962785691977469489430912367546975120364797850102752170500*J09*I03^8 -
        31347606443739959798487400831775852514365640553618891989849047911448614246536477386142067967010961077901113440976675435472576700021179500*I09*I03^8 -
        1329859964810873377340639167180859352627673327556280604608789688907198758443828074865860541273003259686800060757772822749623346056944182000*I06*I03^9,
        82783853311195105447524303333109389454360172831745779964292715758285652035020137189924890467288609070925181028577268091696805236650908044262400*J18*I15 -
        1122295784699310887498053799277404068270527177239520599943721026468128998418926426474692722554886422848031560935838530474919943292760437529600*I18*I15 +
        7569732484572401156665246446453958368766605432514323955958756939495709195714406590364219832557306555195593386060356929823095911617014754320000*J21*J12 +
        19674127324444976987199762313047906405413749078964362648482283688365983054261184791929980066902294306107108658896418095886723670689213256320000*I21*J12 -
        18278188556585853878959396307858402387635802844663373493319294729842189548855425617010185766421217882147217866615088059145867979741479288900000*J21*I12 -
        244931789129945278190942554636279655990067649159139239012771541068562534463141646228938869490854062417456505233567650114428966982285184665504000*I21*I12 -
        45241965303449325519019200322950616107810271009181240099827362050951878025904037786328133806360929151746934622869941336403664161221044777144000*J12^2*J09 +
        86319086584937068638367573257648870689995441536688688730696092969791382008372107909994161720271812007866871799572281002217607739600092763842800*J12*I12*J09 +
        33964564851014194570929713415413617620441886089049956429598959676976099313501011628122667539898263580487503123334781738273626499176909653496800*J15*J09^2 +
        72057857258163664025558448793045320080444322873171346719813190416236517885114587650516906929154877826297201373655979717524996133994673592012000*I15*J09^2 -
        2653290366105479121350485754715886222185381708572517461901336941832092600313099115942133371568308023117191498237053442859143500769963174640000*J12^2*I09 +
        89677391793637038677602662438603515961199310948763835480785519804285202890997732028118349218976984478345963123414473883765545193607231869709600*J12*I12*I09 -
        130059450720188017895345991237786420431235206262434900914753392383392900923902811462552631927002883266670712848584691829401859037921166260748800*I12^2*I09 -
        110219413990039267983257740947020269428606063438597537529786794625870880591461487044900138307570217315607378647058481415463974860545384799906400*J15*J09*I09 -
        101738805995247821297444907388014760374843006730012098297213907606191383055883017515048628699155676186897614704455601467831695202529531838671200*I15*J09*I09 +
        28826221031229409255372187163100533221647002779157356356245206242839856929130972185063591581342476290305671952502353875150416675188753765491200*I15*I09^2 +
        5543671374237154376453007583405684617212028499148658235469824060552629722135832561725423587220637069000212648425995834256772837951781346884000000*J15*J12*I06 +
        255613842812656745702782555803248277834287319377990549442844053715633944742066374275677384816502009605482926054370111273359265383513214638688000*I15*J12*I06 -
        33724199508115146532992434721626560632186454620370011429737983296960353757280783662035074878778703136498868971005432264848358607973833117097387200*J15*I12*I06 -
        7750416724052529892036005009388138550445558248545884906142604530295762922593126902033565344990608748107980162015209763322611848581284798150798400*I15*I12*I06 -
        9802017023741120141036863508301349027830189950803516040648786648288474474208980705797753736951334752661066384608203501178139328517260241272156800*J18*J09*I06 -
        1177291561923816169720037508496737018115472071431384284931813430862668906927606681729122066880094052449805402803021495356346075232741003929251200*I18*J09*I06 -
        989213587556579579348326179605436825348869867173081065152541005648491562420764880714296698596861330616986004267004295773312570652329234095830400*J09^3*I06 -
        3978550567573595378450664936445132775816074679287050477799997232595589803779851874566024809876031800891699992210689422204258735514587643421081600*J18*I09*I06 +
        1836770514167592954109086389682899547079198532326978715821793001782048862353644601016208581117346787240009771674998663405648981694266164701363200*I18*I09*I06 +
        3203944959597552171689723318516476101419194235196101354738356791979921296051562170174252950374698851014757792814840252572745137712381461799062400*J09^2*I09*I06 +
        1015026945867291675591340808245608752308234524261763160120509424674534885773702777817728821573422902641450694563171020421294016630729941586700800*J09*I09^2*I06 -
        412357599030963317769534540383559144066241851489936981494559229136741799319379849166237397917313982138257652016141563960223604862651122800192000*I09^3*I06 -
        49312828502343371264778261363819429941996730016820888782157847202300417497837495035150859208189483162287221162102089881532684625004746408793600000*J21*I06^2 +
        87758556487540940876951150378345840687432611249814197250438939549782711871437133934336133249911472084843853798258928043657340874358682782771200000*I21*I06^2 +
        126794970127850608328619170698833757404085784512722797210234840453099484773172071969191441665835431628192413578858976887705310249732370440637056000*J12*J09*I06^2 +
        320774604083677410885557140536962913295068677801559936308895693470140093620586302749381332803490439786995538502389321061593650927848728243565427200*I12*J09*I06^2 -
        37198613918809073923260842200087336240738166007237880209149602321435582235462570691936306140565797428545980029593730202406229336109854116327936000*J12*I09*I06^2 +
        420507715524915846295002665865272728430348523197858902083300856246179306167538629197772514859525121971093916376208129240292730651186464878279238400*I12*I09*I06^2 -
        18926021164650357532606717552864870448266243595123734785157604924392230952667435333084983060604307078931093205683028399795899739478519412742465280000*J15*I06^3 +
        1953999378116863927984336952569998416812386638704448588895638031642268410613123008888921486480760875214659775242642517510711268333887868954900736000*I15*I06^3 -
        62725692677222485156452036351877785703531765352003506857733395396321322973397579724196264856569957404118765716052476194064163586934800496560000000000*J09*I06^4 +
        245122134293449815725517582735111025718919429877676359642981158237028980476144561139356536981109890004307107392393192042287082684697961984637200384000*I09*I06^4 -
        204090777546239709506279370843772861499077827055433517489521472180521082280115492197932670618476042390162116503616243192195564503663877296752000*J15*I15*I03 -
        17784859614323528802830895130366152368540540933199749522244459498532340743328930817485221625344869985834357492664596695126919825928929603056000*I15^2*I03 +
        220009579942319004205123288560338116159276315773882594637022509950835545598391195646924712799203502917971356161149813489051334564451162399596800*J18*J12*I03 -
        5723347468956336045015943227761630073122992370109844286060662927549807170602016398763013316141082886734422876071942662339733478446696370635200*I18*J12*I03 -
        79429877323668924854879532314334334986324454032692968156423149835631900409372560814662796525306146460460828697157286955753040100217116324237200*J18*I12*I03 -
        22670810376900073468287401383092705333071622840923917242086883908225057578466399321669474100110844966082582997657389351386290999857580987803200*I18*I12*I03 -
        42360240580881660021293658626329003218839989425101046061366990650890412331043013078688922749583734117262569409496411719349697047197678581248000*I21*J09*I03 +
        14600459347202905902428822261649392407589173764005813185588701127857016696696906329026339567193718112053279065589986310130527927067107099987200*J12*J09^2*I03 -
        296662110404017341405799846340075483053068343642824644844244015061054315213955013051275910322522086406921125398002584219334702331604071520020*I12*J09^2*I03 -
        8165886481167531278157757865793663664485981622565685053057980887073166022737853839140009170260769035337979434945094271472932493324974444016000*J21*I09*I03 -
        33187254712644223985810717614932069154799541928445177527053152290050367338542029453285651728998497387853986130037260995476775559269848187177260*I12*J09*I09*I03 +
        13016400311589815626223243579086251260015729823749943744518622804352326415355895135441518115864562634077327463134507045726779751142471961429600*J12*I09^2*I03 -
        14335587833297043451215192202741033707816486910921292849897599640361235635340316304926930929476495208130691683756456059908865283435358092623800*I12*I09^2*I03 -
        1341874191852604021763878973170510988714425964547997200939460146706272416732351971836139460870120242414992617405722504778919438078389997067008000*J12^2*I06*I03 +
        9028610395862105017735892210321868470893770834374601595447166421249720969386647849998173281299512093693009693519905053795633673030568334006283200*J12*I12*I06*I03 -
        21561456818367604809493706812882012734060781823224226874964881769596416595556814049939419583762038152713753900385060941750256150234000465131532800*I12^2*I06*I03 +
        7297768287815587328858309209129883187033952533005308930582257700741340516637738039226945109484607690728046799386204906394260433690653352656185600*J15*J09*I06*I03 -
        3879385541628380158858818139574622652205395248940223511422542508069448077078829060667718353091586729423841389277486324464673790994241684175404800*I15*J09*I06*I03 +
        2340599319920373836231018790988475634969161582275189216898807756284104471020048806181785027830905836253669814167852159193745909039045606362624000*I15*I09*I06*I03 -
        12182006396874975720064601473050586222385029525299290069180480583984199847658225419430758208397252730850492430848345236160106729575772027714560000*J18*I06^2*I03 +
        67001261873818092901887150284837620387969983397565545067754171852801525509198026693788283736413892798902023838334372252631705721347795765762816000*I18*I06^2*I03 -
        95328957469362192678361165279043348041889631157604492705634354486465172636136101579853958500405084310744066229927212916738675216013134304162342400*J09*I09*I06^2*I03 -
        20065843939722451622454337822188256464125333396995805677637082661116963640407469182922985236329574637714262808774101822769971021953504118749913600*I09^2*I06^2*I03 +
        8632551345886073393303646736263467239449174610715314454797460316657361236878753770019753815501477099622814071602467479389296348018049081381193856000*J12*I06^3*I03 -
        28840796765401924159600903377360381745253293058378150161455057417863632270568448346402228485426298403037066413701901628307494792374416433408824627200*I12*I06^3*I03 -
        1143736646073782124922300441131946116073205014414747198861601556168573067619878400266610389409990841156351332068047911551909272200815752549603409920000*I06^5*I03 -
        231369749708185571964504384778396806815262526054257766231749719970400742321316209883032370736520106096664971777132404874533649828028843252155600*J15*J12*I03^2 +
        49331480994481513862658272890232610337306335856060193912075418127953051866090387469439331646290190680362942788271943776414281733063419067201200*I15*J12*I03^2 +
        86536281024950667030929195974529974851328527737575686276042312089868483800142383363699341028773040807669804212319324936093291577834395211952980*J15*I12*I03^2 -
        79429399534114746056472069054156616503005833917872927306628457966477969387477651060206914599828964511036884781377489819726985435242732827855740*I15*I12*I03^2 -
        98929805915797397391737075116498199946177701811047870617436263403170527005906461570396664777806046374978918422988467610891811844230497607910600*J18*J09*I03^2 +
        1506491132496613425713475685117261871055783195766400680869800477182616013777693973546268809778547003547397219761607648476283684560160492915400*I18*J09*I03^2 +
        2209004714052200261037217077546354036737027590046620857012045147305511611383371519286354536335308148669779862202872738039097108021308665958640*J09^3*I03^2 -
        9516891164270974204617891443248492718745282054128270916432395963157266544148881839974349606551172164698253224125368968698663488200643630089360*J09*I09^2*I03^2 -
        55300999850455672406052300098059853102685133429669714292083450684022929627234628015411374397912386766693809097739024273427263115962217527360000*J21*I06*I03^2 +
        1321369177143018907731779815241561761284969039841590015584378670119494363813935300301337284942456710237525876917438982747433102955597387725963680*I12*J09*I06*I03^2 +
        2924375296848719490409452512160207726404878567245402435751212871082459388264176697563439710286745372184101114629956945346949193454817351094270400*J12*I09*I06*I03^2 -
        4040486912486921196832122123466736030265242846891429077624106319224354191284510278576150627636523546861266092937763348164322913723988272339194960*I12*I09*I06*I03^2 +
        127309995976360453617092297547607936024378846958415461812478139844775710737076623468842192277318982150879989100443545970852583088707343027124633600*I15*I06^2*I03^2 -
        595717423715689549723964702531761247850592510487928370939802316189819005241167783282939601574463641462743022639867416439612091358008870119601510400*J09*I06^3*I03^2 -
        2148743093755887454555061264606898984559138894286455303580586189849660925544459341862793231756693021811916994967682008430906309516221022479785753600*I09*I06^3*I03^2 +
        6366575664321805531134057346791628430022151176387112288986580817223069448967398064410066234406152913572600107837872395019015814695307052297200*J12^2*I03^3 -
        46449755328522302934674882824928926804804295500850202379537236737964268150749121191125235179847681113648112115610303267375513989826130111358380*J12*I12*I03^3 +
        16411185971558506326822117144814511953262619895539278056595871347981713339627164220076404007112016090288148275858240247669095622828979934951920*I12^2*I03^3 +
        85274242658240511649043517389456899677313131602962023241540380890381500277305819070135083094769900874359285225449998657906525631145135215684160*J15*J09*I03^3 -
        7353496718568429171056816085605248691384460994192809750720175720664385983897473137319753902685705307472582258895177205851126182417007830017760*I15*J09*I03^3 +
        4630945279211112692508629542596843425655111210145425666887430867467762614072939247499902727025412172843439066952370416286553952159316046904160*I15*I09*I03^3 -
        835083898969273289520021017293879697773160720348873729753233344274109424215112589174172603837742071382159744452594348986659253274318249018352000*J09*I09*I06*I03^3 -
        1388012890929169864235668129399754331378011812352168725227375993850463209533408664831154143595635338043535306380822604152946053030504552965523200*J12*I06^2*I03^3 -
        107404150075437335529512992724827363535498853209910726486879775185218522108759845629709822894460152698471119256928078106245785829654631261220145920*I12*I06^2*I03^3 -
        8459092045451075938958503042449091480406423173700206085003697656813221358876157907508185327457842083173322492059834543900014595088787093797076992000*I06^4*I03^3 +
        1001921584335759393515273697183233114254588119921724054430094173113410212821619902216024926881354414074569241625228257925579982551186147547000*J21*I03^4 -
        15770215662544890434939208101958627615684050688853036677101084354576398102195715555523756693885139930231205864620638407441535138126369814320000*I21*I03^4 +
        12726610572130011772149747371607095463628433621701176607702834652854501646070817307644534970197820667215801130896619087871491183342500566113516*I12*J09*I03^4 -
        3213432792605274032959791681628541797730659920553507928694172899409111884066933501077579097182922257346126993804446578342044601012139492794620*J12*I09*I03^4 -
        1966734599110026426910158828716046639839359561006156207897300932116358985140815402773182344793953449527607317644550412206577507589237051833032*I12*I09*I03^4 +
        473915653304987837115340581662784854702795819180018501348917660851589609468648948565186665337904454685278438103102859867191356772025613008721800*J15*I06*I03^4 +
        858882993738832639748414923027822142190736162092700931565462163854551005545574686095929213925313099335485777080525087560524156121412780226900200*I15*I06*I03^4 -
        1736548106632887092543869809727857086104352452064528996919738801559713163904478991004017233041308761564721746222613218481787157374437960870868640*J09*I06^2*I03^4 -
        5319036658005257764728563475202499351403354035104086915590076670515216598132654447263291123742758882162691568982558958507526351151355947682500*J18*I03^5 +
        1405669605773054095286932713629343883917724488534091658592978374119229090024106137687781510076941828917963138064850364255556926930847536127177*J09^2*I03^5 +
        383150584792335109098156868246268471505325497028685244585859652245501511060149519578879639714755569722093442211367901331828617778398417969161*J09*I09*I03^5 -
        147144430065328212907080491245432453645989494397295040118030622093171442180671499976656361331249515049600186205814799287286532908272628332809700*J12*I06*I03^5 -
        188144448355599016933217590944032828030614185520392073132949827409682857549903487728251873853233297710724733024109563727546025157552576453965920*I12*I06*I03^5 +
        4037956856703748371688630914774356486218707372531723883250820296672470456734801855492964877213633639933008143314598777966201163275255022142175*J15*I03^6 +
        64871242172005174326230090893200282813987400806385168314664379805853167436495797780346143984283925563652086069810125719277699258342467066475*I15*I03^6 +
        1144696019003794091034477100431912798138625020978219969639011731468250325482849380635508108241414018610770974101931958099830190524849838924160*J09*I06*I03^6 -
        4621680543289648683118060403051810383154869179347332296365687301798939535117107723648122383806512856848209736440682077012354260856092108000*J12*I03^7 -
        32512557688609736382707250152810094592849308632290749734333358072598166850232484354567242953530603298992765692408037170123443928581990778650*J09*I03^8 +
        59144343586504314493677072419424463968262023489190800729833879247708014466555079286242894968449658551525669663915084890457200773605621363550*I09*I03^8 +
        3649084053987247926755155140679673919944413480441503132768177984449659431869998721111596275521944565828068836175167971896043371789224588475000*I06*I03^9,
        65383677880597681208178563948253926631800824650960483276153837991641615705368681144843265067932803240379468650339598630304631807600006435097600*J18*I15 +
        47645443933614554233799944005069314433986004893886563583337053071563123465502923215032374454966126147638286911118904129423068175035782954521600*I18*I15 -
        164138270006966830426755597191507997815185901909505474476358009053108641711591470897667662725869835212308858342645234266047515642131088719424000*J21*J12 +
        825615040431609746534504649905500311600564867155375172820281786229513278008392958848887232126895888760462345459025344779530687571655950929152000*I21*J12 +
        50542068480240234338127002084222434485839414047006866615493292100493735761195108702284384250723923754876116264408115305814909860335364387424000*J21*I12 +
        863033981341200137556411659046840804462906170227286856634143229068315460137822207267172953319799386897497324836244536144517406850845743821952000*I21*I12 +
        651200688459808470476908395365625997017896794502948998456612657126372769634669460990220708775503055851257314851992005991329825303503592569798400*J12^2*J09 -
        1183163703408388351944067110988084398138428333054846375827229216363039221768215547520019778725742064019972764338480209557548235489615264187484800*J12*I12*J09 -
        278378048901810011425591263055694809367975260698864770232065915071827018132143299079375402495952295190833770422682733168008354639513193442097600*J15*J09^2 -
        259970357480865984486443707920834793440760705252599755905639564963828135268461065731519892660456672129242866743557211983790626507732410359460800*I15*J09^2 +
        15055837284155557127406851645871100927329685916214928400570445228512879185116577710430916852975314266103210479609074126085358832937157713331200*J12^2*I09 -
        171953722619453962444359164847885088699200132764094460869077797368758417182431503750785972873087212909835178310155761946055457006552081907635200*J12*I12*I09 +
        317778826698704189476444726411281045831119461995839332863122409206277505268166112496649592700362997985733209311394189518598261186716726450899200*I12^2*I09 +
        367997062399462542328203948586861486464494631540512561105225317719637877710243118509199846166576912662676452658389673501267953369295408518601600*J15*J09*I09 +
        210699020600225224387353073961031722690859793473622969947096588774543911339342096773329511592866293323563986178994531154174445875143020398768000*I15*J09*I09 -
        45134795535883718412683189753302543191679813462214923223817794753685200701650640582854632871762619564379924190821266895620540057098384433843200*I15*I09^2 -
        58167966365168363776126380233379324893189471525928320135817323387977699476920308500295713389136047826079270552948386686558986207950872020239456000*J15*J12*I06 -
        3706428050360002600527803228941998710831196959478633474789861559844503641833141528455339722164373898621156890539884342661375360217992028189792000*I15*J12*I06 +
        171846210608678791747210154211220216956241241387322841332951895572709618370963424448348942357453453932918920937808434409273413540745036959089913600*J15*I12*I06 +
        15674886828156065937444954879231332245651021628719321292775678617425841117882479722080448757863199204524794378772633120788340834563047660750099200*I15*I12*I06 -
        35981216213310565492849514138712909858640649554853458158046075612276903588816671854778973720537174170179205276744189579915108331180608427679664000*J18*J09*I06 +
        3216153361243732227826034416931163873513339027057532677071286188183492701853795937700169307573867507502422037787854831108888741872577452708451200*I18*J09*I06 +
        7234909500544247078520288383333206040788963718865926446076611555376754284768655572207015263908698396933566649651826998665150570096596742563129600*J09^3*I06 +
        21965695690407920564385617526058561799162832576200973052221070061669598562925209025877220225549098097097850075786947890984449723088467802366886400*J18*I09*I06 -
        2506724936869831726413292100652452756552662098549734753807996806072023242838169415342271098137376336827467507791944956074701436630182364429376000*I18*I09*I06 -
        7539676503139730334072061719343428699237297715182765117057674996233009260514373095395210834588211448760782723481327260180517665013010652455603200*J09*I09^2*I06 +
        1529738927461129343711478796511099159088263989200649850368092012735657342687787178388876489770143016318970303276882155770534077263913632600601600*I09^3*I06 +
        329238694645575889512175329463153315271821892485398969350959013946225449265587384822443091267025480085195671691179497585334950600972212051352064000*J21*I06^2 -
        986069734084332177168523137948561897893259725135377762873834543092122768791231291277455096039635676645729087189884230775676483462417875586271232000*I21*I06^2 -
        1200468497254571526945984611703114370619900521958308022925291621079406585232373261659322067064645296451909827817109979191143185504788624607003366400*J12*J09*I06^2 +
        1725114140842707794343437197402445282256094879644629506970052114385052020708604248814834561152843953836164313194246658284648006455694240340268480000*I12*J09*I06^2 +
        630355286477246237896150926419796989478466683369014435512043052793883987274975342159984224544205024609989960229757893698078989879769482653300684800*J12*I09*I06^2 -
        1355577552871815205515342342619988193120919619872337164366245637994940897212913090562930779796697087753946488630304508722622183225610108799281395200*I12*I09*I06^2 +
        133504677864881487959048861206019562523791093977637663355988212570309407058317780588858444902651958763689023349100090057784296085883514949161026816000*J15*I06^3 -
        5760469553880702335090825231157938904272541821641513267722128166423208991606516773309996366360103189108454543491087468396704865123165460044311296000*I15*I06^3 +
        461557125337046030253147309723710241897228717557668561879757959748319924842523540834111241656633749124689179490451396477337176463036355303178286080000*J09*I06^4 -
        1751204486667280575612853948747748697721148893850344297806537743208530863764318229919086468224318946459071175228062397689555930559551817832552957952000*I09*I06^4 -
        596691854143992647079364469751975581415970759797498498210515453636029179087879994794376719347050575804959878621488728533723945635683213018169600*J15*I15*I03 +
        47792458161516689105687778767965970282437953799420939798524115482430867145386905452251292199070821705362625287991337132303162009813989107500800*I15^2*I03 -
        1181817681198796718764070588827286679155906338052348579093200057072498683272349801182184120223421915312143539381557391896923042073766808740019200*J18*J12*I03 +
        106857728783205354219775470940217407811060984543808986809478160849847160730146386588489506115875617594566059101980144870290072049117747481260800*I18*J12*I03 +
        2256023550783255006572342197094971516233273664237473278950685533398849463694706661702207796375603643802207278611774471046258875925254460317520000*J18*I12*I03 -
        245447920922734496337372237877355604752092804852219415345631413707334874403537760997299887967757499983983208012205984213287284366413360270560000*I18*I12*I03 +
        508993562819354683275439669401652923005984260452048984164278778979578063990344781728067551634519655309671605447197707728697076494289132168768000*I21*J09*I03 -
        391722677516547439427063100908728014361480469122709113233954142761516441349824114509476650508061404757110978945463746397358177889229344293434400*J12*J09^2*I03 +
        182404355168840598190969218751985513968533149639321090892415848338652062453729810053131139684946924125535078055963142120874226231959228389540320*I12*J09^2*I03 +
        47876249495135095689498010295137971398364955963966442787612060696309910247737729005513775045022434630661302619770305528084117012262961053344000*J21*I09*I03 -
        327428801333620658496639377528820224617519002564212388375669791016912068823034212132787476558903658721411942216037838598405925374299572989653920*I12*J09*I09*I03 -
        85884325731687448054319583357060745420527561991014683479996754518504845760353116800515479599577178332447081746697074930670694772817093958441600*J12*I09^2*I03 +
        201269766699785226913040544947125129641389171004899719302163316251653795404127485489345737789987078495429388845450098383306833681073557898026560*I12*I09^2*I03 +
        8068323299958954218371610678336239733132672665142223189307139062022748490439168858459846995861823643345733918529344349768389547540918785642896000*J12^2*I06*I03 -
        5454452006652964661587688061002166514675957693036788337837429962207632616718652819628081217954465428302252190973379536453395760896905990990620800*J12*I12*I06*I03 -
        16683922039535183469002326424196292048556569111051491539090551353904251059629555032491221620893365575915110431545839191772647085924470480158652800*I12^2*I06*I03 +
        46094133990152289444660580544128971617321682702624749235683727646234328325914191113218906066597408220255531494046731617579737075184197611176041600*J15*J09*I06*I03 -
        2670111877851737585775429981052907001402569111689439483158597725494680451079771141166863858537428144635736700185494600511275158177959410098556800*I15*J09*I06*I03 +
        5704002858809022367753745696418547247409059945223620026088559094156669665555818137668331238641484096900041151361465029450763591533322857382912000*I15*I09*I06*I03 +
        682877303164208985076242100686202723253809472310162959792818561399848739975787236146662290156613177769149078975663685430300845022849330879290624000*J18*I06^2*I03 +
        116580024761766053152584766196687896033645875031009336095837002249893732332186381038419025828060950480185593574675827325952170851158257591312384000*I18*I06^2*I03 -
        194639294337604349306033142816011324694469806173447370958013037289974234075937723440435804667353515287363625822671022438089341319645258900613145600*J09*I09*I06^2*I03 +
        38313740029322487796886583055676566794906560779657021841283688108847931289925553453038073082540382666740203482598280098812980072810458601524902400*I09^2*I06^2*I03 -
        54670568300164622531419708096135696672250406979822120441167490094892378102665628648324339614510369700155666669876268380904449602985627114164394880000*J12*I06^3*I03 +
        192716916334007910068180749921537288479418455455885528464942966461714060362864866927541759266297421031475843196794333441597399836659807483240596684800*I12*I06^3*I03 +
        9085286897737975590918957704042303136361894919758315050979602369298275709795928388912672619912659789406509250048492004643865769246324738479425650688000*I06^5*I03 +
        1498773494123632534170410037869101907816947728501364773473321858708372463337722691823090880426288908504381022659588063293773405262122206457668400*J15*J12*I03^2 -
        39999357080745236498714461792468622214830137481117532301467440891614115424911133442451282090090005701920613927538829913866756117263676090293200*I15*J12*I03^2 -
        2069238774197732468349983921296007335210277229815438150499060323815498680889699302955202703906374577206710090595510044466753387748692310112567680*J15*I12*I03^2 +
        300758391857983567273452173259878529437180088745106026482071933774291952599962895894477280786567721796549669353425032505775518692274735422682240*I15*I12*I03^2 +
        266413366217047885234480701805992649658968398759591708853177388019957533734742903789409831286772840762105216220047147902835219824722506776355400*J18*J09*I03^2 -
        34445364649265905869038047273861360099372142785829705617837729037359507877067233973872412901525087876536972810962172018025867159644619450974600*I18*J09*I03^2 -
        26703052492708537418031502757000353314472193155995575170106985425601430085194110247805918950360960775781298328170617312216567689457202245659520*J09^3*I03^2 +
        44326983115959437453094051376210051916724155923334653285525171837852031829482811639471907663963595534950855053519847731319207778336992281768480*J09*I09^2*I03^2 -
        251161992177110254809524963949438351496215271830229263986919978311551787962593356168210519610354954057594067691418940353372838207188028216224000*J21*I06*I03^2 -
        1871444141632466774346704355140148893122771408855471758219963541556435907390102565751862944997328347547640612582263460357113860890260197437573760*I12*J09*I06*I03^2 -
        16500645492649858939308251601336918151876423287304874878517301121189036414070926452125544784735224256609591618930135166458775371994684464034774400*J12*I09*I06*I03^2 +
        38401763897870265259964454094031570011735833814264985165713454936802675883374121588049740268736486050849821390263893007362579222870541409365861120*I12*I09*I06*I03^2 -
        743623632786534863835649826825636875225508637778174503997074267256510764312851949848207490110774190923536487080689391121950571488581247866382464000*I15*I06^2*I03^2 +
        16281008087052602598313088424550350704387686988272575257759889281941881345127736606498355643037545851651903314499011295831541416077594030869052006400*J09*I06^3*I03^2 +
        9298874379785661866562039879126853017409291584316173631335277601554660372214741216845150722764162577423936327263686044046964064339104358670695705600*I09*I06^3*I03^2 -
        94413897114117979847891226187256859762252719276918978932529719932488289658088518772498654322107408296933452682627672918103608827772907567440200*J12^2*I03^3 +
        513279595474190337419087921873422264133427636340437513433349905464414959943007709022231973359036590104719345838609360034599928301454274865689280*J12*I12*I03^3 -
        698203286047483115979216140725265636835518750873694019370764637907078694033278424574101349562535194948920901926485285383920540954667697893224520*I12^2*I03^3 -
        248623847742721254997870326189446720260125398443976954284574720285517027708999461171522669611683604221344091794199353679872626432421731188787560*J15*J09*I03^3 -
        75952308272689057932625273346898169114271061238608525009244669033515232608077155570764811343376190459804012222777482882673984942468603797538920*I15*J09*I03^3 -
        52893471173587372959685504360964171259571431064908113764141854402611767947934646506311096889365302618677810046804085947411928751512701892072000*I15*I09*I03^3 +
        1779969421998640095383179621398042278566219019553389641521309328877734053361978983430140527985943806119309884897133473651525076506878589888368000*I18*I06*I03^3 +
        5276100174603900620787974191337319127117941532584623462193080420888994896522139382509665216354754922208242438431033351238324885532163597910970400*J09*I09*I06*I03^3 +
        51751650383519015780518307836384645491291383975838931289904682603567056756672909378008347010971397118729646029956188210256370938560734054800755200*J12*I06^2*I03^3 +
        1335364663176489645664101456027407324637137873125500783619915910925032777671105994086737589203387822223163610309666087033126906138065537643230373120*I12*I06^2*I03^3 +
        6759161261926537068597429796569834224614102329233672042245038071866959625659369076997810541846786232304311281036419791906012483887732556322537472000*I06^4*I03^3 -
        12857211661667573662830485829683705388378560189415343707891811845660658600941232966904117689700364309054601455809852338208340718983641800305000*J21*I03^4 +
        154374496084729635619383750544732664018516635878522308980755073276488533039849329681536827028388310641062647502221152742133066025898340554592000*I21*I03^4 -
        37685921671774877437142569491817530040279985802105137529797607224360101722311713376634062543524412718453156220460864013295780290869285208919746*I12*J09*I03^4 +
        47712597637570519661234238935080424996296898856320787680756756110886281023327083084160279453953852279012794144885286108742586549623002812852920*J12*I09*I03^4 -
        42902948397284002348322862232134846232831203184230925091535243448945321509254730258799483722933867471983150018696460321334009554575205049196058*I12*I09*I03^4 -
        1177573560449719081507060159366756726743406771276050529043015393476243854874635043059258210928579655456171707589124008284135820736377064575679000*J15*I06*I03^4 -
        4558707739804177506989992311314264125592833454415622679657207425522844276077724594814088590332800926098697189245232124661372048398409290270227000*I15*I06*I03^4 +
        76462592045046840669344429997706870237410562686018417442789635735855223221890620542505104330380882138292557868261480382443998368534323085580598240*J09*I06^2*I03^4 +
        27968096818241163942533505712219107278329007631766064376863025891306866292648682651008922006096877954894713044152091821949077519009946404611500*J18*I03^5 -
        10842524898461495603284956394014779430694623353373560088483997964123866768126590847618785927731625692470328625138518998485029916642040572830157*J09^2*I03^5 -
        8055407116436671681631631921076309898315117820273251467375173598113829671332759001581477101688492674598677603510971175928397667232610674646801*J09*I09*I03^5 +
        1750273401925004583448879671280952756210563397341087102841558023588762235657891279454525049800080177555546510517247417970223808669169428884602700*J12*I06*I03^5 +
        1685029326470193983580093324795142490691396966702478318618931879364356177286675193726511838713559826038471700768649670802407826955184335918741520*I12*I06*I03^5 -
        22464974573365566977945897436160204806549808687286807825051777498577838640293739108342286492517250410452323076047656719070162425859247790728325*J15*I03^6 -
        7867805154605784125138726293057537124225033553953690213718039894567428172785920928531382942185809170936099770502586448465988458407980507878025*I15*I03^6 +
        45177610519851841059758699760296042309048237307103997818756071255223795906641529387894821568024245088627967844494852006057206376886399330787440*J09*I06*I03^6 +
        1579463870412889241886648390800666237122730783657616151002053356934667096118356027958511100364062412012797670588138662521878454177152865124000*J12*I03^7 +
        1104955776662151511610623377215241016248786203495820085396944918076735900912972563929199625890331971059452585613285522500016214987208520890350*J09*I03^8 -
        1007410387374255090637729704386047460994968788575505288989780854116002600018998364223514454916476281409909524189777591725541533335090250275450*I09*I03^8 -
        46021311821759311881140975460835134757413519797052190516450001643431949643131391693993117964468431916166056193795105793246071575823611230673000*I06*I03^9,
        -3604845455640774014505055821095300929452992776844700903066258766719023108536782462564447614478894669765851232127308820475999784585720062970393600*J18*I15 +
        504212087076132818827514851031246132804182676741422929673820820265911106820883677095491586566656949319561618989731886739802222233238596219622400*I18*I15 -
        947724635278974133157716363239315073305696747431879183400097177965161420237923942988695205876598759383809120286819381403311871489840454467456000*J21*J12 +
        6320532553600464614177976333518911078635818585125047852243182934964695505512554971684657522889968943515694227413480955517476318191818615013888000*I21*J12 +
        696625178205814106992773664914781231867261220152573813384628635955685241387473795806131794976751583253339914927839994115133784529558510413036000*J21*I12 +
        3019701290469621191135722967906176560867666348600753616817461509072893599528412576420250558520220085384861502340656097523145936191630847612128000*I21*I12 +
        3827311110743611207921865144581322619673644933318305365396791987963435905222974802613931632190393711322525831351477797158119012518770245148249600*J12^2*J09 -
        6924618409886265353370750024260584683214830832413722579394049553846131711868936307695009602367642867068995265218422495162771735580174142196341200*J12*I12*J09 -
        7582185745413995318525952397433903884997519874322231292882681883899931181877444110632180656050320805853183411757514610993812603566523279634918400*J15*J09^2 -
        3156662939146032426235129222372665113373339319764984342666428011485203044037312165270901621841778743522782269848956123981717372498172291040563200*I15*J09^2 -
        207606045041726655594300575598509856793978729025545265785844168450782092539567255337067033871384946265799495399182348684646968631633740780147200*J12^2*I09 -
        679656551360563501678317789994946229970058869724499718777913753099530123658670835912159349606023833761444172865186176497493530951639602432408800*J12*I12*I09 +
        1912428629479696323967838035208732989149282185630938671286045746486504241356143631212167102152015404831233967654337564863635522884851951292604800*I12^2*I09 +
        3728135569264961383641034122436801383884930951827762018309424947988952441591924428371548792002819956012951742485521189614573471042008043438918400*J15*J09*I09 +
        3399111227805111013388801155120080513711511979944648444549399436332020600458384281334243463837870993368501272638835350220042210617965929777632000*I15*J09*I09 -
        642969760286533087801520290482767879245600637629830594068217079898114354336012580444995839233454926287961209555047158519993426222713493299788800*I15*I09^2 -
        307119936558996048705187154462976129802193046183718855953947030509514776915837665944323361073540899648358107002679129499950635764234467470472064000*J15*J12*I06 -
        19335497331828729737473422422731909542490374055125814726761340242934707429473132393429235211371972397450944651380940546537822166451903307500928000*I15*J12*I06 +
        1264095955804885164178737017822523682421676639166311667307253035494998507274191424898555829142674594791847448956395316912922428514209225561968630400*J15*I12*I06 +
        283042382566163395610060907088404591147535309747921870997945042402196324912478475043021791126445874393844164423937334604153414590855686842740268800*I15*I12*I06 -
        228035548061761427085846706038930717708729056651151180659098290663790117964600900846404965829892193087775209671099007328775731615418399977899648000*J18*J09*I06 +
        88804465596177713087827414873528812014248652381514083593962205948557647396472074924559475844686269845866705602625170570190858856788999843525708800*I18*J09*I06 +
        19676638595884276083550883530690157715929277868286106579586170676450820554609182869217409779774579333312098975713018266222620885467172723889062400*J09^3*I06 +
        207515517609524374412050769251268060598337383866098412169384163783872950835052514088228653309930688410308782838107264977841852263293126368814617600*J18*I09*I06 -
        35690735271951206309067366660810816870004989310165544874074353002758212517370160270674212131277020913241672292381483891354052101278899643556224000*I18*I09*I06 -
        40070911746467900900818213788250895829434944148306513526822470860520450759605010864972912088218854796357320263713031812416061264432991263815564800*J09*I09^2*I06 +
        6425588685033740727853914749661163690599104588963626848678335942379493959085999368949501555525230989224311104850501601865272315998084613796198400*I09^3*I06 +
        319251691389353691350919557529174230500740238872043452593156292812057302273451798572176328484533178698980204285209832589586700890543617614268416000*J21*I06^2 -
        11018126062002435385568448906998015273107952032729669342012360548510136364044590723493599294654488210530507218027700433465555503757485213931102208000*I21*I06^2 -
        3656677921600976143938720411714036530238764561476661020078474683022879041178997919999757911080127741301638203370834216357082785571467547111427481600*J12*J09*I06^2 +
        11224964830426410483562599848190748093600987465178651577113519759137064275938922741058273571394849591465688700236810375639540131027207673600315520000*I12*J09*I06^2 +
        6340264681785249338608605911300269438295843756882947199478597899327511763484998780273972460029230914439992217217123646555856002445898453791919411200*J12*I09*I06^2 -
        18450520827205502634084486531119657476423963387431969049364072142381780718423776189791243477216646286414363743212101271686160091032772006208095628800*I12*I09*I06^2 -
        363312462573438418808158800279783464806830435801265237233745470216418713266805200340461948034705074671113050575019500292290413718384104049514075136000*J15*I06^3 -
        139670307311839640912114715854047223061354182508280671173608311235763457646592038324562342528444537747370460037612928838023605817745772876765819904000*I15*I06^3 +
        566819322521552507612718643649552531476607280097896437907556716378979007364565151995138809492390163732116704321901065760351380384831189754331299840000*J09*I06^4 +
        37909056938674266317787889396286837712863126546616213339957922604411779592494729862889682660486036348526102012798452647623815514797642942501281792000*I09*I06^4 +
        220061073299231719053698857359465802122581079437129943889498025521990773040600502626383046902188117564609511806180714927731218475953129567225600*J15*I15*I03 -
        587313877388020550156824969808258572187540324533473139719454485576265356861699970698744447884135162043814467898521885320229922103324640858988800*I15^2*I03 -
        7407130872399428901049456862021954545731239404283845222103913312254053550879525562200052971431204242212607957275754866781927671187481383469276800*J18*J12*I03 +
        137018750675699342205778028902585885032701999334118725670530064571852995494573371565264387306277472403854760895638033859079719844332961828995200*I18*J12*I03 -
        5161561889126666743348810345953103975440521905744063141478195428140053475198793802194655910316818740523441155660130393861179728903825145558214000*J18*I12*I03 +
        1523347269803431935629958346612145867486779758664007349802761414269697066448605175921066042519658249520866742743205598652582825068490656866588000*I18*I12*I03 -
        2094686068679215515406076764443694094108953963160268385410271075002025821458168223237565837871166911877195192060550387367893756785349146649728000*I21*J09*I03 -
        716120129995644056204540952710670480416792751467796326394029315224798300708567088250583643922074410642197802592110949218702394330353845412329600*J12*J09^2*I03 -
        2437126137944969562423230026868776551776876068408786134759409982139892956222448102441010546266086986946728980364539837967502396970101764363009220*I12*J09^2*I03 +
        470627307783485062759287794303315695504905204013038530848023587687686929682743938060531536862166902387539320017336901143857073826290254466496000*J21*I09*I03 +
        2984922004381782591827220684971004280493377841057774595820165614362634512860248103739850642347215289402718007852377371200296530613685543893161220*I12*J09*I09*I03 -
        910651522175712091415998212814680449011515172730066240480274856719816419435159934354994949774662573090876508974017473059695763264966686105446400*J12*I09^2*I03 +
        296816207518824104214249900507603709596046376247149854506150730276926256782249593791691820095915243869064660080725881211066259619345483376094440*I12*I09^2*I03 +
        11510951730556289842700523894109659420676564918869940578932505678479241564066975269284270740109089741299914819178753081059853682633673149920064000*J12^2*I06*I03 -
        122744836760556473987897029390554661434237212957222282796389242459941950254646539906647377975771056998245393914389628980873596002765000416480631200*J12*I12*I06*I03 +
        979849063119861882877685430435746610207091710108012026753974223614860023855138501369320533619732796821434217844265894202624073672824537784046100800*I12^2*I06*I03 +
        183732073378567152804275254571900592967515900467014665641003915485164828386185965239992301317131587252639109510798475492488914367612824637017510400*J15*J09*I06*I03 -
        127856957070543520505497562223273945282976755756863502928480843321139662466472770975164764609222814694244282814344928287661634432039539024802803200*I15*J09*I06*I03 +
        52073385494233943455803394743919152156349376872627258365142428827482314047257437931050766303501231843533311398491159672038229018010810533273216000*I15*I09*I06*I03 +
        17909317856400585135919109420734287127229161529465864869910731331617057311279259488406475881214063884032034464044118320556015315403013974404633600000*J18*I06^2*I03 -
        4043579838215228842491118697212481202990329884198885213686600275902860546823637094629228708538196774682844190160349054247440522087164694900298752000*I18*I06^2*I03 -
        1084700754577320565539964240893427655931766983401439508538183304538707796330677957840634955814948651249768102474358428770490516050395912955244134400*J09*I09*I06^2*I03 -
        48135604431904659002920870411529940449732724879570960497786677561531595166041516001900766063642053634090447854068213700929687513668025699983718400*I09^2*I06^2*I03 +
        211106127330713881981188551128423924919509046970760030337799867258443033144763463103121411515378229841692210536843861907298911522910829722776291840000*J12*I06^3*I03 -
        380213537222578274525553656020311303540136564591691364697173333528919507649476180167523155661392685854058470735976179944985125275642056277608372172800*I12*I06^3*I03 -
        177134940797316406396660916627076945219329856064072799519546350901213660846405669906811103161343579241939054084537303951295592146226424791161206734848000*I06^5*I03 +
        8953774149708668258009639903048328164500912212479107561373259215558356155696493667128742780089007917397217304615168929357643383685828479873873600*J15*J12*I03^2 +
        964027344247334181545728694404440111069675392268557174450359828601616821993924528800100117472173262400644543145843957340538335175733724791195200*I15*J12*I03^2 +
        6874848480389074527761270518731444124364798563235627937894728120968339810429877803754917553221751116927999415850950611141884035288700168374182680*J15*I12*I03^2 -
        3405784483598776748993412049203360345979381194338930110561960086721360738825201349405529491874553968264659429108345566915611860170547313920289240*I15*I12*I03^2 +
        1870419146934771478884468909260005201820400394769447857240148530752546457732542407205003955577269087288477449294624046207850653731696363457785600*J18*J09*I03^2 +
        52708051777559757077879782509770398673279676407645950510501432622098489055842104296921104686566760226163192701867441423790243050662767906275200*I18*J09*I03^2 -
        752802486239591585967407321851772886512561985731271626239188177425532607904249847916113146642552024852623426076240479729568542456780965524630880*J09^3*I03^2 +
        196159895485564418674881019501008740903215973583434776820715721957954365064381357357607323492328501082536191396826954239147661492594783375452800*I18*I09*I03^2 +
        586533975503874943277452368836659054352897306686323140658711080611566560218460749991328809718855192198206589645568654487940149399106956307921120*J09*I09^2*I03^2 +
        13883190652934170324528260405389758546566021509210669387192872365896788019130071933406247346815133612942546883036746715595347166465943874355584000*J21*I06*I03^2 +
        251815160577254086266773181511450120060099779828415056656677660049085267420774107894826914952452897778412736300590444661330767932897587143546166160*I12*J09*I06*I03^2 -
        147512176149175648907057891415191898169592159342582251420986470316282226262094135311043848179886486267187385843268059563810457258329230586808665600*J12*I09*I06*I03^2 +
        108839188321996298456012183619019784023950422167818163723556454967399666636050063767405454882021657037385840899981455917275156210022078568779608080*I12*I09*I06*I03^2 +
        8273995421986098081750281244541108320743648178451961129522435968553731256855789166599394161243375670186362327307517957971127410710986878166657536000*I15*I06^2*I03^2 -
        277030345054798570307728558794435551455823082015186557857267392104518713654480220154996081753630199224156943467643283512413974524514242472855768166400*J09*I06^3*I03^2 -
        7085656817311544260885892033342682621314653575848992588382910288655449853067256624705862585328111839433308566795820619708839290072536114487098265600*I09*I06^3*I03^2 -
        512395967033794274567732235481677169215753195943879281120017159287665476352815060326471504916858410374823542051609096924349752461319418270624800*J12^2*I03^3 +
        2090914328570416971219549194875442723347197189013890493008401419730074616199869782437526699662046509311547756418435949750556065099153130479110470*J12*I12*I03^3 +
        2354934456727581638980984198034933124395699089882384122431753287873977123828010539444295915776251391095815506376566614830152491016775751719948020*I12^2*I03^3 -
        2886772954240520241311942708603622165581168749846702553640859897345081418813654083503801205195520952848269421380276146959193479213958231118405440*J15*J09*I03^3 -
        2837215936930427980212665859387566159676876557147377203026801597355861490056419844860923217496112454885803457726854736804050460181163297105063680*I15*J09*I03^3 -
        173078312391932719323543243745289660329434180126748337869347763871431527550637756582272050901943025833883536416459189559273253033594803658196800*I15*I09*I03^3 +
        55756353503857123582959809419951118008502565467528986809391707978914852415211918169820862093910374490045151457985582587185960172628252898438201600*J09*I09*I06*I03^3 -
        3364143703501068343791439828078613044110114370567544268076683788068336493003338606383758341826646272358145879728578335666495851095657387568532915200*J12*I06^2*I03^3 +
        6492498653886835182369398807360612725033922919223294261837040365187978958009301700698281378686503733535164234966819809438358021532699672755807642880*I12*I06^2*I03^3 +
        6486537336062150546925430497361634490066662262899119218055190312510433630667832252127247608730736131843771596604393990003987683332404833148200419328000*I06^4*I03^3 -
        21283270372374234963153637026491865155221974967388593873862535739336205512333061130772811085219093464662608728831160338221066818142451635140000*J21*I03^4 -
        93162763724585968828877535043440012671830875738867598902090507305101344355291333490203330050100531269763265146323374653857526088077635583392000*I21*I03^4 +
        552115525934666494144916070176169134614143078794613831568095582156200691496641138865207191287285195364573225109369542892900908900227657701409421*I12*J09*I03^4 +
        234716530801198125012119149682968503216547952242076386909742786966253662454148478494510405988429416882948067408439067892422513775738501587156080*J12*I09*I03^4 +
        87855540308657877355272842120470736906392366041029299927662430851776858316798979397843721387257592688793914991061638804490798052601543561753583*I12*I09*I03^4 +
        41051960892436673954582843025594798613825392596939040349010179248599801650833308839006708154419552640191539282823589635261148143385928033599628000*J15*I06*I03^4 +
        68096810842652095653195175375768702969756073015235486103966395976005896239383500455964290681479710970729321321800831027731704947926187006598492000*I15*I06*I03^4 +
        1385207221412012262276242436808919193190143097229435268418674975853037777190425313886930770948527461670579541470442984692604966260291191043694869760*J09*I06^2*I03^4 +
        131050804451081233235258066856714661123942755396630381919839557009988138577041416993951884338524080133078679533404849302587907208143795267126000*J18*I03^5 -
        216053918763476746205175326997476582433373723098685731074066717828818115872107663177985117893199984744836332285792160451563716456433897576977868*J09^2*I03^5 +
        66936526212883745289899721573321816493839784728271356075051126039834260073217663228343389438962547225648693494806511638508206279738039623255476*J09*I09*I03^5 -
        508386601141595417350472950839995023907691799537119245447794686951320165950685231570623231067242415875171378912345790854714099100515654589125200*J12*I06*I03^5 +
        3819811482899891971078669222331016927017680852199027622748942556138380455222486382438233654885514708443073944572983513167273224816447532341937480*I12*I06*I03^5 -
        129506266533495391428312217993170830609304412180245675191833197649741567049908426977926938137796194678173410528439984637267250789490242350567300*J15*I03^6 -
        11372767793194509468926743295960425225541506835568809179592686895906457121256565938562908141902769388245209386538720529137097668250820400070100*I15*I03^6 +
        7356383284727084323766835136432925048870193817000227082148475759388066406281603410528576624210046114886070181655324292175065435299002915451650560*J09*I06*I03^6 +
        16051169063621430929489571791765537039159567008166799071961349785751881568651696243762695498903239520843804929296400183348129245421090097936000*J12*I03^7 -
        9624414726373288882193411872445119321937605841736442429100594573188089338683343599049048778282670439074374326200297412752737312827402703126600*J09*I03^8 -
        3817543653738815155347460751002328530321393810477681300108518248231270513922556873916817840035677281789195048277134199095644497210584743725800*I09*I03^8 +
        241609405558397476183814047080220371357857888976691336788804713079580036950706135796460729409086816237229117726956533447044369366280020878748000*I06*I03^9,
        -76795866083756196195977628482192093604161430784581151908289605947449668221749697506678464644278798496527755387038494435421594596599302400230400*J18*I15 +
        21310987901379894186177618842487851628752241779376860636225967993609188122633016368639006300326857135143929324221666676998219746659556124697600*I18*I15 -
        46271702510535977185094442141111297246283175112003755241994637068139394142383367412579806313201825051973644240545907791216783044255689956608000*J21*J12 +
        302320128536635297516570581692853720170751494084270956602995190498997084115429721423752561050493242980777564874719286526372321939383885914624000*I21*J12 +
        20116672789477149336343894032889025770584537260996269562946793037350772843192737391847631770249904589784977058082779254315596817874405032556000*J21*I12 +
        125735069226410678048280646975347004079342256185312666753434559334180634085806835804769914905547819716265451166065393888468871657625599493856000*I21*I12 +
        201475126479834825764209954497227933841773528984555298216875511902307111344704982870253654523301491887596567424247038906117402022877140161676800*J12^2*J09 -
        358627578886839464674723510398353255824586049111908914913800214783962166432669165050562579019910870835761893264701439818251714548428972420821200*J12*I12*J09 -
        31465299866073039732683351448850170254089158392986610508056360854911180002848286449652218842034399117441617882606170097673244316627157833369600*J15*J09^2 -
        163285521116283498767550333467249507664557089643610212046100143396275115340453577223166662039937863266237060213499118584873927292897953015705600*I15*J09^2 -
        11827187705170963983127381176163762436464026092923896137596358906123418646185469801612103206489063553595446196235984933488209279006576640537600*J12^2*I09 -
        35208011913425302559690148938614597164558143405327925085067497001946369953683212692505759039987299250463142691719549594923786628655482361516000*J12*I12*I09 +
        103864042200193394806013437133167530330791166394368781288172057562532680066539343842832473359135319837527644744566853950454146721412450426953600*I12^2*I09 +
        48013541520245717512743016547140143566959682420498316995259038789934289703818403832742409945801947060972326796140957230770940828855910887923200*J15*J09*I09 +
        158294356332894688712074518094742439251230301437881648741716251217694325919424736294049607619132268398493254125814969774694899810739471813260800*I15*J09*I09 -
        31334380040787668837381198163750929740680414122950054761799077833740688072804654839423257996793514530156743647320892003195546096701792730419200*I15*I09^2 -
        8100883969232335515845060696522706714619420375107056459843827916222931396420359483682107169411728682050439311525597772800775287663476045764864000*J15*J12*I06 -
        750322654497609567060222953384130295151312547914955088786521660733976758470771219260432476657304822429493020557759899059603189530645400198400000*I15*J12*I06 +
        29206163918847694436819965059356526108484818243541954008183619373747774008590964331010368308564890325331702093605696254295489903308325591842028800*J15*I12*I06 +
        11716333826451270819932782670099663611681663430714401965551280899191251306590121276253031929216272251198008602514483302803737119018534385273353600*I15*I12*I06 -
        16653377751045836298977414190306570809818073527578322309235781826341768420161863620873054225860815600248275975685250678026380665635833195257881600*J18*J09*I06 +
        3522927854196422742211134670682387966387328307615772381715456867208587258355281951848145685301210529077026420495830566382987218788718773932672000*I18*J09*I06 +
        1623863170534893821972597112226981881053144746589119174274612032848083260394449269942037281941026774077956940946270911506668268312183639469926400*J09^3*I06 +
        6142473245689047437513405015179893873089885903868854031785070228351734698485538539648877831458334365036767391488396714917613430610199252430796800*J18*I09*I06 -
        1534451832040815763111814458156446156675054733955823884625575262842853355127376997412182394150083802224284226954476334057457846297549703326054400*I18*I09*I06 -
        1479188645902901290323066124247328356643986509155352809946084960029007124189950030194886271861892579059354680896194286601881023570106876741734400*J09*I09^2*I06 +
        283378041767665246866431448156965283661674112335078675436550133902023426461025681074433146551453251162567422115267053288829122723769532090265600*I09^3*I06 +
        42731988921915336445597716102828529976250708126667521168069359705708854092936332558183407848245464937439749276914586567043687786519866888767488000*J21*I06^2 -
        29982052123505346701938468160779481927752739036824740000496810420136315699476410988917126192722428113471270469529098343980405083992931408052224000*I21*I06^2 -
        275425026654489741004700339882625063739287597988482733261630486993013690214044845654887414903523857231687182962900375635985983896870245157033164800*J12*J09*I06^2 +
        705761893954163588355364122231307049953807368553909200371386056521818661789032183052239505487205309561770290872012347454340901285882962643988454400*I12*J09*I06^2 +
        246674064503070340059655418696767169533414144135768307846827698514248243669212841629320572551182455001186211642403435495391560414949307151986073600*J12*I09*I06^2 -
        481604955568967155198822891582814113948933362039124783649357948510945656225215416245704453029273342639656771842578752526309823332435016797674982400*I12*I09*I06^2 +
        25314830833841759290244715647126403072319839131723755174900456275042659664760911084246748865591939196841786968532400633768863709467951455336499200000*J15*I06^3 -
        8286992865340589043219160424131161052984998074978828226283226212701362210947906875332931374884096630550142982273361080214811463770076620486432768000*I15*I06^3 +
        69208744478045563030516146006384154354614772222522167156654999364487637305790067168504661970869475111495687247113488762662665923701165527530090496000*J09*I06^4 -
        425631327694610812247320883185735370560185744292634631050372874715134157105966294662367625132797269740549302168094306970072403084465513034713890816000*I09*I06^4 +
        183477740144113112609501719156256541405810002873431395401145955387838419125620284299435950017497207511619896274062933823102764352034923873971200*J15*I15*I03 -
        3336664902206229270433419440021219143601698564661009999236333026342490959198708248740666731564682959537622162039537334725435641206029369881600*I15^2*I03 -
        162882947743449859435204827594522473805783698520769015029260127635544818288848669184056713463998821777950114160147155022977249847981133482630400*J18*J12*I03 -
        1471474534460057518543253779308566955268340110839087217613613416077636533521724242891004503430281403602083605758064388585275820922320196294400*I18*J12*I03 -
        352819698801533927668485335964950573202697480682188485230117488393103210896603932448135091092900788067141967268258789513243034263994339719198000*J18*I12*I03 +
        61026383528667501755124418430604057068066358643887336764457204436989109779610973662287273468159201088188296592859628939529938896990170457908000*I18*I12*I03 +
        100643445026053850805140484657497084094409081168506216770586452052733561106669042621153200147648799882787816964541444861794457545073800455168000*I21*J09*I03 -
        123731476859043011530485143002067745242765226993487035315547310147927132128609734739865302652939271850299948629482242673780517937989062600761600*J12*J09^2*I03 +
        40202556214183605287095341038925294035663244367144051874732215839278205514889893428088193818752841675104223015499850190820880954446774313653820*I12*J09^2*I03 +
        10959229221221604747561180169409823499680028619673138204574525193298103246033875611908482768685054529096661010252807109411761305082491052032000*J21*I09*I03 +
        71169389649497365364739966781322594339804734112296294227792673645787279661694535051668528672619256001888937923542361817023151374874695615508100*I12*J09*I09*I03 -
        13420180490666780614262049539327909480449922405425776800649324936508560240203623794224756201627214598937818086751909252106249760974826256396800*J12*I09^2*I03 -
        8619073872967738299334769190410383080919207534797480943747661114193721780275646579569929001197044819176459165471381294886860833872891259965080*I12*I09^2*I03 -
        833441248304976368881112418853486096858134631816310777636612320550528781536470802957084297460712161247011374076205859787110837972873441333376000*J12^2*I06*I03 -
        2024586531569300539470759914820889018759342724100793507959375844407149538312789148947818783524196125758178400649298190812433426265878394727720800*J12*I12*I06*I03 +
        34498970560935819897882597588602207153033537003089287401846979287478190893938123272185333167533486992664712617047090923408919346692233732335723200*I12^2*I06*I03 +
        14906478580307248467476143789312505789899745217618008314777411089081555792611823925645603479989296845544125671866796441478504515912048606602406400*J15*J09*I06*I03 -
        1584015410702014179156954655915538995805729473249566655766112424078346568938470894312463228004245449954226888418787467692183019876590343876748800*I15*J09*I06*I03 -
        1973595420605687522464802850909493242978276693275399641548979679327175525970781709185284057567281528415464630035081098502109809536047525442252800*I15*I09*I06*I03 +
        398926086430595589180808540433913081733984604336435356901172428390594131718337782814367863637457983342449489674614465448574226405961245454877696000*J18*I06^2*I03 -
        97858203580239322989514955509314664242054373985528170386208620122221503446444446647827145322025160831323618996764734779388862558743300756578304000*I18*I06^2*I03 -
        100462414826306563647661672557725526794318333639945395356516590936258562460033856054202360308422302802911246753104145042997434797467952494520678400*J09*I09*I06^2*I03 -
        2129030043729839824085828002108793004111997306940659088409321753828237196539382064961192741145058297286238221556208905864385680762141896741888000*I09^2*I06^2*I03 -
        2783020871005569405851179948768313991603527455783391238672855006900371743794068852249857100941591860780093301799879144290833831287292796050951168000*J12*I06^3*I03 +
        19414249315413269223664185136785253362840559513475577496935544987829020887055839255301584456684758843529406710723687576729026161804399466246887372800*I12*I06^3*I03 +
        2658017759371681441220140510758344343528654328084485949940475821516349306280590212530031513348945872589274338036680348900363082554625206732935659520000*I06^5*I03 +
        223414954250043675136832305095335019453361493955142183337274436075685950020991987255972754852287205033595102967459384184263887926017708273065600*J15*J12*I03^2 -
        4018755121885346466003083368220213630518526503772024996248776190007343680808472578283983494052924765029784731970456056695184814491251797244800*I15*J12*I03^2 +
        366652849131611474080751647605041515540475071292052551475645722270489510738840788689422416635997023900262889679590391201073781946931240607257920*J15*I12*I03^2 -
        48071999567615321894040189753911928985289160680215364715317742582274459061429602882528317697781093269705775480063696034275847116641614789928560*I15*I12*I03^2 +
        56117404327388194837390575153388532741266890217771595428033926462480599073859720779028161114933310966120551732732757960359148250779064633553600*J18*J09*I03^2 +
        1486824063796570926580998573672172113556834996880992294940307222311766555523403790690771787873622644064149315774239835715544326370655450785600*I18*J09*I03^2 -
        874545568398279194766476328565042860425888592245176281485484298801982882826371216440693643177037581738520831085480758509012577100067637217920*J09^3*I03^2 +
        6578858969961159105231361325771844001981830377335633838901127891895599236327126678166066504262276616020288187452509427256200808480637096030080*J09*I09^2*I03^2 +
        123284860742563105248266701229759640241973965748782926388920618415355020770917056175607549834399912943586262483212594419000577910772018983936000*J21*I06*I03^2 +
        915412845599300620482778091004707457548341210056028958496673369137120370300446334335500842964199671718502226518525786449355753632108989085446400*J12*J09*I06*I03^2 +
        4597405977236880114768788650639821260374488478884034812260044521746928179624020102068260529391473272476899359864914155905291333041469664196982640*I12*J09*I06*I03^2 -
        2010585360453281978183687081777884775421510763553183615801503495151982975203218851270948164081761948666857391698386912686569070467119193228595200*J12*I09*I06*I03^2 +
        174287459239421505615448755883902034354429169606452566469631742995279147491510299230859714551535229069600467873872098960171750319262314087587920*I12*I09*I06*I03^2 +
        4267109621422907452454654376601234512344040206658378212567395971261782351867509954549720551220547100162931412837312403861531145038887920352256000*I15*I06^2*I03^2 +
        1911158125253773415218612312472816851019685376507542073130134471795105876686199724075774513000805913427947256821043027814568585767954805890848256000*J09*I06^3*I03^2 -
        842340656035802603090983764161696761805555123713123894640809963942221570446589521996978341372376860626427905910512249949577541176890538042323353600*I09*I06^3*I03^2 -
        12003687675276127596865717379047365175923388211980144569726932432532394445677833638754306073443711299807850427710420640373809098144275449387200*J12^2*I03^3 +
        37782488357649921459760737447749733365652557553271587460990695196662122474180520209290751877292120961442805183279949400709678180650116557265130*J12*I12*I03^3 +
        132596079243302153152246836441659519221511056065717540372142878512812135596989719212580727599976015797706264070269993059393456927233704433389580*I12^2*I03^3 -
        60677023501904242134902601849083259914581949458108314972524225664105758219003132383203820963201447301173576748765415768564986827099401632232960*J15*J09*I03^3 -
        36339694562974129990259629836161242352791050025807328810855265302701346618806620779017980592637795423337643232534943957539906084286282168702720*I15*J09*I03^3 +
        1844078001782174656707610329248178764498385690978250935512849230699210280272008113838521266145145084507015036727243353411423414163214261664000*I15*I09*I03^3 +
        871990397675137427570454287906448138340705915242499016044735324304776072506060418936836575358345274241798877029469876838510389873858861874502400*J09*I09*I06*I03^3 -
        20134386617553368295348768930811125086709215965971487245152646532340180037372225707642665199636259557212217564062379108023180147457961074778700800*J12*I06^2*I03^3 +
        275014808223994728178737934099895375509459123869754423126475780002374303437349151919219438742716501221439014413598428873801812529555754168644683520*I12*I06^2*I03^3 +
        48156879606849285666398085062168734868333506844605819745354817994616839257417147996223418033585285351318719746203594059640256143702630195710525440000*I06^4*I03^3 -
        3263079497033328070127474159936379417082853573009934074704522219242679548884889047475959268186700698312658243273912966747189868432070061560000*J21*I03^4 +
        27765318227786509076986872810033091204260662472538392021367266187854865376918806994668488491198165235607987985725085917001757410337818672640000*I21*I03^4 -
        14159332086986100474897970664135526740629668208482975288544315404372828308896947485021936245174168442808089101802966243689931975611416507306141*I12*J09*I03^4 +
        6610878138143289482784334786663867324363740483016230496028852702949653450213335680463628422055550469511676204100890859263986543137293672474720*J12*I09*I03^4 +
        6505447315894756290646156649666089313483505774124008034525338745897245205816885636410340240928239582554538315467559678932379137192991776322257*I12*I09*I03^4 +
        164246655983446876025883157655121734819264494321852383042008948751778561415132321415629144085769082708746730735194961089100202037470262935278400*J15*I06*I03^4 +
        101725755965394269801909600977707698817868593888137693454974561131317281519483124527103000850420459495453495816318571614431003489128832924532800*I15*I06*I03^4 +
        25677626721413069618701579740188118727734492473738359365616382314288228460597653472250114876076597587265756704098595211188085039191397298135763840*J09*I06^2*I03^4 +
        6041321790197804899861529219941762923910776885370404740310741245761318233556498966359309063100219449922509028635954885282756874506303212388000*J18*I03^5 -
        4266601840407368975880077564903382276516706583212402282156468578408080303542671284998765332520296209399088877819239287093614457103641984151912*J09^2*I03^5 -
        937557591891827700371651593134732816318718958072609585685802345377874656710991486655993746286344332896233952641192545896919186514236023247016*J09*I09*I03^5 +
        314193992304839637032565248347462723954410613948560659921421155895231885708605700260382311021438336824070895929667875577567702877981639470631200*J12*I06*I03^5 +
        436583725327679611472407037148410899310512312193657129905677139483653187680911348368684033356127888253681377831444569818227275941596419093868920*I12*I06*I03^5 -
        4619490132840662601415143988688738180407373116400788612420383050887335138135776673942060519432703180862574837290101539414319352840692022717400*J15*I03^6 -
        496705114661402865839153272320350970240905323142886218023941235118823690803890733957199679577209161508811385292464863631715641293430033103800*I15*I03^6 +
        123594274966615396466000158181967192464428517660252550479372123554957393669782813723649566194023827621953519986811263595174256664461177267047040*J09*I06*I03^6 +
        292562271315834779184355308245197363978956278454729030503707993847831444429643737208784852664668629011308246081267932694538868437633815968000*J12*I03^7 +
        166633380838529747158231143332909961017592452506687406419757200302374658013951276020887633164426814965891766624835732316765891557913779061200*J09*I03^8 -
        97767671533627881121316016558254597090340255522056320388610282377907573412896866070844058747665757269225013786485902178323025882926882236400*I09*I03^8 -
        4318072923239923574577501326564021441218153458554239463703543843485637150079075643880941448165237094580633103070282124595677546658336347672000*I06*I03^9,
        328959955876453265477562619404053910882547357638814586220337825476046472019673423405213469502830192828167082710593427509404279403819335062809600*J18*I15 -
        115297581518960827191500331939207794329601669651313489010515686865586560622101693423413883300648537575598436947423969674126449363333592475110400*I18*I15 +
        285265404870718655828713542516716957547065079579398884416638876587574342559508403244139222724469388771374191950271250781280837833231592566560000*J21*J12 -
        1748615169576955852459040627048928383516012207955889665171434333358094195412235835970288756376976637726790581401971552609317332731902870588160000*I21*J12 -
        132326086780313796697180693921336031637089824868213730899337288625014260549450459970673409084667999604422872263759738548528132180557041285308000*J21*I12 -
        750034779833387269371603003660067887189863492666610021567660509465471774546118182158481794417616160573987142241406901369356725017653300297312000*I21*I12 -
        1073350219341927006512883338132771347062413903013123622533663399168552844603552082248467804370186125865766099550926770863117448767203569032048000*J12^2*J09 +
        1939400978549806577190372986449727446614316683267591183979707157778696264915595732183492131631756674235172814389831690526645061084668397742707600*J12*I12*J09 +
        7644657156303500446741607310245814570823890681085979174373776854283192107209905471947798881496421039717059537654585467288395681873037523171200*J15*J09^2 +
        778466750968856617333813507569809294131178873322964046586582922327042073204959851041252595964418076268422750175736190084051500701534113842428800*I15*J09^2 -
        17249178929180631985332751077231327015743162072179459523311428627011944479280727860170460132156088363883338860467800756487575708789352776544000*J12^2*I09 +
        277722663890451460476685493920694954777763941583884141339816496743347296568146692091921616804028022564596840662097849601318398993366310758306400*J12*I12*I09 -
        522660908306063708996132502650618108827340832807028548788707205406191796888523242856391432892353012046685490161327767824954035917985653429254400*I12^2*I09 -
        73641733910852282643015667199366550179076345759247132582671090198145067220835444523907549554106446672340781959799814734149016342513526003136000*J15*J09*I09 -
        724131105207659849209789376108234443234504272469632819715573620025320870134718107956720271955237593961753818462022609234513528518547573580070400*I15*J09*I09 +
        137336413006150226483844483893497483571980347296717996267373140975359770267589252108937311589035822624863323293940381823376554580777738360627200*I15*I09^2 +
        65625296753415100846356416628456736315223212722365682879640612975628893261569028933540831326101895219036030068412340587648152610806630104499136000*J15*J12*I06 +
        8754403908941869461580243729184188371658884096132858698366348157415847441454820730180200961996130122936134986555262393574213925949117670951232000*I15*J12*I06 -
        156929016517927748428973686503080967953811201386449296635572695480722088793406790329051836449484156546442517311101382564772043094203211259356620800*J15*I12*I06 -
        58205067456509102815558625298662995378963172031815414722424046038988185733528408468480129032584550244986540503072053064283917615373312716539561600*I15*I12*I06 +
        83915383330562008512111956879382796772186762652625509524613480279610519982521365034339100785327018839247475134236481622722936598071055627706336000*J18*J09*I06 -
        14311946250533427741636261980465915154595269708753105153314796760010074665308896463817581360745539713214366717148247465047528808315116207571987200*I18*J09*I06 -
        8243379713521681134684278038508945276139264323466108910110439622300499880944402340135517804924808699147439407036741852072063406438881678489331200*J09^3*I06 -
        15323518033403727346848562846624756907962394874560283056512717985932020784475597376322508939030412705476391101777687908540114776914740718861721600*J18*I09*I06 +
        3414344754295599500543234864330577605460546284654312290113315687498575740604801156184908834541679687393814664090142029909723215586145483199692800*I18*I09*I06 +
        861138104910153608459073877441783017893003085512723693464694792338296288070010855138894026215310482121348427360432804202759831211153540975411200*J09*I09^2*I06 +
        651901450982133910891421702840372410676173954974841888617935508095063880060042815527202528992289642430265441593300552334974661336428937741363200*I09^3*I06 -
        213848099509604478178167008239005054719283439283770538206693773311226521399174728208926822772816287552577832058051275508151073434780913419105280000*J21*I06^2 +
        762251912515793055272788244212036459160095958844697515849685159271071638797919209305463028220962637832797941713089916026729156146006060277985280000*I21*I06^2 +
        1497932121027431277226474432319459212392374103089611855990607033023740827280187897973186743281773457754593365337421698403723572764642148509863680000*J12*J09*I06^2 -
        3831302713547953699469806353695901695083854642028781961418076269277619192169564686498412795328346268637565959498953884030686424443926247803639603200*I12*J09*I06^2 -
        1427682972684941575637808882272926565683894943892107139549205160398225025691686512907242410845467114457429665763212841523479695504934955326607360000*J12*I09*I06^2 +
        1913318174285851220845765110622404562838012046827800505444474956210325583727511081678969230394095008001559242219106246709561411224706417477107788800*I12*I09*I06^2 -
        120051151052661539482208184588407874599189321797427790445478841153906142040330302462676794716712256845392546332065449542425167972514253779876729344000*J15*I06^3 +
        22373166190368809838747617934909240910437513533127505963463048686954685379388571803519477741826832628732079371370090816138065852876574008036609536000*I15*I06^3 -
        257044485686756122717274772984974808633724080916161101376515572982111632752676169720237370053403686477188019806047321217964036702964516967577094144000*J09*I06^4 +
        1813996570202242916983193388480990619456967439467232952914856536895663909812530595148051845018826868223010693522450470865919573544361236719106699264000*I09*I06^4 -
        1263462834959290678043537721752193143501597969355755102076214319722462772616290017315325713622411177692815172932562807117995411922951286069990400*J15*I15*I03 +
        63217054484676602306695391696245798434383568529744475332129284837273684072087454806360157358605498575282184656117505570483842089038460108467200*I15^2*I03 -
        1061191636719637705333316219033725894185182289680535795218507303305938122961302440347497166895460758121933874509024353744861452412248864519859200*J18*J12*I03 +
        188002459385629618414897874732915737742443561496982148930280027124138401115029356018701850719338412048058485407254333927662975924697849356892800*I18*J12*I03 +
        3439109823530168602282234228154804449520417356289942519776888477709909749282617688887592755293397841840270761834470388950380933592901284353527600*J18*I12*I03 -
        441311133969000775793689862283711364015825303196591998229692624131206682017382064515998608009347748169195358506328937245632467316498350683842400*I18*I12*I03 -
        313238269051344193309346970866336607125305167058369214077984564286548035097329629973356008285696167146389021786408676095553910268849341167232000*I21*J09*I03 +
        582751881931889563485328564375042385168301197988419047138706075722061982337598731432106911996617917444444548218915662593888105558527154946575200*J12*J09^2*I03 -
        190477030274020940670608347248795552483215355202514073784605463495483621548012222701852009598827852567857067465877077690385196885466133312731340*I12*J09^2*I03 -
        19226477394224920686034939101438400294385456049163744941384534874334567811770434888160340442419481715629463114826339925925097220373011118976000*J21*I09*I03 +
        343279817099737732681041784126765296580627953771010859436252513426420138862667375375812816111574876894438334944447169918508407612040870907042400*J12*J09*I09*I03 -
        529622579594501548177428603440467314671661196952684630985904182715090005962068219092588145453124271982290470925244383837355724008867762265811060*I12*J09*I09*I03 -
        43203054753756071086762144880978223486476658033345614285150036133806419365741264444633048150718145987292983701398885437088229785125985208833600*J12*I09^2*I03 +
        118938436798981575041012351886389227414562814862205653464843027241953328566958188120813502480599209879680182476789424668059839059696713963105080*I12*I09^2*I03 -
        13275376232344105650536180786495655331332464045808484152308015379719244467432104657803544279399800080687057414467608024230992928469425651075136000*J12^2*I06*I03 +
        141542525694361434126645500836735089492102589187626692546550587188938627066299825718178399457102874104765601804702168729097893373913013736600700000*J12*I12*I06*I03 -
        281577454798887521098237120829236668878808026210777591037276003554951719533371044501319868644257288130363353081407838939683816932290409676637656000*I12^2*I06*I03 -
        71660147782929346213853446122517362593795211355051427898519617991862873472614447924079982761823583707186620874617330768718114522984844734877708800*J15*J09*I06*I03 +
        1888008215531852652618827508433037235130531657424394107072531732661658298343612610576884658930706131166414436250722146087054112818495816340672000*I15*J09*I06*I03 +
        17402910302453556673623273411775720838069940889615435982874502218839228912849441230706804216503562792786357721899248898265885821088861148435660800*I15*I09*I06*I03 -
        1227639052446592310247072494854686219647729806808520746326341632049573310675587816683852145438768419408319471641745163440742889372119082001572044800*J18*I06^2*I03 +
        255514044116284884419097352214346628839917892434032177735006825852029213609157624009682786609509153498424629653835438991918818738547263358752051200*I18*I06^2*I03 +
        52758225848348894532741921233184055430826395312956250434078833063977489016690935169723226592137077929432773780213057781454668053431012215971814400*J09*I09*I06^2*I03 +
        211937853856827204631739831023419054073369680402161861670289110288098743767526407091921059868014756912313205303777026283606425246645171233492403200*I09^2*I06^2*I03 +
        12726458969884399149777369737347559229604892333589271420387757606371700534931061360125390447197960586952687715436027196463715465572602402289806080000*J12*I06^3*I03 -
        104676604747355287894652816657518763320432326478545636723562915444112456144129558818967135740108211813785918365763587161577461094268298075575137024000*I12*I06^3*I03 -
        17460053181988238380176621183795719799447896894343753031043430829425790334985585675970314562599718871847166098143566798655223732875482653291273388032000*I06^5*I03 +
        965934119468441295157068876647550821126706957620554300339100239265279026231197538786421592261396706439071888210791248298359438189141872983050400*J15*J12*I03^2 -
        255314922889082731686490586897142582860364886836640605313369425713237982662250061726659947450128003394706638507284698461984671340921683952728800*I15*J12*I03^2 -
        3588083977337067896579087086918086838853764333980455282272174896789763688091587093324800044296626235351790487639653744912647110934012957047298640*J15*I12*I03^2 +
        333774313900121097310776279758527437467748532277944235055577588501394680376667230511331582411977650283890296430966084991378946866724065765445920*I15*I12*I03^2 -
        141543284544087183526286021941727221788838625038722834141417169661779002005951596379744354509632568798414293435358443348503493348546632017554000*J18*J09*I03^2 -
        10075867106677780686081159162905884719963678198377117418126685544985077989791354391253785342446225303660825788180539399756029813764501164158000*I18*J09*I03^2 -
        21736496132246253109626537822447977901522206435860974412495568573584392377398088778061844613949640497892134840168271275525776550407016813761600*J09^3*I03^2 -
        9947262430153386931164725100684313759927400613436615218956864552345907602960240855952437279966579442755798572178692098624258084332541220809600*J09*I09^2*I03^2 +
        101520328993577012868011143302065331602298271821469337214238772409787539658000812880109728966661420992217133970916805674449076441194103165952000*J21*I06*I03^2 -
        21821935381387307418222924007775592113421608413203434300565029484847512324747753256419397143606720134917565007894873863336042065922299699444754160*I12*J09*I06*I03^2 -
        8437940090375752932803841676043855444381775941915619329736842829300061069466983469465789313767859971171637265163730693068763963331869583532572800*J12*I09*I06*I03^2 +
        11066756749350380959039623823139737506962452460669846535564995383079730187811772327787098883039105311941412525577794026760098232585284845781575920*I12*I09*I06*I03^2 -
        94544207023092380972799987406254756870174216781141404485856714580121329582129267842655116188682017443198692567835430339549813009360876835633254400*I15*I06^2*I03^2 -
        18834348920800195762724856116512911388969121471459209767469005680409035030446679316825875618222379392195384457624420115016964386948856589157417472000*J09*I06^3*I03^2 +
        14902682229094360260530566752434615345975038958255877019806237580759658440389149969212712840994118250390963690345517429723548087614322757722587084800*I09*I06^3*I03^2 -
        48671846123204576223565244612543474934102394439428438062542889286110338754419006135028890338421388171392260609814262010636972660181302869134400*J12^2*I03^3 +
        652714645003380953385772557564262328012086679020703512453110765221631400321240943923070659642796834489406860698474889209449701254175011715691990*J12*I12*I03^3 -
        1345964679028403988971069159518982061208309280727599076436463015498455300460210898922356552964421955082431422249919481895407883402344398091732860*I12^2*I03^3 +
        149658502278360543742854671284432347712403174030949679311069054122289826811317569136613166306766230378023727481795677139812404049204000839354880*J15*J09*I03^3 +
        58482226341252460522796914891650755233854874105578158199738424477077494125318060964520671374264806824235754916013204301700985273648836363028480*I15*J09*I03^3 -
        57342413508554435858991064185313056590339862276815398898779497897013662138753160976017554961108739904473585356408438194315445167700482217386240*I15*I09*I03^3 -
        903206539233040487934238783681226460158278644601000039437891687978285223516707684408197953025765544269531334938711520222705244371793518179654400*J09*I09*I06*I03^3 +
        61835051393223849200924580725591106134964944194415296358225730825833457595802279616972480909053914275631673960317006451974829049335329532991014400*J12*I06^2*I03^3 -
        1286721848728077972036474906636569668730838572557527752230222524393782734618025859660328885380084667292195527429746743640007459681714313619628074240*I12*I06^2*I03^3 +
        119329694927656224773326589596087877438659109122846257416364292074510182972805945656907443586801054500019631748617802904884633415782997697792180224000*I06^4*I03^3 +
        5165332439516454880524092484301459977442247624031281264646102413719998047591053393967095580730507054927195589146572730927733429462573828914000*J21*I03^4 -
        40731924006736158450684193002703492076132706800431271695700887232739248570796740110400823037645797807892008687252801002305302236114543282496000*I21*I03^4 +
        81405926719228720087652487449087305073388743689039273517064646804732357401788548756607102529370695698067318741338852054147918595975627551600337*I12*J09*I03^4 +
        20164003003476847590808931010719700047281271567440963103171945279165084937550962422563759643018142836180966540147280356921541070166138217101640*J12*I09*I03^4 -
        78124200220463944138681912196391448824555182140563063136476781721407831645918616382433725852213266984930885256740725811074922032577348526303069*I12*I09*I03^4 -
        928152604979790366069467668408935733228471721574805152695267143669918775238288880020456873828250054526125526671829328966360158282128082658733200*J15*I06*I03^4 -
        958909379594212258621289920927147889040995900310938431562197375938792645748505451406726211190453202957370596238088966226243764149711381337598800*I15*I06*I03^4 -
        50771159478419274628879319182857616157618650042034947585345476964244630543572804422455623091282619692818021526077527693741812916113000797473385920*J09*I06^2*I03^4 -
        13941456334335401068526284388044441547761341181455388472792385574415340570824275422795073874735407241184442680218973162002854409038786667007000*J18*I03^5 -
        12467910992763311021911667322062850051119360919077264683942892046886895290847224565325614719384064066910311558106927751354045030635112770397794*J09^2*I03^5 +
        4525655709572965259668397285068477903541969760217923059945780225248069286978061200337435697238179921400011439948178617893475861002657465123758*J09*I09*I03^5 -
        296749603777053276652886731578036838194585356834553123653129831018913150484275447829089974045202004228804619502095181139899881580407785812984600*J12*I06*I03^5 -
        3500699079178293987817727889116062700163612830693090960248205855242028272058132223560728191574068415428698220726275716947014601669603987896495640*I12*I06*I03^5 +
        13907839442789478360215804390703644633339802046296453100872531166782772109045443803054944444994171388349009532331125612164742004069506943090650*J15*I03^6 +
        1409198234209856188902896480547124720259807603785369628812974236543310146262051247462425014136540176922522621819011391149773466756013430102050*I15*I03^6 +
        185858025911952063269356333632295050209727308999949774553498733497357393894177104020480849808533786664063273672084538181899341710365581913068480*J09*I06*I03^6 -
        819532929008367594330758867632055832530639332360255706455417630684926749354707289882881237292006529374985784664324979376128697660465860744000*J12*I03^7 -
        1392241988683882962510673739174416107542094840808825179227845667891978769353654990091148907696097724418435328195934616747084233253891895699900*J09*I03^8 +
        310232801688213372682948258613325982136941623833614673498475367735682730748949909117365230464151491544409845978739969975304380058884156305300*I09*I03^8 +
        27419332044915418624364025298792905044804002101939135123780205523605922819095889773475112544947759706300621812695809111228470500708843232818000*I06*I03^9,
        8994402592515559118108243492318365404482298021656619252473396878597489932640261927379753001770910873046308375814030116310078548637016392122577525312151582523345306211968654581596028357599\
        38877495142925543790160040000*J21*I15 - 37541448157805797947759987518698561233081083927252310335919482766287724865472318331461842319927004492808837212600200159737826042392443087035342\
        359757563911588660845471255636715859970593435481004969719921558703529920000*I21*I15 + 2594178081098848443533991574884053616954511193198179566325384757599319018160406551183147058557796\
        156435470225959097538715423314864047771852628950848306424120604259078912966390322267115280029251356628328431446678784000*J12^2*I12 +
        500081882496012942991670198613625911078798594517039845061411461453560985920030206129316013279331907190071118378176413822549262946658341504050978494465214415460313207784286244603551294\
        48135529485969311285842086715904000*J12*I12^2 - 808491830568743504467020108355330072999674393622518807834438349226326156788654456595594828736548274304904757651344315354920919004428587\
        12276061913578471616590406564095197111068757795181583360044506380667733885101120000*I12^3 - 6489746915135594984963654671629198786680965364884624601488639376723800831839715315995542124\
        9668567506820992903437361576293605920518813095163376299502840366394440558028285056226070394758370139334332000056745824589028000*J15*J12*J09 -
        634062020288019802288114935108771300235373964192538422025330953858577735575261307911844032140525062770246392297172260870168246026646453129652738992926046229724528591299174330311694698\
        01466450869158580959017850010144000*I15*I12*J09 - 2033747202974048737274696842889107327079209078833709911789542510636275038893760205941602421234975453206406206327273124484302917000789\
        325261904653577983773735344028202343206937053702384571605526251288947667398762961600*J18*J09^2 +
        315368446839674506490861407639890194265169811988258967647625257393419268722695551830254244856737488486200276262348869551691184188039020352160209657835133734183265234848122435149055070\
        177985694837788392638792092894400*I18*J09^2 + 12465345911749236316620942443083889448626626026733204571942043700043863045350703917494928102642237231128947996905906518362762775044873471\
        44047586613084077334388051977949750989129738364223055146766456376738712691572000*J15*J12*I09 -
        735494844978829714573920662509386265636853534905506093609933323166477101904381719667862820233659226265201982438734976104899175115816650268660389355176910107564683709808284598604597650\
        8239815530889192088137716625300000*I15*J12*I09 + 46352447519357722786109718394619776045042941113759949702931391694575098653282988352678118363933925341995383791224178109255405352372278\
        598515299695336354746908517100242041640591255101448610163602403369911379012701856000*I15*I12*I09 +
        134044941288162219833207796451495385604001916044744855972776177700053898355011546418181215675921396245805128227236833460770379478072494968322395125465923427453180356756462273568563586\
        5411946996024574359914162917900800*J18*J09*I09 - 50652496524596772032270014088828572680769956407665908309823344451317027799912383403383947629576241501507071137864834894793052861633026\
        4590374764958309883751528137690302689183648534317059223322797755633804564801139200*I18*J09*I09 +
        321827527433208728457222330347961768522927691624248318815633922361799351844199904212274312990264777267758512013546680592367096276624743163014893337012971948922143564515957991715117298\
        8121062909155226344326920292352000*J18*I09^2 - 2484238568667625853180453487829893234452801197997177043940341405473365188925345392533380268354251239146596822920987803109036795194955522\
        27891308714720767433676785558787111373299151646593496133755642302946038769299200*J09^2*I09^2 +
        496847713733525170636090697565978646890560239599435408788068281094673037785069078506676053670850247829319364584197560621807359038991104455782617429441534867353571117574222746598303293\
        186992267511284605892077538598400*J09*I09^3 + 73993868227628501057753312261343329015142531753230065227948004258133538790094798428510840345464811902393460059254388048293367037603278322\
        0342029802147711745824022712141838246849375132598371257946374755516824353700704000*I15^2*I06 +
        129593552948168227922428775768502320744013107894406498722946569612918178005487538065995418543916671016345740857257386122237256479183133860351242574739289198896026840464885477331865436\
        3528226793930798202467094164839990400*J18*I12*I06 + 16539407520588569796790034140443452601120021077577246122448198245504393112178568771060819683967417180627032106468897398144402646889\
        33594651791476756690056433915119893288672427050165139864994003697797417050122813976854400*I18*I12*I06 -
        655170845478207798462629414874805325791388878273103404959221192029284303087810560171825999766130110250428038230601276139146664828922258572185735870166163598559070543297136683194680246\
        38430384302343646702758594236752000*J21*J09*I06 + 1108419433668210503769994078595311203388879913308059134081146864922519304438134467572626815606264380359194806018834933837068840792360\
        026308702335018574373494612466325035872679915186891117174523309738091003298497849216000*I21*J09*I06 +
        275504580781521984366624952825036076010076316529091642113815555366032697856252313025049078363974410921322518683380375870099740340196521414505746409418316233494267482182095117054041573\
        889256310922510513410776408287393600*J12*J09^2*I06 + 3043647831202602154546113893271901451186972385107901454414919470680759926479889028315225455696897459933568944155269108365468564956\
        9907733288558400421854406374246233260794243793971128733084162553677777695958756055040000*J21*I09*I06 -
        475747320945225267416061683155665532544304400804407070028410151036123005140207939140354026495881683592139600540407867836114237258294263014061363149670325720247724589595872165637890821\
        744361739215179642647185652038400000*I21*I09*I06 - 105888421784399398276537566055133954800835582447054106693969805124985727234099625434600862752208263786487133466886802516083055622550\
        7434840197063912658237862222169508621837977878508486864593273675611665523892608679638400*I12*J09*I09*I06 +
        138774561422432661839959939108238723713813146025480271596406897442117524923178578811966615488744095442695314571661758478354428316807336772795998481414110677052217754898465959136273514\
        772290153817568729039530990211555200*I12*I09^2*I06 + 5629073814457959436813590865204058395892252950782256097749261765766684019105834505437970527319068136465313946796339111273159686358\
        398530738334174305751519048443615617074510882115084639900088382389928633456929204974080000*J12^2*I06^2 +
        100709859272688375072159454834393734375313728535968233572808524936089740625073316117706873931548330018296748054955978282918465472078435358157790562684251474545374562439132306406020941\
        585316521864121321756158874740920806400*J15*J09*I06^2 - 5148032081792183876559162403693447378095514548701416841886844211957743992263164987746917621987212065747231070671420412701566938\
        2092506338086373824799108880274551147846065813154410525931629699137671414606330479445431667200*I15*J09*I06^2 +
        542369940815748011289411131539736379717092921841008964016413027621537169636934069648145729777116900802127686706132773829575191542786579755973250867576928388288710545503819187116467384\
        73779945419230275754506639572662272000*I15*I09*I06^2 - 75719612333973990152747087958154395070694550248765431619919522570885373153482524951177805881125982344709954379699671410136127468\
        87017314266801353616634619072545116583070403277690582004729047881066885484336257508959903744000*J18*I06^3 +
        196809449703958166148185318881250753888907369038454484290667609399996117981849692123695416777931259510451300882418209343677511134165070203773523956295976655550116007860760972823001853\
        5680684214316478852597393088740438016000*I18*I06^3 - 1109275311131259542241213143727951643326318302385303492493594383827565995156291161971835439700976312928546692418246791398082597158\
        502007660626590426106344464277708126426543878710029538867533948253615914815829523334920243200*J09^2*I06^3 +
        119305684091888960110448483069968558148691430447289234556607319910105227198522016334323539744593773738388770998667711457609155468890392461148836107628440348704918167797223763513439817\
        9908191805338658477240961748713455155200*J09*I09*I06^3 - 421005374247797657285619895450538208832712399557089001609363408205133533219680802135140328661917840220785167089752777962034887\
        093410650131314197285754360395298444953748369043820484803861574156137133620567701346897926656000*I09^2*I06^3 -
        408361234119350579930430032994308488934898551420044740225350125750581596284565541289474066714134783080583262004296151286298138123850694349025505928690408650646542703660356806465475418\
        99476763978815205017222151238781235200000*J12*I06^4 + 452256841796184099655408538830797032811402582216379724130193101421896507466656191349632556938133106357301208096765772718224272405\
        732242530314970738451119740755685655336409546050809115835965747980424700231418755229675491328000*I12*I06^4 -
        527038187376757719892827615965554897179679605573390117825127056412946756354529275904258692480469611133185039874058175026491733983924112333710615087953119497033162725793253236158734640\
        40908127331422794310474861018559200*J18*I15*I03 - 8100814781874487113117426023324511606967373807560107046241927296205822402299674577060078148363533750594534362728257625753579691165307\
        50898308246506545618632002952111268111932972048166113893280746096791639660213075200*I18*I15*I03 +
        901230572079034839968442931343392222731819985649607144931272692054844367063655069866475175660372781833147119096671786309115491399999701585565634255238619518082371771753185190381627026\
        3326878872173090127778009827100000*J21*J12*I03 - 45288772200939309263500848795896483666703611292831052443267477197815032538976138390150466991850173130538211323588535195377244082819651\
        689995083383092083468628612795318371571072949556712904970920331123317659196330560000*I21*J12*I03 -
        544777592508549328129847588780843390017320723323080490343243745582348120950831193488317405677538925838647035833440980887030646348092876593064181588398819129280923367202087333619507617\
        21342410727000970602912873445608000*J21*I12*I03 + 4753050896631116746232253305259684939903510865779134393769173006130614229317206272819340308435289400279122808073888639068759552517634\
        77813144296082841457252988238347724837005449460724175960338401067200761699248681776000*I21*I12*I03 +
        194256070712817441990111152803893024922398107496383434349151660850422241896065453559395731069454442971191624289836118619599318818513858153644375920672027143336601868917979398913935133\
        563810103234621692242142804576172000*J12*I12*J09*I03 - 32097032571930622548555980657432157104293946778167981357126455615154811570643879132805180689287261482837253515552052399136252080\
        2711651272850030045610378287381948231462555409590663431423150212582619909596956593186090200*I12^2*J09*I03 -
        242054040762967474809257786492137699698229798613880166122627781463734926248223312635955132048169501455689431946068218592716436730901088848707595124927064523573728083487153961412251206\
        25193818042985007633527570321668600*I15*J09^2*I03 - 10090196191914514815784469744177883065146421564511699161248073046562967127959839595650119688682622970323851311816313501949960249244\
        888770791935860848670896989804622611388021966642248789406391970842352499789398085850000*J12^2*I09*I03 -
        113164902661277636624687931276652651994384599868183160939867886752051973065884647917595205511011838527554721593354350850834610064629904684912755395878248585497844881971214222924842984\
        51407442456602346911394813849314400*J12*I12*I09*I03 + 203652476466127579025269353947007653893171259386255084190350644144184138562885411173149262372360646437133461725345047881872177232\
        33885870929686575688512690919888799364052105618342128709617730086490424068735272900548000*I12^2*I09*I03 +
        232786829199437891910369058051610070287707538634480402712486689585320287299110909491140663478795493048981441324220743073838373023475199855440168923183475765536876869326140221985521097\
        79145039065710614955909540296039600*J15*J09*I09*I03 + 420199118218847707950359033514431454889776034526902119035648986263404955261417224279913894971442304501836246479810437452803020771\
        97649228308306999022971480330270873383601712792737553302222643349755735107279785943202600*I15*J09*I09*I03 -
        633395923168560457053618486337287865001854549601604763222937440092632922974534758461385229611410629802183333255803891987473780868463100989886233267300207633620347780645008012826561868\
        9693941509080169899369450580632400*I15*I09^2*I03 - 527769412256065662315443387209168838037970955143720544238146358903523486565004502171108090897811521367551210252496056233594485973132\
        988356562794068010844940196394923909413854084352823019596526663404728046909505575960000*I15*J12*I06*I03 +
        313637717826189269543514749095476395429212756359191065880403958424311395602129108340064352154805313622326728806146142911275367731262119810081069035618561826950826059393875856273173265\
        9482258102184166988009635759672636800*J15*I12*I06*I03 + 4557597862072795765389171105389795879609810576649366665482639397885802758693273077805329573341540601318063562650754586568334422\
        549257547302900632069155558834661513211222698576444461293621793162614082124046945112421433600*I15*I12*I06*I03 +
        999262792766964550716959098388774650230839824857510120543429674175858098079745786818531761617622771128584467951146026660401147600625862301756956363758204751597224918840150313889551157\
        686518448369972412172807340427112000*J18*J09*I06*I03 + 11857499940772303306561295258628713939761315624476447226485220625293010594692504258564914135776295671233443683178708090051299815\
        21004861927772740789578450834516290750414938745039679868369583933600671494550747731618128000*I18*J09*I06*I03 -
        792574604345450294546691707638776109650929507509119968385008702178064931490601501347049013554293382032600782349227125877723621881850068742546101317172301594101304497921597375833098398\
        157866275306337945634092708146399120*J09^3*I06*I03 - 3227261221049949464930478828729883120987550423792600108637172108461734823859435175525702688388643532803494894424558106770767225394\
        58233545054975071961741081660452766054387193987141554285622713543163486451258509371516800*J18*I09*I06*I03 -
        674279120168737846720623010036771416942850476875512278429893944672217060160425128269029006758201360144990922498639176848489366486461642390226929541455008709982174493112990321617342535\
        691816397495121294577561930812668800*I18*I09*I06*I03 - 16364065690279972339642768884273221060353066306938548373449239471666268158292196181471275541490941664143994305912843091313613012\
        2284285543575551687345693626241706259054692654356092820637407694618145447161448066224024560*J09^2*I09*I06*I03 +
        661138725998242361431260448579413820345619811714333297440074259687188178144899987551657518302123610997941865486241219454053636319642787630338262078715921958882017937735310973318348644\
        15063063434628840455334719847285600*J09*I09^2*I06*I03 + 5905865689791533964366938922735563797468493112711460033699790949996556157003508136383638274047636020587694786794342402212572559\
        5940308873969830753349156353698592353983622351237503888396770864581156357738533925204246400*I09^3*I06*I03 -
        105191450074041421483048062297145466549208556198241511819407261629424471207064128278940564370807710083746588906702177614338661382669261696288484592568761152922800911344465875783260917\
        250690081913542171187732950560962560000*I21*I06^2*I03 - 3652054017288132639137517172842714481726680142556736736801537664669510199807761169493283797913435047118417782442568451323596123\
        0902635613494557275737218379213643460355073268407427759608459003258485168127021691938918857600*J12*J09*I06^2*I03 -
        198516571024052254698140538884679800603303242273097000426630539886659673469517127721261641912651550514210766509592847307670022945541413397793630949158281169026478636408874733370980766\
        63630590288199313297096391244879232000*J12*I09*I06^2*I03 + 1581604051409889447537912045157083629405974954251893479327129651450616506574719375190805761154401642857418468363625154103604\
        33557168727060137613608601539937043139318655178725244716567630041037975632451813853302807121939200*I12*I09*I06^2*I03 +
        314462579828679560277963739247084110165782551869191055809995048138637937771507073949591162683830980737656848159148853725938444248639756161371329669091634344716072319211328747173036160\
        968237532482969980822131290779609600000*J15*I06^3*I03 + 8601657478080320890563842457782053997797963525298018662809358575036281211236079024421737330551883324349348575946758343022562711\
        3384435250757396894376908991237930489236596247342530501972376479572079666681823444213477468313600*J09*I06^4*I03 +
        138824352491365361989901889728167411618208246594631669198973563737521806682310403426506192740343558668574685730707924645132976743833730799843052366958366565471783737346678574788619242\
        375373213780832158913936476984757600*J15*I15*I03^2 + 3421379184453995201996009933695770667759819748521646055982796931141390058659177780946541401510657887277420762547287023813376795547\
        093524672510137393246832335000285505142685001327252275498789575855743872669381181003200*I15^2*I03^2 -
        680317363634002799812635081612845777141896927510351240090878546003874616332265853617342262544311204514530683725462355199399218439609733115752805233103374858248068272030138240336080138\
        98134031387734274706297806633944800*J18*J12*I03^2 - 97329019192567641884286367795286828497067553023936816105995053825524381899772231004943150607854367780554062706468569643915072659756\
        2120413124202119694556639971078473352999919103716371220211307031341903523203994450800*I18*J12*I03^2 +
        235872801927703406627576735010800622995317976847021352643511047229447669019649953565088339235416671367514924916273919326348412734547973882982538114817461458279639954630283422662947221\
        53003728733796106692310463795806000*J18*I12*I03^2 + 22906393662706502863001807305333383331365880297494594449976039320258510004250197851867328297946265794984771590795377130658634691363\
        309356464317959733493909337873026518048333032426119095631355058677696166757272660726000*I18*I12*I03^2 -
        899494610817273666979367571883161932142273589170073227548129460760568101464249643845657799123666372615300307001866274036945766688261780244871855780908820333298285953197200288332454076\
        254807155960692373514679560376000*J21*J09*I03^2 + 4864713952123705832696605163286960736377728558593557762423304230594681171450705902689701977055302343874384473078296683872288715093355\
        546276034135881147205565587948092730142155593808456106975516760679968649491016961500*J12*J09^2*I03^2 -
        132842557458688487960050190652846385279808049046630372751636469043668206863606291619873064837427191062180295605413284363023062015707790257399593558302982365824785004661329445632795543\
        804869892672512703988271717806169880*I12*J09^2*I03^2 + 26201012640136679603299524265116759344702137885676189667741898009381832350947368567813206758687529303722302052739257113078413668\
        87329648284880854976084646951405875160352076824166243745320830465077137101826037364956000*J21*I09*I03^2 -
        242592379785327424196554215415608900111126358263414482084114777989079563488180942842255553442230690559450117166399055402282675828461380687448314886968316092162525609196785825022140146\
        16351508663051848343645276013984000*I21*I09*I03^2 + 15594321640380594352916992948864478421066330419747237738080952298066109227770794759645837407887602399354731058516775654346026194266\
        21686421401909741310262603220682327075094812432847896503199226326801793843829707596300*J12*J09*I09*I03^2 +
        177369243873602141423055648340896761995150299149929566259435568663439989296584840182297402132383569022377211740764337927103499162354797115657530426269483779380694231585942297471445956\
        5103700505369976947185455572955400*J12*I09^2*I03^2 - 8031303831702935282243978132055873306067713448924429296008714774971324070950197949548835640397330499904939013738282584052931845331\
        422571662587985604964013322604775798950819365379076237794447749585316421248927877419880*I12*I09^2*I03^2 -
        639784572581995409138141812561620578255174633151918169925335066227720964817286180644269219888254933418180061203424400221865299018789774600989605059809886046823543245212831035843863426\
        080905278984647488861733827456380000*J12^2*I06*I03^2 + 48110308013702653689938104649836325046149707832299476542322575442978698244402526873764607175147878176748364857831953359559529051\
        9557034935918558984431542981575962993087863224394434709295814933015291703536655303045953600*J12*I12*I06*I03^2 +
        451072956524487753975411764045792608081715758152035126164580051409187991214153923047072930852855813040513427147959243418686151018798158996996521278645858020371919494230127735255209061\
        3559393428176953488044635757174393600*I12^2*I06*I03^2 + 1222260243560773840472324790848334543850296803854446610911793846507277690508252781329401843591761282377647339435896998473737625\
        275103502053847036862273954504747320781450790057055968474352206315522977319699345950926137280*J15*J09*I06*I03^2 -
        269838263590380290822348704477157501484556805959691794929705239120803405370352696029666621435074282236337117410605247062339365889693541651373417991379415769497856870585367623516850297\
        6158473631189636515781469482665599840*I15*J09*I06*I03^2 + 24348920144417921953869545868529094783430731275248211303627037737507723227950705212883285436142700218878110174810305468721443\
        4009403924983303188126311171876552668929435597124770002973768747601454783015754626554485735200*J15*I09*I06*I03^2 -
        176642155008134680693520955654378923631574902824097471720116034791536902898985029464346486300782832063124146687364200156913276083019265378896097467730969486420457562043733257775280265\
        6339633377517821993918267042836224000*I18*I06^2*I03^2 + 7873277307607987640785856242562777956538698460950427699950471167896563882587751110694931800487884274451841236392140510699458854\
        3429684028893303712461531395390028020508183562164761517410738065414440093903220390701574728640*J09^2*I06^2*I03^2 -
        199636611710815422659774195016579056930205071870549263125075254848777005459865252363923656587818655356522236222224562055250302736309878008700358277956220190990758941008311062770728982\
        25493373922160027974325024490298966080*J09*I09*I06^2*I03^2 + 77786039705632014942558484035301855561237060217385170793906518054215789647795508592743124282737428240986430409538002750025\
        53194808221631346405925011191367821162655146688568365103568209772079218973114684127982460085072230400*I12*I06^3*I03^2 -
        595276603185616867579026152086763157538529274158240800377677607794648562307189452055342314495440917677423580276900200160356325640451071580666400771425943901987717213327891846216497591\
        785143336203845695238077758659882713088000*I06^5*I03^2 + 593151967000723519668447556566236896711900191798739990693819023761626825224628015596414107057968723719278741528073698624491313\
        26149256612062198187351095867114011850347233241600885941559312680328362798637819992453227600*J15*J12*I03^3 -
        224541605542223197770063133564422988471648654292433033979179451636425790860553804408558260576957503961840968196075204838424045072646259611953506407170569520187154802192349269104667199\
        69386342083497264855267699319032900*I15*J12*I03^3 + 54699617892279426286120079208944276207197072140354287004686941791529191284828770096779351139792772347518237950914252164332193466780\
        427936937057712658518096880553970660912848152769028683936489933060948621698555846627400*I15*I12*I03^3 +
        603871281495248176648856991052663228676034802757674692795721766746110847139542344879000067743929807904771594358779399584530590209767929181255313932021667463164364563925201607667567466\
        89531603345947692782683001963464800*J18*J09*I03^3 - 97384407053649494878618748752743890401445973936903189782811017209247082066953800804240310192654874301721509497478433096565142016525\
        2207864027878579139460995077171053733004688186283164286722983914139845154443242437200*I18*J09*I03^3 +
        924268749405435126670298054775174258343694912699754466619411797922106473008191595269187052424779571610629305474030139880278208079746779730032783323864050799691163892312920010261770773\
        816789152929224304210046133129000*J09*I09^2*I03^3 - 39478517329391137418724998099488971782606469902236514167062515961632530794506508718997913708229938997824241424312016220990252080842\
        8731473542964896723739438030813553904494925130807765804683503149330290099652660623200000*J21*I06*I03^3 +
        306381830021748420235794616623972113119269111712652728877087190348587653456757776491283033822904909079957362881964938631807802426826706848055183329718179876300372944176180445173716437\
        7154166390128439426829558530503808000*I21*I06*I03^3 + 603771820611327674992293571201599669354666716000492793880241166610473033228571871987737522265879612502023401592326113326336655281\
        817614771605299330380408764261866714315617234435254960959920390631927411832951350106797720*J12*J09*I06*I03^3 +
        373454058348427698824217557651545723302936365447306940537648013847681476369363119111943360700174558764186221431189135100109644047948437838418317440129498703436100500516455028551257176\
        8209636023260020571446548660301600800*I12*J09*I06*I03^3 - 59978819526806115689252991972289039757745832407974606286477536093951920623538757328444342892448118314758376519687487531527264\
        768150807186947393843539931702925523133838851229545613177277212369362099077218867992963598160*I12*I09*I06*I03^3 -
        193073299331181099118022143202680260846248878487312146129425167762218621868497805456943144079928131810132315226539300034380647493923669011715307433471549690331409131673696562196884294\
        220119897803562301494605989240482534400*J15*I06^2*I03^3 + 10155441126330814994048168367547204630750284524609805801881675281461553891095236783250862346430584154559950750033378413184015\
        5900352568597580325314906393176138958427163380386091123239524613734288709074121813998648253836800*I15*I06^2*I03^3 -
        210013637851498649479641806125550115384171026978332004508293869182614184405206375420640308470187051620677094397284665807234153103337856787591131632387594206036723678599552336457631412\
        6459567289357134803763390887352095397120*J09*I06^3*I03^3 + 2040990362696546310178470854673420238961476326443277426147925771518402577658122460159907816251012967423521955138774204508077\
        034616252174889300839839394629225999217980335541758763465891028729156725390742760655624922635238400*I09*I06^3*I03^3 -
        358221344671938581210758930593390923903047277373817899036095083852735038886387550061195641254897839855846487865935976840092272327614061895291738002757902418731059884916495548172226449\
        166530707507892257735021385091750*J12^2*I03^4 + 115636339543252224699121002768500935917347561222065407433776441581084589003994902282530909906613942085602405236537297631139052838622429\
        49429318023011158411137974365427228480693557020928144748438836739302140089120891000*J12*I12*I03^4 -
        641444133091088576203946334253736511462223173389865023327193461562091264114894843309138952266084241598237447405527008119231148955917517069272834689627475471610785067279534411114658599\
        2936189966558468268592700118451000*I12^2*I03^4 - 51234217031879278192963677262897474339304439721101289448472426802355413952369774009830706089018156294076714215077119136202906071100012\
        354872578424778630781068942206197710608248516950540209497573172770300357929640651730*J15*J09*I03^4 +
        161523133744884680018187303213106567106148100042409174497927052386488882988739778406946832246818705821884388397143568914345298247465381038912829842453759907614908960030619477012486364\
        7293499886235985247161387839044160*I15*J09*I03^4 - 620263336285857814524638336055445912540181221982766697197720142226041747207664710246469812715969634034844331318855467924834981304535\
        1030925688846713937682579148921781011069682951297262946194803237556567660663373350790*J15*I09*I03^4 -
        449729424811530031065573594338887666594097331922426740223772102405257464978077088216977741854893954573529758921417007648642971980674984297095788232307864320399666495137180045676713224\
        182753595842656402310601107979920*I15*I09*I03^4 - 4715064090644515060710750555889112779774061074671374651811862233066214241064727848214136343297282754744234522201338625048728044786235\
        80390612352090160390773963991333904545280485639282939499458095041675382909607649814000*J18*I06*I03^4 +
        326601152746604645330304538102707128441532531810957727097753547275176556604710416473750501643428633262074921891289720432005513632514964892947243526137850460839809419695595639951073699\
        154256261920691761687273978506470000*I18*I06*I03^4 - 9857864627485950920912494441607480403759652064346137066069294026560682628780263754311385569146584558607306041139571217494534539692\
        65810470083384532968056794598758617062849474145384754225956340225338313868741236791181684*J09^2*I06*I03^4 +
        268553412491691734696099751434430660669450310827060499384989617047096605535002208260323731427934953645672430470923038002886930614990257412919530842268034101325911198195890793757745082\
        53234460797106948876897374546406388*J09*I09*I06*I03^4 + 7435853715920399581242849282607833270987080135809937637100216658152891170353988402801332343525004752799695205747111828761202509\
        38793279599849257760776425367643910689045840752953078013297893092249679975999226035211200*I09^2*I06*I03^4 +
        284181192937326385075266447930502718666247823529756073680333472152933739422708749761349097217129515871427345605403111106543741713021206315822782127926585413430200905066662219750459829\
        11032897945508056371149030484865200000*J12*I06^2*I03^4 - 615137976721819109961085022402140062753245725093010552498057602027438236157019645995672766703639358712439685153477390573119741\
        66900657660312164705318091948442072135311627181997823941804228493946943462221769883934507593600*I12*I06^2*I03^4 -
        199552182040508863959731522747098509160000280518323868971681193719641840330211131345873019594465557812344135613005956826605035748699321329123735302939279552606230568571772591765879305\
        082101216802601843905282154408000*J21*I03^5 - 97497096328613420475151661989244878632612478076946214985336649492346211830087648624456780595546515745310466962164552591129553272660353343\
        7966133868977838734687364955473298331287968733086303432885473586227958022510750*J12*J09*I03^5 +
        104254289992633074077285276222580045470421887486523045565566181434105033010331596497959646527952764244171547001178230820582317634879083024789089651684946162518642795188806575874313566\
        1430011039491804106519920641959000*J12*I09*I03^5 - 190851940333216950636677801900431951539085715668965507578164739569638585799796730730838860649679042917741702254767463848419046826708\
        293541259685813036817839868218048845123896355018496437612454044721607093196118779506800*J15*I06*I03^5 +
        234723008586586225070574383099938875103663898763492259849938718776452142548018015749429526645842051941831448356060720422646594838849266987415027722393994322320764822281056771759720270\
        82469655767368156496338253919225760280*J09*I06^2*I03^5 + 219318396928024906959080725183199652172145957442615021957287305192772646892360873302543213689131535775847297783001319205895819\
        2972204499303862301980864224764887799854112315150167826211416973715616135565669223996564225*J18*I03^6 +
        906765825952373548440119985151079377027206467502426022481200357769502720342187207062176844318586194012034075293710849462600667239470347914507801368202050084904428519245715500893519250\
        551357535614077443151215573246975*I18*I03^6 - 37577107677045780430174986473555045119336438994901854564701566746324705744166195423325289371435865267470916521697164260683199655113219561\
        2096829905349885339966671746679784962130138018332172840987674767144139983994625*J09*I09*I03^6 -
        995130904979210340651883314289622042474649219326331326146753278666477716931850232374809470590749491209848134921952711970800116493690023777715545387751182901142867798993092645420880371\
        95989176522397522318168627973625*I09^2*I03^6 + 4849063113836131782597163886266108750988049285092659742905739027408018394637692351047058761473177333439741519858429227186606687305002235\
        5102944853643143551128466366773313546045948240498317024905146903092191142776859000*I12*I06*I03^6 -
        154233916676528928514619592975174898082163990737503082697422864095939620986031652106016907144208793258429764958686762573616829420570448029444176753139845690278972125824129749635915503\
        138748681109981143465200917784190464000*I06^3*I03^6 - 323619363078588576433125210887130255571809592152608751319798444420044297267083091834342720157249366535047051187647425394059828911\
        5278066653939542423464117231999257291169053466607669885570358811026712616596678837926850*J15*I03^7 +
        294213160971813161319446697854325140004342078138664901942639897662220082937006200476261439782302702067303172409892956303325022209404781411568583622786051873325754150013244964776477379\
        496453930368382738023871463158550*I15*I03^7 + 20772657773102274503661906201557524310396500324008624520013232556522914054871209659591562177015046774732876067731386069944564029216307763\
        761746911576124011593634794065602281545383990946448523456197125327183283268346500*I09*I06*I03^7 +
        880021118521723877303373916203661146717861846443021745998453265936228684349868683917396076481916388138649843145653210167555621193822390901388873413520791158233679669015157503201351462\
        06658712634395459918802219958750*J12*I03^8 - 746628095207304821131584881502705731261049983072253874722746077473414351362000220435697150400726138956396816335098707706237942022394198061\
        65279326832871642536590215613346546524606390743553193599352366381621924056750*J09*I03^9 + 820124377446046664931368653755965433457089765267169006619342267830659931838562663432924410047\
        658177967836662938565528104690503473747210695872281504953575954091586771039328690041302421261114055538854718823032064219000*I06*I03^10 -
        524036139671106487337002197006978273391986929215474407513068212638695882217350870932022486711555969313751784492355747273802042154209706289828106668290432108757527238256666131301140598\
        5804983149904720801538687630000*I03^12,
        8054419489349044825337089842285111928486878380543921970861211043113153221459857902592007586674576668562686528533859166375025678542994206522574247971719501432790510588639213702218596905011\
        06405047460474493152426600000*J21*I15 - 32997918437990544703796650961079919164093408960460451369597768797527521695445974140988526324064771439377863656483583148644779178940166349366799\
        303083522802640351999048113647679321798888016013248788499239479229873600000*I21*I15 + 2517514130268848513264437243756671229156124473986952071334629677087356455789052435673005202055580\
        591558580473104488393016770448045060718792349978300970318076784694525078457315102010617357361294544523040802727497408000*J12^2*I12 +
        420212329011112736017302079927748192971018422029408527527891925882558185887721153072531778028159370396611302032780295437114377793126449648671449005808760341507704993639183003879519266\
        80431102613676145736623582641728000*J12*I12^2 - 686962561447718195574402957876147392112540433708819212896867056558302799086835409411440284088489618904985013694021431998548901770703540\
        64583504802048497266898921311727303979540907413909700716833239395446741510831760000*I12^3 - 6455614026601387792966519213898430738939597935573278405935771205041948326333348515822381297\
        2532787800541787558828446717618251176070033979714404313507661927778778620917409184456570231550044183832340894677491167328964000*J15*J12*J09 -
        525472067130281441642078285459185339256309383065136078860200762567464543461805752133428265053189669115409279482766536517345319223125484839521048421853142952903546525714118476108915244\
        93120889820744261314304140539872000*I15*I12*J09 - 2735628480060849232439367985844431688623777588865190122934574747060124233144891195226819282782051655397062429211740024630619905503281\
        629762136166376379657935130483761565813340113973090349119004895722247342272165601600*J18*J09^2 +
        353911782278695384762852348960740539238586884599209789157459677248488137356485280122794013721466901767858339104475200205099290439639310075936222870518946591936203020804326792102063091\
        393426189296414631966954282273600*I18*J09^2 + 55968654961552486951880423351021866080045929754359637774486465037346645078937308327060703958847781662478657509797941300264681055642319152\
        38985543568941760582874594866652116134346505563314303308688803533129414522196000*J15*J12*I09 -
        659786374903306242897465398336891078012790062616227421564531568261774144035257000890059661672387446883274970241936830272944718261710574833823884081094110419539102229656990479721801531\
        4520326098781895611997926614772000*I15*J12*I09 + 39544332502211203336757417551008352899235798045562889195940426503918921330623571467861519558904473804637669368864074265894121239414019\
        235251288956418174596879927872041591572049465985683137442882533811941087157884256000*I15*I12*I09 +
        350688153791842074478702233616719606764815863258772898341834015866814762424599790120889951741493807592261224311935551174611909570070806333642991820200313123980396870658702179786213306\
        5389458546574612393523957955987200*J18*J09*I09 - 58946575330089529627691499504179208063801956918872454459428772793035818183332257830246743113994887977525141489261140228969043661273296\
        7446843252892796286312109482489919948105897834666017369482406961128329469272825600*I18*J09*I09 +
        179831024178963692170521261920893265809401749011079191793024939270507601225390530351330736284460184205465049091414710886109483381388864368515935783316344556918137370269251115521837892\
        8766866795088037761441265499443200*J18*I09^2 - 2367156225129909464975794057593779956783084000193900674412632531332361857592959638862411926059698475209305266326779962410162885330913054\
        10058385696483213743525847103377410956612583033538965792371736271208878583443200*J09^2*I09^2 +
        473431245025981892995158811518755991356616800038780134882526506266472371518591927772482385211939695041861053265355992482032577066182610820116771392966427487051694206754821913225166067\
        077931584743472542417757166886400*J09*I09^3 + 68815261271318860790667656801892662593563901898501195666849827890799379313960977687527139838258784865588019948253278944521507744983101735\
        5724933897766648434111762471729642394876952038375813932596113597807455008207968000*I15^2*I06 +
        391014763937599451656686849565230933458265114116759549255176792130444578132477460679604731601218044260276658576832802721528776633953545676858301416371066552571461200587735428723114545\
        771290237240656442590786420686080000*J18*J12*I06 + 533377892969978533208295027514130330298506918428911859052811177640687050981560953033598925115191102340840851297768643726976996681171\
        308751960369393581982954544125454047633268650391454483574724397086409527549773824972800*J18*I12*I06 +
        141786189365117907210369558009673072279930619837426970308516516529207274550430213199368979244423687769811869057362229717377995477036555185345852582414686377370150732978153242684190723\
        5106709126554294343012796092516940800*I18*I12*I06 - 74865510122400951973318601759100299204188734936343343285057559895690443400774306518334871876550371006748637621818033891320489764525\
        078645267231220922092116491007539750106895081561369311521691468592904293908238853072000*J21*J09*I06 +
        771280167958923665390100748820212569524279143398095044852745355193752157751964703547144983191647594007973756157760079126029453115675496648598939406713012879379119401808750897860109585\
        074840256396899521352887363756416000*I21*J09*I06 + 270157085026613853273175919172121434842895742981039765540436864461175345088002197019227055190465632479140400739545684705340293729619\
        683001711239976018819794560164243362982565141176125949919233846508115341587603787297600*J12*J09^2*I06 +
        153331725663264846065149905452809766830561033503456903182168409510199585141046541532533562943915548094111704993156717785507107284357811874666220899662090549639171627589410012965092245\
        03161699417336011292741502620800000*J21*I09*I06 - 1204566184495940232838408360482572243411649775515994683737112060988779544816443420792102379830791027496752602071113271505974718217314\
        22161122398067342997056799032483149316973350175406694034080099696872356349165879040000*I21*I09*I06 -
        999201143086334494370567185714277498567733769638318340768163847632453002474949358038427815690201039106044718325433190068083611250760464569012567823858552430156939706124014861266828692\
        381102149843227368199859828824611200*I12*J09*I09*I06 + 12608872055163855868692362953191072749970045008778206263491746380432126590040449181766949288418099492988840090486838247480726847\
        5958112724164515311536042964614465097439148947003626222955922237077444461094744221231996800*I12*I09^2*I06 +
        413434373286085076714968874594095127147199707186473773208936050529128491449265851543708040928644396628902213629801431305264135791416746724279987239063305375441707342825504962553352059\
        4110681045064994194307958553044480000*J12^2*I06^2 + 72737461075547621198758273967456315621491942648425251510971920426918332928130436963041398227317187737656160589756992710366254297509\
        698721234599145681226692828320635807842407126724326741962540972605868989297751920657766400*J15*J09*I06^2 -
        546460155658234254176939101504303431357449235491138439394201229032624282434410097328061591948744567157000720820430129378355382448099668180797711748741441499324515699358856779473370625\
        59360848646775965841285784485816307200*I15*J09*I06^2 + 52062248082105977686452597224656686725243712566496784141243964108841406429784515003727975075614341918896210546072263197342917861\
        847305103431009123341798004768002682761632341581524265099383198203903676575771925411801600000*I15*I09*I06^2 -
        840695834773577003746395530688382302888658365841914862384225445928988522268085177271868278753265507566918769439289089514701407004759430889342106924765252638766558928762612800943346555\
        8969932221216853622217056083548795904000*J18*I06^3 + 2079477392619183121357428496887922438912573849753083810193040373652897261138057477224812804168907513517616629417853043262508024957\
        368275436489540587454365475508946414425094845472602053295370872003239806460757994572000256000*I18*I06^3 -
        102755678633380078977413044407167748008472670510460632921501554055755418163214361908204204198473626484955229062099620260571373393554823702009766518577233316414679620259238992902306704\
        3069584569865735296991880442333482547200*J09^2*I06^3 + 15920611033736398145037464991115698513090176575906646009655234403824285300039997318395077986220755956401232660382749652231874928\
        89372703918523326926838138879894151309082630476201822858925483263007398324415626010666974771200*J09*I09*I06^3 -
        501136080794826755753470338853584827679458210874966012840079889420158738797195684641341137140534526760742028822511219062139529180184946307028812632131914212306791945311341557585723883\
        876809232107394157017938711036731904000*I09^2*I06^3 - 406259351583957807805006848939183027029654012846184752183889841287469824383050428038294424569877974876144321844852401330986097466\
        32999877528028822881060847766758926131349859772248176274212325899822811897869649955585740800000*J12*I06^4 +
        484853724500680018993570007249386526660133701234889220075025746767432304698368655928420566244377336998333169761003430613367010116819486044256483636800179811340164508725561133514791934\
        529480574269515620699193283066341113856000*I12*I06^4 - 60624137069349071805011667628651387157143526717204818699612827380196575682797260209839609112279669699352267525190152265655072099\
        146938041794222114023163325236618549660591258272998771730172198051497527100415172745701600*J18*I15*I03 +
        657564125178513121055326055921993986275552507289087691822347151150784828523855594832904673819450033068298968104128439959995708031116514715539651374823274972695503514885209840361841255\
        007399801344527836410199291878400*I18*I15*I03 + 867955235689128341232007088490530169925077593592381772014289130733273522444064681788786279454824479162959444401759715125824151352689098\
        5084808684072840360958189372136054164220765486099174545102808507755477842254140000*J21*J12*I03 -
        371926999568995596004102882106086388611638943056142587698495967581954956750504173920913552354705808064793676203629341830942458418736138413218169372167307596160320744590107095873164899\
        43442484318954086938113071338560000*I21*J12*I03 - 4812048110510047728549886341974128333862447401664860724818010168145127890079302196493878110142215334271759518870737403452733584275573\
        9866214405992923646242984163209625635946619338093048918622557879161979254159847752000*J21*I12*I03 +
        421515437646803947179584855069802606152443566021417986221819172015557281044734536160908760191499789235938197430367201817130570553096475397741596506358112963368544904979334806234246651\
        575909993890113711268281602755632000*I21*I12*I03 + 174179453942755660584432603794893202177894369732365348494388672823187255076989461137008285208280941581926242729744318041677549643240\
        168693920403414143930456631409119075139413463964441654367897933161031603471874457512800*J12*I12*J09*I03 -
        291129611324514891434342520515759063738623501495068533818318646035275059469631041379394946771916101110419348161680288655742230148657635727397657143328163041921135365682906723723448870\
        573645376895717745593053497569823000*I12^2*J09*I03 - 2596101552849998552862822196027562275048122670381154195689661163870753078120679426425210161312981809570548435064795689908418092635\
        3528195216026290773406020011180507372446660345927526881571225489990665399095920013030200*I15*J09^2*I03 -
        111336098776679057215626614578229944322608407847790819291430041890067515695189088869628429928064377439468908175149757103883162715779896831023566964483699488447014127764226054154031908\
        52874595064232832729981847216746000*J12^2*I09*I03 - 78547293915697030319005416661404405657339727966229381999107811046159160233848352754975324191306668760867409963908086054593674010126\
        18091264903598461571163005446601333200904719743275795349439845153739210304860811285600*J12*I12*I09*I03 +
        216112693266013177431399242984555470241151991300158506525303480839049307357166389196119353338070627079502469389698172876870492971362409616653936004959757074550018447799804526234681071\
        80431196774669255846508124668076000*I12^2*I09*I03 + 17212511650123185670611531850016295062244645526791770634068605358281546024941652290877657006910998998485062220238104753303014247512\
        969461703596859171734488193887561254182928852500043310852306889833163840808043699948400*J15*J09*I09*I03 +
        435608446858802831007129751434127271713734556894867084235284597979425458507449806301003720580725462211660971562845838951441758511290395445823480304878842033192269702478118789355867597\
        74493386507536051327134386460233000*I15*J09*I09*I03 - 666894662634921886634136127434196621240753112860880123551475773779497194221765029059601938229520756198802149837420476516891153458\
        9590078883821392590820450469048388636258117124469498073880710241863602157680706712187600*I15*I09^2*I03 -
        479191017252209073644401441760862865180349731983098718262089995709761087452675866305453435915270267590951779253041394180102471080853986417223241538488258605756735120897181797564228464\
        490429296197608426988487693108312000*I15*J12*I06*I03 + 54749653651655324159437307684794948575844014008504432678923736432053737526315625129252321314420670383773640991155732280124188034\
        41234576817543639741704174640650288801698867227519185465517289489083101167458336842449996800*J15*I12*I06*I03 +
        461203334308071618918155377345266452735112242118512799856664522541935650003971077586648628940807378264745093806010396323938250269826797667413948468658675325393935081896891860135563056\
        3636049642452913022265567701884361600*I15*I12*I06*I03 + 8981438905229569499233234914701476890009547460593795274055121077323754984814635093120527299541534358652127013019916552183900699\
        94497122047204199409212820848831910305124099332161376759813819912339527283606157415910430400*J18*J09*I06*I03 +
        115016831494639816690314012201502025046041558778974676795048846967726049160407645932450011270344328386590406069809772505831413015264872382080806796050203901431210358765712185294303683\
        5759904843265909437642454842955302400*I18*J09*I06*I03 - 7715041405417625453985634316862860910165487583541108689601513002909699370819777462137471711198493731439415036351589185857951175\
        59154808676437249953321710634746032374248366482186973927585286788067233715916429140024911120*J09^3*I06*I03 -
        819786943325327656685602606139239502342086950521062960910566737813745123886112110223044015935398874177099940641321294072113921480756314660488483606507411327050947754348068686561698290\
        316514054445466398193508057438934400*J18*I09*I06*I03 - 59934524028866372411389007997305148465966141858490461887757838039640880856289545209810947006653985637793253281520238130873337295\
        6954562411946205087264633047706604577463234813526642266583339989466748483941981264269974400*I18*I09*I06*I03 -
        128905255569446955533992075183934040102294026795651961333025587017860186536769318277096607014461499571715657834452537491825823311007808719006170660639391596764438040371196559351804557\
        345367204463996847833738605450117360*J09^2*I09*I06*I03 + 113440499813892816040065800488996172098235117858615575330481455225870997049472083057656030485599926474639578482331428177392877\
        474760383208927460701675606327529104475604140650305004371874226862490309905433758787661599200*J09*I09^2*I06*I03 +
        543984218008342813205750444294694214855558936915694211743155056547597896663158898130625927660602951888686567022246704469759427451624478130644213351427610794041637338514457162810892996\
        18028411151424586949126717349622400*I09^3*I06*I03 - 10807680078503850448504833148325029025072813600798249809116855317085542197981636886894230725492395154980654179767447845189499983896\
        3110567774259266156452797021412682893217886290519087243564012327155884620832149254507520000*I21*I06^2*I03 -
        271455451690533972630156123924215852788109396226484152075422618442528996512101913135496439682428378713155478762325479535191301632537931933802933608272595828336194713111217414802974997\
        94189649005221496081828968415359113600*J12*J09*I06^2*I03 - 2279146197995966045011791850907518348101179603085682947804214842806929353173350250857373277049022863089263633537777753669425\
        7609213727886633960215220538217200985225143745799760825877858757921085334449414424859282983168000*J12*I09*I06^2*I03 +
        158364937288285967094936405472459953572204641865111563020816347205659880287145659729103404530807126226551674747987443639697037819133445074074947874282490493766643916348368998739814718\
        500924867549369340312738752497139052800*I12*I09*I06^2*I03 + 239656261470125209430155117248188363875798469907755641452627909343944182415596999063283101924170207669243377352275495126391\
        679465381749754450677902667590223831526721920226238189161072329936687791831151230308637092260352000*J15*I06^3*I03 +
        871120105291323691872190157143838603188302278365942548347705219818416251924311410629506259543015249607831158499530931885600413950537170315075548029129374944884166525228777323135440392\
        44835386544290563292775014528067377305600*J09*I06^4*I03 + 13492640406106786849160008309215670258230060926161023977178885931903523315159751509121422995464407139448592973295424372697514\
        9678926521983471315064813580866900466063827257993084470088570474835995565174383904685330468000*J15*I15*I03^2 -
        761315378049350688881287344442801918085876139094401724450054880980451735639185613145247026850118571017370861154173627795643292374436914431565471129600754866585563354510703194144347679\
        43344010303354443210830675609452800*J18*J12*I03^2 + 56100474930099071134947279910796136979065209150613112170591753420622057583610610780204746076471866701447779209279865406443618548221\
        1026176921427925570137290465443253126994359342451237762961872820105458924760797281200*I18*J12*I03^2 +
        272403414599288049087810297374349593102119497234952583310243581195538354138555688207385952428545746059669005219777932158918159699823351619203521717673573281590089050943202785451724872\
        45266308332989043285670575992354600*J18*I12*I03^2 + 19876896627498803669271103379423008825070914136601407740231990123414586046137118453407295169259047508930118750091233686954822435928\
        799009220826807222996481316312939901549632347481461211158637712390662956485885245892600*I18*I12*I03^2 -
        103015462923958993741048129248931513969342053314554664408951758745976431921196968277622225709874957390117521232430287158568224091129267170448909955820840113672611315323412125039265200\
        6083920414627862540774559360328000*J21*J09*I03^2 + 259012685379515258446359360762323797630207173512726077000726439045349914876235638726295390583170040791206797163641615135605464118845\
        8610218022822000670552118384835363284453552803386876103870470399375107345903905822300*J12*J09^2*I03^2 -
        116198514011530947100618724429822689000083021256419882378573993285178323326486353967027144119148943755022983448035484612050296057912647890153972209118329218144182025630491727923578783\
        563827368267110614694648506719819800*I12*J09^2*I03^2 + 29321158038224884015554432344829960642084344641663479996331855960639792863233007925773664759359012619495257104286006559562763948\
        95728915740770855764748179769385563238721805937287536383561800516998640155431997803612000*J21*I09*I03^2 -
        276452626070745681760041722842819795222796593045019490446372829955319734614498297237078729661934356237731133584416668610358021538345507406332727069592235375999757482474740683381792373\
        69910778388233220714459785685888000*I21*I09*I03^2 + 39090481941104728427631954221124166150208570813246956990080553294484695189917698295775066552082483993459229438598611855078632894559\
        30534540573243182902335189039311523961910081943747775347945409942891109875396182672300*J12*J09*I09*I03^2 +
        194325620603352763968858701857215810133424047759216893655485721754072686830985092081808741848863889336348716554010017284191242330822651358967119470333037283520342229666391146750452659\
        1779933529960984216494241376968200*J12*I09^2*I03^2 - 8711473675627689693200835200185561764066360235420286552589406692952340934503469170639058597347105655025936532220179389493212130824\
        064235947609196342842503870869481476807268794497557222287440423766656922300866141821800*I12*I09^2*I03^2 -
        776410821860520881391231264017566221798057847796497092098186050428414567505478745723876552319655037424533319103086555626015054726653949312596303933976491447445602956220925092122664038\
        561349571109306701518280277748892000*J12^2*I06*I03^2 + 11935492075200481875367973000281525733103990167541036104933182670704937014239608054049563325666251272096980595667201182102708464\
        54878911970403721708614514131839076298238566701281649597165675683637515284615789715882812800*J12*I12*I06*I03^2 +
        439119462172428813449737240038458350369489355338365627741031423676494904241111800408374349303559708004855536564233381626978787394849335750237992391722412987870295966012092960202233821\
        8558021827872110435423081278430556800*I12^2*I06*I03^2 + 1361242792347790680391680978018023379615780327301602975038811196813723001406470557205412267954314405131685677546978588584010060\
        178950794784752218362106438726622156952621137498082093405826475609799899123990757549263569280*J15*J09*I06*I03^2 -
        275558340435373631796304207749547993588439722830313730644092825430572037718926148707326226137222971784015441452498634449638663829581106653511407079580312721204459628482054524539641341\
        1928871890405646451770356671851284640*I15*J09*I06*I03^2 + 36087088349044129345119367734098711475908445141093783663869693061413371649117461103749302452033613615731536228130084120872877\
        4236086142793261769716313355348098433049542837870404222121163466897255530926040347297857562400*J15*I09*I06*I03^2 +
        583643370977113559677508614413313706281203255937655621561145294494419451782126834034435295467832739047166399497391922544906436349717037789944048755382874156195999496933725071054410644\
        8424870034507288914141975575768832000*I18*I06^2*I03^2 + 8110199872366436516004734775460178515345393285271086050743164168801496592072834136247267665014272301356748106102776019087819002\
        7987292948546969680994015181350636876445163582787925106000453055780879972519379455903618408640*J09^2*I06^2*I03^2 -
        279572411195479077934499667629369010208924476751345895781439905597671361462708959325637299207942212445900419155886823481769128337184086349736633282223179697227475877217245738167512025\
        06966107213860502274997647212175254080*J09*I09*I06^2*I03^2 + 80628239286073578859743142446223244820446767599589252810936012394329982323815951306960585743041531526471803465540924353022\
        14312495870133094862237748452868699031626343896403578593765392938043505190157400789753551904165427200*I12*I06^3*I03^2 -
        626761243131473884849653705241793386528787244943327975338804112067294103452057626509506724707957299787071122890911994956869812095566996582598185690309313277242506827884762969294546232\
        024719589263621426737862541471110594560000*I06^5*I03^2 + 696584111064399862641844979125652043236434963056482929309475193216824572789329875579865075604748454573056312467933019356154866\
        52287051152230294965047529495542015642800938586826192004211322724873063558008117366837825600*J15*J12*I03^3 -
        230388070989386310658559631499886262991997880116265309176975367154336949297465884231116713449202672704738027878709535189057938040241638497538832015052381236587082664868851837329940873\
        08174185341412667059212552133735700*I15*J12*I03^3 + 53454545245058086376824605708970196085494538599371331364278545983034372797580236442115144196515117241633086972588092779572022315389\
        038237608035333400840705771200456098525472750639949985413930439585335667468278492342600*I15*I12*I03^3 +
        622177478157652124478751261830105371646720768717914999246422865678936754486159006464466520848867746944756018745238122559012300784767504299460912514308019769268820458970288319725266904\
        36845409911511138493505505687104600*J18*J09*I03^3 - 13885253828790669202862209177780277951591252628136856674504383214373856584139174556946577963717916059543292923276669430680002933752\
        78608908768066675203255197361938109206772910972684115031639562928791973917277971243400*I18*J09*I03^3 +
        569108381290980732771996134714316774970181216281067197091002096295411853383779106854976579409284346377525242233265841620871482459409266518942118565031475168573251360467956740727754841\
        131504524259517171094479231165000*J09*I09^2*I03^3 - 48941963215220967098507121926371697408973255757126274060715987520658399650709363149521605923561309229244664854655721947194584582570\
        5248795842627004910957610141086505616445233948911007627574703684148699172651522247328000*J21*I06*I03^3 +
        386384006323942573987417002336009397693238578371565384963623321079874328732082575795189943243799564847079211047247793262297556139576327043963899026883182744554038665897653408981484768\
        4054993636170445147473578419212736000*I21*I06*I03^3 + 101072335563331826834118570563824817782094533794430475554234745639138330900324552598305053761486728532779047419949469172883554557\
        7871980541694870337828978338933193328810857950313289344209383236855667950277425522489854520*J12*J09*I06*I03^3 +
        291863406941118044004520115170193953265401722462806204261075031043700918409427188553994109099626230042709492879629793998852951240747811096932619676711114010461722872204295880897969692\
        0597018763828418116384027133807704960*I12*J09*I06*I03^3 - 11783114214889466242267177257093046229484297854186562199505777277958912288950698004074796802978540604997560948926309291990129\
        0394515855019925732973683015592903686237021871538584183046302237003326227145607057073800132080*I12*I09*I06*I03^3 -
        232981177362198987628025212199520325462662516037086329721886639343809715585170475537299134595644914486033885434267106319752745808498773452549810068132762762759251784071806787114438497\
        855294799558380676032646520391855308800*J15*I06^2*I03^3 + 10124643716584794798671167582410550449932858759533735580308999058540480257670239793187500227971197797191406219349282260105033\
        7512654687843993282249628297123268902174048120752919879040939281897263605004289945129496305932800*I15*I06^2*I03^3 -
        231224353825461028317935770669916734633821286223010835602435026377825907061373986319114865379837575709340374001912483915661749748303770027299755280463197013375716475130871921218286169\
        0611418689651358642513452857405582603520*J09*I06^3*I03^3 + 2490656668041668026075095263609875333308912498247493545520740352259626519218376328403048824025015249461636662572954206270418\
        249592923522475755214254480224455407802468458377930114945128390959203112726531655453307709893657600*I09*I06^3*I03^3 -
        103237398624217115225044671111145303411711180675019244712717696369017937112076875764205099232395089051307054605533980306774013314017907934362572573783566050984853207263303908459684648\
        4010504744944228933077510652514750*J12^2*I03^4 + 15844760406265746250188194040681927139431022042429625851196402791075900316575435854260385854354772431311288575999502061031818822937504\
        312020251085204793934549728093594744109526837581149522828678052681568327160452319000*J12*I12*I03^4 -
        735235787528864916176300692338499478499328363026687644872929627119649123127124835905809822873674863854196037353171392454691738886458892753775976725260931741602091561195372000416418442\
        7978304309091952112861893725093000*I12^2*I03^4 - 53942996394072413639839186205264693208943228571892997500915969726208265228084915356670956074710599980322515195817928154121030872942951\
        334013769800493841771392686338775903944718380716897929543977697027759611501399082370*J15*J09*I03^4 +
        102324556367216763535804208706205469476594836738091858393823539595534283487673156042120959626213990958766773078131193521066566622437792426575106773495310039641038126005095762217137614\
        5029928134342391127896521908789840*I15*J09*I03^4 - 698340408213146981209991320647235023001970262033366215575147749868093777515422719512288936515651306153740675312935007555596381768496\
        7463616247048831882398627371824900103580573874068168928679566167069450578403769206110*J15*I09*I03^4 -
        954373708421176504095912657272522878803624750022717118659070174938971082118848905961606250812621541258099916711805340407731353503794361651071305005831146297105812720850687704498771573\
        099923997364091292662756723274280*I15*I09*I03^4 - 4882982918627391591333098737605403863542969058067095167909015754639409668139953590465987530067495930960301024725596944885389945701898\
        12840054443366634777345554886813175318549567491619922363359363645842643164757938262000*J18*I06*I03^4 +
        384675835296457737915144175722665258941536602036909341846886843031104084131903680700309155415713677727651209002376385797738392443956856265549445138912711712515897721267433978044540738\
        827244595577833531028040277322430000*I18*I06*I03^4 - 1190270219962681103637633416175815877189270284487961998568085851461628668198877723556776313277280665463387536815820630920153334841\
        404132111819700449217327379506312489117615224967473768433601883503899638367158492036706164*J09^2*I06*I03^4 -
        341279554615343124511217651931531699361094625172380488280008528055599364148216958548737122705905010857201093365592371925437563343648153396627990733380347964730646688395049873347878154\
        33756046933429485987205773575672812*J09*I09*I06*I03^4 + 5328864468450593026801824263618111159507539038269340860449629255321808500787676919468534706106598164620835192895617858466209971\
        56040161737143811904918924717011547964502325656100436540659538566201339469904489620281120*I09^2*I06*I03^4 +
        331928517056145103804337672929140117751286628333994791316647740339173570527571720331928717291021725443497080332840367381044031619275671087220888836775676310876913596388914153880539111\
        20591470807435294564491362632643984000*J12*I06^2*I03^4 - 673032447322618378042541444501772329430023876260752094441396214961426507411451343576318453421048763215825722268325247909783266\
        96740586909680696626339165533029647736891667467358691823230828893940814374992156661660555404800*I12*I06^2*I03^4 -
        231570164176201389978696638981480059387035696224419995227062712425221066068134813462197429311056561666837098300212546792259345164204052616613077548490585075279085582990557476752507400\
        271984509500139386216207265864000*J21*I03^5 - 97027009757978729779701791968573466833127703658788154681911170442758990172520400601266023344232443107709909306296075600565782719762957083\
        0780909071023288849806462029091445123137063146833944858927614889335056174145250*J12*J09*I03^5 +
        136309322572522037261831476897882257154600303334144253625064546621096398007709665686797954167740251843175815056015686399455741286795860903870924888932046894801980384565619209482744108\
        2928414772509189931027361588323000*J12*I09*I03^5 - 200209724240031271204776998138572182781581478851692039719566020849374336678646954052083499335327981554418938235693207490866528359537\
        755950665879756197918541738687498539068048039193777996752160153335206387319766003769200*J15*I06*I03^5 +
        270550529271495934907502866841563946987934091997497895651634536809005740303370295505055757648782935772143105323633402500557660220836237477624492901928519867937159683503018176156104858\
        76387027244756206880141831775279331480*J09*I06^2*I03^5 + 228145715204518431667470922004982030052116243526838315071469694831074338953053194955222476318361027990789921744729700651124136\
        0698328794112525224168807917212436887037113328070721260772014094235311796269959650971494575*J18*I03^6 +
        101385524250170178368949640643958560968438102244198062723529366369483098656413773939463741529706254597826170070282538025330155468734063581289668009256676131353630534944637447895628039\
        0389819138268298671475270377043825*I18*I03^6 - 4932038512067503902019503237598321411987855886262464497640275806845355746109082853609460993302321853085459990235485312638401661868884284\
        88957512803342865411230536748071422625475378774087824444841493355282220676358075*J09*I09*I03^6 -
        979836058367583752901356640652095365943830652424858112502852233010756441341165951650673554798881792493713759063619624603983886356168546529692231544526830173846996609959412907472699553\
        98981562659805684312379077066975*I09^2*I03^6 + 7406374765534817164980315928145974651487362754511577311950163186681740180969732759094394597519007891819642683017265968371675229640420734\
        8092964503256001642082766032950127855151429614153939491405728448971259600305805000*I12*I06*I03^6 -
        147554195773428168861119546439672441321471624894218676342183701590148303127716945863245060456946967832943721147578875384564515664400464864644023942532614419827796716057292328540957156\
        448368057386052636879717014607391232000*I06^3*I03^6 - 350659247521976457232344268515083266720664471160569432342820045427628529891564138326888914653778474938599939454314476285016283282\
        3681068886830811069159629964818664125836231154538767927837390266962816967528615995484950*J15*I03^7 +
        258494984462476819423038340055780600151255522091336683472836753709300398276587475247138065079872266791581859027510438994745588934095102475381564211524400157880435109980324984230862380\
        547442697389069538736860970292850*I15*I03^7 + 25158623954643519268813350947579596327723094204341736992820792612433287361352323423130699682129993331309341411552948525188217715071510273\
        264462563901112370318541980930854386690116848203973910577367214073291439224989500*I09*I06*I03^7 +
        111053519426714689402426891715366911238189585900491823891346000218668177041780238496892609502134242044998436687889123156227620399966635430296434382899180824533839294804544305139759212\
        106954716427233683108385254773250*J12*I03^8 - 84213937456362352001211609006765131101618449182059350585604477179758045438686390027847714509740456728226219672315276088045151935014991173\
        034220680219957196408508614055713523882382645081695845051660955012562662563250*J09*I03^9 + 96447649354744817914600997015302258701633077435159440779062053024941049986464360998530950427\
        9343738872738405129486983808073680885347622764832356928104795469771813947369964102285592109348062865287761502469824085637000*I06*I03^10 -
        605192266945206918862887292554114185729775456315430128358780943331731055991848828397175507426387648951659550488976583454612726052290081451557421886139225326395638869167174587626561990\
        4315565672882150591541916466000*I03^12,
        -490057284986502976885719181603032605175711137474977298196086420642131345920281583841323451783342829258218077244114360344759554209609493909412271418549987264905555409340650688032521110532\
        771480970112136669292751000000*J21*I15 - 6850694719367174596905870289324716561564255260153792788467457378299361389487114044674752750156133407243874545624616954938901602683910259259138\
        918716833611605024381833068879810841974496792036389944293406065879051200000*I21*I15 + 1015637489772087720071428379500018031865229839240161764355051778173364745004277997142534409773888\
        149427152352181267282752890535117383528985732440290197284209945475841767173944204984294123964472573485711789015754512000*J12^2*I12 +
        100449908519022603379716954322121199084888923753684059841079269339712795780027550951109831981697688422694495655647994328947240978182366258626383253110179957750406126544306107573183275\
        60103604698895049442815052175792000*J12*I12^2 - 173526706298405878771182570021932204344301057013429729459607569018469900432637581362371772192459015996152671407550505355360898507414678\
        79011855478619470883134938239625622057510438706001934327111632917015747863711340000*I12^3 - 2802472915456656148928357291980947027151636267810621584464118963673645863687978336322079485\
        8244380916005780950161587149422250257858663483733571261204456270199913141947770274081815973685389564447336106072721717979716000*J15*J12*J09 -
        112017920226380807689543203536231295209907112010436924301068117234577948552485236233831953230404318146207731952064253068041591732076514539335701827541093776935693144588369870259050805\
        49535221142457228589827551275808000*I15*I12*J09 + 2106100461315458338195824044572018167382446334212787127163846169276150173317255836810285507894352975715883215544381701932847434609836\
        535820997543357429599799891318275074256355833153647323082655046827449325805687401600*J18*J09^2 -
        765747463599578078548307428670703499280141431515170438809202852957884189357941374109053363508858729786788219683011481192599812396349275243079519477248216391908479352899496812454540156\
        04991740351452623525908318633600*I18*J09^2 + 256797082893272109751453007123742045486491843297274880186523073745450096847691388775419519277022592288631009917419135633821826741772894801\
        7875621422957907426084718403554653628427264960560580441275796591099846913764000*J15*J12*I09 -
        792793702228148475643861859891454577419879975649045186595427313838507984244858873436888995919619856360567399631520627059944216105580501453948361401508294192827696601452811133729306066\
        095732333315590714109318275428000*I15*J12*I09 + 767264853262068799025444127534233688371538440966751099874585078839829181676204011899323337863265333854676251071560468757358565708894270\
        8478531965827546881616727150373030109334235311450846663656892657698179113705504000*I15*I12*I09 -
        668122878858275006059426656281107532128577551204394858443551887603773361902690932876729803199313006302397903076245442645353436357819298258926694934119576176255082995491832540658797425\
        8590707117193288220268344139555200*J18*J09*I09 + 11261309025326642117609745863750391657383325873860151727702938550905733416071943647986090100528995415476486216041877233505599441841158\
        1131151449558841215730428453613895498723121300470119786572184252541099757873417600*I18*J09*I09 +
        566771097630335227000938943507354007212127618339653492894225440645621761158043440044854992294552047563109527131868547543803041381248875240890390331162482018869474742985883689849627002\
        7512627967535015350370523278796800*J18*I09^2 + 8107280493329838906712805419327356656439005512886514096962237016503900742173767668389954339296358360518556355236704780692793612171654783\
        4928908673216855095906484513368801278739215122180393817037305411904117527699200*J09^2*I09^2 -
        162145609866596778134256108386547133128780110257730281939244740330078014843475353367799086785927167210371127104734095613855872243433095669857817346433710191812969026737602557478430244\
        360787634074610823808235055398400*J09*I09^3 + 17671233706019680480173547170637856045221646049023478908545138466231236702824097307935442147824970973947926692294158806028583700686832385\
        9134240160051711768810488334671437510979905416239456101041492782042921539526752000*I15^2*I06 +
        869482253200236200429944568294040962743249625637384026653821839036999236390096209920660001434064933020076621433906732250282938814748367248377368482651727741623535680831294810400317564\
        084014053953782933196268485658099200*J18*I12*I06 + 310694519637883375451347776833929750933381478269722836772737910682287270139363192701127133140392932037130803639611291830296428674773\
        339149019623605355447756860226174388189146086777884423236157633173212077191039705971200*I18*I12*I06 +
        595633985352804675284155826270055083663890488475547531430469327702674499097770273058175466815051150293954671855669686463002881850927474459284836953444379215754961515657554052832608407\
        46981786513003664044763285738832000*J21*J09*I06 - 1276238234234122171969630999130098847144315260464667476332772324036394076656535185297926010872053362557200969127652351315089373537321\
        381223006246079607258571524859470928460932424499365321032624905449676573823232064896000*I21*J09*I06 +
        996869976615248875583463780482543387967576430874217040419497176198771782151886143887952738020875493852810022007750767495262359445659510188622750564707989802432287858499549634950160836\
        15983462003303461208535249602174400*J12*J09^2*I06 - 89583872372844139844579971037223672847369309459362400401067001132246653460399743801609961538157990887263776077823458412044873741306\
        811474452520191125379801026404779209706703299504467363510094426967583542893342379200000*J21*I09*I06 +
        694900464655761781885294929685809285611971541096841252390104854805796954663428116970095659740436176158826490789890249239836276661092790570882777440063938746312159216298080519070979457\
        246031488218807859203403045904640000*I21*I09*I06 - 508207704768694013176702752146007021978518126343537683485943250192230738968492154778606264426255984380243755144750852360987919013808\
        06944556507008450107444109323146624336646788020730556942053943496813872532042053404800*I12*J09*I09*I06 +
        130338254645866483885562283188410311152755038038919849751725597376814859377492486893201577200406014753425552858944267573842925544651181892286100472123688850857153733529245142907704848\
        590430079080218814196928806895360000*J12*I09^2*I06 - 2632658602017408992191257193443833622331416696127796991398719463019085741668260000513294643198694611131633775608045790731868944717\
        78653141076078166537883912540920276637486427956362148878026621851546868553291481480636800*I12*I09^2*I06 +
        705027321593591021152589334952931095752881927591152927753191928107083738953560163496429937788769531315251774104677146434712553316765778037962551240870680044124742148203120719650372491\
        379707218670256693777679121221120000*J12^2*I06^2 - 148080634036241448494071717037658267945225440266252661816093358646045455980691684769921362998715702965510808730007263336125129486380\
        96954546171100652109636299963738018466132528743137067539743941876168976474179877359718400*J15*J09*I06^2 +
        663921757160827034108040080325355141447053136649664781947241106139800147307974711091258779434960444600556459825720860303629920163253821816583083683759638655756099236279371340217032132\
        2991837778587471812029936047959283200*I15*J09*I06^2 + 623110360163878863092579730685755793351398539233623678378975213649367318018281616706877564585449092679748457621946435789630230917\
        7625932907980697853660929863533356444369465140459841205218828263812160232633715743394560000*I15*I09*I06^2 -
        244147269656620760695819761131909413937021025086637959979784588920843656089878093816776618554020078353774660139566327825068051436781279482395085425627350866915888046013654377316874823\
        3948449444783476830761978265306679296000*J18*I06^3 + 6749210041629210306614945904381116220792796988785843127950310608215536242130898815481892771988825865126531576394681930334571791155\
        74748133159001370223241716641648319859314194170514000339278906801765413168986744745293824000*I18*I06^3 +
        347117462090045261499605195754650887660516677155098922216587498174120665939948904043246555774985790124254674619205109377431310167979828146773768888082412671924285439544300316993465042\
        35923902350448521390186308380379443200*J09^2*I06^3 + 7718554194213804302246721203215715043228833942709063137107944672451233562587888490296994600572032947697208083829650445274793291521\
        97942628805075040101910124944423709413375572863571448493791829991484477088159247767194572800*J09*I09*I06^3 -
        177636138460238726734311527513311479163241360738575196246495080806417962756416992837123214021392875708686302294976335308285003955800126472804033498358208416389421545915359461652781505\
        686876690932833562516567769970189056000*I09^2*I06^3 + 907697525140576548824168100333736721709726759668043656074919123192378015826476862298721083557221484391539545907512198424544861555\
        663172084171078168791853324208376038237590290774608840175119840967536644067562459137945600000*J12*I06^4 +
        884511323958614524305484225216020086254169239515064422221546247996582402192969420148378427637788188252836576799199187394816134088604253972392628007214278602935261974670921343001850744\
        62839987122299079262860379634037443584000*I12*I06^4 - 227925315478417076316654696175212719905779369275843229900548731034073831346652782964811595129976495385131180383777048802826557520\
        76734695683172066337461664778563324362294631508471448766042620021948981086060959964034400*J18*I15*I03 -
        139823440373748710738423172161673863837175764040294799108363186727302536533955670656882829394531854982663397898917693409247218228054635976445532290454720097383330343972726469803930056\
        38934464155255047890552584214400*I18*I15*I03 + 2047900877750238963354349076199884061869240487737968964325181491719512099296978747640765126955785896226119072172959859312535400679879535\
        148439300645607636968002349235741327949624460462607568008464186194882148944060000*J21*J12*I03 +
        144154635048096970056620916371033699336185092143520348842679439472847298877719170315929402720776351991292841155782046604816964375756729977469925927847970783078297179282029871950355837\
        5800441110004126329821878837760000*I21*J12*I03 - 95900772697897445994805235656181433061993787791730414831085031545499868811321717934071368122887541707259582714322442338536947732936169\
        89798335823389881393542504165027172152379156895114215291333668203272931142286968000*J21*I12*I03 +
        766378560025333556378914689966625338714360725569192956410376290928587279024877181343747815546198283566237637418281309550326674610185790745101248106397690429521154976018678774896391663\
        61415196163838076992436894268688000*I21*I12*I03 + 4509642633666732261199565913951869278770504002974252322295735546515630823368852084611065378582091776297327810351969143075465534336797\
        2539401366027757895437037785480826856265133464214286727935735416785806036834709959200*J12*I12*J09*I03 -
        759404881663481415370244768757470766720394153325937860831145865655637477436403340112373370612554036295036246521948310012202475233482947639181429925277421292726904723278102492668961222\
        64639661425226964169148782557935000*I12^2*J09*I03 - 11952376675414720864794768038096606115395153108725623329144705203284631704429111712940773469218592771828262713946008628178232155721\
        533986826356192613629857222867624371700593538852557827198289429498612074365469501439800*I15*J09^2*I03 -
        120217204924564759501632987657377306214685853233153313555949457953718899559027378097079600128271210586167317101678983160682506686505778086087878214028577318426856093924355585885860773\
        9073162615142436138141789010914000*J12^2*I09*I03 - 140014217082805828532697841649854144749314089769340981576319475892877540026196146032217491667234809995934200610061468252931835872018\
        63552044438770163308621089308519083656777424819616011784951063519226508512529861858400*J12*I12*I09*I03 +
        193651780028761813396150861784744430804326056858459074312950675200831728436241454786285169063711918991496633771372076486875004171253953390601333325134037178429296035140104851145550076\
        29575552018654720640965376724100000*I12^2*I09*I03 + 85198801624202652306874151672943872282442219106336242293985481697133476357989158533577844258306351412671760787521156047112347151188\
        42717445709370659495297455525756204968545882424735135690589188158456108892762663287600*J15*J09*I09*I03 +
        168270696919754580033653322633649652644034814923920196387700306482710933793522141740763272340307204744764537932571003194467772644741078502373786431259679340391660750813328096539711891\
        34701627502730276461949114425057000*I15*J09*I09*I03 - 278772691902776919821860629962627562683643380687484197829448537715722454418389772385958223617798847506721654940732477219177161329\
        0756827687156928030609224879756688834594542193451314185731135161827351560837778947848400*I15*I09^2*I03 -
        239491788528473657694285655150382172845219362979383344719722391920230646995622831294825883887352107629682158403972705507421974004974884637640061581566935961215418579742970986959114710\
        077097660768681325850105357619288000*I15*J12*I06*I03 + 30989131086462030346779918920714689441724202180026094875805943236693372687678505563096372771191469474426482223292826728684407956\
        91154757977920647167643298547030941979451868918203850540487666065069290184827419476469819200*J15*I12*I06*I03 +
        216024832718917290148488984632750368434799365866542600756498948141512505957392728703020781246992827363466834587124015315226126201955156941792828694962485824419538807694151801754251697\
        2022634352358875730902291720859550400*I15*I12*I06*I03 + 5375771938263313248633590738945985603172018874904423898111830299816324098439588232980245469359598018987739535502598264734588131\
        1673021158171507112903640696111237555971513512246781481806086368290850237878516121914225600*J18*J09*I06*I03 +
        471777889179815340843765450052874080580276939768370639161676753353845653390326084281697394834847471845691778359989502476017088534396673480522577526635457307750724121477284042238700439\
        541240784604554976288257375826121600*I18*J09*I06*I03 - 24204527804710368136290847890941072329580350960764015030786026899082152174975216207191338263021500702048427176720011034783674903\
        816534043273030996287073077275798726177450614134764936235512538845451564640344786053703280*J09^3*I06*I03 +
        371250854480356251004014394789391304655774045188841512167311581481337107884410425936127060305019558221404682691778580282086238293445693566441542564894912432625159932431164356118509926\
        266739056190604381845302468804038400*J18*I09*I06*I03 - 27463567991440646846185843236365581701404794222570951747692992610529429728939425145666969191114808149168486630506138286062551835\
        8423932985213747312960366358385665357653316704018755879067259556019621230278269748300857600*I18*I09*I06*I03 -
        134446293806079453389643329839023936289011336735980068679955528394821508992354531813606258851050393412239207484415977064404614394537075512534084991433445021667511021718685970176764606\
        906986927775762773298695695586885840*J09^2*I09*I06*I03 - 346195633539300988060716425459575940670154197560778792884881827575754781227574468569261473667578276124507591449445341249089816\
        84942099386436640535109196302821326236912583870183877698606405784863716024915031793308359200*J09*I09^2*I06*I03 -
        123681567482380220139686660554587639738723250487326070378974786792239068482930161104084195901392990762840316173626699327193561607698450258393924831481648716039717367863509559057163218\
        49942155688702838563287170425926400*I09^3*I06*I03 - 23429592354566895998123212159150170312613388400177424595317177762397969046604128247207917076363671665947213472788237535667944957745\
        565205837583085174574951934640293277779539480026026487797024156620785124688258353287680000*I21*I06^2*I03 -
        110790928167751210944881951392164835484333967307591171525772524739823015482016243121451929079573628631836937534287931060657001711141650737190527026753302365577442507843117253955863550\
        81637813929826924959424110371510518400*J12*J09*I06^2*I03 - 1440562436267503007145113591121893799804463987093955603696559668472580291375710755141986869860213930214501496065359618813056\
        516555219585651974074643873613146028934653110944850044029751408436523046732359004921178028992000*J12*I09*I06^2*I03 +
        742665215454227551405199122131877566479926950838962473822640242468596693525532066625050962222579063572586616222483089577874131584331666522413249522785071664799693759889617067906225149\
        3170084755498037935545483815327283200*I12*I09*I06^2*I03 + 10255664185093507644914866374555498916371424719293547633031645437965450427637622081354548673724662297638303586631903695137043\
        8313714167083180846331936831948722902563032242858336689931594949249357266553391066485607100928000*J15*I06^3*I03 +
        750281933473731663905862586423037979809869093350403903091665017360547064209572349449358042144671413373121535763647188150231217329719448801501823569482654791942609536770423639013714736\
        3202326413866263457259835642189329766400*J09*I06^4*I03 + 449935304333988712972066952519063347853235217521762761692659007297749411864928140572690060574002548900237466606234099447356858\
        34950020015319183330781324257367910957368691948366172225331636304704862575825777251172772000*J15*I15*I03^2 -
        248494049457673079158885286215526521872890794185365250840112925149660196112911608237289294180236247459128381031171809966550781748232680465689921255745886344539435378623779897848282664\
        95450395827777149769523360004931200*J18*J12*I03^2 - 53177601740770162591660902097698098862199984007305379966067695592699112917257047234171967827522131534984737868888237218649926491218\
        0801366130423677082618931215395118381847066907807077762372876150297040853506227845200*I18*J12*I03^2 +
        134158327590007829044260596012824698575995389930630027728117458739249014228038731318204306900282597425066656951480773156074294378508195700219277480139872651949660784661771845295339974\
        16151403036725139531113380267895400*J18*I12*I03^2 + 68596800665389886788766299439539832511994074032832192947700690231225664748465740400204430234817876110591173764736374288252041139189\
        42913959413507930623990513681899266462881582633720574085826369651613367804924601417400*I18*I12*I03^2 -
        503948840864476077289310797278729614209245509201445180410929520142348537331758154389900349492116834914790696109750814747504525078992765734717132942634886908768351519166654300641662137\
        906136877098657356203147949832000*J21*J09*I03^2 - 2324425902367524587000233704749344464228675545923581180095726138751809389975734112949197210223993498510205436400608271478118442429621\
        337519128447012414716674995012648370316832152715325859885492819061158368913951527300*J12*J09^2*I03^2 -
        221644463014138208028326855448774713276596272992619620881164206057199291773659155206719090011098466199247482840409643285786270323143231800274015834763216243095019803564535074248531723\
        66114127279348268170817444238340200*I12*J09^2*I03^2 + 971261645141768312573921305182693515987649835931208559800514369917922061889371988967681650808337574955243425276552280414638456193\
        054673562838643934307879529260571026982553349977562182911452193976947770341844350828000*J21*I09*I03^2 -
        136936206862294510666491112554968553394818263088385636797300131630240113166894764678116477921113050154936980937165659551874239444058762387823565643376444423365879268734301968051504687\
        85308651128068670136332172524192000*I21*I09*I03^2 + 11072646252042976824701371982131627168852599574087794439027066970753860686444963143232238259645649680216524478995139789871459086157\
        07874809800191226336431383027239691739253735067170538631645745233511686946743789882700*J12*J09*I09*I03^2 -
        118314081378741456565223105287474857297569145726407119146683645877582592601872387684016421190748233543290717225033418158724963914654043611306031421694249990226027354176678836368325921\
        643820874351899538004800072818200*J12*I09^2*I03^2 - 11370012749895819717418628552861733478510141276984811552269283383975553610450093605271723327683881030935145823256473737049596584158\
        06312540378738992062155397643779877933055660812214298541046010926739765819128069398200*I12*I09^2*I03^2 -
        668331527316748546915859305209596590623286281997378660074957324518947009332063025766379705484678533985397972967782767073818795382335398632324682252778623833154623656705749982801531562\
        40432848883613472241098380170588000*J12^2*I06*I03^2 - 661977987373306999819478491267802538550350705877720030418407135049043963518398127163801423985610641954247315040078970953883718486\
        512744629575978310561681718658747000462064897168116476607644937563312436232732999560344800*J12*I12*I06*I03^2 +
        238161211734737316560905200324161487973691563099521595114588584188080967063325241070401874483797501991618124318623534856466980094600827654648499733228041680195713737125752360606810887\
        6646653551064676214171124833098971200*I12^2*I06*I03^2 + 3919069002398474723306498071000851333994346862466971205086505407424186512282844311774003979751348966719080613845241898771508063\
        40419991697761859275352551602634722520327239268134471217706644509275219752901141286498352320*J15*J09*I06*I03^2 -
        555994741034871864157685324986561383500358416478201024183927323650442889827455488434041827020288637916429040488795529278904481234018399562047823044063992890310297986516159074607221765\
        104264043020468678094032472323528160*I15*J09*I06*I03^2 - 426746681231775111180262397785271819320543833525008403836818710789895420094719593831952568082074853816199786787426914234286211\
        632599386444570438501814338126752177526300385717640174539818314754642341694096889473445586400*J15*I09*I06*I03^2 +
        755057322709010221571677592123461457854734361048983309496681088880745461585446252023430385127265112116031387818168664302213345126861417340562912147032019451438795394095623032789123293\
        8711446048203905657553974916901888000*I18*I06^2*I03^2 + 1981627656572664058936049681377139533619638579796312961150086099615850042098885420622063173013692705173052410151350479351547780\
        1515834646272079677767397016201764596725026612452736984421831278719908891448068882487927812160*J09^2*I06^2*I03^2 -
        640572549381532192953921853463215147095252269540484818634033756650759705448989281883993387648611185344420766111366883998298349262070065396291038547561928567579581049197022602388833102\
        8772466783261737793815107222963363520*J09*I09*I06^2*I03^2 + 222901226460863051596383606543024334313569063132844858744494320043320287202307420510996143431133352008787302727756272003143\
        4267104023161276348694321383364396025631753049765128962487533021951884168277017384704170370432844800*I12*I06^3*I03^2 -
        125378643382695765978468032902447705432850422493108602441980618694902606399847162001390401633043890278352370888491036499070393642516303181261649374613838524113459782919726461847822526\
        588526247415535504753277499026236702720000*I06^5*I03^2 + 200636742731955050187069349480465619724745278469762885348471525695195066097866073599681477809669955643585349214690608400835809\
        28052149459018988877131179173461551234117766495286011384676531005403851885179928743958015400*J15*J12*I03^3 -
        724446924258234014533509607939214250688213993975188166901432536981256893511225402965987721198828467570582901636743982184427803889555884527344901815896214019012144941804432651713827841\
        6656810606264804599971476054376300*I15*J12*I03^3 + 214471746467564445882914882882341851215819716288088308343934333796323571778193449031978126744159272428578466373334679560016525072513\
        61818902095837393955683519277304410900606353039583685909353491312815758287143573763400*I15*I12*I03^3 +
        236855914224064022195067336347609807957173322894115946086874771628000831673639207288900987136547102591978644746932445229734938745610144127954397978346715253991831233984760229297833825\
        92891525961114373196971452074734400*J18*J09*I03^3 - 44997296773987660768201314560059736180865884091805644333571763358115411256472642322344808055256264298337785328366435953373664226613\
        6886503374562298489553943858585808032038166434349122598694016979457286253728588287600*I18*J09*I03^3 +
        970100218767307568788953314332227464553852074432772631712670297135280193152047665688576267564614756319457330230493533937316559091771812526937076169803704136599047370051169290735337650\
        480187250814901221536911495705000*J09*I09^2*I03^3 - 27979777402277193816948066270930769854549376035986683669287698168251716255724678554387864873256637636469516206869204137099555826273\
        1651149048021593711310679115203064325984214124968164535838911671382144271756476621472000*J21*I06*I03^3 +
        208190981020408653444102145351853148157076344676539611808347265887651105251698136620689632555614430765716280824788872063155963555081035379560818238969731571789127551948012814850727598\
        4940607134101631591899498635246944000*I21*I06*I03^3 + 940322183559033364435504784836137400083329674814982798806516094071841512089437434908335823759546645273052581596610556611963035671\
        972621289747484156495999087299302102320403932053218878367550142691413061026493458744895880*J12*J09*I06*I03^3 -
        303676495904161520886006815067764621442136410990779606746458148403870245700169931372917214564833524698954267716858046522849118261792491566133792761758761904449920448210958374469950297\
        842323988165184344745609098583598160*I12*J09*I06*I03^3 - 358867661441102476376531202209400779917144520517113869428695322702911333174499206287533603725219058563852896262107956038002629\
        03017390158666146385871345074059685888589227130251278649178674619077419480361725771957342720*I12*I09*I06*I03^3 -
        107240798714579613501926119360685078926301664510175872189668218800396606627894356744274212961983375135311720379953409924658742906996807829753800957410401561032292694479488731793610360\
        030196912100641028450090983520485427200*J15*I06^2*I03^3 + 21623857456323809052573819779207951548309816207832815898188690412500131130272706759103702350385550205049367635478854797637206\
        325605522625692509386543700888385576750880840677532043549555727028188018194613394143032290419200*I15*I06^2*I03^3 -
        861874547833139069832616879736785064667542130091030282273527173136540430975062139595886752874642228529587357552939529866049607953863404812571590371943206101445323415688066822949407089\
        866360448969359628401030993633209754880*J09*I06^3*I03^3 + 11705285623309313650076553263739828445327820169003055445776189910087151914825300360792194044115738200459851497922785447966724\
        46527909710470115380487443821894559914981526785069409285526882686522361140737436475040082501350400*I09*I06^3*I03^3 -
        205358148507159999020329918596147448625677767632554310643140310518133557237395727776467301793950861929935899075643704174041684771087311505784591799682382264723138208607215130804846767\
        064483803977016593282484239220250*J12^2*I03^4 + 359054035689007928540113201964155446772169737716121118644782041267024473425286232179403580377149625507744379889713702546852174114001251\
        5046232377842075427808128950236756154578714717325680066924922010796932559025121000*J12*I12*I03^4 -
        258949889240822034494845933720083295395027835502453295376238697446961846745674311967342887041274595142992906782054943661556774833787456663329193599541797143448492248319530642960238150\
        9344525969187346496374180823297000*I12^2*I03^4 - 20270861049263577909019653041702184283932070150564365974836291832551027289823864432066302562253889391839079477600959138056287365122157\
        606201323060002741934858476234580931522534343099584434529877440647346555804908233630*J15*J09*I03^4 +
        163801988014481895571165378563015657215421023406320356762898865991361944484871529029296067568468354829610523637423736004352693984671749389669859907908849509179045873354703044772404191\
        7376049627458507492264642195453460*I15*J09*I03^4 - 303607920656814909625426295701708888252238568974361906716997777294244524038179880075283069026286878558730829645823050791969295391474\
        2145796215788082519326653896956824443533986122646368701767304606152933034204288819890*J15*I09*I03^4 -
        815160479528996100630258534339175124896359164750348047888516274565345305455913155161376571154431232348852451884441525009717573683308623157901501394630779200858351781945359317727936608\
        073587259183741190810142896849820*I15*I09*I03^4 - 1401600207177655210557996823346748663775068235457403518410278421082213800603299081816222351875237741811026650130624625253620879991976\
        32985367649659768468853227774696950785126959048218556521406869637312046302582384786000*J18*I06*I03^4 +
        183256229280124420417613961791898471074245775941865994055017314097438856802377153056208644992635301976116861245839372019399926873411966079223646623578107138995441881480222579287076908\
        354808890153519567577712201537682000*I18*I06*I03^4 - 6758252032714205360282641082574973532684801462593123655937771979354426714448577903343601937212277588697180825218976747094100421121\
        28155594187674599575002061933215292716923013484876967804818110433155286272489260898882916*J09^2*I06*I03^4 -
        343163420546034976129590424841520508115932224338282821042396993505668116975792969492589643729230949341184885676053935926305863905321531055718766424440095381352734852884478613096431161\
        77583847319865641667451785559952228*J09*I09*I06*I03^4 - 3158932317885562413240226891287394496001901735099315721753923202487867273816656536993147057141243236109274012195575761387539568\
        0174931619333600587185798254248759099625846856555210237044075718258182899215987656610052920*I09^2*I06*I03^4 +
        118063031234111046162563265289250283281580838361387580496315351008097537415400046489154480697244454271770197442653227215864596154115168342804492983438039892118426413853697518202241823\
        90713514417120414135673386412207376000*J12*I06^2*I03^4 - 258618262721489635986541661307150760588598324681461238442378429401470215541084392051411369053335817098225753808831293118820370\
        98213608029510579065392636723927403409235771630860088323672106075739381779357290684232571463200*I12*I06^2*I03^4 -
        960573098439097965754109449155241538771500942243036239915847975925767134082974661447153348531880092252672283178832169405921981901726402537958756466868365835425642720283024395885878792\
        77305533935077449118812983696000*J21*I03^5 - 323109777219350069423110329540393145326941513151984800583760910155269194407191214978956276305067716511216839073182592487472562762042449133\
        956028342747715306758844719089574263097768940956142352118444145740516580707750*J12*J09*I03^5 +
        484786681860853998328843468100924470359142899341998016700979347476919266467878786023750384002316089661517170895470185703542723620838572145190369039627568190440410363333411294696246174\
        528613540780506807559085822225500*J12*I09*I03^5 - 8959269854567907159862123253992737196312513906339247125778821206464878296279990689888145567485148632654140253769956841275813919335812\
        2999795365166535828625124449583115839862899455270882206475372318654699044294470682800*J15*I06*I03^5 +
        136751803250491425168899794856244892361895369981747417420090802993962835093493361645152777994015912504360507009127612947308669775181981668682627955783172952817817831193688673631722246\
        96728175559776521486625043555707108120*J09*I06^2*I03^5 + 864910031558159917261401854006998076775910351520461672126064895860566265192067221839167253464505494251048675109849043940300883\
        033280145436746534896783623759414916143343937929309172933864606064618604579772077972232175*J18*I03^6 +
        468674448149768589558073952945330011725246416256875100581106547080037862660036931254085442363898627579143319026849596976124960474491120424591729661504742453749105051939409974334638053\
        312258260064310917128615849885425*I18*I03^6 - 24814025668770653153818183490805379773142745507310413338075578013574476132653358798515342059125890620443564250679234605484193528078456263\
        4086281391654403083582470762696100806568138086129742943160025242401355288837175*J09*I09*I03^6 -
        677708125820992521764733646154376722543043427088770702275330413025378258083009108532664282232905302884766659267674557561531147250024881183830111949201555956850413436576994892942433144\
        90844198431130413502139089838775*I09^2*I03^6 + 1039244329587233243585928032373019811841369145081150004955758587717563151363881023559320852302405393279055325548241790204994799779969244\
        2318264401147659888203329136803900616280336657729950699582884876432048320296385000*I12*I06*I03^6 -
        339188089842444361216442548678289864342700709818534306377457241327557218672767566596602082526335930529852432334040440212559649064205135235894102681315530402458484665808722281808113803\
        47158075495084754987531025145968128000*I06^3*I03^6 - 1232424348109012828184861436828173230247484284908568793823140706093089275295406055705001220551017300983264173699407745060432590874\
        248253775290255576980115720478141439845055193433679861051512717457477685275267679056550*J15*I03^7 +
        236465681557523636807642517069179637825924366297682351870414985808189768985116281175136880411207636690555134351219639452569053408713330011670456422298123354651721845000608077103859426\
        922397077839979644553014428551650*I15*I03^7 + 10167309121190068248393632508019178573102841123566557426627207587302746840185272442814724868324743760059798317699406476495867040993936755\
        279885366264281454358269388958740672641782879398032613476272465795602052940615500*I09*I06*I03^7 +
        245859632598155856240788798879956224866687785780625669711328129537995547045083330561402056356894204171822574777449180836210994134123380742409041457007254929033839109493297038132427789\
        26028219557141299910892511469250*J12*I03^8 - 203781863263679159606095110989280870187366643951883515791458985227364708578457434589818465503991229973478909278183004587678007829550036551\
        80733140436216484066718925316831625527482584300035815800219490483938753299250*J09*I03^9 + 396344961723351824096527800714971934881713992907063870278283757413004802228792242985604385617\
        627807166372720399261934666553289861007444361857506861478177009966485053369977459112227135159517277312805658839931606933000*I06*I03^10 -
        155857242515039992296666402146487224711895441648034740755057240043689708114150404146526662997380488331975921421896719555766352885176829463740105550608405482333857208921556767452434475\
        5791176354893843975687339794000*I03^12,
        6842758368907990403992019867391541335519639497043292111965593862282780117318355561893082803021315774554841525094574047626753591094187049345020274786493664670000571010285370002654504550997\
        579151711487745338762362006400000*I21*J15 - 8154461556158498884811862625759348010189864148572700090705505720834751214485443034983321019270629421758974994273921137623568226155648604844\
        9505955213745626015583946607744750585412594544668045224885359542170015773000000*J21*I15 + 295828455676155837002353026309150989020861910783763839210601970681101552946440600292177197474\
        0456508445382870081138083916357746434010024984231744539244023110452084912587026913001298868475082020821752179894309444520000000*I21*I15 +
        884681935515728233068156709493224316825114411077116393661581907028577776459687715805507354659315556224768623449926897963725737762143277454627196845431994868987750456915706394706982239\
        50668358557767687523278164412528000*J12^2*I12 - 480325521939114292841388724591221230317588388139695282532988529500996206853220293849297058317675924732822918372080470428557024082438094\
        8321402282699412883268335338203669378227185299690376266861810913951067097651816752000*J12*I12^2 +
        700582939359567554018049560923234298347817507960307804942097201343351310309487467168321671996679287084177083530497350438651707024008918505481230475889712605698076345269803340196887853\
        1675396485961393629673270607796940000*I12^3 + 18076859664955445090988131302590981301064333519961855328302592046142490262843307332999202091849967494649146964041671607037545920571684849\
        57266690813555710280463143902273019734932213703065518817224321466425942385087476000*J15*J12*J09 +
        563134227866447502486350131136380021532228432928388631618806218467257048975859945501236453473181749985057143853448160547664903364979919021602639445250940289071886764666178829160607970\
        5860627115724774178183048283253408000*I15*I12*J09 + 34559881093126955910486699612659964222563329356980108726077801249631752781353293945647751662299056915081178657001959753663630305849\
        9371660678562318572619482394639049777169495481092623962933802367501651717420482284470400*J18*J09^2 -
        346537837504353801135710989193143169213159449937905739825129395863959963334090130645356884366761872181139643401749114235039724771284335949478923513967967305069867815327196301697097184\
        73510046866793752520742663979126400*I18*J09^2 + 637669468664737050414507235535873162345895044009520899669610178068718632584616579013362254417438528989404138786648682683162653454247603\
        165733659367482567537930986041694915966668751878777716845753744752503226149502796000*J15*J12*I09 +
        417450067852472331867683398779702327022017517733166105984500067899740795484845292259491197134567843022195313193879898270653317888036669497831825217406290163129653960462801950420507757\
        983479835050924883213875395516148000*I15*J12*I09 - 370006850987419426933860416396156479168996454285770030638702734888884347622698146509445805949144615491953144647497763135235022133911\
        6168475777881299065750165215279563341388581076132321253595100577684151393651632483744000*I15*I12*I09 -
        656009609922264677858434519428684031440399041705338659970367697003126416872138049389774270631324769198112541687806538511014318162382557898893728785685418525708505211758840014774551832\
        058736673655827656863296618808796800*J18*J09*I09 + 579056201347622361697251217797334301894710985780661082553023857920124637356367513207943319844116924941075679615583288456235683450009\
        64519367067129075513654931274794203118746551081244583707016821155126748927843657718400*I18*J09*I09 +
        134859028709404552330908423411083159735159154502743685672646224875014243251407287502625282771619536751144430033781578900402203057373877224590124624005795631327032063930771295814820630\
        805373522265431516122946025889331200*J18*I09^2 + 22803894732217048114834152117790407306321582819030079419446986761559057862362549616554089777881363884240721437582988002768753218511805\
        341057435147436159612165397537724641027576676384726626153824864756585114968601068800*J09^2*I09^2 -
        456077894644340962296683042355808146126431656380601588388939735231181157247250992331081795557627277684814428751659760055375064370236106821148702948723192243307950754492820551533527694\
        53252307649729513170229937202137600*J09*I09^3 - 323784441974017288451830107265609154833283642677635475570521840254370325267105710759998901271769094899837837723917355349196905571512869\
        69196214608918768433625540210644992371225918316249502410381645896038606297460236512000*I15^2*I06 -
        891839600516147516718424385314594252546432566873604586511228555455482688852555441664969818385598009935276970085288215630159935407382509188020569421407917208181977785448957066197932608\
        50623644947272669181094908516968115200*J18*I12*I06 - 1312682465327315663007023140807254641134771799525898394859635718740933974534608344982080181843944757261662122292780706897767457686\
        74264367222433075408725336146747320011290095537411571592907739463473153288682086209466547200*I18*I12*I06 +
        134552507680880575457789298161310515259890597561160075657716752320752302529501568138823040498472389697350334442660211771487299157839954083373127790570314768056892059838848437439885807\
        59675142741718275936251719679670448000*J21*J09*I06 - 1705040314074578555333982657274599520459822789674287593581947335203000972046125592997902368999098868186843133098223902225734436616\
        10145526827414731118677194791548647528657292413985446899666342821991817099531479330159744000*I21*J09*I06 -
        248062276578090637673543407915934518121760122799612972960189045494264511106525562185683936250960384756320920354357115637709955630935190039813808477164121422430236481790119341045173278\
        45025085462300562536032742666583358400*J12*J09^2*I06 - 65857661971204073518480638213952861289009024824946827820177205669720260867157550304900828448563622154112108330314303723148541968\
        88746229557515593449897222939839669143312316958085690085681303238577539490478557429393600000*J21*I09*I06 +
        769577507938296361050269117762341780250337722327607350027614198016476448067562169310699063567380084853416234263829935693219121276919930219693876753832468559995324561500051037239620738\
        02920581675420160507980211863765760000*I21*I09*I06 + 1143940288398859004722355696776581872171266385157239730719098776845905116650311065901374967536011088892817340249963136016178945119\
        22688637657923576462608856318015897209482107766080109204106041423340974724846243034757020800*I12*J09*I09*I06 -
        239718274098214007704297166179120112592460033665292013838559904379701647249691722830207893981233457458300824715994258228718232625473830935714730847851282051347736122169072927627916556\
        18674051763678198708175929555345731200*I12*I09^2*I06 - 71403822029272409103628232177396906633691739639282397091699672664105295666212609994997997154213681605624192369761685813616936079\
        773499824182137245213915926074022938194171707816236209998802819741301430216882723367493120000*J12^2*I06^2 -
        650431919467663586934214241350131282878839396851647353744320810191546266161762080924309253270639361480414333216373481161863180941816628028428516111074851678475809534533437190254222275\
        5551508054418998200443690469926642457600*J15*J09*I06^2 + 208964308544762857748325683747321652207723969491358683511504280713111217535497411580279878037881491726903356902415088007296356\
        2788085207523938912655746901892375393573363268221929666421961507654767244075843949398564147084800*I15*J09*I06^2 -
        268334999299309962081942305643151159819214056107053710097542130996462769821937231189524606523037789946804327704538798459750563634063282430790674526137221723794980852811951184424029276\
        1780137729084727200843989731740079360000*I15*I09*I06^2 + 350904527224419146900751893864798850222959448629797888068540462195434666274778033679251408553660125266006256406453128044014939\
        795774177733874799987269960536081530234669123466621682559431838781709011458912463604274305330176000*J18*I06^3 -
        722468083825427533689067886753493088775944373042488792984238002209432835281460225215629792527819368263205211726171131233915319530420201116976252876919359574319716762732357424269340205\
        02755634196229981725852178611150060544000*I18*I06^3 + 742141719929517517366377717506414411959271454328844511862316890962865982608285964646135025684497315207416663044758669200885797970\
        46216504992109114660890923340197361626562694023890581034229258421849637938021405321965255884800*J09^2*I06^3 -
        841471737522365942072298417874336668904125007457962720464068301251813297549080310882871496878754770129895382611998291697220642614143581089064639803709551121377660506757729101539026288\
        68219462091832195160476653819192212940800*J09*I09*I06^3 + 32534902748200609775374577363872674345448263059908101243497388922329847884724840510656755075436254716434820412317603161477328\
        575064881366595493747298676798651271558594163514892363673732926805730014702177471445073388278016000*I09^2*I06^3 -
        135041372549741600259910155469774843239207615186050955190845228216654351785353106007916700133600048632774228205574190087911100134764640582199019289143593212320041100190666676689642615\
        155542690969845314731270358981335347200000*J12*I06^4 - 18752164019750875107992819094882749937766535148392036080900200665751967380128239277104078234110432061609927212315884597096428257\
        197065555902567725311337725962460909471654940305143848329747659112183306841809921768605288827904000*I12*I06^4 +
        374221227146953053977659051046545027679007131472726840852602020293530750250063799768239355368423622944374896381684188072427580293889520091410650687877709911749567818996897840173179337\
        3394636137784289643444705773637074400*J18*I15*I03 - 14562035322451688594847912125647181435750070712319696680243306681326120886774785569930086665556098067008054514410956662179321751389\
        2246366934956795320951152896228827096148890697185086534887706975119026775859596418345600*I18*I15*I03 -
        310821814573093511764722745708631840198404051135974128051933709155161022739835614875454132365859979836283118323318844342052594804789669438037749435940201603403370100784523062006889386\
        873203702215933536802313039669260000*J21*J12*I03 - 165985217668534196853209918514976495887744678719412794756589979069150190667646656684198300422100487637181287820652936418736052709874\
        2252777230923704463132562946107680187294171968523894171765177182705591975914954333760000*I21*J12*I03 +
        443125984006827529398887819936890952058871646975146579760603196063778702838142078563543628977649625084157608937514097365542245019474666783313416816090602364785921786261332079981548655\
        1321849374541833439946416925099768000*J21*I12*I03 - 34582302582125107637732587915148714957668569950784935770001473976156021081348876840647860010221371252161508095790248675104893550626\
        025813563271191378655736805510595963855311038499272874116926858977779903268685930510288000*I21*I12*I03 -
        150811479941697338586781249347932902771336422422745131010937017199344370324836555018428159635280139567849313199107730437043735671299552995446395140892065354359036480210818109979925607\
        22793034910557849651077128909809351200*J12*I12*J09*I03 + 249867976048891706768993876188451208765785212734833285531086462412019160477291960433009943000872860152827397756625326672133593\
        87842265568538206748483186823642382152971301370444692517798277474603588066962531868898318531000*I12^2*J09*I03 +
        967714893924271665238194530401562722168759592828084047579630882512163579766095139851022464662436270978282531858735072372397538931478608238334887887997975332187118331672506821700829132\
        798836607145955995589134511219523800*I15*J09^2*I03 + 3081545299594869081384927695365880104750211387073583156691153260983842311815778288334059427348598579201778282409643379766384883553\
        57306029051968758254130694268509213526768861410085720525437340252773515102403658704874000*J12^2*I09*I03 +
        100633445783843013068757548655352932178909506330994777576769558524862061529478655981158616274424413770364486726316629260986902077018275914736196835572650955075580939631976022727450979\
        9198596456294642534312097594348626400*J12*I12*I09*I03 - 7581432307568575594116632382065727893339254137608707726680358225270795383152176368873583028695622384536946282501031397181828251\
        89835121567951060959555132704057428699487642899247823647637925857564466665047286942819668000*I12^2*I09*I03 -
        118843043584923675619226333009037245558047882321465747433713107779349610191353853413914874576135389438460253662322687781377859400437986534596764089355668845064295690206017513324304722\
        3587092936439891506386433707470263600*J15*J09*I09*I03 - 2365744588378728618110055980431755946213556438839403192594342389914038702331843603677887336142840726983373677643265097214055518\
        102430134071975368270987676643430423595364384515959712391926357741559306712920834229007845000*I15*J09*I09*I03 +
        302796503932080917072103928240543281294603810488641565198533933667131406810677945163706728979164860971790974102730727140975164424060282023675144335702739795924776539821333370499478483\
        748409117453067342867895124536544400*I15*I09^2*I03 + 2734371685827813445021942400495677060216087167673842837893212200048056302358749315592894135885030534192692450983959883602759808404\
        5347832077191874025357198764484335110596208839744190080635735399524817907877440003016568000*I15*J12*I06*I03 -
        218670192547483546121950029537918980584273853619660680350976744346568356512091253939964827230033200036621546598525886041542159205575526395916445979460194474140254684478660454267511089\
        034656107839416850373259948283066187200*J15*I12*I06*I03 - 30584004748782622191313905815262881134440699441788529748282342748306107734452268231204341234657763137419487313029281641127283\
        1620268023014750244435169536080893084976705258646707160989203703300975583291449383052336262126400*I15*I12*I06*I03 +
        470090102512615822422246694435049017456101996638375721155827059340415905281348103155082168113394672870757090306640815248215990633740421471646694861663513380757100896247978103864604993\
        41477772952425674914267393532848014400*J18*J09*I06*I03 - 616689096837891681969507359841080032745706296354147437654083863671620056659660851435521361074446666655722529428551445722273901\
        62626671551452308723124451350892389894781976718564762267844122950293234173452192109743297353600*I18*J09*I06*I03 +
        863538013063527482448012134997929681208004190435013896057689717422329433249237441830002053259524277197766412829032585809088002530119645784180603962796996497062331285523529143903588254\
        51846439755095362381381394944219124080*J09^3*I06*I03 + 14369572966114811707605758072308023211271570853543589657054632449766090133205817992036562077465267754970126218868575181230737127\
        4278670916484647727278024805727869939099094313279864878316245979856926015970462093912970137600*J18*I09*I06*I03 +
        194622450538356538331340963126924838639909336408025558148975214674060863461210913326169562909022385568518681255983860409224374276452467463703707231823403166611725830557177606659204937\
        61733806150226617925438266815485337600*I18*I09*I06*I03 - 482827327560181460953722706557873275956887268245572239718464634955883597373636616460788543240686823262806771826566462155989260\
        94048870300412493230842611054214380329899773094730851653702978489334074174354968824431644099760*J09^2*I09*I06*I03 -
        947607647027907919752336237593471588686588126938727450303626746791127077818184154562273057785451010638188970702467853515223111373557863279175222474503423844022385464242333640106532517\
        7884717263790403835098729919182440800*J09*I09^2*I06*I03 - 45348068319864178102022273128086454041531061569248896576136990511669863074874768363845837382188073479901608725702986560139034\
        106154487418604318773405937283971624274398868634312127272387821668590475751561509599223193600*I09^3*I06*I03 +
        102231876377365592561617791817316348577141650689813166082253379434146270102836546118738328250456950591329587633477456198062151915386123058826256275955600218011097646035222333470151189\
        22270096060213963755865334424272724480000*I21*I06^2*I03 - 71908378308352460419828083336361852451501188873016917872906936388775147946466238037005067725074897521837995602682508272729804\
        3656768882177167667794406766342881308944008769959988351469729824075681739037289913085590959817600*J12*J09*I06^2*I03 +
        201687806292237013429175471267415454593445410099885994909924553799112953821578529259166046511663002503214567103560347137300124497536532698443476297201633368479936953871728346967463362\
        2392937799603381856145173910618757952000*J12*I09*I06^2*I03 - 19923013304525962938770773972399389926485522267961130282181120397976458707246274898279150728136257017454856914971959523183\
        010247230302952481638655012736473762686652442685807701053884717416645172660993875578408569852141299200*I12*I09*I06^2*I03 +
        265169325431446240885398995634016836167442114307973580688226739686113390040406652960694482471128386366907328272858107802196765073657096828724198823597198350670765110477326710565445060\
        036035795434022552062350054162139018752000*J15*I06^3*I03 - 5827195437528687245504051714259609029732112425158171709142381785038850109234069668885448733555066221099815241750336400600217\
        516862298575343460043124170720847408711315701504944348177895619561842405947248002710175968722635110400*J09*I06^4*I03 -
        870715389902631025984401628595382193659036618515192637397623471165446485421675381807878243686080530939313274686257811944671752993917064955611576488814103025191054458410466454193970879\
        1423889265263992091124684181948372000*J15*I15*I03^2 + 462911954356029973023509546990368599677634001821239998821937175926802369837100643097761790765219443950494690989697656195445263369\
        2490369272302334340985101044734429558812045013434388092250163808776188896488411099475987200*J18*J12*I03^2 -
        105297264333373734472338726721826891264927678559943446298524768672473651215143966989631180112503256059972477000703436006951629949499108302393009159397974356721387166208629065749066670\
        968049972373072316748754482404978800*I18*J12*I03^2 - 2929724345017081107572985790352127625215144681632151636853894631587612583942958042552627918300350112687139089607854519685855438472\
        563688390534844223355392573526373031052631732871446399785997021246775210188558340202927400*J18*I12*I03^2 -
        115118637022381627020329669129989329731507476950083378224519596575702217564056684201492695986742413035838035194082895115333359526806741571928560750436290369306227356434670477638824953\
        3509992109108969250874299456114609400*I18*I12*I03^2 + 325710780286605944677156306942333421558917937324849276002273404269332859285009682567364942276783661016465746425666562465354636295\
        40587393375011470217017830126033271131974884893652849391608672556104168942463981425272000*J21*J09*I03^2 +
        163407455336209343608181078894494616663271514379396728067429508788935621584192443167219166443129863647787582634934621026031799430423652347013073182174171536298171599731084615022374040\
        355495113292470092558195545421309300*J12*J09^2*I03^2 + 10852423551246814714232972613484527357248846190609260218669473844971441842734048706469116517858743412947042265172596551491818703\
        303907328992246282445022498654440789465715749401866288106725279666743269856236717872398273000*I12*J09^2*I03^2 -
        202508708040665847253323501735653107538275831048212488930362188322069820523265488124125220157124530057718746019779865731550004593645752864468559882744123223560416781887662769296742320\
        112146359030091503388815657921468000*J21*I09*I03^2 + 2617444835988464274720202342005638510032172309714593100490439700818350685637576557915514718951607468323865892823213403153398061247\
        266038947215640829767228688498795594075530959901408061171407475928356166791355634996832000*I21*I09*I03^2 -
        802918720752473165154160826416372733773629959838341531592796959436972579956344326253980779262111024979035523558994567457831903755436583267644795425756824528518233603559126299427649531\
        06507354479442364904632216694808700*J12*J09*I09*I03^2 - 4097970939916596308020289907268767832538570115899609077358134185734709392657160748888320919921343076710176396088083181181845172\
        1071989936051241198648845231385922548818601473043317127469590284478140617247124094013137800*J12*I09^2*I03^2 +
        554845167034398911242417580756694529602565828563034893651570785320031691955304839289277076852409883929964540165405445594707280918908546538087333991054241610452736683535071441148063928\
        011562096507417714773976117420811000*I12*I09^2*I03^2 + 42466532668327643801926626409104787494699732651487266073580493332855522345956917915179988163979315673387220862033715168591753730\
        781629416424105781904599493480644524876227766153471982840926839197739771912890705380136748000*J12^2*I06*I03^2 -
        842038183998312139237882447402215136590221171168353246638824469797335184997662867488198411539792904688316194231236665356343063283413398100891785537326627391643843107485458018585193301\
        06904508114649917888358815918845295200*J12*I12*I06*I03^2 - 2429361343256277101754896143740596282948733901855252545294851635765533527680446903072313191450829098796592367253616685468218\
        30411203481236624189666045222783648191100678642208163236958010733362531363442098112883201001771200*I12^2*I06*I03^2 -
        252998639322497973985865176719709037749049015991952676656320554559114910090769185771039131299492361444909851324048906847020843410558587029013950886227858292349679463377595220936478228\
        781510118677570707246064167384210315520*J15*J09*I06*I03^2 + 247678623918226261112371249527051762266132124230062441022758569449639449884658290838736018041683504417176187361083447773967\
        587096457845268457243651900997647495312515541805824490846959854041824321631303411465236417874825760*I15*J09*I06*I03^2 -
        554301402163855759135211472736746324240298734254476586366043323365302309043961228035287319871800813693358959553321162976221965745497052707426870653590271572569261589987126023898747677\
        82465123050766101795523845542618333600*J15*I09*I06*I03^2 - 4874871525954708705304918158288946681908199783881981706144288099694643517568050853867625964288008996331448616008713712751190\
        89810216443638827980751856165101645634570379678635259497954130858351662511410818448499161141248000*I18*I06^2*I03^2 -
        722897193702983645953113873985216356821465443042755723437628128630297853679585942532432146365752151990484732508839093246340349555962910132507645140869670370415377131199858898846495275\
        3755927472247847421861084996930818045760*J09^2*I06^2*I03^2 + 54325363121769575900719230283842426830708915093681742034682511864623730897286386043483775471654603328221748826694106984691\
        92836481499017740853055172693137426889347058324597294311120256688959820104152378985637709665955542720*J09*I09*I06^2*I03^2 -
        541646315300102496877107119873995752975777514814162727833579659702998893595363196007695125625880908098662927768402319403765835428056823129085025388567061387697147856597630956757113279\
        393699048909584274206196489005845509964800*I12*I06^3*I03^2 + 65729906201796069735842519623724680720919562210167688257931672144591192112335239173892921805080197460230527156574532762110\
        437818340468784309685143933422415909691615690772108695242308907422288929869250005810086098308077649920000*I06^5*I03^2 -
        500245910746967011721913798214518697482135060486665893438498145036204185558506101304674780579618858037265880633224131582189966014722280311335300892579244034261360491193421716578307923\
        7518449527411629733541166619579461400*J15*J12*I03^3 + 161859884092572929800653310736535661402379797462957443583930133272897289125242966230468963981522483283116869183393236752870493177\
        6413378131800967975789240321145074862814185807856539183798588805324789632116542680475096300*I15*J12*I03^3 -
        392282007289103137559482150115715161396893710088987924059340161264150715428210524078199700367988285005379279121596004522683436715691729538157009847418009234144237008066106711008799666\
        0033592498786330880326130170429711400*I15*I12*I03^3 - 431533448047252619930711140342217160121497551031187788740072740718345098829690539040823654436045748313628320723832172758810546801\
        0659627066413602804307718196720026808709832285374310460492805038583365573264686734231822400*J18*J09*I03^3 +
        242118549239575728359859812449442269249974059288986995683244286252290704058000775571923791068895686801777691765516516064871536553688116933255046215761120260805794428092335665411355965\
        017283430485421587905081637232399600*I18*J09*I03^3 - 5964452546939390432299092262810446836025915390502226914072603807352368189738898426437452180261274775371817833257230195190549749578\
        0547003212265685080838344695771334231979481653278482402326614404698868659978331792905000*J09*I09^2*I03^3 +
        302029662410766769971901371198897360040474948770317406392225958778862435865421428068565264200480950660800131586005877712950835369366417957064971331953075759329729438233766915222102163\
        18760786555060008275366161144851872000*J21*I06*I03^3 - 22620098704168418714073503969576105801914792818773626275444581826320411408924046443531832656055669240689292214256637507432017433\
        7954836550450422812325638884706670648802626143636651068976857494395304703363419644478394464000*I21*I06*I03^3 -
        628584139089740020027605544088708597361648702843485599245719159199348520483372044897448281939669143271398163639140235644400329867900730175792427276529925424623715509207939688180856004\
        00560190353407662712242578980784184680*J12*J09*I06*I03^3 - 3419667959585855558483927529831263830188570840429807392351982233868597390487665766099632684909982446124747084133902702627588\
        73838301752167488760371327311754779295355155033135790263903205272606139981879611821871392312122640*I12*J09*I06*I03^3 -
        282993144401818748555571421115536368193377129332022557194645946345209996263649973545384393460233635640204244292143618621759970987789547850755942243203639846916753653272430893442342716\
        1816384587181201033093686931134477280*I12*I09*I06*I03^3 + 17678251163118713722302838719433410439537553998502344898068224902616592755915233785602732944755564283661110442257057998942621\
        247159848893429448156937444506288654183616900637140477750682500934559916241310264309823532930355200*J15*I06^2*I03^3 -
        843982749871539996080081860071279142218704250107385011302093766658076851585633995167883482471292021252041738231963699030082860310196899285601296716536395128171210008395419944289859617\
        4499381790779775698476003573233129075200*I15*I06^2*I03^3 + 1754464944740476826640062568592744946494040612844400031852182758904152212096135746960816221906876719371602382522662195294466\
        78829132382967645967737657154474077295194748827978556999566460436728943640938180536352146667699175680*J09*I06^3*I03^3 -
        191047014037515689292976503639974798001645105200151827812857338331163359005325537556464526900131639162645394848554021168282852623831880046675406603750321131818577010199574494179701007\
        663325130841280314272771366141332057318400*I09*I06^3*I03^3 + 15619454198750435569419884201823718501148604711234608932126016825823680034099669087260692063095092348517343682325445891149\
        8457303151859470916382148028751279046843116703715175248696880227951398234433029338666670801550250*J12^2*I03^4 -
        111571373166112260980034362209062281611169033222837081866449570555744688020539995898273064177837349500326548649509855264901516789290538171008703614655383182251139876768663678027425851\
        4573266322876167989447346747358421000*J12*I12*I03^4 + 317206886622769776725319883528809098053077319763042351119658805791971551067019422016935176221485219689317365139536358709522595611\
        847152194802433308671781948921629625552220971098596170315846945418371359998477453352997000*I12^2*I03^4 +
        379604448398148570493912761069813377064067427265016074271663498154756889500556051007040181424195846449222433584263945751508680452976137585329166046454996034875252254622636134947568058\
        4944637953324857937927858217293887630*J15*J09*I03^4 - 223315481492988568957726458920618029178268550773622771401441820156520703847365728465629119836956680071155052894923537034759649263\
        782672133689229075801936131318990481365362536081589198911889754914144851912571115358860860*I15*J09*I03^4 +
        576648739339988601522141410889783111901929457631077655592520932369379235016893320958150384688285085170752907422438000482541758801199966911739181006244184589263018884026957499913917556\
        543233359573375177544680945081091890*J15*I09*I03^4 - 3130867818986751308324045134313433333551231526244297494888762857966200251948823627244677687368241698690150823919506774850865832688\
        973904375227622828977491914738342102754342887230185577743870955679610451843322592518380*I15*I09*I03^4 +
        595742317819714632818015772900672299269778371206781525238967147554516682512772754310111091054533822415084361814097900902385491782564041813867753117423522848614561533525601963170841581\
        96041022940954226811113887575758358000*J18*I06*I03^4 - 27792747199698971807057806481148311911097021653474721576603171856232778788313151064932504240360843451370513828088190459178914908\
        573159138756524081910728407714453092215132672031694523966016230668731509518239623840552310000*I18*I06*I03^4 +
        733873277957062749741145909365840876568646597233528805386831447123712456487248968639028390679373311832709830082874881948844704258086635066974246219891880353468392672071217148404481102\
        02821854646872139711411728311578829476*J09^2*I06*I03^4 + 343193346144281502662845576570789548464673293286085450156550704771763095821600945008970822322598354323284727516718844583266127\
        3842944242074275165431260458248232391377045997934996344122687260307676296244545853688350061908*J09*I09*I06*I03^4 -
        722272299189061714954516044383180687314161603375538726511348190346661430521796277374712386638966498179455377488842524482276047011164181100442043694071361986220006226144092429812534342\
        181809249094025135084598810589332280*I09^2*I06*I03^4 - 23179021154199127660181566990667000741946155960743034125494712735207475058692145799239156442145209825918502136676421066005574632\
        89770265748340578345697376368820503237503346511929820188099164153401919442276820462358859856000*J12*I06^2*I03^4 +
        470504811001231480506986829458712261142447043733119363079143986571891803591576599470225734698112162450758795070987444599508755432575347230550657660825563025552642981639258262861478493\
        0568225610864599790717205190404600903200*I12*I06^2*I03^4 + 2072362207020345318656999682428161086104167200528230788526118068353493022904290080966759987490412232430209309535627314717607\
        8112702197299296075375761573560120899234366220334453777651698953322416854091061575736022616000*J21*I03^5 -
        424566947725574829235902172172081883049281519493528553535178113582473419422834923949464908793485313734590757532572577103162165767717756957387321740800032790753410408214113717005782107\
        9121410504440456003672665373373250*J12*J09*I03^5 - 996398314356035733822151051313648525871101253406722778145383674031078358548603262160706966205246556640152734533469650885883124870442\
        36531619349162472423180014069293557652876587984374129242175524793581677242307817953500*J12*I09*I03^5 +
        338870890669385415208094134639668085084846057269115441615499362881179641184095775190691710151477090171841946088145505361945181888563777919673116668446935627155690105919953670293136532\
        5128534993009158318250129533864898800*J15*I06*I03^5 - 168713610502676671176668768138681369584900202081416634336185196157002100943110337534168549012760287135760720962600788902968584375\
        5836917857431653072000466670210487603387467843010053722969026625286461018617697955348552299320*J09*I06^2*I03^5 -
        123339967596934284211845251604816784480394294252788190421383283486578796901909538175714238005438902700459995894233223139960906475782073769323732761285436349934223544976339829357622988\
        581257415035359660180784793918943675*J18*I03^6 - 66281755290718121936284163020539632400126954000481709855689024247922826168219539437572268479782918127125377965320116707548365077552397\
        714555255514760535450078230544509637015655054695297485523618574254754762690022361925*I18*I03^6 +
        439087854215362592029143369732603525647600774240292609104747958896080227708298118209336752873504833330056010848666167808030171805480432784996730096375872182036651393366158561373222222\
        17226710891003864803831480712953675*J09*I09*I03^6 + 63158544893539275484120647285203113487699862286735180240698022118752711670570444752467751781633748857922010484273040627633613601345\
        42438295926702932133092944582415106002462379587953486851125778933495723779747775068275*I09^2*I03^6 -
        624031583294502576772068480471825332063664392203837519593633859409307371632373757054510280654753630278421392075043552581944378710621160911647209308045246037290407918509100701596172799\
        8729186843319011191409869985722485000*I12*I06*I03^6 + 989011739242551631563232554701789078899495864826116763766152908159921685018893591603511856307385071918283145365211167007188057569\
        2298765424704511860251237761400371436393135998539381118999856708389034218652524050761881088000*I06^3*I03^6 +
        238376349741046602061971660151726934370886277404304088866063801098127816889099194152408037585642746236061536064378355163003266417867254364493822126244653668878002237283039549075574160\
        248359455371682821626434644422586550*J15*I03^7 - 22379119016703133552901357152774093377929847222347845900496150492391893195224832990575953885388957927057795297808527003488577510231330\
        565951423271320781052995032693243909946566557697489878548349423413948681412639621650*I15*I03^7 -
        186274289698169443134294328866924546519591818770919005651676856008424941712416803242602948555975628601118925335721934115306457829656915781401400477248568955297560441891462699965768032\
        5959459661942217314044075712860505500*I09*I06*I03^7 - 973984271207349286574646303388573615494961092485288588709952705092466455077955507068317450069990490394163622423434861713347563344\
        9616348428240006117107075051267180623792996172022493150816848126579949075927535939654250*J12*I03^8 +
        400912173912705812742683772549293964144289291045621422370471863840839406682846018538370041957406436796086520387053596506715397805868438174755566821660566587522757574502897332117873177\
        9579977664461537813042704221764250*J09*I03^9 - 4896031465576682945777910014774335267381709659100352666603619785919542878842469755879320972190908757163172416389592849843766064640354225\
        8737160837086996960256285884161180250956262585034958870926414982796870630445753000*I06*I03^10 +
        360006493069642012801891331806008274436698420106428104047916876470978097670455883752818944149909511201728718770002580175998425317228938581752045329122194798887746088892043934650552918\
        776804887980497897356165824634000*I03^12,
        2102095370928534652106348503262681498271633253491699336795830434493270052040198828613555037088148205943247316509053147430938703184134261558790228414410853786624175414359665664815463798066\
        456315405769035368067797608366080000*I18^2 - 854739321377656945011350468392885876880292746763795822952819871661871457472511794647444750949639340050750517505041367534950984283516738435\
        7554137838602470643610770364170421447702339123200377958847197846861581214635624600000*J21*I15 +
        213382201328272937922512765806414806546793303091931194766230239512373894816382095197774754942969195768793101088539146202611231868071594172768821819473445321647117405927921779222476148\
        193545273120951009929185302264552603200000*I21*I15 - 7983334730814585768845800699755109097904473095609699851224393364559795615602615343887045974525183591748523455857562225835613835269\
        5392364180849357393819263693412053880941087780255341736983246808475787143718155522529267904000*J12^2*I12 +
        209216999905337757809010837146610157285118765116679191730667098619339443121571297648614362232657818283599364731394809305306263329662367977230846597150340042046553231470767063726369449\
        206034703829138332086291042139703077056000*J12*I12^2 - 14484232623000416359077412927319260630982764636960226883598068880103594296975160780531913129742884690364495888012414543552721088\
        5798598845580734372937371667054437614009228955512107940378551185521378682797621556509256116080000*I12^3 +
        141877816961939605951444106800027413678669610246781499708559711257351299879081229134075585077494808951774195819779072712419277876011586911446761538527596509110167942039263129701741172\
        368070344954980463278933001444488813372000*J15*J12*J09 - 196724000814691116524515345962356577957346120752292982415187660719860697200039493288800171638530870638178942749224955009186357\
        50256392285490068051168976227603284557461187845899857913440805882588216074385377155309995713184000*I15*I12*J09 -
        125030542861815214682084368819224281289676799039354307390712873236222198462713440030717172812843641938590849878650095704171908394177641508158804749858032426595021201377206123169877793\
        350234272467771308089680703085341248059200*J18*J09^2 + 33941257596434104188425019087188895193192921637599257563001833591154458702596535253553658903971660867706716576692750233939687452\
        62570983839392310834084387699340621689625160022524613864446833696573645468942133485282311675200*I18*J09^2 -
        356514787531249967983704157614404359574713123364101108625833229787812693520911005279978981142766217426987453369532859492154772703950573391678572930503647862618373657725082519241905581\
        27080074422671806443838542457089862988000*J15*J12*I09 + 4165517857218758124972658471699760234828186925093287488147394210681365289424430114412579498183090342712325322152867185046976918\
        8551875433554107120415188292400540468928999010649130772493901761543285025726577698485490885356000*I15*J12*I09 -
        623530452040972206379363411183630450060020146242554425090988618354738518907074190161657880254800819001931248542443518507774968766765191286806630741009483974048164919061727158836456939\
        63725817412351221876940170546234212448000*I15*I12*I09 - 5487493062818907798321013284854852127312766049301233975430265010938235236406020104618257871375361322088382401087501994599703829\
        8574596791915377268550200149026076798478820140819034046632609552255259000373719266672511418513600*J18*J09*I09 +
        120914584093251953752585084829116486461360959511848979785211307122044275683189766440215475355132621789444501324915206191898188241753238159537699026204687842629386874914394891219973070\
        04052005493086538141602424915258196484800*I18*J09*I09 - 1729290702517135739801199147201330791598559820989023486701023309898109921835962167606248314664116204848085209992205136838433748\
        2229976365737147247057729646436112330156238591248722066425074665182631745346471875344016466329600*J18*I09^2 +
        366920150929647982664274489629780166118383610532580582658790551787712509622852695894897975161677088498118192208644800427890451366209291403997486726890815627273841010361035500400388027\
        62941389611377634743829585824751644409600*J09^2*I09^2 - 1277532434708240772805618075351556457551184320737971314383965756145211945244080254284589806699456642387031285943253464483126435\
        3163760619283382014498013464689938644434255978087065729641104371523343523506482884842385901779200*J09*I09^3 -
        475810100100954036540102083033486951470423404209619342802378000131228350234246343054877185090584345950069349883712689317339384602185415791934495269836400085883691110456101666898581263\
        8391495055497708696831954599521961901984000*I15^2*I06 + 8896783570029217366841849489038432467151674584593194871868949257919406018790320710446806005999850679553951470012217742748951349\
        200037912207928894658670922598420522406819058468598712602953077364506833091959955441347034950313600*J18*I12*I06 -
        100785072498205835868348422550440558333830793005542176198741554001374834891127785395931275725910335212799513632199164986474611298646555523071390168911628989076662508809552836877153960\
        2018746523255507538864719823644900447990400*I18*I12*I06 - 11707927847274119216145140728361510174533728787323329947305193649596787046092241442279200078442051841165224652073536066911029\
        18504165457733644817886493616883826544095869455825454882480982745090698396620166190186801043439584000*J21*J09*I06 -
        438327274353380887511235923768530950345476036382520053958226373891453828005448650211743377984770477084761752745269450382777243811919162061866530390233557324820478255337343893634658861\
        2458325115001824107932610667261817122048000*I21*J09*I06 + 25147086008430230282303278477948428869483518710805544632562618669023429435351964169236116512634980316094063695436171523744026\
        82552679155320705709796783961248172494789773569238295118200638799168721431758990539029115639737747200*J12*J09^2*I06 +
        299751259304488182669504610472045745766828585939379264084141245880889355328951791548909905873477432344274485965247113998780007939213782033195195970446676392741449488003296826162733998\
        105944053069754387369189859494284576800000*J21*I09*I06 - 167956671586731225134172215997441175377627866137464693140459003907001140448672360464504597481930883665285845071660235403123506\
        9336568145716332115155608888317946715038313216033207747991071201724875694791773881914587729460480000*I21*I09*I06 +
        503454453032805071638586141595123896829306845238301497959628960179033452468369643517924710433251756014929712609231421810387069476755423623302214793904828475838786779208019057160290407\
        6153910522255583760516407776305641349849600*I12*J09*I09*I06 + 1107921067036022131992980584945304338224515184514927817006908489625698103185037027644045016967002633366245771645243127219\
        890691270257452926805021441942921835504108314952285584206525356354653388260485614917897738093842949657600*I12*I09^2*I06 -
        286595598296032676631592645015961275467484619438354163370663771017407444079088214824965159232415497054793166303131777068887142182637393619715621320025093500163265325037518048608293127\
        41139208236934792784415553182575008509440000*J12^2*I06^2 - 1024678257726309008715490463771208044906771767915145318044851026476660379868199054428339028942060504523584601010894201374261\
        666404122800856375106882327053191845492238389392309940133936714590656988639475846277314841381350786899200*J15*J09*I06^2 +
        366846651831019047231702503126993145222209893131651991359534458325382385005184983041365093338664832326862565789025320860013054131360125223370904348783928237159077266989613952232862522\
        662459238305606734501215192321577111565561600*I15*J09*I06^2 - 2604332219552403010786239327849270851300469105672467858568769362691300855390541742364340073424143708066822919375058326573\
        91017280759897989215793813686443282576212009909132124533833100203776654126129847971464180441670943296640000*I15*I09*I06^2 +
        148127691434981490765133522731117750180757136870821069353367273364263143035231174457726584267305079584704488664579939949992716371671764256767444579408481806753632298330610634352117917\
        99584089860831479613582775344192103084842752000*J18*I06^3 - 918065987461918846645322586947433731570044234065547654858358717633253862673060300077216219657772141292249802289102505060263\
        6486533848443847756246323235075439803189148231577847110028315944674998295956995736408919229239497017088000*I18*I06^3 +
        294255823392777008581622101240893367413023596505169167073706453350540164796651148627954887918346828079451093082310969318113843107128746913136637051058555583709128571665418271878805754\
        6357017072106180122548855771158604486904601600*J09^2*I06^3 + 95246563268880751299736581598538394804912416400977054727208619314600499642889371464022121116258165570835078007751641926713\
        23117092722980002108038789628726061693409135148236220816154178179495587941327506204798205107067521361126400*J09*I09*I06^3 -
        156834771290540187758529225664890171453192276260428005944078904337105955362486370512048281127039673651403425072625040214994253140772937643729840035953057024416225507149985225764964422\
        863827365213501251282728268126759493010048000*I09^2*I06^3 + 198534149809078304190788584041194718230557666676720472698581255582682529575646266545464886018790566461655640131625796782530\
        655716982160642123219232529301800694609527743094271332434899300838352153402883914014741361745260426956800000*J12*I06^4 -
        145634052672577857403408999480558138172110624127459621853401070777570544012014922526105146475190744761379724228339802556396762075537739802383111005155083899794839880045827578680745814\
        8953067441297785168135460446024529977357948928000*I12*I06^4 + 2926640913910595128902373729274726153605695187780208885042455491973192883312826024095783166051568924546319495119899080544\
        95964622407956176037210209958128663699335800946267262644579884545649898554882549595269964377747698336800*J18*I15*I03 -
        289791088889134620438657523385415877258285747175808279139099250814596379014310206994178652257956723554571069155299535596001385965257734990845677002653451098520809276882862555554077568\
        8814762034960173629089156642231833683200*I18*I15*I03 - 35028947413370762130942623015333200441366014725496082158189950754189718952339308631935441322466376734446598081519922937242475074\
        647303414685912863450122719988049919190044873049927599417494676844672665321190446826707379220000*J21*J12*I03 +
        245072218534303066071147372902268809560127371915081650016891637079700100230452550158216157177303639872617347293173933071652168659603667224728326107847636067753833148856636112046706285\
        628218510996050285529449672031647055680000*I21*J12*I03 - 120904021946052741719718573099618697372479684953850841032385051577522645840776956074793240601648671524004358706221808162991025\
        27092107141773166671173034191798528527970586601042487522726982473937046521914196214445514603104000*J21*I12*I03 -
        334828516887784732805538547103552614454024498166959400877385683902876579201301512524635957338953672372690744415839434193763506227305170932282006681418458143493761083909424463229372815\
        455224506201555737495022113450253617936000*I21*I12*I03 + 147686413926053360282662626380398890937736784864609711369707305048600138466403280732978806639626057192153200715089887371706404\
        66290134081178965956613500609156180580228655422160455104562544782626819093290371649453183339113600*J12*I12*J09*I03 +
        531282331369443809234414732817491194602911775761693492072430283217254329203724902698161440504005959172833503786374297448585774498202269901975235852597180894886946181814139400771218579\
        9759953813950866656942017997902377159000*I12^2*J09*I03 + 278866647382650905772542328332712578939526392847996655430455658354830644720393702011065486222912152313717834819225826275293199\
        32031126163229342652264891246498662068759877767725027785697920572407662908196484934241136291302600*I15*J09^2*I03 +
        648564425992915098716788210595779562474621374570779268645989807662330861603666720315723468168346732478689562338948175432951319115358845773943676428793206998539319277575112975327272859\
        36991565854695860818643989788158417718000*J12^2*I09*I03 + 17021484409844286606406552577559891301846783156839433808902055331449581650740933497697369730328953972315427646252821111651817\
        226483893758202515634114773863320691460646721267315567704227186264279696183656038000004539865136800*J12*I12*I09*I03 -
        150523957711905362704310908754069391870459630782412256803483479113825169290294920764287615217046446718323894600932707034827565308972401750969117817881068300056893540629462615313386851\
        032155689686669237402420334475617307944000*I12^2*I09*I03 + 2325333956374323306581735881751630691444273474057168865909332954926963874453353835214653290360099708032096558391400456936242\
        6366979590405811001880174165811638538401278918028731232652814429535646180845918394604800495281206800*J15*J09*I09*I03 -
        175379618055049088296292032233075124955030780402938553893380859143851702884001424643156225660786281134802345183264278470800868121627077672844456718025930535136046018713773910553328358\
        463929405101991016284246014011268814291000*I15*J09*I09*I03 + 25452502580613645847740975612288591325491115306299094825815956269976884499094543863019734742057383126439654907495886338564\
        888800953900054929506814622392325167337311659971842605561031569405639888622253393156978792057459146800*I15*I09^2*I03 +
        274115080101659243393065661353757268273385164593812191967812237018814821860865476731554650728499526675628383095671307349055442288412405727232130609903516049599053957101138124120523338\
        1702552349053169620447450445108962443496000*I15*J12*I06*I03 - 3704375240949896223722340038736782449877108706767903322245498520896048823491481078178854357121922402902726450353079853933\
        4761244752824310591464514486474106038719044836270757288653049574796069606672103639481207801811703603242400*J15*I12*I06*I03 -
        260844561044564246656935456962917968665274259622902403218354286336227165125433660417564824412580197366833274866731121036713268719109240595131917819615540560511383875950424250139978560\
        61016153992068426126488395835564069080608800*I15*I12*I06*I03 - 167929822803820772007130859599790141524658779039054759022681883185395978935251539127235725262273036875165557799249787394\
        08509488076446227264143630763834975909776690218650955680941299694007838686991569448590159194357491069435200*J18*J09*I06*I03 -
        299634283937430561918487096451945294092769264338770567927363643534284229049421639704924161685348419968975617734276463707801057206122016083001554292904617250775396545179760263870218146\
        1163397733445141512056320757817123515003200*I18*J09*I06*I03 - 7400769380853726984056093762988171784446630072944921948691683749402741762000733544743058273217286070239114139857102024909\
        92962075787772792540592328454785271752199551281653976686119135640298645620770932583541512145953827260640*J09^3*I06*I03 -
        238303186263514664337576793722310495487614479676099529659938889637736418994867114961077029256520704243975235137491884529149926498640395090757037755428632069417086782435042109729191368\
        6122085858698178892945081724990460804468800*J18*I09*I06*I03 + 2953508811095848270558615891910882783431920468482059626818266213464003452579150030929015896819827455363359405453333323069\
        998840493245284182148687756442163021962121989801844499995181638882366635123262641529282462390502095755200*I18*I09*I06*I03 +
        762517863862507930865698093642338714474533192295538704826650652630576592141086878881415891813806929801759913495708142013651491761162565583073079773301782406943086682211192975071979311\
        2610649286133334152652345141125399404574080*J09^2*I09*I06*I03 - 21128499449452155122519462204367711064495744544570075282924230004550147283107918445670400658378901625294456331338492440\
        29336946368194101243460970939243963589815069594129867856976114713679439092829603811553490684484409161613600*J09*I09^2*I06*I03 -
        648352564632280292511563474157533332777840264029865026938405021730490460059813768169875745273304150558040303144885608756758083212982414276524472067095119916912354647000394679702797462\
        531824472778176229463302909739960841771200*I09^3*I06*I03 + 2256226036199855175289545896247115351107782614494108415456530386022066129710558761588740342637080877868202487383213377813133\
        12605965429481995646626303177597970720201415687235402561980400297611823751216178453728913114226920960000*I21*I06^2*I03 +
        348801043904444063616583743101946980409780071447891700673056126845797736002327009329721237158268286743504747703434542803860022573605534801182696418356218777024474947496449039666101338\
        123327288195571957774096821031238386905500800*J12*J09*I06^2*I03 + 282914727430695236037510019003080767953374344326900769990755592426850064690185624452873296752837433511502873194933752\
        9972670984101698636965074517255740014894578478624986451034268376099484303977710618975073865989697077199584000*J12*I09*I06^2*I03 +
        325983544359266222631981876152165861120252140402422278625145187878500262136543878769781434076670141093071277445500898036367264635359434690044709660777588145216763950074616569668675536\
        201335163450657967277915324943986226430697600*I12*I09*I06^2*I03 + 302156071283367234507889516245573806518907408335529472478630438704017562118825295274129385015347633398547251381694494\
        014376498736178587045009958029737916862362741415912192268494769724052598696052773317465556569137148824175104000*J15*I06^3*I03 -
        381984492962968772869666088442444755297928941802669365294444800787934559601348092801171017496097518544105905740170109473551412765770299711936955630696061669893038198406448075827538864\
        390447001691670111693307396667314986307227596800*J09*I06^4*I03 - 5557446879824546930521063150482060278444262301460155038758738911252777619111280622771408208418684270201485760014007766\
        90977548323821134421837102523889816075919939111498720132799676952296353355042745900232680770021721628764000*J15*I15*I03^2 +
        296524391276343159626750781403992192121811875068832136948266548301795538144172084144323991884587381267312143803600920686242810074670369883364860929128811961869750242452574652429061718\
        143427012946905897552989180662950323530400*J18*J12*I03^2 - 1650549507641197480097480908720370217596846966298701198281373496228966018194811635542423011747911411663867295789365906098111\
        593785685042156778344470689687052979178677949705837722897959047871711939276581834331803374121671600*I18*J12*I03^2 +
        299491496361025033230313313340655892763453347633658338515821778765065550760060996807105427881287676059544428782823824934224267530484404419321047070485701840660308737241637632053412441\
        60232672298636131255501994716144032609200*J18*I12*I03^2 - 66611618844581621654620038415400024770506894124389874083469274239695716576428216088110501838773298020964124702863090599369309\
        232578957318980942335551027833398642912143665235195907336128052808385176904138676069500533451954800*I18*I12*I03^2 +
        132129131020525864872213258050187947545111631910890250629578792898716035762833014625515075929960389009381165759595743207130263432994632388907124642821105536458995378542326711598216833\
        29094746158366668598247513729971009144000*J21*J09*I03^2 - 59773313383708258631896240614156079986948750457125654194113185329686044457955833733931756609386470514825879937846699826233201\
        919581230343875180101492046808553538845544116438922532293058856643083099361879553313730025377382900*J12*J09^2*I03^2 +
        369031863233595426572911999909746683100332238892963452273954129992975138428051919762287524091886644053948199101850547108715670063444164592111945893725390651226102690315749018570155481\
        50994911379265906367618331219494540351200*I12*J09^2*I03^2 - 110956057792447522385074665704693874716162616614765029630455073054563289350205682168608970673908433283999094871104473577967\
        52380225292281813719047555024112278146350313998048870595168205834007793725402170577096721840123516000*J21*I09*I03^2 +
        559886213859020360416092140896165106053550584411696502269863422158853585812048121873332261362898844447073818550979909876844952460239177710514484060904681380255372736897683850816437034\
        59056325695177274267925398531355890224000*I21*I09*I03^2 - 27774983421072491547829375020582299247304412320789204165820415160882668856689710336797896809532952771016015267501990840295980\
        007095030464290925042282061788882310234715844810574481221514472963212462476376244826584088651568900*J12*J09*I09*I03^2 -
        164823875573627975641669700804799859976390062836534296342780751990608604567260839374125595895288607266366380694624856698211491991788489563447378925303109696478159786043301569294851321\
        66855567899809300677126338323025640726600*J12*I09^2*I03^2 + 439628813012933025981755199200495848997689203527951142676996775427073471979139995502275656008647426435832705281981739845949\
        64342055058968165331174486505267941620886939043845863213021330858390596209450654733325168397701137200*I12*I09^2*I03^2 +
        430428436123139178587975072516859848986326735173365317150406829736856689766875587629040739883508106336817604534887923530191817741234012006211590963678411824343159225073056087531695036\
        3275277009966060223818252575134547163956000*J12^2*I06*I03^2 - 8774092923484405393498173460324954194717725863642746557064121761635942775833737997244702505734331524511443861316507566428\
        386642689878963321917520610688773397017327261274839454686461545476433613380232314375262950027244131304400*J12*I12*I06*I03^2 -
        741123263126289199912184950547330767899764777078699296742880038188380616818370027914421305999572693449908592001277360421012322484771283479714456310627900070287529721507318307538177323\
        4809110183783543257276063626065201384986400*I12^2*I06*I03^2 + 1846853096732494461734350507431821570637874557063025552548292678278621392465083145089459226021269683629664082586324344471\
        4175019628614296328384294467721537847429623314720560799182566134307522396629011902272974615995321136366160*J15*J09*I06*I03^2 +
        114799173223954069471048257819085927775545246637714335672610004752416209196908458061975954094419138030253240162168735175722326294933476786897467831019245135430575967163541311495973695\
        17288606679143247320258985652076270774791920*I15*J09*I06*I03^2 - 3768520833466007120933255932796070206522690801228364661658445893283620534781322558341787730513079621507500464914007388\
        392598342361132641012682993692523399495282959654090231237629789804456025036703174752054421146138689778767200*J15*I09*I06*I03^2 -
        515398632529431847350868882161462431126030811350362577775658886870972185714605961683565909629363326662691284759308968064229432062688181571303029604860138122996860342719954426700450880\
        75129312113002537200730201108407553415936000*I18*I06^2*I03^2 - 193965768749012970490203227285371417133532369172492677791910275776195449825779090138803024486897604309256862235019074995\
        231371390202671862719231080518087940980603843356765948360889622087443382295608923642631859612726412950121920*J09^2*I06^2*I03^2 -
        230794260077930986369027465984814314699284616528271751130330461706213134925084791591758042292311698347756183132039602484670676450461335583776362323752298528403721068245733470949611018\
        498026138456961388040109006378267497744965760*J09*I09*I06^2*I03^2 - 2343847944922378316099648757618598334018684872099322691270698647930127663617839889283789788233344042716005117253434\
        4733153711753965920543478739084539939465186355154717931566769255783309777496127014052246062537162125956901589145600*I12*I06^3*I03^2 +
        113823511600015557154072438051400043215873404765533343838321781899838447889211263372414396391958766807082749065119861130678036405978892478331152171802153746093116720463248157162840892\
        3635345366157491728288823051723877283087319040000*I06^5*I03^2 - 20961350440773380931426937648605695555214240817779322818273576328272861127327849187241202051446757452480593712160375340\
        2065853504303052779498846544011414991133809324471129926467429581617301885051930097720936580664179191006300*J15*J12*I03^3 +
        794830532663148419401707214563313897370841083522240466611090411192058224136763558232158321763830926267247722409162464931706043898464849037025186057098459401001076086050392407600152969\
        14746384879686245835448239262606032855600*I15*J12*I03^3 - 20031397615278659609168621498499107842489536238651755507760948139714707707492481838179092573977602321516831471667597512312794\
        0887001683950879998164026010906125830977487578045136982908343173849836212961372443082846086548547800*I15*I12*I03^3 -
        201902528938557220162001871888726463240788247527841696825609995481450615138396208262146080268319505956656205044140889938392111307162967089292303816209925982379605881433279438650986542\
        943688417000366925874034939130644046420300*J18*J09*I03^3 - 1935600179153288424494813730828307762909023534803210825827886496483349893338915715328486213780467013135021864484032589459566\
        011125182324993835693191428677270972306027235165185082786174002682765406916854198514447844422931300*I18*J09*I03^3 +
        537683873190261305811535633353773004726151901361194865678578943477750626170942176611366019457175465275674824870349100960722472917434877094954727301809072222096287721647149364924823931\
        6298306558798883446599248684299407435000*J09*I09^2*I03^3 + 6563285182505730850956217249223095989453859984439617764801852374104365355026150031161609573463947174591350191487008032269195\
        94717940764987646135420261702440095203098987700068707594675183517655146268003534970875325854912704000*J21*I06*I03^3 -
        680302586275664558551901409294902132225957053821494976254161866997797588927586384488964831188352992572610461014596125366075226504278217087365002145264941803360021520580678559116381192\
        8009779645449009834730716846456488039968000*I21*I06*I03^3 - 149593560346361284718688134377256939913460649734015470182083096173441603736299586193616895953314832445291653708966519550592\
        8057235946633117190220722630791067823121995106022814719160500993195167650057856151944590249483198173560*J12*J09*I06*I03^3 +
        246009003192860065735424047239298140898652613519092824004851331101795792514003218170566469565102080168318447854585816789264589195451302323793052493679900408015313693002012562761999659\
        5877235382292586134261174451949519471057320*I12*J09*I06*I03^3 + 14186546376159018080920622953463073254508293361124213354470788195114836843113277598936128023322478132918616554053665921\
        72959233423696651993561066114060820020276768336593083497314374450744424645889484166887249228750682453696840*I12*I09*I06*I03^3 +
        300371243277760492977276840850527096404179902895373526398878004731150727117945600792785812150630057694982670652787467546139163229443532161645047114503695117343220890310490472402872992\
        864898245955132584292677637793861925361830400*J15*I06^2*I03^3 - 21074305005012528896092014832037396543552629747478064853495164632558855974165098033710486973087628504435099320697180752\
        9897632443817262085174633181771979893591409097455749621072081927902914175461434308327925658601333144473830400*I15*I06^2*I03^3 +
        545342838458148544564042315736428724666989236565877959473575898233907153464859668705337215886644655260807136506631430782031314160870008179554720071651698590109623467177261553278298093\
        0201586073116904973386329413724565597742690560*J09*I06^3*I03^3 - 2600512432095090822979206246020379333049928513685402874244865122647697142181442202671906165505606662027400902277636609\
        865400360728948023137552308211807549790914477534464494923641466718673495795609166103127004777481870424475212800*I09*I06^3*I03^3 -
        298384558573705192612519079767094830695576933497845657481698417766156802150661740660978934218323318456929062678085624182854334659683363405031887575610865220489239110557160389577543781\
        0301540509879267067949429494969631189500*J12^2*I03^4 - 52123571768985502418585197273334785833881223345136064765564391897601333469766212704015288240382620570101572877867580800528336954\
        435682950425923512470796967018031465697999087445891548386490169242573282649578180024035244777000*J12*I12*I03^4 +
        668411935869012274085613801175295475161229578037176718621680383106965838512953536469255765216580961696884058252564910252790676948682214691259019581320069160665106077217640486510483259\
        03603174990410838952746565063422771409000*I12^2*I03^4 + 1747276695793890581054985082939659972354266791252662605451460451017356002806332588537402360725298287854200713656450141094290736\
        36282552663276629608935897805701178256871645526440247969661336230999959154582261709522812853685160*J15*J09*I03^4 +
        248336460678561227817391940285165278145879309903206586469923012204940438739359286669246031894781731467511641794506140982801315181990216481897173103935550258850348170993948707918126603\
        46360078024960975981826908201739574408330*I15*J09*I03^4 + 52822344496238957891634446631122460677233759374182938461369382460357781458658551517220607501356167853194938678632264471305117\
        71179922012059120040175433775633275685727927659901165042206287804709592426369542025993443861577480*J15*I09*I03^4 +
        399550573165106325936331163272562484275221506762302471797526421800558969064456005666783988586461102670956604428995093382051330866492362496964911735399829804829414183735743410926212682\
        8520685041574469039820558385062503381390*I15*I09*I03^4 - 178891176025731330082700184472111270519454281098187265031258444456695456837980548897805033325418637329971399351105109271469815\
        9248233628092386642710329213967142786527179754467178908040732672890372190994239213545297413951365000*J18*I06*I03^4 -
        114796759609140574721274522767014862085315302391709916442449613820695613285511245764643905664016966076768763112996464482530938297721962150099802588120994350692678999874306479296385068\
        6850023355159542628800098611026216421251000*I18*I06*I03^4 + 174998421049666768611580643931422408220233984043687653869394472410279154654440114944663812889893733751854485144895998698132\
        2374521296495140482645762921373147086895330825076889330394160909822563739806869886984727986849526392192*J09^2*I06*I03^4 +
        503699353881029838879626528770081935879177922214085704755432472375828897232910538040584343221399111144164169199502890225469669263621402477620565197725714967705522527560714818403282015\
        524423930039820373338704403923208290556636*J09*I09*I06*I03^4 - 241338563554105605670434342412421716805661233508691526185210177489714913842481121631499120579191326717464756197325468965\
        692950407039321349899821001991776639398605312359004668682918273196172877369718043633289590622557390662060*I09^2*I06*I03^4 -
        863375723353758243379844090198073793951198267418058563731378716139895571063573173093172388388918374225226834151362396634772275259679888429858810649002472285022812618362729510171808845\
        49202831182329244840357809454148129414032000*J12*I06^2*I03^4 + 218027356444046432656810550251282701532389839464236102828094906955932930153230280218286079553342193698523473694914693551\
        209209894982588306618026910553575243957155830210986125451027890323513024581548188297731899936401516609150400*I12*I06^2*I03^4 +
        215667136810341620007908590649661907996598660106053997068570527604519884871205572646732847205662108924786658631687015026166794987210474960731502864003056873818598915086700843968650842\
        78332193286864485628409027605284962000*J21*I03^5 + 388356074151780624332339454383390881336828081725641007556108404950058124359235467758700029851025396372639317966948442729307613847977\
        7611341208178089968848493603544209267453694678405576234356820638090160665370570556506716750*J12*J09*I03^5 -
        181911832656807681693667920928565708820930330519839086071483781606849698580252640073201520300635554173814386518864999494750718869668511692896201823034126293745180220833912319473412729\
        8180833459744371431555084542859696121000*J12*I09*I03^5 + 252368909655718280410427786631420987608769153038450633659691295397138319194936126285732303170209736739412764512127955905997204\
        3995809132820245288481962514365258363544814781559226794160192191430623282836842859383036936071467600*J15*I06*I03^5 -
        364087571284506106208215246492917742234868846819522722498727208890112329046556412257920252525342681386735396783173825959326979359024734351604091640521177788372295139292167018772467208\
        09229691025610484453570903152586491544144440*J09*I06^2*I03^5 - 136964266174843532153758449374677715429444194705008426738231807406739922212995071827016729503640350884353838389895433158\
        96924064034797113921171578876602395493905338111586632523738728315544538167992916671798057694598203886475*J18*I03^6 -
        335072001044458257136936927384924796370937607810545892245979124468171967640187820104343863730922127914755240804586035412652623352187628951063987812136598831556986267841822535981007045\
        0312101338708282458449251723184290441725*I18*I03^6 + 1883093484659803856430034430819391162943803615922076746674357749004332843726463126783531962237322674254744441856315415151246694601\
        219693367028117914465946198663033581400827172519594768841660921988494044682360620677990440225*J09*I09*I03^6 -
        718430807967570565835569036407940524978094840501348403089076612688284435729050883357668635893477491029518222415021732960514768388350146816956913714471042823069401425324089566972055106\
        75244487043245032488108024300679122325*I09^2*I03^6 + 3498942154802390217303871247023109775458395890238383582610208773673813126951879236822442347627438539815032176438939302144210938797\
        53836327499503722898466108668620313678157485005382470193115992069069306091636946421854121515000*I12*I06*I03^6 +
        373079190452504211180098272182198579180095116871423784197443708493393780099264982596859656389647405009364657603043615344368793569852983571410797259076659874359470697878280373525157707\
        936012705815972070990051048124793993834496000*I06^3*I03^6 + 126428603946651766435577604816069603944872341226693601943001382380071479970039469300746523490299143459480400904703980322732\
        87523390463256977235382035479121340263535336985076136165033750611077147586344267145739981276110338100*J15*I03^7 -
        166221893813190139341061947477454614039083206969099183439518736397603456558483369376815124662990194956509230397498850741727964544442265439792190513265624188473765397545883607423994642\
        9948695804337196827458333989356782198300*I15*I03^7 - 2414020007811959459877772475801005279492366385847711226169248799737056344909309863402036030165951730240831829169886395968682216744\
        7230781951307747921470246754237010330890578005900225054962395634123187718346249069867051838500*I09*I06*I03^7 +
        171293755541633109259863089496662095254931518795916693951701178435715720483796094889840078817250598766844139702972618828268637610310394395807596734878144898102516978220179208703164028\
        404079325249543422716739834204992547750*J12*I03^8 + 29883213332759648941914206537351233723696826087836472559836480569591312633792143573074772082577477100439559456176921356576885135584\
        6413886264217855835541924497648544801926063396544405154337743680469983115429921332627282250*J09*I03^9 -
        526014509249537036359273506433715384473966677800198486228964273583530254314565764842260139061614577832422170215612429401914796666965440642458628356399281704830055757466741700609802829\
        3612472431193034673262817255753090881000*I06*I03^10 + 110111935556949167376101323330052322352602241041384399378740969959733441306451459027298366260412445905236287558645585037684301652\
        77815842929644516980123091094552305008114231348624764405916659497801018892962655085308938000*I03^12,
        -875011784656082832819872252518642176699149643864925231666332834760339182725772500310737661750696958165485997580785407104631550947571449851206079207449010184682158103659883302839033439151\
        76392471223490340475645231183017144786103996449726918714873176312178421827716771104382311551901867187950429016669221683200000*I21*I18 +
        134999413945375871691385318597433165832543823609766717010570973458496049298356692786509003385794331464513501855950330350411694713514704316602071701612305479309145678159944737381690817\
        208287915397357280590524142724166547504923364220175174531507620891327822188608641697319868991802306825138489650858531683477760000*J15*J12^2 -
        612120318823766359701075414960287309299480501884392525398123751878931477052230260561277050981900378969910254645787012678681486464225005115589500300255464304510960884525994430005394540\
        0175828775018517725842039528456507131848688921850241805955319693184361488296615705905867587191149597306488211060697025345280000*I15*J12^2 +
        612780049873631855145824241484417356827720302908548692943458825722962395988239620352260408771557264444700384245052370081536588843309983098977317411222496643838374945830377473755047002\
        16013872467107289834371718982545291764840402702420122273397565379832486026903724721468499265483059343176212310030040284012160000*J15*J12*I12 +
        121488678978513890175427540987116046074452020724458551059537261318152044274915783207803865809262570237924110886926573806200117070385864744009409534536471284161484929051623077227874503\
        714288410457025592590358771814473398224823630224903348853752442479810117955667869208482544482453542179772754632570975202785920000*I15*J12*I12 -
        299689314804108752634070507977544756993870324457566539600422512925784174588851073240218256971905931293627920127531054593655819974679983377539477357761514381775710916182532159080083555\
        200445530167506275724802602988770583309623710114168031138484871386694900617150578716010580377553388121119733891722695302355200000*J15*I12^2 -
        172796095609211167095857068379845362709736162767263492659263255932416516325306278386071456114024330016609052296081958448908930036727554509602111351047654933589939522786658151649411853\
        550442828630859712945261792024259359628450878897123264899867404239522834232149227703983269940866293082835993969111545853612800000*I15*I12^2 -
        925921778980346580344758158125490100196803146718482044135770410095359017329485484092254548169398805500346828876803133457136749407211458412992237997149830459143046901168246346087117708\
        847483272038350556979801363420865446389645830328166327618015964804856123059672981560615821571709007412300275050569587551281920000*J15*I15*J09 -
        115847081547073562189267831307104982164511993336287077956893362895523195628490041998291334049839585558808677292285378103151999982043295960393312994188427347623648421370263042447593217\
        250575908293800405359898967475212671408594221879097745231693092352946896838931624540021940506046031955183023900530183489944320000*I15^2*J09 +
        116668237954144377709316300335818956893219952515323364222177711301378557696769666708098354900092927755398133010771387613950873459676193313494143894326534691290954413821317773711871125\
        22023518996163132045396752697491068952638147199526630255828649756841623789577028902813917641540253582291726723868889229557760000*I18*I12*J09 +
        260712094405896695711280004383967958567084408736516334040542018908535176647368287230965586630337106023648055382212913639835210638826561183625585491848463614725178029584217968532039460\
        0661762659889450527780394269104675431533074125245793294630987692855334490878911135106939161564221019906306095624153948262400000*J21*J09^2 +
        302546872412138558562375917861960305969228531159470844259905288725917299786450176410397286138386981639441739373809739648067197429404780594121283718440079684993469180751084872379303816\
        166411540996218555998960857597286696201251551709467347640009408973633749366386439905067376250179265416967911033201289748606720000*J15*I15*I09 +
        618948105938103295932223238683928901823591294446250417872596905489677481874968770224973954772297701451912656732819100710605317179891548901099263804752499783437485540410741550287596182\
        75640449870585453956283386722079793053776240068425678264611058871623966919464626547041463007727049577533432042453249231251200000*I15^2*I09 -
        166578848837511157831416825474946898196392796403550192617708442804609873297781877718682905431602957448441782285400239849378322055285062428344570446626704514976846115561867500835521844\
        34419326153579354431329461719921716535521782708125998736814517676225499604154570983778300106800472417175518868487422383349760000*J18*J12*I09 +
        118616505557854311824144400334624020789716748025586504176612738992863932537806941531413708884799892447839773790982548708372750440791876164835943788822705244762945457793818755827427750\
        64352530359685508095922845795205122231564758462721539067414545537891422642957698960001792813467923345685085738378633191772160000*J18*I12*I09 +
        229275000244391054268070766653153229119682139579710128245453233393694858360315143524941233539725341826703355501522098266750554110226079709781926391843418646993647995190938744868022249\
        74654371092649296480506595529909132323758486934863033341240292849518596482770534722257087046791689828622085170846283422666240000*J21*J09*I09 -
        184145704214488285882819773069386116635351733389045972084133220168830103553107226784323815878222902928839290347927367871970810637232358081106120815705430977757704872556251688442203158\
        597016116221103300935487520812039725800269446100218081229607457174049692234086098030155716438332519111476325524165687659345920000*I21*J09*I09 -
        108834597849945250616775666303231883602699762357067891324087093357858145059198304052437484566562954796321732327072683026007657312664327977551867908067014044616705296837323411600984052\
        181291432686323328623267497412638393427047071280458335099552565393042680248322224819571641537423359191266480678921352391194496000*J12*J09^2*I09 +
        187853021343061089764220836026412061072286891877515650340892875926459822932711203738268375350751452143953686832984623970389822727869579248745144419373548356001438990318549484590706932\
        870154115608490206996982488582166568379038237831114626991238557355122379853668084952780604613709690473876788532406424385658304000*I12*J09^2*I09 +
        517509016175760934479320418110308147250402202717538002109511575555793168761022292170374372265189796124540151250080126147586253952427390966794247315293244890306920786603763696051415836\
        9804912073373274973882913939604325999712289560204605633710843722733623964495855629287720352059060262389371830211253462021120000*J21*I09^2 +
        227964679056742708339255945819570788414060801076659268022742041844981106114977424985438305899224832994559440690363870278928041899063541818263095300765001751547777457855905622254609757\
        00115147879321375479227850277910289955850405248696978959313703005954902621330909787391393871797724980027860751856489021501440000*I21*I09^2 -
        681058050575994671267273678722779398887453942894640638485431931600538423708657335719485197221401074037023595270642545392968899641024211990521494310552200984299580329039108676620677293\
        4516002712009001566296104190293847359241114227475793605697097858685867175492203469331287758242175875699811875782966106942336000*J12*I09^3 -
        181489238310736005429175321621146308231283755662913950026940554639182089634595283513036575367623304777334028373817236560660926973739545471506478910023569645087247548294263494287692361\
        7614591107286047300944015730852851503836730562560011084117887438668516699790364121465627841718514623627354668304412460755136000*I12*I09^3 +
        735422902497612629648697438415040983524292921650183341569522108755993535363951846024266681493971264006925605856219903371507139533495904332821602228219440734224784109784001349558572076\
        1891477823438564278966060930386950380565194863156494822823955438543491743637096858588549431455256541172419472920370709827891200000*J21*J12*I06 -
        401090296646150617360424516863683455737168737432299468387512231591609723793886918330351362169178393951043113551705878984541777273296935734658480280443417720813603618351443560713428867\
        40702810520363972811396271640776229912922385472229021913634810607168992150279430213224566468418517965071223333957680230111129600000*I21*J12*I06 -
        334927649754086534875778104434241156677673489228977308503115601591127757089766782415064205433916625969485401927084930615567051482094435114500198448578312718178257755839504427417706789\
        16047231748600491225763955109360444352572017295621660072694126415663105719056140612799121755953643316660797131194043837382400000000*I21*I12*I06 -
        308354158293914241133937569299424890074104191408464253512768559213813190483026442729358285442571690703004774881166773417821221336088641128087108341549770203842038794035275234844176786\
        46249815971058861534743110191040541207531559611835717893665790645857630170859144545966243288567347797666543221795053725271193600000*J12^2*J09*I06 +
        555051796274558438414468355493650767213867616465149209413922093326216399872625252515079138914584933292561682611911105197613170268749416262531730477322932744997760748877578051317578327\
        72961156874037794115752157680355231030109852444541995779259144196239926024621587531570106343886628475578556036657610274604503040000*J12*I12*J09*I06 +
        172364002826195986678827209965219427950192914871779805966438428867534620946202539526479203853342588853189189320848460766855903137181536865276658434722621322167456735312815327575082367\
        67168474488491134678566981108520418952087831004594174725170636275478166307052021984260260936669852145360084840316207169940853760000*I15*J09^2*I06 -
        539468122601794473132632596766297217217953584899307856219527981566107963815688668722153745457499388295423240799409418757920325926529567977622237036063973583687200389937858629410838967\
        5015153074764860849770080908101084341527525535485283578984115234071705363850684641751353278977826018252199019563362476998917120000*I12^2*I09*I06 +
        610927953617247815397694624441255944554134157763701678804610099300950789253429627982473070292684858959761762647368282502146293854489195315015710730775065418419469219328466612989266010\
        6938564516250849187220041626029200184042333091951379459643019880686106878390446303302879590474419940919959086502223351079548928000*J15*J09*I09*I06 -
        706692570830837032239096653246061832335928544096336415257731532112935901741889212833019673163742355061983163730230310570834795780276086025165334526677377269359614851955506513524699395\
        6286084336955122079906834073764471659638169314363148862831238155718526769760035559285010254290120150651712961491437339890689024000*I15*J09*I09*I06 +
        175427981870837138303101512748870583944388408295976766085360211248232079454141876781794292087862830090359572829670315736388458588927006388182772116682587794985472424147352976410096320\
        5153000860059813042052208121204990895457465943870860992222633170520114146368574170118331728214462908867143736250612999048579543040000*J15*J12*I06^2 +
        560034620256915626902860320825140815404034328042407498342740529006143209447609148410022041434580064469102768629194909821171323774942325784116438820749614803133656440332387518773576599\
        59432408910080245268926369792136013351700342960753763487326492411122877873970801613657747136651305829062248508263775809381806080000*I15*J12*I06^2 -
        591783141708675403206945815161632455216258010560102874373486805670618268451393085196542373270536952128834470399410756894100265831494925024727726157904140033949158681002878076933048190\
        3465485840388072193482638466714021323150210950452529861553352713325394852312054299329972802442313363427278813827360618610229022720000*J15*I12*I06^2 -
        617908806760950873681862719563696374544567260539882547716909054827689166016322624277428423252655115045906379474430894846859417974549557505860884506354811758633699943933140359317851445\
        712411597230261824555310076411431834006653632572757346371375046848304391589613305932541224468609544133805290274740141524690391040000*I15*I12*I06^2 +
        247119828222364138445725324514409650176377295683714192568406694773314103694838884721298708678399584299069120517418416878889812516891334491443534255413891415797939824204627014687732281\
        6388347106648415578186636312086549610200817071790534548510349557147110339965726738796311548105124994005652617667809537903775621120000*J18*J09*I06^2 -
        410821152111844078745617299716458713647920798149010103214347993360947976583027238054067269854912895080316074015009189919818865104330268553337146998704031569078738459449719197785710299\
        954470261309434849751906712334106997028785069722026365513614475706159217301517538438249124854301457227716088289377563648978774016000*J09^3*I06^2 -
        365538715139728221053559336631440102511794889416094985732421421140272619539086957583613302051038392265355731933559544474593636434774814946430639685831340312932312213607370527195818263\
        875940328738617201532035870611772693003222842159757554351531123313478088482483262503219737983654155068276537380238913963924766720000*J18*I09*I06^2 -
        137933154930136119962095089333958927067921061061589658752202251229661489932440229754418998287417649149446390138995928434025105428805481653812279347778277791693498945268630040410205930\
        177284828503025010031185999482104004157071778553540574544712089259626119227122455560255819493181388829746376830901941493862359040000*I18*I09*I06^2 +
        149441746155482609219652827182263782971750454639832831441238951991305939913561317941215247808133485023727198729712767911550174704180103152580883558784062271622077870406196011910164922\
        659416433638195472835556569516892777538408541947046642708922319969287497419431582510143474035260559090723990413308362051435266048000*J09^2*I09*I06^2 -
        369194833881688170159666396026049751787132385633754693223598500930808945310104908164405095156252168957048891237375091445125956199434937956827033933961792647843122214488737150001472650\
        63099474452379737855841542324592026503429847345489380203618678787480794141544262087091135159068307926446494842957123610975813632000*J09*I09^2*I06^2 -
        153062138931079026222140424368271990418313386699582544611014289474152776707958792502830807371284550971446792279054213403589407670717789184213441412172128568800765037673821671629738547\
        38643573010918293870739623879026103621181869383335748259861437082693505277922470688742444053950249261314262724899648073591060480000*I09^3*I06^2 +
        589767303666398933672751330012533360532706312780160732325894904412761963780392359734988721895482125339568980117489882710360382986271078643479087664768760797234978982364162291504000327\
        3430323292088868330419263174576779496803004048240109774773436680374022905417690618545432424279893457580145253152729528905707520000000*J21*I06^3 -
        127772815045068578914608081669967539925963177727145817420069364680736829664063429529929848274485841563709081787315259077547555918525429282565548131543814638781045362912282670093941472\
        669664494782390454377650612988849121867602598856572508597304933993664548614420510665330108785472131888358805616960901697797353472000000*I21*I06^3 -
        352708292511426661912079667967316922083022915169140498583397006335631813127463205651153651349306328323499581745251514806486915175262002470633810590635577900306791394115807298914433178\
        17035575276764997398389613217659344341409515589373463339040994740681699271880519014113994098068300404007631642421347954682882744320000*J12*I09*I06^3 +
        646615016181918633023145605015440084231813702864074372699085079349487965482072305887959710383858274170052482789353413249708399091383058918655111846458847879840312702105783749891249583\
        1172057101453151186175480793989049739197554085682402411297718651770736172535990188194360294868040606252476545162013774213975449600000*I12*I09*I06^3 -
        410548595550013151320309873311393825275470294557326284376997208282136306523476929666880060573232022921426540739793919614178343468713022035575603738892238736407528323120275950329929523\
        0322789848976613407349354222492655059267241842585706702014100240891287585160149827482999772221142336917465576518064736860292039884800000*J15*I06^4 +
        856592763336737777439391926547884556268552469215853461124814687077660254937074408414393221968514347210020545535029654354835048244350418978284408708375915372867554391386906296703946540\
        428113959419380706836999572143147278554984924313392893818617018561437799745824196455260296559928522221890456476417136131372048793600000*I15*I06^4 -
        581012295188398656879130537975261537555407575463222358890832306700820778196765872492570578343149824742779708430875437919359293889728321362553021242159884840567786654577022322613842694\
        1380877888657565831660909937662879512412245803305563494387500288089656910759820454695767805415179735111500999613976963241934948270080000*J09*I06^5 +
        459143561367054469028773592245675685741102506827185426108479518916239004712214516308033462543264490215185178805568422701362744523383983587266101029853481033116087441112705284982789515\
        74561417675518836739201543163502716737071411272541561258042614828157764761762234815780132796093065732093299621659224877533124487086080000*I09*I06^5 -
        689734327933316009793337275431205472100387222504367350920910676612028256269185227224121866010741737181222843186599193484737882520333893934635867329881505709965672523327454871367830629\
        5451680975423866914535976831247283424342348463389068453531499870536824918660238235487732244831289796004289471128704260874240000*I18^2*I03 +
        317803250766076843396677088628110410827859295528341159164942356279359609387615159519190459231706211064503867186584363454688513357279924450996209286440423572143983477739869312628362503\
        9794860882557949061339657329626134499944162238770246801523776152133467125898324494207242248975542642915539010658817654272000000*J21*I15*I03 -
        332140143160982592069950784080971231402297247587751997921092538368003829665360689596278476103709688113241969567441811191894923457838462213782179916251094080773834765600647130544446747\
        56009906267826735066069201431010690573539280719385770873165923485381262160915380972460743424867094944658191936603808208754560000*J12^3*I03 +
        120966989476793027197808079633295711393741587202577609949803065339607821230363679374353681334261624994006921340406035350444924517892608398742739261824926422693495764458374383904021304\
        028787082275903963812474952144123959529655222996105898084916986763654012002109267770290035283946374026611087843872147984927680000*J12^2*I12*I03 -
        111537661779458943160498345441798315034386065378197929537176256519973684761317695988674473462351010587513237254232638993366907559770227166362728833727884559001777896537037135294782948\
        738708295123216923077241833994034543890628613425322865946197728713347236024749125649715320888328917720437388443438038005756000000*I12^3*I03 -
        142746555655357797832577709283896257433259230418403728463720734298970131878445597113735598214087353605595356425035100410119340935090481044350401375805996378690524785215487137717268903\
        523696157994002581790963314218222861999148654792159935837574732626542221620113381466785936612663102354474946569557438525499648000*J15*J12*J09*I03 +
        170253499040231131091204447964030224632588190271973875233616385833081089736327411050610691248421609306169437930258360240491104971935761490877178793146540838600107953229475435643568928\
        632430169346157709032976465566114540109804158213901929512591589727965858704344766592645352061434698202600364476579373856937344000*I15*J12*J09*I03 +
        328184483216871229124195159849113715325651570006922900713984779962879501521043582599020185174902410894488864788493354509590275552647744724743948450950340190470590587202510409590209113\
        969637388091518003292952763827417866938938211219832433490515815951437486580866314989720794527419405009655492811373966728589888000*J15*I12*J09*I03 -
        398720742160049213405194123854175156525010190152811413681163424015494699754997258432560487296549852199829940315119609786937654840211682295604633869784872482677924290559297012001084914\
        639624821344114275166094079270512389802829383456869483811475681562831801730312141805041801447274475837786302884179920328598464000*I15*I12*J09*I03 +
        190629623025299685180399171725529239469911333159235507796156531252503464425143140628082031549341235983116436334211988319148041586815856312666524288858396489275397292960836423681727881\
        026271675887567135210810826721551476341316516255515283840453071570904593445213791039789050874702639796003006236015295719613872000*J18*J09^2*I03 +
        230376498698018395392935973544442329324028322527472273678507246282750945273702223879356634138962847660545591666005032863765198656466569359276286383338979937914801111260844358261314617\
        36314336822185289773865167297637732512309072289442589096946523826040729320323550987707013803768472506454361765932214473781712000*I18*J09^2*I03 -
        202502407122957631309665206916344538289795043375810837521605499064885692656049355220722702846901516807526077150809869330660999795681317316925885103114730643092710971415725612962247914\
        07322638659500824509091018504022371687546925403964494243909952217656442608070761938963757565684519452816649653104524737481096000*J09^4*I03 +
        142812188153095335818116085735247026616142980187006831822565617884835387398931287553933571300880997756853013612463857384862228656406663527783060230671277550358814786360094125587068758\
        722802684167902176192396885817219096610518269470008297514667348644353892580065038735354054654393685393334109369052535148821952000*J15*J12*I09*I03 -
        545588061117417923461051521580263456069059778267943276955285473478586038963147922472464575504207822606431920558404822271824980309578178864600877863951111841549535659220656278980026641\
        11748643106360232992315421429761953828922276216895476502403644282820626655997673661673607485988742698056165612631545654803136000*I15*J12*I09*I03 -
        243082908464376786422604931301619484386050556982168658910079549814456647928565010999607328270098513614446739359885504834780072350283661441295327722429576748514977666211905765108413993\
        424877935253523851991536961087880631361865450493780618355103843941926874895042438089369990468653697723866644681409764266935072000*J15*I12*I09*I03 +
        161326128992923163539768818884483286146384765116083394691170368491700926232152800904360108851483019988737211447237672412035941312400345694964403753117314139543403863340630088974568455\
        49769609609376369173062665684878150405355894456837901040835889855391217711480567275895230159479760757355672015285104771182816000*I15*I12*I09*I03 -
        129947513341312858626705010508176132700617758379147294493494103154461472102834839042026881537247168603287738929464165993342276525148811021833236647947516982193544858050071930876726645\
        642932049106541796776511922550004465101660843432378822197193646161812781865509416623716144656751718615930254015385375528553728000*J18*J09*I09*I03 +
        549754028195632815319825580265311352472056323799830325034507167325875378284101075218836594125876004919945945033072197345018516348363084297517646196701177006732497793192566640295282326\
        41494772168505857617071614308624806459418089941492036858684720381133523691686183330155285336183273024190387362649928671799052800*J09^3*I09*I03 +
        361222496708814890615109960314348025887530156243211584132008877397778842875521323746287435838754380072113810286540713979181646245736473113697941168284706119307094623766890016904286074\
        1457460363305749505318353656838701263928339908561069245558433700056276396169895828574942891615325941400779666046141103478784000*I18*I09^2*I03 -
        168545884758655842051777490309456218384457304410475998786903746718924035019773856807577652876653517911769627924500799939861226726082355099613105892640705321336947195631883494379900383\
        2369765861897921649041690242798389408953284967584989105985147071481362345564329187839211460486317435809689897708928979377097600*J09^2*I09^2*I03 +
        115965196698293966457857783571867092571171723501522533254103582874820401095116990930861117469633803033722984682574143113296150539102888947078345860508235687423944770481036297684583208\
        19135645522093933468467737489134866148327998357569114691387896487760373734344954293761421454766666164077418155457195131701484800*J09*I09^3*I03 -
        720151887142319311553209726508699338918327326298183743973325592339898266309996412975927101359953194839662110189831272339354697837754681239293688544769917986190097974096176424085004653\
        645848262235319745300764216687191339176794326905155555160431246605547186564110490813044182766086166071651344670805182781825600*I09^4*I03 +
        522765835443784686132729580244249099292489186266400299469957243253810450110010232478869001724417097463222757475797341763439892247525884912643724472167119275697779442302907828653908847\
        82293646247170605305489581087719662686271050480908834800172455470329153137481301488893419461659947334266098400123619581495464960000*J15*I15*I06*I03 +
        297274604481068635018274065046306894652895389826574335772394326766439938925804289251477369738024743903744760422268949331854776574239668015878710154356862057983432857962079316972263228\
        6207417293950435413419495713228430371784483876382967410219681199357110197062344183728455995156990326647840517396167089302123520000*I15^2*I06*I03 +
        139752214560617800393029571040965097404368437274377094575553731668552079653926848760360284049622366515794886410819784122515636320740992164861778323888734269785125109114973330386195424\
        63521323389234453377337271567058489286476936119471808185600154870297750651261038871315018427500669536598550101201977535889827840000*J18*J12*I06*I03 -
        570649026768413621935559595116935216096145413326644853378870639877146786485108320158207442488454520460259634554776631322907903708942009063618860871136924172246527316704412832310199220\
        28568608935062782104370059763786258027496206684362865998381200803499933653492414371785091720913522224687013268417035815297177600000*I21*J09*I06*I03 +
        242549366374948586172337412092425302843216200283595492336335677697694068090055145194923236688334504187637649545605507514525864442136967070667103113538045480706523701466599339708066498\
        00242700847327072480428767030622554933047172649636155070631391971789930369598786472089505349717843043959468038240612163088562432000*J12*J09^2*I06*I03 -
        919510956902317842008022038713817204023796044817392826187910549274642585234385261589459981532425442944867113662224169908085620661632157210713317156681735625572415403962658182329711483\
        1232874125184482484483005574920050084844843817515881740255807838128763902573467265035789444411000216080649106222567544374161664000*I12*J09^2*I06*I03 -
        204852640006394522589102897671677690108150038259342800610668805877383928441469846553433402153564605419976728420636185626297531597821243824448874851422078416456680260919863979340025169\
        9817508567730789186406382276913610960326264220704985325492092943976174127470479680578412657874727182784332176559549682473640960000*J21*I09*I06*I03 +
        330860201354857133687070269189639641707437958430612312551103107762079622944313830570894258933755914168721132732390463384682301472565673095895821595759691531129732447685792303739194117\
        15627240260206656344347189451536684989892285968825406576991679136479966352596573637568373348880398024251948656523862192781818880000*I21*I09*I06*I03 +
        103616230983659649043988512490804857465692113737569009488978923440886453229828005627127957730610574253716512517815679686042249798657451579130305807220332968949165178080428592861730479\
        8174249328730810658047295314253801058978895145023988954819279060434434330506622788413555110401605095484402088543941680970126336000*J12*I09^2*I06*I03 -
        172619214347184517377103379585040761918335723994689214359339986397844032817548063367816466615633989457675487697692692350916370427079777754714606579665244583401003579354710054461310599\
        0235760949489677556860771293736501262413076662708717184674960108712637929365163812157717200933037004395572316875254815050212549120000*I12^2*I06^2*I03 -
        123139786746756539178565264535135628457409462697152949100882897963266303098257050789609043980192669286337454800569217652780010031705745671912620190206667867955574356176549992948988964\
        1758323907202289247265146995843623972286474632909936610087874688286559059383767963821912454817589388272225186920466576798095632384000*J15*J09*I06^2*I03 -
        351420986623002710491544037572723840269100074556904757965433459464971105424689829101658192225750159667476565521623166533545925572274609751935136649662871371287051013347930989763849623\
        541958682183488416536974410554037149472706724486563805797403187843403410886720413594174496352867823025948910217268765108247615488000*I15*J09*I06^2*I03 -
        748127049440983766356022390321526877384499732969800101568777651701902004925648994503319404762299041566582447315307571394441070977398839977910421384011612832075898305121090464083240410\
        06581033394114195954610551435290561046198086624908048427621514242682077349872521936538750327321118168125358268431200316148413992960000*J18*I06^3*I03 -
        493027054490513815507134673214359086378214195169598636911693783726134371986946572531139975740789917278359684208172658356983864769938363750767093804711466417624051601961427471709146713\
        3323160939020240830383627209633022812572776152565746922202379349279048811397734134096744889402766680802519438243186760935094661120000*I18*I06^3*I03 +
        406807090232345987319391145988029326906007132853138350766721865920398558096923899360373496820198581561858664249338027301230590411807096151872724138400963521455889171075940268429143031\
        24436324268712108192051275359677063197590054620186698669755978333068512038543511902967427620928076868704781806237986104351240578048000*J09^2*I06^3*I03 +
        320597127354777971273630797951227539613150873087891899094507508512902047462128896886173980253529947827031135428972854853752999891648053664768948919625437272329699934130211504916982347\
        98666059939993201096307709069251341716301373144714001522709709356982433512297333254638139004029217313038865491415830212897713254400000*J09*I09*I06^3*I03 -
        995695956130193942498977298177782683814296625608485735909328568354915644811717839323205791465941788978815073568570304688061488631496222033557975444133251660089490958515868717305668707\
        8660462387709638069159013194110416033305062822084693328714016115734791263794739731399810286447161745921755466021760474546286509056000*I09^2*I06^3*I03 +
        143418669389815358703387054094222195423905183659974709870729298495407462454119666527160174842714949317686611522395507110756985777467812053493044229377027178106346299489429862348327427\
        1215455085286241875654607319202771003496130421344308630069582607535095941597264268620157970974374301374810895990536681577096847728640000*J12*I06^4*I03 -
        532093551335654043901405270632855264144481281352893077217919538897397827397598674059387793900792408832340870653964418117320398096850779603441914172794771782828150988349241424379932328\
        7397380801298482111587378548358217974372472066319621726739244916412388754321218634386448987058708070765831545784277014772804197867520000*I12*I06^4*I03 -
        257830659390128308843358857391726156699724205910497824337759463443094341429803345522457259221233374422527755642430906882659858375152997532020170745271490650180148262341311968913510125\
        537894030843483127446422369787704568532380183181564910736930946297959860785120940919171381792728608153203549550036124935667570450759680000*I06^6*I03 -
        386202159421988509780086532474504468921379788052089552273123778525715865075106415106048463351460794610995908771052021134444639867878468210581450302212745870386595496794832468533627882\
        67351189052289813148390974735883501948553109300639820062156741373137173708219311286346298126435724881830798854735445581987456000*J18*I15*I03^2 +
        188281928148397034230788877910579079861236814645940786046763118718527632109083526075965537773837754385362430864690781023895100005620803680376162451293176508137834403727693017850468535\
        16802498952699483299586474640542555446926746944489132664498423162038068885382131885525195574593192814968196505103346866274944000*I18*I15*I03^2 +
        772958256722415011095749165695572713580590804802221159259951649068833416323986078741530863369905215175819321588896108838285932343513120963073819810887701855906699942452171756024539675\
        345825344615874539487087539568305132014314073515752664235677796012935432578038730567523403111142203473529055791095548483520000*J21*I12*I03^2 -
        298908950757688523834095007232547806566119309491390274690807812788550528635130933418656862815390147594210725870608729415732789792834277642192914274337296696820343785044142143460596427\
        19856643899787114439865235212732320979501216935781174856221782548450205716843100509255715262734581000452061997691379967865984000*J12^2*J09*I03^2 +
        519679175443726898130207546015675650068444866749852738594225816015586245065349499584229092416921728928746028635977637239553057986280921459943081083760169295789533421985862840488049817\
        72925020654122555553022538278909206555033361076879282820681613745363380956848804517809632259413747748241083994139578636624000000*J12*I12*J09*I03^2 +
        708690206057450266302772944027632064705222888287007996243724394385687046436865359421019407053581212805167011774833555997780122847349450815554428333096035239057722955370969588574119215\
        3521106632820688276493521543116445376227839132102805888130066400395809252003298209019513389501888712253574371329907468029408000*J12^2*I09*I03^2 -
        193308595982693659041837708946202417685682646973743879545824663010779674773078536334570283123770847359156702206674269159459693240523879498162467509542161333077258092666588327440745432\
        72046586086481415330701626330088476684241816615804223362521073647596536080171052307858669174402851170100102020167694190637520000*J12*I12*I09*I03^2 -
        430502739471579887986934585681573499043443021007923028039404751226627876362492997163271824819018678800893400064037748610103678112583117163656656112021764748028194961736652103644512943\
        83000748387995679592335154894091091505857156848643133412657975443283193139688867033408192944027622995095286514356442727033475200*J15*J09*I09*I03^2 -
        251655919970695743849673762107666590745029112092558650364854838307241557537476702420843237703656165285867028890492942700092269944953286994197999276885994078204117699273264463911734438\
        35042011794032139778647571838184123201821878947520284169741670687286424563140958569357447189690462733258577408263786662899766400*I15*J09*I09*I03^2 +
        225464065018082535229067576106797360921946538830981836892152064725559054235988657349774617348772147008720298069646036467147334746769457010561179176722542113216715744543919059938661384\
        68258774860614627943420665804176372976262271039314876589232335800801773969931364649688344903493561347293202185862335730692838400*J15*I09^2*I03^2 -
        146236896533018616449956792106477618612906467029628952776091335694639380318059826237079111624091561934156176034648127833753662506030636878897892769027661545226558522663715927829503201\
        68121558865917218783017226889471469783244468740627021136792472430241748720518982071130398811572303835929728396510162482600371200*I15*I09^2*I03^2 -
        465831198242267186134478900507587939678518951003269984821813208604865038375362636965383800972716864277281187089528740221811994392527063897406193731997432133117776926626550882832508322\
        6227906424424247704909178866731897623274425666307548481467005043489334509206723978396912950780703588400350738649232381054437376000*J15*J12*I06*I03^2 -
        119051873977664937220621617116762399382658867823750013804751810889176336811054918855156712324000897461851288474562779060120924607345515606726489128380819020671969560969506355036895692\
        79734014671614058990404633034363785853555140981562122343217038647684461520599532657153377472031829320580884297458877169950469632000*I15*J12*I06*I03^2 -
        433442796385446484716701331059911288399427675283927418955818933860538329842968357175193595104606711309767879936363265646469023675626857427844565636686785732279388960617156617038556206\
        03035990955859744236276811240818428095485354516019619351569905578188008515125634052080763696852052482209328749452609201574817920000*J15*I12*I06*I03^2 +
        155410321284926418897099411492558092806816605683306818834838162446579232237975100072047915811448476610364916152532309148872865133287544859650128662306195216413769699608267991498385504\
        43908773321139175731884891479009820070526839502905213818395234755956320208339176075239802516174607442837279100186962848333755520000*I15*I12*I06*I03^2 +
        950033978702395998658183342567316522072465591841732085830057955650012810197050490134807003709442658001894909739843077346556470633203947784881256517078851897783378489049181741570428110\
        973076802570675856516604232543139200882305755768385561373482322933486165815348146300282203856512198602694101228089536318078822400*J09^3*I06*I03^2 -
        729083370062311653909608711069350004155689133542328308907116310541351832785845617218853280373921907192500065505034673715988280182309126019506732329707707069043513166311588423805459561\
        2212681976082549435787661517653932256796138830437079960599018158661650491807913684763847205777443979560837031563871653987604928000*J18*I09*I06*I03^2 -
        464790385706004184083880721395249865266467592860516018671873080737063078536394813255246852555609327355531284538261997282889150705586627708504944496058930979328687622116854002008719112\
        657224131979177460212382579704846810759205448599902981439220719138427428947686048792703090392512383414444759433333216877041728000*I18*I09*I06*I03^2 -
        215916438575647960127415859578448713199515687182293462311717357563080996145407664067826287814846411602110904733928112760841064846291386058274148669088799673372154489288388559032210118\
        6549128087187259088094878154292271109378933504455023665615195407520641923653232345129561615247985827284321168671188346735973926400*J09^2*I09*I06*I03^2 -
        374648596376538915266920233579578217138820452403420189402114088087755181960131753919688661073488106050657697130533172762685464574835519424440411317503296959742820647807028910210328057\
        204471756705219929831622222323310190740200480691064510378154389626271882695050865038584134127344460517131055266704534517440409600*I09^3*I06*I03^2 -
        638546940095072165053985424353404634696008986274270549238065230978772981519263425566655989750170992774228351006739929608413139855324110047909886108122898205135212743083999355025664194\
        61469425230828719927427915811927628217155645772612717532108067486590397238534260517962039769111617023406499502471644192234455040000*J21*I06^2*I03^2 +
        304203289718015529182709753189715316344032672280451963675985901755682790857478334395386602729404140292935184752752494266580442406115006835293722254340258786612835529497441808209529188\
        3224105122807447888435811653487114133456849935977957185406663986824350424041326195581469897987593599888031371412945574665008568320000*I21*I06^2*I03^2 -
        103878986747313696367472686590202236698103121094889633033885158104259764121556043239170675005103009485952004354797343678476810607121377794350303963367990836872815451283200813409974212\
        2355766793923094535124043682723345424592579414204010167966538392753082019406687209874521728320831054360301185842597897552748888320000*I12*J09*I06^2*I03^2 -
        694101161326365883127158824886568621857140497523167562428750178856094197701614843288985633224787826896820751746807937859137514126500120317614496220897673769276140768399536516511362547\
        443364532083161443775967119540543118083642386799221023134418445386323738364802711549329731483178401386583524849817226971529182969856000*J09*I06^4*I03^2 -
        136324434614605680794337423315397329828115055699142031984983488914673372593735341834612219293945355474957845580662078891863374638654550659678342272483744083794118176851556400090692436\
        4814398876137076288252499008233021899047028498742943074698316244775197128531054355714284240068418999107190445391750457836660053905408000*I09*I06^4*I03^2 -
        892169968689162661463031046693347837684859706523702900528532296964443570386788784320832946754602505307473671395264800065171568751241839630308811002859643273518299827050438251498253423\
        973840265498024103202302632334178305307953557840358202681139781266542077184494755287954251928895314563326033012195988705280000*I18*J12*I03^3 +
        410743599818461148267736023756315563417463539087839405702988098487791450219991163094401369061428955277556360443762273295736478820036946843398862219280399303525602756952259083708894458\
        8309479225697445847934143864159162140637866943026538099544806806908001437279844932205104791905455947553293899502961134587360000*J18*I12*I03^3 +
        134378628894750595167091416691272353064522262044670844103871117995474153967400447279841361547494404933623139339361998972969255884458084411801401777992979483011378483401611877957718189\
        50047397923252394213266843190693682651688702682769582711672643338076393145248222513492464276767438308159798767662819569194880000*I18*I12*I03^3 +
        307042177862893907378039045004550416985687899252884659002588560409539624668170399570272142944521457143927661803338398385031261887933440367458496514952010365727026237058448580686946718\
        14913201169422598283253112119234194451158295869632209726159898256717099068967239687963521847523339360677921962576997809019200000*I21*I09*I03^3 +
        453760503721192888932565394854073576911883797572867676963381942984140772917400679704616330001801710110547233200806780682829089258001330574580281786065049953663834849147185329473698681\
        20788007436191779579413268211693957392583994409181990268945275082428305014669606830802016626204894934361341958738839868171640000*J12*J09*I09*I03^3 -
        634713872257315894748355724337373515110668068518771230222015983819956337400124382718828621738806889169732878177423876770870782060599092311882197454207511755758103716376301529696541592\
        7663298343611768841423450821039830783475660508616556621160125304329382165651077123750176014499293408313399811174926473460120000*I12*J09*I09*I03^3 -
        332782624527926924903721347366308384456246838227728670078885651059923407656864413340544656830999486803829926450568168490573105618223560529791041674498684876693294859462774897164727327\
        482950308421517992597471784148498650806341037599871799522042761407011457655310532637182710071173979083904388762209042321995520000*J12^2*I06*I03^3 -
        336412865127818211533551314767937047976887319194120258489840005383361123013858068742480033293667429355482206873007554045779009708932043769923258702870631588475930095887342062727545047\
        2342454806573973112499530818189897134455583217212649015609796229440560073718942037561629479430260439331592971087566055846871040000*J12*I12*I06*I03^3 -
        167256297500610452380033670303952416347181885875226280615088284109480798106301919782412907101949589848482622383462144277772974864900334604844211574297689416746714657132102164902804439\
        3829071999074973217716769463250822039156559058619383400439082909204876372939042151984809780597404622157980250120815866466337331200*J15*J09*I06*I03^3 +
        116979881044035174161390115307588496480641404626016635392119861271938020577437971411724791172714863923185390602865704565398218973861926099375462565794266890277827932575261681208259062\
        51987258823778968914987836797453752820955376943200559161239976766198847680597877940631776607760189107955536601431098964821086361600*I15*J09*I06*I03^3 +
        128049866669465171064167078047798110779243334213624167853196134490407178516193906586303915789726658032347094974337255777484969822023801529926105437977869212069740937258150629651118763\
        70767897853826135115664469976533491569090172145119530090010489063132607806028741107274054216230769709178572048129758520801356452800*J15*I09*I06*I03^3 -
        195041335837708923880742239501855620742258551012539224664273297492440621227110041856829296031304543228853357667209996475930366454040424198921961290789285525378785209213889842088793538\
        7407848077313618097830276648873570299576571378642498696333626546351934344105580498065989722546634310268036666799603015404340430400*I15*I09*I06*I03^3 -
        845201215862796710869585797223509741887610947610146987577850162327214373448144383385686309010130888909374291908802847530393882168463605628214120635772616886075236017435354937021767748\
        748909637850872344962134030275853325839559882434420549230336368674976211362177199956264776804971470886818113065433011952326952960000*J18*I06^2*I03^3 -
        516602425132820791135721331827076972411763142225763712240030819219580043692079358737736253670769774611819160880308084017016858363385323563793005639185750424108067888000988927845468846\
        69452486459172234426947086736807287128990971811708640040361618376865082243671082980950059267311822419182188828680690552746722585600*J09^2*I06^2*I03^3 -
        841395164166278392352397404461485377013448332910807695863387363784514029730949003568225769120210908645866100178491519332000250922439715046893986653603763331454754846467531816845693976\
        38183030563599881353396373591759244780834047239774945143587136977572954480658867101389066850295291119711175554585235966003310521600*I09^2*I06^2*I03^3 -
        995468527304889865789059058441727692452629660280562685613401029633088913877298138272584237551575092162275070139729211438655959422426568771118983910357098837974985807541145442168903850\
        2315150495646365244829065413135237251457165044437423961739019204789344117735327318900352617786335057167951707614782030546683076526080000*I06^5*I03^3 -
        517200192042771564521653155343685925656024341168899761720829833685160360276319933688361065098042697386633534097787310608235114191179473052664716499921136586142307422035359194494974194\
        68582064831419887198112810779504299664507368566164811260355205669159245702956138881735514416594222276986264364346620723143955200*J15*J12*I03^4 +
        773078672042240120823764580300739306308482873353604523043880545865516822634299808575745527838193939948226430665038403517009811483316824139660199535453000573165590562318266780794280144\
        4554592676031135740556405036506042328563195514551445215487725328240555647665824221512335192410240432413419324028030774568121600*I15*J12*I03^4 +
        163187497352099544737771422742838311125173456565272242867707122426030526069554461611385054736382332646694543226021873453560800250237148215998857729674431381417609103300027191036204020\
        545155437545569560726562590587916600271192085568085885138507773842237886920055356786693942839332506663252122750041848167356571200*J15*I12*I03^4 -
        470180919553338479251099657017851850365541424158107386003608344847077010028879767953736465896837958209337828214168816701228864345725791998413585192469934232670764010398021481042471556\
        04423212139929010810304486906246849386302641243378626908700081101551830987391949243135590516088013817157228501099752646255953600*I15*I12*I03^4 +
        209579056729970912566697977296953358591918058489808881528071547368497335986365979961359357339411774301657273035088831206913591566325064559848742950219913608166489097282975306987621485\
        6648957333468077966780576036514960404036718632164099153590957747686508811650794497016445818139284605463983258148838274998240000*I18*J09*I03^4 -
        253022297685304956679902972348666216852332614672694092225975196732761384998476696936318665869895099507095235010117599598607111656843496185010426641783750014195007289771707903787144596\
        67770800080347670384203482413782384823308913596005839722035629179321924926229159675244438471865570592943266316903789045880440000*J09^2*I09*I03^4 +
        281258020300149572902730597727867269333510365884364787519431140990828983298956486656557122273744764672633349416311415683295634318109631647174305300017403266941019909795238748100521490\
        2302209302777257518028190070441349351743758166136701290747055084670640749085921282242449088076876475054232019504532195367904000000*I21*I06*I03^4 +
        700989848266384849570181543658304019751261718637036826044403743421159722341225887941048579319228877595128548209958416494690632559185412129660290655725135179228081261432607860592301238\
        4201209217303617847097867960949460205701952753989476660827158307407917619964092719129359696518905891730689965898134409063539737600*J12*J09*I06*I03^4 -
        481138200920150212725406280316177105019752877168268472840141141154804479389454069505561233064846692679087352054889490838294004095950561562140745193049266160491109104872180479680796368\
        5601625026451034553431232594900195550503295478462056420227223605247970051970426061709336514314965164023753992071177668051725276800*I12*J09*I06*I03^4 -
        278748144145716655407537567721739449108476707458756056301295177523637434184306604976159409684119324331453960633343696408586524031376816807147589463187605232198417883724945417343928896\
        4973334675685812818492061006474513271465358312497933763119372640183710062872870838170502321952306585323252969881711833620519869600*J12*I09*I06*I03^4 +
        305795269365805506250972856902930162433195772215786909729591613953283531646490655022077827128772584683775101438363145055229286457156218396729126679047871248820879825534667161130541030\
        6365284548036075741157788749513125109004874087435747019663017483716662934044045202247353831383541736744773604063822254845496219200*I12*I09*I06*I03^4 +
        390615249207226212589256302258356931310541739565606694688083375364854503525869291973530776859137299899275197995861762120044326313536876858021385143946935091200034724348644646025937371\
        775770929354433194691831875074717597479259996278534020865535050498918670341099549308954771439905528949099923380842586854590155129600*J15*I06^2*I03^4 -
        621694167298553302798474330630292256965681399432660976003397035409919716148036889748907789221398999165562231518657300850014866755290437770912032410204434494368797885362400935033712666\
        945804725474222736627158028709003871491574798016515932896308689787765520793395652572494132630504289066680057272093425529890759660800*I15*I06^2*I03^4 -
        470016359870013745082720973684670161939865217488477152721437775624960758193877839485428158200678135467401659878681358299420139814897526840203057196185523586898456174222417277381935597\
        4131284388036120836187881682096194044924682180574414696273517692625518176837881869428081997499053031900768766184597839523124390169600*I09*I06^3*I03^4 +
        134465165030418755487708102814794795411104555095960683720505247059097506287539454155912065264508647442039806525862714449894760445393876675194406926626122880473777478853399794666489668\
        61913321306224526038257554357418803382563920590872191460718912114684461988414639900953029489938555348679899513198812727067747200*J12^2*I03^5 -
        842566583300712180391876837901862845162694648464833286922131545481826391214024403239178708077849860001450723648795188696611230774163648010578166768279963092123158277063265840535394186\
        60432709074776605007199925437579744576094550830269991026514699804483506619691646399342214498016213509082413727751326639239176000*J12*I12*I03^5 +
        115016843344890805256554918396430367170518993415247066456606952964341321970613446939873424221202484754327722795237389571220604076972570979280067909018085205086999393282133185660100355\
        121159514985484091608992934423869789535327863531091938281687995971398668025670452029887656436801221858002770373822632428893836800*I12^2*I03^5 +
        387514360335023489250181064784212868543034791615752632344424211733116413107995966196002080118441065867424842337525648580751189077995134012032576414978484289500856327200521489270675570\
        75146056149836641402265359067810857777820124818351510459261879460117637508626982044225142169105055943236409566778066898805438800*J15*J09*I03^5 -
        214431499761296920704806961217577359137792587447339994380081388551142055005234301156752407562338235781823489582373774262752898684907611957344069944913309716325426377050352435916954853\
        5611447250902003502414088009076887791457173515727742684807376551431495001735267327158099804918273141138797389309091226783390000*I15*J09*I03^5 +
        117711516674001252436994602756993567971631117757848106617555734975669673459713134036629738238930435709467385899148097451535918627132889796282790794782377321904467578930496046338171200\
        73809299824922504381258275905305735853636268742232824384699775971257965336950404159413232655490426804091314933439454661195840940*J15*I09*I03^5 -
        141347178163105771114921935076615153805540175318843432448919655009640181994311784580660657127587135353827593632218146285634302036099287170453718037448875285483905721314213806701188250\
        91945890446118200137959992000299579079970380258435818059900058173797700748230529678319799031725165691639252939760001112108543220*I15*I09*I03^5 -
        422741356121141437186590273454536916263859454624788035284503132860340963334979623076565372427294672284919182274080411679403889683228328712902991251219616141879529459807639026082591945\
        15693587553301493656132792218479619198379174677456339798869365957537945547488575099119280226322969561230433813062549300761605280*J09^2*I06*I03^5 +
        227896828697199642938984874331056668721189303507584683585225631202220975357261092176142338074658826836278551923304866904571611432552676299435660242906094196928186518273968204431188112\
        695299487815203411010380163715162332991615659547282470488309038978780161450084285771296953737613493903215399801842742075633209360*J09*I09*I06*I03^5 -
        110249352010098420489199556178603417495975981591459976440989948012658684305957200574212660852977250240822716764284462110632484989840253705230849701144761848742444452309058940409919991\
        876028803165966962986734725176327423181252486888016897466280199275688329487763483842385551850307092158429807585908920688298285852800*J12*I06^2*I03^5 +
        515905561967425274328756376797899363882208146152438217139216990202257506031406510384759300890757687439335453662134611790393405149025669806194134444138516371295910595032884874582950278\
        51997368245655870864716215596893618688434657245637552999078315838227802806253943615712697150259614448010829426879259976697427673600*I12*I06^2*I03^5 +
        877083286675053304928444893612166054208340761065725572056124258308540246791859886070323586450926934554322418172289160571761627308986553557700430771862230820856696366435517582210120980\
        10785300785841759652281397250108732308056078296345408840384155269465592875532435748908324379522542140783777669834521681434636329881600*I06^4*I03^5 -
        126199233479167594781437090606307883677409390478139638297033012567501612195646566950383563793026257610474159911383982067503464917781602944527619578518378127421326393650420532071548097\
        025561156112901169884514645644553038165755355116311703521720587570242046989264476126861800296910439029257626124252412167840000*J21*I03^6 -
        689324720523721934841548391639092205669202637352179654083440135364658665835240524149519175361121547993445874903231140074595550828115085177572016796814543742435952017698883081370059842\
        1092179903920024173714093678569372639053449048558514885693877293036851460844289685447781522875867777184806036411558737039662840*J12*J09*I03^6 +
        598275800431069695150987448786168376838397750022644703937771690235226441446743097865302209588809130111483984315805496925737643643958093651839565868768847519633210724173700130432172489\
        70820882087737871992175062110254079728145993049915975035264734367065102939455310635779119424884938350258796494727003896207679040*I12*J09*I03^6 -
        961447098925921067217985887241817104242314772019233453756330693288255718235973407933403162447558415534893110489311317724876174465290685196449746807450852981408223543222367472109048660\
        2784673442226227070078385888455950821310577129182621059276312432818976196123448351726742093491097278997423798948705077186623810*J12*I09*I03^6 +
        268248724493969328845756060040594487613768822119099489573038192793002347310855667850687076827788180470367887148057909204088695051388847599843401598070113892469135885536897190077761775\
        48457327486975832869659933133067558775948055586616774241231430561060673702158957912439080605063012425733856519743933923928869780*I12*I09*I03^6 -
        365975570152853268352032815777041078444862404042766463306866769144050195336117981895102216828176058381052473946626794305615786396886489327037257951098104606073508460015979390867456306\
        8772258852524512547550530374465264255691238275382852285385309099285237988230388971725086310854132919064332167267834643912888527600*J15*I06*I03^6 -
        830062940129034911335162394040058915568424078892949773753218535199020234818009071132771601458958335216540473832586004972851969841314189150338452023349276834201224471935158471723503762\
        513439851339401424395259804910259760617540589332859134368325945851164717527852822754967563086107878859552389760848063106822681200*I15*I06*I03^6 -
        105683574389724704746038493897758723793225010295405439771765308082115140400850174263117067087354301534731528205643561023899694267858342570437759080328134163345661082447200552456623039\
        03447952801620895963871578598229054011379262005161541333832146048581262717490248322080140877578428235180246538611283696240617686080*J09*I06^2*I03^6 -
        365840375788756477575647075460957375979666238456657753072522458036258634896809141244067377099736736969484660228233717344197939992738657227356315318344459231568250105668105963408851227\
        2010413435035976971161893336982015777379263498135827923102874521635203607879646839983645610699818845743106954341250478072566000*J18*I03^7 +
        959203037651076642985816772000519836577598839647886268365326803957792010143765172124453537143607815522237615803936887147993586684401867238529634812704947724642829054004440432214032718\
        458690500206643410085711823188275255617889945663434893843770936378473742054917724022958986146595884175531184217223218578374000*I18*I03^7 +
        459272577603646862955253688912386923982249825791489788250455508485272005101142581782830061781380198805686698509319810489391552357979839899553867247885950485245389375919728558834545141\
        5748398416199181214516700638581256356000920650507665535000901621370054876360069947887519520758400773198886842917444959904550293*J09*I09*I03^7 +
        721176172335276767377992354665574109061106497059435807288734164631728103898299678696704915745940128548062285077502187158680211299278114440260729638172505846468459469125422970854760641\
        336482339784645783759167104452045694732068194366274116976690290907646280767973644014860500712780991355154434233327779973881799*I09^2*I03^7 +
        574370782671868676979210756202316478822491302167387076640131930161753260513959751918328362984402703774089782172859480629557903768921172054981330245182959245783371046203469835677234719\
        567020660750311999675449154434607069024091130502482917876840218773711858342376242853583557453249768665259331618608070942639351400*J12*I06*I03^7 -
        236151701032297340567997157031722157327127111348715868029329279608327377582886187134515402397242313527780376447241607319747743590178370876974725807430506913886851908210698137456405592\
        8985967009694179388622194558373626908921290103405201266556979009634058268746762273158501787903943090664071915475776949514288493200*I12*I06*I03^7 +
        127060395653617433106007978817854336411128735069962147064532760400101308385126430393533083860653386678862026380246760665423803306046301864700092678371001331440566785159981185397837404\
        2250461483835440778326782478240946486045503506346580260779831798037917953000882143392199463165713397124282756315619325955543580*J09*I06*I03^8 -
        211905278871575681191415036735798804372854316696848269398975194147617174850135690010268837767817852556215448281413246169934757552411331218933787923543308937396599132529643481004346939\
        941830574521911442303611687557340549841293090805304395932709709634899019391223988016333096132258020111021197466807838832306887620*I09*I06*I03^8 +
        101837036348256989033197295126844340065597136929607630684991876227565527708803794148722091504607258299423434951073176033202968904180580081726729950538798266338236357852138773601651291\
        626986914535228047796133958761475857415042303682740541640635989496113002934915548459699546875891398893832822507946072585880000*J12*I03^9 -
        244296195862086481684043953787862191741619054561678598508364050355608853665950672574988343218825831079519736446622918793522840555595823608325866907174862842251531635536676409853461396\
        8245783546237037450060079817838426227594342970882092361518091321211603371602643879841352822679609737569333260102571648354493853600*I06^2*I03^9 +
        229566611867496494043750403784533286149845057430403045786686219324251310243759802211082933228924412762073092491718698873092608779049902070398643529023853028605702118723733254642016081\
        83731884541425172778626904307372611439610571459886425735256721175568736748270735459043017817193000788856178158698221028360000*I09*I03^10 -
        669787631965804502565828639620813966490379977119325868460466600875575874570015688375720987705283563580031498627229571561752655519709689613348946438987587482153403495469308808925840984\
        5238104468827088023436155178083680546973980038105757682600794000288393866978720199788133419124146230783822915374437241056480000*I06*I03^11
        ],
        [ w div 3 : w in [ 24, 24, 27, 27, 27, 27, 27, 30, 30, 30, 30, 30, 30, 30, 33, 33, 33, 33, 33, 33, 36, 36, 36, 36, 36, 39 ] ];

end function;
