/***
 * Exported intrinsics.
 *
 * intrinsic pAdicCayleyOctad(_eqC::RngMPolElt, p::RngIntElt  :
 *   Prec := 100,
 *   gbasis := false,
 *   LPrate := 10,
 *   randomize := true) -> SeqEnum
 *
 * intrinsic CayleyOctadPGLOrbit(O::SeqEnum) -> SeqEnum
 *
 * intrinsic CayleyOctadCremonaOrbit(O::SeqEnum) -> SeqEnum
 *
 ********************************************************************/

import "verbose.m" : MyBenchIndent, MyBenchStart, MyBenchStop;

/* Ad-hoc field completion */
function pAdicBaseRing(Rg)
    if IsField(Rg) then return BaseField(Rg); end if;
    return BaseRing(Rg);
end function;

function pAdicIsPrimeField(Rg)
    if IsField(Rg) then	return IsPrimeField(Rg); end if;
    return false;
end function;

forward pAdicConvert;
function pAdicConvert(elt, F)

    if elt eq 0 then return F!0; end if;

    if pAdicIsPrimeField(F) then
        if Characteristic(F) eq 0 then
            if Type(Parent(elt)) eq FldRat then
                return F!(Rationals()!elt);
            end if;
            return F!(IntegerRing()!elt);
        end if;
	return F!(elt);
    end if;

    return F![pAdicConvert(x, pAdicBaseRing(F)) : x in Eltseq(elt)];

end function;

forward pAdicCompletion;
function pAdicCompletion(F : p := 2, Prec := 10)

    if pAdicIsPrimeField(F) then
        return pAdicField(p, Prec);
    end if;

    FLp :=  pAdicCompletion(pAdicBaseRing(F) : p := p, Prec := Prec);

    return ext< FLp | PolynomialRing(FLp)![pAdicConvert(c, FLp) : c in Eltseq(DefiningPolynomial(F))]>;

end function;

/* Remove monomials with zero coefficients
   (in order to have good degrees) */
function LPClean(f)

    Prng := Parent(f); g := Prng!0;

    /* Multivariate polynomial */
    if Rank(Prng) gt 1 then
        Cf, Mn := CoefficientsAndMonomials(f);
        for i := 1 to #Cf do
            if not IsZero(Cf[i]) then g +:= Cf[i] * Mn[i]; end if;
        end for;
        return g;
    end if;

    /* UnivariatePolynomial */
    x := Prng.1;
    for i := 0 to Degree(f) do
        if not IsZero(Coefficient(f,i)) then g +:= Coefficient(f,i) * x^i; end if;
    end for;
    return g;

end function;

function LPPrecision(P)
    lst := [ IsZero(e) select Infinity() else  Precision(e) : e in Coefficients(P) ];
    return #lst eq 0 select Infinity() else Min(lst);
end function;

function LMPrecision(M)
    lst := [ IsZero(e) select Infinity() else  Precision(e) : e in Eltseq(M) ];
    return #lst eq 0 select Infinity() else Min(lst);
end function;

function LMChangePrecision(_M, prec)
    F := CoefficientRing(_M);
    M := ZeroMatrix(F, Nrows(_M), Ncols(_M));
    for i := 1 to Nrows(M) do for j := 1 to Ncols(M) do
        M[i, j] := ChangePrecision(_M[i,j], prec);
    end for; end for;
    return M;
end function;

/* p div q, the polynomials  p, q are assumed to be "LPCleaned" */
function pAdicDiv(p, q)

    Prng := Parent(q); x := Prng.1; y := Prng.2;

    if IsZero(p) then return Prng!0; end if;

    xp := Degree(LeadingTerm(p), x); yp := Degree(LeadingTerm(p), y);
    xq := Degree(LeadingTerm(q), x); yq := Degree(LeadingTerm(q), y);
    assert( (xp ge xq) and (yp ge yq) );

    r := (LeadingCoefficient(p) / LeadingCoefficient(q)) * x^(xp-xq) * y^(yp-yq);

    return LPClean(r + pAdicDiv(LPClean(p - r*q), q));
end function;

function pAdicGCD(mindeg, _p1, _p2 : LPrate := 10)

    p1 := _p1; p2 := _p2;

    hprec := Min(LPPrecision(p1), LPPrecision(p2));
    R := LPClean(GCD(p1, p2)); if Degree(R) ge mindeg then return R; end if;


    lprec := 1;  gap :=  (LPrate*hprec) div 100;
    hprec := ((100 - LPrate)*hprec) div 100; /* Start at 1% lower*/

    p1 := ChangePrecision(_p1, hprec); p2 := ChangePrecision(_p2, hprec);
    R := LPClean(GCD(p1, p2)); if Degree(R) ge mindeg then return R; end if;

    /* A dichotomic search */
    res := Parent(p1)!0;
    while (hprec -lprec) gt gap do

        prec := (hprec + lprec) div 2;
        p1 := ChangePrecision(_p1, prec); p2 := ChangePrecision(_p2, prec);

        R := LPClean(GCD(p1, p2));
        if Degree(R) ge mindeg then
            lprec := prec; prec := (hprec + lprec) div 2; res := R;
        else
            hprec := prec; lprec := (hprec + lprec) div 2;
        end if;

    end while;

    return res, prec;
end function;

function pAdicKernelMatrix(mindim, _M : LPrate := 10)

    M := _M;

    hprec := LMPrecision(M);
    R := KernelMatrix(M); if Nrows(R) ge mindim then return R; end if;

    lprec := 1;  gap :=  (LPrate*hprec) div 100;
    hprec := ((100 - LPrate)*hprec) div 100; /* Start at 1% lower*/

    M := LMChangePrecision(_M, hprec);
    R := KernelMatrix(M); if Nrows(R) ge mindim then return R; end if;

    /* A dichotomic search  */
    res := Parent(M)!0;
    while (hprec -lprec) gt gap do

        prec := (hprec + lprec) div 2;
        M := LMChangePrecision(_M, prec);

        R := KernelMatrix(M);
        if Nrows(R) ge mindim then
            lprec := prec; prec := (hprec + lprec) div 2; res := R;
        else
            hprec := prec; lprec := (hprec + lprec) div 2;
        end if;

    end while;

    return res, prec;
end function;

function pAdicIsAzygetic(AzBitp, AzBPts)

    Prng := Universe(AzBPts); xL := Prng.1;
    SF := CoefficientRing(Prng);
    P2 := PolynomialRing(SF, 2); x := P2.1; y := P2.2;

    xy2basis := [1, y, y^2, x, x*y, x^2];

    Mcon := ZeroMatrix(SF, #xy2basis, 2*3);
    for j := 1 to #xy2basis do for i := 1 to 3 do
        pol := Evaluate(xy2basis[j], [xL, AzBitp[i,1]*xL + AzBitp[i,2]]) mod AzBPts[i];
        for k := 0 to 1 do Mcon[j, 2*(i-1)+k+1] := Coefficient(pol, k); end for;
    end for; end for;

    return Determinant(Mcon);

end function;

function LPToVector(p, n)
    x := Parent(p).1; y := Parent(p).2;
    assert(Degree(LeadingTerm(p)) le n);
    return &cat[ [MonomialCoefficient(p, x^i*y^j) : j in [0..n-i]] : i in [0..n]];
end function;


function BitangentSystem(B)

    b0, b1, b2, b3, b4 := Explode(B);

    return [
        8*b4^2*b1 - 4*b4*b3*b2 + b3^3,
        16*b4^2*b0 + 2*b4*b3*b1 - 4*b4*b2^2 + b3^2*b2,
        8*b4*b0*b3 - 4*b4*b1*b2 + b3^2*b1,
        b4*b1^2 - b0*b3^2,
        8*b4*b0*b1 - 4*b0*b3*b2 + b3*b1^2,
        16*b4*b0^2 + 2*b0*b3*b1 - 4*b0*b2^2 + b1^2*b2,
        8*b0^2*b3 - 4*b0*b1*b2 + b1^3
        ];

end function;


function LPPrint(str, pol)
    return MyBenchIndent("") * Sprintf("%o of degree %o, at precision %o", str, Degree(pol), LPPrecision(pol));
end function;

function LMPrint(str, mat)
    return MyBenchIndent("") * Sprintf("%o  (%o x %o), at precision %o", str, Nrows(mat), Ncols(mat), LMPrecision(mat));
end function;

intrinsic pAdicCayleyOctad(_eqC::RngMPolElt, p::RngIntElt  :
    Prec := 100,
    gbasis := false,
    LPrate := 10,
    randomize := true) -> SeqEnum

    {Return a Cayley octad for the ternary quartic eqC defined
    in the completion field defined by the prime p}

    eqC := _eqC;

    PXYZ := Parent(eqC); X := PXYZ.1; Y:= PXYZ.2; Z := PXYZ.3;
    K := CoefficientRing(PXYZ);


    TT := MyBenchStart(1, "a Cayley octad");
    vprint G3Cayley, 1: "";

    vprintf G3Cayley, 1:  "%oOptions are\n", MyBenchIndent("");
    vprintf G3Cayley, 1:  "%o\t  Precision: %o\n", MyBenchIndent(""), Prec;
    vprintf G3Cayley, 1:  "%o\t  Randomize: %o\n", MyBenchIndent(""), randomize;
    vprintf G3Cayley, 1:  "%o\t     LPrate: %o\n", MyBenchIndent(""), LPrate;
    vprintf G3Cayley, 1:  "%o\t   Groebner: %o\n", MyBenchIndent(""), gbasis;
    vprint G3Cayley, 1: "";

    // Randomizing the curve equation
    // ------------------------------
    if randomize then
        tt := MyBenchStart(1, "a randomized curve model");

        SL3 := SL(3, Integers()); G3 := Generators(SL3);

        M := &*[ Random(G3) : i in [1..30] ];
        V := Vector([X,Y,Z]) * ChangeRing(M, Parent(X));
        eqC := Evaluate(eqC, Eltseq(V));
        MyBenchStop(1, "a randomized curve model", tt);
        vprint G3Cayley, 1: "";
    end if;

    vprintf G3Cayley, 1:  "%o=> Cayley octad computation modulo %o of the following curve.\n\n",
        MyBenchIndent(""), p;
    vprintf G3Cayley, 1:  "%o  eqC := %o;\n", MyBenchIndent(""), eqC;
    vprint G3Cayley, 1: "";

    // 3 bitangents
    // ------------

    /* p-adic completion, map in it the curve */
    tt := MyBenchStart(1, "a p-adic embedding of the curve");

    Qp := pAdicCompletion(K : p := p, Prec := Prec); tp := Qp.1; AssignNames(~Qp, ["tp"]);
    Rp := PolynomialRing(Qp); xp := Rp.1; AssignNames(~Rp, ["xp"]);

    phiRp := func<Pol | Rp![ pAdicConvert(e, CoefficientRing(Rp)) : e in Coefficients(Pol) ] >;


    Cf, Mn := CoefficientsAndMonomials(eqC);

    Pp := PolynomialRing(Qp, 3); Xp := Pp.1; Yp := Pp.2; Zp := Pp.3; AssignNames(~Pp, ["Xp", "Yp", "Zp"]);

    Cf,Mn := CoefficientsAndMonomials(eqC);
    eqCp := &+[ pAdicConvert(MonomialCoefficient(eqC, X^i*Y^j*Z^(4-i-j)),CoefficientRing(Pp)) *
        Xp^i*Yp^j*Zp^(4-i-j) : i, j in [0..4] | i + j le 4];


    /* Bitangent computations */
    Pabp := PolynomialRing(Qp, 2); ap := Pabp.1; bp := Pabp.2; AssignNames(~Pabp, ["ap", "bp"]);
    PxQ := PolynomialRing(Pabp, 1); xQ := PxQ.1; AssignNames(~PxQ, ["xQ"]);

    // We consider the line y = a*x + b,
    B := Coefficients(Evaluate(eqCp, [xQ, ap*xQ + bp, 1]));

    SYSp := [ LPClean(E) : E in BitangentSystem(B) ];

    MyBenchStop(1, "a p-adic embedding of the curve", tt);
    vprint G3Cayley, 1: "";

    tt := MyBenchStart(1, "a bitangent polynomial");
    if gbasis then    /* Characteristic 0 path */

        RK := PolynomialRing(K); AssignNames(~K, ["W"]);

        Pab := PolynomialRing(K, 2); a := Pab.1; b := Pab.2; AssignNames(~Pab, ["a", "b"]);
        S := PolynomialRing(Parent(a), 1); xS := S.1; AssignNames(~S, ["xS"]);

        // We consider the line y = a*x + b,
        B := Coefficients(Evaluate(eqC, [xS, a*xS + b, 1]));

        SYS := BitangentSystem(B);

        tt0 := MyBenchStart(2, "a Groebner basis");
        GB := GroebnerBasis(SYS);
        MyBenchStop(2, "a Groebner basis", tt0);

        f := RK!UnivariatePolynomial(GB[2]);
        g := RK!UnivariatePolynomial(-Evaluate(GB[1], a, 0));

        polinb := LPClean(phiRp(f));
        polina := LPClean(phiRp(g));

    else              /* p-Adic path */

        tt0 := MyBenchStart(1, "the resultant polinb_1");
        polinb1 := LPClean(UnivariatePolynomial(Resultant(SYSp[1], SYSp[2], ap)));
        vprint G3Cayley, 2:  LPPrint("=>", polinb1);
        MyBenchStop(1, "the resultant polinb_1", tt0);

        tt0 := MyBenchStart(1, "the resultant polinb_2");
        polinb2 := LPClean(UnivariatePolynomial(Resultant(SYSp[4], SYSp[6], ap)));
        vprint G3Cayley, 2:  LPPrint("=>", polinb2);
        MyBenchStop(1, "the resultant polinb_2", tt0);

        tt0 := MyBenchStart(1, "GCD(polinb_1, polinb_2)");
        polinb := LPClean(GCD(polinb1, polinb2));
        vprint G3Cayley, 2:  LPPrint("=>", polinb);
        MyBenchStop(1, "GCD(polinb_1, polinb_2)", tt0);

        polina := 0*polinb;

    end if;

    vprint G3Cayley, 2:  LPPrint("=> Pol. in b", polinb);
    assert(Degree(polinb) le 28);

    MyBenchStop(1, "a bitangent polynomial", tt);


    tt := MyBenchStart(1, "its factorization");
    FP := Factorization(polinb);
    Sort(~FP, func<f1,f2| Degree(f1[1])-Degree(f2[1])>);
    // FP := [ <polinb, 1> ];
    MyBenchStop(1, "its factorization", tt);
    vprint G3Cayley, 1: "";

    fp := Rp!1;
    for _fp in FP do
        tt := MyBenchStart(1, "a splitting field");
        vprint G3Cayley, 2:  LPPrint("=> factor fp", _fp[1]);

        fp := fp*_fp[1];
        if Degree(fp) lt 3 then
            MyBenchStop(1, "a splitting field", tt);
            vprint G3Cayley, 1: "";
            continue;
        end if;

        SF, rts := SplittingField(fp : Std := false);
        vprintf G3Cayley, 2:
            "%o=> Extension of absolute degree %o: unramif. degree %o x ramif. degree %o\n",
            MyBenchIndent(""), AbsoluteDegree(SF), Degree(SF), RamificationDegree(SF);

        MyBenchStop(1, "a splitting field", tt);
        vprint G3Cayley, 1: "";

        tt := MyBenchStart(1, "a triple of azygetic bitangents");

        RSF := ChangeRing(Rp, SF); xL := RSF.1; AssignNames(~RSF, ["xL"]);

        Bitp := []; // Bitangents are of the form y = a*x + b
        BPts := []; // Inteserction points with the curve
        prec := Precision(SF);
        for rb in rts do

            vprintf G3Cayley, 2: "%o=> b, at precision %o\n", MyBenchIndent(""), Precision(rb);

            EQs := [*
                LPClean(UnivariatePolynomial(Evaluate(ChangeRing(E, SF), 2, rb))) : E in SYSp[1..2]
                *];

            if gbasis then
                ra := Evaluate(polina, rb);
            else
                polina := LPClean(pAdicGCD(1, EQs[1], EQs[2] : LPrate := LPrate));
                assert( Degree(polina) eq 1 );

                ra := Roots(polina)[1,1];
            end if;
            vprintf G3Cayley, 2: "%o\t=> a, at precision %o\n", MyBenchIndent(""), Precision(ra);

            bitp := [ ra, rb];

            thisf := Evaluate(eqCp, [xL, bitp[1]*xL+bitp[2], 1]);
            bpts := pAdicGCD(2, thisf, Derivative(thisf));
            vprint G3Cayley, 2: LPPrint("\t=> Bisecant points", bpts);

            assert( Degree(bpts) ge 2);

            /* bitangent in a single point ? */
            if Degree(bpts) eq 3 then
                bpts := pAdicGCD(2, bpts, Derivative(bpts));
                vprint G3Cayley, 2: LPPrint("\t=> Bisecant points (once multiplicity removed)", bpts);
                assert( Degree(bpts) eq 2);
            end if;

            Append(~Bitp, bitp); Append(~BPts, bpts);

            /* Look for an azygetic set of 3 bitangents */
            AzBitp := []; AzBPts := [];
            for S in Subsets({1..#Bitp-1}, 2) do
                AzBitp := Bitp[Setseq(S)] cat [bitp];
                AzBPts := BPts[Setseq(S)] cat [bpts];

                dcon := pAdicIsAzygetic(AzBitp, AzBPts);

                if not IsZero(dcon) then
                    vprint G3Cayley, 2: MyBenchIndent("") * "A triple found!";
                    MyBenchStop(1, "a triple of azygetic bitangents", tt);
                    vprint G3Cayley, 1: "";
                    break _fp;
                end if;
            end for;

        end for;

        vprint G3Cayley, 2: MyBenchIndent("") * "No triple found!";
        MyBenchStop(1, "a triple of azygetic bitangents", tt);
        vprint G3Cayley, 1: "";

    end for;


    // Cayley Octads associated to this triple of bitangents
    // -----------------------------------------------------

    tt := MyBenchStart(1, "the contact cubic matrix");
    Rxy := PolynomialRing(SF, 2); x := Rxy.1; y := Rxy.2; AssignNames(~Rxy, ["x", "y"]);
    eqCL:= Evaluate(eqCp, [x,y,1]);

    /* The 10 x 6 contact cubic matrix */
    xy3basis := [1, y, y^2, y^3, x, x*y, x*y^2, x^2, x^2*y, x^3 ];

    Mcnt := ZeroMatrix(SF, #xy3basis, 6);
    for j := 1 to #xy3basis do for i := 1 to 3 do
        pol := LPClean(Evaluate(xy3basis[j], [xL, AzBitp[i,1]*xL + AzBitp[i,2]]) mod AzBPts[i]);
        for k := 0 to 1 do Mcnt[j, 2*(i-1)+k+1] := Coefficient(pol, k); end for;
    end for; end for;
    vprint G3Cayley, 2:  LMPrint("=> contact cubic matrix", Mcnt);
    MyBenchStop(1, "the contact cubic matrix", tt);

    tt := MyBenchStart(1, "its kernel matrix");
    KrnM := pAdicKernelMatrix(4, Mcnt : LPrate := LPrate);
    vprint G3Cayley, 2:  LMPrint("=> kernel", KrnM);
    MyBenchStop(1, "its kernel matrix", tt);
    vprint G3Cayley, 1: "";


    /* The 28 x 6 matrix f*M */
    tt := MyBenchStart(1, "the f*M matrix");
    xy2basis := [1, y, y^2, x, x*y, x^2];
    fM := Transpose(Matrix([LPToVector(LPClean(eqCL*p), 6) : p in xy2basis]));
    vprint G3Cayley, 2:  LMPrint("=> f*M", fM);
    MyBenchStop(1, "the f*M matrix", tt);

    tt := MyBenchStart(1, "its kernel matrix");
    KrnfM := pAdicKernelMatrix(22, fM :  LPrate := LPrate);
    vprint G3Cayley, 2:  LMPrint("=> kernel", KrnM);
    MyBenchStop(1, "its kernel matrix", tt);
    vprint G3Cayley, 1: "";


    tt := MyBenchStart(1, "Dixon matrix");

    fN := Transpose(KrnfM);

    N := [
        [LPClean(&+[KrnM[j, i]*xy3basis[i] : i in [1..#xy3basis]]) : j in [1..Nrows(KrnM)] ]
        ];

    N[1] := [ LPClean(&*[ y - bitp[1]*x - bitp[2]  : bitp in AzBitp])] cat N[1][[1..3]];

    p00 := N[1,1];

    for i := 2 to 4 do
        Append(~N, []);

        for j := 1 to i-1 do Append(~N[i], N[j, i]); end for;

        for j := i to 4   do

            str := Sprintf("V[%o,%o]", i, j); tt0 := MyBenchStart(1, str);

            /* Kernel of a 11 x 22 matrix */
            P := Matrix( [ LPToVector( LPClean(N[1,i]*N[1,j]), 6)] cat [LPToVector(LPClean(p*p00), 6) : p in xy3basis ] );
            Krn := pAdicKernelMatrix(1, P*fN : LPrate := LPrate);
            assert(Nrows(Krn) eq 1);

            Append(~N[i],
                LPClean(&+[-Krn[1,i+1]/Krn[1,1]*xy3basis[i] : i in [1..#xy3basis] ])
                );

            MyBenchStop(1, str, tt0);

        end for;

    end for;

    N := Matrix(N);
    // assert(not(IsZero(Determinant(N)))); /* Takes time...*/

    pr := Min([IsZero(c) select Infinity() else Precision(c) : c in Coefficients(e), e in Eltseq(N) ]);
    vprint G3Cayley, 2:
        MyBenchIndent("") * "=> The 4x4 Dixon matrix V, at precision " * IntegerToString(pr);
    MyBenchStop(1, "Dixon matrix", tt);


    tt := MyBenchStart(1, "its adjoint matrix");
    aN := Adjoint(N);
    pr := Min([IsZero(c) select Infinity() else Precision(c) : c in Coefficients(e), e in Eltseq(aN) ]);
    vprint G3Cayley, 2:
        MyBenchIndent("") * "=> The adjoint matrix, at precision " * IntegerToString(pr);
    MyBenchStop(1, "its adjoint matrix", tt);

    tt := MyBenchStart(1, "The determinantial quartic equation");
    eqCLp2 := eqCL^2;
    T := Matrix(4, 4, [pAdicDiv(aN[i,j], eqCLp2) : i,j in [1..4]]);

    assert(not IsZero(T));

    A := Matrix([[MonomialCoefficient(T[i,j], x) : i in [1..4]]: j in [1..4]]);
    B := Matrix([[MonomialCoefficient(T[i,j], y) : i in [1..4]]: j in [1..4]]);
    C := Matrix([[MonomialCoefficient(T[i,j], 1) : i in [1..4]]: j in [1..4]]);

    vprint G3Cayley, 2:  LMPrint("=> A", A);
    vprint G3Cayley, 2:  LMPrint("=> B", B);
    vprint G3Cayley, 2:  LMPrint("=> C", C);

    Sabcdq := PolynomialRing(SF, 4); aq := Sabcdq.1; bq := Sabcdq.2;  cq := Sabcdq.3; dq := Sabcdq.4;
    AssignNames(~Sabcdq, ["aq", "bq", "cq", "dq" ]);

    vs := [aq, bq, cq, One(SF)];
    q1 := LPClean(&+[ A[i,j]*vs[i]*vs[j] : i, j in [1..4]]);
    q2 := LPClean(&+[ B[i,j]*vs[i]*vs[j] : i, j in [1..4]]);
    q3 := LPClean(&+[ C[i,j]*vs[i]*vs[j] : i, j in [1..4]]);
    MyBenchStop(1, "the determinantial quartic equation", tt);
    vprint G3Cayley, 1: "";

    tt := MyBenchStart(1, "octad points");
    vprint G3Cayley, 1: "";

    tt0 := MyBenchStart(1, "the bivariate resultant w1");
    w1 := LPClean(Resultant(q2, q3, aq));
    vprint G3Cayley, 2:  LPPrint("=> w1", w1);
    MyBenchStop(1, "the bivariate resultant w1", tt0);

    tt0 := MyBenchStart(1, "the bivariate resultant w2");
    w2 := LPClean(Resultant(q1, q3, aq));
    vprint G3Cayley, 2:  LPPrint("=> w2", w2);
    MyBenchStop(1, "the bivariate resultant w2", tt0);

    tt0 := MyBenchStart(1, "the bivariate resultant w3");
    w3 := LPClean(Resultant(q1, q2, aq));
    vprint G3Cayley, 2:  LPPrint("=> w3", w3);
    MyBenchStop(1, "the bivariate resultant w3", tt0);
    vprint G3Cayley, 1: "";

    tt0 := MyBenchStart(1, "the resultant u12");
    u12 := LPClean(UnivariatePolynomial(Resultant(w1, w2, bq)));
    vprint G3Cayley, 2:  LPPrint("=> u12", u12);
    MyBenchStop(1, "the resultant u12", tt0);

    tt0 := MyBenchStart(1, "the resultant u13");
    u13 := LPClean(UnivariatePolynomial(Resultant(w1, w3, bq)));
    vprint G3Cayley, 2:  LPPrint("=> u13", u13);
    MyBenchStop(1, "the resultant u13", tt0);
    vprint G3Cayley, 1: "";

    tt0 := MyBenchStart(1, "GCD(u12, u13)");
    upol := pAdicGCD(8, u12, u13 : LPrate := LPrate);
    vprint G3Cayley, 2:  LPPrint("=>", upol);
    MyBenchStop(1, "GCD(u12, u13)", tt0);
    vprint G3Cayley, 1: "";

    assert(Degree(upol) ge 8);

    /* Do we need to refine ? */
    if Degree(upol) gt 8 then

        tt0 := MyBenchStart(1, "the resultant u23");
        time u23 := LPClean(UnivariatePolynomial(Resultant(w2, w3, bq)));
        vprint G3Cayley, 2:  LPPrint("=> u23", u23);
        MyBenchStop(1, "the resultant u23", tt0);
        vprint G3Cayley, 1: "";

        tt0 := MyBenchStart(1, "GCD with u23");
        time upol := pAdicGCD(8, upol, u23 : LPrate := LPrate);
        vprint G3Cayley, 2:  LPPrint("=>", upol);
        MyBenchStop(1, "GCD with u23", tt0);
        vprint G3Cayley, 1: "";
    end if;

    assert(Degree(upol) eq 8);

    tt0 := MyBenchStart(1, "its splitting field");
    SU, rts_c := SplittingField(upol : Std := false);
    if SF eq SU then
        vprintf G3Cayley, 2: "%o=> Everything splits\n", MyBenchIndent("");
    else
        vprintf G3Cayley, 2:
            "%o=> Extension of absolute degree %o: unramif. degree %o x ramif. degree %o\n",
            MyBenchIndent(""), AbsoluteDegree(SU), Degree(SU), RamificationDegree(SU);

        /* Embed what is needed in the new extension */
        aq, bq, cq, dq := Explode([* ChangeRing(p, SU) : p in [* aq, bq, cq, dq *] *]);
        w1, w2, w3 := Explode([* ChangeRing(p, SU) : p in [* w1, w2, w3 *] *]);

    end if;
    MyBenchStop(1, "its splitting field", tt0);
    vprint G3Cayley, 1: "";

    tt0 := MyBenchStart(1, "rational solutions");
    cOctad := [];
    for c1 in rts_c do

        str := Sprintf("%o-th point (x:y:z:1)", #cOctad+1); tt1 := MyBenchStart(1, str);

        vprintf G3Cayley, 2: "%o\t=> z, at precision %o\n", MyBenchIndent(""), Precision(c1);

        u1 := LPClean(UnivariatePolynomial(Evaluate(w1, 3, c1)));
        u2 := LPClean(UnivariatePolynomial(Evaluate(w2, 3, c1)));

        bpol := Parent(u1)!0;
        if u1 ne 0 and u2 ne 0 then
            bpol := pAdicGCD(1, u1, u2 : LPrate := LPrate);
            assert(Degree(bpol) ge 1);
        end if;

        if bpol eq 0 then bpol := u1 eq 0 select u2 else u1; end if;

        if bpol eq 0 then
            u3 := UnivariatePolynomial(Evaluate(w3, 3, c1));
            bpol := u3;
        elif Degree(bpol) gt 1 then
            u3 := UnivariatePolynomial(Evaluate(w3, 3, c1));
            bpol := pAdicGCD(1, bpol, u3 : LPrate := LPrate);
        end if;
        assert(Degree(bpol) ge 1);

        for b1 in [ r[1] : r in Roots(bpol) ] do
            vprintf G3Cayley, 2: "%o\t=> y, at precision %o\n", MyBenchIndent(""), Precision(b1);

            u4 := UnivariatePolynomial(Evaluate(q1, [aq, b1, c1, One(SU)]));
            u5 := UnivariatePolynomial(Evaluate(q2, [aq, b1, c1, One(SU)]));

            apol := Parent(u4)!0;
            if u4 ne 0 and u5 ne 0 then
                apol := pAdicGCD(1, u4, u5 : LPrate := LPrate);
                assert(Degree(apol) ne 0);
            end if;

            if apol eq 0 then apol := u4 eq 0 select u5 else u4; end if;

            if apol eq 0 then
                u6 := UnivariatePolynomial(Evaluate(q3, [aq, b1, c1, One(SU)]));
                apol := u6;
            elif Degree(apol) gt 1 then
                u6 := UnivariatePolynomial(Evaluate(q3, [aq, b1, c1, One(SU)]));
                apol := pAdicGCD(1, apol, u6 : LPrate := LPrate);
            end if;
            assert(Degree(apol) ge 1);

            for a1 in [ r[1] : r in Roots(apol) ] do
                vprintf G3Cayley, 2: "%o\t=> x, at precision %o\n", MyBenchIndent(""), Precision(a1);
                assert(IsZero(Evaluate(q1, [a1, b1, c1, One(SU)])));
                assert(IsZero(Evaluate(q2, [a1, b1, c1, One(SU)])));
                assert(IsZero(Evaluate(q3, [a1, b1, c1, One(SU)])));
                Append(~cOctad, [a1, b1, c1, One(SU)]);
                pr := Min([IsZero(e) select Infinity() else Precision(e) : e in [a1, b1, c1, One(SU)]]);
            end for;

            MyBenchStop(1, str, tt1);

        end for;
    end for;
    MyBenchStop(1, "rational solutions", tt0);
    vprint G3Cayley, 1: "";

    assert(#cOctad eq 8);
    MyBenchStop(1, "octad points", tt);
    vprint G3Cayley, 1: "";

    MyBenchStop(1, "a Cayley octad", TT);
    vprint G3Cayley, 1: "";

    return cOctad;
end intrinsic;

function pAdicValuation(x)
    v := Valuation(x);
    if Type(v) eq ExtReElt or Type(v) eq Infty then return Infinity(); end if;
    return Integers()!v;
end function;

function NormaliseValuation(v)
	m := Min([pAdicValuation(v[j]) : j in [1..4]]);
	return [ ShiftValuation(e, -m) : e in Eltseq(v) ];
end function;

function NormaliseOctad(OL)

    M5 := Matrix(OL[[1..5]]);
    K5 := KernelMatrix(M5); assert(Nrows(K5) eq 1);
    N := Matrix(4, 4, [ OL[i,j] * K5[1,i] : i,j in [1..4] ]);
    O2 := Matrix(OL) * N^(-1);
    O3 := [ NormaliseValuation(O2[i]) : i in [1..8] ];
    return O3, N;

end function;

intrinsic CayleyOctadPGLOrbit(O::SeqEnum) -> SeqEnum
    {Orbit of an octad under PGL action, restricted to the ordered octad}

    Indexes := { Sort(Setseq(S)) cat Sort(Setseq({1..8} diff S)) : S in Subsets({1..8}, 5) };

    PGLOrbit := [];
    for L in Indexes do
        Append(~PGLOrbit, NormaliseOctad(O[L]));
    end for;

    return PGLOrbit;

end intrinsic;

intrinsic CayleyOctadCremonaOrbit(Octad::SeqEnum) -> SeqEnum
    {Orbit of an octad under Cremona action, restricted to the ordered octad}

    Indexes := {};
    for S in Subsets({1..8}, 4) do
        if ({1..8} diff S) in Indexes then continue; end if;
        Include(~Indexes, S);
    end for;
    Indexes := Sort([ Sort(Setseq(E)) : E in Indexes ]);

    CremonaOrbit := [ NormaliseOctad(Octad) ];
    for S in Indexes do
        L := Sort(Sort(Setseq({1..8} diff Seqset(S)))) cat S;
        _O := NormaliseOctad(Octad[L]);
        for i := 5 to 8 do
            _O[i, 1] := 1 / _O[i, 1];
            _O[i, 2] := 1 / _O[i, 2];
            _O[i, 3] := 1 / _O[i, 3];
            _O[i, 4] := 1 / _O[i, 4];
        end for;
        Append(~CremonaOrbit, _O);
    end for;

    return CremonaOrbit;
end intrinsic;
