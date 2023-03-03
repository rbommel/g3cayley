/***
 * Exported intrinsics.
 *
 * intrinsic QuarticByReductionType(Type::MonStgElt, p::RngIntElt :
 *   Domain := [-p^4..p^4],
 *   Flat := false,
 *   K := Rationals()) -> RngMPolElt
 *
 * intrinsic G3HyperReductionType(Type::MonStgElt, p::RngIntElt :
 *   Domain := [-p^4..p^4],
 *   K := Rationals())  -> RngMPolElt
 *
 * intrinsic G3QuarticFromHyper(f::RngUPolElt, p::RngIntElt) -> RngMPolElt
 *
 ********************************************************************/

import "verbose.m" : MyBenchIndent, MyBenchStart, MyBenchStop;

 forward Case_0____0,
    Case_0nne, Case_0nnm,
    Case_0nee, Case_0nme, Case_0nmm,
    Case_0xxx;

function RandAlg(K, Domain)
    return K![Random(Domain) : i in [1..Degree(K)] ];
end function;

intrinsic QuarticByReductionType(Type::MonStgElt, p::RngIntElt :
    Domain := [-p^4..p^4], Flat := false, K := Rationals()) -> RngMPolElt

    {Return a plane quartic defined over K, with coefficients randomly chosen in Domain, such that its reduction modulo p is of the given Type.}

    Pxy := PolynomialRing(K, 2); x := Pxy.1; y := Pxy.2; z := K!1;

    a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 :=
        Explode( [K| RandAlg(K, Domain) : i in [1..15] ] );
    f := Pxy!0;

    case Type:

        // Codimension 0
    when "(3)" :
        f :=
            a00*z^4 +
            a10*x*z^3 + a01*y*z^3 +
            (a20*x^2 + a11*x*y + a02*y^2)*z^2+
            (a03*y^3 + a12*x*y^2 + a21*x^2*y + a30*x^3)*z+
            a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*x*y^3 + a04*y^4;

        // Codimension 1
    when "(2n)" :
        f :=
            a00*p*z^4 +
            a10*p*x*z^3 + a01*p*y*z^3 +
            (a20*x^2 + a11*x*y + a02*y^2)*z^2+
            (a03*y^3 + a12*x*y^2 + a21*x^2*y + a30*x^3)*z+
            a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*x*y^3 + a04*y^4;

    when "(2e)" :
        if Flat then
            f :=
                a00*p^1*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                a20*p^1*x^2*z^2 + a11*p^1*x*y*z^2 + a02*y^2*z^2 +
                a30*x^3*z + a21*x^2*y*z + a12*x*y^2*z + a03*y^3*z +
                a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*x*y^3 + a04*y^4;
        else
            f :=
                a00*p^6*z^4 +
                a10*p^4*x*z^3 + a01*p^3*y*z^3 +
                (a20*p^2*x^2 + a11*p*x*y + a02*y^2)*z^2+
                (a03*y^3 + a12*x*y^2 + a21*x^2*y + a30*x^3)*z+
                a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*x*y^3 + a04*y^4;
        end if;

        // Codimension 2
    when "(1nn)" :
        f :=
            a00*p*z^4 +
            a10*p*x*z^3 + a01*p*y*z^3 +
            (a20*x^2 + a11*x*y + a02*y^2)*z^2+
            (a03*p*y^3 + a12*x*y^2 + a21*x^2*y + a30*x^3)*z+
            a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*p*x*y^3 + a04*p*y^4;


    when "(1=1)" :
        if Flat then
            f :=
                a00*p^1*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                (a20*p^1*x^2 + p*a11*x*y + a02*y^2)*z^2+
                (a03*y^3 + a12*x*y^2 + a21*x^2*y + a30*p*x^3)*z+
                a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*x*y^3 + a04*y^4;
        else
            f :=
                a00*p^4*z^4 +
                a10*p^3*x*z^3 + a01*p^2*y*z^3 +
                (a20*p^2*x^2 + p*a11*x*y + a02*y^2)*z^2+
                (a03*y^3 + a12*x*y^2 + a21*x^2*y + a30*p*x^3)*z+
                a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*x*y^3 + a04*y^4;
        end if;

    when "(2m)" :
        if Flat then
            f :=
                a00*p^1*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                a20*x^2*z^2 + a11*x*y*z^2 + a02*y^2*z^2 +
                a30*x^3*z + a21*p^1*x^2*y*z + a12*p^1*x*y^2*z + a03*p^1*y^3*z +
                a40*p^1*x^4 + a31*p^1*x^3*y + a22*p^1*x^2*y^2 + a13*p^1*x*y^3 + a04*p^1*y^4;
        else
            f :=
                a00*p^7*z^4 +
                a10*p^5*x*z^3 + a01*p^4*y*z^3 +
                (a20*p^2*x^2 + a11*p*x*y + a02*y^2)*z^2+
                (a03*y^3 + a12*x*y^2 + a21*x^2*y + a30*x^3)*z+
                a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*x*y^3 + a04*y^4;
        end if;

    when "(1ne)" :
        if Flat then
            f :=
                a00*p*z^4 +
                a10*p*x*z^3 + a01*p*y*z^3 +
                (a20*p*x^2 + a11*p*x*y + a02*y^2)*z^2+
                (a03*p*y^3 + a12*x*y^2 + a21*x^2*y + a30*x^3)*z+
                a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*p*x*y^3 + a04*p*y^4;
        else
            f :=
                a00*p^6*z^4 +
                a10*p^4*x*z^3 + a01*p^3*y*z^3 +
                (a20*p^2*x^2 + a11*p*x*y + a02*y^2)*z^2+
                (a03*p*y^3 + a12*x*y^2 + a21*x^2*y + a30*x^3)*z+
                a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*p*x*y^3 + a04*p*y^4;
        end if;

    when "(1ee)" :
        if Flat then
            f :=
                a00*p*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                a20*p^1*x^2*z^2 + a11*p^1*x*y*z^2 + a02*y^2*z^2 +
                a30*x^3*z + a21*x^2*y*z + a12*p^1*x*y^2*z + a03*p^1*y^3*z +
                a40*x^4 + a31*x^3*y + a22*p^1*x^2*y^2 + a13*p^1*x*y^3 +
                a04*p^1*y^4;
        else
            f :=
                a00*p^6*z^4 +
                a10*p^4*x*z^3 + a01*p^3*y*z^3 +
                (a20*p^2*x^2 + a11*p*x*y + a02*y^2)*z^2+
                (a03*p^3*y^3 + a12*p*x*y^2 + a21*x^2*y + a30*x^3)*z+
                a40*x^4 + a31*x^3*y + a22*p^2*x^2*y^2 + a13*p^4*x*y^3 + a04*p^6*y^4;
        end if;

/*

        jE00 := GF(p)!(-(24*a01*a02*a11*a30-48*a02^2*a10*a30+16*a02^2*a20^2-8*a02*a11^2*a20+a11^4)^3/
        a30^2/a02^3/(432*a00^2*a02^3*a30^2-216*a00*a01^2*a02^2*a30^2+144*a00*a01*a02^2
            *a11*a20*a30-36*a00*a01*a02*a11^3*a30-288*a00*a02^3*a10*a20*a30+64*a00*a02^3*
            a20^3+72*a00*a02^2*a10*a11^2*a30-48*a00*a02^2*a11^2*a20^2+12*a00*a02*a11^4*a20
            -a00*a11^6+27*a01^4*a02*a30^2-36*a01^3*a02*a11*a20*a30+a01^3*a11^3*a30+72*a01^
            2*a02^2*a10*a20*a30-16*a01^2*a02^2*a20^3+30*a01^2*a02*a10*a11^2*a30+8*a01^2*
            a02*a11^2*a20^2-a01^2*a11^4*a20-96*a01*a02^2*a10^2*a11*a30+16*a01*a02^2*a10*
            a11*a20^2-8*a01*a02*a10*a11^3*a20+a01*a10*a11^5+64*a02^3*a10^3*a30-16*a02^3*
            a10^2*a20^2+8*a02^2*a10^2*a11^2*a20-a02*a10^2*a11^4));

        jE40 := GF(p)!(16*a02^2*a40^2-8*a02*a21^2*a40+24*a02*a21*a30*a31+a21^4)^3/a02^3/a30^2/a31^2/
        (16*a02^2*a40^3-8*a02*a21^2*a40^2+36*a02*a21*a30*a31*a40-27*a02*a30^2*a31^2+a21^4*a40-a21^3*a30*a31);

        jE04 := GF(p)!((48*a02^2*a13*a31-16*a02^2*a22^2-24*a02*a03*a12*a31+8*a02*a12^2*a22-a12^4)^3/
        a02^3/a31^2/(432*a02^3*a04^2*a31^2-288*a02^3*a04*a13*a22*a31+64*a02^3*a04*a22^
            3+64*a02^3*a13^3*a31-16*a02^3*a13^2*a22^2-216*a02^2*a03^2*a04*a31^2+72*a02^2*
            a03^2*a13*a22*a31-16*a02^2*a03^2*a22^3+144*a02^2*a03*a04*a12*a22*a31-96*a02^2*
            a03*a12*a13^2*a31+16*a02^2*a03*a12*a13*a22^2+72*a02^2*a04*a12^2*a13*a31-48*a02
            ^2*a04*a12^2*a22^2+8*a02^2*a12^2*a13^2*a22+27*a02*a03^4*a31^2-36*a02*a03^3*a12
            *a22*a31+30*a02*a03^2*a12^2*a13*a31+8*a02*a03^2*a12^2*a22^2-36*a02*a03*a04*a12
            ^3*a31-8*a02*a03*a12^3*a13*a22+12*a02*a04*a12^4*a22-a02*a12^4*a13^2+a03^3*a12^
            3*a31-a03^2*a12^4*a22+a03*a12^5*a13-a04*a12^6));

        [GF(p) | jE00, jE40, jE04];

*/

        // Codimension 3
    when "(0nnn)" :
        f :=
            a00*p*z^4 +
            (a10*p*x + a01*p*y)*z^3 +
            (a20*x^2 + a11*x*y + a02*y^2)*z^2 +
            (a03*p*y^3 + a12*x*y^2 + a21*x^2*y + a30*p*x^3)*z +
            a40*p*x^4 + a31*p*x^3*y + a22*x^2*y^2 + a13*p*x*y^3 + a04*p*y^4;

    when "(1---0)" :
        f :=
            a00*p^1*z^4 +
            a10*p^0*x*z^3 + a01*p^1*y*z^3 +
            a20*p^0*x^2*z^2 + a11*p^0*x*y*z^2 + a02*p^1*y^2*z^2 +
            a30*x^3*z + a21*x^2*y*z + a12*p^0*x*y^2*z + a03*p^1*y^3*z +
            a40*x^4 + a31*x^3*y + a22*p^0*x^2*y^2 + a13*p^0*x*y^3 + a04*p^1*y^4;

    when "(1=0n)" :
        if Flat then
            f :=
                a00*p*z^4 +
                (a10*p*x + a01*p*y)*z^3 +
                (a20*x^2 + a11*x*y + a02*y^2)*z^2+
                (a03*p*y^3 + a12*p*x*y^2 + a21*x^2*y + a30*x^3)*z+
                a40*x^4 + a31*p*x^3*y + a22*p*x^2*y^2 + a13*p*x*y^3 + a04*p*y^4;
        else
            f :=
                a00*p*z^4 +
                (a10*p*x + a01*p*y)*z^3 +
                (a20*x^2 + a11*x*y + a02*y^2)*z^2+
                (a03*p^2*y^3 + a12*p*x*y^2 + a21*x^2*y + a30*x^3)*z+
                a40*x^4 + a31*p^1*x^3*y + a22*p^2*x^2*y^2 + a13*p^3*x*y^3 + a04*p^4*y^4;
        end if;

    when "(0nne)" :
        f := Case_0nne(p : Domain := Domain, Flat := Flat, K := K);

    when "(1nm)" :
        if Flat then
            f :=
                a00*p^4*z^4 +
                a10*p^3*x*z^3 + a01*p^2*y*z^3 +
                (a20*p^1*x^2 + a11*p*x*y + a02*y^2)*z^2+
                (a03*p*y^3 + a12*x*y^2 + a21*x^2*y + a30*x^3)*z+
                a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*p*x*y^3 + a04*p^1*y^4;

        else
            f :=
                a00*p^7*z^4 +
                a10*p^5*x*z^3 + a01*p^4*y*z^3 +
                (a20*p^2*x^2 + a11*p*x*y + a02*y^2)*z^2+
                (a03*p*y^3 + a12*x*y^2 + a21*x^2*y + a30*x^3)*z+
                a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*p*x*y^3 + a04*p^1*y^4;
        end if;

    when "(1=0e)" :
        if Flat then
            f :=
                a00*p^1*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                a20*p^1*x^2*z^2 + a11*p^1*x*y*z^2 + a02*p^0*y^2*z^2 +
                a30*p*x^3*z + a21*x^2*y*z + a12*p^1*x*y^2*z + a03*p^1*y^3*z +
                a40*p^0*x^4 + a31*p^0*x^3*y + a22*p^1*x^2*y^2 + a13*p^1*x*y^3 + a04*p^1*y^4;
        else
            f :=
                a00*p^1*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                a20*p^1*x^2*z^2 + a11*p^1*x*y*z^2 + a02*p^0*y^2*z^2 +
                a30*p*x^3*z + a21*x^2*y*z + a12*p^1*x*y^2*z + a03*p^2*y^3*z +
                a40*p^0*x^4 + a31*p^0*x^3*y + a22*p^1*x^2*y^2 + a13*p^2*x*y^3 + a04*p^3*y^4;
        end if;
    when "(1me)" :
        if Flat then
            f :=
                a00*p^2*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                a20*p^1*x^2*z^2 + a11*p^1*x*y*z^2 + a02*p^1*y^2*z^2 +
                a30*p^1*x^3*z + a21*p^1*x^2*y*z + a12*p^2*x*y^2*z + a03*p^2*y^3*z +
                a40*p^1*x^4 + a31*p^1*x^3*y + a22*x^2*y^2 + a13*p^1*x*y^3 + a04*p^2*y^4;

        else
            f :=
                a00*p^(2*2)*z^4 +
                a10*p^(0*2)*x*z^3 + a01*p^(0*2)*y*z^3 +
                a20*p^(1*2)*x^2*z^2 + a11*p^(0*2)*x*y*z^2 + a02*p^(1*2)*y^2*z^2 +
                a30*p^(2*2)*x^3*z + a21*p^(1)*x^2*y*z + a12*p^(1)*x*y^2*z + a03*p^(7)*y^3*z +
                a40*p^(1*6)*x^4 + a31*p^(3)*x^3*y + a22*x^2*y^2 + a13*p^(1*6)*x*y^3 + a04*p^(2*6)*y^4;
        end if;

    when "(0nee)" :
        f := Case_0nee(p : Domain := Domain, Flat := Flat, K := K);

    when "(0eee)" :
        f := Case_0xxx("(0eee)", p : Domain := Domain, Flat := Flat, K := K);

        // Codimension 4
    when "(0----0)" :
        f := Case_0____0(p : Domain := Domain, Flat := Flat, K := K);

    when "(0---0n)" :
        f :=
            a00*p^1*z^4 +
            a10*p^1*x*z^3 + a01*p^1*y*z^3 +
            a20*p^0*x^2*z^2 + a11*p^0*x*y*z^2 + a02*p^1*y^2*z^2 +
            a30*p^1*x^3*z + a21*p^0*x^2*y*z + a12*p^0*x*y^2*z + a03*p^1*y^3*z +
            a40*p^1*x^4 + a31*p^1*x^3*y + a22*p^0*x^2*y^2 + a13*p^1*x*y^3 + a04*p^1*y^4;

    when "(0n=0n)" :
        if Flat then
            f :=
                a00*p^1*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                a20*p^0*x^2*z^2 + a11*p^0*x*y*z^2 + a02*p^0*y^2*z^2 +
                a30*p^0*x^3*z + a21*p^0*x^2*y*z + a12*p^1*x*y^2*z + a03*p^3*y^3*z +
                a40*p^0*x^4 + a31*p^1*x^3*y + a22*p^1*x^2*y^2 + a13*p^2*x*y^3 + a04*p^3*y^4;
        else
            f :=
                a00*p^1*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                a20*p^0*x^2*z^2 + a11*p^0*x*y*z^2 + a02*p^0*y^2*z^2 +
                a30*p^0*x^3*z + a21*p^0*x^2*y*z + a12*p^1*x*y^2*z + a03*p^3*y^3*z +
                a40*p^0*x^4 + a31*p^1*x^3*y + a22*p^1*x^2*y^2 + a13*p^3*x*y^3 + a04*p^5*y^4;
        end if;

    when "(0nnm)" :
        f := Case_0nnm(p : Domain := Domain, Flat := Flat, K := K);

    when "(Z=1)" :
        if Flat then
            f :=
                a00*p*z^4 +
                (a10*p*x + a01*p*y)*z^3 +
                (a20*p*x^2 + a11*x*y + a02*p*y^2)*z^2 +
                (a30*p*x^3 + a21*p*x^2*y + a12*x*y^2 + a03*p*y^3)*z +
                a40*p*x^4 + a31*p^2*x^3*y + a22*x^2*y^2 + a13*x*y^3 + a04*p*y^4;
        else
            f :=
                a00*p^4*z^4 +
                (a10*p^4*x + a01*p^4*y)*z^3 +
                (a20*p^4*x^2 + a11*x*y + a02*p^4*y^2)*z^2 +
                (a30*p^4*x^3 + a21*p*x^2*y + a12*x*y^2 + a03*p^4*y^3)*z +
                a40*p^4*x^4 + a31*p^2*x^3*y + a22*x^2*y^2 + a13*x*y^3 + a04*p^4*y^4;
        end if;

    when "(0---0e)" :
        if Flat then
            f :=
                a00*p^1*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                a20*p^1*x^2*z^2 + a11*p^1*x*y*z^2 + a02*p^0*y^2*z^2 +
                a30*x^3*z + a21*x^2*y*z + a12*p^0*x*y^2*z + a03*p^0*y^3*z +
                a40*p^2*x^4 + a31*p*x^3*y + a22*p^1*x^2*y^2 + a13*p^2*x*y^3 + a04*p^2*y^4;
        else
            f :=
                a00*p^1*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                a20*p^1*x^2*z^2 + a11*p^1*x*y*z^2 + a02*p^0*y^2*z^2 +
                a30*x^3*z + a21*x^2*y*z + a12*p^0*x*y^2*z + a03*p^0*y^3*z +
                a40*p^2*x^4 + a31*p*x^3*y + a22*p^1*x^2*y^2 + a13*p^2*x*y^3 + a04*p^3*y^4;
    end if;

    when "(1=0m)" :
        f :=
            a00*p^4*z^4 +
            a10*p^3*x*z^3 + a01*p^2*y*z^3 +
            a20*p^1*x^2*z^2 + a11*p^1*x*y*z^2 + a02*p^0*y^2*z^2 +
            a30*p^0*x^3*z + a21*p^0*x^2*y*z + a12*p^1*x*y^2*z + a03*p^1*y^3*z +
            a40*p^0*x^4 + a31*p^1*x^3*y + a22*p^1*x^2*y^2 + a13*p^1*x*y^3 + a04*p^1*y^4;

    when "(0n=0e)" :
        if Flat then
            f :=
                a00*p^1*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                a20*p^1*x^2*z^2 + a11*p^1*x*y*z^2 + a02*p^0*y^2*z^2 +
                a30*p^0*x^3*z + a21*p^0*x^2*y*z + a12*p^1*x*y^2*z + a03*p^3*y^3*z +
                a40*p^1*x^4 + a31*p^1*x^3*y + a22*p^1*x^2*y^2 + a13*p^3*x*y^3 + a04*p^3*y^4;
        else
            f :=
                a00*p^1*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                a20*p^1*x^2*z^2 + a11*p^1*x*y*z^2 + a02*p^0*y^2*z^2 +
                a30*p^0*x^3*z + a21*p^0*x^2*y*z + a12*p^1*x*y^2*z + a03*p^3*y^3*z +
                a40*p^1*x^4 + a31*p^1*x^3*y + a22*p^1*x^2*y^2 + a13*p^3*x*y^3 + a04*p^5*y^4;
        end if;
    when "(1mm)" :
        if Flat then
            f :=
                a00*p^2*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                a20*p^1*x^2*z^2 + a11*p^1*x*y*z^2 + a02*p^1*y^2*z^2 +
                a30*p^2*x^3*z + a21*p^1*x^2*y*z + a12*p^1*x*y^2*z + a03*p^2*y^3*z +
                a40*p^2*x^4 + a31*p^1*x^3*y + a22*p^0*x^2*y^2 + a13*p^1*x*y^3 +
                a04*p^2*y^4;
        else
            f :=
                a00*p^(2*6)*z^4 +
                a10*p^(1*6)*x*z^3 + a01*p^(1*6)*y*z^3 +
                a20*p^(1*6)*x^2*z^2 + a11*p^(4)*x*y*z^2 + a02*p^(1*6)*y^2*z^2 +
                a30*p^(9)*x^3*z + a21*p^(3)*x^2*y*z + a12*p^(3)*x*y^2*z + a03*p^(9)*y^3*z +
                a40*p^(2*6)*x^4 + a31*p^(1*6)*x^3*y + a22*p^(0*6)*x^2*y^2 + a13*p^(1*6)*x*y^3 +
                a04*p^(2*6)*y^4;
        end if;

    when "(0nme)" :
        f := Case_0nme(p : Domain := Domain, Flat := Flat, K := K);

    when "(0e=0e)" :
        f :=
            a00*p^9*z^4 +
            (a10*p^6*x + a01*p^3*y)*z^3 +
            (a20*p^3*x^2 + a11*p^2*x*y + a02*y^2)*z^2 +
            (a30*x^3 + a21*x^2*y + a12*p^3*x*y^2 + a03*p^7*y^3)*z +
            a40*x^4 + a31*p^2*x^3*y + a22*p^6*x^2*y^2 + a13*p^10*x*y^3 + a04*p^14*y^4;

    when "(0mee)" :
        f := Case_0xxx("(0mee)", p : Domain := Domain, Flat := Flat, K := K);

        // Codimension 5
    when "(CAVE)" :
        f :=
            a00*p^1*z^4 +
            a10*p^1*x*z^3 + a01*p^1*y*z^3 +
            a20*p^1*x^2*z^2 + a11*p^0*x*y*z^2 + a02*p^1*y^2*z^2 +
            a30*p^1*x^3*z + a21*p^0*x^2*y*z + a12*p^0*x*y^2*z + a03*p^1*y^3*z +
            a40*p^1*x^4 + a31*p^1*x^3*y + a22*p^0*x^2*y^2 + a13*p^1*x*y^3 + a04*p^1*y^4;

    when "(Z=0n)" :
        f :=
            a00*p^1*z^4 +
            a10*p^2*x*z^3 + a01*p^1*y*z^3 +
            a20*p^0*x^2*z^2 + a11*p^0*x*y*z^2 + a02*p^0*y^2*z^2 +
            a30*p^1*x^3*z + a21*p^2*x^2*y*z + a12*p^0*x*y^2*z + a03*p^2*y^3*z +
            a40*p^3*x^4 + a31*p^4*x^3*y + a22*p^2*x^2*y^2 + a13*p^2*x*y^3 + a04*p^4*y^4;

    when "(0---0m)" :
        if Flat then
            f :=
                a00*p^2*z^4 +
                a10*p^1*x*z^3 + a01*p^1*y*z^3 +
                a20*p^1*x^2*z^2 + a11*p^1*x*y*z^2 + a02*p^1*y^2*z^2 +
                a30*p^1*x^3*z + a21*p^1*x^2*y*z + a12*p^1*x*y^2*z + a03*p^3*y^3*z +
                a40*p^0*x^4 + a31*x^3*y + a22*p^1*x^2*y^2 + a13*p^3*x*y^3 +
                a04*p^4*y^4;
        else
            f :=
                a00*p^(2*6)*z^4 +
                a10*p^(1*6)*x*z^3 + a01*p^(1*6)*y*z^3 +
                a20*p^(1*6)*x^2*z^2 + a11*p^(1*6)*x*y*z^2 + a02*p^(1*6)*y^2*z^2 +
                a30*p^(1*6)*x^3*z + a21*p^(1*6)*x^2*y*z + a12*p^(1*6)*x*y^2*z + a03*p^(3*6)*y^3*z +
                a40*p^(0*6)*x^4 + a31*x^3*y + a22*p^(1*6)*x^2*y^2 + a13*p^(3*6)*x*y^3 + a04*p^(4*6)*y^4;
        end if;

    when "(0n=0m)" :
        f :=
            a00*p^3*z^4 +
            a10*p^2*x*z^3 + a01*p^2*y*z^3 +
            a20*p^0*x^2*z^2 + a11*p^1*x*y*z^2 + a02*p^1*y^2*z^2 +
            a30*p^2*x^3*z + a21*p^1*x^2*y*z + a12*p^0*x*y^2*z + a03*p^1*y^3*z +
            a40*p^4*x^4 + a31*p^3*x^3*y + a22*p^1*x^2*y^2 + a13*p^0*x*y^3 + a04*p^0*y^4;

    when "(0nmm)" :
        f := Case_0nmm(p : Domain := Domain, Flat := Flat, K := K);

    when "(Z=0e)" :
        if Flat then
            f :=
                a00*p^1*z^4 +
                a10*p^2*x*z^3 + a01*p^1*y*z^3 +
                a20*p^2*x^2*z^2 + a11*p^1*x*y*z^2 + a02*p^0*y^2*z^2 +
                a30*p^0*x^3*z + a21*p^0*x^2*y*z + a12*p^4*x*y^2*z + a03*p^1*y^3*z +
                a40*p^3*x^4 + a31*p^2*x^3*y + a22*p^2*x^2*y^2 + a13*p^2*x*y^3 + a04*p^3*y^4;
        else
            f :=
                a00*p^6*z^4 +
                a10*p^4*x*z^3 + a01*p^3*y*z^3 +
                a20*p^2*x^2*z^2 + a11*p^1*x*y*z^2 + a02*p^0*y^2*z^2 +
                a30*p^0*x^3*z + a21*p^0*x^2*y*z + a12*p^4*x*y^2*z + a03*p^1*y^3*z +
                a40*p^3*x^4 + a31*p^2*x^3*y + a22*p^2*x^2*y^2 + a13*p^2*x*y^3 + a04*p^3*y^4;
        end if;

    when "(0m=0e)" :
        if Flat then
            f :=
                a00*p^2*z^4 +
                a10*p^2*x*z^3 + a01*p^1*y*z^3 +
                a20*p^1*x^2*z^2 + a11*p^2*x*y*z^2 + a02*p^0*y^2*z^2 +
                a30*p^0*x^3*z + a21*p^2*x^2*y*z + a12*p^2*x*y^2*z + a03*p^6*y^3*z +
                a40*p^1*x^4 + a31*p^2*x^3*y + a22*p^4*x^2*y^2 + a13*p^7*x*y^3 + a04*p^9*y^4;
        else
            f :=
                a00*p^(6)*z^4 +
                a10*p^(4)*x*z^3 + a01*p^(3)*y*z^3 +
                a20*p^(2)*x^2*z^2 + a11*p^(1)*x*y*z^2 + a02*p^(0*6)*y^2*z^2 +
                a30*p^(0*6)*x^3*z + a21*p^(2)*x^2*y*z + a12*p^(7)*x*y^2*z + a03*p^(15)*y^3*z +
                a40*p^(1*4)*x^4 + a31*p^(7)*x^3*y + a22*p^(2*7)*x^2*y^2 + a13*p^(22)*x*y^3 + a04*p^(30)*y^4;

        end if;

    when "(0mme)" :
        f := Case_0xxx("(0mme)", p : Domain := Domain, Flat := Flat, K := K);

        // Codimension 6
    when "(BRAID)" :
        f :=
            a00*p^1*z^4 +
            a10*p^1*x*z^3 + a01*p^1*y*z^3 +
            a20*p^1*x^2*z^2 + a11*p^0*x*y*z^2 + a02*p^1*y^2*z^2 +
            a30*p^1*x^3*z + a21*p^0*x^2*y*z + a12*p^0*x*y^2*z + a03*p^1*y^3*z +
            a40*p^1*x^4 + a31*p^1*x^3*y + a22*p^1*x^2*y^2 + a13*p^1*x*y^3 + a04*p^1*y^4;

    when "(Z=Z)" :
        if Flat then
            f :=
                a00*p*z^4 +
                (a10*p^2*x + a01*p*y)*z^3 +
                (a20*p^3*x^2 + a11*x*y + a02*p*y^2)*z^2 +
                (a30*p^3*x^3 + a21*p*x^2*y + a12*x*y^2 + a03*p*y^3)*z +
                a40*p^3*x^4 + a31*p*x^3*y + a22*x^2*y^2 + a13*x*y^3 + a04*p*y^4;
        else
            f :=
                a00*p*z^4 +
                (a10*p^2*x + a01*p*y)*z^3 +
                (a20*p^3*x^2 + a11*x*y + a02*p*y^2)*z^2 +
                (a30*p^4*x^3 + a21*p*x^2*y + a12*x*y^2 + a03*p*y^3)*z +
                a40*p^5*x^4 + a31*p*x^3*y + a22*x^2*y^2 + a13*x*y^3 + a04*p*y^4;
        end if;

    when "(Z=0m)" :
        if Flat then
            f :=
                a00*p^4*z^4 +
                a10*p^4*x*z^3 + a01*p^2*y*z^3 +
                a20*p^3*x^2*z^2 + a11*p^2*x*y*z^2 + a02*p^0*y^2*z^2 +
                a30*p^3*x^3*z + a21*p^2*x^2*y*z + a12*p^2*x*y^2*z + a03*p^1*y^3*z +
                a40*p^5*x^4 + a31*p^4*x^3*y + a22*p^4*x^2*y^2 + a13*p^3*x*y^3 + a04*p^3*y^4;
        else
            f :=
                a00*p^(4*2)*z^4 +
                a10*p^(7)*x*z^3 + a01*p^(2*2)*y*z^3 +
                a20*p^(3*2)*x^2*z^2 + a11*p^(3)*x*y*z^2 + a02*p^(0*2)*y^2*z^2 +
                a30*p^(3*2)*x^3*z + a21*p^(2*2)*x^2*y*z + a12*p^(3)*x*y^2*z + a03*p^(1*2)*y^3*z +
                a40*p^(5*2)*x^4 + a31*p^(4*2)*x^3*y + a22*p^(7)*x^2*y^2 + a13*p^(3*2)*x*y^3 + a04*p^(3*2)*y^4;
        end if;

    when "(0m=0m)" :
        f :=
            a00*p^8*z^4 +
            a10*p^5*x*z^3 + a01*p^4*y*z^3 +
            a20*p^2*x^2*z^2 + a11*p^1*x*y*z^2 + a02*p^0*y^2*z^2 +
            a30*p^0*x^3*z + a21*p^0*x^2*y*z + a12*p^2*x*y^2*z + a03*p^10*y^3*z +
            a40*p^0*x^4 + a31*p^1*x^3*y + a22*p^4*x^2*y^2 + a13*p^10*x*y^3 + a04*p^12*y^4;

    when "(0mmm)" :
        f := Case_0xxx("(0mmm)", p : Domain := Domain, Flat := Flat, K := K);

        // Unknown type
        else:
            error "Unknow type \"" cat Type cat "\"";
    end case;

    return f;

end intrinsic;

/* Product of 2 conics mod p */
function Case_0____0(p : Domain := [-p^3..p^3], Flat := false, K := Rationals())

    K := FieldOfFractions(Universe(Domain));
    Pxy := PolynomialRing(K, 2); x := Pxy.1; y := Pxy.2; z := K!1;

    Pu := PolynomialRing(GF(p)); u := Pu.1;

    a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 :=
        Explode( [K| RandAlg(K, Domain) : i in [1..15] ] );

    b20, b11, b10, b02, b01, b00,  c20, c11, c10, c02, c01, c00 :=
        Explode( [K| RandAlg(K, Domain) : i in [1..12] ] );
    f :=
        (b20*x^2 + b11*x*y + b10*x*z + b02*y^2+ b01*y*z+ b00*z^2)
        *
        (c20*x^2 + c11*x*y + c10*x*z + c02*y^2+ c01*y*z+ c00*z^2) +
        p *
        (
        a00*z^4 +
        a10*x*z^3 + a01*y*z^3 +
        a20*x^2*z^2 + a11*x*y*z^2 + a02*y^2*z^2 +
        a30*x^3*z + a21*x^2*y*z + a12*x*y^2*z + a03*y^3*z +
        a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*x*y^3 + a04*y^4
        );

    return f;
end function;

/* Add a node to one of the genus 1 curve in the construction for (1ne) */
function Case_0nne(p : Domain := [-p^3..p^3], Flat := false, K := Rationals())

    K := FieldOfFractions(Universe(Domain));
    Pxy := PolynomialRing(K, 2); x := Pxy.1; y := Pxy.2; z := K!1;

    Pu := PolynomialRing(GF(p)); u := Pu.1;

    repeat
        repeat
            a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 :=
                Explode( [K| RandAlg(K, Domain) : i in [1..15] ] );
            A00, A10, A01, A02, A03, A04, A11, A12, A13, A20, A21, A22, A30, A31, A40 :=
                Explode( [GF(p) | a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 ] );
            disc :=
                (64*A22*A40^4-16*A31^2*A40^3)*u^3 +
                (-16*A12^2*A40^4+16*A12*A21*A31*A40^3-128*A12*A22*A30*A40^3+24*A12*A30*A31^2*A40^2-48*A21^2*A22*A40^3+8*A21^2*A31^2*A40^2+160*A21*A22*A30*A31*A40^2-36*A21*A30*A31^3*A40+128*A22^2*A30^2*A40^2-144*A22*A30^2*A31^2*A40+27*A30^2*A31^4)*u^2 +
                (32*A12^3*A30*A40^3+8*A12^2*A21^2*A40^3-64*A12^2*A21*A30*A31*A40^2+32*A12^2*A22*A30^2*A40^2+24*A12^2*A30^2*A31^2*A40-8*A12*A21^3*A31*A40^2-8*A12*A21^2*A22*A30*A40^2+46*A12*A21^2*A30*A31^2*A40-16*A12*A21*A22*A30^2*A31*A40-36*A12*A21*A30^2*A31^3-128*A12*A22^2*A30^3*A40+72*A12*A22*A30^3*A31^2+12*A21^4*A22*A40^2-A21^4*A31^2*A40-44*A21^3*A22*A30*A31*A40+A21^3*A30*A31^3+80*A21^2*A22^2*A30^2*A40+30*A21^2*A22*A30^2*A31^2-96*A21*A22^2*A30^3*A31+64*A22^3*A30^4)*u
                -16*A12^4*A30^2*A40^2+8*A12^3*A21^2*A30*A40^2+16*A12^3*A21*A30^2*A31*A40+32*A12^3*A22*A30^3*A40-16*A12^3*A30^3*A31^2-A12^2*A21^4*A40^2-8*A12^2*A21^3*A30*A31*A40-32*A12^2*A21^2*A22*A30^2*A40+8*A12^2*A21^2*A30^2*A31^2+16*A12^2*A21*A22*A30^3*A31-16*A12^2*A22^2*A30^4+A12*A21^5*A31*A40+10*A12*A21^4*A22*A30*A40-A12*A21^4*A30*A31^2-8*A12*A21^3*A22*A30^2*A31+8*A12*A21^2*A22^2*A30^3-A21^6*A22*A40+A21^5*A22*A30*A31-A21^4*A22^2*A30^2;
        until Degree(disc) eq 3;

        rts := Roots(disc);
    until #rts gt 1;

    a02 := K!(Integers()!rts[1, 1]) + p * RandAlg(K, Domain);

    if Flat then
        f :=
            a00*p*z^4 +
            a10*p*x*z^3 + a01*p*y*z^3 +
            (a20*p*x^2 + a11*p*x*y + a02*y^2)*z^2+
            (a03*p*y^3 + a12*x*y^2 + a21*x^2*y + a30*x^3)*z+
            a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*p*x*y^3 + a04*p*y^4;
    else
        f :=
            a00*p^6*z^4 +
            a10*p^4*x*z^3 + a01*p^3*y*z^3 +
            (a20*p^2*x^2 + a11*p*x*y + a02*y^2)*z^2+
            (a03*p*y^3 + a12*x*y^2 + a21*x^2*y + a30*x^3)*z+
            a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*p*x*y^3 + a04*p*y^4;
    end if;

    return f;
end function;

/* Add a node to one of the genus 1 curve in the construction for (1nm) */
function Case_0nnm(p : Domain := [-p^3..p^3], Flat := false, K := Rationals())

    K := FieldOfFractions(Universe(Domain));
    Pxy := PolynomialRing(K, 2); x := Pxy.1; y := Pxy.2; z := K!1;

    Pu := PolynomialRing(GF(p)); u := Pu.1;

    repeat
        repeat
            a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 :=
                Explode( [K| RandAlg(K, Domain) : i in [1..15] ] );
            A00, A10, A01, A02, A03, A04, A11, A12, A13, A20, A21, A22, A30, A31, A40 :=
                Explode( [GF(p) | a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 ] );
            disc :=
                (64*A22*A40^4-16*A31^2*A40^3)*u^3 +
                (-16*A12^2*A40^4+16*A12*A21*A31*A40^3-128*A12*A22*A30*A40^3+24*A12*A30*A31^2*A40^2-48*A21^2*A22*A40^3+8*A21^2*A31^2*A40^2+160*A21*A22*A30*A31*A40^2-36*A21*A30*A31^3*A40+128*A22^2*A30^2*A40^2-144*A22*A30^2*A31^2*A40+27*A30^2*A31^4)*u^2 +
                (32*A12^3*A30*A40^3+8*A12^2*A21^2*A40^3-64*A12^2*A21*A30*A31*A40^2+32*A12^2*A22*A30^2*A40^2+24*A12^2*A30^2*A31^2*A40-8*A12*A21^3*A31*A40^2-8*A12*A21^2*A22*A30*A40^2+46*A12*A21^2*A30*A31^2*A40-16*A12*A21*A22*A30^2*A31*A40-36*A12*A21*A30^2*A31^3-128*A12*A22^2*A30^3*A40+72*A12*A22*A30^3*A31^2+12*A21^4*A22*A40^2-A21^4*A31^2*A40-44*A21^3*A22*A30*A31*A40+A21^3*A30*A31^3+80*A21^2*A22^2*A30^2*A40+30*A21^2*A22*A30^2*A31^2-96*A21*A22^2*A30^3*A31+64*A22^3*A30^4)*u
                -16*A12^4*A30^2*A40^2+8*A12^3*A21^2*A30*A40^2+16*A12^3*A21*A30^2*A31*A40+32*A12^3*A22*A30^3*A40-16*A12^3*A30^3*A31^2-A12^2*A21^4*A40^2-8*A12^2*A21^3*A30*A31*A40-32*A12^2*A21^2*A22*A30^2*A40+8*A12^2*A21^2*A30^2*A31^2+16*A12^2*A21*A22*A30^3*A31-16*A12^2*A22^2*A30^4+A12*A21^5*A31*A40+10*A12*A21^4*A22*A30*A40-A12*A21^4*A30*A31^2-8*A12*A21^3*A22*A30^2*A31+8*A12*A21^2*A22^2*A30^3-A21^6*A22*A40+A21^5*A22*A30*A31-A21^4*A22^2*A30^2;
        until Degree(disc) eq 3;

        rts := Roots(disc);
    until #rts gt 1;

    a02 := K!(Integers()!rts[1, 1]) + p * RandAlg(K, Domain);

    if Flat then
        f :=
            a00*p^4*z^4 +
            a10*p^3*x*z^3 + a01*p^2*y*z^3 +
            (a20*p^1*x^2 + a11*p*x*y + a02*y^2)*z^2+
            (a03*p*y^3 + a12*x*y^2 + a21*x^2*y + a30*x^3)*z+
            a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*p*x*y^3 + a04*p^1*y^4;

    else
        f :=
            a00*p^7*z^4 +
            a10*p^5*x*z^3 + a01*p^4*y*z^3 +
            (a20*p^2*x^2 + a11*p*x*y + a02*y^2)*z^2+
            (a03*p*y^3 + a12*x*y^2 + a21*x^2*y + a30*x^3)*z+
            a40*x^4 + a31*x^3*y + a22*x^2*y^2 + a13*p*x*y^3 + a04*p^1*y^4;
    end if;

    return f;
end function;

/* Add a node to one of the genus 1 curve in the construction for (1ee) */
function Case_0nee(p : Domain := [-p^3..p^3], Flat := false, K := Rationals())

    K := FieldOfFractions(Universe(Domain));
    Pxy := PolynomialRing(K, 2); x := Pxy.1; y := Pxy.2; z := K!1;

    Pu := PolynomialRing(GF(p)); u := Pu.1;

    repeat
        repeat
            a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 :=
                Explode( [K| RandAlg(K, Domain) : i in [1..15] ] );
            A00, A10, A01, A02, A03, A04, A11, A12, A13, A20, A21, A22, A30, A31, A40 :=
                Explode( [GF(p) | a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 ] );
            disc :=
                16*A40^3*u^2 +
                (-8*A21^2*A40^2+36*A21*A30*A31*A40-27*A30^2*A31^2)*u +
                A21^4*A40-A21^3*A30*A31;
        until Degree(disc) eq 2;

        rts := Roots(disc);
    until #rts gt 1;

    a02 := K!(Integers()!rts[1, 1]) + p * RandAlg(K, Domain);

    if Flat then
        f :=
            a00*p*z^4 +
            a10*p^1*x*z^3 + a01*p^1*y*z^3 +
            a20*p^1*x^2*z^2 + a11*p^1*x*y*z^2 + a02*y^2*z^2 +
            a30*x^3*z + a21*x^2*y*z + a12*p^1*x*y^2*z + a03*p^1*y^3*z +
            a40*x^4 + a31*x^3*y + a22*p^1*x^2*y^2 + a13*p^1*x*y^3 +
            a04*p^1*y^4;
    else
        f :=
            a00*p^6*z^4 +
            a10*p^4*x*z^3 + a01*p^3*y*z^3 +
            (a20*p^2*x^2 + a11*p*x*y + a02*y^2)*z^2+
            (a03*p^3*y^3 + a12*p*x*y^2 + a21*x^2*y + a30*x^3)*z+
            a40*x^4 + a31*x^3*y + a22*p^2*x^2*y^2 + a13*p^4*x*y^3 + a04*p^6*y^4;
    end if;

    return f;
end function;

/* Add a node to one of the genus 1 curve in the construction for (1me) */
function Case_0nme(p : Domain := [-p^3..p^3], Flat := false, K := Rationals())

    K := FieldOfFractions(Universe(Domain));
    Pxy := PolynomialRing(K, 2); x := Pxy.1; y := Pxy.2; z := K!1;

    Pu := PolynomialRing(GF(p)); u := Pu.1;

    repeat
        repeat
            a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 :=
                Explode( [K| RandAlg(K, Domain) : i in [1..15] ] );
            A00, A10, A01, A02, A03, A04, A11, A12, A13, A20, A21, A22, A30, A31, A40 :=
                Explode( [GF(p) | a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 ] );
            disc := 27*A01*A10*u+A11^3;
        until Degree(disc) eq 1;

        rts := Roots(disc);
    until #rts eq 1;

    a22 := K!(Integers()!rts[1, 1]) + p * RandAlg(K, Domain);

    f :=
        a00*p^(2*2)*z^4 +
        a10*p^(0*2)*x*z^3 + a01*p^(0*2)*y*z^3 +
        a20*p^(1*2)*x^2*z^2 + a11*p^(0*2)*x*y*z^2 + a02*p^(1*2)*y^2*z^2 +
        a30*p^(2*2)*x^3*z + a21*p^(1)*x^2*y*z + a12*p^(1)*x*y^2*z + a03*p^(7)*y^3*z +
        a40*p^(1*6)*x^4 + a31*p^(3)*x^3*y + a22*x^2*y^2 + a13*p^(1*6)*x*y^3 + a04*p^(2*6)*y^4;

    return f;
end function;

/* Add a node to one of the genus 1 curve in the construction for (1mm) */
function Case_0nmm(p : Domain := [-p^3..p^3], Flat := false, K := Rationals())

    K := FieldOfFractions(Universe(Domain));
    Pxy := PolynomialRing(K, 2); x := Pxy.1; y := Pxy.2; z := K!1;

    Pu := PolynomialRing(GF(p)); u := Pu.1;

    repeat
        repeat
            a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 :=
                Explode( [K| RandAlg(K, Domain) : i in [1..15] ] );
            A00, A10, A01, A02, A03, A04, A11, A12, A13, A20, A21, A22, A30, A31, A40 :=
                Explode( [GF(p) | a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 ] );
            disc := 27*A01*A10*u+A11^3;
        until Degree(disc) eq 1;

        rts := Roots(disc);
    until #rts eq 1;

    a22 := K!(Integers()!rts[1, 1]) + p * RandAlg(K, Domain);

    f :=
        a00*p^(2*6)*z^4 +
        a10*p^(1*6)*x*z^3 + a01*p^(1*6)*y*z^3 +
        a20*p^(1*6)*x^2*z^2 + a11*p^(4)*x*y*z^2 + a02*p^(1*6)*y^2*z^2 +
        a30*p^(9)*x^3*z + a21*p^(3)*x^2*y*z + a12*p^(3)*x*y^2*z + a03*p^(9)*y^3*z +
        a40*p^(2*6)*x^4 + a31*p^(1*6)*x^3*y + a22*p^(0*6)*x^2*y^2 + a13*p^(1*6)*x*y^3 +
        a04*p^(2*6)*y^4;

    return f;
end function;

function Case_0xxx_bak(Type, p : Domain := [-p^3..p^3], Flat := false, K := Rationals())

    K := FieldOfFractions(Universe(Domain));
    Pxy := PolynomialRing(K, 2); x := Pxy.1; y := Pxy.2; z := K!1;

    Pu := PolynomialRing(GF(p)); u := Pu.1;

    while true do
        a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 :=
            Explode( [K| RandAlg(K, Domain) : i in [1..15] ] );
        A00, A10, A01, A02, A03, A04, A11, A12, A13, A20, A21, A22, A30, A31, A40 :=
            Explode( [GF(p) | a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 ] );

        if 0 in {A20, A11, A02, A12, A22, A21} then continue; end if;

        // A11^2-4*A02*A20 = 0, A21^2-4*A20*A22 = 0, A12^2-4*A02*A22 = 0;

        A02 := A12^2/A22/4;
        A20 := A21^2/A22/4;

        ret, sqrt := IsSquare(4*A02*A20);
        if not ret then continue; end if;

        A11 := sqrt;

        if  2*A02*A21 + A11*A12 ne 0 or
            A11*A21 + 2*A12*A20 ne 0 or
            2*A11*A22 + A12*A21 ne 0 then A11 := -sqrt; end if;


        if Type in {"(0mee)", "(0mme)", "(0mmm)"}  then
            disc := u^2*A20 - u*A10*A11 + A02*A10^2;
            if Degree(disc) le 1 then continue; end if;

            rts := Roots(disc);
            if #rts le 0 then continue; end if;

            A01 := rts[1, 1];
        end if;

        if Type in {"(0mme)", "(0mmm)"}  then
            disc := A02*u^2 + A03^2*A22 - A03*A12*u;
            if Degree(disc) le 1 then continue; end if;

            rts := Roots(disc);
            if #rts le 0 then continue; end if;

            A13 := rts[1, 1];
        end if;

        if Type in {"(0mmm)"}  then
            disc := A20*u^2 - A21*A30*u + A22*A30^2;
            if Degree(disc) le 1 then continue; end if;

            rts := Roots(disc);
            if #rts le 0 then continue; end if;

            A31 := rts[1, 1];
            break;
        end if;

        break;
    end while;

    a02 := K!(Integers()!A02) + p * RandAlg(K, Domain);
    a20 := K!(Integers()!A20) + p * RandAlg(K, Domain);
    a11 := K!(Integers()!A11) + p * RandAlg(K, Domain);

    if Type in {"(0mee)", "(0mme)", "(0mmm)"} then
        a01 := K!(Integers()!A01) + p * RandAlg(K, Domain);
    end if;
    if Type in {"(0mme)", "(0mmm)"} then
        a13 := K!(Integers()!A13) + p * RandAlg(K, Domain);
    end if;
    if Type in {"(0mmm)"} then
        a31 := K!(Integers()!A31) + p * RandAlg(K, Domain);
    end if;

    f :=
        a00*p^2*z^4 +
        (a10*p^1*x + a01*p^1*y)*z^3 +
        (a20*x^2 + a11*x*y + a02*y^2)*z^2 +
        (a03*p*y^3 + a12*x*y^2 + a21*x^2*y + a30*p*x^3)*z +
        a40*p^2*x^4 + a31*p*x^3*y + a22*x^2*y^2 + a13*p*x*y^3 + a04*p^2*y^4;

    c := Integers()!(-A11/2/A02);
    return Evaluate(f, [ x, y + c * x ]);



end function;


function Case_0xxx_foo(Type, p : Domain := [-p^3..p^3], Flat := false, K := Rationals())

    K := FieldOfFractions(Universe(Domain));
    Pxy := PolynomialRing(K, 2); x := Pxy.1; y := Pxy.2; z := K!1;

    Pu := PolynomialRing(GF(p)); u := Pu.1;

    while true do

        a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 :=
            Explode( [K| RandAlg(K, Domain) : i in [1..15] ] );
        A00, A10, A01, A02, A03, A04, A11, A12, A13, A20, A21, A22, A30, A31, A40 :=
            Explode( [GF(p) | a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 ] );

        if 0 in {A20, A11, A02, A12, A22, A21} then continue; end if;

        // A11^2-4*A02*A20 = 0, A21^2-4*A20*A22 = 0, A12^2-4*A02*A22 = 0;

        A02 := A12^2/A22/4;
        a02 := K!(Integers()!A02) + p * RandAlg(K, Domain);

        A20 := A21^2/A22/4;
        a20 := K!(Integers()!A20) + p * RandAlg(K, Domain);

        ret, sqrt := IsSquare(4*A02*A20);
        if not ret then continue; end if;

        A11 := sqrt;

        if  2*A02*A21 + A11*A12 ne 0 or
            A11*A21 + 2*A12*A20 ne 0 or
            2*A11*A22 + A12*A21 ne 0 then A11 := -sqrt; end if;

        a11 := K!(Integers()!A11) + p * RandAlg(K, Domain);



        b := Integers()!(-A11/2/A02);

        b00 := A00;
        b10 := A01*b+A10;
        b20 := GF(p)!(Integers()!(a02*b^2+a11*b+a20) div p);
        b30 := A12*b^2+A21*b;

        disc := 27*b00^2*b30^2-18*b00*u*b20*b30+4*b00*b20^3+4*u^3*b30-u^2*b20^2;
        if Degree(disc) le 1 then continue; end if;

        rts := Roots(disc);
        if #rts le 0 then continue; end if;

        B10 := rts[1, 1];
        A10 := B10-A01*b;
        a10 := K!(Integers()!A10) + p * RandAlg(K, Domain);



        a := Integers()!(-A12/2/A22);

        b00 := A04;
        b10 := a*A13+A03;
        b20 := GF(p)!(Integers()!(a^2*a22+a*a12+a02) div p);
        b30 := a^2*A21+a*A11;

        disc := 27*b00^2*b30^2-18*b00*u*b20*b30+4*b00*b20^3+4*u^3*b30-u^2*b20^2;
        if Degree(disc) le 1 then continue; end if;

        rts := Roots(disc);
        if #rts le 0 then continue; end if;

        B10 := rts[1, 1];
        A03 := B10-A13*a;
        a03 := K!(Integers()!A03) + p * RandAlg(K, Domain);


        c := Integers()!(-A21/2/A20);

        b00 := A40;
        b10 := A30*c+A31;
        b20 := GF(p)!(Integers()!(a20*c^2+a21*c+a22) div p);
        b30 := A11*c^2+A12*c;

        disc := 27*b00^2*b30^2-18*b00*u*b20*b30+4*b00*b20^3+4*u^3*b30-u^2*b20^2;
        if Degree(disc) le 1 then continue; end if;

        rts := Roots(disc);
        if #rts le 0 then continue; end if;

        B10 := rts[1, 1];
        A31 := B10-A30*c;
        a31 := K!(Integers()!A31) + p * RandAlg(K, Domain);


        break;
    end while;




    /*
    X := x;
    Y := y + b*x;
    Z := z;// + c*x;

    */

    a := Integers()!(-A12/2/A22);
    b := Integers()!(-A11/2/A02);
    c := Integers()!(-A21/2/A20);

    // A11^2-4*A02*A20 = 0, A21^2-4*A20*A22 = 0, A12^2-4*A02*A22 = 0;
    X := x;// + a*z;
    Y := y;// + b*x;
    Z := z;// + c*y;

    f :=
        a00*p^3 * Z^4 +
        (a10*p^2*X + a01*p^2*Y) * Z^3 +
        (a20*X^2 + a11*X*Y + a02*Y^2) * Z^2 +
        (a30*p^2*X^3 + a21*X^2*Y + a12*X*Y^2 + a03*p^2*Y^3) * Z +
        a40*p^3*X^4 + a31*p^2*X^3*Y + a22*X^2*Y^2 + a13*p^2*X*Y^3 + a04*p^3*Y^4;

    return f;



end function;



/*

a00*p^3*z^4+
    ((-a01*p^3*c+a10*p^2)*x+a01*p^3*y)*z^3+
    (a02*y^2 +(-2*a02*c+a11)*y*x+(a02*c^2-a11*c+a20)*x^2)*z^2+
    ((-a03*p*c^3+a12*c^2-a21*c+a30*p)*x^3+a03*p*y^3+(3*a03*c^2*p-2*a12*c+a21)*y*x^2+(-3*a03*c*p+a12)*y^2*x)*z+
    (6*a04*p^2*c^2-3*a13*p*c+a22)*y^2*x^2+(a04*p^2*c^4-a13*p*c^3+a22*c^2-a31*p*c+a40*p^2)*x^4+(-4*a04*p^2*c+a13*p)*y^3*x+(-4*a04*p^2*c^3+3*a13*p*c^2-2*a22*c+a31*p)*y*x^3+a04*p^2*y^4;

a00*p^2*z^4+
((a01*c*p+a10*p)*x+a01*p*y)*z^3+
((2*a02*c+a11)*y*x+(a02*c^2+a11*c+a20)*x^2+a02*y^2)*z^2+
((3*a03*c^2*p+2*a12*c+a21)*y*x^2+(a03*p*c^3+a12*c^2+a21*c+a30*p)*x^3+a03*p*y^3+(3*a03*c*p+a12)*y^2*x)*z+
(4*a04*p^2*c^3+3*a13*p*c^2+2*a22*c+a31*p)*y*x^3+(a04*p^2*c^4+a13*p*c^3+a22*c^2+a31*p*c+a40*p^2)*x^4+a04*p^2*y^4+(6*a04*p^2*c^2+3*a13*p*c+a22)*y^2*x^2+(4*a04*p^2*c+a13*p)*y^3*x


*/
function Case_0xxx_test(Type, p : Domain := [-p^3..p^3], Flat := false, K := Rationals())

    K := FieldOfFractions(Universe(Domain));
    Pxy := PolynomialRing(K, 2); x := Pxy.1; y := Pxy.2; z := K!1;

    Pu := PolynomialRing(GF(p)); u := Pu.1;

    while true do
        a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 :=
            Explode( [K| RandAlg(K, Domain) : i in [1..15] ] );
        A00, A10, A01, A02, A03, A04, A11, A12, A13, A20, A21, A22, A30, A31, A40 :=
            Explode( [GF(p) | a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 ] );

        if 0 in {A21, A30, A31, A40} then continue; end if;

        disc0 := 16*u^2*A40^3+(-8*A21^2*A40^2+36*A21*A30*A31*A40-27*A30^2*A31^2)*u+A21^4*A40-A21^3*A30*A31;
        if Degree(disc0) le 1 then continue; end if;
        rts0 := Roots(disc0);
        if #rts0 ne 1 then continue; end if;
        A02 := rts0[1, 1];
        if A02 eq 0 then continue; end if;

        break;
    end while;

    a02 := K!(Integers()!A02) + p * RandAlg(K, Domain);

    f :=
        a00*p^6*z^4 +
        a10*p^4*x*z^3 + a01*p^3*y*z^3 +
        (a20*p^2*x^2 + a11*p*x*y + a02*y^2)*z^2+
        (a03*p^3*y^3 + a12*p*x*y^2 + a21*x^2*y + a30*x^3)*z+
        a40*x^4 + a31*x^3*y + a22*p^2*x^2*y^2 + a13*p^4*x*y^3 + a04*p^6*y^4;

    f :=
        64327*x^4 + 5610*x^3*y + 478310*x^3 + 2844202016*x^2*y^2 - 244600*x^2*y -
        456617162*x^2 + 78931375064515*x*y^3 - 80120472*x*y^2 + 64524658*x*y +
        90733385443930*x - 336764083217715447*y^4 + 900306892529*y^3 + 19313692*y^2
    - 907750817254*y - 687722813889267466;
   //return f;

    _<X,Y,Z> := PolynomialRing(K, 3);
    F := Homogenization(Evaluate(f, [X, Y]), Z);
    F := Evaluate(F, [ 94*X, 84*X + Y, X + Z ]);
/*
    return Evaluate(F, [
        72*x,
        12*x + y,
        29*x + z]);
*/
    return Evaluate(F, [x, y, z]);

/*

FF := GF(101);
Pxyz<x,y,z> := PolynomialRing(FF, 3);

_<A,B,C, D,E,F, G,H,I> := PolynomialRing(FF, 9);

    x0, y0, z0 := Explode([FF | 0, 0, 1]);
    x1, y1, z1 := Explode([FF | 0, 1, 0]);
    x2, y2, z2 := Explode([FF | 94, 84, 1]);

Sys := [
    A*x0+B*y0+C*z0-0, D*x0+E*y0+F*z0-0, G*x0+H*y0+I*z0-1,
    A*x1+B*y1+C*z1-0, D*x1+E*y1+F*z1-1, G*x1+H*y1+I*z1-0,
    A*x2+B*y2+C*z2-1, D*x2+E*y2+F*z2-0, G*x2+H*y2+I*z2-0
    ];

GB := GroebnerBasis(Sys);
GB;
A,B,C, D,E,F, G,H,I := Explode(ChangeUniverse(NormalForm([A,B,C, D,E,F, G,H,I], GB), FF));

A,B,C, D,E,F, G,H,I := Explode(Eltseq(Matrix(FF, [[A, B, C], [D, E, F], [G, H, I]])^-1));

[A*x+B*y+C*z, D*x+E*y+F*z, G*x+H*y+I*z];

[ 94*X, 84*X + Y, X + Z ]);

*/


end function;

function Case_0xxx(Type, p : Domain := [-p^3..p^3], Flat := false, K := Rationals())

    K := FieldOfFractions(Universe(Domain));
    Pxy := PolynomialRing(K, 2); x := Pxy.1; y := Pxy.2; z := K!1;

    Pu := PolynomialRing(GF(p)); u := Pu.1;

    while true do
        a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 :=
            Explode( [K| RandAlg(K, Domain) : i in [1..15] ] );
        A00, A10, A01, A02, A03, A04, A11, A12, A13, A20, A21, A22, A30, A31, A40 :=
            Explode( [GF(p) | a00, a10, a01, a02, a03, a04, a11, a12, a13, a20, a21, a22, a30, a31, a40 ] );

        if 0 in {A20, A11, A02, A12, A22, A21} then continue; end if;

        // A11^2-4*A02*A20 = 0, A21^2-4*A20*A22 = 0, A12^2-4*A02*A22 = 0;

        A02 := A12^2/A22/4;
        a02 := K!(Integers()!A02) + p * RandAlg(K, Domain);

        A20 := A21^2/A22/4;
        a20 := K!(Integers()!A20) + p * RandAlg(K, Domain);

        ret, sqrt := IsSquare(4*A02*A20);
        if not ret then continue; end if;

        A11 := sqrt;
        if  2*A02*A21 + A11*A12 ne 0 or
            A11*A21 + 2*A12*A20 ne 0 or
            2*A11*A22 + A12*A21 ne 0 then A11 := -sqrt; end if;
        a11 := K!(Integers()!A11) + p * RandAlg(K, Domain);

        a := Integers()!(-A12/2/A22);
        if Type in {"(0mee)", "(0mme)", "(0mmm)"}  then

            b00 := A04;
            b10 := a*A13+A03;
            b20 := GF(p)!(Integers()!(a^2*a22+a*a12+a02) div p);
            b30 := a^2*A21+a*A11;

            disc := 27*b00^2*b30^2-18*b00*u*b20*b30+4*b00*b20^3+4*u^3*b30-u^2*b20^2;
            if Degree(disc) le 1 then continue; end if;

            rts := Roots(disc);
            if #rts le 0 then continue; end if;
            B10 := rts[1, 1];

            A03 := B10-A13*a;
            a03 := K!(Integers()!A03) + p * RandAlg(K, Domain);
        end if;

        b := Integers()!(-A11/2/A02);
        if Type in {"(0mme)", "(0mmm)"}  then

            b00 := A00;
            b10 := A01*b+A10;
            b20 := GF(p)!(Integers()!(a02*b^2+a11*b+a20) div p);
            b30 := A12*b^2+A21*b;

            disc := 27*b00^2*b30^2-18*b00*u*b20*b30+4*b00*b20^3+4*u^3*b30-u^2*b20^2;
            if Degree(disc) le 1 then continue; end if;

            rts := Roots(disc);
            if #rts le 0 then continue; end if;
            B10 := rts[1, 1];

            A10 := B10-A01*b;
            a10 := K!(Integers()!A10) + p * RandAlg(K, Domain);
        end if;

        c := Integers()!(-A21/2/A20);
        if Type in {"(0mmm)"}  then

            b00 := A40;
            b10 := A30*c+A31;
            b20 := GF(p)!(Integers()!(a20*c^2+a21*c+a22) div p);
            b30 := A11*c^2+A12*c;

            disc := 27*b00^2*b30^2-18*b00*u*b20*b30+4*b00*b20^3+4*u^3*b30-u^2*b20^2;
            if Degree(disc) le 1 then continue; end if;

            rts := Roots(disc);
            if #rts le 0 then continue; end if;
            B10 := rts[1, 1];

            A31 := B10-A30*c;
            a31 := K!(Integers()!A31) + p * RandAlg(K, Domain);
        end if;

        break;
    end while;

    X := x;// + a*z;
    Y := y;// + b*x;
    Z := z;// + c*y;

    f :=
        a00*p^3 * Z^4 +
        (a10*p^2*X + a01*p^2*Y) * Z^3 +
        (a20*X^2 + a11*X*Y + a02*Y^2) * Z^2 +
        (a30*p^2*X^3 + a21*X^2*Y + a12*X*Y^2 + a03*p^2*Y^3) * Z +
        a40*p^3*X^4 + a31*p^2*X^3*Y + a22*X^2*Y^2 + a13*p^2*X*Y^3 + a04*p^3*Y^4;

    return f;

end function;

/* See Table 9.1 in "Semistable types of hyperelliptic curves",
   by Tim Dokchitser, Vladimir Dokchitser, Celine Maistret, Adam Morgan
   (https://arxiv.org/pdf/1704.08338.pdf)
*/

intrinsic G3HyperReductionType(Type::MonStgElt, p::RngIntElt :
    Domain := [-p^4..p^4], K := Rationals())  -> RngMPolElt

    { Return an hyperelliptic curve defined over Q, with coefficients randomly chosen in Domain, such that its reduction modulo p is of the given Type.}

    K := FieldOfFractions(Universe(Domain));
    Px := PolynomialRing(K); x := Px.1;

    a0, a1, a2, a3, a4, a5, a6, a7 :=
        Explode( [K| RandAlg(K, Domain) : i in [1..8] ] );
    f := Px!0;

    case Type:

        // Codimension 0
    when "[3]" : /* 3 */
        f := (x-a0) * (x-a1) * (x-a2) * (x-a3) * (x-a4) * (x-a5) * (x-a6) * (x-a7);
        val := 1;

        // Codimension 1
    when "[2n]" : /* 2n */
        f :=
            (x-a0) * (x-a1) * (x-a2) * (x-a3) * (x-a4) * (x-a5) *
            (x-0+p*a6) * (x-0+p*a7);
        val := 1;

    when "[2e]" : /* 2.1 */
        f :=
            (x-a0) * (x-a1) * (x-a2) * (x-a3) * (x-a4) *
            (x-0+p*a5) * (x-0+p*a6) * (x-0+p*a7);
        val := 1;

        // Codimension 2
    when "[1nn]" : /* 1n,m */
        f :=
            (x-a0) * (x-a1) * (x-a2) * (x-a3) *
            (x-1+p*a4) * (x-1+p*a5) *
            (x-0+p*a6) * (x-0+p*a7);
        val := 1;

    when "[1=1]" : /* 1o1 */
        f :=
            (x-0+p*a0) * (x-0+p*a1) * (x-0+p*a2) * (x-0+p*a3) *
            (x-1+p*a4) * (x-1+p*a5) * (x-1+p*a6) * (x-1+p*a7);
        val := 1;

    when "[2m]" : /* 2.In */
        f :=
            (x-a0) * (x-a1) * (x-a2) * (x-a3) * (x-a4) *
            (x-0+p*a5) * (x-0+p^2*a6) * (x-0+p^2*a7);
        val := 2;

    when "[1ne]" : /* 1n.1 */
        f :=
            (x-a0) * (x-a1) * (x-a2) *
            (x-1+p*a3) * (x-1+p*a4) *
            (x-0+p*a5) * (x-0+p*a6) * (x-0+p*a7);
        val := 1;

    when "[1ee]" : /* 1.1.1 */
        f :=
            (x-a0) * (x-a1) *
            (x-1+p*a2) * (x-1+p*a3) * (x-1+p*a4) *
            (x-0+p*a5) * (x-0+p*a6) * (x-0+p*a7);
        val := 1;

        // Codimension 3
    when "[0nnn]" : /* In,m,r */
        f :=
            (x-a0) * (x-a1) *
            (x+1+p*a2) * (x+1+p*a3) *
            (x-1+p*a4) * (x-1+p*a5) *
            (x-0+p*a6) * (x-0+p*a7);
        val := 1;

    when "[1=0n]" : /* 1oIn */
        f :=
            (x-1+p*a0) * (x-1+p*a1) * (x-1+p*a2) * (x-1+p*a3) *
            (x-0+p*a4) * (x-0+p*a5) *
            (x-0+p^2*a6) * (x-0+p^2*a7);
        val := 3;

    when "[0nne]" : /* 0n,m.1 */
        f :=
            (x-a0) *
            (x+1+p*a1) * (x+1+p*a2) *
            (x-1+p*a3) * (x-1+p*a4) *
            (x-0+p*a5) * (x-0+p*a6) * (x-0+p*a7);
        val := 1;

    when "[1nm]" : /* 1n.Im */
        f :=
            (x-a0) * (x-a1) * (x-a2) *
            (x-1+p*a3) * (x-1+p*a4) *
            (x-0+p*a5) * (x-0+p^2*a6) * (x-0+p^2*a7);
        val := 2;

    when "[1=0e]" : /* 1o0.1 */
        f :=
            (x-1+p*a0) * (x-1+p*a1) * (x-1+p*a2) * (x-1+p*a3) *
            (x-0+p*a4) *
            (x-0+p^2*a5) * (x-0+p^2*a6) * (x-0+p^2*a7);
        val := 3;

    when "[1me]" : /* 1.1.In */
        f :=
            (x-a0) * (x-a1) *
            (x-1+p*a2) * (x-1+p*a3) * (x-1+p*a4) *
            (x-0+p*a5) * (x-0+p^2*a6) * (x-0+p^2*a7);
        val := 2;

    when "[0nee]" : /* 0n.1.1 */
        f :=
            (x+1+p*a0) * (x+1+p*a1) *
            (x-1+p*a2) * (x-1+p*a3) * (x-1+p*a4) *
            (x-0+p*a5) * (x-0+p*a6) * (x-0+p*a7);
        val := 1;

        // Codimension 4
    when "[0----0]" : /* Un,m,r,s */
        f :=
            (x+1+p*a0) * (x+1+p*a1) *
            (x-2+p*a2) * (x-2+p*a3) *
            (x-1+p*a4) * (x-1+p*a5) *
            (x-0+p*a6) * (x-0+p*a7);
        val := 1;

    when "[0n=0n]" : /* InoIm */
        f :=
            (x-1+p*a0) * (x-1+p*a1) *
            (x-1+p^2*a2) * (x-1+p^2*a3) *
            (x-0+p*a4) * (x-0+p*a5) *
            (x-0+p^2*a6) * (x-0+p^2*a7);
        val := 3;

    when "[0nnm]" : /* 0n,m.Ir */
        f :=
            (x-a0) *
            (x+1+p*a1) * (x+1+p*a2) *
            (x-1+p*a3) * (x-1+p*a4) *
            (x-0+p*a5) * (x-0+p^2*a6) * (x-0+p^2*a7);
        val := 2;

    when "[Z=1]" : /* 1oUn,m */
        f :=
            (x-1+p*a0) * (x-1+p*a1) * (x-1+p*a2) * (x-1+p*a3) *
            (x-0+p*(1+p*a4)) * (x-0+p*(1+p*a5)) * (x-0+p*(-1+p*a6)) * (x-0+p*(-1+p*a7));
        val := 3;

    when "[1=0m]" : /* 1o0.In */
        f :=
            (x-1+p*a0) * (x-1+p*a1) * (x-1+p*a2) * (x-1+p*a3) *
            (x-p*a4) * (x-p^2*a5) * (x-p^3*a6) * (x-p^3*a7);
        val := 4;

    when "[0n=0e]" : /* Ino0.1 */
        f :=
            (x-1+p*a0) * (x-1+p*a1) * (x-1+p^2*a2) * (x-1+p^2*a3) *
            (x-p*a4) * (x-p^2*a5) * (x-p^2*a6) * (x-p^2*a7);
        val := 3;

    when "[1mm]" : /* 1.In.Im */
        f :=
            (x-a0) * (x-a1) *
            (x-1+p*a2) * (x-1+p^2*a3) * (x-1+p^2*a4) *
            (x-p*a5) * (x-p^2*a6) * (x-p^2*a7);
        val := 2;

    when "[0e=0e]" : /* 0.1o0.1 */
        f :=
            (x-1+p*a0) * (x-1+p^2*a1) * (x-1+p^2*a2) * (x-1+p^2*a3) *
            (x-p*a4) * (x-p^2*a5) * (x-p^2*a6) * (x-p^2*a7);
        val := 3;

    when "[0nme]" : /* 0n.1.Im */
        f :=
            (x+1+p*a0) * (x+1+p*a1) *
            (x-1+p*a2) * (x-1+p*a3) * (x-1+p*a4) *
            (x-p*a5) * (x-p^2*a6) * (x-p^2*a7);
        val := 2;

        // Codimension 5
    when "[Z=0n]" : /* InoUm,r */
        f :=
            (x-1+p*a0) * (x-1+p*a1) * (x-1+p^2*a2) * (x-1+p^2*a3) *
            (x-p*(1+p*a4)) * (x-p*(1+p*a5)) * (x-p^2*a6) * (x-p^2*a7);
        val := 3;

    when "[0n=0m]" : /* Ino0.Im */
        f :=
            (x-1+p*a0) * (x-1+p*a1) * (x-1+p^2*a2) * (x-1+p^2*a3) *
            (x-p*a4) * (x-p^2*a5) * (x-p^3*a6) * (x-p^3*a7);
        val := 4;

    when "[0nmm]" : /* 0n.Im.Ir */
        f :=
            (x+1+p*a0) * (x+1+p*a1) *
            (x-1+p*a2) * (x-1+p^2*a3) * (x-1+p^2*a4) *
            (x-p*a5) * (x-p^2*a6) * (x-p^2*a7);
        val := 2;

    when "[Z=0e]" : /* Un,mo0.1 */
        f :=
            (x-1+p*(1+p*a0)) * (x-1+p*(1+p*a1)) * (x-1+p^2*a2) * (x-1+p^2*a3) *
            (x-p*a4) * (x-p^2*a5) * (x-p^2*a6) * (x-p^2*a7);
        val := 3;

    when "[0m=0e]" : /* 0.Ino0.1 */
        f :=
            (x-1+p*a0) * (x-1+p^2*a1) * (x-1+p^3*a2) * (x-1+p^3*a3) *
            (x-p*a4) * (x-p^2*a5) * (x-p^2*a6) * (x-p^2*a7);
        val := 4;

        // Codimension 6
    when "[Z=Z]" : /* Un,moUr,s */
        f :=
            (x-1+p*(1+p*a0)) * (x-1+p*(1+p*a1)) * (x-1+p^2*a2) * (x-1+p^2*a3) *
            (x-p*(1+p*a4)) * (x-p*(1+p*a5)) * (x-p^2*a6) * (x-p^2*a7);
        val := 3;

    when "[Z=0m]" : /* Un,mo0.Ir */
        f :=
            (x-1+p*(1+p*a0)) * (x-1+p*(1+p*a1)) * (x-1+p^2*a2) * (x-1+p^2*a3) *
            (x-p*a4) * (x-p^2*a5) * (x-p^3*a6) * (x-p^3*a7);
        val := 4;

    when "[0m=0m]" : /* 0.Ino0.Im */
        f :=
            (x-1+p*a0) * (x-1+p^2*a1) * (x-1+p^3*a2) * (x-1+p^3*a3) *
            (x-p*a4) * (x-p^2*a5) * (x-p^3*a6) * (x-p^3*a7);
        val := 4;

        // Unknown type
        else:
            error "Unknow type \"" cat Type cat "\"";
    end case;

    return f, val;

end intrinsic;

intrinsic G3QuarticFromHyper(f::RngUPolElt, p::RngIntElt) -> RngMPolElt
    {}

    K := CoefficientRing(f);
    P3 := PolynomialRing(K, 3); x := P3.1; y := P3.2; z := P3.3;

    b0 := Coefficient(f, 0); b1 := Coefficient(f, 1); b2 := Coefficient(f, 2);
    b3 := Coefficient(f, 3); b4 := Coefficient(f, 4); b5 := Coefficient(f, 5);
    b6 := Coefficient(f, 6); b7 := Coefficient(f, 7); b8 := Coefficient(f, 8);

    /* Some arbitrary coefficients */
    a02 := 2; a03 := 3; a04 := 5; a12 := 7; a13 := 11; a22 := 13;

    /* And the others s.t. (y^2-4*x*z)^2 + p*g(x,y,z) is isomorphic to f */
    a00 := b0; a01 := 1/2*b1;
    a10 := b2-4*a02; a11 := -4*a03+1/2*b3;
    a20 := -16*a04+b4-4*a12; a21 := -4*a13+1/2*b5;
    a30 := b6-4*a22; a31 := 1/2*b7; a40 := b8;

    F :=
        (y^2-4*x*z)^2 + p * (
        a00*z^4+a01*y*z^3+a02*y^2*z^2+a03*y^3*z+a04*y^4+a10*x*z^3+a11*x*y*z^2+a12*x*y^2*z+a13*x*y^3+a20*x^2*z^2+a21*x^2*y*z+a22*x^2*y^2+a30*x^3*z+a31*x^3*y+a40*x^4
        );

    return F;

end intrinsic;
