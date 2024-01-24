/* In this file, we verify the claimed equivalence between quartic singularities
   and Dixmier-Ohno relations

   This script assumes that the spec file "g3cayley/magma/spec" is loaded
   at magma startup (in the .magmarc file)
*/


forward A1NFBiSingular, A1p2NFBiSingular, A2NFBiSingular;

/* The field */
Fld := Rationals();

/* Select the subset of tests you wish */
DOInclusions := true; HNFLargeDims := true; HNFSmallDims := true;

/* 0. A small toolbox
 ***/

function NormFormSpecialized(f, fctStratum :
    VNames := ["a00", "a10", "a01", "a02", "a03", "a04", "a11", "a12", "a13", "a20", "a21", "a22", "a30", "a31", "a40"],
        AdditionalConstraints := [],
        TestIrreducibility := true, MagmaWorkaround := true)

    Fa := BaseRing(Parent(f)); AssignNames(~Fa, VNames);
    Pa := RingOfIntegers(Fa); AssignNames(~Pa, VNames);
    Pxyz := Parent(f); AssignNames(~Pxyz, ["x", "y", "z"]);

    DO := ChangeUniverse(DixmierOhnoInvariants(f : degmax := 21) cat [0], Pa);

    //GB := GroebnerBasis(fctStratum(DO));
    RD := RadicalDecomposition(ideal<Pa | fctStratum(DO) cat AdditionalConstraints>);
    [ Basis(rd) : rd in RD ];
    "";

    RES := [**];
    for rd in RD do

        Qa, phi := quo<Pa | rd>; AssignNames(~Qa, VNames);
        FQa := FieldOfFractions(Qa); AssignNames(~FQa, VNames);
        PXYZ := PolynomialRing(FQa, 3); AssignNames(~PXYZ, ["x", "y", "z"]);
        X := PXYZ.1; Y := PXYZ.2; Z := PXYZ.3;
        PHI := hom<Pxyz -> PXYZ | X, Y, Z>;
        Cfs, Mns := CoefficientsAndMonomials(f);
        F := &+[ FQa!phi(Cfs[i])*PHI(Mns[i]) : i in [1..#Cfs]];
        "Looking at", F;

        if Seqset(DixmierOhnoInvariants(F)) eq {0} then
            "\t=> unstable..."; "";
            Append(~RES, "unstable");
            continue;
        end if;

        if TestIrreducibility and not IsIrreducible(F) then
            FCT := Factorization(F);
            "Non irreducible", FCT;
            if #FCT eq 1 and FCT[1, 2] eq 2 then
                "\t=> c^2..."; "";
                Append(~RES, "c^2");
                continue;
            end if;
        end if;

        if MagmaWorkaround  then

            // A workaround to avoid that magma raises an annoying exception
            // while computing a radical decomposition over a multivariate quotient ring
            // (over finite fields)

            xs := Scheme(ProjectiveSpace(Parent(f)),[f]);
            sngs := SingularSubscheme(xs);
            "Dim Ssing", Dimension(sngs);

            PaXYZ := PolynomialRing(CoefficientRing(Pa), Rank(Pa)+3);
            AssignNames(~PaXYZ, ["X", "Y", "Z"] cat Names(Pa));
            X := PaXYZ.1; Y := PaXYZ.2; Z := PaXYZ.3;
            Paphi := hom<Pa -> PaXYZ | [PaXYZ.(i+3) : i in [1..Rank(Pa)]]>;
            PAPHI := hom<Pxyz -> PaXYZ | X,Y,Z>;
            SNGS := [];
            for e in DefiningEquations(sngs) do
                Cfs, Mns := CoefficientsAndMonomials(e);
                E := &+[ Paphi(Cfs[i])*PAPHI(Mns[i]) : i in [1..#Cfs]];
                Append(~SNGS, E);
            end for;

            RDsngs := RadicalDecomposition(ideal<PaXYZ | SNGS cat [Paphi(e) : e in Basis(rd)]>);//RDsngs;

            XS := Scheme(ProjectiveSpace(Parent(F)),[F]);
            Types := [];
            for rdsngs in RDsngs do

                /* We move back rdsngs in FQa... */
                RDSNGS := [];
                for e in Basis(rdsngs) do
                    Cfs, Mns := CoefficientsAndMonomials(e);
                    E := PXYZ!0;
                    for i->mn in Mns do
                        exp := Exponents(mn);
                        E +:= Cfs[i] *
                            &*[ PXYZ.j^exp[j] : j in [1,2,3] ] *
                            &*[ FQa.j^exp[3+j] : j in [1..Rank(FQa)] ];
                    end for;
                    Append(~RDSNGS, E);
                end for;
                RDSNGS := GroebnerBasis(RDSNGS);

                //RDSNGS;
                PTS := [
                    Evaluate(NormalForm(E, RDSNGS), [FQa|1,1,1]) :
                    E in [PXYZ.1,PXYZ.2,PXYZ.3]
                    ];

                if Seqset(PTS) eq {0} or
                    Seqset([ Evaluate(E, PTS) : E in DefiningEquations(XS) ]) ne {0} then continue; end if;

                pts := XS(FQa)!PTS;

                if not IsSingular(pts) then continue; end if;

                //Basis(rdsngs),
                "->", pts;
                boo,F,seq,dat := IsHypersurfaceSingularity(pts,3);
                _, _, typ := NormalFormOfHypersurfaceSingularity(F);
                Append(~Types, typ);
                typ;
            end for;

        else
            /* A more direct way to get these singular points */

            P2 := ProjectiveSpace(Parent(F));
            XS := Scheme(P2,[F]);
            sngs := SingularSubscheme(XS);
            "Dim Ssing", Dimension(sngs);

            Types := [];
            RDsngs := RadicalDecomposition(ideal<PXYZ | DefiningEquations(sngs)>);//RDsngs;
            for rdsngs in RDsngs do
                //rdsngs;
                pts := XS(FQa)![ Evaluate(NormalForm(e, Basis(rdsngs)), [FQa|1,1,1]) : e in [X,Y,Z]];
                //Basis(rdsngs),
                "->", pts;
                boo,F,seq,dat := IsHypersurfaceSingularity(pts,3);
                _, _, typ := NormalFormOfHypersurfaceSingularity(F);
                Append(~Types, typ);
                typ;
            end for;

        end if;                 /* end workaround */

        "\t=> ", {* t : t in Types *};
        "";
        Append(~RES, {* t : t in Types *});

    end for;

    ""; "All the possible types are thus", RES;

    return RES;
end function;


function SpecialNFinSubStratum(f, fctStratum, SubStratum)

    Fa := BaseRing(Parent(f)); Pa := RingOfIntegers(Fa);

    DO := ChangeUniverse(DixmierOhnoInvariants(f : degmax := 21) cat [0], Pa);

    IdRad := Radical(ideal<Pa | fctStratum(DO)>);

    SubEqs := [ NormalForm(E, IdRad) : E in SubStratum(DO) ];

    return Seqset(SubEqs) eq {0};

end function;


function IdAdd(id1, id2)
    return Seqset(RadicalDecomposition(id1 + id2));
end function;


A2Stratum := func<DO | DixmierOhnoSingularityRelations("(A2)", DO)>;
A1p2Stratum := func<DO | DixmierOhnoSingularityRelations("(A1^2)", DO)>;
A1A2Stratum := func<DO | DixmierOhnoSingularityRelations("(A1A2)", DO)>;
A1p3Stratum := func<DO | DixmierOhnoSingularityRelations("(A1^3)", DO)>;
RedA1p3Stratum := func<DO | DixmierOhnoSingularityRelations("(rA1^3)", DO)>;
RedA1p4cubStratum := func<DO | DixmierOhnoSingularityRelations("(rA1^4_cub)", DO)>;
RedA1p4conStratum := func<DO | DixmierOhnoSingularityRelations("(rA1^4_con)", DO)>;
A2p2Stratum := func<DO | DixmierOhnoSingularityRelations("(A2^2)", DO)>;
A1p2A2Stratum := func<DO | DixmierOhnoSingularityRelations("(A1^2A2)", DO)>;
A1A2p2Stratum := func<DO | DixmierOhnoSingularityRelations("(A1A2^2)", DO)>;
RedA1p3A2Stratum := func<DO | DixmierOhnoSingularityRelations("(rA1^3A2)", DO)>;
RedA1p5Stratum := func<DO | DixmierOhnoSingularityRelations("(rA1^5)", DO)>;
A3Stratum := func<DO | DixmierOhnoSingularityRelations("(A3)", DO)>;
RedA1p6Stratum := func<DO | DixmierOhnoSingularityRelations("(rA1^6)", DO)>;
A2p3Stratum := func<DO | DixmierOhnoSingularityRelations("(A2^3)", DO)>;
RedA1A3Stratum := func<DO | DixmierOhnoSingularityRelations("(rA1A3)", DO)>;
A4Stratum := func<DO | DixmierOhnoSingularityRelations("(A4)", DO)>;

UnstableStratum := func<DO | DO>;


function G3SingularProof(Fld :
    DOInclusions := true, HNFLargeDims := true, HNFSmallDims := true);

    DomQ := [ Fld |];

    AllChecked := true;

   /* 1. the DO strata inclusion graph is as awaited?
    ***/


    ""; "";
    "Invariant criterions for quartic singularities checks, in characteristic p =", Characteristic(Fld);
    "---";
    ""; "";



    PR<I27, J21, I21, J18, I18, J15, I15, J12, I12, J09, I09, I06, I03> :=
        PolynomialRing(Fld, [27, 21, 21, 18, 18, 15, 15, 12, 12, 09, 09, 06, 03]);
    I27, J21, I21, J18, I18, J15, I15, J12, I12, J09, I09, I06, I03 := Explode([PR.i : i in [1..13]]);
    DO := [I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27];

    zeroId := ideal<PR | [
        I27, J21, I21, J18, I18, J15, I15, J12, I12, J09, I09, I06, I03 ]>;

    DORels := DixmierOhnoAlgebraicRelations(DO);

    A2Id      := ideal<PR | GroebnerBasis(A2Stratum(DO) cat DORels)>;
    A1p2Id    := ideal<PR | (A1p2Stratum(DO) cat DORels)>;

    A1A2Id    := ideal<PR | GroebnerBasis(A1A2Stratum(DO) cat DORels)>;
    A1p3Id    := ideal<PR | GroebnerBasis(A1p3Stratum(DO) cat DORels)>;
    rA1p3Id   := ideal<PR | GroebnerBasis(RedA1p3Stratum(DO) cat DORels)>;


    rA1p4cubId  := ideal<PR | GroebnerBasis(RedA1p4cubStratum(DO) cat DORels)>;
    rA1p4conId  := ideal<PR | GroebnerBasis(RedA1p4conStratum(DO) cat DORels)>;
    A2p2Id    := ideal<PR | GroebnerBasis(A2p2Stratum(DO) cat DORels)>;
    A1p2A2Id  := ideal<PR | GroebnerBasis(A1p2A2Stratum(DO) cat DORels)>;

    A1A2p2Id  := ideal<PR | GroebnerBasis(A1A2p2Stratum(DO) cat DORels)>;
    rA1p3A2Id := ideal<PR | GroebnerBasis(RedA1p3A2Stratum(DO) cat DORels)>;
    rA1p5Id   := ideal<PR | GroebnerBasis(RedA1p5Stratum(DO) cat DORels)>;
    A3Id      := ideal<PR | GroebnerBasis(A3Stratum(DO) cat DORels)>;

    rA1p6Id   := ideal<PR | GroebnerBasis(RedA1p6Stratum(DO) cat DORels)>;
    A2p3Id    := ideal<PR | GroebnerBasis(A2p3Stratum(DO) cat DORels)>;
    rA1A3Id   := ideal<PR | GroebnerBasis(RedA1A3Stratum(DO) cat DORels)>;
    A4Id      := ideal<PR | GroebnerBasis(A4Stratum(DO) cat DORels)>;

    if not DOInclusions then
        "I skip DO strata inclusions...";
        "";
    else

        "@ DO strata inclusions";
        "@@@@@@@@@@@@@@@@@@@@@@";
        "";

        "Dimension 0 loci";
        "================";
        "";

        "Intersections are as expected?\n";
        ret := IdAdd(A4Id, rA1A3Id) eq {zeroId}; AllChecked and:= ret;
        "\tV(<A4>) meet V(<rA1A3>) = V(<unstable>)\t\t\t:", ret;
        ret := IdAdd(A4Id, A2p3Id) eq {zeroId}; AllChecked and:= ret;
        "\tV(<A4>) meet V(<A2^3>) = V(<unstable>)\t\t\t:", ret;
        ret := IdAdd(A4Id, rA1p6Id) eq {zeroId}; AllChecked and:= ret;
        "\tV(<A4>) meet V(<rA1^6>) = V(<unstable>)\t\t\t:", ret;
        "";
        ret := IdAdd(rA1A3Id, A2p3Id) eq {zeroId}; AllChecked and:= ret;
        "\tV(<rA1A3>) meet V(<A2^3>) = V(<unstable>)\t\t:", ret;
        ret := IdAdd(rA1A3Id, rA1p6Id) eq {zeroId}; AllChecked and:= ret;
        "\tV(<rA1A3>) meet V(<rA1^6>) = V(<unstable>)\t\t:", ret;
        "";
        ret := IdAdd(A2p3Id, rA1p6Id) eq {zeroId}; AllChecked and:= ret;
        "\tV(<A2^3>) meet V(<rA1^6>) = V(<unstable>)\t\t:", ret;
        ""; "";

        "Dimension 1 loci";
        "================";
        "";

        "dim1 -> dim0 inclusions are as expected?\n";

        ret := IdAdd(A3Id, A4Id) eq {A4Id}; AllChecked and:= ret;
        "\tV(<A3>) meet V(<A4>) = V(<A4>)\t\t\t\t:", ret;
        ret := IdAdd(A3Id, rA1A3Id) in { {rA1A3Id}, {zeroId} }; AllChecked and:= ret;
        "\tV(<A3>) meet V(<rA1A3>) = V(<rA1A3>), or V(<unstable>)\t:", ret;
        ret := IdAdd(A3Id, A2p3Id) eq {zeroId}; AllChecked and:= ret;
        "\tV(<A3>) meet V(<A2^3>) = V(<unstable>)\t\t\t:", ret;
        ret := IdAdd(A3Id, rA1p6Id) eq {zeroId}; AllChecked and:= ret;
        "\tV(<A3>) meet V(<rA1^6>) = V(<unstable>)\t\t\t:", ret;
        "";
        ret := IdAdd(A1A2p2Id, A4Id) eq {A4Id}; AllChecked and:= ret;
        "\tV(<A1A2^2>) meet V(<A4>) = V(<A4>)\t\t\t:", ret;
        ret := IdAdd(A1A2p2Id, rA1A3Id) eq {rA1A3Id}; AllChecked and:= ret;
        "\tV(<A1A2^2>) meet V(<rA1A3>) = V(<rA1A3>)\t\t:", ret;
        ret := IdAdd(A1A2p2Id, A2p3Id) eq {A2p3Id}; AllChecked and:= ret;
        "\tV(<A1A2^2>) meet V(<A2^3>) = V(<A2^3>)\t\t\t:", ret;
        ret := IdAdd(A1A2p2Id, rA1p6Id) eq {zeroId}; AllChecked and:= ret;
        "\tV(<A1A2^2>) meet V(<rA1^6>) = V(<unstable>)\t\t:", ret;
        "";
        ret := IdAdd(rA1p3A2Id, A4Id) eq {zeroId}; AllChecked and:= ret;
        "\tV(<rA1^3A2>) meet V(<A4>) = V(<unstable>)\t\t:", ret;
        ret := IdAdd(rA1p3A2Id, rA1A3Id) eq {rA1A3Id}; AllChecked and:= ret;
        "\tV(<rA1^3A2>) meet V(<rA1A3>) = V(<rA1A3>)\t\t:", ret;
        ret := IdAdd(rA1p3A2Id, A2p3Id) eq {zeroId}; AllChecked and:= ret;
        "\tV(<rA1^3A2>) meet V(<A2^3>) = V(<unstable>)\t\t:", ret;
        ret := IdAdd(rA1p3A2Id, rA1p6Id) eq {zeroId}; AllChecked and:= ret;
        "\tV(<rA1^3A2>) meet V(<rA1^6>) = V(<unstable>)\t\t:", ret;
        "";
        ret := IdAdd(rA1p5Id, A4Id) eq {zeroId}; AllChecked and:= ret;
        "\tV(<rA1^5>) meet V(<A4>) = V(<unstable>)\t\t\t:", ret;
        ret := IdAdd(rA1p5Id, rA1A3Id) eq {rA1A3Id}; AllChecked and:= ret;
        "\tV(<rA1^5>) meet V(<rA1A3>) = V(<rA1A3>)\t\t\t:", ret;
        ret := IdAdd(rA1p5Id, A2p3Id) eq {zeroId}; AllChecked and:= ret;
        "\tV(<rA1^5>) meet V(<A2^3>) = V(<unstable>)\t\t:", ret;
        ret := IdAdd(rA1p5Id, rA1p6Id) eq {rA1p6Id}; AllChecked and:= ret;
        "\tV(<rA1^5>) meet V(<rA1^6>) = V(<rA1^6>)\t\t\t:", ret;
        "";

        "Intersections are as expected?\n";
        ret := IdAdd(A3Id, A1A2p2Id) in {{A4Id, rA1A3Id}, {A4Id}} ; AllChecked and:= ret;
        "\tV(<A3>) meet V(<A1A2^2>) = {V(<A4>),V(<rA1A3>)}, or V(<A4>):", ret;
        ret := IdAdd(A3Id, rA1p3A2Id) in {{rA1A3Id}, {zeroId}}; AllChecked and:= ret;
        "\tV(<A3>) meet V(<rA1^3A2>) = V(<rA1A3>), or V(<unstable>):", ret;
        ret := IdAdd(A3Id, rA1p5Id) in {{rA1A3Id}, {zeroId}}; AllChecked and:= ret;
        "\tV(<A3>) meet V(<rA1^5>) = V(<rA1A3>), or V(<unstable>)\t:", ret;
        "";
        ret := IdAdd(A1A2p2Id, rA1p3A2Id) eq {rA1A3Id}; AllChecked and:= ret;
        "\tV(<A1A2^2>) meet V(<rA1^3A2>) = V(<rA1A3>)\t\t:", ret;
        ret := IdAdd(A1A2p2Id, rA1p5Id) eq {rA1A3Id}; AllChecked and:= ret;
        "\tV(<A1A2^2>) meet V(<rA1^5>) = V(<rA1A3>)\t\t:", ret;
        "";
        ret := IdAdd(rA1p3A2Id, rA1p5Id) eq {rA1A3Id}; AllChecked and:= ret;
        "\tV(<rA1^3A2>) meet V(<rA1^5>) = V(<rA1A3>)\t\t:", ret;
        ""; "";

        "Dimension 2 loci";
        "================";
        "";

        "dim2 -> dim1 inclusions are as expected?\n";

        ret := IdAdd(A2p2Id, A3Id) eq {A3Id}; AllChecked and:= ret;
        "\tV(<A2^2>) meet V(<A3>) = V(<A3>)\t\t\t:", ret;
        ret := IdAdd(A2p2Id, A1A2p2Id) eq {A1A2p2Id}; AllChecked and:= ret;
        "\tV(<A2^2>) meet V(<A1A2^2>) = V(<A1A2^2>)\t\t:", ret;
        ret := IdAdd(A2p2Id, rA1p3A2Id) eq {rA1A3Id}; AllChecked and:= ret;
        "\tV(<A2^2>) meet V(<rA1^3A2>) = V(<rA1A3>)\t\t:", ret;
        ret := IdAdd(A2p2Id, rA1p5Id) eq {rA1A3Id}; AllChecked and:= ret;
        "\tV(<A2^2>) meet V(<rA1^5>) = V(<rA1A3>)\t\t\t:", ret;
        "";
        ret := IdAdd(A1p2A2Id, A3Id) eq {A3Id}; AllChecked and:= ret;
        "\tV(<A1^2A2>) meet V(<A3>) = V(<A3>)\t\t\t:", ret;
        ret := IdAdd(A1p2A2Id, A1A2p2Id) eq {A1A2p2Id}; AllChecked and:= ret;
        "\tV(<A1^2A2>) meet V(<A1A2^2>) = V(<A1A2^2>)\t\t:", ret;
        ret := IdAdd(A1p2A2Id, rA1p3A2Id) eq {rA1p3A2Id}; AllChecked and:= ret;
        "\tV(<A1^2A2>) meet V(<rA1^3A2>) = V(<rA1^3A2>)\t\t:", ret;
        ret := IdAdd(A1p2A2Id, rA1p5Id) eq {rA1A3Id}; AllChecked and:= ret;
        "\tV(<A1^2A2>) meet V(<rA1^5>) = V(<rA1A3>)\t\t:", ret;
        "";
        ret := IdAdd(rA1p4conId, A3Id) eq {A3Id}; AllChecked and:= ret;
        "\tV(<rA1^4_con>) meet V(<A3>) = V(<A3>)\t\t\t:", ret;
        ret := IdAdd(rA1p4conId, A1A2p2Id) eq {rA1A3Id, A4Id}; AllChecked and:= ret;
        "\tV(<rA1^4_con>) meet V(<A1A2^2>)={V(<A4>),V(<rA1A3>)}\t:",  ret;
        ret := IdAdd(rA1p4conId, rA1p3A2Id) eq {rA1A3Id}; AllChecked and:= ret;
        "\tV(<rA1^4_con>) meet V(<rA1^3A2>) = V(<rA1A3>)\t\t:", ret;
        ret := IdAdd(rA1p4conId, rA1p5Id) eq {rA1p5Id}; AllChecked and:= ret;
        "\tV(<rA1^4_con>) meet V(<rA1^5>) = V(<rA1^5>)\t\t:", ret;
        "";
        "";
        ret := IdAdd(rA1p4cubId, A3Id) eq {rA1A3Id}; AllChecked and:= ret;
        "\tV(<rA1^4_cub>) meet V(<A3>) = V(<rA1A3>)\t\t:", ret;
        ret := IdAdd(rA1p4cubId, A1A2p2Id) eq {rA1A3Id}; AllChecked and:= ret;
        "\tV(<rA1^4_cub>) meet V(<A1A2^2>) = V(<rA1A3>)\t\t:",  ret;
        ret := IdAdd(rA1p4cubId, rA1p3A2Id) eq {rA1p3A2Id}; AllChecked and:= ret;
        "\tV(<rA1^4_cub>) meet V(<rA1^3A2>) = V(<rA1^3A2>)\t\t:", ret;
        ret := IdAdd(rA1p4cubId, rA1p5Id) eq {rA1p5Id}; AllChecked and:= ret;
        "\tV(<rA1^4_cub>) meet V(<rA1^5>) = V(<rA1^5>)\t\t:", ret;
        "";

        "Intersections are as expected?\n";
        ret := IdAdd(A2p2Id, A1p2A2Id) eq {A1A2p2Id, A3Id}; AllChecked and:= ret;
        "\tV(<A2^2>) meet V(<A1^2A2>)={V(<A1A2^2>),V(<A3>)}\t:", ret;
        ret := IdAdd(A2p2Id, rA1p4conId) eq {A3Id}; AllChecked and:= ret;
        "\tV(<A2^2>) meet V(<rA1^4_con>) = V(<A3>)\t\t\t:", ret;
        ret := IdAdd(A2p2Id, rA1p4cubId) eq {rA1A3Id}; AllChecked and:= ret;
        "\tV(<A2^2>) meet V(<rA1^4_cub>) = V(<rA1A3>)\t\t:", ret;
        "";
        ret := IdAdd(A1p2A2Id, rA1p4conId) eq {A3Id}; AllChecked and:= ret;
        "\tV(<A1^2A2>) meet V(<rA1^4_con>) = V(<A3>)\t\t:", ret;
        ret := IdAdd(A1p2A2Id, rA1p4cubId) eq {rA1p3A2Id}; AllChecked and:= ret;
        "\tV(<A1^2A2>) meet V(<rA1^4_cub>) = V(<rA1^3A2>)\t\t:", ret;
        "";
        ret := IdAdd(rA1p4conId, rA1p4cubId) eq {rA1p5Id}; AllChecked and:= ret;
        "\tV(<rA1^4_con>) meet V(<rA1^4_cub>) = V(<rA1^5>)\t\t:", ret;

        ""; "";

        "Dimension 3 loci";
        "================";
        "";

        "dim3 -> dim2 inclusions are as expected?\n";

        ret := IdAdd(A1A2Id, A2p2Id) eq {A2p2Id}; AllChecked and:= ret;
        "\tV(<A1A2>) meet V(<A2^2>) = V(<A2^2>)\t\t\t:", ret;
        ret := IdAdd(A1A2Id, A1p2A2Id) eq {A1p2A2Id}; AllChecked and:= ret;
        "\tV(<A1A2>) meet V(<A1^2A2>) = V(<A1^2A2>)\t\t:", ret;
        ret := IdAdd(A1A2Id, rA1p4conId) eq {A3Id}; AllChecked and:= ret;
        "\tV(<A1A2>) meet V(<rA1^4_con>) = V(<A3>)\t\t\t:", ret;
        ret := IdAdd(A1A2Id, rA1p4cubId) eq {rA1p3A2Id}; AllChecked and:= ret;
        "\tV(<A1A2>) meet V(<rA1^4_cub>) = V(<rA1^3A2>)\t\t:", ret;
        "";
        ret := IdAdd(A1p3Id, A2p2Id) eq {A1A2p2Id, A3Id}; AllChecked and:= ret;
        "\tV(<A1^3>) meet V(<A2^2>) = {V(<A1A2^2>), V(<A3>)}\t:", ret;
        ret := IdAdd(A1p3Id, A1p2A2Id) eq {A1p2A2Id}; AllChecked and:= ret;
        "\tV(<A1^3>) meet V(<A1^2A2>) = V(<A1^2A2>)\t\t:", ret;
        ret := IdAdd(A1p3Id, rA1p4conId) eq {rA1p4conId}; AllChecked and:= ret;
        "\tV(<A1^3>) meet V(<rA1^4_con>) = V(<rA1^4_con>)\t\t:", ret;
        ret := IdAdd(A1p3Id, rA1p4cubId) eq {rA1p4cubId}; AllChecked and:= ret;
        "\tV(<A1^3>) meet V(<rA1^4_cub>) = V(<rA1^4_cub>)\t\t:", ret;
        "";
        ret := IdAdd(rA1p3Id, A2p2Id) eq {rA1A3Id}; AllChecked and:= ret;
        "\tV(<rA1^3>) meet V(<A2^2>) = V(<A1A3Id>)\t\t\t:", ret;
        ret := IdAdd(rA1p3Id, A1p2A2Id) eq {rA1p3A2Id}; AllChecked and:= ret;
        "\tV(<rA1^3>) meet V(<A1^2A2>) = V(<rA1p3A2>)\t\t:", ret;
        ret := IdAdd(rA1p3Id, rA1p4conId) eq {rA1p5Id}; AllChecked and:= ret;
        "\tV(<rA1^3>) meet V(<rA1^4_con>) = V(<rA1^5>)\t\t:", ret;
        ret := IdAdd(rA1p3Id, rA1p4cubId) eq {rA1p4cubId}; AllChecked and:= ret;
        "\tV(<rA1^3>) meet V(<rA1^4_cub>) = V(<rA1^4_cub>)\t\t:", ret;
        "";

        "Intersections are as expected?\n";
        ret := IdAdd(A1A2Id, A1p3Id) eq {A1p2A2Id}; AllChecked and:= ret;
        "\tV(<A1A2>) meet V(<A1^3>) = V(<A1^2A2>)\t\t\t:", ret;
        ret := IdAdd(A1A2Id, rA1p3Id) eq {rA1p3A2Id}; AllChecked and:= ret;
        "\tV(<A1A2>) meet V(<rA1^3>) = V(<rA1p3A2>)\t\t:", ret;
        "";
        ret := IdAdd(A1p3Id, rA1p3Id) eq {rA1p4cubId}; AllChecked and:= ret;
        "\tV(<A1^3>) meet V(<rA1^3>) = V(<rA1^4_cub>)\t\t:", ret;

        ""; "";

        "Dimension 4 loci";
        "================";
        "";

        "dim4 -> dim3 inclusions are as expected?\n";

        ret := IdAdd(A2Id, A1A2Id)  eq {A1A2Id}; AllChecked and:= ret;
        "\tV(<A2>) meet V(<A1A2>) = V(<A1A2>)\t\t\t:", ret;
        ret := IdAdd(A2Id, A1p3Id)  eq {A1p2A2Id}; AllChecked and:= ret;
        "\tV(<A2>) meet V(<A1^3>) = V(<A1^2A2>)\t\t\t:", ret;
        ret := IdAdd(A2Id, rA1p3Id) eq {rA1p3A2Id}; AllChecked and:= ret;
        "\tV(<A2>) meet V(<rA1^3>) = V(<rA1^3A2>)\t\t\t:",  ret;

        ret := IdAdd(A1p2Id, A1A2Id) eq {A1A2Id}; AllChecked and:= ret;
        "\tV(<A1^2>) meet V(<A1A2>) = V(<A1A2>)\t\t\t:",  ret;
        ret := IdAdd(A1p2Id, A1p3Id) eq {A1p3Id}; AllChecked and:= ret;
        "\tV(<A1^2>) meet V(<A1^3>) = V(<A1^3>)\t\t\t:",  ret;
        ret := IdAdd(A1p2Id, rA1p3Id) eq {rA1p3Id}; AllChecked and:= ret;
        "\tV(<A1^2>) meet V(<rA1^3>) = V(<rA1^3>)\t\t\t:",  ret;
        "";

        "Intersections are as expected?\n";
        ret := IdAdd(A1p2Id, A2Id) eq {A2Id}; AllChecked and:= ret;
        "\tV(<A1^2>) meet V(<A2>) = V(<A2>)\t\t\t:", ret;

        ""; "";

        "Dimension 5 loci";
        "================";
        "";

        "dim5 -> dim4 inclusions are as expected?\n";

        "\tV(<A1>) meet V(<A2>) = V(<A2>)\t\t\t\t:", true; /* obviously */
        "\tV(<A1>) meet V(<A1^2>) = V(<A1^2>)\t\t\t:", true; /* obviously */


        ""; "";

    end if;

    /* 2. The only normal forms with Dixmier-Ohno invariants that satisfy the
      stratum equation have the prescribed types?
    ***/

    HuiNF := AssociativeArray();

    HuiNF["A1"] := HuiNormalForms("(A1)" : Domain := DomQ) ;

    HuiNF["A1^2"] := HuiNormalForms("(A1^2)" : Domain := DomQ) ;
    HuiNF["A2"] := HuiNormalForms("(A2)" : Domain := DomQ) ;

    HuiNF["rA1^3"] := HuiNormalForms("(rA1^3)" : Domain := DomQ) ;
    HuiNF["A1^3"] := HuiNormalForms("(A1^3)" : Domain := DomQ) ;
    HuiNF["A1A2"] := HuiNormalForms("(A1A2)" : Domain := DomQ) ;
    HuiNF["A3"] := HuiNormalForms("(A3)" : Domain := DomQ) ;

    HuiNF["rA1^4_cub"] := HuiNormalForms("(rA1^4_cub)" : Domain := DomQ) ;
    HuiNF["rA1^4_con"] := HuiNormalForms("(rA1^4_con)" : Domain := DomQ) ;
    HuiNF["A1^2A2"] := HuiNormalForms("(A1^2A2)" : Domain := DomQ) ;
    HuiNF["A2^2"] := HuiNormalForms("(A2^2)" : Domain := DomQ) ;
    HuiNF["rA1A3"] := HuiNormalForms("(rA1A3)" : Domain := DomQ) ;
    HuiNF["A1A3"] := HuiNormalForms("(A1A3)" : Domain := DomQ) ;
    HuiNF["A4"] := HuiNormalForms("(A4)" : Domain := DomQ) ;

    HuiNF["rA1^5"] := HuiNormalForms("(rA1^5)" : Domain := DomQ) ;
    HuiNF["rA1^3A2"] := HuiNormalForms("(rA1^3A2)" : Domain := DomQ) ;
    HuiNF["A1A2^2"] := HuiNormalForms("(A1A2^2)" : Domain := DomQ) ;
    HuiNF["rA1^2A3a"] := HuiNormalForms("(rA1^2A3_cub)" : Domain := DomQ) ;
    HuiNF["rA1^2A3b"] := HuiNormalForms("(rA1^2A3_con)" : Domain := DomQ) ;
    HuiNF["rA3^2"] := HuiNormalForms("(rA3^2)" : Domain := DomQ) ;
    HuiNF["A2A3"] := HuiNormalForms("(A2A3)" : Domain := DomQ) ;
    HuiNF["A1A4"] := HuiNormalForms("(A1A4)" : Domain := DomQ) ;
    HuiNF["A5"] := HuiNormalForms("(A5)" : Domain := DomQ) ;

    HuiNF["rA1^6"] := HuiNormalForms("(rA1^6)" : Domain := DomQ) ;
    HuiNF["A2^3"] := HuiNormalForms("(A2^3)" : Domain := DomQ) ;
    HuiNF["rA1^3A3"] := HuiNormalForms("(rA1^3A3)" : Domain := DomQ) ;
    HuiNF["rA1A3^2"] := HuiNormalForms("(rA1A3^2)" : Domain := DomQ) ;
    HuiNF["rA1A2A3"] := HuiNormalForms("(rA1A2A3)" : Domain := DomQ) ;
    HuiNF["rA1A5"] := HuiNormalForms("(rA1A5_con)" : Domain := DomQ) ;
    HuiNF["rA7"] := HuiNormalForms("(rA7)" : Domain := DomQ) ;
    HuiNF["c^2"] := HuiNormalForms("(c^2)" : Domain := DomQ) ;
    HuiNF["A2A4"] := HuiNormalForms("(A2A4)" : Domain := DomQ) ;
    HuiNF["A6"] := HuiNormalForms("(A6)" : Domain := DomQ) ;

    if not HNFLargeDims then
        "I skip specializations for A1, A1^2 & A2...";
        "";
    else

        "@ Specializing A1, A1^2 & A2 normal forms yields one more singularity";
        "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
        "";

        "Stratum A1^2";
        "============";
        "";

        "A1^2 normal forms are in V(<A1^2>)\t:", Seqset(DixmierOhnoSingularityRelations("(A1^2)", DixmierOhnoInvariants(HuiNF["A1^2"]))) eq {0};
        ""; "";

        Pa<a00, a01, a10, a11> := PolynomialRing(Fld, [1, 1, 1, 1]);
        PXYZ<X,Y,Z> := PolynomialRing(Pa, 3);
        f := a00*Z^4+(X*a10+Y*a01)*Z^3+(X*Y*a11+X^2+Y^2)*Z^2+X^2*Y^2;

        DO := DixmierOhnoInvariants(f : degmax := 21) cat [0];
        a1p2inv := A1p2NFBiSingular(a00, a01, a10, a11);

        for locus in [ "(A4)", "(rA1A3)", "(A2^3)", "(rA1^6)", "(A3)", "(A1A2^2)", "(rA1^3A2)", "(rA1^5)", "(A2^2)", "(A1^2A2)", "(rA1^4_con)", "(rA1^4_cub)", "(A1A2)", "(A1^3)", "(rA1^3)" ] do

            printf "A1^2 normal forms in V(<%o>) have one more singularity?\n", locus;
            "--------------------";
            tt := Cputime(); GB := GroebnerBasis(DixmierOhnoSingularityRelations(locus, DO)); tt := Cputime(tt);
            ret := NormalForm(a1p2inv, GB) eq 0; AllChecked and:= ret;
            "It turns out that it is", ret;
            printf "\t\t\t(checked in %.2os)\n", tt;
            "";

        end for;
        "";

        "Stratum A2";
        "==========";
        "";

        "A2 normal forms are in V(<A2>)\t\t:", Seqset(DixmierOhnoSingularityRelations("(A2)", DixmierOhnoInvariants(HuiNF["A2"]))) eq {0};
        ""; "";

        Pa<a02, a03, a11, a12> := PolynomialRing(Fld, [1, 1, 1, 1]);
        PXYZ<X,Y,Z> := PolynomialRing(Pa, 3);
        f := X^2*Z^2 + X*Y^3 + a12*X*Y^2*Z + a11*X*Y*Z^2 + a03*Y^3*Z + a02*Y^2*Z^2 + Y*Z^3;
        DO := DixmierOhnoInvariants(f : degmax := 21) cat [0];
        a2inv := A2NFBiSingular(a02, a03, a11, a12);

        for locus in [ "(A4)", "(rA1A3)", "(A2^3)", "(A3)", "(A1A2^2)", "(rA1^3A2)", "(A2^2)", "(A1^2A2)", "(A1A2)" ] do

            printf "A2 normal forms in V(<%o>) have one more singularity?\n", locus;
            "--------------------";
            tt := Cputime(); GB := GroebnerBasis(DixmierOhnoSingularityRelations(locus, DO)); tt := Cputime(tt);
            ret := NormalForm(a2inv, GB) eq 0; AllChecked and:= ret;
            "It turns out that it is", ret;
            printf "\t\t\t(checked in %.2os)\n", tt;
            "";

        end for;
        "";


        "Stratum A1";
        "==========";
        "";

        "A1 normal forms are in V(<A1>)\t\t:", DixmierOhnoInvariants(HuiNF["A1"])[13] eq 0;
        ""; "";
        //SetVerbose("Groebner", 1);

        Pa<a03, a04, a12, a13, a02> := PolynomialRing(Fld, [1, 1, 1, 1, 1]);
        PXYZ<X,Y,Z> := PolynomialRing(Pa, 3);
        f := Y*Z^3+(Y^2*a02+X^2)*Z^2+(X*Y^2*a12+Y^3*a03+X^2*Y)*Z+a13*X*Y^3+a04*Y^4;
        DO := DixmierOhnoInvariants(f : degmax := 21) cat [0];
        a1inv := A1NFBiSingular(a03, a04, a12, a13, a02);

        for locus in [ "(A4)", "(rA1A3)", "(A2^3)", "(rA1^6)", "(A3)", "(A1A2^2)", "(rA1^3A2)", "(rA1^5)", "(A2^2)", "(A1^2A2)", "(rA1^4_con)", "(rA1^4_cub)", "(A1A2)", "(A1^3)", "(rA1^3)", "(A2)", "(A1^2)" ] do

            printf "A1 normal forms in V(<%o>) have one more singularity?\n", locus;
            "--------------------";
            tt := Cputime(); GB := GroebnerBasis(DixmierOhnoSingularityRelations(locus, DO)); tt := Cputime(tt);
            ret := NormalForm(a1inv, GB) eq 0; AllChecked and:= ret;
            "It turns out that it is", ret;
            printf "\t\t\t(checked in %.2os)\n", tt;
            "";

        end for;
        "";

    end if;


    if not HNFSmallDims then
        "I skip specializations for the small strata...";
        "";
    else

        "@ Specializations of the other normal forms yields the awaited types";
        "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
        "";

        "Stratum A4";
        "==========";
        "";

        ret := Seqset(DixmierOhnoSingularityRelations("(A4)", DixmierOhnoInvariants(HuiNF["A4"]))) eq {0}; AllChecked and:= ret;
        "A4 normal forms are in V(<A4>)\t\t:", ret;
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(A4)", DixmierOhnoInvariants(HuiNF["A1A4"]))) eq {0}; AllChecked and:= ret;
        "A1A4 normal forms are in V(<A4>)\t:", ret;
        ret := Seqset(DixmierOhnoSingularityRelations("(A4)", DixmierOhnoInvariants(HuiNF["A5"]))) eq {0}; AllChecked and:= ret;
        "A5 normal forms are in V(<A4>)\t\t:", ret;
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(A4)", DixmierOhnoInvariants(HuiNF["rA1A5"]))) eq {0}; AllChecked and:= ret;
        "rA1A5 normal forms are in V(<A4>)\t:", ret;
        ret := Seqset(DixmierOhnoSingularityRelations("(A4)", DixmierOhnoInvariants(HuiNF["rA7"]))) eq {0}; AllChecked and:= ret;
        "rA7 normal forms are in V(<A4>)\t\t:", ret;
        ret := Seqset(DixmierOhnoSingularityRelations("(A4)", DixmierOhnoInvariants(HuiNF["c^2"]))) eq {0}; AllChecked and:= ret;
        "c^2 normal forms are in V(<A4>)\t\t:", ret;
        ret := Seqset(DixmierOhnoSingularityRelations("(A4)", DixmierOhnoInvariants(HuiNF["A2A4"]))) eq {0}; AllChecked and:= ret;
        "A2A4 normal forms are in V(<A4>)\t:", ret;
        ret := Seqset(DixmierOhnoSingularityRelations("(A4)", DixmierOhnoInvariants(HuiNF["A6"]))) eq {0}; AllChecked and:= ret;
        "A6 normal forms are in V(<A4>)\t\t:", ret;
        ""; "";


        "Dimension 1 -> A4";
        "*****************";
        "";

        "A2A3 normal forms in V(<A4>) have at least an A4 singularity?";
        "-------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A2A3)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A4Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in { {* "A2", "A4" *} }) or
            (Type(T) eq MonStgElt and T in { "unstable" } ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A2A4  */


        "rA3^2 normal forms in V(<A4>) have at least an A4 singularity?";
        "--------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA3^2)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A4Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {}) or
            (Type(T) eq MonStgElt and T in {"c^2", "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, c^2  */

        "rA1^2A3b normal forms in V(<A4>) have at least an A4 singularity?";
        "-----------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^2A3_con)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A4Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {}) or
            (Type(T) eq MonStgElt and T in {"c^2", "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, c^2  */


        "A1A2^2 normal forms in V(<A4>) have at least an A4 singularity?";
        "---------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1A2^2)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A4Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {}) or
            (Type(T) eq MonStgElt and T in {"c^2", "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, c^2  */


        "Dimension 2 -> A4";
        "*****************";
        "";

        "A1A3 normal forms in V(<A4>) have at least an A4 singularity?";
        "-------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1A3)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A4Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in { {* "A1", "A4" *} }) or
            (Type(T) eq MonStgElt and T in { "unstable" } ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A1A4  */

        "A2^2 normal forms in V(<A4>) have at least an A4 singularity?";
        "-------------------------------------------------------------";
        "";

        f  := HuiNormalForms("(A2^2)" : Domain := DomQ);
        //Tp := NormFormSpecialized(f, A4Stratum);"";
        Tp := SpecialNFinSubStratum(f, A4Stratum, UnstableStratum); AllChecked and:= Tp;
        "=> Unstable:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => unstable */

        "A1^2A2 normal forms in V(<A4>) have at least an A4 singularity?";
        "---------------------------------------------------------------";
        "";

        f  := HuiNormalForms("(A1^2A2)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A4Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {}) or
            (Type(T) eq MonStgElt and T in {"c^2", "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, c^2 */

        "rA1^4_con normal forms in V(<A4>) have at least an A4 singularity?";
        "---------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^4_con)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A4Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {}) or
            (Type(T) eq MonStgElt and T in {"c^2", "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, c^2 */


        "Dimension 3 -> A4";
        "*****************";
        "";

        "A3 normal forms in V(<A4>) have at least an A4 singularity?";
        "-----------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A3)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A4Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in { {* "A4" *} } ) or
            (Type(T) eq MonStgElt and T in {"unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A4 */

        "A1A2 normal forms in V(<A4>) have at least an A4 singularity?";
        "-------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1A2)" : Domain := DomQ);
        //Tp := NormFormSpecialized(f, A4Stratum);
        Tp := SpecialNFinSubStratum(f, A4Stratum, UnstableStratum); AllChecked and:= Tp;
        "Unstable:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => unstable */

        "A1^3 normal forms in V(<A4>) have at least an A4 singularity?";
        "-------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^3)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A4Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {} ) or
            (Type(T) eq MonStgElt and T in { "c^2", "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, c^2 */

        "";


        "Stratum rA1A3";
        "=============";
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(rA1A3)", DixmierOhnoInvariants(HuiNF["rA1A3"]))) eq {0}; AllChecked and:= ret;
        "rA1A3 normal forms are in V(<rA1A3>)\t:", ret;
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(rA1A3)", DixmierOhnoInvariants(HuiNF["rA1^2A3a"]))) eq {0}; AllChecked and:= ret;
        "rA1^2A3a: normal forms are in V(<rA1A3>)\t:", ret;
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(rA1A3)", DixmierOhnoInvariants(HuiNF["rA1^3A3"]))) eq {0}; AllChecked and:= ret;
        "rA1^3A3 normal forms are in V(<rA1A3>)\t:", ret;
        ret := Seqset(DixmierOhnoSingularityRelations("(rA1A3)", DixmierOhnoInvariants(HuiNF["rA1A3^2"]))) eq {0}; AllChecked and:= ret;
        "rA1A3^2 normal forms are in V(<rA1A3>)\t:", ret;
        ret := Seqset(DixmierOhnoSingularityRelations("(rA1A3)", DixmierOhnoInvariants(HuiNF["rA1A2A3"]))) eq {0}; AllChecked and:= ret;
        "rA1A2A3 normal forms are in V(<rA1A3>)\t:", ret;
        ""; "";

        "Dimension 1 -> rA1A3";
        "********************";
        "";

        "A2A3 normal forms in V(<rA1A3>) have at least A1A3 singularities?";
        "-----------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A2A3)" : Domain := DomQ);
        //Tp := NormFormSpecialized(f, RedA1A3Stratum);
        Tp := SpecialNFinSubStratum(f, RedA1A3Stratum, UnstableStratum); AllChecked and:= Tp;
        "Unstable:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => unstable */

        "rA3^2 normal forms in V(<rA1A3>) have at least A1A3 singularities?";
        "------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA3^2)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1A3Stratum);
        "";
        /* OK => unstable, rA1A3^2 */

        "rA1^2A3b normal forms in V(<rA1A3>) have at least A1A3 singularities?";
        "---------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^2A3_con)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1A3Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^3, "A3" *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, rA1^3A3 */

        "A1A2^2 normal forms in V(<rA1A3>) have at least A1A3 singularities?";
        "-------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1A2^2)" : Domain := DomQ);
        //Tp := NormFormSpecialized(f, RedA1A3Stratum);
        Tp := SpecialNFinSubStratum(f, RedA1A3Stratum, UnstableStratum); AllChecked and:= Tp;
        "Unstable:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => unstable */

        "rA1^3A2 normal forms in V(<rA1A3>) have at least A1A3 singularities?";
        "--------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^3A2)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1A3Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1", "A2", "A3" *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, rA1A2A3 */

        "rA1^5 normal forms in V(<rA1A3>) have at least A1A3 singularities?";
        "------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^5)" : Domain := DomQ);
        Tp := SpecialNFinSubStratum(f, RedA1A3Stratum, UnstableStratum); AllChecked and:= Tp;
        "Unstable:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => unstable */


        "Dimension 2 -> rA1A3";
        "********************";
        "";

        "A1A3 normal forms in V(<rA1A3>) have at least A1A3 singularities?";
        "-----------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1A3)" : Domain := DomQ);
        Tp := SpecialNFinSubStratum(f, RedA1A3Stratum, UnstableStratum); AllChecked and:= Tp;
        "Unstable:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => unstable */
        "";

        "A2^2 normal forms in V(<rA1A3>) have at least A1A3 singularities?";
        "-----------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A2^2)" : Domain := DomQ);
        //Tp := NormFormSpecialized(f, RedA1A3Stratum);
        Tp := SpecialNFinSubStratum(f, RedA1A3Stratum, UnstableStratum); AllChecked and:= Tp;
        "Unstable:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => unstable */

        "A1^2A2 normal forms in V(<rA1A3>) have at least A1A3 singularities?";
        "-------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^2A2)" : Domain := DomQ);
        "Unstable:\t", SpecialNFinSubStratum(f, RedA1A3Stratum, UnstableStratum); AllChecked and:= Tp;
        //Tp := NormFormSpecialized(f, RedA1A3Stratum);
        "";
        /* OK => unstable */

        "rA1^4_con normal forms in V(<rA1A3>) have at least A1A3 singularities?";
        "-------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^4_con)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1A3Stratum);
        "";
        /* OK => unstable, rA1^3A3 */

        "rA1^4_cub normal forms in V(<rA1A3>) have at least A1A3 singularities?";
        "-------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^4_cub)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1A3Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^3, "A3" *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A1^3A3 */


        "Dimension 3 -> rA1A3";
        "********************";
        "";

        "A1A2 normal forms in V(<rA1A3>) have at least A1A3 singularities?";
        "-----------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1A2)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1A3Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1", "A2", "A3" *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A1A2A3 */

        "A1^3 normal forms in V(<rA1A3>) have at least A1A3 singularities?";
        "-----------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^3)" : Domain := DomQ);
        //Tp := NormFormSpecialized(f, RedA1A3Stratum);
        Tp := SpecialNFinSubStratum(f, RedA1A3Stratum, UnstableStratum); AllChecked and:= Tp;
        "Unstable:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => unstable */

        "rA1^3 normal forms in V(<rA1A3>) have at least A1A3 singularities?";
        "------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^3)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1A3Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^3, "A3" *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A1^3A3 */

        "";


        "Stratum A2^3";
        "============";
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(A2^3)", DixmierOhnoInvariants(HuiNF["A2^3"]))) eq {0}; AllChecked and:= ret;
        "A2^3 normal forms are in V(<A2^3>)\t:", ret;
        ""; "";

        "Dimension 1 -> A2^3";
        "*******************";
        "";

        "A1A2^2 normal forms in V(<A2^3>) have at least an A2^3 singularity?";
        "-------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1A2^2)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A2p3Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A2"^^3 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A2^3 */


        "Dimension 2 -> A2^3";
        "*******************";
        "";

        "A2^2 normal forms in V(<A2^3>) have at least an A2^3 singularity?";
        "-----------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A2^2)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A2p3Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A2"^^3 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A2^3 */

        "A1^2A2 normal forms in V(<A2^3>) have at least an A2^3 singularity?";
        "-------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^2A2)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A2p3Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A2"^^3 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A2^3 */


        "Dimension 3 -> A2^3";
        "*******************";
        "";

        "A1A2 normal forms in V(<A2^3>) have at least an A2^3 singularity?";
        "-----------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1A2)" : Domain := DomQ);
        //Tp := NormFormSpecialized(f, A2p3Stratum);
        Tp := SpecialNFinSubStratum(f, A2p3Stratum, UnstableStratum); AllChecked and:= Tp;
        "Unstable:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";

        /* OK => unstable */

        "A1^3 normal forms in V(<A2^3>) have at least an A2^3 singularity?";
        "-----------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^3)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A2p3Stratum);f  := HuiNormalForms("(A1^2A2)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A2p3Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A2"^^3 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A2^3 */

        "";


        "Stratum rA1^6";
        "=============";
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(rA1^6)", DixmierOhnoInvariants(HuiNF["rA1^6"]))) eq {0}; AllChecked and:= ret;
        "rA1^6 normal forms are in V(<rA1^6>)\t:", ret;
        ""; "";

        "Dimension 1 -> rA1^6";
        "********************";
        "";

        "rA1^5 normal forms in V(<rA1^6>) have at least an A1^6 singularity?";
        "-------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^5)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1p6Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^6 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A1^6 */


        "Dimension 2 -> rA1^6";
        "********************";
        "";

        "A1^4b normal forms in V(<rA1^6>) have at least an A1^6 singularity?";
        "-------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^4_con)" : Domain := DomQ);
        //Tp := NormFormSpecialized(f, RedA1p6Stratum);
        Tp := SpecialNFinSubStratum(f, RedA1p6Stratum, UnstableStratum); AllChecked and:= Tp;
        "Unstable:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => unstable */

        "A1^4a normal forms in V(<rA1^6>) have at least an A1^6 singularity?";
        "-------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^4_cub)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1p6Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^6 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A1^6 */


        "Dimension 3 -> rA1^6";
        "********************";
        "";

        "A1^3 normal forms in V(<rA1^6>) have at least an A1^6 singularity?";
        "------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^3)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1p6Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^6 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => A1^6 */

        "rA1^3 normal forms in V(<rA1^6>) have at least an A1^6 singularity?";
        "-------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^3)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1p6Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^6 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A1^6 */

        "";


        "Stratum A3";
        "==========";
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(A3)", DixmierOhnoInvariants(HuiNF["A3"]))) eq {0}; AllChecked and:= ret;
        "A3 normal forms are in V(<A3>)\t\t:", ret;
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(A3)", DixmierOhnoInvariants(HuiNF["A1A3"]))) eq {0}; AllChecked and:= ret;
        "A1A3 normal forms are in V(<A3>)\t:", ret;
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(A3)", DixmierOhnoInvariants(HuiNF["rA1^2A3b"]))) eq {0}; AllChecked and:= ret;
        "rA1^2A3b: normal forms are in V(<A3>)\t:", ret;
        ret := Seqset(DixmierOhnoSingularityRelations("(A3)", DixmierOhnoInvariants(HuiNF["rA3^2"]))) eq {0}; AllChecked and:= ret;
        "rA3^2 normal forms are in V(<A3>)\t:", ret;
        ret := Seqset(DixmierOhnoSingularityRelations("(A3)", DixmierOhnoInvariants(HuiNF["A2A3"]))) eq {0}; AllChecked and:= ret;
        "A2A3 normal forms are in V(<A3>)\t:", ret;
        ""; "";

        "Dimension 2 -> A3";
        "*****************";
        "";

        "A2^2 normal forms in V(<A3>) have at least an A3 singularity?";
        "-------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A2^2)" : Domain := DomQ);
        //Tp := NormFormSpecialized(f, A3Stratum);
        Tp := SpecialNFinSubStratum(f, A3Stratum, UnstableStratum); AllChecked and:= Tp;
        "Unstable:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => unstable */

        "A1^2A2 normal forms in V(<A3>) have at least an A3 singularity?";
        "---------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^2A2)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A3Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^2, "A3" *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A1^2A3 */

        "rA1^4_con normal forms in V(<A3>) have at least an A3 singularity?";
        "---------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^4_con)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A3Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^2, "A3" *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A1^2A3 */


        "Dimension 3 -> A3";
        "*****************";
        "";

        "A1A2 normal forms in V(<A3>) have at least an A3 singularity?";
        "-------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1A2)" : Domain := DomQ);
        //Tp := NormFormSpecialized(f, A3Stratum);
        Tp := SpecialNFinSubStratum(f, A3Stratum, RedA1A3Stratum); AllChecked and:= Tp;
        "rA1A3:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => unstable, A1A2A3 */

        "A1^3 normal forms in V(<A3>) have at least an A3 singularity?";
        "-------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^3)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A3Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^2, "A3" *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A1^2A3 */

        "";


        "Stratum A1A2^2";
        "==============";
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(A1A2^2)", DixmierOhnoInvariants(HuiNF["A1A2^2"]))) eq {0}; AllChecked and:= ret;
        "A1A2^2 normal forms are in V(<A1A2^2>)\t:", ret;
        ""; "";

        "Dimension 2 -> A1A2^2";
        "*********************";
        "";

        "A2^2 normal forms in V(<A1A2^2>) have at least an A1A2^2 singularity?";
        "---------------------------------------------------------------------";
        "";
        Pa<a00, a11> := FunctionField(Fld, 2);
        Pxyz<X,Y,Z> := PolynomialRing(Pa, 3);
        f := a00*Z^4+(X+Y)*Z^3+a11*X*Y*Z^2+X^2*Y^2;
        Tp := NormFormSpecialized(f, A1A2p2Stratum : VNames := ["a00", "a11"], TestIrreducibility := false);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1", "A2"^^2 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => A1A2^2 */

        "A1^2A2 normal forms in V(<A1A2^2>) have at least an A1A2^2 singularity?";
        "-----------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^2A2)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A1A2p2Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1", "A2"^^2 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A1A2^2 */


        "Dimension 3 -> A1A2^2";
        "*********************";
        "";

        "A1A2 normal forms in V(<A1A2^2>) have at least an A1A2^2 singularity?";
        "---------------------------------------------------------------------";
        "";
        Pa<a11, a00, a01> := FunctionField(Fld, 3); /* Take care of the variable order
                                                                 (too slow otherwise) */
        Pxyz<X,Y,Z> := PolynomialRing(Pa, 3);
        f := a00*Z^4+(X+Y*a01)*Z^3+(X*Y*a11+Y^2)*Z^2+X^2*Y^2;
        Tp := NormFormSpecialized(f, A1A2p2Stratum : VNames := [ "a11", "a00", "a01" ]);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1", "A2"^^2 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => A1A2^2 */

        "A1^3 normal forms in V(<A1A2^2>) have at least an A1A2^2 singularity?";
        "---------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^3)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A1A2p2Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1", "A2"^^2 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A1A2^2 */

        "";


        "Stratum rA1^3A2";
        "===============";
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(rA1^3A2)", DixmierOhnoInvariants(HuiNF["rA1^3A2"]))) eq {0}; AllChecked and:= ret;
        "rA1^3A2 normal forms are in V(<rA1^3A2>):", ret;
        ""; "";

        "Dimension 2 -> rA1^3A2";
        "**********************";
        "";


        "A1^2A2 normal forms in V(<rA1^3A2>) have at least an rA1^3A2 singularity?";
        "-------------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^2A2)" : Domain := DomQ);
        //Tp := NormFormSpecialized(f, RedA1p3A2Stratum);
        Tp := SpecialNFinSubStratum(f, RedA1p3A2Stratum, UnstableStratum); AllChecked and:= Tp;
        "Unstable:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => unstable */

        "rA1^4_cub normal forms in V(<rA1^3A2>) have at least an rA1^3A2 singularity?";
        "-------------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^4_cub)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1p3A2Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^3, "A2" *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A1^3A2 */


        "Dimension 3 -> rA1^3A2";
        "**********************";
        "";

        "A1A2 normal forms in V(<rA1^3A2>) have at least an rA1^3A2 singularity?";
        "-----------------------------------------------------------------------";
        "";
        Fa<a11, a00, a01, i> := FunctionField(Fld, 4);
        Pxyz<X,Y,Z> := PolynomialRing(Fa, 3);
        f := a00*Z^4+(X+Y*a01)*Z^3+(X*Y*a11+Y^2)*Z^2+X^2*Y^2;
        Tp := NormFormSpecialized(f, RedA1p3A2Stratum :
            VNames := ["a11", "a00", "a01", "i"],
            AdditionalConstraints := [Numerator(-2*a00*i^2-a00*a01*i+1)]);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^3, "A2" *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => A1^3A2 */

        "A1^3 normal forms in V(<rA1^3A2>) have at least an rA1^3A2 singularity?";
        "-----------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^3)" : Domain := DomQ);
        //Tp := NormFormSpecialized(f, RedA1p3A2Stratum);
        Tp :=  SpecialNFinSubStratum(f, RedA1p3A2Stratum, UnstableStratum); AllChecked and:= Tp;
        "Unstable:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => unstable */

        "";


        "Stratum rA1^5";
        "=============";
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(rA1^5)", DixmierOhnoInvariants(HuiNF["rA1^5"]))) eq {0}; AllChecked and:= ret;
        "rA1^5 normal forms are in V(<rA1^5>)\t:", ret;
        ""; "";

        "Dimension 2 -> rA1^5";
        "********************";
        "";

        "rA1^4_con normal forms in V(<rA1^5>) have at least an rA1^5 singularity?";
        "---------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^4_con)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1p5Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^5 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => A1^5 */

        "rA1^4_cub normal forms in V(<rA1^5>) have at least an rA1^5 singularity?";
        "---------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(rA1^4_cub)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1p5Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^5 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => unstable, A1^5 */


        "Dimension 3 -> rA1^5";
        "********************";
        "";

        "A1^3 normal forms in V(<rA1^5>) have at least an rA1^5 singularity?";
        "-------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^3)" : Domain := DomQ);
        //Tp := NormFormSpecialized(f, RedA1p5Stratum);
        Tp := SpecialNFinSubStratum(f, RedA1p3A2Stratum, RedA1p6Stratum); AllChecked and:= Tp;
        "rA1^6:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => A1^6 */

        "rA1^3 normal forms in V(<rA1^5>) have at least an rA1^5 singularity?";
        "--------------------------------------------------------------------";
        "";
        Fa<a20, a21, a30, i> := FunctionField(Fld, 4);
        Pxyz<X,Y,Z> := PolynomialRing(Fa, 3);
        f := (X^2*a20+X*Y)*Z^2+(X^3*a30+X^2*Y*a21+X*Y^2)*Z+X^2*Y^2;
        Tp := NormFormSpecialized(f, RedA1p5Stratum :
            VNames := ["a20", "a01", "a30", "i"],
            AdditionalConstraints := [Numerator(i^2 + i - a30)]);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^5 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => A1^5 */

        "";


        "Stratum A2^2";
        "============";
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(A2^2)", DixmierOhnoInvariants(HuiNF["A2^2"]))) eq {0}; AllChecked and:= ret;
        "A2^2 normal forms are in V(<A2^2>)\t:", ret;
        ""; "";

        "Dimension 3 -> A2^2";
        "*******************";
        "";

        "A1A2 normal forms in V(<A2^2>) have at least an A2^2 singularity?";
        "-----------------------------------------------------------------";
        "";
        Pa<a11, a00, a01> := FunctionField(Fld, 3);
        Pxyz<X,Y,Z> := PolynomialRing(Pa, 3);
        f := a00*Z^4+(X+Y*a01)*Z^3+(X*Y*a11+Y^2)*Z^2+X^2*Y^2;
        //Tp := NormFormSpecialized(f, A2p2Stratum : VNames := [ "a11", "a00", "a01" ]);
        Tp := SpecialNFinSubStratum(f, A2p2Stratum, A1A2p2Stratum); AllChecked and:= Tp;
        "A1A2^2:\t", Tp;
        "";
        "Singularities are as expected\t\t:", Tp;
        "";
        /* OK => A1A2^2 */

        "";


        "Stratum A1^2A2";
        "==============";
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(A1^2A2)", DixmierOhnoInvariants(HuiNF["A1^2A2"]))) eq {0}; AllChecked and:= ret;
        "A1^2A2 normal forms are in V(<A1^2A2>)\t:", ret;
        ""; "";

        "Dimension 3 -> A1^2A2";
        "*********************";
        "";

        "A1A2 normal forms in V(<A1^2A2>) have at least an A1^2A2 singularity?";
        "---------------------------------------------------------------------";
        "";
        Pa<a11, a00, a01> := FunctionField(Fld, 3);
        Pxyz<X,Y,Z> := PolynomialRing(Pa, 3);
        f := a00*Z^4+(X+Y*a01)*Z^3+(X*Y*a11+Y^2)*Z^2+X^2*Y^2;
        Tp := NormFormSpecialized(f, A1p2A2Stratum : VNames := [ "a11", "a00", "a01" ]);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^2, "A2" *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => A1^2A2 */

        "A1^3 normal forms in V(<A1^2A2>) have at least an A1^2A2 singularity?";
        "---------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^3)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, A1p2A2Stratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^2, "A2" *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";
        /* OK => A1^2A2 */

        "";


        "Stratum rA1^4_con";
        "==============";
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(rA1^4_con)", DixmierOhnoInvariants(HuiNF["rA1^4_con"]))) eq {0}; AllChecked and:= ret;
        "rA1^4_con normal forms are in V(<rA1^4_con>)\t:", ret;
        ""; "";

        "Dimension 3 -> rA1^4_con";
        "*********************";
        "";

        "A1^3 normal forms in V(<rA1^4_con>) have at least an rA1^4_con singularity?";
        "---------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^3)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1p4conStratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^4 *}, {* "A1"^^6 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";


        "Stratum rA1^4_cub";
        "==============";
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(rA1^4_cub)", DixmierOhnoInvariants(HuiNF["rA1^4_cub"]))) eq {0}; AllChecked and:= ret;
        "rA1^4_cub normal forms are in V(<rA1^4_cub>)\t:", ret;
        ""; "";

        "Dimension 3 -> rA1^4_cub";
        "*********************";
        "";

        "A1^3 normal forms in V(<rA1^4_cub>) have at least an rA1^4_cub singularity?";
        "---------------------------------------------------------------------";
        "";
        f  := HuiNormalForms("(A1^3)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1p4cubStratum);
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^6 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";

        "rA1^3 normal forms in V(<rA1^4_cub>) have at least an rA1^4_cub singularity?";
        "----------------------------------------------------------------------";
        "";
        Fa<a20, a21, a30> := FunctionField(Fld, 3);
        Pxyz<X,Y,Z> := PolynomialRing(Fa, 3);
        f := (X^2*a20+X*Y)*Z^2+(X^3*a30+X^2*Y*a21+X*Y^2)*Z+X^2*Y^2;
        // f  := HuiNormalForms("(rA1^3)" : Domain := DomQ);
        Tp := NormFormSpecialized(f, RedA1p4cubStratum : VNames := ["a20", "a21", "a30"] );
        "";
        ret := &and[ (Type(T) eq SetMulti and T in {{* "A1"^^4 *}} ) or
            (Type(T) eq MonStgElt and T in { "unstable"} ) : T in Tp];
        AllChecked and:= ret;
        "Singularities are as expected\t\t:", ret;
        "";


        "Stratum A1A2";
        "============";
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(A1A2)", DixmierOhnoInvariants(HuiNF["A1A2"]))) eq {0}; AllChecked and:= ret;
        "A1A2 normal forms are in V(<A1A2>)\t:", ret;
        ""; "";

        "Nothing more has to be checked :-)";
        "";

        "";


        "Stratum A1^3";
        "============";
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(A1^3)", DixmierOhnoInvariants(HuiNF["A1^3"]))) eq {0}; AllChecked and:= ret;
        "A1^3 normal forms are in V(<A1^3>)\t:", ret;
        ""; "";

        "Nothing more has to be checked :-)";
        "";

        "";


        "Stratum rA1^3";
        "=============";
        "";
        ret := Seqset(DixmierOhnoSingularityRelations("(rA1^3)", DixmierOhnoInvariants(HuiNF["rA1^3"]))) eq {0}; AllChecked and:= ret;
        "rA1^3 normal forms are in V(<rA1^3>)\t:", ret;
        ""; "";

    end if;

    "Nothing more has to be checked :-)";
    "";

    return AllChecked;

end function;

/*
  f := Y*Z^3+(Y^2*a02+X^2)*Z^2+(X*Y^2*a12+Y^3*a03+X^2*Y)*Z+a13*X*Y^3+a04*Y^4;

  Hui A1-normal forms that admit at least another singularity

 */

function A1NFBiSingular(a03, a04, a12, a13, a02)

    return 64*a03^6*a13^2 + 64*a03^5*a04^2 - 64*a03^5*a04*a12*a13 - 96*a03^5*a04*a13^2 - 32*a03^5*a12^2*a13^2 + 144*a03^5*a12*a13^3 -
        108*a03^5*a13^4 - 16*a03^5*a13^2*a02^2 - 128*a03^5*a13^2*a02 + 128*a03^5*a13^2 - 128*a03^4*a04^3 -
        32*a03^4*a04^2*a12^2 + 256*a03^4*a04^2*a12*a13 - 96*a03^4*a04^2*a13^2 - 16*a03^4*a04^2*a02^2 - 128*a03^4*a04^2*a02 +
        128*a03^4*a04^2 + 32*a03^4*a04*a12^3*a13 - 184*a03^4*a04*a12^2*a13^2 + 144*a03^4*a04*a12*a13^3 +
        16*a03^4*a04*a12*a13*a02^2 + 128*a03^4*a04*a12*a13*a02 - 128*a03^4*a04*a12*a13 + 24*a03^4*a04*a13^2*a02^2 -
        256*a03^4*a04*a13^2*a02 - 64*a03^4*a04*a13^2 + 4*a03^4*a12^4*a13^2 - 4*a03^4*a12^3*a13^3 + 8*a03^4*a12^2*a13^2*a02^2 +
        136*a03^4*a12^2*a13^2*a02 - 208*a03^4*a12^2*a13^2 - 36*a03^4*a12*a13^3*a02^2 - 208*a03^4*a12*a13^3*a02 +
        512*a03^4*a12*a13^3 + 27*a03^4*a13^4*a02^2 + 144*a03^4*a13^4*a02 - 168*a03^4*a13^4 + 32*a03^4*a13^2*a02^3 +
        32*a03^4*a13^2*a02^2 - 128*a03^4*a13^2*a02 + 64*a03^4*a13^2 + 64*a03^3*a04^4 - 32*a03^3*a04^3*a12^2 -
        64*a03^3*a04^3*a12*a13 + 64*a03^3*a04^3*a13^2 + 32*a03^3*a04^3*a02^2 - 160*a03^3*a04^3*a02 - 128*a03^3*a04^3 +
        4*a03^3*a04^2*a12^4 + 32*a03^3*a04^2*a12^3*a13 - 32*a03^3*a04^2*a12^2*a13^2 + 8*a03^3*a04^2*a12^2*a02^2 +
        136*a03^3*a04^2*a12^2*a02 - 208*a03^3*a04^2*a12^2 - 64*a03^3*a04^2*a12*a13*a02^2 - 32*a03^3*a04^2*a12*a13*a02 +
        608*a03^3*a04^2*a12*a13 + 24*a03^3*a04^2*a13^2*a02^2 + 688*a03^3*a04^2*a13^2*a02 + 240*a03^3*a04^2*a13^2 +
        32*a03^3*a04^2*a02^3 + 32*a03^3*a04^2*a02^2 - 128*a03^3*a04^2*a02 + 64*a03^3*a04^2 - 4*a03^3*a04*a12^5*a13 +
        4*a03^3*a04*a12^4*a13^2 - 8*a03^3*a04*a12^3*a13*a02^2 - 136*a03^3*a04*a12^3*a13*a02 + 208*a03^3*a04*a12^3*a13 +
        46*a03^3*a04*a12^2*a13^2*a02^2 + 316*a03^3*a04*a12^2*a13^2*a02 - 624*a03^3*a04*a12^2*a13^2 -
        36*a03^3*a04*a12*a13^3*a02^2 - 1016*a03^3*a04*a12*a13^3*a02 - 16*a03^3*a04*a12*a13^3 - 32*a03^3*a04*a12*a13*a02^3 -
        32*a03^3*a04*a12*a13*a02^2 + 128*a03^3*a04*a12*a13*a02 - 64*a03^3*a04*a12*a13 + 630*a03^3*a04*a13^4*a02 -
        120*a03^3*a04*a13^4 + 56*a03^3*a04*a13^2*a02^3 + 688*a03^3*a04*a13^2*a02^2 - 704*a03^3*a04*a13^2*a02 +
        32*a03^3*a04*a13^2 - a03^3*a12^4*a13^2*a02^2 - 44*a03^3*a12^4*a13^2*a02 + 107*a03^3*a12^4*a13^2 +
        a03^3*a12^3*a13^3*a02^2 + 182*a03^3*a12^3*a13^3*a02 - 460*a03^3*a12^3*a13^3 - 267/2*a03^3*a12^2*a13^4*a02 +
        839*a03^3*a12^2*a13^4 - 32*a03^3*a12^2*a13^2*a02^3 + 8*a03^3*a12^2*a13^2*a02^2 + 88*a03^3*a12^2*a13^2*a02 -
        48*a03^3*a12^2*a13^2 - 450*a03^3*a12*a13^5 + 52*a03^3*a12*a13^3*a02^3 - 344*a03^3*a12*a13^3*a02^2 +
        112*a03^3*a12*a13^3*a02 + 112*a03^3*a12*a13^3 - 36*a03^3*a13^4*a02^3 + 34*a03^3*a13^4*a02^2 - 304*a03^3*a13^4*a02 +
        196*a03^3*a13^4 - 16*a03^3*a13^2*a02^4 + 32*a03^3*a13^2*a02^3 - 16*a03^3*a13^2*a02^2 - 16*a03^2*a04^4*a02^2 +
        576*a03^2*a04^4*a02 + 432*a03^2*a04^4 + 8*a03^2*a04^3*a12^2*a02^2 + 32*a03^2*a04^3*a12^2*a02 - 24*a03^2*a04^3*a12^2 +
        16*a03^2*a04^3*a12*a13*a02^2 - 1216*a03^2*a04^3*a12*a13*a02 - 816*a03^2*a04^3*a12*a13 - 16*a03^2*a04^3*a13^2*a02^2 +
        432*a03^2*a04^3*a13^2*a02 - 744*a03^2*a04^3*a13^2 + 32*a03^2*a04^3*a02^3 + 608*a03^2*a04^3*a02^2 - 576*a03^2*a04^3*a02
        - a03^2*a04^2*a12^4*a02^2 - 44*a03^2*a04^2*a12^4*a02 + 107*a03^2*a04^2*a12^4 - 8*a03^2*a04^2*a12^3*a13*a02^2 +
        128*a03^2*a04^2*a12^3*a13*a02 - 392*a03^2*a04^2*a12^3*a13 + 8*a03^2*a04^2*a12^2*a13^2*a02^2 +
        816*a03^2*a04^2*a12^2*a13^2*a02 + 1148*a03^2*a04^2*a12^2*a13^2 - 32*a03^2*a04^2*a12^2*a02^3 +
        8*a03^2*a04^2*a12^2*a02^2 + 88*a03^2*a04^2*a12^2*a02 - 48*a03^2*a04^2*a12^2 - 712*a03^2*a04^2*a12*a13^3*a02 +
        828*a03^2*a04^2*a12*a13^3 + 16*a03^2*a04^2*a12*a13*a02^3 - 928*a03^2*a04^2*a12*a13*a02^2 + 688*a03^2*a04^2*a12*a13*a02
        + 96*a03^2*a04^2*a12*a13 - 825*a03^2*a04^2*a13^4 - 160*a03^2*a04^2*a13^2*a02^3 - 192*a03^2*a04^2*a13^2*a02^2 -
        856*a03^2*a04^2*a13^2*a02 + 1104*a03^2*a04^2*a13^2 - 16*a03^2*a04^2*a02^4 + 32*a03^2*a04^2*a02^3 -
        16*a03^2*a04^2*a02^2 + a03^2*a04*a12^5*a13*a02^2 + 44*a03^2*a04*a12^5*a13*a02 - 107*a03^2*a04*a12^5*a13 -
        a03^2*a04*a12^4*a13^2*a02^2 - 249*a03^2*a04*a12^4*a13^2*a02 + 1235/2*a03^2*a04*a12^4*a13^2 +
        196*a03^2*a04*a12^3*a13^3*a02 - 1582*a03^2*a04*a12^3*a13^3 + 32*a03^2*a04*a12^3*a13*a02^3 -
        8*a03^2*a04*a12^3*a13*a02^2 - 88*a03^2*a04*a12^3*a13*a02 + 48*a03^2*a04*a12^3*a13 + 1945/2*a03^2*a04*a12^2*a13^4 -
        78*a03^2*a04*a12^2*a13^2*a02^3 - 124*a03^2*a04*a12^2*a13^2*a02^2 + 828*a03^2*a04*a12^2*a13^2*a02 -
        200*a03^2*a04*a12^2*a13^2 + 236*a03^2*a04*a12*a13^3*a02^3 + 1384*a03^2*a04*a12*a13^3*a02^2 -
        1312*a03^2*a04*a12*a13^3*a02 - 896*a03^2*a04*a12*a13^3 + 16*a03^2*a04*a12*a13*a02^4 - 32*a03^2*a04*a12*a13*a02^3 +
        16*a03^2*a04*a12*a13*a02^2 - 144*a03^2*a04*a13^4*a02^3 - 682*a03^2*a04*a13^4*a02^2 + 1328*a03^2*a04*a13^4*a02 +
        216*a03^2*a04*a13^4 - 152*a03^2*a04*a13^2*a02^4 - 160*a03^2*a04*a13^2*a02^3 + 632*a03^2*a04*a13^2*a02^2 -
        320*a03^2*a04*a13^2*a02 + 9/2*a03^2*a12^6*a13^2*a02 - 45/2*a03^2*a12^6*a13^2 - 9/2*a03^2*a12^5*a13^3*a02 +
        351/4*a03^2*a12^5*a13^3 - 1017/16*a03^2*a12^4*a13^4 + 10*a03^2*a12^4*a13^2*a02^3 - 10*a03^2*a12^4*a13^2*a02^2 -
        20*a03^2*a12^4*a13^2*a02 + 12*a03^2*a12^4*a13^2 - 41*a03^2*a12^3*a13^3*a02^3 + 266*a03^2*a12^3*a13^3*a02^2 -
        346*a03^2*a12^3*a13^3*a02 - 20*a03^2*a12^3*a13^3 + 30*a03^2*a12^2*a13^4*a02^3 - 1553/2*a03^2*a12^2*a13^4*a02^2 +
        2095/2*a03^2*a12^2*a13^4*a02 - 91*a03^2*a12^2*a13^4 + 8*a03^2*a12^2*a13^2*a02^4 - 16*a03^2*a12^2*a13^2*a02^3 +
        8*a03^2*a12^2*a13^2*a02^2 + 510*a03^2*a12*a13^5*a02^2 - 1355*a03^2*a12*a13^5*a02 + 610*a03^2*a12*a13^5 +
        52*a03^2*a12*a13^3*a02^4 + 128*a03^2*a12*a13^3*a02^3 - 340*a03^2*a12*a13^3*a02^2 + 160*a03^2*a12*a13^3*a02 +
        1125/2*a03^2*a13^6*a02 - 375*a03^2*a13^6 + 2*a03^2*a13^4*a02^4 + 222*a03^2*a13^4*a02^3 + 11*a03^2*a13^4*a02^2 -
        336*a03^2*a13^4*a02 + 128*a03^2*a13^4 - 288*a03*a04^5*a02 - 864*a03*a04^5 + 216*a03*a04^4*a12^2*a02 +
        72*a03*a04^4*a12^2 + 288*a03*a04^4*a12*a13*a02 + 2016*a03*a04^4*a12*a13 - 288*a03*a04^4*a13^2*a02 -
        648*a03*a04^4*a13^2 - 128*a03*a04^4*a02^3 - 576*a03*a04^4*a02^2 - 288*a03*a04^4*a02 + 864*a03*a04^4 -
        54*a03*a04^3*a12^4*a02 + 126*a03*a04^3*a12^4 - 216*a03*a04^3*a12^3*a13*a02 - 648*a03*a04^3*a12^3*a13 +
        216*a03*a04^3*a12^2*a13^2*a02 - 1350*a03*a04^3*a12^2*a13^2 - 8*a03*a04^3*a12^2*a02^3 - 392*a03*a04^3*a12^2*a02^2 +
        792*a03*a04^3*a12^2*a02 - 72*a03*a04^3*a12^2 + 1260*a03*a04^3*a12*a13^3 + 272*a03*a04^3*a12*a13*a02^3 +
        1936*a03*a04^3*a12*a13*a02^2 - 1008*a03*a04^3*a12*a13*a02 - 1584*a03*a04^3*a12*a13 - 96*a03*a04^3*a13^2*a02^3 -
        1064*a03*a04^3*a13^2*a02^2 + 1800*a03*a04^3*a13^2*a02 - 360*a03*a04^3*a13^2 - 128*a03*a04^3*a02^4 -
        160*a03*a04^3*a02^3 + 576*a03*a04^3*a02^2 - 288*a03*a04^3*a02 + 9/2*a03*a04^2*a12^6*a02 - 45/2*a03*a04^2*a12^6 +
        54*a03*a04^2*a12^5*a13*a02 - 54*a03*a04^2*a12^5*a13 - 54*a03*a04^2*a12^4*a13^2*a02 + 1647/2*a03*a04^2*a12^4*a13^2 +
        10*a03*a04^2*a12^4*a02^3 - 10*a03*a04^2*a12^4*a02^2 - 20*a03*a04^2*a12^4*a02 + 12*a03*a04^2*a12^4 -
        657*a03*a04^2*a12^3*a13^3 - 28*a03*a04^2*a12^3*a13*a02^3 + 628*a03*a04^2*a12^3*a13*a02^2 -
        1108*a03*a04^2*a12^3*a13*a02 + 60*a03*a04^2*a12^3*a13 - 184*a03*a04^2*a12^2*a13^2*a02^3 -
        2230*a03*a04^2*a12^2*a13^2*a02^2 + 3056*a03*a04^2*a12^2*a13^2*a02 - 342*a03*a04^2*a12^2*a13^2 +
        8*a03*a04^2*a12^2*a02^4 - 16*a03*a04^2*a12^2*a02^3 + 8*a03*a04^2*a12^2*a02^2 + 160*a03*a04^2*a12*a13^3*a02^3 +
        1896*a03*a04^2*a12*a13^3*a02^2 - 5084*a03*a04^2*a12*a13^3*a02 + 3480*a03*a04^2*a12*a13^3 + 176*a03*a04^2*a12*a13*a02^4
        + 272*a03*a04^2*a12*a13*a02^3 - 880*a03*a04^2*a12*a13*a02^2 + 432*a03*a04^2*a12*a13*a02 - 560*a03*a04^2*a13^4*a02^2 +
        1980*a03*a04^2*a13^4*a02 - 2310*a03*a04^2*a13^4 + 56*a03*a04^2*a13^2*a02^4 - 232*a03*a04^2*a13^2*a02^3 +
        968*a03*a04^2*a13^2*a02^2 - 1368*a03*a04^2*a13^2*a02 + 576*a03*a04^2*a13^2 - 9/2*a03*a04*a12^7*a13*a02 +
        45/2*a03*a04*a12^7*a13 + 9/2*a03*a04*a12^6*a13^2*a02 - 945/8*a03*a04*a12^6*a13^2 + 369/4*a03*a04*a12^5*a13^3 -
        10*a03*a04*a12^5*a13*a02^3 + 10*a03*a04*a12^5*a13*a02^2 + 20*a03*a04*a12^5*a13*a02 - 12*a03*a04*a12^5*a13 +
        56*a03*a04*a12^4*a13^2*a02^3 - 246*a03*a04*a12^4*a13^2*a02^2 + 235/2*a03*a04*a12^4*a13^2*a02 + 40*a03*a04*a12^4*a13^2
        - 44*a03*a04*a12^3*a13^3*a02^3 + 714*a03*a04*a12^3*a13^3*a02^2 - 570*a03*a04*a12^3*a13^3*a02 + 914*a03*a04*a12^3*a13^3
        - 8*a03*a04*a12^3*a13*a02^4 + 16*a03*a04*a12^3*a13*a02^3 - 8*a03*a04*a12^3*a13*a02^2 - 466*a03*a04*a12^2*a13^4*a02^2 +
        3341/2*a03*a04*a12^2*a13^4*a02 - 6967/2*a03*a04*a12^2*a13^4 + 50*a03*a04*a12^2*a13^2*a02^4 -
        252*a03*a04*a12^2*a13^2*a02^3 + 186*a03*a04*a12^2*a13^2*a02^2 - 56*a03*a04*a12^2*a13^2*a02 -
        1025*a03*a04*a12*a13^5*a02 + 3225*a03*a04*a12*a13^5 - 316*a03*a04*a12*a13^3*a02^4 + 432*a03*a04*a12*a13^3*a02^3 -
        444*a03*a04*a12*a13^3*a02^2 + 1048*a03*a04*a12*a13^3*a02 - 576*a03*a04*a12*a13^3 - 1875/2*a03*a04*a13^6 +
        160*a03*a04*a13^4*a02^4 - 502*a03*a04*a13^4*a02^3 + 14*a03*a04*a13^4*a02^2 - 86*a03*a04*a13^4*a02 + 288*a03*a04*a13^4
        + 72*a03*a04*a13^2*a02^5 - 144*a03*a04*a13^2*a02^4 + 72*a03*a04*a13^2*a02^3 + 27/16*a03*a12^8*a13^2 -
        27/16*a03*a12^7*a13^3 - a03*a12^6*a13^2*a02^3 + 3/2*a03*a12^6*a13^2*a02^2 + 3/2*a03*a12^6*a13^2*a02 - a03*a12^6*a13^2
        + a03*a12^5*a13^3*a02^3 - 9*a03*a12^5*a13^3*a02^2 + 321/4*a03*a12^5*a13^3*a02 - 2*a03*a12^5*a13^3 +
        15/2*a03*a12^4*a13^4*a02^2 - 2091/8*a03*a12^4*a13^4*a02 - 567/4*a03*a12^4*a13^4 - a03*a12^4*a13^2*a02^4 +
        2*a03*a12^4*a13^2*a02^3 - a03*a12^4*a13^2*a02^2 + 705/4*a03*a12^3*a13^5*a02 + 1655/4*a03*a12^3*a13^5 -
        41*a03*a12^3*a13^3*a02^4 + 54*a03*a12^3*a13^3*a02^3 + 67*a03*a12^3*a13^3*a02^2 - 44*a03*a12^3*a13^3*a02 -
        2125/8*a03*a12^2*a13^6 + 140*a03*a12^2*a13^4*a02^4 - 733/2*a03*a12^2*a13^4*a02^3 + 300*a03*a12^2*a13^4*a02^2 -
        86*a03*a12^2*a13^4*a02 + 80*a03*a12^2*a13^4 - 96*a03*a12*a13^5*a02^4 + 716*a03*a12*a13^5*a02^3 -
        671*a03*a12*a13^5*a02^2 - 149*a03*a12*a13^5*a02 - 16*a03*a12*a13^5 - 36*a03*a12*a13^3*a02^5 + 72*a03*a12*a13^3*a02^4 -
        36*a03*a12*a13^3*a02^3 - 400*a03*a13^6*a02^3 + 425*a03*a13^6*a02^2 - 25/2*a03*a13^6*a02 + 100*a03*a13^6 -
        36*a03*a13^4*a02^5 - 126*a03*a13^4*a02^4 + 306*a03*a13^4*a02^3 - 144*a03*a13^4*a02^2 + 432*a04^6 - 432*a04^5*a12^2 -
        432*a04^5*a12*a13 + 432*a04^5*a13^2 + 64*a04^5*a02^3 + 864*a04^5*a02 - 864*a04^5 + 162*a04^4*a12^4 +
        432*a04^4*a12^3*a13 - 432*a04^4*a12^2*a13^2 - 48*a04^4*a12^2*a02^3 + 24*a04^4*a12^2*a02^2 + 360*a04^4*a12^2*a02 -
        864*a04^4*a12^2 - 64*a04^4*a12*a13*a02^3 - 48*a04^4*a12*a13*a02^2 - 2880*a04^4*a12*a13*a02 + 3888*a04^4*a12*a13 +
        64*a04^4*a13^2*a02^3 + 1656*a04^4*a13^2*a02 - 2160*a04^4*a13^2 + 128*a04^4*a02^4 - 128*a04^4*a02^3 + 432*a04^4*a02^2 -
        864*a04^4*a02 + 432*a04^4 - 27*a04^3*a12^6 - 162*a04^3*a12^5*a13 + 162*a04^3*a12^4*a13^2 + 12*a04^3*a12^4*a02^3 -
        12*a04^3*a12^4*a02^2 - 150*a04^3*a12^4*a02 + 18*a04^3*a12^4 + 48*a04^3*a12^3*a13*a02^3 - 120*a04^3*a12^3*a13*a02 +
        1656*a04^3*a12^3*a13 - 48*a04^3*a12^2*a13^2*a02^3 + 72*a04^3*a12^2*a13^2*a02^2 + 2802*a04^3*a12^2*a13^2*a02 -
        6120*a04^3*a12^2*a13^2 + 80*a04^3*a12^2*a02^4 - 120*a04^3*a12^2*a02^3 - 96*a04^3*a12^2*a02^2 + 72*a04^3*a12^2*a02 -
        48*a04^3*a12*a13^3*a02^2 - 2916*a04^3*a12*a13^3*a02 + 5472*a04^3*a12*a13^3 - 416*a04^3*a12*a13*a02^4 +
        496*a04^3*a12*a13*a02^3 - 672*a04^3*a12*a13*a02^2 + 1584*a04^3*a12*a13*a02 - 864*a04^3*a12*a13 + 900*a04^3*a13^4*a02 -
        1350*a04^3*a13^4 + 240*a04^3*a13^2*a02^4 - 328*a04^3*a13^2*a02^3 + 384*a04^3*a13^2*a02^2 - 792*a04^3*a13^2*a02 +
        432*a04^3*a13^2 + 64*a04^3*a02^5 - 128*a04^3*a02^4 + 64*a04^3*a02^3 + 27/16*a04^2*a12^8 + 27*a04^2*a12^7*a13 -
        27*a04^2*a12^6*a13^2 - a04^2*a12^6*a02^3 + 3/2*a04^2*a12^6*a02^2 + 3/2*a04^2*a12^6*a02 - a04^2*a12^6 -
        12*a04^2*a12^5*a13*a02^3 + 9*a04^2*a12^5*a13*a02^2 + 216*a04^2*a12^5*a13*a02 - 21*a04^2*a12^5*a13 +
        12*a04^2*a12^4*a13^2*a02^3 - 36*a04^2*a12^4*a13^2*a02^2 - 1119/2*a04^2*a12^4*a13^2*a02 - 903*a04^2*a12^4*a13^2 -
        a04^2*a12^4*a02^4 + 2*a04^2*a12^4*a02^3 - a04^2*a12^4*a02^2 + 24*a04^2*a12^3*a13^3*a02^2 - 105*a04^2*a12^3*a13^3*a02 +
        3248*a04^2*a12^3*a13^3 - 116*a04^2*a12^3*a13*a02^4 + 172*a04^2*a12^3*a13*a02^3 + 148*a04^2*a12^3*a13*a02^2 -
        108*a04^2*a12^3*a13*a02 + 345*a04^2*a12^2*a13^4*a02 - 3330*a04^2*a12^2*a13^4 + 456*a04^2*a12^2*a13^2*a02^4 -
        630*a04^2*a12^2*a13^2*a02^3 + 204*a04^2*a12^2*a13^2*a02^2 - 750*a04^2*a12^2*a13^2*a02 + 504*a04^2*a12^2*a13^2 +
        1125*a04^2*a12*a13^5 - 416*a04^2*a12*a13^3*a02^4 + 664*a04^2*a12*a13^3*a02^3 - 272*a04^2*a12*a13^3*a02^2 +
        528*a04^2*a12*a13^3*a02 - 360*a04^2*a12*a13^3 - 96*a04^2*a12*a13*a02^5 + 192*a04^2*a12*a13*a02^4 -
        96*a04^2*a12*a13*a02^3 + 128*a04^2*a13^4*a02^4 - 208*a04^2*a13^4*a02^3 + 443*a04^2*a13^4*a02^2 - 378*a04^2*a13^4*a02 +
        18*a04^2*a13^4 + 48*a04^2*a13^2*a02^5 - 120*a04^2*a13^2*a02^4 + 96*a04^2*a13^2*a02^3 - 24*a04^2*a13^2*a02^2 -
        27/16*a04*a12^9*a13 + 27/16*a04*a12^8*a13^2 + a04*a12^7*a13*a02^3 - 3/2*a04*a12^7*a13*a02^2 - 3/2*a04*a12^7*a13*a02 +
        a04*a12^7*a13 - a04*a12^6*a13^2*a02^3 + 9/2*a04*a12^6*a13^2*a02^2 - 489/8*a04*a12^6*a13^2*a02 + 2*a04*a12^6*a13^2 -
        3*a04*a12^5*a13^3*a02^2 + 861/4*a04*a12^5*a13^3*a02 + 126*a04*a12^5*a13^3 + a04*a12^5*a13*a02^4 -
        2*a04*a12^5*a13*a02^3 + a04*a12^5*a13*a02^2 - 597/4*a04*a12^4*a13^4*a02 - 2959/8*a04*a12^4*a13^4 +
        33*a04*a12^4*a13^2*a02^4 - 47*a04*a12^4*a13^2*a02^3 - 50*a04*a12^4*a13^2*a02^2 + 34*a04*a12^4*a13^2*a02 +
        475/2*a04*a12^3*a13^5 - 116*a04*a12^3*a13^3*a02^4 + 182*a04*a12^3*a13^3*a02^3 - 20*a04*a12^3*a13^3*a02^2 +
        74*a04*a12^3*a13^3*a02 - 72*a04*a12^3*a13^3 + 80*a04*a12^2*a13^4*a02^4 - 214*a04*a12^2*a13^4*a02^3 +
        284*a04*a12^2*a13^4*a02^2 - 765/2*a04*a12^2*a13^4*a02 + 12*a04*a12^2*a13^4 + 30*a04*a12^2*a13^2*a02^5 -
        60*a04*a12^2*a13^2*a02^4 + 30*a04*a12^2*a13^2*a02^3 + 80*a04*a12*a13^5*a02^3 - 835*a04*a12*a13^5*a02^2 +
        1115*a04*a12*a13^5*a02 + 30*a04*a12*a13^5 - 12*a04*a12*a13^3*a02^5 + 48*a04*a12*a13^3*a02^4 - 60*a04*a12*a13^3*a02^3 +
        24*a04*a12*a13^3*a02^2 + 500*a04*a13^6*a02^2 - 1125/2*a04*a13^6*a02 - 125*a04*a13^6 + 48*a04*a13^4*a02^5 -
        54*a04*a13^4*a02^4 + 210*a04*a13^4*a02^3 - 396*a04*a13^4*a02^2 + 192*a04*a13^4*a02 - 27/16*a12^7*a13^3*a02 +
        27/16*a12^6*a13^4*a02 + 27/16*a12^6*a13^4 - 27/16*a12^5*a13^5 + a12^5*a13^3*a02^4 - 3/2*a12^5*a13^3*a02^3 -
        3/2*a12^5*a13^3*a02^2 + a12^5*a13^3*a02 - a12^4*a13^4*a02^4 + 7/2*a12^4*a13^4*a02^3 - 873/16*a12^4*a13^4*a02^2 +
        7/2*a12^4*a13^4*a02 - a12^4*a13^4 - 2*a12^3*a13^5*a02^3 + 681/4*a12^3*a13^5*a02^2 + 681/4*a12^3*a13^5*a02 -
        2*a12^3*a13^5 + a12^3*a13^3*a02^5 - 2*a12^3*a13^3*a02^4 + a12^3*a13^3*a02^3 - 225/2*a12^2*a13^6*a02^2 -
        3925/8*a12^2*a13^6*a02 - 225/2*a12^2*a13^6 + 30*a12^2*a13^4*a02^5 - 87/2*a12^2*a13^4*a02^4 - 87/2*a12^2*a13^4*a02^3 +
        30*a12^2*a13^4*a02^2 + 625/2*a12*a13^7*a02 + 625/2*a12*a13^7 - 96*a12*a13^5*a02^5 + 126*a12*a13^5*a02^4 -
        6*a12*a13^5*a02^3 + 126*a12*a13^5*a02^2 - 96*a12*a13^5*a02 - 3125/16*a13^8 + 64*a13^6*a02^5 - 80*a13^6*a02^4 +
        5/2*a13^6*a02^3 + 5/2*a13^6*a02^2 - 80*a13^6*a02 + 64*a13^6 + 27*a13^4*a02^6 - 54*a13^4*a02^5 + 27*a13^4*a02^4;

end function;

/*
  f := X^2*Z^2 + X*Y^3 + a12*X*Y^2*Z + a11*X*Y*Z^2 + a03*Y^3*Z + a02*Y^2*Z^2 + Y*Z^3;

  Hui A2-normal forms that admit at least another singularity

 */

function A2NFBiSingular(a02, a03, a11, a12)

    return -1024*a02^5 + 1536*a02^4*a03*a12 + 768*a02^4*a11^2 - 128*a02^4*a11*a12^2 + 16*a02^4*a12^4 -
        1152*a02^3*a03^2*a11 - 480*a02^3*a03^2*a12^2 - 1024*a02^3*a03*a11^2*a12 +
        128*a02^3*a03*a11*a12^3 - 16*a02^3*a03*a12^5 + 6400*a02^3*a03 - 192*a02^3*a11^4 +
        64*a02^3*a11^3*a12^2 - 8*a02^3*a11^2*a12^4 - 2560*a02^3*a11*a12 + 32*a02^3*a12^3 -
        432*a02^2*a03^4 + 576*a02^2*a03^3*a11*a12 - 16*a02^2*a03^3*a12^3 + 832*a02^2*a03^2*a11^3 +
        112*a02^2*a03^2*a11^2*a12^2 + 16*a02^2*a03^2*a11*a12^4 - 8160*a02^2*a03^2*a12 +
        224*a02^2*a03*a11^4*a12 - 64*a02^2*a03*a11^3*a12^3 + 8*a02^2*a03*a11^2*a12^5 -
        2560*a02^2*a03*a11^2 + 4432*a02^2*a03*a11*a12^2 - 120*a02^2*a03*a12^4 + 16*a02^2*a11^6 -
        8*a02^2*a11^5*a12^2 + a02^2*a11^4*a12^4 + 704*a02^2*a11^3*a12 - 296*a02^2*a11^2*a12^3 +
        36*a02^2*a11*a12^5 + 4000*a02^2*a11 + 1800*a02^2*a12^2 + 216*a02*a03^4*a11^2 -
        288*a02*a03^3*a11^3*a12 + 8*a02*a03^3*a11^2*a12^3 + 5040*a02*a03^3*a11 + 2136*a02*a03^3*a12^2
        - 200*a02*a03^2*a11^5 + 34*a02*a03^2*a11^4*a12^2 - 8*a02*a03^2*a11^3*a12^4 -
        632*a02*a03^2*a11^2*a12 - 1636*a02*a03^2*a11*a12^3 + 72*a02*a03^2*a12^5 - 9000*a02*a03^2 -
        16*a02*a03*a11^6*a12 + 8*a02*a03*a11^5*a12^3 - a02*a03*a11^4*a12^5 + 368*a02*a03*a11^4 -
        852*a02*a03*a11^3*a12^2 + 310*a02*a03*a11^2*a12^4 - 36*a02*a03*a11*a12^6 +
        800*a02*a03*a11*a12 - 2820*a02*a03*a12^3 - 16*a02*a11^5*a12 + 8*a02*a11^4*a12^3 -
        a02*a11^3*a12^5 - 200*a02*a11^3 - 430*a02*a11^2*a12^2 + 216*a02*a11*a12^4 - 27*a02*a12^6 -
        5000*a02*a12 + 1728*a03^5 - 27*a03^4*a11^4 - 3168*a03^4*a11*a12 + 64*a03^4*a12^3 +
        36*a03^3*a11^5*a12 - a03^3*a11^4*a12^3 - 1132*a03^3*a11^3 + 1610*a03^3*a11^2*a12^2 -
        96*a03^3*a11*a12^4 + 7200*a03^3*a12 + 16*a03^2*a11^7 - 8*a03^2*a11^6*a12^2 +
        a03^2*a11^5*a12^4 + 476*a03^2*a11^4*a12 - 215*a03^2*a11^3*a12^3 + 30*a03^2*a11^2*a12^5 +
        5550*a03^2*a11^2 - 3020*a03^2*a11*a12^2 + 1017*a03^2*a12^4 - 32*a03*a11^6 +
        32*a03*a11^5*a12^2 - 10*a03*a11^4*a12^4 + a03*a11^3*a12^6 - 980*a03*a11^3*a12 +
        953*a03*a11^2*a12^3 - 279*a03*a11*a12^5 - 7500*a03*a11 + 27*a03*a12^7 + 4250*a03*a12^2 +
        16*a11^5 - 8*a11^4*a12^2 + a11^3*a12^4 + 500*a11^2*a12 - 225*a11*a12^3 + 27*a12^5 + 3125;

end function;

/*
  f := a00*Z^4+(X*a10+Y*a01)*Z^3+(X*Y*a11+X^2+Y^2)*Z^2+X^2*Y^2;

  Hui A1^2-normal forms that admit at least a third singularity

 */
function A1p2NFBiSingular(a00, a01, a10, a11)

    return
        -256*a00^5 + 64*a00^4*a01^2 + 64*a00^4*a10^2 + 256*a00^4*a11^2 + 1024*a00^4
        - 16*a00^3*a01^2*a10^2 - 48*a00^3*a01^2*a11^2 - 768*a00^3*a01^2 -
        704*a00^3*a01*a10*a11 - 48*a00^3*a10^2*a11^2 - 768*a00^3*a10^2 -
        96*a00^3*a11^4 - 256*a00^3*a11^2 - 1536*a00^3 + 128*a00^2*a01^4 +
        160*a00^2*a01^3*a10*a11 + 8*a00^2*a01^2*a10^2*a11^2 +
        784*a00^2*a01^2*a10^2 + 12*a00^2*a01^2*a11^4 - 208*a00^2*a01^2*a11^2 +
        1408*a00^2*a01^2 + 160*a00^2*a01*a10^3*a11 + 368*a00^2*a01*a10*a11^3 -
        704*a00^2*a01*a10*a11 + 128*a00^2*a10^4 + 12*a00^2*a10^2*a11^4 -
        208*a00^2*a10^2*a11^2 + 1408*a00^2*a10^2 + 16*a00^2*a11^6 -
        64*a00^2*a11^4 - 256*a00^2*a11^2 + 1024*a00^2 - 144*a00*a01^4*a10^2 +
        80*a00*a01^4*a11^2 - 512*a00*a01^4 - 36*a00*a01^3*a10^3*a11 -
        44*a00*a01^3*a10*a11^3 + 512*a00*a01^3*a10*a11 - 144*a00*a01^2*a10^4 -
        a00*a01^2*a10^2*a11^4 - 304*a00*a01^2*a10^2*a11^2 - 496*a00*a01^2*a10^2
        - a00*a01^2*a11^6 + 104*a00*a01^2*a11^4 - 208*a00*a01^2*a11^2 -
        768*a00*a01^2 - 44*a00*a01*a10^3*a11^3 + 512*a00*a01*a10^3*a11 -
        52*a00*a01*a10*a11^5 - 160*a00*a01*a10*a11^3 + 1472*a00*a01*a10*a11 +
        80*a00*a10^4*a11^2 - 512*a00*a10^4 - a00*a10^2*a11^6 +
        104*a00*a10^2*a11^4 - 208*a00*a10^2*a11^2 - 768*a00*a10^2 - a00*a11^8 +
        16*a00*a11^6 - 96*a00*a11^4 + 256*a00*a11^2 - 256*a00 + 64*a01^6 -
        96*a01^5*a10*a11 + 27*a01^4*a10^4 + 30*a01^4*a10^2*a11^2 +
        48*a01^4*a10^2 - a01^4*a11^4 + 80*a01^4*a11^2 + 128*a01^4 +
        a01^3*a10^3*a11^3 - 12*a01^3*a10^3*a11 + a01^3*a10*a11^5 -
        116*a01^3*a10*a11^3 - 416*a01^3*a10*a11 + 30*a01^2*a10^4*a11^2 +
        48*a01^2*a10^4 + 33*a01^2*a10^2*a11^4 + 456*a01^2*a10^2*a11^2 +
        240*a01^2*a10^2 - a01^2*a11^6 + 12*a01^2*a11^4 - 48*a01^2*a11^2 +
        64*a01^2 - 96*a01*a10^5*a11 + a01*a10^3*a11^5 - 116*a01*a10^3*a11^3 -
        416*a01*a10^3*a11 + a01*a10*a11^7 - 12*a01*a10*a11^5 + 48*a01*a10*a11^3
        - 64*a01*a10*a11 + 64*a10^6 - a10^4*a11^4 + 80*a10^4*a11^2 + 128*a10^4 -
        a10^2*a11^6 + 12*a10^2*a11^4 - 48*a10^2*a11^2 + 64*a10^2;

end function;

// Main

time ret :=
    G3SingularProof(Fld : DOInclusions := DOInclusions, HNFLargeDims := HNFLargeDims, HNFSmallDims := HNFSmallDims);

"All in all (characteristic", Characteristic(Fld),") :", ret;
