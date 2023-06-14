/***
 * Exported intrinsics.
 *
 * intrinsic QuarticTypeFromOctad(f::RngMPolElt, p::RngIntElt :
 *   PrecMin := 100,
 *   PrecMax := 2^8*100,
 *   gbasis := false,
 *   LPrate := 10,
 *   randomize := true,
 *   AnalysisLevel := 0) -> MonStgElt, SetMulti
 *
 ********************************************************************/

import "verbose.m" : MyBenchIndent, MyBenchStart, MyBenchStop;
import "stabletypes.m" : AllTypes, OctadDiagrams, SubspaceGraphs;
import "loctad.m" : NormaliseOctad;
import "bblocks.m" : AssociatedSubspace, SubspaceGraph, String;


intrinsic QuarticTypeFromOctad(f::RngMPolElt, p::RngIntElt :
    PrecMin := 100,
    PrecMax := 2^8*100,
    gbasis := false,
    LPrate := 10,
    randomize := true,
    AnalysisLevel := 0,
    subspace := true, thetaconstants := false) -> MonStgElt, SetMulti

    {Stable reduction type of a quartic via a Cayley octad approach}

    /* Reset indentation */
    SetVerbose("G3CayleyIndents", 0);

    /* Input normalization */
    P := Parent(f);
    assert(
        ((Rank(P) eq 3 and {Degree(e) : e in Monomials(f)} eq {4}) or
        (Rank(P) eq 2 and Degree(f) le 4))
        );

    F := f;
    if Rank(P) eq 2 then
        F := Basis(Homogenization(ideal<P|f>))[1];
        if Characteristic(P) eq 0 then
            F *:= LCM([Denominator(e) : e in Coefficients(F)]);
        end if;
    end if;
    P := Parent(F);

    if Type(P) ne Prj then P := ProjectiveSpace(P); end if;
    x := P.1; y := P.2; z := P.3; AssignNames(~P, ["x", "y", "z"]);
    F := Evaluate(F, [x, y, z]);

    SubspaceType := "";

    /* let's go */
    vprintf G3Cayley, 1: "%o***\n", MyBenchIndent("");
    vprintf G3Cayley, 1: "%o* Stable reduction type of a quartic via an octad approach\n", MyBenchIndent("");
    vprintf G3Cayley, 1: "%o**********************************************************\n", MyBenchIndent("");
    vprint  G3Cayley, 1: "";


    TT := MyBenchStart(1, "the reduction type");
    vprint  G3Cayley, 1: "";

    vprintf G3Cayley, 1: "%oHere, p := %o;\n\n", MyBenchIndent(""), p;
    vprintf G3Cayley, 1: "%oAnd,  f := %o;\n", MyBenchIndent(""), F;
    vprint  G3Cayley, 1: "";


    vprintf G3Cayley, 1:  "%oOptions are\n", MyBenchIndent("");
    vprintf G3Cayley, 1:  "%o\t     Analysis: %o\n", MyBenchIndent(""), AnalysisLevel;
    vprintf G3Cayley, 1:  "%o\t    Prec. Min: %o\n", MyBenchIndent(""), PrecMin;
    vprintf G3Cayley, 1:  "%o\t    Prec. Max: %o\n", MyBenchIndent(""), PrecMax;
    vprintf G3Cayley, 1:  "%o\t    Randomize: %o\n", MyBenchIndent(""), randomize;
    vprintf G3Cayley, 1:  "%o\t       LPrate: %o\n", MyBenchIndent(""), LPrate;
    vprintf G3Cayley, 1:  "%o\t     Groebner: %o\n", MyBenchIndent(""), gbasis;
    vprint  G3Cayley, 1: "";

    PGLIndexes :=
        Sort([ Sort(Setseq(S)) cat Sort(Setseq({1..8} diff S)) : S in Subsets({1..8}, 5) ]);
    CreIndexes := {}; for S in Subsets({1..8}, 4) do
        if ({1..8} diff S) in CreIndexes then continue; end if;
        Include(~CreIndexes, S);
    end for;
    CreIndexes := Sort([ Sort(Setseq(E)) : E in CreIndexes ]);

    BBType := {* *}; IsHyper := "Unknown";

    Prec := PrecMin; onerr := false; TT := Cputime();
    while Prec le PrecMax do

        vprintf G3Cayley, 1: "%o+++\n", MyBenchIndent("");
        vprintf G3Cayley, 1: "%o+ Precision := %o\n", MyBenchIndent(""), Prec;
        vprintf G3Cayley, 1: "%o++++++++++++++++++\n", MyBenchIndent("");
        vprint  G3Cayley, 1: "";

        /* One Cayley octad */
        try
            indent := GetVerbose("G3CayleyIndents");
            Octad := pAdicCayleyOctad(F, p :
                Prec := Prec, gbasis := gbasis, LPrate := LPrate, randomize := randomize);
        catch e
            Prec *:= 2; onerr := true;
            SetVerbose("G3CayleyIndents", indent);
            vprintf G3Cayley, 1:
                "\n%o!!! An error catched in pAdicCayleyOctad(), let us restart at precision %o...\n",
                MyBenchIndent(""), Prec;
            vprint  G3Cayley, 1: "";

        end try;
        vprint  G3Cayley, 1: "";
        if onerr then onerr := false; continue; end if;

        K := (Universe(Octad[8]));


        /* Let's loop over the Cremona orbit */
        tt := MyBenchStart(1, "the loop over the Cremona orbit");
        vprint  G3Cayley, 1: "";

        BBType := {* *};

        indent := GetVerbose("G3CayleyIndents"); ThisType := Seqset(AllTypes);
        for i := 1 to 36 do

            vprintf G3Cayley, 1:  "%o@@@ Cremona octad %o\n", MyBenchIndent(""), i;
            vprint  G3Cayley, 1: "";

            /* Cremona action */
            tt := MyBenchStart(1, "Cremona action");
            CreOctad := Octad;
            if i gt 1 then
                try
                    indent := GetVerbose("G3CayleyIndents");
                    L := Sort(Sort(Setseq({1..8} diff Seqset(CreIndexes[i-1])))) cat CreIndexes[i-1];
                    CreOctad := NormaliseOctad(Octad[L]);
                    for j := 6 to 8 do
                        CreOctad[j, 1] := 1 / CreOctad[j, 1];
                        CreOctad[j, 2] := 1 / CreOctad[j, 2];
                        CreOctad[j, 3] := 1 / CreOctad[j, 3];
                        CreOctad[j, 4] := 1 / CreOctad[j, 4];
                    end for;
                catch e
                    Prec *:= 2; onerr := true;
                    SetVerbose("G3CayleyIndents", indent);
                    vprintf G3Cayley, 1:
                        "%o!!! An error catched, let us restart at precision %o...\n",
                        MyBenchIndent(""), Prec;
                end try;
            end if;
            MyBenchStop(1, "Cremona action", tt);
            vprint  G3Cayley, 1: "";
            if onerr then onerr := false; continue; end if;

            /* Integral normalization  */
            tt := MyBenchStart(1, "its integral normalization");
            try
                indent := GetVerbose("G3CayleyIndents");
                CreOctad := NormaliseOctad(CreOctad);
            catch e
                Prec *:= 2; onerr := true;
                SetVerbose("G3CayleyIndents", indent);
                vprintf G3Cayley, 1:
                    "%o!!! An error catched in NormaliseOctad(), let us restart at precision %o...\n",
                    MyBenchIndent(""), Prec;
            end try;
            MyBenchStop(1, "Its integral normalization", tt);
            vprint  G3Cayley, 1: "";
            if onerr then break i; end if;

            /* PGL-orbit of the current octad */
            tt := MyBenchStart(1, "its PGL-orbit");
            kbgn := 1;
            try
                indent := GetVerbose("G3CayleyIndents");
                PGLOrb := []; PGLPlOrb := []; PGLPlVals := [];
                for L in PGLIndexes do
                    OctadNrm   := NormaliseOctad(CreOctad[L]);
                    PlOctad := PluckerCoordinates(OctadNrm);
                    PlVal := Weight(PluckerValuations(PlOctad));

                    Append(~PGLOrb, OctadNrm);
                    Append(~PGLPlOrb, PlOctad);
                    Append(~PGLPlVals, PlVal);

                    kend := #PGLOrb;
                    if AnalysisLevel lt 2 then
                        /* Heuristic choice of a specific octad
                           with a Plucker valuation vector of small weight */
                        if PlVal le 41 then
                            kbgn := #PGLOrb; kend := #PGLOrb;
                            vprintf G3Cayley, 2:  "%o=> Weight %o reached at octad %o\n", MyBenchIndent(""), PlVal, #PGLOrb;
                            vprintf G3Cayley, 2:  "%o   ... It should be enough...\n", MyBenchIndent("");
                            break L;
                        end if;
                        if #PGLOrb ge 14 then
                            _, k := Min(PGLPlVals);
                            kbgn := k; kend := k;
                            break L;
                        end if;
                    end if;

                end for;

            catch e
                Prec *:= 2; onerr := true;
                SetVerbose("G3CayleyIndents", indent);
                vprintf G3Cayley, 1:
                    "%o!!! An error catched in NormaliseOctad(), let us restart at precision %o...\n",
                    MyBenchIndent(""), Prec;
            end try;

            MyBenchStop(1, "its PGL-orbit", tt);
            vprint  G3Cayley, 1: "";
            if onerr then break i; end if;

            /* Decomposition in building blocks */
            tt := MyBenchStart(1, "the Octad diagram of this PGL orbit");
            vprint  G3Cayley, 1: "";

            bbtype := {* *};
            for k := kbgn to kend do

                odiag := {* *};

                vprintf G3Cayley, 1 : "%o+++ PGL-Octad_%o-%o:\n\n", MyBenchIndent(""), i, k;

                tt0 := MyBenchStart(1, "Plucker valuations");
                VlOctad := PluckerValuations(PGLPlOrb[k]);
                vprintf G3Cayley, 2:  "%o=> w := %o;\n", MyBenchIndent(""), VlOctad;
                vprintf G3Cayley, 2:  "%o       Weight(w) := %o;\n", MyBenchIndent(""), Weight(VlOctad);
                MyBenchStop(1, "Plucker valuations", tt0);

                try
                    indent := GetVerbose("G3CayleyIndents");
                    ODiag := CayleyOctadDiagram(VlOctad);
                catch e
                    Prec *:= 2; onerr := true;
                    SetVerbose("G3CayleyIndents", indent);
                    vprintf G3Cayley, 1:
                        "%o!!! An error catched in CayleyOctadDiagram(), let us restart at precision %o...\n",
                        MyBenchIndent(""), Prec;
                end try;
                if onerr then break i; end if;

                odiag join:=  {* T[1] : T in ODiag *};

                if subspace then
                    /* Test to see if subspace diagrams give the right answer. */
                    tt0 := MyBenchStart(1, "Subspace diagrams");
                    G := SubspaceGraph([AssociatedSubspace(B) : B in ODiag | B[1] ne "Ln"]);
                    NewSubspaceType := AllTypes[Index(SubspaceGraphs, String(G))];
                    assert SubspaceType eq "" or SubspaceType eq NewSubspaceType;
                    SubspaceType := NewSubspaceType;
                    vprintf G3Cayley, 1: "%oThe type based on subspace graphs is: %o\n", MyBenchIndent(""), SubspaceType;

                    vprintf G3Cayley, 1: "%o=> Type %o\n", MyBenchIndent(""), odiag;
                    MyBenchStop(1, "subspace diagrams", tt0);
                end if;

                if thetaconstants then
                    /* Even thetaconstant valuations */
                    tt0 := MyBenchStart(1, "Thetaconstants");
                    ThetaConstants := [ G3ThetaFromOctad(i, PGLPlOrb[k]) : i in [1..64] | G3ThetaCharParity(i) ];
                    ThetaVal := [ Valuation(t) : t in ThetaConstants ];
                    vprintf G3Cayley, 1: "%o=> Valuations are %o\n", MyBenchIndent(""), {* e - Min(ThetaVal) : e in ThetaVal *};
                    MyBenchStop(1, "thetaconstants", tt0);
                end if;

                /* Is hyperelliptic or not ? (if not already known) */
                if IsHyper eq "Unknown" then
                    if "Ln" in odiag then IsHyper := "Yes"; end if;
                end if;

                if IsHyper eq "Unknown" then
                    Fpl := PolynomialRing( Rationals(), [ 1 : i in [1..70+1] ] ); pi := Fpl.71;

                    Pl := [ Fpl.i * pi^(Integers()!VlOctad[i]) : i in [1..70] ];
                    Tw := CayleyOctadTwistedCubicRelations(Pl);

                    TermDegrees :=  [ [Degree(T, pi) : T in Terms(E) ] : E in Tw ];
                    if { L[1] eq L[2] : L in TermDegrees } ne {true} then IsHyper := "No"; end if;
                end if;

                if IsHyper eq "Unknown" then
                    TV := Vector([ Degree(e, pi) : e in Tw ]);

                    TwO := CayleyOctadTwistedCubicRelations(PGLPlOrb[k]);
                    TVO := Vector([ Rationals() | Valuation(e) : e in TwO]);
                    vprintf G3Cayley, 1: "%o=> Twisted equation valuations are %o\n",
                        MyBenchIndent(""), TVO;

                    DTV := TVO - TV;

                    if Min(Eltseq(DTV)) gt 0 then IsHyper := "Yes"; end if;

                end if;

                vprintf G3Cayley, 1: "%o=> Hyperelliptic reduction: %o\n", MyBenchIndent(""), IsHyper;

                if IsHyper eq "Yes" and not "Ln" in odiag then odiag; odiag join:= {* "TCu" *}; end if;

                if AnalysisLevel lt 2 then
                    bbtype join:= {* odiag^^56 *};
                else
                    bbtype join:= {* odiag *};
                end if;



            end for;

            MyBenchStop(1, "Octad diagrams of this PGL orbit", tt);
            vprint  G3Cayley, 1: "";
            if onerr then break i; end if;

            BBType join:= {* bbtype *};

            vprintf G3Cayley, 1:
                "%o--- Currently, the octad diagrams are:\n%o\n",
                MyBenchIndent(""), BBType;
            vprint  G3Cayley, 1: "";

            /* So far, which are the compatible reduction types ? */
            j := 1; curType := {}; while j le #AllTypes do
                ok := false;
                for Blck in OctadDiagrams[j] do
                    ok := true;
                    for S in BBType do
                        if not S in Blck or
                            not Multiplicity(BBType, S) le Multiplicity(Blck, S)
                            then
                            ok := false; break;
                        end if;
                    end for;
                    if ok then break; end if;
                end for;
                if ok then Include(~curType, AllTypes[j]); end if;
                j +:= 1;
            end while;
            ThisType meet:= curType;

            vprintf G3Cayley, 1: "%o=> Possible types are %o\n", MyBenchIndent(""), ThisType;
            vprint  G3Cayley, 1: "";

            if AnalysisLevel eq 0 and #ThisType eq 1 then break; end if;

        end for;
        MyBenchStop(1, "The loop over the Cremona orbit", tt);
        vprint G3Cayley, 1: "";

        if onerr then onerr := false; continue; end if;

        break;
    end while;

    vprintf G3Cayley, 1:
        "%oOctad diagrams are:\n%o\n",
        MyBenchIndent(""), BBType;
    vprint  G3Cayley, 1: "";

    if #BBType eq 36 then
        ThisType := [];
        j := 1; while j le #AllTypes do
            if BBType in OctadDiagrams[j] then Append(~ThisType, AllTypes[j]); end if;
            j +:= 1;
        end while;
    else
        ThisType := Setseq(ThisType);
    end if;
    vprintf G3Cayley, 1: "%o=> Finally, possible types are %o\n", MyBenchIndent(""), Seqset(ThisType);
    vprint G3Cayley, 1: "";

    MyBenchStop(1, "The reduction type", TT);

    /* We exit on error ? */
    if Prec gt PrecMax then
        MyBenchStop(1, "The reduction type", TT);
    end if;

    /* An anomalous octad diagram ?! */
    if #ThisType ne 1 then return "(?)", BBType; end if;


    /* Check output against subspace type */
    assert not subspace or (SubspaceType[[2..#SubspaceType-1]] eq ThisType[1][[2..#ThisType[1]-1]]);

    /* End */
    return ThisType[1], AnalysisLevel gt 0 select BBType else {**};

end intrinsic;
