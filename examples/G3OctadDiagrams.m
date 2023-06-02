/*
   This script assumes that the spec file "g3cayley/magma/spec" is loaded
   at magma startup (in the .magmarc file)
 */

SetVerbose("G3Cayley", 2);

/* Stable reduction labels */
AllQuarticTypes := [
    "(3)", "(2n)", "(2e)", "(1nn)", "(1=1)", "(2m)", "(1ne)", "(1ee)", "(0nnn)", "(1---0)", "(1=0n)", "(0nne)", "(1nm)", "(1=0e)", "(1me)", "(0nee)", "(0eee)", "(0----0)", "(0---0n)", "(0n=0n)", "(0nnm)", "(Z=1)", "(0---0e)", "(1=0m)", "(0n=0e)",  "(1mm)",  "(0nme)", "(0e=0e)", "(0mee)", "(CAVE)", "(Z=0n)",  "(0---0m)", "(0n=0m)", "(0nmm)", "(Z=0e)",  "(0m=0e)", "(0mme)", "(BRAID)", "(Z=Z)", "(Z=0m)", "(0m=0m)", "(0mmm)"
    ];
AllHyperTypes := [
    "[3]",  "[2n]", "[2e]", "[1nn]", "[1=1]", "[2m]", "[1ne]", "[1ee]", "[0nnn]", "[1=0n]", "[0nne]", "[1nm]", "[1=0e]", "[1me]", "[0nee]", "[0----0]", "[0n=0n]", "[0nnm]", "[Z=1]", "[1=0m]", "[0n=0e]", "[1mm]", "[0e=0e]", "[0nme]", "[Z=0n]", "[0n=0m]", "[0nmm]", "[Z=0e]", "[0m=0e]", "[Z=Z]", "[Z=0m]", "[0m=0m]"
    ];
AllTypes := AllQuarticTypes cat AllHyperTypes;

/* The number field */

// p := 11; n := 2;
// p := 101; n := 1;
p := NextPrime(10^6); n := 1;

K := n le 1
    select
    Rationals()
    else
    NumberField(ChangeRing(DefiningPolynomial(GF(p^n)), Integers()));
if n gt 1 then K<t> := K; else t := 0; end if;

P2<x,y,z> := ProjectivePlane(K);

"";

dx := 1;
//dx := Index(AllTypes, "[3]");

/* Let's loop over all types */
for t := dx to #AllTypes do

    type := AllTypes[t];

    "@@@";
    "@ Type", type;
    "@@@@@@@@@@@@@@@@@@@@";
    "";

    if t ge Index(AllTypes, "[3]") then
        h, v := G3HyperReductionType(type, p : Domain := [-p..p]);
        f := G3QuarticFromHyper(h, p^(2*v));
    else
        f := QuarticByReductionType(type, p : Domain := [-p..p], K := K);
    end if;

    /* Set AnalysisLevel to 1 for octad diagrams of the full Cremona orbit */
    Type := QuarticTypeFromOctad(f, p : AnalysisLevel := 0);
    "";
    "Stable reduction type :", Type;
    "";
    "";

    if Type ne type then
        "Hum... the awaited type is not returned, possibly a singular model ?!";
        "";
    end if;

end for;

quit;
