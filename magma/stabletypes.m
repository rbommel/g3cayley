import "bblocks.m" : CreAction, DiagramAction, MinimalS8Representative;

/* Types */
AllQuarticTypes := [
    "(3)", "(2n)", "(2e)", "(1nn)", "(1=1)", "(2m)", "(1ne)", "(1ee)", "(0nnn)", "(1---0)", "(1=0n)", "(0nne)", "(1nm)", "(1=0e)", "(1me)", "(0nee)", "(0eee)", "(0----0)", "(0---0n)", "(0n=0n)", "(0nnm)", "(Z=1)", "(0---0e)", "(1=0m)", "(0n=0e)",  "(1mm)",  "(0nme)", "(0e=0e)", "(0mee)", "(CAVE)", "(Z=0n)",  "(0---0m)", "(0n=0m)", "(0nmm)", "(Z=0e)",  "(0m=0e)", "(0mme)", "(BRAID)", "(Z=Z)", "(Z=0m)", "(0m=0m)", "(0mmm)"
    ];
AllHyperTypes := [
    "[3]",  "[2n]", "[2e]", "[1nn]", "[1=1]", "[2m]", "[1ne]", "[1ee]", "[0nnn]", "[1=0n]", "[0nne]", "[1nm]", "[1=0e]", "[1me]", "[0nee]", "[0----0]", "[0n=0n]", "[0nnm]", "[Z=1]", "[1=0m]", "[0n=0e]", "[1mm]", "[0e=0e]", "[0nme]", "[Z=0n]", "[0n=0m]", "[0nmm]", "[Z=0e]", "[0m=0e]", "[Z=Z]", "[Z=0m]", "[0m=0m]"
    ];

AllTypes := AllQuarticTypes cat AllHyperTypes;

ExampleDiagrams := [*
    [* *],
    [* <"Tw", {1,2}> *],
    [* <"TB", {1,2,3}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}> *],
    [* <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"TB", {1,2,3}> *],
    [* <"Tw", {1,2}>, <"TB", {3,4,5}> *],
    [* <"TB", {1,2,3}>, <"TB", {4,5,6}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"Tw", {5,6}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"Pl", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"TB", {5,6,7}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"TB", {3,4,5}> *],
    [* <"TB", {1,2,3}>, <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"TB", {1,2,3}>, <"TB", {4,5,6}> *],
    [* <"Tw", {7,8}>, <"TB", {1,2,3}>, <"TB", {4,5,6}> *],
    [* <"TA", <{7,8}, {{1,2,3},{4,5,6}}>>, <"TB", {1,2,3}>, <"TB", {4,5,6}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"Tw", {5,6}>, <"Tw", {7,8}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"Tw", {5,6}>, <"Pl", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"Tw", {5,6}>, <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"Tw", {5,6}>, <"TB", {5,6,7}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"TB", {5,6,7}>, <"Pl", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"TB", {1,2,3}>, <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {5,6}>, <"TB", {1,2,3}>, <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"Tw", {4,5}>, <"TB", {1,2,3}>, <"TB", {4,5,6}> *],
    [* <"Tw", {1,2}>, <"Tw", {7,8}>, <"TB", {1,2,3}>, <"TB", {4,5,6}> *],
    [* <"TB", {1,2,3}>, <"TB", {5,6,7}>, <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {7,8}>, <"TA", <{7,8}, {{1,2,3},{4,5,6}}>>, <"TB", {1,2,3}>, <"TB", {4,5,6}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"Tw", {5,6}>, <"Tw", {7,8}>, <"Pl", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"Tw", {5,6}>, <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"Tw", {5,6}>, <"Pl", {{1,2,3,4},{5,6,7,8}}>, <"TB", {5,6,7}> *],
    [* <"Tw", {1,2}>, <"Tw", {5,6}>, <"TB", {1,2,3}>, <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"Tw", {4,5}>, <"Tw", {7,8}>, <"TB", {1,2,3}>, <"TB", {4,5,6}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"TB", {5,6,7}>, <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"TB", {1,2,3}>, <"TB", {5,6,7}>, <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"Tw", {4,5}>, <"TA", <{7,8}, {{1,2,3},{4,5,6}}>>, <"TB", {1,2,3}>, <"TB", {4,5,6}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"Tw", {5,6}>, <"Tw", {7,8}>, <"Pl", {{1,2,3,4},{5,6,7,8}}>, <"Pl", {{1,2,5,6},{3,4,7,8}}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"Tw", {5,6}>, <"Tw", {7,8}>, <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"Tw", {3,4}>, <"Tw", {5,6}>, <"TB", {5,6,7}>, <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"TB", {1,2,3}>, <"Tw", {5,6}>, <"TB", {5,6,7}>, <"CC", {{1,2,3,4},{5,6,7,8}}> *],
    [* <"Tw", {1,2}>, <"Tw", {4,5}>, <"Tw", {7,8}>, <"TA", <{7,8}, {{1,2,3},{4,5,6}}>>, <"TB", {1,2,3}>, <"TB", {4,5,6}> *]
    *];

/* import "bblocks.m" : AssociatedSubspace, SubspaceGraph, String;
   SubspaceGraphs := [ String(SubspaceGraph([AssociatedSubspace(b) : b in B])) : B in ExampleDiagrams ];
*/

SubspaceGraphs := [
    "6", "6(1)", "6(2)", "6(11)", "6(3)", "6(2(1))", "6(21)", "6(22)", "6(111)", "6([111])", "6(31)", "6(211)", "6(2(1)1)", "6(32)", "6(2(1)2)", "6(221)", "6(222)", "6([1111])", "6([111]1)", "6(3(1)1)", "6(2(1)11)", "6([311])", "6([111]2)", "6(32(1))", "6(3(2)1)", "6(2(1)2(1))", "6(2(1)21)", "6(3(2)2)", "6(2(1)22)", "6([11111])", "6([3(1)11])", "6([111]2(1))", "6(3(2(1))1)", "6(2(1)2(1)1)", "6([3(2)11])", "6(3(2)2(1))", "6(2(1)2(1)2)", "6([111111])", "6([3([11])11])", "6([3(2(1))11])", "6(3(2(1))2(1))", "6(2(1)2(1)2(1))"
    ];



// Primitive octad PGL-orbit by types
OctadDiagrams := [


    /*** Quartic curves ***/


    /* Codimension 0 */

    { /* (3) */
      {*
        {* {* *}^^56 *}^^36
      *}
    },


    /* Codimension 1 */

    { /* (2n) */
      {*
        {* {* "Tw" *}^^56 *}^^16,
        {* {* "Pl" *}^^56 *}^^20
      *}
    },
    { /* (2e) */
      {*
        {* {* "TA" *}^^56 *}^^30,
        {* {* "TB" *}^^56 *}^^6
      *}
    },


    /* Codimension 2 */

    { /* (1nn) */
      {*
        {* {* "Tw"^^2 *}^^56 *}^^8,
        {* {* "Pl", "Tw" *}^^56 *}^^16,
        {* {* "Pl"^^2 *}^^56 *}^^12
      *}
    },
    { /* (1=1) */
      {*
        {* {* "CC" *}^^56 *}^^2,
        {* {* "CB" *}^^56 *}^^16,
        {* {* "CA" *}^^56 *}^^18
      *}
    },
    { /* (2m) */
      {*
        {* {* "TB", "Tw" *}^^56 *}^^6,
        {* {* "TA", "Tw" *}^^56 *}^^10,
        {* {* "Pl", "TA" *}^^56 *}^^20
      *}
    },
    { /* (1ne) */
      {*
        {* {* "TB", "Tw" *}^^56 *}^^4,
        {* {* "Pl", "TB" *}^^56 *}^^2,
        {* {* "TA", "Tw" *}^^56 *}^^12,
        {* {* "Pl", "TA" *}^^56 *}^^18
      *}
    },
    { /* (1ee) */
      {*
        {* {* "TB"^^2 *}^^56 *}^^3,
        {* {* "TA", "TB" *}^^56 *}^^6,
        {* {* "TA"^^2 *}^^56 *}^^27
      *}
    },


    /* Codimension 3 */

    { /* (0nnn) */
      {*
        {* {* "Tw"^^3 *}^^56 *}^^4,
        {* {* "Pl", "Tw"^^2 *}^^56 *}^^12,
        {* {* "Pl"^^2, "Tw" *}^^56 *}^^12,
        {* {* "Pl"^^3 *}^^56 *}^^8
      *}
    },
    { /* (1---0) */
      {*
        {* {* "Pl", "Tw"^^2 *}^^56 *}^^24,
        {* {* "Pl"^^3 *}^^56 *}^^12
      *}
    },
    { /* (1=0n) */
      {*
        {* {* "CC", "Tw" *}^^56 *}^^2,
        {* {* "CB", "Tw" *}^^56 *}^^8,
        {* {* "CB", "Pl" *}^^56 *}^^8,
        {* {* "CA", "Pl" *}^^56 *}^^12,
        {* {* "CA", "Tw" *}^^56 *}^^6
      *}
    },
    { /* (0nne) */
      {*
        {* {* "TB", "Tw"^^2 *}^^56 *}^^2,
        {* {* "Pl", "TB", "Tw" *}^^56 *}^^4,
        {* {* "TA", "Tw"^^2 *}^^56 *}^^6,
        {* {* "Pl", "TA", "Tw" *}^^56 *}^^12,
        {* {* "Pl"^^2, "TA" *}^^56 *}^^12
      *}
    },
    { /* (1nm) */
      {*
        {* {* "TB", "Tw"^^2 *}^^56 *}^^4,
        {* {* "Pl", "TB", "Tw" *}^^56 *}^^2,
        {* {* "TA", "Tw"^^2 *}^^56 *}^^4,
        {* {* "Pl", "TA", "Tw" *}^^56 *}^^14, /* 6 + 8 */
        {* {* "Pl"^^2, "TA" *}^^56 *}^^12
      *}
    },
    { /* (1=0e) */
      {*
        {* {* "CC", "TB" *}^^56 *}^^2,
        {* {* "CB", "TB" *}^^56 *}^^4,
        {* {* "CB", "TA" *}^^56 *}^^12,
        {* {* "CA", "TA" *}^^56 *}^^18
      *}
    },
    { /* (1me) */
      {*
        {* {* "TB"^^2, "Tw" *}^^56 *}^^3,
        {* {* "TA", "TB", "Tw" *}^^56 *}^^4, /* 3 + 1 */
        {* {* "Pl", "TA", "TB" *}^^56 *}^^2,
        {* {* "TA"^^2, "Tw" *}^^56 *}^^9,
        {* {* "Pl", "TA"^^2 *}^^56 *}^^18
      *}
    },
    { /* (0nee) */
      {*
        {* {* "TB"^^2, "Tw" *}^^56 *},
        {* {* "Pl", "TB"^^2 *}^^56 *}^^2,
        {* {* "TA", "TB", "Tw" *}^^56 *}^^6,
        {* {* "TA"^^2, "Tw" *}^^56 *}^^9,
        {* {* "Pl", "TA"^^2 *}^^56 *}^^18
      *}
    },
    { /* (0eee) */
      {*
        {* {* "TA", "TB"^^2 *}^^56 *}^^9,
        {* {* "TA"^^3 *}^^56 *}^^27
      *}
    },


    /* Codimension 4 */

    { /* (0----0) */
      {*
        {* {* "Tw"^^4 *}^^56 *}^^4,
        {* {* "Pl"^^2, "Tw"^^2 *}^^56 *}^^24,
        {* {* "Pl"^^4 *}^^56 *}^^8
      *}
    },
    { /* (0---0n) */
      {*
        {* {* "Pl", "Tw"^^3 *}^^56 *}^^12,
        {* {* "Pl"^^2, "Tw"^^2 *}^^56 *}^^12,
        {* {* "Pl"^^3, "Tw" *}^^56 *}^^4,
        {* {* "Pl"^^4 *}^^56 *}^^8
      *}
    },
    { /* (0n=0n) */
      {*
        {* {* "CC", "Tw"^^2 *}^^56 *}^^2,
        {* {* "CA", "Tw"^^2 *}^^56 *}^^2,
        {* {* "CA", "Pl", "Tw" *}^^56 *}^^8,
        {* {* "CA", "Pl"^^2 *}^^56 *}^^8,
        {* {* "CB", "Pl", "Tw" *}^^56 *}^^8,
        {* {* "CB", "Tw"^^2 *}^^56 *}^^4,
        {* {* "CB", "Pl"^^2 *}^^56 *}^^4
      *}
    },
    { /* (0nnm) */
      {*
        {* {* "TB", "Tw"^^3 *}^^56 *}^^2,
        {* {* "Pl", "TB", "Tw"^^2 *}^^56 *}^^4,
        {* {* "TA", "Tw"^^3 *}^^56 *}^^2,
        {* {* "Pl", "TA", "Tw"^^2 *}^^56 *}^^8,  /* 4 + 4 */
        {* {* "Pl"^^2, "TA", "Tw" *}^^56 *}^^12, /* 4 + 8 */
        {* {* "Pl"^^3, "TA" *}^^56 *}^^8
      *}
    },
    { /* (Z=1) */
      {*
        {* {* "CC", "Tw"^^2 *}^^56 *}^^2,
        {* {* "CA", "Tw"^^2 *}^^56 *}^^6,
        {* {* "CA", "Pl"^^2 *}^^56 *}^^12,
        {* {* "CB", "Pl", "Tw" *}^^56 *}^^16
      *}
    },
    { /* (0---0e) */
      {*
        {* {* "Pl", "TB", "Tw"^^2 *}^^56 *}^^6,
        {* {* "Pl", "TA", "Tw"^^2 *}^^56 *}^^18,
        {* {* "Pl"^^3, "TA" *}^^56 *}^^12
      *}
    },
    { /* (1=0m) */
      {*
        {* {* "CC", "TB", "Tw" *}^^56 *}^^2,
        {* {* "CA", "TA", "Tw" *}^^56 *}^^6,
        {* {* "CA", "Pl", "TA" *}^^56 *}^^12,
        {* {* "CB", "TB", "Tw" *}^^56 *}^^4,
        {* {* "CB", "TA", "Tw" *}^^56 *}^^4,
        {* {* "CB", "Pl", "TA" *}^^56 *}^^8
      *}
    },
    { /* (0n=0e) */
      {*
        {* {* "CC", "TB", "Tw" *}^^56 *}^^2,
        {* {* "CA", "TA", "Tw" *}^^56 *}^^6,
        {* {* "CA", "Pl", "TA" *}^^56 *}^^12,
        {* {* "CB", "TB", "Tw" *}^^56 *}^^2,
        {* {* "CB", "Pl", "TB" *}^^56 *}^^2,
        {* {* "CB", "TA", "Tw" *}^^56 *}^^6,
        {* {* "CB", "Pl", "TA" *}^^56 *}^^6
      *}
    },
    { /* (1mm) */
      {*
        {* {* "TB"^^2, "Tw"^^2 *}^^56 *}^^3,
        {* {* "TA", "TB", "Tw"^^2 *}^^56 *}^^2,
        {* {* "Pl", "TA", "TB", "Tw" *}^^56 *}^^4,
        {* {* "TA"^^2, "Tw"^^2 *}^^56 *}^^3,
        {* {* "Pl", "TA"^^2, "Tw" *}^^56 *}^^12,
        {* {* "Pl"^^2, "TA"^^2 *}^^56 *}^^12
      *}
    },
    { /* (0nme) */
      {*
        {* {* "TB"^^2, "Tw"^^2 *}^^56 *},
        {* {* "Pl", "TB"^^2, "Tw" *}^^56 *}^^2,
        {* {* "TA", "TB", "Tw"^^2 *}^^56 *}^^4, /* 3 + 1 */
        {* {* "Pl", "TA", "TB", "Tw" *}^^56 *}^^2,
        {* {* "TA"^^2, "Tw"^^2 *}^^56 *}^^3,
        {* {* "Pl", "TA"^^2, "Tw" *}^^56 *}^^12, /* 6 + 6 */
        {* {* "Pl"^^2, "TA"^^2 *}^^56 *}^^12
      *}
    },
    { /* (0e=0e) */
      {*
        {* {* "CC", "TB"^^2 *}^^56 *}^^2,
        {* {* "CA", "TA"^^2 *}^^56 *}^^18,
        {* {* "CB", "TA"^^2 *}^^56 *}^^9,
        {* {* "CB", "TA", "TB" *}^^56 *}^^6,
        {* {* "CB", "TB"^^2 *}^^56 *}
      *}
    },
    { /* (0mee) */
      {*
        {* {* "TA", "TB"^^2, "Tw" *}^^56 *}^^7, /* 1 + 6 */
        {* {* "Pl", "TA", "TB"^^2 *}^^56 *}^^2,
        {* {* "TA"^^3, "Tw" *}^^56 *}^^9,
        {* {* "Pl", "TA"^^3 *}^^56 *}^^18
      *}
    },


    /* Codimension 5 */

    { /* ("CAVE) */
      {*
        {* {* "Pl", "Tw"^^4 *}^^56 *}^^4,
        {* {* "Pl"^^2, "Tw"^^3 *}^^56 *}^^16,
        {* {* "Pl"^^3, "Tw"^^2 *}^^56 *}^^8,
        {* {* "Pl"^^5 *}^^56 *}^^8
      *}
    },
    { /* (Z=0n) */
      {*
        {* {* "CC", "Tw"^^3 *}^^56 *}^^2,
        {* {* "CA", "Tw"^^3 *}^^56 *}^^2,
        {* {* "CA", "Pl", "Tw"^^2 *}^^56 *}^^4,
        {* {* "CA", "Pl"^^2, "Tw" *}^^56 *}^^4,
        {* {* "CA", "Pl"^^3 *}^^56 *}^^8,
        {* {* "CB", "Pl"^^2, "Tw" *}^^56 *}^^8,
        {* {* "CB", "Pl", "Tw"^^2 *}^^56 *}^^8
      *}
    },
    { /* (0---0m) */
      {*
        {* {* "Pl", "TB", "Tw"^^3 *}^^56 *}^^6,
        {* {* "Pl", "TA", "Tw"^^3 *}^^56 *}^^6,
        {* {* "Pl"^^2, "TA", "Tw"^^2 *}^^56 *}^^12,
        {* {* "Pl"^^3, "TA", "Tw" *}^^56 *}^^4,
        {* {* "Pl"^^4, "TA" *}^^56 *}^^8
      *}
    },
    { /* (0n=0m) */
      {*
        {* {* "CC", "TB", "Tw"^^2 *}^^56 *}^^2,
        {* {* "CA", "TA", "Tw"^^2 *}^^56 *}^^2,
        {* {* "CA", "Pl", "TA", "Tw" *}^^56 *}^^8, /* 4 + 4 */
        {* {* "CA", "Pl"^^2, "TA" *}^^56 *}^^8,
        {* {* "CB", "TB", "Tw"^^2 *}^^56 *}^^2,
        {* {* "CB", "Pl", "TB", "Tw" *}^^56 *}^^2,
        {* {* "CB", "TA", "Tw"^^2 *}^^56 *}^^2,
        {* {* "CB", "Pl", "TA", "Tw" *}^^56 *}^^6, /* 4 + 2 */
        {* {* "CB", "Pl"^^2, "TA" *}^^56 *}^^4
      *}
    },
    { /* (0nmm) */
      {*
        {* {* "TB"^^2, "Tw"^^3 *}^^56 *},
        {* {* "Pl", "TB"^^2, "Tw"^^2 *}^^56 *}^^2,
        {* {* "TA", "TB", "Tw"^^3 *}^^56 *}^^2,
        {* {* "Pl", "TA", "TB", "Tw"^^2 *}^^56 *}^^4,
        {* {* "TA"^^2, "Tw"^^3 *}^^56 *},
        {* {* "Pl", "TA"^^2, "Tw"^^2 *}^^56 *}^^6, /* 2 + 4 */
        {* {* "Pl"^^2, "TA"^^2, "Tw" *}^^56 *}^^12, /* 4 + 8 */
        {* {* "Pl"^^3, "TA"^^2 *}^^56 *}^^8
      *}
    },
    { /* (Z=0e) */
      {*
        {* {* "CC", "TB", "Tw"^^2 *}^^56 *}^^2,
        {* {* "CA", "TA", "Tw"^^2 *}^^56 *}^^6,
        {* {* "CA", "Pl"^^2, "TA" *}^^56 *}^^12,
        {* {* "CB", "Pl", "TB", "Tw" *}^^56 *}^^4,
        {* {* "CB", "Pl", "TA", "Tw" *}^^56 *}^^12
      *}
    },
    { /* (0m=0e) */
      {*
        {* {* "CC", "TB"^^2, "Tw" *}^^56 *}^^2,
        {* {* "CA", "TA"^^2, "Tw" *}^^56 *}^^6,
        {* {* "CA", "Pl", "TA"^^2 *}^^56 *}^^12,
        {* {* "CB", "TB"^^2, "Tw" *}^^56 *},
        {* {* "CB", "TA", "TB", "Tw" *}^^56 *}^^4, /* 3 + 1 */
        {* {* "CB", "TA"^^2, "Tw" *}^^56 *}^^3,
        {* {* "CB", "Pl", "TA", "TB" *}^^56 *}^^2,
        {* {* "CB", "Pl", "TA"^^2 *}^^56 *}^^6
      *}
    },
    { /* (0mme) */
      {*
        {* {* "TA", "TB"^^2, "Tw"^^2 *}^^56 *}^^5, /* 3 + 2 */
        {* {* "Pl", "TA", "TB"^^2, "Tw" *}^^56 *}^^4,
        {* {* "TA"^^3, "Tw"^^2 *}^^56 *}^^3,
        {* {* "Pl", "TA"^^3, "Tw" *}^^56 *}^^12,
        {* {* "Pl"^^2, "TA"^^3 *}^^56 *}^^12
      *}
    },


    /* Codimension 6 */

    { /* (BRAID) */
      {*
        {* {* "Pl"^^2, "Tw"^^4 *}^^56 *}^^12,
        {* {* "Pl"^^3, "Tw"^^3 *}^^56 *}^^16,
        {* {* "Pl"^^6 *}^^56 *}^^8
      *}
    },
    { /* (Z=Z) */
      {*
        {* {* "CC", "Tw"^^4 *}^^56 *}^^2,
        {* {* "CA", "Tw"^^4 *}^^56 *}^^2,
        {* {* "CA", "Pl"^^2, "Tw"^^2 *}^^56 *}^^8,
        {* {* "CA", "Pl"^^4 *}^^56 *}^^8,
        {* {* "CB", "Pl"^^2, "Tw"^^2 *}^^56 *}^^16
      *}
    },
    { /* (Z=0m) */
      {*
        {* {* "CC", "TB", "Tw"^^3 *}^^56 *}^^2,
        {* {* "CA", "TA", "Tw"^^3 *}^^56 *}^^2,
        {* {* "CA", "Pl", "TA", "Tw"^^2 *}^^56 *}^^4,
        {* {* "CA", "Pl"^^2, "TA", "Tw" *}^^56 *}^^4,
        {* {* "CA", "Pl"^^3, "TA" *}^^56 *}^^8,
        {* {* "CB", "Pl", "TB", "Tw"^^2 *}^^56 *}^^4,
        {* {* "CB", "Pl", "TA", "Tw"^^2 *}^^56 *}^^4,
        {* {* "CB", "Pl"^^2, "TA", "Tw" *}^^56 *}^^8
      *}
    },
    { /* (0m=0m) */
      {*
        {* {* "CC", "TB"^^2, "Tw"^^2 *}^^56 *}^^2,
        {* {* "CA", "TA"^^2, "Tw"^^2 *}^^56 *}^^2,
        {* {* "CA", "Pl", "TA"^^2, "Tw" *}^^56 *}^^8,
        {* {* "CA", "Pl"^^2, "TA"^^2 *}^^56 *}^^8,
        {* {* "CB", "TB"^^2, "Tw"^^2 *}^^56 *},
        {* {* "CB", "TA", "TB", "Tw"^^2 *}^^56 *}^^2,
        {* {* "CB", "TA"^^2, "Tw"^^2 *}^^56 *},
        {* {* "CB", "Pl", "TA"^^2, "Tw" *}^^56 *}^^4,
        {* {* "CB", "Pl", "TA", "TB", "Tw" *}^^56 *}^^4,
        {* {* "CB", "Pl"^^2, "TA"^^2 *}^^56 *}^^4
      *}
    },
    { /* (0mmm) */
      {*
        {* {* "TA", "TB"^^2, "Tw"^^3 *}^^56 *}^^3,
        {* {* "Pl", "TA", "TB"^^2, "Tw"^^2 *}^^56 *}^^6,
        {* {* "TA"^^3, "Tw"^^3 *}^^56 *},
        {* {* "Pl", "TA"^^3, "Tw"^^2 *}^^56 *}^^6,
        {* {* "Pl"^^2, "TA"^^3, "Tw" *}^^56 *}^^12,
        {* {* "Pl"^^3, "TA"^^3 *}^^56 *}^^8
        *}
    },

    /*** Hyperelliptic curves ***/


    /* Codimension 0 */

    { /* [3] */
      {*
        {* {* *}^^56 *},
        {* {* "Ln" *}^^56 *}^^35
      *}
    },


    /* Codimension 1 */

    { /* [2n] */
      {*
        {* {* "Tw" *}^^56 *},
        {* {* "Ln", "Tw" *}^^56 *}^^15,
        {* {* "Ln", "Pl" *}^^56 *}^^20
      *}
    },
    { /* [2e] */
      {*
        {* {* "TB" *}^^56 *},
        {* {* "Ln", "TB" *}^^56 *}^^5,
        {* {* "Ln", "TA" *}^^56 *}^^30
      *}
    },


    /* Codimension 2 */

    { /* [1nn] */
      {*
        {* {* "Tw"^^2 *}^^56 *},
        {* {* "Ln", "Tw"^^2 *}^^56 *}^^7, /* 1 + 6 */
        {* {* "Ln", "Pl", "Tw" *}^^56 *}^^16,
        {* {* "Ln", "Pl"^^2 *}^^56 *}^^12
      *}
    },
    { /* [1=1] */
      {*
        {* {* "CC" *}^^56 *},
        {* {* "Ln", "CC" *}^^56 *},
        {* {* "Ln", "CB" *}^^56 *}^^16,
        {* {* "Ln", "CA" *}^^56 *}^^18
      *}
    },
    { /* [2m] */
      {*
        {* {* "TB", "Tw" *}^^56 *},
        {* {* "Ln", "TB", "Tw" *}^^56 *}^^5,
        {* {* "Ln", "TA", "Tw" *}^^56 *}^^10,
        {* {* "Ln", "Pl", "TA" *}^^56 *}^^20
      *}
    },
    { /* [1ne] */
      {*
        {* {* "TB", "Tw" *}^^56 *},
        {* {* "Ln", "TB", "Tw" *}^^56 *}^^3,
        {* {* "Ln", "Pl", "TB" *}^^56 *}^^2,
        {* {* "Ln", "TA", "Tw" *}^^56 *}^^12, /* 3 + 9 */
        {* {* "Ln", "Pl", "TA" *}^^56 *}^^18
      *}
    },
    { /* [1ee] */
      {*
        {* {* "TB"^^2 *}^^56 *},
        {* {* "Ln", "TB"^^2 *}^^56 *}^^2,
        {* {* "Ln", "TA", "TB" *}^^56 *}^^6,
        {* {* "Ln", "TA"^^2 *}^^56 *}^^27 /* 9 + 18 */
      *}
    },


    /* Codimension 3 */

    { /* [0nnn] */
      {*
        {* {* "Tw"^^3 *}^^56 *},
        {* {* "Ln", "Tw"^^3 *}^^56 *}^^3,
        {* {* "Ln", "Pl", "Tw"^^2 *}^^56 *}^^12,
        {* {* "Ln", "Pl"^^2, "Tw" *}^^56 *}^^12,
        {* {* "Ln", "Pl"^^3 *}^^56 *}^^8
      *}
    },
    { /* [1=0n] */
      {*
        {* {* "CC", "Tw" *}^^56 *},
        {* {* "Ln", "CC", "Tw" *}^^56 *},
        {* {* "Ln", "CB", "Tw" *}^^56 *}^^8,
        {* {* "Ln", "CB", "Pl" *}^^56 *}^^8,
        {* {* "Ln", "CA", "Pl" *}^^56 *}^^12,
        {* {* "Ln", "CA", "Tw" *}^^56 *}^^6
      *}
    },
    { /* [0nne] */
      {*
        {* {* "TB", "Tw"^^2 *}^^56 *},
        {* {* "Ln", "TB", "Tw"^^2 *}^^56 *},
        {* {* "Ln", "Pl", "TB", "Tw" *}^^56 *}^^4,
        {* {* "Ln", "TA", "Tw"^^2 *}^^56 *}^^6,
        {* {* "Ln", "Pl", "TA", "Tw" *}^^56 *}^^12,
        {* {* "Ln", "Pl"^^2, "TA" *}^^56 *}^^12
      *}
    },
    { /* [1nm] */
      {*
        {* {* "TB", "Tw"^^2 *}^^56 *},
        {* {* "Ln", "TB", "Tw"^^2 *}^^56 *}^^3,
        {* {* "Ln", "Pl", "TB", "Tw" *}^^56 *}^^2,
        {* {* "Ln", "TA", "Tw"^^2 *}^^56 *}^^4, /* 1 + 3 */
        {* {* "Ln", "Pl", "TA", "Tw" *}^^56 *}^^14, /* 6 + 2 + 6 */
        {* {* "Ln", "Pl"^^2, "TA" *}^^56 *}^^12
      *}
    },
    { /* [1=0e] */
      {*
        {* {* "CC", "TB" *}^^56 *},
        {* {* "Ln", "CC", "TB" *}^^56 *},
        {* {* "Ln", "CB", "TB" *}^^56 *}^^4,
        {* {* "Ln", "CB", "TA" *}^^56 *}^^12,
        {* {* "Ln", "CA", "TA" *}^^56 *}^^18
      *}
    },
    { /* [1me] */
      {*
        {* {* "TB"^^2, "Tw" *}^^56 *},
        {* {* "Ln", "TB"^^2, "Tw" *}^^56 *}^^2,
        {* {* "Ln", "TA", "TB", "Tw" *}^^56 *}^^4, /* 3 + 1 */
        {* {* "Ln", "Pl", "TA", "TB" *}^^56 *}^^2,
        {* {* "Ln", "TA"^^2, "Tw" *}^^56 *}^^9, /* 3 + 6 */
        {* {* "Ln", "Pl", "TA"^^2 *}^^56 *}^^18 /* 6 + 12 */
      *}
    },
    { /* [0nee] */
      {*
        {* {* "TB"^^2, "Tw" *}^^56 *},
        {* {* "Ln", "Pl", "TB"^^2 *}^^56 *}^^2,
        {* {* "Ln", "TA", "TB", "Tw" *}^^56 *}^^6,
        {* {* "Ln", "TA"^^2, "Tw" *}^^56 *}^^9,
        {* {* "Ln", "Pl", "TA"^^2 *}^^56 *}^^18
      *}
    },


    /* Codimension 4 */

    { /* [0----0] */
      {*
        {* {* "Tw"^^4 *}^^56 *},
        {* {* "Ln", "Tw"^^4 *}^^56 *}^^3,
        {* {* "Ln", "Pl"^^2, "Tw"^^2 *}^^56 *}^^24,
        {* {* "Ln", "Pl"^^4 *}^^56 *}^^8
      *}
    },
    { /* [0n=0n] */
      {*
        {* {* "CC", "Tw"^^2 *}^^56 *},
        {* {* "Ln", "CC", "Tw"^^2 *}^^56 *},
        {* {* "Ln", "CA", "Tw"^^2 *}^^56 *}^^2, /* 1 + 1 */
        {* {* "Ln", "CA", "Pl", "Tw" *}^^56 *}^^8,
        {* {* "Ln", "CA", "Pl"^^2 *}^^56 *}^^8,
        {* {* "Ln", "CB", "Pl", "Tw" *}^^56 *}^^8,
        {* {* "Ln", "CB", "Tw"^^2 *}^^56 *}^^4,
        {* {* "Ln", "CB", "Pl"^^2 *}^^56 *}^^4
      *}
    },
    { /* [0nnm] */
      {*
        {* {* "TB", "Tw"^^3 *}^^56 *},
        {* {* "Ln", "TB", "Tw"^^3 *}^^56 *},
        {* {* "Ln", "Pl", "TB", "Tw"^^2 *}^^56 *}^^4,
        {* {* "Ln", "TA", "Tw"^^3 *}^^56 *}^^2,
        {* {* "Ln", "Pl", "TA", "Tw"^^2 *}^^56 *}^^8, /* 4 + 4 */
        {* {* "Ln", "Pl"^^2, "TA", "Tw" *}^^56 *}^^12, /* 4 + 8 */
        {* {* "Ln", "Pl"^^3, "TA" *}^^56 *}^^8
      *}
    },
    { /* [Z=1] */
      {*
        {* {* "CC", "Tw"^^2 *}^^56 *},
        {* {* "Ln", "CC", "Tw"^^2 *}^^56 *},
        {* {* "Ln", "CA", "Tw"^^2 *}^^56 *}^^6,
        {* {* "Ln", "CA", "Pl"^^2 *}^^56 *}^^12,
        {* {* "Ln", "CB", "Pl", "Tw" *}^^56 *}^^16
      *}
    },
    { /* [1=0m] */
      {*
        {* {* "CC", "TB", "Tw" *}^^56 *},
        {* {* "Ln", "CC", "TB", "Tw" *}^^56 *},
        {* {* "Ln", "CA", "TA", "Tw" *}^^56 *}^^6,
        {* {* "Ln", "CA", "Pl", "TA" *}^^56 *}^^12,
        {* {* "Ln", "CB", "TB", "Tw" *}^^56 *}^^4,
        {* {* "Ln", "CB", "TA", "Tw" *}^^56 *}^^4,
        {* {* "Ln", "CB", "Pl", "TA" *}^^56 *}^^8
      *}
    },
    { /* [0n=0e] */
      {*
        {* {* "CC", "TB", "Tw" *}^^56 *},
        {* {* "Ln", "CC", "TB", "Tw" *}^^56 *},
        {* {* "Ln", "CA", "TA", "Tw" *}^^56 *}^^6, /* 3 + 3 */
        {* {* "Ln", "CA", "Pl", "TA" *}^^56 *}^^12,
        {* {* "Ln", "CB", "TB", "Tw" *}^^56 *}^^2,
        {* {* "Ln", "CB", "Pl", "TB" *}^^56 *}^^2,
        {* {* "Ln", "CB", "TA", "Tw" *}^^56 *}^^6,
        {* {* "Ln", "CB", "Pl", "TA" *}^^56 *}^^6
      *}
    },
    { /* [1mm] */
      {*
        {* {* "TB"^^2, "Tw"^^2 *}^^56 *},
        {* {* "Ln", "TB"^^2, "Tw"^^2 *}^^56 *}^^2,
        {* {* "Ln", "TA", "TB", "Tw"^^2 *}^^56 *}^^2,
        {* {* "Ln", "Pl", "TA", "TB", "Tw" *}^^56 *}^^4,
        {* {* "Ln", "TA"^^2, "Tw"^^2 *}^^56 *}^^3, /* 1 + 2 */
        {* {* "Ln", "Pl", "TA"^^2, "Tw" *}^^56 *}^^12, /* 4 + 8 */
        {* {* "Ln", "Pl"^^2, "TA"^^2 *}^^56 *}^^12 /* 4 + 8 */
      *}
    },
    { /* [0e=0e] */
      {*
        {* {* "CC", "TB"^^2 *}^^56 *},
        {* {* "Ln", "CC", "TB"^^2 *}^^56 *},
        {* {* "Ln", "CA", "TA"^^2 *}^^56 *}^^18, /* 9 + 9 */
        {* {* "Ln", "CB", "TB"^^2 *}^^56 *},
        {* {* "Ln", "CB", "TA", "TB" *}^^56 *}^^6,
        {* {* "Ln", "CB", "TA"^^2 *}^^56 *}^^9
      *}
    },
    { /* [0nme] */
      {*
        {* {* "TB"^^2, "Tw"^^2 *}^^56 *},
        {* {* "Ln", "Pl", "TB"^^2, "Tw" *}^^56 *}^^2,
        {* {* "Ln", "TA", "TB", "Tw"^^2 *}^^56 *}^^4, /* 3 + 1 */
        {* {* "Ln", "Pl", "TA", "TB", "Tw" *}^^56 *}^^2,
        {* {* "Ln", "TA"^^2, "Tw"^^2 *}^^56 *}^^3,
        {* {* "Ln", "Pl", "TA"^^2, "Tw" *}^^56 *}^^12, /* 6 + 6 */
        {* {* "Ln", "Pl"^^2, "TA"^^2 *}^^56 *}^^12
      *}
    },


    /* Codimension 5 */

    { /* [Z=0n] */
      {*
        {* {* "CC", "Tw"^^3 *}^^56 *},
        {* {* "Ln", "CC", "Tw"^^3 *}^^56 *},
        {* {* "Ln", "CA", "Tw"^^3 *}^^56 *}^^2,
        {* {* "Ln", "CA", "Pl", "Tw"^^2 *}^^56 *}^^4,
        {* {* "Ln", "CA", "Pl"^^2, "Tw" *}^^56 *}^^4,
        {* {* "Ln", "CA", "Pl"^^3 *}^^56 *}^^8,
        {* {* "Ln", "CB", "Pl"^^2, "Tw" *}^^56 *}^^8,
        {* {* "Ln", "CB", "Pl", "Tw"^^2 *}^^56 *}^^8
      *}
    },
    { /* [0n=0m] */
      {*
        {* {* "CC", "TB", "Tw"^^2 *}^^56 *},
        {* {* "Ln", "CC", "TB", "Tw"^^2 *}^^56 *},
        {* {* "Ln", "CA", "TA", "Tw"^^2 *}^^56 *}^^2, /* 1 + 1 */
        {* {* "Ln", "CA", "Pl", "TA", "Tw" *}^^56 *}^^8, /* 4 + 2 + 2 */
        {* {* "Ln", "CA", "Pl"^^2, "TA" *}^^56 *}^^8,
        {* {* "Ln", "CB", "TB", "Tw"^^2 *}^^56 *}^^2,
        {* {* "Ln", "CB", "Pl", "TB", "Tw" *}^^56 *}^^2,
        {* {* "Ln", "CB", "TA", "Tw"^^2 *}^^56 *}^^2,
        {* {* "Ln", "CB", "Pl", "TA", "Tw" *}^^56 *}^^6, /* 4 + 2 */
        {* {* "Ln", "CB", "Pl"^^2, "TA" *}^^56 *}^^4
      *}
    },
    { /* [0nmm] */
      {*
        {* {* "TB"^^2, "Tw"^^3 *}^^56 *},
        {* {* "Ln", "Pl", "TB"^^2, "Tw"^^2 *}^^56 *}^^2,
        {* {* "Ln", "TA", "TB", "Tw"^^3 *}^^56 *}^^2,
        {* {* "Ln", "Pl", "TA", "TB", "Tw"^^2 *}^^56 *}^^4,
        {* {* "Ln", "TA"^^2, "Tw"^^3 *}^^56 *},
        {* {* "Ln", "Pl", "TA"^^2, "Tw"^^2 *}^^56 *}^^6, /* 2 + 4 */
        {* {* "Ln", "Pl"^^2, "TA"^^2, "Tw" *}^^56 *}^^12, /* 4 + 8 */
        {* {* "Ln", "Pl"^^3, "TA"^^2 *}^^56 *}^^8
      *}
    },
    { /* [Z=0e] */
      {*
        {* {* "CC", "TB", "Tw"^^2 *}^^56 *},
        {* {* "Ln", "CC", "TB", "Tw"^^2 *}^^56 *},
        {* {* "Ln", "CA", "TA", "Tw"^^2 *}^^56 *}^^6,
        {* {* "Ln", "CA", "Pl"^^2, "TA" *}^^56 *}^^12,
        {* {* "Ln", "CB", "Pl", "TB", "Tw" *}^^56 *}^^4,
        {* {* "Ln", "CB", "Pl", "TA", "Tw" *}^^56 *}^^12
      *}
    },
    { /* [0m=0e] */
      {*
        {* {* "CC", "TB"^^2, "Tw" *}^^56 *},
        {* {* "Ln", "CC", "TB"^^2, "Tw" *}^^56 *},
        {* {* "Ln", "CA", "TA"^^2, "Tw" *}^^56 *}^^6,
        {* {* "Ln", "CA", "Pl", "TA"^^2 *}^^56 *}^^12, /* 6 + 6 */
        {* {* "Ln", "CB", "TB"^^2, "Tw" *}^^56 *},
        {* {* "Ln", "CB", "TA", "TB", "Tw" *}^^56 *}^^4, /* 3 + 1 */
        {* {* "Ln", "CB", "TA"^^2, "Tw" *}^^56 *}^^3,
        {* {* "Ln", "CB", "Pl", "TA", "TB" *}^^56 *}^^2,
        {* {* "Ln", "CB", "Pl", "TA"^^2 *}^^56 *}^^6
      *}
    },


    /* Codimension 6 */

    { /* [Z=Z] */
      {*
        {* {* "CC", "Tw"^^4 *}^^56 *},
        {* {* "Ln", "CC", "Tw"^^4 *}^^56 *},
        {* {* "Ln", "CA", "Tw"^^4 *}^^56 *}^^2,
        {* {* "Ln", "CA", "Pl"^^2, "Tw"^^2 *}^^56 *}^^8,
        {* {* "Ln", "CA", "Pl"^^4 *}^^56 *}^^8,
        {* {* "Ln", "CB", "Pl"^^2, "Tw"^^2 *}^^56 *}^^16
      *}
    },
    { /* [Z=0m] */
      {*
        {* {* "CC", "TB", "Tw"^^3 *}^^56 *},
        {* {* "Ln", "CC", "TB", "Tw"^^3 *}^^56 *},
        {* {* "Ln", "CA", "TA", "Tw"^^3 *}^^56 *}^^2,
        {* {* "Ln", "CA", "Pl", "TA", "Tw"^^2 *}^^56 *}^^4,
        {* {* "Ln", "CA", "Pl"^^2, "TA", "Tw" *}^^56 *}^^4,
        {* {* "Ln", "CA", "Pl"^^3, "TA" *}^^56 *}^^8,
        {* {* "Ln", "CB", "Pl", "TB", "Tw"^^2 *}^^56 *}^^4,
        {* {* "Ln", "CB", "Pl", "TA", "Tw"^^2 *}^^56 *}^^4,
        {* {* "Ln", "CB", "Pl"^^2, "TA", "Tw" *}^^56 *}^^8
      *}
    },
    { /* [0m=0m] */
      {*
        {* {* "CC", "TB"^^2, "Tw"^^2 *}^^56 *},
        {* {* "Ln", "CC", "TB"^^2, "Tw"^^2 *}^^56 *},
        {* {* "Ln", "CA", "TA"^^2, "Tw"^^2 *}^^56 *}^^2, /* 1 + 1 */
        {* {* "Ln", "CA", "Pl", "TA"^^2, "Tw" *}^^56 *}^^8, /* 4 + 4 */
        {* {* "Ln", "CA", "Pl"^^2, "TA"^^2 *}^^56 *}^^8, /* 4 + 4 */
        {* {* "Ln", "CB", "TB"^^2, "Tw"^^2 *}^^56 *},
        {* {* "Ln", "CB", "TA", "TB", "Tw"^^2 *}^^56 *}^^2,
        {* {* "Ln", "CB", "TA"^^2, "Tw"^^2 *}^^56 *},
        {* {* "Ln", "CB", "Pl", "TA"^^2, "Tw" *}^^56 *}^^4,
        {* {* "Ln", "CB", "Pl", "TA", "TB", "Tw" *}^^56 *}^^4,
        {* {* "Ln", "CB", "Pl"^^2, "TA"^^2 *}^^56 *}^^4
      *}
    }

];

// The following procedure generates the full table in Appendix A.
procedure PrintFullTable()

    for D in ExampleDiagrams[[2..36]] do
        print "For diagram", D, "we get the following Cremona transformations:";
        print {* MinimalS8Representative(DiagramAction(D, M)) : M in CreAction *};
    end for;
    
end procedure;
