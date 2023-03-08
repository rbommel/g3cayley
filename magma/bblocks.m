/***
 * Exported intrinsics.
 *
 * intrinsic PluckerCoordinates(Octad::SeqEnum) -> SeqEnum, SeqEnum
 *
 * intrinsic PluckerValuations(PlOctad::SeqEnum) -> ModTupFldElt
 *
 * intrinsic CayleyOctadDiagram(VlOctad::ModTupFldElt) -> List
 *
 ********************************************************************/

import "verbose.m" : MyBenchIndent, MyBenchStart, MyBenchStop;

 /* Global variables
 *******************/

// A fixed choice for the 4-partitions of {1..8}
KeySets := [
    {1,6,7,8}, {5,6,7,8},

    {2,5,7,8}, {4,6,7,8}, {4,5,6,8}, {3,5,6,8}, {1,3,6,8}, {1,2,6,8},
    {1,5,7,8}, {1,2,7,8}, {3,5,7,8}, {1,3,6,7}, {3,6,7,8}, {2,5,6,7},
    {1,5,6,8}, {1,4,6,8}, {1,2,6,7}, {4,5,7,8}, {1,3,7,8}, {2,6,7,8},
    {4,5,6,7}, {2,5,6,8}, {1,4,6,7}, {1,5,6,7}, {1,4,7,8}, {3,5,6,7},

    {1,2,3,8}, {2,4,5,8}, {1,3,5,7}, {1,3,4,7}, {2,3,5,8}, {1,4,5,8},
    {1,3,5,6}, {1,4,5,6}, {3,4,7,8}, {3,4,6,7}, {1,2,3,7}, {2,3,6,8},
    {3,4,5,7}, {2,4,6,8}, {1,2,3,6}, {2,3,7,8}, {1,2,5,8}, {1,4,5,7},
    {2,3,5,6}, {3,4,6,8}, {1,2,4,8}, {1,2,4,6}, {1,3,4,8}, {1,3,5,8},
    {1,3,4,6}, {2,4,5,7}, {2,3,5,7}, {1,2,5,7}, {2,3,6,7}, {1,2,4,7},
    {3,4,5,6}, {2,4,6,7}, {1,2,5,6}, {3,4,5,8}, {2,4,7,8}, {2,4,5,6},

    {1,3,4,5}, {1,2,3,5}, {1,2,3,4}, {2,3,4,5},
    {1,2,4,5}, {2,3,4,7}, {2,3,4,6}, {2,3,4,8}

    ];

V70 := VectorSpace(Rationals(), 70);

// The space E3
V8 := VectorSpace(GF(2), 8);
W8 := sub< V8 | [V8.1 + V8.i : i in [2..8]] >;
E3, rho := quo< W8 | [ W8!&+[V8.i : i in [1..8]] ] >;
E3_M := hom<E3->E3 | Matrix([ [ &+[GF(2)!Min(Integers()!v1[k], Integers()!v2[k]) : k in [1..8] ] where v1 := (E3.i @@ rho) where v2 := (E3.j @@ rho) : i in [1..6] ] : j in [1..6] ])>;

intrinsic PluckerCoordinates(Octad::SeqEnum) -> SeqEnum, SeqEnum
    { On input of a Cayley octad, this function returns its 70-dimensional plucker vector and its corresponding ordered 4-partitions of \{1..8\} }

    PlOctad := [ Determinant(Matrix( Octad[Setseq(KeySets[l])] )) : l in [1..#KeySets] ];

    return PlOctad, KeySets;
end intrinsic;

intrinsic PluckerValuations(PlOctad::SeqEnum) -> ModTupFldElt
    { On input of a plucker sequence, this function returns its 70-dimensional valuation vector }

    w := V70![ Valuation(pl) : pl in PlOctad];
    w := w - Min(Eltseq(w)) * Parent(w)![1 : i in [1..Rank(V70)]];

    return w;
end intrinsic;

function CayleyBuildingBlocks()

    TT := MyBenchStart(1, "Building Blocks Precomputations");

    Things := [* *];

    tt := MyBenchStart(2, "Defaults");
    v := AssociativeArray(); for i := 1 to #KeySets do v[KeySets[i]] := V70.i; end for;
    T := {
        { {1,2,3,4}, {1,2,5,6}, {3,5,7,8}, {4,6,7,8} },
        { {5,6,7,8}, {3,4,7,8}, {1,2,4,6}, {1,2,3,5} }
        };
    TP := {}; for p in Permutations({1..8}) do
        TP join:= {{ { {p[k] : k in K} : K in S} : S in T}};
        if #TP eq 630 then break; end if; /* a shortcut... */
    end for;
    N := [ [&+[v[J] : J in y] : y in x] : x in TP];
    Q := [ n[1] - n[2] : n in N ];
    B := Basis(Kernel( Transpose(Matrix(Q)) ));
    W := sub<V70 | [ V70!x : x in B ]>;
    MyBenchStop(2, "Defaults", tt);

    // Twins
    tt := MyBenchStart(2, "Twins");
    Tw := AssociativeArray();
    for s in Subsets({1..8}, 2) do
        va := &+[v[t] : t in KeySets | s subset t];
        vb := &+[v[t] : t in KeySets | #(s meet t) eq 0];
        assert va in W;
        assert vb in W;
        Tw[s] := [va, vb];
        Append(~Things, <"Tw", s>);
    end for;
    vprintf G3Cayley, 2:  "%o=> %o twin blocks;\n", MyBenchIndent(""), #Keys(Tw);
    MyBenchStop(2, "Twins", tt);

    // Planes
    tt := MyBenchStart(2, "Planes");
    S4 := { {T, {i : i in {1..8} | not(i in T)}} : T in KeySets };
    Pl := AssociativeArray();
    for s in S4 do
        va := &+[v[t] : t in s];
        vb := [];
        for s2 in s do
            vv :=
                &+[v[t] : t in KeySets | #(s2 meet t) eq 2] +
                2*&+[v[t] : t in KeySets | #(s2 meet t) eq 3] + 4*v[s2];
            Append(~vb, vv);
        end for;
        assert va in W;
        assert vb[1] in W;
        assert vb[2] in W;
        Pl[s] := [va] cat vb;
        Append(~Things, <"Pl", s>);
    end for;
    vprintf G3Cayley, 2:  "%o=> %o plane blocks;\n", MyBenchIndent(""), #Keys(Pl);
    MyBenchStop(2, "Planes", tt);

    // Type A
    tt := MyBenchStart(2, "Type A");
    ST := { < T, {V, {i : i in {1..8} | not(i in T join V)}} > : T in Subsets({1..8}, 2), V in Subsets({1..8}, 3) | #(T meet V) eq 0 };
    TA := AssociativeArray();
    for s in ST do
        va :=
            &+[v[t] : t in Subsets(&join([x : x in s[2]]) ,4)] +
            &+[v[{x} join y] : x in s[1], y in s[2]];
        vb :=
            &+[v[t] : t in Subsets({1..8}, 4) | s[1] subset t] +
            &+[v[{x} join y] : x in s[1], y in s[2]];
        vc := [];
        for x in s[2] do
            y := [z : z in s[2] | z ne x][1];
            vv :=
                &+[v[t] : t in Subsets({1..8}, 4) | #(x meet t) eq 2] +
                2*&+[v[t] : t in Subsets({1..8}, 4) | x subset t] +
                &+[v[t] : t in Subsets(s[1] join x, 4)] +
                &+[v[s[1] join {a,b}] : a in x, b in y];
            Append(~vc, vv);
        end for;
        assert va in W;
        assert vb in W;
        assert vc[1] in W;
        assert vc[2] in W;
        TA[s] := [va, vb] cat vc;
        Append(~Things, <"TA", s>);
    end for;
    vprintf G3Cayley, 2:  "%o=> %o Type A blocks;\n", MyBenchIndent(""), #Keys(TA);
    MyBenchStop(2, "Type A", tt);

    // Type B
    tt := MyBenchStart(2, "Type B");
    TB := AssociativeArray();
    for s in Subsets({1..8}, 3) do
        r := {i : i in {1..8} | not(i in s)};
        va :=
            &+[ &+[ v[t] : t in KeySets | #(t meet (r join {x})) eq 4 ]  : x in s];
        vb :=
            &+[v[s join {i}] : i in r] +
            &+[ (#(t meet s) - 1)*v[t] : t in KeySets | #(t meet s) ge 2 ] ;
        vc :=
            &+[v[s join {i}] : i in r] +
            &+[v[t] : t in Subsets(r, 4)];
        assert va in W;
        assert vb in W;
        assert vc in W;
        TB[s] := [va, vb, vc];
        Append(~Things, <"TB", s>);
    end for;
    vprintf G3Cayley, 2:  "%o=> %o Type B blocks;\n", MyBenchIndent(""), #Keys(TB);
    MyBenchStop(2, "Type B", tt);

    // Candy A
    tt := MyBenchStart(2, "Candy A");
    S2222 := {};
    CA := AssociativeArray();
    for T in S4 do
        W1 := Random(T);
        W2 := [x : x in T | x ne W1][1];
        for S1 in Subsets(W1, 2), S2 in Subsets(W2, 2) do
            Include(~S2222, {{S1, {x : x in W1 | not(x in S1)}}, {S2, {x : x in W2 | not(x in S2)}}});
        end for;
    end for;
    for s in S2222 do
        va := [];
        vb := [];
        for x in s do
            x2 := [y : y in s | y ne x][1];
            vvb :=
                &+[ &+[v[t] : t in KeySets | y subset t] : y in x] +
                &+[ v[t] : t in KeySets | { #(t meet y) : y in x } eq {1} and { #(t meet y) : y in x2 } eq {0, 2} ];
            assert vvb in W;
            Append(~vb, vvb);
            for y in x do
                y2 := [z : z in x | z ne y][1];
                vva :=
                    &+[ v[t] : t in KeySets | y subset t] +
                    &+[v[t] : t in KeySets | #(y2 meet t) eq 0] +
                    &+[v[t] : t in KeySets | #(t meet y) eq 1 and #(t meet y2) eq 1 and { #(t meet z) : z in x2 } eq {0, 2} ] ;
                assert vva in W;
                Append(~va, vva);
            end for;
        end for;
        CA[s] := va cat vb;
        Append(~Things, <"CA", s>);
    end for;
    vprintf G3Cayley, 2:  "%o=> %o Candy A blocks;\n", MyBenchIndent(""), #Keys(CA);
    MyBenchStop(2, "Candy A", tt);

    // Candy B
    tt := MyBenchStart(2, "Candy B");
    CB := AssociativeArray();
    for s in ST do
        va :=
            &+[v[t] : t in KeySets | { #(t meet v) : v in s[2] } eq {1,3} ] +
            &+[ &+[v[t] : t in Subsets(y join s[1],4) ] : y in s[2]];
        vb := [];
        vc := [];
        for x in s[2] do
            y := [t : t in s[2] | t ne x][1];
            vvb :=
                &+[v[t] : t in KeySets | s[1] subset t] +
                3*&+[v[t] : t in KeySets | #(t meet x) eq 3] -
                &+[v[t] : t in KeySets | #(t meet x) eq 3 and #(t meet y) eq 1] +
                &+[v[t] : t in KeySets | #(t meet x) eq 2 and #(t meet y) eq 1] +
                2*&+[v[t] : t in KeySets | #(t meet x) eq 2 and s[1] subset t] ;
            assert vvb in W;
            vvc :=
                &+[(#(t meet x) - 1)*v[t] : t in KeySets | #(t meet x) ge 2] +
                &+[v[t] : t in KeySets | { #(t meet v) : v in s[2] } eq {1,3} ] +
                &+[v[t] : t in Subsets(x join s[1], 4)];
            assert vvc in W;
            Append(~vb, vvb);
            Append(~vc, vvc);
        end for;
        assert va in W;
        CB[s] := [va] cat vb cat vc;
        Append(~Things, <"CB", s>);
    end for;
    vprintf G3Cayley, 2:  "%o=> %o Candy B blocks;\n", MyBenchIndent(""), #Keys(CB);
    MyBenchStop(2, "Candy B", tt);

    // Candy C
    tt := MyBenchStart(2, "Candy C");
    CC := AssociativeArray();
    for s in S4 do
        va := [];
        vb := [];
        for x in s do
            y := [t : t in s | t ne x][1];
            vva :=
                3*v[x] +
                v[y] +
                &+[v[t] : t in KeySets | #(x meet t) eq 3];
            assert vva in W;
            vvb :=
                &+[ (#(t meet x) - 1)*v[t] : t in KeySets | #(t meet x) ge 2 ] +
                &+[ v[t] : t in KeySets | #(t meet x) ge 3 ] +
                2*v[x];
            assert vvb in W;
            Append(~va, vva);
            Append(~vb, vvb);
        end for;
        CC[s] := va cat vb;
        Append(~Things, <"CC", s>);
    end for;
    vprintf G3Cayley, 2:  "%o=> %o Candy C blocks;\n", MyBenchIndent(""), #Keys(CC);
    MyBenchStop(2, "Candy C", tt);

    // Line
    tt := MyBenchStart(2, "Line");
    Ln := AssociativeArray();
    for s in S4 do
        va := [];
        for x in s do
            vva :=
                &+[v[t] : t in KeySets | #(t meet x) eq 3] +
                2*v[x];
            assert(vva in W);
            Append(~va, vva);
        end for;
        Ln[s] := va;
        Append(~Things, <"Ln", s>);
    end for;
    vprintf G3Cayley, 2:  "%o=> %o Line blocks;\n", MyBenchIndent(""), #Keys(Ln);
    MyBenchStop(2, "Line", tt);

    vprintf G3Cayley, 1:  "%o=> %o Building blocks;\n", MyBenchIndent(""), #Things;

    MyBenchStop(1, "Building Blocks Precomputations", TT);

    return Things,
        [ Tw,  Pl,  TA, TB,  CA, CB, CC,  Ln ],
        W;

end function;

function AssociatedSubspace(T)

    if T[1] eq "Tw" then
        return sub< E3 | [rho(&+[V8.i : i in T[2]])] >;
    elif T[1] eq "Pl" then
        return sub< E3 | [rho(&+[V8.i : i in p]) : p in T[2]] >;
    elif T[1] eq "TA" then
        return sub< E3 | [rho(V8.s + &+[V8.i : i in t]) : s in T[2][1], t in T[2][2]] >;
    elif T[1] eq "TB" then
        return sub< E3 | [rho(&+[V8.i : i in p]) : p in Subsets(T[2], 2)] >;
    elif T[1] eq "CA" then
        q1 := [ q : q in T[2] | 1 in &join q ][1];
        q2 := [ q : q in T[2] | q ne q1 ][1];
        p11, p12 := Explode([ p : p in q1 ]);
        p21, p22 := Explode([ p : p in q2 ]);
        return sub< E3 | [ rho(&+[V8.i : i in p11]), rho(&+[V8.i : i in p12]), rho(&+[V8.i : i in p21] + V8.Min(p11) + V8.Min(p12)) ] >;
    elif T[1] eq "CB" then
        t1 := [ t : t in T[2][2] | Min(&join T[2][2]) in t ][1];
        return sub< E3 | [rho(&+[V8.i : i in T[2][1]])] cat [rho(&+[V8.i : i in S]) : S in Subsets(t1, 2)] >; 
    elif T[1] eq "CC" then
        q1 := [ q : q in T[2] | 1 in q ][1];
        return sub< E3 | [rho(&+[V8.i : i in S]) : S in Subsets(q1, 2)] >;
    else
        assert(false);
    end if;
     
end function;

forward IsCompatible;

function IsCompatible(T1, T2)

    if T1[1] eq "Tw" then
        if T2[1] eq "Tw" then
            return #(T1[2] meet T2[2]) eq 0;
        elif T2[1] in {"Pl", "CC", "Ln"} then
            return { #(T1[2] meet p) : p in T2[2] } eq { 0, 2 };
        elif T2[1] eq "TA" then
            return #(T1[2] meet T2[2][1]) eq 2 or { #(T1[2] meet t) : t in T2[2][2] } eq { 0, 2 };
        elif T2[1] eq "TB" then
            return #(T1[2] meet T2[2]) in {0, 2};
        elif T2[1] eq "CA" then
            return { { #(T1[2] meet p) : p in q } : q in T2[2] } eq { {0}, {0,2} };
        elif T2[1] eq "CB" then
            return { #(T1[2] meet t) : t in T2[2][2] } in { {0}, { 0, 2 } };
        end if;

    elif T1[1] eq "Pl" then
        if T2[1] eq "Pl" then
            return { #(p1 meet p2) : p1 in T1[2], p2 in T2[2] } eq { 2 };
        elif T2[1] eq "TA" then
            return { { #(p meet t) : t in T2[2][2]} : p in T1[2] } in { { {1}, {2} }, { { 0, 3 } } };
        elif T2[1] eq "TB" then
            return { #(p meet T2[2]) : p in T1[2] } eq { 0, 3 };
        elif T2[1] eq "CA" then
            return { { { #(pa meet pl) : pa in q } : q in T2[2] } : pl in T1[2] } in { { { {2}, {0} } }  ,  { { { 2, 0 }, {1} }  } };
        elif T2[1] eq "CB" then
            return { { #(p meet t) : t in T2[2][2]} : p in T1[2] } eq { {1, 3}, {0, 2} };
        elif T2[1] eq "CC" then
            return T1[2] eq T2[2];
        elif T2[1] eq "Ln" then
            return { #(p1 meet p2) : p1 in T1[2], p2 in T2[2] } eq { 1, 3 };
        else
            return IsCompatible(T2, T1);
        end if;

    elif T1[1] eq "TA" then
        if T2[1] eq "TA" then
            return { { #(t1 meet t2) : t1 in T1[2][2] } : t2 in T2[2][2] } eq { {0, 1}, {1, 2} } and { { #(t1 meet t2) : t1 in T2[2][2] } : t2 in T1[2][2] } eq { {0, 1}, {1, 2} };
        elif T2[1] eq "TB" then
            return { #(T2[2] meet t) : t in T1[2][2] } eq { 0, 3 };
        elif T2[1] eq "CA" then
            return { { { #(t meet p) : t in T1[2][2] } : p in q } : q in T2[2] } eq { { {0, 2} }  , { { 0 }, { 1 } } };
        elif T2[1] eq "CB" then
            return {* #(t1 meet t2) : t1 in T1[2][2], t2 in T2[2][2] *} eq {* 0, 0, 1, 3 *};
        elif T2[1] eq "CC" then
            return false;
        elif T2[1] eq "Ln" then
            return { { #(p meet t) : t in T1[2][2]} : p in T2[2] } eq  { {0,2}, {1,3} };
        else
            return IsCompatible(T2, T1);
        end if;

    elif T1[1] eq "TB" then
        if T2[1] eq "TB" then
            return #(T1[2] meet T2[2]) eq 0;
        elif T2[1] eq "CA" then
            return false;
        elif T2[1] eq "CB" then
            return T1[2] in T2[2][2];
        elif T2[1] eq "CC" then
            return true in { T1[2] subset p : p in T2[2] };
        elif T2[1] eq "Ln" then
            return { #(p meet T1[2]) : p in T2[2] } eq { 0, 3 };
        else
            return IsCompatible(T2, T1);
        end if;

    elif T1[1] eq "CA" then
        if T2[1] in {"CA", "CB", "CC"} then
            return false;
        elif T2[1] eq "Ln" then
            return { { { #(p meet t) : p in q} : q in T1[2]} : t in T2[2] } eq  { { { 0, 2 } } };
        else
            return IsCompatible(T2, T1);
        end if;

    elif T1[1] eq "CB" then
        if T2[1] in {"CB", "CC"} then
            return false;
        elif T2[1] eq "Ln" then
            return { { #(p meet t) : t in T1[2][2]} : p in T2[2] } eq { {0, 3} };
        else
            return IsCompatible(T2, T1);
        end if;

    elif T1[1] eq "CC" then
        if T2[1] eq "CC" then
            return false;
        elif T2[1] eq "Ln" then
            return T1[2] eq T2[2];
        else
            return IsCompatible(T2, T1);
        end if;

    elif T1[1] eq "Ln" then
        if T2[1] eq "Ln" then
            return false;
        else
            return IsCompatible(T2, T1);
        end if;
    end if;

    assert(false);

    return false;

end function;


// The data store for building blocks. Do not access directly!
G3CayleyBBlocks := NewStore();

intrinsic CayleyOctadDiagram(VlOctad::ModTupFldElt) -> List
    {Compute an octad diagram}

    TT := MyBenchStart(1, "Cayley Building Blocks");

    /* Are computations already done ? */
    bool, Things := StoreIsDefined(G3CayleyBBlocks, "Things");
    if bool then
        _, Blocks := StoreIsDefined(G3CayleyBBlocks, "Blocks");
        _, ValLat := StoreIsDefined(G3CayleyBBlocks, "ValLat");
    else
        Things, Blocks, ValLat := CayleyBuildingBlocks();
        StoreSet(G3CayleyBBlocks, "Things", Things);
        StoreSet(G3CayleyBBlocks, "Blocks", Blocks);
        StoreSet(G3CayleyBBlocks, "ValLat", ValLat);
    end if;
    Tw,  Pl,  TA, TB,  CA, CB, CC,  Ln := Explode(Blocks);

    /* Normalizations, if needed */
    w := VlOctad - Min(Eltseq(VlOctad)) * Parent(VlOctad)![1 : i in [1..Rank(Parent(VlOctad))]];

    /* Smooth curves */
    if w eq 0 then
        MyBenchStop(1, "Cayley Building Blocks", TT);
        return [**];
    end if; // Catch smooth curves

    tt := MyBenchStart(2, "compatible Building Blocks");
    PotentialThings := {Integers() |};
    GoodVectors := [ [] : i in [1..#Things]];
    for i := 1 to #Things do
        t := Things[i];
        GoodVectors[i] := [];
        for v in (eval t[1])[t[2]] do
            if Min(Eltseq(w - v)) lt 0 then continue v; end if;
            Include(~PotentialThings, i);
            Include(~GoodVectors[i], v);
        end for;
    end for;
    vprintf G3Cayley, 2:  "%o=> %o building blocks;\n", MyBenchIndent(""), #PotentialThings;
    MyBenchStop(2, "Compatible Building Blocks", tt);

    tt := MyBenchStart(2, "compatible subsets");
    CompatibleSubsets := { { Integers() | } };
    for i in PotentialThings do
        for S in CompatibleSubsets do
            for j in S do
                if not(IsCompatible(Things[i], Things[j])) then
                    continue S;
                end if;
            end for;
            Include(~CompatibleSubsets, S join {i});
        end for;
    end for;
    vprintf G3Cayley, 2:  "%o=> %o subsets;\n", MyBenchIndent(""), #CompatibleSubsets;
    MyBenchStop(2, "Compatible subsets", tt);

    tt := MyBenchStart(2, "subset candidates");
    PotentialSubsets := [ Parent({1}) | ];
    Subspaces := [ Parent(V70) | ];
    for S in CompatibleSubsets do
        W := sub< V70 | &cat[GoodVectors[i] : i in S ]>;
        assert Dimension(W) eq # &cat[GoodVectors[i] : i in S ];
        if w in W then
            Append(~Subspaces, W);
            Append(~PotentialSubsets, S);
        end if;
    end for;
    vprintf G3Cayley, 2:  "%o=> %o candidates;\n", MyBenchIndent(""), #Subspaces;

    assert(#Subspaces gt 0);
    W := &meet Subspaces;
    assert W in Subspaces;
    MyBenchStop(2, "subset candidates", tt);

    tt := MyBenchStart(2, "a linear filtering");
    Sols := [];
    CandidateSubspaces := [ i : i in [1..#Subspaces] | W eq Subspaces[i] ];
    for i in CandidateSubspaces do
        crd, nulspc := Solution(Matrix([Subspaces[i].k : k in [1..Dimension(Subspaces[i])]]), w);
        assert Dimension(nulspc) eq 0;
        if Min(Eltseq(crd)) ge 0 then Append(~Sols, i); end if;
    end for;
    vprintf G3Cayley, 2:  "%o=> %o solutions;\n", MyBenchIndent(""), #Sols;
    assert #Sols eq 1;
    MyBenchStop(2, "A linear filtering", tt);

    MyBenchStop(1, "Cayley Building Blocks", TT);

    return [* Things[k] : k in PotentialSubsets[Sols[1]] *];
end intrinsic;