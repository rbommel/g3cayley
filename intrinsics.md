Exported intrinsics
--

### Stable reduction type

```
intrinsic QuarticTypeFromOctad(f::RngMPolElt, p::RngIntElt :
  PrecMin := 100,
  PrecMax := 2^8*100,
  gbasis := false,
  LPrate := 10,
  randomize := true,
  AnalysisLevel := 0) -> MonStgElt, SetMulti
{Stable reduction type of a quartic via a Cayley octad approach}

intrinsic QuarticTypeFromDO(DO::SeqEnum :
  Prime := 0) -> SeqEnum
{Given Dixmier-Ohno invariants, it returns the reduction type at prime if
 they are defined over Q and Prime is non-zero. Otherwise, it returns two
 lists of compatible singularity types of these Dixmier-Ohno invariants
 (in Arnold classification).}

```

### Quartic/hyperelliptic models

```
intrinsic QuarticByReductionType(Type::MonStgElt, p::RngIntElt :
  Domain := [-p^4..p^4],
  Flat := false,
  K := Rationals()) -> RngMPolElt
{Return a plane quartic defined over K, with coefficients randomly chosen in Domain, such that its reduction modulo p is of the given Type.}

intrinsic G3HyperReductionType(Type::MonStgElt, p::RngIntElt :
  Domain := [-p^4..p^4],
  K := Rationals())  -> RngMPolElt
{ Return an hyperelliptic curve defined over Q, with coefficients randomly chosen in Domain, such that its reduction modulo p is of the given Type.}

intrinsic G3QuarticFromHyper(f::RngUPolElt, p::RngIntElt) -> RngMPolElt
{}
```

### Singular quartics

```
intrinsic HuiNormalForms(type::MonStgElt :
    Domain := [-1000..1000], Monic := false) -> RngMPolElt
{Returns a normal form for the given singularity type,
 as listed p. 107 in Hui 1979 Phd thesis.}

intrinsic  DixmierOhnoSingularityRelations(type::MonStgElt, DOinv::SeqEnum) -> SeqEnum
{Given a singularity type, it evaluates its stratum relations at the
 Dixmier-Ohno invariants in input.}
```


### Octad toolbox

```
intrinsic pAdicCayleyOctad(_eqC::RngMPolElt, p::RngIntElt  :
  Prec := 100,
  gbasis := false,
  LPrate := 10,
  randomize := true) -> SeqEnum
{Return a Cayley octad for the ternary quartic eqC defined in the completion field defined by the prime p}

intrinsic PluckerCoordinates(Octad::SeqEnum) -> SeqEnum, SeqEnum
{ On input of a Cayley octad, this function returns its 70-dimensional plucker vector and its corresponding ordered 4-partitions of \{1..8\} }

intrinsic PluckerValuations(PlOctad::SeqEnum) -> ModTupFldElt
{ On input of a plucker sequence, this function returns its 70-dimensional valuation vector }

intrinsic NormaliseValuationData(v1::ModTupFldElt : S := {1,2,3,4,5})->ModTupFldElt
{ Compute the valuation data of the normalised octad. The optional parameter S determines which points of the octad will be at the standard position (default: 1,2,3,4,5). }

intrinsic CayleyOctadDiagram(VlOctad::ModTupFldElt) -> List
{Compute an octad diagram}

intrinsic CayleyOctadPGLOrbit(O::SeqEnum) -> SeqEnum
{Orbit of an octad under PGL action, restricted to the ordered octad}

intrinsic CayleyOctadCremonaOrbit(O::SeqEnum) -> SeqEnum
{Orbit of an octad under Cremona action, restricted to the ordered octad}

intrinsic G3ThetaCharParity(i::RngIntElt) -> BoolElt
{The parity of the i-th thetaconstant (in the Aronhold numbering)}

intrinsic G3ThetaFromOctad(i::RngIntElt, Plck::SeqEnum) -> Any
{On input Plucker coordinates, return the i-th thetaconstant (in the Aronhold numbering)}
```
