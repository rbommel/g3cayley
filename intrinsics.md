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

intrinsic CayleyOctadDiagram(VlOctad::ModTupFldElt) -> List
{Compute an octad diagram}

intrinsic CayleyOctadPGLOrbit(O::SeqEnum) -> SeqEnum
{Orbit of an octad under PGL action, restricted to the ordered octad}

intrinsic CayleyOctadCremonaOrbit(O::SeqEnum) -> SeqEnum
{Orbit of an octad under Cremona action, restricted to the ordered octad}
```
