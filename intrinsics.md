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
```

### Quartic/hyperelliptic models

```
intrinsic QuarticByReductionType(Type::MonStgElt, p::RngIntElt :
  Domain := [-p^4..p^4],
  Flat := false,
  K := Rationals()) -> RngMPolElt

intrinsic G3HyperReductionType(Type::MonStgElt, p::RngIntElt :
  Domain := [-p^4..p^4],
  K := Rationals())  -> RngMPolElt

intrinsic G3QuarticFromHyper(f::RngUPolElt, p::RngIntElt) -> RngMPolElt
```

### Octad toolbox

```
intrinsic pAdicCayleyOctad(_eqC::RngMPolElt, p::RngIntElt  :
  Prec := 100,
  gbasis := false,
  LPrate := 10,
  randomize := true) -> SeqEnum

intrinsic PluckerCoordinates(Octad::SeqEnum) -> SeqEnum, SeqEnum

intrinsic PluckerValuations(PlOctad::SeqEnum) -> ModTupFldElt

intrinsic CayleyOctadDiagram(VlOctad::ModTupFldElt) -> List


intrinsic CayleyOctadPGLOrbit(O::SeqEnum) -> SeqEnum

intrinsic CayleyOctadCremonaOrbit(O::SeqEnum) -> SeqEnum
```
