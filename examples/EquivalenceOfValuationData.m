/* In this file, we verify the claimed equivalence relations between different
   valuation data for alpha, chi, line and phi blocks.

   Moreover, we check that that the equivalence classes are exhaustive for the
   situation in which 5 points are in standard position.

   This script assumes that the spec file "g3cayley/magma/spec" is loaded
   at magma startup (for example in the .magmarc file)
*/

_, BuildingBlocks := CayleyOctadDiagram(Vector([Rationals()|0 : i in [1..70]]));

for B in BuildingBlocks do
	for Bvectors in B do
		NormalisedOrbitFirstVector := [NormaliseValuationData(Bvectors[1] : S := S) : S in Subsets({1..8}, 5)];
		assert({Index(Bvectors, v) : v in NormalisedOrbitFirstVector} eq {1..#Bvectors});
	end for;
end for;
