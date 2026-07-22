/-
# Audit: axiom hygiene for everything claimed proven (FX discipline)

Every theorem this project calls PROVEN is listed here with `#print axioms`, so
each build displays exactly what it rests on. Expected axiom set for
Mathlib-backed proofs: `propext`, `Classical.choice`, `Quot.sound` — and NOTHING
else. In particular `sorryAx` appearing for any theorem listed here is a broken
promise; roadmap statements carrying `sorry` are deliberately NOT listed.

Update this file in the same commit that completes a proof.
-/
import Gtz.BhatiaDavis
import Gtz.Sanity

#print axioms Gtz.bhatiaDavis_telescope
#print axioms Gtz.exists_pair_mul_le_neg_one
#print axioms Gtz.posSemidef_atomMatrix
#print axioms Gtz.Dominates.mono
#print axioms Gtz.unitDesign
#print axioms Gtz.gtzWeighted_one_one
