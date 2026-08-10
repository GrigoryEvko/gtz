import Gtz.Design.BarycentricCoverage
import Gtz.Design.TightLineRefutationFixtures

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The barycentric open cell is inhabited

`Gtz.TightBarycentricOpenCell` is the hypothesis of
`Gtz.tightLineOneSlotFamily_of_barycentricOpenCell` and of the coverage results
around it.  Nothing in the tree exhibited a design satisfying it, so every one of
those theorems was formally at risk of being VACUOUS.  This file closes that gap
with the landed `Gtz.freePairKillerDesign`.

THE COORDINATES MATTER, AND THEY ARE NOT THE RAW ATOMS.  The consumers all pass
`unitAxisTightVector design tightDir` and `unitAxisFreeAtom design`, that is the
base-frame transport, not `design.atom` itself.  Read on the raw atoms the cell
FAILS here: the free atom `4` is `(0,0,-1)`, so two of the nine coordinate
products are exactly zero.  Under the transport that atom becomes
`(11/15, 2/5, -2/15)` and all nine coordinates are strictly positive.  The base
frame is invertible precisely because the design is line-free.

THE NINE COORDINATES, in the transported frame with tight vector `(2,1,-1)`:
free atom `0` reads `5` and contributes `46/75, 7/50, 37/150`; free atom `1`
reads `2` and contributes `11/15, 1/5, 1/15`; free atom `2` reads `5` and
contributes `16/25, 3/25, 6/25`.

WHAT THIS DOES NOT DO.  It does not make the cell useful.
`Gtz.not_tightBarycentricOpenCell_of_not_tightLineOneSlotFamily` proves the cell
is disjoint from the no-one-slot stratum, and `freePairKillerDesign` inhabits the
cell exactly because it has five strictly dominating one-slot swaps.  So this is
a satisfiability certificate, not progress on the residual.
-/

namespace Gtz

open Matrix

/-- The base frame of the free-pair killer: its three base atoms as rows. -/
theorem freePairKillerDesign_unitAxisBaseFrame_eq :
    unitAxisBaseFrame freePairKillerDesign
      = !![2, 2, -1; -4, -3, -1; -1, 2, -1] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [unitAxisBaseFrame, freePairKillerDesign, freePairKillerAtom, Matrix.cons_val_two]

/-- Its inverse, the normalizer.  The base frame has determinant `15`. -/
theorem freePairKillerDesign_unitAxisBaseNormalizer_eq :
    unitAxisBaseNormalizer freePairKillerDesign
      = !![1 / 3, 0, -(1 / 3);
           -(1 / 5), -(1 / 5), 2 / 5;
           -(11 / 15), -(2 / 5), 2 / 15] := by
  rw [unitAxisBaseNormalizer, freePairKillerDesign_unitAxisBaseFrame_eq]
  refine Matrix.inv_eq_right_inv ?_
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_fin_three,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- The three free atoms in the transported frame.  None has a zero coordinate,
which is what makes the open cell reachable here at all. -/
theorem freePairKillerDesign_unitAxisFreeAtom_eq (freeIndex : Fin 3) :
    unitAxisFreeAtom freePairKillerDesign freeIndex
      = ![![23 / 15, 7 / 10, -(37 / 30)],
          ![11 / 15, 2 / 5, -(2 / 15)],
          ![8 / 5, 3 / 5, -(6 / 5)]] freeIndex := by
  rw [unitAxisFreeAtom, freePairKillerDesign_unitAxisBaseNormalizer_eq]
  fin_cases freeIndex <;>
    · ext coordinate
      fin_cases coordinate <;>
        norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply,
          freePairKillerDesign, freePairKillerAtom, freeThreeLabel, Matrix.cons_val_two]

/-- The tight direction `(1,-1,-2)` transports to `(2,1,-1)`. -/
theorem freePairKillerDesign_unitAxisTightVector_eq :
    unitAxisTightVector freePairKillerDesign ![1, -1, -2] = ![2, 1, -1] := by
  rw [unitAxisTightVector, unitAxisBaseNormalizer,
    Matrix.nonsing_inv_nonsing_inv _
      (unitAxisBaseFrame_det_isUnit freePairKillerDesign freePairKillerDesign_hasLinePattern),
    freePairKillerDesign_unitAxisBaseFrame_eq]
  ext coordinate
  fin_cases coordinate <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

/-- **THE OPEN CELL IS INHABITED.**  All nine transported barycentric
coordinates of `Gtz.freePairKillerDesign` are strictly positive, so
`Gtz.tightLineOneSlotFamily_of_barycentricOpenCell` and its coverage siblings are
not vacuous. -/
theorem freePairKillerDesign_tightBarycentricOpenCell :
    TightBarycentricOpenCell (unitAxisTightVector freePairKillerDesign ![1, -1, -2])
      (unitAxisFreeAtom freePairKillerDesign) := by
  intro freeIndex coordinate
  rw [tightBarycentricCoordinate, tightBarycentricReading,
    freePairKillerDesign_unitAxisTightVector_eq,
    freePairKillerDesign_unitAxisFreeAtom_eq]
  fin_cases freeIndex <;> fin_cases coordinate <;>
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

/-- The satisfiability statement in the form a later reader will want. -/
theorem exists_tightBarycentricOpenCell :
    ∃ (tight : Fin 3 → ℝ) (freeAtom : Fin 3 → Fin 3 → ℝ),
      TightBarycentricOpenCell tight freeAtom :=
  ⟨_, _, freePairKillerDesign_tightBarycentricOpenCell⟩

end Gtz
