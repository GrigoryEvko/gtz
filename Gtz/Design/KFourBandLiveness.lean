import Gtz.Design.KFourChartClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The knife-band liveness layer

Three kernel facts that bound the selection search space of the K4 knife
band.

* `bandResidualWitnessPoint_hasStrictTree` completes the mandatory-point
  ritual for the canonical band inhabitant: the point outside Layer A and
  outside the exchange star carries a strictly dominating spanning tree,
  certified by the invariant pencil triple at the tree `{1, 3, 4}`.  Every
  future knife-band cell must fire at this point, and the designated tree
  data is now exact.
* `heavyPairRefuter_gap_oneTwoFive_det_pos` together with
  `heavyPairRefuter_gap_oneTwoFive_not_posDef` is the first kernel instance
  of the det-positive-not-definite phenomenon: the tree `{1, 2, 5}` at the
  dual refuter has the LARGEST determinant of all sixteen trees but two
  negative eigenvalues.  A determinant reading alone can never select the
  strict tree.
* `posDef_of_pencilGate_det_ge` is the gate collapse: against any positive
  definite competitor, a matrix with positive linear and quadratic pencil
  coefficients and a determinant at least as large is itself positive
  definite.  A determinant argmax over the full pencil gate is therefore
  positive definite as soon as ANY strict tree exists — the gate selection
  is equivalent to bare existence, and cannot produce it.
-/

namespace Gtz

open Matrix

/-! ## The canonical band inhabitant carries a strict tree -/

/-- Entrywise chart gap at the band inhabitant for the tree `{1, 3, 4}`. -/
theorem bandResidual_gap_oneThreeFour_eq :
    directionChartGap kFourDirection bandResidualWitnessPoint.mass
        bandResidualWitnessPoint.weight {1, 3, 4}
      = !![186, 3, -144; 3, 3, 1; -144, 1, 141] := by
  simp only [directionChartGap, bandResidualWitnessPoint_mass_eq,
    bandResidualWitnessPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply,
      bandResidualWitnessMass, bandResidualWitnessWeight] <;>
    norm_num

/-- **The band inhabitant is alive.**  The canonical chart point outside
Layer A and outside the exchange star carries a strictly dominating
spanning tree, with the invariant pencil values `D1 = 190`, `D2 = 20883`,
`D3 = 14151` at the tree `{1, 3, 4}`. -/
theorem bandResidualWitnessPoint_hasStrictTree :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection bandResidualWitnessPoint.mass
        bandResidualWitnessPoint.weight tree).PosDef := by
  refine ⟨{1, 3, 4}, by decide, ?_⟩
  rw [bandResidual_gap_oneThreeFour_eq]
  refine posDef_of_invariantPencilTriple 186 3 (-144) 3 1 141 ?_ ?_ ?_ <;>
    norm_num

/-! ## The det-positive-not-definite witness, in kernel -/

/-- Entrywise chart gap at the dual refuter for the tree `{1, 2, 5}`. -/
theorem heavyPairRefuter_gap_oneTwoFive_eq :
    directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {1, 2, 5}
      = !![-3181/60, 36, -59/60; 36, -3301/60, -59/60;
           -59/60, -59/60, 59/20] := by
  simp only [directionChartGap, heavyPairRefuterPoint_mass_eq,
    heavyPairRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply, heavyPairRefuterMass,
      maxEdgeRefuterWeight] <;>
    norm_num

/-- The `{1, 2, 5}` gap at the dual refuter has positive determinant. -/
theorem heavyPairRefuter_gap_oneTwoFive_det_pos :
    0 < (directionChartGap kFourDirection heavyPairRefuterPoint.mass
      heavyPairRefuterPoint.weight {1, 2, 5}).det := by
  rw [heavyPairRefuter_gap_oneTwoFive_eq]
  simp [Matrix.det_fin_three]
  norm_num

/-- The same gap is NOT positive definite: the vector `(1, -1, 0)` reads
the value `-5401/30`.  With the determinant lemma this is the exact
det-positive-not-definite witness of the knife band. -/
theorem heavyPairRefuter_gap_oneTwoFive_not_posDef :
    ¬ (directionChartGap kFourDirection heavyPairRefuterPoint.mass
      heavyPairRefuterPoint.weight {1, 2, 5}).PosDef := by
  intro hposDef
  have hne : (![1, -1, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcomp := congrFun hzero 0
    norm_num at hcomp
  have hvalue := hposDef.dotProduct_mulVec_pos hne
  rw [star_trivial, heavyPairRefuter_gap_oneTwoFive_eq] at hvalue
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hvalue
  norm_num at hvalue

/-! ## The gate collapse -/

/-- **The pencil-gate collapse.**  A symmetric matrix whose linear and
quadratic pencil coefficients are positive and whose determinant is at
least that of some positive definite competitor is itself positive
definite.  A determinant argmax over the full pencil gate therefore hosts
exactly when a strict tree exists at all: the gate selection is the bare
existence statement and cannot replace it. -/
theorem posDef_of_pencilGate_det_ge
    (aOneOne aOneTwo aOneThree aTwoTwo aTwoThree aThreeThree
      bOneOne bOneTwo bOneThree bTwoTwo bTwoThree bThreeThree : ℝ)
    (hcompetitor : (!![aOneOne, aOneTwo, aOneThree;
        aOneTwo, aTwoTwo, aTwoThree;
        aOneThree, aTwoThree, aThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef)
    (hgateOne : 0 < bOneOne + bTwoTwo + bThreeThree
        + bOneTwo + bOneThree + bTwoThree)
    (hgateTwo : 0 < 3 * bOneOne * bTwoTwo + 3 * bOneOne * bThreeThree
        + 3 * bTwoTwo * bThreeThree
        + 2 * bOneOne * bTwoThree + 2 * bTwoTwo * bOneThree
        + 2 * bThreeThree * bOneTwo
        - 3 * bOneTwo ^ 2 - 3 * bOneThree ^ 2 - 3 * bTwoThree ^ 2
        - 2 * bOneTwo * bOneThree - 2 * bOneTwo * bTwoThree
        - 2 * bOneThree * bTwoThree)
    (hdetGe : aOneOne * aTwoTwo * aThreeThree
          - aOneOne * aTwoThree ^ 2 - aOneTwo ^ 2 * aThreeThree
          + 2 * aOneTwo * aOneThree * aTwoThree
          - aOneThree ^ 2 * aTwoTwo
        ≤ bOneOne * bTwoTwo * bThreeThree
          - bOneOne * bTwoThree ^ 2 - bOneTwo ^ 2 * bThreeThree
          + 2 * bOneTwo * bOneThree * bTwoThree
          - bOneThree ^ 2 * bTwoTwo) :
    (!![bOneOne, bOneTwo, bOneThree;
        bOneTwo, bTwoTwo, bTwoThree;
        bOneThree, bTwoThree, bThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  have hcubic := invariantPencilCubic_pos_of_posDef aOneOne aOneTwo aOneThree
    aTwoTwo aTwoThree aThreeThree hcompetitor
  exact posDef_of_invariantPencilTriple bOneOne bOneTwo bOneThree bTwoTwo
    bTwoThree bThreeThree hgateOne hgateTwo (lt_of_lt_of_le hcubic hdetGe)

end Gtz
