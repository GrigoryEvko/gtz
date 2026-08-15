import Gtz.Quantitative.WeightedTripleCriterion
import Gtz.Wave.BalancedInvolutionClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The balanced Wave closure in weighted-design coordinates

`BalancedInvolutionClosure` proves the sharp `1/6` block floor for every
balanced six-by-three Parseval frame.  This module connects that frame theorem
to the actual `(6,3)` cell.

For a weighted design, the rows of `scaledAtomRows` are a Parseval frame and
their Gram is `projectionOfDesign`.  Hence the Wave balance condition is exactly
uniform projection share `atomShare = 1/2`.  We first export the genuinely
weight-independent conclusion: some principal triple of `projectionOfDesign`
lies above the flat `1/6` diagonal.  Whenever the true weights on that selected
triple are at most `1/6`, the landed projection-block dictionary turns the flat
certificate into `Dominates`.

The final global-light corollary is deliberately presented only as a direct
coordinate adapter.  Since six positive weights sum to one, assuming all six
are at most `1/6` forces them all to equal `1/6`; it does not enlarge the landed
equal-share cell.  The reusable new interface is the flat projection block,
which remains valid for arbitrary weights with uniform share.
-/

namespace Gtz

open Matrix

/-! ## 1. The scaled design rows satisfy the Wave frame laws -/

/-- The scaled rows of any weighted design satisfy the bilinear Parseval law
used by the Wave modules. -/
theorem scaledAtomRows_frameLaw {size rank : ℕ} (design : WeightedDesign size rank) :
    ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (scaledAtomRows design slot ⬝ᵥ probe)
          * (scaledAtomRows design slot ⬝ᵥ direction)) = probe ⬝ᵥ direction := by
  intro probe direction
  change (scaledAtomRows design *ᵥ probe) ⬝ᵥ (scaledAtomRows design *ᵥ direction)
    = probe ⬝ᵥ direction
  calc
    (scaledAtomRows design *ᵥ probe) ⬝ᵥ (scaledAtomRows design *ᵥ direction)
        = probe ⬝ᵥ ((scaledAtomRows design)ᵀ *ᵥ
            (scaledAtomRows design *ᵥ direction)) := by
          rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
    _ = probe ⬝ᵥ (((scaledAtomRows design)ᵀ * scaledAtomRows design) *ᵥ direction) := by
      rw [Matrix.mulVec_mulVec]
    _ = probe ⬝ᵥ direction := by
      rw [transpose_mul_scaledAtomRows, Matrix.one_mulVec]

/-- The Wave atom Gram of the scaled rows is the projection form entrywise. -/
theorem atomGram_scaledAtomRows {size rank : ℕ} (design : WeightedDesign size rank)
    (rowIndex colIndex : Fin size) :
    atomGram (fun slot => scaledAtomRows design slot) rowIndex colIndex
      = projectionOfDesign design rowIndex colIndex := by
  rw [atomGram, scaledAtomRows_row, scaledAtomRows_row, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, projectionOfDesign_apply]
  ring

/-! ## 2. The balanced block in projection coordinates -/

/-- Every uniform-share `(6,3)` design has a principal projection block above
the flat `1/6` diagonal.  The design weights are otherwise unrestricted. -/
theorem exists_flatProjectionTriple_of_uniformShare
    (design : WeightedDesign 6 3)
    (hshare : ∀ atomIndex, atomShare design atomIndex = 1 / 2) :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
      ((projectionOfDesign design).submatrix pick pick
        - (1 / 6 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  let atom : Fin 6 → (Fin 3 → ℝ) := fun slot => scaledAtomRows design slot
  have hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction))
        = probe ⬝ᵥ direction := by
    simpa only [atom] using scaledAtomRows_frameLaw design
  have hbalanced : ∀ slot : Fin 6, atomGram atom slot slot = 1 / 2 := by
    intro slot
    change atomGram (fun index => scaledAtomRows design index) slot slot = 1 / 2
    rw [atomGram_scaledAtomRows, projectionOfDesign_diagonal]
    simpa only [atomShare] using hshare slot
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hfloor⟩ :=
    exists_atomShiftBlockMatrix_posSemidef_of_balanced atom hframe hbalanced
  let pick : Fin 3 → Fin 6 := ![first, second, third]
  have hpick : Function.Injective pick := by
    intro left right heq
    fin_cases left <;> fin_cases right <;>
      simp_all [pick]
  refine ⟨pick, hpick, ?_⟩
  have hshiftShape :
      atomShiftBlockMatrix atom first second third
        = (projectionOfDesign design).submatrix pick pick
            - (1 / 6 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext rowIndex colIndex
    rw [atomShiftBlockMatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.submatrix_apply]
    change atomGram (fun index => scaledAtomRows design index)
        (pick rowIndex) (pick colIndex) - (if rowIndex = colIndex then 1 / 6 else 0)
      = projectionOfDesign design (pick rowIndex) (pick colIndex)
          - (1 / 6) * (if rowIndex = colIndex then 1 else 0)
    rw [atomGram_scaledAtomRows]
    by_cases hsame : rowIndex = colIndex <;> simp [hsame]
  rw [← hshiftShape]
  exact hfloor

/-! ## 3. The flat block becomes an actual dominating triple -/

/-- A balanced projection-share `(6,3)` design whose weights stay below the
sharp balanced floor has a dominating triple. -/
theorem exists_dominates_of_uniformShare_of_weight_le_sixth
    (design : WeightedDesign 6 3)
    (hshare : ∀ atomIndex, atomShare design atomIndex = 1 / 2)
    (hweight : ∀ atomIndex, design.weight atomIndex ≤ 1 / 6) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected := by
  obtain ⟨pick, hpick, hshiftPsd⟩ :=
    exists_flatProjectionTriple_of_uniformShare design hshare
  have hdiagonalPsd :
      (Matrix.diagonal (fun selectedIndex : Fin 3 =>
        (1 / 6 : ℝ) - design.weight (pick selectedIndex))).PosSemidef :=
    Matrix.PosSemidef.diagonal fun selectedIndex => sub_nonneg.mpr (hweight (pick selectedIndex))
  have hactualShape :
      (projectionOfDesign design).submatrix pick pick
          - Matrix.diagonal (fun selectedIndex => design.weight (pick selectedIndex))
        = ((projectionOfDesign design).submatrix pick pick
            - (1 / 6 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
          + Matrix.diagonal (fun selectedIndex : Fin 3 =>
              (1 / 6 : ℝ) - design.weight (pick selectedIndex)) := by
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
    by_cases hsame : rowIndex = colIndex <;> simp [hsame]
  have hactualPsd :
      ((projectionOfDesign design).submatrix pick pick
          - Matrix.diagonal (fun selectedIndex => design.weight (pick selectedIndex))).PosSemidef := by
    rw [hactualShape]
    exact hshiftPsd.add hdiagonalPsd
  have hdominates : Dominates design (Finset.image pick Finset.univ) :=
    (dominates_iff_posSemidef_projectionBlock design pick hpick).mpr hactualPsd
  refine ⟨Finset.image pick Finset.univ, ?_, hdominates⟩
  rw [Finset.card_image_of_injective _ hpick, Finset.card_univ, Fintype.card_fin]

end Gtz
