/-
# The classical Goreinov-Tyrtyshnikov constant is ATTAINED at `(7,3)`

The classical maximal-volume bound is `sigma_min(A_T)^2 >= 1/(k(n-k)+1)`, i.e.
`1/13` at `(n,k) = (7,3)`, where GTZ asks for `1/7`; the shipped
`Gtz.gtzDenominator_add_deficit_eq_classical` and
`Gtz.classicalDenominator_eq_gtzDenominator_add_deficit`
(`Gtz/Reduction/MaximalVolume.lean`) record the deficit as `2*3 = 6`, and that
file's own docstring already spells out the `(7,3)` instance.

This file exhibits a configuration at which EVERY inequality in the classical chain
is an EQUALITY, so the constant `k(n-k)+1` cannot be improved by any sharpening of
that argument.  The solve pattern is `B = [ I_3 ; J_(4x3) ]`, four repeated
all-ones rows, with the pick `T = {0,1,2}`.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `isSwapMaximalRowPick_classicalExtremal` — chain step 1.  The exchange bound
  `|B_rj| <= 1` holds, with twelve entries exactly `1`
  (`solveMatrix_classicalExtremal_outside_eq_one`), so the pick is swap-maximal.
* `frobeniusSq_solveMatrix_classicalExtremal` — chain step 2.  The Frobenius count
  `||B||_F^2 <= k + (n-k)k = 15` is an EQUALITY.  This is a different Frobenius
  object from `Gtz.frobeniusInner` and
  `Gtz.frobeniusNormSq_veroneseTracelessPart`
  (`Gtz/Quantitative/SevenThreeMetricBound.lean`), which live on the veronese
  traceless chart; do not conflate them.
* `posSemidef_thirteen_sub_classicalExtremalGram` with
  `thirteen_sub_classicalExtremalGram_mulVec_ones` — chain step 3.  The trace bound
  `lambda_max(B^T B) <= tr - (k-1) = 13` is an EQUALITY, witnessed by the all-ones
  eigenvector.
* `posSemidef_classicalExtremalBlock_sub_thirteenth` with
  `classicalExtremalBlock_sub_thirteenth_mulVec_ones` — the consequence: the
  selected block `W = (B^T B)^{-1}` has `lambda_min(W) = 1/13` EXACTLY.
* `not_posSemidef_classicalExtremalBlock_sub_seventh` — the GTZ threshold fails at
  the swap-maximal pick, the all-ones direction seeing `-18/91`.  NO CONFLICT with
  the shipped `Gtz.posDef_unitPickGram_sub_fifth_sevenThree`
  (`Gtz/Quantitative/SevenThreeMaxVolume.lean`): that theorem is about
  `Gtz.unitAtomRows`, unit-normalised rows at uniform share `3/7`, whereas this
  frame's rows 3-6 have norm-squared `3`.  The scopes are disjoint.
* `posSemidef_classicalAlternativeBlock_sub_seventh` — GTZ IS NOT REFUTED.  The
  pick `{0,1,3}` has projection block above `(1/7)*1`, so a dominating triple
  exists.  The witness attacks the classical ANALYSIS and the maximal-volume
  RULE, not the conjecture.
* `classicalExtremalProjection_diag_ge` — the configuration is ALL-HEAVY.  Every
  diagonal entry of `P = B W B^T` is at least `3/13`; in the design normalisation
  `t_c = 1/7` the leverage is `l_c = 7*P_cc >= 21/13 > 1`.  So restricting GTZ to
  all-heavy designs cannot rescue the classical bound either.

## NOT proved here — READ THIS BEFORE CITING THE FILE

Nothing in this file is about a `Gtz.WeightedDesign`.  Every quantity is
FRAME-SIDE or PROJECTION-SIDE.  `classicalExtremalProjection` is proved symmetric,
idempotent and of trace three, but the textbook spectral fact that a symmetric
idempotent of trace `k` equals `A A^T` for some `A` with `A^T A = 1` — the step
that would turn `P` into an honest `(7,3)` Parseval frame — is NOT mechanized
here, and it cannot be repaired cheaply: the extremal frame is intrinsically
irrational (`det(B^T B) = 13`, not a rational square), so no rational orthonormal
realisation exists.  Every quantity used above is `P`-side and rational, so
nothing depends on that step numerically, but the bridge to
`Gtz.GtzWeightedHeavy 7 3` runs through an unmechanized link.

The word "attainment" here means attainment of the CLASSICAL CONSTANT `1/13`,
frame-side.  It is unrelated to the chart-minimiser sense of
`Gtz/Reduction/ChartAttainment.lean`.

Provenance: scratch report 13 (`litrecon`).  Two scratch declarations are dropped
as content-free: a bare `norm_num` for `1 < 7*(3/13)` (the reading is folded into
`classicalExtremalProjection_diag_ge`'s docstring) and a `norm_num` restatement of
the shipped `(7,3)` denominator arithmetic, which
`Gtz.gtzDenominator_add_deficit_eq_classical` already carries in general.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.MaximalVolume
import Gtz.Quantitative.SevenThreeMaxVolume

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace Gtz

open Matrix

/-! ## The configuration -/

/-- `B = [I_3 ; J_(4x3)]`, the frame at which the classical chain is tight. -/
def classicalExtremalFrame : Matrix (Fin 7) (Fin 3) ℝ :=
  !![1,0,0; 0,1,0; 0,0,1; 1,1,1; 1,1,1; 1,1,1; 1,1,1]

/-- The pick `T = {0,1,2}`. -/
def classicalExtremalPick : Fin 3 → Fin 7 := ![0,1,2]

/-- The alternative pick `{0,1,3}` — one basis row swapped for a repeated row. -/
def classicalAlternativePick : Fin 3 → Fin 7 := ![0,1,3]

/-- `W = (B^T B)^{-1}`, exhibited rationally. -/
noncomputable def classicalExtremalBlock : Matrix (Fin 3) (Fin 3) ℝ :=
  !![9/13, -4/13, -4/13; -4/13, 9/13, -4/13; -4/13, -4/13, 9/13]

/-- `4(3*1 - J)` at size three: positive semidefinite with kernel the all-ones line.
One Cauchy-Schwarz fact drives every bound below. -/
def onesGapThree : Matrix (Fin 3) (Fin 3) ℝ := !![8,-4,-4; -4,8,-4; -4,-4,8]

theorem isHermitian_onesGapThree : onesGapThree.IsHermitian := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [onesGapThree]

/-- `x^T(3*1 - J)x = 3|x|^2 - (sum x)^2 >= 0`. -/
theorem posSemidef_onesGapThree : onesGapThree.PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨isHermitian_onesGapThree, ?_⟩
  intro probe
  rw [star_trivial]
  simp [onesGapThree, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  nlinarith [sq_nonneg (probe 0 - probe 1), sq_nonneg (probe 0 - probe 2),
    sq_nonneg (probe 1 - probe 2)]

theorem onesGapThree_mulVec_ones : onesGapThree *ᵥ ![1,1,1] = 0 := by
  funext coord
  fin_cases coord <;>
    simp [onesGapThree, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num

/-! ## The Gram and its inverse -/

theorem classicalExtremalFrame_gram :
    classicalExtremalFrameᵀ * classicalExtremalFrame = !![5,4,4; 4,5,4; 4,4,5] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [classicalExtremalFrame, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

theorem classicalExtremalFrame_transpose :
    classicalExtremalFrameᵀ = !![1,0,0,1,1,1,1; 0,1,0,1,1,1,1; 0,0,1,1,1,1,1] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> simp [classicalExtremalFrame]

theorem selectedFrameRows_classicalExtremal :
    selectedFrameRows classicalExtremalFrame classicalExtremalPick = 1 := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [selectedFrameRows, classicalExtremalFrame, classicalExtremalPick]

theorem det_selectedFrameRows_classicalExtremal :
    (selectedFrameRows classicalExtremalFrame classicalExtremalPick).det = 1 := by
  rw [selectedFrameRows_classicalExtremal, Matrix.det_one]

theorem classicalExtremalBlock_isInverse :
    (classicalExtremalFrameᵀ * classicalExtremalFrame) * classicalExtremalBlock = 1 := by
  rw [classicalExtremalFrame_gram]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [classicalExtremalBlock, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-! ## Chain step 1 — the exchange bound, sitting ON its boundary -/

theorem solveMatrix_classicalExtremal :
    solveMatrix classicalExtremalFrame classicalExtremalPick = classicalExtremalFrame := by
  rw [solveMatrix, selectedFrameRows_classicalExtremal, inv_one, Matrix.mul_one]

/-- The exchange bound, here as the INPUT to swap-maximality rather than as the
output of `Gtz.abs_solveMatrix_le_one_of_maximalVolume`. -/
theorem abs_solveMatrix_classicalExtremal_le_one (rowIndex : Fin 7) (colIndex : Fin 3) :
    |solveMatrix classicalExtremalFrame classicalExtremalPick rowIndex colIndex| ≤ 1 := by
  rw [solveMatrix_classicalExtremal]
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [classicalExtremalFrame]

/-- Twelve of the solve coordinates are exactly `1`, so the exchange bound is
saturated at every outside entry. -/
theorem solveMatrix_classicalExtremal_outside_eq_one (rowIndex : Fin 7) (colIndex : Fin 3)
    (houtside : 3 ≤ (rowIndex : ℕ)) :
    solveMatrix classicalExtremalFrame classicalExtremalPick rowIndex colIndex = 1 := by
  rw [solveMatrix_classicalExtremal]
  fin_cases rowIndex <;> fin_cases colIndex <;> simp_all [classicalExtremalFrame]

/-- **The pick is swap-maximal**: no one-row exchange increases the volume. -/
theorem isSwapMaximalRowPick_classicalExtremal :
    IsSwapMaximalRowPick classicalExtremalFrame classicalExtremalPick := by
  intro rowIndex colIndex
  have hunit : IsUnit (selectedFrameRows classicalExtremalFrame classicalExtremalPick).det := by
    rw [det_selectedFrameRows_classicalExtremal]; exact isUnit_one
  rw [det_selectedFrameRows_update classicalExtremalFrame classicalExtremalPick hunit
      colIndex rowIndex,
    det_selectedFrameRows_classicalExtremal, abs_mul, abs_one, mul_one]
  exact abs_solveMatrix_classicalExtremal_le_one rowIndex colIndex

/-! ## Chain step 2 — the Frobenius count is an equality -/

/-- `||B||_F^2 = 15 = k + (n-k)*k` at `(7,3)`. -/
theorem frobeniusSq_solveMatrix_classicalExtremal :
    ∑ rowIndex : Fin 7, ∑ colIndex : Fin 3,
        solveMatrix classicalExtremalFrame classicalExtremalPick rowIndex colIndex ^ 2 = 15 := by
  rw [solveMatrix_classicalExtremal]
  simp [classicalExtremalFrame, Fin.sum_univ_succ]
  norm_num

/-! ## Chain step 3 — the trace bound is an equality: `lambda_max(B^T B) = 13` -/

theorem thirteen_sub_classicalExtremalGram_eq_onesGapThree :
    (13 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - classicalExtremalFrameᵀ * classicalExtremalFrame = onesGapThree := by
  rw [classicalExtremalFrame_gram]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> simp [onesGapThree] <;> norm_num

/-- **UPPER**: `lambda_max(B^T B) <= 13 = k(n-k)+1`. -/
theorem posSemidef_thirteen_sub_classicalExtremalGram :
    ((13 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - classicalExtremalFrameᵀ * classicalExtremalFrame).PosSemidef := by
  rw [thirteen_sub_classicalExtremalGram_eq_onesGapThree]; exact posSemidef_onesGapThree

/-- **ATTAINED**: the all-ones direction is an eigenvector at exactly `13`. -/
theorem thirteen_sub_classicalExtremalGram_mulVec_ones :
    ((13 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - classicalExtremalFrameᵀ * classicalExtremalFrame) *ᵥ ![1,1,1] = 0 := by
  rw [thirteen_sub_classicalExtremalGram_eq_onesGapThree]; exact onesGapThree_mulVec_ones

/-! ## Consequence — the selected block's least eigenvalue is exactly `1/13` -/

theorem classicalExtremalBlock_sub_thirteenth_eq :
    classicalExtremalBlock - (1/13 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = (1/13 : ℝ) • onesGapThree := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [classicalExtremalBlock, onesGapThree] <;> norm_num

/-- `lambda_min(W) >= 1/13` — the classical guarantee. -/
theorem posSemidef_classicalExtremalBlock_sub_thirteenth :
    (classicalExtremalBlock - (1/13 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  rw [classicalExtremalBlock_sub_thirteenth_eq]
  exact posSemidef_onesGapThree.smul (by norm_num)

/-- `lambda_min(W) <= 1/13` — attained on the all-ones direction. -/
theorem classicalExtremalBlock_sub_thirteenth_mulVec_ones :
    (classicalExtremalBlock - (1/13 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ ![1,1,1] = 0 := by
  rw [classicalExtremalBlock_sub_thirteenth_eq, Matrix.smul_mulVec, onesGapThree_mulVec_ones,
    smul_zero]

theorem classicalExtremalBlock_sub_seventh_eq :
    classicalExtremalBlock - (1/7 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = !![50/91, -28/91, -28/91; -28/91, 50/91, -28/91; -28/91, -28/91, 50/91] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> simp [classicalExtremalBlock] <;> norm_num

/-- **THE GTZ THRESHOLD FAILS AT THE SWAP-MAXIMAL PICK**: the all-ones direction sees
`-18/91 < 0`.  This does not contradict the shipped
`Gtz.posDef_unitPickGram_sub_fifth_sevenThree`, which is about unit-normalised rows;
rows 3-6 of this frame have norm-squared `3`. -/
theorem not_posSemidef_classicalExtremalBlock_sub_seventh :
    ¬ (classicalExtremalBlock - (1/7 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  intro hpsd
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![1,1,1]
  rw [star_trivial, classicalExtremalBlock_sub_seventh_eq] at hform
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hform
  norm_num at hform

/-! ## The projection, and the alternative pick that DOES clear `1/7` -/

/-- `P = B W B^T` — the rank-three orthogonal projection of the configuration.  Not
built from a `Gtz.WeightedDesign`: the bridge to a Parseval frame is the
unmechanized step this file's header flags. -/
noncomputable def classicalExtremalProjection : Matrix (Fin 7) (Fin 7) ℝ :=
  classicalExtremalFrame * classicalExtremalBlock * classicalExtremalFrameᵀ

/-- `B^T(B(W B^T)) = B^T`, the only algebra idempotency needs. -/
theorem gramSandwich_classicalExtremal :
    classicalExtremalFrameᵀ
        * (classicalExtremalFrame * (classicalExtremalBlock * classicalExtremalFrameᵀ))
      = classicalExtremalFrameᵀ := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, classicalExtremalBlock_isInverse, Matrix.one_mul]

/-- `P` is idempotent. -/
theorem classicalExtremalProjection_idem :
    classicalExtremalProjection * classicalExtremalProjection = classicalExtremalProjection := by
  rw [classicalExtremalProjection]
  simp only [Matrix.mul_assoc]
  rw [gramSandwich_classicalExtremal]

theorem classicalExtremalBlock_transpose :
    classicalExtremalBlockᵀ = classicalExtremalBlock := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> simp [classicalExtremalBlock]

/-- `P` is symmetric. -/
theorem classicalExtremalProjection_transpose :
    classicalExtremalProjectionᵀ = classicalExtremalProjection := by
  rw [classicalExtremalProjection, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, classicalExtremalBlock_transpose, Matrix.mul_assoc]

/-- `tr P = 3`: the projection has rank three.  The shipped
`Gtz.trace_projectionOfDesign` is the design-side analogue; this projection is not
built from a design, which is exactly the gap the header records. -/
theorem trace_classicalExtremalProjection : Matrix.trace classicalExtremalProjection = 3 := by
  rw [classicalExtremalProjection, classicalExtremalFrame_transpose]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, classicalExtremalFrame,
    classicalExtremalBlock, Fin.sum_univ_succ]
  norm_num

/-- The projection block at the swap-maximal pick IS `W`. -/
theorem projectionBlock_classicalExtremalPick :
    classicalExtremalProjection.submatrix classicalExtremalPick classicalExtremalPick
      = classicalExtremalBlock := by
  ext rowIndex colIndex
  rw [classicalExtremalProjection, classicalExtremalFrame_transpose]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [classicalExtremalPick, classicalExtremalFrame, classicalExtremalBlock]

/-- The projection block at `{0,1,3}`. -/
theorem projectionBlock_classicalAlternativePick :
    classicalExtremalProjection.submatrix classicalAlternativePick classicalAlternativePick
      = !![9/13, -4/13, 1/13; -4/13, 9/13, 1/13; 1/13, 1/13, 3/13] := by
  ext rowIndex colIndex
  rw [classicalExtremalProjection, classicalExtremalFrame_transpose]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [classicalAlternativePick, classicalExtremalFrame, classicalExtremalBlock,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

theorem classicalAlternativeBlock_sub_seventh_eq :
    (!![9/13, -4/13, 1/13; -4/13, 9/13, 1/13; 1/13, 1/13, 3/13] : Matrix (Fin 3) (Fin 3) ℝ)
        - (1/7 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = !![50/91, -28/91, 7/91; -28/91, 50/91, 7/91; 7/91, 7/91, 8/91] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> simp <;> norm_num

theorem isHermitian_classicalAlternativeGap :
    (!![50/91, -28/91, 7/91; -28/91, 50/91, 7/91; 7/91, 7/91, 8/91]
      : Matrix (Fin 3) (Fin 3) ℝ).IsHermitian := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num

/-- **GTZ IS NOT REFUTED HERE**: the pick `{0,1,3}` has projection block above
`(1/7)*1`, so a dominating triple exists.  The witness attacks the classical
bound and the maximal-volume rule, not the conjecture. -/
theorem posSemidef_classicalAlternativeBlock_sub_seventh :
    ((!![9/13, -4/13, 1/13; -4/13, 9/13, 1/13; 1/13, 1/13, 3/13] : Matrix (Fin 3) (Fin 3) ℝ)
      - (1/7 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  rw [classicalAlternativeBlock_sub_seventh_eq]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨isHermitian_classicalAlternativeGap, ?_⟩
  intro probe
  rw [star_trivial]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  nlinarith [sq_nonneg (50 * probe 0 - 28 * probe 1 + 7 * probe 2),
    sq_nonneg (22 * probe 1 + 7 * probe 2), sq_nonneg (probe 2),
    sq_nonneg (probe 0), sq_nonneg (probe 1)]

/-! ## The extremal configuration is ALL-HEAVY -/

/-- Every diagonal entry of `P` is at least `3/13`.  In the design normalisation
`t_c = 1/7` the leverage is `l_c = 7*P_cc`, so every leverage is at least
`7*(3/13) = 21/13 > 1`: the configuration lies inside `Gtz.AllHeavy`, the hypothesis
class of the target `Gtz.GtzWeightedHeavy 7 3`.  Restricting GTZ to all-heavy
designs therefore cannot rescue the classical bound. -/
theorem classicalExtremalProjection_diag_ge (index : Fin 7) :
    3/13 ≤ classicalExtremalProjection index index := by
  rw [classicalExtremalProjection, classicalExtremalFrame_transpose]
  fin_cases index <;>
    simp [classicalExtremalFrame, classicalExtremalBlock, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> norm_num

end Gtz
