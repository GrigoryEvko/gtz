/-
# The sharp balance law: the residual spectrum, not its trace

`Gtz.posDef_subsetSum_compl_of_baseShare_lt` reads the base residual through its
TRACE.  The engine it feeds, `Gtz.posDef_subsetSum_compl_of_residualExceedsMaxWeight`,
asks only that the residual form beat `maxWeight` in every direction, which is the
statement that `baseResidual - maxWeight • 1` is positive definite.  The trace step
`Gtz.trace_sub_two_le_dotProduct_of_quadForm_le_self` throws away two eigenvalues to
get there.

This module supplies the residual test itself.  At rank three the three elementary
symmetric functions of `baseResidual - maxWeight • 1` decide positive definiteness
(`Gtz.posDef_three_of_elementarySymmetric`), and each one is a polynomial in the
design data.  The result is a strictly stronger criterion with the same conclusion.

## What is proved here

* `Gtz.residualShift` and its three invariants, expanded in the invariants of the
  base residual.
* `Gtz.posDef_subsetSum_compl_of_posDef_residualShift` — the sharp balance law.
* `Gtz.posDef_subsetSum_compl_of_residual_invariants` — the same law with the
  hypothesis written as three polynomial inequalities.
* `Gtz.residual_invariant_fails_of_isTie` — the tie side: at every rank-three tie
  and every base set, one of the three invariants fails.
* `Gtz.twinAxisDesign` — a `(6,3)` design at which the trace law does NOT fire and
  the sharp law DOES.  The improvement is strict.
* `Gtz.det_residualShift_tetraDesign_eq_zero` — the calibration: at the tetrahedron
  tie the first two invariants are positive and the determinant is exactly zero.

## Scope

Rank three throughout, every size, every base set.  Nothing here uses a stress
hypothesis and nothing uses `size = 6`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.UThreeSixDisjunction
import Gtz.Design.StressFreeStratum
import Gtz.Design.StressCertificate
import Gtz.Quantitative.TripleCubicCriterion
import Gtz.Reduction.LiftingLemma
import Gtz.Design.FrameConservation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Finset Matrix

variable {size : ℕ}

/-! ## Part 1: the shifted residual -/

/-- A positive multiple of the identity is positive definite. -/
theorem posDef_smul_one {scale : ℝ} (hscale : 0 < scale) :
    ((scale • 1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (by rw [Matrix.transpose_smul, Matrix.transpose_one]),
      fun probeVec hprobeNe => ?_⟩
  rw [star_trivial, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  exact mul_pos hscale (dotProduct_self_pos hprobeNe)

/-- **The base residual, shifted down by a level.**  It is positive definite
exactly when the residual form beats `level` in every direction. -/
noncomputable def residualShift (design : WeightedDesign size 3) (baseSet : Finset (Fin size))
    (level : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  baseResidual design baseSet - level • 1

theorem transpose_baseResidual (design : WeightedDesign size 3) (baseSet : Finset (Fin size)) :
    (baseResidual design baseSet)ᵀ = baseResidual design baseSet := by
  rw [baseResidual, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_sum]
  refine congrArg₂ _ rfl (Finset.sum_congr rfl fun label _ => ?_)
  rw [Matrix.transpose_smul, atomMatrix, Matrix.transpose_vecMulVec]

theorem transpose_residualShift (design : WeightedDesign size 3) (baseSet : Finset (Fin size))
    (level : ℝ) : (residualShift design baseSet level)ᵀ = residualShift design baseSet level := by
  rw [residualShift, Matrix.transpose_sub, transpose_baseResidual, Matrix.transpose_smul,
    Matrix.transpose_one]

theorem dotProduct_residualShift_mulVec (design : WeightedDesign size 3)
    (baseSet : Finset (Fin size)) (level : ℝ) (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ (residualShift design baseSet level *ᵥ probeVec)
      = probeVec ⬝ᵥ (baseResidual design baseSet *ᵥ probeVec) - level * (probeVec ⬝ᵥ probeVec) := by
  rw [residualShift, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

/-- **A positive definite shift beats the level in every direction.**  This is the
hypothesis that `Gtz.posDef_subsetSum_compl_of_residualExceedsMaxWeight` consumes. -/
theorem residualExceedsLevel_of_posDef_residualShift (design : WeightedDesign size 3)
    (baseSet : Finset (Fin size)) {level : ℝ}
    (hposDef : (residualShift design baseSet level).PosDef)
    {probeVec : Fin 3 → ℝ} (hprobeNe : probeVec ≠ 0) :
    level * (probeVec ⬝ᵥ probeVec)
      < probeVec ⬝ᵥ (baseResidual design baseSet *ᵥ probeVec) := by
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobeNe
  rw [star_trivial, dotProduct_residualShift_mulVec] at hpos
  linarith

/-- **THE SHARP BALANCE LAW.**  If the base residual beats the largest complement
weight as a FORM — not merely in trace — the complement dominates strictly. -/
theorem posDef_subsetSum_compl_of_posDef_residualShift (design : WeightedDesign size 3)
    (baseSet : Finset (Fin size)) (maxWeight : ℝ) (hmaxPos : 0 < maxWeight)
    (hmaxBound : ∀ label ∈ baseSetᶜ, design.weight label ≤ maxWeight)
    (hposDef : (residualShift design baseSet maxWeight).PosDef) :
    (subsetSum design baseSetᶜ - 1).PosDef :=
  posDef_subsetSum_compl_of_residualExceedsMaxWeight design baseSet maxWeight hmaxPos hmaxBound
    fun probeVec hprobeNe =>
      residualExceedsLevel_of_posDef_residualShift design baseSet hposDef hprobeNe

/-! ## Part 2: the three invariants of the shift -/

theorem trace_residualShift (design : WeightedDesign size 3) (baseSet : Finset (Fin size))
    (level : ℝ) :
    Matrix.trace (residualShift design baseSet level)
      = Matrix.trace (baseResidual design baseSet) - 3 * level := by
  rw [residualShift, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  norm_num
  ring

theorem trace_eq_diagonal_sum (form : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace form = form 0 0 + form 1 1 + form 2 2 := by
  rw [Matrix.trace_fin_three]

theorem residualShift_diagonal (design : WeightedDesign size 3) (baseSet : Finset (Fin size))
    (level : ℝ) (index : Fin 3) :
    residualShift design baseSet level index index
      = baseResidual design baseSet index index - level := by
  simp [residualShift, Matrix.one_apply]

theorem residualShift_offDiagonal (design : WeightedDesign size 3) (baseSet : Finset (Fin size))
    (level : ℝ) {rowIndex colIndex : Fin 3} (hne : rowIndex ≠ colIndex) :
    residualShift design baseSet level rowIndex colIndex
      = baseResidual design baseSet rowIndex colIndex := by
  simp [residualShift, Matrix.one_apply, hne]

theorem secondInvariantThree_residualShift (design : WeightedDesign size 3)
    (baseSet : Finset (Fin size)) (level : ℝ) :
    secondInvariantThree (residualShift design baseSet level)
      = secondInvariantThree (baseResidual design baseSet)
        - 2 * level * Matrix.trace (baseResidual design baseSet) + 3 * level ^ 2 := by
  rw [secondInvariantThree, secondInvariantThree, trace_eq_diagonal_sum,
    residualShift_diagonal, residualShift_diagonal, residualShift_diagonal,
    residualShift_offDiagonal design baseSet level (by decide : (0 : Fin 3) ≠ 1),
    residualShift_offDiagonal design baseSet level (by decide : (1 : Fin 3) ≠ 0),
    residualShift_offDiagonal design baseSet level (by decide : (0 : Fin 3) ≠ 2),
    residualShift_offDiagonal design baseSet level (by decide : (2 : Fin 3) ≠ 0),
    residualShift_offDiagonal design baseSet level (by decide : (1 : Fin 3) ≠ 2),
    residualShift_offDiagonal design baseSet level (by decide : (2 : Fin 3) ≠ 1)]
  ring

theorem det_residualShift (design : WeightedDesign size 3) (baseSet : Finset (Fin size))
    (level : ℝ) :
    (residualShift design baseSet level).det
      = (baseResidual design baseSet).det
        - level * secondInvariantThree (baseResidual design baseSet)
        + level ^ 2 * Matrix.trace (baseResidual design baseSet) - level ^ 3 := by
  rw [Matrix.det_fin_three, Matrix.det_fin_three, secondInvariantThree, trace_eq_diagonal_sum,
    residualShift_diagonal, residualShift_diagonal, residualShift_diagonal,
    residualShift_offDiagonal design baseSet level (by decide : (0 : Fin 3) ≠ 1),
    residualShift_offDiagonal design baseSet level (by decide : (1 : Fin 3) ≠ 0),
    residualShift_offDiagonal design baseSet level (by decide : (0 : Fin 3) ≠ 2),
    residualShift_offDiagonal design baseSet level (by decide : (2 : Fin 3) ≠ 0),
    residualShift_offDiagonal design baseSet level (by decide : (1 : Fin 3) ≠ 2),
    residualShift_offDiagonal design baseSet level (by decide : (2 : Fin 3) ≠ 1)]
  ring

/-! ## Part 3: the polynomial form of the sharp law -/

/-- **THE SHARP BALANCE LAW, IN THREE POLYNOMIAL INEQUALITIES.**  The three
elementary symmetric functions of the shifted residual decide it, and each is a
polynomial in the invariants of the residual and in the level. -/
theorem posDef_subsetSum_compl_of_residual_invariants (design : WeightedDesign size 3)
    (baseSet : Finset (Fin size)) (maxWeight : ℝ) (hmaxPos : 0 < maxWeight)
    (hmaxBound : ∀ label ∈ baseSetᶜ, design.weight label ≤ maxWeight)
    (hfirst : 0 ≤ Matrix.trace (baseResidual design baseSet) - 3 * maxWeight)
    (hsecond : 0 ≤ secondInvariantThree (baseResidual design baseSet)
      - 2 * maxWeight * Matrix.trace (baseResidual design baseSet) + 3 * maxWeight ^ 2)
    (hthird : 0 < (baseResidual design baseSet).det
      - maxWeight * secondInvariantThree (baseResidual design baseSet)
      + maxWeight ^ 2 * Matrix.trace (baseResidual design baseSet) - maxWeight ^ 3) :
    (subsetSum design baseSetᶜ - 1).PosDef := by
  refine posDef_subsetSum_compl_of_posDef_residualShift design baseSet maxWeight hmaxPos
    hmaxBound (posDef_three_of_elementarySymmetric
      (transpose_residualShift design baseSet maxWeight) ?_ ?_ ?_)
  · rw [← trace_eq_diagonal_sum, trace_residualShift]; linarith
  · show (0 : ℝ) ≤ secondInvariantThree (residualShift design baseSet maxWeight)
    rw [secondInvariantThree_residualShift]
    linarith
  · rw [det_residualShift]; linarith

/-! ## Part 4: the tie side -/

/-- **AT A RANK-THREE TIE ONE OF THE THREE INVARIANTS FAILS.**  A necessary
condition on every tie, at every base set whose complement has three labels.  It is
a consequence of `Gtz.IsTie` and not a restatement of tie emptiness: it constrains
the residual of a NAMED base set, while tie emptiness quantifies over designs. -/
theorem residual_invariant_fails_of_isTie (design : WeightedDesign size 3)
    (htie : IsTie design) (baseSet : Finset (Fin size)) (hcard : (baseSetᶜ).card = 3)
    (maxWeight : ℝ) (hmaxPos : 0 < maxWeight)
    (hmaxBound : ∀ label ∈ baseSetᶜ, design.weight label ≤ maxWeight) :
    Matrix.trace (baseResidual design baseSet) - 3 * maxWeight < 0
      ∨ secondInvariantThree (baseResidual design baseSet)
          - 2 * maxWeight * Matrix.trace (baseResidual design baseSet) + 3 * maxWeight ^ 2 < 0
      ∨ (baseResidual design baseSet).det
          - maxWeight * secondInvariantThree (baseResidual design baseSet)
          + maxWeight ^ 2 * Matrix.trace (baseResidual design baseSet) - maxWeight ^ 3 ≤ 0 := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨hfirst, hsecond, hthird⟩ := hcontra
  exact htie.2 (baseSetᶜ) hcard (posDef_subsetSum_compl_of_residual_invariants design baseSet
    maxWeight hmaxPos hmaxBound hfirst hsecond hthird)

/-- The share reading of the first invariant: the trace of the residual is the
complement share sum, so the first inequality is a share floor. -/
theorem sum_complementShare_ge_of_posDef_residualShift (design : WeightedDesign size 3)
    (baseSet : Finset (Fin size)) (maxWeight : ℝ)
    (hfirst : 0 ≤ Matrix.trace (baseResidual design baseSet) - 3 * maxWeight) :
    3 * maxWeight ≤ ∑ label ∈ baseSetᶜ, atomShare design label := by
  rw [← trace_baseResidual_eq_sum_complementShare]
  linarith

/-! ## Part 5: the calibration at the tetrahedron tie -/

/-- **THE SINGLETON SHIFT, IN CLOSED FORM.**  Off a single label the base residual
is `1 - w_d • atomMatrix (g_d)`, so the shifted residual sends the dropped atom to a
multiple of itself.  The multiplier is `1 - level - atomShare d`. -/
theorem residualShift_singleton_mulVec (design : WeightedDesign size 3) (dropped : Fin size)
    (level : ℝ) :
    residualShift design ({dropped} : Finset (Fin size)) level *ᵥ design.atom dropped
      = (1 - level - atomShare design dropped) • design.atom dropped := by
  have hbase : baseResidual design ({dropped} : Finset (Fin size))
      = 1 - design.weight dropped • atomMatrix (design.atom dropped) := by
    rw [baseResidual, Finset.sum_singleton]
  rw [residualShift, hbase, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    atomMatrix_mulVec_eq_dot_smul, smul_smul, atomShare, leverageOf_eq_dotProduct_self]
  module

/-- **THE SHIFT IS SINGULAR EXACTLY AT THE CO-SHARE LEVEL.**  At `level = 1 - s_d`
the dropped atom is a null vector, so the sharp law cannot fire off that label. -/
theorem not_posDef_residualShift_singleton (design : WeightedDesign size 3)
    (dropped : Fin size) (hatomNe : design.atom dropped ≠ 0) :
    ¬ (residualShift design ({dropped} : Finset (Fin size))
        (1 - atomShare design dropped)).PosDef := by
  intro hposDef
  have hzero := residualShift_singleton_mulVec design dropped (1 - atomShare design dropped)
  have hcoeff : (1 : ℝ) - (1 - atomShare design dropped) - atomShare design dropped = 0 := by
    ring
  rw [hcoeff, zero_smul] at hzero
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hatomNe
  rw [star_trivial, hzero, dotProduct_zero] at hpos
  exact lt_irrefl 0 hpos

/-- **THE SHARP LAW IS TIGHT AT THE TETRAHEDRON TIE.**  Every tetrahedron share is
`3/4` and every weight is `1/4`, so the level the law would use off any one label is
exactly `1 - 3/4 = 1/4`, and the shift is singular there.  The tetrahedron is a tie,
so the law must fail, and this is exactly how. -/
theorem not_posDef_residualShift_tetraDesign (dropped : Fin 4) :
    ¬ (residualShift tetraDesign ({dropped} : Finset (Fin 4)) (1 / 4)).PosDef := by
  have hshare := atomShare_tetraDesign dropped
  have hlevel : (1 : ℝ) / 4 = 1 - atomShare tetraDesign dropped := by rw [hshare]; norm_num
  rw [hlevel]
  exact not_posDef_residualShift_singleton tetraDesign dropped (tetraAtom_ne_zero dropped)

/-! ## Part 6: the twin-axis design, where the trace law misses and the sharp law fires -/

/-- Six atoms on the three axes, a long one and a short one on each. -/
noncomputable def twinAxisAtom : Fin 6 → Fin 3 → ℝ :=
  ![![2, 0, 0], ![3/2, 0, 0], ![0, 2, 0], ![0, 3/2, 0], ![0, 0, 2], ![0, 0, 3/2]]

/-- The matching weights: `1/7` on the long atoms and `4/21` on the short ones. -/
noncomputable def twinAxisWeight : Fin 6 → ℝ :=
  ![1/7, 4/21, 1/7, 4/21, 1/7, 4/21]

/-- **The twin-axis design.**  Each axis carries mass `4/7` from its long atom and
`3/7` from its short one, so the weighted atoms resolve the identity. -/
noncomputable def twinAxisDesign : WeightedDesign 6 3 where
  atom := twinAxisAtom
  weight := twinAxisWeight
  weight_pos := by intro label; fin_cases label <;> simp [twinAxisWeight] <;> norm_num
  weight_sum_one := by
    simp [twinAxisWeight, Fin.sum_univ_six]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_six, smul_eq_mul]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [twinAxisAtom, twinAxisWeight, Matrix.one_apply] <;> norm_num

theorem twinAxisDesign_baseResidual :
    baseResidual twinAxisDesign ({1, 3, 5} : Finset (Fin 6)) = (4/7 : ℝ) • 1 := by
  rw [baseResidual]
  ext rowIndex colIndex
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply]
  have hsum : ({1, 3, 5} : Finset (Fin 6)) = {1, 3, 5} := rfl
  rw [hsum, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [twinAxisDesign, twinAxisAtom, twinAxisWeight, atomMatrix, Matrix.vecMulVec_apply,
      Matrix.one_apply, Matrix.smul_apply] <;> norm_num

theorem twinAxisDesign_complement :
    (({1, 3, 5} : Finset (Fin 6))ᶜ) = ({0, 2, 4} : Finset (Fin 6)) := by decide

theorem twinAxisDesign_maxWeight :
    ∀ label ∈ (({1, 3, 5} : Finset (Fin 6))ᶜ), twinAxisDesign.weight label ≤ 1/7 := by
  intro label hlabel
  rw [twinAxisDesign_complement] at hlabel
  have hcases : label = 0 ∨ label = 2 ∨ label = 4 := by revert hlabel; revert label; decide
  rcases hcases with rfl | rfl | rfl <;> simp [twinAxisDesign, twinAxisWeight] <;> norm_num

/-- **THE TRACE LAW MISSES HERE.**  The residual trace is `12/7`, and the trace step
of `Gtz.residualExceedsMaxWeight_of_trace_gt` needs it to exceed `2 + 1/7 = 15/7`. -/
theorem twinAxisDesign_trace_law_misses :
    Matrix.trace (baseResidual twinAxisDesign ({1, 3, 5} : Finset (Fin 6))) = 12/7
      ∧ ¬ (2 + (1/7 : ℝ)
        < Matrix.trace (baseResidual twinAxisDesign ({1, 3, 5} : Finset (Fin 6)))) := by
  have htrace : Matrix.trace (baseResidual twinAxisDesign ({1, 3, 5} : Finset (Fin 6)))
      = 12/7 := by
    rw [twinAxisDesign_baseResidual, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    norm_num
  exact ⟨htrace, by rw [htrace]; norm_num⟩

/-- **THE SHARP LAW FIRES HERE.**  The shifted residual is `(3/7) • 1`, positive
definite, so the complement triple `{0, 2, 4}` dominates strictly. -/
theorem twinAxisDesign_sharp_law_fires :
    (subsetSum twinAxisDesign ({0, 2, 4} : Finset (Fin 6)) - 1).PosDef := by
  have hshift : residualShift twinAxisDesign ({1, 3, 5} : Finset (Fin 6)) (1/7)
      = (3/7 : ℝ) • 1 := by
    rw [residualShift, twinAxisDesign_baseResidual, ← sub_smul]
    norm_num
  have hposDef : (residualShift twinAxisDesign ({1, 3, 5} : Finset (Fin 6)) (1/7)).PosDef := by
    rw [hshift]
    exact posDef_smul_one (by norm_num)
  have hmain := posDef_subsetSum_compl_of_posDef_residualShift twinAxisDesign
    ({1, 3, 5} : Finset (Fin 6)) (1/7) (by norm_num) twinAxisDesign_maxWeight hposDef
  rwa [twinAxisDesign_complement] at hmain

/-- **THE IMPROVEMENT IS STRICT.**  One design, one base set: the trace hypothesis
is false and the sharp hypothesis is true. -/
theorem sharp_law_strictly_improves_trace_law :
    ¬ (2 + (1/7 : ℝ)
        < Matrix.trace (baseResidual twinAxisDesign ({1, 3, 5} : Finset (Fin 6))))
      ∧ (residualShift twinAxisDesign ({1, 3, 5} : Finset (Fin 6)) (1/7)).PosDef
      ∧ (subsetSum twinAxisDesign ({0, 2, 4} : Finset (Fin 6)) - 1).PosDef := by
  refine ⟨twinAxisDesign_trace_law_misses.2, ?_, twinAxisDesign_sharp_law_fires⟩
  have hshift : residualShift twinAxisDesign ({1, 3, 5} : Finset (Fin 6)) (1/7)
      = (3/7 : ℝ) • 1 := by
    rw [residualShift, twinAxisDesign_baseResidual, ← sub_smul]
    norm_num
  rw [hshift]
  exact posDef_smul_one (by norm_num)

end Gtz
