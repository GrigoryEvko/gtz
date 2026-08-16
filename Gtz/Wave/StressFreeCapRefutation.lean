/-
# The weight cap does not decide branch (i)

`Gtz.not_isTie_of_projectionBlock_gt_weightCap` refutes a tie from ONE scalar
floor on a projection block.  This module measures how far that engine reaches on
the stress-free stratum of `(6,3)`, which is the only open arm of
`Gtz.sixThree_stress_trichotomy`.

## Section 1: two order-level laws the tree lacked

The tree flips `Xᵀ X` and `X Xᵀ` across `PosDef` only at level one, and across a
scalar level only for `PosSemidef`.  Section 1 lands the two strict scalar flips.

## Section 2: the complementary block, at the order level

At `m = 2k` the tree reads complementary blocks of the projection form through
DETERMINANTS (`Gtz.det_submatrix_eq_det_one_sub_complement`).  Section 2 upgrades
that to the Loewner order:

    P_C ≻ t · 1   ↔   P_Cᶜ ≺ (1 − t) · 1

The proof factors the block as a SQUARE matrix, which is exactly the step that
needs `m = 2k`.  Nothing here transports to `(4,3)` or to `(5,3)`.

## Section 3: what a firing cap costs

A firing cap sits below every selected diagonal entry, and its two-label minor
sits below the squared off-diagonal entry.  Section 3 states the pair form, which
is the sharpest reading that survives when the cap is only bounded below.

Section 3 also proves that no PAIR rule alone can block the cap: at rank three
every design carries two labels whose two-by-two Gram gap has positive
determinant.  The obstruction is the second-moment identity.

## Section 4: the refutation

`Gtz.capFoilDesign` is an explicit `(6,3)` design with integer atoms and rational
weights.  It is stress-free, it is not a tie, and NO selection fires the cap.  So
the weight cap cannot close branch (i).
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Certificates.ResidueDissolution
import Gtz.Quantitative.ChartHadamard
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.ConnectednessRoute
import Gtz.Design.StressFreeStratum
import Gtz.Reduction.TrichotomyLedger
import Gtz.Quantitative.WindowPolarity
import Gtz.Wave.TieParallelPairWeightRegular

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

/-! ## 1. The strict scalar transpose flips -/

/-- A positive scalar multiple of a positive definite matrix is positive definite,
and conversely.  The tree carries only the `PosSemidef` twin. -/
theorem posDef_smul_iff {size : ℕ} {form : Matrix (Fin size) (Fin size) ℝ} {scale : ℝ}
    (hscale : 0 < scale) : (scale • form).PosDef ↔ form.PosDef := by
  constructor
  · intro hsmul
    have hscaled := hsmul.smul (a := scale⁻¹) (by positivity)
    rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hscale), one_smul] at hscaled
  · exact fun hform => hform.smul hscale

/-- **The strict flip at a scalar level, square case.**  `Xᵀ X ≻ t` and `X Xᵀ ≻ t`
agree for a square `X` and a positive level.  The tree has this at `t = 1` only. -/
theorem posDef_transpose_mul_sub_smul_one_comm {size : ℕ}
    (square : Matrix (Fin size) (Fin size) ℝ) {level : ℝ} (hlevel : 0 < level) :
    (squareᵀ * square - level • (1 : Matrix (Fin size) (Fin size) ℝ)).PosDef
      ↔ (square * squareᵀ - level • (1 : Matrix (Fin size) (Fin size) ℝ)).PosDef := by
  set scaled : Matrix (Fin size) (Fin size) ℝ := (Real.sqrt level)⁻¹ • square with hscaled
  have hroot : Real.sqrt level * Real.sqrt level = level := Real.mul_self_sqrt hlevel.le
  have hrootPos : 0 < Real.sqrt level := Real.sqrt_pos.mpr hlevel
  have hscalar : (Real.sqrt level)⁻¹ * (Real.sqrt level)⁻¹ = level⁻¹ := by
    rw [← mul_inv, hroot]
  have hleft : scaledᵀ * scaled - 1 = level⁻¹ • (squareᵀ * square - level • 1) := by
    have hprod : scaledᵀ * scaled = level⁻¹ • (squareᵀ * square) := by
      rw [hscaled, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hscalar]
    rw [hprod, smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hlevel), one_smul]
  have hright : scaled * scaledᵀ - 1 = level⁻¹ • (square * squareᵀ - level • 1) := by
    have hprod : scaled * scaledᵀ = level⁻¹ • (square * squareᵀ) := by
      rw [hscaled, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hscalar]
    rw [hprod, smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hlevel), one_smul]
  have hflip := posDef_transpose_mul_sub_one_comm scaled
  rw [hleft, hright, posDef_smul_iff (by positivity), posDef_smul_iff (by positivity)] at hflip
  exact hflip

/-- **The strict flip at a scalar level, upper side, RECTANGULAR.**  `t ≻ Xᵀ X`
and `t ≻ X Xᵀ` agree for every `X`, square or not.  Only the lower side needs a
square matrix, because a rectangular `Xᵀ X` carries extra zero directions. -/
theorem posDef_smul_one_sub_transpose_comm {leftDim rightDim : ℕ} {level : ℝ}
    (hlevel : 0 < level) (rect : Matrix (Fin leftDim) (Fin rightDim) ℝ) :
    (level • (1 : Matrix (Fin rightDim) (Fin rightDim) ℝ) - rectᵀ * rect).PosDef
      ↔ (level • (1 : Matrix (Fin leftDim) (Fin leftDim) ℝ) - rect * rectᵀ).PosDef := by
  set scaled : Matrix (Fin leftDim) (Fin rightDim) ℝ := (Real.sqrt level)⁻¹ • rect with hscaled
  have hroot : Real.sqrt level * Real.sqrt level = level := Real.mul_self_sqrt hlevel.le
  have hrootPos : 0 < Real.sqrt level := Real.sqrt_pos.mpr hlevel
  have hscalar : (Real.sqrt level)⁻¹ * (Real.sqrt level)⁻¹ = level⁻¹ := by
    rw [← mul_inv, hroot]
  have hleft : (1 : Matrix (Fin rightDim) (Fin rightDim) ℝ) - scaledᵀ * scaled
      = level⁻¹ • (level • (1 : Matrix (Fin rightDim) (Fin rightDim) ℝ) - rectᵀ * rect) := by
    have hprod : scaledᵀ * scaled = level⁻¹ • (rectᵀ * rect) := by
      rw [hscaled, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hscalar]
    rw [hprod, smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hlevel), one_smul]
  have hright : (1 : Matrix (Fin leftDim) (Fin leftDim) ℝ) - scaled * scaledᵀ
      = level⁻¹ • (level • (1 : Matrix (Fin leftDim) (Fin leftDim) ℝ) - rect * rectᵀ) := by
    have hprod : scaled * scaledᵀ = level⁻¹ • (rect * rectᵀ) := by
      rw [hscaled, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hscalar]
    rw [hprod, smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hlevel), one_smul]
  have hflip := posDef_one_sub_transpose_comm scaled
  rw [hleft, hright, posDef_smul_iff (by positivity), posDef_smul_iff (by positivity)] at hflip
  exact hflip

/-! ## 2. The complementary block, at the order level

The tree reads complementary blocks of the projection form through determinants.
Here the same split is read through the Loewner order.  The step that needs
`m = 2k` is that the selected scaled rows form a SQUARE matrix. -/

/-- **THE ROW SPLIT.**  Two complementary selections of size `k` out of `2k` labels
exhaust the label set, so their scaled-row Gram matrices add to the identity. -/
theorem transpose_mul_add_transpose_mul_scaledRows {k : ℕ} (D : WeightedDesign (k + k) k)
    (pickKept pickExcluded : Fin k → Fin (k + k))
    (hinjKept : Function.Injective pickKept) (hinjExcluded : Function.Injective pickExcluded)
    (hdisjoint : ∀ keptSlot excludedSlot, pickKept keptSlot ≠ pickExcluded excludedSlot) :
    ((scaledAtomRows D).submatrix pickKept id)ᵀ * ((scaledAtomRows D).submatrix pickKept id)
        + ((scaledAtomRows D).submatrix pickExcluded id)ᵀ
          * ((scaledAtomRows D).submatrix pickExcluded id)
      = 1 := by
  classical
  have hbijective : Function.Bijective (Sum.elim pickKept pickExcluded) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp⟩
    rintro (leftSlot | leftSlot) (rightSlot | rightSlot) hslot <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hslot
    · exact congrArg Sum.inl (hinjKept hslot)
    · exact absurd hslot (hdisjoint leftSlot rightSlot)
    · exact absurd hslot.symm (hdisjoint rightSlot leftSlot)
    · exact congrArg Sum.inr (hinjExcluded hslot)
  rw [← transpose_mul_scaledAtomRows D]
  ext leftCoord rightCoord
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    id_eq]
  rw [← Fintype.sum_bijective _ hbijective
      (fun slot => scaledAtomRows D (Sum.elim pickKept pickExcluded slot) leftCoord
        * scaledAtomRows D (Sum.elim pickKept pickExcluded slot) rightCoord)
      (fun atomLabel => scaledAtomRows D atomLabel leftCoord
        * scaledAtomRows D atomLabel rightCoord) (fun _ => rfl),
    Fintype.sum_sum_type]
  simp

/-- **THE COMPLEMENTARY LOEWNER LAW.**  At `m = 2k` a scalar floor on one block is
the same statement as a scalar ceiling on the complementary block.  The tree
carries only the determinant shadow of this, `Gtz.det_submatrix_eq_det_one_sub_complement`.

This is the exact point where `(6,3)` parts company with `(4,3)` and `(5,3)`: the
selected scaled rows are square only when the size is twice the rank. -/
theorem posDef_projectionBlock_sub_smul_one_iff_complement {k : ℕ}
    (D : WeightedDesign (k + k) k) (pickKept pickExcluded : Fin k → Fin (k + k))
    (hinjKept : Function.Injective pickKept) (hinjExcluded : Function.Injective pickExcluded)
    (hdisjoint : ∀ keptSlot excludedSlot, pickKept keptSlot ≠ pickExcluded excludedSlot)
    {level : ℝ} (hlevelPos : 0 < level) (hlevelLt : level < 1) :
    ((projectionOfDesign D).submatrix pickKept pickKept
        - level • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef
      ↔ ((1 - level) • (1 : Matrix (Fin k) (Fin k) ℝ)
          - (projectionOfDesign D).submatrix pickExcluded pickExcluded).PosDef := by
  set keptRows := (scaledAtomRows D).submatrix pickKept id with hkeptRows
  set excludedRows := (scaledAtomRows D).submatrix pickExcluded id with hexcludedRows
  have hkeptBlock : (projectionOfDesign D).submatrix pickKept pickKept
      = keptRows * keptRowsᵀ := submatrix_mul_transpose_eq (scaledAtomRows D) pickKept
  have hexcludedBlock : (projectionOfDesign D).submatrix pickExcluded pickExcluded
      = excludedRows * excludedRowsᵀ := submatrix_mul_transpose_eq (scaledAtomRows D) pickExcluded
  have hsplit := transpose_mul_add_transpose_mul_scaledRows D pickKept pickExcluded
    hinjKept hinjExcluded hdisjoint
  have hkeptGram : keptRowsᵀ * keptRows = 1 - excludedRowsᵀ * excludedRows := by
    rw [← hsplit, add_sub_cancel_right]
  have hshift : keptRowsᵀ * keptRows - level • (1 : Matrix (Fin k) (Fin k) ℝ)
      = (1 - level) • (1 : Matrix (Fin k) (Fin k) ℝ) - excludedRowsᵀ * excludedRows := by
    rw [hkeptGram, sub_smul, one_smul]
    abel
  rw [hkeptBlock, hexcludedBlock,
    ← posDef_transpose_mul_sub_smul_one_comm keptRows hlevelPos, hshift,
    posDef_smul_one_sub_transpose_comm (by linarith) excludedRows]

/-! ## 3. What a firing cap costs

Two readings of `Matrix.PosDef` on a shifted projection block.  Both hold at every
size and every rank, and both stay inside the projection form. -/

/-- **A FIRING CAP SITS BELOW EVERY SELECTED DIAGONAL ENTRY.**  The diagonal of a
positive definite matrix is positive, so a scalar floor on a projection block is
capped by the smallest selected leverage share. -/
theorem weightCap_lt_projectionDiagonal_of_posDef {m k : ℕ} (D : WeightedDesign m k)
    {size : ℕ} (pick : Fin size → Fin m) (cap : ℝ) (selectedIndex : Fin size)
    (hfloor : ((projectionOfDesign D).submatrix pick pick
      - cap • (1 : Matrix (Fin size) (Fin size) ℝ)).PosDef) :
    cap < projectionOfDesign D (pick selectedIndex) (pick selectedIndex) := by
  have hdiag := hfloor.diag_pos (i := selectedIndex)
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one] at hdiag
  linarith

/-- **THE TWO-LABEL MINOR OF A FIRING CAP.**  Every two-by-two principal minor of a
positive definite matrix is positive, so a firing cap makes the squared off-diagonal
entry strictly smaller than the product of the two shifted diagonal entries. -/
theorem sq_projection_lt_pairGap_of_posDef {m k : ℕ} (D : WeightedDesign m k)
    {size : ℕ} (pick : Fin size → Fin m) (cap : ℝ) (firstIndex secondIndex : Fin size)
    (hne : firstIndex ≠ secondIndex)
    (hfloor : ((projectionOfDesign D).submatrix pick pick
      - cap • (1 : Matrix (Fin size) (Fin size) ℝ)).PosDef) :
    (projectionOfDesign D (pick firstIndex) (pick secondIndex)) ^ 2
      < (projectionOfDesign D (pick firstIndex) (pick firstIndex) - cap)
        * (projectionOfDesign D (pick secondIndex) (pick secondIndex) - cap) := by
  have hinjPair : Function.Injective (![firstIndex, secondIndex] : Fin 2 → Fin size) := by
    intro leftSlot rightSlot hslot
    fin_cases leftSlot <;> fin_cases rightSlot <;> simp_all
  have hminor := ((hfloor.submatrix hinjPair).det_pos)
  rw [Matrix.det_fin_two] at hminor
  have hsymm : projectionOfDesign D (pick secondIndex) (pick firstIndex)
      = projectionOfDesign D (pick firstIndex) (pick secondIndex) := by
    have := projectionOfDesign_transpose D
    calc projectionOfDesign D (pick secondIndex) (pick firstIndex)
        = (projectionOfDesign D)ᵀ (pick firstIndex) (pick secondIndex) := rfl
      _ = _ := by rw [this]
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, hne, Ne.symm hne, ite_true,
    ite_false, mul_one, mul_zero, sub_zero] at hminor
  rw [hsymm] at hminor
  nlinarith [hminor]

/-- **THE PAIR REFUTATION.**  If two selected labels carry a two-by-two gap that is
already blocked at a level the cap must clear, then NO admissible cap fires.  The
level enters only through `Gtz.WeightedDesign.weight` at one further label, which
the cap also has to clear. -/
theorem not_posDef_projectionBlock_of_pairFloor {m k : ℕ} (D : WeightedDesign m k)
    {size : ℕ} (pick : Fin size → Fin m) (cap : ℝ)
    (firstIndex secondIndex levelIndex : Fin size) (hne : firstIndex ≠ secondIndex)
    (hcap : D.weight (pick levelIndex) ≤ cap)
    (hblocked : (projectionOfDesign D (pick firstIndex) (pick firstIndex)
          - D.weight (pick levelIndex))
        * (projectionOfDesign D (pick secondIndex) (pick secondIndex)
          - D.weight (pick levelIndex))
      ≤ (projectionOfDesign D (pick firstIndex) (pick secondIndex)) ^ 2) :
    ¬ ((projectionOfDesign D).submatrix pick pick
        - cap • (1 : Matrix (Fin size) (Fin size) ℝ)).PosDef := by
  intro hfloor
  have hfirst := weightCap_lt_projectionDiagonal_of_posDef D pick cap firstIndex hfloor
  have hsecond := weightCap_lt_projectionDiagonal_of_posDef D pick cap secondIndex hfloor
  have hminor := sq_projection_lt_pairGap_of_posDef D pick cap firstIndex secondIndex hne hfloor
  have hmono := mul_le_mul
    (show projectionOfDesign D (pick firstIndex) (pick firstIndex) - cap
        ≤ projectionOfDesign D (pick firstIndex) (pick firstIndex)
          - D.weight (pick levelIndex) by linarith)
    (show projectionOfDesign D (pick secondIndex) (pick secondIndex) - cap
        ≤ projectionOfDesign D (pick secondIndex) (pick secondIndex)
          - D.weight (pick levelIndex) by linarith)
    (by linarith) (by linarith)
  linarith

/-! ### No pair rule alone can block the cap

The pair refutation reads a THIRD selected label, and it has to.  At rank three
the second moment forbids the two-label test from closing at every pair. -/

/-- The squared self-pairing of an atom is its leverage. -/
theorem dotProduct_self_eq_leverageOf {rank : ℕ} (vector : Fin rank → ℝ) :
    vector ⬝ᵥ vector = leverageOf vector := by
  simp only [dotProduct, leverageOf]
  exact Finset.sum_congr rfl fun _ _ => (sq _).symm

/-- Every weight of a design with at least two labels is strictly below one. -/
theorem weight_lt_one_of_two_le {m k : ℕ} (hsize : 2 ≤ m) (D : WeightedDesign m k)
    (atomLabel : Fin m) : D.weight atomLabel < 1 := by
  classical
  obtain ⟨otherLabel, hother⟩ : ∃ otherLabel : Fin m, otherLabel ≠ atomLabel :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) atomLabel
  have hpair : D.weight atomLabel + D.weight otherLabel
      ≤ ∑ label, D.weight label := by
    have hsubset : ({atomLabel, otherLabel} : Finset (Fin m)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun label _ _ => (D.weight_pos label).le)
    rwa [Finset.sum_pair (Ne.symm hother)] at hsum
  have hpos := D.weight_pos otherLabel
  have hone := D.weight_sum_one
  linarith

/-- The weight square is strictly below one at every design with at least two
labels.  This is the whole budget the pair test would need, and it cannot pay it. -/
theorem sum_sq_weight_lt_one {m k : ℕ} (hsize : 2 ≤ m) (D : WeightedDesign m k) :
    ∑ atomLabel, D.weight atomLabel ^ 2 < 1 := by
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty := by
    refine ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  calc ∑ atomLabel, D.weight atomLabel ^ 2
      < ∑ atomLabel, D.weight atomLabel := by
        refine Finset.sum_lt_sum_of_nonempty hnonempty fun atomLabel _ => ?_
        have hpos := D.weight_pos atomLabel
        have hlt := weight_lt_one_of_two_le hsize D atomLabel
        nlinarith
    _ = 1 := D.weight_sum_one

/-- **AT RANK THREE EVERY DESIGN CARRIES AN OPEN PAIR.**  Two distinct labels
satisfy `(g_a ⬝ᵥ g_b)^2 < (|g_a|^2 − 1) (|g_b|^2 − 1)`.

So no two-label rule can block `Gtz.not_posDef_projectionBlock_of_pairFloor` at
every pair, and a refutation of the cap must read a third selected label.  The
obstruction is the second moment: the pair test summed against the weights asks
for `(k − 1)^2 − k = 1` at rank three, and the weight square never reaches one. -/
theorem exists_open_pair_rankThree {m : ℕ} (hsize : 2 ≤ m) (D : WeightedDesign m 3) :
    ∃ leftLabel rightLabel : Fin m, leftLabel ≠ rightLabel ∧
      (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2
        < (leverageOf (D.atom leftLabel) - 1) * (leverageOf (D.atom rightLabel) - 1) := by
  classical
  by_contra hclosed
  push Not at hclosed
  set gapTerm : Fin m → Fin m → ℝ := fun leftLabel rightLabel =>
    D.weight leftLabel * D.weight rightLabel
      * ((D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2
        - (leverageOf (D.atom leftLabel) - 1) * (leverageOf (D.atom rightLabel) - 1))
    with hgapTerm
  have hnonneg : ∀ leftLabel rightLabel : Fin m, leftLabel ≠ rightLabel →
      0 ≤ gapTerm leftLabel rightLabel := by
    intro leftLabel rightLabel hne
    have hweights : 0 < D.weight leftLabel * D.weight rightLabel :=
      mul_pos (D.weight_pos leftLabel) (D.weight_pos rightLabel)
    have hclose := hclosed leftLabel rightLabel hne
    rw [hgapTerm]
    exact mul_nonneg hweights.le (by linarith)
  have hbudget : ∑ atomLabel, D.weight atomLabel * (leverageOf (D.atom atomLabel) - 1) = 2 := by
    have hmoment := sum_weight_mul_leverage D
    have hunit := D.weight_sum_one
    have hexpand : ∑ atomLabel, D.weight atomLabel * (leverageOf (D.atom atomLabel) - 1)
        = (∑ atomLabel, D.weight atomLabel * leverageOf (D.atom atomLabel))
          - ∑ atomLabel, D.weight atomLabel := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hexpand, hmoment, hunit]
    norm_num
  have hsquareTotal : ∑ leftLabel, ∑ rightLabel,
      D.weight leftLabel * D.weight rightLabel
        * ((leverageOf (D.atom leftLabel) - 1) * (leverageOf (D.atom rightLabel) - 1)) = 4 := by
    have hproduct := Finset.sum_mul_sum (Finset.univ : Finset (Fin m))
      (Finset.univ : Finset (Fin m))
      (fun atomLabel => D.weight atomLabel * (leverageOf (D.atom atomLabel) - 1))
      (fun atomLabel => D.weight atomLabel * (leverageOf (D.atom atomLabel) - 1))
    rw [hbudget] at hproduct
    rw [show (4 : ℝ) = 2 * 2 from by norm_num, hproduct]
    refine Finset.sum_congr rfl fun leftLabel _ => Finset.sum_congr rfl fun rightLabel _ => ?_
    ring
  have hpairTotal : ∑ leftLabel, ∑ rightLabel, gapTerm leftLabel rightLabel = -1 := by
    have hsecond := sum_pair_weight_mul_sq_dotProduct D
    have hsplit : ∑ leftLabel, ∑ rightLabel, gapTerm leftLabel rightLabel
        = (∑ leftLabel, ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
              * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2)
          - ∑ leftLabel, ∑ rightLabel, D.weight leftLabel * D.weight rightLabel
              * ((leverageOf (D.atom leftLabel) - 1) * (leverageOf (D.atom rightLabel) - 1)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun leftLabel _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun rightLabel _ => by rw [hgapTerm]; ring
    rw [hsplit, hsecond, hsquareTotal]
    norm_num
  have hrow : ∀ leftLabel : Fin m,
      gapTerm leftLabel leftLabel ≤ ∑ rightLabel, gapTerm leftLabel rightLabel := by
    intro leftLabel
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ leftLabel)]
    have htail : 0 ≤ ∑ rightLabel ∈ Finset.univ.erase leftLabel, gapTerm leftLabel rightLabel :=
      Finset.sum_nonneg fun rightLabel hmem =>
        hnonneg leftLabel rightLabel (Ne.symm (Finset.ne_of_mem_erase hmem))
    linarith
  have hdiagonalLe : ∑ leftLabel, gapTerm leftLabel leftLabel ≤ -1 := by
    rw [← hpairTotal]
    exact Finset.sum_le_sum fun leftLabel _ => hrow leftLabel
  have hdiagonalForm : ∀ leftLabel : Fin m, gapTerm leftLabel leftLabel
      = D.weight leftLabel ^ 2 * (2 * leverageOf (D.atom leftLabel) - 1) := by
    intro leftLabel
    simp only [hgapTerm, dotProduct_self_eq_leverageOf]
    ring
  have hdiagonalGe : -(∑ atomLabel, D.weight atomLabel ^ 2)
      ≤ ∑ leftLabel, gapTerm leftLabel leftLabel := by
    rw [Finset.sum_congr rfl fun leftLabel _ => hdiagonalForm leftLabel, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun leftLabel _ => ?_
    have hlev : 0 ≤ leverageOf (D.atom leftLabel) :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith [sq_nonneg (D.weight leftLabel)]
  have hweightSquare := sum_sq_weight_lt_one hsize D
  linarith

/-! ## 4. The foil

Six integer vectors in three-space and six rational weights.  The weights are the
unique Parseval solution over these six atoms, which exists and is unique exactly
because the design is stress-free. -/

/-- The six atoms of the foil, as integer vectors. -/
def foilAtom : Fin 6 → Fin 3 → ℝ :=
  ![![1, 1, 2], ![-1, 0, 1], ![-1, -1, -1], ![2, 0, 1], ![1, -1, 0], ![0, 2, -1]]

@[local simp] theorem foilAtom_zero : foilAtom 0 = ![1, 1, 2] := rfl
@[local simp] theorem foilAtom_one : foilAtom 1 = ![-1, 0, 1] := rfl
@[local simp] theorem foilAtom_two : foilAtom 2 = ![-1, -1, -1] := rfl
@[local simp] theorem foilAtom_three : foilAtom 3 = ![2, 0, 1] := rfl
@[local simp] theorem foilAtom_four : foilAtom 4 = ![1, -1, 0] := rfl
@[local simp] theorem foilAtom_five : foilAtom 5 = ![0, 2, -1] := rfl

/-- The weights of the foil.  They sum to one and they are the unique solution of
Parseval over the six atoms. -/
noncomputable def foilWeight : Fin 6 → ℝ := ![1 / 14, 8 / 21, 1 / 7, 1 / 21, 3 / 14, 1 / 7]

@[local simp] theorem foilWeight_zero : foilWeight 0 = 1 / 14 := rfl
@[local simp] theorem foilWeight_one : foilWeight 1 = 8 / 21 := rfl
@[local simp] theorem foilWeight_two : foilWeight 2 = 1 / 7 := rfl
@[local simp] theorem foilWeight_three : foilWeight 3 = 1 / 21 := rfl
@[local simp] theorem foilWeight_four : foilWeight 4 = 3 / 14 := rfl
@[local simp] theorem foilWeight_five : foilWeight 5 = 1 / 7 := rfl

/-- **THE FOIL.**  An explicit `(6,3)` design with integer atoms. -/
noncomputable def capFoilDesign : WeightedDesign 6 3 where
  atom := foilAtom
  weight := foilWeight
  weight_pos := by intro atomLabel; fin_cases atomLabel <;> norm_num [foilWeight]
  weight_sum_one := by
    simp only [Fin.sum_univ_six, foilWeight_zero, foilWeight_one, foilWeight_two,
      foilWeight_three, foilWeight_four, foilWeight_five]
    norm_num
  isParseval := by
    ext rowIndex columnIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, Matrix.one_apply, foilAtom_zero, foilAtom_one,
      foilAtom_two, foilAtom_three, foilAtom_four, foilAtom_five, foilWeight_zero,
      foilWeight_one, foilWeight_two, foilWeight_three, foilWeight_four, foilWeight_five]
    fin_cases rowIndex <;> fin_cases columnIndex <;> norm_num

@[local simp] theorem capFoilDesign_atom : capFoilDesign.atom = foilAtom := rfl
@[local simp] theorem capFoilDesign_weight : capFoilDesign.weight = foilWeight := rfl

/-! ### The foil is stress-free

Reading the six independent entries of a vanishing atom combination gives six
linear equations whose only solution is zero. -/

/-- **THE FOIL IS STRESS-FREE.**  Its six atom matrices are a basis of the
symmetric three-by-three matrices, so it sits on branch (i) of
`Gtz.sixThree_stress_trichotomy`. -/
theorem capFoilDesign_isStressFree :
    ∀ stress : Fin 6 → ℝ,
      (∑ atomLabel, stress atomLabel • atomMatrix (capFoilDesign.atom atomLabel)) = 0 →
        stress = 0 := by
  intro stress hvanishes
  have hentry : ∀ rowIndex columnIndex : Fin 3,
      (∑ atomLabel, stress atomLabel
        * (foilAtom atomLabel rowIndex * foilAtom atomLabel columnIndex)) = 0 := by
    intro rowIndex columnIndex
    have hpointwise := congrFun (congrFun hvanishes rowIndex) columnIndex
    simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix,
      Matrix.vecMulVec_apply] using hpointwise
  have hxx := hentry 0 0
  have hyy := hentry 1 1
  have hzz := hentry 2 2
  have hxy := hentry 0 1
  have hxz := hentry 0 2
  have hyz := hentry 1 2
  simp only [Fin.sum_univ_six, foilAtom_zero, foilAtom_one, foilAtom_two, foilAtom_three,
    foilAtom_four, foilAtom_five] at hxx hyy hzz hxy hxz hyz
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hxx hyy hzz hxy hxz hyz
  have hzero : stress 0 = 0 := by linarith
  have hone : stress 1 = 0 := by linarith
  have htwo : stress 2 = 0 := by linarith
  have hthree : stress 3 = 0 := by linarith
  have hfour : stress 4 = 0 := by linarith
  have hfive : stress 5 = 0 := by linarith
  funext atomLabel
  fin_cases atomLabel <;> simp only [Pi.zero_apply] <;> assumption

/-! ### The foil is not a tie

The triple `{0, 1, 5}` dominates strictly.  Its gap has trace `10`, second
invariant `27` and determinant `11`, so the inertia bridge applies. -/

/-- The gap of the triple `{0, 1, 5}`, in closed form. -/
theorem capFoilDesign_gapTriple :
    subsetSum capFoilDesign {0, 1, 5} - 1 = !![1, 1, 1; 1, 4, 0; 1, 0, 5] := by
  have hsum : subsetSum capFoilDesign {0, 1, 5}
      = atomMatrix (capFoilDesign.atom 0) + atomMatrix (capFoilDesign.atom 1)
        + atomMatrix (capFoilDesign.atom 5) := by
    simp only [subsetSum]
    rw [show ({0, 1, 5} : Finset (Fin 6)) = {0, 1, 5} from rfl]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      add_assoc]
  rw [hsum]
  ext rowIndex columnIndex
  simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
    capFoilDesign_atom, foilAtom_zero, foilAtom_one, foilAtom_five, Matrix.one_apply]
  fin_cases rowIndex <;> fin_cases columnIndex <;> norm_num

/-- **THE FOIL DOMINATES STRICTLY**, so it is not a tie. -/
theorem capFoilDesign_posDef_gapTriple :
    (subsetSum capFoilDesign {0, 1, 5} - 1).PosDef := by
  rw [capFoilDesign_gapTriple]
  refine posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos ?_ ?_ ?_ ?_
  · refine isHermitian_of_transpose_eq ?_
    ext rowIndex columnIndex
    fin_cases rowIndex <;> fin_cases columnIndex <;> norm_num
  · rw [Matrix.trace_fin_three]; norm_num
  · simp only [secondInvariantOfThree]; norm_num
  · rw [Matrix.det_fin_three]; norm_num

/-- **THE FOIL IS NOT A TIE.** -/
theorem capFoilDesign_not_isTie : ¬ IsTie capFoilDesign := fun htie =>
  htie.2 {0, 1, 5} (by decide) capFoilDesign_posDef_gapTriple

/-- **THE FOIL HAS NO PARALLEL PAIR**, because a parallel pair manufactures a
stress.  So it is a genuine branch (i) point and the hinge's conclusion is
unreachable at it. -/
theorem capFoilDesign_not_hasParallelPair : ¬ HasParallelPair capFoilDesign :=
  (isPrimitiveDesign_iff_not_hasParallelPair capFoilDesign).mp
    (isPrimitiveDesign_of_stressFree capFoilDesign capFoilDesign_isStressFree)

/-! ### The integer ledger

Every number the cap reads at the foil is a rational with denominator `42` or
`1764`.  Clearing the denominator once puts the whole selection question inside
the integers, where it is decidable. -/

/-- The atoms as integer vectors. -/
def foilAtomZ : Fin 6 → Fin 3 → ℤ :=
  ![![1, 1, 2], ![-1, 0, 1], ![-1, -1, -1], ![2, 0, 1], ![1, -1, 0], ![0, 2, -1]]

/-- The weights, cleared by `42`. -/
def foilWeightZ : Fin 6 → ℤ := ![3, 16, 6, 2, 9, 6]

theorem foilAtom_eq_cast (atomLabel : Fin 6) (coordinate : Fin 3) :
    foilAtom atomLabel coordinate = (foilAtomZ atomLabel coordinate : ℝ) := by
  fin_cases atomLabel <;> fin_cases coordinate <;> norm_num [foilAtom, foilAtomZ]

theorem foilWeight_eq_cast (atomLabel : Fin 6) :
    foilWeight atomLabel = (foilWeightZ atomLabel : ℝ) / 42 := by
  fin_cases atomLabel <;> norm_num [foilWeight, foilWeightZ]

/-- The integer Gram of the atoms. -/
def foilGramZ (leftLabel rightLabel : Fin 6) : ℤ :=
  ∑ coordinate, foilAtomZ leftLabel coordinate * foilAtomZ rightLabel coordinate

/-- The diagonal of the projection form, cleared by `42`. -/
def foilLevelZ (atomLabel : Fin 6) : ℤ := foilWeightZ atomLabel * foilGramZ atomLabel atomLabel

/-- The squared off-diagonal entry of the projection form, cleared by `1764`.  The
square clears both weight roots, so this is an integer. -/
def foilSquareZ (leftLabel rightLabel : Fin 6) : ℤ :=
  foilWeightZ leftLabel * foilWeightZ rightLabel * foilGramZ leftLabel rightLabel ^ 2

theorem foilGram_eq_cast (leftLabel rightLabel : Fin 6) :
    capFoilDesign.atom leftLabel ⬝ᵥ capFoilDesign.atom rightLabel
      = (foilGramZ leftLabel rightLabel : ℝ) := by
  simp only [capFoilDesign_atom, dotProduct, foilGramZ, foilAtom_eq_cast]
  push_cast
  rfl

theorem foilProjectionDiagonal (atomLabel : Fin 6) :
    projectionOfDesign capFoilDesign atomLabel atomLabel
      = (foilLevelZ atomLabel : ℝ) / 42 := by
  have hleverage : leverageOf (capFoilDesign.atom atomLabel)
      = (foilGramZ atomLabel atomLabel : ℝ) := by
    simp only [leverageOf, foilGramZ, capFoilDesign_atom, foilAtom_eq_cast]
    push_cast
    exact Finset.sum_congr rfl fun coordinate _ => by ring
  rw [projectionOfDesign_diagonal, hleverage, capFoilDesign_weight, foilWeight_eq_cast,
    foilLevelZ]
  push_cast
  ring

theorem foilProjectionSquare (leftLabel rightLabel : Fin 6) :
    projectionOfDesign capFoilDesign leftLabel rightLabel ^ 2
      = (foilSquareZ leftLabel rightLabel : ℝ) / 1764 := by
  rw [sq_projectionOfDesign_apply, foilGram_eq_cast, capFoilDesign_weight,
    foilWeight_eq_cast, foilWeight_eq_cast, foilSquareZ]
  push_cast
  ring

/-! ### The certificate

Every injective selection of three labels carries two labels whose two-by-two gap
is already blocked at the weight of a third selected label.  This is a finite
statement about integers. -/

set_option maxRecDepth 40000 in
/-- **THE PAIR CERTIFICATE, at all one hundred and twenty selections.**  For every
injective triple there are two selected labels and a third selected label whose
weight already closes their two-by-two gap. -/
theorem foil_pairCertificate (pick : Fin 3 → Fin 6) (hinj : Function.Injective pick) :
    ∃ firstIndex secondIndex levelIndex : Fin 3, pick firstIndex ≠ pick secondIndex ∧
      (foilLevelZ (pick firstIndex) - foilWeightZ (pick levelIndex))
          * (foilLevelZ (pick secondIndex) - foilWeightZ (pick levelIndex))
        ≤ foilSquareZ (pick firstIndex) (pick secondIndex) := by
  revert hinj
  revert pick
  decide

/-- **NO SELECTION FIRES THE CAP AT THE FOIL.**  Whatever the selection and
whatever the cap, the strict scalar floor fails. -/
theorem capFoilDesign_not_posDef_projectionBlock (pick : Fin 3 → Fin 6)
    (hinj : Function.Injective pick) (cap : ℝ)
    (hcap : ∀ selectedIndex, capFoilDesign.weight (pick selectedIndex) ≤ cap) :
    ¬ ((projectionOfDesign capFoilDesign).submatrix pick pick
        - cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef := by
  obtain ⟨firstIndex, secondIndex, levelIndex, hlabelNe, hcertificate⟩ :=
    foil_pairCertificate pick hinj
  have hindexNe : firstIndex ≠ secondIndex := fun heq => hlabelNe (by rw [heq])
  refine not_posDef_projectionBlock_of_pairFloor capFoilDesign pick cap firstIndex secondIndex
    levelIndex hindexNe (hcap levelIndex) ?_
  rw [foilProjectionDiagonal, foilProjectionDiagonal, foilProjectionSquare,
    capFoilDesign_weight, foilWeight_eq_cast]
  have hcast : ((foilLevelZ (pick firstIndex) : ℝ) - (foilWeightZ (pick levelIndex) : ℝ))
        * ((foilLevelZ (pick secondIndex) : ℝ) - (foilWeightZ (pick levelIndex) : ℝ))
      ≤ (foilSquareZ (pick firstIndex) (pick secondIndex) : ℝ) := by exact_mod_cast hcertificate
  set leftLevel : ℝ := (foilLevelZ (pick firstIndex) : ℝ) with hleftLevel
  set rightLevel : ℝ := (foilLevelZ (pick secondIndex) : ℝ) with hrightLevel
  set capLevel : ℝ := (foilWeightZ (pick levelIndex) : ℝ) with hcapLevel
  set blockSquare : ℝ := (foilSquareZ (pick firstIndex) (pick secondIndex) : ℝ) with hblockSquare
  have hregroup : (leftLevel / 42 - capLevel / 42) * (rightLevel / 42 - capLevel / 42)
      = ((leftLevel - capLevel) * (rightLevel - capLevel)) / 1764 := by ring
  rw [hregroup]
  linarith

/-- **THE WEIGHT CAP DOES NOT DECIDE BRANCH (i).**  There is a stress-free `(6,3)`
design that is not a tie and at which no selection and no admissible cap fires
`Gtz.not_isTie_of_projectionBlock_gt_weightCap`.  So the cap form of the engine,
which is sound, cannot by itself empty the stress-free stratum of ties. -/
theorem exists_stressFree_sixThree_beyond_weightCap :
    ∃ design : WeightedDesign 6 3,
      (∀ stress : Fin 6 → ℝ,
          (∑ atomLabel, stress atomLabel • atomMatrix (design.atom atomLabel)) = 0 → stress = 0)
        ∧ ¬ HasParallelPair design
        ∧ ¬ IsTie design
        ∧ ∀ pick : Fin 3 → Fin 6, Function.Injective pick → ∀ cap : ℝ,
            (∀ selectedIndex, design.weight (pick selectedIndex) ≤ cap) →
              ¬ ((projectionOfDesign design).submatrix pick pick
                  - cap • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef :=
  ⟨capFoilDesign, capFoilDesign_isStressFree, capFoilDesign_not_hasParallelPair,
    capFoilDesign_not_isTie, capFoilDesign_not_posDef_projectionBlock⟩

end Gtz
