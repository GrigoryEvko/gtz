/-
# The subset mass law and the complementary minor duality

The `rank`-sized principal minors of a design's projection form are non-negative
and total one, so they are a probability weight on the selections.  This file
computes the weight of **every** down-set at once.

**THE SUBSET MASS LAW.**  Split the labels into a kept set `U` and an excluded set
`E`.  Then

  `∑ over rank-subsets S of U of det P_SS  =  det (1 - P_EE)`.

The left side runs over the selections that avoid `E`, and the right side reads
only `E`'s own block.  Neither side mentions the other set's geometry.

The law is one determinant swap.  Parseval splits the identity as
`Gram(U) + Gram(E) = 1`, so `Gram(U) = 1 - Gram(E)`, and `det (1 - CᵀC)` equals
`det (1 - C Cᵀ)` at any shape.  That moves an `E`-sized determinant onto the
`rank`-sized one and back.

Four levels fall out of the single statement, at `(6,3)`:

| excluded | subset mass |
|---|---|
| nothing | `1` |
| one label `c` | `1 - P c c` |
| a pair `a b` | `(1 - P a a) * (1 - P b b) - P a b ^ 2` |
| a triple `E` | `det (1 - P_EE)` |

At three excluded labels the kept set is itself a single selection, so the law
collapses to a **duality**:

  `det P_SS = det (1 - P)_{Sᶜ Sᶜ}`.

**The determinantal weight of a triple is the complementary projection's weight at
the complementary triple.**  So every reading of `det P_SS` has a second reading on
`1 - P` at the complementary triple, for free.

The pair level also gives the exact correlation of the selection measure:
`pairMinorAt P a b - P a a * P b b = -(P a b ^ 2)`, so the measure is negatively
associated and the defect is exactly the squared projection entry.
-/
import Gtz.Wave.ComplementFourBlock

set_option maxHeartbeats 1000000

namespace Gtz

open scoped BigOperators

open Matrix

variable {size rank : ℕ}

/-! ## The partition of Parseval

Two injective picks whose images are disjoint and whose counts add to the label
count split the identity between them.  Card counting, then `Finset.sum_union`. -/

/-- **PARSEVAL SPLITS ALONG A PARTITION.**  Disjoint injective picks of
complementary size carry outer forms totalling the identity. -/
theorem sum_outer_partition (design : WeightedDesign size rank)
    {countKept countExcluded : ℕ} {pickKept : Fin countKept → Fin size}
    {pickExcluded : Fin countExcluded → Fin size}
    (hinjKept : Function.Injective pickKept) (hinjExcluded : Function.Injective pickExcluded)
    (hdisjoint : ∀ (kept : Fin countKept) (excluded : Fin countExcluded),
      pickKept kept ≠ pickExcluded excluded)
    (hcount : countKept + countExcluded = size) :
    (∑ kept : Fin countKept, atomMatrix (scaledAtomRows design (pickKept kept)))
        + ∑ excluded : Fin countExcluded,
            atomMatrix (scaledAtomRows design (pickExcluded excluded)) = 1 := by
  classical
  have hdisjointImage :
      Disjoint (Finset.image pickKept Finset.univ) (Finset.image pickExcluded Finset.univ) := by
    rw [Finset.disjoint_left]
    intro label hkept hexcluded
    obtain ⟨kept, _, hkeptEq⟩ := Finset.mem_image.mp hkept
    obtain ⟨excluded, _, hexcludedEq⟩ := Finset.mem_image.mp hexcluded
    exact hdisjoint kept excluded (hkeptEq.trans hexcludedEq.symm)
  have hcardKept : (Finset.image pickKept Finset.univ).card = countKept := by
    rw [Finset.card_image_of_injective _ hinjKept, Finset.card_univ, Fintype.card_fin]
  have hcardExcluded : (Finset.image pickExcluded Finset.univ).card = countExcluded := by
    rw [Finset.card_image_of_injective _ hinjExcluded, Finset.card_univ, Fintype.card_fin]
  have hunion : Finset.image pickKept Finset.univ ∪ Finset.image pickExcluded Finset.univ
      = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisjointImage, hcardKept, hcardExcluded, hcount]
    exact (Fintype.card_fin size).symm
  have hsumKept : ∑ kept : Fin countKept, atomMatrix (scaledAtomRows design (pickKept kept))
      = ∑ label ∈ Finset.image pickKept Finset.univ,
          atomMatrix (scaledAtomRows design label) := by
    rw [Finset.sum_image fun left _ right _ hlr => hinjKept hlr]
  have hsumExcluded : ∑ excluded : Fin countExcluded,
        atomMatrix (scaledAtomRows design (pickExcluded excluded))
      = ∑ label ∈ Finset.image pickExcluded Finset.univ,
          atomMatrix (scaledAtomRows design label) := by
    rw [Finset.sum_image fun left _ right _ hlr => hinjExcluded hlr]
  have hparseval : ∑ label : Fin size, atomMatrix (scaledAtomRows design label) = 1 := by
    rw [← transpose_mul_self_eq_sum_rows]
    exact transpose_mul_scaledAtomRows design
  rw [hsumKept, hsumExcluded, ← Finset.sum_union hdisjointImage, hunion, hparseval]

/-! ## The subset mass law -/

/-- The Gram of a picked block is the sum of its outer forms. -/
theorem transpose_mul_submatrix_eq_sum_outer (design : WeightedDesign size rank)
    {count : ℕ} (pick : Fin count → Fin size) :
    ((scaledAtomRows design).submatrix pick id)ᵀ * ((scaledAtomRows design).submatrix pick id)
      = ∑ slot : Fin count, atomMatrix (scaledAtomRows design (pick slot)) := by
  rw [transpose_mul_self_eq_sum_rows]
  refine Finset.sum_congr rfl fun slot _ => ?_
  congr 1

/-- **THE SUBSET MASS LAW.**  The total determinantal weight of the `rank`-sized
selections avoiding an excluded set is the determinant of `1` minus the excluded
set's own block.  The kept set's geometry never enters the right side.

One determinant swap carries the whole proof: Parseval splits the identity, and
`det (1 - CᵀC) = det (1 - C Cᵀ)` moves the statement between the two sizes. -/
theorem principalMinorTotal_submatrix_eq_det_one_sub_block (design : WeightedDesign size rank)
    {countKept countExcluded : ℕ} {pickKept : Fin countKept → Fin size}
    {pickExcluded : Fin countExcluded → Fin size}
    (hinjKept : Function.Injective pickKept) (hinjExcluded : Function.Injective pickExcluded)
    (hdisjoint : ∀ (kept : Fin countKept) (excluded : Fin countExcluded),
      pickKept kept ≠ pickExcluded excluded)
    (hcount : countKept + countExcluded = size) :
    principalMinorTotal ((projectionOfDesign design).submatrix pickKept pickKept) rank
      = ((1 : Matrix (Fin countExcluded) (Fin countExcluded) ℝ)
          - (projectionOfDesign design).submatrix pickExcluded pickExcluded).det := by
  set keptFrame := (scaledAtomRows design).submatrix pickKept id with hkeptFrame
  set excludedFrame := (scaledAtomRows design).submatrix pickExcluded id with hexcludedFrame
  have hkeptTotal :
      principalMinorTotal ((projectionOfDesign design).submatrix pickKept pickKept) rank
        = (keptFrameᵀ * keptFrame).det := by
    rw [projectionOfDesign, hkeptFrame, principalMinorTotal_submatrix_mul_transpose_eq_det]
  have hsplit := sum_outer_partition design hinjKept hinjExcluded hdisjoint hcount
  have hkeptGram : keptFrameᵀ * keptFrame
      = 1 - excludedFrameᵀ * excludedFrame := by
    rw [hkeptFrame, hexcludedFrame, transpose_mul_submatrix_eq_sum_outer,
      transpose_mul_submatrix_eq_sum_outer, ← hsplit]
    abel
  have hswap : ((1 : Matrix (Fin rank) (Fin rank) ℝ) - excludedFrameᵀ * excludedFrame).det
      = ((1 : Matrix (Fin countExcluded) (Fin countExcluded) ℝ)
          - excludedFrame * excludedFrameᵀ).det := by
    have hleft : (1 : Matrix (Fin rank) (Fin rank) ℝ) - excludedFrameᵀ * excludedFrame
        = 1 + (-excludedFrameᵀ) * excludedFrame := by
      rw [Matrix.neg_mul]; abel
    have hright : (1 : Matrix (Fin countExcluded) (Fin countExcluded) ℝ)
        - excludedFrame * excludedFrameᵀ
        = 1 + excludedFrame * (-excludedFrameᵀ) := by
      rw [Matrix.mul_neg]; abel
    rw [hleft, hright, Matrix.det_one_add_mul_comm]
  have hexcludedBlock : excludedFrame * excludedFrameᵀ
      = (projectionOfDesign design).submatrix pickExcluded pickExcluded := by
    rw [projectionOfDesign, hexcludedFrame]
    exact (submatrix_mul_transpose_eq_general (scaledAtomRows design) pickExcluded).symm
  rw [hkeptTotal, hkeptGram, hswap, hexcludedBlock]

/-! ## The four levels at six labels and rank three -/

/-- A submatrix of the identity along an injective pick is the identity. -/
theorem submatrix_one_of_injective {count : ℕ} {pick : Fin count → Fin size}
    (hinj : Function.Injective pick) :
    ((1 : Matrix (Fin size) (Fin size) ℝ).submatrix pick pick) = 1 := by
  ext left right
  rw [Matrix.submatrix_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases hcase : left = right
  · rw [if_pos hcase, if_pos (by rw [hcase])]
  · rw [if_neg hcase, if_neg fun hcontra => hcase (hinj hcontra)]

/-- **LEVEL ONE.**  The selections avoiding a single label carry total weight
`1 - P c c`.  So the label's own leverage is exactly the weight of the selections
that DO contain it. -/
theorem principalMinorTotal_eq_one_sub_diagonal (design : WeightedDesign 6 3)
    {pickKept : Fin 5 → Fin 6} (hinjKept : Function.Injective pickKept)
    {excludedLabel : Fin 6} (hmiss : ∀ kept, pickKept kept ≠ excludedLabel) :
    principalMinorTotal ((projectionOfDesign design).submatrix pickKept pickKept) 3
      = 1 - projectionOfDesign design excludedLabel excludedLabel := by
  have hinjExcluded : Function.Injective (fun _ : Fin 1 => excludedLabel) := by
    intro left right _
    exact Subsingleton.elim left right
  have hmain := principalMinorTotal_submatrix_eq_det_one_sub_block design hinjKept hinjExcluded
    (fun kept _ => hmiss kept) (by norm_num)
  rw [hmain, Matrix.det_fin_one]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.submatrix_apply]

/-- **LEVEL TWO.**  The pair level of the law recovers the complement four-block's
determinant, from a route that never mentions the four survivors. -/
theorem principalMinorTotal_eq_pair_slack_det (design : WeightedDesign 6 3)
    {pickKept : Fin 4 → Fin 6} (hinjKept : Function.Injective pickKept)
    {pickExcluded : Fin 2 → Fin 6} (hinjExcluded : Function.Injective pickExcluded)
    (hdisjoint : ∀ kept excluded, pickKept kept ≠ pickExcluded excluded) :
    principalMinorTotal ((projectionOfDesign design).submatrix pickKept pickKept) 3
      = (1 - projectionOfDesign design (pickExcluded 0) (pickExcluded 0))
          * (1 - projectionOfDesign design (pickExcluded 1) (pickExcluded 1))
        - projectionOfDesign design (pickExcluded 0) (pickExcluded 1) ^ 2 := by
  have hmain := principalMinorTotal_submatrix_eq_det_one_sub_block design hinjKept hinjExcluded
    hdisjoint (by norm_num)
  have hsymm := projectionOfDesign_transpose design
  have hsym01 : projectionOfDesign design (pickExcluded 1) (pickExcluded 0)
      = projectionOfDesign design (pickExcluded 0) (pickExcluded 1) := by
    conv_lhs => rw [← hsymm]
    rfl
  rw [hmain, Matrix.det_fin_two]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.submatrix_apply]
  norm_num [hsym01]
  ring

/-- **THE COMPLEMENTARY MINOR DUALITY.**  At three excluded labels the kept set is
itself a single selection, so the subset mass law collapses to an identity between
two `3 × 3` minors on disjoint label sets:

  `det P_S = det (1 - P_E)`,  for complementary triples `S` and `E`.

**The determinantal weight of a triple is the complementary projection's weight at
the complementary triple.**  Every reading of one is a reading of the other. -/
theorem det_submatrix_eq_det_one_sub_complement (design : WeightedDesign 6 3)
    {pickKept pickExcluded : Fin 3 → Fin 6} (hinjKept : Function.Injective pickKept)
    (hinjExcluded : Function.Injective pickExcluded)
    (hdisjoint : ∀ kept excluded, pickKept kept ≠ pickExcluded excluded) :
    ((projectionOfDesign design).submatrix pickKept pickKept).det
      = ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (projectionOfDesign design).submatrix pickExcluded pickExcluded).det := by
  have hmain := principalMinorTotal_submatrix_eq_det_one_sub_block design hinjKept hinjExcluded
    hdisjoint (by norm_num)
  have hcard :
      principalMinorTotal ((projectionOfDesign design).submatrix pickKept pickKept) 3
        = ((projectionOfDesign design).submatrix pickKept pickKept).det := by
    simpa using principalMinorTotal_card ((projectionOfDesign design).submatrix pickKept pickKept)
  rw [← hcard, hmain]

/-- The duality read on the complementary projection itself, rather than on `1`
minus a block.  This is the form a cell consumes. -/
theorem det_submatrix_eq_det_complementProjection (design : WeightedDesign 6 3)
    {pickKept pickExcluded : Fin 3 → Fin 6} (hinjKept : Function.Injective pickKept)
    (hinjExcluded : Function.Injective pickExcluded)
    (hdisjoint : ∀ kept excluded, pickKept kept ≠ pickExcluded excluded) :
    ((projectionOfDesign design).submatrix pickKept pickKept).det
      = (((1 : Matrix (Fin 6) (Fin 6) ℝ)
          - projectionOfDesign design).submatrix pickExcluded pickExcluded).det := by
  have hone : ((1 : Matrix (Fin 6) (Fin 6) ℝ).submatrix pickExcluded pickExcluded)
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) := submatrix_one_of_injective hinjExcluded
  have hblock : (((1 : Matrix (Fin 6) (Fin 6) ℝ) - projectionOfDesign design).submatrix
        pickExcluded pickExcluded)
      = (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (projectionOfDesign design).submatrix pickExcluded pickExcluded := by
    ext left right
    simp only [Matrix.submatrix_apply, Matrix.sub_apply]
    congr 1
    calc (1 : Matrix (Fin 6) (Fin 6) ℝ) (pickExcluded left) (pickExcluded right)
        = ((1 : Matrix (Fin 6) (Fin 6) ℝ).submatrix pickExcluded pickExcluded) left right := rfl
      _ = (1 : Matrix (Fin 3) (Fin 3) ℝ) left right := by rw [hone]
  rw [det_submatrix_eq_det_one_sub_complement design hinjKept hinjExcluded hdisjoint, hblock]

/-- **THE DUALITY IS AN INVOLUTION.**  Swapping the two complementary triples
swaps the two readings, so the pair of minors determines both. -/
theorem det_one_sub_submatrix_eq_det_complement (design : WeightedDesign 6 3)
    {pickKept pickExcluded : Fin 3 → Fin 6} (hinjKept : Function.Injective pickKept)
    (hinjExcluded : Function.Injective pickExcluded)
    (hdisjoint : ∀ kept excluded, pickKept kept ≠ pickExcluded excluded) :
    ((projectionOfDesign design).submatrix pickExcluded pickExcluded).det
      = ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (projectionOfDesign design).submatrix pickKept pickKept).det :=
  det_submatrix_eq_det_one_sub_complement design hinjExcluded hinjKept
    fun excluded kept => (hdisjoint kept excluded).symm

/-! ## The selection measure's exact pair correlation

The pair level of the law prices the correlation of the selection measure.  The
through-pair mass is `pairMinorAt P a b` and the one-point masses are the two
leverages, so the covariance defect is exactly the squared projection entry. -/

/-- **NEGATIVE ASSOCIATION, EXACTLY.**  The through-pair mass falls short of the
product of the two one-point masses by exactly the squared projection entry.  The
selection measure is negatively associated, and the defect is named. -/
theorem pairMinorAt_sub_diagonal_product (form : Matrix (Fin size) (Fin size) ℝ)
    (first second : Fin size) :
    pairMinorAt form first second - form first first * form second second
      = -(form first second ^ 2) := by
  rw [pairMinorAt]
  ring

/-- The through-pair mass never passes the product of the one-point masses. -/
theorem pairMinorAt_le_diagonal_product (form : Matrix (Fin size) (Fin size) ℝ)
    (first second : Fin size) :
    pairMinorAt form first second ≤ form first first * form second second := by
  have hdefect := pairMinorAt_sub_diagonal_product form first second
  nlinarith [sq_nonneg (form first second)]

/-- **THE TWO HALVES OF THE PAIR MARGINAL DIFFER BY A LINEAR TERM.**  The complement
mass minus the through-pair mass is `1 - P a a - P b b`, and the pairing cancels
out of the difference entirely.  So the two halves carry the SAME off-diagonal
information, and only the diagonal separates them. -/
theorem pairMinorAt_one_sub_sub_pairMinorAt (design : WeightedDesign size rank)
    (first second : Fin size) (hne : first ≠ second) :
    pairMinorAt (1 - projectionOfDesign design) first second
        - pairMinorAt (projectionOfDesign design) first second
      = 1 - projectionOfDesign design first first
        - projectionOfDesign design second second := by
  have hoff : (1 - projectionOfDesign design) first second
      = -projectionOfDesign design first second := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne]
    ring
  rw [pairMinorAt, pairMinorAt, hoff, Matrix.sub_apply, Matrix.sub_apply,
    Matrix.one_apply_eq, Matrix.one_apply_eq]
  ring

/-! ## What the duality buys a cell

A determinant cell reads `det P_S` against the weights on `S`.  The duality says
that number is also `det (1 - P)_{Sᶜ}`.  So a bound proved on one side transports
to the other with no new work, and the two sides read DISJOINT label sets. -/

/-- **THE DUAL CELL.**  A determinant cell firing at a triple can be certified from
the complementary projection's block on the complementary triple.  The hypothesis
and the conclusion read disjoint label sets. -/
theorem posDef_projectionBlock_of_weights_lt_complement_det (design : WeightedDesign 6 3)
    {pickKept pickExcluded : Fin 3 → Fin 6} (hinjKept : Function.Injective pickKept)
    (hinjExcluded : Function.Injective pickExcluded)
    (hdisjoint : ∀ kept excluded, pickKept kept ≠ pickExcluded excluded)
    (hweights : ∀ label : Fin 6, design.weight label
      < (((1 : Matrix (Fin 6) (Fin 6) ℝ)
          - projectionOfDesign design).submatrix pickExcluded pickExcluded).det) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ (subsetSum design selected - 1).PosDef := by
  refine exists_posDef_subsetSum_of_forall_weight_lt_det design pickKept hinjKept fun slot => ?_
  rw [det_submatrix_eq_det_complementProjection design hinjKept hinjExcluded hdisjoint]
  exact hweights (pickKept slot)

/-- **THE DUAL CAP.**  Both complementary minors lie in the unit interval, and the
duality forces each to be one minus a quantity read on the other side.  So a
triple whose complementary block is nearly the identity carries almost no
determinantal weight. -/
theorem det_submatrix_le_one_sub_of_complement (design : WeightedDesign 6 3)
    {pickKept pickExcluded : Fin 3 → Fin 6} (hinjKept : Function.Injective pickKept)
    (hinjExcluded : Function.Injective pickExcluded)
    (hdisjoint : ∀ kept excluded, pickKept kept ≠ pickExcluded excluded) :
    ((projectionOfDesign design).submatrix pickKept pickKept).det
      + ((projectionOfDesign design).submatrix pickExcluded pickExcluded).det
      = ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (projectionOfDesign design).submatrix pickExcluded pickExcluded).det
        + ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (projectionOfDesign design).submatrix pickKept pickKept).det := by
  rw [det_submatrix_eq_det_one_sub_complement design hinjKept hinjExcluded hdisjoint,
    det_one_sub_submatrix_eq_det_complement design hinjKept hinjExcluded hdisjoint]

end Gtz
