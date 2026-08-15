/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Design.StarCorankClosure
import Gtz.Design.NearPencilTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The complement form law

Every landed criterion reads the gap of a selection at a probe in the rank-three
space.  This module reads a selection on the labels it OMITS instead.

Write `U` for the full-selection gap and, for a set `omitted` of labels,

  `gap (univ \ omitted) = U - omittedBoostSum omitted`.

The `complementForm` at a coefficient vector `coeff` supported on `omitted` is

  `∑ (mass/weight) * coeff^2  -  x ⬝ U⁻¹ x`,   `x = ∑ (mass/weight) * coeff • direction`.

**THE COMPLEMENT FORM LAW.**  The complement selection `univ \ omitted` has a
positive definite gap exactly when the complement form is positive at every
coefficient vector that is nonzero somewhere on `omitted`.  The number of
conditions drops from the rank-three probe space to the size of `omitted`.

The whole content is one completed square, `complementForm_bracket`: at every
probe the bracket

  `∑ (mass/weight) * coeff^2 - 2 * (x ⬝ probe) + probe ⬝ U probe`

equals a residual sum over the omitted labels plus the complement gap form at
the same probe.  Choosing the probe to kill the residual gives one direction,
and evaluating at the dual `U⁻¹ x` gives the other.

Nothing here is special to a wall, to a chart, or to a direction family.  The
statements take an arbitrary `size`, an arbitrary `direction`, and only ask that
the full-selection gap is positive definite.
-/

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## 1. The omitted boost sum -/

/-- The boost sum over the omitted labels. -/
noncomputable def omittedBoostSum (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ label ∈ omitted, (mass label / weight label) • atomMatrix (direction label)

/-- The complement selection removes exactly the omitted boost sum. -/
theorem directionChartGap_compl_eq (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size)) :
    directionChartGap direction mass weight (Finset.univ \ omitted)
      = directionChartGap direction mass weight Finset.univ
        - omittedBoostSum direction mass weight omitted := by
  have hstep := directionChartGap_sdiff direction mass weight Finset.univ
    (Finset.univ \ omitted)
  have hleft : Finset.univ \ (Finset.univ \ omitted) = omitted := by
    ext label
    simp
  have hright : (Finset.univ \ omitted) \ (Finset.univ : Finset (Fin size)) = ∅ := by
    ext label
    simp
  rw [hleft, hright, Finset.sum_empty, sub_zero] at hstep
  rw [omittedBoostSum, ← hstep]
  abel

/-- The quadratic form of the omitted boost sum is the boosted sum of squared
readings. -/
theorem quadForm_omittedBoostSum (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size)) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (omittedBoostSum direction mass weight omitted *ᵥ probe)
      = ∑ label ∈ omitted, (mass label / weight label)
          * (direction label ⬝ᵥ probe) * (direction label ⬝ᵥ probe) := by
  rw [omittedBoostSum]
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, dotProduct_comm probe (direction label)]
  ring

/-! ## 2. The complement form -/

/-- The rank-three combination the omitted labels contribute at a coefficient
vector. -/
noncomputable def omittedCombination (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size)) (coeff : Fin size → ℝ) :
    Fin 3 → ℝ :=
  ∑ label ∈ omitted, ((mass label / weight label) * coeff label) • direction label

/-- Reading the omitted combination at a probe. -/
theorem dotProduct_omittedCombination (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size)) (coeff : Fin size → ℝ)
    (probe : Fin 3 → ℝ) :
    omittedCombination direction mass weight omitted coeff ⬝ᵥ probe
      = ∑ label ∈ omitted, (mass label / weight label) * coeff label
          * (direction label ⬝ᵥ probe) := by
  rw [omittedCombination, sum_dotProduct]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [smul_dotProduct, smul_eq_mul]

/-- **The complement form.**  The boosted square sum over the omitted labels,
less the inverse reading of the combination they produce. -/
noncomputable def complementForm (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size)) (coeff : Fin size → ℝ) :
    ℝ :=
  (∑ label ∈ omitted, (mass label / weight label) * coeff label * coeff label)
    - omittedCombination direction mass weight omitted coeff ⬝ᵥ
        ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ
          omittedCombination direction mass weight omitted coeff)

/-! ## 3. The completed square -/

/-- **THE COMPLETED SQUARE.**  At every probe the bracket splits into the
residual sum over the omitted labels and the complement gap form.  This is the
whole content of the law, and it involves no inverse. -/
theorem complementForm_bracket (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size)) (coeff : Fin size → ℝ)
    (probe : Fin 3 → ℝ) :
    (∑ label ∈ omitted, (mass label / weight label) * coeff label * coeff label)
        - 2 * (omittedCombination direction mass weight omitted coeff ⬝ᵥ probe)
        + probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe)
      = (∑ label ∈ omitted, (mass label / weight label)
            * (coeff label - direction label ⬝ᵥ probe)
            * (coeff label - direction label ⬝ᵥ probe))
        + probe ⬝ᵥ (directionChartGap direction mass weight (Finset.univ \ omitted)
            *ᵥ probe) := by
  have hgap := directionChartGap_compl_eq direction mass weight omitted
  rw [hgap, Matrix.sub_mulVec, dotProduct_sub, quadForm_omittedBoostSum,
    dotProduct_omittedCombination]
  have hexpand : (∑ label ∈ omitted, (mass label / weight label)
        * (coeff label - direction label ⬝ᵥ probe)
        * (coeff label - direction label ⬝ᵥ probe))
      = (∑ label ∈ omitted, (mass label / weight label) * coeff label * coeff label)
        - 2 * (∑ label ∈ omitted, (mass label / weight label) * coeff label
            * (direction label ⬝ᵥ probe))
        + ∑ label ∈ omitted, (mass label / weight label)
            * (direction label ⬝ᵥ probe) * (direction label ⬝ᵥ probe) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun label _ => ?_
    ring
  rw [hexpand]
  ring

/-! ## 4. The variational bound for the inverse form -/

/-- The inverse form dominates every linear-minus-quadratic probe value.
Reproved here because the tree's copies sit downstream in `Gtz.Certificates`. -/
theorem inverseForm_ge_probe {gramMat : Matrix (Fin 3) (Fin 3) ℝ}
    (hposDef : gramMat.PosDef) (source probe : Fin 3 → ℝ) :
    2 * (source ⬝ᵥ probe) - probe ⬝ᵥ (gramMat *ᵥ probe)
      ≤ source ⬝ᵥ (gramMat⁻¹ *ᵥ source) := by
  have hdet : IsUnit gramMat.det := isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  have htranspose : gramMatᵀ = gramMat := transpose_eq_of_isHermitian hposDef.1
  set dual : Fin 3 → ℝ := gramMat⁻¹ *ᵥ source with hdual
  have hmulDual : gramMat *ᵥ dual = source := by
    rw [hdual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv gramMat hdet,
      Matrix.one_mulVec]
  have hformNonneg : 0 ≤ (probe - dual) ⬝ᵥ (gramMat *ᵥ (probe - dual)) := by
    have hstep := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hposDef.posSemidef).2
      (probe - dual)
    rwa [star_trivial] at hstep
  have hexpand : (probe - dual) ⬝ᵥ (gramMat *ᵥ (probe - dual))
      = probe ⬝ᵥ (gramMat *ᵥ probe) - probe ⬝ᵥ (gramMat *ᵥ dual)
        - dual ⬝ᵥ (gramMat *ᵥ probe) + dual ⬝ᵥ (gramMat *ᵥ dual) := by
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct]
    ring
  have hcross : probe ⬝ᵥ (gramMat *ᵥ dual) = source ⬝ᵥ probe := by
    rw [hmulDual, dotProduct_comm]
  have hcross' : dual ⬝ᵥ (gramMat *ᵥ probe) = source ⬝ᵥ probe := by
    rw [dot_mulVec_comm htranspose, hmulDual, dotProduct_comm]
  have hself : dual ⬝ᵥ (gramMat *ᵥ dual) = source ⬝ᵥ (gramMat⁻¹ *ᵥ source) := by
    rw [hmulDual, dotProduct_comm, hdual]
  rw [hexpand, hcross, hcross', hself] at hformNonneg
  linarith [hformNonneg]

/-- The bound of `inverseForm_ge_probe` is attained at the dual probe. -/
theorem inverseForm_eq_dual {gramMat : Matrix (Fin 3) (Fin 3) ℝ}
    (hposDef : gramMat.PosDef) (source : Fin 3 → ℝ) :
    source ⬝ᵥ (gramMat⁻¹ *ᵥ source)
      = 2 * (source ⬝ᵥ (gramMat⁻¹ *ᵥ source))
        - (gramMat⁻¹ *ᵥ source) ⬝ᵥ (gramMat *ᵥ (gramMat⁻¹ *ᵥ source)) := by
  have hdet : IsUnit gramMat.det := isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  have hmulDual : gramMat *ᵥ (gramMat⁻¹ *ᵥ source) = source := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv gramMat hdet, Matrix.one_mulVec]
  rw [hmulDual, dotProduct_comm (gramMat⁻¹ *ᵥ source) source]
  ring

/-! ## 5. The complement form law -/

/-- **THE PRODUCER.**  If the complement form is positive at every coefficient
vector nonzero somewhere on the omitted labels, the complement selection has a
positive definite gap.  Generic in the size and in the direction family. -/
theorem posDef_directionChartGap_compl_of_complementForm_pos
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (omitted : Finset (Fin size))
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hform : ∀ coeff : Fin size → ℝ, (∃ label ∈ omitted, coeff label ≠ 0) →
      0 < complementForm direction mass weight omitted coeff) :
    (directionChartGap direction mass weight (Finset.univ \ omitted)).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (directionChartGap_transpose _ _ _ _),
      fun probe hprobe => ?_⟩
  rw [star_trivial]
  set coeff : Fin size → ℝ := fun label => direction label ⬝ᵥ probe with hcoeff
  by_cases hzero : ∃ label ∈ omitted, coeff label ≠ 0
  · have hpos := hform coeff hzero
    have hbound := inverseForm_ge_probe huniv
      (omittedCombination direction mass weight omitted coeff) probe
    have hbracket := complementForm_bracket direction mass weight omitted coeff probe
    have hresidual : (∑ label ∈ omitted, (mass label / weight label)
        * (coeff label - direction label ⬝ᵥ probe)
        * (coeff label - direction label ⬝ᵥ probe)) = 0 := by
      refine Finset.sum_eq_zero fun label _ => ?_
      rw [hcoeff]
      ring
    rw [hresidual, zero_add] at hbracket
    rw [complementForm] at hpos
    linarith
  · push Not at hzero
    have hreading : ∀ label ∈ omitted, direction label ⬝ᵥ probe = 0 := by
      intro label hlabel
      have := hzero label hlabel
      rwa [hcoeff] at this
    have hgap := directionChartGap_compl_eq direction mass weight omitted
    have huniPos := (Matrix.posDef_iff_dotProduct_mulVec.mp huniv).2 hprobe
    rw [star_trivial] at huniPos
    have hboost : probe ⬝ᵥ (omittedBoostSum direction mass weight omitted *ᵥ probe) = 0 := by
      rw [quadForm_omittedBoostSum]
      refine Finset.sum_eq_zero fun label hlabel => ?_
      rw [hreading label hlabel]
      ring
    rw [hgap, Matrix.sub_mulVec, dotProduct_sub, hboost, sub_zero]
    exact huniPos

/-- **THE CONVERSE.**  A positive definite complement selection forces the
complement form positive at every coefficient vector nonzero somewhere on the
omitted labels. -/
theorem complementForm_pos_of_posDef_directionChartGap_compl
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (omitted : Finset (Fin size))
    (hboost : ∀ label ∈ omitted, 0 < mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hcompl : (directionChartGap direction mass weight (Finset.univ \ omitted)).PosDef)
    (coeff : Fin size → ℝ) (hne : ∃ label ∈ omitted, coeff label ≠ 0) :
    0 < complementForm direction mass weight omitted coeff := by
  set gapUniv := directionChartGap direction mass weight Finset.univ with hgapUniv
  set source := omittedCombination direction mass weight omitted coeff with hsource
  set dual : Fin 3 → ℝ := gapUniv⁻¹ *ᵥ source with hdual
  have hdet : IsUnit gapUniv.det := isUnit_iff_ne_zero.mpr (ne_of_gt huniv.det_pos)
  have hmulDual : gapUniv *ᵥ dual = source := by
    rw [hdual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv gapUniv hdet,
      Matrix.one_mulVec]
  have hbracket := complementForm_bracket direction mass weight omitted coeff dual
  rw [← hsource, ← hgapUniv] at hbracket
  have heq := inverseForm_eq_dual huniv source
  rw [← hdual] at heq
  have hresidualNonneg : 0 ≤ ∑ label ∈ omitted, (mass label / weight label)
      * (coeff label - direction label ⬝ᵥ dual)
      * (coeff label - direction label ⬝ᵥ dual) := by
    refine Finset.sum_nonneg fun label hlabel => ?_
    rw [mul_assoc]
    exact mul_nonneg (hboost label hlabel).le (mul_self_nonneg _)
  by_cases hdualZero : dual = 0
  · have hsourceZero : source = 0 := by rw [← hmulDual, hdualZero, Matrix.mulVec_zero]
    have hsum : 0 < ∑ label ∈ omitted, (mass label / weight label) * coeff label * coeff label := by
      obtain ⟨witness, hwitness, hne'⟩ := hne
      refine Finset.sum_pos' (fun label hlabel => ?_) ⟨witness, hwitness, ?_⟩
      · rw [mul_assoc]
        exact mul_nonneg (hboost label hlabel).le (mul_self_nonneg _)
      · rw [mul_assoc]
        exact mul_pos (hboost witness hwitness) (mul_self_pos.mpr hne')
    rw [complementForm, ← hsource, hsourceZero]
    simpa using hsum
  · have hcomplPos := (Matrix.posDef_iff_dotProduct_mulVec.mp hcompl).2 hdualZero
    rw [star_trivial] at hcomplPos
    have hform : complementForm direction mass weight omitted coeff
        = (∑ label ∈ omitted, (mass label / weight label)
            * (coeff label - direction label ⬝ᵥ dual)
            * (coeff label - direction label ⬝ᵥ dual))
          + dual ⬝ᵥ (directionChartGap direction mass weight (Finset.univ \ omitted)
              *ᵥ dual) := by
      rw [complementForm, ← hsource, ← hgapUniv, ← hdual]
      linarith [hbracket, heq]
    rw [hform]
    linarith

/-- **THE COMPLEMENT FORM LAW.**  Positive definiteness of a selection is
decided on the labels it omits. -/
theorem posDef_directionChartGap_compl_iff
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (omitted : Finset (Fin size))
    (hboost : ∀ label ∈ omitted, 0 < mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) :
    (directionChartGap direction mass weight (Finset.univ \ omitted)).PosDef
      ↔ ∀ coeff : Fin size → ℝ, (∃ label ∈ omitted, coeff label ≠ 0) →
          0 < complementForm direction mass weight omitted coeff :=
  ⟨fun hcompl coeff hne =>
    complementForm_pos_of_posDef_directionChartGap_compl direction mass weight omitted
      hboost huniv hcompl coeff hne,
   fun hform =>
    posDef_directionChartGap_compl_of_complementForm_pos direction mass weight omitted
      huniv hform⟩

/-- **The law in selection form.**  A selection has a positive definite gap
exactly when the complement form is positive at every coefficient vector nonzero
somewhere on its complement.  A card-three selection at size six is decided by
three coefficients rather than by a rank-three probe space. -/
theorem posDef_directionChartGap_iff_complementForm
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size))
    (hboost : ∀ label ∈ selectedᶜ, 0 < mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) :
    (directionChartGap direction mass weight selected).PosDef
      ↔ ∀ coeff : Fin size → ℝ, (∃ label ∈ selectedᶜ, coeff label ≠ 0) →
          0 < complementForm direction mass weight selectedᶜ coeff := by
  have hsel : Finset.univ \ selectedᶜ = selected := by
    ext label
    simp
  have hstep := posDef_directionChartGap_compl_iff direction mass weight selectedᶜ
    hboost huniv
  rwa [hsel] at hstep

end Gtz
