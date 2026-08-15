import Gtz.Design.ExcessThreshold
import Gtz.Wave.KFourOutsideDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# The polarised moment law for two outside labels

The scalar cross-energy identity reads one outside label at a time and loses
the mixed term between the two labels omitted by a card-four selection.  This
module polarises that identity.

For a positive-definite base let `dual(base,t)` be the inverse-gap image of the
scaled direction at `t`.  The mass moment pairing of two such dual vectors is
exactly the weight-weighted mixed cross sum over all labels.  The unweighted
mixed cross sum over the selected labels is the inverse cross of the two target
labels plus that moment pairing.

Together with `KFourOutsideDecomposition`, both outside columns and their mixed
moment are therefore controlled by the inverse data of the selected four-set.
This retains the two-by-two information discarded by the existing scalar
refusal bound.
-/

namespace Gtz

open Finset Matrix

/-- The inverse-gap image of one scaled chart direction. -/
noncomputable def chartLadderDual {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (base : Finset (Fin size)) (label : Fin size) : Fin 3 → ℝ :=
  (directionChartGap direction mass weight base)⁻¹ *ᵥ
    chartLadderVector direction mass weight label

/-- Inverting a positive-definite gap preserves independence of a pair of
scaled ladder vectors. -/
theorem chartLadderDual_pair_independent_of_ladderVector_pair_independent
    {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (base : Finset (Fin size))
    (hpd : (directionChartGap direction mass weight base).PosDef)
    (left right : Fin size)
    (hindependent : ∀ leftCoeff rightCoeff : ℝ,
      leftCoeff • chartLadderVector direction mass weight left
          + rightCoeff • chartLadderVector direction mass weight right = 0 →
        leftCoeff = 0 ∧ rightCoeff = 0) :
    ∀ leftCoeff rightCoeff : ℝ,
      leftCoeff • chartLadderDual direction mass weight base left
          + rightCoeff • chartLadderDual direction mass weight base right = 0 →
        leftCoeff = 0 ∧ rightCoeff = 0 := by
  intro leftCoeff rightCoeff hzero
  let gap := directionChartGap direction mass weight base
  have hunit : IsUnit gap.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  have hsolve : ∀ label,
      gap *ᵥ chartLadderDual direction mass weight base label
        = chartLadderVector direction mass weight label := by
    intro label
    rw [chartLadderDual, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv gap hunit, Matrix.one_mulVec]
  have himage := congrArg (fun vector : Fin 3 → ℝ => gap *ᵥ vector) hzero
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_zero, hsolve left, hsolve right] at himage
  exact hindependent leftCoeff rightCoeff himage

/-- Distinct K4 edge directions are linearly independent in pairs. -/
theorem kFourDirection_pair_independent {left right : Fin 6} (hne : left ≠ right) :
    ∀ leftCoeff rightCoeff : ℝ,
      leftCoeff • kFourDirection left + rightCoeff • kFourDirection right = 0 →
        leftCoeff = 0 ∧ rightCoeff = 0 := by
  intro leftCoeff rightCoeff hzero
  have hzero0 := congrFun hzero 0
  have hzero1 := congrFun hzero 1
  have hzero2 := congrFun hzero 2
  fin_cases left <;> fin_cases right <;>
    simp_all [kFourDirection]

/-- Positive ladder scaling preserves the pair independence of distinct K4
directions. -/
theorem kFour_chartLadderVector_pair_independent
    (point : DirectionChartPoint 6) {left right : Fin 6} (hne : left ≠ right) :
    ∀ leftCoeff rightCoeff : ℝ,
      leftCoeff • chartLadderVector kFourDirection point.mass point.weight left
          + rightCoeff • chartLadderVector kFourDirection point.mass point.weight right = 0 →
        leftCoeff = 0 ∧ rightCoeff = 0 := by
  intro leftCoeff rightCoeff hzero
  have hleftRoot : 0 < Real.sqrt (point.mass left / point.weight left) :=
    Real.sqrt_pos.2 (div_pos (point.mass_pos left) (point.weight_pos left))
  have hrightRoot : 0 < Real.sqrt (point.mass right / point.weight right) :=
    Real.sqrt_pos.2 (div_pos (point.mass_pos right) (point.weight_pos right))
  have hscaled :
      (leftCoeff * Real.sqrt (point.mass left / point.weight left)) •
          kFourDirection left
        + (rightCoeff * Real.sqrt (point.mass right / point.weight right)) •
          kFourDirection right = 0 := by
    simpa only [chartLadderVector, smul_smul, smul_eq_mul] using hzero
  have hcoeff := kFourDirection_pair_independent hne _ _ hscaled
  constructor
  · exact (mul_eq_zero.mp hcoeff.1).resolve_right (ne_of_gt hleftRoot)
  · exact (mul_eq_zero.mp hcoeff.2).resolve_right (ne_of_gt hrightRoot)

/-- The polarised mass-moment form at two whitened chart directions. -/
noncomputable def chartMomentCross {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (base : Finset (Fin size)) (left right : Fin size) : ℝ :=
  chartLadderDual direction mass weight base left ⬝ᵥ
    ((∑ label, mass label • atomMatrix (direction label)) *ᵥ
      chartLadderDual direction mass weight base right)

/-- **THE POLARISED MOMENT IDENTITY.**  The mixed mass-moment form of two
whitened labels is the weight-weighted mixed cross sum over every label. -/
theorem chartMomentCross_eq_weighted_cross_mul {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) (left right : Fin size) :
    chartMomentCross direction mass weight base left right
      = ∑ label, weight label
          * chartLadderCross direction mass weight base label left
          * chartLadderCross direction mass weight base label right := by
  set dualLeft := chartLadderDual direction mass weight base left with hdualLeft
  set dualRight := chartLadderDual direction mass weight base right with hdualRight
  rw [chartMomentCross, ← hdualLeft, ← hdualRight, Matrix.sum_mulVec,
    dotProduct_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    dotProduct_atomMatrix_mulVec_pair]
  have hweightNe : weight label ≠ 0 := (hweight label).ne'
  have hroot : Real.sqrt (mass label / weight label) ^ 2
      = mass label / weight label :=
    Real.sq_sqrt (div_nonneg (hmass label).le (hweight label).le)
  have hcrossLeft : chartLadderCross direction mass weight base label left
      = Real.sqrt (mass label / weight label)
          * (direction label ⬝ᵥ dualLeft) := by
    rw [chartLadderCross, chartLadderVector, smul_dotProduct, smul_eq_mul,
      hdualLeft, chartLadderDual]
  have hcrossRight : chartLadderCross direction mass weight base label right
      = Real.sqrt (mass label / weight label)
          * (direction label ⬝ᵥ dualRight) := by
    rw [chartLadderCross, chartLadderVector, smul_dotProduct, smul_eq_mul,
      hdualRight, chartLadderDual]
  rw [hcrossLeft, hcrossRight]
  calc
    mass label *
          ((direction label ⬝ᵥ dualLeft) * (direction label ⬝ᵥ dualRight))
        = weight label * (mass label / weight label) *
            ((direction label ⬝ᵥ dualLeft) * (direction label ⬝ᵥ dualRight)) := by
              field_simp
    _ = weight label * Real.sqrt (mass label / weight label) ^ 2 *
            ((direction label ⬝ᵥ dualLeft) * (direction label ⬝ᵥ dualRight)) := by
              rw [hroot]
    _ = weight label *
          (Real.sqrt (mass label / weight label) *
            (direction label ⬝ᵥ dualLeft)) *
          (Real.sqrt (mass label / weight label) *
            (direction label ⬝ᵥ dualRight)) := by ring

/-- The polarised moment form is symmetric. -/
theorem chartMomentCross_comm {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (base : Finset (Fin size)) (left right : Fin size) :
    chartMomentCross direction mass weight base left right
      = chartMomentCross direction mass weight base right left := by
  unfold chartMomentCross
  apply dotProduct_mulVec_comm_of_transpose_eq
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.transpose_smul, atomMatrix_transpose]

/-- Strict Cauchy--Schwarz for the bilinear form of a positive-definite
matrix, in a division-free form tailored to two outside directions.  Equality
would make `selfRight • left - cross • right` a nonzero null vector. -/
theorem form_cross_sq_lt_self_mul_of_posDef_of_pair_independent {dim : ℕ}
    {form : Matrix (Fin dim) (Fin dim) ℝ} (hform : form.PosDef)
    {left right : Fin dim → ℝ}
    (hindependent : ∀ leftCoeff rightCoeff : ℝ,
      leftCoeff • left + rightCoeff • right = 0 →
        leftCoeff = 0 ∧ rightCoeff = 0) :
    (left ⬝ᵥ (form *ᵥ right)) ^ 2
      < (left ⬝ᵥ (form *ᵥ left)) * (right ⬝ᵥ (form *ᵥ right)) := by
  have hsymm : formᵀ = form := PosDef.transpose_eq hform
  have hnonneg : ∀ vector : Fin dim → ℝ,
      0 ≤ vector ⬝ᵥ (form *ᵥ vector) := by
    intro vector
    have hstep := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hform.posSemidef).2 vector
    rwa [star_trivial] at hstep
  have hrightNe : right ≠ 0 := by
    intro hright
    have hcoeff := hindependent 0 1 (by rw [hright]; simp)
    exact one_ne_zero hcoeff.2
  have hrightPos : 0 < right ⬝ᵥ (form *ᵥ right) := by
    have hstep := (Matrix.posDef_iff_dotProduct_mulVec.mp hform).2 hrightNe
    rwa [star_trivial] at hstep
  have hquad : ∀ shift : ℝ,
      0 ≤ (right ⬝ᵥ (form *ᵥ right)) * (shift * shift)
        + 2 * (left ⬝ᵥ (form *ᵥ right)) * shift
        + left ⬝ᵥ (form *ᵥ left) := by
    intro shift
    have hstep := hnonneg (left + shift • right)
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
      dotProduct_add, dotProduct_add, smul_dotProduct, smul_dotProduct,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul,
      dotProduct_mulVec_comm_of_transpose_eq hsymm right left] at hstep
    nlinarith
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  have hweak : (left ⬝ᵥ (form *ᵥ right)) ^ 2
      ≤ (left ⬝ᵥ (form *ᵥ left)) * (right ⬝ᵥ (form *ᵥ right)) := by
    nlinarith
  refine lt_of_le_of_ne hweak ?_
  intro hequality
  let selfRight := right ⬝ᵥ (form *ᵥ right)
  let cross := left ⬝ᵥ (form *ᵥ right)
  let witness := selfRight • left + (-cross) • right
  have hwitnessNe : witness ≠ 0 := by
    intro hwitness
    have hcoeff := hindependent selfRight (-cross) hwitness
    exact (ne_of_gt hrightPos) hcoeff.1
  have hwitnessPos : 0 < witness ⬝ᵥ (form *ᵥ witness) := by
    have hstep := (Matrix.posDef_iff_dotProduct_mulVec.mp hform).2 hwitnessNe
    rwa [star_trivial] at hstep
  have hwitnessForm : witness ⬝ᵥ (form *ᵥ witness)
      = selfRight *
          ((left ⬝ᵥ (form *ᵥ left)) * selfRight - cross ^ 2) := by
    simp only [witness, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
      dotProduct_add, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [dotProduct_mulVec_comm_of_transpose_eq hsymm right left]
    ring
  rw [hwitnessForm] at hwitnessPos
  dsimp only [selfRight, cross] at hwitnessPos
  nlinarith

/-- The two outside dual directions have a strictly positive moment
determinant whenever they are linearly independent.  This is the determinant
arm of the two-by-two refusal system. -/
theorem chartMomentCross_sq_lt_self_mul_self {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (base : Finset (Fin size)) (left right : Fin size)
    (hmoment : (∑ label, mass label • atomMatrix (direction label)).PosDef)
    (hindependent : ∀ leftCoeff rightCoeff : ℝ,
      leftCoeff • chartLadderDual direction mass weight base left
          + rightCoeff • chartLadderDual direction mass weight base right = 0 →
        leftCoeff = 0 ∧ rightCoeff = 0) :
    chartMomentCross direction mass weight base left right ^ 2
      < chartMomentCross direction mass weight base left left
          * chartMomentCross direction mass weight base right right := by
  exact form_cross_sq_lt_self_mul_of_posDef_of_pair_independent hmoment hindependent

/-- For distinct K4 labels, positive ladder scaling and inversion discharge
the independence hypothesis automatically. -/
theorem kFour_chartMomentCross_sq_lt_self_mul_self
    (point : DirectionChartPoint 6) (base : Finset (Fin 6))
    (hpd : (directionChartGap kFourDirection point.mass point.weight base).PosDef)
    {left right : Fin 6} (hne : left ≠ right) :
    chartMomentCross kFourDirection point.mass point.weight base left right ^ 2
      < chartMomentCross kFourDirection point.mass point.weight base left left
          * chartMomentCross kFourDirection point.mass point.weight base right right := by
  apply chartMomentCross_sq_lt_self_mul_self kFourDirection point.mass point.weight
    base left right (posDef_massMoment_kFourDirection point)
  exact chartLadderDual_pair_independent_of_ladderVector_pair_independent
    kFourDirection point.mass point.weight base hpd left right
      (kFour_chartLadderVector_pair_independent point hne)

/-- **THE POLARISED CROSS-ENERGY IDENTITY.**  The mixed cross sum over the
selected base is the inverse cross of the two target labels plus their mixed
mass-moment form.  The diagonal specialization is the exact scalar
cross-energy law. -/
theorem crossEnergy_pair_eq_cross_add_moment {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size))
    (hpd : (directionChartGap direction mass weight base).PosDef)
    (left right : Fin size) :
    ∑ source ∈ base,
        chartLadderCross direction mass weight base source left
          * chartLadderCross direction mass weight base source right
      = chartLadderCross direction mass weight base left right
        + chartMomentCross direction mass weight base left right := by
  set gapMat := directionChartGap direction mass weight base with hgapMat
  set scaledLeft := chartLadderVector direction mass weight left with hscaledLeft
  set scaledRight := chartLadderVector direction mass weight right with hscaledRight
  set dualLeft := gapMat⁻¹ *ᵥ scaledLeft with hdualLeft
  set dualRight := gapMat⁻¹ *ᵥ scaledRight with hdualRight
  have hunit : IsUnit gapMat.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  have hgapLeft : gapMat *ᵥ dualLeft = scaledLeft := by
    rw [hdualLeft, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
  have hgapRight : gapMat *ᵥ dualRight = scaledRight := by
    rw [hdualRight, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
  have hgapSymm : gapMatᵀ = gapMat := by
    rw [hgapMat]
    exact directionChartGap_transpose direction mass weight base
  have hgapPair : dualLeft ⬝ᵥ (gapMat *ᵥ dualRight)
      = chartLadderCross direction mass weight base left right := by
    calc
      dualLeft ⬝ᵥ (gapMat *ᵥ dualRight)
          = dualRight ⬝ᵥ (gapMat *ᵥ dualLeft) :=
              dotProduct_mulVec_comm_of_transpose_eq hgapSymm dualLeft dualRight
      _ = dualRight ⬝ᵥ scaledLeft := by rw [hgapLeft]
      _ = scaledLeft ⬝ᵥ dualRight := dotProduct_comm _ _
      _ = chartLadderCross direction mass weight base left right := by
        rw [chartLadderCross, ← hdualRight, ← hscaledLeft]
  have hselectedPair : dualLeft ⬝ᵥ
      ((∑ label ∈ base,
          atomMatrix (chartLadderVector direction mass weight label)) *ᵥ dualRight)
      = ∑ source ∈ base,
          chartLadderCross direction mass weight base source left
            * chartLadderCross direction mass weight base source right := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun source _ => ?_
    rw [dotProduct_atomMatrix_mulVec_pair]
    rw [chartLadderCross, chartLadderCross, ← hdualLeft, ← hdualRight]
  have hsplit : dualLeft ⬝ᵥ (gapMat *ᵥ dualRight)
      = dualLeft ⬝ᵥ
          ((∑ label ∈ base,
            atomMatrix (chartLadderVector direction mass weight label)) *ᵥ dualRight)
        - chartMomentCross direction mass weight base left right := by
    rw [hgapMat, directionChartGap_eq_ladderSum_sub_moment direction mass weight
      hmass hweight base, Matrix.sub_mulVec, dotProduct_sub,
      chartMomentCross, chartLadderDual, chartLadderDual,
      ← hgapMat, ← hdualLeft, ← hdualRight]
  rw [hgapPair, hselectedPair] at hsplit
  linarith

/-- **THE K4 TWO-OUTSIDE DETERMINANT LAW.**  After subtracting the inverse
cross and the two pivots, the selected cross Gram of two distinct labels has
strictly positive determinant.  This is the exact `2x2` information lost by
the old one-target cross-energy inequality. -/
theorem kFour_twoOutside_crossEnergy_determinant_pos
    (point : DirectionChartPoint 6) (base : Finset (Fin 6))
    (hpd : (directionChartGap kFourDirection point.mass point.weight base).PosDef)
    {left right : Fin 6} (hne : left ≠ right) :
    (∑ source ∈ base,
        chartLadderCross kFourDirection point.mass point.weight base source left
          * chartLadderCross kFourDirection point.mass point.weight base source right
        - chartLadderCross kFourDirection point.mass point.weight base left right) ^ 2
      < ((∑ source ∈ base,
            chartLadderCross kFourDirection point.mass point.weight base source left ^ 2)
          - chartLadderPivot kFourDirection point.mass point.weight base left)
        * ((∑ source ∈ base,
            chartLadderCross kFourDirection point.mass point.weight base source right ^ 2)
          - chartLadderPivot kFourDirection point.mass point.weight base right) := by
  have hstrict := kFour_chartMomentCross_sq_lt_self_mul_self point base hpd hne
  have hmixed := crossEnergy_pair_eq_cross_add_moment kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos base hpd left right
  have hleft := crossEnergy_pair_eq_cross_add_moment kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos base hpd left left
  have hright := crossEnergy_pair_eq_cross_add_moment kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos base hpd right right
  rw [chartLadderCross_self kFourDirection point.mass point.weight point.mass_pos
    point.weight_pos base left] at hleft
  rw [chartLadderCross_self kFourDirection point.mass point.weight point.mass_pos
    point.weight_pos base right] at hright
  simp only [pow_two] at hleft hright ⊢
  have hmixed' :
      (∑ source ∈ base,
          chartLadderCross kFourDirection point.mass point.weight base source left
            * chartLadderCross kFourDirection point.mass point.weight base source right)
        - chartLadderCross kFourDirection point.mass point.weight base left right
      = chartMomentCross kFourDirection point.mass point.weight base left right := by
    linarith
  have hleft' :
      (∑ source ∈ base,
          chartLadderCross kFourDirection point.mass point.weight base source left
            * chartLadderCross kFourDirection point.mass point.weight base source left)
        - chartLadderPivot kFourDirection point.mass point.weight base left
      = chartMomentCross kFourDirection point.mass point.weight base left left := by
    linarith
  have hright' :
      (∑ source ∈ base,
          chartLadderCross kFourDirection point.mass point.weight base source right
            * chartLadderCross kFourDirection point.mass point.weight base source right)
        - chartLadderPivot kFourDirection point.mass point.weight base right
      = chartMomentCross kFourDirection point.mass point.weight base right right := by
    linarith
  rw [hmixed', hleft', hright']
  simpa only [pow_two] using hstrict

end Gtz
