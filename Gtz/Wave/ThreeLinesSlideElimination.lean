/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Design.ThreeLinesAtlas

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The mass leverage of a chart label, and the dual reading of domination

Every landed cell for `Gtz.ChartTieFreeThreeLinesFundamentalDomain` compares the
selected excesses against the outside masses DIRECTLY.  That comparison has no
scale: the excess `m (1 - w) / w` and the mass `m` run over many orders of
magnitude at one chart point, and a cell built on their raw difference is blind
wherever the two ends separate.

This module changes coordinates.  The mass moment `L = sum_c m_c v_c v_c^T` is
positive definite at every chart point, so it supplies an inner product.  Read in
that inner product each label carries a MASS LEVERAGE

  `tau_c = m_c * (v_c . L^{-1} v_c)`,

a number in `(0, 1]`.  The six leverages total the rank three, while the six
weights total one.  Three results follow, and all three are new here.

* **The dual criterion.**  Domination by a triple is an inequality between the
  inverse-moment form of the triple and the diagonal `weight / mass`
  (`Gtz.posDef_directionChartGap_of_dualStrict`).  The transfer runs on one
  completed square for each label.  No inverse monotonicity, no Cauchy-Schwarz
  and no eigenvalue enters.
* **The veto.**  Each label of a strictly dominating triple carries leverage
  above its own weight (`Gtz.weight_lt_chartMassLeverage_of_posDef_gap`).  No
  triple that holds an under-levered label can dominate.
* **The counting law.**  At least three labels are over-levered, at EVERY chart
  point of EVERY direction family (`Gtz.three_le_card_overLevered`).  The veto
  therefore prunes the candidate list without ever emptying it.

On top of the criterion the module lands the leverage dominance cell: three
inequalities in the leverage coordinates, each one comparing a label's leverage
surplus against the masses of its two partners weighted by the cross pivots.
Every quantity there is bounded, because the leverages sit in `(0, 1]` and the
weights sum to one.

The module closes with the twenty brackets of the three-lines chart as integer
polynomials in the slide.
-/

namespace Gtz

open Matrix

section MassLeverage

variable {size : ℕ}

/-! ## 1.  The mass moment, the pivot and the leverage -/

/-- **The mass moment of a chart point.**  The Gram matrix of the directions
weighted by the masses. -/
noncomputable def chartMassMoment (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ label, mass label • atomMatrix (direction label)

theorem chartMassMoment_eq (direction : Fin size → (Fin 3 → ℝ)) (mass : Fin size → ℝ) :
    chartMassMoment direction mass = ∑ label, mass label • atomMatrix (direction label) := rfl

/-- **The mass pivot.**  Two directions read against the inverse mass moment. -/
noncomputable def chartMassPivot (direction : Fin size → (Fin 3 → ℝ)) (mass : Fin size → ℝ)
    (leftLabel rightLabel : Fin size) : ℝ :=
  direction leftLabel ⬝ᵥ ((chartMassMoment direction mass)⁻¹ *ᵥ direction rightLabel)

/-- **The mass leverage of a label.**  The statistical leverage of the label in
the mass moment.  The leverages total the rank and each one is at most one. -/
noncomputable def chartMassLeverage (direction : Fin size → (Fin 3 → ℝ)) (mass : Fin size → ℝ)
    (label : Fin size) : ℝ :=
  mass label * chartMassPivot direction mass label label

/-! ## 2.  Elementary readings -/

/-- A rank-one atom reads a probe by the square of one pairing. -/
theorem dotProduct_atomMatrix_self_form {dimension : ℕ} (atomVector probe : Fin dimension → ℝ) :
    probe ⬝ᵥ (atomMatrix atomVector *ᵥ probe) = (atomVector ⬝ᵥ probe) ^ 2 := by
  have hrow : atomMatrix atomVector *ᵥ probe = (atomVector ⬝ᵥ probe) • atomVector := by
    funext rowIndex
    simp only [Matrix.mulVec, atomMatrix, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply,
      smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun colIndex _ => by ring
  rw [hrow, dotProduct_smul, smul_eq_mul, dotProduct_comm probe atomVector, sq]

/-- The quadratic form of a weighted atom sum, over any support. -/
theorem dotProduct_sumAtom_mulVec (direction : Fin size → (Fin 3 → ℝ))
    (coefficient : Fin size → ℝ) (support : Finset (Fin size)) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((∑ label ∈ support, coefficient label • atomMatrix (direction label)) *ᵥ probe)
      = ∑ label ∈ support, coefficient label * (direction label ⬝ᵥ probe) ^ 2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_self_form]

/-- A symmetric matrix reads a pair of probes in either order. -/
theorem dotProduct_symmetric_mulVec {dimension : ℕ}
    {form : Matrix (Fin dimension) (Fin dimension) ℝ} (hsymmetric : formᵀ = form)
    (leftProbe rightProbe : Fin dimension → ℝ) :
    leftProbe ⬝ᵥ (form *ᵥ rightProbe) = rightProbe ⬝ᵥ (form *ᵥ leftProbe) := by
  have hentry : ∀ rowIndex colIndex, form colIndex rowIndex = form rowIndex colIndex := by
    intro rowIndex colIndex
    have hcongr := congrFun (congrFun hsymmetric rowIndex) colIndex
    simpa [Matrix.transpose_apply] using hcongr
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun rowIndex _ => Finset.sum_congr rfl fun colIndex _ => ?_
  rw [hentry colIndex rowIndex]
  ring

/-- The mass moment is symmetric. -/
theorem chartMassMoment_transpose (direction : Fin size → (Fin 3 → ℝ)) (mass : Fin size → ℝ) :
    (chartMassMoment direction mass)ᵀ = chartMassMoment direction mass := by
  rw [chartMassMoment, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.transpose_smul, atomMatrix_transpose]

/-- The inverse mass moment is symmetric. -/
theorem chartMassMomentInv_transpose (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) :
    ((chartMassMoment direction mass)⁻¹)ᵀ = (chartMassMoment direction mass)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, chartMassMoment_transpose]

/-- The pivot is symmetric in its two labels. -/
theorem chartMassPivot_comm (direction : Fin size → (Fin 3 → ℝ)) (mass : Fin size → ℝ)
    (leftLabel rightLabel : Fin size) :
    chartMassPivot direction mass leftLabel rightLabel
      = chartMassPivot direction mass rightLabel leftLabel := by
  rw [chartMassPivot, chartMassPivot,
    dotProduct_symmetric_mulVec (chartMassMomentInv_transpose direction mass)]

/-- Applying the moment after its inverse returns the probe. -/
theorem chartMassMoment_mulVec_inv_mulVec (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (hmoment : (chartMassMoment direction mass).PosDef)
    (target : Fin 3 → ℝ) :
    chartMassMoment direction mass *ᵥ ((chartMassMoment direction mass)⁻¹ *ᵥ target) = target := by
  have hunit : IsUnit (chartMassMoment direction mass).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hmoment.det_pos)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]

/-- Applying the inverse after the moment returns the probe. -/
theorem chartMassMomentInv_mulVec_mulVec (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (hmoment : (chartMassMoment direction mass).PosDef)
    (probe : Fin 3 → ℝ) :
    (chartMassMoment direction mass)⁻¹ *ᵥ (chartMassMoment direction mass *ᵥ probe) = probe := by
  have hunit : IsUnit (chartMassMoment direction mass).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hmoment.det_pos)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]

/-- The inverse form is nonnegative on the diagonal. -/
theorem chartMassPivot_self_nonneg (direction : Fin size → (Fin 3 → ℝ)) (mass : Fin size → ℝ)
    (hmoment : (chartMassMoment direction mass).PosDef) (label : Fin size) :
    0 ≤ chartMassPivot direction mass label label := by
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hmoment.inv.posSemidef).2
    (direction label)
  rw [star_trivial] at hform
  exact hform

/-- The inverse form is strictly positive on a nonzero direction. -/
theorem chartMassPivot_self_pos (direction : Fin size → (Fin 3 → ℝ)) (mass : Fin size → ℝ)
    (hmoment : (chartMassMoment direction mass).PosDef) {label : Fin size}
    (hdirection : direction label ≠ 0) :
    0 < chartMassPivot direction mass label label := by
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hmoment.inv).2 hdirection
  rw [star_trivial] at hform
  exact hform

/-! ## 3.  The Legendre inequality

The one inequality this module runs on.  It is a completed square, and it
replaces both inverse monotonicity and Cauchy-Schwarz. -/

/-- **The Legendre inequality.**  The moment form dominates every linear reading
minus the inverse form of that reading. -/
theorem legendre_le_dotProduct_massMoment (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (hmoment : (chartMassMoment direction mass).PosDef)
    (probe target : Fin 3 → ℝ) :
    2 * (target ⬝ᵥ probe) - target ⬝ᵥ ((chartMassMoment direction mass)⁻¹ *ᵥ target)
      ≤ probe ⬝ᵥ (chartMassMoment direction mass *ᵥ probe) := by
  set moment := chartMassMoment direction mass with hmomentDef
  set shift := moment⁻¹ *ᵥ target with hshift
  have hback : moment *ᵥ shift = target := by
    rw [hshift, hmomentDef]
    exact chartMassMoment_mulVec_inv_mulVec direction mass hmoment target
  have hnonneg : 0 ≤ (probe - shift) ⬝ᵥ (moment *ᵥ (probe - shift)) := by
    have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hmoment.posSemidef).2 (probe - shift)
    rw [star_trivial] at hform
    exact hform
  have hmomentSymm : momentᵀ = moment := by
    rw [hmomentDef]
    exact chartMassMoment_transpose direction mass
  have hcross : shift ⬝ᵥ (moment *ᵥ probe) = target ⬝ᵥ probe := by
    rw [dotProduct_symmetric_mulVec hmomentSymm shift probe, hback, dotProduct_comm]
  have hself : shift ⬝ᵥ target = target ⬝ᵥ (moment⁻¹ *ᵥ target) := by
    rw [hshift, dotProduct_comm]
  have hother : probe ⬝ᵥ target = target ⬝ᵥ probe := dotProduct_comm _ _
  have hexpand : (probe - shift) ⬝ᵥ (moment *ᵥ (probe - shift))
      = probe ⬝ᵥ (moment *ᵥ probe) - 2 * (target ⬝ᵥ probe)
        + target ⬝ᵥ (moment⁻¹ *ᵥ target) := by
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hback, hcross, hself,
      hother]
    ring
  rw [hexpand] at hnonneg
  linarith

/-! ## 4.  Sum, cap and positivity of the leverages -/

/-- **The leverages total the rank.**  The leverages are the diagonal of a
projection, so they total three. -/
theorem sum_chartMassLeverage_eq_three (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (hmoment : (chartMassMoment direction mass).PosDef) :
    ∑ label, chartMassLeverage direction mass label = 3 := by
  have hunit : IsUnit (chartMassMoment direction mass).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hmoment.det_pos)
  have htrace : ∀ (form : Matrix (Fin 3) (Fin 3) ℝ) (scale : ℝ) (vec : Fin 3 → ℝ),
      Matrix.trace (form * (scale • atomMatrix vec)) = scale * (vec ⬝ᵥ (form *ᵥ vec)) := by
    intro form scale vec
    rw [atomMatrix, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_vecMulVec,
      Matrix.trace_vecMulVec, smul_eq_mul, dotProduct_comm]
  have hstep : ∀ label : Fin size, chartMassLeverage direction mass label
      = Matrix.trace ((chartMassMoment direction mass)⁻¹
          * (mass label • atomMatrix (direction label))) := by
    intro label
    rw [htrace, chartMassLeverage, chartMassPivot]
  rw [Finset.sum_congr rfl (fun label (_ : label ∈ Finset.univ) => hstep label),
    ← Matrix.trace_sum, ← Matrix.mul_sum, ← chartMassMoment_eq,
    Matrix.nonsing_inv_mul _ hunit, Matrix.trace_one, Fintype.card_fin]
  norm_num

/-- **The leverage cap.**  Every mass leverage is at most one.  The Legendre
inequality at the single direction is the whole proof. -/
theorem chartMassLeverage_le_one (direction : Fin size → (Fin 3 → ℝ)) (mass : Fin size → ℝ)
    (hmassPos : ∀ label, 0 < mass label)
    (hmoment : (chartMassMoment direction mass).PosDef) (label : Fin size) :
    chartMassLeverage direction mass label ≤ 1 := by
  set moment := chartMassMoment direction mass with hmomentDef
  set pivot := chartMassPivot direction mass label label with hpivot
  have hprobe : (moment⁻¹ *ᵥ direction label) ⬝ᵥ (moment *ᵥ (moment⁻¹ *ᵥ direction label))
      = pivot := by
    rw [hmomentDef, chartMassMoment_mulVec_inv_mulVec direction mass hmoment, hpivot,
      chartMassPivot, dotProduct_comm]
  have hquad : (moment⁻¹ *ᵥ direction label) ⬝ᵥ (moment *ᵥ (moment⁻¹ *ᵥ direction label))
      = ∑ other, mass other * (direction other ⬝ᵥ (moment⁻¹ *ᵥ direction label)) ^ 2 := by
    rw [hmomentDef, chartMassMoment_eq]
    exact dotProduct_sumAtom_mulVec direction mass Finset.univ _
  have hsingle : mass label * (direction label ⬝ᵥ (moment⁻¹ *ᵥ direction label)) ^ 2
      ≤ ∑ other, mass other * (direction other ⬝ᵥ (moment⁻¹ *ᵥ direction label)) ^ 2 :=
    Finset.single_le_sum
      (f := fun other => mass other * (direction other ⬝ᵥ (moment⁻¹ *ᵥ direction label)) ^ 2)
      (fun other _ => mul_nonneg (le_of_lt (hmassPos other)) (sq_nonneg _))
      (Finset.mem_univ label)
  rw [← hquad, hprobe] at hsingle
  have hread : direction label ⬝ᵥ (moment⁻¹ *ᵥ direction label) = pivot := rfl
  rw [hread] at hsingle
  have hpivotNonneg : 0 ≤ pivot := by
    rw [hpivot]
    exact chartMassPivot_self_nonneg direction mass hmoment label
  rw [chartMassLeverage, ← hpivot]
  nlinarith [hpivotNonneg, hsingle, hmassPos label]

/-- Every mass leverage is nonnegative. -/
theorem chartMassLeverage_nonneg (direction : Fin size → (Fin 3 → ℝ)) (mass : Fin size → ℝ)
    (hmassPos : ∀ label, 0 < mass label)
    (hmoment : (chartMassMoment direction mass).PosDef) (label : Fin size) :
    0 ≤ chartMassLeverage direction mass label :=
  mul_nonneg (le_of_lt (hmassPos label)) (chartMassPivot_self_nonneg direction mass hmoment label)

/-! ## 5.  The counting law -/

/-- **AT LEAST THREE LABELS ARE OVER-LEVERED.**

The leverages total three and the weights total one, so the surplus totals two.
No single surplus reaches one, because the leverage cap is one and every weight
is strictly positive.  Two labels can therefore never carry the whole surplus,
and three always survive.  This holds at every chart point of every direction
family, with no admissibility and no line pattern. -/
theorem three_le_card_overLevered (direction : Fin size → (Fin 3 → ℝ))
    (point : DirectionChartPoint size)
    (hmoment : (chartMassMoment direction point.mass).PosDef) :
    3 ≤ (Finset.univ.filter
      (fun label => point.weight label
        < chartMassLeverage direction point.mass label)).card := by
  classical
  set surplus : Fin size → ℝ :=
    fun label => chartMassLeverage direction point.mass label - point.weight label
    with hsurplus
  set overLevered := Finset.univ.filter
    (fun label => point.weight label < chartMassLeverage direction point.mass label)
    with hover
  have htotal : ∑ label, surplus label = 2 := by
    rw [hsurplus, Finset.sum_sub_distrib,
      sum_chartMassLeverage_eq_three direction point.mass hmoment, point.weight_sum_one]
    norm_num
  have hsplit : ∑ label ∈ overLevered, surplus label
      + ∑ label ∈ Finset.univ.filter
          (fun label => ¬ (point.weight label
            < chartMassLeverage direction point.mass label)), surplus label = 2 := by
    rw [hover, Finset.sum_filter_add_sum_filter_not]
    exact htotal
  have hoffNonpos : ∑ label ∈ Finset.univ.filter
      (fun label => ¬ (point.weight label
        < chartMassLeverage direction point.mass label)), surplus label ≤ 0 := by
    refine Finset.sum_nonpos fun label hmem => ?_
    have hnot := (Finset.mem_filter.mp hmem).2
    rw [hsurplus]
    exact sub_nonpos.mpr (not_lt.mp hnot)
  have hon : (2 : ℝ) ≤ ∑ label ∈ overLevered, surplus label := by linarith
  have hnonempty : overLevered.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.sum_empty] at hon
    linarith
  have hstrict : ∑ label ∈ overLevered, surplus label < ∑ _label ∈ overLevered, (1 : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty hnonempty fun label _ => ?_
    have hcap := chartMassLeverage_le_one direction point.mass point.mass_pos hmoment label
    have hweightPos := point.weight_pos label
    rw [hsurplus]
    simp only
    linarith
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hstrict
  have hcardReal : (2 : ℝ) < (overLevered.card : ℝ) := lt_of_le_of_lt hon hstrict
  have hcardNat : 2 < overLevered.card := by exact_mod_cast hcardReal
  omega

/-! ## 6.  The veto -/

/-- **THE LEVERAGE VETO.**  A label of a strictly dominating triple carries mass
leverage above its own weight.

The probe is blind to the other selected labels, so the gap form at the probe is
carried by the pivot label alone.  The Legendre inequality bounds the moment form
from below by the same reading divided by the leverage, and the two bounds
collide.  Together with `Gtz.three_le_card_overLevered` the veto prunes the
candidate list at every chart point without ever emptying it. -/
theorem weight_lt_chartMassLeverage_of_posDef_gap
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmassPos : ∀ label, 0 < mass label) (hweightPos : ∀ label, 0 < weight label)
    (hmoment : (chartMassMoment direction mass).PosDef)
    (selected : Finset (Fin size)) (pivotLabel : Fin size) (hmem : pivotLabel ∈ selected)
    (probe : Fin 3 → ℝ)
    (hblind : ∀ other ∈ selected, other ≠ pivotLabel → direction other ⬝ᵥ probe = 0)
    (hlive : direction pivotLabel ⬝ᵥ probe ≠ 0)
    (hgap : (directionChartGap direction mass weight selected).PosDef) :
    weight pivotLabel < chartMassLeverage direction mass pivotLabel := by
  classical
  set moment := chartMassMoment direction mass with hmomentDef
  set reading := direction pivotLabel ⬝ᵥ probe with hreading
  set pivot := chartMassPivot direction mass pivotLabel pivotLabel with hpivot
  have hprobeNe : probe ≠ 0 := by
    intro hzero
    apply hlive
    rw [hreading, hzero, dotProduct_zero]
  have hdirectionNe : direction pivotLabel ≠ 0 := by
    intro hzero
    apply hlive
    rw [hreading, hzero, zero_dotProduct]
  have hpivotPos : 0 < pivot := by
    rw [hpivot]
    exact chartMassPivot_self_pos direction mass hmoment hdirectionNe
  have hgapForm : 0 < probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe) := by
    have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hgap).2 hprobeNe
    rw [star_trivial] at hform
    exact hform
  have hgapSplit : probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe)
      = (∑ label ∈ selected, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2)
        - probe ⬝ᵥ (moment *ᵥ probe) := by
    rw [directionChartGap, Matrix.sub_mulVec, dotProduct_sub,
      dotProduct_sumAtom_mulVec direction (fun label => mass label / weight label) selected probe,
      hmomentDef, chartMassMoment_eq]
  have hselectedSingle : (∑ label ∈ selected, mass label / weight label
      * (direction label ⬝ᵥ probe) ^ 2)
      = mass pivotLabel / weight pivotLabel * reading ^ 2 := by
    refine Finset.sum_eq_single_of_mem pivotLabel hmem fun other hother hne => ?_
    rw [hblind other hother hne]
    ring
  rw [hselectedSingle] at hgapSplit
  have hmomentForm : probe ⬝ᵥ (moment *ᵥ probe)
      < mass pivotLabel / weight pivotLabel * reading ^ 2 := by linarith
  have hlegendre := legendre_le_dotProduct_massMoment direction mass hmoment probe
    ((reading / pivot) • direction pivotLabel)
  have hlinear : ((reading / pivot) • direction pivotLabel) ⬝ᵥ probe
      = reading / pivot * reading := by
    rw [smul_dotProduct, smul_eq_mul, ← hreading]
  have hquadratic : ((reading / pivot) • direction pivotLabel)
      ⬝ᵥ (moment⁻¹ *ᵥ ((reading / pivot) • direction pivotLabel))
      = (reading / pivot) ^ 2 * pivot := by
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hpivot,
      chartMassPivot, hmomentDef]
    ring
  rw [hlinear, hquadratic] at hlegendre
  have hpivotNe : pivot ≠ 0 := ne_of_gt hpivotPos
  have hsimplify : 2 * (reading / pivot * reading) - (reading / pivot) ^ 2 * pivot
      = reading ^ 2 / pivot := by
    field_simp
    ring
  rw [hsimplify] at hlegendre
  have hchain : reading ^ 2 / pivot < mass pivotLabel / weight pivotLabel * reading ^ 2 :=
    lt_of_le_of_lt hlegendre hmomentForm
  rw [div_lt_iff₀ hpivotPos] at hchain
  have hweightPosPivot := hweightPos pivotLabel
  have hscaled := mul_lt_mul_of_pos_right hchain hweightPosPivot
  have hclear : mass pivotLabel / weight pivotLabel * reading ^ 2 * pivot * weight pivotLabel
      = mass pivotLabel * reading ^ 2 * pivot := by
    field_simp
  rw [hclear] at hscaled
  have hreadingSq : 0 < reading ^ 2 := by
    have : reading ≠ 0 := hlive
    positivity
  rw [chartMassLeverage, ← hpivot]
  nlinarith [hscaled, hreadingSq]

/-! ## 7.  The dual criterion -/

/-- **THE DUAL CRITERION.**  A strict inequality between the inverse-moment form
of the selected directions and the diagonal `weight / mass` upgrades to strict
domination by the selection.

The proof is one completed square per label.  Write the moment image of the probe
in the selected directions, then read `(m/w) t^2 + (w/m) c^2 >= 2 c t` at every
label and sum.  No inverse monotonicity, no Cauchy-Schwarz and no eigenvalue
enters. -/
theorem posDef_directionChartGap_of_dualStrict
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmassPos : ∀ label, 0 < mass label) (hweightPos : ∀ label, 0 < weight label)
    (hmoment : (chartMassMoment direction mass).PosDef)
    (selected : Finset (Fin size))
    (hspan : ∀ target : Fin 3 → ℝ, ∃ coefficient : Fin size → ℝ,
      ∑ label ∈ selected, coefficient label • direction label = target)
    (hdual : ∀ coefficient : Fin size → ℝ,
      (∑ label ∈ selected, coefficient label • direction label) ≠ 0 →
      ∑ label ∈ selected, weight label / mass label * coefficient label ^ 2
        < (∑ label ∈ selected, coefficient label • direction label) ⬝ᵥ
            ((chartMassMoment direction mass)⁻¹ *ᵥ
              (∑ label ∈ selected, coefficient label • direction label))) :
    (directionChartGap direction mass weight selected).PosDef := by
  classical
  set moment := chartMassMoment direction mass with hmomentDef
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (directionChartGap_transpose direction mass weight selected),
      fun probe hprobeNe => ?_⟩
  rw [star_trivial]
  have hmomentForm : 0 < probe ⬝ᵥ (moment *ᵥ probe) := by
    have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hmoment).2 hprobeNe
    rw [star_trivial] at hform
    exact hform
  obtain ⟨coefficient, hcoefficient⟩ := hspan (moment *ᵥ probe)
  have hcombination : (∑ label ∈ selected, coefficient label • direction label) ⬝ᵥ probe
      = probe ⬝ᵥ (moment *ᵥ probe) := by
    rw [hcoefficient, dotProduct_comm]
  have hspread : (∑ label ∈ selected, coefficient label • direction label) ⬝ᵥ probe
      = ∑ label ∈ selected, coefficient label * (direction label ⬝ᵥ probe) := by
    rw [sum_dotProduct]
    exact Finset.sum_congr rfl fun label _ => by rw [smul_dotProduct, smul_eq_mul]
  have hinverseForm : (∑ label ∈ selected, coefficient label • direction label) ⬝ᵥ
      (moment⁻¹ *ᵥ (∑ label ∈ selected, coefficient label • direction label))
      = probe ⬝ᵥ (moment *ᵥ probe) := by
    rw [hcoefficient, hmomentDef, chartMassMomentInv_mulVec_mulVec direction mass hmoment,
      dotProduct_comm]
  have hcombinationNe : (∑ label ∈ selected, coefficient label • direction label) ≠ 0 := by
    intro hzero
    rw [hzero, zero_dotProduct] at hcombination
    linarith
  have hdualHere := hdual coefficient hcombinationNe
  rw [hinverseForm] at hdualHere
  have hterm : ∀ label ∈ selected,
      2 * (coefficient label * (direction label ⬝ᵥ probe))
        - weight label / mass label * coefficient label ^ 2
      ≤ mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 := by
    intro label _
    have hm := hmassPos label
    have hw := hweightPos label
    have hidentity : mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
        - (2 * (coefficient label * (direction label ⬝ᵥ probe))
          - weight label / mass label * coefficient label ^ 2)
        = (mass label * (direction label ⬝ᵥ probe) - weight label * coefficient label) ^ 2
          / (mass label * weight label) := by
      field_simp
      ring
    have hnonneg : 0 ≤ (mass label * (direction label ⬝ᵥ probe)
        - weight label * coefficient label) ^ 2 / (mass label * weight label) :=
      div_nonneg (sq_nonneg _) (le_of_lt (mul_pos hm hw))
    rw [← hidentity] at hnonneg
    linarith
  have hsum : ∑ label ∈ selected,
      (2 * (coefficient label * (direction label ⬝ᵥ probe))
        - weight label / mass label * coefficient label ^ 2)
      ≤ ∑ label ∈ selected, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 :=
    Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hspread, hcombination] at hsum
  have hgapSplit : probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe)
      = (∑ label ∈ selected, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2)
        - probe ⬝ᵥ (moment *ᵥ probe) := by
    rw [directionChartGap, Matrix.sub_mulVec, dotProduct_sub,
      dotProduct_sumAtom_mulVec direction (fun label => mass label / weight label) selected probe,
      hmomentDef, chartMassMoment_eq]
  rw [hgapSplit]
  linarith

end MassLeverage

/-! ## 8.  Cramer coordinates -/

/-- **Cramer's rule as a spanning statement.**  Three vectors with a nonzero
bracket express every target. -/
theorem exists_coordinates_of_tripleBracket_ne_zero
    (firstVec midVec rightVec target : Fin 3 → ℝ)
    (hbracket : tripleBracket firstVec midVec rightVec ≠ 0) :
    ∃ firstCoord midCoord rightCoord : ℝ,
      firstCoord • firstVec + midCoord • midVec + rightCoord • rightVec = target := by
  refine ⟨tripleBracket target midVec rightVec / tripleBracket firstVec midVec rightVec,
    tripleBracket firstVec target rightVec / tripleBracket firstVec midVec rightVec,
    tripleBracket firstVec midVec target / tripleBracket firstVec midVec rightVec, ?_⟩
  funext coord
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
  rw [← add_div, ← add_div, div_eq_iff hbracket]
  rcases fin_three_cases coord with rfl | rfl | rfl <;>
    · simp only [tripleBracket_eq]
      ring

/-! ## 9.  The leverage dominance cell -/

section LeverageDominance

variable {size : ℕ}

/-- The quadratic form of an explicit symmetric `3 x 3`, with no index reduction
left for the caller. -/
theorem dotProduct_symmetricFinThree_mulVec (entryOneOne entryOneTwo entryOneThree
    entryTwoTwo entryTwoThree entryThreeThree firstCoord midCoord rightCoord : ℝ) :
    (![firstCoord, midCoord, rightCoord] : Fin 3 → ℝ) ⬝ᵥ
        ((!![entryOneOne, entryOneTwo, entryOneThree;
             entryOneTwo, entryTwoTwo, entryTwoThree;
             entryOneThree, entryTwoThree, entryThreeThree] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
          ![firstCoord, midCoord, rightCoord])
      = entryOneOne * firstCoord ^ 2 + entryTwoTwo * midCoord ^ 2
        + entryThreeThree * rightCoord ^ 2
        + 2 * entryOneTwo * (firstCoord * midCoord)
        + 2 * entryOneThree * (firstCoord * rightCoord)
        + 2 * entryTwoThree * (midCoord * rightCoord) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- The dual form of a triple, written out in the three coordinates. -/
private theorem dual_form_triple (direction : Fin size → (Fin 3 → ℝ)) (mass : Fin size → ℝ)
    (first second third : Fin size) (firstCoord midCoord rightCoord : ℝ) :
    (firstCoord • direction first + midCoord • direction second + rightCoord • direction third)
        ⬝ᵥ ((chartMassMoment direction mass)⁻¹ *ᵥ
          (firstCoord • direction first + midCoord • direction second
            + rightCoord • direction third))
      = firstCoord ^ 2 * chartMassPivot direction mass first first
        + midCoord ^ 2 * chartMassPivot direction mass second second
        + rightCoord ^ 2 * chartMassPivot direction mass third third
        + 2 * (firstCoord * midCoord) * chartMassPivot direction mass first second
        + 2 * (firstCoord * rightCoord) * chartMassPivot direction mass first third
        + 2 * (midCoord * rightCoord) * chartMassPivot direction mass second third := by
  have hsymmOne : direction second ⬝ᵥ ((chartMassMoment direction mass)⁻¹ *ᵥ direction first)
      = direction first ⬝ᵥ ((chartMassMoment direction mass)⁻¹ *ᵥ direction second) :=
    dotProduct_symmetric_mulVec (chartMassMomentInv_transpose direction mass) _ _
  have hsymmTwo : direction third ⬝ᵥ ((chartMassMoment direction mass)⁻¹ *ᵥ direction first)
      = direction first ⬝ᵥ ((chartMassMoment direction mass)⁻¹ *ᵥ direction third) :=
    dotProduct_symmetric_mulVec (chartMassMomentInv_transpose direction mass) _ _
  have hsymmThree : direction third ⬝ᵥ ((chartMassMoment direction mass)⁻¹ *ᵥ direction second)
      = direction second ⬝ᵥ ((chartMassMoment direction mass)⁻¹ *ᵥ direction third) :=
    dotProduct_symmetric_mulVec (chartMassMomentInv_transpose direction mass) _ _
  simp only [chartMassPivot, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  linear_combination (firstCoord * midCoord) * hsymmOne
    + (firstCoord * rightCoord) * hsymmTwo + (midCoord * rightCoord) * hsymmThree

/-- **THE LEVERAGE DOMINANCE CELL, discharged.**  Three inequalities in the
leverage coordinates force strict domination by the triple.

Each inequality compares one label's leverage surplus `tau - w` against the
masses of its two partners weighted by the cross pivots.  Every quantity there is
bounded: the leverages sit in `(0, 1]` and the weights sum to one, so the cell
sees no dynamic range at all.  This is what the mass-coordinate cells of the
landed atlas cannot do. -/
theorem posDef_directionChartGap_of_leverageDominance
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmassPos : ∀ label, 0 < mass label) (hweightPos : ∀ label, 0 < weight label)
    (hmoment : (chartMassMoment direction mass).PosDef)
    (first second third : Fin size)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hbracket : tripleBracket (direction first) (direction second) (direction third) ≠ 0)
    (hdominateFirst :
      mass second * |chartMassPivot direction mass first second|
        + mass third * |chartMassPivot direction mass first third|
        < chartMassLeverage direction mass first - weight first)
    (hdominateSecond :
      mass first * |chartMassPivot direction mass first second|
        + mass third * |chartMassPivot direction mass second third|
        < chartMassLeverage direction mass second - weight second)
    (hdominateThird :
      mass first * |chartMassPivot direction mass first third|
        + mass second * |chartMassPivot direction mass second third|
        < chartMassLeverage direction mass third - weight third) :
    (directionChartGap direction mass weight
      ({first, second, third} : Finset (Fin size))).PosDef := by
  classical
  have hnotMemFirst : first ∉ ({second, third} : Finset (Fin size)) := by
    simp [hfirstSecond, hfirstThird]
  have hnotMemSecond : second ∉ ({third} : Finset (Fin size)) := by simp [hsecondThird]
  have hsumTriple : ∀ f : Fin size → ℝ,
      ∑ label ∈ ({first, second, third} : Finset (Fin size)), f label
        = f first + f second + f third := by
    intro f
    rw [Finset.sum_insert hnotMemFirst, Finset.sum_insert hnotMemSecond, Finset.sum_singleton,
      add_assoc]
  have hsumTripleVec : ∀ f : Fin size → ℝ,
      ∑ label ∈ ({first, second, third} : Finset (Fin size)), f label • direction label
        = f first • direction first + f second • direction second + f third • direction third := by
    intro f
    rw [Finset.sum_insert hnotMemFirst, Finset.sum_insert hnotMemSecond, Finset.sum_singleton,
      add_assoc]
  have hmassFirst := hmassPos first
  have hmassSecond := hmassPos second
  have hmassThird := hmassPos third
  have habsOne : |mass first * mass second * chartMassPivot direction mass first second|
      = mass first * (mass second * |chartMassPivot direction mass first second|) := by
    rw [abs_mul, abs_mul, abs_of_pos hmassFirst, abs_of_pos hmassSecond]
    ring
  have habsTwo : |mass first * mass third * chartMassPivot direction mass first third|
      = mass first * (mass third * |chartMassPivot direction mass first third|) := by
    rw [abs_mul, abs_mul, abs_of_pos hmassFirst, abs_of_pos hmassThird]
    ring
  have habsThree : |mass second * mass third * chartMassPivot direction mass second third|
      = mass second * (mass third * |chartMassPivot direction mass second third|) := by
    rw [abs_mul, abs_mul, abs_of_pos hmassSecond, abs_of_pos hmassThird]
    ring
  have hdomMatrix :
      (!![mass first * (chartMassLeverage direction mass first - weight first),
          mass first * mass second * chartMassPivot direction mass first second,
          mass first * mass third * chartMassPivot direction mass first third;
          mass first * mass second * chartMassPivot direction mass first second,
          mass second * (chartMassLeverage direction mass second - weight second),
          mass second * mass third * chartMassPivot direction mass second third;
          mass first * mass third * chartMassPivot direction mass first third,
          mass second * mass third * chartMassPivot direction mass second third,
          mass third * (chartMassLeverage direction mass third - weight third)]
        : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
    refine posDef_of_dominance_fin_three _ _ _
      |mass first * mass second * chartMassPivot direction mass first second|
      |mass first * mass third * chartMassPivot direction mass first third|
      |mass second * mass third * chartMassPivot direction mass second third|
      _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (by rw [sq_abs]) (by rw [sq_abs])
      (by rw [sq_abs]) ?_ ?_ ?_
    · rw [habsOne, habsTwo]
      nlinarith [hdominateFirst, hmassFirst]
    · rw [habsOne, habsThree]
      nlinarith [hdominateSecond, hmassSecond]
    · rw [habsTwo, habsThree]
      nlinarith [hdominateThird, hmassThird]
  refine posDef_directionChartGap_of_dualStrict direction mass weight hmassPos hweightPos hmoment
    ({first, second, third} : Finset (Fin size)) ?_ ?_
  · intro target
    obtain ⟨firstCoord, midCoord, rightCoord, hcoord⟩ :=
      exists_coordinates_of_tripleBracket_ne_zero (direction first) (direction second)
        (direction third) target hbracket
    refine ⟨fun label => if label = first then firstCoord
      else if label = second then midCoord else rightCoord, ?_⟩
    rw [hsumTripleVec]
    rw [if_pos rfl, if_neg (Ne.symm hfirstSecond), if_pos rfl, if_neg (Ne.symm hfirstThird),
      if_neg (Ne.symm hsecondThird)]
    exact hcoord
  · intro coefficient hne
    rw [hsumTripleVec] at hne ⊢
    rw [hsumTriple, dual_form_triple direction mass first second third
      (coefficient first) (coefficient second) (coefficient third)]
    set firstCoord := coefficient first with hfc
    set midCoord := coefficient second with hmc
    set rightCoord := coefficient third with hrc
    have hvecNe : (![firstCoord / mass first, midCoord / mass second,
        rightCoord / mass third] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      apply hne
      have hzeroFirst := congrFun hzero 0
      have hzeroSecond := congrFun hzero 1
      have hzeroThird := congrFun hzero 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, div_eq_zero_iff,
        ne_of_gt hmassFirst, ne_of_gt hmassSecond, ne_of_gt hmassThird, or_false]
        at hzeroFirst hzeroSecond hzeroThird
      rw [hzeroFirst, hzeroSecond, hzeroThird, zero_smul, zero_smul, zero_smul, add_zero, add_zero]
    have hquad := (Matrix.posDef_iff_dotProduct_mulVec.mp hdomMatrix).2 hvecNe
    rw [star_trivial] at hquad
    have hexpand : (![firstCoord / mass first, midCoord / mass second, rightCoord / mass third]
        : Fin 3 → ℝ) ⬝ᵥ
        ((!![mass first * (chartMassLeverage direction mass first - weight first),
          mass first * mass second * chartMassPivot direction mass first second,
          mass first * mass third * chartMassPivot direction mass first third;
          mass first * mass second * chartMassPivot direction mass first second,
          mass second * (chartMassLeverage direction mass second - weight second),
          mass second * mass third * chartMassPivot direction mass second third;
          mass first * mass third * chartMassPivot direction mass first third,
          mass second * mass third * chartMassPivot direction mass second third,
          mass third * (chartMassLeverage direction mass third - weight third)]
          : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
          ![firstCoord / mass first, midCoord / mass second, rightCoord / mass third])
        = (firstCoord ^ 2 * chartMassPivot direction mass first first
            + midCoord ^ 2 * chartMassPivot direction mass second second
            + rightCoord ^ 2 * chartMassPivot direction mass third third
            + 2 * (firstCoord * midCoord) * chartMassPivot direction mass first second
            + 2 * (firstCoord * rightCoord) * chartMassPivot direction mass first third
            + 2 * (midCoord * rightCoord) * chartMassPivot direction mass second third)
          - (weight first / mass first * firstCoord ^ 2
            + weight second / mass second * midCoord ^ 2
            + weight third / mass third * rightCoord ^ 2) := by
      have hne1 := ne_of_gt hmassFirst
      have hne2 := ne_of_gt hmassSecond
      have hne3 := ne_of_gt hmassThird
      rw [dotProduct_symmetricFinThree_mulVec]
      simp only [chartMassLeverage]
      field_simp
      ring
    rw [hexpand] at hquad
    linarith

end LeverageDominance

/-! ## 10.  The twenty brackets of the three-lines chart

Every card-three subset of the chart, with its bracket as an integer polynomial
in the slide.  Three vanish identically -- the three lines `{0,1,2}`, `{0,3,4}`
and `{1,3,5}` -- and the remaining seventeen vanish only at the two slides that
`Gtz.IsAdmissibleThreeLinesParameter` excludes. -/

section BracketTable

variable (slide : ℝ)

theorem threeLinesBracket_zeroOneTwo :
    tripleBracket (threeLinesDirection slide 0) (threeLinesDirection slide 1)
      (threeLinesDirection slide 2) = 0 := by
  simp [tripleBracket_eq, threeLinesDirection_zero, threeLinesDirection_one,
    threeLinesDirection_two]

theorem threeLinesBracket_zeroOneThree :
    tripleBracket (threeLinesDirection slide 0) (threeLinesDirection slide 1)
      (threeLinesDirection slide 3) = 1 := by
  simp [tripleBracket_eq, threeLinesDirection_zero, threeLinesDirection_one,
    threeLinesDirection_three]

theorem threeLinesBracket_zeroOneFour :
    tripleBracket (threeLinesDirection slide 0) (threeLinesDirection slide 1)
      (threeLinesDirection slide 4) = 1 := by
  simp [tripleBracket_eq, threeLinesDirection_zero, threeLinesDirection_one,
    threeLinesDirection_four]

theorem threeLinesBracket_zeroOneFive :
    tripleBracket (threeLinesDirection slide 0) (threeLinesDirection slide 1)
      (threeLinesDirection slide 5) = slide := by
  simp [tripleBracket_eq, threeLinesDirection_zero, threeLinesDirection_one,
    threeLinesDirection_five]

theorem threeLinesBracket_zeroTwoThree :
    tripleBracket (threeLinesDirection slide 0) (threeLinesDirection slide 2)
      (threeLinesDirection slide 3) = 1 := by
  simp [tripleBracket_eq, threeLinesDirection_zero, threeLinesDirection_two,
    threeLinesDirection_three]

theorem threeLinesBracket_zeroTwoFour :
    tripleBracket (threeLinesDirection slide 0) (threeLinesDirection slide 2)
      (threeLinesDirection slide 4) = 1 := by
  simp [tripleBracket_eq, threeLinesDirection_zero, threeLinesDirection_two,
    threeLinesDirection_four]

theorem threeLinesBracket_zeroTwoFive :
    tripleBracket (threeLinesDirection slide 0) (threeLinesDirection slide 2)
      (threeLinesDirection slide 5) = slide := by
  simp [tripleBracket_eq, threeLinesDirection_zero, threeLinesDirection_two,
    threeLinesDirection_five]

theorem threeLinesBracket_zeroThreeFour :
    tripleBracket (threeLinesDirection slide 0) (threeLinesDirection slide 3)
      (threeLinesDirection slide 4) = 0 := by
  simp [tripleBracket_eq, threeLinesDirection_zero, threeLinesDirection_three,
    threeLinesDirection_four]

theorem threeLinesBracket_zeroThreeFive :
    tripleBracket (threeLinesDirection slide 0) (threeLinesDirection slide 3)
      (threeLinesDirection slide 5) = -1 := by
  simp [tripleBracket_eq, threeLinesDirection_zero, threeLinesDirection_three,
    threeLinesDirection_five]

theorem threeLinesBracket_zeroFourFive :
    tripleBracket (threeLinesDirection slide 0) (threeLinesDirection slide 4)
      (threeLinesDirection slide 5) = -1 := by
  simp [tripleBracket_eq, threeLinesDirection_zero, threeLinesDirection_four,
    threeLinesDirection_five]

theorem threeLinesBracket_oneTwoThree :
    tripleBracket (threeLinesDirection slide 1) (threeLinesDirection slide 2)
      (threeLinesDirection slide 3) = -1 := by
  simp [tripleBracket_eq, threeLinesDirection_one, threeLinesDirection_two,
    threeLinesDirection_three]

theorem threeLinesBracket_oneTwoFour :
    tripleBracket (threeLinesDirection slide 1) (threeLinesDirection slide 2)
      (threeLinesDirection slide 4) = -1 := by
  simp [tripleBracket_eq, threeLinesDirection_one, threeLinesDirection_two,
    threeLinesDirection_four]

theorem threeLinesBracket_oneTwoFive :
    tripleBracket (threeLinesDirection slide 1) (threeLinesDirection slide 2)
      (threeLinesDirection slide 5) = -slide := by
  simp [tripleBracket_eq, threeLinesDirection_one, threeLinesDirection_two,
    threeLinesDirection_five]

theorem threeLinesBracket_oneThreeFour :
    tripleBracket (threeLinesDirection slide 1) (threeLinesDirection slide 3)
      (threeLinesDirection slide 4) = 1 := by
  simp [tripleBracket_eq, threeLinesDirection_one, threeLinesDirection_three,
    threeLinesDirection_four]

theorem threeLinesBracket_oneThreeFive :
    tripleBracket (threeLinesDirection slide 1) (threeLinesDirection slide 3)
      (threeLinesDirection slide 5) = 0 := by
  simp [tripleBracket_eq, threeLinesDirection_one, threeLinesDirection_three,
    threeLinesDirection_five]

theorem threeLinesBracket_oneFourFive :
    tripleBracket (threeLinesDirection slide 1) (threeLinesDirection slide 4)
      (threeLinesDirection slide 5) = -slide := by
  simp [tripleBracket_eq, threeLinesDirection_one, threeLinesDirection_four,
    threeLinesDirection_five]

theorem threeLinesBracket_twoThreeFour :
    tripleBracket (threeLinesDirection slide 2) (threeLinesDirection slide 3)
      (threeLinesDirection slide 4) = 1 := by
  simp [tripleBracket_eq, threeLinesDirection_two, threeLinesDirection_three,
    threeLinesDirection_four]

theorem threeLinesBracket_twoThreeFive :
    tripleBracket (threeLinesDirection slide 2) (threeLinesDirection slide 3)
      (threeLinesDirection slide 5) = -1 := by
  simp [tripleBracket_eq, threeLinesDirection_two, threeLinesDirection_three,
    threeLinesDirection_five]

theorem threeLinesBracket_twoFourFive :
    tripleBracket (threeLinesDirection slide 2) (threeLinesDirection slide 4)
      (threeLinesDirection slide 5) = -(1 + slide) := by
  simp [tripleBracket_eq, threeLinesDirection_two, threeLinesDirection_four,
    threeLinesDirection_five]
  ring

theorem threeLinesBracket_threeFourFive :
    tripleBracket (threeLinesDirection slide 3) (threeLinesDirection slide 4)
      (threeLinesDirection slide 5) = 1 := by
  simp [tripleBracket_eq, threeLinesDirection_three, threeLinesDirection_four,
    threeLinesDirection_five]

end BracketTable

/-! ## 11.  The chart-level readings -/

/-- The mass moment of the three-lines chart is positive definite at every chart
point, so the leverage machinery applies with no admissibility hypothesis. -/
theorem posDef_chartMassMoment_threeLines (slide : ℝ) (point : DirectionChartPoint 6) :
    (chartMassMoment (threeLinesDirection slide) point.mass).PosDef :=
  posDef_massMoment_threeLinesDirection slide point

/-- **The counting law at the three-lines chart.**  At every chart point at least
three labels are over-levered. -/
theorem three_le_card_overLevered_threeLines (slide : ℝ) (point : DirectionChartPoint 6) :
    3 ≤ (Finset.univ.filter
      (fun label => point.weight label
        < chartMassLeverage (threeLinesDirection slide) point.mass label)).card :=
  three_le_card_overLevered (threeLinesDirection slide) point
    (posDef_chartMassMoment_threeLines slide point)

/-- **The leverage veto at the three-lines chart.** -/
theorem weight_lt_chartMassLeverage_threeLines (slide : ℝ) (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (pivotLabel : Fin 6) (hmem : pivotLabel ∈ selected)
    (probe : Fin 3 → ℝ)
    (hblind : ∀ other ∈ selected, other ≠ pivotLabel →
      threeLinesDirection slide other ⬝ᵥ probe = 0)
    (hlive : threeLinesDirection slide pivotLabel ⬝ᵥ probe ≠ 0)
    (hgap : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      selected).PosDef) :
    point.weight pivotLabel
      < chartMassLeverage (threeLinesDirection slide) point.mass pivotLabel :=
  weight_lt_chartMassLeverage_of_posDef_gap (threeLinesDirection slide) point.mass point.weight
    point.mass_pos point.weight_pos (posDef_chartMassMoment_threeLines slide point) selected
    pivotLabel hmem probe hblind hlive hgap

/-- **The leverage dominance cell of the three-lines chart.** -/
def ThreeLinesLeverageDominanceCellFires (slide : ℝ) (point : DirectionChartPoint 6) : Prop :=
  ∃ first second third : Fin 6,
    first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
    tripleBracket (threeLinesDirection slide first) (threeLinesDirection slide second)
      (threeLinesDirection slide third) ≠ 0 ∧
    point.mass second
        * |chartMassPivot (threeLinesDirection slide) point.mass first second|
      + point.mass third
        * |chartMassPivot (threeLinesDirection slide) point.mass first third|
      < chartMassLeverage (threeLinesDirection slide) point.mass first - point.weight first ∧
    point.mass first
        * |chartMassPivot (threeLinesDirection slide) point.mass first second|
      + point.mass third
        * |chartMassPivot (threeLinesDirection slide) point.mass second third|
      < chartMassLeverage (threeLinesDirection slide) point.mass second - point.weight second ∧
    point.mass first
        * |chartMassPivot (threeLinesDirection slide) point.mass first third|
      + point.mass second
        * |chartMassPivot (threeLinesDirection slide) point.mass second third|
      < chartMassLeverage (threeLinesDirection slide) point.mass third - point.weight third

/-- **The cell supplies a strict triple.** -/
theorem exists_posDef_threeLines_of_leverageDominanceCellFires (slide : ℝ)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesLeverageDominanceCellFires slide point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef := by
  classical
  obtain ⟨first, second, third, hfs, hft, hst, hbracket, hone, htwo, hthree⟩ := hcell
  refine ⟨{first, second, third}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hfs, hft]),
      Finset.card_insert_of_notMem (by simp [hst]), Finset.card_singleton]
  · exact posDef_directionChartGap_of_leverageDominance (threeLinesDirection slide) point.mass
      point.weight point.mass_pos point.weight_pos (posDef_chartMassMoment_threeLines slide point)
      first second third hfs hft hst hbracket hone htwo hthree

end Gtz
