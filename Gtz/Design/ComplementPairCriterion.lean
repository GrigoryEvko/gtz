/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Design.ComplementFormLaw
import Gtz.Design.ChartInverseTrace
import Gtz.Design.KFourDescentLadder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The complement form at one label and at a pair

`Gtz.posDef_directionChartGap_compl_iff` decides a selection on the labels it
omits, but it quantifies over every coefficient vector.  This module evaluates
that quantifier when the omitted set is a single label or a pair.

Write `κ_c = mass c / weight c` for the boost, `U` for the full-selection gap
and `P i j = direction i ⬝ U⁻¹ ⬝ direction j` for its inverse form.  The
**full pivot** of a label is `π_i = κ_i * P i i`.

**ONE LABEL.**  Taking the coefficient vector supported at a single omitted
label turns the law into a necessary condition with no quantifier at all:

  `gap (univ \ omitted)` positive definite  →  `π_i < 1` for every `i ∈ omitted`.

So the omitted set of any positive definite selection lies inside the
sub-unit-pivot set.  A card-four selection needs BOTH omitted labels there, and
a card-three selection needs all THREE.

**A PAIR.**  At `omitted = {i, j}` the complement form is a binary quadratic
form in the two coefficients, with matrix

  `[[κ_i (1 - π_i), -κ_i κ_j P i j], [-κ_i κ_j P i j, κ_j (1 - π_j)]]`.

Positivity off the origin is the classical two-by-two test, so

  `gap (univ \ {i,j})` positive definite
    ↔  `0 < κ_i (1 - π_i)`  and  `(κ_i κ_j P i j)^2 < κ_i (1 - π_i) * κ_j (1 - π_j)`.

Two polynomial inequalities, no probe space and no quantifier.  At size six
this reads the fifteen card-four selections in closed form.

Everything is generic in the size and in the direction family, so it serves
every chart and the trivial chart of a weighted design.
-/

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## 1. The inverse form of the full-selection gap -/

/-- The inverse form of the full-selection gap, read at two directions. -/
noncomputable def fullInverseForm (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j : Fin size) : ℝ :=
  direction i ⬝ᵥ ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ direction j)

/-- The full pivot of a label: its boost against the inverse form of the
full-selection gap. -/
noncomputable def fullPivot (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i : Fin size) : ℝ :=
  (mass i / weight i) * fullInverseForm direction mass weight i i

/-- The inverse form of the full-selection gap is symmetric. -/
theorem fullInverseForm_comm (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i j : Fin size) :
    fullInverseForm direction mass weight i j = fullInverseForm direction mass weight j i := by
  have hdet : IsUnit (directionChartGap direction mass weight Finset.univ).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt huniv.det_pos)
  have hgap : (directionChartGap direction mass weight Finset.univ)ᵀ
      = directionChartGap direction mass weight Finset.univ :=
    directionChartGap_transpose direction mass weight Finset.univ
  have hinv : ((directionChartGap direction mass weight Finset.univ)⁻¹)ᵀ
      = (directionChartGap direction mass weight Finset.univ)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hgap]
  exact dotProduct_mulVec_comm_of_transpose_eq hinv _ _

/-! ## 2. One omitted label: the pivot is below one -/

/-- The complement form at the indicator of a single omitted label reads the
boost against the full pivot. -/
theorem complementForm_single (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size)) {i : Fin size}
    (hi : i ∈ omitted) :
    complementForm direction mass weight omitted (fun label => if label = i then 1 else 0)
      = (mass i / weight i) * (1 - fullPivot direction mass weight i) := by
  have hsum : (∑ label ∈ omitted, (mass label / weight label)
      * (if label = i then (1 : ℝ) else 0) * (if label = i then (1 : ℝ) else 0))
      = mass i / weight i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro label _ hne
      simp [hne]
    · intro hnot
      exact absurd hi hnot
  have hcomb : omittedCombination direction mass weight omitted
      (fun label => if label = i then 1 else 0)
      = (mass i / weight i) • direction i := by
    rw [omittedCombination, Finset.sum_eq_single i]
    · simp
    · intro label _ hne
      simp [hne]
    · intro hnot
      exact absurd hi hnot
  rw [complementForm, hsum, hcomb, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, fullPivot, fullInverseForm]
  ring

/-- **THE PIVOT EXCLUSION.**  Every label omitted by a positive definite
selection carries full pivot strictly below one.  No quantifier remains, and the
statement is generic in the size, the direction family and the omitted set.

A card-four selection therefore needs BOTH omitted labels below one, and a
card-three selection needs all THREE. -/
theorem fullPivot_lt_one_of_posDef_compl (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size))
    (hboost : ∀ label ∈ omitted, 0 < mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hcompl : (directionChartGap direction mass weight (Finset.univ \ omitted)).PosDef)
    {i : Fin size} (hi : i ∈ omitted) :
    fullPivot direction mass weight i < 1 := by
  have hform := (posDef_directionChartGap_compl_iff direction mass weight omitted
    hboost huniv).mp hcompl (fun label => if label = i then 1 else 0) ⟨i, hi, by simp⟩
  rw [complementForm_single direction mass weight omitted hi] at hform
  have hpos := hboost i hi
  nlinarith [hform, hpos]

/-! ## 3. A pair of omitted labels: the two-by-two test -/

/-- The diagonal entry of the pair form at a label: the boost scaled by the
slack of its full pivot. -/
noncomputable def pairFormDiag (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i : Fin size) : ℝ :=
  (mass i / weight i) * (1 - fullPivot direction mass weight i)

/-- The off-diagonal entry of the pair form: the two boosts against the inverse
form of the full-selection gap. -/
noncomputable def pairFormCross (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j : Fin size) : ℝ :=
  (mass i / weight i) * (mass j / weight j) * fullInverseForm direction mass weight i j

/-- **The complement form at a pair is a binary quadratic form.**  Its matrix is
the pair form, and it involves only the two coefficients at the omitted labels. -/
theorem complementForm_pair (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {i j : Fin size} (hij : i ≠ j)
    (coeff : Fin size → ℝ) :
    complementForm direction mass weight {i, j} coeff
      = pairFormDiag direction mass weight i * coeff i ^ 2
        - 2 * pairFormCross direction mass weight i j * coeff i * coeff j
        + pairFormDiag direction mass weight j * coeff j ^ 2 := by
  set matM := (directionChartGap direction mass weight Finset.univ)⁻¹ with hmatM
  have hsum : (∑ label ∈ ({i, j} : Finset (Fin size)),
      (mass label / weight label) * coeff label * coeff label)
      = (mass i / weight i) * coeff i * coeff i
        + (mass j / weight j) * coeff j * coeff j := Finset.sum_pair hij
  have hcomb : omittedCombination direction mass weight {i, j} coeff
      = ((mass i / weight i) * coeff i) • direction i
        + ((mass j / weight j) * coeff j) • direction j := by
    rw [omittedCombination]
    exact Finset.sum_pair hij
  have hcross : direction j ⬝ᵥ (matM *ᵥ direction i)
      = direction i ⬝ᵥ (matM *ᵥ direction j) := by
    have hgap : (directionChartGap direction mass weight Finset.univ)ᵀ
        = directionChartGap direction mass weight Finset.univ :=
      directionChartGap_transpose direction mass weight Finset.univ
    have hinv : matMᵀ = matM := by
      rw [hmatM, Matrix.transpose_nonsing_inv, hgap]
    exact dotProduct_mulVec_comm_of_transpose_eq hinv _ _
  rw [complementForm, hsum, hcomb, ← hmatM]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add,
    add_dotProduct, add_dotProduct, dotProduct_smul, dotProduct_smul, dotProduct_smul,
    dotProduct_smul, smul_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct]
  simp only [smul_eq_mul]
  rw [hcross]
  simp only [pairFormDiag, pairFormCross, fullPivot, fullInverseForm, ← hmatM]
  ring

/-- A binary quadratic form is positive away from the origin exactly when its
matrix passes the two-by-two test. -/
theorem binaryQuadratic_pos_iff {coefA coefB coefC : ℝ} :
    (∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) →
        0 < coefA * a ^ 2 - 2 * coefC * a * b + coefB * b ^ 2)
      ↔ (0 < coefA ∧ coefC ^ 2 < coefA * coefB) := by
  constructor
  · intro hall
    have hA : 0 < coefA := by
      have := hall 1 0 (Or.inl one_ne_zero)
      simpa using this
    refine ⟨hA, ?_⟩
    have hpick := hall coefC coefA (Or.inr (ne_of_gt hA))
    nlinarith [hpick, hA]
  · rintro ⟨hA, hdisc⟩ a b hab
    rcases eq_or_ne b 0 with hb | hb
    · subst hb
      have ha : a ≠ 0 := by
        rcases hab with h | h
        · exact h
        · exact absurd rfl h
      have ha2 : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha))
      nlinarith [mul_pos hA ha2]
    · have hb2 : 0 < b ^ 2 := lt_of_le_of_ne (sq_nonneg b) (Ne.symm (pow_ne_zero 2 hb))
      have hkey : 0 < (coefA * coefB - coefC ^ 2) * b ^ 2 :=
        mul_pos (by linarith) hb2
      nlinarith [sq_nonneg (coefA * a - coefC * b), hkey, hA]

/-- **THE CARD-FOUR CRITERION.**  A selection that omits exactly two labels has
a positive definite gap exactly when the pair form passes the two-by-two test.
Two polynomial inequalities in the boosts and the inverse form of the
full-selection gap: no probe space, and no quantifier over coefficients.

At size six this reads all fifteen card-four selections in closed form. -/
theorem posDef_directionChartGap_compl_pair_iff (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {i j : Fin size} (hij : i ≠ j)
    (hbi : 0 < mass i / weight i) (hbj : 0 < mass j / weight j)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) :
    (directionChartGap direction mass weight (Finset.univ \ {i, j})).PosDef
      ↔ (0 < pairFormDiag direction mass weight i
          ∧ pairFormCross direction mass weight i j ^ 2
            < pairFormDiag direction mass weight i * pairFormDiag direction mass weight j) := by
  have hboost : ∀ label ∈ ({i, j} : Finset (Fin size)), 0 < mass label / weight label := by
    intro label hlabel
    rcases Finset.mem_insert.mp hlabel with h | h
    · subst h; exact hbi
    · rw [Finset.mem_singleton] at h; subst h; exact hbj
  rw [posDef_directionChartGap_compl_iff direction mass weight {i, j} hboost huniv]
  constructor
  · intro hall
    refine binaryQuadratic_pos_iff.mp ?_
    intro a b hab
    have hcoeff : ∃ label ∈ ({i, j} : Finset (Fin size)),
        (fun label => if label = i then a else if label = j then b else 0) label ≠ 0 := by
      rcases hab with ha | hb
      · exact ⟨i, Finset.mem_insert_self _ _, by simpa using ha⟩
      · refine ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
        simp [Ne.symm hij, hb]
    have hval := hall _ hcoeff
    rw [complementForm_pair direction mass weight hij] at hval
    simpa [Ne.symm hij] using hval
  · intro htest coeff hcoeff
    rw [complementForm_pair direction mass weight hij]
    refine binaryQuadratic_pos_iff.mpr htest (coeff i) (coeff j) ?_
    obtain ⟨label, hlabel, hne⟩ := hcoeff
    rcases Finset.mem_insert.mp hlabel with h | h
    · subst h; exact Or.inl hne
    · rw [Finset.mem_singleton] at h; subst h; exact Or.inr hne

/-- The card-four criterion in pivot form: both omitted labels carry full pivot
below one, and the cross term is dominated by the product of the two slacks. -/
theorem posDef_directionChartGap_compl_pair_pivot (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {i j : Fin size} (hij : i ≠ j)
    (hbi : 0 < mass i / weight i) (hbj : 0 < mass j / weight j)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hcompl : (directionChartGap direction mass weight (Finset.univ \ {i, j})).PosDef) :
    fullPivot direction mass weight i < 1 ∧ fullPivot direction mass weight j < 1 := by
  have hboost : ∀ label ∈ ({i, j} : Finset (Fin size)), 0 < mass label / weight label := by
    intro label hlabel
    rcases Finset.mem_insert.mp hlabel with h | h
    · subst h; exact hbi
    · rw [Finset.mem_singleton] at h; subst h; exact hbj
  refine ⟨fullPivot_lt_one_of_posDef_compl direction mass weight {i, j} hboost huniv hcompl
      (Finset.mem_insert_self _ _),
    fullPivot_lt_one_of_posDef_compl direction mass weight {i, j} hboost huniv hcompl
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩

/-! ## 4. The complement matrix at an arbitrary omitted set -/

/-- The entry of the complement matrix: the boost on the diagonal, less the two
boosts against the inverse form of the full-selection gap. -/
noncomputable def complementMatrixEntry (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j : Fin size) : ℝ :=
  (if i = j then mass i / weight i else 0)
    - (mass i / weight i) * (mass j / weight j) * fullInverseForm direction mass weight i j

/-- **THE COMPLEMENT MATRIX.**  The complement form is the quadratic form of the
complement matrix over the omitted labels.  Positive definiteness of a selection
is therefore positive definiteness of one explicit symmetric matrix indexed by
the labels it omits, of size the omitted count rather than the rank.  The single
label and pair readings are the cases of one and two. -/
theorem complementForm_eq_sum (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size)) (coeff : Fin size → ℝ) :
    complementForm direction mass weight omitted coeff
      = ∑ a ∈ omitted, ∑ b ∈ omitted,
          complementMatrixEntry direction mass weight a b * coeff a * coeff b := by
  classical
  set matM := (directionChartGap direction mass weight Finset.univ)⁻¹ with hmatM
  have hquad : omittedCombination direction mass weight omitted coeff ⬝ᵥ
      (matM *ᵥ omittedCombination direction mass weight omitted coeff)
      = ∑ a ∈ omitted, ∑ b ∈ omitted,
          ((mass a / weight a) * (mass b / weight b)
            * fullInverseForm direction mass weight a b) * coeff a * coeff b := by
    rw [omittedCombination, Matrix.mulVec_sum, sum_dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_dotProduct, dotProduct_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, fullInverseForm, ← hmatM]
    ring
  have hdiag : ∑ a ∈ omitted, ∑ b ∈ omitted,
      (if a = b then mass a / weight a else 0) * coeff a * coeff b
      = ∑ a ∈ omitted, (mass a / weight a) * coeff a * coeff a := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hne
      simp [Ne.symm hne]
    · intro hnot
      exact absurd ha hnot
  rw [complementForm, hquad, ← hdiag, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [complementMatrixEntry]
  ring

/-! ## 5. The slack reading, the leverage, and the pivot count -/

/-- The inverse form of the full-selection gap is nonnegative on the diagonal. -/
theorem fullInverseForm_self_nonneg (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) (i : Fin size) :
    0 ≤ fullInverseForm direction mass weight i i := by
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp huniv.inv.posSemidef).2
    (direction i)
  rwa [star_trivial] at hform

/-- **The chart leverage.**  The slack of a label against the inverse form of the
full-selection gap.  This is the statistical leverage of the label in the slack
representation of the gap. -/
noncomputable def chartLeverage (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i : Fin size) : ℝ :=
  chartSlack mass weight i * fullInverseForm direction mass weight i i

/-- **THE LEVERAGES SUM TO THE RANK.**  The full-selection gap is the slack
Laplacian, so the leverages are the diagonal of a projection and total three. -/
theorem sum_chartLeverage_eq_three (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) :
    ∑ i, chartLeverage direction mass weight i = 3 := by
  have hdet : IsUnit (directionChartGap direction mass weight Finset.univ).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt huniv.det_pos)
  have hstep : ∀ i : Fin size, chartLeverage direction mass weight i
      = Matrix.trace ((directionChartGap direction mass weight Finset.univ)⁻¹
          * (chartSlack mass weight i • atomMatrix (direction i))) := by
    intro i
    rw [trace_mul_smul_atomMatrix, chartLeverage, fullInverseForm]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hstep i), ← Matrix.trace_sum,
    ← Matrix.mul_sum, ← slackLaplacian, ← directionChartGap_univ_eq_slackLaplacian,
    Matrix.nonsing_inv_mul _ hdet, Matrix.trace_one, Fintype.card_fin]
  norm_num

/-- **THE PIVOT IS THE LEVERAGE OVER THE WEIGHT SLACK.**  The slack of a label is
its boost scaled by `1 - weight`, so the full pivot and the leverage differ by
exactly that factor. -/
theorem chartLeverage_eq_one_sub_weight_mul_fullPivot (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {i : Fin size} (hw : weight i ≠ 0) :
    chartLeverage direction mass weight i
      = (1 - weight i) * fullPivot direction mass weight i := by
  rw [chartLeverage, fullPivot, chartSlack]
  field_simp

/-- The pivot exclusion in leverage coordinates: a label carries full pivot below
one exactly when its leverage and its weight together stay below one. -/
theorem fullPivot_lt_one_iff_leverage_add_weight (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {i : Fin size} (hw : 0 < weight i) (hwlt : weight i < 1) :
    fullPivot direction mass weight i < 1
      ↔ chartLeverage direction mass weight i + weight i < 1 := by
  rw [chartLeverage_eq_one_sub_weight_mul_fullPivot direction mass weight (ne_of_gt hw)]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- **AT LEAST THREE LABELS CARRY FULL PIVOT BELOW ONE.**

The leverages total the rank three and the weights total one, so the six sums
`leverage + weight` total exactly four.  Four labels at or above one would
already exhaust that total, and every remaining weight is strictly positive.
So at most three labels are excluded, and at least three survive.

By `fullPivot_lt_one_of_posDef_compl` the omitted set of any positive definite
selection lies inside this surviving set.  The candidate omitted triple of a
card-three selection therefore always exists, at every chart point of every
direction family. -/
theorem three_le_card_fullPivot_lt_one (direction : Fin 6 → (Fin 3 → ℝ))
    (point : DirectionChartPoint 6)
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef) :
    3 ≤ (Finset.univ.filter
      (fun i => fullPivot direction point.mass point.weight i < 1)).card := by
  classical
  set lev : Fin 6 → ℝ := fun i => chartLeverage direction point.mass point.weight i with hlevdef
  set wt : Fin 6 → ℝ := point.weight with hwtdef
  have hwlt : ∀ i, wt i < 1 := chartPoint_weight_lt_one point
  have hwpos : ∀ i, 0 < wt i := point.weight_pos
  have hlevnn : ∀ i, 0 ≤ lev i := by
    intro i
    exact mul_nonneg
      (le_of_lt (chartSlack_pos point.mass point.weight i (point.mass_pos i) (hwpos i)
        (hwlt i)))
      (fullInverseForm_self_nonneg direction point.mass point.weight huniv i)
  have hlevsum : ∑ i, lev i = 3 :=
    sum_chartLeverage_eq_three direction point.mass point.weight huniv
  have htot : ∑ i, (lev i + wt i) = 4 := by
    rw [Finset.sum_add_distrib, hlevsum, hwtdef, point.weight_sum_one]
    norm_num
  set good := Finset.univ.filter (fun i => lev i + wt i < 1) with hgood
  set bad := Finset.univ.filter (fun i => ¬ (lev i + wt i < 1)) with hbad
  have hsplit : (∑ i ∈ good, (lev i + wt i)) + ∑ i ∈ bad, (lev i + wt i) = 4 := by
    rw [hgood, hbad, Finset.sum_filter_add_sum_filter_not]
    exact htot
  have hbadge : (bad.card : ℝ) ≤ ∑ i ∈ bad, (lev i + wt i) := by
    have hone : ∀ i ∈ bad, (1 : ℝ) ≤ lev i + wt i := by
      intro i hi
      rw [hbad, Finset.mem_filter] at hi
      exact not_lt.mp hi.2
    calc (bad.card : ℝ) = ∑ _i ∈ bad, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ bad, (lev i + wt i) := Finset.sum_le_sum hone
  have hgoodnn : 0 ≤ ∑ i ∈ good, (lev i + wt i) :=
    Finset.sum_nonneg fun i _ => by linarith [hlevnn i, (hwpos i).le]
  have hunion : good.card + bad.card = 6 := by
    rw [hgood, hbad, Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_fin]
  -- the surviving set has at least three labels
  have hgoodcard : 3 ≤ good.card := by
    by_contra hcon
    push Not at hcon
    have hbadcard : 4 ≤ bad.card := by omega
    have hbadreal : (4 : ℝ) ≤ (bad.card : ℝ) := by exact_mod_cast hbadcard
    have hgoodzero : ∑ i ∈ good, (lev i + wt i) ≤ 0 := by linarith
    have hgoodempty : good = ∅ := by
      by_contra hne
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hpos : 0 < ∑ j ∈ good, (lev j + wt j) := by
        refine Finset.sum_pos' (fun j _ => by linarith [hlevnn j, (hwpos j).le]) ⟨i, hi, ?_⟩
        linarith [hlevnn i, hwpos i]
      linarith
    have hbadall : bad.card = 6 := by
      rw [hgoodempty, Finset.card_empty] at hunion
      omega
    have hsix : (6 : ℝ) ≤ ∑ i ∈ bad, (lev i + wt i) := by
      have hstep := hbadge
      rw [hbadall] at hstep
      norm_num at hstep
      exact hstep
    linarith
  -- the filter on the pivot is the surviving set
  have hfilter : Finset.univ.filter
      (fun i => fullPivot direction point.mass point.weight i < 1) = good := by
    rw [hgood]
    refine Finset.filter_congr fun i _ => ?_
    exact fullPivot_lt_one_iff_leverage_add_weight direction point.mass point.weight
      (hwpos i) (hwlt i)
  rw [hfilter]
  exact hgoodcard

end Gtz
