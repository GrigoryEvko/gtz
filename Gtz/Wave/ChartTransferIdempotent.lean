import Gtz.Wave.LeverageRowCell

/-!
# The chart transfer is idempotent

The campaign reads a chart point through the leverages `l_c` and the cross
leverages.  Both are entries of one matrix, and that matrix is a projection.

Write `F` for the inverse form of the full-selection gap, `S` for the diagonal
of chart slacks, and `U` for the full-selection gap itself.  Then `U = Dᵀ S D`
and `F = D U⁻¹ Dᵀ`, so `F S F = F` by cancellation, and the transfer

  `Y = S F`,   `Y a b = chartSlack a * fullInverseForm a b`

satisfies `Y * Y = Y`.  It is idempotent of trace three, so its spectrum is
three ones and three zeros, and its principal minors obey the exact global laws
`e₁ = 3`, `e₂ = 3`.

The corpus already carries the diagonal of this fact: the row identity
`sum_chartSlack_mul_fullInverseForm_sq` is `F S F = F` read on the diagonal, and
`sum_chartLeverage_eq_three` is `trace Y = 3`.  The design side carries the
whole fact (`designTransfer_idempotent`).  What is new here is the chart-level
composition law off the diagonal, the transfer matrix itself, its idempotence,
and the second symmetric function.

The last section is the converse.  Setting `mass c = weight c / (1 - weight c)`
makes every chart slack exactly one, and then the full-selection gap is the
plain unweighted Gram of the directions and the transfer is symmetric.  So every
rank-three configuration is realized by a chart point, and the transfer is the
orthogonal projection onto the span of the directions.  No square root appears
anywhere in this file.
-/

namespace Gtz

open Matrix Finset

variable {size : ℕ}

section Composition

variable (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)

/-- **THE COMPOSITION LAW OF THE INVERSE FORM.**  Contracting two inverse forms
against the chart slacks returns a single inverse form: `F S F = F`.  This is
`U = Dᵀ S D` cancelled against `F = D U⁻¹ Dᵀ`, and it is the off-diagonal
generalization of the landed row identity, which is the case `a = c`. -/
theorem sum_chartSlack_mul_fullInverseForm_mul
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) (a c : Fin size) :
    ∑ b, chartSlack mass weight b * fullInverseForm direction mass weight a b
        * fullInverseForm direction mass weight b c
      = fullInverseForm direction mass weight a c := by
  classical
  have hdet : IsUnit (directionChartGap direction mass weight Finset.univ).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt huniv.det_pos)
  have hgapT : (directionChartGap direction mass weight Finset.univ)ᵀ
      = directionChartGap direction mass weight Finset.univ :=
    directionChartGap_transpose direction mass weight Finset.univ
  have hinvT : ((directionChartGap direction mass weight Finset.univ)⁻¹)ᵀ
      = (directionChartGap direction mass weight Finset.univ)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hgapT]
  have hread : ∀ b : Fin size,
      fullInverseForm direction mass weight a b
        = ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ direction a)
            ⬝ᵥ direction b := by
    intro b
    rw [dotProduct_comm, fullInverseForm]
    exact dotProduct_mulVec_comm_of_transpose hinvT (direction a) (direction b)
  have hterm : ∀ b : Fin size,
      chartSlack mass weight b * fullInverseForm direction mass weight a b
          * fullInverseForm direction mass weight b c
        = ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ direction a) ⬝ᵥ
            ((chartSlack mass weight b • atomMatrix (direction b)) *ᵥ
              ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ direction c)) := by
    intro b
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix_mulVec, dotProduct_smul,
      smul_eq_mul, hread b, fullInverseForm]
    ring
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => hterm b), ← dotProduct_sum,
    ← Matrix.sum_mulVec, ← slackLaplacian, ← directionChartGap_univ_eq_slackLaplacian,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  exact (hread c).symm

end Composition

section Transfer

variable (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)

/-- **THE CHART TRANSFER.**  The slack-scaled inverse form, `Y = S F`.  Its
diagonal is the leverage and the square of its off-diagonal entry pair is the
cross leverage.  It carries no square root. -/
noncomputable def chartTransfer : Matrix (Fin size) (Fin size) ℝ :=
  Matrix.of fun a b => chartSlack mass weight a * fullInverseForm direction mass weight a b

@[simp] theorem chartTransfer_apply (a b : Fin size) :
    chartTransfer direction mass weight a b
      = chartSlack mass weight a * fullInverseForm direction mass weight a b := rfl

/-- The diagonal of the transfer is the leverage. -/
theorem chartTransfer_diag (a : Fin size) :
    chartTransfer direction mass weight a a = chartLeverage direction mass weight a := rfl

/-- The product of the two off-diagonal entries is the cross leverage.  The
transfer is not symmetric, but this product is, which is why the campaign's
cross-leverage vocabulary is well defined. -/
theorem chartTransfer_mul_swap
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) (a b : Fin size) :
    chartTransfer direction mass weight a b * chartTransfer direction mass weight b a
      = crossLeverageSq direction mass weight a b := by
  rw [chartTransfer_apply, chartTransfer_apply, crossLeverageSq,
    fullInverseForm_comm direction mass weight huniv b a]
  ring

/-- **THE CHART TRANSFER IS IDEMPOTENT.**  `Y * Y = Y`.  Every global law below
is a consequence: the transfer has spectrum three ones and three zeros. -/
theorem chartTransfer_idempotent
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) :
    chartTransfer direction mass weight * chartTransfer direction mass weight
      = chartTransfer direction mass weight := by
  classical
  ext a c
  rw [Matrix.mul_apply]
  have hstep : ∀ b : Fin size,
      chartTransfer direction mass weight a b * chartTransfer direction mass weight b c
        = chartSlack mass weight a * (chartSlack mass weight b
            * fullInverseForm direction mass weight a b
            * fullInverseForm direction mass weight b c) := by
    intro b
    rw [chartTransfer_apply, chartTransfer_apply]
    ring
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => hstep b), ← Finset.mul_sum,
    sum_chartSlack_mul_fullInverseForm_mul direction mass weight huniv a c,
    chartTransfer_apply]

/-- The transfer is idempotent as an element of the matrix ring. -/
theorem isIdempotentElem_chartTransfer
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) :
    IsIdempotentElem (chartTransfer direction mass weight) :=
  chartTransfer_idempotent direction mass weight huniv

/-- **THE TRANSFER HAS TRACE THREE.**  The rank of the chart. -/
theorem trace_chartTransfer
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) :
    (chartTransfer direction mass weight).trace = 3 := by
  classical
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, chartTransfer_diag]
  exact sum_chartLeverage_eq_three direction mass weight huniv

/-- Every positive power of the transfer is the transfer. -/
theorem chartTransfer_pow_succ
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) (n : ℕ) :
    chartTransfer direction mass weight ^ (n + 1) = chartTransfer direction mass weight := by
  induction n with
  | zero => exact pow_one _
  | succ n ih => rw [pow_succ, ih, chartTransfer_idempotent direction mass weight huniv]

/-- Every power sum of the transfer's spectrum is three.  With the idempotence
this is what forces the spectrum to be three ones and three zeros. -/
theorem trace_chartTransfer_pow
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) (n : ℕ) :
    (chartTransfer direction mass weight ^ (n + 1)).trace = 3 := by
  rw [chartTransfer_pow_succ direction mass weight huniv n]
  exact trace_chartTransfer direction mass weight huniv

end Transfer

section SymmetricFunctions

variable (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)

/-- **THE ROW LAW IN LEVERAGE VOCABULARY.**  The cross leverages of one row
total that row's leverage.  The landed erase form gives the off-diagonal part
and the landed diagonal form gives the rest. -/
theorem sum_crossLeverageSq_row
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) (a : Fin size) :
    ∑ b, crossLeverageSq direction mass weight a b
      = chartLeverage direction mass weight a := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    sum_erase_crossLeverageSq direction mass weight huniv a,
    crossLeverageSq_self direction mass weight a]
  ring

/-- **THE TOTAL CROSS LEVERAGE IS THE RANK.**  Summing the row law over all
rows returns the trace. -/
theorem sum_sum_crossLeverageSq
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) :
    ∑ a, ∑ b, crossLeverageSq direction mass weight a b = 3 := by
  classical
  rw [Finset.sum_congr rfl
    (fun a (_ : a ∈ Finset.univ) => sum_crossLeverageSq_row direction mass weight huniv a)]
  exact sum_chartLeverage_eq_three direction mass weight huniv

/-- **THE PAIR MINORS OF THE TRANSFER ARE NONNEGATIVE.**  The two-by-two
principal minors of an idempotent of this shape cannot go negative, because the
inverse form obeys Cauchy-Schwarz.  The landed bound is stated on the inverse
form only, and this is its leverage reading. -/
theorem crossLeverageSq_le_mul_chartLeverage
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hslack : ∀ c, 0 ≤ chartSlack mass weight c) (a b : Fin size) :
    crossLeverageSq direction mass weight a b
      ≤ chartLeverage direction mass weight a * chartLeverage direction mass weight b := by
  have hcs := sq_fullInverseForm_le_mul direction mass weight huniv a b
  have hmul : chartSlack mass weight a * chartSlack mass weight b
      * (fullInverseForm direction mass weight a b) ^ 2
      ≤ chartSlack mass weight a * chartSlack mass weight b
        * (fullInverseForm direction mass weight a a
          * fullInverseForm direction mass weight b b) :=
    mul_le_mul_of_nonneg_left hcs (mul_nonneg (hslack a) (hslack b))
  rw [crossLeverageSq, chartLeverage, chartLeverage]
  nlinarith [hmul]

/-- **THE SECOND SYMMETRIC FUNCTION OF THE TRANSFER IS THREE.**  Over ordered
pairs the two-by-two principal minors of the transfer total six, and the
diagonal pairs contribute nothing, so the unordered total is three.  With the
trace law this pins `e₁ = 3` and `e₂ = 3`, which is `C(3,1)` and `C(3,2)` — the
signature of an idempotent of rank three. -/
theorem sum_pairMinor_chartTransfer
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) :
    ∑ a, ∑ b, (chartLeverage direction mass weight a * chartLeverage direction mass weight b
        - crossLeverageSq direction mass weight a b) = 6 := by
  classical
  have hsplit : ∑ a, ∑ b, (chartLeverage direction mass weight a
        * chartLeverage direction mass weight b
        - crossLeverageSq direction mass weight a b)
      = (∑ a, ∑ b, chartLeverage direction mass weight a
            * chartLeverage direction mass weight b)
        - ∑ a, ∑ b, crossLeverageSq direction mass weight a b := by
    simp only [Finset.sum_sub_distrib]
  have hprod : ∑ a, ∑ b, chartLeverage direction mass weight a
        * chartLeverage direction mass weight b = 9 := by
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => (Finset.mul_sum _ _ _).symm),
      ← Finset.sum_mul, sum_chartLeverage_eq_three direction mass weight huniv]
    norm_num
  rw [hsplit, hprod, sum_sum_crossLeverageSq direction mass weight huniv]
  norm_num

end SymmetricFunctions

section UnitSlack

/-- **THE UNIT-SLACK MASS.**  The mass that makes every chart slack exactly one.
It is the gauge in which the transfer is symmetric. -/
noncomputable def unitSlackMass (weight : Fin size → ℝ) (c : Fin size) : ℝ :=
  weight c / (1 - weight c)

theorem unitSlackMass_pos (weight : Fin size → ℝ) (hw : ∀ c, 0 < weight c)
    (hwlt : ∀ c, weight c < 1) (c : Fin size) : 0 < unitSlackMass weight c :=
  div_pos (hw c) (sub_pos.mpr (hwlt c))

/-- **THE UNIT-SLACK MASS HAS SLACK ONE.**  Root-free, and it is what makes the
converse below constructive. -/
theorem chartSlack_unitSlackMass (weight : Fin size → ℝ) (hw : ∀ c, 0 < weight c)
    (hwlt : ∀ c, weight c < 1) (c : Fin size) :
    chartSlack (unitSlackMass weight) weight c = 1 := by
  have hne : (1 : ℝ) - weight c ≠ 0 := ne_of_gt (sub_pos.mpr (hwlt c))
  have hwne : weight c ≠ 0 := ne_of_gt (hw c)
  rw [chartSlack, unitSlackMass]
  field_simp

/-- **AT UNIT SLACK THE FULL GAP IS THE UNWEIGHTED GRAM.**  Every rank-three
configuration of directions is realized by a chart point whose full-selection
gap is the plain Gram of those directions.  This is the converse half of the
reduction: the transfer's spectrum carries no information about the masses. -/
theorem directionChartGap_univ_unitSlack (direction : Fin size → (Fin 3 → ℝ))
    (weight : Fin size → ℝ) (hw : ∀ c, 0 < weight c) (hwlt : ∀ c, weight c < 1) :
    directionChartGap direction (unitSlackMass weight) weight Finset.univ
      = ∑ c, atomMatrix (direction c) := by
  classical
  rw [directionChartGap_univ_eq_slackLaplacian, slackLaplacian]
  exact Finset.sum_congr rfl fun c _ => by
    rw [chartSlack_unitSlackMass weight hw hwlt c, one_smul]

/-- **AT UNIT SLACK THE TRANSFER IS THE INVERSE FORM.**  The slack scaling is
gone, so the transfer is symmetric and is the orthogonal projection onto the
span of the directions. -/
theorem chartTransfer_unitSlack (direction : Fin size → (Fin 3 → ℝ))
    (weight : Fin size → ℝ) (hw : ∀ c, 0 < weight c) (hwlt : ∀ c, weight c < 1)
    (a b : Fin size) :
    chartTransfer direction (unitSlackMass weight) weight a b
      = fullInverseForm direction (unitSlackMass weight) weight a b := by
  rw [chartTransfer_apply, chartSlack_unitSlackMass weight hw hwlt a, one_mul]

/-- The unit-slack transfer is symmetric. -/
theorem chartTransfer_unitSlack_symm (direction : Fin size → (Fin 3 → ℝ))
    (weight : Fin size → ℝ) (hw : ∀ c, 0 < weight c) (hwlt : ∀ c, weight c < 1)
    (huniv : (directionChartGap direction (unitSlackMass weight) weight Finset.univ).PosDef)
    (a b : Fin size) :
    chartTransfer direction (unitSlackMass weight) weight a b
      = chartTransfer direction (unitSlackMass weight) weight b a := by
  rw [chartTransfer_unitSlack direction weight hw hwlt a b,
    chartTransfer_unitSlack direction weight hw hwlt b a,
    fullInverseForm_comm direction (unitSlackMass weight) weight huniv a b]

/-- At unit slack the leverage is the diagonal of the inverse form. -/
theorem chartLeverage_unitSlack (direction : Fin size → (Fin 3 → ℝ))
    (weight : Fin size → ℝ) (hw : ∀ c, 0 < weight c) (hwlt : ∀ c, weight c < 1)
    (a : Fin size) :
    chartLeverage direction (unitSlackMass weight) weight a
      = fullInverseForm direction (unitSlackMass weight) weight a a := by
  rw [chartLeverage, chartSlack_unitSlackMass weight hw hwlt a, one_mul]

end UnitSlack

end Gtz
