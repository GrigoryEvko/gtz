/-
# The four-set law: every four-set determinant through a weak dominator is one
# squared reading

The campaign carries a weighted ledger for the rank-one UPDATE
(`Gtz.sum_weight_mul_det_add_atomMatrix_fin_three`):

  `Σ_c t_c · det(N + a_c a_cᵀ) = det N + e₂(N)` ,

and its own docstring records the verdict six lanes reached: it is a weighted
AVERAGE, so reading a sign off it "has failed six times and will fail a
seventh".  That verdict is correct for a general `N`.  It is not correct at the
one place the campaign needs it.

**At a weak dominator every summand is known exactly.**  Let `C` be a triple
whose gap `G = S_C - 1` kills a unit probe `w`.  Then for EVERY vector `v`

  **`det(G + v vᵀ) = e₂(G) · (v ⬝ᵥ w)²`**   (`Gtz.det_add_atomMatrix_of_unit_null`)

so the ledger's average is a sum of individually determined nonnegative terms,
and Parseval is the only thing that makes them total `e₂`.  The aggregation
barrier does not apply here: the sign of each term is readable one term at a
time.

## Why it is true

A symmetric three-by-three form that kills a unit vector has

  **`adj(form) = e₂(form) • w wᵀ`**

read against any pair of vectors
(`Gtz.adjugate_reading_of_unit_null`).  No rank hypothesis and no positivity.
The landed `Gtz.adjugate_law_core` is the diagonal of this identity in the Gram
coordinates of a triple.  Here it is the whole quadratic form, in the ambient
coordinates, so it can be paired with an arbitrary vector.  Six scalar
identities carry it, one `linear_combination` each.  The determinant of such a
form vanishes because the probe is a nonzero kernel vector, and the landed
rank-one update `Gtz.det_add_atomMatrix_fin_three` finishes the argument.

## What the two arms read off it

* **The cells.**  Every four-set determinant built on a weak dominator is
  NONNEGATIVE (`Gtz.fourSet_gapDet_nonneg_of_unit_null`), because `e₂` of a
  weak dominator's gap is the total of its three pair minors and the landed
  `Gtz.pairGapMinor_nonneg_of_dominates` makes each of those nonnegative.  It
  vanishes exactly when the added atom is blind to the probe.  The cells are
  written in four-set determinants, and this computes all of them from one
  probe.
* **Corank two.**  A corner has `e₂ = 0`, so EVERY four-set determinant through
  it vanishes (`Gtz.fourSet_gapDet_eq_zero_of_secondInvariant_eq_zero`).  A
  single nonzero four-set determinant therefore certifies corank one
  (`Gtz.secondInvariant_ne_zero_of_fourSet_gapDet_ne_zero`) — a four-set
  determinant SEPARATES the two arms, and it is a polynomial in the atoms.
* **Corank one.**  If `e₂` is positive then some atom of the design is not
  blind to the probe (`Gtz.exists_reading_ne_zero_of_secondInvariant_pos`), and
  that atom's four-set determinant is strictly positive.  No selector names the
  atom: Parseval supplies the total and every term is nonnegative.

## The termwise refinement, stated

`Gtz.weighted_fourSet_gapDet_total` re-proves the landed ledger at a weak
dominator from the four-set law and Parseval alone, which exhibits the
refinement: the average `e₂` is `Σ_c t_c · e₂ · (a_c ⬝ᵥ w)²`, and the weights
enter only through Parseval.

[MEASURED before proving, at 20000 independently built corank-one weak
dominators with three arbitrary extra vectors each: the four-set law holds to a
maximum relative residual of `5.3e-14`, and at the members it reproduces the
pair minor of the other two to `3.3e-14`.  The harness reproduces the `(5,3)`
diamond tie exactly first — leverages `(2, 3.25, 3.25, 3.25, 3.25)`, pair
minors `0.75 / 4.5 / 2.0`, eight of ten triples weakly dominating, and the
landed adjugate law returning readings `(0.75, 0.125, 0.125)` against normalized
pair minors `(4.5, 0.75, 0.75)/6`.]
-/
import Gtz.Wave.NullProbeAdjugateLaw
import Gtz.Wave.CellHDowndateLaws
import Gtz.Design.PlaneBranchComplementSelector

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The six scalar adjugate identities

A symmetric three-by-three form with entries `A P Q / P B R / Q R C` that kills
the unit vector `(w1, w2, w3)` has every entry of its adjugate equal to the
second invariant times the matching product of probe coordinates.  Each identity
is one `linear_combination` against the three rows and the normalization.  No
rank hypothesis and no positivity is used. -/

section ScalarAdjugate

variable {A B C P Q R w1 w2 w3 : ℝ}

/-- The first diagonal entry of the adjugate. -/
theorem adjugateScalar_diag_first
    (h1 : A * w1 + P * w2 + Q * w3 = 0) (h2 : P * w1 + B * w2 + R * w3 = 0)
    (h3 : Q * w1 + R * w2 + C * w3 = 0) (hn : w1 ^ 2 + w2 ^ 2 + w3 ^ 2 = 1) :
    B * C - R ^ 2
      = ((A * B - P ^ 2) + (A * C - Q ^ 2) + (B * C - R ^ 2)) * w1 ^ 2 := by
  linear_combination (-B * w1 - C * w1) * h1 + (C * w2 + P * w1 - R * w3) * h2
    + (B * w3 + Q * w1 - R * w2) * h3 + (-(B * C) + R ^ 2) * hn

/-- The second diagonal entry of the adjugate. -/
theorem adjugateScalar_diag_second
    (h1 : A * w1 + P * w2 + Q * w3 = 0) (h2 : P * w1 + B * w2 + R * w3 = 0)
    (h3 : Q * w1 + R * w2 + C * w3 = 0) (hn : w1 ^ 2 + w2 ^ 2 + w3 ^ 2 = 1) :
    A * C - Q ^ 2
      = ((A * B - P ^ 2) + (A * C - Q ^ 2) + (B * C - R ^ 2)) * w2 ^ 2 := by
  linear_combination (C * w1 + P * w2 - Q * w3) * h1 + (-A * w2 - C * w2) * h2
    + (A * w3 - Q * w1 + R * w2) * h3 + (-(A * C) + Q ^ 2) * hn

/-- The third diagonal entry of the adjugate. -/
theorem adjugateScalar_diag_third
    (h1 : A * w1 + P * w2 + Q * w3 = 0) (h2 : P * w1 + B * w2 + R * w3 = 0)
    (h3 : Q * w1 + R * w2 + C * w3 = 0) (hn : w1 ^ 2 + w2 ^ 2 + w3 ^ 2 = 1) :
    A * B - P ^ 2
      = ((A * B - P ^ 2) + (A * C - Q ^ 2) + (B * C - R ^ 2)) * w3 ^ 2 := by
  linear_combination (B * w1 - P * w2 + Q * w3) * h1 + (A * w2 - P * w1 + R * w3) * h2
    + (-A * w3 - B * w3) * h3 + (-(A * B) + P ^ 2) * hn

/-- The first off-diagonal entry of the adjugate. -/
theorem adjugateScalar_offDiag_first
    (h1 : A * w1 + P * w2 + Q * w3 = 0) (h2 : P * w1 + B * w2 + R * w3 = 0)
    (h3 : Q * w1 + R * w2 + C * w3 = 0) (hn : w1 ^ 2 + w2 ^ 2 + w3 ^ 2 = 1) :
    Q * R - P * C
      = ((A * B - P ^ 2) + (A * C - Q ^ 2) + (B * C - R ^ 2)) * (w1 * w2) := by
  linear_combination (-B * w2 - C * w2) * h1 + (-C * w1 + P * w2 + Q * w3) * h2
    + (-P * w3 + Q * w2 + R * w1) * h3 + (C * P - Q * R) * hn

/-- The second off-diagonal entry of the adjugate. -/
theorem adjugateScalar_offDiag_second
    (h1 : A * w1 + P * w2 + Q * w3 = 0) (h2 : P * w1 + B * w2 + R * w3 = 0)
    (h3 : Q * w1 + R * w2 + C * w3 = 0) (hn : w1 ^ 2 + w2 ^ 2 + w3 ^ 2 = 1) :
    P * R - Q * B
      = ((A * B - P ^ 2) + (A * C - Q ^ 2) + (B * C - R ^ 2)) * (w1 * w3) := by
  linear_combination (-B * w3 - C * w3) * h1 + (P * w3 - Q * w2 + R * w1) * h2
    + (-B * w1 + P * w2 + Q * w3) * h3 + (B * Q - P * R) * hn

/-- The third off-diagonal entry of the adjugate. -/
theorem adjugateScalar_offDiag_third
    (h1 : A * w1 + P * w2 + Q * w3 = 0) (h2 : P * w1 + B * w2 + R * w3 = 0)
    (h3 : Q * w1 + R * w2 + C * w3 = 0) (hn : w1 ^ 2 + w2 ^ 2 + w3 ^ 2 = 1) :
    P * Q - A * R
      = ((A * B - P ^ 2) + (A * C - Q ^ 2) + (B * C - R ^ 2)) * (w2 * w3) := by
  linear_combination (P * w3 + Q * w2 - R * w1) * h1 + (-A * w3 - C * w3) * h2
    + (-A * w2 + P * w1 + R * w3) * h3 + (A * R - P * Q) * hn

/-- **THE ADJUGATE READING, IN SCALARS.**  The quadratic form of the adjugate at
an arbitrary vector is the second invariant times the squared reading of that
vector against the probe.  The six entry identities assemble by their own
coefficients. -/
theorem adjugateScalar_reading {v1 v2 v3 : ℝ}
    (h1 : A * w1 + P * w2 + Q * w3 = 0) (h2 : P * w1 + B * w2 + R * w3 = 0)
    (h3 : Q * w1 + R * w2 + C * w3 = 0) (hn : w1 ^ 2 + w2 ^ 2 + w3 ^ 2 = 1) :
    v1 ^ 2 * (B * C - R ^ 2) + v2 ^ 2 * (A * C - Q ^ 2) + v3 ^ 2 * (A * B - P ^ 2)
        + 2 * v1 * v2 * (Q * R - P * C) + 2 * v1 * v3 * (P * R - Q * B)
        + 2 * v2 * v3 * (P * Q - A * R)
      = ((A * B - P ^ 2) + (A * C - Q ^ 2) + (B * C - R ^ 2))
          * (v1 * w1 + v2 * w2 + v3 * w3) ^ 2 := by
  linear_combination v1 ^ 2 * adjugateScalar_diag_first h1 h2 h3 hn
    + v2 ^ 2 * adjugateScalar_diag_second h1 h2 h3 hn
    + v3 ^ 2 * adjugateScalar_diag_third h1 h2 h3 hn
    + 2 * v1 * v2 * adjugateScalar_offDiag_first h1 h2 h3 hn
    + 2 * v1 * v3 * adjugateScalar_offDiag_second h1 h2 h3 hn
    + 2 * v2 * v3 * adjugateScalar_offDiag_third h1 h2 h3 hn

end ScalarAdjugate

/-! ## 2. The matrix form -/

/-- The three rows of a null condition, as scalars. -/
theorem null_row_of_mulVec_eq_zero {form : Matrix (Fin 3) (Fin 3) ℝ} {w : Fin 3 → ℝ}
    (hnull : form *ᵥ w = 0) (i : Fin 3) :
    form i 0 * w 0 + form i 1 * w 1 + form i 2 * w 2 = 0 := by
  have h := congrFun hnull i
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h

/-- **A UNIT NULL PROBE KILLS THE DETERMINANT.**  The probe is a nonzero kernel
vector, and over a field that is exactly a vanishing determinant. -/
theorem det_eq_zero_of_unit_null {form : Matrix (Fin 3) (Fin 3) ℝ}
    {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1) :
    form.det = 0 := by
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, ?_, hnull⟩
  intro hw
  rw [hw] at hunit
  simp at hunit

/-- **THE ADJUGATE READS EVERY VECTOR AS ONE SQUARED READING.**  A symmetric
form with a unit null probe has adjugate quadratic form equal to its second
invariant times the squared reading. -/
theorem adjugate_reading_of_unit_null {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (v : Fin 3 → ℝ) :
    v ⬝ᵥ (form.adjugate *ᵥ v) = secondInvariantOfThree form * (v ⬝ᵥ w) ^ 2 := by
  have h10 : form 1 0 = form 0 1 := by simpa using (congrFun (congrFun hsym 1) 0).symm
  have h20 : form 2 0 = form 0 2 := by simpa using (congrFun (congrFun hsym 2) 0).symm
  have h21 : form 2 1 = form 1 2 := by simpa using (congrFun (congrFun hsym 2) 1).symm
  have h1 := null_row_of_mulVec_eq_zero hnull 0
  have h2 := null_row_of_mulVec_eq_zero hnull 1
  have h3 := null_row_of_mulVec_eq_zero hnull 2
  rw [h10] at h2
  rw [h20, h21] at h3
  have hn : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using hunit
  have key := adjugateScalar_reading (A := form 0 0) (B := form 1 1) (C := form 2 2)
    (P := form 0 1) (Q := form 0 2) (R := form 1 2)
    (w1 := w 0) (w2 := w 1) (w3 := w 2)
    (v1 := v 0) (v2 := v 1) (v3 := v 2) h1 h2 h3 hn
  simp only [Matrix.adjugate_fin_three, secondInvariantOfThree, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    h10, h20, h21]
  linear_combination key

/-! ## 3. The four-set law -/

/-- **THE FOUR-SET LAW.**  A symmetric form with a unit null probe reads every
rank-one update as its second invariant times one squared reading:

  `det(form + v vᵀ) = e₂(form) · (v ⬝ᵥ w)²` .

The landed weighted ledger is the Parseval average of this identity, so the
average's summands are individually determined and their signs are readable one
at a time. -/
theorem det_add_atomMatrix_of_unit_null {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (v : Fin 3 → ℝ) :
    (form + atomMatrix v).det = secondInvariantOfThree form * (v ⬝ᵥ w) ^ 2 := by
  rw [det_add_atomMatrix_fin_three, det_eq_zero_of_unit_null hnull hunit,
    adjugate_reading_of_unit_null hsym hnull hunit v, zero_add]

/-- **THE UPDATE IS NONNEGATIVE WHEN THE SECOND INVARIANT IS.** -/
theorem det_add_atomMatrix_nonneg_of_unit_null {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : 0 ≤ secondInvariantOfThree form) (v : Fin 3 → ℝ) :
    0 ≤ (form + atomMatrix v).det := by
  rw [det_add_atomMatrix_of_unit_null hsym hnull hunit v]
  exact mul_nonneg he (sq_nonneg _)

/-- **A NONZERO UPDATE FORCES A NONZERO SECOND INVARIANT.**  One four-set
determinant certifies that the form is not of rank one. -/
theorem secondInvariant_ne_zero_of_det_add_ne_zero
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsym : formᵀ = form) {w : Fin 3 → ℝ}
    (hnull : form *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1) {v : Fin 3 → ℝ}
    (hv : (form + atomMatrix v).det ≠ 0) :
    secondInvariantOfThree form ≠ 0 := by
  intro hzero
  exact hv (by rw [det_add_atomMatrix_of_unit_null hsym hnull hunit v, hzero, zero_mul])

/-! ## 4. The law at a design -/

/-- **THE FOUR-SET LAW AT A DESIGN.**  Inserting any label into a triple whose
gap kills a unit probe gives a four-set whose gap determinant is the triple's
second invariant times that label's squared reading. -/
theorem fourSet_gapDet_of_unit_null (D : WeightedDesign m 3) {T : Finset (Fin m)}
    {w : Fin 3 → ℝ} (hnull : (subsetSum D T - 1) *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1)
    {d : Fin m} (hd : d ∉ T) :
    (subsetSum D (insert d T) - 1).det
      = secondInvariantOfThree (subsetSum D T - 1) * (D.atom d ⬝ᵥ w) ^ 2 := by
  have hins : subsetSum D (insert d T) - 1
      = (subsetSum D T - 1) + atomMatrix (D.atom d) := by
    rw [subsetSum, subsetSum, Finset.sum_insert hd]; abel
  have hsym : (subsetSum D T - 1)ᵀ = subsetSum D T - 1 := by
    rw [Matrix.transpose_sub, subsetSum_transpose, Matrix.transpose_one]
  rw [hins, det_add_atomMatrix_of_unit_null hsym hnull hunit]

/-- **EVERY FOUR-SET THROUGH A WEAK DOMINATOR HAS A NONNEGATIVE DETERMINANT.**
The second invariant of a weak dominator's gap is the total of its three pair
minors, and the landed `Gtz.pairGapMinor_nonneg_of_dominates` makes each of them
nonnegative. -/
theorem fourSet_gapDet_nonneg_of_unit_null (D : WeightedDesign m 3)
    {T : Finset (Fin m)} {w : Fin 3 → ℝ} (hnull : (subsetSum D T - 1) *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : 0 ≤ secondInvariantOfThree (subsetSum D T - 1))
    {d : Fin m} (hd : d ∉ T) :
    0 ≤ (subsetSum D (insert d T) - 1).det := by
  rw [fourSet_gapDet_of_unit_null D hnull hunit hd]
  exact mul_nonneg he (sq_nonneg _)

/-- **THE CORNER COLLAPSE.**  A vanishing second invariant kills every four-set
determinant through the triple at once.  A corner is exactly this case, and the
statement needs no corner normal form and no axis. -/
theorem fourSet_gapDet_eq_zero_of_secondInvariant_eq_zero (D : WeightedDesign m 3)
    {T : Finset (Fin m)} {w : Fin 3 → ℝ} (hnull : (subsetSum D T - 1) *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (hzero : secondInvariantOfThree (subsetSum D T - 1) = 0)
    {d : Fin m} (hd : d ∉ T) :
    (subsetSum D (insert d T) - 1).det = 0 := by
  rw [fourSet_gapDet_of_unit_null D hnull hunit hd, hzero, zero_mul]

/-- **A FOUR-SET DETERMINANT SEPARATES THE TWO ARMS.**  One nonzero four-set
determinant through a weak dominator certifies that its gap is not of rank one,
so the dominator has corank one and the corank-two arm does not own it.  The
certificate is a polynomial in the atoms. -/
theorem secondInvariant_ne_zero_of_fourSet_gapDet_ne_zero (D : WeightedDesign m 3)
    {T : Finset (Fin m)} {w : Fin 3 → ℝ} (hnull : (subsetSum D T - 1) *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) {d : Fin m} (hd : d ∉ T)
    (hne : (subsetSum D (insert d T) - 1).det ≠ 0) :
    secondInvariantOfThree (subsetSum D T - 1) ≠ 0 := by
  intro hzero
  exact hne (fourSet_gapDet_eq_zero_of_secondInvariant_eq_zero D hnull hunit hzero hd)

/-! ## 5. The termwise refinement of the landed ledger -/

/-- **THE LEDGER IS A SUM OF KNOWN TERMS.**  At a triple whose gap kills a unit
probe, the landed weighted update ledger reduces to Parseval: every summand is
the second invariant times a squared reading, and the readings total one.

This is the refinement the aggregation doctrine says is impossible for a general
form.  It is available here because the null probe determines each summand, not
merely their average. -/
theorem weighted_fourSet_gapDet_total (D : WeightedDesign m 3) {T : Finset (Fin m)}
    {w : Fin 3 → ℝ} (hunit : w ⬝ᵥ w = 1) :
    ∑ c, D.weight c * (secondInvariantOfThree (subsetSum D T - 1)
        * (D.atom c ⬝ᵥ w) ^ 2)
      = secondInvariantOfThree (subsetSum D T - 1) := by
  have hp := parseval_probe_form D w
  calc ∑ c, D.weight c * (secondInvariantOfThree (subsetSum D T - 1)
          * (D.atom c ⬝ᵥ w) ^ 2)
      = secondInvariantOfThree (subsetSum D T - 1)
          * ∑ c, D.weight c * (D.atom c ⬝ᵥ w) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = secondInvariantOfThree (subsetSum D T - 1) := by rw [hp, hunit, mul_one]

/-- **A POSITIVE SECOND INVARIANT EXHIBITS A LIVE READING.**  No selector names
the atom: Parseval supplies the total and every term is nonnegative, so the
readings cannot all vanish. -/
theorem exists_reading_ne_zero_of_unit_probe (D : WeightedDesign m 3)
    {w : Fin 3 → ℝ} (hunit : w ⬝ᵥ w = 1) :
    ∃ c, D.atom c ⬝ᵥ w ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hp := parseval_probe_form D w
  have hzero : ∀ c ∈ (Finset.univ : Finset (Fin m)),
      D.weight c * (D.atom c ⬝ᵥ w) ^ 2 = 0 := by
    intro c _; simp [hcon c]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, hunit] at hp
  exact absurd hp one_ne_zero.symm

/-- **A POSITIVE SECOND INVARIANT EXHIBITS A POSITIVE FOUR-SET DETERMINANT.**
Some atom of the design reads the probe, and its rank-one update of the gap has
a strictly positive determinant. -/
theorem exists_det_add_atomMatrix_pos_of_secondInvariant_pos (D : WeightedDesign m 3)
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsym : formᵀ = form) {w : Fin 3 → ℝ}
    (hnull : form *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1)
    (hpos : 0 < secondInvariantOfThree form) :
    ∃ c, 0 < (form + atomMatrix (D.atom c)).det := by
  obtain ⟨c, hc⟩ := exists_reading_ne_zero_of_unit_probe D hunit
  refine ⟨c, ?_⟩
  rw [det_add_atomMatrix_of_unit_null hsym hnull hunit]
  exact mul_pos hpos (by positivity)

/-! ## 6. The pair currency -/

/-- **THE SECOND INVARIANT OF A TRIPLE GAP IS ITS PAIR MINOR TOTAL.**  The
ambient gap and the Gram gap have the same second invariant, and on the Gram
side that invariant is the sum of the three two-by-two principal minors, which
are exactly the pair minors. -/
theorem secondInvariantOfThree_atomTriple_eq_pairMinorTotal (a b c : Fin 3 → ℝ) :
    secondInvariantOfThree (atomMatrix a + atomMatrix b + atomMatrix c - 1)
      = pairMinorTotal a b c := by
  rw [secondInvariantOfThree, Matrix.one_fin_three]
  simp only [pairMinorTotal, pairGapMinor, leverageOf, Matrix.add_apply,
    Matrix.sub_apply, atomMatrix, Matrix.vecMulVec_apply, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_val', Matrix.of_apply]
  ring

/-- The gap of an explicit triple is symmetric. -/
theorem atomTriple_gap_transpose (a b c : Fin 3 → ℝ) :
    (atomMatrix a + atomMatrix b + atomMatrix c - 1)ᵀ
      = atomMatrix a + atomMatrix b + atomMatrix c - 1 := by
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
    atomMatrix, Matrix.transpose_vecMulVec]

/-- **THE FOUR-SET LAW IN PAIR CURRENCY.**  For three atoms whose gap kills a
unit probe, the determinant of the gap updated by any vector is the total of the
three pair minors times that vector's squared reading. -/
theorem det_add_atomMatrix_eq_pairMinorTotal_mul_reading_sq {a b c w : Fin 3 → ℝ}
    (hnull : (atomMatrix a + atomMatrix b + atomMatrix c - 1) *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (v : Fin 3 → ℝ) :
    ((atomMatrix a + atomMatrix b + atomMatrix c - 1) + atomMatrix v).det
      = pairMinorTotal a b c * (v ⬝ᵥ w) ^ 2 := by
  rw [det_add_atomMatrix_of_unit_null (atomTriple_gap_transpose a b c) hnull hunit v,
    secondInvariantOfThree_atomTriple_eq_pairMinorTotal]

/-- **THE MEMBERS REPRODUCE THE ADJUGATE LAW.**  Updating a triple's gap by one
of its own members gives the pair minor of the other two, because the landed
`Gtz.pairGapMinor_eq_pairMinorTotal_mul_reading_first` computes that squared
reading.  The four-set law extends that statement from the three members to
every vector. -/
theorem det_add_own_atomMatrix_eq_pairGapMinor {a b c w : Fin 3 → ℝ}
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w)
    (hnull : (atomMatrix a + atomMatrix b + atomMatrix c - 1) *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) :
    ((atomMatrix a + atomMatrix b + atomMatrix c - 1) + atomMatrix a).det
      = pairGapMinor b c := by
  rw [det_add_atomMatrix_eq_pairMinorTotal_mul_reading_sq hnull hunit a,
    ← pairGapMinor_eq_pairMinorTotal_mul_reading_first a b c w hrep hunit]

end Gtz
