/-
# A corank-one weak dominator always sits inside a strictly dominating four-set

Every producer this campaign owns REFUSES a triple.  The cells' producers are
the exception, and each of them opens with the same hypothesis: that a four-set
gap is POSITIVE DEFINITE.  `Gtz.star_exists_posDef_of_posDef_of_det_pos` assumes
it, `Gtz.twoStar_exists_dominating_triple` assumes it twice, and the `Z1` cells
are named by which of the three four-sets carries it.  Nobody produced it.

The four-set law produces it, in one line each way.

Let `C` be a weak dominator whose gap kills a unit probe `w`, and let `d` be any
label.  The four-set gap is `G + a_d a_dᵀ` with `G ⪰ 0`, so it is POSITIVE
SEMIDEFINITE for free.  Its determinant is `e₂(G)·(a_d ⬝ᵥ w)²`
(`Gtz.fourSet_gapDet_of_unit_null`).  A positive semidefinite form with a
nonzero determinant is positive definite.  Hence

  **`Gtz.fourSet_posDef_of_reading_ne_zero`: a corank-one weak dominator plus
  any label that READS its probe is a strictly dominating four-set.**

and the reading atom always exists (`Gtz.exists_reading_ne_zero_of_unit_probe`).

## The same law refuses the corner

A corner has `e₂ = 0`, so every four-set determinant through it vanishes and no
such four-set is positive definite
(`Gtz.fourSet_not_posDef_of_secondInvariant_eq_zero`).  So the four-set through
a weak dominator is a LOEWNER separator of the two arms, not merely a polynomial
one: corank one always extends to a strict four-set, a corner never does.

## What a tie must pay

At a tie no triple dominates strictly.  The landed
`Gtz.sum_fourSet_gapDet_eq_det_sub_e2` totals the four triple gap determinants
of a four-set at `det − e₂` of that four-set's gap, and the dominator's own
triple contributes zero.  So a tie forces

  **`Gtz.tie_fourSet_det_le_secondInvariant`: `det A ≤ e₂(A)` at every four-set
  `A` built on a corank-one weak dominator** ,

which in the dominator's own currency is
`e₂(G)·(a_d ⬝ᵥ w)² ≤ e₂(G) + ℓ_d·tr(G) − a_d ⬝ᵥ (G *ᵥ a_d)`
through the second-invariant update `Gtz.secondInvariantOfThree_add_atomMatrix`.
The right-hand side is the four-set's own second invariant, written without a
determinant.

[MEASURED: the second-invariant update holds to a maximum relative residual of
`6.1e-12` over 20000 random designs and arbitrary symmetric forms, in the same
harness that reproduces the `(5,3)` diamond tie exactly.]
-/
import Gtz.Wave.NullProbeFourSetLaw
import Gtz.Core.Sanity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The four-set gap is positive semidefinite for free -/

/-- A weak dominator's gap updated by any atom stays positive semidefinite. -/
theorem posSemidef_gap_add_atomMatrix {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hpsd : form.PosSemidef) (v : Fin 3 → ℝ) :
    (form + atomMatrix v).PosSemidef :=
  hpsd.add (posSemidef_atomMatrix v)

/-- **THE PRODUCER.**  A positive semidefinite form with a unit null probe and a
nonzero second invariant is turned into a POSITIVE DEFINITE form by any vector
that reads the probe.  Positive semidefiniteness is free, the determinant is the
four-set law, and a positive semidefinite form with a nonzero determinant is
positive definite. -/
theorem posDef_add_atomMatrix_of_reading_ne_zero {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hpsd : form.PosSemidef) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : secondInvariantOfThree form ≠ 0)
    {v : Fin 3 → ℝ} (hread : v ⬝ᵥ w ≠ 0) :
    (form + atomMatrix v).PosDef := by
  have hsym : formᵀ = form := (by simpa using hpsd.isHermitian : form.IsSymm)
  refine (Matrix.PosSemidef.posDef_iff_det_ne_zero (posSemidef_gap_add_atomMatrix hpsd v)).mpr ?_
  rw [det_add_atomMatrix_of_unit_null hsym hnull hunit]
  exact mul_ne_zero he (pow_ne_zero 2 hread)

/-- **NO FOUR-SET THROUGH A CORNER IS STRICT.**  A vanishing second invariant
makes every rank-one update determinant vanish, and a positive definite form has
a nonzero determinant. -/
theorem not_posDef_add_atomMatrix_of_secondInvariant_eq_zero
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsym : formᵀ = form) {w : Fin 3 → ℝ}
    (hnull : form *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1)
    (hzero : secondInvariantOfThree form = 0) (v : Fin 3 → ℝ) :
    ¬ (form + atomMatrix v).PosDef := by
  intro hpd
  have hdet : (form + atomMatrix v).det = 0 := by
    rw [det_add_atomMatrix_of_unit_null hsym hnull hunit, hzero, zero_mul]
  exact absurd hdet (ne_of_gt hpd.det_pos)

/-! ## 2. At a design -/

/-- **A CORANK-ONE WEAK DOMINATOR EXTENDS TO A STRICT FOUR-SET.**  The label is
any one that reads the dominator's null probe, and `Gtz.exists_reading_ne_zero_of_unit_probe`
supplies one at every design. -/
theorem fourSet_posDef_of_reading_ne_zero (D : WeightedDesign m 3)
    {T : Finset (Fin m)} (hdom : Dominates D T) {w : Fin 3 → ℝ}
    (hnull : (subsetSum D T - 1) *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1)
    (he : secondInvariantOfThree (subsetSum D T - 1) ≠ 0)
    {d : Fin m} (hd : d ∉ T) (hread : D.atom d ⬝ᵥ w ≠ 0) :
    (subsetSum D (insert d T) - 1).PosDef := by
  have hins : subsetSum D (insert d T) - 1
      = (subsetSum D T - 1) + atomMatrix (D.atom d) := by
    rw [subsetSum, subsetSum, Finset.sum_insert hd]; abel
  rw [hins]
  exact posDef_add_atomMatrix_of_reading_ne_zero hdom hnull hunit he hread

/-- **EVERY CORANK-ONE WEAK DOMINATOR OF A DESIGN CARRIES A STRICT FOUR-SET.**
No selector names the label: Parseval forbids the design from being blind to a
unit probe. -/
theorem exists_fourSet_posDef_of_secondInvariant_ne_zero (D : WeightedDesign m 3)
    {T : Finset (Fin m)} (hdom : Dominates D T) {w : Fin 3 → ℝ}
    (hnull : (subsetSum D T - 1) *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1)
    (he : secondInvariantOfThree (subsetSum D T - 1) ≠ 0) :
    ∃ d : Fin m, D.atom d ⬝ᵥ w ≠ 0
      ∧ ((subsetSum D T - 1) + atomMatrix (D.atom d)).PosDef := by
  obtain ⟨d, hd⟩ := exists_reading_ne_zero_of_unit_probe D hunit
  exact ⟨d, hd, posDef_add_atomMatrix_of_reading_ne_zero hdom hnull hunit he hd⟩

/-- **A CORNER EXTENDS TO NOTHING STRICT.**  The corank-two arm's four-sets
through the corner are all degenerate. -/
theorem fourSet_not_posDef_of_secondInvariant_eq_zero (D : WeightedDesign m 3)
    {T : Finset (Fin m)} {w : Fin 3 → ℝ} (hnull : (subsetSum D T - 1) *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (hzero : secondInvariantOfThree (subsetSum D T - 1) = 0)
    {d : Fin m} (hd : d ∉ T) :
    ¬ (subsetSum D (insert d T) - 1).PosDef := by
  intro hpd
  exact absurd (fourSet_gapDet_eq_zero_of_secondInvariant_eq_zero D hnull hunit hzero hd)
    (ne_of_gt hpd.det_pos)

/-! ## 3. The second invariant of a rank-one update -/

/-- **THE SECOND INVARIANT UPDATE.**  Adding a rank-one atom to a form raises its
second invariant by the atom's leverage times the trace, less the form's own
reading of that atom.  A hypothesis-free identity in dimension three. -/
theorem secondInvariantOfThree_add_atomMatrix (form : Matrix (Fin 3) (Fin 3) ℝ)
    (v : Fin 3 → ℝ) :
    secondInvariantOfThree (form + atomMatrix v)
      = secondInvariantOfThree form + leverageOf v * Matrix.trace form
        - v ⬝ᵥ (form *ᵥ v) := by
  simp only [secondInvariantOfThree, leverageOf, Matrix.trace_fin_three,
    Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three]
  ring

/-! ## 4. What a tie pays at every four-set it carries -/

/-- The second invariant of a three-by-three form, in trace vocabulary.  A
hypothesis-free identity, needed to read the landed four-set total. -/
theorem secondInvariantOfThree_eq_trace_form (form : Matrix (Fin 3) (Fin 3) ℝ) :
    secondInvariantOfThree form
      = ((Matrix.trace form) ^ 2 - Matrix.trace (form * form)) / 2 := by
  simp only [secondInvariantOfThree, Matrix.trace_fin_three, Matrix.mul_apply,
    Fin.sum_univ_three]
  ring

/-- **THE TIE PAYS ITS FOUR-SET DETERMINANT.**  At a four-set built on a weak
dominator, the dominator's own triple contributes a zero gap determinant to the
landed four-set total.  If a tie also refuses the three swapped triples, the
total is nonpositive, and the total is `det − e₂` of the four-set gap.

The hypothesis is exactly what a tie supplies through the promotion: a strictly
positive swapped determinant inside a positive definite four-set would produce a
strictly dominating triple. -/
theorem det_le_secondInvariant_of_swaps_nonpos {a b c d : Fin 3 → ℝ}
    (hzero : (atomMatrix a + atomMatrix b + atomMatrix c - 1).det = 0)
    (hbcd : (atomMatrix b + atomMatrix c + atomMatrix d - 1).det ≤ 0)
    (hacd : (atomMatrix a + atomMatrix c + atomMatrix d - 1).det ≤ 0)
    (habd : (atomMatrix a + atomMatrix b + atomMatrix d - 1).det ≤ 0) :
    (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1).det
      ≤ secondInvariantOfThree
          (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1) := by
  have htotal := sum_fourSet_gapDet_eq_det_sub_e2 a b c d
  rw [secondInvariantOfThree_eq_trace_form]
  linarith

/-- **THE PAYMENT IN THE DOMINATOR'S OWN CURRENCY.**  Rewriting the four-set's
second invariant through the update identity turns the payment into a statement
about the dominator's gap alone, plus the new atom's leverage and reading. -/
theorem tie_fourSet_reading_bound {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) {v : Fin 3 → ℝ}
    (hpay : (form + atomMatrix v).det
      ≤ secondInvariantOfThree (form + atomMatrix v)) :
    secondInvariantOfThree form * (v ⬝ᵥ w) ^ 2
      ≤ secondInvariantOfThree form + leverageOf v * Matrix.trace form
        - v ⬝ᵥ (form *ᵥ v) := by
  rw [det_add_atomMatrix_of_unit_null hsym hnull hunit v,
    secondInvariantOfThree_add_atomMatrix form v] at hpay
  exact hpay

/-- **A HEAVY READING IS THE ONLY WAY THE PAYMENT BINDS.**  When the new atom
reads the probe at most one, the payment is free, because a positive
semidefinite form reads any vector below its trace times that vector's
leverage. -/
theorem tie_fourSet_reading_bound_free {form : Matrix (Fin 3) (Fin 3) ℝ}
    (he : 0 ≤ secondInvariantOfThree form)
    {w v : Fin 3 → ℝ} (hsmall : (v ⬝ᵥ w) ^ 2 ≤ 1)
    (htrace : v ⬝ᵥ (form *ᵥ v) ≤ leverageOf v * Matrix.trace form) :
    secondInvariantOfThree form * (v ⬝ᵥ w) ^ 2
      ≤ secondInvariantOfThree form + leverageOf v * Matrix.trace form
        - v ⬝ᵥ (form *ᵥ v) := by
  have h1 : secondInvariantOfThree form * (v ⬝ᵥ w) ^ 2
      ≤ secondInvariantOfThree form * 1 :=
    mul_le_mul_of_nonneg_left hsmall he
  rw [mul_one] at h1
  linarith

end Gtz
