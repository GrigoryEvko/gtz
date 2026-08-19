import Gtz.Wave.CornerSecondMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# A corner where the co-weighted outside aggregate sees what the unweighted one
cannot

The corner ledger `Gtz.corner_pairRefusal_bound` consumes the three outside
refusal slacks of one inside pair through their UNWEIGHTED sum.  The campaign
believed that this was the whole content of those three refusals: a symmetric
matrix has an orthonormal basis with nonnegative diagonal exactly when its trace
is nonnegative, so freeing the outside frame makes the three refusals equivalent
to their sum.  The conclusion drawn was that no pair-by-pair programme can beat
the unweighted aggregate.

That conclusion is false, and the reason is that the outside frame is NOT free.
The co-weighted Parseval identity pins `Σ_d (1−t_d) g_d g_dᵀ` as well as
`Σ_d g_d g_dᵀ`, so the frame is the eigenframe of one fixed matrix and its
co-weights are that matrix's eigenvalues.  A second weighting is therefore
available, and it is strictly sharper.

## The foil

`Gtz.ledgerFoil` is an exact rational `(6,3)` design with a NON-PLANAR
corank-two corner at `C = {0,1,2}`, gap scale `lam = 3` and gap axis `e₁`.  At
the admissible inside pair `{0,1}`:

* the three outside slacks are `288575/3650112`, `288575/3650112` and
  `−210889/1825056`;
* their UNWEIGHTED sum is `38843/912528 > 0`
  (`Gtz.ledgerFoil_aggregate_nonneg`), so `Gtz.corner_pairRefusal_bound` holds
  and says nothing;
* their CO-WEIGHTED sum is `−227837953/83614028112 < 0`
  (`Gtz.ledgerFoil_coweight_neg`), so `Gtz.ghostDeficitForm_ge_coweight_slack`
  refutes the tie at that same pair.

The third outside slack is negative, so the triple `{2,3,4}` dominates the foil
strictly and the foil is not a tie (`Gtz.ledgerFoil_not_isTie`).  The point of
the foil is not the refutation but the SEPARATION: one landed law is blind
exactly where the co-weighted law is not.
-/

namespace Gtz

open Matrix Finset

namespace LedgerFoil

/-- The six atoms of the foil. -/
noncomputable def atomFn : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![0, 1, 0]
  | 1 => ![0, 0, 1]
  | 2 => ![2, 0, 0]
  | 3 => ![1 / 8, 6 / 5, -(6 / 5)]
  | 4 => ![1 / 8, -(6 / 5), -(6 / 5)]
  | 5 => ![-(7 / 4), 0, -2]

/-- The six weights of the foil. -/
noncomputable def weightFn : Fin 6 → ℝ
  | 0 => 1221 / 10181
  | 1 => 463 / 30543
  | 2 => 20851 / 91629
  | 3 => 28000 / 91629
  | 4 => 28000 / 91629
  | 5 => 800 / 30543

/-- The gap axis of the corner. -/
def axisVec : Fin 3 → ℝ := ![1, 0, 0]

/-- The six-set gap of the foil, in closed form. -/
noncomputable def gapMat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![195 / 32, 0, 16 / 5; 0, 72 / 25, 0; 16 / 5, 0, 172 / 25]

/-- The inverse of the six-set gap, in closed form. -/
noncomputable def gapInvMat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1376 / 6337, 0, -(640 / 6337); 0, 25 / 72, 0; -(640 / 6337), 0, 4875 / 25348]

end LedgerFoil

open LedgerFoil

/-- **The foil.**  An exact rational `(6,3)` design with a non-planar corank-two
corner at `{0,1,2}`. -/
noncomputable def ledgerFoil : WeightedDesign 6 3 where
  atom := atomFn
  weight := weightFn
  weight_pos := by
    intro c
    fin_cases c <;> norm_num [weightFn]
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    norm_num [weightFn]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [atomFn, weightFn, atomMatrix, Matrix.cons_val_two] <;> norm_num

/-! ## 1. The closed forms -/

/-- The six-set gap of the foil. -/
theorem ledgerFoil_atom : ledgerFoil.atom = atomFn := rfl

theorem ledgerFoil_weight : ledgerFoil.weight = weightFn := rfl

theorem ledgerFoil_gapMat : subsetSum ledgerFoil Finset.univ - 1 = gapMat := by
  rw [subsetSum, Fin.sum_univ_six]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ledgerFoil_atom, atomFn, atomMatrix, Matrix.cons_val_two, gapMat]

/-- The inverse of the six-set gap of the foil. -/
theorem ledgerFoil_gapInv :
    (subsetSum ledgerFoil Finset.univ - 1)⁻¹ = gapInvMat := by
  rw [ledgerFoil_gapMat]
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gapMat, gapInvMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
    norm_num

/-- **The corner.**  The inside triple is orthogonal with one doubled axis, so
its gap is three times the atom matrix of the first axis. -/
theorem ledgerFoil_corner :
    subsetSum ledgerFoil ({0, 1, 2} : Finset (Fin 6)) - 1
      = (3 : ℝ) • atomMatrix axisVec := by
  have hsum : subsetSum ledgerFoil ({0, 1, 2} : Finset (Fin 6))
      = atomMatrix (ledgerFoil.atom 0) + atomMatrix (ledgerFoil.atom 1)
        + atomMatrix (ledgerFoil.atom 2) := by
    rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    abel
  rw [hsum]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ledgerFoil_atom, atomFn, axisVec, atomMatrix, Matrix.cons_val_two]

/-- **The corner is non-planar.**  The outside atom `3` reads the gap axis. -/
theorem ledgerFoil_nonplanar : ledgerFoil.atom 3 ⬝ᵥ axisVec = 1 / 8 := by
  norm_num [ledgerFoil_atom, atomFn, axisVec, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-! ## 2. The pivots that the pair reads -/

/-- The pivot table entries the pair `{0,1}` reads. -/
theorem ledgerFoil_pivot (a b : Fin 6) :
    sixSetPivot ledgerFoil a b = atomFn a ⬝ᵥ (gapInvMat *ᵥ atomFn b) := by
  rw [sixSetPivot, ledgerFoil_gapInv, ledgerFoil_atom]

theorem ledgerFoil_pivot_00 : sixSetPivot ledgerFoil 0 0 = 25 / 72 := by
  rw [ledgerFoil_pivot]
  norm_num [atomFn, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem ledgerFoil_pivot_11 : sixSetPivot ledgerFoil 1 1 = 4875 / 25348 := by
  rw [ledgerFoil_pivot]
  norm_num [atomFn, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem ledgerFoil_pivot_01 : sixSetPivot ledgerFoil 0 1 = 0 := by
  rw [ledgerFoil_pivot]
  norm_num [atomFn, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem ledgerFoil_pivot_03 : sixSetPivot ledgerFoil 0 3 = 5 / 12 := by
  rw [ledgerFoil_pivot]
  norm_num [atomFn, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem ledgerFoil_pivot_04 : sixSetPivot ledgerFoil 0 4 = -(5 / 12) := by
  rw [ledgerFoil_pivot]
  norm_num [atomFn, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem ledgerFoil_pivot_05 : sixSetPivot ledgerFoil 0 5 = 0 := by
  rw [ledgerFoil_pivot]
  norm_num [atomFn, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem ledgerFoil_pivot_13 : sixSetPivot ledgerFoil 1 3 = -(3085 / 12674) := by
  rw [ledgerFoil_pivot]
  norm_num [atomFn, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem ledgerFoil_pivot_14 : sixSetPivot ledgerFoil 1 4 = -(3085 / 12674) := by
  rw [ledgerFoil_pivot]
  norm_num [atomFn, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem ledgerFoil_pivot_15 : sixSetPivot ledgerFoil 1 5 = -(2635 / 12674) := by
  rw [ledgerFoil_pivot]
  norm_num [atomFn, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem ledgerFoil_pivot_33 : sixSetPivot ledgerFoil 3 3 = 5137 / 6337 := by
  rw [ledgerFoil_pivot]
  norm_num [atomFn, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem ledgerFoil_pivot_44 : sixSetPivot ledgerFoil 4 4 = 5137 / 6337 := by
  rw [ledgerFoil_pivot]
  norm_num [atomFn, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem ledgerFoil_pivot_55 : sixSetPivot ledgerFoil 5 5 = 4609 / 6337 := by
  rw [ledgerFoil_pivot]
  norm_num [atomFn, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-! ## 3. The pair is admissible and its three outside slacks are exact -/

/-- The pair minor of `{0,1}`. -/
theorem ledgerFoil_pairMinor : pairPivotMinor ledgerFoil 0 1 = 962231 / 1825056 := by
  rw [pairPivotMinor, ledgerFoil_pivot_00, ledgerFoil_pivot_11, ledgerFoil_pivot_01]
  norm_num

/-- The pair `{0,1}` is admissible. -/
theorem ledgerFoil_admissible :
    sixSetPivot ledgerFoil 0 0 < 1 ∧ 0 < pairPivotMinor ledgerFoil 0 1 := by
  rw [ledgerFoil_pivot_00, ledgerFoil_pairMinor]
  norm_num

theorem ledgerFoil_slack_three :
    pairRefusalSlack ledgerFoil 0 1 3 = 288575 / 3650112 := by
  rw [pairRefusalSlack, pairPivotMinor, ledgerFoil_pivot_00, ledgerFoil_pivot_11,
    ledgerFoil_pivot_01, ledgerFoil_pivot_03, ledgerFoil_pivot_13, ledgerFoil_pivot_33]
  norm_num

theorem ledgerFoil_slack_four :
    pairRefusalSlack ledgerFoil 0 1 4 = 288575 / 3650112 := by
  rw [pairRefusalSlack, pairPivotMinor, ledgerFoil_pivot_00, ledgerFoil_pivot_11,
    ledgerFoil_pivot_01, ledgerFoil_pivot_04, ledgerFoil_pivot_14, ledgerFoil_pivot_44]
  norm_num

/-- **The third outside slack is negative.**  The triple `{2,3,4}` dominates the
foil strictly. -/
theorem ledgerFoil_slack_five :
    pairRefusalSlack ledgerFoil 0 1 5 = -(210889 / 1825056) := by
  rw [pairRefusalSlack, pairPivotMinor, ledgerFoil_pivot_00, ledgerFoil_pivot_11,
    ledgerFoil_pivot_01, ledgerFoil_pivot_05, ledgerFoil_pivot_15, ledgerFoil_pivot_55]
  norm_num

/-! ## 4. The separation -/

/-- The complement of the dominator. -/
theorem ledgerFoil_compl :
    (({0, 1, 2} : Finset (Fin 6))ᶜ) = ({3, 4, 5} : Finset (Fin 6)) := by decide

/-- **The unweighted aggregate is blind.**  The three outside slacks of the pair
`{0,1}` sum to a POSITIVE number, so `Gtz.corner_pairRefusal_bound` holds at the
foil and refutes nothing. -/
theorem ledgerFoil_aggregate_nonneg :
    (0 : ℝ) < ∑ d ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ, pairRefusalSlack ledgerFoil 0 1 d := by
  rw [ledgerFoil_compl,
    show ({3, 4, 5} : Finset (Fin 6)) = insert 3 (insert 4 {5}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    ledgerFoil_slack_three, ledgerFoil_slack_four, ledgerFoil_slack_five]
  norm_num

/-- **The co-weighted aggregate is not blind.**  The same three slacks, weighted
by the co-weights, sum to a NEGATIVE number, so
`Gtz.ghostDeficitForm_ge_coweight_slack` refutes the tie at the same pair. -/
theorem ledgerFoil_coweight_neg :
    ∑ d ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ,
        (1 - ledgerFoil.weight d) * pairRefusalSlack ledgerFoil 0 1 d < 0 := by
  rw [ledgerFoil_compl,
    show ({3, 4, 5} : Finset (Fin 6)) = insert 3 (insert 4 {5}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    ledgerFoil_slack_three, ledgerFoil_slack_four, ledgerFoil_slack_five]
  norm_num [ledgerFoil, weightFn]

/-- **The foil is not a tie.**  The third outside slack is negative, so the
triple `{2,3,4}` dominates strictly. -/
theorem ledgerFoil_not_isTie : ¬ IsTie ledgerFoil := by
  intro htie
  have h := pairRefusalSlack_nonneg_of_isTie ledgerFoil htie
    (by decide : (0 : Fin 6) ≠ 1) (by decide : (0 : Fin 6) ≠ 5)
    (by decide : (1 : Fin 6) ≠ 5) ledgerFoil_admissible.1 ledgerFoil_admissible.2
  rw [ledgerFoil_slack_five] at h
  norm_num at h

/-- **The Schur–Horn cap on a single inside pair is false.**  At a corank-two
corner the three outside refusal slacks of one admissible pair can sum to a
positive number while their co-weighted sum is negative, so the co-weighted
weighting is STRICTLY sharper than the unweighted one — even for one pair, with
the corner scalars fixed.  The outside frame is not free: the co-weighted
Parseval identity pins it. -/
theorem exists_coweight_beats_aggregate :
    ∃ (D : WeightedDesign 6 3) (C : Finset (Fin 6)) (lam : ℝ) (u : Fin 3 → ℝ) (f h : Fin 6),
      C.card = 3 ∧ 0 < lam ∧ subsetSum D C - 1 = lam • atomMatrix u
      ∧ f ∈ C ∧ h ∈ C ∧ f ≠ h
      ∧ sixSetPivot D f f < 1 ∧ 0 < pairPivotMinor D f h
      ∧ 0 < ∑ d ∈ Cᶜ, pairRefusalSlack D f h d
      ∧ ∑ d ∈ Cᶜ, (1 - D.weight d) * pairRefusalSlack D f h d < 0 :=
  ⟨ledgerFoil, {0, 1, 2}, 3, axisVec, 0, 1, by decide, by norm_num, ledgerFoil_corner,
    by decide, by decide, by decide, ledgerFoil_admissible.1, ledgerFoil_admissible.2,
    ledgerFoil_aggregate_nonneg, ledgerFoil_coweight_neg⟩

end Gtz
