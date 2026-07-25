import Mathlib
import Gtz.Reduction.BranchTwoRational

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Adversarial audit A — provable hypothesis redundancy in `BranchTwoRational`

Three of the file's hypotheses are derivable from the others.  Each theorem
below restates a landed declaration with the redundant hypothesis DELETED and
proves it, so the deletion is kernel-checked rather than asserted.
-/

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ### 1. `hbasisDet` is redundant wherever a one-negative-pivot congruence appears

`det(basis)^2 * det(form) = prod d`, and a one-negative-pivot diagonal has
nonzero product, so `det basis` cannot vanish.  The hypothesis
`IsUnit basis.det` carried by `signatureWitness_of_oneNegativePivot`,
`det_neg_of_oneNegativePivot`, `dominates_of_capCongruence`,
`ratDominates_of_capCongruence` and
`ratCapCertificate_exists_dominating` is therefore free. -/
theorem isUnit_basisDet_of_oneNegativePivot
    {form basis : Matrix (Fin k) (Fin k) ℝ} {diagVec : Fin k → ℝ}
    {negIndex : Fin k}
    (hCongr : basisᵀ * form * basis = Matrix.diagonal diagVec)
    (hNegPivot : diagVec negIndex < 0)
    (hPosPivots : ∀ i, i ≠ negIndex → 0 < diagVec i) :
    IsUnit basis.det := by
  have hdet := congrArg Matrix.det hCongr
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal] at hdet
  have hprodNeg : ∏ i, diagVec i < 0 := by
    rw [← Finset.mul_prod_erase Finset.univ diagVec (Finset.mem_univ negIndex)]
    exact mul_neg_of_neg_of_pos hNegPivot
      (Finset.prod_pos fun i hi => hPosPivots i (Finset.mem_erase.mp hi).1)
  rw [isUnit_iff_ne_zero]
  intro hzero
  rw [hzero] at hdet
  simp only [zero_mul, mul_zero] at hdet
  exact absurd hdet.symm (ne_of_lt hprodNeg)

/-- `signatureWitness_of_oneNegativePivot` with `hbasisDet` DELETED. -/
theorem signatureWitness_of_oneNegativePivot_noUnit
    {form basis : Matrix (Fin k) (Fin k) ℝ} {diagVec : Fin k → ℝ}
    {negIndex : Fin k}
    (hCongr : basisᵀ * form * basis = Matrix.diagonal diagVec)
    (hNegPivot : diagVec negIndex < 0)
    (hPosPivots : ∀ i, i ≠ negIndex → 0 < diagVec i) :
    (negativeDirection basis negIndex)
        ⬝ᵥ (form *ᵥ (negativeDirection basis negIndex)) < 0
      ∧ ∀ probe : Fin k → ℝ,
          probe ⬝ᵥ (form *ᵥ (negativeDirection basis negIndex)) = 0
            → 0 ≤ probe ⬝ᵥ (form *ᵥ probe) :=
  signatureWitness_of_oneNegativePivot
    (isUnit_basisDet_of_oneNegativePivot hCongr hNegPivot hPosPivots)
    hCongr hNegPivot hPosPivots

/-- `det_neg_of_oneNegativePivot` with `hbasisDet` DELETED. -/
theorem det_neg_of_oneNegativePivot_noUnit
    {form basis : Matrix (Fin k) (Fin k) ℝ} {diagVec : Fin k → ℝ}
    {negIndex : Fin k}
    (hCongr : basisᵀ * form * basis = Matrix.diagonal diagVec)
    (hNegPivot : diagVec negIndex < 0)
    (hPosPivots : ∀ i, i ≠ negIndex → 0 < diagVec i) :
    form.det < 0 :=
  det_neg_of_oneNegativePivot
    (isUnit_basisDet_of_oneNegativePivot hCongr hNegPivot hPosPivots)
    hCongr hNegPivot hPosPivots

/-! ### 2. `hfresh` is redundant in every cap consumer

If `extra` already lay in the gate then `insert extra gate = gate`, so the cap
determinant hypothesis `0 <= det (S_{gate + extra} - 1)` would contradict the
gate's own `det < 0`.  Freshness is a CONSEQUENCE of the two determinant signs,
not an extra assumption. -/
theorem notMem_of_capDet (D : WeightedDesign m k) (gate : Finset (Fin m))
    (extra : Fin m)
    (hgateDetNeg : (subsetSum D gate - 1).det < 0)
    (hCapDet : 0 ≤ (subsetSum D (insert extra gate) - 1).det) :
    extra ∉ gate := by
  intro hmember
  rw [Finset.insert_eq_self.mpr hmember] at hCapDet
  linarith

/-- `dominates_of_capWitness` with `hfresh` DELETED. -/
theorem dominates_of_capWitness_noFresh (D : WeightedDesign m k)
    (gate : Finset (Fin m)) (extra : Fin m)
    (negDirection : Fin k → ℝ)
    (hnegative : negDirection ⬝ᵥ ((subsetSum D gate - 1) *ᵥ negDirection) < 0)
    (hcomplement : ∀ probe : Fin k → ℝ,
      probe ⬝ᵥ ((subsetSum D gate - 1) *ᵥ negDirection) = 0
        → 0 ≤ probe ⬝ᵥ ((subsetSum D gate - 1) *ᵥ probe))
    (hgateDetNeg : (subsetSum D gate - 1).det < 0)
    (hCapDet : 0 ≤ (subsetSum D (insert extra gate) - 1).det) :
    Dominates D (insert extra gate) :=
  dominates_of_capWitness D gate extra
    (notMem_of_capDet D gate extra hgateDetNeg hCapDet)
    negDirection hnegative hcomplement hgateDetNeg hCapDet

/-- `dominates_of_capCongruence` with BOTH `hbasisDet` and `hfresh` DELETED. -/
theorem dominates_of_capCongruence_minimal (D : WeightedDesign m k)
    (gate : Finset (Fin m)) (extra : Fin m)
    (basis : Matrix (Fin k) (Fin k) ℝ) (diagVec : Fin k → ℝ) (negIndex : Fin k)
    (hCongr : basisᵀ * (subsetSum D gate - 1) * basis = Matrix.diagonal diagVec)
    (hNegPivot : diagVec negIndex < 0)
    (hPosPivots : ∀ i, i ≠ negIndex → 0 < diagVec i)
    (hCapDet : 0 ≤ (subsetSum D (insert extra gate) - 1).det) :
    Dominates D (insert extra gate) := by
  have hbasisDet := isUnit_basisDet_of_oneNegativePivot hCongr hNegPivot hPosPivots
  exact dominates_of_capCongruence D gate extra
    (notMem_of_capDet D gate extra
      (det_neg_of_oneNegativePivot hbasisDet hCongr hNegPivot hPosPivots) hCapDet)
    basis diagVec negIndex hbasisDet hCongr hNegPivot hPosPivots hCapDet

/-! ### 3. At rank three BOTH set-theoretic side conditions are redundant

`hdistinct` follows from the two scalar hypotheses alone: with one atom used
twice the pair test reads `1 - 2*leverage > 0` while the trace test reads
`leverage > 1`.  `hfresh` then follows from `hgateDet` and `hCapDet` as above. -/
theorem distinct_of_pairGateScalars (D : WeightedDesign m 3)
    (firstGate secondGate : Fin m)
    (htrace : 0 < (leverageOf (D.atom firstGate) - 1)
                    + (leverageOf (D.atom secondGate) - 1))
    (hgateDet : 0 < (leverageOf (D.atom firstGate) - 1)
                      * (leverageOf (D.atom secondGate) - 1)
                    - (D.atom firstGate ⬝ᵥ D.atom secondGate) ^ 2) :
    firstGate ≠ secondGate := by
  intro hsame
  rw [hsame] at htrace hgateDet
  rw [dotProduct_self_eq_sum_sq, ← leverageOf] at hgateDet
  nlinarith [htrace, hgateDet]

/-- `dominates_of_pairGate` with BOTH `hdistinct` and `hfresh` DELETED:
the three polynomial inequalities the report advertises really are the whole
hypothesis set. -/
theorem dominates_of_pairGate_minimal (D : WeightedDesign m 3)
    (firstGate secondGate extra : Fin m)
    (htrace : 0 < (leverageOf (D.atom firstGate) - 1)
                    + (leverageOf (D.atom secondGate) - 1))
    (hgateDet : 0 < (leverageOf (D.atom firstGate) - 1)
                      * (leverageOf (D.atom secondGate) - 1)
                    - (D.atom firstGate ⬝ᵥ D.atom secondGate) ^ 2)
    (hCapDet : 0 ≤ (subsetSum D (insert extra {firstGate, secondGate}) - 1).det) :
    Dominates D (insert extra {firstGate, secondGate}) := by
  have hdistinct := distinct_of_pairGateScalars D firstGate secondGate htrace hgateDet
  have hgateShift : subsetSum D {firstGate, secondGate} - 1
      = pairGramShift (D.atom firstGate) (D.atom secondGate) := by
    rw [subsetSum, Finset.sum_pair hdistinct, pairGramShift]
  have hgateDetNeg : (subsetSum D {firstGate, secondGate} - 1).det < 0 := by
    rw [hgateShift, pairGramShift_det]
    rw [dotProduct_self_eq_sum_sq, dotProduct_self_eq_sum_sq, ← leverageOf,
      ← leverageOf]
    linarith
  exact dominates_of_pairGate D firstGate secondGate extra hdistinct
    (notMem_of_capDet D {firstGate, secondGate} extra hgateDetNeg hCapDet)
    htrace hgateDet hCapDet


/-! ### 4. The rational twins: the same two hypotheses are free over the rationals -/

/-- `hbasisDet` is free over `Q` too. -/
theorem ratIsUnit_basisDet_of_oneNegativePivot
    {form basisRat : Matrix (Fin k) (Fin k) ℚ} {diagRat : Fin k → ℚ}
    {negIndex : Fin k}
    (hCongr : basisRatᵀ * form * basisRat = Matrix.diagonal diagRat)
    (hNegPivot : diagRat negIndex < 0)
    (hPosPivots : ∀ i, i ≠ negIndex → 0 < diagRat i) :
    basisRat.det ≠ 0 ∧ form.det < 0 := by
  have hdet := congrArg Matrix.det hCongr
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal] at hdet
  have hprodNeg : ∏ i, diagRat i < 0 := by
    rw [← Finset.mul_prod_erase Finset.univ diagRat (Finset.mem_univ negIndex)]
    exact mul_neg_of_neg_of_pos hNegPivot
      (Finset.prod_pos fun i hi => hPosPivots i (Finset.mem_erase.mp hi).1)
  have hbasisNe : basisRat.det ≠ 0 := by
    intro hzero
    rw [hzero] at hdet
    simp only [zero_mul, mul_zero] at hdet
    exact absurd hdet.symm (ne_of_lt hprodNeg)
  refine ⟨hbasisNe, ?_⟩
  nlinarith [hdet, hprodNeg, mul_self_pos.mpr hbasisNe]

/-- `ratDominates_of_capCongruence` with BOTH `hbasisDet` and `hfresh` DELETED. -/
theorem ratDominates_of_capCongruence_minimal (R : RatDesign m k)
    (gate : Finset (Fin m)) (extra : Fin m)
    (basisRat : Matrix (Fin k) (Fin k) ℚ) (diagRat : Fin k → ℚ)
    (negIndex : Fin k)
    (hCongr : basisRatᵀ * ratGram R gate * basisRat = Matrix.diagonal diagRat)
    (hNegPivot : diagRat negIndex < 0)
    (hPosPivots : ∀ i, i ≠ negIndex → 0 < diagRat i)
    (hCapDet : 0 ≤ (ratGram R (insert extra gate)).det) :
    Dominates R.toReal (insert extra gate) := by
  obtain ⟨hbasisNe, hgateDetNeg⟩ :=
    ratIsUnit_basisDet_of_oneNegativePivot hCongr hNegPivot hPosPivots
  have hfresh : extra ∉ gate := by
    intro hmember
    rw [Finset.insert_eq_self.mpr hmember] at hCapDet
    linarith
  exact ratDominates_of_capCongruence R gate extra hfresh basisRat diagRat negIndex
    hbasisNe hCongr hNegPivot hPosPivots hCapDet

/-- `ratDominates_of_pairGate` with BOTH `hdistinct` and `hfresh` DELETED: the
report's "three exact rational comparisons" is then literally the hypothesis set. -/
theorem ratDominates_of_pairGate_minimal (R : RatDesign m 3)
    (firstGate secondGate extra : Fin m)
    (htrace : 0 < ((∑ i, R.atom firstGate i ^ 2) - 1)
                    + ((∑ i, R.atom secondGate i ^ 2) - 1))
    (hgateDet : 0 < ((∑ i, R.atom firstGate i ^ 2) - 1)
                      * ((∑ i, R.atom secondGate i ^ 2) - 1)
                    - (R.atom firstGate ⬝ᵥ R.atom secondGate) ^ 2)
    (hCapDet : 0 ≤ (ratGram R (insert extra {firstGate, secondGate})).det) :
    Dominates R.toReal (insert extra {firstGate, secondGate}) := by
  refine dominates_of_pairGate_minimal R.toReal firstGate secondGate extra ?_ ?_ ?_
  · rw [R.leverage_cast firstGate, R.leverage_cast secondGate]
    exact_mod_cast htrace
  · rw [R.leverage_cast firstGate, R.leverage_cast secondGate,
      R.dot_cast firstGate secondGate]
    exact_mod_cast hgateDet
  · rw [R.gram_cast (insert extra {firstGate, secondGate}), det_cast]
    exact_mod_cast hCapDet


end Gtz
