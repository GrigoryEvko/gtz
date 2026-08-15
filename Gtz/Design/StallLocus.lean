/-
# The division-free stall locus

`Gtz.pivot_sum_eq_rank_add_trace_inv` reads the inverse gap alone and prices a
stalled base set by `trace ((S_Q - 1)⁻¹)`.  That is the TRACE of something
exact, and this file lands the vector form it summarises.

Clear the pivot of its division.  With `G := S_Q - 1` and `G⁻¹ = adj G / det G`,

  `pivot D Q c * det G = atom c ⬝ᵥ (adj G *ᵥ atom c) =: adjugateReading D Q c`

so every pivot comparison becomes a polynomial comparison in the selected atoms:

  `Dominates D (Q.erase d) ↔ adjugateReading D Q d ≤ det G`

and a base set is stalled exactly when every one of its adjugate readings is at
least the determinant.  **No inverse, no division, no eigenvalue.**

The readings satisfy one identity, which needs no positivity at all:

  `∑ d ∈ Q, adjugateReading D Q d = k * det G + trace (adj G)`

Summing the stall conditions against it returns the landed inverse-trace price
in division-free form, at every size and rank.  So the trace criterion is the
SUMMED WEAKENING of the per-label criterion, and a stall satisfies the negation
of the trace criterion by construction — the trace criterion can never fire at
a stall, and this file proves that rather than measuring it.

Finally the whole locus is Gram data: by Sylvester's determinant identity the
gap determinant is the determinant of `Γ - 1` on the selected labels, up to
sign, where `Γ` is their Gram matrix.
-/
import Mathlib
import Gtz.Design.InverseTraceEscape

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- **The adjugate reading.**  The gap's adjugate read at a label's atom.  It is
the pivot cleared of its division, and it is a polynomial in the selected
atoms. -/
noncomputable def adjugateReading (D : WeightedDesign m k) (Q : Finset (Fin m))
    (c : Fin m) : ℝ :=
  (D.atom c) ⬝ᵥ ((subsetSum D Q - 1).adjugate *ᵥ (D.atom c))

/-- Any matrix traced against the subset sum spreads into the quadratic forms of
the selected atoms.  This is the shared step behind both the pivot sum and the
adjugate-reading sum. -/
theorem trace_mul_subsetSum_eq_sum_quadForm (D : WeightedDesign m k)
    (Q : Finset (Fin m)) (N : Matrix (Fin k) (Fin k) ℝ) :
    Matrix.trace (N * subsetSum D Q) = ∑ d ∈ Q, (D.atom d) ⬝ᵥ (N *ᵥ (D.atom d)) := by
  rw [subsetSum, Matrix.mul_sum, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun d _ => by
    rw [atomMatrix, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- The adjugate reading is the pivot scaled by the determinant.  This is the
whole content of the division clearance. -/
theorem pivot_mul_det_eq_adjugateReading (D : WeightedDesign m k) (Q : Finset (Fin m))
    (hQ : (subsetSum D Q - 1).PosDef) (c : Fin m) :
    pivot D Q c * (subsetSum D Q - 1).det = adjugateReading D Q c := by
  have hne : (subsetSum D Q - 1).det ≠ 0 := ne_of_gt hQ.det_pos
  rw [pivot_eq_dot, adjugateReading, Matrix.inv_def, Ring.inverse_eq_inv',
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  field_simp

/-- A pivot clears one exactly when its adjugate reading clears the
determinant. -/
theorem one_le_pivot_iff_det_le_adjugateReading (D : WeightedDesign m k)
    (Q : Finset (Fin m)) (hQ : (subsetSum D Q - 1).PosDef) (c : Fin m) :
    1 ≤ pivot D Q c ↔ (subsetSum D Q - 1).det ≤ adjugateReading D Q c := by
  rw [← pivot_mul_det_eq_adjugateReading D Q hQ c]
  constructor
  · intro h
    nlinarith [hQ.det_pos]
  · intro h
    nlinarith [hQ.det_pos]

/-- **The division-free rank-one Schur step.**  Dropping a label dominates
exactly when that label's adjugate reading falls at or below the determinant.
The landed `erase_dominates_iff_pivot_le_one` with the inverse removed. -/
theorem erase_dominates_iff_adjugateReading_le_det (D : WeightedDesign m k)
    (Q : Finset (Fin m)) (hQ : (subsetSum D Q - 1).PosDef) {d : Fin m} (hd : d ∈ Q) :
    Dominates D (Q.erase d) ↔ adjugateReading D Q d ≤ (subsetSum D Q - 1).det := by
  rw [erase_dominates_iff_pivot_le_one D Q hQ hd,
    ← pivot_mul_det_eq_adjugateReading D Q hQ d]
  constructor
  · intro h
    nlinarith [hQ.det_pos]
  · intro h
    nlinarith [hQ.det_pos]

/-- **The reading identity.**  The adjugate readings of a base set sum to the
rank times the determinant plus the adjugate trace.  No positivity is used, so
this holds at every base set of every design. -/
theorem sum_adjugateReading_eq (D : WeightedDesign m k) (Q : Finset (Fin m)) :
    ∑ d ∈ Q, adjugateReading D Q d
      = k * (subsetSum D Q - 1).det + Matrix.trace (subsetSum D Q - 1).adjugate := by
  have hspread := trace_mul_subsetSum_eq_sum_quadForm D Q (subsetSum D Q - 1).adjugate
  have hfactor : (subsetSum D Q - 1).adjugate * subsetSum D Q
      = (subsetSum D Q - 1).adjugate * (subsetSum D Q - 1)
        + (subsetSum D Q - 1).adjugate := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [hfactor, Matrix.trace_add, Matrix.adjugate_mul, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at hspread
  simp only [adjugateReading]
  rw [← hspread]
  ring

/-- **The stall locus, division-free.**  A positive definite base set is stalled
exactly when every one of its adjugate readings clears the determinant.  Four
polynomial inequalities at a card-four base set of a rank-three design. -/
theorem stall_iff_forall_det_le_adjugateReading (D : WeightedDesign m k)
    (Q : Finset (Fin m)) (hQ : (subsetSum D Q - 1).PosDef) :
    (∀ d ∈ Q, 1 ≤ pivot D Q d)
      ↔ ∀ d ∈ Q, (subsetSum D Q - 1).det ≤ adjugateReading D Q d := by
  constructor
  · intro h d hd
    exact (one_le_pivot_iff_det_le_adjugateReading D Q hQ d).mp (h d hd)
  · intro h d hd
    exact (one_le_pivot_iff_det_le_adjugateReading D Q hQ d).mpr (h d hd)

/-- **The sharp producer.**  One reading below the determinant is enough, and it
is strictly weaker as a hypothesis than the summed trace criterion. -/
theorem exists_erase_dominates_of_adjugateReading_lt (D : WeightedDesign m k)
    (Q : Finset (Fin m)) (hQ : (subsetSum D Q - 1).PosDef) {d : Fin m} (hd : d ∈ Q)
    (hlt : adjugateReading D Q d < (subsetSum D Q - 1).det) :
    ∃ c ∈ Q, Dominates D (Q.erase c) :=
  ⟨d, hd, (erase_dominates_iff_adjugateReading_le_det D Q hQ hd).mpr hlt.le⟩

/-- **The division-free stall price, at every size and rank.**  Summing the
stall conditions against the reading identity prices the adjugate trace by the
excess cardinality times the determinant.  This generalises the landed
`det_le_adjugateTrace_of_cardFour_stall` off the `(6,3)` cell and removes its
passage through the inverse. -/
theorem card_sub_rank_mul_det_le_adjugateTrace_of_stall (D : WeightedDesign m k)
    (Q : Finset (Fin m)) (hQ : (subsetSum D Q - 1).PosDef)
    (hstall : ∀ d ∈ Q, 1 ≤ pivot D Q d) :
    ((Q.card : ℝ) - k) * (subsetSum D Q - 1).det
      ≤ Matrix.trace (subsetSum D Q - 1).adjugate := by
  have hread := (stall_iff_forall_det_le_adjugateReading D Q hQ).mp hstall
  have hsum : (Q.card : ℝ) * (subsetSum D Q - 1).det
      ≤ ∑ d ∈ Q, adjugateReading D Q d := by
    calc (Q.card : ℝ) * (subsetSum D Q - 1).det
        = ∑ _d ∈ Q, (subsetSum D Q - 1).det := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ d ∈ Q, adjugateReading D Q d := Finset.sum_le_sum hread
  rw [sum_adjugateReading_eq] at hsum
  linarith

/-- **The trace criterion is vacuous at a stall, and this is a theorem.**  A
stalled base set satisfies the negation of the summed criterion by
construction, so no measurement of that criterion against a stall residual can
ever return a positive result. -/
theorem not_adjugateTrace_lt_of_stall (D : WeightedDesign m k) (Q : Finset (Fin m))
    (hQ : (subsetSum D Q - 1).PosDef) (hstall : ∀ d ∈ Q, 1 ≤ pivot D Q d) :
    ¬ (Matrix.trace (subsetSum D Q - 1).adjugate
        < ((Q.card : ℝ) - k) * (subsetSum D Q - 1).det) :=
  not_lt.mpr (card_sub_rank_mul_det_le_adjugateTrace_of_stall D Q hQ hstall)

/-- The Gram matrix of the selected labels: the inner products of the selected
atoms, indexed by the base set itself. -/
noncomputable def selectedGram (D : WeightedDesign m k) (Q : Finset (Fin m)) :
    Matrix Q Q ℝ :=
  Matrix.of fun c d => (D.atom c.1) ⬝ᵥ (D.atom d.1)

/-- The selected atoms as a rank-by-base-set matrix. -/
noncomputable def selectedFrame (D : WeightedDesign m k) (Q : Finset (Fin m)) :
    Matrix (Fin k) Q ℝ :=
  Matrix.of fun i c => D.atom c.1 i

/-- The subset sum is the frame against its own transpose. -/
theorem selectedFrame_mul_transpose (D : WeightedDesign m k) (Q : Finset (Fin m)) :
    selectedFrame D Q * (selectedFrame D Q)ᵀ = subsetSum D Q := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selectedFrame, Matrix.of_apply,
    subsetSum, Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply]
  exact Finset.sum_attach Q fun c => D.atom c i * D.atom c j

/-- The Gram is the transpose against the frame. -/
theorem transpose_mul_selectedFrame (D : WeightedDesign m k) (Q : Finset (Fin m)) :
    (selectedFrame D Q)ᵀ * selectedFrame D Q = selectedGram D Q := by
  ext c d
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selectedFrame, selectedGram,
    Matrix.of_apply, dotProduct]

/-- **The stall locus is Gram data.**  By Sylvester's determinant identity the
gap determinant is the determinant of `Γ - 1` on the selected labels, up to the
sign carried by the two dimensions.  So the whole card-four stall condition is a
statement about the four selected atoms' inner products alone. -/
theorem det_gap_eq_sign_mul_det_gram_sub_one (D : WeightedDesign m k)
    (Q : Finset (Fin m)) :
    (subsetSum D Q - 1).det
      = (-1) ^ k * (-1) ^ Q.card * (selectedGram D Q - 1).det := by
  have hsylv : (1 - selectedFrame D Q * (selectedFrame D Q)ᵀ).det
      = (1 - (selectedFrame D Q)ᵀ * selectedFrame D Q).det :=
    Matrix.det_one_sub_mul_comm _ _
  rw [selectedFrame_mul_transpose, transpose_mul_selectedFrame] at hsylv
  have hleft : (subsetSum D Q - 1).det = (-1) ^ k * (1 - subsetSum D Q).det := by
    rw [show subsetSum D Q - 1 = -(1 - subsetSum D Q) by abel, Matrix.det_neg,
      Fintype.card_fin]
  have hright : (selectedGram D Q - 1).det
      = (-1) ^ Q.card * (1 - selectedGram D Q).det := by
    rw [show selectedGram D Q - 1 = -(1 - selectedGram D Q) by abel, Matrix.det_neg,
      Fintype.card_coe]
  rw [hleft, hright, ← hsylv]
  rw [show ((-1 : ℝ)) ^ k * ((-1 : ℝ)) ^ Q.card * (((-1 : ℝ)) ^ Q.card
      * (1 - subsetSum D Q).det) = ((-1 : ℝ)) ^ k
      * (((-1 : ℝ)) ^ Q.card * ((-1 : ℝ)) ^ Q.card) * (1 - subsetSum D Q).det by ring,
    ← pow_add, ← two_mul, pow_mul]
  norm_num

end Gtz
