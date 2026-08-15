/-
# The inverse-trace escape

`Gtz.trace_identity` multiplies the Parseval split of `S_Q - 1` by its own
inverse and takes traces.  That prices the insiders' WEIGHTED pivot sum against
the outsiders'.  It never reads the inverse alone, and every consequence of it
carries a weight.

Drop Parseval.  Multiply `S_Q = (S_Q - 1) + 1` by `(S_Q - 1)⁻¹` and take traces:

  `∑ d ∈ Q, pivot D Q d = k + trace ((S_Q - 1)⁻¹)`     (the inverse-trace law)

The right side carries no weight and no outsider.  It reads the selected atoms
alone.

A stall asks every insider pivot to be at least one.  A stalled base set of
`k + j` labels therefore forces the inverse trace to be at least `j`, and the
contrapositive is a producer: below that threshold some erasure dominates.

At `Q.card = k + 1` the threshold is one and the conclusion is a dominating
subset of `k` labels, which is the shape `GtzWeighted` consumes.  The criterion
is division-free through the adjugate.
-/
import Mathlib
import Gtz.Design.TraceIdentity

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- **The inverse-trace law.**  Over a positive definite base set the unweighted
pivot sum is the rank plus the trace of the inverse gap.  No weight and no
outside label occurs on either side. -/
theorem pivot_sum_eq_rank_add_trace_inv (D : WeightedDesign m k) (Q : Finset (Fin m))
    (hQ : (subsetSum D Q - 1).PosDef) :
    ∑ d ∈ Q, pivot D Q d = k + Matrix.trace ((subsetSum D Q - 1)⁻¹) := by
  have hdet : IsUnit (subsetSum D Q - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hQ.det_pos)
  have hsum : ∑ d ∈ Q, pivot D Q d
      = Matrix.trace ((subsetSum D Q - 1)⁻¹ * subsetSum D Q) := by
    simp only [pivot, subsetSum, Matrix.mul_sum, Matrix.trace_sum]
  have hkey : Matrix.trace ((subsetSum D Q - 1)⁻¹ * subsetSum D Q)
      = k + Matrix.trace ((subsetSum D Q - 1)⁻¹) := by
    have hfactor : (subsetSum D Q - 1)⁻¹ * subsetSum D Q
        = (subsetSum D Q - 1)⁻¹ * (subsetSum D Q - 1) + (subsetSum D Q - 1)⁻¹ := by
      rw [Matrix.mul_sub, Matrix.mul_one]
      abel
    rw [hfactor, Matrix.trace_add, Matrix.nonsing_inv_mul _ hdet, Matrix.trace_one,
      Fintype.card_fin]
  rw [hsum, hkey]

/-- **The stall price on the inverse trace.**  A base set every label of which
carries pivot at least one prices its inverse trace by the excess of its
cardinality over the rank.  No weight enters. -/
theorem card_sub_rank_le_trace_inv_of_stall (D : WeightedDesign m k) (Q : Finset (Fin m))
    (hQ : (subsetSum D Q - 1).PosDef) (hstall : ∀ d ∈ Q, 1 ≤ pivot D Q d) :
    ((Q.card : ℝ) - k) ≤ Matrix.trace ((subsetSum D Q - 1)⁻¹) := by
  have hlaw := pivot_sum_eq_rank_add_trace_inv D Q hQ
  have hge : (Q.card : ℝ) ≤ ∑ d ∈ Q, pivot D Q d := by
    calc (Q.card : ℝ) = ∑ _d ∈ Q, (1 : ℝ) := by simp
      _ ≤ ∑ d ∈ Q, pivot D Q d := Finset.sum_le_sum hstall
  linarith

/-- **The escape.**  An inverse trace below the excess threshold hands back an
erasure that dominates. -/
theorem exists_erase_dominates_of_trace_inv_lt (D : WeightedDesign m k)
    (Q : Finset (Fin m)) (hQ : (subsetSum D Q - 1).PosDef)
    (hlt : Matrix.trace ((subsetSum D Q - 1)⁻¹) < (Q.card : ℝ) - k) :
    ∃ d ∈ Q, Dominates D (Q.erase d) := by
  by_contra hno
  push Not at hno
  have hstall : ∀ d ∈ Q, 1 ≤ pivot D Q d := by
    intro d hd
    by_contra hlt1
    push Not at hlt1
    exact hno d hd ((erase_dominates_iff_pivot_le_one D Q hQ hd).mpr hlt1.le)
  linarith [card_sub_rank_le_trace_inv_of_stall D Q hQ hstall]

/-- The inverse trace read through the adjugate.  This clears the division and
turns the escape threshold into a polynomial comparison. -/
theorem trace_inv_lt_iff_adjugateTrace_lt (G : Matrix (Fin k) (Fin k) ℝ)
    (hdet : 0 < G.det) (c : ℝ) :
    Matrix.trace G⁻¹ < c ↔ Matrix.trace G.adjugate < c * G.det := by
  rw [Matrix.inv_def, Matrix.trace_smul, Ring.inverse_eq_inv', smul_eq_mul,
    inv_mul_eq_div, div_lt_iff₀ hdet]

/-- **The escape, division-free.**  The hypothesis is one polynomial inequality
in the selected atoms: the adjugate trace of the gap against its determinant,
scaled by the excess of the cardinality over the rank. -/
theorem exists_erase_dominates_of_adjugateTrace_lt (D : WeightedDesign m k)
    (Q : Finset (Fin m)) (hQ : (subsetSum D Q - 1).PosDef)
    (hadj : Matrix.trace (subsetSum D Q - 1).adjugate
      < ((Q.card : ℝ) - k) * (subsetSum D Q - 1).det) :
    ∃ d ∈ Q, Dominates D (Q.erase d) :=
  exists_erase_dominates_of_trace_inv_lt D Q hQ
    ((trace_inv_lt_iff_adjugateTrace_lt _ hQ.det_pos _).mpr hadj)

/-- At one label above the rank the threshold is one, and the erasure has
exactly `k` labels. -/
theorem exists_dominates_card_rank_of_adjugateTrace_lt_det (D : WeightedDesign m k)
    (Q : Finset (Fin m)) (hcard : Q.card = k + 1)
    (hQ : (subsetSum D Q - 1).PosDef)
    (hadj : Matrix.trace (subsetSum D Q - 1).adjugate < (subsetSum D Q - 1).det) :
    ∃ T : Finset (Fin m), T.card = k ∧ Dominates D T := by
  have hthresh : Matrix.trace (subsetSum D Q - 1).adjugate
      < ((Q.card : ℝ) - k) * (subsetSum D Q - 1).det := by
    rw [hcard]
    push_cast
    simpa using hadj
  obtain ⟨d, hd, hdom⟩ := exists_erase_dominates_of_adjugateTrace_lt D Q hQ hthresh
  refine ⟨Q.erase d, ?_, hdom⟩
  rw [Finset.card_erase_of_mem hd, hcard]
  omega

/-- **The rank-three producer.**  A positive definite four-label selection whose
gap has adjugate trace below its determinant hands back a dominating triple.
This is the shape `GtzWeighted 6 3` consumes, and it reads only the four
selected atoms. -/
theorem exists_dominates_cardThree_of_adjugateTrace_lt_det (D : WeightedDesign 6 3)
    (Q : Finset (Fin 6)) (hcard : Q.card = 4)
    (hQ : (subsetSum D Q - 1).PosDef)
    (hadj : Matrix.trace (subsetSum D Q - 1).adjugate < (subsetSum D Q - 1).det) :
    ∃ T : Finset (Fin 6), T.card = 3 ∧ Dominates D T :=
  exists_dominates_card_rank_of_adjugateTrace_lt_det D Q hcard hQ hadj

/-- **The stalled four-set is pinned.**  Every card-four stall at rank three
carries inverse trace at least one, equivalently adjugate trace at least the
determinant.  This is the exact complement of the producer above: the two
together are a dichotomy on one polynomial. -/
theorem det_le_adjugateTrace_of_cardFour_stall (D : WeightedDesign 6 3)
    (Q : Finset (Fin 6)) (hcard : Q.card = 4)
    (hQ : (subsetSum D Q - 1).PosDef) (hstall : ∀ d ∈ Q, 1 ≤ pivot D Q d) :
    (subsetSum D Q - 1).det ≤ Matrix.trace (subsetSum D Q - 1).adjugate := by
  by_contra hlt
  push Not at hlt
  obtain ⟨T, hTcard, hTdom⟩ :=
    exists_dominates_cardThree_of_adjugateTrace_lt_det D Q hcard hQ hlt
  have hstall' := card_sub_rank_le_trace_inv_of_stall D Q hQ hstall
  rw [hcard] at hstall'
  have hone : (1 : ℝ) ≤ Matrix.trace ((subsetSum D Q - 1)⁻¹) := by
    push_cast at hstall'
    linarith
  have hlt' : Matrix.trace ((subsetSum D Q - 1)⁻¹) < 1 :=
    (trace_inv_lt_iff_adjugateTrace_lt _ hQ.det_pos 1).mpr (by simpa using hlt)
  linarith

end Gtz
