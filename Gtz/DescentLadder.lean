/-
# Theorem Q: the descent ladder

The trace identity read at the full base set `Q = [m]`, where there are no
outsiders. The co-Parseval operator `W = S_[m] − 1 = Σ_c (1−t_c) g_c g_cᵀ` is
positive definite for every design of at least two atoms, and the identity
collapses to

  `Σ_c (1 − t_c) b_c = k`,   `b_c = g_cᵀ W⁻¹ g_c`,   `Σ_c (1 − t_c) = m − 1`.

Two consequences make it a descent step rather than a curiosity. The weights
`(1 − t_c)` sum to `m − 1`, so the pivots average to `k/(m−1)` and the smallest
is at most that — at `(6,3)` this is the sharp `3/5` the octahedron attains.
And counting the atoms whose pivot exceeds one gives at least `m − k` atoms
that can be dropped, which is what feeds the ladder down to the last rung.

The identity is field-blind by construction — it fires over the complex numbers
too, which is exactly why it locates all the real content in the final rung.
-/
import Mathlib
import Gtz.Basic
import Gtz.TraceIdentity
import Gtz.Naimark

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ### The full excess -/

/-- The excess of the full atom set is the co-Parseval operator: subtracting
Parseval from the unweighted sum reweights each atom by `1 − t_c`. -/
theorem fullExcess_eq_coParseval (D : WeightedDesign m k) :
    subsetSum D Finset.univ - 1
      = ∑ c, (1 - D.weight c) • atomMatrix (D.atom c) := by
  have hterm : ∀ c, (1 - D.weight c) • atomMatrix (D.atom c)
      = atomMatrix (D.atom c) - D.weight c • atomMatrix (D.atom c) := fun c => by
    rw [sub_smul, one_smul]
  simp only [hterm]
  rw [Finset.sum_sub_distrib, D.isParseval, subsetSum]

/-- The full excess is positive definite whenever the design has two or more
atoms: every weight is then strictly below one, and Parseval makes the atoms
span. -/
theorem posDef_fullExcess (D : WeightedDesign m k) (hm : 2 ≤ m) :
    (subsetSum D Finset.univ - 1).PosDef := by
  rw [fullExcess_eq_coParseval]
  exact coParseval_posDef D hm

/-! ### Theorem Q -/

/-- **Theorem Q, the descent identity**: at the full base set the trace identity
has no outsider term, so the co-weighted pivots sum exactly to the rank. -/
theorem descent_identity (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ∑ c, (1 - D.weight c) * pivot D Finset.univ c = (k : ℝ) := by
  have hidentity := trace_identity D Finset.univ (posDef_fullExcess D hm)
  simpa using hidentity

/-- The co-weights sum to `m − 1`. -/
theorem sum_one_sub_weight (D : WeightedDesign m k) :
    ∑ c, (1 - D.weight c) = (m : ℝ) - 1 := by
  rw [Finset.sum_sub_distrib, D.weight_sum_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Every co-weight is strictly between zero and one. -/
theorem one_sub_weight_mem (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    0 < 1 - D.weight c ∧ 1 - D.weight c < 1 := by
  refine ⟨by linarith [weight_lt_one D hm c], by linarith [D.weight_pos c]⟩

/-- Pivots against a positive definite base are nonnegative — the inverse of a
positive definite matrix is positive definite, and the pivot is its quadratic
form at the atom vector. -/
theorem pivot_nonneg (D : WeightedDesign m k) (Q : Finset (Fin m))
    (hQ : (subsetSum D Q - 1).PosDef) (c : Fin m) :
    0 ≤ pivot D Q c := by
  rw [pivot_eq_dot]
  have hinv := hQ.inv
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hinv.posSemidef).2
    (D.atom c)
  rwa [star_trivial] at hnonneg

/-! ### The two ladder consequences -/

/-- **The smallest pivot is at most `k/(m−1)`** — the average against the
co-weights. At `(6,3)` this is `3/5`, attained exactly at the octahedron. -/
theorem exists_pivot_le_average (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ∃ c, pivot D Finset.univ c ≤ (k : ℝ) / ((m : ℝ) - 1) := by
  by_contra hcontra
  push_neg at hcontra
  have hcoweightPos : ∀ c ∈ Finset.univ, (0 : ℝ) < 1 - D.weight c := fun c _ =>
    (one_sub_weight_mem D hm c).1
  have hstrict : ∑ c, (1 - D.weight c) * ((k : ℝ) / ((m : ℝ) - 1))
      < ∑ c, (1 - D.weight c) * pivot D Finset.univ c := by
    refine Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      fun c hc => ?_
    exact mul_lt_mul_of_pos_left (hcontra c) (hcoweightPos c hc)
  rw [← Finset.sum_mul, sum_one_sub_weight, descent_identity D hm] at hstrict
  have hden : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  rw [mul_div_assoc'] at hstrict
  rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hden), mul_one] at hstrict
  exact lt_irrefl _ hstrict

/-- **At least `m − k` atoms are droppable**: counting the pivots that do not
exceed one. Each such atom's erasure dominates by the rank-one Schur step, so
this is the supply of descent moves the ladder consumes. -/
theorem card_pivot_le_one_ge (D : WeightedDesign m k) (hm : 2 ≤ m) :
    m ≤ k + (Finset.univ.filter
      (fun c => pivot D Finset.univ c ≤ 1)).card := by
  classical
  set lightSet := Finset.univ.filter
    (fun c => pivot D Finset.univ c ≤ 1) with hlightSet
  have hposDef := posDef_fullExcess D hm
  have hcoweightPos : ∀ c, (0 : ℝ) < 1 - D.weight c := fun c =>
    (one_sub_weight_mem D hm c).1
  -- the excess identity: Σ (1−t)(b−1) = k − (m−1)
  have hexcess : ∑ c, (1 - D.weight c) * (pivot D Finset.univ c - 1)
      = (k : ℝ) - ((m : ℝ) - 1) := by
    have hsplit : ∀ c, (1 - D.weight c) * (pivot D Finset.univ c - 1)
        = (1 - D.weight c) * pivot D Finset.univ c - (1 - D.weight c) :=
      fun c => by ring
    simp only [hsplit]
    rw [Finset.sum_sub_distrib, descent_identity D hm, sum_one_sub_weight]
  -- heavy atoms contribute nonnegatively, light atoms at worst −(1−t) > −1
  have hheavy : (0 : ℝ) ≤ ∑ c ∈ lightSetᶜ,
      (1 - D.weight c) * (pivot D Finset.univ c - 1) := by
    refine Finset.sum_nonneg fun c hc => ?_
    have hgt : 1 < pivot D Finset.univ c := by
      by_contra hle
      push_neg at hle
      have hmem : c ∈ lightSet := by
        rw [hlightSet]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hle⟩
      exact (Finset.mem_compl.mp hc) hmem
    exact mul_nonneg (hcoweightPos c).le (by linarith)
  have hlight : -((lightSet.card : ℝ)) ≤ ∑ c ∈ lightSet,
      (1 - D.weight c) * (pivot D Finset.univ c - 1) := by
    have hbound : ∀ c ∈ lightSet,
        (-1 : ℝ) ≤ (1 - D.weight c) * (pivot D Finset.univ c - 1) := by
      intro c _
      have hp := pivot_nonneg D Finset.univ hposDef c
      nlinarith [hcoweightPos c, (one_sub_weight_mem D hm c).2, hp]
    calc -((lightSet.card : ℝ)) = ∑ _c ∈ lightSet, (-1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum hbound
  have hsplitSum : ∑ c, (1 - D.weight c) * (pivot D Finset.univ c - 1)
      = (∑ c ∈ lightSet, (1 - D.weight c) * (pivot D Finset.univ c - 1))
        + ∑ c ∈ lightSetᶜ, (1 - D.weight c) * (pivot D Finset.univ c - 1) :=
    (Finset.sum_add_sum_compl lightSet _).symm
  -- the sharp integer bound needs the strict co-weight bound, so split on
  -- whether any light atom exists at all
  rcases Finset.eq_empty_or_nonempty lightSet with hempty | hne
  · -- no light atoms: every pivot exceeds one, forcing m ≤ k
    have hallHeavy : ∀ c, 1 < pivot D Finset.univ c := by
      intro c
      by_contra hle
      push_neg at hle
      have hmem : c ∈ lightSet := by
        rw [hlightSet]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hle⟩
      rw [hempty] at hmem
      exact absurd hmem (Finset.notMem_empty c)
    have hpos : (0 : ℝ) < ∑ c, (1 - D.weight c) * (pivot D Finset.univ c - 1) := by
      refine Finset.sum_pos (fun c _ => ?_) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      exact mul_pos (hcoweightPos c) (by linarith [hallHeavy c])
    rw [hexcess] at hpos
    have hreal : (m : ℝ) < (k : ℝ) + 1 := by linarith
    have hmk : m < k + 1 := by exact_mod_cast hreal
    omega
  · -- some light atom: the co-weight bound is strict, killing the extra one
    have hstrictLight : -((lightSet.card : ℝ)) < ∑ c ∈ lightSet,
        (1 - D.weight c) * (pivot D Finset.univ c - 1) := by
      have hbound : ∀ c ∈ lightSet,
          (-1 : ℝ) < (1 - D.weight c) * (pivot D Finset.univ c - 1) := by
        intro c _
        have hp := pivot_nonneg D Finset.univ hposDef c
        nlinarith [hcoweightPos c, (one_sub_weight_mem D hm c).2, hp]
      calc -((lightSet.card : ℝ)) = ∑ _c ∈ lightSet, (-1 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ < _ := Finset.sum_lt_sum_of_nonempty hne hbound
    have : (m : ℝ) < (k : ℝ) + (lightSet.card : ℝ) + 1 := by
      linarith [hexcess, hsplitSum, hstrictLight, hheavy]
    have hnat : m < k + lightSet.card + 1 := by exact_mod_cast this
    omega

end Gtz
