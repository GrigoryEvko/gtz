import Gtz.Wave.FiveSetPairFloor
import Gtz.Reduction.DescentLadder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The half floor of the co-Parseval pivot, and what it decides at `(5,3)`

Question 7.1 of the survey asks whether every boundary `(5,3)` system has at
least four dominating triples.  A positive answer closes the whole unit-length
branch of the `(6,3)` problem, because the swap-degree cap
`Gtz.swapDegree_le_one_card_le_three` bounds that branch's family of triples by
three.  This module turns the question into ONE scalar inequality about five
vectors, and proves the half of it that is provable.

## The pivot chart

Write `W = subsetSum D univ - 1`, positive definite at every design of size at
least two (`Gtz.posDef_fullExcess`).  The campaign's landed pivot
`Gtz.pivot D univ a = g_a ⬝ᵥ (W⁻¹ *ᵥ g_a)` is the reading of an atom against
the resolvent of `W`, and two shipped laws already pin its first two moments:
`Gtz.descent_identity` gives `Σ_c (1 − t_c)·ρ_c = k`, and
`Gtz.sum_one_sub_weight` gives `Σ_c (1 − t_c) = m − 1`.

This module adds the SECOND-ORDER law the two moments were missing
(`Gtz.sum_coWeight_mul_resolvent_reading_sq`):

  **`Σ_c (1 − t_c)·(g_a ⬝ᵥ (W⁻¹ *ᵥ g_c))² = ρ_a`** ,

hypothesis-free at every size and rank.  It is Parseval read once in the
resolvent metric: the co-weighted atoms rebuild `W`, and `W` cancels one of the
two resolvents.

## The floor

At `(5,3)` the co-weights total `4` and the pivots total `3`, so the co-weighted
total of `1 − ρ_c` is exactly `1`.  A boundary system refuses every triple, and a
triple is a double downdate of `W`, so `Gtz.tie_fiveSet_pair_reading` at the full
index set says each pair obeys

  `1 ≤ ρ_a  or  (1 − ρ_a)(1 − ρ_b) ≤ (g_a ⬝ᵥ (W⁻¹ *ᵥ g_b))²` .

Feeding that disjunction into the second-order law collapses everything to
`t_a·(2ρ_a − 1) ≥ 0`, so

  **`Gtz.pivot_half_floor`: at a boundary `(5,3)` system every pivot is at least
  one half**, and the bound is attained.

## What the floor decides

`Gtz.erase_dominates_iff_pivot_le_one` reads `ρ_a ≤ 1` as "the four-set omitting
`a` dominates".  The half floor is the pair-level refinement: a pivot at exactly
one half forces every one of the four pair minors at `a` to vanish, and each
vanishing minor is a dominating triple.  So Question 7.1 reduces to the single
scalar statement `Gtz.PivotHalfAttained` below, `min_a ρ_a ≤ 1/2`, whose reverse
`min_a ρ_a ≥ 1/2` is the theorem proved here.

[MEASURED, and the harness reproduces the `(5,3)` diamond exactly — leverages
`(2, 13/4, 13/4, 13/4, 13/4)`, `8` of `10` dominating triples.  Over 40 boundary
`(5,3)` systems found as the zero set of `Σ_T max(λmin,0)²` under a weight floor
`t ≥ 0.05`: the floor `ρ_a ≥ 1/2` holds with worst slack `−1.6e−9`, the minimum
`min_a ρ_a` equals `0.4999999984` in EVERY system, and the equivalence
`ρ_a = 1/2 ⟺ all four triples avoiding a dominate` holds with zero mismatches.
The dominating-triple counts were `7` and `8`, never fewer, so Question 7.1 has
room to spare.  At the diamond `ρ = (1/2, 13/16, 13/16, 13/16, 13/16)`.]
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The resolvent is symmetric -/

/-- The full excess is invertible at any design of size at least two. -/
theorem isUnit_det_fullExcess (D : WeightedDesign m k) (hm : 2 ≤ m) :
    IsUnit (subsetSum D Finset.univ - 1).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (posDef_fullExcess D hm).isUnit

/-- The resolvent of the full excess is symmetric, so its cross readings do not
depend on the order of the two atoms. -/
theorem resolvent_reading_comm (D : WeightedDesign m k) (hm : 2 ≤ m) (a b : Fin m) :
    D.atom a ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom b)
      = D.atom b ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom a) := by
  have hsymm : ((subsetSum D Finset.univ - 1)⁻¹)ᵀ = (subsetSum D Finset.univ - 1)⁻¹ :=
    transpose_eq_of_isHermitian (posDef_fullExcess D hm).inv.1
  rw [dotProduct_mulVec, ← hsymm, Matrix.vecMul_transpose, dotProduct_comm, hsymm]

/-! ## 2. The second-order law of the pivot chart -/

/-- **THE RESOLVENT READING BUDGET.**  The co-weighted squares of an atom's
resolvent readings total that atom's own pivot.  Hypothesis-free at every size
and rank: the co-weighted atoms rebuild the full excess, and the full excess
cancels one of the two resolvents. -/
theorem sum_coWeight_mul_resolvent_reading_sq (D : WeightedDesign m k) (hm : 2 ≤ m)
    (a : Fin m) :
    ∑ c, (1 - D.weight c)
        * (D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom a)) ^ 2
      = pivot D Finset.univ a := by
  have hdet := isUnit_det_fullExcess D hm
  have hcancel : (subsetSum D Finset.univ - 1)
      *ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom a) = D.atom a := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hread := dot_weighted_atoms_mulVec (fun c => 1 - D.weight c) D.atom
    ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom a)
  rw [← fullExcess_eq_coParseval, hcancel] at hread
  rw [← hread, pivot_eq_dot, dotProduct_comm]

/-! ## 3. The floor at `(5,3)` -/

/-- The co-weighted total of the pivot deficits at `(5,3)` is exactly one: the
co-weights total four and the pivots total three. -/
theorem sum_coWeight_mul_one_sub_pivot_fiveThree (D : WeightedDesign 5 3) :
    ∑ c, (1 - D.weight c) * (1 - pivot D Finset.univ c) = 1 := by
  have hdesc := descent_identity D (by norm_num)
  have hmass := sum_one_sub_weight D
  have hexpand : ∑ c, (1 - D.weight c) * (1 - pivot D Finset.univ c)
      = (∑ c, (1 - D.weight c)) - ∑ c, (1 - D.weight c) * pivot D Finset.univ c := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hexpand, hmass, hdesc]
  norm_num

/-- **THE PAIR REFUSAL AT THE FULL INDEX SET.**  At a boundary `(5,3)` system
every pair of atoms obeys the depth-two refusal disjunction read against the full
excess: the first pivot reaches one, or the pair's resolvent minor gives way. -/
theorem tie_fullSet_pair_reading (D : WeightedDesign 5 3) (htie : IsTie D)
    {a b : Fin 5} (hab : a ≠ b) :
    1 ≤ pivot D Finset.univ a
      ∨ (1 - pivot D Finset.univ a) * (1 - pivot D Finset.univ b)
        ≤ (D.atom a ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom b)) ^ 2 := by
  have hcard : (Finset.univ : Finset (Fin 5)).card = 5 := by simp
  have hPD : (subsetSum D Finset.univ - 1).PosDef := posDef_fullExcess D (by norm_num)
  have h := tie_fiveSet_pair_reading D htie Finset.univ hcard hPD
    (Finset.mem_univ a) (Finset.mem_univ b) hab
  rw [pivot_eq_dot, pivot_eq_dot]
  exact h

/-- **THE HALF FLOOR.**  At a boundary `(5,3)` system every co-Parseval pivot is
at least one half.

The proof is the second-order law fed by the pair refusals.  Split the resolvent
reading budget at the atom itself, bound each remaining reading below by the
pair minor the refusal supplies, and collapse the rest with the two shipped
moments.  What survives is `t_a·(2ρ_a − 1) ≥ 0`, and the weight is positive. -/
theorem pivot_half_floor (D : WeightedDesign 5 3) (htie : IsTie D) (a : Fin 5) :
    (1 : ℝ) / 2 ≤ pivot D Finset.univ a := by
  classical
  set W := subsetSum D Finset.univ - 1 with hW
  set rho : Fin 5 → ℝ := fun c => pivot D Finset.univ c with hrho
  by_cases hbig : 1 ≤ rho a
  · linarith
  push_neg at hbig
  -- every other atom pays its pair minor
  have hpair : ∀ c, c ≠ a →
      (1 - rho a) * (1 - rho c) ≤ (D.atom c ⬝ᵥ (W⁻¹ *ᵥ D.atom a)) ^ 2 := by
    intro c hc
    rcases tie_fullSet_pair_reading D htie (Ne.symm hc) with hone | hminor
    · exact absurd hone (not_le.mpr hbig)
    · rw [resolvent_reading_comm D (by norm_num) a c] at hminor
      exact hminor
  -- the second-order law, split at the atom
  have hbudget := sum_coWeight_mul_resolvent_reading_sq D (by norm_num) a
  have hselfRead : D.atom a ⬝ᵥ (W⁻¹ *ᵥ D.atom a) = rho a :=
    (pivot_eq_dot D Finset.univ a).symm
  have hsplit : (∑ c ∈ Finset.univ.erase a,
        (1 - D.weight c) * (D.atom c ⬝ᵥ (W⁻¹ *ᵥ D.atom a)) ^ 2)
      + (1 - D.weight a) * rho a ^ 2 = rho a := by
    have h := Finset.sum_erase_add Finset.univ
      (fun c => (1 - D.weight c) * (D.atom c ⬝ᵥ (W⁻¹ *ᵥ D.atom a)) ^ 2)
      (Finset.mem_univ a)
    rw [hselfRead] at h
    rw [h]; exact hbudget
  -- the deficits, split at the atom
  have hdef := sum_coWeight_mul_one_sub_pivot_fiveThree D
  have hdefSplit : (∑ c ∈ Finset.univ.erase a, (1 - D.weight c) * (1 - rho c))
      + (1 - D.weight a) * (1 - rho a) = 1 := by
    have h := Finset.sum_erase_add Finset.univ
      (fun c => (1 - D.weight c) * (1 - rho c)) (Finset.mem_univ a)
    rw [h]; exact hdef
  -- the lower bound on the erased sum
  have hcoPos : ∀ c : Fin 5, 0 < 1 - D.weight c := fun c => by
    linarith [weight_lt_one D (by norm_num) c]
  have hlow : (1 - rho a) * (∑ c ∈ Finset.univ.erase a, (1 - D.weight c) * (1 - rho c))
      ≤ ∑ c ∈ Finset.univ.erase a,
          (1 - D.weight c) * (D.atom c ⬝ᵥ (W⁻¹ *ᵥ D.atom a)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hne : c ≠ a := Finset.ne_of_mem_erase hc
    have := hpair c hne
    nlinarith [hcoPos c, this]
  -- collapse
  have hwpos := D.weight_pos a
  nlinarith [hsplit, hdefSplit, hlow, hwpos, hbig]

/-! ## 4. What the floor decides -/

/-- The scalar statement Question 7.1 reduces to: some atom of a boundary
`(5,3)` system attains the half floor. -/
def PivotHalfAttained : Prop :=
  ∀ D : WeightedDesign 5 3, IsTie D →
    ∃ a : Fin 5, pivot D Finset.univ a ≤ (1 : ℝ) / 2

/-- **THE FLOOR IS ATTAINED EXACTLY.**  Under `Gtz.PivotHalfAttained` the
minimum pivot of a boundary `(5,3)` system is exactly one half. -/
theorem exists_pivot_eq_half_of_attained (hattained : PivotHalfAttained)
    (D : WeightedDesign 5 3) (htie : IsTie D) :
    ∃ a : Fin 5, pivot D Finset.univ a = (1 : ℝ) / 2 := by
  obtain ⟨a, hle⟩ := hattained D htie
  exact ⟨a, le_antisymm hle (pivot_half_floor D htie a)⟩

/-- **AN ATTAINING ATOM PAYS EVERY PAIR MINOR.**  If an atom sits at the half
floor then each of its four pair minors against the resolvent is at least the
squared cross reading — one half of the equality the floor's tightness forces,
and the half that needs no new argument. -/
theorem resolvent_pair_minor_le_of_pivot_eq_half (D : WeightedDesign 5 3)
    (htie : IsTie D) {a : Fin 5} (hhalf : pivot D Finset.univ a = (1 : ℝ) / 2)
    {c : Fin 5} (hc : c ≠ a) :
    (1 - pivot D Finset.univ a) * (1 - pivot D Finset.univ c)
      ≤ (D.atom a ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c)) ^ 2 := by
  rcases tie_fullSet_pair_reading D htie (Ne.symm hc) with hone | hminor
  · rw [hhalf] at hone; linarith
  · exact hminor

end Gtz
