import Gtz.Wave.CornerSecondMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The four-set trace floor of a tie

A four-set of atoms contains exactly FOUR triples, and each of them is one
rank-one downdate away from the four-set's own gap.  At a tie every one of the
four refuses, so each atom of the four-set reads the inverse gap at least at
one, and the four readings add to the trace of the identity plus the trace of
the inverse gap.

  `Σ_{a∈F} g_aᵀ (S_F − 1)⁻¹ g_a = tr((S_F − 1)⁻¹ S_F) = 3 + tr((S_F − 1)⁻¹)` ,

so `4 ≤ 3 + tr((S_F − 1)⁻¹)` (`Gtz.fourSet_trace_floor`):

  **every four-set of a tie whose gap is positive definite has
  `tr((S_F − 1)⁻¹) ≥ 1`.**

The floor caps how far a four-set can dominate: a four-set whose inverse gap has
trace below one cannot occur at a tie
(`Gtz.not_isTie_of_fourSet_trace_lt`).  Nothing in the statement reads the
weights, and nothing reads the size beyond `|F| = 4` and rank three, so the
floor holds at every `(m,3)`.

At a corank-two corner the four-sets `{e} ∪ Cᶜ` are exactly the ones whose four
triples are the complement triple and the three one-inside triples through `e`,
so the floor is the corner's own reading of the refusal budget.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. Dropping one atom is a rank-one downdate -/

/-- Removing one atom from a set is a rank-one downdate of its gap. -/
theorem subsetSum_erase_sub_one_rankOne (D : WeightedDesign m 3) (F : Finset (Fin m))
    {a : Fin m} (ha : a ∈ F) :
    subsetSum D (F.erase a) - 1
      = (subsetSum D F - 1) - Matrix.vecMulVec (D.atom a) (D.atom a) := by
  classical
  have hsum : subsetSum D F
      = atomMatrix (D.atom a) + subsetSum D (F.erase a) := by
    rw [subsetSum, subsetSum, ← Finset.add_sum_erase F _ ha]
  rw [hsum, show atomMatrix (D.atom a) = Matrix.vecMulVec (D.atom a) (D.atom a) from rfl]
  abel

/-! ## 2. Every atom of a strictly dominating four-set reads its gap at one -/

/-- **A refused triple reads its four-set gap at least at one.**  The triple is
one rank-one downdate from the four-set, so its failure to dominate strictly is
exactly a leverage floor. -/
theorem fourSet_leverage_ge_one (D : WeightedDesign m 3) (htie : IsTie D)
    (F : Finset (Fin m)) (hcard : F.card = 4)
    (hPD : (subsetSum D F - 1).PosDef) {a : Fin m} (ha : a ∈ F) :
    1 ≤ D.atom a ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom a) := by
  classical
  have hT : (F.erase a).card = 3 := by
    rw [Finset.card_erase_of_mem ha, hcard]
  have hnot := htie.2 (F.erase a) hT
  rw [subsetSum_erase_sub_one_rankOne D F ha] at hnot
  by_contra hlt
  push_neg at hlt
  exact hnot ((posDef_sub_vecMulVec_iff _ hPD (D.atom a)).mpr hlt)

/-! ## 3. The trace floor -/

/-- **The four-set trace floor.**  At a tie every four-set with a positive
definite gap obeys `1 ≤ tr((S_F − 1)⁻¹)`.  The four triples of the four-set each
contribute a unit of leverage, and the four units total the rank plus the trace
of the inverse gap. -/
theorem fourSet_trace_floor (D : WeightedDesign m 3) (htie : IsTie D)
    (F : Finset (Fin m)) (hcard : F.card = 4)
    (hPD : (subsetSum D F - 1).PosDef) :
    1 ≤ Matrix.trace ((subsetSum D F - 1)⁻¹) := by
  classical
  set B : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hB
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  have hsum : (4 : ℝ) ≤ ∑ a ∈ F, D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a) := by
    calc (4 : ℝ) = ∑ _a ∈ F, (1 : ℝ) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
          norm_num
      _ ≤ ∑ a ∈ F, D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a) :=
          Finset.sum_le_sum fun a ha =>
            fourSet_leverage_ge_one D htie F hcard hPD ha
  have htr := sum_subset_quadForm_eq_trace D F B⁻¹
  have hSF : subsetSum D F = B + 1 := by rw [hB]; abel
  have hval : Matrix.trace (B⁻¹ * subsetSum D F) = 3 + Matrix.trace B⁻¹ := by
    rw [hSF, Matrix.mul_add, Matrix.mul_one, Matrix.trace_add,
      Matrix.nonsing_inv_mul B hu, Matrix.trace_one]
    norm_num
  rw [htr, hval] at hsum
  linarith

/-- **The contrapositive.**  A design with a four-set whose gap is positive
definite and whose inverse gap has trace below one is not a tie. -/
theorem not_isTie_of_fourSet_trace_lt (D : WeightedDesign m 3)
    (F : Finset (Fin m)) (hcard : F.card = 4)
    (hPD : (subsetSum D F - 1).PosDef)
    (hsmall : Matrix.trace ((subsetSum D F - 1)⁻¹) < 1) : ¬ IsTie D := fun htie =>
  absurd (fourSet_trace_floor D htie F hcard hPD) (not_le.mpr hsmall)

/-- **The floor read at the corner.**  At a corank-two corner the four-set
`{e} ∪ Cᶜ` carries the complement refusal and the three one-inside refusals
through `e`, so its inverse gap has trace at least one. -/
theorem corner_fourSet_trace_floor (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {e : Fin 6} (he : e ∈ C)
    (hPD : (subsetSum D (insert e Cᶜ) - 1).PosDef) :
    1 ≤ Matrix.trace ((subsetSum D (insert e Cᶜ) - 1)⁻¹) := by
  classical
  have hcompl : (Cᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, hcard]; simp
  have hne : e ∉ (Cᶜ : Finset (Fin 6)) := by simpa using he
  have hF : (insert e (Cᶜ : Finset (Fin 6))).card = 4 := by
    rw [Finset.card_insert_of_notMem hne, hcompl]
  exact fourSet_trace_floor D htie _ hF hPD

end Gtz
