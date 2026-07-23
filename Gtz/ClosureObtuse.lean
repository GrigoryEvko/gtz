/-
# Closure forces an obtuse pair: the half-circle argument's germ

The gaps-stability σ_min(J)-floor argument runs on one generic fact: a
positively-weighted family of nonzero vectors that sums to zero cannot be
pairwise-acute — expanding `0 = |Σ t_c v_c|²` leaves a strictly positive
diagonal against the cross terms, so some ordered pair has strictly negative
weighted overlap, hence some pair of atoms is obtuse. Any rank, any size,
spectra-free. (At rank 2 this is "some pair has gap ≥ π/2", which kills
near-collinearity of the design's squares and floors the Jacobian.)
-/
import Mathlib
import Gtz.ResolventPerturbation

namespace Gtz

open Finset

variable {m k : ℕ}

/-- **Closure forces an obtuse pair**: positive weights, nonzero atoms,
vanishing weighted sum ⟹ some distinct pair has negative overlap. -/
theorem closure_forces_obtuse_pair (weight : Fin m → ℝ)
    (atom : Fin m → (Fin k → ℝ))
    (hweightPos : ∀ c, 0 < weight c)
    (hatomNonzero : ∃ c, atom c ≠ 0)
    (hclosure : ∑ c, weight c • atom c = 0) :
    ∃ c d, c ≠ d ∧ atom c ⬝ᵥ atom d < 0 := by
  -- expand the vanishing square of the closure
  have hsquare : (0:ℝ)
      = ∑ c, ∑ d, (weight c * weight d) * (atom c ⬝ᵥ atom d) := by
    have hdot : (∑ c, weight c • atom c) ⬝ᵥ (∑ c, weight c • atom c)
        = 0 := by
      rw [hclosure, dotProduct_zero]
    rw [sum_dotProduct] at hdot
    calc (0:ℝ) = ∑ c, (weight c • atom c) ⬝ᵥ (∑ d, weight d • atom d) := by
          rw [← hdot]
      _ = ∑ c, ∑ d, (weight c * weight d) * (atom c ⬝ᵥ atom d) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [smul_dotProduct, dotProduct_sum, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [dotProduct_smul, smul_eq_mul]
          ring
  -- the diagonal is strictly positive at the nonzero atom
  obtain ⟨witness, hwitness⟩ := hatomNonzero
  have hdiagPos : 0 < ∑ c ∈ {witness},
      (weight c * weight c) * (atom c ⬝ᵥ atom c) := by
    rw [Finset.sum_singleton]
    have hselfPos : 0 < atom witness ⬝ᵥ atom witness := by
      rcases lt_or_eq_of_le (dotProduct_self_nonneg (atom witness)) with
        hpos | hzero
      · exact hpos
      · exact absurd (eq_zero_of_dotProduct_self_eq_zero hzero.symm) hwitness
    exact mul_pos (mul_pos (hweightPos witness) (hweightPos witness)) hselfPos
  -- so some off-diagonal weighted term is negative
  by_contra hall
  push_neg at hall
  have htermNonneg : ∀ c ∈ (Finset.univ : Finset (Fin m)), ∀ d ∈ Finset.univ,
      c ≠ d → 0 ≤ (weight c * weight d) * (atom c ⬝ᵥ atom d) := by
    intro c _ d _ hne
    exact mul_nonneg (mul_pos (hweightPos c) (hweightPos d)).le (hall c d hne)
  have hdiagNonneg : ∀ c ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ (weight c * weight c) * (atom c ⬝ᵥ atom c) := fun c _ =>
    mul_nonneg (mul_pos (hweightPos c) (hweightPos c)).le
      (dotProduct_self_nonneg _)
  -- every summand is nonnegative and one is positive: the total is positive
  have htotal : 0 < ∑ c, ∑ d, (weight c * weight d) * (atom c ⬝ᵥ atom d) := by
    have hinner : ∀ c ∈ (Finset.univ : Finset (Fin m)),
        0 ≤ ∑ d, (weight c * weight d) * (atom c ⬝ᵥ atom d) := by
      intro c _
      refine Finset.sum_nonneg fun d _ => ?_
      rcases eq_or_ne c d with rfl | hne
      · exact hdiagNonneg c (Finset.mem_univ c)
      · exact htermNonneg c (Finset.mem_univ c) d (Finset.mem_univ d) hne
    refine Finset.sum_pos' hinner ⟨witness, Finset.mem_univ witness, ?_⟩
    refine Finset.sum_pos' (fun d _ => ?_) ⟨witness, Finset.mem_univ _, ?_⟩
    · rcases eq_or_ne witness d with rfl | hne
      · exact hdiagNonneg witness (Finset.mem_univ witness)
      · exact htermNonneg witness (Finset.mem_univ _) d (Finset.mem_univ d) hne
    · simpa using hdiagPos
  linarith [hsquare, htotal]

end Gtz
