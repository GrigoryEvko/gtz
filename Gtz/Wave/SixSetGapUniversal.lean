import Gtz.Wave.SixSetProjection
import Gtz.Reduction.RealVolumeFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The six-set gap is positive definite at EVERY design

`Gtz.sixSetGap_posDef_of_rankOneGap` proves `S_univ − 1 ≻ 0` at the corank-two
corner, through the split criterion and the outside plane cover.  That work is
unnecessary: the statement holds at every weighted design with at least two
atoms, with no hypothesis on any dominator.

The reason is the co-weighted reading of the gap
(`Gtz.coweight_atomSum_eq_sixSetGap`):

  `S_univ − 1 = Σ_c (1 − t_c)·g_c g_cᵀ` .

Every co-weight is positive, because a design with two or more atoms has every
weight strictly below one.  So the form vanishes on a direction only if that
direction is orthogonal to EVERY atom, and Parseval forbids that: reading
`|w|² = Σ_c t_c (g_c·w)²` at such a direction gives `|w|² = 0`.

The consequence is that the whole projection calculus — the pivot matrix, the
projection identity, the trace law, the caps, the downdate dictionary — is
unconditional, at every corank, with no corner hypothesis.
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-- **The six-set gap is positive definite, unconditionally.**  Every weighted
design with at least two atoms has `S_univ − 1 ≻ 0`. -/
theorem sixSetGap_posDef (D : WeightedDesign m k) (hm : 2 ≤ m) :
    (subsetSum D Finset.univ - 1).PosDef := by
  classical
  have hform : ∀ w : Fin k → ℝ,
      w ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ w)
        = ∑ c, (1 - D.weight c) * (D.atom c ⬝ᵥ w) ^ 2 := by
    intro w
    rw [← coweight_atomSum_eq_sixSetGap D, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm w (D.atom c)]
    ring
  have hherm : (subsetSum D Finset.univ - 1).IsHermitian :=
    isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D Finset.univ)
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hherm, fun w hwne => ?_⟩
  rw [star_trivial, hform]
  have hnn : ∀ c ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ (1 - D.weight c) * (D.atom c ⬝ᵥ w) ^ 2 := fun c _ =>
    mul_nonneg (by linarith [design_weight_lt_one D hm c]) (sq_nonneg _)
  by_contra hcon
  push_neg at hcon
  have hsum0 : ∑ c, (1 - D.weight c) * (D.atom c ⬝ᵥ w) ^ 2 = 0 :=
    le_antisymm hcon (Finset.sum_nonneg hnn)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0
  -- every atom reads the direction at zero, which Parseval forbids
  have hzero : ∀ c : Fin m, D.atom c ⬝ᵥ w = 0 := by
    intro c
    have hco : (0:ℝ) < 1 - D.weight c := by
      linarith [design_weight_lt_one D hm c]
    have hsq : (D.atom c ⬝ᵥ w) ^ 2 = 0 := by
      rcases mul_eq_zero.mp (hterm c (Finset.mem_univ c)) with h | h
      · exact absurd h (ne_of_gt hco)
      · exact h
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hsq
  have hpar := dotProduct_self_eq_sum_weight_mul_sq D w
  have hall : ∑ c, D.weight c * (D.atom c ⬝ᵥ w) ^ 2 = 0 :=
    Finset.sum_eq_zero fun c _ => by rw [hzero c]; ring
  rw [hall] at hpar
  exact absurd hpar (ne_of_gt (dotProduct_self_pos hwne))

/-- **The six-set gap is positive definite at every `(6,3)` design.**  The
instance the hinge consumes: no corner hypothesis, no dominator, no corank
case. -/
theorem sixSetGap_posDef_sixThree (D : WeightedDesign 6 3) :
    (subsetSum D Finset.univ - 1).PosDef :=
  sixSetGap_posDef D (by norm_num)

end Gtz
