/-
# The per-atom leverage bound: no atom dominates a tight frame

The isotropy constraint `Σ_c t_c g_c g_cᵀ = I` forces a hard ceiling on every
individual atom's leverage share: for each atom, `t_c · ℓ_c ≤ 1` where
`ℓ_c = |g_c|²`. Equivalently, `t_c g_c g_cᵀ ⪯ I` (one rank-one term of a PSD
resolution of the identity cannot exceed the whole), so its single nonzero
eigenvalue `t_c ℓ_c` is at most 1. This is the frame-theoretic foundation of
the leverage-decay story (`ρ(ℓ̄)`): a design's pivots and cap dictionary are
all controlled by leverage, and leverage is universally bounded here.

Proof is elementary and matrix-agnostic: the erased sum
`I − t_e g_e g_eᵀ = Σ_{c≠e} t_c g_c g_cᵀ` evaluated at `g_e` is a sum of
nonnegative terms `t_c ⟨g_c, g_e⟩² ≥ 0`, giving `ℓ_e − t_e ℓ_e² ≥ 0`.
-/
import Mathlib
import Gtz.Basic
import Gtz.MarginTransfer

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-- `leverageOf` in dot-product form. -/
theorem leverageOf_eq_dotProduct (g : Fin k → ℝ) : leverageOf g = g ⬝ᵥ g := by
  simp only [leverageOf, dotProduct, pow_two]

/-- **The per-atom leverage bound**: in any weighted design (tight frame),
each atom's weighted leverage is at most one — `t_e · ℓ_e ≤ 1`. No single
atom can carry more than the whole identity's worth of a direction. -/
theorem weighted_leverage_le_one (D : WeightedDesign m k) (e : Fin m) :
    D.weight e * leverageOf (D.atom e) ≤ 1 := by
  set probe := D.atom e with hprobe
  set lev := probe ⬝ᵥ probe with hlev
  -- the erased quadratic form at the atom is a sum of nonnegative terms
  have herasedNonneg :
      0 ≤ probe ⬝ᵥ ((∑ c ∈ univ.erase e,
        D.weight c • atomMatrix (D.atom c)) *ᵥ probe) := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_nonneg fun c _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]
    exact mul_nonneg (D.weight_pos c).le (sq_nonneg _)
  -- read the same form through Parseval's erased identity
  have hreading : probe ⬝ᵥ ((∑ c ∈ univ.erase e,
        D.weight c • atomMatrix (D.atom c)) *ᵥ probe)
      = lev - D.weight e * lev ^ 2 := by
    rw [parseval_erase, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]
  rw [hreading] at herasedNonneg
  -- `lev - t·lev² ≥ 0` with `lev ≥ 0` gives `t·lev ≤ 1`
  have hlevNonneg : 0 ≤ lev := by
    rw [hlev]; exact dotProduct_self_nonneg probe
  have hlevEq : leverageOf (D.atom e) = lev := by
    rw [hlev, hprobe, leverageOf_eq_dotProduct]
  rw [hlevEq]
  rcases eq_or_lt_of_le hlevNonneg with hzero | hpos
  · rw [← hzero]; simpa using zero_le_one
  · have hcancel : D.weight e * lev * lev ≤ 1 * lev := by
      rw [one_mul]; nlinarith [herasedNonneg]
    exact le_of_mul_le_mul_right hcancel hpos

/-- **Leverage decay**: with all weights at least `weightFloor > 0`, every
atom's raw leverage is bounded by `1/weightFloor` — the uniform ceiling that
the `ρ(ℓ̄)` pivot-spread argument consumes. -/
theorem leverage_le_of_weight_floor (D : WeightedDesign m k)
    {weightFloor : ℝ} (hfloor : 0 < weightFloor)
    (hweights : ∀ c, weightFloor ≤ D.weight c) (e : Fin m) :
    leverageOf (D.atom e) ≤ 1 / weightFloor := by
  have hshare := weighted_leverage_le_one D e
  have hlevNonneg : 0 ≤ leverageOf (D.atom e) :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hfloorShare : weightFloor * leverageOf (D.atom e)
      ≤ D.weight e * leverageOf (D.atom e) :=
    mul_le_mul_of_nonneg_right (hweights e) hlevNonneg
  rw [le_div_iff₀ hfloor, mul_comm]
  linarith [hshare, hfloorShare]

end Gtz
