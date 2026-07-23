/-
# Theorem Z-AGG: the aggregate pushoff — six-plane manifold contact is impossible

The z-mass workflow's structural instrument (audit-confirmed): per atom-plane
the Zero-Atom Pushoff prices the plane's distance to the tight-triangle
manifold against the atom's own weight, `t_e ≤ L_e·dist_e` (the kernel's
`zeroAtom_pushoff_clean` with Lipschitz constant `L = 1/2 + |ξ|`). Summed over
ALL atom-planes with `Σ t_e = 1`, the distances cannot be simultaneously
small: `L_sup·Σ dist_e ≥ 1`, and by pigeonhole some plane sits at distance at
least `1/(m·L_sup)` — at `(6,3)` with `L_sup < 1`, some plane is at distance
`> 1/6`. The `t_e → 0` escape can hollow one plane, never all of them.

Stated hypothesis-parameterized over the per-plane pushoff conclusions, which
each planar compression instantiates.
-/
import Mathlib
import Gtz.Basic

namespace Gtz

variable {m : ℕ}

/-- **Z-AGG, the summed form**: per-plane pushoff bounds with capped Lipschitz
constants force the total manifold distance to at least `1/L_sup`. -/
theorem aggregate_pushoff (weight planeDist lipschitz : Fin m → ℝ)
    {lipschitzSup : ℝ}
    (hweightSum : ∑ e, weight e = 1)
    (hdistNonneg : ∀ e, 0 ≤ planeDist e)
    (hperPlane : ∀ e, weight e ≤ lipschitz e * planeDist e)
    (hlipschitzCap : ∀ e, lipschitz e ≤ lipschitzSup) :
    1 ≤ lipschitzSup * ∑ e, planeDist e := by
  calc (1 : ℝ) = ∑ e, weight e := hweightSum.symm
    _ ≤ ∑ e, lipschitzSup * planeDist e := by
        refine Finset.sum_le_sum fun e _ => ?_
        exact le_trans (hperPlane e)
          (mul_le_mul_of_nonneg_right (hlipschitzCap e) (hdistNonneg e))
    _ = lipschitzSup * ∑ e, planeDist e := by rw [Finset.mul_sum]

/-- **Z-AGG, the pigeonhole form**: some single plane carries distance at
least `1/(m·L_sup)` — simultaneous near-contact of every atom-plane with the
tight-triangle manifold is impossible. Division-free. -/
theorem aggregate_pushoff_pigeonhole (weight planeDist lipschitz : Fin m → ℝ)
    {lipschitzSup : ℝ}
    (hweightSum : ∑ e, weight e = 1)
    (hdistNonneg : ∀ e, 0 ≤ planeDist e)
    (hperPlane : ∀ e, weight e ≤ lipschitz e * planeDist e)
    (hlipschitzCap : ∀ e, lipschitz e ≤ lipschitzSup) :
    ∃ e, 1 ≤ (m : ℝ) * (lipschitzSup * planeDist e) := by
  have htotal := aggregate_pushoff weight planeDist lipschitz hweightSum
    hdistNonneg hperPlane hlipschitzCap
  by_contra hcontra
  push_neg at hcontra
  have hcardPos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hzero | hpos
    · exfalso
      subst hzero
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hweightSum
      exact one_ne_zero hweightSum.symm
    · exact hpos
  have hsumLt : lipschitzSup * ∑ e, planeDist e < 1 := by
    have hterm : ∀ e : Fin m, lipschitzSup * planeDist e < 1 / m := by
      intro e
      have hstrict := hcontra e
      rw [lt_div_iff₀ (by exact_mod_cast hcardPos : (0:ℝ) < m)]
      linarith [hstrict]
    calc lipschitzSup * ∑ e, planeDist e
        = ∑ e, lipschitzSup * planeDist e := Finset.mul_sum _ _ _
      _ < ∑ _e : Fin m, 1 / (m : ℝ) := by
          refine Finset.sum_lt_sum_of_nonempty ?_ fun e _ => hterm e
          exact Finset.univ_nonempty_iff.mpr
            ⟨⟨0, hcardPos⟩⟩
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          field_simp
  linarith [htotal, hsumLt]

end Gtz
