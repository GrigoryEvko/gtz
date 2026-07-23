/-
# The cyclic stress criterion: nontrivial stress forces the ratio product to close

The full-stress-cycle wall's determinant criterion (p4c5 §3, verified at the
anchor), in its generic algebraic form. A stress vector on a k-cycle
satisfies the interior compatibility at every atom: consecutive stresses are
tied by `λ_{i} · g_i = −λ_{i+1} · h_i` (the two-edge stress equation at atom
`i+1`, with `g_i, h_i` the two leaf-form couplings). A nonzero solution
telescopes around the cycle:

`(∏ λ) · (∏ g) = (−1)ᵏ · (∏ λ) · (∏ h)`,

and when every stress is nonzero this pins `∏ (g_i / h_i) = (−1)ᵏ` — the
closure condition whose Cayley-torsion solutions are the Poncelet wall.
Stated over the cyclic index `ZMod k` with everything division-free: the
kernel content is the telescoping itself, list-generic.
-/
import Mathlib

namespace Gtz

/-- **The cyclic telescoping law**: per-step ties `λ_i·g_i = −λ_{i+1}·h_i`
around a cycle multiply to `(∏λ)·(∏g) = (−1)ᵏ·(∏λ')·(∏h)` where `λ'` is the
rotated stress — and the rotation preserves the product, so
`(∏λ)·(∏g) = (−1)ᵏ·(∏λ)·(∏h)`. Division-free, any `k`. -/
theorem cyclic_stress_telescope {k : ℕ} [NeZero k]
    (stress leafG leafH : ZMod k → ℝ)
    (hties : ∀ i, stress i * leafG i = -(stress (i + 1) * leafH i)) :
    (∏ i, stress i) * (∏ i, leafG i)
      = (-1)^k * (∏ i, stress i) * (∏ i, leafH i) := by
  have hproduct : ∏ i, (stress i * leafG i)
      = ∏ i, (-(stress (i + 1) * leafH i)) :=
    Finset.prod_congr rfl fun i _ => hties i
  have hleft : ∏ i, (stress i * leafG i)
      = (∏ i, stress i) * (∏ i, leafG i) := Finset.prod_mul_distrib
  have hsign : ∏ i, (-(stress (i + 1) * leafH i))
      = (-1)^k * ∏ i, (stress (i + 1) * leafH i) := by
    have hpointwise : ∏ i, (-(stress (i + 1) * leafH i))
        = ∏ i, ((-1) * (stress (i + 1) * leafH i)) :=
      Finset.prod_congr rfl fun i _ => by ring
    rw [hpointwise, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, ZMod.card]
  have hrotate : ∏ i, stress (i + 1) = ∏ i, stress i :=
    Fintype.prod_equiv (Equiv.addRight (1 : ZMod k)) _ _ fun i => rfl
  have hright : ∏ i, (stress (i + 1) * leafH i)
      = (∏ i, stress i) * (∏ i, leafH i) := by
    rw [Finset.prod_mul_distrib, hrotate]
  calc (∏ i, stress i) * (∏ i, leafG i)
      = ∏ i, (stress i * leafG i) := hleft.symm
    _ = ∏ i, (-(stress (i + 1) * leafH i)) := hproduct
    _ = (-1)^k * ∏ i, (stress (i + 1) * leafH i) := hsign
    _ = (-1)^k * ((∏ i, stress i) * (∏ i, leafH i)) := by rw [hright]
    _ = (-1)^k * (∏ i, stress i) * (∏ i, leafH i) := by ring

/-- **The closure criterion**: a nowhere-zero stress on the cycle forces the
coupling products to close — `∏g = (−1)ᵏ·∏h`. This is `∏(g/h) = (−1)ᵏ` in
division-free form: the algebraic gate every full-stress cycle must pass,
whose solutions on the conic are the Cayley-torsion loci. -/
theorem cyclic_stress_closure {k : ℕ} [NeZero k]
    (stress leafG leafH : ZMod k → ℝ)
    (hties : ∀ i, stress i * leafG i = -(stress (i + 1) * leafH i))
    (hnonzero : ∀ i, stress i ≠ 0) :
    (∏ i, leafG i) = (-1)^k * (∏ i, leafH i) := by
  have htelescope := cyclic_stress_telescope stress leafG leafH hties
  have hstressProd : (∏ i, stress i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hnonzero i
  have hrearranged : (∏ i, stress i) * (∏ i, leafG i)
      = (∏ i, stress i) * ((-1)^k * (∏ i, leafH i)) := by
    rw [htelescope]; ring
  exact mul_left_cancel₀ hstressProd hrearranged

/-- **The contrapositive kill**: when the coupling products FAIL to close,
every cyclic stress has a zero — the stress support cannot be full, and the
leaf-tangency theorem finishes the cycle off. The deep-cycle wall is exactly
the inhabitation question of the closure equation. -/
theorem cyclic_stress_vanishes_of_open {k : ℕ} [NeZero k]
    (stress leafG leafH : ZMod k → ℝ)
    (hties : ∀ i, stress i * leafG i = -(stress (i + 1) * leafH i))
    (hopen : (∏ i, leafG i) ≠ (-1)^k * (∏ i, leafH i)) :
    ∃ i, stress i = 0 := by
  by_contra hall
  push_neg at hall
  exact hopen (cyclic_stress_closure stress leafG leafH hties hall)

end Gtz
