/-
# The one object, narrowed to a finite system

The seventh (open) conjunct of `Gtz.LiftingLemma` at rank `k = 2` — the
(6,3)/(7,3) frontier, kernel-equivalent by `liftingLemma_two_iff_the_two_residuals`
to the entire remaining content of the 1997 problem at rank 3 — is a
universally-quantified discriminant over all test vectors:

    ∀ v : Fin 2 → ℝ,  ⟨m, v⟩² ≤ A · (vᵀ(G' - I)v),   i.e.  A·(G' - I) - m·mᵀ ⪰ 0,

with `A = ⟨u, g_pivot⟩² + Σ r_c² - 1`, `r_c = ⟨u, g_c⟩`, `g'_c = B·g_c`. For a
projected pair the form is `2×2`, and a `2×2` symmetric form is globally
nonnegative iff its trace and determinant are nonnegative. So the object's open
content, per (pivot, pair), is exactly TWO scalar polynomial inequalities — the
∀-quantifier over test vectors is eliminated.

This is a faithful narrowing, not a proof: the one object stays open (its
compact-collar minimizer is the tie variety, floor exactly 0, false over ℂ), but
its shape is now a finite real-algebraic system. Result of the gtz3-one-object
workflow (both adversarial audits SOUND).
-/
import Mathlib

namespace Gtz

/-- **The `2×2` nonnegativity criterion**: a real symmetric quadratic form
`p·x² + 2q·xy + s·y²` is globally nonnegative iff its trace `p + s` and its
determinant `p·s - q²` are both nonnegative. The scalar heart that collapses the
seventh Lifting-Lemma conjunct (over all test vectors in `ℝ²`) to a finite
system; boundary-robust — the `p = 0` degenerate case (a tight projected
direction) is handled without division. -/
theorem twoByTwoForm_nonneg_iff_trace_det_nonneg (p q s : ℝ) :
    (∀ x y : ℝ, 0 ≤ p * x ^ 2 + 2 * q * x * y + s * y ^ 2)
      ↔ (0 ≤ p + s ∧ 0 ≤ p * s - q ^ 2) := by
  constructor
  · intro hform
    have hpNonneg : 0 ≤ p := by have := hform 1 0; nlinarith [this]
    have hsNonneg : 0 ≤ s := by have := hform 0 1; nlinarith [this]
    refine ⟨by linarith, ?_⟩
    by_cases hppos : 0 < p
    · have hkey := hform (-(q / p)) 1
      have hexpand : p * (-(q / p)) ^ 2 + 2 * q * (-(q / p)) * 1 + s * 1 ^ 2
          = s - q ^ 2 / p := by
        field_simp; ring
      rw [hexpand] at hkey
      have hmul := (div_le_iff₀ hppos).mp (by linarith [hkey] : q ^ 2 / p ≤ s)
      nlinarith [hmul]
    · have hpZero : p = 0 := le_antisymm (not_lt.mp hppos) hpNonneg
      have hqZero : q = 0 := by
        by_contra hqne
        have hbad := hform (-(s + 1) / (2 * q)) 1
        rw [hpZero] at hbad
        have hcancel : 2 * q * (-(s + 1) / (2 * q)) * 1 = -(s + 1) := by
          field_simp
        nlinarith [hbad, hcancel]
      rw [hpZero, hqZero]; norm_num
  · rintro ⟨htrace, hdet⟩ x y
    by_cases hppos : 0 < p
    · nlinarith [sq_nonneg (p * x + q * y), hdet, hppos, sq_nonneg y,
        mul_pos hppos hppos]
    · have hple : p ≤ 0 := not_lt.mp hppos
      have hpZero : p = 0 := by nlinarith [hdet, htrace, sq_nonneg q]
      have hqZero : q = 0 := by nlinarith [hdet, hpZero, sq_nonneg q]
      have hsNonneg : 0 ≤ s := by nlinarith [htrace, hpZero]
      rw [hpZero, hqZero]; nlinarith [sq_nonneg y, hsNonneg]

/-- **The rank-3 discriminant as a finite system**: with the assembled `2×2`
entries of `A·(G' - I) - m·mᵀ` — `p = A·(G'₀₀ - 1) - m₀²`, `q = A·G'₀₁ - m₀m₁`,
`s = A·(G'₁₁ - 1) - m₁²` — the seventh Lifting-Lemma conjunct at rank 3 (the
discriminant over ALL test vectors `v = (x, y)`) holds iff the trace and
determinant of that `2×2` matrix are nonnegative. The ∀-quantifier over test
vectors is eliminated; the one object's open content, per (pivot, pair), is the
pair of scalar polynomial inequalities on the right. -/
theorem rank3Discriminant_iff_trace_det_nonneg
    (bigA g00 g01 g11 m0 m1 : ℝ) :
    (∀ x y : ℝ,
        (m0 * x + m1 * y) ^ 2
          ≤ bigA * ((g00 * x ^ 2 + 2 * g01 * x * y + g11 * y ^ 2)
              - (x ^ 2 + y ^ 2)))
      ↔ (0 ≤ (bigA * (g00 - 1) - m0 ^ 2) + (bigA * (g11 - 1) - m1 ^ 2)
          ∧ 0 ≤ (bigA * (g00 - 1) - m0 ^ 2) * (bigA * (g11 - 1) - m1 ^ 2)
              - (bigA * g01 - m0 * m1) ^ 2) := by
  have hrewrite : ∀ x y : ℝ,
      (0 ≤ (bigA * (g00 - 1) - m0 ^ 2) * x ^ 2
            + 2 * (bigA * g01 - m0 * m1) * x * y
            + (bigA * (g11 - 1) - m1 ^ 2) * y ^ 2)
        ↔ ((m0 * x + m1 * y) ^ 2
            ≤ bigA * ((g00 * x ^ 2 + 2 * g01 * x * y + g11 * y ^ 2)
                - (x ^ 2 + y ^ 2))) := by
    intro x y; constructor <;> intro h <;> nlinarith [h]
  constructor
  · intro hobj
    exact (twoByTwoForm_nonneg_iff_trace_det_nonneg _ _ _).mp
      (fun x y => (hrewrite x y).mpr (hobj x y))
  · intro hsys x y
    exact (hrewrite x y).mp
      ((twoByTwoForm_nonneg_iff_trace_det_nonneg _ _ _).mpr hsys x y)

end Gtz
