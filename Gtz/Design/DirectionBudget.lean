/-
# The per-direction budget and the complementary-pair exclusion

Every tool the campaign has aimed at the selection problem is ISOTROPIC: the
trace identity, the pivot budget, the leverage cap and the bad-edge count are
rotation-invariant scalars.  The obstruction is not.  A selection fails because
some SINGLE direction overloads it, and different selections are overloaded in
different directions.

This module reads the problem one direction at a time.  At a probe `y` the
squared reading of an atom is `(a_c ⬝ y)^2`.  Two budgets hold at every probe:

  `∑ c, weight c * (a_c ⬝ y)^2 = y ⬝ y`                    (Parseval)
  `y ⬝ (univGap *ᵥ y) = ∑ c, (1 - weight c) * (a_c ⬝ y)^2` (deficiency)

A selection omitting `T` is positive definite exactly when `∑_{c ∈ T}` of the
readings stays below the deficiency budget at every probe.

The payoff is the COMPLEMENTARY-PAIR EXCLUSION.  If a label set and its
complement both overload one probe, adding the two inequalities gives
`∑ c, (a_c ⬝ y)^2 ≥ 2 * ∑ c, (1 - weight c) * (a_c ⬝ y)^2`, and that forces some
weight to reach one half.  So when every weight is below one half, at most ONE
of any complementary pair fails at a given direction.  At `(6,3)` the twenty
triples form ten complementary pairs, so at most ten fail at any single
direction — a ceiling measured to be attained exactly, never exceeded.

Nothing here whitens, inverts, or takes a square root.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.MarginTransfer
import Gtz.Design.ComplementLeverageLaw

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- **The Parseval budget at a probe.**  The weighted squared readings of all
atoms recover the probe energy, at every probe.  This is Parseval read one
direction at a time. -/
theorem sum_weight_mul_sq_reading (D : WeightedDesign m k) (y : Fin k → ℝ) :
    ∑ c, D.weight c * (D.atom c ⬝ᵥ y) ^ 2 = y ⬝ᵥ y := by
  have hexpand : ∑ c, D.weight c * (D.atom c ⬝ᵥ y) ^ 2
      = y ⬝ᵥ ((∑ c, D.weight c • atomMatrix (D.atom c)) *ᵥ y) := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    exact (Finset.sum_congr rfl fun c _ => by
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]).symm
  rw [hexpand, D.isParseval, Matrix.one_mulVec]

/-- **The deficiency budget at a probe.**  The full-selection gap reads, at
every probe, as the deficiency-weighted sum of the same squared readings. -/
theorem quadForm_univGap_eq_sum (D : WeightedDesign m k) (y : Fin k → ℝ) :
    y ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ y)
      = ∑ c, (1 - D.weight c) * (D.atom c ⬝ᵥ y) ^ 2 := by
  rw [univGap_eq_deficiencySum, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun c _ => by
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]

/-- The unweighted squared readings are strictly positive at a nonzero probe:
the weighted ones already recover the probe energy, and no weight exceeds one.

`Gtz.weight_le_one` already exists twice in the tree (`Reduction.FrameDropDescent`
and `Quantitative.BalancedCollections`), so the one-line weight bound is inlined
here rather than restated a third time. -/
theorem sum_sq_reading_pos (D : WeightedDesign m k) {y : Fin k → ℝ} (hy : y ≠ 0) :
    0 < ∑ c, (D.atom c ⬝ᵥ y) ^ 2 := by
  have hwle : ∀ c : Fin m, D.weight c ≤ 1 := fun c => by
    have h := Finset.single_le_sum (f := D.weight)
      (fun d _ => (D.weight_pos d).le) (Finset.mem_univ c)
    rwa [D.weight_sum_one] at h
  have hyy : 0 < y ⬝ᵥ y := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    have hpos : 0 < y i * y i := mul_self_pos.mpr hi
    simpa [dotProduct] using
      Finset.sum_pos' (fun j _ => mul_self_nonneg (y j)) ⟨i, Finset.mem_univ i, hpos⟩
  have hle : ∑ c, D.weight c * (D.atom c ⬝ᵥ y) ^ 2 ≤ ∑ c, (D.atom c ⬝ᵥ y) ^ 2 :=
    Finset.sum_le_sum fun c _ => by
      nlinarith [hwle c, sq_nonneg (D.atom c ⬝ᵥ y)]
  rw [sum_weight_mul_sq_reading] at hle
  linarith

/-- **The half-weight surplus.**  When every weight is strictly below one half,
twice the deficiency budget strictly exceeds the unweighted reading sum at every
nonzero probe. -/
theorem sum_sq_reading_lt_two_mul_deficiency (D : WeightedDesign m k)
    {y : Fin k → ℝ} (hy : y ≠ 0) (hw : ∀ c, D.weight c < 1 / 2) :
    ∑ c, (D.atom c ⬝ᵥ y) ^ 2
      < 2 * ∑ c, (1 - D.weight c) * (D.atom c ⬝ᵥ y) ^ 2 := by
  have hex : ∃ c, 0 < (D.atom c ⬝ᵥ y) ^ 2 := by
    by_contra hno
    push Not at hno
    have : ∑ c, (D.atom c ⬝ᵥ y) ^ 2 ≤ 0 :=
      Finset.sum_nonpos fun c _ => hno c
    linarith [sum_sq_reading_pos D hy]
  obtain ⟨c₀, hc₀⟩ := hex
  have hgap : 0 < ∑ c, (1 - 2 * D.weight c) * (D.atom c ⬝ᵥ y) ^ 2 := by
    refine Finset.sum_pos' (fun c _ => ?_) ⟨c₀, Finset.mem_univ c₀, ?_⟩
    · nlinarith [sq_nonneg (D.atom c ⬝ᵥ y), hw c]
    · nlinarith [hc₀, hw c₀]
  have hrw : ∑ c, (1 - 2 * D.weight c) * (D.atom c ⬝ᵥ y) ^ 2
      = 2 * (∑ c, (1 - D.weight c) * (D.atom c ⬝ᵥ y) ^ 2)
        - ∑ c, (D.atom c ⬝ᵥ y) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  linarith [hrw ▸ hgap]

/-- **THE COMPLEMENTARY-PAIR EXCLUSION.**  If a label set overloads a probe —
its readings reach the deficiency budget — then its complement does not, provided
every weight is strictly below one half.  Adding the two overload inequalities
would make the unweighted reading sum dominate twice the deficiency budget,
which the half-weight surplus forbids.

At `(6,3)` this pairs the twenty triples into ten complementary pairs and caps
the number failing at any single direction by ten. -/
theorem not_both_overload_of_weight_lt_half (D : WeightedDesign m k)
    (T : Finset (Fin m)) {y : Fin k → ℝ} (hy : y ≠ 0)
    (hw : ∀ c, D.weight c < 1 / 2)
    (hT : ∑ c, (1 - D.weight c) * (D.atom c ⬝ᵥ y) ^ 2
            ≤ ∑ c ∈ T, (D.atom c ⬝ᵥ y) ^ 2) :
    ∑ c ∈ Tᶜ, (D.atom c ⬝ᵥ y) ^ 2
      < ∑ c, (1 - D.weight c) * (D.atom c ⬝ᵥ y) ^ 2 := by
  by_contra hcon
  push Not at hcon
  have hsplit : ∑ c ∈ T, (D.atom c ⬝ᵥ y) ^ 2 + ∑ c ∈ Tᶜ, (D.atom c ⬝ᵥ y) ^ 2
      = ∑ c, (D.atom c ⬝ᵥ y) ^ 2 := Finset.sum_add_sum_compl T _
  linarith [sum_sq_reading_lt_two_mul_deficiency D hy hw, hsplit, hT, hcon]

/-- **The common-direction corollary.**  When every weight is below one half, no
single direction can overload a label set and its complement at once, so the
twenty triples of `(6,3)` cannot all fail at one direction. -/
theorem exists_not_overload_of_weight_lt_half (D : WeightedDesign m k)
    (T : Finset (Fin m)) {y : Fin k → ℝ} (hy : y ≠ 0)
    (hw : ∀ c, D.weight c < 1 / 2) :
    ∑ c ∈ T, (D.atom c ⬝ᵥ y) ^ 2
        < ∑ c, (1 - D.weight c) * (D.atom c ⬝ᵥ y) ^ 2
      ∨ ∑ c ∈ Tᶜ, (D.atom c ⬝ᵥ y) ^ 2
        < ∑ c, (1 - D.weight c) * (D.atom c ⬝ᵥ y) ^ 2 := by
  by_cases hT : ∑ c, (1 - D.weight c) * (D.atom c ⬝ᵥ y) ^ 2
      ≤ ∑ c ∈ T, (D.atom c ⬝ᵥ y) ^ 2
  · exact Or.inr (not_both_overload_of_weight_lt_half D T hy hw hT)
  · exact Or.inl (not_le.mp hT)

end Gtz
