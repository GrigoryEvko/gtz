/-
# Sanity: definition-pinning instances (all sorry-free, kept that way)

Definitions can lie. This module keeps them honest with small fully-proved facts:

* `posSemidef_atomMatrix` — the atoms are genuinely PSD, so `Dominates` is a
  genuine Loewner statement, not a vacuous one;
* `Dominates.mono` — domination is monotone in the subset, as the math demands
  (S_C is a sum of PSD atoms);
* `unitDesign` / `gtzWeighted_one_one` — the design structure is satisfiable and
  the problem statement composes end-to-end at the smallest instance (m = k = 1,
  where GTZ is the trivial pigeonhole).

If a refactor ever breaks one of these, the definitions drifted from the
mathematics — treat that as an alarm, not an inconvenience.
-/
import Mathlib
import Gtz.Basic

namespace Gtz

variable {m k : ℕ}

/-- Each atom g gᵀ is PSD (over ℝ, `star g = g`, so this is Mathlib's
`posSemidef_vecMulVec_self_star` on the nose). -/
theorem posSemidef_atomMatrix (g : Fin k → ℝ) : (atomMatrix g).PosSemidef := by
  simpa [atomMatrix] using Matrix.posSemidef_vecMulVec_self_star g

/-- Domination is monotone under enlarging the subset: adding PSD atoms cannot
destroy S_C ⪰ I. -/
theorem Dominates.mono {D : WeightedDesign m k} {C C' : Finset (Fin m)}
    (hsub : C ⊆ C') (h : Dominates D C) : Dominates D C' := by
  have hsplit : subsetSum D C' - 1
      = (subsetSum D C - 1) + ∑ c ∈ C' \ C, atomMatrix (D.atom c) := by
    unfold subsetSum
    rw [← Finset.sum_sdiff hsub]
    abel
  have hrest : (∑ c ∈ C' \ C, atomMatrix (D.atom c)).PosSemidef :=
    Matrix.posSemidef_sum (C' \ C) fun c _ => posSemidef_atomMatrix (D.atom c)
  rw [Dominates, hsplit]
  exact h.add hrest

/-- The smallest design: one unit atom in ℝ¹ with full weight. -/
def unitDesign : WeightedDesign 1 1 where
  atom := fun _ _ => 1
  weight := fun _ => 1
  weight_pos := fun _ => one_pos
  weight_sum_one := by simp
  isParseval := by
    have hA : atomMatrix (fun _ : Fin 1 => (1 : ℝ)) = 1 := by
      ext i j
      have hi : i = 0 := Subsingleton.elim i 0
      have hj : j = 0 := Subsingleton.elim j 0
      subst hi; subst hj
      simp [atomMatrix, Matrix.vecMulVec_apply]
    simp [hA]

/-- GTZ at (m, k) = (1, 1), end-to-end: the definitions compose and the smallest
instance is a theorem (Parseval forces the single atom to leverage exactly 1). -/
theorem gtzWeighted_one_one : GtzWeighted 1 1 := by
  intro D
  refine ⟨Finset.univ, by simp, ?_⟩
  have hw : D.weight 0 = 1 := by
    have hsum := D.weight_sum_one
    simpa [Fin.sum_univ_one] using hsum
  have hA : atomMatrix (D.atom 0) = 1 := by
    have hp := D.isParseval
    rw [Fin.sum_univ_one, hw, one_smul] at hp
    exact hp
  have hS : subsetSum D Finset.univ = 1 := by
    simpa [subsetSum, Fin.sum_univ_one] using hA
  show (subsetSum D Finset.univ - 1).PosSemidef
  rw [hS, sub_self]
  exact Matrix.PosSemidef.zero

end Gtz
