/-
# The refusal budget of a corner: twenty triples collapse to ten

A corank-two corner carries twenty triples, and a tie must refuse all of them.
This module shows that ten of the twenty are refused FOR FREE, by the corner
equation alone and with no tie hypothesis:

* the dominator `C` itself, whose gap `lam • uuᵀ` has rank at most one and
  therefore vanishing determinant
  (`Gtz.corner_self_not_posDef`);
* the nine TWO-INSIDE triples, which meet `C` in exactly two labels, through
  the landed `Gtz.corner_twoInside_det_nonpos`
  (`Gtz.corner_twoInside_not_posDef`).

The consequence is the budget itself
(`Gtz.corner_posDef_triple_inter_le_one`): at a corner, EVERY strictly
dominating triple meets the dominator in at most one label.  So the ten
conditions that can carry a tie are the nine informative triples and the
complement, and a certificate never has to consult the other ten.

[MEASURED, 745,691 generic corners: the dominating triple is the complement at
88.54 percent and an informative triple at 11.46 percent.  A two-inside triple
dominates at 0.00 percent — zero exceptions, which is this file's content.]
-/
import Gtz.Wave.CornerParityLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The dominator of a corner never dominates strictly -/

/-- **A CORNER NEVER DOMINATES STRICTLY.**  The gap of the dominator is a
multiple of a rank-one atom, so its determinant vanishes, while a positive
definite matrix has positive determinant. -/
theorem corner_self_not_posDef (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ¬ (subsetSum D C - 1).PosDef := by
  intro hpd
  have hatom : (atomMatrix u).det = 0 := by
    simp only [Matrix.det_fin_three, atomMatrix, Matrix.vecMulVec_apply]
    ring
  have hdet : (subsetSum D C - 1).det = 0 := by
    rw [hgap, Matrix.det_smul, hatom, mul_zero]
  exact absurd hpd.det_pos (by rw [hdet]; exact lt_irrefl 0)

/-! ## 2. A two-inside triple never dominates strictly -/

/-- **A TWO-INSIDE TRIPLE NEVER DOMINATES STRICTLY.**  The landed tie leg of a
two-inside triple is nonpositive, and a positive definite gap has positive
determinant.  No tie hypothesis: the corner equation alone. -/
theorem corner_twoInside_not_posDef (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y outLbl : Fin m} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y)
    (hxOut : x ≠ outLbl) (hyOut : y ≠ outLbl) :
    ¬ (subsetSum D ({x, y, outLbl} : Finset (Fin m)) - 1).PosDef := by
  intro hpd
  have hdet := corner_twoInside_det_nonpos D C hcard hlam hunit hgap hx hy hxy
    hxOut hyOut
  exact absurd hpd.det_pos (not_lt.mpr hdet)

/-! ## 3. The budget -/

/-- **THE REFUSAL BUDGET OF A CORNER.**  At a corner, every strictly dominating
triple meets the dominator in AT MOST ONE label.  The three-label case is the
dominator itself, whose gap is rank one; the two-label case is a two-inside
triple, whose tie leg is nonpositive.  So of the twenty triples of a `(6,3)`
design only the nine informative ones and the complement can carry a tie, and
a certificate never has to consult the other ten. -/
theorem corner_posDef_triple_inter_le_one (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {T : Finset (Fin m)} (hT : T.card = 3)
    (hpd : (subsetSum D T - 1).PosDef) :
    (T ∩ C).card ≤ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  -- two or three shared labels
  rcases Nat.lt_or_ge (T ∩ C).card 3 with hlt | hge
  · -- exactly two shared labels: a two-inside triple
    have hcard2 : (T ∩ C).card = 2 := by omega
    obtain ⟨x, y, hxy, hpair⟩ := Finset.card_eq_two.mp hcard2
    have hxmem : x ∈ T ∩ C := by rw [hpair]; simp
    have hymem : y ∈ T ∩ C := by rw [hpair]; simp
    have hxT := (Finset.mem_inter.mp hxmem).1
    have hxC := (Finset.mem_inter.mp hxmem).2
    have hyT := (Finset.mem_inter.mp hymem).1
    have hyC := (Finset.mem_inter.mp hymem).2
    have hsub : ({x, y} : Finset (Fin m)) ⊆ T := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact hxT
      · rw [Finset.mem_singleton] at hz'; exact hz' ▸ hyT
    have hxy2 : ({x, y} : Finset (Fin m)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    have hinter : ({x, y} : Finset (Fin m)) ∩ T = {x, y} :=
      Finset.inter_eq_left.mpr hsub
    have hdiff : (T \ ({x, y} : Finset (Fin m))).card = 1 := by
      rw [Finset.card_sdiff, hinter, hT, hxy2]
    obtain ⟨outLbl, hout⟩ := Finset.card_eq_one.mp hdiff
    have houtmem : outLbl ∈ T \ ({x, y} : Finset (Fin m)) := by
      rw [hout]; exact Finset.mem_singleton_self outLbl
    have houtT := (Finset.mem_sdiff.mp houtmem).1
    have houtNot := (Finset.mem_sdiff.mp houtmem).2
    have hxOut : x ≠ outLbl := fun h => houtNot (by rw [← h]; simp)
    have hyOut : y ≠ outLbl := fun h => houtNot (by rw [← h]; simp)
    have hyo2 : ({y, outLbl} : Finset (Fin m)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hyOut]), Finset.card_singleton]
    have hcard3 : ({x, y, outLbl} : Finset (Fin m)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxOut]), hyo2]
    have hsub3 : ({x, y, outLbl} : Finset (Fin m)) ⊆ T := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hxT
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hyT
      · rw [Finset.mem_singleton] at hz; exact hz ▸ houtT
    have hTeq : ({x, y, outLbl} : Finset (Fin m)) = T :=
      Finset.eq_of_subset_of_card_le hsub3 (by rw [hT, hcard3])
    rw [← hTeq] at hpd
    exact corner_twoInside_not_posDef D C hcard hlam hunit hgap hxC hyC hxy
      hxOut hyOut hpd
  · -- all three labels shared: `T = C`
    have hle : (T ∩ C).card ≤ 3 := by
      rw [← hT]; exact Finset.card_le_card Finset.inter_subset_left
    have heq3 : (T ∩ C).card = 3 := le_antisymm hle hge
    have h1 : T ∩ C = T :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hT, heq3])
    have h2 : T ⊆ C := by rw [← h1]; exact Finset.inter_subset_right
    have hTC : T = C := Finset.eq_of_subset_of_card_le h2 (by rw [hcard, hT])
    rw [hTC] at hpd
    exact corner_self_not_posDef D C hgap hpd

end Gtz
