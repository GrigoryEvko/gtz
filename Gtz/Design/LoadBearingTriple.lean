/-
# The load-bearing triple

`Gtz.card_le_rank_of_forall_pivot_univ_ge_one` caps the labels of full-selection
pivot one or more by the rank.  This module proves that AT the cap the selection
those labels form is positive definite.

A label of full-selection pivot one or more cannot be erased from the full
selection.  The theorem therefore says: the labels you cannot erase are exactly
the ones you keep.

The proof prices the omitted energy twice and never diagonalizes.

* The deficiency budget spends the rank exactly, and each capped label spends at
  least its own deficiency, so the labels OUTSIDE the cap carry
  deficiency-weighted pivot mass at most the weight the cap holds.
* Cauchy-Schwarz through the resolvent prices every omitted squared reading by
  that label's own pivot times the probe energy, so the outside energy is at
  most that same weight times the probe energy.
* Weighted Cauchy-Schwarz collapses the omitted combination against the outside
  energy, and testing at the dual probe turns the resulting uniform square bound
  into a bound on the inverse form.
* The residual is one weight comparison: the cap's weight is strictly below
  every outside deficiency, because at least two labels stay outside and every
  weight is strictly positive.

No square root occurs in a statement or in a proof, no spectral theorem is used,
and no chart is built.  Everything is generic in the size and the rank.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.TraceIdentity
import Gtz.Design.DowndateInterlacing
import Gtz.Design.ComplementLeverageLaw
import Gtz.Design.PivotGramIdempotent

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. Weighted Cauchy-Schwarz, square-root free -/

/-- **Weighted Cauchy-Schwarz.**  The per-label hypothesis of
`Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` holds with EQUALITY here, so the
weights cancel and no square root enters the proof. -/
theorem sq_sum_mul_le_weighted (S : Finset (Fin m)) (y t d : Fin m → ℝ)
    (hd : ∀ c ∈ S, 0 < d c) :
    (∑ c ∈ S, y c * t c) ^ 2
      ≤ (∑ c ∈ S, y c ^ 2 / d c) * ∑ c ∈ S, d c * t c ^ 2 := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S (fun c hc => ?_) (fun c hc => ?_)
    (fun c hc => ?_)
  · exact div_nonneg (sq_nonneg _) (hd c hc).le
  · exact mul_nonneg (hd c hc).le (sq_nonneg _)
  · have hdc : d c ≠ 0 := (hd c hc).ne'
    refine le_of_eq ?_
    field_simp

/-! ## 2. The omitted energy is priced by its own pivot mass -/

/-- **The energy bound.**  Cauchy-Schwarz through the resolvent prices each
squared reading by that label's full-selection pivot times the probe energy, so
a deficiency-weighted sum of readings is priced by the same weighted pivot sum. -/
theorem sum_deficiency_mul_sq_reading_le (D : WeightedDesign m k) (hm : 2 ≤ m)
    (S : Finset (Fin m)) (q : Fin k → ℝ) :
    ∑ c ∈ S, (1 - D.weight c) * (D.atom c ⬝ᵥ q) ^ 2
      ≤ (∑ c ∈ S, (1 - D.weight c) * pivot D Finset.univ c)
        * (q ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ q)) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun c _ => ?_
  have hpr := pivot_prices_overlap (posDef_fullExcess D hm) (fullExcess_transpose D)
    (D.atom c) q
  rw [← pivot_eq_dot] at hpr
  calc (1 - D.weight c) * (D.atom c ⬝ᵥ q) ^ 2
      ≤ (1 - D.weight c)
        * (pivot D Finset.univ c * (q ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ q))) :=
        mul_le_mul_of_nonneg_left hpr (deficiency_pos D hm c).le
    _ = (1 - D.weight c) * pivot D Finset.univ c
        * (q ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ q)) := by ring

/-! ## 3. The budget outside the cap -/

/-- **The outside budget.**  When exactly `k` labels carry full-selection pivot
one or more, the labels outside them carry deficiency-weighted pivot mass at
most the weight the cap holds. -/
theorem sum_deficiency_mul_pivot_compl_le (D : WeightedDesign m k) (hm : 2 ≤ m)
    (B : Finset (Fin m)) (hB : ∀ c ∈ B, 1 ≤ pivot D Finset.univ c)
    (hcard : B.card = k) :
    ∑ c ∈ Bᶜ, (1 - D.weight c) * pivot D Finset.univ c ≤ ∑ c ∈ B, D.weight c := by
  have hbudget := sum_deficiency_mul_pivot_univ D hm
  have hsplit : (∑ c ∈ B, (1 - D.weight c) * pivot D Finset.univ c)
      + ∑ c ∈ Bᶜ, (1 - D.weight c) * pivot D Finset.univ c = (k : ℝ) := by
    rw [Finset.sum_add_sum_compl B (fun c => (1 - D.weight c) * pivot D Finset.univ c)]
    exact hbudget
  have hBspend : ∑ c ∈ B, (1 - D.weight c)
      ≤ ∑ c ∈ B, (1 - D.weight c) * pivot D Finset.univ c := by
    refine Finset.sum_le_sum fun c hc => ?_
    nlinarith [deficiency_pos D hm c, hB c hc]
  have hBsum : ∑ c ∈ B, (1 - D.weight c) = (k : ℝ) - ∑ c ∈ B, D.weight c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
  linarith

/-! ## 4. A uniform square bound caps the inverse form -/

/-- **The dual probe.**  A square bound that holds at EVERY probe becomes a
bound on the inverse form, by testing it at the dual probe. -/
theorem inverseForm_le_of_forall_sq_le {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosDef)
    (v : Fin k → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ q : Fin k → ℝ, (v ⬝ᵥ q) ^ 2 ≤ C * (q ⬝ᵥ (E *ᵥ q))) :
    v ⬝ᵥ (E⁻¹ *ᵥ v) ≤ C := by
  have hdet : IsUnit E.det := isUnit_iff_ne_zero.mpr (ne_of_gt hE.det_pos)
  have hEq : E *ᵥ (E⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv E hdet, Matrix.one_mulVec]
  have hcomm : (E⁻¹ *ᵥ v) ⬝ᵥ v = v ⬝ᵥ (E⁻¹ *ᵥ v) := dotProduct_comm _ _
  have hkey := h (E⁻¹ *ᵥ v)
  rw [hEq, hcomm] at hkey
  have hnn : 0 ≤ v ⬝ᵥ (E⁻¹ *ᵥ v) := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hE.inv).2 hv
      simp only [star_trivial] at hpos
      exact hpos.le
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · linarith
  · nlinarith [hkey, hpos]

/-! ## 5. The load-bearing triple -/

/-- **THE LOAD-BEARING TRIPLE.**  When exactly `k` labels carry a full-selection
pivot of one or more, those labels form a positive definite selection.

A label of pivot one or more cannot be erased from the full selection, so this
says the labels you cannot erase are exactly the ones you keep.  Generic in the
size and the rank, and it needs two labels to stay outside the cap. -/
theorem posDef_subsetSum_of_card_pivot_univ_ge_one (D : WeightedDesign m k)
    (hm : k + 2 ≤ m) (B : Finset (Fin m))
    (hB : ∀ c ∈ B, 1 ≤ pivot D Finset.univ c) (hcard : B.card = k) :
    (subsetSum D B - 1).PosDef := by
  have hm2 : 2 ≤ m := by omega
  have hK := posDef_fullExcess D hm2
  have hstrict : ∀ c ∈ Bᶜ, ∑ j ∈ B, D.weight j < 1 - D.weight c := by
    intro c hc
    have hcB : c ∉ B := Finset.mem_compl.mp hc
    have hins : ∑ j ∈ insert c B, D.weight j = D.weight c + ∑ j ∈ B, D.weight j :=
      Finset.sum_insert hcB
    have hcard' : (insert c B).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hcB, hcard]
    obtain ⟨e, he⟩ : ∃ e, e ∉ insert c B := by
      by_contra hcon
      push Not at hcon
      have huniv : insert c B = Finset.univ := Finset.eq_univ_of_forall hcon
      rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard'
      omega
    have hlt : ∑ j ∈ insert c B, D.weight j < ∑ j ∈ Finset.univ, D.weight j :=
      Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ e) he
        (D.weight_pos e) (fun j _ _ => (D.weight_pos j).le)
    rw [D.weight_sum_one, hins] at hlt
    linarith
  have hmain : ∀ y : Fin m → ℝ, (∃ c ∈ Bᶜ, y c ≠ 0) →
      0 < designComplementForm D Bᶜ y := by
    intro y hy
    have hQnn : 0 ≤ ∑ c ∈ Bᶜ, y c ^ 2 / (1 - D.weight c) :=
      Finset.sum_nonneg fun c _ => div_nonneg (sq_nonneg _) (deficiency_pos D hm2 c).le
    have hsnn : 0 ≤ ∑ j ∈ B, D.weight j :=
      Finset.sum_nonneg fun j _ => (D.weight_pos j).le
    have hfa : ∀ q : Fin k → ℝ,
        (complementCombination D Bᶜ y ⬝ᵥ q) ^ 2
          ≤ ((∑ c ∈ Bᶜ, y c ^ 2 / (1 - D.weight c)) * ∑ j ∈ B, D.weight j)
            * (q ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ q)) := by
      intro q
      have henergy : 0 ≤ q ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ q) := by
        rcases eq_or_ne q 0 with rfl | hq
        · simp
        · have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hK).2 hq
          simp only [star_trivial] at hpos
          exact hpos.le
      rw [dotProduct_complementCombination]
      calc (∑ c ∈ Bᶜ, y c * (D.atom c ⬝ᵥ q)) ^ 2
          ≤ (∑ c ∈ Bᶜ, y c ^ 2 / (1 - D.weight c))
            * ∑ c ∈ Bᶜ, (1 - D.weight c) * (D.atom c ⬝ᵥ q) ^ 2 :=
            sq_sum_mul_le_weighted Bᶜ y (fun c => D.atom c ⬝ᵥ q)
              (fun c => 1 - D.weight c) (fun c _ => deficiency_pos D hm2 c)
        _ ≤ (∑ c ∈ Bᶜ, y c ^ 2 / (1 - D.weight c))
            * ((∑ c ∈ Bᶜ, (1 - D.weight c) * pivot D Finset.univ c)
              * (q ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ q))) :=
            mul_le_mul_of_nonneg_left (sum_deficiency_mul_sq_reading_le D hm2 Bᶜ q) hQnn
        _ ≤ (∑ c ∈ Bᶜ, y c ^ 2 / (1 - D.weight c))
            * ((∑ j ∈ B, D.weight j)
              * (q ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ q))) := by
            refine mul_le_mul_of_nonneg_left ?_ hQnn
            exact mul_le_mul_of_nonneg_right
              (sum_deficiency_mul_pivot_compl_le D hm2 B hB hcard) henergy
        _ = ((∑ c ∈ Bᶜ, y c ^ 2 / (1 - D.weight c)) * ∑ j ∈ B, D.weight j)
            * (q ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ q)) := by ring
    have hbound := inverseForm_le_of_forall_sq_le hK (complementCombination D Bᶜ y)
      (mul_nonneg hQnn hsnn) hfa
    have hgap : (∑ c ∈ Bᶜ, y c ^ 2 / (1 - D.weight c)) * (∑ j ∈ B, D.weight j)
        < ∑ c ∈ Bᶜ, y c ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_lt_sum (fun c hc => ?_) ?_
      · have hd := deficiency_pos D hm2 c
        have hs := (hstrict c hc).le
        rw [div_mul_eq_mul_div, div_le_iff₀ hd]
        nlinarith [sq_nonneg (y c)]
      · obtain ⟨c, hc, hyc⟩ := hy
        refine ⟨c, hc, ?_⟩
        have hd := deficiency_pos D hm2 c
        have hlt := hstrict c hc
        have hy2 : 0 < y c ^ 2 := by positivity
        rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
        nlinarith
    rw [designComplementForm]
    linarith
  have hres := (posDef_complementGap_iff_designComplementForm_pos D Bᶜ hK).mpr hmain
  rwa [compl_compl] at hres

/-- **The load-bearing triple at `(6,3)`.**  Three labels of full-selection pivot
one or more form a positive definite triple. -/
theorem posDef_subsetSum_of_cardThree_pivot_univ_ge_one (D : WeightedDesign 6 3)
    (B : Finset (Fin 6)) (hB : ∀ c ∈ B, 1 ≤ pivot D Finset.univ c)
    (hcard : B.card = 3) :
    (subsetSum D B - 1).PosDef :=
  posDef_subsetSum_of_card_pivot_univ_ge_one D (by norm_num) B hB hcard

/-- **The escape at the cap.**  If three labels carry full-selection pivot one or
more, some card-three selection is positive definite -- the conclusion every
on-path cell of the campaign asks for. -/
theorem exists_cardThree_posDef_of_cardThree_pivot_ge_one (D : WeightedDesign 6 3)
    (B : Finset (Fin 6)) (hB : ∀ c ∈ B, 1 ≤ pivot D Finset.univ c)
    (hcard : B.card = 3) :
    ∃ T : Finset (Fin 6), T.card = 3 ∧ (subsetSum D T - 1).PosDef :=
  ⟨B, hcard, posDef_subsetSum_of_cardThree_pivot_univ_ge_one D B hB hcard⟩

/-- **The dichotomy at `(6,3)`.**  Either some label outside a given card-three
set drops its pivot below one, or that set is already a positive definite
triple.  Stated as the contrapositive the theorem discharges. -/
theorem exists_pivot_lt_one_or_posDef (D : WeightedDesign 6 3) (B : Finset (Fin 6))
    (hcard : B.card = 3) :
    (∃ c ∈ B, pivot D Finset.univ c < 1) ∨ (subsetSum D B - 1).PosDef := by
  by_cases hB : ∀ c ∈ B, 1 ≤ pivot D Finset.univ c
  · exact Or.inr (posDef_subsetSum_of_cardThree_pivot_univ_ge_one D B hB hcard)
  · push Not at hB
    exact Or.inl hB

end Gtz
