/-
# The projection tax of a tie: refusals tax the weights at the block floors

The Gram-side projection of a design (`Gtz.projectionOfDesign`, the `m × m`
rank-`k` projection `VVᵀ` of the scaled frame) decides domination through the
landed congruence: a triple dominates strictly exactly when its projection
block beats the weight diagonal.  This module prices that decision:

* a triple whose projection block carries a quadratic floor `lam` and whose
  three weights sit below `lam` DOMINATES STRICTLY — the first polynomial
  strict-dominator producer of the arm;
* at a tie every refused triple therefore CONTAINS A TAXED ATOM: some member
  weight reaches the block floor;
* the taxed atoms hit every triple, so at most TWO atoms of a tie are light
  for a uniform floor, at every size;
* the weight simplex caps the total tax: a uniform floor obeys
  `lam ≤ 1/(m − 2)`.  At `(6,3)` the tie caps every uniform projection floor
  at `1/4`, while `(5,3)` only forces `1/3` — the size enters as the
  cardinality of a hitting set of all triples.

The floors connect to the arm's rigidity currency: the block determinant is
`t_at_bt_c·[abc]²`, and the pair minors of the projection are the weighted
cross wedges — a parallel pair makes its four blocks floorless.  The tax law
is the first exact step of the K0 target shape: refusal margins against the
minimum pair minor.
-/
import Gtz.Quantitative.ProjectionBasisCoordinates
import Gtz.Certificates.ResidueDissolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The strict-dominator producer -/

/-- The projection block of a pick, minus the weight diagonal. -/
theorem projectionWeightGap_transpose (D : WeightedDesign m 3)
    (pick : Fin 3 → Fin m) :
    ((projectionOfDesign D).submatrix pick pick
        - Matrix.diagonal (fun slot => D.weight (pick slot)))ᵀ
      = (projectionOfDesign D).submatrix pick pick
        - Matrix.diagonal (fun slot => D.weight (pick slot)) := by
  rw [Matrix.transpose_sub, Matrix.transpose_submatrix, Matrix.diagonal_transpose,
    projectionOfDesign_transpose]

/-- **THE LIGHT-TRIPLE PRODUCER.**  A triple whose projection block carries
the quadratic floor `lam` and whose three weights all sit below `lam`
dominates STRICTLY.  Polynomial data in, strict dominator out — no
eigenvalues and no tie hypothesis. -/
theorem posDef_subsetSum_of_projectionFloor_light (D : WeightedDesign m 3)
    (pick : Fin 3 → Fin m) (hinj : Function.Injective pick) {lam : ℝ}
    (hfloor : ∀ ξ : Fin 3 → ℝ, lam * (ξ ⬝ᵥ ξ) ≤
      ξ ⬝ᵥ ((projectionOfDesign D).submatrix pick pick *ᵥ ξ))
    (hlight : ∀ slot, D.weight (pick slot) < lam) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef := by
  rw [posDef_subsetSum_iff_posDef_projectionBlock D pick hinj]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (projectionWeightGap_transpose D pick), fun ξ hξ => ?_⟩
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
  have hdiag : ξ ⬝ᵥ (Matrix.diagonal (fun slot => D.weight (pick slot)) *ᵥ ξ)
      = ∑ slot, D.weight (pick slot) * ξ slot ^ 2 := by
    simp only [Matrix.mulVec_diagonal, dotProduct]
    exact Finset.sum_congr rfl fun slot _ => by ring
  obtain ⟨slot₀, hslot₀⟩ := Function.ne_iff.mp hξ
  have hstrict : ∑ slot, D.weight (pick slot) * ξ slot ^ 2
      < ∑ slot, lam * ξ slot ^ 2 := by
    refine Finset.sum_lt_sum (fun slot _ => ?_) ⟨slot₀, Finset.mem_univ _, ?_⟩
    · exact mul_le_mul_of_nonneg_right (hlight slot).le (sq_nonneg _)
    · have hpos : 0 < ξ slot₀ ^ 2 := by
        have : ξ slot₀ ≠ 0 := hslot₀
        positivity
      exact mul_lt_mul_of_pos_right (hlight slot₀) hpos
  have hnorm : ∑ slot, lam * ξ slot ^ 2 = lam * (ξ ⬝ᵥ ξ) := by
    rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun slot _ => by ring
  have hfl := hfloor ξ
  rw [hdiag]
  linarith [hstrict, hnorm ▸ hstrict, hfl]

/-! ## 2. The tax of a refusal -/

/-- **A refused floored triple carries a taxed atom.**  When the projection
block has the floor `lam` and the triple does not dominate strictly, some
member weight reaches `lam`. -/
theorem exists_heavy_slot_of_refused (D : WeightedDesign m 3)
    (pick : Fin 3 → Fin m) (hinj : Function.Injective pick) {lam : ℝ}
    (hfloor : ∀ ξ : Fin 3 → ℝ, lam * (ξ ⬝ᵥ ξ) ≤
      ξ ⬝ᵥ ((projectionOfDesign D).submatrix pick pick *ᵥ ξ))
    (hrefused : ¬ (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef) :
    ∃ slot, lam ≤ D.weight (pick slot) := by
  by_contra hcon
  push Not at hcon
  exact hrefused (posDef_subsetSum_of_projectionFloor_light D pick hinj hfloor hcon)

set_option linter.unusedSimpArgs false in
/-- Three distinct labels give an injective slot map. -/
theorem injective_tripleSlots {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : Function.Injective ![a, b, c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at hij ⊢ <;>
    first
      | rfl
      | exact absurd hij hab
      | exact absurd hij hac
      | exact absurd hij hbc
      | exact absurd hij.symm hab
      | exact absurd hij.symm hac
      | exact absurd hij.symm hbc

/-- The image of a triple-slot map is the explicit triple. -/
theorem image_tripleSlots (a b c : Fin m) :
    Finset.image ![a, b, c] Finset.univ = {a, b, c} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨slot, rfl⟩
    fin_cases slot <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-! ## 3. The light set of a tie has at most two atoms, every size -/

set_option linter.unusedSimpArgs false in
/-- **AT MOST TWO ATOMS OF A TIE ARE LIGHT.**  For a uniform projection
floor `lam` over all triples, a tie keeps the set `{c : t_c < lam}` at
cardinality two or less: three light atoms would form a strictly dominating
triple.  The statement holds at EVERY size `(m, 3)`. -/
theorem card_light_le_two_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    {lam : ℝ}
    (hfloor : ∀ pick : Fin 3 → Fin m, Function.Injective pick →
      ∀ ξ : Fin 3 → ℝ, lam * (ξ ⬝ᵥ ξ) ≤
        ξ ⬝ᵥ ((projectionOfDesign D).submatrix pick pick *ᵥ ξ)) :
    (Finset.univ.filter fun c => D.weight c < lam).card ≤ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨light₃, hsub, hcard₃⟩ := Finset.exists_subset_card_eq hcon
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hcard₃
  have hlightmem : ∀ x ∈ light₃, D.weight x < lam := fun x hx =>
    (Finset.mem_filter.mp (hsub hx)).2
  have hinj := injective_tripleSlots hab hac hbc
  have hpd := posDef_subsetSum_of_projectionFloor_light D ![a, b, c] hinj
    (hfloor ![a, b, c] hinj) (fun slot => by
      fin_cases slot <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons] <;>
        exact hlightmem _ (by rw [hset]; simp)
      )
  have hcard : (Finset.image ![a, b, c] Finset.univ).card = 3 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  exact htie.2 _ hcard hpd

/-! ## 4. The tax cap: a uniform floor pays `1/(m − 2)` -/

/-- **THE TAX CAP.**  At a tie with a uniform projection floor `lam`, at
least `m − 2` atoms are taxed at `lam` each, and the weight simplex pays at
most one:  `(m − 2)·lam ≤ 1`.  The size enters as the cardinality of a
hitting set of all triples. -/
theorem uniform_floor_tax_cap_of_isTie (D : WeightedDesign m 3)
    (htie : IsTie D) {lam : ℝ}
    (hfloor : ∀ pick : Fin 3 → Fin m, Function.Injective pick →
      ∀ ξ : Fin 3 → ℝ, lam * (ξ ⬝ᵥ ξ) ≤
        ξ ⬝ᵥ ((projectionOfDesign D).submatrix pick pick *ᵥ ξ)) :
    ((m : ℝ) - 2) * lam ≤ 1 := by
  classical
  have hm3 : 3 ≤ m := by
    obtain ⟨C, hcard, -⟩ := htie.1
    calc 3 = C.card := hcard.symm
      _ ≤ (Finset.univ : Finset (Fin m)).card :=
          Finset.card_le_card (Finset.subset_univ C)
      _ = m := by rw [Finset.card_univ, Fintype.card_fin]
  have hm3r : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
  rcases le_or_gt lam 0 with hlam | hlam
  · nlinarith
  set light := Finset.univ.filter fun c => D.weight c < lam with hlight
  have hcardlight := card_light_le_two_of_isTie D htie hfloor
  have hheavycard : (m : ℝ) - 2 ≤ ((Finset.univ \ light).card : ℝ) := by
    have h1 : (Finset.univ \ light).card = m - light.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Fintype.card_fin]
    rw [h1]
    have h2 : light.card ≤ m := le_trans (Finset.card_filter_le _ _)
      (by rw [Finset.card_univ, Fintype.card_fin])
    push_cast [Nat.cast_sub h2]
    have : (light.card : ℝ) ≤ 2 := by exact_mod_cast hcardlight
    linarith
  have hheavysum : ((Finset.univ \ light).card : ℝ) * lam
      ≤ ∑ c ∈ Finset.univ \ light, D.weight c := by
    have hstep := Finset.card_nsmul_le_sum (Finset.univ \ light) D.weight lam
      (fun c hc => ?_)
    · rwa [nsmul_eq_mul] at hstep
    · rw [hlight, Finset.mem_sdiff, Finset.mem_filter] at hc
      have h2 := hc.2
      push Not at h2
      exact h2 (Finset.mem_univ c)
  have htotal : ∑ c ∈ Finset.univ \ light, D.weight c ≤ 1 := by
    rw [← D.weight_sum_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      fun c _ _ => (D.weight_pos c).le
  nlinarith [hheavycard, hheavysum, htotal, hlam]

/-- **THE QUARTER LAW OF `(6,3)`.**  Every uniform projection floor of a
`(6,3)` tie is at most one quarter.  The `(5,3)` instance only reaches one
third: the gap is the whole size gain of the arm. -/
theorem uniform_floor_le_quarter_of_isTie (D : WeightedDesign 6 3)
    (htie : IsTie D) {lam : ℝ}
    (hfloor : ∀ pick : Fin 3 → Fin 6, Function.Injective pick →
      ∀ ξ : Fin 3 → ℝ, lam * (ξ ⬝ᵥ ξ) ≤
        ξ ⬝ᵥ ((projectionOfDesign D).submatrix pick pick *ᵥ ξ)) :
    lam ≤ 1 / 4 := by
  have := uniform_floor_tax_cap_of_isTie D htie hfloor
  norm_num at this
  linarith

end Gtz
