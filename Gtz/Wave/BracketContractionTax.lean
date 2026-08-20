/-
# The contraction tax: domination from the bracket alone

The projection of a design is an ORTHOGONAL projection, so every principal
block is a CONTRACTION: `0 ⪯ Π[C] ⪯ 1`.  The determinant of a contraction is
below each of its eigenvalues, hence below every Rayleigh quotient at a unit
probe — the landed spectral step of `Gtz.CauchyBinetValueFloor`.  Read at a
triple block this says the block determinant is itself a QUADRATIC FLOOR of
the block, and the landed light-triple producer converts a floor into a
strict dominator.  The result is the sharpest producer of the arm:

* `Gtz.posDef_subsetSum_of_det_gt_weights` — a triple whose block
  determinant beats all three member weights DOMINATES STRICTLY;
* `Gtz.posDef_subsetSum_of_bracket_gt_weights` — the same in the invariant
  arena: `t_at_bt_c·[abc]² > t_a, t_b, t_c` produces a strict dominator.
  A sufficient condition for the campaign's goal, written entirely in the
  bracket and the weights;
* `Gtz.isTie_bracket_tax` — the contrapositive at a tie: at EVERY triple,
  the weighted squared bracket is at most one of its member weights.

This is the wedge-bracket tax of `Gtz.WedgeBracketTax` with the second
invariant REMOVED.  The two are complementary: the wedge tax prices the
bracket by `t·e₂` and wins when `e₂ < 1`, the contraction tax prices it by
`t` alone and wins when `e₂ > 1`.  `Gtz.isTie_bracket_tax_combined` states
the conjunction, and `Gtz.blockFloor_ge_det` records the combined block
floor `λ ≥ det·max(1, 1/e₂)` in floor form.

The tax then consumes the SIZE twice more.  A design always carries a triple
whose three weights are at most `1/(m−2)` (`Gtz.exists_light_triple`), by the
pigeonhole on the weight simplex, so:

* `Gtz.isTie_light_triple_bracket_cap` — every `(m,3)` tie carries a triple
  with `t_at_bt_c·[abc]² ≤ 1/(m−2)`.  The QUARTER at `(6,3)`, the THIRD at
  `(5,3)`.

Finally the equality case is contact geometry, and it needs no spectral
theorem: `Gtz.blockEigen_one_of_supported_mem_range` shows a vector supported
on the triple and fixed by the projection is a `+1` eigenvector of the block.
[MEASURED: the criterion has no counterexample in 400000 random triples, and
it is EXACTLY TIGHT at the tetrahedral tie, whose block spectrum is
`(1/4, 1, 1)` — the two `+1` eigenvalues are the two contact directions.]
-/
import Gtz.Wave.InvariantBudgets
import Gtz.Quantitative.CauchyBinetValueFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The triple block is a contraction -/

/-- The complement of a projection block is the block of the complement. -/
theorem one_sub_projectionBlock (D : WeightedDesign m 3) {pick : Fin 3 → Fin m}
    (hinj : Function.Injective pick) :
    (1 : Matrix (Fin 3) (Fin 3) ℝ) - (projectionOfDesign D).submatrix pick pick
      = ((1 : Matrix (Fin m) (Fin m) ℝ) - projectionOfDesign D).submatrix pick pick := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.one_apply,
    hinj.eq_iff]

/-- **THE BLOCK IS A CONTRACTION.**  `1 − Π[C]` is positive semidefinite:
the complement of the projection is positive semidefinite, and a principal
block of a positive semidefinite matrix is positive semidefinite. -/
theorem posSemidef_one_sub_projectionBlock (D : WeightedDesign m 3)
    {pick : Fin 3 → Fin m} (hinj : Function.Injective pick) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - (projectionOfDesign D).submatrix pick pick).PosSemidef := by
  rw [one_sub_projectionBlock D hinj]
  exact (posSemidef_one_sub_projectionOfDesign D).submatrix pick

/-! ## 2. The determinant is a quadratic floor of the block -/

/-- **THE DETERMINANT FLOOR, HOMOGENEOUS.**  For every probe, the block
determinant times the squared probe norm is below the block form.  The unit
probe case is the landed spectral step; the homogeneous case follows by
scaling, and the zero probe is trivial. -/
theorem det_projectionBlock_mul_normSq_le (D : WeightedDesign m 3)
    {pick : Fin 3 → Fin m} (hinj : Function.Injective pick) (ξ : Fin 3 → ℝ) :
    ((projectionOfDesign D).submatrix pick pick).det * (ξ ⬝ᵥ ξ)
      ≤ ξ ⬝ᵥ ((projectionOfDesign D).submatrix pick pick *ᵥ ξ) := by
  classical
  set A : Matrix (Fin 3) (Fin 3) ℝ := (projectionOfDesign D).submatrix pick pick with hA
  have hpsd : A.PosSemidef := (posSemidef_projectionOfDesign D).submatrix pick
  have hcon : ((1 : Matrix (Fin 3) (Fin 3) ℝ) - A).PosSemidef :=
    posSemidef_one_sub_projectionBlock D hinj
  rcases eq_or_ne ξ 0 with hzero | hne
  · subst hzero
    simp
  · have hpos : 0 < ξ ⬝ᵥ ξ := dotProduct_self_pos hne
    set s : ℝ := Real.sqrt (ξ ⬝ᵥ ξ) with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr hpos
    set u : Fin 3 → ℝ := s⁻¹ • ξ with hu
    have hsne : s ≠ 0 := hspos.ne'
    have hsq : s * s = ξ ⬝ᵥ ξ := by rw [hs, Real.mul_self_sqrt hpos.le]
    have hunit : u ⬝ᵥ u = 1 := by
      rw [hu, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hsq]
      field_simp
    have hstep := det_le_dotProduct_mulVec_of_posSemidef_of_posSemidef_one_sub
      hpsd hcon hunit
    have hform : u ⬝ᵥ (A *ᵥ u) = (s⁻¹ * s⁻¹) * (ξ ⬝ᵥ (A *ᵥ ξ)) := by
      rw [hu, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        smul_eq_mul]
      ring
    rw [hform] at hstep
    have hmul := mul_le_mul_of_nonneg_left hstep (mul_nonneg hspos.le hspos.le)
    calc A.det * (ξ ⬝ᵥ ξ) = (s * s) * A.det := by rw [hsq]; ring
      _ ≤ (s * s) * ((s⁻¹ * s⁻¹) * (ξ ⬝ᵥ (A *ᵥ ξ))) := hmul
      _ = ξ ⬝ᵥ (A *ᵥ ξ) := by field_simp

/-! ## 3. The determinant producer -/

/-- **THE DETERMINANT PRODUCER.**  A triple whose block determinant strictly
beats all three of its member weights DOMINATES STRICTLY.  No eigenvalues, no
tie hypothesis, no second invariant: the contraction turns the determinant
itself into the block floor. -/
theorem posDef_subsetSum_of_det_gt_weights (D : WeightedDesign m 3)
    (pick : Fin 3 → Fin m) (hinj : Function.Injective pick)
    (hbeat : ∀ slot, D.weight (pick slot)
      < ((projectionOfDesign D).submatrix pick pick).det) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef :=
  posDef_subsetSum_of_projectionFloor_light D pick hinj
    (fun ξ => det_projectionBlock_mul_normSq_le D hinj ξ) hbeat

/-- **THE BRACKET PRODUCER.**  In the invariant arena: a triple whose
weighted squared bracket beats each of its member weights dominates
strictly.  A sufficient condition for the campaign's goal written entirely in
the bracket and the weights. -/
theorem posDef_subsetSum_of_bracket_gt_weights (D : WeightedDesign m 3)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbeatA : D.weight a
      < D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2)))
    (hbeatB : D.weight b
      < D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2)))
    (hbeatC : D.weight c
      < D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))) :
    (subsetSum D ({a, b, c} : Finset (Fin m)) - 1).PosDef := by
  have hinj := injective_tripleSlots hab hac hbc
  have hdet := projectionBlock_det_eq D ![a, b, c]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hdet
  rw [← image_tripleSlots a b c]
  refine posDef_subsetSum_of_det_gt_weights D ![a, b, c] hinj (fun slot => ?_)
  rw [hdet]
  fin_cases slot
  · simpa using hbeatA
  · simpa using hbeatB
  · simpa using hbeatC

/-! ## 4. The bracket tax of a tie -/

/-- **THE BRACKET TAX OF A TIE.**  At every triple of a tie the weighted
squared bracket is at most one of its member weights.  The wedge-bracket tax
with the second invariant removed. -/
theorem isTie_bracket_tax (D : WeightedDesign m 3) (htie : IsTie D)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ member ∈ ({a, b, c} : Finset (Fin m)),
      D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
        ≤ D.weight member := by
  by_contra hcon
  push Not at hcon
  have hA := hcon a (by simp)
  have hB := hcon b (by simp)
  have hC := hcon c (by simp)
  have hcard : (({a, b, c} : Finset (Fin m))).card = 3 := by
    rw [← image_tripleSlots a b c,
      Finset.card_image_of_injective _ (injective_tripleSlots hab hac hbc),
      Finset.card_univ, Fintype.card_fin]
  exact htie.2 _ hcard
    (posDef_subsetSum_of_bracket_gt_weights D hab hac hbc hA hB hC)

/-- **THE COMBINED TAX.**  Both prices hold at every triple of a tie: the
weighted squared bracket is at most a member weight, AND at most a member
weight times the wedge mass.  The first wins when the wedge mass exceeds one,
the second when it falls below. -/
theorem isTie_bracket_tax_combined (D : WeightedDesign m 3) (htie : IsTie D)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hmass : 0 < D.weight a * (D.weight b
        * (leverageOf (D.atom a) * leverageOf (D.atom b) - atomPairing D a b ^ 2))
      + D.weight a * (D.weight c
        * (leverageOf (D.atom a) * leverageOf (D.atom c) - atomPairing D a c ^ 2))
      + D.weight b * (D.weight c
        * (leverageOf (D.atom b) * leverageOf (D.atom c) - atomPairing D b c ^ 2))) :
    (∃ member ∈ ({a, b, c} : Finset (Fin m)),
      D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
        ≤ D.weight member)
    ∧ (∃ member ∈ ({a, b, c} : Finset (Fin m)),
      D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
        ≤ D.weight member
          * (D.weight a * (D.weight b
              * (leverageOf (D.atom a) * leverageOf (D.atom b) - atomPairing D a b ^ 2))
            + D.weight a * (D.weight c
              * (leverageOf (D.atom a) * leverageOf (D.atom c) - atomPairing D a c ^ 2))
            + D.weight b * (D.weight c
              * (leverageOf (D.atom b) * leverageOf (D.atom c)
                - atomPairing D b c ^ 2)))) :=
  ⟨isTie_bracket_tax D htie hab hac hbc,
    isTie_wedgeBracket_tax D htie hab hac hbc hmass⟩

/-- **THE COMBINED BLOCK FLOOR.**  Both the determinant and the determinant
over the second invariant are quadratic floors of the block, so their maximum
is.  The contraction supplies the first, the teeth the second. -/
theorem blockFloor_ge_det (D : WeightedDesign m 3)
    {pick : Fin 3 → Fin m} (hinj : Function.Injective pick)
    (he₂ : 0 < ((Matrix.trace ((projectionOfDesign D).submatrix pick pick))^2
        - Matrix.trace ((projectionOfDesign D).submatrix pick pick
          * (projectionOfDesign D).submatrix pick pick))/2)
    (ξ : Fin 3 → ℝ) :
    max (((projectionOfDesign D).submatrix pick pick).det)
        (((projectionOfDesign D).submatrix pick pick).det
          / ((((Matrix.trace ((projectionOfDesign D).submatrix pick pick))^2
            - Matrix.trace ((projectionOfDesign D).submatrix pick pick
              * (projectionOfDesign D).submatrix pick pick))/2)))
      * (ξ ⬝ᵥ ξ)
      ≤ ξ ⬝ᵥ ((projectionOfDesign D).submatrix pick pick *ᵥ ξ) := by
  set A : Matrix (Fin 3) (Fin 3) ℝ := (projectionOfDesign D).submatrix pick pick with hA
  set e₂ : ℝ := ((Matrix.trace A)^2 - Matrix.trace (A * A))/2 with he
  have hpsd : A.PosSemidef := (posSemidef_projectionOfDesign D).submatrix pick
  have hnn : 0 ≤ ξ ⬝ᵥ ξ := dotProduct_self_nonneg ξ
  have hteeth : A.det / e₂ * (ξ ⬝ᵥ ξ) ≤ ξ ⬝ᵥ (A *ᵥ ξ) := by
    have h := e2_mul_form_ge_det_mul_normSq hpsd ξ
    rw [← he] at h
    rw [div_mul_eq_mul_div, div_le_iff₀ he₂]
    nlinarith [h]
  have hcontr := det_projectionBlock_mul_normSq_le D hinj ξ
  rcases le_total (A.det) (A.det / e₂) with hle | hle
  · rw [max_eq_right hle]; exact hteeth
  · rw [max_eq_left hle]; exact hcontr

/-! ## 5. The size consumption: the light triple -/

/-- **EVERY DESIGN CARRIES A LIGHT TRIPLE.**  Three distinct atoms whose
weights are all at most `1/(m−2)`.  The heavy atoms — those above the
threshold — number at most `m − 3`, because `m − 2` of them would already
exceed the whole simplex. -/
theorem exists_light_triple (D : WeightedDesign m 3) (hm : 3 ≤ m) :
    ∃ a b c : Fin m, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      D.weight a ≤ 1 / ((m : ℝ) - 2) ∧ D.weight b ≤ 1 / ((m : ℝ) - 2)
      ∧ D.weight c ≤ 1 / ((m : ℝ) - 2) := by
  classical
  set thr : ℝ := 1 / ((m : ℝ) - 2) with hthr
  have hmr : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : 0 < (m : ℝ) - 2 := by linarith
  set heavy := Finset.univ.filter fun c => thr < D.weight c with hheavy
  have hheavycard : heavy.card ≤ m - 3 := by
    by_contra hcon
    push Not at hcon
    have hge : m - 2 ≤ heavy.card := by omega
    have hgeR : ((m : ℝ) - 2) ≤ (heavy.card : ℝ) := by
      have h1 : ((m - 2 : ℕ) : ℝ) ≤ (heavy.card : ℝ) := by exact_mod_cast hge
      have h2m : 2 ≤ m := by omega
      have h2 : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
        rw [Nat.cast_sub h2m]
        norm_num
      rw [h2] at h1
      exact h1
    have hnonempty : heavy.Nonempty := by
      rw [← Finset.card_pos]
      omega
    have hstrict : ∑ _c ∈ heavy, thr < ∑ c ∈ heavy, D.weight c :=
      Finset.sum_lt_sum_of_nonempty hnonempty
        fun c hc => (Finset.mem_filter.mp hc).2
    have hconst : ∑ _c ∈ heavy, thr = (heavy.card : ℝ) * thr := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have htotal : ∑ c ∈ heavy, D.weight c ≤ 1 := by
      rw [← D.weight_sum_one]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun c _ _ => (D.weight_pos c).le
    have hone : (1 : ℝ) ≤ (heavy.card : ℝ) * thr := by
      rw [hthr]
      calc (1 : ℝ) = ((m : ℝ) - 2) * (1 / ((m : ℝ) - 2)) := by field_simp
        _ ≤ (heavy.card : ℝ) * (1 / ((m : ℝ) - 2)) :=
            mul_le_mul_of_nonneg_right hgeR (by positivity)
    rw [hconst] at hstrict
    linarith [hstrict, htotal, hone]
  have hlightcard : 3 ≤ (Finset.univ \ heavy).card := by
    have h1 : (Finset.univ \ heavy).card = m - heavy.card := by
      have hc : (Finset.univ \ heavy).card
          = (Finset.univ : Finset (Fin m)).card - (heavy ∩ Finset.univ).card :=
        Finset.card_sdiff
      rw [Finset.inter_univ, Finset.card_univ, Fintype.card_fin] at hc
      exact hc
    omega
  obtain ⟨light₃, hsub, hcard₃⟩ := Finset.exists_subset_card_eq hlightcard
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hcard₃
  have hmem : ∀ x ∈ light₃, D.weight x ≤ thr := by
    intro x hx
    have hxs := hsub hx
    rw [Finset.mem_sdiff, hheavy, Finset.mem_filter] at hxs
    have h2 := hxs.2
    push Not at h2
    exact h2 (Finset.mem_univ x)
  exact ⟨a, b, c, hab, hac, hbc,
    hmem a (by rw [hset]; simp), hmem b (by rw [hset]; simp),
    hmem c (by rw [hset]; simp)⟩

/-- **THE LIGHT-TRIPLE BRACKET CAP OF A TIE.**  Every `(m,3)` tie carries a
triple whose weighted squared bracket is at most `1/(m−2)`.  The QUARTER at
`(6,3)`, the THIRD at `(5,3)`: the size enters through the weight simplex,
and the conclusion is a pure invariant statement. -/
theorem isTie_light_triple_bracket_cap (D : WeightedDesign m 3) (htie : IsTie D)
    (hm : 3 ≤ m) :
    ∃ a b c : Fin m, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
        ≤ 1 / ((m : ℝ) - 2) := by
  obtain ⟨a, b, c, hab, hac, hbc, hA, hB, hC⟩ := exists_light_triple D hm
  obtain ⟨member, hmem, hle⟩ := isTie_bracket_tax D htie hab hac hbc
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

/-- **THE QUARTER LAW OF `(6,3)`, IN THE BRACKET.**  Every `(6,3)` tie carries
a triple whose weighted squared bracket is at most one quarter. -/
theorem isTie_sixThree_bracket_quarter (D : WeightedDesign 6 3) (htie : IsTie D) :
    ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
        ≤ 1 / 4 := by
  obtain ⟨a, b, c, hab, hac, hbc, hle⟩ :=
    isTie_light_triple_bracket_cap D htie (by norm_num)
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  norm_num at hle
  exact hle

/-! ## 6. The contact geometry of the equality case -/

/-- **THE CONTACT LEMMA.**  A vector supported on the triple and fixed by the
projection restricts to a `+1` eigenvector of the block.  No spectral theorem
and no eigenvalue: the projection's action at a coordinate of the triple sees
only the triple's own entries, because the vector vanishes off it.

[The tetrahedral tie realizes the extreme case: its triple block has spectrum
`(1/4, 1, 1)`, so the determinant floor is ATTAINED, and the two `+1`
directions are exactly two independent supported vectors in the range.] -/
theorem blockEigen_one_of_supported_mem_range (D : WeightedDesign m 3)
    {pick : Fin 3 → Fin m} (hinj : Function.Injective pick)
    {v : Fin m → ℝ} (hsupp : ∀ x, (∀ slot, x ≠ pick slot) → v x = 0)
    (hfix : projectionOfDesign D *ᵥ v = v) :
    (projectionOfDesign D).submatrix pick pick *ᵥ (fun slot => v (pick slot))
      = fun slot => v (pick slot) := by
  classical
  funext slot
  have hrow : ∑ x, projectionOfDesign D (pick slot) x * v x = v (pick slot) := by
    have h := congrFun hfix (pick slot)
    rwa [Matrix.mulVec, dotProduct] at h
  have himg : ∑ x ∈ (Finset.univ.image pick), projectionOfDesign D (pick slot) x * v x
      = ∑ other, projectionOfDesign D (pick slot) (pick other) * v (pick other) :=
    Finset.sum_image fun x _ y _ h => hinj h
  have hzero : ∑ x, projectionOfDesign D (pick slot) x * v x
      = ∑ x ∈ (Finset.univ.image pick), projectionOfDesign D (pick slot) x * v x := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    have hoff : ∀ s2, x ≠ pick s2 := by
      intro s2 hxs
      exact hx (Finset.mem_image.mpr ⟨s2, Finset.mem_univ _, hxs.symm⟩)
    rw [hsupp x hoff, mul_zero]
  have hsplit : ∑ x, projectionOfDesign D (pick slot) x * v x
      = ∑ other, projectionOfDesign D (pick slot) (pick other) * v (pick other) := by
    rw [hzero, himg]
  rw [Matrix.mulVec, dotProduct]
  simp only [Matrix.submatrix_apply]
  rw [← hsplit, hrow]

end Gtz
