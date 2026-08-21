/-
# Duality removes the Bargmann cycle, and sharpens the leverage count

The Naimark dual negates every off-diagonal Gram entry and leaves every squared
one alone.  A `3 × 3` gap determinant carries exactly one term that is odd in the
off-diagonal entries — the Bargmann 3-cycle `2 p_ab p_ac p_bc` — so ADDING the
primal and dual gap determinants of the same triple kills it.

## The cycle-free sum

`Gtz.naimark_gapSum_cycleFree`:

  **`det(Gram_T - 1) + det(Gram*_T - 1)
     = ∏(ℓ_c - 1) + ∏(ℓ̃_c - 1) - Σ (1/t_c - 2) · q`**

where `ℓ̃_c = 1/t_c - ℓ_c` and each `q` is a squared pair reading of the triple.
Every term on the right is a leverage, a weight or a SQUARE.  The one quantity in
the vocabulary whose sign is not forced has left the statement.

The law holds at every size and every corank: the dual only has to have rank
three for the second determinant to be a `3 × 3` object, and it does not have to
be a design.

## The cycle-free reading at six points

At `(6,3)` the bracket law of `Gtz/Wave/NaimarkDualDesign.lean` pins the cycle by
the complementary triple, so the primal gap determinant alone becomes cycle-free
— `Gtz.sixThree_tripleGapDet_cycleFree`:

  **`tripleGapDet_T = ∏(ℓ_c-1) - Σ (ℓ_c-1) q + (∏ℓ̃_c - Σ ℓ̃_c q)
     - (∏_{Tᶜ} t / ∏_T t) · [Tᶜ]²`**

The right side is a polynomial in leverages, weights, squared pair readings and
one squared bracket.  No 3-cycle appears.

## The pair reading

`Gtz.naimark_pairGapMinor_sub` — the DIFFERENCE of the primal and dual pair
minors is free of the cross reading altogether:

  **`q_ab - q*_ab = (ℓ_a-1)(ℓ_b-1) - (ℓ̃_a-1)(ℓ̃_b-1)`.**

## A sharp leverage count

`Gtz.rank_le_card_heavyLeverage`:

  **Every `(m,k)` design has at least `k` atoms with leverage at least one.**

The landed `Gtz.rank_sub_one_sub_threshold_le_card_heavySet` gives `k - 1`.  The
missing atom comes from a STRICT inequality: on the light atoms the weighted
leverage is strictly below the weight.  At rank three this raises "at least two
atoms are heavy" to "at least three atoms are heavy", which is exactly the count
a triple needs.  Reading it in the dual gives `Gtz.corank_le_card_cappedLeverage`:
at least `m - k` atoms satisfy `t_c(ℓ_c + 1) ≤ 1`, the diagonal condition a
capped selection needs.  At `(6,3)` both counts are three, and the two candidate
triples are the ones the two forms of the conjecture ask about.

[MEASURED before proving.  The gap sum law, the pair difference law and the
six-point cycle-free reading were checked on 125 random designs at `(6,3)`,
`(5,3)`, `(7,3)`, `(4,3)` and `(8,3)` over every triple, with residuals at most
`9.5e-11`, `2.3e-13` and `9.5e-11`.]
-/
import Gtz.Wave.NaimarkDualExistence
import Gtz.Ties.AllTied

namespace Gtz

open Matrix Finset

variable {m k r : ℕ}

/-! ## 1. The three-by-three gap determinant, in any ambient dimension -/

/-- **THE GAP DETERMINANT OF THREE VECTORS.**  The `3 × 3` determinant of the Gram
of three vectors minus the identity, expanded.  The ambient dimension is free:
only the pairings enter.  At ambient dimension three this is `Gtz.tripleGapDet`. -/
theorem gapThree_det_expand {d : ℕ} (v : Fin 3 → (Fin d → ℝ)) :
    ((Matrix.of fun a b => v a ⬝ᵥ v b : Matrix (Fin 3) (Fin 3) ℝ) - 1).det
      = (leverageOf (v 0) - 1) * (leverageOf (v 1) - 1) * (leverageOf (v 2) - 1)
        - (leverageOf (v 0) - 1) * (v 1 ⬝ᵥ v 2) ^ 2
        - (leverageOf (v 1) - 1) * (v 0 ⬝ᵥ v 2) ^ 2
        - (leverageOf (v 2) - 1) * (v 0 ⬝ᵥ v 1) ^ 2
        + 2 * (v 0 ⬝ᵥ v 1) * (v 0 ⬝ᵥ v 2) * (v 1 ⬝ᵥ v 2) := by
  have hd : ∀ i j : Fin 3, i ≠ j →
      ((Matrix.of fun a b => v a ⬝ᵥ v b : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j = v i ⬝ᵥ v j := by
    intro i j hij
    simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply_ne hij, sub_zero]
  have he : ∀ i : Fin 3,
      ((Matrix.of fun a b => v a ⬝ᵥ v b : Matrix (Fin 3) (Fin 3) ℝ) - 1) i i
        = v i ⬝ᵥ v i - 1 := by
    intro i
    simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply_eq]
  rw [Matrix.det_fin_three, he 0, he 1, he 2,
    hd 0 1 (by decide), hd 0 2 (by decide), hd 1 0 (by decide), hd 1 2 (by decide),
    hd 2 0 (by decide), hd 2 1 (by decide),
    leverageOf_eq_dotProduct, leverageOf_eq_dotProduct, leverageOf_eq_dotProduct,
    dotProduct_comm (v 1) (v 0), dotProduct_comm (v 2) (v 0), dotProduct_comm (v 2) (v 1)]
  ring

variable {D : WeightedDesign m k}

/-- The primal gap determinant of a triple, expanded. -/
theorem naimarkGram_gap_expand (D : WeightedDesign m k) (pick : Fin 3 → Fin m) :
    (naimarkGram D pick - 1).det
      = (leverageOf (D.atom (pick 0)) - 1) * (leverageOf (D.atom (pick 1)) - 1)
          * (leverageOf (D.atom (pick 2)) - 1)
        - (leverageOf (D.atom (pick 0)) - 1) * (D.atom (pick 1) ⬝ᵥ D.atom (pick 2)) ^ 2
        - (leverageOf (D.atom (pick 1)) - 1) * (D.atom (pick 0) ⬝ᵥ D.atom (pick 2)) ^ 2
        - (leverageOf (D.atom (pick 2)) - 1) * (D.atom (pick 0) ⬝ᵥ D.atom (pick 1)) ^ 2
        + 2 * (D.atom (pick 0) ⬝ᵥ D.atom (pick 1)) * (D.atom (pick 0) ⬝ᵥ D.atom (pick 2))
            * (D.atom (pick 1) ⬝ᵥ D.atom (pick 2)) :=
  gapThree_det_expand fun a => D.atom (pick a)

/-- The dual gap determinant of a triple, expanded in DUAL data. -/
theorem naimarkCoGram_gap_expand (N : NaimarkDual D r) (pick : Fin 3 → Fin m) :
    (naimarkCoGram N pick - 1).det
      = (leverageOf (N.co (pick 0)) - 1) * (leverageOf (N.co (pick 1)) - 1)
          * (leverageOf (N.co (pick 2)) - 1)
        - (leverageOf (N.co (pick 0)) - 1) * (N.co (pick 1) ⬝ᵥ N.co (pick 2)) ^ 2
        - (leverageOf (N.co (pick 1)) - 1) * (N.co (pick 0) ⬝ᵥ N.co (pick 2)) ^ 2
        - (leverageOf (N.co (pick 2)) - 1) * (N.co (pick 0) ⬝ᵥ N.co (pick 1)) ^ 2
        + 2 * (N.co (pick 0) ⬝ᵥ N.co (pick 1)) * (N.co (pick 0) ⬝ᵥ N.co (pick 2))
            * (N.co (pick 1) ⬝ᵥ N.co (pick 2)) :=
  gapThree_det_expand fun a => N.co (pick a)

/-! ## 2. The cycle-free sum -/

/-- **THE CYCLE-FREE GAP SUM.**  The primal and dual gap determinants of the same
triple add to a polynomial in leverages, weights and SQUARED pair readings.  The
Bargmann 3-cycle is the only term of the expansion that is odd in the off-diagonal
entries, and duality negates exactly those, so the two copies cancel.

The law needs no relation between the size and the rank, and the dual does not
have to be a design.  Every quantity on the right has a forced sign except the
leverage terms. -/
theorem naimark_gapSum_cycleFree (N : NaimarkDual D r) {pick : Fin 3 → Fin m}
    (hpick : Function.Injective pick) :
    (naimarkGram D pick - 1).det + (naimarkCoGram N pick - 1).det
      = (leverageOf (D.atom (pick 0)) - 1) * (leverageOf (D.atom (pick 1)) - 1)
          * (leverageOf (D.atom (pick 2)) - 1)
        + (coLeverageDual D (pick 0) - 1) * (coLeverageDual D (pick 1) - 1)
          * (coLeverageDual D (pick 2) - 1)
        - ((D.weight (pick 0))⁻¹ - 2) * (D.atom (pick 1) ⬝ᵥ D.atom (pick 2)) ^ 2
        - ((D.weight (pick 1))⁻¹ - 2) * (D.atom (pick 0) ⬝ᵥ D.atom (pick 2)) ^ 2
        - ((D.weight (pick 2))⁻¹ - 2) * (D.atom (pick 0) ⬝ᵥ D.atom (pick 1)) ^ 2 := by
  have h01 : pick 0 ≠ pick 1 := fun h => by simpa using hpick h
  have h02 : pick 0 ≠ pick 2 := fun h => by simpa using hpick h
  have h12 : pick 1 ≠ pick 2 := fun h => by simpa using hpick h
  rw [naimarkGram_gap_expand D pick, naimarkCoGram_gap_expand N pick]
  rw [naimark_dot_eq_neg N h01, naimark_dot_eq_neg N h02, naimark_dot_eq_neg N h12]
  rw [← coLeverageDual_eq N, ← coLeverageDual_eq N, ← coLeverageDual_eq N]
  have hlev : ∀ u : Fin m,
      leverageOf (D.atom u) + coLeverageDual D u = (D.weight u)⁻¹ := by
    intro u
    rw [coLeverageDual]
    ring
  have h0 := hlev (pick 0)
  have h1 := hlev (pick 1)
  have h2 := hlev (pick 2)
  ring_nf
  nlinarith [h0, h1, h2, sq_nonneg (D.atom (pick 0) ⬝ᵥ D.atom (pick 1)),
    sq_nonneg (D.atom (pick 0) ⬝ᵥ D.atom (pick 2)),
    sq_nonneg (D.atom (pick 1) ⬝ᵥ D.atom (pick 2))]

/-! ## 3. The pair reading -/

/-- The dual pair minor, expanded in primal data. -/
theorem naimark_pairGapMinor_dual (N : NaimarkDual D r) {a b : Fin m} (hab : a ≠ b) :
    (coLeverageDual D a - 1) * (coLeverageDual D b - 1) - (N.co a ⬝ᵥ N.co b) ^ 2
      = (coLeverageDual D a - 1) * (coLeverageDual D b - 1)
        - (D.atom a ⬝ᵥ D.atom b) ^ 2 := by
  rw [naimark_crossNormSq_invariant N hab]

/-- **THE PAIR MINOR DIFFERENCE IS CROSS-FREE.**  Subtracting the dual pair minor
from the primal one removes the cross reading, leaving a difference of two
products of shifted leverages. -/
theorem naimark_pairGapMinor_sub (N : NaimarkDual D r) {a b : Fin m} (hab : a ≠ b) :
    ((leverageOf (D.atom a) - 1) * (leverageOf (D.atom b) - 1) - (D.atom a ⬝ᵥ D.atom b) ^ 2)
      - ((leverageOf (N.co a) - 1) * (leverageOf (N.co b) - 1) - (N.co a ⬝ᵥ N.co b) ^ 2)
      = (leverageOf (D.atom a) - 1) * (leverageOf (D.atom b) - 1)
        - (coLeverageDual D a - 1) * (coLeverageDual D b - 1) := by
  rw [naimark_crossNormSq_invariant N hab, ← coLeverageDual_eq N, ← coLeverageDual_eq N]
  ring

/-! ## 4. The cycle-free reading at six points -/

/-- **THE SIX-POINT GAP DETERMINANT WITHOUT ITS CYCLE.**  On a `(6,3)` design the
gap determinant of a triple is a polynomial in leverages, weights, squared pair
readings and the squared bracket of the COMPLEMENTARY triple.  The Bargmann
3-cycle, whose sign is the campaign's realness carrier, has been eliminated by
the bracket law. -/
theorem sixThree_tripleGapDet_cycleFree (D : WeightedDesign 6 3) (N : NaimarkDual D 3)
    (sel cosel : Fin 3 → Fin 6) (hpart : Function.Bijective (Sum.elim sel cosel)) :
    (∏ j, D.weight (cosel j))
        * tripleGapDet (D.atom (cosel 0)) (D.atom (cosel 1)) (D.atom (cosel 2))
      = (∏ j, D.weight (cosel j))
          * ((leverageOf (D.atom (cosel 0)) - 1) * (leverageOf (D.atom (cosel 1)) - 1)
              * (leverageOf (D.atom (cosel 2)) - 1)
            - (leverageOf (D.atom (cosel 0)) - 1) * (D.atom (cosel 1) ⬝ᵥ D.atom (cosel 2)) ^ 2
            - (leverageOf (D.atom (cosel 1)) - 1) * (D.atom (cosel 0) ⬝ᵥ D.atom (cosel 2)) ^ 2
            - (leverageOf (D.atom (cosel 2)) - 1) * (D.atom (cosel 0) ⬝ᵥ D.atom (cosel 1)) ^ 2
            + coLeverageDual D (cosel 0) * coLeverageDual D (cosel 1) * coLeverageDual D (cosel 2)
            - coLeverageDual D (cosel 0) * (D.atom (cosel 1) ⬝ᵥ D.atom (cosel 2)) ^ 2
            - coLeverageDual D (cosel 1) * (D.atom (cosel 0) ⬝ᵥ D.atom (cosel 2)) ^ 2
            - coLeverageDual D (cosel 2) * (D.atom (cosel 0) ⬝ᵥ D.atom (cosel 1)) ^ 2)
        - (∏ a, D.weight (sel a)) * (naimarkGram D sel).det := by
  have hcoinj : Function.Injective cosel := by
    intro a b hab
    have h : Sum.elim sel cosel (Sum.inr a) = Sum.elim sel cosel (Sum.inr b) := hab
    exact Sum.inr.inj (hpart.1 h)
  have hcyc := sixThree_bargmann_cycle D N sel cosel hpart
  have hexp := naimarkGram_gap_expand D cosel
  rw [naimarkGram_gap_det_eq_tripleGapDet D cosel] at hexp
  rw [hexp]
  linarith [hcyc]

/-! ## 5. A sharp count of heavy atoms -/

/-- The atoms whose leverage is at least one: the only candidates for a
dominating selection. -/
noncomputable def heavyLeverageSet (D : WeightedDesign m k) : Finset (Fin m) :=
  Finset.univ.filter fun c => (1 : ℝ) ≤ leverageOf (D.atom c)

/-- **AT LEAST `k` ATOMS ARE HEAVY.**  Every `(m,k)` design has at least `k`
atoms of leverage one or more.  The strict inequality on the light atoms is what
raises the landed count of `k - 1` by one, and at rank three it is the difference
between "two atoms" and "a triple". -/
theorem rank_le_card_heavyLeverage (D : WeightedDesign m k) :
    k ≤ (heavyLeverageSet D).card := by
  classical
  set light : Finset (Fin m) := Finset.univ.filter fun c => leverageOf (D.atom c) < 1
    with hlight
  have hsplit : light ∪ heavyLeverageSet D = Finset.univ := by
    ext c
    simp only [hlight, heavyLeverageSet, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => lt_or_ge (leverageOf (D.atom c)) 1⟩
  have hdisj : Disjoint light (heavyLeverageSet D) := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [hlight, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp only [heavyLeverageSet, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
    linarith
  have htrace : ∑ c, D.weight c * leverageOf (D.atom c) = (k : ℝ) :=
    sum_weight_mul_leverage D
  have hsum : (∑ c ∈ light, D.weight c * leverageOf (D.atom c))
      + ∑ c ∈ heavyLeverageSet D, D.weight c * leverageOf (D.atom c) = (k : ℝ) := by
    rw [← Finset.sum_union hdisj, hsplit, htrace]
  have hheavy : ∑ c ∈ heavyLeverageSet D, D.weight c * leverageOf (D.atom c)
      ≤ ((heavyLeverageSet D).card : ℝ) := by
    calc ∑ c ∈ heavyLeverageSet D, D.weight c * leverageOf (D.atom c)
        ≤ ∑ _c ∈ heavyLeverageSet D, (1 : ℝ) :=
          Finset.sum_le_sum fun c _ => weight_mul_leverage_le_one D c
      _ = ((heavyLeverageSet D).card : ℝ) := by simp
  rcases Finset.eq_empty_or_nonempty light with hempty | hne
  · -- no light atom: every atom is heavy, and the rank never exceeds the size
    have hall : heavyLeverageSet D = Finset.univ := by
      rw [← hsplit, hempty, Finset.empty_union]
    have hcard : (heavyLeverageSet D).card = m := by
      rw [hall, Finset.card_univ, Fintype.card_fin]
    have hkm : (k : ℝ) ≤ (m : ℝ) := by
      rw [← htrace]
      calc ∑ c, D.weight c * leverageOf (D.atom c) ≤ ∑ _c : Fin m, (1 : ℝ) :=
            Finset.sum_le_sum fun c _ => weight_mul_leverage_le_one D c
        _ = (m : ℝ) := by simp
    have hkmnat : k ≤ m := by exact_mod_cast hkm
    omega
  · -- some light atom: its weighted leverage is strictly below its weight
    have hstrict : ∑ c ∈ light, D.weight c * leverageOf (D.atom c) < ∑ c ∈ light, D.weight c := by
      refine Finset.sum_lt_sum_of_nonempty hne fun c hc => ?_
      simp only [hlight, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      nlinarith [D.weight_pos c]
    have hweight : ∑ c ∈ light, D.weight c ≤ 1 := by
      rw [← D.weight_sum_one]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ light)
        fun c _ _ => (D.weight_pos c).le
    have hbound : (k : ℝ) < 1 + ((heavyLeverageSet D).card : ℝ) := by linarith
    have : k < 1 + (heavyLeverageSet D).card := by exact_mod_cast hbound
    omega

/-! ## 6. The dual count -/

/-- The atoms that can sit in a capped selection: those with `t_c(ℓ_c + 1) ≤ 1`. -/
noncomputable def cappedLeverageSet (D : WeightedDesign m k) : Finset (Fin m) :=
  Finset.univ.filter fun c => D.weight c * (leverageOf (D.atom c) + 1) ≤ 1

/-- The capped condition is the dual heavy condition. -/
theorem mem_cappedLeverageSet_iff (N : NaimarkDual D r) (c : Fin m) :
    c ∈ cappedLeverageSet D ↔ c ∈ heavyLeverageSet N.dual := by
  have hshare := naimark_coShare N c
  have hpos := D.weight_pos c
  simp only [cappedLeverageSet, heavyLeverageSet, Finset.mem_filter, Finset.mem_univ,
    true_and, NaimarkDual.dual_atom]
  constructor
  · intro h
    nlinarith [hshare, h]
  · intro h
    nlinarith [hshare, h]

/-- **AT LEAST `m - k` ATOMS ARE CAPPED.**  Read the heavy count in the Naimark
dual.  At `(6,3)` this gives three atoms with `t_c(ℓ_c + 1) ≤ 1`, exactly the
diagonal condition a capped triple needs, and the count is again exactly a
triple. -/
theorem corank_le_card_cappedLeverage (D : WeightedDesign m k) (hr : k + r = m) :
    r ≤ (cappedLeverageSet D).card := by
  classical
  obtain ⟨N⟩ := exists_naimarkDual D hr
  have hsets : cappedLeverageSet D = heavyLeverageSet N.dual := by
    ext c
    exact mem_cappedLeverageSet_iff N c
  rw [hsets]
  exact rank_le_card_heavyLeverage N.dual

/-! ## 7. The two candidate triples at six points -/

/-- **THREE HEAVY ATOMS AND THREE CAPPED ATOMS.**  Every `(6,3)` design has at
least three atoms of leverage one or more, and at least three atoms with
`t_c(ℓ_c + 1) ≤ 1`.  The first set carries every candidate for a dominating
triple, the second every candidate for a capped triple, and the two forms of the
conjecture ask about those two sets. -/
theorem sixThree_candidate_counts (D : WeightedDesign 6 3) :
    3 ≤ (heavyLeverageSet D).card ∧ 3 ≤ (cappedLeverageSet D).card :=
  ⟨rank_le_card_heavyLeverage D, corank_le_card_cappedLeverage D (r := 3) (by norm_num)⟩

/-- **DOMINATION FORCES HEAVY ATOMS.**  Every atom of a dominating selection has
leverage at least one, so a dominating triple lies inside `heavyLeverageSet`. -/
theorem dominates_subset_heavyLeverage (D : WeightedDesign m k) {pick : Fin k → Fin m}
    (hpick : Function.Injective pick)
    (hdom : Dominates D (Finset.image pick Finset.univ)) (a : Fin k) :
    pick a ∈ heavyLeverageSet D := by
  have hgap := (dominates_iff_naimarkGram D hpick).mp hdom
  have hdiag : (0 : ℝ) ≤ (naimarkGram D pick - 1) a a := hgap.diag_nonneg
  rw [Matrix.sub_apply, naimarkGram, Matrix.of_apply, Matrix.one_apply_eq,
    ← leverageOf_eq_dotProduct] at hdiag
  simp only [heavyLeverageSet, Finset.mem_filter, Finset.mem_univ, true_and]
  linarith

/-- **CAPPING FORCES CAPPED ATOMS.**  Every atom of a capped selection satisfies
`t_c(ℓ_c + 1) ≤ 1`, so a capped triple lies inside `cappedLeverageSet`. -/
theorem cappedTriple_subset_cappedLeverage (D : WeightedDesign 6 3) {pick : Fin 3 → Fin 6}
    (hcap : CappedTriple D pick) (a : Fin 3) :
    pick a ∈ cappedLeverageSet D := by
  obtain ⟨hpick, hpsd⟩ := hcap
  have hdiag : (0 : ℝ) ≤ (naimarkCap D pick - naimarkGram D pick) a a := hpsd.diag_nonneg
  rw [Matrix.sub_apply, naimarkCap, naimarkGram, Matrix.of_apply, Matrix.diagonal_apply_eq,
    ← leverageOf_eq_dotProduct] at hdiag
  simp only [cappedLeverageSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hpos := D.weight_pos (pick a)
  have hinv : D.weight (pick a) * (D.weight (pick a))⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  nlinarith [hdiag, hpos, hinv]

end Gtz
