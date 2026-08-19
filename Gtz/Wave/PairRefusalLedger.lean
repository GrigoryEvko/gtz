import Gtz.Wave.LightSetFloor
import Gtz.Wave.SixSetRefusal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The refusal ledger of a pair, and the emptiness of the deficit residual

At a `(6,3)` design every card-3 subset `R` of labels reads the six-set pivot
matrix through the depth-three downdate, and the triple `Rᶜ` dominates strictly
exactly when the three Sylvester minors of `I₃ − P_R` are positive
(`Gtz.tie_refusal_sylvester`).  Fix a pair `f ≠ h` and let `x` run over the four
remaining labels.  When the pair itself is ADMISSIBLE — both pivots below one
and the pair minor `Δ := (1 − P_ff)(1 − P_hh) − P_fh²` positive — the first two
Sylvester minors of `I₃ − P_{f,h,x}` are positive, so a refusal of `{f,h,x}ᶜ`
falls on the third minor alone.  That third minor is the REFUSAL SLACK

  `slack_x := (1 − P_hh)P_fx² + 2 P_fh P_fx P_hx + (1 − P_ff)P_hx² − (1 − P_xx)·Δ` ,

and the refusal says exactly `0 ≤ slack_x`.

## The ledger identity

The four slacks do not merely bound the pair.  Weighted by the co-weights they
ADD UP to the weighted ghost deficit, exactly
(`Gtz.sum_coweight_pairRefusalSlack`):

  `Σ_{x ∉ {f,h}} (1 − t_x)·slack_x = Gtz.ghostDeficitForm D f h` .

The proof is three instances of the projection identity
(`Gtz.pivot_coweight_projection`) — the row masses `Σ_x (1−t_x)P_fx² = P_ff`,
`Σ_x (1−t_x)P_fxP_hx = P_fh`, `Σ_x (1−t_x)P_hx² = P_hh` — together with the
co-weight deficit `Σ_x (1−t_x)(1−P_xx) = m − 4`.  The size enters once, and it
enters as a clean correction: at general `m` the two sides differ by
`(m − 6)·Δ`, so the identity is exact at `(6,3)` and at no other size.  At
`(5,3)` the slack budget is one `Δ` larger than the deficit, which is the room
the diamond needs.

## What the ledger says

A tie makes every slack nonnegative, so the weighted ghost deficit of every
admissible pair is nonnegative (`Gtz.ghostDeficitForm_nonneg_of_isTie`).  That
is the exact negation of `Gtz.GhostDeficitShort`, hence:

* no pair of a `(6,3)` tie is ghost-deficient
  (`Gtz.not_ghostDeficitShort_of_isTie`);
* no pair of a `(6,3)` tie carries a short ghost block
  (`Gtz.not_ghostBlockShort_of_isTie`), which strengthens
  `Gtz.not_ghostBlockShort_two_selectors` from "at most one selector" to "no
  selector";
* `Gtz.NonplanarDeficitResidual` has NO PRODUCER: at a tie its conclusion is
  unreachable, so the residual holds exactly when the corner is empty
  (`Gtz.nonplanarDeficitResidual_iff_no_corner`).  The residual is not a
  weakening of the corner closure — it IS the corner closure.

## The pivot law

Cauchy–Schwarz on the co-weighted rows gives `P_fh² ≤ P_ff·P_hh`
(`Gtz.sixSetPivot_sq_le_mul`).  Feeding it to the ledger in the inadmissible
branch as well collapses the case analysis into one weight-free law
(`Gtz.tie_pair_pivot_law`): at every `(6,3)` tie and every pair,

  `1 ≤ 2·P_ff + P_hh`  or  `1 ≤ 2·P_hh + P_ff` .

So at most one atom of a tie has pivot below one third
(`Gtz.tie_pivot_lt_third_unique`), and the light set of a tie has at least FOUR
atoms (`Gtz.four_le_card_lightSet_of_isTie`), which sharpens
`Gtz.three_le_card_lightSet` and empties
`Gtz.eq_compl_lightSet_of_card_three` at a tie.

## The corner

At a corank-two corner the same slacks summed over the complement triple alone,
with no weights, price the corner (`Gtz.sum_pairRefusalSlack_compl`): the
outside cross readings and the corner pivot appear, and a tie turns the identity
into the corner ledger `Gtz.corner_pairRefusal_bound`.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The refusal slack and the deficit form -/

/-- The pair minor `Δ = (1 − P_ff)(1 − P_hh) − P_fh²` of the six-set pivot
matrix: the second Sylvester minor of `I₃ − P_R` at every triple through the
pair. -/
noncomputable def pairPivotMinor (D : WeightedDesign 6 3) (f h : Fin 6) : ℝ :=
  (1 - sixSetPivot D f f) * (1 - sixSetPivot D h h) - sixSetPivot D f h ^ 2

/-- The REFUSAL SLACK of a pair against a third label: the third Sylvester minor
of `I₃ − P_{f,h,x}`, with the sign that makes a refusal read `0 ≤ slack`. -/
noncomputable def pairRefusalSlack (D : WeightedDesign 6 3) (f h x : Fin 6) : ℝ :=
  (1 - sixSetPivot D h h) * sixSetPivot D f x ^ 2
    + 2 * (sixSetPivot D f h * (sixSetPivot D f x * sixSetPivot D h x))
    + (1 - sixSetPivot D f f) * sixSetPivot D h x ^ 2
    - (1 - sixSetPivot D x x) * pairPivotMinor D f h

/-- The weighted ghost deficit form of a pair: the weighted sum of the two swap
brackets of `Gtz.GhostDeficitShort`. -/
noncomputable def ghostDeficitForm (D : WeightedDesign 6 3) (f h : Fin 6) : ℝ :=
  D.weight f * ((1 - sixSetPivot D h h) * (2 * sixSetPivot D f f - 1)
      + 2 * sixSetPivot D f h ^ 2)
    + D.weight h * ((1 - sixSetPivot D f f) * (2 * sixSetPivot D h h - 1)
      + 2 * sixSetPivot D f h ^ 2)

/-- The deficit form is symmetric in the pair. -/
theorem ghostDeficitForm_comm (D : WeightedDesign 6 3) (f h : Fin 6) :
    ghostDeficitForm D f h = ghostDeficitForm D h f := by
  rw [ghostDeficitForm, ghostDeficitForm, sixSetPivot_comm D h f]
  ring

/-- The pair minor is symmetric in the pair. -/
theorem pairPivotMinor_comm (D : WeightedDesign 6 3) (f h : Fin 6) :
    pairPivotMinor D f h = pairPivotMinor D h f := by
  rw [pairPivotMinor, pairPivotMinor, sixSetPivot_comm D h f]
  ring

/-- A ghost-deficient pair has negative deficit form. -/
theorem ghostDeficitForm_neg_of_ghostDeficitShort (D : WeightedDesign 6 3)
    {f h : Fin 6} (hdef : GhostDeficitShort D f h) : ghostDeficitForm D f h < 0 :=
  hdef.2.2.2

/-! ## 2. The co-weighted row masses -/

/-- **The co-weighted row mass of one pivot row.**  The diagonal instance of the
projection identity. -/
theorem sum_coweight_pivot_sq (D : WeightedDesign m 3)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (f : Fin m) :
    ∑ x, (1 - D.weight x) * sixSetPivot D f x ^ 2 = sixSetPivot D f f := by
  have hproj := pivot_coweight_projection D hPD f f
  have hsymm : ∀ x : Fin m,
      D.atom x ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom f) = sixSetPivot D f x :=
    fun x => (sixSetPivot_comm D f x) ▸ rfl
  calc ∑ x, (1 - D.weight x) * sixSetPivot D f x ^ 2
      = ∑ x, (1 - D.weight x)
          * ((D.atom f ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom x))
            * (D.atom x ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom f))) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [show D.atom f ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom x)
            = sixSetPivot D f x from rfl, hsymm x]
        ring
    _ = sixSetPivot D f f := hproj

/-- **The co-weighted pairing of two pivot rows.**  The off-diagonal instance of
the projection identity. -/
theorem sum_coweight_pivot_cross (D : WeightedDesign m 3)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (f h : Fin m) :
    ∑ x, (1 - D.weight x) * (sixSetPivot D f x * sixSetPivot D h x)
      = sixSetPivot D f h := by
  have hproj := pivot_coweight_projection D hPD f h
  have hsymm : ∀ x : Fin m,
      D.atom x ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom h) = sixSetPivot D h x :=
    fun x => (sixSetPivot_comm D h x) ▸ rfl
  calc ∑ x, (1 - D.weight x) * (sixSetPivot D f x * sixSetPivot D h x)
      = ∑ x, (1 - D.weight x)
          * ((D.atom f ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom x))
            * (D.atom x ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom h))) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [show D.atom f ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom x)
            = sixSetPivot D f x from rfl, hsymm x]
    _ = sixSetPivot D f h := hproj

/-- **Cauchy–Schwarz on the co-weighted rows.**  Every off-diagonal pivot is
dominated by the two diagonals it sits between. -/
theorem sixSetPivot_sq_le_mul (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (f h : Fin m) :
    sixSetPivot D f h ^ 2 ≤ sixSetPivot D f f * sixSetPivot D h h := by
  classical
  have hco : ∀ x : Fin m, (0 : ℝ) ≤ 1 - D.weight x := fun x => by
    linarith [design_weight_lt_one D hm x]
  have hroot : ∀ x : Fin m,
      Real.sqrt (1 - D.weight x) * Real.sqrt (1 - D.weight x) = 1 - D.weight x :=
    fun x => Real.mul_self_sqrt (hco x)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
    (fun x => Real.sqrt (1 - D.weight x) * sixSetPivot D f x)
    (fun x => Real.sqrt (1 - D.weight x) * sixSetPivot D h x)
  have hprod : ∀ x : Fin m,
      (Real.sqrt (1 - D.weight x) * sixSetPivot D f x)
          * (Real.sqrt (1 - D.weight x) * sixSetPivot D h x)
        = (1 - D.weight x) * (sixSetPivot D f x * sixSetPivot D h x) := by
    intro x
    rw [show (Real.sqrt (1 - D.weight x) * sixSetPivot D f x)
        * (Real.sqrt (1 - D.weight x) * sixSetPivot D h x)
        = (Real.sqrt (1 - D.weight x) * Real.sqrt (1 - D.weight x))
          * (sixSetPivot D f x * sixSetPivot D h x) from by ring, hroot x]
  have hsqf : ∀ x : Fin m, (Real.sqrt (1 - D.weight x) * sixSetPivot D f x) ^ 2
      = (1 - D.weight x) * sixSetPivot D f x ^ 2 := by
    intro x
    rw [mul_pow, Real.sq_sqrt (hco x)]
  have hsqh : ∀ x : Fin m, (Real.sqrt (1 - D.weight x) * sixSetPivot D h x) ^ 2
      = (1 - D.weight x) * sixSetPivot D h x ^ 2 := by
    intro x
    rw [mul_pow, Real.sq_sqrt (hco x)]
  simp only [hprod, hsqf, hsqh] at hcs
  rw [sum_coweight_pivot_cross D hPD f h, sum_coweight_pivot_sq D hPD f,
    sum_coweight_pivot_sq D hPD h] at hcs
  exact hcs

/-! ## 3. The ledger identity -/

/-- **The refusal ledger identity.**  The four refusal slacks of a pair,
weighted by the co-weights, sum to the weighted ghost deficit of that pair.  The
proof consumes three instances of the projection identity and the co-weight
deficit, and the size `m = 6` is what makes the two sides agree exactly. -/
theorem sum_coweight_pairRefusalSlack (D : WeightedDesign 6 3) {f h : Fin 6}
    (hfh : f ≠ h) :
    ∑ x ∈ ({f, h} : Finset (Fin 6))ᶜ, (1 - D.weight x) * pairRefusalSlack D f h x
      = ghostDeficitForm D f h := by
  classical
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have hff := sum_coweight_pivot_sq D hPD f
  have hhh := sum_coweight_pivot_sq D hPD h
  have hcross := sum_coweight_pivot_cross D hPD f h
  have hdef : ∑ x, (1 - D.weight x) * (1 - sixSetPivot D x x) = 2 := by
    have h := coweight_pivot_deficit D hPD
    rw [h]; norm_num
  -- expand each summand into the four aggregates
  have hexp : ∀ x : Fin 6, (1 - D.weight x) * pairRefusalSlack D f h x
      = (1 - sixSetPivot D h h) * ((1 - D.weight x) * sixSetPivot D f x ^ 2)
        + (2 * sixSetPivot D f h)
            * ((1 - D.weight x) * (sixSetPivot D f x * sixSetPivot D h x))
        + (1 - sixSetPivot D f f) * ((1 - D.weight x) * sixSetPivot D h x ^ 2)
        + (-(pairPivotMinor D f h)) * ((1 - D.weight x) * (1 - sixSetPivot D x x)) := by
    intro x
    rw [pairRefusalSlack]
    ring
  have htotal : ∑ x, (1 - D.weight x) * pairRefusalSlack D f h x
      = (1 - sixSetPivot D h h) * sixSetPivot D f f
        + (2 * sixSetPivot D f h) * sixSetPivot D f h
        + (1 - sixSetPivot D f f) * sixSetPivot D h h
        + (-(pairPivotMinor D f h)) * 2 := by
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hexp x]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      hff, hcross, hhh, hdef]
  -- split off the two terms of the pair itself
  have hsplit : ∑ x ∈ ({f, h} : Finset (Fin 6))ᶜ, (1 - D.weight x) * pairRefusalSlack D f h x
      = (∑ x, (1 - D.weight x) * pairRefusalSlack D f h x)
        - (1 - D.weight f) * pairRefusalSlack D f h f
        - (1 - D.weight h) * pairRefusalSlack D f h h := by
    have hunion := Finset.sum_add_sum_compl ({f, h} : Finset (Fin 6))
      (fun x => (1 - D.weight x) * pairRefusalSlack D f h x)
    rw [Finset.sum_insert (by simp [hfh]), Finset.sum_singleton] at hunion
    linarith
  rw [hsplit, htotal, pairRefusalSlack, pairRefusalSlack, ghostDeficitForm,
    pairPivotMinor, sixSetPivot_comm D h f]
  ring

/-! ## 4. The refusal makes every slack nonnegative -/

/-- **An admissible pair reads a refusal on the third minor alone.**  At a tie
the triple `{f,h,x}` breaks a Sylvester minor of `I₃ − P`, and the first two are
positive, so the third gives way. -/
theorem pairRefusalSlack_nonneg_of_isTie (D : WeightedDesign 6 3) (htie : IsTie D)
    {f h x : Fin 6} (hfh : f ≠ h) (hfx : f ≠ x) (hhx : h ≠ x)
    (ha : sixSetPivot D f f < 1) (hminor : 0 < pairPivotMinor D f h) :
    0 ≤ pairRefusalSlack D f h x := by
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have hsyl := tie_refusal_sylvester D htie hPD hfh hfx hhx
  simp only [show ∀ p q : Fin 6, D.atom p ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom q)
    = sixSetPivot D p q from fun _ _ => rfl] at hsyl
  rcases hsyl with hone | hpair | hthird
  · exact absurd hone (not_le.mpr ha)
  · rw [pairPivotMinor] at hminor
    linarith
  · rw [pairRefusalSlack, pairPivotMinor]
    nlinarith [hthird]

/-! ## 5. The ledger -/

/-- **The refusal ledger.**  At a `(6,3)` tie the weighted ghost deficit of every
admissible pair is nonnegative.  Every slack is nonnegative and the co-weights
are positive, so the ledger identity transports the sign. -/
theorem ghostDeficitForm_nonneg_of_isTie (D : WeightedDesign 6 3) (htie : IsTie D)
    {f h : Fin 6} (hfh : f ≠ h) (ha : sixSetPivot D f f < 1)
    (hminor : 0 < pairPivotMinor D f h) : 0 ≤ ghostDeficitForm D f h := by
  classical
  rw [← sum_coweight_pairRefusalSlack D hfh]
  refine Finset.sum_nonneg fun x hx => ?_
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  refine mul_nonneg ?_ (pairRefusalSlack_nonneg_of_isTie D htie hfh
    (fun hc => hx.1 hc.symm) (fun hc => hx.2 hc.symm) ha hminor)
  linarith [design_weight_lt_one D (by norm_num) x]

/-- **The ledger in scalar form.**  `2(t_f + t_h)·Δ ≤ t_h(1 − P_ff) + t_f(1 − P_hh)`
at every admissible pair of a `(6,3)` tie. -/
theorem pairRefusalLedger (D : WeightedDesign 6 3) (htie : IsTie D)
    {f h : Fin 6} (hfh : f ≠ h) (ha : sixSetPivot D f f < 1)
    (hminor : 0 < pairPivotMinor D f h) :
    2 * (D.weight f + D.weight h) * pairPivotMinor D f h
      ≤ D.weight h * (1 - sixSetPivot D f f)
        + D.weight f * (1 - sixSetPivot D h h) := by
  have h := ghostDeficitForm_nonneg_of_isTie D htie hfh ha hminor
  rw [ghostDeficitForm] at h
  rw [pairPivotMinor]
  nlinarith [h]

/-- **The pair minor of a tie never reaches one half.**  The co-weights are
below one and the pivots are nonnegative. -/
theorem pairPivotMinor_le_half_of_isTie (D : WeightedDesign 6 3) (htie : IsTie D)
    {f h : Fin 6} (hfh : f ≠ h) (ha : sixSetPivot D f f < 1)
    (hminor : 0 < pairPivotMinor D f h) : pairPivotMinor D f h ≤ 1 / 2 := by
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have hled := pairRefusalLedger D htie hfh ha hminor
  have hf0 : 0 ≤ sixSetPivot D f f := sixSetPivot_self_nonneg D (by norm_num) hPD f
  have hh0 : 0 ≤ sixSetPivot D h h := sixSetPivot_self_nonneg D (by norm_num) hPD h
  have hwf := D.weight_pos f
  have hwh := D.weight_pos h
  nlinarith [hled, hf0, hh0, hwf, hwh]

/-! ## 6. The residual has no producer -/

/-- **No pair of a `(6,3)` tie is ghost-deficient.**  A deficient pair is
admissible by definition, and the ledger gives its deficit form the opposite
sign. -/
theorem not_ghostDeficitShort_of_isTie (D : WeightedDesign 6 3) (htie : IsTie D)
    {f h : Fin 6} (hfh : f ≠ h) : ¬ GhostDeficitShort D f h := by
  intro hdef
  obtain ⟨ha, hb, hminor, hbracket⟩ := hdef
  have hm : 0 < pairPivotMinor D f h := by rw [pairPivotMinor]; linarith
  have hled := ghostDeficitForm_nonneg_of_isTie D htie hfh ha hm
  rw [ghostDeficitForm] at hled
  linarith

/-- **No pair of a `(6,3)` tie carries a short ghost block.**  This strengthens
`Gtz.not_ghostBlockShort_two_selectors` from "at most one selector is short" to
"no selector is short", and it needs neither a dominator nor a corner. -/
theorem not_ghostBlockShort_of_isTie (D : WeightedDesign 6 3) (htie : IsTie D)
    {f h : Fin 6} (hfh : f ≠ h) : ¬ GhostBlockShort D f h := fun hshort =>
  not_ghostDeficitShort_of_isTie D htie hfh (ghostDeficitShort_of_ghostBlockShort D hshort)

/-- **The corner of a primitive tie is empty, or the residual fails.**  A
producer of `Gtz.NonplanarDeficitResidual` at a tie would name a deficient pair,
which the ledger forbids.  So the residual carries no information beyond the
emptiness of the corner. -/
theorem no_nonplanar_corner_of_nonplanarDeficitResidual (D : WeightedDesign 6 3)
    (htie : IsTie D) (hprimitive : IsPrimitiveDesign D)
    (hres : NonplanarDeficitResidual D) (C : Finset (Fin 6)) (hcard : C.card = 3)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ¬ (∃ d ∈ Cᶜ, D.atom d ⬝ᵥ u ≠ 0) := by
  intro hnp
  obtain ⟨e, _, f, h, hfh, _, hdef⟩ := hres htie hprimitive C hcard lam hlam u hunit hgap hnp
  exact not_ghostDeficitShort_of_isTie D htie hfh hdef

/-- **The residual IS the corner closure.**  At a primitive `(6,3)` tie the
weighted deficit residual holds exactly when no non-planar corank-two corner
exists.  The residual is therefore not a weakening of the corner problem, and no
argument that PRODUCES a deficient selector can discharge it. -/
theorem nonplanarDeficitResidual_iff_no_corner (D : WeightedDesign 6 3)
    (htie : IsTie D) (hprimitive : IsPrimitiveDesign D) :
    NonplanarDeficitResidual D
      ↔ ∀ C : Finset (Fin 6), C.card = 3 → ∀ lam : ℝ, 0 < lam → ∀ u : Fin 3 → ℝ,
          u ⬝ᵥ u = 1 → subsetSum D C - 1 = lam • atomMatrix u →
          ¬ (∃ d ∈ Cᶜ, D.atom d ⬝ᵥ u ≠ 0) := by
  constructor
  · intro hres C hcard lam hlam u hunit hgap
    exact no_nonplanar_corner_of_nonplanarDeficitResidual D htie hprimitive hres C hcard
      hlam hunit hgap
  · intro hempty _ _ C hcard lam hlam u hunit hgap hnp
    exact absurd hnp (hempty C hcard lam hlam u hunit hgap)

/-! ## 7. The pivot law of a tie -/

/-- The scalar core of the pivot law: three pairwise disjunctions of the shape
`1 ≤ 2p + q` force the three values to total at least one.  Each of the eight
branches is a linear program whose minimum is exactly one. -/
theorem sum_three_ge_one_of_pairLaw {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hpq : 1 ≤ 2 * p + q ∨ 1 ≤ 2 * q + p)
    (hpr : 1 ≤ 2 * p + r ∨ 1 ≤ 2 * r + p)
    (hqr : 1 ≤ 2 * q + r ∨ 1 ≤ 2 * r + q) : 1 ≤ p + q + r := by
  rcases hpq with h1 | h1 <;> rcases hpr with h2 | h2 <;> rcases hqr with h3 | h3 <;> linarith

/-- **The pivot law of a `(6,3)` tie.**  Every pair obeys
`1 ≤ 2·P_ff + P_hh` or `1 ≤ 2·P_hh + P_ff`, with no admissibility proviso and no
weights in the conclusion.  Three branches close it: a heavy pivot closes it
outright, an inadmissible pair closes it through Cauchy–Schwarz, and an
admissible pair closes it through the ledger. -/
theorem tie_pair_pivot_law (D : WeightedDesign 6 3) (htie : IsTie D)
    {f h : Fin 6} (hfh : f ≠ h) :
    1 ≤ 2 * sixSetPivot D f f + sixSetPivot D h h
      ∨ 1 ≤ 2 * sixSetPivot D h h + sixSetPivot D f f := by
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have hf0 : 0 ≤ sixSetPivot D f f := sixSetPivot_self_nonneg D (by norm_num) hPD f
  have hh0 : 0 ≤ sixSetPivot D h h := sixSetPivot_self_nonneg D (by norm_num) hPD h
  have hcs : sixSetPivot D f h ^ 2 ≤ sixSetPivot D f f * sixSetPivot D h h :=
    sixSetPivot_sq_le_mul D (by norm_num) hPD f h
  by_cases ha : 1 ≤ sixSetPivot D f f
  · exact Or.inl (by linarith)
  by_cases hb : 1 ≤ sixSetPivot D h h
  · exact Or.inr (by linarith)
  push_neg at ha hb
  by_cases hminor : 0 < pairPivotMinor D f h
  · -- the admissible branch: the ledger keeps one swap bracket nonnegative
    have hled := ghostDeficitForm_nonneg_of_isTie D htie hfh ha hminor
    rw [ghostDeficitForm] at hled
    have hwf := D.weight_pos f
    have hwh := D.weight_pos h
    by_cases hbf : 0 ≤ (1 - sixSetPivot D h h) * (2 * sixSetPivot D f f - 1)
        + 2 * sixSetPivot D f h ^ 2
    · exact Or.inl (by nlinarith [hcs, hbf])
    · push_neg at hbf
      have hbh : 0 ≤ (1 - sixSetPivot D f f) * (2 * sixSetPivot D h h - 1)
          + 2 * sixSetPivot D f h ^ 2 := by nlinarith [hled, hbf, hwf, hwh]
      exact Or.inr (by nlinarith [hcs, hbh])
  · -- the inadmissible branch: Cauchy–Schwarz alone
    push_neg at hminor
    rw [pairPivotMinor] at hminor
    exact Or.inl (by nlinarith [hcs, hminor, hh0])

/-- **At most one atom of a tie has pivot below one third.** -/
theorem tie_pivot_lt_third_unique (D : WeightedDesign 6 3) (htie : IsTie D)
    {f h : Fin 6} (hfh : f ≠ h) (hf : sixSetPivot D f f < 1 / 3) :
    ¬ (sixSetPivot D h h < 1 / 3) := by
  intro hh
  rcases tie_pair_pivot_law D htie hfh with hlaw | hlaw <;> linarith

/-- **Every pair of a tie carries half a unit of pivot.** -/
theorem tie_pair_pivot_sum_ge_half (D : WeightedDesign 6 3) (htie : IsTie D)
    {f h : Fin 6} (hfh : f ≠ h) :
    1 / 2 ≤ sixSetPivot D f f + sixSetPivot D h h := by
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have hf0 : 0 ≤ sixSetPivot D f f := sixSetPivot_self_nonneg D (by norm_num) hPD f
  have hh0 : 0 ≤ sixSetPivot D h h := sixSetPivot_self_nonneg D (by norm_num) hPD h
  rcases tie_pair_pivot_law D htie hfh with hlaw | hlaw <;> linarith

/-! ## 8. The light set of a tie has four atoms -/

/-- The co-weight deficit concentrated on the light set: heavy atoms contribute
nothing positive, so the light atoms must carry the whole deficit. -/
theorem two_le_sum_lightSet_coweight_deficit (D : WeightedDesign 6 3) :
    (2 : ℝ) ≤ ∑ c ∈ lightSet D, (1 - D.weight c) * (1 - sixSetPivot D c c) := by
  classical
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have hdef : ∑ c, (1 - D.weight c) * (1 - sixSetPivot D c c) = 2 := by
    have h := coweight_pivot_deficit D hPD
    rw [h]; norm_num
  have hheavy : ∑ c ∈ (lightSet D)ᶜ, (1 - D.weight c) * (1 - sixSetPivot D c c) ≤ 0 := by
    refine Finset.sum_nonpos fun c hc => ?_
    rw [Finset.mem_compl, mem_lightSet_iff, not_lt] at hc
    exact mul_nonpos_of_nonneg_of_nonpos
      (by linarith [design_weight_lt_one D (by norm_num) c]) (by linarith)
  have hsplit := Finset.sum_add_sum_compl (lightSet D)
    (fun c => (1 - D.weight c) * (1 - sixSetPivot D c c))
  linarith [hsplit, hdef, hheavy]

/-- **The pivots of the light set of a tie fall short of its size by more than
two.**  Every co-weight is strictly below one and every light co-pivot is
strictly positive. -/
theorem sum_lightSet_pivot_lt (D : WeightedDesign 6 3) :
    ∑ c ∈ lightSet D, sixSetPivot D c c < ((lightSet D).card : ℝ) - 2 := by
  classical
  have hbase := two_le_sum_lightSet_coweight_deficit D
  have hne : (lightSet D).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (lightSet D) with hemp | hne
    · rw [hemp, Finset.sum_empty] at hbase; linarith
    · exact hne
  have hstrict : ∑ c ∈ lightSet D, (1 - D.weight c) * (1 - sixSetPivot D c c)
      < ∑ c ∈ lightSet D, (1 - sixSetPivot D c c) := by
    refine Finset.sum_lt_sum_of_nonempty hne fun c hc => ?_
    rw [mem_lightSet_iff] at hc
    have hw := D.weight_pos c
    nlinarith [hc, hw]
  have hcount : ∑ c ∈ lightSet D, (1 - sixSetPivot D c c)
      = ((lightSet D).card : ℝ) - ∑ c ∈ lightSet D, sixSetPivot D c c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith [hbase, hstrict, hcount]

/-- **The light set of a `(6,3)` tie has at least four atoms.**  This sharpens
`Gtz.three_le_card_lightSet` and empties `Gtz.eq_compl_lightSet_of_card_three` at
a tie.  A three-atom light set would have pivot total below one, while the pivot
law of every one of its three pairs forces the total to at least one. -/
theorem four_le_card_lightSet_of_isTie (D : WeightedDesign 6 3) (htie : IsTie D) :
    4 ≤ (lightSet D).card := by
  classical
  have hthree := three_le_card_lightSet D
  by_contra hcon
  push_neg at hcon
  have hcard : (lightSet D).card = 3 := by omega
  obtain ⟨c1, c2, c3, h12, h13, h23, hset⟩ := Finset.card_eq_three.mp hcard
  have hsum := sum_lightSet_pivot_lt D
  rw [hcard, hset] at hsum
  rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton] at hsum
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have hlaw := sum_three_ge_one_of_pairLaw
    (sixSetPivot_self_nonneg D (by norm_num) hPD c1)
    (sixSetPivot_self_nonneg D (by norm_num) hPD c2)
    (sixSetPivot_self_nonneg D (by norm_num) hPD c3)
    (tie_pair_pivot_law D htie h12) (tie_pair_pivot_law D htie h13)
    (tie_pair_pivot_law D htie h23)
  norm_num at hsum
  linarith

/-! ## 9. The corner refusal ledger -/

/-- **The corner refusal identity.**  At a corank-two corner the refusal slacks
of a pair, summed over the complement triple with NO weights, price the corner:
the outside cross readings and the corner pivot appear and nothing else.  The
identity is unconditional — it needs only the rank-one gap. -/
theorem sum_pairRefusalSlack_compl (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) (f h : Fin 6) :
    ∑ d ∈ Cᶜ, pairRefusalSlack D f h d
      = (1 - sixSetPivot D h h) * (sixSetPivot D f f - lam * gapCross D u f ^ 2)
        + 2 * (sixSetPivot D f h
            * (sixSetPivot D f h - lam * (gapCross D u f * gapCross D u h)))
        + (1 - sixSetPivot D f f) * (sixSetPivot D h h - lam * gapCross D u h ^ 2)
        - cornerPivot D lam u * pairPivotMinor D f h := by
  classical
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have hcff := outside_pivot_compose D C hgap hPD f f
  have hchh := outside_pivot_compose D C hgap hPD h h
  have hcfh := outside_pivot_compose D C hgap hPD f h
  have hsum := outside_pivot_sum D C hgap hPD
  have hsumP : ∑ d ∈ Cᶜ, sixSetPivot D d d = 3 - cornerPivot D lam u := by
    simpa only [sixSetPivot, gapSelf, cornerPivot] using hsum
  have hcompl : (Cᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, hcard]
    simp
  have hff : ∑ d ∈ Cᶜ, sixSetPivot D f d ^ 2
      = sixSetPivot D f f - lam * (gapCross D u f * gapCross D u f) := by
    rw [← hcff]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [sixSetPivot_comm D d f]
    ring
  have hhh : ∑ d ∈ Cᶜ, sixSetPivot D h d ^ 2
      = sixSetPivot D h h - lam * (gapCross D u h * gapCross D u h) := by
    rw [← hchh]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [sixSetPivot_comm D d h]
    ring
  have hcross : ∑ d ∈ Cᶜ, sixSetPivot D f d * sixSetPivot D h d
      = sixSetPivot D f h - lam * (gapCross D u f * gapCross D u h) := by
    rw [← hcfh]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [sixSetPivot_comm D d h]
  have hone : ∑ d ∈ Cᶜ, (1 - sixSetPivot D d d) = cornerPivot D lam u := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hsumP, hcompl]
    norm_num
  have hexp : ∀ d : Fin 6, pairRefusalSlack D f h d
      = (1 - sixSetPivot D h h) * sixSetPivot D f d ^ 2
        + (2 * sixSetPivot D f h) * (sixSetPivot D f d * sixSetPivot D h d)
        + (1 - sixSetPivot D f f) * sixSetPivot D h d ^ 2
        + (-(pairPivotMinor D f h)) * (1 - sixSetPivot D d d) := by
    intro d
    rw [pairRefusalSlack]
    ring
  rw [Finset.sum_congr rfl fun d (_ : d ∈ Cᶜ) => hexp d]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    hff, hcross, hhh, hone]
  ring

/-- **The corner ledger.**  At a corank-two corner of a `(6,3)` tie the corner
pivot and the outside cross readings of an admissible pair are capped by the
pair's own co-pivots.  It is the corner half of the refusal budget, and the
weight-free half. -/
theorem corner_pairRefusal_bound (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) {f h : Fin 6}
    (hf : f ∈ C) (hh : h ∈ C) (hfh : f ≠ h) (ha : sixSetPivot D f f < 1)
    (hminor : 0 < pairPivotMinor D f h) :
    (cornerPivot D lam u + 2) * pairPivotMinor D f h
        + lam * ((1 - sixSetPivot D h h) * gapCross D u f ^ 2
          + 2 * (sixSetPivot D f h * (gapCross D u f * gapCross D u h))
          + (1 - sixSetPivot D f f) * gapCross D u h ^ 2)
      ≤ (1 - sixSetPivot D f f) + (1 - sixSetPivot D h h) := by
  classical
  have hid := sum_pairRefusalSlack_compl D C hcard hgap f h
  have hnn : 0 ≤ ∑ d ∈ Cᶜ, pairRefusalSlack D f h d := by
    refine Finset.sum_nonneg fun d hd => ?_
    rw [Finset.mem_compl] at hd
    exact pairRefusalSlack_nonneg_of_isTie D htie hfh
      (fun hc => hd (hc ▸ hf)) (fun hc => hd (hc ▸ hh)) ha hminor
  rw [hid] at hnn
  have hkey : (1 - sixSetPivot D h h) * (sixSetPivot D f f - lam * gapCross D u f ^ 2)
        + 2 * (sixSetPivot D f h
            * (sixSetPivot D f h - lam * (gapCross D u f * gapCross D u h)))
        + (1 - sixSetPivot D f f) * (sixSetPivot D h h - lam * gapCross D u h ^ 2)
        - cornerPivot D lam u * pairPivotMinor D f h
      = ((1 - sixSetPivot D f f) + (1 - sixSetPivot D h h))
        - ((cornerPivot D lam u + 2) * pairPivotMinor D f h
          + lam * ((1 - sixSetPivot D h h) * gapCross D u f ^ 2
            + 2 * (sixSetPivot D f h * (gapCross D u f * gapCross D u h))
            + (1 - sixSetPivot D f f) * gapCross D u h ^ 2)) := by
    rw [pairPivotMinor]
    ring
  linarith [hnn, hkey]

/-! ## 10. The triple pivot floor and the corner trace floor -/

/-- **Every triple of a `(6,3)` tie carries a unit of pivot.**  Three instances
of the pivot law meet in the scalar core, whose eight branches each bottom out at
exactly one. -/
theorem tie_triple_pivot_sum_ge_one (D : WeightedDesign 6 3) (htie : IsTie D)
    {r1 r2 r3 : Fin 6} (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) :
    1 ≤ sixSetPivot D r1 r1 + sixSetPivot D r2 r2 + sixSetPivot D r3 r3 := by
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  exact sum_three_ge_one_of_pairLaw
    (sixSetPivot_self_nonneg D (by norm_num) hPD r1)
    (sixSetPivot_self_nonneg D (by norm_num) hPD r2)
    (sixSetPivot_self_nonneg D (by norm_num) hPD r3)
    (tie_pair_pivot_law D htie h12) (tie_pair_pivot_law D htie h13)
    (tie_pair_pivot_law D htie h23)

/-- **The inside pivot sum of a corank-two corner.**  The dominator's atom sum is
`1 + lam·u uᵀ`, so its pivot diagonal totals the corner pivot plus the trace of
the inverse gap.  It is the inside twin of `Gtz.outside_pivot_sum`. -/
theorem inside_pivot_sum (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ∑ e ∈ C, sixSetPivot D e e
      = cornerPivot D lam u + Matrix.trace ((subsetSum D Finset.univ - 1)⁻¹) := by
  have htr := sum_subset_quadForm_eq_trace D C (subsetSum D Finset.univ - 1)⁻¹
  have hC : subsetSum D C = 1 + lam • atomMatrix u := by
    rw [← hgap]; abel
  rw [show ∑ e ∈ C, sixSetPivot D e e
      = ∑ e ∈ C, D.atom e ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom e) from rfl,
    htr, hC, Matrix.mul_add, Matrix.trace_add, Matrix.mul_one, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, trace_mul_atomMatrix, cornerPivot, gapSelf]
  ring

/-- **The corner trace floor of a tie.**  The corner pivot and the trace of the
inverse six-set gap together reach one at every corank-two corner of a `(6,3)`
tie.  The dominator is a triple, and every triple of a tie carries a unit of
pivot. -/
theorem corner_trace_floor_of_isTie (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    1 ≤ cornerPivot D lam u + Matrix.trace ((subsetSum D Finset.univ - 1)⁻¹) := by
  classical
  obtain ⟨r1, r2, r3, h12, h13, h23, hset⟩ := Finset.card_eq_three.mp hcard
  have hsum := inside_pivot_sum D C hgap
  rw [hset, Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton] at hsum
  have hfloor := tie_triple_pivot_sum_ge_one D htie h12 h13 h23
  linarith

end Gtz
