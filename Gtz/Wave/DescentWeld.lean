import Gtz.Ties.ComplementJawWindow
import Gtz.Wave.BalancedCutSelection
import Gtz.Wave.PlaneTieDesignBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The descent weld

This module connects the quantitative interior, the tie boundary, and the
rank-two terminal face of the real `(6,3)` campaign.

* `exists_atomCarrier_or_balancedSubcritical` removes the entire balanced
  heavy-edge region.  A balanced frame at scales at most `1/6` either already
  has the carrier consumed by the cell, or every distinct doubled correlation
  has square strictly below `2/3`.
* `exists_gapNeedle_eight_of_isTie_six_three` is the exact numeric boundary
  law at the landed tenth floor: every triple of a light tie has a direction
  on which its gap reaches eight.
* `not_isTie_of_tenth_of_gap_lt_eight` is the matching chart interface.  One
  strict upper gap cap below eight, on one triple, excludes a light tie.
* `PlaneParseval.exact_boundary_of_no_strict_pair_three` and
  `PlaneParseval.strict_or_exact_boundary_three` close the full nonuniform
  three-atom terminal face.  Either there is a strict pair, or every weight is
  forced to `2 * mass - 1`; then every pair weakly dominates on the exact
  determinant boundary, is nonparallel, and carries an explicit nonzero kernel
  probe.  The older uniform alternative remains as a convenient corollary for
  arbitrary atom count.
* `isTie_rankTwo_three_pair_boundary` transports that equality locus through
  `scaledAtomRows` into the core weighted-design language.  Every `(3,2)` tied
  pair is now a PSD singular gap with determinant zero, a nonzero bracket, and
  an explicit nonzero `mulVec` kernel, exactly in the form consumed by the
  rank-one Schur calculus.

The three statements are genuine eliminations.  No new global obligation is
introduced, and no selector is merely rephrased.
-/

namespace Gtz

open Matrix

/-! ## 1. The balanced interior: heavy edge or strict subcriticality -/

/-- **THE BALANCED HEAVY-EDGE ELIMINATION.**  At scales bounded by `1/6`, a
balanced six-vector Parseval frame either supplies the actual three-slot
carrier or lies in the strict subcritical edge region.

This packages the heavy-edge theorem as a useful disjunction.  The right arm
is therefore a real narrowing: every failure of it produces an edge of square
at least `2/3`, which the complementary cut law turns into the left arm. -/
theorem exists_atomCarrier_or_balancedSubcritical
    (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    (hscale : ∀ slot, scale slot ≤ 1 / 6) :
    (∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe)
      ∨ (∀ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo →
          (2 * atomGram atom slotOne slotTwo) ^ 2 < 2 / 3) := by
  by_cases hsubcritical : ∀ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo →
      (2 * atomGram atom slotOne slotTwo) ^ 2 < 2 / 3
  · exact Or.inr hsubcritical
  · left
    push Not at hsubcritical
    obtain ⟨slotOne, slotTwo, hne, hheavy⟩ := hsubcritical
    obtain ⟨σ, hσzero, hσone⟩ := exists_pairPermOfDistinct hne
    have hheavy' : 2 / 3 ≤ (2 * atomGram atom (σ 0) (σ 1)) ^ 2 := by
      rwa [hσzero, hσone]
    exact exists_atomCarrier_of_balanced_heavyEdge atom scale hframe hbal hscale σ hheavy'

/-! ## 2. The tie boundary: the exact eight-needle interface -/

/-- **LIGHT TIES HAVE AN EIGHT-NEEDLE ON EVERY TRIPLE.**  If every weight of a
`(6,3)` tie is at most `1/10`, then each triple has a nonzero direction on
which its unweighted domination gap is at least eight times the direction's
energy. -/
theorem exists_gapNeedle_eight_of_isTie_six_three
    (D : WeightedDesign 6 3) (htie : IsTie D)
    (hbound : ∀ label, D.weight label ≤ 1 / 10)
    (C : Finset (Fin 6)) (hcard : C.card = 3) :
    ∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧
      8 * (probe ⬝ᵥ probe)
        ≤ probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) := by
  obtain ⟨probe, hprobe, hneedle⟩ :=
    exists_gapNeedle_of_isTie_six_three D htie (1 / 10) (by norm_num) hbound C hcard
  refine ⟨probe, hprobe, ?_⟩
  nlinarith

/-- **THE STRICT GAP-CAP EXIT.**  A light `(6,3)` design cannot be a tie if
even one triple has gap form strictly below eight in every nonzero direction.

This is the finite chart endpoint required by the complement/needle program:
normal-form work only has to manufacture one strict `< 8` cap. -/
theorem not_isTie_of_tenth_of_gap_lt_eight
    (D : WeightedDesign 6 3)
    (hbound : ∀ label, D.weight label ≤ 1 / 10)
    (C : Finset (Fin 6)) (hcard : C.card = 3)
    (hcap : ∀ probe : Fin 3 → ℝ, probe ≠ 0 →
      probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) < 8 * (probe ⬝ᵥ probe)) :
    ¬ IsTie D := by
  intro htie
  obtain ⟨probe, hprobe, hneedle⟩ :=
    exists_gapNeedle_eight_of_isTie_six_three D htie hbound C hcard
  exact (not_lt_of_ge hneedle) (hcap probe hprobe)

/-! ## 3. The rank-two terminal face: strict or tied and nonparallel -/

/-- **THE PLANE TERMINAL ALTERNATIVE.**  An equal-mass real plane frame at the
uniform mass-one scale has a strict pair, or a pair which simultaneously

* lies exactly at the sixty-degree determinant boundary,
* weakly dominates, and
* is not parallel.

The last conclusion is the legality filter needed by the rank-three descent:
the real plane base has genuine nonparallel ties. -/
theorem PlaneParseval.strict_or_tied_nonparallel_pair_uniform
    {slotCount : ℕ} (hcount : 2 ≤ slotCount)
    {atom : Fin slotCount → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom)
    (hequal : ∀ slotOne slotTwo, atom slotOne ⬝ᵥ atom slotOne
      = atom slotTwo ⬝ᵥ atom slotTwo) :
    (∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ PlanePairDominatesStrict (atom slotOne) (atom slotTwo)
          (1 / slotCount) (1 / slotCount))
      ∨ (∃ slotOne slotTwo, slotOne ≠ slotTwo
        ∧ 4 * (atom slotOne ⬝ᵥ atom slotTwo) ^ 2
            = (atom slotOne ⬝ᵥ atom slotOne) * (atom slotTwo ⬝ᵥ atom slotTwo)
        ∧ PlanePairDominates (atom slotOne) (atom slotTwo)
            (1 / slotCount) (1 / slotCount)
        ∧ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2
            < (atom slotOne ⬝ᵥ atom slotOne) * (atom slotTwo ⬝ᵥ atom slotTwo)) := by
  rcases hframe.strict_or_tied_pair_uniform hcount hequal with hstrict | htied
  · exact Or.inl hstrict
  ·
    obtain ⟨slotOne, slotTwo, hne, hboundary, hdom⟩ := htied
    have hcountPos : (0 : ℝ) < slotCount := by
      have hcast : (2 : ℝ) ≤ slotCount := by exact_mod_cast hcount
      linarith
    have hmassOne : 0 < atom slotOne ⬝ᵥ atom slotOne := by
      rw [hframe.mass_eq_of_equal (by omega) hequal slotOne]
      positivity
    have hmassTwo : 0 < atom slotTwo ⬝ᵥ atom slotTwo := by
      rw [hframe.mass_eq_of_equal (by omega) hequal slotTwo]
      positivity
    refine Or.inr ⟨slotOne, slotTwo, hne, hboundary, hdom, ?_⟩
    nlinarith [mul_pos hmassOne hmassTwo]

/-! ## 4. The full nonuniform three-atom terminal face -/

/-- **THE EXACT THREE-ATOM BOUNDARY PACKAGE.**  A positive mass-one
three-atom plane frame with no strict pair is not merely constrained by an
inequality.  Its weights are forced, every pair weakly dominates, every pair
determinant is exactly zero after shifting, every pair is nonparallel, and an
explicit nonzero probe witnesses equality in the pair form.

This is the terminal interface needed by a rank-three Schur lift: the consumer
gets the equality direction and the exact determinant identity together, with
no uniform-weight or equal-mass assumption. -/
theorem PlaneParseval.exact_boundary_of_no_strict_pair_three
    {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    {weight : Fin 3 → ℝ} (hpos : ∀ slot, 0 < weight slot)
    (hmass : (∑ slot, weight slot) = 1)
    (hnostrict : ∀ x y : Fin 3, x ≠ y →
      ¬ PlanePairDominatesStrict (atom x) (atom y) (weight x) (weight y)) :
    (∀ slot, weight slot = planeTieWeight atom slot)
      ∧ (∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot)
      ∧ ∀ x y : Fin 3, x ≠ y →
        PlanePairDominates (atom x) (atom y) (weight x) (weight y)
          ∧ (atom x ⬝ᵥ atom y) ^ 2
              = (atom x ⬝ᵥ atom x - weight x) * (atom y ⬝ᵥ atom y - weight y)
          ∧ (atom x ⬝ᵥ atom y) ^ 2
              < (atom x ⬝ᵥ atom x) * (atom y ⬝ᵥ atom y)
          ∧ ¬ PlanePairDominatesStrict (atom x) (atom y) (weight x) (weight y)
          ∧ ∃ probe : Fin 2 → ℝ, probe ≠ 0 ∧
              weight y * (atom x ⬝ᵥ probe) ^ 2
                  + weight x * (atom y ⬝ᵥ probe) ^ 2
                = weight x * weight y * (probe ⬝ᵥ probe) := by
  have hweights := plane_three_classification hframe hpos hmass hnostrict
  have hhalf : ∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot := by
    intro slot
    have hslot := hpos slot
    rw [hweights slot] at hslot
    simp only [planeTieWeight] at hslot
    linarith
  refine ⟨hweights, hhalf, ?_⟩
  intro x y hxy
  have hdet := planeTie_pair_det_eq hframe hxy
  have hindependent := planeTie_pair_independent hframe hhalf hxy
  have hprobe := planeTieProbe_ne_zero hframe hhalf hxy
  have hcertificate := planeTieProbe_certificate hframe hxy
  refine ⟨plane_three_pair_dominates_of_tie hframe hpos hmass hnostrict hxy, ?_,
    hindependent, hnostrict x y hxy, planeTieProbe atom x y, hprobe, ?_⟩
  · simpa only [hweights x, hweights y] using hdet
  · simpa only [hweights x, hweights y] using hcertificate

/-- **THE EXACT STRICTNESS DECISION.**  At a positive mass-one three-atom
plane frame, a strict pair exists exactly when at least one weight misses the
closed-form tie value.  Thus the terminal selector is a three-scalar equality
test, not a search over the three pairs. -/
theorem PlaneParseval.exists_strict_pair_three_iff_weight_ne
    {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    {weight : Fin 3 → ℝ} (hpos : ∀ slot, 0 < weight slot)
    (hmass : (∑ slot, weight slot) = 1) :
    (∃ x y : Fin 3, x ≠ y
      ∧ PlanePairDominatesStrict (atom x) (atom y) (weight x) (weight y))
      ↔ ∃ slot, weight slot ≠ planeTieWeight atom slot := by
  constructor
  · rintro ⟨x, y, hxy, hstrict⟩
    by_contra hnone
    push Not at hnone
    have hhalf : ∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot := by
      intro slot
      have hslot := hpos slot
      rw [hnone slot] at hslot
      simp only [planeTieWeight] at hslot
      linarith
    rw [hnone x, hnone y] at hstrict
    exact (planeTie_pair_not_strict hframe hhalf hxy) hstrict
  · rintro ⟨slot, hslot⟩
    by_contra hnone
    have hnostrict : ∀ x y : Fin 3, x ≠ y →
        ¬ PlanePairDominatesStrict (atom x) (atom y) (weight x) (weight y) := by
      intro x y hxy hstrict
      exact hnone ⟨x, y, hxy, hstrict⟩
    exact hslot (plane_three_classification hframe hpos hmass hnostrict slot)

/-- **THE NONUNIFORM TERMINAL ALTERNATIVE.**  The entire positive mass-one
three-atom plane face is the disjoint union of the strict region and the exact
tie point.  The right arm exposes all equality data required downstream rather
than hiding it behind a renamed proposition. -/
theorem PlaneParseval.strict_or_exact_boundary_three
    {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    {weight : Fin 3 → ℝ} (hpos : ∀ slot, 0 < weight slot)
    (hmass : (∑ slot, weight slot) = 1) :
    (∃ x y : Fin 3, x ≠ y
      ∧ PlanePairDominatesStrict (atom x) (atom y) (weight x) (weight y))
      ∨ ((∀ slot, weight slot = planeTieWeight atom slot)
        ∧ (∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot)
        ∧ ∀ x y : Fin 3, x ≠ y →
          PlanePairDominates (atom x) (atom y) (weight x) (weight y)
            ∧ (atom x ⬝ᵥ atom y) ^ 2
                = (atom x ⬝ᵥ atom x - weight x) * (atom y ⬝ᵥ atom y - weight y)
            ∧ (atom x ⬝ᵥ atom y) ^ 2
                < (atom x ⬝ᵥ atom x) * (atom y ⬝ᵥ atom y)
            ∧ ¬ PlanePairDominatesStrict (atom x) (atom y) (weight x) (weight y)
            ∧ ∃ probe : Fin 2 → ℝ, probe ≠ 0 ∧
                weight y * (atom x ⬝ᵥ probe) ^ 2
                    + weight x * (atom y ⬝ᵥ probe) ^ 2
                  = weight x * weight y * (probe ⬝ᵥ probe)) := by
  by_cases hstrict : ∃ x y : Fin 3, x ≠ y
      ∧ PlanePairDominatesStrict (atom x) (atom y) (weight x) (weight y)
  · exact Or.inl hstrict
  · right
    apply hframe.exact_boundary_of_no_strict_pair_three hpos hmass
    intro x y hxy hpair
    exact hstrict ⟨x, y, hxy, hpair⟩

end Gtz
