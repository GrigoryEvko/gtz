import Gtz.Ties.ComplementJawWindow
import Gtz.Wave.BalancedCutSelection
import Gtz.Wave.PlanePairCriterion

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
* `PlaneParseval.strict_or_tied_nonparallel_pair_uniform` records the terminal
  real-plane alternative.  At equal mass and total scale one there is a strict
  pair, or a weakly dominating sixty-degree pair which is nonparallel.  Thus a
  rank-three tie-confinement proof cannot finish with rank-blind pair rigidity.

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

end Gtz
