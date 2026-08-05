/-
# Branch (ii) reduced: the selection residual IS a tie exclusion, and it lives on
# one codimension-one slice

`Gtz.BalancedStratumSelection 6` is stated as a positive domination claim on the
region where three certificates have all been peeled off: no stress mass gap in
either orientation, and no triple meeting the free-mass budget.  Two facts
already in the tree collapse that shape.

* `Gtz.exists_dominating_sixThree_of_stress` -- a `(6,3)` design carrying ANY
  nonzero stress HAS a dominating triple, unconditionally.  On the balanced
  stratum the weak half of the conclusion is therefore free, and the only thing
  the residual can be about is the gap between `PosSemidef` and `PosDef`.

* `Gtz.posDef_gap_of_freeMassBudget` and
  `Gtz.sixThree_exists_posDef_triple_of_stressMassGap` -- each of the three
  peeled certificates produces a STRICT dominator when it fires, so each of them
  automatically fails at an exact tie.

Together these give `balancedStratumSelection_six_iff_noPrimitiveBalancedTie`:
the Prop is EQUIVALENT to the flat statement that no primitive `(6,3)` design
carrying a full-support stress is an exact tie.  The forward direction never
consumes the three negative hypotheses -- they are dead weight, discharged for
free at any tie by the very certificates that named them.  So a proof of branch
(ii) gains nothing from working inside the residual region, and any attempt to
close it by shrinking that region is attacking a set that carries no
information.  This is the branch-(ii) analogue of the polarity law recorded
above `Gtz.sum_det_subsetSum_sub_one_sixThree`.

The second reduction is a genuine narrowing.
`Gtz.exists_posDef_sixThree_of_stress_sum_ne_zero` supplies a STRICT dominator
whenever the stress has nonzero coordinate sum, so only stresses with
`∑ z = 0` remain: `balancedStratumSelection_six_of_zeroSumSlice`.  Dually
`Gtz.hasOnlyBalancedStress_of_isTie_sixThree` says every stress of a `(6,3)` tie
already has zero coordinate sum, so the slice is not a restriction on the tie
side either -- `noPrimitiveBalancedTie_iff_zeroSum`.  Branch (ii) is a
codimension-one question inside the balanced stratum, in both vocabularies.

## What is NOT proved here

Nothing here decides branch (ii).  It relocates it: from a positive selection
claim on a certificate-failure region to the exclusion of one geometric object,
a primitive `(6,3)` tie whose six Veronese images are dependent with all six
coefficients nonzero and summing to zero.
-/
import Mathlib
import Gtz.Design.BalancedStratum
import Gtz.Reduction.StressConditionalWalk
import Gtz.Quantitative.HingeStressNarrowing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The flat tie-exclusion statements -/

/-- **The balanced branch as a tie exclusion.**  No primitive `(6,3)` design
carrying a full-support stress is an exact tie. -/
def NoPrimitiveBalancedTieSixThree : Prop :=
  ∀ (design : WeightedDesign 6 3) (stressCoeff : Fin 6 → ℝ),
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ c, stressCoeff c ≠ 0) →
    IsPrimitiveDesign design →
    ¬ IsTie design

/-- The same exclusion restricted to stresses of vanishing coordinate sum. -/
def NoPrimitiveBalancedTieZeroSumSixThree : Prop :=
  ∀ (design : WeightedDesign 6 3) (stressCoeff : Fin 6 → ℝ),
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ c, stressCoeff c ≠ 0) →
    (∑ c, stressCoeff c) = 0 →
    IsPrimitiveDesign design →
    ¬ IsTie design

/-! ## The weak-to-strict upgrade on the balanced stratum -/

/-- **On the balanced stratum, "not a tie" already means "strictly dominated".**
The stress-conditional walk supplies a weakly dominating triple with no
hypothesis at all, so the first conjunct of `Gtz.IsTie` is discharged and the
negation of the second is exactly a strict dominator. -/
theorem exists_posDef_triple_of_stress_of_not_isTie (design : WeightedDesign 6 3)
    {stressCoeff : Fin 6 → ℝ} (hnonzero : stressCoeff ≠ 0)
    (hstress : (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0)
    (hnotTie : ¬ IsTie design) :
    ∃ triple : Finset (Fin 6), triple.card = 3
      ∧ (subsetSum design triple - 1).PosDef := by
  classical
  obtain ⟨selected, hcard, hdominates⟩ :=
    exists_dominating_sixThree_of_stress design hnonzero hstress
  by_contra hnone
  push Not at hnone
  exact hnotTie ⟨⟨selected, hcard, hdominates⟩, hnone⟩

/-- A full-support stress is in particular a nonzero one. -/
theorem stress_ne_zero_of_fullSupport {size : ℕ} {stressCoeff : Fin (size + 1) → ℝ}
    (hfull : ∀ c, stressCoeff c ≠ 0) : stressCoeff ≠ 0 :=
  fun hzero => hfull 0 (congrFun hzero 0)

/-! ## The three negative hypotheses are dead weight -/

/-- **Tie exclusion implies the selection residual, using NONE of its three
negative hypotheses.**  The three underscores are the point: the peeled
certificate region contributes nothing. -/
theorem balancedStratumSelection_six_of_noPrimitiveBalancedTie
    (hexclusion : NoPrimitiveBalancedTieSixThree) : BalancedStratumSelection 6 := by
  intro design stressCoeff hstress hfull hprimitive _ _ _
  exact exists_posDef_triple_of_stress_of_not_isTie design
    (stress_ne_zero_of_fullSupport hfull) hstress
    (hexclusion design stressCoeff hstress hfull hprimitive)

/-- **Conversely the selection residual implies tie exclusion.**  At a tie each
of the three named certificates automatically fails, because each one produces a
STRICT dominator when it fires and a tie has none. -/
theorem noPrimitiveBalancedTie_of_balancedStratumSelection_six
    (hselection : BalancedStratumSelection 6) : NoPrimitiveBalancedTieSixThree := by
  intro design stressCoeff hstress hfull hprimitive htie
  have hgapPos : ¬ HasStressMassGap design stressCoeff := by
    intro hgap
    obtain ⟨triple, hcard, hposDef⟩ :=
      sixThree_exists_posDef_triple_of_stressMassGap design hstress hfull hgap
    exact htie.2 triple hcard hposDef
  have hstressNeg : ∑ c, (-stressCoeff) c • atomMatrix (design.atom c) = 0 :=
    stress_of_neg_stress hstress
  have hfullNeg : ∀ c, (-stressCoeff) c ≠ 0 := fun c => neg_ne_zero.mpr (hfull c)
  have hgapNeg : ¬ HasStressMassGap design (-stressCoeff) := by
    intro hgap
    obtain ⟨triple, hcard, hposDef⟩ :=
      sixThree_exists_posDef_triple_of_stressMassGap design hstressNeg hfullNeg hgap
    exact htie.2 triple hcard hposDef
  have hbudget : ∀ triple : Finset (Fin 6), triple.card = 3 →
      ¬ HasFreeMassBudget design triple := by
    intro triple hcard hbud
    exact htie.2 triple hcard
      (posDef_gap_of_freeMassBudget design triple hbud.1 hbud.2)
  obtain ⟨triple, hcard, hposDef⟩ :=
    hselection design stressCoeff hstress hfull hprimitive hgapPos hgapNeg hbudget
  exact htie.2 triple hcard hposDef

/-- **THE RESIDUAL IS EXACTLY A TIE EXCLUSION.**  `Gtz.BalancedStratumSelection 6`
neither more nor less than: no primitive `(6,3)` design with a full-support
stress is an exact tie. -/
theorem balancedStratumSelection_six_iff_noPrimitiveBalancedTie :
    BalancedStratumSelection 6 ↔ NoPrimitiveBalancedTieSixThree :=
  ⟨noPrimitiveBalancedTie_of_balancedStratumSelection_six,
    balancedStratumSelection_six_of_noPrimitiveBalancedTie⟩

/-! ## The codimension-one slice -/

/-- **The zero-sum slice is no restriction on the tie side.**  Every stress of a
`(6,3)` tie has vanishing coordinate sum, so excluding ties carrying a zero-sum
full-support stress excludes them all. -/
theorem noPrimitiveBalancedTie_iff_zeroSum :
    NoPrimitiveBalancedTieSixThree ↔ NoPrimitiveBalancedTieZeroSumSixThree := by
  constructor
  · intro hexclusion design stressCoeff hstress hfull _ hprimitive htie
    exact hexclusion design stressCoeff hstress hfull hprimitive htie
  · intro hexclusion design stressCoeff hstress hfull hprimitive htie
    exact hexclusion design stressCoeff hstress hfull
      (hasOnlyBalancedStress_of_isTie_sixThree design htie stressCoeff
        (stress_ne_zero_of_fullSupport hfull) hstress)
      hprimitive htie

/-- **Branch (ii) only has to be proved on the zero-sum slice.**  Off it, a
strict dominator is already a theorem. -/
theorem balancedStratumSelection_six_of_zeroSumSlice
    (hslice : ∀ (design : WeightedDesign 6 3) (stressCoeff : Fin 6 → ℝ),
      (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
      (∀ c, stressCoeff c ≠ 0) →
      (∑ c, stressCoeff c) = 0 →
      IsPrimitiveDesign design →
      ∃ triple : Finset (Fin 6), triple.card = 3
        ∧ (subsetSum design triple - 1).PosDef) :
    BalancedStratumSelection 6 := by
  intro design stressCoeff hstress hfull hprimitive _ _ _
  by_cases hsum : (∑ c, stressCoeff c) = 0
  · exact hslice design stressCoeff hstress hfull hsum hprimitive
  · exact exists_posDef_sixThree_of_stress_sum_ne_zero design
      (stress_ne_zero_of_fullSupport hfull) hstress hsum

/-- **The composite reading.**  The whole of branch (ii) is the exclusion of one
object: a primitive `(6,3)` tie whose six rank-one atoms satisfy a dependency
with all six coefficients nonzero and summing to zero. -/
theorem balancedStratumSelection_six_of_zeroSumTieExclusion
    (hexclusion : NoPrimitiveBalancedTieZeroSumSixThree) :
    BalancedStratumSelection 6 :=
  balancedStratumSelection_six_of_noPrimitiveBalancedTie
    (noPrimitiveBalancedTie_iff_zeroSum.mpr hexclusion)

end Gtz
