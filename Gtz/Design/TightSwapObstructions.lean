/-
# Tight-swap obstructions: the tie side, collapsed to two dimensions

A weak dominator that is not strictly dominating carries a TIGHT DIRECTION --
a unit null vector of its gap.  This module reads everything that direction
forces.  The payoff is the ONE-SLOT SWAP: replacing a single dominator member
by an outside atom, the three-dimensional plane cover of
`posDef_of_normalSurplus_planeCover` collapses to a comparison between the
dominator's OWN gap form and a single rank-one square, because the tightness
antecedent kills every trace of the two retained members (square identity
`sum (a_s . v)^2 = 1` and cross identity `sum (a_s . v)(a_s . p) = 0`).

The tie side then reads: a design with NO strictly dominating card-3 subset
must refuse all three one-slot swaps of any weak dominator, and the surplus
premise of those refusals is discharged -- weighted Parseval always produces an
outside atom over-reading the tight direction.  Where
`isTie_yields_planeCover_failure` quantifies over all card-3 subsets and all
unit normals, `noStrictDominator_yields_overReaderRefusals` is THREE
two-dimensional inequalities.

SCOPE (exact-arithmetic record, do not lose): the swap family is NOT
exhaustive.  There are heavy one-line designs whose strict dominators all sit
at Hamming distance two or three from the weak dominator, so "some one-slot
swap works" is STRICTLY STRONGER than the class obligation -- it is not a
sharpening of it, and must never be registered as one.  The witness at the end
of this file shows the family is not empty either: at the only exact in-scope
fixture that fires the tightness antecedent, the swap `{3,4,5} -> {0,3,4}`
strictly dominates.
-/
import Gtz.Design.LineClassObstructions

set_option maxHeartbeats 4000000

namespace Gtz
open Matrix

/-! ## Step 1: the tight-direction data -/

/-- A tight direction is a null vector of the dominator's gap. -/
theorem tightDirection_mem_gapKernel {size : ℕ} (design : WeightedDesign size 3)
    (dominator : Finset (Fin size)) (tightDir : Fin 3 → ℝ)
    (hdominates : Dominates design dominator)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0) :
    (subsetSum design dominator - 1) *ᵥ tightDir = 0 :=
  (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hdominates tightDir).mp
    (by rw [star_trivial]; exact htight)

/-- **The tight cross identity.**  Against any probe orthogonal to the tight
direction, the dominator's atom readings pair to zero.  This is the polarized
half of the tightness antecedent, and it is what makes a one-slot swap collapse. -/
theorem tightDirection_crossReadings_vanish {size : ℕ} (design : WeightedDesign size 3)
    (dominator : Finset (Fin size)) (tightDir probe : Fin 3 → ℝ)
    (hdominates : Dominates design dominator)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0)
    (hprobeFlat : probe ⬝ᵥ tightDir = 0) :
    ∑ dominatorLabel ∈ dominator,
        (design.atom dominatorLabel ⬝ᵥ probe) * (design.atom dominatorLabel ⬝ᵥ tightDir) = 0 := by
  have hkernel := tightDirection_mem_gapKernel design dominator tightDir hdominates htight
  have hpaired : probe ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0 := by
    rw [hkernel, dotProduct_zero]
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    subsetSum_bilinearForm_eq_sum_mul, hprobeFlat, sub_zero] at hpaired
  exact hpaired

/-- **The tight square identity.**  A unit tight direction's readings from the
dominator square-sum to exactly one. -/
theorem tightDirection_squareReadings_eq_one {size : ℕ} (design : WeightedDesign size 3)
    (dominator : Finset (Fin size)) (tightDir : Fin 3 → ℝ)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0) :
    ∑ dominatorLabel ∈ dominator, (design.atom dominatorLabel ⬝ᵥ tightDir) ^ 2 = 1 := by
  rw [dominationGap_form, hunit, sub_eq_zero] at htight
  exact htight

/-- Every dominator atom under-covers a unit tight direction. -/
theorem tightDirection_memberReading_le_one {size : ℕ} (design : WeightedDesign size 3)
    (dominator : Finset (Fin size)) (tightDir : Fin 3 → ℝ)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0)
    {memberLabel : Fin size} (hmem : memberLabel ∈ dominator) :
    (design.atom memberLabel ⬝ᵥ tightDir) ^ 2 ≤ 1 := by
  have hsum := tightDirection_squareReadings_eq_one design dominator tightDir hunit htight
  have hsingle : (design.atom memberLabel ⬝ᵥ tightDir) ^ 2
      ≤ ∑ dominatorLabel ∈ dominator, (design.atom dominatorLabel ⬝ᵥ tightDir) ^ 2 :=
    Finset.single_le_sum
      (f := fun dominatorLabel => (design.atom dominatorLabel ⬝ᵥ tightDir) ^ 2)
      (fun dominatorLabel _ => sq_nonneg _) hmem
  linarith


/-! ## Step 2: the one-slot swap -/

/-- Reading a sum over the one-slot swap of a subset. -/
theorem sum_over_tightSwap {size : ℕ} (dominator : Finset (Fin size))
    (swapOut swapIn : Fin size) (hmemOut : swapOut ∈ dominator)
    (hnotMemIn : swapIn ∉ dominator) (readings : Fin size → ℝ) :
    ∑ label ∈ insert swapIn (dominator.erase swapOut), readings label
      = readings swapIn + (∑ label ∈ dominator, readings label) - readings swapOut := by
  have hnotErase : swapIn ∉ dominator.erase swapOut := fun hmem =>
    hnotMemIn (Finset.mem_of_mem_erase hmem)
  rw [Finset.sum_insert hnotErase]
  have herase : ∑ label ∈ dominator.erase swapOut, readings label
      = (∑ label ∈ dominator, readings label) - readings swapOut := by
    rw [eq_sub_iff_add_eq]
    exact Finset.sum_erase_add dominator readings hmemOut
  rw [herase]
  ring

/-- The one-slot swap keeps the cardinality. -/
theorem card_tightSwap {size : ℕ} (dominator : Finset (Fin size))
    (swapOut swapIn : Fin size) (hmemOut : swapOut ∈ dominator)
    (hnotMemIn : swapIn ∉ dominator) :
    (insert swapIn (dominator.erase swapOut)).card = dominator.card := by
  have hnotErase : swapIn ∉ dominator.erase swapOut := fun hmem =>
    hnotMemIn (Finset.mem_of_mem_erase hmem)
  have hpos : 1 ≤ dominator.card := Finset.card_pos.mpr ⟨swapOut, hmemOut⟩
  rw [Finset.card_insert_of_notMem hnotErase, Finset.card_erase_of_mem hmemOut]
  omega

/-- **The tight-swap collapse.**  At the TIGHT DIRECTION of a weak dominator, the
three-dimensional plane cover of a one-slot swap of that dominator collapses to a
comparison between the dominator's OWN gap form and a single rank-one square
built from the two swapped atoms.  Every trace of the two retained dominator
atoms cancels: the tightness antecedent supplies both the square identity
`Sigma (a_s . v)^2 = 1` and the cross identity `Sigma (a_s . v)(a_s . p) = 0`. -/
theorem tightSwap_planeCover_iff_dominatorGapExcess {size : ℕ}
    (design : WeightedDesign size 3) (dominator : Finset (Fin size))
    (swapOut swapIn : Fin size) (tightDir probe : Fin 3 → ℝ)
    (hmemOut : swapOut ∈ dominator) (hnotMemIn : swapIn ∉ dominator)
    (hdominates : Dominates design dominator)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0)
    (hprobeFlat : probe ⬝ᵥ tightDir = 0) :
    ((∑ selectedLabel ∈ insert swapIn (dominator.erase swapOut),
          (design.atom selectedLabel ⬝ᵥ probe) * (design.atom selectedLabel ⬝ᵥ tightDir)) ^ 2
        < ((∑ selectedLabel ∈ insert swapIn (dominator.erase swapOut),
              (design.atom selectedLabel ⬝ᵥ tightDir) ^ 2) - 1)
          * ((∑ selectedLabel ∈ insert swapIn (dominator.erase swapOut),
                (design.atom selectedLabel ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe))
      ↔ ((design.atom swapIn ⬝ᵥ tightDir) * (design.atom swapOut ⬝ᵥ probe)
            - (design.atom swapOut ⬝ᵥ tightDir) * (design.atom swapIn ⬝ᵥ probe)) ^ 2
          < ((design.atom swapIn ⬝ᵥ tightDir) ^ 2 - (design.atom swapOut ⬝ᵥ tightDir) ^ 2)
            * (probe ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ probe)) := by
  rw [sum_over_tightSwap dominator swapOut swapIn hmemOut hnotMemIn
        (fun label => (design.atom label ⬝ᵥ probe) * (design.atom label ⬝ᵥ tightDir)),
    sum_over_tightSwap dominator swapOut swapIn hmemOut hnotMemIn
      (fun label => (design.atom label ⬝ᵥ tightDir) ^ 2),
    sum_over_tightSwap dominator swapOut swapIn hmemOut hnotMemIn
      (fun label => (design.atom label ⬝ᵥ probe) ^ 2),
    tightDirection_crossReadings_vanish design dominator tightDir probe hdominates htight
      hprobeFlat,
    tightDirection_squareReadings_eq_one design dominator tightDir hunit htight,
    dominationGap_form]
  constructor
  · intro hcover
    nlinarith [hcover]
  · intro hexcess
    nlinarith [hexcess]

/-! ## Step 3: the swap producer and the swap obstruction -/

/-- **The tight-swap producer.**  A one-slot swap of a weak dominator whose
incoming atom out-reads the outgoing atom along the tight direction, and whose
rank-one swap square is beaten by the dominator's own gap form on the tight
direction's orthogonal plane, has a POSITIVE DEFINITE gap. -/
theorem posDef_of_tightSwap_dominatorGapExcess {size : ℕ} (design : WeightedDesign size 3)
    (dominator : Finset (Fin size)) (swapOut swapIn : Fin size) (tightDir : Fin 3 → ℝ)
    (hmemOut : swapOut ∈ dominator) (hnotMemIn : swapIn ∉ dominator)
    (hdominates : Dominates design dominator)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0)
    (hswapSurplus :
      (design.atom swapOut ⬝ᵥ tightDir) ^ 2 < (design.atom swapIn ⬝ᵥ tightDir) ^ 2)
    (hgapExcess : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ tightDir = 0 → probe ≠ 0 →
      ((design.atom swapIn ⬝ᵥ tightDir) * (design.atom swapOut ⬝ᵥ probe)
          - (design.atom swapOut ⬝ᵥ tightDir) * (design.atom swapIn ⬝ᵥ probe)) ^ 2
        < ((design.atom swapIn ⬝ᵥ tightDir) ^ 2 - (design.atom swapOut ⬝ᵥ tightDir) ^ 2)
          * (probe ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ probe))) :
    (subsetSum design (insert swapIn (dominator.erase swapOut)) - 1).PosDef := by
  refine posDef_of_normalSurplus_planeCover design
    (insert swapIn (dominator.erase swapOut)) tightDir hunit ?_ ?_
  · rw [sum_over_tightSwap dominator swapOut swapIn hmemOut hnotMemIn
        (fun label => (design.atom label ⬝ᵥ tightDir) ^ 2),
      tightDirection_squareReadings_eq_one design dominator tightDir hunit htight]
    linarith
  · intro probe hprobeFlat hprobeNe
    rw [tightSwap_planeCover_iff_dominatorGapExcess design dominator swapOut swapIn
      tightDir probe hmemOut hnotMemIn hdominates hunit htight hprobeFlat]
    exact hgapExcess probe hprobeFlat hprobeNe

/-- **The corank obstruction.**  If the dominator's gap is degenerate in a second
direction inside the tight direction's plane, then NO one-slot swap of that
dominator strictly dominates -- for any incoming atom and any outgoing slot.
Corank two on the gap kills the entire swap family at once. -/
theorem tightSwap_not_posDef_of_degenerateDominatorGap {size : ℕ}
    (design : WeightedDesign size 3) (dominator : Finset (Fin size))
    (swapOut swapIn : Fin size) (tightDir probe : Fin 3 → ℝ)
    (hmemOut : swapOut ∈ dominator) (hnotMemIn : swapIn ∉ dominator)
    (hdominates : Dominates design dominator)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0)
    (hprobeFlat : probe ⬝ᵥ tightDir = 0) (hprobeNe : probe ≠ 0)
    (hdegenerate : probe ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ probe) = 0) :
    ¬ (subsetSum design (insert swapIn (dominator.erase swapOut)) - 1).PosDef := by
  intro hposDef
  have hcover := (normalSurplus_planeCover_of_posDef design
    (insert swapIn (dominator.erase swapOut)) tightDir hunit hposDef).2 probe hprobeFlat hprobeNe
  rw [tightSwap_planeCover_iff_dominatorGapExcess design dominator swapOut swapIn
    tightDir probe hmemOut hnotMemIn hdominates hunit htight hprobeFlat,
    hdegenerate, mul_zero] at hcover
  exact absurd hcover (not_lt.mpr (sq_nonneg _))

/-! ## Step 4: the free surplus witness -/

/-- **Some atom outside the dominator strictly over-reads the tight direction.**
Pattern-free and heaviness-free: the tight identity caps every dominator atom at
one, at least one dominator atom is strictly below one because three nonnegative
readings sum to one, and then weighted Parseval forces some atom of the whole
design above one.  That atom cannot be in the dominator. -/
theorem exists_outsideAtom_overreads_tightDirection {size : ℕ}
    (design : WeightedDesign size 3) (dominator : Finset (Fin size))
    (tightDir : Fin 3 → ℝ) (hcardTwo : 2 ≤ dominator.card)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0) :
    ∃ overLabel : Fin size, overLabel ∉ dominator ∧
      1 < (design.atom overLabel ⬝ᵥ tightDir) ^ 2 := by
  have hsum := tightDirection_squareReadings_eq_one design dominator tightDir hunit htight
  have hmemberLe : ∀ memberLabel ∈ dominator,
      (design.atom memberLabel ⬝ᵥ tightDir) ^ 2 ≤ 1 := fun memberLabel hmem =>
    tightDirection_memberReading_le_one design dominator tightDir hunit htight hmem
  -- some dominator atom is STRICTLY below one
  have hstrictMember : ∃ slackLabel ∈ dominator,
      (design.atom slackLabel ⬝ᵥ tightDir) ^ 2 < 1 := by
    by_contra hnone
    push Not at hnone
    have hge : (dominator.card : ℝ)
        ≤ ∑ dominatorLabel ∈ dominator, (design.atom dominatorLabel ⬝ᵥ tightDir) ^ 2 := by
      calc (dominator.card : ℝ) = ∑ _dominatorLabel ∈ dominator, (1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum hnone
    have hcardReal : (2 : ℝ) ≤ (dominator.card : ℝ) := by exact_mod_cast hcardTwo
    linarith [hsum ▸ hge]
  obtain ⟨slackLabel, hslackMem, hslackLt⟩ := hstrictMember
  by_contra hnone
  push Not at hnone
  have hallLe : ∀ label : Fin size, (design.atom label ⬝ᵥ tightDir) ^ 2 ≤ 1 := by
    intro label
    by_cases hmem : label ∈ dominator
    · exact hmemberLe label hmem
    · exact hnone label hmem
  have hparseval := parseval_weighted_sum_sq design tightDir
  rw [hunit] at hparseval
  have hstrict : ∑ label : Fin size, design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2
      < ∑ label : Fin size, design.weight label := by
    refine Finset.sum_lt_sum (fun label _ => ?_) ⟨slackLabel, Finset.mem_univ slackLabel, ?_⟩
    · nlinarith [design.weight_pos label, hallLe label]
    · nlinarith [design.weight_pos slackLabel]
  rw [design.weight_sum_one, hparseval] at hstrict
  exact lt_irrefl 1 hstrict

/-! ## Step 6: the swap, decided -/

/-- **The one-slot swap, decided.**  At the tight direction, a one-slot swap of a
weak dominator strictly dominates IF AND ONLY IF the incoming atom out-reads the
outgoing atom along the tight direction and the rank-one swap square is beaten by
the dominator's own gap form.  NOTE (exact-arithmetic record): the swap family is
NOT exhaustive -- there are heavy one-line designs with a singular card-3 weak
dominator whose strict dominators are all at Hamming distance two or three from
that dominator, so "some one-slot swap works" is a STRICTLY STRONGER statement
than the class obligation, not a sharpening of it. -/
theorem tightSwap_posDef_iff_surplus_and_gapExcess {size : ℕ}
    (design : WeightedDesign size 3) (dominator : Finset (Fin size))
    (swapOut swapIn : Fin size) (tightDir : Fin 3 → ℝ)
    (hmemOut : swapOut ∈ dominator) (hnotMemIn : swapIn ∉ dominator)
    (hdominates : Dominates design dominator)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0) :
    (subsetSum design (insert swapIn (dominator.erase swapOut)) - 1).PosDef
      ↔ ((design.atom swapOut ⬝ᵥ tightDir) ^ 2 < (design.atom swapIn ⬝ᵥ tightDir) ^ 2 ∧
        ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ tightDir = 0 → probe ≠ 0 →
          ((design.atom swapIn ⬝ᵥ tightDir) * (design.atom swapOut ⬝ᵥ probe)
              - (design.atom swapOut ⬝ᵥ tightDir) * (design.atom swapIn ⬝ᵥ probe)) ^ 2
            < ((design.atom swapIn ⬝ᵥ tightDir) ^ 2 - (design.atom swapOut ⬝ᵥ tightDir) ^ 2)
              * (probe ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ probe))) := by
  constructor
  · intro hposDef
    obtain ⟨hsurplus, hcover⟩ := normalSurplus_planeCover_of_posDef design
      (insert swapIn (dominator.erase swapOut)) tightDir hunit hposDef
    rw [sum_over_tightSwap dominator swapOut swapIn hmemOut hnotMemIn
        (fun label => (design.atom label ⬝ᵥ tightDir) ^ 2),
      tightDirection_squareReadings_eq_one design dominator tightDir hunit htight] at hsurplus
    refine ⟨by linarith, fun probe hprobeFlat hprobeNe => ?_⟩
    exact (tightSwap_planeCover_iff_dominatorGapExcess design dominator swapOut swapIn
      tightDir probe hmemOut hnotMemIn hdominates hunit htight hprobeFlat).mp
      (hcover probe hprobeFlat hprobeNe)
  · rintro ⟨hswapSurplus, hgapExcess⟩
    exact posDef_of_tightSwap_dominatorGapExcess design dominator swapOut swapIn tightDir
      hmemOut hnotMemIn hdominates hunit htight hswapSurplus hgapExcess

/-! ## Step 7: the tie side -- the refusal family, collapsed to two dimensions -/

/-- **A tie must refuse every one-slot swap, and its refusal is
two-dimensional.**  Where `isTie_yields_planeCover_failure` quantifies a refusal
over all card-three subsets and all unit normals, this states the refusal at the
tight direction only, for a one-slot swap, and with the two retained dominator
atoms eliminated: the refusing probe compares the DOMINATOR'S OWN gap form
against a single rank-one square. -/
theorem noStrictDominator_yields_tightSwapExcess_failure {size : ℕ}
    (design : WeightedDesign size 3) (dominator : Finset (Fin size))
    (swapOut swapIn : Fin size) (tightDir : Fin 3 → ℝ)
    (hcard : dominator.card = 3)
    (hmemOut : swapOut ∈ dominator) (hnotMemIn : swapIn ∉ dominator)
    (hdominates : Dominates design dominator)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0)
    (hswapSurplus :
      (design.atom swapOut ⬝ᵥ tightDir) ^ 2 < (design.atom swapIn ⬝ᵥ tightDir) ^ 2)
    (hnoStrict : ∀ selected : Finset (Fin size), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    ∃ probe : Fin 3 → ℝ, probe ⬝ᵥ tightDir = 0 ∧ probe ≠ 0 ∧
      ((design.atom swapIn ⬝ᵥ tightDir) ^ 2 - (design.atom swapOut ⬝ᵥ tightDir) ^ 2)
          * (probe ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ probe))
        ≤ ((design.atom swapIn ⬝ᵥ tightDir) * (design.atom swapOut ⬝ᵥ probe)
            - (design.atom swapOut ⬝ᵥ tightDir) * (design.atom swapIn ⬝ᵥ probe)) ^ 2 := by
  by_contra hnone
  push Not at hnone
  refine hnoStrict (insert swapIn (dominator.erase swapOut)) ?_
    (posDef_of_tightSwap_dominatorGapExcess design dominator swapOut swapIn tightDir
      hmemOut hnotMemIn hdominates hunit htight hswapSurplus
      (fun probe hprobeFlat hprobeNe => hnone probe hprobeFlat hprobeNe))
  rw [card_tightSwap dominator swapOut swapIn hmemOut hnotMemIn]
  exact hcard

/-- **The refusal family a tie actually has to carry.**  The surplus hypothesis
is discharged: the antecedents produce an outside atom over-reading the tight
direction, and every dominator member under-reads it, so the reading difference
is automatically positive.  What survives is exactly THREE inequalities -- one
per dominator slot -- each a two-dimensional comparison inside the tight
direction's orthogonal plane. -/
theorem noStrictDominator_yields_overReaderRefusals {size : ℕ}
    (design : WeightedDesign size 3) (dominator : Finset (Fin size))
    (tightDir : Fin 3 → ℝ)
    (hcard : dominator.card = 3)
    (hdominates : Dominates design dominator)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0)
    (hnoStrict : ∀ selected : Finset (Fin size), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    ∃ overLabel : Fin size, overLabel ∉ dominator ∧
      1 < (design.atom overLabel ⬝ᵥ tightDir) ^ 2 ∧
      ∀ swapOut ∈ dominator, ∃ probe : Fin 3 → ℝ, probe ⬝ᵥ tightDir = 0 ∧ probe ≠ 0 ∧
        ((design.atom overLabel ⬝ᵥ tightDir) ^ 2
            - (design.atom swapOut ⬝ᵥ tightDir) ^ 2)
            * (probe ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ probe))
          ≤ ((design.atom overLabel ⬝ᵥ tightDir) * (design.atom swapOut ⬝ᵥ probe)
              - (design.atom swapOut ⬝ᵥ tightDir)
                * (design.atom overLabel ⬝ᵥ probe)) ^ 2 := by
  have hcardTwo : 2 ≤ dominator.card := by rw [hcard]; norm_num
  obtain ⟨overLabel, hnotMem, hover⟩ :=
    exists_outsideAtom_overreads_tightDirection design dominator tightDir hcardTwo
      hunit htight
  refine ⟨overLabel, hnotMem, hover, fun swapOut hmemOut => ?_⟩
  have hmemberLe := tightDirection_memberReading_le_one design dominator tightDir
    hunit htight hmemOut
  exact noStrictDominator_yields_tightSwapExcess_failure design dominator swapOut
    overLabel tightDir hcard hmemOut hnotMem hdominates hunit htight
    (by linarith) hnoStrict


/-! # Corroboration: the tight-swap family is non-empty at the only exact
in-scope witness.

Atoms and weights are transcribed from the R4 lane's exact rational witness
(re-verified independently here).  The free triple `{3,4,5}` weakly dominates
with a SINGULAR gap `diag(7/2, 0, 17)` and unit tight direction `(0,1,0)`, so
this design fires the antecedent of the class obligation.  The claim proved
below is that the ONE-SLOT SWAP `{3,4,5} -> {0,3,4}` (drop 5, take the line
atom 0) strictly dominates. -/

noncomputable def swapWitnessAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![9 / 2, 2, 0]
  | 1 => ![-(9 / 2), 2, 0]
  | 2 => ![0, 1, 0]
  | 3 => ![0, 1 / 3, 4]
  | 4 => ![3 / 2, -(2 / 3), 1]
  | 5 => ![-(3 / 2), -(2 / 3), 1]

noncomputable def swapWitnessWeight : Fin 6 → ℝ
  | 0 => 1 / 54
  | 1 => 1 / 54
  | 2 => 43 / 54
  | 3 => 1 / 18
  | 4 => 1 / 18
  | 5 => 1 / 18

noncomputable def swapWitnessDesign : WeightedDesign 6 3 where
  atom := swapWitnessAtom
  weight := swapWitnessWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [swapWitnessWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [swapWitnessWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [swapWitnessAtom, swapWitnessWeight, atomMatrix] <;> norm_num

theorem swapWitnessDesign_hasLinePattern :
    HasLinePattern swapWitnessDesign (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by
  intro firstLabel secondLabel thirdLabel hfirstSecond hfirstThird hsecondThird
  fin_cases firstLabel <;> fin_cases secondLabel <;> fin_cases thirdLabel <;>
    first
      | exact absurd rfl hfirstSecond
      | exact absurd rfl hfirstThird
      | exact absurd rfl hsecondThird
      | exact Iff.intro
          (fun _ => by decide)
          (by norm_num [atomBracket, tripleBracket_eq, swapWitnessDesign,
            swapWitnessAtom, Matrix.cons_val_two])
      | exact Iff.intro
          (by norm_num [atomBracket, tripleBracket_eq, swapWitnessDesign,
            swapWitnessAtom, Matrix.cons_val_two])
          (by decide)

theorem swapWitnessDesign_isHeavy (label : Fin 6) :
    1 ≤ leverageOf (swapWitnessDesign.atom label) := by
  fin_cases label <;>
    simp [leverageOf, Fin.sum_univ_three, swapWitnessDesign, swapWitnessAtom] <;> norm_num

theorem swapWitness_freeTripleGap_form (vecArg : Fin 3 → ℝ) :
    vecArg ⬝ᵥ ((subsetSum swapWitnessDesign {3, 4, 5} - 1) *ᵥ vecArg)
      = 7 / 2 * vecArg 0 ^ 2 + 17 * vecArg 2 ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [swapWitnessDesign, swapWitnessAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

theorem swapWitness_dominates_freeTriple :
    Dominates swapWitnessDesign ({3, 4, 5} : Finset (Fin 6)) := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg => ?_⟩
  · exact ((Matrix.posSemidef_sum ({3, 4, 5} : Finset (Fin 6)) fun freeLabel _ =>
      posSemidef_atomMatrix (swapWitnessDesign.atom freeLabel)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, swapWitness_freeTripleGap_form]
    positivity

theorem swapWitness_tightDirection_isUnit :
    (![0, 1, 0] : Fin 3 → ℝ) ⬝ᵥ ![0, 1, 0] = 1 := by
  simp [dotProduct, Fin.sum_univ_three, show (![0, 1, 0] : Fin 3 → ℝ) 2 = 0 from rfl]

theorem swapWitness_tightDirection_rayleigh :
    (![0, 1, 0] : Fin 3 → ℝ)
        ⬝ᵥ ((subsetSum swapWitnessDesign {3, 4, 5} - 1) *ᵥ ![0, 1, 0]) = 0 := by
  rw [swapWitness_freeTripleGap_form]
  norm_num [show (![0, 1, 0] : Fin 3 → ℝ) 2 = 0 from rfl]

/-- The swap subset, as a literal. -/
theorem swapWitness_swapSet :
    insert (0 : Fin 6) ((({3, 4, 5} : Finset (Fin 6))).erase 5)
      = ({0, 3, 4} : Finset (Fin 6)) := by decide

/-- The swap gap, as an explicit sum of three squares. -/
theorem swapWitness_swapGap_form (vecArg : Fin 3 → ℝ) :
    vecArg ⬝ᵥ ((subsetSum swapWitnessDesign {0, 3, 4} - 1) *ᵥ vecArg)
      = 43 / 2 * (vecArg 0 + 16 / 43 * vecArg 1 + 3 / 43 * vecArg 2) ^ 2
        + 224 / 387 * (vecArg 1 + 3 / 16 * vecArg 2) ^ 2
        + 127 / 8 * vecArg 2 ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [swapWitnessDesign, swapWitnessAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

theorem swapWitness_swapGap_posDef :
    (subsetSum swapWitnessDesign ({0, 3, 4} : Finset (Fin 6)) - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 3, 4} : Finset (Fin 6)) fun label _ =>
      posSemidef_atomMatrix (swapWitnessDesign.atom label)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, swapWitness_swapGap_form]
    by_cases hthird : vecArg 2 = 0
    · by_cases hsecond : vecArg 1 = 0
      · have hfirst : vecArg 0 ≠ 0 := by
          intro hzero
          apply hne
          funext coord
          fin_cases coord <;> simpa using ‹_›
        have hfirstSq : 0 < vecArg 0 ^ 2 :=
          lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hfirst))
        rw [hthird, hsecond]
        nlinarith [hfirstSq]
      · have hsecondSq : 0 < vecArg 1 ^ 2 :=
          lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hsecond))
        rw [hthird]
        nlinarith [hsecondSq, sq_nonneg (vecArg 0 + 16 / 43 * vecArg 1)]
    · have hthirdSq : 0 < vecArg 2 ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hthird))
      nlinarith [hthirdSq, sq_nonneg (vecArg 0 + 16 / 43 * vecArg 1 + 3 / 43 * vecArg 2),
        sq_nonneg (vecArg 1 + 3 / 16 * vecArg 2)]

/-- **The tight-swap conclusion holds at this witness.**  Exactly the shape
`PatternTightSwapExcessProperty` demands: an outgoing dominator member and an
incoming outsider whose one-slot swap strictly dominates. -/
theorem swapWitness_tightSwapConclusion :
    ∃ swapOut ∈ ({3, 4, 5} : Finset (Fin 6)), ∃ swapIn : Fin 6,
      swapIn ∉ ({3, 4, 5} : Finset (Fin 6)) ∧
      (subsetSum swapWitnessDesign
        (insert swapIn ((({3, 4, 5} : Finset (Fin 6))).erase swapOut)) - 1).PosDef := by
  refine ⟨5, by decide, 0, by decide, ?_⟩
  rw [swapWitness_swapSet]
  exact swapWitness_swapGap_posDef

end Gtz
