/-
# Tight double-swap obstructions

This scratch module extends `TightSwapObstructions` from one-slot swaps to
card-three subsets at Hamming distance two from a tight weak dominator.  Exact
censuses of the U(3,6) antecedent show that this is the first unformalized
candidate family: whenever every one-slot swap failed in the sampled hard
residual, some double swap strictly dominated.
-/
import Gtz.Design.TightSwapObstructions
import Gtz.Design.PairDifferenceCover

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz

open Matrix

/-- Replace `swapOutFirst` by `swapInFirst`, then `swapOutSecond` by
`swapInSecond`.  Under the hypotheses used below this is a card-preserving
distance-two exchange. -/
def tightDoubleSwap {size : ℕ} (dominator : Finset (Fin size))
    (swapOutFirst swapOutSecond swapInFirst swapInSecond : Fin size) : Finset (Fin size) :=
  insert swapInSecond
    ((insert swapInFirst (dominator.erase swapOutFirst)).erase swapOutSecond)

/-- The normal surplus of the rank-two update, already cancelled against the
tight dominator. -/
def tightDoubleSwapAlpha {size : ℕ} (design : WeightedDesign size 3)
    (swapOutFirst swapOutSecond swapInFirst swapInSecond : Fin size)
    (tightDir : Fin 3 → ℝ) : ℝ :=
  (design.atom swapInFirst ⬝ᵥ tightDir) ^ 2
    + (design.atom swapInSecond ⬝ᵥ tightDir) ^ 2
    - (design.atom swapOutFirst ⬝ᵥ tightDir) ^ 2
    - (design.atom swapOutSecond ⬝ᵥ tightDir) ^ 2

/-- The cross-coupling of the rank-two exchange at a planar probe. -/
def tightDoubleSwapCross {size : ℕ} (design : WeightedDesign size 3)
    (swapOutFirst swapOutSecond swapInFirst swapInSecond : Fin size)
    (tightDir probe : Fin 3 → ℝ) : ℝ :=
  (design.atom swapInFirst ⬝ᵥ probe) * (design.atom swapInFirst ⬝ᵥ tightDir)
    + (design.atom swapInSecond ⬝ᵥ probe) * (design.atom swapInSecond ⬝ᵥ tightDir)
    - (design.atom swapOutFirst ⬝ᵥ probe) * (design.atom swapOutFirst ⬝ᵥ tightDir)
    - (design.atom swapOutSecond ⬝ᵥ probe) * (design.atom swapOutSecond ⬝ᵥ tightDir)

/-- The planar bilinear excess of the original dominator plus the rank-two
exchange update. -/
def tightDoubleSwapPlaneExcess {size : ℕ} (design : WeightedDesign size 3)
    (dominator : Finset (Fin size))
    (swapOutFirst swapOutSecond swapInFirst swapInSecond : Fin size)
    (probeLeft probeRight : Fin 3 → ℝ) : ℝ :=
  probeLeft ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ probeRight)
    + (design.atom swapInFirst ⬝ᵥ probeLeft)
        * (design.atom swapInFirst ⬝ᵥ probeRight)
    + (design.atom swapInSecond ⬝ᵥ probeLeft)
        * (design.atom swapInSecond ⬝ᵥ probeRight)
    - (design.atom swapOutFirst ⬝ᵥ probeLeft)
        * (design.atom swapOutFirst ⬝ᵥ probeRight)
    - (design.atom swapOutSecond ⬝ᵥ probeLeft)
        * (design.atom swapOutSecond ⬝ᵥ probeRight)

/-- The two-dimensional Schur-cover form after all tight-dominator terms have
been cancelled. -/
def tightDoubleSwapCover {size : ℕ} (design : WeightedDesign size 3)
    (dominator : Finset (Fin size))
    (swapOutFirst swapOutSecond swapInFirst swapInSecond : Fin size)
    (tightDir probeLeft probeRight : Fin 3 → ℝ) : ℝ :=
  tightDoubleSwapAlpha design swapOutFirst swapOutSecond swapInFirst swapInSecond tightDir
      * tightDoubleSwapPlaneExcess design dominator swapOutFirst swapOutSecond
          swapInFirst swapInSecond probeLeft probeRight
    - tightDoubleSwapCross design swapOutFirst swapOutSecond swapInFirst swapInSecond
        tightDir probeLeft
      * tightDoubleSwapCross design swapOutFirst swapOutSecond swapInFirst swapInSecond
          tightDir probeRight

/-- Reading a sum over a two-slot exchange. -/
theorem sum_over_tightDoubleSwap {size : ℕ} (dominator : Finset (Fin size))
    (swapOutFirst swapOutSecond swapInFirst swapInSecond : Fin size)
    (hmemOutFirst : swapOutFirst ∈ dominator)
    (hmemOutSecond : swapOutSecond ∈ dominator)
    (houtDistinct : swapOutFirst ≠ swapOutSecond)
    (hnotMemInFirst : swapInFirst ∉ dominator)
    (hnotMemInSecond : swapInSecond ∉ dominator)
    (hinDistinct : swapInFirst ≠ swapInSecond)
    (readings : Fin size → ℝ) :
    ∑ label ∈ tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond,
        readings label
      = (∑ label ∈ dominator, readings label)
        + readings swapInFirst + readings swapInSecond
        - readings swapOutFirst - readings swapOutSecond := by
  have hmemOutSecondAfter :
      swapOutSecond ∈ insert swapInFirst (dominator.erase swapOutFirst) := by
    simp only [Finset.mem_insert, Finset.mem_erase]
    exact Or.inr ⟨Ne.symm houtDistinct, hmemOutSecond⟩
  have hnotMemInSecondAfter :
      swapInSecond ∉ insert swapInFirst (dominator.erase swapOutFirst) := by
    simp only [Finset.mem_insert, Finset.mem_erase, not_or]
    exact ⟨Ne.symm hinDistinct, fun hmem => hnotMemInSecond hmem.2⟩
  rw [tightDoubleSwap,
    sum_over_tightSwap
      (insert swapInFirst (dominator.erase swapOutFirst)) swapOutSecond swapInSecond
      hmemOutSecondAfter hnotMemInSecondAfter readings,
    sum_over_tightSwap dominator swapOutFirst swapInFirst hmemOutFirst hnotMemInFirst readings]
  ring

/-- A two-slot exchange keeps the cardinality. -/
theorem card_tightDoubleSwap {size : ℕ} (dominator : Finset (Fin size))
    (swapOutFirst swapOutSecond swapInFirst swapInSecond : Fin size)
    (hmemOutFirst : swapOutFirst ∈ dominator)
    (hmemOutSecond : swapOutSecond ∈ dominator)
    (houtDistinct : swapOutFirst ≠ swapOutSecond)
    (hnotMemInFirst : swapInFirst ∉ dominator)
    (hnotMemInSecond : swapInSecond ∉ dominator)
    (hinDistinct : swapInFirst ≠ swapInSecond) :
    (tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond).card
      = dominator.card := by
  have hmemOutSecondAfter :
      swapOutSecond ∈ insert swapInFirst (dominator.erase swapOutFirst) := by
    simp only [Finset.mem_insert, Finset.mem_erase]
    exact Or.inr ⟨Ne.symm houtDistinct, hmemOutSecond⟩
  have hnotMemInSecondAfter :
      swapInSecond ∉ insert swapInFirst (dominator.erase swapOutFirst) := by
    simp only [Finset.mem_insert, Finset.mem_erase, not_or]
    exact ⟨Ne.symm hinDistinct, fun hmem => hnotMemInSecond hmem.2⟩
  rw [tightDoubleSwap,
    card_tightSwap
      (insert swapInFirst (dominator.erase swapOutFirst)) swapOutSecond swapInSecond
      hmemOutSecondAfter hnotMemInSecondAfter,
    card_tightSwap dominator swapOutFirst swapInFirst hmemOutFirst hnotMemInFirst]

/-- At a unit tight direction, the normal surplus of a double swap is the
incoming square sum minus the outgoing square sum. -/
theorem tightDoubleSwap_normalSurplus {size : ℕ}
    (design : WeightedDesign size 3) (dominator : Finset (Fin size))
    (swapOutFirst swapOutSecond swapInFirst swapInSecond : Fin size)
    (tightDir : Fin 3 → ℝ)
    (hmemOutFirst : swapOutFirst ∈ dominator)
    (hmemOutSecond : swapOutSecond ∈ dominator)
    (houtDistinct : swapOutFirst ≠ swapOutSecond)
    (hnotMemInFirst : swapInFirst ∉ dominator)
    (hnotMemInSecond : swapInSecond ∉ dominator)
    (hinDistinct : swapInFirst ≠ swapInSecond)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0) :
    (∑ label ∈ tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond,
        (design.atom label ⬝ᵥ tightDir) ^ 2) - 1
      = (design.atom swapInFirst ⬝ᵥ tightDir) ^ 2
        + (design.atom swapInSecond ⬝ᵥ tightDir) ^ 2
        - (design.atom swapOutFirst ⬝ᵥ tightDir) ^ 2
        - (design.atom swapOutSecond ⬝ᵥ tightDir) ^ 2 := by
  rw [sum_over_tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond
      hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
      (fun label => (design.atom label ⬝ᵥ tightDir) ^ 2),
    tightDirection_squareReadings_eq_one design dominator tightDir hunit htight]
  ring

/-- The exact Schur plane-cover condition for a double swap, expressed against
the original tight dominator's gap. -/
theorem tightDoubleSwap_planeCover_iff_dominatorGapExcess {size : ℕ}
    (design : WeightedDesign size 3) (dominator : Finset (Fin size))
    (swapOutFirst swapOutSecond swapInFirst swapInSecond : Fin size)
    (tightDir probe : Fin 3 → ℝ)
    (hmemOutFirst : swapOutFirst ∈ dominator)
    (hmemOutSecond : swapOutSecond ∈ dominator)
    (houtDistinct : swapOutFirst ≠ swapOutSecond)
    (hnotMemInFirst : swapInFirst ∉ dominator)
    (hnotMemInSecond : swapInSecond ∉ dominator)
    (hinDistinct : swapInFirst ≠ swapInSecond)
    (hdominates : Dominates design dominator)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0)
    (hprobeFlat : probe ⬝ᵥ tightDir = 0) :
    ((∑ label ∈ tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond,
          (design.atom label ⬝ᵥ probe) * (design.atom label ⬝ᵥ tightDir)) ^ 2
        < ((∑ label ∈ tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond,
              (design.atom label ⬝ᵥ tightDir) ^ 2) - 1)
          * ((∑ label ∈ tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond,
                (design.atom label ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe))
      ↔
      ((design.atom swapInFirst ⬝ᵥ probe) * (design.atom swapInFirst ⬝ᵥ tightDir)
          + (design.atom swapInSecond ⬝ᵥ probe) * (design.atom swapInSecond ⬝ᵥ tightDir)
          - (design.atom swapOutFirst ⬝ᵥ probe) * (design.atom swapOutFirst ⬝ᵥ tightDir)
          - (design.atom swapOutSecond ⬝ᵥ probe) * (design.atom swapOutSecond ⬝ᵥ tightDir)) ^ 2
        < ((design.atom swapInFirst ⬝ᵥ tightDir) ^ 2
              + (design.atom swapInSecond ⬝ᵥ tightDir) ^ 2
              - (design.atom swapOutFirst ⬝ᵥ tightDir) ^ 2
              - (design.atom swapOutSecond ⬝ᵥ tightDir) ^ 2)
          * (probe ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ probe)
              + (design.atom swapInFirst ⬝ᵥ probe) ^ 2
              + (design.atom swapInSecond ⬝ᵥ probe) ^ 2
              - (design.atom swapOutFirst ⬝ᵥ probe) ^ 2
              - (design.atom swapOutSecond ⬝ᵥ probe) ^ 2) := by
  rw [sum_over_tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond
      hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
      (fun label => (design.atom label ⬝ᵥ probe) * (design.atom label ⬝ᵥ tightDir)),
    sum_over_tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond
      hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
      (fun label => (design.atom label ⬝ᵥ tightDir) ^ 2),
    sum_over_tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond
      hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
      (fun label => (design.atom label ⬝ᵥ probe) ^ 2),
    tightDirection_crossReadings_vanish design dominator tightDir probe hdominates htight
      hprobeFlat,
    tightDirection_squareReadings_eq_one design dominator tightDir hunit htight,
    dominationGap_form]
  constructor <;> intro h <;> nlinarith [h]

/-- The repository's generic `coverForm` of a double swap is exactly the
cancelled rank-two update form.  This polarized statement is what permits the
two-by-two frame-minor criterion below. -/
theorem coverForm_tightDoubleSwap {size : ℕ}
    (design : WeightedDesign size 3) (dominator : Finset (Fin size))
    (swapOutFirst swapOutSecond swapInFirst swapInSecond : Fin size)
    (tightDir probeLeft probeRight : Fin 3 → ℝ)
    (hmemOutFirst : swapOutFirst ∈ dominator)
    (hmemOutSecond : swapOutSecond ∈ dominator)
    (houtDistinct : swapOutFirst ≠ swapOutSecond)
    (hnotMemInFirst : swapInFirst ∉ dominator)
    (hnotMemInSecond : swapInSecond ∉ dominator)
    (hinDistinct : swapInFirst ≠ swapInSecond)
    (hdominates : Dominates design dominator)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0)
    (hleftFlat : probeLeft ⬝ᵥ tightDir = 0)
    (hrightFlat : probeRight ⬝ᵥ tightDir = 0) :
    coverForm design
        (tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond)
        tightDir probeLeft probeRight
      = tightDoubleSwapCover design dominator swapOutFirst swapOutSecond
          swapInFirst swapInSecond tightDir probeLeft probeRight := by
  have hbasePairing :
      probeLeft ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ probeRight)
        = (∑ label ∈ dominator,
            (design.atom label ⬝ᵥ probeLeft) * (design.atom label ⬝ᵥ probeRight))
          - probeLeft ⬝ᵥ probeRight := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      subsetSum_bilinearForm_eq_sum_mul]
  rw [coverForm,
    sum_over_tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond
      hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
      (fun label => (design.atom label ⬝ᵥ tightDir) ^ 2),
    sum_over_tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond
      hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
      (fun label => (design.atom label ⬝ᵥ probeLeft)
        * (design.atom label ⬝ᵥ probeRight)),
    sum_over_tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond
      hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
      (fun label => (design.atom label ⬝ᵥ probeLeft)
        * (design.atom label ⬝ᵥ tightDir)),
    sum_over_tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond
      hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
      (fun label => (design.atom label ⬝ᵥ probeRight)
        * (design.atom label ⬝ᵥ tightDir)),
    tightDirection_squareReadings_eq_one design dominator tightDir hunit htight,
    tightDirection_crossReadings_vanish design dominator tightDir probeLeft hdominates htight
      hleftFlat,
    tightDirection_crossReadings_vanish design dominator tightDir probeRight hdominates htight
      hrightFlat]
  simp only [tightDoubleSwapCover, tightDoubleSwapAlpha, tightDoubleSwapCross,
    tightDoubleSwapPlaneExcess]
  rw [hbasePairing]
  ring

/-- A double swap strictly dominates exactly when its combined incoming normal
mass beats the combined outgoing normal mass and the resulting rank-two update
passes the planar Schur test. -/
theorem tightDoubleSwap_posDef_iff_surplus_and_gapExcess {size : ℕ}
    (design : WeightedDesign size 3) (dominator : Finset (Fin size))
    (swapOutFirst swapOutSecond swapInFirst swapInSecond : Fin size)
    (tightDir : Fin 3 → ℝ)
    (hmemOutFirst : swapOutFirst ∈ dominator)
    (hmemOutSecond : swapOutSecond ∈ dominator)
    (houtDistinct : swapOutFirst ≠ swapOutSecond)
    (hnotMemInFirst : swapInFirst ∉ dominator)
    (hnotMemInSecond : swapInSecond ∉ dominator)
    (hinDistinct : swapInFirst ≠ swapInSecond)
    (hdominates : Dominates design dominator)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0) :
    (subsetSum design
        (tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond) - 1).PosDef
      ↔
      (0 < (design.atom swapInFirst ⬝ᵥ tightDir) ^ 2
            + (design.atom swapInSecond ⬝ᵥ tightDir) ^ 2
            - (design.atom swapOutFirst ⬝ᵥ tightDir) ^ 2
            - (design.atom swapOutSecond ⬝ᵥ tightDir) ^ 2
        ∧ ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ tightDir = 0 → probe ≠ 0 →
          ((design.atom swapInFirst ⬝ᵥ probe) * (design.atom swapInFirst ⬝ᵥ tightDir)
              + (design.atom swapInSecond ⬝ᵥ probe) * (design.atom swapInSecond ⬝ᵥ tightDir)
              - (design.atom swapOutFirst ⬝ᵥ probe) * (design.atom swapOutFirst ⬝ᵥ tightDir)
              - (design.atom swapOutSecond ⬝ᵥ probe) * (design.atom swapOutSecond ⬝ᵥ tightDir)) ^ 2
            < ((design.atom swapInFirst ⬝ᵥ tightDir) ^ 2
                  + (design.atom swapInSecond ⬝ᵥ tightDir) ^ 2
                  - (design.atom swapOutFirst ⬝ᵥ tightDir) ^ 2
                  - (design.atom swapOutSecond ⬝ᵥ tightDir) ^ 2)
              * (probe ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ probe)
                  + (design.atom swapInFirst ⬝ᵥ probe) ^ 2
                  + (design.atom swapInSecond ⬝ᵥ probe) ^ 2
                  - (design.atom swapOutFirst ⬝ᵥ probe) ^ 2
                  - (design.atom swapOutSecond ⬝ᵥ probe) ^ 2)) := by
  constructor
  · intro hposDef
    obtain ⟨hsurplus, hcover⟩ := normalSurplus_planeCover_of_posDef design
      (tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond)
      tightDir hunit hposDef
    have hnormal := tightDoubleSwap_normalSurplus design dominator
      swapOutFirst swapOutSecond swapInFirst swapInSecond tightDir
      hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
      hunit htight
    refine ⟨by linarith, fun probe hprobeFlat hprobeNe => ?_⟩
    exact (tightDoubleSwap_planeCover_iff_dominatorGapExcess design dominator
      swapOutFirst swapOutSecond swapInFirst swapInSecond tightDir probe
      hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
      hdominates hunit htight hprobeFlat).mp (hcover probe hprobeFlat hprobeNe)
  · rintro ⟨hsurplus, hgapExcess⟩
    refine posDef_of_normalSurplus_planeCover design
      (tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond)
      tightDir hunit ?_ ?_
    · have hnormal := tightDoubleSwap_normalSurplus design dominator
        swapOutFirst swapOutSecond swapInFirst swapInSecond tightDir
        hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
        hunit htight
      linarith
    · intro probe hprobeFlat hprobeNe
      exact (tightDoubleSwap_planeCover_iff_dominatorGapExcess design dominator
        swapOutFirst swapOutSecond swapInFirst swapInSecond tightDir probe
        hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
        hdominates hunit htight hprobeFlat).mpr
        (hgapExcess probe hprobeFlat hprobeNe)

/-- **The quantifier-free double-swap criterion.**  In any orthonormal frame of
the tight plane, strict domination by the distance-two candidate is equivalent
to three explicit polynomial signs: its normal surplus, one diagonal entry of
the cancelled cover form, and that cover form's two-by-two determinant. -/
theorem tightDoubleSwap_posDef_iff_frameMinors {size : ℕ}
    (design : WeightedDesign size 3) (dominator : Finset (Fin size))
    (swapOutFirst swapOutSecond swapInFirst swapInSecond : Fin size)
    (planeFirst planeSecond tightDir : Fin 3 → ℝ)
    (hmemOutFirst : swapOutFirst ∈ dominator)
    (hmemOutSecond : swapOutSecond ∈ dominator)
    (houtDistinct : swapOutFirst ≠ swapOutSecond)
    (hnotMemInFirst : swapInFirst ∉ dominator)
    (hnotMemInSecond : swapInSecond ∉ dominator)
    (hinDistinct : swapInFirst ≠ swapInSecond)
    (hdominates : Dominates design dominator)
    (hfirstUnit : planeFirst ⬝ᵥ planeFirst = 1)
    (hsecondUnit : planeSecond ⬝ᵥ planeSecond = 1)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (hfirstSecond : planeFirst ⬝ᵥ planeSecond = 0)
    (hfirstFlat : planeFirst ⬝ᵥ tightDir = 0)
    (hsecondFlat : planeSecond ⬝ᵥ tightDir = 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0) :
    (subsetSum design
        (tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond) - 1).PosDef
      ↔ 0 < tightDoubleSwapAlpha design swapOutFirst swapOutSecond
            swapInFirst swapInSecond tightDir
        ∧ 0 < tightDoubleSwapCover design dominator swapOutFirst swapOutSecond
            swapInFirst swapInSecond tightDir planeFirst planeFirst
        ∧ 0 < tightDoubleSwapCover design dominator swapOutFirst swapOutSecond
                swapInFirst swapInSecond tightDir planeFirst planeFirst
              * tightDoubleSwapCover design dominator swapOutFirst swapOutSecond
                swapInFirst swapInSecond tightDir planeSecond planeSecond
            - tightDoubleSwapCover design dominator swapOutFirst swapOutSecond
                swapInFirst swapInSecond tightDir planeFirst planeSecond ^ 2 := by
  have hnormal := tightDoubleSwap_normalSurplus design dominator
    swapOutFirst swapOutSecond swapInFirst swapInSecond tightDir
    hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
    hunit htight
  have hnormalAlpha :
      (∑ label ∈ tightDoubleSwap dominator swapOutFirst swapOutSecond
          swapInFirst swapInSecond, (design.atom label ⬝ᵥ tightDir) ^ 2) - 1
        = tightDoubleSwapAlpha design swapOutFirst swapOutSecond
            swapInFirst swapInSecond tightDir := by
    simpa only [tightDoubleSwapAlpha] using hnormal
  have hcoverFirstFirst := coverForm_tightDoubleSwap design dominator
    swapOutFirst swapOutSecond swapInFirst swapInSecond tightDir planeFirst planeFirst
    hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
    hdominates hunit htight hfirstFlat hfirstFlat
  have hcoverSecondSecond := coverForm_tightDoubleSwap design dominator
    swapOutFirst swapOutSecond swapInFirst swapInSecond tightDir planeSecond planeSecond
    hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
    hdominates hunit htight hsecondFlat hsecondFlat
  have hcoverFirstSecond := coverForm_tightDoubleSwap design dominator
    swapOutFirst swapOutSecond swapInFirst swapInSecond tightDir planeFirst planeSecond
    hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
    hdominates hunit htight hfirstFlat hsecondFlat
  constructor
  · intro hposDef
    obtain ⟨hsurplus, hdiag, hdet⟩ :=
      (posDef_iff_surplus_and_frameMinors design
        (tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond)
        planeFirst planeSecond tightDir hfirstUnit hsecondUnit hunit hfirstSecond
        hfirstFlat hsecondFlat).mp hposDef
    rw [hcoverFirstFirst] at hdiag
    rw [hcoverFirstFirst, hcoverSecondSecond, hcoverFirstSecond] at hdet
    refine ⟨?_, hdiag, hdet⟩
    linarith [hnormalAlpha]
  · rintro ⟨halpha, hdiag, hdet⟩
    refine (posDef_iff_surplus_and_frameMinors design
      (tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond)
      planeFirst planeSecond tightDir hfirstUnit hsecondUnit hunit hfirstSecond
      hfirstFlat hsecondFlat).mpr ⟨?_, ?_, ?_⟩
    · linarith [hnormalAlpha]
    · rwa [hcoverFirstFirst]
    · rwa [hcoverFirstFirst, hcoverSecondSecond, hcoverFirstSecond]

/-- A tie must refuse every normal-surplus double swap.  The refusing witness
is entirely two-dimensional and compares the original dominator gap plus the
rank-two exchange update against the exchange cross-coupling square. -/
theorem noStrictDominator_yields_tightDoubleSwapExcess_failure {size : ℕ}
    (design : WeightedDesign size 3) (dominator : Finset (Fin size))
    (swapOutFirst swapOutSecond swapInFirst swapInSecond : Fin size)
    (tightDir : Fin 3 → ℝ)
    (hcard : dominator.card = 3)
    (hmemOutFirst : swapOutFirst ∈ dominator)
    (hmemOutSecond : swapOutSecond ∈ dominator)
    (houtDistinct : swapOutFirst ≠ swapOutSecond)
    (hnotMemInFirst : swapInFirst ∉ dominator)
    (hnotMemInSecond : swapInSecond ∉ dominator)
    (hinDistinct : swapInFirst ≠ swapInSecond)
    (hdominates : Dominates design dominator)
    (hunit : tightDir ⬝ᵥ tightDir = 1)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0)
    (hsurplus :
      0 < (design.atom swapInFirst ⬝ᵥ tightDir) ^ 2
          + (design.atom swapInSecond ⬝ᵥ tightDir) ^ 2
          - (design.atom swapOutFirst ⬝ᵥ tightDir) ^ 2
          - (design.atom swapOutSecond ⬝ᵥ tightDir) ^ 2)
    (hnoStrict : ∀ selected : Finset (Fin size), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    ∃ probe : Fin 3 → ℝ, probe ⬝ᵥ tightDir = 0 ∧ probe ≠ 0 ∧
      ((design.atom swapInFirst ⬝ᵥ tightDir) ^ 2
            + (design.atom swapInSecond ⬝ᵥ tightDir) ^ 2
            - (design.atom swapOutFirst ⬝ᵥ tightDir) ^ 2
            - (design.atom swapOutSecond ⬝ᵥ tightDir) ^ 2)
          * (probe ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ probe)
              + (design.atom swapInFirst ⬝ᵥ probe) ^ 2
              + (design.atom swapInSecond ⬝ᵥ probe) ^ 2
              - (design.atom swapOutFirst ⬝ᵥ probe) ^ 2
              - (design.atom swapOutSecond ⬝ᵥ probe) ^ 2)
        ≤ ((design.atom swapInFirst ⬝ᵥ probe) * (design.atom swapInFirst ⬝ᵥ tightDir)
              + (design.atom swapInSecond ⬝ᵥ probe) * (design.atom swapInSecond ⬝ᵥ tightDir)
              - (design.atom swapOutFirst ⬝ᵥ probe) * (design.atom swapOutFirst ⬝ᵥ tightDir)
              - (design.atom swapOutSecond ⬝ᵥ probe) * (design.atom swapOutSecond ⬝ᵥ tightDir)) ^ 2 := by
  by_contra hnone
  push Not at hnone
  refine hnoStrict
    (tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond) ?_ ?_
  · rw [card_tightDoubleSwap dominator swapOutFirst swapOutSecond swapInFirst swapInSecond
      hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct,
      hcard]
  · exact (tightDoubleSwap_posDef_iff_surplus_and_gapExcess design dominator
      swapOutFirst swapOutSecond swapInFirst swapInSecond tightDir
      hmemOutFirst hmemOutSecond houtDistinct hnotMemInFirst hnotMemInSecond hinDistinct
      hdominates hunit htight).mpr
      ⟨hsurplus, fun probe hprobeFlat hprobeNe => hnone probe hprobeFlat hprobeNe⟩

end Gtz
