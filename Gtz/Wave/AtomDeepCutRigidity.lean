import Gtz.Wave.AtomCutRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The single-cut rigidity and the split of the deep stratum

The deep stratum of the sharp split runs from the single onset
`(12 - 3 * sqrt 6) / 5`, about `0.9303062`, up to one.  The rigidity law
of the trine cut is weak there, because the trine-cut deficit is large.
This module supplies the law that is sharp there: the rigidity of the
SINGLE cut, whose deficit vanishes exactly at the single onset.

The construction is the one of the blocked cut with the deflation
coefficient one in place of two.  The single tangent gap of a slot splits
into a deviation term, `(mass - 6 * scale) ^ 2` against the splitting
weight, and a slack term, the single slot excess against `3 - mass - 6 *
scale`.  The six gaps add to `-2 (3 - 2 * mass) * singleCut mass`, and at
a datum that fails the single budget everywhere each gap is nonnegative,
thus each one is capped by that total.

Two structural facts come with it.  The single slot excess and the
blocked slot excess differ by `scale * (diagonal - 1)`, which a frame
makes nonpositive, thus a datum that fails the single budget at every
live slot is automatically blocked at every live slot.  And at the single
onset the uniform equality pins the diagonal to ONE HALF, which is
exactly the normalization of the scaled two-trine.  The trine is not a
coincidence of the stratum, it is its unique tangent point.

The deep stratum then splits again, losslessly, by whether a live pivot
of single budget exists.  The DOUBLY BLOCKED part needs no scale mass
hypothesis at all, because failing the single budget everywhere forces
the mass above the single onset by itself.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.singleTangentGap`, `Gtz.singleTangentGap_split`,
  `Gtz.singleTangentGap_nonneg`, `Gtz.singleTangentGap_total_six`,
  `Gtz.singleTangentGap_total`, `Gtz.singleTangentGap_le_total` — **THE
  SINGLE-CUT RIGIDITY IDENTITY** and its cap.
* `Gtz.singleFail_scale_deviation_le`, `Gtz.singleFail_slack_le` — **THE
  DEEP RIGIDITY BOUNDS**: near the single onset every light slot carries
  the uniform scale and every single budget fails by nothing.
* `Gtz.blockedSlotExcess_sub_singleSlotExcess`,
  `Gtz.blockedSlotExcess_nonpos_of_single`, `Gtz.blocked_of_singleFail`
  — **THE EXCESS ORDERING**: the single failure carries blockedness.
* `Gtz.uniform_diagonal_half_iff_singleCut_zero` — **THE TRINE
  NORMALIZATION IS THE SINGLE ONSET**: at uniform scales the equality of
  the single budget pins the diagonal to one half exactly when the single
  cut vanishes.
* `Gtz.AtomSingleBudgetDeepClosed`, `Gtz.AtomDoublyBlockedClosed`,
  `Gtz.atomBlockedDeepCutClosed_iff_singleBudgetDeep_and_doublyBlocked`
  — **THE LOSSLESS SPLIT OF THE DEEP STRATUM.**
* `Gtz.AtomSingleBudgetDeepKill`, `Gtz.AtomDoublyBlockedKill` and their
  equivalences — the global kills of the two deep parts.
* `Gtz.atomBlockedPairClosed_of_three_parts`,
  `Gtz.gtzWeighted_six_three_of_three_parts`,
  `Gtz.gtzWeightedAll_three_of_three_parts`,
  `Gtz.isEmpty_sixThreeCrux_of_three_parts` — the cell and the
  rank-three payoff from the three sharp parts.

## Vacuity

Every law of layers zero thru two is an unconditional statement about a
family of vectors, a family of scales and one slot.  Layer three only
rearranges the landed residues, and the equivalence theorem proves that
the rearrangement is lossless.
-/

namespace Gtz

/-! ## Layer 0 — the single-cut rigidity -/

/-- The SINGLE TANGENT GAP of a slot: the slack of the tangent step of the
sharp single-budget threshold.  It splits into a deviation term, which
measures the distance of the scale from the uniform value, and a slack
term, which measures how far the single budget is from an equality. -/
def singleTangentGap {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount) : ℝ :=
  (2 * scale pivot + 3 - (∑ slot, scale slot) - 4 * atomGram atom pivot pivot)
      * ((∑ slot, scale slot) - 6 * scale pivot) ^ 2
    - 12 * singleSlotExcess atom scale pivot
      * (3 - (∑ slot, scale slot) - 6 * scale pivot)

/-- **THE SINGLE TANGENT GAP IS THE SLACK OF THE TANGENT STEP.**  The
identity is polynomial and unconditional. -/
theorem singleTangentGap_split {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot : Fin slotCount) :
    singleTangentGap atom scale pivot
      = (3 - 2 * (∑ slot, scale slot)) ^ 2
          * (2 * scale pivot + 3 - (∑ slot, scale slot)
            - 4 * atomGram atom pivot pivot)
        - 3 * ((1 - (∑ slot, scale slot)) * (3 - (∑ slot, scale slot)))
          * (2 * (3 - 2 * (∑ slot, scale slot))
            - 3 * (1 - (∑ slot, scale slot) + 2 * scale pivot)) := by
  simp only [singleTangentGap, singleSlotExcess]
  ring

/-- **THE SINGLE TANGENT GAP IS NONNEGATIVE WHEN THE SINGLE BUDGET FAILS
EVERYWHERE.** -/
theorem singleTangentGap_nonneg {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hscale : ∀ slot, 0 ≤ scale slot) (hsmall : (∑ slot, scale slot) < 1)
    (hfail : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot))
    (pivot : Fin 6) : 0 ≤ singleTangentGap atom scale pivot := by
  have hexcess := singleSlotExcess_nonpos_of_singleFail hscale hsmall hfail pivot
  have hbound : atomGram atom pivot pivot
        * (1 - (∑ slot, scale slot) + 2 * scale pivot)
      ≤ scale pivot * (2 - (∑ slot, scale slot) + scale pivot) := by
    simp only [singleSlotExcess] at hexcess
    linarith [hexcess]
  have htangent := single_slot_tangent hsmall (hscale pivot) hbound
  rw [singleTangentGap_split]
  linarith [htangent]

/-- **THE SIX SINGLE TANGENT GAPS ADD TO THE SINGLE CUT DEFICIT.** -/
theorem singleTangentGap_total_six
    {mass scaleZero scaleOne scaleTwo scaleThree scaleFour scaleFive
      diagZero diagOne diagTwo diagThree diagFour diagFive : ℝ}
    (hmassSum : scaleZero + scaleOne + scaleTwo + scaleThree + scaleFour + scaleFive
      = mass)
    (htraceSum : diagZero + diagOne + diagTwo + diagThree + diagFour + diagFive = 3) :
    ((3 - 2 * mass) ^ 2 * (2 * scaleZero + 3 - mass - 4 * diagZero)
        - 3 * ((1 - mass) * (3 - mass))
          * (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * scaleZero)))
      + ((3 - 2 * mass) ^ 2 * (2 * scaleOne + 3 - mass - 4 * diagOne)
        - 3 * ((1 - mass) * (3 - mass))
          * (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * scaleOne)))
      + ((3 - 2 * mass) ^ 2 * (2 * scaleTwo + 3 - mass - 4 * diagTwo)
        - 3 * ((1 - mass) * (3 - mass))
          * (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * scaleTwo)))
      + ((3 - 2 * mass) ^ 2 * (2 * scaleThree + 3 - mass - 4 * diagThree)
        - 3 * ((1 - mass) * (3 - mass))
          * (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * scaleThree)))
      + ((3 - 2 * mass) ^ 2 * (2 * scaleFour + 3 - mass - 4 * diagFour)
        - 3 * ((1 - mass) * (3 - mass))
          * (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * scaleFour)))
      + ((3 - 2 * mass) ^ 2 * (2 * scaleFive + 3 - mass - 4 * diagFive)
        - 3 * ((1 - mass) * (3 - mass))
          * (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * scaleFive)))
      = -(2 * (3 - 2 * mass) * singleCut mass) := by
  simp only [singleCut]
  have hscaleFive : scaleFive
      = mass - (scaleZero + scaleOne + scaleTwo + scaleThree + scaleFour) := by
    linarith [hmassSum]
  have hdiagFive : diagFive
      = 3 - (diagZero + diagOne + diagTwo + diagThree + diagFour) := by
    linarith [htraceSum]
  rw [hscaleFive, hdiagFive]
  ring

/-- **THE SINGLE RIGIDITY IDENTITY.**  The six single tangent gaps of a
tight frame add to `-2 (3 - 2 * mass) * singleCut mass`. -/
theorem singleTangentGap_total {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ pivot, singleTangentGap atom scale pivot)
      = -(2 * (3 - 2 * (∑ slot, scale slot)) * singleCut (∑ slot, scale slot)) := by
  have hmassSum : scale 0 + scale 1 + scale 2 + scale 3 + scale 4 + scale 5
      = ∑ slot, scale slot := by rw [Fin.sum_univ_six]
  have htraceSum : atomGram atom 0 0 + atomGram atom 1 1 + atomGram atom 2 2
      + atomGram atom 3 3 + atomGram atom 4 4 + atomGram atom 5 5 = 3 := by
    have htrace : (∑ slot, atomGram atom slot slot) = 3 := by
      simpa using atomGram_trace hframe
    rw [← htrace, Fin.sum_univ_six]
  have hsix : (∑ pivot, singleTangentGap atom scale pivot)
      = singleTangentGap atom scale 0 + singleTangentGap atom scale 1
        + singleTangentGap atom scale 2 + singleTangentGap atom scale 3
        + singleTangentGap atom scale 4 + singleTangentGap atom scale 5 := by
    rw [Fin.sum_univ_six]
  rw [hsix, singleTangentGap_split, singleTangentGap_split, singleTangentGap_split,
    singleTangentGap_split, singleTangentGap_split, singleTangentGap_split]
  exact singleTangentGap_total_six hmassSum htraceSum

/-- **EVERY SINGLE TANGENT GAP IS CAPPED BY THE SINGLE CUT DEFICIT.**
Near the single onset the cap goes to zero. -/
theorem singleTangentGap_le_total {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) (hsmall : (∑ slot, scale slot) < 1)
    (hfail : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot))
    (pivot : Fin 6) :
    singleTangentGap atom scale pivot
      ≤ -(2 * (3 - 2 * (∑ slot, scale slot)) * singleCut (∑ slot, scale slot)) := by
  have htotal := singleTangentGap_total (scale := scale) hframe
  have hnonneg : ∀ other : Fin 6, 0 ≤ singleTangentGap atom scale other :=
    singleTangentGap_nonneg hscale hsmall hfail
  have hsplit : (∑ other, singleTangentGap atom scale other)
      = singleTangentGap atom scale pivot
        + ∑ other ∈ Finset.univ.erase pivot, singleTangentGap atom scale other :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ pivot)).symm
  have hrest : 0 ≤ ∑ other ∈ Finset.univ.erase pivot,
      singleTangentGap atom scale other :=
    Finset.sum_nonneg fun other _ => hnonneg other
  linarith [htotal, hsplit, hrest]

/-- **THE SCALES OF A DOUBLY BLOCKED DATUM SIT NEAR THE UNIFORM VALUE.**
At a light slot the deviation term alone is capped by the single cut
deficit, which vanishes at the single onset. -/
theorem singleFail_scale_deviation_le {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) (hsmall : (∑ slot, scale slot) < 1)
    (hfail : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot))
    {pivot : Fin 6}
    (hlight : 6 * scale pivot ≤ 3 - (∑ slot, scale slot)) :
    (2 * scale pivot + 3 - (∑ slot, scale slot)
        - 4 * atomGram atom pivot pivot)
        * ((∑ slot, scale slot) - 6 * scale pivot) ^ 2
      ≤ -(2 * (3 - 2 * (∑ slot, scale slot)) * singleCut (∑ slot, scale slot)) := by
  have hcap := singleTangentGap_le_total hframe hscale hsmall hfail pivot
  have hexcess := singleSlotExcess_nonpos_of_singleFail hscale hsmall hfail pivot
  have hsign : 0 ≤ -(12 * singleSlotExcess atom scale pivot
      * (3 - (∑ slot, scale slot) - 6 * scale pivot)) := by
    have hone : (0:ℝ) ≤ 3 - (∑ slot, scale slot) - 6 * scale pivot := by linarith
    nlinarith [hexcess, hone]
  simp only [singleTangentGap] at hcap
  linarith [hcap, hsign]

/-- **THE SINGLE BUDGETS OF A DOUBLY BLOCKED DATUM FAIL BY NOTHING.**
Wherever the diagonal stays below the splitting level, the slack term
alone is capped by the single cut deficit. -/
theorem singleFail_slack_le {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) (hsmall : (∑ slot, scale slot) < 1)
    (hfail : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot))
    {pivot : Fin 6}
    (hdiag : 4 * atomGram atom pivot pivot
      ≤ 2 * scale pivot + 3 - (∑ slot, scale slot)) :
    -(12 * singleSlotExcess atom scale pivot
        * (3 - (∑ slot, scale slot) - 6 * scale pivot))
      ≤ -(2 * (3 - 2 * (∑ slot, scale slot)) * singleCut (∑ slot, scale slot)) := by
  have hcap := singleTangentGap_le_total hframe hscale hsmall hfail pivot
  have hdev : 0 ≤ (2 * scale pivot + 3 - (∑ slot, scale slot)
        - 4 * atomGram atom pivot pivot)
      * ((∑ slot, scale slot) - 6 * scale pivot) ^ 2 :=
    mul_nonneg (by linarith [hdiag]) (sq_nonneg _)
  simp only [singleTangentGap] at hcap
  linarith [hcap, hdev]

/-! ## Layer 1 — the excess ordering and the trine normalization -/

/-- **THE TWO EXCESSES DIFFER BY ONE PRODUCT.**  The identity is
polynomial and unconditional. -/
theorem blockedSlotExcess_sub_singleSlotExcess {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot : Fin slotCount) :
    blockedSlotExcess atom scale pivot - singleSlotExcess atom scale pivot
      = scale pivot * (atomGram atom pivot pivot - 1) := by
  simp only [blockedSlotExcess, singleSlotExcess]
  ring

/-- **THE SINGLE FAILURE CARRIES THE BLOCKED FAILURE.**  A frame diagonal
is at most one, thus the blocked excess never beats the single excess. -/
theorem blockedSlotExcess_nonpos_of_single {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} {pivot : Fin slotCount}
    (hscale : 0 ≤ scale pivot)
    (hsingle : singleSlotExcess atom scale pivot ≤ 0) :
    blockedSlotExcess atom scale pivot ≤ 0 := by
  have hdiag := atomGram_diag_le_one hframe pivot
  have hdiff := blockedSlotExcess_sub_singleSlotExcess atom scale pivot
  nlinarith [hdiff, hsingle, mul_nonneg hscale (by linarith : (0:ℝ) ≤ 1 - atomGram atom pivot pivot)]

/-- **A DOUBLY BLOCKED DATUM IS BLOCKED.**  Failure of the single budget
at a live slot forces failure of the double budget there, because the
diagonal of a frame is at most one. -/
theorem blocked_of_singleFail {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hfail : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot))
    (pivot : Fin 6) (hlive : 0 < atomShiftedDiag atom scale pivot) :
    atomShiftedDiag atom scale pivot
      ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
        + 2 * scale pivot * (1 - atomGram atom pivot pivot) := by
  have hb := hfail pivot hlive
  have hdiag := atomGram_diag_le_one hframe pivot
  nlinarith [hb, mul_nonneg (hscale pivot)
    (by linarith : (0:ℝ) ≤ 1 - atomGram atom pivot pivot)]

/-- **THE TRINE NORMALIZATION IS THE SINGLE ONSET.**  At uniform scales
the single budget holds with equality at the diagonal one half exactly
when the single cut vanishes.  The scaled two-trine has diagonal one half
at every slot, thus it is the unique tangent point of the whole
threshold. -/
theorem uniform_diagonal_half_iff_singleCut_zero (mass : ℝ) :
    ((1:ℝ) / 2) * (1 - mass + 2 * (mass / 6))
        = (mass / 6) * (2 - mass + mass / 6)
      ↔ singleCut mass = 0 := by
  simp only [singleCut]
  constructor
  · intro heq
    linarith [heq]
  · intro heq
    linarith [heq]

/-! ## Layer 2 — the lossless split of the deep stratum -/

/-- **THE DEEP STRATUM WITH A SINGLE-BUDGET PIVOT.**  The blocked residue
above the single onset at a datum that still carries a live pivot of
single budget.  The plane closure fires there, thus the live inflation
engines of the previous modules apply. -/
def AtomSingleBudgetDeepClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) →
    singleCut (∑ slot, scale slot) ≤ 0 →
    (∃ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot
      ∧ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)
        < atomShiftedDiag atom scale pivot) →
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo

/-- **THE DOUBLY BLOCKED STRATUM.**  Every live pivot fails even the
single inflation budget.  This residue needs NO scale mass hypothesis and
NO blockedness hypothesis: the single failure forces the mass above the
single onset by the sharp window law, and it forces blockedness by the
excess ordering. -/
def AtomDoublyBlockedClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)) →
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo

/-- **THE TWO DEEP PARTS CLOSE THE DEEP STRATUM.** -/
theorem atomBlockedDeepCutClosed_of_singleBudgetDeep_of_doublyBlocked
    (hbudget : AtomSingleBudgetDeepClosed) (hdouble : AtomDoublyBlockedClosed) :
    AtomBlockedDeepCutClosed := by
  intro atom scale hpos hsmall hframe hblocked hcut
  by_cases hex : ∃ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot
      ∧ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)
        < atomShiftedDiag atom scale pivot
  · exact hbudget atom scale hpos hsmall hframe hblocked hcut hex
  · push Not at hex
    exact hdouble atom scale hpos hsmall hframe hex

/-- The deep stratum carries the single-budget part. -/
theorem atomSingleBudgetDeepClosed_of_deepCut
    (hdeep : AtomBlockedDeepCutClosed) : AtomSingleBudgetDeepClosed :=
  fun atom scale hpos hsmall hframe hblocked hcut _ =>
    hdeep atom scale hpos hsmall hframe hblocked hcut

/-- The deep stratum carries the doubly blocked part. -/
theorem atomDoublyBlockedClosed_of_deepCut
    (hdeep : AtomBlockedDeepCutClosed) : AtomDoublyBlockedClosed := by
  intro atom scale hpos hsmall hframe hfail
  refine hdeep atom scale hpos hsmall hframe
    (blocked_of_singleFail hframe (fun slot => (hpos slot).le) hfail) ?_
  exact singleFail_singleCut_nonpos hframe (fun slot => (hpos slot).le) hsmall hfail

/-- **THE SPLIT OF THE DEEP STRATUM IS LOSSLESS.** -/
theorem atomBlockedDeepCutClosed_iff_singleBudgetDeep_and_doublyBlocked :
    AtomBlockedDeepCutClosed
      ↔ AtomSingleBudgetDeepClosed ∧ AtomDoublyBlockedClosed :=
  ⟨fun hdeep => ⟨atomSingleBudgetDeepClosed_of_deepCut hdeep,
      atomDoublyBlockedClosed_of_deepCut hdeep⟩,
    fun hparts => atomBlockedDeepCutClosed_of_singleBudgetDeep_of_doublyBlocked
      hparts.1 hparts.2⟩

/-- The doubly blocked stratum lives above the single onset. -/
theorem singleCut_nonpos_of_doublyBlocked {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) (hsmall : (∑ slot, scale slot) < 1)
    (hfail : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)) :
    singleCut (∑ slot, scale slot) ≤ 0 :=
  singleFail_singleCut_nonpos hframe hscale hsmall hfail

/-! ## Layer 3 — the global kills of the two deep parts -/

/-- **THE GLOBAL KILL OF THE SINGLE-BUDGET DEEP PART.** -/
def AtomSingleBudgetDeepKill : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) →
    singleCut (∑ slot, scale slot) ≤ 0 →
    (∃ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot
      ∧ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)
        < atomShiftedDiag atom scale pivot) →
    (∀ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne → pivot ≠ slotTwo → slotOne ≠ slotTwo →
      0 < atomShiftedDiag atom scale pivot →
      0 < atomPairMinor atom scale pivot slotOne →
      atomPairMinor atom scale pivot slotOne
          * atomPairMinor atom scale pivot slotTwo
        ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2) →
    False

/-- **THE GLOBAL KILL OF THE DOUBLY BLOCKED PART.** -/
def AtomDoublyBlockedKill : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)) →
    (∀ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne → pivot ≠ slotTwo → slotOne ≠ slotTwo →
      0 < atomShiftedDiag atom scale pivot →
      0 < atomPairMinor atom scale pivot slotOne →
      atomPairMinor atom scale pivot slotOne
          * atomPairMinor atom scale pivot slotTwo
        ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2) →
    False

theorem atomSingleBudgetDeepClosed_of_kill
    (hkill : AtomSingleBudgetDeepKill) : AtomSingleBudgetDeepClosed := by
  intro atom scale hpos hsmall hframe hblocked hcut hex
  by_contra hno
  push Not at hno
  exact hkill atom scale hpos hsmall hframe hblocked hcut hex hno

theorem atomSingleBudgetDeepKill_of_closed
    (hclosed : AtomSingleBudgetDeepClosed) : AtomSingleBudgetDeepKill := by
  intro atom scale hpos hsmall hframe hblocked hcut hex hfail
  obtain ⟨pivot, slotOne, slotTwo, honePivot, htwoPivot, hpairNe, hlive, hminor,
    hcross⟩ := hclosed atom scale hpos hsmall hframe hblocked hcut hex
  exact absurd hcross
    (not_lt.mpr (hfail pivot slotOne slotTwo honePivot htwoPivot hpairNe hlive hminor))

theorem atomSingleBudgetDeepClosed_iff_kill :
    AtomSingleBudgetDeepClosed ↔ AtomSingleBudgetDeepKill :=
  ⟨atomSingleBudgetDeepKill_of_closed, atomSingleBudgetDeepClosed_of_kill⟩

theorem atomDoublyBlockedClosed_of_kill
    (hkill : AtomDoublyBlockedKill) : AtomDoublyBlockedClosed := by
  intro atom scale hpos hsmall hframe hfail
  by_contra hno
  push Not at hno
  exact hkill atom scale hpos hsmall hframe hfail hno

theorem atomDoublyBlockedKill_of_closed
    (hclosed : AtomDoublyBlockedClosed) : AtomDoublyBlockedKill := by
  intro atom scale hpos hsmall hframe hfail hpairFail
  obtain ⟨pivot, slotOne, slotTwo, honePivot, htwoPivot, hpairNe, hlive, hminor,
    hcross⟩ := hclosed atom scale hpos hsmall hframe hfail
  exact absurd hcross
    (not_lt.mpr (hpairFail pivot slotOne slotTwo honePivot htwoPivot hpairNe hlive hminor))

theorem atomDoublyBlockedClosed_iff_kill :
    AtomDoublyBlockedClosed ↔ AtomDoublyBlockedKill :=
  ⟨atomDoublyBlockedKill_of_closed, atomDoublyBlockedClosed_of_kill⟩

/-! ## Layer 4 — the cell and the payoff from the three sharp parts -/

/-- **THE BLOCKED RESIDUE FROM THE THREE SHARP PARTS.**  The window
between the two cuts, the deep part with a single-budget pivot, and the
doubly blocked part. -/
theorem atomBlockedPairClosed_of_three_parts
    (hwindow : AtomBlockedWindowClosed) (hbudget : AtomSingleBudgetDeepClosed)
    (hdouble : AtomDoublyBlockedClosed) : AtomBlockedPairClosed :=
  atomBlockedPairClosed_of_window_of_deepCut hwindow
    (atomBlockedDeepCutClosed_of_singleBudgetDeep_of_doublyBlocked hbudget hdouble)

/-- **THE THREE-PART SPLIT IS LOSSLESS.** -/
theorem atomBlockedPairClosed_iff_three_parts :
    AtomBlockedPairClosed
      ↔ AtomBlockedWindowClosed ∧ AtomSingleBudgetDeepClosed
        ∧ AtomDoublyBlockedClosed := by
  constructor
  · intro hresidue
    have hparts := atomBlockedPairClosed_iff_window_and_deepCut.mp hresidue
    exact ⟨hparts.1, atomSingleBudgetDeepClosed_of_deepCut hparts.2,
      atomDoublyBlockedClosed_of_deepCut hparts.2⟩
  · intro hparts
    exact atomBlockedPairClosed_of_three_parts hparts.1 hparts.2.1 hparts.2.2

/-- **THE `(6,3)` CELL FROM THE THREE SHARP PARTS.** -/
theorem gtzWeighted_six_three_of_three_parts
    (hwindow : AtomBlockedWindowClosed) (hbudget : AtomSingleBudgetDeepClosed)
    (hdouble : AtomDoublyBlockedClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_blockedPair
    (atomBlockedPairClosed_of_three_parts hwindow hbudget hdouble)

/-- **THE RANK-THREE PAYOFF FROM THE THREE SHARP PARTS.** -/
theorem gtzWeightedAll_three_of_three_parts
    (hwindow : AtomBlockedWindowClosed) (hbudget : AtomSingleBudgetDeepClosed)
    (hdouble : AtomDoublyBlockedClosed) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_blockedPair
    (atomBlockedPairClosed_of_three_parts hwindow hbudget hdouble)

/-- The crux type is empty under the three sharp parts. -/
theorem isEmpty_sixThreeCrux_of_three_parts
    (hwindow : AtomBlockedWindowClosed) (hbudget : AtomSingleBudgetDeepClosed)
    (hdouble : AtomDoublyBlockedClosed) : IsEmpty SixThreeCrux :=
  isEmpty_sixThreeCrux_of_blockedPair
    (atomBlockedPairClosed_of_three_parts hwindow hbudget hdouble)

/-- **THE `(6,3)` CELL FROM THE THREE GLOBAL KILLS.** -/
theorem gtzWeighted_six_three_of_three_kills
    (hwindow : AtomBlockedWindowKill) (hbudget : AtomSingleBudgetDeepKill)
    (hdouble : AtomDoublyBlockedKill) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_three_parts
    (atomBlockedWindowClosed_of_windowKill hwindow)
    (atomSingleBudgetDeepClosed_of_kill hbudget)
    (atomDoublyBlockedClosed_of_kill hdouble)

/-- **THE RANK-THREE PAYOFF FROM THE THREE GLOBAL KILLS.** -/
theorem gtzWeightedAll_three_of_three_kills
    (hwindow : AtomBlockedWindowKill) (hbudget : AtomSingleBudgetDeepKill)
    (hdouble : AtomDoublyBlockedKill) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_three_parts
    (atomBlockedWindowClosed_of_windowKill hwindow)
    (atomSingleBudgetDeepClosed_of_kill hbudget)
    (atomDoublyBlockedClosed_of_kill hdouble)

end Gtz
