import Gtz.Wave.AtomTrineCutBand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The slot excess, the sharp unconditional thresholds, and the rigidity law

The two cuts of the previous module come from one per-slot bound.  This
module makes that bound a first class object, reads it as the exact gap
of the landed budgets, and draws the three consequences that the sharp
thresholds make available.

The SLOT EXCESS of a pivot is `diagonal * (1 - mass + 3 * scale) - scale *
(3 - mass + scale)`.  It is EXACTLY the amount by which the double
inflation budget clears at that pivot, thus a positive excess at any live
slot supplies the deflated pair and the dominating carrier with no other
hypothesis.  The SINGLE SLOT EXCESS does the same for the single
inflation budget with the coefficient two in place of three.

Three consequences follow.

First, the HEAVY stratum is superseded.  A heavy slot has excess at least
`2 (1 - mass) (1 - scale) / 3`, thus it clears the budget with a margin
that the landed heavy law never names.

Second, the UNCONDITIONAL THRESHOLD moves.  Every scale family of mass at
most `779/1000` carries a dominating card-three carrier, and every family
of mass at most `93/100` carries a live pivot of single budget.  The
landed thresholds are `13/20`, which is `0.65`, and `39/50`, which is
`0.78`.

Third, the blocked stratum is RIGID.  The six tangent gaps of the sharp
threshold add to `-3 (2 - mass) * trineCut mass`, and every one of them is
nonnegative at a blocked datum.  Thus each gap is capped by that total,
and near the trine onset the cap goes to zero: every light slot must carry
the uniform scale `mass / 6` and every blocked inequality must be nearly
an equality.  The adversarial floor datum of the previous sessions has
exactly that shape, which the identity now explains.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.blockedSlotExcess`, `Gtz.singleSlotExcess`,
  `Gtz.blockedSlotExcess_eq_budget_gap`,
  `Gtz.singleSlotExcess_eq_budget_gap` — **THE SLOT EXCESS IS THE BUDGET
  GAP**, exactly and unconditionally.
* `Gtz.blockedSlotExcess_nonpos_of_blocked`,
  `Gtz.singleSlotExcess_nonpos_of_singleFail` — the per-slot laws that
  the two sharp thresholds consume, made public.
* `Gtz.exists_deflated_pair_of_slot_excess`,
  `Gtz.exists_dominating_carrier_of_slot_excess`,
  `Gtz.exists_pivot_single_budget_of_single_excess` — **THE PER-SLOT
  DISPATCHES.**
* `Gtz.blockedSlotExcess_of_heavy_slot` — **THE HEAVY STRATUM WITH A
  MARGIN**, which supersedes the landed heavy law.
* `Gtz.exists_dominating_triple_of_scale_le_split`,
  `Gtz.exists_deflated_pair_of_scale_le_split`,
  `Gtz.exists_pivot_single_budget_of_scale_le_split` — **THE SHARP
  UNCONDITIONAL THRESHOLDS** at `779/1000` and at `93/100`.
* `Gtz.blockedTangentGap`, `Gtz.blockedTangentGap_split`,
  `Gtz.blockedTangentGap_nonneg`, `Gtz.tangentGap_total_six`,
  `Gtz.blockedTangentGap_total` — **THE RIGIDITY IDENTITY**: the six
  tangent gaps add to the cut deficit.
* `Gtz.blockedTangentGap_le_total`,
  `Gtz.blocked_scale_deviation_le`,
  `Gtz.blocked_slack_le` — **THE RIGIDITY BOUNDS**: at a blocked datum
  every light slot sits near the uniform scale and every blocked
  inequality is nearly an equality, both by the cut deficit.
* `Gtz.atomBlockedDeepClosed_of_window_of_deepCut`,
  `Gtz.atomBlockedWindowClosed_of_band_of_deep`,
  `Gtz.atomBlockedDeepCutClosed_of_band_of_deep`,
  `Gtz.blockedSplit_iff_sharpSplit` — **THE TWO SPLITS ARE EQUIVALENT**,
  thus the refinement gives up nothing.
* `Gtz.gtzWeighted_six_three_of_sharpSplit`,
  `Gtz.gtzWeightedAll_three_of_sharpSplit`,
  `Gtz.isEmpty_sixThreeCrux_of_sharpSplit` — the cell and the rank-three
  payoff from the sharp split.

## Vacuity

Every law of layers zero thru three is an unconditional statement about a
family of vectors, a family of scales and one slot.  Layer four only
rearranges the landed residues, and the equivalence theorem proves that
the rearrangement is lossless.
-/

namespace Gtz

/-! ## Layer 0 — the slot excess -/

/-- The SLOT EXCESS of a pivot: the diagonal against the shifted scale,
minus the scale against the shifted rank.  It is exactly the amount by
which the DOUBLE inflation budget clears at that pivot. -/
def blockedSlotExcess {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount) : ℝ :=
  atomGram atom pivot pivot * (1 - (∑ slot, scale slot) + 3 * scale pivot)
    - scale pivot * (3 - (∑ slot, scale slot) + scale pivot)

/-- The SINGLE SLOT EXCESS of a pivot: the same reading with the
deflation coefficient one.  It is exactly the amount by which the SINGLE
inflation budget clears at that pivot. -/
def singleSlotExcess {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount) : ℝ :=
  atomGram atom pivot pivot * (1 - (∑ slot, scale slot) + 2 * scale pivot)
    - scale pivot * (2 - (∑ slot, scale slot) + scale pivot)

/-- **THE EXCESS IS THE DOUBLE BUDGET GAP.**  The identity is polynomial
and unconditional. -/
theorem blockedSlotExcess_eq_budget_gap {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot : Fin slotCount) :
    blockedSlotExcess atom scale pivot
      = atomShiftedDiag atom scale pivot
        - (((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) := by
  simp only [blockedSlotExcess, atomShiftedDiag]
  ring

/-- **THE SINGLE EXCESS IS THE SINGLE BUDGET GAP.** -/
theorem singleSlotExcess_eq_budget_gap {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot : Fin slotCount) :
    singleSlotExcess atom scale pivot
      = atomShiftedDiag atom scale pivot
        - (((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)) := by
  simp only [singleSlotExcess, atomShiftedDiag]
  ring

/-- **THE BLOCKED DATUM HAS NO SLOT EXCESS.**  At a live slot the blocked
inequality is exactly the nonpositive excess, and a dead slot has a
diagonal below its scale, which gives the same reading. -/
theorem blockedSlotExcess_nonpos_of_blocked {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ} (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hblocked : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot))
    (pivot : Fin 6) : blockedSlotExcess atom scale pivot ≤ 0 := by
  have hslotLe : scale pivot ≤ ∑ slot, scale slot :=
    Finset.single_le_sum (f := scale) (fun i _ => hscale i) (Finset.mem_univ pivot)
  rcases le_or_gt (atomShiftedDiag atom scale pivot) 0 with hdead | hlive
  · have hdiagLe : atomGram atom pivot pivot ≤ scale pivot := by
      simp only [atomShiftedDiag] at hdead
      linarith
    have hU : 0 < 1 - (∑ slot, scale slot) + 3 * scale pivot := by
      linarith [hscale pivot]
    have hunit : scale pivot ≤ 1 := le_trans hslotLe (le_of_lt hsmall)
    simp only [blockedSlotExcess]
    nlinarith [mul_le_mul_of_nonneg_right hdiagLe hU.le,
      mul_nonneg (hscale pivot) (by linarith : (0:ℝ) ≤ 1 - scale pivot)]
  · have hb := hblocked pivot hlive
    rw [blockedSlotExcess_eq_budget_gap]
    linarith [hb]

/-- **THE SINGLE-BUDGET FAILURE HAS NO SINGLE SLOT EXCESS.** -/
theorem singleSlotExcess_nonpos_of_singleFail {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ} (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hfail : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot))
    (pivot : Fin 6) : singleSlotExcess atom scale pivot ≤ 0 := by
  have hslotLe : scale pivot ≤ ∑ slot, scale slot :=
    Finset.single_le_sum (f := scale) (fun i _ => hscale i) (Finset.mem_univ pivot)
  rcases le_or_gt (atomShiftedDiag atom scale pivot) 0 with hdead | hlive
  · have hdiagLe : atomGram atom pivot pivot ≤ scale pivot := by
      simp only [atomShiftedDiag] at hdead
      linarith
    have hU : 0 < 1 - (∑ slot, scale slot) + 2 * scale pivot := by
      linarith [hscale pivot]
    have hunit : scale pivot ≤ 1 := le_trans hslotLe (le_of_lt hsmall)
    simp only [singleSlotExcess]
    nlinarith [mul_le_mul_of_nonneg_right hdiagLe hU.le,
      mul_nonneg (hscale pivot) (by linarith : (0:ℝ) ≤ 1 - scale pivot)]
  · have hb := hfail pivot hlive
    rw [singleSlotExcess_eq_budget_gap]
    linarith [hb]

/-! ## Layer 1 — the per-slot dispatches -/

/-- **THE PER-SLOT DISPATCH.**  A live slot of positive excess supplies
the deflated pair.  This is the sharpest per-slot criterion available:
the excess IS the budget gap, thus no weaker slot condition can work. -/
theorem exists_deflated_pair_of_slot_excess
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hexcess : 0 < blockedSlotExcess atom scale pivot) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ 0 < atomPairMinor atom scale pivot slotTwo
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo := by
  refine exists_deflated_pair_of_pivot_budget hframe hscale hpivot ?_
  rw [blockedSlotExcess_eq_budget_gap] at hexcess
  linarith [hexcess]

/-- **THE PER-SLOT CARRIER.**  A live slot of positive excess supplies a
dominating card-three carrier. -/
theorem exists_dominating_carrier_of_slot_excess
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hexcess : 0 < blockedSlotExcess atom scale pivot) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
          (∑ slot, scale slot * probe slot ^ 2)
            < atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  refine exists_dominating_carrier_of_pivot_budget hframe hscale hpivot ?_
  rw [blockedSlotExcess_eq_budget_gap] at hexcess
  linarith [hexcess]

/-- **THE PER-SLOT SINGLE BUDGET.**  A live slot of positive single
excess carries the single inflation budget, thus the plane closure fires
there and the live budget engine applies. -/
theorem exists_pivot_single_budget_of_single_excess
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ} {pivot : Fin 6}
    (hexcess : 0 < singleSlotExcess atom scale pivot) :
    ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
        + scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot := by
  rw [singleSlotExcess_eq_budget_gap] at hexcess
  linarith [hexcess]

/-- **THE HEAVY SLOT WITH A MARGIN.**  A slot whose tripled diagonal
beats two plus its scale carries an excess of at least
`2 (1 - mass) (1 - scale) / 3`.  This SUPERSEDES the landed heavy law,
which names no margin. -/
theorem blockedSlotExcess_of_heavy_slot {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ} {pivot : Fin 6}
    (hscalePivot : 0 ≤ scale pivot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hheavy : 2 + scale pivot ≤ 3 * atomGram atom pivot pivot) :
    2 * (1 - (∑ slot, scale slot)) * (1 - scale pivot) / 3
      ≤ blockedSlotExcess atom scale pivot := by
  have hU : 0 < 1 - (∑ slot, scale slot) + 3 * scale pivot := by linarith
  have hstep : (2 + scale pivot) * (1 - (∑ slot, scale slot) + 3 * scale pivot)
      ≤ 3 * atomGram atom pivot pivot
        * (1 - (∑ slot, scale slot) + 3 * scale pivot) :=
    mul_le_mul_of_nonneg_right hheavy hU.le
  simp only [blockedSlotExcess]
  nlinarith [hstep]

/-! ## Layer 2 — the sharp unconditional thresholds -/

/-- **THE SHARP UNCONDITIONAL CARRIER.**  Every scale family of mass at
most `779/1000` carries a dominating card-three carrier.  This SUPERSEDES
the landed `13/20` dispatch, which stops at `0.65`. -/
theorem exists_dominating_triple_of_scale_le_split
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsplit : (∑ slot, scale slot) ≤ 779 / 1000) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
          (∑ slot, scale slot * probe slot ^ 2)
            < atomBlend atom probe ⬝ᵥ atomBlend atom probe :=
  exists_dominating_triple_of_trineCut_pos hframe hscale
    (lt_of_le_of_lt hsplit (by norm_num))
    (lt_of_lt_of_le (by norm_num) (trineCut_pos_of_le_split hsplit))

/-- **THE SHARP UNCONDITIONAL PAIR.**  Every scale family of mass at most
`779/1000` carries a deflated pair at some live pivot. -/
theorem exists_deflated_pair_of_scale_le_split
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsplit : (∑ slot, scale slot) ≤ 779 / 1000) :
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo :=
  exists_deflated_pair_of_trineCut_pos hframe hscale
    (lt_of_le_of_lt hsplit (by norm_num))
    (lt_of_lt_of_le (by norm_num) (trineCut_pos_of_le_split hsplit))

/-- **THE SHARP UNCONDITIONAL WINDOW.**  Every scale family of mass at
most `93/100` carries a live pivot of single budget.  This SUPERSEDES the
landed window `exists_pivot_single_budget_of_scale_le`, which stops at
`39/50`. -/
theorem exists_pivot_single_budget_of_scale_le_split
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsplit : (∑ slot, scale slot) ≤ 93 / 100) :
    ∃ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot
      ∧ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)
        < atomShiftedDiag atom scale pivot :=
  exists_pivot_single_budget_of_singleCut_pos hframe hscale
    (lt_of_le_of_lt hsplit (by norm_num))
    (lt_of_lt_of_le (by norm_num) (singleCut_pos_of_le_split hsplit))

/-! ## Layer 3 — the rigidity identity -/

/-- The TANGENT GAP of a slot: the slack of the tangent step of the sharp
blocked threshold.  It splits into a deviation term, which measures the
distance of the scale from the uniform value, and a slack term, which
measures how far the blocked inequality is from an equality. -/
def blockedTangentGap {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount) : ℝ :=
  (3 * scale pivot + 8 - 2 * (∑ slot, scale slot) - 9 * atomGram atom pivot pivot)
      * ((∑ slot, scale slot) - 6 * scale pivot) ^ 2
    - 36 * blockedSlotExcess atom scale pivot * (1 - 3 * scale pivot)

/-- **THE TANGENT GAP IS THE SLACK OF THE TANGENT STEP.**  The identity
is polynomial and unconditional. -/
theorem blockedTangentGap_split {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot : Fin slotCount) :
    blockedTangentGap atom scale pivot
      = (2 - (∑ slot, scale slot)) ^ 2
          * (3 * scale pivot + 8 - 2 * (∑ slot, scale slot)
            - 9 * atomGram atom pivot pivot)
        - 4 * (2 * (1 - (∑ slot, scale slot)) * (4 - (∑ slot, scale slot)))
          * (1 - 3 * scale pivot) := by
  simp only [blockedTangentGap, blockedSlotExcess]
  ring

/-- **THE TANGENT GAP IS NONNEGATIVE AT A BLOCKED DATUM.** -/
theorem blockedTangentGap_nonneg {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hscale : ∀ slot, 0 ≤ scale slot) (hsmall : (∑ slot, scale slot) < 1)
    (hblocked : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot))
    (pivot : Fin 6) : 0 ≤ blockedTangentGap atom scale pivot := by
  have hexcess := blockedSlotExcess_nonpos_of_blocked hscale hsmall hblocked pivot
  have hbound : atomGram atom pivot pivot
        * (1 - (∑ slot, scale slot) + 3 * scale pivot)
      ≤ scale pivot * (3 - (∑ slot, scale slot) + scale pivot) := by
    simp only [blockedSlotExcess] at hexcess
    linarith [hexcess]
  have htangent := blocked_slot_tangent hsmall (hscale pivot) hbound
  rw [blockedTangentGap_split]
  linarith [htangent]

/-- **THE SIX TANGENT GAPS ADD TO THE CUT DEFICIT.**  The scalar identity
behind the rigidity law: under the two sum constraints the total is
`-3 (2 - mass) * trineCut mass`, with no other input. -/
theorem tangentGap_total_six
    {mass scaleZero scaleOne scaleTwo scaleThree scaleFour scaleFive
      diagZero diagOne diagTwo diagThree diagFour diagFive : ℝ}
    (hmassSum : scaleZero + scaleOne + scaleTwo + scaleThree + scaleFour + scaleFive
      = mass)
    (htraceSum : diagZero + diagOne + diagTwo + diagThree + diagFour + diagFive = 3) :
    ((2 - mass) ^ 2 * (3 * scaleZero + 8 - 2 * mass - 9 * diagZero)
        - 4 * (2 * (1 - mass) * (4 - mass)) * (1 - 3 * scaleZero))
      + ((2 - mass) ^ 2 * (3 * scaleOne + 8 - 2 * mass - 9 * diagOne)
        - 4 * (2 * (1 - mass) * (4 - mass)) * (1 - 3 * scaleOne))
      + ((2 - mass) ^ 2 * (3 * scaleTwo + 8 - 2 * mass - 9 * diagTwo)
        - 4 * (2 * (1 - mass) * (4 - mass)) * (1 - 3 * scaleTwo))
      + ((2 - mass) ^ 2 * (3 * scaleThree + 8 - 2 * mass - 9 * diagThree)
        - 4 * (2 * (1 - mass) * (4 - mass)) * (1 - 3 * scaleThree))
      + ((2 - mass) ^ 2 * (3 * scaleFour + 8 - 2 * mass - 9 * diagFour)
        - 4 * (2 * (1 - mass) * (4 - mass)) * (1 - 3 * scaleFour))
      + ((2 - mass) ^ 2 * (3 * scaleFive + 8 - 2 * mass - 9 * diagFive)
        - 4 * (2 * (1 - mass) * (4 - mass)) * (1 - 3 * scaleFive))
      = -(3 * (2 - mass) * trineCut mass) := by
  simp only [trineCut]
  have hscaleFive : scaleFive
      = mass - (scaleZero + scaleOne + scaleTwo + scaleThree + scaleFour) := by
    linarith [hmassSum]
  have hdiagFive : diagFive
      = 3 - (diagZero + diagOne + diagTwo + diagThree + diagFour) := by
    linarith [htraceSum]
  rw [hscaleFive, hdiagFive]
  ring

/-- **THE RIGIDITY IDENTITY.**  The six tangent gaps of a tight frame add
to `-3 (2 - mass) * trineCut mass`.  At a blocked datum the cut is
nonpositive, thus the total is nonnegative, and every gap is nonnegative
by the tangent law. -/
theorem blockedTangentGap_total {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ pivot, blockedTangentGap atom scale pivot)
      = -(3 * (2 - (∑ slot, scale slot)) * trineCut (∑ slot, scale slot)) := by
  have hmassSum : scale 0 + scale 1 + scale 2 + scale 3 + scale 4 + scale 5
      = ∑ slot, scale slot := by rw [Fin.sum_univ_six]
  have htraceSum : atomGram atom 0 0 + atomGram atom 1 1 + atomGram atom 2 2
      + atomGram atom 3 3 + atomGram atom 4 4 + atomGram atom 5 5 = 3 := by
    have htrace : (∑ slot, atomGram atom slot slot) = 3 := by
      simpa using atomGram_trace hframe
    rw [← htrace, Fin.sum_univ_six]
  have hsix : (∑ pivot, blockedTangentGap atom scale pivot)
      = blockedTangentGap atom scale 0 + blockedTangentGap atom scale 1
        + blockedTangentGap atom scale 2 + blockedTangentGap atom scale 3
        + blockedTangentGap atom scale 4 + blockedTangentGap atom scale 5 := by
    rw [Fin.sum_univ_six]
  rw [hsix, blockedTangentGap_split, blockedTangentGap_split, blockedTangentGap_split,
    blockedTangentGap_split, blockedTangentGap_split, blockedTangentGap_split]
  exact tangentGap_total_six hmassSum htraceSum

/-- **EVERY TANGENT GAP IS CAPPED BY THE CUT DEFICIT.**  The other five
gaps are nonnegative, thus each single gap is at most the total.  Near
the trine onset the cap goes to zero. -/
theorem blockedTangentGap_le_total {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) (hsmall : (∑ slot, scale slot) < 1)
    (hblocked : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot))
    (pivot : Fin 6) :
    blockedTangentGap atom scale pivot
      ≤ -(3 * (2 - (∑ slot, scale slot)) * trineCut (∑ slot, scale slot)) := by
  have htotal := blockedTangentGap_total (scale := scale) hframe
  have hnonneg : ∀ other : Fin 6, 0 ≤ blockedTangentGap atom scale other :=
    blockedTangentGap_nonneg hscale hsmall hblocked
  have hsplit : (∑ other, blockedTangentGap atom scale other)
      = blockedTangentGap atom scale pivot
        + ∑ other ∈ Finset.univ.erase pivot, blockedTangentGap atom scale other :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ pivot)).symm
  have hrest : 0 ≤ ∑ other ∈ Finset.univ.erase pivot,
      blockedTangentGap atom scale other :=
    Finset.sum_nonneg fun other _ => hnonneg other
  linarith [htotal, hsplit, hrest]

/-- **THE SCALES OF A BLOCKED DATUM SIT NEAR THE UNIFORM VALUE.**  At a
light slot, whose scale is at most one third, the deviation term alone is
capped by the cut deficit.  Near the trine onset the deficit vanishes,
thus every light slot carries the uniform scale `mass / 6`. -/
theorem blocked_scale_deviation_le {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) (hsmall : (∑ slot, scale slot) < 1)
    (hblocked : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot))
    {pivot : Fin 6} (hlight : scale pivot ≤ 1 / 3) :
    (3 * scale pivot + 8 - 2 * (∑ slot, scale slot)
        - 9 * atomGram atom pivot pivot)
        * ((∑ slot, scale slot) - 6 * scale pivot) ^ 2
      ≤ -(3 * (2 - (∑ slot, scale slot)) * trineCut (∑ slot, scale slot)) := by
  have hcap := blockedTangentGap_le_total hframe hscale hsmall hblocked pivot
  have hexcess := blockedSlotExcess_nonpos_of_blocked hscale hsmall hblocked pivot
  have hsign : 0 ≤ -(36 * blockedSlotExcess atom scale pivot * (1 - 3 * scale pivot)) := by
    have hone : (0:ℝ) ≤ 1 - 3 * scale pivot := by linarith
    nlinarith [hexcess, hone]
  simp only [blockedTangentGap] at hcap
  linarith [hcap, hsign]

/-- **THE BLOCKED INEQUALITIES OF A BLOCKED DATUM ARE NEARLY
EQUALITIES.**  Wherever the diagonal stays below the splitting level, the
slack term alone is capped by the cut deficit.  Near the trine onset the
deficit vanishes, thus every such slot is blocked with equality. -/
theorem blocked_slack_le {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) (hsmall : (∑ slot, scale slot) < 1)
    (hblocked : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot))
    {pivot : Fin 6}
    (hdiag : 9 * atomGram atom pivot pivot
      ≤ 3 * scale pivot + 8 - 2 * (∑ slot, scale slot)) :
    -(36 * blockedSlotExcess atom scale pivot * (1 - 3 * scale pivot))
      ≤ -(3 * (2 - (∑ slot, scale slot)) * trineCut (∑ slot, scale slot)) := by
  have hcap := blockedTangentGap_le_total hframe hscale hsmall hblocked pivot
  have hdev : 0 ≤ (3 * scale pivot + 8 - 2 * (∑ slot, scale slot)
        - 9 * atomGram atom pivot pivot)
      * ((∑ slot, scale slot) - 6 * scale pivot) ^ 2 :=
    mul_nonneg (by linarith [hdiag]) (sq_nonneg _)
  simp only [blockedTangentGap] at hcap
  linarith [hcap, hdev]

/-! ## Layer 4 — the two splits agree -/

/-- **THE SHARP SPLIT CLOSES THE LANDED DEEP PART.**  A blocked datum of
scale mass above `39/50` sits in the window or in the sharp deep
stratum. -/
theorem atomBlockedDeepClosed_of_window_of_deepCut
    (hwindow : AtomBlockedWindowClosed) (hdeep : AtomBlockedDeepCutClosed) :
    AtomBlockedDeepClosed := by
  intro atom scale hpos hsmall hframe hblocked _
  have hcut := blocked_trineCut_nonpos hframe (fun slot => (hpos slot).le) hsmall hblocked
  rcases le_or_gt (singleCut (∑ slot, scale slot)) 0 with hside | hside
  · exact hdeep atom scale hpos hsmall hframe hblocked hside
  · exact hwindow atom scale hpos hsmall hframe hblocked hcut hside

/-- The landed split closes the window. -/
theorem atomBlockedWindowClosed_of_band_of_deep
    (hband : AtomBlockedBandClosed) (hdeep : AtomBlockedDeepClosed) :
    AtomBlockedWindowClosed :=
  atomBlockedWindowClosed_of_blockedPair
    (atomBlockedPairClosed_of_band_of_deep hband hdeep)

/-- The landed split closes the sharp deep stratum. -/
theorem atomBlockedDeepCutClosed_of_band_of_deep
    (hband : AtomBlockedBandClosed) (hdeep : AtomBlockedDeepClosed) :
    AtomBlockedDeepCutClosed :=
  atomBlockedDeepCutClosed_of_blockedPair
    (atomBlockedPairClosed_of_band_of_deep hband hdeep)

/-- **THE TWO SPLITS ARE EQUIVALENT.**  The sharp split of the blocked
residue gives up nothing against the landed one, and it moves both
boundaries: the lower one from `13/20` to the trine onset, the upper one
from `39/50` to the single onset. -/
theorem blockedSplit_iff_sharpSplit :
    (AtomBlockedBandClosed ∧ AtomBlockedDeepClosed)
      ↔ (AtomBlockedWindowClosed ∧ AtomBlockedDeepCutClosed) :=
  ⟨fun hpair => ⟨atomBlockedWindowClosed_of_band_of_deep hpair.1 hpair.2,
      atomBlockedDeepCutClosed_of_band_of_deep hpair.1 hpair.2⟩,
    fun hpair => ⟨atomBlockedBandClosed_of_windowClosed hpair.1,
      atomBlockedDeepClosed_of_window_of_deepCut hpair.1 hpair.2⟩⟩

/-- **THE `(6,3)` CELL FROM THE SHARP SPLIT.** -/
theorem gtzWeighted_six_three_of_sharpSplit
    (hwindow : AtomBlockedWindowClosed) (hdeep : AtomBlockedDeepCutClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_window_of_deepCut hwindow hdeep

/-- **THE RANK-THREE PAYOFF FROM THE SHARP SPLIT.** -/
theorem gtzWeightedAll_three_of_sharpSplit
    (hwindow : AtomBlockedWindowClosed) (hdeep : AtomBlockedDeepCutClosed) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_window_of_deepCut hwindow hdeep

/-- The crux type is empty under the sharp split. -/
theorem isEmpty_sixThreeCrux_of_sharpSplit
    (hwindow : AtomBlockedWindowClosed) (hdeep : AtomBlockedDeepCutClosed) :
    IsEmpty SixThreeCrux :=
  isEmpty_sixThreeCrux_of_window_of_deepCut hwindow hdeep

end Gtz
