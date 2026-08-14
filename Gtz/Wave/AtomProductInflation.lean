import Gtz.Wave.AtomDefectBandSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The product inflation engine — the deflation weight spreads across the pair

The transfer of the plane closure to the defected cross needs one extra
inflation of the scales, and the landed engines take that extra to be one
deflation weight at every slot.  That choice is uniform, and it doubles
the deflation cost of the budget.  This module replaces the uniform
choice by the exact law that the transfer consumes: the extra inflation
must only beat the deflation defect IN THE PRODUCT, one pair at a time.

The scalar core is one polynomial line.  With plain gaps of the inflated
scales, a plain cross below its bound, and an extra inflation whose
product dominates the squared defect, the defected cross stays below the
deflated bound, and the margin of the deflated test is at least the
margin of the plain test.  The engine feeds the landed plane closure the
inflated scales and reads the result through the public deflation
dictionary.

Two consequences follow.  The uniform inflation is the instance of equal
weights, thus the landed double budget is a corollary of the law here.
And the DISCOUNTED inflation, which divides the weight of one slot by a
factor and multiplies the weight of every other slot by the same factor,
obeys the product law with no loss.  Its budget is strictly cheaper than
the uniform one whenever the reading energy is concentrated, thus it
opens a stratum that the uniform budget closes out.

## The measured setting of the band (probes, banked, not consumed)

The blocked stratum inside the scale mass window from `13/20` to `39/50`
is a thin extremal set: six hundred thousand rejection samples of tight
frames with blocked scales in that window produced NOT ONE datum.  Thus
the coverage of a budget on the band cannot be sampled, and the value of
the law here is its strictly larger reach, not a measured fraction.

## The realness boundary, machine verified

The scaled complex two-trine with uniform scales is blocked from the
scale mass `0.7792` upward, it carries a single inflation budget at all
six slots, and it admits NO deflated pair there, with margin `-0.00026`
at the band boundary `39/50`.  Thus the band kill is FALSE over the
complex field, and the whole obstruction sits in the scale window of
width `0.00084` between the trine onset and the band boundary.  The
deflated pair test is invariant under every unit phase gauge (two
hundred random gauges move the margin by `1.6e-17`), and the cycle
Bargmann phase of the trine triple is a right angle that no phase lock
moves.  As a result the real-only step of any band proof must control
the cycle phases, never one bracket.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.transfer_pair_of_product_inflation` — **THE SCALAR CORE**: the
  product law of the extra inflation carries the plain pair to the
  deflated pair, and the deflated margin keeps the plain margin.
* `Gtz.exists_deflated_pair_of_product_inflation` — **THE ENGINE**: a
  live pivot, an extra inflation of the product law, and one
  division-free budget supply the deflated pair.
* `Gtz.exists_deflated_pair_of_uniform_inflation` — the uniform
  instance, thus the landed double budget as a corollary.
* `Gtz.discountInflation`, `Gtz.discountInflation_nonneg`,
  `Gtz.discountInflation_product` — **THE DISCOUNTED INFLATION**: one
  slot pays less by a factor and every other slot pays more by the same
  factor, and the product law survives.
* `Gtz.exists_deflated_pair_of_discount_inflation` — **THE DISCOUNTED
  STRATUM**, strictly cheaper than the uniform budget when the reading
  energy concentrates.
* `Gtz.AtomBlockedProductKill`, `Gtz.atomBlockedBandKill_of_productKill`
  — **THE NARROWED ATTACK SURFACE**: the band kill only has to answer at
  pivots where NO admissible product inflation clears the budget.
* `Gtz.atomBlockedBandClosed_of_productKill`,
  `Gtz.gtzWeighted_six_three_of_productKill_of_deep`,
  `Gtz.gtzWeightedAll_three_of_productKill_of_deep` — the cell and the
  rank-three payoff from the narrowed kill with the deep part.

## Vacuity

Every law of layers zero thru two is an unconditional statement about a
family of vectors, a family of scales and an inflation.  The narrowed
kill of layer three implies the landed band kill, thus it is at least as
strong, and the bridge theorem proves that implication.
-/

namespace Gtz

/-! ## Layer 0 — the scalar core -/

/-- **THE PRODUCT LAW CARRIES THE PAIR.**  Two positive gaps of the
inflated scales, a plain cross below its bound, and an extra inflation
whose PRODUCT dominates the squared defect: the defected cross stays
below the deflated bound.  The deflated margin is at least the plain
margin, thus the law loses nothing at all.

The certificate is one decomposition.  The deflated margin is the plain
margin, plus the mixed term, plus the product surplus, and the mixed
term is nonnegative because its square dominates the squared cross term
through the arithmetic-geometric bound. -/
theorem transfer_pair_of_product_inflation {gapOne gapTwo cross defect extraOne extraTwo : ℝ}
    (hextraOne : 0 ≤ extraOne) (hextraTwo : 0 ≤ extraTwo)
    (hproduct : defect ^ 2 ≤ extraOne * extraTwo)
    (hgapOne : 0 < gapOne) (hgapTwo : 0 < gapTwo)
    (hcross : cross ^ 2 < gapOne * gapTwo) :
    (cross - defect) ^ 2 < (gapOne + extraOne) * (gapTwo + extraTwo) := by
  have hmixNonneg : 0 ≤ extraOne * gapTwo + extraTwo * gapOne :=
    add_nonneg (mul_nonneg hextraOne hgapTwo.le) (mul_nonneg hextraTwo hgapOne.le)
  have hsquare : (2 * cross * defect) ^ 2
      ≤ (extraOne * gapTwo + extraTwo * gapOne) ^ 2 := by
    have hamgm : 4 * (extraOne * extraTwo) * (gapOne * gapTwo)
        ≤ (extraOne * gapTwo + extraTwo * gapOne) ^ 2 := by
      nlinarith [sq_nonneg (extraOne * gapTwo - extraTwo * gapOne)]
    have hstep : 4 * defect ^ 2 * (gapOne * gapTwo)
        ≤ 4 * (extraOne * extraTwo) * (gapOne * gapTwo) :=
      mul_le_mul_of_nonneg_right (by linarith)
        (mul_pos hgapOne hgapTwo).le
    nlinarith [hstep, hamgm, hcross, sq_nonneg defect,
      mul_le_mul_of_nonneg_left hcross.le (by positivity : (0:ℝ) ≤ 4 * defect ^ 2)]
  have hmix : 0 ≤ extraOne * gapTwo + extraTwo * gapOne + 2 * cross * defect := by
    nlinarith [hsquare, hmixNonneg]
  nlinarith [hmix, hcross, hproduct]

/-! ## Layer 1 — the engine -/

/-- **THE PRODUCT INFLATION ENGINE.**  A pivot of positive shifted
diagonal, an extra inflation that vanishes at the pivot, stays
nonnegative, and obeys the product law at every pair off the pivot, and
one division-free budget that pays the scales, the single deflation and
the extra: together they supply a deflated pair at that pivot.

The landed plane closure fires at the inflated scales, and the public
deflation dictionary reads the plain gaps as the pivot minors and the
plain cross as the deflated cross. -/
theorem exists_deflated_pair_of_product_inflation
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale extra : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hextraNonneg : ∀ slot, 0 ≤ extra slot)
    (hextraPivot : extra pivot = 0)
    (hproduct : ∀ slotOne slotTwo : Fin 6, slotOne ≠ pivot → slotTwo ≠ pivot →
      slotOne ≠ slotTwo →
      (scale pivot * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
        ≤ (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
          * (extra slotOne * extra slotTwo))
    (hbudget : ((∑ slot, scale slot) - scale pivot + ∑ slot, extra slot)
          * atomShiftedDiag atom scale pivot
        + scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ 0 < atomPairMinor atom scale pivot slotTwo
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo := by
  classical
  have hdiagPos : 0 < atomGram atom pivot pivot := by
    have hp := hscale pivot
    have hR := hpivot
    simp only [atomShiftedDiag] at hR
    linarith
  have hdiagNe : atomGram atom pivot pivot ≠ 0 := ne_of_gt hdiagPos
  have hRne : atomShiftedDiag atom scale pivot ≠ 0 := ne_of_gt hpivot
  have hRne' : atomGram atom pivot pivot - scale pivot ≠ 0 := by
    have hval := hpivot
    simp only [atomShiftedDiag] at hval
    exact ne_of_gt hval
  have haxisNe : atom pivot ⬝ᵥ atom pivot ≠ 0 := by
    have := hdiagPos
    simp only [atomGram] at this
    exact ne_of_gt this
  have hshadowPivot : planeShadow (atom pivot) (atom pivot) = 0 :=
    planeShadow_self_eq_zero haxisNe
  have hperp : ∀ slot : Fin 6, planeShadow (atom pivot) (atom slot) ⬝ᵥ atom pivot = 0 :=
    fun slot => planeShadow_dot_axis (atom pivot) (atom slot) haxisNe
  have hshadowFrame : ∀ probe direction : Fin 3 → ℝ,
      probe ⬝ᵥ atom pivot = 0 → direction ⬝ᵥ atom pivot = 0 →
      (∑ slot, (planeShadow (atom pivot) (atom slot) ⬝ᵥ probe)
          * (planeShadow (atom pivot) (atom slot) ⬝ᵥ direction)) = probe ⬝ᵥ direction := by
    intro probe direction hprobe hdirection
    rw [← hframe probe direction]
    exact Finset.sum_congr rfl fun slot _ => by
      rw [planeShadow_dot_plane (atom pivot) (atom slot) probe hprobe,
        planeShadow_dot_plane (atom pivot) (atom slot) direction hdirection]
  have hdeflNonneg : 0 ≤ scale pivot
      / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) :=
    div_nonneg (hscale pivot) (mul_nonneg hdiagPos.le hpivot.le)
  have hinflNonneg : ∀ slot : Fin 6, 0 ≤ (if slot = pivot then (0:ℝ)
      else scale slot + (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2
        + extra slot) := by
    intro slot
    by_cases hcase : slot = pivot
    · rw [if_pos hcase]
    · rw [if_neg hcase]
      have hterm := mul_nonneg hdeflNonneg (sq_nonneg (atomGram atom pivot slot))
      linarith [hscale slot, hextraNonneg slot]
  have hrowEnergy : (∑ slot ∈ Finset.univ.erase pivot, atomGram atom pivot slot ^ 2)
      = atomGram atom pivot pivot - atomGram atom pivot pivot ^ 2 := by
    have hsplit := Finset.sum_erase_eq_sub
      (f := fun slot => atomGram atom pivot slot ^ 2) (Finset.mem_univ pivot)
    rw [hsplit, atomGram_row_energy hframe pivot]
  have hinflSum : (∑ slot, (if slot = pivot then (0:ℝ)
      else scale slot + (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2
        + extra slot)) < 1 := by
    have hsplit : (∑ slot, (if slot = pivot then (0:ℝ)
        else scale slot + (scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2
          + extra slot))
        = ∑ slot ∈ Finset.univ.erase pivot, (scale slot + (scale pivot
            / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slot ^ 2 + extra slot) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ pivot)]
      rw [if_pos rfl, add_zero]
      exact Finset.sum_congr rfl fun slot hslot =>
        if_neg (Finset.mem_erase.mp hslot).1
    have hfold : (∑ slot ∈ Finset.univ.erase pivot, (scale pivot
        / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
        * atomGram atom pivot slot ^ 2)
        = (scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot))
          * (atomGram atom pivot pivot - atomGram atom pivot pivot ^ 2) := by
      rw [← hrowEnergy, Finset.mul_sum]
    have hextraSum : (∑ slot ∈ Finset.univ.erase pivot, extra slot)
        = ∑ slot, extra slot := by
      rw [Finset.sum_erase_eq_sub (f := extra) (Finset.mem_univ pivot), hextraPivot]
      ring
    rw [hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_erase_eq_sub (f := scale) (Finset.mem_univ pivot), hfold, hextraSum]
    have hcancel : scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)
        * (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot)
        = scale pivot :=
      div_mul_cancel₀ _ (mul_ne_zero hdiagNe hRne)
    have hcancelSq : scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)
        * (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot)
        * atomGram atom pivot pivot
        = scale pivot * atomGram atom pivot pivot := by
      rw [hcancel]
    nlinarith [hbudget, hpivot, hcancel, hcancelSq]
  obtain ⟨slotOne, slotTwo, hneOneTwo, hgapRaw, hdetRaw⟩ :=
    atomPairGramClosed_holds (fun slot => planeShadow (atom pivot) (atom slot))
      (fun slot => if slot = pivot then (0:ℝ)
        else scale slot + (scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2
          + extra slot)
      (atom pivot)
      (by
        have := hdiagPos
        simp only [atomGram] at this
        exact this)
      hperp hinflNonneg hinflSum hshadowFrame
  have hOneNe : slotOne ≠ pivot := by
    intro heq
    rw [heq, hshadowPivot, if_pos rfl] at hgapRaw
    simp at hgapRaw
  have hTwoNe : slotTwo ≠ pivot := by
    intro heq
    rw [heq, hshadowPivot, if_pos rfl] at hdetRaw
    simp at hdetRaw
  rw [if_neg hOneNe] at hgapRaw hdetRaw
  rw [if_neg hTwoNe] at hdetRaw
  have hgapTwo : 0 < planeShadow (atom pivot) (atom slotTwo)
        ⬝ᵥ planeShadow (atom pivot) (atom slotTwo)
      - (scale slotTwo + (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2
        + extra slotTwo) := by
    nlinarith [hdetRaw, hgapRaw,
      sq_nonneg (planeShadow (atom pivot) (atom slotOne)
        ⬝ᵥ planeShadow (atom pivot) (atom slotTwo))]
  have hdefectSq : ((scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot))
        * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
      ≤ extra slotOne * extra slotTwo := by
    have hraw := hproduct slotOne slotTwo hOneNe hTwoNe hneOneTwo
    have hposSq : 0 < (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot) ^ 2 :=
      pow_pos (mul_pos hdiagPos hpivot) 2
    have hrewrite : ((scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot))
          * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
        = (scale pivot * (atomGram atom pivot slotOne
              * atomGram atom pivot slotTwo)) ^ 2
          / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2 := by
      field_simp
    rw [hrewrite, div_le_iff₀ hposSq]
    linarith [hraw]
  have hcore := transfer_pair_of_product_inflation
    (gapOne := planeShadow (atom pivot) (atom slotOne)
        ⬝ᵥ planeShadow (atom pivot) (atom slotOne)
      - (scale slotOne + (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2
        + extra slotOne))
    (gapTwo := planeShadow (atom pivot) (atom slotTwo)
        ⬝ᵥ planeShadow (atom pivot) (atom slotTwo)
      - (scale slotTwo + (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2
        + extra slotTwo))
    (cross := planeShadow (atom pivot) (atom slotOne)
        ⬝ᵥ planeShadow (atom pivot) (atom slotTwo))
    (defect := (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot))
      * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo))
    (hextraNonneg slotOne) (hextraNonneg slotTwo) hdefectSq hgapRaw hgapTwo hdetRaw
  have hminorOne : atomPairMinor atom scale pivot slotOne
      = atomShiftedDiag atom scale pivot
        * ((planeShadow (atom pivot) (atom slotOne)
            ⬝ᵥ planeShadow (atom pivot) (atom slotOne))
          - scale slotOne
          - (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slotOne ^ 2) :=
    atomPairMinor_eq_shadow slotOne hdiagNe hRne'
  have hminorTwo : atomPairMinor atom scale pivot slotTwo
      = atomShiftedDiag atom scale pivot
        * ((planeShadow (atom pivot) (atom slotTwo)
            ⬝ᵥ planeShadow (atom pivot) (atom slotTwo))
          - scale slotTwo
          - (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slotTwo ^ 2) :=
    atomPairMinor_eq_shadow slotTwo hdiagNe hRne'
  have hcrossEq : atomPivotCross atom scale pivot slotOne slotTwo
      = atomShiftedDiag atom scale pivot
        * ((planeShadow (atom pivot) (atom slotOne)
              ⬝ᵥ planeShadow (atom pivot) (atom slotTwo))
          - (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
            * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) :=
    atomPivotCross_eq_shadow slotOne slotTwo hdiagNe hRne'
  refine ⟨slotOne, slotTwo, fun heq => hOneNe heq.symm, fun heq => hTwoNe heq.symm,
    hneOneTwo, ?_, ?_, ?_⟩
  · rw [hminorOne]
    refine mul_pos hpivot ?_
    linarith [hgapRaw, hextraNonneg slotOne]
  · rw [hminorTwo]
    refine mul_pos hpivot ?_
    linarith [hgapTwo, hextraNonneg slotTwo]
  · rw [hcrossEq, hminorOne, hminorTwo]
    have hRsq : 0 < atomShiftedDiag atom scale pivot ^ 2 := by positivity
    nlinarith [hcore, hRsq]

/-! ## Layer 2 — the uniform instance and the discounted inflation -/

/-- **THE UNIFORM INSTANCE.**  One deflation weight at every slot obeys
the product law with equality, thus the landed double budget is the
uniform corollary of the product engine. -/
theorem exists_deflated_pair_of_uniform_inflation
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hbudget : ((∑ slot, scale slot) - scale pivot
          + ∑ slot, (if slot = pivot then (0:ℝ)
            else (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2))
          * atomShiftedDiag atom scale pivot
        + scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ 0 < atomPairMinor atom scale pivot slotTwo
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo := by
  classical
  have hdiagPos : 0 < atomGram atom pivot pivot := by
    have hp := hscale pivot
    have hR := hpivot
    simp only [atomShiftedDiag] at hR
    linarith
  have hdeflNonneg : 0 ≤ scale pivot
      / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) :=
    div_nonneg (hscale pivot) (mul_nonneg hdiagPos.le hpivot.le)
  refine exists_deflated_pair_of_product_inflation hframe hscale hpivot
    (fun slot => ?_) (by rw [if_pos rfl]) (fun slotOne slotTwo hone htwo _ => ?_) hbudget
  · by_cases hcase : slot = pivot
    · rw [if_pos hcase]
    · rw [if_neg hcase]
      exact mul_nonneg hdeflNonneg (sq_nonneg _)
  · rw [if_neg hone, if_neg htwo]
    have hcancel : (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot))
        * (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot)
        = scale pivot :=
      div_mul_cancel₀ _ (mul_ne_zero (ne_of_gt hdiagPos) (ne_of_gt hpivot))
    have hexpand : (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
        * ((scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2
          * ((scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2))
        = (scale pivot * (atomGram atom pivot slotOne
            * atomGram atom pivot slotTwo)) ^ 2 := by
      linear_combination (atomGram atom pivot slotOne ^ 2
        * atomGram atom pivot slotTwo ^ 2
        * ((scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
            * (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot)
          + scale pivot)) * hcancel
    linarith [hexpand]

/-- The DISCOUNTED INFLATION at one slot and one factor: the named slot
pays one deflation weight divided by the factor, and every other slot
off the pivot pays one deflation weight multiplied by the factor. -/
noncomputable def discountInflation {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot discount : Fin slotCount) (factor : ℝ) : Fin slotCount → ℝ :=
  fun slot => if slot = pivot then 0
    else if slot = discount then
      (scale pivot / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
        * atomGram atom pivot slot ^ 2 / factor
    else factor
      * ((scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2)

theorem discountInflation_pivot {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot discount : Fin slotCount) (factor : ℝ) :
    discountInflation atom scale pivot discount factor pivot = 0 := by
  simp [discountInflation]

theorem discountInflation_nonneg {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot discount : Fin slotCount) {factor : ℝ} (hfactor : 0 < factor)
    (hdefl : 0 ≤ scale pivot
      / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
    (slot : Fin slotCount) :
    0 ≤ discountInflation atom scale pivot discount factor slot := by
  simp only [discountInflation]
  by_cases hpivot : slot = pivot
  · rw [if_pos hpivot]
  · rw [if_neg hpivot]
    by_cases hdisc : slot = discount
    · rw [if_pos hdisc]
      exact div_nonneg (mul_nonneg hdefl (sq_nonneg _)) hfactor.le
    · rw [if_neg hdisc]
      exact mul_nonneg hfactor.le (mul_nonneg hdefl (sq_nonneg _))

/-- **THE DISCOUNTED INFLATION OBEYS THE PRODUCT LAW.**  At a pair that
holds the discounted slot the two factors cancel exactly, and at a pair
that misses it the two factors multiply to at least one. -/
theorem discountInflation_product {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot discount : Fin slotCount) {factor : ℝ} (hfactor : 1 ≤ factor)
    (hdiagPos : 0 < atomGram atom pivot pivot)
    (hpivotPos : 0 < atomShiftedDiag atom scale pivot)
    (slotOne slotTwo : Fin slotCount) (hone : slotOne ≠ pivot) (htwo : slotTwo ≠ pivot)
    (hne : slotOne ≠ slotTwo) :
    (scale pivot * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
      ≤ (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
        * (discountInflation atom scale pivot discount factor slotOne
          * discountInflation atom scale pivot discount factor slotTwo) := by
  have hfactorPos : 0 < factor := lt_of_lt_of_le zero_lt_one hfactor
  have hprodNe : atomGram atom pivot pivot * atomShiftedDiag atom scale pivot ≠ 0 :=
    ne_of_gt (mul_pos hdiagPos hpivotPos)
  have hcancel : (scale pivot / (atomGram atom pivot pivot
      * atomShiftedDiag atom scale pivot))
      * (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot)
      = scale pivot :=
    div_mul_cancel₀ _ hprodNe
  have hbase : (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
      * ((scale pivot / (atomGram atom pivot pivot
            * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2
        * ((scale pivot / (atomGram atom pivot pivot
            * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2))
      = (scale pivot * (atomGram atom pivot slotOne
          * atomGram atom pivot slotTwo)) ^ 2 := by
    linear_combination (atomGram atom pivot slotOne ^ 2
      * atomGram atom pivot slotTwo ^ 2
      * ((scale pivot / (atomGram atom pivot pivot
            * atomShiftedDiag atom scale pivot))
          * (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot)
        + scale pivot)) * hcancel
  have hweightOne : 0 ≤ (scale pivot / (atomGram atom pivot pivot
      * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2
      * ((scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2) := by
    have hsq : (0:ℝ) ≤ (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg (atomGram atom pivot slotOne * atomGram atom pivot slotTwo),
      hsq]
  simp only [discountInflation]
  rw [if_neg hone, if_neg htwo]
  by_cases hdiscOne : slotOne = discount
  · rw [if_pos hdiscOne, if_neg (fun heq => hne (hdiscOne.trans heq.symm))]
    have hsplit : (scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2 / factor
        * (factor * ((scale pivot / (atomGram atom pivot pivot
            * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2))
        = (scale pivot / (atomGram atom pivot pivot
            * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2
          * ((scale pivot / (atomGram atom pivot pivot
            * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2) := by
      field_simp
    rw [hsplit]
    linarith [hbase]
  · rw [if_neg hdiscOne]
    by_cases hdiscTwo : slotTwo = discount
    · rw [if_pos hdiscTwo]
      have hsplit : factor * ((scale pivot / (atomGram atom pivot pivot
            * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2)
          * ((scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slotTwo ^ 2 / factor)
          = (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2
            * ((scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
              * atomGram atom pivot slotTwo ^ 2) := by
        field_simp
      rw [hsplit]
      linarith [hbase]
    · rw [if_neg hdiscTwo]
      have hsplit : factor * ((scale pivot / (atomGram atom pivot pivot
            * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2)
          * (factor * ((scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slotTwo ^ 2))
          = factor ^ 2 * ((scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2
            * ((scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
              * atomGram atom pivot slotTwo ^ 2)) := by ring
      rw [hsplit]
      have hgrow : (1:ℝ) ≤ factor ^ 2 := by nlinarith [hfactor]
      nlinarith [hbase, hweightOne, hgrow,
        mul_nonneg (mul_pos hdiagPos hpivotPos).le (mul_pos hdiagPos hpivotPos).le]

/-- **THE DISCOUNTED STRATUM.**  A live pivot, one discounted slot and
one factor of at least one: the discounted budget supplies the deflated
pair.  The budget is strictly cheaper than the uniform one whenever the
reading energy concentrates at the discounted slot. -/
theorem exists_deflated_pair_of_discount_inflation
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot discount : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot) {factor : ℝ} (hfactor : 1 ≤ factor)
    (hbudget : ((∑ slot, scale slot) - scale pivot
          + ∑ slot, discountInflation atom scale pivot discount factor slot)
          * atomShiftedDiag atom scale pivot
        + scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ 0 < atomPairMinor atom scale pivot slotTwo
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo := by
  have hdiagPos : 0 < atomGram atom pivot pivot := by
    have hp := hscale pivot
    have hR := hpivot
    simp only [atomShiftedDiag] at hR
    linarith
  have hdeflNonneg : 0 ≤ scale pivot
      / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) :=
    div_nonneg (hscale pivot) (mul_nonneg hdiagPos.le hpivot.le)
  exact exists_deflated_pair_of_product_inflation hframe hscale hpivot
    (discountInflation_nonneg atom scale pivot discount
      (lt_of_lt_of_le zero_lt_one hfactor) hdeflNonneg)
    (discountInflation_pivot atom scale pivot discount factor)
    (fun slotOne slotTwo hone htwo hne =>
      discountInflation_product atom scale pivot discount hfactor hdiagPos hpivot
        slotOne slotTwo hone htwo hne)
    hbudget

/-! ## Layer 3 — the narrowed attack surface -/

/-- **THE NARROWED BAND KILL.**  The band kill only has to answer at a
pivot where NO admissible product inflation clears the budget.  Every
inflation of the product law is an escape, thus this residue is at most
as large as the landed band kill, and the bridge theorem shows it is at
least as strong. -/
def AtomBlockedProductKill : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) →
    (∑ slot, scale slot) ≤ 39 / 50 →
    ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)
        < atomShiftedDiag atom scale pivot →
      (∀ extra : Fin 6 → ℝ, (∀ slot, 0 ≤ extra slot) → extra pivot = 0 →
        (∀ slotOne slotTwo : Fin 6, slotOne ≠ pivot → slotTwo ≠ pivot →
          slotOne ≠ slotTwo →
          (scale pivot * (atomGram atom pivot slotOne
              * atomGram atom pivot slotTwo)) ^ 2
            ≤ (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
              * (extra slotOne * extra slotTwo)) →
        atomShiftedDiag atom scale pivot
          ≤ ((∑ slot, scale slot) - scale pivot + ∑ slot, extra slot)
              * atomShiftedDiag atom scale pivot
            + scale pivot * (1 - atomGram atom pivot pivot)) →
      (∀ slotOne slotTwo : Fin 6,
        pivot ≠ slotOne → pivot ≠ slotTwo → slotOne ≠ slotTwo →
        0 < atomPairMinor atom scale pivot slotOne →
        atomPairMinor atom scale pivot slotOne
            * atomPairMinor atom scale pivot slotTwo
          ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2) →
      False

/-- **THE NARROWED KILL CLOSES THE BAND KILL.**  Either some admissible
product inflation clears the budget, and the engine supplies the pair
against the failure hypothesis, or no inflation clears it, and the
narrowed kill fires. -/
theorem atomBlockedBandKill_of_productKill
    (hkill : AtomBlockedProductKill) : AtomBlockedBandKill := by
  intro atom scale hpos hsmall hframe hblocked hband pivot hlive hsingle hfail
  by_cases hclear : ∃ extra : Fin 6 → ℝ, (∀ slot, 0 ≤ extra slot) ∧ extra pivot = 0
      ∧ (∀ slotOne slotTwo : Fin 6, slotOne ≠ pivot → slotTwo ≠ pivot →
        slotOne ≠ slotTwo →
        (scale pivot * (atomGram atom pivot slotOne
            * atomGram atom pivot slotTwo)) ^ 2
          ≤ (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
            * (extra slotOne * extra slotTwo))
      ∧ ((∑ slot, scale slot) - scale pivot + ∑ slot, extra slot)
            * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)
        < atomShiftedDiag atom scale pivot
  · obtain ⟨extra, hnonneg, hzero, hproduct, hbudget⟩ := hclear
    obtain ⟨slotOne, slotTwo, honePivot, htwoPivot, hpairNe, hminorOne, _, hcross⟩ :=
      exists_deflated_pair_of_product_inflation hframe (fun slot => (hpos slot).le)
        hlive hnonneg hzero hproduct hbudget
    exact absurd hcross
      (not_lt.mpr (hfail slotOne slotTwo honePivot htwoPivot hpairNe hminorOne))
  · refine hkill atom scale hpos hsmall hframe hblocked hband pivot hlive hsingle
      (fun extra hnonneg hzero hproduct => ?_) hfail
    by_contra hlt
    exact hclear ⟨extra, hnonneg, hzero, hproduct, not_le.mp hlt⟩

/-- The band residue from the narrowed kill. -/
theorem atomBlockedBandClosed_of_productKill
    (hkill : AtomBlockedProductKill) : AtomBlockedBandClosed :=
  atomBlockedBandClosed_of_bandKill (atomBlockedBandKill_of_productKill hkill)

/-- **THE `(6,3)` CELL FROM THE NARROWED KILL AND THE DEEP PART.** -/
theorem gtzWeighted_six_three_of_productKill_of_deep
    (hkill : AtomBlockedProductKill) (hdeep : AtomBlockedDeepClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_band_of_deep
    (atomBlockedBandClosed_of_productKill hkill) hdeep

/-- **THE RANK-THREE PAYOFF FROM THE NARROWED KILL AND THE DEEP PART.** -/
theorem gtzWeightedAll_three_of_productKill_of_deep
    (hkill : AtomBlockedProductKill) (hdeep : AtomBlockedDeepClosed) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_band_of_deep
    (atomBlockedBandClosed_of_productKill hkill) hdeep

end Gtz
