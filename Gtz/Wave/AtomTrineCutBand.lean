import Gtz.Wave.AtomProductInflation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The two trine cuts: the sharp blocked threshold and the sharp window

The blocked residue carries one known obstruction over the complex field:
the scaled two-trine.  That datum normalizes to the diagonal one half at
every slot, and at uniform scales each of its two budget inequalities
collapses to one quadratic in the scale mass.  This module makes the two
quadratics first class objects, PROVES that they are the exact thresholds
of the blocked stratum and of the single-budget window, and re-splits the
blocked residue along them.

The two quadratics are `5 m ^ 2 - 27 m + 18`, the TRINE CUT, and
`5 m ^ 2 - 24 m + 18`, the SINGLE CUT.  Their relevant roots are
`(27 - 3 * sqrt 41) / 10`, about `0.7790627`, and `(12 - 3 * sqrt 6) / 5`,
about `0.9303062`.

## The two sharp thresholds

A blocked datum obeys the trine cut, thus its scale mass is at least
`0.7790627`.  A datum whose every live slot fails the single inflation
budget obeys the single cut, thus its scale mass is at least `0.9303062`.
Both bounds are attained by the scaled two-trine, thus both are sharp.

These laws SUPERSEDE the landed thresholds.  The landed blocked window is
`13/20`, which is `0.65`, and the landed single window is `39/50`, which
is `0.78`.  The blocked stratum is therefore far smaller than the landed
split says, and the single-budget engine reaches far further.

The proof of each is three lines of algebra and one summation.  The
budget inequality at a live slot is EXACTLY a bound of the shape
`diagonal * (1 - mass + k * scale) <= scale * (k - mass + scale)`, with
`k` equal to three for the blocked budget and two for the single budget.
A dead slot obeys the same bound because its diagonal is at most its
scale.  That bound is a concave rational law of the scale, its tangent at
the uniform scale is a linear bound that is exact at the uniform point,
and the six tangents add to the cut.  The tangent step is one square.

## What the thresholds buy

The free side of the trine cut is EMPTY: nothing is blocked below the
trine onset, thus `Gtz.AtomBlockedCutClosed` is a theorem with no
hypothesis.  The blocked residue therefore splits into two parts only:
the WINDOW between the two cuts, where the single-budget engine applies,
and the DEEP stratum above the single onset, where it does not.  The
landed band residue and the landed deep residue both follow.

## The live budget

The second half of the module answers the question that the window
raises: how cheap can the extra inflation of the transfer be made?  The
landed engine inflates every slot off the pivot.  The engine here
inflates only the LIVE slots, which are the slots that the plane closure
can return at all, and it lets one live slot pay less by a factor while
the others pay more by the same factor.  The budget of the live inflation
is one division-free inequality in the reading row of the pivot, and a
closed criterion of two polynomial inequalities decides the whole search
over the factor.

## The measured setting (probes, banked, not consumed)

The adversarial search minimizes the scale mass over complex Parseval
data that are blocked at every live pivot.  The minimum is `0.7790638`,
which is the trine onset to six decimal places, and the minimizer is the
trine itself.  Over the real field the same search bottoms out at
`0.7814`.  With the extra demand that no deflated pair exists the complex
minimum is `0.7791406`, and with the scale mass capped at `779 / 1000`
the search finds NOTHING in four thousand eight hundred starts across two
seeds.  Over the real field it finds no blocked pair-free datum at any
scale mass below `0.999`.

A strict kill margin of `0.001` pushes the complex onset to `0.9044`,
thus the complex obstruction near the trine onset is razor thin and the
realness content that the window needs grows with the scale mass.

## The realness note, corrected

The window and the deep stratum both contain the scaled two-trine, thus
both are FALSE over the complex field and both need a real-only step.
The correct rule for that step, measured at complex ties: a SINGLE square
law is gauge repairable and carries no realness, while the SYSTEM of the
pairing square and the bracket square is not repairable.  The untwisted
cross moment and the pairing transport are gauge repairable, thus they
carry no realness at all.  The test that settles any candidate law is two
hundred random unit phase gauges: a residual that stays at `1e-15` can
carry realness, a residual that moves by order one cannot.  The deflated
pair criterion of this lane is gauge invariant at `1.6e-17`, thus it is
of the right type.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.trineCut`, `Gtz.trineCut_factor_split`, `Gtz.trineCut_factor_band`,
  `Gtz.trineCut_pos_of_le_split`, `Gtz.trineCut_onset`,
  `Gtz.scale_lt_band_of_trineCut_pos`, `Gtz.singleCut`,
  `Gtz.singleCut_onset`, `Gtz.singleCut_pos_of_le_band` — **THE TWO
  CUTS**, their rational factorizations and their algebraic roots.
* `Gtz.blocked_slot_tangent`, `Gtz.trineCut_nonpos_of_six_tangents`,
  `Gtz.blocked_trineCut_nonpos` — **THE SHARP BLOCKED THRESHOLD.**
* `Gtz.single_slot_tangent`, `Gtz.singleCut_nonpos_of_six_tangents`,
  `Gtz.singleFail_singleCut_nonpos`,
  `Gtz.exists_pivot_single_budget_of_singleCut_pos` — **THE SHARP
  SINGLE-BUDGET WINDOW.**
* `Gtz.thirteen_twentieths_lt_of_blocked`,
  `Gtz.trineCut_pos_of_le_thirteen_twentieths` — the supersession of the
  landed `13/20` threshold.
* `Gtz.exists_deflated_pair_of_trineCut_pos`,
  `Gtz.exists_dominating_triple_of_trineCut_pos` — **THE UNBLOCKED
  DISPATCH**, which supersedes the landed `13/20` dispatch.
* `Gtz.exists_deflated_pair_of_live_product_inflation` — **THE LIVE
  PRODUCT ENGINE**: the product law of the extra inflation is only
  needed at pairs of slots that the plane closure can return.
* `Gtz.liveSlots`, `Gtz.liveReadingEnergy`,
  `Gtz.liveReadingEnergy_le_row` — **THE LIVE READING ROW.**
* `Gtz.liveInflation`, `Gtz.liveInflation_product`,
  `Gtz.liveInflation_sum` — **THE LIVE DISCOUNT INFLATION** and its
  closed budget.
* `Gtz.exists_deflated_pair_of_live_inflation`,
  `Gtz.exists_deflated_pair_of_live_budget`,
  `Gtz.discount_room_lt`,
  `Gtz.exists_deflated_pair_of_discount_criterion` — **THE LIVE BUDGET
  ENGINES** and the closed discount criterion.
* `Gtz.AtomBlockedCutClosed`, `Gtz.atomBlockedCutClosed_holds` — **THE
  FREE SIDE IS A THEOREM.**
* `Gtz.AtomBlockedWindowClosed`, `Gtz.AtomBlockedDeepCutClosed`,
  `Gtz.atomBlockedPairClosed_iff_window_and_deepCut` — **THE SHARP
  LOSSLESS SPLIT** of the blocked residue into two parts.
* `Gtz.atomBlockedBandClosed_of_windowClosed`,
  `Gtz.atomBlockedDeepCutClosed_of_deepClosed`,
  `Gtz.not_blocked_of_le_split` — the bridges to the landed split and
  the rational re-cut at `779 / 1000`.
* `Gtz.AtomBlockedWindowKill`, `Gtz.AtomBlockedDeepCutKill`,
  `Gtz.atomBlockedWindowClosed_iff_windowKill`,
  `Gtz.atomBlockedDeepCutClosed_iff_deepCutKill` — **THE GLOBAL KILLS**:
  the exact contrapositive of each part, which hands the prover the
  failure of every pair at EVERY live pivot, not only at one.
* `Gtz.AtomBlockedWindowLiveKill`, `Gtz.AtomBlockedDeepCutLiveKill` and
  their bridges — **THE NARROWED ATTACK SURFACE**: each kill only has to
  answer where no live discount inflation clears the budget.
* `Gtz.gtzWeighted_six_three_of_window_of_deepCut`,
  `Gtz.gtzWeightedAll_three_of_window_of_deepCut`,
  `Gtz.isEmpty_sixThreeCrux_of_window_of_deepCut` and the kill forms —
  the cell and the rank-three payoff from the two remaining parts.

## Vacuity

Every law of layers zero thru three is an unconditional statement about a
family of vectors, a family of scales, one pivot and one inflation.  The
free side of layer four is a theorem, and the two remaining residues are
vacuous under no hypothesis.  The bridge theorems prove that the two
parts together are equivalent to the landed blocked residue, and each
kill is equivalent to its part, thus nothing is given up at any step.
-/

namespace Gtz

/-! ## Layer 0 — the trine cut -/

/-- **THE TRINE CUT.**  The quadratic that the blocked inequality of the
scaled two-trine collapses to at uniform scales.  The trine normalizes to
the diagonal one half at every slot, thus its blocked inequality is
`(3 - m) * (6 - 5 m) <= 6 m` after the common denominator, which is this
quadratic with the sign reversed. -/
def trineCut (mass : ℝ) : ℝ := 5 * mass ^ 2 - 27 * mass + 18

/-- The cut factors against the rational split point `779 / 1000`. -/
theorem trineCut_factor_split (mass : ℝ) :
    trineCut mass - 241 / 200000
      = 5 * (779 / 1000 - mass) * (4621 / 1000 - mass) := by
  simp only [trineCut]; ring

/-- The cut factors against the landed band boundary `39 / 50`. -/
theorem trineCut_factor_band (mass : ℝ) :
    trineCut mass + 9 / 500 = 5 * (39 / 50 - mass) * (231 / 50 - mass) := by
  simp only [trineCut]; ring

/-- **THE RATIONAL CERTIFICATE.**  Below the rational split point the cut
is positive by at least `241 / 200000`. -/
theorem trineCut_pos_of_le_split {mass : ℝ} (hmass : mass ≤ 779 / 1000) :
    241 / 200000 ≤ trineCut mass := by
  have hfac := trineCut_factor_split mass
  have hone : (0:ℝ) ≤ 779 / 1000 - mass := by linarith
  have htwo : (0:ℝ) ≤ 4621 / 1000 - mass := by linarith
  nlinarith [hfac, mul_nonneg hone htwo]

/-- **THE ALGEBRAIC ROOT.**  The cut vanishes exactly at the trine onset
`(27 - 3 * sqrt 41) / 10`, which is about `0.7790627`. -/
theorem trineCut_onset : trineCut ((27 - 3 * Real.sqrt 41) / 10) = 0 := by
  have hsq : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  simp only [trineCut]
  linear_combination (9 / 20 : ℝ) * hsq

/-- **THE CUT SITS INSIDE THE BAND.**  A positive cut at a scale mass of
the unit interval forces that mass below the landed band boundary, thus
the single-budget window theorem applies on the whole free side. -/
theorem scale_lt_band_of_trineCut_pos {mass : ℝ} (hupper : mass < 1)
    (hcut : 0 < trineCut mass) : mass < 39 / 50 := by
  by_contra hno
  have hband : 39 / 50 ≤ mass := not_lt.mp hno
  have hfac := trineCut_factor_band mass
  have hone : (0:ℝ) ≤ mass - 39 / 50 := by linarith
  have htwo : (0:ℝ) < 231 / 50 - mass := by linarith
  nlinarith [hfac, mul_nonneg hone htwo.le]

/-- The cut is negative at the landed band boundary, thus the boundary
lies strictly inside the trine stratum. -/
theorem trineCut_band_boundary : trineCut (39 / 50) = -(9 / 500) := by
  simp only [trineCut]; norm_num

/-! ## Layer 0b — the sharp blocked threshold -/

/-- **THE TANGENT LAW OF ONE BLOCKED SLOT.**  The per-slot bound of a
blocked slot reads as a concave rational law of the scale, thus its
tangent at the uniform scale is a linear bound with no loss at the uniform
point.  The tangent inequality is one square, and the whole step is
division free.

The names of the pieces are `U = 1 - mass + 3 * scale`, the shifted
scale; `V = 2 - mass`, twice the uniform tangent point; `W = 3 * scale +
8 - 2 * mass - 9 * diagonal`, nine times the gap of the splitting; and
`Kn = 2 (1 - mass) (4 - mass)`, nine times the curvature weight. -/
theorem blocked_slot_tangent {mass slotScale slotDiag : ℝ}
    (hsmall : mass < 1) (hscale : 0 ≤ slotScale)
    (hslot : slotDiag * (1 - mass + 3 * slotScale)
      ≤ slotScale * (3 - mass + slotScale)) :
    4 * (2 * (1 - mass) * (4 - mass)) * (1 - 3 * slotScale)
      ≤ (2 - mass) ^ 2 * (3 * slotScale + 8 - 2 * mass - 9 * slotDiag) := by
  have hU : 0 < 1 - mass + 3 * slotScale := by linarith
  have hKn : 0 < 2 * (1 - mass) * (4 - mass) :=
    mul_pos (by linarith : (0:ℝ) < 2 * (1 - mass)) (by linarith : (0:ℝ) < 4 - mass)
  have hUW : 2 * (1 - mass) * (4 - mass)
      ≤ (1 - mass + 3 * slotScale)
        * (3 * slotScale + 8 - 2 * mass - 9 * slotDiag) := by
    have hid : (1 - mass + 3 * slotScale)
          * (3 * slotScale + 8 - 2 * mass - 9 * slotDiag)
        - 2 * (1 - mass) * (4 - mass)
        = 9 * (slotScale * (3 - mass + slotScale)
            - slotDiag * (1 - mass + 3 * slotScale)) := by ring
    linarith [hid, hslot]
  have hW : 0 ≤ 3 * slotScale + 8 - 2 * mass - 9 * slotDiag := by
    by_contra hno
    push Not at hno
    nlinarith [hUW, hKn, hU, hno]
  have hsq : 4 * (1 - mass + 3 * slotScale)
        * ((2 - mass) - (1 - mass + 3 * slotScale))
      ≤ (2 - mass) ^ 2 := by
    nlinarith [sq_nonneg ((2 - mass) - 2 * (1 - mass + 3 * slotScale))]
  rcases le_or_gt ((2 - mass) - (1 - mass + 3 * slotScale)) 0 with hle | hgt
  · nlinarith [hKn, hle, hW, sq_nonneg (2 - mass),
      mul_nonneg (sq_nonneg (2 - mass)) hW]
  · nlinarith [mul_le_mul_of_nonneg_right hsq hW,
      mul_le_mul_of_nonneg_left hUW (le_of_lt hgt)]

/-- **THE SIX TANGENTS CLEAR TO THE CUT.**  Six tangent laws whose scales
add to the mass and whose diagonals add to the rank force the cut to be
nonpositive.  The uniform point is the tangent point, thus the step is
exact and the resulting threshold is sharp. -/
theorem trineCut_nonpos_of_six_tangents
    {mass scaleZero scaleOne scaleTwo scaleThree scaleFour scaleFive
      diagZero diagOne diagTwo diagThree diagFour diagFive : ℝ}
    (hsmall : mass < 1)
    (hmassSum : scaleZero + scaleOne + scaleTwo + scaleThree + scaleFour + scaleFive
      = mass)
    (htraceSum : diagZero + diagOne + diagTwo + diagThree + diagFour + diagFive = 3)
    (hzero : 4 * (2 * (1 - mass) * (4 - mass)) * (1 - 3 * scaleZero)
      ≤ (2 - mass) ^ 2 * (3 * scaleZero + 8 - 2 * mass - 9 * diagZero))
    (hone : 4 * (2 * (1 - mass) * (4 - mass)) * (1 - 3 * scaleOne)
      ≤ (2 - mass) ^ 2 * (3 * scaleOne + 8 - 2 * mass - 9 * diagOne))
    (htwo : 4 * (2 * (1 - mass) * (4 - mass)) * (1 - 3 * scaleTwo)
      ≤ (2 - mass) ^ 2 * (3 * scaleTwo + 8 - 2 * mass - 9 * diagTwo))
    (hthree : 4 * (2 * (1 - mass) * (4 - mass)) * (1 - 3 * scaleThree)
      ≤ (2 - mass) ^ 2 * (3 * scaleThree + 8 - 2 * mass - 9 * diagThree))
    (hfour : 4 * (2 * (1 - mass) * (4 - mass)) * (1 - 3 * scaleFour)
      ≤ (2 - mass) ^ 2 * (3 * scaleFour + 8 - 2 * mass - 9 * diagFour))
    (hfive : 4 * (2 * (1 - mass) * (4 - mass)) * (1 - 3 * scaleFive)
      ≤ (2 - mass) ^ 2 * (3 * scaleFive + 8 - 2 * mass - 9 * diagFive)) :
    trineCut mass ≤ 0 := by
  have hweight : (2 * (1 - mass) * (4 - mass))
      * (scaleZero + scaleOne + scaleTwo + scaleThree + scaleFour + scaleFive)
      = (2 * (1 - mass) * (4 - mass)) * mass := by rw [hmassSum]
  have htangentMass : (2 - mass) ^ 2
      * (scaleZero + scaleOne + scaleTwo + scaleThree + scaleFour + scaleFive)
      = (2 - mass) ^ 2 * mass := by rw [hmassSum]
  have htangentTrace : (2 - mass) ^ 2
      * (diagZero + diagOne + diagTwo + diagThree + diagFour + diagFive)
      = (2 - mass) ^ 2 * 3 := by rw [htraceSum]
  have hcombined : 8 * (1 - mass) * (4 - mass) * (6 - 3 * mass)
      ≤ (2 - mass) ^ 2 * (21 - 9 * mass) := by
    linarith [hzero, hone, htwo, hthree, hfour, hfive, hweight, htangentMass,
      htangentTrace]
  by_contra hno
  push Not at hno
  simp only [trineCut] at hno
  have hroom : (0:ℝ) < 2 - mass := by linarith
  have hid : (2 - mass) ^ 2 * (21 - 9 * mass)
      - 8 * (1 - mass) * (4 - mass) * (6 - 3 * mass)
      = -(3 * ((2 - mass) * (5 * mass ^ 2 - 27 * mass + 18))) := by ring
  linarith [hcombined, hid, mul_pos hroom hno]

/-- **THE SHARP BLOCKED THRESHOLD.**  A blocked datum obeys the trine
cut.  Thus every blocked scale mass is at least the trine onset
`(27 - 3 * sqrt 41) / 10`, and the complex two-trine attains that bound
with equality at every slot.

The chain is one line per slot and one summation.  The blocked inequality
at a live slot is EXACTLY the bound `diagonal * (1 - mass + 3 * scale) <=
scale * (3 - mass + scale)`, and a dead slot obeys the same bound because
its diagonal is at most its scale.  That bound is a concave rational law
of the scale, its tangent at the uniform scale is exact at the uniform
point, and the six tangents add to the cut.

This law SUPERSEDES the landed `13/20` threshold: the trine onset is
`0.7790627`, thus the blocked stratum is far smaller than the landed
window says. -/
theorem blocked_trineCut_nonpos
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hblocked : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) :
    trineCut (∑ slot, scale slot) ≤ 0 := by
  have hslotLe : ∀ p : Fin 6, scale p ≤ ∑ slot, scale slot := fun p =>
    Finset.single_le_sum (f := scale) (fun i _ => hscale i) (Finset.mem_univ p)
  have hslot : ∀ p : Fin 6,
      atomGram atom p p * (1 - (∑ slot, scale slot) + 3 * scale p)
        ≤ scale p * (3 - (∑ slot, scale slot) + scale p) := by
    intro p
    rcases le_or_gt (atomShiftedDiag atom scale p) 0 with hdead | hlive
    · have hdiagLe : atomGram atom p p ≤ scale p := by
        simp only [atomShiftedDiag] at hdead
        linarith
      have hU : 0 < 1 - (∑ slot, scale slot) + 3 * scale p := by
        linarith [hscale p]
      have hunit : scale p ≤ 1 := le_trans (hslotLe p) (le_of_lt hsmall)
      nlinarith [mul_le_mul_of_nonneg_right hdiagLe hU.le,
        mul_nonneg (hscale p) (by linarith : (0:ℝ) ≤ 1 - scale p)]
    · have hb := hblocked p hlive
      simp only [atomShiftedDiag] at hb
      have hid : scale p * (3 - (∑ slot, scale slot) + scale p)
            - atomGram atom p p * (1 - (∑ slot, scale slot) + 3 * scale p)
          = ((∑ slot, scale slot) - scale p) * (atomGram atom p p - scale p)
            + 2 * scale p * (1 - atomGram atom p p)
            - (atomGram atom p p - scale p) := by ring
      linarith [hb, hid]
  have htangent : ∀ p : Fin 6,
      4 * (2 * (1 - (∑ slot, scale slot)) * (4 - (∑ slot, scale slot)))
          * (1 - 3 * scale p)
        ≤ (2 - (∑ slot, scale slot)) ^ 2
          * (3 * scale p + 8 - 2 * (∑ slot, scale slot) - 9 * atomGram atom p p) :=
    fun p => blocked_slot_tangent hsmall (hscale p) (hslot p)
  have hmassSum : scale 0 + scale 1 + scale 2 + scale 3 + scale 4 + scale 5
      = ∑ slot, scale slot := by rw [Fin.sum_univ_six]
  have htraceSum : atomGram atom 0 0 + atomGram atom 1 1 + atomGram atom 2 2
      + atomGram atom 3 3 + atomGram atom 4 4 + atomGram atom 5 5 = 3 := by
    have htrace : (∑ slot, atomGram atom slot slot) = 3 := by
      simpa using atomGram_trace hframe
    rw [← htrace, Fin.sum_univ_six]
  exact trineCut_nonpos_of_six_tangents hsmall hmassSum htraceSum
    (htangent 0) (htangent 1) (htangent 2) (htangent 3) (htangent 4) (htangent 5)

/-- The cut is positive by `41/16` below the landed `13/20` threshold. -/
theorem trineCut_pos_of_le_thirteen_twentieths {mass : ℝ} (hmass : mass ≤ 13 / 20) :
    41 / 16 ≤ trineCut mass := by
  have hfac : trineCut mass - 41 / 16 = 5 * (13 / 20 - mass) * (19 / 4 - mass) := by
    simp only [trineCut]; ring
  have hone : (0:ℝ) ≤ 13 / 20 - mass := by linarith
  have htwo : (0:ℝ) ≤ 19 / 4 - mass := by linarith
  nlinarith [hfac, mul_nonneg hone htwo]

/-- **THE SHARP THRESHOLD SUPERSEDES THE LANDED WINDOW.**  A blocked
datum has scale mass above `13/20`, and in fact above the trine onset. -/
theorem thirteen_twentieths_lt_of_blocked
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hblocked : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) :
    13 / 20 < ∑ slot, scale slot := by
  by_contra hno
  have hle : (∑ slot, scale slot) ≤ 13 / 20 := not_lt.mp hno
  have hpos := trineCut_pos_of_le_thirteen_twentieths hle
  have hnonpos := blocked_trineCut_nonpos hframe hscale hsmall hblocked
  linarith

/-- **THE UNBLOCKED DISPATCH.**  At a positive cut no datum is blocked at
every live slot, thus some live pivot carries the double budget and the
landed transfer supplies the deflated pair with no hypothesis at all. -/
theorem exists_deflated_pair_of_trineCut_pos
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hcut : 0 < trineCut (∑ slot, scale slot)) :
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo := by
  by_cases hblocked : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)
  · exact absurd (blocked_trineCut_nonpos hframe hscale hsmall hblocked)
      (not_le.mpr hcut)
  · push Not at hblocked
    obtain ⟨pivot, hlive, hbudget⟩ := hblocked
    obtain ⟨slotOne, slotTwo, honePivot, htwoPivot, hpairNe, hminorOne, _, hcross⟩ :=
      exists_deflated_pair_of_pivot_budget hframe hscale hlive hbudget
    exact ⟨pivot, slotOne, slotTwo, honePivot, htwoPivot, hpairNe, hlive, hminorOne,
      hcross⟩

/-- **THE DOMINATING TRIPLE AT A POSITIVE CUT.**  This SUPERSEDES the
landed `13/20` dispatch: every scale family of positive cut carries a
dominating card-three carrier, and the trine onset `0.7790627` is far
above `13/20`. -/
theorem exists_dominating_triple_of_trineCut_pos
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hcut : 0 < trineCut (∑ slot, scale slot)) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
          (∑ slot, scale slot * probe slot ^ 2)
            < atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  by_cases hblocked : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)
  · exact absurd (blocked_trineCut_nonpos hframe hscale hsmall hblocked)
      (not_le.mpr hcut)
  · push Not at hblocked
    obtain ⟨pivot, hlive, hbudget⟩ := hblocked
    exact exists_dominating_carrier_of_pivot_budget hframe hscale hlive hbudget

/-! ## Layer 0c — the sharp single-budget window -/

/-- **THE SINGLE CUT.**  The quadratic that the SINGLE inflation budget
of the scaled two-trine collapses to at uniform scales.  It is positive
below the root `(12 - 3 * sqrt 6) / 5`, which is about `0.9303062`, and
that root is where the trine loses its single budget. -/
def singleCut (mass : ℝ) : ℝ := 5 * mass ^ 2 - 24 * mass + 18

/-- The single cut factors against the rational point `93 / 100`. -/
theorem singleCut_factor_split (mass : ℝ) :
    singleCut mass - 9 / 2000 = 5 * (93 / 100 - mass) * (387 / 100 - mass) := by
  simp only [singleCut]; ring

theorem singleCut_pos_of_le_split {mass : ℝ} (hmass : mass ≤ 93 / 100) :
    9 / 2000 ≤ singleCut mass := by
  have hfac := singleCut_factor_split mass
  have hone : (0:ℝ) ≤ 93 / 100 - mass := by linarith
  have htwo : (0:ℝ) ≤ 387 / 100 - mass := by linarith
  nlinarith [hfac, mul_nonneg hone htwo]

/-- **THE ALGEBRAIC ROOT OF THE SINGLE CUT.** -/
theorem singleCut_onset : singleCut ((12 - 3 * Real.sqrt 6) / 5) = 0 := by
  have hsq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  simp only [singleCut]
  linear_combination (9 / 5 : ℝ) * hsq

/-- The single cut is positive at the landed band boundary, thus the
landed window `39/50` is far inside the new one. -/
theorem singleCut_band_boundary : singleCut (39 / 50) = 1161 / 500 := by
  simp only [singleCut]; norm_num

/-- **A NONPOSITIVE TRINE CUT FORCES A POSITIVE SINGLE CUT ON THE BAND.**
The two roots are ordered, thus the working window of the single-budget
engine strictly contains the whole blocked band of the landed split. -/
theorem singleCut_pos_of_le_band {mass : ℝ} (hmass : mass ≤ 39 / 50) :
    0 < singleCut mass := by
  have hfac : singleCut mass - 1161 / 500 = 5 * (39 / 50 - mass) * (201 / 50 - mass) := by
    simp only [singleCut]; ring
  have hone : (0:ℝ) ≤ 39 / 50 - mass := by linarith
  have htwo : (0:ℝ) ≤ 201 / 50 - mass := by linarith
  nlinarith [hfac, mul_nonneg hone htwo]

/-- **THE TANGENT LAW OF ONE SLOT WITHOUT THE SINGLE BUDGET.**  The same
concave splitting as the blocked tangent, with the deflation coefficient
one instead of two.  The pieces are `U = 1 - mass + 2 * scale`,
`V = 3 - 2 * mass`, `W = 2 * scale + 3 - mass - 4 * diagonal` and
`Kn = (1 - mass) (3 - mass)`. -/
theorem single_slot_tangent {mass slotScale slotDiag : ℝ}
    (hsmall : mass < 1) (hscale : 0 ≤ slotScale)
    (hslot : slotDiag * (1 - mass + 2 * slotScale)
      ≤ slotScale * (2 - mass + slotScale)) :
    3 * ((1 - mass) * (3 - mass)) * (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * slotScale))
      ≤ (3 - 2 * mass) ^ 2 * (2 * slotScale + 3 - mass - 4 * slotDiag) := by
  have hU : 0 < 1 - mass + 2 * slotScale := by linarith
  have hKn : 0 < (1 - mass) * (3 - mass) :=
    mul_pos (by linarith : (0:ℝ) < 1 - mass) (by linarith : (0:ℝ) < 3 - mass)
  have hUW : (1 - mass) * (3 - mass)
      ≤ (1 - mass + 2 * slotScale) * (2 * slotScale + 3 - mass - 4 * slotDiag) := by
    have hid : (1 - mass + 2 * slotScale) * (2 * slotScale + 3 - mass - 4 * slotDiag)
        - (1 - mass) * (3 - mass)
        = 4 * (slotScale * (2 - mass + slotScale)
            - slotDiag * (1 - mass + 2 * slotScale)) := by ring
    linarith [hid, hslot]
  have hW : 0 ≤ 2 * slotScale + 3 - mass - 4 * slotDiag := by
    by_contra hno
    push Not at hno
    nlinarith [hUW, hKn, hU, hno]
  have hsq : 3 * (1 - mass + 2 * slotScale)
        * (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * slotScale))
      ≤ (3 - 2 * mass) ^ 2 := by
    nlinarith [sq_nonneg ((3 - 2 * mass) - 3 * (1 - mass + 2 * slotScale))]
  rcases le_or_gt (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * slotScale)) 0 with hle | hgt
  · nlinarith [hKn, hle, hW, sq_nonneg (3 - 2 * mass),
      mul_nonneg (sq_nonneg (3 - 2 * mass)) hW]
  · nlinarith [mul_le_mul_of_nonneg_right hsq hW,
      mul_le_mul_of_nonneg_left hUW (le_of_lt hgt)]

/-- **THE SIX SINGLE TANGENTS CLEAR TO THE SINGLE CUT.** -/
theorem singleCut_nonpos_of_six_tangents
    {mass scaleZero scaleOne scaleTwo scaleThree scaleFour scaleFive
      diagZero diagOne diagTwo diagThree diagFour diagFive : ℝ}
    (hsmall : mass < 1)
    (hmassSum : scaleZero + scaleOne + scaleTwo + scaleThree + scaleFour + scaleFive
      = mass)
    (htraceSum : diagZero + diagOne + diagTwo + diagThree + diagFour + diagFive = 3)
    (hzero : 3 * ((1 - mass) * (3 - mass))
        * (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * scaleZero))
      ≤ (3 - 2 * mass) ^ 2 * (2 * scaleZero + 3 - mass - 4 * diagZero))
    (hone : 3 * ((1 - mass) * (3 - mass))
        * (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * scaleOne))
      ≤ (3 - 2 * mass) ^ 2 * (2 * scaleOne + 3 - mass - 4 * diagOne))
    (htwo : 3 * ((1 - mass) * (3 - mass))
        * (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * scaleTwo))
      ≤ (3 - 2 * mass) ^ 2 * (2 * scaleTwo + 3 - mass - 4 * diagTwo))
    (hthree : 3 * ((1 - mass) * (3 - mass))
        * (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * scaleThree))
      ≤ (3 - 2 * mass) ^ 2 * (2 * scaleThree + 3 - mass - 4 * diagThree))
    (hfour : 3 * ((1 - mass) * (3 - mass))
        * (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * scaleFour))
      ≤ (3 - 2 * mass) ^ 2 * (2 * scaleFour + 3 - mass - 4 * diagFour))
    (hfive : 3 * ((1 - mass) * (3 - mass))
        * (2 * (3 - 2 * mass) - 3 * (1 - mass + 2 * scaleFive))
      ≤ (3 - 2 * mass) ^ 2 * (2 * scaleFive + 3 - mass - 4 * diagFive)) :
    singleCut mass ≤ 0 := by
  have hweight : ((1 - mass) * (3 - mass))
      * (scaleZero + scaleOne + scaleTwo + scaleThree + scaleFour + scaleFive)
      = ((1 - mass) * (3 - mass)) * mass := by rw [hmassSum]
  have htangentMass : (3 - 2 * mass) ^ 2
      * (scaleZero + scaleOne + scaleTwo + scaleThree + scaleFour + scaleFive)
      = (3 - 2 * mass) ^ 2 * mass := by rw [hmassSum]
  have htangentTrace : (3 - 2 * mass) ^ 2
      * (diagZero + diagOne + diagTwo + diagThree + diagFour + diagFive)
      = (3 - 2 * mass) ^ 2 * 3 := by rw [htraceSum]
  have hcombined : 18 * ((1 - mass) * (3 - mass)) * (3 - 2 * mass)
      ≤ (3 - 2 * mass) ^ 2 * (6 - 4 * mass) := by
    linarith [hzero, hone, htwo, hthree, hfour, hfive, hweight, htangentMass,
      htangentTrace]
  by_contra hno
  push Not at hno
  simp only [singleCut] at hno
  have hroom : (0:ℝ) < 3 - 2 * mass := by linarith
  have hid : (3 - 2 * mass) ^ 2 * (6 - 4 * mass)
      - 18 * ((1 - mass) * (3 - mass)) * (3 - 2 * mass)
      = -(2 * ((3 - 2 * mass) * (5 * mass ^ 2 - 24 * mass + 18))) := by ring
  linarith [hcombined, hid, mul_pos hroom hno]

/-- **THE SHARP SINGLE-BUDGET WINDOW.**  When every live slot fails the
single inflation budget, the scale mass obeys the single cut.  Thus the
doubly blocked stratum lives above `(12 - 3 * sqrt 6) / 5`, about
`0.9303062`, and the landed window boundary `39/50` is far below it.

This law SUPERSEDES `Gtz.singleBudget_scale_lt`. -/
theorem singleFail_singleCut_nonpos
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hfail : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)) :
    singleCut (∑ slot, scale slot) ≤ 0 := by
  have hslotLe : ∀ p : Fin 6, scale p ≤ ∑ slot, scale slot := fun p =>
    Finset.single_le_sum (f := scale) (fun i _ => hscale i) (Finset.mem_univ p)
  have hslot : ∀ p : Fin 6,
      atomGram atom p p * (1 - (∑ slot, scale slot) + 2 * scale p)
        ≤ scale p * (2 - (∑ slot, scale slot) + scale p) := by
    intro p
    rcases le_or_gt (atomShiftedDiag atom scale p) 0 with hdead | hlive
    · have hdiagLe : atomGram atom p p ≤ scale p := by
        simp only [atomShiftedDiag] at hdead
        linarith
      have hU : 0 < 1 - (∑ slot, scale slot) + 2 * scale p := by
        linarith [hscale p]
      have hunit : scale p ≤ 1 := le_trans (hslotLe p) (le_of_lt hsmall)
      nlinarith [mul_le_mul_of_nonneg_right hdiagLe hU.le,
        mul_nonneg (hscale p) (by linarith : (0:ℝ) ≤ 1 - scale p)]
    · have hb := hfail p hlive
      simp only [atomShiftedDiag] at hb
      have hid : scale p * (2 - (∑ slot, scale slot) + scale p)
            - atomGram atom p p * (1 - (∑ slot, scale slot) + 2 * scale p)
          = ((∑ slot, scale slot) - scale p) * (atomGram atom p p - scale p)
            + scale p * (1 - atomGram atom p p)
            - (atomGram atom p p - scale p) := by ring
      linarith [hb, hid]
  have htangent : ∀ p : Fin 6,
      3 * ((1 - (∑ slot, scale slot)) * (3 - (∑ slot, scale slot)))
          * (2 * (3 - 2 * (∑ slot, scale slot))
            - 3 * (1 - (∑ slot, scale slot) + 2 * scale p))
        ≤ (3 - 2 * (∑ slot, scale slot)) ^ 2
          * (2 * scale p + 3 - (∑ slot, scale slot) - 4 * atomGram atom p p) :=
    fun p => single_slot_tangent hsmall (hscale p) (hslot p)
  have hmassSum : scale 0 + scale 1 + scale 2 + scale 3 + scale 4 + scale 5
      = ∑ slot, scale slot := by rw [Fin.sum_univ_six]
  have htraceSum : atomGram atom 0 0 + atomGram atom 1 1 + atomGram atom 2 2
      + atomGram atom 3 3 + atomGram atom 4 4 + atomGram atom 5 5 = 3 := by
    have htrace : (∑ slot, atomGram atom slot slot) = 3 := by
      simpa using atomGram_trace hframe
    rw [← htrace, Fin.sum_univ_six]
  exact singleCut_nonpos_of_six_tangents hsmall hmassSum htraceSum
    (htangent 0) (htangent 1) (htangent 2) (htangent 3) (htangent 4) (htangent 5)

/-- **THE SHARP SINGLE-BUDGET PIVOT.**  At a positive single cut a live
pivot of single budget exists.  This SUPERSEDES the landed window
`exists_pivot_single_budget_of_scale_le`, whose bound is `39/50`. -/
theorem exists_pivot_single_budget_of_singleCut_pos
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hcut : 0 < singleCut (∑ slot, scale slot)) :
    ∃ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot
      ∧ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)
        < atomShiftedDiag atom scale pivot := by
  by_contra hno
  have hfail : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot) := by
    intro pivot hpos
    by_contra hlt
    exact hno ⟨pivot, hpos, not_le.mp hlt⟩
  exact absurd (singleFail_singleCut_nonpos hframe hscale hsmall hfail) (not_le.mpr hcut)

/-! ## Layer 1 — the live product inflation engine -/

/-- **THE LIVE PRODUCT ENGINE.**  The product law of the extra inflation
is only needed at pairs of slots whose pivot minor is already positive.
The plane closure cannot return a slot of nonpositive pivot minor, because
the extra inflation only lowers the gap that the closure reports, thus the
hypothesis at the other pairs is dead weight.

This engine is strictly stronger than the landed product engine: its
product hypothesis is the landed one restricted to the live pairs. -/
theorem exists_deflated_pair_of_live_product_inflation
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale extra : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hextraNonneg : ∀ slot, 0 ≤ extra slot)
    (hextraPivot : extra pivot = 0)
    (hproduct : ∀ slotOne slotTwo : Fin 6, slotOne ≠ pivot → slotTwo ≠ pivot →
      slotOne ≠ slotTwo →
      0 < atomPairMinor atom scale pivot slotOne →
      0 < atomPairMinor atom scale pivot slotTwo →
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
  have hminorOnePos : 0 < atomPairMinor atom scale pivot slotOne := by
    rw [hminorOne]
    refine mul_pos hpivot ?_
    linarith [hgapRaw, hextraNonneg slotOne]
  have hminorTwoPos : 0 < atomPairMinor atom scale pivot slotTwo := by
    rw [hminorTwo]
    refine mul_pos hpivot ?_
    linarith [hgapTwo, hextraNonneg slotTwo]
  have hdefectSq : ((scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot))
        * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
      ≤ extra slotOne * extra slotTwo := by
    have hraw := hproduct slotOne slotTwo hOneNe hTwoNe hneOneTwo hminorOnePos hminorTwoPos
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
  have hcrossEq : atomPivotCross atom scale pivot slotOne slotTwo
      = atomShiftedDiag atom scale pivot
        * ((planeShadow (atom pivot) (atom slotOne)
              ⬝ᵥ planeShadow (atom pivot) (atom slotTwo))
          - (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
            * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) :=
    atomPivotCross_eq_shadow slotOne slotTwo hdiagNe hRne'
  refine ⟨slotOne, slotTwo, fun heq => hOneNe heq.symm, fun heq => hTwoNe heq.symm,
    hneOneTwo, hminorOnePos, hminorTwoPos, ?_⟩
  rw [hcrossEq, hminorOne, hminorTwo]
  have hRsq : 0 < atomShiftedDiag atom scale pivot ^ 2 := by positivity
  nlinarith [hcore, hRsq]

/-! ## Layer 2 — the live reading row and the live discount inflation -/

/-- The LIVE SLOTS of a pivot: the slots off the pivot whose pivot minor
is already positive.  The plane closure can only ever return such a slot,
because the extra inflation lowers the gap that the closure reports. -/
noncomputable def liveSlots {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount) : Finset (Fin slotCount) :=
  Finset.univ.filter
    (fun slot => slot ≠ pivot ∧ 0 < atomPairMinor atom scale pivot slot)

theorem mem_liveSlots {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}
    {scale : Fin slotCount → ℝ} {pivot slot : Fin slotCount} :
    slot ∈ liveSlots atom scale pivot
      ↔ slot ≠ pivot ∧ 0 < atomPairMinor atom scale pivot slot := by
  simp only [liveSlots, Finset.mem_filter, Finset.mem_univ, true_and]

theorem pivot_not_mem_liveSlots {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {pivot : Fin slotCount} : pivot ∉ liveSlots atom scale pivot := by
  intro hmem
  exact (mem_liveSlots.mp hmem).1 rfl

/-- The LIVE READING ENERGY of a pivot: the squared readings of the pivot
against its live slots only. -/
noncomputable def liveReadingEnergy {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot : Fin slotCount) : ℝ :=
  ∑ slot ∈ liveSlots atom scale pivot, atomGram atom pivot slot ^ 2

theorem liveReadingEnergy_nonneg {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot : Fin slotCount) : 0 ≤ liveReadingEnergy atom scale pivot :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **THE LIVE ROW IS BELOW THE FULL ROW.**  The live reading energy never
beats the row energy of the pivot off its own slot, thus the live budget
of layer three is never harder than the landed uniform budget. -/
theorem liveReadingEnergy_le_row {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount) :
    liveReadingEnergy atom scale pivot
      ≤ atomGram atom pivot pivot - atomGram atom pivot pivot ^ 2 := by
  have hsub : liveSlots atom scale pivot ⊆ Finset.univ.erase pivot := by
    intro slot hslot
    exact Finset.mem_erase.mpr ⟨(mem_liveSlots.mp hslot).1, Finset.mem_univ slot⟩
  have hgrow : (∑ slot ∈ liveSlots atom scale pivot, atomGram atom pivot slot ^ 2)
      ≤ ∑ slot ∈ Finset.univ.erase pivot, atomGram atom pivot slot ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  have hrow : (∑ slot ∈ Finset.univ.erase pivot, atomGram atom pivot slot ^ 2)
      = atomGram atom pivot pivot - atomGram atom pivot pivot ^ 2 := by
    have hsplit := Finset.sum_erase_eq_sub
      (f := fun slot => atomGram atom pivot slot ^ 2) (Finset.mem_univ pivot)
    rw [hsplit, atomGram_row_energy hframe pivot]
  simp only [liveReadingEnergy]
  linarith [hgrow, hrow]

/-- The LIVE DISCOUNT INFLATION at one pivot, one discounted slot and one
factor: every live slot pays one deflation weight, the discounted slot
divided by the factor and every other live slot multiplied by it.  A dead
slot pays nothing at all. -/
noncomputable def liveInflation {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot discount : Fin slotCount) (factor : ℝ) : Fin slotCount → ℝ :=
  fun slot => if slot ∈ liveSlots atom scale pivot then
      (if slot = discount then 1 / factor else factor)
        * ((scale pivot / (atomGram atom pivot pivot
            * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2)
    else 0

theorem liveInflation_of_not_mem {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot discount : Fin slotCount) (factor : ℝ) {slot : Fin slotCount}
    (hslot : slot ∉ liveSlots atom scale pivot) :
    liveInflation atom scale pivot discount factor slot = 0 := by
  simp only [liveInflation, if_neg hslot]

theorem liveInflation_pivot {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot discount : Fin slotCount) (factor : ℝ) :
    liveInflation atom scale pivot discount factor pivot = 0 :=
  liveInflation_of_not_mem atom scale pivot discount factor pivot_not_mem_liveSlots

theorem liveInflation_nonneg {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot discount : Fin slotCount) {factor : ℝ} (hfactor : 0 < factor)
    (hdefl : 0 ≤ scale pivot
      / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
    (slot : Fin slotCount) :
    0 ≤ liveInflation atom scale pivot discount factor slot := by
  simp only [liveInflation]
  by_cases hmem : slot ∈ liveSlots atom scale pivot
  · rw [if_pos hmem]
    have hweight : 0 ≤ (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2 :=
      mul_nonneg hdefl (sq_nonneg _)
    by_cases hdisc : slot = discount
    · rw [if_pos hdisc]
      exact mul_nonneg (by positivity) hweight
    · rw [if_neg hdisc]
      exact mul_nonneg hfactor.le hweight
  · rw [if_neg hmem]

/-- **THE LIVE INFLATION OBEYS THE PRODUCT LAW AT EVERY LIVE PAIR.**  At a
pair that holds the discounted slot the two factors cancel exactly, and at
a pair that misses it the two factors multiply to at least one. -/
theorem liveInflation_product {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot discount : Fin slotCount) {factor : ℝ} (hfactor : 1 ≤ factor)
    (hdiagPos : 0 < atomGram atom pivot pivot)
    (hpivotPos : 0 < atomShiftedDiag atom scale pivot)
    (slotOne slotTwo : Fin slotCount)
    (hone : slotOne ∈ liveSlots atom scale pivot)
    (htwo : slotTwo ∈ liveSlots atom scale pivot) (hne : slotOne ≠ slotTwo) :
    (scale pivot * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
      ≤ (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
        * (liveInflation atom scale pivot discount factor slotOne
          * liveInflation atom scale pivot discount factor slotTwo) := by
  have hfactorPos : 0 < factor := lt_of_lt_of_le zero_lt_one hfactor
  have hfactorNe : factor ≠ 0 := ne_of_gt hfactorPos
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
  have hweightNonneg : 0 ≤ (scale pivot / (atomGram atom pivot pivot
      * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2
      * ((scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2) := by
    nlinarith [sq_nonneg ((scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot))
      * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo))]
  simp only [liveInflation, if_pos hone, if_pos htwo]
  have hcoef : (1:ℝ) ≤ (if slotOne = discount then 1 / factor else factor)
      * (if slotTwo = discount then 1 / factor else factor) := by
    by_cases hdOne : slotOne = discount
    · have hdTwo : slotTwo ≠ discount := fun heq => hne (hdOne.trans heq.symm)
      rw [if_pos hdOne, if_neg hdTwo]
      rw [one_div, inv_mul_cancel₀ hfactorNe]
    · rw [if_neg hdOne]
      by_cases hdTwo : slotTwo = discount
      · rw [if_pos hdTwo, one_div, mul_inv_cancel₀ hfactorNe]
      · rw [if_neg hdTwo]
        nlinarith [hfactor]
  have hrearrange : ((if slotOne = discount then 1 / factor else factor)
        * ((scale pivot / (atomGram atom pivot pivot
            * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2))
      * ((if slotTwo = discount then 1 / factor else factor)
        * ((scale pivot / (atomGram atom pivot pivot
            * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2))
      = ((if slotOne = discount then 1 / factor else factor)
          * (if slotTwo = discount then 1 / factor else factor))
        * ((scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2
          * ((scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slotTwo ^ 2)) := by ring
  rw [hrearrange]
  have hpos : 0 < (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2 :=
    pow_pos (mul_pos hdiagPos hpivotPos) 2
  nlinarith [hbase, hweightNonneg, hcoef, hpos]

/-- **THE CLOSED BUDGET OF THE LIVE INFLATION.**  The total of the live
discount inflation is the deflation weight against the discounted reading
divided by the factor, plus the factor against the remaining live reading
energy. -/
theorem liveInflation_sum {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot discount : Fin slotCount) {factor : ℝ} (hfactor : factor ≠ 0)
    (hmem : discount ∈ liveSlots atom scale pivot) :
    (∑ slot, liveInflation atom scale pivot discount factor slot)
      = (scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot))
        * (atomGram atom pivot discount ^ 2 / factor
          + factor * (liveReadingEnergy atom scale pivot
            - atomGram atom pivot discount ^ 2)) := by
  have hzero : ∀ slot ∈ Finset.univ, slot ∉ liveSlots atom scale pivot →
      liveInflation atom scale pivot discount factor slot = 0 :=
    fun slot _ hslot => liveInflation_of_not_mem atom scale pivot discount factor hslot
  have hrestrict : (∑ slot, liveInflation atom scale pivot discount factor slot)
      = ∑ slot ∈ liveSlots atom scale pivot,
          liveInflation atom scale pivot discount factor slot :=
    (Finset.sum_subset (Finset.subset_univ _) hzero).symm
  have hpeel : (∑ slot ∈ liveSlots atom scale pivot,
        liveInflation atom scale pivot discount factor slot)
      = liveInflation atom scale pivot discount factor discount
        + ∑ slot ∈ (liveSlots atom scale pivot).erase discount,
            liveInflation atom scale pivot discount factor slot :=
    (Finset.add_sum_erase _ _ hmem).symm
  have hdiscValue : liveInflation atom scale pivot discount factor discount
      = (1 / factor) * ((scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot)) * atomGram atom pivot discount ^ 2) := by
    simp only [liveInflation, if_pos hmem, if_true]
  have hrest : (∑ slot ∈ (liveSlots atom scale pivot).erase discount,
        liveInflation atom scale pivot discount factor slot)
      = factor * ((scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot))
        * ∑ slot ∈ (liveSlots atom scale pivot).erase discount,
            atomGram atom pivot slot ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun slot hslot => ?_
    have hin : slot ∈ liveSlots atom scale pivot := Finset.mem_of_mem_erase hslot
    have hne : slot ≠ discount := Finset.ne_of_mem_erase hslot
    simp only [liveInflation, if_pos hin, if_neg hne]
  have herase : (∑ slot ∈ (liveSlots atom scale pivot).erase discount,
        atomGram atom pivot slot ^ 2)
      = liveReadingEnergy atom scale pivot - atomGram atom pivot discount ^ 2 := by
    simp only [liveReadingEnergy]
    exact Finset.sum_erase_eq_sub (f := fun slot => atomGram atom pivot slot ^ 2) hmem
  rw [hrestrict, hpeel, hdiscValue, hrest, herase]
  field_simp

/-! ## Layer 3 — the live budget engine -/

/-- **THE LIVE INFLATION ENGINE.**  A live pivot, one live discounted
slot, one factor of at least one, and one division-free budget of the live
reading row: together they supply the deflated pair.

The budget compares the single-budget slack of the pivot, scaled by the
pivot diagonal, against the live reading energy of the pivot spread by the
factor.  Only the live slots pay, thus the budget is never harder than the
landed uniform budget and it is strictly cheaper whenever a slot is
dead. -/
theorem exists_deflated_pair_of_live_inflation
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot discount : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hmem : discount ∈ liveSlots atom scale pivot)
    {factor : ℝ} (hfactor : 1 ≤ factor)
    (hbudget : scale pivot
          * (atomGram atom pivot discount ^ 2 / factor
            + factor * (liveReadingEnergy atom scale pivot
              - atomGram atom pivot discount ^ 2))
        < atomGram atom pivot pivot
          * (atomShiftedDiag atom scale pivot
              * (1 - (∑ slot, scale slot) + scale pivot)
            - scale pivot * (1 - atomGram atom pivot pivot))) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ 0 < atomPairMinor atom scale pivot slotTwo
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo := by
  have hfactorPos : 0 < factor := lt_of_lt_of_le zero_lt_one hfactor
  have hfactorNe : factor ≠ 0 := ne_of_gt hfactorPos
  have hdiagPos : 0 < atomGram atom pivot pivot := by
    have hp := hscale pivot
    have hR := hpivot
    simp only [atomShiftedDiag] at hR
    linarith
  have hdiagNe : atomGram atom pivot pivot ≠ 0 := ne_of_gt hdiagPos
  have hRne : atomShiftedDiag atom scale pivot ≠ 0 := ne_of_gt hpivot
  have hdeflNonneg : 0 ≤ scale pivot
      / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) :=
    div_nonneg (hscale pivot) (mul_nonneg hdiagPos.le hpivot.le)
  refine exists_deflated_pair_of_live_product_inflation hframe hscale hpivot
    (liveInflation_nonneg atom scale pivot discount hfactorPos hdeflNonneg)
    (liveInflation_pivot atom scale pivot discount factor)
    (fun slotOne slotTwo hone htwo hne hminorOne hminorTwo =>
      liveInflation_product atom scale pivot discount hfactor hdiagPos hpivot
        slotOne slotTwo (mem_liveSlots.mpr ⟨hone, hminorOne⟩)
        (mem_liveSlots.mpr ⟨htwo, hminorTwo⟩) hne) ?_
  rw [liveInflation_sum atom scale pivot discount hfactorNe hmem]
  set spread : ℝ := atomGram atom pivot discount ^ 2 / factor
      + factor * (liveReadingEnergy atom scale pivot
        - atomGram atom pivot discount ^ 2) with hspread
  have hclear : (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * spread
      * atomShiftedDiag atom scale pivot * atomGram atom pivot pivot
      = scale pivot * spread := by
    field_simp
  have hstrict : atomGram atom pivot pivot
      * ((scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot)) * spread
        * atomShiftedDiag atom scale pivot)
      < atomGram atom pivot pivot
        * (atomShiftedDiag atom scale pivot
            * (1 - (∑ slot, scale slot) + scale pivot)
          - scale pivot * (1 - atomGram atom pivot pivot)) := by
    have hleft : atomGram atom pivot pivot
        * ((scale pivot / (atomGram atom pivot pivot
            * atomShiftedDiag atom scale pivot)) * spread
          * atomShiftedDiag atom scale pivot)
        = scale pivot * spread := by linarith [hclear]
    rw [hleft]
    exact hbudget
  have hdrop := lt_of_mul_lt_mul_left hstrict hdiagPos.le
  linarith [hdrop]

/-- **THE LIVE BUDGET.**  The uniform instance of the live inflation: the
live reading energy of the pivot against the single-budget slack, scaled
by the pivot diagonal.  This one inequality replaces the landed double
budget, and the live reading energy is at most the full row energy. -/
theorem exists_deflated_pair_of_live_budget
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot discount : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hmem : discount ∈ liveSlots atom scale pivot)
    (hbudget : scale pivot * liveReadingEnergy atom scale pivot
        < atomGram atom pivot pivot
          * (atomShiftedDiag atom scale pivot
              * (1 - (∑ slot, scale slot) + scale pivot)
            - scale pivot * (1 - atomGram atom pivot pivot))) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ 0 < atomPairMinor atom scale pivot slotTwo
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo := by
  refine exists_deflated_pair_of_live_inflation hframe hscale hpivot hmem
    (factor := 1) le_rfl ?_
  have hrewrite : atomGram atom pivot discount ^ 2 / (1:ℝ)
      + (1:ℝ) * (liveReadingEnergy atom scale pivot
        - atomGram atom pivot discount ^ 2)
      = liveReadingEnergy atom scale pivot := by ring
  rw [hrewrite]
  exact hbudget

/-- **THE SCALAR CORE OF THE DISCOUNT CRITERION.**  At the factor that
divides the room by twice the spread, the discounted total is the room
against the geometric bound, thus two division-free inequalities decide
the whole search over the factor. -/
theorem discount_room_lt {head spread room : ℝ} (hspread : 0 < spread)
    (hroom : 2 * spread < room) (hgeom : 4 * head * spread < room ^ 2) :
    head / (room / (2 * spread)) + (room / (2 * spread)) * spread < room := by
  have hroomPos : 0 < room := by linarith
  have hroomNe : room ≠ 0 := ne_of_gt hroomPos
  have hspreadNe : (2:ℝ) * spread ≠ 0 := by positivity
  have hvalue : head / (room / (2 * spread)) + (room / (2 * spread)) * spread
      = (4 * head * spread + room ^ 2) / (2 * room) := by
    field_simp
    ring
  rw [hvalue, div_lt_iff₀ (by linarith : (0:ℝ) < 2 * room)]
  nlinarith [hgeom, hroomPos]

/-- **THE CLOSED DISCOUNT CRITERION.**  Two division-free polynomial
inequalities replace the search over the discount factor: the discounted
reading must be dominated by the room of the single-budget slack, and the
geometric mean of the discounted reading against the remaining live
reading energy must stay below half that room.

The optimal factor is the room divided by twice the spread, and the two
hypotheses are exactly the two conditions that make it admissible. -/
theorem exists_deflated_pair_of_discount_criterion
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot discount : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hmem : discount ∈ liveSlots atom scale pivot)
    (hspread : 0 < scale pivot
      * (liveReadingEnergy atom scale pivot - atomGram atom pivot discount ^ 2))
    (hroom : 2 * (scale pivot
        * (liveReadingEnergy atom scale pivot - atomGram atom pivot discount ^ 2))
      < atomGram atom pivot pivot
        * (atomShiftedDiag atom scale pivot
            * (1 - (∑ slot, scale slot) + scale pivot)
          - scale pivot * (1 - atomGram atom pivot pivot)))
    (hgeom : 4 * (scale pivot * atomGram atom pivot discount ^ 2)
        * (scale pivot
          * (liveReadingEnergy atom scale pivot - atomGram atom pivot discount ^ 2))
      < (atomGram atom pivot pivot
        * (atomShiftedDiag atom scale pivot
            * (1 - (∑ slot, scale slot) + scale pivot)
          - scale pivot * (1 - atomGram atom pivot pivot))) ^ 2) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ 0 < atomPairMinor atom scale pivot slotTwo
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo := by
  set spread : ℝ := scale pivot
      * (liveReadingEnergy atom scale pivot - atomGram atom pivot discount ^ 2)
    with hspreadDef
  set room : ℝ := atomGram atom pivot pivot
      * (atomShiftedDiag atom scale pivot
          * (1 - (∑ slot, scale slot) + scale pivot)
        - scale pivot * (1 - atomGram atom pivot pivot)) with hroomDef
  set head : ℝ := scale pivot * atomGram atom pivot discount ^ 2 with hheadDef
  have hroomPos : 0 < room := by linarith [hspread, hroom]
  have hfactorGe : (1:ℝ) ≤ room / (2 * spread) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * spread)]
    linarith [hroom]
  refine exists_deflated_pair_of_live_inflation hframe hscale hpivot hmem
    (factor := room / (2 * spread)) hfactorGe ?_
  have hfactorPos : 0 < room / (2 * spread) := lt_of_lt_of_le zero_lt_one hfactorGe
  have hvalue : scale pivot
      * (atomGram atom pivot discount ^ 2 / (room / (2 * spread))
        + (room / (2 * spread)) * (liveReadingEnergy atom scale pivot
          - atomGram atom pivot discount ^ 2))
      = head / (room / (2 * spread)) + (room / (2 * spread)) * spread := by
    rw [hheadDef, hspreadDef]
    ring
  rw [hvalue]
  exact discount_room_lt hspread hroom hgeom

/-! ## Layer 4 — the sharp split of the blocked residue -/

/-- **THE FREE SIDE.**  The blocked residue at a scale mass of positive
trine cut.  The scaled two-trine is NOT blocked there, and the sharp
threshold shows that NOTHING is blocked there. -/
def AtomBlockedCutClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) →
    0 < trineCut (∑ slot, scale slot) →
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo

/-- **THE FREE SIDE IS A THEOREM.**  Nothing is blocked at a positive
trine cut, thus the whole stratum below the trine onset is vacuous.  This
is the payoff of the sharp threshold: the demoted field-agnostic programs
are not merely licensed on the free side, they are not needed there. -/
theorem atomBlockedCutClosed_holds : AtomBlockedCutClosed := by
  intro atom scale hpos hsmall hframe hblocked hcut
  exact absurd
    (blocked_trineCut_nonpos hframe (fun slot => (hpos slot).le) hsmall hblocked)
    (not_le.mpr hcut)

/-- **THE WORKING WINDOW.**  The blocked residue between the two cuts:
the trine cut is nonpositive, thus the datum can be blocked, and the
single cut is positive, thus the single-budget engine supplies a pivot.
The window runs from the trine onset `0.7790627` to the single onset
`0.9303062`, and it strictly contains the whole landed band. -/
def AtomBlockedWindowClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) →
    trineCut (∑ slot, scale slot) ≤ 0 →
    0 < singleCut (∑ slot, scale slot) →
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo

/-- **THE DEEP STRATUM.**  The blocked residue at a nonpositive single
cut.  Every live pivot fails even the single inflation budget there, thus
the plane closure supplies nothing and the proof must select its pivot.
The stratum starts at `0.9303062`, far above the landed `39/50`. -/
def AtomBlockedDeepCutClosed : Prop :=
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
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo

/-- **THE TWO REMAINING PARTS CLOSE THE BLOCKED RESIDUE.**  The free side
is a theorem, thus only the window and the deep stratum are left. -/
theorem atomBlockedPairClosed_of_window_of_deepCut
    (hwindow : AtomBlockedWindowClosed) (hdeep : AtomBlockedDeepCutClosed) :
    AtomBlockedPairClosed := by
  intro atom scale hpos hsmall hframe hblocked
  have hcut := blocked_trineCut_nonpos hframe (fun slot => (hpos slot).le) hsmall hblocked
  rcases le_or_gt (singleCut (∑ slot, scale slot)) 0 with hside | hside
  · exact hdeep atom scale hpos hsmall hframe hblocked hside
  · exact hwindow atom scale hpos hsmall hframe hblocked hcut hside

/-- The blocked residue carries the window. -/
theorem atomBlockedWindowClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : AtomBlockedWindowClosed :=
  fun atom scale hpos hsmall hframe hblocked _ _ =>
    hresidue atom scale hpos hsmall hframe hblocked

/-- The blocked residue carries the deep stratum. -/
theorem atomBlockedDeepCutClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : AtomBlockedDeepCutClosed :=
  fun atom scale hpos hsmall hframe hblocked _ =>
    hresidue atom scale hpos hsmall hframe hblocked

/-- **THE SHARP SPLIT IS LOSSLESS.**  The blocked residue is exactly the
conjunction of the window and the deep stratum.  The free side of the
trine cut has vanished from the ledger, because it is a theorem. -/
theorem atomBlockedPairClosed_iff_window_and_deepCut :
    AtomBlockedPairClosed ↔ AtomBlockedWindowClosed ∧ AtomBlockedDeepCutClosed :=
  ⟨fun hresidue => ⟨atomBlockedWindowClosed_of_blockedPair hresidue,
      atomBlockedDeepCutClosed_of_blockedPair hresidue⟩,
    fun hparts => atomBlockedPairClosed_of_window_of_deepCut hparts.1 hparts.2⟩

/-- **THE WINDOW SWALLOWS THE LANDED BAND.**  Every blocked datum of
scale mass at most `39/50` sits inside the window, thus the landed band
residue follows from the window residue alone. -/
theorem atomBlockedBandClosed_of_windowClosed
    (hwindow : AtomBlockedWindowClosed) : AtomBlockedBandClosed :=
  fun atom scale hpos hsmall hframe hblocked hband =>
    hwindow atom scale hpos hsmall hframe hblocked
      (blocked_trineCut_nonpos hframe (fun slot => (hpos slot).le) hsmall hblocked)
      (singleCut_pos_of_le_band hband)

/-- **THE NEW DEEP STRATUM SITS INSIDE THE LANDED ONE.**  A nonpositive
single cut forces the scale mass above `39/50`, thus the landed deep
residue closes the new one. -/
theorem atomBlockedDeepCutClosed_of_deepClosed
    (hdeep : AtomBlockedDeepClosed) : AtomBlockedDeepCutClosed := by
  intro atom scale hpos hsmall hframe hblocked hcut
  refine hdeep atom scale hpos hsmall hframe hblocked ?_
  by_contra hno
  exact absurd (singleCut_pos_of_le_band (not_lt.mp hno)) (not_lt.mpr hcut)

/-- **THE RATIONAL RE-CUT.**  Below the rational split point `779/1000`
the trine cut is positive, thus no datum there is blocked at all. -/
theorem not_blocked_of_le_split
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsplit : (∑ slot, scale slot) ≤ 779 / 1000) :
    ¬ (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) := by
  intro hblocked
  have hsmall : (∑ slot, scale slot) < 1 := lt_of_le_of_lt hsplit (by norm_num)
  have hpos := trineCut_pos_of_le_split hsplit
  have hnonpos := blocked_trineCut_nonpos hframe hscale hsmall hblocked
  linarith

/-! ## Layer 5 — the global kills of the two remaining parts -/

/-- **THE GLOBAL KILL OF THE WINDOW.**  No blocked datum between the two
cuts fails every deflated pair at EVERY live pivot.  This hands the
prover the failure at every live pivot, not only at one, thus it is a
strictly larger hypothesis package than the landed band kill. -/
def AtomBlockedWindowKill : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) →
    trineCut (∑ slot, scale slot) ≤ 0 →
    0 < singleCut (∑ slot, scale slot) →
    (∀ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne → pivot ≠ slotTwo → slotOne ≠ slotTwo →
      0 < atomShiftedDiag atom scale pivot →
      0 < atomPairMinor atom scale pivot slotOne →
      atomPairMinor atom scale pivot slotOne
          * atomPairMinor atom scale pivot slotTwo
        ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2) →
    False

/-- **THE GLOBAL KILL OF THE DEEP STRATUM.** -/
def AtomBlockedDeepCutKill : Prop :=
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
    (∀ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne → pivot ≠ slotTwo → slotOne ≠ slotTwo →
      0 < atomShiftedDiag atom scale pivot →
      0 < atomPairMinor atom scale pivot slotOne →
      atomPairMinor atom scale pivot slotOne
          * atomPairMinor atom scale pivot slotTwo
        ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2) →
    False

theorem atomBlockedWindowClosed_of_windowKill
    (hkill : AtomBlockedWindowKill) : AtomBlockedWindowClosed := by
  intro atom scale hpos hsmall hframe hblocked hcut hsingle
  by_contra hno
  push Not at hno
  exact hkill atom scale hpos hsmall hframe hblocked hcut hsingle hno

theorem atomBlockedWindowKill_of_windowClosed
    (hclosed : AtomBlockedWindowClosed) : AtomBlockedWindowKill := by
  intro atom scale hpos hsmall hframe hblocked hcut hsingle hfail
  obtain ⟨pivot, slotOne, slotTwo, honePivot, htwoPivot, hpairNe, hlive, hminor,
    hcross⟩ := hclosed atom scale hpos hsmall hframe hblocked hcut hsingle
  exact absurd hcross
    (not_lt.mpr (hfail pivot slotOne slotTwo honePivot htwoPivot hpairNe hlive hminor))

/-- **THE GLOBAL KILL IS THE EXACT CONTRAPOSITIVE OF THE WINDOW.** -/
theorem atomBlockedWindowClosed_iff_windowKill :
    AtomBlockedWindowClosed ↔ AtomBlockedWindowKill :=
  ⟨atomBlockedWindowKill_of_windowClosed, atomBlockedWindowClosed_of_windowKill⟩

theorem atomBlockedDeepCutClosed_of_deepCutKill
    (hkill : AtomBlockedDeepCutKill) : AtomBlockedDeepCutClosed := by
  intro atom scale hpos hsmall hframe hblocked hcut
  by_contra hno
  push Not at hno
  exact hkill atom scale hpos hsmall hframe hblocked hcut hno

theorem atomBlockedDeepCutKill_of_deepCutClosed
    (hclosed : AtomBlockedDeepCutClosed) : AtomBlockedDeepCutKill := by
  intro atom scale hpos hsmall hframe hblocked hcut hfail
  obtain ⟨pivot, slotOne, slotTwo, honePivot, htwoPivot, hpairNe, hlive, hminor,
    hcross⟩ := hclosed atom scale hpos hsmall hframe hblocked hcut
  exact absurd hcross
    (not_lt.mpr (hfail pivot slotOne slotTwo honePivot htwoPivot hpairNe hlive hminor))

theorem atomBlockedDeepCutClosed_iff_deepCutKill :
    AtomBlockedDeepCutClosed ↔ AtomBlockedDeepCutKill :=
  ⟨atomBlockedDeepCutKill_of_deepCutClosed, atomBlockedDeepCutClosed_of_deepCutKill⟩

/-! ## Layer 6 — the narrowed attack surface of the window -/

/-- **THE NARROWED KILL OF THE WINDOW.**  The kill only has to answer at
data where NO live discount inflation clears the budget at any live pivot
and any live discounted slot.  That hypothesis is a quantitative
statement about the live reading row of every pivot, and it is strictly
more than the blocked inequality alone.

This is the sharpest named target of the whole atom lane. -/
def AtomBlockedWindowLiveKill : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) →
    trineCut (∑ slot, scale slot) ≤ 0 →
    0 < singleCut (∑ slot, scale slot) →
    (∀ (pivot discount : Fin 6), 0 < atomShiftedDiag atom scale pivot →
      discount ∈ liveSlots atom scale pivot →
      ∀ factor : ℝ, 1 ≤ factor →
        atomGram atom pivot pivot
            * (atomShiftedDiag atom scale pivot
                * (1 - (∑ slot, scale slot) + scale pivot)
              - scale pivot * (1 - atomGram atom pivot pivot))
          ≤ scale pivot
            * (atomGram atom pivot discount ^ 2 / factor
              + factor * (liveReadingEnergy atom scale pivot
                - atomGram atom pivot discount ^ 2))) →
    (∀ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne → pivot ≠ slotTwo → slotOne ≠ slotTwo →
      0 < atomShiftedDiag atom scale pivot →
      0 < atomPairMinor atom scale pivot slotOne →
      atomPairMinor atom scale pivot slotOne
          * atomPairMinor atom scale pivot slotTwo
        ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2) →
    False

/-- **THE NARROWED KILL OF THE DEEP STRATUM.** -/
def AtomBlockedDeepCutLiveKill : Prop :=
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
    (∀ (pivot discount : Fin 6), 0 < atomShiftedDiag atom scale pivot →
      discount ∈ liveSlots atom scale pivot →
      ∀ factor : ℝ, 1 ≤ factor →
        atomGram atom pivot pivot
            * (atomShiftedDiag atom scale pivot
                * (1 - (∑ slot, scale slot) + scale pivot)
              - scale pivot * (1 - atomGram atom pivot pivot))
          ≤ scale pivot
            * (atomGram atom pivot discount ^ 2 / factor
              + factor * (liveReadingEnergy atom scale pivot
                - atomGram atom pivot discount ^ 2))) →
    (∀ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne → pivot ≠ slotTwo → slotOne ≠ slotTwo →
      0 < atomShiftedDiag atom scale pivot →
      0 < atomPairMinor atom scale pivot slotOne →
      atomPairMinor atom scale pivot slotOne
          * atomPairMinor atom scale pivot slotTwo
        ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2) →
    False

/-- **THE NARROWED KILL CLOSES THE GLOBAL KILL.**  Either a live discount
inflation clears the budget at some live pivot, and the live engine
supplies the pair against the global failure, or none does and the
narrowed kill fires. -/
theorem atomBlockedWindowKill_of_windowLiveKill
    (hkill : AtomBlockedWindowLiveKill) : AtomBlockedWindowKill := by
  intro atom scale hpos hsmall hframe hblocked hcut hsingle hfail
  refine hkill atom scale hpos hsmall hframe hblocked hcut hsingle ?_ hfail
  intro pivot discount hlive hmem factor hfactor
  by_contra hno
  push Not at hno
  obtain ⟨slotOne, slotTwo, honePivot, htwoPivot, hpairNe, hminorOne, _, hcross⟩ :=
    exists_deflated_pair_of_live_inflation hframe (fun slot => (hpos slot).le)
      hlive hmem hfactor hno
  exact absurd hcross
    (not_lt.mpr (hfail pivot slotOne slotTwo honePivot htwoPivot hpairNe hlive hminorOne))

theorem atomBlockedDeepCutKill_of_deepCutLiveKill
    (hkill : AtomBlockedDeepCutLiveKill) : AtomBlockedDeepCutKill := by
  intro atom scale hpos hsmall hframe hblocked hcut hfail
  refine hkill atom scale hpos hsmall hframe hblocked hcut ?_ hfail
  intro pivot discount hlive hmem factor hfactor
  by_contra hno
  push Not at hno
  obtain ⟨slotOne, slotTwo, honePivot, htwoPivot, hpairNe, hminorOne, _, hcross⟩ :=
    exists_deflated_pair_of_live_inflation hframe (fun slot => (hpos slot).le)
      hlive hmem hfactor hno
  exact absurd hcross
    (not_lt.mpr (hfail pivot slotOne slotTwo honePivot htwoPivot hpairNe hlive hminorOne))

/-- The window from the narrowed kill. -/
theorem atomBlockedWindowClosed_of_windowLiveKill
    (hkill : AtomBlockedWindowLiveKill) : AtomBlockedWindowClosed :=
  atomBlockedWindowClosed_of_windowKill (atomBlockedWindowKill_of_windowLiveKill hkill)

/-- The deep stratum from the narrowed kill. -/
theorem atomBlockedDeepCutClosed_of_deepCutLiveKill
    (hkill : AtomBlockedDeepCutLiveKill) : AtomBlockedDeepCutClosed :=
  atomBlockedDeepCutClosed_of_deepCutKill (atomBlockedDeepCutKill_of_deepCutLiveKill hkill)

/-! ## Layer 7 — the cell and the payoff from the two remaining parts -/

/-- **THE `(6,3)` CELL FROM THE WINDOW AND THE DEEP STRATUM.** -/
theorem gtzWeighted_six_three_of_window_of_deepCut
    (hwindow : AtomBlockedWindowClosed) (hdeep : AtomBlockedDeepCutClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_blockedPair
    (atomBlockedPairClosed_of_window_of_deepCut hwindow hdeep)

/-- **THE RANK-THREE PAYOFF FROM THE WINDOW AND THE DEEP STRATUM.** -/
theorem gtzWeightedAll_three_of_window_of_deepCut
    (hwindow : AtomBlockedWindowClosed) (hdeep : AtomBlockedDeepCutClosed) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_blockedPair
    (atomBlockedPairClosed_of_window_of_deepCut hwindow hdeep)

/-- The crux type is empty under the window and the deep stratum. -/
theorem isEmpty_sixThreeCrux_of_window_of_deepCut
    (hwindow : AtomBlockedWindowClosed) (hdeep : AtomBlockedDeepCutClosed) :
    IsEmpty SixThreeCrux :=
  isEmpty_sixThreeCrux_of_blockedPair
    (atomBlockedPairClosed_of_window_of_deepCut hwindow hdeep)

/-- **THE `(6,3)` CELL FROM THE TWO GLOBAL KILLS.** -/
theorem gtzWeighted_six_three_of_windowKill_of_deepCutKill
    (hwindow : AtomBlockedWindowKill) (hdeep : AtomBlockedDeepCutKill) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_window_of_deepCut
    (atomBlockedWindowClosed_of_windowKill hwindow)
    (atomBlockedDeepCutClosed_of_deepCutKill hdeep)

/-- **THE RANK-THREE PAYOFF FROM THE TWO GLOBAL KILLS.** -/
theorem gtzWeightedAll_three_of_windowKill_of_deepCutKill
    (hwindow : AtomBlockedWindowKill) (hdeep : AtomBlockedDeepCutKill) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_window_of_deepCut
    (atomBlockedWindowClosed_of_windowKill hwindow)
    (atomBlockedDeepCutClosed_of_deepCutKill hdeep)

/-- **THE `(6,3)` CELL FROM THE TWO NARROWED KILLS.** -/
theorem gtzWeighted_six_three_of_windowLiveKill_of_deepCutLiveKill
    (hwindow : AtomBlockedWindowLiveKill) (hdeep : AtomBlockedDeepCutLiveKill) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_window_of_deepCut
    (atomBlockedWindowClosed_of_windowLiveKill hwindow)
    (atomBlockedDeepCutClosed_of_deepCutLiveKill hdeep)

/-- **THE RANK-THREE PAYOFF FROM THE TWO NARROWED KILLS.** -/
theorem gtzWeightedAll_three_of_windowLiveKill_of_deepCutLiveKill
    (hwindow : AtomBlockedWindowLiveKill) (hdeep : AtomBlockedDeepCutLiveKill) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_window_of_deepCut
    (atomBlockedWindowClosed_of_windowLiveKill hwindow)
    (atomBlockedDeepCutClosed_of_deepCutLiveKill hdeep)

end Gtz
