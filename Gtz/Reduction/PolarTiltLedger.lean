/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.PolarCoverDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The polar tilt ledger: Parseval along the pole prices the whole budget

`Gtz.PolarTiltSelection` asks a covering set of the pole's orthogonal hyperplane
to hold little squared pairing against the pole.  The mass that pairing can hold
is not free: Parseval read along the pole direction prices it exactly.

## 1. The tilt mass

`Gtz.sum_weight_polarPairing_sq` -- the weighted squared pairings of ALL labels
against the pole add up to the pole's own leverage.  Subtracting the pole's own
term gives `Gtz.sum_weight_polarPairing_sq_erase`:

  `Sum_{c != pole} weight c * (atom c . atom pole)^2 = leverage * (1 - weight pole * leverage)`.

The second factor is the SATURATION DEFICIT of the pole.  Every label of the
design carries at most one unit of weighted leverage, thus the deficit is never
negative, and it vanishes exactly when the pole saturates the cap.

## 2. The budget is half the leverage, not the leverage

`Gtz.polarTilt_budget_le_half_leverage` -- the tilt budget the polar
construction supplies is at most HALF the pole's leverage, and the leverage cap
`weight pole * leverage <= 1` is the only input.  This halves the shipped
reading `Gtz.polarTilt_budget_lt_leverage`.

## 3. The saturated pole is closed, with no residual

`Gtz.polarPairing_eq_zero_of_saturated` -- when the pole saturates the leverage
cap, EVERY other atom is orthogonal to it.  The zero-tilt producer then fires,
thus `Gtz.not_isTie_of_saturatedPole` closes the whole saturated stratum from
the previous rank alone.  At rank three the previous rank is the theorem
`Gtz.gtz_rank_two`, thus `Gtz.not_isTie_of_saturatedPole_three` is
unconditional.

## 4. The tie weight law

`Gtz.tie_weightFloor_saturation_sharp` -- a new unconditional inequality about
ties.  At every tie and every overshooting atom,

  `weightFloor * weight pole * (leverage - 1) <= (1 - weight pole) * (1 - weight pole * leverage)`,

where `weightFloor` is any lower bound on the design weights.  The proof reads
the tilted cover of a tie against the tilt mass of part 1, and the share of the
polar construction is driven to zero to reach the sharp constant.  The
contrapositive `Gtz.not_isTie_of_saturationGap` is a checkable criterion that
closes a band of designs outright.

## 5. The narrowed residual

`Gtz.PolarSaturationBudget` bundles the two facts a tie supplies for free, and
`Gtz.PolarTiltSelectionUnsaturated` is `Gtz.PolarTiltSelection` with that bundle
as an extra hypothesis.  It is weaker, and it still closes the hinge, all three
arms of `Gtz.design_stress_trichotomy`, the partial-support sub-arm, the
repaired degenerate cover, the three threshold arms and both registry hinge
obligations.  `Gtz.not_polarTiltSelectionUnsaturated_five_three` calibrates it
at the cell where the hinge is false.
-/

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ## Part 1: Parseval read along the pole

The design identity contracted twice against one atom returns that atom's own
leverage.  The contraction is an identity with no hypothesis, and it is the only
source of information about the squared pairings the residual has to bound. -/

/-- **THE TILT MASS, AS AN IDENTITY.**  The weighted squared pairings of all
labels against a fixed atom add up to that atom's leverage. -/
theorem sum_weight_polarPairing_sq (design : WeightedDesign size rank) (pole : Fin size) :
    ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom pole) ^ 2
      = design.atom pole ⬝ᵥ design.atom pole := by
  conv_rhs =>
    rw [dotProduct_eq_sum_weight_mul_pair design (design.atom pole) (design.atom pole)]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- **THE OFF-POLE TILT MASS.**  Removing the pole's own term leaves the
leverage times the SATURATION DEFICIT `1 - weight pole * leverage`. -/
theorem sum_weight_polarPairing_sq_erase (design : WeightedDesign size rank) (pole : Fin size) :
    ∑ c ∈ Finset.univ.erase pole, design.weight c * (design.atom c ⬝ᵥ design.atom pole) ^ 2
      = (design.atom pole ⬝ᵥ design.atom pole)
        * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole)) := by
  classical
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ pole), sum_weight_polarPairing_sq]
  ring

/-- The saturation deficit of every atom is nonnegative, because the weighted
leverage of an atom never exceeds one. -/
theorem saturationDeficit_nonneg (design : WeightedDesign size rank) (pole : Fin size) :
    0 ≤ 1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole) := by
  have hcap := weight_mul_selfDotProduct_le_one design pole
  linarith

/-- **A SATURATED POLE IS ORTHOGONAL TO EVERY OTHER ATOM.**  A vanishing
saturation deficit kills the whole off-pole tilt mass, and every term of that
mass is nonnegative. -/
theorem polarPairing_eq_zero_of_saturated (design : WeightedDesign size rank) {pole : Fin size}
    (hsaturated : design.weight pole * (design.atom pole ⬝ᵥ design.atom pole) = 1)
    {label : Fin size} (hne : label ≠ pole) :
    design.atom label ⬝ᵥ design.atom pole = 0 := by
  classical
  have hmass := sum_weight_polarPairing_sq_erase design pole
  rw [hsaturated] at hmass
  have hzero : ∑ c ∈ Finset.univ.erase pole,
      design.weight c * (design.atom c ⬝ᵥ design.atom pole) ^ 2 = 0 := by
    rw [hmass]; ring
  have hnonneg : ∀ c ∈ Finset.univ.erase pole,
      0 ≤ design.weight c * (design.atom c ⬝ᵥ design.atom pole) ^ 2 :=
    fun c _ => mul_nonneg (design.weight_pos c).le (sq_nonneg _)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero label
    (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ label⟩)
  rcases mul_eq_zero.mp hterm with hweight | hsquare
  · exact absurd hweight (ne_of_gt (design.weight_pos label))
  · exact sq_eq_zero_iff.mp hsquare

/-- **THE WEIGHT FLOOR PRICES EVERY TILT.**  A set that misses the pole carries
squared pairing at most the off-pole tilt mass divided by the weight floor.
Stated multiplication-only, thus no division and no positivity side condition on
the floor beyond nonnegativity. -/
theorem weightFloor_mul_polarTilt_le (design : WeightedDesign size rank) (pole : Fin size)
    {selected : Finset (Fin size)} (hpoleNotMem : pole ∉ selected)
    {weightFloor : ℝ} (hfloor : ∀ c, weightFloor ≤ design.weight c) :
    weightFloor * ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2
      ≤ (design.atom pole ⬝ᵥ design.atom pole)
        * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole)) := by
  classical
  have hsub : selected ⊆ Finset.univ.erase pole := fun c hc =>
    Finset.mem_erase.mpr ⟨fun heq => hpoleNotMem (heq ▸ hc), Finset.mem_univ c⟩
  have hstep : weightFloor * ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2
      ≤ ∑ c ∈ selected, design.weight c * (design.atom c ⬝ᵥ design.atom pole) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (hfloor c) (sq_nonneg _)
  have hgrow : ∑ c ∈ selected, design.weight c * (design.atom c ⬝ᵥ design.atom pole) ^ 2
      ≤ ∑ c ∈ Finset.univ.erase pole,
          design.weight c * (design.atom c ⬝ᵥ design.atom pole) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun c _ _ =>
      mul_nonneg (design.weight_pos c).le (sq_nonneg _)
  rw [← sum_weight_polarPairing_sq_erase design pole]
  linarith

/-- **EVERY DESIGN HAS A POSITIVE WEIGHT FLOOR.**  The smallest weight of a
finite family of positive weights is positive. -/
theorem exists_weight_floor (design : WeightedDesign size rank) (hpos : 0 < size) :
    ∃ weightFloor : ℝ, 0 < weightFloor ∧ ∀ c, weightFloor ≤ design.weight c := by
  classical
  have hne : (Finset.univ : Finset (Fin size)).Nonempty := ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne design.weight, ?_,
    fun c => Finset.inf'_le _ (Finset.mem_univ c)⟩
  rw [Finset.lt_inf'_iff]
  exact fun c _ => design.weight_pos c

/-- The weight floor of a design of rank at least one, with the size hypothesis
discharged by `Gtz.rank_le_of_design`. -/
theorem exists_weight_floor_of_rank (design : WeightedDesign size rank) (hrank : 1 ≤ rank) :
    ∃ weightFloor : ℝ, 0 < weightFloor ∧ ∀ c, weightFloor ≤ design.weight c :=
  exists_weight_floor design (lt_of_lt_of_le hrank (rank_le_of_design design))

/-! ## Part 2: the budget is half the leverage

The shipped reading `Gtz.polarTilt_budget_lt_leverage` prices the budget by the
leverage.  The leverage cap prices it by HALF the leverage, and the two-line
proof is the cap itself. -/

/-- **THE TILT BUDGET IS AT MOST HALF THE LEVERAGE.**  At the margin the polar
construction supplies at the half share, the budget `margin * leverage *
(leverage - 1)` never exceeds `leverage / 2`.  Equality asks the pole to saturate
the leverage cap, and `Gtz.polarPairing_eq_zero_of_saturated` closes that case
outright. -/
theorem polarTilt_budget_le_half_leverage (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    design.weight pole / (2 * (1 - design.weight pole))
        * (design.atom pole ⬝ᵥ design.atom pole)
        * (design.atom pole ⬝ᵥ design.atom pole - 1)
      ≤ (design.atom pole ⬝ᵥ design.atom pole) / 2 := by
  have hcap := weight_mul_selfDotProduct_le_one design pole
  have hweightPos := design.weight_pos pole
  have hweightLt := weight_lt_one_of_one_lt_selfDotProduct design hlong
  have hden : (0 : ℝ) < 2 * (1 - design.weight pole) := by linarith
  have hproduct : 0 ≤ (design.atom pole ⬝ᵥ design.atom pole)
      * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole)) :=
    mul_nonneg (by linarith) (saturationDeficit_nonneg design pole)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [hproduct, hlong, hweightPos]

/-- **THE BUDGET IS STRICTLY BELOW HALF THE LEVERAGE OFF THE SATURATED
STRATUM.**  A positive saturation deficit makes the cap strict. -/
theorem polarTilt_budget_lt_half_leverage (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hunsaturated : design.weight pole * (design.atom pole ⬝ᵥ design.atom pole) < 1) :
    design.weight pole / (2 * (1 - design.weight pole))
        * (design.atom pole ⬝ᵥ design.atom pole)
        * (design.atom pole ⬝ᵥ design.atom pole - 1)
      < (design.atom pole ⬝ᵥ design.atom pole) / 2 := by
  have hweightPos := design.weight_pos pole
  have hweightLt := weight_lt_one_of_one_lt_selfDotProduct design hlong
  have hden : (0 : ℝ) < 2 * (1 - design.weight pole) := by linarith
  have hproduct : 0 < (design.atom pole ⬝ᵥ design.atom pole)
      * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole)) :=
    mul_pos (by linarith) (by linarith)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ hden]
  nlinarith [hproduct, hlong, hweightPos]

/-! ## Part 3: the saturated stratum is closed, with no residual

The zero-tilt producer `Gtz.posDef_insert_of_orthogonalCover` fires with no
budget at all.  The saturated pole supplies its hypothesis for free, thus a whole
stratum of designs leaves the residual untouched. -/

/-- **A SATURATED POLE PRODUCES A STRICT DOMINATOR.**  The previous rank supplies
the cover and the saturation supplies the orthogonality, thus the pole together
with its cover beats the identity strictly. -/
theorem exists_dominating_of_saturatedPole (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    {pole : Fin size} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hsaturated : design.weight pole * (design.atom pole ⬝ᵥ design.atom pole) = 1) :
    ∃ selected : Finset (Fin size), selected.card = rank
      ∧ (subsetSum design selected - 1).PosDef := by
  classical
  obtain ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin hrank hpredecessor design hlong
  have horthogonal : ∀ label ∈ covering, design.atom label ⬝ᵥ design.atom pole = 0 := by
    intro label hlabel
    exact polarPairing_eq_zero_of_saturated design hsaturated
      (fun heq => hnotMem (heq ▸ hlabel))
  have hposDef := posDef_insert_of_orthogonalCover design hnotMem hlong hmarginPos hcover
    horthogonal
  refine exists_card_eq_posDef design ?_ hposDef
  rw [Finset.card_insert_of_notMem hnotMem, hcard]
  omega

/-- **NO TIE CARRIES A SATURATED OVERSHOOTING ATOM.**  The whole saturated
stratum is closed by the previous rank alone. -/
theorem not_isTie_of_saturatedPole (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    {pole : Fin size} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hsaturated : design.weight pole * (design.atom pole ⬝ᵥ design.atom pole) = 1) :
    ¬ IsTie design := by
  intro htie
  obtain ⟨selected, hcard, hposDef⟩ :=
    exists_dominating_of_saturatedPole hrank hpredecessor design hlong hsaturated
  exact htie.2 selected hcard hposDef

/-- **AT A TIE EVERY OVERSHOOTING ATOM IS STRICTLY BELOW THE LEVERAGE CAP.**  The
cap `weight * leverage <= 1` holds at every design, and a tie forbids equality at
an overshooting atom. -/
theorem tie_weight_mul_leverage_lt_one (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    (htie : IsTie design) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    design.weight pole * (design.atom pole ⬝ᵥ design.atom pole) < 1 := by
  rcases lt_or_eq_of_le (weight_mul_selfDotProduct_le_one design pole) with hlt | heq
  · exact hlt
  · exact absurd htie (not_isTie_of_saturatedPole hrank hpredecessor design hlong heq)

/-- The saturated stratum at rank three, with the previous rank discharged by the
theorem `Gtz.gtz_rank_two`. -/
theorem not_isTie_of_saturatedPole_three (design : WeightedDesign size 3)
    {pole : Fin size} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hsaturated : design.weight pole * (design.atom pole ⬝ᵥ design.atom pole) = 1) :
    ¬ IsTie design :=
  not_isTie_of_saturatedPole (by norm_num) gtz_rank_two design hlong hsaturated

/-! ## Part 4: the share-parametrized cover and the tie weight law

`Gtz.exists_polarCover_margin` hides the margin behind an existential and fixes
the share at half the pole's weight.  The margin is a named function of the
share, and driving the share to zero doubles the budget.  That is what the tie
weight law needs. -/

/-- **THE POLAR COVER AT AN EXPLICIT SHARE.**  The margin of the cover the
previous rank supplies is `(weight pole - share) / (1 - weight pole)` at every
admissible share.  The shipped `Gtz.exists_polarCover_margin` is the instance at
the half share, with the margin hidden. -/
theorem exists_polarCover_margin_of_share (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {share : ℝ} (hshare : 0 < share) (hshareLt : share < design.weight pole) :
    ∃ covering : Finset (Fin size), covering.card = rank - 1 ∧ pole ∉ covering
      ∧ ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + (design.weight pole - share) / (1 - design.weight pole)) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 := by
  have hweightLt := weight_lt_one_of_one_lt_selfDotProduct design hlong
  obtain ⟨covering, hcard, hnotMem, hcover⟩ :=
    exists_polarStrictCover hrank hpredecessor design hlong hshare hshareLt
  refine ⟨covering, hcard, hnotMem, fun probe hprobe => ?_⟩
  have hne : (1 : ℝ) - design.weight pole ≠ 0 := by linarith
  have hrewrite : (1 : ℝ) + (design.weight pole - share) / (1 - design.weight pole)
      = (1 - share) / (1 - design.weight pole) := by
    field_simp
    ring
  rw [hrewrite]
  exact hcover probe hprobe

/-- **THE TILTED COVER AT AN EXPLICIT SHARE.**  At a tie the cover of the
previous rank spends the whole budget of its own share. -/
theorem exists_tilted_polarCover_of_share (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    (htie : IsTie design) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {share : ℝ} (hshare : 0 < share) (hshareLt : share < design.weight pole) :
    ∃ covering : Finset (Fin size), covering.card = rank - 1 ∧ pole ∉ covering
      ∧ (design.weight pole - share) / (1 - design.weight pole)
            * (design.atom pole ⬝ᵥ design.atom pole)
            * (design.atom pole ⬝ᵥ design.atom pole - 1)
          ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2 := by
  have hweightLt := weight_lt_one_of_one_lt_selfDotProduct design hlong
  obtain ⟨covering, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin_of_share hrank hpredecessor design hlong hshare hshareLt
  have hmarginPos : 0 < (design.weight pole - share) / (1 - design.weight pole) :=
    div_pos (by linarith) (by linarith)
  exact ⟨covering, hcard, hnotMem,
    budget_le_tilt_of_isTie design htie (by omega) (le_of_eq hcard) hnotMem hlong hmarginPos
      hcover⟩

/-- **THE TIE WEIGHT LAW AT AN EXPLICIT SHARE.**  The tilted cover of a tie is
priced by the off-pole tilt mass, thus the weight floor, the share and the
saturation deficit obey one inequality. -/
theorem tie_weightFloor_saturation_of_share (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    (htie : IsTie design) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {weightFloor : ℝ} (hfloorNonneg : 0 ≤ weightFloor)
    (hfloor : ∀ c, weightFloor ≤ design.weight c)
    {share : ℝ} (hshare : 0 < share) (hshareLt : share < design.weight pole) :
    weightFloor * (design.weight pole - share)
        * (design.atom pole ⬝ᵥ design.atom pole - 1)
      ≤ (1 - design.weight pole)
        * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole)) := by
  classical
  have hweightLt := weight_lt_one_of_one_lt_selfDotProduct design hlong
  have hslack : (0 : ℝ) < 1 - design.weight pole := by linarith
  have hleveragePos : (0 : ℝ) < design.atom pole ⬝ᵥ design.atom pole := by linarith
  obtain ⟨covering, hcard, hnotMem, htilt⟩ :=
    exists_tilted_polarCover_of_share hrank hpredecessor design htie hlong hshare hshareLt
  have hmass := weightFloor_mul_polarTilt_le design pole hnotMem hfloor
  have hscaled : weightFloor
      * ((design.weight pole - share) / (1 - design.weight pole)
          * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1))
      ≤ weightFloor * ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2 :=
    mul_le_mul_of_nonneg_left htilt hfloorNonneg
  have hchain : weightFloor
      * ((design.weight pole - share) / (1 - design.weight pole)
          * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1))
      ≤ (design.atom pole ⬝ᵥ design.atom pole)
        * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole)) := by
    linarith [hscaled, hmass]
  have hclear : weightFloor
      * ((design.weight pole - share) / (1 - design.weight pole)
          * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1))
      * ((1 - design.weight pole) * (design.atom pole ⬝ᵥ design.atom pole)⁻¹)
      = weightFloor * (design.weight pole - share)
        * (design.atom pole ⬝ᵥ design.atom pole - 1) := by
    field_simp
  have hpositive : (0 : ℝ)
      < (1 - design.weight pole) * (design.atom pole ⬝ᵥ design.atom pole)⁻¹ :=
    mul_pos hslack (inv_pos.mpr hleveragePos)
  have hstep := mul_le_mul_of_nonneg_right hchain hpositive.le
  rw [hclear] at hstep
  have hright : (design.atom pole ⬝ᵥ design.atom pole)
      * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole))
      * ((1 - design.weight pole) * (design.atom pole ⬝ᵥ design.atom pole)⁻¹)
      = (1 - design.weight pole)
        * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole)) := by
    field_simp
  rwa [hright] at hstep

/-- **THE TIE WEIGHT LAW, SHARP.**  Driving the share to zero removes it from the
inequality:

  `weightFloor * weight pole * (leverage - 1)
     <= (1 - weight pole) * (1 - weight pole * leverage)`.

No residual and no conjecture is spent beyond the previous rank.  The right side
is the SATURATION DEFICIT scaled by the free mass, thus a tie cannot let any
overshooting atom approach the leverage cap while the weights stay bounded
below. -/
theorem tie_weightFloor_saturation_sharp (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    (htie : IsTie design) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {weightFloor : ℝ} (hfloorPos : 0 < weightFloor)
    (hfloor : ∀ c, weightFloor ≤ design.weight c) :
    weightFloor * design.weight pole * (design.atom pole ⬝ᵥ design.atom pole - 1)
      ≤ (1 - design.weight pole)
        * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole)) := by
  by_contra hcontra
  rw [not_le] at hcontra
  have hweightPos := design.weight_pos pole
  have hgapPos : (0 : ℝ) < design.atom pole ⬝ᵥ design.atom pole - 1 := by linarith
  set gap : ℝ := weightFloor * design.weight pole
      * (design.atom pole ⬝ᵥ design.atom pole - 1)
    - (1 - design.weight pole)
      * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole)) with hgapDef
  have hgap : 0 < gap := by rw [hgapDef]; linarith
  have hscalePos : (0 : ℝ) < weightFloor
      * (design.atom pole ⬝ᵥ design.atom pole - 1) := mul_pos hfloorPos hgapPos
  set share : ℝ := min (design.weight pole / 2)
    (gap / (2 * (weightFloor * (design.atom pole ⬝ᵥ design.atom pole - 1)))) with hshareDef
  have hshareLeHalf : share ≤ design.weight pole / 2 := by rw [hshareDef]; exact min_le_left _ _
  have hshareLeGap : share
      ≤ gap / (2 * (weightFloor * (design.atom pole ⬝ᵥ design.atom pole - 1))) := by
    rw [hshareDef]; exact min_le_right _ _
  have hsharePos : 0 < share := by
    rw [hshareDef]
    exact lt_min (by linarith) (div_pos hgap (by linarith))
  have hshareLt : share < design.weight pole := by linarith
  have hlaw := tie_weightFloor_saturation_of_share hrank hpredecessor design htie hlong
    hfloorPos.le hfloor hsharePos hshareLt
  have hspend : weightFloor * (design.atom pole ⬝ᵥ design.atom pole - 1) * share ≤ gap / 2 := by
    have hstep := mul_le_mul_of_nonneg_left hshareLeGap hscalePos.le
    rw [mul_div_assoc'] at hstep
    calc weightFloor * (design.atom pole ⬝ᵥ design.atom pole - 1) * share
        ≤ weightFloor * (design.atom pole ⬝ᵥ design.atom pole - 1) * gap
            / (2 * (weightFloor * (design.atom pole ⬝ᵥ design.atom pole - 1))) := hstep
      _ = gap / 2 := by field_simp
  nlinarith [hlaw, hspend, hgap]

/-- **THE CRITERION.**  A design whose weight floor beats the saturation deficit
at one overshooting atom is not a tie.  This is the tie weight law read
backwards, and it closes a band of designs with no residual. -/
theorem not_isTie_of_saturationGap (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    {pole : Fin size} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {weightFloor : ℝ} (hfloorPos : 0 < weightFloor)
    (hfloor : ∀ c, weightFloor ≤ design.weight c)
    (hgap : (1 - design.weight pole)
        * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole))
      < weightFloor * design.weight pole
        * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ¬ IsTie design := by
  intro htie
  exact absurd (tie_weightFloor_saturation_sharp hrank hpredecessor design htie hlong hfloorPos
    hfloor) (not_le.mpr hgap)

/-- The tie weight law at rank three, with the previous rank discharged. -/
theorem tie_weightFloor_saturation_three (design : WeightedDesign size 3)
    (htie : IsTie design) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {weightFloor : ℝ} (hfloorPos : 0 < weightFloor)
    (hfloor : ∀ c, weightFloor ≤ design.weight c) :
    weightFloor * design.weight pole * (design.atom pole ⬝ᵥ design.atom pole - 1)
      ≤ (1 - design.weight pole)
        * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole)) :=
  tie_weightFloor_saturation_sharp (by norm_num) gtz_rank_two design htie hlong hfloorPos hfloor

/-- The criterion at rank three, with the previous rank discharged. -/
theorem not_isTie_of_saturationGap_three (design : WeightedDesign size 3)
    {pole : Fin size} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {weightFloor : ℝ} (hfloorPos : 0 < weightFloor)
    (hfloor : ∀ c, weightFloor ≤ design.weight c)
    (hgap : (1 - design.weight pole)
        * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole))
      < weightFloor * design.weight pole
        * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ¬ IsTie design :=
  not_isTie_of_saturationGap (by norm_num) gtz_rank_two design hlong hfloorPos hfloor hgap

/-! ## Part 5: how many poles a design carries

The tie weight law fires at every overshooting atom, thus it is worth knowing how
many there are.  Every design of rank at least two carries at least `rank` of
them, and the count is free from the leverage cap. -/

/-- **A DESIGN CARRIES AT LEAST `rank` OVERSHOOTING ATOMS.**  The weighted
leverage of a design is its rank, the weights add up to one, and every atom
carries at most one unit of weighted leverage.  Thus the overshooting labels
cannot be fewer than the rank. -/
theorem card_overshooting_ge_rank (design : WeightedDesign size rank) (hrank : 2 ≤ rank) :
    (rank : ℕ)
      ≤ (Finset.univ.filter fun c : Fin size => 1 < design.atom c ⬝ᵥ design.atom c).card := by
  classical
  set heavy := Finset.univ.filter fun c : Fin size => 1 < design.atom c ⬝ᵥ design.atom c
    with hheavyDef
  have hleverage : ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom c) = (rank : ℝ) := by
    rw [← sum_weighted_leverage design]
    exact Finset.sum_congr rfl fun c _ => by rw [leverageOf_eq_dotProduct]
  have hexcess : ∑ c, design.weight c * ((design.atom c ⬝ᵥ design.atom c) - 1)
      = (rank : ℝ) - 1 := by
    have hsplit : ∑ c, design.weight c * ((design.atom c ⬝ᵥ design.atom c) - 1)
        = (∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom c)) - ∑ c, design.weight c := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [hsplit, hleverage, design.weight_sum_one]
  have hlight : ∑ c ∈ heavyᶜ, design.weight c * ((design.atom c ⬝ᵥ design.atom c) - 1) ≤ 0 := by
    refine Finset.sum_nonpos fun c hc => ?_
    have hmem : c ∉ heavy := Finset.mem_compl.mp hc
    have hle : design.atom c ⬝ᵥ design.atom c ≤ 1 := by
      by_contra hgt
      exact hmem (by rw [hheavyDef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, not_le.mp hgt⟩)
    exact mul_nonpos_of_nonneg_of_nonpos (design.weight_pos c).le (by linarith)
  have hheavy : (rank : ℝ) - 1
      ≤ ∑ c ∈ heavy, design.weight c * ((design.atom c ⬝ᵥ design.atom c) - 1) := by
    have hsplit : ∑ c ∈ heavy, design.weight c * ((design.atom c ⬝ᵥ design.atom c) - 1)
        + ∑ c ∈ heavyᶜ, design.weight c * ((design.atom c ⬝ᵥ design.atom c) - 1)
        = ∑ c, design.weight c * ((design.atom c ⬝ᵥ design.atom c) - 1) :=
      Finset.sum_add_sum_compl heavy _
    linarith [hsplit, hexcess, hlight]
  have hcapped : ∑ c ∈ heavy, design.weight c * ((design.atom c ⬝ᵥ design.atom c) - 1)
      < (heavy.card : ℝ) := by
    have hterms : ∀ c ∈ heavy,
        design.weight c * ((design.atom c ⬝ᵥ design.atom c) - 1) < 1 := by
      intro c _
      have hcap := weight_mul_selfDotProduct_le_one design c
      have hpos := design.weight_pos c
      nlinarith [hcap, hpos]
    have hne : heavy.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.sum_empty] at hheavy
      have hrankCast : (2 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
      linarith
    calc ∑ c ∈ heavy, design.weight c * ((design.atom c ⬝ᵥ design.atom c) - 1)
        < ∑ _c ∈ heavy, (1 : ℝ) := Finset.sum_lt_sum_of_nonempty hne hterms
      _ = (heavy.card : ℝ) := by simp
  have hcast : (rank : ℝ) - 1 < (heavy.card : ℝ) := by linarith
  have hnat : (rank : ℝ) < (heavy.card : ℝ) + 1 := by linarith
  have hstep : rank < heavy.card + 1 := by exact_mod_cast hnat
  omega

/-! ## Part 6: the narrowed residual

Both facts of parts 3 and 4 are theorems at a tie, but only under the previous
rank, which the residual does not carry.  Bundling them as a hypothesis makes the
residual strictly easier to attack at every rank above three while it still
closes every consumer. -/

/-- **THE FREE BUDGET FACTS.**  What a tie supplies at an overshooting atom: a
strict leverage cap, and the tie weight law against every weight floor. -/
def PolarSaturationBudget (design : WeightedDesign size rank) (pole : Fin size) : Prop :=
  design.weight pole * (design.atom pole ⬝ᵥ design.atom pole) < 1
    ∧ ∀ weightFloor : ℝ, 0 < weightFloor → (∀ c, weightFloor ≤ design.weight c) →
        weightFloor * design.weight pole * (design.atom pole ⬝ᵥ design.atom pole - 1)
          ≤ (1 - design.weight pole)
            * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole))

/-- **THE BUDGET FACTS ARE FREE AT EVERY TIE.** -/
theorem polarSaturationBudget_of_isTie (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    (htie : IsTie design) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    PolarSaturationBudget design pole :=
  ⟨tie_weight_mul_leverage_lt_one hrank hpredecessor design htie hlong,
    fun _weightFloor hfloorPos hfloor =>
      tie_weightFloor_saturation_sharp hrank hpredecessor design htie hlong hfloorPos hfloor⟩

/-- **THE NARROWED TILT RESIDUAL.**  `Gtz.PolarTiltSelection` with the free
budget facts of a tie handed to it.  Every consumer of the shipped residual runs
on this one. -/
def PolarTiltSelectionUnsaturated (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (pole : Fin size) (covering : Finset (Fin size))
      (margin : ℝ),
    IsPrimitiveDesign design →
    IsTie design →
    1 < design.atom pole ⬝ᵥ design.atom pole →
    PolarSaturationBudget design pole →
    0 < margin →
    covering.card = rank - 1 → pole ∉ covering →
    (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) →
    ∃ selected : Finset (Fin size), selected.card = rank - 1 ∧ pole ∉ selected
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2)
      ∧ ∑ label ∈ selected, (design.atom label ⬝ᵥ design.atom pole) ^ 2
          < margin * (design.atom pole ⬝ᵥ design.atom pole)
              * (design.atom pole ⬝ᵥ design.atom pole - 1)

/-- The narrowed residual is weaker than the shipped one. -/
theorem polarTiltSelectionUnsaturated_of_polarTiltSelection
    (htilt : PolarTiltSelection size rank) : PolarTiltSelectionUnsaturated size rank :=
  fun design pole covering margin hprimitive htie hlong _hbudget hmargin hcard hnotMem hcover =>
    htilt design pole covering margin hprimitive htie hlong hmargin hcard hnotMem hcover

/-- **THE HINGE FROM THE NARROWED RESIDUAL.**  The budget facts are theorems at a
tie, thus the narrowing costs nothing downstream. -/
theorem hingeHoldsAtSize_of_polarTiltUnsaturated (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelectionUnsaturated size rank) : HingeHoldsAtSize size rank := by
  classical
  intro design htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  obtain ⟨pole, hlong⟩ := exists_overshooting_atom design hrank
  obtain ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin hrank hpredecessor design hlong
  obtain ⟨selected, hselCard, hselNotMem, hselCover, hselTilt⟩ :=
    htilt design pole covering margin hprimitive htie hlong
      (polarSaturationBudget_of_isTie hrank hpredecessor design htie hlong)
      hmarginPos hcard hnotMem hcover
  have hposDef := posDef_insert_of_polarCover design hselNotMem hlong hmarginPos hselCover hselTilt
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hselNotMem, hselCard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-! ### Every consumer of the shipped residual, on the narrowed one -/

/-- Arm (i). -/
theorem stressFreeArmAt_of_polarTiltUnsaturated (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelectionUnsaturated size rank) : StressFreeArmAt size rank :=
  fun design _hfree htie =>
    hingeHoldsAtSize_of_polarTiltUnsaturated hrank hpredecessor htilt design htie

/-- Arm (ii). -/
theorem balancedArmAt_of_polarTiltUnsaturated (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelectionUnsaturated size rank) : BalancedArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltUnsaturated hrank hpredecessor htilt design htie

/-- Arm (iii). -/
theorem degenerateArmAt_of_polarTiltUnsaturated (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelectionUnsaturated size rank) : DegenerateArmAt size rank :=
  fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
    hingeHoldsAtSize_of_polarTiltUnsaturated hrank hpredecessor htilt design htie

/-- The partial-support sub-arm. -/
theorem balancedPartialSupportArmAt_of_polarTiltUnsaturated (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelectionUnsaturated size rank) :
    BalancedPartialSupportArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hunsupported _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltUnsaturated hrank hpredecessor htilt design htie

/-- The full-support sub-arm. -/
theorem balancedFullSupportArmAt_of_polarTiltUnsaturated (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelectionUnsaturated size rank) :
    BalancedFullSupportArmAt size rank :=
  fun design _stressCoeff _hstress _hfull htie =>
    hingeHoldsAtSize_of_polarTiltUnsaturated hrank hpredecessor htilt design htie

/-- The repaired degenerate cover. -/
theorem degenerateHyperplaneCover_of_polarTiltUnsaturated (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelectionUnsaturated size rank) :
    DegenerateHyperplaneCover size rank := by
  intro design _stressCoeff _unitNormal _pole hprimitive htie _hstressNe _hunit _hstress
    _hsupport _hpole
  exact absurd (hingeHoldsAtSize_of_polarTiltUnsaturated hrank hpredecessor htilt design htie)
    ((isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive)

/-- The threshold cell obligation of the registry. -/
theorem thresholdCellHingeRankFourAndUp_of_polarTiltUnsaturated
    (htilt : ∀ rank : ℕ, 4 ≤ rank →
      PolarTiltSelectionUnsaturated (thresholdSize rank) rank) :
    ∀ rank : ℕ, 4 ≤ rank → GtzWeightedAll (rank - 1) →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor _hcell design htie
  exact hingeHoldsAtSize_of_polarTiltUnsaturated (by omega) hpredecessor (htilt rank hrank)
    design htie

/-- The sub-threshold band obligation of the registry. -/
theorem subThresholdBandHinge_of_polarTiltUnsaturated
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size < thresholdSize rank →
      PolarTiltSelectionUnsaturated size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor size hlow hhigh _hcell design htie
  exact hingeHoldsAtSize_of_polarTiltUnsaturated (by omega) hpredecessor
    (htilt rank size hrank hlow hhigh) design htie

/-- The whole sharp window, from one narrowed residual per cell. -/
theorem sharpWindowHinge_of_polarTiltUnsaturated
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size ≤ thresholdSize rank →
      PolarTiltSelectionUnsaturated size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        HingeHoldsAtSize size rank := by
  intro rank hrank hpredecessor size hlow hhigh
  exact hingeHoldsAtSize_of_polarTiltUnsaturated (by omega) hpredecessor
    (htilt rank size hrank hlow hhigh)

/-- Arm (i) at the deciding cell of a rank. -/
theorem thresholdStressFreeArm_of_polarTiltUnsaturated (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelectionUnsaturated (thresholdSize rank) rank) :
    ThresholdStressFreeArm rank :=
  stressFreeArmAt_of_polarTiltUnsaturated hrank hpredecessor htilt

/-- Arm (ii) at the deciding cell of a rank. -/
theorem thresholdBalancedArm_of_polarTiltUnsaturated (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelectionUnsaturated (thresholdSize rank) rank) :
    ThresholdBalancedArm rank :=
  balancedArmAt_of_polarTiltUnsaturated hrank hpredecessor htilt

/-- Arm (iii) at the deciding cell of a rank. -/
theorem thresholdDegenerateArm_of_polarTiltUnsaturated (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelectionUnsaturated (thresholdSize rank) rank) :
    ThresholdDegenerateArm rank :=
  degenerateArmAt_of_polarTiltUnsaturated hrank hpredecessor htilt

/-- **THE COLLAPSE, ON THE NARROWED RESIDUAL.** -/
theorem polarTiltUnsaturated_closes_every_arm (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelectionUnsaturated size rank) :
    HingeHoldsAtSize size rank ∧ StressFreeArmAt size rank ∧ BalancedArmAt size rank
      ∧ DegenerateArmAt size rank ∧ BalancedPartialSupportArmAt size rank
      ∧ DegenerateHyperplaneCover size rank :=
  ⟨hingeHoldsAtSize_of_polarTiltUnsaturated hrank hpredecessor htilt,
    stressFreeArmAt_of_polarTiltUnsaturated hrank hpredecessor htilt,
    balancedArmAt_of_polarTiltUnsaturated hrank hpredecessor htilt,
    degenerateArmAt_of_polarTiltUnsaturated hrank hpredecessor htilt,
    balancedPartialSupportArmAt_of_polarTiltUnsaturated hrank hpredecessor htilt,
    degenerateHyperplaneCover_of_polarTiltUnsaturated hrank hpredecessor htilt⟩

/-! ### The deciding cell of rank three, and the calibration -/

/-- The hinge at the deciding cell of rank three. -/
theorem hingeHoldsAtSize_six_three_of_polarTiltUnsaturated
    (htilt : PolarTiltSelectionUnsaturated 6 3) : HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_polarTiltUnsaturated (by norm_num) gtz_rank_two htilt

/-- The three rank-three arms from the narrowed residual. -/
theorem thresholdArms_rank_three_of_polarTiltUnsaturated
    (htilt : PolarTiltSelectionUnsaturated 6 3) :
    ThresholdStressFreeArm 3 ∧ ThresholdBalancedArm 3 ∧ ThresholdDegenerateArm 3 :=
  ⟨thresholdStressFreeArm_of_polarTiltUnsaturated 3 (by norm_num) gtz_rank_two htilt,
    thresholdBalancedArm_of_polarTiltUnsaturated 3 (by norm_num) gtz_rank_two htilt,
    thresholdDegenerateArm_of_polarTiltUnsaturated 3 (by norm_num) gtz_rank_two htilt⟩

/-- **THE DECIDING CELL OF RANK THREE FROM THE NARROWED RESIDUAL ALONE.** -/
theorem gtzWeighted_six_three_of_polarTiltUnsaturated
    (htilt : PolarTiltSelectionUnsaturated 6 3) : GtzWeighted 6 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltUnsaturated htilt
  exact GeneralRankReach.gtzWeighted_six_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **ALL OF RANK THREE FROM THE NARROWED RESIDUAL ALONE.** -/
theorem gtzWeightedAll_three_of_polarTiltUnsaturated
    (htilt : PolarTiltSelectionUnsaturated 6 3) : GtzWeightedAll 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltUnsaturated htilt
  exact GeneralRankReach.gtzWeightedAll_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **THE NARROWED RESIDUAL IS FALSE AT `(5,3)`.**  The calibration transports,
because the budget facts the narrowing supplies are theorems at every tie.  Thus
the narrowing removes no content the window floor `2 * rank <= size` supplies. -/
theorem not_polarTiltSelectionUnsaturated_five_three :
    ¬ PolarTiltSelectionUnsaturated 5 3 :=
  fun htilt => not_hingeHoldsAtSize_five_three
    (hingeHoldsAtSize_of_polarTiltUnsaturated (by norm_num) gtz_rank_two htilt)

/-- **THE GUARDRAIL.**  The narrowed residual forbids only PRIMITIVE ties, thus
neither tie in the tree refutes it: the diamond refutes it only at `(5,3)`, where
the hinge itself is false, and the split diamond is not primitive. -/
theorem polarTiltUnsaturated_forbids_only_primitive_ties (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelectionUnsaturated size rank)
    (design : WeightedDesign size rank) (htie : IsTie design) : HasParallelPair design :=
  hingeHoldsAtSize_of_polarTiltUnsaturated hrank hpredecessor htilt design htie

/-- **THE DISCRIMINATOR, ON THE NARROWED RESIDUAL.**  The `(6,3)` tie in the tree
is not primitive, thus it separates the refuted last-stage Prop from the polar
residuals, narrowed one included. -/
theorem sixSplitDiamondDesign_spares_polarTiltUnsaturated :
    ¬ RankSuccShrinks 6 3 ∧ IsTie sixSplitDiamondDesign
      ∧ ¬ IsPrimitiveDesign sixSplitDiamondDesign
      ∧ ¬ PolarTiltSelectionUnsaturated 5 3 :=
  ⟨not_rankSuccShrinks_six_three, sixSplitDiamondDesign_isTie,
    not_isPrimitiveDesign_sixSplitDiamondDesign, not_polarTiltSelectionUnsaturated_five_three⟩

/-! ## Part 7: what the weight law says at named strata

The weight law is one inequality between four numbers, thus it reads as an
explicit leverage cap at every stratum where the weights are known.  At uniform
weights it improves the leverage cap of the design by almost one whole unit. -/

/-- **THE UNIFORM-WEIGHT TIE LEVERAGE CAP.**  Every design caps the leverage of
an atom by the inverse of that atom's weight, thus a uniform design caps it by
the size.  A TIE caps it by one unit less, up to the inverse of the size:

  `size * leverage <= size^2 - size + 1`.

At six labels of rank three this is `leverage <= 31/6`, against the design cap
`leverage <= 6`. -/
theorem uniformWeight_tie_leverage_bound (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    (htie : IsTie design) (huniform : ∀ c, design.weight c = ((size : ℝ))⁻¹)
    {pole : Fin size} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    (size : ℝ) * (design.atom pole ⬝ᵥ design.atom pole)
      ≤ (size : ℝ) ^ 2 - (size : ℝ) + 1 := by
  have hsize : 0 < size := lt_of_lt_of_le (by omega) (rank_le_of_design design)
  have hsizeCast : (0 : ℝ) < (size : ℝ) := by exact_mod_cast hsize
  have hsizeNe : (size : ℝ) ≠ 0 := ne_of_gt hsizeCast
  have hfloorPos : (0 : ℝ) < ((size : ℝ))⁻¹ := inv_pos.mpr hsizeCast
  have hlaw := tie_weightFloor_saturation_sharp hrank hpredecessor design htie hlong hfloorPos
    (fun c => le_of_eq (huniform c).symm)
  rw [huniform pole] at hlaw
  have hscaled := mul_le_mul_of_nonneg_right hlaw (le_of_lt (by positivity : (0 : ℝ)
    < (size : ℝ) ^ 2))
  have hleft : ((size : ℝ))⁻¹ * ((size : ℝ))⁻¹
      * (design.atom pole ⬝ᵥ design.atom pole - 1) * (size : ℝ) ^ 2
      = design.atom pole ⬝ᵥ design.atom pole - 1 := by
    field_simp
  have hright : (1 - ((size : ℝ))⁻¹)
      * (1 - ((size : ℝ))⁻¹ * (design.atom pole ⬝ᵥ design.atom pole)) * (size : ℝ) ^ 2
      = (size : ℝ) ^ 2 - (size : ℝ) - (size : ℝ) * (design.atom pole ⬝ᵥ design.atom pole)
        + (design.atom pole ⬝ᵥ design.atom pole) := by
    field_simp
    ring
  rw [hleft, hright] at hscaled
  linarith

/-- **THE UNIFORM-WEIGHT CRITERION.**  A uniform design with one atom above the
tie cap is not a tie. -/
theorem not_isTie_of_uniformWeight_long_atom (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    (huniform : ∀ c, design.weight c = ((size : ℝ))⁻¹)
    {pole : Fin size} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (habove : (size : ℝ) ^ 2 - (size : ℝ) + 1
      < (size : ℝ) * (design.atom pole ⬝ᵥ design.atom pole)) :
    ¬ IsTie design := by
  intro htie
  exact absurd (uniformWeight_tie_leverage_bound hrank hpredecessor design htie huniform hlong)
    (not_le.mpr habove)

/-- The uniform tie cap at rank three, with the previous rank discharged. -/
theorem uniformWeight_tie_leverage_bound_three (design : WeightedDesign size 3)
    (htie : IsTie design) (huniform : ∀ c, design.weight c = ((size : ℝ))⁻¹)
    {pole : Fin size} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    (size : ℝ) * (design.atom pole ⬝ᵥ design.atom pole)
      ≤ (size : ℝ) ^ 2 - (size : ℝ) + 1 :=
  uniformWeight_tie_leverage_bound (by norm_num) gtz_rank_two design htie huniform hlong

/-! ### The residual is a TWO-LABEL statement at rank three

At rank three the covering set has card two, thus the whole tilt residual reads
against exactly two labels.  Extracting them makes the shape of a certificate
explicit. -/

/-- **THE TWO TILTED LABELS OF A RANK-THREE TIE.**  A tie of rank three hands
back two distinct labels, neither of them the pole, whose squared pairings
against the pole already spend the whole budget of the share. -/
theorem exists_two_tilted_labels_of_isTie_three (design : WeightedDesign size 3)
    (htie : IsTie design) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {share : ℝ} (hshare : 0 < share) (hshareLt : share < design.weight pole) :
    ∃ first second : Fin size, first ≠ second ∧ first ≠ pole ∧ second ≠ pole
      ∧ (design.weight pole - share) / (1 - design.weight pole)
            * (design.atom pole ⬝ᵥ design.atom pole)
            * (design.atom pole ⬝ᵥ design.atom pole - 1)
          ≤ (design.atom first ⬝ᵥ design.atom pole) ^ 2
            + (design.atom second ⬝ᵥ design.atom pole) ^ 2 := by
  classical
  obtain ⟨covering, hcard, hnotMem, htilt⟩ :=
    exists_tilted_polarCover_of_share (rank := 3) (by norm_num) gtz_rank_two design htie hlong
      hshare hshareLt
  have hcardTwo : covering.card = 2 := by omega
  obtain ⟨first, second, hne, hpair⟩ := Finset.card_eq_two.mp hcardTwo
  subst hpair
  have hfirst : first ≠ pole := fun heq => hnotMem (by rw [← heq]; exact Finset.mem_insert_self _ _)
  have hsecond : second ≠ pole := fun heq => hnotMem (by
    rw [← heq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine ⟨first, second, hne, hfirst, hsecond, ?_⟩
  rwa [Finset.sum_pair hne] at htilt

/-- **THE TWO LABELS ARE ALSO PRICED BY THE TILT MASS.**  The same pair obeys the
weight floor bound of part 1, thus a rank-three tie is caught between two
inequalities about exactly two of its labels. -/
theorem two_label_tilt_mass_bound (design : WeightedDesign size rank) (pole : Fin size)
    {first second : Fin size} (hne : first ≠ second)
    (hfirst : first ≠ pole) (hsecond : second ≠ pole)
    {weightFloor : ℝ} (hfloor : ∀ c, weightFloor ≤ design.weight c) :
    weightFloor * ((design.atom first ⬝ᵥ design.atom pole) ^ 2
        + (design.atom second ⬝ᵥ design.atom pole) ^ 2)
      ≤ (design.atom pole ⬝ᵥ design.atom pole)
        * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole)) := by
  classical
  have hnotMem : pole ∉ ({first, second} : Finset (Fin size)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (heq | heq)
    · exact hfirst heq.symm
    · exact hsecond heq.symm
  have hstep := weightFloor_mul_polarTilt_le design pole hnotMem hfloor
  rwa [Finset.sum_pair hne] at hstep

/-! ### The coupling residual, narrowed by the same free facts -/

/-- **THE NARROWED COUPLING RESIDUAL.**  `Gtz.PolarCouplingSelection` with the
free budget facts of a tie handed to it. -/
def PolarCouplingSelectionUnsaturated (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (pole : Fin size) (covering : Finset (Fin size))
      (margin : ℝ),
    IsPrimitiveDesign design →
    IsTie design →
    1 < design.atom pole ⬝ᵥ design.atom pole →
    PolarSaturationBudget design pole →
    0 < margin →
    covering.card = rank - 1 → pole ∉ covering →
    (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) →
    ∃ (selected : Finset (Fin size)) (couplingBound : ℝ),
      selected.card = rank - 1 ∧ pole ∉ selected
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2)
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (∑ label ∈ selected,
              (design.atom label ⬝ᵥ probe) * (design.atom label ⬝ᵥ design.atom pole)) ^ 2
            ≤ couplingBound * (probe ⬝ᵥ probe))
      ∧ couplingBound < margin * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)

/-- The narrowed coupling residual is weaker than the shipped one. -/
theorem polarCouplingSelectionUnsaturated_of_polarCouplingSelection
    (hcoupling : PolarCouplingSelection size rank) :
    PolarCouplingSelectionUnsaturated size rank :=
  fun design pole covering margin hprimitive htie hlong _hbudget hmargin hcard hnotMem hcover =>
    hcoupling design pole covering margin hprimitive htie hlong hmargin hcard hnotMem hcover

/-- **THE HINGE FROM THE NARROWED COUPLING RESIDUAL.** -/
theorem hingeHoldsAtSize_of_polarCouplingUnsaturated (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (hcoupling : PolarCouplingSelectionUnsaturated size rank) : HingeHoldsAtSize size rank := by
  classical
  intro design htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  obtain ⟨pole, hlong⟩ := exists_overshooting_atom design hrank
  obtain ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin hrank hpredecessor design hlong
  obtain ⟨selected, couplingBound, hselCard, hselNotMem, hselCover, hselCoupling, hselBound⟩ :=
    hcoupling design pole covering margin hprimitive htie hlong
      (polarSaturationBudget_of_isTie hrank hpredecessor design htie hlong)
      hmarginPos hcard hnotMem hcover
  have hposDef := posDef_insert_of_polarCoupling design hselNotMem hlong hmarginPos hselCover
    hselCoupling hselBound
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hselNotMem, hselCard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-- The deciding cell of rank three from the narrowed coupling residual. -/
theorem gtzWeighted_six_three_of_polarCouplingUnsaturated
    (hcoupling : PolarCouplingSelectionUnsaturated 6 3) : GtzWeighted 6 3 := by
  have hhinge := hingeHoldsAtSize_of_polarCouplingUnsaturated (rank := 3) (size := 6)
    (by norm_num) gtz_rank_two hcoupling
  exact GeneralRankReach.gtzWeighted_six_three_of_arms
    (fun design _hfree htie => hhinge design htie)
    (fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie => hhinge design htie)
    (fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
      hhinge design htie)

/-- The narrowed coupling residual is calibrated at the cell of size five. -/
theorem not_polarCouplingSelectionUnsaturated_five_three :
    ¬ PolarCouplingSelectionUnsaturated 5 3 :=
  fun hcoupling => not_hingeHoldsAtSize_five_three
    (hingeHoldsAtSize_of_polarCouplingUnsaturated (by norm_num) gtz_rank_two hcoupling)

/-- **THE LEDGER OF A RANK-THREE TIE, IN ONE STATEMENT.**  At every overshooting
atom of every rank-three tie: the leverage cap is strict, the weight law holds
against every weight floor, and two named labels carry the whole budget. -/
theorem sixThree_tie_polar_ledger (design : WeightedDesign 6 3) (htie : IsTie design)
    {pole : Fin 6} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {weightFloor : ℝ} (hfloorPos : 0 < weightFloor)
    (hfloor : ∀ c, weightFloor ≤ design.weight c) :
    design.weight pole * (design.atom pole ⬝ᵥ design.atom pole) < 1
      ∧ weightFloor * design.weight pole * (design.atom pole ⬝ᵥ design.atom pole - 1)
          ≤ (1 - design.weight pole)
            * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole))
      ∧ ∃ first second : Fin 6, first ≠ second ∧ first ≠ pole ∧ second ≠ pole
          ∧ (design.weight pole / 2) / (1 - design.weight pole)
                * (design.atom pole ⬝ᵥ design.atom pole)
                * (design.atom pole ⬝ᵥ design.atom pole - 1)
              ≤ (design.atom first ⬝ᵥ design.atom pole) ^ 2
                + (design.atom second ⬝ᵥ design.atom pole) ^ 2 := by
  have hweightPos := design.weight_pos pole
  refine ⟨tie_weight_mul_leverage_lt_one (by norm_num) gtz_rank_two design htie hlong,
    tie_weightFloor_saturation_three design htie hlong hfloorPos hfloor, ?_⟩
  obtain ⟨first, second, hne, hfirst, hsecond, hbudget⟩ :=
    exists_two_tilted_labels_of_isTie_three design htie hlong
      (share := design.weight pole / 2) (by linarith) (by linarith)
  refine ⟨first, second, hne, hfirst, hsecond, ?_⟩
  have hrewrite : design.weight pole - design.weight pole / 2 = design.weight pole / 2 := by ring
  rwa [hrewrite] at hbudget

end Gtz
