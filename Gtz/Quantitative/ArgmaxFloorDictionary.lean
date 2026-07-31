/-
# The argmax / floor dictionary

`Gtz.GtzWeightedFloor m k level` asks that every weighted design admit a `k`-subset
whose subset sum dominates `level . 1`.  `Gtz.IsArgmaxDominated D value` says that at
every `k`-subset some unit probe reads a quadratic form at most `value`.  This file
proves the two are the SAME statement once the design is universally quantified, and
reads the consequences off in both directions.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `le_value_of_gtzWeightedFloor_of_isArgmaxDominated` -- any proved floor is a lower
  bound on argmax-dominated values.  Strictly generalises the shipped
  `Gtz.one_le_value_of_isArgmaxDominated`, which is the case `level = 1`.
* `gtzWeightedFloor_of_forall_le_value_of_isArgmaxDominated` -- the converse, by
  normalising a bad direction at each `k`-subset and taking the supremum over the
  finitely many subsets.
* `gtzWeightedFloor_iff_forall_le_value_of_isArgmaxDominated` -- the dictionary.
* `gtzWeighted_iff_gtzWeightedFloor_one` -- the unit level of the floor is exactly
  `Gtz.GtzWeighted`.  The per-subset halves of this are the shipped
  `Gtz.dominatesAtLevel_one_iff_dominates` and
  `Gtz.gtzWeightedFloor_iff_dominatesAtLevel` (both in `Gtz/Reduction/SplitTransfer.lean`);
  what is new here is the `forall`/`exists` lift across designs, proved directly so
  that this file need not import that 2000-line module.
* `gtzWeighted_iff_forall_one_le_value_of_isArgmaxDominated` -- **THE NO-GO.**  Deleting
  the `GtzWeighted` premise from `Gtz.one_le_value_of_isArgmaxDominated` and quantifying
  over designs yields a statement EQUIVALENT to `GtzWeighted m k` itself.
* `inv_rank_le_value_of_isArgmaxDominated`, `inv_rank_lt_value_of_isArgmaxDominated`,
  `inv_three_lt_value_of_isArgmaxDominated_sevenThree` -- the best UNCONDITIONAL
  replacements for the deleted premise, from the shipped `Gtz.gtzWeightedFloor_inv_rank`.
* `three_fifths_le_value_of_isArgmaxDominated_sixThree` and
  `two_thirds_le_value_of_isArgmaxDominated_sevenThree` -- the dictionary applied to the
  two landed deflation floors of `Gtz/Reduction/AllHeavyMinimiser.lean`.

## SCOPE CAVEAT -- what the no-go does NOT say

The equivalence is **argmax-only**.  Adding the stationarity bundle to the hypotheses
STRENGTHENS them and therefore WEAKENS the resulting statement, so nothing here shows
that "bundle and argmax and `value < 1`" is equivalent to GTZ.  The no-go closes exactly
one route -- deleting the premise from the argmax-only theorem -- and leaves the bundled
interior lane open.  Read: the bundle must carry the whole interval `(1/3, 1]`, because
`inv_three_lt_value_of_isArgmaxDominated_sevenThree` is everything the argmax datum alone
gives at the frontier cell.

## NOT PROVED here

No new bound on `GtzWeighted 6 3` or `GtzWeighted 7 3`.  The strictness in
`inv_rank_lt_value_of_isArgmaxDominated` is PER DESIGN and does not improve the uniform
`Gtz.gtzWeightedFloor_inv_rank`, because the selected weight is not bounded away from zero
across designs; in particular it does not move the bracket of
`Gtz.gtzWeightedFloor_rankThree_bracket`.

Provenance: workflow scratch `/tmp/gtz-wf/interior-crux/probe.lean` (report 18), landed
with `push_neg` rewritten to the house `push Not` and with the two deflation-floor
corollaries added.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Reduction.LiftingLemma
import Gtz.Reduction.ExchangeInvariant
import Gtz.Reduction.RealVolumeFloor
import Gtz.Reduction.AllHeavyMinimiser
import Gtz.Quantitative.InteriorExclusion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The two halves of the dictionary -/

/-- **The forward half, with the premise weakened from GTZ to ANY proved floor.**
Strictly generalises `Gtz.one_le_value_of_isArgmaxDominated`, which is the case
`level = 1`. -/
theorem le_value_of_gtzWeightedFloor_of_isArgmaxDominated {m k : ℕ} {D : WeightedDesign m k}
    {value level : ℝ} (hfloor : GtzWeightedFloor m k level)
    (hargmax : IsArgmaxDominated D value) :
    level ≤ value := by
  obtain ⟨chosenSubset, hcard, hpsd⟩ := hfloor D
  obtain ⟨probe, hunitProbe, hquotientLe⟩ := hargmax chosenSubset hcard
  have hcover := (hasLeastEigenvalueAtLeast_iff D chosenSubset level).mp hpsd probe
  rw [hunitProbe, mul_one] at hcover
  rw [subsetSum_form_eq_sum_sq] at hquotientLe
  linarith

/-- **The converse: an unconditional floor on argmax values IS the floor itself.**
Given a bad direction at every `k`-subset, normalise it and take the maximum over
the finitely many subsets; that maximum is an argmax-dominated value below the
level. -/
theorem gtzWeightedFloor_of_forall_le_value_of_isArgmaxDominated {m k : ℕ} (hrankLe : k ≤ m)
    {level : ℝ}
    (hvalue : ∀ (D : WeightedDesign m k) (value : ℝ), IsArgmaxDominated D value → level ≤ value) :
    GtzWeightedFloor m k level := by
  classical
  intro D
  by_contra hnone
  push Not at hnone
  have hbadProbe : ∀ chosenSubset : Finset (Fin m), ∃ probe : Fin k → ℝ,
      chosenSubset.card = k →
        probe ⬝ᵥ probe = 1 ∧ probe ⬝ᵥ (subsetSum D chosenSubset *ᵥ probe) < level := by
    intro chosenSubset
    by_cases hcard : chosenSubset.card = k
    · have hexistsBad : ∃ direction : Fin k → ℝ,
          ∑ atomLabel ∈ chosenSubset, (D.atom atomLabel ⬝ᵥ direction) ^ 2
            < level * (direction ⬝ᵥ direction) := by
        by_contra hallCover
        push Not at hallCover
        exact hnone chosenSubset hcard
          ((hasLeastEigenvalueAtLeast_iff D chosenSubset level).mpr hallCover)
      obtain ⟨direction, hbad⟩ := hexistsBad
      have hsumNonneg : (0 : ℝ)
          ≤ ∑ atomLabel ∈ chosenSubset, (D.atom atomLabel ⬝ᵥ direction) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hnormPos : 0 < direction ⬝ᵥ direction := by
        rcases (dotProduct_self_nonneg direction).lt_or_eq with hpositive | hzero
        · exact hpositive
        · rw [← hzero, mul_zero] at hbad
          linarith
      have hrootPos : 0 < Real.sqrt (direction ⬝ᵥ direction) := Real.sqrt_pos.mpr hnormPos
      have hrootSq : Real.sqrt (direction ⬝ᵥ direction) * Real.sqrt (direction ⬝ᵥ direction)
          = direction ⬝ᵥ direction := Real.mul_self_sqrt hnormPos.le
      refine ⟨(Real.sqrt (direction ⬝ᵥ direction))⁻¹ • direction, fun _ => ⟨?_, ?_⟩⟩
      · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
          ← mul_inv, hrootSq, inv_mul_cancel₀ (ne_of_gt hnormPos)]
      · rw [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          ← mul_assoc, ← mul_inv, hrootSq, subsetSum_form_eq_sum_sq,
          inv_mul_lt_iff₀ hnormPos]
        linarith
    · exact ⟨0, fun hcontradiction => absurd hcontradiction hcard⟩
  choose probeOf hprobeOf using hbadProbe
  have hfamilyNonempty : ((Finset.univ : Finset (Fin m)).powersetCard k).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by simpa using hrankLe)
  have hexistsArgmax : ∃ topValue : ℝ, IsArgmaxDominated D topValue ∧ topValue < level := by
    refine ⟨Finset.sup' ((Finset.univ : Finset (Fin m)).powersetCard k) hfamilyNonempty
      (fun chosenSubset =>
        probeOf chosenSubset ⬝ᵥ (subsetSum D chosenSubset *ᵥ probeOf chosenSubset)), ?_, ?_⟩
    · intro chosenSubset hcard
      exact ⟨probeOf chosenSubset, (hprobeOf chosenSubset hcard).1,
        Finset.le_sup'
          (fun otherSubset : Finset (Fin m) =>
            probeOf otherSubset ⬝ᵥ (subsetSum D otherSubset *ᵥ probeOf otherSubset))
          (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩)⟩
    · rw [Finset.sup'_lt_iff]
      exact fun chosenSubset hmem =>
        (hprobeOf chosenSubset (Finset.mem_powersetCard.mp hmem).2).2
  obtain ⟨argmaxValue, hisArgmax, hbelowLevel⟩ := hexistsArgmax
  exact absurd (hvalue D argmaxValue hisArgmax) (not_le.mpr hbelowLevel)

/-- **THE DICTIONARY.**  For `k ≤ m` the floor statement and the unconditional
lower bound on argmax-dominated values are the SAME statement. -/
theorem gtzWeightedFloor_iff_forall_le_value_of_isArgmaxDominated {m k : ℕ} (hrankLe : k ≤ m)
    (level : ℝ) :
    GtzWeightedFloor m k level
      ↔ ∀ (D : WeightedDesign m k) (value : ℝ), IsArgmaxDominated D value → level ≤ value :=
  ⟨fun hfloor _ _ hargmax => le_value_of_gtzWeightedFloor_of_isArgmaxDominated hfloor hargmax,
    gtzWeightedFloor_of_forall_le_value_of_isArgmaxDominated hrankLe⟩

/-! ## The unit level, and the no-go it produces -/

/-- The unit level of the floor is exactly `Gtz.GtzWeighted`.  The per-subset halves of
this equivalence are the shipped `Gtz.dominatesAtLevel_one_iff_dominates` and
`Gtz.gtzWeightedFloor_iff_dominatesAtLevel`; this is the `forall`/`exists` lift across
designs, proved here by hand rather than by importing `Gtz.Reduction.SplitTransfer`. -/
theorem gtzWeighted_iff_gtzWeightedFloor_one (m k : ℕ) :
    GtzWeighted m k ↔ GtzWeightedFloor m k 1 := by
  have hscalar : ((1 : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ)) = 1 := one_smul _ _
  constructor
  · intro hgtz D
    obtain ⟨chosenSubset, hcard, hdominates⟩ := hgtz D
    exact ⟨chosenSubset, hcard, by rw [hscalar]; exact hdominates⟩
  · intro hfloor D
    obtain ⟨chosenSubset, hcard, hpsd⟩ := hfloor D
    rw [hscalar] at hpsd
    exact ⟨chosenSubset, hcard, hpsd⟩

/-- **THE PREMISE IS NOT REMOVABLE.**  Dropping `hgtz` from
`Gtz.one_le_value_of_isArgmaxDominated` and quantifying over designs gives a
statement EQUIVALENT to `GtzWeighted m k` itself, at every size with `k ≤ m`.

This promotes to a theorem what `Gtz/Quantitative/InteriorExclusion.lean` states twice in
prose: the obligation with the argmax attached is the interior case of GTZ itself, and is
not a lemma standing in front of it.  See the SCOPE CAVEAT in this file's header -- the
equivalence is argmax-only and says nothing about the bundled interior lane. -/
theorem gtzWeighted_iff_forall_one_le_value_of_isArgmaxDominated {m k : ℕ} (hrankLe : k ≤ m) :
    GtzWeighted m k
      ↔ ∀ (D : WeightedDesign m k) (value : ℝ), IsArgmaxDominated D value → 1 ≤ value := by
  rw [gtzWeighted_iff_gtzWeightedFloor_one]
  exact gtzWeightedFloor_iff_forall_le_value_of_isArgmaxDominated hrankLe 1

/-- **THE PREMISE IS NOT REMOVABLE AT THE FRONTIER CELL `(7,3)`.** -/
theorem gtzWeighted_sevenThree_iff_forall_one_le_value_of_isArgmaxDominated :
    GtzWeighted 7 3
      ↔ ∀ (D : WeightedDesign 7 3) (value : ℝ), IsArgmaxDominated D value → 1 ≤ value :=
  gtzWeighted_iff_forall_one_le_value_of_isArgmaxDominated (by norm_num)

/-! ## What the dictionary yields unconditionally -/

/-- **The best UNCONDITIONAL replacement**: the shipped rank floor, read on the
argmax side.  No `GtzWeighted`, no stationarity bundle. -/
theorem inv_rank_le_value_of_isArgmaxDominated {m k : ℕ} {D : WeightedDesign m k} {value : ℝ}
    (hargmax : IsArgmaxDominated D value) :
    ((k : ℝ))⁻¹ ≤ value :=
  le_value_of_gtzWeightedFloor_of_isArgmaxDominated (gtzWeightedFloor_inv_rank m k) hargmax

/-- **The weight-aware unconditional bound.**  Some `k`-subset -- the maximal-volume
pick of `Gtz.exists_selection_posSemidef_sub_selectedWeight_level` -- has
`1 ≤ value * (k - (k-1) * t(C))`, i.e. its total weight is at most
`(k - 1/value)/(k-1)`. -/
theorem exists_selection_one_le_value_mul_selectedLevel_of_isArgmaxDominated {m k : ℕ}
    {D : WeightedDesign m k} {value : ℝ} (hrankPos : 0 < k)
    (hargmax : IsArgmaxDominated D value) :
    ∃ chosenSubset : Finset (Fin m), chosenSubset.card = k ∧
      1 ≤ value * ((k : ℝ) - ((k : ℝ) - 1) * ∑ atomLabel ∈ chosenSubset, D.weight atomLabel) := by
  obtain ⟨chosenSubset, hcard, hpsd⟩ := exists_selection_posSemidef_sub_selectedWeight_level D
  obtain ⟨probe, hunitProbe, hquotientLe⟩ := hargmax chosenSubset hcard
  have hcover := (hasLeastEigenvalueAtLeast_iff D chosenSubset
    (((k : ℝ) - ((k : ℝ) - 1) * ∑ atomLabel ∈ chosenSubset, D.weight atomLabel)⁻¹)).mp hpsd probe
  rw [hunitProbe, mul_one] at hcover
  rw [subsetSum_form_eq_sum_sq] at hquotientLe
  have hrankOneLe : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrankPos
  have hweightLe := sum_weight_subset_le_one D chosenSubset
  have hweightNonneg : 0 ≤ ∑ atomLabel ∈ chosenSubset, D.weight atomLabel :=
    Finset.sum_nonneg fun _ _ => (D.weight_pos _).le
  have hlevelPos : 0 < (k : ℝ) - ((k : ℝ) - 1) * ∑ atomLabel ∈ chosenSubset, D.weight atomLabel := by
    nlinarith [hrankOneLe, hweightLe, hweightNonneg]
  refine ⟨chosenSubset, hcard, ?_⟩
  have hvalueGe : (((k : ℝ) - ((k : ℝ) - 1)
      * ∑ atomLabel ∈ chosenSubset, D.weight atomLabel))⁻¹ ≤ value := by linarith
  calc (1 : ℝ)
      = (((k : ℝ) - ((k : ℝ) - 1) * ∑ atomLabel ∈ chosenSubset, D.weight atomLabel))⁻¹
          * ((k : ℝ) - ((k : ℝ) - 1) * ∑ atomLabel ∈ chosenSubset, D.weight atomLabel) := by
        rw [inv_mul_cancel₀ (ne_of_gt hlevelPos)]
    _ ≤ value * ((k : ℝ) - ((k : ℝ) - 1)
          * ∑ atomLabel ∈ chosenSubset, D.weight atomLabel) :=
        mul_le_mul_of_nonneg_right hvalueGe hlevelPos.le

/-- **The rank floor is STRICT on argmax values, at every rank at least two.**
The maximal-volume subset carries strictly positive weight, so its level is
strictly above `1/k`.  Note this is per DESIGN: it does NOT improve the uniform
floor `Gtz.gtzWeightedFloor_inv_rank`, because the selected weight is not bounded
away from zero over all designs. -/
theorem inv_rank_lt_value_of_isArgmaxDominated {m k : ℕ} {D : WeightedDesign m k} {value : ℝ}
    (hrankTwo : 2 ≤ k) (hargmax : IsArgmaxDominated D value) :
    ((k : ℝ))⁻¹ < value := by
  obtain ⟨chosenSubset, hcard, hbound⟩ :=
    exists_selection_one_le_value_mul_selectedLevel_of_isArgmaxDominated (by omega) hargmax
  have hrankTwoLe : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrankTwo
  have hcardPos : 0 < chosenSubset.card := by omega
  have hweightPos : 0 < ∑ atomLabel ∈ chosenSubset, D.weight atomLabel :=
    Finset.sum_pos (fun atomLabel _ => D.weight_pos atomLabel)
      (Finset.card_pos.mp hcardPos)
  have hweightLe := sum_weight_subset_le_one D chosenSubset
  have hlevelPos : 0 < (k : ℝ) - ((k : ℝ) - 1) * ∑ atomLabel ∈ chosenSubset, D.weight atomLabel := by
    nlinarith
  have hlevelLt : (k : ℝ) - ((k : ℝ) - 1) * ∑ atomLabel ∈ chosenSubset, D.weight atomLabel
      < (k : ℝ) := by nlinarith
  have hrankPos : (0 : ℝ) < (k : ℝ) := by linarith
  have hvaluePos : 0 < value := by nlinarith
  have hstrict : 1 < value * (k : ℝ) := by nlinarith
  have hinvMul : ((k : ℝ))⁻¹ * (k : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hrankPos)
  by_contra hnotLess
  push Not at hnotLess
  have hscaled : value * (k : ℝ) ≤ ((k : ℝ))⁻¹ * (k : ℝ) :=
    mul_le_mul_of_nonneg_right hnotLess hrankPos.le
  rw [hinvMul] at hscaled
  linarith

/-- **At the frontier cell the unconditional bound is exactly one third**, strictly.
The gap to the target `1 ≤ value` is the full factor three that
`Gtz.gtzWeightedFloor_rankThree_bracket` records as the whole content of the
problem. -/
theorem inv_three_lt_value_of_isArgmaxDominated_sevenThree {D : WeightedDesign 7 3} {value : ℝ}
    (hargmax : IsArgmaxDominated D value) :
    (3 : ℝ)⁻¹ < value := by
  have hbound := inv_rank_lt_value_of_isArgmaxDominated (k := 3) (by norm_num) hargmax
  norm_num at hbound ⊢
  linarith

/-! ## The dictionary against the two landed deflation floors -/

/-- **AT `(6,3)` EVERY ARGMAX-DOMINATED VALUE IS AT LEAST `3/5`, UNCONDITIONALLY.**
The dictionary applied to `Gtz.gtzWeightedFloor_six_three_three_fifths`.  This is the
sharpest unconditional argmax bound available at the smaller cell -- strictly better than
the `1/3` of `inv_rank_le_value_of_isArgmaxDominated`, and with no open premise. -/
theorem three_fifths_le_value_of_isArgmaxDominated_sixThree {D : WeightedDesign 6 3} {value : ℝ}
    (hargmax : IsArgmaxDominated D value) :
    (3 : ℝ) / 5 ≤ value :=
  le_value_of_gtzWeightedFloor_of_isArgmaxDominated gtzWeightedFloor_six_three_three_fifths hargmax

/-- **AT `(7,3)` THE ARGMAX FLOOR IS `2/3`, granted the open `Gtz.GtzWeighted 6 3`.**
The dictionary applied to `Gtz.gtzWeightedFloor_seven_three_two_thirds`.  Unlike the
`(6,3)` sibling above this carries the open premise, which is exactly why the
unconditional `inv_three_lt_value_of_isArgmaxDominated_sevenThree` remains the operative
bound at the frontier cell. -/
theorem two_thirds_le_value_of_isArgmaxDominated_sevenThree {D : WeightedDesign 7 3} {value : ℝ}
    (hsixThree : GtzWeighted 6 3) (hargmax : IsArgmaxDominated D value) :
    (2 : ℝ) / 3 ≤ value :=
  le_value_of_gtzWeightedFloor_of_isArgmaxDominated
    (gtzWeightedFloor_seven_three_two_thirds hsixThree) hargmax

end Gtz
