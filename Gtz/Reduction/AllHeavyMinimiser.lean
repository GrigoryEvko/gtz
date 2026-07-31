/-
# The all-heavy minimising counterexample, the deflation floors, and the lane's ceiling

A failure of weighted GTZ is not merely realised somewhere in the design space: given
the two rungs one size down it is realised at a design that is simultaneously a genuine
`Gtz.WeightedDesign`, `Gtz.AllHeavy`, and a GLOBAL MINIMISER of `Gtz.chartObjective` over
the whole closed chart domain.  Both boundaries of the all-heavy region are paid for.
The vanishing-weight face is discharged by `Gtz.ChartAttainment`'s interiority clause;
the leverage-one face is discharged here, and costs nothing beyond the smaller rung,
because at a counterexample even WEAK domination is already a contradiction -- which is
exactly why `Gtz.allHeavy_or_exists_leverage_eq_one_of_isTie` has to remain a dichotomy
at a tie, where weak domination is present, and does not have to remain one here.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

1. **The certificate.**  `exists_posSemidef_sub_of_atomShare_le`: deflation at any atom
   whose share is small enough pays for domination at a chosen level, under the
   share-only division-free hypothesis `s_d <= 1 - value (1 - t_d)`.  At `value = 1` the
   hypothesis reads `s_d <= t_d` and the statement is the shipped
   `Gtz.dominating_of_light_atom`; the content is that the same transport, read as a
   LEVEL rather than a sign, keeps working for heavier atoms.  Its sharp form
   `deflationLevel_le_lambdaMinMat_subsetSum` names the exact level an atom can buy.

2. **The universal share floor.**  `lt_atomShare_of_forall_not_posSemidef`: at a design
   that fails at a level, EVERY atom's share is bounded below.  Every share statement the
   campaign had reached was existential (`Gtz.exists_atomShare_le_rank_div_size`,
   `Gtz.exists_weight_le_sizeInv`); this is the universal companion, and the existential
   ones follow from it by summation.  Two corollaries: at `value = 1` it is
   ALL-HEAVINESS with an explicit rate, and summed over the atoms it is the size-aware
   floor `GtzWeightedFloor (m+1) k (1 - (k-1)/m)`, hence `3/5` at `(6,3)` UNCONDITIONALLY
   and `2/3` at `(7,3)` granted the open cell.  Before this file the only shipped floor
   was the size-free `Gtz.gtzWeightedFloor_inv_rank` at `1/k`.

3. **The ceiling.**  `deflationLevel_lt_one_iff_one_lt_leverage` is an exact equivalence
   with no estimate in it: the level is below one precisely when the atom is heavy.  So
   on the all-heavy class, which is where the frontier lives, the deflation lane is
   structurally incapable of certifying domination, and `deflationLevel_eq_of_uniform`
   shows the mediant `1 - (k-1)/m` is ATTAINED simultaneously at every atom on the
   equal-share stratum -- the floor is the lane's exact ceiling, not a lossy estimate.
   `one_lt_level_of_dustBudget` closes the branch that was built to consume floors.

4. **The minimiser and the residue.**  `exists_allHeavy_minimiser_of_not_gtzWeighted`,
   unconditional at `(6,3)` because both smaller rungs are the shipped
   `Gtz.gtzWeighted_of_le_five`; and `gtzWeightedHeavyMinimal_iff_gtzWeighted`, which
   records that adding the minimality clause is NOT a logical discount -- the residue is
   EQUIVALENT to the cell.  Minimality is extra usable structure for a prover, and this
   file pins that distinction in the kernel so the residue is not later misread.

## NOT PROVED here

No cell is closed.  `Gtz.GtzWeighted 6 3` remains open and every `(7,3)` statement below
carries it as a hypothesis.  The design-side stationarity bundle
`Gtz.IsQuadricStationaryData` is still never derived from minimality anywhere; only the
CHART-side bundle is (see `Gtz.Reduction.ChartAttainmentWeld`), and the two objectives
are related by the non-uniform congruence `diagonal (sqrt t_C)`, so a minimiser of one is
not a minimiser of the other -- `Gtz.Reduction.CompactnessReduction` records that
mismatch.  Whether the supremum of the deflation level over the all-heavy class is
actually one is not claimed.

## Provenance

Two scratch files of the July 2026 attainment run, merged because they are one subject
and independently proved five of the same facts.  Where they collided the stronger
version is the one landed: the share-summation floor rather than the atom-selection
floor (no rank hypothesis, no atom chosen); the hypothesis-free all-heaviness rather than
the version carrying a redundant weak-heaviness assumption; the two-way
`gtzWeightedHeavyMinimal_iff_gtzWeighted` rather than the one-directional weakening.
Dropped as already shipped: an `allHeavy_of_uniform` duplicating
`Gtz.IsEqualShare.allHeavy`, and a cheap-atom pigeonhole whose only consumer was the
superseded floor proof.
-/
import Mathlib
import Gtz.Design.StratumEmptinessLedger
import Gtz.Quantitative.HollowInvolution
import Gtz.Reduction.BranchTransferConstants
import Gtz.Reduction.ChartAttainment
import Gtz.Reduction.ChartPointFactorisation
import Gtz.Reduction.Deflation
import Gtz.Reduction.RankFourWindow
import Gtz.Reduction.RealVolumeFloor
import Gtz.Reduction.Reductions
import Gtz.Ties.SevenThreeTieLocus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}
variable {size rank : ℕ}

/-! ## The certificate: deflation as a level, not a sign -/

/-- **DEFLATION PAYS FOR ANY LEVEL THE ATOM'S SHARE CAN AFFORD.**

Given weighted GTZ one size down, deflating at an atom `d` whose share obeys
`s_d <= 1 - value (1 - t_d)` produces a `k`-subset dominating `value . I`.

At `value = 1` the hypothesis reads `s_d <= t_d`, i.e. leverage at most one, and the
statement is the shipped `Gtz.dominating_of_light_atom`, which this therefore strictly
generalises.  The content is that the SAME transport
(`Gtz.exists_deflatedGapBound`), read as a level rather than a sign, keeps working for
heavier atoms -- it just certifies less.  No side condition on saturation: the saturated
case `s_d = 1` forces `value <= 0` and is discharged by positive semidefiniteness of the
subset sum. -/
theorem exists_posSemidef_sub_of_atomShare_le (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (hsmaller : GtzWeighted m k) {value : ℝ} (dropLabel : Fin (m + 1))
    (hcheap : atomShare D dropLabel ≤ 1 - value * (1 - D.weight dropLabel)) :
    ∃ selected : Finset (Fin (m + 1)), selected.card = k ∧
      (subsetSum D selected - value • 1).PosSemidef := by
  classical
  have hweightPos := D.weight_pos dropLabel
  have hweightLtOne : D.weight dropLabel < 1 := weight_lt_one D (by omega) dropLabel
  have hsurviving : (0 : ℝ) < 1 - D.weight dropLabel := by linarith
  have hcheapExp : D.weight dropLabel * leverageOf (D.atom dropLabel)
      ≤ 1 - value * (1 - D.weight dropLabel) := hcheap
  by_cases hshare : D.weight dropLabel * leverageOf (D.atom dropLabel) < 1
  · obtain ⟨selected, hcard, _, hbound⟩ :=
      exists_deflatedGapBound D hsize hsmaller dropLabel hshare
    refine ⟨selected, hcard, ?_⟩
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq ?_, fun probe => ?_⟩
    · rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, subsetSum_transpose]
    · have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hbound).2 probe
      rw [star_trivial] at hform ⊢
      have hexpand : probe ⬝ᵥ (((((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1))
            - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))) *ᵥ probe)
          = ((1 : ℝ) - D.weight dropLabel)
              * (probe ⬝ᵥ (subsetSum D selected *ᵥ probe) - probe ⬝ᵥ probe)
            - D.weight dropLabel * (probe ⬝ᵥ probe - (D.atom dropLabel ⬝ᵥ probe) ^ 2) := by
        rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.smul_mulVec,
          dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, Matrix.sub_mulVec,
          Matrix.sub_mulVec, dotProduct_sub, dotProduct_sub, Matrix.one_mulVec,
          dotProduct_atomMatrix_mulVec]
      rw [hexpand] at hform
      have hcauchy : (D.atom dropLabel ⬝ᵥ probe) ^ 2
          ≤ leverageOf (D.atom dropLabel) * (probe ⬝ᵥ probe) := by
        have hraw := dotProduct_sq_le_mul (D.atom dropLabel) probe
        rwa [show D.atom dropLabel ⬝ᵥ D.atom dropLabel = leverageOf (D.atom dropLabel) from
          dotProduct_self_eq_sum_sq _] at hraw
      have hgoal : probe ⬝ᵥ ((subsetSum D selected - value • 1) *ᵥ probe)
          = probe ⬝ᵥ (subsetSum D selected *ᵥ probe) - value * (probe ⬝ᵥ probe) := by
        rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
          dotProduct_smul, smul_eq_mul]
      rw [hgoal, sub_nonneg]
      nlinarith [hform, hcauchy, hweightPos, hsurviving, dotProduct_self_nonneg probe,
        mul_le_mul_of_nonneg_left hcauchy hweightPos.le,
        mul_le_mul_of_nonneg_right hcheapExp (dotProduct_self_nonneg probe)]
  · have hsaturated : D.weight dropLabel * leverageOf (D.atom dropLabel) = 1 :=
      le_antisymm (weighted_leverage_le_one D dropLabel) (not_lt.mp hshare)
    have hvalueNonpos : value ≤ 0 := by nlinarith [hcheapExp, hsurviving]
    obtain ⟨selected, _, hcard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin (m + 1)))) (n := k)
        (by simpa using rank_le_of_design D)
    refine ⟨selected, hcard, ?_⟩
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq ?_, fun probe => ?_⟩
    · rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, subsetSum_transpose]
    · rw [star_trivial]
      have hbase :=
        (Matrix.posSemidef_iff_dotProduct_mulVec.mp (posSemidef_subsetSum D selected)).2 probe
      rw [star_trivial] at hbase
      have hgoal : probe ⬝ᵥ ((subsetSum D selected - value • 1) *ᵥ probe)
          = probe ⬝ᵥ (subsetSum D selected *ᵥ probe) - value * (probe ⬝ᵥ probe) := by
        rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
          dotProduct_smul, smul_eq_mul]
      rw [hgoal]
      nlinarith [hbase, hvalueNonpos, dotProduct_self_nonneg probe]

/-- The level that deflation at an atom certifies: the atom's remaining share divided by
the mass that survives its deletion.

This ratio is the transfer factor the header of `Gtz.Reduction.BranchTransferConstants`
already writes as `kappa_e = (1 - s_e)/(1 - t_e)` in prose; that comment is the one place
a reader would look for it, and until now it had no name in the kernel. -/
noncomputable def deflationLevel (D : WeightedDesign m k) (atomIndex : Fin m) : ℝ :=
  (1 - atomShare D atomIndex) / (1 - D.weight atomIndex)

/-- **THE SHARP FORM.**  Every atom certifies a `k`-subset whose least eigenvalue is at
least that atom's deflation level.  This is the certificate above with the level pushed
to the exact value the share can buy. -/
theorem deflationLevel_le_lambdaMinMat_subsetSum [Nonempty (Fin k)]
    (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m) (hsmaller : GtzWeighted m k)
    (dropLabel : Fin (m + 1)) :
    ∃ selected : Finset (Fin (m + 1)), selected.card = k ∧
      deflationLevel D dropLabel ≤ lambdaMinMat (subsetSum D selected) := by
  have hweightLtOne : D.weight dropLabel < 1 := weight_lt_one D (by omega) dropLabel
  have hsurviving : (0 : ℝ) < 1 - D.weight dropLabel := by linarith
  have hcheap : atomShare D dropLabel
      ≤ 1 - deflationLevel D dropLabel * (1 - D.weight dropLabel) := by
    rw [deflationLevel, div_mul_cancel₀ _ (ne_of_gt hsurviving)]
    linarith
  obtain ⟨selected, hcard, hpsd⟩ :=
    exists_posSemidef_sub_of_atomShare_le D hsize hsmaller dropLabel hcheap
  exact ⟨selected, hcard, (le_lambdaMinMat_iff_posSemidef_sub_smul_one _
    (subsetSum_transpose D selected) _).mpr hpsd⟩

/-! ## The universal share floor -/

/-- **EVERY ATOM OF A FAILING DESIGN IS HEAVY, AT AN EXPLICIT RATE.**

If no `k`-subset dominates `value . I`, then every atom's share exceeds
`1 - value (1 - t_d)`.  Every statement of this shape the campaign had reached is
EXISTENTIAL -- some atom is cheap enough to deflate, as in
`Gtz.exists_atomShare_le_rank_div_size`; this is the universal companion, and the
existential ones follow from it by summation. -/
theorem lt_atomShare_of_forall_not_posSemidef (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (hsmaller : GtzWeighted m k) {value : ℝ}
    (hfail : ∀ C : Finset (Fin (m + 1)), C.card = k →
      ¬ (subsetSum D C - value • 1).PosSemidef)
    (dropLabel : Fin (m + 1)) :
    1 - value * (1 - D.weight dropLabel) < atomShare D dropLabel := by
  by_contra hle
  obtain ⟨selected, hcard, hpsd⟩ :=
    exists_posSemidef_sub_of_atomShare_le D hsize hsmaller dropLabel (not_lt.mp hle)
  exact hfail selected hcard hpsd

/-- The leverage reading of the share floor. -/
theorem lt_leverage_of_forall_not_posSemidef (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (hsmaller : GtzWeighted m k) {value : ℝ}
    (hfail : ∀ C : Finset (Fin (m + 1)), C.card = k →
      ¬ (subsetSum D C - value • 1).PosSemidef)
    (dropLabel : Fin (m + 1)) :
    1 + (1 - D.weight dropLabel) * (1 - value) / D.weight dropLabel
      < leverageOf (D.atom dropLabel) := by
  have hweightPos := D.weight_pos dropLabel
  have hshare := lt_atomShare_of_forall_not_posSemidef D hsize hsmaller hfail dropLabel
  rw [show atomShare D dropLabel = D.weight dropLabel * leverageOf (D.atom dropLabel) from rfl]
    at hshare
  have hrewrite : 1 + (1 - D.weight dropLabel) * (1 - value) / D.weight dropLabel
      = (1 - value * (1 - D.weight dropLabel)) / D.weight dropLabel := by
    field_simp
    ring
  rw [hrewrite, div_lt_iff₀ hweightPos]
  nlinarith [hshare]

/-- **ALL-HEAVINESS AT A COUNTEREXAMPLE.**  A design with no dominating `k`-subset is
all-heavy.  This is the `value = 1` case of the share floor, so crossing the leverage-one
face costs nothing beyond the smaller rung -- and unlike the route through
`Gtz.dominating_of_light_atom` it comes with the rate above.

This is NOT a duplicate of the shipped `Gtz.allHeavy_or_exists_leverage_eq_one_of_isTie`,
which has to stay a dichotomy: at a TIE weak domination is already present, so the
leverage-one face cannot be crossed.  At a counterexample there is no domination at all,
so weak domination is already a contradiction and the face is crossed for free. -/
theorem allHeavy_of_forall_not_dominates (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (hsmaller : GtzWeighted m k)
    (hfail : ∀ C : Finset (Fin (m + 1)), C.card = k → ¬ Dominates D C) :
    AllHeavy D := by
  intro atomIndex
  have hweightPos := D.weight_pos atomIndex
  have hshare := lt_atomShare_of_forall_not_posSemidef D hsize hsmaller
    (value := 1) (fun C hcard hpsd => hfail C hcard (by rwa [one_smul] at hpsd)) atomIndex
  rw [show atomShare D atomIndex = D.weight atomIndex * leverageOf (D.atom atomIndex) from rfl]
    at hshare
  nlinarith [hshare]

/-! ## The size-aware floor -/

/-- **THE SIZE-AWARE FLOOR, from the universal bound by summation.**

Weighted GTZ at size `m` lifts to level `1 - (k-1)/m` at size `m + 1`.  The proof is a
count against `Gtz.sum_atomShare_eq_rank` and `WeightedDesign.weight_sum_one`; no atom has
to be selected and no bound on the rank is needed.  At rank three this beats the shipped
size-free `Gtz.gtzWeightedFloor_inv_rank` at `1/k = 1/3` as soon as `m >= 4`. -/
theorem gtzWeightedFloor_succ_of_gtzWeighted (hsize : 1 ≤ m) (hsmaller : GtzWeighted m k) :
    GtzWeightedFloor (m + 1) k (1 - ((k : ℝ) - 1) / (m : ℝ)) := by
  intro D
  by_contra hfail
  push Not at hfail
  have hfailFull : ∀ C : Finset (Fin (m + 1)), C.card = k →
      ¬ (subsetSum D C - (1 - ((k : ℝ) - 1) / (m : ℝ)) • 1).PosSemidef :=
    fun C hcard => hfail C hcard
  have hstrict : ∀ atomIndex : Fin (m + 1),
      1 - (1 - ((k : ℝ) - 1) / (m : ℝ)) * (1 - D.weight atomIndex) < atomShare D atomIndex :=
    fun atomIndex => lt_atomShare_of_forall_not_posSemidef D hsize hsmaller hfailFull atomIndex
  have hsum : (∑ atomIndex : Fin (m + 1),
        (1 - (1 - ((k : ℝ) - 1) / (m : ℝ)) * (1 - D.weight atomIndex)))
      < ∑ atomIndex : Fin (m + 1), atomShare D atomIndex :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun atomIndex _ => hstrict atomIndex
  rw [sum_atomShare_eq_rank D] at hsum
  have hexpand : (∑ atomIndex : Fin (m + 1),
        (1 - (1 - ((k : ℝ) - 1) / (m : ℝ)) * (1 - D.weight atomIndex)))
      = ((m : ℝ) + 1) - (1 - ((k : ℝ) - 1) / (m : ℝ)) * (((m : ℝ) + 1) - 1) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, D.weight_sum_one]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [hexpand] at hsum
  have hmassPos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hsize
  rw [show ((m : ℝ) + 1) - 1 = (m : ℝ) from by ring, sub_mul,
    div_mul_cancel₀ _ (ne_of_gt hmassPos)] at hsum
  linarith

/-- **AT `(6,3)` THE FLOOR IS `3/5`, UNCONDITIONALLY** -- the input is the shipped
`Gtz.gtzWeighted_of_le_five`.  Almost double the shipped size-free `1/3`. -/
theorem gtzWeightedFloor_six_three_three_fifths :
    GtzWeightedFloor 6 3 ((3 : ℝ) / 5) := by
  have hfloor := gtzWeightedFloor_succ_of_gtzWeighted (m := 5) (k := 3) (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num))
  norm_num at hfloor
  exact hfloor

/-- **AT `(7,3)` THE FLOOR IS `2/3`, granted the open `Gtz.GtzWeighted 6 3`.**  Its
contrapositive is the quantitative form of boundary one: a `(7,3)` counterexample can miss
domination by at most `1/3`. -/
theorem gtzWeightedFloor_seven_three_two_thirds (hsixThree : GtzWeighted 6 3) :
    GtzWeightedFloor 7 3 ((2 : ℝ) / 3) := by
  have hfloor := gtzWeightedFloor_succ_of_gtzWeighted (m := 6) (k := 3) (by norm_num) hsixThree
  norm_num at hfloor
  exact hfloor

/-! ## The ceiling of the deflation lane -/

/-- **THE CEILING, as an exact equivalence.**  Deflation at an atom certifies a level
strictly below one EXACTLY when that atom is heavy.  There is no estimate in this
statement and therefore nothing to sharpen. -/
theorem deflationLevel_lt_one_iff_one_lt_leverage (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (atomIndex : Fin (m + 1)) :
    deflationLevel D atomIndex < 1 ↔ 1 < leverageOf (D.atom atomIndex) := by
  have hweightPos := D.weight_pos atomIndex
  have hweightLtOne : D.weight atomIndex < 1 := weight_lt_one D (by omega) atomIndex
  have hsurviving : (0 : ℝ) < 1 - D.weight atomIndex := by linarith
  rw [deflationLevel, div_lt_one hsurviving,
    show atomShare D atomIndex = D.weight atomIndex * leverageOf (D.atom atomIndex) from rfl]
  constructor <;> intro hbound <;> nlinarith [hbound]

/-- **THE LANE CANNOT REACH LEVEL ONE ON THE ALL-HEAVY CLASS.**

Every deflation level of an all-heavy design is strictly below one.  Since the frontier of
the campaign is exactly the all-heavy class, this says the deflation transport -- however
the pivot is chosen, and however the atom selection is refined -- can never output a
domination certificate.  The inequality is strict at every atom and there is no uniform
gap: the equivalence above turns level one into leverage one exactly, so the bound degrades
to nothing as an atom approaches the light face.  Whether the supremum over the class is
actually one is not claimed here. -/
theorem deflationLevel_lt_one_of_allHeavy (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (hheavy : AllHeavy D) (atomIndex : Fin (m + 1)) :
    deflationLevel D atomIndex < 1 :=
  (deflationLevel_lt_one_iff_one_lt_leverage D hsize atomIndex).mpr (hheavy atomIndex)

/-- **THE FLOOR IS THE LANE'S EXACT CEILING.**  On the shipped equal-share stratum
`Gtz.IsEqualShare` -- equal weights `1/(m+1)` and equal leverages `k`, hence equal shares
`k/(m+1)` by `Gtz.IsEqualShare.atomShare_eq` -- EVERY atom's deflation level is exactly
`1 - (k-1)/m`, the value the summation floor extracts.  So no refinement of the cheap-atom
selection can beat that constant: there is a design on which all atoms tie at it.

The ceiling is not attained vacuously: `Gtz.IsEqualShare.allHeavy` puts the whole stratum
inside the all-heavy class as soon as the rank exceeds one. -/
theorem deflationLevel_eq_of_uniform (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (hequal : IsEqualShare D) (atomIndex : Fin (m + 1)) :
    deflationLevel D atomIndex = 1 - ((k : ℝ) - 1) / (m : ℝ) := by
  have hmassPos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hsize
  have hsizePos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hmassNe : (m : ℝ) ≠ 0 := ne_of_gt hmassPos
  have hsizeNe : (m : ℝ) + 1 ≠ 0 := ne_of_gt hsizePos
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hweight : D.weight atomIndex = 1 / ((m : ℝ) + 1) := by
    rw [hequal.weight_eq atomIndex, hcast, one_div]
  have hshare : atomShare D atomIndex = (k : ℝ) / ((m : ℝ) + 1) := by
    rw [hequal.atomShare_eq atomIndex, hcast]
  have hden : (1 : ℝ) - 1 / ((m : ℝ) + 1) = (m : ℝ) / ((m : ℝ) + 1) := by
    field_simp
    ring
  have hdenNe : (1 : ℝ) - 1 / ((m : ℝ) + 1) ≠ 0 := by
    rw [hden]; exact div_ne_zero hmassNe hsizeNe
  rw [deflationLevel, hweight, hshare, div_eq_iff hdenNe]
  field_simp
  ring

/-- **THE DUST BRANCH NEEDS A LEVEL STRICTLY ABOVE ONE.**

`Gtz.exists_dominating_of_dust_atom_of_deflatedLevel` converts a Rayleigh floor one size
down into FULL domination, but only against the budget `1 - t_d <= level (1 - s_d)`.  At a
heavy atom that budget forces `1 < level`.  So no floor BELOW one, however good, can ever
fire that branch on an all-heavy design: the deflated statement would itself have to beat
weighted GTZ.  This is the ceiling above, read on the branch that was built to consume
floors.

The shipped barrier for the same lane is `Gtz.dustBudget_forces_leverage_le_one`, which
needs `4 <= floorSize`, rank exactly three, and a `Gtz.GtzWeightedFloor` hypothesis, and
derives `level <= 1` from the rank-three ceiling before running the same step.  The
statement here is the contrapositive of that step alone: rank-free, floor-free,
level-free. -/
theorem one_lt_level_of_dustBudget (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (dropLabel : Fin (m + 1)) (hheavy : 1 < leverageOf (D.atom dropLabel))
    (hshareBelowOne : atomShare D dropLabel < 1) {level : ℝ}
    (hbudget : 1 - D.weight dropLabel ≤ level * (1 - atomShare D dropLabel)) :
    1 < level := by
  have hweightPos := D.weight_pos dropLabel
  have hweightLtOne : D.weight dropLabel < 1 := weight_lt_one D (by omega) dropLabel
  have hexpand : atomShare D dropLabel
      = D.weight dropLabel * leverageOf (D.atom dropLabel) := rfl
  have hexcess : D.weight dropLabel < atomShare D dropLabel := by
    rw [hexpand]; nlinarith
  nlinarith [hbudget, hexcess, hshareBelowOne]

/-! ## The relative step of the size induction -/

/-- **The relative all-heavy step.**  Weighted GTZ one size down plus the ALL-HEAVY
statement at this size gives the plain statement at this size.  This is the inner step of
`Gtz.gtzWeightedAll_of_heavy_bounded`, which inlines it twice, isolated so the hypothesis
the size induction actually supplies at each rung is visible. -/
theorem gtzWeighted_succ_of_heavy_of_smaller (hsize : 1 ≤ size)
    (hsmaller : GtzWeighted size rank) (hheavy : GtzWeightedHeavy (size + 1) rank) :
    GtzWeighted (size + 1) rank := by
  intro design
  by_cases hlight : ∃ lightLabel, leverageOf (design.atom lightLabel) ≤ 1
  · obtain ⟨lightLabel, hlightLabel⟩ := hlight
    exact dominating_of_light_atom design hsize hsmaller lightLabel hlightLabel
  · exact hheavy design fun atomLabel => not_le.mp fun hle => hlight ⟨atomLabel, hle⟩

/-- The `(7,3)` reading of the relative step. -/
theorem gtzWeighted_seven_three_of_six_three_of_heavy (hsixThree : GtzWeighted 6 3)
    (hheavy : GtzWeightedHeavy 7 3) : GtzWeighted 7 3 :=
  gtzWeighted_succ_of_heavy_of_smaller (size := 6) (rank := 3) (by norm_num) hsixThree hheavy

/-! ## The all-heavy minimising counterexample -/

/-- **THE MINIMISING COUNTEREXAMPLE IS A DESIGN, AND IT IS ALL-HEAVY.**

Given the two smaller rungs, a failure of weighted GTZ at `(size + 1, rank + 1)` is
realised at a WEIGHTED DESIGN which

  * is `Gtz.AllHeavy` -- every leverage STRICTLY above one,
  * admits no dominating `(rank + 1)`-subset, and
  * globally minimises `Gtz.chartObjective` over the whole CLOSED chart domain, at a
    strictly negative value.

Three shipped facts compose, and nothing else is used.  `Gtz.ChartAttainment` supplies the
minimiser and, through the boundary dichotomy, its strict weight positivity;
`Gtz.chartPointHasDesign` turns a strictly-interior chart point into a design, which is
exactly where that positivity is spent; and the universal share floor above crosses the
leverage-one face.

Note the hypotheses are the SAME two rungs the attainment leg already consumes:
all-heaviness is free once interiority is paid for. -/
theorem exists_allHeavy_minimiser_of_not_gtzWeighted (hsize : 1 ≤ size)
    (hsameRank : GtzWeighted size (rank + 1)) (hdropRank : GtzWeighted size rank)
    (hfail : ¬ GtzWeighted (size + 1) (rank + 1)) :
    ∃ design : WeightedDesign (size + 1) (rank + 1),
      AllHeavy design
      ∧ (∀ selected : Finset (Fin (size + 1)), selected.card = rank + 1 →
          ¬ Dominates design selected)
      ∧ (∀ point : ChartPoint (size + 1) (rank + 1),
          chartObjective (chartPointOfDesign design) ≤ chartObjective point)
      ∧ chartObjective (chartPointOfDesign design) < 0 := by
  obtain ⟨minimiser, hmin, hnegative, hfails, hpositive⟩ :=
    exists_interior_minimiser_of_not_chartGtz
      ((chartGtz_iff_gtzWeighted size (rank + 1)).mpr hsameRank)
      ((chartGtz_iff_gtzWeighted size rank).mpr hdropRank)
      fun hchart => hfail (gtzWeighted_of_chartGtz hchart)
  obtain ⟨design, hdesign⟩ := chartPointHasDesign (size + 1) (rank + 1) minimiser hpositive
  subst hdesign
  have hnotDominates : ∀ selected : Finset (Fin (size + 1)), selected.card = rank + 1 →
      ¬ Dominates design selected := fun selected hcard hdominates =>
    hfails selected hcard ((dominates_iff_chartDominates design selected hcard).mp hdominates)
  exact ⟨design,
    allHeavy_of_forall_not_dominates (m := size) design hsize hsameRank hnotDominates,
    hnotDominates, hmin, hnegative⟩

/-- **At `(6,3)` the statement is UNCONDITIONAL**: both smaller rungs are the shipped
`Gtz.gtzWeighted_of_le_five`.  This is the cell where every reduction of this file is
a theorem rather than an implication. -/
theorem exists_allHeavy_minimiser_sixThree (hfail : ¬ GtzWeighted 6 3) :
    ∃ design : WeightedDesign 6 3,
      AllHeavy design
      ∧ (∀ selected : Finset (Fin 6), selected.card = 3 → ¬ Dominates design selected)
      ∧ (∀ point : ChartPoint 6 3,
          chartObjective (chartPointOfDesign design) ≤ chartObjective point)
      ∧ chartObjective (chartPointOfDesign design) < 0 :=
  exists_allHeavy_minimiser_of_not_gtzWeighted (size := 5) (rank := 2) (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num))
    (gtzWeighted_of_le_five 5 2 (by norm_num) (by norm_num)) hfail

/-- **At `(7,3)` the only hypothesis is the open `Gtz.GtzWeighted 6 3`** -- the drop-rank
rung is `Gtz.gtz_rank_two`, a theorem. -/
theorem exists_allHeavy_minimiser_sevenThree (hsixThree : GtzWeighted 6 3)
    (hfail : ¬ GtzWeighted 7 3) :
    ∃ design : WeightedDesign 7 3,
      AllHeavy design
      ∧ (∀ selected : Finset (Fin 7), selected.card = 3 → ¬ Dominates design selected)
      ∧ (∀ point : ChartPoint 7 3,
          chartObjective (chartPointOfDesign design) ≤ chartObjective point)
      ∧ chartObjective (chartPointOfDesign design) < 0 :=
  exists_allHeavy_minimiser_of_not_gtzWeighted (size := 6) (rank := 2) (by norm_num)
    hsixThree (gtz_rank_two 6) hfail

/-- **THE HYPOTHESIS-FREE DICHOTOMY.**  If rank three fails at all, then a minimising
ALL-HEAVY counterexample design exists at `(6,3)` or at `(7,3)`, with nothing assumed on
either side.  The split is on the open `Gtz.GtzWeighted 6 3` itself, so exactly one branch
is live and neither carries a hypothesis. -/
theorem exists_allHeavy_minimiser_of_not_rank_three (hfail : ¬ GtzWeightedAll 3) :
    (∃ design : WeightedDesign 6 3,
      AllHeavy design
      ∧ (∀ selected : Finset (Fin 6), selected.card = 3 → ¬ Dominates design selected)
      ∧ (∀ point : ChartPoint 6 3,
          chartObjective (chartPointOfDesign design) ≤ chartObjective point)
      ∧ chartObjective (chartPointOfDesign design) < 0)
    ∨ (∃ design : WeightedDesign 7 3,
      AllHeavy design
      ∧ (∀ selected : Finset (Fin 7), selected.card = 3 → ¬ Dominates design selected)
      ∧ (∀ point : ChartPoint 7 3,
          chartObjective (chartPointOfDesign design) ≤ chartObjective point)
      ∧ chartObjective (chartPointOfDesign design) < 0) := by
  by_cases hsixThree : GtzWeighted 6 3
  · exact Or.inr (exists_allHeavy_minimiser_sevenThree hsixThree
      fun hsevenThree => hfail (gtzWeightedAll_three_of_seven_three hsevenThree))
  · exact Or.inl (exists_allHeavy_minimiser_sixThree hsixThree)

/-! ## Boundary one, read in the chart -/

/-- **All-heaviness read in the chart**: the gap's diagonal is STRICTLY POSITIVE at an
all-heavy design.  Since `P_cc = t_c * leverage_c` and the weights are positive.

The rank-three twin `Gtz.chartMatrix_diagonal_gt_weight_of_allHeavy` is shipped in
`Gtz.Quantitative.SpreadCertificateSixThree` on `Gtz.chartMatrix`, built from
`Gtz.chartEntry`.  This one is rank-general and stated on the canonical
`Gtz.chartPointOfDesign` / `Gtz.projectionOfDesign`.  Those are two of the four separate
copies of the chart that `Gtz.Design.ProjectionChart`'s header ledgers; no bridge lemma
identifies them, so neither statement is formally derivable from the other. -/
theorem weight_lt_chart_diag_of_allHeavy {atoms rankValue : ℕ}
    {design : WeightedDesign atoms rankValue} (hheavy : AllHeavy design)
    (atomLabel : Fin atoms) :
    (chartPointOfDesign design).weight atomLabel
      < (chartPointOfDesign design).chart atomLabel atomLabel := by
  have hdiag : (chartPointOfDesign design).chart atomLabel atomLabel
      = design.weight atomLabel * leverageOf (design.atom atomLabel) :=
    projectionOfDesign_diagonal design atomLabel
  have hweight : (chartPointOfDesign design).weight atomLabel = design.weight atomLabel := rfl
  rw [hdiag, hweight]
  nlinarith [hheavy atomLabel, design.weight_pos atomLabel]

/-- Conversely, a light atom in the DESIGN sense is a nonpositive chart gap diagonal, so
the two readings of boundary one agree. -/
theorem leverage_le_one_of_projection_diag_le_weight {atoms rankValue : ℕ}
    (design : WeightedDesign atoms rankValue) (atomLabel : Fin atoms)
    (hlight : projectionOfDesign design atomLabel atomLabel ≤ design.weight atomLabel) :
    leverageOf (design.atom atomLabel) ≤ 1 := by
  rw [projectionOfDesign_diagonal] at hlight
  nlinarith [design.weight_pos atomLabel]

/-! ## The residue, and why it is not a discount -/

/-- Domination restricted to all-heavy designs that additionally MINIMISE the chart
objective over the closed chart domain.  Syntactically weaker than
`Gtz.GtzWeightedHeavy`: the minimality clause is an extra hypothesis on the design.
Logically, given the two smaller rungs, it is not weaker at all -- see
`gtzWeightedHeavyMinimal_iff_gtzWeighted`. -/
def GtzWeightedHeavyMinimal (atoms rankValue : ℕ) [Nonempty (Fin rankValue)] : Prop :=
  ∀ design : WeightedDesign atoms rankValue, AllHeavy design →
    (∀ point : ChartPoint atoms rankValue,
      chartObjective (chartPointOfDesign design) ≤ chartObjective point) →
    ∃ selected : Finset (Fin atoms), selected.card = rankValue ∧ Dominates design selected

/-- **THE REDUCTION.**  Given the two smaller rungs, weighted GTZ at
`(size + 1, rank + 1)` follows from the residue: all-heavy designs that minimise the chart
objective dominate.  Both boundaries of the all-heavy region have been paid -- the
vanishing-weight face by `Gtz.ChartAttainment`'s interiority clause, the leverage-one face
by the universal share floor. -/
theorem gtzWeighted_of_heavyMinimal (hsize : 1 ≤ size)
    (hsameRank : GtzWeighted size (rank + 1)) (hdropRank : GtzWeighted size rank)
    (hresidue : GtzWeightedHeavyMinimal (size + 1) (rank + 1)) :
    GtzWeighted (size + 1) (rank + 1) := by
  by_contra hfail
  obtain ⟨design, hdesignHeavy, hfails, hminimal, _⟩ :=
    exists_allHeavy_minimiser_of_not_gtzWeighted hsize hsameRank hdropRank hfail
  obtain ⟨selected, hcard, hdominates⟩ := hresidue design hdesignHeavy hminimal
  exact hfails selected hcard hdominates

/-- The `(6,3)` reduction, unconditional. -/
theorem gtzWeighted_six_three_of_heavyMinimal (hresidue : GtzWeightedHeavyMinimal 6 3) :
    GtzWeighted 6 3 :=
  gtzWeighted_of_heavyMinimal (size := 5) (rank := 2) (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num))
    (gtzWeighted_of_le_five 5 2 (by norm_num) (by norm_num)) hresidue

/-- The `(7,3)` reduction, carrying only the open `Gtz.GtzWeighted 6 3`. -/
theorem gtzWeighted_seven_three_of_heavyMinimal (hsixThree : GtzWeighted 6 3)
    (hresidue : GtzWeightedHeavyMinimal 7 3) : GtzWeighted 7 3 :=
  gtzWeighted_of_heavyMinimal (size := 6) (rank := 2) (by norm_num)
    hsixThree (gtz_rank_two 6) hresidue

/-- **RANK THREE FROM THE TWO MINIMAL RESIDUES.**  Both cells reduced to their minimising
all-heavy designs, with no hypothesis left over. -/
theorem gtzWeightedAll_three_of_heavyMinimal (hsixThree : GtzWeightedHeavyMinimal 6 3)
    (hsevenThree : GtzWeightedHeavyMinimal 7 3) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_seven_three
    (gtzWeighted_seven_three_of_heavyMinimal
      (gtzWeighted_six_three_of_heavyMinimal hsixThree) hsevenThree)

/-- **THE RESIDUE IS EQUIVALENT, NOT WEAKER.**  Granted the two smaller rungs, adding the
minimality clause to the all-heavy statement changes nothing about what has to be proved.
This is the statement that stops the residue being misread as a discount: minimality is
extra usable structure for a prover, not a logical saving.

Together with the shipped `Gtz.gtzWeightedHeavy_of_gtzWeighted`, the three statements
`GtzWeighted`, `Gtz.GtzWeightedHeavy` and `GtzWeightedHeavyMinimal` are therefore all
EQUIVALENT at `(size + 1, rank + 1)` given the rungs. -/
theorem gtzWeightedHeavyMinimal_iff_gtzWeighted (hsize : 1 ≤ size)
    (hsameRank : GtzWeighted size (rank + 1)) (hdropRank : GtzWeighted size rank) :
    GtzWeightedHeavyMinimal (size + 1) (rank + 1) ↔ GtzWeighted (size + 1) (rank + 1) :=
  ⟨gtzWeighted_of_heavyMinimal hsize hsameRank hdropRank,
    fun hfull design _ _ => hfull design⟩

/-- The `(6,3)` reading, UNCONDITIONAL: at the crux cell the minimising all-heavy residue
is exactly the cell. -/
theorem gtzWeightedHeavyMinimal_iff_gtzWeighted_six_three :
    GtzWeightedHeavyMinimal 6 3 ↔ GtzWeighted 6 3 :=
  gtzWeightedHeavyMinimal_iff_gtzWeighted (size := 5) (rank := 2) (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num))
    (gtzWeighted_of_le_five 5 2 (by norm_num) (by norm_num))

/-- The `(7,3)` reading: the minimising all-heavy residue at the frontier cell is exactly
the frontier cell. -/
theorem gtzWeightedHeavyMinimal_iff_gtzWeighted_seven_three (hsixThree : GtzWeighted 6 3) :
    GtzWeightedHeavyMinimal 7 3 ↔ GtzWeighted 7 3 :=
  gtzWeightedHeavyMinimal_iff_gtzWeighted (size := 6) (rank := 2) (by norm_num) hsixThree
    (gtz_rank_two 6)

/-! ## The frontier reading -/

/-- **THE `(7,3)` FRONTIER, quantified.**  Granted the open `Gtz.GtzWeighted 6 3`, a
`(7,3)` counterexample is all-heavy AND dominates at level `2/3`; and the two facts have
the same one-line source, the universal share floor. -/
theorem allHeavy_and_two_thirds_seven_three (hsixThree : GtzWeighted 6 3)
    (D : WeightedDesign 7 3)
    (hfail : ∀ C : Finset (Fin 7), C.card = 3 → ¬ Dominates D C) :
    AllHeavy D
      ∧ ∃ C : Finset (Fin 7), C.card = 3
          ∧ (subsetSum D C - ((2 : ℝ) / 3) • 1).PosSemidef :=
  ⟨allHeavy_of_forall_not_dominates (m := 6) D (by norm_num) hsixThree hfail,
    gtzWeightedFloor_seven_three_two_thirds hsixThree D⟩

/-- **AND THE LANE IS SPENT THERE.**  At that same counterexample every deflation level is
strictly below one, so no further pivot choice inside the transport can close the remaining
gap from `2/3` to `1`. -/
theorem deflationLevel_lt_one_seven_three (hsixThree : GtzWeighted 6 3)
    (D : WeightedDesign 7 3)
    (hfail : ∀ C : Finset (Fin 7), C.card = 3 → ¬ Dominates D C)
    (atomIndex : Fin 7) :
    deflationLevel D atomIndex < 1 :=
  deflationLevel_lt_one_of_allHeavy (m := 6) D (by norm_num)
    (allHeavy_of_forall_not_dominates (m := 6) D (by norm_num) hsixThree hfail) atomIndex

/-! ## Non-vacuity guard -/

/-- **ATTAINMENT FIRES AT THE FRONTIER CELL.**  The shipped `(7,3)` design
`Gtz.tripleSplitTetraDesign` inhabits the closed chart domain, so the minimality clause of
`GtzWeightedHeavyMinimal 7 3` is a condition on a NONEMPTY class of chart points: a global
minimiser of the chart objective exists at `(7,3)`.  The shipped
`Gtz.exists_chartObjective_isMin_fourTwo` guards the `(4,2)` cell only.

The all-heavy clause is likewise not vacuous, by the shipped
`Gtz.tripleSplitTetraDesign_allHeavy` -- and more sharply by
`Gtz.exists_allHeavy_isTie_seven_with_leverage_ge`. -/
theorem exists_chartObjective_isMin_sevenThree :
    ∃ minimiser : ChartPoint 7 3,
      ∀ point : ChartPoint 7 3, chartObjective minimiser ≤ chartObjective point :=
  exists_chartObjective_isMin (chartPointOfDesign tripleSplitTetraDesign)

end Gtz
