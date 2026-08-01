/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Reduction.Crystallization
import Gtz.Reduction.Reductions
import Gtz.Reduction.RankFourWindow

/-!
# The stress walk: crystallization one atom below the shipped cap

`Gtz.crystallization` reduces every weighted design down to the cap
`M(k) = k(k+1)/2 + 1` and STOPS THERE.  This file walks one atom further, to
`M'(k) = k(k+1)/2`, and at rank three that single atom is the whole difference
between a frontier of two open cells and a frontier of one.

## WHY THE SHIPPED WALK STOPS, AND WHY THIS ONE DOES NOT

`Gtz.exists_null_direction` asks its perturbation to annihilate `Gtz.momentMap`,
which bundles SEVEN linear functionals at rank three: the six upper-triangle
coordinates of `Gtz.upperTriangleCoords` and, in the second factor, the total
mass.  Seven functionals need eight unknowns to have a nontrivial kernel, so the
hypothesis is `k*(k+1)/2 + 1 < m` and at rank three the walk halts at `m = 8`,
leaving `(7,3)` unreachable.

`Gtz.exists_parsevalNullDirection` below drops the mass functional by composing
`Gtz.momentMap` with `LinearMap.fst`.  Six functionals on seven unknowns always
have a nontrivial kernel, so EVERY `(7,3)` design carries a stress and the
hypothesis relaxes to `k*(k+1)/2 < m`.

The price is that the mass now drifts.  The entire content of this file is that
the drift is AFFINE: along `w(s) = t + s * stress` the mass is exactly
`1 - s * A` with `A = ∑ stress`, so after normalising the sign of `A` the walk
that terminates is also the walk that does not gain mass, and it lands at some
`W ∈ (0, 1]`.  Parseval is preserved EXACTLY along the whole line, because
`∑ w(s)_c • atomMatrix (g c) = 1 + s • 0`.

## WHY A MASS BELOW ONE IS A GIFT

Renormalising the survivors divides the weights by `W` and scales the atoms by
`Real.sqrt W ≤ 1`, so the reduced design's atoms are SHORTER than the original's.
That looks like a loss and is not, because `Gtz.Dominates` reads `Gtz.subsetSum`,
which is WEIGHT-FREE: a triple dominating the shrunken atoms satisfies
`W * S ≥ 1`, hence `S ≥ W⁻¹ • 1 ≥ 1`.  This is
`Gtz.posSemidef_sub_one_of_smul_sub_one`, and it is where `W ≤ 1` is spent.

## WHAT LANDS

* `Gtz.exists_parsevalNullDirection` — the mass-free null direction.
* `Gtz.exists_rescaledReducedDesign` — the walk itself: above the Veronese
  dimension every design admits a strictly smaller design on a uniformly
  rescaled sub-family of its own atoms, at a scale in `(0, 1]`.
* `Gtz.crystallizationSharp` — the cap drops to `M'(k) = k(k+1)/2`, sharpening
  `Gtz.crystallization` by exactly the atom the mass constraint was costing.
* `Gtz.gtzWeighted_seven_three_of_six_three` — THE FLAGSHIP, the arrow the tree
  was missing.  The pre-existing candidate
  `Gtz.gtzWeighted_seven_three_of_six_three_of_heavy` still demands
  `Gtz.GtzWeightedHeavy 7 3`; this one demands nothing beyond `(6,3)`.
* `Gtz.gtzWeighted_six_three_iff_seven_three` — with the shipped converse
  `Gtz.gtzWeighted_six_three_of_seven_three`, the two cells are EQUIVALENT, so
  the campaign may fight at whichever carries more structure.
* `Gtz.gtzWeightedAll_three_of_six_three` and
  `Gtz.gtz_original_rank_three_of_six_three` — rank three, and the 1997
  statement at rank three, from the `(6,3)` cell alone.
* `Gtz.rank_three_iff_six_three` — RANK THREE IS ONE OBJECT, as an iff,
  sharpening `Gtz.rank_three_iff_the_two_residuals` from a conjunction of two
  cells to a single cell.
* `Gtz.liftingLemma_two_iff_six_three` — the same collapse for
  `Gtz.liftingLemma_two_iff_the_two_residuals`.
* `Gtz.gtzWeightedAll_two_of_walk` — `M'(2) = 3`, and every size at or below
  three is already a theorem, so weighted rank two falls out of the pigeonhole
  with no appeal to `Gtz.gtz_rank_two`.
* `Gtz.gtzWeightedAll_four_of_ten` — rank four's single object drops from
  `(11,4)` to `(10,4)`, sharpening `Gtz.gtzWeightedAll_four_of_eleven`.
* `Gtz.gtzWeightedAll_of_veroneseTop` — one object per rank, at `k(k+1)/2`.
* `Gtz.gtzWeightedAll_of_heavyVeroneseWindow` and
  `Gtz.rank_three_of_heavy_six_three` — the ALL-HEAVY window drops by the same
  atom, so rank three follows from the all-heavy `(6,3)` cell ALONE.  This is
  strictly stronger than the plain arrow, since `Gtz.GtzWeightedHeavy 6 3` is a
  weaker hypothesis than `Gtz.GtzWeighted 6 3`, and it sharpens all three of
  `Gtz.rank_three_of_heavy_residuals` (heavy at six AND seven),
  `Gtz.rank_three_of_heavy_top` (heavy at seven) and
  `Gtz.gtz_original_rank_three_of_heavy`.

## WHAT THIS DOES NOT DO, AND THE CAPITALS ARE THE POINT

THIS PROVES NOTHING ABOUT `(6,3)`.  It deletes the SECOND open cell of the
rank-three frontier, leaving the first exactly as open as it was:
`IsEmpty Gtz.SixThreeCrux` is untouched here and remains the wall.  What changes
is that the frontier is now ONE object rather than two, and that a `(7,3)`
result buys nothing a `(6,3)` result does not already buy.

THERE IS NO ALL-HEAVY VARIANT OF THE ARROW ITSELF, and it should not be
attempted.  Note carefully that this is NOT in tension with
`Gtz.rank_three_of_heavy_six_three` below: that theorem sharpens the all-heavy
WINDOW, by running the shipped deflation induction under the sharpened cap, and
never transports all-heaviness ALONG the walk.  What fails is the arrow
`Gtz.GtzWeightedHeavy 6 3 → Gtz.GtzWeightedHeavy 7 3`.
The reduced atoms are scaled by `Real.sqrt W ≤ 1`, so leverages SHRINK and
all-heaviness is not preserved.  Measured counterexample [exact rational,
outside Lean, not mechanized]: a `(7,3)` design built from three axis spikes and
four whitened planar atoms, every leverage strictly above one, walks to `W = 6/7`
with support size five and a reduced atom of leverage EXACTLY one.  So
`Gtz.GtzWeightedHeavy 6 3 → Gtz.GtzWeightedHeavy 7 3` does NOT follow from this
walk, and `Gtz.gtzWeighted_seven_three_of_six_three_of_heavy` is not subsumed —
it is a different statement that this one simply outruns.

## THE ARGUMENT HAS NO COMPLEX ANALOGUE, BY A DIMENSION COUNT

The stress exists because seven rank-one symmetric `3 × 3` matrices cannot be
independent in `Sym_3(ℝ)`, which has dimension `k*(k+1)/2 = 6`.  Over `ℂ` the
Veronese images live in `Herm_3(ℂ)`, of real dimension `k^2 = 9`, and `7 < 9`, so
SEVEN COMPLEX ATOMS CARRY NO STRESS AT ALL and this reduction is vacuous there.
That is the same mechanism as the shipped realness quantum
`Gtz.hermitianMomentFloor_lt_realMomentFloor`, and it is consistent with
`Gtz.complexGtzWeighted_six_three_fails`: the arrow proved here is a REAL
theorem, so it cannot transport a false complex `(6,3)` into a complex `(7,3)`.
[The complex non-existence is a dimension count, stated here for orientation;
it is not mechanized in this file.]

## WHAT THE OWNER'S SKETCH OVER-BUILT

The campaign sketch ran in nine steps, of which two are unnecessary and are not
used below.  Step S0 (dispose of zero atoms first) is unneeded: a design with a
zero atom walks correctly, and the reduced object is a genuine
`Gtz.WeightedDesign` whether the zero atom dies or survives.  Step S2 (the
stress has mixed signs, via `∑ stress_c * leverage_c = 0` with every leverage
positive) is TRUE but never invoked; the sign of `A = ∑ stress` alone selects
the walk direction, and `A ≥ 0` with `stress ≠ 0` already forces a strictly
positive coordinate — `Gtz.exists_pos_of_sum_nonneg`.  Dropping S2 removes the
only place positivity of leverages entered, which is what removes S0 with it.
-/

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The mass-free null direction -/

/-- **The Parseval null direction.**  More atoms than `k(k+1)/2` force a
nonzero weight perturbation annihilating Parseval alone.  This is
`Gtz.exists_null_direction` with the mass functional dropped: six constraints
instead of seven at rank three, so the hypothesis relaxes from `7 < m` to
`6 < m` and the walk reaches size seven. -/
theorem exists_parsevalNullDirection (g : Fin m → (Fin k → ℝ))
    (hm : k * (k + 1) / 2 < m) :
    ∃ stress : Fin m → ℝ, stress ≠ 0 ∧ (∑ c, stress c • atomMatrix (g c)) = 0 := by
  have hnotinj : ¬ Function.Injective
      ((LinearMap.fst ℝ ({ p : Fin k × Fin k // p.1 ≤ p.2 } → ℝ) ℝ).comp (momentMap g)) := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_fin, card_orderedPairs] at hle
    exact absurd hm (not_lt.mpr hle)
  rw [← LinearMap.ker_eq_bot] at hnotinj
  obtain ⟨stress, hmem, hne⟩ := (Submodule.ne_bot_iff _).mp hnotinj
  have hcoords : upperTriangleCoords (∑ c, stress c • atomMatrix (g c)) = 0 :=
    LinearMap.mem_ker.mp hmem
  have hsymmT : (∑ c, stress c • atomMatrix (g c))ᵀ
      = ∑ c, stress c • atomMatrix (g c) := by
    rw [Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (g c)).1]
  exact ⟨stress, hne, symmetric_eq_zero_of_coords_eq_zero hsymmT hcoords⟩

/-- **Sign normalisation.**  A nonzero direction whose coordinate sum is
nonnegative has a strictly positive coordinate -- so the walk that decreases
the mass is the one that terminates.  (With `sum = 0` this is the step
`Gtz.exists_reduced_design` performs inline.) -/
theorem exists_pos_of_sum_nonneg {stress : Fin m → ℝ} (hne : stress ≠ 0)
    (hsum : 0 ≤ ∑ c, stress c) : ∃ c, 0 < stress c := by
  by_contra hno
  push Not at hno
  have hallzero : ∀ c ∈ Finset.univ, stress c = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos fun c _ => hno c).mp
      (le_antisymm (Finset.sum_nonpos fun c _ => hno c) hsum)
  exact hne (funext fun c => hallzero c (Finset.mem_univ c))

/-! ## The walk, its mass law, and the rescaled reduced design -/

/-- **The mass-free kernel walk.**  A design with more than `k(k+1)/2` atoms
admits a strictly smaller design whose atoms are a UNIFORMLY RESCALED
sub-family of its own, at a scale in `(0, 1]`.

The scale is the walked mass `W = 1 - s* A`; when `A = 0` (in particular
whenever the stress can be chosen mass-free, e.g. a repeated-atom merge) it is
exactly one and this is `Gtz.exists_reduced_design` one size lower. -/
theorem exists_rescaledReducedDesign (D : WeightedDesign m k) (hk : 1 ≤ k)
    (hm : k * (k + 1) / 2 < m) :
    ∃ scale : ℝ, 0 < scale ∧ scale ≤ 1 ∧
      ∃ msmall : ℕ, msmall < m ∧ ∃ Dsmall : WeightedDesign msmall k,
        ∃ inject : Fin msmall → Fin m, Function.Injective inject ∧
          ∀ i, Dsmall.atom i = Real.sqrt scale • D.atom (inject i) := by
  obtain ⟨rawStress, hrawne, hrawParseval⟩ := exists_parsevalNullDirection D.atom hm
  -- sign-normalise: the walk that lowers the mass is the one that terminates
  obtain ⟨stress, hne, hstressParseval, hsumNonneg⟩ :
      ∃ stress : Fin m → ℝ, stress ≠ 0
        ∧ (∑ c, stress c • atomMatrix (D.atom c)) = 0 ∧ 0 ≤ ∑ c, stress c := by
    rcases le_or_gt 0 (∑ c, rawStress c) with hnonneg | hnegative
    · exact ⟨rawStress, hrawne, hrawParseval, hnonneg⟩
    · refine ⟨-rawStress, neg_ne_zero.mpr hrawne, ?_, ?_⟩
      · simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrawParseval, neg_zero]
      · simp only [Pi.neg_apply, Finset.sum_neg_distrib]
        linarith
  obtain ⟨cpos, hcpos⟩ := exists_pos_of_sum_nonneg hne hsumNonneg
  -- the walk length: the first weight to vanish
  set raisers : Finset (Fin m) := Finset.univ.filter (fun c => 0 < stress c) with hraisers
  have hraisersne : raisers.Nonempty :=
    ⟨cpos, Finset.mem_filter.mpr ⟨Finset.mem_univ cpos, hcpos⟩⟩
  obtain ⟨cstar, hcstarmem, hmin⟩ :=
    Finset.exists_min_image raisers (fun c => D.weight c / stress c) hraisersne
  have hstressStar : 0 < stress cstar := (Finset.mem_filter.mp hcstarmem).2
  set walkLen : ℝ := D.weight cstar / stress cstar with hwalkLen
  have hwalkLenPos : 0 < walkLen := div_pos (D.weight_pos cstar) hstressStar
  set walked : Fin m → ℝ := fun c => D.weight c - walkLen * stress c with hwalked
  have hwnonneg : ∀ c, 0 ≤ walked c := by
    intro c
    rcases le_or_gt (stress c) 0 with hnonpos | hposc
    · have hwc := D.weight_pos c
      simp only [hwalked]
      nlinarith
    · have hcmem : c ∈ raisers := Finset.mem_filter.mpr ⟨Finset.mem_univ c, hposc⟩
      have hle := (le_div_iff₀ hposc).mp (hmin c hcmem)
      simp only [hwalked]
      linarith
  have hwstar : walked cstar = 0 := by
    simp only [hwalked, hwalkLen]
    rw [div_mul_cancel₀ _ (ne_of_gt hstressStar), sub_self]
  have hwpars : ∑ c, walked c • atomMatrix (D.atom c) = 1 := by
    simp only [hwalked, sub_smul, mul_smul]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hstressParseval, smul_zero, sub_zero,
      D.isParseval]
  -- THE MASS LAW: affine in the walk length, hence at most one
  set mass : ℝ := ∑ c, walked c with hmass
  have hmassLaw : mass = 1 - walkLen * (∑ c, stress c) := by
    simp only [hmass, hwalked]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, D.weight_sum_one]
  have hmassLeOne : mass ≤ 1 := by
    rw [hmassLaw]
    nlinarith [hwalkLenPos, hsumNonneg]
  have hmassNonneg : 0 ≤ mass := Finset.sum_nonneg fun c _ => hwnonneg c
  have hmassPos : 0 < mass := by
    rcases eq_or_lt_of_le hmassNonneg with hzero | hpos
    · exfalso
      have hallzero : ∀ c ∈ Finset.univ, walked c = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun c _ => hwnonneg c).mp hzero.symm
      have hcollapse : (0 : Matrix (Fin k) (Fin k) ℝ) = 1 := by
        rw [← hwpars]
        exact (Finset.sum_eq_zero fun c hc => by
          rw [hallzero c hc, zero_smul]).symm
      have hentry := congrFun (congrFun hcollapse ⟨0, hk⟩) ⟨0, hk⟩
      rw [Matrix.zero_apply, Matrix.one_apply_eq] at hentry
      exact zero_ne_one hentry
    · exact hpos
  -- the positive-weight support: strictly smaller, and cstar is gone
  set support : Finset (Fin m) := Finset.univ.filter (fun c => 0 < walked c) with hsupport
  have hcstarout : cstar ∉ support := by simp [hsupport, hwstar]
  have hsupportlt : support.card < m := by
    have hsub : support ⊆ Finset.univ.erase cstar := fun c hc =>
      Finset.mem_erase.mpr ⟨fun heq => hcstarout (heq ▸ hc), Finset.mem_univ c⟩
    calc support.card ≤ (Finset.univ.erase cstar).card := Finset.card_le_card hsub
      _ < m := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ cstar), Finset.card_univ,
            Fintype.card_fin]
          omega
  have houtside : ∀ c ∈ Finset.univ, c ∉ support → walked c = 0 := by
    intro c _ hc
    have hnotpos : ¬ 0 < walked c := fun hposc =>
      hc (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hposc⟩)
    exact le_antisymm (not_lt.mp hnotpos) (hwnonneg c)
  have hsumS : ∑ c ∈ support, walked c = mass := by
    rw [Finset.sum_subset (Finset.subset_univ support) houtside]
  have hparsS : ∑ c ∈ support, walked c • atomMatrix (D.atom c) = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ support)
      (fun c hcu hcs => by rw [houtside c hcu hcs, zero_smul])]
    exact hwpars
  -- the atoms shrink by sqrt(mass), so their matrices shrink by mass
  have hatomScale : ∀ v : Fin k → ℝ,
      atomMatrix (Real.sqrt mass • v) = mass • atomMatrix v := fun v => by
    rw [atomMatrix_smul, Real.sq_sqrt hmassPos.le]
  refine ⟨mass, hmassPos, hmassLeOne, support.card, hsupportlt,
    { atom := fun i => Real.sqrt mass • D.atom (support.orderIsoOfFin rfl i).val
      weight := fun i => walked (support.orderIsoOfFin rfl i).val / mass
      weight_pos := fun i =>
        div_pos (Finset.mem_filter.mp (support.orderIsoOfFin rfl i).2).2 hmassPos
      weight_sum_one := ?_
      isParseval := ?_ },
    fun i => (support.orderIsoOfFin rfl i).val,
    fun a b hab => (support.orderIsoOfFin rfl).toEquiv.injective
      (Subtype.val_injective hab),
    fun i => rfl⟩
  · rw [← Finset.sum_div, sum_orderIsoOfFin support rfl walked, hsumS,
      div_self (ne_of_gt hmassPos)]
  · calc ∑ i, (walked (support.orderIsoOfFin rfl i).val / mass)
            • atomMatrix (Real.sqrt mass • D.atom (support.orderIsoOfFin rfl i).val)
        = ∑ i, walked (support.orderIsoOfFin rfl i).val
            • atomMatrix (D.atom (support.orderIsoOfFin rfl i).val) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hatomScale, smul_smul, div_mul_cancel₀ _ (ne_of_gt hmassPos)]
      _ = 1 := by
          rw [sum_orderIsoOfFin support rfl
            (fun c => walked c • atomMatrix (D.atom c))]
          exact hparsS

/-! ## The pullback -/

/-- **Rescaling only helps.**  If the atoms were shrunk by `sqrt W` with
`0 < W <= 1` and the shrunken subset already dominates, the original subset
dominates: `W * S >= I` gives `S >= (1/W) * I >= I`.  Domination is
weight-free, so nothing about the weights enters. -/
theorem posSemidef_sub_one_of_smul_sub_one {scale : ℝ} (hpos : 0 < scale)
    (hle : scale ≤ 1) {S : Matrix (Fin k) (Fin k) ℝ}
    (hdom : (scale • S - 1).PosSemidef) : (S - 1).PosSemidef := by
  have hsplit : S - 1
      = scale⁻¹ • (scale • S - 1) + (scale⁻¹ - 1) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul, sub_smul,
      one_smul]
    abel
  rw [hsplit]
  refine Matrix.PosSemidef.add (hdom.smul (le_of_lt (inv_pos.mpr hpos))) ?_
  refine Matrix.PosSemidef.one.smul ?_
  have hinv : 1 ≤ scale⁻¹ := (one_le_inv_iff₀).mpr ⟨hpos, hle⟩
  linarith

/-! ## The sharpened crystallization -/

/-- **The relative step.**  Above the Veronese dimension, weighted GTZ at every
STRICTLY SMALLER size gives it at this size. -/
theorem gtzWeighted_of_forall_smaller (hm : k * (k + 1) / 2 < m)
    (hsmaller : ∀ msmall, msmall < m → GtzWeighted msmall k) : GtzWeighted m k := by
  rcases Nat.eq_zero_or_pos k with hrankZero | hrankPos
  · rw [hrankZero]
    exact gtzWeighted_dim_zero m
  intro D
  obtain ⟨scale, hpos, hle, msmall, hlt, Dsmall, inject, hinj, hatoms⟩ :=
    exists_rescaledReducedDesign D hrankPos hm
  obtain ⟨Csmall, hcard, hdom⟩ := hsmaller msmall hlt Dsmall
  refine ⟨Csmall.image inject, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, hcard]
  · show (subsetSum D (Csmall.image inject) - 1).PosSemidef
    have hsums : subsetSum Dsmall Csmall
        = scale • subsetSum D (Csmall.image inject) := by
      rw [subsetSum, subsetSum, Finset.sum_image fun x _ y _ hxy => hinj hxy,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hatoms i, atomMatrix_smul, Real.sq_sqrt hpos.le]
    refine posSemidef_sub_one_of_smul_sub_one hpos hle ?_
    rw [← hsums]
    exact hdom

/-- **Crystallization at the Veronese dimension.**  If weighted GTZ(k) holds at
every size at most `M'(k) = k(k+1)/2`, it holds at every size.  This sharpens
`Gtz.crystallization`, whose cap is `M(k) = k(k+1)/2 + 1`, by exactly one
atom -- the atom the mass constraint was costing. -/
theorem crystallizationSharp (k : ℕ)
    (hsmall : ∀ m, m ≤ k * (k + 1) / 2 → GtzWeighted m k) : GtzWeightedAll k := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases le_or_gt m (k * (k + 1) / 2) with hle | hgt
    · exact hsmall m hle
    · exact gtzWeighted_of_forall_smaller hgt ih

/-- **One object per rank, at the Veronese dimension.**  Weighted GTZ at the
single size `k(k+1)/2` carries the whole rank, since every smaller size follows
from `Gtz.gtzWeighted_of_le`.  This is the sharpened cap in the form the
campaign consumes: at rank three the one object is `(6,3)`, at rank four
`(10,4)`. -/
theorem gtzWeightedAll_of_veroneseTop (rank : ℕ)
    (htop : GtzWeighted (rank * (rank + 1) / 2) rank) : GtzWeightedAll rank :=
  crystallizationSharp rank fun _size hsize => gtzWeighted_of_le hsize htop

/-! ## Rank three: the flagship -/

/-- **`(7,3)` follows from `(6,3)`** -- the arrow the tree was missing.  The
existing candidate `Gtz.gtzWeighted_seven_three_of_six_three_of_heavy` still
demands `Gtz.GtzWeightedHeavy 7 3`; this one demands nothing extra. -/
theorem gtzWeighted_seven_three_of_six_three (h63 : GtzWeighted 6 3) :
    GtzWeighted 7 3 :=
  gtzWeighted_of_forall_smaller (m := 7) (k := 3) (by norm_num)
    fun msmall hlt => gtzWeighted_of_le (by omega) h63

/-- **`(6,3)` and `(7,3)` are EQUIVALENT.**  The converse is the shipped
`Gtz.gtzWeighted_six_three_of_seven_three`, so the campaign may fight at
whichever cell carries more structure. -/
theorem gtzWeighted_six_three_iff_seven_three :
    GtzWeighted 6 3 ↔ GtzWeighted 7 3 :=
  ⟨gtzWeighted_seven_three_of_six_three, gtzWeighted_six_three_of_seven_three⟩

/-- **Rank three from `(6,3)` alone.**  Proved DIRECTLY as the rank-three
instance of `Gtz.gtzWeightedAll_of_veroneseTop`, because `3 * (3+1) / 2 = 6` on
the nose: the `(6,3)` cell IS the Veronese top at rank three.

Routing instead through the flagship arrow and
`Gtz.gtzWeightedAll_three_of_seven_three` also works, but drags the whole chain
back through the SHIPPED `Gtz.crystallization` and `Gtz.exists_null_direction`,
whose cap is the weaker `M(k) = k(k+1)/2 + 1`.  Measured by transitive closure
over `ConstantInfo.value? (allowOpaque := true)`: the detour reaches 21196
constants including all three of `Gtz.crystallization`,
`Gtz.gtzWeightedAll_three_of_seven_three` and `Gtz.exists_null_direction`, the
direct route reaches 20951 and NONE of them.  So rank three now rests on the
sharpened walk alone. -/
theorem gtzWeightedAll_three_of_six_three (h63 : GtzWeighted 6 3) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_of_veroneseTop 3 h63

/-- **The 1997 statement at rank three from `(6,3)` alone.** -/
theorem gtz_original_rank_three_of_six_three (h63 : GtzWeighted 6 3) :
    ∀ n, 0 < n → GtzOriginal n 3 :=
  original_of_weighted 3 (gtzWeightedAll_three_of_six_three h63)

/-- **RANK THREE IS ONE OBJECT, AS AN IFF.**  Sharpens
`Gtz.rank_three_iff_the_two_residuals`, whose right-hand side is the CONJUNCTION
`GtzWeighted 6 3 ∧ GtzWeighted 7 3`.  The second conjunct was never independent. -/
theorem rank_three_iff_six_three : GtzWeightedAll 3 ↔ GtzWeighted 6 3 :=
  ⟨fun hall => hall 6, gtzWeightedAll_three_of_six_three⟩

/-- The lifting-lemma frontier collapses to one residual, sharpening
`Gtz.liftingLemma_two_iff_the_two_residuals`. -/
theorem liftingLemma_two_iff_six_three : LiftingLemma 2 ↔ GtzWeighted 6 3 :=
  liftingLemma_two_iff_the_two_residuals.trans
    ⟨fun hpair => hpair.1,
     fun h63 => ⟨h63, gtzWeighted_seven_three_of_six_three h63⟩⟩

/-! ## Bonus consequences of the sharpened cap -/

/-- **Weighted rank two, with no appeal to Sengupta-Pautov.**  `M'(2) = 3`, and
`GtzWeighted m 2` for `m <= 3` is the square plus co-rank one -- both already
theorems that descend to rank ONE only.  So the walk reproves
`Gtz.gtz_rank_two` from the pigeonhole. -/
theorem gtzWeightedAll_two_of_walk : GtzWeightedAll 2 := by
  refine crystallizationSharp 2 fun size hsize => ?_
  norm_num at hsize
  interval_cases size
  · exact fun D => absurd (rank_le_of_design D) (by omega)
  · exact fun D => absurd (rank_le_of_design D) (by omega)
  · exact gtzWeighted_square 2
  · exact gtzWeighted_corank_one 2 (by omega)

/-- **Rank four from `(10,4)`**, sharpening `Gtz.gtzWeightedAll_four_of_eleven`,
whose single object is `(11,4)`. -/
theorem gtzWeightedAll_four_of_ten (h10 : GtzWeighted 10 4) : GtzWeightedAll 4 :=
  gtzWeightedAll_of_veroneseTop 4 h10

/-! ## The all-heavy window drops by the same atom

`Gtz.gtzWeightedAll_of_heavy_bounded` reaches the cap through
`Gtz.crystallization`, and that call is the ONLY place the cap enters -- the
deflation induction beneath it only ever DECREASES the size, so it never
notices which cap it is running under.  Swapping in `Gtz.crystallizationSharp`
therefore drops the all-heavy window verbatim, and the consequence is STRICTLY
STRONGER than the plain arrow above, because `Gtz.GtzWeightedHeavy 6 3` is a
weaker hypothesis than `Gtz.GtzWeighted 6 3`. -/

/-- **The all-heavy window at the Veronese dimension.**  Sharpens
`Gtz.gtzWeightedAll_of_heavy_bounded`, whose window is `k(k+1)/2 + 1`. -/
theorem gtzWeightedAll_of_heavyVeroneseWindow {k : ℕ} (hk : 1 ≤ k)
    (hheavy : ∀ m, m ≤ k * (k + 1) / 2 → GtzWeightedHeavy m k) :
    GtzWeightedAll k := by
  refine crystallizationSharp k fun m hm => ?_
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro D
    have hkm : k ≤ m := rank_le_of_design D
    rcases eq_or_lt_of_le hkm with hsquare | hstrict
    · subst hsquare
      exact gtzWeighted_square k D
    · by_cases hlight : ∃ d, leverageOf (D.atom d) ≤ 1
      · obtain ⟨d, hd⟩ := hlight
        obtain ⟨mpred, rfl⟩ : ∃ mpred, m = mpred + 1 := ⟨m - 1, by omega⟩
        exact dominating_of_light_atom D (by omega)
          (ih mpred (by omega) (by omega)) d hd
      · push Not at hlight
        exact hheavy m hm D hlight

/-- **Rank three from the ALL-HEAVY `(6,3)` cell alone.**  Sharpens both
`Gtz.rank_three_of_heavy_residuals`, which asks for all-heavy at sizes six AND
seven, and `Gtz.rank_three_of_heavy_top`, which asks at seven.  This is the
strongest rank-three reduction in the tree: every design with a light atom,
every size away from six, and every rank below three are already theorems, so
what remains is the all-heavy `(6,3)` box -- exactly the box
`Gtz.IsSixThreeRefutationCandidate` describes, whose `Gtz.AllHeavy` conjunct is
therefore not a restriction of the search but a property of it.

The size-five rung is discharged by `Gtz.gtzWeightedAll_two_of_walk` rather than
by the shipped `Gtz.gtz_rank_two`, which makes the whole chain independent of
Sengupta-Pautov: measured by transitive closure over
`ConstantInfo.value? (allowOpaque := true)`, this proof term reaches neither
`Gtz.gtz_rank_two` nor `Gtz.exists_dominating_pair_of_heavy`, where the shipped
`Gtz.rank_three_of_the_two_residuals` reaches both. -/
theorem rank_three_of_heavy_six_three (h63 : GtzWeightedHeavy 6 3) :
    GtzWeightedAll 3 := by
  refine gtzWeightedAll_of_heavyVeroneseWindow (by omega) fun m hm => ?_
  norm_num at hm
  interval_cases m
  · exact fun D _ => absurd (rank_le_of_design D) (by omega)
  · exact fun D _ => absurd (rank_le_of_design D) (by omega)
  · exact fun D _ => absurd (rank_le_of_design D) (by omega)
  · exact fun D _ => gtzWeighted_square 3 D
  · exact fun D _ => gtzWeighted_of_dual_rank (by omega) (by omega) (gtz_rank_one 4) D
  · exact fun D _ => gtzWeighted_of_dual_rank (by omega) (by omega)
      (gtzWeightedAll_two_of_walk 5) D
  · exact h63

/-- **The 1997 statement at rank three from the ALL-HEAVY `(6,3)` cell alone**,
sharpening `Gtz.gtz_original_rank_three_of_heavy`, which asks for all-heavy at
sizes six AND seven. -/
theorem gtz_original_rank_three_of_heavy_six_three (h63 : GtzWeightedHeavy 6 3) :
    ∀ n, 0 < n → GtzOriginal n 3 :=
  original_of_weighted 3 (rank_three_of_heavy_six_three h63)

end Gtz
