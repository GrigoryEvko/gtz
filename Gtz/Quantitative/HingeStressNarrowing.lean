/-
# The strict stress walk, and the third narrowing of every six-point ledger entry

`Gtz.hingeHoldsAtSize_of_linearSpaceEnumeration_sixThree` reduces
`Gtz.HingeHoldsAtSize 6 3` to the combinatorial completeness of
`Gtz.linePatternListSix` — attacked in `Gtz.Design.LinePatternSixCases` — plus
one tie-freeness obligation per non-near-pencil entry of `Gtz.lineFamiliesSix`.
This file attacks the SECOND input.

## The honest arithmetic

READ THIS BEFORE CITING ANYTHING BELOW.  ZERO of the eight entries is
discharged here.  There were eight open obligations, or sixteen after
`Gtz.stratumIsTieFreeAmongHeavy_of_allHeavy_and_unitLeverage` splits each at the
unit-leverage face, and there still are.  What changes is that every one of them
may now assume MORE about its designs, and that three of the eight are sharpened
from an open stratum to an equation on a sublocus of it.

## The strict stress walk

`Gtz.exists_dominating_sixThree_of_stress` turns any nonzero stress on a `(6,3)`
design into a WEAKLY dominating triple.  A tie already has one, so as shipped the
theorem cannot exclude a tie and the hinge lane has never consumed it.

`exists_posDef_sixThree_of_stress_sum_ne_zero` upgrades the conclusion to
`Matrix.PosDef` under one purely arithmetic extra hypothesis: the stress's
COORDINATE SUM is nonzero.  The mechanism is the mass law already visible inside
the shipped walk's own proof — `mass = 1 - walkLength * (∑ c, stress c)` with
`walkLength > 0` — so a stress of nonzero sum walks to mass strictly below one,
and `W • S ≥ 1` with `W < 1` gives `S - 1 ≥ (W⁻¹ - 1) • 1 > 0`.  The walk is not
re-proved: `stressWalkedDesign` moves the strict mass loss OUTSIDE it by
pre-shrinking the design along the stress, and the shipped walk is then applied
to the shrunken design as a black box.

## The narrowing, and what it costs

`HasOnlyBalancedStress` says every stress of the design has coordinate sum zero.
Dually — the stress space is the kernel of the Hadamard-square Gram — it says the
all-ones vector lies in that Gram's RANGE.  Every `(6,3)` tie has the property
(`hasOnlyBalancedStress_of_isTie_sixThree`), so a ledger entry may assume it for
free, and `stratumIsTieFreeAmongHeavy_of_balancedStress_sixThree` composes it with
the ledger's own leverage narrowing.  The two are orthogonal: the ledger's
constrains atom LENGTHS, this one constrains DEPENDENCIES.

The narrowing is stated at all four ledger shapes —
`StratumIsTieFreeAmongHeavyAtBalancedStress`,
`StratumIsTieFreeAmongAllHeavyAtBalancedStress`,
`StratumIsTieFreeAtUnitLeverageAtBalancedStress`, and the plain
`StratumIsTieFreeAtBalancedStress` — so it applies to whichever form an entry is
being attacked in, including both halves of the unit-leverage split.

## Three entries sharpened to an equation

`PatternForcesStress` names the entries whose pattern alone manufactures a
stress, through a line-pair quadric built from two plane normals that between
them cover all six labels.  Three of the eight qualify, and the third is the one
worth noticing:

* `[[0,1,2],[3,4,5]]` — two disjoint three-point lines, two planes;
* `[[0,1,2,3],[0,4,5]]` — a four-point line and a three-point line, two planes;
* `[[0,1,2,3]]` — ONE four-point line.  The second plane is not a line of the
  pattern at all: any two vectors lie in a plane, so the two labels off the line
  supply a normal for free, and `Gtz.exists_lineNormal_of_hasLinePattern` returns
  it because no line of the pattern carries both of them.

On those three entries a tie must therefore carry a nonzero stress of zero
coordinate sum, so the residual is not "no tie on the stratum" but "no tie on the
codimension-one sublocus where the stress balances".  The other five entries
admit no covering pair of planes and get no stress from their pattern.

## What a tie must look like, and the descent

* every stress of a `(6,3)` tie has coordinate sum ZERO;
* hence every parallel pair of a `(6,3)` tie has `ratio ^ 2 = 1` — the two atoms
  have EQUAL LENGTH, which sharpens `Gtz.HingeHoldsAtSize`'s own conclusion;
* hence every STRESSED `(6,3)` tie restricts to a tie on FOUR or FIVE atoms
  carrying the SAME vectors.  The shrink factor of the shipped walk must be
  exactly one at a tie, since any strict shrink would make the pullback strictly
  dominating; three atoms are excluded by `Gtz.posDef_fullExcess`.

## The Bezout brick

`quadForm_eq_zero_of_span_of_three_collinear`: a symmetric form vanishing on two
independent vectors and on a combination of them with both coefficients nonzero
vanishes on their whole span.  A conic meeting a line three times contains it.
This is what separates the nine six-point classes into those whose lines admit a
covering pair of planes and those whose lines do not; it is stated size-generically
and is not consumed below, where the covering pairs are exhibited directly.

## What is NOT here

* Any discharged class.  The descent lands at four or five atoms, and both
  `U(3,4)` and the `(5,3)` diamond host ties, so it does not bottom out.
* Any statement about a crux.  This lane is about `Gtz.IsTie`, and the hinge is
  one lane among several.
* The five entries with no covering pair.  Their patterns force no stress, so
  every tool in this file is silent on them.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Certificates.ResidueDissolution
import Gtz.Reduction.Reductions
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.StressWalk
import Gtz.Reduction.StressConditionalWalk
import Gtz.Design.PrimitiveTightClassification
import Gtz.Design.StratumTieFreeClasses
import Gtz.Reduction.DescentLadder
import Gtz.Design.StratumEmptinessLedger
import Gtz.Design.LinePatternEnumeration
import Gtz.Design.LinePatternSixCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The strict pullback -/

/-- **Strict rescaling strictly helps.**  `Gtz.posSemidef_sub_one_of_smul_sub_one`
with the mass loss made strict: `W * S >= I` and `W < 1` give
`S - I >= (1/W - 1) I`, which is positive definite. -/
theorem posDef_sub_one_of_smul_sub_one {shrink : ℝ} (hpos : 0 < shrink)
    (hlt : shrink < 1) {gramSum : Matrix (Fin rank) (Fin rank) ℝ}
    (hdom : (shrink • gramSum - 1).PosSemidef) : (gramSum - 1).PosDef := by
  have hinvPos : 0 < shrink⁻¹ := inv_pos.mpr hpos
  have hinvGtOne : 1 < shrink⁻¹ := by
    have hcancel : shrink * shrink⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
    nlinarith
  have hsplit : gramSum - 1
      = (shrink⁻¹ - 1) • (1 : Matrix (Fin rank) (Fin rank) ℝ)
        + shrink⁻¹ • (shrink • gramSum - 1) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul, sub_smul, one_smul]
    abel
  rw [hsplit]
  exact Matrix.PosDef.add_posSemidef (Matrix.PosDef.one.smul (by linarith))
    (hdom.smul hinvPos.le)

/-! ## Pre-shrinking along a stress

The shipped walk returns only `scale <= 1`.  Rather than re-prove it with the
strict mass law exposed, move the strict loss into the INPUT: walk the weights a
short way along the stress by hand, renormalise, and hand the result to the walk.
Both steps shrink, so the composite shrink is strictly below one. -/

/-- **The stress-perturbed design.**  Weights moved a step along the stress and
renormalised by their total mass; atoms shrunk by the square root of that mass so
Parseval survives.  Parseval is preserved because the stress annihilates it and
the atom shrink exactly undoes the weight renormalisation. -/
noncomputable def stressWalkedDesign (design : WeightedDesign size rank)
    (stress : Fin size → ℝ) (step : ℝ) (hsizePos : 0 < size)
    (hstepped : ∀ c, 0 < design.weight c - step * stress c)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0) :
    WeightedDesign size rank where
  atom c := Real.sqrt (∑ d, (design.weight d - step * stress d)) • design.atom c
  weight c := (design.weight c - step * stress c)
    / ∑ d, (design.weight d - step * stress d)
  weight_pos c := by
    have hmassPos : 0 < ∑ d, (design.weight d - step * stress d) :=
      Finset.sum_pos (fun d _ => hstepped d) ⟨⟨0, hsizePos⟩, Finset.mem_univ _⟩
    exact div_pos (hstepped c) hmassPos
  weight_sum_one := by
    have hmassPos : 0 < ∑ d, (design.weight d - step * stress d) :=
      Finset.sum_pos (fun d _ => hstepped d) ⟨⟨0, hsizePos⟩, Finset.mem_univ _⟩
    rw [← Finset.sum_div, div_self (ne_of_gt hmassPos)]
  isParseval := by
    have hmassPos : 0 < ∑ d, (design.weight d - step * stress d) :=
      Finset.sum_pos (fun d _ => hstepped d) ⟨⟨0, hsizePos⟩, Finset.mem_univ _⟩
    have hatomScale : ∀ vec : Fin rank → ℝ,
        atomMatrix (Real.sqrt (∑ d, (design.weight d - step * stress d)) • vec)
          = (∑ d, (design.weight d - step * stress d)) • atomMatrix vec := fun vec => by
      rw [atomMatrix_smul, Real.sq_sqrt hmassPos.le]
    calc ∑ c, ((design.weight c - step * stress c)
              / ∑ d, (design.weight d - step * stress d))
            • atomMatrix (Real.sqrt (∑ d, (design.weight d - step * stress d))
              • design.atom c)
        = ∑ c, (design.weight c - step * stress c) • atomMatrix (design.atom c) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hatomScale, smul_smul, div_mul_cancel₀ _ (ne_of_gt hmassPos)]
      _ = 1 := by
          simp only [sub_smul, mul_smul]
          rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hstress, smul_zero, sub_zero,
            design.isParseval]

/-- The perturbed design's atoms are a uniform shrink of the original ones, so its
subset sums are the original ones scaled by the mass. -/
theorem subsetSum_stressWalkedDesign (design : WeightedDesign size rank)
    (stress : Fin size → ℝ) (step : ℝ) (hsizePos : 0 < size)
    (hstepped : ∀ c, 0 < design.weight c - step * stress c)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0)
    (selected : Finset (Fin size)) :
    subsetSum (stressWalkedDesign design stress step hsizePos hstepped hstress) selected
      = (∑ d, (design.weight d - step * stress d)) • subsetSum design selected := by
  have hmassPos : 0 < ∑ d, (design.weight d - step * stress d) :=
    Finset.sum_pos (fun d _ => hstepped d) ⟨⟨0, hsizePos⟩, Finset.mem_univ _⟩
  rw [subsetSum, subsetSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  show atomMatrix (Real.sqrt (∑ d, (design.weight d - step * stress d)) • design.atom c)
    = _
  rw [atomMatrix_smul, Real.sq_sqrt hmassPos.le]

/-- The perturbed design carries the same stress, scaled by the mass — so it is
still a stress, and the shipped walk applies to it. -/
theorem stress_stressWalkedDesign (design : WeightedDesign size rank)
    (stress : Fin size → ℝ) (step : ℝ) (hsizePos : 0 < size)
    (hstepped : ∀ c, 0 < design.weight c - step * stress c)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0) :
    (∑ c, stress c
      • atomMatrix ((stressWalkedDesign design stress step hsizePos hstepped hstress).atom c))
      = 0 := by
  have hmassPos : 0 < ∑ d, (design.weight d - step * stress d) :=
    Finset.sum_pos (fun d _ => hstepped d) ⟨⟨0, hsizePos⟩, Finset.mem_univ _⟩
  have hrewrite : ∀ c, stress c
      • atomMatrix ((stressWalkedDesign design stress step hsizePos hstepped hstress).atom c)
      = (∑ d, (design.weight d - step * stress d))
        • (stress c • atomMatrix (design.atom c)) := by
    intro c
    show stress c
      • atomMatrix (Real.sqrt (∑ d, (design.weight d - step * stress d)) • design.atom c) = _
    rw [atomMatrix_smul, Real.sq_sqrt hmassPos.le, smul_comm]
  rw [Finset.sum_congr rfl fun c _ => hrewrite c, ← Finset.smul_sum, hstress, smul_zero]

/-- A step short enough to keep every perturbed weight positive exists. -/
theorem exists_safeStep (design : WeightedDesign size rank) (hsizePos : 0 < size)
    (stress : Fin size → ℝ) :
    ∃ step : ℝ, 0 < step ∧ ∀ c, 0 < design.weight c - step * stress c := by
  classical
  have hnonempty : (Finset.univ : Finset (Fin size)).Nonempty :=
    ⟨⟨0, hsizePos⟩, Finset.mem_univ _⟩
  obtain ⟨spreadLabel, -, hspread⟩ :=
    Finset.exists_max_image Finset.univ (fun c => |stress c|) hnonempty
  obtain ⟨lightLabel, -, hlight⟩ :=
    Finset.exists_min_image Finset.univ (fun c => design.weight c) hnonempty
  refine ⟨design.weight lightLabel / (2 * (|stress spreadLabel| + 1)), ?_, fun c => ?_⟩
  · exact div_pos (design.weight_pos lightLabel) (by positivity)
  · have hspreadBound : |stress c| ≤ |stress spreadLabel| := hspread c (Finset.mem_univ c)
    have hlightBound : design.weight lightLabel ≤ design.weight c :=
      hlight c (Finset.mem_univ c)
    have hlightPos : 0 < design.weight lightLabel := design.weight_pos lightLabel
    have hdenomPos : (0 : ℝ) < 2 * (|stress spreadLabel| + 1) := by positivity
    have hstressLe : stress c ≤ |stress spreadLabel| :=
      le_trans (le_abs_self _) hspreadBound
    have hstepPos : 0 < design.weight lightLabel / (2 * (|stress spreadLabel| + 1)) :=
      div_pos hlightPos hdenomPos
    have hproduct : design.weight lightLabel / (2 * (|stress spreadLabel| + 1)) * stress c
        ≤ design.weight lightLabel / (2 * (|stress spreadLabel| + 1))
          * (|stress spreadLabel| + 1) := by
      have : stress c ≤ |stress spreadLabel| + 1 := by linarith
      exact mul_le_mul_of_nonneg_left this hstepPos.le
    have hhalf : design.weight lightLabel / (2 * (|stress spreadLabel| + 1))
        * (|stress spreadLabel| + 1) = design.weight lightLabel / 2 := by
      field_simp
    rw [hhalf] at hproduct
    linarith

/-! ## The strict conclusion at six points -/

/-- **A STRESS OF NONZERO SUM STRICTLY DOMINATES.**  The upgrade of
`Gtz.exists_dominating_sixThree_of_stress`: if the stress's coordinate sum is
nonzero, the walk loses mass strictly and the pulled-back triple dominates
STRICTLY.  This is what a tie cannot survive. -/
theorem exists_posDef_sixThree_of_stress_sum_ne_zero (design : WeightedDesign 6 3)
    {stress : Fin 6 → ℝ} (hnonzero : stress ≠ 0)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0)
    (hsumNe : (∑ c, stress c) ≠ 0) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ (subsetSum design selected - 1).PosDef := by
  classical
  -- orient the stress so its coordinate sum is strictly positive
  obtain ⟨oriented, horientedNonzero, horientedStress, horientedSumPos⟩ :
      ∃ oriented : Fin 6 → ℝ, oriented ≠ 0
        ∧ (∑ c, oriented c • atomMatrix (design.atom c)) = 0 ∧ 0 < ∑ c, oriented c := by
    rcases lt_or_gt_of_ne hsumNe with hneg | hpos
    · refine ⟨-stress, neg_ne_zero.mpr hnonzero, ?_, ?_⟩
      · simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hstress, neg_zero]
      · simp only [Pi.neg_apply, Finset.sum_neg_distrib]
        linarith
    · exact ⟨stress, hnonzero, hstress, hpos⟩
  obtain ⟨step, hstepPos, hstepped⟩ := exists_safeStep design (by norm_num) oriented
  set shrunk := stressWalkedDesign design oriented step (by norm_num) hstepped horientedStress
    with hshrunk
  have hmassPos : 0 < ∑ d, (design.weight d - step * oriented d) :=
    Finset.sum_pos (fun d _ => hstepped d) ⟨0, Finset.mem_univ _⟩
  have hmassLaw : (∑ d, (design.weight d - step * oriented d))
      = 1 - step * ∑ d, oriented d := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, design.weight_sum_one]
  have hmassLtOne : (∑ d, (design.weight d - step * oriented d)) < 1 := by
    rw [hmassLaw]
    nlinarith
  obtain ⟨selected, hcard, hdominates⟩ :=
    exists_dominating_sixThree_of_stress shrunk horientedNonzero
      (stress_stressWalkedDesign design oriented step (by norm_num) hstepped horientedStress)
  refine ⟨selected, hcard, ?_⟩
  refine posDef_sub_one_of_smul_sub_one hmassPos hmassLtOne ?_
  have hsums := subsetSum_stressWalkedDesign design oriented step (by norm_num) hstepped
    horientedStress selected
  rw [← hsums]
  exact hdominates

/-! ## What a tie must therefore look like -/

/-- **EVERY STRESS OF A `(6,3)` TIE HAS COORDINATE SUM ZERO.**  Unconditional: the
input is `Gtz.gtzWeighted_of_le_five` through the shipped walk.  Dually, the
all-ones vector lies in the RANGE of the Hadamard-square Gram, since the stress
space is its kernel. -/
theorem sum_eq_zero_of_stress_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) {stress : Fin 6 → ℝ} (hnonzero : stress ≠ 0)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0) :
    (∑ c, stress c) = 0 := by
  by_contra hsumNe
  obtain ⟨selected, hcard, hposDef⟩ :=
    exists_posDef_sixThree_of_stress_sum_ne_zero design hnonzero hstress hsumNe
  exact htie.2 selected hcard hposDef

/-- **A PARALLEL PAIR OF A `(6,3)` TIE HAS UNIT RATIO.**  The two atoms have equal
length: the stress a parallel pair manufactures has coordinate sum `1 - ratio ^ 2`,
which the previous theorem forces to vanish.  This SHARPENS the hinge's own
conclusion — the parallel pair `Gtz.HingeHoldsAtSize` asks for, if it exists at
all, is automatically a pair of atoms of equal length. -/
theorem sq_eq_one_of_parallel_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) {keptLabel dropLabel : Fin 6} {ratio : ℝ}
    (hdistinct : keptLabel ≠ dropLabel)
    (hparallel : design.atom dropLabel = ratio • design.atom keptLabel) :
    ratio ^ 2 = 1 := by
  classical
  set stress : Fin 6 → ℝ := fun c =>
    (if c = dropLabel then (1 : ℝ) else 0) - (if c = keptLabel then ratio ^ 2 else 0)
    with hstressDef
  have hnonzero : stress ≠ 0 := by
    intro hzero
    have hentry : stress dropLabel = 0 := congrFun hzero dropLabel
    rw [hstressDef] at hentry
    simp only [if_neg (Ne.symm hdistinct)] at hentry
    norm_num at hentry
  have hstressParseval : (∑ c, stress c • atomMatrix (design.atom c)) = 0 := by
    have hdrop : atomMatrix (design.atom dropLabel)
        = ratio ^ 2 • atomMatrix (design.atom keptLabel) := by
      rw [hparallel, atomMatrix_smul]
    have hpointwise : ∀ c, stress c • atomMatrix (design.atom c)
        = (if c = dropLabel then (1 : ℝ) else 0) • atomMatrix (design.atom c)
          - (if c = keptLabel then ratio ^ 2 else 0) • atomMatrix (design.atom c) := by
      intro c
      rw [hstressDef, sub_smul]
    rw [Finset.sum_congr rfl fun c _ => hpointwise c, Finset.sum_sub_distrib]
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_pos]
    rw [hdrop, one_smul, sub_self]
  have hsumZero := sum_eq_zero_of_stress_of_isTie_sixThree design htie hnonzero hstressParseval
  have hsumValue : (∑ c, stress c) = 1 - ratio ^ 2 := by
    rw [hstressDef]
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_pos]
  rw [hsumValue] at hsumZero
  linarith

/-- **A STRESSED `(6,3)` TIE RESTRICTS TO A SMALLER TIE ON THE SAME VECTORS.**  The
shipped walk's shrink factor must be exactly one at a tie (any strict shrink would
make the pullback strictly dominating), so the reduced design's atoms are the
original vectors UNCHANGED, and it is itself a tie: weakly dominated by
`Gtz.gtzWeighted_of_le_five` and strictly dominated by nothing, since a strict
dominator would transport straight back up. -/
theorem exists_smallerTie_of_stress_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) {stress : Fin 6 → ℝ} (hnonzero : stress ≠ 0)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0) :
    ∃ smallSize : ℕ, smallSize < 6 ∧ ∃ smallDesign : WeightedDesign smallSize 3,
      ∃ inject : Fin smallSize → Fin 6, Function.Injective inject ∧
        (∀ i, smallDesign.atom i = design.atom (inject i)) ∧ IsTie smallDesign := by
  classical
  obtain ⟨shrink, hshrinkPos, hshrinkLe, smallSize, hsmallLt, smallDesign, inject, hinject,
    hatoms⟩ := exists_rescaledReducedDesign_of_stress design (by norm_num) hnonzero hstress
  have hsums : ∀ chosen : Finset (Fin smallSize), subsetSum smallDesign chosen
      = shrink • subsetSum design (chosen.image inject) := by
    intro chosen
    rw [subsetSum, subsetSum, Finset.sum_image fun x _ y _ hxy => hinject hxy, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hatoms i, atomMatrix_smul, Real.sq_sqrt hshrinkPos.le]
  obtain ⟨smallSelected, hsmallCard, hsmallDominates⟩ :=
    gtzWeighted_of_le_five smallSize 3 (by norm_num) (by omega) smallDesign
  -- a strict shrink would make the pullback strictly dominating, which a tie forbids
  have hshrinkOne : shrink = 1 := by
    rcases eq_or_lt_of_le hshrinkLe with heq | hlt
    · exact heq
    · exfalso
      refine htie.2 (smallSelected.image inject) ?_ ?_
      · rw [Finset.card_image_of_injective _ hinject, hsmallCard]
      · refine posDef_sub_one_of_smul_sub_one hshrinkPos hlt ?_
        rw [← hsums smallSelected]
        exact hsmallDominates
  have hatomsEq : ∀ i, smallDesign.atom i = design.atom (inject i) := by
    intro i
    rw [hatoms i, hshrinkOne, Real.sqrt_one, one_smul]
  refine ⟨smallSize, hsmallLt, smallDesign, inject, hinject, hatomsEq, ⟨smallSelected,
    hsmallCard, hsmallDominates⟩, fun chosen hchosenCard hchosenPosDef => ?_⟩
  refine htie.2 (chosen.image inject) ?_ ?_
  · rw [Finset.card_image_of_injective _ hinject, hchosenCard]
  · have hsameSum : subsetSum design (chosen.image inject) = subsetSum smallDesign chosen := by
      rw [subsetSum, subsetSum, Finset.sum_image fun x _ y _ hxy => hinject hxy]
      exact (Finset.sum_congr rfl fun i _ => by rw [hatomsEq i]).symm
    rw [hsameSum]
    exact hchosenPosDef

/-- **NO SQUARE TIE.**  At size equal to the rank the only three-subset is
everything, and the full excess `S_univ - I = Sum_c (1 - t_c) g_c g_c^T` is
STRICTLY positive definite as soon as there are two atoms
(`Gtz.posDef_fullExcess`).  So the descent above cannot bottom out at three
atoms. -/
theorem not_isTie_square (design : WeightedDesign 3 3) : ¬ IsTie design := fun htie =>
  htie.2 Finset.univ (by rw [Finset.card_univ, Fintype.card_fin])
    (posDef_fullExcess design (by norm_num))

/-- **THE DESCENT, SIZE-PINNED.**  The smaller tie a stressed `(6,3)` tie
restricts to carries FOUR or FIVE atoms: at least three by
`Gtz.rank_le_of_design`, and not exactly three by `not_isTie_square`. -/
theorem exists_smallerTie_size_four_or_five_of_stress_of_isTie_sixThree
    (design : WeightedDesign 6 3) (htie : IsTie design) {stress : Fin 6 → ℝ}
    (hnonzero : stress ≠ 0)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0) :
    ∃ smallSize : ℕ, (smallSize = 4 ∨ smallSize = 5) ∧
      ∃ smallDesign : WeightedDesign smallSize 3, ∃ inject : Fin smallSize → Fin 6,
        Function.Injective inject ∧
          (∀ i, smallDesign.atom i = design.atom (inject i)) ∧ IsTie smallDesign := by
  obtain ⟨smallSize, hsmallLt, smallDesign, inject, hinject, hatoms, hsmallTie⟩ :=
    exists_smallerTie_of_stress_of_isTie_sixThree design htie hnonzero hstress
  have hlower : 3 ≤ smallSize := rank_le_of_design smallDesign
  have hnotThree : smallSize ≠ 3 := by
    rintro rfl
    exact not_isTie_square smallDesign hsmallTie
  exact ⟨smallSize, by omega, smallDesign, inject, hinject, hatoms, hsmallTie⟩

/-! ## The narrowing -/

/-- A stress whose coordinate sum vanishes.  Dually — the stress space is the
kernel of the Hadamard-square Gram — this says the all-ones vector lies in that
Gram's RANGE. -/
def HasOnlyBalancedStress {size : ℕ} (design : WeightedDesign size 3) : Prop :=
  ∀ stress : Fin size → ℝ, stress ≠ 0 →
    (∑ c, stress c • atomMatrix (design.atom c)) = 0 → (∑ c, stress c) = 0

/-- **EVERY `(6,3)` TIE HAS ONLY BALANCED STRESSES.** -/
theorem hasOnlyBalancedStress_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) : HasOnlyBalancedStress design := by
  intro stress hnonzero hstress
  by_contra hsumNe
  obtain ⟨selected, hcard, hposDef⟩ :=
    exists_posDef_sixThree_of_stress_sum_ne_zero design hnonzero hstress hsumNe
  exact htie.2 selected hcard hposDef

/-- Tie-freeness asked only of the designs every one of whose stresses has
coordinate sum zero.  Weaker than `Gtz.StratumIsTieFree`, and by the strict stress
walk equivalent to it at six points. -/
def StratumIsTieFreeAtBalancedStress (pattern : LinePattern 6) : Prop :=
  ∀ design : WeightedDesign 6 3, HasLinePattern design pattern →
    HasOnlyBalancedStress design → ¬ IsTie design

/-- The narrowed obligation is genuinely weaker. -/
theorem stratumIsTieFreeAtBalancedStress_of_stratumIsTieFree {pattern : LinePattern 6}
    (hfree : StratumIsTieFree pattern) : StratumIsTieFreeAtBalancedStress pattern :=
  fun design hpattern _ => hfree design hpattern

/-- **THE THIRD NARROWING, unconditional at six points.**  A `(6,3)` ledger entry
may assume every stress of the design has coordinate sum zero.  Orthogonal to the
heavy narrowings of `Gtz.Design.StratumEmptinessLedger`: those constrain the atom
LENGTHS, this one constrains the DEPENDENCIES. -/
theorem stratumIsTieFree_of_balancedStress_sixThree {pattern : LinePattern 6}
    (hnarrowed : StratumIsTieFreeAtBalancedStress pattern) : StratumIsTieFree pattern :=
  fun design hpattern htie =>
    hnarrowed design hpattern (hasOnlyBalancedStress_of_isTie_sixThree design htie) htie

/-! ## The line-pair classes

`Gtz.exists_dominating_of_twoPlanes` manufactures a stress internally and throws
it away.  Kept, it feeds the strict walk. -/

/-- **A TWO-PLANE SPLIT MANUFACTURES A STRESS**, kept rather than consumed. -/
theorem exists_stress_of_twoPlanes (design : WeightedDesign 6 3)
    {firstNormal secondNormal : Fin 3 → ℝ} (hfirst : firstNormal ≠ 0)
    (hsecond : secondNormal ≠ 0)
    (hsplit : ∀ atomIndex, firstNormal ⬝ᵥ design.atom atomIndex = 0
      ∨ secondNormal ⬝ᵥ design.atom atomIndex = 0) :
    ∃ stress : Fin 6 → ℝ, stress ≠ 0
      ∧ (∑ c, stress c • atomMatrix (design.atom c)) = 0 :=
  exists_stress_of_commonQuadric design.atom (transpose_linePairForm firstNormal secondNormal)
    (linePairForm_ne_zero hfirst hsecond) fun atomIndex => by
      rw [quadForm_linePairForm]
      rcases hsplit atomIndex with hleft | hright
      · rw [hleft, zero_mul, mul_zero]
      · rw [hright, mul_zero, mul_zero]

/-- **THE STRICT EXCLUSION.**  An unbalanced stress kills a tie outright.
`Gtz.exists_dominating_of_twoPlanes` reaches only weak domination, which a tie
satisfies; this is the strict form, and it needs no geometry at all — the
two-plane hypotheses enter only to MANUFACTURE the stress. -/
theorem not_isTie_of_unbalancedStress (design : WeightedDesign 6 3)
    (hunbalanced : ¬ HasOnlyBalancedStress design) : ¬ IsTie design :=
  fun htie => hunbalanced (hasOnlyBalancedStress_of_isTie_sixThree design htie)

/-! ## The Bezout brick

A conic meeting a line in three points contains the line.  In this vocabulary: a
symmetric form annihilating two independent vectors and one combination of them
with both coefficients nonzero annihilates their whole span.  Two lines of
bilinear expansion, no frame, no projective line, no determinant.

This is what separates the nine six-point classes into those whose lines admit a
covering pair of planes and those whose lines do not, because a common quadric of
a class with a three-point line must contain that line's plane and is therefore a
LINE PAIR.  It is stated size-generically and is not consumed below, where the
three covering pairs are exhibited directly. -/

/-- The symmetric bilinear form of a symmetric matrix, polarised. -/
theorem quadForm_add_expand {rank : ℕ} (form : Matrix (Fin rank) (Fin rank) ℝ)
    (hsymmetric : formᵀ = form) (leftScale rightScale : ℝ)
    (leftVec rightVec : Fin rank → ℝ) :
    (leftScale • leftVec + rightScale • rightVec)
        ⬝ᵥ (form *ᵥ (leftScale • leftVec + rightScale • rightVec))
      = leftScale ^ 2 * (leftVec ⬝ᵥ (form *ᵥ leftVec))
        + 2 * (leftScale * rightScale) * (leftVec ⬝ᵥ (form *ᵥ rightVec))
        + rightScale ^ 2 * (rightVec ⬝ᵥ (form *ᵥ rightVec)) := by
  have hcross : rightVec ⬝ᵥ (form *ᵥ leftVec) = leftVec ⬝ᵥ (form *ᵥ rightVec) := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymmetric, dotProduct_comm]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hcross]
  ring

/-- **A QUADRIC THROUGH THREE COLLINEAR POINTS CONTAINS THE LINE.**  If a
symmetric form kills two vectors and kills a combination of them with BOTH
coefficients nonzero, it kills their whole span.  The middle step is the only
content: the combination's quadratic value collapses to the cross term. -/
theorem quadForm_eq_zero_of_span_of_three_collinear {rank : ℕ}
    {form : Matrix (Fin rank) (Fin rank) ℝ} (hsymmetric : formᵀ = form)
    {leftVec rightVec : Fin rank → ℝ} {leftScale rightScale : ℝ}
    (hleftScale : leftScale ≠ 0) (hrightScale : rightScale ≠ 0)
    (hleftZero : leftVec ⬝ᵥ (form *ᵥ leftVec) = 0)
    (hrightZero : rightVec ⬝ᵥ (form *ᵥ rightVec) = 0)
    (hthirdZero : (leftScale • leftVec + rightScale • rightVec)
      ⬝ᵥ (form *ᵥ (leftScale • leftVec + rightScale • rightVec)) = 0)
    (probeLeft probeRight : ℝ) :
    (probeLeft • leftVec + probeRight • rightVec)
      ⬝ᵥ (form *ᵥ (probeLeft • leftVec + probeRight • rightVec)) = 0 := by
  have hcrossZero : leftVec ⬝ᵥ (form *ᵥ rightVec) = 0 := by
    have hexpand := quadForm_add_expand form hsymmetric leftScale rightScale leftVec rightVec
    rw [hthirdZero, hleftZero, hrightZero] at hexpand
    have hprod : (2 : ℝ) * (leftScale * rightScale) ≠ 0 :=
      mul_ne_zero two_ne_zero (mul_ne_zero hleftScale hrightScale)
    have hzero : 2 * (leftScale * rightScale) * (leftVec ⬝ᵥ (form *ᵥ rightVec)) = 0 := by
      linear_combination -hexpand
    exact (mul_eq_zero.mp hzero).resolve_left hprod
  rw [quadForm_add_expand form hsymmetric probeLeft probeRight leftVec rightVec,
    hleftZero, hrightZero, hcrossZero]
  ring

/-! ## The narrowing, at all four ledger shapes

`Gtz.StratumIsTieFreeAmongHeavy` is what
`Gtz.hingeHoldsAtSize_of_linearSpaceEnumeration_sixThree` asks of each entry, and
`Gtz.stratumIsTieFreeAmongHeavy_of_allHeavy_and_unitLeverage` splits it into the
`Gtz.AllHeavy` interior and the unit-leverage face.  Each of those three shapes,
and the unnarrowed `Gtz.StratumIsTieFree`, gains `HasOnlyBalancedStress` for
free at six points.  Every implication below is one application of
`hasOnlyBalancedStress_of_isTie_sixThree`. -/

/-- The ledger's own obligation, with balanced stress assumed. -/
def StratumIsTieFreeAmongHeavyAtBalancedStress (pattern : LinePattern 6) : Prop :=
  ∀ design : WeightedDesign 6 3, HasLinePattern design pattern →
    (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) → HasOnlyBalancedStress design →
      ¬ IsTie design

/-- The strict-heavy half of the split, with balanced stress assumed. -/
def StratumIsTieFreeAmongAllHeavyAtBalancedStress (pattern : LinePattern 6) : Prop :=
  ∀ design : WeightedDesign 6 3, HasLinePattern design pattern → AllHeavy design →
    HasOnlyBalancedStress design → ¬ IsTie design

/-- The unit-leverage face of the split, with balanced stress assumed. -/
def StratumIsTieFreeAtUnitLeverageAtBalancedStress (pattern : LinePattern 6) : Prop :=
  ∀ design : WeightedDesign 6 3, HasLinePattern design pattern →
    (∃ label : Fin 6, leverageOf (design.atom label) = 1) → HasOnlyBalancedStress design →
      ¬ IsTie design

/-- **THE NARROWING AT THE LEDGER'S OWN OBLIGATION.**  A `(6,3)` entry may assume
heaviness AND balanced stress at once, with no hypothesis anywhere. -/
theorem stratumIsTieFreeAmongHeavy_of_balancedStress_sixThree {pattern : LinePattern 6}
    (hnarrowed : StratumIsTieFreeAmongHeavyAtBalancedStress pattern) :
    StratumIsTieFreeAmongHeavy pattern :=
  fun design hpattern hheavy htie =>
    hnarrowed design hpattern hheavy (hasOnlyBalancedStress_of_isTie_sixThree design htie) htie

/-- The narrowing on the strict-heavy half of the split. -/
theorem stratumIsTieFreeAmongAllHeavy_of_balancedStress_sixThree {pattern : LinePattern 6}
    (hnarrowed : StratumIsTieFreeAmongAllHeavyAtBalancedStress pattern) :
    StratumIsTieFreeAmongAllHeavy pattern :=
  fun design hpattern hheavy htie =>
    hnarrowed design hpattern hheavy (hasOnlyBalancedStress_of_isTie_sixThree design htie) htie

/-- The narrowing on the unit-leverage face of the split. -/
theorem stratumIsTieFreeAtUnitLeverage_of_balancedStress_sixThree {pattern : LinePattern 6}
    (hnarrowed : StratumIsTieFreeAtUnitLeverageAtBalancedStress pattern) :
    StratumIsTieFreeAtUnitLeverage pattern :=
  fun design hpattern hunit htie =>
    hnarrowed design hpattern hunit (hasOnlyBalancedStress_of_isTie_sixThree design htie) htie

/-- **BOTH HALVES OF THE SPLIT, BOTH NARROWED.**  The sharpest form of a six-point
ledger entry this file reaches: the strict-heavy interior and the unit-leverage
face, each additionally allowed to assume every stress balanced. -/
theorem stratumIsTieFreeAmongHeavy_of_allHeavy_and_unitLeverage_atBalancedStress
    {pattern : LinePattern 6}
    (hallHeavyFree : StratumIsTieFreeAmongAllHeavyAtBalancedStress pattern)
    (hunitFree : StratumIsTieFreeAtUnitLeverageAtBalancedStress pattern) :
    StratumIsTieFreeAmongHeavy pattern :=
  stratumIsTieFreeAmongHeavy_of_allHeavy_and_unitLeverage
    (stratumIsTieFreeAmongAllHeavy_of_balancedStress_sixThree hallHeavyFree)
    (stratumIsTieFreeAtUnitLeverage_of_balancedStress_sixThree hunitFree)

/-! ## The entries whose pattern forces a stress

Two plane normals covering all six labels give a line-pair quadric annihilating
every atom, hence a stress.  `Gtz.exists_lineNormal_of_hasLinePattern` produces a
normal for any label set the pattern makes coplanar, and the non-vanishing comes
from a witness triple the pattern leaves independent.  Three of the eight open
entries admit such a pair. -/

/-- The entries whose pattern alone manufactures a stress on every design of the
stratum. -/
def PatternForcesStress (pattern : LinePattern 6) : Prop :=
  ∀ design : WeightedDesign 6 3, HasLinePattern design pattern →
    ∃ stress : Fin 6 → ℝ, stress ≠ 0 ∧ (∑ c, stress c • atomMatrix (design.atom c)) = 0

/-- **ENTRY `[[0,1,2],[3,4,5]]`, two disjoint three-point lines.**  Both normals
are lines of the pattern. -/
theorem patternForcesStress_twoDisjointLines :
    PatternForcesStress (lineFamilyPattern [[0, 1, 2], [3, 4, 5]]) := by
  intro design hpattern
  obtain ⟨firstNormal, hfirstNe, hfirstPlane⟩ :=
    exists_lineNormal_of_hasLinePattern design hpattern ({0, 1, 2} : Finset (Fin 6))
      0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨secondNormal, hsecondNe, hsecondPlane⟩ :=
    exists_lineNormal_of_hasLinePattern design hpattern ({3, 4, 5} : Finset (Fin 6))
      3 4 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine exists_stress_of_twoPlanes design hfirstNe hsecondNe fun atomIndex => ?_
  by_cases hlow : atomIndex ∈ ({0, 1, 2} : Finset (Fin 6))
  · exact Or.inl (by rw [dotProduct_comm]; exact hfirstPlane atomIndex hlow)
  · refine Or.inr ?_
    rw [dotProduct_comm]
    refine hsecondPlane atomIndex ?_
    revert hlow
    fin_cases atomIndex <;> decide

/-- **ENTRY `[[0,1,2,3]]`, one four-point line — and NO second line.**  The second
plane is not a line of the pattern at all: any two vectors lie in a plane, so the
two labels off the line supply a normal, and
`Gtz.exists_lineNormal_of_hasLinePattern` returns it because no line of the
pattern carries both of them.  Its coplanarity hypothesis is vacuous on a
two-element set. -/
theorem patternForcesStress_fourPointLine :
    PatternForcesStress (lineFamilyPattern [[0, 1, 2, 3]]) := by
  intro design hpattern
  obtain ⟨firstNormal, hfirstNe, hfirstPlane⟩ :=
    exists_lineNormal_of_hasLinePattern design hpattern ({0, 1, 2, 3} : Finset (Fin 6))
      0 1 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨secondNormal, hsecondNe, hsecondPlane⟩ :=
    exists_lineNormal_of_hasLinePattern design hpattern ({4, 5} : Finset (Fin 6))
      4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine exists_stress_of_twoPlanes design hfirstNe hsecondNe fun atomIndex => ?_
  by_cases hlow : atomIndex ∈ ({0, 1, 2, 3} : Finset (Fin 6))
  · exact Or.inl (by rw [dotProduct_comm]; exact hfirstPlane atomIndex hlow)
  · refine Or.inr ?_
    rw [dotProduct_comm]
    refine hsecondPlane atomIndex ?_
    revert hlow
    fin_cases atomIndex <;> decide

/-- **ENTRY `[[0,1,2,3],[0,4,5]]`, a four-point line and a three-point line.**
Both normals are lines of the pattern, and together the two lines cover every
label. -/
theorem patternForcesStress_fourPointLineWithThreePointLine :
    PatternForcesStress (lineFamilyPattern [[0, 1, 2, 3], [0, 4, 5]]) := by
  intro design hpattern
  obtain ⟨firstNormal, hfirstNe, hfirstPlane⟩ :=
    exists_lineNormal_of_hasLinePattern design hpattern ({0, 1, 2, 3} : Finset (Fin 6))
      1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨secondNormal, hsecondNe, hsecondPlane⟩ :=
    exists_lineNormal_of_hasLinePattern design hpattern ({0, 4, 5} : Finset (Fin 6))
      4 5 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine exists_stress_of_twoPlanes design hfirstNe hsecondNe fun atomIndex => ?_
  by_cases hlow : atomIndex ∈ ({0, 1, 2, 3} : Finset (Fin 6))
  · exact Or.inl (by rw [dotProduct_comm]; exact hfirstPlane atomIndex hlow)
  · refine Or.inr ?_
    rw [dotProduct_comm]
    refine hsecondPlane atomIndex ?_
    revert hlow
    fin_cases atomIndex <;> decide

/-- **A TIE ON A STRESS-FORCING ENTRY CARRIES A NONZERO BALANCED STRESS.**  The
pattern supplies the stress and the strict walk forbids it being unbalanced, so
what such an entry still owes is not "no tie on the stratum" but "no tie on the
sublocus where the stress balances". -/
theorem exists_nonzero_balanced_stress_of_isTie_of_forcesStress {pattern : LinePattern 6}
    (hforces : PatternForcesStress pattern) (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design pattern) (htie : IsTie design) :
    ∃ stress : Fin 6 → ℝ, stress ≠ 0
      ∧ (∑ c, stress c • atomMatrix (design.atom c)) = 0 ∧ (∑ c, stress c) = 0 := by
  obtain ⟨stress, hnonzero, hstress⟩ := hforces design hpattern
  exact ⟨stress, hnonzero, hstress,
    hasOnlyBalancedStress_of_isTie_sixThree design htie stress hnonzero hstress⟩

/-! ## The assembly

The hinge at six points from the two open inputs in their sharpest form: six
combinatorial classes, and eight tie-freeness obligations each of which may
assume heaviness and balanced stress.  BOTH inputs are undischarged. -/

/-- **THE HINGE AT SIX POINTS, BOTH INPUTS NARROWED.**  `hmulti` is catalogue
`#2` through `#7` and `hresidual` is the eight ledger entries; neither is proved
anywhere.  What this theorem records is the shape they have been reduced to. -/
theorem hingeHoldsAtSize_of_multiLineCases_balancedStress_sixThree
    (hmulti : LinearSpaceMultiLineCasesSix)
    (hresidual : ∀ lines ∈ lineFamiliesSix, ¬ IsNearPencilFamily lines →
      StratumIsTieFreeAmongHeavyAtBalancedStress (lineFamilyPattern lines)) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_multiLineCases_sixThree hmulti fun lines hlines hnotNearPencil =>
    stratumIsTieFreeAmongHeavy_of_balancedStress_sixThree (hresidual lines hlines hnotNearPencil)

/-- The same with the unit-leverage split applied to every entry: sixteen
obligations, each narrowed by heaviness and by balanced stress. -/
theorem hingeHoldsAtSize_of_multiLineCases_splitBalancedStress_sixThree
    (hmulti : LinearSpaceMultiLineCasesSix)
    (hallHeavyFree : ∀ lines ∈ lineFamiliesSix, ¬ IsNearPencilFamily lines →
      StratumIsTieFreeAmongAllHeavyAtBalancedStress (lineFamilyPattern lines))
    (hunitFree : ∀ lines ∈ lineFamiliesSix, ¬ IsNearPencilFamily lines →
      StratumIsTieFreeAtUnitLeverageAtBalancedStress (lineFamilyPattern lines)) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_multiLineCases_sixThree hmulti fun lines hlines hnotNearPencil =>
    stratumIsTieFreeAmongHeavy_of_allHeavy_and_unitLeverage_atBalancedStress
      (hallHeavyFree lines hlines hnotNearPencil) (hunitFree lines hlines hnotNearPencil)

/-! ## Non-vacuity

The three stress-forcing entries are genuine members of `Gtz.lineFamiliesSix` and
none of them is the near pencil, so each really is one of the eight obligations
the ledger asks about, and `PatternForcesStress` really does apply to it. -/

example : [[(0 : Fin 6), 1, 2], [3, 4, 5]] ∈ lineFamiliesSix ∧
    ¬ IsNearPencilFamily [[(0 : Fin 6), 1, 2], [3, 4, 5]] := by decide

example : [[(0 : Fin 6), 1, 2, 3]] ∈ lineFamiliesSix ∧
    ¬ IsNearPencilFamily [[(0 : Fin 6), 1, 2, 3]] := by decide

example : [[(0 : Fin 6), 1, 2, 3], [0, 4, 5]] ∈ lineFamiliesSix ∧
    ¬ IsNearPencilFamily [[(0 : Fin 6), 1, 2, 3], [0, 4, 5]] := by decide

end Gtz
