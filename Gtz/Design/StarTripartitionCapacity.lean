/-
# The star tripartition certificate and the free-sub-star budget

This module makes the multi-edge Farkas layer of the forced box system
PARAMETRIC on the exceptional locus.  Three things are proved.

## 1. The star tripartition capacity theorem

A multiplier vector supported on the five edges through one atom -- a STAR
dual -- has an aggregate that vanishes on every triple missing the apex, so
its whole content lives on the LINK of the apex.  Writing the multiplier on
edge `(apex, i)` as `weight i * chi i`, the aggregate of the triple
`{apex, i, j}` is `weight i * weight j * (chi i + chi j)`: a TWO-TERM sum.

`Gtz.exists_nonneg_edgeTripleValue_of_starTripartitionDeficit` says that when
the star deficit is strict, some FORCED slot of the link carries a nonnegative
triple value.  The proof is the value-form erase law at the five edges through
the apex, symmetrised over the link, plus one triangle bound -- no genericity,
no heaviness, no exceptionality, no failure hypothesis, at every ambient size.

Realness enters exactly where it enters the shipped single-edge capacity
lemma: the design's own triple values solve the erase law over `ℝ`, so the
equation value is pinned inside the box `±∑ w·r`.  Over `ℂ` the triple value
carries a free phase, only `|t| ≤ r` survives, and the trine sits strictly
inside the box with nothing to contradict.

## 2. Why the tripartition alphabet `{0, 1, -1}` is exhaustive for stars

`Gtz.thresholdSign_add_nonneg_mul` and `Gtz.thresholdSign_add_eq_zero` are the
core of the following statement, proved on paper and measured this slot: if
the star objective is positive at ANY real `chi`, it is positive at some
`chi` valued in `{0, 1, -1}`.  For `t ≥ 0` put
`chi^t = thresholdSign · t`; then `chi = ∫₀^∞ chi^t dt` and a TWO-term sum
cannot change sign under thresholding, so both `chi i + chi j` and
`|chi i + chi j|` integrate, the objective integrates, and some integrand is
positive.  The integrands are exactly the tripartition vectors.

`Gtz.exists_thresholdSign_triple_sum_neg` is the matching NEGATIVE result: the
argument is genuinely special to stars, because a THREE-term sum does change
sign under thresholding.  That is why the small supports of the measured dual
library concentrate on stars.

## 3. The free-sub-star budget

`Gtz.exists_nonneg_edgeTripleValue_of_freeStarBudget` replaces the free star
slots by ONE Cauchy-Schwarz bound against the two free sub-star budgets,
leaving the forced slots exact.  It is the split form of the whole-star budget
test: bounding only the free part and keeping the forced part exact is weaker
as a hypothesis and therefore strictly stronger as a test.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Reduction.BranchTransferConstants
import Gtz.Design.EraseSystem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Finset

variable {sizeIndex : ℕ}

/-! ## The link of an atom, and the symmetry of the triple value in it -/

/-- The triple value through a fixed apex does not see the order of the two
link atoms: `p_apex,i · p_apex,j · p_j,i` is symmetric under swapping `i` and
`j` because the pairing is. -/
theorem edgeTripleValue_link_comm (D : WeightedDesign sizeIndex 3)
    (apex linkFirst linkSecond : Fin sizeIndex) :
    edgeTripleValue D apex linkFirst linkSecond
      = edgeTripleValue D apex linkSecond linkFirst := by
  simp only [edgeTripleValue]
  rw [atomPairing_comm D linkFirst linkSecond]
  ring

/-- **The symmetrised link law.**  Summing the value-form erase law at the
edges through the apex, each weighted by `weight i * chi i`, and adding the
result to its own transpose, gives the link sum with the SYMMETRIC coefficient
`chi i + chi j`.  This is the only place the erase law is consumed. -/
theorem sum_link_symmetric_coefficient_mul_edgeTripleValue
    (D : WeightedDesign sizeIndex 3) (apex : Fin sizeIndex)
    (coefficient : Fin sizeIndex → ℝ) :
    ∑ linkFirst ∈ Finset.univ.erase apex,
        ∑ linkSecond ∈ (Finset.univ.erase apex).erase linkFirst,
          (coefficient linkFirst + coefficient linkSecond)
            * (D.weight linkFirst
              * (D.weight linkSecond
                * edgeTripleValue D apex linkFirst linkSecond))
      = 2 * ∑ linkFirst ∈ Finset.univ.erase apex,
          coefficient linkFirst * (D.weight linkFirst
            * (atomPairing D apex linkFirst ^ 2
              * (1 - atomShare D apex - atomShare D linkFirst))) := by
  classical
  set link : Finset (Fin sizeIndex) := Finset.univ.erase apex with hlink
  have hownTerm :
      ∑ linkFirst ∈ link, ∑ linkSecond ∈ link.erase linkFirst,
          coefficient linkFirst
            * (D.weight linkFirst
              * (D.weight linkSecond
                * edgeTripleValue D apex linkFirst linkSecond))
        = ∑ linkFirst ∈ link,
            coefficient linkFirst * (D.weight linkFirst
              * (atomPairing D apex linkFirst ^ 2
                * (1 - atomShare D apex - atomShare D linkFirst))) := by
    refine Finset.sum_congr rfl fun linkFirst hfirst => ?_
    have hne : apex ≠ linkFirst := (Finset.ne_of_mem_erase hfirst).symm
    have hlaw := sum_erasePair_weight_mul_edgeTripleValue D hne
    rw [← Finset.mul_sum, ← Finset.mul_sum, hlink, hlaw]
  have hswapTerm :
      ∑ linkFirst ∈ link, ∑ linkSecond ∈ link.erase linkFirst,
          coefficient linkSecond
            * (D.weight linkFirst
              * (D.weight linkSecond
                * edgeTripleValue D apex linkFirst linkSecond))
        = ∑ linkFirst ∈ link, ∑ linkSecond ∈ link.erase linkFirst,
            coefficient linkFirst
              * (D.weight linkFirst
                * (D.weight linkSecond
                  * edgeTripleValue D apex linkFirst linkSecond)) := by
    refine (Finset.sum_comm' (s := link) (t := fun outer => link.erase outer)
      (t' := link) (s' := fun inner => link.erase inner) ?_).trans ?_
    · intro outer inner
      simp only [Finset.mem_erase]
      constructor
      · rintro ⟨houter, hne, hinner⟩
        exact ⟨⟨Ne.symm hne, houter⟩, hinner⟩
      · rintro ⟨⟨hne, houter⟩, hinner⟩
        exact ⟨houter, Ne.symm hne, hinner⟩
    · refine Finset.sum_congr rfl fun linkFirst _ => ?_
      refine Finset.sum_congr rfl fun linkSecond _ => ?_
      rw [edgeTripleValue_link_comm D apex linkSecond linkFirst]
      ring
  have hexpand :
      ∑ linkFirst ∈ link, ∑ linkSecond ∈ link.erase linkFirst,
          (coefficient linkFirst + coefficient linkSecond)
            * (D.weight linkFirst
              * (D.weight linkSecond
                * edgeTripleValue D apex linkFirst linkSecond))
        = (∑ linkFirst ∈ link, ∑ linkSecond ∈ link.erase linkFirst,
            coefficient linkFirst
              * (D.weight linkFirst
                * (D.weight linkSecond
                  * edgeTripleValue D apex linkFirst linkSecond)))
          + ∑ linkFirst ∈ link, ∑ linkSecond ∈ link.erase linkFirst,
              coefficient linkSecond
                * (D.weight linkFirst
                  * (D.weight linkSecond
                    * edgeTripleValue D apex linkFirst linkSecond)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun linkFirst _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun linkSecond _ => ?_
    ring
  rw [hexpand, hswapTerm, hownTerm]
  ring

/-! ## The star tripartition capacity theorem -/

/-- **THE STAR CAPACITY THEOREM.**  Fix an apex atom and a real coefficient on
every atom.  Suppose that, over the link of the apex, the free slots' total
mass measured with the SYMMETRIC coefficient `|chi i + chi j|` is strictly
less than twice the coefficient-weighted erase requirement plus the forced
slots' mass measured with the signed coefficient `chi i + chi j`.  Then some
forced slot of the link carries a nonnegative triple value.

`forcedLink linkFirst` is the forced part of the link seen from `linkFirst`;
the statement does not need it to be symmetric, since both orientations of a
pair are summed independently.

The coefficient is an ARBITRARY real function.  The measured content of this
slot is that on the exceptional locus the alphabet `{0, 1, -1}` already
suffices -- see `Gtz.thresholdSign_add_nonneg_mul`. -/
theorem exists_nonneg_edgeTripleValue_of_starTripartitionDeficit
    (D : WeightedDesign sizeIndex 3) (apex : Fin sizeIndex)
    (coefficient : Fin sizeIndex → ℝ)
    (forcedLink : Fin sizeIndex → Finset (Fin sizeIndex))
    (hsubset : ∀ linkFirst ∈ Finset.univ.erase apex,
      forcedLink linkFirst ⊆ (Finset.univ.erase apex).erase linkFirst)
    (hdeficit :
      ∑ linkFirst ∈ Finset.univ.erase apex,
          ∑ linkSecond ∈ ((Finset.univ.erase apex).erase linkFirst)
              \ forcedLink linkFirst,
            |coefficient linkFirst + coefficient linkSecond|
              * (D.weight linkFirst
                * (D.weight linkSecond
                  * |edgeTripleValue D apex linkFirst linkSecond|))
        < 2 * (∑ linkFirst ∈ Finset.univ.erase apex,
              coefficient linkFirst * (D.weight linkFirst
                * (atomPairing D apex linkFirst ^ 2
                  * (1 - atomShare D apex - atomShare D linkFirst))))
          + ∑ linkFirst ∈ Finset.univ.erase apex,
              ∑ linkSecond ∈ forcedLink linkFirst,
                (coefficient linkFirst + coefficient linkSecond)
                  * (D.weight linkFirst
                    * (D.weight linkSecond
                      * |edgeTripleValue D apex linkFirst linkSecond|))) :
    ∃ linkFirst ∈ Finset.univ.erase apex, ∃ linkSecond ∈ forcedLink linkFirst,
      0 ≤ edgeTripleValue D apex linkFirst linkSecond := by
  classical
  by_contra hall
  push Not at hall
  set link : Finset (Fin sizeIndex) := Finset.univ.erase apex with hlink
  -- the symmetrised link law
  have hlaw := sum_link_symmetric_coefficient_mul_edgeTripleValue D apex
    coefficient
  -- split every inner sum into its free and forced parts
  have hsplit : ∀ linkFirst ∈ link,
      ∑ linkSecond ∈ (link.erase linkFirst) \ forcedLink linkFirst,
          (coefficient linkFirst + coefficient linkSecond)
            * (D.weight linkFirst
              * (D.weight linkSecond
                * edgeTripleValue D apex linkFirst linkSecond))
        + ∑ linkSecond ∈ forcedLink linkFirst,
            (coefficient linkFirst + coefficient linkSecond)
              * (D.weight linkFirst
                * (D.weight linkSecond
                  * edgeTripleValue D apex linkFirst linkSecond))
      = ∑ linkSecond ∈ link.erase linkFirst,
          (coefficient linkFirst + coefficient linkSecond)
            * (D.weight linkFirst
              * (D.weight linkSecond
                * edgeTripleValue D apex linkFirst linkSecond)) :=
    fun linkFirst hfirst => Finset.sum_sdiff (hsubset linkFirst hfirst)
  -- the forced slots read as minus their magnitude
  have hforced : ∀ linkFirst ∈ link,
      ∑ linkSecond ∈ forcedLink linkFirst,
          (coefficient linkFirst + coefficient linkSecond)
            * (D.weight linkFirst
              * (D.weight linkSecond
                * edgeTripleValue D apex linkFirst linkSecond))
        = -∑ linkSecond ∈ forcedLink linkFirst,
            (coefficient linkFirst + coefficient linkSecond)
              * (D.weight linkFirst
                * (D.weight linkSecond
                  * |edgeTripleValue D apex linkFirst linkSecond|)) := by
    intro linkFirst hfirst
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun linkSecond hsecond => ?_
    rw [abs_of_neg (hall linkFirst hfirst linkSecond hsecond)]
    ring
  -- the free slots are bounded above by their magnitude
  have hfree : ∀ linkFirst ∈ link,
      ∑ linkSecond ∈ (link.erase linkFirst) \ forcedLink linkFirst,
          (coefficient linkFirst + coefficient linkSecond)
            * (D.weight linkFirst
              * (D.weight linkSecond
                * edgeTripleValue D apex linkFirst linkSecond))
        ≤ ∑ linkSecond ∈ (link.erase linkFirst) \ forcedLink linkFirst,
            |coefficient linkFirst + coefficient linkSecond|
              * (D.weight linkFirst
                * (D.weight linkSecond
                  * |edgeTripleValue D apex linkFirst linkSecond|)) := by
    intro linkFirst _
    refine Finset.sum_le_sum fun linkSecond _ => ?_
    have hweightFirst := (D.weight_pos linkFirst).le
    have hweightSecond := (D.weight_pos linkSecond).le
    have hbound :
        |(coefficient linkFirst + coefficient linkSecond)
            * (D.weight linkFirst
              * (D.weight linkSecond
                * edgeTripleValue D apex linkFirst linkSecond))|
          = |coefficient linkFirst + coefficient linkSecond|
            * (D.weight linkFirst
              * (D.weight linkSecond
                * |edgeTripleValue D apex linkFirst linkSecond|)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hweightFirst,
        abs_of_nonneg hweightSecond]
    have := le_abs_self
      ((coefficient linkFirst + coefficient linkSecond)
        * (D.weight linkFirst
          * (D.weight linkSecond
            * edgeTripleValue D apex linkFirst linkSecond)))
    rw [hbound] at this
    exact this
  -- assemble
  have hsumSplit :
      ∑ linkFirst ∈ link,
          (∑ linkSecond ∈ (link.erase linkFirst) \ forcedLink linkFirst,
              (coefficient linkFirst + coefficient linkSecond)
                * (D.weight linkFirst
                  * (D.weight linkSecond
                    * edgeTripleValue D apex linkFirst linkSecond))
            + ∑ linkSecond ∈ forcedLink linkFirst,
                (coefficient linkFirst + coefficient linkSecond)
                  * (D.weight linkFirst
                    * (D.weight linkSecond
                      * edgeTripleValue D apex linkFirst linkSecond)))
        = 2 * ∑ linkFirst ∈ link,
            coefficient linkFirst * (D.weight linkFirst
              * (atomPairing D apex linkFirst ^ 2
                * (1 - atomShare D apex - atomShare D linkFirst))) := by
    rw [← hlaw]
    exact Finset.sum_congr rfl fun linkFirst hfirst => hsplit linkFirst hfirst
  rw [Finset.sum_add_distrib] at hsumSplit
  rw [Finset.sum_congr rfl hforced] at hsumSplit
  have hfreeTotal :
      ∑ linkFirst ∈ link,
          ∑ linkSecond ∈ (link.erase linkFirst) \ forcedLink linkFirst,
            (coefficient linkFirst + coefficient linkSecond)
              * (D.weight linkFirst
                * (D.weight linkSecond
                  * edgeTripleValue D apex linkFirst linkSecond))
        ≤ ∑ linkFirst ∈ link,
            ∑ linkSecond ∈ (link.erase linkFirst) \ forcedLink linkFirst,
              |coefficient linkFirst + coefficient linkSecond|
                * (D.weight linkFirst
                  * (D.weight linkSecond
                    * |edgeTripleValue D apex linkFirst linkSecond|)) :=
    Finset.sum_le_sum fun linkFirst hfirst => hfree linkFirst hfirst
  rw [Finset.sum_neg_distrib] at hsumSplit
  linarith [hsumSplit, hfreeTotal, hdeficit]

/-! ## Why the tripartition alphabet is exhaustive for star duals -/

/-- The threshold sign of a real at level `t`: the `{0, 1, -1}`-valued layer
of the layer-cake decomposition `x = ∫₀^∞ thresholdSign x t dt`. -/
noncomputable def thresholdSign (value threshold : ℝ) : ℝ :=
  if threshold < value then 1 else if value < -threshold then -1 else 0

/-- **THE TWO-TERM THRESHOLD LEMMA.**  A two-term sum never changes sign under
thresholding: the threshold layer of `x + y` is zero or carries the sign of
`x + y`.  This is the whole reason the tripartition alphabet is exhaustive for
STAR duals, whose triple aggregates are two-term sums. -/
theorem thresholdSign_add_nonneg_mul (first second threshold : ℝ)
    (hthreshold : 0 ≤ threshold) :
    0 ≤ (first + second)
      * (thresholdSign first threshold + thresholdSign second threshold) := by
  unfold thresholdSign
  split_ifs <;> nlinarith

/-- The companion: a two-term sum that vanishes has vanishing threshold layer
at every level, so the decomposition never creates a cost where there was
none. -/
theorem thresholdSign_add_eq_zero (first second threshold : ℝ)
    (hthreshold : 0 ≤ threshold) (hsum : first + second = 0) :
    thresholdSign first threshold + thresholdSign second threshold = 0 := by
  unfold thresholdSign
  split_ifs <;> linarith

/-- **THE NEGATIVE CONTROL, IN KERNEL.**  A THREE-term sum does change sign
under thresholding: `3 + (-1) + (-1) = 1 > 0` while its layer at level `1/2`
sums to `-1`.  So the exhaustiveness argument above is genuinely special to
star duals, and a general multi-edge dual has no tripartition normal form.
This is why the measured small supports concentrate on stars. -/
theorem exists_thresholdSign_triple_sum_neg :
    ∃ first second third threshold : ℝ, 0 ≤ threshold
      ∧ 0 < first + second + third
      ∧ thresholdSign first threshold + thresholdSign second threshold
          + thresholdSign third threshold < 0 := by
  refine ⟨3, -1, -1, 1 / 2, by norm_num, by norm_num, ?_⟩
  unfold thresholdSign
  norm_num

/-! ## The free-sub-star budget -/

/-- The Cauchy-Schwarz bound behind the split budget test: the free star
slots' total magnitude is controlled by the two FREE sub-star budgets, with
the edge pairing pulled out.  The forced slots never enter. -/
theorem sum_weight_mul_abs_edgeTripleValue_sq_le_freeBudget
    (D : WeightedDesign sizeIndex 3) (edgeFirst edgeSecond : Fin sizeIndex)
    (freeStar : Finset (Fin sizeIndex)) :
    (∑ other ∈ freeStar,
        D.weight other * |edgeTripleValue D edgeFirst edgeSecond other|) ^ 2
      ≤ atomPairing D edgeFirst edgeSecond ^ 2
        * ((∑ other ∈ freeStar,
            D.weight other * atomPairing D edgeFirst other ^ 2)
          * ∑ other ∈ freeStar,
              D.weight other * atomPairing D other edgeSecond ^ 2) := by
  classical
  have hfactor : ∀ other : Fin sizeIndex,
      D.weight other * |edgeTripleValue D edgeFirst edgeSecond other|
        = |atomPairing D edgeFirst edgeSecond|
          * ((Real.sqrt (D.weight other) * |atomPairing D edgeFirst other|)
            * (Real.sqrt (D.weight other) * |atomPairing D other edgeSecond|)) := by
    intro other
    set root : ℝ := Real.sqrt (D.weight other) with hrootDef
    have hweight : root * root = D.weight other :=
      Real.mul_self_sqrt (D.weight_pos other).le
    simp only [edgeTripleValue, abs_mul]
    rw [← hweight]
    ring
  have hsquare : ∀ other : Fin sizeIndex,
      (Real.sqrt (D.weight other) * |atomPairing D edgeFirst other|) ^ 2
        = D.weight other * atomPairing D edgeFirst other ^ 2 := by
    intro other
    rw [mul_pow, Real.sq_sqrt (D.weight_pos other).le, sq_abs]
  have hsquareSecond : ∀ other : Fin sizeIndex,
      (Real.sqrt (D.weight other) * |atomPairing D other edgeSecond|) ^ 2
        = D.weight other * atomPairing D other edgeSecond ^ 2 := by
    intro other
    rw [mul_pow, Real.sq_sqrt (D.weight_pos other).le, sq_abs]
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq freeStar
    (fun other => Real.sqrt (D.weight other) * |atomPairing D edgeFirst other|)
    (fun other => Real.sqrt (D.weight other) * |atomPairing D other edgeSecond|)
  rw [Finset.sum_congr rfl (fun other (_ : other ∈ freeStar) => hfactor other),
    ← Finset.mul_sum, mul_pow, sq_abs]
  rw [Finset.sum_congr rfl (fun other (_ : other ∈ freeStar) => hsquare other),
    Finset.sum_congr rfl
      (fun other (_ : other ∈ freeStar) => hsquareSecond other)] at hcauchy
  have hpair : (0:ℝ) ≤ atomPairing D edgeFirst edgeSecond ^ 2 := sq_nonneg _
  exact mul_le_mul_of_nonneg_left hcauchy hpair

/-- **THE FREE-SUB-STAR BUDGET TEST.**  Bound the free star slots by one
Cauchy-Schwarz against the two FREE sub-star budgets, keep the forced slots
exact, and the box deficit follows -- hence a forced slot with a nonnegative
triple value.  This is the split form of the whole-star budget test: because
the forced part is never bounded and the budgets are taken over the free
sub-star only, the hypothesis is weaker and the test strictly stronger.
Measured this slot: the whole-star test fires at 124 of the 307 corpus kills
and this one at 174, with the ten-point magnitude-carried hard core inside
both. -/
theorem exists_nonneg_edgeTripleValue_of_freeStarBudget
    (D : WeightedDesign sizeIndex 3)
    {edgeFirst edgeSecond : Fin sizeIndex} (hedge : edgeFirst ≠ edgeSecond)
    (forcedStar : Finset (Fin sizeIndex))
    (hsubset : forcedStar ⊆ (Finset.univ.erase edgeFirst).erase edgeSecond)
    (hpositive :
      0 < atomPairing D edgeFirst edgeSecond ^ 2
            * (1 - atomShare D edgeFirst - atomShare D edgeSecond)
          + ∑ other ∈ forcedStar,
              D.weight other * |edgeTripleValue D edgeFirst edgeSecond other|)
    (hbudget :
      atomPairing D edgeFirst edgeSecond ^ 2
        * ((∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond)
                \ forcedStar,
              D.weight other * atomPairing D edgeFirst other ^ 2)
          * ∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond)
                \ forcedStar,
              D.weight other * atomPairing D other edgeSecond ^ 2)
        < (atomPairing D edgeFirst edgeSecond ^ 2
              * (1 - atomShare D edgeFirst - atomShare D edgeSecond)
            + ∑ other ∈ forcedStar,
                D.weight other
                  * |edgeTripleValue D edgeFirst edgeSecond other|) ^ 2) :
    ∃ other ∈ forcedStar,
      0 ≤ edgeTripleValue D edgeFirst edgeSecond other := by
  classical
  refine exists_nonneg_edgeTripleValue_of_boxDeficit D hedge forcedStar hsubset
    ?_
  set freeStar : Finset (Fin sizeIndex) :=
    ((Finset.univ.erase edgeFirst).erase edgeSecond) \ forcedStar with hfree
  set freeMass : ℝ := ∑ other ∈ freeStar,
      D.weight other * |edgeTripleValue D edgeFirst edgeSecond other|
    with hmass
  set requirement : ℝ := atomPairing D edgeFirst edgeSecond ^ 2
        * (1 - atomShare D edgeFirst - atomShare D edgeSecond)
      + ∑ other ∈ forcedStar,
          D.weight other * |edgeTripleValue D edgeFirst edgeSecond other|
    with hrequirement
  have hmassNonneg : 0 ≤ freeMass :=
    Finset.sum_nonneg fun other _ =>
      mul_nonneg (D.weight_pos other).le (abs_nonneg _)
  have hcauchy := sum_weight_mul_abs_edgeTripleValue_sq_le_freeBudget D
    edgeFirst edgeSecond freeStar
  have hsq : freeMass ^ 2 < requirement ^ 2 := lt_of_le_of_lt hcauchy hbudget
  have hlt : freeMass < requirement := by
    by_contra hge
    push Not at hge
    nlinarith [hmassNonneg, hpositive, hge, hsq]
  linarith [hlt]

end Gtz
