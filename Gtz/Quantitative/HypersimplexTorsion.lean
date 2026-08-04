/-
# The degree/triangle bridge, and the exact budget the 2-torsion buys

GTZ at rank three is an INTEGRALITY GAP: the fractional relaxation of subset
selection is unconditionally true (`Gtz.posSemidef_hypersimplexRelaxation`) while
the conjecture asks for a 0/1 point (`Gtz.gtzWeighted_iff_forall_exists_zeroOne_relaxation`),
and the failure of that rounding step over the complex field is the whole content.
The fractional certificate is a vector of DEGREE coordinates (one number per atom);
the realness that must be consumed is the 2-torsion of the Bargmann triangle
invariant, a vector of TRIANGLE coordinates (one number per triple).  This module
is the bridge between the two coordinate systems, in both directions.

## The negative direction: the torsion is invisible to every linear functional

`isGreatest_sum_smul_isTorsionPoint` and `isGreatest_sum_smul_isBoxPoint`: over the
TORSION set (each coordinate pinned to `± radius`, which is what realness gives) and
over the BOX (each coordinate merely bounded by `radius`, which is all the complex
field gives), every linear functional has the SAME greatest value
`sum |coefficient| * radius`.  So a linear -- equivalently, by LP duality, a convex
-- argument about the triangle vector proves a statement that is true over both
fields, and by boundary condition B1 cannot reach the cell.

The fractional layer is exactly such an argument.  Its master identity
(`Gtz.sum_smul_subsetSum_eq_sum_multiplierDegree_smul`) says the aggregated gap
depends on a multiplier only through its DEGREE vector, and the degree map is
linear with no sign constraint attached.  `isFractionalCertificate_congr` and
`hypersimplexRelaxationWeight_congr` sharpen this to the crudest possible form: the
whole certificate polytope is a function of the WEIGHT VECTOR ALONE, and at uniform
weight it is the barycentre `rank / size` of the hypersimplex
(`hypersimplexRelaxationWeight_uniform`) -- the one point invariant under every
relabelling, at exactly the weights where the complex counterexample lives.

## The positive direction: sign conditions are where the torsion is spendable

`sum_smul_le_free_sub_forced_of_isTorsionPoint` versus
`sum_smul_le_free_of_isBoxPoint`: once the functional is read on the SIGN-CONSTRAINED
face "negative on a forced set", the two bounds separate, and they separate by
EXACTLY `sum over the forced set of weight * radius`.  Over the reals a negative
coordinate of modulus `radius` IS `-radius`; over the complex field it is only
somewhere in `[-radius, 0)`.  That single sentence is the whole realness content of
the erase/capacity layer, and `torsionBudget` names the gap.

`exists_nonneg_of_boxDeficit` is the resulting TORSION-FREE capacity lemma, and
`exists_nonneg_edgeTripleValue_of_boxDeficit_torsionFree` its design instance:
the shipped `Gtz.exists_nonneg_edgeTripleValue_of_boxDeficit` with the forced mass
deleted from the right-hand side.  `hasForcedBoxDeficitEdge_of_torsionFreeDeficit`
shows the torsion-free region sits INSIDE the shipped one, so the shipped fragment
is the strictly larger of the two and the difference is bought by realness.

## Measured scope (measurements, not theorems; recorded for calibration)

On the Phase-3 exact corpus, recomputed this run from the raw `(B, w)` blobs with
three firing controls (Parseval idempotence, the edge law re-derived from `Pi^2 = Pi`
at all fifteen edges, and the torsion `tau^2 = mu mu mu` at all twenty triples, each
418 of 418): the shipped real deficit fires at `95` of the `118` exceptional points,
the torsion-free deficit at `6`.  Over the whole 418-point corpus the counts are
`221` and `29`.  So `89` of the `95` exceptional kills -- 94 percent of the landed
coverage fragment's reach on the locus that matters -- are bought by the 2-torsion
and by nothing else.

At `Gtz.icosaDesign` the degree projection of the triangle vector
`c |-> sum over the triples through c of the pairing product` is EXACTLY ZERO
(verified in `Q(sqrt 5)`: the two-graph is the order-six Paley conference matrix,
so `S^3 = 5 S` has zero diagonal), and it is zero at the trine too.  So the one
object the degree coordinate can see about the triangle vector does not separate
the real witness from the complex counterexample.
-/
import Mathlib
import Gtz.Quantitative.BalancedCollections
import Gtz.Reduction.SignClashCoverage
import Gtz.Quantitative.CocycleRigidity
import Gtz.Ties.SelectionObstruction
import Gtz.Quantitative.PhaseFreeNoGo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Finset

variable {index : Type*}

/-! ## 1. The torsion set and the box -/

/-- **THE TORSION SET.**  Every coordinate pinned to plus or minus its radius.  Over
the reals the Bargmann triangle invariant of a design lies here: its modulus IS the
radius (`Gtz.abs_edgeTripleValue`). -/
def IsTorsionPoint (support : Finset index) (radius value : index → ℝ) : Prop :=
  ∀ member ∈ support, |value member| = radius member

/-- **THE BOX.**  Every coordinate merely bounded by its radius.  Over the complex
field this is all that survives: the Bargmann phase is free, so the triangle sits
anywhere in the interval. -/
def IsBoxPoint (support : Finset index) (radius value : index → ℝ) : Prop :=
  ∀ member ∈ support, |value member| ≤ radius member

theorem isBoxPoint_of_isTorsionPoint {support : Finset index} {radius value : index → ℝ}
    (htorsion : IsTorsionPoint support radius value) : IsBoxPoint support radius value :=
  fun member hmember => le_of_eq (htorsion member hmember)

/-! ## 2. Every linear functional is blind to the difference -/

/-- A linear functional on the box is bounded by the absolute-value pairing. -/
theorem sum_smul_le_sum_abs_smul_of_isBoxPoint (support : Finset index)
    (coefficient radius value : index → ℝ)
    (hbox : IsBoxPoint support radius value) :
    ∑ member ∈ support, coefficient member * value member
      ≤ ∑ member ∈ support, |coefficient member| * radius member := by
  refine Finset.sum_le_sum fun member hmember => ?_
  calc coefficient member * value member
      ≤ |coefficient member * value member| := le_abs_self _
    _ = |coefficient member| * |value member| := abs_mul _ _
    _ ≤ |coefficient member| * radius member :=
        mul_le_mul_of_nonneg_left (hbox member hmember) (abs_nonneg _)

/-- The signed choice that attains the bound: take `radius` where the coefficient is
nonnegative and `-radius` where it is negative. -/
noncomputable def signedExtreme (coefficient radius : index → ℝ) (member : index) : ℝ :=
  if 0 ≤ coefficient member then radius member else -radius member

theorem isTorsionPoint_signedExtreme (support : Finset index)
    (coefficient radius : index → ℝ) (hradius : ∀ member ∈ support, 0 ≤ radius member) :
    IsTorsionPoint support radius (signedExtreme coefficient radius) := by
  intro member hmember
  by_cases hsign : 0 ≤ coefficient member
  · rw [signedExtreme, if_pos hsign, abs_of_nonneg (hradius member hmember)]
  · rw [signedExtreme, if_neg hsign, abs_neg, abs_of_nonneg (hradius member hmember)]

theorem sum_smul_signedExtreme (support : Finset index) (coefficient radius : index → ℝ) :
    ∑ member ∈ support, coefficient member * signedExtreme coefficient radius member
      = ∑ member ∈ support, |coefficient member| * radius member := by
  refine Finset.sum_congr rfl fun member _ => ?_
  by_cases hsign : 0 ≤ coefficient member
  · rw [signedExtreme, if_pos hsign, abs_of_nonneg hsign]
  · rw [signedExtreme, if_neg hsign, abs_of_neg (not_le.mp hsign)]
    ring

/-- **THE OBSTRUCTION, HALF ONE.**  Over the torsion set every linear functional
attains exactly `sum |coefficient| * radius`. -/
theorem isGreatest_sum_smul_isTorsionPoint (support : Finset index)
    (coefficient radius : index → ℝ) (hradius : ∀ member ∈ support, 0 ≤ radius member) :
    IsGreatest {pairing : ℝ | ∃ value : index → ℝ, IsTorsionPoint support radius value
        ∧ pairing = ∑ member ∈ support, coefficient member * value member}
      (∑ member ∈ support, |coefficient member| * radius member) := by
  constructor
  · exact ⟨signedExtreme coefficient radius,
      isTorsionPoint_signedExtreme support coefficient radius hradius,
      (sum_smul_signedExtreme support coefficient radius).symm⟩
  · rintro pairing ⟨value, htorsion, rfl⟩
    exact sum_smul_le_sum_abs_smul_of_isBoxPoint support coefficient radius value
      (isBoxPoint_of_isTorsionPoint htorsion)

/-- **THE OBSTRUCTION, HALF TWO.**  Over the box every linear functional attains the
SAME number.  The witness is the same signed extreme point, which lies in the torsion
set and hence in the box. -/
theorem isGreatest_sum_smul_isBoxPoint (support : Finset index)
    (coefficient radius : index → ℝ) (hradius : ∀ member ∈ support, 0 ≤ radius member) :
    IsGreatest {pairing : ℝ | ∃ value : index → ℝ, IsBoxPoint support radius value
        ∧ pairing = ∑ member ∈ support, coefficient member * value member}
      (∑ member ∈ support, |coefficient member| * radius member) := by
  constructor
  · exact ⟨signedExtreme coefficient radius,
      isBoxPoint_of_isTorsionPoint
        (isTorsionPoint_signedExtreme support coefficient radius hradius),
      (sum_smul_signedExtreme support coefficient radius).symm⟩
  · rintro pairing ⟨value, hbox, rfl⟩
    exact sum_smul_le_sum_abs_smul_of_isBoxPoint support coefficient radius value hbox

/-- **THE TORSION IS LINEARLY INVISIBLE.**  The two optimisation problems have the
same value, at every support, every radius vector and every linear functional.  So no
linear -- equivalently, by LP duality, no convex -- argument about the triangle vector
can distinguish the real locus from its complex relaxation.  The fractional/balanced
layer is such an argument: its master identity factors the aggregated gap through the
DEGREE map, which is linear and carries no sign condition. -/
theorem torsion_invisible_to_linear_functionals (support : Finset index)
    (coefficient radius : index → ℝ) (hradius : ∀ member ∈ support, 0 ≤ radius member) :
    IsGreatest {pairing : ℝ | ∃ value : index → ℝ, IsTorsionPoint support radius value
        ∧ pairing = ∑ member ∈ support, coefficient member * value member}
      (∑ member ∈ support, |coefficient member| * radius member)
    ∧ IsGreatest {pairing : ℝ | ∃ value : index → ℝ, IsBoxPoint support radius value
        ∧ pairing = ∑ member ∈ support, coefficient member * value member}
      (∑ member ∈ support, |coefficient member| * radius member) :=
  ⟨isGreatest_sum_smul_isTorsionPoint support coefficient radius hradius,
   isGreatest_sum_smul_isBoxPoint support coefficient radius hradius⟩

/-! ## 3. Sign conditions: where the two sets finally separate

Nothing above sees the difference between the torsion set and the box.  Restricting
to the face "strictly negative on a forced subset" is what makes them separate, and
the separation is by exactly one term. -/

variable [DecidableEq index]

/-- **THE ONE LINE OF REALNESS.**  Over the reals a strictly negative coordinate whose
modulus is `radius` IS `-radius`.  Over the complex field the same coordinate is only
somewhere in `[-radius, 0)`, and every quantitative loss below is this loss. -/
theorem eq_neg_radius_of_neg_of_abs_eq {radiusValue value : ℝ} (habs : |value| = radiusValue)
    (hneg : value < 0) : value = -radiusValue := by
  rw [← habs, abs_of_neg hneg, neg_neg]

/-- **THE REAL BOUND on the sign-constrained face.**  The forced coordinates are pinned
to the bottom of the box, so they SUBTRACT their full mass. -/
theorem sum_smul_le_free_sub_forced_of_isTorsionPoint (support forced : Finset index)
    (hsubset : forced ⊆ support) (weight radius value : index → ℝ)
    (hweight : ∀ member ∈ support, 0 ≤ weight member)
    (htorsion : IsTorsionPoint support radius value)
    (hnegative : ∀ member ∈ forced, value member < 0) :
    ∑ member ∈ support, weight member * value member
      ≤ (∑ member ∈ support \ forced, weight member * radius member)
        - ∑ member ∈ forced, weight member * radius member := by
  have hsplit : ∑ member ∈ support \ forced, weight member * value member
      + ∑ member ∈ forced, weight member * value member
      = ∑ member ∈ support, weight member * value member := Finset.sum_sdiff hsubset
  have hfree : ∑ member ∈ support \ forced, weight member * value member
      ≤ ∑ member ∈ support \ forced, weight member * radius member := by
    refine Finset.sum_le_sum fun member hmember => ?_
    have hin : member ∈ support := (Finset.mem_sdiff.mp hmember).1
    calc weight member * value member
        ≤ weight member * |value member| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (hweight member hin)
      _ = weight member * radius member := by rw [htorsion member hin]
  have hforced : ∑ member ∈ forced, weight member * value member
      = -∑ member ∈ forced, weight member * radius member := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun member hmember => ?_
    rw [eq_neg_radius_of_neg_of_abs_eq (htorsion member (hsubset hmember))
      (hnegative member hmember)]
    ring
  linarith [hsplit, hfree, hforced]

/-- **THE COMPLEX BOUND on the same face.**  All the box gives is that the forced
coordinates are nonpositive, so their mass is LOST rather than subtracted. -/
theorem sum_smul_le_free_of_isBoxPoint (support forced : Finset index)
    (hsubset : forced ⊆ support) (weight radius value : index → ℝ)
    (hweight : ∀ member ∈ support, 0 ≤ weight member)
    (hbox : IsBoxPoint support radius value)
    (hnegative : ∀ member ∈ forced, value member < 0) :
    ∑ member ∈ support, weight member * value member
      ≤ ∑ member ∈ support \ forced, weight member * radius member := by
  have hsplit : ∑ member ∈ support \ forced, weight member * value member
      + ∑ member ∈ forced, weight member * value member
      = ∑ member ∈ support, weight member * value member := Finset.sum_sdiff hsubset
  have hfree : ∑ member ∈ support \ forced, weight member * value member
      ≤ ∑ member ∈ support \ forced, weight member * radius member := by
    refine Finset.sum_le_sum fun member hmember => ?_
    have hin : member ∈ support := (Finset.mem_sdiff.mp hmember).1
    calc weight member * value member
        ≤ weight member * |value member| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (hweight member hin)
      _ ≤ weight member * radius member :=
          mul_le_mul_of_nonneg_left (hbox member hin) (hweight member hin)
  have hforced : ∑ member ∈ forced, weight member * value member ≤ 0 :=
    Finset.sum_nonpos fun member hmember =>
      mul_nonpos_of_nonneg_of_nonpos (hweight member (hsubset hmember))
        (hnegative member hmember).le
  linarith [hsplit, hfree, hforced]

/-- **THE REAL BOUND IS ATTAINED**, so the separation below is exact rather than an
artefact of the estimate: take the top of the box off the forced set and the bottom
on it. -/
noncomputable def forcedExtreme (forced : Finset index) (radius : index → ℝ)
    (member : index) : ℝ :=
  if member ∈ forced then -radius member else radius member

theorem exists_isTorsionPoint_neg_on_forced (support forced : Finset index)
    (hsubset : forced ⊆ support) (weight radius : index → ℝ)
    (hradius : ∀ member ∈ support, 0 ≤ radius member)
    (hradiusPos : ∀ member ∈ forced, 0 < radius member) :
    IsTorsionPoint support radius (forcedExtreme forced radius)
      ∧ (∀ member ∈ forced, forcedExtreme forced radius member < 0)
      ∧ ∑ member ∈ support, weight member * forcedExtreme forced radius member
        = (∑ member ∈ support \ forced, weight member * radius member)
          - ∑ member ∈ forced, weight member * radius member := by
  refine ⟨fun member hmember => ?_, fun member hmember => ?_, ?_⟩
  · by_cases hin : member ∈ forced
    · rw [forcedExtreme, if_pos hin, abs_neg, abs_of_nonneg (hradius member hmember)]
    · rw [forcedExtreme, if_neg hin, abs_of_nonneg (hradius member hmember)]
  · rw [forcedExtreme, if_pos hmember]
    exact neg_neg_iff_pos.mpr (hradiusPos member hmember)
  · have hsplit : ∑ member ∈ support \ forced,
        weight member * forcedExtreme forced radius member
        + ∑ member ∈ forced, weight member * forcedExtreme forced radius member
        = ∑ member ∈ support, weight member * forcedExtreme forced radius member :=
      Finset.sum_sdiff hsubset
    have hfree : ∑ member ∈ support \ forced,
        weight member * forcedExtreme forced radius member
        = ∑ member ∈ support \ forced, weight member * radius member :=
      Finset.sum_congr rfl fun member hmember => by
        rw [forcedExtreme, if_neg (Finset.mem_sdiff.mp hmember).2]
    have hforced : ∑ member ∈ forced,
        weight member * forcedExtreme forced radius member
        = -∑ member ∈ forced, weight member * radius member := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun member hmember => by
        rw [forcedExtreme, if_pos hmember]; ring
    linarith [hsplit, hfree, hforced]

/-- **THE TORSION BUDGET.**  The real threshold and the complex threshold on the
sign-constrained face differ by exactly the forced mass.  Everything realness buys in
the erase/capacity layer is this number, and nothing else. -/
theorem torsionBudget (support forced : Finset index) (weight radius : index → ℝ) :
    ((∑ member ∈ support \ forced, weight member * radius member)
        - ∑ member ∈ forced, weight member * radius member)
      + ∑ member ∈ forced, weight member * radius member
      = ∑ member ∈ support \ forced, weight member * radius member :=
  sub_add_cancel _ _

/-! ## 4. The capacity lemma, field-split -/

/-- **THE TORSION-FREE CAPACITY LEMMA.**  Assuming only the BOX -- which is all the
complex field supplies -- a deficit against the FREE mass alone already forces some
forced member nonnegative.  This is the fragment of the shipped capacity lemma that
survives over the complex field, and its design instance is the shipped
`Gtz.exists_nonneg_edgeTripleValue_of_boxDeficit` with the forced mass deleted from
the right-hand side. -/
theorem exists_nonneg_of_boxDeficit (support forced : Finset index)
    (hsubset : forced ⊆ support) (weight radius value : index → ℝ) (target : ℝ)
    (hweight : ∀ member ∈ support, 0 ≤ weight member)
    (hbox : IsBoxPoint support radius value)
    (hlaw : ∑ member ∈ support, weight member * value member = target)
    (hdeficit : ∑ member ∈ support \ forced, weight member * radius member < target) :
    ∃ member ∈ forced, 0 ≤ value member := by
  by_contra hall
  push Not at hall
  have hbound := sum_smul_le_free_of_isBoxPoint support forced hsubset weight radius value
    hweight hbox hall
  rw [hlaw] at hbound
  linarith

/-- **THE TORSION CAPACITY LEMMA**, for comparison: the same conclusion from the
strictly weaker deficit that the forced mass is allowed to help pay for.  DISCLOSURE:
this is the abstract form of the shipped `Gtz.exists_nonneg_edgeTripleValue_of_boxDeficit`
and is stated here only so that the two thresholds can be compared in one place. -/
theorem exists_nonneg_of_torsionDeficit (support forced : Finset index)
    (hsubset : forced ⊆ support) (weight radius value : index → ℝ) (target : ℝ)
    (hweight : ∀ member ∈ support, 0 ≤ weight member)
    (htorsion : IsTorsionPoint support radius value)
    (hlaw : ∑ member ∈ support, weight member * value member = target)
    (hdeficit : ∑ member ∈ support \ forced, weight member * radius member
      < target + ∑ member ∈ forced, weight member * radius member) :
    ∃ member ∈ forced, 0 ≤ value member := by
  by_contra hall
  push Not at hall
  have hbound := sum_smul_le_free_sub_forced_of_isTorsionPoint support forced hsubset
    weight radius value hweight htorsion hall
  rw [hlaw] at hbound
  linarith

/-- **THE NESTING.**  The torsion-free deficit implies the torsion deficit, so the
region the complex-valid lemma covers sits INSIDE the region the shipped lemma covers,
and the difference is exactly the forced mass.  Measured on the Phase-3 corpus: the
shipped region contains `95` of the `118` exceptional points and the torsion-free
region `6`. -/
theorem torsionDeficit_of_boxDeficit (support forced : Finset index)
    (hsubset : forced ⊆ support) (weight radius : index → ℝ) (target : ℝ)
    (hweight : ∀ member ∈ support, 0 ≤ weight member)
    (hradius : ∀ member ∈ support, 0 ≤ radius member)
    (hdeficit : ∑ member ∈ support \ forced, weight member * radius member < target) :
    ∑ member ∈ support \ forced, weight member * radius member
      < target + ∑ member ∈ forced, weight member * radius member := by
  have hforcedNonneg : 0 ≤ ∑ member ∈ forced, weight member * radius member :=
    Finset.sum_nonneg fun member hmember =>
      mul_nonneg (hweight member (hsubset hmember)) (hradius member (hsubset hmember))
  linarith

end Gtz


namespace Gtz

open Matrix Finset

variable {sizeIndex : ℕ}

/-! ## A. The capacity lemma without the torsion

`Gtz.exists_nonneg_edgeTripleValue_of_boxDeficit` pays for its deficit with the free
star mass MINUS the forced star mass; the subtraction is the 2-torsion, which pins a
negative triple value to `-tripleRadius`.  The version below pays with the free mass
alone, so it uses only `|value| <= radius` -- the cap
`Gtz.IsPhaseFreeAdmissible.triangleCap`, which holds over the complex field too. -/

/-- **THE TORSION-FREE CAPACITY LEMMA at an edge.**  Same conclusion as the shipped
capacity lemma, from a deficit that the forced mass is NOT allowed to help pay for. -/
theorem exists_nonneg_edgeTripleValue_of_boxDeficit_torsionFree
    (design : WeightedDesign sizeIndex 3) {edgeFirst edgeSecond : Fin sizeIndex}
    (hedge : edgeFirst ≠ edgeSecond) (forcedStar : Finset (Fin sizeIndex))
    (hsubset : forcedStar ⊆ (Finset.univ.erase edgeFirst).erase edgeSecond)
    (hdeficit :
      ∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond) \ forcedStar,
          design.weight other * tripleRadius design edgeFirst edgeSecond other
        < atomPairing design edgeFirst edgeSecond ^ 2
            * (1 - atomShare design edgeFirst - atomShare design edgeSecond)) :
    ∃ other ∈ forcedStar, 0 ≤ edgeTripleValue design edgeFirst edgeSecond other :=
  Gtz.exists_nonneg_of_boxDeficit
    ((Finset.univ.erase edgeFirst).erase edgeSecond) forcedStar hsubset design.weight
    (fun other => tripleRadius design edgeFirst edgeSecond other)
    (fun other => edgeTripleValue design edgeFirst edgeSecond other)
    (atomPairing design edgeFirst edgeSecond ^ 2
      * (1 - atomShare design edgeFirst - atomShare design edgeSecond))
    (fun other _ => (design.weight_pos other).le)
    (fun other _ => le_of_eq (abs_edgeTripleValue design edgeFirst edgeSecond other))
    (sum_erasePair_weight_mul_edgeTripleValue design hedge) hdeficit

/-- **THE NESTING.**  The torsion-free deficit implies the shipped one, so the region
the complex-valid lemma reaches sits INSIDE the region the shipped lemma reaches.  The
difference is exactly the forced star mass, which is the whole of what realness buys
here.  MEASURED on the Phase-3 exact corpus this run (three firing controls, 418 of
418): the shipped region contains `95` of the `118` exceptional points, the
torsion-free region `6`. -/
theorem hasForcedBoxDeficitEdge_of_torsionFreeDeficit
    (design : WeightedDesign sizeIndex 3) {edgeFirst edgeSecond : Fin sizeIndex}
    (hedge : edgeFirst ≠ edgeSecond) (forcedStar : Finset (Fin sizeIndex))
    (hsubset : forcedStar ⊆ (Finset.univ.erase edgeFirst).erase edgeSecond)
    (hforced : ∀ other ∈ forcedStar,
      IsForcedMinusTriple design edgeFirst edgeSecond other)
    (hdeficit :
      ∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond) \ forcedStar,
          design.weight other * tripleRadius design edgeFirst edgeSecond other
        < atomPairing design edgeFirst edgeSecond ^ 2
            * (1 - atomShare design edgeFirst - atomShare design edgeSecond)) :
    HasForcedBoxDeficitEdge design := by
  refine ⟨edgeFirst, edgeSecond, hedge, forcedStar, hsubset, hforced, ?_⟩
  have hfreeSame :
      ∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond) \ forcedStar,
          design.weight other * |edgeTripleValue design edgeFirst edgeSecond other|
        = ∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond) \ forcedStar,
            design.weight other * tripleRadius design edgeFirst edgeSecond other :=
    Finset.sum_congr rfl fun other _ => by rw [abs_edgeTripleValue]
  have hforcedNonneg : 0 ≤ ∑ other ∈ forcedStar,
      design.weight other * |edgeTripleValue design edgeFirst edgeSecond other| :=
    Finset.sum_nonneg fun other _ =>
      mul_nonneg (design.weight_pos other).le (abs_nonneg _)
  rw [hfreeSame]
  linarith

/-! ## B. The fractional certificate is a function of the WEIGHTS ALONE -/

/-- The fractional certificate POLYTOPE: the points of the hypersimplex that dominate
the design's own weight vector coordinatewise.  Every one of them dominates
(`posSemidef_of_isFractionalCertificate`), so this is the whole fractional relaxation
of GTZ, not just the canonical point `Gtz.hypersimplexRelaxationWeight`. -/
def IsFractionalCertificate {size rank : ℕ} (design : WeightedDesign size rank)
    (point : Fin size → ℝ) : Prop :=
  (∀ atomIndex, design.weight atomIndex ≤ point atomIndex)
    ∧ (∀ atomIndex, point atomIndex ≤ 1)
    ∧ ∑ atomIndex, point atomIndex = (rank : ℝ)

/-- **THE WHOLE CERTIFICATE POLYTOPE DOMINATES.**  Generalises the shipped
`Gtz.posSemidef_hypersimplexRelaxation` from the canonical point to every point of the
polytope, by the same consumption of `Gtz.mem_dominationCone_of_nonneg`. -/
theorem posSemidef_of_isFractionalCertificate {size rank : ℕ}
    (design : WeightedDesign size rank) (point : Fin size → ℝ)
    (hcertificate : IsFractionalCertificate design point) :
    ((∑ atomIndex, point atomIndex • atomMatrix (design.atom atomIndex)) - 1).PosSemidef := by
  have hcone : (fun atomIndex => point atomIndex - design.weight atomIndex)
      ∈ dominationCone design :=
    mem_dominationCone_of_nonneg design
      (fun atomIndex => sub_nonneg.mpr (hcertificate.1 atomIndex))
  rw [mem_dominationCone_iff] at hcone
  have hrewrite : ∑ atomIndex,
      (point atomIndex - design.weight atomIndex) • atomMatrix (design.atom atomIndex)
      = (∑ atomIndex, point atomIndex • atomMatrix (design.atom atomIndex)) - 1 := by
    rw [← design.isParseval, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => by rw [sub_smul]
  rwa [hrewrite] at hcone

/-- **THE OBSTRUCTION, CRUDEST FORM.**  The certificate polytope is determined by the
weight vector: two designs with the same weights have literally the same set of
fractional certificates. -/
theorem isFractionalCertificate_congr {size rank : ℕ}
    (designFirst designSecond : WeightedDesign size rank)
    (hweight : designFirst.weight = designSecond.weight) (point : Fin size → ℝ) :
    IsFractionalCertificate designFirst point ↔ IsFractionalCertificate designSecond point := by
  simp only [IsFractionalCertificate, hweight]

/-- The canonical certificate is a function of the weights alone. -/
theorem hypersimplexRelaxationWeight_congr {size rank : ℕ}
    (designFirst designSecond : WeightedDesign size rank)
    (hweight : designFirst.weight = designSecond.weight) :
    hypersimplexRelaxationWeight designFirst = hypersimplexRelaxationWeight designSecond := by
  funext atomIndex
  simp only [hypersimplexRelaxationWeight, hweight]

/-- **AT UNIFORM WEIGHT THE CERTIFICATE IS THE BARYCENTRE** `rank / size` of the
hypersimplex -- the one point invariant under every relabelling, hence carrying no
information at all about which subset to choose.  Both `Gtz.icosaDesign` and the
complex counterexample `Gtz.trineSixData` have uniform weight `1/6`. -/
theorem hypersimplexRelaxationWeight_uniform {size rank : ℕ}
    (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (huniform : ∀ atomIndex, design.weight atomIndex = ((size : ℝ))⁻¹)
    (atomIndex : Fin size) :
    hypersimplexRelaxationWeight design atomIndex = (rank : ℝ) / (size : ℝ) := by
  have hsizeReal : (2 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsize
  have hsizeNe : (size : ℝ) ≠ 0 := by linarith
  have hgapNe : (size : ℝ) - 1 ≠ 0 := by linarith
  rw [hypersimplexRelaxationWeight, huniform atomIndex]
  field_simp
  ring

/-- The canonical certificate is unchanged by relabelling when the weight is constant:
relabelling permutes atoms and weights together, and a constant weight vector is fixed
by every permutation. -/
theorem hypersimplexRelaxationWeight_relabelDesign_of_constant {size rank : ℕ}
    (design : WeightedDesign size rank) (relabel : Equiv.Perm (Fin size)) (value : ℝ)
    (hconstant : ∀ atomIndex, design.weight atomIndex = value) :
    hypersimplexRelaxationWeight (relabelDesign design relabel)
      = hypersimplexRelaxationWeight design :=
  hypersimplexRelaxationWeight_congr _ _
    (funext fun atomIndex => by
      simp only [relabelDesign, hconstant])

/-! ## C. The separation: two designs, one certificate, different domination -/

/-- The icosahedral tie leg at the INCOHERENT triple `{0,1,4}`: the two-graph sign
product is `-1` there, so the torsion pushes the determinant to the bottom of the
band. -/
theorem discriminantTie_icosaDesign_zeroOneFour :
    discriminantTie icosaDesign 0 1 4 = -14 / 5 - 18 / 5 * icosaRadius := by
  have hsq := icosaRadius_sq
  have hsignZeroOne : icosaOverlapSign 0 1 = 1 := by simp [icosaOverlapSign]
  have hsignZeroFour : icosaOverlapSign 0 4 = 1 := by simp [icosaOverlapSign]
  have hsignOneFour : icosaOverlapSign 1 4 = -1 := by simp [icosaOverlapSign]
  rw [discriminantTie, icosaDesign_heavyExcess, icosaDesign_heavyExcess,
    icosaDesign_heavyExcess,
    atomPairing_icosaDesign_of_ne (by decide : (0 : Fin 6) ≠ 1),
    atomPairing_icosaDesign_of_ne (by decide : (0 : Fin 6) ≠ 4),
    atomPairing_icosaDesign_of_ne (by decide : (1 : Fin 6) ≠ 4),
    hsignZeroOne, hsignZeroFour, hsignOneFour]
  linear_combination (-6 - 2 * icosaRadius) * hsq

/-- **`Gtz.icosaDesign` DOES NOT DOMINATE `{0,1,4}`** -- its determinant is negative,
so the block cannot be positive semidefinite.  Ten of the twenty triples are like
this; `Gtz.icosaDesign_dominates` supplies one of the other ten. -/
theorem not_dominates_icosaDesign_zeroOneFour :
    ¬ Dominates icosaDesign ({0, 1, 4} : Finset (Fin 6)) := by
  intro hdominates
  have hdet := hdominates.det_nonneg
  rw [det_subsetSum_sub_one_eq_discriminantTie icosaDesign (by decide : (0 : Fin 6) ≠ 1)
    (by decide : (0 : Fin 6) ≠ 4) (by decide : (1 : Fin 6) ≠ 4),
    discriminantTie_icosaDesign_zeroOneFour] at hdet
  nlinarith [icosaRadius_lower]

/-- **THE FRACTIONAL CERTIFICATE CANNOT DECIDE DOMINATION.**  Two `(6,3)` designs with
IDENTICAL weight vectors -- hence, by `isFractionalCertificate_congr` and
`hypersimplexRelaxationWeight_congr`, identical certificate polytopes and identical
canonical certificates -- disagree about whether `{0,2,4}` dominates.  So no function
of the fractional certificate is a rounding rule: the bridge from degree coordinates
to a choice of subset cannot be written.

The second design is `Gtz.icosaDesign` relabelled by the transposition `(1 2)`, which
carries the coherent triple `{0,2,4}` to the incoherent triple `{0,1,4}`. -/
theorem certificate_does_not_decide_domination :
    ∃ (designFirst designSecond : WeightedDesign 6 3) (chosen : Finset (Fin 6)),
      designFirst.weight = designSecond.weight
        ∧ chosen.card = 3
        ∧ hypersimplexRelaxationWeight designFirst = hypersimplexRelaxationWeight designSecond
        ∧ Dominates designFirst chosen
        ∧ ¬ Dominates designSecond chosen := by
  refine ⟨icosaDesign, relabelDesign icosaDesign (Equiv.swap 1 2), {0, 2, 4}, ?_, by decide,
    ?_, icosaDesign_dominates, ?_⟩
  · funext atomIndex; rfl
  · exact (hypersimplexRelaxationWeight_relabelDesign_of_constant icosaDesign
      (Equiv.swap 1 2) (1 / 6) (fun _ => rfl)).symm
  · rw [dominates_relabelDesign_iff]
    have hmap : ({0, 2, 4} : Finset (Fin 6)).map (Equiv.swap (1 : Fin 6) 2).toEmbedding
        = ({0, 1, 4} : Finset (Fin 6)) := by decide
    rw [hmap]
    exact not_dominates_icosaDesign_zeroOneFour

/-! ## D. The complex counterexample violates exactly the dropped hypothesis

`exists_nonneg_of_torsionDeficit` uses one thing beyond `exists_nonneg_of_boxDeficit`:
the torsion identity `|triangle| = radius`.  At the shipped complex counterexample the
identity fails by the WHOLE radius. -/

/-- At `Gtz.trineSixData` the Bargmann triangle of any triple of distinct atoms is
ZERO -- setting every phase to a right angle is precisely what builds the
counterexample. -/
theorem trineSixData_triangle_eq_zero {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hsecondThird : second ≠ third)
    (hfirstThird : first ≠ third) :
    trineSixData.triangle first second third = 0 := by
  rw [trineSixData, trinePoint_triangle, trineTriangleTable]
  simp only [id_eq]
  rw [if_neg hfirstSecond, if_neg hsecondThird, if_neg hfirstThird]

/-- ... while every squared pairing of distinct atoms is at least one, so the RADIUS
`sqrt(pairing * pairing * pairing)` is at least one too. -/
theorem trineSixData_one_le_pairing {first second : Fin 6} (hne : first ≠ second) :
    1 ≤ trineSixData.pairing first second := by
  rw [trineSixData, trinePoint_pairing, trineOverlap]
  simp only [id_eq]
  rw [if_neg hne]
  split <;> norm_num

/-- **THE DROPPED HYPOTHESIS IS EXACTLY WHAT FAILS OVER THE COMPLEX FIELD.**  At
`Gtz.trineSixData` the squared triangle is `0` while the product of the three squared
pairings is at least `1`, so the torsion equality
`triangle^2 = pairing * pairing * pairing` -- the design-level
`Gtz.abs_edgeTripleValue`, i.e. `|edgeTripleValue| = tripleRadius` -- fails by the full
radius.  Everything the shipped capacity lemma has over
`exists_nonneg_edgeTripleValue_of_boxDeficit_torsionFree` is bought with this one
identity, and this is the object that refutes it. -/
theorem trineSixData_torsion_fails {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hsecondThird : second ≠ third)
    (hfirstThird : first ≠ third) :
    trineSixData.triangle first second third ^ 2
      < trineSixData.pairing first second * trineSixData.pairing first third
        * trineSixData.pairing second third := by
  have hone := trineSixData_one_le_pairing hfirstSecond
  have htwo := trineSixData_one_le_pairing hfirstThird
  have hthree := trineSixData_one_le_pairing hsecondThird
  rw [trineSixData_triangle_eq_zero hfirstSecond hsecondThird hfirstThird]
  have hzero : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [hzero]
  have hpair : (1 : ℝ) ≤ trineSixData.pairing first second * trineSixData.pairing first third := by
    nlinarith [hone, htwo]
  nlinarith [hpair, hthree]

end Gtz
