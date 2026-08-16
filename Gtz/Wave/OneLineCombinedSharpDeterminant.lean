import Gtz.Wave.MixedTripleBalance
import Gtz.Design.SphereDichotomy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The determinant of the flat split, and the sharp balance as a surplus reading

`Gtz.LineFlatSplitSelectorAt` asks for a card-three subset whose combined value
`lead * surplus + sharp` is positive at every in-plane probe.  The landed
`Gtz.not_forall_sharpBalanceValue_pos` refutes the sharp part on its own, and the
landed `Gtz.wedgeBalanceValue_flatSplit_reading` factors the combined value into
the two named parts.  Nothing related the two parts.

This module relates them.  The combined value is a quadratic form in the probe on
a two-dimensional plane, so its whole content is a trace and a DETERMINANT.  The
determinant of the sharp part turns out to be the normal SURPLUS again, times a
sign and two squares:

  `det(sharp) = splitMeasure u * splitMeasure v * splitMeasure w
                  * atomBracket u v w ^ 2 * surplus`

with `{u, v, w}` the three sharp labels.  So the two ingredients of the selector
are ONE object read two ways.  The determinant of the whole combined form then
factors, and the surplus comes out as a factor of it:

  `det(combined) = surplus * (surplus * det(lead) + mixed(lead, sharp)
                              + splitMeasure u * splitMeasure v * splitMeasure w
                                  * atomBracket u v w ^ 2)`

Both determinants are read through a PAIR of probes, and the plane orientation
enters as the square of one bracket, so no basis and no square root occur.

## What carries the proof

Three bracket identities of rank three, each a pure polynomial identity:

* `Gtz.tripleBracket_mul_dotProduct` — Cramer.  The bracket of three vectors
  times a dot product expands on the three brackets that replace one slot.
* `Gtz.tripleBracket_shadowPair` — the shadow bracket.  Two shadow vectors that
  share a slot have a bracket equal to one height times one atom bracket.
* `Gtz.dotProduct_pair_sub_eq_tripleBracket` — Binet and Cauchy.

None of the three carries a hypothesis.  The three-label wedge determinant law
`Gtz.tripleWedge_determinant` that they produce carries no hypothesis either: no
unit normal, no flat set, no orthogonal probe.

## What the module concludes

* `Gtz.sharpBalance_determinant` — the sharp determinant law, at any card-three
  flat complement.  Parseval enters here and only here.
* `Gtz.exists_mixedProbe_sharpBalanceValue_nonpos` — a sign criterion that
  replaces the landed pair-wedge refutation.  A negative sharp determinant
  supplies an explicit in-plane probe where the sharp balance is not positive.
* `Gtz.flatSplit_determinant` — the factorization of the combined determinant.
* `Gtz.exists_sharp_selection_surplus_pos` — the SURPLUS FLOOR.  Every design
  with a nonempty flat set carries a sharp label whose height square is more than
  one, so every selection through that label has a positive normal surplus.

## The plane form, and the general criterion

Sections 7 thru 11 drop the flat set.  A PLANE FORM is a measure-weighted sum of
squared readings of directions that are flat against the normal.  Its determinant
at a pair of probes is one number, the MINOR, times the square of the plane
bracket of the probes (`Gtz.planeForm_determinant`).  The whole wedge balance is
one plane form indexed by ordered label pairs, so:

* `Gtz.wedgeMinor` — one number per subset and per unit normal, built from the
  split measure and the brackets of the design's own shadow directions.
* `Gtz.posDef_iff_surplus_and_wedgeMinor` — STRICT DOMINATION at rank three is
  decided by a normal surplus, a wedge minor and ONE probe reading.  Any size,
  any subset, any unit normal.
* `Gtz.gtzWeighted_rank_three_of_wedgeMinorSelector` — the objective itself, at
  every size, from three strict inequalities per design.
* `Gtz.wedgeMinorSelector_iff_exists_strictTriple` — that selector is EXACTLY the
  strict half of rank-three GTZ, so it is neither a strengthening nor a weakening
  of it.

## The one-line lane

* `Gtz.wedgeMinor_eq_surplus_mul_flatSplitReduced` — at a flat set of complement
  size three the wedge minor FACTORS, and the normal surplus is one factor.  So
  the surplus divides the minor and the two selector ingredients are not
  independent.
* `Gtz.exists_tallFree_lineFlatSplitSelector_producer` — the one-line residual
  with the surplus discharged.  One free label supplies the surplus for every
  selection through it, and what remains is one polynomial inequality on
  `Gtz.flatSplitReduced` plus one probe sign.
* `Gtz.oneLine_and_twoMeetingLines_of_wedgeMinorSelector` — both line
  obligations from one minor condition.

## Rank

Every section that names `Gtz.tripleBracket` or `Gtz.crossProduct` consumes rank
three.  Section 5, the surplus floor, is rank generic, and so are
`Gtz.splitMeasure_normalSq_triple_eq_surplus`, `Gtz.wedgeDirection` and
`Gtz.wedgeBalanceValue_eq_wedgeTotal_splitMeasure`.

## Field

Every statement here is an order statement over the reals except the bracket
identities of section 1, `Gtz.planeForm_determinant`, `Gtz.planeForm_crossDeterminant`
and the two determinant laws, which are ring identities.  A ring identity compiles
over any commutative ring, so those carry no field content.  The criteria of
sections 11 thru 14 read strict inequalities, and `Matrix.PosDef` over `ℝ`, so they
do not.
-/

namespace Gtz

open Matrix

/-! ## 1.  Three bracket identities of rank three

Each is a polynomial identity in the coordinates, with no hypothesis. -/

/-- **CRAMER.**  The bracket of three vectors times one dot product expands on
the three brackets that put the probe in one slot. -/
theorem tripleBracket_mul_dotProduct (leftVec midVec rightVec pivotVec probeVec : Fin 3 → ℝ) :
    tripleBracket leftVec midVec rightVec * (pivotVec ⬝ᵥ probeVec)
      = (pivotVec ⬝ᵥ leftVec) * tripleBracket midVec rightVec probeVec
        + (pivotVec ⬝ᵥ midVec) * tripleBracket rightVec leftVec probeVec
        + (pivotVec ⬝ᵥ rightVec) * tripleBracket leftVec midVec probeVec := by
  simp only [tripleBracket_eq, dotProduct, Fin.sum_univ_three]
  ring

/-- **THE SHADOW BRACKET.**  Two shadow vectors that share their base slot have a
bracket equal to the base height times the bracket of the three base vectors. -/
theorem tripleBracket_shadowPair (baseVec firstVec secondVec pivotVec probeVec : Fin 3 → ℝ) :
    tripleBracket ((pivotVec ⬝ᵥ baseVec) • firstVec - (pivotVec ⬝ᵥ firstVec) • baseVec)
        ((pivotVec ⬝ᵥ baseVec) • secondVec - (pivotVec ⬝ᵥ secondVec) • baseVec) probeVec
      = (pivotVec ⬝ᵥ baseVec) * tripleBracket baseVec firstVec secondVec
          * (pivotVec ⬝ᵥ probeVec) := by
  simp only [tripleBracket_eq, dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- **BINET AND CAUCHY.**  The two-by-two minor of two vectors against two probes
is the bracket against the cross product of the probes. -/
theorem dotProduct_pair_sub_eq_tripleBracket (leftVec rightVec probeOne probeTwo : Fin 3 → ℝ) :
    (leftVec ⬝ᵥ probeOne) * (rightVec ⬝ᵥ probeTwo)
        - (rightVec ⬝ᵥ probeOne) * (leftVec ⬝ᵥ probeTwo)
      = tripleBracket leftVec rightVec (crossProduct probeOne probeTwo) := by
  simp only [tripleBracket_eq, dotProduct, Fin.sum_univ_three, cross_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- The normal reads the cross product of two probes as their plane bracket. -/
theorem dotProduct_crossProduct_eq_tripleBracket (probeOne probeTwo normalVec : Fin 3 → ℝ) :
    normalVec ⬝ᵥ crossProduct probeOne probeTwo = tripleBracket probeOne probeTwo normalVec := by
  rw [tripleBracket_eq_crossProduct_dotProduct, dotProduct_comm]

/-- **THE COPLANAR REDUCTION.**  Two vectors flat against the normal have a
bracket whose third slot factors through the normal. -/
theorem tripleBracket_of_perp_pair {leftVec rightVec normalVec : Fin 3 → ℝ}
    (hleft : leftVec ⬝ᵥ normalVec = 0) (hright : rightVec ⬝ᵥ normalVec = 0)
    (probeVec : Fin 3 → ℝ) :
    tripleBracket leftVec rightVec normalVec * (normalVec ⬝ᵥ probeVec)
      = (normalVec ⬝ᵥ normalVec) * tripleBracket leftVec rightVec probeVec := by
  have hexpand := tripleBracket_mul_dotProduct leftVec rightVec normalVec normalVec probeVec
  rw [dotProduct_comm normalVec leftVec, dotProduct_comm normalVec rightVec, hleft, hright,
    zero_mul, zero_mul, zero_add, zero_add] at hexpand
  exact hexpand

/-- The frame bracket of a probe against the normal-driven companion probe. -/
theorem tripleBracket_frame (baseVec normalVec : Fin 3 → ℝ) :
    tripleBracket baseVec (crossProduct normalVec baseVec) normalVec
      = (baseVec ⬝ᵥ baseVec) * (normalVec ⬝ᵥ normalVec) - (baseVec ⬝ᵥ normalVec) ^ 2 := by
  simp only [tripleBracket_eq, dotProduct, Fin.sum_univ_three, cross_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- The companion probe is flat against the normal. -/
theorem dotProduct_crossProduct_left_self (normalVec baseVec : Fin 3 → ℝ) :
    crossProduct normalVec baseVec ⬝ᵥ normalVec = 0 := by
  simp only [dotProduct, Fin.sum_univ_three, cross_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## 2.  The wedge pair bracket, and the three-label determinant law -/

/-- **THE WEDGE PAIR BRACKET.**  Two wedge shadows sharing a base label form a
minor against two probes, and that minor is one height times one atom bracket
times the plane bracket of the probes.  No hypothesis. -/
theorem wedgeShadow_pair_bracket {size : ℕ} (design : WeightedDesign size 3)
    (normalVec probeOne probeTwo : Fin 3 → ℝ) (baseLabel firstLabel secondLabel : Fin size) :
    wedgeShadow design normalVec probeOne baseLabel firstLabel
        * wedgeShadow design normalVec probeTwo baseLabel secondLabel
      - wedgeShadow design normalVec probeOne baseLabel secondLabel
        * wedgeShadow design normalVec probeTwo baseLabel firstLabel
      = (design.atom baseLabel ⬝ᵥ normalVec) * atomBracket design baseLabel firstLabel secondLabel
          * tripleBracket probeOne probeTwo normalVec := by
  have hbinet := dotProduct_pair_sub_eq_tripleBracket
    ((normalVec ⬝ᵥ design.atom baseLabel) • design.atom firstLabel
      - (normalVec ⬝ᵥ design.atom firstLabel) • design.atom baseLabel)
    ((normalVec ⬝ᵥ design.atom baseLabel) • design.atom secondLabel
      - (normalVec ⬝ᵥ design.atom secondLabel) • design.atom baseLabel)
    probeOne probeTwo
  rw [tripleBracket_shadowPair (design.atom baseLabel) (design.atom firstLabel)
    (design.atom secondLabel) normalVec (crossProduct probeOne probeTwo)] at hbinet
  rw [dotProduct_crossProduct_eq_tripleBracket probeOne probeTwo normalVec] at hbinet
  simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul] at hbinet
  simp only [wedgeShadow, atomBracket]
  rw [dotProduct_comm normalVec (design.atom baseLabel),
    dotProduct_comm normalVec (design.atom firstLabel),
    dotProduct_comm normalVec (design.atom secondLabel)] at hbinet
  linarith [hbinet]

/-- The wedge total of a three-label sharp set, written out. -/
noncomputable def tripleWedgeValue {size : ℕ} (design : WeightedDesign size 3)
    (measure : Fin size → ℝ) (labelOne labelTwo labelThree : Fin size)
    (normalVec probeVec : Fin 3 → ℝ) : ℝ :=
  measure labelOne * measure labelTwo
      * wedgeShadow design normalVec probeVec labelOne labelTwo ^ 2
    + measure labelOne * measure labelThree
      * wedgeShadow design normalVec probeVec labelOne labelThree ^ 2
    + measure labelTwo * measure labelThree
      * wedgeShadow design normalVec probeVec labelTwo labelThree ^ 2

/-- The polarization of `Gtz.tripleWedgeValue` at a pair of probes. -/
noncomputable def tripleWedgePairing {size : ℕ} (design : WeightedDesign size 3)
    (measure : Fin size → ℝ) (labelOne labelTwo labelThree : Fin size)
    (normalVec probeOne probeTwo : Fin 3 → ℝ) : ℝ :=
  measure labelOne * measure labelTwo
      * (wedgeShadow design normalVec probeOne labelOne labelTwo
        * wedgeShadow design normalVec probeTwo labelOne labelTwo)
    + measure labelOne * measure labelThree
      * (wedgeShadow design normalVec probeOne labelOne labelThree
        * wedgeShadow design normalVec probeTwo labelOne labelThree)
    + measure labelTwo * measure labelThree
      * (wedgeShadow design normalVec probeOne labelTwo labelThree
        * wedgeShadow design normalVec probeTwo labelTwo labelThree)

theorem tripleWedgePairing_self {size : ℕ} (design : WeightedDesign size 3)
    (measure : Fin size → ℝ) (labelOne labelTwo labelThree : Fin size)
    (normalVec probeVec : Fin 3 → ℝ) :
    tripleWedgePairing design measure labelOne labelTwo labelThree normalVec probeVec probeVec
      = tripleWedgeValue design measure labelOne labelTwo labelThree normalVec probeVec := by
  unfold tripleWedgePairing tripleWedgeValue
  ring

/-- **THE THREE-LABEL WEDGE DETERMINANT LAW.**  The two-by-two determinant of the
three-label wedge form, read through a pair of probes, is the product of the
three measures, the square of the atom bracket, the measure-weighted height
total, and the square of the plane bracket of the probes.  No hypothesis: no unit
normal, no flat set, no orthogonal probe, and no rank-three position. -/
theorem tripleWedge_determinant {size : ℕ} (design : WeightedDesign size 3)
    (measure : Fin size → ℝ) (labelOne labelTwo labelThree : Fin size)
    (normalVec probeOne probeTwo : Fin 3 → ℝ) :
    tripleWedgeValue design measure labelOne labelTwo labelThree normalVec probeOne
        * tripleWedgeValue design measure labelOne labelTwo labelThree normalVec probeTwo
      - tripleWedgePairing design measure labelOne labelTwo labelThree normalVec probeOne
          probeTwo ^ 2
      = measure labelOne * measure labelTwo * measure labelThree
          * atomBracket design labelOne labelTwo labelThree ^ 2
          * (measure labelOne * (design.atom labelOne ⬝ᵥ normalVec) ^ 2
              + measure labelTwo * (design.atom labelTwo ⬝ᵥ normalVec) ^ 2
              + measure labelThree * (design.atom labelThree ⬝ᵥ normalVec) ^ 2)
          * tripleBracket probeOne probeTwo normalVec ^ 2 := by
  have hone := wedgeShadow_pair_bracket design normalVec probeOne probeTwo labelOne labelTwo
    labelThree
  have htwo := wedgeShadow_pair_bracket design normalVec probeOne probeTwo labelTwo labelOne
    labelThree
  have hthree := wedgeShadow_pair_bracket design normalVec probeOne probeTwo labelThree labelOne
    labelTwo
  rw [wedgeShadow_swap design normalVec probeOne labelOne labelTwo,
    wedgeShadow_swap design normalVec probeTwo labelOne labelTwo] at htwo
  rw [wedgeShadow_swap design normalVec probeOne labelOne labelThree,
    wedgeShadow_swap design normalVec probeTwo labelOne labelThree,
    wedgeShadow_swap design normalVec probeOne labelTwo labelThree,
    wedgeShadow_swap design normalVec probeTwo labelTwo labelThree] at hthree
  have hbracketTwo : atomBracket design labelTwo labelOne labelThree
      = -atomBracket design labelOne labelTwo labelThree := by
    simp only [atomBracket]
    exact tripleBracket_swapLeft (design.atom labelTwo) (design.atom labelOne)
      (design.atom labelThree)
  have hbracketThree : atomBracket design labelThree labelOne labelTwo
      = atomBracket design labelOne labelTwo labelThree := by
    simp only [atomBracket, tripleBracket_eq]
    ring
  rw [hbracketTwo] at htwo
  rw [hbracketThree] at hthree
  set shadowOneTwoFirst := wedgeShadow design normalVec probeOne labelOne labelTwo with hs12a
  set shadowOneTwoSecond := wedgeShadow design normalVec probeTwo labelOne labelTwo with hs12b
  set shadowOneThreeFirst := wedgeShadow design normalVec probeOne labelOne labelThree with hs13a
  set shadowOneThreeSecond := wedgeShadow design normalVec probeTwo labelOne labelThree with hs13b
  set shadowTwoThreeFirst := wedgeShadow design normalVec probeOne labelTwo labelThree with hs23a
  set shadowTwoThreeSecond := wedgeShadow design normalVec probeTwo labelTwo labelThree with hs23b
  set heightOne := design.atom labelOne ⬝ᵥ normalVec with hh1
  set heightTwo := design.atom labelTwo ⬝ᵥ normalVec with hh2
  set heightThree := design.atom labelThree ⬝ᵥ normalVec with hh3
  set bracketValue := atomBracket design labelOne labelTwo labelThree with hbr
  set planeBracket := tripleBracket probeOne probeTwo normalVec with hpl
  have hminorOne : shadowOneTwoFirst * shadowOneThreeSecond
      - shadowOneThreeFirst * shadowOneTwoSecond = heightOne * bracketValue * planeBracket := hone
  have hminorTwo : shadowOneTwoFirst * shadowTwoThreeSecond
      - shadowTwoThreeFirst * shadowOneTwoSecond = heightTwo * bracketValue * planeBracket := by
    linarith [htwo]
  have hminorThree : shadowOneThreeFirst * shadowTwoThreeSecond
      - shadowTwoThreeFirst * shadowOneThreeSecond
      = heightThree * bracketValue * planeBracket := by
    linarith [hthree]
  unfold tripleWedgeValue tripleWedgePairing
  have hlagrange :
      (measure labelOne * measure labelTwo * shadowOneTwoFirst ^ 2
          + measure labelOne * measure labelThree * shadowOneThreeFirst ^ 2
          + measure labelTwo * measure labelThree * shadowTwoThreeFirst ^ 2)
        * (measure labelOne * measure labelTwo * shadowOneTwoSecond ^ 2
          + measure labelOne * measure labelThree * shadowOneThreeSecond ^ 2
          + measure labelTwo * measure labelThree * shadowTwoThreeSecond ^ 2)
        - (measure labelOne * measure labelTwo
              * (shadowOneTwoFirst * shadowOneTwoSecond)
            + measure labelOne * measure labelThree
              * (shadowOneThreeFirst * shadowOneThreeSecond)
            + measure labelTwo * measure labelThree
              * (shadowTwoThreeFirst * shadowTwoThreeSecond)) ^ 2
      = (measure labelOne * measure labelTwo) * (measure labelOne * measure labelThree)
            * (shadowOneTwoFirst * shadowOneThreeSecond
                - shadowOneThreeFirst * shadowOneTwoSecond) ^ 2
        + (measure labelOne * measure labelTwo) * (measure labelTwo * measure labelThree)
            * (shadowOneTwoFirst * shadowTwoThreeSecond
                - shadowTwoThreeFirst * shadowOneTwoSecond) ^ 2
        + (measure labelOne * measure labelThree) * (measure labelTwo * measure labelThree)
            * (shadowOneThreeFirst * shadowTwoThreeSecond
                - shadowTwoThreeFirst * shadowOneThreeSecond) ^ 2 := by
    ring
  rw [hlagrange, hminorOne, hminorTwo, hminorThree]
  ring

/-! ## 3.  The sharp determinant law

Parseval enters exactly once, through the landed
`Gtz.sharpNormalGap_eq_normalSurplus`. -/

/-- The three sharp labels carry the split measure, and their measure-weighted
height total is the NORMAL SURPLUS of the selection. -/
theorem splitMeasure_normalSq_triple_eq_surplus {size rank : ℕ} (design : WeightedDesign size rank)
    (selected flatSet : Finset (Fin size)) {sharpOne sharpTwo sharpThree : Fin size}
    (hOneTwo : sharpOne ≠ sharpTwo) (hOneThree : sharpOne ≠ sharpThree)
    (hTwoThree : sharpTwo ≠ sharpThree)
    (hsharp : flatSetᶜ = {sharpOne, sharpTwo, sharpThree}) (normalVec : Fin rank → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    splitMeasure design selected sharpOne * (design.atom sharpOne ⬝ᵥ normalVec) ^ 2
        + splitMeasure design selected sharpTwo * (design.atom sharpTwo ⬝ᵥ normalVec) ^ 2
        + splitMeasure design selected sharpThree * (design.atom sharpThree ⬝ᵥ normalVec) ^ 2
      = (∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec := by
  classical
  have hnotOne : sharpOne ∉ ({sharpTwo, sharpThree} : Finset (Fin size)) := by
    simp [hOneTwo, hOneThree]
  have hnotTwo : sharpTwo ∉ ({sharpThree} : Finset (Fin size)) := by simp [hTwoThree]
  have htriple : ∑ label ∈ flatSetᶜ, splitMeasure design selected label
        * (design.atom label ⬝ᵥ normalVec) ^ 2
      = splitMeasure design selected sharpOne * (design.atom sharpOne ⬝ᵥ normalVec) ^ 2
        + splitMeasure design selected sharpTwo * (design.atom sharpTwo ⬝ᵥ normalVec) ^ 2
        + splitMeasure design selected sharpThree * (design.atom sharpThree ⬝ᵥ normalVec) ^ 2 := by
    rw [hsharp, Finset.sum_insert hnotOne, Finset.sum_insert hnotTwo, Finset.sum_singleton]
    ring
  have hleft : ∑ label ∈ selected \ flatSet, splitMeasure design selected label
        * (design.atom label ⬝ᵥ normalVec) ^ 2
      = ∑ label ∈ selected \ flatSet, weightDeficit design label
        * (design.atom label ⬝ᵥ normalVec) ^ 2 :=
    Finset.sum_congr rfl fun label hmem => by
      rw [splitMeasure_of_mem design (Finset.mem_sdiff.mp hmem).1]
  have hright : ∑ label ∈ selectedᶜ \ flatSet, splitMeasure design selected label
        * (design.atom label ⬝ᵥ normalVec) ^ 2
      = (-1) * ∑ label ∈ selectedᶜ \ flatSet, design.weight label
        * (design.atom label ⬝ᵥ normalVec) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun label hmem => by
      rw [splitMeasure_of_notMem design (Finset.mem_compl.mp (Finset.mem_sdiff.mp hmem).1)]
      ring
  have hunion : ∑ label ∈ flatSetᶜ, splitMeasure design selected label
        * (design.atom label ⬝ᵥ normalVec) ^ 2
      = (∑ label ∈ selected \ flatSet, weightDeficit design label
            * (design.atom label ⬝ᵥ normalVec) ^ 2)
        - ∑ label ∈ selectedᶜ \ flatSet, design.weight label
            * (design.atom label ⬝ᵥ normalVec) ^ 2 := by
    rw [← sharp_union selected flatSet,
      Finset.sum_union (sharp_disjoint selected flatSet), hleft, hright]
    ring
  rw [← htriple, hunion,
    sharpNormalGap_eq_normalSurplus design selected flatSet normalVec hflat]

/-- The sharp balance is the three-label wedge value of the split measure. -/
theorem sharpBalanceValue_eq_tripleWedgeValue {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) {sharpOne sharpTwo sharpThree : Fin size}
    (hOneTwo : sharpOne ≠ sharpTwo) (hOneThree : sharpOne ≠ sharpThree)
    (hTwoThree : sharpTwo ≠ sharpThree)
    (hsharp : flatSetᶜ = {sharpOne, sharpTwo, sharpThree}) (normalVec probeVec : Fin 3 → ℝ) :
    sharpBalanceValue design selected flatSet normalVec probeVec
      = tripleWedgeValue design (splitMeasure design selected) sharpOne sharpTwo sharpThree
          normalVec probeVec := by
  rw [sharpBalanceValue_of_sharp_triple design selected flatSet hOneTwo hOneThree hTwoThree
    hsharp normalVec probeVec]
  unfold tripleWedgeValue
  ring

/-- **THE SHARP DETERMINANT LAW.**  The two-by-two determinant of the sharp
balance form, read through a pair of probes, is the product of the three split
measures, the square of the sharp atom bracket, the NORMAL SURPLUS of the
selection, and the square of the plane bracket of the probes.

So the sharp balance and the normal surplus, the two ingredients that
`Gtz.LineFlatSplitSelectorAt` asks for, are one object read two ways. -/
theorem sharpBalance_determinant {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) {sharpOne sharpTwo sharpThree : Fin size}
    (hOneTwo : sharpOne ≠ sharpTwo) (hOneThree : sharpOne ≠ sharpThree)
    (hTwoThree : sharpTwo ≠ sharpThree)
    (hsharp : flatSetᶜ = {sharpOne, sharpTwo, sharpThree}) (normalVec probeOne probeTwo : Fin 3 → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    sharpBalanceValue design selected flatSet normalVec probeOne
        * sharpBalanceValue design selected flatSet normalVec probeTwo
      - tripleWedgePairing design (splitMeasure design selected) sharpOne sharpTwo sharpThree
          normalVec probeOne probeTwo ^ 2
      = splitMeasure design selected sharpOne * splitMeasure design selected sharpTwo
          * splitMeasure design selected sharpThree
          * atomBracket design sharpOne sharpTwo sharpThree ^ 2
          * ((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
          * tripleBracket probeOne probeTwo normalVec ^ 2 := by
  rw [sharpBalanceValue_eq_tripleWedgeValue design selected flatSet hOneTwo hOneThree hTwoThree
      hsharp normalVec probeOne,
    sharpBalanceValue_eq_tripleWedgeValue design selected flatSet hOneTwo hOneThree hTwoThree
      hsharp normalVec probeTwo,
    tripleWedge_determinant design (splitMeasure design selected) sharpOne sharpTwo sharpThree
      normalVec probeOne probeTwo,
    splitMeasure_normalSq_triple_eq_surplus design selected flatSet hOneTwo hOneThree hTwoThree
      hsharp normalVec hflat]

/-- **THE SHARP FORM IS DEFINITE ON A POSITIVE DETERMINANT.**  A positive sharp
determinant forces the sharp balance to carry the same strict sign at the two
probes. -/
theorem sharpBalanceValue_mul_pos {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) {sharpOne sharpTwo sharpThree : Fin size}
    (hOneTwo : sharpOne ≠ sharpTwo) (hOneThree : sharpOne ≠ sharpThree)
    (hTwoThree : sharpTwo ≠ sharpThree)
    (hsharp : flatSetᶜ = {sharpOne, sharpTwo, sharpThree}) (normalVec probeOne probeTwo : Fin 3 → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0)
    (hdeterminant : 0 < splitMeasure design selected sharpOne * splitMeasure design selected sharpTwo
      * splitMeasure design selected sharpThree
      * atomBracket design sharpOne sharpTwo sharpThree ^ 2
      * ((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
      * tripleBracket probeOne probeTwo normalVec ^ 2) :
    0 < sharpBalanceValue design selected flatSet normalVec probeOne
      * sharpBalanceValue design selected flatSet normalVec probeTwo := by
  have hlaw := sharpBalance_determinant design selected flatSet hOneTwo hOneThree hTwoThree
    hsharp normalVec probeOne probeTwo hflat
  nlinarith [hlaw, hdeterminant, sq_nonneg (tripleWedgePairing design (splitMeasure design selected)
    sharpOne sharpTwo sharpThree normalVec probeOne probeTwo)]

/-! ## 4.  The probe is a quadratic variable, and a negative determinant supplies
a killing probe

The wedge shadow is linear in the probe, so the sharp balance is a quadratic form
on the probe plane.  A negative determinant then names an explicit probe where
the sharp balance is not positive.  That refines the landed
`Gtz.not_forall_sharpBalanceValue_pos`, which needed a vanishing pair wedge. -/

theorem wedgeShadow_add_probe {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec probeOne probeTwo : Fin rank → ℝ) (weightOne weightTwo : ℝ)
    (leftLabel rightLabel : Fin size) :
    wedgeShadow design normalVec (weightOne • probeOne + weightTwo • probeTwo) leftLabel rightLabel
      = weightOne * wedgeShadow design normalVec probeOne leftLabel rightLabel
        + weightTwo * wedgeShadow design normalVec probeTwo leftLabel rightLabel := by
  simp only [wedgeShadow, dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

/-- The three-label wedge value is a quadratic form in the probe. -/
theorem tripleWedgeValue_add_probe {size : ℕ} (design : WeightedDesign size 3)
    (measure : Fin size → ℝ) (labelOne labelTwo labelThree : Fin size)
    (normalVec probeOne probeTwo : Fin 3 → ℝ) (weightOne weightTwo : ℝ) :
    tripleWedgeValue design measure labelOne labelTwo labelThree normalVec
        (weightOne • probeOne + weightTwo • probeTwo)
      = weightOne ^ 2
          * tripleWedgeValue design measure labelOne labelTwo labelThree normalVec probeOne
        + 2 * weightOne * weightTwo
          * tripleWedgePairing design measure labelOne labelTwo labelThree normalVec probeOne
            probeTwo
        + weightTwo ^ 2
          * tripleWedgeValue design measure labelOne labelTwo labelThree normalVec probeTwo := by
  unfold tripleWedgeValue tripleWedgePairing
  rw [wedgeShadow_add_probe design normalVec probeOne probeTwo weightOne weightTwo labelOne
      labelTwo,
    wedgeShadow_add_probe design normalVec probeOne probeTwo weightOne weightTwo labelOne
      labelThree,
    wedgeShadow_add_probe design normalVec probeOne probeTwo weightOne weightTwo labelTwo
      labelThree]
  ring

/-- **A NEGATIVE SHARP DETERMINANT KILLS THE SHARP BALANCE.**  When the sharp
determinant at a probe pair is negative, one explicit combination of the two
probes reads the sharp balance as nonpositive.  The combination is written from
the two probe values and their pairing alone. -/
theorem exists_mixedProbe_sharpBalanceValue_nonpos {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) {sharpOne sharpTwo sharpThree : Fin size}
    (hOneTwo : sharpOne ≠ sharpTwo) (hOneThree : sharpOne ≠ sharpThree)
    (hTwoThree : sharpTwo ≠ sharpThree)
    (hsharp : flatSetᶜ = {sharpOne, sharpTwo, sharpThree}) (normalVec probeOne probeTwo : Fin 3 → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0)
    (hdeterminant : splitMeasure design selected sharpOne * splitMeasure design selected sharpTwo
      * splitMeasure design selected sharpThree
      * atomBracket design sharpOne sharpTwo sharpThree ^ 2
      * ((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
      * tripleBracket probeOne probeTwo normalVec ^ 2 < 0) :
    ∃ mixOne mixTwo : ℝ, (mixOne ≠ 0 ∨ mixTwo ≠ 0)
      ∧ sharpBalanceValue design selected flatSet normalVec
          (mixOne • probeOne + mixTwo • probeTwo) ≤ 0 := by
  have hlaw := sharpBalance_determinant design selected flatSet hOneTwo hOneThree hTwoThree
    hsharp normalVec probeOne probeTwo hflat
  set valueOne := sharpBalanceValue design selected flatSet normalVec probeOne with hvalueOne
  set valueTwo := sharpBalanceValue design selected flatSet normalVec probeTwo with hvalueTwo
  set pairing := tripleWedgePairing design (splitMeasure design selected) sharpOne sharpTwo
    sharpThree normalVec probeOne probeTwo with hpairing
  have hquad : ∀ mixOne mixTwo : ℝ,
      sharpBalanceValue design selected flatSet normalVec (mixOne • probeOne + mixTwo • probeTwo)
        = mixOne ^ 2 * valueOne + 2 * mixOne * mixTwo * pairing + mixTwo ^ 2 * valueTwo := by
    intro mixOne mixTwo
    rw [hvalueOne, hvalueTwo, hpairing,
      sharpBalanceValue_eq_tripleWedgeValue design selected flatSet hOneTwo hOneThree hTwoThree
        hsharp normalVec (mixOne • probeOne + mixTwo • probeTwo),
      sharpBalanceValue_eq_tripleWedgeValue design selected flatSet hOneTwo hOneThree hTwoThree
        hsharp normalVec probeOne,
      sharpBalanceValue_eq_tripleWedgeValue design selected flatSet hOneTwo hOneThree hTwoThree
        hsharp normalVec probeTwo]
    exact tripleWedgeValue_add_probe design (splitMeasure design selected) sharpOne sharpTwo
      sharpThree normalVec probeOne probeTwo mixOne mixTwo
  have hgap : valueOne * valueTwo - pairing ^ 2 < 0 := by rw [hlaw]; exact hdeterminant
  rcases le_or_gt valueOne 0 with hnonpos | hpos
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    rw [hquad 1 0]
    nlinarith [hnonpos]
  · refine ⟨-pairing, valueOne, Or.inr (ne_of_gt hpos), ?_⟩
    rw [hquad (-pairing) valueOne]
    nlinarith [hgap, hpos]

/-! ## 5.  The surplus floor

Weighted Parseval at the normal spends all of its mass on the SHARP labels,
because the flat labels read the normal as zero.  The sharp weights sum to less
than one, so some sharp label carries a height square of more than one.  Every
selection through that label then has a positive normal surplus, with no probe
and no domination hypothesis at all. -/

/-- Parseval, restricted to the sharp labels. -/
theorem sum_sharp_weight_normalSq {size rank : ℕ} (design : WeightedDesign size rank)
    (flatSet : Finset (Fin size)) (normalVec : Fin rank → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    ∑ label ∈ flatSetᶜ, design.weight label * (design.atom label ⬝ᵥ normalVec) ^ 2
      = normalVec ⬝ᵥ normalVec := by
  classical
  have hsplit := Finset.sum_add_sum_compl flatSet
    (fun label => design.weight label * (design.atom label ⬝ᵥ normalVec) ^ 2)
  have hzero : ∑ label ∈ flatSet, design.weight label * (design.atom label ⬝ᵥ normalVec) ^ 2 = 0 :=
    Finset.sum_eq_zero fun label hmem => by rw [hflat label hmem]; ring
  rw [hzero, zero_add] at hsplit
  rw [hsplit]
  exact (dotProduct_self_eq_sum_weight_mul_sq design normalVec).symm

/-- The sharp weight total is less than one when the flat set is nonempty. -/
theorem sum_sharp_weight_lt_one {size rank : ℕ} (design : WeightedDesign size rank)
    {flatSet : Finset (Fin size)} (hflatNonempty : flatSet.Nonempty) :
    ∑ label ∈ flatSetᶜ, design.weight label < 1 := by
  classical
  have hsplit := Finset.sum_add_sum_compl flatSet design.weight
  have hpos : 0 < ∑ label ∈ flatSet, design.weight label :=
    Finset.sum_pos (fun label _ => design.weight_pos label) hflatNonempty
  have htotal : ∑ label, design.weight label = 1 := design.weight_sum_one
  linarith [hsplit, hpos, htotal]

/-- **THE SURPLUS FLOOR.**  Some sharp label reads the unit normal with a height
square of more than one.  The floor is the reciprocal of the sharp weight total,
so it grows as the flat set gets heavier. -/
theorem exists_sharp_normalSq_gt_one {size rank : ℕ} (design : WeightedDesign size rank)
    {flatSet : Finset (Fin size)} (normalVec : Fin rank → ℝ)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0)
    (hsharpNonempty : flatSetᶜ.Nonempty) :
    ∃ sharpLabel ∈ flatSetᶜ,
      1 ≤ (∑ label ∈ flatSetᶜ, design.weight label)
          * (design.atom sharpLabel ⬝ᵥ normalVec) ^ 2 := by
  classical
  by_contra hnone
  push Not at hnone
  have hparseval := sum_sharp_weight_normalSq design flatSet normalVec hflat
  rw [hunit] at hparseval
  have hstrict : ∑ label ∈ flatSetᶜ, design.weight label
        * ((∑ other ∈ flatSetᶜ, design.weight other)
          * (design.atom label ⬝ᵥ normalVec) ^ 2)
      < ∑ label ∈ flatSetᶜ, design.weight label * 1 := by
    refine Finset.sum_lt_sum_of_nonempty hsharpNonempty fun label hmem => ?_
    exact mul_lt_mul_of_pos_left (hnone label hmem) (design.weight_pos label)
  have hleft : ∑ label ∈ flatSetᶜ, design.weight label
        * ((∑ other ∈ flatSetᶜ, design.weight other)
          * (design.atom label ⬝ᵥ normalVec) ^ 2)
      = (∑ other ∈ flatSetᶜ, design.weight other)
        * ∑ label ∈ flatSetᶜ, design.weight label * (design.atom label ⬝ᵥ normalVec) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun label _ => by ring
  rw [hleft, hparseval, mul_one] at hstrict
  simp only [mul_one] at hstrict
  exact absurd hstrict (lt_irrefl _)

/-- **EVERY SELECTION THROUGH ONE SHARP LABEL HAS A POSITIVE SURPLUS.**  The
first conjunct of `Gtz.LineFlatSplitSelectorAt` is discharged for every subset
that holds the tall sharp label, with no probe and no domination hypothesis. -/
theorem exists_sharp_selection_surplus_pos {size rank : ℕ} (design : WeightedDesign size rank)
    {flatSet : Finset (Fin size)} (normalVec : Fin rank → ℝ)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0)
    (hflatNonempty : flatSet.Nonempty) (hsharpNonempty : flatSetᶜ.Nonempty) :
    ∃ sharpLabel ∈ flatSetᶜ, ∀ selected : Finset (Fin size), sharpLabel ∈ selected →
      1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2 := by
  classical
  obtain ⟨sharpLabel, hmem, hfloor⟩ := exists_sharp_normalSq_gt_one design normalVec hunit hflat
    hsharpNonempty
  have hweightLt : ∑ label ∈ flatSetᶜ, design.weight label < 1 :=
    sum_sharp_weight_lt_one design hflatNonempty
  have hweightPos : 0 < ∑ label ∈ flatSetᶜ, design.weight label :=
    Finset.sum_pos (fun label _ => design.weight_pos label) hsharpNonempty
  have hheight : 1 < (design.atom sharpLabel ⬝ᵥ normalVec) ^ 2 := by
    nlinarith [hfloor, hweightLt, hweightPos]
  refine ⟨sharpLabel, hmem, fun selected hselected => ?_⟩
  have hsingle : (design.atom sharpLabel ⬝ᵥ normalVec) ^ 2
      ≤ ∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2 :=
    Finset.single_le_sum (f := fun label => (design.atom label ⬝ᵥ normalVec) ^ 2)
      (fun label _ => sq_nonneg _) hselected
  linarith [hheight, hsingle]

/-! ## 6.  The combined determinant, and its surplus factor

The flat split reads the combined value as `lead * surplus + sharp`.  The lead is
a quadratic form in the probe, and so is the sharp, so the combined value is one
too.  Its determinant then expands on three terms, and the sharp determinant law
puts the surplus in front of all three. -/

/-- The polarization of `Gtz.flatSplitLead` at a pair of probes. -/
noncomputable def flatSplitLeadPairing {size rank : ℕ} (design : WeightedDesign size rank)
    (selected flatSet : Finset (Fin size)) (probeOne probeTwo : Fin rank → ℝ) : ℝ :=
  (∑ label ∈ selected ∩ flatSet,
      (design.atom label ⬝ᵥ probeOne) * (design.atom label ⬝ᵥ probeTwo))
    - ∑ label ∈ flatSet, design.weight label
        * ((design.atom label ⬝ᵥ probeOne) * (design.atom label ⬝ᵥ probeTwo))

theorem flatSplitLeadPairing_self {size rank : ℕ} (design : WeightedDesign size rank)
    (selected flatSet : Finset (Fin size)) (probeVec : Fin rank → ℝ) :
    flatSplitLeadPairing design selected flatSet probeVec probeVec
      = flatSplitLead design selected flatSet probeVec := by
  unfold flatSplitLeadPairing flatSplitLead
  rw [flatLeak_eq_sum]
  have hleft : ∑ label ∈ selected ∩ flatSet,
        (design.atom label ⬝ᵥ probeVec) * (design.atom label ⬝ᵥ probeVec)
      = ∑ label ∈ selected ∩ flatSet, (design.atom label ⬝ᵥ probeVec) ^ 2 :=
    Finset.sum_congr rfl fun label _ => by ring
  have hright : ∑ label ∈ flatSet, design.weight label
        * ((design.atom label ⬝ᵥ probeVec) * (design.atom label ⬝ᵥ probeVec))
      = ∑ label ∈ flatSet, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 :=
    Finset.sum_congr rfl fun label _ => by ring
  rw [hleft, hright]

/-- The polarization of the whole combined value at a pair of probes. -/
noncomputable def flatSplitPairing {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) (sharpOne sharpTwo sharpThree : Fin size)
    (normalVec probeOne probeTwo : Fin 3 → ℝ) : ℝ :=
  flatSplitLeadPairing design selected flatSet probeOne probeTwo
      * ((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
    + tripleWedgePairing design (splitMeasure design selected) sharpOne sharpTwo sharpThree
        normalVec probeOne probeTwo

theorem flatSplitPairing_self {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) {sharpOne sharpTwo sharpThree : Fin size}
    (hOneTwo : sharpOne ≠ sharpTwo) (hOneThree : sharpOne ≠ sharpThree)
    (hTwoThree : sharpTwo ≠ sharpThree)
    (hsharp : flatSetᶜ = {sharpOne, sharpTwo, sharpThree}) (normalVec probeVec : Fin 3 → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    flatSplitPairing design selected flatSet sharpOne sharpTwo sharpThree normalVec probeVec
        probeVec
      = wedgeBalanceValue design selected normalVec probeVec := by
  unfold flatSplitPairing
  rw [flatSplitLeadPairing_self design selected flatSet probeVec,
    tripleWedgePairing_self design (splitMeasure design selected) sharpOne sharpTwo sharpThree
      normalVec probeVec,
    ← sharpBalanceValue_eq_tripleWedgeValue design selected flatSet hOneTwo hOneThree hTwoThree
      hsharp normalVec probeVec,
    wedgeBalanceValue_flatSplit_reading design selected flatSet normalVec probeVec hflat]

/-- **THE COMBINED DETERMINANT FACTORS THROUGH THE SURPLUS.**  The two-by-two
determinant of the combined flat-split form, read through a pair of probes, is
the normal surplus times a REDUCED quantity.  The reduced quantity is linear in
the surplus, and its constant term is the product of the three split measures
times the square of the sharp atom bracket times the square of the plane bracket
of the probes.

That constant term never vanishes off the sharp line locus.  So the whole
determinant test of the selector is one strict inequality in one variable. -/
theorem flatSplit_determinant {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) {sharpOne sharpTwo sharpThree : Fin size}
    (hOneTwo : sharpOne ≠ sharpTwo) (hOneThree : sharpOne ≠ sharpThree)
    (hTwoThree : sharpTwo ≠ sharpThree)
    (hsharp : flatSetᶜ = {sharpOne, sharpTwo, sharpThree}) (normalVec probeOne probeTwo : Fin 3 → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    wedgeBalanceValue design selected normalVec probeOne
        * wedgeBalanceValue design selected normalVec probeTwo
      - flatSplitPairing design selected flatSet sharpOne sharpTwo sharpThree normalVec probeOne
          probeTwo ^ 2
      = ((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
        * (((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
              * (flatSplitLead design selected flatSet probeOne
                  * flatSplitLead design selected flatSet probeTwo
                - flatSplitLeadPairing design selected flatSet probeOne probeTwo ^ 2)
            + (flatSplitLead design selected flatSet probeOne
                  * sharpBalanceValue design selected flatSet normalVec probeTwo
                + sharpBalanceValue design selected flatSet normalVec probeOne
                  * flatSplitLead design selected flatSet probeTwo
                - 2 * flatSplitLeadPairing design selected flatSet probeOne probeTwo
                  * tripleWedgePairing design (splitMeasure design selected) sharpOne sharpTwo
                      sharpThree normalVec probeOne probeTwo)
            + splitMeasure design selected sharpOne * splitMeasure design selected sharpTwo
                * splitMeasure design selected sharpThree
                * atomBracket design sharpOne sharpTwo sharpThree ^ 2
                * tripleBracket probeOne probeTwo normalVec ^ 2) := by
  have hsharpLaw := sharpBalance_determinant design selected flatSet hOneTwo hOneThree hTwoThree
    hsharp normalVec probeOne probeTwo hflat
  have hreadOne := wedgeBalanceValue_flatSplit_reading design selected flatSet normalVec probeOne
    hflat
  have hreadTwo := wedgeBalanceValue_flatSplit_reading design selected flatSet normalVec probeTwo
    hflat
  unfold flatSplitPairing
  rw [hreadOne, hreadTwo]
  set surplus := (∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec
    with hsurplus
  set leadOne := flatSplitLead design selected flatSet probeOne with hleadOne
  set leadTwo := flatSplitLead design selected flatSet probeTwo with hleadTwo
  set leadPair := flatSplitLeadPairing design selected flatSet probeOne probeTwo with hleadPair
  set sharpValueOne := sharpBalanceValue design selected flatSet normalVec probeOne with hsvOne
  set sharpValueTwo := sharpBalanceValue design selected flatSet normalVec probeTwo with hsvTwo
  set sharpPair := tripleWedgePairing design (splitMeasure design selected) sharpOne sharpTwo
    sharpThree normalVec probeOne probeTwo with hsp
  set constantTerm := splitMeasure design selected sharpOne * splitMeasure design selected sharpTwo
    * splitMeasure design selected sharpThree
    * atomBracket design sharpOne sharpTwo sharpThree ^ 2
    * tripleBracket probeOne probeTwo normalVec ^ 2 with hconst
  have hgap : sharpValueOne * sharpValueTwo - sharpPair ^ 2 = constantTerm * surplus := by
    rw [hsharpLaw, hconst, hsurplus]; ring
  nlinarith [hgap]


/-! ## 7.  The plane form, and the intrinsic determinant

A quadratic form on the probe plane, written as a measure-weighted sum of squared
readings of directions that are flat against the normal.  Its determinant is one
number, and the probe pair enters only through the square of its plane bracket.
That number is the thing the selector must decide. -/

/-- The reading of a plane form at one probe. -/
noncomputable def planeFormValue {index : Type*} (support : Finset index) (measure : index → ℝ)
    (direction : index → (Fin 3 → ℝ)) (probeVec : Fin 3 → ℝ) : ℝ :=
  ∑ label ∈ support, measure label * (direction label ⬝ᵥ probeVec) ^ 2

/-- The polarization of a plane form at a pair of probes. -/
noncomputable def planeFormPairing {index : Type*} (support : Finset index) (measure : index → ℝ)
    (direction : index → (Fin 3 → ℝ)) (probeOne probeTwo : Fin 3 → ℝ) : ℝ :=
  ∑ label ∈ support, measure label
    * ((direction label ⬝ᵥ probeOne) * (direction label ⬝ᵥ probeTwo))

/-- The MINOR of a plane form: the number the determinant reads. -/
noncomputable def planeFormMinor {index : Type*} (support : Finset index) (measure : index → ℝ)
    (direction : index → (Fin 3 → ℝ)) (normalVec : Fin 3 → ℝ) : ℝ :=
  (∑ leftLabel ∈ support, ∑ rightLabel ∈ support, measure leftLabel * measure rightLabel
    * tripleBracket (direction leftLabel) (direction rightLabel) normalVec ^ 2) / 2

theorem planeFormPairing_self {index : Type*} (support : Finset index) (measure : index → ℝ)
    (direction : index → (Fin 3 → ℝ)) (probeVec : Fin 3 → ℝ) :
    planeFormPairing support measure direction probeVec probeVec
      = planeFormValue support measure direction probeVec :=
  Finset.sum_congr rfl fun _ _ => by rw [sq]

theorem planeFormValue_smul_measure {index : Type*} (support : Finset index) (measure : index → ℝ)
    (direction : index → (Fin 3 → ℝ)) (scale : ℝ) (probeVec : Fin 3 → ℝ) :
    planeFormValue support (fun label => scale * measure label) direction probeVec
      = scale * planeFormValue support measure direction probeVec := by
  unfold planeFormValue
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem planeFormPairing_smul_measure {index : Type*} (support : Finset index)
    (measure : index → ℝ) (direction : index → (Fin 3 → ℝ)) (scale : ℝ)
    (probeOne probeTwo : Fin 3 → ℝ) :
    planeFormPairing support (fun label => scale * measure label) direction probeOne probeTwo
      = scale * planeFormPairing support measure direction probeOne probeTwo := by
  unfold planeFormPairing
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem planeFormValue_smul_probe {index : Type*} (support : Finset index) (measure : index → ℝ)
    (direction : index → (Fin 3 → ℝ)) (scale : ℝ) (probeVec : Fin 3 → ℝ) :
    planeFormValue support measure direction (scale • probeVec)
      = scale ^ 2 * planeFormValue support measure direction probeVec := by
  unfold planeFormValue
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by rw [dotProduct_smul, smul_eq_mul]; ring

/-- **THE PERPENDICULAR MINOR.**  Two directions flat against a unit normal read
two probes in a two-by-two minor that factors into two plane brackets. -/
theorem perpPair_minor {leftVec rightVec normalVec : Fin 3 → ℝ}
    (hunit : normalVec ⬝ᵥ normalVec = 1) (hleft : leftVec ⬝ᵥ normalVec = 0)
    (hright : rightVec ⬝ᵥ normalVec = 0) (probeOne probeTwo : Fin 3 → ℝ) :
    (leftVec ⬝ᵥ probeOne) * (rightVec ⬝ᵥ probeTwo)
        - (rightVec ⬝ᵥ probeOne) * (leftVec ⬝ᵥ probeTwo)
      = tripleBracket leftVec rightVec normalVec * tripleBracket probeOne probeTwo normalVec := by
  rw [dotProduct_pair_sub_eq_tripleBracket]
  have hreduce := tripleBracket_of_perp_pair hleft hright (crossProduct probeOne probeTwo)
  rw [dotProduct_crossProduct_eq_tripleBracket, hunit, one_mul] at hreduce
  exact hreduce.symm

/-- **THE PLANE FORM DETERMINANT.**  The two-by-two determinant of a plane form,
read through a pair of probes, is the form's MINOR times the square of the plane
bracket of the probes.  So the probe pair contributes a positive factor and
nothing else. -/
theorem planeForm_determinant {index : Type*} (support : Finset index) (measure : index → ℝ)
    (direction : index → (Fin 3 → ℝ)) (normalVec probeOne probeTwo : Fin 3 → ℝ)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hperp : ∀ label ∈ support, direction label ⬝ᵥ normalVec = 0) :
    planeFormValue support measure direction probeOne
        * planeFormValue support measure direction probeTwo
      - planeFormPairing support measure direction probeOne probeTwo ^ 2
      = planeFormMinor support measure direction normalVec
        * tripleBracket probeOne probeTwo normalVec ^ 2 := by
  have hlagrange := sum_sum_wedgeSq_eq_lagrange support measure
    (fun label => direction label ⬝ᵥ probeOne) (fun label => direction label ⬝ᵥ probeTwo)
  have hrewrite : ∑ leftLabel ∈ support, ∑ rightLabel ∈ support,
      measure leftLabel * measure rightLabel
        * ((direction leftLabel ⬝ᵥ probeOne) * (direction rightLabel ⬝ᵥ probeTwo)
            - (direction rightLabel ⬝ᵥ probeOne) * (direction leftLabel ⬝ᵥ probeTwo)) ^ 2
      = (∑ leftLabel ∈ support, ∑ rightLabel ∈ support,
          measure leftLabel * measure rightLabel
            * tripleBracket (direction leftLabel) (direction rightLabel) normalVec ^ 2)
        * tripleBracket probeOne probeTwo normalVec ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun leftLabel hleft => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun rightLabel hright => ?_
    rw [perpPair_minor hunit (hperp leftLabel hleft) (hperp rightLabel hright) probeOne probeTwo]
    ring
  rw [hrewrite] at hlagrange
  unfold planeFormValue planeFormPairing planeFormMinor
  linarith [hlagrange]


/-- **THE LAGRANGE IDENTITY ACROSS TWO INDEX TYPES.**  The landed
`Gtz.sum_sum_wedgeSq_eq_lagrange_pair` needs one index type and one pair of
families.  The flat labels and the sharp pairs of a flat split are indexed
differently, so this is the form the split consumes. -/
theorem sum_sum_crossWedgeSq_eq_lagrange {indexLeft indexRight : Type*}
    (leftSupport : Finset indexLeft) (rightSupport : Finset indexRight)
    (leftMeasure : indexLeft → ℝ) (rightMeasure : indexRight → ℝ)
    (leftNormal leftProbe : indexLeft → ℝ) (rightNormal rightProbe : indexRight → ℝ) :
    ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
        leftMeasure leftLabel * rightMeasure rightLabel
          * (leftNormal leftLabel * rightProbe rightLabel
              - rightNormal rightLabel * leftProbe leftLabel) ^ 2
      = (∑ label ∈ leftSupport, leftMeasure label * leftNormal label ^ 2)
            * (∑ label ∈ rightSupport, rightMeasure label * rightProbe label ^ 2)
          + (∑ label ∈ leftSupport, leftMeasure label * leftProbe label ^ 2)
            * (∑ label ∈ rightSupport, rightMeasure label * rightNormal label ^ 2)
        - 2 * ((∑ label ∈ leftSupport, leftMeasure label * (leftNormal label * leftProbe label))
            * ∑ label ∈ rightSupport, rightMeasure label
                * (rightNormal label * rightProbe label)) := by
  have hsplit : ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
      leftMeasure leftLabel * rightMeasure rightLabel
        * (leftNormal leftLabel * rightProbe rightLabel
            - rightNormal rightLabel * leftProbe leftLabel) ^ 2
      = ((∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
            (leftMeasure leftLabel * leftNormal leftLabel ^ 2)
              * (rightMeasure rightLabel * rightProbe rightLabel ^ 2))
          + ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
              (leftMeasure leftLabel * leftProbe leftLabel ^ 2)
                * (rightMeasure rightLabel * rightNormal rightLabel ^ 2))
        - ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
            2 * ((leftMeasure leftLabel * (leftNormal leftLabel * leftProbe leftLabel))
              * (rightMeasure rightLabel
                  * (rightNormal rightLabel * rightProbe rightLabel))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun leftLabel _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun rightLabel _ => by ring
  have hcross : ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
      2 * ((leftMeasure leftLabel * (leftNormal leftLabel * leftProbe leftLabel))
        * (rightMeasure rightLabel * (rightNormal rightLabel * rightProbe rightLabel)))
      = 2 * ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
          (leftMeasure leftLabel * (leftNormal leftLabel * leftProbe leftLabel))
            * (rightMeasure rightLabel * (rightNormal rightLabel * rightProbe rightLabel)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun leftLabel _ => by rw [Finset.mul_sum]
  rw [hsplit, hcross, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum]

/-- The CROSS MINOR of two plane forms carried by two index types. -/
noncomputable def planeFormCrossMinor {indexLeft indexRight : Type*}
    (leftSupport : Finset indexLeft) (rightSupport : Finset indexRight)
    (leftMeasure : indexLeft → ℝ) (rightMeasure : indexRight → ℝ)
    (leftDirection : indexLeft → (Fin 3 → ℝ)) (rightDirection : indexRight → (Fin 3 → ℝ))
    (normalVec : Fin 3 → ℝ) : ℝ :=
  ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
    leftMeasure leftLabel * rightMeasure rightLabel
      * tripleBracket (leftDirection leftLabel) (rightDirection rightLabel) normalVec ^ 2

/-- **THE PLANE FORM CROSS DETERMINANT.**  The polarized determinant of two plane
forms is their CROSS MINOR times the same square of the plane bracket. -/
theorem planeForm_crossDeterminant {indexLeft indexRight : Type*}
    (leftSupport : Finset indexLeft) (rightSupport : Finset indexRight)
    (leftMeasure : indexLeft → ℝ) (rightMeasure : indexRight → ℝ)
    (leftDirection : indexLeft → (Fin 3 → ℝ)) (rightDirection : indexRight → (Fin 3 → ℝ))
    (normalVec probeOne probeTwo : Fin 3 → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hperpLeft : ∀ label ∈ leftSupport, leftDirection label ⬝ᵥ normalVec = 0)
    (hperpRight : ∀ label ∈ rightSupport, rightDirection label ⬝ᵥ normalVec = 0) :
    planeFormValue leftSupport leftMeasure leftDirection probeOne
          * planeFormValue rightSupport rightMeasure rightDirection probeTwo
        + planeFormValue leftSupport leftMeasure leftDirection probeTwo
          * planeFormValue rightSupport rightMeasure rightDirection probeOne
        - 2 * (planeFormPairing leftSupport leftMeasure leftDirection probeOne probeTwo
          * planeFormPairing rightSupport rightMeasure rightDirection probeOne probeTwo)
      = planeFormCrossMinor leftSupport rightSupport leftMeasure rightMeasure leftDirection
          rightDirection normalVec * tripleBracket probeOne probeTwo normalVec ^ 2 := by
  have hlagrange := sum_sum_crossWedgeSq_eq_lagrange leftSupport rightSupport leftMeasure
    rightMeasure (fun label => leftDirection label ⬝ᵥ probeOne)
    (fun label => leftDirection label ⬝ᵥ probeTwo)
    (fun label => rightDirection label ⬝ᵥ probeOne)
    (fun label => rightDirection label ⬝ᵥ probeTwo)
  have hkey : ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
      leftMeasure leftLabel * rightMeasure rightLabel
        * ((leftDirection leftLabel ⬝ᵥ probeOne) * (rightDirection rightLabel ⬝ᵥ probeTwo)
            - (rightDirection rightLabel ⬝ᵥ probeOne)
              * (leftDirection leftLabel ⬝ᵥ probeTwo)) ^ 2
      = planeFormCrossMinor leftSupport rightSupport leftMeasure rightMeasure leftDirection
          rightDirection normalVec * tripleBracket probeOne probeTwo normalVec ^ 2 := by
    unfold planeFormCrossMinor
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun leftLabel hleft => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun rightLabel hright => ?_
    rw [perpPair_minor hunit (hperpLeft leftLabel hleft) (hperpRight rightLabel hright)
      probeOne probeTwo]
    ring
  rw [hkey] at hlagrange
  unfold planeFormValue planeFormPairing
  linarith [hlagrange]

/-! ## 8.  The flat split written as two plane forms -/

/-- The direction the wedge shadow reads.  It is flat against the normal at every
pair of labels, whatever the design and the normal. -/
noncomputable def wedgeDirection {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec : Fin rank → ℝ) (leftLabel rightLabel : Fin size) : Fin rank → ℝ :=
  (design.atom leftLabel ⬝ᵥ normalVec) • design.atom rightLabel
    - (design.atom rightLabel ⬝ᵥ normalVec) • design.atom leftLabel

theorem wedgeShadow_eq_wedgeDirection_dotProduct {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec probeVec : Fin rank → ℝ) (leftLabel rightLabel : Fin size) :
    wedgeShadow design normalVec probeVec leftLabel rightLabel
      = wedgeDirection design normalVec leftLabel rightLabel ⬝ᵥ probeVec := by
  simp only [wedgeShadow, wedgeDirection, sub_dotProduct, smul_dotProduct, smul_eq_mul]

theorem wedgeDirection_dotProduct_normal {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec : Fin rank → ℝ) (leftLabel rightLabel : Fin size) :
    wedgeDirection design normalVec leftLabel rightLabel ⬝ᵥ normalVec = 0 := by
  simp only [wedgeDirection, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

theorem wedgeDirection_swap {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec : Fin rank → ℝ) (leftLabel rightLabel : Fin size) :
    wedgeDirection design normalVec rightLabel leftLabel
      = -wedgeDirection design normalVec leftLabel rightLabel := by
  unfold wedgeDirection
  abel

theorem tripleBracket_neg_left (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket (-leftVec) midVec rightVec = -tripleBracket leftVec midVec rightVec := by
  simp only [tripleBracket_eq, Pi.neg_apply]
  ring

theorem tripleBracket_neg_mid (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec (-midVec) rightVec = -tripleBracket leftVec midVec rightVec := by
  simp only [tripleBracket_eq, Pi.neg_apply]
  ring

theorem tripleBracket_self_left (leftVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec leftVec rightVec = 0 := by
  simp only [tripleBracket_eq]
  ring

/-- **THE SHADOW BRACKET, AT LABELS.**  Two shadow vectors sharing a base label
have a bracket against the normal equal to the base height times the atom bracket
of the three labels. -/
theorem tripleBracket_wedgeDirection_pair {size : ℕ} (design : WeightedDesign size 3)
    (normalVec : Fin 3 → ℝ) (baseLabel firstLabel secondLabel : Fin size) :
    tripleBracket (wedgeDirection design normalVec baseLabel firstLabel)
        (wedgeDirection design normalVec baseLabel secondLabel) normalVec
      = (design.atom baseLabel ⬝ᵥ normalVec)
        * atomBracket design baseLabel firstLabel secondLabel * (normalVec ⬝ᵥ normalVec) := by
  have hshadow := tripleBracket_shadowPair (design.atom baseLabel) (design.atom firstLabel)
    (design.atom secondLabel) normalVec normalVec
  rw [dotProduct_comm normalVec (design.atom baseLabel),
    dotProduct_comm normalVec (design.atom firstLabel),
    dotProduct_comm normalVec (design.atom secondLabel)] at hshadow
  simp only [wedgeDirection, atomBracket]
  exact hshadow

/-- The lead measure of a flat split: one inside the selection, zero outside, and
the design weight subtracted at every flat label. -/
noncomputable def leadMeasure {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (label : Fin size) : ℝ :=
  (if label ∈ selected then (1 : ℝ) else 0) - design.weight label

/-- The lead is a plane form on the flat labels. -/
theorem flatSplitLead_eq_planeFormValue {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) (probeVec : Fin 3 → ℝ) :
    flatSplitLead design selected flatSet probeVec
      = planeFormValue flatSet (leadMeasure design selected) design.atom probeVec := by
  classical
  unfold flatSplitLead planeFormValue leadMeasure
  rw [flatLeak_eq_sum]
  have hsplit : ∑ label ∈ flatSet,
        ((if label ∈ selected then (1 : ℝ) else 0) - design.weight label)
          * (design.atom label ⬝ᵥ probeVec) ^ 2
      = (∑ label ∈ flatSet, (if label ∈ selected then (1 : ℝ) else 0)
            * (design.atom label ⬝ᵥ probeVec) ^ 2)
        - ∑ label ∈ flatSet, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hsplit]
  have hselect : ∑ label ∈ flatSet, (if label ∈ selected then (1 : ℝ) else 0)
        * (design.atom label ⬝ᵥ probeVec) ^ 2
      = ∑ label ∈ selected ∩ flatSet, (design.atom label ⬝ᵥ probeVec) ^ 2 := by
    have hite : ∀ label : Fin size, (if label ∈ selected then (1 : ℝ) else 0)
        * (design.atom label ⬝ᵥ probeVec) ^ 2
        = if label ∈ selected then (design.atom label ⬝ᵥ probeVec) ^ 2 else 0 := by
      intro label; by_cases hmem : label ∈ selected <;> simp [hmem]
    simp only [hite]
    rw [Finset.sum_ite_mem, Finset.inter_comm]
  rw [hselect]

/-- The lead polarization is the plane form polarization on the flat labels. -/
theorem flatSplitLeadPairing_eq_planeFormPairing {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) (probeOne probeTwo : Fin 3 → ℝ) :
    flatSplitLeadPairing design selected flatSet probeOne probeTwo
      = planeFormPairing flatSet (leadMeasure design selected) design.atom probeOne probeTwo := by
  classical
  unfold flatSplitLeadPairing planeFormPairing leadMeasure
  have hsplit : ∑ label ∈ flatSet,
        ((if label ∈ selected then (1 : ℝ) else 0) - design.weight label)
          * ((design.atom label ⬝ᵥ probeOne) * (design.atom label ⬝ᵥ probeTwo))
      = (∑ label ∈ flatSet, (if label ∈ selected then (1 : ℝ) else 0)
            * ((design.atom label ⬝ᵥ probeOne) * (design.atom label ⬝ᵥ probeTwo)))
        - ∑ label ∈ flatSet, design.weight label
            * ((design.atom label ⬝ᵥ probeOne) * (design.atom label ⬝ᵥ probeTwo)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hsplit]
  have hselect : ∑ label ∈ flatSet, (if label ∈ selected then (1 : ℝ) else 0)
        * ((design.atom label ⬝ᵥ probeOne) * (design.atom label ⬝ᵥ probeTwo))
      = ∑ label ∈ selected ∩ flatSet,
          (design.atom label ⬝ᵥ probeOne) * (design.atom label ⬝ᵥ probeTwo) := by
    have hite : ∀ label : Fin size, (if label ∈ selected then (1 : ℝ) else 0)
        * ((design.atom label ⬝ᵥ probeOne) * (design.atom label ⬝ᵥ probeTwo))
        = if label ∈ selected
            then (design.atom label ⬝ᵥ probeOne) * (design.atom label ⬝ᵥ probeTwo) else 0 := by
      intro label; by_cases hmem : label ∈ selected <;> simp [hmem]
    simp only [hite]
    rw [Finset.sum_ite_mem, Finset.inter_comm]
  rw [hselect]

/-- The three sharp pair directions. -/
noncomputable def sharpPairDirection {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec : Fin rank → ℝ) (sharpOne sharpTwo sharpThree : Fin size) :
    Fin 3 → (Fin rank → ℝ) :=
  ![wedgeDirection design normalVec sharpOne sharpTwo,
    wedgeDirection design normalVec sharpOne sharpThree,
    wedgeDirection design normalVec sharpTwo sharpThree]

/-- The three sharp pair measures. -/
noncomputable def sharpPairMeasure {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (sharpOne sharpTwo sharpThree : Fin size) : Fin 3 → ℝ :=
  ![splitMeasure design selected sharpOne * splitMeasure design selected sharpTwo,
    splitMeasure design selected sharpOne * splitMeasure design selected sharpThree,
    splitMeasure design selected sharpTwo * splitMeasure design selected sharpThree]

theorem sharpPairDirection_perp {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec : Fin rank → ℝ) (sharpOne sharpTwo sharpThree : Fin size)
    (pairIndex : Fin 3) :
    sharpPairDirection design normalVec sharpOne sharpTwo sharpThree pairIndex ⬝ᵥ normalVec = 0 := by
  fin_cases pairIndex <;>
    simp only [sharpPairDirection] <;>
    exact wedgeDirection_dotProduct_normal design normalVec _ _

/-- The sharp balance is a plane form on the three sharp pairs. -/
theorem tripleWedgeValue_eq_planeFormValue {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (sharpOne sharpTwo sharpThree : Fin size)
    (normalVec probeVec : Fin 3 → ℝ) :
    tripleWedgeValue design (splitMeasure design selected) sharpOne sharpTwo sharpThree normalVec
        probeVec
      = planeFormValue Finset.univ (sharpPairMeasure design selected sharpOne sharpTwo sharpThree)
          (sharpPairDirection design normalVec sharpOne sharpTwo sharpThree) probeVec := by
  unfold tripleWedgeValue planeFormValue sharpPairMeasure sharpPairDirection
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, wedgeShadow_eq_wedgeDirection_dotProduct]

theorem tripleWedgePairing_eq_planeFormPairing {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (sharpOne sharpTwo sharpThree : Fin size)
    (normalVec probeOne probeTwo : Fin 3 → ℝ) :
    tripleWedgePairing design (splitMeasure design selected) sharpOne sharpTwo sharpThree normalVec
        probeOne probeTwo
      = planeFormPairing Finset.univ (sharpPairMeasure design selected sharpOne sharpTwo sharpThree)
          (sharpPairDirection design normalVec sharpOne sharpTwo sharpThree) probeOne probeTwo := by
  unfold tripleWedgePairing planeFormPairing sharpPairMeasure sharpPairDirection
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, wedgeShadow_eq_wedgeDirection_dotProduct]

/-! ## 9.  The intrinsic minor of the flat split -/

theorem planeFormMinor_smul_measure {index : Type*} (support : Finset index) (measure : index → ℝ)
    (direction : index → (Fin 3 → ℝ)) (scale : ℝ) (normalVec : Fin 3 → ℝ) :
    planeFormMinor support (fun label => scale * measure label) direction normalVec
      = scale ^ 2 * planeFormMinor support measure direction normalVec := by
  unfold planeFormMinor
  have hinner : ∑ leftLabel ∈ support, ∑ rightLabel ∈ support,
      (scale * measure leftLabel) * (scale * measure rightLabel)
        * tripleBracket (direction leftLabel) (direction rightLabel) normalVec ^ 2
      = scale ^ 2 * ∑ leftLabel ∈ support, ∑ rightLabel ∈ support,
          measure leftLabel * measure rightLabel
            * tripleBracket (direction leftLabel) (direction rightLabel) normalVec ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun leftLabel _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun rightLabel _ => by ring
  simp only []
  rw [hinner]
  ring

theorem planeFormCrossMinor_smul_left {indexLeft indexRight : Type*}
    (leftSupport : Finset indexLeft) (rightSupport : Finset indexRight)
    (leftMeasure : indexLeft → ℝ) (rightMeasure : indexRight → ℝ)
    (leftDirection : indexLeft → (Fin 3 → ℝ)) (rightDirection : indexRight → (Fin 3 → ℝ))
    (scale : ℝ) (normalVec : Fin 3 → ℝ) :
    planeFormCrossMinor leftSupport rightSupport (fun label => scale * leftMeasure label)
        rightMeasure leftDirection rightDirection normalVec
      = scale * planeFormCrossMinor leftSupport rightSupport leftMeasure rightMeasure leftDirection
          rightDirection normalVec := by
  unfold planeFormCrossMinor
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun leftLabel _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun rightLabel _ => by ring

/-- **THE SHARP MINOR IS THE SURPLUS.**  The intrinsic minor of the sharp plane
form carries the three split measures, the square of the sharp atom bracket, and
the normal surplus.  This is `Gtz.sharpBalance_determinant` with the probe pair
removed. -/
theorem planeFormMinor_sharpPair_eq {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) {sharpOne sharpTwo sharpThree : Fin size}
    (hOneTwo : sharpOne ≠ sharpTwo) (hOneThree : sharpOne ≠ sharpThree)
    (hTwoThree : sharpTwo ≠ sharpThree)
    (hsharp : flatSetᶜ = {sharpOne, sharpTwo, sharpThree}) (normalVec : Fin 3 → ℝ)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    planeFormMinor Finset.univ (sharpPairMeasure design selected sharpOne sharpTwo sharpThree)
        (sharpPairDirection design normalVec sharpOne sharpTwo sharpThree) normalVec
      = splitMeasure design selected sharpOne * splitMeasure design selected sharpTwo
        * splitMeasure design selected sharpThree
        * atomBracket design sharpOne sharpTwo sharpThree ^ 2
        * ((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec) := by
  have hbracketTwo : atomBracket design sharpTwo sharpOne sharpThree
      = -atomBracket design sharpOne sharpTwo sharpThree := by
    simp only [atomBracket]
    exact tripleBracket_swapLeft (design.atom sharpTwo) (design.atom sharpOne)
      (design.atom sharpThree)
  have hbracketThree : atomBracket design sharpThree sharpOne sharpTwo
      = atomBracket design sharpOne sharpTwo sharpThree := by
    simp only [atomBracket, tripleBracket_eq]
    ring
  have hzeroOne : tripleBracket (wedgeDirection design normalVec sharpOne sharpTwo)
      (wedgeDirection design normalVec sharpOne sharpThree) normalVec
      = (design.atom sharpOne ⬝ᵥ normalVec)
        * atomBracket design sharpOne sharpTwo sharpThree := by
    rw [tripleBracket_wedgeDirection_pair design normalVec sharpOne sharpTwo sharpThree, hunit,
      mul_one]
  have hzeroTwo : tripleBracket (wedgeDirection design normalVec sharpOne sharpTwo)
      (wedgeDirection design normalVec sharpTwo sharpThree) normalVec
      = (design.atom sharpTwo ⬝ᵥ normalVec)
        * atomBracket design sharpOne sharpTwo sharpThree := by
    rw [wedgeDirection_swap design normalVec sharpTwo sharpOne, tripleBracket_neg_left,
      tripleBracket_wedgeDirection_pair design normalVec sharpTwo sharpOne sharpThree, hunit,
      mul_one, hbracketTwo]
    ring
  have hzeroThree : tripleBracket (wedgeDirection design normalVec sharpOne sharpThree)
      (wedgeDirection design normalVec sharpTwo sharpThree) normalVec
      = (design.atom sharpThree ⬝ᵥ normalVec)
        * atomBracket design sharpOne sharpTwo sharpThree := by
    rw [wedgeDirection_swap design normalVec sharpThree sharpOne,
      wedgeDirection_swap design normalVec sharpThree sharpTwo, tripleBracket_neg_left,
      tripleBracket_neg_mid, neg_neg,
      tripleBracket_wedgeDirection_pair design normalVec sharpThree sharpOne sharpTwo, hunit,
      mul_one, hbracketThree]
  have hsurplus := splitMeasure_normalSq_triple_eq_surplus design selected flatSet hOneTwo
    hOneThree hTwoThree hsharp normalVec hflat
  unfold planeFormMinor sharpPairMeasure sharpPairDirection
  rw [Fin.sum_univ_three]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [tripleBracket_self_left, tripleBracket_self_left, tripleBracket_self_left]
  rw [show tripleBracket (wedgeDirection design normalVec sharpOne sharpThree)
      (wedgeDirection design normalVec sharpOne sharpTwo) normalVec
      = -tripleBracket (wedgeDirection design normalVec sharpOne sharpTwo)
        (wedgeDirection design normalVec sharpOne sharpThree) normalVec from
    tripleBracket_swapLeft _ _ _]
  rw [show tripleBracket (wedgeDirection design normalVec sharpTwo sharpThree)
      (wedgeDirection design normalVec sharpOne sharpTwo) normalVec
      = -tripleBracket (wedgeDirection design normalVec sharpOne sharpTwo)
        (wedgeDirection design normalVec sharpTwo sharpThree) normalVec from
    tripleBracket_swapLeft _ _ _]
  rw [show tripleBracket (wedgeDirection design normalVec sharpTwo sharpThree)
      (wedgeDirection design normalVec sharpOne sharpThree) normalVec
      = -tripleBracket (wedgeDirection design normalVec sharpOne sharpThree)
        (wedgeDirection design normalVec sharpTwo sharpThree) normalVec from
    tripleBracket_swapLeft _ _ _]
  rw [hzeroOne, hzeroTwo, hzeroThree]
  rw [← hsurplus]
  ring

/-! ## 10.  The general wedge minor, at any design, any subset and any unit normal

Section 9 read the flat split.  This section drops the flat set.  The whole wedge
balance is ONE wedge total under the split measure over all the labels, so it is
a plane form indexed by ordered label pairs, and section 7 decides it.  The
outcome is a probe-free criterion for STRICT DOMINATION at rank three, written in
the design's own bracket data. -/

theorem tripleBracket_smul_left (scale : ℝ) (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket (scale • leftVec) midVec rightVec
      = scale * tripleBracket leftVec midVec rightVec := by
  simp only [tripleBracket_eq, Pi.smul_apply, smul_eq_mul]
  ring

theorem tripleBracket_smul_mid (scale : ℝ) (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec (scale • midVec) rightVec
      = scale * tripleBracket leftVec midVec rightVec := by
  simp only [tripleBracket_eq, Pi.smul_apply, smul_eq_mul]
  ring

/-- A nonzero normal at rank three always carries a nonzero flat probe. -/
theorem exists_inPlane_probe_ne_zero {normalVec : Fin 3 → ℝ} (_hnormalNe : normalVec ≠ 0) :
    ∃ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ normalVec = 0 ∧ probeVec ≠ 0 := by
  by_cases hfirst : normalVec 0 = 0 ∧ normalVec 1 = 0
  · refine ⟨![1, 0, 0], ?_, ?_⟩
    · simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      rw [hfirst.1]; ring
    · intro hzero
      have hone : (![1, 0, 0] : Fin 3 → ℝ) 0 = (0 : Fin 3 → ℝ) 0 := by rw [hzero]
      simp only [Matrix.cons_val_zero, Pi.zero_apply] at hone
      exact one_ne_zero hone
  · refine ⟨![-normalVec 1, normalVec 0, 0], ?_, ?_⟩
    · simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring
    · intro hzero
      have hzeroth : (![-normalVec 1, normalVec 0, 0] : Fin 3 → ℝ) 0 = (0 : Fin 3 → ℝ) 0 := by
        rw [hzero]
      have hfirstEntry : (![-normalVec 1, normalVec 0, 0] : Fin 3 → ℝ) 1 = (0 : Fin 3 → ℝ) 1 := by
        rw [hzero]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at hzeroth hfirstEntry
      exact hfirst ⟨hfirstEntry, by linarith [hzeroth]⟩

/-- **THE WEDGE BALANCE IS ONE WEDGE TOTAL.**  Under the split measure, over all
the labels.  This is the flat split at an EMPTY flat set. -/
theorem wedgeBalanceValue_eq_wedgeTotal_splitMeasure {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) :
    wedgeBalanceValue design selected normalVec probeVec
      = wedgeTotal design (splitMeasure design selected) Finset.univ normalVec probeVec := by
  classical
  have hsharp := sharpBalanceValue_eq_wedgeTotal_splitMeasure design selected ∅ normalVec probeVec
  rw [Finset.compl_empty] at hsharp
  rw [← hsharp]
  unfold sharpBalanceValue wedgeBalanceValue
  rw [Finset.sdiff_empty, Finset.sdiff_empty, mixedWedgeTotal_eq_crossWedgeTotal]

/-- The measure a wedge total puts on an ordered pair of labels. -/
noncomputable def wedgePairMeasure {size : ℕ} (measure : Fin size → ℝ)
    (labelPair : Fin size × Fin size) : ℝ :=
  measure labelPair.1 * measure labelPair.2 / 2

/-- The direction a wedge total reads at an ordered pair of labels. -/
noncomputable def wedgePairDirection {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec : Fin rank → ℝ) (labelPair : Fin size × Fin size) : Fin rank → ℝ :=
  wedgeDirection design normalVec labelPair.1 labelPair.2

theorem wedgePairDirection_perp {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec : Fin rank → ℝ) (labelPair : Fin size × Fin size) :
    wedgePairDirection design normalVec labelPair ⬝ᵥ normalVec = 0 :=
  wedgeDirection_dotProduct_normal design normalVec labelPair.1 labelPair.2

/-- **THE WEDGE TOTAL IS A PLANE FORM.**  Indexed by ordered label pairs. -/
theorem wedgeTotal_eq_planeFormValue {size : ℕ} (design : WeightedDesign size 3)
    (measure : Fin size → ℝ) (support : Finset (Fin size)) (normalVec probeVec : Fin 3 → ℝ) :
    wedgeTotal design measure support normalVec probeVec
      = planeFormValue (support ×ˢ support) (wedgePairMeasure measure)
          (wedgePairDirection design normalVec) probeVec := by
  unfold wedgeTotal planeFormValue wedgePairMeasure wedgePairDirection
  rw [Finset.sum_product, Finset.sum_div]
  refine Finset.sum_congr rfl fun leftLabel _ => ?_
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun rightLabel _ => by
    rw [wedgeShadow_eq_wedgeDirection_dotProduct]; ring

/-- The polarization of the wedge balance at a pair of probes. -/
noncomputable def wedgeBalancePairing {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (normalVec probeOne probeTwo : Fin 3 → ℝ) : ℝ :=
  planeFormPairing (Finset.univ ×ˢ Finset.univ)
    (wedgePairMeasure (splitMeasure design selected)) (wedgePairDirection design normalVec)
    probeOne probeTwo

/-- **THE WEDGE MINOR.**  One number, built from the split measure and the
brackets of the design's own shadow directions.  It carries the whole probe
content of strict domination at a unit normal. -/
noncomputable def wedgeMinor {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (normalVec : Fin 3 → ℝ) : ℝ :=
  planeFormMinor (Finset.univ ×ˢ Finset.univ)
    (wedgePairMeasure (splitMeasure design selected)) (wedgePairDirection design normalVec)
    normalVec

theorem wedgeBalanceValue_eq_planeFormValue {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin 3 → ℝ) :
    wedgeBalanceValue design selected normalVec probeVec
      = planeFormValue (Finset.univ ×ˢ Finset.univ)
          (wedgePairMeasure (splitMeasure design selected))
          (wedgePairDirection design normalVec) probeVec := by
  rw [wedgeBalanceValue_eq_wedgeTotal_splitMeasure design selected normalVec probeVec,
    wedgeTotal_eq_planeFormValue design (splitMeasure design selected) Finset.univ normalVec
      probeVec]

/-- **THE WEDGE BALANCE DETERMINANT.**  At any design, any subset, any unit
normal and any pair of probes.  The probe pair enters only as the square of its
plane bracket. -/
theorem wedgeBalanceValue_determinant {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (normalVec probeOne probeTwo : Fin 3 → ℝ)
    (hunit : normalVec ⬝ᵥ normalVec = 1) :
    wedgeBalanceValue design selected normalVec probeOne
        * wedgeBalanceValue design selected normalVec probeTwo
      - wedgeBalancePairing design selected normalVec probeOne probeTwo ^ 2
      = wedgeMinor design selected normalVec * tripleBracket probeOne probeTwo normalVec ^ 2 := by
  rw [wedgeBalanceValue_eq_planeFormValue design selected normalVec probeOne,
    wedgeBalanceValue_eq_planeFormValue design selected normalVec probeTwo]
  exact planeForm_determinant (Finset.univ ×ˢ Finset.univ)
    (wedgePairMeasure (splitMeasure design selected)) (wedgePairDirection design normalVec)
    normalVec probeOne probeTwo hunit
    (fun labelPair _ => wedgePairDirection_perp design normalVec labelPair)

/-- A plane form is a quadratic form in the probe. -/
theorem planeFormValue_add_probe {index : Type*} (support : Finset index) (measure : index → ℝ)
    (direction : index → (Fin 3 → ℝ)) (weightOne weightTwo : ℝ)
    (probeOne probeTwo : Fin 3 → ℝ) :
    planeFormValue support measure direction (weightOne • probeOne + weightTwo • probeTwo)
      = weightOne ^ 2 * planeFormValue support measure direction probeOne
        + 2 * weightOne * weightTwo
          * planeFormPairing support measure direction probeOne probeTwo
        + weightTwo ^ 2 * planeFormValue support measure direction probeTwo := by
  unfold planeFormValue planeFormPairing
  have hexpand : ∀ label : index, measure label
      * (direction label ⬝ᵥ (weightOne • probeOne + weightTwo • probeTwo)) ^ 2
      = weightOne ^ 2 * (measure label * (direction label ⬝ᵥ probeOne) ^ 2)
        + 2 * weightOne * weightTwo
          * (measure label
            * ((direction label ⬝ᵥ probeOne) * (direction label ⬝ᵥ probeTwo)))
        + weightTwo ^ 2 * (measure label * (direction label ⬝ᵥ probeTwo) ^ 2) := by
    intro label
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun label _ => hexpand label), Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

theorem wedgeBalanceValue_add_probe {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (normalVec probeOne probeTwo : Fin 3 → ℝ)
    (weightOne weightTwo : ℝ) :
    wedgeBalanceValue design selected normalVec (weightOne • probeOne + weightTwo • probeTwo)
      = weightOne ^ 2 * wedgeBalanceValue design selected normalVec probeOne
        + 2 * weightOne * weightTwo
          * wedgeBalancePairing design selected normalVec probeOne probeTwo
        + weightTwo ^ 2 * wedgeBalanceValue design selected normalVec probeTwo := by
  rw [wedgeBalanceValue_eq_planeFormValue design selected normalVec
      (weightOne • probeOne + weightTwo • probeTwo),
    wedgeBalanceValue_eq_planeFormValue design selected normalVec probeOne,
    wedgeBalanceValue_eq_planeFormValue design selected normalVec probeTwo]
  exact planeFormValue_add_probe (Finset.univ ×ˢ Finset.univ)
    (wedgePairMeasure (splitMeasure design selected)) (wedgePairDirection design normalVec)
    weightOne weightTwo probeOne probeTwo

theorem wedgeBalanceValue_smul_probe {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin 3 → ℝ) (scale : ℝ) :
    wedgeBalanceValue design selected normalVec (scale • probeVec)
      = scale ^ 2 * wedgeBalanceValue design selected normalVec probeVec := by
  rw [wedgeBalanceValue_eq_planeFormValue design selected normalVec (scale • probeVec),
    wedgeBalanceValue_eq_planeFormValue design selected normalVec probeVec]
  exact planeFormValue_smul_probe (Finset.univ ×ˢ Finset.univ)
    (wedgePairMeasure (splitMeasure design selected)) (wedgePairDirection design normalVec)
    scale probeVec

/-- A vanishing plane bracket at two flat probes makes them proportional. -/
theorem exists_smul_of_tripleBracket_eq_zero {baseVec probeVec normalVec : Fin 3 → ℝ}
    (hunit : normalVec ⬝ᵥ normalVec = 1) (hbasePerp : baseVec ⬝ᵥ normalVec = 0)
    (hprobePerp : probeVec ⬝ᵥ normalVec = 0) (hbaseNe : baseVec ≠ 0)
    (hbracket : tripleBracket baseVec probeVec normalVec = 0) :
    ∃ ratio : ℝ, probeVec = ratio • baseVec := by
  refine eq_smul_of_crossProduct_eq_zero hbaseNe ?_
  have hreduce := tripleBracket_of_perp_pair hbasePerp hprobePerp
    (crossProduct baseVec probeVec)
  rw [hbracket, zero_mul, hunit, one_mul] at hreduce
  have hself : crossProduct baseVec probeVec ⬝ᵥ crossProduct baseVec probeVec = 0 := by
    rw [← tripleBracket_eq_crossProduct_dotProduct]
    exact hreduce.symm
  exact dotProduct_self_eq_zero.mp hself

/-- Two flat probes with a nonzero plane bracket span the plane. -/
theorem ne_zero_of_tripleBracket_ne_zero {baseVec companionVec normalVec : Fin 3 → ℝ}
    (hbracket : tripleBracket baseVec companionVec normalVec ≠ 0) {weightOne weightTwo : ℝ}
    (hnotBoth : weightOne ≠ 0 ∨ weightTwo ≠ 0) :
    weightOne • baseVec + weightTwo • companionVec ≠ 0 := by
  intro hzero
  have hbase : weightOne • baseVec = -(weightTwo • companionVec) := by
    have := hzero
    rw [add_eq_zero_iff_eq_neg] at this
    exact this
  have hfirst : weightOne * tripleBracket baseVec companionVec normalVec = 0 := by
    rw [← tripleBracket_smul_left, hbase, ← neg_smul, tripleBracket_smul_left,
      tripleBracket_self_left]
    ring
  have hcompanion : weightTwo • companionVec = -(weightOne • baseVec) := by
    rw [hbase]; abel
  have hsecond : weightTwo * tripleBracket baseVec companionVec normalVec = 0 := by
    rw [← tripleBracket_smul_mid, hcompanion, ← neg_smul, tripleBracket_smul_mid]
    have hzeroMid : tripleBracket baseVec baseVec normalVec = 0 :=
      tripleBracket_self_left baseVec normalVec
    rw [hzeroMid]
    ring
  rcases hnotBoth with hone | htwo
  · exact hone ((mul_eq_zero.mp hfirst).resolve_right hbracket)
  · exact htwo ((mul_eq_zero.mp hsecond).resolve_right hbracket)

/-! ## 11.  The probe-free criterion for strict domination -/

/-- **THE FRAME CRITERION.**  One positive probe value and one positive wedge
minor force the wedge balance positive at EVERY flat probe.  The probe quantifier
is discharged by the determinant, not by a search. -/
theorem forall_inPlane_wedgeBalanceValue_pos {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) {normalVec baseProbe : Fin 3 → ℝ}
    (hunit : normalVec ⬝ᵥ normalVec = 1) (hbasePerp : baseProbe ⬝ᵥ normalVec = 0)
    (hbaseNe : baseProbe ≠ 0)
    (hbasePos : 0 < wedgeBalanceValue design selected normalVec baseProbe)
    (hminor : 0 < wedgeMinor design selected normalVec) :
    ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ normalVec = 0 → probeVec ≠ 0 →
      0 < wedgeBalanceValue design selected normalVec probeVec := by
  intro probeVec hperp hne
  by_cases hbracket : tripleBracket baseProbe probeVec normalVec = 0
  · obtain ⟨ratio, hratio⟩ := exists_smul_of_tripleBracket_eq_zero hunit hbasePerp hperp hbaseNe
      hbracket
    have hratioNe : ratio ≠ 0 := by
      intro hzero
      rw [hzero, zero_smul] at hratio
      exact hne hratio
    have hratioSq : 0 < ratio ^ 2 := by
      rcases lt_or_gt_of_ne hratioNe with hneg | hpos <;> nlinarith
    rw [hratio, wedgeBalanceValue_smul_probe]
    exact mul_pos hratioSq hbasePos
  · have hdet := wedgeBalanceValue_determinant design selected normalVec baseProbe probeVec hunit
    have hbracketSq : 0 < tripleBracket baseProbe probeVec normalVec ^ 2 := by
      rcases lt_or_gt_of_ne hbracket with hneg | hpos <;> nlinarith
    nlinarith [hdet, mul_pos hminor hbracketSq, hbasePos,
      sq_nonneg (wedgeBalancePairing design selected normalVec baseProbe probeVec)]

/-- **STRICT DOMINATION FROM THREE NUMBERS.**  A positive normal surplus, a
positive wedge minor and one positive probe reading make the subset gap
positive definite.  No probe quantifier anywhere. -/
theorem posDef_of_surplus_and_wedgeMinor {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) {normalVec baseProbe : Fin 3 → ℝ}
    (hunit : normalVec ⬝ᵥ normalVec = 1) (hbasePerp : baseProbe ⬝ᵥ normalVec = 0)
    (hbaseNe : baseProbe ≠ 0)
    (hsurplus : 1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2)
    (hbasePos : 0 < wedgeBalanceValue design selected normalVec baseProbe)
    (hminor : 0 < wedgeMinor design selected normalVec) :
    (subsetSum design selected - 1).PosDef := by
  refine (posDef_iff_normalSurplus_and_wedgeBalance design selected normalVec hunit).mpr
    ⟨hsurplus, fun probeVec hperp hne => ?_⟩
  exact (wedgeBalanceAt_iff_pos_wedgeBalanceValue design selected normalVec probeVec).mpr
    (forall_inPlane_wedgeBalanceValue_pos design selected hunit hbasePerp hbaseNe hbasePos hminor
      probeVec hperp hne)

/-- The companion probe of a flat base probe. -/
theorem tripleBracket_frame_pos {baseVec normalVec : Fin 3 → ℝ}
    (hunit : normalVec ⬝ᵥ normalVec = 1) (hperp : baseVec ⬝ᵥ normalVec = 0) (hne : baseVec ≠ 0) :
    0 < tripleBracket baseVec (crossProduct normalVec baseVec) normalVec := by
  rw [tripleBracket_frame, hunit, hperp, mul_one]
  have hself : 0 < baseVec ⬝ᵥ baseVec := by
    rcases (dotProduct_self_nonneg baseVec).lt_or_eq with hpos | hzero
    · exact hpos
    · exact absurd (dotProduct_self_eq_zero.mp hzero.symm) hne
  linarith [hself]

/-- **THE WEDGE MINOR IS POSITIVE AT EVERY STRICT DOMINATOR.**  So the criterion
of `Gtz.posDef_of_surplus_and_wedgeMinor` is not vacuous, and the three numbers
decide strict domination exactly. -/
theorem wedgeMinor_pos_of_posDef {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    0 < wedgeMinor design selected normalVec := by
  have hnormalNe : normalVec ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    simp only [dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hunit
    exact zero_ne_one hunit
  obtain ⟨baseProbe, hbasePerp, hbaseNe⟩ := exists_inPlane_probe_ne_zero hnormalNe
  obtain ⟨hsurplus, hbalance⟩ :=
    (posDef_iff_normalSurplus_and_wedgeBalance design selected normalVec hunit).mp hposDef
  have hvalue : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ normalVec = 0 → probeVec ≠ 0 →
      0 < wedgeBalanceValue design selected normalVec probeVec := fun probeVec hperp hne =>
    (wedgeBalanceAt_iff_pos_wedgeBalanceValue design selected normalVec probeVec).mp
      (hbalance probeVec hperp hne)
  set companion := crossProduct normalVec baseProbe with hcompanion
  have hcompanionPerp : companion ⬝ᵥ normalVec = 0 :=
    dotProduct_crossProduct_left_self normalVec baseProbe
  have hbracketPos : 0 < tripleBracket baseProbe companion normalVec :=
    tripleBracket_frame_pos hunit hbasePerp hbaseNe
  have hbracketNe : tripleBracket baseProbe companion normalVec ≠ 0 := ne_of_gt hbracketPos
  have hcompanionNe : companion ≠ 0 := by
    intro hzero
    rw [hzero] at hbracketPos
    simp only [tripleBracket_eq, Pi.zero_apply, mul_zero, zero_mul, add_zero,
      sub_self] at hbracketPos
    exact absurd hbracketPos (lt_irrefl 0)
  have hbaseValue := hvalue baseProbe hbasePerp hbaseNe
  set valueBase := wedgeBalanceValue design selected normalVec baseProbe with hvalueBase
  set valueCompanion := wedgeBalanceValue design selected normalVec companion with hvalueCompanion
  set pairing := wedgeBalancePairing design selected normalVec baseProbe companion with hpairing
  have hcombination : 0 < wedgeBalanceValue design selected normalVec
      ((-pairing) • baseProbe + valueBase • companion) := by
    refine hvalue _ ?_ ?_
    · rw [add_dotProduct, smul_dotProduct, smul_dotProduct, hbasePerp, hcompanionPerp]
      simp
    · exact ne_zero_of_tripleBracket_ne_zero hbracketNe (Or.inr (ne_of_gt hbaseValue))
  rw [wedgeBalanceValue_add_probe design selected normalVec baseProbe companion (-pairing)
    valueBase] at hcombination
  have hgap : 0 < valueBase * valueCompanion - pairing ^ 2 := by nlinarith [hcombination,
    hbaseValue]
  have hdet := wedgeBalanceValue_determinant design selected normalVec baseProbe companion hunit
  have hbracketSq : 0 < tripleBracket baseProbe companion normalVec ^ 2 := by nlinarith
  nlinarith [hdet, hgap, hbracketSq]

/-- **THE DECISION.**  Strict domination at rank three, decided by a normal
surplus, a wedge minor and one probe reading. -/
theorem posDef_iff_surplus_and_wedgeMinor {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1) :
    (subsetSum design selected - 1).PosDef
      ↔ (1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2)
        ∧ 0 < wedgeMinor design selected normalVec
        ∧ ∃ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ normalVec = 0 ∧ probeVec ≠ 0
            ∧ 0 < wedgeBalanceValue design selected normalVec probeVec := by
  constructor
  · intro hposDef
    have hnormalNe : normalVec ≠ 0 := by
      intro hzero
      rw [hzero] at hunit
      simp only [dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hunit
      exact zero_ne_one hunit
    obtain ⟨baseProbe, hbasePerp, hbaseNe⟩ := exists_inPlane_probe_ne_zero hnormalNe
    obtain ⟨hsurplus, hbalance⟩ :=
      (posDef_iff_normalSurplus_and_wedgeBalance design selected normalVec hunit).mp hposDef
    exact ⟨hsurplus, wedgeMinor_pos_of_posDef design selected hunit hposDef,
      baseProbe, hbasePerp, hbaseNe,
      (wedgeBalanceAt_iff_pos_wedgeBalanceValue design selected normalVec baseProbe).mp
        (hbalance baseProbe hbasePerp hbaseNe)⟩
  · rintro ⟨hsurplus, hminor, baseProbe, hbasePerp, hbaseNe, hbasePos⟩
    exact posDef_of_surplus_and_wedgeMinor design selected hunit hbasePerp hbaseNe hsurplus
      hbasePos hminor

/-! ## 12.  The wedge minor of a flat split carries the surplus as a factor -/

/-- The combined value is the sum of two plane forms: the scaled flat form and
the sharp form. -/
theorem wedgeBalanceValue_eq_flat_add_sharp {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) {sharpOne sharpTwo sharpThree : Fin size}
    (hOneTwo : sharpOne ≠ sharpTwo) (hOneThree : sharpOne ≠ sharpThree)
    (hTwoThree : sharpTwo ≠ sharpThree)
    (hsharp : flatSetᶜ = {sharpOne, sharpTwo, sharpThree}) (normalVec probeVec : Fin 3 → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    wedgeBalanceValue design selected normalVec probeVec
      = planeFormValue flatSet
          (fun label => ((∑ other ∈ selected, (design.atom other ⬝ᵥ normalVec) ^ 2)
              - normalVec ⬝ᵥ normalVec) * leadMeasure design selected label)
          design.atom probeVec
        + planeFormValue Finset.univ
            (sharpPairMeasure design selected sharpOne sharpTwo sharpThree)
            (sharpPairDirection design normalVec sharpOne sharpTwo sharpThree) probeVec := by
  rw [wedgeBalanceValue_flatSplit_reading design selected flatSet normalVec probeVec hflat,
    planeFormValue_smul_measure flatSet (leadMeasure design selected) design.atom
      ((∑ other ∈ selected, (design.atom other ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
      probeVec,
    ← flatSplitLead_eq_planeFormValue design selected flatSet probeVec,
    sharpBalanceValue_eq_tripleWedgeValue design selected flatSet hOneTwo hOneThree hTwoThree
      hsharp normalVec probeVec,
    tripleWedgeValue_eq_planeFormValue design selected sharpOne sharpTwo sharpThree normalVec
      probeVec]
  ring

/-- The pairing of the pair-indexed form and the pairing of the two-form split
agree, because both polarize the same quadratic form. -/
theorem wedgeBalancePairing_eq_flat_add_sharp {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) {sharpOne sharpTwo sharpThree : Fin size}
    (hOneTwo : sharpOne ≠ sharpTwo) (hOneThree : sharpOne ≠ sharpThree)
    (hTwoThree : sharpTwo ≠ sharpThree)
    (hsharp : flatSetᶜ = {sharpOne, sharpTwo, sharpThree})
    (normalVec probeOne probeTwo : Fin 3 → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    wedgeBalancePairing design selected normalVec probeOne probeTwo
      = planeFormPairing flatSet
          (fun label => ((∑ other ∈ selected, (design.atom other ⬝ᵥ normalVec) ^ 2)
              - normalVec ⬝ᵥ normalVec) * leadMeasure design selected label)
          design.atom probeOne probeTwo
        + planeFormPairing Finset.univ
            (sharpPairMeasure design selected sharpOne sharpTwo sharpThree)
            (sharpPairDirection design normalVec sharpOne sharpTwo sharpThree) probeOne
            probeTwo := by
  have hsum : (1 : ℝ) • probeOne + (1 : ℝ) • probeTwo = probeOne + probeTwo := by
    rw [one_smul, one_smul]
  have hpair := wedgeBalanceValue_add_probe design selected normalVec probeOne probeTwo 1 1
  rw [hsum] at hpair
  have hflatSide := planeFormValue_add_probe flatSet
    (fun label => ((∑ other ∈ selected, (design.atom other ⬝ᵥ normalVec) ^ 2)
      - normalVec ⬝ᵥ normalVec) * leadMeasure design selected label)
    design.atom 1 1 probeOne probeTwo
  rw [hsum] at hflatSide
  have hsharpSide := planeFormValue_add_probe (Finset.univ : Finset (Fin 3))
    (sharpPairMeasure design selected sharpOne sharpTwo sharpThree)
    (sharpPairDirection design normalVec sharpOne sharpTwo sharpThree) 1 1 probeOne probeTwo
  rw [hsum] at hsharpSide
  have hsplitSum := wedgeBalanceValue_eq_flat_add_sharp design selected flatSet hOneTwo hOneThree
    hTwoThree hsharp normalVec (probeOne + probeTwo) hflat
  have hsplitOne := wedgeBalanceValue_eq_flat_add_sharp design selected flatSet hOneTwo hOneThree
    hTwoThree hsharp normalVec probeOne hflat
  have hsplitTwo := wedgeBalanceValue_eq_flat_add_sharp design selected flatSet hOneTwo hOneThree
    hTwoThree hsharp normalVec probeTwo hflat
  rw [hsplitSum, hflatSide, hsharpSide, hsplitOne, hsplitTwo] at hpair
  linarith [hpair]

/-- **THE WEDGE MINOR OF A FLAT SPLIT.**  At every design with a flat set of
complement size three, the wedge minor of every subset factors, and the NORMAL
SURPLUS is one of the two factors.  So the two ingredients that the flat-split
selector asks for are not independent: the surplus divides the minor.

The remaining factor is linear in the surplus, and its constant term is the
product of the three split measures times the square of the sharp atom bracket.
That constant term is positive at every selection that holds exactly one sharp
label, and negative at every selection that holds exactly two. -/
theorem wedgeMinor_eq_surplus_mul_reduced {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) {sharpOne sharpTwo sharpThree : Fin size}
    (hOneTwo : sharpOne ≠ sharpTwo) (hOneThree : sharpOne ≠ sharpThree)
    (hTwoThree : sharpTwo ≠ sharpThree)
    (hsharp : flatSetᶜ = {sharpOne, sharpTwo, sharpThree}) (normalVec : Fin 3 → ℝ)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    wedgeMinor design selected normalVec
      = ((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
        * (((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
              * planeFormMinor flatSet (leadMeasure design selected) design.atom normalVec
            + planeFormCrossMinor flatSet Finset.univ (leadMeasure design selected)
                (sharpPairMeasure design selected sharpOne sharpTwo sharpThree) design.atom
                (sharpPairDirection design normalVec sharpOne sharpTwo sharpThree) normalVec
            + splitMeasure design selected sharpOne * splitMeasure design selected sharpTwo
                * splitMeasure design selected sharpThree
                * atomBracket design sharpOne sharpTwo sharpThree ^ 2) := by
  have hnormalNe : normalVec ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    simp only [dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hunit
    exact zero_ne_one hunit
  obtain ⟨baseProbe, hbasePerp, hbaseNe⟩ := exists_inPlane_probe_ne_zero hnormalNe
  set companion := crossProduct normalVec baseProbe with hcompanionDef
  have hcompanionPerp : companion ⬝ᵥ normalVec = 0 :=
    dotProduct_crossProduct_left_self normalVec baseProbe
  have hbracketPos : 0 < tripleBracket baseProbe companion normalVec :=
    tripleBracket_frame_pos hunit hbasePerp hbaseNe
  set surplus := (∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec
    with hsurplusDef
  set flatMeasure := fun label => surplus * leadMeasure design selected label with hflatMeasure
  set sharpMeasure := sharpPairMeasure design selected sharpOne sharpTwo sharpThree
    with hsharpMeasure
  set sharpDirectionFamily := sharpPairDirection design normalVec sharpOne sharpTwo sharpThree
    with hsharpDirection
  have hflatDet := planeForm_determinant flatSet flatMeasure design.atom normalVec baseProbe
    companion hunit hflat
  have hsharpDet := planeForm_determinant (Finset.univ : Finset (Fin 3)) sharpMeasure
    sharpDirectionFamily normalVec baseProbe companion hunit
    (fun pairIndex _ => sharpPairDirection_perp design normalVec sharpOne sharpTwo sharpThree
      pairIndex)
  have hcrossDet := planeForm_crossDeterminant flatSet (Finset.univ : Finset (Fin 3)) flatMeasure
    sharpMeasure design.atom sharpDirectionFamily normalVec baseProbe companion hunit hflat
    (fun pairIndex _ => sharpPairDirection_perp design normalVec sharpOne sharpTwo sharpThree
      pairIndex)
  have hwedgeDet := wedgeBalanceValue_determinant design selected normalVec baseProbe companion
    hunit
  have hvalueBase := wedgeBalanceValue_eq_flat_add_sharp design selected flatSet hOneTwo hOneThree
    hTwoThree hsharp normalVec baseProbe hflat
  have hvalueCompanion := wedgeBalanceValue_eq_flat_add_sharp design selected flatSet hOneTwo
    hOneThree hTwoThree hsharp normalVec companion hflat
  have hpairing := wedgeBalancePairing_eq_flat_add_sharp design selected flatSet hOneTwo hOneThree
    hTwoThree hsharp normalVec baseProbe companion hflat
  rw [hvalueBase, hvalueCompanion, hpairing] at hwedgeDet
  have hsharpMinor := planeFormMinor_sharpPair_eq design selected flatSet hOneTwo hOneThree
    hTwoThree hsharp normalVec hunit hflat
  have hflatScale := planeFormMinor_smul_measure flatSet (leadMeasure design selected) design.atom
    surplus normalVec
  have hcrossScale := planeFormCrossMinor_smul_left flatSet (Finset.univ : Finset (Fin 3))
    (leadMeasure design selected) sharpMeasure design.atom sharpDirectionFamily surplus normalVec
  have hbracketSq : 0 < tripleBracket baseProbe companion normalVec ^ 2 := by nlinarith
  have hcombine : wedgeMinor design selected normalVec
        * tripleBracket baseProbe companion normalVec ^ 2
      = (surplus * (surplus
            * planeFormMinor flatSet (leadMeasure design selected) design.atom normalVec
          + planeFormCrossMinor flatSet Finset.univ (leadMeasure design selected) sharpMeasure
              design.atom sharpDirectionFamily normalVec
          + splitMeasure design selected sharpOne * splitMeasure design selected sharpTwo
              * splitMeasure design selected sharpThree
              * atomBracket design sharpOne sharpTwo sharpThree ^ 2))
        * tripleBracket baseProbe companion normalVec ^ 2 := by
    rw [← hwedgeDet]
    rw [← hflatMeasure] at hflatScale hcrossScale
    rw [hflatScale] at hflatDet
    rw [hcrossScale] at hcrossDet
    rw [hsharpMinor] at hsharpDet
    nlinarith [hflatDet, hsharpDet, hcrossDet]
  exact mul_right_cancel₀ (ne_of_gt hbracketSq) hcombine

/-! ## 13.  Producers

The criterion of section 11 is a producer of strict domination, so it is a
producer of the objective and of the two line obligations. -/

/-- The residual of the objective, written in wedge minor data.  Three strict
inequalities at one subset, one unit normal and one probe. -/
def WedgeMinorSelector (size : ℕ) : Prop :=
  ∀ design : WeightedDesign size 3, ∃ unitNormal : Fin 3 → ℝ,
    unitNormal ⬝ᵥ unitNormal = 1 ∧ ∃ selected : Finset (Fin size), selected.card = 3
      ∧ (1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
      ∧ 0 < wedgeMinor design selected unitNormal
      ∧ ∃ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 ∧ probeVec ≠ 0
          ∧ 0 < wedgeBalanceValue design selected unitNormal probeVec

theorem dotProduct_self_firstAxis : (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ ![1, 0, 0] = 1 := by
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **THE OBJECTIVE, FROM THE WEDGE MINOR SELECTOR.**  Weighted GTZ at rank
three, at every size, from three strict inequalities per design.  No probe
quantifier, no matrix inverse and no eigenvalue. -/
theorem gtzWeighted_rank_three_of_wedgeMinorSelector {size : ℕ}
    (hselector : WedgeMinorSelector size) : GtzWeighted size 3 := by
  intro design
  obtain ⟨unitNormal, hunit, selected, hcard, hsurplus, hminor, probeVec, hperp, hprobeNe,
    hpos⟩ := hselector design
  exact ⟨selected, hcard,
    Matrix.PosDef.posSemidef
      (posDef_of_surplus_and_wedgeMinor design selected hunit hperp hprobeNe hsurplus hpos
        hminor)⟩

/-- **THE SELECTOR IS EXACTLY THE STRICT HALF.**  It is not a strengthening
beyond strict domination, and it is not a weakening of it. -/
theorem wedgeMinorSelector_iff_exists_strictTriple {size : ℕ} :
    WedgeMinorSelector size
      ↔ ∀ design : WeightedDesign size 3, ∃ selected : Finset (Fin size), selected.card = 3
          ∧ (subsetSum design selected - 1).PosDef := by
  constructor
  · intro hselector design
    obtain ⟨unitNormal, hunit, selected, hcard, hsurplus, hminor, probeVec, hperp, hprobeNe,
      hpos⟩ := hselector design
    exact ⟨selected, hcard, posDef_of_surplus_and_wedgeMinor design selected hunit hperp hprobeNe
      hsurplus hpos hminor⟩
  · intro hstrict design
    obtain ⟨selected, hcard, hposDef⟩ := hstrict design
    obtain ⟨hsurplus, hminor, probeData⟩ :=
      (posDef_iff_surplus_and_wedgeMinor design selected dotProduct_self_firstAxis).mp hposDef
    exact ⟨![1, 0, 0], dotProduct_self_firstAxis, selected, hcard, hsurplus, hminor, probeData⟩

/-- The flat-split selector of the one-line class, from the wedge minor. -/
theorem lineFlatSplitSelectorAt_of_wedgeMinor (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    (hsurplus : 1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
    (hminor : 0 < wedgeMinor design selected unitNormal)
    {baseProbe : Fin 3 → ℝ} (hbasePerp : baseProbe ⬝ᵥ unitNormal = 0) (hbaseNe : baseProbe ≠ 0)
    (hbasePos : 0 < wedgeBalanceValue design selected unitNormal baseProbe) :
    LineFlatSplitSelectorAt design unitNormal :=
  lineFlatSplitSelectorAt_of_exists_posDef_cardThree design hunit hlineFlat
    ⟨selected, hcard, posDef_of_surplus_and_wedgeMinor design selected hunit hbasePerp hbaseNe
      hsurplus hbasePos hminor⟩

/-- **BOTH LINE OBLIGATIONS FROM ONE MINOR CONDITION.**  A design-level choice of
a card-three subset with a positive surplus, a positive wedge minor and one
positive probe reading retires the one-line residual and the two-meeting-lines
residual at the same time. -/
theorem oneLine_and_twoMeetingLines_of_wedgeMinorSelector
    (hselector : ∀ design : WeightedDesign 6 3, ∀ unitNormal : Fin 3 → ℝ,
      unitNormal ⬝ᵥ unitNormal = 1 →
      (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        design.atom lineLabel ⬝ᵥ unitNormal = 0) →
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
        ∧ 0 < wedgeMinor design selected unitNormal
        ∧ ∃ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 ∧ probeVec ≠ 0
            ∧ 0 < wedgeBalanceValue design selected unitNormal probeVec) :
    OneLineTenthHeavyJointBlindLineSparse
      ∧ TwoMeetingLinesTenthHeavyJointBlindTransversal := by
  refine oneLine_and_twoMeetingLines_of_lineFlatSplitSelector ?_
  intro design unitNormal hunit hlineFlat hheavy hcapBlind hweak
  obtain ⟨selected, hcard, hsurplus, hminor, probeVec, hperp, hprobeNe, hpos⟩ :=
    hselector design unitNormal hunit hlineFlat hheavy hcapBlind hweak
  exact lineFlatSplitSelectorAt_of_wedgeMinor design hunit hlineFlat hcard hsurplus hminor hperp
    hprobeNe hpos

/-! ## 14.  The one-line lane, with the surplus discharged

Section 5 supplies a sharp label whose height square is more than one, so every
selection through it has a positive normal surplus.  Section 12 factors the wedge
minor through that same surplus.  Together they leave ONE polynomial inequality
and one probe sign. -/

/-- The REDUCED quantity of a flat split: the second factor of the wedge minor. -/
noncomputable def flatSplitReduced {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) (sharpOne sharpTwo sharpThree : Fin size)
    (normalVec : Fin 3 → ℝ) : ℝ :=
  ((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
      * planeFormMinor flatSet (leadMeasure design selected) design.atom normalVec
    + planeFormCrossMinor flatSet Finset.univ (leadMeasure design selected)
        (sharpPairMeasure design selected sharpOne sharpTwo sharpThree) design.atom
        (sharpPairDirection design normalVec sharpOne sharpTwo sharpThree) normalVec
    + splitMeasure design selected sharpOne * splitMeasure design selected sharpTwo
        * splitMeasure design selected sharpThree
        * atomBracket design sharpOne sharpTwo sharpThree ^ 2

theorem wedgeMinor_eq_surplus_mul_flatSplitReduced {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) {sharpOne sharpTwo sharpThree : Fin size}
    (hOneTwo : sharpOne ≠ sharpTwo) (hOneThree : sharpOne ≠ sharpThree)
    (hTwoThree : sharpTwo ≠ sharpThree)
    (hsharp : flatSetᶜ = {sharpOne, sharpTwo, sharpThree}) (normalVec : Fin 3 → ℝ)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    wedgeMinor design selected normalVec
      = ((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
        * flatSplitReduced design selected flatSet sharpOne sharpTwo sharpThree normalVec :=
  wedgeMinor_eq_surplus_mul_reduced design selected flatSet hOneTwo hOneThree hTwoThree hsharp
    normalVec hunit hflat

/-- **THE MINOR TEST IS THE REDUCED TEST, ONCE THE SURPLUS IS POSITIVE.** -/
theorem wedgeMinor_pos_iff_flatSplitReduced_pos {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) {sharpOne sharpTwo sharpThree : Fin size}
    (hOneTwo : sharpOne ≠ sharpTwo) (hOneThree : sharpOne ≠ sharpThree)
    (hTwoThree : sharpTwo ≠ sharpThree)
    (hsharp : flatSetᶜ = {sharpOne, sharpTwo, sharpThree}) (normalVec : Fin 3 → ℝ)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0)
    (hsurplus : 1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) :
    0 < wedgeMinor design selected normalVec
      ↔ 0 < flatSplitReduced design selected flatSet sharpOne sharpTwo sharpThree normalVec := by
  rw [wedgeMinor_eq_surplus_mul_flatSplitReduced design selected flatSet hOneTwo hOneThree
    hTwoThree hsharp normalVec hunit hflat, hunit]
  have hpos : 0 < (∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - 1 := by linarith
  constructor
  · intro hproduct
    nlinarith [hproduct, hpos]
  · intro hreduced
    exact mul_pos hpos hreduced

/-- The line of the one-line class has the free triple as its complement. -/
theorem oneLine_flat_compl : ({0, 1, 2} : Finset (Fin 6))ᶜ = ({3, 4, 5} : Finset (Fin 6)) := by
  decide

/-- **THE ONE-LINE RESIDUAL, WITH THE SURPLUS DISCHARGED.**  At every one-line
design and its own line normal there is a FREE label whose presence alone
supplies the normal surplus.  Every card-three selection through it then needs
only the reduced inequality and one positive probe reading, and either line
obligation follows. -/
theorem exists_tallFree_lineFlatSplitSelector_producer (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0) :
    ∃ tallLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      ∀ selected : Finset (Fin 6), selected.card = 3 → tallLabel ∈ selected →
        0 < flatSplitReduced design selected ({0, 1, 2} : Finset (Fin 6)) 3 4 5 unitNormal →
        (∃ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 ∧ probeVec ≠ 0
            ∧ 0 < wedgeBalanceValue design selected unitNormal probeVec) →
        LineFlatSplitSelectorAt design unitNormal := by
  classical
  have hflatNonempty : ({0, 1, 2} : Finset (Fin 6)).Nonempty := ⟨0, by decide⟩
  have hsharpNonempty : ({0, 1, 2} : Finset (Fin 6))ᶜ.Nonempty := ⟨3, by decide⟩
  obtain ⟨tallLabel, hmem, hfloor⟩ := exists_sharp_selection_surplus_pos design unitNormal hunit
    hlineFlat hflatNonempty hsharpNonempty
  refine ⟨tallLabel, by rw [← oneLine_flat_compl]; exact hmem, ?_⟩
  intro selected hcard htall hreduced ⟨probeVec, hperp, hprobeNe, hpos⟩
  have hsurplus : 1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2 :=
    hfloor selected htall
  have hminor : 0 < wedgeMinor design selected unitNormal :=
    (wedgeMinor_pos_iff_flatSplitReduced_pos design selected ({0, 1, 2} : Finset (Fin 6))
      (by decide) (by decide) (by decide) oneLine_flat_compl unitNormal hunit hlineFlat
      hsurplus).mpr hreduced
  exact lineFlatSplitSelectorAt_of_wedgeMinor design hunit hlineFlat hcard hsurplus hminor hperp
    hprobeNe hpos

end Gtz
