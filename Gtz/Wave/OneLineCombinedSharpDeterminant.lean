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
* `Gtz.exists_mixedProbe_sharpBalanceValue_nonpos` — a sign criterion that replaces
  the landed pair-wedge refutation.  A negative sharp determinant supplies an
  explicit in-plane probe where the sharp balance is not positive.
* `Gtz.flatSplit_determinant` — the factorization of the combined determinant.
* `Gtz.exists_sharp_selection_surplus_pos` — the SURPLUS FLOOR.  Every design
  with a nonempty flat set carries a sharp label whose height square is more than
  one, so every selection through that label has a positive normal surplus.
* `Gtz.flatSplitMinor_determinant` — the INTRINSIC form.  The whole determinant
  is one number times the square of the plane bracket of the two probes, so the
  test does not depend on which probe pair reads it.
* `Gtz.lineFlatSplitSelectorAt_of_combinedMinor_pos` — a producer of the target
  selector from one probe value and one number.

## Rank

Sections 1 thru 4 and section 6 consume rank three, because `Gtz.tripleBracket`
and `Gtz.crossProduct` live there.  Section 5 is rank generic.
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
    simp only [sharpPairDirection, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_fin_one] <;>
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
