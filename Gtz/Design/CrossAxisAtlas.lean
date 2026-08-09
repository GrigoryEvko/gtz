import Gtz.Design.LiftCriterion
import Gtz.Design.OneDeterminantReduction
import Gtz.Design.RhoNormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The cross-axis atlas, and the identification of the cross-axis lane

`Gtz.posDef_tripleGap_iff_pos_liftMargin` is an equivalence at a UNIT normal,
GUARDED by two positivity hypotheses on the pair.  Supplying a normal and
discharging the guards has so far been done by hand, one stratum at a time, and
the coverage lemma `Gtz.exists_pos_liftMargin_of_posDef_tripleGap` produces only
an unnamed normal and carries an undischarged `atom ≠ 0` side hypothesis.

This file supplies the CANONICAL normal, discharges both guards from data the
tree already computes, and then determines exactly how much the criterion says
there.

THE NORMAL.  A pair's own CROSS AXIS `Gtz.crossAxis` is the direction both its
atoms are orthogonal to.  `Gtz.crossAxis_ne_zero_of_isLivePair` says it is a
genuine direction at a live pair, so it normalises: `Gtz.unitCrossAxis`.

THE GUARDS ARE FREE.  At the cross axis both readings of the pair vanish, so the
pair's shadow Gram IS its Gram.  The corner guard becomes
`0 < leverageOf a - 1` and the determinant guard becomes
`0 < pairGapExcessOf`.  Those two, with the second corner, are LITERALLY the
three conjuncts of `Gtz.IsLivePair`.  Nothing has to be proved about the normal:
the criterion's hypotheses at a cross axis are exactly liveness of the pair, and
`Gtz.isLivePair_of_posDef_tripleGapMatrix` already supplies liveness from strict
domination.  So the atlas is unconditional -- no unit hypothesis to produce, no
guard to check, no nonzero-atom side condition.

THE CLOSED FORM, AND WHAT IT COSTS.  Evaluating the criterion at the cross axis
collapses completely:

  `liftMargin D (unitCrossAxis D i j) i j x
      = pairGapExcessOf D i j * det (tripleGapMatrix D i j x)`.

Two square roots enter through the normalisation and both cancel, because the
third reading appears only through its square and `Gtz.crossAxisBudget` times
that square is the squared bracket.  The proof needs one new coordinate identity
-- the Gram determinant of three vectors in three-space is the squared bracket,
`Gtz.tripleBracket_sq_eq_gramCombination` -- and after that it is scalar algebra.

The closed form is simultaneously the atlas and its BARRIER.  The gap
determinant IS the tie leg (`Gtz.det_tripleGapMatrix`), so the closed form reads

  `liftMargin D (unitCrossAxis D i j) i j x
      = pairGapExcessOf D i j * discriminantTie D i j x`,

and `pairGapExcessOf` is positive at a live pair.  So the sign of the lift
margin at a cross axis is the sign of the tie leg and nothing else, and
`Gtz.hasLivePairPositiveTie_iff_exists_crossAxisWitness` says the cross-axis
atlas and `Gtz.HasLivePairPositiveTie` are literally the same predicate.

That is the honest accounting.  The one-determinant reduction already states
that the whole content of a "there exists a strictly dominating triple"
obligation is the sign of one tie leg at one completing label.  The lift
criterion, evaluated at the canonical normal of the atlas that sees EVERY strict
triple, reproduces exactly that sign times a positive factor.  It is therefore
not new leverage on this conclusion shape but the landed reduction in different
coordinates -- the mechanized form of the measured observation that the
criterion is an exact reformulation of positive definiteness rather than a
relaxation, and a reason NOT to spend a wave on cross-axis enumeration.

What the atlas does buy is the elimination of the normal quantifier:
`Gtz.exists_posDef_cardThree_iff_exists_crossAxisWitness` turns "some card-three
subset dominates strictly" into a finite search over ordered label triples with
no direction quantifier anywhere, and
`Gtz.exists_posDef_cardThree_of_crossAxisWitness` is the plug a stratum argument
calls once it has produced a live pair and a positive margin.

CALIBRATION.  The regular tetrahedron is a tie and every one of its pairs is
live, so a sharp criterion must sit exactly on its boundary.  It does:
`Gtz.tetraDesign_liftMargin_unitCrossAxis_eq_zero` is an exact zero at every
cross axis, and non-domination follows from the closed form alone.
-/

namespace Gtz

variable {size : ℕ}

/-! ## Part 1: the unit cross axis

`Gtz.crossAxis` is `Gtz.bracketNormal` of the two atoms and its squared length is
`Gtz.crossAxisBudget`, which exceeds one at a live pair.  So the axis normalises,
and the normalised axis reads every atom through the bracket. -/

/-- The **unit cross axis** of an ordered pair: the pair's cross axis scaled to
unit length.  The scaling is by the inverse square root of the axis budget, which
is positive at a live pair (`Gtz.pos_crossAxisBudget_of_isLivePair`). -/
noncomputable def unitCrossAxis (design : WeightedDesign size 3)
    (pairFirst pairSecond : Fin size) : Fin 3 → ℝ :=
  (Real.sqrt (crossAxisBudget design pairFirst pairSecond))⁻¹
    • crossAxis design pairFirst pairSecond

/-- A live pair has strictly positive axis budget. -/
theorem pos_crossAxisBudget_of_isLivePair (design : WeightedDesign size 3)
    {pairFirst pairSecond : Fin size} (hlive : IsLivePair design pairFirst pairSecond) :
    0 < crossAxisBudget design pairFirst pairSecond := by
  linarith [one_lt_crossAxisBudget_of_isLivePair design hlive]

/-- The square root of a positive axis budget squares back to it. -/
theorem sq_sqrt_crossAxisBudget_of_isLivePair (design : WeightedDesign size 3)
    {pairFirst pairSecond : Fin size} (hlive : IsLivePair design pairFirst pairSecond) :
    Real.sqrt (crossAxisBudget design pairFirst pairSecond) ^ 2
      = crossAxisBudget design pairFirst pairSecond := by
  rw [pow_two, Real.mul_self_sqrt (pos_crossAxisBudget_of_isLivePair design hlive).le]

/-- **The unit cross axis is a unit vector**, so it is a legal input to the lift
criterion. -/
theorem unitCrossAxis_dotProduct_self (design : WeightedDesign size 3)
    {pairFirst pairSecond : Fin size} (hlive : IsLivePair design pairFirst pairSecond) :
    unitCrossAxis design pairFirst pairSecond ⬝ᵥ unitCrossAxis design pairFirst pairSecond
      = 1 := by
  have hbudgetPos := pos_crossAxisBudget_of_isLivePair design hlive
  rw [unitCrossAxis, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    crossAxis_dotProduct_self, ← mul_assoc, ← mul_inv,
    Real.mul_self_sqrt hbudgetPos.le]
  exact inv_mul_cancel₀ hbudgetPos.ne'

/-- **Every reading at the unit cross axis is a scaled bracket.** -/
theorem normalReading_unitCrossAxis (design : WeightedDesign size 3)
    (pairFirst pairSecond probeLabel : Fin size) :
    normalReading design (unitCrossAxis design pairFirst pairSecond) probeLabel
      = (Real.sqrt (crossAxisBudget design pairFirst pairSecond))⁻¹
        * atomBracket design pairFirst pairSecond probeLabel := by
  rw [normalReading, unitCrossAxis, dotProduct_smul, smul_eq_mul, atom_dotProduct_crossAxis]

/-- The pair's FIRST atom is flat against the unit cross axis. -/
theorem normalReading_unitCrossAxis_pairFirst (design : WeightedDesign size 3)
    (pairFirst pairSecond : Fin size) :
    normalReading design (unitCrossAxis design pairFirst pairSecond) pairFirst = 0 := by
  rw [normalReading_unitCrossAxis, atomBracket_self_left, mul_zero]

/-- The pair's SECOND atom is flat against the unit cross axis. -/
theorem normalReading_unitCrossAxis_pairSecond (design : WeightedDesign size 3)
    (pairFirst pairSecond : Fin size) :
    normalReading design (unitCrossAxis design pairFirst pairSecond) pairSecond = 0 := by
  rw [normalReading_unitCrossAxis, atomBracket_self_right, mul_zero]

/-- **THE SQUARE ROOT CANCELS.**  The axis budget times the squared reading of any
atom at the unit cross axis is the squared bracket -- a polynomial identity in the
design data, with no radical left in it.  This is the single fact that makes the
closed form of Part 3 denominator free. -/
theorem crossAxisBudget_mul_normalReading_unitCrossAxis_sq (design : WeightedDesign size 3)
    {pairFirst pairSecond : Fin size} (hlive : IsLivePair design pairFirst pairSecond)
    (probeLabel : Fin size) :
    crossAxisBudget design pairFirst pairSecond
        * normalReading design (unitCrossAxis design pairFirst pairSecond) probeLabel ^ 2
      = atomBracket design pairFirst pairSecond probeLabel ^ 2 := by
  have hbudgetPos := pos_crossAxisBudget_of_isLivePair design hlive
  rw [normalReading_unitCrossAxis, mul_pow, inv_pow,
    sq_sqrt_crossAxisBudget_of_isLivePair design hlive, ← mul_assoc,
    mul_inv_cancel₀ hbudgetPos.ne', one_mul]

/-! ## Part 2: the shadow scalars at the cross axis are Gram scalars

Both readings of the pair vanish, so every shadow pairing the criterion consumes
degenerates to a Gram entry -- except the third atom's self pairing, which keeps
exactly one squared reading. -/

/-- The shadow self pairing at ANY normal is the leverage minus the squared
reading. -/
theorem shadowPairing_self_eq_leverageOf_sub_normalReading_sq
    (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ) (label : Fin size) :
    shadowPairing design normalVec label label
      = leverageOf (design.atom label) - normalReading design normalVec label ^ 2 := by
  rw [shadowPairing, dotProduct_self_eq_leverageOf, pow_two]

/-- At the unit cross axis the FIRST atom's shadow corner is its leverage. -/
theorem shadowPairing_unitCrossAxis_pairFirst_self (design : WeightedDesign size 3)
    (pairFirst pairSecond : Fin size) :
    shadowPairing design (unitCrossAxis design pairFirst pairSecond) pairFirst pairFirst
      = leverageOf (design.atom pairFirst) :=
  shadowPairing_self_eq_leverageOf_of_normalReading_eq_zero design _ pairFirst
    (normalReading_unitCrossAxis_pairFirst design pairFirst pairSecond)

/-- At the unit cross axis the SECOND atom's shadow corner is its leverage. -/
theorem shadowPairing_unitCrossAxis_pairSecond_self (design : WeightedDesign size 3)
    (pairFirst pairSecond : Fin size) :
    shadowPairing design (unitCrossAxis design pairFirst pairSecond) pairSecond pairSecond
      = leverageOf (design.atom pairSecond) :=
  shadowPairing_self_eq_leverageOf_of_normalReading_eq_zero design _ pairSecond
    (normalReading_unitCrossAxis_pairSecond design pairFirst pairSecond)

/-- A shadow pairing whose LEFT slot is the flat first atom is the atom
pairing. -/
theorem shadowPairing_unitCrossAxis_pairFirst_probe (design : WeightedDesign size 3)
    (pairFirst pairSecond probeLabel : Fin size) :
    shadowPairing design (unitCrossAxis design pairFirst pairSecond) pairFirst probeLabel
      = atomPairing design pairFirst probeLabel := by
  rw [shadowPairing, normalReading_unitCrossAxis_pairFirst, zero_mul, sub_zero, atomPairing]

/-- A shadow pairing whose LEFT slot is the flat second atom is the atom
pairing. -/
theorem shadowPairing_unitCrossAxis_pairSecond_probe (design : WeightedDesign size 3)
    (pairFirst pairSecond probeLabel : Fin size) :
    shadowPairing design (unitCrossAxis design pairFirst pairSecond) pairSecond probeLabel
      = atomPairing design pairSecond probeLabel := by
  rw [shadowPairing, normalReading_unitCrossAxis_pairSecond, zero_mul, sub_zero, atomPairing]

/-- **THE GUARD BRIDGE.**  At its own cross axis a pair's shadow-gap determinant
IS its gap minor.  So the criterion's determinant guard is the third conjunct of
`Gtz.IsLivePair`, with no geometry left to do. -/
theorem shadowGapDeterminant_unitCrossAxis_eq_pairGapExcessOf (design : WeightedDesign size 3)
    (pairFirst pairSecond : Fin size) :
    shadowGapDeterminant design (unitCrossAxis design pairFirst pairSecond)
        pairFirst pairSecond
      = pairGapExcessOf design pairFirst pairSecond := by
  rw [shadowGapDeterminant, shadowGapDeterminantOf,
    shadowPairing_unitCrossAxis_pairFirst_self, shadowPairing_unitCrossAxis_pairSecond_self,
    shadowPairing_unitCrossAxis_pairFirst_probe, pairGapExcessOf, gapExcessOf, gapExcessOf,
    gapPairingOf, atomPairing]

/-! ## Part 3: the closed form

One coordinate identity, then scalar algebra. -/

/-- **THE GRAM DETERMINANT IS THE SQUARED BRACKET.**  For three vectors in three
space, `det (A^T A) = (det A)^2`, written out in the invariants the campaign
actually uses.  A polynomial identity in the nine coordinates; no hypothesis. -/
theorem tripleBracket_sq_eq_gramCombination (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    tripleBracket firstVec secondVec thirdVec ^ 2
      = leverageOf firstVec * leverageOf secondVec * leverageOf thirdVec
        + 2 * (firstVec ⬝ᵥ secondVec) * (firstVec ⬝ᵥ thirdVec) * (secondVec ⬝ᵥ thirdVec)
        - leverageOf firstVec * (secondVec ⬝ᵥ thirdVec) ^ 2
        - leverageOf secondVec * (firstVec ⬝ᵥ thirdVec) ^ 2
        - leverageOf thirdVec * (firstVec ⬝ᵥ secondVec) ^ 2 := by
  simp only [tripleBracket_eq, leverageOf, dotProduct, Fin.sum_univ_three]
  ring

/-- **The gap determinant, read against a distinguished pair.**  The determinant
of `Gram - 1` on a triple, split so that the pair's own minor and the third
atom's data are visible separately.  This is the shape the cross-axis evaluation
produces. -/
theorem det_tripleGapMatrix_eq_atomBracket_sq_sub (design : WeightedDesign size 3)
    (pairFirst pairSecond thirdLabel : Fin size) :
    (tripleGapMatrix design pairFirst pairSecond thirdLabel).det
      = atomBracket design pairFirst pairSecond thirdLabel ^ 2
        - pairGapExcessOf design pairFirst pairSecond
        - (leverageOf (design.atom pairFirst) + leverageOf (design.atom pairSecond) - 1)
            * leverageOf (design.atom thirdLabel)
        + atomPairing design pairFirst thirdLabel ^ 2
        + atomPairing design pairSecond thirdLabel ^ 2 := by
  rw [det_tripleGapMatrix]
  simp only [discriminantTie, heavyExcess, pairGapExcessOf, gapExcessOf, gapPairingOf,
    atomPairing, atomBracket]
  linear_combination (-1 : ℝ) * tripleBracket_sq_eq_gramCombination (design.atom pairFirst)
    (design.atom pairSecond) (design.atom thirdLabel)

/-- **THE CLOSED FORM.**  At a live pair's own unit cross axis the lift margin is
the pair's gap minor times the determinant of the triple's Gram gap.  Both square
roots introduced by the normalisation cancel; the statement is polynomial in the
design data. -/
theorem liftMargin_unitCrossAxis_eq_pairGapExcessOf_mul_det (design : WeightedDesign size 3)
    {pairFirst pairSecond : Fin size} (thirdLabel : Fin size)
    (hlive : IsLivePair design pairFirst pairSecond) :
    liftMargin design (unitCrossAxis design pairFirst pairSecond) pairFirst pairSecond thirdLabel
      = pairGapExcessOf design pairFirst pairSecond
        * (tripleGapMatrix design pairFirst pairSecond thirdLabel).det := by
  have hreading := crossAxisBudget_mul_normalReading_unitCrossAxis_sq design hlive thirdLabel
  rw [det_tripleGapMatrix_eq_atomBracket_sq_sub, liftMargin, liftMarginOf, liftReadingOf,
    liftLeverageOf, liftDemandOf, shadowGapDeterminantOf,
    shadowPairing_unitCrossAxis_pairFirst_self design pairFirst pairSecond,
    shadowPairing_unitCrossAxis_pairSecond_self design pairFirst pairSecond,
    shadowPairing_unitCrossAxis_pairFirst_probe design pairFirst pairSecond pairSecond,
    shadowPairing_unitCrossAxis_pairFirst_probe design pairFirst pairSecond thirdLabel,
    shadowPairing_unitCrossAxis_pairSecond_probe design pairFirst pairSecond thirdLabel,
    shadowPairing_self_eq_leverageOf_sub_normalReading_sq design
      (unitCrossAxis design pairFirst pairSecond) thirdLabel,
    normalReading_unitCrossAxis_pairFirst design pairFirst pairSecond,
    normalReading_unitCrossAxis_pairSecond design pairFirst pairSecond]
  simp only [crossAxisBudget, atomPairing, pairGapExcessOf, gapExcessOf, gapPairingOf]
    at hreading ⊢
  linear_combination (leverageOf (design.atom pairFirst) - 1)
      * (leverageOf (design.atom pairSecond) - 1) * hreading
    - (design.atom pairFirst ⬝ᵥ design.atom pairSecond) ^ 2 * hreading

/-! ## Part 4: the atlas -/

/-- The leading pair of a strictly dominating triple is live, read at the design
level rather than at the gap matrix. -/
theorem isLivePair_of_posDef_tripleGap (design : WeightedDesign size 3)
    {pairFirst pairSecond thirdLabel : Fin size}
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hposDef : (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef) :
    IsLivePair design pairFirst pairSecond :=
  isLivePair_of_posDef_tripleGapMatrix design pairFirst pairSecond thirdLabel
    ((posDef_subsetSum_sub_one_iff_posDef_tripleGapMatrix design hFirstSecond hFirstThird
      hSecondThird).mp hposDef)

/-- **THE CRITERION AT A CROSS AXIS, GUARD FREE.**  Liveness of the pair is the
only hypothesis: it supplies the unit normal, the corner and the determinant all
at once. -/
theorem posDef_tripleGap_iff_pos_liftMargin_unitCrossAxis (design : WeightedDesign size 3)
    {pairFirst pairSecond thirdLabel : Fin size}
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hlive : IsLivePair design pairFirst pairSecond) :
    (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef
      ↔ 0 < liftMargin design (unitCrossAxis design pairFirst pairSecond)
              pairFirst pairSecond thirdLabel := by
  obtain ⟨hfirstExcess, _, hpairExcess⟩ := hlive
  refine posDef_tripleGap_iff_pos_liftMargin design
    (unitCrossAxis_dotProduct_self design ⟨hfirstExcess, ‹_›, hpairExcess⟩)
    pairFirst pairSecond thirdLabel hFirstSecond hFirstThird hSecondThird ?_ ?_
  · rw [shadowPairing_unitCrossAxis_pairFirst_self]
    simpa only [gapExcessOf] using hfirstExcess
  · rw [shadowGapDeterminant_unitCrossAxis_eq_pairGapExcessOf]
    exact hpairExcess

/-- **THE ATLAS.**  Strict domination by an ordered triple is EXACTLY liveness of
its leading pair together with a positive lift margin at that pair's own unit
cross axis.  No direction is quantified, no unit hypothesis is required and no
guard is left over. -/
theorem posDef_tripleGap_iff_isLivePair_and_pos_liftMargin_unitCrossAxis
    (design : WeightedDesign size 3) {pairFirst pairSecond thirdLabel : Fin size}
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel) :
    (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef
      ↔ IsLivePair design pairFirst pairSecond
        ∧ 0 < liftMargin design (unitCrossAxis design pairFirst pairSecond)
                pairFirst pairSecond thirdLabel := by
  constructor
  · intro hposDef
    have hlive := isLivePair_of_posDef_tripleGap design hFirstSecond hFirstThird
      hSecondThird hposDef
    exact ⟨hlive, (posDef_tripleGap_iff_pos_liftMargin_unitCrossAxis design hFirstSecond
      hFirstThird hSecondThird hlive).mp hposDef⟩
  · rintro ⟨hlive, hmargin⟩
    exact (posDef_tripleGap_iff_pos_liftMargin_unitCrossAxis design hFirstSecond hFirstThird
      hSecondThird hlive).mpr hmargin

/-- **COMPLETENESS, CONSTRUCTIVELY.**  Every strictly dominating triple is seen by
the criterion at the cross axis of its leading pair.  This strengthens the
packaged coverage lemma in two ways: the normal is named rather than merely
asserted to exist, and the nonzero-atom side hypothesis is gone. -/
theorem pos_liftMargin_unitCrossAxis_of_posDef_tripleGap (design : WeightedDesign size 3)
    {pairFirst pairSecond thirdLabel : Fin size}
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hposDef : (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef) :
    0 < liftMargin design (unitCrossAxis design pairFirst pairSecond)
          pairFirst pairSecond thirdLabel :=
  ((posDef_tripleGap_iff_isLivePair_and_pos_liftMargin_unitCrossAxis design hFirstSecond
    hFirstThird hSecondThird).mp hposDef).2

/-- **THE PLUG.**  A live pair and a positive cross-axis margin produce a
card-three strict dominator, in the shape every stratum obligation asks for. -/
theorem exists_posDef_cardThree_of_crossAxisWitness (design : WeightedDesign size 3)
    {pairFirst pairSecond thirdLabel : Fin size}
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hlive : IsLivePair design pairFirst pairSecond)
    (hmargin : 0 < liftMargin design (unitCrossAxis design pairFirst pairSecond)
                pairFirst pairSecond thirdLabel) :
    ∃ selected : Finset (Fin size), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef :=
  ⟨{pairFirst, pairSecond, thirdLabel},
    card_labelTriple_eq_three hFirstSecond hFirstThird hSecondThird,
    (posDef_tripleGap_iff_isLivePair_and_pos_liftMargin_unitCrossAxis design hFirstSecond
      hFirstThird hSecondThird).mpr ⟨hlive, hmargin⟩⟩

/-- **THE NORMAL QUANTIFIER IS ELIMINATED.**  Existence of a strictly dominating
card-three subset is equivalent to a finite search over ordered label triples,
with no direction appearing anywhere in the right-hand side. -/
theorem exists_posDef_cardThree_iff_exists_crossAxisWitness (design : WeightedDesign size 3) :
    (∃ selected : Finset (Fin size), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef)
      ↔ ∃ pairFirst pairSecond thirdLabel : Fin size,
          pairFirst ≠ pairSecond ∧ pairFirst ≠ thirdLabel ∧ pairSecond ≠ thirdLabel
            ∧ IsLivePair design pairFirst pairSecond
            ∧ 0 < liftMargin design (unitCrossAxis design pairFirst pairSecond)
                    pairFirst pairSecond thirdLabel := by
  constructor
  · rintro ⟨selected, hcard, hposDef⟩
    obtain ⟨firstLabel, secondLabel, thirdLabel, hFirstSecond, hFirstThird, hSecondThird,
      hselected⟩ := Finset.card_eq_three.mp hcard
    subst hselected
    exact ⟨firstLabel, secondLabel, thirdLabel, hFirstSecond, hFirstThird, hSecondThird,
      isLivePair_of_posDef_tripleGap design hFirstSecond hFirstThird hSecondThird hposDef,
      pos_liftMargin_unitCrossAxis_of_posDef_tripleGap design hFirstSecond hFirstThird
        hSecondThird hposDef⟩
  · rintro ⟨pairFirst, pairSecond, thirdLabel, hFirstSecond, hFirstThird, hSecondThird,
      hlive, hmargin⟩
    exact exists_posDef_cardThree_of_crossAxisWitness design hFirstSecond hFirstThird
      hSecondThird hlive hmargin

/-! ## Part 5: the barrier

The atlas is complete, and the closed form says exactly what it costs. -/

/-- **THE CROSS-AXIS LANE IS THE DETERMINANT LANE.**  At a live pair the sign of
the lift margin at the cross axis is the sign of the gap determinant and nothing
else.  Together with completeness this says the cross-axis atlas, though it sees
every strict triple, carries no information beyond the one determinant the landed
reduction already isolates -- so enumerating cross axes is not a route past the
frontier. -/
theorem pos_liftMargin_unitCrossAxis_iff_pos_det (design : WeightedDesign size 3)
    {pairFirst pairSecond : Fin size} (thirdLabel : Fin size)
    (hlive : IsLivePair design pairFirst pairSecond) :
    0 < liftMargin design (unitCrossAxis design pairFirst pairSecond)
          pairFirst pairSecond thirdLabel
      ↔ 0 < (tripleGapMatrix design pairFirst pairSecond thirdLabel).det := by
  rw [liftMargin_unitCrossAxis_eq_pairGapExcessOf_mul_det design thirdLabel hlive]
  constructor
  · intro hmargin
    by_contra hdetNonpos
    exact absurd hmargin (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hlive.2.2.le
      (not_lt.mp hdetNonpos)))
  · exact mul_pos hlive.2.2

/-- **THE CLOSED FORM IN THE TREE'S OWN TIE VOCABULARY.**  The gap determinant is
the tie leg, so the cross-axis lift margin is the pair's gap minor times the tie
leg of the completing label. -/
theorem liftMargin_unitCrossAxis_eq_pairGapExcessOf_mul_discriminantTie
    (design : WeightedDesign size 3) {pairFirst pairSecond : Fin size} (thirdLabel : Fin size)
    (hlive : IsLivePair design pairFirst pairSecond) :
    liftMargin design (unitCrossAxis design pairFirst pairSecond) pairFirst pairSecond thirdLabel
      = pairGapExcessOf design pairFirst pairSecond
        * discriminantTie design pairFirst pairSecond thirdLabel := by
  rw [liftMargin_unitCrossAxis_eq_pairGapExcessOf_mul_det design thirdLabel hlive,
    det_tripleGapMatrix]

/-- **THE BARRIER, STATED AGAINST THE LANDED REDUCTION.**  The cross-axis atlas
and `Gtz.HasLivePairPositiveTie` are the SAME predicate.  The one-determinant
reduction already says the whole content of a "there exists a strictly
dominating triple" obligation is the sign of one tie leg at one completing
label; this says the lift criterion, evaluated at the canonical normal of the
complete atlas, reproduces that sign and multiplies it by a positive factor.
The new tool is therefore not new leverage on this conclusion shape -- it is the
landed reduction in different coordinates. -/
theorem hasLivePairPositiveTie_iff_exists_crossAxisWitness (design : WeightedDesign size 3) :
    HasLivePairPositiveTie design
      ↔ ∃ pairFirst pairSecond thirdLabel : Fin size,
          pairFirst ≠ pairSecond ∧ pairFirst ≠ thirdLabel ∧ pairSecond ≠ thirdLabel
            ∧ IsLivePair design pairFirst pairSecond
            ∧ 0 < liftMargin design (unitCrossAxis design pairFirst pairSecond)
                    pairFirst pairSecond thirdLabel :=
  (hasLivePairPositiveTie_iff_exists_posDef_cardThree design).trans
    (exists_posDef_cardThree_iff_exists_crossAxisWitness design)

/-- **The margin vanishes exactly when the gap determinant does.**  A tie is
therefore pinned to the criterion's boundary at every cross axis of every live
pair, which is the sharpness the tetrahedron exhibits below. -/
theorem liftMargin_unitCrossAxis_eq_zero_iff_det_eq_zero (design : WeightedDesign size 3)
    {pairFirst pairSecond : Fin size} (thirdLabel : Fin size)
    (hlive : IsLivePair design pairFirst pairSecond) :
    liftMargin design (unitCrossAxis design pairFirst pairSecond)
        pairFirst pairSecond thirdLabel = 0
      ↔ (tripleGapMatrix design pairFirst pairSecond thirdLabel).det = 0 := by
  rw [liftMargin_unitCrossAxis_eq_pairGapExcessOf_mul_det design thirdLabel hlive,
    mul_eq_zero]
  exact ⟨fun hzero => hzero.resolve_left hlive.2.2.ne', fun hzero => Or.inr hzero⟩

/-! ## Part 6: calibration at the tetrahedron

The regular tetrahedron is a genuine tie, so a sharp criterion must report
exactly zero on it.  It does, at every cross axis. -/

/-- The tetrahedron's gap determinant vanishes on every triple. -/
theorem tetraDesign_det_tripleGapMatrix_eq_zero {pairFirst pairSecond thirdLabel : Fin 4}
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel) :
    (tripleGapMatrix tetraDesign pairFirst pairSecond thirdLabel).det = 0 := by
  rw [det_tripleGapMatrix, discriminantTie,
    tetraDesign_atomPairing_of_distinct hFirstSecond,
    tetraDesign_atomPairing_of_distinct hFirstThird,
    tetraDesign_atomPairing_of_distinct hSecondThird]
  simp only [tetraDesign_heavyExcess]
  norm_num

/-- **SHARPNESS.**  The tetrahedron's lift margin is EXACTLY zero at every cross
axis of every pair -- the tie sits precisely on the criterion's boundary. -/
theorem tetraDesign_liftMargin_unitCrossAxis_eq_zero {pairFirst pairSecond thirdLabel : Fin 4}
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel) :
    liftMargin tetraDesign (unitCrossAxis tetraDesign pairFirst pairSecond)
        pairFirst pairSecond thirdLabel = 0 :=
  (liftMargin_unitCrossAxis_eq_zero_iff_det_eq_zero tetraDesign thirdLabel
    (tetraDesign_isLivePair hFirstSecond)).mpr
    (tetraDesign_det_tripleGapMatrix_eq_zero hFirstSecond hFirstThird hSecondThird)

/-- Non-domination at the tetrahedron, rederived through the atlas alone. -/
theorem tetraDesign_not_posDef_tripleGap_via_crossAxis
    {pairFirst pairSecond thirdLabel : Fin 4}
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel) :
    ¬ (subsetSum tetraDesign {pairFirst, pairSecond, thirdLabel} - 1).PosDef := by
  intro hposDef
  have hmargin := pos_liftMargin_unitCrossAxis_of_posDef_tripleGap tetraDesign hFirstSecond
    hFirstThird hSecondThird hposDef
  rw [tetraDesign_liftMargin_unitCrossAxis_eq_zero hFirstSecond hFirstThird hSecondThird]
    at hmargin
  exact lt_irrefl 0 hmargin

end Gtz
