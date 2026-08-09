import Gtz.Design.LiftCriterion
import Gtz.Design.ChartlessKill
import Gtz.Design.OneLineCanonicalTripleRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-
# The one-line class, read through the lift criterion at a flat pair

`Gtz.posDef_tripleGap_iff_pos_liftMargin` is an equivalence GUARDED by two
hypotheses on the pair -- its shadow corner and its shadow-gap determinant must
be positive.  This file removes the guard in the one configuration where the
geometry supplies it for free, and then reads the consequences on the one-line
stratum.

THE FLAT-PAIR DISCHARGE.  If BOTH members of the pair have vanishing normal
reading -- equivalently the normal is a normal of their span, the pair's CROSS
AXIS -- then the shadow Gram of the pair IS its Gram, so the pair's shadow gap IS
its `Gram - 1` block, and a strictly dominating triple through the pair forces
that block positive definite by `Gtz.isLivePair_of_posDef_tripleGapMatrix`.  So
at a cross axis the criterion needs NO hypothesis, and
`Gtz.posDef_tripleGap_iff_flatPairFires` is an unguarded scalar characterisation
of strict domination.

THE ENGINE IDENTIFICATION.  Read the landed averaging law
`Gtz.sum_weight_mul_liftMargin_eq_neg` at a flat pair and subtract the two terms
the pair contributes to itself.  What is left over the COMPLEMENT is exactly the
shadow-gap determinant times the pair-cap excess of `Gtz.IsCapBlindSpot`.  The
pair-cap engine and the lift criterion's complement average are therefore the
same test, and on the cap blind spot the lift criterion's own averaging provably
produces nothing.  That is the barrier, named:
`Gtz.sum_offPair_weight_mul_liftMargin_nonpos_of_capBlindSpot`.

THE ONE-LINE READING.  The line normal of `[[0,1,2]]` is flat against all three
line atoms, so every LINE PAIR sits at its own cross axis there.  Consequence
(`Gtz.oneLine_not_posDef_linePairTriple_of_linePairBlindSpot`): if no line pair
has positive shadow-gap determinant, then NO strictly dominating triple contains
two line atoms -- the residual is cut out combinatorially, by the signs of three
explicit `Gram - 1` minors, not by a metric degeneracy.  Two further one-line
facts come free from the stratum: weighted Parseval at the line normal is carried
entirely by the free atoms, so one of them reads the normal above one in square
(`Gtz.oneLine_exists_freeAtom_one_lt_normalReading_sq`), and that inequality is
exactly what a flat-pair winner NEEDS
(`Gtz.one_lt_normalReading_sq_of_posDef_tripleGap_of_flatPair`).

On `Gtz.oneLineFailureDesign` all nine ordered line pairs have nonpositive
shadow-gap determinant -- `{0,1}` exactly at zero, the two pairs through atom `2`
at `-4` -- so no winner of that fixture meets the line twice, matching its landed
strict dominators `{2,3,5}` and `{2,4,5}`.  Its MIXED pair `{2,5}` fires with lift
margin exactly `14`, which rederives `Gtz.oneLineFailure_mixedTripleGap_posDef`.

WHAT IS NOT CLOSED.  `Skeleton.obligationHeavyWeakToStrictOneLine` is NOT
discharged.  `Gtz.patternHeavyWeakToStrict_oneLine_of_lineNormalBlindSpot`
reduces it to designs that are simultaneously cap blind and line-normal blind;
that joint residual is nonempty, so no axiom is retired here.
-/

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## Part 1: at a flat label the shadow Gram is the Gram -/

/-- A vanishing normal reading on EITHER side collapses the shadow pairing to the
plain atom pairing. -/
theorem shadowPairing_eq_atomPairing_of_normalReading_eq_zero
    (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (leftLabel rightLabel : Fin size)
    (hflat : normalReading design normalVec leftLabel = 0) :
    shadowPairing design normalVec leftLabel rightLabel
      = design.atom leftLabel ⬝ᵥ design.atom rightLabel := by
  simp only [shadowPairing, hflat, zero_mul, sub_zero]

/-- At a normal both pair members are orthogonal to, the pair's shadow-gap
determinant IS its pair gap excess -- the `Gram - 1` two-by-two minor.  This is
the bridge between the criterion's shadow vocabulary and the Gram vocabulary the
rest of the tree speaks. -/
theorem shadowGapDeterminant_eq_pairGapExcessOf_of_flatPair
    (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond : Fin size)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0) :
    shadowGapDeterminant design normalVec pairFirst pairSecond
      = pairGapExcessOf design pairFirst pairSecond := by
  rw [shadowGapDeterminant, shadowGapDeterminantOf,
    shadowPairing_self_eq_leverageOf_of_normalReading_eq_zero design normalVec pairFirst
      hFirstFlat,
    shadowPairing_self_eq_leverageOf_of_normalReading_eq_zero design normalVec pairSecond
      hSecondFlat,
    shadowPairing_eq_atomPairing_of_normalReading_eq_zero design normalVec pairFirst
      pairSecond hFirstFlat]
  simp only [pairGapExcessOf, gapExcessOf, gapPairingOf]

/-! ## Part 2: the cross-axis discharge -/

/-- **THE FLAT-PAIR DISCHARGE.**  A strictly dominating triple whose first two
members are orthogonal to the normal forces BOTH guards of the lift criterion --
the pair's shadow corner and its shadow-gap determinant -- with no further
hypothesis, not even that the normal is a unit vector.  Every pair is flat at its
own cross axis, so the criterion has an unguarded reading at fifteen named
directions of a six-atom design. -/
theorem shadowGap_pos_of_posDef_tripleGap_of_flatPair
    (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond thirdLabel : Fin size)
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0)
    (hposDef : (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef) :
    0 < shadowPairing design normalVec pairFirst pairFirst - 1
      ∧ 0 < shadowPairing design normalVec pairSecond pairSecond - 1
      ∧ 0 < shadowGapDeterminant design normalVec pairFirst pairSecond := by
  have hgramPosDef : (tripleGapMatrix design pairFirst pairSecond thirdLabel).PosDef :=
    (posDef_subsetSum_sub_one_iff_posDef_tripleGapMatrix design hFirstSecond hFirstThird
      hSecondThird).mp hposDef
  obtain ⟨hexcessFirst, hexcessSecond, hpairExcess⟩ :=
    isLivePair_of_posDef_tripleGapMatrix design pairFirst pairSecond thirdLabel hgramPosDef
  refine ⟨?_, ?_, ?_⟩
  · rw [shadowPairing_self_eq_leverageOf_of_normalReading_eq_zero design normalVec pairFirst
      hFirstFlat]
    simpa only [gapExcessOf] using hexcessFirst
  · rw [shadowPairing_self_eq_leverageOf_of_normalReading_eq_zero design normalVec pairSecond
      hSecondFlat]
    simpa only [gapExcessOf] using hexcessSecond
  · rw [shadowGapDeterminant_eq_pairGapExcessOf_of_flatPair design normalVec pairFirst
      pairSecond hFirstFlat hSecondFlat]
    exact hpairExcess

/-- **THE UNGUARDED CRITERION AT A CROSS AXIS.**  With the pair flat against a
unit normal, strict domination by the triple is EXACTLY the conjunction of the
two guards and the collapsed scalar comparison.  No hypothesis survives on the
right-hand side that is not itself a polynomial sign in the shadow Gram, so the
criterion is a complete decision procedure along the pair's cross axis. -/
theorem posDef_tripleGap_iff_flatPairFires (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    (pairFirst pairSecond thirdLabel : Fin size)
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0) :
    (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef
      ↔ (0 < shadowPairing design normalVec pairFirst pairFirst - 1
          ∧ 0 < shadowGapDeterminant design normalVec pairFirst pairSecond
          ∧ liftLeverage design normalVec pairFirst pairSecond thirdLabel
              < normalReading design normalVec thirdLabel ^ 2
                * shadowGapDeterminant design normalVec pairFirst pairSecond) := by
  constructor
  · intro hposDef
    obtain ⟨hcorner, _, hdet⟩ := shadowGap_pos_of_posDef_tripleGap_of_flatPair design normalVec
      pairFirst pairSecond thirdLabel hFirstSecond hFirstThird hSecondThird hFirstFlat
      hSecondFlat hposDef
    exact ⟨hcorner, hdet,
      (posDef_tripleGap_iff_lineNormalCollapse design hunit pairFirst pairSecond thirdLabel
        hFirstSecond hFirstThird hSecondThird hFirstFlat hSecondFlat hcorner hdet).mp hposDef⟩
  · rintro ⟨hcorner, hdet, hcollapse⟩
    exact (posDef_tripleGap_iff_lineNormalCollapse design hunit pairFirst pairSecond thirdLabel
      hFirstSecond hFirstThird hSecondThird hFirstFlat hSecondFlat hcorner hdet).mpr hcollapse

/-! ## Part 3: the flat-pair obstruction -/

/-- **THE FLAT-PAIR OBSTRUCTION.**  A pair whose shadow-gap determinant is
nonpositive at a normal it is flat against sits in NO strictly dominating triple.
This is the sharp form of the observation that a leverage-one line atom cannot
enter a pair that strictly dominates the shadow: the corner is only half the
story, the determinant is the whole of it. -/
theorem not_posDef_tripleGap_of_flatPair_of_shadowGapDeterminant_nonpos
    (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond thirdLabel : Fin size)
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0)
    (hdetNonpos : shadowGapDeterminant design normalVec pairFirst pairSecond ≤ 0) :
    ¬ (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef := by
  intro hposDef
  obtain ⟨_, _, hdetPos⟩ := shadowGap_pos_of_posDef_tripleGap_of_flatPair design normalVec
    pairFirst pairSecond thirdLabel hFirstSecond hFirstThird hSecondThird hFirstFlat
    hSecondFlat hposDef
  exact absurd hdetPos (not_lt.mpr hdetNonpos)

/-! ## Part 4: the lift criterion's complement average IS the pair cap -/

/-- The margin the pair reads at its own FIRST member, at a normal it is flat
against: the reading vanishes and the demand is the shadow-gap determinant, so
the whole margin is minus a product. -/
theorem liftMargin_at_pairFirst_of_flatPair (design : WeightedDesign size 3)
    (normalVec : Fin 3 → ℝ) (pairFirst pairSecond : Fin size)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0) :
    liftMargin design normalVec pairFirst pairSecond pairFirst
      = -(shadowGapDeterminant design normalVec pairFirst pairSecond
          * (2 * shadowGapDeterminant design normalVec pairFirst pairSecond
            + (shadowPairing design normalVec pairSecond pairSecond - 1))) := by
  rw [liftMargin, hFirstFlat, hSecondFlat, shadowPairing_comm design normalVec pairSecond pairFirst]
  simp only [shadowGapDeterminant, liftMarginOf, liftReadingOf, liftLeverageOf, liftDemandOf,
    shadowGapDeterminantOf]
  ring

/-- The margin the pair reads at its own SECOND member. -/
theorem liftMargin_at_pairSecond_of_flatPair (design : WeightedDesign size 3)
    (normalVec : Fin 3 → ℝ) (pairFirst pairSecond : Fin size)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0) :
    liftMargin design normalVec pairFirst pairSecond pairSecond
      = -(shadowGapDeterminant design normalVec pairFirst pairSecond
          * (2 * shadowGapDeterminant design normalVec pairFirst pairSecond
            + (shadowPairing design normalVec pairFirst pairFirst - 1))) := by
  rw [liftMargin, hFirstFlat, hSecondFlat]
  simp only [shadowGapDeterminant, liftMarginOf, liftReadingOf, liftLeverageOf, liftDemandOf,
    shadowGapDeterminantOf]
  ring

/-- **THE ENGINE IDENTIFICATION.**  Take the landed averaging law
`Gtz.sum_weight_mul_liftMargin_eq_neg` at a pair the normal is flat against and
remove the two terms the pair contributes to itself.  What survives over the
COMPLEMENT is the shadow-gap determinant times exactly the quantity whose sign
`Gtz.IsCapBlindSpot` tests.  The pair-cap engine and the lift criterion's
complement average are therefore the SAME test, read in two vocabularies. -/
theorem sum_offPair_weight_mul_liftMargin_eq_capExcess (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    (pairFirst pairSecond : Fin size) (hFirstSecond : pairFirst ≠ pairSecond)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0) :
    ∑ label ∈ ({pairFirst, pairSecond} : Finset (Fin size))ᶜ,
        design.weight label * liftMargin design normalVec pairFirst pairSecond label
      = shadowGapDeterminant design normalVec pairFirst pairSecond
        * (2 * (design.weight pairFirst + design.weight pairSecond)
              * (heavyExcess design pairFirst * heavyExcess design pairSecond
                - atomPairing design pairFirst pairSecond ^ 2)
            - ((1 - design.weight pairSecond) * heavyExcess design pairFirst
              + (1 - design.weight pairFirst) * heavyExcess design pairSecond)) := by
  have hsplit : (∑ label ∈ ({pairFirst, pairSecond} : Finset (Fin size)),
        design.weight label * liftMargin design normalVec pairFirst pairSecond label)
      + ∑ label ∈ ({pairFirst, pairSecond} : Finset (Fin size))ᶜ,
          design.weight label * liftMargin design normalVec pairFirst pairSecond label
      = ∑ label, design.weight label
          * liftMargin design normalVec pairFirst pairSecond label :=
    Finset.sum_add_sum_compl _ _
  have hpairFirstValue := liftMargin_at_pairFirst_of_flatPair design normalVec pairFirst
    pairSecond hFirstFlat hSecondFlat
  have hpairSecondValue := liftMargin_at_pairSecond_of_flatPair design normalVec pairFirst
    pairSecond hFirstFlat hSecondFlat
  have htotal := sum_weight_mul_liftMargin_eq_neg design hunit pairFirst pairSecond
  rw [Finset.sum_pair hFirstSecond, hpairFirstValue, hpairSecondValue, htotal, hFirstFlat,
    hSecondFlat] at hsplit
  have hcornerFirst : shadowPairing design normalVec pairFirst pairFirst - 1
      = heavyExcess design pairFirst := by
    rw [shadowPairing_self_eq_leverageOf_of_normalReading_eq_zero design normalVec pairFirst
      hFirstFlat]
    rfl
  have hcornerSecond : shadowPairing design normalVec pairSecond pairSecond - 1
      = heavyExcess design pairSecond := by
    rw [shadowPairing_self_eq_leverageOf_of_normalReading_eq_zero design normalVec pairSecond
      hSecondFlat]
    rfl
  have hdetGram : shadowGapDeterminant design normalVec pairFirst pairSecond
      = heavyExcess design pairFirst * heavyExcess design pairSecond
        - atomPairing design pairFirst pairSecond ^ 2 := by
    rw [shadowGapDeterminant_eq_pairGapExcessOf_of_flatPair design normalVec pairFirst
      pairSecond hFirstFlat hSecondFlat]
    simp only [pairGapExcessOf, gapExcessOf_eq_heavyExcess, gapPairingOf_eq_atomPairing]
  rw [hcornerFirst, hcornerSecond, hdetGram] at hsplit
  rw [hdetGram]
  linear_combination hsplit

/-- **THE THIRD BARRIER, NAMED.**  On the cap blind spot the lift criterion's own
complement average at a flat pair is nonpositive, so averaging over the labels
outside the pair can never exhibit the completing atom.  This stands alongside
the landed pair-averaging barrier and the whole-design F7 barrier
`Gtz.sum_weight_mul_liftMargin_neg`: the lift criterion adds NOTHING to the
pair-cap engine by averaging. -/
theorem sum_offPair_weight_mul_liftMargin_nonpos_of_capBlindSpot
    (design : WeightedDesign size 3) {normalVec : Fin 3 → ℝ}
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (pairFirst pairSecond : Fin size) (hFirstSecond : pairFirst ≠ pairSecond)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0)
    (hdetNonneg : 0 ≤ shadowGapDeterminant design normalVec pairFirst pairSecond)
    (hblind : IsCapBlindSpot design) :
    ∑ label ∈ ({pairFirst, pairSecond} : Finset (Fin size))ᶜ,
        design.weight label * liftMargin design normalVec pairFirst pairSecond label ≤ 0 := by
  have hcap := hblind pairFirst pairSecond hFirstSecond
  rw [sum_offPair_weight_mul_liftMargin_eq_capExcess design hunit pairFirst pairSecond
    hFirstSecond hFirstFlat hSecondFlat]
  nlinarith [hdetNonneg, hcap]

/-- **THE PAIR-CAP ENGINE, REDERIVED THROUGH THE LIFT CRITERION.**  Positive cap
excess at a pair makes the complement average of the lift margins positive, so
some label outside the pair has a positive margin and the criterion -- unguarded
at the pair's cross axis -- delivers the strictly dominating triple.  The
conclusion duplicates the landed `Gtz.exists_posDef_triple_of_pairCapExcess`; the
point is that the two engines are ONE engine. -/
theorem exists_posDef_cardThree_of_flatPair_capExcess (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    (pairFirst pairSecond : Fin size) (hFirstSecond : pairFirst ≠ pairSecond)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0)
    (hheavy : ∀ label : Fin size, 1 ≤ leverageOf (design.atom label))
    (hcapExcess : (1 - design.weight pairSecond) * heavyExcess design pairFirst
        + (1 - design.weight pairFirst) * heavyExcess design pairSecond
      < 2 * (design.weight pairFirst + design.weight pairSecond)
          * (heavyExcess design pairFirst * heavyExcess design pairSecond
            - atomPairing design pairFirst pairSecond ^ 2)) :
    ∃ selected : Finset (Fin size), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  have hexcessFirst : 0 ≤ heavyExcess design pairFirst := by
    have hlev := hheavy pairFirst
    simp only [heavyExcess]
    linarith
  have hexcessSecond : 0 ≤ heavyExcess design pairSecond := by
    have hlev := hheavy pairSecond
    simp only [heavyExcess]
    linarith
  have hweightFirst := design.weight_pos pairFirst
  have hweightSecond := design.weight_pos pairSecond
  have hdetGram : shadowGapDeterminant design normalVec pairFirst pairSecond
      = heavyExcess design pairFirst * heavyExcess design pairSecond
        - atomPairing design pairFirst pairSecond ^ 2 := by
    rw [shadowGapDeterminant_eq_pairGapExcessOf_of_flatPair design normalVec pairFirst
      pairSecond hFirstFlat hSecondFlat]
    simp only [pairGapExcessOf, gapExcessOf_eq_heavyExcess, gapPairingOf_eq_atomPairing]
  have hsizeTwo : 2 ≤ size := by
    have hvalNe : pairFirst.val ≠ pairSecond.val := fun hval => hFirstSecond (Fin.ext hval)
    have hfirstLt := pairFirst.isLt
    have hsecondLt := pairSecond.isLt
    omega
  have hweightFirstLt := weight_lt_one design hsizeTwo pairFirst
  have hweightSecondLt := weight_lt_one design hsizeTwo pairSecond
  have hcapLeftNonneg : 0 ≤ (1 - design.weight pairSecond) * heavyExcess design pairFirst
      + (1 - design.weight pairFirst) * heavyExcess design pairSecond := by nlinarith
  have hproductPos : 0 < heavyExcess design pairFirst * heavyExcess design pairSecond
      - atomPairing design pairFirst pairSecond ^ 2 := by nlinarith
  have hdetPos : 0 < shadowGapDeterminant design normalVec pairFirst pairSecond := by
    rw [hdetGram]
    exact hproductPos
  have hcornerPos : 0 < shadowPairing design normalVec pairFirst pairFirst - 1 := by
    rw [shadowPairing_self_eq_leverageOf_of_normalReading_eq_zero design normalVec pairFirst
      hFirstFlat]
    have hexcessPos : 0 < heavyExcess design pairFirst := by nlinarith
    simpa only [heavyExcess] using hexcessPos
  have hsumPos : 0 < ∑ label ∈ ({pairFirst, pairSecond} : Finset (Fin size))ᶜ,
      design.weight label * liftMargin design normalVec pairFirst pairSecond label := by
    rw [sum_offPair_weight_mul_liftMargin_eq_capExcess design hunit pairFirst pairSecond
      hFirstSecond hFirstFlat hSecondFlat, hdetGram]
    exact mul_pos hproductPos (by linarith)
  obtain ⟨witnessLabel, hwitnessMem, hwitnessPos⟩ :=
    Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ)) (by simpa using hsumPos)
  have hwitnessWeight := design.weight_pos witnessLabel
  have hmarginPos : 0 < liftMargin design normalVec pairFirst pairSecond witnessLabel := by
    nlinarith [hwitnessPos]
  have hnotMem : witnessLabel ∉ ({pairFirst, pairSecond} : Finset (Fin size)) := by
    simpa using hwitnessMem
  have hFirstWitness : pairFirst ≠ witnessLabel := by
    intro heq
    exact hnotMem (by simp [← heq])
  have hSecondWitness : pairSecond ≠ witnessLabel := by
    intro heq
    exact hnotMem (by simp [← heq])
  exact exists_posDef_cardThree_of_pos_liftMargin design hunit pairFirst pairSecond witnessLabel
    hFirstSecond hFirstWitness hSecondWitness hcornerPos hdetPos hmarginPos

/-! ## Part 5: the one-line stratum at its line normal -/

/-- At the line normal the three line atoms have vanishing normal reading, so
every LINE PAIR sits at its own cross axis and Part 2 applies to it unguarded. -/
theorem oneLine_normalReading_eq_zero (design : WeightedDesign 6 3) (normalVec : Fin 3 → ℝ)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0)
    (lineLabel : Fin 6) (hmem : lineLabel ∈ ({0, 1, 2} : Finset (Fin 6))) :
    normalReading design normalVec lineLabel = 0 :=
  horthogonal lineLabel hmem

/-- **THE FREE-ATOM CORNER, FOR FREE.**  Weighted Parseval at a unit line normal
is carried entirely by the three free atoms, and their weights sum to STRICTLY
less than one, so SOME free atom has squared normal reading strictly above one.
Positivity of `h_x^2 - 1` is the necessary part of the collapsed criterion, and
the stratum hands it over with no hypothesis beyond the pattern. -/
theorem oneLine_exists_freeAtom_one_lt_normalReading_sq (design : WeightedDesign 6 3)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0) :
    ∃ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      1 < normalReading design normalVec freeLabel ^ 2 := by
  by_contra hcontra
  push Not at hcontra
  have hcarried := normalParseval_on_complement design {0, 1, 2} normalVec horthogonal
  rw [show (({0, 1, 2} : Finset (Fin 6)))ᶜ = {3, 4, 5} from by decide, hunit] at hcarried
  have hfreeSum : ∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)), design.weight freeLabel
      = design.weight 3 + design.weight 4 + design.weight 5 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have hbound : ∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      design.weight freeLabel * (design.atom freeLabel ⬝ᵥ normalVec) ^ 2
      ≤ ∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)), design.weight freeLabel := by
    refine Finset.sum_le_sum fun freeLabel hmem => ?_
    have hsq := hcontra freeLabel hmem
    have hweight := (design.weight_pos freeLabel).le
    simp only [normalReading] at hsq
    nlinarith
  have htotalWeight : design.weight 0 + design.weight 1 + design.weight 2
      + design.weight 3 + design.weight 4 + design.weight 5 = 1 := by
    have hsum := design.weight_sum_one
    rw [Fin.sum_univ_six] at hsum
    linarith
  have hlineWeightPos : 0 < design.weight 0 + design.weight 1 + design.weight 2 := by
    have h0 := design.weight_pos 0
    have h1 := design.weight_pos 1
    have h2 := design.weight_pos 2
    linarith
  rw [hcarried, hfreeSum] at hbound
  linarith

/-- **THE NECESSARY CORNER.**  A strictly dominating triple whose first two
members are flat against a unit normal must have its THIRD member read that
normal above one in absolute value: probe the gap at the normal itself and the
two flat members contribute nothing.  So `1 < h_x^2` is a necessary condition of
the collapsed criterion, and `Gtz.oneLine_exists_freeAtom_one_lt_normalReading_sq`
says the one-line stratum always supplies a free atom that meets it. -/
theorem one_lt_normalReading_sq_of_posDef_tripleGap_of_flatPair
    (design : WeightedDesign size 3) {normalVec : Fin 3 → ℝ}
    (hunit : normalVec ⬝ᵥ normalVec = 1) (pairFirst pairSecond thirdLabel : Fin size)
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0)
    (hposDef : (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef) :
    1 < normalReading design normalVec thirdLabel ^ 2 := by
  have hnormalNe : normalVec ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    exact absurd hunit.symm one_ne_zero
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hnormalNe
  rw [star_trivial, dominationGap_form, hunit] at hform
  rw [Finset.sum_insert (by simp [hFirstSecond, hFirstThird]),
    Finset.sum_insert (by simp [hSecondThird]), Finset.sum_singleton] at hform
  simp only [normalReading] at hFirstFlat hSecondFlat ⊢
  rw [hFirstFlat, hSecondFlat] at hform
  nlinarith [hform]

/-! ## Part 6: the residual, named, and the reduction -/

/-- **THE LINE-NORMAL BLIND SPOT.**  A design of the one-line stratum lies in the
blind spot when the lift criterion never fires at any unit line normal: no pair,
no third label, no direction flat against the whole line produces a guarded
positive margin.  This is a condition on the design data alone -- it never
mentions a strictly dominating triple -- so it is a legitimate residual for a
weak-to-strict obligation.

The restriction of the quantifier to normals flat against the WHOLE line is
load-bearing.  Quantifying over all unit normals instead would make the residual
circular: by the coverage theorem
`Gtz.exists_pos_liftMargin_of_posDef_tripleGap` the criterion sees EVERY strictly
dominating triple at some normal, so "never fires anywhere" would just restate
"no strictly dominating triple exists". -/
def IsOneLineNormalBlindSpot (design : WeightedDesign 6 3) : Prop :=
  ∀ normalVec : Fin 3 → ℝ, normalVec ⬝ᵥ normalVec = 1 →
    (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0) →
    ∀ pairFirst pairSecond thirdLabel : Fin 6, pairFirst ≠ pairSecond →
      pairFirst ≠ thirdLabel → pairSecond ≠ thirdLabel →
      ¬ (0 < shadowPairing design normalVec pairFirst pairFirst - 1
        ∧ 0 < shadowGapDeterminant design normalVec pairFirst pairSecond
        ∧ 0 < liftMargin design normalVec pairFirst pairSecond thirdLabel)

/-- **THE ONE-LINE REDUCTION THROUGH THE LIFT CRITERION.**  Stacked on the landed
`Gtz.patternHeavyWeakToStrict_of_capBlindSpot`: the whole obligation at the
one-line pattern follows from the designs that are simultaneously CAP blind and
LINE-NORMAL blind.  Outside the line-normal blind spot the criterion itself
produces the strictly dominating triple, with no pattern and no weak dominator
needed.  This does NOT discharge
`Skeleton.obligationHeavyWeakToStrictOneLine`: the joint residual is nonempty. -/
theorem patternHeavyWeakToStrict_oneLine_of_lineNormalBlindSpot
    (hresidual : ∀ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) →
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      IsOneLineNormalBlindSpot design →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by
  refine patternHeavyWeakToStrict_of_capBlindSpot _
    fun design hpattern hheavy hcapBlind hweak => ?_
  by_cases hlineBlind : IsOneLineNormalBlindSpot design
  · exact hresidual design hpattern hheavy hcapBlind hlineBlind hweak
  · simp only [IsOneLineNormalBlindSpot] at hlineBlind
    push Not at hlineBlind
    obtain ⟨normalVec, hunit, _, pairFirst, pairSecond, thirdLabel, hFirstSecond, hFirstThird,
      hSecondThird, hcorner, hdet, hmargin⟩ := hlineBlind
    exact exists_posDef_cardThree_of_pos_liftMargin design hunit pairFirst pairSecond thirdLabel
      hFirstSecond hFirstThird hSecondThird hcorner hdet hmargin

/-! ## Part 7: the combinatorial shape of the line-normal residual -/

/-- **THE SHAPE THEOREM.**  If NO line pair has positive shadow-gap determinant
at the line normal, then no strictly dominating triple contains TWO line atoms.
So the line-normal route is silent exactly when every winner meets the line at
most once, which localises the residual combinatorially rather than metrically:
it is cut out by the signs of three explicit `Gram - 1` minors. -/
theorem oneLine_not_posDef_linePairTriple_of_linePairBlindSpot
    (design : WeightedDesign 6 3) (normalVec : Fin 3 → ℝ)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0)
    (hlinePairDead : ∀ lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)),
      ∀ lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)),
        shadowGapDeterminant design normalVec lineFirst lineSecond ≤ 0)
    (lineFirst lineSecond thirdLabel : Fin 6)
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hFirstSecond : lineFirst ≠ lineSecond) (hFirstThird : lineFirst ≠ thirdLabel)
    (hSecondThird : lineSecond ≠ thirdLabel) :
    ¬ (subsetSum design {lineFirst, lineSecond, thirdLabel} - 1).PosDef :=
  not_posDef_tripleGap_of_flatPair_of_shadowGapDeterminant_nonpos design normalVec lineFirst
    lineSecond thirdLabel hFirstSecond hFirstThird hSecondThird
    (oneLine_normalReading_eq_zero design normalVec horthogonal lineFirst hFirstMem)
    (oneLine_normalReading_eq_zero design normalVec horthogonal lineSecond hSecondMem)
    (hlinePairDead lineFirst hFirstMem lineSecond hSecondMem)

/-! ## Part 8: calibration on the canonical one-line fixture -/

/-- The line of `Gtz.oneLineFailureDesign` lies in the plane `z = 0`, so the third
coordinate direction is already a UNIT line normal. -/
theorem oneLineFailureDesign_lineNormal_unit :
    (![0, 0, 1] : Fin 3 → ℝ) ⬝ᵥ ![0, 0, 1] = 1 := by
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

/-- All three line atoms are flat against it. -/
theorem oneLineFailureDesign_lineAtoms_flat (lineLabel : Fin 6)
    (hmem : lineLabel ∈ ({0, 1, 2} : Finset (Fin 6))) :
    oneLineFailureDesign.atom lineLabel ⬝ᵥ (![0, 0, 1] : Fin 3 → ℝ) = 0 := by
  fin_cases hmem <;>
    norm_num [oneLineFailureDesign, oneLineFailureAtom, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two]

/-- **EVERY LINE PAIR IS DEAD.**  At the line normal all nine shadow-gap
determinants of pairs drawn from the line are nonpositive: `{0,1}` sits exactly
at zero because atoms `0` and `1` have leverage exactly one, and the two pairs
through atom `2` sit at `-4`.  This is A0's leverage-one obstruction, measured. -/
theorem oneLineFailureDesign_linePair_shadowGapDeterminant_nonpos
    (lineFirst lineSecond : Fin 6)
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6))) :
    shadowGapDeterminant oneLineFailureDesign ![0, 0, 1] lineFirst lineSecond ≤ 0 := by
  fin_cases hFirstMem <;> fin_cases hSecondMem <;>
    norm_num [shadowGapDeterminant, shadowGapDeterminantOf, shadowPairing, normalReading,
      oneLineFailureDesign, oneLineFailureAtom, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two]

/-- **NO WINNER OF THE FIXTURE MEETS THE LINE TWICE.**  Combining the dead line
pairs with the shape theorem: on `Gtz.oneLineFailureDesign` no strictly
dominating triple contains two line atoms.  The landed strict dominators
`{2,3,5}` and `{2,4,5}` each meet the line exactly once, so this is sharp, and it
is why a line-pair certificate can never close this fixture. -/
theorem oneLineFailureDesign_not_posDef_linePairTriple (lineFirst lineSecond thirdLabel : Fin 6)
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hFirstSecond : lineFirst ≠ lineSecond) (hFirstThird : lineFirst ≠ thirdLabel)
    (hSecondThird : lineSecond ≠ thirdLabel) :
    ¬ (subsetSum oneLineFailureDesign {lineFirst, lineSecond, thirdLabel} - 1).PosDef :=
  oneLine_not_posDef_linePairTriple_of_linePairBlindSpot oneLineFailureDesign ![0, 0, 1]
    oneLineFailureDesign_lineAtoms_flat
    (fun lineOne hone lineTwo htwo =>
      oneLineFailureDesign_linePair_shadowGapDeterminant_nonpos lineOne lineTwo hone htwo)
    lineFirst lineSecond thirdLabel hFirstMem hSecondMem hFirstSecond hFirstThird hSecondThird

/-- The MIXED pair `{2,5}` -- one line atom and one free atom -- has a live shadow
gap at the same normal. -/
theorem oneLineFailure_shadowGapDeterminant_mixedPair :
    shadowGapDeterminant oneLineFailureDesign ![0, 0, 1] 2 5 = 7 := by
  norm_num [shadowGapDeterminant, shadowGapDeterminantOf, shadowPairing, normalReading,
    oneLineFailureDesign, oneLineFailureAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-- Its shadow corner. -/
theorem oneLineFailure_shadowPairing_mixedPair_corner :
    shadowPairing oneLineFailureDesign ![0, 0, 1] 2 2 = 8 := by
  norm_num [shadowPairing, normalReading, oneLineFailureDesign, oneLineFailureAtom, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]

/-- **THE MIXED PAIR FIRES, EXACTLY.**  The lift margin of `{2,5}` against the
free atom `3` at the line normal is `14`.  The identity
`Gtz.shadowGapDeterminantOf_mul_gapDeterminant_eq_liftMarginOf` then reads
`7 * det(gap) = 14`, i.e. the triple gap has determinant `2`. -/
theorem oneLineFailure_liftMargin_mixedPair_eq :
    liftMargin oneLineFailureDesign ![0, 0, 1] 2 5 3 = 14 := by
  norm_num [liftMargin, liftMarginOf, liftReadingOf, liftLeverageOf, liftDemandOf,
    shadowGapDeterminantOf, shadowPairing, normalReading, oneLineFailureDesign,
    oneLineFailureAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

/-- **END TO END.**  The lift criterion at the line normal, with the MIXED pair
`{2,5}`, gives an independent proof of the landed
`Gtz.oneLineFailure_mixedTripleGap_posDef` -- same statement, different route.  So
the line normal is NOT silent on this fixture; only its LINE pairs are, and the
winner it finds is the mixed one. -/
theorem oneLineFailure_mixedTripleGap_posDef_of_liftMargin :
    (subsetSum oneLineFailureDesign {2, 3, 5} - 1).PosDef := by
  have hlabelSet : ({2, 5, 3} : Finset (Fin 6)) = {2, 3, 5} := by decide
  have hcorner : 0 < shadowPairing oneLineFailureDesign ![0, 0, 1] 2 2 - 1 := by
    rw [oneLineFailure_shadowPairing_mixedPair_corner]
    norm_num
  have hdet : 0 < shadowGapDeterminant oneLineFailureDesign ![0, 0, 1] 2 5 := by
    rw [oneLineFailure_shadowGapDeterminant_mixedPair]
    norm_num
  have hmargin : 0 < liftMargin oneLineFailureDesign ![0, 0, 1] 2 5 3 := by
    rw [oneLineFailure_liftMargin_mixedPair_eq]
    norm_num
  rw [← hlabelSet]
  exact (posDef_tripleGap_iff_pos_liftMargin oneLineFailureDesign
    oneLineFailureDesign_lineNormal_unit 2 5 3 (by decide) (by decide) (by decide) hcorner
    hdet).mpr hmargin

end Gtz
