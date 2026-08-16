import Gtz.Wave.A1NeedleWiring
import Gtz.Design.LineFreeConicBridge
import Gtz.Design.StressFreeMatroidStratification

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The A1 needle antecedent collapses onto the class statement

`Gtz.BaseTripleTightLineFreeOffConicHeavyNeedleResidual` carries nineteen
hypotheses.  Four of them name the stratum and the pinned base triple.  The
other fifteen read as a sharpening: a tight direction, a weak direction, a
strict separation, two share sandwiches, a zero discriminant, a positive base
residual, a twenty-triple balance family, a tenth-heavy label, two window edges
on the global cap, and a gap needle at every one of the twenty triples.

This module proves that the fifteen are FREE.  Each one follows from the four
that name the stratum, together with the no-strict ledger.  The producers are
all landed.  Nobody had assembled them, so the axiom read as a sharpening.

The result is an equivalence.  The registry axiom holds exactly when the
line-free off-conic stratum carries no tie.  That is the class statement
itself, so the four producer layers between the axiom and the class buy
nothing.

Read the equivalence in the other direction.  The axiom fails exactly when one
line-free off-conic `(6,3)` design is a tie.  There is no cheaper counterexample
than that, and there is no cheaper theorem than the class statement.

## The five producers that carry the collapse

- The weak direction: were there none, the residual form would exceed the
  largest complement weight at every probe, and
  `Gtz.posDef_subsetSum_complementTriple_of_residualExceedsMaxWeight` would make
  `{3,4,5}` strict.
- The light-triple family: were one triple light, its complement would be
  strict by `Gtz.exists_posDef_cardThree_of_lightTriple`.
- The strict separation, the two share sandwiches and the zero discriminant are
  landed consequences of the tight direction alone.
- The positive base residual is landed from line-freeness alone.
- The gap needle is the landed complement-jaw law at a tie.
-/

namespace Gtz

open Matrix Finset

/-! ## The two hypotheses that the no-strict ledger supplies -/

/-- **The weak direction is free at a tie.**  A design whose complement triple
fails to dominate strictly carries a nonzero probe on which the base residual
form sits at or below the largest complement weight.  Otherwise Family One fires
and `{3,4,5}` is strict. -/
theorem exists_weakDirection_of_not_posDef_complementTriple (design : WeightedDesign 6 3)
    (hnotStrict : ¬ (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef) :
    ∃ weakDir : Fin 3 → ℝ, weakDir ≠ 0 ∧
      weakDir ⬝ᵥ (baseResidual design ({0, 1, 2} : Finset (Fin 6)) *ᵥ weakDir)
        ≤ complementTripleMaxWeight design * (weakDir ⬝ᵥ weakDir) := by
  by_contra hcon
  push Not at hcon
  exact hnotStrict (posDef_subsetSum_complementTriple_of_residualExceedsMaxWeight design
    (fun probeVec hne => hcon probeVec hne))

/-- **The twenty-triple balance family is free at a tie.**  A light triple
anywhere hands its complement over as a strict dominator, so the no-strict
ledger forces every triple to carry its share. -/
theorem lightTripleBalance_of_noStrictTriple (design : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    ∀ lightTriple : Finset (Fin 6), lightTriple.card = 3 →
      ∀ maxWeight : ℝ, 0 < maxWeight →
      (∀ label ∈ lightTripleᶜ, design.weight label ≤ maxWeight) →
      1 - maxWeight ≤ ∑ label ∈ lightTriple, atomShare design label := by
  intro lightTriple hcard maxWeight hmaxPos hmaxBound
  by_contra hlight
  obtain ⟨selected, hselectedCard, hselectedPosDef⟩ :=
    exists_posDef_cardThree_of_lightTriple design lightTriple hcard maxWeight hmaxPos
      hmaxBound (not_le.mp hlight)
  exact hnoStrict selected hselectedCard hselectedPosDef

/-! ## The collapse, counterexample side -/

/-- **THE FIFTEEN DECORATIONS ARE FREE.**  One line-free off-conic `(6,3)`
design whose base triple dominates weakly and whose twenty triples all fail to
dominate strictly refutes the whole needle residual.  Every hypothesis beyond
the four naming ones is produced here from landed laws, so a counterexample
needs nothing but a line-free off-conic tie at the pinned base triple. -/
theorem not_heavyNeedleResidual_of_lineFreeOffConicBaseTie (design : WeightedDesign 6 3)
    (hlineFree : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    ¬ BaseTripleTightLineFreeOffConicHeavyNeedleResidual := by
  intro hresidual
  have htie : IsTie design :=
    ⟨⟨({0, 1, 2} : Finset (Fin 6)), by decide, hdominates⟩, hnoStrict⟩
  obtain ⟨tightDir, htightNe, htight⟩ :=
    exists_tightDirection_of_dominates_not_posDef design ({0, 1, 2} : Finset (Fin 6))
      hdominates (hnoStrict ({0, 1, 2} : Finset (Fin 6)) (by decide))
  obtain ⟨weakDir, hweakNe, hweak⟩ :=
    exists_weakDirection_of_not_posDef_complementTriple design
      (hnoStrict ({3, 4, 5} : Finset (Fin 6)) (by decide))
  have hheavy : ∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel :=
    exists_weight_ge_tenth_of_no_strict_triple design hnoStrict
  exact hresidual design tightDir weakDir hlineFree hoffConic hdominates htightNe htight
    hweakNe hweak
    (complementTripleMaxWeight_lt_dotProduct_baseResidual_mulVec_tightDirection design
      htightNe htight)
    (heavyBaseTripleShare_of_weakDirection design hweakNe hweak)
    (sum_atomShare_baseTriple_le_of_tightDirection design htightNe htight)
    (discriminantTie_baseTriple_eq_zero_of_tightDirection design hdominates htightNe htight)
    (hnoStrict ({0, 1, 2} : Finset (Fin 6)) (by decide))
    (posDef_baseResidual_baseTriple_of_lineFree design hlineFree)
    (lightTripleBalance_of_noStrictTriple design hnoStrict)
    hheavy hnoStrict
    (tenth_le_baseComplementMaxWeight_of_exists_heavy design hheavy)
    (baseComplementMaxWeight_lt_one design)
    (fun selected hcard => exists_gapNeedle_of_isTie_six_three design htie
      (baseComplementMaxWeight design) (baseComplementMaxWeight_pos design)
      (weight_le_baseComplementMaxWeight design) selected hcard)

/-! ## The collapse, theorem side -/

/-- **The needle residual follows from bare tie-freeness.**  Nothing but the
four naming hypotheses and the no-strict ledger is read. -/
theorem heavyNeedleResidual_of_pinnedStratumTieFree
    (hclass : ∀ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
      HasNoCommonQuadric design.atom → ¬ IsTie design) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual := by
  intro design _tightDir _weakDir hlineFree hoffConic hdominates _htightNe _htight
    _hweakNe _hweak _hseparated _hheavyBase _hbaseUpper _hdiscriminant _hbaseNotStrict
    _hbaseResidual _hnoLight _hheavy hnoStrict _htenth _hbelowOne _hneedles
  exact hclass design hlineFree hoffConic
    ⟨⟨({0, 1, 2} : Finset (Fin 6)), by decide, hdominates⟩, hnoStrict⟩

/-! ## The empty pattern is relabelling-blind -/

/-- **The empty line family absorbs every relabelling.**  Both readings of the
pattern are the everywhere-false one, so the class statement and its
identity-labelled form agree. -/
theorem lineFreeOffConicTieFree_iff_stressFreeStratumIsTieFree :
    (∀ design : WeightedDesign 6 3,
        HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
        HasNoCommonQuadric design.atom → ¬ IsTie design)
      ↔ StressFreeStratumIsTieFree (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  constructor
  · intro hplain design relabel hstressFree hpattern
    refine hplain design ?_ ((isStressFreeDesign_iff_hasNoCommonQuadric design).mp hstressFree)
    intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
    have hread := hpattern leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
    simpa [lineFamilyPattern] using hread
  · intro hclass design hlineFree hoffConic
    refine hclass design (Equiv.refl (Fin 6))
      ((isStressFreeDesign_iff_hasNoCommonQuadric design).mpr hoffConic) ?_
    intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
    have hread := hlineFree leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
    simpa [lineFamilyPattern] using hread

/-! ## The equivalence -/

/-- **THE COLLAPSE.**  The registry axiom is the class statement, verbatim.
Every one of the fifteen hypotheses that the four producer layers install is a
consequence of the four naming hypotheses plus the no-strict ledger, so the
sharpening chain has zero content.  An eventual prover receives nothing from it
that the class statement did not already hand over. -/
theorem heavyNeedleResidual_iff_lineFreeOffConicTieFree :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ↔
      ∀ design : WeightedDesign 6 3,
        HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
        HasNoCommonQuadric design.atom → ¬ IsTie design := by
  refine ⟨fun hneedle => ?_, heavyNeedleResidual_of_pinnedStratumTieFree⟩
  exact lineFreeOffConicTieFree_iff_stressFreeStratumIsTieFree.mpr
    (stressFreeStratumIsTieFree_lineFree_of_heavyNeedleResidual hneedle)

/-- **The axiom and the class statement are one statement.** -/
theorem heavyNeedleResidual_iff_stressFreeStratumIsTieFree :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ↔
      StressFreeStratumIsTieFree (lineFamilyPattern ([] : List (List (Fin 6)))) :=
  heavyNeedleResidual_iff_lineFreeOffConicTieFree.trans
    lineFreeOffConicTieFree_iff_stressFreeStratumIsTieFree

/-! ## The inhabitation reading -/

/-- **THE ONLY COUNTEREXAMPLE SHAPE.**  If the registry axiom is false, then one
line-free off-conic `(6,3)` design is a tie.  No other object refutes it. -/
theorem exists_lineFreeOffConicTie_of_not_heavyNeedleResidual
    (hfalse : ¬ BaseTripleTightLineFreeOffConicHeavyNeedleResidual) :
    ∃ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) ∧
        HasNoCommonQuadric design.atom ∧ IsTie design := by
  by_contra hcon
  push Not at hcon
  exact hfalse (heavyNeedleResidual_of_pinnedStratumTieFree
    (fun design hlineFree hoffConic => hcon design hlineFree hoffConic))

/-- **The pinned form of the same reading.**  A counterexample can always be
presented with its weak dominator at the base triple. -/
theorem not_heavyNeedleResidual_iff_exists_lineFreeOffConicTie :
    ¬ BaseTripleTightLineFreeOffConicHeavyNeedleResidual ↔
      ∃ design : WeightedDesign 6 3,
        HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) ∧
          HasNoCommonQuadric design.atom ∧ IsTie design := by
  refine ⟨exists_lineFreeOffConicTie_of_not_heavyNeedleResidual, ?_⟩
  rintro ⟨design, hlineFree, hoffConic, htie⟩ hneedle
  exact (heavyNeedleResidual_iff_lineFreeOffConicTieFree.mp hneedle) design hlineFree
    hoffConic htie

end Gtz
