import Gtz.Wave.TenthLightA1Wiring
import Gtz.Ties.ComplementJawWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spend the complement-jaw needle law in the A1 residual

The line-free/off-conic obligation already carries the largest weight on the
base triple and on its complement.  Their maximum is therefore a positive
global weight cap.  If the desired strict triple did not exist, the weak base
triple would make the design an `IsTie`, so `exists_gapNeedle_of_isTie_six_three`
applies to every one of the twenty triples at that exact cap.

This module inserts that conclusion into the live A1 formula.  The resulting
counterexample residual is exactly equivalent to the former separated-heavy
residual, but an eventual proof receives the no-strict ledger, the numerical
range of the global cap, and a nonzero gap needle on every triple as explicit
hypotheses.
-/

namespace Gtz

open Matrix Finset

/-! ## The pinned global cap -/

/-- The maximum of the maxima on the pinned base triple and its complement. -/
noncomputable def baseComplementMaxWeight (design : WeightedDesign 6 3) : ℝ :=
  max (baseTripleMaxWeight design) (complementTripleMaxWeight design)

/-- Every label is bounded by the pinned global cap. -/
theorem weight_le_baseComplementMaxWeight (design : WeightedDesign 6 3) (label : Fin 6) :
    design.weight label ≤ baseComplementMaxWeight design := by
  by_cases hbase : label ∈ ({0, 1, 2} : Finset (Fin 6))
  · exact (weight_le_baseTripleMaxWeight design label hbase).trans
      (le_max_left _ _)
  · have hcompl : label ∈ (({0, 1, 2} : Finset (Fin 6))ᶜ) :=
      Finset.mem_compl.mpr hbase
    exact (weight_le_complementTripleMaxWeight design label hcompl).trans
      (le_max_right _ _)

/-- The pinned global cap is positive. -/
theorem baseComplementMaxWeight_pos (design : WeightedDesign 6 3) :
    0 < baseComplementMaxWeight design :=
  (design.weight_pos 0).trans_le (weight_le_baseComplementMaxWeight design 0)

/-- The pinned global cap is attained by one of the six labels. -/
theorem exists_eq_baseComplementMaxWeight (design : WeightedDesign 6 3) :
    ∃ label : Fin 6, baseComplementMaxWeight design = design.weight label := by
  rcases max_choice (baseTripleMaxWeight design) (complementTripleMaxWeight design) with
    hbase | hcompl
  · rcases exists_eq_baseTripleMaxWeight design with hzero | hone | htwo
    · exact ⟨0, hbase.trans hzero⟩
    · exact ⟨1, hbase.trans hone⟩
    · exact ⟨2, hbase.trans htwo⟩
  · rcases exists_eq_complementTripleMaxWeight design with hthree | hfour | hfive
    · exact ⟨3, hcompl.trans hthree⟩
    · exact ⟨4, hcompl.trans hfour⟩
    · exact ⟨5, hcompl.trans hfive⟩

/-- Positivity of the other five weights keeps the global cap strictly below
one. -/
theorem baseComplementMaxWeight_lt_one (design : WeightedDesign 6 3) :
    baseComplementMaxWeight design < 1 := by
  obtain ⟨label, hlabel⟩ := exists_eq_baseComplementMaxWeight design
  rw [hlabel]
  exact weight_lt_one design (by norm_num) label

/-- A tenth-heavy label makes the pinned global cap at least `1/10`. -/
theorem tenth_le_baseComplementMaxWeight_of_exists_heavy
    (design : WeightedDesign 6 3)
    (hheavy : ∃ label : Fin 6, 1 / 10 ≤ design.weight label) :
    1 / 10 ≤ baseComplementMaxWeight design := by
  obtain ⟨label, hlabel⟩ := hheavy
  exact hlabel.trans (weight_le_baseComplementMaxWeight design label)

/-! ## The exact A1 counterexample residual -/

/-- The surviving A1 counterexample after spending the complement-jaw needle
law at the exact global cap supplied by the two pinned triple maxima. -/
def BaseTripleTightLineFreeOffConicHeavyNeedleResidual : Prop :=
  ∀ (design : WeightedDesign 6 3) (tightDir weakDir : Fin 3 → ℝ),
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    Dominates design {0, 1, 2} →
    tightDir ≠ 0 →
    tightDir ⬝ᵥ ((subsetSum design {0, 1, 2} - 1) *ᵥ tightDir) = 0 →
    weakDir ≠ 0 →
    weakDir ⬝ᵥ (baseResidual design ({0, 1, 2} : Finset (Fin 6)) *ᵥ weakDir)
      ≤ complementTripleMaxWeight design * (weakDir ⬝ᵥ weakDir) →
    complementTripleMaxWeight design * (tightDir ⬝ᵥ tightDir)
      < tightDir ⬝ᵥ (baseResidual design ({0, 1, 2} : Finset (Fin 6)) *ᵥ tightDir) →
    1 - complementTripleMaxWeight design
      ≤ ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare design label →
    ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare design label
      ≤ 2 + baseTripleMaxWeight design →
    discriminantTie design 0 1 2 = 0 →
    ¬ (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef →
    (baseResidual design ({0, 1, 2} : Finset (Fin 6))).PosDef →
    (∀ lightTriple : Finset (Fin 6), lightTriple.card = 3 →
      ∀ maxWeight : ℝ, 0 < maxWeight →
      (∀ label ∈ lightTripleᶜ, design.weight label ≤ maxWeight) →
      1 - maxWeight ≤ ∑ label ∈ lightTriple, atomShare design label) →
    (∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel) →
    (∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) →
    1 / 10 ≤ baseComplementMaxWeight design →
    baseComplementMaxWeight design < 1 →
    (∀ selected : Finset (Fin 6), selected.card = 3 →
      ∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧
        (1 - 2 * baseComplementMaxWeight design) * (probe ⬝ᵥ probe)
          ≤ baseComplementMaxWeight design
            * (probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe))) →
    False

/-- The sharpened counterexample residual discharges the former A1 residual. -/
theorem separatedHeavyResidual_of_heavyNeedleResidual
    (hneedle : BaseTripleTightLineFreeOffConicHeavyNeedleResidual) :
    BaseTripleTightLineFreeOffConicSeparatedHeavyResidual := by
  intro design tightDir weakDir hlineFree hoffConic hdominates
    htightNe htight hweakNe hweak htightSeparated hheavyBase hbaseUpper
    hdiscriminant hbaseNotStrict hbaseResidual hnoLight hheavy
  by_contra hstrict
  push Not at hstrict
  have htie : IsTie design :=
    ⟨⟨({0, 1, 2} : Finset (Fin 6)), by decide, hdominates⟩, hstrict⟩
  have hneedles : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧
        (1 - 2 * baseComplementMaxWeight design) * (probe ⬝ᵥ probe)
          ≤ baseComplementMaxWeight design
            * (probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe)) := by
    intro selected hcard
    exact exists_gapNeedle_of_isTie_six_three design htie
      (baseComplementMaxWeight design) (baseComplementMaxWeight_pos design)
      (weight_le_baseComplementMaxWeight design) selected hcard
  exact hneedle design tightDir weakDir hlineFree hoffConic hdominates
    htightNe htight hweakNe hweak htightSeparated hheavyBase hbaseUpper
    hdiscriminant hbaseNotStrict hbaseResidual hnoLight hheavy hstrict
    (tenth_le_baseComplementMaxWeight_of_exists_heavy design hheavy)
    (baseComplementMaxWeight_lt_one design) hneedles

/-- The former separated-heavy residual supplies the restricted counterexample
formula by contradicting its no-strict ledger. -/
theorem heavyNeedleResidual_of_separatedHeavyResidual
    (hresidual : BaseTripleTightLineFreeOffConicSeparatedHeavyResidual) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual := by
  intro design tightDir weakDir hlineFree hoffConic hdominates
    htightNe htight hweakNe hweak htightSeparated hheavyBase hbaseUpper
    hdiscriminant hbaseNotStrict hbaseResidual hnoLight hheavy hnoStrict
    _htenth _hbelowOne _hneedles
  obtain ⟨selected, hcard, hposDef⟩ :=
    hresidual design tightDir weakDir hlineFree hoffConic hdominates
      htightNe htight hweakNe hweak htightSeparated hheavyBase hbaseUpper
      hdiscriminant hbaseNotStrict hbaseResidual hnoLight hheavy
  exact hnoStrict selected hcard hposDef

/-- The needle-wired counterexample residual is exactly A1. -/
theorem baseTripleTightLineFreeOffConicHeavyNeedleResidual_iff :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ↔
      BaseTripleTightLineFreeOffConicWeakToStrict :=
  ⟨fun hneedle =>
      baseTripleTightLineFreeOffConicWeakToStrict_of_separatedHeavyResidual
        (separatedHeavyResidual_of_heavyNeedleResidual hneedle),
    fun hbase => heavyNeedleResidual_of_separatedHeavyResidual
      (separatedHeavyResidual_of_baseTripleTightLineFreeOffConicWeakToStrict hbase)⟩

/-- Direct A1 consumer for the stress-free line-free class. -/
theorem stressFreeStratumIsTieFree_lineFree_of_heavyNeedleResidual
    (hneedle : BaseTripleTightLineFreeOffConicHeavyNeedleResidual) :
    StressFreeStratumIsTieFree
      (lineFamilyPattern ([] : List (List (Fin 6)))) :=
  stressFreeStratumIsTieFree_lineFree_of_separatedHeavyResidual
    (separatedHeavyResidual_of_heavyNeedleResidual hneedle)

end Gtz
