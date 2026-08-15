import Gtz.Design.UThreeSixDisjunction
import Gtz.Wave.ProjectionDictionary

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The tenth-light closure wired into the A1 residual

`ProjectionDictionary` turns the unconditional real tenth spectral supply into
a strict triple whenever all six weights are below `1/10`.  This module spends
that theorem at the exact line-free/off-conic consumer, after the separated
weak-direction and twenty-triple balance reductions have also fired.

The surviving residual carries every previously landed tie pin, the complete
no-light-triple ledger, and an explicit tenth-heavy label.  The final IFF shows
that presenting this residual in the obligation registry changes the formula,
not the strength of A1.
-/

namespace Gtz

open Matrix Finset

/-! ## The global no-strict consumer -/

/-- Every `(6,3)` design with no strictly dominating triple has a tenth-heavy
label.  This is the contrapositive form of the projection dictionary's light
region, packaged for crux and tie consumers. -/
theorem exists_weight_ge_tenth_of_no_strict_triple
    (design : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    ∃ label : Fin 6, 1 / 10 ≤ design.weight label := by
  by_contra hheavy
  push Not at hheavy
  obtain ⟨selected, hcard, hposDef⟩ :=
    exists_posDef_triple_of_weights_lt_tenth design hheavy
  exact hnoStrict selected hcard hposDef

/-- In particular, every `(6,3)` tie has a tenth-heavy label. -/
theorem exists_weight_ge_tenth_of_isTie (design : WeightedDesign 6 3)
    (htie : IsTie design) :
    ∃ label : Fin 6, 1 / 10 ≤ design.weight label :=
  exists_weight_ge_tenth_of_no_strict_triple design htie.2

/-! ## The A1 consumer -/

/-- The surviving A1 branch after spending the complement residual, all twenty
balance certificates, and the strict tenth-light theorem. -/
def BaseTripleTightLineFreeOffConicSeparatedHeavyResidual : Prop :=
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
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - 1).PosDef

/-- **THE WIRED A1 REDUCTION.**  To prove the registered A1 proposition it is
enough to solve the separated residual in which no twenty-triple balance
certificate fires and at least one atom is tenth-heavy. -/
theorem baseTripleTightLineFreeOffConicWeakToStrict_of_separatedHeavyResidual
    (hresidual : BaseTripleTightLineFreeOffConicSeparatedHeavyResidual) :
    BaseTripleTightLineFreeOffConicWeakToStrict := by
  refine baseTripleTightLineFreeOffConicWeakToStrict_of_separatedWeakResidualBranch ?_
  intro design tightDir weakDir hlineFree hoffConic hdominates
    htightNe htight hweakNe hweak htightSeparated hheavyBase hbaseUpper
    hdiscriminant hbaseNotStrict hbaseResidual
  by_cases hbalanceLight : ∃ lightTriple : Finset (Fin 6),
      lightTriple.card = 3 ∧ ∃ maxWeight : ℝ,
      0 < maxWeight ∧
        (∀ label ∈ lightTripleᶜ, design.weight label ≤ maxWeight) ∧
        ∑ label ∈ lightTriple, atomShare design label < 1 - maxWeight
  · obtain ⟨lightTriple, hcard, maxWeight, hmaxPos, hmaxBound, hshare⟩ :=
      hbalanceLight
    exact exists_posDef_cardThree_of_lightTriple design lightTriple hcard
      maxWeight hmaxPos hmaxBound hshare
  · have hnoLight : ∀ lightTriple : Finset (Fin 6), lightTriple.card = 3 →
        ∀ maxWeight : ℝ, 0 < maxWeight →
        (∀ label ∈ lightTripleᶜ, design.weight label ≤ maxWeight) →
        1 - maxWeight ≤ ∑ label ∈ lightTriple, atomShare design label := by
      push Not at hbalanceLight
      exact hbalanceLight
    by_cases hheavy : ∃ heavyLabel : Fin 6,
        1 / 10 ≤ design.weight heavyLabel
    · exact hresidual design tightDir weakDir hlineFree hoffConic hdominates
        htightNe htight hweakNe hweak htightSeparated hheavyBase hbaseUpper
        hdiscriminant hbaseNotStrict hbaseResidual hnoLight hheavy
    · apply exists_posDef_triple_of_weights_lt_tenth design
      intro label
      exact lt_of_not_ge fun hge => hheavy ⟨label, hge⟩

/-- The original A1 statement trivially supplies the restricted residual.  In
combination with the wired reduction this proves that changing the registry to
the residual changes only the formula presented to a prover, not its strength. -/
theorem separatedHeavyResidual_of_baseTripleTightLineFreeOffConicWeakToStrict
    (hbase : BaseTripleTightLineFreeOffConicWeakToStrict) :
    BaseTripleTightLineFreeOffConicSeparatedHeavyResidual := by
  intro design tightDir _weakDir hlineFree hoffConic hdominates
    htightNe htight _hweakNe _hweak _htightSeparated _hheavyBase _hbaseUpper
    _hdiscriminant _hbaseNotStrict _hbaseResidual _hnoLight _hheavy
  exact hbase design tightDir hlineFree hoffConic hdominates htightNe htight

/-- The fully wired residual is kernel-equivalent to the registered A1
statement. -/
theorem baseTripleTightLineFreeOffConicSeparatedHeavyResidual_iff :
    BaseTripleTightLineFreeOffConicSeparatedHeavyResidual ↔
      BaseTripleTightLineFreeOffConicWeakToStrict :=
  ⟨baseTripleTightLineFreeOffConicWeakToStrict_of_separatedHeavyResidual,
    separatedHeavyResidual_of_baseTripleTightLineFreeOffConicWeakToStrict⟩

/-- Direct consumer in the line-free stress-free class. -/
theorem stressFreeStratumIsTieFree_lineFree_of_separatedHeavyResidual
    (hresidual : BaseTripleTightLineFreeOffConicSeparatedHeavyResidual) :
    StressFreeStratumIsTieFree
      (lineFamilyPattern ([] : List (List (Fin 6)))) :=
  stressFreeStratumIsTieFree_lineFree_of_baseTripleTight
    (baseTripleTightLineFreeOffConicWeakToStrict_of_separatedHeavyResidual hresidual)

end Gtz
