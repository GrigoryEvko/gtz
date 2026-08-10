import Gtz.Design.BarycentricOneSlotRigidity
import Gtz.Design.TightLineBranchLivePairBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Gtz

open Matrix

/-! # What the barycentric open cell actually covers

`Gtz.exists_posDef_cardThree_of_tightLine_of_barycentricOpenCell` is a partial
closure of the tight-line branch: on the cell where every barycentric coordinate
of every transverse free atom is positive, a line-free tight-line antecedent
already carries a strictly dominating card-three subset, and off-conicity is not
needed to say so.  Read alone, that invites the reading "the branch is partly
proved, so the residual is partly smaller".  It is not, and this file proves the
correction rather than asserting it.

The closure's proof finishes with the ONE-SLOT disjunct of the landed nineteen
candidates.  Transporting that winner out of the chart through
`unitAxisHiddenSubsetGap_oneSlot` and `posDef_gap_iff_unitAxisHiddenSubsetGap`
gives an ambient one-slot swap, so

    the open cell is contained in `TightLineOneSlotFamily`.

By the landed exhaustion
`exists_posDef_cardThree_iff_oneSlot_or_freePairPositiveTie`, the one-slot family
is exactly the EASY disjunct, and every residual of this development is
conditioned on its negation.  So the cell and the residual are disjoint, and the
two corollaries below make that precise from both sides: the cell misses the
conjecturally empty failure locus, and -- strictly more -- it misses the entire
no-one-slot stratum, which is where every hard witness and every refuted
ingredient of this wave lives.  Adjoining `¬ open cell` to the residual is
therefore FREE, and buys nothing.

None of this weakens the closure.  It is a genuine and cheap sufficient
condition for the easy disjunct: nine sign conditions on barycentric coordinates
decide what nine positive-definiteness tests would otherwise decide, and the
containment is strict -- roughly a tenth of the easy region in a stage-two
census, not all of it.  What the file forbids is spending it as leverage on the
part of the problem that is open.
-/

/-- **THE COVERAGE THEOREM.**  On the barycentric open cell the winner the
closure produces is always a ONE-SLOT swap, so the cell is contained in
`TightLineOneSlotFamily` -- the easy disjunct of the landed exhaustion. -/
theorem tightLineOneSlotFamily_of_barycentricOpenCell
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hopen : TightBarycentricOpenCell
      (unitAxisTightVector design tightDir) (unitAxisFreeAtom design)) :
    TightLineOneSlotFamily design := by
  have hweight := design.weight_sum_one
  rw [Fin.sum_univ_six] at hweight
  have hweightSix :
      design.weight (baseThreeLabel 0)
          + design.weight (baseThreeLabel 1)
          + design.weight (baseThreeLabel 2)
          + design.weight 3 + design.weight 4 + design.weight 5 = 1 := by
    simpa [baseThreeLabel] using hweight
  have hbracket :
      tripleBracket (unitAxisFreeAtom design 0)
          (unitAxisFreeAtom design 1) (unitAxisFreeAtom design 2) ≠ 0 := by
    simpa [unitAxisFreeFrame, tripleBracket] using
      unitAxisFreeFrame_det_ne_zero design hlineFree
  obtain ⟨omittedBase, freeIndex, hdet⟩ :=
    exists_hiddenOneSlotGap_det_pos_of_tightBarycentricOpenCell
      (unitAxisHiddenForm design) (unitAxisTightVector design tightDir)
      (unitAxisFreeAtom design)
      (design.weight 3) (design.weight 4) (design.weight 5)
      (fun coordinate => design.weight (baseThreeLabel coordinate))
      (unitAxisHiddenForm_transpose design)
      (unitAxisHiddenForm_mulVec_tightVector_eq_zero
        design hlineFree hdominates htight)
      (unitAxisFiveVectorIdentity design hlineFree)
      hweightSix (design.weight_pos 3) (design.weight_pos 4)
      (design.weight_pos 5) hopen hbracket
  have homitted : unitAxisTightVector design tightDir omittedBase ≠ 0 :=
    tight_coordinate_ne_zero_of_openCell
      (unitAxisTightVector design tightDir) (unitAxisFreeAtom design)
      hopen omittedBase
  have hposDef :
      (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design) omittedBase freeIndex).PosDef :=
    (unitAxisHiddenOneSlotGap_posDef_iff_det_pos_of_tightCoordinate_ne_zero
      design hlineFree hdominates htight hline omittedBase freeIndex
      homitted).mpr hdet
  have hsubset :
      (subsetSum design (unitAxisOneSlotSubset omittedBase freeIndex)
        - 1).PosDef := by
    rw [← posDef_gap_iff_unitAxisHiddenSubsetGap design hlineFree,
      unitAxisHiddenSubsetGap_oneSlot]
    exact hposDef
  refine ⟨baseThreeLabel omittedBase, ?_, freeThreeLabel freeIndex, ?_, ?_⟩
  · fin_cases omittedBase <;> decide
  · fin_cases freeIndex <;> decide
  · simpa [unitAxisOneSlotSubset] using hsubset

/-- **THE FAILURE LOCUS IS DISJOINT FROM THE OPEN CELL.**  Immediate from the
closure: on the cell a strict card-three subset already exists. -/
theorem not_tightBarycentricOpenCell_of_no_cardThree_posDef
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hfail : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    ¬ TightBarycentricOpenCell
        (unitAxisTightVector design tightDir) (unitAxisFreeAtom design) := by
  intro hopen
  obtain ⟨selected, hcard, hposDef⟩ :=
    exists_posDef_cardThree_of_tightLine_of_barycentricOpenCell
      design tightDir hlineFree hdominates htightNe htight hline hopen
  exact hfail selected hcard hposDef

/-- **AND THE CELL MISSES STRICTLY MORE THAN THE FAILURE LOCUS.**  It misses the
entire no-one-slot stratum -- where every hard witness and every refuted
ingredient of this development lives -- so adjoining `¬ open cell` to the
residual is free, and therefore buys nothing. -/
theorem not_tightBarycentricOpenCell_of_not_tightLineOneSlotFamily
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hno : ¬ TightLineOneSlotFamily design) :
    ¬ TightBarycentricOpenCell
        (unitAxisTightVector design tightDir) (unitAxisFreeAtom design) :=
  fun hopen => hno (tightLineOneSlotFamily_of_barycentricOpenCell
    design tightDir hlineFree hdominates htight hline hopen)

end Gtz
