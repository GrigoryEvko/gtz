import Gtz.Design.FreePairPlane
import Gtz.Design.LineFreeConicBridge
import Gtz.Design.UThreeSixDisjunction
import Gtz.Design.TightDoubleSwapObstructions
import Gtz.Design.TightAntecedentMining
import Gtz.Design.ComplementHeavy
import Gtz.Quantitative.WindowGramSignature
import Gtz.Quantitative.GeneralPositionWindow
import Gtz.Quantitative.DesignQuadraticFloors
import Gtz.Design.CrossAxisAtlas
import Gtz.Design.OneDeterminantReduction
import Gtz.Design.TightAxisPairBudget
import Gtz.Corner.CapDictionary
import Gtz.Ties.TotalTieCorankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The U(3,6) tight-line branch: candidates, families and the live-pair bridge
-/

namespace Gtz

open Matrix

/-! ## Part 1: label combinatorics of the base triple -/

/-- A label outside the base triple is one of the three free labels. -/
theorem freeLabel_eq_of_not_mem_baseTriple {label : Fin 6}
    (hnotMem : label ∉ ({0, 1, 2} : Finset (Fin 6))) :
    label = 3 ∨ label = 4 ∨ label = 5 := by
  revert hnotMem
  revert label
  decide

/-- A label inside the base triple is one of the three base labels. -/
theorem baseLabel_eq_of_mem_baseTriple {label : Fin 6}
    (hmem : label ∈ ({0, 1, 2} : Finset (Fin 6))) :
    label = 0 ∨ label = 1 ∨ label = 2 := by
  revert hmem
  revert label
  decide

/-! ## Part 2: the nineteen non-base candidates -/

/-- The nineteen card-three label sets other than the base triple, each asked to
dominate strictly.  On the tight-line branch nothing prunes this list further:
unlike the plane branch, the one-slot swaps survive. -/
def TightLineNineteenCandidate (design : WeightedDesign 6 3) : Prop :=
  (subsetSum design ({0, 1, 3} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({0, 1, 4} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({0, 1, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({0, 2, 3} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({0, 2, 4} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({0, 2, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({0, 3, 4} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({0, 3, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({0, 4, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({1, 2, 3} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({1, 2, 4} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({1, 2, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({1, 3, 4} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({1, 3, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({1, 4, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({2, 3, 4} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({2, 3, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({2, 4, 5} : Finset (Fin 6)) - 1).PosDef
    ∨ (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef

/-- **Exact candidate reduction for the tight-line branch.**  A nonzero tight
direction of the base triple already excludes the base triple itself, so
strict-triple existence is equivalent to the explicit nineteen-way disjunction.
The tight-line analogue of `Gtz.exists_posDef_cardThree_iff_planeBranchTenCandidate`;
there the corank obstruction removes nine more candidates, here none can be. -/
theorem exists_posDef_cardThree_iff_tightLineNineteenCandidate
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    (∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef)
      ↔ TightLineNineteenCandidate design := by
  classical
  have hbaseNot :
      ¬ (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef :=
    not_posDef_baseTripleGap_of_tightDirection design htightNe htight
  constructor
  · rintro ⟨selected, hcard, hpos⟩
    have hpow : selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3 :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    rcases cardThreeFinsetsOfSix_enumeration selected hpow with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hbaseNot hpos)
    · exact Or.inl hpos
    · exact Or.inr (Or.inl hpos)
    · exact Or.inr (Or.inr (Or.inl hpos))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hpos)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpos))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpos)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpos))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpos)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl hpos))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl hpos)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl hpos))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl hpos)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpos))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpos)))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpos))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl hpos)))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl hpos))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl hpos)))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr hpos)))))))))))))))))
  · intro hcandidates
    rcases hcandidates with h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h
    · exact ⟨{0, 1, 3}, by decide, h⟩
    · exact ⟨{0, 1, 4}, by decide, h⟩
    · exact ⟨{0, 1, 5}, by decide, h⟩
    · exact ⟨{0, 2, 3}, by decide, h⟩
    · exact ⟨{0, 2, 4}, by decide, h⟩
    · exact ⟨{0, 2, 5}, by decide, h⟩
    · exact ⟨{0, 3, 4}, by decide, h⟩
    · exact ⟨{0, 3, 5}, by decide, h⟩
    · exact ⟨{0, 4, 5}, by decide, h⟩
    · exact ⟨{1, 2, 3}, by decide, h⟩
    · exact ⟨{1, 2, 4}, by decide, h⟩
    · exact ⟨{1, 2, 5}, by decide, h⟩
    · exact ⟨{1, 3, 4}, by decide, h⟩
    · exact ⟨{1, 3, 5}, by decide, h⟩
    · exact ⟨{1, 4, 5}, by decide, h⟩
    · exact ⟨{2, 3, 4}, by decide, h⟩
    · exact ⟨{2, 3, 5}, by decide, h⟩
    · exact ⟨{2, 4, 5}, by decide, h⟩
    · exact ⟨{3, 4, 5}, by decide, h⟩

/-- The tight-line branch restated on the explicit nineteen candidates. -/
def UThreeSixTightLineNineteenCandidateBranch : Prop :=
  ∀ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    Dominates design ({0, 1, 2} : Finset (Fin 6)) →
    tightDir ≠ 0 →
    IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir →
    HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir →
    TightLineNineteenCandidate design

/-- **The tight-line half of the U(3,6) frontier, in explicit finite form.** -/
theorem uThreeSixTightLineBranch_iff_nineteenCandidateBranch :
    UThreeSixTightLineBranch ↔ UThreeSixTightLineNineteenCandidateBranch := by
  constructor
  · intro hbranch design tightDir hlineFree hoffConic hdominates htightNe htight hline
    exact (exists_posDef_cardThree_iff_tightLineNineteenCandidate design htightNe
      htight).mp
      (hbranch design tightDir hlineFree hoffConic hdominates htightNe htight hline)
  · intro hbranch design tightDir hlineFree hoffConic hdominates htightNe htight hline
    exact (exists_posDef_cardThree_iff_tightLineNineteenCandidate design htightNe
      htight).mpr
      (hbranch design tightDir hlineFree hoffConic hdominates htightNe htight hline)

/-! ## Part 3: the three candidate families -/

/-- Some one-slot swap of the base triple strictly dominates. -/
def TightLineOneSlotFamily (design : WeightedDesign 6 3) : Prop :=
  ∃ swapOut ∈ ({0, 1, 2} : Finset (Fin 6)), ∃ swapIn ∉ ({0, 1, 2} : Finset (Fin 6)),
    (subsetSum design (insert swapIn ((({0, 1, 2} : Finset (Fin 6))).erase swapOut))
      - 1).PosDef

/-- Some distance-two exchange of the base triple strictly dominates: one base
label is retained and two free labels come in. -/
def TightLineDoubleSwapFamily (design : WeightedDesign 6 3) : Prop :=
  ∃ swapOutFirst ∈ ({0, 1, 2} : Finset (Fin 6)),
    ∃ swapOutSecond ∈ ({0, 1, 2} : Finset (Fin 6)),
      ∃ swapInFirst ∉ ({0, 1, 2} : Finset (Fin 6)),
        ∃ swapInSecond ∉ ({0, 1, 2} : Finset (Fin 6)),
          swapOutFirst ≠ swapOutSecond ∧ swapInFirst ≠ swapInSecond ∧
            (subsetSum design (tightDoubleSwap ({0, 1, 2} : Finset (Fin 6))
              swapOutFirst swapOutSecond swapInFirst swapInSecond) - 1).PosDef

/-- The full complement of the base triple strictly dominates. -/
def TightLineComplementCandidate (design : WeightedDesign 6 3) : Prop :=
  (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef

/-- **The nineteen candidates ARE the three families.**  Every non-base
card-three label set is a one-slot swap, a distance-two exchange, or the
complement, and conversely each family member has card three, so the explicit
disjunction and the three-family disjunction are the same statement. -/
theorem tightLineNineteenCandidate_iff_tightLineThreeFamilies
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    TightLineNineteenCandidate design ↔
      (TightLineOneSlotFamily design ∨ TightLineDoubleSwapFamily design
        ∨ TightLineComplementCandidate design) := by
  classical
  constructor
  · intro hcandidates
    rcases hcandidates with h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h
    · exact Or.inl ⟨2, by decide, 3, by decide, by
        rw [show insert (3 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 2)
          = ({0, 1, 3} : Finset (Fin 6)) from by decide]
        exact h⟩
    · exact Or.inl ⟨2, by decide, 4, by decide, by
        rw [show insert (4 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 2)
          = ({0, 1, 4} : Finset (Fin 6)) from by decide]
        exact h⟩
    · exact Or.inl ⟨2, by decide, 5, by decide, by
        rw [show insert (5 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 2)
          = ({0, 1, 5} : Finset (Fin 6)) from by decide]
        exact h⟩
    · exact Or.inl ⟨1, by decide, 3, by decide, by
        rw [show insert (3 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 1)
          = ({0, 2, 3} : Finset (Fin 6)) from by decide]
        exact h⟩
    · exact Or.inl ⟨1, by decide, 4, by decide, by
        rw [show insert (4 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 1)
          = ({0, 2, 4} : Finset (Fin 6)) from by decide]
        exact h⟩
    · exact Or.inl ⟨1, by decide, 5, by decide, by
        rw [show insert (5 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 1)
          = ({0, 2, 5} : Finset (Fin 6)) from by decide]
        exact h⟩
    · exact Or.inr (Or.inl ⟨1, by decide, 2, by decide, 3, by decide, 4, by decide,
        by decide, by decide, by
          rw [show tightDoubleSwap ({0, 1, 2} : Finset (Fin 6)) 1 2 3 4
            = ({0, 3, 4} : Finset (Fin 6)) from by decide]
          exact h⟩)
    · exact Or.inr (Or.inl ⟨1, by decide, 2, by decide, 3, by decide, 5, by decide,
        by decide, by decide, by
          rw [show tightDoubleSwap ({0, 1, 2} : Finset (Fin 6)) 1 2 3 5
            = ({0, 3, 5} : Finset (Fin 6)) from by decide]
          exact h⟩)
    · exact Or.inr (Or.inl ⟨1, by decide, 2, by decide, 4, by decide, 5, by decide,
        by decide, by decide, by
          rw [show tightDoubleSwap ({0, 1, 2} : Finset (Fin 6)) 1 2 4 5
            = ({0, 4, 5} : Finset (Fin 6)) from by decide]
          exact h⟩)
    · exact Or.inl ⟨0, by decide, 3, by decide, by
        rw [show insert (3 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 0)
          = ({1, 2, 3} : Finset (Fin 6)) from by decide]
        exact h⟩
    · exact Or.inl ⟨0, by decide, 4, by decide, by
        rw [show insert (4 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 0)
          = ({1, 2, 4} : Finset (Fin 6)) from by decide]
        exact h⟩
    · exact Or.inl ⟨0, by decide, 5, by decide, by
        rw [show insert (5 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 0)
          = ({1, 2, 5} : Finset (Fin 6)) from by decide]
        exact h⟩
    · exact Or.inr (Or.inl ⟨0, by decide, 2, by decide, 3, by decide, 4, by decide,
        by decide, by decide, by
          rw [show tightDoubleSwap ({0, 1, 2} : Finset (Fin 6)) 0 2 3 4
            = ({1, 3, 4} : Finset (Fin 6)) from by decide]
          exact h⟩)
    · exact Or.inr (Or.inl ⟨0, by decide, 2, by decide, 3, by decide, 5, by decide,
        by decide, by decide, by
          rw [show tightDoubleSwap ({0, 1, 2} : Finset (Fin 6)) 0 2 3 5
            = ({1, 3, 5} : Finset (Fin 6)) from by decide]
          exact h⟩)
    · exact Or.inr (Or.inl ⟨0, by decide, 2, by decide, 4, by decide, 5, by decide,
        by decide, by decide, by
          rw [show tightDoubleSwap ({0, 1, 2} : Finset (Fin 6)) 0 2 4 5
            = ({1, 4, 5} : Finset (Fin 6)) from by decide]
          exact h⟩)
    · exact Or.inr (Or.inl ⟨0, by decide, 1, by decide, 3, by decide, 4, by decide,
        by decide, by decide, by
          rw [show tightDoubleSwap ({0, 1, 2} : Finset (Fin 6)) 0 1 3 4
            = ({2, 3, 4} : Finset (Fin 6)) from by decide]
          exact h⟩)
    · exact Or.inr (Or.inl ⟨0, by decide, 1, by decide, 3, by decide, 5, by decide,
        by decide, by decide, by
          rw [show tightDoubleSwap ({0, 1, 2} : Finset (Fin 6)) 0 1 3 5
            = ({2, 3, 5} : Finset (Fin 6)) from by decide]
          exact h⟩)
    · exact Or.inr (Or.inl ⟨0, by decide, 1, by decide, 4, by decide, 5, by decide,
        by decide, by decide, by
          rw [show tightDoubleSwap ({0, 1, 2} : Finset (Fin 6)) 0 1 4 5
            = ({2, 4, 5} : Finset (Fin 6)) from by decide]
          exact h⟩)
    · exact Or.inr (Or.inr h)
  · rintro (⟨swapOut, hmemOut, swapIn, hnotMemIn, hpos⟩ |
      ⟨outFirst, hmemFirst, outSecond, hmemSecond, inFirst, hnotFirst, inSecond,
        hnotSecond, houtDistinct, hinDistinct, hpos⟩ | hpos)
    · refine (exists_posDef_cardThree_iff_tightLineNineteenCandidate design htightNe
        htight).mp ⟨_, ?_, hpos⟩
      rw [card_tightSwap ({0, 1, 2} : Finset (Fin 6)) swapOut swapIn hmemOut hnotMemIn]
      decide
    · refine (exists_posDef_cardThree_iff_tightLineNineteenCandidate design htightNe
        htight).mp ⟨_, ?_, hpos⟩
      rw [card_tightDoubleSwap ({0, 1, 2} : Finset (Fin 6)) outFirst outSecond inFirst
        inSecond hmemFirst hmemSecond houtDistinct hnotFirst hnotSecond hinDistinct]
      decide
    · exact (exists_posDef_cardThree_iff_tightLineNineteenCandidate design htightNe
        htight).mp ⟨{3, 4, 5}, by decide, hpos⟩

/-- The tight-line branch restated as the three-family disjunction. -/
def TightLineThreeFamilySelector : Prop :=
  ∀ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    Dominates design ({0, 1, 2} : Finset (Fin 6)) →
    tightDir ≠ 0 →
    IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir →
    HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir →
      (TightLineOneSlotFamily design ∨ TightLineDoubleSwapFamily design
        ∨ TightLineComplementCandidate design)

/-- **The three-family reduction of the tight-line branch.**  Proving that every
tight-line antecedent has a strict one-slot swap, a strict distance-two
exchange, or a strict complement is exactly the branch — no candidate is lost
and none is added. -/
theorem uThreeSixTightLineBranch_iff_threeFamilySelector :
    UThreeSixTightLineBranch ↔ TightLineThreeFamilySelector := by
  constructor
  · intro hbranch design tightDir hlineFree hoffConic hdominates htightNe htight hline
    refine (tightLineNineteenCandidate_iff_tightLineThreeFamilies design htightNe
      htight).mp ?_
    exact (exists_posDef_cardThree_iff_tightLineNineteenCandidate design htightNe
      htight).mp
      (hbranch design tightDir hlineFree hoffConic hdominates htightNe htight hline)
  · intro hselector design tightDir hlineFree hoffConic hdominates htightNe htight hline
    refine (exists_posDef_cardThree_iff_tightLineNineteenCandidate design htightNe
      htight).mpr ?_
    refine (tightLineNineteenCandidate_iff_tightLineThreeFamilies design htightNe
      htight).mpr ?_
    exact hselector design tightDir hlineFree hoffConic hdominates htightNe htight hline

/-! ## Part 4: the live base pair of the tight line -/

/-- Tightness is preserved by rescaling the direction. -/
theorem isTightDirectionOf_smul {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hdominates : Dominates design selected)
    {direction : Fin rank → ℝ}
    (htight : IsTightDirectionOf design selected direction) (scale : ℝ) :
    IsTightDirectionOf design selected (scale • direction) := by
  have hcombination :=
    isTightDirectionOf_add_smul design selected hdominates htight htight scale 0
  simpa using hcombination

/-- The normalised tight direction is a tight direction. -/
theorem isTightDirectionOf_normalizedDirection {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (hdominates : Dominates design selected) {tightDir : Fin rank → ℝ}
    (htight : IsTightDirectionOf design selected tightDir) :
    IsTightDirectionOf design selected (normalizedDirection tightDir) := by
  rw [normalizedDirection]
  exact isTightDirectionOf_smul design selected hdominates htight _

/-- A one-dimensional tight space is one-dimensional after rescaling. -/
theorem hasTightLineAt_smul {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) {tightDir : Fin rank → ℝ}
    (hline : HasTightLineAt design selected tightDir) {scale : ℝ} (hscale : scale ≠ 0) :
    HasTightLineAt design selected (scale • tightDir) := by
  intro other hother
  obtain ⟨ratio, hratio⟩ := hline other hother
  refine ⟨ratio / scale, ?_⟩
  rw [hratio, smul_smul, div_mul_cancel₀ ratio hscale]

/-- The normalised tight direction spans the same line. -/
theorem hasTightLineAt_normalizedDirection {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    {tightDir : Fin rank → ℝ} (htightNe : tightDir ≠ 0)
    (hline : HasTightLineAt design selected tightDir) :
    HasTightLineAt design selected (normalizedDirection tightDir) := by
  have hnormPos : 0 < tightDir ⬝ᵥ tightDir := dotProduct_self_pos htightNe
  have hrootPos : 0 < Real.sqrt (tightDir ⬝ᵥ tightDir) := Real.sqrt_pos.mpr hnormPos
  rw [normalizedDirection]
  exact hasTightLineAt_smul design selected hline (inv_ne_zero (ne_of_gt hrootPos))

/-- **Transverse positivity of a tight-line gap.**  A semidefinite gap whose
tight space is one line is strictly positive on every nonzero vector orthogonal
to ANY vector that is itself transverse to the line.  This generalises
`Gtz.dominationGap_form_pos_of_hasTightLineAt`, which is the case where the
transverse vector is the tight direction itself. -/
theorem dominationGap_form_pos_of_hasTightLineAt_of_transverse
    {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (tightDir pivot probe : Fin rank → ℝ)
    (hdominates : Dominates design selected)
    (hline : HasTightLineAt design selected tightDir)
    (htransverse : pivot ⬝ᵥ tightDir ≠ 0)
    (hprobePivot : probe ⬝ᵥ pivot = 0) (hprobeNe : probe ≠ 0) :
    0 < probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) := by
  have hnonneg : 0 ≤ probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) := by
    have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
    simpa only [star_trivial] using hform
  apply lt_of_le_of_ne hnonneg
  intro hzeroReverse
  have hzero : probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) = 0 :=
    hzeroReverse.symm
  obtain ⟨ratio, hprobe⟩ := hline probe hzero
  have hratioZero : ratio = 0 := by
    rw [hprobe, smul_dotProduct, smul_eq_mul] at hprobePivot
    rcases mul_eq_zero.mp hprobePivot with hleft | hright
    · exact hleft
    · exact absurd (by rw [dotProduct_comm] at hright; exact hright) htransverse
  exact hprobeNe (by rw [hprobe, hratioZero, zero_smul])

/-- **The base pair opposite a transverse base atom is plane positive.**  On the
tight-line branch, if a base atom reads the tight direction nontrivially then the
gap of the two remaining base atoms is strictly positive on the whole plane
orthogonal to that atom.  This is the coordinate-free form of the numerically
observed base-pair liveness law: a card-two gap in rank three is negative
somewhere, so a plane-positive one has inertia `(2, 0, 1)`. -/
theorem basePairGap_form_pos_of_tightLine (design : WeightedDesign 6 3)
    (tightDir : Fin 3 → ℝ) (baseLabel : Fin 6)
    (hmem : baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hline : HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hreading : design.atom baseLabel ⬝ᵥ tightDir ≠ 0)
    (probe : Fin 3 → ℝ) (hprobePerp : probe ⬝ᵥ design.atom baseLabel = 0)
    (hprobeNe : probe ≠ 0) :
    0 < probe ⬝ᵥ ((subsetSum design ((({0, 1, 2} : Finset (Fin 6))).erase baseLabel)
      - 1) *ᵥ probe) := by
  have hbase : 0 < probe ⬝ᵥ ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ probe) :=
    dominationGap_form_pos_of_hasTightLineAt_of_transverse design
      ({0, 1, 2} : Finset (Fin 6)) tightDir (design.atom baseLabel) probe hdominates hline
      hreading hprobePerp hprobeNe
  have hsplit : subsetSum design ((({0, 1, 2} : Finset (Fin 6))).erase baseLabel) - 1
      = (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1)
        - atomMatrix (design.atom baseLabel) := by
    rw [subsetSum_erase design hmem]
    abel
  have hdropped : probe ⬝ᵥ (atomMatrix (design.atom baseLabel) *ᵥ probe) = 0 := by
    rw [dotProduct_atomMatrix_mulVec, dotProduct_comm, hprobePerp]
    norm_num
  rw [hsplit, Matrix.sub_mulVec, dotProduct_sub, hdropped, sub_zero]
  exact hbase

/-- Some base atom reads the tight direction nontrivially. -/
theorem exists_baseLabel_tightReading_ne_zero (design : WeightedDesign 6 3)
    {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    ∃ baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom baseLabel ⬝ᵥ tightDir ≠ 0 := by
  have hunit : normalizedDirection tightDir ⬝ᵥ normalizedDirection tightDir = 1 :=
    normalizedDirection_isUnit tightDir htightNe
  have htightUnit :
      IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) (normalizedDirection tightDir) :=
    isTightDirectionOf_normalizedDirection design ({0, 1, 2} : Finset (Fin 6)) hdominates htight
  have hsquares := tightDirection_squareReadings_eq_one design
    ({0, 1, 2} : Finset (Fin 6)) (normalizedDirection tightDir) hunit htightUnit
  have hsumNe :
      ∑ baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        (design.atom baseLabel ⬝ᵥ normalizedDirection tightDir) ^ 2 ≠ 0 := by
    rw [hsquares]
    norm_num
  obtain ⟨baseLabel, hmem, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumNe
  refine ⟨baseLabel, hmem, ?_⟩
  intro hzero
  apply hne
  rw [dotProduct_normalizedDirection_sq (design.atom baseLabel) tightDir htightNe, hzero]
  norm_num

/-- **The tight line always has a live base pair.**  Some base label reads the
tight direction nontrivially, and the gap of the two remaining base atoms is
then strictly positive on the whole plane orthogonal to that label's atom. -/
theorem exists_liveBasePair_planePositive_of_tightLine (design : WeightedDesign 6 3)
    {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    ∃ baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom baseLabel ⬝ᵥ tightDir ≠ 0 ∧
        ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ design.atom baseLabel = 0 → probe ≠ 0 →
          0 < probe ⬝ᵥ ((subsetSum design
            ((({0, 1, 2} : Finset (Fin 6))).erase baseLabel) - 1) *ᵥ probe) := by
  obtain ⟨baseLabel, hmem, hreading⟩ :=
    exists_baseLabel_tightReading_ne_zero design htightNe hdominates htight
  exact ⟨baseLabel, hmem, hreading, fun probe hperp hne =>
    basePairGap_form_pos_of_tightLine design tightDir baseLabel hmem hdominates hline
      hreading probe hperp hne⟩

/-! ## Part 5: the three families in their landed sign forms -/

/-- The one-slot family in the landed one-slot sign criterion: an incoming atom
out-reads the outgoing one along the tight direction, and the rank-one swap
square is beaten by the base gap's own planar form. -/
def TightLineOneSlotSignFamily (design : WeightedDesign 6 3)
    (unitTight : Fin 3 → ℝ) : Prop :=
  ∃ swapOut ∈ ({0, 1, 2} : Finset (Fin 6)), ∃ swapIn ∉ ({0, 1, 2} : Finset (Fin 6)),
    (design.atom swapOut ⬝ᵥ unitTight) ^ 2 < (design.atom swapIn ⬝ᵥ unitTight) ^ 2 ∧
      ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitTight = 0 → probe ≠ 0 →
        ((design.atom swapIn ⬝ᵥ unitTight) * (design.atom swapOut ⬝ᵥ probe)
            - (design.atom swapOut ⬝ᵥ unitTight) * (design.atom swapIn ⬝ᵥ probe)) ^ 2
          < ((design.atom swapIn ⬝ᵥ unitTight) ^ 2
              - (design.atom swapOut ⬝ᵥ unitTight) ^ 2)
            * (probe ⬝ᵥ ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ probe))

/-- The one-slot family and its sign form agree. -/
theorem tightLineOneSlotFamily_iff_signFamily (design : WeightedDesign 6 3)
    (unitTight : Fin 3 → ℝ)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hunit : unitTight ⬝ᵥ unitTight = 1)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) unitTight) :
    TightLineOneSlotFamily design ↔ TightLineOneSlotSignFamily design unitTight := by
  constructor
  · rintro ⟨swapOut, hmemOut, swapIn, hnotMemIn, hpos⟩
    exact ⟨swapOut, hmemOut, swapIn, hnotMemIn,
      (tightSwap_posDef_iff_surplus_and_gapExcess design ({0, 1, 2} : Finset (Fin 6))
        swapOut swapIn unitTight hmemOut hnotMemIn hdominates hunit htight).mp hpos⟩
  · rintro ⟨swapOut, hmemOut, swapIn, hnotMemIn, hsigns⟩
    exact ⟨swapOut, hmemOut, swapIn, hnotMemIn,
      (tightSwap_posDef_iff_surplus_and_gapExcess design ({0, 1, 2} : Finset (Fin 6))
        swapOut swapIn unitTight hmemOut hnotMemIn hdominates hunit htight).mpr hsigns⟩

/-- The distance-two family in the landed three-sign frame criterion. -/
def TightLineDoubleSwapSignFamily (design : WeightedDesign 6 3)
    (planeFirst planeSecond unitTight : Fin 3 → ℝ) : Prop :=
  ∃ outFirst ∈ ({0, 1, 2} : Finset (Fin 6)), ∃ outSecond ∈ ({0, 1, 2} : Finset (Fin 6)),
    ∃ inFirst ∉ ({0, 1, 2} : Finset (Fin 6)), ∃ inSecond ∉ ({0, 1, 2} : Finset (Fin 6)),
      outFirst ≠ outSecond ∧ inFirst ≠ inSecond ∧
        0 < tightDoubleSwapAlpha design outFirst outSecond inFirst inSecond unitTight ∧
          0 < tightDoubleSwapCover design ({0, 1, 2} : Finset (Fin 6)) outFirst outSecond
              inFirst inSecond unitTight planeFirst planeFirst ∧
            0 < tightDoubleSwapCover design ({0, 1, 2} : Finset (Fin 6)) outFirst
                  outSecond inFirst inSecond unitTight planeFirst planeFirst
                * tightDoubleSwapCover design ({0, 1, 2} : Finset (Fin 6)) outFirst
                    outSecond inFirst inSecond unitTight planeSecond planeSecond
              - tightDoubleSwapCover design ({0, 1, 2} : Finset (Fin 6)) outFirst
                  outSecond inFirst inSecond unitTight planeFirst planeSecond ^ 2

/-- The distance-two family and its sign form agree. -/
theorem tightLineDoubleSwapFamily_iff_signFamily (design : WeightedDesign 6 3)
    (planeFirst planeSecond unitTight : Fin 3 → ℝ)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfirstUnit : planeFirst ⬝ᵥ planeFirst = 1)
    (hsecondUnit : planeSecond ⬝ᵥ planeSecond = 1)
    (hunit : unitTight ⬝ᵥ unitTight = 1)
    (hfirstSecond : planeFirst ⬝ᵥ planeSecond = 0)
    (hfirstFlat : planeFirst ⬝ᵥ unitTight = 0)
    (hsecondFlat : planeSecond ⬝ᵥ unitTight = 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) unitTight) :
    TightLineDoubleSwapFamily design
      ↔ TightLineDoubleSwapSignFamily design planeFirst planeSecond unitTight := by
  constructor
  · rintro ⟨outFirst, hmemFirst, outSecond, hmemSecond, inFirst, hnotFirst, inSecond,
      hnotSecond, houtDistinct, hinDistinct, hpos⟩
    exact ⟨outFirst, hmemFirst, outSecond, hmemSecond, inFirst, hnotFirst, inSecond,
      hnotSecond, houtDistinct, hinDistinct,
      (tightDoubleSwap_posDef_iff_frameMinors design ({0, 1, 2} : Finset (Fin 6))
        outFirst outSecond inFirst inSecond planeFirst planeSecond unitTight hmemFirst
        hmemSecond houtDistinct hnotFirst hnotSecond hinDistinct hdominates hfirstUnit
        hsecondUnit hunit hfirstSecond hfirstFlat hsecondFlat htight).mp hpos⟩
  · rintro ⟨outFirst, hmemFirst, outSecond, hmemSecond, inFirst, hnotFirst, inSecond,
      hnotSecond, houtDistinct, hinDistinct, hsigns⟩
    exact ⟨outFirst, hmemFirst, outSecond, hmemSecond, inFirst, hnotFirst, inSecond,
      hnotSecond, houtDistinct, hinDistinct,
      (tightDoubleSwap_posDef_iff_frameMinors design ({0, 1, 2} : Finset (Fin 6))
        outFirst outSecond inFirst inSecond planeFirst planeSecond unitTight hmemFirst
        hmemSecond houtDistinct hnotFirst hnotSecond hinDistinct hdominates hfirstUnit
        hsecondUnit hunit hfirstSecond hfirstFlat hsecondFlat htight).mpr hsigns⟩

/-! ## Part 6: the complement candidate needs only two signs -/

/-- **The complement's normal surplus is free on the tight line.**  The
complement of a weak dominator strictly over-covers its tight direction, so the
first of the three frame signs is automatic and never has to be proved. -/
theorem complementGap_tightReading_surplus_pos_of_tightDirection
    (design : WeightedDesign 6 3) {unitTight : Fin 3 → ℝ}
    (hunit : unitTight ⬝ᵥ unitTight = 1)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) unitTight) :
    1 < ∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      (design.atom freeLabel ⬝ᵥ unitTight) ^ 2 := by
  have htightNe : unitTight ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    norm_num at hunit
  have hover := dominatorComplement_strictly_overcovers_tightDirection design
    ({0, 1, 2} : Finset (Fin 6)) unitTight (by decide) htightNe htight
  rw [show ((({0, 1, 2} : Finset (Fin 6)))ᶜ) = ({3, 4, 5} : Finset (Fin 6)) from by decide,
    hunit] at hover
  exact hover

/-- **The complement candidate is two signs, not three.**  Because the surplus
is automatic, strict domination by `{3, 4, 5}` on the tight-line branch is
decided by the cover form's diagonal entry and its two-by-two determinant. -/
theorem posDef_complementGap_iff_two_frameMinors_of_tightDirection
    (design : WeightedDesign 6 3) (planeFirst planeSecond unitTight : Fin 3 → ℝ)
    (hfirstUnit : planeFirst ⬝ᵥ planeFirst = 1)
    (hsecondUnit : planeSecond ⬝ᵥ planeSecond = 1)
    (hunit : unitTight ⬝ᵥ unitTight = 1)
    (hfirstSecond : planeFirst ⬝ᵥ planeSecond = 0)
    (hfirstFlat : planeFirst ⬝ᵥ unitTight = 0)
    (hsecondFlat : planeSecond ⬝ᵥ unitTight = 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) unitTight) :
    TightLineComplementCandidate design
      ↔ (0 < coverForm design ({3, 4, 5} : Finset (Fin 6)) unitTight planeFirst planeFirst
        ∧ 0 < coverForm design ({3, 4, 5} : Finset (Fin 6)) unitTight planeFirst planeFirst
              * coverForm design ({3, 4, 5} : Finset (Fin 6)) unitTight planeSecond
                planeSecond
            - coverForm design ({3, 4, 5} : Finset (Fin 6)) unitTight planeFirst
              planeSecond ^ 2) := by
  have hsurplus := complementGap_tightReading_surplus_pos_of_tightDirection design hunit htight
  have hcriterion := posDef_iff_surplus_and_frameMinors design
    ({3, 4, 5} : Finset (Fin 6)) planeFirst planeSecond unitTight hfirstUnit hsecondUnit
    hunit hfirstSecond hfirstFlat hsecondFlat
  constructor
  · intro hpos
    obtain ⟨_, hdiagonal, hdeterminant⟩ := hcriterion.mp hpos
    exact ⟨hdiagonal, hdeterminant⟩
  · rintro ⟨hdiagonal, hdeterminant⟩
    exact hcriterion.mpr ⟨hsurplus, hdiagonal, hdeterminant⟩

/-! ## Part 7: the sign-level three-family selector -/

/-- The three-family reduction with every disjunct written in its landed
quantifier-free sign form: two signs for a one-slot swap, three for a
distance-two exchange, two for the complement. -/
def TightLineThreeFamilySignSelector : Prop :=
  ∀ (design : WeightedDesign 6 3) (planeFirst planeSecond unitTight : Fin 3 → ℝ),
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    Dominates design ({0, 1, 2} : Finset (Fin 6)) →
    unitTight ⬝ᵥ unitTight = 1 →
    IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) unitTight →
    HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) unitTight →
    planeFirst ⬝ᵥ planeFirst = 1 →
    planeSecond ⬝ᵥ planeSecond = 1 →
    planeFirst ⬝ᵥ planeSecond = 0 →
    planeFirst ⬝ᵥ unitTight = 0 →
    planeSecond ⬝ᵥ unitTight = 0 →
      (TightLineOneSlotSignFamily design unitTight
        ∨ TightLineDoubleSwapSignFamily design planeFirst planeSecond unitTight
        ∨ (0 < coverForm design ({3, 4, 5} : Finset (Fin 6)) unitTight planeFirst
              planeFirst
            ∧ 0 < coverForm design ({3, 4, 5} : Finset (Fin 6)) unitTight planeFirst
                  planeFirst
                * coverForm design ({3, 4, 5} : Finset (Fin 6)) unitTight planeSecond
                  planeSecond
              - coverForm design ({3, 4, 5} : Finset (Fin 6)) unitTight planeFirst
                planeSecond ^ 2))

/-- **The tight-line branch from the sign-level three-family selector.**  The
tight direction is normalised and an orthonormal frame of its plane is built
from the landed planar-frame construction, so the selector may be stated with a
unit tight direction and a frame without loss. -/
theorem uThreeSixTightLineBranch_of_threeFamilySignSelector :
    TightLineThreeFamilySignSelector → UThreeSixTightLineBranch := by
  intro hselector design tightDir hlineFree hoffConic hdominates htightNe htight hline
  have hunit : normalizedDirection tightDir ⬝ᵥ normalizedDirection tightDir = 1 :=
    normalizedDirection_isUnit tightDir htightNe
  have htightUnit :
      IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) (normalizedDirection tightDir) :=
    isTightDirectionOf_normalizedDirection design ({0, 1, 2} : Finset (Fin 6)) hdominates htight
  have hlineUnit :
      HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) (normalizedDirection tightDir) :=
    hasTightLineAt_normalizedDirection design ({0, 1, 2} : Finset (Fin 6)) htightNe hline
  obtain ⟨planeFirst, planeSecond, hfirstUnit, hsecondUnit, hfirstSecond, hfirstFlat,
    hsecondFlat⟩ := exists_orthonormal_planarFrame hunit
  refine (exists_posDef_cardThree_iff_tightLineNineteenCandidate design htightNe htight).mpr ?_
  refine (tightLineNineteenCandidate_iff_tightLineThreeFamilies design htightNe htight).mpr ?_
  rcases hselector design planeFirst planeSecond (normalizedDirection tightDir) hlineFree
    hoffConic hdominates hunit htightUnit hlineUnit hfirstUnit hsecondUnit hfirstSecond
    hfirstFlat hsecondFlat with hone | htwo | hcomplement
  · exact Or.inl ((tightLineOneSlotFamily_iff_signFamily design
      (normalizedDirection tightDir) hdominates hunit htightUnit).mpr hone)
  · exact Or.inr (Or.inl ((tightLineDoubleSwapFamily_iff_signFamily design planeFirst
      planeSecond (normalizedDirection tightDir) hdominates hfirstUnit hsecondUnit hunit
      hfirstSecond hfirstFlat hsecondFlat htightUnit).mpr htwo))
  · exact Or.inr (Or.inr ((posDef_complementGap_iff_two_frameMinors_of_tightDirection design
      planeFirst planeSecond (normalizedDirection tightDir) hfirstUnit hsecondUnit hunit
      hfirstSecond hfirstFlat hsecondFlat htightUnit).mpr hcomplement))

/-! ## Part 8: the live base pair, packaged for a unit-axis plane criterion -/

/-- Orthogonality to a nonzero vector and to its normalisation are the same
condition. -/
theorem dotProduct_normalizedDirection_eq_zero_iff {rank : ℕ}
    (probe rawDir : Fin rank → ℝ) (hne : rawDir ≠ 0) :
    probe ⬝ᵥ normalizedDirection rawDir = 0 ↔ probe ⬝ᵥ rawDir = 0 := by
  have hnormPos : 0 < rawDir ⬝ᵥ rawDir := dotProduct_self_pos hne
  have hrootPos : 0 < Real.sqrt (rawDir ⬝ᵥ rawDir) := Real.sqrt_pos.mpr hnormPos
  rw [normalizedDirection, dotProduct_smul, smul_eq_mul, mul_eq_zero]
  constructor
  · rintro (hscale | hvalue)
    · exact absurd hscale (inv_ne_zero (ne_of_gt hrootPos))
    · exact hvalue
  · intro hvalue
    exact Or.inr hvalue

/-- Inserting an outside label keeps a plane-positive gap plane positive. -/
theorem insertGap_form_pos_of_form_pos (design : WeightedDesign 6 3)
    (base : Finset (Fin 6)) (added : Fin 6) (hnew : added ∉ base) (probe : Fin 3 → ℝ)
    (hbase : 0 < probe ⬝ᵥ ((subsetSum design base - 1) *ᵥ probe)) :
    0 < probe ⬝ᵥ ((subsetSum design (insert added base) - 1) *ᵥ probe) := by
  rw [subsetSum_insert_sub_one design hnew, Matrix.add_mulVec, dotProduct_add,
    dotProduct_atomMatrix_mulVec]
  nlinarith [sq_nonneg (design.atom added ⬝ᵥ probe), hbase]

/-- **The tight-line branch always supplies a live base label whose one-slot
swaps are all plane positive.**  Some base label reads the tight direction
nontrivially; its opposite base pair, and every one-slot swap obtained by adding
a free label to that pair, is strictly positive on the whole unit-axis plane
orthogonal to that base atom.  This is the exact input a hyperplane Sylvester
criterion consumes: on that plane the three one-slot gaps at the live base label
are decided by their determinant alone. -/
theorem exists_liveBaseLabel_oneSlot_planePositive_of_tightLine
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    ∃ baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)), ∃ axis : Fin 3 → ℝ,
      axis ⬝ᵥ axis = 1 ∧ design.atom baseLabel ⬝ᵥ tightDir ≠ 0
        ∧ (∀ probe : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → probe ≠ 0 →
            0 < probe ⬝ᵥ ((subsetSum design
              ((({0, 1, 2} : Finset (Fin 6))).erase baseLabel) - 1) *ᵥ probe))
        ∧ (∀ swapIn ∉ ({0, 1, 2} : Finset (Fin 6)), ∀ probe : Fin 3 → ℝ,
            probe ⬝ᵥ axis = 0 → probe ≠ 0 →
              0 < probe ⬝ᵥ ((subsetSum design (insert swapIn
                ((({0, 1, 2} : Finset (Fin 6))).erase baseLabel)) - 1) *ᵥ probe)) := by
  obtain ⟨baseLabel, hmem, hreading⟩ :=
    exists_baseLabel_tightReading_ne_zero design htightNe hdominates htight
  have hatomNe : design.atom baseLabel ≠ 0 := by
    intro hzero
    apply hreading
    rw [hzero, zero_dotProduct]
  have hpairPos : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ normalizedDirection (design.atom baseLabel) = 0 →
      probe ≠ 0 → 0 < probe ⬝ᵥ ((subsetSum design
        ((({0, 1, 2} : Finset (Fin 6))).erase baseLabel) - 1) *ᵥ probe) := by
    intro probe hperp hne
    exact basePairGap_form_pos_of_tightLine design tightDir baseLabel hmem hdominates hline
      hreading probe
      ((dotProduct_normalizedDirection_eq_zero_iff probe (design.atom baseLabel)
        hatomNe).mp hperp) hne
  refine ⟨baseLabel, hmem, normalizedDirection (design.atom baseLabel),
    normalizedDirection_isUnit (design.atom baseLabel) hatomNe, hreading, hpairPos, ?_⟩
  intro swapIn hnotMemIn probe hperp hne
  have hnotErase : swapIn ∉ (({0, 1, 2} : Finset (Fin 6))).erase baseLabel := fun hmemErase =>
    hnotMemIn (Finset.mem_of_mem_erase hmemErase)
  exact insertGap_form_pos_of_form_pos design
    ((({0, 1, 2} : Finset (Fin 6))).erase baseLabel) swapIn hnotErase probe
    (hpairPos probe hperp hne)

/-! ## Part 9: Sylvester after a hyperplane -/

/-- A symmetric form's quadratic value expanded in an orthonormal frame. -/
theorem quadForm_eq_frameExpansion {form : Matrix (Fin 3) (Fin 3) ℝ} (hsym : formᵀ = form)
    {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    (vec : Fin 3 → ℝ) :
    vec ⬝ᵥ (form *ᵥ vec)
      = (vec ⬝ᵥ pOne) ^ 2 * (pOne ⬝ᵥ (form *ᵥ pOne))
        + (vec ⬝ᵥ pTwo) ^ 2 * (pTwo ⬝ᵥ (form *ᵥ pTwo))
        + (vec ⬝ᵥ axis) ^ 2 * (axis ⬝ᵥ (form *ᵥ axis))
        + 2 * (vec ⬝ᵥ pOne) * (vec ⬝ᵥ pTwo) * (pOne ⬝ᵥ (form *ᵥ pTwo))
        + 2 * (vec ⬝ᵥ pOne) * (vec ⬝ᵥ axis) * (pOne ⬝ᵥ (form *ᵥ axis))
        + 2 * (vec ⬝ᵥ pTwo) * (vec ⬝ᵥ axis) * (pTwo ⬝ᵥ (form *ᵥ axis)) := by
  have hresolution := orthonormalFrame_resolution hOneOne hTwoTwo hAxisAxis hOneTwo
    hOneAxis hTwoAxis vec
  conv_lhs => rw [hresolution]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [symmPairing_comm hsym pTwo pOne, symmPairing_comm hsym axis pOne,
    symmPairing_comm hsym axis pTwo]
  ring

/-- **Sylvester after a hyperplane, in scalars.**  A real quadratic form in
three coordinates whose leading two-by-two block is positive definite and whose
determinant is positive is strictly positive at every nonzero coordinate triple.
The certificate is an explicit sum of three squares. -/
theorem quadForm_pos_of_planeBlock_pos_of_det_pos
    (cornerOne cross cornerTwo pairingOne pairingTwo cornerAxis
      coordOne coordTwo coordAxis : ℝ)
    (hcorner : 0 < cornerOne)
    (hminor : 0 < cornerOne * cornerTwo - cross ^ 2)
    (hdet : 0 < cornerOne * cornerTwo * cornerAxis - cornerOne * pairingTwo ^ 2
        - cross ^ 2 * cornerAxis + 2 * cross * pairingOne * pairingTwo
        - pairingOne ^ 2 * cornerTwo)
    (hnonzero : ¬ (coordOne = 0 ∧ coordTwo = 0 ∧ coordAxis = 0)) :
    0 < coordOne ^ 2 * cornerOne + coordTwo ^ 2 * cornerTwo + coordAxis ^ 2 * cornerAxis
        + 2 * coordOne * coordTwo * cross + 2 * coordOne * coordAxis * pairingOne
        + 2 * coordTwo * coordAxis * pairingTwo := by
  rcases eq_or_ne coordAxis 0 with haxisZero | haxisNe
  · subst haxisZero
    have hidentity : cornerOne * (coordOne ^ 2 * cornerOne + coordTwo ^ 2 * cornerTwo
          + (0 : ℝ) ^ 2 * cornerAxis + 2 * coordOne * coordTwo * cross
          + 2 * coordOne * 0 * pairingOne + 2 * coordTwo * 0 * pairingTwo)
        = (cornerOne * coordOne + cross * coordTwo) ^ 2
          + (cornerOne * cornerTwo - cross ^ 2) * coordTwo ^ 2 := by ring
    rcases eq_or_ne coordTwo 0 with htwoZero | htwoNe
    · have honeNe : coordOne ≠ 0 := by
        intro hzero
        exact hnonzero ⟨hzero, htwoZero, rfl⟩
      have hbaseNe : cornerOne * coordOne + cross * coordTwo ≠ 0 := by
        rw [htwoZero]
        simpa using mul_ne_zero (ne_of_gt hcorner) honeNe
      have hsquare : 0 < (cornerOne * coordOne + cross * coordTwo) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hbaseNe))
      nlinarith [hidentity, hsquare, sq_nonneg coordTwo]
    · have hsecond : 0 < (cornerOne * cornerTwo - cross ^ 2) * coordTwo ^ 2 := by
        have hsq : 0 < coordTwo ^ 2 := by positivity
        exact mul_pos hminor hsq
      nlinarith [hidentity, hsecond, sq_nonneg (cornerOne * coordOne + cross * coordTwo)]
  · have hidentity : cornerOne * (cornerOne * cornerTwo - cross ^ 2)
          * (coordOne ^ 2 * cornerOne + coordTwo ^ 2 * cornerTwo
            + coordAxis ^ 2 * cornerAxis + 2 * coordOne * coordTwo * cross
            + 2 * coordOne * coordAxis * pairingOne + 2 * coordTwo * coordAxis * pairingTwo)
        = (cornerOne * cornerTwo - cross ^ 2)
            * (cornerOne * coordOne + cross * coordTwo + pairingOne * coordAxis) ^ 2
          + ((cornerOne * cornerTwo - cross ^ 2) * coordTwo
              + (cornerOne * pairingTwo - cross * pairingOne) * coordAxis) ^ 2
          + cornerOne * (cornerOne * cornerTwo * cornerAxis - cornerOne * pairingTwo ^ 2
              - cross ^ 2 * cornerAxis + 2 * cross * pairingOne * pairingTwo
              - pairingOne ^ 2 * cornerTwo) * coordAxis ^ 2 := by ring
    have hthird : 0 < cornerOne * (cornerOne * cornerTwo * cornerAxis
        - cornerOne * pairingTwo ^ 2 - cross ^ 2 * cornerAxis
        + 2 * cross * pairingOne * pairingTwo - pairingOne ^ 2 * cornerTwo)
        * coordAxis ^ 2 := by
      have hsq : 0 < coordAxis ^ 2 := by positivity
      exact mul_pos (mul_pos hcorner hdet) hsq
    have hfirst : 0 ≤ (cornerOne * cornerTwo - cross ^ 2)
        * (cornerOne * coordOne + cross * coordTwo + pairingOne * coordAxis) ^ 2 :=
      mul_nonneg hminor.le (sq_nonneg _)
    have hsecond : 0 ≤ ((cornerOne * cornerTwo - cross ^ 2) * coordTwo
        + (cornerOne * pairingTwo - cross * pairingOne) * coordAxis) ^ 2 := sq_nonneg _
    nlinarith [hidentity, hfirst, hsecond, hthird, mul_pos hcorner hminor]

/-- **Plane positivity plus one determinant sign is positive definiteness.**  A
symmetric `3x3` form that is strictly positive on the plane orthogonal to a unit
axis is positive definite exactly when its determinant is positive.  No
eigenvalue theory and no congruence transport: the frame comes from the landed
planar-frame construction and the conclusion from the three-square certificate. -/
theorem posDef_of_unitAxisPlanePositive_of_det_pos {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {axis : Fin 3 → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (hplanePos : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → probe ≠ 0 →
      0 < probe ⬝ᵥ (form *ᵥ probe))
    (hdet : 0 < form.det) : form.PosDef := by
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩ :=
    exists_orthonormal_planarFrame hunit
  have hOneNe : pOne ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hOneOne
    norm_num at hOneOne
  have hcorner : 0 < pOne ⬝ᵥ (form *ᵥ pOne) := hplanePos pOne hOneAxis hOneNe
  have hTwoOne : pTwo ⬝ᵥ pOne = 0 := by rw [dotProduct_comm]; exact hOneTwo
  have hminor : 0 < (pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ pTwo))
      - (pOne ⬝ᵥ (form *ᵥ pTwo)) ^ 2 := by
    set probe : Fin 3 → ℝ :=
      (-(pOne ⬝ᵥ (form *ᵥ pTwo))) • pOne + (pOne ⬝ᵥ (form *ᵥ pOne)) • pTwo with hprobeDef
    have hprobeOne : probe ⬝ᵥ pOne = -(pOne ⬝ᵥ (form *ᵥ pTwo)) := by
      rw [hprobeDef, add_dotProduct, smul_dotProduct, smul_dotProduct, hOneOne, hTwoOne]
      ring
    have hprobeTwo : probe ⬝ᵥ pTwo = pOne ⬝ᵥ (form *ᵥ pOne) := by
      rw [hprobeDef, add_dotProduct, smul_dotProduct, smul_dotProduct, hOneTwo, hTwoTwo]
      ring
    have hprobeAxis : probe ⬝ᵥ axis = 0 := by
      rw [hprobeDef, add_dotProduct, smul_dotProduct, smul_dotProduct, hOneAxis, hTwoAxis]
      ring
    have hprobeNe : probe ≠ 0 := by
      intro hzero
      rw [hzero, zero_dotProduct] at hprobeTwo
      exact absurd hprobeTwo.symm (ne_of_gt hcorner)
    have hvalue := hplanePos probe hprobeAxis hprobeNe
    rw [quadForm_eq_frameExpansion hsym hOneOne hTwoTwo hunit hOneTwo hOneAxis hTwoAxis probe,
      hprobeOne, hprobeTwo, hprobeAxis] at hvalue
    nlinarith [hvalue, hcorner]
  have hdetFrame := det_eq_framePairing_det hsym hOneOne hTwoTwo hunit hOneTwo hOneAxis hTwoAxis
  have hdetScalar : 0 < (pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ pTwo))
        * (axis ⬝ᵥ (form *ᵥ axis))
      - (pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ axis)) ^ 2
      - (pOne ⬝ᵥ (form *ᵥ pTwo)) ^ 2 * (axis ⬝ᵥ (form *ᵥ axis))
      + 2 * (pOne ⬝ᵥ (form *ᵥ pTwo)) * (pOne ⬝ᵥ (form *ᵥ axis)) * (pTwo ⬝ᵥ (form *ᵥ axis))
      - (pOne ⬝ᵥ (form *ᵥ axis)) ^ 2 * (pTwo ⬝ᵥ (form *ᵥ pTwo)) := by
    rw [hdetFrame] at hdet
    nlinarith [hdet]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_of_transpose_eq hsym, ?_⟩
  intro vec hvecNe
  rw [star_trivial,
    quadForm_eq_frameExpansion hsym hOneOne hTwoTwo hunit hOneTwo hOneAxis hTwoAxis vec]
  refine quadForm_pos_of_planeBlock_pos_of_det_pos _ _ _ _ _ _ _ _ _ hcorner hminor
    hdetScalar ?_
  rintro ⟨hone, htwo, haxis⟩
  apply hvecNe
  rw [orthonormalFrame_resolution hOneOne hTwoTwo hunit hOneTwo hOneAxis hTwoAxis vec,
    hone, htwo, haxis]
  simp

/-- The plane-positive criterion as an equivalence. -/
theorem posDef_iff_det_pos_of_unitAxisPlanePositive {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {axis : Fin 3 → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (hplanePos : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → probe ≠ 0 →
      0 < probe ⬝ᵥ (form *ᵥ probe)) :
    form.PosDef ↔ 0 < form.det :=
  ⟨fun hposDef => hposDef.det_pos,
    fun hdet => posDef_of_unitAxisPlanePositive_of_det_pos hsym hunit hplanePos hdet⟩

/-! ## Part 10: the one-slot swaps at the live base label are one sign -/

/-- **At the live base label every one-slot swap costs a single determinant
sign.**  Combining the tight-line base-pair plane positivity with the hyperplane
Sylvester criterion: for the base label whose atom reads the tight direction
nontrivially, each of the three one-slot swaps strictly dominates if and only if
its gap determinant is positive.  This is the tight-line analogue of the
plane-branch one-determinant reduction, in the original coordinates of the
design. -/
theorem exists_liveBaseLabel_oneSlot_posDef_iff_det_pos_of_tightLine
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    ∃ baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom baseLabel ⬝ᵥ tightDir ≠ 0 ∧
        ∀ swapIn ∉ ({0, 1, 2} : Finset (Fin 6)),
          ((subsetSum design (insert swapIn
              ((({0, 1, 2} : Finset (Fin 6))).erase baseLabel)) - 1).PosDef
            ↔ 0 < (subsetSum design (insert swapIn
              ((({0, 1, 2} : Finset (Fin 6))).erase baseLabel)) - 1).det) := by
  obtain ⟨baseLabel, hmem, axis, haxisUnit, hreading, _hpairPos, hswapPos⟩ :=
    exists_liveBaseLabel_oneSlot_planePositive_of_tightLine design htightNe hdominates
      htight hline
  refine ⟨baseLabel, hmem, hreading, ?_⟩
  intro swapIn hnotMemIn
  exact posDef_iff_det_pos_of_unitAxisPlanePositive
    (transpose_subsetSum_sub_one design
      (insert swapIn ((({0, 1, 2} : Finset (Fin 6))).erase baseLabel)))
    haxisUnit (fun probe hperp hne => hswapPos swapIn hnotMemIn probe hperp hne)

/-- A single strict one-slot swap already discharges the nineteen-candidate
disjunction. -/
theorem tightLineNineteenCandidate_of_oneSlotGap_posDef
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    {swapOut swapIn : Fin 6} (hmemOut : swapOut ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hnotMemIn : swapIn ∉ ({0, 1, 2} : Finset (Fin 6)))
    (hpos : (subsetSum design (insert swapIn
      ((({0, 1, 2} : Finset (Fin 6))).erase swapOut)) - 1).PosDef) :
    TightLineNineteenCandidate design :=
  (tightLineNineteenCandidate_iff_tightLineThreeFamilies design htightNe htight).mpr
    (Or.inl ⟨swapOut, hmemOut, swapIn, hnotMemIn, hpos⟩)

/-! ## Part 11: the antecedent region is inhabited -/

/-- **Non-vacuity guard.**  The landed `U(3,6)` stratum witness is line-free,
off-conic, weakly dominated by its base triple, not strictly dominated by it,
and its tight space is exactly one line — so every hypothesis bundle in this
file is satisfiable — and its nineteen-candidate disjunction genuinely fires,
through the complement. -/
theorem exists_tightLineBranch_antecedent_witness :
    ∃ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))
        ∧ HasNoCommonQuadric design.atom
        ∧ Dominates design ({0, 1, 2} : Finset (Fin 6))
        ∧ tightDir ≠ 0
        ∧ IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir
        ∧ HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir
        ∧ ¬ (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef
        ∧ TightLineComplementCandidate design
        ∧ TightLineNineteenCandidate design := by
  refine ⟨uThreeSixStratumDesign, uThreeSixStratumTightDirection,
    uThreeSixStratumDesign_hasLinePattern, uThreeSixStratumDesign_hasNoCommonQuadric,
    uThreeSixStratumDesign_dominates_baseTriple, uThreeSixStratumTightDirection_ne_zero,
    uThreeSixStratumDesign_tightDirection_isTight, uThreeSixStratumDesign_hasTightLineAt,
    uThreeSixStratumDesign_not_posDef_baseTripleGap,
    uThreeSixStratumDesign_posDef_complementTripleGap, ?_⟩
  exact (tightLineNineteenCandidate_iff_tightLineThreeFamilies uThreeSixStratumDesign
    uThreeSixStratumTightDirection_ne_zero
    uThreeSixStratumDesign_tightDirection_isTight).mpr
    (Or.inr (Or.inr uThreeSixStratumDesign_posDef_complementTripleGap))


/-! ## Part 12: plane positivity and live pairs -/

theorem frameDeterminant_negativeDirection_identity
    (blockOne cross blockTwo pairingOne pairingTwo cornerAxis
      coordOne coordTwo coordAxis : ℝ) :
    (blockOne * blockTwo - cross ^ 2) * (blockOne * blockTwo - cross ^ 2)
        * (coordOne ^ 2 * blockOne + coordTwo ^ 2 * blockTwo + coordAxis ^ 2 * cornerAxis
          + 2 * coordOne * coordTwo * cross + 2 * coordOne * coordAxis * pairingOne
          + 2 * coordTwo * coordAxis * pairingTwo)
      = blockOne * ((blockOne * blockTwo - cross ^ 2) * coordOne
            + (blockTwo * pairingOne - cross * pairingTwo) * coordAxis) ^ 2
        + 2 * cross * ((blockOne * blockTwo - cross ^ 2) * coordOne
              + (blockTwo * pairingOne - cross * pairingTwo) * coordAxis)
            * ((blockOne * blockTwo - cross ^ 2) * coordTwo
              + (blockOne * pairingTwo - cross * pairingOne) * coordAxis)
        + blockTwo * ((blockOne * blockTwo - cross ^ 2) * coordTwo
            + (blockOne * pairingTwo - cross * pairingOne) * coordAxis) ^ 2
        + (blockOne * blockTwo - cross ^ 2)
            * (blockOne * (blockTwo * cornerAxis - pairingTwo ^ 2)
              - cross * (cross * cornerAxis - pairingTwo * pairingOne)
              + pairingOne * (cross * pairingTwo - blockTwo * pairingOne))
            * coordAxis ^ 2 := by
  ring

theorem planeBlock_leading_pos_of_planePositive {form : Matrix (Fin 3) (Fin 3) ℝ}
    {pOne axis : Fin 3 → ℝ} (hOneOne : pOne ⬝ᵥ pOne = 1) (hOneAxis : pOne ⬝ᵥ axis = 0)
    (hplanePos : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → probe ≠ 0 →
      0 < probe ⬝ᵥ (form *ᵥ probe)) :
    0 < pOne ⬝ᵥ (form *ᵥ pOne) := by
  refine hplanePos pOne hOneAxis ?_
  intro hzero
  rw [hzero, dotProduct_zero] at hOneOne
  norm_num at hOneOne

theorem planeBlock_minor_pos_of_planePositive {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1) (hAxisAxis : axis ⬝ᵥ axis = 1)
    (hOneTwo : pOne ⬝ᵥ pTwo = 0) (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    (hplanePos : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → probe ≠ 0 →
      0 < probe ⬝ᵥ (form *ᵥ probe)) :
    0 < (pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ pTwo))
      - (pOne ⬝ᵥ (form *ᵥ pTwo)) ^ 2 := by
  have hcorner : 0 < pOne ⬝ᵥ (form *ᵥ pOne) :=
    planeBlock_leading_pos_of_planePositive hOneOne hOneAxis hplanePos
  have hTwoOne : pTwo ⬝ᵥ pOne = 0 := by rw [dotProduct_comm]; exact hOneTwo
  set probe : Fin 3 → ℝ :=
    (-(pOne ⬝ᵥ (form *ᵥ pTwo))) • pOne + (pOne ⬝ᵥ (form *ᵥ pOne)) • pTwo with hprobeDef
  have hprobeOne : probe ⬝ᵥ pOne = -(pOne ⬝ᵥ (form *ᵥ pTwo)) := by
    rw [hprobeDef, add_dotProduct, smul_dotProduct, smul_dotProduct, hOneOne, hTwoOne]
    ring
  have hprobeTwo : probe ⬝ᵥ pTwo = pOne ⬝ᵥ (form *ᵥ pOne) := by
    rw [hprobeDef, add_dotProduct, smul_dotProduct, smul_dotProduct, hOneTwo, hTwoTwo]
    ring
  have hprobeAxis : probe ⬝ᵥ axis = 0 := by
    rw [hprobeDef, add_dotProduct, smul_dotProduct, smul_dotProduct, hOneAxis, hTwoAxis]
    ring
  have hprobeNe : probe ≠ 0 := by
    intro hzero
    rw [hzero, zero_dotProduct] at hprobeTwo
    exact absurd hprobeTwo.symm (ne_of_gt hcorner)
  have hvalue := hplanePos probe hprobeAxis hprobeNe
  rw [quadForm_eq_frameExpansion hsym hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis hTwoAxis probe,
    hprobeOne, hprobeTwo, hprobeAxis] at hvalue
  nlinarith [hvalue, hcorner]

/-- **A plane-positive form with one strictly negative direction has negative
determinant.**  Sylvester's law of inertia in the only case this campaign needs,
proved by an explicit polynomial identity rather than by eigenvalues.  Only the
unit axis is demanded: the orthonormal frame of its plane is constructed from the
landed planar-frame lemma rather than required from the caller. -/
theorem det_neg_of_unitAxisPlanePositive_of_negativeDirection {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {axis : Fin 3 → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (hplanePos : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → probe ≠ 0 →
      0 < probe ⬝ᵥ (form *ᵥ probe))
    {negative : Fin 3 → ℝ} (hnegative : negative ⬝ᵥ (form *ᵥ negative) < 0) :
    form.det < 0 := by
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩ :=
    exists_orthonormal_planarFrame hunit
  have hcorner : 0 < pOne ⬝ᵥ (form *ᵥ pOne) :=
    planeBlock_leading_pos_of_planePositive hOneOne hOneAxis hplanePos
  have hminor : 0 < (pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ pTwo))
      - (pOne ⬝ᵥ (form *ᵥ pTwo)) ^ 2 :=
    planeBlock_minor_pos_of_planePositive hsym hOneOne hTwoTwo hunit hOneTwo hOneAxis hTwoAxis
      hplanePos
  have hnegativeNe : negative ≠ 0 := by
    intro hzero
    rw [hzero, Matrix.mulVec_zero, dotProduct_zero] at hnegative
    exact absurd hnegative (lt_irrefl 0)
  have haxisCoord : negative ⬝ᵥ axis ≠ 0 := by
    intro hzero
    exact absurd (hplanePos negative hzero hnegativeNe) (not_lt.mpr hnegative.le)
  have hkey : ((pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ pTwo))
          - (pOne ⬝ᵥ (form *ᵥ pTwo)) ^ 2)
        * ((pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ pTwo))
          - (pOne ⬝ᵥ (form *ᵥ pTwo)) ^ 2)
        * (negative ⬝ᵥ (form *ᵥ negative))
      = (pOne ⬝ᵥ (form *ᵥ pOne))
          * (((pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ pTwo))
                - (pOne ⬝ᵥ (form *ᵥ pTwo)) ^ 2) * (negative ⬝ᵥ pOne)
            + ((pTwo ⬝ᵥ (form *ᵥ pTwo)) * (pOne ⬝ᵥ (form *ᵥ axis))
                - (pOne ⬝ᵥ (form *ᵥ pTwo)) * (pTwo ⬝ᵥ (form *ᵥ axis)))
              * (negative ⬝ᵥ axis)) ^ 2
        + 2 * (pOne ⬝ᵥ (form *ᵥ pTwo))
            * (((pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ pTwo))
                  - (pOne ⬝ᵥ (form *ᵥ pTwo)) ^ 2) * (negative ⬝ᵥ pOne)
              + ((pTwo ⬝ᵥ (form *ᵥ pTwo)) * (pOne ⬝ᵥ (form *ᵥ axis))
                  - (pOne ⬝ᵥ (form *ᵥ pTwo)) * (pTwo ⬝ᵥ (form *ᵥ axis)))
                * (negative ⬝ᵥ axis))
            * (((pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ pTwo))
                  - (pOne ⬝ᵥ (form *ᵥ pTwo)) ^ 2) * (negative ⬝ᵥ pTwo)
              + ((pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ axis))
                  - (pOne ⬝ᵥ (form *ᵥ pTwo)) * (pOne ⬝ᵥ (form *ᵥ axis)))
                * (negative ⬝ᵥ axis))
        + (pTwo ⬝ᵥ (form *ᵥ pTwo))
            * (((pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ pTwo))
                  - (pOne ⬝ᵥ (form *ᵥ pTwo)) ^ 2) * (negative ⬝ᵥ pTwo)
              + ((pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ axis))
                  - (pOne ⬝ᵥ (form *ᵥ pTwo)) * (pOne ⬝ᵥ (form *ᵥ axis)))
                * (negative ⬝ᵥ axis)) ^ 2
        + ((pOne ⬝ᵥ (form *ᵥ pOne)) * (pTwo ⬝ᵥ (form *ᵥ pTwo))
            - (pOne ⬝ᵥ (form *ᵥ pTwo)) ^ 2) * form.det * (negative ⬝ᵥ axis) ^ 2 := by
    rw [quadForm_eq_frameExpansion hsym hOneOne hTwoTwo hunit hOneTwo hOneAxis hTwoAxis negative,
      det_eq_framePairing_det hsym hOneOne hTwoTwo hunit hOneTwo hOneAxis hTwoAxis]
    ring
  set blockOne := pOne ⬝ᵥ (form *ᵥ pOne)
  set blockTwo := pTwo ⬝ᵥ (form *ᵥ pTwo)
  set cross := pOne ⬝ᵥ (form *ᵥ pTwo)
  set minor := blockOne * blockTwo - cross ^ 2
  set firstSquare := minor * (negative ⬝ᵥ pOne)
      + (blockTwo * (pOne ⬝ᵥ (form *ᵥ axis)) - cross * (pTwo ⬝ᵥ (form *ᵥ axis)))
        * (negative ⬝ᵥ axis)
  set secondSquare := minor * (negative ⬝ᵥ pTwo)
      + (blockOne * (pTwo ⬝ᵥ (form *ᵥ axis)) - cross * (pOne ⬝ᵥ (form *ᵥ axis)))
        * (negative ⬝ᵥ axis)
  have hquadNonneg : 0 ≤ blockOne * firstSquare ^ 2 + 2 * cross * firstSquare * secondSquare
      + blockTwo * secondSquare ^ 2 := by
    nlinarith [sq_nonneg (blockOne * firstSquare + cross * secondSquare), sq_nonneg secondSquare,
      hcorner, hminor, mul_pos hcorner hminor]
  have haxisSquarePos : 0 < (negative ⬝ᵥ axis) ^ 2 := by positivity
  have hleftNeg : minor * minor * (negative ⬝ᵥ (form *ᵥ negative)) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hminor hminor) hnegative
  have hdetTerm : minor * form.det * (negative ⬝ᵥ axis) ^ 2 < 0 := by
    nlinarith [hkey, hquadNonneg, hleftNeg]
  nlinarith [hdetTerm, hminor, haxisSquarePos, mul_pos hminor haxisSquarePos]

/-! ## Part 13: the pair gap, its determinant and its normal -/

/-- Two vectors in three-space always share a nonzero normal. -/
theorem exists_pairNormal_ne_zero (leftVec rightVec : Fin 3 → ℝ) :
    ∃ normal : Fin 3 → ℝ, normal ≠ 0 ∧ leftVec ⬝ᵥ normal = 0 ∧ rightVec ⬝ᵥ normal = 0 := by
  classical
  have hdet : (Matrix.of ![leftVec, rightVec, (0 : Fin 3 → ℝ)]).det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero 2 (fun col => by simp)
  obtain ⟨kernelVec, hne, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨kernelVec, hne, ?_, ?_⟩
  · have hrow := congrFun hzero 0
    simpa [Matrix.mulVec, Matrix.of_apply] using hrow
  · have hrow := congrFun hzero 1
    simpa [Matrix.mulVec, Matrix.of_apply] using hrow

/-- **The pair gap determinant is minus the pair gap minor.**  Sylvester's
identity for `A_i + A_j - 1` against the two-by-two Gram gap, in the tree's own
`pairGapExcessOf` vocabulary. -/
theorem det_pairGap_eq_neg_pairGapExcessOf {m : ℕ} (design : WeightedDesign m 3)
    {pairFirst pairSecond : Fin m} (hdistinct : pairFirst ≠ pairSecond) :
    (subsetSum design {pairFirst, pairSecond} - 1).det
      = -pairGapExcessOf design pairFirst pairSecond := by
  rw [subsetSum, Finset.sum_pair hdistinct,
    det_pair_matrix_eq_neg_pairGram (design.atom pairFirst) (design.atom pairSecond)]
  rw [pairGapExcessOf, gapExcessOf, gapExcessOf, gapPairingOf, leverageOf_eq_dotProduct,
    leverageOf_eq_dotProduct, Matrix.det_fin_two]
  simp only [pairGram, Matrix.sub_apply, Matrix.one_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.of_apply, Fin.reduceEq, reduceIte]
  rw [dotProduct_comm (design.atom pairSecond) (design.atom pairFirst)]
  ring

/-- The pair gap is strictly negative along any common normal of the pair. -/
theorem pairGap_form_neg_of_pairNormal {m : ℕ} (design : WeightedDesign m 3)
    {pairFirst pairSecond : Fin m} (hdistinct : pairFirst ≠ pairSecond)
    {normal : Fin 3 → ℝ} (hnormalNe : normal ≠ 0)
    (hfirst : design.atom pairFirst ⬝ᵥ normal = 0)
    (hsecond : design.atom pairSecond ⬝ᵥ normal = 0) :
    normal ⬝ᵥ ((subsetSum design {pairFirst, pairSecond} - 1) *ᵥ normal) < 0 := by
  have hform := dotProduct_subsetSum_mulVec_of_finset design
    ({pairFirst, pairSecond} : Finset (Fin m)) normal
  rw [Finset.sum_pair hdistinct, hfirst, hsecond] at hform
  have hselfPos : 0 < normal ⬝ᵥ normal := dotProduct_self_pos hnormalNe
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hform]
  nlinarith [hselfPos]

/-- **PLANE POSITIVITY IS LIVENESS.**  If the gap of a pair of atoms of a
rank-three design is strictly positive on the plane orthogonal to some unit axis,
the pair is live.  The axis is arbitrary: liveness does not depend on which plane
exhibits the positivity, because a pair gap has a canonical negative direction --
any common normal of the two atoms -- and inertia does the rest.  This is the
converse of the landed `Gtz.pos_gapForm_pair_of_isLivePair`. -/
theorem isLivePair_of_planePositive_pairGap {m : ℕ} (design : WeightedDesign m 3)
    {pairFirst pairSecond : Fin m} (hdistinct : pairFirst ≠ pairSecond)
    {axis : Fin 3 → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (hplanePos : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → probe ≠ 0 →
      0 < probe ⬝ᵥ ((subsetSum design {pairFirst, pairSecond} - 1) *ᵥ probe)) :
    IsLivePair design pairFirst pairSecond := by
  obtain ⟨normal, hnormalNe, hfirstNormal, hsecondNormal⟩ :=
    exists_pairNormal_ne_zero (design.atom pairFirst) (design.atom pairSecond)
  have hdetNeg : (subsetSum design {pairFirst, pairSecond} - 1).det < 0 :=
    det_neg_of_unitAxisPlanePositive_of_negativeDirection
      (transpose_subsetSum_sub_one design ({pairFirst, pairSecond} : Finset (Fin m)))
      hunit hplanePos
      (pairGap_form_neg_of_pairNormal design hdistinct hnormalNe hfirstNormal hsecondNormal)
  have hminorPos : 0 < pairGapExcessOf design pairFirst pairSecond := by
    rw [det_pairGap_eq_neg_pairGapExcessOf design hdistinct] at hdetNeg
    linarith
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩ :=
    exists_orthonormal_planarFrame hunit
  have hOneNe : pOne ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hOneOne
    norm_num at hOneOne
  have hTwoNe : pTwo ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hTwoTwo
    norm_num at hTwoTwo
  have hpairForm : ∀ probe : Fin 3 → ℝ,
      probe ⬝ᵥ ((subsetSum design {pairFirst, pairSecond} - 1) *ᵥ probe)
        = (design.atom pairFirst ⬝ᵥ probe) ^ 2 + (design.atom pairSecond ⬝ᵥ probe) ^ 2
          - probe ⬝ᵥ probe := by
    intro probe
    have hform := dotProduct_subsetSum_mulVec_of_finset design
      ({pairFirst, pairSecond} : Finset (Fin m)) probe
    rw [Finset.sum_pair hdistinct] at hform
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hform]
  have hOneValue := hplanePos pOne hOneAxis hOneNe
  have hTwoValue := hplanePos pTwo hTwoAxis hTwoNe
  rw [hpairForm pOne, hOneOne] at hOneValue
  rw [hpairForm pTwo, hTwoTwo] at hTwoValue
  have hfirstSplit := dotProduct_eq_frameCoordinateSum hOneOne hTwoTwo hunit hOneTwo hOneAxis
    hTwoAxis (design.atom pairFirst) (design.atom pairFirst)
  have hsecondSplit := dotProduct_eq_frameCoordinateSum hOneOne hTwoTwo hunit hOneTwo hOneAxis
    hTwoAxis (design.atom pairSecond) (design.atom pairSecond)
  have hsumExcess : 0 < gapExcessOf design pairFirst + gapExcessOf design pairSecond := by
    rw [gapExcessOf, gapExcessOf, leverageOf_eq_dotProduct, leverageOf_eq_dotProduct,
      hfirstSplit, hsecondSplit]
    have hfirstOne : design.atom pairFirst ⬝ᵥ pOne = pOne ⬝ᵥ design.atom pairFirst :=
      dotProduct_comm _ _
    have hfirstTwo : design.atom pairFirst ⬝ᵥ pTwo = pTwo ⬝ᵥ design.atom pairFirst :=
      dotProduct_comm _ _
    have hsecondOne : design.atom pairSecond ⬝ᵥ pOne = pOne ⬝ᵥ design.atom pairSecond :=
      dotProduct_comm _ _
    have hsecondTwo : design.atom pairSecond ⬝ᵥ pTwo = pTwo ⬝ᵥ design.atom pairSecond :=
      dotProduct_comm _ _
    nlinarith [hOneValue, hTwoValue, sq_nonneg (design.atom pairFirst ⬝ᵥ axis),
      sq_nonneg (design.atom pairSecond ⬝ᵥ axis)]
  refine ⟨?_, ?_, hminorPos⟩
  · rw [pairGapExcessOf] at hminorPos
    nlinarith [hminorPos, hsumExcess, sq_nonneg (gapPairingOf design pairFirst pairSecond)]
  · rw [pairGapExcessOf] at hminorPos
    nlinarith [hminorPos, hsumExcess, sq_nonneg (gapPairingOf design pairFirst pairSecond)]

/-- **THE DICTIONARY.**  For a pair of atoms of a rank-three design, liveness and
plane positivity of the pair gap are the same condition.  The forward direction is
the landed `Gtz.pos_gapForm_pair_of_isLivePair` read at the pair's own unit cross
axis; the backward direction is the inertia argument above, and it does not care
which plane exhibits the positivity. -/
theorem isLivePair_iff_planePositive_pairGap {m : ℕ} (design : WeightedDesign m 3)
    {pairFirst pairSecond : Fin m} (hdistinct : pairFirst ≠ pairSecond) :
    IsLivePair design pairFirst pairSecond
      ↔ ∃ axis : Fin 3 → ℝ, axis ⬝ᵥ axis = 1 ∧
          ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → probe ≠ 0 →
            0 < probe ⬝ᵥ ((subsetSum design {pairFirst, pairSecond} - 1) *ᵥ probe) := by
  constructor
  · intro hlive
    have hbudgetPos : 0 < crossAxisBudget design pairFirst pairSecond :=
      pos_crossAxisBudget_of_isLivePair design hlive
    have hrootPos : 0 < Real.sqrt (crossAxisBudget design pairFirst pairSecond) :=
      Real.sqrt_pos.mpr hbudgetPos
    refine ⟨unitCrossAxis design pairFirst pairSecond,
      unitCrossAxis_dotProduct_self design hlive, fun probe hperp hne => ?_⟩
    refine pos_gapForm_pair_of_isLivePair design hlive hdistinct ?_ hne
    rw [unitCrossAxis, dotProduct_smul, smul_eq_mul, mul_eq_zero] at hperp
    exact hperp.resolve_left (inv_ne_zero (ne_of_gt hrootPos))
  · rintro ⟨axis, hunit, hplanePos⟩
    exact isLivePair_of_planePositive_pairGap design hdistinct hunit hplanePos

/-! ## Part 14: the tight line's canonical live pair -/

/-- **The base pair opposite a transverse base label is live.**  On the tight-line
branch the two base atoms other than one that reads the tight direction form a
live pair, so the whole landed live-pair machinery applies to them. -/
theorem isLivePair_basePair_of_tightLine_of_transverse (design : WeightedDesign 6 3)
    (tightDir : Fin 3 → ℝ) (retained first second : Fin 6)
    (hmem : retained ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hpair : ({first, second} : Finset (Fin 6)) = (({0, 1, 2} : Finset (Fin 6)).erase retained))
    (hdistinct : first ≠ second)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hline : HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hreading : design.atom retained ⬝ᵥ tightDir ≠ 0) :
    IsLivePair design first second := by
  have hatomNe : design.atom retained ≠ 0 := by
    intro hzero
    apply hreading
    rw [hzero, zero_dotProduct]
  refine isLivePair_of_planePositive_pairGap design hdistinct
    (normalizedDirection_isUnit (design.atom retained) hatomNe) ?_
  intro probe hperp hne
  rw [hpair]
  exact basePairGap_form_pos_of_tightLine design tightDir retained hmem hdominates hline hreading
    probe ((dotProduct_normalizedDirection_eq_zero_iff probe (design.atom retained)
      hatomNe).mp hperp) hne

/-- **Every tight-line antecedent owns a live base pair.**  Some base label reads
the tight direction nontrivially, and the other two base labels are then a live
pair -- named explicitly, so the landed one-determinant reduction can be applied
to them. -/
theorem exists_isLivePair_baseTriplePair_of_tightLine (design : WeightedDesign 6 3)
    {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    ∃ retained first second : Fin 6, retained ∈ ({0, 1, 2} : Finset (Fin 6))
      ∧ ({first, second} : Finset (Fin 6)) = (({0, 1, 2} : Finset (Fin 6)).erase retained)
      ∧ first ≠ second ∧ design.atom retained ⬝ᵥ tightDir ≠ 0
      ∧ IsLivePair design first second := by
  obtain ⟨retained, hmem, hreading⟩ :=
    exists_baseLabel_tightReading_ne_zero design htightNe hdominates htight
  rcases baseLabel_eq_of_mem_baseTriple hmem with rfl | rfl | rfl
  · exact ⟨0, 1, 2, hmem, by decide, by decide, hreading,
      isLivePair_basePair_of_tightLine_of_transverse design tightDir 0 1 2 hmem (by decide)
        (by decide) hdominates hline hreading⟩
  · exact ⟨1, 0, 2, hmem, by decide, by decide, hreading,
      isLivePair_basePair_of_tightLine_of_transverse design tightDir 1 0 2 hmem (by decide)
        (by decide) hdominates hline hreading⟩
  · exact ⟨2, 0, 1, hmem, by decide, by decide, hreading,
      isLivePair_basePair_of_tightLine_of_transverse design tightDir 2 0 1 hmem (by decide)
        (by decide) hdominates hline hreading⟩

/-! ## Part 15: one tie sign per candidate at a live pair -/

/-- **A live pair reduces every completion to one tie sign.**  Assembled from the
landed cross-axis atlas: strict domination by a triple whose leading pair is live
is exactly positivity of the triple's discriminant tie leg. -/
theorem posDef_gap_iff_pos_discriminantTie_of_isLivePair {size : ℕ}
    (design : WeightedDesign size 3) {pairFirst pairSecond thirdLabel : Fin size}
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hlive : IsLivePair design pairFirst pairSecond) :
    (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).PosDef
      ↔ 0 < discriminantTie design pairFirst pairSecond thirdLabel := by
  rw [posDef_tripleGap_iff_isLivePair_and_pos_liftMargin_unitCrossAxis design hFirstSecond
      hFirstThird hSecondThird,
    pos_liftMargin_unitCrossAxis_iff_pos_det design thirdLabel hlive, det_tripleGapMatrix]
  exact ⟨fun hboth => hboth.2, fun htie => ⟨hlive, htie⟩⟩

/-- **Every one-slot swap at a transverse base label is one tie sign.**  This is
the universal form: it holds at every base label that reads the tight direction,
not merely at one produced by an existential. -/
theorem oneSlotGap_posDef_iff_pos_discriminantTie_of_tightLine (design : WeightedDesign 6 3)
    (tightDir : Fin 3 → ℝ) (retained first second swapIn : Fin 6)
    (hmem : retained ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hpair : ({first, second} : Finset (Fin 6)) = (({0, 1, 2} : Finset (Fin 6)).erase retained))
    (hdistinct : first ≠ second) (hfirstIn : first ≠ swapIn) (hsecondIn : second ≠ swapIn)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hline : HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hreading : design.atom retained ⬝ᵥ tightDir ≠ 0) :
    (subsetSum design (insert swapIn ((({0, 1, 2} : Finset (Fin 6))).erase retained)) - 1).PosDef
      ↔ 0 < discriminantTie design first second swapIn := by
  classical
  have hlive := isLivePair_basePair_of_tightLine_of_transverse design tightDir retained first
    second hmem hpair hdistinct hdominates hline hreading
  have hset : insert swapIn ((({0, 1, 2} : Finset (Fin 6))).erase retained)
      = ({first, second, swapIn} : Finset (Fin 6)) := by
    rw [← hpair]
    ext label
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hset]
  exact posDef_gap_iff_pos_discriminantTie_of_isLivePair design hdistinct hfirstIn hsecondIn hlive

/-! ## Part 16: pruning the nineteen by the tight reading -/

/-- **The tight-reading pruning test.**  A subset whose atoms do not out-read the
tight direction cannot dominate strictly: the gap's value at the tight direction
is the reading surplus, so a nonpositive surplus refutes strictness outright.  No
frame, no minors, no cardinality assumption. -/
theorem not_posDef_gap_of_tightReading_sum_le_one {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    {unitTight : Fin rank → ℝ} (hunit : unitTight ⬝ᵥ unitTight = 1)
    (hsum : ∑ label ∈ selected, (design.atom label ⬝ᵥ unitTight) ^ 2 ≤ 1) :
    ¬ (subsetSum design selected - 1).PosDef := by
  intro hposDef
  have hne : unitTight ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    norm_num at hunit
  have hvalue := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hne
  rw [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_subsetSum_mulVec_of_finset, hunit] at hvalue
  linarith

/-- **The first pruning of the tight-line nineteen.**  A one-slot swap whose
incoming atom does not strictly out-read the outgoing one along the tight
direction is never a strict dominator. -/
theorem tightSwap_not_posDef_of_tightReading_le {size : ℕ} (design : WeightedDesign size 3)
    (dominator : Finset (Fin size)) (swapOut swapIn : Fin size) (unitTight : Fin 3 → ℝ)
    (hmemOut : swapOut ∈ dominator) (hnotMemIn : swapIn ∉ dominator)
    (hdominates : Dominates design dominator) (hunit : unitTight ⬝ᵥ unitTight = 1)
    (htight : IsTightDirectionOf design dominator unitTight)
    (hle : (design.atom swapIn ⬝ᵥ unitTight) ^ 2 ≤ (design.atom swapOut ⬝ᵥ unitTight) ^ 2) :
    ¬ (subsetSum design (insert swapIn (dominator.erase swapOut)) - 1).PosDef := by
  intro hposDef
  have hcriterion := (tightSwap_posDef_iff_surplus_and_gapExcess design dominator swapOut swapIn
    unitTight hmemOut hnotMemIn hdominates hunit htight).mp hposDef
  linarith [hcriterion.1]

/-- **One free atom out-reads every base atom.**  The landed uniform corner, at
weight floor zero: on the tight-line branch some free label beats all three base
labels in the tight reading at once, so the surplus sign of the one-slot criterion
is simultaneously satisfiable at all three base labels. -/
theorem exists_freeLabel_outreads_every_baseLabel (design : WeightedDesign 6 3)
    {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    ∃ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      ∀ baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        (design.atom baseLabel ⬝ᵥ tightDir) ^ 2
          < (design.atom freeLabel ⬝ᵥ tightDir) ^ 2 := by
  obtain ⟨freeLabel, hmem, hall⟩ := uThreeSix_exists_complementAtom_uniform_tightSwapCorner
    design tightDir htightNe htight 0 (fun label _ => (design.weight_pos label).le)
  refine ⟨freeLabel, hmem, fun baseLabel hbase => ?_⟩
  have hcorner := hall baseLabel hbase
  linarith

/-! ## Part 18: the refusal set -/

/-- **The refusal set of the one-determinant reduction.**  Every ordered triple
either fails to have a live leading pair or has a nonpositive tie leg.  Both
disjuncts are explicit polynomial sign conditions in the design's Gram data. -/
def LivePairTieRefusal {size : ℕ} (design : WeightedDesign size 3) : Prop :=
  ∀ pivotLabel pairFirst pairSecond : Fin size,
    pivotLabel ≠ pairFirst → pivotLabel ≠ pairSecond → pairFirst ≠ pairSecond →
      ¬ IsLivePair design pivotLabel pairFirst
        ∨ discriminantTie design pivotLabel pairFirst pairSecond ≤ 0

/-- **Failure is exactly the refusal set.**  At any rank-three design, having no
strictly dominating triple at all is the explicit semialgebraic refusal. -/
theorem not_exists_posDef_cardThree_iff_livePairTieRefusal {size : ℕ}
    (design : WeightedDesign size 3) :
    (¬ ∃ selected : Finset (Fin size), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef)
      ↔ LivePairTieRefusal design := by
  rw [← hasLivePairPositiveTie_iff_exists_posDef_cardThree design, HasLivePairPositiveTie]
  constructor
  · intro hno pivotLabel pairFirst pairSecond hpivotFirst hpivotSecond hpairDistinct
    by_contra hcontra
    push Not at hcontra
    exact hno ⟨pivotLabel, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
      hcontra.1, hcontra.2⟩
  · rintro hrefusal ⟨pivotLabel, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
      hlive, htie⟩
    rcases hrefusal pivotLabel pairFirst pairSecond hpivotFirst hpivotSecond hpairDistinct with
      hnotLive | hnonpos
    · exact hnotLive hlive
    · linarith

/-- **The tight-line branch's own refusal set.**  Failure of the nineteen-way
disjunction at a tight-line antecedent is exactly the refusal above -- the
line-branch analogue of `Gtz.PlaneBranchAxisFailureWitness`, but stated in the
design's own Gram alphabet with no normal form and no transport. -/
theorem not_tightLineNineteenCandidate_iff_livePairTieRefusal (design : WeightedDesign 6 3)
    {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    ¬ TightLineNineteenCandidate design ↔ LivePairTieRefusal design := by
  rw [← exists_posDef_cardThree_iff_tightLineNineteenCandidate design htightNe htight]
  exact not_exists_posDef_cardThree_iff_livePairTieRefusal design

/-- **A NECESSARY CONDITION AT THE CANONICAL LIVE BASE PAIR.**  If the
nineteen-way disjunction fails at a tight-line antecedent, then at the canonical
live base pair every completing label has a nonpositive tie leg.  Four explicit
polynomial signs at one named pair.  NOT a characterization of failure, and NOT
a target to contradict: the conclusion is satisfied at designs where the branch
HOLDS, because a strict triple may use only ONE base label and then says nothing
about the base pair's own tie legs.  The genuine failure characterization is the
equivalence `not_tightLineNineteenCandidate_iff_livePairTieRefusal`, whose
`LivePairTieRefusal` quantifies over ALL pairs rather than this one. -/
theorem exists_liveBasePair_all_discriminantTie_nonpos_of_not_nineteenCandidate
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hfail : ¬ TightLineNineteenCandidate design) :
    ∃ retained first second : Fin 6, retained ∈ ({0, 1, 2} : Finset (Fin 6))
      ∧ ({first, second} : Finset (Fin 6)) = (({0, 1, 2} : Finset (Fin 6)).erase retained)
      ∧ first ≠ second ∧ IsLivePair design first second
      ∧ ∀ third : Fin 6, first ≠ third → second ≠ third →
          discriminantTie design first second third ≤ 0 := by
  obtain ⟨retained, first, second, hmem, hpair, hdistinct, _hreading, hlive⟩ :=
    exists_isLivePair_baseTriplePair_of_tightLine design htightNe hdominates htight hline
  have hrefusal := (not_tightLineNineteenCandidate_iff_livePairTieRefusal design htightNe
    htight).mp hfail
  refine ⟨retained, first, second, hmem, hpair, hdistinct, hlive, fun third hfirst hsecond => ?_⟩
  rcases hrefusal first second third hdistinct hfirst hsecond with hnotLive | hnonpos
  · exact absurd hlive hnotLive
  · exact hnonpos

/-! ## Part 19: the branch as a live-pair tie statement -/

/-- The tight-line branch in the landed one-determinant vocabulary. -/
def TightLineLivePairTieSelector : Prop :=
  ∀ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    Dominates design ({0, 1, 2} : Finset (Fin 6)) →
    tightDir ≠ 0 →
    IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir →
    HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir →
      HasLivePairPositiveTie design

/-- **The tight-line branch IS a live-pair tie statement.**  Nineteen positive
definiteness tests, three families and forty-seven frame signs all collapse to the
landed one-determinant predicate: some pair is live and some completing label has
a positive tie leg. -/
theorem uThreeSixTightLineBranch_iff_livePairTieSelector :
    UThreeSixTightLineBranch ↔ TightLineLivePairTieSelector := by
  constructor
  · intro hbranch design tightDir hlineFree hoffConic hdominates htightNe htight hline
    exact (hasLivePairPositiveTie_iff_exists_posDef_cardThree design).mpr
      (hbranch design tightDir hlineFree hoffConic hdominates htightNe htight hline)
  · intro hselector design tightDir hlineFree hoffConic hdominates htightNe htight hline
    exact (hasLivePairPositiveTie_iff_exists_posDef_cardThree design).mp
      (hselector design tightDir hlineFree hoffConic hdominates htightNe htight hline)

/-! ## Part 20: the new predicates are not vacuous -/

/-- The landed stratum witness carries a live base pair, so the canonical live
pair of the tight-line branch is a real object. -/
theorem exists_isLivePair_baseTriplePair_uThreeSixStratumDesign :
    ∃ retained first second : Fin 6, retained ∈ ({0, 1, 2} : Finset (Fin 6))
      ∧ ({first, second} : Finset (Fin 6)) = (({0, 1, 2} : Finset (Fin 6)).erase retained)
      ∧ first ≠ second
      ∧ uThreeSixStratumDesign.atom retained ⬝ᵥ uThreeSixStratumTightDirection ≠ 0
      ∧ IsLivePair uThreeSixStratumDesign first second :=
  exists_isLivePair_baseTriplePair_of_tightLine uThreeSixStratumDesign
    uThreeSixStratumTightDirection_ne_zero uThreeSixStratumDesign_dominates_baseTriple
    uThreeSixStratumDesign_tightDirection_isTight uThreeSixStratumDesign_hasTightLineAt

/-- **The refusal set is a genuine constraint.**  It fails at the landed stratum
witness, so `Gtz.LivePairTieRefusal` is not vacuously true on the tight-line
antecedent region. -/
theorem not_livePairTieRefusal_uThreeSixStratumDesign :
    ¬ LivePairTieRefusal uThreeSixStratumDesign := by
  intro hrefusal
  exact ((not_exists_posDef_cardThree_iff_livePairTieRefusal uThreeSixStratumDesign).mpr hrefusal)
    ⟨{3, 4, 5}, by decide, uThreeSixStratumDesign_posDef_complementTripleGap⟩

/-! ## Part 21: what a distance-two candidate costs -/

/-- Rotating a three-element insert chain. -/
theorem tripleInsert_rotate {alpha : Type*} [DecidableEq alpha]
    (firstElem secondElem thirdElem : alpha) :
    ({firstElem, secondElem, thirdElem} : Finset alpha) = {secondElem, thirdElem, firstElem} := by
  ext element
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **A strict distance-two candidate forces its free pair to be live.**  So the
nine distance-two candidates and the complement are all dead unless some free pair
is live, and when one is, each of its four completions costs a single tie sign. -/
theorem isLivePair_freePair_of_posDef_distanceTwoGap {size : ℕ} (design : WeightedDesign size 3)
    (retained first second : Fin size) (hdistinct : first ≠ second)
    (hfirstRetained : first ≠ retained) (hsecondRetained : second ≠ retained)
    (hposDef : (subsetSum design {retained, first, second} - 1).PosDef) :
    IsLivePair design first second := by
  refine isLivePair_of_posDef_tripleGap design hdistinct hfirstRetained hsecondRetained ?_
  rwa [tripleInsert_rotate retained first second] at hposDef

/-- A base label and a free label are never equal. -/
theorem baseLabel_ne_freeLabel_of_memBaseTriple {baseLabel freeLabel : Fin 6}
    (hbase : baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hfree : freeLabel ∈ ({3, 4, 5} : Finset (Fin 6))) : baseLabel ≠ freeLabel := by
  revert hbase hfree
  revert baseLabel freeLabel
  decide

/-- **THE SHARPEST NECESSARY CONDITION AT THE CANONICAL LIVE BASE PAIR.**  If the
branch fails at a tight-line antecedent then, at the canonically named live base
pair, the tie leg of every one of the three free labels is nonpositive.  Three
explicit polynomial signs at one named pair.  As with the four-leg form above
this is a one-way implication and NOT a target to contradict -- its conclusion
holds at designs whose branch is true. -/
theorem exists_liveBasePair_freeTie_nonpos_of_not_nineteenCandidate
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hfail : ¬ TightLineNineteenCandidate design) :
    ∃ retained first second : Fin 6, retained ∈ ({0, 1, 2} : Finset (Fin 6))
      ∧ ({first, second} : Finset (Fin 6)) = (({0, 1, 2} : Finset (Fin 6)).erase retained)
      ∧ first ≠ second ∧ IsLivePair design first second
      ∧ ∀ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
          discriminantTie design first second freeLabel ≤ 0 := by
  obtain ⟨retained, first, second, hmem, hpair, hdistinct, hlive, hall⟩ :=
    exists_liveBasePair_all_discriminantTie_nonpos_of_not_nineteenCandidate design htightNe
      hdominates htight hline hfail
  have hfirstBase : first ∈ ({0, 1, 2} : Finset (Fin 6)) := by
    have hmemPair : first ∈ ({first, second} : Finset (Fin 6)) :=
      Finset.mem_insert_self first {second}
    rw [hpair] at hmemPair
    exact Finset.mem_of_mem_erase hmemPair
  have hsecondBase : second ∈ ({0, 1, 2} : Finset (Fin 6)) := by
    have hmemPair : second ∈ ({first, second} : Finset (Fin 6)) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self second)
    rw [hpair] at hmemPair
    exact Finset.mem_of_mem_erase hmemPair
  refine ⟨retained, first, second, hmem, hpair, hdistinct, hlive, fun freeLabel hfree => ?_⟩
  exact hall freeLabel (baseLabel_ne_freeLabel_of_memBaseTriple hfirstBase hfree)
    (baseLabel_ne_freeLabel_of_memBaseTriple hsecondBase hfree)

end Gtz
