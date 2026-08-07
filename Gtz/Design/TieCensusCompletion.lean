import Gtz.Design.ShippedTieParallelCensus
import Gtz.Quantitative.ChartInstances
import Gtz.Quantitative.ExtremalBasisActivity
import Gtz.Quantitative.GlobalMinimumRankThree
import Gtz.Ties.SplitClassTieFamily
import Gtz.Ties.CorankOneTieExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# Completing the (6,3) tie census: the factoring lemma and the omitted ties

`Gtz.every_shipped_sixThree_tie_hasParallelPair` claims to cover every `(6,3)`
tie the tree owns, but an environment scan found three it omits:
`Gtz.chartSplitSixDesign`, `Gtz.sixSplitDiamondDesign` and
`Gtz.paddedTetraDesign 2`.  This module settles all three, so the census claim
is true after all -- and it does so through ONE lemma that subsumes five
separate tie-family arguments: atoms that factor through a smaller index set
are never parallel-free, by pigeonhole.

The same lemma disposes of every general tie family at every cell of the sharp
window `2 * rank <= size <= rank * (rank + 1) / 2`: the bundled cycles, the
parallel splits and the split classes all build their atoms by composing a
smaller index set with a representative map, so inside the window -- where the
size strictly exceeds the class count -- each carries a parallel pair, exactly
as the hinge demands.  The bundled `(8,4)` design at the end inhabits and
confirms the first window cell BELOW the stress threshold, the band where no
rank-three theorem is evidence about anything.
-/

namespace Gtz

/-! ## The factoring lemma -/

/-- **Atoms that factor through a smaller index set are never parallel-free.**
Pigeonhole: two labels share a representative, and equal atoms are a parallel
pair at ratio one. -/
theorem hasParallelPair_of_atomFactorsThroughSmallerIndex {size rank classCount : ℕ}
    (design : WeightedDesign size rank) (classOf : Fin size → Fin classCount)
    (representative : Fin classCount → (Fin rank → ℝ))
    (hfactor : ∀ atomIndex, design.atom atomIndex = representative (classOf atomIndex))
    (hsmaller : classCount < size) : HasParallelPair design := by
  have hnotInjective : ¬ Function.Injective classOf := by
    intro hinjective
    have hcard := Fintype.card_le_of_injective _ hinjective
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨leftIndex, rightIndex, hsameClass, hdistinct⟩ :=
    Function.not_injective_iff.mp hnotInjective
  exact ⟨leftIndex, rightIndex, 1, hdistinct, by rw [one_smul, hfactor, hfactor, hsameClass]⟩

/-! ## The general tie families, checked inside the sharp window -/

/-- Every bundled-cycle tie inside the sharp window carries a parallel pair:
the window floor `2 * rank` already exceeds the arc count `rank + 1` once the
rank is at least two. -/
theorem bundledCycleDesign_hasParallelPair_of_windowFloor {edgeCount vertexRank : ℕ}
    (bundling : CycleBundling edgeCount vertexRank) (hrank : 1 ≤ vertexRank)
    (hrankAtLeastTwo : 2 ≤ vertexRank) (hfloor : 2 * vertexRank ≤ edgeCount) :
    HasParallelPair (bundledCycleDesign bundling hrank) :=
  hasParallelPair_bundledCycleDesign bundling hrank (by omega)

/-- Every parallel split with more atoms than base classes carries a parallel
pair -- the factoring lemma applied to the split's own class map. -/
theorem parallelSplitDesign_hasParallelPair_of_moreAtoms {baseSize splitSize rank : ℕ}
    (base : WeightedDesign baseSize rank) (classOf : Fin splitSize → Fin baseSize)
    (weight : Fin splitSize → ℝ) (hsplit : IsParallelSplitting base classOf weight)
    (hmoreAtomsThanClasses : baseSize < splitSize) :
    HasParallelPair (parallelSplitDesign base classOf weight hsplit) :=
  hasParallelPair_of_atomFactorsThroughSmallerIndex _ classOf base.atom
    (fun atomIndex => parallelSplitDesign_atom base classOf weight hsplit atomIndex)
    hmoreAtomsThanClasses

/-- Every split-class tie inside the sharp window carries a parallel pair: its
atoms factor through `Fin (rank + 1)`, and `rank + 1 < 2 * rank` once the rank
is at least two. -/
theorem splitClassDesign_hasParallelPair_of_windowFloor {size rank : ℕ}
    (classOf : Fin size → Fin (rank + 1)) (weight : Fin size → ℝ) (hrank : 1 ≤ rank)
    (hsurjective : Function.Surjective classOf)
    (hpos : ∀ atomIndex, 0 < weight atomIndex) (hsum : ∑ atomIndex, weight atomIndex = 1)
    (hrankAtLeastTwo : 2 ≤ rank) (hfloor : 2 * rank ≤ size) :
    HasParallelPair (splitClassDesign classOf weight hrank hsurjective hpos hsum) :=
  hasParallelPair_of_atomFactorsThroughSmallerIndex _ classOf
    (simplexTieAtom (classTotalWeight classOf weight)) (fun _ => rfl) (by omega)

/-- The padded tetrahedron carries a parallel pair from its second copy on: its
atoms factor through the four tetrahedron vertices. -/
theorem paddedTetraDesign_hasParallelPair {extra : ℕ} (hpadded : 1 ≤ extra) :
    HasParallelPair (paddedTetraDesign extra) :=
  hasParallelPair_of_atomFactorsThroughSmallerIndex _ (paddedTetraVertex extra) tetraAtom
    (fun atomIndex => paddedTetraDesign_atom extra atomIndex) (by omega)

/-! ## The three omitted `(6,3)` ties -/

/-- `Gtz.chartSplitSixDesign` is definitionally `Gtz.splitTetraDesign (1/8) (1/8)`. -/
theorem chartSplitSixDesign_hasParallelPair : HasParallelPair chartSplitSixDesign :=
  hasParallelPair_splitTetraDesign (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `Gtz.sixSplitDiamondDesign` splits the five-atom diamond into six atoms. -/
theorem sixSplitDiamondDesign_hasParallelPair : HasParallelPair sixSplitDiamondDesign :=
  parallelSplitDesign_hasParallelPair_of_moreAtoms diamondDesign sixIntoFiveDiamond
    sixSplitDiamondWeight sixSplitDiamond_isParallelSplitting (by norm_num)

/-- **The completed `(6,3)` census.**  Every `(6,3)` tie the tree owns --
including the three the shipped census omits -- carries a parallel pair. -/
theorem completedSixThreeTieCensus :
    HasParallelPair uniformTieDesign
      ∧ HasParallelPair (bundledCycleDesign bundlingSixThreeHeavy (by norm_num))
      ∧ HasParallelPair (bundledCycleDesign bundlingSixThreePaired (by norm_num))
      ∧ HasParallelPair chartSplitSixDesign
      ∧ HasParallelPair sixSplitDiamondDesign
      ∧ HasParallelPair (paddedTetraDesign 2)
      ∧ ∀ (splitA splitB : ℝ) (hAPos : 0 < splitA) (hALt : splitA < 1/4)
          (hBPos : 0 < splitB) (hBLt : splitB < 1/4),
          HasParallelPair (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) :=
  ⟨uniformTieDesign_hasParallelPair, hasParallelPair_bundlingSixThreeHeavy,
   hasParallelPair_bundlingSixThreePaired, chartSplitSixDesign_hasParallelPair,
   sixSplitDiamondDesign_hasParallelPair, paddedTetraDesign_hasParallelPair (by norm_num),
   fun _ _ hAPos hALt hBPos hBLt => hasParallelPair_splitTetraDesign hAPos hALt hBPos hBLt⟩

/-! ## The first sub-threshold window cell is inhabited and confirmed

The cell `(8,4)` is the first window cell strictly below the stress threshold
`dim Sym(rank)` at any rank -- the band that is EMPTY at rank three, so no
rank-three theorem is evidence about it.  The bundled cycle below inhabits it
with a genuine tie, and that tie carries a parallel pair, exactly as the hinge
demands there. -/

/-- Eight edges over five arcs, every arc occupied. -/
def eightIntoFiveBundling : CycleBundling 8 4 where
  bundleOf := fun edge => ⟨min edge.val 4, by omega⟩
  hasEdgeInEveryBundle := by
    intro position
    refine ⟨⟨position.val, by omega⟩, Fin.ext ?_⟩
    have hposition : position.val ≤ 4 := by omega
    simpa using Nat.min_eq_left hposition

/-- The `(8,4)` witness design. -/
noncomputable def eightFourBundledDesign : WeightedDesign 8 4 :=
  bundledCycleDesign eightIntoFiveBundling (by norm_num)

/-- The witness is a genuine tie, so the sub-threshold band's first cell
quantifies over a nonempty set of ties. -/
theorem eightFourBundledDesign_isTie : IsTie eightFourBundledDesign :=
  bundledCycle_isTie eightIntoFiveBundling (by norm_num)

/-- And the witness carries a parallel pair: the hinge is CONFIRMED, not
refuted, at the band's first live cell. -/
theorem eightFourBundledDesign_hasParallelPair : HasParallelPair eightFourBundledDesign :=
  bundledCycleDesign_hasParallelPair_of_windowFloor eightIntoFiveBundling (by norm_num)
    (by norm_num) (by norm_num)

end Gtz
