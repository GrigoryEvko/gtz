/-
# Parallel status of the shipped `(6,3)` ties

`Gtz.HingeHoldsAtSize 6 3` says every `(6,3)` tie carries a parallel pair.  Its
evidence base is the tree's own catalogue of ties, and until now that catalogue
was only partly checked: `Gtz.uniformTieDesign_hasParallelPair` was shipped, the
bundled cycle's status was recorded nowhere, and the split tetrahedron's only "by
construction".  This module closes the census.

The bundled cycle falls to PIGEONHOLE, at every size and rank at once.  The
bundle map lands in `Fin (vertexRank + 1)`, so above that many edges it cannot be
injective, and `Gtz.bundledCycle_atom_eq_of_sameBundle` turns a repeated bundle
into EQUAL atoms — not merely parallel, so the ratio is `1`.

R6: the tree's only general parallel theorem for graphic designs,
`Gtz.graphicRankThree_hasParallelPair`, carries the hypothesis `6 < edgeCount`
and so does NOT reach the `(6,3)` instances; nothing else covers them.

The conclusion is `Gtz.every_shipped_sixThree_tie_hasParallelPair`: not one
`(6,3)` tie the tree owns escapes the hinge.  That is evidence for the hinge, not
a proof of it — a design refuting it would have to be a tie the catalogue does
not contain.
-/
import Mathlib
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.EqualityLocus
import Gtz.Quantitative.UniformWeightTie
import Gtz.Reduction.SplitTransfer
import Gtz.Ties.SplitTetrahedronTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz


/-- **The bundled-cycle design has a parallel pair whenever it has more edges than
arcs.**  Two edges of one arc carry EQUAL atoms, so the ratio is `1`. -/
theorem hasParallelPair_bundledCycleDesign {edgeCount vertexRank : ℕ}
    (bundling : CycleBundling edgeCount vertexRank) (hrank : 1 ≤ vertexRank)
    (hmoreEdgesThanArcs : vertexRank + 1 < edgeCount) :
    HasParallelPair (bundledCycleDesign bundling hrank) := by
  have hnotInjective : ¬ Function.Injective bundling.bundleOf := by
    intro hinjective
    have hcard := Fintype.card_le_of_injective _ hinjective
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨leftEdge, rightEdge, hsame, hdistinct⟩ := Function.not_injective_iff.mp hnotInjective
  exact ⟨leftEdge, rightEdge, 1, hdistinct, by
    rw [one_smul]; exact bundledCycle_atom_eq_of_sameBundle bundling hrank hsame.symm⟩

/-- The `(6,3)` bundled cycle with arc sizes `(3,1,1,1)` — an exact tie
(`Gtz.bundlingSixThreeHeavy_isTie`) — carries a parallel pair. -/
theorem hasParallelPair_bundlingSixThreeHeavy :
    HasParallelPair (bundledCycleDesign bundlingSixThreeHeavy (by norm_num)) :=
  hasParallelPair_bundledCycleDesign _ _ (by norm_num)

/-- The `(6,3)` bundled cycle with arc sizes `(2,2,1,1)` — also an exact tie. -/
theorem hasParallelPair_bundlingSixThreePaired :
    HasParallelPair (bundledCycleDesign bundlingSixThreePaired (by norm_num)) :=
  hasParallelPair_bundledCycleDesign _ _ (by norm_num)

/-- Every `(7,3)` bundled cycle of the shipped catalogue carries one too. -/
theorem hasParallelPair_bundlingSevenThreeHeavy :
    HasParallelPair (bundledCycleDesign bundlingSevenThreeHeavy (by norm_num)) :=
  hasParallelPair_bundledCycleDesign _ _ (by norm_num)

theorem hasParallelPair_bundlingSevenThreeMixed :
    HasParallelPair (bundledCycleDesign bundlingSevenThreeMixed (by norm_num)) :=
  hasParallelPair_bundledCycleDesign _ _ (by norm_num)

theorem hasParallelPair_bundlingSevenThreePaired :
    HasParallelPair (bundledCycleDesign bundlingSevenThreePaired (by norm_num)) :=
  hasParallelPair_bundledCycleDesign _ _ (by norm_num)

/-- **The split tetrahedron carries a parallel pair**, for every admissible split:
atoms `2` and `3` both carry tetrahedron direction `2`. -/
theorem hasParallelPair_splitTetraDesign {splitA splitB : ℝ}
    (hAPos : 0 < splitA) (hALt : splitA < 1/4) (hBPos : 0 < splitB) (hBLt : splitB < 1/4) :
    HasParallelPair (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) :=
  ⟨2, 3, 1, by decide, by rw [one_smul]; rfl⟩

/-- **EVERY `(6,3)` TIE THE TREE OWNS CARRIES A PARALLEL PAIR.**  The three named
witnesses are the uniform-weight `ℚ(√5)` split, the bundled cycle at both `(6,3)`
bundlings, and the split tetrahedron at every admissible split.  This is the exact
evidence base of `Gtz.HingeHoldsAtSize 6 3`: not one shipped tie escapes it. -/
theorem every_shipped_sixThree_tie_hasParallelPair :
    (IsTie uniformTieDesign ∧ HasParallelPair uniformTieDesign)
    ∧ (IsTie (bundledCycleDesign bundlingSixThreeHeavy (by norm_num))
        ∧ HasParallelPair (bundledCycleDesign bundlingSixThreeHeavy (by norm_num)))
    ∧ (IsTie (bundledCycleDesign bundlingSixThreePaired (by norm_num))
        ∧ HasParallelPair (bundledCycleDesign bundlingSixThreePaired (by norm_num)))
    ∧ ∀ (splitA splitB : ℝ) (hAPos : 0 < splitA) (hALt : splitA < 1/4)
        (hBPos : 0 < splitB) (hBLt : splitB < 1/4),
        IsTie (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt)
          ∧ HasParallelPair (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) :=
  ⟨⟨uniformTieDesign_isTie, uniformTieDesign_hasParallelPair⟩,
   ⟨bundlingSixThreeHeavy_isTie, hasParallelPair_bundlingSixThreeHeavy⟩,
   ⟨bundlingSixThreePaired_isTie, hasParallelPair_bundlingSixThreePaired⟩,
   fun splitA splitB hAPos hALt hBPos hBLt =>
     ⟨splitTetraDesign_isTie splitA splitB hAPos hALt hBPos hBLt,
      hasParallelPair_splitTetraDesign hAPos hALt hBPos hBLt⟩⟩

end Gtz
