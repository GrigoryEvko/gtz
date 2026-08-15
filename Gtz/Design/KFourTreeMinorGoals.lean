/-
# The K4 tree minor goals: A3's leaf as named scalar inequalities

A3's live route consumes two leaves, and each concludes

  `∃ winner ∈ kFourSpanningTreeList, (directionChartGap ... winner).PosDef`

That is one existential over sixteen trees, and no tactic can land progress in
it, because there is no smaller named thing to land it in.

This module splits it.  `Gtz.kFourGaugeWall_posDef_spanningTree_mem_nine` cuts
the sixteen trees to the nine of `Gtz.kFourGaugeWallTreeShortList`, and Sylvester
decides each tree by three leading minors.  So the leaf becomes twenty-seven
named scalar inequalities `0 < kFourTreeMinorOne point tree` and its two
companions, one triple per surviving tree.

The split is LOSSLESS under the wall hypotheses: `kFourLeaf_iff_shortListMinors`
is an equivalence, not a sufficient condition, because Sylvester is an
equivalence (`Gtz.leadingMinors_pos_iff_posDef_fin_three`) and the nine-element
cut is a necessary condition on a positive definite tree.

`directionChartGap_entry` is generic in the size and the direction family, so
the other strata read their own gaps through it without more work.

The Sylvester equivalence is NOT new here.  `Gtz.posDef_finThree_iff_leadingMinors`
already states it, with the three polynomials written inline.  This module adds
the three names and nothing else, because a tactic needs a named target, and an
inline polynomial is not a named target.
-/
import Mathlib
import Gtz.Design.KFourBandAtlas
import Gtz.Design.KFourChartClosure
import Gtz.Design.OneDeterminantReduction
import Gtz.Wave.GaugeWallTriangleTreeReduction

namespace Gtz

open Matrix

/-! ## The entry reading, generic in the size and the direction family -/

/-- **The chart gap entry by entry.**  Each entry is the selected labels'
boosted outer products less the full mass sum, both read at that entry.  No
positivity is used, and nothing is specialised to `K4`. -/
theorem directionChartGap_entry {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size))
    (rowIndex colIndex : Fin 3) :
    directionChartGap direction mass weight selected rowIndex colIndex
      = (∑ label ∈ selected, mass label / weight label
            * direction label rowIndex * direction label colIndex)
        - ∑ label, mass label * direction label rowIndex * direction label colIndex := by
  simp only [directionChartGap, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
    atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul, mul_assoc]

/-! ## The three leading minors of a symmetric `3x3` -/

/-- The first leading minor: the corner entry. -/
def leadingMinorOne (mat : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := mat 0 0

/-- The second leading minor: the top-left `2x2` determinant. -/
def leadingMinorTwo (mat : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  mat 0 0 * mat 1 1 - mat 0 1 ^ 2

/-- The third leading minor: the determinant. -/
noncomputable def leadingMinorThree (mat : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := mat.det

/-- **Sylvester, in named minors.**  A symmetric `3x3` matrix is positive
definite exactly when its three named leading minors are positive.  The
equivalence itself is `Gtz.posDef_finThree_iff_leadingMinors`, which states the
same three polynomials inline.  This restatement adds nothing but the three
names, and the names are the point: a tactic needs a named target. -/
theorem posDef_iff_leadingMinors {mat : Matrix (Fin 3) (Fin 3) ℝ} (hsymm : matᵀ = mat) :
    mat.PosDef ↔ 0 < leadingMinorOne mat ∧ 0 < leadingMinorTwo mat
      ∧ 0 < leadingMinorThree mat := by
  have hdet : leadingMinorThree mat
      = mat 0 0 * mat 1 1 * mat 2 2 - mat 0 0 * mat 1 2 ^ 2 - mat 0 1 ^ 2 * mat 2 2
        + 2 * mat 0 1 * mat 0 2 * mat 1 2 - mat 0 2 ^ 2 * mat 1 1 := by
    rw [leadingMinorThree]
    conv_lhs => rw [symmetricFinThree_eq_explicit mat hsymm]
    simp [Matrix.det_fin_three]
    ring
  rw [leadingMinorOne, leadingMinorTwo, hdet]
  exact posDef_finThree_iff_leadingMinors mat hsymm

/-! ## The named goals of a K4 tree -/

/-- The first named goal of a tree: the corner entry of its chart gap. -/
noncomputable def kFourTreeMinorOne (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : ℝ :=
  leadingMinorOne (directionChartGap kFourDirection point.mass point.weight tree)

/-- The second named goal of a tree: the `2x2` leading minor of its chart gap. -/
noncomputable def kFourTreeMinorTwo (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : ℝ :=
  leadingMinorTwo (directionChartGap kFourDirection point.mass point.weight tree)

/-- The third named goal of a tree: the determinant of its chart gap. -/
noncomputable def kFourTreeMinorThree (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : ℝ :=
  leadingMinorThree (directionChartGap kFourDirection point.mass point.weight tree)

/-- **A tree is decided by its three named goals.**  The chart gap is symmetric,
so Sylvester applies verbatim. -/
theorem kFourTree_posDef_iff (point : DirectionChartPoint 6) (tree : Finset (Fin 6)) :
    (directionChartGap kFourDirection point.mass point.weight tree).PosDef
      ↔ 0 < kFourTreeMinorOne point tree ∧ 0 < kFourTreeMinorTwo point tree
        ∧ 0 < kFourTreeMinorThree point tree :=
  posDef_iff_leadingMinors (directionChartGap_transpose kFourDirection point.mass
    point.weight tree)

/-! ## The assembly -/

/-- Every tree of the nine-element short list is a spanning tree. -/
theorem kFourGaugeWallTreeShortList_subset :
    ∀ tree ∈ kFourGaugeWallTreeShortList, tree ∈ kFourSpanningTreeList := by
  decide

/-- **The leaf conclusion from the named goals.**  One surviving tree whose three
named goals are positive supplies the leaf's existential. -/
theorem kFourLeafConclusion_of_shortListMinors (point : DirectionChartPoint 6)
    (hgoals : ∃ tree ∈ kFourGaugeWallTreeShortList,
      0 < kFourTreeMinorOne point tree ∧ 0 < kFourTreeMinorTwo point tree
        ∧ 0 < kFourTreeMinorThree point tree) :
    ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef := by
  obtain ⟨tree, hmem, hminors⟩ := hgoals
  exact ⟨tree, kFourGaugeWallTreeShortList_subset tree hmem,
    (kFourTree_posDef_iff point tree).mpr hminors⟩

/-- **The converse, on the gauge wall.**  A positive definite spanning tree lies
in the nine-element short list, so its three named goals are positive.  This is
what makes the split lossless rather than merely sufficient. -/
theorem shortListMinors_of_kFourLeafConclusion (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ) (hscale : 0 < scale)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis)
    (haxisSum : axis ⬝ᵥ kFourAllOnes ≠ 0)
    (hleaf : ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef) :
    ∃ tree ∈ kFourGaugeWallTreeShortList,
      0 < kFourTreeMinorOne point tree ∧ 0 < kFourTreeMinorTwo point tree
        ∧ 0 < kFourTreeMinorThree point tree := by
  obtain ⟨winner, hmem, hposDef⟩ := hleaf
  exact ⟨winner, kFourGaugeWall_posDef_spanningTree_mem_nine point axis scale hscale
    hwall haxisSum hmem hposDef, (kFourTree_posDef_iff point winner).mp hposDef⟩

/-- **THE SPLIT IS LOSSLESS.**  On the gauge wall the leaf's conclusion is
EQUIVALENT to the existence of one surviving tree with three positive named
goals.  Twenty-seven scalar inequalities replace one existential over sixteen
trees, and nothing is given away. -/
theorem kFourLeaf_iff_shortListMinors (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ) (hscale : 0 < scale)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis)
    (haxisSum : axis ⬝ᵥ kFourAllOnes ≠ 0) :
    (∃ winner ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection point.mass point.weight winner).PosDef)
      ↔ ∃ tree ∈ kFourGaugeWallTreeShortList,
          0 < kFourTreeMinorOne point tree ∧ 0 < kFourTreeMinorTwo point tree
            ∧ 0 < kFourTreeMinorThree point tree :=
  ⟨shortListMinors_of_kFourLeafConclusion point axis scale hscale hwall haxisSum,
    kFourLeafConclusion_of_shortListMinors point⟩

end Gtz
