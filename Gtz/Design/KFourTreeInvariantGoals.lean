/-
# The K4 tree invariant goals: A3's leaf in the frame-free basis

`Gtz.kFourLeaf_iff_shortListMinors` splits A3's leaf into twenty-seven scalar
goals through Sylvester's leading minors.  Those minors read the gap in the
coordinates that `Gtz.kFourDirection` supplies, and that direction family is K4
grounded at one vertex.  Each coordinate's support is one vertex star, so the
tree that matches a star gets a corner minor that is positive for free, and a
tree that misses it does not.  The difficulty of a leading minor is an artifact
of the grounding.

The knife band already carries a criterion with no such artifact.
`Gtz.posDef_iff_invariantPencilTriple` states that positive definiteness of a
symmetric `3x3` matrix is positivity of the three invariant pencil
coefficients.  This module names those three coefficients as goals of a tree,
and restates the leaf through them.

The count is the same as the leading-minor split: three goals for each of the
nine surviving trees.  The difference is that no goal is free and none is
harder than another because of the grounding.

The criterion itself is NOT new here, and neither is the nine-element cut.
This module composes `Gtz.posDef_iff_invariantPencilTriple` with
`Gtz.kFourGaugeWall_posDef_spanningTree_mem_nine` and adds the names.
-/
import Mathlib
import Gtz.Design.KFourChartClosure
import Gtz.Design.KFourTreeMinorGoals
import Gtz.Wave.GaugeWallTriangleTreeReduction

namespace Gtz

open Matrix

/-! ## The three invariant pencil coefficients of a symmetric `3x3` -/

/-- The first invariant coefficient: the linear one. -/
def invariantOne (mat : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  mat 0 0 + mat 1 1 + mat 2 2 + mat 0 1 + mat 0 2 + mat 1 2

/-- The second invariant coefficient: the quadratic one. -/
def invariantTwo (mat : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  3 * mat 0 0 * mat 1 1 + 3 * mat 0 0 * mat 2 2 + 3 * mat 1 1 * mat 2 2
    + 2 * mat 0 0 * mat 1 2 + 2 * mat 1 1 * mat 0 2 + 2 * mat 2 2 * mat 0 1
    - 3 * mat 0 1 ^ 2 - 3 * mat 0 2 ^ 2 - 3 * mat 1 2 ^ 2
    - 2 * mat 0 1 * mat 0 2 - 2 * mat 0 1 * mat 1 2 - 2 * mat 0 2 * mat 1 2

/-- The third invariant coefficient: the cubic one, which is the determinant. -/
def invariantThree (mat : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  mat 0 0 * mat 1 1 * mat 2 2 - mat 0 0 * mat 1 2 ^ 2 - mat 0 1 ^ 2 * mat 2 2
    + 2 * mat 0 1 * mat 0 2 * mat 1 2 - mat 0 2 ^ 2 * mat 1 1

/-- **The frame-free criterion, in named coefficients.**  A symmetric `3x3`
matrix is positive definite exactly when its three named invariant coefficients
are positive.  The equivalence is `Gtz.posDef_iff_invariantPencilTriple`, which
states the same three polynomials on explicit entries.  This restatement adds
the three names, and the names are the point: a tactic needs a named target. -/
theorem posDef_iff_invariantTriple {mat : Matrix (Fin 3) (Fin 3) ℝ} (hsymm : matᵀ = mat) :
    mat.PosDef ↔ 0 < invariantOne mat ∧ 0 < invariantTwo mat
      ∧ 0 < invariantThree mat := by
  rw [invariantOne, invariantTwo, invariantThree]
  conv_lhs => rw [symmetricFinThree_eq_explicit mat hsymm]
  exact posDef_iff_invariantPencilTriple _ _ _ _ _ _

/-! ## The named invariant goals of a K4 tree -/

/-- The first invariant goal of a tree. -/
noncomputable def kFourTreeInvariantOne (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : ℝ :=
  invariantOne (directionChartGap kFourDirection point.mass point.weight tree)

/-- The second invariant goal of a tree. -/
noncomputable def kFourTreeInvariantTwo (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : ℝ :=
  invariantTwo (directionChartGap kFourDirection point.mass point.weight tree)

/-- The third invariant goal of a tree. -/
noncomputable def kFourTreeInvariantThree (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : ℝ :=
  invariantThree (directionChartGap kFourDirection point.mass point.weight tree)

/-- **A tree is decided by its three invariant goals.**  The chart gap is
symmetric, so the frame-free criterion applies verbatim. -/
theorem kFourTree_posDef_iff_invariant (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) :
    (directionChartGap kFourDirection point.mass point.weight tree).PosDef
      ↔ 0 < kFourTreeInvariantOne point tree ∧ 0 < kFourTreeInvariantTwo point tree
        ∧ 0 < kFourTreeInvariantThree point tree :=
  posDef_iff_invariantTriple (directionChartGap_transpose kFourDirection point.mass
    point.weight tree)

/-! ## The leaf, restated with no frame -/

/-- **The leaf conclusion from the invariant goals.**  One surviving tree whose
three invariant goals are positive supplies the leaf's existential. -/
theorem kFourLeafConclusion_of_shortListInvariants (point : DirectionChartPoint 6)
    (hgoals : ∃ tree ∈ kFourGaugeWallTreeShortList,
      0 < kFourTreeInvariantOne point tree ∧ 0 < kFourTreeInvariantTwo point tree
        ∧ 0 < kFourTreeInvariantThree point tree) :
    ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef := by
  obtain ⟨tree, hmem, hgoal⟩ := hgoals
  exact ⟨tree, kFourGaugeWallTreeShortList_subset tree hmem,
    (kFourTree_posDef_iff_invariant point tree).mpr hgoal⟩

/-- **The converse, on the gauge wall.**  A positive definite spanning tree lies
in the nine-element short list, so its three invariant goals are positive. -/
theorem shortListInvariants_of_kFourLeafConclusion (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ) (hscale : 0 < scale)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis)
    (haxisSum : axis ⬝ᵥ kFourAllOnes ≠ 0)
    (hleaf : ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef) :
    ∃ tree ∈ kFourGaugeWallTreeShortList,
      0 < kFourTreeInvariantOne point tree ∧ 0 < kFourTreeInvariantTwo point tree
        ∧ 0 < kFourTreeInvariantThree point tree := by
  obtain ⟨winner, hmem, hposDef⟩ := hleaf
  exact ⟨winner, kFourGaugeWall_posDef_spanningTree_mem_nine point axis scale hscale
    hwall haxisSum hmem hposDef, (kFourTree_posDef_iff_invariant point winner).mp hposDef⟩

/-- **THE FRAME-FREE SPLIT, AND IT IS LOSSLESS.**  On the gauge wall the leaf's
conclusion is EQUIVALENT to the existence of one surviving tree with three
positive invariant goals.  This is the sentence the A3 status paragraph names as
the closure of the class, cut from sixteen trees to nine. -/
theorem kFourLeaf_iff_shortListInvariants (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ) (hscale : 0 < scale)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis)
    (haxisSum : axis ⬝ᵥ kFourAllOnes ≠ 0) :
    (∃ winner ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection point.mass point.weight winner).PosDef)
      ↔ ∃ tree ∈ kFourGaugeWallTreeShortList,
          0 < kFourTreeInvariantOne point tree ∧ 0 < kFourTreeInvariantTwo point tree
            ∧ 0 < kFourTreeInvariantThree point tree :=
  ⟨shortListInvariants_of_kFourLeafConclusion point axis scale hscale hwall haxisSum,
    kFourLeafConclusion_of_shortListInvariants point⟩

/-! ## The trace rung, read off the entry law

The trace of a chart gap is linear in the boosted masses.  It is NOT the same
inequality for every tree, because `Gtz.kFourDirection` gives the three triangle
labels squared length two and the three star labels squared length one. -/

/-- **The trace of a K4 chart gap.**  The three triangle labels carry weight two
and the three star labels weight one, so the rung is linear but is not the same
inequality for every tree. -/
theorem kFourTrace_eq (point : DirectionChartPoint 6) (tree : Finset (Fin 6)) :
    (directionChartGap kFourDirection point.mass point.weight tree) 0 0
      + (directionChartGap kFourDirection point.mass point.weight tree) 1 1
      + (directionChartGap kFourDirection point.mass point.weight tree) 2 2
      = (∑ label ∈ tree, point.mass label / point.weight label
            * (kFourDirection label 0 ^ 2 + kFourDirection label 1 ^ 2
              + kFourDirection label 2 ^ 2))
        - ∑ label, point.mass label
            * (kFourDirection label 0 ^ 2 + kFourDirection label 1 ^ 2
              + kFourDirection label 2 ^ 2) := by
  rw [directionChartGap_entry, directionChartGap_entry, directionChartGap_entry]
  have hsplit : ∀ (labels : Finset (Fin 6)) (scaled : Fin 6 → ℝ),
      ∑ label ∈ labels, scaled label
          * (kFourDirection label 0 ^ 2 + kFourDirection label 1 ^ 2
            + kFourDirection label 2 ^ 2)
        = (∑ label ∈ labels, scaled label * kFourDirection label 0 * kFourDirection label 0)
          + (∑ label ∈ labels, scaled label * kFourDirection label 1 * kFourDirection label 1)
          + (∑ label ∈ labels, scaled label * kFourDirection label 2
              * kFourDirection label 2) := by
    intro labels scaled
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun label _ => by ring)
  rw [hsplit, hsplit]
  ring

/-- **The squared length of each K4 direction.**  The three triangle labels have
squared length two and the three star labels have squared length one.  The
asymmetry comes from the grounding at one vertex, not from the geometry: in the
sum-zero frame every K4 edge has squared length two. -/
theorem kFourDirection_normSq (label : Fin 6) :
    kFourDirection label 0 ^ 2 + kFourDirection label 1 ^ 2
      + kFourDirection label 2 ^ 2 = if label.val < 3 then 2 else 1 := by
  fin_cases label <;>
    norm_num [kFourDirection, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **The trace rung of a K4 tree, with its coefficients.**  The rung is linear
in the boosted masses.  It is NOT the same inequality for every tree: a triangle
label counts twice and a star label counts once, so trees carrying different
numbers of triangle labels get different inequalities. -/
theorem kFourTrace_eq_explicit (point : DirectionChartPoint 6) (tree : Finset (Fin 6)) :
    (directionChartGap kFourDirection point.mass point.weight tree) 0 0
      + (directionChartGap kFourDirection point.mass point.weight tree) 1 1
      + (directionChartGap kFourDirection point.mass point.weight tree) 2 2
      = (∑ label ∈ tree, point.mass label / point.weight label
            * (if label.val < 3 then 2 else 1))
        - ∑ label, point.mass label * (if label.val < 3 then 2 else 1) := by
  rw [kFourTrace_eq]
  simp only [kFourDirection_normSq]

end Gtz
