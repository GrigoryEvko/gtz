/-
# The trace rung of a K4 tree as a necessary condition

`Gtz.kFourTrace_eq_explicit` reads the trace of a K4 chart gap as a linear
expression in the boosted masses.  That statement is an identity, and an identity
filters nothing on its own.

This module makes the rung a NECESSARY condition.  A positive definite matrix has
a positive diagonal, so a positive definite gap clears its own trace rung.  The
contrapositive is the useful direction: a chart point at which no tree of the
nine-element short list clears its rung hosts no positive definite tree there
either.

The rung is linear, and it is NOT the same inequality for every tree.  A triangle
label of `Gtz.kFourDirection` has squared length two and a star label has squared
length one, so trees carrying different numbers of triangle labels get different
inequalities.  The asymmetry comes from the grounding at one vertex, and not from
the geometry.
-/
import Mathlib
import Gtz.Design.KFourTreeInvariantGoals

namespace Gtz

open Matrix

/-! ## 1. The trace of a positive definite three-by-three -/

/-- **A positive definite `3x3` has positive trace.**  Each diagonal entry is the
quadratic form at a standard basis vector. -/
theorem trace_pos_of_posDef_three {mat : Matrix (Fin 3) (Fin 3) ℝ}
    (hpd : mat.PosDef) : 0 < mat 0 0 + mat 1 1 + mat 2 2 := by
  have h0 : (0 : ℝ) < mat 0 0 := hpd.diag_pos
  have h1 : (0 : ℝ) < mat 1 1 := hpd.diag_pos
  have h2 : (0 : ℝ) < mat 2 2 := hpd.diag_pos
  linarith

/-! ## 2. The trace rung as a necessary condition -/

/-- **THE TRACE RUNG IS NECESSARY.**  A positive definite K4 tree gap has its
boosted trace strictly above the unboosted trace.  The coefficient of a label is
two on the three triangle labels and one on the three star labels. -/
theorem kFourTrace_pos_of_posDef (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6))
    (hpd : (directionChartGap kFourDirection point.mass point.weight tree).PosDef) :
    ∑ label, point.mass label * (if label.val < 3 then 2 else 1)
      < ∑ label ∈ tree, point.mass label / point.weight label
          * (if label.val < 3 then 2 else 1) := by
  have h := trace_pos_of_posDef_three hpd
  rw [kFourTrace_eq_explicit] at h
  linarith

/-- The rung written as the boosted trace of a tree. -/
noncomputable def kFourTreeBoostedTrace (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : ℝ :=
  ∑ label ∈ tree, point.mass label / point.weight label
    * (if label.val < 3 then 2 else 1)

/-- The unboosted trace of a chart point.  It does not depend on the tree. -/
noncomputable def kFourAmbientTrace (point : DirectionChartPoint 6) : ℝ :=
  ∑ label, point.mass label * (if label.val < 3 then 2 else 1)

/-- The rung in the named form. -/
theorem kFourAmbientTrace_lt_of_posDef (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6))
    (hpd : (directionChartGap kFourDirection point.mass point.weight tree).PosDef) :
    kFourAmbientTrace point < kFourTreeBoostedTrace point tree :=
  kFourTrace_pos_of_posDef point tree hpd

/-! ## 3. The filter on the nine-element short list -/

/-- **THE RUNG FILTERS THE SHORT LIST.**  If no tree of the nine-element gauge
wall short list clears its trace rung, then no tree of that list is positive
definite.  This is a cheap linear test in front of the three invariant goals. -/
theorem shortList_not_posDef_of_trace_le (point : DirectionChartPoint 6)
    (htrace : ∀ tree ∈ kFourGaugeWallTreeShortList,
      kFourTreeBoostedTrace point tree ≤ kFourAmbientTrace point) :
    ∀ tree ∈ kFourGaugeWallTreeShortList,
      ¬ (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  intro tree hmem hpd
  exact absurd (kFourAmbientTrace_lt_of_posDef point tree hpd)
    (not_lt.mpr (htrace tree hmem))

/-- **THE RUNG IS NECESSARY FOR THE LEAF.**  If some short list tree is positive
definite, then some short list tree clears its trace rung. -/
theorem exists_shortList_trace_gt_of_exists_posDef (point : DirectionChartPoint 6)
    (hleaf : ∃ tree ∈ kFourGaugeWallTreeShortList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef) :
    ∃ tree ∈ kFourGaugeWallTreeShortList,
      kFourAmbientTrace point < kFourTreeBoostedTrace point tree := by
  obtain ⟨tree, hmem, hpd⟩ := hleaf
  exact ⟨tree, hmem, kFourAmbientTrace_lt_of_posDef point tree hpd⟩

end Gtz
