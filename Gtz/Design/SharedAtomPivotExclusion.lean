/-
# The omitted-label pivot exclusion, and the shared atom of two meeting lines

The complement leverage law reads a selection's gap on the labels the selection
OMITS.  At a single omitted label the complement form is one minus that label's
full-selection pivot.  Taking the coefficient vector supported at one label
therefore kills the quantifier outright:

  a positive definite selection forces EVERY label it omits below unit pivot.

This is the design-level companion of the chart-level pivot exclusion, and it
needs no chart, no whitening and no square root.

Spent at the two meeting lines it isolates ONE scalar.  The two lines are
`{0,1,2}` and `{0,3,4}`, sharing the atom `0` and leaving `5` open.  All four
transversals of `Gtz.TwoMeetingLinesTransversalStrict` OMIT the shared atom, so
each of them forces `pivot design univ 0 < 1`.  The shared atom is the class's
rigidity kernel, and the obligation cannot hold unless that atom is droppable at
the full selection.

The contrapositive is an obstruction: a design whose shared atom carries unit
pivot or more admits no strict transversal at all.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.ComplementLeverageLaw
import Gtz.Design.TwoMeetingLinesTransversal

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The indicator coefficient vector -/

/-- The complement combination at an indicator coefficient is the atom itself. -/
theorem complementCombination_indicator (D : WeightedDesign m k)
    (T : Finset (Fin m)) (c : Fin m) (hc : c ∈ T) :
    complementCombination D T (fun d => if d = c then 1 else 0) = D.atom c := by
  classical
  have hstep : ∀ d ∈ T, (if d = c then (1 : ℝ) else 0) • D.atom d
      = if d = c then D.atom d else 0 := by
    intro d _
    by_cases h : d = c
    · simp [h]
    · simp [h]
  rw [complementCombination, Finset.sum_congr rfl hstep]
  simp [hc]

/-- The squared indicator sums to one over any set containing its label. -/
theorem sum_sq_indicator (T : Finset (Fin m)) (c : Fin m) (hc : c ∈ T) :
    ∑ d ∈ T, (if d = c then (1 : ℝ) else 0) ^ 2 = 1 := by
  classical
  have hstep : ∀ d ∈ T, (if d = c then (1 : ℝ) else 0) ^ 2
      = if d = c then (1 : ℝ) else 0 := by
    intro d _
    by_cases h : d = c
    · simp [h]
    · simp [h]
  rw [Finset.sum_congr rfl hstep]
  simp [hc]

/-- **The complement form at one label.**  Supported at a single omitted label
the form reads one minus that label's full-selection pivot, whatever the rest of
the omitted set is. -/
theorem designComplementForm_indicator (D : WeightedDesign m k)
    (T : Finset (Fin m)) (c : Fin m) (hc : c ∈ T) :
    designComplementForm D T (fun d => if d = c then 1 else 0)
      = 1 - pivot D Finset.univ c := by
  rw [designComplementForm, complementCombination_indicator D T c hc,
    sum_sq_indicator T c hc, pivot_eq_dot]

/-! ## The pivot exclusion -/

/-- **THE OMITTED-LABEL PIVOT EXCLUSION.**  Every label omitted by a positive
definite selection carries full-selection pivot strictly below one.  Generic in
the size and the rank, with no chart. -/
theorem pivot_univ_lt_one_of_posDef_of_mem_compl (D : WeightedDesign m k)
    (hm : 2 ≤ m) (selected : Finset (Fin m)) (c : Fin m)
    (hc : c ∈ selectedᶜ)
    (hpos : (subsetSum D selected - 1).PosDef) :
    pivot D Finset.univ c < 1 := by
  classical
  have hK := posDef_fullExcess D hm
  have hcc : (selectedᶜ)ᶜ = selected := compl_compl selected
  have hlaw := (posDef_complementGap_iff_designComplementForm_pos D selectedᶜ hK).mp
    (by rw [hcc]; exact hpos)
  have hne : ∃ d ∈ selectedᶜ, (if d = c then (1 : ℝ) else 0) ≠ 0 := ⟨c, hc, by simp⟩
  have hval := hlaw (fun d => if d = c then 1 else 0) hne
  rw [designComplementForm_indicator D selectedᶜ c hc] at hval
  linarith

/-- **The omitted set sits inside the low-pivot set.**  A positive definite
selection places its whole complement below unit pivot. -/
theorem compl_subset_lowPivot_of_posDef (D : WeightedDesign m k) (hm : 2 ≤ m)
    (selected : Finset (Fin m))
    (hpos : (subsetSum D selected - 1).PosDef) :
    selectedᶜ ⊆ Finset.univ.filter fun c => pivot D Finset.univ c < 1 := by
  classical
  intro c hc
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ c,
    pivot_univ_lt_one_of_posDef_of_mem_compl D hm selected c hc hpos⟩

/-! ## The two meeting lines -/

/-- **THE SHARED ATOM MUST BE DROPPABLE.**  Every transversal omits the shared
atom `0`, so a strict transversal forces that atom below unit pivot at the full
selection.  This is a necessary condition for the two-meeting-lines obligation,
and it is one scalar. -/
theorem twoMeetingLines_shared_pivot_lt_one (design : WeightedDesign 6 3)
    (hstrict : TwoMeetingLinesTransversalStrict design) :
    pivot design Finset.univ 0 < 1 := by
  rcases hstrict with h | h | h | h
  · exact pivot_univ_lt_one_of_posDef_of_mem_compl design (by norm_num)
      ({1, 3, 5} : Finset (Fin 6)) 0 (by decide) h
  · exact pivot_univ_lt_one_of_posDef_of_mem_compl design (by norm_num)
      ({1, 4, 5} : Finset (Fin 6)) 0 (by decide) h
  · exact pivot_univ_lt_one_of_posDef_of_mem_compl design (by norm_num)
      ({2, 3, 5} : Finset (Fin 6)) 0 (by decide) h
  · exact pivot_univ_lt_one_of_posDef_of_mem_compl design (by norm_num)
      ({2, 4, 5} : Finset (Fin 6)) 0 (by decide) h

/-- **THE OBSTRUCTION.**  A design whose shared atom carries unit pivot or more
admits no strict transversal.  The contrapositive of the exclusion, and the form
a refutation would take.

#ZERO-CONSUMER, and it is the sharpest refuter shape in this class.  A single
design on the two-meeting-lines stratum that satisfies the antecedent of
`Gtz.TwoMeetingLinesSeededTransversal` (Gtz/Wave/FlatPairWeakSeed.lean:651) and
carries `1 <= pivot design Finset.univ 0` would refute
`Skeleton.obligationSeededTransversalTwoMeetingLines` outright.  No search for
such a design is recorded.  The exact-rational stratum witness
`Gtz.twinFailureDesign` (Gtz/Design/OrthogonalConicAndTwinRefutation.lean:670)
is the natural first probe. -/
theorem not_twoMeetingLinesTransversalStrict_of_shared_pivot_ge_one
    (design : WeightedDesign 6 3) (hge : 1 ≤ pivot design Finset.univ 0) :
    ¬ TwoMeetingLinesTransversalStrict design := fun hstrict =>
  absurd (twoMeetingLines_shared_pivot_lt_one design hstrict) (not_lt.mpr hge)

/-- **The open atom is droppable too.**  Every transversal HOLDS the open label
`5`, so no transversal omits it -- but each transversal omits one private label
from each line, so a strict transversal places one of `{1,2}` and one of `{3,4}`
below unit pivot as well. -/
theorem twoMeetingLines_privates_pivot_lt_one (design : WeightedDesign 6 3)
    (hstrict : TwoMeetingLinesTransversalStrict design) :
    (pivot design Finset.univ 2 < 1 ∨ pivot design Finset.univ 1 < 1) ∧
      (pivot design Finset.univ 4 < 1 ∨ pivot design Finset.univ 3 < 1) := by
  rcases hstrict with h | h | h | h
  · exact ⟨Or.inl (pivot_univ_lt_one_of_posDef_of_mem_compl design (by norm_num)
      ({1, 3, 5} : Finset (Fin 6)) 2 (by decide) h),
      Or.inl (pivot_univ_lt_one_of_posDef_of_mem_compl design (by norm_num)
        ({1, 3, 5} : Finset (Fin 6)) 4 (by decide) h)⟩
  · exact ⟨Or.inl (pivot_univ_lt_one_of_posDef_of_mem_compl design (by norm_num)
      ({1, 4, 5} : Finset (Fin 6)) 2 (by decide) h),
      Or.inr (pivot_univ_lt_one_of_posDef_of_mem_compl design (by norm_num)
        ({1, 4, 5} : Finset (Fin 6)) 3 (by decide) h)⟩
  · exact ⟨Or.inr (pivot_univ_lt_one_of_posDef_of_mem_compl design (by norm_num)
      ({2, 3, 5} : Finset (Fin 6)) 1 (by decide) h),
      Or.inl (pivot_univ_lt_one_of_posDef_of_mem_compl design (by norm_num)
        ({2, 3, 5} : Finset (Fin 6)) 4 (by decide) h)⟩
  · exact ⟨Or.inr (pivot_univ_lt_one_of_posDef_of_mem_compl design (by norm_num)
      ({2, 4, 5} : Finset (Fin 6)) 1 (by decide) h),
      Or.inr (pivot_univ_lt_one_of_posDef_of_mem_compl design (by norm_num)
        ({2, 4, 5} : Finset (Fin 6)) 3 (by decide) h)⟩

end Gtz
