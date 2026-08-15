/-
# The transversal load ledger of the two meeting lines

The landed layer decides a strict transversal from a set that is handed to it.
`Gtz.twoMeetingLinesTransversalStrict_of_pivotLoadScore_sum_ge_three` takes the
card-three set as an input, so it answers a question about one triple and not a
question about the design.

This module closes the selection.  It reads the four transversals as one scalar,
the TRANSVERSAL DEFICIT, and decides the whole disjunction from that scalar.

The deficit is the load the four transversals cannot reach.  Every transversal
holds the open label `5`, one private label of the first line and one private
label of the second line.  The three labels a transversal drops are therefore
the shared label `0`, one of `{1,2}` and one of `{3,4}`, and the cheapest drop
is the one that leaves the most load behind.

Six results, in order.

* The UNIT DICTIONARY.  `load c - 1 = (1 - weight c) * (pivot c - 1)`, so unit
  load and unit pivot are the same threshold.  The whole shared-atom exclusion
  layer speaks in load language through this one identity.
* The BALANCE IDENTITY.  `∑ (load c - 1) = rank + 1 - size`, which is `-2` at
  `(6,3)`.
* The DEFICIT PARTITION.  `deficit + (best transversal load) = rank + 1`.
* The CRITERION.  `deficit ≤ 1` gives a strict transversal.
* The SELECTION RULE.  Unit pivot at the open label and at one private label of
  each line gives a strict transversal.  This is the exact converse of the
  landed exclusions, which say that a strict transversal forces those same
  labels below unit pivot.
* The CLOSED DOOR.  A load vector exists that satisfies every counting law of
  this ledger and still carries unit load at the shared label.  No argument that
  reads only the load vector can exclude a shared atom at unit pivot.
-/

import Gtz.Wave.LineResidualPivotLoadWiring
import Gtz.Design.SharedAtomPivotExclusion

namespace Gtz

open Finset

variable {m k : ℕ}

/-! ## The unit dictionary -/

/-- The load excess is the co-weight times the pivot excess. -/
theorem pivotLoadScore_sub_one (D : WeightedDesign m k) (c : Fin m) :
    pivotLoadScore D c - 1 = (1 - D.weight c) * (pivot D Finset.univ c - 1) := by
  simp only [pivotLoadScore]
  ring

/-- Unit load and unit pivot are the same threshold, in the strict direction. -/
theorem pivotLoadScore_lt_one_iff (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    pivotLoadScore D c < 1 ↔ pivot D Finset.univ c < 1 := by
  have hpos : 0 < 1 - D.weight c := by
    have := weight_lt_one D hm c
    linarith
  constructor
  · intro hlt
    have hneg : pivotLoadScore D c - 1 < 0 := by linarith
    rw [pivotLoadScore_sub_one] at hneg
    nlinarith [hneg, hpos]
  · intro hlt
    have hneg : pivot D Finset.univ c - 1 < 0 := by linarith
    have hprod := mul_neg_of_pos_of_neg hpos hneg
    rw [← pivotLoadScore_sub_one] at hprod
    linarith

/-- Unit load and unit pivot are the same threshold, in the weak direction. -/
theorem one_le_pivotLoadScore_iff (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    1 ≤ pivotLoadScore D c ↔ 1 ≤ pivot D Finset.univ c := by
  rw [← not_lt, ← not_lt, not_iff_not]
  exact pivotLoadScore_lt_one_iff D hm c

/-- The load of a label is positive: the pivot is nonnegative and the weight is
positive. -/
theorem pivotLoadScore_pos (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    0 < pivotLoadScore D c := by
  have hpivot : 0 ≤ pivot D Finset.univ c := pivot_univ_nonneg D hm c
  have hw : 0 < D.weight c := D.weight_pos c
  have hco : 0 < 1 - D.weight c := by
    have := weight_lt_one D hm c
    linarith
  have hprod : 0 ≤ (1 - D.weight c) * pivot D Finset.univ c :=
    mul_nonneg (le_of_lt hco) hpivot
  simp only [pivotLoadScore]
  linarith

/-! ## The balance identity -/

/-- The load excesses sum to rank plus one minus the label count. -/
theorem sum_pivotLoadScore_sub_one (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ∑ c, (pivotLoadScore D c - 1) = (k : ℝ) + 1 - (m : ℝ) := by
  rw [Finset.sum_sub_distrib, sum_pivotLoadScore D hm]
  simp

/-- The co-weighted pivot excesses sum to rank plus one minus the label count.
This is the balance identity in pivot language. -/
theorem sum_deficiency_mul_pivot_sub_one (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ∑ c, (1 - D.weight c) * (pivot D Finset.univ c - 1) = (k : ℝ) + 1 - (m : ℝ) := by
  rw [← sum_pivotLoadScore_sub_one D hm]
  exact Finset.sum_congr rfl fun c _ => (pivotLoadScore_sub_one D c).symm

/-- At the `(6,3)` shape the load excesses sum to minus two. -/
theorem sum_pivotLoadScore_sub_one_sixThree (D : WeightedDesign 6 3) :
    ∑ c, (pivotLoadScore D c - 1) = -2 := by
  rw [sum_pivotLoadScore_sub_one D (by norm_num)]
  norm_num

/-! ## The deficit -/

/-- **The transversal deficit.**  The load that no transversal of the two
meeting lines can reach: the shared label, the lighter private label of the
first line and the lighter private label of the second line. -/
noncomputable def transversalDeficit (D : WeightedDesign 6 3) : ℝ :=
  pivotLoadScore D 0
    + min (pivotLoadScore D 1) (pivotLoadScore D 2)
    + min (pivotLoadScore D 3) (pivotLoadScore D 4)

/-- The total load of a `(6,3)` design is four. -/
theorem sum_pivotLoadScore_sixThree (D : WeightedDesign 6 3) :
    pivotLoadScore D 0 + pivotLoadScore D 1 + pivotLoadScore D 2
        + pivotLoadScore D 3 + pivotLoadScore D 4 + pivotLoadScore D 5 = 4 := by
  have h := sum_pivotLoadScore D (by norm_num : (2 : ℕ) ≤ 6)
  rw [Fin.sum_univ_six] at h
  norm_num at h
  linarith

/-- **The deficit partition.**  The deficit and the load of the heaviest
transversal add to four.  The heaviest transversal holds the open label, the
heavier private label of the first line and the heavier private label of the
second line. -/
theorem transversalDeficit_add_max (D : WeightedDesign 6 3) :
    transversalDeficit D
        + (max (pivotLoadScore D 1) (pivotLoadScore D 2)
          + max (pivotLoadScore D 3) (pivotLoadScore D 4)
          + pivotLoadScore D 5) = 4 := by
  have htotal := sum_pivotLoadScore_sixThree D
  have h12 := min_add_max (pivotLoadScore D 1) (pivotLoadScore D 2)
  have h34 := min_add_max (pivotLoadScore D 3) (pivotLoadScore D 4)
  simp only [transversalDeficit]
  linarith

/-- The deficit is positive. -/
theorem transversalDeficit_pos (D : WeightedDesign 6 3) : 0 < transversalDeficit D := by
  have h0 : 0 < pivotLoadScore D 0 := pivotLoadScore_pos D (by norm_num) 0
  have h1 : 0 < pivotLoadScore D 1 := pivotLoadScore_pos D (by norm_num) 1
  have h2 : 0 < pivotLoadScore D 2 := pivotLoadScore_pos D (by norm_num) 2
  have h3 : 0 < pivotLoadScore D 3 := pivotLoadScore_pos D (by norm_num) 3
  have h4 : 0 < pivotLoadScore D 4 := pivotLoadScore_pos D (by norm_num) 4
  have hmin12 : 0 < min (pivotLoadScore D 1) (pivotLoadScore D 2) := lt_min h1 h2
  have hmin34 : 0 < min (pivotLoadScore D 3) (pivotLoadScore D 4) := lt_min h3 h4
  simp only [transversalDeficit]
  linarith

/-! ## The four transversal sums -/

private theorem sum_load_135 (D : WeightedDesign 6 3) :
    ∑ c ∈ ({1, 3, 5} : Finset (Fin 6)), pivotLoadScore D c
      = pivotLoadScore D 1 + pivotLoadScore D 3 + pivotLoadScore D 5 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem sum_load_145 (D : WeightedDesign 6 3) :
    ∑ c ∈ ({1, 4, 5} : Finset (Fin 6)), pivotLoadScore D c
      = pivotLoadScore D 1 + pivotLoadScore D 4 + pivotLoadScore D 5 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem sum_load_235 (D : WeightedDesign 6 3) :
    ∑ c ∈ ({2, 3, 5} : Finset (Fin 6)), pivotLoadScore D c
      = pivotLoadScore D 2 + pivotLoadScore D 3 + pivotLoadScore D 5 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem sum_load_245 (D : WeightedDesign 6 3) :
    ∑ c ∈ ({2, 4, 5} : Finset (Fin 6)), pivotLoadScore D c
      = pivotLoadScore D 2 + pivotLoadScore D 4 + pivotLoadScore D 5 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-! ## The criterion -/

/-- **THE TRANSVERSAL CRITERION.**  A design whose transversal deficit is at
most one has a strictly dominating transversal.  This decides the four-way
disjunction from ONE scalar of the design, where the landed load theorem needed
the card-three set as an input. -/
theorem twoMeetingLinesTransversalStrict_of_transversalDeficit_le_one
    (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hblindFirst : IsLinePairLiftBlindAt design normalFirst {0, 1, 2})
    (hblindSecond : IsLinePairLiftBlindAt design normalSecond {0, 3, 4})
    (hdeficit : transversalDeficit design ≤ 1) :
    TwoMeetingLinesTransversalStrict design := by
  have htotal := sum_pivotLoadScore_sixThree design
  simp only [transversalDeficit] at hdeficit
  rcases le_total (pivotLoadScore design 1) (pivotLoadScore design 2) with h12 | h12 <;>
    rcases le_total (pivotLoadScore design 3) (pivotLoadScore design 4) with h34 | h34
  · rw [min_eq_left h12, min_eq_left h34] at hdeficit
    refine twoMeetingLinesTransversalStrict_of_pivotLoadScore_sum_ge_three design
      normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond ({2, 4, 5} : Finset (Fin 6)) (by decide) ?_
    rw [sum_load_245]
    linarith
  · rw [min_eq_left h12, min_eq_right h34] at hdeficit
    refine twoMeetingLinesTransversalStrict_of_pivotLoadScore_sum_ge_three design
      normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond ({2, 3, 5} : Finset (Fin 6)) (by decide) ?_
    rw [sum_load_235]
    linarith
  · rw [min_eq_right h12, min_eq_left h34] at hdeficit
    refine twoMeetingLinesTransversalStrict_of_pivotLoadScore_sum_ge_three design
      normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond ({1, 4, 5} : Finset (Fin 6)) (by decide) ?_
    rw [sum_load_145]
    linarith
  · rw [min_eq_right h12, min_eq_right h34] at hdeficit
    refine twoMeetingLinesTransversalStrict_of_pivotLoadScore_sum_ge_three design
      normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond ({1, 3, 5} : Finset (Fin 6)) (by decide) ?_
    rw [sum_load_135]
    linarith

/-- The contrapositive: a design with no strict transversal has deficit above
one. -/
theorem one_lt_transversalDeficit_of_not_transversalStrict
    (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hblindFirst : IsLinePairLiftBlindAt design normalFirst {0, 1, 2})
    (hblindSecond : IsLinePairLiftBlindAt design normalSecond {0, 3, 4})
    (hfail : ¬ TwoMeetingLinesTransversalStrict design) :
    1 < transversalDeficit design := by
  by_contra hle
  exact hfail (twoMeetingLinesTransversalStrict_of_transversalDeficit_le_one design
    normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
    hblindFirst hblindSecond (not_lt.mp hle))

/-! ## The selection rule -/

/-- **THE SELECTION RULE.**  Unit pivot at the open label together with unit
pivot at one private label of each line produces a strictly dominating
transversal.

This is the exact converse of the landed exclusions.  `Gtz.twoMeetingLines_shared_pivot_lt_one`
and `Gtz.twoMeetingLines_privates_pivot_lt_one` say that a strict transversal
forces the shared label and one private label of each line BELOW unit pivot.
This theorem reads the same three labels in the other direction. -/
theorem twoMeetingLinesTransversalStrict_of_private_pivots_ge_one
    (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hblindFirst : IsLinePairLiftBlindAt design normalFirst {0, 1, 2})
    (hblindSecond : IsLinePairLiftBlindAt design normalSecond {0, 3, 4})
    (hopen : 1 ≤ pivot design Finset.univ 5)
    (hfirst : 1 ≤ pivot design Finset.univ 1 ∨ 1 ≤ pivot design Finset.univ 2)
    (hsecond : 1 ≤ pivot design Finset.univ 3 ∨ 1 ≤ pivot design Finset.univ 4) :
    TwoMeetingLinesTransversalStrict design := by
  have hopenLoad : 1 ≤ pivotLoadScore design 5 :=
    (one_le_pivotLoadScore_iff design (by norm_num) 5).mpr hopen
  rcases hfirst with h1 | h2 <;> rcases hsecond with h3 | h4
  · have hl1 : 1 ≤ pivotLoadScore design 1 :=
      (one_le_pivotLoadScore_iff design (by norm_num) 1).mpr h1
    have hl3 : 1 ≤ pivotLoadScore design 3 :=
      (one_le_pivotLoadScore_iff design (by norm_num) 3).mpr h3
    refine twoMeetingLinesTransversalStrict_of_pivotLoadScore_sum_ge_three design
      normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond ({1, 3, 5} : Finset (Fin 6)) (by decide) ?_
    rw [sum_load_135]
    linarith
  · have hl1 : 1 ≤ pivotLoadScore design 1 :=
      (one_le_pivotLoadScore_iff design (by norm_num) 1).mpr h1
    have hl4 : 1 ≤ pivotLoadScore design 4 :=
      (one_le_pivotLoadScore_iff design (by norm_num) 4).mpr h4
    refine twoMeetingLinesTransversalStrict_of_pivotLoadScore_sum_ge_three design
      normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond ({1, 4, 5} : Finset (Fin 6)) (by decide) ?_
    rw [sum_load_145]
    linarith
  · have hl2 : 1 ≤ pivotLoadScore design 2 :=
      (one_le_pivotLoadScore_iff design (by norm_num) 2).mpr h2
    have hl3 : 1 ≤ pivotLoadScore design 3 :=
      (one_le_pivotLoadScore_iff design (by norm_num) 3).mpr h3
    refine twoMeetingLinesTransversalStrict_of_pivotLoadScore_sum_ge_three design
      normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond ({2, 3, 5} : Finset (Fin 6)) (by decide) ?_
    rw [sum_load_235]
    linarith
  · have hl2 : 1 ≤ pivotLoadScore design 2 :=
      (one_le_pivotLoadScore_iff design (by norm_num) 2).mpr h2
    have hl4 : 1 ≤ pivotLoadScore design 4 :=
      (one_le_pivotLoadScore_iff design (by norm_num) 4).mpr h4
    refine twoMeetingLinesTransversalStrict_of_pivotLoadScore_sum_ge_three design
      normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond ({2, 4, 5} : Finset (Fin 6)) (by decide) ?_
    rw [sum_load_245]
    linarith

/-! ## The band -/

/-- A strict transversal keeps the shared label below unit load.  The landed
exclusion reads the pivot, and the dictionary carries it to the load. -/
theorem shared_pivotLoadScore_lt_one_of_transversalStrict
    (design : WeightedDesign 6 3)
    (hstrict : TwoMeetingLinesTransversalStrict design) :
    pivotLoadScore design 0 < 1 :=
  (pivotLoadScore_lt_one_iff design (by norm_num) 0).mpr
    (twoMeetingLines_shared_pivot_lt_one design hstrict)

/-- A strict transversal keeps the lighter private label of each line below unit
load. -/
theorem private_min_pivotLoadScore_lt_one_of_transversalStrict
    (design : WeightedDesign 6 3)
    (hstrict : TwoMeetingLinesTransversalStrict design) :
    min (pivotLoadScore design 1) (pivotLoadScore design 2) < 1
      ∧ min (pivotLoadScore design 3) (pivotLoadScore design 4) < 1 := by
  obtain ⟨hfirst, hsecond⟩ := twoMeetingLines_privates_pivot_lt_one design hstrict
  constructor
  · rcases hfirst with h2 | h1
    · exact lt_of_le_of_lt (min_le_right _ _)
        ((pivotLoadScore_lt_one_iff design (by norm_num) 2).mpr h2)
    · exact lt_of_le_of_lt (min_le_left _ _)
        ((pivotLoadScore_lt_one_iff design (by norm_num) 1).mpr h1)
  · rcases hsecond with h4 | h3
    · exact lt_of_le_of_lt (min_le_right _ _)
        ((pivotLoadScore_lt_one_iff design (by norm_num) 4).mpr h4)
    · exact lt_of_le_of_lt (min_le_left _ _)
        ((pivotLoadScore_lt_one_iff design (by norm_num) 3).mpr h3)

/-- **THE UPPER WALL.**  A strict transversal forces the deficit strictly below
three.  Each of the three dropped labels sits below unit load. -/
theorem transversalDeficit_lt_three_of_transversalStrict
    (design : WeightedDesign 6 3)
    (hstrict : TwoMeetingLinesTransversalStrict design) :
    transversalDeficit design < 3 := by
  have hshared := shared_pivotLoadScore_lt_one_of_transversalStrict design hstrict
  obtain ⟨hfirst, hsecond⟩ :=
    private_min_pivotLoadScore_lt_one_of_transversalStrict design hstrict
  simp only [transversalDeficit]
  linarith

/-- The shared atom at unit pivot lifts the deficit above one, because the two
private minima are positive.  This gives the landed shared-atom exclusion a
quantitative home inside the ledger. -/
theorem one_lt_transversalDeficit_of_shared_pivot_ge_one
    (design : WeightedDesign 6 3)
    (hshared : 1 ≤ pivot design Finset.univ 0) :
    1 < transversalDeficit design := by
  have hload : 1 ≤ pivotLoadScore design 0 :=
    (one_le_pivotLoadScore_iff design (by norm_num) 0).mpr hshared
  have h1 : 0 < pivotLoadScore design 1 := pivotLoadScore_pos design (by norm_num) 1
  have h2 : 0 < pivotLoadScore design 2 := pivotLoadScore_pos design (by norm_num) 2
  have h3 : 0 < pivotLoadScore design 3 := pivotLoadScore_pos design (by norm_num) 3
  have h4 : 0 < pivotLoadScore design 4 := pivotLoadScore_pos design (by norm_num) 4
  have hmin12 : 0 < min (pivotLoadScore design 1) (pivotLoadScore design 2) := lt_min h1 h2
  have hmin34 : 0 < min (pivotLoadScore design 3) (pivotLoadScore design 4) := lt_min h3 h4
  simp only [transversalDeficit]
  linarith

/-- **THE RESIDUAL BAND.**  Under both line blind-spot hypotheses a design that
defeats the obligation lies strictly inside the deficit band `(1,3)`.  Below one
the criterion fires.  The upper wall is the contrapositive of the landed
exclusions. -/
theorem transversalDeficit_mem_Ioo_of_not_transversalStrict
    (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hblindFirst : IsLinePairLiftBlindAt design normalFirst {0, 1, 2})
    (hblindSecond : IsLinePairLiftBlindAt design normalSecond {0, 3, 4})
    (hfail : ¬ TwoMeetingLinesTransversalStrict design) :
    1 < transversalDeficit design :=
  one_lt_transversalDeficit_of_not_transversalStrict design normalFirst
    normalSecond hunitFirst hunitSecond horthFirst horthSecond hblindFirst
    hblindSecond hfail

/-! ## The squeeze law

The co-weight lies strictly between zero and one, so the load excess is a
strict contraction of the pivot excess.  The load therefore sits between the
pivot and one, on the same side of one as the pivot. -/

/-- The load never overshoots the pivot away from one. -/
theorem pivotLoadScore_le_max_pivot_one (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    pivotLoadScore D c ≤ max (pivot D Finset.univ c) 1 := by
  have hco : 0 < 1 - D.weight c := by
    have := weight_lt_one D hm c
    linarith
  have hcoLt : 1 - D.weight c ≤ 1 := by
    have := D.weight_pos c
    linarith
  have hexc := pivotLoadScore_sub_one D c
  rcases le_total 1 (pivot D Finset.univ c) with hge | hle
  · have hnn : 0 ≤ pivot D Finset.univ c - 1 := by linarith
    have : pivotLoadScore D c - 1 ≤ pivot D Finset.univ c - 1 := by
      rw [hexc]
      nlinarith [hnn, hcoLt]
    exact le_trans (by linarith) (le_max_left _ _)
  · have hnp : pivot D Finset.univ c - 1 ≤ 0 := by linarith
    have : pivotLoadScore D c - 1 ≤ 0 := by
      rw [hexc]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hco) hnp
    exact le_trans (by linarith) (le_max_right _ _)

/-- The load never undershoots the pivot away from one. -/
theorem min_pivot_one_le_pivotLoadScore (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    min (pivot D Finset.univ c) 1 ≤ pivotLoadScore D c := by
  have hco : 0 < 1 - D.weight c := by
    have := weight_lt_one D hm c
    linarith
  have hcoLt : 1 - D.weight c ≤ 1 := by
    have := D.weight_pos c
    linarith
  have hexc := pivotLoadScore_sub_one D c
  rcases le_total 1 (pivot D Finset.univ c) with hge | hle
  · have hnn : 0 ≤ pivot D Finset.univ c - 1 := by linarith
    have : 0 ≤ pivotLoadScore D c - 1 := by
      rw [hexc]
      exact mul_nonneg (le_of_lt hco) hnn
    exact le_trans (min_le_right _ _) (by linarith)
  · have hnp : pivot D Finset.univ c - 1 ≤ 0 := by linarith
    have : pivot D Finset.univ c - 1 ≤ pivotLoadScore D c - 1 := by
      rw [hexc]
      nlinarith [hnp, hcoLt]
    exact le_trans (min_le_left _ _) (by linarith)

/-! ## The deficit triple

The deficit is the load of an honest card-three set: the shared label together
with the lighter private label of each line.  Reading it that way replaces the
landed pivot exclusions by the landed load band, and gives BOTH walls at once. -/

private theorem sum_load_013 (D : WeightedDesign 6 3) :
    ∑ c ∈ ({0, 1, 3} : Finset (Fin 6)), pivotLoadScore D c
      = pivotLoadScore D 0 + pivotLoadScore D 1 + pivotLoadScore D 3 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem sum_load_014 (D : WeightedDesign 6 3) :
    ∑ c ∈ ({0, 1, 4} : Finset (Fin 6)), pivotLoadScore D c
      = pivotLoadScore D 0 + pivotLoadScore D 1 + pivotLoadScore D 4 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem sum_load_023 (D : WeightedDesign 6 3) :
    ∑ c ∈ ({0, 2, 3} : Finset (Fin 6)), pivotLoadScore D c
      = pivotLoadScore D 0 + pivotLoadScore D 2 + pivotLoadScore D 3 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem sum_load_024 (D : WeightedDesign 6 3) :
    ∑ c ∈ ({0, 2, 4} : Finset (Fin 6)), pivotLoadScore D c
      = pivotLoadScore D 0 + pivotLoadScore D 2 + pivotLoadScore D 4 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- **THE BAND, WITHOUT THE PIVOT EXCLUSIONS.**  A design with no strictly
dominating card-three set at all has deficit strictly inside `(1,3)`.  The
deficit IS a triple load, so the landed load band applies to it directly and
supplies both walls.  This route does not use the shared-atom exclusion or the
private-label exclusion. -/
theorem transversalDeficit_mem_Ioo_of_noStrict
    (design : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    transversalDeficit design ∈ Set.Ioo (1 : ℝ) 3 := by
  rcases le_total (pivotLoadScore design 1) (pivotLoadScore design 2) with h12 | h12 <;>
    rcases le_total (pivotLoadScore design 3) (pivotLoadScore design 4) with h34 | h34
  · have h := triple_pivotLoadScore_mem_Ioo_of_noStrict design hnoStrict
      ({0, 1, 3} : Finset (Fin 6)) (by decide)
    rw [sum_load_013] at h
    simpa only [transversalDeficit, min_eq_left h12, min_eq_left h34] using h
  · have h := triple_pivotLoadScore_mem_Ioo_of_noStrict design hnoStrict
      ({0, 1, 4} : Finset (Fin 6)) (by decide)
    rw [sum_load_014] at h
    simpa only [transversalDeficit, min_eq_left h12, min_eq_right h34] using h
  · have h := triple_pivotLoadScore_mem_Ioo_of_noStrict design hnoStrict
      ({0, 2, 3} : Finset (Fin 6)) (by decide)
    rw [sum_load_023] at h
    simpa only [transversalDeficit, min_eq_right h12, min_eq_left h34] using h
  · have h := triple_pivotLoadScore_mem_Ioo_of_noStrict design hnoStrict
      ({0, 2, 4} : Finset (Fin 6)) (by decide)
    rw [sum_load_024] at h
    simpa only [transversalDeficit, min_eq_right h12, min_eq_right h34] using h

/-- **THE UNIVERSAL WALL.**  Under both line blind-spot hypotheses NO design of
the stratum reaches deficit three, whether or not it has a strict transversal.
The strict branch is the upper wall and the failing branch is the load band. -/
theorem transversalDeficit_lt_three
    (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hblindFirst : IsLinePairLiftBlindAt design normalFirst {0, 1, 2})
    (hblindSecond : IsLinePairLiftBlindAt design normalSecond {0, 3, 4}) :
    transversalDeficit design < 3 := by
  by_cases hstrict : TwoMeetingLinesTransversalStrict design
  · exact transversalDeficit_lt_three_of_transversalStrict design hstrict
  · have hno := (noStrict_iff_not_twoMeetingLinesTransversalStrict_of_blind design
      normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond).mpr hstrict
    exact (transversalDeficit_mem_Ioo_of_noStrict design hno).2

/-- **THE DICHOTOMY.**  Under both blind-spot hypotheses every design of the
stratum either has a strictly dominating transversal, or sits strictly inside
the deficit band.  The band is therefore the exact open content of the
two-meeting-lines obligation, read as one scalar. -/
theorem transversalStrict_or_deficit_mem_Ioo
    (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hblindFirst : IsLinePairLiftBlindAt design normalFirst {0, 1, 2})
    (hblindSecond : IsLinePairLiftBlindAt design normalSecond {0, 3, 4}) :
    TwoMeetingLinesTransversalStrict design
      ∨ transversalDeficit design ∈ Set.Ioo (1 : ℝ) 3 := by
  by_cases hstrict : TwoMeetingLinesTransversalStrict design
  · exact Or.inl hstrict
  · refine Or.inr ?_
    have hno := (noStrict_iff_not_twoMeetingLinesTransversalStrict_of_blind design
      normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond).mpr hstrict
    exact transversalDeficit_mem_Ioo_of_noStrict design hno

/-- The heaviest transversal carries load `4 - deficit`, so the band on the
deficit is the same band on the heaviest transversal. -/
theorem maxTransversalLoad_mem_Ioo_of_noStrict
    (design : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    max (pivotLoadScore design 1) (pivotLoadScore design 2)
        + max (pivotLoadScore design 3) (pivotLoadScore design 4)
        + pivotLoadScore design 5 ∈ Set.Ioo (1 : ℝ) 3 := by
  obtain ⟨hlow, hhigh⟩ := transversalDeficit_mem_Ioo_of_noStrict design hnoStrict
  have hpart := transversalDeficit_add_max design
  exact ⟨by linarith, by linarith⟩

/-! ## The closed door

The counting laws of this ledger are: every load is positive, the six loads sum
to four, and under a blind design every card-three load sum lies strictly
between one and three.  The profile below satisfies all three and still carries
unit load at the shared label.  So no argument that reads only the load vector
can exclude a shared atom at unit pivot, and the incompatibility question needs
the geometry of the two lines rather than the ledger. -/

/-- A load profile that meets every counting law of the ledger and carries unit
load at the shared label. -/
noncomputable def ledgerEscapeProfile : Fin 6 → ℝ :=
  fun c => if c = 0 then 1 else 3/5

theorem ledgerEscapeProfile_shared : ledgerEscapeProfile 0 = 1 := by
  simp only [ledgerEscapeProfile, if_pos]

theorem ledgerEscapeProfile_eq_add (c : Fin 6) :
    ledgerEscapeProfile c = 3/5 + (if c = 0 then (2/5 : ℝ) else 0) := by
  simp only [ledgerEscapeProfile]
  split <;> norm_num

theorem ledgerEscapeProfile_pos (c : Fin 6) : 0 < ledgerEscapeProfile c := by
  simp only [ledgerEscapeProfile]
  split <;> norm_num

theorem sum_ledgerEscapeProfile : ∑ c, ledgerEscapeProfile c = 4 := by
  rw [Finset.sum_congr rfl fun c _ => ledgerEscapeProfile_eq_add c,
    Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_ite_eq' Finset.univ (0 : Fin 6) fun _ => (2/5 : ℝ)]
  simp
  norm_num

/-- Every card-three sum of the escape profile lies strictly inside the band. -/
theorem ledgerEscapeProfile_triple_mem_Ioo (S : Finset (Fin 6)) (hcard : S.card = 3) :
    ∑ c ∈ S, ledgerEscapeProfile c ∈ Set.Ioo (1 : ℝ) 3 := by
  have hrw : ∑ c ∈ S, ledgerEscapeProfile c
      = (S.card : ℝ) * (3/5) + (if (0 : Fin 6) ∈ S then (2/5 : ℝ) else 0) := by
    rw [Finset.sum_congr rfl fun c _ => ledgerEscapeProfile_eq_add c,
      Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_ite_eq' S (0 : Fin 6) fun _ => (2/5 : ℝ)]
    simp
  rw [hrw, hcard]
  split <;> constructor <;> norm_num

/-- **THE CLOSED DOOR.**  The counting laws of the load ledger are consistent
with a shared atom at unit load.  A refutation of the shared-atom route cannot
come from the ledger alone. -/
theorem ledger_counting_admits_unit_shared_load :
    ∃ profile : Fin 6 → ℝ,
      (∀ c, 0 < profile c)
        ∧ (∑ c, profile c = 4)
        ∧ (∀ S : Finset (Fin 6), S.card = 3 →
            ∑ c ∈ S, profile c ∈ Set.Ioo (1 : ℝ) 3)
        ∧ profile 0 = 1 :=
  ⟨ledgerEscapeProfile, ledgerEscapeProfile_pos, sum_ledgerEscapeProfile,
    ledgerEscapeProfile_triple_mem_Ioo, ledgerEscapeProfile_shared⟩

end Gtz
