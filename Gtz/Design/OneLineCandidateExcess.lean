/-
# The excess classification of the ten plane-branch candidates

`Gtz.PlaneBranchTenCandidate` is a disjunction over ten card-three selections at
the one-line stratum: the nine that hold exactly one line atom, and the free
triple `{3,4,5}` that holds none.  `Gtz.flatSplit_posDef_iff` splits each of them
into an EXCESS condition and a PLANE inequality, and
`Gtz.flatSplit_posDef_iff_planeInequality` discharges the criterion as soon as
the excess holds.

`Gtz.exists_complementAtom_overcovers_normal` supplies ONE free label whose
squared normal reading already exceeds the probe energy.  A selection's excess
reads only the labels it holds OUTSIDE the line, and every remaining term is a
square.  So a selection that holds that one label clears the excess, whatever
else it holds.

Seven of the ten hold it: the free triple, and the six that pair it with a line
atom and one other free atom.  `Gtz.planeBranchTenList_filter_mem_length` counts
them by decision.

The three that do not are `{j} ∪ ({3,4,5} \ {f})` for the three line atoms `j`.
Their excess conditions are the SAME statement.  The set difference removes the
line atom, so the three selections differ in no term of the excess sum.  Either
all three clear it or none do, and one scalar decides which.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.FreePairPlane
import Gtz.Design.LineClassObstructions
import Gtz.Design.FlatNormalBudget

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The generic engine -/

/-- **One over-covering label carries the whole excess.**  The excess sum runs
over the labels a selection holds outside the flat set, and every term is a
square.  A single term above one therefore lifts the sum above one, whatever the
selection holds besides.  Generic in the size, the rank, the selection and the
flat set. -/
theorem excess_of_mem_sdiff_of_one_lt_sq (design : WeightedDesign size rank)
    (selected flat : Finset (Fin size)) (normalVec : Fin rank → ℝ)
    (freeLabel : Fin size) (hmem : freeLabel ∈ selected \ flat)
    (hover : 1 < (design.atom freeLabel ⬝ᵥ normalVec) ^ 2) :
    1 < ∑ label ∈ selected \ flat, (design.atom label ⬝ᵥ normalVec) ^ 2 :=
  lt_of_lt_of_le hover
    (Finset.single_le_sum
      (f := fun label => (design.atom label ⬝ᵥ normalVec) ^ 2)
      (fun _ _ => sq_nonneg _) hmem)

/-! ## The one-line stratum -/

/-- The line atoms and the free atoms are disjoint. -/
theorem oneLine_free_not_mem_line (freeLabel : Fin 6)
    (hmem : freeLabel ∈ ({3, 4, 5} : Finset (Fin 6))) :
    freeLabel ∉ ({0, 1, 2} : Finset (Fin 6)) := by
  revert hmem
  revert freeLabel
  decide

/-- **The over-covering free label at the one-line stratum.**  At a unit normal
that every line atom kills, some free atom alone reads above one. -/
theorem oneLine_exists_free_one_lt_sq (design : WeightedDesign 6 3)
    (normalVec : Fin 3 → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normalVec = 0) :
    ∃ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      1 < (design.atom freeLabel ⬝ᵥ normalVec) ^ 2 := by
  have hnormalNe : normalVec ≠ 0 := by
    intro hzero
    rw [hzero, zero_dotProduct] at hunit
    norm_num at hunit
  have hcompl : (({0, 1, 2} : Finset (Fin 6)))ᶜ = ({3, 4, 5} : Finset (Fin 6)) := by
    decide
  obtain ⟨freeLabel, hmem, hover⟩ :=
    exists_complementAtom_overcovers_normal design ({0, 1, 2} : Finset (Fin 6))
      normalVec (by norm_num) hnormalNe hflat
  rw [hcompl] at hmem
  exact ⟨freeLabel, hmem, by rwa [hunit] at hover⟩

/-- **Seven of the ten clear the excess unconditionally.**  One free label reads
above one, and every selection holding it clears the excess whatever else it
holds.  The seven are the free triple and the six that pair the label with a
line atom and one other free atom. -/
theorem oneLine_seven_of_ten_excess (design : WeightedDesign 6 3)
    (normalVec : Fin 3 → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normalVec = 0) :
    ∃ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      1 < (design.atom freeLabel ⬝ᵥ normalVec) ^ 2 ∧
        ∀ selected : Finset (Fin 6), freeLabel ∈ selected →
          1 < ∑ label ∈ selected \ ({0, 1, 2} : Finset (Fin 6)),
            (design.atom label ⬝ᵥ normalVec) ^ 2 := by
  obtain ⟨freeLabel, hmem, hover⟩ :=
    oneLine_exists_free_one_lt_sq design normalVec hunit hflat
  refine ⟨freeLabel, hmem, hover, fun selected hsel => ?_⟩
  exact excess_of_mem_sdiff_of_one_lt_sq design selected
    ({0, 1, 2} : Finset (Fin 6)) normalVec freeLabel
    (Finset.mem_sdiff.mpr ⟨hsel, oneLine_free_not_mem_line freeLabel hmem⟩) hover

/-- **Every selection holding the over-covering label is decided by its plane
inequality alone.**  This is the reduction for the seven, stated once. -/
theorem oneLine_posDef_iff_planeInequality_of_mem (design : WeightedDesign 6 3)
    (normalVec : Fin 3 → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normalVec = 0)
    (freeLabel : Fin 6) (hfree : freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hover : 1 < (design.atom freeLabel ⬝ᵥ normalVec) ^ 2)
    (selected : Finset (Fin 6)) (hsel : freeLabel ∈ selected) :
    (subsetSum design selected - 1).PosDef ↔
      ∀ planeProbe : Fin 3 → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
        (∑ label ∈ selected \ ({0, 1, 2} : Finset (Fin 6)),
            (design.atom label ⬝ᵥ planeProbe)
              * (design.atom label ⬝ᵥ normalVec)) ^ 2
          < ((∑ label ∈ selected \ ({0, 1, 2} : Finset (Fin 6)),
                (design.atom label ⬝ᵥ normalVec) ^ 2) - 1)
            * ((∑ label ∈ selected,
                  (design.atom label ⬝ᵥ planeProbe) ^ 2)
                - planeProbe ⬝ᵥ planeProbe) :=
  flatSplit_posDef_iff_planeInequality design selected
    ({0, 1, 2} : Finset (Fin 6)) normalVec hunit hflat
    (excess_of_mem_sdiff_of_one_lt_sq design selected
      ({0, 1, 2} : Finset (Fin 6)) normalVec freeLabel
      (Finset.mem_sdiff.mpr ⟨hsel, oneLine_free_not_mem_line freeLabel hfree⟩)
      hover)

/-! ## The count -/

/-- The ten plane-branch candidates as a list. -/
def planeBranchTenList : List (Finset (Fin 6)) :=
  [{0, 3, 4}, {0, 3, 5}, {0, 4, 5}, {1, 3, 4}, {1, 3, 5}, {1, 4, 5},
    {2, 3, 4}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}]

/-- The list carries exactly the ten candidates. -/
theorem planeBranchTenList_length : planeBranchTenList.length = 10 := by decide

/-- **Seven of ten, counted.**  Whichever free label over-covers, exactly seven
of the ten candidates hold it. -/
theorem planeBranchTenList_filter_mem_length (freeLabel : Fin 6)
    (hmem : freeLabel ∈ ({3, 4, 5} : Finset (Fin 6))) :
    (planeBranchTenList.filter (fun selected => freeLabel ∈ selected)).length = 7 := by
  revert hmem
  revert freeLabel
  decide

/-- **Three of ten, counted.**  The three that miss the over-covering label are
the three that pair a line atom with the two other free atoms. -/
theorem planeBranchTenList_filter_not_mem_length (freeLabel : Fin 6)
    (hmem : freeLabel ∈ ({3, 4, 5} : Finset (Fin 6))) :
    (planeBranchTenList.filter
      (fun selected => ¬ freeLabel ∈ selected)).length = 3 := by
  revert hmem
  revert freeLabel
  decide

/-! ## The three that remain share one condition -/

/-- **The line atom leaves no trace in the excess.**  A candidate holding one
line atom and a free pair reads its excess on the free pair alone. -/
theorem oneLine_insert_sdiff_line (lineLabel : Fin 6)
    (hline : lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (freePair : Finset (Fin 6)) (hsub : freePair ⊆ ({3, 4, 5} : Finset (Fin 6))) :
    (insert lineLabel freePair) \ ({0, 1, 2} : Finset (Fin 6)) = freePair := by
  rw [Finset.insert_sdiff_of_mem _ hline]
  refine Finset.sdiff_eq_self_of_disjoint ?_
  refine Finset.disjoint_left.mpr fun label hlabel hcontra => ?_
  exact oneLine_free_not_mem_line label (hsub hlabel) hcontra

/-- **The three remaining candidates share ONE excess condition.**  Their excess
sums are literally the same sum, so the three differ in no term.  Either all
three clear the excess or none of them do, and one scalar decides which. -/
theorem oneLine_remaining_excess_shared (design : WeightedDesign 6 3)
    (normalVec : Fin 3 → ℝ)
    (freePair : Finset (Fin 6)) (hsub : freePair ⊆ ({3, 4, 5} : Finset (Fin 6)))
    (lineLabel lineLabel' : Fin 6)
    (hline : lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hline' : lineLabel' ∈ ({0, 1, 2} : Finset (Fin 6))) :
    (∑ label ∈ (insert lineLabel freePair) \ ({0, 1, 2} : Finset (Fin 6)),
        (design.atom label ⬝ᵥ normalVec) ^ 2)
      = ∑ label ∈ (insert lineLabel' freePair) \ ({0, 1, 2} : Finset (Fin 6)),
          (design.atom label ⬝ᵥ normalVec) ^ 2 := by
  rw [oneLine_insert_sdiff_line lineLabel hline freePair hsub,
    oneLine_insert_sdiff_line lineLabel' hline' freePair hsub]

/-- **The three remaining candidates, decided together.**  When the free pair
outside the over-covering label clears the excess, each of the three is decided
by its plane inequality alone. -/
theorem oneLine_remaining_posDef_iff_planeInequality (design : WeightedDesign 6 3)
    (normalVec : Fin 3 → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normalVec = 0)
    (freePair : Finset (Fin 6)) (hsub : freePair ⊆ ({3, 4, 5} : Finset (Fin 6)))
    (lineLabel : Fin 6) (hline : lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hexcess : 1 < ∑ label ∈ freePair,
      (design.atom label ⬝ᵥ normalVec) ^ 2) :
    (subsetSum design (insert lineLabel freePair) - 1).PosDef ↔
      ∀ planeProbe : Fin 3 → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
        (∑ label ∈ freePair,
            (design.atom label ⬝ᵥ planeProbe)
              * (design.atom label ⬝ᵥ normalVec)) ^ 2
          < ((∑ label ∈ freePair,
                (design.atom label ⬝ᵥ normalVec) ^ 2) - 1)
            * ((∑ label ∈ insert lineLabel freePair,
                  (design.atom label ⬝ᵥ planeProbe) ^ 2)
                - planeProbe ⬝ᵥ planeProbe) := by
  have hsdiff := oneLine_insert_sdiff_line lineLabel hline freePair hsub
  have hmain := flatSplit_posDef_iff_planeInequality design
    (insert lineLabel freePair) ({0, 1, 2} : Finset (Fin 6)) normalVec hunit hflat
    (by rw [hsdiff]; exact hexcess)
  rwa [hsdiff] at hmain

end Gtz
