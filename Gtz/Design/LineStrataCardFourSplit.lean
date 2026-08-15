import Gtz.Design.WeightedFormCriterion
import Gtz.Design.DesignDescentPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The card-four split of the line strata, and the exact normal reading

The descent port makes both line obligations a card-four stall escape at their
stratum.  This module supplies the combinatorial spine of that escape and the
one reading the line supplies for free.

## The normal reading

At a probe every atom of a flat set reads zero on, the gap of ANY selection
reads its atoms OUTSIDE the flat set alone, against the probe energy:

  `probe ⬝ (gap S) probe = ∑_{c ∈ S \ flat} (atom c ⬝ probe)² − probe ⬝ probe`

The selected flat atoms contribute nothing.  Two consequences are immediate: a
selection inside the flat set is never positive definite, and a selection
meeting the flat set in all but one label has its whole reading carried by that
one atom.

## The splits

At one line the coplanar triple is `{0,1,2}` and the free triple is `{3,4,5}`.
The fifteen card-four selections split by how many line atoms they hold as
**3 / 9 / 3** — three hold the whole line, nine hold exactly two line atoms,
three hold exactly one.  No selection avoids the line entirely, because only
three free atoms exist.

At two meeting lines the pattern is `[[0,1,2],[0,3,4]]`.  Three card-four
selections hold the first line, three hold the second, and **no selection holds
both**, because the two lines together span five labels.

## What the normal pin does NOT do

The unit law caps the same reading from the other side: at the line normal the
complement carries exactly one unit of weighted energy, so the single free atom
of a whole-line selection satisfies `weight · reading ≤ 1`.  Combined with the
positive definiteness requirement `reading > 1` this yields only
`weight < 1`, which EVERY design satisfies.  The two bounds do not close the
whole-line cases.  `oneLine_wholeLine_posDef_weight_lt_one` records the exact
strength of that pin so no successor spends a fork on it.
-/

namespace Gtz

open Finset Matrix

variable {size rank : ℕ}

/-! ## The exact reading at a flat probe -/

/-- **THE FLAT-PROBE READING.**  At a probe every atom of `flat` reads zero on,
the gap of `selected` reads only the atoms of `selected` outside `flat`.  The
selected flat atoms contribute nothing, whatever the selection is. -/
theorem gap_quadForm_at_flat_probe (design : WeightedDesign size rank)
    (selected flat : Finset (Fin size)) (probe : Fin rank → ℝ)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ probe = 0) :
    probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe)
      = (∑ label ∈ selected \ flat, (design.atom label ⬝ᵥ probe) ^ 2)
        - probe ⬝ᵥ probe := by
  rw [dotProduct_gapForm_eq_readings_sub_energy]
  have hinter : (∑ label ∈ selected ∩ flat, (design.atom label ⬝ᵥ probe) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun label hlabel => ?_
    rw [hflat label (Finset.mem_of_mem_inter_right hlabel)]
    ring
  have hset : selected \ (selected ∩ flat) = selected \ flat := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsubi : selected ∩ flat ⊆ selected := Finset.inter_subset_left
  have hsplit := Finset.sum_sdiff (f := fun label => (design.atom label ⬝ᵥ probe) ^ 2) hsubi
  rw [hset, hinter, add_zero] at hsplit
  rw [hsplit]

/-- A selection contained in the flat set is never positive definite: at the
flat probe its gap reads minus the probe energy. -/
theorem not_posDef_gap_of_subset_flat (design : WeightedDesign size rank)
    (selected flat : Finset (Fin size)) (probe : Fin rank → ℝ)
    (hprobe : probe ≠ 0) (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ probe = 0)
    (hsub : selected ⊆ flat) :
    ¬ (subsetSum design selected - 1).PosDef := by
  intro hposDef
  have hread := gap_quadForm_at_flat_probe design selected flat probe hflat
  rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.sum_empty, zero_sub] at hread
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
  simp only [star_trivial] at hpos
  have henergy : 0 < probe ⬝ᵥ probe := by
    rcases (dotProduct_self_nonneg probe).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (dotProduct_self_eq_zero.mp heq.symm) hprobe
  rw [hread] at hpos
  linarith

/-- **The single-atom reading.**  A selection that holds the whole flat set plus
one outside label has its entire gap reading at the flat probe carried by that
one atom. -/
theorem gap_quadForm_insert_flat (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (free : Fin size) (hfree : free ∉ flat)
    (probe : Fin rank → ℝ) (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ probe = 0) :
    probe ⬝ᵥ ((subsetSum design (insert free flat) - 1) *ᵥ probe)
      = (design.atom free ⬝ᵥ probe) ^ 2 - probe ⬝ᵥ probe := by
  have hsd : (insert free flat) \ flat = {free} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hnot⟩
      rcases hx with rfl | hx
      · rfl
      · exact absurd hx hnot
    · rintro rfl
      exact ⟨Or.inl rfl, hfree⟩
  rw [gap_quadForm_at_flat_probe design (insert free flat) flat probe hflat, hsd,
    Finset.sum_singleton]

/-- Positive definiteness of a whole-flat-plus-one selection forces its single
outside atom to read strictly above the probe energy. -/
theorem energy_lt_reading_of_posDef_insert_flat (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (free : Fin size) (hfree : free ∉ flat)
    (probe : Fin rank → ℝ) (hprobe : probe ≠ 0)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ probe = 0)
    (hposDef : (subsetSum design (insert free flat) - 1).PosDef) :
    probe ⬝ᵥ probe < (design.atom free ⬝ᵥ probe) ^ 2 := by
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
  simp only [star_trivial] at hpos
  rw [gap_quadForm_insert_flat design flat free hfree probe hflat] at hpos
  linarith

/-- **THE FLAT SET MUST DOMINATE ON THE FREE ATOM'S ORTHOGONAL COMPLEMENT.**

A whole-flat-plus-one selection is positive definite only if the flat atoms
ALONE beat the probe energy at every probe the single outside atom reads zero
on.  The outside atom is blind there, so it can lend no help.

At one line this says the three coplanar atoms must strictly dominate the
identity on the two-dimensional space orthogonal to the free atom — a rank-two
domination statement, stated here with no plane machinery.  It is the structural
handle the whole-line branch of the escape turns on. -/
theorem flat_dominates_on_free_orthogonal (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (free : Fin size) (hfree : free ∉ flat)
    (hposDef : (subsetSum design (insert free flat) - 1).PosDef)
    (probe : Fin rank → ℝ) (hprobe : probe ≠ 0)
    (hblind : design.atom free ⬝ᵥ probe = 0) :
    probe ⬝ᵥ probe < ∑ label ∈ flat, (design.atom label ⬝ᵥ probe) ^ 2 := by
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
  simp only [star_trivial] at hpos
  rw [dotProduct_gapForm_eq_readings_sub_energy, Finset.sum_insert hfree,
    hblind] at hpos
  have hzero : (0 : ℝ) ^ 2 = 0 := by ring
  rw [hzero, zero_add] at hpos
  linarith

/-! ## The card-four splits, by decision -/

/-- **The one-line card-four split.**  Every card-four selection holds one, two
or three of the three coplanar labels.  None avoids the line, because only three
free labels exist. -/
theorem oneLine_cardFour_lineCount :
    ∀ selected : Finset (Fin 6), selected.card = 4 →
      (selected ∩ ({0, 1, 2} : Finset (Fin 6))).card = 1
      ∨ (selected ∩ ({0, 1, 2} : Finset (Fin 6))).card = 2
      ∨ (selected ∩ ({0, 1, 2} : Finset (Fin 6))).card = 3 := by
  decide

/-- The three card-four selections holding the whole line, named. -/
theorem oneLine_wholeLine_cardFour_eq :
    ∀ selected : Finset (Fin 6), selected.card = 4 →
      ({0, 1, 2} : Finset (Fin 6)) ⊆ selected →
        selected = ({0, 1, 2, 3} : Finset (Fin 6))
        ∨ selected = ({0, 1, 2, 4} : Finset (Fin 6))
        ∨ selected = ({0, 1, 2, 5} : Finset (Fin 6)) := by
  decide

/-- Exactly three card-four selections hold the whole line. -/
theorem oneLine_wholeLine_cardFour_card :
    (Finset.univ.filter (fun selected : Finset (Fin 6) =>
      selected.card = 4 ∧ ({0, 1, 2} : Finset (Fin 6)) ⊆ selected)).card = 3 := by
  decide

/-- Exactly nine card-four selections hold exactly two line labels. -/
theorem oneLine_twoLine_cardFour_card :
    (Finset.univ.filter (fun selected : Finset (Fin 6) =>
      selected.card = 4 ∧ (selected ∩ ({0, 1, 2} : Finset (Fin 6))).card = 2)).card = 9 := by
  decide

/-- **No card-four selection holds both meeting lines.**  The two lines share
one label and together span five, so a card-four selection cannot contain both.
The whole-line branch of the two-meeting-lines escape is therefore a disjoint
three-plus-three, never a joint case. -/
theorem twoMeetingLines_cardFour_not_both_lines :
    ∀ selected : Finset (Fin 6), selected.card = 4 →
      ¬ (({0, 1, 2} : Finset (Fin 6)) ⊆ selected
        ∧ ({0, 3, 4} : Finset (Fin 6)) ⊆ selected) := by
  decide

/-- The three card-four selections holding the second meeting line, named. -/
theorem twoMeetingLines_secondLine_cardFour_eq :
    ∀ selected : Finset (Fin 6), selected.card = 4 →
      ({0, 3, 4} : Finset (Fin 6)) ⊆ selected →
        selected = ({0, 1, 3, 4} : Finset (Fin 6))
        ∨ selected = ({0, 2, 3, 4} : Finset (Fin 6))
        ∨ selected = ({0, 3, 4, 5} : Finset (Fin 6)) := by
  decide

/-! ## The exact strength of the normal pin -/

/-- **THE PIN IS VACUOUS, AND THIS RECORDS ITS EXACT STRENGTH.**

At the line normal the unit law gives the complement exactly one unit of
weighted energy, so the single free atom of a whole-line card-four selection
satisfies `weight · reading ≤ 1`.  Positive definiteness gives `reading > 1`.
The two together yield only `weight < 1`, which every weighted design satisfies
outright.

The normal pin therefore does NOT close the three whole-line selections.  It is
stated here so that no successor spends a fork rediscovering that. -/
theorem oneLine_wholeLine_posDef_weight_lt_one (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (free : Fin size) (hfree : free ∉ flat)
    (probe : Fin rank → ℝ) (hprobe : probe ≠ 0) (hunit : probe ⬝ᵥ probe = 1)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ probe = 0)
    (hposDef : (subsetSum design (insert free flat) - 1).PosDef) :
    design.weight free < 1 := by
  have hgt : 1 < (design.atom free ⬝ᵥ probe) ^ 2 := by
    have := energy_lt_reading_of_posDef_insert_flat design flat free hfree probe
      hprobe hflat hposDef
    rwa [hunit] at this
  have hcompl := sum_compl_weighted_sq_eq_energy_of_orthogonal design flat probe hflat
  have hmem : free ∈ flatᶜ := Finset.mem_compl.mpr hfree
  have hsingle : design.weight free * (design.atom free ⬝ᵥ probe) ^ 2
      ≤ ∑ label ∈ flatᶜ, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 :=
    Finset.single_le_sum
      (f := fun label => design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
      (fun label _ => mul_nonneg (design.weight_pos label).le (sq_nonneg _)) hmem
  rw [hcompl, hunit] at hsingle
  nlinarith [design.weight_pos free]

end Gtz
