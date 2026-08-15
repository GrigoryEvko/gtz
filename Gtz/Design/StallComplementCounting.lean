import Gtz.Design.CardFourStallEquivalence
import Gtz.Design.StallTypeSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Counting positive definite sets at a stall, and why the count repackages

The card-four stall branch has been attacked by escaping *from* the stall.  The
landed equivalence `strictTree_iff_exists_nonStalledCardFour` asks for less: any
non-stalled positive definite four-set at the point serves as the witness, not
only an exchange neighbour of the stall.  This module measures that freedom and
finds it empty.

* `posDef_insert_pivot_lt_one` — the extension step.  A positive definite
  selection stays positive definite when a label is added, and the added label
  then carries pivot below one.  Generic in the size and the direction family.
* `nonStalled_cardFour_of_posDef_cardThree` — **the counting floor**.  Every
  label outside a positive definite triple extends it to a positive definite
  four-set that the triple itself un-stalls.  In a six-label chart a triple has
  three outside labels, so one strict triple already produces three non-stalled
  four-sets.  The observed floor of three is the image of the floor of one.
* `not_subset_of_posDef_of_stall` — a stall is a minimal positive definite set,
  so no smaller positive definite selection sits inside it.
* `posDef_cardThree_meets_compl_of_cardFour_stall` — at a card-four stall every
  positive definite triple meets the two-label complement.
* `exists_nonStalled_cardFour_supset_compl_of_stall` — **the complement-pair
  escape**.  At a card-four stall, whenever a strict triple exists somewhere at
  the point, some non-stalled positive definite four-set contains *both*
  complement labels.

The last statement is the sharpest counting law that survives, and it is proved
here *from* the existence of a strict triple.  Together with the landed
equivalence that reads the implication back, the complement-restricted count is
therefore equivalent to the chart statement it was meant to reduce.  Counting
positive definite sets at a stall repackages the target, exactly as the
unrestricted card-four branch does.

The corresponding statement one level down is false: a positive definite
*triple* containing both complement labels need not exist.
-/

namespace Gtz

open Finset

/-- Adding a label to a positive definite selection keeps positive definiteness,
and the added label then carries chart ladder pivot below one. -/
theorem posDef_insert_pivot_lt_one {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {selected : Finset (Fin size)} {added : Fin size} (hadded : added ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef) :
    (directionChartGap direction mass weight (insert added selected)).PosDef
      ∧ chartLadderPivot direction mass weight (insert added selected) added < 1 := by
  have hbig : (directionChartGap direction mass weight (insert added selected)).PosDef :=
    posDef_directionChartGap_of_subset direction mass weight hmass hweight
      (Finset.subset_insert _ _) hpd
  refine ⟨hbig, ?_⟩
  refine (posDef_directionChartGap_erase_iff direction mass weight hmass hweight _
    (Finset.mem_insert_self added selected) hbig).mp ?_
  rwa [Finset.erase_insert hadded]

/-- **THE COUNTING FLOOR.**  Every label outside a positive definite triple
extends it to a non-stalled positive definite four-set.  A triple of a six-label
chart has three outside labels, so one strict triple already supplies three
non-stalled four-sets: the observed floor of three is the image of the floor of
one, and carries no information beyond it. -/
theorem nonStalled_cardFour_of_posDef_cardThree
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hcard : tree.card = 3)
    (hpd : (directionChartGap kFourDirection point.mass point.weight tree).PosDef)
    {added : Fin 6} (hadded : added ∉ tree) :
    (insert added tree).card = 4
      ∧ (directionChartGap kFourDirection point.mass point.weight
          (insert added tree)).PosDef
      ∧ ∃ label ∈ insert added tree,
          chartLadderPivot kFourDirection point.mass point.weight
            (insert added tree) label < 1 := by
  obtain ⟨hbig, hpivot⟩ := posDef_insert_pivot_lt_one kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos hadded hpd
  exact ⟨by rw [Finset.card_insert_of_notMem hadded, hcard], hbig,
    added, Finset.mem_insert_self _ _, hpivot⟩

/-- A stall is a minimal positive definite selection, so no strictly smaller
positive definite selection is contained in it. -/
theorem not_subset_of_posDef_of_stall {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {stalled smaller : Finset (Fin size)}
    (hpd : (directionChartGap direction mass weight stalled).PosDef)
    (hstall : ∀ label ∈ stalled,
      1 ≤ chartLadderPivot direction mass weight stalled label)
    (hsmallPd : (directionChartGap direction mass weight smaller).PosDef)
    (hcard : smaller.card < stalled.card) :
    ¬ smaller ⊆ stalled := by
  intro hsub
  have hne : smaller ≠ stalled := by
    intro heq
    rw [heq] at hcard
    omega
  exact ((stall_iff_minimal_posDef direction mass weight hmass hweight stalled
    hpd).mp hstall) smaller (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩) hsmallPd

/-- At a card-four stall every positive definite triple meets the two-label
complement of the stall. -/
theorem posDef_cardThree_meets_compl_of_cardFour_stall
    (point : DirectionChartPoint 6) {stalled tree : Finset (Fin 6)}
    (hcard : stalled.card = 4)
    (hpd : (directionChartGap kFourDirection point.mass point.weight stalled).PosDef)
    (hstall : ∀ label ∈ stalled,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight stalled label)
    (htcard : tree.card = 3)
    (htpd : (directionChartGap kFourDirection point.mass point.weight tree).PosDef) :
    ∃ label ∈ tree, label ∉ stalled := by
  have hnot := not_subset_of_posDef_of_stall kFourDirection point.mass point.weight
    point.mass_pos point.weight_pos hpd hstall htpd (by omega)
  by_contra hall
  push Not at hall
  exact hnot hall

/-- **THE COMPLEMENT-PAIR ESCAPE.**  At a card-four stall, a strict triple
anywhere at the point already produces a non-stalled positive definite four-set
that contains *both* complement labels.

The stall is a minimal positive definite set, so the triple must leave it.  If
the triple already holds both complement labels, extend it by any outside label.
Otherwise it holds exactly one, and extending by the other reaches a four-set
holding the pair.  Either way the extension is positive definite and the added
label carries pivot below one.

Read with `strictTree_iff_exists_nonStalledCardFour`, which returns the strict
triple from a non-stalled four-set, this makes the complement-restricted count
equivalent to the chart statement rather than a reduction of it. -/
theorem exists_nonStalled_cardFour_supset_compl_of_stall
    (point : DirectionChartPoint 6) {stalled tree : Finset (Fin 6)}
    (hcard : stalled.card = 4)
    (hpd : (directionChartGap kFourDirection point.mass point.weight stalled).PosDef)
    (hstall : ∀ label ∈ stalled,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight stalled label)
    (htcard : tree.card = 3)
    (htpd : (directionChartGap kFourDirection point.mass point.weight tree).PosDef) :
    ∃ big : Finset (Fin 6), big.card = 4 ∧ stalledᶜ ⊆ big
      ∧ (directionChartGap kFourDirection point.mass point.weight big).PosDef
      ∧ ∃ label ∈ big, chartLadderPivot kFourDirection point.mass point.weight
          big label < 1 := by
  obtain ⟨inside, hinsideTree, hinsideOut⟩ :=
    posDef_cardThree_meets_compl_of_cardFour_stall point hcard hpd hstall htcard htpd
  have hcompl : stalledᶜ.card = 2 := by
    rw [Finset.card_compl, hcard]
    simp
  have hinsideCompl : inside ∈ stalledᶜ := Finset.mem_compl.mpr hinsideOut
  -- choose the label to add: the complement label outside the triple if there is
  -- one, and otherwise any label outside the triple at all
  rcases Finset.eq_empty_or_nonempty (stalledᶜ \ tree) with hempty | ⟨outside, houtside⟩
  · -- the triple already holds both complement labels
    obtain ⟨added, hadded⟩ : ∃ added : Fin 6, added ∉ tree := by
      by_contra hall
      push Not at hall
      have : (Finset.univ : Finset (Fin 6)) ⊆ tree := fun label _ => hall label
      have hle := Finset.card_le_card this
      simp [htcard] at hle
    obtain ⟨hbig, hpivot⟩ := posDef_insert_pivot_lt_one kFourDirection point.mass
      point.weight point.mass_pos point.weight_pos hadded htpd
    refine ⟨insert added tree, by rw [Finset.card_insert_of_notMem hadded, htcard],
      ?_, hbig, added, Finset.mem_insert_self _ _, hpivot⟩
    intro label hlabel
    refine Finset.mem_insert_of_mem ?_
    by_contra hnot
    exact (Finset.notMem_empty label) (hempty ▸ Finset.mem_sdiff.mpr ⟨hlabel, hnot⟩)
  · -- the triple holds exactly one complement label; add the other
    obtain ⟨houtsideCompl, houtsideTree⟩ := Finset.mem_sdiff.mp houtside
    have hne : inside ≠ outside := fun heq => houtsideTree (heq ▸ hinsideTree)
    have hpair : stalledᶜ = {inside, outside} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro label hlabel
        rcases Finset.mem_insert.mp hlabel with h | h
        · exact h ▸ hinsideCompl
        · exact (Finset.mem_singleton.mp h) ▸ houtsideCompl
      · rw [hcompl, Finset.card_insert_of_notMem (by simpa using hne),
          Finset.card_singleton]
    obtain ⟨hbig, hpivot⟩ := posDef_insert_pivot_lt_one kFourDirection point.mass
      point.weight point.mass_pos point.weight_pos houtsideTree htpd
    refine ⟨insert outside tree,
      by rw [Finset.card_insert_of_notMem houtsideTree, htcard], ?_, hbig,
      outside, Finset.mem_insert_self _ _, hpivot⟩
    rw [hpair]
    intro label hlabel
    rcases Finset.mem_insert.mp hlabel with h | h
    · exact h ▸ Finset.mem_insert_of_mem hinsideTree
    · exact (Finset.mem_singleton.mp h) ▸ Finset.mem_insert_self _ _

end Gtz
