import Gtz.Design.StallComplementCounting
import Gtz.Design.DesignDescentPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The complement-pair escape, and the design-level reformulation of the stall branch

The descent leaves one branch: a stalled positive definite card-four selection.
`Gtz.exists_dominates_cardThree_of_no_cardFour_stall` shows that a design with no
such stall already satisfies `GtzWeighted 6 3`, so the stall branch carries the
whole remaining content.  This module reformulates that branch as an existence
statement over **six explicit selections** instead of twenty.

At a card-four stall the two labels outside it form a pair, and a stall is a
minimal positive definite set, so no strict triple sits inside the stall: every
strict triple must leave it.  Extending such a triple by a complement label
reaches a card-four selection that holds the whole pair, is positive definite,
and is un-stalled by the triple.  The converse drops the sub-one label.  The two
directions give an equivalence.

* `exists_nonStalled_supset_compl_of_stall` — the generic escape, at any size
  and any direction family whose stall has a two-label complement.
* `exists_posDef_smaller_iff_exists_nonStalled_supset_compl` — **the
  equivalence**.  A positive definite selection one below the stall exists
  exactly when a non-stalled positive definite selection of the stall's own size
  contains both complement labels.
* `exists_posDef_cardThree_of_complPair_escape` — the design-level consumer.
* `exists_dominates_cardThree_of_complPair_escape` — the same in the shape
  `GtzWeighted 6 3` consumes.

Because the selections that contain both complement labels are the stall's own
complement together with two of its four labels, the disjunction runs over
`Nat.choose 4 2 = 6` selections.  The statement one level down is false: a
positive definite *triple* holding both complement labels need not exist.

Nothing here is specific to the K4 chart.  The generic form serves the K4 chart,
the three-lines chart, and the trivial chart of a weighted design alike.
-/

namespace Gtz

open Finset

/-- **THE COMPLEMENT-PAIR ESCAPE, GENERIC.**  At a stall whose complement is a
two-label pair, any positive definite selection one label smaller than the stall
extends to a non-stalled positive definite selection of the stall's own size that
contains *both* complement labels.

The stall is minimal, so the smaller selection is not contained in it and hence
meets the pair.  If it already holds both, extend by any outside label; if it
holds exactly one, extend by the other.  Either way the added label carries pivot
below one. -/
theorem exists_nonStalled_supset_compl_of_stall {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {stalled smaller : Finset (Fin size)}
    (hsize : stalled.card + 2 = size)
    (hpd : (directionChartGap direction mass weight stalled).PosDef)
    (hstall : ∀ label ∈ stalled,
      1 ≤ chartLadderPivot direction mass weight stalled label)
    (hsc : smaller.card + 1 = stalled.card)
    (hspd : (directionChartGap direction mass weight smaller).PosDef) :
    ∃ big : Finset (Fin size), big.card = stalled.card ∧ stalledᶜ ⊆ big
      ∧ (directionChartGap direction mass weight big).PosDef
      ∧ ∃ label ∈ big, chartLadderPivot direction mass weight big label < 1 := by
  have hcompl : stalledᶜ.card = 2 := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  -- minimality: the smaller selection leaves the stall
  have hnotsub : ¬ smaller ⊆ stalled :=
    not_subset_of_posDef_of_stall direction mass weight hmass hweight hpd hstall
      hspd (by omega)
  obtain ⟨inside, hinsideSmall, hinsideOut⟩ : ∃ label ∈ smaller, label ∉ stalled := by
    by_contra hall
    push Not at hall
    exact hnotsub hall
  have hinsideCompl : inside ∈ stalledᶜ := Finset.mem_compl.mpr hinsideOut
  rcases Finset.eq_empty_or_nonempty (stalledᶜ \ smaller) with hempty | ⟨outside, houtside⟩
  · -- the smaller selection already holds both complement labels
    obtain ⟨added, hadded⟩ : ∃ added : Fin size, added ∉ smaller := by
      by_contra hall
      push Not at hall
      have hsub : (Finset.univ : Finset (Fin size)) ⊆ smaller := fun label _ => hall label
      have := Finset.card_le_card hsub
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    obtain ⟨hbig, hpivot⟩ := posDef_insert_pivot_lt_one direction mass weight
      hmass hweight hadded hspd
    refine ⟨insert added smaller, ?_, ?_, hbig, added, Finset.mem_insert_self _ _, hpivot⟩
    · rw [Finset.card_insert_of_notMem hadded]; omega
    · intro label hlabel
      refine Finset.mem_insert_of_mem ?_
      by_contra hnot
      exact (Finset.notMem_empty label) (hempty ▸ Finset.mem_sdiff.mpr ⟨hlabel, hnot⟩)
  · -- it holds exactly one; add the other
    obtain ⟨houtsideCompl, houtsideSmall⟩ := Finset.mem_sdiff.mp houtside
    have hne : inside ≠ outside := fun heq => houtsideSmall (heq ▸ hinsideSmall)
    have hpair : stalledᶜ = {inside, outside} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro label hlabel
        rcases Finset.mem_insert.mp hlabel with h | h
        · exact h ▸ hinsideCompl
        · exact (Finset.mem_singleton.mp h) ▸ houtsideCompl
      · rw [hcompl, Finset.card_insert_of_notMem (by simpa using hne),
          Finset.card_singleton]
    obtain ⟨hbig, hpivot⟩ := posDef_insert_pivot_lt_one direction mass weight
      hmass hweight houtsideSmall hspd
    refine ⟨insert outside smaller, ?_, ?_, hbig,
      outside, Finset.mem_insert_self _ _, hpivot⟩
    · rw [Finset.card_insert_of_notMem houtsideSmall]; omega
    · rw [hpair]
      intro label hlabel
      rcases Finset.mem_insert.mp hlabel with h | h
      · exact h ▸ Finset.mem_insert_of_mem hinsideSmall
      · exact (Finset.mem_singleton.mp h) ▸ Finset.mem_insert_self _ _

/-- A non-stalled positive definite selection drops one label and stays positive
definite, one card smaller. -/
theorem exists_posDef_erase_of_pivot_lt_one {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {big : Finset (Fin size)}
    (hpd : (directionChartGap direction mass weight big).PosDef)
    {label : Fin size} (hmem : label ∈ big)
    (hlt : chartLadderPivot direction mass weight big label < 1) :
    (big.erase label).card + 1 = big.card
      ∧ (directionChartGap direction mass weight (big.erase label)).PosDef := by
  have hpos : 0 < big.card := Finset.card_pos.mpr ⟨label, hmem⟩
  refine ⟨by rw [Finset.card_erase_of_mem hmem]; omega, ?_⟩
  exact (posDef_directionChartGap_erase_iff direction mass weight hmass hweight big
    hmem hpd).mpr hlt

/-- **THE EQUIVALENCE.**  At a stall with a two-label complement, a positive
definite selection one card below the stall exists exactly when a non-stalled
positive definite selection of the stall's own size contains both complement
labels.

The forward direction is the complement-pair escape; the reverse drops the
sub-one label.  So the complement-restricted count is a reformulation of the
chart statement over six selections, and not a weakening of it. -/
theorem exists_posDef_smaller_iff_exists_nonStalled_supset_compl {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {stalled : Finset (Fin size)}
    (hsize : stalled.card + 2 = size)
    (hpd : (directionChartGap direction mass weight stalled).PosDef)
    (hstall : ∀ label ∈ stalled,
      1 ≤ chartLadderPivot direction mass weight stalled label) :
    (∃ smaller : Finset (Fin size), smaller.card + 1 = stalled.card
        ∧ (directionChartGap direction mass weight smaller).PosDef)
      ↔ (∃ big : Finset (Fin size), big.card = stalled.card ∧ stalledᶜ ⊆ big
        ∧ (directionChartGap direction mass weight big).PosDef
        ∧ ∃ label ∈ big, chartLadderPivot direction mass weight big label < 1) := by
  constructor
  · rintro ⟨smaller, hsc, hspd⟩
    exact exists_nonStalled_supset_compl_of_stall direction mass weight hmass
      hweight hsize hpd hstall hsc hspd
  · rintro ⟨big, hbcard, -, hbpd, label, hmem, hlt⟩
    obtain ⟨hcard, hepd⟩ := exists_posDef_erase_of_pivot_lt_one direction mass
      weight hmass hweight hbpd hmem hlt
    exact ⟨big.erase label, by omega, hepd⟩

/-! ## The design-level consumer

At the trivial chart of a weighted design the chart gap is the design's own gap,
so the escape reads directly as a statement about `subsetSum`. -/

/-- **THE STALL BRANCH OF `GtzWeighted 6 3`, OVER SIX SELECTIONS.**  If at every
stalled positive definite four-set of a design some four-set holding both
complement labels is positive definite and non-stalled, the design carries a
strictly dominating triple.

Together with `exists_dominates_cardThree_of_no_cardFour_stall`, which handles
the stall-free case, this is the whole of `GtzWeighted 6 3` for that design. -/
theorem exists_posDef_cardThree_of_complPair_escape (design : WeightedDesign 6 3)
    (hesc : ∀ sel : Finset (Fin 6), sel.card = 4 → (subsetSum design sel - 1).PosDef →
      (∀ label ∈ sel, 1 ≤ chartLadderPivot design.atom (designChartPoint design).mass
        (designChartPoint design).weight sel label) →
      ∃ big : Finset (Fin 6), big.card = 4 ∧ selᶜ ⊆ big
        ∧ (subsetSum design big - 1).PosDef
        ∧ ∃ label ∈ big, chartLadderPivot design.atom (designChartPoint design).mass
            (designChartPoint design).weight big label < 1) :
    ∃ sel : Finset (Fin 6), sel.card = 3 ∧ (subsetSum design sel - 1).PosDef := by
  rcases design_cardThree_or_cardFour_stall design with
    ⟨sel, hcard, hpd⟩ | ⟨sel, hcard, hpd, hstall⟩
  · exact ⟨sel, hcard, hpd⟩
  obtain ⟨big, hbcard, -, hbpd, label, hmem, hlt⟩ := hesc sel hcard hpd hstall
  have hbchart : (directionChartGap design.atom (designChartPoint design).mass
      (designChartPoint design).weight big).PosDef := by
    rwa [directionChartGap_designChartPoint design big]
  obtain ⟨hcard', hepd⟩ := exists_posDef_erase_of_pivot_lt_one design.atom
    (designChartPoint design).mass (designChartPoint design).weight
    (designChartPoint design).mass_pos (designChartPoint design).weight_pos
    hbchart hmem hlt
  refine ⟨big.erase label, by omega, ?_⟩
  rwa [directionChartGap_designChartPoint design (big.erase label)] at hepd

/-- The same in the shape `GtzWeighted 6 3` consumes. -/
theorem exists_dominates_cardThree_of_complPair_escape (design : WeightedDesign 6 3)
    (hesc : ∀ sel : Finset (Fin 6), sel.card = 4 → (subsetSum design sel - 1).PosDef →
      (∀ label ∈ sel, 1 ≤ chartLadderPivot design.atom (designChartPoint design).mass
        (designChartPoint design).weight sel label) →
      ∃ big : Finset (Fin 6), big.card = 4 ∧ selᶜ ⊆ big
        ∧ (subsetSum design big - 1).PosDef
        ∧ ∃ label ∈ big, chartLadderPivot design.atom (designChartPoint design).mass
            (designChartPoint design).weight big label < 1) :
    ∃ sel : Finset (Fin 6), sel.card = 3 ∧ Dominates design sel := by
  obtain ⟨sel, hcard, hpd⟩ := exists_posDef_cardThree_of_complPair_escape design hesc
  exact ⟨sel, hcard, hpd.posSemidef⟩

/-! ## The chart instances

Both live charts have six labels, so a card-four stall has a two-label
complement in each.  The generic escape therefore serves them unchanged. -/

/-- The K4 chart instance: at a card-four stall, a strict triple anywhere at the
point produces a non-stalled positive definite four-set holding both complement
labels. -/
theorem kFour_exists_nonStalled_supset_compl_of_stall
    (point : DirectionChartPoint 6) {stalled smaller : Finset (Fin 6)}
    (hcard : stalled.card = 4)
    (hpd : (directionChartGap kFourDirection point.mass point.weight stalled).PosDef)
    (hstall : ∀ label ∈ stalled,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight stalled label)
    (hsc : smaller.card = 3)
    (hspd : (directionChartGap kFourDirection point.mass point.weight smaller).PosDef) :
    ∃ big : Finset (Fin 6), big.card = 4 ∧ stalledᶜ ⊆ big
      ∧ (directionChartGap kFourDirection point.mass point.weight big).PosDef
      ∧ ∃ label ∈ big, chartLadderPivot kFourDirection point.mass point.weight
          big label < 1 := by
  have := exists_nonStalled_supset_compl_of_stall kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos (by omega) hpd hstall
    (by omega : smaller.card + 1 = stalled.card) hspd
  rwa [hcard] at this

/-- The three-lines chart instance, at every slide. -/
theorem threeLines_exists_nonStalled_supset_compl_of_stall (slide : ℝ)
    (point : DirectionChartPoint 6) {stalled smaller : Finset (Fin 6)}
    (hcard : stalled.card = 4)
    (hpd : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      stalled).PosDef)
    (hstall : ∀ label ∈ stalled, 1 ≤ chartLadderPivot (threeLinesDirection slide)
      point.mass point.weight stalled label)
    (hsc : smaller.card = 3)
    (hspd : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      smaller).PosDef) :
    ∃ big : Finset (Fin 6), big.card = 4 ∧ stalledᶜ ⊆ big
      ∧ (directionChartGap (threeLinesDirection slide) point.mass point.weight
          big).PosDef
      ∧ ∃ label ∈ big, chartLadderPivot (threeLinesDirection slide) point.mass
          point.weight big label < 1 := by
  have := exists_nonStalled_supset_compl_of_stall (threeLinesDirection slide)
    point.mass point.weight point.mass_pos point.weight_pos (by omega) hpd hstall
    (by omega : smaller.card + 1 = stalled.card) hspd
  rwa [hcard] at this

end Gtz
