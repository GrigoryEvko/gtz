import Gtz.Design.PivotArmClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The card-four stall, and where the descent bottoms out

The descent dichotomy leaves one branch: a stalled positive-definite four-edge
selection.  This module measures that branch.

* `strictTree_iff_exists_nonStalledCardFour` — **the equivalence**.  A strict
  spanning tree exists exactly when a non-stalled positive-definite four-edge
  selection exists.  A tree extends to a four-set which the tree itself
  un-stalls, and a non-stalled four-set drops to a tree.  The card-four branch
  therefore repackages the chart statement, and does not reduce it.
* `exists_mem_pivot_univ_lt_one_of_cardFour_stall` — **the univ-descent law**.
  At a stalled four-edge selection some label of the stall is droppable from
  the full selection.  Both complement labels are droppable because the full
  selection minus either one still holds the stall, so the balance at the full
  selection has to spend its three units inside the stall.
* `kFourMatching_insert_mem_spanningTreeList` — a perfect matching of `K4` plus
  any further edge is a spanning tree.  At a stall whose complement is a
  matching this is the shape of every winner the probes leave available.
-/

namespace Gtz

/-! ## The equivalence -/

/-- A strict spanning tree un-stalls every four-edge selection that holds it:
the added label carries pivot below one, because deleting it returns the
tree. -/
theorem exists_nonStalledCardFour_of_strictTree (point : DirectionChartPoint 6)
    {tree : Finset (Fin 6)} (htree : tree ∈ kFourSpanningTreeList)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      tree).PosDef) :
    ∃ sel : Finset (Fin 6), sel.card = 4
      ∧ (directionChartGap kFourDirection point.mass point.weight sel).PosDef
      ∧ ∃ label ∈ sel, chartLadderPivot kFourDirection point.mass point.weight
          sel label < 1 := by
  have hcard : tree.card = 3 := kFourSpanningTree_card tree htree
  obtain ⟨added, hadded⟩ : ∃ added : Fin 6, added ∉ tree := by
    by_contra hall
    push Not at hall
    have huniv : tree = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  refine ⟨insert added tree, ?_, ?_, added, Finset.mem_insert_self _ _, ?_⟩
  · rw [Finset.card_insert_of_notMem hadded, hcard]
  · exact posDef_directionChartGap_of_subset kFourDirection point.mass
      point.weight point.mass_pos point.weight_pos (Finset.subset_insert _ _) hpd
  · refine (posDef_directionChartGap_erase_iff kFourDirection point.mass
      point.weight point.mass_pos point.weight_pos _
      (Finset.mem_insert_self added tree) ?_).mp ?_
    · exact posDef_directionChartGap_of_subset kFourDirection point.mass
        point.weight point.mass_pos point.weight_pos
        (Finset.subset_insert _ _) hpd
    · rwa [Finset.erase_insert hadded]

/-- A non-stalled positive-definite four-edge selection drops to a strict
spanning tree: the sub-one label leaves a positive-definite triple, and a
triangle is never positive definite. -/
theorem exists_strictTree_of_nonStalledCardFour (point : DirectionChartPoint 6)
    {sel : Finset (Fin 6)} (hcard : sel.card = 4)
    (hpd : (directionChartGap kFourDirection point.mass point.weight sel).PosDef)
    {label : Fin 6} (hmem : label ∈ sel)
    (hlt : chartLadderPivot kFourDirection point.mass point.weight sel
      label < 1) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  have hpdTree : (directionChartGap kFourDirection point.mass point.weight
      (sel.erase label)).PosDef :=
    (posDef_directionChartGap_erase_iff kFourDirection point.mass point.weight
      point.mass_pos point.weight_pos sel hmem hpd).mpr hlt
  have hcardTree : (sel.erase label).card = 3 := by
    rw [Finset.card_erase_of_mem hmem, hcard]
  refine ⟨sel.erase label,
    mem_kFourSpanningTreeList_of_card_three _ hcardTree ?_, hpdTree⟩
  intro htriangle
  exact kFourTriangle_gap_not_posDef point _ htriangle hpdTree

/-- **THE CARD-FOUR EQUIVALENCE.**  A strict spanning tree exists exactly when
a non-stalled positive-definite four-edge selection exists.

The card-four branch of the descent dichotomy is therefore a repackaging of the
chart statement rather than a reduction of it: closing the stalled branch is
worth exactly as much as the conclusion it produces. -/
theorem strictTree_iff_exists_nonStalledCardFour
    (point : DirectionChartPoint 6) :
    (∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef)
    ↔ (∃ sel : Finset (Fin 6), sel.card = 4
        ∧ (directionChartGap kFourDirection point.mass point.weight sel).PosDef
        ∧ ∃ label ∈ sel, chartLadderPivot kFourDirection point.mass
            point.weight sel label < 1) := by
  constructor
  · rintro ⟨tree, htree, hpd⟩
    exact exists_nonStalledCardFour_of_strictTree point htree hpd
  · rintro ⟨sel, hcard, hpd, label, hmem, hlt⟩
    exact exists_strictTree_of_nonStalledCardFour point hcard hpd hmem hlt

/-! ## The univ-descent law -/

/-- Both labels outside a positive-definite four-edge selection are droppable
from the full selection: the full selection minus either one still holds the
selection, so it stays positive definite. -/
theorem chartLadderPivot_univ_lt_one_of_notMem (point : DirectionChartPoint 6)
    {sel : Finset (Fin 6)}
    (hpd : (directionChartGap kFourDirection point.mass point.weight sel).PosDef)
    {label : Fin 6} (hnot : label ∉ sel) :
    chartLadderPivot kFourDirection point.mass point.weight Finset.univ
      label < 1 := by
  have hsub : sel ⊆ Finset.univ.erase label := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
    rintro rfl
    exact hnot hx
  have hpdErase : (directionChartGap kFourDirection point.mass point.weight
      (Finset.univ.erase label)).PosDef :=
    posDef_directionChartGap_of_subset kFourDirection point.mass point.weight
      point.mass_pos point.weight_pos hsub hpd
  exact (posDef_directionChartGap_erase_iff kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos Finset.univ
    (Finset.mem_univ label) (posDef_directionChartGap_univ point)).mp hpdErase

-- AUDIT-PORTABLE (2026-08-17): the proof below is DIRECTION-GENERIC but the
-- statement is hard-coded to `kFourDirection`.  Measured: the three inputs are
-- `Gtz.pivot_balance` (Gtz/Design/PivotBalanceLaw.lean:86, takes `direction` as
-- an argument), `Gtz.directionChartPoint_weight_lt_one`
-- (Gtz/Design/StarOnlyLaw.lean:140, no direction at all) and
-- `Gtz.posDef_directionChartGap_univ` (Gtz/Design/PivotBalanceLaw.lean:134, the
-- ONLY K4-specific input).  The three-lines analogue of that last input is
-- landed and unconditional at every slide:
-- `Gtz.posDef_directionChartGap_univ_threeLines`
-- (Gtz/Design/ThreeLinesDescentPort.lean:312).
-- A three-lines copy is therefore a two-symbol substitution, not new
-- mathematics.  The docstring below already asserts the genericity in prose
-- ("applies to ... any four labels at all") while the signature denies it.
-- The same remark applies to `Gtz.chartLadderPivot_univ_lt_one_of_notMem` (:108)
-- and to the K4 wrappers in Gtz/Design/StallComplementCounting.lean at :70,
-- :108 and :136, whose generic engines at :50 and :88 already take `direction`.
/-- **THE UNIV-DESCENT LAW.**  Every four-element set of labels holds a label
which is droppable from the full selection.

Equivalently: at most three labels carry full-selection pivot at least one.  The
balance at the full selection spends exactly three units, while four labels
alone would already spend `4 - (their weight)`, which exceeds three because the
two remaining weights are positive.

Neither positive definiteness nor a stall is needed, so the law applies to every
stalled four-edge selection, to its complement, and to any four labels at all. -/
theorem exists_mem_pivot_univ_lt_one_of_card_four
    (point : DirectionChartPoint 6) {sel : Finset (Fin 6)}
    (hcard : sel.card = 4) :
    ∃ label ∈ sel, chartLadderPivot kFourDirection point.mass point.weight
      Finset.univ label < 1 := by
  by_contra hall
  push Not at hall
  have hunivPD := posDef_directionChartGap_univ point
  have hbal := pivot_balance kFourDirection point Finset.univ hunivPD
  rw [Finset.compl_univ, Finset.sum_empty, add_zero] at hbal
  rw [← Finset.sum_add_sum_compl sel] at hbal
  -- the stall's own labels already spend `4 - (weight of the stall)`
  have hinside : ((sel.card : ℝ) - ∑ label ∈ sel, point.weight label)
      ≤ ∑ label ∈ sel, (1 - point.weight label)
        * chartLadderPivot kFourDirection point.mass point.weight
            Finset.univ label := by
    have hterm : ∀ label ∈ sel, (1 - point.weight label)
        ≤ (1 - point.weight label)
          * chartLadderPivot kFourDirection point.mass point.weight
              Finset.univ label := by
      intro label hmem
      have hw1 := directionChartPoint_weight_lt_one point label
      exact le_mul_of_one_le_right (by linarith) (hall label hmem)
    have hsum := Finset.sum_le_sum hterm
    have hleft : ∑ label ∈ sel, (1 - point.weight label)
        = (sel.card : ℝ) - ∑ label ∈ sel, point.weight label := by
      rw [Finset.sum_sub_distrib, Finset.sum_const]
      simp
    rwa [hleft] at hsum
  -- the two complement labels contribute nothing negative
  have houtside : 0 ≤ ∑ label ∈ selᶜ, (1 - point.weight label)
      * chartLadderPivot kFourDirection point.mass point.weight
          Finset.univ label := by
    refine Finset.sum_nonneg fun label _ => ?_
    have hw1 := directionChartPoint_weight_lt_one point label
    exact mul_nonneg (by linarith)
      (chartLadderPivot_nonneg_of_posDef kFourDirection point.mass point.weight
        point.mass_pos point.weight_pos Finset.univ hunivPD label)
  -- but the stall's weight is strictly below one
  have hsplit : ∑ label ∈ sel, point.weight label
      + ∑ label ∈ selᶜ, point.weight label = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact point.weight_sum_one
  have hcompl : selᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, hcard]
    simp
  have houtPos : 0 < ∑ label ∈ selᶜ, point.weight label :=
    Finset.sum_pos (fun label _ => point.weight_pos label) hcompl
  rw [hcard] at hinside
  norm_num at hinside
  linarith

/-! ## The matching shape of a type-A winner -/

/-- A perfect matching of `K4` plus any further edge is a spanning tree.  At a
stall whose complement is a matching, the four sets `{s} ∪ complement` are all
spanning trees, and the probes report configurations where the winner has to be
one of them. -/
theorem kFourMatching_insert_mem_spanningTreeList (matching : Finset (Fin 6))
    (hmatch : matching = {0, 5} ∨ matching = {1, 4} ∨ matching = {2, 3})
    (edge : Fin 6) (hedge : edge ∉ matching) :
    insert edge matching ∈ kFourSpanningTreeList := by
  revert hedge
  rcases hmatch with h | h | h <;> subst h <;> revert edge <;> decide

end Gtz
