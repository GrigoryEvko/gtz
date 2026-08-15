import Gtz.Design.StallTypeSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The exchange criterion and the price of a refused exchange

An EXCHANGE at a selection replaces one of its labels by an outside label.  The
card-four statement asks for a positive definite exchange at a stall, and this
module reads the question at the five-edge selection that holds both labels.

* `insert_erase_comm_of_ne` — the set identity behind everything here: the
  exchange `(C \ s) ∪ {t}` is the erasure of `s` from `C ∪ {t}`.
* `posDef_exchange_iff_pivot_insert_lt_one` — **the exchange criterion**.  The
  exchange is positive definite exactly when the pivot of the leaving label,
  read at the five-edge base, is below one.  No new machinery: the base is
  positive definite because it holds `C`, and the ladder rung decides an
  erasure.
* `no_exchange_outside_price` — **the price of a refused exchange**.  A four-edge
  selection whose exchanges into `t` all fail pays for it at the other outside
  label: `w t + (1 - w t) * pivot t ≤ w t' * (pivot t' - 1)`, both pivots read
  at `C ∪ {t}`.  The balance at the five-edge selection is the whole proof.
* `one_lt_pivot_insert_of_no_exchange` — the qualitative reading: the other
  outside pivot exceeds one.  This is strictly sharper than the stall price,
  which bounds only the weighted average of the two outside pivots.
* `half_price_of_no_exchange` — the quantitative reading when the entering label
  was itself priced at one: `(1 + w t) / 2 ≤ w t' * (pivot t' - 1)`.
* `kFourTypeB_leftover_compl_eq_star`, `kFourStarThree_mem_spanningTreeList` —
  the type-B shape.  A four-edge selection holding a triangle leaves, together
  with its complement, exactly the star at the free vertex, which is a spanning
  tree.
-/

namespace Gtz

open Matrix

/-! ## The exchange is an erasure -/

/-- The exchange rewritten: dropping `s` and adding `t` is adding `t` and then
dropping `s`, whenever the two labels differ. -/
theorem insert_erase_comm_of_ne {size : ℕ} (selected : Finset (Fin size))
    {leaving entering : Fin size} (hne : leaving ≠ entering) :
    insert entering (selected.erase leaving)
      = (insert entering selected).erase leaving := by
  ext label
  simp only [Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro (rfl | ⟨hlab, hmem⟩)
    · exact ⟨fun h => hne h.symm, Or.inl rfl⟩
    · exact ⟨hlab, Or.inr hmem⟩
  · rintro ⟨hlab, rfl | hmem⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hlab, hmem⟩

/-- **THE EXCHANGE CRITERION.**  Replacing a selected label by an outside label
keeps positive definiteness exactly when the leaving label's pivot, read at the
base which holds both, is below one.

The exchange is an erasure at that base, and the base is positive definite
because it contains the original selection. -/
theorem posDef_exchange_iff_pivot_insert_lt_one {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {leaving entering : Fin size}
    (hleaving : leaving ∈ selected) (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef) :
    (directionChartGap direction mass weight
        (insert entering (selected.erase leaving))).PosDef
      ↔ chartLadderPivot direction mass weight (insert entering selected)
          leaving < 1 := by
  have hne : leaving ≠ entering := by
    rintro rfl
    exact hentering hleaving
  have hbase : (directionChartGap direction mass weight
      (insert entering selected)).PosDef :=
    posDef_directionChartGap_of_subset direction mass weight hmass hweight
      (Finset.subset_insert entering selected) hpd
  rw [insert_erase_comm_of_ne selected hne]
  exact posDef_directionChartGap_erase_iff direction mass weight hmass hweight
    (insert entering selected) (Finset.mem_insert_of_mem hleaving) hbase

/-- The selection form of the criterion: some exchange into `entering` is
positive definite exactly when some selected label is droppable from the
five-edge base. -/
theorem exists_posDef_exchange_iff {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {entering : Fin size}
    (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef) :
    (∃ leaving ∈ selected, (directionChartGap direction mass weight
        (insert entering (selected.erase leaving))).PosDef)
      ↔ ∃ leaving ∈ selected,
          chartLadderPivot direction mass weight (insert entering selected)
            leaving < 1 := by
  constructor
  · rintro ⟨leaving, hmem, hex⟩
    exact ⟨leaving, hmem, (posDef_exchange_iff_pivot_insert_lt_one direction
      mass weight hmass hweight selected hmem hentering hpd).mp hex⟩
  · rintro ⟨leaving, hmem, hlt⟩
    exact ⟨leaving, hmem, (posDef_exchange_iff_pivot_insert_lt_one direction
      mass weight hmass hweight selected hmem hentering hpd).mpr hlt⟩

/-- A refused exchange stalls the five-edge base at every selected label. -/
theorem stall_insert_of_no_exchange {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {entering : Fin size}
    (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (hno : ∀ leaving ∈ selected, ¬ (directionChartGap direction mass weight
      (insert entering (selected.erase leaving))).PosDef) :
    ∀ leaving ∈ selected,
      1 ≤ chartLadderPivot direction mass weight (insert entering selected)
        leaving := by
  intro leaving hmem
  by_contra hlt
  push Not at hlt
  exact hno leaving hmem ((posDef_exchange_iff_pivot_insert_lt_one direction
    mass weight hmass hweight selected hmem hentering hpd).mpr hlt)

/-! ## The price of a refused exchange -/

/-- **THE PRICE OF A REFUSED EXCHANGE.**  Let a four-edge selection have the two
outside labels `entering` and `other`.  If every exchange into `entering` fails,
then the other outside label is priced at the five-edge base by

`weight entering + (1 - weight entering) * pivot entering ≤ weight other * (pivot other - 1)`.

The balance at the five-edge selection carries the whole argument: its four
inherited labels each spend at least their own `1 - weight`, and the sum of those
is `3 + weight entering + weight other`. -/
theorem no_exchange_outside_price (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) {entering other : Fin 6}
    (hcompl : selectedᶜ = {entering, other}) (hne : entering ≠ other)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    (hstall : ∀ leaving ∈ selected, 1 ≤ chartLadderPivot kFourDirection
      point.mass point.weight (insert entering selected) leaving) :
    point.weight entering + (1 - point.weight entering)
        * chartLadderPivot kFourDirection point.mass point.weight
            (insert entering selected) entering
      ≤ point.weight other * (chartLadderPivot kFourDirection point.mass
          point.weight (insert entering selected) other - 1) := by
  have hentering : entering ∉ selected := by
    have : entering ∈ selectedᶜ := by rw [hcompl]; exact Finset.mem_insert_self _ _
    exact Finset.mem_compl.mp this
  -- the five-edge base and its complement
  have hcard : selected.card = 4 := by
    have hc : selectedᶜ.card = 2 := by rw [hcompl, Finset.card_pair hne]
    have := Finset.card_compl selected
    rw [hc] at this
    simp only [Fintype.card_fin] at this
    omega
  have hcompl' : (insert entering selected)ᶜ = {other} := by
    rw [Finset.compl_insert, hcompl]
    exact Finset.erase_insert (by simpa using hne)
  have hbasePD : (directionChartGap kFourDirection point.mass point.weight
      (insert entering selected)).PosDef :=
    posDef_directionChartGap_of_subset kFourDirection point.mass
      point.weight point.mass_pos point.weight_pos
      (Finset.subset_insert entering selected) hpd
  have hbal := pivot_balance kFourDirection point (insert entering selected)
    hbasePD
  rw [hcompl', Finset.sum_singleton, Finset.sum_insert hentering] at hbal
  -- the inherited labels each spend at least their own `1 - weight`
  have hinside : ∑ label ∈ selected, (1 - point.weight label)
      ≤ ∑ label ∈ selected, (1 - point.weight label)
        * chartLadderPivot kFourDirection point.mass point.weight
            (insert entering selected) label := by
    refine Finset.sum_le_sum fun label hmem => ?_
    have hw1 := directionChartPoint_weight_lt_one point label
    exact le_mul_of_one_le_right (by linarith) (hstall label hmem)
  -- and their `1 - weight` sum is `3 + weight entering + weight other`
  have hweightSum : ∑ label ∈ selected, point.weight label
      = 1 - point.weight entering - point.weight other := by
    have hsplit : ∑ label ∈ selected, point.weight label
        + ∑ label ∈ selectedᶜ, point.weight label = 1 := by
      rw [Finset.sum_add_sum_compl]
      exact point.weight_sum_one
    rw [hcompl, Finset.sum_pair hne] at hsplit
    linarith
  have hleft : ∑ label ∈ selected, (1 - point.weight label)
      = 3 + point.weight entering + point.weight other := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hweightSum, hcard]
    simp
    ring
  rw [hleft] at hinside
  linarith

/-- The qualitative reading: a refused exchange forces the other outside pivot
above one.  The stall price bounds only the weighted average of the two outside
pivots, so this is strictly sharper. -/
theorem one_lt_pivot_insert_of_no_exchange (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) {entering other : Fin 6}
    (hcompl : selectedᶜ = {entering, other}) (hne : entering ≠ other)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    (hstall : ∀ leaving ∈ selected, 1 ≤ chartLadderPivot kFourDirection
      point.mass point.weight (insert entering selected) leaving) :
    1 < chartLadderPivot kFourDirection point.mass point.weight
      (insert entering selected) other := by
  have hprice := no_exchange_outside_price point selected hcompl hne hpd hstall
  have hwE := point.weight_pos entering
  have hwO := point.weight_pos other
  have hwE1 := directionChartPoint_weight_lt_one point entering
  have hbasePD : (directionChartGap kFourDirection point.mass point.weight
      (insert entering selected)).PosDef :=
    posDef_directionChartGap_of_subset kFourDirection point.mass
      point.weight point.mass_pos point.weight_pos
      (Finset.subset_insert entering selected) hpd
  have hnn := chartLadderPivot_nonneg_of_posDef kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos (insert entering selected)
    hbasePD entering
  nlinarith

/-- **THE HALF PRICE.**  When the entering label was itself priced at one before
the insertion, its pivot at the five-edge base is at least `1 / 2`, and the
refused exchange costs the other outside label at least `(1 + weight entering) / 2`. -/
theorem half_price_of_no_exchange (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) {entering other : Fin 6}
    (hcompl : selectedᶜ = {entering, other}) (hne : entering ≠ other)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    (hpriced : 1 ≤ chartLadderPivot kFourDirection point.mass point.weight
      selected entering)
    (hstall : ∀ leaving ∈ selected, 1 ≤ chartLadderPivot kFourDirection
      point.mass point.weight (insert entering selected) leaving) :
    (1 + point.weight entering) / 2
      ≤ point.weight other * (chartLadderPivot kFourDirection point.mass
          point.weight (insert entering selected) other - 1) := by
  have hentering : entering ∉ selected := by
    have : entering ∈ selectedᶜ := by rw [hcompl]; exact Finset.mem_insert_self _ _
    exact Finset.mem_compl.mp this
  have hprice := no_exchange_outside_price point selected hcompl hne hpd hstall
  have hhalf := (chartLadderPivot_insert_self_mem_Ico kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos selected hentering hpd
    hpriced).1
  have hwE1 := directionChartPoint_weight_lt_one point entering
  nlinarith

/-- **BOTH OUTSIDE PIVOTS EXCEED ONE.**  A four-edge selection refusing every
exchange at either outside label pays at both.

The stall price bounds only the weighted average of the two outside pivots read
at the selection itself; this reads each of them separately, at its own five-edge
base, and puts both strictly above one. -/
theorem both_outside_pivots_gt_one_of_no_exchange (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) {entering other : Fin 6}
    (hcompl : selectedᶜ = {entering, other}) (hne : entering ≠ other)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    (hstallOne : ∀ leaving ∈ selected, 1 ≤ chartLadderPivot kFourDirection
      point.mass point.weight (insert entering selected) leaving)
    (hstallTwo : ∀ leaving ∈ selected, 1 ≤ chartLadderPivot kFourDirection
      point.mass point.weight (insert other selected) leaving) :
    1 < chartLadderPivot kFourDirection point.mass point.weight
        (insert entering selected) other
      ∧ 1 < chartLadderPivot kFourDirection point.mass point.weight
        (insert other selected) entering := by
  refine ⟨one_lt_pivot_insert_of_no_exchange point selected hcompl hne hpd
    hstallOne, ?_⟩
  refine one_lt_pivot_insert_of_no_exchange point selected ?_ hne.symm hpd
    hstallTwo
  rw [hcompl, Finset.pair_comm]

/-! ## The type-B shape -/

/-- A four-edge selection holding the triangle `{0, 1, 2}` leaves, together with
its complement, exactly the star at the free vertex. -/
theorem kFourTypeB_leftover_compl_eq_star (selected : Finset (Fin 6))
    (hcard : selected.card = 4)
    (htriangle : ({0, 1, 2} : Finset (Fin 6)) ⊆ selected) :
    selectedᶜ ∪ (selected \ ({0, 1, 2} : Finset (Fin 6)))
      = ({3, 4, 5} : Finset (Fin 6)) := by
  revert hcard htriangle
  revert selected
  decide

/-- The star at the free vertex of a type-B selection is a spanning tree. -/
theorem kFourStarThree_mem_spanningTreeList :
    ({3, 4, 5} : Finset (Fin 6)) ∈ kFourSpanningTreeList := by
  decide

end Gtz
