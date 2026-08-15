import Gtz.Design.PivotBalanceLaw
import Gtz.Design.PivotStallPropagation
import Gtz.Design.ChartReadingLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The descent port: the full-selection descent at every spanning chart

The K4 descent stack proves that every K4 chart point carries a strict
spanning tree or a stalled selection.  Its engine room is size-generic and
direction-generic already: `pivot_balance`, `exists_univ_pivot_lt_one` and
`posDef_directionChartGap_erase_iff` all take the direction family as an
explicit parameter.  Only two statements name the K4 chart, and one of them
names it for a single reason.

`posDef_directionChartGap_univ` reads the full-selection gap as a positive
combination of the direction atoms.  Its proof consumes exactly one property
of the K4 chart: `kFourDirection_span`, the fact that the six directions
leave no probe unread.  This module removes that hard-coded reference and
takes the span property as a hypothesis.  Every chart whose directions span
then inherits the whole descent.

The three-lines chart has that property as `threeLinesDirection_span`, which
is landed and audited.  So the three-lines chart inherits the descent, and
this module lands the instantiation.

The A2 form of the descent is SHORTER than the A3 form.  The K4 trichotomy
ends by classifying a card-three selection as a spanning tree, which needs
the spanning-tree list and the triangle exclusion.  A2 asks only for a
card-three positive definite selection, with no classification at all.  The
generic trichotomy therefore stops one step earlier and lands A2's own
conclusion in its first branch.

The results:

* `posDef_directionChartGap_univ_of_span` — the full-selection gap is
  positive definite at every chart point of a spanning direction family;
* `exists_posDef_erase_univ_of_span` — every such point carries a positive
  definite five-label selection;
* `descent_trichotomy_of_span` — a card-three positive definite selection,
  or a stalled card-five selection, or a stalled card-four selection;
* the four three-lines instantiations, ending in
  `threeLines_cardThree_or_stall`, which is A2's conclusion under the two
  stall alternatives.
-/

namespace Gtz

open Finset Matrix

/-! ## The generic full-selection law -/

/-- **THE FULL-SELECTION LAW, GENERIC.**  The full-selection gap is positive
definite at every chart point whose direction family spans.  Its coefficients
are the positive boosts `m (1 - w) / w`, and a probe that every direction
reads as zero is itself zero. -/
theorem posDef_directionChartGap_univ_of_span
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    (hspan : ∀ probe : Fin 3 → ℝ,
      (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0) :
    (directionChartGap direction point.mass point.weight
      Finset.univ).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq
      (directionChartGap_transpose _ _ _ _), fun probe hne => ?_⟩
  rw [star_trivial, dotProduct_directionChartGap_mulVec_eq]
  have hd : ∀ label : Fin 6,
      0 < point.mass label / point.weight label - point.mass label := by
    intro label
    have hm := point.mass_pos label
    have hw := point.weight_pos label
    have hw1 := directionChartPoint_weight_lt_one point label
    rw [sub_pos, lt_div_iff₀ hw]
    nlinarith
  obtain ⟨witness, hwitness⟩ :
      ∃ label, direction label ⬝ᵥ probe ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (hspan probe hall)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_pos' (fun label _ => ?_) ⟨witness, Finset.mem_univ _, ?_⟩
  · have hterm : point.mass label / point.weight label
        * (direction label ⬝ᵥ probe) ^ 2
        - point.mass label * (direction label ⬝ᵥ probe) ^ 2
      = (point.mass label / point.weight label - point.mass label)
        * (direction label ⬝ᵥ probe) ^ 2 := by ring
    rw [hterm]
    exact mul_nonneg (hd label).le (sq_nonneg _)
  · have hterm : point.mass witness / point.weight witness
        * (direction witness ⬝ᵥ probe) ^ 2
        - point.mass witness * (direction witness ⬝ᵥ probe) ^ 2
      = (point.mass witness / point.weight witness - point.mass witness)
        * (direction witness ⬝ᵥ probe) ^ 2 := by ring
    rw [hterm]
    exact mul_pos (hd witness)
      (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hwitness)))

/-- **THE DESCENT STARTS, GENERIC.**  Every chart point of a spanning
direction family carries a positive definite five-label selection.  The six
full-selection pivots have weighted average three fifths, so one of them lies
below one and its label erases. -/
theorem exists_posDef_erase_univ_of_span
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    (hspan : ∀ probe : Fin 3 → ℝ,
      (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0) :
    ∃ label, (directionChartGap direction point.mass point.weight
      (Finset.univ.erase label)).PosDef := by
  have hunivPd := posDef_directionChartGap_univ_of_span direction point hspan
  obtain ⟨label, hlt⟩ := exists_univ_pivot_lt_one direction point hunivPd
  exact ⟨label, (posDef_directionChartGap_erase_iff direction point.mass
    point.weight point.mass_pos point.weight_pos Finset.univ
    (Finset.mem_univ label) hunivPd).mpr hlt⟩

/-! ## The generic descent trichotomy -/

/-- **THE DESCENT TRICHOTOMY, GENERIC.**  Every chart point of a spanning
direction family carries a card-three positive definite selection, or a
stalled positive definite five-label selection, or a stalled positive
definite four-label selection.  The stalls are the only obstructions between
the always-strict full selection and a card-three selection.

This is the A2 form of the K4 trichotomy.  It stops one step earlier, because
it makes no claim about WHICH card-three selection appears.  The K4 form pays
for that claim with the spanning-tree list and the triangle exclusion. -/
theorem descent_trichotomy_of_span
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    (hspan : ∀ probe : Fin 3 → ℝ,
      (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0) :
    (∃ sel : Finset (Fin 6), sel.card = 3
        ∧ (directionChartGap direction point.mass point.weight sel).PosDef)
    ∨ (∃ sel : Finset (Fin 6), sel.card = 5
        ∧ (directionChartGap direction point.mass point.weight sel).PosDef
        ∧ ∀ label ∈ sel, 1 ≤ chartLadderPivot direction point.mass
            point.weight sel label)
    ∨ (∃ sel : Finset (Fin 6), sel.card = 4
        ∧ (directionChartGap direction point.mass point.weight sel).PosDef
        ∧ ∀ label ∈ sel, 1 ≤ chartLadderPivot direction point.mass
            point.weight sel label) := by
  obtain ⟨dropFive, hpdFive⟩ :=
    exists_posDef_erase_univ_of_span direction point hspan
  have hcardFive : (Finset.univ.erase dropFive).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  by_cases hstallFive : ∀ label ∈ Finset.univ.erase dropFive,
      1 ≤ chartLadderPivot direction point.mass point.weight
        (Finset.univ.erase dropFive) label
  · exact Or.inr (Or.inl ⟨_, hcardFive, hpdFive, hstallFive⟩)
  push Not at hstallFive
  obtain ⟨dropFour, hmemFour, hltFour⟩ := hstallFive
  have hpdFour : (directionChartGap direction point.mass point.weight
      ((Finset.univ.erase dropFive).erase dropFour)).PosDef :=
    (posDef_directionChartGap_erase_iff direction point.mass
      point.weight point.mass_pos point.weight_pos _ hmemFour hpdFive).mpr
      hltFour
  have hcardFour : ((Finset.univ.erase dropFive).erase dropFour).card = 4 := by
    rw [Finset.card_erase_of_mem hmemFour, hcardFive]
  by_cases hstallFour : ∀ label ∈ (Finset.univ.erase dropFive).erase dropFour,
      1 ≤ chartLadderPivot direction point.mass point.weight
        ((Finset.univ.erase dropFive).erase dropFour) label
  · exact Or.inr (Or.inr ⟨_, hcardFour, hpdFour, hstallFour⟩)
  push Not at hstallFour
  obtain ⟨dropThree, hmemThree, hltThree⟩ := hstallFour
  have hpdThree : (directionChartGap direction point.mass point.weight
      (((Finset.univ.erase dropFive).erase dropFour).erase
        dropThree)).PosDef :=
    (posDef_directionChartGap_erase_iff direction point.mass
      point.weight point.mass_pos point.weight_pos _ hmemThree hpdFour).mpr
      hltThree
  have hcardThree : (((Finset.univ.erase dropFive).erase dropFour).erase
      dropThree).card = 3 := by
    rw [Finset.card_erase_of_mem hmemThree, hcardFour]
  exact Or.inl ⟨_, hcardThree, hpdThree⟩

/-! ## The five-stall elimination, generic -/

/-- **THE FIVE-STALL ELIMINATION, GENERIC.**  Every chart point of a spanning
direction family carries a positive definite five-label selection which is not
stalled.

A stalled one would price its missing label at `1 + 1/w`; the insertion law
would raise the matching full-selection pivot to at least `(1 + w)/(1 + 2w)`,
which is at least `1 - 2w`; and the balance at the full selection would then
read `3 >= 4`. -/
theorem exists_posDef_erase_univ_not_stall_of_span
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    (hspan : ∀ probe : Fin 3 → ℝ,
      (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0) :
    ∃ missing : Fin 6,
      (directionChartGap direction point.mass point.weight
        (Finset.univ.erase missing)).PosDef ∧
      ∃ label ∈ Finset.univ.erase missing,
        chartLadderPivot direction point.mass point.weight
          (Finset.univ.erase missing) label < 1 := by
  by_contra hall
  push Not at hall
  have hunivPD := posDef_directionChartGap_univ_of_span direction point hspan
  have hlow : ∀ missing : Fin 6,
      1 - 2 * point.weight missing
        ≤ (1 - point.weight missing)
          * chartLadderPivot direction point.mass point.weight
              Finset.univ missing := by
    intro missing
    have hw := point.weight_pos missing
    have hw1 := directionChartPoint_weight_lt_one point missing
    by_cases hpd : (directionChartGap direction point.mass point.weight
        (Finset.univ.erase missing)).PosDef
    · have hstall := hall missing hpd
      have hprice := card_five_stall direction point hpd hstall
      have hnot : missing ∉ Finset.univ.erase missing := Finset.notMem_erase _ _
      have hinsert : insert missing (Finset.univ.erase missing)
          = (Finset.univ : Finset (Fin 6)) :=
        Finset.insert_erase (Finset.mem_univ missing)
      have hlaw := chartLadderPivot_insert_self direction point.mass
        point.weight point.mass_pos point.weight_pos
        (Finset.univ.erase missing) hnot hpd
      rw [hinsert] at hlaw
      have hPpos : (0 : ℝ) < chartLadderPivot direction point.mass
          point.weight (Finset.univ.erase missing) missing :=
        lt_of_lt_of_le (by positivity) hprice
      have hwP : 1 + point.weight missing
          ≤ point.weight missing
            * chartLadderPivot direction point.mass point.weight
                (Finset.univ.erase missing) missing := by
        have hmul := mul_le_mul_of_nonneg_left hprice hw.le
        have hexp : point.weight missing * (1 + 1 / point.weight missing)
            = 1 + point.weight missing := by
          field_simp
          ring
        rw [hexp] at hmul
        exact hmul
      have hden : (0 : ℝ) < 1 + chartLadderPivot direction point.mass
          point.weight (Finset.univ.erase missing) missing := by linarith
      rw [hlaw]
      have hshape : (1 - point.weight missing)
            * (chartLadderPivot direction point.mass point.weight
                (Finset.univ.erase missing) missing
              / (1 + chartLadderPivot direction point.mass point.weight
                  (Finset.univ.erase missing) missing))
          = ((1 - point.weight missing)
              * chartLadderPivot direction point.mass point.weight
                  (Finset.univ.erase missing) missing)
            / (1 + chartLadderPivot direction point.mass point.weight
                (Finset.univ.erase missing) missing) := by ring
      rw [hshape, le_div_iff₀ hden]
      nlinarith [hwP, hw, hw1]
    · have hge : 1 ≤ chartLadderPivot direction point.mass point.weight
          Finset.univ missing := by
        by_contra hlt
        push Not at hlt
        exact hpd ((posDef_directionChartGap_erase_iff direction
          point.mass point.weight point.mass_pos point.weight_pos Finset.univ
          (Finset.mem_univ missing) hunivPD).mpr hlt)
      nlinarith [hge, hw, hw1]
  have hbal := pivot_balance direction point Finset.univ hunivPD
  rw [Finset.compl_univ, Finset.sum_empty, add_zero] at hbal
  have hsum := Finset.sum_le_sum (fun label (_ : label ∈ Finset.univ) =>
    hlow label)
  have hfour : ∑ _label : Fin 6, (1 : ℝ) - 2 * ∑ label : Fin 6,
      point.weight label = (4 : ℝ) := by
    rw [point.weight_sum_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    norm_num
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hfour, hbal] at hsum
  linarith

/-- **THE DESCENT DICHOTOMY, GENERIC.**  Every chart point of a spanning
direction family carries a card-three positive definite selection or a stalled
positive definite four-label selection.  The five-label branch of the
trichotomy is deleted by the five-stall elimination. -/
theorem cardThree_or_cardFour_stall_of_span
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    (hspan : ∀ probe : Fin 3 → ℝ,
      (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0) :
    (∃ sel : Finset (Fin 6), sel.card = 3
        ∧ (directionChartGap direction point.mass point.weight sel).PosDef)
    ∨ (∃ sel : Finset (Fin 6), sel.card = 4
        ∧ (directionChartGap direction point.mass point.weight sel).PosDef
        ∧ ∀ label ∈ sel, 1 ≤ chartLadderPivot direction point.mass
            point.weight sel label) := by
  obtain ⟨missing, hpdFive, label, hmem, hlt⟩ :=
    exists_posDef_erase_univ_not_stall_of_span direction point hspan
  have hpdFour : (directionChartGap direction point.mass point.weight
      ((Finset.univ.erase missing).erase label)).PosDef :=
    (posDef_directionChartGap_erase_iff direction point.mass point.weight
      point.mass_pos point.weight_pos _ hmem hpdFive).mpr hlt
  have hcardFive : (Finset.univ.erase missing).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hcardFour : ((Finset.univ.erase missing).erase label).card = 4 := by
    rw [Finset.card_erase_of_mem hmem, hcardFive]
  by_cases hstallFour : ∀ inside ∈ (Finset.univ.erase missing).erase label,
      1 ≤ chartLadderPivot direction point.mass point.weight
        ((Finset.univ.erase missing).erase label) inside
  · exact Or.inr ⟨_, hcardFour, hpdFour, hstallFour⟩
  push Not at hstallFour
  obtain ⟨dropThree, hmemThree, hltThree⟩ := hstallFour
  have hpdThree : (directionChartGap direction point.mass point.weight
      (((Finset.univ.erase missing).erase label).erase dropThree)).PosDef :=
    (posDef_directionChartGap_erase_iff direction point.mass point.weight
      point.mass_pos point.weight_pos _ hmemThree hpdFour).mpr hltThree
  have hcardThree : (((Finset.univ.erase missing).erase label).erase
      dropThree).card = 3 := by
    rw [Finset.card_erase_of_mem hmemThree, hcardFour]
  exact Or.inl ⟨_, hcardThree, hpdThree⟩

/-! ## The three-lines instantiations -/

/-- The full-selection gap is positive definite at every three-lines chart
point, at every slide. -/
theorem posDef_directionChartGap_univ_threeLines (slide : ℝ)
    (point : DirectionChartPoint 6) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      Finset.univ).PosDef :=
  posDef_directionChartGap_univ_of_span _ point
    (threeLinesDirection_span slide)

/-- Every three-lines chart point carries a positive definite five-label
selection. -/
theorem exists_posDef_erase_univ_threeLines (slide : ℝ)
    (point : DirectionChartPoint 6) :
    ∃ label, (directionChartGap (threeLinesDirection slide) point.mass
      point.weight (Finset.univ.erase label)).PosDef :=
  exists_posDef_erase_univ_of_span _ point (threeLinesDirection_span slide)

/-- **THE A2 DESCENT.**  Every three-lines chart point carries a card-three
positive definite selection, or a stalled positive definite five-label
selection, or a stalled positive definite four-label selection.

The first branch is exactly A2's conclusion.  So A2's residual is the two
stall branches and nothing else: no case tree over the wall coordinates, and
no selection rule naming which triple fires. -/
theorem threeLines_cardThree_or_stall (slide : ℝ)
    (point : DirectionChartPoint 6) :
    (∃ sel : Finset (Fin 6), sel.card = 3
        ∧ (directionChartGap (threeLinesDirection slide) point.mass
            point.weight sel).PosDef)
    ∨ (∃ sel : Finset (Fin 6), sel.card = 5
        ∧ (directionChartGap (threeLinesDirection slide) point.mass
            point.weight sel).PosDef
        ∧ ∀ label ∈ sel, 1 ≤ chartLadderPivot (threeLinesDirection slide)
            point.mass point.weight sel label)
    ∨ (∃ sel : Finset (Fin 6), sel.card = 4
        ∧ (directionChartGap (threeLinesDirection slide) point.mass
            point.weight sel).PosDef
        ∧ ∀ label ∈ sel, 1 ≤ chartLadderPivot (threeLinesDirection slide)
            point.mass point.weight sel label) :=
  descent_trichotomy_of_span _ point (threeLinesDirection_span slide)

/-- Every three-lines chart point carries a positive definite five-label
selection which is not stalled. -/
theorem exists_posDef_erase_univ_not_stall_threeLines (slide : ℝ)
    (point : DirectionChartPoint 6) :
    ∃ missing : Fin 6,
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        (Finset.univ.erase missing)).PosDef ∧
      ∃ label ∈ Finset.univ.erase missing,
        chartLadderPivot (threeLinesDirection slide) point.mass point.weight
          (Finset.univ.erase missing) label < 1 :=
  exists_posDef_erase_univ_not_stall_of_span _ point
    (threeLinesDirection_span slide)

/-- **THE A2 DICHOTOMY.**  Every three-lines chart point carries a card-three
positive definite selection or a stalled positive definite four-label
selection.

The first branch is exactly A2's conclusion, at every slide and with no side
condition.  A2's whole residual is therefore the card-four stall: the
question is not which triple fires, but whether a stalled four-label
selection can exist at all. -/
theorem threeLines_cardThree_or_cardFour_stall (slide : ℝ)
    (point : DirectionChartPoint 6) :
    (∃ sel : Finset (Fin 6), sel.card = 3
        ∧ (directionChartGap (threeLinesDirection slide) point.mass
            point.weight sel).PosDef)
    ∨ (∃ sel : Finset (Fin 6), sel.card = 4
        ∧ (directionChartGap (threeLinesDirection slide) point.mass
            point.weight sel).PosDef
        ∧ ∀ label ∈ sel, 1 ≤ chartLadderPivot (threeLinesDirection slide)
            point.mass point.weight sel label) :=
  cardThree_or_cardFour_stall_of_span _ point (threeLinesDirection_span slide)

end Gtz
