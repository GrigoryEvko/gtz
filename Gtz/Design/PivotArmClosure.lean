import Gtz.Design.PivotStallPropagation
import Gtz.Design.StallConfinement

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The unified stall law and the five-stall elimination

The pivot balance law is an identity, so it cannot by itself contradict a
stall: the five-edge price `1 + 1/w` is *derived* from the balance and is the
sharp value the balance permits.  The independent lever is the landed
insertion law `chartLadderPivot_insert_self`, which transports a price at a
base to a price at the base with one more label — the opposite direction to
the monotonicity of the pivot.

* `stall_outside_price` — the unified stall law.  A stalled positive-definite
  selection of `k` labels prices its complement by
  `sum over the complement of w * (pivot - 1) >= k - 4`.  At `k = 6` this reads
  `0 >= 2` and reproves that the full selection never stalls, at `k = 5` it is
  the landed five-edge price, and at `k = 4` it is the two-label law below.
* `card_four_stall` — the four-edge instance: the two outside pivots of a
  stalled four-edge selection have weighted average at least one.
* `exists_posDef_erase_univ_not_stall` — **the five-stall elimination**.  Every
  chart point carries a positive-definite five-edge selection which is *not*
  stalled.  A stalled one prices its missing label at `1 + 1/w`, the insertion
  law then pushes the matching full-selection pivot up to `(1 + w)/(1 + 2w)`,
  and the balance at the full selection reads `3 >= 4`.
* `kFour_strictTree_or_cardFour_stall` — **the descent dichotomy**.  The
  five-edge branch of the landed trichotomy is deleted: every chart point
  carries a strict spanning tree or a stalled four-edge selection.
-/

namespace Gtz

open Matrix

/-! ## The unified stall law -/

/-- **THE UNIFIED STALL LAW.**  A stalled positive-definite selection of `k`
labels prices its complement: the weight-weighted excess of the outside pivots
above one is at least `k - 4`. -/
theorem stall_outside_price (direction : Fin 6 → (Fin 3 → ℝ))
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hpd : (directionChartGap direction point.mass point.weight
      selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot direction point.mass point.weight selected label) :
    (selected.card : ℝ) - 4
      ≤ ∑ label ∈ selectedᶜ, point.weight label
          * (chartLadderPivot direction point.mass point.weight selected
              label - 1) := by
  have hbal := pivot_balance direction point selected hpd
  have hterm : ∀ label ∈ selected, (1 - point.weight label)
      ≤ (1 - point.weight label)
        * chartLadderPivot direction point.mass point.weight selected label := by
    intro label hmem
    have hw1 := directionChartPoint_weight_lt_one point label
    exact le_mul_of_one_le_right (by linarith) (hstall label hmem)
  have hsum := Finset.sum_le_sum hterm
  have hleft : ∑ label ∈ selected, (1 - point.weight label)
      = (selected.card : ℝ) - ∑ label ∈ selected, point.weight label := by
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp
  have hsplit : ∑ label ∈ selected, point.weight label
      + ∑ label ∈ selectedᶜ, point.weight label = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact point.weight_sum_one
  have hright : ∑ label ∈ selectedᶜ, point.weight label
        * (chartLadderPivot direction point.mass point.weight selected
            label - 1)
      = ∑ label ∈ selectedᶜ, point.weight label
          * chartLadderPivot direction point.mass point.weight selected label
        - ∑ label ∈ selectedᶜ, point.weight label := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by ring
  rw [hleft] at hsum
  rw [hright]
  linarith

/-- **THE FOUR-EDGE STALL LAW.**  A stalled positive-definite four-edge
selection has two outside labels whose pivots have weighted average at least
one. -/
theorem card_four_stall (direction : Fin 6 → (Fin 3 → ℝ))
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hcard : selected.card = 4)
    (hpd : (directionChartGap direction point.mass point.weight
      selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot direction point.mass point.weight selected label) :
    0 ≤ ∑ label ∈ selectedᶜ, point.weight label
          * (chartLadderPivot direction point.mass point.weight selected
              label - 1) := by
  have hprice := stall_outside_price direction point selected hpd hstall
  rw [hcard] at hprice
  norm_num at hprice
  exact hprice

/-! ## The five-stall elimination -/

/-- **THE FIVE-STALL ELIMINATION.**  Every K4 chart point carries a positive
definite five-edge selection which is not stalled.

A stalled one would price its missing label at `1 + 1/w`; the insertion law
would raise the matching full-selection pivot to at least `(1 + w)/(1 + 2w)`,
which is at least `1 - 2w`; and the balance at the full selection would then
read `3 >= 4`. -/
theorem exists_posDef_erase_univ_not_stall (point : DirectionChartPoint 6) :
    ∃ missing : Fin 6,
      (directionChartGap kFourDirection point.mass point.weight
        (Finset.univ.erase missing)).PosDef ∧
      ∃ label ∈ Finset.univ.erase missing,
        chartLadderPivot kFourDirection point.mass point.weight
          (Finset.univ.erase missing) label < 1 := by
  by_contra hall
  push Not at hall
  have hunivPD := posDef_directionChartGap_univ point
  have hlow : ∀ missing : Fin 6,
      1 - 2 * point.weight missing
        ≤ (1 - point.weight missing)
          * chartLadderPivot kFourDirection point.mass point.weight
              Finset.univ missing := by
    intro missing
    have hw := point.weight_pos missing
    have hw1 := directionChartPoint_weight_lt_one point missing
    by_cases hpd : (directionChartGap kFourDirection point.mass point.weight
        (Finset.univ.erase missing)).PosDef
    · have hstall := hall missing hpd
      have hprice := card_five_stall kFourDirection point hpd hstall
      have hnot : missing ∉ Finset.univ.erase missing := Finset.notMem_erase _ _
      have hinsert : insert missing (Finset.univ.erase missing)
          = (Finset.univ : Finset (Fin 6)) :=
        Finset.insert_erase (Finset.mem_univ missing)
      have hlaw := chartLadderPivot_insert_self kFourDirection point.mass
        point.weight point.mass_pos point.weight_pos
        (Finset.univ.erase missing) hnot hpd
      rw [hinsert] at hlaw
      have hPpos : (0 : ℝ) < chartLadderPivot kFourDirection point.mass
          point.weight (Finset.univ.erase missing) missing :=
        lt_of_lt_of_le (by positivity) hprice
      have hwP : 1 + point.weight missing
          ≤ point.weight missing
            * chartLadderPivot kFourDirection point.mass point.weight
                (Finset.univ.erase missing) missing := by
        have hmul := mul_le_mul_of_nonneg_left hprice hw.le
        have hexp : point.weight missing * (1 + 1 / point.weight missing)
            = 1 + point.weight missing := by
          field_simp
          ring
        rw [hexp] at hmul
        exact hmul
      have hden : (0 : ℝ) < 1 + chartLadderPivot kFourDirection point.mass
          point.weight (Finset.univ.erase missing) missing := by linarith
      rw [hlaw]
      have hshape : (1 - point.weight missing)
            * (chartLadderPivot kFourDirection point.mass point.weight
                (Finset.univ.erase missing) missing
              / (1 + chartLadderPivot kFourDirection point.mass point.weight
                  (Finset.univ.erase missing) missing))
          = ((1 - point.weight missing)
              * chartLadderPivot kFourDirection point.mass point.weight
                  (Finset.univ.erase missing) missing)
            / (1 + chartLadderPivot kFourDirection point.mass point.weight
                (Finset.univ.erase missing) missing) := by ring
      rw [hshape, le_div_iff₀ hden]
      nlinarith [hwP, hw, hw1]
    · have hge : 1 ≤ chartLadderPivot kFourDirection point.mass point.weight
          Finset.univ missing := by
        by_contra hlt
        push Not at hlt
        exact hpd ((posDef_directionChartGap_erase_iff kFourDirection
          point.mass point.weight point.mass_pos point.weight_pos Finset.univ
          (Finset.mem_univ missing) hunivPD).mpr hlt)
      nlinarith [hge, hw, hw1]
  have hbal := pivot_balance kFourDirection point Finset.univ hunivPD
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

/-- **THE DESCENT DICHOTOMY.**  Every K4 chart point carries a strict spanning
tree or a stalled positive-definite four-edge selection.  The five-edge branch
of the landed trichotomy is deleted by the five-stall elimination. -/
theorem kFour_strictTree_or_cardFour_stall (point : DirectionChartPoint 6) :
    (∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef)
    ∨ (∃ sel : Finset (Fin 6), sel.card = 4
        ∧ (directionChartGap kFourDirection point.mass point.weight
            sel).PosDef
        ∧ ∀ label ∈ sel, 1 ≤ chartLadderPivot kFourDirection point.mass
            point.weight sel label) := by
  obtain ⟨missing, hpdFive, label, hmem, hlt⟩ :=
    exists_posDef_erase_univ_not_stall point
  have hpdFour : (directionChartGap kFourDirection point.mass point.weight
      ((Finset.univ.erase missing).erase label)).PosDef :=
    (posDef_directionChartGap_erase_iff kFourDirection point.mass point.weight
      point.mass_pos point.weight_pos _ hmem hpdFive).mpr hlt
  have hcardFive : (Finset.univ.erase missing).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hcardFour : ((Finset.univ.erase missing).erase label).card = 4 := by
    rw [Finset.card_erase_of_mem hmem, hcardFive]
  rcases exists_strictTree_or_cardFour_stall_of_posDef point hcardFour hpdFour
    with hstrict | hstall
  · exact Or.inl hstrict
  · exact Or.inr ⟨_, hcardFour, hpdFour, hstall⟩

end Gtz
