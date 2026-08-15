import Gtz.Design.PivotWallVacuity
import Gtz.Reduction.MassGapDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The pivot balance law and the descent from the full selection

The chart gap is the coefficient combination of the direction atoms, with
positive coefficients on the selection and negative coefficients off it.  A
positive-definite gap therefore satisfies one exact trace identity: the
coefficient-weighted inverse readings of all directions sum to three.  In
pivot form the law reads

`sum over the selection of (1 - w) * pivot`
`  = 3 + sum over the complement of w * pivot`.

The law has direct consequences for the A3 endgame:

* `posDef_directionChartGap_univ` — the full-selection gap is positive
  definite at every K4 chart point;
* `exists_univ_pivot_lt_one` — the weighted average of the six full-selection
  pivots is three fifths, so some pivot is below one: **the descent from the
  full selection always starts**;
* `exists_posDef_erase_univ` — every K4 chart point carries a positive
  definite five-edge selection;
* `card_five_stall` — a stalled five-edge selection prices the missing label
  at pivot at least `1 + 1/w`;
* `pivotWall_exists_outside_pivot_ge_one` — a four-pivot wall forces a label
  outside its window with ladder pivot at least one.
-/

namespace Gtz

open Matrix

/-! ## The balance law -/

/-- **THE PIVOT BALANCE LAW, coefficient form.**  At a positive-definite
chart gap the coefficient-weighted inverse readings of all directions sum to
exactly three. -/
theorem chartCoeff_inv_balance {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size))
    (hpd : (directionChartGap direction mass weight selected).PosDef) :
    ∑ label, chartCoeff mass weight selected label
        * (direction label ⬝ᵥ
          ((directionChartGap direction mass weight selected)⁻¹
            *ᵥ direction label))
      = 3 := by
  have hunit : IsUnit (directionChartGap direction mass weight selected).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  have hterm : ∀ label : Fin size,
      chartCoeff mass weight selected label
        * (direction label ⬝ᵥ
          ((directionChartGap direction mass weight selected)⁻¹
            *ᵥ direction label))
      = ((directionChartGap direction mass weight selected)⁻¹
          * (chartCoeff mass weight selected label
              • atomMatrix (direction label))).trace := by
    intro label
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul]
  calc ∑ label, chartCoeff mass weight selected label
        * (direction label ⬝ᵥ
          ((directionChartGap direction mass weight selected)⁻¹
            *ᵥ direction label))
      = ∑ label, ((directionChartGap direction mass weight selected)⁻¹
          * (chartCoeff mass weight selected label
              • atomMatrix (direction label))).trace :=
        Finset.sum_congr rfl fun label _ => hterm label
    _ = ((directionChartGap direction mass weight selected)⁻¹
          * ∑ label, chartCoeff mass weight selected label
              • atomMatrix (direction label)).trace := by
        rw [Matrix.mul_sum, Matrix.trace_sum]
    _ = ((directionChartGap direction mass weight selected)⁻¹
          * directionChartGap direction mass weight selected).trace := by
        rw [← directionChartGap_eq_coeff_sum]
    _ = (1 : Matrix (Fin 3) (Fin 3) ℝ).trace := by
        rw [Matrix.nonsing_inv_mul _ hunit]
    _ = 3 := by rw [Matrix.trace_one, Fintype.card_fin]; norm_num

/-- **THE PIVOT BALANCE LAW, pivot form.**  The inside pivots weighted by the
weight complements balance the outside pivots weighted by the weights, around
three. -/
theorem pivot_balance {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (point : DirectionChartPoint size) (selected : Finset (Fin size))
    (hpd : (directionChartGap direction point.mass point.weight
      selected).PosDef) :
    ∑ label ∈ selected, (1 - point.weight label)
        * chartLadderPivot direction point.mass point.weight selected label
      = 3 + ∑ label ∈ selectedᶜ, point.weight label
          * chartLadderPivot direction point.mass point.weight selected
              label := by
  have hbal :=
    chartCoeff_inv_balance direction point.mass point.weight selected hpd
  rw [← Finset.sum_add_sum_compl selected] at hbal
  have hin : ∀ label ∈ selected,
      chartCoeff point.mass point.weight selected label
        * (direction label ⬝ᵥ
          ((directionChartGap direction point.mass point.weight selected)⁻¹
            *ᵥ direction label))
      = (1 - point.weight label)
          * chartLadderPivot direction point.mass point.weight selected
              label := by
    intro label hmem
    unfold chartCoeff chartLadderPivot
    rw [if_pos hmem]
    have hw := point.weight_pos label
    field_simp
  have hout : ∀ label ∈ selectedᶜ,
      chartCoeff point.mass point.weight selected label
        * (direction label ⬝ᵥ
          ((directionChartGap direction point.mass point.weight selected)⁻¹
            *ᵥ direction label))
      = -(point.weight label
          * chartLadderPivot direction point.mass point.weight selected
              label) := by
    intro label hmem
    unfold chartCoeff chartLadderPivot
    rw [if_neg (Finset.mem_compl.mp hmem)]
    have hw := point.weight_pos label
    field_simp
    ring
  rw [Finset.sum_congr rfl hin, Finset.sum_congr rfl hout,
    Finset.sum_neg_distrib] at hbal
  linarith

/-! ## The descent from the full selection -/

/-- The full-selection gap is positive definite at every K4 chart point: its
coefficients are the positive boosts `m (1 - w) / w`, and the six directions
span. -/
theorem posDef_directionChartGap_univ (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight
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
      ∃ label, kFourDirection label ⬝ᵥ probe ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (kFourDirection_span probe hall)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_pos' (fun label _ => ?_) ⟨witness, Finset.mem_univ _, ?_⟩
  · have hterm : point.mass label / point.weight label
        * (kFourDirection label ⬝ᵥ probe) ^ 2
        - point.mass label * (kFourDirection label ⬝ᵥ probe) ^ 2
      = (point.mass label / point.weight label - point.mass label)
        * (kFourDirection label ⬝ᵥ probe) ^ 2 := by ring
    rw [hterm]
    exact mul_nonneg (hd label).le (sq_nonneg _)
  · have hterm : point.mass witness / point.weight witness
        * (kFourDirection witness ⬝ᵥ probe) ^ 2
        - point.mass witness * (kFourDirection witness ⬝ᵥ probe) ^ 2
      = (point.mass witness / point.weight witness - point.mass witness)
        * (kFourDirection witness ⬝ᵥ probe) ^ 2 := by ring
    rw [hterm]
    exact mul_pos (hd witness)
      (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hwitness)))

/-- **THE FULL-SELECTION DESCENT.**  The six full-selection pivots have
weighted average three fifths, so some pivot is below one. -/
theorem exists_univ_pivot_lt_one (direction : Fin 6 → (Fin 3 → ℝ))
    (point : DirectionChartPoint 6)
    (hpd : (directionChartGap direction point.mass point.weight
      Finset.univ).PosDef) :
    ∃ label, chartLadderPivot direction point.mass point.weight
      Finset.univ label < 1 := by
  by_contra hall
  push Not at hall
  have hbal := pivot_balance direction point Finset.univ hpd
  rw [Finset.compl_univ, Finset.sum_empty, add_zero] at hbal
  have hterm : ∀ label ∈ Finset.univ, (1 - point.weight label)
      ≤ (1 - point.weight label)
        * chartLadderPivot direction point.mass point.weight Finset.univ
            label := by
    intro label _
    have hw1 := directionChartPoint_weight_lt_one point label
    exact le_mul_of_one_le_right (by linarith) (hall label)
  have hsum := Finset.sum_le_sum hterm
  have hfive : ∑ label, (1 - point.weight label) = (5 : ℝ) := by
    rw [Finset.sum_sub_distrib, point.weight_sum_one]
    simp
    norm_num
  rw [hfive, hbal] at hsum
  linarith

/-- Every K4 chart point carries a positive definite five-edge selection. -/
theorem exists_posDef_erase_univ (point : DirectionChartPoint 6) :
    ∃ label, (directionChartGap kFourDirection point.mass point.weight
      (Finset.univ.erase label)).PosDef := by
  obtain ⟨label, hlt⟩ := exists_univ_pivot_lt_one kFourDirection point
    (posDef_directionChartGap_univ point)
  exact ⟨label, (posDef_directionChartGap_erase_iff kFourDirection
    point.mass point.weight point.mass_pos point.weight_pos Finset.univ
    (Finset.mem_univ label) (posDef_directionChartGap_univ point)).mpr hlt⟩

/-! ## The stall laws -/

/-- **THE FIVE-EDGE STALL LAW.**  A positive definite five-edge selection
with every inside pivot at least one prices the missing label at pivot at
least `1 + 1/w`. -/
theorem card_five_stall (direction : Fin 6 → (Fin 3 → ℝ))
    (point : DirectionChartPoint 6) {missing : Fin 6}
    (hpd : (directionChartGap direction point.mass point.weight
      (Finset.univ.erase missing)).PosDef)
    (hstall : ∀ label ∈ Finset.univ.erase missing,
      1 ≤ chartLadderPivot direction point.mass point.weight
        (Finset.univ.erase missing) label) :
    1 + 1 / point.weight missing
      ≤ chartLadderPivot direction point.mass point.weight
          (Finset.univ.erase missing) missing := by
  have hbal := pivot_balance direction point (Finset.univ.erase missing) hpd
  have hcompl : (Finset.univ.erase missing)ᶜ = {missing} := by
    ext label
    simp [eq_comm]
  rw [hcompl, Finset.sum_singleton] at hbal
  have hterm : ∀ label ∈ Finset.univ.erase missing,
      (1 - point.weight label)
        ≤ (1 - point.weight label)
          * chartLadderPivot direction point.mass point.weight
              (Finset.univ.erase missing) label := by
    intro label hmem
    have hw1 := directionChartPoint_weight_lt_one point label
    exact le_mul_of_one_le_right (by linarith) (hstall label hmem)
  have hsum := Finset.sum_le_sum hterm
  have hbound : ∑ label ∈ Finset.univ.erase missing,
      (1 - point.weight label) = 4 + point.weight missing := by
    rw [Finset.sum_sub_distrib]
    have hone : ∑ _label ∈ Finset.univ.erase missing, (1 : ℝ) = 5 := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp
    have hweights : ∑ label ∈ Finset.univ.erase missing, point.weight label
        = 1 - point.weight missing := by
      have hsplit := Finset.add_sum_erase Finset.univ point.weight
        (Finset.mem_univ missing)
      have := point.weight_sum_one
      linarith
    rw [hone, hweights]
    ring
  have hw := point.weight_pos missing
  have hkey : 1 + point.weight missing
      ≤ point.weight missing
        * chartLadderPivot direction point.mass point.weight
            (Finset.univ.erase missing) missing := by
    rw [hbound] at hsum
    linarith
  have hdiv : 1 + 1 / point.weight missing
      = (1 + point.weight missing) / point.weight missing := by
    field_simp
    ring
  rw [hdiv, div_le_iff₀ hw]
  linarith [hkey, mul_comm (point.weight missing)
    (chartLadderPivot direction point.mass point.weight
      (Finset.univ.erase missing) missing)]

/-- **THE WALL'S OUTSIDE POINTER.**  A four-pivot wall over a spanning tree
forces a label outside its window with ladder pivot at least one. -/
theorem pivotWall_exists_outside_pivot_ge_one (point : DirectionChartPoint 6)
    {tree : Finset (Fin 6)} (htree : tree ∈ kFourSpanningTreeList)
    (hwall : KFourTreeWindowAllPivotWallData point tree) :
    ∃ pointer : Fin 6, pointer ∉ tree ∧
      ∃ label ∉ insert pointer tree,
        1 ≤ chartLadderPivot kFourDirection point.mass point.weight
          (insert pointer tree) label := by
  obtain ⟨pointer, hout, hpd, hpivots⟩ := hwall
  refine ⟨pointer, hout, ?_⟩
  by_contra hnone
  push Not at hnone
  have hbal := pivot_balance kFourDirection point (insert pointer tree) hpd
  have hterm : ∀ label ∈ insert pointer tree,
      (1 - point.weight label)
        ≤ (1 - point.weight label)
          * chartLadderPivot kFourDirection point.mass point.weight
              (insert pointer tree) label := by
    intro label hmem
    have hw1 := directionChartPoint_weight_lt_one point label
    exact le_mul_of_one_le_right (by linarith) (hpivots label hmem)
  have hsumW := Finset.sum_le_sum hterm
  have hcard : (insert pointer tree).card = 4 := by
    rw [Finset.card_insert_of_notMem hout, kFourSpanningTree_card tree htree]
  have hWsum : ∑ label ∈ insert pointer tree, (1 - point.weight label)
      = 4 - ∑ label ∈ insert pointer tree, point.weight label := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard]
    simp
  have hsplit : ∑ label ∈ insert pointer tree, point.weight label
      + ∑ label ∈ (insert pointer tree)ᶜ, point.weight label = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact point.weight_sum_one
  have hne : ((insert pointer tree)ᶜ : Finset (Fin 6)).Nonempty := by
    refine Finset.card_pos.mp ?_
    rw [Finset.card_compl, hcard]
    simp
  have hout_lt : ∑ label ∈ (insert pointer tree)ᶜ,
      point.weight label
        * chartLadderPivot kFourDirection point.mass point.weight
            (insert pointer tree) label
      < ∑ label ∈ (insert pointer tree)ᶜ, point.weight label := by
    refine Finset.sum_lt_sum_of_nonempty hne fun label hmem => ?_
    have hlt := hnone label (Finset.mem_compl.mp hmem)
    have hw := point.weight_pos label
    nlinarith
  rw [hWsum] at hsumW
  linarith

/-! ## The descent trichotomy -/

/-- **THE DESCENT TRICHOTOMY.**  Every K4 chart point carries a strict
spanning tree, or a stalled positive definite five-edge selection, or a
stalled positive definite four-edge selection.  The stalls are the only
obstructions between the always-strict full selection and a strict tree. -/
theorem kFour_descent_trichotomy (point : DirectionChartPoint 6) :
    (∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef)
    ∨ (∃ sel : Finset (Fin 6), sel.card = 5
        ∧ (directionChartGap kFourDirection point.mass point.weight
            sel).PosDef
        ∧ ∀ label ∈ sel, 1 ≤ chartLadderPivot kFourDirection point.mass
            point.weight sel label)
    ∨ (∃ sel : Finset (Fin 6), sel.card = 4
        ∧ (directionChartGap kFourDirection point.mass point.weight
            sel).PosDef
        ∧ ∀ label ∈ sel, 1 ≤ chartLadderPivot kFourDirection point.mass
            point.weight sel label) := by
  obtain ⟨dropFive, hpdFive⟩ := exists_posDef_erase_univ point
  have hcardFive : (Finset.univ.erase dropFive).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  by_cases hstallFive : ∀ label ∈ Finset.univ.erase dropFive,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight
        (Finset.univ.erase dropFive) label
  · exact Or.inr (Or.inl ⟨_, hcardFive, hpdFive, hstallFive⟩)
  push Not at hstallFive
  obtain ⟨dropFour, hmemFour, hltFour⟩ := hstallFive
  have hpdFour : (directionChartGap kFourDirection point.mass point.weight
      ((Finset.univ.erase dropFive).erase dropFour)).PosDef :=
    (posDef_directionChartGap_erase_iff kFourDirection point.mass
      point.weight point.mass_pos point.weight_pos _ hmemFour hpdFive).mpr
      hltFour
  have hcardFour : ((Finset.univ.erase dropFive).erase dropFour).card = 4 := by
    rw [Finset.card_erase_of_mem hmemFour, hcardFive]
  by_cases hstallFour : ∀ label ∈ (Finset.univ.erase dropFive).erase dropFour,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight
        ((Finset.univ.erase dropFive).erase dropFour) label
  · exact Or.inr (Or.inr ⟨_, hcardFour, hpdFour, hstallFour⟩)
  push Not at hstallFour
  obtain ⟨dropThree, hmemThree, hltThree⟩ := hstallFour
  have hpdThree : (directionChartGap kFourDirection point.mass point.weight
      (((Finset.univ.erase dropFive).erase dropFour).erase
        dropThree)).PosDef :=
    (posDef_directionChartGap_erase_iff kFourDirection point.mass
      point.weight point.mass_pos point.weight_pos _ hmemThree hpdFour).mpr
      hltThree
  have hcardThree : (((Finset.univ.erase dropFive).erase dropFour).erase
      dropThree).card = 3 := by
    rw [Finset.card_erase_of_mem hmemThree, hcardFour]
  refine Or.inl ⟨_, mem_kFourSpanningTreeList_of_card_three _ hcardThree
    ?_, hpdThree⟩
  intro htriangle
  exact kFourTriangle_gap_not_posDef point _ htriangle hpdThree

end Gtz
