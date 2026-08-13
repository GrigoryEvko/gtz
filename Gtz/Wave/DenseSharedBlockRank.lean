import Gtz.Wave.DenseHeavyFiveStructure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The dense shared-block rank — the rank-one gap block and its budget

Two basis slots on one dense block carry two independent kernel vectors
of the shifted gap block.  The axis kill makes every pairwise cross
determinant nonzero, thus the cofactor identities of the two directions
cross-multiply to zero.  The shifted gap block loses every pair minor:
it has rank one.

The rank-one dictionary is six scalar equations in the six gap entries
of the block.  Three price the pair minors, three price the products of
the off-diagonal entries.  Together they make the product of the three
off-diagonal entries the product of the three shifted diagonal entries —
a sign law with no complex counterpart.

The row square budget then caps the block: the shifted diagonal entry of
one atom times the sum of the other two is at most one quarter.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.triple_insert_rotate_two` — the second rotation of an atom
  triple.
* `Gtz.shared_block_crossDet_ne_zero`,
  `Gtz.shared_block_crossDet_ne_zero_second`,
  `Gtz.shared_block_crossDet_ne_zero_third` — **THE THREE
  NONDEGENERACIES.**
* `Gtz.shared_block_minor_and_cofactors` — **THE RANK-ONE CORE.**
* `Gtz.shared_block_rank_one` — **THE FULL DICTIONARY:** three pair
  minors and three cofactor products.
* `Gtz.shared_block_offdiag_product` — the sign law.
* `Gtz.shared_block_row_budget` — **THE BUDGET.**
* `Gtz.SixThreeCrux.shared_block_row_quarter` — the quarter cap.
* `Gtz.RankFiveFrame.shared_support_rank_one`,
  `Gtz.RankSixFrame.shared_support_rank_one` — the frame dictionaries.
* `Gtz.RankFiveFrame.shared_support_row_quarter`,
  `Gtz.RankSixFrame.shared_support_row_quarter` — the frame budgets.

## Vacuity

The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the three nondegeneracies -/

/-- The second rotation of an atom triple. -/
theorem triple_insert_rotate_two {α : Type*} [DecidableEq α]
    (first second third : α) :
    ({first, second, third} : Finset α) = {third, first, second} := by
  ext atomIndex
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The first cross determinant of a shared block does not vanish. -/
theorem shared_block_crossDet_ne_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {slotOne slotTwo : Fin basisCount} (hslot : slotOne ≠ slotTwo)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    {atomA atomB atomC : Fin size} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport tightDir (basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport tightDir (basisLabel slotTwo)
      = {atomA, atomB, atomC})
    (hdiagC : chartStationaryGap projection weight atomC atomC ≠ value) :
    tightDir (basisLabel slotOne) atomA * tightDir (basisLabel slotTwo) atomB
      - tightDir (basisLabel slotOne) atomB
        * tightDir (basisLabel slotTwo) atomA ≠ 0 :=
  fun hcross => false_of_shared_block_cross_zero hdata basisLabel leftInv hleft
    hslot hmemOne hmemTwo hAB hAC hBC hsupportOne hsupportTwo hdiagC hcross

/-- The second cross determinant of a shared block does not vanish. -/
theorem shared_block_crossDet_ne_zero_second
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {slotOne slotTwo : Fin basisCount} (hslot : slotOne ≠ slotTwo)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    {atomA atomB atomC : Fin size} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport tightDir (basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport tightDir (basisLabel slotTwo)
      = {atomA, atomB, atomC})
    (hdiagA : chartStationaryGap projection weight atomA atomA ≠ value) :
    tightDir (basisLabel slotOne) atomB * tightDir (basisLabel slotTwo) atomC
      - tightDir (basisLabel slotOne) atomC
        * tightDir (basisLabel slotTwo) atomB ≠ 0 :=
  fun hcross => false_of_shared_block_cross_zero hdata basisLabel leftInv hleft
    hslot hmemOne hmemTwo hBC (Ne.symm hAB) (Ne.symm hAC)
    (by rw [hsupportOne, triple_insert_rotate])
    (by rw [hsupportTwo, triple_insert_rotate]) hdiagA hcross

/-- The third cross determinant of a shared block does not vanish. -/
theorem shared_block_crossDet_ne_zero_third
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {slotOne slotTwo : Fin basisCount} (hslot : slotOne ≠ slotTwo)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    {atomA atomB atomC : Fin size} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport tightDir (basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport tightDir (basisLabel slotTwo)
      = {atomA, atomB, atomC})
    (hdiagB : chartStationaryGap projection weight atomB atomB ≠ value) :
    tightDir (basisLabel slotOne) atomA * tightDir (basisLabel slotTwo) atomC
      - tightDir (basisLabel slotOne) atomC
        * tightDir (basisLabel slotTwo) atomA ≠ 0 := by
  intro hcross
  refine false_of_shared_block_cross_zero hdata basisLabel leftInv hleft hslot
    hmemOne hmemTwo (Ne.symm hAC) (Ne.symm hBC) hAB
    (by rw [hsupportOne, triple_insert_rotate_two])
    (by rw [hsupportTwo, triple_insert_rotate_two]) hdiagB ?_
  linear_combination -hcross

/-! ## Layer 2 — the rank-one core -/

/-- **THE RANK-ONE CORE.**  Two slots on one block kill the shifted pair
minor of the first two atoms and both of its cofactors. -/
theorem shared_block_minor_and_cofactors
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {slotOne slotTwo : Fin basisCount} (hslot : slotOne ≠ slotTwo)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    {atomA atomB atomC : Fin size} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport tightDir (basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport tightDir (basisLabel slotTwo)
      = {atomA, atomB, atomC})
    (hdiagB : chartStationaryGap projection weight atomB atomB ≠ value)
    (hdiagC : chartStationaryGap projection weight atomC atomC ≠ value) :
    (chartStationaryGap projection weight atomA atomA - value)
          * (chartStationaryGap projection weight atomB atomB - value)
        - chartStationaryGap projection weight atomA atomB
          * chartStationaryGap projection weight atomA atomB = 0
      ∧ chartStationaryGap projection weight atomA atomB
          * chartStationaryGap projection weight atomB atomC
        = (chartStationaryGap projection weight atomB atomB - value)
          * chartStationaryGap projection weight atomA atomC
      ∧ chartStationaryGap projection weight atomA atomB
          * chartStationaryGap projection weight atomA atomC
        = (chartStationaryGap projection weight atomA atomA - value)
          * chartStationaryGap projection weight atomB atomC := by
  have hmemA : atomA ∈ ({atomA, atomB, atomC} : Finset (Fin size)) :=
    Finset.mem_insert_self _ _
  have hmemB : atomB ∈ ({atomA, atomB, atomC} : Finset (Fin size)) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hmemC : atomC ∈ ({atomA, atomB, atomC} : Finset (Fin size)) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have hrowAOne := block_eigen_row hdata hmemOne hAB hAC hBC hsupportOne hmemA
  have hrowBOne := block_eigen_row hdata hmemOne hAB hAC hBC hsupportOne hmemB
  have hrowATwo := block_eigen_row hdata hmemTwo hAB hAC hBC hsupportTwo hmemA
  have hrowBTwo := block_eigen_row hdata hmemTwo hAB hAC hBC hsupportTwo hmemB
  rw [gap_entry_symm hdata atomB atomA] at hrowBOne hrowBTwo
  have hcofOne := block_cofactor_first hrowAOne hrowBOne
  have hcofTwo := block_cofactor_first hrowATwo hrowBTwo
  have hcofSecondOne := block_cofactor_second hrowAOne hrowBOne
  have hcofSecondTwo := block_cofactor_second hrowATwo hrowBTwo
  have hcrossAC := shared_block_crossDet_ne_zero_third hdata basisLabel leftInv
    hleft hslot hmemOne hmemTwo hAB hAC hBC hsupportOne hsupportTwo hdiagB
  have hminorMul : ((chartStationaryGap projection weight atomA atomA - value)
        * (chartStationaryGap projection weight atomB atomB - value)
      - chartStationaryGap projection weight atomA atomB
        * chartStationaryGap projection weight atomA atomB)
      * (tightDir (basisLabel slotOne) atomA
          * tightDir (basisLabel slotTwo) atomC
        - tightDir (basisLabel slotOne) atomC
          * tightDir (basisLabel slotTwo) atomA) = 0 := by
    linear_combination tightDir (basisLabel slotTwo) atomC * hcofOne
      - tightDir (basisLabel slotOne) atomC * hcofTwo
  have hminor : (chartStationaryGap projection weight atomA atomA - value)
        * (chartStationaryGap projection weight atomB atomB - value)
      - chartStationaryGap projection weight atomA atomB
        * chartStationaryGap projection weight atomA atomB = 0 := by
    rcases mul_eq_zero.mp hminorMul with hcase | hcase
    · exact hcase
    · exact absurd hcase hcrossAC
  have hcoordC : tightDir (basisLabel slotOne) atomC ≠ 0 :=
    tightDir_ne_zero_of_support_triple hsupportOne hmemC
  refine ⟨hminor, ?_, ?_⟩
  · have hzero : (chartStationaryGap projection weight atomA atomB
          * chartStationaryGap projection weight atomB atomC
        - (chartStationaryGap projection weight atomB atomB - value)
          * chartStationaryGap projection weight atomA atomC)
        * tightDir (basisLabel slotOne) atomC = 0 := by
      linear_combination -hcofOne
        + tightDir (basisLabel slotOne) atomA * hminor
    rcases mul_eq_zero.mp hzero with hcase | hcase
    · linarith [hcase]
    · exact absurd hcase hcoordC
  · have hzero : (chartStationaryGap projection weight atomA atomB
          * chartStationaryGap projection weight atomA atomC
        - (chartStationaryGap projection weight atomA atomA - value)
          * chartStationaryGap projection weight atomB atomC)
        * tightDir (basisLabel slotOne) atomC = 0 := by
      linear_combination -hcofSecondOne
        + tightDir (basisLabel slotOne) atomB * hminor
    rcases mul_eq_zero.mp hzero with hcase | hcase
    · linarith [hcase]
    · exact absurd hcase hcoordC

/-! ## Layer 3 — the full dictionary -/

/-- **THE RANK-ONE DICTIONARY.**  Two slots on one block make the
shifted gap block rank one: every pair minor vanishes, and every
off-diagonal product reads the opposite shifted diagonal entry times the
third off-diagonal entry. -/
theorem shared_block_rank_one
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {slotOne slotTwo : Fin basisCount} (hslot : slotOne ≠ slotTwo)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    {atomA atomB atomC : Fin size} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport tightDir (basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport tightDir (basisLabel slotTwo)
      = {atomA, atomB, atomC})
    (hdiagA : chartStationaryGap projection weight atomA atomA ≠ value)
    (hdiagB : chartStationaryGap projection weight atomB atomB ≠ value)
    (hdiagC : chartStationaryGap projection weight atomC atomC ≠ value) :
    (chartStationaryGap projection weight atomA atomA - value)
          * (chartStationaryGap projection weight atomB atomB - value)
        = chartStationaryGap projection weight atomA atomB
          * chartStationaryGap projection weight atomA atomB
      ∧ (chartStationaryGap projection weight atomB atomB - value)
          * (chartStationaryGap projection weight atomC atomC - value)
        = chartStationaryGap projection weight atomB atomC
          * chartStationaryGap projection weight atomB atomC
      ∧ (chartStationaryGap projection weight atomA atomA - value)
          * (chartStationaryGap projection weight atomC atomC - value)
        = chartStationaryGap projection weight atomA atomC
          * chartStationaryGap projection weight atomA atomC
      ∧ chartStationaryGap projection weight atomA atomB
          * chartStationaryGap projection weight atomB atomC
        = (chartStationaryGap projection weight atomB atomB - value)
          * chartStationaryGap projection weight atomA atomC
      ∧ chartStationaryGap projection weight atomA atomB
          * chartStationaryGap projection weight atomA atomC
        = (chartStationaryGap projection weight atomA atomA - value)
          * chartStationaryGap projection weight atomB atomC
      ∧ chartStationaryGap projection weight atomA atomC
          * chartStationaryGap projection weight atomB atomC
        = (chartStationaryGap projection weight atomC atomC - value)
          * chartStationaryGap projection weight atomA atomB := by
  obtain ⟨hminorAB, hcofB, hcofA⟩ := shared_block_minor_and_cofactors hdata
    basisLabel leftInv hleft hslot hmemOne hmemTwo hAB hAC hBC hsupportOne
    hsupportTwo hdiagB hdiagC
  obtain ⟨hminorBC, hcofC, _hcofBsecond⟩ := shared_block_minor_and_cofactors
    hdata basisLabel leftInv hleft hslot hmemOne hmemTwo hBC (Ne.symm hAB)
    (Ne.symm hAC) (by rw [hsupportOne, triple_insert_rotate])
    (by rw [hsupportTwo, triple_insert_rotate]) hdiagC hdiagA
  obtain ⟨hminorCA, _hcofA', _hcofC'⟩ := shared_block_minor_and_cofactors hdata
    basisLabel leftInv hleft hslot hmemOne hmemTwo (Ne.symm hAC) (Ne.symm hBC)
    hAB (by rw [hsupportOne, triple_insert_rotate_two])
    (by rw [hsupportTwo, triple_insert_rotate_two]) hdiagA hdiagB
  rw [gap_entry_symm hdata atomC atomA] at hminorCA hcofC
  rw [gap_entry_symm hdata atomB atomA] at hcofC
  refine ⟨by linarith [hminorAB], by linarith [hminorBC], by linarith [hminorCA],
    hcofB, hcofA, ?_⟩
  linear_combination hcofC

/-- **THE SIGN LAW.**  The product of the three off-diagonal gap entries
of a shared block is the product of the three shifted diagonal
entries. -/
theorem shared_block_offdiag_product
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {slotOne slotTwo : Fin basisCount} (hslot : slotOne ≠ slotTwo)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    {atomA atomB atomC : Fin size} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport tightDir (basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport tightDir (basisLabel slotTwo)
      = {atomA, atomB, atomC})
    (hdiagA : chartStationaryGap projection weight atomA atomA ≠ value)
    (hdiagB : chartStationaryGap projection weight atomB atomB ≠ value)
    (hdiagC : chartStationaryGap projection weight atomC atomC ≠ value) :
    chartStationaryGap projection weight atomA atomB
        * chartStationaryGap projection weight atomB atomC
        * chartStationaryGap projection weight atomA atomC
      = (chartStationaryGap projection weight atomA atomA - value)
        * (chartStationaryGap projection weight atomB atomB - value)
        * (chartStationaryGap projection weight atomC atomC - value) := by
  obtain ⟨hminorAB, _hminorBC, hminorCA, hcofB, _hcofA, _hcofC⟩ :=
    shared_block_rank_one hdata basisLabel leftInv hleft hslot hmemOne hmemTwo
      hAB hAC hBC hsupportOne hsupportTwo hdiagA hdiagB hdiagC
  linear_combination chartStationaryGap projection weight atomA atomC * hcofB
    - (chartStationaryGap projection weight atomB atomB - value) * hminorCA

/-! ## Layer 4 — the row square budget -/

/-- **THE BUDGET.**  The shifted diagonal entry of one atom of a shared
block times the sum of the other two is capped by the row square of the
chart. -/
theorem shared_block_row_budget
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {slotOne slotTwo : Fin basisCount} (hslot : slotOne ≠ slotTwo)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    {atomA atomB atomC : Fin size} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport tightDir (basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport tightDir (basisLabel slotTwo)
      = {atomA, atomB, atomC})
    (hdiagA : chartStationaryGap projection weight atomA atomA ≠ value)
    (hdiagB : chartStationaryGap projection weight atomB atomB ≠ value)
    (hdiagC : chartStationaryGap projection weight atomC atomC ≠ value) :
    (chartStationaryGap projection weight atomA atomA - value)
        * ((chartStationaryGap projection weight atomB atomB - value)
          + (chartStationaryGap projection weight atomC atomC - value))
      ≤ projection atomA atomA - projection atomA atomA * projection atomA atomA := by
  classical
  obtain ⟨hminorAB, _hminorBC, hminorCA, _hcofB, _hcofA, _hcofC⟩ :=
    shared_block_rank_one hdata basisLabel leftInv hleft hslot hmemOne hmemTwo
      hAB hAC hBC hsupportOne hsupportTwo hdiagA hdiagB hdiagC
  have hsquare := projection_offdiag_square hdata atomA
  have hmemB : atomB ∈ Finset.univ.erase atomA :=
    Finset.mem_erase.mpr ⟨Ne.symm hAB, Finset.mem_univ _⟩
  have hsplitB := Finset.add_sum_erase (Finset.univ.erase atomA)
    (fun atomCol : Fin size => projection atomA atomCol * projection atomA atomCol)
    hmemB
  have hmemC : atomC ∈ (Finset.univ.erase atomA).erase atomB :=
    Finset.mem_erase.mpr ⟨Ne.symm hBC,
      Finset.mem_erase.mpr ⟨Ne.symm hAC, Finset.mem_univ _⟩⟩
  have hsplitC := Finset.add_sum_erase ((Finset.univ.erase atomA).erase atomB)
    (fun atomCol : Fin size => projection atomA atomCol * projection atomA atomCol)
    hmemC
  have hrest : 0 ≤ ∑ atomCol ∈ (((Finset.univ.erase atomA).erase atomB).erase
      atomC), projection atomA atomCol * projection atomA atomCol :=
    Finset.sum_nonneg fun atomCol _ => mul_self_nonneg _
  have hentryB : projection atomA atomB
      = chartStationaryGap projection weight atomA atomB := by
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hAB,
      sub_zero]
  have hentryC : projection atomA atomC
      = chartStationaryGap projection weight atomA atomC := by
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hAC,
      sub_zero]
  rw [hentryB] at hsplitB
  rw [hentryC] at hsplitC
  nlinarith [hsquare, hsplitB, hsplitC, hrest, hminorAB, hminorCA]

/-- The quarter cap of the shared-block budget at a crux. -/
theorem SixThreeCrux.shared_block_row_quarter (crux : SixThreeCrux)
    {activeIndex : Type} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin 6 → ℝ)}
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    {basisCount : ℕ} (basisLabel : Fin basisCount → activeIndex)
    (leftInv : Matrix (Fin basisCount) (Fin 6) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {slotOne slotTwo : Fin basisCount} (hslot : slotOne ≠ slotTwo)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    {atomA atomB atomC : Fin 6} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport tightDir (basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport tightDir (basisLabel slotTwo)
      = {atomA, atomB, atomC}) :
    (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomA
        - chartObjective (chartPointOfDesign crux.design))
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design))
          + (chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomC atomC
            - chartObjective (chartPointOfDesign crux.design)))
      ≤ 1 / 4 := by
  have hbudget := shared_block_row_budget hdata basisLabel leftInv hleft hslot
    hmemOne hmemTwo hAB hAC hBC hsupportOne hsupportTwo
    (crux.gap_diagonal_ne_value atomA) (crux.gap_diagonal_ne_value atomB)
    (crux.gap_diagonal_ne_value atomC)
  nlinarith [hbudget, sq_nonneg ((chartPointOfDesign crux.design).chart atomA
    atomA - 1 / 2)]

/-! ## Layer 5 — the frame dictionaries -/

/-- The rank-five frame dictionary of a shared support. -/
theorem RankFiveFrame.shared_support_rank_one {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {slotOne slotTwo : Fin 5}
    (hslot : slotOne ≠ slotTwo) {atomA atomB atomC : Fin 6}
    (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC) (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport frame.tightDir (frame.basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
      = {atomA, atomB, atomC}) :
    (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomA
        - chartObjective (chartPointOfDesign crux.design))
        * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design))
      = chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomB
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomB
    ∧ chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomB
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomC
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomC
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA atomA
          - chartObjective (chartPointOfDesign crux.design))
        * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design))
        * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomC atomC
          - chartObjective (chartPointOfDesign crux.design)) := by
  obtain ⟨hminorAB, _, _, _, _, _⟩ := shared_block_rank_one frame.hdata
    frame.basisLabel frame.leftInv frame.hleft hslot (frame.hmemAll slotOne)
    (frame.hmemAll slotTwo) hAB hAC hBC hsupportOne hsupportTwo
    (crux.gap_diagonal_ne_value atomA) (crux.gap_diagonal_ne_value atomB)
    (crux.gap_diagonal_ne_value atomC)
  exact ⟨hminorAB, shared_block_offdiag_product frame.hdata frame.basisLabel
    frame.leftInv frame.hleft hslot (frame.hmemAll slotOne)
    (frame.hmemAll slotTwo) hAB hAC hBC hsupportOne hsupportTwo
    (crux.gap_diagonal_ne_value atomA) (crux.gap_diagonal_ne_value atomB)
    (crux.gap_diagonal_ne_value atomC)⟩

/-- The rank-six frame dictionary of a shared support. -/
theorem RankSixFrame.shared_support_rank_one {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {slotOne slotTwo : Fin 6}
    (hslot : slotOne ≠ slotTwo) {atomA atomB atomC : Fin 6}
    (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC) (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport frame.tightDir (frame.basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
      = {atomA, atomB, atomC}) :
    (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomA
        - chartObjective (chartPointOfDesign crux.design))
        * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design))
      = chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomB
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomB
    ∧ chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomB
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomC
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomC
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA atomA
          - chartObjective (chartPointOfDesign crux.design))
        * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design))
        * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomC atomC
          - chartObjective (chartPointOfDesign crux.design)) := by
  obtain ⟨hminorAB, _, _, _, _, _⟩ := shared_block_rank_one frame.hdata
    frame.basisLabel frame.leftInv frame.hleft hslot (frame.hmemAll slotOne)
    (frame.hmemAll slotTwo) hAB hAC hBC hsupportOne hsupportTwo
    (crux.gap_diagonal_ne_value atomA) (crux.gap_diagonal_ne_value atomB)
    (crux.gap_diagonal_ne_value atomC)
  exact ⟨hminorAB, shared_block_offdiag_product frame.hdata frame.basisLabel
    frame.leftInv frame.hleft hslot (frame.hmemAll slotOne)
    (frame.hmemAll slotTwo) hAB hAC hBC hsupportOne hsupportTwo
    (crux.gap_diagonal_ne_value atomA) (crux.gap_diagonal_ne_value atomB)
    (crux.gap_diagonal_ne_value atomC)⟩

/-- The rank-five frame budget of a shared support. -/
theorem RankFiveFrame.shared_support_row_quarter {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {slotOne slotTwo : Fin 5}
    (hslot : slotOne ≠ slotTwo) {atomA atomB atomC : Fin 6}
    (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC) (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport frame.tightDir (frame.basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
      = {atomA, atomB, atomC}) :
    (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomA
        - chartObjective (chartPointOfDesign crux.design))
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design))
          + (chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomC atomC
            - chartObjective (chartPointOfDesign crux.design)))
      ≤ 1 / 4 :=
  crux.shared_block_row_quarter frame.hdata frame.basisLabel frame.leftInv
    frame.hleft hslot (frame.hmemAll slotOne) (frame.hmemAll slotTwo) hAB hAC
    hBC hsupportOne hsupportTwo

/-- The rank-six frame budget of a shared support. -/
theorem RankSixFrame.shared_support_row_quarter {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {slotOne slotTwo : Fin 6}
    (hslot : slotOne ≠ slotTwo) {atomA atomB atomC : Fin 6}
    (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC) (hBC : atomB ≠ atomC)
    (hsupportOne : datumTightSupport frame.tightDir (frame.basisLabel slotOne)
      = {atomA, atomB, atomC})
    (hsupportTwo : datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
      = {atomA, atomB, atomC}) :
    (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomA
        - chartObjective (chartPointOfDesign crux.design))
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design))
          + (chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomC atomC
            - chartObjective (chartPointOfDesign crux.design)))
      ≤ 1 / 4 :=
  crux.shared_block_row_quarter frame.hdata frame.basisLabel frame.leftInv
    frame.hleft hslot (frame.hmemAll slotOne) (frame.hmemAll slotTwo) hAB hAC
    hBC hsupportOne hsupportTwo

end Gtz
