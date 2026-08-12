import Gtz.Wave.CriticalBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The residual-row cancellation, freed from the four-count

The rung-four kills consume
`Gtz.exists_nontrivial_threeRow_cancellation_off_pair`, whose four-count
hypothesis feeds EXACTLY ONE clause of its conclusion: the erased family has
three members.  The cancellation itself — a nontrivial combination of the
residual rows supported on the selected pair — never reads the count.  This
file restates the engine at every active count and rebuilds the two bridge
forms of `Gtz.Wave.CriticalBridge` on top of it.

This is the working interface of the rank-four generalization: a support-two
block inside ANY active family, with the second-order row-span witness at its
pair, yields a nontrivial residual cancellation.  The count arithmetic that
the fifteen family kills perform afterwards is where the per-pattern work
begins, and it is not attempted here.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.exists_nontrivial_residualRow_cancellation_off_pair` — the engine, at
  every active count.
* `Gtz.exists_residualRow_cancellation_of_mem_finiteRowSpan` — the row-span
  bridge, at every active count.
* `Gtz.exists_residualEigenSquareRow_cancellation_of_support_pair` — the
  fully instantiated eigen-square form the kills consume, at every family.

## Vacuity

Nothing here quantifies over a crux.  The statements hold at every finite
family of rows with the stated support data.
-/

namespace Gtz

open Matrix Finset

/-- **THE RESIDUAL CANCELLATION, EVERY COUNT.**  If a coordinate axis lies in
the span of the active rows and one active row is genuinely supported on a
pair containing that coordinate, then the OTHER active rows admit a nontrivial
linear combination that vanishes outside the pair.  The four-count of
`Gtz.exists_nontrivial_threeRow_cancellation_off_pair` fed only the erased
cardinality clause, and this statement drops it. -/
theorem exists_nontrivial_residualRow_cancellation_off_pair
    {activeIndex : Type*} [DecidableEq activeIndex]
    {size : ℕ} (activeSet : Finset activeIndex)
    (row : activeIndex → (Fin size → ℝ))
    {selected : activeIndex} (hselected : selected ∈ activeSet)
    {pairFirst pairSecond : Fin size} (hpairDistinct : pairFirst ≠ pairSecond)
    (hselectedSecond : row selected pairSecond ≠ 0)
    (hselectedSupport : ∀ atomIndex,
      atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)) →
        row selected atomIndex = 0)
    (hcoordinate : ∃ coefficient : activeIndex → ℝ,
      ∑ activeLabel ∈ activeSet, coefficient activeLabel • row activeLabel
        = Pi.single pairFirst (1 : ℝ)) :
    ∃ coefficient : activeIndex → ℝ,
      (∃ activeLabel ∈ activeSet.erase selected, coefficient activeLabel ≠ 0)
        ∧ (∑ activeLabel ∈ activeSet.erase selected,
            coefficient activeLabel • row activeLabel) ≠ 0
        ∧ ∀ atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)),
          ∑ activeLabel ∈ activeSet.erase selected,
            coefficient activeLabel * row activeLabel atomIndex = 0 := by
  classical
  obtain ⟨coefficient, hcoordinate⟩ := hcoordinate
  have heraseCombinationNonzero :
      (∑ activeLabel ∈ activeSet.erase selected,
        coefficient activeLabel • row activeLabel) ≠ 0 := by
    intro heraseZero
    have hsplit := Finset.sum_erase_add activeSet
      (fun activeLabel ↦ coefficient activeLabel • row activeLabel) hselected
    rw [heraseZero, zero_add] at hsplit
    have honlySelected : coefficient selected • row selected
        = Pi.single pairFirst (1 : ℝ) := hsplit.trans hcoordinate
    have hsecondEntry := congrFun honlySelected pairSecond
    simp only [Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne hpairDistinct.symm] at hsecondEntry
    have hcoefficientZero : coefficient selected = 0 :=
      (mul_eq_zero.mp hsecondEntry).resolve_right hselectedSecond
    have hfirstEntry := congrFun honlySelected pairFirst
    simp [hcoefficientZero] at hfirstEntry
  refine ⟨coefficient, ?_, heraseCombinationNonzero, ?_⟩
  · by_contra hnone
    push Not at hnone
    have heraseZero :
        ∑ activeLabel ∈ activeSet.erase selected,
          coefficient activeLabel • row activeLabel = 0 := by
      apply Finset.sum_eq_zero
      intro activeLabel hactive
      rw [hnone activeLabel hactive, zero_smul]
    exact heraseCombinationNonzero heraseZero
  · intro atomIndex hnotPair
    have hfirstNe : atomIndex ≠ pairFirst := by
      intro heq
      apply hnotPair
      simp [heq]
    have hentry := congrFun hcoordinate atomIndex
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne hfirstNe] at hentry
    have hsplit := Finset.sum_erase_add activeSet
      (fun activeLabel ↦ coefficient activeLabel * row activeLabel atomIndex) hselected
    rw [hselectedSupport atomIndex hnotPair, mul_zero, add_zero] at hsplit
    exact hsplit.trans hentry

/-- The row-span bridge at every count: membership of the pair axis in the
finite row span yields the residual cancellation. -/
theorem exists_residualRow_cancellation_of_mem_finiteRowSpan
    {size : ℕ} {family : Finset (Finset (Fin size))}
    (row : Finset (Fin size) → (Fin size → ℝ))
    {selected : Finset (Fin size)} (hselected : selected ∈ family)
    {pairFirst pairSecond : Fin size} (hpairDistinct : pairFirst ≠ pairSecond)
    (hselectedSecond : row selected pairSecond ≠ 0)
    (hselectedSupport : ∀ atomIndex,
      atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)) →
        row selected atomIndex = 0)
    (hcoordinate : Pi.single pairFirst (1 : ℝ) ∈ finiteRowSpan family row) :
    ∃ coefficient : Finset (Fin size) → ℝ,
      (∃ activeBlock ∈ family.erase selected, coefficient activeBlock ≠ 0)
        ∧ (∑ activeBlock ∈ family.erase selected,
            coefficient activeBlock • row activeBlock) ≠ 0
        ∧ ∀ atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)),
          ∑ activeBlock ∈ family.erase selected,
            coefficient activeBlock * row activeBlock atomIndex = 0 := by
  classical
  obtain ⟨coefficient, hcombination⟩ :=
    exists_family_linearCombination_eq_of_mem_finiteRowSpan hcoordinate
  exact exists_nontrivial_residualRow_cancellation_off_pair family row hselected
    hpairDistinct hselectedSecond hselectedSupport ⟨coefficient, hcombination⟩

/-- **THE INSTANTIATED FORM, EVERY FAMILY.**  A support-two block inside any
family of card-three blocks, with the second-order row-span witness at its
pair, yields a nontrivial residual cancellation of the eigen-square rows. -/
theorem exists_residualEigenSquareRow_cancellation_of_support_pair
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    {family : Finset (Finset (Fin 6))}
    {selected : Finset (Fin 6)} (hselected : selected ∈ family)
    (hselectedCard : selected.card = 3)
    {pairFirst pairSecond : Fin 6} (hpairDistinct : pairFirst ≠ pairSecond)
    (hsupport : totalTightSupport tightVec selected
      = ({pairFirst, pairSecond} : Finset (Fin 6)))
    (hcoordinate : Pi.single pairFirst (1 : ℝ) ∈
      finiteRowSpan family (totalEigenSquareRow tightVec)) :
    ∃ coefficient : Finset (Fin 6) → ℝ,
      (∃ activeBlock ∈ family.erase selected, coefficient activeBlock ≠ 0)
        ∧ (∑ activeBlock ∈ family.erase selected,
            coefficient activeBlock • totalEigenSquareRow tightVec activeBlock) ≠ 0
        ∧ ∀ atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin 6)),
          ∑ activeBlock ∈ family.erase selected,
            coefficient activeBlock
              * totalEigenSquareRow tightVec activeBlock atomIndex = 0 := by
  have hsecondMem : pairSecond ∈ totalTightSupport tightVec selected := by
    rw [hsupport]
    simp
  have hsecondRow : totalEigenSquareRow tightVec selected pairSecond ≠ 0 :=
    (totalEigenSquareRow_ne_zero_iff_mem_totalTightSupport tightVec hselectedCard).mpr
      hsecondMem
  have hrowSupport : ∀ atomIndex,
      atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin 6)) →
        totalEigenSquareRow tightVec selected atomIndex = 0 := by
    intro atomIndex hnotPair
    by_contra hrow
    have hmem :=
      (totalEigenSquareRow_ne_zero_iff_mem_totalTightSupport tightVec hselectedCard).mp hrow
    rw [hsupport] at hmem
    exact hnotPair hmem
  exact exists_residualRow_cancellation_of_mem_finiteRowSpan
    (totalEigenSquareRow tightVec) hselected hpairDistinct hsecondRow
    hrowSupport hcoordinate

end Gtz
