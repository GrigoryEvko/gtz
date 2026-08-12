import Gtz.Wave.CriticalBridge
import Gtz.Wave.FourActivePositiveMultipliers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Finset

/-! **THE SUPPORT-PROFILE COMBINATORIAL KIT.**  A card-four stationary datum
carries one tight support per active block: a subset of the block of size at
least two.  The kit provides the four tools every profile branch of the
leaf-exit dispatch consumes: the quadrichotomy listing the possible supports
of a block, the pair collapse from a single missing atom, the private-atom
coefficient kill inside a three-row cancellation, and the opposite-sign
triangle exit.  Everything downstream is generated case analysis. -/

/-- A subset of a listed triple missing the third atom is the leading pair,
provided it has at least two elements. -/
theorem eq_pair_of_notMem_third {atomA atomB atomC : Fin 6} {support : Finset (Fin 6)}
    (hsubset : support ⊆ {atomA, atomB, atomC}) (hcard : 2 ≤ support.card)
    (hmiss : atomC ∉ support) (hne : atomA ≠ atomB) :
    support = {atomA, atomB} := by
  have hpairSubset : support ⊆ {atomA, atomB} := by
    intro atom hmem
    have hin := hsubset hmem
    simp only [mem_insert, mem_singleton] at hin ⊢
    rcases hin with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hmem hmiss
  refine Finset.eq_of_subset_of_card_le hpairSubset ?_
  rw [Finset.card_pair hne]
  exact hcard

/-- A subset of a listed triple missing the second atom is the outer pair. -/
theorem eq_pair_of_notMem_second {atomA atomB atomC : Fin 6} {support : Finset (Fin 6)}
    (hsubset : support ⊆ {atomA, atomB, atomC}) (hcard : 2 ≤ support.card)
    (hmiss : atomB ∉ support) (hne : atomA ≠ atomC) :
    support = {atomA, atomC} := by
  refine eq_pair_of_notMem_third (atomC := atomB) ?_ hcard hmiss hne
  intro atom hmem
  have hin := hsubset hmem
  simp only [mem_insert, mem_singleton] at hin ⊢
  tauto

/-- A subset of a listed triple missing the first atom is the trailing pair. -/
theorem eq_pair_of_notMem_first {atomA atomB atomC : Fin 6} {support : Finset (Fin 6)}
    (hsubset : support ⊆ {atomA, atomB, atomC}) (hcard : 2 ≤ support.card)
    (hmiss : atomA ∉ support) (hne : atomB ≠ atomC) :
    support = {atomB, atomC} := by
  refine eq_pair_of_notMem_third (atomC := atomA) ?_ hcard hmiss hne
  intro atom hmem
  have hin := hsubset hmem
  simp only [mem_insert, mem_singleton] at hin ⊢
  tauto

/-- **THE SUPPORT QUADRICHOTOMY.**  A subset of a listed triple with at least
two elements is one of the three pairs or the whole triple. -/
theorem support_quadrichotomy {atomA atomB atomC : Fin 6} {support : Finset (Fin 6)}
    (hsubset : support ⊆ {atomA, atomB, atomC}) (hcard : 2 ≤ support.card)
    (hneAB : atomA ≠ atomB) (hneAC : atomA ≠ atomC) (hneBC : atomB ≠ atomC) :
    support = {atomA, atomB} ∨ support = {atomA, atomC} ∨ support = {atomB, atomC}
      ∨ support = {atomA, atomB, atomC} := by
  by_cases hmissC : atomC ∈ support
  · by_cases hmissB : atomB ∈ support
    · by_cases hmissA : atomA ∈ support
      · refine Or.inr (Or.inr (Or.inr (Finset.Subset.antisymm hsubset ?_)))
        intro atom hmem
        simp only [mem_insert, mem_singleton] at hmem
        rcases hmem with rfl | rfl | rfl <;> assumption
      · exact Or.inr (Or.inr (Or.inl
          (eq_pair_of_notMem_first hsubset hcard hmissA hneBC)))
    · exact Or.inr (Or.inl (eq_pair_of_notMem_second hsubset hcard hmissB hneAC))
  · exact Or.inl (eq_pair_of_notMem_third hsubset hcard hmissC hneAB)

/-- **THE PRIVATE-ATOM KILL, FIRST SLOT.**  In a vanishing three-term
combination whose other two terms are dead (zero coefficient or zero row),
a nonzero first row forces a zero first coefficient. -/
theorem firstCoeff_eq_zero_of_sum_three {coeffOne coeffTwo coeffThree : ℝ}
    {rowOne rowTwo rowThree : ℝ}
    (hsum : coeffOne * rowOne + (coeffTwo * rowTwo + coeffThree * rowThree) = 0)
    (hdeadTwo : coeffTwo = 0 ∨ rowTwo = 0) (hdeadThree : coeffThree = 0 ∨ rowThree = 0)
    (hrowOne : rowOne ≠ 0) : coeffOne = 0 := by
  have htermTwo : coeffTwo * rowTwo = 0 := by
    rcases hdeadTwo with hzero | hzero <;> rw [hzero] <;> ring
  have htermThree : coeffThree * rowThree = 0 := by
    rcases hdeadThree with hzero | hzero <;> rw [hzero] <;> ring
  have hprod : coeffOne * rowOne = 0 := by rw [htermTwo, htermThree] at hsum; linarith
  exact (mul_eq_zero.mp hprod).resolve_right hrowOne

/-- **THE PRIVATE-ATOM KILL, SECOND SLOT.** -/
theorem secondCoeff_eq_zero_of_sum_three {coeffOne coeffTwo coeffThree : ℝ}
    {rowOne rowTwo rowThree : ℝ}
    (hsum : coeffOne * rowOne + (coeffTwo * rowTwo + coeffThree * rowThree) = 0)
    (hdeadOne : coeffOne = 0 ∨ rowOne = 0) (hdeadThree : coeffThree = 0 ∨ rowThree = 0)
    (hrowTwo : rowTwo ≠ 0) : coeffTwo = 0 :=
  firstCoeff_eq_zero_of_sum_three (by linarith) hdeadOne hdeadThree hrowTwo

/-- **THE PRIVATE-ATOM KILL, THIRD SLOT.** -/
theorem thirdCoeff_eq_zero_of_sum_three {coeffOne coeffTwo coeffThree : ℝ}
    {rowOne rowTwo rowThree : ℝ}
    (hsum : coeffOne * rowOne + (coeffTwo * rowTwo + coeffThree * rowThree) = 0)
    (hdeadOne : coeffOne = 0 ∨ rowOne = 0) (hdeadTwo : coeffTwo = 0 ∨ rowTwo = 0)
    (hrowThree : rowThree ≠ 0) : coeffThree = 0 :=
  firstCoeff_eq_zero_of_sum_three (by linarith) hdeadOne hdeadTwo hrowThree

/-- **THE OPPOSITE-SIGN TRIANGLE EXIT.**  Three rows meeting pairwise at three
witness atoms with strictly positive values cannot carry a two-term vanishing
combination at each meeting unless all three coefficients vanish: each meeting
forces opposite signs, and the three oppositions form an odd cycle. -/
theorem false_of_oppositeSign_triangle {coeffA coeffB coeffC : ℝ}
    {rowAX rowBX rowBY rowCY rowAZ rowCZ : ℝ}
    (hmeetX : coeffA * rowAX + coeffB * rowBX = 0)
    (hmeetY : coeffB * rowBY + coeffC * rowCY = 0)
    (hmeetZ : coeffA * rowAZ + coeffC * rowCZ = 0)
    (hposAX : 0 < rowAX) (hposBX : 0 < rowBX) (hposBY : 0 < rowBY)
    (hposCY : 0 < rowCY) (hposAZ : 0 < rowAZ) (hposCZ : 0 < rowCZ)
    (hsomeNonzero : coeffA ≠ 0 ∨ coeffB ≠ 0 ∨ coeffC ≠ 0) : False := by
  rcases lt_trichotomy coeffA 0 with hnegA | hzeroA | hposA
  · have hposTermB : 0 < coeffB * rowBX := by nlinarith
    have hposB : 0 < coeffB := by
      rcases mul_pos_iff.mp hposTermB with ⟨hcoeff, _⟩ | ⟨_, hrow⟩
      · exact hcoeff
      · linarith
    have hposTermC : 0 < coeffC * rowCZ := by nlinarith
    have hposC : 0 < coeffC := by
      rcases mul_pos_iff.mp hposTermC with ⟨hcoeff, _⟩ | ⟨_, hrow⟩
      · exact hcoeff
      · linarith
    nlinarith
  · have hzeroB : coeffB = 0 := by
      have hprod : coeffB * rowBX = 0 := by rw [hzeroA] at hmeetX; linarith
      exact (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hposBX)
    have hzeroC : coeffC = 0 := by
      have hprod : coeffC * rowCY = 0 := by rw [hzeroB] at hmeetY; linarith
      exact (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hposCY)
    rcases hsomeNonzero with hne | hne | hne
    · exact hne hzeroA
    · exact hne hzeroB
    · exact hne hzeroC
  · have hnegTermB : coeffB * rowBX < 0 := by nlinarith
    have hnegB : coeffB < 0 := by
      rcases lt_trichotomy coeffB 0 with hlt | hzero | hgt
      · exact hlt
      · rw [hzero] at hnegTermB; linarith
      · nlinarith
    have hnegTermC : coeffC * rowCZ < 0 := by nlinarith
    have hnegC : coeffC < 0 := by
      rcases lt_trichotomy coeffC 0 with hlt | hzero | hgt
      · exact hlt
      · rw [hzero] at hnegTermC; linarith
      · nlinarith
    nlinarith

/-- The total eigen-square row is pointwise nonnegative. -/
theorem totalEigenSquareRow_nonneg {size rank : ℕ}
    (tightVec : Finset (Fin size) → (Fin rank → ℝ)) (selected : Finset (Fin size))
    (atomIndex : Fin size) : 0 ≤ totalEigenSquareRow tightVec selected atomIndex := by
  unfold totalEigenSquareRow
  split
  · unfold eigenSquareRow
    refine Finset.sum_nonneg fun blockIndex _ => ?_
    split
    · positivity
    · exact le_refl 0
  · exact le_refl 0

/-- The total eigen-square row is strictly positive exactly on the tight support. -/
theorem totalEigenSquareRow_pos_of_mem_totalTightSupport {size rank : ℕ}
    (tightVec : Finset (Fin size) → (Fin rank → ℝ)) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) {atomIndex : Fin size}
    (hmem : atomIndex ∈ totalTightSupport tightVec selected) :
    0 < totalEigenSquareRow tightVec selected atomIndex :=
  lt_of_le_of_ne (totalEigenSquareRow_nonneg tightVec selected atomIndex)
    (Ne.symm ((totalEigenSquareRow_ne_zero_iff_mem_totalTightSupport tightVec hcard).mpr hmem))

/-- The total eigen-square row vanishes off the tight support. -/
theorem totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport {size rank : ℕ}
    (tightVec : Finset (Fin size) → (Fin rank → ℝ)) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) {atomIndex : Fin size}
    (hmiss : atomIndex ∉ totalTightSupport tightVec selected) :
    totalEigenSquareRow tightVec selected atomIndex = 0 := by
  by_contra hrow
  exact hmiss ((totalEigenSquareRow_ne_zero_iff_mem_totalTightSupport tightVec hcard).mp hrow)

/-- **COVERAGE.**  With strictly positive multipliers, every atom lies in the
tight support of some active block: the multiplier assembly has constant
diagonal `1/6`, and a totally uncovered atom would read a zero diagonal. -/
theorem SixThreeCrux.exists_mem_totalTightSupport_of_positive_multiplier
    (crux : SixThreeCrux)
    {tightVec : Finset (Fin 6) → (Fin 3 → ℝ)} {multiplier : Finset (Fin 6) → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
      (ambientTightSelection tightVec))
    (atomIndex : Fin 6) :
    ∃ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      atomIndex ∈ totalTightSupport tightVec selected := by
  classical
  by_contra hnone
  push Not at hnone
  have hrowEq : ∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      ∀ atom : Fin 6,
        totalEigenSquareRow tightVec selected atom
          = ambientTightSelection tightVec selected atom
              * ambientTightSelection tightVec selected atom := by
    intro selected hmember atom
    have hcard : selected.card = 3 :=
      ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmember).1
    have hrestriction : tightVec selected = fun blockIndex =>
        ambientTightSelection tightVec selected (selected.orderEmbOfFin hcard blockIndex) := by
      funext blockIndex
      rw [ambientTightSelection, dif_pos hcard,
        selectionInjection_mulVec_apply (selected.orderEmbOfFin hcard).injective]
    rw [totalEigenSquareRow_of_card tightVec hcard, hrestriction]
    exact eigenSquareRow_eq_mul_self_of_support hcard
      (ambientTightSelection tightVec selected)
      (hdata.tightDir_support selected hmember) atom
  have hassembly := assemblyDiagonal_of_isChartStationaryData_of_rowEq hdata
    (totalEigenSquareRow tightVec) hrowEq atomIndex
  have hvanish : ∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      multiplier selected * totalEigenSquareRow tightVec selected atomIndex = 0 := by
    intro selected hmember
    have hcard : selected.card = 3 :=
      ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmember).1
    rw [totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec hcard
      (hnone selected hmember), mul_zero]
  rw [Finset.sum_eq_zero hvanish] at hassembly
  norm_num at hassembly

end Gtz
