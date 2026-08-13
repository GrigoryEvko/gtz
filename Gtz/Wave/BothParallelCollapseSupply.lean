import Gtz.Wave.BothParallelDiagonalCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The both-parallel collapse supply — the row-square masses of the core

The diagonal-core branch of closure five prices the two single-atom gap
rows.  This module proves the two collapse identities: each off-diagonal
row-square mass equals a polynomial in the two shifted gap diagonals.
The module also supplies the frame readers and the two inequality steps
that the Schur finale consumes.

The collapse chain, in the even language of the squared coordinates:

1. Each carrier row at a single atom collapses to one product law, and
   the squares of the four cross entries follow.
2. The paired eigen rows give the two scale balances between the
   shifted diagonals and the squared coordinates.
3. The diagonal reads of the effective core give four two-term reads.
   The read differences eliminate the multipliers.
4. The eliminations, the norms, and the two balances prove the two
   collapse identities.  The degenerate third-mass case closes through
   the balances alone.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.pair_row_gap_collapse` — the carrier row product law.
* `Gtz.carrier_row_difference` — the paired-row difference law.
* `Gtz.bothParallel_scale_balance` — the scale balance.
* `Gtz.four_slot_diag_read` — the two-term diagonal read.
* `Gtz.collapse_core_b`, `Gtz.collapse_core_d` — **THE COLLAPSES**, in
  the pure even language.
* `Gtz.six_atom_offdiag_budget` — the row-square budget.
* `Gtz.six_atom_trace_read` — the trace read.
* `Gtz.triple_schur_step` — the per-triple Schur consequence.
* `Gtz.schur_sum_nonneg` — **THE FINAL INEQUALITY.**

## Vacuity

Nothing here quantifies over a crux.  The even-language lemmas hold for
all real numbers with the stated equations.  The frame readers hold at
each stationary datum with the stated pattern hypotheses.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the carrier row product law -/

/-- **THE ROW PRODUCT LAW.**  The eigen row of a carrier at its single
atom, the pair ratio, and the equal pair squares collapse the row to one
product: the pair mass prices the shifted diagonal. -/
theorem pair_row_gap_collapse
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomOne atomTwo atomRow : Fin size}
    (h12 : atomOne ≠ atomTwo) (h1R : atomOne ≠ atomRow) (h2R : atomTwo ≠ atomRow)
    (hrow : atomRow ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      atomIndex ≠ atomRow → tightDir label atomIndex = 0)
    (hone : tightDir label atomOne ≠ 0)
    (hsq : tightDir label atomOne ^ 2 = tightDir label atomTwo ^ 2)
    (hratio : chartStationaryGap projection weight atomRow atomOne
        * tightDir label atomTwo
      = chartStationaryGap projection weight atomRow atomTwo
        * tightDir label atomOne) :
    2 * tightDir label atomOne
        * chartStationaryGap projection weight atomRow atomOne
      = (value - chartStationaryGap projection weight atomRow atomRow)
        * tightDir label atomRow := by
  have hrowEq := gap_row_eigen_triple hdata hmem hrow h12 h1R h2R hsupp
  have hcancel : (2 * tightDir label atomOne
        * chartStationaryGap projection weight atomRow atomOne
      - (value - chartStationaryGap projection weight atomRow atomRow)
        * tightDir label atomRow) * tightDir label atomOne = 0 := by
    linear_combination tightDir label atomOne * hrowEq
      + chartStationaryGap projection weight atomRow atomOne * hsq
      + tightDir label atomTwo * hratio
  rcases mul_eq_zero.mp hcancel with hcase | hcase
  · linarith [hcase]
  · exact absurd hcase hone

/-- **THE PAIRED-ROW DIFFERENCE.**  Two eigen rows at one shared pair
atom, with the parallel determinant, price the two anchor entries
against each other. -/
theorem carrier_row_difference
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {labelA labelB : activeIndex}
    (hmemA : labelA ∈ activeSet) (hmemB : labelB ∈ activeSet)
    {atomOne atomTwo atomAnchorA atomAnchorB : Fin size}
    (h12 : atomOne ≠ atomTwo) (h1A : atomOne ≠ atomAnchorA)
    (h2A : atomTwo ≠ atomAnchorA) (h1B : atomOne ≠ atomAnchorB)
    (h2B : atomTwo ≠ atomAnchorB)
    (hrowA : atomOne ∈ activeSubset labelA) (hrowB : atomOne ∈ activeSubset labelB)
    (hsuppA : ∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      atomIndex ≠ atomAnchorA → tightDir labelA atomIndex = 0)
    (hsuppB : ∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      atomIndex ≠ atomAnchorB → tightDir labelB atomIndex = 0)
    (hdet : tightDir labelA atomOne * tightDir labelB atomTwo
      - tightDir labelA atomTwo * tightDir labelB atomOne = 0) :
    chartStationaryGap projection weight atomOne atomAnchorA
        * tightDir labelA atomAnchorA * tightDir labelB atomOne
      = chartStationaryGap projection weight atomOne atomAnchorB
        * tightDir labelB atomAnchorB * tightDir labelA atomOne := by
  have hrowEqA := gap_row_eigen_triple hdata hmemA hrowA h12 h1A h2A hsuppA
  have hrowEqB := gap_row_eigen_triple hdata hmemB hrowB h12 h1B h2B hsuppB
  linear_combination tightDir labelB atomOne * hrowEqA
    - tightDir labelA atomOne * hrowEqB
    + chartStationaryGap projection weight atomOne atomTwo * hdet

/-- **THE SCALE BALANCE.**  The two row product laws at the two single
atoms, the paired-row difference, and the gap symmetry balance the two
shifted diagonals against the squared coordinates. -/
theorem bothParallel_scale_balance
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {labelA labelB : activeIndex}
    (hmemA : labelA ∈ activeSet) (hmemB : labelB ∈ activeSet)
    {atomOne atomTwo atomD atomB : Fin size}
    (h12 : atomOne ≠ atomTwo) (h1D : atomOne ≠ atomD) (h2D : atomTwo ≠ atomD)
    (h1B : atomOne ≠ atomB) (h2B : atomTwo ≠ atomB)
    (hrowA : atomOne ∈ activeSubset labelA) (hrowAD : atomD ∈ activeSubset labelA)
    (hrowB : atomOne ∈ activeSubset labelB) (hrowBB : atomB ∈ activeSubset labelB)
    (hsuppA : ∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      atomIndex ≠ atomD → tightDir labelA atomIndex = 0)
    (hsuppB : ∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      atomIndex ≠ atomB → tightDir labelB atomIndex = 0)
    (hdet : tightDir labelA atomOne * tightDir labelB atomTwo
      - tightDir labelA atomTwo * tightDir labelB atomOne = 0)
    (honeA : tightDir labelA atomOne ≠ 0) (honeB : tightDir labelB atomOne ≠ 0)
    (hsqA : tightDir labelA atomOne ^ 2 = tightDir labelA atomTwo ^ 2)
    (hsqB : tightDir labelB atomOne ^ 2 = tightDir labelB atomTwo ^ 2)
    (hratioA : chartStationaryGap projection weight atomD atomOne
        * tightDir labelA atomTwo
      = chartStationaryGap projection weight atomD atomTwo
        * tightDir labelA atomOne)
    (hratioB : chartStationaryGap projection weight atomB atomOne
        * tightDir labelB atomTwo
      = chartStationaryGap projection weight atomB atomTwo
        * tightDir labelB atomOne) :
    (chartStationaryGap projection weight atomD atomD - value)
        * tightDir labelA atomD ^ 2 * tightDir labelB atomOne ^ 2
      = (chartStationaryGap projection weight atomB atomB - value)
        * tightDir labelB atomB ^ 2 * tightDir labelA atomOne ^ 2 := by
  have hcollA := pair_row_gap_collapse hdata hmemA h12 h1D h2D hrowAD
    hsuppA honeA hsqA hratioA
  have hcollB := pair_row_gap_collapse hdata hmemB h12 h1B h2B hrowBB
    hsuppB honeB hsqB hratioB
  have hdiff := carrier_row_difference hdata hmemA hmemB h12 h1D h2D h1B h2B
    hrowA hrowB hsuppA hsuppB hdet
  have hsymmD := gap_entry_symm hdata atomOne atomD
  have hsymmB := gap_entry_symm hdata atomOne atomB
  linear_combination
    tightDir labelA atomD * tightDir labelB atomOne ^ 2 * hcollA
      - tightDir labelB atomB * tightDir labelA atomOne ^ 2 * hcollB
      - 2 * tightDir labelA atomOne * tightDir labelB atomOne * hdiff
      + 2 * tightDir labelA atomOne * tightDir labelB atomOne
        * tightDir labelA atomD * tightDir labelB atomOne * hsymmD
      - 2 * tightDir labelA atomOne * tightDir labelB atomOne
        * tightDir labelB atomB * tightDir labelA atomOne * hsymmB

/-! ## Layer 2 — the two-term diagonal read -/

/-- **THE TWO-TERM READ.**  The effective diagonal read collapses to the
two slots that survive at the atom. -/
theorem four_slot_diag_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {leftInv : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (hmemPos : ∀ slot, basisLabel slot
      ∈ positiveActiveSet activeSet activeWeight)
    (hparallel : ∀ label ∈ positiveActiveSet activeSet activeWeight,
      ∃ (slot : Fin basisCount) (scal : ℝ),
        tightDir label = scal • tightDir (basisLabel slot))
    {slotOne slotTwo : Fin basisCount} (hne : slotOne ≠ slotTwo)
    {atomIndex : Fin size}
    (hvanish : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      tightDir (basisLabel slot) atomIndex = 0) :
    effectiveMultiplier activeSet activeWeight tightDir basisLabel slotOne
        * tightDir (basisLabel slotOne) atomIndex ^ 2
      + effectiveMultiplier activeSet activeWeight tightDir basisLabel slotTwo
        * tightDir (basisLabel slotTwo) atomIndex ^ 2
      = ((size : ℝ))⁻¹ := by
  have hread := effective_diagonal_read hdata basisLabel hleft hmemPos
    hparallel atomIndex
  have hnotOne : slotOne ∉ ({slotTwo} : Finset (Fin basisCount)) := fun hmem =>
    hne (Finset.mem_singleton.mp hmem)
  have hrestrict : ∑ slot, effectiveMultiplier activeSet activeWeight tightDir
        basisLabel slot * tightDir (basisLabel slot) atomIndex ^ 2
      = ∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin basisCount)),
          effectiveMultiplier activeSet activeWeight tightDir basisLabel slot
            * tightDir (basisLabel slot) atomIndex ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro slot _ hnot
    have hcases : slot ≠ slotOne ∧ slot ≠ slotTwo := by
      constructor
      · intro heq
        exact hnot (heq ▸ Finset.mem_insert_self _ _)
      · intro heq
        exact hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [hvanish slot hcases.1 hcases.2]
    ring
  rw [← hread, hrestrict, Finset.sum_insert hnotOne, Finset.sum_singleton]

/-! ## Layer 3 — the collapse identities, even language -/

/-- **THE B-COLLAPSE CORE.**  The even-language identity behind the
b-row square mass.  The read eliminations, the norms, and the two
balances force the collapse.  The degenerate third-mass case closes
through the balances alone. -/
theorem collapse_core_b
    {x X W B y C V Y m n nuA nuB nuC nuD : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hm : 0 < m) (hn : 0 < n)
    (hN1 : 2 * x + X = 1) (hN2 : 2 * W + B = 1)
    (hN3 : 2 * y + C = 1) (hN4 : 2 * V + Y = 1)
    (hS4 : n * X * W = m * B * x) (hS5 : n * Y * y = m * C * V)
    (hD1 : nuA * x + nuB * W = 1 / 6) (hD2 : nuB * B + nuC * C = 1 / 6)
    (hD3 : nuC * y + nuD * V = 1 / 6) (hD4 : nuA * X + nuD * Y = 1 / 6) :
    m * B * y + m * C * W = (m + n) * W * y := by
  have hX : X = 1 - 2 * x := by linarith
  have hB : B = 1 - 2 * W := by linarith
  have hC : C = 1 - 2 * y := by linarith
  have hY : Y = 1 - 2 * V := by linarith
  subst hX hB hC hY
  have hK1 : nuD * (1 - 2 * V) * x - nuB * W * (1 - 2 * x)
      + ((1 - 2 * x) - x) / 6 = 0 := by
    linear_combination x * hD4 - (1 - 2 * x) * hD1
  have hK2 : nuB * (1 - 2 * W) * y - nuD * V * (1 - 2 * y)
      - (y - (1 - 2 * y)) / 6 = 0 := by
    linear_combination y * hD2 - (1 - 2 * y) * hD3
  have hRKEY : m * x * (1 - 3 * y) - n * y * (3 * x - 1) = 0 := by
    linear_combination 6 * n * y * hK1 + 6 * m * x * hK2
      - 6 * nuD * x * hS5 + 6 * nuB * y * hS4
  by_cases hdeg : 3 * x - 1 = 0
  · -- The degenerate third-mass case.
    have hy3 : 1 - 3 * y = 0 := by
      have hprod : m * x * (1 - 3 * y) = 0 := by
        linear_combination hRKEY + n * y * hdeg
      rcases mul_eq_zero.mp hprod with hcase | hcase
      · rcases mul_eq_zero.mp hcase with hcase' | hcase'
        · exact absurd hcase' (ne_of_gt hm)
        · exact absurd hcase' hx
      · exact hcase
    have hBW : n * W = m * (1 - 2 * W) := by
      have hcancel : x * (n * W - m * (1 - 2 * W)) = 0 := by
        linear_combination hS4 + n * W * hdeg
      rcases mul_eq_zero.mp hcancel with hcase | hcase
      · exact absurd hcase hx
      · linarith [hcase]
    linear_combination m * W * hy3 - y * hBW
  · -- The generic case: the collapse is the normed null combination.
    have hBRANCH : (1 - 2 * W) * (1 - 2 * V) * x * y
        - W * V * (1 - 2 * x) * (1 - 2 * y) = 0 := by
      have hprod : n * ((1 - 2 * W) * (1 - 2 * V) * x * y
          - W * V * (1 - 2 * x) * (1 - 2 * y)) = 0 := by
        linear_combination (1 - 2 * W) * x * hS5 - V * (1 - 2 * y) * hS4
      rcases mul_eq_zero.mp hprod with hcase | hcase
      · exact absurd hcase (ne_of_gt hn)
      · exact hcase
    have hCON1 : 12 * W * x * y - 2 * W * x - 5 * W * y + W - 3 * x * y + y
        = 0 := by
      linear_combination (-6 * ((1 - 2 * x) * (1 - 2 * W) * y)) * hD1
        + 6 * W * (1 - 2 * x) * y * hD2
        - 6 * W * (1 - 2 * y) * (1 - 2 * x) * hD3
        + 6 * x * (1 - 2 * W) * y * hD4
        - 6 * nuD * hBRANCH
    have hcore : (3 * x - 1)
        * (m * y + m * W - 5 * m * W * y - n * W * y) = 0 := by
      linear_combination W * hRKEY - m * hCON1
    rcases mul_eq_zero.mp hcore with hcase | hcase
    · exact absurd hcase hdeg
    · linarith [hcase]

/-- **THE D-COLLAPSE CORE.**  The mirror identity for the d-row square
mass.  The fifth read elimination is the collapse itself. -/
theorem collapse_core_d
    {x X W B y C V Y m n nuA nuB nuC nuD : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hm : 0 < m) (hn : 0 < n)
    (hN1 : 2 * x + X = 1) (hN2 : 2 * W + B = 1)
    (hN3 : 2 * y + C = 1) (hN4 : 2 * V + Y = 1)
    (hS4 : n * X * W = m * B * x) (hS5 : n * Y * y = m * C * V)
    (hD1 : nuA * x + nuB * W = 1 / 6) (hD2 : nuB * B + nuC * C = 1 / 6)
    (hD3 : nuC * y + nuD * V = 1 / 6) (hD4 : nuA * X + nuD * Y = 1 / 6) :
    n * X * V + n * Y * x = (m + n) * x * V := by
  have hX : X = 1 - 2 * x := by linarith
  have hB : B = 1 - 2 * W := by linarith
  have hC : C = 1 - 2 * y := by linarith
  have hY : Y = 1 - 2 * V := by linarith
  subst hX hB hC hY
  have hK1 : nuD * (1 - 2 * V) * x - nuB * W * (1 - 2 * x)
      + ((1 - 2 * x) - x) / 6 = 0 := by
    linear_combination x * hD4 - (1 - 2 * x) * hD1
  have hK2 : nuB * (1 - 2 * W) * y - nuD * V * (1 - 2 * y)
      - (y - (1 - 2 * y)) / 6 = 0 := by
    linear_combination y * hD2 - (1 - 2 * y) * hD3
  have hRKEY : m * x * (1 - 3 * y) - n * y * (3 * x - 1) = 0 := by
    linear_combination 6 * n * y * hK1 + 6 * m * x * hK2
      - 6 * nuD * x * hS5 + 6 * nuB * y * hS4
  by_cases hdeg : 1 - 3 * y = 0
  · -- The degenerate third-mass case.
    have hx3 : 3 * x - 1 = 0 := by
      have hprod : n * y * (3 * x - 1) = 0 := by
        linear_combination (-1) * hRKEY + m * x * hdeg
      rcases mul_eq_zero.mp hprod with hcase | hcase
      · rcases mul_eq_zero.mp hcase with hcase' | hcase'
        · exact absurd hcase' (ne_of_gt hn)
        · exact absurd hcase' hy
      · exact hcase
    have hYV : n * (1 - 2 * V) = m * V := by
      have hcancel : y * (n * (1 - 2 * V) - m * V) = 0 := by
        linear_combination hS5 + m * V * hdeg
      rcases mul_eq_zero.mp hcancel with hcase | hcase
      · exact absurd hcase hy
      · linarith [hcase]
    linear_combination x * hYV - n * V * hx3
  · -- The generic case: the fifth read elimination is the collapse.
    have hBRANCH : (1 - 2 * W) * (1 - 2 * V) * x * y
        - W * V * (1 - 2 * x) * (1 - 2 * y) = 0 := by
      have hprod : n * ((1 - 2 * W) * (1 - 2 * V) * x * y
          - W * V * (1 - 2 * x) * (1 - 2 * y)) = 0 := by
        linear_combination (1 - 2 * W) * x * hS5 - V * (1 - 2 * y) * hS4
      rcases mul_eq_zero.mp hprod with hcase | hcase
      · exact absurd hcase (ne_of_gt hn)
      · exact hcase
    have hRKEY5 : V * (1 - 2 * y) * (1 - 3 * x)
        - (1 - 2 * V) * x * (3 * y - 1) = 0 := by
      linear_combination 6 * V * (1 - 2 * y) * hK1 + 6 * (1 - 2 * V) * x * hK2
        - 6 * nuB * hBRANCH
    have hcore : (1 - 3 * y)
        * (n * V + n * x - 5 * n * x * V - m * x * V) = 0 := by
      linear_combination (-V) * hRKEY + n * hRKEY5
    rcases mul_eq_zero.mp hcore with hcase | hcase
    · exact absurd hcase hdeg
    · linarith [hcase]

/-! ## Layer 4 — the budget, the trace, and the Schur steps -/

/-- **THE ROW-SQUARE BUDGET.**  The off-diagonal square mass of a
projection row is at most one quarter. -/
theorem six_atom_offdiag_budget
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (atomRow : Fin size) :
    ∑ atomCol ∈ Finset.univ.erase atomRow,
        projection atomRow atomCol * projection atomRow atomCol
      ≤ 1 / 4 := by
  have hsquare := projection_offdiag_square hdata atomRow
  nlinarith [sq_nonneg (projection atomRow atomRow - 1 / 2)]

/-- **THE TRACE READ.**  The gap diagonal sums to the rank minus one. -/
theorem six_atom_trace_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ∑ atomIndex : Fin size,
        chartStationaryGap projection weight atomIndex atomIndex
      = (rank : ℝ) - 1 := by
  have htrace := hdata.hasTraceRank
  have hweight := hdata.weight_sum_one
  calc ∑ atomIndex : Fin size,
        chartStationaryGap projection weight atomIndex atomIndex
      = ∑ atomIndex : Fin size,
          (projection atomIndex atomIndex - weight atomIndex) := by
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        simp [chartStationaryGap]
    _ = (∑ atomIndex : Fin size, projection atomIndex atomIndex)
        - ∑ atomIndex : Fin size, weight atomIndex := by
        rw [Finset.sum_sub_distrib]
    _ = (rank : ℝ) - 1 := by rw [hweight, ← htrace]; rfl

/-- **THE SCHUR STEP.**  A strictly negative witness of the shifted
triple form with a vanished cross entry forces the determinant test. -/
theorem triple_schur_step
    {gbb gdd gxx gbx gdx sigma a b c : ℝ}
    (hM : 0 < gbb - sigma) (hN : 0 < gdd - sigma)
    (hwitness : a * ((gbb - sigma) * a + gbx * c)
        + b * ((gdd - sigma) * b + gdx * c)
        + c * (gbx * a + gdx * b + (gxx - sigma) * c) < 0) :
    (gxx - sigma) * ((gbb - sigma) * (gdd - sigma))
      < (gdd - sigma) * gbx ^ 2 + (gbb - sigma) * gdx ^ 2 := by
  by_contra hcontra
  push_neg at hcontra
  have hkey : 0 ≤ (gxx - sigma) * ((gbb - sigma) * (gdd - sigma))
      - (gdd - sigma) * gbx ^ 2 - (gbb - sigma) * gdx ^ 2 := by linarith
  have hscaled := mul_lt_mul_of_pos_left hwitness (mul_pos hM hN)
  rw [mul_zero] at hscaled
  nlinarith [mul_nonneg hN.le (sq_nonneg ((gbb - sigma) * a + gbx * c)),
    mul_nonneg hM.le (sq_nonneg ((gdd - sigma) * b + gdx * c)),
    mul_nonneg hkey (sq_nonneg c), hscaled]

set_option maxHeartbeats 1600000 in
/-- **THE FINAL INEQUALITY.**  The summed determinant tests, the two
collapses, and the two budgets refuse a negative value on the whole
constraint region. -/
theorem schur_sum_nonneg
    {m n eta : ℝ} (heta : 0 < eta) (hm : 2 * eta ≤ m) (hn : 2 * eta ≤ n)
    (hbm : m * (m + n) ≤ 1 / 2) (hbn : n * (m + n) ≤ 1 / 2) :
    m * n * (m + n) - eta * (m + n) ^ 2 / 2
      ≤ (2 - m - n + 8 * eta) * (m - eta) * (n - eta) := by
  have hmpos : 0 < m := lt_of_lt_of_le (by linarith) hm
  have hnpos : 0 < n := lt_of_lt_of_le (by linarith) hn
  have hsum : (m + n) ^ 2 ≤ 1 := by nlinarith [hbm, hbn]
  have hple : m + n ≤ 1 := by nlinarith [hsum, sq_nonneg (m + n - 1)]
  have hmn : eta * (m + n) ≤ m * n := by nlinarith
  have hs1 : (0:ℝ) ≤ 1 - (m + n) := by linarith
  have hm' : (0:ℝ) ≤ m - 2 * eta := by linarith
  have hn' : (0:ℝ) ≤ n - 2 * eta := by linarith
  have hbm' : (0:ℝ) ≤ 1 / 2 - m * (m + n) := by linarith
  have hbn' : (0:ℝ) ≤ 1 / 2 - n * (m + n) := by linarith
  nlinarith [mul_nonneg (mul_nonneg hmpos.le hnpos.le) hs1,
    mul_nonneg (mul_nonneg heta.le hm') hnpos.le,
    mul_nonneg (mul_nonneg heta.le hn') hmpos.le,
    mul_nonneg (mul_nonneg heta.le heta.le) heta.le,
    mul_nonneg (mul_nonneg heta.le heta.le) hs1,
    mul_nonneg heta.le (sq_nonneg (m - n)),
    mul_nonneg heta.le hbm', mul_nonneg heta.le hbn',
    mul_nonneg hm' hbn', mul_nonneg hn' hbm']

end Gtz
