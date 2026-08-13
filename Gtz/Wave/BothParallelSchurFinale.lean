import Gtz.Wave.BothParallelEffectiveEntries
import Gtz.Wave.AmbientCeilingToolbox

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The both-parallel Schur finale — the four-triple ceiling contradiction

The diagonal-core branch of closure five ends in one inequality chain.
This module assembles it: the per-triple margin dichotomy, the four
summed determinant tests, the trace read, the two collapse masses, the
two budgets, and the final refusal.

The chain, at the six-atom C4 pattern with a vanished cross entry:

1. Each triple over the two single atoms and one double atom either
   dominates the chart objective with margin half the value, or its
   shifted form has a strict witness.  A dominating triple kills the
   crux through the landed ceiling interface.
2. A witness forces the determinant test of the shifted triple.
3. The four tests sum.  The trace read prices the diagonal sum, the
   collapse masses price the two off-row squares, and the budgets cap
   them.  The landed final inequality refuses the sum.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.six_sum_univ_eq`, `Gtz.six_sum_erase_eq` — the six-atom sums.
* `Gtz.SixThreeCrux.schur_test_of_cross_zero` — **THE PER-TRIPLE TEST.**
* `Gtz.SixThreeCrux.false_of_bothParallel_finale` — **THE FINALE.**

## Vacuity

The crux statements are vacuous if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the six-atom sum enumerations -/

/-- A sum over `Fin 6` collapses to six named distinct atoms. -/
theorem six_sum_univ_eq {f : Fin 6 → ℝ}
    {atomA1 atomA2 atomB atomC1 atomC2 atomD : Fin 6}
    (hA12 : atomA1 ≠ atomA2) (hA1B : atomA1 ≠ atomB) (hA1C1 : atomA1 ≠ atomC1)
    (hA1C2 : atomA1 ≠ atomC2) (hA1D : atomA1 ≠ atomD)
    (hA2B : atomA2 ≠ atomB) (hA2C1 : atomA2 ≠ atomC1)
    (hA2C2 : atomA2 ≠ atomC2) (hA2D : atomA2 ≠ atomD)
    (hBC1 : atomB ≠ atomC1) (hBC2 : atomB ≠ atomC2) (hBD : atomB ≠ atomD)
    (hC12 : atomC1 ≠ atomC2) (hC1D : atomC1 ≠ atomD) (hC2D : atomC2 ≠ atomD) :
    ∑ atomIndex : Fin 6, f atomIndex
      = f atomA1 + f atomA2 + f atomB + f atomC1 + f atomC2 + f atomD := by
  have hset : (Finset.univ : Finset (Fin 6))
      = {atomA1, atomA2, atomB, atomC1, atomC2, atomD} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem (by
        simp [hA12, hA1B, hA1C1, hA1C2, hA1D]),
      Finset.card_insert_of_notMem (by simp [hA2B, hA2C1, hA2C2, hA2D]),
      Finset.card_insert_of_notMem (by simp [hBC1, hBC2, hBD]),
      Finset.card_insert_of_notMem (by simp [hC12, hC1D]),
      Finset.card_insert_of_notMem (by simp [hC2D]), Finset.card_singleton]
  rw [hset, Finset.sum_insert (by simp [hA12, hA1B, hA1C1, hA1C2, hA1D]),
    Finset.sum_insert (by simp [hA2B, hA2C1, hA2C2, hA2D]),
    Finset.sum_insert (by simp [hBC1, hBC2, hBD]),
    Finset.sum_insert (by simp [hC12, hC1D]),
    Finset.sum_insert (by simp [hC2D]), Finset.sum_singleton]
  ring

/-- A sum over `Fin 6` without one named atom collapses to the other
five. -/
theorem six_sum_erase_eq {f : Fin 6 → ℝ}
    {atomA1 atomA2 atomB atomC1 atomC2 atomD : Fin 6}
    (hA12 : atomA1 ≠ atomA2) (hA1B : atomA1 ≠ atomB) (hA1C1 : atomA1 ≠ atomC1)
    (hA1C2 : atomA1 ≠ atomC2) (hA1D : atomA1 ≠ atomD)
    (hA2B : atomA2 ≠ atomB) (hA2C1 : atomA2 ≠ atomC1)
    (hA2C2 : atomA2 ≠ atomC2) (hA2D : atomA2 ≠ atomD)
    (hBC1 : atomB ≠ atomC1) (hBC2 : atomB ≠ atomC2) (hBD : atomB ≠ atomD)
    (hC12 : atomC1 ≠ atomC2) (hC1D : atomC1 ≠ atomD) (hC2D : atomC2 ≠ atomD) :
    ∑ atomIndex ∈ Finset.univ.erase atomB, f atomIndex
      = f atomA1 + f atomA2 + f atomC1 + f atomC2 + f atomD := by
  have hsplit := six_sum_univ_eq (f := f) hA12 hA1B hA1C1 hA1C2 hA1D hA2B
    hA2C1 hA2C2 hA2D hBC1 hBC2 hBD hC12 hC1D hC2D
  have herase : ∑ atomIndex : Fin 6, f atomIndex
      = f atomB + ∑ atomIndex ∈ Finset.univ.erase atomB, f atomIndex :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ atomB)).symm
  rw [hsplit] at herase
  linarith

/-! ## Layer 2 — the per-triple Schur test -/

/-- **THE PER-TRIPLE TEST.**  At a crux with a vanished cross entry, each
triple over the two anchors and one third atom either kills the crux
through the ceiling, or forces the determinant test at the margin half
the value. -/
theorem SixThreeCrux.schur_test_of_cross_zero (crux : SixThreeCrux)
    {activeIndex : Type*} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin 6 → ℝ)}
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    {atomB atomD atomX : Fin 6}
    (hBD : atomB ≠ atomD) (hBX : atomB ≠ atomX) (hDX : atomD ≠ atomX)
    (hvalueNeg : chartObjective (chartPointOfDesign crux.design) < 0)
    (hcross : chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomB atomD = 0) :
    (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomX atomX
        - chartObjective (chartPointOfDesign crux.design) / 2)
      * ((chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design) / 2)
        * (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomD
          - chartObjective (chartPointOfDesign crux.design) / 2))
      < (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomD
          - chartObjective (chartPointOfDesign crux.design) / 2)
        * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomX ^ 2
        + (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design) / 2)
          * chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomD atomX ^ 2 := by
  have hM : 0 < chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomB atomB
      - chartObjective (chartPointOfDesign crux.design) / 2 := by
    have hpos := crux.chartGap_diagonal_pos atomB
    linarith
  have hN : 0 < chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomD atomD
      - chartObjective (chartPointOfDesign crux.design) / 2 := by
    have hpos := crux.chartGap_diagonal_pos atomD
    linarith
  have hsymmDB := gap_entry_symm hdata atomD atomB
  have hsymmXB := gap_entry_symm hdata atomX atomB
  have hsymmXD := gap_entry_symm hdata atomX atomD
  by_cases hdominate : ∀ probeB probeD probeX : ℝ,
      chartObjective (chartPointOfDesign crux.design) / 2
          * (probeB * probeB + probeD * probeD + probeX * probeX)
        ≤ probeB * (chartPointGap (chartPointOfDesign crux.design) atomB atomB
              * probeB
            + chartPointGap (chartPointOfDesign crux.design) atomB atomD
              * probeD
            + chartPointGap (chartPointOfDesign crux.design) atomB atomX
              * probeX)
          + probeD * (chartPointGap (chartPointOfDesign crux.design) atomD
                atomB * probeB
            + chartPointGap (chartPointOfDesign crux.design) atomD atomD
              * probeD
            + chartPointGap (chartPointOfDesign crux.design) atomD atomX
              * probeX)
          + probeX * (chartPointGap (chartPointOfDesign crux.design) atomX
                atomB * probeB
            + chartPointGap (chartPointOfDesign crux.design) atomX atomD
              * probeD
            + chartPointGap (chartPointOfDesign crux.design) atomX atomX
              * probeX)
  · exact (crux.false_of_gap_triple_margin_entries hBD hBX hDX
      (margin := chartObjective (chartPointOfDesign crux.design) / 2)
      (by linarith) hdominate).elim
  · push Not at hdominate
    obtain ⟨probeB, probeD, probeX, hwitness⟩ := hdominate
    refine triple_schur_step hM hN (a := probeB) (b := probeD)
      (c := probeX) ?_
    have hbridge : chartPointGap (chartPointOfDesign crux.design)
        = chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight := rfl
    rw [hbridge] at hwitness
    have hexpand : probeB * ((chartStationaryGap
            (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design) / 2) * probeB
          + chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomX * probeX)
        + probeD * ((chartStationaryGap
            (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design) / 2) * probeD
          + chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomX * probeX)
        + probeX * (chartStationaryGap
            (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomX * probeB
          + chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomX * probeD
          + (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomX atomX
            - chartObjective (chartPointOfDesign crux.design) / 2) * probeX)
        = probeB * (chartStationaryGap
              (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomB * probeB
            + chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomD * probeD
            + chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomX * probeX)
          + probeD * (chartStationaryGap
              (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomD atomB * probeB
            + chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomD atomD * probeD
            + chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomD atomX * probeX)
          + probeX * (chartStationaryGap
              (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomX atomB * probeB
            + chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomX atomD * probeD
            + chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomX atomX * probeX)
          - chartObjective (chartPointOfDesign crux.design) / 2
            * (probeB * probeB + probeD * probeD + probeX * probeX) := by
      linear_combination (-probeB * probeD) * hsymmDB
        - 2 * probeB * probeD * hcross - probeX * probeB * hsymmXB
        - probeX * probeD * hsymmXD
    linarith [hexpand, hwitness]

/-! ## Layer 3 — the finale -/

/-- **THE FINALE.**  At the six-atom C4 pattern with a vanished cross
entry and the two collapse masses, the four summed determinant tests,
the trace read, and the budgets refuse the negative value. -/
theorem SixThreeCrux.false_of_bothParallel_finale (crux : SixThreeCrux)
    {activeIndex : Type*} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin 6 → ℝ)}
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    {atomA1 atomA2 atomB atomC1 atomC2 atomD : Fin 6}
    (hA12 : atomA1 ≠ atomA2) (hA1B : atomA1 ≠ atomB) (hA1C1 : atomA1 ≠ atomC1)
    (hA1C2 : atomA1 ≠ atomC2) (hA1D : atomA1 ≠ atomD)
    (hA2B : atomA2 ≠ atomB) (hA2C1 : atomA2 ≠ atomC1)
    (hA2C2 : atomA2 ≠ atomC2) (hA2D : atomA2 ≠ atomD)
    (hBC1 : atomB ≠ atomC1) (hBC2 : atomB ≠ atomC2) (hBD : atomB ≠ atomD)
    (hC12 : atomC1 ≠ atomC2) (hC1D : atomC1 ≠ atomD) (hC2D : atomC2 ≠ atomD)
    (hvalueNeg : chartObjective (chartPointOfDesign crux.design) < 0)
    (hcross : chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomB atomD = 0)
    (hSb : chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomA1 ^ 2
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomA2 ^ 2
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomC1 ^ 2
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomC2 ^ 2
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design))
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design))
          + (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design))) / 2)
    (hSd : chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomA1 ^ 2
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomA2 ^ 2
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomC1 ^ 2
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomC2 ^ 2
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomD
          - chartObjective (chartPointOfDesign crux.design))
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design))
          + (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design))) / 2) :
    False := by
  have hposB := crux.chartGap_diagonal_pos atomB
  have hposD := crux.chartGap_diagonal_pos atomD
  -- The four determinant tests at the four double atoms.
  have htestA1 := crux.schur_test_of_cross_zero hdata hBD hA1B.symm hA1D.symm
    hvalueNeg hcross
  have htestA2 := crux.schur_test_of_cross_zero hdata hBD hA2B.symm hA2D.symm
    hvalueNeg hcross
  have htestC1 := crux.schur_test_of_cross_zero hdata hBD hBC1 hC1D.symm
    hvalueNeg hcross
  have htestC2 := crux.schur_test_of_cross_zero hdata hBD hBC2 hC2D.symm
    hvalueNeg hcross
  -- Reorient the third-atom rows of the four tests through the symmetry.
  have hsymmXB : ∀ atomX : Fin 6,
      chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomX
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomX atomB := fun atomX =>
    gap_entry_symm hdata atomB atomX
  -- The trace read prices the diagonal sum.
  have htraceSix : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomA1 atomA1
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomA2 atomA2
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomB
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomC1 atomC1
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomC2 atomC2
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomD = 2 := by
    have htrace := six_atom_trace_read hdata
    have hread := six_sum_univ_eq
      (f := fun atomIndex => chartStationaryGap
        (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomIndex atomIndex)
      hA12 hA1B hA1C1 hA1C2 hA1D hA2B hA2C1 hA2C2 hA2D hBC1 hBC2 hBD
      hC12 hC1D hC2D
    rw [hread] at htrace
    rw [htrace]
    norm_num
  -- The chart entry equals the gap entry off the diagonal.
  have hentryOff : ∀ atomRow atomCol : Fin 6, atomRow ≠ atomCol →
      (chartPointOfDesign crux.design).chart atomRow atomCol
        = chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomRow atomCol := by
    intro atomRow atomCol hne
    rw [chartStationaryGap, Matrix.sub_apply,
      Matrix.diagonal_apply_ne _ hne, sub_zero]
  -- The b-row budget.
  have hbudgetB : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomB
        - chartObjective (chartPointOfDesign crux.design))
      * ((chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design))
        + (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomD
          - chartObjective (chartPointOfDesign crux.design))) / 2
      ≤ 1 / 4 := by
    have hsum := six_atom_offdiag_budget hdata atomB
    have herase := six_sum_erase_eq
      (f := fun atomCol => (chartPointOfDesign crux.design).chart atomB
          atomCol
        * (chartPointOfDesign crux.design).chart atomB atomCol)
      hA12 hA1B hA1C1 hA1C2 hA1D hA2B hA2C1 hA2C2 hA2D hBC1 hBC2 hBD
      hC12 hC1D hC2D
    rw [herase, hentryOff atomB atomA1 hA1B.symm,
      hentryOff atomB atomA2 hA2B.symm, hentryOff atomB atomC1 hBC1,
      hentryOff atomB atomC2 hBC2, hentryOff atomB atomD hBD,
      hcross] at hsum
    nlinarith [hsum, hSb]
  -- The d-row budget.
  have hbudgetD : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomD
        - chartObjective (chartPointOfDesign crux.design))
      * ((chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design))
        + (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomD
          - chartObjective (chartPointOfDesign crux.design))) / 2
      ≤ 1 / 4 := by
    have hsum := six_atom_offdiag_budget hdata atomD
    have herase := six_sum_erase_eq
      (f := fun atomCol => (chartPointOfDesign crux.design).chart atomD
          atomCol
        * (chartPointOfDesign crux.design).chart atomD atomCol)
      (atomB := atomD) (atomD := atomB)
      hA12 hA1D hA1C1 hA1C2 hA1B hA2D hA2C1 hA2C2 hA2B hC1D.symm hC2D.symm
      hBD.symm hC12 hBC1.symm hBC2.symm
    have hsymmDB := gap_entry_symm hdata atomD atomB
    rw [herase, hentryOff atomD atomA1 hA1D.symm,
      hentryOff atomD atomA2 hA2D.symm, hentryOff atomD atomC1 hC1D.symm,
      hentryOff atomD atomC2 hC2D.symm, hentryOff atomD atomB hBD.symm,
      hsymmDB, hcross] at hsum
    nlinarith [hsum, hSd]
  -- The landed final inequality at the shifted masses.
  have hfinal := schur_sum_nonneg
    (m := chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomB atomB
      - chartObjective (chartPointOfDesign crux.design))
    (n := chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomD atomD
      - chartObjective (chartPointOfDesign crux.design))
    (eta := -chartObjective (chartPointOfDesign crux.design) / 2)
    (by linarith) (by linarith) (by linarith)
    (by linarith [hbudgetB]) (by linarith [hbudgetD])
  -- The four tests sum against the final inequality.
  have hsumTests := add_lt_add (add_lt_add (add_lt_add htestA1 htestA2)
    htestC1) htestC2
  have hLHSeq : ((chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA1 atomA1
          - chartObjective (chartPointOfDesign crux.design) / 2)
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design) / 2)
          * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design) / 2))
      + (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA2 atomA2
          - chartObjective (chartPointOfDesign crux.design) / 2)
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design) / 2)
          * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design) / 2))
      + (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomC1 atomC1
          - chartObjective (chartPointOfDesign crux.design) / 2)
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design) / 2)
          * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design) / 2))
      + (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomC2 atomC2
          - chartObjective (chartPointOfDesign crux.design) / 2)
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design) / 2)
          * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design) / 2)))
      = (2 - (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design))
          - (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design))
          + 8 * (-chartObjective (chartPointOfDesign crux.design) / 2))
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomB
              - chartObjective (chartPointOfDesign crux.design)
              - -chartObjective (chartPointOfDesign crux.design) / 2)
          * (chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomD atomD
              - chartObjective (chartPointOfDesign crux.design)
              - -chartObjective (chartPointOfDesign crux.design) / 2)) := by
    linear_combination ((chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design) / 2)
        * (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomD
          - chartObjective (chartPointOfDesign crux.design) / 2))
      * htraceSix
  have hRHSeq : ((chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomD
          - chartObjective (chartPointOfDesign crux.design) / 2)
        * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomA1 ^ 2
        + (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design) / 2)
          * chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomD atomA1 ^ 2
      + ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design) / 2)
          * chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomA2 ^ 2
        + (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design) / 2)
          * chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomD atomA2 ^ 2)
      + ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design) / 2)
          * chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomC1 ^ 2
        + (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design) / 2)
          * chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomD atomC1 ^ 2)
      + ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design) / 2)
          * chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomC2 ^ 2
        + (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design) / 2)
          * chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomD atomC2 ^ 2))
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design))
          * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design))
          * ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomB
              - chartObjective (chartPointOfDesign crux.design))
            + (chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomD atomD
              - chartObjective (chartPointOfDesign crux.design)))
        - -chartObjective (chartPointOfDesign crux.design) / 2
          * ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomB
              - chartObjective (chartPointOfDesign crux.design))
            + (chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomD atomD
              - chartObjective (chartPointOfDesign crux.design))) ^ 2 / 2 := by
    linear_combination (chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomD
          - chartObjective (chartPointOfDesign crux.design) / 2) * hSb
      + (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design) / 2) * hSd
  linarith [hsumTests, hLHSeq, hRHSeq, hfinal]

end Gtz
