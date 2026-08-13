import Gtz.Wave.BothParallelKernelRigidity
import Gtz.Wave.AssemblySupportCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The both-parallel extra-label trichotomy — the core reduction of closure five

The frame law carries a full positive-semidefinite Gram core.  Extra
positive labels fold into that core as off-diagonal mass, and the banked
diagonal-core kill does not see them.  This module classifies every
positive label of a both-parallel C4 stationary datum.  The
classification reduces the core to the diagonal case plus one named
residual branch.

The chain, for an extra positive label with direction `e`:

1. The direction lies in the span of the four basis directions, because
   the assembly range equals the span of the positive directions.
2. On each parallel pair, `e` aligns with the carrier restriction.
   Thus the two pair coordinates vanish together.
3. The support has at most three atoms.  Two alive pairs need four
   atoms, and this case dies by counting.
4. One alive pair puts `e` on the pair plus at most one anchor.  If `e`
   is not parallel to a carrier, a two-atom combination is tight on the
   pair alone, and the carrier eigen rows force a negative gap diagonal.
   The all-heavy field refuses, and only the parallel case survives.
5. No alive pair puts `e` on the two single atoms.  A singleton support
   dies by the same diagonal refusal.  The two-atom support is the
   circuit: its eigen rows force the product law and a nonzero cross
   entry.  The circuit laws are the named residual of this module.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.exists_basis_coefficients_of_pos` — the span decomposition.
* `Gtz.combination_apply_two` — the two-slot evaluation collapse.
* `Gtz.pair_aligned_vanish_iff` — the pair dichotomy.
* `Gtz.false_of_two_pairs_alive` — **THE COUNTING KILL.**
* `Gtz.false_of_pair_supported_tight` — **THE PAIR REFUSAL.**
* `Gtz.extra_pair_alive_parallel` — **THE PARALLEL PROMOTION.**
* `Gtz.false_of_extra_singleton`, `Gtz.false_of_extra_zero` — the small
  supports.
* `Gtz.extra_circuit_laws` — the circuit reduction laws.
* `Gtz.bothParallel_extra_label_trichotomy` — **THE TRICHOTOMY.**
* `Gtz.SixThreeCrux.chartGap_diagonal_pos` — the all-heavy gap floor.

## Vacuity

Only the crux-facing floor quantifies over a crux.  Every other
statement holds at each stationary datum with the stated hypotheses.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the span decomposition -/

/-- **THE SPAN DECOMPOSITION.**  A positively weighted direction is a
combination of the basis directions, because the assembly range equals
the basis span. -/
theorem exists_basis_coefficients_of_pos
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hspan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    {label : activeIndex} (hmem : label ∈ activeSet)
    (hpos : 0 < activeWeight label) :
    ∃ coeff : Fin basisCount → ℝ,
      ∑ columnIndex, coeff columnIndex • tightDir (basisLabel columnIndex)
        = tightDir label := by
  have hrange := tightDir_mem_range_multiplier_of_pos hdata hmem hpos
  rw [← hspan] at hrange
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp hrange

/-- A basis combination evaluates through the two slots that do not
vanish at the atom. -/
theorem combination_apply_two
    (basisLabel : Fin basisCount → activeIndex)
    {slotOne slotTwo : Fin basisCount} (hne : slotOne ≠ slotTwo)
    {atomIndex : Fin size}
    (hvanish : ∀ columnIndex, columnIndex ≠ slotOne → columnIndex ≠ slotTwo →
      tightDir (basisLabel columnIndex) atomIndex = 0)
    (coeff : Fin basisCount → ℝ) :
    (∑ columnIndex, coeff columnIndex • tightDir (basisLabel columnIndex))
        atomIndex
      = coeff slotOne * tightDir (basisLabel slotOne) atomIndex
        + coeff slotTwo * tightDir (basisLabel slotTwo) atomIndex := by
  have hnotOne : slotOne ∉ ({slotTwo} : Finset (Fin basisCount)) := fun hmem =>
    hne (Finset.mem_singleton.mp hmem)
  have hrestrict : ∑ columnIndex, coeff columnIndex
        * tightDir (basisLabel columnIndex) atomIndex
      = ∑ columnIndex ∈ ({slotOne, slotTwo} : Finset (Fin basisCount)),
          coeff columnIndex * tightDir (basisLabel columnIndex) atomIndex := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro columnIndex _ hnot
    have hcases : columnIndex ≠ slotOne ∧ columnIndex ≠ slotTwo := by
      constructor
      · intro heq
        exact hnot (heq ▸ Finset.mem_insert_self _ _)
      · intro heq
        exact hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [hvanish columnIndex hcases.1 hcases.2, mul_zero]
  calc (∑ columnIndex, coeff columnIndex
          • tightDir (basisLabel columnIndex)) atomIndex
      = ∑ columnIndex, coeff columnIndex
          * tightDir (basisLabel columnIndex) atomIndex := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = ∑ columnIndex ∈ ({slotOne, slotTwo} : Finset (Fin basisCount)),
          coeff columnIndex * tightDir (basisLabel columnIndex) atomIndex :=
        hrestrict
    _ = coeff slotOne * tightDir (basisLabel slotOne) atomIndex
        + coeff slotTwo * tightDir (basisLabel slotTwo) atomIndex := by
        rw [Finset.sum_insert hnotOne, Finset.sum_singleton]

/-- **THE PAIR DICHOTOMY.**  Aligned pair coordinates vanish together
when the reference coordinates are nonzero. -/
theorem pair_aligned_vanish_iff {coordOne coordTwo refOne refTwo : ℝ}
    (halign : coordOne * refTwo = coordTwo * refOne)
    (hrefOne : refOne ≠ 0) (hrefTwo : refTwo ≠ 0) :
    coordOne = 0 ↔ coordTwo = 0 := by
  constructor
  · intro hzero
    rw [hzero, zero_mul] at halign
    rcases mul_eq_zero.mp halign.symm with hcase | hcase
    · exact hcase
    · exact absurd hcase hrefOne
  · intro hzero
    rw [hzero, zero_mul] at halign
    rcases mul_eq_zero.mp halign with hcase | hcase
    · exact hcase
    · exact absurd hcase hrefTwo

/-! ## Layer 2 — the counting kill -/

/-- **THE COUNTING KILL.**  Four distinct alive atoms do not fit inside
a three-atom block. -/
theorem false_of_two_pairs_alive
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hrank : rank = 3) {label : activeIndex} (hmem : label ∈ activeSet)
    {atomW atomX atomY atomZ : Fin size}
    (hWX : atomW ≠ atomX) (hWY : atomW ≠ atomY) (hWZ : atomW ≠ atomZ)
    (hXY : atomX ≠ atomY) (hXZ : atomX ≠ atomZ) (hYZ : atomY ≠ atomZ)
    (hw : tightDir label atomW ≠ 0) (hx : tightDir label atomX ≠ 0)
    (hy : tightDir label atomY ≠ 0) (hz : tightDir label atomZ ≠ 0) : False := by
  have hmemOf : ∀ atomIndex, tightDir label atomIndex ≠ 0 →
      atomIndex ∈ activeSubset label := by
    intro atomIndex hne
    by_contra hnot
    exact hne (hdata.tightDir_support label hmem atomIndex hnot)
  have hsub : ({atomW, atomX, atomY, atomZ} : Finset (Fin size))
      ⊆ activeSubset label := by
    intro atomIndex hmemFour
    rcases Finset.mem_insert.mp hmemFour with heq | hmemThree
    · exact heq ▸ hmemOf atomW hw
    rcases Finset.mem_insert.mp hmemThree with heq | hmemTwo
    · exact heq ▸ hmemOf atomX hx
    rcases Finset.mem_insert.mp hmemTwo with heq | hmemOne
    · exact heq ▸ hmemOf atomY hy
    · exact (Finset.mem_singleton.mp hmemOne) ▸ hmemOf atomZ hz
  have hcardFour : ({atomW, atomX, atomY, atomZ} : Finset (Fin size)).card
      = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hWX, hWY, hWZ]),
      Finset.card_insert_of_notMem (by simp [hXY, hXZ]),
      Finset.card_insert_of_notMem (by simp [hYZ]), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  rw [hcardFour, hdata.activeSubset_card label hmem, hrank] at hle
  omega

/-! ## Layer 3 — the pair refusal -/

/-- **THE PAIR REFUSAL.**  A nonzero pair-supported tight probe aligned
with a card-3 carrier forces the anchor gap diagonal to the negative
value.  The all-heavy floor refuses. -/
theorem false_of_pair_supported_tight
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {carrier : activeIndex} (hmemA : carrier ∈ activeSet)
    {pairOne pairTwo anchor : Fin size}
    (h12 : pairOne ≠ pairTwo) (h1A : pairOne ≠ anchor) (h2A : pairTwo ≠ anchor)
    (hsuppA : ∀ atomIndex, atomIndex ≠ pairOne → atomIndex ≠ pairTwo →
      atomIndex ≠ anchor → tightDir carrier atomIndex = 0)
    (hq1 : tightDir carrier pairOne ≠ 0) (hq2 : tightDir carrier pairTwo ≠ 0)
    (hqA : tightDir carrier anchor ≠ 0)
    {probeOne probeTwo : ℝ}
    (hnotBoth : ¬(probeOne = 0 ∧ probeTwo = 0))
    (halign : probeOne * tightDir carrier pairTwo
      = probeTwo * tightDir carrier pairOne)
    (hrowOne : chartStationaryGap projection weight pairOne pairOne * probeOne
        + chartStationaryGap projection weight pairOne pairTwo * probeTwo
      = value * probeOne)
    (hrowTwo : chartStationaryGap projection weight pairTwo pairOne * probeOne
        + chartStationaryGap projection weight pairTwo pairTwo * probeTwo
      = value * probeTwo)
    (hvalueNeg : value < 0)
    (hdiag : 0 ≤ chartStationaryGap projection weight anchor anchor) :
    False := by
  have hprobeOne : probeOne ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at halign
    rcases mul_eq_zero.mp halign.symm with hcase | hcase
    · exact hnotBoth ⟨hzero, hcase⟩
    · exact hq1 hcase
  have hprobeTwo : probeTwo ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at halign
    rcases mul_eq_zero.mp halign with hcase | hcase
    · exact hnotBoth ⟨hcase, hzero⟩
    · exact hq2 hcase
  have hmemOf : ∀ atomIndex, tightDir carrier atomIndex ≠ 0 →
      atomIndex ∈ activeSubset carrier := by
    intro atomIndex hne
    by_contra hnot
    exact hne (hdata.tightDir_support carrier hmemA atomIndex hnot)
  have hrowQ1 := gap_row_eigen_triple hdata hmemA (hmemOf pairOne hq1)
    h12 h1A h2A hsuppA
  have hrowQ2 := gap_row_eigen_triple hdata hmemA (hmemOf pairTwo hq2)
    h12 h1A h2A hsuppA
  have hrowQA := gap_row_eigen_triple hdata hmemA (hmemOf anchor hqA)
    h12 h1A h2A hsuppA
  have hbracketOne : probeOne
      * (chartStationaryGap projection weight pairOne pairOne
          * tightDir carrier pairOne
        + chartStationaryGap projection weight pairOne pairTwo
          * tightDir carrier pairTwo
        - value * tightDir carrier pairOne) = 0 := by
    linear_combination tightDir carrier pairOne * hrowOne
      + chartStationaryGap projection weight pairOne pairTwo * halign
  have hbracketTwo : probeTwo
      * (chartStationaryGap projection weight pairTwo pairOne
          * tightDir carrier pairOne
        + chartStationaryGap projection weight pairTwo pairTwo
          * tightDir carrier pairTwo
        - value * tightDir carrier pairTwo) = 0 := by
    linear_combination tightDir carrier pairTwo * hrowTwo
      - chartStationaryGap projection weight pairTwo pairOne * halign
  have hanchorOne : chartStationaryGap projection weight pairOne anchor
      * tightDir carrier anchor = 0 := by
    rcases mul_eq_zero.mp hbracketOne with hcase | hcase
    · exact absurd hcase hprobeOne
    · linear_combination hrowQ1 - hcase
  have hanchorTwo : chartStationaryGap projection weight pairTwo anchor
      * tightDir carrier anchor = 0 := by
    rcases mul_eq_zero.mp hbracketTwo with hcase | hcase
    · exact absurd hcase hprobeTwo
    · linear_combination hrowQ2 - hcase
  have hgapOne : chartStationaryGap projection weight pairOne anchor = 0 := by
    rcases mul_eq_zero.mp hanchorOne with hcase | hcase
    · exact hcase
    · exact absurd hcase hqA
  have hgapTwo : chartStationaryGap projection weight pairTwo anchor = 0 := by
    rcases mul_eq_zero.mp hanchorTwo with hcase | hcase
    · exact hcase
    · exact absurd hcase hqA
  have hsymmOne := gap_entry_symm hdata anchor pairOne
  have hsymmTwo := gap_entry_symm hdata anchor pairTwo
  have hfinal : (chartStationaryGap projection weight anchor anchor - value)
      * tightDir carrier anchor = 0 := by
    linear_combination hrowQA - tightDir carrier pairOne * hsymmOne
      - tightDir carrier pairTwo * hsymmTwo
      - tightDir carrier pairOne * hgapOne - tightDir carrier pairTwo * hgapTwo
  rcases mul_eq_zero.mp hfinal with hcase | hcase
  · have hvalue : chartStationaryGap projection weight anchor anchor = value := by
      linarith [hcase]
    linarith
  · exact absurd hcase hqA

/-! ## Layer 4 — the parallel promotion -/

/-- **THE PARALLEL PROMOTION.**  An extra positive label alive on one
parallel pair is parallel to one of the two pair carriers.  Every other
escape dies through the pair refusal. -/
theorem extra_pair_alive_parallel
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex) (hrank : rank = 3)
    {slotOne slotTwo : Fin basisCount}
    {pairOne pairTwo anchorOne anchorTwo : Fin size}
    (h12 : pairOne ≠ pairTwo) (h1A : pairOne ≠ anchorOne)
    (h2A : pairTwo ≠ anchorOne) (h1B : pairOne ≠ anchorTwo)
    (h2B : pairTwo ≠ anchorTwo) (hAB : anchorOne ≠ anchorTwo)
    (hmemOne : basisLabel slotOne ∈ activeSet)
    (hmemTwo : basisLabel slotTwo ∈ activeSet)
    (hsuppOne : ∀ atomIndex, atomIndex ≠ pairOne → atomIndex ≠ pairTwo →
      atomIndex ≠ anchorOne → tightDir (basisLabel slotOne) atomIndex = 0)
    (hsuppTwo : ∀ atomIndex, atomIndex ≠ pairOne → atomIndex ≠ pairTwo →
      atomIndex ≠ anchorTwo → tightDir (basisLabel slotTwo) atomIndex = 0)
    (hq11 : tightDir (basisLabel slotOne) pairOne ≠ 0)
    (hq12 : tightDir (basisLabel slotOne) pairTwo ≠ 0)
    (hq1A : tightDir (basisLabel slotOne) anchorOne ≠ 0)
    (hq21 : tightDir (basisLabel slotTwo) pairOne ≠ 0)
    (hq22 : tightDir (basisLabel slotTwo) pairTwo ≠ 0)
    (hq2B : tightDir (basisLabel slotTwo) anchorTwo ≠ 0)
    (hdet : tightDir (basisLabel slotOne) pairOne
        * tightDir (basisLabel slotTwo) pairTwo
      - tightDir (basisLabel slotOne) pairTwo
        * tightDir (basisLabel slotTwo) pairOne = 0)
    {label : activeIndex} (hmem : label ∈ activeSet)
    (halign : tightDir label pairOne * tightDir (basisLabel slotOne) pairTwo
      = tightDir label pairTwo * tightDir (basisLabel slotOne) pairOne)
    (halive1 : tightDir label pairOne ≠ 0)
    (halive2 : tightDir label pairTwo ≠ 0)
    (hthirdCases : ∀ atomIndex ∈ activeSubset label, atomIndex ≠ pairOne →
      atomIndex ≠ pairTwo → atomIndex = anchorOne ∨ atomIndex = anchorTwo
        ∨ tightDir label atomIndex = 0)
    (hvalueNeg : value < 0)
    (hdiagOne : 0 ≤ chartStationaryGap projection weight anchorOne anchorOne)
    (hdiagTwo : 0 ≤ chartStationaryGap projection weight anchorTwo anchorTwo) :
    (∃ scal : ℝ, tightDir label = scal • tightDir (basisLabel slotOne))
      ∨ ∃ scal : ℝ, tightDir label = scal • tightDir (basisLabel slotTwo) := by
  have hmemOf : ∀ atomIndex, tightDir label atomIndex ≠ 0 →
      atomIndex ∈ activeSubset label := by
    intro atomIndex hne
    by_contra hnot
    exact hne (hdata.tightDir_support label hmem atomIndex hnot)
  have hpairOneMem := hmemOf pairOne halive1
  have hpairTwoMem := hmemOf pairTwo halive2
  have hcardThree : (activeSubset label).card = 3 := by
    rw [hdata.activeSubset_card label hmem, hrank]
  have hcardOne : (((activeSubset label).erase pairOne).erase pairTwo).card
      = 1 := by
    rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨h12.symm, hpairTwoMem⟩),
      Finset.card_erase_of_mem hpairOneMem, hcardThree]
  obtain ⟨third, hthirdEq⟩ := Finset.card_eq_one.mp hcardOne
  have hthirdMemErase : third
      ∈ ((activeSubset label).erase pairOne).erase pairTwo := by
    rw [hthirdEq]
    exact Finset.mem_singleton_self third
  have hthirdNeTwo : third ≠ pairTwo :=
    (Finset.mem_erase.mp hthirdMemErase).1
  have hthirdNeOne : third ≠ pairOne :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hthirdMemErase).2).1
  have hthirdMem : third ∈ activeSubset label :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hthirdMemErase).2).2
  have hsuppLabel : ∀ atomIndex, atomIndex ≠ pairOne → atomIndex ≠ pairTwo →
      atomIndex ≠ third → tightDir label atomIndex = 0 := by
    intro atomIndex hne1 hne2 hne3
    by_contra hne
    have hmemBlock := hmemOf atomIndex hne
    have hmemDouble : atomIndex
        ∈ ((activeSubset label).erase pairOne).erase pairTwo :=
      Finset.mem_erase.mpr ⟨hne2, Finset.mem_erase.mpr ⟨hne1, hmemBlock⟩⟩
    rw [hthirdEq, Finset.mem_singleton] at hmemDouble
    exact hne3 hmemDouble
  rcases hthirdCases third hthirdMem hthirdNeOne hthirdNeTwo with
    hthirdA | hthirdB | hthirdZero
  · -- The third atom is the first anchor: compare with the first carrier.
    rw [hthirdA] at hsuppLabel
    have hrowE1 := gap_row_eigen_triple hdata hmem hpairOneMem
      h12 h1A h2A hsuppLabel
    have hrowE2 := gap_row_eigen_triple hdata hmem hpairTwoMem
      h12 h1A h2A hsuppLabel
    have hmemOfOne : ∀ atomIndex,
        tightDir (basisLabel slotOne) atomIndex ≠ 0 →
        atomIndex ∈ activeSubset (basisLabel slotOne) := by
      intro atomIndex hne
      by_contra hnot
      exact hne (hdata.tightDir_support _ hmemOne atomIndex hnot)
    have hrowQ1 := gap_row_eigen_triple hdata hmemOne (hmemOfOne pairOne hq11)
      h12 h1A h2A hsuppOne
    have hrowQ2 := gap_row_eigen_triple hdata hmemOne (hmemOfOne pairTwo hq12)
      h12 h1A h2A hsuppOne
    by_cases hzero : tightDir (basisLabel slotOne) anchorOne
          * tightDir label pairOne
        - tightDir label anchorOne * tightDir (basisLabel slotOne) pairOne = 0
        ∧ tightDir (basisLabel slotOne) anchorOne * tightDir label pairTwo
        - tightDir label anchorOne * tightDir (basisLabel slotOne) pairTwo = 0
    · refine Or.inl ⟨tightDir label anchorOne
        / tightDir (basisLabel slotOne) anchorOne, ?_⟩
      funext atomIndex
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hq1A]
      by_cases hone : atomIndex = pairOne
      · subst hone
        linear_combination hzero.1
      by_cases htwo : atomIndex = pairTwo
      · subst htwo
        linear_combination hzero.2
      by_cases hthree : atomIndex = anchorOne
      · subst hthree
        ring
      · rw [hsuppLabel atomIndex hone htwo hthree,
          hsuppOne atomIndex hone htwo hthree]
        ring
    · exfalso
      refine false_of_pair_supported_tight hdata hmemOne h12 h1A h2A hsuppOne
        hq11 hq12 hq1A (probeOne := tightDir (basisLabel slotOne) anchorOne
          * tightDir label pairOne
          - tightDir label anchorOne * tightDir (basisLabel slotOne) pairOne)
        (probeTwo := tightDir (basisLabel slotOne) anchorOne
          * tightDir label pairTwo
          - tightDir label anchorOne * tightDir (basisLabel slotOne) pairTwo)
        ?_ ?_ ?_ ?_ hvalueNeg hdiagOne
      · intro hboth
        exact hzero ⟨hboth.1, hboth.2⟩
      · linear_combination tightDir (basisLabel slotOne) anchorOne * halign
      · linear_combination tightDir (basisLabel slotOne) anchorOne * hrowE1
          - tightDir label anchorOne * hrowQ1
      · linear_combination tightDir (basisLabel slotOne) anchorOne * hrowE2
          - tightDir label anchorOne * hrowQ2
  · -- The third atom is the second anchor: compare with the second carrier.
    rw [hthirdB] at hsuppLabel
    have halignTwo : tightDir label pairOne
          * tightDir (basisLabel slotTwo) pairTwo
        = tightDir label pairTwo * tightDir (basisLabel slotTwo) pairOne := by
      have hproduct : (tightDir label pairOne
            * tightDir (basisLabel slotTwo) pairTwo
          - tightDir label pairTwo * tightDir (basisLabel slotTwo) pairOne)
          * tightDir (basisLabel slotOne) pairOne = 0 := by
        linear_combination tightDir label pairOne * hdet
          + tightDir (basisLabel slotTwo) pairOne * halign
      rcases mul_eq_zero.mp hproduct with hcase | hcase
      · linarith [hcase]
      · exact absurd hcase hq11
    have hrowE1 := gap_row_eigen_triple hdata hmem hpairOneMem
      h12 h1B h2B hsuppLabel
    have hrowE2 := gap_row_eigen_triple hdata hmem hpairTwoMem
      h12 h1B h2B hsuppLabel
    have hmemOfTwo : ∀ atomIndex,
        tightDir (basisLabel slotTwo) atomIndex ≠ 0 →
        atomIndex ∈ activeSubset (basisLabel slotTwo) := by
      intro atomIndex hne
      by_contra hnot
      exact hne (hdata.tightDir_support _ hmemTwo atomIndex hnot)
    have hrowQ1 := gap_row_eigen_triple hdata hmemTwo (hmemOfTwo pairOne hq21)
      h12 h1B h2B hsuppTwo
    have hrowQ2 := gap_row_eigen_triple hdata hmemTwo (hmemOfTwo pairTwo hq22)
      h12 h1B h2B hsuppTwo
    by_cases hzero : tightDir (basisLabel slotTwo) anchorTwo
          * tightDir label pairOne
        - tightDir label anchorTwo * tightDir (basisLabel slotTwo) pairOne = 0
        ∧ tightDir (basisLabel slotTwo) anchorTwo * tightDir label pairTwo
        - tightDir label anchorTwo * tightDir (basisLabel slotTwo) pairTwo = 0
    · refine Or.inr ⟨tightDir label anchorTwo
        / tightDir (basisLabel slotTwo) anchorTwo, ?_⟩
      funext atomIndex
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hq2B]
      by_cases hone : atomIndex = pairOne
      · subst hone
        linear_combination hzero.1
      by_cases htwo : atomIndex = pairTwo
      · subst htwo
        linear_combination hzero.2
      by_cases hthree : atomIndex = anchorTwo
      · subst hthree
        ring
      · rw [hsuppLabel atomIndex hone htwo hthree,
          hsuppTwo atomIndex hone htwo hthree]
        ring
    · exfalso
      refine false_of_pair_supported_tight hdata hmemTwo h12 h1B h2B hsuppTwo
        hq21 hq22 hq2B (probeOne := tightDir (basisLabel slotTwo) anchorTwo
          * tightDir label pairOne
          - tightDir label anchorTwo * tightDir (basisLabel slotTwo) pairOne)
        (probeTwo := tightDir (basisLabel slotTwo) anchorTwo
          * tightDir label pairTwo
          - tightDir label anchorTwo * tightDir (basisLabel slotTwo) pairTwo)
        ?_ ?_ ?_ ?_ hvalueNeg hdiagTwo
      · intro hboth
        exact hzero ⟨hboth.1, hboth.2⟩
      · linear_combination tightDir (basisLabel slotTwo) anchorTwo * halignTwo
      · linear_combination tightDir (basisLabel slotTwo) anchorTwo * hrowE1
          - tightDir label anchorTwo * hrowQ1
      · linear_combination tightDir (basisLabel slotTwo) anchorTwo * hrowE2
          - tightDir label anchorTwo * hrowQ2
  · -- The third coordinate vanishes: the label itself is pair-supported.
    exfalso
    have hsuppPair : ∀ atomIndex, atomIndex ≠ pairOne → atomIndex ≠ pairTwo →
        tightDir label atomIndex = 0 := by
      intro atomIndex hne1 hne2
      by_cases hthree : atomIndex = third
      · exact hthree ▸ hthirdZero
      · exact hsuppLabel atomIndex hne1 hne2 hthree
    have hrowE1 := gap_row_eigen_pair hdata hmem hpairOneMem h12 hsuppPair
    have hrowE2 := gap_row_eigen_pair hdata hmem hpairTwoMem h12 hsuppPair
    exact false_of_pair_supported_tight hdata hmemOne h12 h1A h2A hsuppOne
      hq11 hq12 hq1A (fun hboth => halive1 hboth.1) halign hrowE1 hrowE2
      hvalueNeg hdiagOne

/-! ## Layer 5 — the small supports -/

/-- **THE SINGLETON REFUSAL.**  A direction alive at one atom only
forces that gap diagonal to the negative value. -/
theorem false_of_extra_singleton
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomAlive atomOther : Fin size} (hne : atomAlive ≠ atomOther)
    (halive : tightDir label atomAlive ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomAlive →
      tightDir label atomIndex = 0)
    (hvalueNeg : value < 0)
    (hdiag : 0 ≤ chartStationaryGap projection weight atomAlive atomAlive) :
    False := by
  have hmemAlive : atomAlive ∈ activeSubset label := by
    by_contra hnot
    exact halive (hdata.tightDir_support label hmem atomAlive hnot)
  have hsuppPair : ∀ atomIndex, atomIndex ≠ atomAlive →
      atomIndex ≠ atomOther → tightDir label atomIndex = 0 :=
    fun atomIndex hne1 _ => hsupp atomIndex hne1
  have hrow := gap_row_eigen_pair hdata hmem hmemAlive hne hsuppPair
  rw [hsupp atomOther (Ne.symm hne), mul_zero, add_zero] at hrow
  have hproduct : (chartStationaryGap projection weight atomAlive atomAlive
      - value) * tightDir label atomAlive = 0 := by
    linear_combination hrow
  rcases mul_eq_zero.mp hproduct with hcase | hcase
  · have hvalue : chartStationaryGap projection weight atomAlive atomAlive
        = value := by linarith [hcase]
    linarith
  · exact absurd hcase halive

/-- **THE ZERO REFUSAL.**  A tight direction does not vanish everywhere,
because it is a unit vector. -/
theorem false_of_extra_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    (hzero : ∀ atomIndex, tightDir label atomIndex = 0) : False := by
  have hunit := hdata.tightDir_unit label hmem
  rw [dotProduct, Finset.sum_eq_zero
    (fun atomIndex _ => by rw [hzero atomIndex, mul_zero])] at hunit
  exact zero_ne_one hunit

/-! ## Layer 6 — the circuit reduction laws -/

/-- **THE CIRCUIT LAWS.**  A direction alive at exactly the two single
atoms forces the singular product law, a nonzero cross entry, and one
annihilated third row. -/
theorem extra_circuit_laws
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hrank : rank = 3) {label : activeIndex} (hmem : label ∈ activeSet)
    {atomB atomD : Fin size} (hBD : atomB ≠ atomD)
    (hb : tightDir label atomB ≠ 0) (hd : tightDir label atomD ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      tightDir label atomIndex = 0)
    (hvalueNeg : value < 0)
    (hdiagB : 0 ≤ chartStationaryGap projection weight atomB atomB) :
    chartStationaryGap projection weight atomB atomD ≠ 0
      ∧ (chartStationaryGap projection weight atomB atomB - value)
          * (chartStationaryGap projection weight atomD atomD - value)
        = chartStationaryGap projection weight atomB atomD ^ 2
      ∧ ∃ atomThird, atomThird ∈ activeSubset label ∧ atomThird ≠ atomB
        ∧ atomThird ≠ atomD
        ∧ chartStationaryGap projection weight atomThird atomB
            * tightDir label atomB
          + chartStationaryGap projection weight atomThird atomD
            * tightDir label atomD = 0 := by
  have hmemOf : ∀ atomIndex, tightDir label atomIndex ≠ 0 →
      atomIndex ∈ activeSubset label := by
    intro atomIndex hne
    by_contra hnot
    exact hne (hdata.tightDir_support label hmem atomIndex hnot)
  have hmemB := hmemOf atomB hb
  have hmemD := hmemOf atomD hd
  have hrowB := gap_row_eigen_pair hdata hmem hmemB hBD hsupp
  have hrowD := gap_row_eigen_pair hdata hmem hmemD hBD hsupp
  have hsymmDB := gap_entry_symm hdata atomD atomB
  have hcrossNe : chartStationaryGap projection weight atomB atomD ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul, add_zero] at hrowB
    have hproduct : (chartStationaryGap projection weight atomB atomB - value)
        * tightDir label atomB = 0 := by
      linear_combination hrowB
    rcases mul_eq_zero.mp hproduct with hcase | hcase
    · have hvalue : chartStationaryGap projection weight atomB atomB
          = value := by linarith [hcase]
      linarith
    · exact absurd hcase hb
  have hproductLaw : (chartStationaryGap projection weight atomB atomB - value)
      * (chartStationaryGap projection weight atomD atomD - value)
      = chartStationaryGap projection weight atomB atomD ^ 2 := by
    have hcancel : ((chartStationaryGap projection weight atomB atomB - value)
        * (chartStationaryGap projection weight atomD atomD - value)
        - chartStationaryGap projection weight atomB atomD ^ 2)
        * (tightDir label atomB * tightDir label atomD) = 0 := by
      linear_combination (chartStationaryGap projection weight atomD atomD
            - value) * tightDir label atomD * hrowB
        - chartStationaryGap projection weight atomB atomD
          * tightDir label atomD * hrowD
        + chartStationaryGap projection weight atomB atomD
          * tightDir label atomB * tightDir label atomD * hsymmDB
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · rcases mul_eq_zero.mp hcase with hcase' | hcase'
      · exact absurd hcase' hb
      · exact absurd hcase' hd
  have hcardThree : (activeSubset label).card = 3 := by
    rw [hdata.activeSubset_card label hmem, hrank]
  have hcardOne : (((activeSubset label).erase atomB).erase atomD).card
      = 1 := by
    rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hBD.symm, hmemD⟩),
      Finset.card_erase_of_mem hmemB, hcardThree]
  obtain ⟨third, hthirdEq⟩ := Finset.card_eq_one.mp hcardOne
  have hthirdMemErase : third
      ∈ ((activeSubset label).erase atomB).erase atomD := by
    rw [hthirdEq]
    exact Finset.mem_singleton_self third
  have hthirdNeD : third ≠ atomD := (Finset.mem_erase.mp hthirdMemErase).1
  have hthirdNeB : third ≠ atomB :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hthirdMemErase).2).1
  have hthirdMem : third ∈ activeSubset label :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hthirdMemErase).2).2
  have hrowThird := gap_row_eigen_pair hdata hmem hthirdMem hBD hsupp
  rw [hsupp third hthirdNeB hthirdNeD, mul_zero] at hrowThird
  exact ⟨hcrossNe, hproductLaw, third, hthirdMem, hthirdNeB, hthirdNeD,
    hrowThird⟩

/-! ## Layer 7 — the trichotomy capstone -/

/-- **THE TRICHOTOMY.**  At a both-parallel C4 stationary datum, every
positive label is parallel to a basis direction, or its direction lives
on exactly the two single atoms and obeys the circuit laws.  Every other
pattern dies inside the proof. -/
theorem bothParallel_extra_label_trichotomy
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex) (hrank : rank = 3)
    (hspan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    {slotA slotB slotC slotD : Fin basisCount}
    (hslotAB : slotA ≠ slotB) (hslotCD : slotC ≠ slotD)
    (hmemA : basisLabel slotA ∈ activeSet) (hmemB : basisLabel slotB ∈ activeSet)
    (hmemC : basisLabel slotC ∈ activeSet) (hmemD : basisLabel slotD ∈ activeSet)
    {atomA1 atomA2 atomB atomC1 atomC2 atomD : Fin size}
    (hA12 : atomA1 ≠ atomA2) (hA1D : atomA1 ≠ atomD) (hA2D : atomA2 ≠ atomD)
    (hA1B : atomA1 ≠ atomB) (hA2B : atomA2 ≠ atomB)
    (hC12 : atomC1 ≠ atomC2) (hC1B : atomC1 ≠ atomB) (hC2B : atomC2 ≠ atomB)
    (hC1D : atomC1 ≠ atomD) (hC2D : atomC2 ≠ atomD) (hBD : atomB ≠ atomD)
    (hA1C1 : atomA1 ≠ atomC1) (hA1C2 : atomA1 ≠ atomC2)
    (hA2C1 : atomA2 ≠ atomC1) (hA2C2 : atomA2 ≠ atomC2)
    (hsuppA : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotA) atomIndex = 0)
    (hsuppB : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotB) atomIndex = 0)
    (hsuppC : ∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotC) atomIndex = 0)
    (hsuppD : ∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotD) atomIndex = 0)
    (hqA1 : tightDir (basisLabel slotA) atomA1 ≠ 0)
    (hqA2 : tightDir (basisLabel slotA) atomA2 ≠ 0)
    (hqAd : tightDir (basisLabel slotA) atomD ≠ 0)
    (hqB1 : tightDir (basisLabel slotB) atomA1 ≠ 0)
    (hqB2 : tightDir (basisLabel slotB) atomA2 ≠ 0)
    (hqBb : tightDir (basisLabel slotB) atomB ≠ 0)
    (hqC1 : tightDir (basisLabel slotC) atomC1 ≠ 0)
    (hqC2 : tightDir (basisLabel slotC) atomC2 ≠ 0)
    (hqCb : tightDir (basisLabel slotC) atomB ≠ 0)
    (hqD1 : tightDir (basisLabel slotD) atomC1 ≠ 0)
    (hqD2 : tightDir (basisLabel slotD) atomC2 ≠ 0)
    (hqDd : tightDir (basisLabel slotD) atomD ≠ 0)
    (hdetAB : tightDir (basisLabel slotA) atomA1
        * tightDir (basisLabel slotB) atomA2
      - tightDir (basisLabel slotA) atomA2
        * tightDir (basisLabel slotB) atomA1 = 0)
    (hdetCD : tightDir (basisLabel slotC) atomC1
        * tightDir (basisLabel slotD) atomC2
      - tightDir (basisLabel slotC) atomC2
        * tightDir (basisLabel slotD) atomC1 = 0)
    (hvanishPairA : ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
      tightDir (basisLabel columnIndex) atomA1 = 0
        ∧ tightDir (basisLabel columnIndex) atomA2 = 0)
    (hvanishPairC : ∀ columnIndex, columnIndex ≠ slotC → columnIndex ≠ slotD →
      tightDir (basisLabel columnIndex) atomC1 = 0
        ∧ tightDir (basisLabel columnIndex) atomC2 = 0)
    (hsix : ∀ atomIndex : Fin size, atomIndex = atomA1 ∨ atomIndex = atomA2
      ∨ atomIndex = atomB ∨ atomIndex = atomC1 ∨ atomIndex = atomC2
      ∨ atomIndex = atomD)
    (hvalueNeg : value < 0)
    (hdiagNonneg : ∀ atomIndex,
      0 ≤ chartStationaryGap projection weight atomIndex atomIndex)
    {label : activeIndex} (hmem : label ∈ activeSet)
    (hpos : 0 < activeWeight label) :
    (∃ (slot : Fin basisCount) (scal : ℝ),
        tightDir label = scal • tightDir (basisLabel slot))
      ∨ (tightDir label atomB ≠ 0 ∧ tightDir label atomD ≠ 0
        ∧ (∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
            tightDir label atomIndex = 0)
        ∧ chartStationaryGap projection weight atomB atomD ≠ 0
        ∧ (chartStationaryGap projection weight atomB atomB - value)
            * (chartStationaryGap projection weight atomD atomD - value)
          = chartStationaryGap projection weight atomB atomD ^ 2
        ∧ ∃ atomThird, atomThird ∈ activeSubset label ∧ atomThird ≠ atomB
          ∧ atomThird ≠ atomD
          ∧ chartStationaryGap projection weight atomThird atomB
              * tightDir label atomB
            + chartStationaryGap projection weight atomThird atomD
              * tightDir label atomD = 0) := by
  obtain ⟨coeff, hcoeff⟩ := exists_basis_coefficients_of_pos hdata basisLabel
    hspan hmem hpos
  have happA1 : tightDir label atomA1
      = coeff slotA * tightDir (basisLabel slotA) atomA1
        + coeff slotB * tightDir (basisLabel slotB) atomA1 := by
    rw [← hcoeff]
    exact combination_apply_two basisLabel hslotAB
      (fun columnIndex hne1 hne2 => (hvanishPairA columnIndex hne1 hne2).1)
      coeff
  have happA2 : tightDir label atomA2
      = coeff slotA * tightDir (basisLabel slotA) atomA2
        + coeff slotB * tightDir (basisLabel slotB) atomA2 := by
    rw [← hcoeff]
    exact combination_apply_two basisLabel hslotAB
      (fun columnIndex hne1 hne2 => (hvanishPairA columnIndex hne1 hne2).2)
      coeff
  have happC1 : tightDir label atomC1
      = coeff slotC * tightDir (basisLabel slotC) atomC1
        + coeff slotD * tightDir (basisLabel slotD) atomC1 := by
    rw [← hcoeff]
    exact combination_apply_two basisLabel hslotCD
      (fun columnIndex hne1 hne2 => (hvanishPairC columnIndex hne1 hne2).1)
      coeff
  have happC2 : tightDir label atomC2
      = coeff slotC * tightDir (basisLabel slotC) atomC2
        + coeff slotD * tightDir (basisLabel slotD) atomC2 := by
    rw [← hcoeff]
    exact combination_apply_two basisLabel hslotCD
      (fun columnIndex hne1 hne2 => (hvanishPairC columnIndex hne1 hne2).2)
      coeff
  have halignA : tightDir label atomA1 * tightDir (basisLabel slotA) atomA2
      = tightDir label atomA2 * tightDir (basisLabel slotA) atomA1 := by
    linear_combination tightDir (basisLabel slotA) atomA2 * happA1
      - tightDir (basisLabel slotA) atomA1 * happA2 - coeff slotB * hdetAB
  have halignC : tightDir label atomC1 * tightDir (basisLabel slotC) atomC2
      = tightDir label atomC2 * tightDir (basisLabel slotC) atomC1 := by
    linear_combination tightDir (basisLabel slotC) atomC2 * happC1
      - tightDir (basisLabel slotC) atomC1 * happC2 - coeff slotD * hdetCD
  have hdichA := pair_aligned_vanish_iff halignA hqA1 hqA2
  have hdichC := pair_aligned_vanish_iff halignC hqC1 hqC2
  by_cases haliveA : tightDir label atomA1 = 0
  · by_cases haliveC : tightDir label atomC1 = 0
    · -- Both pairs vanish: the small supports and the circuit.
      have hzeroA2 := hdichA.mp haliveA
      have hzeroC2 := hdichC.mp haliveC
      have hsuppBD : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
          tightDir label atomIndex = 0 := by
        intro atomIndex hneB hneD
        rcases hsix atomIndex with heq | heq | heq | heq | heq | heq
        · exact heq ▸ haliveA
        · exact heq ▸ hzeroA2
        · exact absurd heq hneB
        · exact heq ▸ haliveC
        · exact heq ▸ hzeroC2
        · exact absurd heq hneD
      by_cases hb : tightDir label atomB = 0
      · by_cases hd : tightDir label atomD = 0
        · exact (false_of_extra_zero hdata hmem (fun atomIndex => by
            by_cases hcaseB : atomIndex = atomB
            · exact hcaseB ▸ hb
            by_cases hcaseD : atomIndex = atomD
            · exact hcaseD ▸ hd
            · exact hsuppBD atomIndex hcaseB hcaseD)).elim
        · exact (false_of_extra_singleton hdata hmem hBD.symm hd
            (fun atomIndex hne => by
              by_cases hcaseB : atomIndex = atomB
              · exact hcaseB ▸ hb
              · exact hsuppBD atomIndex hcaseB hne)
            hvalueNeg (hdiagNonneg atomD)).elim
      · by_cases hd : tightDir label atomD = 0
        · exact (false_of_extra_singleton hdata hmem hBD hb
            (fun atomIndex hne => by
              by_cases hcaseD : atomIndex = atomD
              · exact hcaseD ▸ hd
              · exact hsuppBD atomIndex hne hcaseD)
            hvalueNeg (hdiagNonneg atomB)).elim
        · obtain ⟨hcrossNe, hproductLaw, hthird⟩ := extra_circuit_laws hdata
            hrank hmem hBD hb hd hsuppBD hvalueNeg (hdiagNonneg atomB)
          exact Or.inr ⟨hb, hd, hsuppBD, hcrossNe, hproductLaw, hthird⟩
    · -- The copair is alive: promote through its two carriers.
      have haliveC2 : tightDir label atomC2 ≠ 0 :=
        fun hzero => haliveC (hdichC.mpr hzero)
      have hthirdCases : ∀ atomIndex ∈ activeSubset label,
          atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
          atomIndex = atomB ∨ atomIndex = atomD
            ∨ tightDir label atomIndex = 0 := by
        intro atomIndex _ hne1 hne2
        rcases hsix atomIndex with heq | heq | heq | heq | heq | heq
        · exact Or.inr (Or.inr (heq ▸ haliveA))
        · exact Or.inr (Or.inr (heq ▸ hdichA.mp haliveA))
        · exact Or.inl heq
        · exact absurd heq hne1
        · exact absurd heq hne2
        · exact Or.inr (Or.inl heq)
      rcases extra_pair_alive_parallel hdata basisLabel hrank
        hC12 hC1B hC2B hC1D hC2D hBD hmemC hmemD hsuppC hsuppD
        hqC1 hqC2 hqCb hqD1 hqD2 hqDd hdetCD hmem halignC haliveC haliveC2
        hthirdCases hvalueNeg (hdiagNonneg atomB) (hdiagNonneg atomD) with
        hparallel | hparallel
      · exact Or.inl ⟨slotC, hparallel⟩
      · exact Or.inl ⟨slotD, hparallel⟩
  · by_cases haliveC : tightDir label atomC1 = 0
    · -- The pair is alive: promote through its two carriers.
      have haliveA2 : tightDir label atomA2 ≠ 0 :=
        fun hzero => haliveA (hdichA.mpr hzero)
      have hthirdCases : ∀ atomIndex ∈ activeSubset label,
          atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
          atomIndex = atomD ∨ atomIndex = atomB
            ∨ tightDir label atomIndex = 0 := by
        intro atomIndex _ hne1 hne2
        rcases hsix atomIndex with heq | heq | heq | heq | heq | heq
        · exact absurd heq hne1
        · exact absurd heq hne2
        · exact Or.inr (Or.inl heq)
        · exact Or.inr (Or.inr (heq ▸ haliveC))
        · exact Or.inr (Or.inr (heq ▸ hdichC.mp haliveC))
        · exact Or.inl heq
      rcases extra_pair_alive_parallel hdata basisLabel hrank
        hA12 hA1D hA2D hA1B hA2B (fun heq => hBD heq.symm) hmemA hmemB
        hsuppA hsuppB hqA1 hqA2 hqAd hqB1 hqB2 hqBb hdetAB hmem halignA
        haliveA haliveA2 hthirdCases hvalueNeg
        (hdiagNonneg atomD) (hdiagNonneg atomB) with hparallel | hparallel
      · exact Or.inl ⟨slotA, hparallel⟩
      · exact Or.inl ⟨slotB, hparallel⟩
    · -- Both pairs alive: four atoms in a three-atom block.
      exact (false_of_two_pairs_alive hdata hrank hmem hA12 hA1C1 hA1C2
        hA2C1 hA2C2 hC12 haliveA (fun hzero => haliveA (hdichA.mpr hzero))
        haliveC (fun hzero => haliveC (hdichC.mpr hzero))).elim

/-! ## Layer 8 — the all-heavy gap floor -/

/-- **THE GAP FLOOR.**  At an all-heavy crux, every diagonal entry of
the stationary gap is positive: the leverage excess prices it. -/
theorem SixThreeCrux.chartGap_diagonal_pos (crux : SixThreeCrux)
    (atomIndex : Fin 6) :
    0 < chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomIndex atomIndex := by
  have hbridge : chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      = chartPointGap (chartPointOfDesign crux.design) := rfl
  rw [hbridge]
  simp only [chartPointGap, chartPointOfDesign, Matrix.sub_apply,
    Matrix.diagonal_apply_eq]
  rw [projectionOfDesign_diagonal]
  have hweight := crux.design.weight_pos atomIndex
  have hexcess := allHeavy_heavyExcess_pos crux.isAllHeavy atomIndex
  rw [heavyExcess] at hexcess
  nlinarith

end Gtz
