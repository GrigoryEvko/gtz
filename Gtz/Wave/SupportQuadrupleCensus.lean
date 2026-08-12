import Gtz.Wave.RankFourNormalForm
import Gtz.Wave.AssemblyBasisCoverage

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The support-quadruple census — the trichotomy of the rank-four rung

The four basis supports of a rank-four crux datum have cardinality two or
three (the dichotomy) and cover the six atoms (the coverage law).  The mass
count then forces a TRICHOTOMY: some support has cardinality two, or all
four have cardinality three and some atom is private to one support, or all
four have cardinality three and every atom sits in exactly two supports.
The three branches are the three kill groups of the rank-four rung.

## The realness calibration

The complex two-trine witness (`paper/sections/04-complex.tex`, two coplanar
trines with a shared axis) satisfies the FULL first-order system over the
complex field: constant diagonal exactly `1/6`, exact commutation, eighteen
argmax triples with uniform multipliers `1/18`, and the chart value
`(2 - sqrt 5)/6` inside the value window.  The witness sits in the RANK-SIX
cell: its assembly has rank six, with captured rank three and complement
rank three.  All eighteen directions are dense (ambient support three), and
all fifty-four entry products `q x * conj (q y)` are non-real.  Thus rank
four contains no known complex datum, but the survivor analysis is
field-agnostic, and every pattern branch must still END in a real-only
step.  The approved real-only exits are:

- The sign enumeration of an entry recovered from a square (over the
  complex field the phase is a continuum, over the reals a finite split)
- The odd sign cycle `false_of_oppositeSign_triangle` (at the trine every
  pair product carries a phase, thus the exit does not complexify)
- The real ratio of a two-by-two least eigenvector (the real symmetric gap
  block gives a real ratio, the Hermitian block gives a phase).

These tools are complex-valid and must NOT close a branch alone: the
private-atom linear kills, the parallel-pair atom merge, the circuit
equations, the H-form laws, the coverage law, the support dichotomy, and
the value and trace windows.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.basisSupportMultiplicity` with `Gtz.sum_basisSupportMultiplicity` —
  the multiplicity vocabulary and the double count.
* `Gtz.basisSupportMultiplicity_pos_of_Hform` — coverage from the H-form.
* `Gtz.datumTightSupport_eq_activeSubset_of_card_eq_rank` — a full support
  IS its block.
* `Gtz.basisSupport_trichotomy` — **THE TRICHOTOMY.**
* `Gtz.SixThreeCrux.exists_rankFour_support_dispatch` — **THE DISPATCH.**
  The normal form together with the trichotomy, at every rank-four crux
  datum.

## Vacuity

The crux statements are vacuous if `Gtz.GtzWeighted 6 3` holds.  The
combinatorial statements are unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- The number of basis supports that contain one atom. -/
noncomputable def basisSupportMultiplicity (tightDir : activeIndex → (Fin size → ℝ))
    (basisLabel : Fin basisCount → activeIndex) (atomIndex : Fin size) : ℕ :=
  (Finset.univ.filter fun columnIndex =>
    atomIndex ∈ datumTightSupport tightDir (basisLabel columnIndex)).card

/-- Double counting: the total multiplicity is the total support mass. -/
theorem sum_basisSupportMultiplicity (tightDir : activeIndex → (Fin size → ℝ))
    (basisLabel : Fin basisCount → activeIndex) :
    ∑ atomIndex : Fin size, basisSupportMultiplicity tightDir basisLabel atomIndex
      = ∑ columnIndex : Fin basisCount,
          (datumTightSupport tightDir (basisLabel columnIndex)).card := by
  classical
  simp only [basisSupportMultiplicity, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun columnIndex _ => ?_
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Coverage from the H-form: every atom meets some basis support.  A zero
row of the basis columns would read a zero assembly diagonal against the
constant `1/size`. -/
theorem basisSupportMultiplicity_pos_of_Hform
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (H : Matrix (Fin basisCount) (Fin basisCount) ℝ)
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    (atomIndex : Fin size) :
    0 < basisSupportMultiplicity tightDir basisLabel atomIndex := by
  classical
  have hexists : ∃ columnIndex : Fin basisCount,
      tightDir (basisLabel columnIndex) atomIndex ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hdiag := hdata.assembly_diagonal atomIndex
    rw [← hHform] at hdiag
    have hentry : (tightBasisColumns tightDir basisLabel * H
        * (tightBasisColumns tightDir basisLabel)ᵀ) atomIndex atomIndex = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun columnIndex _ => ?_
      have hzero : (tightBasisColumns tightDir basisLabel)ᵀ columnIndex atomIndex = 0 := by
        rw [Matrix.transpose_apply]
        exact hnone columnIndex
      rw [hzero, mul_zero]
    rw [hentry] at hdiag
    have hsizePos : (0 : ℝ) < ((size : ℝ))⁻¹ :=
      inv_pos.mpr (Nat.cast_pos.mpr (size_pos_of_isChartStationaryData hdata))
    linarith
  obtain ⟨columnIndex, hne⟩ := hexists
  rw [basisSupportMultiplicity, Finset.card_pos]
  exact ⟨columnIndex, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    mem_datumTightSupport.mpr hne⟩⟩

/-- A basis support of full block cardinality IS the block. -/
theorem datumTightSupport_eq_activeSubset_of_card_eq_rank
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    (hcard : (datumTightSupport tightDir label).card = rank) :
    datumTightSupport tightDir label = activeSubset label := by
  refine Finset.eq_of_subset_of_card_le (datumTightSupport_subset hdata hmem) ?_
  have hblockCard := hdata.activeSubset_card label hmem
  omega

/-- **THE SUPPORT-QUADRUPLE TRICHOTOMY.**  Four supports of cardinality two
or three that cover the six atoms fall into three classes: some support has
cardinality two, or all four have cardinality three and some atom is
private, or all four have cardinality three and every atom sits in exactly
two supports.  The last branch is the mass count: twelve incidences over
six atoms, each at least two, force exactly two everywhere. -/
theorem basisSupport_trichotomy {activeIndex : Type*}
    (tightDir : activeIndex → (Fin 6 → ℝ)) (basisLabel : Fin 4 → activeIndex)
    (hcard : ∀ columnIndex,
        (datumTightSupport tightDir (basisLabel columnIndex)).card = 2
      ∨ (datumTightSupport tightDir (basisLabel columnIndex)).card = 3)
    (hcover : ∀ atomIndex : Fin 6,
        0 < basisSupportMultiplicity tightDir basisLabel atomIndex) :
    (∃ columnIndex, (datumTightSupport tightDir (basisLabel columnIndex)).card = 2)
      ∨ ((∀ columnIndex,
            (datumTightSupport tightDir (basisLabel columnIndex)).card = 3)
          ∧ ∃ atomIndex,
              basisSupportMultiplicity tightDir basisLabel atomIndex = 1)
      ∨ ((∀ columnIndex,
            (datumTightSupport tightDir (basisLabel columnIndex)).card = 3)
          ∧ ∀ atomIndex,
              basisSupportMultiplicity tightDir basisLabel atomIndex = 2) := by
  classical
  by_cases htwo : ∃ columnIndex,
      (datumTightSupport tightDir (basisLabel columnIndex)).card = 2
  · exact Or.inl htwo
  have hthree : ∀ columnIndex,
      (datumTightSupport tightDir (basisLabel columnIndex)).card = 3 := fun columnIndex =>
    (hcard columnIndex).resolve_left fun hcontra => htwo ⟨columnIndex, hcontra⟩
  by_cases hprivate : ∃ atomIndex,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 1
  · exact Or.inr (Or.inl ⟨hthree, hprivate⟩)
  have htwoLe : ∀ atomIndex : Fin 6,
      2 ≤ basisSupportMultiplicity tightDir basisLabel atomIndex := by
    intro atomIndex
    have hpos := hcover atomIndex
    have hne : basisSupportMultiplicity tightDir basisLabel atomIndex ≠ 1 :=
      fun hcontra => hprivate ⟨atomIndex, hcontra⟩
    omega
  have hmass : ∑ atomIndex : Fin 6,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 12 := by
    rw [sum_basisSupportMultiplicity]
    have hsum : ∑ columnIndex : Fin 4,
        (datumTightSupport tightDir (basisLabel columnIndex)).card
        = ∑ _columnIndex : Fin 4, 3 :=
      Finset.sum_congr rfl fun columnIndex _ => hthree columnIndex
    rw [hsum]
    simp
  refine Or.inr (Or.inr ⟨hthree, fun atomIndex => ?_⟩)
  by_contra hne
  have hthreeLe : 3 ≤ basisSupportMultiplicity tightDir basisLabel atomIndex := by
    have := htwoLe atomIndex
    omega
  have hsplit : basisSupportMultiplicity tightDir basisLabel atomIndex
      + ∑ other ∈ Finset.univ.erase atomIndex,
          basisSupportMultiplicity tightDir basisLabel other = 12 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ atomIndex)]
    exact hmass
  have herase : (Finset.univ.erase atomIndex).card • 2
      ≤ ∑ other ∈ Finset.univ.erase atomIndex,
          basisSupportMultiplicity tightDir basisLabel other :=
    Finset.card_nsmul_le_sum _ _ _ fun other _ => htwoLe other
  have hcardErase : (Finset.univ.erase atomIndex).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ atomIndex), Finset.card_univ,
      Fintype.card_fin]
  rw [hcardErase, smul_eq_mul] at herase
  omega

/-- **THE CENSUS DISPATCH.**  Every rank-four crux datum carries the normal
form together with the support trichotomy: the three branches are the three
kill groups of the rank-four rung. -/
theorem SixThreeCrux.exists_rankFour_support_dispatch
    (crux : SixThreeCrux)
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hrankFour : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir))) = 4) :
    ∃ (reducedWeight : activeIndex → ℝ)
      (basisLabel : Fin 4 → activeIndex)
      (L : Matrix (Fin 4) (Fin 6) ℝ) (M H : Matrix (Fin 4) (Fin 4) ℝ),
      IsChartStationaryData 3
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design))
          activeSet activeSubset reducedWeight tightDir
        ∧ chartMultiplierAssembly activeSet reducedWeight tightDir
            = chartMultiplierAssembly activeSet activeWeight tightDir
        ∧ Function.Injective basisLabel
        ∧ (∀ columnIndex, basisLabel columnIndex
            ∈ positiveActiveSet activeSet reducedWeight)
        ∧ Submodule.span ℝ
              (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
            = LinearMap.range (Matrix.toLin'
                (chartMultiplierAssembly activeSet reducedWeight tightDir))
        ∧ L * tightBasisColumns tightDir basisLabel = 1
        ∧ (chartPointOfDesign crux.design).chart * tightBasisColumns tightDir basisLabel
            = tightBasisColumns tightDir basisLabel * M
        ∧ M * M = M
        ∧ tightBasisColumns tightDir basisLabel * H
              * (tightBasisColumns tightDir basisLabel)ᵀ
            = chartMultiplierAssembly activeSet reducedWeight tightDir
        ∧ Hᵀ = H
        ∧ H.PosSemidef
        ∧ (∀ coeffVec : Fin 4 → ℝ, H *ᵥ coeffVec = 0 → coeffVec = 0)
        ∧ M * H = H * Mᵀ
        ∧ Matrix.trace M = 2
        ∧ ((∃ columnIndex,
              (datumTightSupport tightDir (basisLabel columnIndex)).card = 2)
          ∨ ((∀ columnIndex,
                (datumTightSupport tightDir (basisLabel columnIndex)).card = 3)
              ∧ ∃ atomIndex,
                  basisSupportMultiplicity tightDir basisLabel atomIndex = 1)
          ∨ ((∀ columnIndex,
                (datumTightSupport tightDir (basisLabel columnIndex)).card = 3)
              ∧ ∀ atomIndex,
                  basisSupportMultiplicity tightDir basisLabel atomIndex = 2)) := by
  obtain ⟨reducedWeight, basisLabel, L, M, H, hreducedData, hassemblyEq, hinjective,
    hmem, hspan, hleft, hrepresentation, hidempotent, hHform, hsymmH, hpsd, hker,
    hexchange, htrace⟩ := crux.exists_rankFour_coefficient_normalForm hdata hrankFour
  have hcard : ∀ columnIndex,
      (datumTightSupport tightDir (basisLabel columnIndex)).card = 2
      ∨ (datumTightSupport tightDir (basisLabel columnIndex)).card = 3 := by
    intro columnIndex
    exact crux.card_datumTightSupport_eq_two_or_three hreducedData
      (positiveActiveSet_subset_activeSet (hmem columnIndex))
  have hcover : ∀ atomIndex : Fin 6,
      0 < basisSupportMultiplicity tightDir basisLabel atomIndex :=
    basisSupportMultiplicity_pos_of_Hform hreducedData basisLabel H hHform
  exact ⟨reducedWeight, basisLabel, L, M, H, hreducedData, hassemblyEq, hinjective,
    hmem, hspan, hleft, hrepresentation, hidempotent, hHform, hsymmH, hpsd, hker,
    hexchange, htrace, basisSupport_trichotomy tightDir basisLabel hcard hcover⟩

end Gtz
