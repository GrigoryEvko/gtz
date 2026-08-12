import Gtz.Wave.AssemblyCircuitEquations
import Gtz.Reduction.DiagonalRungs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The datum support dichotomy — every active direction touches two or three atoms

The landed support dichotomy speaks about least-eigenvector FAMILIES.  The
rank-split campaign works with the DATUM's own tight directions, whose tight
equation holds coordinatewise on the block.  This file defines the ambient
support of a datum direction and lands the dichotomy at the datum: at a crux,
every active label's direction has EXACTLY TWO OR THREE nonzero coordinates.
The floor is the landed sign engine — a negative eigenvector of a matrix with
positive diagonal has two nonzero coordinates — applied to the block
submatrix, which the datum's coordinatewise tight equation reconstitutes
because the direction vanishes off its block.  The ceiling is the block.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.datumTightSupport` with `Gtz.mem_datumTightSupport` and
  `Gtz.datumTightSupport_subset` — the ambient support vocabulary.
* `Gtz.SixThreeCrux.two_le_card_datumTightSupport` — **THE FLOOR.**
* `Gtz.SixThreeCrux.card_datumTightSupport_eq_two_or_three` — **THE
  DICHOTOMY.**

## Vacuity

The crux statements are vacuous if `Gtz.GtzWeighted 6 3` holds.  The
vocabulary is unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- The ambient support of a datum tight direction. -/
noncomputable def datumTightSupport (tightDir : activeIndex → (Fin size → ℝ))
    (label : activeIndex) : Finset (Fin size) :=
  Finset.univ.filter fun atomIndex => tightDir label atomIndex ≠ 0

/-- Membership in the ambient support, unfolded. -/
theorem mem_datumTightSupport {label : activeIndex} {atomIndex : Fin size} :
    atomIndex ∈ datumTightSupport tightDir label ↔ tightDir label atomIndex ≠ 0 := by
  rw [datumTightSupport, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- The ambient support sits inside the label's block. -/
theorem datumTightSupport_subset
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet) :
    datumTightSupport tightDir label ⊆ activeSubset label := by
  intro atomIndex hatom
  by_contra hnot
  exact mem_datumTightSupport.mp hatom (hdata.tightDir_support label hmem atomIndex hnot)

namespace SixThreeCrux

variable {activeIndex : Type*}

/-- **THE SUPPORT FLOOR AT THE DATUM.**  Every active label's tight direction
has at least two nonzero coordinates.  The block submatrix carries the tight
equation because the direction vanishes off its block, the chart value is
negative at a crux, the chart-gap diagonal is positive by all-heaviness, and
the landed sign engine fires. -/
theorem two_le_card_datumTightSupport
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
    {label : activeIndex} (hmem : label ∈ activeSet) :
    2 ≤ (datumTightSupport tightDir label).card := by
  classical
  have hcard : (activeSubset label).card = 3 := hdata.activeSubset_card label hmem
  -- the block reconstitution of the tight equation
  have hblockUnit :
      (fun blockIndex => tightDir label ((activeSubset label).orderEmbOfFin hcard blockIndex))
        ⬝ᵥ (fun blockIndex =>
          tightDir label ((activeSubset label).orderEmbOfFin hcard blockIndex)) = 1 := by
    have hunitAmbient := hdata.tightDir_unit label hmem
    rw [← hunitAmbient]
    calc (fun blockIndex =>
            tightDir label ((activeSubset label).orderEmbOfFin hcard blockIndex))
          ⬝ᵥ (fun blockIndex =>
            tightDir label ((activeSubset label).orderEmbOfFin hcard blockIndex))
        = ∑ atomIndex ∈ activeSubset label,
            tightDir label atomIndex * tightDir label atomIndex :=
          sum_orderEmbOfFin_eq_sum (activeSubset label) hcard
            (fun atomIndex => tightDir label atomIndex * tightDir label atomIndex)
      _ = ∑ atomIndex, tightDir label atomIndex * tightDir label atomIndex :=
          Finset.sum_subset (Finset.subset_univ _) (fun atomIndex _ hnot => by
            rw [hdata.tightDir_support label hmem atomIndex hnot, mul_zero])
      _ = tightDir label ⬝ᵥ tightDir label := rfl
  have hblockEigen :
      (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight).submatrix
        ((activeSubset label).orderEmbOfFin hcard) ((activeSubset label).orderEmbOfFin hcard)
        *ᵥ (fun blockIndex =>
          tightDir label ((activeSubset label).orderEmbOfFin hcard blockIndex))
      = chartObjective (chartPointOfDesign crux.design)
          • fun blockIndex =>
            tightDir label ((activeSubset label).orderEmbOfFin hcard blockIndex) := by
    funext blockIndex
    have hentry :
        ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight).submatrix
          ((activeSubset label).orderEmbOfFin hcard)
          ((activeSubset label).orderEmbOfFin hcard)
          *ᵥ (fun innerIndex =>
            tightDir label ((activeSubset label).orderEmbOfFin hcard innerIndex))) blockIndex
        = ∑ atomIndex ∈ activeSubset label,
            chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight
              ((activeSubset label).orderEmbOfFin hcard blockIndex) atomIndex
            * tightDir label atomIndex := by
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
      exact sum_orderEmbOfFin_eq_sum (activeSubset label) hcard
        (fun atomIndex => chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          ((activeSubset label).orderEmbOfFin hcard blockIndex) atomIndex
          * tightDir label atomIndex)
    have hextend : ∑ atomIndex ∈ activeSubset label,
        chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          ((activeSubset label).orderEmbOfFin hcard blockIndex) atomIndex
        * tightDir label atomIndex
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            *ᵥ tightDir label) ((activeSubset label).orderEmbOfFin hcard blockIndex) := by
      rw [Finset.sum_subset (Finset.subset_univ _) (fun atomIndex _ hnot => by
        rw [hdata.tightDir_support label hmem atomIndex hnot, mul_zero])]
      simp only [Matrix.mulVec, dotProduct]
    have htight := hdata.tightDir_isTight label hmem
      ((activeSubset label).orderEmbOfFin hcard blockIndex)
      ((activeSubset label).orderEmbOfFin_mem hcard blockIndex)
    rw [hentry, hextend, htight]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hdiag : ∀ coordinate,
      0 < ((chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight).submatrix
        ((activeSubset label).orderEmbOfFin hcard)
        ((activeSubset label).orderEmbOfFin hcard)) coordinate coordinate := by
    intro coordinate
    have hbridge : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        = chartPointGap (chartPointOfDesign crux.design) := rfl
    rw [hbridge]
    simp only [Matrix.submatrix_apply, chartPointGap, chartPointOfDesign,
      Matrix.sub_apply, Matrix.diagonal_apply_eq]
    rw [projectionOfDesign_diagonal]
    have hweight := crux.design.weight_pos
      ((activeSubset label).orderEmbOfFin hcard coordinate)
    have hexcess := allHeavy_heavyExcess_pos crux.isAllHeavy
      ((activeSubset label).orderEmbOfFin hcard coordinate)
    rw [heavyExcess] at hexcess
    nlinarith
  obtain ⟨first, second, hne, hfirst, hsecond⟩ :=
    exists_two_ne_zero_of_unit_eigen_of_neg_of_pos_diagonal
      ((chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight).submatrix
        ((activeSubset label).orderEmbOfFin hcard)
        ((activeSubset label).orderEmbOfFin hcard))
      (fun blockIndex =>
        tightDir label ((activeSubset label).orderEmbOfFin hcard blockIndex))
      (chartObjective (chartPointOfDesign crux.design))
      hblockUnit hblockEigen crux.hasNegativeChartValue hdiag
  have hfirstMem : (activeSubset label).orderEmbOfFin hcard first
      ∈ datumTightSupport tightDir label := mem_datumTightSupport.mpr hfirst
  have hsecondMem : (activeSubset label).orderEmbOfFin hcard second
      ∈ datumTightSupport tightDir label := mem_datumTightSupport.mpr hsecond
  have hembNe : (activeSubset label).orderEmbOfFin hcard first
      ≠ (activeSubset label).orderEmbOfFin hcard second := fun hcollide =>
    hne (((activeSubset label).orderEmbOfFin hcard).injective hcollide)
  have honeLt : 1 < (datumTightSupport tightDir label).card :=
    Finset.one_lt_card.mpr ⟨_, hfirstMem, _, hsecondMem, hembNe⟩
  omega

/-- **THE DATUM SUPPORT DICHOTOMY.**  Every active label's tight direction has
exactly two or exactly three nonzero coordinates. -/
theorem card_datumTightSupport_eq_two_or_three
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
    {label : activeIndex} (hmem : label ∈ activeSet) :
    (datumTightSupport tightDir label).card = 2
      ∨ (datumTightSupport tightDir label).card = 3 := by
  have hlower := crux.two_le_card_datumTightSupport hdata hmem
  have hupper : (datumTightSupport tightDir label).card ≤ 3 := by
    have hsubset := Finset.card_le_card (datumTightSupport_subset hdata hmem)
    rw [hdata.activeSubset_card label hmem] at hsubset
    exact hsubset
  omega

end SixThreeCrux

end Gtz
