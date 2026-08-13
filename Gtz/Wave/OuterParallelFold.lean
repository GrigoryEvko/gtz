import Gtz.Wave.OuterBlockDegreeDispatch
import Gtz.Wave.PrivateAtomGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The outer parallel fold — parallel labels give the diagonal Gram

The block-pin machinery consumes a diagonal Gram core.  This file
supplies it.  The Gram core is the left-inverse conjugation of the
assembly, thus its entries are the multiplier sums of coefficient
products.  A positive label parallel to a basis column has an axis
coefficient vector, and an axis pair with two distinct slots kills
every product.  Thus a datum whose positive labels are all parallel to
basis columns has a diagonal Gram core, with no partition of the label
set and no choice bookkeeping.

The circuit residue names the other arm: a positive label parallel to
no basis column.  The router turns a closed circuit residue into the
parallel hypothesis at every datum.  The composition narrows the
rank-four outer datum to the fully two-carrier dense branch, and gives
the rank-five and rank-six data the refined profile kills.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.gram_offdiag_eq_zero_of_parallel` — **THE FOLD.**
* `Gtz.exists_diagonal_gram_of_parallel` — the diagonal Gram package.
* `Gtz.RankFourOuterCircuitClosed`, `Gtz.RankFiveOuterCircuitClosed`,
  `Gtz.RankSixOuterCircuitClosed` — the circuit residues.
* `Gtz.RankFourOuterData.parallel_of_circuitClosed` — the router.
* `Gtz.RankFourOuterData.dense_of_circuitClosed_interior` — **THE
  RANK-FOUR NARROWING AT THE DATUM.**
* `Gtz.RankFiveOuterData.false_of_circuitClosed_refined`,
  `Gtz.RankSixOuterData.false_of_circuitClosed_refined` — the refined
  profile kills at the datum.

## Vacuity

The datum statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no
crux exists, thus no frame exists.
-/

namespace Gtz

open Matrix

variable {activeIndex : Type*} {basisCount : ℕ}
variable {projection : Matrix (Fin 6) (Fin 6) ℝ} {weight : Fin 6 → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin 6)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin 6 → ℝ)}

/-! ## Layer 1 — the fold -/

/-- **THE FOLD.**  If every positive active label is parallel to a
basis column, the Gram core has a zero off-diagonal.  Each summand of
the conjugated assembly carries an axis pair, and two distinct slots
kill the product. -/
theorem gram_offdiag_eq_zero_of_parallel
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    {leftInv : Matrix (Fin basisCount) (Fin 6) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {gram : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * gram
        * (tightBasisColumns tightDir basisLabel)ᵀ
      = chartMultiplierAssembly activeSet activeWeight tightDir)
    (hpar : ∀ label ∈ activeSet, 0 < activeWeight label →
      ∃ (slot : Fin basisCount) (scale : ℝ),
        tightDir label = scale • tightDir (basisLabel slot))
    {rowSlot colSlot : Fin basisCount} (hne : rowSlot ≠ colSlot) :
    gram rowSlot colSlot = 0 := by
  classical
  have hentry : gram rowSlot colSlot = ∑ label ∈ activeSet,
      activeWeight label * ((leftInv *ᵥ tightDir label) rowSlot
        * (leftInv *ᵥ tightDir label) colSlot) := by
    rw [coefficientGram_eq_sum_of_Hform basisLabel leftInv hleft hHform,
      Matrix.sum_apply]
    simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      smul_eq_mul]
  rw [hentry]
  refine Finset.sum_eq_zero fun label hmem => ?_
  rcases (hdata.activeWeight_nonneg label hmem).lt_or_eq with hpos | hzero
  · obtain ⟨slot, scale, hparl⟩ := hpar label hmem hpos
    have hL : leftInv *ᵥ tightDir label = scale • Pi.single slot 1 := by
      rw [hparl, Matrix.mulVec_smul,
        leftInverse_mulVec_tightDir_basisLabel basisLabel leftInv hleft
          slot]
    rw [hL]
    rcases ne_or_eq rowSlot slot with hrow | hrow
    · have hzeroRow : (scale • (Pi.single slot 1 : Fin basisCount → ℝ))
          rowSlot = 0 := by
        rw [Pi.smul_apply, Pi.single_eq_of_ne hrow, smul_zero]
      rw [hzeroRow, zero_mul, mul_zero]
    · have hcol : colSlot ≠ slot := by
        rw [← hrow]
        exact hne.symm
      have hzeroCol : (scale • (Pi.single slot 1 : Fin basisCount → ℝ))
          colSlot = 0 := by
        rw [Pi.smul_apply, Pi.single_eq_of_ne hcol, smul_zero]
      rw [hzeroCol, mul_zero, mul_zero]
  · rw [← hzero, zero_mul]

/-- The diagonal Gram package: the fold gives the diagonal witness. -/
theorem exists_diagonal_gram_of_parallel
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    {leftInv : Matrix (Fin basisCount) (Fin 6) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {gram : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * gram
        * (tightBasisColumns tightDir basisLabel)ᵀ
      = chartMultiplierAssembly activeSet activeWeight tightDir)
    (hpar : ∀ label ∈ activeSet, 0 < activeWeight label →
      ∃ (slot : Fin basisCount) (scale : ℝ),
        tightDir label = scale • tightDir (basisLabel slot)) :
    ∃ gramDiag : Fin basisCount → ℝ,
      gram = Matrix.diagonal gramDiag := by
  refine ⟨fun slot => gram slot slot, ?_⟩
  ext rowSlot colSlot
  rcases eq_or_ne rowSlot colSlot with rfl | hne
  · rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hne]
    exact gram_offdiag_eq_zero_of_parallel hdata hleft hHform hpar hne

/-! ## Layer 2 — the circuit residues and the router -/

/-- **THE RANK-FOUR CIRCUIT RESIDUE.**  A positive label parallel to no
basis column dies at every rank-four outer datum. -/
def RankFourOuterCircuitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
    (label : data.frame.activeIndex),
    label ∈ data.frame.activeSet →
    0 < data.frame.reducedWeight label →
    (∀ (slot : Fin 4) (scale : ℝ),
      data.frame.tightDir label
        ≠ scale • data.frame.tightDir (data.frame.basisLabel slot)) →
    False

/-- **THE RANK-FIVE CIRCUIT RESIDUE.** -/
def RankFiveOuterCircuitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFiveOuterData crux)
    (label : data.frame.activeIndex),
    label ∈ data.frame.activeSet →
    0 < data.frame.reducedWeight label →
    (∀ (slot : Fin 5) (scale : ℝ),
      data.frame.tightDir label
        ≠ scale • data.frame.tightDir (data.frame.basisLabel slot)) →
    False

/-- **THE RANK-SIX CIRCUIT RESIDUE.** -/
def RankSixOuterCircuitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankSixOuterData crux)
    (label : data.frame.activeIndex),
    label ∈ data.frame.activeSet →
    0 < data.frame.reducedWeight label →
    (∀ (slot : Fin 6) (scale : ℝ),
      data.frame.tightDir label
        ≠ scale • data.frame.tightDir (data.frame.basisLabel slot)) →
    False

/-- **THE ROUTER.**  A closed rank-four circuit residue makes every
positive label parallel to a basis column at every datum. -/
theorem RankFourOuterData.parallel_of_circuitClosed
    (hcirc : RankFourOuterCircuitClosed)
    {crux : SixThreeCrux} (data : RankFourOuterData crux) :
    ∀ label ∈ data.frame.activeSet, 0 < data.frame.reducedWeight label →
      ∃ (slot : Fin 4) (scale : ℝ),
        data.frame.tightDir label
          = scale • data.frame.tightDir (data.frame.basisLabel slot) := by
  intro label hmem hpos
  by_contra hnot
  push Not at hnot
  exact hcirc crux data label hmem hpos hnot

/-- The rank-five router. -/
theorem RankFiveOuterData.parallel_of_circuitClosed
    (hcirc : RankFiveOuterCircuitClosed)
    {crux : SixThreeCrux} (data : RankFiveOuterData crux) :
    ∀ label ∈ data.frame.activeSet, 0 < data.frame.reducedWeight label →
      ∃ (slot : Fin 5) (scale : ℝ),
        data.frame.tightDir label
          = scale • data.frame.tightDir (data.frame.basisLabel slot) := by
  intro label hmem hpos
  by_contra hnot
  push Not at hnot
  exact hcirc crux data label hmem hpos hnot

/-- The rank-six router. -/
theorem RankSixOuterData.parallel_of_circuitClosed
    (hcirc : RankSixOuterCircuitClosed)
    {crux : SixThreeCrux} (data : RankSixOuterData crux) :
    ∀ label ∈ data.frame.activeSet, 0 < data.frame.reducedWeight label →
      ∃ (slot : Fin 6) (scale : ℝ),
        data.frame.tightDir label
          = scale • data.frame.tightDir (data.frame.basisLabel slot) := by
  intro label hmem hpos
  by_contra hnot
  push Not at hnot
  exact hcirc crux data label hmem hpos hnot

/-! ## Layer 3 — the compositions at the datum -/

/-- **THE RANK-FOUR NARROWING AT THE DATUM.**  With the circuit residue
closed and interior shifted weights at every three-plus-carrier atom,
every atom of a rank-four outer datum carries exactly two blocks.  The
fold gives the diagonal Gram, and the pin branch dies at the refined
budget. -/
theorem RankFourOuterData.dense_of_circuitClosed_interior
    (hcirc : RankFourOuterCircuitClosed)
    {crux : SixThreeCrux} (data : RankFourOuterData crux)
    (hint : ∀ atomIndex : Fin 6,
      2 < (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomIndex).card →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    ∀ atomIndex : Fin 6,
      (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomIndex).card = 2 := by
  obtain ⟨gramDiag, hdiag⟩ := exists_diagonal_gram_of_parallel
    data.frame.hdata data.frame.hleft data.frame.hHform
    (data.parallel_of_circuitClosed hcirc)
  exact data.frame.dense_of_diagonal_gram hdiag hint

/-- **THE RANK-FIVE REFINED KILL AT THE DATUM.**  With the circuit
residue closed, a rank-five outer datum dies at any refined profile. -/
theorem RankFiveOuterData.false_of_circuitClosed_refined
    (hcirc : RankFiveOuterCircuitClosed)
    {crux : SixThreeCrux} (data : RankFiveOuterData crux)
    (pinSet pairSet : Finset (Fin 6)) (hdisjoint : Disjoint pinSet pairSet)
    (hpinSet : ∀ atom ∈ pinSet, ∃ pinSlot,
      blockCarrier data.frame.activeSubset data.frame.basisLabel atom
        = {pinSlot})
    (hpairSet : ∀ atom ∈ pairSet, ∃ slotOne slotTwo, slotOne ≠ slotTwo ∧
      blockCarrier data.frame.activeSubset data.frame.basisLabel atom
        = {slotOne, slotTwo})
    (hint : ∀ atom, atom ∉ pinSet → atom ∉ pairSet →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atom)
    (hprofileTwo : Matrix.trace data.frame.coeff = 2 → 1 ≤ pinSet.card)
    (hprofileThree : Matrix.trace data.frame.coeff = 3 →
      4 ≤ 2 * pinSet.card + pairSet.card) :
    False := by
  obtain ⟨gramDiag, hdiag⟩ := exists_diagonal_gram_of_parallel
    data.frame.hdata data.frame.hleft data.frame.hHform
    (data.parallel_of_circuitClosed hcirc)
  exact data.frame.false_of_diagonal_gram_refined hdiag pinSet pairSet
    hdisjoint hpinSet hpairSet hint hprofileTwo hprofileThree

/-- **THE RANK-SIX REFINED KILL AT THE DATUM.**  With the circuit
residue closed, a rank-six outer datum dies at profile mass four. -/
theorem RankSixOuterData.false_of_circuitClosed_refined
    (hcirc : RankSixOuterCircuitClosed)
    {crux : SixThreeCrux} (data : RankSixOuterData crux)
    (pinSet pairSet : Finset (Fin 6)) (hdisjoint : Disjoint pinSet pairSet)
    (hpinSet : ∀ atom ∈ pinSet, ∃ pinSlot,
      blockCarrier data.frame.activeSubset data.frame.basisLabel atom
        = {pinSlot})
    (hpairSet : ∀ atom ∈ pairSet, ∃ slotOne slotTwo, slotOne ≠ slotTwo ∧
      blockCarrier data.frame.activeSubset data.frame.basisLabel atom
        = {slotOne, slotTwo})
    (hint : ∀ atom, atom ∉ pinSet → atom ∉ pairSet →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atom)
    (hprofile : 4 ≤ 2 * pinSet.card + pairSet.card) :
    False := by
  obtain ⟨gramDiag, hdiag⟩ := exists_diagonal_gram_of_parallel
    data.frame.hdata data.frame.hleft data.frame.hHform
    (data.parallel_of_circuitClosed hcirc)
  exact data.frame.false_of_diagonal_gram_refined hdiag pinSet pairSet
    hdisjoint hpinSet hpairSet hint hprofile

end Gtz
