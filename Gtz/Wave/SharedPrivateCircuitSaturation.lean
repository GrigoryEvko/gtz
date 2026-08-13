import Gtz.Wave.SharedPrivateCircuitRankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The circuit saturation law — the rank-one gap block pays a unit budget

A singular shifted gap block gives an equation.  This module turns that
equation into an INEQUALITY, and the inequality is sharp.

The dictionary.  The chart is a symmetric idempotent, thus it contracts
every probe: `x · (P x) ≤ x · x`.  Write `d y := value + weight y` for the
captured diagonal and `A := P - diagonal d` for the shifted gap.  The
contraction reads `A ⪯ diagonal (1 - d)`, atom by atom, with no frame and
no basis.

The saturation.  On a set where the shifted gap block is a rank-one
square, the contraction has an EXACT extremal probe: the column of the
block divided by `1 - d`.  At that probe the contraction collapses to
`W * W ≤ A_UU * W` with `W` positive, thus the shifted diagonals pay a
unit budget:

  `Σ (gap y y - value) / (1 - d y) ≤ 1`.

Every term is positive, thus the plain sum obeys the same budget.  The
pair form needs one vanishing minor, the triple form needs three.

The row energy.  Symmetry plus idempotence give `Σ_z A y z ^ 2 =
P y y (1 - P y y)` off the diagonal.  On a rank-one triple two of those
squares are known products, thus the cross energy of the triple is capped
by one quarter.

The cover kill.  The whole shifted gap diagonal sums to `rank - 1 - size
* value`.  Two rank-one sets that cover every atom pay only two units
together, thus `rank <= 3 + size * value`, thus the chart value is
nonnegative.  Every kill target has a negative value, thus the six atoms
of a shared-private datum never carry two rank-one blocks that cover
them.  The identical branch already supplies one such block.

The readings.  The identical-support branch of a pair circuit carries a
rank-one triple, thus it pays the triple budget.  The dead-wedge branch
carries a support-two label on the two foreign atoms, thus it pays the
pair budget, and its two shared rows are parallel.  The four circuit
residues are restated with those payments in hand.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.sum_of_pair_support`, `Gtz.sum_of_triple_support` — the sparse sum
  readings.
* `Gtz.pairProbe`, `Gtz.tripleProbe` and their dot and `mulVec` readings.
* `Gtz.shiftedGapDiag`, `Gtz.projection_offDiag_eq_gap`,
  `Gtz.projection_diag_eq_shift` — **THE GAP DICTIONARY.**
* `Gtz.gapPairSingular_saturation`,
  `Gtz.gapPairSingular_shifted_sum_le_one` — **THE PAIR BUDGET.**
* `Gtz.projection_pair_contraction`, `Gtz.projection_triple_contraction` —
  the sparse contraction readings.
* `Gtz.pairBudget_core`, `Gtz.tripleBudget_core` — the division-free
  budget arithmetic.
* `Gtz.gapBlockRankOne_saturation`,
  `Gtz.gapBlockRankOne_shifted_sum_le_one` — **THE TRIPLE BUDGET.**
* `Gtz.projection_row_energy` — **THE ROW ENERGY LAW.**
* `Gtz.gapBlockRankOne_cross_energy_le` — **THE CROSS ENERGY CEILING.**
* `Gtz.SharedPrivateData.captureDiag_lt_one`,
  `Gtz.SharedPrivateData.identical_support_saturation`,
  `Gtz.SharedPrivateData.identical_support_shifted_sum_le_one`,
  `Gtz.SharedPrivateData.identical_support_cross_energy_le` — the
  identical branch payments.
* `Gtz.SharedPrivateData.pairCircuit_reconstruction`,
  `Gtz.SharedPrivateData.splitCircuit_label_pair_support`,
  `Gtz.SharedPrivateData.pairCircuit_gap_row_of_shared`,
  `Gtz.SharedPrivateData.splitCircuit_foreign_rows_parallel`,
  `Gtz.SharedPrivateData.splitCircuit_deadWedge_saturation`,
  `Gtz.SharedPrivateData.splitCircuit_deadWedge_shifted_sum_le_one` — the
  dead-wedge branch payments.
* `Gtz.shiftedGap`, `Gtz.shiftedGap_apply_diag`,
  `Gtz.shiftedGap_apply_offDiag`, `Gtz.projection_eq_shiftedGap_add` — the
  shifted gap matrix.
* `Gtz.setProbe`, `Gtz.setProbe_dotProduct`, `Gtz.setProbe_mulVec`,
  `Gtz.projection_set_contraction` — the contraction at a set probe.
* `Gtz.gapSet_saturation`, `Gtz.gapSet_shifted_sum_le_one` — **THE SET
  BUDGET AT EVERY SIZE.**
* `Gtz.shiftedGap_rankOne_of_gapBlockRankOne` — the triple bridge.
* `Gtz.shiftedGapDiag_sum_eq` — **THE SHIFTED GAP TOTAL.**
* `Gtz.rank_le_of_shiftedGap_rankOne_cover` — **THE TWO-SET COVER KILL.**
* `Gtz.SharedPrivateData.shiftedGapDiag_sum`,
  `Gtz.SharedPrivateData.false_of_shiftedGap_rankOne_cover`,
  `Gtz.SharedPrivateData.false_of_identical_support_complement_rankOne` —
  **THE IDENTICAL BRANCH DIES AGAINST A RANK-ONE COMPLEMENT.**
* `Gtz.SharedPrivateCircuitPairIdenticalSaturatedClosed`,
  `Gtz.SharedPrivateCircuitSplitPairSaturatedClosed` — the two paid
  residues.
* `Gtz.sharedPrivateCircuitPairIdenticalClosed_of_saturated`,
  `Gtz.sharedPrivateCircuitSplitPairClosed_of_saturated` — the payment
  bridges.
* `Gtz.sharedPrivateExtrasClosed_of_saturated_lattice`,
  `Gtz.sharedPrivateKilled_of_saturated_lattice`,
  `Gtz.rankFourSharedPrivateClosed_of_saturated_lattice`,
  `Gtz.rankFiveSharedPrivateClosed_of_saturated_lattice`,
  `Gtz.rankSixSharedPrivateClosed_of_saturated_lattice` — **CLOSURE TWO
  ON THE PAID RESIDUES.**

## Vacuity

The matrix statements are unconditional.  The datum statements quantify
over shared-private data, and no such datum exists if `Gtz.GtzWeighted 6 3`
holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — sparse probes and their readings -/

section SparseProbe

variable {size : ℕ}

/-- A sum whose summand vanishes off a pair collapses to two terms. -/
theorem sum_of_pair_support {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (summand : Fin size → ℝ)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      summand atomIndex = 0) :
    ∑ atomIndex : Fin size, summand atomIndex
      = summand atomU + summand atomV := by
  classical
  have hsub : ∑ atomIndex ∈ ({atomU, atomV} : Finset (Fin size)), summand atomIndex
      = ∑ atomIndex : Fin size, summand atomIndex := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro atomIndex _ hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    exact hsupp atomIndex hnot.1 hnot.2
  rw [← hsub, Finset.sum_pair hUV]

/-- A sum whose summand vanishes off a triple collapses to three terms. -/
theorem sum_of_triple_support {atomU atomV atomS : Fin size} (hUV : atomU ≠ atomV)
    (hUS : atomU ≠ atomS) (hVS : atomV ≠ atomS) (summand : Fin size → ℝ)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomS → summand atomIndex = 0) :
    ∑ atomIndex : Fin size, summand atomIndex
      = summand atomU + summand atomV + summand atomS := by
  classical
  have hsub : ∑ atomIndex ∈ ({atomU, atomV, atomS} : Finset (Fin size)),
      summand atomIndex = ∑ atomIndex : Fin size, summand atomIndex := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro atomIndex _ hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    exact hsupp atomIndex hnot.1 hnot.2.1 hnot.2.2
  have hnotMem : atomU ∉ ({atomV, atomS} : Finset (Fin size)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hUV, hUS⟩
  rw [← hsub, Finset.sum_insert hnotMem, Finset.sum_pair hVS, add_assoc]

/-- The two-atom probe. -/
noncomputable def pairProbe (atomU atomV : Fin size) (scaleU scaleV : ℝ) :
    Fin size → ℝ :=
  fun atomIndex =>
    if atomIndex = atomU then scaleU else if atomIndex = atomV then scaleV else 0

/-- The three-atom probe. -/
noncomputable def tripleProbe (atomU atomV atomS : Fin size)
    (scaleU scaleV scaleS : ℝ) : Fin size → ℝ :=
  fun atomIndex =>
    if atomIndex = atomU then scaleU
    else if atomIndex = atomV then scaleV
    else if atomIndex = atomS then scaleS else 0

variable {atomU atomV atomS : Fin size} {scaleU scaleV scaleS : ℝ}

theorem pairProbe_left : pairProbe atomU atomV scaleU scaleV atomU = scaleU := by
  rw [pairProbe, if_pos rfl]

theorem pairProbe_right (hUV : atomU ≠ atomV) :
    pairProbe atomU atomV scaleU scaleV atomV = scaleV := by
  rw [pairProbe, if_neg (Ne.symm hUV), if_pos rfl]

theorem pairProbe_off {atomIndex : Fin size} (hU : atomIndex ≠ atomU)
    (hV : atomIndex ≠ atomV) :
    pairProbe atomU atomV scaleU scaleV atomIndex = 0 := by
  rw [pairProbe, if_neg hU, if_neg hV]

theorem tripleProbe_first :
    tripleProbe atomU atomV atomS scaleU scaleV scaleS atomU = scaleU := by
  rw [tripleProbe, if_pos rfl]

theorem tripleProbe_second (hUV : atomU ≠ atomV) :
    tripleProbe atomU atomV atomS scaleU scaleV scaleS atomV = scaleV := by
  rw [tripleProbe, if_neg (Ne.symm hUV), if_pos rfl]

theorem tripleProbe_third (hUS : atomU ≠ atomS) (hVS : atomV ≠ atomS) :
    tripleProbe atomU atomV atomS scaleU scaleV scaleS atomS = scaleS := by
  rw [tripleProbe, if_neg (Ne.symm hUS), if_neg (Ne.symm hVS), if_pos rfl]

theorem tripleProbe_off {atomIndex : Fin size} (hU : atomIndex ≠ atomU)
    (hV : atomIndex ≠ atomV) (hS : atomIndex ≠ atomS) :
    tripleProbe atomU atomV atomS scaleU scaleV scaleS atomIndex = 0 := by
  rw [tripleProbe, if_neg hU, if_neg hV, if_neg hS]

/-- The dot product against a two-atom probe. -/
theorem pairProbe_dotProduct (hUV : atomU ≠ atomV) (other : Fin size → ℝ) :
    pairProbe atomU atomV scaleU scaleV ⬝ᵥ other
      = scaleU * other atomU + scaleV * other atomV := by
  rw [dotProduct, sum_of_pair_support hUV _
    (fun atomIndex hU hV => by rw [pairProbe_off hU hV, zero_mul]),
    pairProbe_left, pairProbe_right hUV]

/-- The matrix action on a two-atom probe. -/
theorem pairProbe_mulVec (hUV : atomU ≠ atomV)
    (matrixA : Matrix (Fin size) (Fin size) ℝ) (rowIndex : Fin size) :
    (matrixA *ᵥ pairProbe atomU atomV scaleU scaleV) rowIndex
      = matrixA rowIndex atomU * scaleU + matrixA rowIndex atomV * scaleV := by
  rw [Matrix.mulVec, dotProduct, sum_of_pair_support hUV _
    (fun atomIndex hU hV => by rw [pairProbe_off hU hV, mul_zero]),
    pairProbe_left, pairProbe_right hUV]

/-- The dot product against a three-atom probe. -/
theorem tripleProbe_dotProduct (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS) (other : Fin size → ℝ) :
    tripleProbe atomU atomV atomS scaleU scaleV scaleS ⬝ᵥ other
      = scaleU * other atomU + scaleV * other atomV + scaleS * other atomS := by
  rw [dotProduct, sum_of_triple_support hUV hUS hVS _
    (fun atomIndex hU hV hS => by rw [tripleProbe_off hU hV hS, zero_mul]),
    tripleProbe_first, tripleProbe_second hUV, tripleProbe_third hUS hVS]

/-- The matrix action on a three-atom probe. -/
theorem tripleProbe_mulVec (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS) (matrixA : Matrix (Fin size) (Fin size) ℝ)
    (rowIndex : Fin size) :
    (matrixA *ᵥ tripleProbe atomU atomV atomS scaleU scaleV scaleS) rowIndex
      = matrixA rowIndex atomU * scaleU + matrixA rowIndex atomV * scaleV
        + matrixA rowIndex atomS * scaleS := by
  rw [Matrix.mulVec, dotProduct, sum_of_triple_support hUV hUS hVS _
    (fun atomIndex hU hV hS => by rw [tripleProbe_off hU hV hS, mul_zero]),
    tripleProbe_first, tripleProbe_second hUV, tripleProbe_third hUS hVS]

end SparseProbe

/-! ## Layer 2 — the gap dictionary -/

section GapDictionary

variable {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
variable {weight : Fin size → ℝ} {value : ℝ}

/-- The shifted gap diagonal at an atom: the gap diagonal minus the chart
value.  It is the corner of the shifted gap block. -/
noncomputable def shiftedGapDiag (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (value : ℝ) (atomIndex : Fin size) : ℝ :=
  chartStationaryGap projection weight atomIndex atomIndex - value

/-- Off the diagonal the chart entry IS the gap entry. -/
theorem projection_offDiag_eq_gap {rowIndex colIndex : Fin size}
    (hne : rowIndex ≠ colIndex) :
    projection rowIndex colIndex
      = chartStationaryGap projection weight rowIndex colIndex := by
  rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hne, sub_zero]

/-- On the diagonal the chart entry is the shifted gap plus the captured
diagonal. -/
theorem projection_diag_eq_shift (atomIndex : Fin size) :
    projection atomIndex atomIndex
      = shiftedGapDiag projection weight value atomIndex
        + (value + weight atomIndex) := by
  rw [shiftedGapDiag, chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_eq]
  ring

/-- The entry symmetry of a symmetric chart, in the direction the readings
want. -/
theorem projection_symm_entry (hsymm : projectionᵀ = projection)
    (rowIndex colIndex : Fin size) :
    projection colIndex rowIndex = projection rowIndex colIndex :=
  congrFun (congrFun hsymm rowIndex) colIndex

end GapDictionary

/-! ## Layer 3 — the contraction readings and the budget cores -/

section Contraction

variable {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
variable {weight : Fin size → ℝ} {value : ℝ}

/-- **THE PAIR CONTRACTION.**  A symmetric idempotent chart contracts every
two-atom probe.  The reading uses the four chart entries of the pair. -/
theorem projection_pair_contraction (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV) (scaleU scaleV : ℝ) :
    projection atomU atomU * scaleU * scaleU
        + projection atomV atomV * scaleV * scaleV
        + 2 * (projection atomU atomV * scaleU * scaleV)
      ≤ scaleU * scaleU + scaleV * scaleV := by
  have hbase := dotProduct_mulVec_le_self_of_symmetricIdempotent hsymm hidem
    (pairProbe atomU atomV scaleU scaleV)
  have hleft : pairProbe atomU atomV scaleU scaleV
      ⬝ᵥ (projection *ᵥ pairProbe atomU atomV scaleU scaleV)
      = projection atomU atomU * scaleU * scaleU
        + projection atomV atomV * scaleV * scaleV
        + 2 * (projection atomU atomV * scaleU * scaleV) := by
    rw [pairProbe_dotProduct hUV, pairProbe_mulVec hUV, pairProbe_mulVec hUV,
      projection_symm_entry hsymm atomU atomV]
    ring
  have hright : pairProbe atomU atomV scaleU scaleV ⬝ᵥ pairProbe atomU atomV scaleU scaleV
      = scaleU * scaleU + scaleV * scaleV := by
    rw [pairProbe_dotProduct hUV, pairProbe_left, pairProbe_right hUV]
  rw [hleft, hright] at hbase
  exact hbase

/-- **THE TRIPLE CONTRACTION.**  The same reading on three atoms. -/
theorem projection_triple_contraction (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    {atomU atomV atomS : Fin size} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS) (scaleU scaleV scaleS : ℝ) :
    projection atomU atomU * scaleU * scaleU
        + projection atomV atomV * scaleV * scaleV
        + projection atomS atomS * scaleS * scaleS
        + 2 * (projection atomU atomV * scaleU * scaleV)
        + 2 * (projection atomU atomS * scaleU * scaleS)
        + 2 * (projection atomV atomS * scaleV * scaleS)
      ≤ scaleU * scaleU + scaleV * scaleV + scaleS * scaleS := by
  have hbase := dotProduct_mulVec_le_self_of_symmetricIdempotent hsymm hidem
    (tripleProbe atomU atomV atomS scaleU scaleV scaleS)
  have hleft : tripleProbe atomU atomV atomS scaleU scaleV scaleS
      ⬝ᵥ (projection *ᵥ tripleProbe atomU atomV atomS scaleU scaleV scaleS)
      = projection atomU atomU * scaleU * scaleU
        + projection atomV atomV * scaleV * scaleV
        + projection atomS atomS * scaleS * scaleS
        + 2 * (projection atomU atomV * scaleU * scaleV)
        + 2 * (projection atomU atomS * scaleU * scaleS)
        + 2 * (projection atomV atomS * scaleV * scaleS) := by
    rw [tripleProbe_dotProduct hUV hUS hVS, tripleProbe_mulVec hUV hUS hVS,
      tripleProbe_mulVec hUV hUS hVS, tripleProbe_mulVec hUV hUS hVS,
      projection_symm_entry hsymm atomU atomV, projection_symm_entry hsymm atomU atomS,
      projection_symm_entry hsymm atomV atomS]
    ring
  have hright : tripleProbe atomU atomV atomS scaleU scaleV scaleS
      ⬝ᵥ tripleProbe atomU atomV atomS scaleU scaleV scaleS
      = scaleU * scaleU + scaleV * scaleV + scaleS * scaleS := by
    rw [tripleProbe_dotProduct hUV hUS hVS, tripleProbe_first, tripleProbe_second hUV,
      tripleProbe_third hUS hVS]
  rw [hleft, hright] at hbase
  exact hbase

end Contraction

section BudgetCore

/-- **THE PAIR BUDGET CORE.**  Division-free arithmetic: a singular block
with a positive corner and the contraction at the extremal probe pay a
budget of one corner. -/
theorem pairBudget_core {cornerU cornerV crossUV diagU diagV captureU captureV
    scaleU scaleV : ℝ}
    (hcapU : captureU < 1) (hcapV : captureV < 1)
    (hposU : 0 < cornerU) (hposV : 0 < cornerV)
    (hdiagU : diagU = cornerU + captureU) (hdiagV : diagV = cornerV + captureV)
    (hminorUV : crossUV * crossUV = cornerU * cornerV)
    (hscaleU : (1 - captureU) * scaleU = cornerU)
    (hscaleV : (1 - captureV) * scaleV = crossUV)
    (hcontract : diagU * scaleU * scaleU + diagV * scaleV * scaleV
        + 2 * (crossUV * scaleU * scaleV)
      ≤ scaleU * scaleU + scaleV * scaleV) :
    cornerU * scaleU + crossUV * scaleV ≤ cornerU := by
  have hdefU : (0 : ℝ) < 1 - captureU := by linarith
  have hdefV : (0 : ℝ) < 1 - captureV := by linarith
  rw [hdiagU, hdiagV] at hcontract
  have hbudget : (1 - captureU) * (scaleU * scaleU) + (1 - captureV) * (scaleV * scaleV)
      = cornerU * scaleU + crossUV * scaleV := by
    rw [← hscaleU, ← hscaleV]; ring
  have hform : cornerU * scaleU * scaleU + cornerV * scaleV * scaleV
      + 2 * (crossUV * scaleU * scaleV) ≤ cornerU * scaleU + crossUV * scaleV := by
    rw [← hbudget]; linarith [hcontract]
  have hquad : cornerU * (cornerU * scaleU * scaleU + cornerV * scaleV * scaleV
      + 2 * (crossUV * scaleU * scaleV))
      = (cornerU * scaleU + crossUV * scaleV) * (cornerU * scaleU + crossUV * scaleV) := by
    linear_combination (-(scaleV * scaleV)) * hminorUV
  have hfirst : 0 < cornerU * scaleU := by
    have hscalePos : 0 < scaleU := by nlinarith [hscaleU, hposU, hdefU]
    exact mul_pos hposU hscalePos
  have hsecond : 0 < crossUV * scaleV := by
    have hval : (1 - captureV) * (crossUV * scaleV) = cornerU * cornerV := by
      rw [mul_comm crossUV scaleV, ← mul_assoc, hscaleV]; exact hminorUV
    nlinarith [hval, mul_pos hposU hposV, hdefV]
  have htotalPos : 0 < cornerU * scaleU + crossUV * scaleV := by linarith
  have hsq : (cornerU * scaleU + crossUV * scaleV) * (cornerU * scaleU + crossUV * scaleV)
      ≤ cornerU * (cornerU * scaleU + crossUV * scaleV) := by
    rw [← hquad]; exact mul_le_mul_of_nonneg_left hform (le_of_lt hposU)
  by_contra hcontra
  rw [not_le] at hcontra
  nlinarith [hsq, htotalPos, hcontra]

/-- **THE TRIPLE BUDGET CORE.**  The same arithmetic on three atoms.  The
cross equation of the rank-one block is the only extra input. -/
theorem tripleBudget_core {cornerU cornerV cornerS crossUV crossUS crossVS
    diagU diagV diagS captureU captureV captureS scaleU scaleV scaleS : ℝ}
    (hcapU : captureU < 1) (hcapV : captureV < 1) (hcapS : captureS < 1)
    (hposU : 0 < cornerU) (hposV : 0 < cornerV) (hposS : 0 < cornerS)
    (hdiagU : diagU = cornerU + captureU) (hdiagV : diagV = cornerV + captureV)
    (hdiagS : diagS = cornerS + captureS)
    (hminorUV : crossUV * crossUV = cornerU * cornerV)
    (hminorUS : crossUS * crossUS = cornerU * cornerS)
    (hcross : cornerU * crossVS = crossUV * crossUS)
    (hscaleU : (1 - captureU) * scaleU = cornerU)
    (hscaleV : (1 - captureV) * scaleV = crossUV)
    (hscaleS : (1 - captureS) * scaleS = crossUS)
    (hcontract : diagU * scaleU * scaleU + diagV * scaleV * scaleV
        + diagS * scaleS * scaleS + 2 * (crossUV * scaleU * scaleV)
        + 2 * (crossUS * scaleU * scaleS) + 2 * (crossVS * scaleV * scaleS)
      ≤ scaleU * scaleU + scaleV * scaleV + scaleS * scaleS) :
    cornerU * scaleU + crossUV * scaleV + crossUS * scaleS ≤ cornerU := by
  have hdefU : (0 : ℝ) < 1 - captureU := by linarith
  have hdefV : (0 : ℝ) < 1 - captureV := by linarith
  have hdefS : (0 : ℝ) < 1 - captureS := by linarith
  rw [hdiagU, hdiagV, hdiagS] at hcontract
  have hbudget : (1 - captureU) * (scaleU * scaleU) + (1 - captureV) * (scaleV * scaleV)
      + (1 - captureS) * (scaleS * scaleS)
      = cornerU * scaleU + crossUV * scaleV + crossUS * scaleS := by
    rw [← hscaleU, ← hscaleV, ← hscaleS]; ring
  have hform : cornerU * scaleU * scaleU + cornerV * scaleV * scaleV
      + cornerS * scaleS * scaleS + 2 * (crossUV * scaleU * scaleV)
      + 2 * (crossUS * scaleU * scaleS) + 2 * (crossVS * scaleV * scaleS)
      ≤ cornerU * scaleU + crossUV * scaleV + crossUS * scaleS := by
    rw [← hbudget]; linarith [hcontract]
  have hquad : cornerU * (cornerU * scaleU * scaleU + cornerV * scaleV * scaleV
      + cornerS * scaleS * scaleS + 2 * (crossUV * scaleU * scaleV)
      + 2 * (crossUS * scaleU * scaleS) + 2 * (crossVS * scaleV * scaleS))
      = (cornerU * scaleU + crossUV * scaleV + crossUS * scaleS)
        * (cornerU * scaleU + crossUV * scaleV + crossUS * scaleS) := by
    linear_combination (-(scaleV * scaleV)) * hminorUV + (-(scaleS * scaleS)) * hminorUS
      + (2 * scaleV * scaleS) * hcross
  have hfirst : 0 < cornerU * scaleU := by
    have hscalePos : 0 < scaleU := by nlinarith [hscaleU, hposU, hdefU]
    exact mul_pos hposU hscalePos
  have hsecond : 0 < crossUV * scaleV := by
    have hval : (1 - captureV) * (crossUV * scaleV) = cornerU * cornerV := by
      rw [mul_comm crossUV scaleV, ← mul_assoc, hscaleV]; exact hminorUV
    nlinarith [hval, mul_pos hposU hposV, hdefV]
  have hthird : 0 < crossUS * scaleS := by
    have hval : (1 - captureS) * (crossUS * scaleS) = cornerU * cornerS := by
      rw [mul_comm crossUS scaleS, ← mul_assoc, hscaleS]; exact hminorUS
    nlinarith [hval, mul_pos hposU hposS, hdefS]
  have htotalPos : 0 < cornerU * scaleU + crossUV * scaleV + crossUS * scaleS := by
    linarith
  have hsq : (cornerU * scaleU + crossUV * scaleV + crossUS * scaleS)
      * (cornerU * scaleU + crossUV * scaleV + crossUS * scaleS)
      ≤ cornerU * (cornerU * scaleU + crossUV * scaleV + crossUS * scaleS) := by
    rw [← hquad]; exact mul_le_mul_of_nonneg_left hform (le_of_lt hposU)
  by_contra hcontra
  rw [not_le] at hcontra
  nlinarith [hsq, htotalPos, hcontra]

end BudgetCore

/-! ## Layer 4 — the saturation laws -/

section Saturation

variable {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
variable {weight : Fin size → ℝ} {value : ℝ}

/-- **THE PAIR BUDGET.**  A singular shifted gap block on two atoms with a
positive shifted diagonal pays a unit budget: the two shifted diagonals,
each divided by the captured defect, sum to at most one. -/
theorem gapPairSingular_saturation (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hcapU : value + weight atomU < 1) (hcapV : value + weight atomV < 1)
    (hposU : 0 < shiftedGapDiag projection weight value atomU)
    (hposV : 0 < shiftedGapDiag projection weight value atomV)
    (hminor : chartStationaryGap projection weight atomU atomV
        * chartStationaryGap projection weight atomU atomV
      = (chartStationaryGap projection weight atomU atomU - value)
        * (chartStationaryGap projection weight atomV atomV - value)) :
    shiftedGapDiag projection weight value atomU / (1 - (value + weight atomU))
      + shiftedGapDiag projection weight value atomV / (1 - (value + weight atomV))
      ≤ 1 := by
  have hdefU : (0 : ℝ) < 1 - (value + weight atomU) := by linarith
  have hdefV : (0 : ℝ) < 1 - (value + weight atomV) := by linarith
  have hscaleU : (1 - (value + weight atomU))
      * (shiftedGapDiag projection weight value atomU / (1 - (value + weight atomU)))
      = shiftedGapDiag projection weight value atomU := by
    field_simp
  have hscaleV : (1 - (value + weight atomV))
      * (chartStationaryGap projection weight atomU atomV / (1 - (value + weight atomV)))
      = chartStationaryGap projection weight atomU atomV := by
    field_simp
  have hcore := pairBudget_core hcapU hcapV hposU hposV
    (projection_diag_eq_shift (projection := projection) (weight := weight)
      (value := value) atomU)
    (projection_diag_eq_shift (projection := projection) (weight := weight)
      (value := value) atomV)
    hminor hscaleU hscaleV
    (by
      have hbase := projection_pair_contraction hsymm hidem hUV
        (shiftedGapDiag projection weight value atomU / (1 - (value + weight atomU)))
        (chartStationaryGap projection weight atomU atomV / (1 - (value + weight atomV)))
      rwa [projection_offDiag_eq_gap (projection := projection) (weight := weight) hUV] at hbase)
  -- turn the division-free budget into the stated sum
  have hsecond : chartStationaryGap projection weight atomU atomV
      * (chartStationaryGap projection weight atomU atomV / (1 - (value + weight atomV)))
      = shiftedGapDiag projection weight value atomU
        * (shiftedGapDiag projection weight value atomV / (1 - (value + weight atomV))) := by
    rw [shiftedGapDiag, shiftedGapDiag]
    field_simp
    linear_combination hminor
  rw [hsecond] at hcore
  have hfinal : shiftedGapDiag projection weight value atomU
      * (shiftedGapDiag projection weight value atomU / (1 - (value + weight atomU))
        + shiftedGapDiag projection weight value atomV / (1 - (value + weight atomV)))
      ≤ shiftedGapDiag projection weight value atomU * 1 := by
    rw [mul_one, mul_add]; linarith [hcore]
  exact le_of_mul_le_mul_left hfinal hposU

/-- The plain pair budget: the captured defect never exceeds one, thus
dropping it only weakens the bound. -/
theorem gapPairSingular_shifted_sum_le_one (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hfloorU : 0 ≤ value + weight atomU) (hfloorV : 0 ≤ value + weight atomV)
    (hcapU : value + weight atomU < 1) (hcapV : value + weight atomV < 1)
    (hposU : 0 < shiftedGapDiag projection weight value atomU)
    (hposV : 0 < shiftedGapDiag projection weight value atomV)
    (hminor : chartStationaryGap projection weight atomU atomV
        * chartStationaryGap projection weight atomU atomV
      = (chartStationaryGap projection weight atomU atomU - value)
        * (chartStationaryGap projection weight atomV atomV - value)) :
    shiftedGapDiag projection weight value atomU
      + shiftedGapDiag projection weight value atomV ≤ 1 := by
  have hsat := gapPairSingular_saturation hsymm hidem hUV hcapU hcapV hposU hposV hminor
  have hdefU : (0 : ℝ) < 1 - (value + weight atomU) := by linarith
  have hdefV : (0 : ℝ) < 1 - (value + weight atomV) := by linarith
  have hgrowU : shiftedGapDiag projection weight value atomU
      ≤ shiftedGapDiag projection weight value atomU / (1 - (value + weight atomU)) := by
    rw [le_div_iff₀ hdefU]; nlinarith [hposU, hfloorU]
  have hgrowV : shiftedGapDiag projection weight value atomV
      ≤ shiftedGapDiag projection weight value atomV / (1 - (value + weight atomV)) := by
    rw [le_div_iff₀ hdefV]; nlinarith [hposV, hfloorV]
  linarith

/-- **THE TRIPLE BUDGET.**  A rank-one shifted gap block on three atoms
with a positive shifted diagonal pays a unit budget.  The cross equation of
the block is one of the six vanishing minors, thus no sign hypothesis is
necessary. -/
theorem gapBlockRankOne_saturation (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    {atomU atomV atomS : Fin size} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hcapU : value + weight atomU < 1) (hcapV : value + weight atomV < 1)
    (hcapS : value + weight atomS < 1)
    (hposU : 0 < shiftedGapDiag projection weight value atomU)
    (hposV : 0 < shiftedGapDiag projection weight value atomV)
    (hposS : 0 < shiftedGapDiag projection weight value atomS)
    (hshape : GapBlockRankOne projection weight value atomU atomV atomS) :
    shiftedGapDiag projection weight value atomU / (1 - (value + weight atomU))
      + shiftedGapDiag projection weight value atomV / (1 - (value + weight atomV))
      + shiftedGapDiag projection weight value atomS / (1 - (value + weight atomS))
      ≤ 1 := by
  obtain ⟨hminorUV, hminorUS, _, hcross, _, _⟩ := hshape
  have hdefU : (0 : ℝ) < 1 - (value + weight atomU) := by linarith
  have hdefV : (0 : ℝ) < 1 - (value + weight atomV) := by linarith
  have hdefS : (0 : ℝ) < 1 - (value + weight atomS) := by linarith
  have hscaleU : (1 - (value + weight atomU))
      * (shiftedGapDiag projection weight value atomU / (1 - (value + weight atomU)))
      = shiftedGapDiag projection weight value atomU := by field_simp
  have hscaleV : (1 - (value + weight atomV))
      * (chartStationaryGap projection weight atomU atomV / (1 - (value + weight atomV)))
      = chartStationaryGap projection weight atomU atomV := by field_simp
  have hscaleS : (1 - (value + weight atomS))
      * (chartStationaryGap projection weight atomU atomS / (1 - (value + weight atomS)))
      = chartStationaryGap projection weight atomU atomS := by field_simp
  have hcore := tripleBudget_core hcapU hcapV hcapS hposU hposV hposS
    (projection_diag_eq_shift (projection := projection) (weight := weight)
      (value := value) atomU)
    (projection_diag_eq_shift (projection := projection) (weight := weight)
      (value := value) atomV)
    (projection_diag_eq_shift (projection := projection) (weight := weight)
      (value := value) atomS)
    hminorUV hminorUS hcross hscaleU hscaleV hscaleS
    (by
      have hbase := projection_triple_contraction hsymm hidem hUV hUS hVS
        (shiftedGapDiag projection weight value atomU / (1 - (value + weight atomU)))
        (chartStationaryGap projection weight atomU atomV / (1 - (value + weight atomV)))
        (chartStationaryGap projection weight atomU atomS / (1 - (value + weight atomS)))
      rwa [projection_offDiag_eq_gap (projection := projection) (weight := weight) hUV,
        projection_offDiag_eq_gap (projection := projection) (weight := weight) hUS,
        projection_offDiag_eq_gap (projection := projection) (weight := weight) hVS] at hbase)
  have hsecond : chartStationaryGap projection weight atomU atomV
      * (chartStationaryGap projection weight atomU atomV / (1 - (value + weight atomV)))
      = shiftedGapDiag projection weight value atomU
        * (shiftedGapDiag projection weight value atomV
          / (1 - (value + weight atomV))) := by
    rw [shiftedGapDiag, shiftedGapDiag]
    field_simp
    linear_combination hminorUV
  have hthird : chartStationaryGap projection weight atomU atomS
      * (chartStationaryGap projection weight atomU atomS / (1 - (value + weight atomS)))
      = shiftedGapDiag projection weight value atomU
        * (shiftedGapDiag projection weight value atomS
          / (1 - (value + weight atomS))) := by
    rw [shiftedGapDiag, shiftedGapDiag]
    field_simp
    linear_combination hminorUS
  rw [hsecond, hthird] at hcore
  have hfinal : shiftedGapDiag projection weight value atomU
      * (shiftedGapDiag projection weight value atomU / (1 - (value + weight atomU))
        + shiftedGapDiag projection weight value atomV / (1 - (value + weight atomV))
        + shiftedGapDiag projection weight value atomS / (1 - (value + weight atomS)))
      ≤ shiftedGapDiag projection weight value atomU * 1 := by
    rw [mul_one, mul_add, mul_add]; linarith [hcore]
  exact le_of_mul_le_mul_left hfinal hposU

/-- The plain triple budget. -/
theorem gapBlockRankOne_shifted_sum_le_one (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    {atomU atomV atomS : Fin size} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hfloorU : 0 ≤ value + weight atomU) (hfloorV : 0 ≤ value + weight atomV)
    (hfloorS : 0 ≤ value + weight atomS)
    (hcapU : value + weight atomU < 1) (hcapV : value + weight atomV < 1)
    (hcapS : value + weight atomS < 1)
    (hposU : 0 < shiftedGapDiag projection weight value atomU)
    (hposV : 0 < shiftedGapDiag projection weight value atomV)
    (hposS : 0 < shiftedGapDiag projection weight value atomS)
    (hshape : GapBlockRankOne projection weight value atomU atomV atomS) :
    shiftedGapDiag projection weight value atomU
      + shiftedGapDiag projection weight value atomV
      + shiftedGapDiag projection weight value atomS ≤ 1 := by
  have hsat := gapBlockRankOne_saturation hsymm hidem hUV hUS hVS hcapU hcapV hcapS
    hposU hposV hposS hshape
  have hdefU : (0 : ℝ) < 1 - (value + weight atomU) := by linarith
  have hdefV : (0 : ℝ) < 1 - (value + weight atomV) := by linarith
  have hdefS : (0 : ℝ) < 1 - (value + weight atomS) := by linarith
  have hgrowU : shiftedGapDiag projection weight value atomU
      ≤ shiftedGapDiag projection weight value atomU / (1 - (value + weight atomU)) := by
    rw [le_div_iff₀ hdefU]; nlinarith [hposU, hfloorU]
  have hgrowV : shiftedGapDiag projection weight value atomV
      ≤ shiftedGapDiag projection weight value atomV / (1 - (value + weight atomV)) := by
    rw [le_div_iff₀ hdefV]; nlinarith [hposV, hfloorV]
  have hgrowS : shiftedGapDiag projection weight value atomS
      ≤ shiftedGapDiag projection weight value atomS / (1 - (value + weight atomS)) := by
    rw [le_div_iff₀ hdefS]; nlinarith [hposS, hfloorS]
  linarith

end Saturation

/-! ## Layer 4 — the row energy law and the cross energy ceiling -/

section RowEnergy

variable {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
variable {weight : Fin size → ℝ} {value : ℝ}

/-- **THE ROW ENERGY LAW.**  The off-diagonal energy of a chart row is the
diagonal entry times its own defect.  Symmetry turns the idempotent read
into a sum of squares, and the diagonal term peels off. -/
theorem projection_row_energy (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection) (rowIndex : Fin size) :
    ∑ colIndex ∈ Finset.univ.erase rowIndex,
        projection rowIndex colIndex * projection rowIndex colIndex
      = projection rowIndex rowIndex * (1 - projection rowIndex rowIndex) := by
  classical
  have hidemEntry : ∑ colIndex : Fin size,
      projection rowIndex colIndex * projection colIndex rowIndex
      = projection rowIndex rowIndex := by
    have hentry := congrFun (congrFun hidem rowIndex) rowIndex
    rwa [Matrix.mul_apply] at hentry
  have hsquares : ∑ colIndex : Fin size,
      projection rowIndex colIndex * projection rowIndex colIndex
      = projection rowIndex rowIndex := by
    rw [← hidemEntry]
    exact Finset.sum_congr rfl fun colIndex _ => by
      rw [projection_symm_entry hsymm rowIndex colIndex]
  have hpeel := Finset.add_sum_erase Finset.univ
    (fun colIndex => projection rowIndex colIndex * projection rowIndex colIndex)
    (Finset.mem_univ rowIndex)
  rw [hsquares] at hpeel
  linarith [hpeel]

/-- **THE CROSS ENERGY CEILING.**  On a rank-one shifted gap block the two
known off-diagonal squares are products of shifted diagonals, thus the
first corner times the sum of the other two never exceeds one quarter. -/
theorem gapBlockRankOne_cross_energy_le (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    {atomU atomV atomS : Fin size} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hshape : GapBlockRankOne projection weight value atomU atomV atomS) :
    shiftedGapDiag projection weight value atomU
        * (shiftedGapDiag projection weight value atomV
          + shiftedGapDiag projection weight value atomS)
      ≤ 1 / 4 := by
  classical
  obtain ⟨hminorUV, hminorUS, _⟩ := hshape
  have hsubset : ({atomV, atomS} : Finset (Fin size)) ⊆ Finset.univ.erase atomU := by
    intro atomIndex hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    rcases hmem with hV | hS
    · rw [hV]; exact Ne.symm hUV
    · rw [hS]; exact Ne.symm hUS
  have hpartial : ∑ colIndex ∈ ({atomV, atomS} : Finset (Fin size)),
      projection atomU colIndex * projection atomU colIndex
      ≤ ∑ colIndex ∈ Finset.univ.erase atomU,
        projection atomU colIndex * projection atomU colIndex :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun colIndex _ _ => mul_self_nonneg _)
  rw [Finset.sum_pair hVS,
    projection_offDiag_eq_gap (projection := projection) (weight := weight) hUV,
    projection_offDiag_eq_gap (projection := projection) (weight := weight) hUS,
    hminorUV, hminorUS, projection_row_energy hsymm hidem atomU] at hpartial
  simp only [shiftedGapDiag]
  nlinarith [hpartial, sq_nonneg (projection atomU atomU - 1 / 2)]

end RowEnergy

/-! ## Layer 5 — the datum payments -/

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-- The captured diagonal of a shared-private datum is less than one. -/
theorem captureDiag_lt_one (data : SharedPrivateData crux) (atomIndex : Fin 6) :
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex < 1 :=
  capture_diagonal_lt_one_of_negative_value data.hdata data.hvalueNeg atomIndex

/-- The captured diagonal of a shared-private datum is nonnegative. -/
theorem captureDiag_nonneg (data : SharedPrivateData crux) (atomIndex : Fin 6) :
    0 ≤ chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex :=
  capture_diagonal_nonneg_of_isChartStationaryData data.hdata atomIndex

/-- The shifted gap diagonal of a shared-private datum is positive. -/
theorem shiftedGapDiag_pos (data : SharedPrivateData crux) (atomIndex : Fin 6) :
    0 < shiftedGapDiag (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) atomIndex :=
  data.shiftedGap_diag_pos atomIndex

/-- **THE IDENTICAL BRANCH PAYS THE TRIPLE BUDGET.**  Two basis slots with
one support give a rank-one shifted gap block, and the block pays. -/
theorem identical_support_saturation (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomU atomV atomS : Fin 6} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS}) :
    shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomU
      / (1 - (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomU))
    + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomV
      / (1 - (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomV))
    + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomS
      / (1 - (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomS))
      ≤ 1 :=
  gapBlockRankOne_saturation data.hdata.isSymmetric data.hdata.isIdempotent hUV hUS hVS
    (data.captureDiag_lt_one atomU) (data.captureDiag_lt_one atomV)
    (data.captureDiag_lt_one atomS) (data.shiftedGapDiag_pos atomU)
    (data.shiftedGapDiag_pos atomV) (data.shiftedGapDiag_pos atomS)
    (data.gapBlockRankOne_of_identical_support hne hUV hUS hVS hsupportOne hsupportTwo)

/-- The plain triple budget at a shared triple. -/
theorem identical_support_shifted_sum_le_one (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomU atomV atomS : Fin 6} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS}) :
    shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomU
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomV
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomS ≤ 1 :=
  gapBlockRankOne_shifted_sum_le_one data.hdata.isSymmetric data.hdata.isIdempotent
    hUV hUS hVS (data.captureDiag_nonneg atomU) (data.captureDiag_nonneg atomV)
    (data.captureDiag_nonneg atomS) (data.captureDiag_lt_one atomU)
    (data.captureDiag_lt_one atomV) (data.captureDiag_lt_one atomS)
    (data.shiftedGapDiag_pos atomU) (data.shiftedGapDiag_pos atomV)
    (data.shiftedGapDiag_pos atomS)
    (data.gapBlockRankOne_of_identical_support hne hUV hUS hVS hsupportOne hsupportTwo)

/-- The cross energy ceiling at a shared triple. -/
theorem identical_support_cross_energy_le (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomU atomV atomS : Fin 6} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS}) :
    shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomU
      * (shiftedGapDiag (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design)) atomV
        + shiftedGapDiag (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design)) atomS)
      ≤ 1 / 4 :=
  gapBlockRankOne_cross_energy_le data.hdata.isSymmetric data.hdata.isIdempotent
    hUV hUS hVS
    (data.gapBlockRankOne_of_identical_support hne hUV hUS hVS hsupportOne hsupportTwo)

/-! ## Layer 7 — the dead-wedge branch payments -/

/-- The reconstruction of a pair circuit collapses to its two live
slots. -/
theorem pairCircuit_reconstruction (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    (hpos : 0 < data.reducedWeight label)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hpair : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      data.labelCoeff label slot = 0) (atomIndex : Fin 6) :
    data.tightDir label atomIndex
      = data.labelCoeff label slotOne
          * data.tightDir (data.basisLabel slotOne) atomIndex
        + data.labelCoeff label slotTwo
          * data.tightDir (data.basisLabel slotTwo) atomIndex := by
  classical
  rw [data.reconstruction_apply hmem hpos atomIndex]
  exact sum_of_pair_support hne _
    (fun slot hone htwo => by rw [hpair slot hone htwo, zero_mul])

/-- **THE DEAD-WEDGE LABEL IS A SUPPORT-TWO LABEL.**  When the circuit
label dies at the two shared atoms, its support is exactly the two foreign
atoms, and it is alive at each of them. -/
theorem splitCircuit_label_pair_support (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    (hpos : 0 < data.reducedWeight label)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hcoeffOne : data.labelCoeff label slotOne ≠ 0)
    (hcoeffTwo : data.labelCoeff label slotTwo ≠ 0)
    (hpair : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      data.labelCoeff label slot = 0)
    {atomA atomB atomX atomY : Fin 6}
    (_hAB : atomA ≠ atomB) (hAX : atomA ≠ atomX) (hAY : atomA ≠ atomY)
    (hBX : atomB ≠ atomX) (hBY : atomB ≠ atomY) (hXY : atomX ≠ atomY)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomA, atomB, atomX})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomA, atomB, atomY})
    (hdeadA : data.tightDir label atomA = 0)
    (hdeadB : data.tightDir label atomB = 0) :
    (∀ atomIndex, atomIndex ≠ atomX → atomIndex ≠ atomY →
        data.tightDir label atomIndex = 0)
      ∧ data.tightDir label atomX ≠ 0 ∧ data.tightDir label atomY ≠ 0 := by
  classical
  have hliveOneX : data.tightDir (data.basisLabel slotOne) atomX ≠ 0 :=
    data.basis_live_of_mem_support (by rw [hsupportOne]; simp)
  have hliveTwoY : data.tightDir (data.basisLabel slotTwo) atomY ≠ 0 :=
    data.basis_live_of_mem_support (by rw [hsupportTwo]; simp)
  have hdeadTwoX : data.tightDir (data.basisLabel slotTwo) atomX = 0 :=
    data.basis_dead_of_notMem_support
      (by rw [hsupportTwo]; simp [Ne.symm hAX, Ne.symm hBX, hXY])
  have hdeadOneY : data.tightDir (data.basisLabel slotOne) atomY = 0 :=
    data.basis_dead_of_notMem_support
      (by rw [hsupportOne]; simp [Ne.symm hAY, Ne.symm hBY, Ne.symm hXY])
  refine ⟨?_, ?_, ?_⟩
  · intro atomIndex hX hY
    by_cases hA : atomIndex = atomA
    · rw [hA]; exact hdeadA
    by_cases hB : atomIndex = atomB
    · rw [hB]; exact hdeadB
    have hzeroOne : data.tightDir (data.basisLabel slotOne) atomIndex = 0 :=
      data.basis_dead_of_notMem_support (by rw [hsupportOne]; simp [hA, hB, hX])
    have hzeroTwo : data.tightDir (data.basisLabel slotTwo) atomIndex = 0 :=
      data.basis_dead_of_notMem_support (by rw [hsupportTwo]; simp [hA, hB, hY])
    rw [data.pairCircuit_reconstruction hmem hpos hne hpair atomIndex, hzeroOne,
      hzeroTwo, mul_zero, mul_zero, add_zero]
  · rw [data.pairCircuit_reconstruction hmem hpos hne hpair atomX, hdeadTwoX,
      mul_zero, add_zero]
    exact mul_ne_zero hcoeffOne hliveOneX
  · rw [data.pairCircuit_reconstruction hmem hpos hne hpair atomY, hdeadOneY,
      mul_zero, zero_add]
    exact mul_ne_zero hcoeffTwo hliveTwoY

/-- **THE SHARED ROW OF A PAIR CIRCUIT.**  At an atom that both live blocks
carry, the chart gap row of the circuit label reads the label value.  When
the label dies there, the row vanishes. -/
theorem pairCircuit_gap_row_of_shared (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    (hpos : 0 < data.reducedWeight label)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hpair : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      data.labelCoeff label slot = 0)
    {atomShared : Fin 6}
    (hmemOne : atomShared ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hmemTwo : atomShared ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo)) :
    (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight *ᵥ data.tightDir label) atomShared
      = chartObjective (chartPointOfDesign crux.design)
        * data.tightDir label atomShared := by
  classical
  have htightOne := data.hdata.tightDir_isTight (data.basisLabel slotOne)
    (data.basisLabel_mem_activeSet slotOne) atomShared
    (by rw [data.basisBlock_eq_support slotOne]; exact hmemOne)
  have htightTwo := data.hdata.tightDir_isTight (data.basisLabel slotTwo)
    (data.basisLabel_mem_activeSet slotTwo) atomShared
    (by rw [data.basisBlock_eq_support slotTwo]; exact hmemTwo)
  have hexpand : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight *ᵥ data.tightDir label) atomShared
      = data.labelCoeff label slotOne
          * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            *ᵥ data.tightDir (data.basisLabel slotOne)) atomShared
        + data.labelCoeff label slotTwo
          * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            *ᵥ data.tightDir (data.basisLabel slotTwo)) atomShared := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => by
      rw [data.pairCircuit_reconstruction hmem hpos hne hpair atomIndex]; ring
  rw [hexpand, htightOne, htightTwo,
    data.pairCircuit_reconstruction hmem hpos hne hpair atomShared]
  ring

/-- **THE PARALLEL FOREIGN ROWS.**  In the dead-wedge branch the two shared
atoms carry gap rows that are proportional across the two foreign atoms:
both rows annihilate the support-two label direction. -/
theorem splitCircuit_foreign_rows_parallel (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    (hpos : 0 < data.reducedWeight label)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hcoeffOne : data.labelCoeff label slotOne ≠ 0)
    (hcoeffTwo : data.labelCoeff label slotTwo ≠ 0)
    (hpair : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      data.labelCoeff label slot = 0)
    {atomA atomB atomX atomY : Fin 6}
    (hAB : atomA ≠ atomB) (hAX : atomA ≠ atomX) (hAY : atomA ≠ atomY)
    (hBX : atomB ≠ atomX) (hBY : atomB ≠ atomY) (hXY : atomX ≠ atomY)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomA, atomB, atomX})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomA, atomB, atomY})
    (hdeadA : data.tightDir label atomA = 0)
    (hdeadB : data.tightDir label atomB = 0) :
    chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomX
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomY
      = chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomY
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomX := by
  classical
  obtain ⟨hsupp, hliveX, _⟩ := data.splitCircuit_label_pair_support hmem hpos hne
    hcoeffOne hcoeffTwo hpair hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo
    hdeadA hdeadB
  have hmemAone : atomA ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne]; simp
  have hmemAtwo : atomA ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsupportTwo]; simp
  have hmemBone : atomB ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne]; simp
  have hmemBtwo : atomB ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsupportTwo]; simp
  have hrowA := data.pairCircuit_gap_row_of_shared hmem hpos hne hpair hmemAone hmemAtwo
  have hrowB := data.pairCircuit_gap_row_of_shared hmem hpos hne hpair hmemBone hmemBtwo
  rw [mulVec_apply_of_pair_support _ hXY hsupp atomA, hdeadA, mul_zero] at hrowA
  rw [mulVec_apply_of_pair_support _ hXY hsupp atomB, hdeadB, mul_zero] at hrowB
  have hkey : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomX
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomY
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomA atomY
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomX)
      * data.tightDir label atomX = 0 := by
    linear_combination (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomY) * hrowA
      - (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomA atomY) * hrowB
  rcases mul_eq_zero.mp hkey with hzero | hzero
  · linarith
  · exact absurd hzero hliveX

/-- **THE DEAD-WEDGE PAIR BUDGET.**  The vanishing pair minor of the two
foreign atoms is a singular two-atom block, thus the two shifted diagonals
pay a unit budget. -/
theorem splitCircuit_deadWedge_saturation (data : SharedPrivateData crux)
    {atomX atomY : Fin 6} (hXY : atomX ≠ atomY)
    (hminor : chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomX atomY
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomX atomY
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomX atomX
          - chartObjective (chartPointOfDesign crux.design))
        * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomY atomY
          - chartObjective (chartPointOfDesign crux.design))) :
    shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomX
      / (1 - (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomX))
    + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomY
      / (1 - (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomY))
      ≤ 1 :=
  gapPairSingular_saturation data.hdata.isSymmetric data.hdata.isIdempotent hXY
    (data.captureDiag_lt_one atomX) (data.captureDiag_lt_one atomY)
    (data.shiftedGapDiag_pos atomX) (data.shiftedGapDiag_pos atomY) hminor

/-- The plain dead-wedge pair budget. -/
theorem splitCircuit_deadWedge_shifted_sum_le_one (data : SharedPrivateData crux)
    {atomX atomY : Fin 6} (hXY : atomX ≠ atomY)
    (hminor : chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomX atomY
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomX atomY
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomX atomX
          - chartObjective (chartPointOfDesign crux.design))
        * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomY atomY
          - chartObjective (chartPointOfDesign crux.design))) :
    shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomX
      + shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomY ≤ 1 :=
  gapPairSingular_shifted_sum_le_one data.hdata.isSymmetric data.hdata.isIdempotent hXY
    (data.captureDiag_nonneg atomX) (data.captureDiag_nonneg atomY)
    (data.captureDiag_lt_one atomX) (data.captureDiag_lt_one atomY)
    (data.shiftedGapDiag_pos atomX) (data.shiftedGapDiag_pos atomY) hminor

end SharedPrivateData

/-! ## Layer 8 — the two paid residues and the whole of closure two -/

/-- **THE PAID IDENTICAL RESIDUE.**  The identical-support branch of a pair
circuit, together with the rank-one block, the triple budget it pays, and
the cross energy ceiling. -/
def SharedPrivateCircuitPairIdenticalSaturatedClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      (∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        data.labelCoeff label slot = 0) →
      ∀ atomU atomV atomS : Fin 6, atomU ≠ atomV → atomU ≠ atomS → atomV ≠ atomS →
        datumTightSupport data.tightDir (data.basisLabel slotOne)
          = {atomU, atomV, atomS} →
        datumTightSupport data.tightDir (data.basisLabel slotTwo)
          = {atomU, atomV, atomS} →
        GapBlockRankOne (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design)) atomU atomV atomS →
        data.pinAtom ∉ datumTightSupport data.tightDir (data.basisLabel slotOne) →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomU
          / (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomU))
        + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomV
          / (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomV))
        + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomS
          / (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomS)) ≤ 1 →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomU
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomV
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomS ≤ 1 →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomU
          * (shiftedGapDiag (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight
              (chartObjective (chartPointOfDesign crux.design)) atomV
            + shiftedGapDiag (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight
              (chartObjective (chartPointOfDesign crux.design)) atomS) ≤ 1 / 4 →
        False

/-- **THE PAID DEAD-WEDGE RESIDUE.**  The collapsed split branch, together
with the support-two shape of its label, the pair budget it pays, and the
parallel shared rows. -/
def SharedPrivateCircuitSplitPairSaturatedClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      (∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        data.labelCoeff label slot = 0) →
      ∀ atomA atomB atomX atomY : Fin 6,
        atomA ≠ atomB → atomA ≠ atomX → atomA ≠ atomY →
        atomB ≠ atomX → atomB ≠ atomY → atomX ≠ atomY →
        datumTightSupport data.tightDir (data.basisLabel slotOne)
          = {atomA, atomB, atomX} →
        datumTightSupport data.tightDir (data.basisLabel slotTwo)
          = {atomA, atomB, atomY} →
        data.tightDir label atomA = 0 →
        data.tightDir label atomB = 0 →
        chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomX atomY
            * chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomX atomY
          = (chartStationaryGap (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight atomX atomX
              - chartObjective (chartPointOfDesign crux.design))
            * (chartStationaryGap (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight atomY atomY
              - chartObjective (chartPointOfDesign crux.design)) →
        (∀ atomIndex, atomIndex ≠ atomX → atomIndex ≠ atomY →
          data.tightDir label atomIndex = 0) →
        data.tightDir label atomX ≠ 0 →
        data.tightDir label atomY ≠ 0 →
        chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomA atomX
            * chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomY
          = chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomA atomY
            * chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomX →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomX
          / (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomX))
        + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomY
          / (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomY)) ≤ 1 →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomX
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomY ≤ 1 →
        False

/-- **THE IDENTICAL PAYMENT BRIDGE.**  Every hypothesis that the paid
residue adds is a theorem at the datum, thus the paid residue closes the
plain one. -/
theorem sharedPrivateCircuitPairIdenticalClosed_of_saturated
    (hpaid : SharedPrivateCircuitPairIdenticalSaturatedClosed) :
    SharedPrivateCircuitPairIdenticalClosed := by
  intro crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomU atomV atomS hUV hUS hVS hsupportOne hsupportTwo hshape
  exact hpaid crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomU atomV atomS hUV hUS hVS hsupportOne hsupportTwo hshape
    (data.pinAtom_notMem_of_identical_support hne (hsupportTwo.trans hsupportOne.symm))
    (data.identical_support_saturation hne hUV hUS hVS hsupportOne hsupportTwo)
    (data.identical_support_shifted_sum_le_one hne hUV hUS hVS hsupportOne hsupportTwo)
    (data.identical_support_cross_energy_le hne hUV hUS hVS hsupportOne hsupportTwo)

/-- **THE DEAD-WEDGE PAYMENT BRIDGE.** -/
theorem sharedPrivateCircuitSplitPairClosed_of_saturated
    (hpaid : SharedPrivateCircuitSplitPairSaturatedClosed) :
    SharedPrivateCircuitSplitPairClosed := by
  intro crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomA atomB atomX atomY hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo
    hdeadA hdeadB hminor
  obtain ⟨hsupp, hliveX, hliveY⟩ := data.splitCircuit_label_pair_support hmem hpos hne
    hcoeffOne hcoeffTwo hpair hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo
    hdeadA hdeadB
  exact hpaid crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomA atomB atomX atomY hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo
    hdeadA hdeadB hminor hsupp hliveX hliveY
    (data.splitCircuit_foreign_rows_parallel hmem hpos hne hcoeffOne hcoeffTwo hpair
      hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo hdeadA hdeadB)
    (data.splitCircuit_deadWedge_saturation hXY hminor)
    (data.splitCircuit_deadWedge_shifted_sum_le_one hXY hminor)

/-- **THE EXTRAS FROM THE PAID LATTICE.** -/
theorem sharedPrivateExtrasClosed_of_saturated_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalSaturatedClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateExtrasClosed :=
  sharedPrivateExtrasClosed_of_circuit_lattice
    (sharedPrivateCircuitPairIdenticalClosed_of_saturated hidentical) hwedgeLive
    (sharedPrivateCircuitSplitPairClosed_of_saturated hwedgeDead) hwide

/-- **THE WHOLE OF CLOSURE TWO ON THE PAID RESIDUES.** -/
theorem sharedPrivateKilled_of_saturated_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalSaturatedClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_sharedPrivate_lattice
    (sharedPrivateCircuitPairIdenticalClosed_of_saturated hidentical) hwedgeLive
    (sharedPrivateCircuitSplitPairClosed_of_saturated hwedgeDead) hwide hconfined

/-- Closure two of the rank-four rung on the paid residues. -/
theorem rankFourSharedPrivateClosed_of_saturated_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalSaturatedClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_sharedPrivate_lattice
    (sharedPrivateCircuitPairIdenticalClosed_of_saturated hidentical) hwedgeLive
    (sharedPrivateCircuitSplitPairClosed_of_saturated hwedgeDead) hwide hconfined

/-- The shared-private closure of the rank-five rung on the paid
residues. -/
theorem rankFiveSharedPrivateClosed_of_saturated_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalSaturatedClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_sharedPrivate_lattice
    (sharedPrivateCircuitPairIdenticalClosed_of_saturated hidentical) hwedgeLive
    (sharedPrivateCircuitSplitPairClosed_of_saturated hwedgeDead) hwide hconfined

/-- The shared-private closure of the rank-six rung on the paid
residues. -/
theorem rankSixSharedPrivateClosed_of_saturated_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalSaturatedClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_sharedPrivate_lattice
    (sharedPrivateCircuitPairIdenticalClosed_of_saturated hidentical) hwedgeLive
    (sharedPrivateCircuitSplitPairClosed_of_saturated hwedgeDead) hwide hconfined

/-! ## Layer 9 — the set budget at every size -/

section SetBudget

variable {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
variable {weight : Fin size → ℝ} {value : ℝ}

/-- **THE SHIFTED GAP MATRIX.**  The chart minus the captured diagonal.
Its diagonal is the shifted gap diagonal and its off-diagonal is the gap
itself. -/
noncomputable def shiftedGap (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (value : ℝ) : Matrix (Fin size) (Fin size) ℝ :=
  projection - Matrix.diagonal (fun atomIndex => value + weight atomIndex)

theorem shiftedGap_apply_diag (atomIndex : Fin size) :
    shiftedGap projection weight value atomIndex atomIndex
      = shiftedGapDiag projection weight value atomIndex := by
  rw [shiftedGap, Matrix.sub_apply, Matrix.diagonal_apply_eq, shiftedGapDiag,
    chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_eq]
  ring

theorem shiftedGap_apply_offDiag {rowIndex colIndex : Fin size}
    (hne : rowIndex ≠ colIndex) :
    shiftedGap projection weight value rowIndex colIndex
      = chartStationaryGap projection weight rowIndex colIndex := by
  rw [shiftedGap, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hne, sub_zero,
    chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hne, sub_zero]

/-- The chart entry through the shifted gap. -/
theorem projection_eq_shiftedGap_add (rowIndex colIndex : Fin size) :
    projection rowIndex colIndex
      = shiftedGap projection weight value rowIndex colIndex
        + (if rowIndex = colIndex then value + weight rowIndex else 0) := by
  by_cases hne : rowIndex = colIndex
  · subst hne
    rw [shiftedGap_apply_diag, if_pos rfl, shiftedGapDiag, chartStationaryGap,
      Matrix.sub_apply, Matrix.diagonal_apply_eq]
    ring
  · rw [shiftedGap_apply_offDiag hne, if_neg hne, add_zero,
      projection_offDiag_eq_gap (projection := projection) (weight := weight) hne]

/-- The probe supported on a finite set. -/
noncomputable def setProbe (setS : Finset (Fin size)) (val : Fin size → ℝ) :
    Fin size → ℝ :=
  fun atomIndex => if atomIndex ∈ setS then val atomIndex else 0

theorem setProbe_mem {setS : Finset (Fin size)} {val : Fin size → ℝ}
    {atomIndex : Fin size} (hmem : atomIndex ∈ setS) :
    setProbe setS val atomIndex = val atomIndex := by
  rw [setProbe, if_pos hmem]

theorem setProbe_dotProduct (setS : Finset (Fin size)) (val other : Fin size → ℝ) :
    setProbe setS val ⬝ᵥ other = ∑ atomIndex ∈ setS, val atomIndex * other atomIndex := by
  classical
  rw [dotProduct]
  refine (Finset.sum_subset (Finset.subset_univ setS) ?_).symm.trans ?_
  · intro atomIndex _ hnot
    rw [setProbe, if_neg hnot, zero_mul]
  · exact Finset.sum_congr rfl fun atomIndex hmem => by rw [setProbe_mem hmem]

theorem setProbe_mulVec (matrixA : Matrix (Fin size) (Fin size) ℝ)
    (setS : Finset (Fin size)) (val : Fin size → ℝ) (rowIndex : Fin size) :
    (matrixA *ᵥ setProbe setS val) rowIndex
      = ∑ atomIndex ∈ setS, matrixA rowIndex atomIndex * val atomIndex := by
  classical
  rw [Matrix.mulVec, dotProduct]
  refine (Finset.sum_subset (Finset.subset_univ setS) ?_).symm.trans ?_
  · intro atomIndex _ hnot
    rw [setProbe, if_neg hnot, mul_zero]
  · exact Finset.sum_congr rfl fun atomIndex hmem => by rw [setProbe_mem hmem]

/-- **THE SET CONTRACTION.**  The chart contracts every probe supported on
a finite set, read as a double sum over the set. -/
theorem projection_set_contraction (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection) (setS : Finset (Fin size))
    (val : Fin size → ℝ) :
    ∑ rowIndex ∈ setS, ∑ colIndex ∈ setS,
        projection rowIndex colIndex * (val rowIndex * val colIndex)
      ≤ ∑ atomIndex ∈ setS, val atomIndex * val atomIndex := by
  classical
  have hbase := dotProduct_mulVec_le_self_of_symmetricIdempotent hsymm hidem
    (setProbe setS val)
  have hleft : setProbe setS val ⬝ᵥ (projection *ᵥ setProbe setS val)
      = ∑ rowIndex ∈ setS, ∑ colIndex ∈ setS,
        projection rowIndex colIndex * (val rowIndex * val colIndex) := by
    rw [setProbe_dotProduct]
    refine Finset.sum_congr rfl fun rowIndex _ => ?_
    rw [setProbe_mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun colIndex _ => by ring
  have hright : setProbe setS val ⬝ᵥ setProbe setS val
      = ∑ atomIndex ∈ setS, val atomIndex * val atomIndex := by
    rw [setProbe_dotProduct]
    exact Finset.sum_congr rfl fun atomIndex hmem => by rw [setProbe_mem hmem]
  rw [hleft, hright] at hbase
  exact hbase

/-- **THE SET BUDGET.**  A shifted gap block that is a rank-one square on a
finite set pays a unit budget, at EVERY size of the set.  The pair and the
triple budgets are the two smallest instances.

The extremal probe is the corner column of the block divided by the
captured defect.  The rank-one law folds the double sum into a square, and
the contraction reads `W * W ≤ corner * W` with `W` positive. -/
theorem gapSet_saturation (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection) {setS : Finset (Fin size)}
    {atomU : Fin size} (hmemU : atomU ∈ setS)
    (hcap : ∀ atomIndex ∈ setS, value + weight atomIndex < 1)
    (hpos : ∀ atomIndex ∈ setS, 0 < shiftedGapDiag projection weight value atomIndex)
    (hrankOne : ∀ rowIndex ∈ setS, ∀ colIndex ∈ setS,
      shiftedGap projection weight value rowIndex colIndex
          * shiftedGapDiag projection weight value atomU
        = shiftedGap projection weight value atomU rowIndex
          * shiftedGap projection weight value atomU colIndex) :
    ∑ atomIndex ∈ setS, shiftedGapDiag projection weight value atomIndex
        / (1 - (value + weight atomIndex))
      ≤ 1 := by
  classical
  have hcorner : 0 < shiftedGapDiag projection weight value atomU := hpos atomU hmemU
  set val : Fin size → ℝ := fun atomIndex =>
    shiftedGap projection weight value atomU atomIndex
      / (1 - (value + weight atomIndex)) with hval
  have hvalApply : ∀ atomIndex : Fin size, val atomIndex
      = shiftedGap projection weight value atomU atomIndex
        / (1 - (value + weight atomIndex)) := fun _ => rfl
  have hdef : ∀ atomIndex ∈ setS, (0 : ℝ) < 1 - (value + weight atomIndex) :=
    fun atomIndex hmem => by linarith [hcap atomIndex hmem]
  -- the square of a corner column entry is the corner times the diagonal
  have hsquare : ∀ atomIndex ∈ setS,
      shiftedGap projection weight value atomU atomIndex
          * shiftedGap projection weight value atomU atomIndex
        = shiftedGapDiag projection weight value atomIndex
          * shiftedGapDiag projection weight value atomU := by
    intro atomIndex hmem
    have hinstance := hrankOne atomIndex hmem atomIndex hmem
    rw [shiftedGap_apply_diag] at hinstance
    exact hinstance.symm
  -- the ratio sum and the folded total
  have hratio : ∀ atomIndex ∈ setS,
      shiftedGap projection weight value atomU atomIndex * val atomIndex
        = shiftedGapDiag projection weight value atomU
          * (shiftedGapDiag projection weight value atomIndex
            / (1 - (value + weight atomIndex))) := by
    intro atomIndex hmem
    have hne : (1 : ℝ) - (value + weight atomIndex) ≠ 0 :=
      ne_of_gt (hdef atomIndex hmem)
    rw [hvalApply atomIndex]
    field_simp
    linear_combination hsquare atomIndex hmem
  have hsumNonneg : ∀ atomIndex ∈ setS,
      0 ≤ shiftedGapDiag projection weight value atomIndex
        / (1 - (value + weight atomIndex)) :=
    fun atomIndex hmem =>
      le_of_lt (div_pos (hpos atomIndex hmem) (hdef atomIndex hmem))
  have hsumPos : 0 < ∑ atomIndex ∈ setS,
      shiftedGapDiag projection weight value atomIndex
        / (1 - (value + weight atomIndex)) :=
    Finset.sum_pos' hsumNonneg ⟨atomU, hmemU, div_pos hcorner (hdef atomU hmemU)⟩
  set total := ∑ atomIndex ∈ setS,
    shiftedGap projection weight value atomU atomIndex * val atomIndex with htotal
  have htotalEq : total = shiftedGapDiag projection weight value atomU
      * ∑ atomIndex ∈ setS, shiftedGapDiag projection weight value atomIndex
        / (1 - (value + weight atomIndex)) := by
    rw [htotal, Finset.mul_sum]
    exact Finset.sum_congr rfl hratio
  have htotalPos : 0 < total := by
    rw [htotalEq]; exact mul_pos hcorner hsumPos
  -- the contraction, split into the shifted gap form and the captured diagonal
  have hcontract := projection_set_contraction hsymm hidem setS val
  have hsplit : ∑ rowIndex ∈ setS, ∑ colIndex ∈ setS,
        projection rowIndex colIndex * (val rowIndex * val colIndex)
      = (∑ rowIndex ∈ setS, ∑ colIndex ∈ setS,
          shiftedGap projection weight value rowIndex colIndex
            * (val rowIndex * val colIndex))
        + ∑ atomIndex ∈ setS,
          (value + weight atomIndex) * (val atomIndex * val atomIndex) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun rowIndex hrow => ?_
    have hinner : ∑ colIndex ∈ setS,
        projection rowIndex colIndex * (val rowIndex * val colIndex)
        = (∑ colIndex ∈ setS, shiftedGap projection weight value rowIndex colIndex
            * (val rowIndex * val colIndex))
          + (value + weight rowIndex) * (val rowIndex * val rowIndex) := by
      have hterm : ∀ colIndex ∈ setS,
          projection rowIndex colIndex * (val rowIndex * val colIndex)
          = shiftedGap projection weight value rowIndex colIndex
              * (val rowIndex * val colIndex)
            + (if rowIndex = colIndex then value + weight rowIndex else 0)
              * (val rowIndex * val colIndex) := by
        intro colIndex _
        rw [projection_eq_shiftedGap_add (projection := projection) (weight := weight)
          (value := value) rowIndex colIndex]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single rowIndex
        (fun colIndex _ hne => by rw [if_neg (Ne.symm hne), zero_mul])
        (fun hnot => absurd hrow hnot), if_pos rfl]
    exact hinner
  rw [hsplit] at hcontract
  -- the defect side collapses to the total
  have hdefectSide : ∑ atomIndex ∈ setS, val atomIndex * val atomIndex
      - ∑ atomIndex ∈ setS, (value + weight atomIndex) * (val atomIndex * val atomIndex)
      = total := by
    rw [htotal, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun atomIndex hmem => ?_
    have hne : (1 : ℝ) - (value + weight atomIndex) ≠ 0 :=
      ne_of_gt (hdef atomIndex hmem)
    rw [hvalApply atomIndex]
    field_simp
  have hform : ∑ rowIndex ∈ setS, ∑ colIndex ∈ setS,
      shiftedGap projection weight value rowIndex colIndex
        * (val rowIndex * val colIndex) ≤ total := by
    rw [← hdefectSide]; linarith [hcontract]
  -- the rank-one law folds the double sum into a square
  have hfold : shiftedGapDiag projection weight value atomU
      * ∑ rowIndex ∈ setS, ∑ colIndex ∈ setS,
        shiftedGap projection weight value rowIndex colIndex
          * (val rowIndex * val colIndex)
      = total * total := by
    rw [Finset.mul_sum, htotal, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun rowIndex hrow => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun colIndex hcol => ?_
    have hinstance := hrankOne rowIndex hrow colIndex hcol
    linear_combination (val rowIndex * val colIndex) * hinstance
  have hsq : total * total ≤ shiftedGapDiag projection weight value atomU * total := by
    rw [← hfold]; exact mul_le_mul_of_nonneg_left hform (le_of_lt hcorner)
  have hle : total ≤ shiftedGapDiag projection weight value atomU := by
    by_contra hcontra
    rw [not_le] at hcontra
    nlinarith [hsq, htotalPos, hcontra]
  rw [htotalEq] at hle
  have hfinal : shiftedGapDiag projection weight value atomU
      * ∑ atomIndex ∈ setS, shiftedGapDiag projection weight value atomIndex
        / (1 - (value + weight atomIndex))
      ≤ shiftedGapDiag projection weight value atomU * 1 := by
    rw [mul_one]; exact hle
  exact le_of_mul_le_mul_left hfinal hcorner

/-- The plain set budget. -/
theorem gapSet_shifted_sum_le_one (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection) {setS : Finset (Fin size)}
    {atomU : Fin size} (hmemU : atomU ∈ setS)
    (hfloor : ∀ atomIndex ∈ setS, 0 ≤ value + weight atomIndex)
    (hcap : ∀ atomIndex ∈ setS, value + weight atomIndex < 1)
    (hpos : ∀ atomIndex ∈ setS, 0 < shiftedGapDiag projection weight value atomIndex)
    (hrankOne : ∀ rowIndex ∈ setS, ∀ colIndex ∈ setS,
      shiftedGap projection weight value rowIndex colIndex
          * shiftedGapDiag projection weight value atomU
        = shiftedGap projection weight value atomU rowIndex
          * shiftedGap projection weight value atomU colIndex) :
    ∑ atomIndex ∈ setS, shiftedGapDiag projection weight value atomIndex ≤ 1 := by
  refine le_trans (Finset.sum_le_sum ?_)
    (gapSet_saturation hsymm hidem hmemU hcap hpos hrankOne)
  intro atomIndex hmem
  have hdef : (0 : ℝ) < 1 - (value + weight atomIndex) := by
    linarith [hcap atomIndex hmem]
  rw [le_div_iff₀ hdef]
  nlinarith [hpos atomIndex hmem, hfloor atomIndex hmem]

/-- **THE TRIPLE BRIDGE.**  The six vanishing minors of a rank-one gap
block give the nine rank-one instances that the set budget wants. -/
theorem shiftedGap_rankOne_of_gapBlockRankOne (hsymm : projectionᵀ = projection)
    {atomU atomV atomS : Fin size} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hshape : GapBlockRankOne projection weight value atomU atomV atomS) :
    ∀ rowIndex ∈ ({atomU, atomV, atomS} : Finset (Fin size)),
      ∀ colIndex ∈ ({atomU, atomV, atomS} : Finset (Fin size)),
        shiftedGap projection weight value rowIndex colIndex
            * shiftedGapDiag projection weight value atomU
          = shiftedGap projection weight value atomU rowIndex
            * shiftedGap projection weight value atomU colIndex := by
  classical
  obtain ⟨hminorUV, hminorUS, _, hcross, _, _⟩ := hshape
  have hgapSymm : ∀ rowIndex colIndex : Fin size,
      chartStationaryGap projection weight colIndex rowIndex
        = chartStationaryGap projection weight rowIndex colIndex := by
    intro rowIndex colIndex
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.sub_apply,
      projection_symm_entry hsymm rowIndex colIndex]
    by_cases hne : rowIndex = colIndex
    · subst hne; rfl
    · rw [Matrix.diagonal_apply_ne _ (Ne.symm hne), Matrix.diagonal_apply_ne _ hne]
  have hdiagU := shiftedGap_apply_diag (projection := projection) (weight := weight)
    (value := value) atomU
  have hdiagV := shiftedGap_apply_diag (projection := projection) (weight := weight)
    (value := value) atomV
  have hdiagS := shiftedGap_apply_diag (projection := projection) (weight := weight)
    (value := value) atomS
  have hoffUV := shiftedGap_apply_offDiag (projection := projection) (weight := weight)
    (value := value) hUV
  have hoffUS := shiftedGap_apply_offDiag (projection := projection) (weight := weight)
    (value := value) hUS
  have hoffVS := shiftedGap_apply_offDiag (projection := projection) (weight := weight)
    (value := value) hVS
  have hoffVU := shiftedGap_apply_offDiag (projection := projection) (weight := weight)
    (value := value) (Ne.symm hUV)
  have hoffSU := shiftedGap_apply_offDiag (projection := projection) (weight := weight)
    (value := value) (Ne.symm hUS)
  have hoffSV := shiftedGap_apply_offDiag (projection := projection) (weight := weight)
    (value := value) (Ne.symm hVS)
  intro rowIndex hrow colIndex hcol
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrow hcol
  rcases hrow with hrow | hrow | hrow <;> rcases hcol with hcol | hcol | hcol <;>
    rw [hrow, hcol] <;>
  simp only [hdiagU, hdiagV, hdiagS, hoffUV, hoffUS, hoffVS, hoffVU, hoffSU,
    hoffSV, shiftedGapDiag]
  · ring
  · ring
  · linear_combination (chartStationaryGap projection weight atomU atomU - value) * hgapSymm atomU atomV
  · linear_combination -hminorUV
  · linear_combination hcross
  · linear_combination (chartStationaryGap projection weight atomU atomU - value) * hgapSymm atomU atomS
  · linear_combination (chartStationaryGap projection weight atomU atomU - value) * hgapSymm atomV atomS + hcross
  · linear_combination -hminorUS

end SetBudget

/-! ## Layer 10 — the total and the two-set cover kill -/

section CoverKill

variable {size rank : ℕ} {activeIndex : Type}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE SHIFTED GAP TOTAL.**  The whole shifted gap diagonal sums to the
rank minus one minus the value times the size.  The chart trace and the
weight simplex are the only inputs. -/
theorem shiftedGapDiag_sum_eq
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ∑ atomIndex : Fin size, shiftedGapDiag projection weight value atomIndex
      = (rank : ℝ) - 1 - (size : ℝ) * value := by
  classical
  have hexpand : ∀ atomIndex : Fin size,
      shiftedGapDiag projection weight value atomIndex
        = projection atomIndex atomIndex - weight atomIndex - value := by
    intro atomIndex
    rw [shiftedGapDiag, chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_eq]
  rw [Finset.sum_congr rfl fun atomIndex _ => hexpand atomIndex]
  have hsplit : ∑ atomIndex : Fin size,
      (projection atomIndex atomIndex - weight atomIndex - value)
      = (∑ atomIndex : Fin size, projection atomIndex atomIndex)
        - (∑ atomIndex : Fin size, weight atomIndex)
        - ∑ _atomIndex : Fin size, value := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have htrace : ∑ atomIndex : Fin size, projection atomIndex atomIndex = (rank : ℝ) :=
    hdata.hasTraceRank
  rw [hsplit, htrace, hdata.weight_sum_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- **THE TWO-SET COVER KILL.**  Two rank-one shifted gap blocks whose sets
cover every atom pay two units together, thus the shifted gap total obeys
`rank ≤ 3 + size * value`.  At rank three the chart value is therefore
nonnegative, and every kill target has a negative value. -/
theorem rank_le_of_shiftedGap_rankOne_cover
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {setOne setTwo : Finset (Fin size)} {atomOne atomTwo : Fin size}
    (hcover : setOne ∪ setTwo = Finset.univ)
    (hmemOne : atomOne ∈ setOne) (hmemTwo : atomTwo ∈ setTwo)
    (hpos : ∀ atomIndex : Fin size,
      0 < shiftedGapDiag projection weight value atomIndex)
    (hrankOneFirst : ∀ rowIndex ∈ setOne, ∀ colIndex ∈ setOne,
      shiftedGap projection weight value rowIndex colIndex
          * shiftedGapDiag projection weight value atomOne
        = shiftedGap projection weight value atomOne rowIndex
          * shiftedGap projection weight value atomOne colIndex)
    (hrankOneSecond : ∀ rowIndex ∈ setTwo, ∀ colIndex ∈ setTwo,
      shiftedGap projection weight value rowIndex colIndex
          * shiftedGapDiag projection weight value atomTwo
        = shiftedGap projection weight value atomTwo rowIndex
          * shiftedGap projection weight value atomTwo colIndex)
    (hvalue : value < 0) :
    (rank : ℝ) ≤ 3 + (size : ℝ) * value := by
  classical
  have hfloor : ∀ atomIndex : Fin size, 0 ≤ value + weight atomIndex :=
    fun atomIndex => capture_diagonal_nonneg_of_isChartStationaryData hdata atomIndex
  have hcap : ∀ atomIndex : Fin size, value + weight atomIndex < 1 :=
    fun atomIndex => capture_diagonal_lt_one_of_negative_value hdata hvalue atomIndex
  have hfirst := gapSet_shifted_sum_le_one hdata.isSymmetric hdata.isIdempotent hmemOne
    (fun atomIndex _ => hfloor atomIndex) (fun atomIndex _ => hcap atomIndex)
    (fun atomIndex _ => hpos atomIndex) hrankOneFirst
  have hsecond := gapSet_shifted_sum_le_one hdata.isSymmetric hdata.isIdempotent hmemTwo
    (fun atomIndex _ => hfloor atomIndex) (fun atomIndex _ => hcap atomIndex)
    (fun atomIndex _ => hpos atomIndex) hrankOneSecond
  have hunion : ∑ atomIndex ∈ setOne ∪ setTwo,
      shiftedGapDiag projection weight value atomIndex
      ≤ (∑ atomIndex ∈ setOne, shiftedGapDiag projection weight value atomIndex)
        + ∑ atomIndex ∈ setTwo, shiftedGapDiag projection weight value atomIndex := by
    have hsplit : ∑ atomIndex ∈ setOne ∪ setTwo,
        shiftedGapDiag projection weight value atomIndex
        = (∑ atomIndex ∈ setOne, shiftedGapDiag projection weight value atomIndex)
          + ∑ atomIndex ∈ setTwo \ setOne,
            shiftedGapDiag projection weight value atomIndex := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
    have hrest : ∑ atomIndex ∈ setTwo \ setOne,
        shiftedGapDiag projection weight value atomIndex
        ≤ ∑ atomIndex ∈ setTwo, shiftedGapDiag projection weight value atomIndex :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
        (fun atomIndex _ _ => le_of_lt (hpos atomIndex))
    rw [hsplit]; linarith
  rw [hcover] at hunion
  have htotal := shiftedGapDiag_sum_eq hdata
  rw [htotal] at hunion
  linarith

end CoverKill

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-- The shifted gap total of a shared-private datum. -/
theorem shiftedGapDiag_sum (data : SharedPrivateData crux) :
    ∑ atomIndex : Fin 6, shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomIndex
      = 2 - 6 * chartObjective (chartPointOfDesign crux.design) := by
  have hsum := shiftedGapDiag_sum_eq data.hdata
  norm_num at hsum
  linarith [hsum]

/-- **THE COMPLEMENT KILL.**  Two rank-one shifted gap blocks whose atom
sets cover the six atoms cannot both exist: the shifted gap total is
`2 - 6 * value` and the two budgets pay only two.  The value is negative,
thus the two never meet. -/
theorem false_of_shiftedGap_rankOne_cover (data : SharedPrivateData crux)
    {setOne setTwo : Finset (Fin 6)} {atomOne atomTwo : Fin 6}
    (hcover : setOne ∪ setTwo = Finset.univ)
    (hmemOne : atomOne ∈ setOne) (hmemTwo : atomTwo ∈ setTwo)
    (hrankOneFirst : ∀ rowIndex ∈ setOne, ∀ colIndex ∈ setOne,
      shiftedGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) rowIndex colIndex
          * shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomOne
        = shiftedGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomOne rowIndex
          * shiftedGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomOne colIndex)
    (hrankOneSecond : ∀ rowIndex ∈ setTwo, ∀ colIndex ∈ setTwo,
      shiftedGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) rowIndex colIndex
          * shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomTwo
        = shiftedGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomTwo rowIndex
          * shiftedGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomTwo colIndex) :
    False := by
  have hbound := rank_le_of_shiftedGap_rankOne_cover data.hdata hcover hmemOne hmemTwo
    (fun atomIndex => data.shiftedGapDiag_pos atomIndex) hrankOneFirst hrankOneSecond
    data.hvalueNeg
  have hvalue := data.hvalueNeg
  norm_num at hbound
  linarith

/-- **THE IDENTICAL BRANCH DIES AGAINST A RANK-ONE COMPLEMENT.**  The shared
triple already pays one unit.  A rank-one shifted gap block on the other
three atoms would pay the second, and the two payments are one unit short
of the shifted gap total. -/
theorem false_of_identical_support_complement_rankOne (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomU atomV atomS atomP atomQ atomR : Fin 6}
    (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS) (hVS : atomV ≠ atomS)
    (hPQ : atomP ≠ atomQ) (hPR : atomP ≠ atomR) (hQR : atomQ ≠ atomR)
    (hcover : ({atomU, atomV, atomS} : Finset (Fin 6)) ∪ {atomP, atomQ, atomR}
      = Finset.univ)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS})
    (hcomplement : GapBlockRankOne (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) atomP atomQ atomR) :
    False :=
  data.false_of_shiftedGap_rankOne_cover hcover (by simp) (by simp)
    (shiftedGap_rankOne_of_gapBlockRankOne data.hdata.isSymmetric hUV hUS hVS
      (data.gapBlockRankOne_of_identical_support hne hUV hUS hVS hsupportOne
        hsupportTwo))
    (shiftedGap_rankOne_of_gapBlockRankOne data.hdata.isSymmetric hPQ hPR hQR
      hcomplement)

end SharedPrivateData

end Gtz
