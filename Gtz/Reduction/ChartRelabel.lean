import Mathlib
import Gtz.LinAlg.LambdaMinReindex
import Gtz.Reduction.ChartAttainment

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Relabelling equivariance of the chart objective, at the configuration level

Permuting the atoms of a chart configuration conjugates the gap, transports
every principal block to the image block, and leaves the objective unchanged:
the block value moves along `C ↦ C.map σ` by the landed enumeration
independence of the least block eigenvalue, and the candidate family is
permutation-stable, so the sup is fixed.  These are the configuration-level
bricks; the chart-point and crux transports consume them downstream.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-- The relabelled configuration: chart entries and weights read through the
permutation. -/
def relabelChartConfig (relabel : Equiv.Perm (Fin size))
    (config : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) :
    (Fin size → Fin size → ℝ) × (Fin size → ℝ) :=
  (fun rowIndex colIndex => config.1 (relabel rowIndex) (relabel colIndex),
    fun atomIndex => config.2 (relabel atomIndex))

/-- Relabelling the configuration conjugates the gap by the permutation. -/
theorem chartGapRaw_relabelChartConfig (relabel : Equiv.Perm (Fin size))
    (config : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) :
    chartGapRaw (relabelChartConfig relabel config)
      = (chartGapRaw config).submatrix relabel relabel := by
  ext rowIndex colIndex
  simp only [chartGapRaw, relabelChartConfig, Matrix.sub_apply, Matrix.of_apply,
    Matrix.submatrix_apply]
  rcases eq_or_ne rowIndex colIndex with rfl | hne
  · simp only [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hne,
      Matrix.diagonal_apply_ne _ (fun hcontra => hne (relabel.injective hcontra))]

/-- **The block value transports along the permutation**: the relabelled
configuration's block at `C` is the original configuration's block at the image
`C.map relabel`. -/
theorem chartBlockValue_relabelChartConfig [Nonempty (Fin rank)]
    (relabel : Equiv.Perm (Fin size))
    (config : (Fin size → Fin size → ℝ) × (Fin size → ℝ))
    (selected : Finset (Fin size)) :
    chartBlockValue rank (relabelChartConfig relabel config) selected
      = chartBlockValue rank config (selected.map relabel.toEmbedding) := by
  classical
  rcases eq_or_ne selected.card rank with hcard | hcard
  · have hcardMap : (selected.map relabel.toEmbedding).card = rank := by
      rw [Finset.card_map]
      exact hcard
    rw [chartBlockValue, chartBlockValue, dif_pos hcard, dif_pos hcardMap,
      chartGapRaw_relabelChartConfig]
    have hcompose : (chartGapRaw config).submatrix
          (fun blockIndex => relabel (selected.orderEmbOfFin hcard blockIndex))
          (fun blockIndex => relabel (selected.orderEmbOfFin hcard blockIndex))
        = ((chartGapRaw config).submatrix relabel relabel).submatrix
            (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) := by
      ext rowIndex colIndex
      simp only [Matrix.submatrix_apply]
    rw [← hcompose]
    apply lambdaMinMat_submatrix_eq_of_range_eq
    · exact fun _ _ hinjective =>
        (selected.orderEmbOfFin hcard).injective (relabel.injective hinjective)
    · exact ((selected.map relabel.toEmbedding).orderEmbOfFin hcardMap).injective
    · calc Set.range (fun blockIndex => relabel (selected.orderEmbOfFin hcard blockIndex))
          = relabel '' Set.range (selected.orderEmbOfFin hcard) := by
            rw [← Set.range_comp]
            rfl
        _ = relabel '' ↑selected := by rw [Finset.range_orderEmbOfFin]
        _ = ↑(selected.map relabel.toEmbedding) := by
            rw [Finset.coe_map]
            rfl
        _ = Set.range ((selected.map relabel.toEmbedding).orderEmbOfFin hcardMap) := by
            rw [Finset.range_orderEmbOfFin]
  · have hcardMap : (selected.map relabel.toEmbedding).card ≠ rank := by
      rw [Finset.card_map]
      exact hcard
    rw [chartBlockValue, chartBlockValue, dif_neg hcard, dif_neg hcardMap]

/-- **The chart objective is relabelling-invariant**: the candidate family is
permutation-stable and the block value moves along the permutation. -/
theorem chartObjectiveRaw_relabelChartConfig [Nonempty (Fin rank)] (hrank : rank ≤ size)
    (relabel : Equiv.Perm (Fin size))
    (config : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) :
    chartObjectiveRaw size rank hrank (relabelChartConfig relabel config)
      = chartObjectiveRaw size rank hrank config := by
  classical
  have hroundTrip : ∀ selected : Finset (Fin size),
      (selected.map relabel.symm.toEmbedding).map relabel.toEmbedding = selected := by
    intro selected
    rw [Finset.map_map]
    ext atomIndex
    simp only [Finset.mem_map, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨sourceAtom, hsourceMem, rfl⟩
      simpa using hsourceMem
    · intro hmem
      exact ⟨atomIndex, hmem, by simp⟩
  rw [chartObjectiveRaw, chartObjectiveRaw]
  apply le_antisymm
  · apply Finset.sup'_le
    intro selected hselected
    rw [chartBlockValue_relabelChartConfig]
    exact Finset.le_sup' (fun block => chartBlockValue rank config block)
      ((mem_chartCandidates_iff size rank _).mpr
        (by rw [Finset.card_map]
            exact (mem_chartCandidates_iff size rank selected).mp hselected))
  · apply Finset.sup'_le
    intro selected hselected
    have hlift : chartBlockValue rank config selected
        = chartBlockValue rank (relabelChartConfig relabel config)
            (selected.map relabel.symm.toEmbedding) := by
      rw [chartBlockValue_relabelChartConfig relabel config
        (selected.map relabel.symm.toEmbedding), hroundTrip]
    rw [hlift]
    exact Finset.le_sup'
      (fun block => chartBlockValue rank (relabelChartConfig relabel config) block)
      ((mem_chartCandidates_iff size rank _).mpr
        (by rw [Finset.card_map]
            exact (mem_chartCandidates_iff size rank selected).mp hselected))

end Gtz
