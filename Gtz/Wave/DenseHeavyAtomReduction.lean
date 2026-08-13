import Gtz.Wave.DenseSharedBlockRank

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The heavy-atom reduction — the deflated chart and the doubled-pair cell

A dense rank-five profile with a full-carrier atom carries one extra pin:
the shifted weight of that atom is zero.  The pin turns the heavy row of
the chart into a rank-one row, and the chart deflates.

Write `x` for the heavy row of the chart and `R` for the deflated chart
`R x y = P x y - P h x * P h y / P h h`.  The deflated chart is a
symmetric idempotent again, its heavy row vanishes, and its trace is one
less than the rank.  The heavy row of the block eigen system is exactly
the orthogonality of the direction to `x`, thus every block equation
collapses to a two-by-two system on the two non-heavy atoms of the block.
The determinant of that system vanishes, and a block that carries two
basis slots kills the whole two-by-two corner.

At the doubled cell of the heavy-five profile two slots share a block,
the three remaining doubles carry the three blocks of a triangle, and the
deflated diagonal on the triangle sums to `1 - 6G`.  The row squares, the
positive semidefiniteness of the deflated chart and its contraction cap
the same sum at one.  The chart value is then nonnegative, against the
crux.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.chart_mulVec_dotProduct_self`, `Gtz.chart_quadratic_le_self`,
  `Gtz.chart_heavy_row_cauchy_schwarz` — **THE CHART QUADRATIC
  CALCULUS.**
* `Gtz.heavyReducedEntry` with `Gtz.heavyReducedEntry_symm`,
  `Gtz.heavyReducedEntry_heavy_row`, `Gtz.heavyReducedEntry_row_square`,
  `Gtz.heavyReducedEntry_row_pair_le`, `Gtz.heavyReducedEntry_trace` —
  **THE DEFLATED CHART.**
* `Gtz.heavyReducedEntry_triple_nonneg`,
  `Gtz.heavyReducedEntry_triple_le_self` — **THE DEFLATED FORM
  BOUNDS.**
* `Gtz.heavy_block_reduced_row`, `Gtz.heavy_block_reduced_minor` — **THE
  COLLAPSED BLOCK SYSTEM.**
* `Gtz.heavy_doubled_block_corner_zero` — **THE DOUBLED-BLOCK KILL.**
* `Gtz.dense_triangle_trace_le_one` — **THE TRIANGLE TRACE CAP.**
* `Gtz.RankFiveFrame.heavyFive_exists_shared_block_triple` — the triangle
  supply of the doubled cell.
* `Gtz.RankFiveDenseHeavyFiveDistinctClosed` — the residual cycle cell.
* `Gtz.rankFiveDenseHeavyFiveClosed_of_distinct` — **THE PROFILE-A
  DISPATCH: THE DOUBLED CELL IS DEAD.**

## Vacuity

The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no crux
exists, thus no frame exists.  The chart calculus, the deflated chart and
the triangle cap are unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## Layer 1 — the chart quadratic calculus -/

/-- The chart image keeps its energy: a symmetric idempotent reads the
square of an image as the form of the source. -/
theorem chart_mulVec_dotProduct_self
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (probe : Fin size → ℝ) :
    (projection *ᵥ probe) ⬝ᵥ (projection *ᵥ probe) = probe ⬝ᵥ (projection *ᵥ probe) := by
  have hstep : probe ⬝ᵥ (projection *ᵥ (projection *ᵥ probe))
      = (projection *ᵥ probe) ⬝ᵥ (projection *ᵥ probe) := by
    rw [Matrix.dotProduct_mulVec]
    congr 1
    rw [← hdata.isSymmetric, Matrix.vecMul_transpose, hdata.isSymmetric]
  rw [← hstep, Matrix.mulVec_mulVec, hdata.isIdempotent]

/-- **THE CONTRACTION.**  The chart form never exceeds the raw square:
the residual of the chart image is a sum of squares. -/
theorem chart_quadratic_le_self
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (probe : Fin size → ℝ) :
    probe ⬝ᵥ (projection *ᵥ probe) ≤ probe ⬝ᵥ probe := by
  have hresidual : (0 : ℝ)
      ≤ (probe - projection *ᵥ probe) ⬝ᵥ (probe - projection *ᵥ probe) :=
    dotProduct_self_nonneg _
  have hexpand : (probe - projection *ᵥ probe) ⬝ᵥ (probe - projection *ᵥ probe)
      = probe ⬝ᵥ probe - 2 * (probe ⬝ᵥ (projection *ᵥ probe))
        + (projection *ᵥ probe) ⬝ᵥ (projection *ᵥ probe) := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub,
      dotProduct_comm (projection *ᵥ probe) probe]
    ring
  rw [chart_mulVec_dotProduct_self hdata probe] at hexpand
  linarith [hresidual, hexpand.ge, hexpand.le]

/-- **THE HEAVY CAUCHY–SCHWARZ.**  The heavy coordinate of a chart image
is capped by the heavy diagonal entry and the chart form. -/
theorem chart_heavy_row_cauchy_schwarz
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (heavyAtom : Fin size) (probe : Fin size → ℝ) :
    ((projection *ᵥ probe) heavyAtom) * ((projection *ᵥ probe) heavyAtom)
      ≤ projection heavyAtom heavyAtom * (probe ⬝ᵥ (projection *ᵥ probe)) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin size))
    (fun colIndex => projection heavyAtom colIndex)
    (fun colIndex => (projection *ᵥ probe) colIndex)
  have hcross : ∑ colIndex : Fin size,
      projection heavyAtom colIndex * (projection *ᵥ probe) colIndex
      = (projection *ᵥ probe) heavyAtom := by
    have hstep : ∑ colIndex : Fin size,
        projection heavyAtom colIndex * (projection *ᵥ probe) colIndex
        = (projection *ᵥ (projection *ᵥ probe)) heavyAtom := rfl
    rw [hstep, Matrix.mulVec_mulVec, hdata.isIdempotent]
  have hheavy : ∑ colIndex : Fin size,
      projection heavyAtom colIndex ^ 2 = projection heavyAtom heavyAtom := by
    have hproduct := projection_row_product hdata heavyAtom heavyAtom
    rw [← hproduct]
    exact Finset.sum_congr rfl fun colIndex _ => pow_two _
  have himage : ∑ colIndex : Fin size, (projection *ᵥ probe) colIndex ^ 2
      = probe ⬝ᵥ (projection *ᵥ probe) := by
    have hstep : ∑ colIndex : Fin size, (projection *ᵥ probe) colIndex ^ 2
        = (projection *ᵥ probe) ⬝ᵥ (projection *ᵥ probe) := by
      simp only [dotProduct, pow_two]
    rw [hstep, chart_mulVec_dotProduct_self hdata probe]
  rw [hcross, hheavy, himage] at hcs
  nlinarith [hcs]

/-! ## Layer 2 — the deflated chart -/

/-- **THE DEFLATED CHART.**  The chart with its heavy rank-one row
removed.  At a heavy atom of vanishing shifted weight this is the part of
the chart the block systems see. -/
noncomputable def heavyReducedEntry (projection : Matrix (Fin size) (Fin size) ℝ)
    (heavyAtom rowAtom colAtom : Fin size) : ℝ :=
  projection rowAtom colAtom
    - projection heavyAtom rowAtom * projection heavyAtom colAtom
      / projection heavyAtom heavyAtom

/-- The deflated chart is symmetric. -/
theorem heavyReducedEntry_symm
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (heavyAtom rowAtom colAtom : Fin size) :
    heavyReducedEntry projection heavyAtom rowAtom colAtom
      = heavyReducedEntry projection heavyAtom colAtom rowAtom := by
  have hentry := congrFun (congrFun hdata.isSymmetric colAtom) rowAtom
  rw [Matrix.transpose_apply] at hentry
  rw [heavyReducedEntry, heavyReducedEntry, hentry]
  ring

/-- The heavy row of the deflated chart vanishes. -/
theorem heavyReducedEntry_heavy_row {heavyAtom : Fin size}
    (hdiag : projection heavyAtom heavyAtom ≠ 0) (colAtom : Fin size) :
    heavyReducedEntry projection heavyAtom heavyAtom colAtom = 0 := by
  have hcancel : projection heavyAtom heavyAtom * projection heavyAtom colAtom
      / projection heavyAtom heavyAtom = projection heavyAtom colAtom := by
    field_simp
  rw [heavyReducedEntry, hcancel, sub_self]

/-- **THE DEFLATED ROW SQUARE.**  The deflated chart is idempotent again:
each row square reads its own diagonal entry. -/
theorem heavyReducedEntry_row_square
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {heavyAtom : Fin size}
    (hdiag : projection heavyAtom heavyAtom ≠ 0) (rowAtom : Fin size) :
    ∑ colAtom : Fin size, heavyReducedEntry projection heavyAtom rowAtom colAtom
        * heavyReducedEntry projection heavyAtom rowAtom colAtom
      = heavyReducedEntry projection heavyAtom rowAtom rowAtom := by
  have hrowRow := projection_row_product hdata rowAtom rowAtom
  have hrowHeavy := projection_row_product hdata heavyAtom rowAtom
  have hheavyHeavy := projection_row_product hdata heavyAtom heavyAtom
  have hterm : ∀ colAtom : Fin size,
      heavyReducedEntry projection heavyAtom rowAtom colAtom
        * heavyReducedEntry projection heavyAtom rowAtom colAtom
      = 1 * (projection rowAtom colAtom * projection rowAtom colAtom)
        + (-(2 * (projection heavyAtom rowAtom / projection heavyAtom heavyAtom)))
          * (projection heavyAtom colAtom * projection rowAtom colAtom)
        + ((projection heavyAtom rowAtom / projection heavyAtom heavyAtom)
            * (projection heavyAtom rowAtom / projection heavyAtom heavyAtom))
          * (projection heavyAtom colAtom * projection heavyAtom colAtom) := by
    intro colAtom
    rw [heavyReducedEntry]
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun colAtom _ => hterm colAtom), Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    hrowRow, hrowHeavy, hheavyHeavy, heavyReducedEntry]
  field_simp
  ring

/-- The deflated row drops two off-diagonal squares below the diagonal
slack. -/
theorem heavyReducedEntry_row_pair_le
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {heavyAtom : Fin size}
    (hdiag : projection heavyAtom heavyAtom ≠ 0)
    {rowAtom colOne colTwo : Fin size} (hrowOne : rowAtom ≠ colOne)
    (hrowTwo : rowAtom ≠ colTwo) (hcols : colOne ≠ colTwo) :
    heavyReducedEntry projection heavyAtom rowAtom colOne
        * heavyReducedEntry projection heavyAtom rowAtom colOne
      + heavyReducedEntry projection heavyAtom rowAtom colTwo
        * heavyReducedEntry projection heavyAtom rowAtom colTwo
      ≤ heavyReducedEntry projection heavyAtom rowAtom rowAtom
        - heavyReducedEntry projection heavyAtom rowAtom rowAtom
          * heavyReducedEntry projection heavyAtom rowAtom rowAtom := by
  classical
  have hsquare := heavyReducedEntry_row_square hdata hdiag rowAtom
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin size))
    (fun colAtom => heavyReducedEntry projection heavyAtom rowAtom colAtom
      * heavyReducedEntry projection heavyAtom rowAtom colAtom)
    (Finset.mem_univ rowAtom)
  have hsubset : ({colOne, colTwo} : Finset (Fin size))
      ⊆ Finset.univ.erase rowAtom := by
    intro colAtom hmem
    rcases Finset.mem_insert.mp hmem with heq | hlast
    · exact Finset.mem_erase.mpr ⟨heq ▸ Ne.symm hrowOne, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr
        ⟨(Finset.mem_singleton.mp hlast) ▸ Ne.symm hrowTwo, Finset.mem_univ _⟩
  have hpair : ∑ colAtom ∈ ({colOne, colTwo} : Finset (Fin size)),
      heavyReducedEntry projection heavyAtom rowAtom colAtom
        * heavyReducedEntry projection heavyAtom rowAtom colAtom
      = heavyReducedEntry projection heavyAtom rowAtom colOne
          * heavyReducedEntry projection heavyAtom rowAtom colOne
        + heavyReducedEntry projection heavyAtom rowAtom colTwo
          * heavyReducedEntry projection heavyAtom rowAtom colTwo := by
    rw [Finset.sum_insert (by simpa using hcols), Finset.sum_singleton]
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun colAtom _ _ => mul_self_nonneg
      (heavyReducedEntry projection heavyAtom rowAtom colAtom))
  rw [hpair] at hmono
  linarith [hsquare, hsplit, hmono]

/-- **THE DEFLATED TRACE.**  Removing the heavy row costs exactly one
unit of trace. -/
theorem heavyReducedEntry_trace
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {heavyAtom : Fin size}
    (hdiag : projection heavyAtom heavyAtom ≠ 0) :
    ∑ rowAtom : Fin size, heavyReducedEntry projection heavyAtom rowAtom rowAtom
      = (rank : ℝ) - 1 := by
  have htrace : ∑ rowAtom : Fin size, projection rowAtom rowAtom = (rank : ℝ) := by
    rw [← hdata.hasTraceRank, Matrix.trace]
    rfl
  have hheavy := projection_row_product hdata heavyAtom heavyAtom
  have hterm : ∀ rowAtom : Fin size,
      heavyReducedEntry projection heavyAtom rowAtom rowAtom
      = 1 * projection rowAtom rowAtom
        + (-(1 / projection heavyAtom heavyAtom))
          * (projection heavyAtom rowAtom * projection heavyAtom rowAtom) := by
    intro rowAtom
    rw [heavyReducedEntry]
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun rowAtom _ => hterm rowAtom), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, htrace, hheavy]
  field_simp
  ring

/-! ## Layer 3 — the deflated form bounds -/

/-- **THE DEFLATED FORM IS NONNEGATIVE.**  The three-atom deflated form
is the chart form minus the heavy Cauchy–Schwarz defect. -/
theorem heavyReducedEntry_triple_nonneg
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {heavyAtom : Fin size}
    (hdiag : 0 < projection heavyAtom heavyAtom)
    {atomX atomY atomZ : Fin size} (hXY : atomX ≠ atomY) (hXZ : atomX ≠ atomZ)
    (hYZ : atomY ≠ atomZ) (coeffX coeffY coeffZ : ℝ) :
    0 ≤ coeffX * (heavyReducedEntry projection heavyAtom atomX atomX * coeffX
          + heavyReducedEntry projection heavyAtom atomX atomY * coeffY
          + heavyReducedEntry projection heavyAtom atomX atomZ * coeffZ)
      + coeffY * (heavyReducedEntry projection heavyAtom atomY atomX * coeffX
          + heavyReducedEntry projection heavyAtom atomY atomY * coeffY
          + heavyReducedEntry projection heavyAtom atomY atomZ * coeffZ)
      + coeffZ * (heavyReducedEntry projection heavyAtom atomZ atomX * coeffX
          + heavyReducedEntry projection heavyAtom atomZ atomY * coeffY
          + heavyReducedEntry projection heavyAtom atomZ atomZ * coeffZ) := by
  set probe := tripleLift atomX atomY atomZ coeffX coeffY coeffZ with hprobe
  have hform := tripleLift_dotProduct_mulVec (size := size) hXY hXZ hYZ projection
    coeffX coeffY coeffZ
  have hheavyRow : (projection *ᵥ probe) heavyAtom
      = projection heavyAtom atomX * coeffX + projection heavyAtom atomY * coeffY
        + projection heavyAtom atomZ * coeffZ := by
    have hstep : (projection *ᵥ probe) heavyAtom
        = ∑ colAtom : Fin size, projection heavyAtom colAtom * probe colAtom := rfl
    rw [hstep, hprobe]
    have hnotX : atomX ∉ ({atomY, atomZ} : Finset (Fin size)) := by
      intro hmem
      rcases Finset.mem_insert.mp hmem with heq | hrest
      · exact hXY heq
      · exact hXZ (Finset.mem_singleton.mp hrest)
    have hnotY : atomY ∉ ({atomZ} : Finset (Fin size)) := fun hmem =>
      hYZ (Finset.mem_singleton.mp hmem)
    have hsum : (∑ colAtom : Fin size, projection heavyAtom colAtom
          * tripleLift atomX atomY atomZ coeffX coeffY coeffZ colAtom)
        = ∑ colAtom ∈ ({atomX, atomY, atomZ} : Finset (Fin size)),
            projection heavyAtom colAtom
              * tripleLift atomX atomY atomZ coeffX coeffY coeffZ colAtom := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro colAtom _ hnot
      obtain ⟨hux, huy, huz⟩ := notMem_triple.mp hnot
      rw [tripleLift_apply_off hux huy huz, mul_zero]
    rw [hsum, Finset.sum_insert hnotX, Finset.sum_insert hnotY, Finset.sum_singleton,
      tripleLift_apply_first, tripleLift_apply_second hXY,
      tripleLift_apply_third hXZ hYZ]
    ring
  have hcs := chart_heavy_row_cauchy_schwarz hdata heavyAtom probe
  rw [hheavyRow] at hcs
  have hbridge : coeffX * (heavyReducedEntry projection heavyAtom atomX atomX * coeffX
          + heavyReducedEntry projection heavyAtom atomX atomY * coeffY
          + heavyReducedEntry projection heavyAtom atomX atomZ * coeffZ)
      + coeffY * (heavyReducedEntry projection heavyAtom atomY atomX * coeffX
          + heavyReducedEntry projection heavyAtom atomY atomY * coeffY
          + heavyReducedEntry projection heavyAtom atomY atomZ * coeffZ)
      + coeffZ * (heavyReducedEntry projection heavyAtom atomZ atomX * coeffX
          + heavyReducedEntry projection heavyAtom atomZ atomY * coeffY
          + heavyReducedEntry projection heavyAtom atomZ atomZ * coeffZ)
      = probe ⬝ᵥ (projection *ᵥ probe)
        - (projection heavyAtom atomX * coeffX + projection heavyAtom atomY * coeffY
            + projection heavyAtom atomZ * coeffZ)
          * (projection heavyAtom atomX * coeffX + projection heavyAtom atomY * coeffY
            + projection heavyAtom atomZ * coeffZ)
          / projection heavyAtom heavyAtom := by
    rw [hform]
    simp only [heavyReducedEntry]
    field_simp
    ring
  rw [hbridge]
  rw [sub_nonneg, div_le_iff₀ hdiag]
  nlinarith [hcs]

/-- **THE DEFLATED FORM IS A CONTRACTION.**  The deflated three-atom
form never exceeds the raw square of the coefficients. -/
theorem heavyReducedEntry_triple_le_self
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {heavyAtom : Fin size}
    (hdiag : 0 < projection heavyAtom heavyAtom)
    {atomX atomY atomZ : Fin size} (hXY : atomX ≠ atomY) (hXZ : atomX ≠ atomZ)
    (hYZ : atomY ≠ atomZ) (coeffX coeffY coeffZ : ℝ) :
    coeffX * (heavyReducedEntry projection heavyAtom atomX atomX * coeffX
          + heavyReducedEntry projection heavyAtom atomX atomY * coeffY
          + heavyReducedEntry projection heavyAtom atomX atomZ * coeffZ)
      + coeffY * (heavyReducedEntry projection heavyAtom atomY atomX * coeffX
          + heavyReducedEntry projection heavyAtom atomY atomY * coeffY
          + heavyReducedEntry projection heavyAtom atomY atomZ * coeffZ)
      + coeffZ * (heavyReducedEntry projection heavyAtom atomZ atomX * coeffX
          + heavyReducedEntry projection heavyAtom atomZ atomY * coeffY
          + heavyReducedEntry projection heavyAtom atomZ atomZ * coeffZ)
      ≤ coeffX * coeffX + coeffY * coeffY + coeffZ * coeffZ := by
  set probe := tripleLift atomX atomY atomZ coeffX coeffY coeffZ with hprobe
  have hform := tripleLift_dotProduct_mulVec (size := size) hXY hXZ hYZ projection
    coeffX coeffY coeffZ
  have hself := tripleLift_dotProduct_self (size := size) hXY hXZ hYZ coeffX coeffY coeffZ
  have hcontract := chart_quadratic_le_self hdata probe
  rw [hprobe] at hcontract
  rw [hform, hself] at hcontract
  have hdefect : (0 : ℝ)
      ≤ (projection heavyAtom atomX * coeffX + projection heavyAtom atomY * coeffY
          + projection heavyAtom atomZ * coeffZ)
        * (projection heavyAtom atomX * coeffX + projection heavyAtom atomY * coeffY
          + projection heavyAtom atomZ * coeffZ)
        / projection heavyAtom heavyAtom :=
    div_nonneg (mul_self_nonneg _) hdiag.le
  have hbridge : coeffX * (heavyReducedEntry projection heavyAtom atomX atomX * coeffX
          + heavyReducedEntry projection heavyAtom atomX atomY * coeffY
          + heavyReducedEntry projection heavyAtom atomX atomZ * coeffZ)
      + coeffY * (heavyReducedEntry projection heavyAtom atomY atomX * coeffX
          + heavyReducedEntry projection heavyAtom atomY atomY * coeffY
          + heavyReducedEntry projection heavyAtom atomY atomZ * coeffZ)
      + coeffZ * (heavyReducedEntry projection heavyAtom atomZ atomX * coeffX
          + heavyReducedEntry projection heavyAtom atomZ atomY * coeffY
          + heavyReducedEntry projection heavyAtom atomZ atomZ * coeffZ)
      = (coeffX * (projection atomX atomX * coeffX + projection atomX atomY * coeffY
            + projection atomX atomZ * coeffZ)
        + coeffY * (projection atomY atomX * coeffX + projection atomY atomY * coeffY
            + projection atomY atomZ * coeffZ)
        + coeffZ * (projection atomZ atomX * coeffX + projection atomZ atomY * coeffY
            + projection atomZ atomZ * coeffZ))
        - (projection heavyAtom atomX * coeffX + projection heavyAtom atomY * coeffY
            + projection heavyAtom atomZ * coeffZ)
          * (projection heavyAtom atomX * coeffX + projection heavyAtom atomY * coeffY
            + projection heavyAtom atomZ * coeffZ)
          / projection heavyAtom heavyAtom := by
    simp only [heavyReducedEntry]
    field_simp
    ring
  rw [hbridge]
  linarith [hcontract, hdefect]

/-! ## Layer 4 — the collapsed block system -/

/-- The atom triple with its last two entries exchanged. -/
theorem triple_swap_last {α : Type*} [DecidableEq α] (first second third : α) :
    ({first, second, third} : Finset α) = {first, third, second} := by
  ext atomIndex
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **THE COLLAPSED BLOCK ROW.**  At a heavy atom of vanishing shifted
weight the heavy row of the block eigen system is the orthogonality of
the direction to the heavy chart row.  Every other block row then reads
the two-by-two deflated system on the two non-heavy atoms. -/
theorem heavy_block_reduced_row
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {heavyAtom atomOne atomTwo : Fin size} (hOneTwo : atomOne ≠ atomTwo)
    (hHeavyOne : heavyAtom ≠ atomOne) (hHeavyTwo : heavyAtom ≠ atomTwo)
    (hsupport : datumTightSupport tightDir label = {heavyAtom, atomOne, atomTwo})
    (hheavy : value + weight heavyAtom = 0)
    (hdiag : projection heavyAtom heavyAtom ≠ 0) :
    (heavyReducedEntry projection heavyAtom atomOne atomOne
          - (value + weight atomOne)) * tightDir label atomOne
      + heavyReducedEntry projection heavyAtom atomOne atomTwo
        * tightDir label atomTwo = 0 := by
  have hmemHeavy : heavyAtom ∈ ({heavyAtom, atomOne, atomTwo} : Finset (Fin size)) :=
    Finset.mem_insert_self _ _
  have hmemOne : atomOne ∈ ({heavyAtom, atomOne, atomTwo} : Finset (Fin size)) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hrowHeavy := block_eigen_row hdata hmem hHeavyOne hHeavyTwo hOneTwo hsupport
    hmemHeavy
  have hrowOne := block_eigen_row hdata hmem hHeavyOne hHeavyTwo hOneTwo hsupport
    hmemOne
  have hgapHeavyHeavy : chartStationaryGap projection weight heavyAtom heavyAtom
      = projection heavyAtom heavyAtom - weight heavyAtom := by
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_eq]
  have hgapHeavyOne : chartStationaryGap projection weight heavyAtom atomOne
      = projection heavyAtom atomOne := by
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hHeavyOne,
      sub_zero]
  have hgapHeavyTwo : chartStationaryGap projection weight heavyAtom atomTwo
      = projection heavyAtom atomTwo := by
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hHeavyTwo,
      sub_zero]
  have hgapOneHeavy : chartStationaryGap projection weight atomOne heavyAtom
      = projection heavyAtom atomOne := by
    rw [gap_entry_symm hdata atomOne heavyAtom, hgapHeavyOne]
  have hgapOneOne : chartStationaryGap projection weight atomOne atomOne
      = projection atomOne atomOne - weight atomOne := by
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_eq]
  have hgapOneTwo : chartStationaryGap projection weight atomOne atomTwo
      = projection atomOne atomTwo := by
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hOneTwo,
      sub_zero]
  rw [hgapHeavyHeavy, hgapHeavyOne, hgapHeavyTwo] at hrowHeavy
  rw [hgapOneHeavy, hgapOneOne, hgapOneTwo] at hrowOne
  have hexpandDiag : heavyReducedEntry projection heavyAtom atomOne atomOne
      * projection heavyAtom heavyAtom
      = projection atomOne atomOne * projection heavyAtom heavyAtom
        - projection heavyAtom atomOne * projection heavyAtom atomOne := by
    rw [heavyReducedEntry]
    field_simp
  have hexpandOff : heavyReducedEntry projection heavyAtom atomOne atomTwo
      * projection heavyAtom heavyAtom
      = projection atomOne atomTwo * projection heavyAtom heavyAtom
        - projection heavyAtom atomOne * projection heavyAtom atomTwo := by
    rw [heavyReducedEntry]
    field_simp
  have hproduct : ((heavyReducedEntry projection heavyAtom atomOne atomOne
        - (value + weight atomOne)) * tightDir label atomOne
      + heavyReducedEntry projection heavyAtom atomOne atomTwo
        * tightDir label atomTwo) * projection heavyAtom heavyAtom = 0 := by
    linear_combination (tightDir label atomOne) * hexpandDiag
      + (tightDir label atomTwo) * hexpandOff
      + (projection heavyAtom heavyAtom) * hrowOne
      - (projection heavyAtom atomOne) * hrowHeavy
      - (projection heavyAtom atomOne) * (tightDir label heavyAtom) * hheavy
  rcases mul_eq_zero.mp hproduct with hcase | hcase
  · exact hcase
  · exact absurd hcase hdiag

/-- **THE COLLAPSED BLOCK MINOR.**  The two-by-two deflated system of a
block is singular. -/
theorem heavy_block_reduced_minor
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {heavyAtom atomOne atomTwo : Fin size} (hOneTwo : atomOne ≠ atomTwo)
    (hHeavyOne : heavyAtom ≠ atomOne) (hHeavyTwo : heavyAtom ≠ atomTwo)
    (hsupport : datumTightSupport tightDir label = {heavyAtom, atomOne, atomTwo})
    (hheavy : value + weight heavyAtom = 0)
    (hdiag : projection heavyAtom heavyAtom ≠ 0) :
    (heavyReducedEntry projection heavyAtom atomOne atomOne
          - (value + weight atomOne))
        * (heavyReducedEntry projection heavyAtom atomTwo atomTwo
          - (value + weight atomTwo))
      = heavyReducedEntry projection heavyAtom atomOne atomTwo
        * heavyReducedEntry projection heavyAtom atomOne atomTwo := by
  have hrowOne := heavy_block_reduced_row hdata hmem hOneTwo hHeavyOne hHeavyTwo
    hsupport hheavy hdiag
  have hrowTwo := heavy_block_reduced_row hdata hmem (Ne.symm hOneTwo) hHeavyTwo
    hHeavyOne (by rw [hsupport, triple_swap_last]) hheavy hdiag
  have hsymmetric : heavyReducedEntry projection heavyAtom atomTwo atomOne
      = heavyReducedEntry projection heavyAtom atomOne atomTwo :=
    heavyReducedEntry_symm hdata heavyAtom atomTwo atomOne
  rw [hsymmetric] at hrowTwo
  have hcoordOne : tightDir label atomOne ≠ 0 :=
    tightDir_ne_zero_of_support_triple hsupport
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hproduct : ((heavyReducedEntry projection heavyAtom atomOne atomOne
          - (value + weight atomOne))
        * (heavyReducedEntry projection heavyAtom atomTwo atomTwo
          - (value + weight atomTwo))
      - heavyReducedEntry projection heavyAtom atomOne atomTwo
        * heavyReducedEntry projection heavyAtom atomOne atomTwo)
      * tightDir label atomOne = 0 := by
    linear_combination (heavyReducedEntry projection heavyAtom atomTwo atomTwo
        - (value + weight atomTwo)) * hrowOne
      - heavyReducedEntry projection heavyAtom atomOne atomTwo * hrowTwo
  rcases mul_eq_zero.mp hproduct with hcase | hcase
  · linarith [hcase]
  · exact absurd hcase hcoordOne

/-- **THE COLLAPSED BLOCK PROPAGATION.**  A vanishing deflated diagonal
entry at one atom of a block forces the whole two-by-two corner of that
block to vanish. -/
theorem heavy_block_reduced_propagate
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {heavyAtom atomOne atomTwo : Fin size} (hOneTwo : atomOne ≠ atomTwo)
    (hHeavyOne : heavyAtom ≠ atomOne) (hHeavyTwo : heavyAtom ≠ atomTwo)
    (hsupport : datumTightSupport tightDir label = {heavyAtom, atomOne, atomTwo})
    (hheavy : value + weight heavyAtom = 0)
    (hdiag : projection heavyAtom heavyAtom ≠ 0)
    (hzero : heavyReducedEntry projection heavyAtom atomOne atomOne
      - (value + weight atomOne) = 0) :
    heavyReducedEntry projection heavyAtom atomTwo atomTwo
      - (value + weight atomTwo) = 0 := by
  have hminor := heavy_block_reduced_minor hdata hmem hOneTwo hHeavyOne hHeavyTwo
    hsupport hheavy hdiag
  have hoff : heavyReducedEntry projection heavyAtom atomOne atomTwo = 0 := by
    have hsq : heavyReducedEntry projection heavyAtom atomOne atomTwo
        * heavyReducedEntry projection heavyAtom atomOne atomTwo = 0 := by
      rw [← hminor, hzero, zero_mul]
    exact by nlinarith [hsq, sq_nonneg (heavyReducedEntry projection heavyAtom atomOne
      atomTwo)]
  have hrowTwo := heavy_block_reduced_row hdata hmem (Ne.symm hOneTwo) hHeavyTwo
    hHeavyOne (by rw [hsupport, triple_swap_last]) hheavy hdiag
  have hsymmetric : heavyReducedEntry projection heavyAtom atomTwo atomOne
      = heavyReducedEntry projection heavyAtom atomOne atomTwo :=
    heavyReducedEntry_symm hdata heavyAtom atomTwo atomOne
  rw [hsymmetric, hoff, zero_mul, add_zero] at hrowTwo
  have hcoordTwo : tightDir label atomTwo ≠ 0 :=
    tightDir_ne_zero_of_support_triple hsupport
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  rcases mul_eq_zero.mp hrowTwo with hcase | hcase
  · exact hcase
  · exact absurd hcase hcoordTwo

/-- **THE DOUBLED-BLOCK KILL.**  Two basis slots on one block with a
nonzero cross determinant annihilate the whole deflated corner of that
block. -/
theorem heavy_doubled_block_corner_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {labelOne labelTwo : activeIndex} (hmemOne : labelOne ∈ activeSet)
    (hmemTwo : labelTwo ∈ activeSet)
    {heavyAtom atomOne atomTwo : Fin size} (hOneTwo : atomOne ≠ atomTwo)
    (hHeavyOne : heavyAtom ≠ atomOne) (hHeavyTwo : heavyAtom ≠ atomTwo)
    (hsupportOne : datumTightSupport tightDir labelOne = {heavyAtom, atomOne, atomTwo})
    (hsupportTwo : datumTightSupport tightDir labelTwo = {heavyAtom, atomOne, atomTwo})
    (hheavy : value + weight heavyAtom = 0)
    (hdiag : projection heavyAtom heavyAtom ≠ 0)
    (hcross : tightDir labelOne atomOne * tightDir labelTwo atomTwo
      - tightDir labelOne atomTwo * tightDir labelTwo atomOne ≠ 0) :
    heavyReducedEntry projection heavyAtom atomOne atomOne
        - (value + weight atomOne) = 0
      ∧ heavyReducedEntry projection heavyAtom atomTwo atomTwo
        - (value + weight atomTwo) = 0
      ∧ heavyReducedEntry projection heavyAtom atomOne atomTwo = 0 := by
  have hrowOne := heavy_block_reduced_row hdata hmemOne hOneTwo hHeavyOne hHeavyTwo
    hsupportOne hheavy hdiag
  have hrowTwo := heavy_block_reduced_row hdata hmemTwo hOneTwo hHeavyOne hHeavyTwo
    hsupportTwo hheavy hdiag
  have hdiagZero : heavyReducedEntry projection heavyAtom atomOne atomOne
      - (value + weight atomOne) = 0 := by
    have hproduct : (heavyReducedEntry projection heavyAtom atomOne atomOne
          - (value + weight atomOne))
        * (tightDir labelOne atomOne * tightDir labelTwo atomTwo
          - tightDir labelOne atomTwo * tightDir labelTwo atomOne) = 0 := by
      linear_combination (tightDir labelTwo atomTwo) * hrowOne
        - (tightDir labelOne atomTwo) * hrowTwo
    rcases mul_eq_zero.mp hproduct with hcase | hcase
    · exact hcase
    · exact absurd hcase hcross
  have hoffZero : heavyReducedEntry projection heavyAtom atomOne atomTwo = 0 := by
    have hproduct : heavyReducedEntry projection heavyAtom atomOne atomTwo
        * (tightDir labelOne atomOne * tightDir labelTwo atomTwo
          - tightDir labelOne atomTwo * tightDir labelTwo atomOne) = 0 := by
      linear_combination (tightDir labelOne atomOne) * hrowTwo
        - (tightDir labelTwo atomOne) * hrowOne
    rcases mul_eq_zero.mp hproduct with hcase | hcase
    · exact hcase
    · exact absurd hcase hcross
  refine ⟨hdiagZero, ?_, hoffZero⟩
  exact heavy_block_reduced_propagate hdata hmemOne hOneTwo hHeavyOne hHeavyTwo
    hsupportOne hheavy hdiag hdiagZero

/-! ## Layer 5 — the triangle trace cap -/

/-- **THE TRIANGLE TRACE CAP.**  A three-atom corner of a symmetric
contraction whose three shifted pair minors vanish, whose shifts are
nonnegative and whose shifted diagonal is positive, has a shifted trace
of at most one.

The proof runs on one probe.  The three off-diagonal products fix the
probe `(m₁₂m₁₃, m₁₂m₂₃, m₁₃m₂₃)`, whose square coordinates are the
shifted diagonal entries times their product.  The cube of the three
off-diagonal entries squares to the cube of the shifted diagonal, thus
the probe form is either the full square of the trace or its reflection.
The first case reads the contraction, the second reads the
nonnegativity, and the row squares close the residue. -/
theorem dense_triangle_trace_le_one
    {entryOneOne entryTwoTwo entryThreeThree : ℝ}
    {entryOneTwo entryOneThree entryTwoThree : ℝ}
    {shiftOne shiftTwo shiftThree : ℝ}
    (hshiftOne : 0 ≤ shiftOne) (hshiftTwo : 0 ≤ shiftTwo)
    (hshiftThree : 0 ≤ shiftThree)
    (hposOne : 0 < entryOneOne - shiftOne) (hposTwo : 0 < entryTwoTwo - shiftTwo)
    (hposThree : 0 < entryThreeThree - shiftThree)
    (hminorOneTwo : (entryOneOne - shiftOne) * (entryTwoTwo - shiftTwo)
      = entryOneTwo * entryOneTwo)
    (hminorOneThree : (entryOneOne - shiftOne) * (entryThreeThree - shiftThree)
      = entryOneThree * entryOneThree)
    (hminorTwoThree : (entryTwoTwo - shiftTwo) * (entryThreeThree - shiftThree)
      = entryTwoThree * entryTwoThree)
    (hrowOne : entryOneTwo * entryOneTwo + entryOneThree * entryOneThree
      ≤ entryOneOne - entryOneOne * entryOneOne)
    (hrowTwo : entryOneTwo * entryOneTwo + entryTwoThree * entryTwoThree
      ≤ entryTwoTwo - entryTwoTwo * entryTwoTwo)
    (hrowThree : entryOneThree * entryOneThree + entryTwoThree * entryTwoThree
      ≤ entryThreeThree - entryThreeThree * entryThreeThree)
    (hnonneg : ∀ coeffOne coeffTwo coeffThree : ℝ,
      0 ≤ coeffOne * (entryOneOne * coeffOne + entryOneTwo * coeffTwo
            + entryOneThree * coeffThree)
        + coeffTwo * (entryOneTwo * coeffOne + entryTwoTwo * coeffTwo
            + entryTwoThree * coeffThree)
        + coeffThree * (entryOneThree * coeffOne + entryTwoThree * coeffTwo
            + entryThreeThree * coeffThree))
    (hcontract : ∀ coeffOne coeffTwo coeffThree : ℝ,
      coeffOne * (entryOneOne * coeffOne + entryOneTwo * coeffTwo
            + entryOneThree * coeffThree)
        + coeffTwo * (entryOneTwo * coeffOne + entryTwoTwo * coeffTwo
            + entryTwoThree * coeffThree)
        + coeffThree * (entryOneThree * coeffOne + entryTwoThree * coeffTwo
            + entryThreeThree * coeffThree)
        ≤ coeffOne * coeffOne + coeffTwo * coeffTwo + coeffThree * coeffThree) :
    (entryOneOne - shiftOne) + (entryTwoTwo - shiftTwo)
      + (entryThreeThree - shiftThree) ≤ 1 := by
  set shiftedOne : ℝ := entryOneOne - shiftOne with hshiftedOne
  set shiftedTwo : ℝ := entryTwoTwo - shiftTwo with hshiftedTwo
  set shiftedThree : ℝ := entryThreeThree - shiftThree with hshiftedThree
  set traceSum : ℝ := shiftedOne + shiftedTwo + shiftedThree with htraceSum
  set massProduct : ℝ := shiftedOne * shiftedTwo * shiftedThree with hmassProduct
  set offProduct : ℝ := entryOneTwo * entryOneThree * entryTwoThree with hoffProduct
  have hmassPos : 0 < massProduct := by
    rw [hmassProduct]
    exact mul_pos (mul_pos hposOne hposTwo) hposThree
  have htracePos : 0 < traceSum := by
    rw [htraceSum]
    linarith [hposOne, hposTwo, hposThree]
  -- the three probe coordinates
  set probeOne : ℝ := entryOneTwo * entryOneThree with hprobeOne
  set probeTwo : ℝ := entryOneTwo * entryTwoThree with hprobeTwo
  set probeThree : ℝ := entryOneThree * entryTwoThree with hprobeThree
  clear_value shiftedOne shiftedTwo shiftedThree traceSum massProduct offProduct
    probeOne probeTwo probeThree
  have hsquareOne : probeOne * probeOne = massProduct * shiftedOne := by
    have hrewrite : probeOne * probeOne
        = (entryOneTwo * entryOneTwo) * (entryOneThree * entryOneThree) := by
      rw [hprobeOne]; ring
    rw [hrewrite, ← hminorOneTwo, ← hminorOneThree, hmassProduct]; ring
  have hsquareTwo : probeTwo * probeTwo = massProduct * shiftedTwo := by
    have hrewrite : probeTwo * probeTwo
        = (entryOneTwo * entryOneTwo) * (entryTwoThree * entryTwoThree) := by
      rw [hprobeTwo]; ring
    rw [hrewrite, ← hminorOneTwo, ← hminorTwoThree, hmassProduct]; ring
  have hsquareThree : probeThree * probeThree = massProduct * shiftedThree := by
    have hrewrite : probeThree * probeThree
        = (entryOneThree * entryOneThree) * (entryTwoThree * entryTwoThree) := by
      rw [hprobeThree]; ring
    rw [hrewrite, ← hminorOneThree, ← hminorTwoThree, hmassProduct]; ring
  have hcrossOneTwo : entryOneTwo * (probeOne * probeTwo)
      = (shiftedOne * shiftedTwo) * offProduct := by
    have hrewrite : entryOneTwo * (probeOne * probeTwo)
        = (entryOneTwo * entryOneTwo)
          * (entryOneTwo * entryOneThree * entryTwoThree) := by
      rw [hprobeOne, hprobeTwo]; ring
    rw [hrewrite, ← hminorOneTwo, hoffProduct, hprobeOne]
  have hcrossOneThree : entryOneThree * (probeOne * probeThree)
      = (shiftedOne * shiftedThree) * offProduct := by
    have hrewrite : entryOneThree * (probeOne * probeThree)
        = (entryOneThree * entryOneThree)
          * (entryOneTwo * entryOneThree * entryTwoThree) := by
      rw [hprobeOne, hprobeThree]; ring
    rw [hrewrite, ← hminorOneThree, hoffProduct, hprobeOne]
  have hcrossTwoThree : entryTwoThree * (probeTwo * probeThree)
      = (shiftedTwo * shiftedThree) * offProduct := by
    have hrewrite : entryTwoThree * (probeTwo * probeThree)
        = (entryTwoThree * entryTwoThree)
          * (entryOneTwo * entryOneThree * entryTwoThree) := by
      rw [hprobeTwo, hprobeThree]; ring
    rw [hrewrite, ← hminorTwoThree, hoffProduct, hprobeOne]
  -- the probe form
  have hprobeForm : probeOne * (entryOneOne * probeOne + entryOneTwo * probeTwo
          + entryOneThree * probeThree)
      + probeTwo * (entryOneTwo * probeOne + entryTwoTwo * probeTwo
          + entryTwoThree * probeThree)
      + probeThree * (entryOneThree * probeOne + entryTwoThree * probeTwo
          + entryThreeThree * probeThree)
      = massProduct * (entryOneOne * shiftedOne + entryTwoTwo * shiftedTwo
          + entryThreeThree * shiftedThree)
        + 2 * offProduct * (shiftedOne * shiftedTwo + shiftedOne * shiftedThree
          + shiftedTwo * shiftedThree) := by
    linear_combination entryOneOne * hsquareOne + entryTwoTwo * hsquareTwo
      + entryThreeThree * hsquareThree + 2 * hcrossOneTwo + 2 * hcrossOneThree
      + 2 * hcrossTwoThree
  have hprobeSelf : probeOne * probeOne + probeTwo * probeTwo
      + probeThree * probeThree = massProduct * traceSum := by
    rw [hsquareOne, hsquareTwo, hsquareThree, htraceSum]; ring
  -- the sign dichotomy of the off-diagonal product
  have hsignSquare : (offProduct - massProduct) * (offProduct + massProduct) = 0 := by
    have hoffSquare : offProduct * offProduct = massProduct * massProduct := by
      have hrewrite : offProduct * offProduct
          = (entryOneTwo * entryOneTwo) * (entryOneThree * entryOneThree)
            * (entryTwoThree * entryTwoThree) := by
        rw [hoffProduct, hprobeOne]; ring
      rw [hrewrite, ← hminorOneTwo, ← hminorOneThree, ← hminorTwoThree, hmassProduct]
      ring
    linear_combination hoffSquare
  -- the entry dictionary and the shifted row inequalities
  have hentryOne : entryOneOne = shiftedOne + shiftOne := by rw [hshiftedOne]; ring
  have hentryTwo : entryTwoTwo = shiftedTwo + shiftTwo := by rw [hshiftedTwo]; ring
  have hentryThree : entryThreeThree = shiftedThree + shiftThree := by
    rw [hshiftedThree]; ring
  have hrowShiftedOne : shiftOne * (2 * shiftedOne + shiftOne - 1)
      ≤ shiftedOne * (1 - traceSum) := by
    have hkey : shiftedOne * shiftedTwo + shiftedOne * shiftedThree
        ≤ entryOneOne - entryOneOne * entryOneOne := by
      rw [hminorOneTwo, hminorOneThree]
      exact hrowOne
    rw [hentryOne] at hkey
    rw [htraceSum]
    linarith only [hkey]
  have hrowShiftedTwo : shiftTwo * (2 * shiftedTwo + shiftTwo - 1)
      ≤ shiftedTwo * (1 - traceSum) := by
    have hkey : shiftedOne * shiftedTwo + shiftedTwo * shiftedThree
        ≤ entryTwoTwo - entryTwoTwo * entryTwoTwo := by
      rw [hminorOneTwo, hminorTwoThree]
      exact hrowTwo
    rw [hentryTwo] at hkey
    rw [htraceSum]
    linarith only [hkey]
  have hrowShiftedThree : shiftThree * (2 * shiftedThree + shiftThree - 1)
      ≤ shiftedThree * (1 - traceSum) := by
    have hkey : shiftedOne * shiftedThree + shiftedTwo * shiftedThree
        ≤ entryThreeThree - entryThreeThree * entryThreeThree := by
      rw [hminorOneThree, hminorTwoThree]
      exact hrowThree
    rw [hentryThree] at hkey
    rw [htraceSum]
    linarith only [hkey]
  rcases mul_eq_zero.mp hsignSquare with hplus | hminus
  · -- the aligned branch: the contraction reads the square of the trace
    have hoffEq : offProduct = massProduct := by linarith [hplus]
    have hcap := hcontract probeOne probeTwo probeThree
    rw [hprobeForm, hoffEq, hprobeSelf] at hcap
    have hshifted : massProduct * (traceSum * traceSum
          + (shiftOne * shiftedOne + shiftTwo * shiftedTwo + shiftThree * shiftedThree))
        ≤ massProduct * traceSum := by
      have hrewrite : massProduct * (traceSum * traceSum
            + (shiftOne * shiftedOne + shiftTwo * shiftedTwo
              + shiftThree * shiftedThree))
          = massProduct * (entryOneOne * shiftedOne + entryTwoTwo * shiftedTwo
              + entryThreeThree * shiftedThree)
            + 2 * massProduct * (shiftedOne * shiftedTwo + shiftedOne * shiftedThree
              + shiftedTwo * shiftedThree) := by
        rw [hentryOne, hentryTwo, hentryThree, htraceSum]
        ring
      rw [hrewrite]
      linarith only [hcap]
    have hcancel : traceSum * traceSum
        + (shiftOne * shiftedOne + shiftTwo * shiftedTwo + shiftThree * shiftedThree)
        ≤ traceSum := le_of_mul_le_mul_left hshifted hmassPos
    have hmassOne : 0 ≤ shiftOne * shiftedOne := mul_nonneg hshiftOne hposOne.le
    have hmassTwo : 0 ≤ shiftTwo * shiftedTwo := mul_nonneg hshiftTwo hposTwo.le
    have hmassThree : 0 ≤ shiftThree * shiftedThree :=
      mul_nonneg hshiftThree hposThree.le
    nlinarith only [hcancel, hmassOne, hmassTwo, hmassThree, htracePos]
  · -- the reflected branch: the nonnegativity reads the doubled diagonal mass
    have hoffEq : offProduct = -massProduct := by linarith [hminus]
    have hfloor := hnonneg probeOne probeTwo probeThree
    rw [hprobeForm, hoffEq] at hfloor
    have hshifted : massProduct * 0 ≤ massProduct
        * (2 * (shiftedOne * shiftedOne + shiftedTwo * shiftedTwo
            + shiftedThree * shiftedThree)
          + (shiftOne * shiftedOne + shiftTwo * shiftedTwo + shiftThree * shiftedThree)
          - traceSum * traceSum) := by
      have hrewrite : massProduct
          * (2 * (shiftedOne * shiftedOne + shiftedTwo * shiftedTwo
              + shiftedThree * shiftedThree)
            + (shiftOne * shiftedOne + shiftTwo * shiftedTwo
              + shiftThree * shiftedThree)
            - traceSum * traceSum)
          = massProduct * (entryOneOne * shiftedOne + entryTwoTwo * shiftedTwo
              + entryThreeThree * shiftedThree)
            + 2 * (-massProduct) * (shiftedOne * shiftedTwo
              + shiftedOne * shiftedThree + shiftedTwo * shiftedThree) := by
        rw [hentryOne, hentryTwo, hentryThree, htraceSum]
        ring
      rw [hrewrite, mul_zero]
      exact hfloor
    have hcancel : (0 : ℝ) ≤ 2 * (shiftedOne * shiftedOne + shiftedTwo * shiftedTwo
          + shiftedThree * shiftedThree)
        + (shiftOne * shiftedOne + shiftTwo * shiftedTwo + shiftThree * shiftedThree)
        - traceSum * traceSum := le_of_mul_le_mul_left hshifted hmassPos
    by_cases hbigOne : 1 ≤ 2 * shiftedOne + shiftOne
    · have hfactor : 0 ≤ shiftOne * (2 * shiftedOne + shiftOne - 1) :=
        mul_nonneg hshiftOne (by linarith)
      have hprod : 0 ≤ shiftedOne * (1 - traceSum) := le_trans hfactor hrowShiftedOne
      nlinarith only [hprod, hposOne]
    by_cases hbigTwo : 1 ≤ 2 * shiftedTwo + shiftTwo
    · have hfactor : 0 ≤ shiftTwo * (2 * shiftedTwo + shiftTwo - 1) :=
        mul_nonneg hshiftTwo (by linarith)
      have hprod : 0 ≤ shiftedTwo * (1 - traceSum) := le_trans hfactor hrowShiftedTwo
      nlinarith only [hprod, hposTwo]
    by_cases hbigThree : 1 ≤ 2 * shiftedThree + shiftThree
    · have hfactor : 0 ≤ shiftThree * (2 * shiftedThree + shiftThree - 1) :=
        mul_nonneg hshiftThree (by linarith)
      have hprod : 0 ≤ shiftedThree * (1 - traceSum) :=
        le_trans hfactor hrowShiftedThree
      nlinarith only [hprod, hposThree]
    · have hltOne := not_le.mp hbigOne
      have hltTwo := not_le.mp hbigTwo
      have hltThree := not_le.mp hbigThree
      have hboundOne : shiftOne * shiftedOne ≤ shiftedOne * (1 - 2 * shiftedOne) := by
        nlinarith only [hposOne, hltOne]
      have hboundTwo : shiftTwo * shiftedTwo ≤ shiftedTwo * (1 - 2 * shiftedTwo) := by
        nlinarith only [hposTwo, hltTwo]
      have hboundThree : shiftThree * shiftedThree
          ≤ shiftedThree * (1 - 2 * shiftedThree) := by
        nlinarith only [hposThree, hltThree]
      rw [htraceSum] at hcancel
      have hsquare : traceSum * traceSum ≤ traceSum := by
        rw [htraceSum]
        linarith only [hcancel, hboundOne, hboundTwo, hboundThree]
      nlinarith only [hsquare, htracePos]

/-! ## Layer 6 — the rank-five heavy-five cells -/

/-- The chart diagonal at a heavy atom of vanishing shifted weight is
positive: the gap floor plus the negative chart value. -/
theorem RankFiveFrame.heavyFive_chart_diagonal_pos {crux : SixThreeCrux}
    (_frame : RankFiveFrame crux) {heavyAtom : Fin 6}
    (hheavy : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight heavyAtom = 0) :
    0 < (chartPointOfDesign crux.design).chart heavyAtom heavyAtom := by
  have hgap := crux.gap_diagonal_pos_of_allHeavy heavyAtom
  have hentry : chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight heavyAtom heavyAtom
      = (chartPointOfDesign crux.design).chart heavyAtom heavyAtom
        - (chartPointOfDesign crux.design).weight heavyAtom := by
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_eq]
  rw [hentry] at hgap
  have hneg := crux.hasNegativeChartValue
  linarith

/-- **THE TRIANGLE SUPPLY.**  Two double atoms that avoid one pair of
slots share a third slot, and that slot carries exactly the heavy atom
and the two of them. -/
theorem RankFiveFrame.heavyFive_exists_block_of_pair {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {heavyAtom atomOne atomTwo : Fin 6}
    (hthree : ∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3)
    (hfive : basisSupportMultiplicity frame.tightDir frame.basisLabel heavyAtom = 5)
    (hOneTwo : atomOne ≠ atomTwo) (hOneHeavy : atomOne ≠ heavyAtom)
    (hTwoHeavy : atomTwo ≠ heavyAtom)
    (hmultOne : basisSupportMultiplicity frame.tightDir frame.basisLabel atomOne = 2)
    (hmultTwo : basisSupportMultiplicity frame.tightDir frame.basisLabel atomTwo = 2)
    {slotP slotQ : Fin 5} (hslot : slotP ≠ slotQ)
    (hOneP : atomOne ∉ datumTightSupport frame.tightDir (frame.basisLabel slotP))
    (hOneQ : atomOne ∉ datumTightSupport frame.tightDir (frame.basisLabel slotQ))
    (hTwoP : atomTwo ∉ datumTightSupport frame.tightDir (frame.basisLabel slotP))
    (hTwoQ : atomTwo ∉ datumTightSupport frame.tightDir (frame.basisLabel slotQ)) :
    ∃ slotIndex : Fin 5, datumTightSupport frame.tightDir (frame.basisLabel slotIndex)
      = {heavyAtom, atomOne, atomTwo} := by
  classical
  have hcardOne : (Finset.univ.filter fun slotIndex : Fin 5 =>
      atomOne ∈ datumTightSupport frame.tightDir (frame.basisLabel slotIndex)).card
      = 2 := hmultOne
  have hcardTwo : (Finset.univ.filter fun slotIndex : Fin 5 =>
      atomTwo ∈ datumTightSupport frame.tightDir (frame.basisLabel slotIndex)).card
      = 2 := hmultTwo
  have hsubOne : (Finset.univ.filter fun slotIndex : Fin 5 =>
      atomOne ∈ datumTightSupport frame.tightDir (frame.basisLabel slotIndex))
      ⊆ (Finset.univ.erase slotP).erase slotQ := by
    intro slotIndex hmem
    have hcarry := (Finset.mem_filter.mp hmem).2
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
    · intro heq
      exact hOneQ (heq ▸ hcarry)
    · intro heq
      exact hOneP (heq ▸ hcarry)
  have hsubTwo : (Finset.univ.filter fun slotIndex : Fin 5 =>
      atomTwo ∈ datumTightSupport frame.tightDir (frame.basisLabel slotIndex))
      ⊆ (Finset.univ.erase slotP).erase slotQ := by
    intro slotIndex hmem
    have hcarry := (Finset.mem_filter.mp hmem).2
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
    · intro heq
      exact hTwoQ (heq ▸ hcarry)
    · intro heq
      exact hTwoP (heq ▸ hcarry)
  have hcardRest : ((Finset.univ.erase slotP).erase slotQ).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hslot,
      Finset.mem_univ _⟩), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  have hunion : ((Finset.univ.filter fun slotIndex : Fin 5 =>
        atomOne ∈ datumTightSupport frame.tightDir (frame.basisLabel slotIndex))
      ∪ Finset.univ.filter fun slotIndex : Fin 5 =>
        atomTwo ∈ datumTightSupport frame.tightDir (frame.basisLabel slotIndex)).card
      ≤ 3 := by
    rw [← hcardRest]
    exact Finset.card_le_card (Finset.union_subset hsubOne hsubTwo)
  have hinter := Finset.card_inter_add_card_union
    (Finset.univ.filter fun slotIndex : Fin 5 =>
      atomOne ∈ datumTightSupport frame.tightDir (frame.basisLabel slotIndex))
    (Finset.univ.filter fun slotIndex : Fin 5 =>
      atomTwo ∈ datumTightSupport frame.tightDir (frame.basisLabel slotIndex))
  have hpos : 0 < ((Finset.univ.filter fun slotIndex : Fin 5 =>
        atomOne ∈ datumTightSupport frame.tightDir (frame.basisLabel slotIndex))
      ∩ Finset.univ.filter fun slotIndex : Fin 5 =>
        atomTwo ∈ datumTightSupport frame.tightDir (frame.basisLabel slotIndex)).card := by
    omega
  obtain ⟨slotIndex, hmemInter⟩ := Finset.card_pos.mp hpos
  refine ⟨slotIndex, ?_⟩
  have hmemOne := (Finset.mem_filter.mp (Finset.mem_inter.mp hmemInter).1).2
  have hmemTwo := (Finset.mem_filter.mp (Finset.mem_inter.mp hmemInter).2).2
  have hmemHeavy := forall_carrier_of_multiplicity_eq_card hfive slotIndex
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro atomIndex hmem
    rcases Finset.mem_insert.mp hmem with heq | hrest
    · exact heq ▸ hmemHeavy
    rcases Finset.mem_insert.mp hrest with heq | hlast
    · exact heq ▸ hmemOne
    · exact (Finset.mem_singleton.mp hlast) ▸ hmemTwo
  · rw [hthree slotIndex, card_triple_of_distinct (Ne.symm hOneHeavy)
      (Ne.symm hTwoHeavy) hOneTwo]

/-- **THE RESIDUAL CELL.**  The heavy-five profile with five pairwise
distinct basis supports: the five doubles carry a five-cycle. -/
def RankFiveDenseHeavyFiveDistinctClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankFiveFrame crux) (heavyAtom : Fin 6),
    (∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3) →
    basisSupportMultiplicity frame.tightDir frame.basisLabel heavyAtom = 5 →
    (∀ atomIndex, atomIndex ≠ heavyAtom →
      basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex = 2) →
    Matrix.trace frame.coeff = 2 →
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight heavyAtom = 0 →
    (∀ slotOne slotTwo : Fin 5, slotOne ≠ slotTwo →
      datumTightSupport frame.tightDir (frame.basisLabel slotOne)
        ≠ datumTightSupport frame.tightDir (frame.basisLabel slotTwo)) →
    False

/-- **THE DOUBLED CELL IS DEAD.**  Two basis slots on one heavy-five
block kill the corner of that block, the three remaining doubles carry
the three blocks of a triangle, and the deflated trace of the triangle is
both `1 - 6G` and at most one.  The chart value is then nonnegative. -/
theorem RankFiveFrame.heavyFive_doubled_cell_false {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {heavyAtom : Fin 6}
    (hthree : ∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3)
    (hfive : basisSupportMultiplicity frame.tightDir frame.basisLabel heavyAtom = 5)
    (hdoubles : ∀ atomIndex, atomIndex ≠ heavyAtom →
      basisSupportMultiplicity frame.tightDir frame.basisLabel atomIndex = 2)
    (hheavyZero : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight heavyAtom = 0)
    {slotP slotQ : Fin 5} (hslot : slotP ≠ slotQ)
    (hequal : datumTightSupport frame.tightDir (frame.basisLabel slotP)
      = datumTightSupport frame.tightDir (frame.basisLabel slotQ)) :
    False := by
  classical
  set chartMatrix := (chartPointOfDesign crux.design).chart with hchartMatrix
  set chartWeight := (chartPointOfDesign crux.design).weight with hchartWeight
  set chartValue := chartObjective (chartPointOfDesign crux.design) with hchartValue
  obtain ⟨atomA, atomB, hAB, hAheavy, hBheavy, hsuppP⟩ :=
    frame.heavyFive_support_pair hthree hfive slotP
  have hsuppQ : datumTightSupport frame.tightDir (frame.basisLabel slotQ)
      = {heavyAtom, atomA, atomB} := hequal ▸ hsuppP
  have hdiagPos : 0 < chartMatrix heavyAtom heavyAtom :=
    frame.heavyFive_chart_diagonal_pos hheavyZero
  have hdiagNe : chartMatrix heavyAtom heavyAtom ≠ 0 := ne_of_gt hdiagPos
  have hcardRest : (((Finset.univ.erase heavyAtom).erase atomA).erase atomB).card
      = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hAB,
      Finset.mem_erase.mpr ⟨hBheavy, Finset.mem_univ _⟩⟩),
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hAheavy, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  obtain ⟨atomC, atomD, atomE, hCD, hCE, hDE, hrest⟩ :=
    Finset.card_eq_three.mp hcardRest
  have hmemRest : ∀ atomIndex ∈ ({atomC, atomD, atomE} : Finset (Fin 6)),
      atomIndex ≠ heavyAtom ∧ atomIndex ≠ atomA ∧ atomIndex ≠ atomB := by
    intro atomIndex hmem
    rw [← hrest] at hmem
    exact ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp
        (Finset.mem_erase.mp hmem).2).2).1,
      (Finset.mem_erase.mp (Finset.mem_erase.mp hmem).2).1,
      (Finset.mem_erase.mp hmem).1⟩
  obtain ⟨hCheavy, hCA, hCB⟩ := hmemRest atomC (Finset.mem_insert_self _ _)
  obtain ⟨hDheavy, hDA, hDB⟩ := hmemRest atomD
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hEheavy, hEA, hEB⟩ := hmemRest atomE
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  have hnotBlock : ∀ atomIndex : Fin 6, atomIndex ≠ heavyAtom → atomIndex ≠ atomA →
      atomIndex ≠ atomB → ∀ slotIndex : Fin 5,
      datumTightSupport frame.tightDir (frame.basisLabel slotIndex)
        = {heavyAtom, atomA, atomB} →
      atomIndex ∉ datumTightSupport frame.tightDir (frame.basisLabel slotIndex) := by
    intro atomIndex hheavy hA hB slotIndex hsupport
    rw [hsupport]
    exact notMem_triple.mpr ⟨hheavy, hA, hB⟩
  obtain ⟨slotCD, hblockCD⟩ := frame.heavyFive_exists_block_of_pair hthree hfive hCD
    hCheavy hDheavy (hdoubles atomC hCheavy) (hdoubles atomD hDheavy) hslot
    (hnotBlock atomC hCheavy hCA hCB slotP hsuppP)
    (hnotBlock atomC hCheavy hCA hCB slotQ hsuppQ)
    (hnotBlock atomD hDheavy hDA hDB slotP hsuppP)
    (hnotBlock atomD hDheavy hDA hDB slotQ hsuppQ)
  obtain ⟨slotCE, hblockCE⟩ := frame.heavyFive_exists_block_of_pair hthree hfive hCE
    hCheavy hEheavy (hdoubles atomC hCheavy) (hdoubles atomE hEheavy) hslot
    (hnotBlock atomC hCheavy hCA hCB slotP hsuppP)
    (hnotBlock atomC hCheavy hCA hCB slotQ hsuppQ)
    (hnotBlock atomE hEheavy hEA hEB slotP hsuppP)
    (hnotBlock atomE hEheavy hEA hEB slotQ hsuppQ)
  obtain ⟨slotDE, hblockDE⟩ := frame.heavyFive_exists_block_of_pair hthree hfive hDE
    hDheavy hEheavy (hdoubles atomD hDheavy) (hdoubles atomE hEheavy) hslot
    (hnotBlock atomD hDheavy hDA hDB slotP hsuppP)
    (hnotBlock atomD hDheavy hDA hDB slotQ hsuppQ)
    (hnotBlock atomE hEheavy hEA hEB slotP hsuppP)
    (hnotBlock atomE hEheavy hEA hEB slotQ hsuppQ)
  -- the block laws in the deflated chart
  have hminorLaw : ∀ atomX atomY : Fin 6, atomX ≠ atomY → atomX ≠ heavyAtom →
      atomY ≠ heavyAtom → ∀ slotIndex : Fin 5,
      datumTightSupport frame.tightDir (frame.basisLabel slotIndex)
        = {heavyAtom, atomX, atomY} →
      (heavyReducedEntry chartMatrix heavyAtom atomX atomX
            - (chartValue + chartWeight atomX))
          * (heavyReducedEntry chartMatrix heavyAtom atomY atomY
            - (chartValue + chartWeight atomY))
        = heavyReducedEntry chartMatrix heavyAtom atomX atomY
          * heavyReducedEntry chartMatrix heavyAtom atomX atomY :=
    fun atomX atomY hXY hXheavy hYheavy slotIndex hsupport =>
      heavy_block_reduced_minor frame.hdata (frame.hmemAll slotIndex) hXY
        (Ne.symm hXheavy) (Ne.symm hYheavy) hsupport hheavyZero hdiagNe
  have hpropagate : ∀ atomX atomY : Fin 6, atomX ≠ atomY → atomX ≠ heavyAtom →
      atomY ≠ heavyAtom → ∀ slotIndex : Fin 5,
      datumTightSupport frame.tightDir (frame.basisLabel slotIndex)
        = {heavyAtom, atomX, atomY} →
      heavyReducedEntry chartMatrix heavyAtom atomX atomX
          - (chartValue + chartWeight atomX) = 0 →
      heavyReducedEntry chartMatrix heavyAtom atomY atomY
        - (chartValue + chartWeight atomY) = 0 :=
    fun atomX atomY hXY hXheavy hYheavy slotIndex hsupport hzero =>
      heavy_block_reduced_propagate frame.hdata (frame.hmemAll slotIndex) hXY
        (Ne.symm hXheavy) (Ne.symm hYheavy) hsupport hheavyZero hdiagNe hzero
  obtain ⟨hcornerA, hcornerB, _hcornerAB⟩ := heavy_doubled_block_corner_zero
    frame.hdata (frame.hmemAll slotP) (frame.hmemAll slotQ) hAB (Ne.symm hAheavy)
    (Ne.symm hBheavy) hsuppP hsuppQ hheavyZero hdiagNe
    (frame.heavyFive_crossDet_ne_zero hAB hAheavy hBheavy hslot hsuppP hsuppQ)
  have hheavyCorner : heavyReducedEntry chartMatrix heavyAtom heavyAtom heavyAtom
      - (chartValue + chartWeight heavyAtom) = 0 := by
    rw [heavyReducedEntry_heavy_row hdiagNe, hheavyZero, sub_zero]
  -- the deflated trace splits onto the triangle
  have htraceAll : ∑ atomIndex : Fin 6,
      (heavyReducedEntry chartMatrix heavyAtom atomIndex atomIndex
        - (chartValue + chartWeight atomIndex)) = 1 - 6 * chartValue := by
    have hdeflatedTrace : ∑ atomIndex : Fin 6,
        heavyReducedEntry chartMatrix heavyAtom atomIndex atomIndex
        = ((3 : ℕ) : ℝ) - 1 := heavyReducedEntry_trace frame.hdata hdiagNe
    have hshiftTrace : ∑ atomIndex : Fin 6, (chartValue + chartWeight atomIndex)
        = 6 * chartValue + 1 := frame.shifted_weight_sum
    rw [Finset.sum_sub_distrib, hdeflatedTrace, hshiftTrace]
    push_cast
    ring
  have hsplit : ∑ atomIndex : Fin 6,
      (heavyReducedEntry chartMatrix heavyAtom atomIndex atomIndex
        - (chartValue + chartWeight atomIndex))
      = (heavyReducedEntry chartMatrix heavyAtom heavyAtom heavyAtom
          - (chartValue + chartWeight heavyAtom))
        + (heavyReducedEntry chartMatrix heavyAtom atomA atomA
          - (chartValue + chartWeight atomA))
        + (heavyReducedEntry chartMatrix heavyAtom atomB atomB
          - (chartValue + chartWeight atomB))
        + ((heavyReducedEntry chartMatrix heavyAtom atomC atomC
            - (chartValue + chartWeight atomC))
          + (heavyReducedEntry chartMatrix heavyAtom atomD atomD
            - (chartValue + chartWeight atomD))
          + (heavyReducedEntry chartMatrix heavyAtom atomE atomE
            - (chartValue + chartWeight atomE))) := by
    have hmemA : atomA ∈ Finset.univ.erase heavyAtom :=
      Finset.mem_erase.mpr ⟨hAheavy, Finset.mem_univ _⟩
    have hmemB : atomB ∈ (Finset.univ.erase heavyAtom).erase atomA :=
      Finset.mem_erase.mpr ⟨Ne.symm hAB, Finset.mem_erase.mpr ⟨hBheavy,
        Finset.mem_univ _⟩⟩
    have hstepHeavy := Finset.add_sum_erase (Finset.univ : Finset (Fin 6))
      (fun atomIndex => heavyReducedEntry chartMatrix heavyAtom atomIndex atomIndex
        - (chartValue + chartWeight atomIndex)) (Finset.mem_univ heavyAtom)
    have hstepA := Finset.add_sum_erase (Finset.univ.erase heavyAtom)
      (fun atomIndex => heavyReducedEntry chartMatrix heavyAtom atomIndex atomIndex
        - (chartValue + chartWeight atomIndex)) hmemA
    have hstepB := Finset.add_sum_erase ((Finset.univ.erase heavyAtom).erase atomA)
      (fun atomIndex => heavyReducedEntry chartMatrix heavyAtom atomIndex atomIndex
        - (chartValue + chartWeight atomIndex)) hmemB
    have hnotC : atomC ∉ ({atomD, atomE} : Finset (Fin 6)) := by
      intro hmem
      rcases Finset.mem_insert.mp hmem with heq | hlast
      · exact hCD heq
      · exact hCE (Finset.mem_singleton.mp hlast)
    have hnotD : atomD ∉ ({atomE} : Finset (Fin 6)) := fun hmem =>
      hDE (Finset.mem_singleton.mp hmem)
    have hlast : ∑ atomIndex ∈ (((Finset.univ.erase heavyAtom).erase atomA).erase
        atomB), (heavyReducedEntry chartMatrix heavyAtom atomIndex atomIndex
          - (chartValue + chartWeight atomIndex))
        = (heavyReducedEntry chartMatrix heavyAtom atomC atomC
            - (chartValue + chartWeight atomC))
          + (heavyReducedEntry chartMatrix heavyAtom atomD atomD
            - (chartValue + chartWeight atomD))
          + (heavyReducedEntry chartMatrix heavyAtom atomE atomE
            - (chartValue + chartWeight atomE)) := by
      rw [hrest, Finset.sum_insert hnotC, Finset.sum_insert hnotD,
        Finset.sum_singleton, add_assoc]
    rw [← hstepHeavy, ← hstepA, ← hstepB, hlast]
    ring
  have htracePos : 1 < (heavyReducedEntry chartMatrix heavyAtom atomC atomC
        - (chartValue + chartWeight atomC))
      + (heavyReducedEntry chartMatrix heavyAtom atomD atomD
        - (chartValue + chartWeight atomD))
      + (heavyReducedEntry chartMatrix heavyAtom atomE atomE
        - (chartValue + chartWeight atomE)) := by
    rw [hsplit, hheavyCorner, hcornerA, hcornerB] at htraceAll
    have hneg : chartValue < 0 := crux.hasNegativeChartValue
    linarith [htraceAll]
  -- the triangle diagonal is nonzero, then positive
  have hminorCD := hminorLaw atomC atomD hCD hCheavy hDheavy slotCD hblockCD
  have hminorCE := hminorLaw atomC atomE hCE hCheavy hEheavy slotCE hblockCE
  have hminorDE := hminorLaw atomD atomE hDE hDheavy hEheavy slotDE hblockDE
  have hCzero : heavyReducedEntry chartMatrix heavyAtom atomC atomC
      - (chartValue + chartWeight atomC) ≠ 0 := by
    intro hzero
    have hDvanish := hpropagate atomC atomD hCD hCheavy hDheavy slotCD hblockCD hzero
    have hEvanish := hpropagate atomD atomE hDE hDheavy hEheavy slotDE hblockDE
      hDvanish
    rw [hzero, hDvanish, hEvanish] at htracePos
    linarith
  have hDzero : heavyReducedEntry chartMatrix heavyAtom atomD atomD
      - (chartValue + chartWeight atomD) ≠ 0 := fun hzero =>
    hCzero (hpropagate atomD atomC (Ne.symm hCD) hDheavy hCheavy slotCD
      (by rw [hblockCD, triple_swap_last]) hzero)
  have hEzero : heavyReducedEntry chartMatrix heavyAtom atomE atomE
      - (chartValue + chartWeight atomE) ≠ 0 := fun hzero =>
    hDzero (hpropagate atomE atomD (Ne.symm hDE) hEheavy hDheavy slotDE
      (by rw [hblockDE, triple_swap_last]) hzero)
  have hoffCD : heavyReducedEntry chartMatrix heavyAtom atomC atomD ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hminorCD
    rcases mul_eq_zero.mp hminorCD with hcase | hcase
    · exact hCzero hcase
    · exact hDzero hcase
  have hoffCE : heavyReducedEntry chartMatrix heavyAtom atomC atomE ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hminorCE
    rcases mul_eq_zero.mp hminorCE with hcase | hcase
    · exact hCzero hcase
    · exact hEzero hcase
  have hprodCD : 0 < (heavyReducedEntry chartMatrix heavyAtom atomC atomC
        - (chartValue + chartWeight atomC))
      * (heavyReducedEntry chartMatrix heavyAtom atomD atomD
        - (chartValue + chartWeight atomD)) := by
    rw [hminorCD]
    exact mul_self_pos.mpr hoffCD
  have hprodCE : 0 < (heavyReducedEntry chartMatrix heavyAtom atomC atomC
        - (chartValue + chartWeight atomC))
      * (heavyReducedEntry chartMatrix heavyAtom atomE atomE
        - (chartValue + chartWeight atomE)) := by
    rw [hminorCE]
    exact mul_self_pos.mpr hoffCE
  have hposC : 0 < heavyReducedEntry chartMatrix heavyAtom atomC atomC
      - (chartValue + chartWeight atomC) := by
    rcases lt_or_gt_of_ne hCzero with hneg | hpos
    · exfalso
      have hnegD : heavyReducedEntry chartMatrix heavyAtom atomD atomD
          - (chartValue + chartWeight atomD) < 0 := by
        nlinarith only [hneg, hprodCD]
      have hnegE : heavyReducedEntry chartMatrix heavyAtom atomE atomE
          - (chartValue + chartWeight atomE) < 0 := by
        nlinarith only [hneg, hprodCE]
      linarith [htracePos]
    · exact hpos
  have hposD : 0 < heavyReducedEntry chartMatrix heavyAtom atomD atomD
      - (chartValue + chartWeight atomD) := by
    nlinarith only [hposC, hprodCD]
  have hposE : 0 < heavyReducedEntry chartMatrix heavyAtom atomE atomE
      - (chartValue + chartWeight atomE) := by
    nlinarith only [hposC, hprodCE]
  -- the row squares and the two deflated form bounds
  have hsymCD : heavyReducedEntry chartMatrix heavyAtom atomD atomC
      = heavyReducedEntry chartMatrix heavyAtom atomC atomD :=
    heavyReducedEntry_symm frame.hdata heavyAtom atomD atomC
  have hsymCE : heavyReducedEntry chartMatrix heavyAtom atomE atomC
      = heavyReducedEntry chartMatrix heavyAtom atomC atomE :=
    heavyReducedEntry_symm frame.hdata heavyAtom atomE atomC
  have hsymDE : heavyReducedEntry chartMatrix heavyAtom atomE atomD
      = heavyReducedEntry chartMatrix heavyAtom atomD atomE :=
    heavyReducedEntry_symm frame.hdata heavyAtom atomE atomD
  have hrowC := heavyReducedEntry_row_pair_le frame.hdata hdiagNe hCD hCE hDE
  have hrowD : heavyReducedEntry chartMatrix heavyAtom atomC atomD
        * heavyReducedEntry chartMatrix heavyAtom atomC atomD
      + heavyReducedEntry chartMatrix heavyAtom atomD atomE
        * heavyReducedEntry chartMatrix heavyAtom atomD atomE
      ≤ heavyReducedEntry chartMatrix heavyAtom atomD atomD
        - heavyReducedEntry chartMatrix heavyAtom atomD atomD
          * heavyReducedEntry chartMatrix heavyAtom atomD atomD := by
    have hstep := heavyReducedEntry_row_pair_le frame.hdata hdiagNe (Ne.symm hCD)
      hDE hCE
    rw [hsymCD] at hstep
    linarith [hstep]
  have hrowE : heavyReducedEntry chartMatrix heavyAtom atomC atomE
        * heavyReducedEntry chartMatrix heavyAtom atomC atomE
      + heavyReducedEntry chartMatrix heavyAtom atomD atomE
        * heavyReducedEntry chartMatrix heavyAtom atomD atomE
      ≤ heavyReducedEntry chartMatrix heavyAtom atomE atomE
        - heavyReducedEntry chartMatrix heavyAtom atomE atomE
          * heavyReducedEntry chartMatrix heavyAtom atomE atomE := by
    have hstep := heavyReducedEntry_row_pair_le frame.hdata hdiagNe (Ne.symm hCE)
      (Ne.symm hDE) hCD
    rw [hsymCE, hsymDE] at hstep
    linarith [hstep]
  have hshiftNonneg : ∀ atomIndex : Fin 6, 0 ≤ chartValue + chartWeight atomIndex :=
    fun atomIndex =>
      capture_diagonal_nonneg_of_isChartStationaryData frame.hdata atomIndex
  have hnonneg : ∀ coeffOne coeffTwo coeffThree : ℝ,
      0 ≤ coeffOne * (heavyReducedEntry chartMatrix heavyAtom atomC atomC * coeffOne
            + heavyReducedEntry chartMatrix heavyAtom atomC atomD * coeffTwo
            + heavyReducedEntry chartMatrix heavyAtom atomC atomE * coeffThree)
        + coeffTwo * (heavyReducedEntry chartMatrix heavyAtom atomC atomD * coeffOne
            + heavyReducedEntry chartMatrix heavyAtom atomD atomD * coeffTwo
            + heavyReducedEntry chartMatrix heavyAtom atomD atomE * coeffThree)
        + coeffThree * (heavyReducedEntry chartMatrix heavyAtom atomC atomE * coeffOne
            + heavyReducedEntry chartMatrix heavyAtom atomD atomE * coeffTwo
            + heavyReducedEntry chartMatrix heavyAtom atomE atomE * coeffThree) := by
    intro coeffOne coeffTwo coeffThree
    have hstep := heavyReducedEntry_triple_nonneg frame.hdata hdiagPos hCD hCE hDE
      coeffOne coeffTwo coeffThree
    rw [hsymCD, hsymCE, hsymDE] at hstep
    exact hstep
  have hcontract : ∀ coeffOne coeffTwo coeffThree : ℝ,
      coeffOne * (heavyReducedEntry chartMatrix heavyAtom atomC atomC * coeffOne
            + heavyReducedEntry chartMatrix heavyAtom atomC atomD * coeffTwo
            + heavyReducedEntry chartMatrix heavyAtom atomC atomE * coeffThree)
        + coeffTwo * (heavyReducedEntry chartMatrix heavyAtom atomC atomD * coeffOne
            + heavyReducedEntry chartMatrix heavyAtom atomD atomD * coeffTwo
            + heavyReducedEntry chartMatrix heavyAtom atomD atomE * coeffThree)
        + coeffThree * (heavyReducedEntry chartMatrix heavyAtom atomC atomE * coeffOne
            + heavyReducedEntry chartMatrix heavyAtom atomD atomE * coeffTwo
            + heavyReducedEntry chartMatrix heavyAtom atomE atomE * coeffThree)
        ≤ coeffOne * coeffOne + coeffTwo * coeffTwo + coeffThree * coeffThree := by
    intro coeffOne coeffTwo coeffThree
    have hstep := heavyReducedEntry_triple_le_self frame.hdata hdiagPos hCD hCE hDE
      coeffOne coeffTwo coeffThree
    rw [hsymCD, hsymCE, hsymDE] at hstep
    exact hstep
  have hcap := dense_triangle_trace_le_one (hshiftNonneg atomC) (hshiftNonneg atomD)
    (hshiftNonneg atomE) hposC hposD hposE hminorCD hminorCE hminorDE hrowC hrowD
    hrowE hnonneg hcontract
  linarith [hcap, htracePos]

/-- **THE PROFILE-A DISPATCH.**  The heavy-five profile splits into the
doubled cell and the distinct cell.  The doubled cell is dead, thus the
residual closure carries the whole profile. -/
theorem rankFiveDenseHeavyFiveClosed_of_distinct
    (killDistinct : RankFiveDenseHeavyFiveDistinctClosed) :
    RankFiveDenseHeavyFiveClosed := by
  intro crux frame heavyAtom hthree hfive hdoubles htrace hheavyZero
  classical
  by_cases hdistinct : ∀ slotOne slotTwo : Fin 5, slotOne ≠ slotTwo →
      datumTightSupport frame.tightDir (frame.basisLabel slotOne)
        ≠ datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
  · exact killDistinct crux frame heavyAtom hthree hfive hdoubles htrace hheavyZero
      hdistinct
  · simp only [not_forall, not_not] at hdistinct
    obtain ⟨slotP, slotQ, hslot, hequal⟩ := hdistinct
    exact frame.heavyFive_doubled_cell_false hthree hfive hdoubles hheavyZero hslot
      hequal

end Gtz
