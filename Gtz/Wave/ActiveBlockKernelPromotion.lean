import Gtz.Wave.PositiveRowSpanRankFloor
import Gtz.Reduction.ChartAttainmentWeld

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace Gtz

open Matrix Finset
open scoped BigOperators

theorem linear_eq_zero_of_quadratic_nonneg
    {quadratic linear : ℝ}
    (hnonneg : ∀ scale : ℝ, 0 ≤ quadratic * scale ^ 2 + 2 * linear * scale) :
    linear = 0 := by
  by_cases hquadratic : quadratic = 0
  · have hpos := hnonneg 1
    have hneg := hnonneg (-1)
    rw [hquadratic] at hpos hneg
    norm_num at hpos hneg
    linarith
  · have hquadNonneg : 0 ≤ quadratic := by
      have hpos := hnonneg 1
      have hneg := hnonneg (-1)
      norm_num at hpos hneg
      linarith
    have hquadPos : 0 < quadratic := lt_of_le_of_ne hquadNonneg (Ne.symm hquadratic)
    have htest := hnonneg (-linear / quadratic)
    have hquadNe : quadratic ≠ 0 := ne_of_gt hquadPos
    field_simp [hquadNe] at htest
    nlinarith [sq_nonneg linear]

/-- Equality in the quadratic lower bound of a block is a kernel equation on
that block.  This is the ambient-coordinate version of the standard fact that
`xᵀ A x = 0` for `A ⪧0` implies `A x = 0`. -/
theorem isChartTightVector_of_dominatesAtValue_of_rayleigh_eq
    {size : ℕ}
    {projection : Matrix (Fin size) (Fin size) ℝ}
    {weight : Fin size → ℝ} {value : ℝ}
    {chosenSubset : Finset (Fin size)} {probe : Fin size → ℝ}
    (hsymmetric : projectionᵀ = projection)
    (hdominates : ChartBlockDominatesAtValue projection weight value chosenSubset)
    (hsupport : ∀ atomIndex : Fin size,
      atomIndex ∉ chosenSubset → probe atomIndex = 0)
    (hequality : probe ⬝ᵥ (chartStationaryGap projection weight *ᵥ probe)
      = value * (probe ⬝ᵥ probe)) :
    IsChartTightVector projection weight value chosenSubset probe := by
  refine ⟨hsupport, ?_⟩
  intro atomIndex hmember
  let axis : Fin size → ℝ := fun otherIndex => if otherIndex = atomIndex then 1 else 0
  have haxisSupport : ∀ otherIndex : Fin size,
      otherIndex ∉ chosenSubset → axis otherIndex = 0 := by
    intro otherIndex hnotMember
    simp only [axis]
    split_ifs with heq
    · exact (hnotMember (heq.symm ▸ hmember)).elim
    · rfl
  have hsumSupport : ∀ scale : ℝ, ∀ otherIndex : Fin size,
      otherIndex ∉ chosenSubset → (probe + scale • axis) otherIndex = 0 := by
    intro scale otherIndex hnotMember
    simp [hsupport otherIndex hnotMember, haxisSupport otherIndex hnotMember]
  have hgapSymmetric :
      (chartStationaryGap projection weight)ᵀ = chartStationaryGap projection weight := by
    simp [chartStationaryGap, Matrix.transpose_sub, hsymmetric]
  let quadratic := axis ⬝ᵥ (chartStationaryGap projection weight *ᵥ axis)
      - value * (axis ⬝ᵥ axis)
  let linear := axis ⬝ᵥ (chartStationaryGap projection weight *ᵥ probe)
      - value * (axis ⬝ᵥ probe)
  have hpoly : ∀ scale : ℝ,
      0 ≤ quadratic * scale ^ 2 + 2 * linear * scale := by
    intro scale
    have hbound := hdominates (probe + scale • axis) (hsumSupport scale)
    have hcross :
        probe ⬝ᵥ (chartStationaryGap projection weight *ᵥ axis)
          = axis ⬝ᵥ (chartStationaryGap projection weight *ᵥ probe) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hgapSymmetric,
        dotProduct_comm]
    dsimp only [quadratic, linear]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
      dotProduct_add, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hbound
    rw [hcross, hequality] at hbound
    rw [dotProduct_comm probe axis] at hbound
    ring_nf at hbound ⊢
    linarith
  have hlinear : linear = 0 := linear_eq_zero_of_quadratic_nonneg hpoly
  have haxisDot : axis ⬝ᵥ probe = probe atomIndex := by
    simp [axis, dotProduct, Finset.sum_ite_eq', Finset.mem_univ]
  have haxisGap :
      axis ⬝ᵥ (chartStationaryGap projection weight *ᵥ probe)
        = (chartStationaryGap projection weight *ᵥ probe) atomIndex := by
    simp [axis, dotProduct, Finset.sum_ite_eq', Finset.mem_univ]
  dsimp only [linear] at hlinear
  rw [haxisDot, haxisGap] at hlinear
  linarith

def orbitFourBlockZeroOneTwo : Finset (Fin 6) := {0, 1, 2}
def orbitFourBlockZeroOneThree : Finset (Fin 6) := {0, 1, 3}
def orbitFourBlockZeroTwoThree : Finset (Fin 6) := {0, 2, 3}
def orbitFourBlockOneFourFive : Finset (Fin 6) := {1, 4, 5}

def orbitFourFamily : Finset (Finset (Fin 6)) :=
  {orbitFourBlockZeroOneTwo, orbitFourBlockZeroOneThree,
    orbitFourBlockZeroTwoThree, orbitFourBlockOneFourFive}

/-- In the four-block orbit `{012,013,023,145}`, a stationary selection cannot
use the same tight direction at `013` and `023`: its positive rows would span
at most three dimensions, whereas every negative `(6,3)` crux requires four. -/
theorem SixThreeCrux.false_of_orbitFour_duplicate_tightDirection
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design) = orbitFourFamily)
    {activeWeight : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) activeWeight tightDir)
    (hduplicate : tightDir orbitFourBlockZeroOneThree
      = tightDir orbitFourBlockZeroTwoThree) :
    False := by
  classical
  let positiveSet := positiveActiveSet
    (chartArgmaxFamily (chartPointOfDesign crux.design)) activeWeight
  let rows := positiveSet.image tightDir
  let threeRows : Finset (Fin 6 → ℝ) :=
    {tightDir orbitFourBlockZeroOneTwo,
      tightDir orbitFourBlockZeroOneThree,
      tightDir orbitFourBlockOneFourFive}
  have hrowsSubset : rows ⊆ threeRows := by
    intro row hrow
    obtain ⟨block, hblockPositive, rfl⟩ := Finset.mem_image.mp hrow
    have hblockActive : block ∈ chartArgmaxFamily (chartPointOfDesign crux.design) :=
      (Finset.filter_subset _ _) hblockPositive
    rw [hfamily] at hblockActive
    simp only [orbitFourFamily, Finset.mem_insert, Finset.mem_singleton] at hblockActive
    rcases hblockActive with rfl | rfl | rfl | rfl
    · simp [threeRows]
    · simp [threeRows]
    · rw [← hduplicate]
      simp [threeRows]
    · simp [threeRows]
  have hupper : Module.finrank ℝ (Submodule.span ℝ (↑rows : Set (Fin 6 → ℝ))) ≤ 3 := by
    calc
      Module.finrank ℝ (Submodule.span ℝ (↑rows : Set (Fin 6 → ℝ)))
          ≤ rows.card := finrank_span_finset_le_card rows
      _ ≤ threeRows.card := Finset.card_le_card hrowsSubset
      _ ≤ 3 := by
        have hfirst := Finset.card_insert_le
          (tightDir orbitFourBlockZeroOneTwo)
          ({tightDir orbitFourBlockZeroOneThree,
            tightDir orbitFourBlockOneFourFive} : Finset (Fin 6 → ℝ))
        have hsecond := Finset.card_insert_le
          (tightDir orbitFourBlockZeroOneThree)
          ({tightDir orbitFourBlockOneFourFive} : Finset (Fin 6 → ℝ))
        dsimp only [threeRows]
        simp only [Finset.card_singleton] at hsecond
        omega
  have hlower := crux.four_le_positiveTightRowSpan_finrank hdata
  change 4 ≤ Module.finrank ℝ
    (Submodule.span ℝ (↑rows : Set (Fin 6 → ℝ))) at hlower
  omega

/-- **TYPE-7 SUPPORT LEAF CLOSED.**  If the `013` active block has a unit tight
direction supported only on the shared pair `{0,3}`, positivity of the active
`023` block makes the same vector tight there.  Strong stationarity may then
select the duplicate direction at both labels, contradicting the four-dimensional
positive-row-span floor. -/
theorem SixThreeCrux.false_of_orbitFour_thin_sharedPair
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design) = orbitFourFamily)
    {thin : Fin 6 → ℝ}
    (hthin : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      orbitFourBlockZeroOneThree thin)
    (hthinSupport : ∀ atomIndex : Fin 6,
      atomIndex ∉ ({0, 3} : Finset (Fin 6)) → thin atomIndex = 0) :
    False := by
  classical
  let point := chartPointOfDesign crux.design
  let value := chartObjective point
  have hsharedSubset : ({0, 3} : Finset (Fin 6)) ⊆ orbitFourBlockZeroTwoThree := by
    intro atomIndex hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl <;> simp [orbitFourBlockZeroTwoThree]
  have hthinNeighborSupport : ∀ atomIndex : Fin 6,
      atomIndex ∉ orbitFourBlockZeroTwoThree → thin atomIndex = 0 := by
    intro atomIndex hnotMem
    apply hthinSupport atomIndex
    intro hpair
    exact hnotMem (hsharedSubset hpair)
  have hneighborMem : orbitFourBlockZeroTwoThree ∈ chartArgmaxFamily point := by
    rw [hfamily]
    simp [orbitFourFamily]
  obtain ⟨hneighborCard, hneighborFloor⟩ :=
    (mem_chartArgmaxFamily_iff point orbitFourBlockZeroTwoThree).mp hneighborMem
  have hneighborDominates : ChartBlockDominatesAtValue
      point.chart point.weight value orbitFourBlockZeroTwoThree :=
    chartBlockDominatesAtValue_of_le_chartBlockValue point hneighborCard hneighborFloor
  have hthinRayleigh :
      thin ⬝ᵥ (chartStationaryGap point.chart point.weight *ᵥ thin)
        = value * (thin ⬝ᵥ thin) :=
    dotProduct_chartStationaryGap_mulVec_of_isChartTightVector
      (isChartTightVector_of_isChartTightDirection hthin)
  have hthinNeighborVector : IsChartTightVector point.chart point.weight value
      orbitFourBlockZeroTwoThree thin :=
    isChartTightVector_of_dominatesAtValue_of_rayleigh_eq
      crux.isChartStrongStationaryData.isSymmetric hneighborDominates
      hthinNeighborSupport hthinRayleigh
  have hthinNeighbor : IsChartTightDirection point.chart point.weight value
      orbitFourBlockZeroTwoThree thin :=
    { isUnit := hthin.isUnit
      hasSupport := hthinNeighborVector.hasSupport
      isTight := hthinNeighborVector.isTight }
  choose fallback hfallback using crux.isChartStrongStationaryData.exists_tightDir
  let selection : Finset (Fin 6) → (Fin 6 → ℝ) := fun block =>
    if block = orbitFourBlockZeroOneThree then thin
    else if block = orbitFourBlockZeroTwoThree then thin
    else if hmem : block ∈ chartArgmaxFamily point then fallback block hmem else 0
  have hselection : ∀ block ∈ chartArgmaxFamily point,
      IsChartTightDirection point.chart point.weight value block (selection block) := by
    intro block hmem
    by_cases hleft : block = orbitFourBlockZeroOneThree
    · subst block
      simpa [selection] using hthin
    by_cases hright : block = orbitFourBlockZeroTwoThree
    · subst block
      simpa [selection, orbitFourBlockZeroOneThree,
        orbitFourBlockZeroTwoThree] using hthinNeighbor
    · simpa [selection, hleft, hright, hmem] using hfallback block hmem
  obtain ⟨activeWeight, hdata⟩ :=
    exists_multiplier_isChartStationaryData_of_isChartStrongStationaryData
      crux.isChartStrongStationaryData selection hselection
  apply crux.false_of_orbitFour_duplicate_tightDirection hfamily hdata
  simp [selection, orbitFourBlockZeroOneThree, orbitFourBlockZeroTwoThree]


end Gtz
