import Gtz.Wave.CaptureLineTrichotomy
import Gtz.Wave.PlaneCapTripleClosure
import Gtz.Wave.AssemblySupportCap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The pair kill — the commutation row closes the clone residue

The pair residue of the capture line trichotomy dies by ONE exact
identity.  Read the commutation law `P Ξ = Ξ P` at the row of the first
clone atom, against the chart entries into the four coplanar atoms.
The two evaluations of that read are `s (s - τ) / 6` and `s (1 - τ) / 6`
with `s` the shifted weight of the clone atom and `τ` the pair trace
excess.  Equality forces `s (1 - s) = 0`, and the handed interiority of
the clone atom refuses it.

The chain that feeds the read:

* **The capture line entry laws.**  The chart fixes the pair line, thus
  the pair rows give `P₁₂ = -σ (1 - P₁₁)` and the plane rows give
  `P_{t₂ z} = σ P_{t₁ z}`, with `σ` the clone ratio.
* **The clone law at every positive label.**  Every positive multiplier
  puts its tight direction in the range of the assembly, the basis
  spans that range, and the handed basis clone laws extend by
  linearity.
* **`σ² = 1`.**  The assembly diagonal is `1/6` at each clone atom, and
  the clone law converts one diagonal into `σ²` times the other.
* **The uniform row law.**  At every positive label the ambient chart
  row at the first clone atom reads `s` times the coordinate: inside
  the block this is the tight row, and outside it the floor makes the
  capture line alive on the block, thus the tight row at the second
  clone atom kills the leak.
* **The row energy laws.**  Idempotence prices the plane part of the
  first clone row and makes it an eigenvector of the plane block.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.pair_commutation_endgame` — the scalar endgame.
* `Gtz.rankFourCaptureLinePairFlooredClosed_holds` — **THE PAIR
  RESIDUE IS A THEOREM.**
* `Gtz.rankFourChartNullBasisNullFloored_of_wide`,
  `Gtz.isSixThreeAssemblyRankExcludedFloored_four_of_wide`,
  `Gtz.gtzWeighted_six_three_of_wideResidue_of_upperClosures`,
  `Gtz.gtzWeightedAll_three_of_wideResidue_of_upperClosures` — **THE
  CELL NOW RESTS ON THE WIDE RESIDUE AND THE SIX UPPER CLOSURES.**

## Vacuity

Every crux-quantified statement is vacuous if `Gtz.GtzWeighted 6 3`
holds: no crux exists.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the split calculus and the scalar endgame -/

section SplitCalculus

/-- A sum over `Fin 6` splits into two named atoms and their complement. -/
theorem sum_eq_pair_add_compl {atomOne atomTwo : Fin 6} (hne : atomOne ≠ atomTwo)
    (value : Fin 6 → ℝ) :
    ∑ y, value y = value atomOne + value atomTwo
      + ∑ y ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ, value y := by
  rw [← Finset.sum_add_sum_compl ({atomOne, atomTwo} : Finset (Fin 6)) value,
    Finset.sum_pair hne]

/-- A member of the pair complement differs from the two atoms. -/
theorem ne_of_mem_pair_compl {atomOne atomTwo z : Fin 6}
    (hz : z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ) :
    z ≠ atomOne ∧ z ≠ atomTwo := by
  simpa [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] using hz

/-- **THE SCALAR ENDGAME.**  The two evaluations of the weighted
commutation row agree only at a shifted weight of zero or one. -/
theorem pair_commutation_endgame {shift diag ratio : ℝ}
    (hsq : ratio ^ 2 = 1)
    (hmain : shift * (shift - (2 * diag - 1))
      = 2 * (diag - (diag ^ 2 + (-(ratio * (1 - diag))) ^ 2))
        + (2 - 2 * diag) * (shift - (2 * diag - 1))) :
    shift * (1 - shift) = 0 := by
  linear_combination (-1 : ℝ) * hmain + 2 * (1 - diag) ^ 2 * hsq

end SplitCalculus

/-! ## Layer 1 — the pair residue is a theorem -/

section PairKill

/-- **THE PAIR RESIDUE IS A THEOREM.**  The commutation row at the first
clone atom, read against the chart entries into the coplanar atoms,
forces the shifted weight of the clone atom to zero or one. -/
theorem rankFourCaptureLinePairFlooredClosed_holds :
    RankFourCaptureLinePairFlooredClosed := by
  classical
  intro crux frame hfloors nullVec lineVec atomOne atomTwo normalVec
    _hnullNe _hnullBasis _hnullChart hne hliveOne hliveTwo hoff hlineChart _hlineBasis
    hclone hinteriorOne _hinteriorTwo _hnormalNe _hnormal
  set chartP := (chartPointOfDesign crux.design).chart with hchartPDef
  set weightW := (chartPointOfDesign crux.design).weight with hweightWDef
  set valueG := chartObjective (chartPointOfDesign crux.design) with hvalueGDef
  set ratio := -lineVec atomOne / lineVec atomTwo with hratioDef
  have hdata := frame.hdata
  have hratioNe : ratio ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hliveOne) hliveTwo
  have hratioLine : ratio * lineVec atomTwo = -lineVec atomOne := by
    rw [hratioDef]
    exact div_mul_cancel₀ _ hliveTwo
  -- entry symmetry
  have hsymE : ∀ a b : Fin 6, chartP a b = chartP b a := by
    intro a b
    have hentry := congrFun (congrFun hdata.isSymmetric a) b
    rw [Matrix.transpose_apply] at hentry
    exact hentry.symm
  -- the fixed-line rows
  have hrow : ∀ y : Fin 6,
      chartP y atomOne * lineVec atomOne + chartP y atomTwo * lineVec atomTwo
        = lineVec y := by
    intro y
    have hy := congrFun hlineChart y
    rw [Matrix.mulVec, dotProduct] at hy
    rw [sum_eq_pair_add_compl hne (value := fun x => chartP y x * lineVec x)] at hy
    have hvanish : ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
        chartP y z * lineVec z = 0 := by
      refine Finset.sum_eq_zero fun z hz => ?_
      obtain ⟨hz1, hz2⟩ := ne_of_mem_pair_compl hz
      rw [hoff z hz1 hz2, mul_zero]
    rw [hvanish, add_zero] at hy
    exact hy
  -- the cross entry law
  have hP12 : chartP atomOne atomTwo = -(ratio * (1 - chartP atomOne atomOne)) := by
    have hone := hrow atomOne
    apply mul_right_cancel₀ hliveTwo
    linear_combination hone + (1 - chartP atomOne atomOne) * hratioLine
  -- the plane entry law
  have hPlane : ∀ z : Fin 6, z ≠ atomOne → z ≠ atomTwo →
      chartP atomTwo z = ratio * chartP atomOne z := by
    intro z hz1 hz2
    have hzrow := hrow z
    rw [hoff z hz1 hz2] at hzrow
    have hswap : chartP z atomTwo = ratio * chartP z atomOne := by
      apply mul_right_cancel₀ hliveTwo
      linear_combination hzrow - chartP z atomOne * hratioLine
    rw [hsymE atomTwo z, hswap, hsymE z atomOne]
  -- the clone law at every positive label
  have hcloneAll : ∀ L ∈ frame.activeSet, 0 < frame.reducedWeight L →
      frame.tightDir L atomTwo = ratio * frame.tightDir L atomOne := by
    intro L hL hpos
    have hrange := tightDir_mem_range_multiplier_of_pos hdata hL hpos
    rw [← frame.hspan] at hrange
    obtain ⟨coeff, hcoeff⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hrange
    have honeEval := congrFun hcoeff atomOne
    have htwoEval := congrFun hcoeff atomTwo
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at honeEval htwoEval
    rw [← htwoEval, ← honeEval, Finset.mul_sum]
    exact Finset.sum_congr rfl fun slot _ => by rw [hclone slot]; ring
  -- the assembly diagonal as a label sum
  have hassembly : ∀ y : Fin 6,
      ∑ L ∈ frame.activeSet,
          frame.reducedWeight L * frame.tightDir L y ^ 2 = ((6 : ℕ) : ℝ)⁻¹ :=
    fun y => (chartMultiplierAssembly_diagonal frame.activeSet frame.reducedWeight
      frame.tightDir y).symm.trans (hdata.assembly_diagonal y)
  -- the clone ratio squares to one
  have hsq : ratio ^ 2 = 1 := by
    have hconvert : ∑ L ∈ frame.activeSet,
        frame.reducedWeight L * frame.tightDir L atomTwo ^ 2
          = ratio ^ 2 * ∑ L ∈ frame.activeSet,
              frame.reducedWeight L * frame.tightDir L atomOne ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun L hL => ?_
      rcases (hdata.activeWeight_nonneg L hL).eq_or_lt with hzero | hpos
      · rw [← hzero]; ring
      · rw [hcloneAll L hL hpos]; ring
    rw [hassembly atomTwo, hassembly atomOne] at hconvert
    have hsix : ((6 : ℕ) : ℝ)⁻¹ ≠ 0 := by norm_num
    field_simp at hconvert
    linarith
  -- the shifted weight window
  have hshiftPos : 0 < valueG + weightW atomOne := hinteriorOne
  have hshiftLtOne : valueG + weightW atomOne < 1 := by
    have hneg : valueG < 0 := crux.hasNegativeChartValue
    have hweight : weightW atomOne < 1 :=
      weight_lt_one crux.design (by norm_num) atomOne
    linarith
  -- the uniform row law at the first clone atom
  have hRowLaw : ∀ L ∈ frame.activeSet, 0 < frame.reducedWeight L →
      ∑ y, chartP atomOne y * frame.tightDir L y
        = (valueG + weightW atomOne) * frame.tightDir L atomOne := by
    intro L hL hpos
    by_cases hmemOne : atomOne ∈ frame.activeSubset L
    · have htight := hdata.tightDir_isTight L hL atomOne hmemOne
      have hexpand : (chartStationaryGap chartP weightW *ᵥ frame.tightDir L) atomOne
          = (∑ y, chartP atomOne y * frame.tightDir L y)
            - weightW atomOne * frame.tightDir L atomOne := by
        rw [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
        rfl
      rw [hexpand] at htight
      linear_combination htight
    · have hqOne : frame.tightDir L atomOne = 0 :=
        hdata.tightDir_support L hL atomOne hmemOne
      have hqTwo : frame.tightDir L atomTwo = 0 := by
        rw [hcloneAll L hL hpos, hqOne, mul_zero]
      have hlineNe : lineVec ≠ 0 := fun hcontra =>
        hliveOne (by rw [hcontra]; rfl)
      obtain ⟨liveAtom, hliveMem, hliveVal⟩ := crux.chart_fixed_live_on_floored_block
        (hdata.activeSubset_card L hL) (hfloors L hL)
        (fun atomIndex _ => crux.shifted_weight_pos atomIndex) hlineNe hlineChart
      have hmemTwo : atomTwo ∈ frame.activeSubset L := by
        rcases eq_or_ne liveAtom atomOne with hcase | hcase
        · exact absurd (hcase ▸ hliveMem) hmemOne
        rcases eq_or_ne liveAtom atomTwo with hcase2 | hcase2
        · exact hcase2 ▸ hliveMem
        · exact absurd (hoff liveAtom hcase hcase2) hliveVal
      have htight := hdata.tightDir_isTight L hL atomTwo hmemTwo
      have hexpand : (chartStationaryGap chartP weightW *ᵥ frame.tightDir L) atomTwo
          = (∑ y, chartP atomTwo y * frame.tightDir L y)
            - weightW atomTwo * frame.tightDir L atomTwo := by
        rw [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
        rfl
      rw [hexpand, hqTwo] at htight
      have hzeroTwo : ∑ y, chartP atomTwo y * frame.tightDir L y = 0 := by
        linear_combination htight
      have hsplitTwo : ∑ y, chartP atomTwo y * frame.tightDir L y
          = ratio * ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
              chartP atomOne z * frame.tightDir L z := by
        rw [sum_eq_pair_add_compl hne
          (value := fun y => chartP atomTwo y * frame.tightDir L y),
          hqOne, hqTwo, mul_zero, mul_zero, zero_add, zero_add, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z hz => ?_
        obtain ⟨hz1, hz2⟩ := ne_of_mem_pair_compl hz
        rw [hPlane z hz1 hz2]
        ring
      rw [hsplitTwo] at hzeroTwo
      have hcomplZero : ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
          chartP atomOne z * frame.tightDir L z = 0 := by
        rcases mul_eq_zero.mp hzeroTwo with hcase | hcase
        · exact absurd hcase hratioNe
        · exact hcase
      rw [sum_eq_pair_add_compl hne
        (value := fun y => chartP atomOne y * frame.tightDir L y),
        hqOne, hqTwo, mul_zero, mul_zero, zero_add, zero_add, hcomplZero, mul_zero]
  -- the plane read of the row law
  have hPlaneRead : ∀ L ∈ frame.activeSet, 0 < frame.reducedWeight L →
      ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
          chartP atomOne z * frame.tightDir L z
        = (valueG + weightW atomOne - (2 * chartP atomOne atomOne - 1))
            * frame.tightDir L atomOne := by
    intro L hL hpos
    have hlaw := hRowLaw L hL hpos
    rw [sum_eq_pair_add_compl hne
      (value := fun y => chartP atomOne y * frame.tightDir L y),
      hcloneAll L hL hpos, hP12] at hlaw
    linear_combination hlaw
      + (1 - chartP atomOne atomOne) * frame.tightDir L atomOne * hsq
  -- idempotence entries
  have hIdemEntry : ∀ a b : Fin 6, ∑ y, chartP a y * chartP y b = chartP a b := by
    intro a b
    have hentry := congrFun (congrFun hdata.isIdempotent a) b
    rw [Matrix.mul_apply] at hentry
    exact hentry
  -- the plane row energy
  have hRho : ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
      chartP atomOne z * chartP atomOne z
        = chartP atomOne atomOne
          - (chartP atomOne atomOne ^ 2 + chartP atomOne atomTwo ^ 2) := by
    have hentry := hIdemEntry atomOne atomOne
    rw [sum_eq_pair_add_compl hne
      (value := fun y => chartP atomOne y * chartP y atomOne)] at hentry
    have hsymSum : ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
        chartP atomOne z * chartP z atomOne
          = ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
              chartP atomOne z * chartP atomOne z :=
      Finset.sum_congr rfl fun z _ => by rw [hsymE z atomOne]
    rw [hsymSum, hsymE atomTwo atomOne] at hentry
    linear_combination hentry
  -- the eigen law of the plane block
  have hEigen : ∀ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
      ∑ z' ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
          chartP z z' * chartP atomOne z'
        = (2 - 2 * chartP atomOne atomOne) * chartP atomOne z := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := ne_of_mem_pair_compl hz
    have hentry := hIdemEntry z atomOne
    rw [sum_eq_pair_add_compl hne
      (value := fun y => chartP z y * chartP y atomOne)] at hentry
    have hsymSum : ∑ z' ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
        chartP z z' * chartP z' atomOne
          = ∑ z' ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
              chartP z z' * chartP atomOne z' :=
      Finset.sum_congr rfl fun z' _ => by rw [hsymE z' atomOne]
    rw [hsymSum, hsymE z atomOne, hsymE z atomTwo, hPlane z hz1 hz2,
      hsymE atomTwo atomOne, hP12] at hentry
    linear_combination hentry
      + (1 - chartP atomOne atomOne) * chartP atomOne z * hsq
  -- the two evaluations of the weighted commutation row
  have hcomm := hdata.assembly_commutes
  have hLeftExpand : ∀ z : Fin 6,
      (chartP * chartMultiplierAssembly frame.activeSet frame.reducedWeight
          frame.tightDir) atomOne z
        = ∑ L ∈ frame.activeSet, frame.reducedWeight L
            * ((∑ y, chartP atomOne y * frame.tightDir L y) * frame.tightDir L z) := by
    intro z
    rw [Matrix.mul_apply]
    have hpoint : ∀ y : Fin 6,
        chartP atomOne y * chartMultiplierAssembly frame.activeSet
            frame.reducedWeight frame.tightDir y z
          = ∑ L ∈ frame.activeSet, chartP atomOne y
              * (frame.reducedWeight L * (frame.tightDir L y * frame.tightDir L z)) := by
      intro y
      rw [chartMultiplierAssembly_apply, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun y _ => hpoint y, Finset.sum_comm]
    refine Finset.sum_congr rfl fun L _ => ?_
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hRightExpand : ∀ z : Fin 6,
      (chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir
          * chartP) atomOne z
        = ∑ L ∈ frame.activeSet, frame.reducedWeight L
            * (frame.tightDir L atomOne * (∑ y, frame.tightDir L y * chartP y z)) := by
    intro z
    rw [Matrix.mul_apply]
    have hpoint : ∀ y : Fin 6,
        chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir
            atomOne y * chartP y z
          = ∑ L ∈ frame.activeSet, frame.reducedWeight L
              * (frame.tightDir L atomOne * frame.tightDir L y) * chartP y z := by
      intro y
      rw [chartMultiplierAssembly_apply, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun y _ => hpoint y, Finset.sum_comm]
    refine Finset.sum_congr rfl fun L _ => ?_
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  -- the left value
  have hLeftValue : ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
      chartP atomOne z * (chartP * chartMultiplierAssembly frame.activeSet
          frame.reducedWeight frame.tightDir) atomOne z
        = (valueG + weightW atomOne)
            * (valueG + weightW atomOne - (2 * chartP atomOne atomOne - 1))
            * ((6 : ℕ) : ℝ)⁻¹ := by
    have hswap : ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
        chartP atomOne z * (chartP * chartMultiplierAssembly frame.activeSet
            frame.reducedWeight frame.tightDir) atomOne z
          = ∑ L ∈ frame.activeSet, frame.reducedWeight L
              * ((∑ y, chartP atomOne y * frame.tightDir L y)
                * (∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
                    chartP atomOne z * frame.tightDir L z)) := by
      have hexp : ∀ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
          chartP atomOne z * (chartP * chartMultiplierAssembly frame.activeSet
              frame.reducedWeight frame.tightDir) atomOne z
            = chartP atomOne z * ∑ L ∈ frame.activeSet, frame.reducedWeight L
                * ((∑ y, chartP atomOne y * frame.tightDir L y)
                  * frame.tightDir L z) :=
        fun z _ => by rw [hLeftExpand z]
      rw [Finset.sum_congr rfl hexp]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun L _ =>
        Finset.sum_congr rfl fun z _ =>
          Finset.sum_congr rfl fun y _ => by ring
    rw [hswap]
    have hterm : ∀ L ∈ frame.activeSet,
        frame.reducedWeight L
            * ((∑ y, chartP atomOne y * frame.tightDir L y)
              * (∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
                  chartP atomOne z * frame.tightDir L z))
          = (valueG + weightW atomOne)
              * (valueG + weightW atomOne - (2 * chartP atomOne atomOne - 1))
              * (frame.reducedWeight L * frame.tightDir L atomOne ^ 2) := by
      intro L hL
      rcases (hdata.activeWeight_nonneg L hL).eq_or_lt with hzero | hpos
      · rw [← hzero]; ring
      · rw [hRowLaw L hL hpos, hPlaneRead L hL hpos]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hassembly atomOne]
  -- the right value
  have hRightValue : ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
      chartP atomOne z * (chartMultiplierAssembly frame.activeSet
          frame.reducedWeight frame.tightDir * chartP) atomOne z
        = (2 * (chartP atomOne atomOne
              - (chartP atomOne atomOne ^ 2 + chartP atomOne atomTwo ^ 2))
            + (2 - 2 * chartP atomOne atomOne)
              * (valueG + weightW atomOne - (2 * chartP atomOne atomOne - 1)))
            * ((6 : ℕ) : ℝ)⁻¹ := by
    have hswap : ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
        chartP atomOne z * (chartMultiplierAssembly frame.activeSet
            frame.reducedWeight frame.tightDir * chartP) atomOne z
          = ∑ L ∈ frame.activeSet, frame.reducedWeight L
              * (frame.tightDir L atomOne
                * (∑ y, frame.tightDir L y
                  * (∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
                      chartP y z * chartP atomOne z))) := by
      have hexp : ∀ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
          chartP atomOne z * (chartMultiplierAssembly frame.activeSet
              frame.reducedWeight frame.tightDir * chartP) atomOne z
            = chartP atomOne z * ∑ L ∈ frame.activeSet, frame.reducedWeight L
                * (frame.tightDir L atomOne
                  * (∑ y, frame.tightDir L y * chartP y z)) :=
        fun z _ => by rw [hRightExpand z]
      rw [Finset.sum_congr rfl hexp]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun L _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun z _ =>
        Finset.sum_congr rfl fun y _ => by ring
    rw [hswap]
    have hterm : ∀ L ∈ frame.activeSet,
        frame.reducedWeight L
            * (frame.tightDir L atomOne
              * (∑ y, frame.tightDir L y
                * (∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
                    chartP y z * chartP atomOne z)))
          = (2 * (chartP atomOne atomOne
                - (chartP atomOne atomOne ^ 2 + chartP atomOne atomTwo ^ 2))
              + (2 - 2 * chartP atomOne atomOne)
                * (valueG + weightW atomOne - (2 * chartP atomOne atomOne - 1)))
              * (frame.reducedWeight L * frame.tightDir L atomOne ^ 2) := by
      intro L hL
      rcases (hdata.activeWeight_nonneg L hL).eq_or_lt with hzero | hpos
      · rw [← hzero]; ring
      · have hinner : ∑ y, frame.tightDir L y
            * (∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
                chartP y z * chartP atomOne z)
          = 2 * frame.tightDir L atomOne
              * (chartP atomOne atomOne
                - (chartP atomOne atomOne ^ 2 + chartP atomOne atomTwo ^ 2))
            + (2 - 2 * chartP atomOne atomOne)
              * ((valueG + weightW atomOne - (2 * chartP atomOne atomOne - 1))
                * frame.tightDir L atomOne) := by
          rw [sum_eq_pair_add_compl hne (value := fun y => frame.tightDir L y
            * (∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
                chartP y z * chartP atomOne z))]
          have hKtwo : ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
              chartP atomTwo z * chartP atomOne z
                = ratio * ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
                    chartP atomOne z * chartP atomOne z := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun z hz => ?_
            obtain ⟨hz1, hz2⟩ := ne_of_mem_pair_compl hz
            rw [hPlane z hz1 hz2]
            ring
          have hKplane : ∑ z' ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
              frame.tightDir L z'
                * (∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
                    chartP z' z * chartP atomOne z)
                = (2 - 2 * chartP atomOne atomOne)
                  * ∑ z' ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
                      chartP atomOne z' * frame.tightDir L z' := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun z' hz' => ?_
            rw [hEigen z' hz']
            ring
          rw [hKtwo, hKplane, hcloneAll L hL hpos, hRho, hPlaneRead L hL hpos]
          linear_combination frame.tightDir L atomOne
            * (chartP atomOne atomOne
              - (chartP atomOne atomOne ^ 2 + chartP atomOne atomTwo ^ 2)) * hsq
        rw [hinner]
        ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hassembly atomOne]
  -- the commutation forces the endgame equation
  have hagree : ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
      chartP atomOne z * (chartP * chartMultiplierAssembly frame.activeSet
          frame.reducedWeight frame.tightDir) atomOne z
        = ∑ z ∈ ({atomOne, atomTwo} : Finset (Fin 6))ᶜ,
            chartP atomOne z * (chartMultiplierAssembly frame.activeSet
                frame.reducedWeight frame.tightDir * chartP) atomOne z :=
    Finset.sum_congr rfl fun z _ => by rw [hcomm]
  rw [hLeftValue, hRightValue] at hagree
  have hsix : ((6 : ℕ) : ℝ)⁻¹ ≠ 0 := by norm_num
  have hmain : (valueG + weightW atomOne)
      * (valueG + weightW atomOne - (2 * chartP atomOne atomOne - 1))
        = 2 * (chartP atomOne atomOne
            - (chartP atomOne atomOne ^ 2 + chartP atomOne atomTwo ^ 2))
          + (2 - 2 * chartP atomOne atomOne)
            * (valueG + weightW atomOne - (2 * chartP atomOne atomOne - 1)) :=
    mul_right_cancel₀ hsix hagree
  rw [hP12] at hmain
  have hdead : (valueG + weightW atomOne) * (1 - (valueG + weightW atomOne)) = 0 :=
    pair_commutation_endgame hsq hmain
  have hlive : 0 < (valueG + weightW atomOne) * (1 - (valueG + weightW atomOne)) :=
    mul_pos hshiftPos (by linarith)
  exact absurd hdead (ne_of_gt hlive)

end PairKill

/-! ## Layer 2 — the cell rests on the wide residue -/

section WideSpine

/-- **THE FLOORED RESIDUE FROM THE WIDE RESIDUE ALONE.**  The pair
branch is a theorem, thus the trichotomy needs only the wide branch. -/
theorem rankFourChartNullBasisNullFloored_of_wide
    (hwide : RankFourCaptureLineWideFlooredClosed) :
    RankFourChartNullBasisNullFlooredClosed :=
  rankFourChartNullBasisNullFloored_of_pair_wide
    rankFourCaptureLinePairFlooredClosed_holds hwide

/-- The floored rank-four rung from the wide residue alone. -/
theorem isSixThreeAssemblyRankExcludedFloored_four_of_wide
    (hwide : RankFourCaptureLineWideFlooredClosed) :
    IsSixThreeAssemblyRankExcludedFloored 4 :=
  isSixThreeAssemblyRankExcludedFloored_four_of_chartNullBasisNullFloored
    (rankFourChartNullBasisNullFloored_of_wide hwide)

/-- **THE CELL FROM THE WIDE RESIDUE AND THE SIX UPPER CLOSURES.** -/
theorem gtzWeighted_six_three_of_wideResidue_of_upperClosures
    (hwide : RankFourCaptureLineWideFlooredClosed)
    (hfiveOne : RankFiveSupportTwoClosed)
    (hfiveTwo : RankFiveSharedPrivateClosed)
    (hfiveDense : RankFiveDenseClosed)
    (hsixOne : RankSixSupportTwoClosed)
    (hsixTwo : RankSixSharedPrivateClosed)
    (hsixDense : RankSixDenseClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_captureLine_residues
    rankFourCaptureLinePairFlooredClosed_holds hwide hfiveOne hfiveTwo hfiveDense
    hsixOne hsixTwo hsixDense

/-- The rank-three payoff from the wide residue and the six upper
closures. -/
theorem gtzWeightedAll_three_of_wideResidue_of_upperClosures
    (hwide : RankFourCaptureLineWideFlooredClosed)
    (hfiveOne : RankFiveSupportTwoClosed)
    (hfiveTwo : RankFiveSharedPrivateClosed)
    (hfiveDense : RankFiveDenseClosed)
    (hsixOne : RankSixSupportTwoClosed)
    (hsixTwo : RankSixSharedPrivateClosed)
    (hsixDense : RankSixDenseClosed) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three
    (gtzWeighted_six_three_of_wideResidue_of_upperClosures hwide hfiveOne hfiveTwo
      hfiveDense hsixOne hsixTwo hsixDense)

end WideSpine

end Gtz
