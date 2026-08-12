import Gtz.Quantitative.CapturedRankFloor
import Gtz.Quantitative.ChartMultiplierSplit
import Gtz.Wave.RankOneCaptureBridge


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ}
variable {weight : Fin size → ℝ} {value : ℝ}
variable {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → Fin size → ℝ}

/-- A direction spanning a nonzero rank-one complementary stationary assembly
lies in the kernel of the chart projection. -/
theorem complementDirection_fixed_of_rankOne
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (direction : Fin size → ℝ)
    (hdirectionUnit : direction ⬝ᵥ direction = 1)
    (scale : ℝ)
    (hproduct : (1 - projection) *
        chartMultiplierAssembly activeSet activeWeight tightDir =
      scale • atomMatrix direction)
    (hscalePositive : 0 < scale) :
    (1 - projection) *ᵥ direction = direction := by
  let complement := 1 - projection
  let assembly := chartMultiplierAssembly activeSet activeWeight tightDir
  have hcomplementIdempotent : complement * complement = complement := by
    dsimp only [complement]
    rw [sub_mul, Matrix.one_mul, mul_sub, Matrix.mul_one, hdata.isIdempotent,
      sub_self, sub_zero]
  have hinvariant : complement * (complement * assembly) = complement * assembly := by
    rw [← Matrix.mul_assoc, hcomplementIdempotent]
  have hproduct' : complement * assembly = scale • atomMatrix direction := by
    simpa only [complement, assembly] using hproduct
  rw [hproduct'] at hinvariant
  have happly := congrArg
    (fun form : Matrix (Fin size) (Fin size) ℝ => form *ᵥ direction) hinvariant
  rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul,
    hdirectionUnit, one_smul, Matrix.mulVec_smul] at happly
  apply funext
  intro atomIndex
  have hcoordinate := congrFun happly atomIndex
  simp only [Pi.smul_apply, smul_eq_mul] at hcoordinate
  nlinarith

/-- A positively weighted tight direction projects onto the unique line of a
rank-one complementary stationary assembly. -/
theorem complementProjected_tightDir_eq_smul_of_rankOne
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (direction : Fin size → ℝ)
    (hdirectionUnit : direction ⬝ᵥ direction = 1)
    (hdirectionFixed : (1 - projection) *ᵥ direction = direction)
    (scale : ℝ)
    (hproduct : (1 - projection) *
        chartMultiplierAssembly activeSet activeWeight tightDir =
      scale • atomMatrix direction)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet)
    (hweightPositive : 0 < activeWeight activeLabel) :
    (1 - projection) *ᵥ tightDir activeLabel =
      (direction ⬝ᵥ ((1 - projection) *ᵥ tightDir activeLabel)) • direction := by
  let complement := 1 - projection
  let captured := complement *ᵥ tightDir activeLabel
  let coefficient := direction ⬝ᵥ captured
  let residual := captured - coefficient • direction
  have hcomplementSymmetric : complementᵀ = complement := by
    dsimp only [complement]
    rw [Matrix.transpose_sub, Matrix.transpose_one, hdata.isSymmetric]
  have hcomplementIdempotent : complement * complement = complement := by
    dsimp only [complement]
    rw [sub_mul, Matrix.one_mul, mul_sub, Matrix.mul_one, hdata.isIdempotent,
      sub_self, sub_zero]
  have hcapturedFixed : complement *ᵥ captured = captured := by
    dsimp only [captured]
    rw [Matrix.mulVec_mulVec, hcomplementIdempotent]
  have hresidualFixed : complement *ᵥ residual = residual := by
    dsimp only [residual]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hcapturedFixed, hdirectionFixed]
  have hresidualOrthogonal : direction ⬝ᵥ residual = 0 := by
    exact dotProduct_sub_projection_unit direction captured hdirectionUnit
  have hrankOneZero : residual ⬝ᵥ
      (((1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir) *ᵥ
        residual) = 0 := by
    rw [hproduct, Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul]
    simp [hresidualOrthogonal]
  have hassemblyZero : residual ⬝ᵥ
      (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ residual) = 0 := by
    calc
      residual ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ residual) =
          (complementᵀ *ᵥ residual) ⬝ᵥ
            (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ residual) := by
              rw [hcomplementSymmetric, hresidualFixed]
      _ = residual ⬝ᵥ (complement *ᵥ
            (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ residual)) :=
        dotProduct_mulVec_transpose complement residual _
      _ = residual ⬝ᵥ (((1 - projection) *
            chartMultiplierAssembly activeSet activeWeight tightDir) *ᵥ residual) := by
        dsimp only [complement]
        rw [Matrix.mulVec_mulVec]
      _ = 0 := hrankOneZero
  have hsumZero :
      ∑ label ∈ activeSet,
          activeWeight label * (tightDir label ⬝ᵥ residual) ^ 2 = 0 := by
    rw [← dotProduct_mulVec_chartMultiplierAssembly]
    exact hassemblyZero
  have hselectedNonneg : 0 ≤
      activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ residual) ^ 2 :=
    mul_nonneg hweightPositive.le (sq_nonneg _)
  have hselectedLe :
      activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ residual) ^ 2 ≤ 0 := by
    rw [← hsumZero]
    exact Finset.single_le_sum
      (s := activeSet)
      (f := fun label => activeWeight label * (tightDir label ⬝ᵥ residual) ^ 2)
      (fun label hlabel =>
        mul_nonneg (hdata.activeWeight_nonneg label hlabel) (sq_nonneg _)) hmem
  have hselectedZero : tightDir activeLabel ⬝ᵥ residual = 0 := by
    have hzero : activeWeight activeLabel *
        (tightDir activeLabel ⬝ᵥ residual) ^ 2 = 0 :=
      le_antisymm hselectedLe hselectedNonneg
    rcases mul_eq_zero.mp hzero with hweightZero | hsquareZero
    · exact (ne_of_gt hweightPositive hweightZero).elim
    · exact sq_eq_zero_iff.mp hsquareZero
  have hcapturedPair : captured ⬝ᵥ residual = 0 := by
    calc
      captured ⬝ᵥ residual =
          (complementᵀ *ᵥ tightDir activeLabel) ⬝ᵥ residual := by
            dsimp only [captured]
            rw [hcomplementSymmetric]
      _ = tightDir activeLabel ⬝ᵥ (complement *ᵥ residual) :=
        dotProduct_mulVec_transpose complement (tightDir activeLabel) residual
      _ = tightDir activeLabel ⬝ᵥ residual := by rw [hresidualFixed]
      _ = 0 := hselectedZero
  have hresidualNorm : residual ⬝ᵥ residual = 0 := by
    rw [← hcapturedPair]
    exact (dotProduct_residual_eq_self direction captured hdirectionUnit).symm
  have hresidualZero : residual = 0 := by
    apply funext
    intro atomIndex
    have hsumSquares : ∑ index : Fin size, residual index ^ 2 = 0 := by
      simpa only [dotProduct_self_eq_sum_sq] using hresidualNorm
    have htermNonneg : ∀ index ∈ (Finset.univ : Finset (Fin size)),
        0 ≤ residual index ^ 2 := fun index _ => sq_nonneg _
    have htermZero := Finset.sum_eq_zero_iff_of_nonneg htermNonneg |>.mp
      hsumSquares atomIndex (Finset.mem_univ atomIndex)
    exact sq_eq_zero_iff.mp htermZero
  change captured = coefficient • direction
  dsimp only [residual] at hresidualZero
  exact sub_eq_zero.mp hresidualZero

/-- Complementary rank-one capture pins the stationary value.  The equation is
the Naimark dual of the primal rank-one mass transport: every active subset has
`rank` coordinates, while the complementary shifted masses sum to `size` times
the complementary trace. -/
theorem value_eq_sub_rank_add_one_div_size_of_complementRankOne
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (direction : Fin size → ℝ) (coefficient : activeIndex → ℝ)
    (hdirectionUnit : direction ⬝ᵥ direction = 1)
    (himage : ∀ activeLabel ∈ activeSet,
      (1 - projection) *ᵥ tightDir activeLabel =
        coefficient activeLabel • direction)
    (hproduct : (1 - projection) *
        chartMultiplierAssembly activeSet activeWeight tightDir =
      (1 - value - ((size : ℝ))⁻¹) • atomMatrix direction)
    (htracePositive : 0 < 1 - value - ((size : ℝ))⁻¹)
    (hshiftedPositive : ∀ atomIndex, 0 < 1 - value - weight atomIndex) :
    value = ((size : ℝ) - rank - 1) / size := by
  let complementTrace := 1 - value - ((size : ℝ))⁻¹
  let shiftedComplement : Fin size → ℝ := fun atomIndex =>
    1 - value - weight atomIndex
  let capturedMass : activeIndex → ℝ := fun activeLabel =>
    activeWeight activeLabel * coefficient activeLabel ^ 2
  have hmassSum : ∑ activeLabel ∈ activeSet, capturedMass activeLabel =
      complementTrace := by
    have hfixed := complementDirection_fixed_of_rankOne hdata direction
      hdirectionUnit complementTrace (by simpa only [complementTrace] using hproduct)
      htracePositive
    have hquad := dotProduct_mulVec_chartMultiplierAssembly activeSet activeWeight
      tightDir direction
    have hcoefficient : ∀ activeLabel ∈ activeSet,
        coefficient activeLabel = tightDir activeLabel ⬝ᵥ direction := by
      intro activeLabel hmem
      have himageCoordinate := congrArg (fun vector => direction ⬝ᵥ vector)
        (himage activeLabel hmem)
      rw [dotProduct_smul, smul_eq_mul, hdirectionUnit, mul_one] at himageCoordinate
      calc
        coefficient activeLabel = direction ⬝ᵥ
            ((1 - projection) *ᵥ tightDir activeLabel) := himageCoordinate.symm
        _ = (((1 - projection)ᵀ *ᵥ direction) ⬝ᵥ
            tightDir activeLabel) :=
              (dotProduct_mulVec_transpose (1 - projection) direction _).symm
        _ = direction ⬝ᵥ tightDir activeLabel := by
              rw [Matrix.transpose_sub, Matrix.transpose_one,
                hdata.isSymmetric, hfixed]
        _ = tightDir activeLabel ⬝ᵥ direction := dotProduct_comm _ _
    calc
      ∑ activeLabel ∈ activeSet, capturedMass activeLabel =
          ∑ activeLabel ∈ activeSet,
            activeWeight activeLabel *
              (tightDir activeLabel ⬝ᵥ direction) ^ 2 := by
                refine Finset.sum_congr rfl fun activeLabel hmem => ?_
                dsimp only [capturedMass]
                rw [hcoefficient activeLabel hmem]
      _ = direction ⬝ᵥ
          (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ direction) :=
            hquad.symm
      _ = direction ⬝ᵥ (((1 - projection) *
            chartMultiplierAssembly activeSet activeWeight tightDir) *ᵥ direction) := by
              calc
                direction ⬝ᵥ
                    (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ
                      direction) =
                    (((1 - projection)ᵀ *ᵥ direction) ⬝ᵥ
                      (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ
                        direction)) := by
                          rw [Matrix.transpose_sub, Matrix.transpose_one,
                            hdata.isSymmetric, hfixed]
                _ = direction ⬝ᵥ ((1 - projection) *ᵥ
                    (chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ
                      direction)) :=
                        dotProduct_mulVec_transpose (1 - projection) direction _
                _ = direction ⬝ᵥ (((1 - projection) *
                    chartMultiplierAssembly activeSet activeWeight tightDir) *ᵥ
                      direction) := by rw [Matrix.mulVec_mulVec]
      _ = complementTrace := by
        rw [hproduct, Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul,
          hdirectionUnit, one_smul, dotProduct_smul, hdirectionUnit]
        simp only [smul_eq_mul, mul_one]
        rfl
  have hincident : ∀ atomIndex : Fin size,
      ∑ activeLabel ∈ activeSet.filter
          (fun label => atomIndex ∈ activeSubset label), capturedMass activeLabel =
        complementTrace * shiftedComplement atomIndex := by
    intro atomIndex
    let incident := activeSet.filter
      (fun label => atomIndex ∈ activeSubset label)
    have hsquares : ∑ activeLabel ∈ incident,
        activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2 =
          ((size : ℝ))⁻¹ := by
      have hrestrict :
          ∑ activeLabel ∈ incident,
              activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2 =
            ∑ activeLabel ∈ activeSet,
              activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2 := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro activeLabel hmem hnotIncident
        have hnotSubset : atomIndex ∉ activeSubset activeLabel := by
          intro hcontra
          exact hnotIncident (Finset.mem_filter.mpr ⟨hmem, hcontra⟩)
        rw [hdata.tightDir_support activeLabel hmem atomIndex hnotSubset]
        ring
      rw [hrestrict, ← chartMultiplierAssembly_diagonal,
        hdata.assembly_diagonal atomIndex]
    have hterm : ∀ activeLabel ∈ incident,
        coefficient activeLabel * direction atomIndex =
          shiftedComplement atomIndex * tightDir activeLabel atomIndex := by
      intro activeLabel hmem
      have hactive : activeLabel ∈ activeSet := (Finset.mem_filter.mp hmem).1
      have hatom : atomIndex ∈ activeSubset activeLabel :=
        (Finset.mem_filter.mp hmem).2
      have hcoordinate := congrFun (himage activeLabel hactive) atomIndex
      simp only [Pi.smul_apply, smul_eq_mul] at hcoordinate
      have hprojection :
          (projection *ᵥ tightDir activeLabel) atomIndex =
            (value + weight atomIndex) * tightDir activeLabel atomIndex := by
        exact projection_mulVec_tightDir_of_mem hdata hactive hatom
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at hcoordinate
      dsimp only [shiftedComplement]
      linarith
    have hscaled : direction atomIndex ^ 2 *
        ∑ activeLabel ∈ incident, capturedMass activeLabel =
          shiftedComplement atomIndex ^ 2 * ((size : ℝ))⁻¹ := by
      calc
        direction atomIndex ^ 2 *
            ∑ activeLabel ∈ incident, capturedMass activeLabel =
            ∑ activeLabel ∈ incident,
              activeWeight activeLabel *
                (coefficient activeLabel * direction atomIndex) ^ 2 := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun activeLabel _ => ?_
                  dsimp only [capturedMass]
                  ring
        _ = ∑ activeLabel ∈ incident,
              activeWeight activeLabel *
                (shiftedComplement atomIndex *
                  tightDir activeLabel atomIndex) ^ 2 := by
                    refine Finset.sum_congr rfl fun activeLabel hmem => by
                      rw [hterm activeLabel hmem]
        _ = shiftedComplement atomIndex ^ 2 * ((size : ℝ))⁻¹ := by
              rw [← hsquares, Finset.mul_sum]
              refine Finset.sum_congr rfl fun activeLabel _ => by ring
    have hproductDiagonal := congrArg
      (fun form : Matrix (Fin size) (Fin size) ℝ => form atomIndex atomIndex) hproduct
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply,
      hdata.assembly_diagonal atomIndex,
      diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomIndex,
      Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul] at hproductDiagonal
    have hinvPositive : 0 < ((size : ℝ))⁻¹ :=
      inv_pos.mpr (size_cast_pos_of_isChartStationaryData hdata)
    have hshiftPositive := hshiftedPositive atomIndex
    change shiftedComplement atomIndex > 0 at hshiftPositive
    change complementTrace > 0 at htracePositive
    have hproductDiagonal' :
        shiftedComplement atomIndex * ((size : ℝ))⁻¹ =
          complementTrace * direction atomIndex ^ 2 := by
      dsimp only [shiftedComplement, complementTrace]
      nlinarith [hproductDiagonal]
    have hpositiveProduct : 0 < complementTrace * direction atomIndex ^ 2 := by
      rw [← hproductDiagonal']
      exact mul_pos hshiftPositive hinvPositive
    have hdirectionSqPositive : 0 < direction atomIndex ^ 2 := by
      nlinarith
    change ∑ activeLabel ∈ incident, capturedMass activeLabel =
      complementTrace * shiftedComplement atomIndex
    nlinarith [hscaled, hproductDiagonal', hdirectionSqPositive]
  have hdoubleCount :
      ∑ atomIndex : Fin size,
          ∑ activeLabel ∈ activeSet.filter
            (fun label => atomIndex ∈ activeSubset label), capturedMass activeLabel =
        (rank : ℝ) * ∑ activeLabel ∈ activeSet, capturedMass activeLabel := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun activeLabel hmem => ?_
    have hfilterSum :
        ∑ atomIndex : Fin size,
            (if atomIndex ∈ activeSubset activeLabel then capturedMass activeLabel else 0) =
          ∑ atomIndex ∈ (Finset.univ : Finset (Fin size)).filter
              (fun atomIndex => atomIndex ∈ activeSubset activeLabel),
            capturedMass activeLabel := by
      rw [← Finset.sum_filter]
    have hfilterEq : (Finset.univ : Finset (Fin size)).filter
        (fun atomIndex => atomIndex ∈ activeSubset activeLabel) =
        activeSubset activeLabel := by
      ext atomIndex
      simp
    rw [hfilterSum, hfilterEq, Finset.sum_const, nsmul_eq_mul,
      hdata.activeSubset_card activeLabel hmem]
  have hshiftedSum : ∑ atomIndex : Fin size, shiftedComplement atomIndex =
      (size : ℝ) * complementTrace := by
    simp only [shiftedComplement, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hdata.weight_sum_one]
    have hsizeNe : (size : ℝ) ≠ 0 :=
      ne_of_gt (size_cast_pos_of_isChartStationaryData hdata)
    dsimp only [complementTrace]
    field_simp
  have htransport :
      (rank : ℝ) * complementTrace = (size : ℝ) * complementTrace ^ 2 := by
    calc
      (rank : ℝ) * complementTrace =
          (rank : ℝ) * ∑ activeLabel ∈ activeSet, capturedMass activeLabel := by
            rw [hmassSum]
      _ = ∑ atomIndex : Fin size,
          ∑ activeLabel ∈ activeSet.filter
            (fun label => atomIndex ∈ activeSubset label), capturedMass activeLabel :=
              hdoubleCount.symm
      _ = ∑ atomIndex : Fin size,
          complementTrace * shiftedComplement atomIndex := by
            refine Finset.sum_congr rfl fun atomIndex _ => hincident atomIndex
      _ = complementTrace * ∑ atomIndex : Fin size,
          shiftedComplement atomIndex := by rw [Finset.mul_sum]
      _ = (size : ℝ) * complementTrace ^ 2 := by
            rw [hshiftedSum]
            ring
  have htraceEq : complementTrace = (rank : ℝ) / size := by
    have hsizePositive := size_cast_pos_of_isChartStationaryData hdata
    field_simp
    nlinarith
  dsimp only [complementTrace] at htraceEq
  have hsizeNe : (size : ℝ) ≠ 0 :=
    ne_of_gt (size_cast_pos_of_isChartStationaryData hdata)
  field_simp
  field_simp at htraceEq
  linarith

/-- At `(6,3)`, a negative stationary datum cannot have complementary captured
range of dimension at most one.  Rank zero is included: the complementary trace
is strictly positive, so the factorization automatically produces a genuine
unit line. -/
theorem false_of_complementProjectedMultiplier_range_finrank_le_one_sixThree
    {projection : Matrix (Fin 6) (Fin 6) ℝ}
    {weight : Fin 6 → ℝ} {value : ℝ}
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3 projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hvalueNegative : value < 0)
    (hweightLtOne : ∀ atomIndex, weight atomIndex < 1)
    (hactiveWeightPositive : ∀ activeLabel ∈ activeSet,
      0 < activeWeight activeLabel)
    (hrange : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      ((1 - projection) *
        chartMultiplierAssembly activeSet activeWeight tightDir))) ≤ 1) :
    False := by
  let assembly := chartMultiplierAssembly activeSet activeWeight tightDir
  let complement := 1 - projection
  let captured := complement * assembly
  have htrace : Matrix.trace captured = 1 - value - (6 : ℝ)⁻¹ := by
    dsimp only [captured, complement, assembly]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
      trace_chartMultiplierAssembly_of_isChartStationaryData hdata,
      trace_projection_mul_multiplier_of_isChartStationaryData hdata]
    ring
  have htracePositive : 0 < Matrix.trace captured := by
    rw [htrace]
    norm_num
    linarith
  have hcomplementConjTranspose :
      (complement : Matrix (Fin 6) (Fin 6) ℝ)ᴴ = complement := by
    dsimp only [complement]
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_one, hdata.isSymmetric]
  have hcapturedPsd : captured.PosSemidef := by
    have hsandwich := (posSemidef_chartMultiplierAssembly_of_isChartStationaryData hdata).mul_mul_conjTranspose_same complement
    rw [hcomplementConjTranspose] at hsandwich
    dsimp only [captured, complement, assembly]
    rw [complementProjection_mul_multiplier_eq_sandwich_of_isChartStationaryData hdata]
    exact hsandwich
  have hcapturedSymmetric : capturedᵀ = captured :=
    transpose_eq_of_isHermitian hcapturedPsd.1
  obtain ⟨direction, hdirectionUnit, hfactor⟩ :=
    exists_unit_eq_trace_smul_atomMatrix_of_symmetric_of_range_finrank_le_one
      captured hcapturedSymmetric (by simpa only [captured, complement, assembly] using hrange)
      htracePositive
  have hfactor' : complement * assembly =
      (1 - value - (6 : ℝ)⁻¹) • atomMatrix direction := by
    dsimp only [captured] at hfactor
    rw [htrace] at hfactor
    exact hfactor
  have hdirectionFixed := complementDirection_fixed_of_rankOne hdata direction
    hdirectionUnit (1 - value - (6 : ℝ)⁻¹)
    (by simpa only [complement, assembly] using hfactor') (by
      norm_num
      linarith)
  let coefficient : activeIndex → ℝ := fun activeLabel =>
    direction ⬝ᵥ (complement *ᵥ tightDir activeLabel)
  have himage : ∀ activeLabel ∈ activeSet,
      (1 - projection) *ᵥ tightDir activeLabel =
        coefficient activeLabel • direction := by
    intro activeLabel hmem
    exact complementProjected_tightDir_eq_smul_of_rankOne hdata direction
      hdirectionUnit (by simpa only [complement] using hdirectionFixed)
      (1 - value - (6 : ℝ)⁻¹)
      (by simpa only [complement, assembly] using hfactor') hmem
      (hactiveWeightPositive activeLabel hmem)
  have hshiftedPositive : ∀ atomIndex, 0 < 1 - value - weight atomIndex := by
    intro atomIndex
    linarith [hweightLtOne atomIndex]
  have hvalue := value_eq_sub_rank_add_one_div_size_of_complementRankOne
    hdata direction coefficient hdirectionUnit himage
    (by simpa [complement, assembly] using hfactor') (by
      norm_num
      linarith) hshiftedPositive
  norm_num at hvalue
  linarith

/-- The primal captured range also cannot have dimension at most one at a
negative stationary `(6,3)` point once its trace is positive. -/
theorem false_of_projectedMultiplier_range_finrank_le_one_sixThree
    {projection : Matrix (Fin 6) (Fin 6) ℝ}
    {weight : Fin 6 → ℝ} {value : ℝ}
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3 projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hvalueNegative : value < 0)
    (htracePositive : 0 < value + (6 : ℝ)⁻¹)
    (hactiveWeightPositive : ∀ activeLabel ∈ activeSet,
      0 < activeWeight activeLabel)
    (hrange : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      (projection * chartMultiplierAssembly activeSet activeWeight tightDir))) ≤ 1) :
    False := by
  let captured := projection *
    chartMultiplierAssembly activeSet activeWeight tightDir
  have hcapturedPsd : captured.PosSemidef := by
    dsimp only [captured]
    exact posSemidef_projection_mul_multiplier_of_isChartStationaryData hdata
  have hcapturedSymmetric : capturedᵀ = captured :=
    transpose_eq_of_isHermitian hcapturedPsd.1
  have htrace : Matrix.trace captured = value + (6 : ℝ)⁻¹ := by
    dsimp only [captured]
    exact trace_projection_mul_multiplier_of_isChartStationaryData hdata
  obtain ⟨direction, hdirectionUnit, hfactor⟩ :=
    exists_unit_eq_trace_smul_atomMatrix_of_symmetric_of_range_finrank_le_one
      captured hcapturedSymmetric (by simpa only [captured] using hrange)
      (by rw [htrace]; exact htracePositive)
  have hfactor' : projection *
      chartMultiplierAssembly activeSet activeWeight tightDir =
      (value + (6 : ℝ)⁻¹) • atomMatrix direction := by
    dsimp only [captured] at hfactor
    rw [htrace] at hfactor
    exact hfactor
  have hnonnegative := value_nonneg_of_projectedMultiplier_rankOne_of_activeWeight_pos
    hdata direction hdirectionUnit hfactor' htracePositive hactiveWeightPositive
  linarith

end Gtz
