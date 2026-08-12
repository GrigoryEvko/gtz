import Gtz.Wave.CrossSupportedTightExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-! **THE ISOLATED-ROW PROJECTION KILL.**  A tight row whose support is
disjoint from every other active support is an eigenvector of the multiplier
assembly with eigenvalue its own multiplier, and an isolated support atom
floors that multiplier at `1/6`.  Since the captured product `P * assembly`
is positive semidefinite with trace `value + 1/6 < 1/6`, the projection must
annihilate the row outright.  Tightness then pins the weights on the support
at `-value`, and on a pair support the landed parallel-pair floor closes.
This is the engine for every disconnected support profile. -/

/-- **RAYLEIGH BOUND BY THE TRACE.**  A nonzero eigenvector of a positive
semidefinite real matrix has its eigenvalue bounded by the trace. -/
theorem eigenvalue_le_trace_of_posSemidef {dimension : ℕ}
    {psdMatrix : Matrix (Fin dimension) (Fin dimension) ℝ}
    (hpsd : psdMatrix.PosSemidef) {eigenvalue : ℝ} {eigenvector : Fin dimension → ℝ}
    (heigen : psdMatrix *ᵥ eigenvector = eigenvalue • eigenvector)
    (hnonzero : eigenvector ≠ 0) :
    eigenvalue ≤ Matrix.trace psdMatrix := by
  classical
  have hsym : psdMatrixᵀ = psdMatrix := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hpsd.isHermitian
  have hnormNonneg : 0 ≤ eigenvector ⬝ᵥ eigenvector :=
    Finset.sum_nonneg fun index _ => mul_self_nonneg (eigenvector index)
  have hnormPos : 0 < eigenvector ⬝ᵥ eigenvector := by
    rcases lt_or_eq_of_le hnormNonneg with hpos | hzero
    · exact hpos
    · exact absurd (dotProduct_self_eq_zero.mp hzero.symm) hnonzero
  have hentry : ∀ index : Fin dimension,
      eigenvalue * (eigenvector index * eigenvector index)
        ≤ psdMatrix index index * (eigenvector ⬝ᵥ eigenvector) := by
    intro index
    have hquad := hpsd.dotProduct_mulVec_nonneg
      ((eigenvector ⬝ᵥ eigenvector) • Pi.single index (1 : ℝ)
        - eigenvector index • eigenvector)
    rw [star_trivial] at hquad
    have hprobe : ((eigenvector ⬝ᵥ eigenvector) • Pi.single index (1 : ℝ)
        - eigenvector index • eigenvector) ⬝ᵥ (psdMatrix *ᵥ
          ((eigenvector ⬝ᵥ eigenvector) • Pi.single index (1 : ℝ)
            - eigenvector index • eigenvector))
        = (eigenvector ⬝ᵥ eigenvector) * (eigenvector ⬝ᵥ eigenvector)
            * psdMatrix index index
          - eigenvalue * (eigenvector index * eigenvector index)
            * (eigenvector ⬝ᵥ eigenvector) := by
      have hsingleImage : psdMatrix *ᵥ Pi.single index (1 : ℝ)
          = fun rowIndex => psdMatrix rowIndex index := by
        funext rowIndex
        rw [Matrix.mulVec_single]
        exact mul_one _
      have hsingleQuad : Pi.single index (1 : ℝ) ⬝ᵥ
          (fun rowIndex => psdMatrix rowIndex index) = psdMatrix index index := by
        rw [single_dotProduct]
        exact one_mul _
      have hsingleCross : eigenvector ⬝ᵥ (fun rowIndex => psdMatrix rowIndex index)
          = eigenvalue * eigenvector index := by
        calc eigenvector ⬝ᵥ (fun rowIndex => psdMatrix rowIndex index)
            = (psdMatrixᵀ *ᵥ eigenvector) index := by
              rw [Matrix.mulVec]
              simp [dotProduct, Matrix.transpose_apply, mul_comm]
          _ = eigenvalue * eigenvector index := by
              rw [hsym, heigen]
              rfl
      have hcrossSingle : Pi.single index (1 : ℝ) ⬝ᵥ (psdMatrix *ᵥ eigenvector)
          = eigenvalue * eigenvector index := by
        rw [heigen, single_dotProduct]
        simp [Pi.smul_apply, smul_eq_mul]
      have heigenQuad : eigenvector ⬝ᵥ (psdMatrix *ᵥ eigenvector)
          = eigenvalue * (eigenvector ⬝ᵥ eigenvector) := by
        rw [heigen, dotProduct_smul, smul_eq_mul]
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hsingleImage]
      rw [sub_dotProduct, smul_dotProduct, smul_dotProduct,
        dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul,
        dotProduct_smul, dotProduct_smul, hsingleQuad, hsingleCross,
        hcrossSingle, heigenQuad]
      simp only [smul_eq_mul]
      ring
    rw [hprobe] at hquad
    nlinarith [hnormPos]
  have hsumBound := Finset.sum_le_sum (fun index (_ : index ∈ Finset.univ) => hentry index)
  have hleft : ∑ index : Fin dimension,
      eigenvalue * (eigenvector index * eigenvector index)
        = eigenvalue * (eigenvector ⬝ᵥ eigenvector) := by
    rw [← Finset.mul_sum]
    rfl
  have hright : ∑ index : Fin dimension,
      psdMatrix index index * (eigenvector ⬝ᵥ eigenvector)
        = Matrix.trace psdMatrix * (eigenvector ⬝ᵥ eigenvector) := by
    rw [← Finset.sum_mul]
    rfl
  rw [hleft, hright] at hsumBound
  exact le_of_mul_le_mul_right hsumBound hnormPos

/-- An active row orthogonal to every other active row is an eigenvector of
the multiplier assembly, with its own multiplier as eigenvalue. -/
theorem chartMultiplierAssembly_mulVec_eq_smul_of_orthogonal
    {size : ℕ} {activeIndex : Type*} [DecidableEq activeIndex]
    {activeSet : Finset activeIndex} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)} {hostLabel : activeIndex}
    (hhostMem : hostLabel ∈ activeSet)
    (hunit : tightDir hostLabel ⬝ᵥ tightDir hostLabel = 1)
    (horthogonal : ∀ otherLabel ∈ activeSet, otherLabel ≠ hostLabel →
      tightDir otherLabel ⬝ᵥ tightDir hostLabel = 0) :
    chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ tightDir hostLabel
      = activeWeight hostLabel • tightDir hostLabel := by
  classical
  funext rowIndex
  have hexpand : (chartMultiplierAssembly activeSet activeWeight tightDir
      *ᵥ tightDir hostLabel) rowIndex
      = ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * tightDir activeLabel rowIndex
          * (tightDir activeLabel ⬝ᵥ tightDir hostLabel) := by
    simp only [Matrix.mulVec, dotProduct, chartMultiplierAssembly_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun activeLabel _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun colIndex _ => ?_
    ring
  rw [hexpand, Finset.sum_eq_single_of_mem hostLabel hhostMem]
  · rw [hunit, Pi.smul_apply, smul_eq_mul]
    ring
  · intro otherLabel hotherMem hotherNe
    rw [horthogonal otherLabel hotherMem hotherNe]
    ring

/-- **THE PROJECTION ANNIHILATES AN ISOLATED ROW.**  If the row is orthogonal
to every other active row and its multiplier is at least `1/6`, the captured
image `P *ᵥ row` would be a `PA`-eigenvector with eigenvalue at least `1/6`,
against the captured trace `value + 1/6 < 1/6`. -/
theorem SixThreeCrux.projection_mulVec_eq_zero_of_orthogonal_of_sixth_le_multiplier
    (crux : SixThreeCrux)
    {multiplier : Finset (Fin 6) → ℝ} {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    {hostBlock : Finset (Fin 6)}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir)
    (hhostMem : hostBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (horthogonal : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      otherBlock ≠ hostBlock → tightDir otherBlock ⬝ᵥ tightDir hostBlock = 0)
    (hmultiplierFloor : 1 / 6 ≤ multiplier hostBlock) :
    (chartPointOfDesign crux.design).chart *ᵥ tightDir hostBlock = 0 := by
  classical
  by_contra hcapturedNonzero
  have hassemblyEigen := chartMultiplierAssembly_mulVec_eq_smul_of_orthogonal
    (activeWeight := multiplier) hhostMem
    (hdata.tightDir_unit hostBlock hhostMem) horthogonal
  set projection := (chartPointOfDesign crux.design).chart
  set assembly := chartMultiplierAssembly
    (chartArgmaxFamily (chartPointOfDesign crux.design)) multiplier tightDir
  have hcapturedEigen : (projection * assembly) *ᵥ (projection *ᵥ tightDir hostBlock)
      = multiplier hostBlock • (projection *ᵥ tightDir hostBlock) := by
    rw [← Matrix.mulVec_mulVec]
    have hswap : assembly *ᵥ (projection *ᵥ tightDir hostBlock)
        = projection *ᵥ (assembly *ᵥ tightDir hostBlock) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hdata.assembly_commutes]
    rw [hswap, hassemblyEigen, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, hdata.isIdempotent]
  have heigenvalueBound := eigenvalue_le_trace_of_posSemidef
    (posSemidef_projection_mul_multiplier_of_isChartStationaryData hdata)
    hcapturedEigen hcapturedNonzero
  rw [trace_projection_mul_multiplier_of_isChartStationaryData hdata] at heigenvalueBound
  have hnegative := crux.hasNegativeChartValue
  norm_num at heigenvalueBound
  linarith

/-- An isolated support atom floors the multiplier at `1/6`: the assembly
diagonal reads `1/6` there and only the host row contributes. -/
theorem SixThreeCrux.sixth_le_multiplier_of_isolated_support_atom
    (crux : SixThreeCrux)
    {tightVec : Finset (Fin 6) → (Fin 3 → ℝ)} {multiplier : Finset (Fin 6) → ℝ}
    {hostBlock : Finset (Fin 6)} {atomIndex : Fin 6}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
      (ambientTightSelection tightVec))
    (hhostMem : hostBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hatomMem : atomIndex ∈ totalTightSupport tightVec hostBlock)
    (hothersVanish : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      otherBlock ≠ hostBlock →
        totalEigenSquareRow tightVec otherBlock atomIndex = 0) :
    1 / 6 ≤ multiplier hostBlock := by
  classical
  have hhostCard : hostBlock.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) hostBlock).mp hhostMem).1
  have hrowEq : ∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      ∀ atom : Fin 6,
        totalEigenSquareRow tightVec selected atom
          = ambientTightSelection tightVec selected atom
              * ambientTightSelection tightVec selected atom := by
    intro selected hmember atom
    have hcard : selected.card = 3 :=
      ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmember).1
    exact totalEigenSquareRow_eq_ambientTightSelection_mul_self tightVec hcard atom
  have hassembly := assemblyDiagonal_of_isChartStationaryData_of_rowEq hdata
    (totalEigenSquareRow tightVec) hrowEq atomIndex
  rw [Finset.sum_eq_single_of_mem hostBlock hhostMem
    (fun otherBlock hotherMem hotherNe => by
      rw [hothersVanish otherBlock hotherMem hotherNe, mul_zero])] at hassembly
  have hrowLe : totalEigenSquareRow tightVec hostBlock atomIndex ≤ 1 := by
    have hunit := hdata.tightDir_unit hostBlock hhostMem
    have hrowSum : ∑ atom : Fin 6, totalEigenSquareRow tightVec hostBlock atom = 1 := by
      rw [← hunit]
      exact Finset.sum_congr rfl fun atom _ =>
        hrowEq hostBlock hhostMem atom
    calc totalEigenSquareRow tightVec hostBlock atomIndex
        ≤ ∑ atom : Fin 6, totalEigenSquareRow tightVec hostBlock atom :=
          Finset.single_le_sum
            (fun atom _ => totalEigenSquareRow_nonneg tightVec hostBlock atom)
            (Finset.mem_univ atomIndex)
      _ = 1 := hrowSum
  have hrowPos : 0 < totalEigenSquareRow tightVec hostBlock atomIndex :=
    totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec hhostCard hatomMem
  nlinarith [hassembly, hrowLe, hrowPos]

/-- **THE ISOLATED PAIR ROW DIES.**  A pair-supported row whose two atoms are
covered by no other active support forces its projection image to vanish, so
both support weights equal `-value` — the landed parallel-pair floor. -/
theorem SixThreeCrux.false_of_isolated_pair_row
    (crux : SixThreeCrux)
    {tightVec : Finset (Fin 6) → (Fin 3 → ℝ)} {multiplier : Finset (Fin 6) → ℝ}
    {hostBlock : Finset (Fin 6)} {atomA atomB : Fin 6}
    (hatomsNe : atomA ≠ atomB)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
      (ambientTightSelection tightVec))
    (hhostMem : hostBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hsupportEq : totalTightSupport tightVec hostBlock
      = ({atomA, atomB} : Finset (Fin 6)))
    (hisolatedA : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      otherBlock ≠ hostBlock →
        totalEigenSquareRow tightVec otherBlock atomA = 0)
    (hisolatedB : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      otherBlock ≠ hostBlock →
        totalEigenSquareRow tightVec otherBlock atomB = 0) :
    False := by
  classical
  have hhostCard : hostBlock.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) hostBlock).mp hhostMem).1
  have hselectionOff : ∀ atom : Fin 6, atom ∉ ({atomA, atomB} : Finset (Fin 6)) →
      ambientTightSelection tightVec hostBlock atom = 0 := by
    intro atom hnotPair
    refine ambientTightSelection_eq_zero_of_totalEigenSquareRow_eq_zero tightVec
      hostBlock hhostCard atom
      (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec hhostCard ?_)
    rw [hsupportEq]
    exact hnotPair
  have horthogonal : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      otherBlock ≠ hostBlock →
        ambientTightSelection tightVec otherBlock
          ⬝ᵥ ambientTightSelection tightVec hostBlock = 0 := by
    intro otherBlock hotherMem hotherNe
    have hotherCard : otherBlock.card = 3 :=
      ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) otherBlock).mp
        hotherMem).1
    refine Finset.sum_eq_zero fun atom _ => ?_
    by_cases hpairMem : atom ∈ ({atomA, atomB} : Finset (Fin 6))
    · have hotherZero : ambientTightSelection tightVec otherBlock atom = 0 := by
        refine ambientTightSelection_eq_zero_of_totalEigenSquareRow_eq_zero tightVec
          otherBlock hotherCard atom ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpairMem
        rcases hpairMem with rfl | rfl
        · exact hisolatedA otherBlock hotherMem hotherNe
        · exact hisolatedB otherBlock hotherMem hotherNe
      rw [hotherZero, zero_mul]
    · rw [hselectionOff atom hpairMem, mul_zero]
  have hatomAMem : atomA ∈ totalTightSupport tightVec hostBlock := by
    rw [hsupportEq]
    exact Finset.mem_insert_self _ _
  have hatomBMem : atomB ∈ totalTightSupport tightVec hostBlock := by
    rw [hsupportEq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hmultiplierFloor := crux.sixth_le_multiplier_of_isolated_support_atom hdata
    hhostMem hatomAMem hisolatedA
  have hprojectionZero :=
    crux.projection_mulVec_eq_zero_of_orthogonal_of_sixth_le_multiplier hdata
      hhostMem horthogonal hmultiplierFloor
  have hselectionNe : ∀ atom ∈ totalTightSupport tightVec hostBlock,
      ambientTightSelection tightVec hostBlock atom ≠ 0 := by
    intro atom hatomMem hzero
    have hrowNe := (totalEigenSquareRow_ne_zero_iff_mem_totalTightSupport tightVec
      hhostCard).mpr hatomMem
    rw [totalEigenSquareRow_eq_ambientTightSelection_mul_self tightVec hhostCard,
      hzero, mul_zero] at hrowNe
    exact hrowNe rfl
  have hweightAt : ∀ atom ∈ totalTightSupport tightVec hostBlock,
      crux.design.weight atom
        = -chartObjective (chartPointOfDesign crux.design) := by
    intro atom hatomMem
    have hatomBlock : atom ∈ hostBlock :=
      totalTightSupport_subset tightVec hhostCard hatomMem
    have htight := hdata.tightDir_isTight hostBlock hhostMem atom hatomBlock
    rw [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply, hprojectionZero] at htight
    have hdiag : (Matrix.diagonal (chartPointOfDesign crux.design).weight
        *ᵥ ambientTightSelection tightVec hostBlock) atom
        = (chartPointOfDesign crux.design).weight atom
            * ambientTightSelection tightVec hostBlock atom := by
      rw [Matrix.mulVec_diagonal]
    rw [hdiag] at htight
    have hweightPoint : (chartPointOfDesign crux.design).weight atom
        = crux.design.weight atom := rfl
    have hselNe := hselectionNe atom hatomMem
    have hzeroAt : (0 : ℝ) = 0 := rfl
    have hbalance : -(crux.design.weight atom
        * ambientTightSelection tightVec hostBlock atom)
        = chartObjective (chartPointOfDesign crux.design)
            * ambientTightSelection tightVec hostBlock atom := by
      rw [← hweightPoint]
      simpa using htight
    have hfactor : (-(crux.design.weight atom)
        - chartObjective (chartPointOfDesign crux.design))
        * ambientTightSelection tightVec hostBlock atom = 0 := by
      ring_nf
      ring_nf at hbalance
      linarith
    rcases mul_eq_zero.mp hfactor with hcoeff | hsel
    · linarith
    · exact absurd hsel hselNe
  exact crux.not_both_weight_eq_neg_of_tightDirection_support_pair hhostMem
    (isChartTightDirection_of_isChartStationaryData hdata hhostMem)
    hatomsNe (hselectionNe atomA hatomAMem) (hselectionNe atomB hatomBMem)
    hselectionOff
    ⟨hweightAt atomA hatomAMem, hweightAt atomB hatomBMem⟩

end Gtz
