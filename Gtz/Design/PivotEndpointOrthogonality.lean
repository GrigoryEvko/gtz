import Gtz.Design.PivotStallPropagation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The priced pivot endpoint is an orthogonality endpoint

The first pivot-wall propagation leaves a five-label endpoint in which the
four old pivots remain at least one.  The incoming pointer started at pivot
exactly one, while rank-one insertion can only decrease it.  Hence it remains
exactly one, and the exact cross update forces one inverse-form cross term to
vanish.

This module identifies the geometric meaning of that equality.  If a singular
base form kills `kernel` and adding `lift` makes it positive definite, then

`(lift . kernel) * (target . (base + lift lift^T)^-1 lift) = target . kernel`.

The lift necessarily sees the kernel, so inverse-form orthogonality to the lift
is equivalent to ordinary orthogonality to the original kernel.  At the K4
pivot endpoint the newly inserted edge is therefore orthogonal to the original
tight direction.  Adding it directly to the weak tree preserves that exact
kernel: the resulting four-label gap is positive semidefinite but singular.
-/

namespace Gtz

open Matrix

/-! ## A division-free inverse/kernel identity -/

/-- **THE LIFT/KERNEL IDENTITY.**  A rank-one lift of a singular form identifies
the inverse pairing with the original kernel pairing.  The statement is
division-free, so it retains the exact orthogonality locus. -/
theorem inverseForm_lift_pairing_mul_kernel_pairing {rank : ℕ}
    {baseMat : Matrix (Fin rank) (Fin rank) ℝ}
    (lift target kernel : Fin rank → ℝ)
    (hkernel : baseMat *ᵥ kernel = 0)
    (hposDef : (baseMat + atomMatrix lift).PosDef) :
    (lift ⬝ᵥ kernel)
        * (target ⬝ᵥ ((baseMat + atomMatrix lift)⁻¹ *ᵥ lift))
      = target ⬝ᵥ kernel := by
  have hunit : IsUnit (baseMat + atomMatrix lift).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  have hbigKernel : (baseMat + atomMatrix lift) *ᵥ kernel
      = (lift ⬝ᵥ kernel) • lift := by
    rw [Matrix.add_mulVec, hkernel, zero_add, atomMatrix,
      vecMulVec_mulVec_eq]
  have hsolve : (lift ⬝ᵥ kernel) •
      ((baseMat + atomMatrix lift)⁻¹ *ᵥ lift) = kernel := by
    have hcancel : (baseMat + atomMatrix lift)⁻¹ *ᵥ
        ((baseMat + atomMatrix lift) *ᵥ kernel) = kernel := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit,
        Matrix.one_mulVec]
    rw [hbigKernel, Matrix.mulVec_smul] at hcancel
    exact hcancel
  have hpaired := congrArg (fun vector : Fin rank → ℝ => target ⬝ᵥ vector) hsolve
  simpa [dotProduct_smul, smul_eq_mul] using hpaired

/-- Inverse-form orthogonality to the lifting vector is exactly ordinary
orthogonality to the old kernel. -/
theorem inverseForm_lift_cross_eq_zero_iff_kernel_orthogonal {rank : ℕ}
    {baseMat : Matrix (Fin rank) (Fin rank) ℝ}
    (lift target kernel : Fin rank → ℝ) (hkernelNe : kernel ≠ 0)
    (hkernel : baseMat *ᵥ kernel = 0)
    (hposDef : (baseMat + atomMatrix lift).PosDef) :
    lift ⬝ᵥ ((baseMat + atomMatrix lift)⁻¹ *ᵥ target) = 0
      ↔ target ⬝ᵥ kernel = 0 := by
  have hbigKernel : (baseMat + atomMatrix lift) *ᵥ kernel
      = (lift ⬝ᵥ kernel) • lift := by
    rw [Matrix.add_mulVec, hkernel, zero_add, atomMatrix,
      vecMulVec_mulVec_eq]
  have hliftKernel : lift ⬝ᵥ kernel ≠ 0 := by
    intro hzero
    have hzeroKernel : (baseMat + atomMatrix lift) *ᵥ kernel = 0 := by
      rw [hbigKernel, hzero, zero_smul]
    have hpositive := hposDef.dotProduct_mulVec_pos hkernelNe
    rw [hzeroKernel, dotProduct_zero] at hpositive
    exact (lt_irrefl 0) hpositive
  have hinvSymm : ((baseMat + atomMatrix lift)⁻¹)ᵀ
      = (baseMat + atomMatrix lift)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, PosDef.transpose_eq hposDef]
  have hcomm := dotProduct_mulVec_comm_of_transpose_eq hinvSymm lift target
  have hidentity := inverseForm_lift_pairing_mul_kernel_pairing lift target
    kernel hkernel hposDef
  constructor
  · intro hcross
    have htargetCross : target ⬝ᵥ
        ((baseMat + atomMatrix lift)⁻¹ *ᵥ lift) = 0 := by
      rw [← hcomm]
      exact hcross
    rw [htargetCross, mul_zero] at hidentity
    exact hidentity.symm
  · intro htargetKernel
    have hproduct : (lift ⬝ᵥ kernel)
        * (target ⬝ᵥ ((baseMat + atomMatrix lift)⁻¹ *ᵥ lift)) = 0 := by
      rw [hidentity, htargetKernel]
    have htargetCross := (mul_eq_zero.mp hproduct).resolve_left hliftKernel
    rw [hcomm]
    exact htargetCross

/-! ## The chart specialization -/

/-- A positive-definite pointer lift necessarily sees every nonzero kernel of
the base gap. -/
theorem direction_dot_kernel_ne_zero_of_insert_posDef {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (base : Finset (Fin size)) {pointer : Fin size} (hpointer : pointer ∉ base)
    {kernel : Fin 3 → ℝ} (hkernelNe : kernel ≠ 0)
    (hkernel : directionChartGap direction mass weight base *ᵥ kernel = 0)
    (hposDef : (directionChartGap direction mass weight
      (insert pointer base)).PosDef) :
    direction pointer ⬝ᵥ kernel ≠ 0 := by
  intro horth
  have hgapInsert := directionChartGap_insert direction mass weight base hpointer
  have hatomKernel : atomMatrix (direction pointer) *ᵥ kernel = 0 := by
    rw [atomMatrix, vecMulVec_mulVec_eq, horth, zero_smul]
  have hwindowKernel : directionChartGap direction mass weight
      (insert pointer base) *ᵥ kernel = 0 := by
    rw [hgapInsert, Matrix.add_mulVec, Matrix.smul_mulVec, hkernel,
      hatomKernel, smul_zero, add_zero]
  have hpositive := hposDef.dotProduct_mulVec_pos hkernelNe
  rw [hwindowKernel, dotProduct_zero] at hpositive
  exact (lt_irrefl 0) hpositive

/-- **THE CHART CROSS/KERNEL DICTIONARY.**  At a positive-definite pointer
lift, vanishing of the inverse cross with `added` is exactly orthogonality of
the added chart direction to the old kernel. -/
theorem chartLadderCross_eq_zero_iff_direction_dot_kernel_eq_zero {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) {pointer : Fin size} (hpointer : pointer ∉ base)
    (added : Fin size) {kernel : Fin 3 → ℝ} (hkernelNe : kernel ≠ 0)
    (hkernel : directionChartGap direction mass weight base *ᵥ kernel = 0)
    (hposDef : (directionChartGap direction mass weight
      (insert pointer base)).PosDef) :
    chartLadderCross direction mass weight (insert pointer base) pointer added = 0
      ↔ direction added ⬝ᵥ kernel = 0 := by
  have hgap : directionChartGap direction mass weight (insert pointer base)
      = directionChartGap direction mass weight base
        + atomMatrix (chartLadderVector direction mass weight pointer) := by
    rw [atomMatrix_chartLadderVector direction mass weight hmass
      hweight pointer, ← directionChartGap_insert direction mass weight base
        hpointer]
  have hraw := inverseForm_lift_cross_eq_zero_iff_kernel_orthogonal
    (chartLadderVector direction mass weight pointer)
    (chartLadderVector direction mass weight added) kernel hkernelNe hkernel
      (hgap ▸ hposDef)
  rw [← hgap] at hraw
  have hscaled : chartLadderVector direction mass weight added ⬝ᵥ kernel = 0
      ↔ direction added ⬝ᵥ kernel = 0 := by
    have hscalePos : 0 < Real.sqrt (mass added / weight added) :=
      Real.sqrt_pos.2 (div_pos (hmass added) (hweight added))
    rw [chartLadderVector, smul_dotProduct, smul_eq_mul,
      mul_eq_zero]
    simp [ne_of_gt hscalePos]
  unfold chartLadderCross
  rw [hraw, hscaled]

/-! ## The priced endpoint -/

/-- The five-label endpoint can delete its newly inserted label back to the
positive-definite pointer window. -/
theorem KFourPivotWallPricedEndpointData.window_posDef
    {point : DirectionChartPoint 6} {tree : Finset (Fin 6)}
    (data : KFourPivotWallPricedEndpointData point tree) :
    (directionChartGap kFourDirection point.mass point.weight
      (insert data.pointer tree)).PosDef := by
  have hmem : data.added ∈ insert data.added (insert data.pointer tree) :=
    Finset.mem_insert_self _ _
  have herase := (posDef_directionChartGap_erase_iff kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos
      (insert data.added (insert data.pointer tree)) hmem data.five_posDef).mpr
        data.added_pivot_lt_one
  rw [Finset.erase_insert data.added_notMem] at herase
  exact herase

/-- At the priced endpoint the old pointer remains exactly on its boundary
pivot after the insertion. -/
theorem KFourPivotWallPricedEndpointData.pointer_pivot_eq_one_after
    {point : DirectionChartPoint 6} {tree : Finset (Fin 6)}
    (data : KFourPivotWallPricedEndpointData point tree) :
    chartLadderPivot kFourDirection point.mass point.weight
      (insert data.added (insert data.pointer tree)) data.pointer = 1 := by
  have hge := data.old_pivots_ge_one data.pointer
    (Finset.mem_insert_self data.pointer tree)
  have hle := chartLadderPivot_insert_le kFourDirection point.mass point.weight
    point.mass_pos point.weight_pos (insert data.pointer tree)
      data.added_notMem data.window_posDef data.pointer
  rw [data.pointer_pivot_eq_one] at hle
  exact le_antisymm hle hge

/-- The priced endpoint lies on the exact zero-cross locus. -/
theorem KFourPivotWallPricedEndpointData.pointer_cross_eq_zero
    {point : DirectionChartPoint 6} {tree : Finset (Fin 6)}
    (data : KFourPivotWallPricedEndpointData point tree) :
    chartLadderCross kFourDirection point.mass point.weight
      (insert data.pointer tree) data.pointer data.added = 0 := by
  apply (chartLadderPivot_insert_eq_iff_cross_eq_zero kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos (insert data.pointer tree)
      data.added_notMem data.window_posDef data.pointer).mp
  rw [data.pointer_pivot_eq_one_after, data.pointer_pivot_eq_one]

/-- The geometric normal form of the priced endpoint.  The inserted edge is
orthogonal to the original tight direction and therefore preserves it as a
kernel vector when added directly to the weak tree. -/
structure KFourPivotWallPricedOrthogonalEndpointData
    (point : DirectionChartPoint 6) (tree : Finset (Fin 6)) where
  endpoint : KFourPivotWallPricedEndpointData point tree
  tightDirection : Fin 3 → ℝ
  tightDirection_ne : tightDirection ≠ 0
  tree_kernel : directionChartGap kFourDirection point.mass point.weight tree
    *ᵥ tightDirection = 0
  pointer_reads : kFourDirection endpoint.pointer ⬝ᵥ tightDirection ≠ 0
  added_orthogonal : kFourDirection endpoint.added ⬝ᵥ tightDirection = 0
  added_gap_kernel : directionChartGap kFourDirection point.mass point.weight
    (insert endpoint.added tree) *ᵥ tightDirection = 0
  added_gap_posSemidef : (directionChartGap kFourDirection point.mass
    point.weight (insert endpoint.added tree)).PosSemidef
  added_gap_not_posDef :
    ¬ (directionChartGap kFourDirection point.mass point.weight
      (insert endpoint.added tree)).PosDef

/-- **THE PRICED ENDPOINT COLLAPSE.**  Every priced endpoint produced at a
genuine pivot wall has the orthogonal normal form above. -/
theorem kFourPivotWall_pricedOrthogonalEndpointData
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hwindow : KFourTreeWindowData point tree)
    (data : KFourPivotWallPricedEndpointData point tree) :
    Nonempty (KFourPivotWallPricedOrthogonalEndpointData point tree) := by
  obtain ⟨tightDirection, _incoming, htightNe, _hincomingOut, htreeKernel,
    _hincomingReads, _hwindowPsd, _hwindowRead, _hwindowCase⟩ := hwindow
  have hpointerOut : data.pointer ∉ tree := data.pointer_notMem
  have hpointerReads := direction_dot_kernel_ne_zero_of_insert_posDef
    kFourDirection point.mass point.weight tree hpointerOut htightNe htreeKernel
      data.window_posDef
  have haddedOrth :=
    (chartLadderCross_eq_zero_iff_direction_dot_kernel_eq_zero kFourDirection
      point.mass point.weight point.mass_pos point.weight_pos tree hpointerOut
      data.added htightNe htreeKernel data.window_posDef).mp
        data.pointer_cross_eq_zero
  have haddedOut : data.added ∉ tree := fun hmem =>
    data.added_notMem (Finset.mem_insert_of_mem hmem)
  have haddedKernel : directionChartGap kFourDirection point.mass point.weight
      (insert data.added tree) *ᵥ tightDirection = 0 := by
    rw [directionChartGap_insert kFourDirection point.mass point.weight tree
      haddedOut, Matrix.add_mulVec, Matrix.smul_mulVec, htreeKernel,
      atomMatrix, vecMulVec_mulVec_eq, haddedOrth, zero_smul, smul_zero,
      add_zero]
  have haddedPsd : (directionChartGap kFourDirection point.mass point.weight
      (insert data.added tree)).PosSemidef := by
    rw [directionChartGap_insert kFourDirection point.mass point.weight tree
      haddedOut]
    exact hgap.add ((posSemidef_atomMatrix (kFourDirection data.added)).smul
      (div_pos (point.mass_pos data.added)
        (point.weight_pos data.added)).le)
  have haddedNotPd : ¬ (directionChartGap kFourDirection point.mass point.weight
      (insert data.added tree)).PosDef := by
    intro hpd
    have hpositive := hpd.dotProduct_mulVec_pos htightNe
    rw [haddedKernel, dotProduct_zero] at hpositive
    exact (lt_irrefl 0) hpositive
  exact ⟨⟨data, tightDirection, htightNe, htreeKernel, hpointerReads,
    haddedOrth, haddedKernel, haddedPsd, haddedNotPd⟩⟩

end Gtz
