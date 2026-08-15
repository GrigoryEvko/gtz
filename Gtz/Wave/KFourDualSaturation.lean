import Gtz.Wave.KFourFamilySelectionWiring

/-!
# Saturating a K4 Z-matrix dual witness

The Gershgorin projection of a Z-matrix dual witness loses too much: all
sixteen selected bad rows can hold at a chart point that already has strict
trees.  The full three-coordinate witness has a stronger complementarity law.
If its symmetric Z-matrix is positive semidefinite, the witness is a genuine
kernel vector.

For a K4 path tree the unsigned cycle form is not merely a lower bound on one
specific sign chamber.  Alternating signs along the path simultaneously
saturate all three fundamental-cycle triangle inequalities.  The module proves
this directly for all seven paths added by the row atlas.  Weak domination of
any such path makes its canonical Z-matrix positive semidefinite; coupled with
atlas blindness, its nonnegative dual witness is therefore an explicit nonzero
kernel vector of both the Z-matrix and the actual chart gap.

The final ledger is consumed by an exact A3 formula equivalent to the previous
all-tree Z-obstructed residual and to the design-side K4 family selector.
-/

namespace Gtz

open Matrix Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-- The symmetric scalar Z-matrix used by every three-coordinate dual
witness. -/
def zThreeMatrix (a b c d e f : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, b, c; b, d, e; c, e, f]

theorem zThreeMatrix_transpose (a b c d e f : ℝ) :
    (zThreeMatrix a b c d e f)ᵀ = zThreeMatrix a b c d e f := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- A full nonnegative dual witness for a PSD Z-matrix is a nonzero kernel
vector.  This is the complementarity information discarded by selecting only
one Gershgorin row. -/
theorem exists_nonnegative_kernel_of_zThreeDualWitness_of_posSemidef
    {a b c d e f : ℝ}
    (hdual : ZThreeDualWitness a b c d e f)
    (hpsd : (zThreeMatrix a b c d e f).PosSemidef) :
    ∃ yOne yTwo yThree : ℝ,
      0 ≤ yOne ∧ 0 ≤ yTwo ∧ 0 ≤ yThree ∧
      ¬ (yOne = 0 ∧ yTwo = 0 ∧ yThree = 0) ∧
      zThreeMatrix a b c d e f *ᵥ ![yOne, yTwo, yThree] = 0 := by
  obtain ⟨yOne, yTwo, yThree, hyOne, hyTwo, hyThree, hne,
    hrowOne, hrowTwo, hrowThree⟩ := hdual
  let y : Fin 3 → ℝ := ![yOne, yTwo, yThree]
  have hnonpos : y ⬝ᵥ (zThreeMatrix a b c d e f *ᵥ y) ≤ 0 := by
    have hOne := mul_nonpos_of_nonneg_of_nonpos hyOne hrowOne
    have hTwo := mul_nonpos_of_nonneg_of_nonpos hyTwo hrowTwo
    have hThree := mul_nonpos_of_nonneg_of_nonpos hyThree hrowThree
    simp [y, zThreeMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    linarith
  have hnonneg := hpsd.dotProduct_mulVec_nonneg y
  rw [star_trivial] at hnonneg
  have hzero : y ⬝ᵥ (zThreeMatrix a b c d e f *ᵥ y) = 0 := by linarith
  have hkernel := (hpsd.dotProduct_mulVec_zero_iff y).mp hzero
  exact ⟨yOne, yTwo, yThree, hyOne, hyTwo, hyThree, hne, hkernel⟩

/-- A quadratic pullback of a PSD gap makes the corresponding symmetric
Z-matrix PSD.  This isolates the common matrix argument from the finite K4
path arithmetic. -/
theorem zThreeMatrix_posSemidef_of_gap_pullback
    {gap : Matrix (Fin 3) (Fin 3) ℝ} (hgap : gap.PosSemidef)
    (probe : (Fin 3 → ℝ) → (Fin 3 → ℝ)) {a b c d e f : ℝ}
    (hpullback : ∀ y, probe y ⬝ᵥ (gap *ᵥ probe y)
      = y ⬝ᵥ (zThreeMatrix a b c d e f *ᵥ y)) :
    (zThreeMatrix a b c d e f).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (isHermitian_of_transpose_eq (zThreeMatrix_transpose _ _ _ _ _ _)) ?_
  intro y
  rw [star_trivial, ← hpullback]
  simpa only [star_trivial] using hgap.dotProduct_mulVec_nonneg (probe y)

/-- Generic path complementarity.  A full nonnegative dual witness, an exact
quadratic pullback, and injectivity of the pullback produce a nonzero kernel
direction of the original PSD gap. -/
theorem exists_nonnegative_tightDirection_of_zThreeDualWitness_of_gap_pullback
    {gap : Matrix (Fin 3) (Fin 3) ℝ} {a b c d e f : ℝ}
    (hdual : ZThreeDualWitness a b c d e f) (hgap : gap.PosSemidef)
    (probe : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hprobe : ∀ {y}, y ≠ 0 → probe y ≠ 0)
    (hpullback : ∀ y, probe y ⬝ᵥ (gap *ᵥ probe y)
      = y ⬝ᵥ (zThreeMatrix a b c d e f *ᵥ y)) :
    ∃ yOne yTwo yThree : ℝ,
      0 ≤ yOne ∧ 0 ≤ yTwo ∧ 0 ≤ yThree ∧
      ¬ (yOne = 0 ∧ yTwo = 0 ∧ yThree = 0) ∧
      let y : Fin 3 → ℝ := ![yOne, yTwo, yThree]
      zThreeMatrix a b c d e f *ᵥ y = 0 ∧
      probe y ≠ 0 ∧ gap *ᵥ probe y = 0 := by
  have hzPsd := zThreeMatrix_posSemidef_of_gap_pullback hgap probe hpullback
  obtain ⟨yOne, yTwo, yThree, hyOne, hyTwo, hyThree, hne, hkernel⟩ :=
    exists_nonnegative_kernel_of_zThreeDualWitness_of_posSemidef hdual hzPsd
  let y : Fin 3 → ℝ := ![yOne, yTwo, yThree]
  have hy : y ≠ 0 := by
    intro hyZero
    apply hne
    have hzero := congrFun hyZero
    exact ⟨by simpa [y] using hzero 0, by simpa [y] using hzero 1,
      by simpa [y] using hzero 2⟩
  have hkernelY : zThreeMatrix a b c d e f *ᵥ y = 0 := by
    simpa [y] using hkernel
  have hprobeNe : probe y ≠ 0 := hprobe hy
  have hquad : probe y ⬝ᵥ (gap *ᵥ probe y) = 0 := by
    rw [hpullback, hkernelY, dotProduct_zero]
  have hgapKernel := (hgap.dotProduct_mulVec_zero_iff (probe y)).mp hquad
  exact ⟨yOne, yTwo, yThree, hyOne, hyTwo, hyThree, hne, hkernelY, hprobeNe,
    hgapKernel⟩

/-- The reusable output package for a saturated K4 path: a nonnegative
nonzero Z-kernel whose signed pullback is a nonzero tight direction of the
actual chart gap. -/
def KFourPathDualTightData (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (zMatrix : Matrix (Fin 3) (Fin 3) ℝ)
    (probe : (Fin 3 → ℝ) → (Fin 3 → ℝ)) : Prop :=
  ∃ yOne yTwo yThree : ℝ,
    0 ≤ yOne ∧ 0 ≤ yTwo ∧ 0 ≤ yThree ∧
    ¬ (yOne = 0 ∧ yTwo = 0 ∧ yThree = 0) ∧
    let y : Fin 3 → ℝ := ![yOne, yTwo, yThree]
    zMatrix *ᵥ y = 0 ∧ probe y ≠ 0 ∧
    directionChartGap kFourDirection point.mass point.weight selected *ᵥ probe y = 0

/-! ## The canonical path `{0,1,5}` -/

/-- The exact Z-matrix attached to the unsigned path cell at `{0,1,5}`. -/
noncomputable def kFourPath015ZMatrix (point : DirectionChartPoint 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  zThreeMatrix
    (directionChartExactFloor point 0 - (point.mass 2 + point.mass 4))
    (-(point.mass 2 + point.mass 4)) (-(point.mass 4))
    (directionChartExactFloor point 1 - (point.mass 2 + point.mass 3 + point.mass 4))
    (-(point.mass 3 + point.mass 4))
    (directionChartExactFloor point 5 - (point.mass 3 + point.mass 4))

/-- The alternating-sign pullback from Z-coordinates to the ambient chart
coordinates for the path `{0,1,5}`. -/
def kFourPath015Probe (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![y 1 + y 2, y 0 + y 1 + y 2, y 2]

theorem dotProduct_kFourPath015Gap_probe_eq_zMatrix
    (point : DirectionChartPoint 6) (y : Fin 3 → ℝ) :
    kFourPath015Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({0, 1, 5} : Finset (Fin 6)) *ᵥ kFourPath015Probe y)
      = y ⬝ᵥ (kFourPath015ZMatrix point *ᵥ y) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  simp [kFourPath015Probe, kFourPath015ZMatrix, zThreeMatrix,
    kFourDirection, directionChartExactFloor, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Fin.sum_univ_six]
  field_simp [ne_of_gt (point.weight_pos 0), ne_of_gt (point.weight_pos 1),
    ne_of_gt (point.weight_pos 5)]
  ring

theorem kFourPath015Probe_ne_zero_of_ne_zero {y : Fin 3 → ℝ} (hy : y ≠ 0) :
    kFourPath015Probe y ≠ 0 := by
  intro hzero
  apply hy
  funext index
  fin_cases index
  · have hread := congrArg (fun probe => kFourDirection 0 ⬝ᵥ probe) hzero
    simpa [kFourPath015Probe, kFourDirection, dotProduct, Fin.sum_univ_three] using hread
  · have hread := congrArg (fun probe => kFourDirection 1 ⬝ᵥ probe) hzero
    simpa [kFourPath015Probe, kFourDirection, dotProduct, Fin.sum_univ_three] using hread
  · have hread := congrArg (fun probe => kFourDirection 5 ⬝ᵥ probe) hzero
    simpa [kFourPath015Probe, kFourDirection, dotProduct, Fin.sum_univ_three] using hread

/-- Alternating signs along the path `{0,1,5}` saturate all three unsigned
fundamental-cycle bounds.  Therefore weak domination of this path makes the
canonical Z-matrix positive semidefinite. -/
theorem kFourPath015ZMatrix_posSemidef_of_gap
    (point : DirectionChartPoint 6)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      ({0, 1, 5} : Finset (Fin 6))).PosSemidef) :
    (kFourPath015ZMatrix point).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (isHermitian_of_transpose_eq ?_) ?_
  · exact zThreeMatrix_transpose _ _ _ _ _ _
  · intro y
    rw [star_trivial]
    rw [← dotProduct_kFourPath015Gap_probe_eq_zMatrix]
    simpa only [star_trivial] using
      hgap.dotProduct_mulVec_nonneg (kFourPath015Probe y)

/-- On an atlas-blind weak `{0,1,5}` path, the canonical dual witness becomes
an explicit nonzero nonnegative kernel vector. -/
theorem exists_path015_nonnegative_kernel_of_blind_of_weak
    (point : DirectionChartPoint 6)
    (hblind : ¬ KFourPathCell015Fires point)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      ({0, 1, 5} : Finset (Fin 6))).PosSemidef) :
    ∃ yOne yTwo yThree : ℝ,
      0 ≤ yOne ∧ 0 ≤ yTwo ∧ 0 ≤ yThree ∧
      ¬ (yOne = 0 ∧ yTwo = 0 ∧ yThree = 0) ∧
      kFourPath015ZMatrix point *ᵥ ![yOne, yTwo, yThree] = 0 := by
  exact exists_nonnegative_kernel_of_zThreeDualWitness_of_posSemidef
    (kFourPath015DualWitness_of_not_fires point hblind)
    (kFourPath015ZMatrix_posSemidef_of_gap point hweak)

/-- The full coupling behind the canonical path cell.  On an atlas-blind weak
path, the nonnegative Z-kernel pulls back to a nonzero kernel direction of the
actual chart gap; no Gershgorin-row projection remains. -/
theorem exists_path015_nonnegative_tightDirection_of_blind_of_weak
    (point : DirectionChartPoint 6)
    (hblind : ¬ KFourPathCell015Fires point)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      ({0, 1, 5} : Finset (Fin 6))).PosSemidef) :
    ∃ yOne yTwo yThree : ℝ,
      0 ≤ yOne ∧ 0 ≤ yTwo ∧ 0 ≤ yThree ∧
      ¬ (yOne = 0 ∧ yTwo = 0 ∧ yThree = 0) ∧
      let y : Fin 3 → ℝ := ![yOne, yTwo, yThree]
      kFourPath015ZMatrix point *ᵥ y = 0 ∧
      kFourPath015Probe y ≠ 0 ∧
      directionChartGap kFourDirection point.mass point.weight
        ({0, 1, 5} : Finset (Fin 6)) *ᵥ kFourPath015Probe y = 0 := by
  simpa only [kFourPath015ZMatrix] using
    exists_nonnegative_tightDirection_of_zThreeDualWitness_of_gap_pullback
      (kFourPath015DualWitness_of_not_fires point hblind) hweak kFourPath015Probe
      kFourPath015Probe_ne_zero_of_ne_zero
      (dotProduct_kFourPath015Gap_probe_eq_zMatrix point)

theorem kFourPath015DualTightData_of_blind_of_weak
    (point : DirectionChartPoint 6) (hblind : ¬ KFourPathCell015Fires point)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      ({0, 1, 5} : Finset (Fin 6))).PosSemidef) :
    KFourPathDualTightData point ({0, 1, 5} : Finset (Fin 6))
      (kFourPath015ZMatrix point) kFourPath015Probe := by
  simpa only [KFourPathDualTightData] using
    exists_path015_nonnegative_tightDirection_of_blind_of_weak point hblind hweak

/-! ## The path `{0,2,5}` -/

noncomputable def kFourPath025ZMatrix (point : DirectionChartPoint 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  zThreeMatrix
    (directionChartExactFloor point 0 - (point.mass 1 + point.mass 3))
    (-(point.mass 1 + point.mass 3)) (-(point.mass 3))
    (directionChartExactFloor point 2 - (point.mass 1 + point.mass 3 + point.mass 4))
    (-(point.mass 3 + point.mass 4))
    (directionChartExactFloor point 5 - (point.mass 3 + point.mass 4))

def kFourPath025Probe (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![y 0 + y 1 + y 2, y 1 + y 2, y 2]

theorem dotProduct_kFourPath025Gap_probe_eq_zMatrix
    (point : DirectionChartPoint 6) (y : Fin 3 → ℝ) :
    kFourPath025Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({0, 2, 5} : Finset (Fin 6)) *ᵥ kFourPath025Probe y)
      = y ⬝ᵥ (kFourPath025ZMatrix point *ᵥ y) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  simp [kFourPath025Probe, kFourPath025ZMatrix, zThreeMatrix,
    kFourDirection, directionChartExactFloor, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Fin.sum_univ_six]
  field_simp [ne_of_gt (point.weight_pos 0), ne_of_gt (point.weight_pos 2),
    ne_of_gt (point.weight_pos 5)]
  ring

theorem kFourPath025Probe_ne_zero_of_ne_zero {y : Fin 3 → ℝ} (hy : y ≠ 0) :
    kFourPath025Probe y ≠ 0 := by
  intro hzero
  apply hy
  have hzero0 := congrFun hzero 0
  have hzero1 := congrFun hzero 1
  have hzero2 := congrFun hzero 2
  simp [kFourPath025Probe] at hzero0 hzero1 hzero2
  funext index
  fin_cases index <;> simp <;> linarith

theorem kFourPath025DualTightData_of_blind_of_weak
    (point : DirectionChartPoint 6) (hblind : ¬ KFourPathCell025Fires point)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      ({0, 2, 5} : Finset (Fin 6))).PosSemidef) :
    KFourPathDualTightData point ({0, 2, 5} : Finset (Fin 6))
      (kFourPath025ZMatrix point) kFourPath025Probe := by
  simpa only [KFourPathDualTightData, kFourPath025ZMatrix] using
    exists_nonnegative_tightDirection_of_zThreeDualWitness_of_gap_pullback
      (kFourPath025DualWitness_of_not_fires point hblind) hweak kFourPath025Probe
      kFourPath025Probe_ne_zero_of_ne_zero
      (dotProduct_kFourPath025Gap_probe_eq_zMatrix point)

/-! ## The path `{0,3,5}` -/

noncomputable def kFourPath035ZMatrix (point : DirectionChartPoint 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  zThreeMatrix
    (directionChartExactFloor point 0 - (point.mass 2 + point.mass 4))
    (-(point.mass 2 + point.mass 4)) (-(point.mass 2))
    (directionChartExactFloor point 3 - (point.mass 1 + point.mass 2 + point.mass 4))
    (-(point.mass 1 + point.mass 2))
    (directionChartExactFloor point 5 - (point.mass 1 + point.mass 2))

def kFourPath035Probe (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![y 1, y 0 + y 1, -y 2]

theorem dotProduct_kFourPath035Gap_probe_eq_zMatrix
    (point : DirectionChartPoint 6) (y : Fin 3 → ℝ) :
    kFourPath035Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({0, 3, 5} : Finset (Fin 6)) *ᵥ kFourPath035Probe y)
      = y ⬝ᵥ (kFourPath035ZMatrix point *ᵥ y) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  simp [kFourPath035Probe, kFourPath035ZMatrix, zThreeMatrix,
    kFourDirection, directionChartExactFloor, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Fin.sum_univ_six]
  field_simp [ne_of_gt (point.weight_pos 0), ne_of_gt (point.weight_pos 3),
    ne_of_gt (point.weight_pos 5)]
  ring

theorem kFourPath035Probe_ne_zero_of_ne_zero {y : Fin 3 → ℝ} (hy : y ≠ 0) :
    kFourPath035Probe y ≠ 0 := by
  intro hzero
  apply hy
  have hzero0 := congrFun hzero 0
  have hzero1 := congrFun hzero 1
  have hzero2 := congrFun hzero 2
  simp [kFourPath035Probe] at hzero0 hzero1 hzero2
  funext index
  fin_cases index <;> simp <;> linarith

theorem kFourPath035DualTightData_of_blind_of_weak
    (point : DirectionChartPoint 6) (hblind : ¬ KFourPathCell035Fires point)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      ({0, 3, 5} : Finset (Fin 6))).PosSemidef) :
    KFourPathDualTightData point ({0, 3, 5} : Finset (Fin 6))
      (kFourPath035ZMatrix point) kFourPath035Probe := by
  simpa only [KFourPathDualTightData, kFourPath035ZMatrix] using
    exists_nonnegative_tightDirection_of_zThreeDualWitness_of_gap_pullback
      (kFourPath035DualWitness_of_not_fires point hblind) hweak kFourPath035Probe
      kFourPath035Probe_ne_zero_of_ne_zero
      (dotProduct_kFourPath035Gap_probe_eq_zMatrix point)

/-! ## The path `{0,4,5}` -/

noncomputable def kFourPath045ZMatrix (point : DirectionChartPoint 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  zThreeMatrix
    (directionChartExactFloor point 0 - (point.mass 1 + point.mass 3))
    (-(point.mass 1 + point.mass 3)) (-(point.mass 1))
    (directionChartExactFloor point 4 - (point.mass 1 + point.mass 2 + point.mass 3))
    (-(point.mass 1 + point.mass 2))
    (directionChartExactFloor point 5 - (point.mass 1 + point.mass 2))

def kFourPath045Probe (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![y 0 + y 1, y 1, -y 2]

theorem dotProduct_kFourPath045Gap_probe_eq_zMatrix
    (point : DirectionChartPoint 6) (y : Fin 3 → ℝ) :
    kFourPath045Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({0, 4, 5} : Finset (Fin 6)) *ᵥ kFourPath045Probe y)
      = y ⬝ᵥ (kFourPath045ZMatrix point *ᵥ y) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  simp [kFourPath045Probe, kFourPath045ZMatrix, zThreeMatrix,
    kFourDirection, directionChartExactFloor, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Fin.sum_univ_six]
  field_simp [ne_of_gt (point.weight_pos 0), ne_of_gt (point.weight_pos 4),
    ne_of_gt (point.weight_pos 5)]
  ring

theorem kFourPath045Probe_ne_zero_of_ne_zero {y : Fin 3 → ℝ} (hy : y ≠ 0) :
    kFourPath045Probe y ≠ 0 := by
  intro hzero
  apply hy
  have hzero0 := congrFun hzero 0
  have hzero1 := congrFun hzero 1
  have hzero2 := congrFun hzero 2
  simp [kFourPath045Probe] at hzero0 hzero1 hzero2
  funext index
  fin_cases index <;> simp <;> linarith

theorem kFourPath045DualTightData_of_blind_of_weak
    (point : DirectionChartPoint 6) (hblind : ¬ KFourPathCell045Fires point)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      ({0, 4, 5} : Finset (Fin 6))).PosSemidef) :
    KFourPathDualTightData point ({0, 4, 5} : Finset (Fin 6))
      (kFourPath045ZMatrix point) kFourPath045Probe := by
  simpa only [KFourPathDualTightData, kFourPath045ZMatrix] using
    exists_nonnegative_tightDirection_of_zThreeDualWitness_of_gap_pullback
      (kFourPath045DualWitness_of_not_fires point hblind) hweak kFourPath045Probe
      kFourPath045Probe_ne_zero_of_ne_zero
      (dotProduct_kFourPath045Gap_probe_eq_zMatrix point)

/-! ## The path `{0,1,4}` -/

noncomputable def kFourPath014ZMatrix (point : DirectionChartPoint 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  zThreeMatrix
    (directionChartExactFloor point 0 - (point.mass 2 + point.mass 3 + point.mass 5))
    (-(point.mass 2 + point.mass 5)) (-(point.mass 3 + point.mass 5))
    (directionChartExactFloor point 1 - (point.mass 2 + point.mass 5))
    (-(point.mass 5))
    (directionChartExactFloor point 4 - (point.mass 3 + point.mass 5))

def kFourPath014Probe (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![y 0 + y 2, y 2, y 0 + y 1 + y 2]

theorem dotProduct_kFourPath014Gap_probe_eq_zMatrix
    (point : DirectionChartPoint 6) (y : Fin 3 → ℝ) :
    kFourPath014Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({0, 1, 4} : Finset (Fin 6)) *ᵥ kFourPath014Probe y)
      = y ⬝ᵥ (kFourPath014ZMatrix point *ᵥ y) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  simp [kFourPath014Probe, kFourPath014ZMatrix, zThreeMatrix,
    kFourDirection, directionChartExactFloor, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Fin.sum_univ_six]
  field_simp [ne_of_gt (point.weight_pos 0), ne_of_gt (point.weight_pos 1),
    ne_of_gt (point.weight_pos 4)]
  ring

theorem kFourPath014Probe_ne_zero_of_ne_zero {y : Fin 3 → ℝ} (hy : y ≠ 0) :
    kFourPath014Probe y ≠ 0 := by
  intro hzero
  apply hy
  have hzero0 := congrFun hzero 0
  have hzero1 := congrFun hzero 1
  have hzero2 := congrFun hzero 2
  simp [kFourPath014Probe] at hzero0 hzero1 hzero2
  funext index
  fin_cases index <;> simp <;> linarith

theorem kFourPath014DualTightData_of_blind_of_weak
    (point : DirectionChartPoint 6) (hblind : ¬ KFourPathCell014Fires point)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      ({0, 1, 4} : Finset (Fin 6))).PosSemidef) :
    KFourPathDualTightData point ({0, 1, 4} : Finset (Fin 6))
      (kFourPath014ZMatrix point) kFourPath014Probe := by
  simpa only [KFourPathDualTightData, kFourPath014ZMatrix] using
    exists_nonnegative_tightDirection_of_zThreeDualWitness_of_gap_pullback
      (kFourPath014DualWitness_of_not_fires point hblind) hweak kFourPath014Probe
      kFourPath014Probe_ne_zero_of_ne_zero
      (dotProduct_kFourPath014Gap_probe_eq_zMatrix point)

/-! ## The path `{1,2,4}` -/

noncomputable def kFourPath124ZMatrix (point : DirectionChartPoint 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  zThreeMatrix
    (directionChartExactFloor point 1 - (point.mass 0 + point.mass 3))
    (-(point.mass 0 + point.mass 3)) (-(point.mass 3))
    (directionChartExactFloor point 2 - (point.mass 0 + point.mass 3 + point.mass 5))
    (-(point.mass 3 + point.mass 5))
    (directionChartExactFloor point 4 - (point.mass 3 + point.mass 5))

def kFourPath124Probe (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![y 0 + y 1 + y 2, y 2, y 1 + y 2]

theorem dotProduct_kFourPath124Gap_probe_eq_zMatrix
    (point : DirectionChartPoint 6) (y : Fin 3 → ℝ) :
    kFourPath124Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({1, 2, 4} : Finset (Fin 6)) *ᵥ kFourPath124Probe y)
      = y ⬝ᵥ (kFourPath124ZMatrix point *ᵥ y) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  simp [kFourPath124Probe, kFourPath124ZMatrix, zThreeMatrix,
    kFourDirection, directionChartExactFloor, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Fin.sum_univ_six]
  field_simp [ne_of_gt (point.weight_pos 1), ne_of_gt (point.weight_pos 2),
    ne_of_gt (point.weight_pos 4)]
  ring

theorem kFourPath124Probe_ne_zero_of_ne_zero {y : Fin 3 → ℝ} (hy : y ≠ 0) :
    kFourPath124Probe y ≠ 0 := by
  intro hzero
  apply hy
  have hzero0 := congrFun hzero 0
  have hzero1 := congrFun hzero 1
  have hzero2 := congrFun hzero 2
  simp [kFourPath124Probe] at hzero0 hzero1 hzero2
  funext index
  fin_cases index <;> simp <;> linarith

theorem kFourPath124DualTightData_of_blind_of_weak
    (point : DirectionChartPoint 6) (hblind : ¬ KFourPathCell124Fires point)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      ({1, 2, 4} : Finset (Fin 6))).PosSemidef) :
    KFourPathDualTightData point ({1, 2, 4} : Finset (Fin 6))
      (kFourPath124ZMatrix point) kFourPath124Probe := by
  simpa only [KFourPathDualTightData, kFourPath124ZMatrix] using
    exists_nonnegative_tightDirection_of_zThreeDualWitness_of_gap_pullback
      (kFourPath124DualWitness_of_not_fires point hblind) hweak kFourPath124Probe
      kFourPath124Probe_ne_zero_of_ne_zero
      (dotProduct_kFourPath124Gap_probe_eq_zMatrix point)

/-! ## The path `{1,4,5}` -/

noncomputable def kFourPath145ZMatrix (point : DirectionChartPoint 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  zThreeMatrix
    (directionChartExactFloor point 1 - (point.mass 0 + point.mass 3))
    (-(point.mass 0)) (-(point.mass 0 + point.mass 3))
    (directionChartExactFloor point 4 - (point.mass 0 + point.mass 2))
    (-(point.mass 0 + point.mass 2))
    (directionChartExactFloor point 5 - (point.mass 0 + point.mass 2 + point.mass 3))

def kFourPath145Probe (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![y 0 + y 2, -y 1, y 2]

theorem dotProduct_kFourPath145Gap_probe_eq_zMatrix
    (point : DirectionChartPoint 6) (y : Fin 3 → ℝ) :
    kFourPath145Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({1, 4, 5} : Finset (Fin 6)) *ᵥ kFourPath145Probe y)
      = y ⬝ᵥ (kFourPath145ZMatrix point *ᵥ y) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  simp [kFourPath145Probe, kFourPath145ZMatrix, zThreeMatrix,
    kFourDirection, directionChartExactFloor, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Fin.sum_univ_six]
  field_simp [ne_of_gt (point.weight_pos 1), ne_of_gt (point.weight_pos 4),
    ne_of_gt (point.weight_pos 5)]
  ring

theorem kFourPath145Probe_ne_zero_of_ne_zero {y : Fin 3 → ℝ} (hy : y ≠ 0) :
    kFourPath145Probe y ≠ 0 := by
  intro hzero
  apply hy
  have hzero0 := congrFun hzero 0
  have hzero1 := congrFun hzero 1
  have hzero2 := congrFun hzero 2
  simp [kFourPath145Probe] at hzero0 hzero1 hzero2
  funext index
  fin_cases index <;> simp <;> linarith

theorem kFourPath145DualTightData_of_blind_of_weak
    (point : DirectionChartPoint 6) (hblind : ¬ KFourPathCell145Fires point)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      ({1, 4, 5} : Finset (Fin 6))).PosSemidef) :
    KFourPathDualTightData point ({1, 4, 5} : Finset (Fin 6))
      (kFourPath145ZMatrix point) kFourPath145Probe := by
  simpa only [KFourPathDualTightData, kFourPath145ZMatrix] using
    exists_nonnegative_tightDirection_of_zThreeDualWitness_of_gap_pullback
      (kFourPath145DualWitness_of_not_fires point hblind) hweak kFourPath145Probe
      kFourPath145Probe_ne_zero_of_ne_zero
      (dotProduct_kFourPath145Gap_probe_eq_zMatrix point)

/-! ## The seven-path saturation ledger -/

/-- Every weak path in the seven-cell row atlas carries its full saturated
dual data.  The antecedents are kept local to each path so downstream case
splits can consume exactly the weak witness they possess. -/
def KFourMissingPathDualSaturationLedger (point : DirectionChartPoint 6) : Prop :=
  ((directionChartGap kFourDirection point.mass point.weight
      ({0, 1, 5} : Finset (Fin 6))).PosSemidef →
    KFourPathDualTightData point ({0, 1, 5} : Finset (Fin 6))
      (kFourPath015ZMatrix point) kFourPath015Probe) ∧
  ((directionChartGap kFourDirection point.mass point.weight
      ({0, 2, 5} : Finset (Fin 6))).PosSemidef →
    KFourPathDualTightData point ({0, 2, 5} : Finset (Fin 6))
      (kFourPath025ZMatrix point) kFourPath025Probe) ∧
  ((directionChartGap kFourDirection point.mass point.weight
      ({0, 3, 5} : Finset (Fin 6))).PosSemidef →
    KFourPathDualTightData point ({0, 3, 5} : Finset (Fin 6))
      (kFourPath035ZMatrix point) kFourPath035Probe) ∧
  ((directionChartGap kFourDirection point.mass point.weight
      ({0, 4, 5} : Finset (Fin 6))).PosSemidef →
    KFourPathDualTightData point ({0, 4, 5} : Finset (Fin 6))
      (kFourPath045ZMatrix point) kFourPath045Probe) ∧
  ((directionChartGap kFourDirection point.mass point.weight
      ({0, 1, 4} : Finset (Fin 6))).PosSemidef →
    KFourPathDualTightData point ({0, 1, 4} : Finset (Fin 6))
      (kFourPath014ZMatrix point) kFourPath014Probe) ∧
  ((directionChartGap kFourDirection point.mass point.weight
      ({1, 2, 4} : Finset (Fin 6))).PosSemidef →
    KFourPathDualTightData point ({1, 2, 4} : Finset (Fin 6))
      (kFourPath124ZMatrix point) kFourPath124Probe) ∧
  ((directionChartGap kFourDirection point.mass point.weight
      ({1, 4, 5} : Finset (Fin 6))).PosSemidef →
    KFourPathDualTightData point ({1, 4, 5} : Finset (Fin 6))
      (kFourPath145ZMatrix point) kFourPath145Probe)

/-- Failure of the full sixteen-tree atlas supplies all seven conditional
path saturations at once.  This is the consumer-facing replacement for the
seven separate Gershgorin rows on these paths. -/
theorem kFourMissingPathDualSaturationLedger_of_allTreeBlind
    (point : DirectionChartPoint 6)
    (hblind : ¬ KFourAllTreeMinorAtlasCellFires point) :
    KFourMissingPathDualSaturationLedger point := by
  have h015 : ¬ KFourPathCell015Fires point :=
    fun h => hblind (Or.inr (Or.inl h))
  have h025 : ¬ KFourPathCell025Fires point :=
    fun h => hblind (Or.inr (Or.inr (Or.inl h)))
  have h035 : ¬ KFourPathCell035Fires point :=
    fun h => hblind (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have h045 : ¬ KFourPathCell045Fires point :=
    fun h => hblind (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have h014 : ¬ KFourPathCell014Fires point :=
    fun h => hblind (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  have h124 : ¬ KFourPathCell124Fires point :=
    fun h => hblind
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  have h145 : ¬ KFourPathCell145Fires point :=
    fun h => hblind
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
  exact ⟨kFourPath015DualTightData_of_blind_of_weak point h015,
    kFourPath025DualTightData_of_blind_of_weak point h025,
    kFourPath035DualTightData_of_blind_of_weak point h035,
    kFourPath045DualTightData_of_blind_of_weak point h045,
    kFourPath014DualTightData_of_blind_of_weak point h014,
    kFourPath124DualTightData_of_blind_of_weak point h124,
    kFourPath145DualTightData_of_blind_of_weak point h145⟩

/-! ## Spend the saturated ledger in A3 -/

/-- The exact A3 residual after retaining both the complete sixteen-tree
obstruction ledger and the seven path-specific kernel couplings. -/
noncomputable def KFourKnifeBandRefinedMissingPathSaturatedWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourMissingPathDualSaturationLedger point →
    (∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef) →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem missingPathSaturatedKFourKnifeBandRefined_of_allTreeZObstructed
    (hall : KFourKnifeBandRefinedAllTreeZObstructedWeakToStrict) :
    KFourKnifeBandRefinedMissingPathSaturatedWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger _hsaturated hweak
  exact hall point hnotLayerA hnotExchange hnotAtlas hledger hweak

theorem allTreeZObstructedKFourKnifeBandRefined_of_missingPathSaturated
    (hsaturated : KFourKnifeBandRefinedMissingPathSaturatedWeakToStrict) :
    KFourKnifeBandRefinedAllTreeZObstructedWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger hweak
  exact hsaturated point hnotLayerA hnotExchange hnotAtlas hledger
    (kFourMissingPathDualSaturationLedger_of_allTreeBlind point hnotAtlas) hweak

theorem kFourKnifeBandRefinedMissingPathSaturated_iff_allTreeZObstructed :
    KFourKnifeBandRefinedMissingPathSaturatedWeakToStrict ↔
      KFourKnifeBandRefinedAllTreeZObstructedWeakToStrict :=
  ⟨allTreeZObstructedKFourKnifeBandRefined_of_missingPathSaturated,
    missingPathSaturatedKFourKnifeBandRefined_of_allTreeZObstructed⟩

theorem kFourKnifeBandRefinedMissingPathSaturated_iff :
    KFourKnifeBandRefinedMissingPathSaturatedWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedMissingPathSaturated_iff_allTreeZObstructed.trans
    kFourKnifeBandRefinedAllTreeZObstructed_iff

theorem kFourFamilySelection_iff_missingPathSaturated :
    KFourFamilySelection ↔ KFourKnifeBandRefinedMissingPathSaturatedWeakToStrict :=
  kFourFamilySelection_iff_allTreeZObstructed.trans
    kFourKnifeBandRefinedMissingPathSaturated_iff_allTreeZObstructed.symm

end Gtz
