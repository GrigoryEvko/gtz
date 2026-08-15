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
saturate all three fundamental-cycle triangle inequalities.  The first path
lemma below proves this directly for `{0,1,5}`: weak domination of that tree
makes its canonical Z-matrix positive semidefinite.  Coupled with atlas
blindness, its nonnegative dual witness is therefore an explicit nonzero
kernel vector.
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
  obtain ⟨yOne, yTwo, yThree, hyOne, hyTwo, hyThree, hne, hkernel⟩ :=
    exists_path015_nonnegative_kernel_of_blind_of_weak point hblind hweak
  let y : Fin 3 → ℝ := ![yOne, yTwo, yThree]
  have hy : y ≠ 0 := by
    intro hyZero
    apply hne
    have hzero := congrFun hyZero
    exact ⟨by simpa [y] using hzero 0, by simpa [y] using hzero 1,
      by simpa [y] using hzero 2⟩
  have hprobe : kFourPath015Probe y ≠ 0 :=
    kFourPath015Probe_ne_zero_of_ne_zero hy
  have hkernelY : kFourPath015ZMatrix point *ᵥ y = 0 := by
    simpa [y] using hkernel
  have hquad : kFourPath015Probe y ⬝ᵥ
      (directionChartGap kFourDirection point.mass point.weight
        ({0, 1, 5} : Finset (Fin 6)) *ᵥ kFourPath015Probe y) = 0 := by
    rw [dotProduct_kFourPath015Gap_probe_eq_zMatrix]
    rw [hkernelY, dotProduct_zero]
  have hgapKernel := (hweak.dotProduct_mulVec_zero_iff (kFourPath015Probe y)).mp hquad
  exact ⟨yOne, yTwo, yThree, hyOne, hyTwo, hyThree, hne, hkernelY, hprobe,
    hgapKernel⟩

end Gtz
