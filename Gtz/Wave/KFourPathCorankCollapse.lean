import Gtz.Wave.KFourTreeWindowCorankReduction
import Gtz.Wave.KFourPriorPathDualSaturation
import Mathlib.LinearAlgebra.CrossProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# Corank two cannot occur on a K4 path tree

Every non-star K4 spanning tree has an exact three-coordinate pullback whose
matrix is a positive-semidefinite Z-matrix with all three off-diagonal entries
strictly negative.  Such a matrix has kernel dimension at most one.  This
module proves that fact without spectral theory and spends it on the two
independent kernels carried by the singular-window A3 residual.

The conclusion removes all twelve path trees from the corank-two branch.  The
only possible corank-two witnesses are the four vertex stars, precisely the
sign-frustrated family addressed by the star amplification machinery.
-/

namespace Gtz

open Matrix

/-! ## An irreducible three-dimensional PSD Z-matrix has nullity at most one -/

/-- A PSD `3 x 3` Z-matrix with three strictly negative off-diagonal entries
cannot kill two nonzero noncollinear vectors.  The proof is elementary: one
coordinate minor of the vectors is nonzero; eliminating the two kernel
equations across that minor forces a rank-one cofactor identity, whose two
sides have opposite signs. -/
theorem false_of_zThreeMatrix_posSemidef_of_two_noncollinear_kernels
    {a b c d e f : Real}
    (hpsd : (zThreeMatrix a b c d e f).PosSemidef)
    (hb : b < 0) (hc : c < 0) (he : e < 0)
    {x y : Fin 3 -> Real} (hxNe : x ≠ 0)
    (hxKernel : zThreeMatrix a b c d e f *ᵥ x = 0)
    (hyKernel : zThreeMatrix a b c d e f *ᵥ y = 0)
    (hnotCollinear : ¬ exists scale : Real, y = scale • x) : False := by
  have ha : 0 <= a := by
    have hdiag := hpsd.dotProduct_mulVec_nonneg ![1, 0, 0]
    simpa [zThreeMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_three] using hdiag
  have hd : 0 <= d := by
    have hdiag := hpsd.dotProduct_mulVec_nonneg ![0, 1, 0]
    simpa [zThreeMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_three] using hdiag
  have hxRowZero : a * x 0 + b * x 1 + c * x 2 = 0 := by
    simpa [zThreeMatrix, Matrix.mulVec, Fin.sum_univ_three, Matrix.vecHead,
      Matrix.vecTail, add_assoc] using congrFun hxKernel 0
  have hxRowOne : b * x 0 + d * x 1 + e * x 2 = 0 := by
    simpa [zThreeMatrix, Matrix.mulVec, Fin.sum_univ_three, Matrix.vecHead,
      Matrix.vecTail, add_assoc] using congrFun hxKernel 1
  have hxRowTwo : c * x 0 + e * x 1 + f * x 2 = 0 := by
    simpa [zThreeMatrix, Matrix.mulVec, Fin.sum_univ_three, Matrix.vecHead,
      Matrix.vecTail, add_assoc] using congrFun hxKernel 2
  have hyRowZero : a * y 0 + b * y 1 + c * y 2 = 0 := by
    simpa [zThreeMatrix, Matrix.mulVec, Fin.sum_univ_three, Matrix.vecHead,
      Matrix.vecTail, add_assoc] using congrFun hyKernel 0
  have hyRowOne : b * y 0 + d * y 1 + e * y 2 = 0 := by
    simpa [zThreeMatrix, Matrix.mulVec, Fin.sum_univ_three, Matrix.vecHead,
      Matrix.vecTail, add_assoc] using congrFun hyKernel 1
  have hyRowTwo : c * y 0 + e * y 1 + f * y 2 = 0 := by
    simpa [zThreeMatrix, Matrix.mulVec, Fin.sum_univ_three, Matrix.vecHead,
      Matrix.vecTail, add_assoc] using congrFun hyKernel 2
  by_cases hZeroOne : x 0 * y 1 - x 1 * y 0 ≠ 0
  · have hproduct :
        (x 0 * y 1 - x 1 * y 0) * (a * e - b * c) = 0 := by
      linear_combination
        (e * y 1) * hxRowZero - (e * x 1) * hyRowZero
          - (c * y 1) * hxRowOne + (c * x 1) * hyRowOne
    have hcofactor : a * e = b * c := by
      have := (mul_eq_zero.mp hproduct).resolve_left hZeroOne
      linarith
    have hleft : a * e <= 0 := mul_nonpos_of_nonneg_of_nonpos ha he.le
    have hright : 0 < b * c := mul_pos_of_neg_of_neg hb hc
    nlinarith
  · have hZeroOneEq : x 0 * y 1 - x 1 * y 0 = 0 := by
      simpa using hZeroOne
    by_cases hZeroTwo : x 0 * y 2 - x 2 * y 0 ≠ 0
    · have hproduct :
          (x 0 * y 2 - x 2 * y 0) * (a * e - b * c) = 0 := by
        linear_combination
          (e * y 2) * hxRowZero - (e * x 2) * hyRowZero
            - (b * y 2) * hxRowTwo + (b * x 2) * hyRowTwo
      have hcofactor : a * e = b * c := by
        have := (mul_eq_zero.mp hproduct).resolve_left hZeroTwo
        linarith
      have hleft : a * e <= 0 := mul_nonpos_of_nonneg_of_nonpos ha he.le
      have hright : 0 < b * c := mul_pos_of_neg_of_neg hb hc
      nlinarith
    · have hZeroTwoEq : x 0 * y 2 - x 2 * y 0 = 0 := by
        simpa using hZeroTwo
      by_cases hOneTwo : x 1 * y 2 - x 2 * y 1 ≠ 0
      · have hproduct :
            (x 1 * y 2 - x 2 * y 1) * (c * d - b * e) = 0 := by
          linear_combination
            (c * y 2) * hxRowOne - (c * x 2) * hyRowOne
              - (b * y 2) * hxRowTwo + (b * x 2) * hyRowTwo
        have hcofactor : c * d = b * e := by
          have := (mul_eq_zero.mp hproduct).resolve_left hOneTwo
          linarith
        have hleft : c * d <= 0 := mul_nonpos_of_nonpos_of_nonneg hc.le hd
        have hright : 0 < b * e := mul_pos_of_neg_of_neg hb he
        nlinarith
      · have hOneTwoEq : x 1 * y 2 - x 2 * y 1 = 0 := by
          simpa using hOneTwo
        have hlinearIndependent : LinearIndependent Real ![x, y] := by
          rw [LinearIndependent.pair_iff' hxNe]
          intro scale hscale
          exact hnotCollinear ⟨scale, hscale.symm⟩
        have hcross : x ⨯₃ y ≠ 0 :=
          crossProduct_ne_zero_iff_linearIndependent.mpr hlinearIndependent
        apply hcross
        rw [cross_apply]
        ext index
        fin_cases index
        · simpa using hOneTwoEq
        · simp
          nlinarith [hZeroTwoEq]
        · simpa using hZeroOneEq

/-! ## Transport corank two through an injective quadratic pullback -/

/-- An injective linear endomorphism of `R^3` is surjective.  This small
wrapper matches the injectivity interface already proved for every K4 path
probe. -/
theorem probe_surjective_of_ne_zero
    (probe : (Fin 3 -> Real) →ₗ[Real] (Fin 3 -> Real))
    (hprobe : forall {y}, y ≠ 0 -> probe y ≠ 0) :
    Function.Surjective probe := by
  have hinjective : Function.Injective probe := by
    rw [← LinearMap.ker_eq_bot]
    refine LinearMap.ker_eq_bot'.mpr ?_
    intro y hy
    by_contra hyNe
    exact hprobe hyNe hy
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl)).mp
    hinjective

/-- A corank-two PSD gap cannot have an injective pullback to an irreducible
PSD Z-matrix. -/
theorem false_of_gapCorankTwo_of_irreducible_zThree_pullback
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      selected).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point selected)
    (probe : (Fin 3 -> Real) →ₗ[Real] (Fin 3 -> Real))
    (hprobe : forall {y}, y ≠ 0 -> probe y ≠ 0)
    {a b c d e f : Real}
    (hpullback : forall y,
      probe y ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
        selected *ᵥ probe y) =
        y ⬝ᵥ (zThreeMatrix a b c d e f *ᵥ y))
    (hb : b < 0) (hc : c < 0) (he : e < 0) : False := by
  obtain ⟨tightDirection, secondDirection, pointer, htightNe, hpointerOut,
    htightKernel, hpointerReads, hsecondNe, hsecondKernel,
    hpointerOrthogonal, hnotCollinear⟩ := hcorank
  have hsurjective := probe_surjective_of_ne_zero probe hprobe
  obtain ⟨tightPreimage, htightPreimage⟩ := hsurjective tightDirection
  obtain ⟨secondPreimage, hsecondPreimage⟩ := hsurjective secondDirection
  have hzPsd : (zThreeMatrix a b c d e f).PosSemidef :=
    zThreeMatrix_posSemidef_of_gap_pullback hgap probe hpullback
  have htightPreimageNe : tightPreimage ≠ 0 := by
    intro hzero
    apply htightNe
    rw [← htightPreimage, hzero, map_zero]
  have htightZKernel :
      zThreeMatrix a b c d e f *ᵥ tightPreimage = 0 := by
    apply (hzPsd.dotProduct_mulVec_zero_iff tightPreimage).mp
    rw [star_trivial]
    rw [← hpullback, htightPreimage, htightKernel, dotProduct_zero]
  have hsecondZKernel :
      zThreeMatrix a b c d e f *ᵥ secondPreimage = 0 := by
    apply (hzPsd.dotProduct_mulVec_zero_iff secondPreimage).mp
    rw [star_trivial]
    rw [← hpullback, hsecondPreimage, hsecondKernel, dotProduct_zero]
  have hpreimagesNotCollinear :
      ¬ exists scale : Real, secondPreimage = scale • tightPreimage := by
    rintro ⟨scale, hscale⟩
    apply hnotCollinear
    refine ⟨scale, ?_⟩
    rw [← hsecondPreimage, ← htightPreimage, hscale, map_smul]
  exact false_of_zThreeMatrix_posSemidef_of_two_noncollinear_kernels hzPsd
    hb hc he htightPreimageNe htightZKernel hsecondZKernel
    hpreimagesNotCollinear

/-! ## The twelve path probes as linear equivalences -/

def kFourPath015ProbeLinear :
    (Fin 3 -> Real) →ₗ[Real] (Fin 3 -> Real) where
  toFun := kFourPath015Probe
  map_add' left right := by
    funext index
    fin_cases index <;> simp [kFourPath015Probe] <;> ring
  map_smul' scale y := by
    funext index
    fin_cases index <;> simp [kFourPath015Probe] <;> ring

def kFourPath025ProbeLinear :
    (Fin 3 -> Real) →ₗ[Real] (Fin 3 -> Real) where
  toFun := kFourPath025Probe
  map_add' left right := by
    funext index
    fin_cases index <;> simp [kFourPath025Probe] <;> ring
  map_smul' scale y := by
    funext index
    fin_cases index <;> simp [kFourPath025Probe] <;> ring

def kFourPath035ProbeLinear :
    (Fin 3 -> Real) →ₗ[Real] (Fin 3 -> Real) where
  toFun := kFourPath035Probe
  map_add' left right := by
    funext index
    fin_cases index <;> simp [kFourPath035Probe] <;> ring
  map_smul' scale y := by
    funext index
    fin_cases index <;> (simp [kFourPath035Probe] <;> ring)

def kFourPath045ProbeLinear :
    (Fin 3 -> Real) →ₗ[Real] (Fin 3 -> Real) where
  toFun := kFourPath045Probe
  map_add' left right := by
    funext index
    fin_cases index <;> simp [kFourPath045Probe] <;> ring
  map_smul' scale y := by
    funext index
    fin_cases index <;> (simp [kFourPath045Probe] <;> ring)

def kFourPath014ProbeLinear :
    (Fin 3 -> Real) →ₗ[Real] (Fin 3 -> Real) where
  toFun := kFourPath014Probe
  map_add' left right := by
    funext index
    fin_cases index <;> simp [kFourPath014Probe] <;> ring
  map_smul' scale y := by
    funext index
    fin_cases index <;> simp [kFourPath014Probe] <;> ring

def kFourPath124ProbeLinear :
    (Fin 3 -> Real) →ₗ[Real] (Fin 3 -> Real) where
  toFun := kFourPath124Probe
  map_add' left right := by
    funext index
    fin_cases index <;> simp [kFourPath124Probe] <;> ring
  map_smul' scale y := by
    funext index
    fin_cases index <;> simp [kFourPath124Probe] <;> ring

def kFourPath145ProbeLinear :
    (Fin 3 -> Real) →ₗ[Real] (Fin 3 -> Real) where
  toFun := kFourPath145Probe
  map_add' left right := by
    funext index
    fin_cases index <;> simp [kFourPath145Probe] <;> ring
  map_smul' scale y := by
    funext index
    fin_cases index <;> (simp [kFourPath145Probe] <;> ring)

def kFourBand134ProbeLinear :
    (Fin 3 -> Real) →ₗ[Real] (Fin 3 -> Real) where
  toFun := kFourBand134Probe
  map_add' left right := by
    funext index
    fin_cases index <;> simp [kFourBand134Probe] <;> ring
  map_smul' scale y := by
    funext index
    fin_cases index <;> (simp [kFourBand134Probe] <;> ring)

def kFourPendant023ProbeLinear :
    (Fin 3 -> Real) →ₗ[Real] (Fin 3 -> Real) where
  toFun := kFourPendant023Probe
  map_add' left right := by
    funext index
    fin_cases index <;> simp [kFourPendant023Probe] <;> ring
  map_smul' scale y := by
    funext index
    fin_cases index <;> simp [kFourPendant023Probe] <;> ring

def kFourPendant123ProbeLinear :
    (Fin 3 -> Real) →ₗ[Real] (Fin 3 -> Real) where
  toFun := kFourPendant123Probe
  map_add' left right := by
    funext index
    fin_cases index <;> simp [kFourPendant123Probe] <;> ring
  map_smul' scale y := by
    funext index
    fin_cases index <;> simp [kFourPendant123Probe] <;> ring

def kFourPendant234ProbeLinear :
    (Fin 3 -> Real) →ₗ[Real] (Fin 3 -> Real) where
  toFun := kFourPendant234Probe
  map_add' left right := by
    funext index
    fin_cases index <;> simp [kFourPendant234Probe] <;> ring
  map_smul' scale y := by
    funext index
    fin_cases index <;> (simp [kFourPendant234Probe] <;> ring)

def kFourPendant235ProbeLinear :
    (Fin 3 -> Real) →ₗ[Real] (Fin 3 -> Real) where
  toFun := kFourPendant235Probe
  map_add' left right := by
    funext index
    fin_cases index <;> simp [kFourPendant235Probe] <;> ring
  map_smul' scale y := by
    funext index
    fin_cases index <;> (simp [kFourPendant235Probe] <;> ring)

/-! ## Eliminate corank two on each path -/

theorem false_of_kFourPath015_gapCorankTwo
    (point : DirectionChartPoint 6)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      ({0, 1, 5} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point ({0, 1, 5} : Finset (Fin 6))) :
    False := by
  refine false_of_gapCorankTwo_of_irreducible_zThree_pullback point
    ({0, 1, 5} : Finset (Fin 6)) hgap hcorank kFourPath015ProbeLinear
    (a := directionChartExactFloor point 0 - (point.mass 2 + point.mass 4))
    (b := -(point.mass 2 + point.mass 4)) (c := -(point.mass 4))
    (d := directionChartExactFloor point 1 -
      (point.mass 2 + point.mass 3 + point.mass 4))
    (e := -(point.mass 3 + point.mass 4))
    (f := directionChartExactFloor point 5 - (point.mass 3 + point.mass 4))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact kFourPath015Probe_ne_zero_of_ne_zero hy
  · intro y
    change kFourPath015Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({0, 1, 5} : Finset (Fin 6)) *ᵥ kFourPath015Probe y) = _
    exact dotProduct_kFourPath015Gap_probe_eq_zMatrix point y
  · have := point.mass_pos 2
    have := point.mass_pos 4
    linarith
  · have := point.mass_pos 4
    linarith
  · have := point.mass_pos 3
    have := point.mass_pos 4
    linarith

theorem false_of_kFourPath025_gapCorankTwo
    (point : DirectionChartPoint 6)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      ({0, 2, 5} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point ({0, 2, 5} : Finset (Fin 6))) :
    False := by
  refine false_of_gapCorankTwo_of_irreducible_zThree_pullback point
    ({0, 2, 5} : Finset (Fin 6)) hgap hcorank kFourPath025ProbeLinear
    (a := directionChartExactFloor point 0 - (point.mass 1 + point.mass 3))
    (b := -(point.mass 1 + point.mass 3)) (c := -(point.mass 3))
    (d := directionChartExactFloor point 2 -
      (point.mass 1 + point.mass 3 + point.mass 4))
    (e := -(point.mass 3 + point.mass 4))
    (f := directionChartExactFloor point 5 - (point.mass 3 + point.mass 4))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact kFourPath025Probe_ne_zero_of_ne_zero hy
  · intro y
    change kFourPath025Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({0, 2, 5} : Finset (Fin 6)) *ᵥ kFourPath025Probe y) = _
    exact dotProduct_kFourPath025Gap_probe_eq_zMatrix point y
  · nlinarith [point.mass_pos 1, point.mass_pos 3]
  · linarith [point.mass_pos 3]
  · nlinarith [point.mass_pos 3, point.mass_pos 4]

theorem false_of_kFourPath035_gapCorankTwo
    (point : DirectionChartPoint 6)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      ({0, 3, 5} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point ({0, 3, 5} : Finset (Fin 6))) :
    False := by
  refine false_of_gapCorankTwo_of_irreducible_zThree_pullback point
    ({0, 3, 5} : Finset (Fin 6)) hgap hcorank kFourPath035ProbeLinear
    (a := directionChartExactFloor point 0 - (point.mass 2 + point.mass 4))
    (b := -(point.mass 2 + point.mass 4)) (c := -(point.mass 2))
    (d := directionChartExactFloor point 3 -
      (point.mass 1 + point.mass 2 + point.mass 4))
    (e := -(point.mass 1 + point.mass 2))
    (f := directionChartExactFloor point 5 - (point.mass 1 + point.mass 2))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact kFourPath035Probe_ne_zero_of_ne_zero hy
  · intro y
    change kFourPath035Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({0, 3, 5} : Finset (Fin 6)) *ᵥ kFourPath035Probe y) = _
    exact dotProduct_kFourPath035Gap_probe_eq_zMatrix point y
  · nlinarith [point.mass_pos 2, point.mass_pos 4]
  · linarith [point.mass_pos 2]
  · nlinarith [point.mass_pos 1, point.mass_pos 2]

theorem false_of_kFourPath045_gapCorankTwo
    (point : DirectionChartPoint 6)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      ({0, 4, 5} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point ({0, 4, 5} : Finset (Fin 6))) :
    False := by
  refine false_of_gapCorankTwo_of_irreducible_zThree_pullback point
    ({0, 4, 5} : Finset (Fin 6)) hgap hcorank kFourPath045ProbeLinear
    (a := directionChartExactFloor point 0 - (point.mass 1 + point.mass 3))
    (b := -(point.mass 1 + point.mass 3)) (c := -(point.mass 1))
    (d := directionChartExactFloor point 4 -
      (point.mass 1 + point.mass 2 + point.mass 3))
    (e := -(point.mass 1 + point.mass 2))
    (f := directionChartExactFloor point 5 - (point.mass 1 + point.mass 2))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact kFourPath045Probe_ne_zero_of_ne_zero hy
  · intro y
    change kFourPath045Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({0, 4, 5} : Finset (Fin 6)) *ᵥ kFourPath045Probe y) = _
    exact dotProduct_kFourPath045Gap_probe_eq_zMatrix point y
  · nlinarith [point.mass_pos 1, point.mass_pos 3]
  · linarith [point.mass_pos 1]
  · nlinarith [point.mass_pos 1, point.mass_pos 2]

theorem false_of_kFourPath014_gapCorankTwo
    (point : DirectionChartPoint 6)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      ({0, 1, 4} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point ({0, 1, 4} : Finset (Fin 6))) :
    False := by
  refine false_of_gapCorankTwo_of_irreducible_zThree_pullback point
    ({0, 1, 4} : Finset (Fin 6)) hgap hcorank kFourPath014ProbeLinear
    (a := directionChartExactFloor point 0 -
      (point.mass 2 + point.mass 3 + point.mass 5))
    (b := -(point.mass 2 + point.mass 5))
    (c := -(point.mass 3 + point.mass 5))
    (d := directionChartExactFloor point 1 - (point.mass 2 + point.mass 5))
    (e := -(point.mass 5))
    (f := directionChartExactFloor point 4 - (point.mass 3 + point.mass 5))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact kFourPath014Probe_ne_zero_of_ne_zero hy
  · intro y
    change kFourPath014Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({0, 1, 4} : Finset (Fin 6)) *ᵥ kFourPath014Probe y) = _
    exact dotProduct_kFourPath014Gap_probe_eq_zMatrix point y
  · nlinarith [point.mass_pos 2, point.mass_pos 5]
  · nlinarith [point.mass_pos 3, point.mass_pos 5]
  · linarith [point.mass_pos 5]

theorem false_of_kFourPath124_gapCorankTwo
    (point : DirectionChartPoint 6)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      ({1, 2, 4} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point ({1, 2, 4} : Finset (Fin 6))) :
    False := by
  refine false_of_gapCorankTwo_of_irreducible_zThree_pullback point
    ({1, 2, 4} : Finset (Fin 6)) hgap hcorank kFourPath124ProbeLinear
    (a := directionChartExactFloor point 1 - (point.mass 0 + point.mass 3))
    (b := -(point.mass 0 + point.mass 3)) (c := -(point.mass 3))
    (d := directionChartExactFloor point 2 -
      (point.mass 0 + point.mass 3 + point.mass 5))
    (e := -(point.mass 3 + point.mass 5))
    (f := directionChartExactFloor point 4 - (point.mass 3 + point.mass 5))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact kFourPath124Probe_ne_zero_of_ne_zero hy
  · intro y
    change kFourPath124Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({1, 2, 4} : Finset (Fin 6)) *ᵥ kFourPath124Probe y) = _
    exact dotProduct_kFourPath124Gap_probe_eq_zMatrix point y
  · nlinarith [point.mass_pos 0, point.mass_pos 3]
  · linarith [point.mass_pos 3]
  · nlinarith [point.mass_pos 3, point.mass_pos 5]

theorem false_of_kFourPath145_gapCorankTwo
    (point : DirectionChartPoint 6)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      ({1, 4, 5} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point ({1, 4, 5} : Finset (Fin 6))) :
    False := by
  refine false_of_gapCorankTwo_of_irreducible_zThree_pullback point
    ({1, 4, 5} : Finset (Fin 6)) hgap hcorank kFourPath145ProbeLinear
    (a := directionChartExactFloor point 1 - (point.mass 0 + point.mass 3))
    (b := -(point.mass 0)) (c := -(point.mass 0 + point.mass 3))
    (d := directionChartExactFloor point 4 - (point.mass 0 + point.mass 2))
    (e := -(point.mass 0 + point.mass 2))
    (f := directionChartExactFloor point 5 -
      (point.mass 0 + point.mass 2 + point.mass 3))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact kFourPath145Probe_ne_zero_of_ne_zero hy
  · intro y
    change kFourPath145Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({1, 4, 5} : Finset (Fin 6)) *ᵥ kFourPath145Probe y) = _
    exact dotProduct_kFourPath145Gap_probe_eq_zMatrix point y
  · linarith [point.mass_pos 0]
  · nlinarith [point.mass_pos 0, point.mass_pos 3]
  · nlinarith [point.mass_pos 0, point.mass_pos 2]

theorem false_of_kFourBand134_gapCorankTwo
    (point : DirectionChartPoint 6)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      ({1, 3, 4} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point ({1, 3, 4} : Finset (Fin 6))) :
    False := by
  refine false_of_gapCorankTwo_of_irreducible_zThree_pullback point
    ({1, 3, 4} : Finset (Fin 6)) hgap hcorank kFourBand134ProbeLinear
    (a := directionChartExactFloor point 1 - (point.mass 2 + point.mass 5))
    (b := -(point.mass 2 + point.mass 5)) (c := -(point.mass 2))
    (d := directionChartExactFloor point 3 -
      (point.mass 0 + point.mass 2 + point.mass 5))
    (e := -(point.mass 0 + point.mass 2))
    (f := directionChartExactFloor point 4 - (point.mass 0 + point.mass 2))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact kFourBand134Probe_ne_zero_of_ne_zero hy
  · intro y
    change kFourBand134Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({1, 3, 4} : Finset (Fin 6)) *ᵥ kFourBand134Probe y) = _
    exact dotProduct_kFourBand134Gap_probe_eq_zMatrix point y
  · nlinarith [point.mass_pos 2, point.mass_pos 5]
  · linarith [point.mass_pos 2]
  · nlinarith [point.mass_pos 0, point.mass_pos 2]

theorem false_of_kFourPendant023_gapCorankTwo
    (point : DirectionChartPoint 6)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      ({0, 2, 3} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point ({0, 2, 3} : Finset (Fin 6))) :
    False := by
  refine false_of_gapCorankTwo_of_irreducible_zThree_pullback point
    ({0, 2, 3} : Finset (Fin 6)) hgap hcorank kFourPendant023ProbeLinear
    (a := directionChartExactFloor point 0 -
      (point.mass 1 + point.mass 4 + point.mass 5))
    (b := -(point.mass 1 + point.mass 5))
    (c := -(point.mass 4 + point.mass 5))
    (d := directionChartExactFloor point 2 - (point.mass 1 + point.mass 5))
    (e := -(point.mass 5))
    (f := directionChartExactFloor point 3 - (point.mass 4 + point.mass 5))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact kFourPendant023Probe_ne_zero_of_ne_zero hy
  · intro y
    change kFourPendant023Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({0, 2, 3} : Finset (Fin 6)) *ᵥ kFourPendant023Probe y) = _
    exact dotProduct_kFourPendant023Gap_probe_eq_zMatrix point y
  · nlinarith [point.mass_pos 1, point.mass_pos 5]
  · nlinarith [point.mass_pos 4, point.mass_pos 5]
  · linarith [point.mass_pos 5]

theorem false_of_kFourPendant123_gapCorankTwo
    (point : DirectionChartPoint 6)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      ({1, 2, 3} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point ({1, 2, 3} : Finset (Fin 6))) :
    False := by
  refine false_of_gapCorankTwo_of_irreducible_zThree_pullback point
    ({1, 2, 3} : Finset (Fin 6)) hgap hcorank kFourPendant123ProbeLinear
    (a := directionChartExactFloor point 1 -
      (point.mass 0 + point.mass 4 + point.mass 5))
    (b := -(point.mass 0 + point.mass 4))
    (c := -(point.mass 4 + point.mass 5))
    (d := directionChartExactFloor point 2 - (point.mass 0 + point.mass 4))
    (e := -(point.mass 4))
    (f := directionChartExactFloor point 3 - (point.mass 4 + point.mass 5))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact kFourPendant123Probe_ne_zero_of_ne_zero hy
  · intro y
    change kFourPendant123Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({1, 2, 3} : Finset (Fin 6)) *ᵥ kFourPendant123Probe y) = _
    exact dotProduct_kFourPendant123Gap_probe_eq_zMatrix point y
  · nlinarith [point.mass_pos 0, point.mass_pos 4]
  · nlinarith [point.mass_pos 4, point.mass_pos 5]
  · linarith [point.mass_pos 4]

theorem false_of_kFourPendant234_gapCorankTwo
    (point : DirectionChartPoint 6)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      ({2, 3, 4} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point ({2, 3, 4} : Finset (Fin 6))) :
    False := by
  refine false_of_gapCorankTwo_of_irreducible_zThree_pullback point
    ({2, 3, 4} : Finset (Fin 6)) hgap hcorank kFourPendant234ProbeLinear
    (a := directionChartExactFloor point 2 - (point.mass 1 + point.mass 5))
    (b := -(point.mass 1)) (c := -(point.mass 1 + point.mass 5))
    (d := directionChartExactFloor point 3 - (point.mass 0 + point.mass 1))
    (e := -(point.mass 0 + point.mass 1))
    (f := directionChartExactFloor point 4 -
      (point.mass 0 + point.mass 1 + point.mass 5))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact kFourPendant234Probe_ne_zero_of_ne_zero hy
  · intro y
    change kFourPendant234Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({2, 3, 4} : Finset (Fin 6)) *ᵥ kFourPendant234Probe y) = _
    exact dotProduct_kFourPendant234Gap_probe_eq_zMatrix point y
  · linarith [point.mass_pos 1]
  · nlinarith [point.mass_pos 1, point.mass_pos 5]
  · nlinarith [point.mass_pos 0, point.mass_pos 1]

theorem false_of_kFourPendant235_gapCorankTwo
    (point : DirectionChartPoint 6)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      ({2, 3, 5} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point ({2, 3, 5} : Finset (Fin 6))) :
    False := by
  refine false_of_gapCorankTwo_of_irreducible_zThree_pullback point
    ({2, 3, 5} : Finset (Fin 6)) hgap hcorank kFourPendant235ProbeLinear
    (a := directionChartExactFloor point 2 - (point.mass 0 + point.mass 4))
    (b := -(point.mass 0)) (c := -(point.mass 0 + point.mass 4))
    (d := directionChartExactFloor point 3 - (point.mass 0 + point.mass 1))
    (e := -(point.mass 0 + point.mass 1))
    (f := directionChartExactFloor point 5 -
      (point.mass 0 + point.mass 1 + point.mass 4))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact kFourPendant235Probe_ne_zero_of_ne_zero hy
  · intro y
    change kFourPendant235Probe y ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight
          ({2, 3, 5} : Finset (Fin 6)) *ᵥ kFourPendant235Probe y) = _
    exact dotProduct_kFourPendant235Gap_probe_eq_zMatrix point y
  · linarith [point.mass_pos 0]
  · nlinarith [point.mass_pos 0, point.mass_pos 4]
  · nlinarith [point.mass_pos 0, point.mass_pos 1]

/-! ## The corank-two branch is star-only -/

/-- A weak K4 spanning tree with two noncollinear gap kernels is necessarily a
vertex star.  The twelve path cases are discharged by their exact
irreducible-Z pullbacks. -/
theorem mem_kFourStarList_of_gapCorankTwo
    (point : DirectionChartPoint 6) (tree : Finset (Fin 6))
    (htree : tree ∈ kFourSpanningTreeList)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point tree) :
    tree ∈ kFourStarList := by
  simp only [kFourSpanningTreeList, List.mem_cons, List.not_mem_nil, or_false]
    at htree
  rcases htree with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · exact (false_of_kFourPath014_gapCorankTwo point hgap hcorank).elim
  · exact (false_of_kFourPath015_gapCorankTwo point hgap hcorank).elim
  · exact (false_of_kFourPendant023_gapCorankTwo point hgap hcorank).elim
  · exact (false_of_kFourPath025_gapCorankTwo point hgap hcorank).elim
  · exact (false_of_kFourPath035_gapCorankTwo point hgap hcorank).elim
  · exact (false_of_kFourPath045_gapCorankTwo point hgap hcorank).elim
  · exact (false_of_kFourPendant123_gapCorankTwo point hgap hcorank).elim
  · exact (false_of_kFourPath124_gapCorankTwo point hgap hcorank).elim
  · exact (false_of_kFourBand134_gapCorankTwo point hgap hcorank).elim
  · exact (false_of_kFourPath145_gapCorankTwo point hgap hcorank).elim
  · exact (false_of_kFourPendant234_gapCorankTwo point hgap hcorank).elim
  · exact (false_of_kFourPendant235_gapCorankTwo point hgap hcorank).elim

/-- The orbit-free A3 residual after eliminating every path from the
corank-two disjunct. -/
def KFourWeakTreeGapStarCorankResidual (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList,
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
    KFourTreeWindowData point tree ∧
    (KFourTreeWindowPivotWallData point tree ∨
      (tree ∈ kFourStarList ∧ KFourTreeGapCorankTwoData point tree))

/-- Every gap-corank residual has the star-only form. -/
theorem kFourWeakTreeGapStarCorankResidual_of_gapCorankResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeGapCorankResidual point) :
    KFourWeakTreeGapStarCorankResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | hcorank⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl hpivot⟩
  · exact ⟨tree, htree, hgap, hwindow, Or.inr
      ⟨mem_kFourStarList_of_gapCorankTwo point tree htree hgap hcorank,
        hcorank⟩⟩

/-- Forgetting the proved star classification recovers the preceding
gap-corank residual. -/
theorem kFourWeakTreeGapCorankResidual_of_starCorankResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeGapStarCorankResidual point) :
    KFourWeakTreeGapCorankResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | ⟨_, hcorank⟩⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl hpivot⟩
  · exact ⟨tree, htree, hgap, hwindow, Or.inr hcorank⟩

theorem kFourWeakTreeGapStarCorankResidual_iff_gapCorankResidual
    (point : DirectionChartPoint 6) :
    KFourWeakTreeGapStarCorankResidual point ↔
      KFourWeakTreeGapCorankResidual point :=
  ⟨kFourWeakTreeGapCorankResidual_of_starCorankResidual point,
    kFourWeakTreeGapStarCorankResidual_of_gapCorankResidual point⟩

/-- **THE STAR-ONLY A3 JOINT.**  The singular branch has been reduced from
sixteen spanning trees to the four vertex stars. -/
noncomputable def KFourKnifeBandRefinedTreeGapStarCorankResidualWeakToStrict :
    Prop :=
  forall point : DirectionChartPoint 6, ¬ KFourLayerACellFires point ->
    ¬ KFourExchangeStarCellFires point ->
    ¬ KFourAllTreeMinorAtlasCellFires point ->
    KFourAllTreeObstructionLedger point ->
    KFourWeakTreeGapStarCorankResidual point ->
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- The star-only formula is exactly the previous original-gap formula. -/
theorem kFourKnifeBandRefinedTreeGapStarCorankResidual_iff_gapCorankResidual :
    KFourKnifeBandRefinedTreeGapStarCorankResidualWeakToStrict ↔
      KFourKnifeBandRefinedTreeGapCorankResidualWeakToStrict := by
  constructor
  · intro hstar point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hstar point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeGapStarCorankResidual_of_gapCorankResidual point hwitness)
  · intro hgap point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hgap point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeGapCorankResidual_of_starCorankResidual point hwitness)

/-- The star-only residual is exactly the public refined K4 knife band. -/
theorem kFourKnifeBandRefinedTreeGapStarCorankResidual_iff :
    KFourKnifeBandRefinedTreeGapStarCorankResidualWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedTreeGapStarCorankResidual_iff_gapCorankResidual.trans
    kFourKnifeBandRefinedTreeGapCorankResidual_iff

/-- The design-side K4 selector is exactly the star-only residual. -/
theorem kFourFamilySelection_iff_treeGapStarCorankResidual :
    KFourFamilySelection ↔
      KFourKnifeBandRefinedTreeGapStarCorankResidualWeakToStrict :=
  kFourFamilySelection_iff_treeGapCorankResidual.trans
    kFourKnifeBandRefinedTreeGapStarCorankResidual_iff_gapCorankResidual.symm

end Gtz
