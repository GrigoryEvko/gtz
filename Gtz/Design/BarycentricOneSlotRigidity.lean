import Gtz.Design.LineBranchRankTwoOneSlot
import Gtz.Design.LineBranchOneSlotDeterminant
import Gtz.Design.LineBranchCandidateReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

/-!
# A barycentric conservation law for the tight-line one-slot grid

This file isolates the algebra behind a new partial closure of the generic
tight-line branch.  A symmetric rank-two form whose kernel is the all-ones
vector is a three-vertex Laplacian

    L = !![a+b, -a, -b; -a, a+c, -c; -b, -c, b+c].

Write a transverse free atom as `sqrt(rho) * q`, where the barycentric
coordinates of `q` sum to one.  The determinant of the one-slot candidate
obtained by dropping axis `i` of squared tight reading `s_i` is

    kappa * (rho - s_i) - s_i * rho * energy_i(q),

where `kappa = a*b + a*c + b*c`.  Parseval makes a positive weighted sum of
the nine determinants exactly zero.  Consequently, if all barycentric
coordinates are positive, universal refusal forces all nine determinants to
vanish.  The three equalities for one free atom determine its barycentric
coordinates uniquely when `kappa > 0`; hence all three free atoms are
parallel.  This is incompatible with the line-free free-frame determinant.

The bridge from the design normal form is intentionally not asserted here.
In particular, this theorem does not cover the zero-tight-coordinate face
inhabited by Wave C's `windowRefusalWitnessDesign`.
-/

namespace Gtz

/-- The common cofactor of a three-vertex Laplacian. -/
def triangleLaplacianCofactor (edge01 edge02 edge12 : ℝ) : ℝ :=
  edge01 * edge02 + edge01 * edge12 + edge02 * edge12

/-- Effective-energy numerator at vertex zero for barycentric coordinates
`(x,y,1-x-y)`. -/
def barycentricEnergyZero (edge01 edge02 edge12 x y : ℝ) : ℝ :=
  edge01 * (1 - x - y) ^ 2 + edge02 * y ^ 2 + edge12 * (1 - x) ^ 2

/-- Effective-energy numerator at vertex one. -/
def barycentricEnergyOne (edge01 edge02 edge12 x y : ℝ) : ℝ :=
  edge01 * (1 - x - y) ^ 2 + edge02 * (1 - y) ^ 2 + edge12 * x ^ 2

/-- Effective-energy numerator at vertex two. -/
def barycentricEnergyTwo (edge01 edge02 edge12 x y : ℝ) : ℝ :=
  edge01 * (x + y) ^ 2 + edge02 * y ^ 2 + edge12 * x ^ 2

/-- The determinant polynomial for dropping axis zero. -/
def barycentricOneSlotDetZero
    (edge01 edge02 edge12 scale rho x y : ℝ) : ℝ :=
  triangleLaplacianCofactor edge01 edge02 edge12 * (rho - scale)
    - scale * rho * barycentricEnergyZero edge01 edge02 edge12 x y

/-- The determinant polynomial for dropping axis one. -/
def barycentricOneSlotDetOne
    (edge01 edge02 edge12 scale rho x y : ℝ) : ℝ :=
  triangleLaplacianCofactor edge01 edge02 edge12 * (rho - scale)
    - scale * rho * barycentricEnergyOne edge01 edge02 edge12 x y

/-- The determinant polynomial for dropping axis two. -/
def barycentricOneSlotDetTwo
    (edge01 edge02 edge12 scale rho x y : ℝ) : ℝ :=
  triangleLaplacianCofactor edge01 edge02 edge12 * (rho - scale)
    - scale * rho * barycentricEnergyTwo edge01 edge02 edge12 x y

/-- The determinant of the rank-one update/downdate of a three-vertex
Laplacian is the corresponding barycentric polynomial. -/
theorem det_triangleLaplacian_sub_axis_add_barycentricAtom
    (edge01 edge02 edge12 scale rho x y : ℝ) :
    let laplacian : Matrix (Fin 3) (Fin 3) ℝ :=
      !![edge01 + edge02, -edge01, -edge02;
        -edge01, edge01 + edge12, -edge12;
        -edge02, -edge12, edge02 + edge12]
    let barycentric : Fin 3 → ℝ := ![x, y, 1 - x - y]
    (laplacian - scale • atomMatrix (![1, 0, 0] : Fin 3 → ℝ)
        + rho • atomMatrix barycentric).det
      = barycentricOneSlotDetZero edge01 edge02 edge12 scale rho x y := by
  simp only [Matrix.det_fin_three, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply,
    barycentricOneSlotDetZero, barycentricEnergyZero,
    triangleLaplacianCofactor]
  ring

theorem det_triangleLaplacian_sub_axis_one_add_barycentricAtom
    (edge01 edge02 edge12 scale rho x y : ℝ) :
    let laplacian : Matrix (Fin 3) (Fin 3) ℝ :=
      !![edge01 + edge02, -edge01, -edge02;
        -edge01, edge01 + edge12, -edge12;
        -edge02, -edge12, edge02 + edge12]
    let barycentric : Fin 3 → ℝ := ![x, y, 1 - x - y]
    (laplacian - scale • atomMatrix (![0, 1, 0] : Fin 3 → ℝ)
        + rho • atomMatrix barycentric).det
      = barycentricOneSlotDetOne edge01 edge02 edge12 scale rho x y := by
  simp only [Matrix.det_fin_three, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply,
    barycentricOneSlotDetOne, barycentricEnergyOne,
    triangleLaplacianCofactor]
  ring

theorem det_triangleLaplacian_sub_axis_two_add_barycentricAtom
    (edge01 edge02 edge12 scale rho x y : ℝ) :
    let laplacian : Matrix (Fin 3) (Fin 3) ℝ :=
      !![edge01 + edge02, -edge01, -edge02;
        -edge01, edge01 + edge12, -edge12;
        -edge02, -edge12, edge02 + edge12]
    let barycentric : Fin 3 → ℝ := ![x, y, 1 - x - y]
    (laplacian - scale • atomMatrix (![0, 0, 1] : Fin 3 → ℝ)
        + rho • atomMatrix barycentric).det
      = barycentricOneSlotDetTwo edge01 edge02 edge12 scale rho x y := by
  simp only [Matrix.det_fin_three, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply,
    barycentricOneSlotDetTwo, barycentricEnergyTwo,
    triangleLaplacianCofactor]
  ring

/-! ## The determinant conservation law -/

/-- **THE BARYCENTRIC ONE-SLOT CONSERVATION LAW.**

The edge equations say that the Laplacian is the weighted covariance of the
three barycentric free atoms.  The coordinate equations are the diagonal
Parseval equations, and the last equation is weight normalization.  Under
exactly these identities, the positive barycentric weighted sum of all nine
one-slot determinant polynomials is zero.

The coefficients have been multiplied by `s0*s1*s2`, so the statement is
division-free. -/
theorem barycentricOneSlot_weighted_det_sum_eq_zero
    (edge01 edge02 edge12 : ℝ)
    (s0 s1 s2 b0 b1 b2 : ℝ)
    (u0 u1 u2 rho0 rho1 rho2 : ℝ)
    (x0 y0 x1 y1 x2 y2 : ℝ)
    (hedge01 : edge01 =
      u0 * rho0 * x0 * y0 + u1 * rho1 * x1 * y1 + u2 * rho2 * x2 * y2)
    (hedge02 : edge02 =
      u0 * rho0 * x0 * (1 - x0 - y0)
        + u1 * rho1 * x1 * (1 - x1 - y1)
        + u2 * rho2 * x2 * (1 - x2 - y2))
    (hedge12 : edge12 =
      u0 * rho0 * y0 * (1 - x0 - y0)
        + u1 * rho1 * y1 * (1 - x1 - y1)
        + u2 * rho2 * y2 * (1 - x2 - y2))
    (hcoord0 :
      u0 * rho0 * x0 + u1 * rho1 * x1 + u2 * rho2 * x2 = (1 - b0) * s0)
    (hcoord1 :
      u0 * rho0 * y0 + u1 * rho1 * y1 + u2 * rho2 * y2 = (1 - b1) * s1)
    (hcoord2 :
      u0 * rho0 * (1 - x0 - y0) + u1 * rho1 * (1 - x1 - y1)
          + u2 * rho2 * (1 - x2 - y2) = (1 - b2) * s2)
    (hweight : b0 + b1 + b2 + u0 + u1 + u2 = 1) :
    u0 * (x0 * s1 * s2
            * barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho0 x0 y0
          + y0 * s0 * s2
            * barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho0 x0 y0
          + (1 - x0 - y0) * s0 * s1
            * barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho0 x0 y0)
      + u1 * (x1 * s1 * s2
            * barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho1 x1 y1
          + y1 * s0 * s2
            * barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho1 x1 y1
          + (1 - x1 - y1) * s0 * s1
            * barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho1 x1 y1)
      + u2 * (x2 * s1 * s2
            * barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho2 x2 y2
          + y2 * s0 * s2
            * barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho2 x2 y2
          + (1 - x2 - y2) * s0 * s1
            * barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho2 x2 y2) = 0 := by
  rw [hedge01, hedge02, hedge12]
  simp only [barycentricOneSlotDetZero, barycentricOneSlotDetOne,
    barycentricOneSlotDetTwo, barycentricEnergyZero, barycentricEnergyOne,
    barycentricEnergyTwo, triangleLaplacianCofactor]
  let edgeZeroOne :=
    u0 * rho0 * x0 * y0 + u1 * rho1 * x1 * y1 + u2 * rho2 * x2 * y2
  let edgeZeroTwo :=
    u0 * rho0 * x0 * (1 - x0 - y0)
      + u1 * rho1 * x1 * (1 - x1 - y1)
      + u2 * rho2 * x2 * (1 - x2 - y2)
  let edgeOneTwo :=
    u0 * rho0 * y0 * (1 - x0 - y0)
      + u1 * rho1 * y1 * (1 - x1 - y1)
      + u2 * rho2 * y2 * (1 - x2 - y2)
  let commonCofactor := edgeZeroOne * edgeZeroTwo
    + edgeZeroOne * edgeOneTwo + edgeZeroTwo * edgeOneTwo
  linear_combination
    s1 * s2 * commonCofactor * hcoord0
      + s0 * s2 * commonCofactor * hcoord1
      + s0 * s1 * commonCofactor * hcoord2
      - s0 * s1 * s2 * commonCofactor * hweight

/-! ## Rigidity of the equality locus -/

theorem barycentricEnergyZero_sub_one
    (edge01 edge02 edge12 x y : ℝ) :
    barycentricEnergyZero edge01 edge02 edge12 x y
        - barycentricEnergyOne edge01 edge02 edge12 x y
      = 2 * edge02 * y - edge02 - 2 * edge12 * x + edge12 := by
  simp only [barycentricEnergyZero, barycentricEnergyOne]
  ring

theorem barycentricEnergyZero_sub_two
    (edge01 edge02 edge12 x y : ℝ) :
    barycentricEnergyZero edge01 edge02 edge12 x y
        - barycentricEnergyTwo edge01 edge02 edge12 x y
      = -2 * edge01 * x - 2 * edge01 * y + edge01
          - 2 * edge12 * x + edge12 := by
  simp only [barycentricEnergyZero, barycentricEnergyTwo]
  ring

/-- Three vanishing one-slot determinants pin the two energy differences to
values independent of the free atom's transverse scale. -/
theorem barycentric_energy_differences_of_three_dets_zero
    (edge01 edge02 edge12 s0 s1 s2 rho x y : ℝ)
    (hrho : rho ≠ 0)
    (hzero : barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho x y = 0)
    (hone : barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho x y = 0)
    (htwo : barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho x y = 0) :
    s0 * s1 *
          (barycentricEnergyZero edge01 edge02 edge12 x y
            - barycentricEnergyOne edge01 edge02 edge12 x y)
        = triangleLaplacianCofactor edge01 edge02 edge12 * (s1 - s0)
      ∧ s0 * s2 *
          (barycentricEnergyZero edge01 edge02 edge12 x y
            - barycentricEnergyTwo edge01 edge02 edge12 x y)
        = triangleLaplacianCofactor edge01 edge02 edge12 * (s2 - s0) := by
  constructor
  · have hfactor : rho *
        (triangleLaplacianCofactor edge01 edge02 edge12 * (s1 - s0)
          - s0 * s1 *
            (barycentricEnergyZero edge01 edge02 edge12 x y
              - barycentricEnergyOne edge01 edge02 edge12 x y)) = 0 := by
      simp only [barycentricOneSlotDetZero] at hzero
      simp only [barycentricOneSlotDetOne] at hone
      linear_combination s1 * hzero - s0 * hone
    have hinside := (mul_eq_zero.mp hfactor).resolve_left hrho
    linarith
  · have hfactor : rho *
        (triangleLaplacianCofactor edge01 edge02 edge12 * (s2 - s0)
          - s0 * s2 *
            (barycentricEnergyZero edge01 edge02 edge12 x y
              - barycentricEnergyTwo edge01 edge02 edge12 x y)) = 0 := by
      simp only [barycentricOneSlotDetZero] at hzero
      simp only [barycentricOneSlotDetTwo] at htwo
      linear_combination s2 * hzero - s0 * htwo
    have hinside := (mul_eq_zero.mp hfactor).resolve_left hrho
    linarith

/-- At nonzero cofactor and nonzero axis scales, the common zero locus of the
three one-slot determinant polynomials contains at most one barycentric point.
The transverse scale `rho` may differ between the two points. -/
theorem barycentric_point_unique_of_three_dets_zero
    (edge01 edge02 edge12 s0 s1 s2 rho rho' x y x' y' : ℝ)
    (hkappa : triangleLaplacianCofactor edge01 edge02 edge12 ≠ 0)
    (hs0 : s0 ≠ 0) (hs1 : s1 ≠ 0) (hs2 : s2 ≠ 0)
    (hrho : rho ≠ 0) (hrho' : rho' ≠ 0)
    (hzero : barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho x y = 0)
    (hone : barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho x y = 0)
    (htwo : barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho x y = 0)
    (hzero' : barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho' x' y' = 0)
    (hone' : barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho' x' y' = 0)
    (htwo' : barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho' x' y' = 0) :
    x = x' ∧ y = y' := by
  have hdiff := barycentric_energy_differences_of_three_dets_zero
    edge01 edge02 edge12 s0 s1 s2 rho x y hrho hzero hone htwo
  have hdiff' := barycentric_energy_differences_of_three_dets_zero
    edge01 edge02 edge12 s0 s1 s2 rho' x' y' hrho' hzero' hone' htwo'
  have hs01 : s0 * s1 ≠ 0 := mul_ne_zero hs0 hs1
  have hs02 : s0 * s2 ≠ 0 := mul_ne_zero hs0 hs2
  have henergy01 :
      barycentricEnergyZero edge01 edge02 edge12 x y
          - barycentricEnergyOne edge01 edge02 edge12 x y
        = barycentricEnergyZero edge01 edge02 edge12 x' y'
          - barycentricEnergyOne edge01 edge02 edge12 x' y' := by
    have hmul : s0 * s1 *
        ((barycentricEnergyZero edge01 edge02 edge12 x y
            - barycentricEnergyOne edge01 edge02 edge12 x y)
          - (barycentricEnergyZero edge01 edge02 edge12 x' y'
            - barycentricEnergyOne edge01 edge02 edge12 x' y')) = 0 := by
      linear_combination hdiff.1 - hdiff'.1
    have := (mul_eq_zero.mp hmul).resolve_left hs01
    linarith
  have henergy02 :
      barycentricEnergyZero edge01 edge02 edge12 x y
          - barycentricEnergyTwo edge01 edge02 edge12 x y
        = barycentricEnergyZero edge01 edge02 edge12 x' y'
          - barycentricEnergyTwo edge01 edge02 edge12 x' y' := by
    have hmul : s0 * s2 *
        ((barycentricEnergyZero edge01 edge02 edge12 x y
            - barycentricEnergyTwo edge01 edge02 edge12 x y)
          - (barycentricEnergyZero edge01 edge02 edge12 x' y'
            - barycentricEnergyTwo edge01 edge02 edge12 x' y')) = 0 := by
      linear_combination hdiff.2 - hdiff'.2
    have := (mul_eq_zero.mp hmul).resolve_left hs02
    linarith
  rw [barycentricEnergyZero_sub_one, barycentricEnergyZero_sub_one] at henergy01
  rw [barycentricEnergyZero_sub_two, barycentricEnergyZero_sub_two] at henergy02
  have hxmul : 2 * triangleLaplacianCofactor edge01 edge02 edge12 * (x - x') = 0 := by
    simp only [triangleLaplacianCofactor]
    linear_combination
      -(edge01 * henergy01 + edge02 * henergy02)
  have hymul : 2 * triangleLaplacianCofactor edge01 edge02 edge12 * (y - y') = 0 := by
    simp only [triangleLaplacianCofactor]
    linear_combination
      (edge01 + edge12) * henergy01 - edge12 * henergy02
  have hkappaTwo : 2 * triangleLaplacianCofactor edge01 edge02 edge12 ≠ 0 :=
    mul_ne_zero (by norm_num) hkappa
  have hxzero := (mul_eq_zero.mp hxmul).resolve_left hkappaTwo
  have hyzero := (mul_eq_zero.mp hymul).resolve_left hkappaTwo
  exact ⟨sub_eq_zero.mp hxzero, sub_eq_zero.mp hyzero⟩

/-! ## Universal refusal forces the equality locus -/

/-- A positive weighted sum of nine nonpositive values can vanish only when
all nine values vanish.  Kept scalar so downstream design bridges do not need
to normalize a `Fin 9` enumeration. -/
theorem nine_values_eq_zero_of_positive_weighted_sum
    (c00 c10 c20 c01 c11 c21 c02 c12 c22 : ℝ)
    (d00 d10 d20 d01 d11 d21 d02 d12 d22 : ℝ)
    (hc00 : 0 < c00) (hc10 : 0 < c10) (hc20 : 0 < c20)
    (hc01 : 0 < c01) (hc11 : 0 < c11) (hc21 : 0 < c21)
    (hc02 : 0 < c02) (hc12 : 0 < c12) (hc22 : 0 < c22)
    (hd00 : d00 ≤ 0) (hd10 : d10 ≤ 0) (hd20 : d20 ≤ 0)
    (hd01 : d01 ≤ 0) (hd11 : d11 ≤ 0) (hd21 : d21 ≤ 0)
    (hd02 : d02 ≤ 0) (hd12 : d12 ≤ 0) (hd22 : d22 ≤ 0)
    (hsum : c00 * d00 + c10 * d10 + c20 * d20
        + (c01 * d01 + c11 * d11 + c21 * d21)
        + (c02 * d02 + c12 * d12 + c22 * d22) = 0) :
    d00 = 0 ∧ d10 = 0 ∧ d20 = 0
      ∧ d01 = 0 ∧ d11 = 0 ∧ d21 = 0
      ∧ d02 = 0 ∧ d12 = 0 ∧ d22 = 0 := by
  have ht00 : c00 * d00 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc00.le hd00
  have ht10 : c10 * d10 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc10.le hd10
  have ht20 : c20 * d20 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc20.le hd20
  have ht01 : c01 * d01 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc01.le hd01
  have ht11 : c11 * d11 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc11.le hd11
  have ht21 : c21 * d21 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc21.le hd21
  have ht02 : c02 * d02 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc02.le hd02
  have ht12 : c12 * d12 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc12.le hd12
  have ht22 : c22 * d22 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc22.le hd22
  have hz00 : c00 * d00 = 0 := by linarith
  have hz10 : c10 * d10 = 0 := by linarith
  have hz20 : c20 * d20 = 0 := by linarith
  have hz01 : c01 * d01 = 0 := by linarith
  have hz11 : c11 * d11 = 0 := by linarith
  have hz21 : c21 * d21 = 0 := by linarith
  have hz02 : c02 * d02 = 0 := by linarith
  have hz12 : c12 * d12 = 0 := by linarith
  have hz22 : c22 * d22 = 0 := by linarith
  exact ⟨(mul_eq_zero.mp hz00).resolve_left hc00.ne',
    (mul_eq_zero.mp hz10).resolve_left hc10.ne',
    (mul_eq_zero.mp hz20).resolve_left hc20.ne',
    (mul_eq_zero.mp hz01).resolve_left hc01.ne',
    (mul_eq_zero.mp hz11).resolve_left hc11.ne',
    (mul_eq_zero.mp hz21).resolve_left hc21.ne',
    (mul_eq_zero.mp hz02).resolve_left hc02.ne',
    (mul_eq_zero.mp hz12).resolve_left hc12.ne',
    (mul_eq_zero.mp hz22).resolve_left hc22.ne'⟩

/-- In the open barycentric cell, refusal of all nine one-slot determinant
polynomials forces all nine onto their common equality locus. -/
theorem barycentric_all_oneSlot_dets_eq_zero_of_refusal
    (edge01 edge02 edge12 : ℝ)
    (s0 s1 s2 b0 b1 b2 : ℝ)
    (u0 u1 u2 rho0 rho1 rho2 : ℝ)
    (x0 y0 x1 y1 x2 y2 : ℝ)
    (hedge01 : edge01 =
      u0 * rho0 * x0 * y0 + u1 * rho1 * x1 * y1 + u2 * rho2 * x2 * y2)
    (hedge02 : edge02 =
      u0 * rho0 * x0 * (1 - x0 - y0)
        + u1 * rho1 * x1 * (1 - x1 - y1)
        + u2 * rho2 * x2 * (1 - x2 - y2))
    (hedge12 : edge12 =
      u0 * rho0 * y0 * (1 - x0 - y0)
        + u1 * rho1 * y1 * (1 - x1 - y1)
        + u2 * rho2 * y2 * (1 - x2 - y2))
    (hcoord0 :
      u0 * rho0 * x0 + u1 * rho1 * x1 + u2 * rho2 * x2 = (1 - b0) * s0)
    (hcoord1 :
      u0 * rho0 * y0 + u1 * rho1 * y1 + u2 * rho2 * y2 = (1 - b1) * s1)
    (hcoord2 :
      u0 * rho0 * (1 - x0 - y0) + u1 * rho1 * (1 - x1 - y1)
          + u2 * rho2 * (1 - x2 - y2) = (1 - b2) * s2)
    (hweight : b0 + b1 + b2 + u0 + u1 + u2 = 1)
    (hs0 : 0 < s0) (hs1 : 0 < s1) (hs2 : 0 < s2)
    (hu0 : 0 < u0) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hx0 : 0 < x0) (hy0 : 0 < y0) (hz0 : 0 < 1 - x0 - y0)
    (hx1 : 0 < x1) (hy1 : 0 < y1) (hz1 : 0 < 1 - x1 - y1)
    (hx2 : 0 < x2) (hy2 : 0 < y2) (hz2 : 0 < 1 - x2 - y2)
    (hd00 : barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho0 x0 y0 ≤ 0)
    (hd10 : barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho0 x0 y0 ≤ 0)
    (hd20 : barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho0 x0 y0 ≤ 0)
    (hd01 : barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho1 x1 y1 ≤ 0)
    (hd11 : barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho1 x1 y1 ≤ 0)
    (hd21 : barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho1 x1 y1 ≤ 0)
    (hd02 : barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho2 x2 y2 ≤ 0)
    (hd12 : barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho2 x2 y2 ≤ 0)
    (hd22 : barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho2 x2 y2 ≤ 0) :
    barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho0 x0 y0 = 0
      ∧ barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho0 x0 y0 = 0
      ∧ barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho0 x0 y0 = 0
      ∧ barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho1 x1 y1 = 0
      ∧ barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho1 x1 y1 = 0
      ∧ barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho1 x1 y1 = 0
      ∧ barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho2 x2 y2 = 0
      ∧ barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho2 x2 y2 = 0
      ∧ barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho2 x2 y2 = 0 := by
  have hsum := barycentricOneSlot_weighted_det_sum_eq_zero
    edge01 edge02 edge12 s0 s1 s2 b0 b1 b2
    u0 u1 u2 rho0 rho1 rho2 x0 y0 x1 y1 x2 y2
    hedge01 hedge02 hedge12 hcoord0 hcoord1 hcoord2 hweight
  apply nine_values_eq_zero_of_positive_weighted_sum
    (u0 * x0 * s1 * s2) (u0 * y0 * s0 * s2)
      (u0 * (1 - x0 - y0) * s0 * s1)
    (u1 * x1 * s1 * s2) (u1 * y1 * s0 * s2)
      (u1 * (1 - x1 - y1) * s0 * s1)
    (u2 * x2 * s1 * s2) (u2 * y2 * s0 * s2)
      (u2 * (1 - x2 - y2) * s0 * s1)
  · positivity
  · positivity
  · positivity
  · positivity
  · positivity
  · positivity
  · positivity
  · positivity
  · positivity
  · exact hd00
  · exact hd10
  · exact hd20
  · exact hd01
  · exact hd11
  · exact hd21
  · exact hd02
  · exact hd12
  · exact hd22
  · linear_combination hsum

/-- Once all nine determinants vanish, every free atom has the same
barycentric point. -/
theorem barycentric_points_equal_of_all_oneSlot_dets_zero
    (edge01 edge02 edge12 s0 s1 s2 rho0 rho1 rho2 x0 y0 x1 y1 x2 y2 : ℝ)
    (hkappa : triangleLaplacianCofactor edge01 edge02 edge12 ≠ 0)
    (hs0 : s0 ≠ 0) (hs1 : s1 ≠ 0) (hs2 : s2 ≠ 0)
    (hrho0 : rho0 ≠ 0) (hrho1 : rho1 ≠ 0) (hrho2 : rho2 ≠ 0)
    (hzeros :
      barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho0 x0 y0 = 0
        ∧ barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho0 x0 y0 = 0
        ∧ barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho0 x0 y0 = 0
        ∧ barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho1 x1 y1 = 0
        ∧ barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho1 x1 y1 = 0
        ∧ barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho1 x1 y1 = 0
        ∧ barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho2 x2 y2 = 0
        ∧ barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho2 x2 y2 = 0
        ∧ barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho2 x2 y2 = 0) :
    x0 = x1 ∧ y0 = y1 ∧ x0 = x2 ∧ y0 = y2 := by
  rcases hzeros with ⟨h00, h10, h20, h01, h11, h21, h02, h12, h22⟩
  have hpoint01 := barycentric_point_unique_of_three_dets_zero
    edge01 edge02 edge12 s0 s1 s2 rho0 rho1 x0 y0 x1 y1
    hkappa hs0 hs1 hs2 hrho0 hrho1 h00 h10 h20 h01 h11 h21
  have hpoint02 := barycentric_point_unique_of_three_dets_zero
    edge01 edge02 edge12 s0 s1 s2 rho0 rho2 x0 y0 x2 y2
    hkappa hs0 hs1 hs2 hrho0 hrho2 h00 h10 h20 h02 h12 h22
  exact ⟨hpoint01.1, hpoint01.2, hpoint02.1, hpoint02.2⟩

/-- **OPEN-CELL ONE-SLOT WIN.**  Under the Parseval balance equations, three
positive barycentric free points that are not all equal cannot refuse all nine
one-slot determinants. -/
theorem exists_positive_barycentricOneSlotDet_of_not_all_points_equal
    (edge01 edge02 edge12 : ℝ)
    (s0 s1 s2 b0 b1 b2 : ℝ)
    (u0 u1 u2 rho0 rho1 rho2 : ℝ)
    (x0 y0 x1 y1 x2 y2 : ℝ)
    (hedge01 : edge01 =
      u0 * rho0 * x0 * y0 + u1 * rho1 * x1 * y1 + u2 * rho2 * x2 * y2)
    (hedge02 : edge02 =
      u0 * rho0 * x0 * (1 - x0 - y0)
        + u1 * rho1 * x1 * (1 - x1 - y1)
        + u2 * rho2 * x2 * (1 - x2 - y2))
    (hedge12 : edge12 =
      u0 * rho0 * y0 * (1 - x0 - y0)
        + u1 * rho1 * y1 * (1 - x1 - y1)
        + u2 * rho2 * y2 * (1 - x2 - y2))
    (hcoord0 :
      u0 * rho0 * x0 + u1 * rho1 * x1 + u2 * rho2 * x2 = (1 - b0) * s0)
    (hcoord1 :
      u0 * rho0 * y0 + u1 * rho1 * y1 + u2 * rho2 * y2 = (1 - b1) * s1)
    (hcoord2 :
      u0 * rho0 * (1 - x0 - y0) + u1 * rho1 * (1 - x1 - y1)
          + u2 * rho2 * (1 - x2 - y2) = (1 - b2) * s2)
    (hweight : b0 + b1 + b2 + u0 + u1 + u2 = 1)
    (hs0 : 0 < s0) (hs1 : 0 < s1) (hs2 : 0 < s2)
    (hu0 : 0 < u0) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hrho0 : 0 < rho0) (hrho1 : 0 < rho1) (hrho2 : 0 < rho2)
    (hx0 : 0 < x0) (hy0 : 0 < y0) (hz0 : 0 < 1 - x0 - y0)
    (hx1 : 0 < x1) (hy1 : 0 < y1) (hz1 : 0 < 1 - x1 - y1)
    (hx2 : 0 < x2) (hy2 : 0 < y2) (hz2 : 0 < 1 - x2 - y2)
    (hdistinct : x0 ≠ x1 ∨ y0 ≠ y1 ∨ x0 ≠ x2 ∨ y0 ≠ y2) :
    0 < barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho0 x0 y0
      ∨ 0 < barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho0 x0 y0
      ∨ 0 < barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho0 x0 y0
      ∨ 0 < barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho1 x1 y1
      ∨ 0 < barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho1 x1 y1
      ∨ 0 < barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho1 x1 y1
      ∨ 0 < barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho2 x2 y2
      ∨ 0 < barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho2 x2 y2
      ∨ 0 < barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho2 x2 y2 := by
  have hedge01pos : 0 < edge01 := by rw [hedge01]; positivity
  have hedge02pos : 0 < edge02 := by rw [hedge02]; positivity
  have hedge12pos : 0 < edge12 := by rw [hedge12]; positivity
  have hkappa : triangleLaplacianCofactor edge01 edge02 edge12 ≠ 0 := by
    apply ne_of_gt
    simp only [triangleLaplacianCofactor]
    positivity
  by_contra hnone
  simp only [not_or, not_lt] at hnone
  rcases hnone with ⟨hd00, hd10, hd20, hd01, hd11, hd21, hd02, hd12, hd22⟩
  have hzeros := barycentric_all_oneSlot_dets_eq_zero_of_refusal
    edge01 edge02 edge12 s0 s1 s2 b0 b1 b2
    u0 u1 u2 rho0 rho1 rho2 x0 y0 x1 y1 x2 y2
    hedge01 hedge02 hedge12 hcoord0 hcoord1 hcoord2 hweight
    hs0 hs1 hs2 hu0 hu1 hu2 hx0 hy0 hz0 hx1 hy1 hz1 hx2 hy2 hz2
    hd00 hd10 hd20 hd01 hd11 hd21 hd02 hd12 hd22
  have hpoints := barycentric_points_equal_of_all_oneSlot_dets_zero
    edge01 edge02 edge12 s0 s1 s2 rho0 rho1 rho2 x0 y0 x1 y1 x2 y2
    hkappa hs0.ne' hs1.ne' hs2.ne' hrho0.ne' hrho1.ne' hrho2.ne' hzeros
  rcases hdistinct with hx01 | hy01 | hx02 | hy02
  · exact hx01 hpoints.1
  · exact hy01 hpoints.2.1
  · exact hx02 hpoints.2.2.1
  · exact hy02 hpoints.2.2.2

/-! ## Projective interpretation of the barycentric point -/

def tightBarycentricReading (tight freeAtom : Fin 3 → ℝ) : ℝ :=
  tight ⬝ᵥ freeAtom

noncomputable def tightBarycentricCoordinate
    (tight freeAtom : Fin 3 → ℝ) (coordinate : Fin 3) : ℝ :=
  tight coordinate * freeAtom coordinate / tightBarycentricReading tight freeAtom

def TightBarycentricOpenCell
    (tight : Fin 3 → ℝ) (freeAtom : Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ freeIndex coordinate,
    0 < tightBarycentricCoordinate tight (freeAtom freeIndex) coordinate

theorem tightBarycentricReading_ne_zero_of_openCell
    (tight : Fin 3 → ℝ) (freeAtom : Fin 3 → Fin 3 → ℝ)
    (hopen : TightBarycentricOpenCell tight freeAtom) (freeIndex : Fin 3) :
    tightBarycentricReading tight (freeAtom freeIndex) ≠ 0 := by
  intro hzero
  have hpositive := hopen freeIndex 0
  simp [tightBarycentricCoordinate, hzero] at hpositive

theorem tight_coordinate_ne_zero_of_openCell
    (tight : Fin 3 → ℝ) (freeAtom : Fin 3 → Fin 3 → ℝ)
    (hopen : TightBarycentricOpenCell tight freeAtom) (coordinate : Fin 3) :
    tight coordinate ≠ 0 := by
  intro hzero
  have hpositive := hopen 0 coordinate
  simp [tightBarycentricCoordinate, hzero] at hpositive

theorem sum_tightBarycentricCoordinate_eq_one
    (tight freeAtom : Fin 3 → ℝ)
    (hreading : tightBarycentricReading tight freeAtom ≠ 0) :
    tightBarycentricCoordinate tight freeAtom 0
        + tightBarycentricCoordinate tight freeAtom 1
        + tightBarycentricCoordinate tight freeAtom 2 = 1 := by
  simp only [tightBarycentricCoordinate, tightBarycentricReading,
    dotProduct, Fin.sum_univ_three] at hreading ⊢
  field_simp [hreading]

/-- Equal barycentric points make the corresponding free atoms parallel. -/
theorem freeAtom_parallel_of_barycentricCoordinates_eq
    (tight firstFree secondFree : Fin 3 → ℝ)
    (htight : ∀ coordinate, tight coordinate ≠ 0)
    (hfirstReading : tightBarycentricReading tight firstFree ≠ 0)
    (hsecondReading : tightBarycentricReading tight secondFree ≠ 0)
    (hcoordinates : ∀ coordinate,
      tightBarycentricCoordinate tight firstFree coordinate
        = tightBarycentricCoordinate tight secondFree coordinate) :
    secondFree =
      (tightBarycentricReading tight secondFree
          / tightBarycentricReading tight firstFree) • firstFree := by
  funext coordinate
  have hcoordinate := hcoordinates coordinate
  simp only [tightBarycentricCoordinate] at hcoordinate
  have hcross :
      tight coordinate *
          (secondFree coordinate * tightBarycentricReading tight firstFree)
        = tight coordinate *
          (tightBarycentricReading tight secondFree * firstFree coordinate) := by
    field_simp [hfirstReading, hsecondReading] at hcoordinate
    nlinarith
  have hcancel := mul_left_cancel₀ (htight coordinate) hcross
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [hfirstReading]
  nlinarith

/-- A nonzero free-frame bracket prevents the three free atoms from sharing
one barycentric point.  Only the first two coordinates need be compared: the
third follows because every barycentric point sums to one. -/
theorem not_all_tightBarycentricPoints_equal_of_tripleBracket_ne_zero
    (tight : Fin 3 → ℝ) (freeAtom : Fin 3 → Fin 3 → ℝ)
    (hopen : TightBarycentricOpenCell tight freeAtom)
    (hbracket : tripleBracket (freeAtom 0) (freeAtom 1) (freeAtom 2) ≠ 0) :
    tightBarycentricCoordinate tight (freeAtom 0) 0
        ≠ tightBarycentricCoordinate tight (freeAtom 1) 0
      ∨ tightBarycentricCoordinate tight (freeAtom 0) 1
        ≠ tightBarycentricCoordinate tight (freeAtom 1) 1
      ∨ tightBarycentricCoordinate tight (freeAtom 0) 0
        ≠ tightBarycentricCoordinate tight (freeAtom 2) 0
      ∨ tightBarycentricCoordinate tight (freeAtom 0) 1
        ≠ tightBarycentricCoordinate tight (freeAtom 2) 1 := by
  by_contra hall
  simp only [not_or, not_not] at hall
  rcases hall with ⟨hzero01, hone01, hzero02, hone02⟩
  have hread0 := tightBarycentricReading_ne_zero_of_openCell tight freeAtom hopen 0
  have hread1 := tightBarycentricReading_ne_zero_of_openCell tight freeAtom hopen 1
  have hread2 := tightBarycentricReading_ne_zero_of_openCell tight freeAtom hopen 2
  have hsum0 := sum_tightBarycentricCoordinate_eq_one tight (freeAtom 0) hread0
  have hsum1 := sum_tightBarycentricCoordinate_eq_one tight (freeAtom 1) hread1
  have hsum2 := sum_tightBarycentricCoordinate_eq_one tight (freeAtom 2) hread2
  have htwo01 : tightBarycentricCoordinate tight (freeAtom 0) 2
      = tightBarycentricCoordinate tight (freeAtom 1) 2 := by linarith
  have htwo02 : tightBarycentricCoordinate tight (freeAtom 0) 2
      = tightBarycentricCoordinate tight (freeAtom 2) 2 := by linarith
  have hparallel : freeAtom 1 =
      (tightBarycentricReading tight (freeAtom 1)
          / tightBarycentricReading tight (freeAtom 0)) • freeAtom 0 := by
    apply freeAtom_parallel_of_barycentricCoordinates_eq tight
      (freeAtom 0) (freeAtom 1)
      (tight_coordinate_ne_zero_of_openCell tight freeAtom hopen) hread0 hread1
    intro coordinate
    fin_cases coordinate
    · exact hzero01
    · exact hone01
    · exact htwo01
  apply hbracket
  exact tripleBracket_eq_zero_of_parallel (freeAtom 0) (freeAtom 2)
    (tightBarycentricReading tight (freeAtom 1)
      / tightBarycentricReading tight (freeAtom 0)) hparallel

/-! ## Diagonal congruence to the three-vertex Laplacian -/

def tightScaledEdgeZeroOne
    (form : Matrix (Fin 3) (Fin 3) ℝ) (tight : Fin 3 → ℝ) : ℝ :=
  -(tight 0 * tight 1 * form 0 1)

def tightScaledEdgeZeroTwo
    (form : Matrix (Fin 3) (Fin 3) ℝ) (tight : Fin 3 → ℝ) : ℝ :=
  -(tight 0 * tight 2 * form 0 2)

def tightScaledEdgeOneTwo
    (form : Matrix (Fin 3) (Fin 3) ℝ) (tight : Fin 3 → ℝ) : ℝ :=
  -(tight 1 * tight 2 * form 1 2)

/-- A symmetric three-dimensional form killing `tight`, after congruence by
the diagonal of `tight`, is exactly a three-vertex Laplacian. -/
theorem diagonal_mul_form_mul_diagonal_eq_triangleLaplacian
    (form : Matrix (Fin 3) (Fin 3) ℝ) (tight : Fin 3 → ℝ)
    (hsymmetric : Matrix.transpose form = form)
    (hkernel : Matrix.mulVec form tight = 0) :
    Matrix.diagonal tight * form * Matrix.diagonal tight
      = !![tightScaledEdgeZeroOne form tight + tightScaledEdgeZeroTwo form tight,
            -tightScaledEdgeZeroOne form tight, -tightScaledEdgeZeroTwo form tight;
          -tightScaledEdgeZeroOne form tight,
            tightScaledEdgeZeroOne form tight + tightScaledEdgeOneTwo form tight,
            -tightScaledEdgeOneTwo form tight;
          -tightScaledEdgeZeroTwo form tight, -tightScaledEdgeOneTwo form tight,
            tightScaledEdgeZeroTwo form tight + tightScaledEdgeOneTwo form tight] := by
  have hk0 := congrFun hkernel 0
  have hk1 := congrFun hkernel 1
  have hk2 := congrFun hkernel 2
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.zero_apply] at hk0 hk1 hk2
  have hsym : ∀ row col : Fin 3, form col row = form row col := by
    intro row col
    have hentry := congrFun (congrFun hsymmetric row) col
    simpa only [Matrix.transpose_apply] using hentry
  have hd0 : tight 0 * form 0 0 * tight 0
      = -(tight 0 * tight 1 * form 0 1) - (tight 0 * tight 2 * form 0 2) := by
    linear_combination tight 0 * hk0
  have hd1 : tight 1 * form 1 1 * tight 1
      = -(tight 0 * tight 1 * form 0 1) - (tight 1 * tight 2 * form 1 2) := by
    rw [hsym 0 1] at hk1
    linear_combination tight 1 * hk1
  have hd2 : tight 2 * form 2 2 * tight 2
      = -(tight 0 * tight 2 * form 0 2) - (tight 1 * tight 2 * form 1 2) := by
    rw [hsym 0 2, hsym 1 2] at hk2
    linear_combination tight 2 * hk2
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply,
      tightScaledEdgeZeroOne, tightScaledEdgeZeroTwo, tightScaledEdgeOneTwo,
      hsym 0 1, hsym 0 2, hsym 1 2] <;>
    first | exact hd0 | exact hd1 | exact hd2 | ring

theorem sq_tightBarycentricReading_mul_two_coordinates
    (tight freeAtom : Fin 3 → ℝ) (first second : Fin 3)
    (hreading : tightBarycentricReading tight freeAtom ≠ 0) :
    tightBarycentricReading tight freeAtom ^ 2
        * tightBarycentricCoordinate tight freeAtom first
        * tightBarycentricCoordinate tight freeAtom second
      = (tight first * freeAtom first) * (tight second * freeAtom second) := by
  simp only [tightBarycentricCoordinate]
  field_simp [hreading]

theorem sq_tightBarycentricReading_mul_coordinate
    (tight freeAtom : Fin 3 → ℝ) (coordinate : Fin 3)
    (hreading : tightBarycentricReading tight freeAtom ≠ 0) :
    tightBarycentricReading tight freeAtom ^ 2
        * tightBarycentricCoordinate tight freeAtom coordinate
      = tightBarycentricReading tight freeAtom
          * (tight coordinate * freeAtom coordinate) := by
  simp only [tightBarycentricCoordinate]
  field_simp [hreading]

/-- The off-diagonal Parseval equations identify the three Laplacian edges
with the positive weighted barycentric edge moments. -/
theorem tightScaledEdges_eq_barycentricMoments_of_frame
    (form : Matrix (Fin 3) (Fin 3) ℝ) (tight : Fin 3 → ℝ)
    (freeAtom : Fin 3 → Fin 3 → ℝ)
    (u0 u1 u2 : ℝ) (baseWeight : Fin 3 → ℝ)
    (hframe : form
        + u0 • atomMatrix (freeAtom 0)
        + u1 • atomMatrix (freeAtom 1)
        + u2 • atomMatrix (freeAtom 2)
      = Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate))
    (hread0 : tightBarycentricReading tight (freeAtom 0) ≠ 0)
    (hread1 : tightBarycentricReading tight (freeAtom 1) ≠ 0)
    (hread2 : tightBarycentricReading tight (freeAtom 2) ≠ 0) :
    tightScaledEdgeZeroOne form tight =
        u0 * tightBarycentricReading tight (freeAtom 0) ^ 2
            * tightBarycentricCoordinate tight (freeAtom 0) 0
            * tightBarycentricCoordinate tight (freeAtom 0) 1
          + u1 * tightBarycentricReading tight (freeAtom 1) ^ 2
            * tightBarycentricCoordinate tight (freeAtom 1) 0
            * tightBarycentricCoordinate tight (freeAtom 1) 1
          + u2 * tightBarycentricReading tight (freeAtom 2) ^ 2
            * tightBarycentricCoordinate tight (freeAtom 2) 0
            * tightBarycentricCoordinate tight (freeAtom 2) 1
      ∧ tightScaledEdgeZeroTwo form tight =
        u0 * tightBarycentricReading tight (freeAtom 0) ^ 2
            * tightBarycentricCoordinate tight (freeAtom 0) 0
            * tightBarycentricCoordinate tight (freeAtom 0) 2
          + u1 * tightBarycentricReading tight (freeAtom 1) ^ 2
            * tightBarycentricCoordinate tight (freeAtom 1) 0
            * tightBarycentricCoordinate tight (freeAtom 1) 2
          + u2 * tightBarycentricReading tight (freeAtom 2) ^ 2
            * tightBarycentricCoordinate tight (freeAtom 2) 0
            * tightBarycentricCoordinate tight (freeAtom 2) 2
      ∧ tightScaledEdgeOneTwo form tight =
        u0 * tightBarycentricReading tight (freeAtom 0) ^ 2
            * tightBarycentricCoordinate tight (freeAtom 0) 1
            * tightBarycentricCoordinate tight (freeAtom 0) 2
          + u1 * tightBarycentricReading tight (freeAtom 1) ^ 2
            * tightBarycentricCoordinate tight (freeAtom 1) 1
            * tightBarycentricCoordinate tight (freeAtom 1) 2
          + u2 * tightBarycentricReading tight (freeAtom 2) ^ 2
            * tightBarycentricCoordinate tight (freeAtom 2) 1
            * tightBarycentricCoordinate tight (freeAtom 2) 2 := by
  have h01 := congrFun (congrFun hframe 0) 1
  have h02 := congrFun (congrFun hframe 0) 2
  have h12 := congrFun (congrFun hframe 1) 2
  simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix,
    Matrix.vecMulVec_apply] at h01 h02 h12
  have hm001 := sq_tightBarycentricReading_mul_two_coordinates
    tight (freeAtom 0) 0 1 hread0
  have hm101 := sq_tightBarycentricReading_mul_two_coordinates
    tight (freeAtom 1) 0 1 hread1
  have hm201 := sq_tightBarycentricReading_mul_two_coordinates
    tight (freeAtom 2) 0 1 hread2
  have hm002 := sq_tightBarycentricReading_mul_two_coordinates
    tight (freeAtom 0) 0 2 hread0
  have hm102 := sq_tightBarycentricReading_mul_two_coordinates
    tight (freeAtom 1) 0 2 hread1
  have hm202 := sq_tightBarycentricReading_mul_two_coordinates
    tight (freeAtom 2) 0 2 hread2
  have hm012 := sq_tightBarycentricReading_mul_two_coordinates
    tight (freeAtom 0) 1 2 hread0
  have hm112 := sq_tightBarycentricReading_mul_two_coordinates
    tight (freeAtom 1) 1 2 hread1
  have hm212 := sq_tightBarycentricReading_mul_two_coordinates
    tight (freeAtom 2) 1 2 hread2
  constructor
  · simp only [tightScaledEdgeZeroOne]
    linear_combination
      -(tight 0 * tight 1) * h01 - u0 * hm001 - u1 * hm101 - u2 * hm201
  constructor
  · simp only [tightScaledEdgeZeroTwo]
    linear_combination
      -(tight 0 * tight 2) * h02 - u0 * hm002 - u1 * hm102 - u2 * hm202
  · simp only [tightScaledEdgeOneTwo]
    linear_combination
      -(tight 1 * tight 2) * h12 - u0 * hm012 - u1 * hm112 - u2 * hm212

/-- Applying Parseval to the tight vector gives the three barycentric first
moment equations used by the conservation law. -/
theorem barycentricCoordinateMoments_eq_of_frame_of_kernel
    (form : Matrix (Fin 3) (Fin 3) ℝ) (tight : Fin 3 → ℝ)
    (freeAtom : Fin 3 → Fin 3 → ℝ)
    (u0 u1 u2 : ℝ) (baseWeight : Fin 3 → ℝ)
    (hframe : form
        + u0 • atomMatrix (freeAtom 0)
        + u1 • atomMatrix (freeAtom 1)
        + u2 • atomMatrix (freeAtom 2)
      = Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate))
    (hkernel : Matrix.mulVec form tight = 0)
    (hread0 : tightBarycentricReading tight (freeAtom 0) ≠ 0)
    (hread1 : tightBarycentricReading tight (freeAtom 1) ≠ 0)
    (hread2 : tightBarycentricReading tight (freeAtom 2) ≠ 0) :
    u0 * tightBarycentricReading tight (freeAtom 0) ^ 2
          * tightBarycentricCoordinate tight (freeAtom 0) 0
        + u1 * tightBarycentricReading tight (freeAtom 1) ^ 2
          * tightBarycentricCoordinate tight (freeAtom 1) 0
        + u2 * tightBarycentricReading tight (freeAtom 2) ^ 2
          * tightBarycentricCoordinate tight (freeAtom 2) 0
      = (1 - baseWeight 0) * tight 0 ^ 2
      ∧ u0 * tightBarycentricReading tight (freeAtom 0) ^ 2
          * tightBarycentricCoordinate tight (freeAtom 0) 1
        + u1 * tightBarycentricReading tight (freeAtom 1) ^ 2
          * tightBarycentricCoordinate tight (freeAtom 1) 1
        + u2 * tightBarycentricReading tight (freeAtom 2) ^ 2
          * tightBarycentricCoordinate tight (freeAtom 2) 1
      = (1 - baseWeight 1) * tight 1 ^ 2
      ∧ u0 * tightBarycentricReading tight (freeAtom 0) ^ 2
          * tightBarycentricCoordinate tight (freeAtom 0) 2
        + u1 * tightBarycentricReading tight (freeAtom 1) ^ 2
          * tightBarycentricCoordinate tight (freeAtom 1) 2
        + u2 * tightBarycentricReading tight (freeAtom 2) ^ 2
          * tightBarycentricCoordinate tight (freeAtom 2) 2
      = (1 - baseWeight 2) * tight 2 ^ 2 := by
  have hmul := congrArg (fun matrix => Matrix.mulVec matrix tight) hframe
  have hrow0 := congrFun hmul 0
  have hrow1 := congrFun hmul 1
  have hrow2 := congrFun hmul 2
  have hk0 := congrFun hkernel 0
  have hk1 := congrFun hkernel 1
  have hk2 := congrFun hkernel 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.diagonal_apply, atomMatrix, Matrix.vecMulVec_apply]
    at hrow0 hrow1 hrow2 hk0 hk1 hk2
  have hm00 := sq_tightBarycentricReading_mul_coordinate
    tight (freeAtom 0) 0 hread0
  have hm10 := sq_tightBarycentricReading_mul_coordinate
    tight (freeAtom 1) 0 hread1
  have hm20 := sq_tightBarycentricReading_mul_coordinate
    tight (freeAtom 2) 0 hread2
  have hm01 := sq_tightBarycentricReading_mul_coordinate
    tight (freeAtom 0) 1 hread0
  have hm11 := sq_tightBarycentricReading_mul_coordinate
    tight (freeAtom 1) 1 hread1
  have hm21 := sq_tightBarycentricReading_mul_coordinate
    tight (freeAtom 2) 1 hread2
  have hm02 := sq_tightBarycentricReading_mul_coordinate
    tight (freeAtom 0) 2 hread0
  have hm12 := sq_tightBarycentricReading_mul_coordinate
    tight (freeAtom 1) 2 hread1
  have hm22 := sq_tightBarycentricReading_mul_coordinate
    tight (freeAtom 2) 2 hread2
  simp only [tightBarycentricReading, dotProduct, Fin.sum_univ_three]
    at hm00 hm10 hm20 hm01 hm11 hm21 hm02 hm12 hm22 ⊢
  constructor
  · linear_combination
      tight 0 * (hrow0 - hk0) + u0 * hm00 + u1 * hm10 + u2 * hm20
  constructor
  · linear_combination
      tight 1 * (hrow1 - hk1) + u0 * hm01 + u1 * hm11 + u2 * hm21
  · linear_combination
      tight 2 * (hrow2 - hk2) + u0 * hm02 + u1 * hm12 + u2 * hm22

/-! ## Determinant bridge back to the hidden one-slot gaps -/

theorem diagonal_mulVec_eq_reading_smul_barycentricCoordinates
    (tight freeAtom : Fin 3 → ℝ)
    (hreading : tightBarycentricReading tight freeAtom ≠ 0) :
    Matrix.mulVec (Matrix.diagonal tight) freeAtom =
      tightBarycentricReading tight freeAtom •
        (fun coordinate =>
          tightBarycentricCoordinate tight freeAtom coordinate) := by
  ext coordinate
  rw [Matrix.mulVec_diagonal]
  simp only [Pi.smul_apply, smul_eq_mul, tightBarycentricCoordinate]
  field_simp [hreading]

theorem diagonal_mulVec_single_eq_smul_single
    (tight : Fin 3 → ℝ) (coordinate : Fin 3) :
    Matrix.mulVec (Matrix.diagonal tight) (Pi.single coordinate 1) =
      tight coordinate • Pi.single coordinate 1 := by
  rw [Matrix.diagonal_mulVec_single]
  ext row
  fin_cases coordinate <;> fin_cases row <;>
    simp

/-- Diagonal congruence turns an arbitrary one-slot update into a scaled
barycentric rank-one update.  No positivity is used. -/
theorem diagonal_congr_oneSlotGap_eq_barycentricUpdate
    (form : Matrix (Fin 3) (Fin 3) ℝ) (tight freeAtom : Fin 3 → ℝ)
    (omittedBase : Fin 3)
    (hreading : tightBarycentricReading tight freeAtom ≠ 0) :
    Matrix.diagonal tight
        * (form + atomMatrix freeAtom
            - atomMatrix (Pi.single omittedBase 1))
        * Matrix.diagonal tight
      = Matrix.diagonal tight * form * Matrix.diagonal tight
          + tightBarycentricReading tight freeAtom ^ 2 •
              atomMatrix (fun coordinate =>
                tightBarycentricCoordinate tight freeAtom coordinate)
          - tight omittedBase ^ 2 •
              atomMatrix (Pi.single omittedBase 1) := by
  let diagonal := Matrix.diagonal tight
  have hfreeConj :
      diagonal * atomMatrix freeAtom * diagonal =
        atomMatrix (Matrix.mulVec diagonal freeAtom) := by
    simpa [diagonal] using transpose_mul_atomMatrix_mul diagonal freeAtom
  have haxisConj :
      diagonal * atomMatrix (Pi.single omittedBase 1) * diagonal =
        atomMatrix (Matrix.mulVec diagonal (Pi.single omittedBase 1)) := by
    simpa [diagonal] using
      transpose_mul_atomMatrix_mul diagonal (Pi.single omittedBase 1)
  rw [diagonal_mulVec_eq_reading_smul_barycentricCoordinates
      tight freeAtom hreading,
    atomMatrix_smul] at hfreeConj
  rw [diagonal_mulVec_single_eq_smul_single tight omittedBase,
    atomMatrix_smul] at haxisConj
  change diagonal * (form + atomMatrix freeAtom
      - atomMatrix (Pi.single omittedBase 1)) * diagonal = _
  calc
    diagonal * (form + atomMatrix freeAtom
          - atomMatrix (Pi.single omittedBase 1)) * diagonal =
        diagonal * form * diagonal
          + diagonal * atomMatrix freeAtom * diagonal
          - diagonal * atomMatrix (Pi.single omittedBase 1) * diagonal := by
            noncomm_ring
    _ = _ := by rw [hfreeConj, haxisConj]

theorem tightBarycentricCoordinates_eq_finThreeVector
    (tight freeAtom : Fin 3 → ℝ)
    (hreading : tightBarycentricReading tight freeAtom ≠ 0) :
    (fun coordinate => tightBarycentricCoordinate tight freeAtom coordinate) =
      ![tightBarycentricCoordinate tight freeAtom 0,
        tightBarycentricCoordinate tight freeAtom 1,
        1 - tightBarycentricCoordinate tight freeAtom 0
          - tightBarycentricCoordinate tight freeAtom 1] := by
  have hsum := sum_tightBarycentricCoordinate_eq_one tight freeAtom hreading
  funext coordinate
  fin_cases coordinate <;> simp
  linarith

theorem det_diagonal_congr_eq_coordinateProduct_sq_mul
    (form : Matrix (Fin 3) (Fin 3) ℝ) (tight : Fin 3 → ℝ) :
    (Matrix.diagonal tight * form * Matrix.diagonal tight).det =
      (tight 0 * tight 1 * tight 2) ^ 2 * form.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Fin.prod_univ_three]
  ring

theorem det_diagonal_congr_oneSlot_zero_eq_barycentricOneSlotDet
    (form : Matrix (Fin 3) (Fin 3) ℝ) (tight freeAtom : Fin 3 → ℝ)
    (hsymmetric : Matrix.transpose form = form)
    (hkernel : Matrix.mulVec form tight = 0)
    (hreading : tightBarycentricReading tight freeAtom ≠ 0) :
    (Matrix.diagonal tight
        * (form + atomMatrix freeAtom - atomMatrix (Pi.single 0 1))
        * Matrix.diagonal tight).det =
      barycentricOneSlotDetZero
        (tightScaledEdgeZeroOne form tight)
        (tightScaledEdgeZeroTwo form tight)
        (tightScaledEdgeOneTwo form tight)
        (tight 0 ^ 2)
        (tightBarycentricReading tight freeAtom ^ 2)
        (tightBarycentricCoordinate tight freeAtom 0)
        (tightBarycentricCoordinate tight freeAtom 1) := by
  rw [diagonal_congr_oneSlotGap_eq_barycentricUpdate
      form tight freeAtom 0 hreading,
    diagonal_mul_form_mul_diagonal_eq_triangleLaplacian
      form tight hsymmetric hkernel,
    tightBarycentricCoordinates_eq_finThreeVector tight freeAtom hreading]
  have haxis : (Pi.single (0 : Fin 3) 1 : Fin 3 → ℝ) = ![1, 0, 0] := by
    funext coordinate
    fin_cases coordinate <;> simp
  rw [haxis]
  rw [show
      (!![tightScaledEdgeZeroOne form tight + tightScaledEdgeZeroTwo form tight,
            -tightScaledEdgeZeroOne form tight, -tightScaledEdgeZeroTwo form tight;
          -tightScaledEdgeZeroOne form tight,
            tightScaledEdgeZeroOne form tight + tightScaledEdgeOneTwo form tight,
            -tightScaledEdgeOneTwo form tight;
          -tightScaledEdgeZeroTwo form tight, -tightScaledEdgeOneTwo form tight,
            tightScaledEdgeZeroTwo form tight + tightScaledEdgeOneTwo form tight]
          + tightBarycentricReading tight freeAtom ^ 2 •
              atomMatrix
                (![tightBarycentricCoordinate tight freeAtom 0,
                  tightBarycentricCoordinate tight freeAtom 1,
                  1 - tightBarycentricCoordinate tight freeAtom 0
                    - tightBarycentricCoordinate tight freeAtom 1] : Fin 3 → ℝ)
          - tight 0 ^ 2 • atomMatrix (![1, 0, 0] : Fin 3 → ℝ)) =
        (!![tightScaledEdgeZeroOne form tight + tightScaledEdgeZeroTwo form tight,
            -tightScaledEdgeZeroOne form tight, -tightScaledEdgeZeroTwo form tight;
          -tightScaledEdgeZeroOne form tight,
            tightScaledEdgeZeroOne form tight + tightScaledEdgeOneTwo form tight,
            -tightScaledEdgeOneTwo form tight;
          -tightScaledEdgeZeroTwo form tight, -tightScaledEdgeOneTwo form tight,
            tightScaledEdgeZeroTwo form tight + tightScaledEdgeOneTwo form tight]
          - tight 0 ^ 2 • atomMatrix (![1, 0, 0] : Fin 3 → ℝ)
          + tightBarycentricReading tight freeAtom ^ 2 •
              atomMatrix
                (![tightBarycentricCoordinate tight freeAtom 0,
                  tightBarycentricCoordinate tight freeAtom 1,
                  1 - tightBarycentricCoordinate tight freeAtom 0
                    - tightBarycentricCoordinate tight freeAtom 1] : Fin 3 → ℝ)) by
      abel]
  exact det_triangleLaplacian_sub_axis_add_barycentricAtom
    (tightScaledEdgeZeroOne form tight)
    (tightScaledEdgeZeroTwo form tight)
    (tightScaledEdgeOneTwo form tight)
    (tight 0 ^ 2)
    (tightBarycentricReading tight freeAtom ^ 2)
    (tightBarycentricCoordinate tight freeAtom 0)
    (tightBarycentricCoordinate tight freeAtom 1)

theorem det_diagonal_congr_oneSlot_one_eq_barycentricOneSlotDet
    (form : Matrix (Fin 3) (Fin 3) ℝ) (tight freeAtom : Fin 3 → ℝ)
    (hsymmetric : Matrix.transpose form = form)
    (hkernel : Matrix.mulVec form tight = 0)
    (hreading : tightBarycentricReading tight freeAtom ≠ 0) :
    (Matrix.diagonal tight
        * (form + atomMatrix freeAtom - atomMatrix (Pi.single 1 1))
        * Matrix.diagonal tight).det =
      barycentricOneSlotDetOne
        (tightScaledEdgeZeroOne form tight)
        (tightScaledEdgeZeroTwo form tight)
        (tightScaledEdgeOneTwo form tight)
        (tight 1 ^ 2)
        (tightBarycentricReading tight freeAtom ^ 2)
        (tightBarycentricCoordinate tight freeAtom 0)
        (tightBarycentricCoordinate tight freeAtom 1) := by
  rw [diagonal_congr_oneSlotGap_eq_barycentricUpdate
      form tight freeAtom 1 hreading,
    diagonal_mul_form_mul_diagonal_eq_triangleLaplacian
      form tight hsymmetric hkernel,
    tightBarycentricCoordinates_eq_finThreeVector tight freeAtom hreading]
  have haxis : (Pi.single (1 : Fin 3) 1 : Fin 3 → ℝ) = ![0, 1, 0] := by
    funext coordinate
    fin_cases coordinate <;> simp
  rw [haxis]
  rw [show
      (!![tightScaledEdgeZeroOne form tight + tightScaledEdgeZeroTwo form tight,
            -tightScaledEdgeZeroOne form tight, -tightScaledEdgeZeroTwo form tight;
          -tightScaledEdgeZeroOne form tight,
            tightScaledEdgeZeroOne form tight + tightScaledEdgeOneTwo form tight,
            -tightScaledEdgeOneTwo form tight;
          -tightScaledEdgeZeroTwo form tight, -tightScaledEdgeOneTwo form tight,
            tightScaledEdgeZeroTwo form tight + tightScaledEdgeOneTwo form tight]
          + tightBarycentricReading tight freeAtom ^ 2 •
              atomMatrix
                (![tightBarycentricCoordinate tight freeAtom 0,
                  tightBarycentricCoordinate tight freeAtom 1,
                  1 - tightBarycentricCoordinate tight freeAtom 0
                    - tightBarycentricCoordinate tight freeAtom 1] : Fin 3 → ℝ)
          - tight 1 ^ 2 • atomMatrix (![0, 1, 0] : Fin 3 → ℝ)) =
        (!![tightScaledEdgeZeroOne form tight + tightScaledEdgeZeroTwo form tight,
            -tightScaledEdgeZeroOne form tight, -tightScaledEdgeZeroTwo form tight;
          -tightScaledEdgeZeroOne form tight,
            tightScaledEdgeZeroOne form tight + tightScaledEdgeOneTwo form tight,
            -tightScaledEdgeOneTwo form tight;
          -tightScaledEdgeZeroTwo form tight, -tightScaledEdgeOneTwo form tight,
            tightScaledEdgeZeroTwo form tight + tightScaledEdgeOneTwo form tight]
          - tight 1 ^ 2 • atomMatrix (![0, 1, 0] : Fin 3 → ℝ)
          + tightBarycentricReading tight freeAtom ^ 2 •
              atomMatrix
                (![tightBarycentricCoordinate tight freeAtom 0,
                  tightBarycentricCoordinate tight freeAtom 1,
                  1 - tightBarycentricCoordinate tight freeAtom 0
                    - tightBarycentricCoordinate tight freeAtom 1] : Fin 3 → ℝ)) by
      abel]
  exact det_triangleLaplacian_sub_axis_one_add_barycentricAtom
    (tightScaledEdgeZeroOne form tight)
    (tightScaledEdgeZeroTwo form tight)
    (tightScaledEdgeOneTwo form tight)
    (tight 1 ^ 2)
    (tightBarycentricReading tight freeAtom ^ 2)
    (tightBarycentricCoordinate tight freeAtom 0)
    (tightBarycentricCoordinate tight freeAtom 1)

theorem det_diagonal_congr_oneSlot_two_eq_barycentricOneSlotDet
    (form : Matrix (Fin 3) (Fin 3) ℝ) (tight freeAtom : Fin 3 → ℝ)
    (hsymmetric : Matrix.transpose form = form)
    (hkernel : Matrix.mulVec form tight = 0)
    (hreading : tightBarycentricReading tight freeAtom ≠ 0) :
    (Matrix.diagonal tight
        * (form + atomMatrix freeAtom - atomMatrix (Pi.single 2 1))
        * Matrix.diagonal tight).det =
      barycentricOneSlotDetTwo
        (tightScaledEdgeZeroOne form tight)
        (tightScaledEdgeZeroTwo form tight)
        (tightScaledEdgeOneTwo form tight)
        (tight 2 ^ 2)
        (tightBarycentricReading tight freeAtom ^ 2)
        (tightBarycentricCoordinate tight freeAtom 0)
        (tightBarycentricCoordinate tight freeAtom 1) := by
  rw [diagonal_congr_oneSlotGap_eq_barycentricUpdate
      form tight freeAtom 2 hreading,
    diagonal_mul_form_mul_diagonal_eq_triangleLaplacian
      form tight hsymmetric hkernel,
    tightBarycentricCoordinates_eq_finThreeVector tight freeAtom hreading]
  have haxis : (Pi.single (2 : Fin 3) 1 : Fin 3 → ℝ) = ![0, 0, 1] := by
    funext coordinate
    fin_cases coordinate <;> simp
  rw [haxis]
  rw [show
      (!![tightScaledEdgeZeroOne form tight + tightScaledEdgeZeroTwo form tight,
            -tightScaledEdgeZeroOne form tight, -tightScaledEdgeZeroTwo form tight;
          -tightScaledEdgeZeroOne form tight,
            tightScaledEdgeZeroOne form tight + tightScaledEdgeOneTwo form tight,
            -tightScaledEdgeOneTwo form tight;
          -tightScaledEdgeZeroTwo form tight, -tightScaledEdgeOneTwo form tight,
            tightScaledEdgeZeroTwo form tight + tightScaledEdgeOneTwo form tight]
          + tightBarycentricReading tight freeAtom ^ 2 •
              atomMatrix
                (![tightBarycentricCoordinate tight freeAtom 0,
                  tightBarycentricCoordinate tight freeAtom 1,
                  1 - tightBarycentricCoordinate tight freeAtom 0
                    - tightBarycentricCoordinate tight freeAtom 1] : Fin 3 → ℝ)
          - tight 2 ^ 2 • atomMatrix (![0, 0, 1] : Fin 3 → ℝ)) =
        (!![tightScaledEdgeZeroOne form tight + tightScaledEdgeZeroTwo form tight,
            -tightScaledEdgeZeroOne form tight, -tightScaledEdgeZeroTwo form tight;
          -tightScaledEdgeZeroOne form tight,
            tightScaledEdgeZeroOne form tight + tightScaledEdgeOneTwo form tight,
            -tightScaledEdgeOneTwo form tight;
          -tightScaledEdgeZeroTwo form tight, -tightScaledEdgeOneTwo form tight,
            tightScaledEdgeZeroTwo form tight + tightScaledEdgeOneTwo form tight]
          - tight 2 ^ 2 • atomMatrix (![0, 0, 1] : Fin 3 → ℝ)
          + tightBarycentricReading tight freeAtom ^ 2 •
              atomMatrix
                (![tightBarycentricCoordinate tight freeAtom 0,
                  tightBarycentricCoordinate tight freeAtom 1,
                  1 - tightBarycentricCoordinate tight freeAtom 0
                    - tightBarycentricCoordinate tight freeAtom 1] : Fin 3 → ℝ)) by
      abel]
  exact det_triangleLaplacian_sub_axis_two_add_barycentricAtom
    (tightScaledEdgeZeroOne form tight)
    (tightScaledEdgeZeroTwo form tight)
    (tightScaledEdgeOneTwo form tight)
    (tight 2 ^ 2)
    (tightBarycentricReading tight freeAtom ^ 2)
    (tightBarycentricCoordinate tight freeAtom 0)
    (tightBarycentricCoordinate tight freeAtom 1)

/-- **MATRIX-LEVEL OPEN-CELL HINGE.**  Parseval, positive weights and a
nondegenerate free frame force one of the nine one-slot hidden gaps to have
positive determinant throughout the open barycentric cell. -/
theorem exists_hiddenOneSlotGap_det_pos_of_tightBarycentricOpenCell
    (form : Matrix (Fin 3) (Fin 3) ℝ) (tight : Fin 3 → ℝ)
    (freeAtom : Fin 3 → Fin 3 → ℝ)
    (u0 u1 u2 : ℝ) (baseWeight : Fin 3 → ℝ)
    (hsymmetric : Matrix.transpose form = form)
    (hkernel : Matrix.mulVec form tight = 0)
    (hframe : form
        + u0 • atomMatrix (freeAtom 0)
        + u1 • atomMatrix (freeAtom 1)
        + u2 • atomMatrix (freeAtom 2)
      = Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate))
    (hweight : baseWeight 0 + baseWeight 1 + baseWeight 2
        + u0 + u1 + u2 = 1)
    (hu0 : 0 < u0) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hopen : TightBarycentricOpenCell tight freeAtom)
    (hbracket : tripleBracket (freeAtom 0) (freeAtom 1) (freeAtom 2) ≠ 0) :
    ∃ omittedBase freeIndex : Fin 3,
      0 < (unitAxisHiddenOneSlotGap form freeAtom omittedBase freeIndex).det := by
  have hread0 := tightBarycentricReading_ne_zero_of_openCell
    tight freeAtom hopen 0
  have hread1 := tightBarycentricReading_ne_zero_of_openCell
    tight freeAtom hopen 1
  have hread2 := tightBarycentricReading_ne_zero_of_openCell
    tight freeAtom hopen 2
  have htight0 := tight_coordinate_ne_zero_of_openCell tight freeAtom hopen 0
  have htight1 := tight_coordinate_ne_zero_of_openCell tight freeAtom hopen 1
  have htight2 := tight_coordinate_ne_zero_of_openCell tight freeAtom hopen 2
  have hedges := tightScaledEdges_eq_barycentricMoments_of_frame
    form tight freeAtom u0 u1 u2 baseWeight hframe hread0 hread1 hread2
  have hcoordinates := barycentricCoordinateMoments_eq_of_frame_of_kernel
    form tight freeAtom u0 u1 u2 baseWeight hframe hkernel
      hread0 hread1 hread2
  have hsum0 := sum_tightBarycentricCoordinate_eq_one
    tight (freeAtom 0) hread0
  have hsum1 := sum_tightBarycentricCoordinate_eq_one
    tight (freeAtom 1) hread1
  have hsum2 := sum_tightBarycentricCoordinate_eq_one
    tight (freeAtom 2) hread2
  have hq0two : tightBarycentricCoordinate tight (freeAtom 0) 2 =
      1 - tightBarycentricCoordinate tight (freeAtom 0) 0
        - tightBarycentricCoordinate tight (freeAtom 0) 1 := by
    linarith
  have hq1two : tightBarycentricCoordinate tight (freeAtom 1) 2 =
      1 - tightBarycentricCoordinate tight (freeAtom 1) 0
        - tightBarycentricCoordinate tight (freeAtom 1) 1 := by
    linarith
  have hq2two : tightBarycentricCoordinate tight (freeAtom 2) 2 =
      1 - tightBarycentricCoordinate tight (freeAtom 2) 0
        - tightBarycentricCoordinate tight (freeAtom 2) 1 := by
    linarith
  have hedge02 := hedges.2.1
  have hedge12 := hedges.2.2
  have hcoordinate2 := hcoordinates.2.2
  rw [hq0two, hq1two, hq2two] at hedge02 hedge12 hcoordinate2
  have hz0 : 0 < 1 - tightBarycentricCoordinate tight (freeAtom 0) 0
      - tightBarycentricCoordinate tight (freeAtom 0) 1 := by
    have := hopen 0 2
    linarith
  have hz1 : 0 < 1 - tightBarycentricCoordinate tight (freeAtom 1) 0
      - tightBarycentricCoordinate tight (freeAtom 1) 1 := by
    have := hopen 1 2
    linarith
  have hz2 : 0 < 1 - tightBarycentricCoordinate tight (freeAtom 2) 0
      - tightBarycentricCoordinate tight (freeAtom 2) 1 := by
    have := hopen 2 2
    linarith
  have hdistinct :=
    not_all_tightBarycentricPoints_equal_of_tripleBracket_ne_zero
      tight freeAtom hopen hbracket
  have hscalar := exists_positive_barycentricOneSlotDet_of_not_all_points_equal
    (tightScaledEdgeZeroOne form tight)
    (tightScaledEdgeZeroTwo form tight)
    (tightScaledEdgeOneTwo form tight)
    (tight 0 ^ 2) (tight 1 ^ 2) (tight 2 ^ 2)
    (baseWeight 0) (baseWeight 1) (baseWeight 2)
    u0 u1 u2
    (tightBarycentricReading tight (freeAtom 0) ^ 2)
    (tightBarycentricReading tight (freeAtom 1) ^ 2)
    (tightBarycentricReading tight (freeAtom 2) ^ 2)
    (tightBarycentricCoordinate tight (freeAtom 0) 0)
    (tightBarycentricCoordinate tight (freeAtom 0) 1)
    (tightBarycentricCoordinate tight (freeAtom 1) 0)
    (tightBarycentricCoordinate tight (freeAtom 1) 1)
    (tightBarycentricCoordinate tight (freeAtom 2) 0)
    (tightBarycentricCoordinate tight (freeAtom 2) 1)
    hedges.1 hedge02 hedge12
    hcoordinates.1 hcoordinates.2.1 hcoordinate2 hweight
    (sq_pos_of_ne_zero htight0) (sq_pos_of_ne_zero htight1)
    (sq_pos_of_ne_zero htight2) hu0 hu1 hu2
    (sq_pos_of_ne_zero hread0) (sq_pos_of_ne_zero hread1)
    (sq_pos_of_ne_zero hread2)
    (hopen 0 0) (hopen 0 1) hz0
    (hopen 1 0) (hopen 1 1) hz1
    (hopen 2 0) (hopen 2 1) hz2 hdistinct
  have hscalePos : 0 < (tight 0 * tight 1 * tight 2) ^ 2 :=
    sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero htight0 htight1) htight2)
  have hzero : ∀ freeIndex : Fin 3,
      0 < barycentricOneSlotDetZero
          (tightScaledEdgeZeroOne form tight)
          (tightScaledEdgeZeroTwo form tight)
          (tightScaledEdgeOneTwo form tight)
          (tight 0 ^ 2)
          (tightBarycentricReading tight (freeAtom freeIndex) ^ 2)
          (tightBarycentricCoordinate tight (freeAtom freeIndex) 0)
          (tightBarycentricCoordinate tight (freeAtom freeIndex) 1) →
        0 < (unitAxisHiddenOneSlotGap form freeAtom 0 freeIndex).det := by
    intro freeIndex hpositive
    have hread := tightBarycentricReading_ne_zero_of_openCell
      tight freeAtom hopen freeIndex
    have hpoly := det_diagonal_congr_oneSlot_zero_eq_barycentricOneSlotDet
      form tight (freeAtom freeIndex) hsymmetric hkernel hread
    have hscale := det_diagonal_congr_eq_coordinateProduct_sq_mul
      (unitAxisHiddenOneSlotGap form freeAtom 0 freeIndex) tight
    have heq :
        (tight 0 * tight 1 * tight 2) ^ 2
            * (unitAxisHiddenOneSlotGap form freeAtom 0 freeIndex).det =
          barycentricOneSlotDetZero
            (tightScaledEdgeZeroOne form tight)
            (tightScaledEdgeZeroTwo form tight)
            (tightScaledEdgeOneTwo form tight)
            (tight 0 ^ 2)
            (tightBarycentricReading tight (freeAtom freeIndex) ^ 2)
            (tightBarycentricCoordinate tight (freeAtom freeIndex) 0)
            (tightBarycentricCoordinate tight (freeAtom freeIndex) 1) := by
      rw [← hpoly, ← hscale]
      rfl
    nlinarith
  have hone : ∀ freeIndex : Fin 3,
      0 < barycentricOneSlotDetOne
          (tightScaledEdgeZeroOne form tight)
          (tightScaledEdgeZeroTwo form tight)
          (tightScaledEdgeOneTwo form tight)
          (tight 1 ^ 2)
          (tightBarycentricReading tight (freeAtom freeIndex) ^ 2)
          (tightBarycentricCoordinate tight (freeAtom freeIndex) 0)
          (tightBarycentricCoordinate tight (freeAtom freeIndex) 1) →
        0 < (unitAxisHiddenOneSlotGap form freeAtom 1 freeIndex).det := by
    intro freeIndex hpositive
    have hread := tightBarycentricReading_ne_zero_of_openCell
      tight freeAtom hopen freeIndex
    have hpoly := det_diagonal_congr_oneSlot_one_eq_barycentricOneSlotDet
      form tight (freeAtom freeIndex) hsymmetric hkernel hread
    have hscale := det_diagonal_congr_eq_coordinateProduct_sq_mul
      (unitAxisHiddenOneSlotGap form freeAtom 1 freeIndex) tight
    have heq :
        (tight 0 * tight 1 * tight 2) ^ 2
            * (unitAxisHiddenOneSlotGap form freeAtom 1 freeIndex).det =
          barycentricOneSlotDetOne
            (tightScaledEdgeZeroOne form tight)
            (tightScaledEdgeZeroTwo form tight)
            (tightScaledEdgeOneTwo form tight)
            (tight 1 ^ 2)
            (tightBarycentricReading tight (freeAtom freeIndex) ^ 2)
            (tightBarycentricCoordinate tight (freeAtom freeIndex) 0)
            (tightBarycentricCoordinate tight (freeAtom freeIndex) 1) := by
      rw [← hpoly, ← hscale]
      rfl
    nlinarith
  have htwo : ∀ freeIndex : Fin 3,
      0 < barycentricOneSlotDetTwo
          (tightScaledEdgeZeroOne form tight)
          (tightScaledEdgeZeroTwo form tight)
          (tightScaledEdgeOneTwo form tight)
          (tight 2 ^ 2)
          (tightBarycentricReading tight (freeAtom freeIndex) ^ 2)
          (tightBarycentricCoordinate tight (freeAtom freeIndex) 0)
          (tightBarycentricCoordinate tight (freeAtom freeIndex) 1) →
        0 < (unitAxisHiddenOneSlotGap form freeAtom 2 freeIndex).det := by
    intro freeIndex hpositive
    have hread := tightBarycentricReading_ne_zero_of_openCell
      tight freeAtom hopen freeIndex
    have hpoly := det_diagonal_congr_oneSlot_two_eq_barycentricOneSlotDet
      form tight (freeAtom freeIndex) hsymmetric hkernel hread
    have hscale := det_diagonal_congr_eq_coordinateProduct_sq_mul
      (unitAxisHiddenOneSlotGap form freeAtom 2 freeIndex) tight
    have heq :
        (tight 0 * tight 1 * tight 2) ^ 2
            * (unitAxisHiddenOneSlotGap form freeAtom 2 freeIndex).det =
          barycentricOneSlotDetTwo
            (tightScaledEdgeZeroOne form tight)
            (tightScaledEdgeZeroTwo form tight)
            (tightScaledEdgeOneTwo form tight)
            (tight 2 ^ 2)
            (tightBarycentricReading tight (freeAtom freeIndex) ^ 2)
            (tightBarycentricCoordinate tight (freeAtom freeIndex) 0)
            (tightBarycentricCoordinate tight (freeAtom freeIndex) 1) := by
      rw [← hpoly, ← hscale]
      rfl
    nlinarith
  rcases hscalar with h00 | h10 | h20 | h01 | h11 | h21 | h02 | h12 | h22
  · exact ⟨0, 0, hzero 0 h00⟩
  · exact ⟨1, 0, hone 0 h10⟩
  · exact ⟨2, 0, htwo 0 h20⟩
  · exact ⟨0, 1, hzero 1 h01⟩
  · exact ⟨1, 1, hone 1 h11⟩
  · exact ⟨2, 1, htwo 1 h21⟩
  · exact ⟨0, 2, hzero 2 h02⟩
  · exact ⟨1, 2, hone 2 h12⟩
  · exact ⟨2, 2, htwo 2 h22⟩

/-- **DESIGN-LEVEL OPEN-CELL TIGHT-LINE HINGE.**  On the sign-coherent
barycentric cell, every line-free tight-line antecedent already has a strict
card-three subset.  Off-conicity is not needed on this cell. -/
theorem exists_posDef_cardThree_of_tightLine_of_barycentricOpenCell
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hline : HasTightLineAt design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hopen : TightBarycentricOpenCell
      (unitAxisTightVector design tightDir) (unitAxisFreeAtom design)) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  have hweight := design.weight_sum_one
  rw [Fin.sum_univ_six] at hweight
  have hweightSix :
      design.weight (baseThreeLabel 0)
          + design.weight (baseThreeLabel 1)
          + design.weight (baseThreeLabel 2)
          + design.weight 3 + design.weight 4 + design.weight 5 = 1 := by
    simpa [baseThreeLabel] using hweight
  have hbracket :
      tripleBracket (unitAxisFreeAtom design 0)
          (unitAxisFreeAtom design 1) (unitAxisFreeAtom design 2) ≠ 0 := by
    simpa [unitAxisFreeFrame, tripleBracket] using
      unitAxisFreeFrame_det_ne_zero design hlineFree
  obtain ⟨omittedBase, freeIndex, hdet⟩ :=
    exists_hiddenOneSlotGap_det_pos_of_tightBarycentricOpenCell
      (unitAxisHiddenForm design) (unitAxisTightVector design tightDir)
      (unitAxisFreeAtom design)
      (design.weight 3) (design.weight 4) (design.weight 5)
      (fun coordinate => design.weight (baseThreeLabel coordinate))
      (unitAxisHiddenForm_transpose design)
      (unitAxisHiddenForm_mulVec_tightVector_eq_zero
        design hlineFree hdominates htight)
      (unitAxisFiveVectorIdentity design hlineFree)
      hweightSix (design.weight_pos 3) (design.weight_pos 4)
      (design.weight_pos 5) hopen hbracket
  have homitted : unitAxisTightVector design tightDir omittedBase ≠ 0 :=
    tight_coordinate_ne_zero_of_openCell
      (unitAxisTightVector design tightDir) (unitAxisFreeAtom design)
      hopen omittedBase
  have hposDef :
      (unitAxisHiddenOneSlotGap (unitAxisHiddenForm design)
        (unitAxisFreeAtom design) omittedBase freeIndex).PosDef :=
    (unitAxisHiddenOneSlotGap_posDef_iff_det_pos_of_tightCoordinate_ne_zero
      design hlineFree hdominates htight hline omittedBase freeIndex
      homitted).mpr hdet
  apply (exists_posDef_cardThree_iff_unitAxisHiddenNineteenCandidate
    design tightDir hlineFree htightNe htight).mpr
  exact Or.inl ⟨omittedBase, freeIndex, hposDef⟩

/-! ## A sign-free selector outside the open cell -/

/-- The contribution of one barycentric free point to the determinant
conservation law.  Unlike the open-cell argument above, this quantity is useful
when the barycentric coordinates have mixed signs. -/
def barycentricSelectorContribution
    (edge01 edge02 edge12 s0 s1 s2 rho x y : ℝ) : ℝ :=
  x * s1 * s2
      * barycentricOneSlotDetZero edge01 edge02 edge12 s0 rho x y
    + y * s0 * s2
      * barycentricOneSlotDetOne edge01 edge02 edge12 s1 rho x y
    + (1 - x - y) * s0 * s1
      * barycentricOneSlotDetTwo edge01 edge02 edge12 s2 rho x y

/-- The quadratic energy which remains after the three one-slot energies are
combined barycentrically. -/
def barycentricSelectorEnergy
    (edge01 edge02 edge12 x y : ℝ) : ℝ :=
  edge01 * (1 - x - y) * (x + y)
    + edge02 * y * (1 - y)
    + edge12 * x * (1 - x)

/-- **CLOSED FORM FOR THE MIXED-SIGN SELECTOR.**  The seemingly cubic weighted
sum of the three one-slot determinants is affine in the squared tight reading
`rho`.  This is the exact scalar tested by the max-S census. -/
theorem barycentricSelectorContribution_eq_affine
    (edge01 edge02 edge12 s0 s1 s2 rho x y : ℝ) :
    barycentricSelectorContribution edge01 edge02 edge12 s0 s1 s2 rho x y
      = rho *
          (triangleLaplacianCofactor edge01 edge02 edge12
              * (x * s1 * s2 + y * s0 * s2
                  + (1 - x - y) * s0 * s1)
            - s0 * s1 * s2
                * barycentricSelectorEnergy edge01 edge02 edge12 x y)
        - triangleLaplacianCofactor edge01 edge02 edge12 * s0 * s1 * s2 := by
  simp only [barycentricSelectorContribution, barycentricOneSlotDetZero,
    barycentricOneSlotDetOne, barycentricOneSlotDetTwo,
    barycentricEnergyZero, barycentricEnergyOne, barycentricEnergyTwo,
    barycentricSelectorEnergy]
  ring

/-- Three positive coefficients whose weighted sum is zero cannot multiply
three strictly negative values. -/
theorem exists_nonnegative_of_positive_weighted_sum_three
    {u0 u1 u2 value0 value1 value2 : ℝ}
    (hu0 : 0 < u0) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hsum : u0 * value0 + u1 * value1 + u2 * value2 = 0) :
    0 ≤ value0 ∨ 0 ≤ value1 ∨ 0 ≤ value2 := by
  by_contra hnone
  simp only [not_or, not_le] at hnone
  have hzero : u0 * value0 < 0 := mul_neg_of_pos_of_neg hu0 hnone.1
  have hone : u1 * value1 < 0 := mul_neg_of_pos_of_neg hu1 hnone.2.1
  have htwo : u2 * value2 < 0 := mul_neg_of_pos_of_neg hu2 hnone.2.2
  linarith

/-- **THE SIGN-FREE BARYCENTRIC SELECTOR.**  Under the exact Parseval moment
and weight equations, one of the three free points has nonnegative selector
contribution.  No sign assumption on its barycentric coordinates is made.

On the positive open cell the earlier rigidity theorem spends this fact by
forcing a one-slot winner.  Outside that cell it is the finite mixed-sign
handoff: a hypothetical failure must place a nonnegative selected point in one
of the six nonzero sign wedges (or on a zero-coordinate face). -/
theorem exists_nonnegative_barycentricSelectorContribution
    (edge01 edge02 edge12 : ℝ)
    (s0 s1 s2 b0 b1 b2 : ℝ)
    (u0 u1 u2 rho0 rho1 rho2 : ℝ)
    (x0 y0 x1 y1 x2 y2 : ℝ)
    (hedge01 : edge01 =
      u0 * rho0 * x0 * y0 + u1 * rho1 * x1 * y1 + u2 * rho2 * x2 * y2)
    (hedge02 : edge02 =
      u0 * rho0 * x0 * (1 - x0 - y0)
        + u1 * rho1 * x1 * (1 - x1 - y1)
        + u2 * rho2 * x2 * (1 - x2 - y2))
    (hedge12 : edge12 =
      u0 * rho0 * y0 * (1 - x0 - y0)
        + u1 * rho1 * y1 * (1 - x1 - y1)
        + u2 * rho2 * y2 * (1 - x2 - y2))
    (hcoord0 :
      u0 * rho0 * x0 + u1 * rho1 * x1 + u2 * rho2 * x2 = (1 - b0) * s0)
    (hcoord1 :
      u0 * rho0 * y0 + u1 * rho1 * y1 + u2 * rho2 * y2 = (1 - b1) * s1)
    (hcoord2 :
      u0 * rho0 * (1 - x0 - y0) + u1 * rho1 * (1 - x1 - y1)
          + u2 * rho2 * (1 - x2 - y2) = (1 - b2) * s2)
    (hweight : b0 + b1 + b2 + u0 + u1 + u2 = 1)
    (hu0 : 0 < u0) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    0 ≤ barycentricSelectorContribution
          edge01 edge02 edge12 s0 s1 s2 rho0 x0 y0
      ∨ 0 ≤ barycentricSelectorContribution
          edge01 edge02 edge12 s0 s1 s2 rho1 x1 y1
      ∨ 0 ≤ barycentricSelectorContribution
          edge01 edge02 edge12 s0 s1 s2 rho2 x2 y2 := by
  have hsum := barycentricOneSlot_weighted_det_sum_eq_zero
    edge01 edge02 edge12 s0 s1 s2 b0 b1 b2 u0 u1 u2 rho0 rho1 rho2
    x0 y0 x1 y1 x2 y2 hedge01 hedge02 hedge12 hcoord0 hcoord1 hcoord2 hweight
  apply exists_nonnegative_of_positive_weighted_sum_three hu0 hu1 hu2
  simpa only [barycentricSelectorContribution] using hsum

/-- The sign-free selector contribution in the transported tight-line design
coordinates. -/
noncomputable def tightLineBarycentricSelectorContribution
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ)
    (freeIndex : Fin 3) : ℝ :=
  let tight := unitAxisTightVector design tightDir
  let form := unitAxisHiddenForm design
  let freeAtom := unitAxisFreeAtom design
  barycentricSelectorContribution
    (tightScaledEdgeZeroOne form tight)
    (tightScaledEdgeZeroTwo form tight)
    (tightScaledEdgeOneTwo form tight)
    (tight 0 ^ 2) (tight 1 ^ 2) (tight 2 ^ 2)
    (tightBarycentricReading tight (freeAtom freeIndex) ^ 2)
    (tightBarycentricCoordinate tight (freeAtom freeIndex) 0)
    (tightBarycentricCoordinate tight (freeAtom freeIndex) 1)

/-- **DESIGN-LEVEL SIGN-FREE SELECTOR.**  If none of the three free atoms is
blind to the tight direction, Parseval selects one free atom with nonnegative
barycentric contribution.  No coordinate sign and no openness hypothesis is
used. -/
theorem exists_nonnegative_tightLineBarycentricSelectorContribution
    (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htight : IsTightDirectionOf design
      ({0, 1, 2} : Finset (Fin 6)) tightDir)
    (hreading : ∀ freeIndex : Fin 3,
      tightBarycentricReading (unitAxisTightVector design tightDir)
          (unitAxisFreeAtom design freeIndex) ≠ 0) :
    ∃ freeIndex : Fin 3,
      0 ≤ tightLineBarycentricSelectorContribution design tightDir freeIndex := by
  let tight := unitAxisTightVector design tightDir
  let form := unitAxisHiddenForm design
  let freeAtom := unitAxisFreeAtom design
  have hframe := unitAxisFiveVectorIdentity design hlineFree
  have hkernel : Matrix.mulVec form tight = 0 := by
    exact unitAxisHiddenForm_mulVec_tightVector_eq_zero
      design hlineFree hdominates htight
  have hread0 : tightBarycentricReading tight (freeAtom 0) ≠ 0 := hreading 0
  have hread1 : tightBarycentricReading tight (freeAtom 1) ≠ 0 := hreading 1
  have hread2 : tightBarycentricReading tight (freeAtom 2) ≠ 0 := hreading 2
  have hedges := tightScaledEdges_eq_barycentricMoments_of_frame
    form tight freeAtom (design.weight 3) (design.weight 4) (design.weight 5)
    (fun coordinate => design.weight (baseThreeLabel coordinate))
    hframe hread0 hread1 hread2
  have hcoordinates := barycentricCoordinateMoments_eq_of_frame_of_kernel
    form tight freeAtom (design.weight 3) (design.weight 4) (design.weight 5)
    (fun coordinate => design.weight (baseThreeLabel coordinate))
    hframe hkernel hread0 hread1 hread2
  have hsum0 := sum_tightBarycentricCoordinate_eq_one
    tight (freeAtom 0) hread0
  have hsum1 := sum_tightBarycentricCoordinate_eq_one
    tight (freeAtom 1) hread1
  have hsum2 := sum_tightBarycentricCoordinate_eq_one
    tight (freeAtom 2) hread2
  have hq0two : tightBarycentricCoordinate tight (freeAtom 0) 2 =
      1 - tightBarycentricCoordinate tight (freeAtom 0) 0
        - tightBarycentricCoordinate tight (freeAtom 0) 1 := by
    linarith
  have hq1two : tightBarycentricCoordinate tight (freeAtom 1) 2 =
      1 - tightBarycentricCoordinate tight (freeAtom 1) 0
        - tightBarycentricCoordinate tight (freeAtom 1) 1 := by
    linarith
  have hq2two : tightBarycentricCoordinate tight (freeAtom 2) 2 =
      1 - tightBarycentricCoordinate tight (freeAtom 2) 0
        - tightBarycentricCoordinate tight (freeAtom 2) 1 := by
    linarith
  have hedge02 := hedges.2.1
  have hedge12 := hedges.2.2
  have hcoordinate2 := hcoordinates.2.2
  rw [hq0two, hq1two, hq2two] at hedge02 hedge12 hcoordinate2
  have hweight := design.weight_sum_one
  rw [Fin.sum_univ_six] at hweight
  have hweightSix :
      design.weight (baseThreeLabel 0)
          + design.weight (baseThreeLabel 1)
          + design.weight (baseThreeLabel 2)
          + design.weight 3 + design.weight 4 + design.weight 5 = 1 := by
    simpa [baseThreeLabel] using hweight
  have hselector := exists_nonnegative_barycentricSelectorContribution
    (tightScaledEdgeZeroOne form tight)
    (tightScaledEdgeZeroTwo form tight)
    (tightScaledEdgeOneTwo form tight)
    (tight 0 ^ 2) (tight 1 ^ 2) (tight 2 ^ 2)
    (design.weight (baseThreeLabel 0))
    (design.weight (baseThreeLabel 1))
    (design.weight (baseThreeLabel 2))
    (design.weight 3) (design.weight 4) (design.weight 5)
    (tightBarycentricReading tight (freeAtom 0) ^ 2)
    (tightBarycentricReading tight (freeAtom 1) ^ 2)
    (tightBarycentricReading tight (freeAtom 2) ^ 2)
    (tightBarycentricCoordinate tight (freeAtom 0) 0)
    (tightBarycentricCoordinate tight (freeAtom 0) 1)
    (tightBarycentricCoordinate tight (freeAtom 1) 0)
    (tightBarycentricCoordinate tight (freeAtom 1) 1)
    (tightBarycentricCoordinate tight (freeAtom 2) 0)
    (tightBarycentricCoordinate tight (freeAtom 2) 1)
    hedges.1 hedge02 hedge12 hcoordinates.1 hcoordinates.2.1 hcoordinate2
    hweightSix (design.weight_pos 3) (design.weight_pos 4) (design.weight_pos 5)
  rcases hselector with hzero | hone | htwo
  · exact ⟨0, hzero⟩
  · exact ⟨1, hone⟩
  · exact ⟨2, htwo⟩

end Gtz
