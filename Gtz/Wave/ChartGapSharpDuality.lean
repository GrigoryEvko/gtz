/-
# The chart gap is invertible, and the sharp dual is `-N M⁻¹ N`

`Gtz/Wave/ChartQuadraticCore.lean` presents a design as one symmetric matrix
`M = P - diag t` and one quadratic equation.  This module gives that matrix its
inverse and reads the campaign's sharp duality off it in one line.

## The gap is invertible, and the reason is the pair mass

The whole of the inertia statement the campaign needs is one identity:

    **`x ⬝ M x = |P x|² - Σ_c t_c x_c²`**   (`Gtz.quadForm_chartGapOfDesign`)

because `P` is a symmetric idempotent.  A null vector of `M` satisfies `P x = T x`,
so the first term is `Σ_c t_c² x_c²` while the whole expression vanishes, and

    `Σ_c t_c (1 - t_c) x_c² = 0` .

Every coefficient is strictly positive once the design has two atoms, so `x = 0`
(`Gtz.chartGapOfDesign_mulVec_eq_zero`).  The obstruction is exactly the campaign's
universal pair mass `t_c(1 - t_c)`: it vanishes at a vertex of the simplex, which is
the one place the argument — and the whole duality below — has nothing to stand on.

## The inverse is Woodbury, and its diagonal is the co-atom reading

Write `V` for the scaled frame (rows `√t_c g_c`), `W` for the inverse-scaled frame
(rows `g_c / √t_c`), and `G = S_all - 1` for the total gap.  Then

    **`M⁻¹ = W G⁻¹ Wᵀ - diag(1/t)`**   (`Gtz.chartGapOfDesign_inv_eq`)

which is one four-term product using only `Vᵀ W = G + 1`, `T W = V` and `Vᵀ T⁻¹ = Wᵀ`.
Reading it on the diagonal gives

    **`t_c · (M⁻¹)_cc = ρ_c - 1`**   (`Gtz.weight_mul_chartGapInverse_diag`)

with `ρ_c` the co-atom reading of `Gtz/Wave/SharpFiveSetCriterion.lean`.  Three
readings follow with nothing further computed.

* `(M⁻¹)_cc < 0` at every `c` ⟺ every co-atom set dominates STRICTLY.  At `(6,3)`
  that is "every five-set dominates strictly", one of the two hypotheses of the
  open stratum.
* `M_cc > 0` at every `c` ⟺ the design is ALL-HEAVY, the other hypothesis.  So the
  residual `(6,3)` stratum is a sign condition on the diagonal of `M` and a sign
  condition on the diagonal of `M⁻¹`.
* `(M⁻¹)_cc = 0` at every `c` ⟺ the design is an exact TIE, at the corank-one cell
  `(k+1, k)` (`Gtz.isTie_iff_chartGapInverse_diag_eq_zero`).  The corank-one
  stratum classified by `Gtz.isTie_iff_leverage_law` is therefore precisely the
  EQUALITY BOUNDARY of the first reading, and the proof here is one line of the
  landed reading budget rather than a second derivation of that law.

## The duality

With `N := diag(√(t_c(1 - t_c)))`,

    **`-(N M⁻¹ N) = 1 - diag t - Π`**   (`Gtz.chartGapOfDesign_sharpDual_eq`)

where `Π = Gtz.totalGapHat` is the hat matrix of the co-weighted frame.  The proof
is the inverse formula and two diagonal identities: `N T⁻¹ N = 1 - T` and
`N W = Gtz.totalGapFrame`.  By the landed `Gtz.totalGapHat_add_sharpHat` the right
side is `Gtz.sharpHat - diag t`, that is the chart gap of the SHARP design of
`Gtz/Wave/NaimarkSharpDesign.lean`.  So the sharp duality — the one that DOES
transport domination — is a conjugation by a positive diagonal composed with matrix
inversion and a sign.

Two properties are then free and abstract, stated for any invertible symmetric form
and any positive diagonal:

* `Gtz.negConjInv_negConjInv` — the map is an INVOLUTION.
* `Gtz.negConjInv_ne_self_of_diagonal_pos` — it has NO FIXED POINT, at any size and
  any cell.  A fixed point forces `M N⁻¹ M = -N`, whose left side has a nonnegative
  quadratic form and whose right side has a strictly negative one.  No square root
  and no eigenvalue enters.

## Scope warning

The sharp duality preserves `Gtz.IsTie` and does NOT preserve
`Gtz.HasParallelPair`: `Gtz.hinge_not_preserved_by_duality` refutes that at
`(k+1, k)` against `(k+1, 1)`.  Nothing below claims otherwise.  The pair
dictionary of `Gtz/Wave/ChartQuadraticCore.lean` is scoped to `(6,3)`, the Gale
self-dual cell, and this module states no transport of the hinge at any cell.

The complement chart `1 - P` of `Gtz/Quantitative/ChartDuality.lean` is a THIRD
object, distinct from both `M` and the sharp dual, and
`Gtz.not_forall_dominates_chartDual_compl` shows it does not transport domination.
It is not used here.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.Reductions
import Gtz.Certificates.ResidueDissolution
import Gtz.Wave.BandTieTower
import Gtz.Wave.SharpFiveSetCriterion
import Gtz.Wave.SharpShareCoAtom
import Gtz.Wave.ChartQuadraticCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1 — the two frames and the two diagonals

Four matrices carry every computation below.  `V` and `W` are the atom rows scaled
by `√t_c` and by `1/√t_c`; `T⁻¹` and `N` are the two diagonals the duality needs. -/

/-- The INVERSE-SCALED frame: row `c` is `g_c / √t_c`.  It is `diag(1/t) · V`, and
it is the frame the inverse of the chart gap is built from. -/
noncomputable def invRootAtomRows (D : WeightedDesign m k) : Matrix (Fin m) (Fin k) ℝ :=
  Matrix.of fun atomIndex coord => (Real.sqrt (D.weight atomIndex))⁻¹ * D.atom atomIndex coord

/-- The inverse weight diagonal `diag(1/t)`. -/
noncomputable def inverseWeightDiagonal (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal fun atomIndex => (D.weight atomIndex)⁻¹

/-- **THE PAIR-MASS ROOT DIAGONAL** `N = diag(√(t_c(1 - t_c)))`.  Its square is the
campaign's universal pair mass, and it is the conjugator of the sharp duality. -/
noncomputable def pairRootDiagonal (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal fun atomIndex => Real.sqrt (D.weight atomIndex * (1 - D.weight atomIndex))

theorem sqrtWeight_ne_zero (D : WeightedDesign m k) (atomIndex : Fin m) :
    Real.sqrt (D.weight atomIndex) ≠ 0 :=
  (Real.sqrt_pos.mpr (D.weight_pos atomIndex)).ne'

theorem sqrtWeight_mul_self' (D : WeightedDesign m k) (atomIndex : Fin m) :
    Real.sqrt (D.weight atomIndex) * Real.sqrt (D.weight atomIndex) = D.weight atomIndex :=
  Real.mul_self_sqrt (D.weight_pos atomIndex).le

theorem sqrtWeight_sq (D : WeightedDesign m k) (atomIndex : Fin m) :
    Real.sqrt (D.weight atomIndex) ^ 2 = D.weight atomIndex :=
  Real.sq_sqrt (D.weight_pos atomIndex).le

/-- The root against the reciprocal weight is the reciprocal root. -/
theorem sqrtWeight_mul_inv_weight (D : WeightedDesign m k) (atomIndex : Fin m) :
    Real.sqrt (D.weight atomIndex) * (D.weight atomIndex)⁻¹
      = (Real.sqrt (D.weight atomIndex))⁻¹ := by
  have hne := sqrtWeight_ne_zero D atomIndex
  have hwne : D.weight atomIndex ≠ 0 := (D.weight_pos atomIndex).ne'
  have hsq := sqrtWeight_mul_self' D atomIndex
  field_simp
  linear_combination hsq

/-- The weight against the reciprocal root is the root. -/
theorem weight_mul_inv_sqrtWeight (D : WeightedDesign m k) (atomIndex : Fin m) :
    D.weight atomIndex * (Real.sqrt (D.weight atomIndex))⁻¹
      = Real.sqrt (D.weight atomIndex) := by
  have hne := sqrtWeight_ne_zero D atomIndex
  have hsq := sqrtWeight_mul_self' D atomIndex
  field_simp
  linear_combination -hsq

/-- The reciprocal root squares to the reciprocal weight. -/
theorem inv_sqrtWeight_sq (D : WeightedDesign m k) (atomIndex : Fin m) :
    (Real.sqrt (D.weight atomIndex))⁻¹ ^ 2 = (D.weight atomIndex)⁻¹ := by
  rw [inv_pow, sqrtWeight_sq]

/-- The weight diagonal cancels its inverse. -/
theorem weightDiagonal_mul_inverseWeightDiagonal (D : WeightedDesign m k) :
    Matrix.diagonal D.weight * inverseWeightDiagonal D = 1 := by
  rw [inverseWeightDiagonal, Matrix.diagonal_mul_diagonal]
  have hone : (fun atomIndex => D.weight atomIndex * (D.weight atomIndex)⁻¹)
      = fun _ : Fin m => (1 : ℝ) :=
    funext fun atomIndex => mul_inv_cancel₀ (D.weight_pos atomIndex).ne'
  rw [hone, Matrix.diagonal_one]

/-- The weight diagonal turns the inverse-scaled frame into the scaled frame. -/
theorem weightDiagonal_mul_invRootAtomRows (D : WeightedDesign m k) :
    Matrix.diagonal D.weight * invRootAtomRows D = scaledAtomRows D := by
  ext atomIndex coord
  rw [Matrix.diagonal_mul]
  simp only [invRootAtomRows, scaledAtomRows, Matrix.of_apply]
  rw [← mul_assoc, weight_mul_inv_sqrtWeight]

/-- The scaled frame against the inverse weight diagonal is the inverse-scaled
frame. -/
theorem transpose_scaledAtomRows_mul_inverseWeightDiagonal (D : WeightedDesign m k) :
    (scaledAtomRows D)ᵀ * inverseWeightDiagonal D = (invRootAtomRows D)ᵀ := by
  ext coord atomIndex
  rw [inverseWeightDiagonal, Matrix.mul_diagonal]
  simp only [Matrix.transpose_apply, scaledAtomRows, invRootAtomRows, Matrix.of_apply]
  rw [mul_comm (Real.sqrt (D.weight atomIndex)) (D.atom atomIndex coord), mul_assoc,
    sqrtWeight_mul_inv_weight, mul_comm]

/-- **THE TWO FRAMES PAIR TO THE UNWEIGHTED MOMENT.**  The two square roots cancel
and what is left is `Σ_c g_c g_cᵀ`, which is the total gap shifted by one. -/
theorem transpose_scaledAtomRows_mul_invRootAtomRows (D : WeightedDesign m k) :
    (scaledAtomRows D)ᵀ * invRootAtomRows D = totalGap D + 1 := by
  have hshift : totalGap D + 1 = subsetSum D Finset.univ := by rw [totalGap]; abel
  rw [hshift]
  ext coordRow coordCol
  rw [Matrix.mul_apply, subsetSum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  have hne := sqrtWeight_ne_zero D atomIndex
  simp only [Matrix.transpose_apply, scaledAtomRows, invRootAtomRows, Matrix.of_apply,
    atomMatrix, Matrix.vecMulVec_apply]
  field_simp

/-! ## Part 2 — the gap is invertible

One Rayleigh identity, and the pair mass does the rest. -/

/-- **THE RAYLEIGH IDENTITY OF THE CHART GAP.**  Because the chart is a symmetric
idempotent, its quadratic form at a probe is the squared length of the PROJECTED
probe, and the gap's form is that against the weighted square total.  This is the
whole inertia statement in one line: on the range of the chart the projection is
the identity and the form is `Σ(1 - t_c)x_c² > 0`, on the kernel it is
`-Σ t_c x_c² < 0`. -/
theorem quadForm_chartGapOfDesign (D : WeightedDesign m k) (probe : Fin m → ℝ) :
    probe ⬝ᵥ (chartGapOfDesign D *ᵥ probe)
      = (projectionOfDesign D *ᵥ probe) ⬝ᵥ (projectionOfDesign D *ᵥ probe)
        - ∑ atomIndex, D.weight atomIndex * probe atomIndex ^ 2 := by
  have hidem : projectionOfDesign D *ᵥ (projectionOfDesign D *ᵥ probe)
      = projectionOfDesign D *ᵥ probe := by
    rw [Matrix.mulVec_mulVec, projectionOfDesign_mul_self]
  have hchart : probe ⬝ᵥ (projectionOfDesign D *ᵥ probe)
      = (projectionOfDesign D *ᵥ probe) ⬝ᵥ (projectionOfDesign D *ᵥ probe) := by
    have hadj := dotProduct_mulVec_transpose (projectionOfDesign D) probe
      (projectionOfDesign D *ᵥ probe)
    rw [projectionOfDesign_transpose, hidem] at hadj
    exact hadj.symm
  have hweightForm : probe ⬝ᵥ (Matrix.diagonal D.weight *ᵥ probe)
      = ∑ atomIndex, D.weight atomIndex * probe atomIndex ^ 2 := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun atomIndex _ => by
      rw [Matrix.mulVec_diagonal]; ring
  rw [chartGapOfDesign, Matrix.sub_mulVec, dotProduct_sub, hchart, hweightForm]

/-- **THE CHART GAP HAS NO KERNEL.**  A null vector satisfies `P x = T x`, so the
Rayleigh identity collapses to `Σ_c t_c(1 - t_c) x_c² = 0`, and every coefficient is
strictly positive once the design has two atoms.  The pair mass is the whole
obstruction, and it is exactly the quantity that vanishes at a vertex of the
simplex. -/
theorem chartGapOfDesign_mulVec_eq_zero (D : WeightedDesign m k) (hm : 2 ≤ m)
    {probe : Fin m → ℝ} (hkill : chartGapOfDesign D *ᵥ probe = 0) : probe = 0 := by
  classical
  have hsplit : projectionOfDesign D *ᵥ probe = Matrix.diagonal D.weight *ᵥ probe := by
    have hstep := hkill
    rw [chartGapOfDesign, Matrix.sub_mulVec, sub_eq_zero] at hstep
    exact hstep
  have hquad := quadForm_chartGapOfDesign D probe
  rw [hkill, dotProduct_zero] at hquad
  have hnorm : (projectionOfDesign D *ᵥ probe) ⬝ᵥ (projectionOfDesign D *ᵥ probe)
      = ∑ atomIndex, D.weight atomIndex ^ 2 * probe atomIndex ^ 2 := by
    rw [hsplit, dotProduct]
    exact Finset.sum_congr rfl fun atomIndex _ => by
      rw [Matrix.mulVec_diagonal]; ring
  rw [hnorm] at hquad
  have hmass : ∑ atomIndex, D.weight atomIndex * (1 - D.weight atomIndex)
      * probe atomIndex ^ 2 = 0 := by
    rw [show (∑ atomIndex, D.weight atomIndex * (1 - D.weight atomIndex) * probe atomIndex ^ 2)
        = (∑ atomIndex, D.weight atomIndex * probe atomIndex ^ 2)
          - ∑ atomIndex, D.weight atomIndex ^ 2 * probe atomIndex ^ 2 from by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun atomIndex _ => by ring]
    linarith [hquad]
  have hnonneg : ∀ atomIndex ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ D.weight atomIndex * (1 - D.weight atomIndex) * probe atomIndex ^ 2 := by
    intro atomIndex _
    have hslack : (0 : ℝ) < 1 - D.weight atomIndex := by
      linarith [weight_lt_one D hm atomIndex]
    exact mul_nonneg (mul_nonneg (D.weight_pos atomIndex).le hslack.le) (sq_nonneg _)
  funext atomIndex
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hmass atomIndex (Finset.mem_univ _)
  have hslack : (0 : ℝ) < 1 - D.weight atomIndex := by
    linarith [weight_lt_one D hm atomIndex]
  have hcoef : (0 : ℝ) < D.weight atomIndex * (1 - D.weight atomIndex) :=
    mul_pos (D.weight_pos atomIndex) hslack
  have hsq : probe atomIndex ^ 2 = 0 := by
    rcases mul_eq_zero.mp hterm with hbad | hgood
    · exact absurd hbad (ne_of_gt hcoef)
    · exact hgood
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

/-- The chart gap is invertible at every design with two or more atoms. -/
theorem isUnit_det_chartGapOfDesign (D : WeightedDesign m k) (hm : 2 ≤ m) :
    IsUnit (chartGapOfDesign D).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨probe, hne, hkill⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hne (chartGapOfDesign_mulVec_eq_zero D hm hkill)

/-! ## Part 3 — the inverse, in closed form

One Woodbury product.  Nothing spectral, and the only inverse on the right is the
total gap's, which the campaign has carried since `Gtz.posDef_totalGap`. -/

/-- **THE INVERSE OF THE CHART GAP**, as an explicit matrix: the hat of the
inverse-scaled frame in the metric of the total gap, less the inverse weight
diagonal. -/
noncomputable def chartGapInverseForm (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  invRootAtomRows D * (totalGap D)⁻¹ * (invRootAtomRows D)ᵀ - inverseWeightDiagonal D

/-- **THE WOODBURY PRODUCT.**  Four terms, three substitutions, and the total gap's
own cancellation. -/
theorem chartGapOfDesign_mul_inverseForm (D : WeightedDesign m k) (hm : 2 ≤ m) :
    chartGapOfDesign D * chartGapInverseForm D = 1 := by
  have hGGinv : totalGap D * (totalGap D)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_det_totalGap D hm)
  have hGZ : totalGap D * ((totalGap D)⁻¹ * (invRootAtomRows D)ᵀ) = (invRootAtomRows D)ᵀ := by
    rw [← Matrix.mul_assoc, hGGinv, Matrix.one_mul]
  have hcore : (scaledAtomRows D)ᵀ
        * (invRootAtomRows D * ((totalGap D)⁻¹ * (invRootAtomRows D)ᵀ))
      = (invRootAtomRows D)ᵀ + (totalGap D)⁻¹ * (invRootAtomRows D)ᵀ := by
    rw [← Matrix.mul_assoc, transpose_scaledAtomRows_mul_invRootAtomRows, Matrix.add_mul,
      Matrix.one_mul, hGZ]
  have hshift : Matrix.diagonal D.weight
        * (invRootAtomRows D * ((totalGap D)⁻¹ * (invRootAtomRows D)ᵀ))
      = scaledAtomRows D * ((totalGap D)⁻¹ * (invRootAtomRows D)ᵀ) := by
    rw [← Matrix.mul_assoc, weightDiagonal_mul_invRootAtomRows]
  rw [chartGapOfDesign, chartGapInverseForm, projectionOfDesign]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  rw [hcore, transpose_scaledAtomRows_mul_inverseWeightDiagonal, hshift,
    weightDiagonal_mul_inverseWeightDiagonal, Matrix.mul_add]
  abel

/-- **THE INVERSE IS THE WOODBURY FORM.** -/
theorem chartGapOfDesign_inv_eq (D : WeightedDesign m k) (hm : 2 ≤ m) :
    (chartGapOfDesign D)⁻¹ = chartGapInverseForm D :=
  Matrix.inv_eq_right_inv (chartGapOfDesign_mul_inverseForm D hm)

/-! ## Part 4 — the diagonal readings

The diagonal of `M` is the weighted heavy excess and the diagonal of `M⁻¹` is the
co-atom reading, both up to one factor of the weight.  Three strata of the campaign
become sign conditions on those two diagonals. -/

/-- **THE DIAGONAL OF THE INVERSE IS THE CO-ATOM READING.**

    `t_c · (M⁻¹)_cc = ρ_c - 1` .

The hat term contributes `ρ_c / t_c` and the inverse weight diagonal contributes
`-1 / t_c`. -/
theorem weight_mul_chartGapInverse_diag (D : WeightedDesign m k) (hm : 2 ≤ m)
    (atomIndex : Fin m) :
    D.weight atomIndex * (chartGapOfDesign D)⁻¹ atomIndex atomIndex
      = totalGapReading D atomIndex - 1 := by
  have hwne : D.weight atomIndex ≠ 0 := (D.weight_pos atomIndex).ne'
  have hrow : (fun coord => invRootAtomRows D atomIndex coord)
      = fun coord => (Real.sqrt (D.weight atomIndex))⁻¹ * D.atom atomIndex coord := by
    funext coord; rw [invRootAtomRows, Matrix.of_apply]
  have hhat : (invRootAtomRows D * (totalGap D)⁻¹ * (invRootAtomRows D)ᵀ) atomIndex atomIndex
      = (Real.sqrt (D.weight atomIndex))⁻¹ ^ 2 * totalGapReading D atomIndex := by
    rw [hat_diag_eq, hrow, reading_smul, totalGapReading]
  have hdiag : inverseWeightDiagonal D atomIndex atomIndex = (D.weight atomIndex)⁻¹ := by
    rw [inverseWeightDiagonal, Matrix.diagonal_apply_eq]
  rw [chartGapOfDesign_inv_eq D hm, chartGapInverseForm, Matrix.sub_apply, hhat, hdiag,
    inv_sqrtWeight_sq]
  field_simp

/-- **A CO-ATOM SET DOMINATES STRICTLY EXACTLY AT A NEGATIVE INVERSE DIAGONAL.** -/
theorem posDef_gap_erase_iff_chartGapInverse_diag_neg (D : WeightedDesign m k) (hm : 2 ≤ m)
    (atomIndex : Fin m) :
    (subsetSum D (Finset.univ.erase atomIndex) - 1).PosDef
      ↔ (chartGapOfDesign D)⁻¹ atomIndex atomIndex < 0 := by
  have hkey := weight_mul_chartGapInverse_diag D hm atomIndex
  have hpos := D.weight_pos atomIndex
  rw [posDef_gap_erase_iff D hm atomIndex]
  constructor
  · intro hlt
    nlinarith [hkey, hlt, hpos]
  · intro hneg
    nlinarith [hkey, hneg, hpos]

/-- **A CO-ATOM SET IS A CORANK-ONE WEAK DOMINATOR EXACTLY AT A VANISHING INVERSE
DIAGONAL.** -/
theorem gap_erase_corankOne_iff_chartGapInverse_diag_eq_zero (D : WeightedDesign m k)
    (hm : 2 ≤ m) (atomIndex : Fin m) :
    totalGapReading D atomIndex = 1
      ↔ (chartGapOfDesign D)⁻¹ atomIndex atomIndex = 0 := by
  have hkey := weight_mul_chartGapInverse_diag D hm atomIndex
  have hpos := D.weight_pos atomIndex
  constructor
  · intro hone
    rw [hone, sub_self] at hkey
    rcases mul_eq_zero.mp hkey with hbad | hgood
    · exact absurd hbad hpos.ne'
    · exact hgood
  · intro hzero
    rw [hzero, mul_zero] at hkey
    linarith [hkey]

/-- **EVERY CO-ATOM SET DOMINATES STRICTLY EXACTLY WHEN THE INVERSE DIAGONAL IS
EVERYWHERE NEGATIVE.**  At `(6,3)` this is one of the two hypotheses of the open
residual stratum, and it has become a sign condition on `M⁻¹`. -/
theorem forall_posDef_gap_erase_iff_chartGapInverse_diag_neg (D : WeightedDesign m k)
    (hm : 2 ≤ m) :
    (∀ atomIndex : Fin m, (subsetSum D (Finset.univ.erase atomIndex) - 1).PosDef)
      ↔ ∀ atomIndex : Fin m, (chartGapOfDesign D)⁻¹ atomIndex atomIndex < 0 := by
  constructor
  · intro hall atomIndex
    exact (posDef_gap_erase_iff_chartGapInverse_diag_neg D hm atomIndex).mp (hall atomIndex)
  · intro hall atomIndex
    exact (posDef_gap_erase_iff_chartGapInverse_diag_neg D hm atomIndex).mpr (hall atomIndex)

/-- **ALL-HEAVY IS A POSITIVE DIAGONAL OF THE GAP.**  The other hypothesis of the
open residual stratum, on the OTHER matrix.  So the stratum is: `diag M > 0` and
`diag M⁻¹ < 0`. -/
theorem allHeavy_iff_chartGapOfDesign_diag_pos (D : WeightedDesign m k) :
    AllHeavy D ↔ ∀ atomIndex : Fin m, 0 < chartGapOfDesign D atomIndex atomIndex := by
  constructor
  · intro hheavy atomIndex
    rw [chartGapOfDesign_diagonal]
    exact mul_pos (D.weight_pos atomIndex) (by linarith [hheavy atomIndex])
  · intro hdiag atomIndex
    have hstep := hdiag atomIndex
    rw [chartGapOfDesign_diagonal] at hstep
    have hpos := D.weight_pos atomIndex
    nlinarith [hstep, hpos]

/-- **THE CORANK-ONE TIE IS THE VANISHING OF THE INVERSE DIAGONAL.**  At size one
above the rank the `rank`-subsets are exactly the co-atom sets, so a tie says every
co-atom reading is at least one, and the landed reading budget — the co-weighted
readings total the rank while the co-weights total the size less one — forces
equality everywhere.

This puts the classified corank-one stratum of `Gtz.isTie_iff_leverage_law` exactly
on the EQUALITY BOUNDARY of
`Gtz.forall_posDef_gap_erase_iff_chartGapInverse_diag_neg`, and it derives that
placement from the budget rather than from the leverage law. -/
theorem card_erase_univ_eq (missing : Fin (k + 1)) :
    (Finset.univ.erase missing).card = k := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

theorem isTie_iff_chartGapInverse_diag_eq_zero (D : WeightedDesign (k + 1) k) (hrank : 1 ≤ k) :
    IsTie D ↔ ∀ atomIndex : Fin (k + 1), (chartGapOfDesign D)⁻¹ atomIndex atomIndex = 0 := by
  classical
  have hm : 2 ≤ k + 1 := by omega
  have hslack : ∀ atomIndex : Fin (k + 1), (0 : ℝ) < 1 - D.weight atomIndex := by
    intro atomIndex; linarith [weight_lt_one D hm atomIndex]
  have hbudget := sum_one_sub_weight_mul_totalGapReading D hm
  have hcoweight : ∑ atomIndex : Fin (k + 1), (1 - D.weight atomIndex) = (k : ℝ) := by
    rw [Finset.sum_sub_distrib, D.weight_sum_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  constructor
  · intro htie atomIndex
    -- no co-atom set dominates strictly, so every reading is at least one
    have hfloor : ∀ other : Fin (k + 1), 1 ≤ totalGapReading D other := by
      intro other
      by_contra hcontra
      push Not at hcontra
      exact htie.2 (Finset.univ.erase other) (card_erase_univ_eq other)
        ((posDef_gap_erase_iff D hm other).mpr hcontra)
    -- the budget spends exactly the co-weight total, so no slack is available
    have hgap : ∑ other : Fin (k + 1),
        (1 - D.weight other) * (totalGapReading D other - 1) = 0 := by
      rw [show (∑ other : Fin (k + 1), (1 - D.weight other) * (totalGapReading D other - 1))
          = (∑ other : Fin (k + 1), (1 - D.weight other) * totalGapReading D other)
            - ∑ other : Fin (k + 1), (1 - D.weight other) from by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun other _ => by ring]
      rw [hbudget, hcoweight, sub_self]
    have hnonneg : ∀ other ∈ (Finset.univ : Finset (Fin (k + 1))),
        0 ≤ (1 - D.weight other) * (totalGapReading D other - 1) :=
      fun other _ => mul_nonneg (hslack other).le (by linarith [hfloor other])
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hgap atomIndex
      (Finset.mem_univ _)
    have hread : totalGapReading D atomIndex = 1 := by
      rcases mul_eq_zero.mp hterm with hbad | hgood
      · exact absurd hbad (hslack atomIndex).ne'
      · linarith [hgood]
    exact (gap_erase_corankOne_iff_chartGapInverse_diag_eq_zero D hm atomIndex).mp hread
  · intro hzero
    have hread : ∀ atomIndex : Fin (k + 1), totalGapReading D atomIndex = 1 :=
      fun atomIndex =>
        (gap_erase_corankOne_iff_chartGapInverse_diag_eq_zero D hm atomIndex).mpr (hzero atomIndex)
    refine ⟨⟨Finset.univ.erase ⟨0, by omega⟩, card_erase_univ_eq _, ?_⟩, ?_⟩
    · exact (posSemidef_gap_erase_iff D hm _).mpr (le_of_eq (hread _))
    · intro selected hcard hposDef
      obtain ⟨missing, rfl⟩ := exists_erase_of_card_eq hcard
      have hstrict := (posDef_gap_erase_iff D hm missing).mp hposDef
      rw [hread missing] at hstrict
      exact absurd hstrict (lt_irrefl 1)

/-! ## Part 5 — the sharp duality

Two diagonal identities and the inverse formula.  Nothing else. -/

/-- The pair-mass root turns the inverse-scaled frame into the co-weighted frame:
`√(t(1-t)) · (1/√t) = √(1-t)`. -/
theorem pairRootDiagonal_mul_invRootAtomRows (D : WeightedDesign m k) (hm : 2 ≤ m) :
    pairRootDiagonal D * invRootAtomRows D = totalGapFrame D := by
  ext atomIndex coord
  rw [pairRootDiagonal, Matrix.diagonal_mul]
  simp only [invRootAtomRows, totalGapFrame, Matrix.of_apply, coRoot]
  have hslack : (0 : ℝ) ≤ 1 - D.weight atomIndex := by
    linarith [weight_lt_one D hm atomIndex]
  have hsplit : Real.sqrt (D.weight atomIndex * (1 - D.weight atomIndex))
      = Real.sqrt (D.weight atomIndex) * Real.sqrt (1 - D.weight atomIndex) :=
    Real.sqrt_mul (D.weight_pos atomIndex).le _
  have hne := sqrtWeight_ne_zero D atomIndex
  rw [hsplit]
  field_simp

/-- The transposed reading of the same identity. -/
theorem transpose_invRootAtomRows_mul_pairRootDiagonal (D : WeightedDesign m k) (hm : 2 ≤ m) :
    (invRootAtomRows D)ᵀ * pairRootDiagonal D = (totalGapFrame D)ᵀ := by
  have hsymm : (pairRootDiagonal D)ᵀ = pairRootDiagonal D := by
    rw [pairRootDiagonal, Matrix.diagonal_transpose]
  have hstep := congrArg Matrix.transpose (pairRootDiagonal_mul_invRootAtomRows D hm)
  rwa [Matrix.transpose_mul, hsymm] at hstep

/-- **THE PAIR MASS CONJUGATES THE INVERSE WEIGHT DIAGONAL TO THE CO-WEIGHT
DIAGONAL**: `N T⁻¹ N = 1 - T`.  This is the identity that makes the duality
weight-aware, and it is the only place `t_c(1 - t_c)/t_c = 1 - t_c` is spent. -/
theorem pairRootDiagonal_conj_inverseWeightDiagonal (D : WeightedDesign m k) (hm : 2 ≤ m) :
    pairRootDiagonal D * inverseWeightDiagonal D * pairRootDiagonal D
      = 1 - Matrix.diagonal D.weight := by
  rw [pairRootDiagonal, inverseWeightDiagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  have hentry : (fun atomIndex : Fin m =>
        Real.sqrt (D.weight atomIndex * (1 - D.weight atomIndex)) * (D.weight atomIndex)⁻¹
          * Real.sqrt (D.weight atomIndex * (1 - D.weight atomIndex)))
      = fun atomIndex : Fin m => 1 - D.weight atomIndex := by
    funext atomIndex
    have hslack : (0 : ℝ) ≤ 1 - D.weight atomIndex := by
      linarith [weight_lt_one D hm atomIndex]
    have hprod : (0 : ℝ) ≤ D.weight atomIndex * (1 - D.weight atomIndex) :=
      mul_nonneg (D.weight_pos atomIndex).le hslack
    have hsq := Real.mul_self_sqrt hprod
    have hne := (D.weight_pos atomIndex).ne'
    field_simp
    linear_combination hsq
  rw [hentry]
  ext leftIndex rightIndex
  rcases eq_or_ne leftIndex rightIndex with rfl | hne
  · rw [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hne, Matrix.sub_apply, Matrix.one_apply_ne hne,
      Matrix.diagonal_apply_ne _ hne, sub_zero]

/-- **THE SHARP CHART GAP** of a design: the chart gap of its sharp dual, written
without the dual, without the whitener and without a square root of a matrix.  By
`Gtz.totalGapHat_add_sharpHat` the leading part `1 - Π` is `Gtz.sharpHat`. -/
noncomputable def sharpChartGap (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  1 - Matrix.diagonal D.weight - totalGapHat D

/-- **THE SHARP DUALITY IS `-N M⁻¹ N`.**  The inverse formula, conjugated by the
pair-mass root, is the sharp chart gap.  The hat term becomes the co-weighted hat
and the inverse weight diagonal becomes the co-weight diagonal. -/
theorem chartGapOfDesign_sharpDual_eq (D : WeightedDesign m k) (hm : 2 ≤ m) :
    -(pairRootDiagonal D * (chartGapOfDesign D)⁻¹ * pairRootDiagonal D) = sharpChartGap D := by
  have hhat : pairRootDiagonal D
        * (invRootAtomRows D * (totalGap D)⁻¹ * (invRootAtomRows D)ᵀ)
        * pairRootDiagonal D
      = totalGapHat D := by
    rw [totalGapHat, ← transpose_invRootAtomRows_mul_pairRootDiagonal D hm,
      ← pairRootDiagonal_mul_invRootAtomRows D hm]
    simp only [Matrix.mul_assoc]
  rw [chartGapOfDesign_inv_eq D hm, chartGapInverseForm, Matrix.mul_sub, Matrix.sub_mul,
    hhat, pairRootDiagonal_conj_inverseWeightDiagonal D hm, sharpChartGap]
  abel

/-- The sharp chart gap shifted back by the weight diagonal is the complementary
hat, which the landed `Gtz.totalGapHat_add_sharpHat` identifies with
`Gtz.sharpHat`. -/
theorem sharpChartGap_add_weightDiagonal (D : WeightedDesign m k) :
    sharpChartGap D + Matrix.diagonal D.weight = 1 - totalGapHat D := by
  rw [sharpChartGap]
  abel

/-- **THE SHARP CHART IS THE SHARP HAT.**  For every Naimark dual of the design the
chart of the sharp design — the complement of the co-weighted hat — is
`Gtz.sharpHat`, so `Gtz.sharpChartGap` really is the gap of the design of
`Gtz.exists_naimark_sharp_design` and not merely a matrix with its formula. -/
theorem sharpChartGap_add_weightDiagonal_eq_sharpHat {r : ℕ} (D : WeightedDesign m k)
    (N : NaimarkDual D r) (hm : 2 ≤ m) :
    sharpChartGap D + Matrix.diagonal D.weight = sharpHat D N := by
  rw [sharpChartGap_add_weightDiagonal]
  have hsum := totalGapHat_add_sharpHat D N hm
  rw [← hsum]
  abel

/-! ## Part 6 — the involution and the missing fixed point

Both are abstract: they hold for any invertible matrix and any invertible
conjugator, and the fixed-point statement needs only that the conjugator is a
POSITIVE diagonal. -/

/-- **THE DUALITY MAP**, abstractly: conjugate the inverse by a fixed matrix and
change the sign. -/
noncomputable def negConjInv {size : ℕ} (scale form : Matrix (Fin size) (Fin size) ℝ) :
    Matrix (Fin size) (Fin size) ℝ :=
  -(scale * form⁻¹ * scale)

theorem chartGapOfDesign_sharpDual_eq_negConjInv (D : WeightedDesign m k) (hm : 2 ≤ m) :
    negConjInv (pairRootDiagonal D) (chartGapOfDesign D) = sharpChartGap D :=
  chartGapOfDesign_sharpDual_eq D hm

/-- The image of the duality map is invertible, with the reciprocal conjugation as
its inverse. -/
theorem negConjInv_inv_eq {size : ℕ} {scale form : Matrix (Fin size) (Fin size) ℝ}
    (hscale : IsUnit scale.det) (hform : IsUnit form.det) :
    (negConjInv scale form)⁻¹ = -(scale⁻¹ * form * scale⁻¹) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [negConjInv, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  calc scale * form⁻¹ * scale * (scale⁻¹ * form * scale⁻¹)
      = scale * form⁻¹ * (scale * scale⁻¹) * form * scale⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = scale * (form⁻¹ * form) * scale⁻¹ := by
        rw [Matrix.mul_nonsing_inv _ hscale, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [Matrix.nonsing_inv_mul _ hform, Matrix.mul_one,
          Matrix.mul_nonsing_inv _ hscale]

/-- **THE DUALITY IS AN INVOLUTION.**  Applying it twice returns the original
matrix on the nose, with no congruence and no orthogonal ambiguity left over. -/
theorem negConjInv_negConjInv {size : ℕ} {scale form : Matrix (Fin size) (Fin size) ℝ}
    (hscale : IsUnit scale.det) (hform : IsUnit form.det) :
    negConjInv scale (negConjInv scale form) = form := by
  rw [negConjInv, negConjInv_inv_eq hscale hform, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  calc scale * (scale⁻¹ * form * scale⁻¹) * scale
      = (scale * scale⁻¹) * form * (scale⁻¹ * scale) := by
        simp only [Matrix.mul_assoc]
    _ = form := by
        rw [Matrix.mul_nonsing_inv _ hscale, Matrix.nonsing_inv_mul _ hscale, Matrix.one_mul,
          Matrix.mul_one]

/-- The pair-mass root diagonal is invertible once the design has two atoms. -/
theorem isUnit_det_pairRootDiagonal (D : WeightedDesign m k) (hm : 2 ≤ m) :
    IsUnit (pairRootDiagonal D).det := by
  rw [pairRootDiagonal, Matrix.det_diagonal, isUnit_iff_ne_zero]
  refine Finset.prod_ne_zero_iff.mpr fun atomIndex _ => ?_
  have hslack : (0 : ℝ) < 1 - D.weight atomIndex := by
    linarith [weight_lt_one D hm atomIndex]
  exact (Real.sqrt_pos.mpr (mul_pos (D.weight_pos atomIndex) hslack)).ne'

/-- **THE SHARP DUALITY OF A DESIGN IS AN INVOLUTION.** -/
theorem chartGapOfDesign_sharpDual_involutive (D : WeightedDesign m k) (hm : 2 ≤ m) :
    negConjInv (pairRootDiagonal D) (sharpChartGap D) = chartGapOfDesign D := by
  rw [← chartGapOfDesign_sharpDual_eq_negConjInv D hm]
  exact negConjInv_negConjInv (isUnit_det_pairRootDiagonal D hm)
    (isUnit_det_chartGapOfDesign D hm)

/-! ### No fixed point, at any size and any cell -/

/-- The reciprocal of a positive diagonal cancels it. -/
theorem diagonal_mul_diagonal_inv {size : ℕ} {entry : Fin size → ℝ}
    (hentry : ∀ index, 0 < entry index) :
    Matrix.diagonal (fun index => (entry index)⁻¹) * Matrix.diagonal entry = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have hone : (fun index => (entry index)⁻¹ * entry index) = fun _ : Fin size => (1 : ℝ) :=
    funext fun index => inv_mul_cancel₀ (hentry index).ne'
  rw [hone, Matrix.diagonal_one]

/-- **THE DUALITY HAS NO FIXED POINT.**  A fixed point of `M ↦ -(N M⁻¹ N)` at a
symmetric invertible `M` and a positive diagonal `N` forces `M N⁻¹ M = -N`.  The
left side reads every probe as `Σ_c (M x)_c² / n_c ≥ 0` and the right side reads a
coordinate probe as `-n_c < 0`.

Three lines, and no square root of a matrix: the argument never forms `N^{1/2}`.
Consequently no design is its own sharp dual, at any cell. -/
theorem negConjInv_ne_self_of_diagonal_pos {size : ℕ} (hsize : 0 < size)
    {gapForm : Matrix (Fin size) (Fin size) ℝ} {entry : Fin size → ℝ}
    (hentry : ∀ index, 0 < entry index) (hsymm : gapFormᵀ = gapForm)
    (hunit : IsUnit gapForm.det) :
    negConjInv (Matrix.diagonal entry) gapForm ≠ gapForm := by
  classical
  intro hfixed
  rw [negConjInv] at hfixed
  set probe : Fin size → ℝ := Pi.single ⟨0, hsize⟩ 1 with hprobe
  set reciprocal : Matrix (Fin size) (Fin size) ℝ :=
    Matrix.diagonal fun index => (entry index)⁻¹ with hreciprocal
  have hcancel : reciprocal * Matrix.diagonal entry = 1 := diagonal_mul_diagonal_inv hentry
  -- the fixed point forces the sandwich identity
  have hsandwich : gapForm * reciprocal * gapForm = -Matrix.diagonal entry := by
    have hstep : gapForm * reciprocal * gapForm
        = gapForm * reciprocal
          * (-(Matrix.diagonal entry * gapForm⁻¹ * Matrix.diagonal entry)) := by
      rw [hfixed]
    rw [hstep, Matrix.mul_neg, neg_inj]
    calc gapForm * reciprocal * (Matrix.diagonal entry * gapForm⁻¹ * Matrix.diagonal entry)
        = gapForm * (reciprocal * Matrix.diagonal entry) * gapForm⁻¹ * Matrix.diagonal entry := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal entry := by
          rw [hcancel, Matrix.mul_one, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]
  -- the left side is nonnegative
  have hleft : 0 ≤ probe ⬝ᵥ ((gapForm * reciprocal * gapForm) *ᵥ probe) := by
    have hexpand : (gapForm * reciprocal * gapForm) *ᵥ probe
        = gapForm *ᵥ (reciprocal *ᵥ (gapForm *ᵥ probe)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have hadj := dotProduct_mulVec_transpose gapForm probe
      (reciprocal *ᵥ (gapForm *ᵥ probe))
    rw [hsymm] at hadj
    rw [hexpand, ← hadj, dotProduct]
    refine Finset.sum_nonneg fun index _ => ?_
    rw [hreciprocal, Matrix.mulVec_diagonal]
    have hinv : 0 < (entry index)⁻¹ := inv_pos.mpr (hentry index)
    nlinarith [hinv, sq_nonneg ((gapForm *ᵥ probe) index)]
  -- the right side is strictly negative
  have hright : probe ⬝ᵥ ((-Matrix.diagonal entry) *ᵥ probe) < 0 := by
    have hvalue : probe ⬝ᵥ ((-Matrix.diagonal entry) *ᵥ probe) = -entry ⟨0, hsize⟩ := by
      rw [dotProduct]
      have hterm : ∀ index : Fin size,
          probe index * ((-Matrix.diagonal entry) *ᵥ probe) index
            = if index = ⟨0, hsize⟩ then -entry index else 0 := by
        intro index
        rw [Matrix.neg_mulVec, Pi.neg_apply, Matrix.mulVec_diagonal, hprobe]
        by_cases hcase : index = ⟨0, hsize⟩
        · subst hcase
          simp only [Pi.single_eq_same, if_true]
          ring
        · simp only [Pi.single_eq_of_ne hcase, if_neg hcase]
          ring
      rw [Finset.sum_congr rfl fun index _ => hterm index,
        Finset.sum_ite_eq' Finset.univ (⟨0, hsize⟩ : Fin size) (fun index => -entry index)]
      simp
    rw [hvalue]
    linarith [hentry ⟨0, hsize⟩]
  rw [hsandwich] at hleft
  linarith [hleft, hright]

/-- **NO DESIGN IS ITS OWN SHARP DUAL.**  The sharp chart gap of a design is never
its own chart gap, at any size and any rank.  So the duality acts on the design
variety with every orbit of size exactly two, and the tie stratum — which the
duality preserves — is partitioned into genuine pairs. -/
theorem sharpChartGap_ne_chartGapOfDesign (D : WeightedDesign m k) (hm : 2 ≤ m) :
    sharpChartGap D ≠ chartGapOfDesign D := by
  rw [← chartGapOfDesign_sharpDual_eq_negConjInv D hm, negConjInv, pairRootDiagonal]
  have hentry : ∀ atomIndex : Fin m,
      0 < Real.sqrt (D.weight atomIndex * (1 - D.weight atomIndex)) := by
    intro atomIndex
    have hslack : (0 : ℝ) < 1 - D.weight atomIndex := by
      linarith [weight_lt_one D hm atomIndex]
    exact Real.sqrt_pos.mpr (mul_pos (D.weight_pos atomIndex) hslack)
  have hsize : 0 < m := by omega
  exact negConjInv_ne_self_of_diagonal_pos hsize hentry (chartGapOfDesign_transpose D)
    (isUnit_det_chartGapOfDesign D hm)

end Gtz
