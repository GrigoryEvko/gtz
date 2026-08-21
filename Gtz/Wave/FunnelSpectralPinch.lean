/-
# The funnel gap is a singular plane form: its Cayley-Hamilton law, its inverse
in closed form, and the payment law in four scalars

At a funnel the gap `G = S_T - 1` of the dominator is positive semidefinite AND
SINGULAR: it kills the unit atom `w = g_a`.  So `det G = 0` and the whole
spectrum of `G` is the root set of a QUADRATIC, not a cubic.  This module spends
that fact three times.

## 1. The plane Cayley-Hamilton law

At three-by-three the adjugate is a polynomial in the matrix,

  `adj M = M^2 - (tr M) M + e2 M * 1`     (`Gtz.adjugate_eq_sq_sub_trace_smul`)

with no hypothesis at all.  The landed `Gtz.adjugate_reading_of_unit_null` gives
the adjugate's quadratic form at a unit null probe, and polarization
(`Gtz.eq_of_quadForm_eq`) upgrades that reading to a MATRIX identity:

  **`Gtz.adjugate_eq_smul_atomMatrix_of_unit_null`: `adj G = e2 * w wᵀ`.**

Substituting the first display in the second gives the whole spectral content of
a singular symmetric three-by-three, division-free and eigenvalue-free:

  **`Gtz.mul_self_of_unit_null`: `G * G = tau * G - e2 * (1 - w wᵀ)`** ,

which is two-by-two Cayley-Hamilton on the plane `wᗮ`, carried on a
three-by-three matrix.  Its scalar shadow `Gtz.quadForm_mul_self_of_unit_null` is
the one the pinch consumes.

## 2. The kernel shift, inverted in closed form

`Gtz.KernelSlideDropLaw` evaluates a four-set's inverse form against
`(G + w wᵀ)⁻¹` and carries `IsUnit (kernelShift gap kern).det` as a hypothesis
throughout, because nothing evaluated that inverse.  The plane Cayley-Hamilton
law evaluates it outright:

  **`Gtz.inv_kernelShift_eq`:
  `(G + w wᵀ)⁻¹ = e2⁻¹ * (tau * 1 - G + (e2 - tau) * w wᵀ)`** ,

a POLYNOMIAL in `G`, `tau`, `e2` and `w`.  Invertibility is no longer a
hypothesis but a consequence of `e2 ≠ 0` (`Gtz.isUnit_det_kernelShift`).  Two
readings follow at once: `trace (G + w wᵀ)⁻¹ = 1 + tau / e2`, and every atom's
inverse form is `(tau * leverage - reading) / e2 + (1 - tau / e2) * (v ⬝ᵥ w) ^ 2`.

**THE TWO ROUTES ARE ONE LAW.**  Reading those two into the landed reading cap
turns it, term for term, into the landed funnel payment
(`Gtz.readingCap_iff_payment`, `Gtz.readingCap_sub_eq_payment_sub`): the deficit
of the cap is the deficit of the payment divided by `e2`.  The four-set
determinant route (`Gtz.isTie_funnel_payment`) and the three-drop route
(`Gtz.reading_cap_of_isTie`) carry IDENTICAL information.  A successor must not
spend effort on both.

## 3. The spectral pinch, and the elimination of the gap reading

The payment carries the gap's own reading `s = v ⬝ᵥ (G *ᵥ v)`, which is not one
of the four scalars a floor can bound.  Pair the plane Cayley-Hamilton law
against a probe `h` orthogonal to the kernel and read the result with
Cauchy-Schwarz:

  `‖G h‖ ^ 2 = tau * s - e2 * n` , `s ^ 2 ≤ n * ‖G h‖ ^ 2` ,

hence, with `n = h ⬝ᵥ h` and no eigenvalue and no square root,

  **`Gtz.pinch_of_kernelOrth`: `s ^ 2 - tau * n * s + e2 * n ^ 2 ≤ 0`** .

That single polynomial inequality carries the whole statement "the Rayleigh
quotient of `G` on the plane lies between the two nonzero eigenvalues".  At an
atom `v` the slid probe `h = v - (v ⬝ᵥ w) * w` has `n = leverage - reading ^ 2`
and the SAME gap reading as `v` itself, so the pinch reads in four scalars.

Write the **payment ceiling** `M = leverage * tau - e2 * (reading ^ 2 - 1)`: the
producer fires exactly when `s > M`.  Then the two eliminants of the brief are
not new polynomials at all —

  `K = tau * n - 2 * M`   and   `Q = M ^ 2 - tau * n * M + e2 * n ^ 2` ,

so `Q` is the PINCH POLYNOMIAL evaluated at the payment ceiling.  The producer's
window is `K > 0` and `Q > 0`, and the tie law is its negation.

## 4. What a boundary system must obey

The bridge of section 2 runs in the other direction too.  The landed reading cap
holds at EVERY corank-one weak dominator of a boundary system, with no unit atom
and at any size, and both of its inverse ingredients now evaluate
(`Gtz.triple_inverseForm_sum_of_unit_null` reads the summed shifted form as
`3 + tau / e2`).  So the payment law itself generalizes off the funnel:

  **`Gtz.payment_law_of_isTie`: `e2 * (reading ^ 2 - 1) ≤ leverage * tau - s`
  at every corank-one weak dominator of every boundary system.**

Eliminating `s` with the pinch gives the four-scalar law, likewise with no
funnel hypothesis (`Gtz.isTie_pinch_law`, and `Gtz.isTie_funnel_pinch_law` and
`Gtz.isTie_sixThree_funnel_pinch_law` at the funnel): at every atom outside the
dominator that reads the kernel,

  **`tau * n ≤ 2 * M`  or  `M ^ 2 - tau * n * M + e2 * n ^ 2 ≤ 0`** ,

a polynomial law in the four scalars `(e2, tau, leverage, reading ^ 2)` alone.

## 5. What the window needs

The producer's first condition alone forces two things
(`Gtz.trace_lt_secondInvariant_of_window`, `Gtz.one_lt_reading_of_window`):

  **`tau < e2`**   and   **`e2 < reading ^ 2 * (e2 - tau)`, hence `reading ^ 2 > 1`.**

So the window is open only where the squared reading of the kernel exceeds one,
which is exactly where the landed `Gtz.exists_outside_reading_sq_gt_one` puts an
atom of a funnel, and only when the dominator's second invariant beats its own
trace.  Reading `tau / e2 = 1 / lam1 + 1 / lam2`, that second condition says the
two nonzero eigenvalues satisfy `1 / lam1 + 1 / lam2 < 1`.  Two further scalar
facts fall out of the pinch alone: `Gtz.four_mul_secondInvariant_le_trace_sq_of_unit_null`
(`4 * e2 ≤ tau ^ 2`, the two nonzero eigenvalues are real, with no spectral
theorem) and `Gtz.isTie_funnel_ceiling_nonneg` (the payment ceiling of a
boundary system is never negative).

[MEASURED FIRST, then proved.  The five identities of sections 1 and 2 hold to
`6.9e-11` over 200000 random symmetric forms with a unit null vector.  The cap
and the payment agree to `2.2e-11` over 300000 draws.  The eigenvalue form of the
window implies the producer's payment hypothesis at 16197 of 300000 draws with
ZERO failures, and the root-free window agrees with it at every draw.

THE WINDOW IS NOT VACUOUS, AND IT IS EXACTLY WEIGHT-BOUND.  Over 251581 funnel
`(6,3)` designs built by exact rank-two closure the window fires at 35.5 percent
of them.  But minimizing the best triple's `lambda_min` SUBJECT TO the window
never firing gives `0.345, 0.103, 0.0527, 0.0176, 0.0083` at smallest-weight
floors `0.10, 0.05, 0.02, 0.01, 0.003`: the residual is LINEAR in the smallest
weight, near `2.6` times it.  This is the campaign's universal obstruction, not
a defect of the law.  The `(5,3)` diamond has leverages `2, 13/4, 13/4, 13/4,
13/4` and no unit atom, so it is an ALL-HEAVY tie and does not test this branch.]
-/
import Gtz.Wave.KernelSlideDropLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. Polarization -/

/-- **A SYMMETRIC MATRIX IS ITS OWN QUADRATIC FORM.**  Two symmetric matrices
with the same quadratic form are equal.  Polarization on the sum, then evaluation
at the standard basis. -/
theorem eq_of_quadForm_eq {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = A) (hB : Bᵀ = B)
    (h : ∀ v : Fin n → ℝ, v ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (B *ᵥ v)) : A = B := by
  have hcross : ∀ u v : Fin n → ℝ, u ⬝ᵥ (A *ᵥ v) = u ⬝ᵥ (B *ᵥ v) := by
    intro u v
    have hsA : v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := by
      have hmove := dotProduct_mulVec_transpose A v u
      rw [hA] at hmove
      rw [← hmove, dotProduct_comm]
    have hsB : v ⬝ᵥ (B *ᵥ u) = u ⬝ᵥ (B *ᵥ v) := by
      have hmove := dotProduct_mulVec_transpose B v u
      rw [hB] at hmove
      rw [← hmove, dotProduct_comm]
    have huv := h (u + v)
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct] at huv
    have hu := h u
    have hv := h v
    linarith [huv, hu, hv, hsA, hsB]
  ext i j
  simpa using hcross (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))

/-! ## 2. The adjugate of a three-by-three, in trace vocabulary -/

/-- **THE ADJUGATE IS A POLYNOMIAL IN THE MATRIX.**  At three-by-three,

  `adj M = M ^ 2 - (tr M) M + e2 M * 1` .

No symmetry, no positivity, no rank: an entry identity.  This is the shape that
makes Cayley-Hamilton usable, because `M * adj M = det M * 1`. -/
theorem adjugate_eq_sq_sub_trace_smul (form : Matrix (Fin 3) (Fin 3) ℝ) :
    form.adjugate = form * form - Matrix.trace form • form
      + secondInvariantOfThree form • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.trace_fin_three, secondInvariantOfThree] <;> ring

/-- The adjugate of a symmetric matrix is symmetric. -/
theorem adjugate_transpose_eq {n : ℕ} {form : Matrix (Fin n) (Fin n) ℝ}
    (hsym : formᵀ = form) : form.adjugateᵀ = form.adjugate := by
  rw [Matrix.adjugate_transpose, hsym]

/-! ## 3. The plane Cayley-Hamilton law -/

/-- **THE ADJUGATE OF A SINGULAR SYMMETRIC FORM IS ITS KERNEL ATOM.**  A
symmetric three-by-three form with a unit null probe has

  `adj form = e2 * w wᵀ` .

The landed `Gtz.adjugate_reading_of_unit_null` gives the quadratic form of the
adjugate at every vector, and both sides are symmetric, so polarization closes
the matrix statement.  The corpus carried only the reading. -/
theorem adjugate_eq_smul_atomMatrix_of_unit_null {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) :
    form.adjugate = secondInvariantOfThree form • atomMatrix w := by
  refine eq_of_quadForm_eq (adjugate_transpose_eq hsym) ?_ ?_
  · rw [Matrix.transpose_smul, transpose_eq_of_isHermitian (posSemidef_atomMatrix w).1]
  · intro v
    rw [adjugate_reading_of_unit_null hsym hnull hunit v, Matrix.smul_mulVec,
      atomMatrix, vecMulVec_mulVec_eq, smul_smul, dotProduct_smul, smul_eq_mul,
      dotProduct_comm w v]
    ring

/-- **THE PLANE CAYLEY-HAMILTON LAW.**  A symmetric three-by-three form with a
unit null probe satisfies

  `form * form = tau * form - e2 * (1 - w wᵀ)` ,

with `tau` its trace and `e2` its second invariant.  On the plane `wᗮ` this is
the two-by-two Cayley-Hamilton identity of the form's restriction, whose trace is
`tau` and whose determinant is `e2` because the third eigenvalue is zero.  No
eigenvalue, no square root, no diagonalization. -/
theorem mul_self_of_unit_null {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) :
    form * form = Matrix.trace form • form
      - secondInvariantOfThree form • ((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix w) := by
  have hpoly := adjugate_eq_sq_sub_trace_smul form
  have hker := adjugate_eq_smul_atomMatrix_of_unit_null hsym hnull hunit
  rw [hpoly] at hker
  linear_combination (norm := module) hker

/-- **THE PLANE CAYLEY-HAMILTON LAW, ON A VECTOR.** -/
theorem mulVec_mulVec_of_unit_null {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (v : Fin 3 → ℝ) :
    form *ᵥ (form *ᵥ v)
      = Matrix.trace form • (form *ᵥ v) - secondInvariantOfThree form • v
        + (secondInvariantOfThree form * (w ⬝ᵥ v)) • w := by
  have hmat := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M *ᵥ v)
    (mul_self_of_unit_null hsym hnull hunit)
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, atomMatrix,
    vecMulVec_mulVec_eq] at hmat
  rw [Matrix.mulVec_mulVec, hmat]
  module

/-- **THE PLANE CAYLEY-HAMILTON LAW, AS A SCALAR.**  This is the reading the
spectral pinch consumes: the form's squared reading of a vector, in the form's
own trace and second invariant plus the squared reading of the probe. -/
theorem quadForm_mul_self_of_unit_null {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (v : Fin 3 → ℝ) :
    v ⬝ᵥ (form *ᵥ (form *ᵥ v))
      = Matrix.trace form * (v ⬝ᵥ (form *ᵥ v)) - secondInvariantOfThree form * (v ⬝ᵥ v)
        + secondInvariantOfThree form * (v ⬝ᵥ w) ^ 2 := by
  rw [mulVec_mulVec_of_unit_null hsym hnull hunit v, dotProduct_add, dotProduct_sub,
    dotProduct_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, dotProduct_comm w v]
  ring

/-! ## 4. The kernel shift, inverted in closed form -/

/-- A matrix times a rank-one atom is the rank-one product of the image with the
atom's vector. -/
theorem mul_atomMatrix_eq {k : ℕ} (form : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ) :
    form * atomMatrix v = Matrix.vecMulVec (form *ᵥ v) v := by
  ext i j
  simp only [Matrix.mul_apply, atomMatrix, Matrix.vecMulVec_apply, Matrix.mulVec,
    dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- A rank-one atom times a matrix, likewise. -/
theorem atomMatrix_mul_eq {k : ℕ} (form : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ) :
    atomMatrix v * form = Matrix.vecMulVec v (formᵀ *ᵥ v) := by
  ext i j
  simp only [Matrix.mul_apply, atomMatrix, Matrix.vecMulVec_apply, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The atom of a unit vector is idempotent. -/
theorem atomMatrix_mul_self_of_unit {k : ℕ} {w : Fin k → ℝ} (hunit : w ⬝ᵥ w = 1) :
    atomMatrix w * atomMatrix w = atomMatrix w := by
  rw [mul_atomMatrix_eq, atomMatrix, vecMulVec_mulVec_eq, hunit, one_smul]

/-- **THE CLOSED FORM OF THE KERNEL SHIFT'S INVERSE.**  The restored gap
`G + w wᵀ` has a POLYNOMIAL inverse:

  `e2⁻¹ * (tau * 1 - G + (e2 - tau) * w wᵀ)` .

`Gtz.KernelSlideDropLaw` reads every four-set drop against this matrix and never
evaluated it.  On the plane it is the pseudo-inverse `(tau * 1 - G) / e2`, which
is the plane Cayley-Hamilton law read backwards, and on the kernel it is the
identity. -/
noncomputable def kernelShiftInverse (form : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (secondInvariantOfThree form)⁻¹ •
    (Matrix.trace form • (1 : Matrix (Fin 3) (Fin 3) ℝ) - form
      + (secondInvariantOfThree form - Matrix.trace form) • atomMatrix w)

/-- **THE CLOSED FORM IS A RIGHT INVERSE.** -/
theorem kernelShift_mul_kernelShiftInverse {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : secondInvariantOfThree form ≠ 0) :
    kernelShift form w * kernelShiftInverse form w = 1 := by
  have hzeroR : form * atomMatrix w = 0 := by
    rw [mul_atomMatrix_eq, hnull, Matrix.zero_vecMulVec]
  have hzeroL : atomMatrix w * form = 0 := by
    rw [atomMatrix_mul_eq, hsym, hnull, Matrix.vecMulVec_zero]
  have hidem := atomMatrix_mul_self_of_unit hunit
  have hch := mul_self_of_unit_null hsym hnull hunit
  have hcore : (form + atomMatrix w)
      * (Matrix.trace form • (1 : Matrix (Fin 3) (Fin 3) ℝ) - form
        + (secondInvariantOfThree form - Matrix.trace form) • atomMatrix w)
      = secondInvariantOfThree form • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.mul_one, hzeroR, hzeroL, hidem, hch]
    module
  rw [kernelShift, kernelShiftInverse, Matrix.mul_smul, hcore, smul_smul,
    inv_mul_cancel₀ he, one_smul]

/-- **THE KERNEL SHIFT IS INVERTIBLE.**  Its determinant is a unit whenever the
second invariant does not vanish.  `Gtz.KernelSlideDropLaw` carried this as a
hypothesis at every statement. -/
theorem isUnit_det_kernelShift {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : secondInvariantOfThree form ≠ 0) :
    IsUnit (kernelShift form w).det := by
  exact Matrix.isUnit_det_of_right_inverse
    (kernelShift_mul_kernelShiftInverse hsym hnull hunit he)

/-- **THE INVERSE, EVALUATED.** -/
theorem inv_kernelShift_eq {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : secondInvariantOfThree form ≠ 0) :
    (kernelShift form w)⁻¹ = kernelShiftInverse form w :=
  Matrix.inv_eq_right_inv (kernelShift_mul_kernelShiftInverse hsym hnull hunit he)

/-- **THE INVERSE FORM OF THE KERNEL SHIFT AT ANY VECTOR.**  Its three
ingredients are the atom's leverage, the gap's own reading of the atom, and the
atom's squared reading of the kernel.  Every matrix inverse is gone. -/
theorem inverseForm_kernelShift {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : secondInvariantOfThree form ≠ 0) (v : Fin 3 → ℝ) :
    v ⬝ᵥ ((kernelShift form w)⁻¹ *ᵥ v)
      = (Matrix.trace form * leverageOf v - v ⬝ᵥ (form *ᵥ v)
          + (secondInvariantOfThree form - Matrix.trace form) * (v ⬝ᵥ w) ^ 2)
        / secondInvariantOfThree form := by
  have hlev : v ⬝ᵥ v = leverageOf v := dotProduct_self_eq_leverage v
  rw [inv_kernelShift_eq hsym hnull hunit he, kernelShiftInverse]
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul,
    dotProduct_add, dotProduct_sub, smul_eq_mul, smul_smul, dotProduct_comm w v,
    hlev]
  field_simp

/-- **THE TRACE OF THE INVERTED KERNEL SHIFT.**  It is `1 + tau / e2`: the
kernel direction contributes exactly one, and the plane contributes the sum of
the reciprocals of the two nonzero eigenvalues. -/
theorem trace_inv_kernelShift {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : secondInvariantOfThree form ≠ 0) :
    Matrix.trace ((kernelShift form w)⁻¹)
      = 1 + Matrix.trace form / secondInvariantOfThree form := by
  have hlev : leverageOf w = 1 := by rw [← dotProduct_self_eq_leverage]; exact hunit
  rw [inv_kernelShift_eq hsym hnull hunit he, kernelShiftInverse, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, trace_atomMatrix, hlev]
  simp only [smul_eq_mul, Fintype.card_fin]
  push_cast
  field_simp
  ring

/-! ## 5. The reading cap and the payment are ONE inequality -/

/-- **THE DEFICIT OF THE CAP IS THE DEFICIT OF THE PAYMENT.**  Written out, the
landed `Gtz.reading_cap_of_refusals` at a corank-one gap and the landed
`Gtz.isTie_funnel_payment` are the same inequality scaled by the second
invariant.  Everything on the left is inverse data and everything on the right is
polynomial. -/
theorem readingCap_sub_eq_payment_sub {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : secondInvariantOfThree form ≠ 0) (v : Fin 3 → ℝ) :
    secondInvariantOfThree form
        * ((3 - Matrix.trace ((kernelShift form w)⁻¹)) * (v ⬝ᵥ w) ^ 2
          - (1 + v ⬝ᵥ ((kernelShift form w)⁻¹ *ᵥ v)))
      = secondInvariantOfThree form * ((v ⬝ᵥ w) ^ 2 - 1)
        - (leverageOf v * Matrix.trace form - v ⬝ᵥ (form *ᵥ v)) := by
  rw [trace_inv_kernelShift hsym hnull hunit he,
    inverseForm_kernelShift hsym hnull hunit he]
  field_simp
  ring

/-- **THE CAP HOLDS EXACTLY WHEN THE PAYMENT HOLDS.**  The four-set determinant
route and the three-drop route of `Gtz.KernelSlideDropLaw` carry identical
information at a corank-one dominator. -/
theorem readingCap_iff_payment {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : 0 < secondInvariantOfThree form) (v : Fin 3 → ℝ) :
    ((3 - Matrix.trace ((kernelShift form w)⁻¹)) * (v ⬝ᵥ w) ^ 2
        ≤ 1 + v ⬝ᵥ ((kernelShift form w)⁻¹ *ᵥ v))
      ↔ secondInvariantOfThree form * ((v ⬝ᵥ w) ^ 2 - 1)
        ≤ leverageOf v * Matrix.trace form - v ⬝ᵥ (form *ᵥ v) := by
  have hkey := readingCap_sub_eq_payment_sub hsym hnull hunit (ne_of_gt he) v
  constructor
  · intro hcap; nlinarith [hkey, hcap, he]
  · intro hpay; nlinarith [hkey, hpay, he]

/-! ## 6. The spectral pinch -/

/-- The squared length of the gap's image at a probe orthogonal to the kernel,
with no eigenvalue: the plane Cayley-Hamilton law paired against the probe. -/
theorem normSq_mulVec_of_kernelOrth {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) {h : Fin 3 → ℝ} (horth : h ⬝ᵥ w = 0) :
    (form *ᵥ h) ⬝ᵥ (form *ᵥ h)
      = Matrix.trace form * (h ⬝ᵥ (form *ᵥ h))
        - secondInvariantOfThree form * (h ⬝ᵥ h) := by
  have hmove := dotProduct_mulVec_transpose form (form *ᵥ h) h
  rw [hsym] at hmove
  have hfold : (form *ᵥ h) ⬝ᵥ (form *ᵥ h) = h ⬝ᵥ (form *ᵥ (form *ᵥ h)) := by
    rw [← hmove, dotProduct_comm]
  rw [hfold, quadForm_mul_self_of_unit_null hsym hnull hunit h, horth]
  ring

/-- **THE SPECTRAL PINCH.**  For a probe orthogonal to the kernel, with
`n = h ⬝ᵥ h` and `s = h ⬝ᵥ (form *ᵥ h)`,

  `s ^ 2 - tau * n * s + e2 * n ^ 2 ≤ 0` .

Cauchy-Schwarz against the plane Cayley-Hamilton law.  This one polynomial
inequality says that the Rayleigh quotient `s / n` lies between the two nonzero
eigenvalues, with no eigenvalue named and no square root taken.  No positivity
hypothesis is used. -/
theorem pinch_of_kernelOrth {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) {h : Fin 3 → ℝ} (horth : h ⬝ᵥ w = 0) :
    (h ⬝ᵥ (form *ᵥ h)) ^ 2
        - Matrix.trace form * (h ⬝ᵥ h) * (h ⬝ᵥ (form *ᵥ h))
        + secondInvariantOfThree form * (h ⬝ᵥ h) ^ 2 ≤ 0 := by
  have hcs := dotProduct_sq_le_mul h (form *ᵥ h)
  have hn := normSq_mulVec_of_kernelOrth hsym hnull hunit horth
  rw [hn] at hcs
  nlinarith [hcs]

/-! ## 7. The pinch at an atom, in four scalars -/

/-- The probe of an atom: the atom slid off the kernel. -/
noncomputable def kernelPart (v w : Fin 3 → ℝ) : Fin 3 → ℝ := v - (v ⬝ᵥ w) • w

theorem kernelPart_dotProduct_kernel {v w : Fin 3 → ℝ} (hunit : w ⬝ᵥ w = 1) :
    kernelPart v w ⬝ᵥ w = 0 := by
  rw [kernelPart, sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit, mul_one, sub_self]

/-- The slid probe's squared length is the leverage less the squared reading. -/
theorem kernelPart_normSq {v w : Fin 3 → ℝ} (hunit : w ⬝ᵥ w = 1) :
    kernelPart v w ⬝ᵥ kernelPart v w = leverageOf v - (v ⬝ᵥ w) ^ 2 := by
  have hlev : v ⬝ᵥ v = leverageOf v := dotProduct_self_eq_leverage v
  simp only [kernelPart, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, dotProduct_comm w v, hunit, hlev]
  ring

/-- The gap reads the slid probe exactly as it reads the atom, because it kills
the kernel and is symmetric. -/
theorem kernelPart_gap_reading {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0) (v : Fin 3 → ℝ) :
    kernelPart v w ⬝ᵥ (form *ᵥ kernelPart v w) = v ⬝ᵥ (form *ᵥ v) := by
  have hmove := dotProduct_mulVec_transpose form w v
  rw [hsym] at hmove
  have hleft : w ⬝ᵥ (form *ᵥ v) = 0 := by
    rw [← hmove, hnull]; simp
  rw [kernelPart, Matrix.mulVec_sub, Matrix.mulVec_smul, hnull, smul_zero, sub_zero,
    sub_dotProduct, smul_dotProduct, smul_eq_mul, hleft, mul_zero, sub_zero]

/-- The plane norm of an atom against the kernel. -/
noncomputable def planeNormSq (v w : Fin 3 → ℝ) : ℝ := leverageOf v - (v ⬝ᵥ w) ^ 2

/-- **THE PINCH AT AN ATOM.**  In the four scalars `e2`, `tau`, the leverage and
the squared reading, with the gap's own reading of the atom as the unknown. -/
theorem atom_pinch {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (v : Fin 3 → ℝ) :
    (v ⬝ᵥ (form *ᵥ v)) ^ 2
        - Matrix.trace form * planeNormSq v w * (v ⬝ᵥ (form *ᵥ v))
        + secondInvariantOfThree form * planeNormSq v w ^ 2 ≤ 0 := by
  have hp := pinch_of_kernelOrth hsym hnull hunit (kernelPart_dotProduct_kernel (v := v) hunit)
  rw [kernelPart_gap_reading hsym hnull v, kernelPart_normSq hunit] at hp
  rw [planeNormSq]
  exact hp

/-- The plane norm of an atom is nonnegative: Cauchy-Schwarz at a unit kernel. -/
theorem planeNormSq_nonneg {v w : Fin 3 → ℝ} (hunit : w ⬝ᵥ w = 1) :
    0 ≤ planeNormSq v w := by
  rw [planeNormSq, ← kernelPart_normSq hunit, dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-! ## 8. The elimination: the producer's window -/

/-- **THE PAYMENT CEILING.**  The producer of `Gtz.exists_star_posDef_of_payment_lt`
fires exactly when the gap's reading of the atom EXCEEDS this number. -/
noncomputable def paymentCeiling (form : Matrix (Fin 3) (Fin 3) ℝ) (v w : Fin 3 → ℝ) : ℝ :=
  leverageOf v * Matrix.trace form - secondInvariantOfThree form * ((v ⬝ᵥ w) ^ 2 - 1)

/-- **THE PINCH POLYNOMIAL**, evaluated anywhere.  The pinch says it is
nonpositive at the gap's true reading, and the producer's window says it is
positive at the payment ceiling. -/
noncomputable def pinchPoly (form : Matrix (Fin 3) (Fin 3) ℝ) (norm point : ℝ) : ℝ :=
  point ^ 2 - Matrix.trace form * norm * point + secondInvariantOfThree form * norm ^ 2

/-- **THE ELIMINATION, AS ONE SCALAR STEP.**  A quantity pinched by a quadratic
is strictly above any point at which that quadratic is strictly positive and
which lies left of the vertex. -/
theorem lt_of_pinch_of_window {c d x point : ℝ}
    (hpinch : x ^ 2 - c * x + d ≤ 0) (hpos : 0 < point ^ 2 - c * point + d)
    (hleft : 2 * point < c) : point < x := by
  by_contra hcon
  push Not at hcon
  nlinarith [hpinch, hpos, hleft, hcon]

/-- **THE PAYMENT, FROM THE WINDOW.**  If the payment ceiling lies left of the
pinch's vertex and the pinch polynomial is strictly positive there, then the
producer's payment hypothesis holds.  The gap's own reading has been eliminated:
what is left is a polynomial condition in `e2`, `tau`, the leverage and the
squared reading. -/
theorem payment_lt_of_window {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) {v : Fin 3 → ℝ}
    (hleft : 2 * paymentCeiling form v w
      < Matrix.trace form * planeNormSq v w)
    (hpos : 0 < pinchPoly form (planeNormSq v w) (paymentCeiling form v w)) :
    leverageOf v * Matrix.trace form - v ⬝ᵥ (form *ᵥ v)
      < secondInvariantOfThree form * ((v ⬝ᵥ w) ^ 2 - 1) := by
  have hp := atom_pinch hsym hnull hunit v
  have hstep := lt_of_pinch_of_window
    (c := Matrix.trace form * planeNormSq v w)
    (d := secondInvariantOfThree form * planeNormSq v w ^ 2)
    (x := v ⬝ᵥ (form *ᵥ v)) (point := paymentCeiling form v w)
    (by linarith [hp]) (by rw [pinchPoly] at hpos; linarith [hpos]) hleft
  rw [paymentCeiling] at hstep
  linarith [hstep]

/-- **THE PRODUCER IN FOUR SCALARS.**  A funnel dominator's gap, an atom whose
window is open, and a strictly dominating triple in the star of that atom.  The
gap's reading of the atom never appears. -/
theorem exists_star_posDef_of_window
    {G : Matrix (Fin 3) (Fin 3) ℝ} (hpsd : G.PosSemidef)
    {w : Fin 3 → ℝ} (hnull : G *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1)
    (he : 0 < secondInvariantOfThree G)
    {x y z v : Fin 3 → ℝ}
    (hG : G = atomMatrix x + atomMatrix y + atomMatrix z - 1)
    (hread : v ⬝ᵥ w ≠ 0)
    (hleft : 2 * paymentCeiling G v w < Matrix.trace G * planeNormSq v w)
    (hpos : 0 < pinchPoly G (planeNormSq v w) (paymentCeiling G v w)) :
    (atomMatrix v + atomMatrix y + atomMatrix z - 1).PosDef
      ∨ (atomMatrix v + atomMatrix x + atomMatrix z - 1).PosDef
      ∨ (atomMatrix v + atomMatrix x + atomMatrix y - 1).PosDef := by
  have hsym : Gᵀ = G := (by simpa using hpsd.isHermitian : G.IsSymm)
  exact exists_star_posDef_of_payment_lt hpsd hnull hunit he hG hread
    (payment_lt_of_window hsym hnull hunit hleft hpos)

/-! ## 9. The window at a design -/

/-- **THE WINDOW PRODUCER AT A DESIGN.** -/
theorem funnel_exists_strict_of_window (D : WeightedDesign m 3)
    {a x y z p : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    (hunit : leverageOf (D.atom a) = 1)
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ D.atom a = D.atom a)
    (he : 0 < pairMinorTotal (D.atom x) (D.atom y) (D.atom z))
    (hread : D.atom p ⬝ᵥ D.atom a ≠ 0)
    (hleft : 2 * paymentCeiling (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          (D.atom p) (D.atom a)
        < Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          * planeNormSq (D.atom p) (D.atom a))
    (hpos : 0 < pinchPoly (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          (planeNormSq (D.atom p) (D.atom a))
          (paymentCeiling (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
            (D.atom p) (D.atom a))) :
    (atomMatrix (D.atom p) + atomMatrix (D.atom y) + atomMatrix (D.atom z) - 1).PosDef
      ∨ (atomMatrix (D.atom p) + atomMatrix (D.atom x)
          + atomMatrix (D.atom z) - 1).PosDef
      ∨ (atomMatrix (D.atom p) + atomMatrix (D.atom x)
          + atomMatrix (D.atom y) - 1).PosDef := by
  have hunit' : D.atom a ⬝ᵥ D.atom a = 1 := by
    rw [dotProduct_self_eq_leverage]; exact hunit
  have hnull : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ D.atom a = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix, sub_self]
  have hsym : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)ᵀ
      = subsetSum D ({x, y, z} : Finset (Fin m)) - 1 :=
    (by simpa using (hdom : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosSemidef).isHermitian :
      (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).IsSymm)
  have hePM : secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
      = pairMinorTotal (D.atom x) (D.atom y) (D.atom z) :=
    secondInvariantOfThree_gap_eq_pairMinorTotal D hxy hxz hyz
  refine funnel_exists_strict_of_payment_lt D hxy hxz hyz hdom hunit hfix he hread ?_
  rw [← hePM]
  exact payment_lt_of_window hsym hnull hunit' hleft hpos

/-- **THE FUNNEL PINCH LAW.**  At a boundary system no triple dominates
strictly, so the producer's window is SHUT at every atom outside the dominator
that reads the unit atom:

  `tau * n ≤ 2 * M`  or  `M ^ 2 - tau * n * M + e2 * n ^ 2 ≤ 0` ,

with `M` the payment ceiling and `n` the atom's plane norm.  This is a
polynomial law in `e2`, `tau`, the atom's leverage and its squared reading of the
unit atom, with the gap's own reading of the atom ELIMINATED. -/
theorem isTie_funnel_pinch_law (D : WeightedDesign m 3) (htie : IsTie D)
    {a x y z p : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    (hunit : leverageOf (D.atom a) = 1)
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ D.atom a = D.atom a)
    (he : 0 < pairMinorTotal (D.atom x) (D.atom y) (D.atom z))
    (hread : D.atom p ⬝ᵥ D.atom a ≠ 0) :
    Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          * planeNormSq (D.atom p) (D.atom a)
        ≤ 2 * paymentCeiling (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
            (D.atom p) (D.atom a)
      ∨ pinchPoly (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          (planeNormSq (D.atom p) (D.atom a))
          (paymentCeiling (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
            (D.atom p) (D.atom a)) ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hleft, hpos⟩ := hcon
  have hstrict := funnel_exists_strict_of_window D hxy hxz hyz hdom hunit hfix he hread
    hleft (lt_of_le_of_ne (le_of_not_gt (fun hh => absurd hh (not_lt.mpr hpos.le)))
      (fun hh => absurd hh.symm (ne_of_gt hpos)))
  have hkill : ∀ u v w : Fin m, u ≠ v → u ≠ w → v ≠ w →
      ¬ (atomMatrix (D.atom u) + atomMatrix (D.atom v)
          + atomMatrix (D.atom w) - 1).PosDef := by
    intro u v w huv huw hvw hposd
    refine htie.2 ({u, v, w} : Finset (Fin m)) (card_triple_eq huv huw hvw) ?_
    rwa [subsetSum_triple_atoms D huv huw hvw]
  rcases hstrict with h | h | h
  · exact hkill p y z hpy hpz hyz h
  · exact hkill p x z hpx hpz hxz h
  · exact hkill p x y hpx hpy hxy h

/-- **THE PAYMENT CEILING OF A FUNNEL BOUNDARY SYSTEM IS NONNEGATIVE.**  A
clean corollary of the pinch law: at every atom outside the dominator,

  `e2 * (reading ^ 2 - 1) ≤ leverage * tau` .

Neither branch of the pinch law lets the ceiling go negative, because the plane
norm and the trace are both nonnegative at a weak dominator. -/
theorem isTie_funnel_ceiling_nonneg (D : WeightedDesign m 3) (htie : IsTie D)
    {a x y z p : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    (hunit : leverageOf (D.atom a) = 1)
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ D.atom a = D.atom a)
    (he : 0 < pairMinorTotal (D.atom x) (D.atom y) (D.atom z))
    (hread : D.atom p ⬝ᵥ D.atom a ≠ 0) :
    0 ≤ paymentCeiling (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
      (D.atom p) (D.atom a) := by
  have hunit' : D.atom a ⬝ᵥ D.atom a = 1 := by
    rw [dotProduct_self_eq_leverage]; exact hunit
  have hpsd : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosSemidef := hdom
  have hn : 0 ≤ planeNormSq (D.atom p) (D.atom a) := planeNormSq_nonneg hunit'
  have htr : 0 ≤ Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) :=
    trace_nonneg_of_posSemidef hpsd
  have hePM : secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
      = pairMinorTotal (D.atom x) (D.atom y) (D.atom z) :=
    secondInvariantOfThree_gap_eq_pairMinorTotal D hxy hxz hyz
  have hlaw := isTie_funnel_pinch_law D htie hxy hxz hyz hpx hpy hpz hdom hunit hfix he hread
  have he2 : 0 < secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) := by
    rw [hePM]; exact he
  rcases hlaw with hbranch | hbranch
  · linarith [hbranch, mul_nonneg htr hn]
  · rw [pinchPoly] at hbranch
    by_contra hneg
    push Not at hneg
    nlinarith [hbranch, mul_nonneg (mul_nonneg htr hn) (neg_nonneg.mpr hneg.le),
      mul_nonneg he2.le (sq_nonneg (planeNormSq (D.atom p) (D.atom a))),
      mul_pos_of_neg_of_neg hneg hneg]

/-! ## 10. The landed reading cap, made polynomial -/

/-- **THE CLOSED FORM IS A LEFT INVERSE TOO**, and its product with the gap is the
projection off the kernel. -/
theorem kernelShiftInverse_mul_self {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : secondInvariantOfThree form ≠ 0) :
    kernelShiftInverse form w * form
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix w := by
  have hzeroL : atomMatrix w * form = 0 := by
    rw [atomMatrix_mul_eq, hsym, hnull, Matrix.vecMulVec_zero]
  have hch := mul_self_of_unit_null hsym hnull hunit
  have hcore : (Matrix.trace form • (1 : Matrix (Fin 3) (Fin 3) ℝ) - form
        + (secondInvariantOfThree form - Matrix.trace form) • atomMatrix w) * form
      = secondInvariantOfThree form
        • ((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix w) := by
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
      hzeroL, hch]
    module
  rw [kernelShiftInverse, Matrix.smul_mul, hcore, smul_smul, inv_mul_cancel₀ he,
    one_smul]

/-- **THE SUMMED SHIFTED FORM OF A CORANK-ONE DOMINATOR, EVALUATED.**  The
quantity `Gtz.reading_cap_of_refusals` leaves abstract is `3 + tau / e2`, so the
cap's coefficient `5 - sum` is exactly `2 - tau / e2`. -/
theorem triple_inverseForm_sum_of_unit_null {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : secondInvariantOfThree form ≠ 0)
    {ga gb gc : Fin 3 → ℝ}
    (hS : atomMatrix ga + atomMatrix gb + atomMatrix gc = form + 1) :
    ga ⬝ᵥ ((kernelShift form w)⁻¹ *ᵥ ga) + gb ⬝ᵥ ((kernelShift form w)⁻¹ *ᵥ gb)
        + gc ⬝ᵥ ((kernelShift form w)⁻¹ *ᵥ gc)
      = 3 + Matrix.trace form / secondInvariantOfThree form := by
  have hlev : leverageOf w = 1 := by rw [← dotProduct_self_eq_leverage]; exact hunit
  have hN := inv_kernelShift_eq hsym hnull hunit he
  have hsum : ga ⬝ᵥ ((kernelShift form w)⁻¹ *ᵥ ga)
        + gb ⬝ᵥ ((kernelShift form w)⁻¹ *ᵥ gb) + gc ⬝ᵥ ((kernelShift form w)⁻¹ *ᵥ gc)
      = Matrix.trace ((kernelShift form w)⁻¹
          * (atomMatrix ga + atomMatrix gb + atomMatrix gc)) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
      trace_mul_atomMatrix, trace_mul_atomMatrix, trace_mul_atomMatrix]
  rw [hsum, hS, Matrix.mul_add, Matrix.mul_one, Matrix.trace_add, hN,
    kernelShiftInverse_mul_self hsym hnull hunit he, Matrix.trace_sub,
    Matrix.trace_one, trace_atomMatrix, hlev, ← hN,
    trace_inv_kernelShift hsym hnull hunit he]
  simp only [Fintype.card_fin]
  push_cast
  ring

/-- **THE PAYMENT LAW AT EVERY CORANK-ONE WEAK DOMINATOR.**  The landed
`Gtz.reading_cap_of_isTie` reads three drop refusals against a matrix inverse.
The closed form evaluates both of its inverse ingredients, and the result is
exactly the funnel payment — but with NO funnel hypothesis, at ANY size:

  `e2 * (reading ^ 2 - 1) ≤ leverage * tau - gap reading` .

The unit atom and the reproduction are gone.  What is left is a weak dominator
whose gap has corank one and any atom outside it that reads the kernel. -/
theorem payment_law_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z d : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdx : d ≠ x) (hdy : d ≠ y) (hdz : d ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    {kern : Fin 3 → ℝ}
    (hgap : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ kern = 0)
    (hunit : kern ⬝ᵥ kern = 1)
    (he : 0 < secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
    (hread : D.atom d ⬝ᵥ kern ≠ 0) :
    secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
        * ((D.atom d ⬝ᵥ kern) ^ 2 - 1)
      ≤ leverageOf (D.atom d)
          * Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
        - D.atom d ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ D.atom d) := by
  have hpsd : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosSemidef := hdom
  have hsym : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)ᵀ
      = subsetSum D ({x, y, z} : Finset (Fin m)) - 1 :=
    (by simpa using hpsd.isHermitian :
      (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).IsSymm)
  have hS : atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z)
      = (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) + 1 := by
    rw [subsetSum_triple_atoms D hxy hxz hyz]; abel
  have hcap := reading_cap_of_isTie D htie hxy hxz hyz hdx hdy hdz hdom hgap hunit
    (ne_of_gt he) hread
  rw [triple_inverseForm_sum_of_unit_null hsym hgap hunit (ne_of_gt he) hS] at hcap
  refine (readingCap_iff_payment hsym hgap hunit he (D.atom d)).mp ?_
  rw [trace_inv_kernelShift hsym hgap hunit (ne_of_gt he),
    show (3 : ℝ) - (1 + Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
        / secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
      = 5 - (3 + Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
        / secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)) from by ring]
  exact hcap

/-! ## 11. The pinch law at every corank-one weak dominator -/

/-- **THE PINCH LAW, WITH NO FUNNEL.**  At a boundary system, every corank-one
weak dominator and every atom outside it that reads the dominator's kernel obey
the four-scalar law

  `tau * n ≤ 2 * M`  or  `M ^ 2 - tau * n * M + e2 * n ^ 2 ≤ 0` .

No unit atom, no reproduction, no size hypothesis.  The gap's own reading of the
atom has been eliminated by the spectral pinch, and what is left is polynomial in
`e2`, `tau`, the atom's leverage and its squared reading of the kernel. -/
theorem isTie_pinch_law (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z d : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdx : d ≠ x) (hdy : d ≠ y) (hdz : d ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    {kern : Fin 3 → ℝ}
    (hgap : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ kern = 0)
    (hunit : kern ⬝ᵥ kern = 1)
    (he : 0 < secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
    (hread : D.atom d ⬝ᵥ kern ≠ 0) :
    Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          * planeNormSq (D.atom d) kern
        ≤ 2 * paymentCeiling (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
            (D.atom d) kern
      ∨ pinchPoly (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          (planeNormSq (D.atom d) kern)
          (paymentCeiling (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
            (D.atom d) kern) ≤ 0 := by
  have hpsd : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosSemidef := hdom
  have hsym : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)ᵀ
      = subsetSum D ({x, y, z} : Finset (Fin m)) - 1 :=
    (by simpa using hpsd.isHermitian :
      (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).IsSymm)
  have hpay := payment_law_of_isTie D htie hxy hxz hyz hdx hdy hdz hdom hgap hunit he hread
  by_contra hcon
  push Not at hcon
  obtain ⟨hleft, hpos⟩ := hcon
  have hfire := payment_lt_of_window hsym hgap hunit hleft
    (lt_of_le_of_ne (le_of_lt hpos) (Ne.symm (ne_of_gt hpos)))
  linarith [hpay, hfire]

/-! ## 12. What the window needs, in four scalars -/

/-- **THE WINDOW IS SHUT UNLESS THE SECOND INVARIANT BEATS THE TRACE.**  A scalar
statement about the producer's first condition alone.  With `n = lev - read` the
plane norm and `M = lev * tau - e2 * (read - 1)` the payment ceiling,

  `2 * M < tau * n` forces `tau < e2` and `e2 < read * (e2 - tau)` ,

hence `read > 1`.  So the window can only be open at an atom whose squared
reading of the kernel exceeds one, which is exactly where the landed
`Gtz.exists_outside_reading_sq_gt_one` puts an atom of a funnel. -/
theorem trace_lt_secondInvariant_of_window {e2 tau lev read : ℝ}
    (he : 0 < e2) (htr : 0 ≤ tau) (hn : 0 ≤ lev - read) (hR : 0 < read)
    (hleft : 2 * (lev * tau - e2 * (read - 1)) < tau * (lev - read)) :
    tau < e2 ∧ e2 < read * (e2 - tau) := by
  have hkey : e2 < read * (e2 - tau) := by nlinarith [hleft, htr, hn, he]
  refine ⟨?_, hkey⟩
  by_contra hcon
  push Not at hcon
  nlinarith [hkey, hcon, hR, he]

/-- **AND THE READING MUST EXCEED ONE.** -/
theorem one_lt_reading_of_window {e2 tau lev read : ℝ}
    (he : 0 < e2) (htr : 0 ≤ tau) (hn : 0 ≤ lev - read) (hR : 0 < read)
    (hleft : 2 * (lev * tau - e2 * (read - 1)) < tau * (lev - read)) :
    1 < read := by
  obtain ⟨hlt, hkey⟩ := trace_lt_secondInvariant_of_window he htr hn hR hleft
  nlinarith [hkey, htr, he]

/-- **THE WINDOW, AT A GAP.**  The matrix form of the two scalar conditions: an
open window forces the gap's second invariant strictly above its trace. -/
theorem trace_lt_secondInvariant_of_window_gap {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hpsd : form.PosSemidef) {w : Fin 3 → ℝ}
    (hunit : w ⬝ᵥ w = 1) (he : 0 < secondInvariantOfThree form)
    {v : Fin 3 → ℝ} (hread : v ⬝ᵥ w ≠ 0)
    (hleft : 2 * paymentCeiling form v w < Matrix.trace form * planeNormSq v w) :
    Matrix.trace form < secondInvariantOfThree form
      ∧ 1 < (v ⬝ᵥ w) ^ 2 := by
  have htr : 0 ≤ Matrix.trace form := trace_nonneg_of_posSemidef hpsd
  have hn : 0 ≤ leverageOf v - (v ⬝ᵥ w) ^ 2 := planeNormSq_nonneg (v := v) hunit
  have hR : 0 < (v ⬝ᵥ w) ^ 2 := by positivity
  rw [paymentCeiling, planeNormSq] at hleft
  exact ⟨(trace_lt_secondInvariant_of_window he htr hn hR hleft).1,
    one_lt_reading_of_window he htr hn hR hleft⟩

/-! ## 13. The two nonzero eigenvalues are real -/

/-- A unit vector at rank three has a coordinate whose square is below one. -/
theorem exists_coord_sq_lt_one {w : Fin 3 → ℝ} (hunit : w ⬝ᵥ w = 1) :
    ∃ i : Fin 3, (w i) ^ 2 < 1 := by
  by_contra hcon
  push Not at hcon
  have h0 := hcon 0
  have h1 := hcon 1
  have h2 := hcon 2
  have hs : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using hunit
  linarith

/-- **THE DISCRIMINANT OF THE PINCH IS NONNEGATIVE.**  A symmetric three-by-three
form with a unit null probe has `4 * e2 ≤ tau ^ 2`: its two nonzero eigenvalues
are real, read off the pinch at any probe that is not parallel to the kernel.
No spectral theorem is used. -/
theorem four_mul_secondInvariant_le_trace_sq_of_unit_null
    {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) :
    4 * secondInvariantOfThree form ≤ Matrix.trace form ^ 2 := by
  obtain ⟨i, hi⟩ := exists_coord_sq_lt_one hunit
  set v : Fin 3 → ℝ := Pi.single i 1 with hv
  have hlev : leverageOf v = 1 := by
    simp [hv, leverageOf, Pi.single_apply, Finset.sum_ite_eq']
  have hdot : v ⬝ᵥ w = w i := by simp [hv, dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  have hn : planeNormSq v w = 1 - (w i) ^ 2 := by rw [planeNormSq, hlev, hdot]
  have hpos : 0 < planeNormSq v w := by rw [hn]; linarith
  have hp := atom_pinch hsym hnull hunit v
  have hsq := sq_nonneg (v ⬝ᵥ (form *ᵥ v) - Matrix.trace form * planeNormSq v w / 2)
  have hkey : planeNormSq v w ^ 2
      * (4 * secondInvariantOfThree form - Matrix.trace form ^ 2) ≤ 0 := by
    nlinarith [hp, hsq]
  nlinarith [hkey, pow_pos hpos 2]

/-! ## 14. The pinch law at six points -/

/-- **THE FUNNEL PINCH LAW AT `(6,3)`.**  The funnel is supplied by the landed
`Gtz.isTie_sixThree_unitAtom_funnel`, so at six points the law needs only the
unit atom and a nonzero pair minor total. -/
theorem isTie_sixThree_funnel_pinch_law (D : WeightedDesign 6 3) (htie : IsTie D)
    {a : Fin 6} (hunit : leverageOf (D.atom a) = 1) :
    ∃ x y z : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z
      ∧ a ∉ ({x, y, z} : Finset (Fin 6))
      ∧ Dominates D ({x, y, z} : Finset (Fin 6))
      ∧ subsetSum D ({x, y, z} : Finset (Fin 6)) *ᵥ D.atom a = D.atom a
      ∧ ∀ p : Fin 6, p ≠ x → p ≠ y → p ≠ z →
          D.atom p ⬝ᵥ D.atom a ≠ 0 →
          0 < pairMinorTotal (D.atom x) (D.atom y) (D.atom z) →
          (Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
                * planeNormSq (D.atom p) (D.atom a)
              ≤ 2 * paymentCeiling (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
                  (D.atom p) (D.atom a)
            ∨ pinchPoly (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
                (planeNormSq (D.atom p) (D.atom a))
                (paymentCeiling (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
                  (D.atom p) (D.atom a)) ≤ 0) := by
  obtain ⟨T, hcard, havoid, hdom, hfix⟩ := isTie_sixThree_unitAtom_funnel D htie a hunit
  obtain ⟨x, y, z, hxy, hxz, hyz, hT⟩ := Finset.card_eq_three.mp hcard
  subst hT
  exact ⟨x, y, z, hxy, hxz, hyz, havoid, hdom, hfix,
    fun p hpx hpy hpz hread he =>
      isTie_funnel_pinch_law D htie hxy hxz hyz hpx hpy hpz hdom hunit hfix he hread⟩

end Gtz
