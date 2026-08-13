/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.PolarTiltLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The plane whitener and the deletion law

`Gtz.exists_polarCover_margin` hands the polar construction a covering set that
the previous rank selects.  The selection cannot be steered by the weights,
because the previous rank reads the weight vector only through its total.  The
one steering that remains is DELETION: remove one atom from the design that the
previous rank sees, and the covering set it returns cannot contain that atom.

## 1. The whitener is rank one, thus it is elementary

Deleting one atom of weight `t` and vector `v` from a Parseval frame leaves the
form `1 - t * v vᵀ`.  Making it a frame again asks for the inverse square root
of that form.  It is a RANK-ONE perturbation of the identity, thus the root is
explicit and no square root of a matrix is needed:

  `(1 - t v vᵀ)^(-1/2) = 1 + gain * v vᵀ`, `gain = (1/sqrt(1 - t |v|²) - 1)/|v|²`.

`Gtz.shear` is the map `probe ↦ probe + gain * (v ⬝ᵥ probe) * v`.  Three
identities carry the whole file: `Gtz.shear_dotProduct_shear` (the form of a
shear), `Gtz.whiten_dotProduct_delete` (the whitening shear turns the deleted
form back into the plain one) and `Gtz.whiten_unwhiten` (the two shears are
inverse).  Every one of them is polynomial algebra plus one square root.

## 2. The deletion of an atom

`Gtz.deletePairDesign` removes a LIVE atom and a DEAD one (an atom that is
already zero) from a design and renormalizes.  It is a genuine weighted design,
thus the previous rank applies to it verbatim, and its covering set misses both
labels.  `Gtz.exists_deletePairCover` is the cover it returns, with the explicit
factor

  `(1 - weight live * |atom live|²) * (1 - 2 * share) / (1 - weight dead - weight live)`.

## 3. The polar deletion cover

The pole reads as the ZERO atom of the plane restriction, thus the polar cover
and the deletion are ONE application of `Gtz.deletePairDesign`.
`Gtz.exists_polarDeletionCover` is the payoff named by the ledger: the covering
set of the pole's orthogonal hyperplane can be chosen to AVOID ONE NAMED ATOM,
and it still carries a margin exactly when

  `weight drop * planeShadowSq < weight pole + weight drop`.

## 4. What the deletion kills

`Gtz.not_isTie_of_deletableTilt` — a tie cannot carry a deletable atom whose
removal leaves every other label below the tilt budget.
`Gtz.not_isTie_of_singleTiltedLabel` — the stratum with exactly one tilted label
closes outright.  `Gtz.exists_heavy_tilt_of_isTie_of_deletable` is the same law
read forwards: every tie carries a SECOND heavy label at every deletable one.
-/

namespace Gtz

open Matrix Finset

/-! ## Part 1: the shear along an axis

The rank-one whitener is a shear.  Six identities describe it completely, and
each is a two-line computation. -/

section Shear

variable {dim : ℕ}

/-- **THE SHEAR ALONG AN AXIS.**  The linear map `1 + gain * axis axisᵀ`, written
as a function of the probe.  Every whitener of a rank-one deletion is one of
these. -/
def shear (gain : ℝ) (axis probe : Fin dim → ℝ) : Fin dim → ℝ :=
  probe + (gain * (axis ⬝ᵥ probe)) • axis

@[simp] theorem shear_zero_gain (axis probe : Fin dim → ℝ) : shear 0 axis probe = probe := by
  simp [shear]

@[simp] theorem shear_zero_probe (gain : ℝ) (axis : Fin dim → ℝ) :
    shear gain axis (0 : Fin dim → ℝ) = 0 := by
  simp [shear]

@[simp] theorem shear_zero_axis (gain : ℝ) (probe : Fin dim → ℝ) :
    shear gain (0 : Fin dim → ℝ) probe = probe := by
  simp [shear]

/-- The shear read on the left of a dot product. -/
theorem shear_dotProduct (gain : ℝ) (axis probe other : Fin dim → ℝ) :
    (shear gain axis probe) ⬝ᵥ other
      = probe ⬝ᵥ other + gain * (axis ⬝ᵥ probe) * (axis ⬝ᵥ other) := by
  rw [shear, add_dotProduct, smul_dotProduct, smul_eq_mul, mul_assoc]

/-- The shear read on the right of a dot product. -/
theorem dotProduct_shear (gain : ℝ) (axis probe other : Fin dim → ℝ) :
    other ⬝ᵥ (shear gain axis probe)
      = other ⬝ᵥ probe + gain * (axis ⬝ᵥ probe) * (axis ⬝ᵥ other) := by
  rw [shear, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm other axis]

/-- **THE SHEAR IS SELF-ADJOINT.**  This is what lets a cover stated at the
sheared probe be read back at the plain one. -/
theorem shear_dotProduct_comm (gain : ℝ) (axis probe other : Fin dim → ℝ) :
    (shear gain axis probe) ⬝ᵥ other = probe ⬝ᵥ (shear gain axis other) := by
  rw [shear_dotProduct, dotProduct_shear]
  ring

/-- **THE FORM OF A SHEAR.**  The quadratic form the shear transports differs
from the plain one by one rank-one term. -/
theorem shear_dotProduct_shear (gain : ℝ) (axis probe other : Fin dim → ℝ) :
    (shear gain axis probe) ⬝ᵥ (shear gain axis other)
      = probe ⬝ᵥ other
        + (2 * gain + gain ^ 2 * (axis ⬝ᵥ axis)) * ((axis ⬝ᵥ probe) * (axis ⬝ᵥ other)) := by
  rw [shear_dotProduct, dotProduct_shear, dotProduct_shear]
  ring

/-- The axis reads a shear by one scalar factor. -/
theorem dotProduct_shear_axis (gain : ℝ) (axis probe : Fin dim → ℝ) :
    axis ⬝ᵥ (shear gain axis probe) = (1 + gain * (axis ⬝ᵥ axis)) * (axis ⬝ᵥ probe) := by
  rw [dotProduct_shear]
  ring

/-- **THE COMPOSITION LAW.**  Two shears along one axis make a third. -/
theorem shear_shear (leftGain rightGain : ℝ) (axis probe : Fin dim → ℝ) :
    shear leftGain axis (shear rightGain axis probe)
      = shear (leftGain + rightGain + leftGain * rightGain * (axis ⬝ᵥ axis)) axis probe := by
  funext coord
  simp only [shear, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct_add, dotProduct_smul]
  ring

/-- A vector of vanishing self dot product is orthogonal to everything, because
over the reals a vanishing self dot product means the zero vector. -/
theorem dotProduct_eq_zero_of_self_eq_zero {axis : Fin dim → ℝ} (haxis : axis ⬝ᵥ axis = 0)
    (probe : Fin dim → ℝ) : axis ⬝ᵥ probe = 0 := by
  have hzero : axis = 0 := by
    by_contra hne
    exact absurd haxis (ne_of_gt (selfDotProduct_pos hne))
  rw [hzero, zero_dotProduct]

/-- A shear whose gain kills the axis energy is the identity. -/
theorem shear_eq_self_of_gain_mul_self_eq_zero {gain : ℝ} {axis : Fin dim → ℝ}
    (hgain : gain * (axis ⬝ᵥ axis) = 0) (probe : Fin dim → ℝ) :
    shear gain axis probe = probe := by
  rcases mul_eq_zero.mp hgain with hzero | hzero
  · rw [hzero, shear_zero_gain]
  · rw [shear, dotProduct_eq_zero_of_self_eq_zero hzero probe, mul_zero, zero_smul, add_zero]

end Shear

/-! ## Part 2: the whitening gains

The two gains are named functions of the weight and the axis, and both are
divisions by the axis energy.  The Lean convention `x / 0 = 0` makes them
correct at the zero axis with no case split in the definition, and one lemma
each discharges the case split in the proofs. -/

section Whiten

variable {dim : ℕ}

/-- The gain of the WHITENING shear: the one that turns `1 - scale * axis axisᵀ`
back into the identity. -/
noncomputable def whitenGain (scale : ℝ) (axis : Fin dim → ℝ) : ℝ :=
  ((Real.sqrt (1 - scale * (axis ⬝ᵥ axis)))⁻¹ - 1) / (axis ⬝ᵥ axis)

/-- The gain of the UNWHITENING shear, the inverse of the whitening one. -/
noncomputable def unwhitenGain (scale : ℝ) (axis : Fin dim → ℝ) : ℝ :=
  (Real.sqrt (1 - scale * (axis ⬝ᵥ axis)) - 1) / (axis ⬝ᵥ axis)

variable {scale : ℝ} {axis : Fin dim → ℝ}

/-- The deletion deficit has a positive square root exactly below saturation. -/
theorem sqrt_deficit_pos (hunsat : scale * (axis ⬝ᵥ axis) < 1) :
    0 < Real.sqrt (1 - scale * (axis ⬝ᵥ axis)) :=
  Real.sqrt_pos.mpr (by linarith)

theorem sq_sqrt_deficit (hunsat : scale * (axis ⬝ᵥ axis) < 1) :
    Real.sqrt (1 - scale * (axis ⬝ᵥ axis)) ^ 2 = 1 - scale * (axis ⬝ᵥ axis) :=
  Real.sq_sqrt (by linarith)

/-- **THE WHITENING GAIN, CLEARED OF ITS DENOMINATOR.**  This one identity
removes every division from the file. -/
theorem whitenGain_mul_self (scale : ℝ) (axis : Fin dim → ℝ) :
    whitenGain scale axis * (axis ⬝ᵥ axis)
      = (Real.sqrt (1 - scale * (axis ⬝ᵥ axis)))⁻¹ - 1 := by
  by_cases hzero : axis ⬝ᵥ axis = 0
  · simp [whitenGain, hzero]
  · rw [whitenGain, div_mul_cancel₀ _ hzero]

/-- The unwhitening gain, cleared of its denominator. -/
theorem unwhitenGain_mul_self (scale : ℝ) (axis : Fin dim → ℝ) :
    unwhitenGain scale axis * (axis ⬝ᵥ axis)
      = Real.sqrt (1 - scale * (axis ⬝ᵥ axis)) - 1 := by
  by_cases hzero : axis ⬝ᵥ axis = 0
  · simp [unwhitenGain, hzero]
  · rw [unwhitenGain, div_mul_cancel₀ _ hzero]

/-- **THE UNWHITENING SHEAR REALIZES THE DELETED FORM.**  Reading the plain dot
product at the unwhitened probes gives the form with one atom removed. -/
theorem unwhiten_dotProduct (hunsat : scale * (axis ⬝ᵥ axis) < 1) (probe other : Fin dim → ℝ) :
    (shear (unwhitenGain scale axis) axis probe) ⬝ᵥ (shear (unwhitenGain scale axis) axis other)
      = probe ⬝ᵥ other - scale * ((axis ⬝ᵥ probe) * (axis ⬝ᵥ other)) := by
  set energy : ℝ := axis ⬝ᵥ axis with henergy
  set gain : ℝ := unwhitenGain scale axis with hgain
  set root : ℝ := Real.sqrt (1 - scale * energy) with hroot
  have hgainMul : gain * energy = root - 1 := unwhitenGain_mul_self scale axis
  have hrootSq : root ^ 2 = 1 - scale * energy := sq_sqrt_deficit hunsat
  rw [shear_dotProduct_shear]
  have hcoeff : (2 * gain + gain ^ 2 * energy) * ((axis ⬝ᵥ probe) * (axis ⬝ᵥ other))
      = -scale * ((axis ⬝ᵥ probe) * (axis ⬝ᵥ other)) := by
    by_cases hzero : energy = 0
    · rw [dotProduct_eq_zero_of_self_eq_zero (by rw [← henergy]; exact hzero) probe]
      ring
    · have hexpand : (2 * gain + gain ^ 2 * energy) * energy
          = 2 * (gain * energy) + (gain * energy) ^ 2 := by ring
      rw [hgainMul] at hexpand
      have hvalue : 2 * (root - 1) + (root - 1) ^ 2 = -scale * energy := by nlinarith [hrootSq]
      rw [hvalue] at hexpand
      rw [mul_right_cancel₀ hzero hexpand]
  rw [hcoeff]
  ring

/-- **THE TWO SHEARS ARE INVERSE.** -/
theorem whiten_unwhiten (hunsat : scale * (axis ⬝ᵥ axis) < 1) (probe : Fin dim → ℝ) :
    shear (whitenGain scale axis) axis (shear (unwhitenGain scale axis) axis probe) = probe := by
  set energy : ℝ := axis ⬝ᵥ axis with henergy
  set root : ℝ := Real.sqrt (1 - scale * energy) with hroot
  have hrootPos : 0 < root := sqrt_deficit_pos hunsat
  have hwhite : whitenGain scale axis * energy = root⁻¹ - 1 := whitenGain_mul_self scale axis
  have hunwhite : unwhitenGain scale axis * energy = root - 1 := unwhitenGain_mul_self scale axis
  rw [shear_shear]
  refine shear_eq_self_of_gain_mul_self_eq_zero ?_ probe
  rw [← henergy]
  have hexpand : (whitenGain scale axis + unwhitenGain scale axis
        + whitenGain scale axis * unwhitenGain scale axis * energy) * energy
      = whitenGain scale axis * energy + unwhitenGain scale axis * energy
        + (whitenGain scale axis * energy) * (unwhitenGain scale axis * energy) := by ring
  rw [hexpand, hwhite, hunwhite]
  have hrootNe : root ≠ 0 := ne_of_gt hrootPos
  field_simp
  ring

/-- **THE WHITENING SHEAR REMOVES THE DELETED ATOM.**  Reading the DELETED form
at the whitened probes gives the plain dot product back.  This is the Parseval
identity of the deleted design. -/
theorem whiten_dotProduct_delete (hunsat : scale * (axis ⬝ᵥ axis) < 1)
    (probe other : Fin dim → ℝ) :
    (shear (whitenGain scale axis) axis probe) ⬝ᵥ (shear (whitenGain scale axis) axis other)
        - scale * ((axis ⬝ᵥ shear (whitenGain scale axis) axis probe)
            * (axis ⬝ᵥ shear (whitenGain scale axis) axis other))
      = probe ⬝ᵥ other := by
  set energy : ℝ := axis ⬝ᵥ axis with henergy
  set gain : ℝ := whitenGain scale axis with hgain
  set root : ℝ := Real.sqrt (1 - scale * energy) with hroot
  have hrootPos : 0 < root := sqrt_deficit_pos hunsat
  have hrootSq : root ^ 2 = 1 - scale * energy := sq_sqrt_deficit hunsat
  have hgainMul : gain * energy = root⁻¹ - 1 := whitenGain_mul_self scale axis
  rw [shear_dotProduct_shear, dotProduct_shear_axis, dotProduct_shear_axis]
  have hcoeff : (2 * gain + gain ^ 2 * energy) * ((axis ⬝ᵥ probe) * (axis ⬝ᵥ other))
      = scale * ((1 + gain * energy) * (axis ⬝ᵥ probe) * ((1 + gain * energy) * (axis ⬝ᵥ other))) := by
    by_cases hzero : energy = 0
    · rw [dotProduct_eq_zero_of_self_eq_zero (by rw [← henergy]; exact hzero) probe]
      ring
    · have hrootNe : root ≠ 0 := ne_of_gt hrootPos
      have hkappaRoot : root⁻¹ * root = 1 := inv_mul_cancel₀ hrootNe
      have hsqNe : root ^ 2 ≠ 0 := pow_ne_zero 2 hrootNe
      have hvalue : 2 * (root⁻¹ - 1) + (root⁻¹ - 1) ^ 2 = scale * energy * root⁻¹ ^ 2 := by
        refine mul_right_cancel₀ hsqNe ?_
        have hleftVal : (2 * (root⁻¹ - 1) + (root⁻¹ - 1) ^ 2) * root ^ 2
            = (root⁻¹ * root) ^ 2 - root ^ 2 := by ring
        have hrightVal : scale * energy * root⁻¹ ^ 2 * root ^ 2
            = scale * energy * (root⁻¹ * root) ^ 2 := by ring
        rw [hleftVal, hrightVal, hkappaRoot, hrootSq]
        ring
      have hshape : (2 * gain + gain ^ 2 * energy) * energy
          = scale * (1 + gain * energy) ^ 2 * energy := by
        have hleftVal : (2 * gain + gain ^ 2 * energy) * energy
            = 2 * (gain * energy) + (gain * energy) ^ 2 := by ring
        have hrightVal : scale * (1 + gain * energy) ^ 2 * energy
            = scale * energy * (1 + gain * energy) ^ 2 := by ring
        rw [hleftVal, hrightVal, hgainMul]
        have hkappa : (1 : ℝ) + (root⁻¹ - 1) = root⁻¹ := by ring
        rw [hkappa]
        exact hvalue
      have hfinal : 2 * gain + gain ^ 2 * energy = scale * (1 + gain * energy) ^ 2 :=
        mul_right_cancel₀ hzero hshape
      rw [hfinal]
      ring
  rw [hcoeff]
  ring

end Whiten

/-! ## Part 3: Parseval from the bilinear form

The `isParseval` field of a weighted design is a matrix identity.  Every design
built in this file is described by its BILINEAR form, thus one constructor turns
a bilinear identity into the matrix one. -/

/-- **PARSEVAL FROM THE BILINEAR FORM.**  A family of atoms and weights whose
weighted bilinear form is the dot product resolves the identity. -/
theorem isParseval_of_bilinear {size dim : ℕ} {atoms : Fin size → Fin dim → ℝ}
    {weights : Fin size → ℝ}
    (hform : ∀ leftVec rightVec : Fin dim → ℝ,
      ∑ c, weights c * ((atoms c ⬝ᵥ leftVec) * (atoms c ⬝ᵥ rightVec)) = leftVec ⬝ᵥ rightVec) :
    ∑ c, weights c • atomMatrix (atoms c) = (1 : Matrix (Fin dim) (Fin dim) ℝ) := by
  ext rowIndex colIndex
  have hread := hform (Pi.single rowIndex 1) (Pi.single colIndex 1)
  simp only [dotProduct_single, mul_one] at hread
  rw [Matrix.sum_apply, Matrix.one_apply]
  rw [Finset.sum_congr rfl fun c _ => (by
    simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul] :
      (weights c • atomMatrix (atoms c)) rowIndex colIndex
        = weights c * (atoms c rowIndex * atoms c colIndex))]
  rw [hread, Pi.single_apply]
  by_cases heq : rowIndex = colIndex
  · rw [if_pos heq, if_pos heq.symm]
  · rw [if_neg heq, if_neg (fun hswap : colIndex = rowIndex => heq hswap.symm)]

/-! ## Part 4: the deletion of one atom from a design

A design that already carries a ZERO atom admits the deletion of any other atom
that stays strictly below the leverage cap.  The zero atom is the pole of the
polar construction, read against a frame of its own orthogonal hyperplane.

The two deleted labels keep a positive `share` of the weight so that the result
is a genuine design.  Every remaining atom shrinks by one common scalar, and the
shrink is what makes the returned cover STRICT. -/

section DeletePair

variable {size dim : ℕ}

/-- The squared shrink factor of the deleted design.  It is below one exactly
when the two deleted labels keep less weight than they had. -/
noncomputable def deleteScaleSq (D : WeightedDesign size dim) (dead live : Fin size)
    (share : ℝ) : ℝ :=
  (1 - D.weight dead - D.weight live) / (1 - 2 * share)

/-- **THE DELETED DESIGN.**  The design with one dead atom and one live atom
removed: the live atom is whitened away by a shear, the two labels keep the
share `share` each, and every remaining atom is renormalized. -/
noncomputable def deletePairDesign (D : WeightedDesign size dim) (dead live : Fin size)
    (share : ℝ) (hne : live ≠ dead) (hdead : D.atom dead = 0)
    (hshare : 0 < share) (hshareLt : 2 * share < D.weight dead + D.weight live)
    (hpairLt : D.weight dead + D.weight live < 1)
    (hunsat : D.weight live * (D.atom live ⬝ᵥ D.atom live) < 1) :
    WeightedDesign size dim where
  atom := fun label =>
    if label = dead then 0
    else if label = live then 0
    else Real.sqrt (deleteScaleSq D dead live share)
      • shear (whitenGain (D.weight live) (D.atom live)) (D.atom live) (D.atom label)
  weight := fun label =>
    if label = dead then share
    else if label = live then share
    else D.weight label * ((1 - 2 * share) / (1 - D.weight dead - D.weight live))
  weight_pos := by
    intro label
    have hfree : (0 : ℝ) < 1 - D.weight dead - D.weight live := by linarith
    have hnum : (0 : ℝ) < 1 - 2 * share := by
      have := D.weight_pos dead
      have := D.weight_pos live
      linarith
    by_cases hlabelDead : label = dead
    · rw [if_pos hlabelDead]; exact hshare
    · rw [if_neg hlabelDead]
      by_cases hlabelLive : label = live
      · rw [if_pos hlabelLive]; exact hshare
      · rw [if_neg hlabelLive]
        exact mul_pos (D.weight_pos label) (div_pos hnum hfree)
  weight_sum_one := by
    classical
    have hfree : (0 : ℝ) < 1 - D.weight dead - D.weight live := by linarith
    have hfreeNe : (1 : ℝ) - D.weight dead - D.weight live ≠ 0 := ne_of_gt hfree
    have hmass : ∑ label ∈ (Finset.univ.erase dead).erase live, D.weight label
        = 1 - D.weight dead - D.weight live := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ live⟩),
        Finset.sum_erase_eq_sub (Finset.mem_univ dead), D.weight_sum_one]
    have hsplit : ∑ label, (if label = dead then share
          else if label = live then share
          else D.weight label * ((1 - 2 * share) / (1 - D.weight dead - D.weight live)))
        = share + share + ∑ label ∈ (Finset.univ.erase dead).erase live,
            D.weight label * ((1 - 2 * share) / (1 - D.weight dead - D.weight live)) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ dead), if_pos rfl,
        ← Finset.add_sum_erase (Finset.univ.erase dead) _
          (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ live⟩),
        if_neg hne, if_pos rfl, ← add_assoc]
      refine congrArg (share + share + ·) (Finset.sum_congr rfl fun label hlabel => ?_)
      have hlive : label ≠ live := Finset.ne_of_mem_erase hlabel
      have hdeadNe : label ≠ dead := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hlabel)
      rw [if_neg hdeadNe, if_neg hlive]
    rw [hsplit, ← Finset.sum_mul, hmass]
    field_simp
    ring
  isParseval := by
    classical
    have hfree : (0 : ℝ) < 1 - D.weight dead - D.weight live := by linarith
    have hnum : (0 : ℝ) < 1 - 2 * share := by
      have := D.weight_pos dead
      have := D.weight_pos live
      linarith
    have hscalePos : 0 < deleteScaleSq D dead live share := div_pos hfree hnum
    have hscaleSq : Real.sqrt (deleteScaleSq D dead live share) ^ 2
        = deleteScaleSq D dead live share := Real.sq_sqrt hscalePos.le
    refine isParseval_of_bilinear fun leftVec rightVec => ?_
    set gain : ℝ := whitenGain (D.weight live) (D.atom live) with hgainDef
    set leftShear : Fin dim → ℝ := shear gain (D.atom live) leftVec with hleftShear
    set rightShear : Fin dim → ℝ := shear gain (D.atom live) rightVec with hrightShear
    -- every surviving term reads the ORIGINAL atom against the sheared probes
    have hterm : ∀ label : Fin size, label ≠ dead → label ≠ live →
        (if label = dead then (0 : Fin dim → ℝ)
            else if label = live then 0
            else Real.sqrt (deleteScaleSq D dead live share)
              • shear gain (D.atom live) (D.atom label)) ⬝ᵥ leftVec
          = Real.sqrt (deleteScaleSq D dead live share) * (D.atom label ⬝ᵥ leftShear) := by
      intro label hlabelDead hlabelLive
      rw [if_neg hlabelDead, if_neg hlabelLive, smul_dotProduct, smul_eq_mul,
        shear_dotProduct_comm, hleftShear]
    have htermRight : ∀ label : Fin size, label ≠ dead → label ≠ live →
        (if label = dead then (0 : Fin dim → ℝ)
            else if label = live then 0
            else Real.sqrt (deleteScaleSq D dead live share)
              • shear gain (D.atom live) (D.atom label)) ⬝ᵥ rightVec
          = Real.sqrt (deleteScaleSq D dead live share) * (D.atom label ⬝ᵥ rightShear) := by
      intro label hlabelDead hlabelLive
      rw [if_neg hlabelDead, if_neg hlabelLive, smul_dotProduct, smul_eq_mul,
        shear_dotProduct_comm, hrightShear]
    -- drop the two deleted labels, then rewrite the rest
    have hreduce : ∑ label, (if label = dead then share
            else if label = live then share
            else D.weight label * ((1 - 2 * share) / (1 - D.weight dead - D.weight live)))
          * (((if label = dead then (0 : Fin dim → ℝ)
                else if label = live then 0
                else Real.sqrt (deleteScaleSq D dead live share)
                  • shear gain (D.atom live) (D.atom label)) ⬝ᵥ leftVec)
            * ((if label = dead then (0 : Fin dim → ℝ)
                else if label = live then 0
                else Real.sqrt (deleteScaleSq D dead live share)
                  • shear gain (D.atom live) (D.atom label)) ⬝ᵥ rightVec))
        = ∑ label ∈ (Finset.univ.erase dead).erase live,
            D.weight label * ((D.atom label ⬝ᵥ leftShear) * (D.atom label ⬝ᵥ rightShear)) := by
      have hvanish : ∀ label ∈ Finset.univ,
          label ∉ (Finset.univ.erase dead).erase live →
          (if label = dead then share
              else if label = live then share
              else D.weight label * ((1 - 2 * share) / (1 - D.weight dead - D.weight live)))
            * (((if label = dead then (0 : Fin dim → ℝ)
                  else if label = live then 0
                  else Real.sqrt (deleteScaleSq D dead live share)
                    • shear gain (D.atom live) (D.atom label)) ⬝ᵥ leftVec)
              * ((if label = dead then (0 : Fin dim → ℝ)
                  else if label = live then 0
                  else Real.sqrt (deleteScaleSq D dead live share)
                    • shear gain (D.atom live) (D.atom label)) ⬝ᵥ rightVec)) = 0 := by
        intro label _ hout
        by_cases hlabelDead : label = dead
        · simp [hlabelDead]
        · have hlabelLive : label = live := by
            by_contra hlive
            exact hout (Finset.mem_erase.mpr ⟨hlive,
              Finset.mem_erase.mpr ⟨hlabelDead, Finset.mem_univ label⟩⟩)
          simp [hlabelLive, hne]
      rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ.erase dead).erase live)) hvanish]
      refine Finset.sum_congr rfl fun label hlabel => ?_
      have hlive : label ≠ live := Finset.ne_of_mem_erase hlabel
      have hdeadNe : label ≠ dead := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hlabel)
      rw [if_neg hdeadNe, if_neg hlive, hterm label hdeadNe hlive,
        htermRight label hdeadNe hlive]
      have hshape : Real.sqrt (deleteScaleSq D dead live share) * (D.atom label ⬝ᵥ leftShear)
            * (Real.sqrt (deleteScaleSq D dead live share) * (D.atom label ⬝ᵥ rightShear))
          = Real.sqrt (deleteScaleSq D dead live share) ^ 2
            * ((D.atom label ⬝ᵥ leftShear) * (D.atom label ⬝ᵥ rightShear)) := by ring
      rw [hshape, hscaleSq, deleteScaleSq]
      field_simp
    rw [hreduce]
    -- the erased sum is the full Parseval sum minus the two deleted terms
    have hfull : ∑ label ∈ (Finset.univ.erase dead).erase live,
          D.weight label * ((D.atom label ⬝ᵥ leftShear) * (D.atom label ⬝ᵥ rightShear))
        = leftShear ⬝ᵥ rightShear
          - D.weight live * ((D.atom live ⬝ᵥ leftShear) * (D.atom live ⬝ᵥ rightShear)) := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ live⟩),
        Finset.sum_erase_eq_sub (Finset.mem_univ dead),
        ← dotProduct_eq_sum_weight_mul_pair D leftShear rightShear, hdead]
      simp
    rw [hfull, hleftShear, hrightShear, hgainDef]
    exact whiten_dotProduct_delete hunsat leftVec rightVec

/-- The weight of a surviving label of the deleted design. -/
theorem deletePairDesign_weight_of_ne (D : WeightedDesign size dim) {dead live : Fin size}
    {share : ℝ} (hne : live ≠ dead) (hdead : D.atom dead = 0)
    (hshare : 0 < share) (hshareLt : 2 * share < D.weight dead + D.weight live)
    (hpairLt : D.weight dead + D.weight live < 1)
    (hunsat : D.weight live * (D.atom live ⬝ᵥ D.atom live) < 1)
    {label : Fin size} (hlabelDead : label ≠ dead) (hlabelLive : label ≠ live) :
    (deletePairDesign D dead live share hne hdead hshare hshareLt hpairLt hunsat).weight label
      = D.weight label * ((1 - 2 * share) / (1 - D.weight dead - D.weight live)) := by
  show (if label = dead then share
      else if label = live then share
      else D.weight label * ((1 - 2 * share) / (1 - D.weight dead - D.weight live))) = _
  rw [if_neg hlabelDead, if_neg hlabelLive]

/-- The atom of a deleted label of the deleted design vanishes. -/
theorem deletePairDesign_atom_dead (D : WeightedDesign size dim) {dead live : Fin size}
    {share : ℝ} (hne : live ≠ dead) (hdead : D.atom dead = 0)
    (hshare : 0 < share) (hshareLt : 2 * share < D.weight dead + D.weight live)
    (hpairLt : D.weight dead + D.weight live < 1)
    (hunsat : D.weight live * (D.atom live ⬝ᵥ D.atom live) < 1) :
    (deletePairDesign D dead live share hne hdead hshare hshareLt hpairLt hunsat).atom dead = 0 := by
  show (if dead = dead then (0 : Fin dim → ℝ) else _) = 0
  rw [if_pos rfl]

theorem deletePairDesign_atom_live (D : WeightedDesign size dim) {dead live : Fin size}
    {share : ℝ} (hne : live ≠ dead) (hdead : D.atom dead = 0)
    (hshare : 0 < share) (hshareLt : 2 * share < D.weight dead + D.weight live)
    (hpairLt : D.weight dead + D.weight live < 1)
    (hunsat : D.weight live * (D.atom live ⬝ᵥ D.atom live) < 1) :
    (deletePairDesign D dead live share hne hdead hshare hshareLt hpairLt hunsat).atom live = 0 := by
  show (if live = dead then (0 : Fin dim → ℝ) else if live = live then 0 else _) = 0
  rw [if_neg hne, if_pos rfl]

/-- The atom of a surviving label, read against a probe: the shear moves to the
probe, because a shear is self-adjoint. -/
theorem deletePairDesign_atom_dotProduct (D : WeightedDesign size dim) {dead live : Fin size}
    {share : ℝ} (hne : live ≠ dead) (hdead : D.atom dead = 0)
    (hshare : 0 < share) (hshareLt : 2 * share < D.weight dead + D.weight live)
    (hpairLt : D.weight dead + D.weight live < 1)
    (hunsat : D.weight live * (D.atom live ⬝ᵥ D.atom live) < 1)
    {label : Fin size} (hlabelDead : label ≠ dead) (hlabelLive : label ≠ live)
    (probe : Fin dim → ℝ) :
    (deletePairDesign D dead live share hne hdead hshare hshareLt hpairLt hunsat).atom label
        ⬝ᵥ probe
      = Real.sqrt (deleteScaleSq D dead live share)
        * (D.atom label ⬝ᵥ shear (whitenGain (D.weight live) (D.atom live)) (D.atom live) probe) := by
  show ((if label = dead then (0 : Fin dim → ℝ)
      else if label = live then 0
      else Real.sqrt (deleteScaleSq D dead live share)
        • shear (whitenGain (D.weight live) (D.atom live)) (D.atom live) (D.atom label))
        ⬝ᵥ probe) = _
  rw [if_neg hlabelDead, if_neg hlabelLive, smul_dotProduct, smul_eq_mul, shear_dotProduct_comm]

end DeletePair

/-! ## Part 5: the cover the deletion returns

The previous rank applies to the deleted design verbatim, thus its covering set
misses both deleted labels.  Transporting the cover back through the
unwhitening shear costs exactly one Cauchy-Schwarz step, and the loss is the
deleted atom's own energy. -/

section DeleteCover

variable {size dim : ℕ}

/-- Cauchy-Schwarz for the dot product of real coordinate vectors. -/
theorem dotProduct_sq_le_mul_self (leftVec rightVec : Fin dim → ℝ) :
    (leftVec ⬝ᵥ rightVec) ^ 2 ≤ (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) := by
  have hraw := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin dim))
    (fun i => leftVec i) (fun i => rightVec i)
  have hcross : leftVec ⬝ᵥ rightVec = ∑ i, leftVec i * rightVec i := rfl
  have hleft : leftVec ⬝ᵥ leftVec = ∑ i, leftVec i ^ 2 :=
    Finset.sum_congr rfl fun i _ => (pow_two (leftVec i)).symm
  have hright : rightVec ⬝ᵥ rightVec = ∑ i, rightVec i ^ 2 :=
    Finset.sum_congr rfl fun i _ => (pow_two (rightVec i)).symm
  rw [hcross, hleft, hright]
  exact hraw

/-- **THE DELETION COVER.**  Under the previous rank, every design with a dead
atom and an unsaturated live atom carries `dim` OTHER atoms that cover the
identity with the explicit factor

  `(1 - weight live * |atom live|²) * (1 - 2 * share) / (1 - weight dead - weight live)`.

The covering set misses BOTH named labels.  This is the deletion tool: the
selection of the previous rank can be forced away from one named atom. -/
theorem exists_deletePairCover (hpredecessor : GtzWeightedAll dim)
    (D : WeightedDesign size dim) {dead live : Fin size} (hne : live ≠ dead)
    (hdead : D.atom dead = 0) (hroom : dim + 2 ≤ size)
    {share : ℝ} (hshare : 0 < share) (hshareLt : 2 * share < D.weight dead + D.weight live)
    (hpairLt : D.weight dead + D.weight live < 1)
    (hunsat : D.weight live * (D.atom live ⬝ᵥ D.atom live) < 1) :
    ∃ covering : Finset (Fin size), covering.card = dim ∧ dead ∉ covering ∧ live ∉ covering
      ∧ ∀ probe : Fin dim → ℝ,
          ((1 - D.weight live * (D.atom live ⬝ᵥ D.atom live))
              * ((1 - 2 * share) / (1 - D.weight dead - D.weight live)))
              * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ covering, (D.atom label ⬝ᵥ probe) ^ 2 := by
  classical
  have hfree : (0 : ℝ) < 1 - D.weight dead - D.weight live := by linarith
  have hnum : (0 : ℝ) < 1 - 2 * share := by
    have := D.weight_pos dead
    have := D.weight_pos live
    linarith
  have hscalePos : 0 < deleteScaleSq D dead live share := div_pos hfree hnum
  have hscaleSq : Real.sqrt (deleteScaleSq D dead live share) ^ 2
      = deleteScaleSq D dead live share := Real.sq_sqrt hscalePos.le
  set deleted := deletePairDesign D dead live share hne hdead hshare hshareLt hpairLt hunsat
    with hdeleted
  obtain ⟨rawCovering, hrawCard, hrawDominates⟩ := hpredecessor size deleted
  -- pad the raw covering inside the complement of the two deleted labels
  set forbidden : Finset (Fin size) := {dead, live} with hforbidden
  have hforbiddenCard : forbidden.card = 2 := by
    rw [hforbidden, Finset.card_insert_of_notMem (by simpa using fun h => hne h.symm),
      Finset.card_singleton]
  have hcomplementCard : (Finset.univ \ forbidden).card = size - 2 := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin, hforbiddenCard]
  have hsubset : rawCovering \ forbidden ⊆ Finset.univ \ forbidden :=
    Finset.sdiff_subset_sdiff (Finset.subset_univ _) (le_refl _)
  have hsmallCard : (rawCovering \ forbidden).card ≤ dim :=
    le_trans (Finset.card_le_card Finset.sdiff_subset) (le_of_eq hrawCard)
  have hbigCard : dim ≤ (Finset.univ \ forbidden).card := by rw [hcomplementCard]; omega
  obtain ⟨covering, hcoverSup, hcoverSub, hcoverCard⟩ :=
    Finset.exists_subsuperset_card_eq hsubset hsmallCard hbigCard
  have hdeadNotMem : dead ∉ covering := fun hmem => by
    have := (Finset.mem_sdiff.mp (hcoverSub hmem)).2
    exact this (by rw [hforbidden]; exact Finset.mem_insert_self _ _)
  have hliveNotMem : live ∉ covering := fun hmem => by
    have := (Finset.mem_sdiff.mp (hcoverSub hmem)).2
    exact this (by rw [hforbidden]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine ⟨covering, hcoverCard, hdeadNotMem, hliveNotMem, fun probe => ?_⟩
  -- read the domination of the deleted design at the UNWHITENED probe
  set unwhitened : Fin dim → ℝ :=
    shear (unwhitenGain (D.weight live) (D.atom live)) (D.atom live) probe with hunwhitened
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hrawDominates).2 unwhitened
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, subsetSum_form, Matrix.one_mulVec] at hform
  have hlength : unwhitened ⬝ᵥ unwhitened
      = probe ⬝ᵥ probe
        - D.weight live * ((D.atom live ⬝ᵥ probe) * (D.atom live ⬝ᵥ probe)) := by
    rw [hunwhitened]
    exact unwhiten_dotProduct hunsat probe probe
  -- the deleted labels contribute nothing, and the rest reads the original atoms
  have hzeroOut : ∀ label ∈ rawCovering, label ∉ rawCovering \ forbidden →
      (deleted.atom label ⬝ᵥ unwhitened) ^ 2 = 0 := by
    intro label hmem hnot
    have hin : label ∈ forbidden := by
      by_contra hout
      exact hnot (Finset.mem_sdiff.mpr ⟨hmem, hout⟩)
    rw [hforbidden] at hin
    rcases Finset.mem_insert.mp hin with heq | heq
    · rw [heq, hdeleted, deletePairDesign_atom_dead, zero_dotProduct]; ring
    · rw [Finset.mem_singleton.mp heq, hdeleted, deletePairDesign_atom_live, zero_dotProduct]
      ring
  have hshrink : ∑ label ∈ rawCovering, (deleted.atom label ⬝ᵥ unwhitened) ^ 2
      = ∑ label ∈ rawCovering \ forbidden, (deleted.atom label ⬝ᵥ unwhitened) ^ 2 :=
    (Finset.sum_subset Finset.sdiff_subset hzeroOut).symm
  have hread : ∀ label ∈ rawCovering \ forbidden,
      (deleted.atom label ⬝ᵥ unwhitened) ^ 2
        = deleteScaleSq D dead live share * (D.atom label ⬝ᵥ probe) ^ 2 := by
    intro label hmem
    have hout : label ∉ forbidden := (Finset.mem_sdiff.mp hmem).2
    have hlabelDead : label ≠ dead := fun heq => hout (by
      rw [hforbidden, heq]; exact Finset.mem_insert_self _ _)
    have hlabelLive : label ≠ live := fun heq => hout (by
      rw [hforbidden, heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [hdeleted, deletePairDesign_atom_dotProduct D hne hdead hshare hshareLt hpairLt hunsat
      hlabelDead hlabelLive, hunwhitened, whiten_unwhiten hunsat, mul_pow, hscaleSq]
  rw [hshrink, Finset.sum_congr rfl hread, ← Finset.mul_sum] at hform
  -- grow the padded covering, then pay the Cauchy-Schwarz step
  have hgrow : ∑ label ∈ rawCovering \ forbidden, (D.atom label ⬝ᵥ probe) ^ 2
      ≤ ∑ label ∈ covering, (D.atom label ⬝ᵥ probe) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hcoverSup fun label _ _ => sq_nonneg _
  have hchain : unwhitened ⬝ᵥ unwhitened
      ≤ deleteScaleSq D dead live share * ∑ label ∈ covering, (D.atom label ⬝ᵥ probe) ^ 2 := by
    have hstep := mul_le_mul_of_nonneg_left hgrow hscalePos.le
    linarith [hform, hstep]
  have hcauchy : (D.atom live ⬝ᵥ probe) ^ 2
      ≤ (D.atom live ⬝ᵥ D.atom live) * (probe ⬝ᵥ probe) :=
    dotProduct_sq_le_mul_self (D.atom live) probe
  have hfloor : (1 - D.weight live * (D.atom live ⬝ᵥ D.atom live)) * (probe ⬝ᵥ probe)
      ≤ unwhitened ⬝ᵥ unwhitened := by
    rw [hlength]
    have hweightPos := D.weight_pos live
    nlinarith [hcauchy, hweightPos]
  have hinverse : ((1 - 2 * share) / (1 - D.weight dead - D.weight live))
      * deleteScaleSq D dead live share = 1 := by
    rw [deleteScaleSq, div_mul_div_comm,
      mul_comm (1 - 2 * share) (1 - D.weight dead - D.weight live)]
    exact div_self (by positivity)
  have hfactorPos : (0 : ℝ) < (1 - 2 * share) / (1 - D.weight dead - D.weight live) :=
    div_pos hnum hfree
  calc ((1 - D.weight live * (D.atom live ⬝ᵥ D.atom live))
        * ((1 - 2 * share) / (1 - D.weight dead - D.weight live))) * (probe ⬝ᵥ probe)
      = ((1 - 2 * share) / (1 - D.weight dead - D.weight live))
        * ((1 - D.weight live * (D.atom live ⬝ᵥ D.atom live)) * (probe ⬝ᵥ probe)) := by ring
    _ ≤ ((1 - 2 * share) / (1 - D.weight dead - D.weight live))
        * (deleteScaleSq D dead live share
          * ∑ label ∈ covering, (D.atom label ⬝ᵥ probe) ^ 2) :=
        mul_le_mul_of_nonneg_left (le_trans hfloor hchain) hfactorPos.le
    _ = ∑ label ∈ covering, (D.atom label ⬝ᵥ probe) ^ 2 := by
        rw [← mul_assoc, hinverse, one_mul]

end DeleteCover

/-! ## Part 6: the plane shadow

The polar construction reads the design against an orthonormal frame of the
pole's orthogonal hyperplane.  The energy an atom keeps there is its own energy
minus the square of its normalized pairing with the pole. -/

variable {size rank : ℕ}

/-- **THE PLANE SHADOW ENERGY.**  The squared length of the component of an atom
orthogonal to the pole. -/
noncomputable def planeShadowSq (design : WeightedDesign size rank) (pole label : Fin size) : ℝ :=
  (design.atom label ⬝ᵥ design.atom label)
    - (design.atom label ⬝ᵥ design.atom pole) ^ 2 / (design.atom pole ⬝ᵥ design.atom pole)

/-- The plane shadow never exceeds the atom's own energy. -/
theorem planeShadowSq_le_leverage (design : WeightedDesign size rank) (pole label : Fin size)
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) :
    planeShadowSq design pole label ≤ design.atom label ⬝ᵥ design.atom label := by
  rw [planeShadowSq]
  have hquotient : 0 ≤ (design.atom label ⬝ᵥ design.atom pole) ^ 2
      / (design.atom pole ⬝ᵥ design.atom pole) := div_nonneg (sq_nonneg _) hpole.le
  linarith

/-- The plane shadow is never negative, by Cauchy-Schwarz. -/
theorem planeShadowSq_nonneg (design : WeightedDesign size rank) (pole label : Fin size)
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) :
    0 ≤ planeShadowSq design pole label := by
  rw [planeShadowSq, sub_nonneg, div_le_iff₀ hpole]
  have hcauchy := dotProduct_sq_le_mul_self (design.atom label) (design.atom pole)
  linarith

/-- **A TILTED ATOM STAYS STRICTLY BELOW THE PLANE CAP.**  The leverage cap of
the design gives the deletion its unsaturation hypothesis for free at every atom
that is not orthogonal to the pole. -/
theorem weight_mul_planeShadowSq_lt_one (design : WeightedDesign size rank)
    {pole label : Fin size} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (htilted : design.atom label ⬝ᵥ design.atom pole ≠ 0) :
    design.weight label * planeShadowSq design pole label < 1 := by
  have hcap := weight_mul_selfDotProduct_le_one design label
  have hweightPos := design.weight_pos label
  have hquotient : 0 < (design.atom label ⬝ᵥ design.atom pole) ^ 2
      / (design.atom pole ⬝ᵥ design.atom pole) :=
    div_pos (by positivity) hpole
  have hshadow : planeShadowSq design pole label
      < design.atom label ⬝ᵥ design.atom label := by
    rw [planeShadowSq]; linarith
  nlinarith [hcap, hweightPos, hshadow]

/-- The unsaturation also holds, non-strictly, at every atom. -/
theorem weight_mul_planeShadowSq_le_one (design : WeightedDesign size rank)
    (pole label : Fin size) (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) :
    design.weight label * planeShadowSq design pole label ≤ 1 := by
  have hcap := weight_mul_selfDotProduct_le_one design label
  have hweightPos := design.weight_pos label
  nlinarith [planeShadowSq_le_leverage design pole label hpole, hweightPos, hcap]

/-- **TWO LABELS NEVER CARRY THE WHOLE WEIGHT.**  A design of at least three
labels leaves a positive free mass outside any two of them. -/
theorem weight_pair_lt_one (design : WeightedDesign size rank) {first second : Fin size}
    (hne : first ≠ second) (hsize : 3 ≤ size) :
    design.weight first + design.weight second < 1 := by
  classical
  have hcard : ((Finset.univ.erase first).erase second).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨fun heq => hne heq.symm, Finset.mem_univ second⟩),
      Finset.card_erase_of_mem (Finset.mem_univ first), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨other, hother⟩ := hcard
  have hotherSecond : other ≠ second := Finset.ne_of_mem_erase hother
  have hotherFirst : other ≠ first := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hother)
  have hmass : design.weight first + design.weight second + design.weight other
      ≤ ∑ label, design.weight label := by
    have hsub : ({first, second, other} : Finset (Fin size)) ⊆ Finset.univ := Finset.subset_univ _
    have hsum : ∑ label ∈ ({first, second, other} : Finset (Fin size)), design.weight label
        = design.weight first + design.weight second + design.weight other := by
      rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (heq | heq)
          · exact hne heq
          · exact hotherFirst heq.symm),
        Finset.sum_insert (by
          simp only [Finset.mem_singleton]
          exact fun heq => hotherSecond heq.symm),
        Finset.sum_singleton, add_assoc]
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun label _ _ => (design.weight_pos label).le
  rw [design.weight_sum_one] at hmass
  linarith [design.weight_pos other]

/-! ## Part 7: the frame reads the shadow

One Parseval identity of the Householder frame turns the frame readings of an
atom into its plane shadow, and it is the only bridge the composition needs. -/

/-- **THE FRAME PARSEVAL, BILINEAR.**  The Householder frame of a unit normal
reads the whole dot product except the normal component. -/
theorem sum_householderFrame_read_mul (hpos : 0 < rank) {unitNormal : Fin rank → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) (leftVec rightVec : Fin rank → ℝ) :
    ∑ index, (leftVec ⬝ᵥ householderFrame hpos unitNormal index)
        * (rightVec ⬝ᵥ householderFrame hpos unitNormal index)
      = leftVec ⬝ᵥ rightVec - (leftVec ⬝ᵥ unitNormal) * (rightVec ⬝ᵥ unitNormal) := by
  classical
  have hflat : ∀ index, unitNormal ⬝ᵥ householderFrame hpos unitNormal index = 0 := by
    intro index
    rw [dotProduct_comm]
    exact householderFrame_dotProduct_normal hpos hunit index
  have hperp : ∀ vec : Fin rank → ℝ,
      (vec - (vec ⬝ᵥ unitNormal) • unitNormal) ⬝ᵥ unitNormal = 0 := by
    intro vec
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit, mul_one, sub_self]
  have hread : ∀ (vec : Fin rank → ℝ) (index : Fin (rank - 1)),
      (vec - (vec ⬝ᵥ unitNormal) • unitNormal) ⬝ᵥ householderFrame hpos unitNormal index
        = vec ⬝ᵥ householderFrame hpos unitNormal index := by
    intro vec index
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, hflat index, mul_zero, sub_zero]
  have hspan := householderFrame_spans hpos hunit (hperp leftVec)
  have hproduct : (leftVec - (leftVec ⬝ᵥ unitNormal) • unitNormal)
        ⬝ᵥ (rightVec - (rightVec ⬝ᵥ unitNormal) • unitNormal)
      = ∑ index, ((leftVec - (leftVec ⬝ᵥ unitNormal) • unitNormal)
            ⬝ᵥ householderFrame hpos unitNormal index)
          * ((rightVec - (rightVec ⬝ᵥ unitNormal) • unitNormal)
            ⬝ᵥ householderFrame hpos unitNormal index) := by
    conv_lhs => rw [hspan]
    rw [sum_dotProduct]
    refine Finset.sum_congr rfl fun index _ => ?_
    rw [smul_dotProduct, smul_eq_mul,
      dotProduct_comm (householderFrame hpos unitNormal index)
        (rightVec - (rightVec ⬝ᵥ unitNormal) • unitNormal)]
  have hexpand : (leftVec - (leftVec ⬝ᵥ unitNormal) • unitNormal)
        ⬝ᵥ (rightVec - (rightVec ⬝ᵥ unitNormal) • unitNormal)
      = leftVec ⬝ᵥ rightVec - (leftVec ⬝ᵥ unitNormal) * (rightVec ⬝ᵥ unitNormal) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hunit, dotProduct_comm unitNormal rightVec]
    ring
  rw [← hexpand, hproduct]
  exact Finset.sum_congr rfl fun index _ => by rw [hread leftVec index, hread rightVec index]

/-! ## Part 8: the polar deletion cover

The pole reads as the ZERO atom of the plane restriction, thus the polar cover
and the deletion are ONE application of `Gtz.deletePairDesign`.  This is the tool
the ledger named: the covering set of the pole's orthogonal hyperplane can be
chosen to AVOID ONE NAMED ATOM. -/

/-- **THE POLAR DELETION COVER.**  Under the previous rank, every design with an
overshooting pole and a named other label carries `rank - 1` atoms, NEITHER of
them the pole NOR the named label, that cover the pole's orthogonal hyperplane
with the explicit factor

  `(1 - weight drop * planeShadowSq) * (1 - 2 * share) / (1 - weight pole - weight drop)`.

The factor beats one exactly when `weight drop * planeShadowSq` stays below
`weight pole + weight drop` and the share is small.  No matrix square root, no
Cholesky and no spectral theorem is spent: the whitener is the rank-one shear
`Gtz.shear`. -/
theorem exists_polarDeletionCover (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole drop : Fin size} (hne : drop ≠ pole)
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hroom : rank + 1 ≤ size)
    {share : ℝ} (hshare : 0 < share)
    (hshareLt : 2 * share < design.weight pole + design.weight drop)
    (hunsat : design.weight drop * planeShadowSq design pole drop < 1) :
    ∃ covering : Finset (Fin size), covering.card = rank - 1
      ∧ pole ∉ covering ∧ drop ∉ covering
      ∧ ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          ((1 - design.weight drop * planeShadowSq design pole drop)
              * ((1 - 2 * share) / (1 - design.weight pole - design.weight drop)))
              * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 := by
  classical
  have hpos : 0 < rank := by omega
  have hsize : 3 ≤ size := by omega
  have hpairLt : design.weight pole + design.weight drop < 1 :=
    weight_pair_lt_one design (fun heq => hne heq.symm) hsize
  have hpoleNe := atom_ne_zero_of_one_lt_selfDotProduct design hlong
  have hleveragePos : (0 : ℝ) < design.atom pole ⬝ᵥ design.atom pole := by linarith
  set unitNormal : Fin rank → ℝ :=
    (Real.sqrt (design.atom pole ⬝ᵥ design.atom pole))⁻¹ • design.atom pole with hunitNormal
  have hunit : unitNormal ⬝ᵥ unitNormal = 1 := unit_of_ne_zero (design.atom pole) hpoleNe
  set frame := householderFrame hpos unitNormal with hframe
  have horthonormal := householderFrame_orthonormal hpos unitNormal
  have hrootPos : 0 < Real.sqrt (design.atom pole ⬝ᵥ design.atom pole) :=
    Real.sqrt_pos.mpr hleveragePos
  have hrootSq : Real.sqrt (design.atom pole ⬝ᵥ design.atom pole) ^ 2
      = design.atom pole ⬝ᵥ design.atom pole := Real.sq_sqrt hleveragePos.le
  have hnormalRead : ∀ vec : Fin rank → ℝ, vec ⬝ᵥ unitNormal
      = (Real.sqrt (design.atom pole ⬝ᵥ design.atom pole))⁻¹ * (vec ⬝ᵥ design.atom pole) := by
    intro vec
    rw [hunitNormal, dotProduct_smul, smul_eq_mul]
  have hpoleFlat : ∀ index, design.atom pole ⬝ᵥ frame index = 0 := by
    intro index
    have hread := householderFrame_dotProduct_normal hpos hunit index
    rw [hnormalRead (householderFrame hpos unitNormal index)] at hread
    rcases mul_eq_zero.mp hread with hinv | hdot
    · exact absurd hinv (by positivity)
    · rw [dotProduct_comm]
      exact hdot
  -- the plane restriction reads the pole as the zero atom
  set restricted := subspaceRestriction design frame horthonormal with hrestricted
  have hdead : restricted.atom pole = 0 := by
    funext index
    exact hpoleFlat index
  have hweightRead : ∀ label : Fin size, restricted.weight label = design.weight label :=
    fun _ => rfl
  have hshadow : restricted.atom drop ⬝ᵥ restricted.atom drop
      = planeShadowSq design pole drop := by
    have hexpand : restricted.atom drop ⬝ᵥ restricted.atom drop
        = ∑ index, (design.atom drop ⬝ᵥ householderFrame hpos unitNormal index)
            * (design.atom drop ⬝ᵥ householderFrame hpos unitNormal index) := rfl
    rw [hexpand, sum_householderFrame_read_mul hpos hunit (design.atom drop) (design.atom drop),
      hnormalRead (design.atom drop), planeShadowSq]
    have hsquare : (Real.sqrt (design.atom pole ⬝ᵥ design.atom pole))⁻¹
          * (design.atom drop ⬝ᵥ design.atom pole)
        * ((Real.sqrt (design.atom pole ⬝ᵥ design.atom pole))⁻¹
          * (design.atom drop ⬝ᵥ design.atom pole))
        = (design.atom drop ⬝ᵥ design.atom pole) ^ 2
          / (Real.sqrt (design.atom pole ⬝ᵥ design.atom pole)) ^ 2 := by
      field_simp
    rw [hsquare, hrootSq]
  -- the deletion of the named label from the plane restriction
  have hunsatRestricted : restricted.weight drop
      * (restricted.atom drop ⬝ᵥ restricted.atom drop) < 1 := by
    rw [hshadow]; exact hunsat
  have hpairRestricted : restricted.weight pole + restricted.weight drop < 1 := hpairLt
  have hshareRestricted : 2 * share < restricted.weight pole + restricted.weight drop :=
    hshareLt
  have hroomRestricted : (rank - 1) + 2 ≤ size := by omega
  obtain ⟨covering, hcard, hpoleNotMem, hdropNotMem, hcover⟩ :=
    exists_deletePairCover hpredecessor restricted hne hdead hroomRestricted hshare
      hshareRestricted hpairRestricted hunsatRestricted
  refine ⟨covering, hcard, hpoleNotMem, hdropNotMem, fun probe hprobe => ?_⟩
  -- transport the cover from the plane coordinates back to the probe
  have hprobeNormal : probe ⬝ᵥ unitNormal = 0 := by
    rw [hnormalRead probe, hprobe, mul_zero]
  set planeProbe : Fin (rank - 1) → ℝ := fun index => probe ⬝ᵥ frame index with hplaneProbe
  have hplaneLength : planeProbe ⬝ᵥ planeProbe = probe ⬝ᵥ probe := by
    have hexpand : planeProbe ⬝ᵥ planeProbe
        = ∑ index, (probe ⬝ᵥ householderFrame hpos unitNormal index)
            * (probe ⬝ᵥ householderFrame hpos unitNormal index) := rfl
    rw [hexpand, sum_householderFrame_read_mul hpos hunit probe probe, hprobeNormal]
    ring
  have hplaneRead : ∀ label : Fin size,
      restricted.atom label ⬝ᵥ planeProbe = design.atom label ⬝ᵥ probe := by
    intro label
    have hexpand : restricted.atom label ⬝ᵥ planeProbe
        = ∑ index, (design.atom label ⬝ᵥ householderFrame hpos unitNormal index)
            * (probe ⬝ᵥ householderFrame hpos unitNormal index) := rfl
    rw [hexpand, sum_householderFrame_read_mul hpos hunit (design.atom label) probe,
      hprobeNormal, mul_zero, sub_zero]
  have hstep := hcover planeProbe
  have hcoeff : (1 - restricted.weight drop * (restricted.atom drop ⬝ᵥ restricted.atom drop))
        * ((1 - 2 * share) / (1 - restricted.weight pole - restricted.weight drop))
      = (1 - design.weight drop * planeShadowSq design pole drop)
        * ((1 - 2 * share) / (1 - design.weight pole - design.weight drop)) := by
    rw [hshadow, hweightRead drop, hweightRead pole]
  rw [hplaneLength, hcoeff] at hstep
  calc ((1 - design.weight drop * planeShadowSq design pole drop)
        * ((1 - 2 * share) / (1 - design.weight pole - design.weight drop))) * (probe ⬝ᵥ probe)
      ≤ ∑ label ∈ covering, (restricted.atom label ⬝ᵥ planeProbe) ^ 2 := hstep
    _ = ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 :=
        Finset.sum_congr rfl fun label _ => by rw [hplaneRead label]

/-! ## Part 9: the deletion factor, the deletion margin, and what they kill

The factor of the polar deletion cover is one named quotient, and the share only
shrinks it linearly.  Thus the sharp criterion needs no limit: the share is
chosen by one minimum. -/

/-- **THE DELETION COVER FACTOR.**  The factor the polar deletion cover carries
at share zero. -/
noncomputable def deletionCoverFactor (design : WeightedDesign size rank)
    (pole drop : Fin size) : ℝ :=
  (1 - design.weight drop * planeShadowSq design pole drop)
    / (1 - design.weight pole - design.weight drop)

/-- **THE DELETION MARGIN.**  The margin the polar deletion cover carries at
share zero.  It is positive exactly at a DELETABLE label. -/
noncomputable def deletionMargin (design : WeightedDesign size rank)
    (pole drop : Fin size) : ℝ :=
  deletionCoverFactor design pole drop - 1

/-- **THE DELETION CONDITION IS THE POSITIVITY OF THE MARGIN.** -/
theorem deletionMargin_pos (design : WeightedDesign size rank) {pole drop : Fin size}
    (hpairLt : design.weight pole + design.weight drop < 1)
    (hdeletable : design.weight drop * planeShadowSq design pole drop
      < design.weight pole + design.weight drop) :
    0 < deletionMargin design pole drop := by
  have hfree : (0 : ℝ) < 1 - design.weight pole - design.weight drop := by linarith
  rw [deletionMargin, deletionCoverFactor, sub_pos, lt_div_iff₀ hfree, one_mul]
  linarith

/-- The deletion cover factor is positive at every deletable label. -/
theorem deletionCoverFactor_pos (design : WeightedDesign size rank) {pole drop : Fin size}
    (hpairLt : design.weight pole + design.weight drop < 1)
    (hdeletable : design.weight drop * planeShadowSq design pole drop
      < design.weight pole + design.weight drop) :
    0 < deletionCoverFactor design pole drop := by
  have hmargin := deletionMargin_pos design hpairLt hdeletable
  rw [deletionMargin] at hmargin
  linarith

/-- A deletable label never saturates the plane cap. -/
theorem deletable_unsaturated (design : WeightedDesign size rank) {pole drop : Fin size}
    (hpairLt : design.weight pole + design.weight drop < 1)
    (hdeletable : design.weight drop * planeShadowSq design pole drop
      < design.weight pole + design.weight drop) :
    design.weight drop * planeShadowSq design pole drop < 1 := by linarith

/-- **A SHORT PLANE SHADOW MAKES A LABEL DELETABLE.**  No hypothesis beyond the
positivity of the weights is spent. -/
theorem deletable_of_planeShadowSq_le_one (design : WeightedDesign size rank)
    (pole drop : Fin size) (hshadow : planeShadowSq design pole drop ≤ 1) :
    design.weight drop * planeShadowSq design pole drop
      < design.weight pole + design.weight drop := by
  have hweightDrop := design.weight_pos drop
  have hweightPole := design.weight_pos pole
  nlinarith [hshadow, hweightDrop, hweightPole]

/-- **THE STRICT DOMINATOR THE DELETION PRODUCES.**  When one label is deletable
and every OTHER label stays below the tilt cap, the pole together with the
deleted cover beats the identity strictly. -/
theorem exists_dominating_of_deletableTilt (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole drop : Fin size} (hne : drop ≠ pole)
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hroom : rank + 1 ≤ size)
    (hdeletable : design.weight drop * planeShadowSq design pole drop
      < design.weight pole + design.weight drop)
    {tiltCap : ℝ}
    (htilt : ∀ label : Fin size, label ≠ pole → label ≠ drop →
      (design.atom label ⬝ᵥ design.atom pole) ^ 2 ≤ tiltCap)
    (hbudget : ((rank : ℝ) - 1) * tiltCap
      < deletionMargin design pole drop * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ∃ selected : Finset (Fin size), selected.card = rank
      ∧ (subsetSum design selected - 1).PosDef := by
  classical
  have hsize : 3 ≤ size := by omega
  have hpairLt : design.weight pole + design.weight drop < 1 :=
    weight_pair_lt_one design (fun heq => hne heq.symm) hsize
  have hfree : (0 : ℝ) < 1 - design.weight pole - design.weight drop := by linarith
  have hfactorPos : 0 < deletionCoverFactor design pole drop :=
    deletionCoverFactor_pos design hpairLt hdeletable
  have hmarginPos : 0 < deletionMargin design pole drop :=
    deletionMargin_pos design hpairLt hdeletable
  have hleveragePos : (0 : ℝ) < design.atom pole ⬝ᵥ design.atom pole := by linarith
  have hgapPos : (0 : ℝ) < (design.atom pole ⬝ᵥ design.atom pole)
      * (design.atom pole ⬝ᵥ design.atom pole - 1) := by nlinarith [hlong, hleveragePos]
  have hpairPos : (0 : ℝ) < design.weight pole + design.weight drop := by
    have := design.weight_pos pole
    have := design.weight_pos drop
    linarith
  -- one minimum picks the share, because the share only shrinks the factor linearly
  set gap : ℝ := deletionMargin design pole drop * (design.atom pole ⬝ᵥ design.atom pole)
      * (design.atom pole ⬝ᵥ design.atom pole - 1) - ((rank : ℝ) - 1) * tiltCap with hgapDef
  have hgap : 0 < gap := by rw [hgapDef]; linarith
  set scaleDown : ℝ := 4 * deletionCoverFactor design pole drop
      * ((design.atom pole ⬝ᵥ design.atom pole)
        * (design.atom pole ⬝ᵥ design.atom pole - 1)) with hscaleDown
  have hscalePos : 0 < scaleDown := by
    rw [hscaleDown]; positivity
  set share : ℝ := min ((design.weight pole + design.weight drop) / 4) (gap / scaleDown)
    with hshareDef
  have hsharePos : 0 < share := by
    rw [hshareDef]
    exact lt_min (by linarith) (div_pos hgap hscalePos)
  have hshareLeWeight : share ≤ (design.weight pole + design.weight drop) / 4 := by
    rw [hshareDef]; exact min_le_left _ _
  have hshareLeGap : share ≤ gap / scaleDown := by rw [hshareDef]; exact min_le_right _ _
  have hshareLt : 2 * share < design.weight pole + design.weight drop := by linarith
  obtain ⟨covering, hcard, hpoleNotMem, hdropNotMem, hcover⟩ :=
    exists_polarDeletionCover hrank hpredecessor design hne hlong hroom hsharePos hshareLt
      (deletable_unsaturated design hpairLt hdeletable)
  -- the achieved margin, and the shape of the achieved factor
  set margin : ℝ := deletionCoverFactor design pole drop * (1 - 2 * share) - 1 with hmarginDef
  have hfactorShape : (1 - design.weight drop * planeShadowSq design pole drop)
      * ((1 - 2 * share) / (1 - design.weight pole - design.weight drop)) = 1 + margin := by
    rw [hmarginDef, deletionCoverFactor]
    field_simp
    ring
  have hspend : 2 * share * (deletionCoverFactor design pole drop
      * ((design.atom pole ⬝ᵥ design.atom pole)
        * (design.atom pole ⬝ᵥ design.atom pole - 1))) ≤ gap / 2 := by
    have hstep : 2 * share * (deletionCoverFactor design pole drop
        * ((design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)))
        = share * scaleDown / 2 := by rw [hscaleDown]; ring
    rw [hstep, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
    calc share * scaleDown ≤ (gap / scaleDown) * scaleDown :=
          mul_le_mul_of_nonneg_right hshareLeGap hscalePos.le
      _ = gap := by field_simp
  have hmarginPosAchieved : 0 < margin := by
    have hbig : 2 * share * (deletionCoverFactor design pole drop
        * ((design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1))) ≤ gap / 2 := hspend
    have hmarginShape : margin = deletionMargin design pole drop
        - 2 * share * deletionCoverFactor design pole drop := by
      rw [hmarginDef, deletionMargin]; ring
    have htiltNonneg : 0 ≤ ((rank : ℝ) - 1) * tiltCap := by
      have hrankCast : (2 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
      have hcapNonneg : 0 ≤ tiltCap := by
        have hchoice : ∃ label : Fin size, label ≠ pole ∧ label ≠ drop := by
          have hcount : ((Finset.univ.erase pole).erase drop).Nonempty := by
            rw [← Finset.card_pos, Finset.card_erase_of_mem
              (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ drop⟩),
              Finset.card_erase_of_mem (Finset.mem_univ pole), Finset.card_univ,
              Fintype.card_fin]
            omega
          obtain ⟨label, hlabel⟩ := hcount
          exact ⟨label, Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hlabel),
            Finset.ne_of_mem_erase hlabel⟩
        obtain ⟨label, hlabelPole, hlabelDrop⟩ := hchoice
        exact le_trans (sq_nonneg _) (htilt label hlabelPole hlabelDrop)
      nlinarith [hrankCast, hcapNonneg]
    nlinarith [hbig, hgap, hmarginShape, htiltNonneg, hgapPos, hfactorPos]
  -- the covering avoids the pole and the deleted label, thus its tilt is capped
  have htiltSum : ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2
      ≤ ((rank : ℝ) - 1) * tiltCap := by
    have hbound : ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2
        ≤ ∑ _label ∈ covering, tiltCap := by
      refine Finset.sum_le_sum fun label hlabel => ?_
      exact htilt label (fun heq => hpoleNotMem (heq ▸ hlabel))
        (fun heq => hdropNotMem (heq ▸ hlabel))
    have hcardCast : ((covering.card : ℕ) : ℝ) = (rank : ℝ) - 1 := by
      rw [hcard]
      have hcastStep : ((rank - 1 : ℕ) : ℝ) = (rank : ℝ) - 1 := by
        have : (1 : ℕ) ≤ rank := by omega
        push_cast [Nat.cast_sub this]
        ring
      exact hcastStep
    calc ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2
        ≤ ∑ _label ∈ covering, tiltCap := hbound
      _ = (covering.card : ℝ) * tiltCap := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((rank : ℝ) - 1) * tiltCap := by rw [hcardCast]
  have htiltStrict : ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2
      < margin * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1) := by
    have hmarginShape : margin = deletionMargin design pole drop
        - 2 * share * deletionCoverFactor design pole drop := by
      rw [hmarginDef, deletionMargin]; ring
    nlinarith [htiltSum, hspend, hgap, hmarginShape, hgapDef]
  have hcoverMargin : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 := by
    intro probe hprobe
    have hstep := hcover probe hprobe
    rwa [hfactorShape] at hstep
  have hposDef := posDef_insert_of_polarCover design hpoleNotMem hlong hmarginPosAchieved
    hcoverMargin htiltStrict
  refine exists_card_eq_posDef design ?_ hposDef
  rw [Finset.card_insert_of_notMem hpoleNotMem, hcard]
  omega

/-- **THE DELETION KILL.**  No tie carries a deletable label whose removal leaves
every other label below the tilt budget. -/
theorem not_isTie_of_deletableTilt (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole drop : Fin size} (hne : drop ≠ pole)
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hroom : rank + 1 ≤ size)
    (hdeletable : design.weight drop * planeShadowSq design pole drop
      < design.weight pole + design.weight drop)
    {tiltCap : ℝ}
    (htilt : ∀ label : Fin size, label ≠ pole → label ≠ drop →
      (design.atom label ⬝ᵥ design.atom pole) ^ 2 ≤ tiltCap)
    (hbudget : ((rank : ℝ) - 1) * tiltCap
      < deletionMargin design pole drop * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ¬ IsTie design := by
  intro htie
  obtain ⟨selected, hcard, hposDef⟩ := exists_dominating_of_deletableTilt hrank hpredecessor
    design hne hlong hroom hdeletable htilt hbudget
  exact htie.2 selected hcard hposDef

/-- **THE ONE-TILTED-LABEL STRATUM CLOSES.**  When a single label carries the
whole tilt of the pole and that label is deletable, the design is not a tie: the
deletion returns an ORTHOGONAL cover and the budget is spent on nothing. -/
theorem not_isTie_of_singleTiltedLabel (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole drop : Fin size} (hne : drop ≠ pole)
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hroom : rank + 1 ≤ size)
    (hdeletable : design.weight drop * planeShadowSq design pole drop
      < design.weight pole + design.weight drop)
    (hsingle : ∀ label : Fin size, label ≠ pole → label ≠ drop →
      design.atom label ⬝ᵥ design.atom pole = 0) :
    ¬ IsTie design := by
  have hsize : 3 ≤ size := by omega
  have hpairLt : design.weight pole + design.weight drop < 1 :=
    weight_pair_lt_one design (fun heq => hne heq.symm) hsize
  have hmarginPos : 0 < deletionMargin design pole drop :=
    deletionMargin_pos design hpairLt hdeletable
  have hleveragePos : (0 : ℝ) < design.atom pole ⬝ᵥ design.atom pole := by linarith
  refine not_isTie_of_deletableTilt hrank hpredecessor design hne hlong hroom hdeletable
    (tiltCap := 0) (fun label hlabelPole hlabelDrop => ?_) ?_
  · rw [hsingle label hlabelPole hlabelDrop]
    norm_num
  · rw [mul_zero]
    exact mul_pos (mul_pos hmarginPos hleveragePos) (by linarith)

/-- **THE FORWARD READING.**  Every tie carries a SECOND heavy label at every
deletable one.  This is the deletion kill read backwards, and it is a new
unconditional constraint on ties at every rank. -/
theorem exists_heavy_tilt_of_isTie_of_deletable (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) (htie : IsTie design) {pole drop : Fin size}
    (hne : drop ≠ pole) (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hroom : rank + 1 ≤ size)
    (hdeletable : design.weight drop * planeShadowSq design pole drop
      < design.weight pole + design.weight drop)
    {tiltCap : ℝ}
    (hbudget : ((rank : ℝ) - 1) * tiltCap
      < deletionMargin design pole drop * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ∃ label : Fin size, label ≠ pole ∧ label ≠ drop
      ∧ tiltCap < (design.atom label ⬝ᵥ design.atom pole) ^ 2 := by
  by_contra hcontra
  refine not_isTie_of_deletableTilt hrank hpredecessor design hne hlong hroom hdeletable
    (fun label hlabelPole hlabelDrop => ?_) hbudget htie
  by_contra hbig
  exact hcontra ⟨label, hlabelPole, hlabelDrop, not_le.mp hbig⟩

/-! ### Rank three, with the previous rank discharged -/

/-- The deletion kill at rank three. -/
theorem not_isTie_of_deletableTilt_three (design : WeightedDesign size 3)
    {pole drop : Fin size} (hne : drop ≠ pole)
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) (hroom : 4 ≤ size)
    (hdeletable : design.weight drop * planeShadowSq design pole drop
      < design.weight pole + design.weight drop)
    {tiltCap : ℝ}
    (htilt : ∀ label : Fin size, label ≠ pole → label ≠ drop →
      (design.atom label ⬝ᵥ design.atom pole) ^ 2 ≤ tiltCap)
    (hbudget : 2 * tiltCap
      < deletionMargin design pole drop * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ¬ IsTie design :=
  not_isTie_of_deletableTilt (by norm_num) gtz_rank_two design hne hlong hroom hdeletable htilt
    (by push_cast; linarith)

/-- The one-tilted-label stratum at rank three. -/
theorem not_isTie_of_singleTiltedLabel_three (design : WeightedDesign size 3)
    {pole drop : Fin size} (hne : drop ≠ pole)
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) (hroom : 4 ≤ size)
    (hdeletable : design.weight drop * planeShadowSq design pole drop
      < design.weight pole + design.weight drop)
    (hsingle : ∀ label : Fin size, label ≠ pole → label ≠ drop →
      design.atom label ⬝ᵥ design.atom pole = 0) :
    ¬ IsTie design :=
  not_isTie_of_singleTiltedLabel (by norm_num) gtz_rank_two design hne hlong hroom hdeletable
    hsingle

/-- The forward reading at rank three: a tie of six labels carries a second
heavy label at every deletable one. -/
theorem exists_heavy_tilt_of_isTie_of_deletable_three (design : WeightedDesign size 3)
    (htie : IsTie design) {pole drop : Fin size} (hne : drop ≠ pole)
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) (hroom : 4 ≤ size)
    (hdeletable : design.weight drop * planeShadowSq design pole drop
      < design.weight pole + design.weight drop)
    {tiltCap : ℝ}
    (hbudget : 2 * tiltCap
      < deletionMargin design pole drop * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ∃ label : Fin size, label ≠ pole ∧ label ≠ drop
      ∧ tiltCap < (design.atom label ⬝ᵥ design.atom pole) ^ 2 :=
  exists_heavy_tilt_of_isTie_of_deletable (by norm_num) gtz_rank_two design htie hne hlong hroom
    hdeletable (by push_cast; linarith)

/-! ## Part 10: the residual, narrowed by the deletion law

The deletion kill is a theorem at every tie, thus its contrapositive is a FREE
fact that a tie hands to the residual.  Adding it as a hypothesis makes the
residual strictly weaker while every consumer still runs on it, exactly as
`Gtz.PolarSaturationBudget` did for the saturation facts. -/

/-- **THE HEAVY LABEL OF A DELETABLE ONE, SHARP.**  Every tie carries, at every
overshooting pole and every DELETABLE label, a THIRD label whose squared pairing
against the pole already spends the whole deletion budget. -/
theorem exists_heavy_tilt_of_isTie_of_deletable_sharp (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) (htie : IsTie design) {pole drop : Fin size}
    (hne : drop ≠ pole) (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hroom : rank + 1 ≤ size)
    (hdeletable : design.weight drop * planeShadowSq design pole drop
      < design.weight pole + design.weight drop) :
    ∃ label : Fin size, label ≠ pole ∧ label ≠ drop
      ∧ deletionMargin design pole drop * (design.atom pole ⬝ᵥ design.atom pole)
            * (design.atom pole ⬝ᵥ design.atom pole - 1)
          ≤ ((rank : ℝ) - 1) * (design.atom label ⬝ᵥ design.atom pole) ^ 2 := by
  classical
  by_contra hcontra
  have hstrict : ∀ label : Fin size, label ≠ pole → label ≠ drop →
      ((rank : ℝ) - 1) * (design.atom label ⬝ᵥ design.atom pole) ^ 2
        < deletionMargin design pole drop * (design.atom pole ⬝ᵥ design.atom pole)
            * (design.atom pole ⬝ᵥ design.atom pole - 1) := by
    intro label hlabelPole hlabelDrop
    by_contra hbig
    exact hcontra ⟨label, hlabelPole, hlabelDrop, not_lt.mp hbig⟩
  -- the admissible labels form a nonempty finite set, thus the tilt has a maximum
  have hadmissible : ((Finset.univ.erase pole).erase drop).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ drop⟩),
      Finset.card_erase_of_mem (Finset.mem_univ pole), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨top, htopMem, htopMax⟩ := Finset.exists_max_image
    ((Finset.univ.erase pole).erase drop)
    (fun label => (design.atom label ⬝ᵥ design.atom pole) ^ 2) hadmissible
  have htopDrop : top ≠ drop := Finset.ne_of_mem_erase htopMem
  have htopPole : top ≠ pole := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase htopMem)
  refine not_isTie_of_deletableTilt hrank hpredecessor design hne hlong hroom hdeletable
    (tiltCap := (design.atom top ⬝ᵥ design.atom pole) ^ 2) (fun label hlabelPole hlabelDrop => ?_)
    (hstrict top htopPole htopDrop) htie
  exact htopMax label (Finset.mem_erase.mpr ⟨hlabelDrop,
    Finset.mem_erase.mpr ⟨hlabelPole, Finset.mem_univ label⟩⟩)

/-- **THE FREE DELETION FACT.**  What a tie supplies at an overshooting pole: at
every deletable label some other label is already heavy. -/
def PolarDeletionHeavy (design : WeightedDesign size rank) (pole : Fin size) : Prop :=
  ∀ drop : Fin size, drop ≠ pole →
    design.weight drop * planeShadowSq design pole drop
        < design.weight pole + design.weight drop →
      ∃ label : Fin size, label ≠ pole ∧ label ≠ drop
        ∧ deletionMargin design pole drop * (design.atom pole ⬝ᵥ design.atom pole)
              * (design.atom pole ⬝ᵥ design.atom pole - 1)
            ≤ ((rank : ℝ) - 1) * (design.atom label ⬝ᵥ design.atom pole) ^ 2

/-- **THE DELETION FACT IS FREE AT EVERY TIE.** -/
theorem polarDeletionHeavy_of_isTie (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    (htie : IsTie design) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) (hroom : rank + 1 ≤ size) :
    PolarDeletionHeavy design pole :=
  fun _drop hne hdeletable =>
    exists_heavy_tilt_of_isTie_of_deletable_sharp hrank hpredecessor design htie hne hlong hroom
      hdeletable

/-- **THE TWICE-NARROWED TILT RESIDUAL.**  `Gtz.PolarTiltSelectionUnsaturated`
with the deletion fact handed to it as well.  It is weaker than both shipped
residuals, and every consumer of them runs on this one. -/
def PolarTiltSelectionDeletion (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (pole : Fin size) (covering : Finset (Fin size))
      (margin : ℝ),
    IsPrimitiveDesign design →
    IsTie design →
    1 < design.atom pole ⬝ᵥ design.atom pole →
    PolarSaturationBudget design pole →
    PolarDeletionHeavy design pole →
    0 < margin →
    covering.card = rank - 1 → pole ∉ covering →
    (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) →
    ∃ selected : Finset (Fin size), selected.card = rank - 1 ∧ pole ∉ selected
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2)
      ∧ ∑ label ∈ selected, (design.atom label ⬝ᵥ design.atom pole) ^ 2
          < margin * (design.atom pole ⬝ᵥ design.atom pole)
              * (design.atom pole ⬝ᵥ design.atom pole - 1)

/-- The twice-narrowed residual is weaker than the once-narrowed one. -/
theorem polarTiltSelectionDeletion_of_polarTiltSelectionUnsaturated
    (htilt : PolarTiltSelectionUnsaturated size rank) : PolarTiltSelectionDeletion size rank :=
  fun design pole covering margin hprimitive htie hlong hbudget _hheavy hmargin hcard hnotMem
    hcover =>
    htilt design pole covering margin hprimitive htie hlong hbudget hmargin hcard hnotMem hcover

/-- The twice-narrowed residual is weaker than the shipped one. -/
theorem polarTiltSelectionDeletion_of_polarTiltSelection
    (htilt : PolarTiltSelection size rank) : PolarTiltSelectionDeletion size rank :=
  polarTiltSelectionDeletion_of_polarTiltSelectionUnsaturated
    (polarTiltSelectionUnsaturated_of_polarTiltSelection htilt)

/-- **THE HINGE FROM THE TWICE-NARROWED RESIDUAL.**  Both bundles are theorems at
a tie, thus the second narrowing costs nothing downstream either. -/
theorem hingeHoldsAtSize_of_polarTiltDeletion (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionDeletion size rank) : HingeHoldsAtSize size rank := by
  classical
  intro design htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  obtain ⟨pole, hlong⟩ := exists_overshooting_atom design hrank
  obtain ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin hrank hpredecessor design hlong
  obtain ⟨selected, hselCard, hselNotMem, hselCover, hselTilt⟩ :=
    htilt design pole covering margin hprimitive htie hlong
      (polarSaturationBudget_of_isTie hrank hpredecessor design htie hlong)
      (polarDeletionHeavy_of_isTie hrank hpredecessor design htie hlong hroom)
      hmarginPos hcard hnotMem hcover
  have hposDef := posDef_insert_of_polarCover design hselNotMem hlong hmarginPos hselCover hselTilt
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hselNotMem, hselCard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-! ### Every consumer of the shipped residual, on the twice-narrowed one -/

/-- Arm (i). -/
theorem stressFreeArmAt_of_polarTiltDeletion (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionDeletion size rank) : StressFreeArmAt size rank :=
  fun design _hfree htie =>
    hingeHoldsAtSize_of_polarTiltDeletion hrank hpredecessor hroom htilt design htie

/-- Arm (ii). -/
theorem balancedArmAt_of_polarTiltDeletion (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionDeletion size rank) : BalancedArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltDeletion hrank hpredecessor hroom htilt design htie

/-- Arm (iii). -/
theorem degenerateArmAt_of_polarTiltDeletion (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionDeletion size rank) : DegenerateArmAt size rank :=
  fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
    hingeHoldsAtSize_of_polarTiltDeletion hrank hpredecessor hroom htilt design htie

/-- The partial-support sub-arm. -/
theorem balancedPartialSupportArmAt_of_polarTiltDeletion (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionDeletion size rank) : BalancedPartialSupportArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hunsupported _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltDeletion hrank hpredecessor hroom htilt design htie

/-- The full-support sub-arm. -/
theorem balancedFullSupportArmAt_of_polarTiltDeletion (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionDeletion size rank) : BalancedFullSupportArmAt size rank :=
  fun design _stressCoeff _hstress _hfull htie =>
    hingeHoldsAtSize_of_polarTiltDeletion hrank hpredecessor hroom htilt design htie

/-- The repaired degenerate cover. -/
theorem degenerateHyperplaneCover_of_polarTiltDeletion (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionDeletion size rank) : DegenerateHyperplaneCover size rank := by
  intro design _stressCoeff _unitNormal _pole hprimitive htie _hstressNe _hunit _hstress
    _hsupport _hpole
  exact absurd (hingeHoldsAtSize_of_polarTiltDeletion hrank hpredecessor hroom htilt design htie)
    ((isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive)

/-- **THE COLLAPSE, ON THE TWICE-NARROWED RESIDUAL.** -/
theorem polarTiltDeletion_closes_every_arm (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionDeletion size rank) :
    HingeHoldsAtSize size rank ∧ StressFreeArmAt size rank ∧ BalancedArmAt size rank
      ∧ DegenerateArmAt size rank ∧ BalancedPartialSupportArmAt size rank
      ∧ BalancedFullSupportArmAt size rank ∧ DegenerateHyperplaneCover size rank :=
  ⟨hingeHoldsAtSize_of_polarTiltDeletion hrank hpredecessor hroom htilt,
    stressFreeArmAt_of_polarTiltDeletion hrank hpredecessor hroom htilt,
    balancedArmAt_of_polarTiltDeletion hrank hpredecessor hroom htilt,
    degenerateArmAt_of_polarTiltDeletion hrank hpredecessor hroom htilt,
    balancedPartialSupportArmAt_of_polarTiltDeletion hrank hpredecessor hroom htilt,
    balancedFullSupportArmAt_of_polarTiltDeletion hrank hpredecessor hroom htilt,
    degenerateHyperplaneCover_of_polarTiltDeletion hrank hpredecessor hroom htilt⟩

/-! ### The registry obligations, on the twice-narrowed residual -/

/-- The threshold cell obligation of the registry. -/
theorem thresholdCellHingeRankFourAndUp_of_polarTiltDeletion
    (htilt : ∀ rank : ℕ, 4 ≤ rank →
      PolarTiltSelectionDeletion (thresholdSize rank) rank) :
    ∀ rank : ℕ, 4 ≤ rank → GtzWeightedAll (rank - 1) →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor _hcell design htie
  have hroom : rank + 1 ≤ rank * (rank + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc (rank + 1) * 2 ≤ (rank + 1) * rank := Nat.mul_le_mul_left _ (by omega)
      _ = rank * (rank + 1) := Nat.mul_comm _ _
  exact hingeHoldsAtSize_of_polarTiltDeletion (by omega) hpredecessor hroom (htilt rank hrank)
    design htie

/-- The sub-threshold band obligation of the registry. -/
theorem subThresholdBandHinge_of_polarTiltDeletion
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size < thresholdSize rank →
      PolarTiltSelectionDeletion size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor size hlow hhigh _hcell design htie
  exact hingeHoldsAtSize_of_polarTiltDeletion (by omega) hpredecessor (by omega)
    (htilt rank size hrank hlow hhigh) design htie

/-- The whole sharp window, from one twice-narrowed residual per cell. -/
theorem sharpWindowHinge_of_polarTiltDeletion
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size ≤ thresholdSize rank →
      PolarTiltSelectionDeletion size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        HingeHoldsAtSize size rank := by
  intro rank hrank hpredecessor size hlow hhigh
  exact hingeHoldsAtSize_of_polarTiltDeletion (by omega) hpredecessor (by omega)
    (htilt rank size hrank hlow hhigh)

/-- Arm (i) at the deciding cell of a rank. -/
theorem thresholdStressFreeArm_of_polarTiltDeletion (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionDeletion (thresholdSize rank) rank) :
    ThresholdStressFreeArm rank :=
  stressFreeArmAt_of_polarTiltDeletion hrank hpredecessor hroom htilt

/-- Arm (ii) at the deciding cell of a rank. -/
theorem thresholdBalancedArm_of_polarTiltDeletion (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionDeletion (thresholdSize rank) rank) :
    ThresholdBalancedArm rank :=
  balancedArmAt_of_polarTiltDeletion hrank hpredecessor hroom htilt

/-- Arm (iii) at the deciding cell of a rank. -/
theorem thresholdDegenerateArm_of_polarTiltDeletion (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionDeletion (thresholdSize rank) rank) :
    ThresholdDegenerateArm rank :=
  degenerateArmAt_of_polarTiltDeletion hrank hpredecessor hroom htilt

/-! ### The deciding cell of rank three, and the calibration -/

/-- The hinge at the deciding cell of rank three. -/
theorem hingeHoldsAtSize_six_three_of_polarTiltDeletion
    (htilt : PolarTiltSelectionDeletion 6 3) : HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_polarTiltDeletion (by norm_num) gtz_rank_two (by norm_num) htilt

/-- The three rank-three arms from the twice-narrowed residual. -/
theorem thresholdArms_rank_three_of_polarTiltDeletion
    (htilt : PolarTiltSelectionDeletion 6 3) :
    ThresholdStressFreeArm 3 ∧ ThresholdBalancedArm 3 ∧ ThresholdDegenerateArm 3 := by
  have hhinge := hingeHoldsAtSize_six_three_of_polarTiltDeletion htilt
  exact ⟨fun design _hfree htie => hhinge design htie,
    fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie => hhinge design htie,
    fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
      hhinge design htie⟩

/-- **THE DECIDING CELL OF RANK THREE FROM THE TWICE-NARROWED RESIDUAL ALONE.** -/
theorem gtzWeighted_six_three_of_polarTiltDeletion
    (htilt : PolarTiltSelectionDeletion 6 3) : GtzWeighted 6 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltDeletion htilt
  exact GeneralRankReach.gtzWeighted_six_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **ALL OF RANK THREE FROM THE TWICE-NARROWED RESIDUAL ALONE.** -/
theorem gtzWeightedAll_three_of_polarTiltDeletion
    (htilt : PolarTiltSelectionDeletion 6 3) : GtzWeightedAll 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltDeletion htilt
  exact GeneralRankReach.gtzWeightedAll_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **THE TWICE-NARROWED RESIDUAL IS FALSE AT `(5,3)`.**  The calibration
transports through the second narrowing too: the deletion fact is free at every
tie of five labels of rank three. -/
theorem not_polarTiltSelectionDeletion_five_three :
    ¬ PolarTiltSelectionDeletion 5 3 :=
  fun htilt => not_hingeHoldsAtSize_five_three
    (hingeHoldsAtSize_of_polarTiltDeletion (by norm_num) gtz_rank_two (by norm_num) htilt)

/-- **THE GUARDRAIL.**  The `(6,3)` tie in the tree is not primitive, thus it
does not touch the twice-narrowed residual, and the last-stage Prop stays
refuted. -/
theorem sixSplitDiamondDesign_spares_polarTiltDeletion :
    ¬ RankSuccShrinks 6 3 ∧ IsTie sixSplitDiamondDesign
      ∧ ¬ IsPrimitiveDesign sixSplitDiamondDesign
      ∧ ¬ PolarTiltSelectionDeletion 5 3 :=
  ⟨not_rankSuccShrinks_six_three, sixSplitDiamondDesign_isTie,
    not_isPrimitiveDesign_sixSplitDiamondDesign, not_polarTiltSelectionDeletion_five_three⟩

/-- **THE LEDGER OF A RANK-THREE TIE, WITH THE DELETION LAW.**  At every
overshooting atom of every rank-three tie of at least four labels: the leverage
cap is strict, the weight law holds against every weight floor, and at every
DELETABLE label a third label already spends the whole deletion budget. -/
theorem sixThree_tie_deletion_ledger (design : WeightedDesign 6 3) (htie : IsTie design)
    {pole : Fin 6} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    design.weight pole * (design.atom pole ⬝ᵥ design.atom pole) < 1
      ∧ (∀ drop : Fin 6, drop ≠ pole →
          design.weight drop * planeShadowSq design pole drop
              < design.weight pole + design.weight drop →
            ∃ label : Fin 6, label ≠ pole ∧ label ≠ drop
              ∧ deletionMargin design pole drop * (design.atom pole ⬝ᵥ design.atom pole)
                    * (design.atom pole ⬝ᵥ design.atom pole - 1)
                  ≤ 2 * (design.atom label ⬝ᵥ design.atom pole) ^ 2)
      ∧ ∀ drop : Fin 6, drop ≠ pole →
          planeShadowSq design pole drop ≤ 1 →
            ∃ label : Fin 6, label ≠ pole ∧ label ≠ drop
              ∧ design.atom label ⬝ᵥ design.atom pole ≠ 0 := by
  refine ⟨tie_weight_mul_leverage_lt_one (by norm_num) gtz_rank_two design htie hlong, ?_, ?_⟩
  · intro drop hne hdeletable
    obtain ⟨label, hlabelPole, hlabelDrop, hheavy⟩ :=
      exists_heavy_tilt_of_isTie_of_deletable_sharp (rank := 3) (by norm_num) gtz_rank_two design
        htie hne hlong (by norm_num) hdeletable
    exact ⟨label, hlabelPole, hlabelDrop, by push_cast at hheavy; linarith⟩
  · intro drop hne hshadow
    by_contra hcontra
    have hsingle : ∀ label : Fin 6, label ≠ pole → label ≠ drop →
        design.atom label ⬝ᵥ design.atom pole = 0 := by
      intro label hlabelPole hlabelDrop
      by_contra hnonzero
      exact hcontra ⟨label, hlabelPole, hlabelDrop, hnonzero⟩
    exact not_isTie_of_singleTiltedLabel_three design hne hlong (by norm_num)
      (deletable_of_planeShadowSq_le_one design pole drop hshadow) hsingle htie

end Gtz
