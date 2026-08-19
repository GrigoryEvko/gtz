import Gtz.Wave.CornerFramePair

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The four-set dichotomy of the one-zero corner: both-heavy is empty

At a corank-two corner whose gap axis one inside atom reads at zero — the `Z1`
stratum — the two four-sets through a single axis-carrying inside atom compete:
`{z} ∪ Cᶜ` keeps `z` and removes the unit atom `x` and the atom `y`, and
`{y} ∪ Cᶜ` keeps `y`.  This module proves that ONE of the two always dominates
strictly (`Gtz.corner_oneAxisZero_fourSet_split`), with no tie hypothesis: the
sub-stratum of `Z1` where both inside readings of the five-set anchor reach one
is EMPTY, because those readings are exactly the failures of these four-sets.

## The mechanism

Parseval pays each four-set's quadratic form through the weighted outside mass
capped by the heaviest outside weight `ms`, and the frame of the one-zero
corner (`Gtz.corner_oneAxisZero_frame_decomp`) reduces each form to an explicit
two-by-two Sylvester datum in the axis plane.  The two Sylvester determinants
obey an exact algebra: after eliminating the gap scale against the plane block
of the weighted Parseval identity, each determinant condition is LINEAR in
`ms` with a nonnegative slope, and at the endpoint `ms = 1 − t_y − t_z` the two
conditions satisfy the syzygy

  `(1 − t_y) · G_y + (1 − t_z) · G_z = 0`,

so they cannot both fail: the two slopes would both vanish while totalling
`(1+lam)³(1−t_y)(1−t_z) > 0` (`Gtz.oneAxisZero_fourSet_scalar_core`).  The
weights carry the certificate: every inequality degenerates as the weight
floor collapses, exactly as the boundary limit to `(5,3)` demands.

## What this empties

At the five-set anchor `B` of the zero atom, the reading `R_ee ≥ 1` of an
inside atom is equivalent to the loss of positive definiteness of the four-set
through the OTHER inside atom (`Gtz.posDef_sub_vecMulVec_iff`).  The split
therefore says: the `Z1` case split on `(R_yy ≥ 1, R_zz ≥ 1)` has an EMPTY
both-heavy cell, and the pair machine of `Gtz.tie_fiveSet_pair_reading` always
owns a light inside atom.  Measured on thirty thousand sampled `Z1`
configurations the dichotomy holds with margin, and an adversarial search
pushed `min(R_yy, R_zz)` no higher than `0.86`; this module replaces that
measurement with a kernel proof.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The frame decomposition of the one-zero corner -/

/-- **The frame decomposition.**  At a corank-two corner whose first inside
atom reads the axis at zero and whose third does not, the zero atom is unit and
orthogonal to the axis plane, and the two axis-carrying atoms decompose over an
explicit orthonormal pair `(u, w)` with the three scalar relations of the
frame: axis masses totalling `1 + lam`, plane masses totalling one, and
orthogonal mixed masses. -/
theorem corner_oneAxisZero_frame_decomp (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0) :
    ∃ w : Fin 3 → ℝ, w ⬝ᵥ w = 1 ∧ u ⬝ᵥ w = 0 ∧ D.atom x ⬝ᵥ w = 0
      ∧ D.atom x ⬝ᵥ D.atom x = 1
      ∧ D.atom y = (D.atom y ⬝ᵥ u) • u + (D.atom y ⬝ᵥ w) • w
      ∧ D.atom z = (D.atom z ⬝ᵥ u) • u + (D.atom z ⬝ᵥ w) • w
      ∧ (D.atom y ⬝ᵥ u) ^ 2 + (D.atom z ⬝ᵥ u) ^ 2 = 1 + lam
      ∧ (D.atom y ⬝ᵥ w) ^ 2 + (D.atom z ⬝ᵥ w) ^ 2 = 1
      ∧ (D.atom y ⬝ᵥ u) * (D.atom y ⬝ᵥ w)
          + (D.atom z ⬝ᵥ u) * (D.atom z ⬝ᵥ w) = 0 := by
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have hcard : ({x, y, z} : Finset (Fin m)).card = 3 := card_triple_eq hxy hxz hyz
  have hx : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hy : y ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hz : z ∈ ({x, y, z} : Finset (Fin m)) := by simp
  set ay : ℝ := D.atom y ⬝ᵥ u with hay
  set az : ℝ := D.atom z ⬝ᵥ u with hazv
  have hazsq : (0 : ℝ) < az ^ 2 := by positivity
  have hmass := corner_axis_mass D ({x, y, z} : Finset (Fin m)) hunit hgap
  rw [sum_triple_eq hxy hxz hyz, hax] at hmass
  have hmass' : ay ^ 2 + az ^ 2 = 1 + lam := by linear_combination hmass
  have hexY := corner_heavyExcess_axis D _ hcard hlam hunit hgap hy
  simp only [heavyExcess] at hexY
  rw [show leverageOf (D.atom y) = D.atom y ⬝ᵥ D.atom y from
    (dotProduct_self_eq_sum_sq (D.atom y)).symm] at hexY
  have hlevY : (1 + lam) * (D.atom y ⬝ᵥ D.atom y) = (1 + lam) + lam * ay ^ 2 := by
    linear_combination hexY
  have hexZ := corner_heavyExcess_axis D _ hcard hlam hunit hgap hz
  simp only [heavyExcess] at hexZ
  rw [show leverageOf (D.atom z) = D.atom z ⬝ᵥ D.atom z from
    (dotProduct_self_eq_sum_sq (D.atom z)).symm] at hexZ
  have hlevZ : (1 + lam) * (D.atom z ⬝ᵥ D.atom z) = (1 + lam) + lam * az ^ 2 := by
    linear_combination hexZ
  have hexX := corner_heavyExcess_axis D _ hcard hlam hunit hgap hx
  simp only [heavyExcess] at hexX
  rw [hax, show leverageOf (D.atom x) = D.atom x ⬝ᵥ D.atom x from
    (dotProduct_self_eq_sum_sq (D.atom x)).symm] at hexX
  have hlevX : D.atom x ⬝ᵥ D.atom x = 1 := by
    have hcancel := mul_left_cancel₀ (ne_of_gt hone)
      (show (1 + lam) * (D.atom x ⬝ᵥ D.atom x - 1) = (1 + lam) * 0 by
        rw [mul_zero]
        linear_combination hexX)
    linarith
  have hpairXY := corner_atomPairing_axis D _ hcard hlam hunit hgap hx hy hxy
  rw [hax] at hpairXY
  have hPxy : D.atom x ⬝ᵥ D.atom y = 0 := by
    have h0 : (1 + lam) * atomPairing D x y = 0 := by rw [hpairXY]; ring
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (ne_of_gt hone)
    · simpa only [atomPairing] using h
  have hpairXZ := corner_atomPairing_axis D _ hcard hlam hunit hgap hx hz hxz
  rw [hax] at hpairXZ
  have hPxz : D.atom x ⬝ᵥ D.atom z = 0 := by
    have h0 : (1 + lam) * atomPairing D x z = 0 := by rw [hpairXZ]; ring
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (ne_of_gt hone)
    · simpa only [atomPairing] using h
  have hpairYZ := corner_atomPairing_axis D _ hcard hlam hunit hgap hy hz hyz
  have hPyz : (1 + lam) * (D.atom y ⬝ᵥ D.atom z) = lam * (ay * az) := by
    have h := hpairYZ
    simp only [atomPairing] at h
    linear_combination h
  -- the plane part of the second atom
  set w0 : Fin 3 → ℝ := D.atom y - ay • u with hw0
  have hw0u : u ⬝ᵥ w0 = 0 := by
    rw [hw0, dotProduct_sub, dotProduct_smul, hunit, dotProduct_comm u (D.atom y),
      ← hay]
    simp only [smul_eq_mul]
    ring
  have hw0x : D.atom x ⬝ᵥ w0 = 0 := by
    rw [hw0, dotProduct_sub, dotProduct_smul, hPxy, hax]
    simp only [smul_eq_mul]
    ring
  have hw0sq : (1 + lam) * (w0 ⬝ᵥ w0) = az ^ 2 := by
    have hexpand : w0 ⬝ᵥ w0 = D.atom y ⬝ᵥ D.atom y - ay ^ 2 := by
      rw [hw0, dotProduct_sub, sub_dotProduct, sub_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_dotProduct, dotProduct_smul, hunit,
        dotProduct_comm u (D.atom y), ← hay]
      simp only [smul_eq_mul]
      ring
    rw [hexpand]
    linear_combination hlevY - hmass'
  have hw0pos : 0 < w0 ⬝ᵥ w0 := by nlinarith [hw0sq, hone, hazsq]
  set cnorm : ℝ := Real.sqrt (w0 ⬝ᵥ w0) with hcnorm
  have hcpos : 0 < cnorm := Real.sqrt_pos.mpr hw0pos
  have hcsq : cnorm ^ 2 = w0 ⬝ᵥ w0 := Real.sq_sqrt hw0pos.le
  obtain ⟨w, hw⟩ : ∃ v : Fin 3 → ℝ, v = cnorm⁻¹ • w0 := ⟨cnorm⁻¹ • w0, rfl⟩
  have hwunit : w ⬝ᵥ w = 1 := by
    rw [hw, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    rw [show cnorm⁻¹ * (cnorm⁻¹ * (w0 ⬝ᵥ w0)) = (w0 ⬝ᵥ w0) / cnorm ^ 2 by ring, hcsq]
    exact div_self (ne_of_gt hw0pos)
  have hwu : u ⬝ᵥ w = 0 := by
    rw [hw, dotProduct_smul, hw0u]
    simp
  have hwx : D.atom x ⬝ᵥ w = 0 := by
    rw [hw, dotProduct_smul, hw0x]
    simp
  -- the y reading of w and the definitional decomposition
  have hyw : D.atom y ⬝ᵥ w = cnorm := by
    have hysplit : D.atom y = w0 + ay • u := by rw [hw0]; abel
    have hyw0 : D.atom y ⬝ᵥ w0 = w0 ⬝ᵥ w0 := by
      rw [hysplit, add_dotProduct, smul_dotProduct, hw0u]
      simp
    rw [hw, dotProduct_smul, hyw0]
    simp only [smul_eq_mul]
    rw [← hcsq, sq, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcpos), one_mul]
  have hyDecomp : D.atom y = ay • u + cnorm • w := by
    rw [hw, smul_smul, mul_inv_cancel₀ (ne_of_gt hcpos), one_smul, hw0]
    abel
  -- the z reading of w
  set beta : ℝ := D.atom z ⬝ᵥ w with hbeta
  have hbetaval : (1 + lam) * (cnorm * beta) = -(ay * az) := by
    have hread : cnorm * beta = D.atom z ⬝ᵥ w0 := by
      rw [hbeta, hw, dotProduct_smul]
      simp only [smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul]
    have hzw0 : (1 + lam) * (D.atom z ⬝ᵥ w0) = -(ay * az) := by
      have hexpand : D.atom z ⬝ᵥ w0 = D.atom y ⬝ᵥ D.atom z - ay * az := by
        rw [hw0, dotProduct_sub, dotProduct_smul,
          dotProduct_comm (D.atom z) (D.atom y), ← hazv]
        simp only [smul_eq_mul]
      rw [hexpand]
      linear_combination hPyz
    rw [hread]
    exact hzw0
  have hbsq' : (1 + lam) * beta ^ 2 = ay ^ 2 := by
    have hsq : ((1 + lam) * (cnorm * beta)) ^ 2 = (ay * az) ^ 2 := by
      rw [hbetaval]
      ring
    have hcsq' : (1 + lam) * cnorm ^ 2 = az ^ 2 := by rw [hcsq]; exact hw0sq
    have hkey : az ^ 2 * ((1 + lam) * beta ^ 2) = az ^ 2 * ay ^ 2 := by
      linear_combination hsq - ((1 + lam) * beta ^ 2) * hcsq'
    exact mul_left_cancel₀ (ne_of_gt hazsq) hkey
  -- the z decomposition through the orthonormal resolution
  have hres := atomMatrix_orthonormal_resolution hunit hwunit hlevX hwu
    (by rw [dotProduct_comm]; exact hax) (by rw [dotProduct_comm]; exact hwx)
  have hzDecomp : D.atom z = az • u + beta • w := by
    have happly := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) ℝ => M *ᵥ D.atom z) hres
    simp only [Matrix.add_mulVec, Matrix.one_mulVec] at happly
    rw [show atomMatrix u = Matrix.vecMulVec u u from rfl,
      show atomMatrix w = Matrix.vecMulVec w w from rfl,
      show atomMatrix (D.atom x) = Matrix.vecMulVec (D.atom x) (D.atom x) from rfl,
      vecMulVec_mulVec_eq, vecMulVec_mulVec_eq, vecMulVec_mulVec_eq,
      dotProduct_comm u (D.atom z), ← hazv, dotProduct_comm w (D.atom z), ← hbeta,
      hPxz, zero_smul, add_zero] at happly
    exact happly.symm
  -- the three scalar relations
  have hcsq' : (1 + lam) * cnorm ^ 2 = az ^ 2 := by rw [hcsq]; exact hw0sq
  have hsum2 : cnorm ^ 2 + beta ^ 2 = 1 := by
    have hadd : (1 + lam) * (cnorm ^ 2 + beta ^ 2) = (1 + lam) * 1 := by
      rw [mul_one]
      linear_combination hcsq' + hbsq' + hmass'
    exact mul_left_cancel₀ (ne_of_gt hone) hadd
  have hsum3 : ay * cnorm + az * beta = 0 := by
    have hfactor : ((1 + lam) * cnorm) * (ay * cnorm + az * beta)
        = ((1 + lam) * cnorm) * 0 := by
      rw [mul_zero]
      linear_combination ay * hcsq' + az * hbetaval
    exact mul_left_cancel₀ (by positivity) hfactor
  refine ⟨w, hwunit, hwu, hwx, hlevX, ?_, ?_, hmass', ?_, ?_⟩
  · rw [hyw]
    exact hyDecomp
  · rw [← hbeta]
    exact hzDecomp
  · rw [hyw, ← hbeta]
    exact hsum2
  · rw [hyw, ← hbeta]
    exact hsum3

/-! ## 2. The scalar core: the two endpoint conditions cannot both fail -/

/-- **THE SCALAR CORE OF THE DICHOTOMY.**  After the Parseval payment, the
failure of each four-set is a linear condition in the heaviest outside weight
with a nonnegative slope, and the two endpoint values obey an exact syzygy: a
joint failure forces both slopes to vanish while they total
`(1+lam)³(1−t_y)(1−t_z) > 0`. -/
theorem oneAxisZero_fourSet_scalar_core (ty tz ms lam b : ℝ)
    (hty : 0 < ty) (htz : 0 < tz) (hms : 0 < ms) (hlam : 0 < lam)
    (hb0 : 0 ≤ b) (hbnu : b ≤ 1 + lam) (hsum : ms + ty + tz < 1)
    (hn2 : ty * (1 + lam - b) + tz * b ≤ 1 + lam)
    (hn3 : (ty - tz) ^ 2 * b * (1 + lam - b)
      ≤ (1 - ty * b - tz * (1 + lam - b))
        * ((1 + lam) - ty * (1 + lam - b) - tz * b))
    (hdz : (1 + lam) * ((1 - tz) * (1 - ms - ty))
      ≤ lam * ((1 + lam - b) * ms * (ms - 1 + ty - tz) + b * (ty - tz)
          + (1 + lam) * tz * (1 - ty)))
    (hdy : (1 + lam) * ((1 - ty) * (1 - ms - tz))
      ≤ lam * (b * ms * (ms - 1 + tz - ty) + (1 + lam - b) * (tz - ty)
          + (1 + lam) * ty * (1 - tz))) : False := by
  set nu : ℝ := 1 + lam with hnu
  have hnupos : 0 < nu := by rw [hnu]; linarith
  set zz : ℝ := 1 + lam - b with hzz
  have hz0 : 0 ≤ zz := by rw [hzz]; linarith
  have hty1 : ty < 1 := by linarith
  have htz1 : tz < 1 := by linarith
  have hgap : 0 < 1 - ty - tz - ms := by linarith
  set BY : ℝ := zz * ms * (ms - 1 + ty - tz) + b * (ty - tz) + nu * tz * (1 - ty)
    with hBY
  set BZ : ℝ := b * ms * (ms - 1 + tz - ty) + zz * (tz - ty) + nu * ty * (1 - tz)
    with hBZ
  set H2 : ℝ := nu - ty * zz - tz * b with hH2
  set U1 : ℝ := ty * b + tz * zz with hU1
  set TT : ℝ := U1 * H2 + (ty - tz) ^ 2 * b * zz with hTT
  have hH2nn : 0 ≤ H2 := by rw [hH2, hzz, hnu]; linarith [hn2]
  have hU1nn : 0 ≤ U1 := by
    rw [hU1]
    have := mul_nonneg hty.le hb0
    have := mul_nonneg htz.le hz0
    linarith
  have hTTnn : 0 ≤ TT := by
    rw [hTT]
    have h1 : 0 ≤ U1 * H2 := mul_nonneg hU1nn hH2nn
    have h2 : 0 ≤ (ty - tz) ^ 2 * b * zz :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hb0) hz0
    linarith
  have hcyc : 0 < (1 - tz) * (1 - ms - ty) := by
    have : 0 < 1 - ms - ty := by linarith
    positivity
  have hczc : 0 < (1 - ty) * (1 - ms - tz) := by
    have : 0 < 1 - ms - tz := by linarith
    positivity
  have hdz' : nu * ((1 - tz) * (1 - ms - ty)) ≤ lam * BY := hdz
  have hdy' : nu * ((1 - ty) * (1 - ms - tz)) ≤ lam * BZ := hdy
  have hBYpos : 0 < BY := by
    by_contra hcon
    push Not at hcon
    have h1 : lam * BY ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam.le hcon
    have h2 : 0 < nu * ((1 - tz) * (1 - ms - ty)) := mul_pos hnupos hcyc
    linarith
  have hBZpos : 0 < BZ := by
    by_contra hcon
    push Not at hcon
    have h1 : lam * BZ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam.le hcon
    have h2 : 0 < nu * ((1 - ty) * (1 - ms - tz)) := mul_pos hnupos hczc
    linarith
  have hcap : TT ≤ H2 := by
    have hring : H2 - TT = (1 - U1) * H2 - (ty - tz) ^ 2 * b * zz := by
      rw [hTT]; ring
    have hn3' : (ty - tz) ^ 2 * b * zz ≤ (1 - U1) * H2 := by
      rw [hU1, hH2, hzz, hnu]
      calc (ty - tz) ^ 2 * b * (1 + lam - b)
          ≤ (1 - ty * b - tz * (1 + lam - b))
            * ((1 + lam) - ty * (1 + lam - b) - tz * b) := hn3
        _ = (1 - (ty * b + tz * (1 + lam - b)))
            * ((1 + lam) - ty * (1 + lam - b) - tz * b) := by ring
    linarith [hring, hn3']
  have hEY : 0 ≤ nu * H2 * BY - TT * (BY + nu * ((1 - tz) * (1 - ms - ty))) := by
    have h1 : TT * BY ≤ H2 * BY := mul_le_mul_of_nonneg_right hcap hBYpos.le
    have h2 : TT * (nu * ((1 - tz) * (1 - ms - ty))) ≤ TT * (lam * BY) :=
      mul_le_mul_of_nonneg_left hdz' hTTnn
    nlinarith [h1, h2, hnupos, hTTnn]
  have hEZ : 0 ≤ nu * H2 * BZ - TT * (BZ + nu * ((1 - ty) * (1 - ms - tz))) := by
    have h1 : TT * BZ ≤ H2 * BZ := mul_le_mul_of_nonneg_right hcap hBZpos.le
    have h2 : TT * (nu * ((1 - ty) * (1 - ms - tz))) ≤ TT * (lam * BZ) :=
      mul_le_mul_of_nonneg_left hdy' hTTnn
    nlinarith [h1, h2, hnupos, hTTnn]
  set AY : ℝ := nu ^ 2 * (1 - tz) * (b * (ty ^ 2 - ty * tz - ty + 1)
    - nu * (1 - ty) ^ 2) with hAY
  set BEY : ℝ := nu ^ 2 * zz * (1 - ty) * (1 - tz) with hBEY
  set AZ : ℝ := nu ^ 2 * (1 - ty) * (b * (ty * tz - tz ^ 2 + tz - 1)
    + nu * tz * (1 - ty)) with hAZ
  set BEZ : ℝ := nu ^ 2 * b * (1 - ty) * (1 - tz) with hBEZ
  have hJ1 : nu * H2 * BY - TT * (BY + nu * ((1 - tz) * (1 - ms - ty)))
      = ms * (AY + BEY * ms) := by
    rw [hAY, hBEY, hTT, hU1, hH2, hBY, hzz, hnu]
    ring
  have hJ1z : nu * H2 * BZ - TT * (BZ + nu * ((1 - ty) * (1 - ms - tz)))
      = ms * (AZ + BEZ * ms) := by
    rw [hAZ, hBEZ, hTT, hU1, hH2, hBZ, hzz, hnu]
    ring
  have hAYms : 0 ≤ AY + BEY * ms := by
    rw [hJ1] at hEY
    by_contra hcon
    push Not at hcon
    have hneg : ms * (AY + BEY * ms) < 0 := mul_neg_of_pos_of_neg hms hcon
    linarith
  have hAZms : 0 ≤ AZ + BEZ * ms := by
    rw [hJ1z] at hEZ
    by_contra hcon
    push Not at hcon
    have hneg : ms * (AZ + BEZ * ms) < 0 := mul_neg_of_pos_of_neg hms hcon
    linarith
  have hBEYnn : 0 ≤ BEY := by
    rw [hBEY]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg nu) hz0)
      (by linarith)) (by linarith)
  have hBEZnn : 0 ≤ BEZ := by
    rw [hBEZ]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg nu) hb0)
      (by linarith)) (by linarith)
  set GY : ℝ := AY + BEY * (1 - ty - tz) with hGY
  set GZ : ℝ := AZ + BEZ * (1 - ty - tz) with hGZ
  have hGYnn : 0 ≤ GY := by
    have hstep : BEY * ms ≤ BEY * (1 - ty - tz) :=
      mul_le_mul_of_nonneg_left (by linarith) hBEYnn
    rw [hGY]
    linarith [hAYms, hstep]
  have hGZnn : 0 ≤ GZ := by
    have hstep : BEZ * ms ≤ BEZ * (1 - ty - tz) :=
      mul_le_mul_of_nonneg_left (by linarith) hBEZnn
    rw [hGZ]
    linarith [hAZms, hstep]
  have hsyz : (1 - ty) * GY + (1 - tz) * GZ = 0 := by
    rw [hGY, hGZ, hAY, hAZ, hBEY, hBEZ, hzz, hnu]
    ring
  have hGY0 : GY = 0 := by
    have h1 : 0 ≤ (1 - ty) * GY := mul_nonneg (by linarith) hGYnn
    have h2 : 0 ≤ (1 - tz) * GZ := mul_nonneg (by linarith) hGZnn
    have h3 : (1 - ty) * GY = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · exact h
  have hGZ0 : GZ = 0 := by
    have h1 : 0 ≤ (1 - ty) * GY := mul_nonneg (by linarith) hGYnn
    have h2 : 0 ≤ (1 - tz) * GZ := mul_nonneg (by linarith) hGZnn
    have h3 : (1 - tz) * GZ = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · exact h
  have hBEY0 : BEY = 0 := by
    have hGYval : AY + BEY * (1 - ty - tz) = 0 := by rw [← hGY]; exact hGY0
    have hexp : BEY * (1 - ty - tz - ms)
        = (AY + BEY * (1 - ty - tz)) - (AY + BEY * ms) := by ring
    have hchain : BEY * (1 - ty - tz - ms) ≤ 0 := by
      rw [hexp, hGYval]
      linarith [hAYms]
    by_contra hcon
    have hpos : 0 < BEY := lt_of_le_of_ne hBEYnn (Ne.symm hcon)
    have := mul_pos hpos hgap
    linarith
  have hBEZ0 : BEZ = 0 := by
    have hGZval : AZ + BEZ * (1 - ty - tz) = 0 := by rw [← hGZ]; exact hGZ0
    have hexp : BEZ * (1 - ty - tz - ms)
        = (AZ + BEZ * (1 - ty - tz)) - (AZ + BEZ * ms) := by ring
    have hchain : BEZ * (1 - ty - tz - ms) ≤ 0 := by
      rw [hexp, hGZval]
      linarith [hAZms]
    by_contra hcon
    have hpos : 0 < BEZ := lt_of_le_of_ne hBEZnn (Ne.symm hcon)
    have := mul_pos hpos hgap
    linarith
  have hzero : nu ^ 2 * zz * (1 - ty) * (1 - tz)
      + nu ^ 2 * b * (1 - ty) * (1 - tz) = 0 := by
    have e1 : nu ^ 2 * zz * (1 - ty) * (1 - tz) = 0 := by rw [← hBEY]; exact hBEY0
    have e2 : nu ^ 2 * b * (1 - ty) * (1 - tz) = 0 := by rw [← hBEZ]; exact hBEZ0
    linarith
  have hfactor : nu ^ 2 * zz * (1 - ty) * (1 - tz)
      + nu ^ 2 * b * (1 - ty) * (1 - tz)
      = nu ^ 3 * (1 - ty) * (1 - tz) := by
    rw [hzz, hnu]; ring
  rw [hfactor] at hzero
  have hpos : 0 < nu ^ 3 * (1 - ty) * (1 - tz) := by
    have h1 : 0 < nu ^ 3 := by positivity
    have h2 : 0 < 1 - ty := by linarith
    have h3 : 0 < 1 - tz := by linarith
    positivity
  linarith

/-! ## 3. The Sylvester branch: a certified plane form dominates -/

/-- **The four-set through the kept inside atom dominates when its plane
Sylvester datum is positive.**  Parseval pays the outside atoms through the
heaviest outside weight, the frame reduces the residue to a two-by-two form in
the axis plane, and the Sylvester conditions close it. -/
theorem oneAxisZero_fourSet_posDef_branch (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {u w : Fin 3 → ℝ} {lam ay az cy cz ms : ℝ}
    (hunit : u ⬝ᵥ u = 1) (hwunit : w ⬝ᵥ w = 1) (huw : u ⬝ᵥ w = 0)
    (hxu : D.atom x ⬝ᵥ u = 0) (hxw : D.atom x ⬝ᵥ w = 0)
    (hxlev : D.atom x ⬝ᵥ D.atom x = 1)
    (hyd : D.atom y = ay • u + cy • w) (hzd : D.atom z = az • u + cz • w)
    (hmass : ay ^ 2 + az ^ 2 = 1 + lam) (hunit2 : cy ^ 2 + cz ^ 2 = 1)
    (horth : ay * cy + az * cz = 0)
    (hms : 0 < ms) (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d ≤ ms)
    (hmx : ms + D.weight x < 1)
    (hsylC : 0 < 1 - (D.weight y + ms) * cy ^ 2 - D.weight z * cz ^ 2)
    (hsylD : 0 < (1 + ms * lam - (D.weight y + ms) * ay ^ 2 - D.weight z * az ^ 2)
        * (1 - (D.weight y + ms) * cy ^ 2 - D.weight z * cz ^ 2)
      - ((D.weight y + ms) * (ay * cy) + D.weight z * (az * cz)) ^ 2) :
    (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef := by
  classical
  have hzC : z ∈ ({x, y, z} : Finset (Fin 6)) := by simp
  have hzCc : z ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D _), fun v hv => ?_⟩
  rw [star_trivial, quadForm_subsetSum_sub_one, Finset.sum_insert hzCc]
  set X : ℝ := u ⬝ᵥ v with hX
  set Y : ℝ := w ⬝ᵥ v with hY
  set Zr : ℝ := D.atom x ⬝ᵥ v with hZr
  have hres := read_sq_orthonormal_resolution hunit hwunit hxlev huw
    (by rw [dotProduct_comm]; exact hxu) (by rw [dotProduct_comm]; exact hxw) v
  rw [← hX, ← hY, ← hZr] at hres
  have hpar := parseval_read_corner_split D hxy hxz hyz v
  have hyread : D.atom y ⬝ᵥ v = ay * X + cy * Y := by
    rw [hyd, add_dotProduct, smul_dotProduct, smul_dotProduct, hX, hY]
    simp only [smul_eq_mul]
  have hzread : D.atom z ⬝ᵥ v = az * X + cz * Y := by
    rw [hzd, add_dotProduct, smul_dotProduct, smul_dotProduct, hX, hY]
    simp only [smul_eq_mul]
  have hcap : ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d * (D.atom d ⬝ᵥ v) ^ 2
      ≤ ms * ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), (D.atom d ⬝ᵥ v) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun d hd =>
      mul_le_mul_of_nonneg_right (hmd d hd) (sq_nonneg _)
  set ty : ℝ := D.weight y
  set tz : ℝ := D.weight z
  set tx : ℝ := D.weight x
  -- the exact plane reduction of the paid quadratic form
  have hforms : ms * (az * X + cz * Y) ^ 2
      + ((X ^ 2 + Y ^ 2 + Zr ^ 2) - tx * Zr ^ 2 - ty * (ay * X + cy * Y) ^ 2
        - tz * (az * X + cz * Y) ^ 2)
      - ms * (X ^ 2 + Y ^ 2 + Zr ^ 2)
      = (1 - ms - tx) * Zr ^ 2
        + ((1 + ms * lam - (ty + ms) * ay ^ 2 - tz * az ^ 2) * X ^ 2
          + 2 * (-((ty + ms) * (ay * cy) + tz * (az * cz))) * (X * Y)
          + (1 - (ty + ms) * cy ^ 2 - tz * cz ^ 2) * Y ^ 2) := by
    linear_combination (ms * X ^ 2) * hmass + (ms * Y ^ 2) * hunit2
      + (2 * X * Y * ms) * horth
  -- the chain: pay the outside, then read the frame
  have hchain : ms * ((D.atom z ⬝ᵥ v) ^ 2
        + ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), (D.atom d ⬝ᵥ v) ^ 2 - v ⬝ᵥ v)
      ≥ (1 - ms - tx) * Zr ^ 2
        + ((1 + ms * lam - (ty + ms) * ay ^ 2 - tz * az ^ 2) * X ^ 2
          + 2 * (-((ty + ms) * (ay * cy) + tz * (az * cz))) * (X * Y)
          + (1 - (ty + ms) * cy ^ 2 - tz * cz ^ 2) * Y ^ 2) := by
    have hpar' : ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        D.weight d * (D.atom d ⬝ᵥ v) ^ 2
        = v ⬝ᵥ v - tx * Zr ^ 2 - ty * (ay * X + cy * Y) ^ 2
          - tz * (az * X + cz * Y) ^ 2 := by
      rw [← hyread, ← hzread]
      have := hpar
      rw [← hZr] at this
      linarith [this]
    have hvv : v ⬝ᵥ v = X ^ 2 + Y ^ 2 + Zr ^ 2 := hres.symm
    calc ms * ((D.atom z ⬝ᵥ v) ^ 2
          + ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), (D.atom d ⬝ᵥ v) ^ 2 - v ⬝ᵥ v)
        ≥ ms * (D.atom z ⬝ᵥ v) ^ 2
          + ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
              D.weight d * (D.atom d ⬝ᵥ v) ^ 2
          - ms * (v ⬝ᵥ v) := by
          have := hcap
          nlinarith [hcap]
      _ = ms * (az * X + cz * Y) ^ 2
          + ((X ^ 2 + Y ^ 2 + Zr ^ 2) - tx * Zr ^ 2 - ty * (ay * X + cy * Y) ^ 2
            - tz * (az * X + cz * Y) ^ 2)
          - ms * (X ^ 2 + Y ^ 2 + Zr ^ 2) := by
          rw [hpar', hzread, hvv]
      _ = (1 - ms - tx) * Zr ^ 2
          + ((1 + ms * lam - (ty + ms) * ay ^ 2 - tz * az ^ 2) * X ^ 2
            + 2 * (-((ty + ms) * (ay * cy) + tz * (az * cz))) * (X * Y)
            + (1 - (ty + ms) * cy ^ 2 - tz * cz ^ 2) * Y ^ 2) := hforms
  -- positivity of the reduced data
  set Ac : ℝ := 1 + ms * lam - (ty + ms) * ay ^ 2 - tz * az ^ 2 with hAc
  set Bc : ℝ := -((ty + ms) * (ay * cy) + tz * (az * cz)) with hBc
  set Cc : ℝ := 1 - (ty + ms) * cy ^ 2 - tz * cz ^ 2 with hCc
  have hCpos : 0 < Cc := hsylC
  have hDpos : 0 < Ac * Cc - Bc ^ 2 := by
    rw [hAc, hBc, hCc]
    have := hsylD
    nlinarith [hsylD]
  have hQnn : ∀ X' Y' : ℝ, 0 ≤ Ac * X' ^ 2 + 2 * Bc * (X' * Y') + Cc * Y' ^ 2 := by
    intro X' Y'
    have hsq : Cc * (Ac * X' ^ 2 + 2 * Bc * (X' * Y') + Cc * Y' ^ 2)
        = (Ac * Cc - Bc ^ 2) * X' ^ 2 + (Cc * Y' + Bc * X') ^ 2 := by ring
    have hrhs : 0 ≤ (Ac * Cc - Bc ^ 2) * X' ^ 2 + (Cc * Y' + Bc * X') ^ 2 := by
      have := mul_nonneg hDpos.le (sq_nonneg X')
      have := sq_nonneg (Cc * Y' + Bc * X')
      linarith
    nlinarith [hsq, hrhs, hCpos]
  have hQpos : ∀ X' Y' : ℝ, ¬(X' = 0 ∧ Y' = 0)
      → 0 < Ac * X' ^ 2 + 2 * Bc * (X' * Y') + Cc * Y' ^ 2 := by
    intro X' Y' hne
    have hsq : Cc * (Ac * X' ^ 2 + 2 * Bc * (X' * Y') + Cc * Y' ^ 2)
        = (Ac * Cc - Bc ^ 2) * X' ^ 2 + (Cc * Y' + Bc * X') ^ 2 := by ring
    by_cases hX0 : X' = 0
    · have hY0 : Y' ≠ 0 := fun h => hne ⟨hX0, h⟩
      have hpos : 0 < (Ac * Cc - Bc ^ 2) * X' ^ 2 + (Cc * Y' + Bc * X') ^ 2 := by
        rw [hX0]
        have : (Cc * Y' + Bc * 0) ^ 2 = (Cc * Y') ^ 2 := by ring
        have hcy : Cc * Y' ≠ 0 := mul_ne_zero (ne_of_gt hCpos) hY0
        have := sq_pos_of_ne_zero hcy
        nlinarith [this]
      nlinarith [hsq, hpos, hCpos]
    · have hpos : 0 < (Ac * Cc - Bc ^ 2) * X' ^ 2 + (Cc * Y' + Bc * X') ^ 2 := by
        have h1 : 0 < (Ac * Cc - Bc ^ 2) * X' ^ 2 :=
          mul_pos hDpos (sq_pos_of_ne_zero hX0)
        have h2 : 0 ≤ (Cc * Y' + Bc * X') ^ 2 := sq_nonneg _
        linarith
      nlinarith [hsq, hpos, hCpos]
  -- the final assembly
  have hvpos : 0 < v ⬝ᵥ v := dotProduct_self_pos hv
  have hXYZ : 0 < X ^ 2 + Y ^ 2 + Zr ^ 2 := by rw [hres]; exact hvpos
  by_cases hXY : X = 0 ∧ Y = 0
  · have hZne : Zr ≠ 0 := by
      intro h0
      rw [hXY.1, hXY.2, h0] at hXYZ
      norm_num at hXYZ
    have hZpos : 0 < (1 - ms - tx) * Zr ^ 2 :=
      mul_pos (by linarith) (sq_pos_of_ne_zero hZne)
    have hQ := hQnn X Y
    have hbig : 0 < ms * ((D.atom z ⬝ᵥ v) ^ 2
        + ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), (D.atom d ⬝ᵥ v) ^ 2 - v ⬝ᵥ v) := by
      calc (0 : ℝ) < (1 - ms - tx) * Zr ^ 2
            + (Ac * X ^ 2 + 2 * Bc * (X * Y) + Cc * Y ^ 2) := by linarith
        _ ≤ ms * ((D.atom z ⬝ᵥ v) ^ 2
            + ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), (D.atom d ⬝ᵥ v) ^ 2
            - v ⬝ᵥ v) := hchain
    nlinarith [hbig, hms]
  · have hQ := hQpos X Y hXY
    have hZnn : 0 ≤ (1 - ms - tx) * Zr ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have hbig : 0 < ms * ((D.atom z ⬝ᵥ v) ^ 2
        + ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), (D.atom d ⬝ᵥ v) ^ 2 - v ⬝ᵥ v) := by
      calc (0 : ℝ) < (1 - ms - tx) * Zr ^ 2
            + (Ac * X ^ 2 + 2 * Bc * (X * Y) + Cc * Y ^ 2) := by linarith
        _ ≤ ms * ((D.atom z ⬝ᵥ v) ^ 2
            + ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), (D.atom d ⬝ᵥ v) ^ 2
            - v ⬝ᵥ v) := hchain
    nlinarith [hbig, hms]

/-! ## 4. The dichotomy -/

/-- **THE FOUR-SET DICHOTOMY OF THE ONE-ZERO CORNER.**  At a corank-two corner
with positive gap scale whose first inside atom reads the axis at zero and
whose third does not, one of the two four-sets through a single axis-carrying
inside atom dominates strictly — with no tie hypothesis.  Equivalently, the
both-heavy cell of the `Z1` five-set case split is empty. -/
theorem corner_oneAxisZero_fourSet_split (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0) :
    (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef
      ∨ (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef := by
  classical
  obtain ⟨w, hwunit, hwu, hwx, hxlev, hyd, hzd, hmass, hunit2, horth⟩ :=
    corner_oneAxisZero_frame_decomp D hxy hxz hyz hlam.le hunit hgap hax haz
  set ay : ℝ := D.atom y ⬝ᵥ u with hayd
  set az : ℝ := D.atom z ⬝ᵥ u with hazd
  set cy : ℝ := D.atom y ⬝ᵥ w with hcyd
  set cz : ℝ := D.atom z ⬝ᵥ w with hczd
  set ty : ℝ := D.weight y with htyd
  set tz : ℝ := D.weight z with htzd
  set tx : ℝ := D.weight x with htxd
  -- the heaviest outside weight
  have hcardC : ({x, y, z} : Finset (Fin 6)).card = 3 := card_triple_eq hxy hxz hyz
  obtain ⟨d1, d2, d3, h12, h13, h23, hCc⟩ :=
    Finset.card_eq_three.mp (card_compl_eq_three_of_card_eq_three _ hcardC)
  set ms : ℝ := max (D.weight d1) (max (D.weight d2) (D.weight d3)) with hmsd
  have hd1 : d1 ∈ ({x, y, z} : Finset (Fin 6))ᶜ := by rw [hCc]; simp
  have hd2 : d2 ∈ ({x, y, z} : Finset (Fin 6))ᶜ := by rw [hCc]; simp
  have hd3 : d3 ∈ ({x, y, z} : Finset (Fin 6))ᶜ := by rw [hCc]; simp
  have hmspos : 0 < ms := lt_of_lt_of_le (D.weight_pos d1) (le_max_left _ _)
  have hmd : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d ≤ ms := by
    intro d hd
    rw [hCc] at hd
    rcases Finset.mem_insert.mp hd with h | h
    · rw [h, hmsd]; exact le_max_left _ _
    · rcases Finset.mem_insert.mp h with h' | h'
      · rw [h', hmsd]; exact le_trans (le_max_left _ _) (le_max_right _ _)
      · rw [Finset.mem_singleton.mp h', hmsd]
        exact le_trans (le_max_right _ _) (le_max_right _ _)
  have htot : tx + ty + tz + (D.weight d1 + (D.weight d2 + D.weight d3)) = 1 := by
    have := D.weight_sum_one
    rw [← Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin 6)) D.weight,
      sum_triple_eq hxy hxz hyz, hCc, sum_triple_eq h12 h13 h23] at this
    rw [htxd, htyd, htzd]
    linarith
  have hmslt : ms < D.weight d1 + (D.weight d2 + D.weight d3) := by
    rw [hmsd]
    rcases max_cases (D.weight d1) (max (D.weight d2) (D.weight d3)) with
      ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq]
      linarith [D.weight_pos d2, D.weight_pos d3]
    · rw [heq]
      rcases max_cases (D.weight d2) (D.weight d3) with ⟨heq2, _⟩ | ⟨heq2, _⟩
      · rw [heq2]
        linarith [D.weight_pos d1, D.weight_pos d3]
      · rw [heq2]
        linarith [D.weight_pos d1, D.weight_pos d2]
  have hsum : ms + ty + tz < 1 := by
    have := D.weight_pos x
    rw [← htxd] at this
    linarith [htot, hmslt]
  have hmx : ms + tx < 1 := by
    have hy' := D.weight_pos y
    have hz' := D.weight_pos z
    rw [← htyd] at hy'
    rw [← htzd] at hz'
    linarith [htot, hmslt]
  -- the frame-square reductions
  have hnu : (0 : ℝ) < 1 + lam := by linarith
  have hcy2 : (1 + lam) * cy ^ 2 = az ^ 2 := by
    linear_combination (-cy ^ 2) * hmass + az ^ 2 * hunit2
      + (ay * cy - az * cz) * horth
  have hcz2 : (1 + lam) * cz ^ 2 = ay ^ 2 := by
    linear_combination (-cz ^ 2) * hmass + ay ^ 2 * hunit2
      + (az * cz - ay * cy) * horth
  have hccc : (1 + lam) * (ay * az * (cy * cz)) = -(ay ^ 2 * az ^ 2) := by
    linear_combination ((1 + lam) * az * cz) * horth - az ^ 2 * hcz2
  -- the Parseval plane facts of the weighted outside mass
  set N : Matrix (Fin 3) (Fin 3) ℝ :=
    ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d • atomMatrix (D.atom d)
    with hN
  have hNpsd : N.PosSemidef := by
    rw [hN]
    exact Matrix.posSemidef_sum _ fun d _ =>
      (posSemidef_atomMatrix (D.atom d)).smul (D.weight_pos d).le
  have hNread : ∀ v : Fin 3 → ℝ, v ⬝ᵥ (N *ᵥ v)
      = v ⬝ᵥ v - tx * (D.atom x ⬝ᵥ v) ^ 2 - ty * (D.atom y ⬝ᵥ v) ^ 2
        - tz * (D.atom z ⬝ᵥ v) ^ 2 := by
    intro v
    have hquad : v ⬝ᵥ (N *ᵥ v) = ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        D.weight d * (D.atom d ⬝ᵥ v) ^ 2 := by
      rw [hN, Matrix.sum_mulVec, dotProduct_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        show atomMatrix (D.atom d) = Matrix.vecMulVec (D.atom d) (D.atom d) from rfl,
        quadForm_atomMatrix]
    rw [hquad]
    have hpar := parseval_read_corner_split D hxy hxz hyz v
    rw [htxd, htyd, htzd]
    linarith [hpar]
  have hn00 : ty * ay ^ 2 + tz * az ^ 2 ≤ 1 := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hNpsd).2 u
    rw [star_trivial, hNread u, hunit] at h
    have hxu' : D.atom x ⬝ᵥ u = 0 := hax
    have hyu : D.atom y ⬝ᵥ u = ay := rfl
    have hzu : D.atom z ⬝ᵥ u = az := rfl
    rw [hxu', hyu, hzu] at h
    nlinarith [h]
  have hn11 : ty * cy ^ 2 + tz * cz ^ 2 ≤ 1 := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hNpsd).2 w
    rw [star_trivial, hNread w, hwunit] at h
    have hyw' : D.atom y ⬝ᵥ w = cy := rfl
    have hzw' : D.atom z ⬝ᵥ w = cz := rfl
    rw [hwx, hyw', hzw'] at h
    nlinarith [h]
  have hncross : (ty * (ay * cy) + tz * (az * cz)) ^ 2
      ≤ (1 - ty * ay ^ 2 - tz * az ^ 2) * (1 - ty * cy ^ 2 - tz * cz ^ 2) := by
    have hcs := psd_form_cross_sq_le hNpsd u w
    rw [hNread u, hNread w, hunit, hwunit] at hcs
    have hNuw : u ⬝ᵥ (N *ᵥ w) = -(ty * (ay * cy) + tz * (az * cz)) := by
      have hquad : u ⬝ᵥ (N *ᵥ w) = ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          D.weight d * ((D.atom d ⬝ᵥ u) * (D.atom d ⬝ᵥ w)) := by
        rw [hN, Matrix.sum_mulVec, dotProduct_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
          show atomMatrix (D.atom d) = Matrix.vecMulVec (D.atom d) (D.atom d)
            from rfl]
        rw [vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
          dotProduct_comm u (D.atom d)]
        ring_nf
      have hParPol : ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          D.weight d * ((D.atom d ⬝ᵥ u) * (D.atom d ⬝ᵥ w))
          = u ⬝ᵥ w - tx * ((D.atom x ⬝ᵥ u) * (D.atom x ⬝ᵥ w))
            - ty * ((D.atom y ⬝ᵥ u) * (D.atom y ⬝ᵥ w))
            - tz * ((D.atom z ⬝ᵥ u) * (D.atom z ⬝ᵥ w)) := by
        have hpolar := dotProduct_eq_sum_weight_mul_pair D u w
        rw [← Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin 6))
          (fun a => D.weight a * ((D.atom a ⬝ᵥ u) * (D.atom a ⬝ᵥ w))),
          sum_triple_eq hxy hxz hyz] at hpolar
        rw [htxd, htyd, htzd]
        linarith [hpolar]
      rw [hquad, hParPol, hwu, hax]
      have hyu : D.atom y ⬝ᵥ u = ay := rfl
      have hyw' : D.atom y ⬝ᵥ w = cy := rfl
      have hzu : D.atom z ⬝ᵥ u = az := rfl
      have hzw' : D.atom z ⬝ᵥ w = cz := rfl
      rw [hyu, hyw', hzu, hzw']
      ring
    rw [hNuw] at hcs
    have hxu' : D.atom x ⬝ᵥ u = 0 := hax
    have hyu : D.atom y ⬝ᵥ u = ay := rfl
    have hzu : D.atom z ⬝ᵥ u = az := rfl
    have hyw' : D.atom y ⬝ᵥ w = cy := rfl
    have hzw' : D.atom z ⬝ᵥ w = cz := rfl
    rw [hxu', hyu, hzu, hyw', hzw', hwx] at hcs
    nlinarith [hcs]
  -- the two branch conditions
  set DZ : ℝ := lam * (az ^ 2 * ms * (ms - 1 + ty - tz) + ay ^ 2 * (ty - tz)
      + (1 + lam) * tz * (1 - ty))
    - (1 + lam) * ((1 - tz) * (1 - ms - ty)) with hDZ
  set DY : ℝ := lam * (ay ^ 2 * ms * (ms - 1 + tz - ty) + az ^ 2 * (tz - ty)
      + (1 + lam) * ty * (1 - tz))
    - (1 + lam) * ((1 - ty) * (1 - ms - tz)) with hDY
  -- both nonnegative is impossible: the scalar core
  have hnotboth : ¬(0 ≤ DZ ∧ 0 ≤ DY) := by
    rintro ⟨hgez, hgey⟩
    have hz2 : az ^ 2 = 1 + lam - ay ^ 2 := by linarith [hmass]
    rw [hDZ, hz2] at hgez
    rw [hDY, hz2] at hgey
    have hb0 : (0 : ℝ) ≤ ay ^ 2 := sq_nonneg ay
    have hbnu : ay ^ 2 ≤ 1 + lam := by nlinarith [sq_nonneg az, hmass]
    have hn2core : ty * (1 + lam - ay ^ 2) + tz * ay ^ 2 ≤ 1 + lam := by
      have hscaled : (1 + lam) * (ty * cy ^ 2 + tz * cz ^ 2)
          = ty * az ^ 2 + tz * ay ^ 2 := by
        linear_combination ty * hcy2 + tz * hcz2
      have hmul := mul_le_mul_of_nonneg_left hn11 hnu.le
      have hz2y : ty * az ^ 2 = ty * (1 + lam - ay ^ 2) := by rw [hz2]
      linarith [hscaled, hz2y, hmul]
    have hn3core : (ty - tz) ^ 2 * ay ^ 2 * (1 + lam - ay ^ 2)
        ≤ (1 - ty * ay ^ 2 - tz * (1 + lam - ay ^ 2))
          * ((1 + lam) - ty * (1 + lam - ay ^ 2) - tz * ay ^ 2) := by
      have hsq : (1 + lam) * (ty * (ay * cy) + tz * (az * cz)) ^ 2
          = (ty - tz) ^ 2 * (ay ^ 2 * az ^ 2) := by
        linear_combination (ty ^ 2 * ay ^ 2) * hcy2 + (2 * ty * tz) * hccc
          + (tz ^ 2 * az ^ 2) * hcz2
      have hH2v : (1 + lam) * (1 - ty * cy ^ 2 - tz * cz ^ 2)
          = (1 + lam) - ty * az ^ 2 - tz * ay ^ 2 := by
        linear_combination (-ty) * hcy2 + (-tz) * hcz2
      have hstep : (ty - tz) ^ 2 * (ay ^ 2 * az ^ 2)
          ≤ (1 - ty * ay ^ 2 - tz * az ^ 2)
            * ((1 + lam) - ty * az ^ 2 - tz * ay ^ 2) := by
        have hmul := mul_le_mul_of_nonneg_left hncross hnu.le
        rw [hsq] at hmul
        calc (ty - tz) ^ 2 * (ay ^ 2 * az ^ 2)
            ≤ (1 + lam) * ((1 - ty * ay ^ 2 - tz * az ^ 2)
                * (1 - ty * cy ^ 2 - tz * cz ^ 2)) := hmul
          _ = (1 - ty * ay ^ 2 - tz * az ^ 2)
              * ((1 + lam) * (1 - ty * cy ^ 2 - tz * cz ^ 2)) := by ring
          _ = (1 - ty * ay ^ 2 - tz * az ^ 2)
              * ((1 + lam) - ty * az ^ 2 - tz * ay ^ 2) := by rw [hH2v]
      rw [hz2] at hstep
      nlinarith [hstep]
    exact oneAxisZero_fourSet_scalar_core ty tz ms lam (ay ^ 2)
      (by rw [htyd]; exact D.weight_pos y) (by rw [htzd]; exact D.weight_pos z)
      hmspos hlam hb0 hbnu hsum hn2core hn3core (by linarith [hgez])
      (by linarith [hgey])
  -- the branch selection
  by_cases hcase : DZ < 0
  · -- the four-set through z dominates
    left
    have hsylD : 0 < (1 + ms * lam - (ty + ms) * ay ^ 2 - tz * az ^ 2)
        * (1 - (ty + ms) * cy ^ 2 - tz * cz ^ 2)
        - ((ty + ms) * (ay * cy) + tz * (az * cz)) ^ 2 := by
      -- the determinant bridge
      have hC2 : (1 + lam) * (1 - (ty + ms) * cy ^ 2 - tz * cz ^ 2)
          = (1 + lam) - (ty + ms) * az ^ 2 - tz * ay ^ 2 := by
        linear_combination (-(ty + ms)) * hcy2 + (-tz) * hcz2
      have hB2 : (1 + lam) * ((ty + ms) * (ay * cy) + tz * (az * cz)) ^ 2
          = (ty + ms - tz) ^ 2 * (ay ^ 2 * az ^ 2) := by
        linear_combination ((ty + ms) ^ 2 * ay ^ 2) * hcy2
          + (2 * (ty + ms) * tz) * hccc + (tz ^ 2 * az ^ 2) * hcz2
      have hbridge : (1 + lam) * ((1 + ms * lam - (ty + ms) * ay ^ 2 - tz * az ^ 2)
            * (1 - (ty + ms) * cy ^ 2 - tz * cz ^ 2)
          - ((ty + ms) * (ay * cy) + tz * (az * cz)) ^ 2) = -DZ := by
        rw [hDZ]
        linear_combination (1 + ms * lam - (ty + ms) * ay ^ 2 - tz * az ^ 2) * hC2
          - hB2
          + (ay ^ 2 * ms * tz + ay ^ 2 * ty * tz - lam * ms + lam * ty * tz
              - lam * tz + ms * tz * az ^ 2 + ms * tz - ms + ty * tz * az ^ 2
              + ty * tz - ty - tz) * hmass
      have hDZpos : 0 < -DZ := by linarith
      nlinarith [hbridge, hDZpos, hnu]
    have hsylC : 0 < 1 - (ty + ms) * cy ^ 2 - tz * cz ^ 2 := by
      have hcy1 : cy ^ 2 ≤ 1 := by nlinarith [sq_nonneg cz, hunit2]
      have hcz1 : cz ^ 2 ≤ 1 := by nlinarith [sq_nonneg cy, hunit2]
      have h1 : (ty + ms) * cy ^ 2 ≤ ty + ms := by
        nlinarith [sq_nonneg cy, D.weight_pos y]
      have h2 : tz * cz ^ 2 ≤ tz := by nlinarith [sq_nonneg cz, D.weight_pos z]
      linarith [hsum]
    exact oneAxisZero_fourSet_posDef_branch D hxy hxz hyz hunit hwunit hwu hax hwx
      hxlev hyd hzd hmass hunit2 horth hmspos hmd hmx hsylC hsylD
  · -- the four-set through y dominates
    right
    push Not at hcase
    have hDYneg : DY < 0 := by
      by_contra hcon
      push Not at hcon
      exact hnotboth ⟨hcase, hcon⟩
    -- swap the roles of y and z
    have hCswap : ({x, z, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) := by
      ext a
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hsylD : 0 < (1 + ms * lam - (tz + ms) * az ^ 2 - ty * ay ^ 2)
        * (1 - (tz + ms) * cz ^ 2 - ty * cy ^ 2)
        - ((tz + ms) * (az * cz) + ty * (ay * cy)) ^ 2 := by
      have hC2 : (1 + lam) * (1 - (tz + ms) * cz ^ 2 - ty * cy ^ 2)
          = (1 + lam) - (tz + ms) * ay ^ 2 - ty * az ^ 2 := by
        linear_combination (-(tz + ms)) * hcz2 + (-ty) * hcy2
      have hB2 : (1 + lam) * ((tz + ms) * (az * cz) + ty * (ay * cy)) ^ 2
          = (tz + ms - ty) ^ 2 * (ay ^ 2 * az ^ 2) := by
        linear_combination ((tz + ms) ^ 2 * az ^ 2) * hcz2
          + (2 * (tz + ms) * ty) * hccc + (ty ^ 2 * ay ^ 2) * hcy2
      have hbridge : (1 + lam)
            * ((1 + ms * lam - (tz + ms) * az ^ 2 - ty * ay ^ 2)
              * (1 - (tz + ms) * cz ^ 2 - ty * cy ^ 2)
            - ((tz + ms) * (az * cz) + ty * (ay * cy)) ^ 2) = -DY := by
        rw [hDY]
        linear_combination (1 + ms * lam - (tz + ms) * az ^ 2 - ty * ay ^ 2) * hC2
          - hB2
          + (ay ^ 2 * ms * ty + ay ^ 2 * ty * tz - lam * ms + lam * ty * tz
              - lam * ty + ms * ty * az ^ 2 + ms * ty - ms + ty * tz * az ^ 2
              + ty * tz - ty - tz) * hmass
      have hDYpos : 0 < -DY := by linarith
      nlinarith [hbridge, hDYpos, hnu]
    have hsylC : 0 < 1 - (tz + ms) * cz ^ 2 - ty * cy ^ 2 := by
      have hcy1 : cy ^ 2 ≤ 1 := by nlinarith [sq_nonneg cz, hunit2]
      have hcz1 : cz ^ 2 ≤ 1 := by nlinarith [sq_nonneg cy, hunit2]
      have h1 : (tz + ms) * cz ^ 2 ≤ tz + ms := by
        nlinarith [sq_nonneg cz, D.weight_pos z]
      have h2 : ty * cy ^ 2 ≤ ty := by nlinarith [sq_nonneg cy, D.weight_pos y]
      linarith [hsum]
    have hmd' : ∀ d ∈ (({x, z, y} : Finset (Fin 6))ᶜ), D.weight d ≤ ms := by
      rw [hCswap]; exact hmd
    have hgoal := oneAxisZero_fourSet_posDef_branch D hxz hxy (Ne.symm hyz)
      hunit hwunit hwu hax hwx hxlev hzd hyd
      (by linarith [hmass] : az ^ 2 + ay ^ 2 = 1 + lam)
      (by linarith [hunit2] : cz ^ 2 + cy ^ 2 = 1)
      (by linarith [horth] : az * cz + ay * cy = 0)
      hmspos hmd' hmx hsylC hsylD
    rwa [hCswap] at hgoal

end Gtz
