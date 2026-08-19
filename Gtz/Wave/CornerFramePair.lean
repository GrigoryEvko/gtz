import Gtz.Wave.FiveSetPairFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# The frame pair of the one-zero corner, and its modulus-free complement law

At a corank-two corner one inside atom can read the gap axis at zero while the
other two do not — the residual degenerate stratum after
`Gtz.corner_zeroPairings_absurd`.  This module proves that the stratum's two
axis-carrying atoms are RIGID as a pair: their atom sum is exactly the atom sum
of the stretched axis and one unit vector orthogonal to it,

  `G_y + G_z = (1 + lam) • u uᵀ + w wᵀ`   (`Gtz.corner_oneAxisZero_frame_pair`).

The pair carries one modulus — the split of the axis mass between the two
atoms — and the identity says that modulus is invisible to every quantity that
reads only `G_y + G_z`.  The complement refusal of a tie is such a quantity:
`S_{Cᶜ} − 1 = B − (G_y + G_z)` at the five-set anchor `B` of the zero-reading
atom, so the depth-two criterion turns the complement refusal into a
modulus-free disjunction on three readings of `B⁻¹`
(`Gtz.corner_oneAxisZero_complement_law`):

  `1 ≤ (1+lam) · uᵀB⁻¹u`, or
  `(1 − (1+lam)·uᵀB⁻¹u) · (1 − wᵀB⁻¹w) ≤ (1+lam) · (uᵀB⁻¹w)²`.

Together with `Gtz.tie_fiveSet_pair_floor` and the four-set coweight caps this
is the instrument set of the one-zero stratum: the residual fight lives in the
three anchor readings and the outside atoms, with the inside modulus gone.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. Atom sums distribute over vector sums -/

/-- The atom of a sum of two vectors, expanded. -/
theorem atomMatrix_add_expand (a b : Fin 3 → ℝ) :
    atomMatrix (a + b) = atomMatrix a + atomMatrix b
      + (Matrix.vecMulVec a b + Matrix.vecMulVec b a) := by
  ext i j
  simp only [atomMatrix, Matrix.vecMulVec_apply, Matrix.add_apply, Pi.add_apply]
  ring

/-! ## 2. The frame pair -/

/-- **THE FRAME PAIR OF THE ONE-ZERO CORNER.**  At a corank-two corner whose
first inside atom reads the axis at zero and whose third does not, the two
axis-carrying inside atoms have atom sum exactly `(1+lam) • u uᵀ + w wᵀ` for an
explicit unit vector `w` orthogonal to the axis and to the zero atom.  The
one-parameter modulus of the pair drops out of the sum. -/
theorem corner_oneAxisZero_frame_pair (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0) :
    ∃ w : Fin 3 → ℝ, w ⬝ᵥ w = 1 ∧ u ⬝ᵥ w = 0 ∧ D.atom x ⬝ᵥ w = 0
      ∧ atomMatrix (D.atom y) + atomMatrix (D.atom z)
        = (1 + lam) • atomMatrix u + atomMatrix w := by
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have hcard : ({x, y, z} : Finset (Fin m)).card = 3 := card_triple_eq hxy hxz hyz
  have hx : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hy : y ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hz : z ∈ ({x, y, z} : Finset (Fin m)) := by simp
  set ay : ℝ := D.atom y ⬝ᵥ u with hay
  set az : ℝ := D.atom z ⬝ᵥ u with hazv
  have hazsq : (0 : ℝ) < az ^ 2 := by positivity
  -- the axis mass
  have hmass := corner_axis_mass D ({x, y, z} : Finset (Fin m)) hunit hgap
  rw [sum_triple_eq hxy hxz hyz, hax] at hmass
  have hmass' : ay ^ 2 + az ^ 2 = 1 + lam := by linear_combination hmass
  -- the inside leverages and pairings, deflated by 1 + lam
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
  have hcsq' : (1 + lam) * cnorm ^ 2 = az ^ 2 := by rw [hcsq]; exact hw0sq
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
  -- the y decomposition is definitional
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
  -- the three scalar collapses
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
  -- assemble the matrix identity
  refine ⟨w, hwunit, hwu, hwx, ?_⟩
  rw [hyDecomp, hzDecomp, atomMatrix_add_expand, atomMatrix_add_expand,
    atomMatrix_smul, atomMatrix_smul, atomMatrix_smul, atomMatrix_smul,
    Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec,
    Matrix.vecMulVec_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul,
    Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]
  match_scalars <;>
    first
      | linear_combination hmass'
      | linear_combination hsum2
      | linear_combination hsum3
      | linear_combination hsum2 - hsum3
      | linear_combination hsum2 + hsum3
      | linear_combination hmass' + hsum2 - hsum3
      | linear_combination hmass' - hsum3
      | linear_combination hmass' + hsum3

/-! ## 3. The modulus-free complement law -/

/-- **THE MODULUS-FREE COMPLEMENT LAW OF THE ONE-ZERO STRATUM.**  At a `(6,3)`
tie with a corank-two corner whose first inside atom reads the axis at zero
and whose third does not, the five-set anchor `B` of the zero atom is positive
definite, and the complement refusal collapses to a disjunction on three
readings of `B⁻¹` at the frame pair — with the inside modulus absent. -/
theorem corner_oneAxisZero_complement_law (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0) :
    ∃ w : Fin 3 → ℝ, w ⬝ᵥ w = 1 ∧ u ⬝ᵥ w = 0 ∧ D.atom x ⬝ᵥ w = 0
      ∧ (1 ≤ (1 + lam)
            * (u ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹ *ᵥ u))
        ∨ (1 - (1 + lam)
              * (u ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹ *ᵥ u)))
            * (1 - w ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹ *ᵥ w))
          ≤ (1 + lam)
            * (u ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹ *ᵥ w)) ^ 2) := by
  classical
  have hone : (0 : ℝ) < 1 + lam := by linarith
  obtain ⟨w, hwunit, hwu, hwx, hframe⟩ :=
    corner_oneAxisZero_frame_pair D hxy hxz hyz hlam hunit hgap hax haz
  set B : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ((univ : Finset (Fin 6)).erase x) - 1 with hB
  have hPD : B.PosDef :=
    corner_oneAxisZero_fiveSet_posDef D hxy hxz hyz hlam hunit hgap hax
  set su : Fin 3 → ℝ := Real.sqrt (1 + lam) • u with hsu
  have hssq : Real.sqrt (1 + lam) ^ 2 = 1 + lam := Real.sq_sqrt hone.le
  have hsuMat : Matrix.vecMulVec su su = (1 + lam) • atomMatrix u := by
    rw [hsu, show Matrix.vecMulVec (Real.sqrt (1 + lam) • u) (Real.sqrt (1 + lam) • u)
        = atomMatrix (Real.sqrt (1 + lam) • u) from rfl, atomMatrix_smul, hssq]
  have hyE : y ∈ (univ : Finset (Fin 6)).erase x :=
    Finset.mem_erase.mpr ⟨Ne.symm hxy, Finset.mem_univ y⟩
  have hzE : z ∈ (univ : Finset (Fin 6)).erase x :=
    Finset.mem_erase.mpr ⟨Ne.symm hxz, Finset.mem_univ z⟩
  have hdown := subsetSum_erase_erase_sub_one D ((univ : Finset (Fin 6)).erase x)
    hyE hzE hyz
  have hdown' : subsetSum D ((((univ : Finset (Fin 6)).erase x).erase y).erase z) - 1
      = B - Matrix.vecMulVec su su - Matrix.vecMulVec w w := by
    rw [hdown, hsuMat, ← hB]
    have hswap : Matrix.vecMulVec (D.atom y) (D.atom y)
        + Matrix.vecMulVec (D.atom z) (D.atom z)
        = (1 + lam) • atomMatrix u + Matrix.vecMulVec w w := by
      rw [show Matrix.vecMulVec (D.atom y) (D.atom y) = atomMatrix (D.atom y) from rfl,
        show Matrix.vecMulVec (D.atom z) (D.atom z) = atomMatrix (D.atom z) from rfl,
        show Matrix.vecMulVec w w = atomMatrix w from rfl]
      exact hframe
    have hstep : B - Matrix.vecMulVec (D.atom y) (D.atom y)
        - Matrix.vecMulVec (D.atom z) (D.atom z)
        = B - ((1 + lam) • atomMatrix u + Matrix.vecMulVec w w) := by
      rw [← hswap]
      abel
    rw [hstep]
    abel
  have hcard3 : ((((univ : Finset (Fin 6)).erase x).erase y).erase z).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hyz, hzE⟩),
      Finset.card_erase_of_mem hyE,
      Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      Fintype.card_fin]
  have hrefuse := htie.2 _ hcard3
  rw [hdown'] at hrefuse
  have hdisj := (not_posDef_sub_two_vecMulVec_iff B hPD su w).mp hrefuse
  have hread1 : su ⬝ᵥ (B⁻¹ *ᵥ su) = (1 + lam) * (u ⬝ᵥ (B⁻¹ *ᵥ u)) := by
    rw [hsu, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul]
    simp only [smul_eq_mul]
    linear_combination (u ⬝ᵥ (B⁻¹ *ᵥ u)) * hssq
  have hread2 : (su ⬝ᵥ (B⁻¹ *ᵥ w)) ^ 2 = (1 + lam) * (u ⬝ᵥ (B⁻¹ *ᵥ w)) ^ 2 := by
    rw [hsu, smul_dotProduct]
    simp only [smul_eq_mul]
    rw [mul_pow, hssq]
  refine ⟨w, hwunit, hwu, hwx, ?_⟩
  rcases hdisj with hheavy | hminor
  · left
    rw [← hread1]
    exact hheavy
  · right
    rw [← hread1, ← hread2]
    exact hminor

end Gtz
