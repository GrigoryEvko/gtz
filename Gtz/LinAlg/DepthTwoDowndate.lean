/-
# The depth-two downdate: N − g₁g₁ᵀ − g₂g₂ᵀ ≻ 0 ⟺ the 2×2 Gram in the N⁻¹ metric sits below I₂

`Gtz/LinAlg/SchurRankOne.lean` prices one removed atom: for N ≻ 0, the downdate
N − ggᵀ is PD iff the reading gᵀN⁻¹g is below one.  This module prices TWO
removed atoms at once.  With the readings

  `q₁₁ = g₁ᵀN⁻¹g₁,  q₂₂ = g₂ᵀN⁻¹g₂,  q₁₂ = g₁ᵀN⁻¹g₂`

the criterion is

  `N − g₁g₁ᵀ − g₂g₂ᵀ ≻ 0  ⟺  q₁₁ < 1  ∧  q₁₂² < (1 − q₁₁)(1 − q₂₂)`

which is exactly Sylvester for the 2×2 matrix `I₂ − Q` of the removed pair's
Gram in the N⁻¹ metric.  The proof iterates the depth-one lemma through the
Sherman–Morrison inverse of the first downdate, so no block Schur API is
needed: `(N − g₁g₁ᵀ)⁻¹ = N⁻¹ + (1 − q₁₁)⁻¹ N⁻¹g₁g₁ᵀN⁻¹`, and the second
reading opens to `q₂₂ + q₁₂²/(1 − q₁₁)`.

The consumer is the corank-two arm of the `(6,3)` hinge: a one-shared triple
`{e, d₁, d₂}` is the five-set `C ∪ {d₁, d₂}` with two inside atoms removed, so
its refusal at a tie is priced by this criterion in the five-set anchor
metric.  The same instrument prices the triples beyond the four-set that the
corank-one conic theorem needs.

The criterion is symmetric in the pair even though the proof is sequential:
`q₁₂² < (1 − q₁₁)(1 − q₂₂)` together with `q₁₁ < 1` forces `q₂₂ < 1`.
-/
import Mathlib
import Gtz.LinAlg.SchurRankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {k : ℕ}

/-- A rank-one operator eats a matrix from the right through a `mulVec`. -/
theorem vecMulVec_mul (a b : Fin k → ℝ) (M : Matrix (Fin k) (Fin k) ℝ) :
    Matrix.vecMulVec a b * M = Matrix.vecMulVec a (Mᵀ *ᵥ b) := by
  ext rowIndex colIndex
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec,
    Matrix.transpose_apply, dotProduct]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun index _ => by ring

/-- **The Sherman–Morrison inverse of a rank-one downdate.**  For `N ≻ 0` with
reading `q = gᵀN⁻¹g ≠ 1`, the downdate `N − ggᵀ` has the explicit inverse
`N⁻¹ + (1 − q)⁻¹ · N⁻¹ggᵀN⁻¹`. -/
theorem shermanMorrison_downdate_inv (N : Matrix (Fin k) (Fin k) ℝ) (hN : N.PosDef)
    (g : Fin k → ℝ) (hne : g ⬝ᵥ (N⁻¹ *ᵥ g) ≠ 1) :
    (N - Matrix.vecMulVec g g)⁻¹
      = N⁻¹ + (1 - g ⬝ᵥ (N⁻¹ *ᵥ g))⁻¹
          • (N⁻¹ * Matrix.vecMulVec g g * N⁻¹) := by
  have hdet : IsUnit N.det := isUnit_iff_ne_zero.mpr (ne_of_gt hN.det_pos)
  have hNT : Nᵀ = N := PosDef.transpose_eq hN
  have hinvT : (N⁻¹)ᵀ = N⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hNT]
  set q : ℝ := g ⬝ᵥ (N⁻¹ *ᵥ g) with hq
  refine Matrix.inv_eq_right_inv ?_
  have hGN : Matrix.vecMulVec g g * N⁻¹ = Matrix.vecMulVec g (N⁻¹ *ᵥ g) := by
    rw [vecMulVec_mul, hinvT]
  have hGNG : Matrix.vecMulVec g g * N⁻¹ * Matrix.vecMulVec g g
      = q • Matrix.vecMulVec g g := by
    rw [hGN, vecMulVec_mul_vecMulVec]
    rw [show (N⁻¹ *ᵥ g) ⬝ᵥ g = q from by rw [hq, dotProduct_comm]]
  have hexpand : (N - Matrix.vecMulVec g g)
        * (N⁻¹ + (1 - q)⁻¹ • (N⁻¹ * Matrix.vecMulVec g g * N⁻¹))
      = 1 + ((1 - q)⁻¹ - 1 - (1 - q)⁻¹ * q) • (Matrix.vecMulVec g g * N⁻¹) := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.mul_nonsing_inv N hdet, Matrix.mul_smul, Matrix.mul_smul]
    have hNassoc : N * (N⁻¹ * Matrix.vecMulVec g g * N⁻¹)
        = Matrix.vecMulVec g g * N⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv N hdet,
        Matrix.one_mul]
    have hGassoc : Matrix.vecMulVec g g * (N⁻¹ * Matrix.vecMulVec g g * N⁻¹)
        = q • (Matrix.vecMulVec g g * N⁻¹) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGNG, Matrix.smul_mul]
    rw [hNassoc, hGassoc, smul_smul]
    abel_nf
    module
  rw [hexpand]
  have hcoeff : (1 - q)⁻¹ - 1 - (1 - q)⁻¹ * q = 0 := by
    have hsub : (1 : ℝ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    field_simp
    ring
  rw [hcoeff, zero_smul, add_zero]

/-- **The second reading opens.**  After removing `g₁`, the reading of `g₂` in
the downdated metric is `q₂₂ + q₁₂²/(1 − q₁₁)`. -/
theorem downdate_reading (N : Matrix (Fin k) (Fin k) ℝ) (hN : N.PosDef)
    (g₁ g₂ : Fin k → ℝ) (hne : g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁) ≠ 1) :
    g₂ ⬝ᵥ ((N - Matrix.vecMulVec g₁ g₁)⁻¹ *ᵥ g₂)
      = g₂ ⬝ᵥ (N⁻¹ *ᵥ g₂)
        + (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁))⁻¹ * (g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂)) ^ 2 := by
  have hNT : Nᵀ = N := PosDef.transpose_eq hN
  have hinvT : (N⁻¹)ᵀ = N⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hNT]
  rw [shermanMorrison_downdate_inv N hN g₁ hne]
  set q₁₂ : ℝ := g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂) with hq₁₂
  have hstep1 : (Matrix.vecMulVec g₁ g₁ * N⁻¹) *ᵥ g₂ = q₁₂ • g₁ := by
    rw [← Matrix.mulVec_mulVec, vecMulVec_mulVec_eq, hq₁₂]
  have hmulVec : (N⁻¹ * Matrix.vecMulVec g₁ g₁ * N⁻¹) *ᵥ g₂
      = q₁₂ • (N⁻¹ *ᵥ g₁) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hstep1, Matrix.mulVec_smul]
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, hmulVec,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hsymm : g₂ ⬝ᵥ (N⁻¹ *ᵥ g₁) = q₁₂ := by
    rw [hq₁₂, dot_mulVec_comm hinvT]
  rw [hsymm]
  ring

/-- **The depth-two downdate criterion, strict form.**  For `N ≻ 0`, removing
two atoms keeps the matrix PD exactly when the removed pair's Gram in the
`N⁻¹` metric sits strictly below `I₂`, read through Sylvester: the first
reading is below one and the Gram determinant `(1−q₁₁)(1−q₂₂) − q₁₂²` is
positive. -/
theorem posDef_sub_two_vecMulVec_iff (N : Matrix (Fin k) (Fin k) ℝ) (hN : N.PosDef)
    (g₁ g₂ : Fin k → ℝ) :
    (N - Matrix.vecMulVec g₁ g₁ - Matrix.vecMulVec g₂ g₂).PosDef
      ↔ g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁) < 1
          ∧ (g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂)) ^ 2
              < (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁)) * (1 - g₂ ⬝ᵥ (N⁻¹ *ᵥ g₂)) := by
  set q₁₁ : ℝ := g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁) with hq₁₁
  set q₂₂ : ℝ := g₂ ⬝ᵥ (N⁻¹ *ᵥ g₂) with hq₂₂
  set q₁₂ : ℝ := g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂) with hq₁₂
  constructor
  · intro hpd
    have hfirst : (N - Matrix.vecMulVec g₁ g₁).PosDef := by
      have hsum : (N - Matrix.vecMulVec g₁ g₁ - Matrix.vecMulVec g₂ g₂)
          + Matrix.vecMulVec g₂ g₂ = N - Matrix.vecMulVec g₁ g₁ := by
        abel
      have hadd := Matrix.PosDef.add_posSemidef hpd (posSemidef_atomMatrix g₂)
      rwa [show atomMatrix g₂ = Matrix.vecMulVec g₂ g₂ from rfl, hsum] at hadd
    have hq₁ : q₁₁ < 1 := (posDef_sub_vecMulVec_iff N hN g₁).mp hfirst
    refine ⟨hq₁, ?_⟩
    have hsecond : g₂ ⬝ᵥ ((N - Matrix.vecMulVec g₁ g₁)⁻¹ *ᵥ g₂) < 1 :=
      (posDef_sub_vecMulVec_iff (N - Matrix.vecMulVec g₁ g₁) hfirst g₂).mp hpd
    rw [downdate_reading N hN g₁ g₂ (ne_of_lt hq₁)] at hsecond
    have hpos : (0 : ℝ) < 1 - q₁₁ := by linarith
    have hinv : (1 - q₁₁)⁻¹ * (1 - q₁₁) = 1 :=
      inv_mul_cancel₀ (ne_of_gt hpos)
    nlinarith [hsecond, hpos, hinv, sq_nonneg q₁₂,
      mul_pos (inv_pos.mpr hpos) hpos]
  · rintro ⟨hq₁, hdet⟩
    have hfirst : (N - Matrix.vecMulVec g₁ g₁).PosDef :=
      (posDef_sub_vecMulVec_iff N hN g₁).mpr hq₁
    have hpos : (0 : ℝ) < 1 - q₁₁ := by linarith
    have hreading : g₂ ⬝ᵥ ((N - Matrix.vecMulVec g₁ g₁)⁻¹ *ᵥ g₂) < 1 := by
      rw [downdate_reading N hN g₁ g₂ (ne_of_lt hq₁)]
      have hexpand : (1 - q₁₁)⁻¹ * ((1 - q₁₁) * (1 - q₂₂)) = 1 - q₂₂ := by
        field_simp
      nlinarith [mul_lt_mul_of_pos_left hdet (inv_pos.mpr hpos), hexpand]
    exact (posDef_sub_vecMulVec_iff (N - Matrix.vecMulVec g₁ g₁) hfirst g₂).mpr
      hreading

/-- The pair's second reading is also below one: the criterion is symmetric in
the removed pair even though its statement reads the atoms in order. -/
theorem second_reading_lt_one_of_posDef_sub_two (N : Matrix (Fin k) (Fin k) ℝ)
    (hN : N.PosDef) (g₁ g₂ : Fin k → ℝ)
    (hpd : (N - Matrix.vecMulVec g₁ g₁ - Matrix.vecMulVec g₂ g₂).PosDef) :
    g₂ ⬝ᵥ (N⁻¹ *ᵥ g₂) < 1 := by
  obtain ⟨hq₁, hdet⟩ := (posDef_sub_two_vecMulVec_iff N hN g₁ g₂).mp hpd
  nlinarith [sq_nonneg (g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂))]

/-- **The refusal reading.**  The depth-two downdate FAILS to be PD exactly
when the first reading reaches one or the `N⁻¹`-Gram determinant of the pair
gives way.  This is the form a tie's refusal of a one-shared triple takes in
the five-set anchor metric. -/
theorem not_posDef_sub_two_vecMulVec_iff (N : Matrix (Fin k) (Fin k) ℝ)
    (hN : N.PosDef) (g₁ g₂ : Fin k → ℝ) :
    ¬ (N - Matrix.vecMulVec g₁ g₁ - Matrix.vecMulVec g₂ g₂).PosDef
      ↔ 1 ≤ g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁)
          ∨ (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁)) * (1 - g₂ ⬝ᵥ (N⁻¹ *ᵥ g₂))
              ≤ (g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂)) ^ 2 := by
  rw [posDef_sub_two_vecMulVec_iff N hN g₁ g₂]
  constructor
  · intro hnot
    by_cases hfirst : g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁) < 1
    · right
      by_contra hlt
      exact hnot ⟨hfirst, not_le.mp hlt⟩
    · left
      exact not_lt.mp hfirst
  · rintro (hge | hle) ⟨hlt, hdet⟩
    · linarith
    · linarith

end Gtz
