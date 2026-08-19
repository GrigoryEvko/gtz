/-
# The depth-three downdate: N − g₁g₁ᵀ − g₂g₂ᵀ − g₃g₃ᵀ ≻ 0 ⟺ Sylvester for I₃ − Q

`Gtz/LinAlg/SchurRankOne.lean` prices one removed atom, and
`Gtz/LinAlg/DepthTwoDowndate.lean` prices two.  This module prices THREE
removed atoms at once.  With the readings `q_{ij} = g_iᵀN⁻¹g_j` the criterion
is Sylvester for the 3×3 matrix `I₃ − Q` of the removed triple's Gram in the
`N⁻¹` metric:

  `q₁₁ < 1  ∧  q₁₂² < (1 − q₁₁)(1 − q₂₂)  ∧  det(I₃ − Q) > 0` .

The proof iterates the depth-two criterion through the Sherman–Morrison
inverse of the first downdate.  The second and third readings open to
`r_{ij} = q_{ij} + q_{1i}q_{1j}/(1 − q₁₁)`, and two scalar bridges convert
the depth-two conditions on the `r`-matrix into the trailing Sylvester
minors.  The bridge for the determinant is the Desnanot–Jacobi condensation
identity of `I₃ − Q`,

  `[(1−q₁₁)(1−q₂₂) − q₁₂²]·[(1−q₁₁)(1−q₃₃) − q₁₃²] − [(1−q₁₁)q₂₃ + q₁₂q₁₃]²
     = (1 − q₁₁)·det(I₃ − Q)` ,

carried by one `linear_combination` certificate against `c·(1 − q₁₁) = 1`.

The consumer is the `(6,3)` hinge at the corank-two corner: a triple's gap is
the three-atom downdate of the six-set gap `W = S_univ − 1` at its
complement, so a tie's refusal of EVERY triple is priced by this criterion in
the `W⁻¹` metric — the refusal-consumption direction that makes the tie
system on the six-set pivot matrix exact and two-sided.
-/
import Mathlib
import Gtz.LinAlg.DepthTwoDowndate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {k : ℕ}

/-- **The cross reading opens.**  After removing `g₁`, the mixed reading of
`g₂, g₃` in the downdated metric is `q₂₃ + q₁₂q₁₃/(1 − q₁₁)`. -/
theorem downdate_cross_reading (N : Matrix (Fin k) (Fin k) ℝ) (hN : N.PosDef)
    (g₁ g₂ g₃ : Fin k → ℝ) (hne : g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁) ≠ 1) :
    g₂ ⬝ᵥ ((N - Matrix.vecMulVec g₁ g₁)⁻¹ *ᵥ g₃)
      = g₂ ⬝ᵥ (N⁻¹ *ᵥ g₃)
        + (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁))⁻¹
          * ((g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂)) * (g₁ ⬝ᵥ (N⁻¹ *ᵥ g₃))) := by
  have hNT : Nᵀ = N := PosDef.transpose_eq hN
  have hinvT : (N⁻¹)ᵀ = N⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hNT]
  rw [shermanMorrison_downdate_inv N hN g₁ hne]
  set q₁₃ : ℝ := g₁ ⬝ᵥ (N⁻¹ *ᵥ g₃) with hq₁₃
  have hstep1 : (Matrix.vecMulVec g₁ g₁ * N⁻¹) *ᵥ g₃ = q₁₃ • g₁ := by
    rw [← Matrix.mulVec_mulVec, vecMulVec_mulVec_eq, hq₁₃]
  have hmulVec : (N⁻¹ * Matrix.vecMulVec g₁ g₁ * N⁻¹) *ᵥ g₃
      = q₁₃ • (N⁻¹ *ᵥ g₁) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hstep1, Matrix.mulVec_smul]
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, hmulVec,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hsymm : g₂ ⬝ᵥ (N⁻¹ *ᵥ g₁) = g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂) := dot_mulVec_comm hinvT g₂ g₁
  rw [hsymm]
  ring

/-! ## The two scalar bridges

The depth-two conditions on the opened readings `r_{ij}` translate to the
trailing Sylvester minors of `I₃ − Q` and back.  The inverse enters only
through `c` with `c·(1 − q₁₁) = 1`. -/

/-- **The scalar bridge, downdate to Sylvester.** -/
theorem sylvester_of_downdate_chain {q₁₁ q₂₂ q₃₃ q₁₂ q₁₃ q₂₃ c : ℝ}
    (h1 : q₁₁ < 1) (hc : c * (1 - q₁₁) = 1)
    (hr₂ : q₂₂ + c * q₁₂ ^ 2 < 1)
    (hrdet : (q₂₃ + c * (q₁₂ * q₁₃)) ^ 2
      < (1 - (q₂₂ + c * q₁₂ ^ 2)) * (1 - (q₃₃ + c * q₁₃ ^ 2))) :
    q₁₂ ^ 2 < (1 - q₁₁) * (1 - q₂₂)
      ∧ (1 - q₁₁) * q₂₃ ^ 2 + (1 - q₂₂) * q₁₃ ^ 2 + (1 - q₃₃) * q₁₂ ^ 2
            + 2 * (q₁₂ * q₁₃ * q₂₃)
          < (1 - q₁₁) * (1 - q₂₂) * (1 - q₃₃) := by
  have ha : (0 : ℝ) < 1 - q₁₁ := by linarith
  have hcq : c * (1 - q₁₁) * q₁₂ ^ 2 = q₁₂ ^ 2 := by rw [hc]; ring
  have hA : (0 : ℝ) < 1 - (q₂₂ + c * q₁₂ ^ 2) := by linarith
  refine ⟨by nlinarith [mul_pos ha hA, hcq], ?_⟩
  have hkey : (1 - q₁₁) ^ 2 * ((1 - (q₂₂ + c * q₁₂ ^ 2))
        * (1 - (q₃₃ + c * q₁₃ ^ 2)) - (q₂₃ + c * (q₁₂ * q₁₃)) ^ 2)
      = ((1 - q₁₁) * (1 - q₂₂) - q₁₂ ^ 2)
          * ((1 - q₁₁) * (1 - q₃₃) - q₁₃ ^ 2)
        - ((1 - q₁₁) * q₂₃ + q₁₂ * q₁₃) ^ 2 := by
    linear_combination ((1 - q₁₁) * (q₁₂ ^ 2 * q₃₃ - q₁₂ ^ 2
      - 2 * q₁₂ * q₁₃ * q₂₃ + q₁₃ ^ 2 * q₂₂ - q₁₃ ^ 2)) * hc
  have hpos : (0 : ℝ) < ((1 - q₁₁) * (1 - q₂₂) - q₁₂ ^ 2)
        * ((1 - q₁₁) * (1 - q₃₃) - q₁₃ ^ 2)
      - ((1 - q₁₁) * q₂₃ + q₁₂ * q₁₃) ^ 2 := by
    rw [← hkey]
    exact mul_pos (pow_pos ha 2) (sub_pos.mpr hrdet)
  nlinarith [hpos, ha]

/-- **The scalar bridge, Sylvester to downdate.** -/
theorem downdate_chain_of_sylvester {q₁₁ q₂₂ q₃₃ q₁₂ q₁₃ q₂₃ c : ℝ}
    (h1 : q₁₁ < 1) (hc : c * (1 - q₁₁) = 1)
    (hd₂ : q₁₂ ^ 2 < (1 - q₁₁) * (1 - q₂₂))
    (hd₃ : (1 - q₁₁) * q₂₃ ^ 2 + (1 - q₂₂) * q₁₃ ^ 2 + (1 - q₃₃) * q₁₂ ^ 2
        + 2 * (q₁₂ * q₁₃ * q₂₃)
      < (1 - q₁₁) * (1 - q₂₂) * (1 - q₃₃)) :
    (q₂₂ + c * q₁₂ ^ 2 < 1)
      ∧ (q₂₃ + c * (q₁₂ * q₁₃)) ^ 2
          < (1 - (q₂₂ + c * q₁₂ ^ 2)) * (1 - (q₃₃ + c * q₁₃ ^ 2)) := by
  have ha : (0 : ℝ) < 1 - q₁₁ := by linarith
  have hcpos : (0 : ℝ) < c := by nlinarith [hc, ha]
  have hcq' : c * (1 - q₁₁) * (1 - q₂₂) = 1 - q₂₂ := by rw [hc]; ring
  refine ⟨by nlinarith [mul_pos hcpos (sub_pos.mpr hd₂), hcq'], ?_⟩
  have hkey : (1 - q₁₁) ^ 2 * ((1 - (q₂₂ + c * q₁₂ ^ 2))
        * (1 - (q₃₃ + c * q₁₃ ^ 2)) - (q₂₃ + c * (q₁₂ * q₁₃)) ^ 2)
      = ((1 - q₁₁) * (1 - q₂₂) - q₁₂ ^ 2)
          * ((1 - q₁₁) * (1 - q₃₃) - q₁₃ ^ 2)
        - ((1 - q₁₁) * q₂₃ + q₁₂ * q₁₃) ^ 2 := by
    linear_combination ((1 - q₁₁) * (q₁₂ ^ 2 * q₃₃ - q₁₂ ^ 2
      - 2 * q₁₂ * q₁₃ * q₂₃ + q₁₃ ^ 2 * q₂₂ - q₁₃ ^ 2)) * hc
  have hX : (0 : ℝ) < (1 - (q₂₂ + c * q₁₂ ^ 2)) * (1 - (q₃₃ + c * q₁₃ ^ 2))
      - (q₂₃ + c * (q₁₂ * q₁₃)) ^ 2 := by
    nlinarith [hkey, mul_pos ha (sub_pos.mpr hd₃), mul_pos ha ha]
  linarith [hX]

/-- **The depth-three downdate criterion, strict form.**  For `N ≻ 0`,
removing three atoms keeps the matrix positive definite exactly when the
removed triple's Gram in the `N⁻¹` metric sits strictly below `I₃`, read
through Sylvester: the first reading below one, the leading pair determinant
positive, and the full determinant of `I₃ − Q` positive. -/
theorem posDef_sub_three_vecMulVec_iff (N : Matrix (Fin k) (Fin k) ℝ)
    (hN : N.PosDef) (g₁ g₂ g₃ : Fin k → ℝ) :
    (N - Matrix.vecMulVec g₁ g₁ - Matrix.vecMulVec g₂ g₂
        - Matrix.vecMulVec g₃ g₃).PosDef
      ↔ g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁) < 1
          ∧ (g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂)) ^ 2
              < (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁)) * (1 - g₂ ⬝ᵥ (N⁻¹ *ᵥ g₂))
          ∧ (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁)) * (g₂ ⬝ᵥ (N⁻¹ *ᵥ g₃)) ^ 2
                + (1 - g₂ ⬝ᵥ (N⁻¹ *ᵥ g₂)) * (g₁ ⬝ᵥ (N⁻¹ *ᵥ g₃)) ^ 2
                + (1 - g₃ ⬝ᵥ (N⁻¹ *ᵥ g₃)) * (g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂)) ^ 2
                + 2 * ((g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂)) * (g₁ ⬝ᵥ (N⁻¹ *ᵥ g₃))
                  * (g₂ ⬝ᵥ (N⁻¹ *ᵥ g₃)))
              < (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁)) * (1 - g₂ ⬝ᵥ (N⁻¹ *ᵥ g₂))
                  * (1 - g₃ ⬝ᵥ (N⁻¹ *ᵥ g₃)) := by
  constructor
  · intro hpd
    have hN₁ : (N - Matrix.vecMulVec g₁ g₁).PosDef := by
      have h3 := Matrix.PosDef.add_posSemidef hpd (posSemidef_atomMatrix g₃)
      rw [show atomMatrix g₃ = Matrix.vecMulVec g₃ g₃ from rfl,
        sub_add_cancel] at h3
      have h2 := Matrix.PosDef.add_posSemidef h3 (posSemidef_atomMatrix g₂)
      rwa [show atomMatrix g₂ = Matrix.vecMulVec g₂ g₂ from rfl,
        sub_add_cancel] at h2
    have hq₁ : g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁) < 1 := (posDef_sub_vecMulVec_iff N hN g₁).mp hN₁
    have ha : (0 : ℝ) < 1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁) := by linarith
    have hc : (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁))⁻¹ * (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁)) = 1 :=
      inv_mul_cancel₀ (ne_of_gt ha)
    have hpair := (posDef_sub_two_vecMulVec_iff (N - Matrix.vecMulVec g₁ g₁)
      hN₁ g₂ g₃).mp hpd
    rw [downdate_reading N hN g₁ g₂ (ne_of_lt hq₁),
      downdate_reading N hN g₁ g₃ (ne_of_lt hq₁),
      downdate_cross_reading N hN g₁ g₂ g₃ (ne_of_lt hq₁)] at hpair
    exact ⟨hq₁, sylvester_of_downdate_chain hq₁ hc hpair.1 hpair.2⟩
  · rintro ⟨hq₁, hd₂, hd₃⟩
    have ha : (0 : ℝ) < 1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁) := by linarith
    have hc : (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁))⁻¹ * (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁)) = 1 :=
      inv_mul_cancel₀ (ne_of_gt ha)
    have hN₁ : (N - Matrix.vecMulVec g₁ g₁).PosDef :=
      (posDef_sub_vecMulVec_iff N hN g₁).mpr hq₁
    obtain ⟨hr₂, hrdet⟩ := downdate_chain_of_sylvester hq₁ hc hd₂ hd₃
    refine (posDef_sub_two_vecMulVec_iff (N - Matrix.vecMulVec g₁ g₁)
      hN₁ g₂ g₃).mpr ⟨?_, ?_⟩
    · rw [downdate_reading N hN g₁ g₂ (ne_of_lt hq₁)]
      exact hr₂
    · rw [downdate_reading N hN g₁ g₂ (ne_of_lt hq₁),
        downdate_reading N hN g₁ g₃ (ne_of_lt hq₁),
        downdate_cross_reading N hN g₁ g₂ g₃ (ne_of_lt hq₁)]
      exact hrdet

/-- **The refusal reading at depth three.**  The triple downdate FAILS to be
positive definite exactly when one of the three Sylvester minors of `I₃ − Q`
gives way.  This is the form a tie's refusal of a triple takes in the
six-set metric. -/
theorem not_posDef_sub_three_vecMulVec_iff (N : Matrix (Fin k) (Fin k) ℝ)
    (hN : N.PosDef) (g₁ g₂ g₃ : Fin k → ℝ) :
    ¬ (N - Matrix.vecMulVec g₁ g₁ - Matrix.vecMulVec g₂ g₂
        - Matrix.vecMulVec g₃ g₃).PosDef
      ↔ 1 ≤ g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁)
          ∨ (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁)) * (1 - g₂ ⬝ᵥ (N⁻¹ *ᵥ g₂))
              ≤ (g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂)) ^ 2
          ∨ (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁)) * (1 - g₂ ⬝ᵥ (N⁻¹ *ᵥ g₂))
                  * (1 - g₃ ⬝ᵥ (N⁻¹ *ᵥ g₃))
              ≤ (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁)) * (g₂ ⬝ᵥ (N⁻¹ *ᵥ g₃)) ^ 2
                + (1 - g₂ ⬝ᵥ (N⁻¹ *ᵥ g₂)) * (g₁ ⬝ᵥ (N⁻¹ *ᵥ g₃)) ^ 2
                + (1 - g₃ ⬝ᵥ (N⁻¹ *ᵥ g₃)) * (g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂)) ^ 2
                + 2 * ((g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂)) * (g₁ ⬝ᵥ (N⁻¹ *ᵥ g₃))
                  * (g₂ ⬝ᵥ (N⁻¹ *ᵥ g₃))) := by
  rw [posDef_sub_three_vecMulVec_iff N hN g₁ g₂ g₃]
  constructor
  · intro hnot
    by_cases h1 : g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁) < 1
    · by_cases h2 : (g₁ ⬝ᵥ (N⁻¹ *ᵥ g₂)) ^ 2
          < (1 - g₁ ⬝ᵥ (N⁻¹ *ᵥ g₁)) * (1 - g₂ ⬝ᵥ (N⁻¹ *ᵥ g₂))
      · right; right
        by_contra hlt
        exact hnot ⟨h1, h2, not_le.mp hlt⟩
      · right; left
        exact not_lt.mp h2
    · left
      exact not_lt.mp h1
  · rintro (hge | hle | hle) ⟨h1, h2, h3⟩
    · linarith
    · linarith
    · linarith

end Gtz
