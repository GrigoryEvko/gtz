/-
# The ball perturbation: the Gram data moves by at most `2√r·ε + ε²`

The first brick of Theorem A's chain, taking the exact-corner cap machinery
off the corner. Atoms within `ε` of the simplex vectors have every Gram entry
within `δ₁ = 2√r·ε + ε²` of the exact corner's values: split the difference
bilinearly into three cross terms and apply Cauchy–Schwarz to each. Everything
downstream of the perturbed gate (`κ₁`, the ball bound, the off-window gate
constant already kernel-checked at radius `1/400`) consumes exactly this
estimate.
-/
import Mathlib
import Gtz.Basic

namespace Gtz

variable {k : ℕ}

/-- Cauchy–Schwarz for the raw dot product, in absolute-value form. -/
theorem abs_dotProduct_le (leftVec rightVec : Fin k → ℝ) :
    |leftVec ⬝ᵥ rightVec|
      ≤ Real.sqrt (leftVec ⬝ᵥ leftVec) * Real.sqrt (rightVec ⬝ᵥ rightVec) := by
  have hsq : (leftVec ⬝ᵥ rightVec) ^ 2
      ≤ (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) := by
    simp only [dotProduct, pow_two]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => leftVec i) (fun i => rightVec i)
    calc (∑ i, leftVec i * rightVec i) * (∑ i, leftVec i * rightVec i)
        ≤ (∑ i, leftVec i ^ 2) * (∑ i, rightVec i ^ 2) := by
          nlinarith [hcs]
      _ = (∑ i, leftVec i * leftVec i) * (∑ i, rightVec i * rightVec i) := by
          congr 1 <;> exact Finset.sum_congr rfl fun i _ => (pow_two _)
  calc |leftVec ⬝ᵥ rightVec| = Real.sqrt ((leftVec ⬝ᵥ rightVec) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec)) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (leftVec ⬝ᵥ leftVec) * Real.sqrt (rightVec ⬝ᵥ rightVec) :=
        Real.sqrt_mul (by
          simp only [dotProduct]
          exact Finset.sum_nonneg fun i _ => mul_self_nonneg _) _

/-- **The Gram perturbation bound** `δ₁ = 2√r·ε + ε²`: atoms within `ε` of
reference vectors of squared length `r` have Gram entries within `δ₁` of the
reference Gram. The bilinear split into three cross terms, each capped by
Cauchy–Schwarz. -/
theorem gram_perturbation {rank eps : ℝ}
    {gLeft gRight refLeft refRight : Fin k → ℝ}
    (hrefLeft : refLeft ⬝ᵥ refLeft = rank)
    (hrefRight : refRight ⬝ᵥ refRight = rank)
    (hleftClose : (gLeft - refLeft) ⬝ᵥ (gLeft - refLeft) ≤ eps ^ 2)
    (hrightClose : (gRight - refRight) ⬝ᵥ (gRight - refRight) ≤ eps ^ 2)
    (hepsNonneg : 0 ≤ eps) :
    |gLeft ⬝ᵥ gRight - refLeft ⬝ᵥ refRight|
      ≤ 2 * Real.sqrt rank * eps + eps ^ 2 := by
  set leftDrift := gLeft - refLeft with hleftDrift
  set rightDrift := gRight - refRight with hrightDrift
  have hrankNonneg : 0 ≤ rank := hrefLeft ▸ (by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  -- the bilinear split
  have hsplit : gLeft ⬝ᵥ gRight - refLeft ⬝ᵥ refRight
      = leftDrift ⬝ᵥ rightDrift + leftDrift ⬝ᵥ refRight
        + refLeft ⬝ᵥ rightDrift := by
    rw [hleftDrift, hrightDrift]
    simp only [sub_dotProduct, dotProduct_sub]
    ring
  -- drift lengths are capped by ε
  have hdriftLen : ∀ drift : Fin k → ℝ,
      drift ⬝ᵥ drift ≤ eps ^ 2 → Real.sqrt (drift ⬝ᵥ drift) ≤ eps := by
    intro drift hclose
    calc Real.sqrt (drift ⬝ᵥ drift) ≤ Real.sqrt (eps ^ 2) :=
          Real.sqrt_le_sqrt hclose
      _ = eps := by rw [Real.sqrt_sq hepsNonneg]
  have hrefLen : ∀ ref : Fin k → ℝ, ref ⬝ᵥ ref = rank
      → Real.sqrt (ref ⬝ᵥ ref) = Real.sqrt rank := fun ref href => by
    rw [href]
  -- three Cauchy–Schwarz caps
  have hcross : |leftDrift ⬝ᵥ rightDrift| ≤ eps * eps := by
    calc |leftDrift ⬝ᵥ rightDrift|
        ≤ Real.sqrt (leftDrift ⬝ᵥ leftDrift)
          * Real.sqrt (rightDrift ⬝ᵥ rightDrift) := abs_dotProduct_le _ _
      _ ≤ eps * eps := by
          have hl := hdriftLen leftDrift hleftClose
          have hr := hdriftLen rightDrift hrightClose
          have hlNonneg := Real.sqrt_nonneg (leftDrift ⬝ᵥ leftDrift)
          have hrNonneg := Real.sqrt_nonneg (rightDrift ⬝ᵥ rightDrift)
          nlinarith
  have hleftRef : |leftDrift ⬝ᵥ refRight| ≤ eps * Real.sqrt rank := by
    calc |leftDrift ⬝ᵥ refRight|
        ≤ Real.sqrt (leftDrift ⬝ᵥ leftDrift)
          * Real.sqrt (refRight ⬝ᵥ refRight) := abs_dotProduct_le _ _
      _ ≤ eps * Real.sqrt rank := by
          rw [hrefLen refRight hrefRight]
          exact mul_le_mul_of_nonneg_right (hdriftLen leftDrift hleftClose)
            (Real.sqrt_nonneg rank)
  have hrefRightDrift : |refLeft ⬝ᵥ rightDrift| ≤ Real.sqrt rank * eps := by
    calc |refLeft ⬝ᵥ rightDrift|
        ≤ Real.sqrt (refLeft ⬝ᵥ refLeft)
          * Real.sqrt (rightDrift ⬝ᵥ rightDrift) := abs_dotProduct_le _ _
      _ ≤ Real.sqrt rank * eps := by
          rw [hrefLen refLeft hrefLeft]
          exact mul_le_mul_of_nonneg_left (hdriftLen rightDrift hrightClose)
            (Real.sqrt_nonneg rank)
  -- assemble by the triangle inequality, written through two-sided bounds
  rw [hsplit]
  obtain ⟨hcrossLo, hcrossHi⟩ := abs_le.mp hcross
  obtain ⟨hleftLo, hleftHi⟩ := abs_le.mp hleftRef
  obtain ⟨hrightLo, hrightHi⟩ := abs_le.mp hrefRightDrift
  rw [abs_le]
  constructor
  · nlinarith [hcrossLo, hleftLo, hrightLo]
  · nlinarith [hcrossHi, hleftHi, hrightHi]

end Gtz
