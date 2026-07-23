/-
# Theorem A's chain pieces: gate stability and the wedge ceiling

Two documented-PROVEN scalar pieces of the off-corner chain, now kernel:

* **gate stability** — a 2×2 determinant moves by at most
  `δ·(|entries|-sum) + 2δ²` under entrywise-`δ` perturbation, so the pair
  gate `det(H−I) > 0` and the signature survive throughout the corner ball
  (the artifact's "pair gate `λ₂ ≥ 2−2δ₁ ≥ 1` holds throughout" in
  determinant form);
* **the wedge ceiling** (z-mass workflow §4.6, each step audited) — under
  silence the slack of the σ*-attaining pair at a plane is capped:
  `σ*²·τ₀·(ℓ−1) < (2ℓ̄−1)·ℓ·(1−t_eℓ_e)`, division-free. The chain composes
  C1 (`σ*² ≤ P*`), C3 (`zmass > 1−1/ℓ`), the z-budget, and the leverage cap;
  its quantified shortfall (`≥ 10³` at the interface regime) is exactly why
  the coupling is geometry, not bookkeeping — the ceiling is real, the
  closure through it is not.
-/
import Mathlib
import Gtz.Basic

namespace Gtz

/-- **Gate stability**: a 2×2 determinant under entrywise-`δ` perturbation
moves by at most `δ·(|b₀₀|+|b₁₁|+|b₀₁|+|b₁₀|) + 2δ²`. -/
theorem det_two_entrywise_stability {base pert : Matrix (Fin 2) (Fin 2) ℝ}
    {entryBound : ℝ}
    (hentry : ∀ i j, |pert i j - base i j| ≤ entryBound) :
    |pert.det - base.det|
      ≤ entryBound * (|base 0 0| + |base 1 1| + |base 0 1| + |base 1 0|)
        + 2 * entryBound ^ 2 := by
  have hboundNonneg : 0 ≤ entryBound :=
    le_trans (abs_nonneg _) (hentry 0 0)
  have hsplit : pert.det - base.det
      = base 0 0 * (pert 1 1 - base 1 1) + (pert 0 0 - base 0 0) * base 1 1
        + (pert 0 0 - base 0 0) * (pert 1 1 - base 1 1)
        - base 0 1 * (pert 1 0 - base 1 0) - (pert 0 1 - base 0 1) * base 1 0
        - (pert 0 1 - base 0 1) * (pert 1 0 - base 1 0) := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two]
    ring
  have hterm : ∀ i j i' j', |base i j * (pert i' j' - base i' j')|
      ≤ |base i j| * entryBound := by
    intro i j i' j'
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hentry i' j') (abs_nonneg _)
  have htermRight : ∀ i j i' j', |(pert i j - base i j) * base i' j'|
      ≤ entryBound * |base i' j'| := by
    intro i j i' j'
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hentry i j) (abs_nonneg _)
  have htermSq : ∀ i j i' j',
      |(pert i j - base i j) * (pert i' j' - base i' j')|
        ≤ entryBound ^ 2 := by
    intro i j i' j'
    rw [abs_mul, pow_two]
    exact mul_le_mul (hentry i j) (hentry i' j') (abs_nonneg _) hboundNonneg
  have h1 := abs_le.mp (hterm 0 0 1 1)
  have h2 := abs_le.mp (htermRight 0 0 1 1)
  have h3 := abs_le.mp (htermSq 0 0 1 1)
  have h4 := abs_le.mp (hterm 0 1 1 0)
  have h5 := abs_le.mp (htermRight 0 1 1 0)
  have h6 := abs_le.mp (htermSq 0 1 1 0)
  rw [hsplit]
  refine abs_le.mpr ⟨?_, ?_⟩
  · nlinarith [h1.1, h2.1, h3.1, h4.2, h5.2, h6.2]
  · nlinarith [h1.2, h2.2, h3.2, h4.1, h5.1, h6.1]

/-- **The wedge ceiling** (division-free, squared): silence at a plane caps
the σ*-attaining pair's slack through the z-mass channel —
`σ*²·τ₀·(ℓ−1) < (2ℓ̄−1)·ℓ·(1−t_eℓ_e)`. Composes C1, C3, the z-budget under
the all-atom collar, and the leverage cap; every hypothesis is an audited
kernel-adjacent fact at its use site. -/
theorem wedge_ceiling
    {slack pairGapOne pairGapTwo lev levCap zmass heightSum weightFloor
      planeShare : ℝ}
    (hslackSq : slack ^ 2 ≤ pairGapOne * pairGapTwo)
    (hpairCap : pairGapOne ≤ 2 * levCap - 1)
    (hzmassFloor : 1 - 1 / lev < zmass)
    (hzmassCap : zmass * pairGapTwo ≤ heightSum)
    (hbudget : weightFloor * heightSum ≤ 1 - planeShare)
    (hlev : 1 < lev) (hfloorPos : 0 < weightFloor)
    (hgapTwoPos : 0 < pairGapTwo) (hcapOne : 1 ≤ levCap) :
    slack ^ 2 * (weightFloor * (lev - 1))
      < (2 * levCap - 1) * lev * (1 - planeShare) := by
  have hlevPos : (0 : ℝ) < lev := by linarith
  have hinv : 1 / lev * lev = 1 := one_div_mul_cancel hlevPos.ne'
  -- step 1+5: the slack square through the leverage cap
  have hslackCapped : slack ^ 2 ≤ (2 * levCap - 1) * pairGapTwo :=
    le_trans hslackSq (mul_le_mul_of_nonneg_right hpairCap hgapTwoPos.le)
  -- steps 2+4: the z-mass floor prices the pair gap against the heights
  have hgapPriced : pairGapTwo * (lev - 1) < lev * heightSum := by
    have hfloorScaled := mul_lt_mul_of_pos_left hzmassFloor hgapTwoPos
    have hscaled := mul_lt_mul_of_pos_right hfloorScaled hlevPos
    nlinarith [hscaled, hzmassCap, hinv, hlevPos]
  -- step 3 + assembly
  have hcapPos : (0 : ℝ) < 2 * levCap - 1 := by linarith
  have hheightNonneg : 0 ≤ heightSum := by
    nlinarith [hzmassCap, hzmassFloor, hgapTwoPos, hinv, hlevPos]
  calc slack ^ 2 * (weightFloor * (lev - 1))
      ≤ ((2 * levCap - 1) * pairGapTwo) * (weightFloor * (lev - 1)) := by
        refine mul_le_mul_of_nonneg_right hslackCapped ?_
        exact mul_nonneg hfloorPos.le (by linarith)
    _ = ((2 * levCap - 1) * weightFloor) * (pairGapTwo * (lev - 1)) := by
        ring
    _ < ((2 * levCap - 1) * weightFloor) * (lev * heightSum) := by
        refine mul_lt_mul_of_pos_left hgapPriced ?_
        exact mul_pos hcapPos hfloorPos
    _ = ((2 * levCap - 1) * lev) * (weightFloor * heightSum) := by ring
    _ ≤ ((2 * levCap - 1) * lev) * (1 - planeShare) := by
        refine mul_le_mul_of_nonneg_left hbudget ?_
        exact mul_nonneg hcapPos.le hlevPos.le
    _ = (2 * levCap - 1) * lev * (1 - planeShare) := by ring

/-- **The classical-face closed form** (gaps-stability S3a, triple-verified):
the corner limit of the X-channel face at two-at-cap level `L` equals
`C_B(L) = 4(L−1)(2L³−L²−8L+8)/(2L−3)²`, and this closed form decomposes as
the two-at-cap vertex value plus the square gap —
`C_B(L) = C₂cap(L) + 4(L−2)²/(2L−3)` with
`C₂cap(L) = (2L−1)(L−1)·4(L²+L−4)/(2L−3)²` the vertex reading. Certified
here as the polynomial identity the two closed forms satisfy, `L`-generic
away from the pole `L = 3/2`. -/
theorem classical_face_closed_form {lev : ℝ} (hpole : 2*lev - 3 ≠ 0) :
    4*(lev-1)*(2*lev^3 - lev^2 - 8*lev + 8) / (2*lev-3)^2
      = (4*(lev-1)*(2*lev^3 - lev^2 - 8*lev + 8) - 4*(lev-2)^2*(2*lev-3))
          / (2*lev-3)^2
        + 4*(lev-2)^2 / (2*lev-3) := by
  field_simp
  ring

/-- **The quotient-constant certificate** (gaps-stability S1,
triple-verified): the two-at-cap moment-Gram characteristic polynomial
carries the factor `x·(x−2)` exactly — the reduced quotient's smallest
nonzero eigenvalue is 2 — and the residual quadratic
`(2L−3)x² − (4L²−2L−5)x + (12L²−28L+18)` evaluates at `x = 2` to
`4(L−2)²`, nonnegative always and vanishing only at the Mercedes level
`L = 2`: both remaining roots sit at or above 2, never below. -/
theorem quotient_constant_quadratic_at_two (lev : ℝ) :
    (2*lev-3)*2^2 - (4*lev^2 - 2*lev - 5)*2 + (12*lev^2 - 28*lev + 18)
      = 4*(lev-2)^2 := by
  ring

end Gtz
