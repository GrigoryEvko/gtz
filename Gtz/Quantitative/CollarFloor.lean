/-
# The collar floor and the off-window fire

Two exact statements from the sub-gap V layer.

**The R1 rescaled floor.** The rescaled anchored covector component on the R1
stratum is `m(T) = (1+T)/((1−T)(3+T))`. It is strictly increasing on `[0,1)`
with value `1/3` at the endpoint `T = 0`, so `m ≥ 1/3` uniformly — no `τ`-floor
is needed on R1, which is what makes the collar statement survive down to
arbitrarily small extra weight. The monotonicity has the clean cross-multiplied
form `(T₂−T₁)(5 + T₁ + T₂ + T₁T₂) > 0`; nothing about the chart enters.

**The off-window fire.** The cap value in the ball is bounded by
`(3−δ)(F(u) + κ)` with the corner normal form `F(u) = −1/3 + (4/3)G(u)`, and the
whole gate collapses to one algebraic identity:

  `(3−δ)(−1/3 + (4/3)G + κ) + 1 = −(4/3)(3−δ)( (−G) − G₀ )`,
  `G₀ = δ/(4(3−δ)) + (3/4)κ`.

So the cap fires exactly when `−G ≥ G₀`, with margin `(4/3)(3−δ)((−G) − G₀)`.
The chain is weight-free — no `τ` appears anywhere — which is why the
off-window half of the collar is discharged for every extra weight at once.
At the ball radius `1/400` the gate constant is strictly below `1/50`, so the
Cauchy–Schwarz branch of the real quantitative bound clears it with room; that
strictness is the difference between a decorative radius and a working one.
-/
import Mathlib

namespace Gtz

/-! ### The R1 rescaled floor -/

/-- The rescaled anchored covector component on the R1 stratum. -/
noncomputable def collarFloorRate (tieParameter : ℝ) : ℝ :=
  (1 + tieParameter) / ((1 - tieParameter) * (3 + tieParameter))

/-- The denominator is positive on the whole stratum. -/
theorem collarDenominator_pos {tieParameter : ℝ} (hnonneg : 0 ≤ tieParameter)
    (hlt : tieParameter < 1) :
    0 < (1 - tieParameter) * (3 + tieParameter) := by
  have hfirst : 0 < 1 - tieParameter := by linarith
  have hsecond : 0 < 3 + tieParameter := by linarith
  exact mul_pos hfirst hsecond

/-- **The floor**: the rate never drops below `1/3` anywhere on the stratum. -/
theorem collarFloorRate_ge_third {tieParameter : ℝ} (hnonneg : 0 ≤ tieParameter)
    (hlt : tieParameter < 1) :
    (1 : ℝ) / 3 ≤ collarFloorRate tieParameter := by
  have hden := collarDenominator_pos hnonneg hlt
  rw [collarFloorRate, le_div_iff₀ hden]
  nlinarith [hnonneg]

/-- The floor is attained exactly at the tie boundary. -/
theorem collarFloorRate_zero : collarFloorRate 0 = 1 / 3 := by
  rw [collarFloorRate]
  norm_num

/-- **Strict monotonicity**: the cross-multiplied difference factors as
`(T₂ − T₁)(5 + T₁ + T₂ + T₁T₂)`, positive throughout. So `1/3` really is the
infimum and it is approached only at the boundary. -/
theorem collarFloorRate_lt_of_lt {firstTie secondTie : ℝ}
    (hnonneg : 0 ≤ firstTie) (horder : firstTie < secondTie)
    (hlt : secondTie < 1) :
    collarFloorRate firstTie < collarFloorRate secondTie := by
  have hsecondNonneg : 0 ≤ secondTie := le_of_lt (lt_of_le_of_lt hnonneg horder)
  have hfirstLt : firstTie < 1 := lt_trans horder hlt
  have hdenFirst := collarDenominator_pos hnonneg hfirstLt
  have hdenSecond := collarDenominator_pos hsecondNonneg hlt
  rw [collarFloorRate, collarFloorRate, div_lt_div_iff₀ hdenFirst hdenSecond]
  nlinarith [horder, hnonneg, hsecondNonneg, hfirstLt, hlt,
    mul_nonneg hnonneg hsecondNonneg]

/-! ### The off-window gate -/

/-- The gate constant assembled from the ball's two perturbation defects. -/
noncomputable def offWindowGate (ballDefect capDrift : ℝ) : ℝ :=
  ballDefect / (4 * (3 - ballDefect)) + (3 / 4) * capDrift

/-- **The gate identity**: the cap-plus-one collapses to the gate excess scaled
by `(4/3)(3−δ)`. Everything downstream is a sign reading of this line. -/
theorem offWindowGate_identity {ballDefect capDrift conicValue : ℝ}
    (hballLt : ballDefect < 3) :
    (3 - ballDefect) * (-(1 / 3) + (4 / 3) * conicValue + capDrift) + 1
      = -((4 / 3) * (3 - ballDefect)
          * (-conicValue - offWindowGate ballDefect capDrift)) := by
  have hne : (3 : ℝ) - ballDefect ≠ 0 := by
    intro hzero
    exact absurd hzero (ne_of_gt (by linarith))
  rw [offWindowGate]
  field_simp
  ring

/-- **Theorem OW, the fire**: off the window the cap value drops below `−1`,
with the explicit margin `(4/3)(3−δ)((−G) − G₀)`. No weight enters the chain,
so the conclusion holds for every extra weight — the off-window half of the
collar is discharged uniformly. -/
theorem offWindow_cap_fires {ballDefect capDrift conicValue capValue : ℝ}
    (hballNonneg : 0 ≤ ballDefect) (hballLt : ballDefect < 3)
    (hcapBound : capValue
      ≤ (3 - ballDefect) * (-(1 / 3) + (4 / 3) * conicValue + capDrift))
    (hoffWindow : offWindowGate ballDefect capDrift ≤ -conicValue) :
    capValue ≤ -1 - (4 / 3) * (3 - ballDefect)
        * (-conicValue - offWindowGate ballDefect capDrift)
      ∧ capValue ≤ -1 := by
  have hidentity := offWindowGate_identity (capDrift := capDrift)
    (conicValue := conicValue) hballLt
  have hmarginNonneg : 0 ≤ (4 / 3) * (3 - ballDefect)
      * (-conicValue - offWindowGate ballDefect capDrift) := by
    have hscale : (0 : ℝ) < (4 / 3) * (3 - ballDefect) := by linarith
    have hexcess : (0 : ℝ) ≤ -conicValue - offWindowGate ballDefect capDrift := by
      linarith
    exact mul_nonneg hscale.le hexcess
  exact ⟨by linarith, by linarith⟩

/-! ### The gate constant at the working radius -/

/-- The perturbation defect of the ball of radius `ε`. -/
noncomputable def ballPerturbation (ballRadius : ℝ) : ℝ :=
  2 * Real.sqrt 3 * ballRadius + ballRadius ^ 2

/-- A working numerical bound for `√3`. -/
theorem sqrt_three_lt : Real.sqrt 3 < (17320509 : ℝ) / 10 ^ 7 := by
  rw [show ((17320509 : ℝ) / 10 ^ 7)
      = Real.sqrt (((17320509 : ℝ) / 10 ^ 7) ^ 2) from
    (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **The radius is not decorative**: at `ε = 1/400` the gate constant is
strictly below `1/50`, the level the real quantitative Cauchy–Schwarz bound
guarantees off the window. So the off-window fire at that radius is strict. -/
theorem offWindowGate_lt_fifty_at_working_radius :
    offWindowGate (4 * ballPerturbation ((1 : ℝ) / 400))
        (2 * ballPerturbation ((1 : ℝ) / 400)
          / (1 - 2 * ballPerturbation ((1 : ℝ) / 400)))
      < 1 / 50 := by
  have hsqrt := sqrt_three_lt
  have hsqrtPos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  set perturbation := ballPerturbation ((1 : ℝ) / 400) with hperturbation
  have hperturbationEq : perturbation
      = 2 * Real.sqrt 3 * ((1 : ℝ) / 400) + ((1 : ℝ) / 400) ^ 2 := by
    rw [hperturbation, ballPerturbation]
  have hupper : perturbation < (867 : ℝ) / 100000 := by
    rw [hperturbationEq]
    nlinarith [hsqrt]
  have hlower : (0 : ℝ) < perturbation := by
    rw [hperturbationEq]
    nlinarith [hsqrtPos]
  have hdriftDen : (0 : ℝ) < 1 - 2 * perturbation := by linarith
  have hbigDen : (0 : ℝ) < 4 * (3 - 4 * perturbation) := by linarith
  rw [offWindowGate]
  have hdriftBound : 2 * perturbation / (1 - 2 * perturbation)
      < (1770 : ℝ) / 100000 := by
    rw [div_lt_iff₀ hdriftDen]
    nlinarith [hupper, hlower]
  have hfirstBound : 4 * perturbation / (4 * (3 - 4 * perturbation))
      < (300 : ℝ) / 100000 := by
    rw [div_lt_iff₀ hbigDen]
    nlinarith [hupper, hlower]
  linarith

end Gtz
