/-
# The statement-(2) interface: the vacuous pair and the repaired one

The composed interface of statement (2) is the campaign's most defect-prone
object: the pair `(τ₀, ε₀′)` recorded for two sessions turned out to compose
to the EMPTY set (diary §73, GAP V-1), because a tied point with extra-weight
`τ` sits at corner distance `√(3/2)·τ`, so demanding `τ ≥ τ₀` and
`distance ≤ ε₀′` is contradictory unless `ε₀′ ≥ √(3/2)·τ₀`.

Both facts are mechanized here, so the trap cannot recur silently:

* `oldInterfacePair_vacuous` — for the recorded `(τ₀, ε₀) = (10⁻², 1/400)`
  the tube and the ball do not meet: EVERY tied point with `τ ≥ 10⁻²` lies
  strictly outside the ball. (The composed `ε₀′ ≤ 1.4·10⁻⁵` is smaller still,
  so it is vacuous a fortiori.)
* `ballTauCeiling` — the exact ceiling: only `τ ≲ 2.05·10⁻³` can be in-ball.
* `newInterfacePair_nonempty` — the repaired pair `(10⁻¹², 1.95·10⁻¹²)` from
  the `√τ₀` law DOES meet: an explicit witness `τ = 1.59·10⁻¹²` satisfies both
  constraints.
* `interfaceFormula_rounds_down` — the quoted `ε₀′* = 1.95·10⁻¹²` is a
  round-DOWN of the formula value `2.76·10⁻⁶·√(τ₀·min(σ,1−σ))`, i.e. the
  conservative direction (a round-UP would have been unsound).

`cornerDistanceRate` is the `√(3/2)` per-atom constant of the R1 distance law.
-/
import Mathlib

namespace Gtz

/-- The per-atom corner-distance rate of the R1 law: `distance = √(3/2)·τ`. -/
noncomputable def cornerDistanceRate : ℝ := Real.sqrt (3/2)

theorem cornerDistanceRate_lower : (12247 : ℝ)/10000 < cornerDistanceRate := by
  rw [cornerDistanceRate, show ((12247 : ℝ)/10000)
    = Real.sqrt (((12247 : ℝ)/10000) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)

theorem cornerDistanceRate_upper : cornerDistanceRate < (12248 : ℝ)/10000 := by
  rw [cornerDistanceRate, show ((12248 : ℝ)/10000)
    = Real.sqrt (((12248 : ℝ)/10000) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **The recorded interface pair is vacuous** (diary §73, GAP V-1): every
tied point carrying extra-weight `τ ≥ 10⁻²` sits strictly outside the
`ε₀ = 1/400` corner ball, so `tube(10⁻²) ∩ ball = ∅` and statement (2)'s
in-ball coverage rests entirely on the collar. -/
theorem oldInterfacePair_vacuous (tieWeight : ℝ)
    (hfloor : (1 : ℝ)/100 ≤ tieWeight) :
    (1 : ℝ)/400 < cornerDistanceRate * tieWeight := by
  have hrate := cornerDistanceRate_lower
  nlinarith [hrate, hfloor]

/-- The exact ceiling the ball imposes on the extra weight: in-ball tied
points have `τ < 2.05·10⁻³`. Any `τ₀` above this makes the pairing vacuous. -/
theorem ballTauCeiling (tieWeight : ℝ) (hnonneg : 0 ≤ tieWeight)
    (hinBall : cornerDistanceRate * tieWeight ≤ (1 : ℝ)/400) :
    tieWeight < (205 : ℝ)/100000 := by
  have hrate := cornerDistanceRate_lower
  nlinarith [hrate, hinBall, hnonneg]

/-- **The repaired pair is nonvacuous**: with `τ₀* = 10⁻¹²` and
`ε₀′* = 1.95·10⁻¹²` from the `√τ₀` law, there are tied points satisfying BOTH
constraints — an explicit witness at `τ = 1.59·10⁻¹²`. -/
theorem newInterfacePair_nonempty :
    ∃ tieWeight : ℝ, (1 : ℝ)/10^12 ≤ tieWeight
      ∧ cornerDistanceRate * tieWeight ≤ (195 : ℝ)/10^14 := by
  refine ⟨(159 : ℝ)/10^14, by norm_num, ?_⟩
  have hrate := cornerDistanceRate_upper
  nlinarith [hrate, cornerDistanceRate_lower]

/-- **The quoted interface constant rounds DOWN** (the conservative
direction): the `√τ₀` formula `2.76·10⁻⁶·√(τ₀·min(σ,1−σ))` evaluated at
`τ₀ = 10⁻¹²`, `σ = 1/2` exceeds the quoted `1.95·10⁻¹²`, so using the quoted
value shrinks the ball and keeps the pairing sound. -/
theorem interfaceFormula_rounds_down :
    (195 : ℝ)/10^14
      ≤ (276 : ℝ)/10^8 * Real.sqrt ((1 : ℝ)/10^12 * (1/2)) := by
  have hsqrtLower : (7071 : ℝ)/10^10 < Real.sqrt ((1 : ℝ)/10^12 * (1/2)) := by
    rw [show ((7071 : ℝ)/10^10)
      = Real.sqrt (((7071 : ℝ)/10^10) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  nlinarith [hsqrtLower]

/-- The pairing law itself: a pair `(τ₀, ε₀′)` is nonvacuous exactly when the
ball radius clears the tube's own distance floor. This is the one-line test
whose omission produced the §73 defect. -/
theorem interfacePair_nonvacuous_iff (tauFloor ballRadius : ℝ)
    (hfloorPos : 0 < tauFloor) :
    (∃ tieWeight : ℝ, tauFloor ≤ tieWeight
        ∧ cornerDistanceRate * tieWeight ≤ ballRadius)
      ↔ cornerDistanceRate * tauFloor ≤ ballRadius := by
  constructor
  · rintro ⟨tieWeight, hge, hle⟩
    have hratePos : 0 < cornerDistanceRate := by
      have := cornerDistanceRate_lower; linarith
    nlinarith [hge, hle, hratePos]
  · intro hclears
    exact ⟨tauFloor, le_refl _, hclears⟩


/-! ### The C₂ assembly and the off-window margin -/

/-- **The C₂ assembly** (SS50 defect B, assembled for the first time by the
subgapv build): `C₂ = H_max/(2·ĉ₁)` with the audited `H_max ≤ 2.5·10³` and the
rescaled transverse fire rate `ĉ₁ ≥ 2.7·10⁻³` gives `C₂ ≤ 4.7·10⁵`. Mechanized
as the composition it is, so the inputs' provenance is visible at the use
site. -/
theorem c2_assembly (curvatureBound fireRate : ℝ)
    (hcurvature : curvatureBound ≤ 25 * 10^2)
    (hfireRate : (27 : ℝ)/10^4 ≤ fireRate) (hfirePos : 0 < fireRate) :
    curvatureBound / (2 * fireRate) ≤ 47 * 10^4 := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith [hcurvature, hfireRate, hfirePos]

/-- **The off-window margin is positive exactly on the off-window condition**
(Theorem OW's shape): the assembled cap-fire margin
`(4/3)(3−δ)(min((4/9)sinθ, 1/50) − G₀)` is strictly positive iff the window
gate `G₀ < min((4/9)sinθ, 1/50)` holds — the τ-free criterion. -/
theorem offWindow_margin_pos (sinAngle windowGate slackDefect : ℝ)
    (hslack : slackDefect < 3) (hgate : windowGate < min ((4/9) * sinAngle) (1/50)) :
    0 < (4/3) * (3 - slackDefect)
      * (min ((4/9) * sinAngle) (1/50) - windowGate) := by
  have hpos : 0 < min ((4/9) * sinAngle) (1/50) - windowGate := by linarith
  have hfactor : 0 < (4/3) * (3 - slackDefect) := by linarith
  exact mul_pos hfactor hpos

/-- The acid-test instance: at the recorded in-ball complex witnesses the
extras sit off-window (`sin θ ≈ 0.60`), so the window gate is the binding
`1/50` branch and the real-side margin is positive — the exclusion happens on
the real side, exactly as the field-discipline gate demands. -/
theorem acidTest_margin_pos (slackDefect : ℝ) (hslack : slackDefect < 3) :
    0 < (4/3) * (3 - slackDefect)
      * (min ((4/9) * ((6039 : ℝ)/10000)) (1/50) - (1616 : ℝ)/10^5) := by
  refine offWindow_margin_pos _ _ _ hslack ?_
  rw [min_eq_right (by norm_num)]
  norm_num

end Gtz
