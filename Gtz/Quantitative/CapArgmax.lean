/-
# The cap-boundary argmax: the corrected H1b, decided in both directions

Residual 8's H1b leg asked whether the two-at-cap corner constant
`C_B(L) = 4(L−1)(2L³ − L² − 8L + 8)/(2L−3)²` bounds the X-channel rate of every
admissible probe atom.  `Gtz/Quantitative/CapBoundaryConstant.lean` proves `C_B`
is strictly monotone; the argmax itself stayed open.  This file settles it
EXACTLY, and the answer is a threshold, not a yes:

  the corner dominates precisely on `2 < L ≤ 4 + 2√2`, and FAILS at every
  `L > 4 + 2√2`.

## The objects

Fix the two-at-cap design at cap `L > 2`: cap atoms `S_A = (L−1, u)` and
`S_B = (L−1, −u)` with `u² = 2L−1` (so `|S_A| = |S_B| = L`), light atom
`S_C = (−ℓ_C, 0)` with `ℓ_C = (2L−2)/(2L−3)`, weights `w_A = w_B = 1/(2L−1)`,
`w_C = (2L−3)/(2L−1)`, stress covector `ξ = ((L−2)/(2L−2), 0)`.
`twoAtCap_design_valid` checks the planar design equations for this system.

For a probe atom `X = (x, y)` of radius `ρ = |X|`, `M_c(X)` is the repo's
`pairEntry` at level 1 with shifted leverages `ℓ_c − 2` — the obstruction entry
of the pair `(c, X)`.  The channel numerator and defect are

  `H(X) = Σ_c w_c · M_c(X) · |S_c − X|²`,     `d(X) = 1 + ⟨ξ, X⟩ − ρ/2`.

`H` is even in `y` and even in `u`, so after `y² = ρ² − x²` and `u² = 2L−1` it
becomes a rational function of `(x, ρ)` alone: that is `capChannelNumerator`,
and `capChannelNumerator_eq_pairEntrySum` proves the identification against
`pairEntry` itself (stated scaled by `2L−1`, which turns the weight triple into
the integer profile `1, 1, 2L−3`).  Likewise `M_A + M_B = 2·capSilenceSum` and
`M_A · M_B = capSilenceProduct` (`capSilence_sum_and_product`), so the silence
constraints `M_A ≥ 0`, `M_B ≥ 0` are visible in `(x, ρ)` coordinates.

## The certificate

`capArgmaxGap L x ρ := C_B(L)·d − H` is the corner advantage.  Everything rests
on ONE exact polynomial identity, `capArgmaxGap_certificate`:

  `2(L−1)(2L−3) · Gap  =  −4(L−1)²(L² − 8L + 8) · d²  +  (L−2)² · (M_A·M_B)`.

Both multipliers are CONSTANTS.  There is no Positivstellensatz hierarchy, no
stationary-point enumeration, no face census: positivity is read off the two
signs, and the threshold is the larger root of `L² − 8L + 8`, namely `4 + 2√2`.
The identity was verified independently in sympy (symbolic residual 0) and in
python-flint (4000 exact rational configurations rebuilt from `⟨S_c, X⟩`
directly, residual exactly 0).

## How this DIFFERS from the display — stated plainly, not smuggled

The display used `C_B(ℓ̄)` as a global constant.  `Gtz/Planar/LawCounterexample.lean`
already refuted that at cap 10 with one design.  This file is SHARPER in one
direction and deliberately WEAKER in the other:

* SHARPER — the failure is not an artifact of a single design or a single cap.
  For EVERY `L > 4 + 2√2` an explicit admissible probe beats the corner
  (`capArgmax_fails_above_threshold`); on that face the certificate gives the
  excess in closed form as `2(L−1)(L²−8L+8)·d²/(2L−3)`, and `capRefuter_defect`
  supplies the defect `d = 6(L−3)(2L−1)/((2L−3)(L²+6L−3))` exactly.
* WEAKER — the positive statement is proved only on `2 < L ≤ 4 + 2√2`
  (`capArgmax_corner_dominates_below_threshold`), NOT on all of `L ≥ 2` as
  displayed.  That restriction is not a proof convenience: beyond `4 + 2√2` the
  displayed statement is FALSE, by the theorem named just above.

## Scope — what is NOT claimed

`capChannelNumerator` and `capChannelDefect` are the channel numerator and
defect of the two-at-cap ATOM SYSTEM.  Nothing here asserts that `sup H/d` is
the GAP-S first-order constant of a `WeightedDesign`, nor that any design's
budget realizes it.  The leash that would connect the two
(`Gtz/Quantitative/FirstOrderLaw.lean`, `budget_le_max_of_leash`) is stated
abstractly over an arbitrary index type and is NOT consumed here.  So
`capArgmax_fails_above_threshold` refutes the CHANNEL-level argmax — a statement
about probe atoms — and does not by itself refute or reprove any design-level
law.  The FAMILY-level argmax (that the two-at-cap point beats other family
points) is a different claim, and is untouched by this file.
-/
import Mathlib
import Gtz.Quantitative.CapBoundaryConstant
import Gtz.Planar.PlanarPlatform

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ### The channel objects in `(x, ρ)` coordinates -/

/-- The channel **defect** `d(X) = 1 + ⟨ξ, X⟩ − ρ/2` of a probe atom of abscissa
`x` and radius `ρ`, against the two-at-cap stress `ξ = ((L−2)/(2L−2), 0)`. -/
noncomputable def capChannelDefect (leverage xcoord radius : ℝ) : ℝ :=
  1 + (leverage - 2) / (2 * leverage - 2) * xcoord - radius / 2

/-- Half the sum of the two cap-atom obstruction entries: `M_A + M_B = 2·P`.
The `u`-terms cancel, so this is rational in `(x, ρ)`. -/
noncomputable def capSilenceSum (leverage xcoord radius : ℝ) : ℝ :=
  (leverage - 1) * xcoord - (leverage - 2) * (radius - 2) + 2

/-- The product of the two cap-atom obstruction entries,
`M_A · M_B = P² − (2L−1)·y²` with `y² = ρ² − x²`.  Together with `P ≥ 0`, its
nonnegativity is exactly the pair of silence constraints `M_A ≥ 0`, `M_B ≥ 0`. -/
noncomputable def capSilenceProduct (leverage xcoord radius : ℝ) : ℝ :=
  capSilenceSum leverage xcoord radius ^ 2
    - (2 * leverage - 1) * (radius ^ 2 - xcoord ^ 2)

/-- The channel **numerator** `H(X) = Σ_c w_c M_c(X) |S_c − X|²`, reduced to a
rational function of `(x, ρ)`.  Quadratic in `x`, leading coefficient
`−4(L−2)²/(2L−3) < 0`. -/
noncomputable def capChannelNumerator (leverage xcoord radius : ℝ) : ℝ :=
  (-4 * (leverage - 2) ^ 2 / (2 * leverage - 3)) * xcoord ^ 2
    + (2 * (leverage - 2) * (leverage - 1)
        * (2 * leverage ^ 2 + 4 * leverage * radius - 9 * leverage - 6 * radius + 10)
        / (2 * leverage - 3) ^ 2) * xcoord
    - 2 * (2 * leverage ^ 4 * radius - 4 * leverage ^ 4 - 9 * leverage ^ 3 * radius
        + 14 * leverage ^ 3 + 4 * leverage ^ 2 * radius ^ 2 + 10 * leverage ^ 2 * radius
        - 14 * leverage ^ 2 - 12 * leverage * radius ^ 2 + 4 * leverage * radius
        + 9 * radius ^ 2 - 8 * radius + 4) / (2 * leverage - 3) ^ 2

/-- `capChannelNumerator` as a single fraction over `(2L−3)²`.  Used to keep
`field_simp` from re-deriving the squared denominator as an opaque atom.

Stated without a pole hypothesis: at `2L − 3 = 0` both sides collapse to the
same junk value under Lean's `x / 0 = 0` convention, so the identity is
unconditional.  A reader who wants the nonzero-denominator reading must
supply it separately. -/
theorem capChannelNumerator_eq_div {leverage xcoord radius : ℝ} :
    capChannelNumerator leverage xcoord radius
      = (-4 * (leverage - 2) ^ 2 * (2 * leverage - 3) * xcoord ^ 2
          + 2 * (leverage - 2) * (leverage - 1)
            * (2 * leverage ^ 2 + 4 * leverage * radius - 9 * leverage - 6 * radius + 10)
            * xcoord
          - 2 * (2 * leverage ^ 4 * radius - 4 * leverage ^ 4 - 9 * leverage ^ 3 * radius
              + 14 * leverage ^ 3 + 4 * leverage ^ 2 * radius ^ 2
              + 10 * leverage ^ 2 * radius - 14 * leverage ^ 2 - 12 * leverage * radius ^ 2
              + 4 * leverage * radius + 9 * radius ^ 2 - 8 * radius + 4))
        / (2 * leverage - 3) ^ 2 := by
  rcases eq_or_ne (2 * leverage - 3) 0 with hzero | h3
  · unfold capChannelNumerator
    rw [hzero]
    norm_num
  · unfold capChannelNumerator
    field_simp

/-- **The corner advantage** `C_B(L)·d(X) − H(X)`: nonnegative exactly when the
probe `X` does not beat the corner rate `C_B(L)`. -/
noncomputable def capArgmaxGap (leverage xcoord radius : ℝ) : ℝ :=
  capBoundaryConstant leverage * capChannelDefect leverage xcoord radius
    - capChannelNumerator leverage xcoord radius

/-! ### The certificate -/

/-- **THE CERTIFICATE** — one exact polynomial identity with constant multipliers:

`2(L−1)(2L−3)·Gap = −4(L−1)²(L²−8L+8)·d² + (L−2)²·(M_A·M_B)`.

Every sign statement in this file is a reading of this one line. -/
theorem capArgmaxGap_certificate {leverage xcoord radius : ℝ}
    (hlev : 2 < leverage) :
    2 * (leverage - 1) * (2 * leverage - 3) * capArgmaxGap leverage xcoord radius
      = -4 * (leverage - 1) ^ 2 * (leverage ^ 2 - 8 * leverage + 8)
          * capChannelDefect leverage xcoord radius ^ 2
        + (leverage - 2) ^ 2 * capSilenceProduct leverage xcoord radius := by
  have hone : (leverage - 1) ≠ 0 := by intro h; nlinarith
  have h2 : (2 * leverage - 2) ≠ 0 := by intro h; nlinarith
  have h3 : (2 * leverage - 3) ≠ 0 := by intro h; nlinarith
  unfold capArgmaxGap capChannelDefect capChannelNumerator capSilenceProduct
    capSilenceSum capBoundaryConstant
  field_simp
  ring

/-! ### The positive half: the corner dominates below the threshold -/

/-- **Corner dominance, algebraic form.**  If the probe is silent for the two cap
atoms (`M_A·M_B ≥ 0`) and `L² − 8L + 8 ≤ 0`, the corner advantage is nonnegative.

Only TWO facts are consumed — the sign of `L² − 8L + 8` and silence.  The cap
`ρ ≤ L`, the essentiality `ρ ≥ 1`, the light-atom silence `M_C ≥ 0` and the
positivity of the defect are all unnecessary, which is why the conclusion is so
much stronger than a numerical scan over the admissible region. -/
theorem capArgmax_corner_dominates {leverage xcoord radius : ℝ}
    (hlev : 2 < leverage)
    (hthreshold : leverage ^ 2 - 8 * leverage + 8 ≤ 0)
    (hsilent : 0 ≤ capSilenceProduct leverage xcoord radius) :
    0 ≤ capArgmaxGap leverage xcoord radius := by
  have hscale : (0 : ℝ) < 2 * (leverage - 1) * (2 * leverage - 3) := by nlinarith
  have hkey := capArgmaxGap_certificate (xcoord := xcoord) (radius := radius) hlev
  have hsq : (0 : ℝ) ≤ (leverage - 1) ^ 2
      * capChannelDefect leverage xcoord radius ^ 2 := by positivity
  have hfirst : 0 ≤ -4 * (leverage - 1) ^ 2 * (leverage ^ 2 - 8 * leverage + 8)
      * capChannelDefect leverage xcoord radius ^ 2 := by
    nlinarith [hsq, hthreshold]
  have hsecond : 0 ≤ (leverage - 2) ^ 2 * capSilenceProduct leverage xcoord radius :=
    mul_nonneg (sq_nonneg _) hsilent
  nlinarith [hkey, hfirst, hsecond, hscale]

/-- The threshold `L² − 8L + 8 ≤ 0` is exactly `L ≤ 4 + 2√2` on `L ≥ 2`
(the other root `4 − 2√2 < 2` is out of range). -/
theorem capArgmax_threshold_iff {leverage : ℝ} (hlev : 2 ≤ leverage) :
    leverage ^ 2 - 8 * leverage + 8 ≤ 0 ↔ leverage ≤ 4 + 2 * Real.sqrt 2 := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : (1 : ℝ) < Real.sqrt 2 := by
    have hmono : Real.sqrt 1 < Real.sqrt 2 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using hmono
  have hlt : Real.sqrt 2 < 3 / 2 := by nlinarith [hsq, Real.sqrt_nonneg 2]
  constructor
  · intro hle
    nlinarith [hsq, hpos, hle]
  · intro hle
    nlinarith [hsq, hpos, hlt, hle]

/-- **The corrected H1b, positive half.**  For `2 < L ≤ 4 + 2√2`, every probe
silent against the two cap atoms satisfies `H(X) ≤ C_B(L)·d(X)`: the two-at-cap
corner rate dominates.  This is the display's claim restricted to the range
where it is TRUE — beyond `4 + 2√2` it is false, see
`capArgmax_fails_above_threshold`. -/
theorem capArgmax_corner_dominates_below_threshold {leverage xcoord radius : ℝ}
    (hlev : 2 < leverage) (hcap : leverage ≤ 4 + 2 * Real.sqrt 2)
    (hsilent : 0 ≤ capSilenceProduct leverage xcoord radius) :
    capChannelNumerator leverage xcoord radius
      ≤ capBoundaryConstant leverage * capChannelDefect leverage xcoord radius := by
  have hthreshold : leverage ^ 2 - 8 * leverage + 8 ≤ 0 :=
    (capArgmax_threshold_iff hlev.le).mpr hcap
  have hgap := capArgmax_corner_dominates hlev hthreshold hsilent
  unfold capArgmaxGap at hgap
  linarith

/-! ### Sharpness: the corner attains the bound -/

/-- The corner advantage VANISHES at the light atom `S_C = (−ℓ_C, 0)`, whose
radius is `ℓ_C`.  So the bound of `capArgmax_corner_dominates_below_threshold`
is attained and `C_B(L)` cannot be lowered. -/
theorem capArgmaxGap_at_lightAtom {leverage : ℝ} (hlev : 2 < leverage) :
    capArgmaxGap leverage (-((2 * leverage - 2) / (2 * leverage - 3)))
      ((2 * leverage - 2) / (2 * leverage - 3)) = 0 := by
  have hone : (leverage - 1) ≠ 0 := by intro h; nlinarith
  have h2 : (2 * leverage - 2) ≠ 0 := by intro h; nlinarith
  have h3 : (2 * leverage - 3) ≠ 0 := by intro h; nlinarith
  unfold capArgmaxGap capChannelDefect capChannelNumerator capBoundaryConstant
  set shifted := 2 * leverage - 3 with hshift
  have hs : shifted ≠ 0 := by rw [hshift]; exact h3
  field_simp
  rw [hshift]
  ring

/-- The corner advantage also vanishes at a cap atom (abscissa `L−1`, radius `L`). -/
theorem capArgmaxGap_at_capAtom {leverage : ℝ} (hlev : 2 < leverage) :
    capArgmaxGap leverage (leverage - 1) leverage = 0 := by
  have hone : (leverage - 1) ≠ 0 := by intro h; nlinarith
  have h2 : (2 * leverage - 2) ≠ 0 := by intro h; nlinarith
  have h3 : (2 * leverage - 3) ≠ 0 := by intro h; nlinarith
  unfold capArgmaxGap capChannelDefect capChannelNumerator capBoundaryConstant
  field_simp
  ring

/-! ### The negative half: the corner FAILS above the threshold -/

/-- **Abstract refutation.**  On the silence face `M_A · M_B = 0` the certificate
collapses to `2(L−1)(2L−3)·Gap = −4(L−1)²(L²−8L+8)·d²`, so beyond the threshold
any face probe with nonzero defect strictly beats the corner. -/
theorem capArgmax_face_refutation {leverage xcoord radius : ℝ}
    (hlev : 2 < leverage)
    (habove : 0 < leverage ^ 2 - 8 * leverage + 8)
    (hface : capSilenceProduct leverage xcoord radius = 0)
    (hdefect : capChannelDefect leverage xcoord radius ≠ 0) :
    capArgmaxGap leverage xcoord radius < 0 := by
  have hscale : (0 : ℝ) < 2 * (leverage - 1) * (2 * leverage - 3) := by nlinarith
  have hkey := capArgmaxGap_certificate (xcoord := xcoord) (radius := radius) hlev
  rw [hface] at hkey
  have hsqpos : 0 < capChannelDefect leverage xcoord radius ^ 2 :=
    pow_pos (abs_pos.mpr hdefect) 2 |>.trans_le (by rw [sq_abs])
  have hone : (0 : ℝ) < (leverage - 1) ^ 2 :=
    pow_pos (by linarith : (0 : ℝ) < leverage - 1) 2
  nlinarith [hkey, hsqpos, hscale, habove, hone,
    mul_pos (mul_pos hone habove) hsqpos]

/-- The abscissa of the explicit refuting probe — the `p = 2` point of the pencil
of lines through the light atom, which lies on the silence face `M_A = 0`. -/
noncomputable def capRefuterAbscissa (leverage : ℝ) : ℝ :=
  -2 * (leverage - 1) * (leverage ^ 2 - 18 * leverage + 9)
    / ((2 * leverage - 3) * (leverage ^ 2 + 6 * leverage - 3))

/-- The radius of the explicit refuting probe. -/
noncomputable def capRefuterRadius (leverage : ℝ) : ℝ :=
  2 * (leverage - 1) * (leverage ^ 2 + 18 * leverage - 9)
    / ((2 * leverage - 3) * (leverage ^ 2 + 6 * leverage - 3))

/-- The refuting probe lies exactly ON the silence face: `M_A · M_B = 0`. -/
theorem capRefuter_onFace {leverage : ℝ} (hlev : 3 < leverage) :
    capSilenceProduct leverage (capRefuterAbscissa leverage)
      (capRefuterRadius leverage) = 0 := by
  have h3 : (2 * leverage - 3) ≠ 0 := by intro h; nlinarith
  have hq : (leverage ^ 2 + 6 * leverage - 3) ≠ 0 := by intro h; nlinarith
  unfold capSilenceProduct capSilenceSum capRefuterAbscissa capRefuterRadius
  set carrier := (2 * leverage - 3) * (leverage ^ 2 + 6 * leverage - 3) with hcar
  have hc : carrier ≠ 0 := by rw [hcar]; exact mul_ne_zero h3 hq
  field_simp
  rw [hcar]
  ring

/-- The refuting probe's remaining cap-atom entry, in closed form. -/
theorem capRefuter_silenceSum {leverage : ℝ} (hlev : 3 < leverage) :
    capSilenceSum leverage (capRefuterAbscissa leverage) (capRefuterRadius leverage)
      = 12 * leverage * (leverage - 1) * (2 * leverage - 1)
        / ((2 * leverage - 3) * (leverage ^ 2 + 6 * leverage - 3)) := by
  have h3 : (2 * leverage - 3) ≠ 0 := by intro h; nlinarith
  have hq : (leverage ^ 2 + 6 * leverage - 3) ≠ 0 := by intro h; nlinarith
  unfold capSilenceSum capRefuterAbscissa capRefuterRadius
  set carrier := (2 * leverage - 3) * (leverage ^ 2 + 6 * leverage - 3) with hcar
  have hc : carrier ≠ 0 := by rw [hcar]; exact mul_ne_zero h3 hq
  field_simp
  rw [hcar]
  ring

/-- The refuting probe's defect, in closed form — positive for `L > 3`. -/
theorem capRefuter_defect {leverage : ℝ} (hlev : 3 < leverage) :
    capChannelDefect leverage (capRefuterAbscissa leverage) (capRefuterRadius leverage)
      = 6 * (leverage - 3) * (2 * leverage - 1)
        / ((2 * leverage - 3) * (leverage ^ 2 + 6 * leverage - 3)) := by
  have hone : (leverage - 1) ≠ 0 := by intro h; nlinarith
  have h2 : (2 * leverage - 2) ≠ 0 := by intro h; nlinarith
  have h3 : (2 * leverage - 3) ≠ 0 := by intro h; nlinarith
  have hq : (leverage ^ 2 + 6 * leverage - 3) ≠ 0 := by intro h; nlinarith
  unfold capChannelDefect capRefuterAbscissa capRefuterRadius
  set carrier := (2 * leverage - 3) * (leverage ^ 2 + 6 * leverage - 3) with hcar
  have hc : carrier ≠ 0 := by rw [hcar]; exact mul_ne_zero h3 hq
  field_simp
  rw [hcar]
  ring

/-- The refuting probe's radius exceeds 1 — by a perfect square over the
positive carrier, so the probe is `τ`-essential. -/
theorem capRefuter_radiusLower {leverage : ℝ} (hlev : 3 < leverage) :
    capRefuterRadius leverage - 1
      = (5 * leverage - 3) ^ 2
        / ((2 * leverage - 3) * (leverage ^ 2 + 6 * leverage - 3)) := by
  have h3 : (2 * leverage - 3) ≠ 0 := by intro h; nlinarith
  have hq : (leverage ^ 2 + 6 * leverage - 3) ≠ 0 := by intro h; nlinarith
  unfold capRefuterRadius
  set carrier := (2 * leverage - 3) * (leverage ^ 2 + 6 * leverage - 3) with hcar
  have hc : carrier ≠ 0 := by rw [hcar]; exact mul_ne_zero h3 hq
  field_simp
  rw [hcar]
  ring

/-- The refuting probe respects the leverage cap. -/
theorem capRefuter_radiusUpper {leverage : ℝ} (hlev : 3 < leverage) :
    leverage - capRefuterRadius leverage
      = (leverage - 3) * (2 * leverage - 1) * (leverage ^ 2 + 7 * leverage - 6)
        / ((2 * leverage - 3) * (leverage ^ 2 + 6 * leverage - 3)) := by
  have h3 : (2 * leverage - 3) ≠ 0 := by intro h; nlinarith
  have hq : (leverage ^ 2 + 6 * leverage - 3) ≠ 0 := by intro h; nlinarith
  unfold capRefuterRadius
  set carrier := (2 * leverage - 3) * (leverage ^ 2 + 6 * leverage - 3) with hcar
  have hc : carrier ≠ 0 := by rw [hcar]; exact mul_ne_zero h3 hq
  field_simp
  rw [hcar]
  ring

/-- The implied `y² = ρ² − x²` of the refuting probe is strictly positive, so the
probe is a genuine planar point off the axis. -/
theorem capRefuter_heightSq {leverage : ℝ} (hlev : 3 < leverage) :
    capRefuterRadius leverage ^ 2 - capRefuterAbscissa leverage ^ 2
      = 144 * leverage ^ 2 * (leverage - 1) ^ 2 * (2 * leverage - 1)
        / ((2 * leverage - 3) * (leverage ^ 2 + 6 * leverage - 3)) ^ 2 := by
  have h3 : (2 * leverage - 3) ≠ 0 := by intro h; nlinarith
  have hq : (leverage ^ 2 + 6 * leverage - 3) ≠ 0 := by intro h; nlinarith
  unfold capRefuterRadius capRefuterAbscissa
  set carrier := (2 * leverage - 3) * (leverage ^ 2 + 6 * leverage - 3) with hcar
  have hc : carrier ≠ 0 := by rw [hcar]; exact mul_ne_zero h3 hq
  field_simp
  ring

/-- **The refuting probe is admissible** for every `L > 3`: the surviving
cap-atom entry is positive, the radius lies strictly inside `[1, L]`, the
implied height squared is positive, and the defect is positive. -/
theorem capRefuter_admissible {leverage : ℝ} (hlev : 3 < leverage) :
    0 < capSilenceSum leverage (capRefuterAbscissa leverage) (capRefuterRadius leverage)
      ∧ 1 < capRefuterRadius leverage
      ∧ capRefuterRadius leverage < leverage
      ∧ 0 < capRefuterRadius leverage ^ 2 - capRefuterAbscissa leverage ^ 2
      ∧ 0 < capChannelDefect leverage (capRefuterAbscissa leverage)
          (capRefuterRadius leverage) := by
  have h3pos : (0 : ℝ) < 2 * leverage - 3 := by linarith
  have hqpos : (0 : ℝ) < leverage ^ 2 + 6 * leverage - 3 := by nlinarith
  have hden : (0 : ℝ) < (2 * leverage - 3) * (leverage ^ 2 + 6 * leverage - 3) :=
    mul_pos h3pos hqpos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [capRefuter_silenceSum hlev]
    apply div_pos _ hden
    nlinarith
  · have hstep : 0 < capRefuterRadius leverage - 1 := by
      rw [capRefuter_radiusLower hlev]
      apply div_pos _ hden
      nlinarith
    linarith
  · have hstep : 0 < leverage - capRefuterRadius leverage := by
      rw [capRefuter_radiusUpper hlev]
      apply div_pos _ hden
      nlinarith
    linarith
  · rw [capRefuter_heightSq hlev]
    refine div_pos ?_ (pow_pos hden 2)
    exact mul_pos (mul_pos (mul_pos (by norm_num)
      (pow_pos (by linarith : (0 : ℝ) < leverage) 2))
      (pow_pos (by linarith : (0 : ℝ) < leverage - 1) 2)) (by linarith)
  · rw [capRefuter_defect hlev]
    apply div_pos _ hden
    nlinarith

/-- **The corrected H1b, negative half.**  For EVERY `L > 4 + 2√2` the explicit
admissible probe `(capRefuterAbscissa L, capRefuterRadius L)` strictly beats the
corner: `C_B(L)·d < H`.  The argmax is not merely unproven above the threshold —
it is FALSE there, at every single cap. -/
theorem capArgmax_fails_above_threshold {leverage : ℝ}
    (hlev : 4 + 2 * Real.sqrt 2 < leverage) :
    capBoundaryConstant leverage
        * capChannelDefect leverage (capRefuterAbscissa leverage)
            (capRefuterRadius leverage)
      < capChannelNumerator leverage (capRefuterAbscissa leverage)
          (capRefuterRadius leverage) := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hgt : (1 : ℝ) < Real.sqrt 2 := by
    have hmono : Real.sqrt 1 < Real.sqrt 2 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using hmono
  have hbig : 3 < leverage := by nlinarith
  have habove : 0 < leverage ^ 2 - 8 * leverage + 8 := by nlinarith [hsq, hgt]
  have hdef := (capRefuter_admissible hbig).2.2.2.2
  have hneg := capArgmax_face_refutation (leverage := leverage)
    (xcoord := capRefuterAbscissa leverage) (radius := capRefuterRadius leverage)
    (by linarith) habove (capRefuter_onFace hbig) (ne_of_gt hdef)
  unfold capArgmaxGap at hneg
  linarith

/-! ### An exact rational adversarial probe at cap 13

`2·13 − 1 = 25` is a perfect square, so the whole geometry is rational at cap 13
and the refutation needs no radicals: the probe `X = (9/5, −12/5)` has radius
`3`, is silent against both cap atoms, sits well inside the cap, and beats the
corner by exactly `63618/13225`. -/

/-- The cap-13 probe is silent against both cap atoms: `M_A + M_B = 2·(63/5)` and
`M_A · M_B = 369/25 > 0`, so in fact `M_A = 3/5` and `M_B = 123/5`. -/
theorem capThirteen_probe_silenceSum : capSilenceSum 13 (9 / 5) 3 = 63 / 5 := by
  unfold capSilenceSum
  norm_num

/-- The cap-13 probe's silence product is strictly positive. -/
theorem capThirteen_probe_silenceProduct : capSilenceProduct 13 (9 / 5) 3 = 369 / 25 := by
  unfold capSilenceProduct capSilenceSum
  norm_num

/-- The cap-13 probe has positive defect `13/40`. -/
theorem capThirteen_probe_defect : capChannelDefect 13 (9 / 5) 3 = 13 / 40 := by
  unfold capChannelDefect
  norm_num

/-- **Kernel-checked refutation at cap 13**: the corner advantage is strictly
negative, `C_B(13)·d − H = −63618/13225`.  With `C_B(13) = 198192/529 ≈ 374.65`,
the probe's channel rate is `H/d = 66957120/171925 ≈ 389.45`. -/
theorem capThirteen_beats_corner : capArgmaxGap 13 (9 / 5) 3 = -(63618 / 13225) := by
  unfold capArgmaxGap capBoundaryConstant capChannelDefect capChannelNumerator
  norm_num

/-- The cap-13 statement in rate form: the corner constant is strictly exceeded
by an interior (not merely boundary) admissible probe. -/
theorem capThirteen_corner_exceeded :
    capBoundaryConstant 13 * capChannelDefect 13 (9 / 5) 3
      < capChannelNumerator 13 (9 / 5) 3 := by
  have hval := capThirteen_beats_corner
  unfold capArgmaxGap at hval
  linarith

/-! ### The bridge to the planar platform

The statements above are only worth as much as the identification of
`capChannelNumerator` and `capSilence*` with the repo's own `pairEntry`, so that
identification is proved here rather than asserted. -/

/-- The three two-at-cap atom squares together with a probe atom, as a
`Fin 4 → Fin 2 → ℝ` planar configuration.  `radial` is `u`, with `u² = 2L−1`. -/
noncomputable def twoAtCapSquares (leverage radial xcoord ycoord : ℝ) :
    Fin 4 → Fin 2 → ℝ :=
  ![![leverage - 1, radial], ![leverage - 1, -radial],
    ![-((2 * leverage - 2) / (2 * leverage - 3)), 0], ![xcoord, ycoord]]

/-- The leverages of the three atoms and of the probe. -/
noncomputable def twoAtCapLeverages (leverage radius : ℝ) : Fin 4 → ℝ :=
  ![leverage, leverage, (2 * leverage - 2) / (2 * leverage - 3), radius]

/-- The obstruction entry `M_c(X)` of atom `index` against the probe: the repo's
`pairEntry` at level 1 with shifted leverages `ℓ − 2`. -/
noncomputable def twoAtCapEntry (leverage radial xcoord ycoord radius : ℝ)
    (index : Fin 4) : ℝ :=
  pairEntry (twoAtCapSquares leverage radial xcoord ycoord)
    (fun other => twoAtCapLeverages leverage radius other - 2) 1 index 3

/-- The squared distance `|S_index − X|²` from an atom to the probe. -/
noncomputable def twoAtCapDistanceSq (leverage radial xcoord ycoord : ℝ)
    (index : Fin 4) : ℝ :=
  ∑ coord : Fin 2, (twoAtCapSquares leverage radial xcoord ycoord index coord
    - twoAtCapSquares leverage radial xcoord ycoord 3 coord) ^ 2

/-- **The two-at-cap system is a valid planar design**: weights positive and
summing to one, exact closure in both coordinates, trace two, and each atom
square's norm equal to its leverage. -/
theorem twoAtCap_design_valid {leverage radial : ℝ} (hlev : 2 < leverage)
    (hradial : radial ^ 2 = 2 * leverage - 1) :
    (0 < 1 / (2 * leverage - 1) ∧ 0 < (2 * leverage - 3) / (2 * leverage - 1))
      ∧ 1 / (2 * leverage - 1) + 1 / (2 * leverage - 1)
          + (2 * leverage - 3) / (2 * leverage - 1) = 1
      ∧ 1 / (2 * leverage - 1) * twoAtCapSquares leverage radial 0 0 0 0
          + 1 / (2 * leverage - 1) * twoAtCapSquares leverage radial 0 0 1 0
          + (2 * leverage - 3) / (2 * leverage - 1)
            * twoAtCapSquares leverage radial 0 0 2 0 = 0
      ∧ 1 / (2 * leverage - 1) * twoAtCapSquares leverage radial 0 0 0 1
          + 1 / (2 * leverage - 1) * twoAtCapSquares leverage radial 0 0 1 1
          + (2 * leverage - 3) / (2 * leverage - 1)
            * twoAtCapSquares leverage radial 0 0 2 1 = 0
      ∧ 1 / (2 * leverage - 1) * twoAtCapLeverages leverage 0 0
          + 1 / (2 * leverage - 1) * twoAtCapLeverages leverage 0 1
          + (2 * leverage - 3) / (2 * leverage - 1) * twoAtCapLeverages leverage 0 2 = 2
      ∧ (∑ coord : Fin 2, twoAtCapSquares leverage radial 0 0 0 coord ^ 2)
          = twoAtCapLeverages leverage 0 0 ^ 2
      ∧ (∑ coord : Fin 2, twoAtCapSquares leverage radial 0 0 1 coord ^ 2)
          = twoAtCapLeverages leverage 0 1 ^ 2
      ∧ (∑ coord : Fin 2, twoAtCapSquares leverage radial 0 0 2 coord ^ 2)
          = twoAtCapLeverages leverage 0 2 ^ 2 := by
  have h1 : (2 * leverage - 1) ≠ 0 := by intro h; nlinarith
  have h3 : (2 * leverage - 3) ≠ 0 := by intro h; nlinarith
  refine ⟨⟨div_pos one_pos (by linarith), div_pos (by linarith) (by linarith)⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp
    ring
  · simp only [twoAtCapSquares, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    field_simp
    ring
  · simp only [twoAtCapSquares, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    field_simp
    ring
  · simp only [twoAtCapLeverages, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    field_simp
    ring
  · simp only [Fin.sum_univ_two, twoAtCapSquares, twoAtCapLeverages,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    linear_combination hradial
  · simp only [Fin.sum_univ_two, twoAtCapSquares, twoAtCapLeverages,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    linear_combination hradial
  · simp only [Fin.sum_univ_two, twoAtCapSquares, twoAtCapLeverages,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    ring

/-- **The silence bridge**: the two cap-atom `pairEntry` values sum to
`2·capSilenceSum` and multiply to `capSilenceProduct`.  So the `(x, ρ)` silence
functions really are `M_A + M_B` and `M_A · M_B`. -/
theorem capSilence_sum_and_product {leverage radial xcoord ycoord radius : ℝ}
    (hradial : radial ^ 2 = 2 * leverage - 1)
    (hheight : ycoord ^ 2 = radius ^ 2 - xcoord ^ 2) :
    twoAtCapEntry leverage radial xcoord ycoord radius 0
        + twoAtCapEntry leverage radial xcoord ycoord radius 1
        = 2 * capSilenceSum leverage xcoord radius
      ∧ twoAtCapEntry leverage radial xcoord ycoord radius 0
          * twoAtCapEntry leverage radial xcoord ycoord radius 1
        = capSilenceProduct leverage xcoord radius := by
  constructor
  · simp only [twoAtCapEntry, pairEntry, twoAtCapSquares, twoAtCapLeverages,
      capSilenceSum, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue]
    ring
  · simp only [twoAtCapEntry, pairEntry, twoAtCapSquares, twoAtCapLeverages,
      capSilenceProduct, capSilenceSum, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue]
    linear_combination (-(ycoord ^ 2)) * hradial
      + (-(2 * leverage - 1)) * hheight

/-- The two cap atoms' contribution, before any substitution: a pure ring
identity in which the odd powers of `radial` have already cancelled.  This is
what makes the channel numerator even in `u` and in `y`. -/
theorem twoAtCap_capPairContribution (leverage radial xcoord ycoord radius : ℝ) :
    twoAtCapEntry leverage radial xcoord ycoord radius 0
        * twoAtCapDistanceSq leverage radial xcoord ycoord 0
      + twoAtCapEntry leverage radial xcoord ycoord radius 1
        * twoAtCapDistanceSq leverage radial xcoord ycoord 1
      = 2 * capSilenceSum leverage xcoord radius
          * ((leverage - 1 - xcoord) ^ 2 + ycoord ^ 2 + radial ^ 2)
        - 4 * radial ^ 2 * ycoord ^ 2 := by
  simp only [twoAtCapEntry, twoAtCapDistanceSq, pairEntry, twoAtCapSquares,
    twoAtCapLeverages, capSilenceSum, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue]
  ring

/-- The light atom's contribution, before any substitution: another pure ring
identity, exposing `y²` at first power so the height relation can be applied. -/
theorem twoAtCap_lightContribution (leverage radial xcoord ycoord radius : ℝ) :
    twoAtCapEntry leverage radial xcoord ycoord radius 2
        * twoAtCapDistanceSq leverage radial xcoord ycoord 2
      = (-((2 * leverage - 2) / (2 * leverage - 3)) * xcoord
          - ((2 * leverage - 2) / (2 * leverage - 3) - 2) * (radius - 2) + 2)
        * (((2 * leverage - 2) / (2 * leverage - 3) + xcoord) ^ 2 + ycoord ^ 2) := by
  simp only [twoAtCapEntry, twoAtCapDistanceSq, pairEntry, twoAtCapSquares,
    twoAtCapLeverages, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue]
  ring

/-- **The channel bridge**: `capChannelNumerator` really IS the weighted channel
sum `Σ_c w_c · M_c(X) · |S_c − X|²` built from the repo's `pairEntry`, once
`u² = 2L−1` and `y² = ρ² − x²`.  Stated scaled by `2L−1` so that the atom
weights `1/(2L−1)`, `1/(2L−1)`, `(2L−3)/(2L−1)` appear as the integer profile
`1, 1, 2L−3` — the same statement, with no weight denominator.

This is the identification that makes every result in this file a statement
about the planar platform's own obstruction entries rather than about an
ad-hoc polynomial. -/
theorem capChannelNumerator_eq_pairEntrySum {leverage radial xcoord ycoord radius : ℝ}
    (hlev : 2 < leverage) (hradial : radial ^ 2 = 2 * leverage - 1)
    (hheight : ycoord ^ 2 = radius ^ 2 - xcoord ^ 2) :
    (2 * leverage - 1) * capChannelNumerator leverage xcoord radius
      = twoAtCapEntry leverage radial xcoord ycoord radius 0
          * twoAtCapDistanceSq leverage radial xcoord ycoord 0
        + twoAtCapEntry leverage radial xcoord ycoord radius 1
          * twoAtCapDistanceSq leverage radial xcoord ycoord 1
        + (2 * leverage - 3)
          * (twoAtCapEntry leverage radial xcoord ycoord radius 2
            * twoAtCapDistanceSq leverage radial xcoord ycoord 2) := by
  have h3 : (2 * leverage - 3) ≠ 0 := by intro h; nlinarith
  have h3norm : (-3 + leverage * 2) ≠ 0 := by intro h; nlinarith
  have hsqnorm : (9 - leverage * 12 + leverage ^ 2 * 4) ≠ 0 := by
    have hrw : (9 - leverage * 12 + leverage ^ 2 * 4) = (2 * leverage - 3) ^ 2 := by ring
    rw [hrw]; exact pow_ne_zero 2 h3
  rw [twoAtCap_capPairContribution, twoAtCap_lightContribution, hradial, hheight]
  unfold capChannelNumerator capSilenceSum
  field_simp
  ring

end Gtz
