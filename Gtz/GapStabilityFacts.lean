/-
# GAP-S stability: the exact structural facts (H1a/H3b support)

Supporting algebra for the GAP-S stability leg (residual 8). GAP-S itself is
NOT closed — each of H1a (the envelope law), H1b (the C_B(L) argmax), and H3b
(the quantitative strata) remains PROVEN-conditional on one precisely-named
analytic wall:

  * H1a — a uniform second-order coefficient K₁(ℓ̄) as a theorem (Bonnans–Shapiro
    second-order tangent-set analysis over the family; the channel is bounded by
    the kernel `whitening_gram_exact`, which is the WALL, not consumed here);
  * H1b — the full symbolic monotonicity of `C_B(L)` along the cap boundary;
  * H3b — the transverse coercivity modulus `s₂ > 0` derived from the kernel
    `closure_forces_obtuse_pair` (Lyusternik–Graves; currently assumed, the WALL).

The theorems below are the exact, non-tautological facts underneath those laws —
standalone ordered-field algebra with every analytic hypothesis named, not
smuggled. They do NOT consume the kernel whitening/closure instruments (those are
the walls) and do NOT close GAP-S. The envelope/argmax/strata *shape* combinators
from the drafting round (pure `linarith` over undischarged hypotheses) are
deliberately omitted. Result of the gtz3-gaps-stability workflow (audit #1 SOUND;
audit #2 GAP_FOUND on the framing only — the numbers and these facts verified
airtight).
-/
import Mathlib

namespace Gtz

/-- **The per-pair budget decomposition** (H1a core). A pair with geometric
weight `b`, excess trace `beta`, own critical slack `slack0`, at level slack
`level`, contributes `b · 2(level − slack0)(beta − level − slack0)` to the
budget, splitting as the first-order rate `(2·b·beta)·x` (`x = level − slack0`)
plus the exact second-order remainder `2·b·x·(x − 2·level)`. Pure ring identity. -/
theorem pair_budget_decompose (b beta slack0 level : ℝ) :
    b * (2 * (level - slack0) * (beta - level - slack0))
      = (2 * b * beta) * (level - slack0)
        + 2 * b * (level - slack0) * ((level - slack0) - 2 * level) := by
  ring

/-- **Tight-pair self-suppression** (H1a core): if a pair's slack deficit
`deficit = level − slack0` lies in `[0, 2·level]` (near-tight), its second-order
remainder `2·b·deficit·(deficit − 2·level)` is nonpositive for `b ≥ 0`. So a
near-tight pair is bounded above by its first-order term and never supplies the
boxed-law excess — the positive remainder is confined to the down-pair /
vanishing-atom channel priced by the corrected constant. -/
theorem tight_pair_second_order_nonpos {b level deficit : ℝ}
    (hb : 0 ≤ b) (hlow : 0 ≤ deficit) (hhigh : deficit ≤ 2 * level) :
    2 * b * deficit * (deficit - 2 * level) ≤ 0 := by
  have hfac : deficit - 2 * level ≤ 0 := by linarith
  nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hb) hlow, hfac]

/-- A near-tight pair is LP-covered: its whole contribution is at most its
first-order rate times its deficit (the payoff of `pair_budget_decompose` +
`tight_pair_second_order_nonpos`). -/
theorem pair_budget_le_firstOrder {b beta slack0 level : ℝ}
    (hb : 0 ≤ b) (hlow : 0 ≤ level - slack0)
    (hhigh : level - slack0 ≤ 2 * level) :
    b * (2 * (level - slack0) * (beta - level - slack0))
      ≤ (2 * b * beta) * (level - slack0) := by
  rw [pair_budget_decompose]
  have := tight_pair_second_order_nonpos hb hlow hhigh
  linarith

/-- **The realness gate, ℝ side**: a strictly positive budget under the linear
envelope `budget ≤ cFirst·maxSlack` with `cFirst > 0` forces `maxSlack > 0`.
Over ℝ this is delivered by `gtz_rank_two` (`σ* ≥ 0`) — the single real-field
consumption of the whole GAP-S argument. -/
theorem envelope_forces_slack_pos {budget cFirst maxSlack : ℝ}
    (hbudgetPos : 0 < budget) (hcFirstPos : 0 < cFirst)
    (henvelope : budget ≤ cFirst * maxSlack) :
    0 < maxSlack := by
  by_contra hle
  rw [not_lt] at hle
  have : cFirst * maxSlack ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcFirstPos.le hle
  linarith

/-- **The realness gate, ℂ side**: the complex SIC / Bloch tetrahedron is a
silent design with slack `1 − 2/√3 = α − 1 < 0` yet nonnegative budget, so the
envelope cannot hold over ℂ — exactly where the α-cap says it must not. The exact
sign fact. -/
theorem complex_sic_slack_neg : (1 : ℝ) - 2 / Real.sqrt 3 < 0 := by
  have h3 : (0:ℝ) < 3 := by norm_num
  have hsqrt : (1:ℝ) < Real.sqrt 3 := by
    rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hpos : (0:ℝ) < Real.sqrt 3 := by linarith
  rw [sub_neg, lt_div_iff₀ hpos]
  nlinarith [Real.sq_sqrt h3.le, hsqrt]

/-- **Per-stratum metric regularity, exponent 1** (H3b core): if the slack map is
coercive with modulus `stratumModulus` on the transverse space —
`stratumModulus²·transverseDist² ≤ slackSize²` — then a configuration whose slack
has size `≤ epsilon` sits within `epsilon / stratumModulus` of the zero-slack
(family-split) manifold. The distance is LINEAR in the slack, forced by the
coercivity (the H3b wall: deriving that coercivity from `closure_forces_obtuse_pair`),
NOT by a generic Łojasiewicz exponent. -/
theorem transverse_dist_le_of_coercive
    {stratumModulus transverseDist slackSize epsilon : ℝ}
    (hmod : 0 < stratumModulus)
    (hcoercive : stratumModulus ^ 2 * transverseDist ^ 2 ≤ slackSize ^ 2)
    (hslack : slackSize ≤ epsilon) (hslackNonneg : 0 ≤ slackSize) :
    transverseDist ≤ epsilon / stratumModulus := by
  have hstep : stratumModulus * transverseDist ≤ slackSize := by
    nlinarith [hcoercive, hslackNonneg, mul_pos hmod hmod]
  rw [le_div_iff₀ hmod, mul_comm]
  linarith [hstep, hslack]

/-- **The quotient floor is uniform** (H3b core): the reduced moment-Gram's
smallest nonzero eigenvalue is `2` at every family stratum — the residual
quadratic evaluated at `x = 2` is `4(lev − 2)² ≥ 0`, vanishing only at the
symmetric (Mercedes) design, so the transverse conditioning never degrades below
2. Only the slack modulus `s₂` degrades with leverage. -/
theorem quotient_floor_uniform (lev : ℝ) :
    0 ≤ (2 * lev - 3) * 2 ^ 2 - (4 * lev ^ 2 - 2 * lev - 5) * 2
        + (12 * lev ^ 2 - 28 * lev + 18) := by
  have h : (2 * lev - 3) * 2 ^ 2 - (4 * lev ^ 2 - 2 * lev - 5) * 2
      + (12 * lev ^ 2 - 28 * lev + 18) = 4 * (lev - 2) ^ 2 := by ring
  rw [h]; positivity

end Gtz
