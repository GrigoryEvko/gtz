/-
# The collar EXPONENT: what erodes, how fast, and what the a priori lever is worth

This file is the exponent bookkeeping for residual 7.  `Gtz.Quantitative.CollarRate`
ships the reduction machinery with the measured rate law passed in as a
hypothesis; what was missing was any kernel-visible statement about the
EXPONENT in that law — the number that decides whether the clean `c/l̄`
survives.  Nothing here closes residual 7.  Every lemma is unconditional
arithmetic or topology about the SHAPE of an eroding rate; no lemma consumes
a measured constant, and no lemma asserts one.

## What is hypothesis and what is theorem

**LOUDLY: every statement below takes the erosion exponent as a bound
variable.**  `collarRate_tendsto_zero`, `linearLaw_collapses_of_exponent_gt_one`,
`erosionExponents_incomparable` and friends say what FOLLOWS from an exponent,
never what the exponent IS.  The measured values live in the campaign log, not
in the kernel, and they are numerics, not proofs.  The only lemmas here that
commit to a number are the two a-priori-bound witnesses, and those are exact
natural-number arithmetic about a published theorem's bound, not about GTZ.

## The three separate exponents, which must never be conflated

1. the FIRST-ORDER TRANSVERSE RATE `ρ(l̄)` at a tie point — a derivative
   object, defined only ON the tie variety;
2. the CONSUMED Łojasiewicz MODULUS `inf (Φ−1)/dist₅` over the collared class
   — the quantity occupying the `htube` slot of `collared_two_piece_law`, hence
   the one that actually gates residual 7;
3. the Łojasiewicz EXPONENT IN `dist` — the power `α` in `Φ − 1 ≥ c·dist^α`,
   which is what makes `two_piece_law_assembly` (and `rate_floor_of_weight_floor`)
   the right shape at `α = 1` and the wrong shape at `α > 1`.

(1) and (2) are exponents in `l̄`; (3) is an exponent in `dist`.
`erosionExponents_incomparable` is the kernel form of the observation that two
erosion measurements with different exponents cannot be measurements of the
same quantity up to constants — so a ledger carrying both `1.46` and
`1.0–1.2` for `ρ` and the modulus is asserting they are different objects, and
that assertion is falsifiable.

It was falsified.  An independent measurement (float64, ties Newton-polished to
`|Φ − 1| ~ 1e-15` so the active gate set is exact — eight gates at
`λ_min = 1`, two at `λ_min = 0`, spectral separation exactly one) finds
`ρ` and the consumed modulus EQUAL to five decimal places at the extremal tie
at every leverage cap in `[5, 78]`, with the Łojasiewicz exponent in `dist`
equal to one (the ratio is constant to `6e-3` relative across three decades of
probe step, and the projection distance equals the probe step to six digits).
So (1) and (2) are not two objects with two exponents; and (3) — the exponent
that decides whether `two_piece_law_assembly` has the right SHAPE — is one, at
the extremal tie, at every cap tested.  What erodes is the CONSTANT.  These are
numerics, they are not proofs, and none of them is asserted below.

The same numerics measure that constant's erosion at `β ≈ 1.92–1.97` over the
band where the tie search is reliable, `l̄ ∈ [5, 44]` — under one decade.  Above
`l̄ ≈ 50` the random tie search stops reaching the extremal ties and the measured
minimum becomes an over-estimate, so the exponent's `l̄ → ∞` value is NOT
settled.  What IS settled on the measured band is `β > 1`: the diagnostic
`m·l̄` falls monotonically from `1.10` at `l̄ = 5` to `0.152` at `l̄ = 36`, an
assumption-free eight-fold collapse of the clean `c/l̄` — for the CONSUMED
modulus, not merely for the first-order proxy.

One control deserves recording because the campaign's diary lists it as a
reproduction of the eroded exponent and it is not one.  The once-split family
(regular simplex with one direction cloned, weights `(1/4,1/4,1/4,s,1/4−s)`,
exactly rational, an exact tie at every `s`) has `ρ ~ wmin^1` in the ambient
metric and `ρ ~ wmin^(1/2)` in the W₂ position metric, with local slopes
converging to `1.0000` and `0.5000` over four decades and `ρ·l̄ → 1.182`
constant.  That is a clean `c/l̄` with a genuinely `l̄`-independent constant: the
once-split family is the NO-EROSION CONTROL, not a witness.  The erosion lives
on the other tie branches, which the once-split family does not see.

## Why (1) and (2) can differ at all

`tube_law_from_rate_curvature` (`Gtz.Certificates.LawEquivalence`) delivers the
linear law `(rate/2)·dist ≤ φ` only on the radius `dist ≤ rate/(2·curv)`.
`tubeRadius_mono_in_rate` and `tubeRadius_antitone_in_leverage` make explicit
that this radius SHRINKS as the first-order rate erodes, so a `ρ`-derived
guarantee covers a vanishing tube while the global infimum is increasingly set
by the off-tube channel.  That is the structural reason the two exponents are
not forced to agree — and equally the reason a measurement of one is not a
measurement of the other.

## The a priori semialgebraic lever, priced

The collared class is a basic closed semialgebraic set — read the four
conditions of `Gtz.collaredSet` — and `Gtz.isCompact_collaredSet` supplies the
closed-and-bounded hypothesis of the effective Łojasiewicz inequality (Basu &
Mohammad-Nezhad, *Forum Math. Sigma* **12** (2024) e115, Thm 2.2): for
`f, g` continuous semialgebraic of degree `≤ d` in `n` variables on a compact
basic semialgebraic set with `f⁻¹(0) ⊆ g⁻¹(0)`, one gets `|g|^N ≤ c·|f|` with
`N ≤ (8d)^(2(n+7))`.  At `(5,3)` the ambient dimension is
`n = m·k + m = 20` and the margin's describing degree is `d = 6` (the
characteristic cubic of `S_C` has coefficients of degree 6 in the atoms), so
`N ≤ 48^54`.  `effectiveLojasiewiczUpperBound_exceeds_ten_pow_ninety` is that
number, kernel-checked, against a measured exponent of about `1`.

The lever is not merely weak, it is dead: the same paper's Example 2.4 (after
Ji–Kollár–Shiffman) gives a MATCHING GENERAL LOWER bound `d^n`, and
`effectiveLojasiewiczLowerBound_exceeds_ten_pow_fifteen` records that even the
best exponent any general-purpose theorem could ever deliver at this size is
already fifteen orders of magnitude above the measured one.  No improvement in
effective semialgebraic geometry can rescue this route; a usable exponent must
come from the specific metric-regularity structure instead.

Kollár's sharper `(2d)^n` does not apply: it needs an ISOLATED zero, and the
GTZ zero set `{Φ = 1}` is positive-dimensional.  D'Acunto–Kurdyka does not
apply either: it needs `f` to be a POLYNOMIAL and bounds the GRADIENT exponent,
while `Φ = max_C λ_min(S_C)` is a max of smallest eigenvalues — semialgebraic
and continuous, but neither polynomial nor differentiable at the ties.
-/
import Mathlib
import Gtz.Certificates.LawEquivalence
import Gtz.Quantitative.CollarRate
import Gtz.Quantitative.StrictDomination
import Gtz.Design.CollaredCompact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Filter Topology

/-! ### The eroding rate floor vanishes: residual 7's limit, as a matter of shape -/

/-- **Any positive erosion exponent sends the guaranteed collar rate to zero.**
The rate floor `rateConst / leverageCap ^ exponent` that
`rate_floor_of_weight_floor_rpow` delivers tends to `0` along the leverage cap
for EVERY positive exponent.  So the question "is the `l̄ → ∞` limit of the
collar rate positive?" is settled negatively by the SHAPE alone, the moment any
positive erosion exponent is granted — no measurement needed, and in particular
the answer does not depend on whether the exponent is `1`, `1.2` or `1.46`.
What a measurement can still decide is the RATE of the decay, which is what
`linearLaw_collapses_of_exponent_gt_one` turns on. -/
theorem collarRate_tendsto_zero (rateConst exponent : ℝ) (hExp : 0 < exponent) :
    Tendsto (fun leverageCap : ℝ => rateConst / leverageCap ^ exponent)
      atTop (𝓝 0) :=
  (tendsto_const_nhds (x := rateConst) (f := atTop (α := ℝ))).div_atTop
    (tendsto_rpow_atTop hExp)

/-! ### The trichotomy at exponent one -/

/-- **Exponent one is exactly leverage-uniformity.** At `exponent = 1` the
product of the rate floor with the leverage cap is the CONSTANT `rateConst`:
this is the precise content of "a clean `c/l̄` with an `l̄`-independent
constant", the statement residual 7 is about. -/
theorem linearLaw_scaleInvariant_at_exponent_one
    (rateConst leverageCap : ℝ) (hCap : 0 < leverageCap) :
    rateConst / leverageCap ^ (1 : ℝ) * leverageCap = rateConst := by
  rw [Real.rpow_one]
  field_simp

/-- **Above exponent one the clean `c/l̄` is destroyed.** For any erosion
exponent strictly above `1`, the leverage-scaled rate floor tends to zero: no
constant `c` makes `rate ≥ c/l̄` hold for all leverage caps.  This is the kernel
form of "the clean `c/l̄` is refuted" — and it is exactly what a measured
exponent strictly above `1` would deliver. -/
theorem linearLaw_collapses_of_exponent_gt_one
    (rateConst exponent : ℝ) (hExp : 1 < exponent) :
    Tendsto (fun leverageCap : ℝ =>
        rateConst / leverageCap ^ exponent * leverageCap) atTop (𝓝 0) := by
  have hEventually : (fun leverageCap : ℝ => rateConst / leverageCap ^ (exponent - 1))
      =ᶠ[atTop] (fun leverageCap : ℝ =>
        rateConst / leverageCap ^ exponent * leverageCap) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with leverageCap hPos
    rw [Real.rpow_sub hPos, Real.rpow_one]
    field_simp
  exact Tendsto.congr' hEventually
    (collarRate_tendsto_zero rateConst (exponent - 1) (by linarith))

/-- **Below exponent one the leverage-scaled floor diverges.** The remaining
branch of the trichotomy, recorded so the exponent-one boundary is visible from
both sides: a sub-linear erosion would make the guaranteed rate BETTER than
`c/l̄` at large leverage. -/
theorem linearLaw_diverges_of_exponent_lt_one
    (rateConst exponent : ℝ) (hRateConst : 0 < rateConst) (hExp : exponent < 1) :
    Tendsto (fun leverageCap : ℝ =>
        rateConst / leverageCap ^ exponent * leverageCap) atTop atTop := by
  have hEventually : (fun leverageCap : ℝ => rateConst * leverageCap ^ (1 - exponent))
      =ᶠ[atTop] (fun leverageCap : ℝ =>
        rateConst / leverageCap ^ exponent * leverageCap) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with leverageCap hPos
    rw [Real.rpow_sub hPos, Real.rpow_one]
    field_simp
  exact Tendsto.congr' hEventually
    (Filter.Tendsto.const_mul_atTop hRateConst (tendsto_rpow_atTop (by linarith)))

/-! ### Two exponents cannot be one quantity -/

/-- **Different erosion exponents are different quantities.** If one erosion
measurement returns exponent `mildExponent` and another returns a strictly
larger `harshExponent`, then the two rate floors diverge from one another
without bound: no positive constants make them comparable, so they cannot be
two measurements of a single quantity.

This is the kernel form of the ledger check that the campaign's `α ≈ 1.46` for
the FIRST-ORDER transverse proxy and its `α ∈ [1.0, 1.2]` for the CONSUMED
Łojasiewicz modulus are claims about two different objects.  Whichever number
is fed into `rate_floor_of_weight_floor_rpow`, feeding the other is a different
theorem — and only the consumed modulus sits in the `htube` slot of
`collared_two_piece_law`. -/
theorem erosionExponents_incomparable
    (mildConst harshConst mildExponent harshExponent : ℝ)
    (hMildConst : 0 < mildConst) (hHarshConst : 0 < harshConst)
    (hOrder : mildExponent < harshExponent) :
    Tendsto (fun leverageCap : ℝ =>
        (mildConst / leverageCap ^ mildExponent)
          / (harshConst / leverageCap ^ harshExponent)) atTop atTop := by
  have hEventually :
      (fun leverageCap : ℝ =>
          (mildConst / harshConst) * leverageCap ^ (harshExponent - mildExponent))
        =ᶠ[atTop] (fun leverageCap : ℝ =>
          (mildConst / leverageCap ^ mildExponent)
            / (harshConst / leverageCap ^ harshExponent)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with leverageCap hPos
    have hMildPow : (0 : ℝ) < leverageCap ^ mildExponent :=
      Real.rpow_pos_of_pos hPos _
    have hHarshPow : (0 : ℝ) < leverageCap ^ harshExponent :=
      Real.rpow_pos_of_pos hPos _
    rw [Real.rpow_sub hPos]
    field_simp
  exact Tendsto.congr' hEventually
    (Filter.Tendsto.const_mul_atTop (by positivity)
      (tendsto_rpow_atTop (by linarith)))

/-! ### Why the two exponents are not forced to agree: the shrinking tube -/

/-- **The tube on which the first-order rate delivers the linear law shrinks
with the rate.** `tube_law_from_rate_curvature` produces `(rate/2)·dist ≤ φ`
only under `dist·(2·curv) ≤ rate`, i.e. only on the radius `rate/(2·curv)`.
That radius is MONOTONE in the rate, so an eroding first-order rate buys the
linear law on a proportionally vanishing neighbourhood of the tie variety. -/
theorem tubeRadius_mono_in_rate {slowRate fastRate curv : ℝ}
    (hCurv : 0 < curv) (hRates : slowRate ≤ fastRate) :
    slowRate / (2 * curv) ≤ fastRate / (2 * curv) := by
  have hDen : (0 : ℝ) < 2 * curv := by linarith
  gcongr

/-- **Hence the admissible tube radius is antitone in the leverage cap.**
Chaining `rate_floor_antitone_in_leverage` with `tubeRadius_mono_in_rate`: at a
higher-leverage cell both the guaranteed first-order rate AND the radius on
which it yields the linear law are smaller.  So the region where the
`ρ`-derived guarantee is in force is itself eroding, and outside it the global
modulus is set by the off-tube channel — the structural reason the consumed
modulus is not the first-order proxy. -/
theorem tubeRadius_antitone_in_leverage
    {rateConst exponent leverageCap1 leverageCap2 curv : ℝ}
    (hRateConst : 0 ≤ rateConst) (hExp : 0 ≤ exponent) (hCurv : 0 < curv)
    (hCap1 : 0 < leverageCap1) (hMono : leverageCap1 ≤ leverageCap2) :
    rateConst / leverageCap2 ^ exponent / (2 * curv)
      ≤ rateConst / leverageCap1 ^ exponent / (2 * curv) :=
  tubeRadius_mono_in_rate hCurv
    (rate_floor_antitone_in_leverage hRateConst hExp hCap1 hMono)

/-! ### A ceiling on the consumed modulus, from the mechanized Weyl bound -/

/-- The consumed Łojasiewicz modulus of a margin at a point: the ratio of the
margin to the distance to the margin's zero set.  This is the object in the
`htube` slot of `collared_two_piece_law`; `Gtz.dominationMargin` composed with
`Gtz.collaredSet`'s tie locus is the intended instance. -/
noncomputable def consumedModulus {carrier : Type*} [MetricSpace carrier]
    (margin : carrier → ℝ) (zeroSet : Set carrier) (point : carrier) : ℝ :=
  margin point / Metric.infDist point zeroSet

/-- **A Lipschitz margin caps its own modulus at every zero.** If the margin
vanishes at `zero` then it is at most `lipschitzConstant · dist point zero`;
this is the elementary half of the ceiling. -/
theorem margin_le_lipschitz_mul_dist {carrier : Type*} [MetricSpace carrier]
    {margin : carrier → ℝ} {lipschitzConstant : NNReal}
    (hLipschitz : LipschitzWith lipschitzConstant margin)
    {point zero : carrier} (hZero : margin zero = 0) :
    margin point ≤ lipschitzConstant * dist point zero := by
  have hdist := hLipschitz.dist_le_mul point zero
  rw [Real.dist_eq, hZero, sub_zero] at hdist
  exact le_trans (le_abs_self _) hdist

/-- **The consumed modulus can never exceed the margin's Lipschitz constant.**
Weyl's bound `lipschitzWith_lambdaMinCLM` (mechanized in
`Gtz.Quantitative.MarginContinuity`) makes `λ_min` `1`-Lipschitz, hence the
domination margin Lipschitz on the compact collared class; this lemma turns
that into a hard CEILING on any collar rate.  The two-piece law's constant
`min (rateConst/leverageCap) (offGap/domainCap)` therefore lives in
`[0, lipschitzConstant]`: residual 7 is a question about where in that interval
the truth sits, and no program can answer it above the ceiling. -/
theorem consumedModulus_le_lipschitzConstant {carrier : Type*} [MetricSpace carrier]
    {margin : carrier → ℝ} {lipschitzConstant : NNReal}
    (hLipschitz : LipschitzWith lipschitzConstant margin)
    {zeroSet : Set carrier} (hNonempty : zeroSet.Nonempty)
    (hVanishes : ∀ zero ∈ zeroSet, margin zero = 0)
    (point : carrier) :
    consumedModulus margin zeroSet point ≤ lipschitzConstant := by
  have hCoeNonneg : (0 : ℝ) ≤ (lipschitzConstant : ℝ) := lipschitzConstant.coe_nonneg
  have hkey : ∀ zero ∈ zeroSet, margin point ≤ lipschitzConstant * dist point zero :=
    fun zero hmem => margin_le_lipschitz_mul_dist hLipschitz (hVanishes zero hmem)
  rcases le_or_gt (Metric.infDist point zeroSet) 0 with hzero | hpos
  · have hEq : Metric.infDist point zeroSet = 0 :=
      le_antisymm hzero Metric.infDist_nonneg
    rw [consumedModulus, hEq, div_zero]
    exact hCoeNonneg
  · rw [consumedModulus, div_le_iff₀ hpos]
    rcases eq_or_lt_of_le hCoeNonneg with hzeroConst | hposConst
    · obtain ⟨zero, hmem⟩ := hNonempty
      have hbound := hkey zero hmem
      rw [← hzeroConst] at hbound ⊢
      simpa using hbound
    · have hstep : margin point / lipschitzConstant ≤ Metric.infDist point zeroSet := by
        refine (Metric.le_infDist hNonempty).mpr fun zero hmem => ?_
        rw [div_le_iff₀ hposConst]
        linarith [hkey zero hmem]
      calc margin point
          = margin point / lipschitzConstant * lipschitzConstant := by field_simp
        _ ≤ Metric.infDist point zeroSet * lipschitzConstant := by gcongr
        _ = lipschitzConstant * Metric.infDist point zeroSet := mul_comm _ _

/-! ### The tie variety, named over real designs

Everything in `Gtz.Quantitative.CollarRate` is stated over bare reals or an abstract
compact carrier — residual 7 has, until here, no kernel-level statement about
the GTZ objects themselves.  The zero set the collar rate is measured against
deserves at least a name and an intrinsic characterisation. -/

section TieLocus

variable {m k : ℕ} [Nonempty (Fin k)]

/-- **The tie locus of the collared class**: collared configurations at which
NO gate strictly dominates the identity.  This is the `Z5` of the collar
literature — the set the funneling distance `dist₅` is measured to, and (by
`gtzWeighted_of_le_five`, which forces `Φ ≥ 1` at rank five) exactly the set
where the domination margin vanishes. -/
def tieLocus (m k : ℕ) [Nonempty (Fin k)] (weightFloor : ℝ)
    (gates : Finset (Finset (Fin m))) :
    Set ((Fin m → Fin k → ℝ) × (Fin m → ℝ)) :=
  {config | config ∈ collaredSet m k weightFloor ∧
    ∀ gate ∈ gates, ¬ (subsetSumRaw config gate - 1).PosDef}

/-- **The margin is nonpositive exactly on the tie condition.** Contrapositive
of `margin_pos_iff_exists_strictDominates`: the domination margin
`Φ − 1 = sup_C λ_min(S_C) − 1` fails to be positive precisely when every gate
fails to strictly dominate.  Unconditional — no rank hypothesis, no compactness. -/
theorem margin_nonpos_iff_no_gate_strictDominates
    (config : (Fin m → Fin k → ℝ) × (Fin m → ℝ))
    (gates : Finset (Finset (Fin m))) (hNe : gates.Nonempty) :
    (gates.sup' hNe (fun gate => lambdaMinMat (subsetSumRaw config gate))) - 1 ≤ 0
      ↔ ∀ gate ∈ gates, ¬ (subsetSumRaw config gate - 1).PosDef := by
  rw [← not_lt, margin_pos_iff_exists_strictDominates config gates hNe]
  simp only [not_exists, not_and]

/-- **Membership of the tie locus is exactly collaredness plus a nonpositive
margin.** So `tieLocus` really is `{Φ ≤ 1} ∩ collaredSet`, and — once
`gtzWeighted_of_le_five` supplies `Φ ≥ 1` at rank five — exactly `{Φ = 1}`.
This is the set that `collared_two_piece_law`'s `dist` argument measures to,
now named in the kernel rather than only in prose. -/
theorem mem_tieLocus_iff (weightFloor : ℝ)
    (config : (Fin m → Fin k → ℝ) × (Fin m → ℝ))
    (gates : Finset (Finset (Fin m))) (hNe : gates.Nonempty) :
    config ∈ tieLocus m k weightFloor gates ↔
      config ∈ collaredSet m k weightFloor ∧
        (gates.sup' hNe (fun gate => lambdaMinMat (subsetSumRaw config gate))) - 1 ≤ 0 := by
  rw [tieLocus, Set.mem_setOf_eq,
    margin_nonpos_iff_no_gate_strictDominates config gates hNe]

end TieLocus

/-! ### The a priori effective Łojasiewicz lever, priced exactly -/

/-- **The effective semialgebraic bound is ninety orders of magnitude off.**
Basu–Mohammad-Nezhad (Forum Math. Sigma 12 (2024) e115, Thm 2.2) bound the
Łojasiewicz exponent of a pair of continuous semialgebraic functions of degree
`≤ d` in `n` variables on a compact basic semialgebraic set by
`(8d)^(2(n+7))`.  At collared `(5,3)` — `n = 5·3 + 5 = 20` ambient coordinates,
`d = 6` from the characteristic cubic of `S_C` — that is `48^54`, a
ninety-one-digit integer, against a Łojasiewicz exponent in `dist` measured at
about `1`.  Kernel-checked so the corpus carries a record that this lever is
priced, not merely "non-effective in practice". -/
theorem effectiveLojasiewiczUpperBound_exceeds_ten_pow_ninety :
    (10 : ℕ) ^ 90 < (8 * 6 : ℕ) ^ (2 * (20 + 7)) := by norm_num

/-- **And the lever is dead from below, not merely weak from above.** The same
paper's Example 2.4 (after Ji–Kollár–Shiffman) exhibits a matching GENERAL
lower bound `d^n` for the best exponent any theorem of this kind can deliver.
At collared `(5,3)` that is `6^20`, already sixteen digits — fifteen orders of
magnitude above the measured exponent.  So no sharpening of effective
semialgebraic geometry can ever produce a usable collar exponent at this size:
the gap is closed from below, and the route must be abandoned rather than
improved. -/
theorem effectiveLojasiewiczLowerBound_exceeds_ten_pow_fifteen :
    (10 : ℕ) ^ 15 < (6 : ℕ) ^ 20 := by norm_num

/-- The `(6,3)` figures, for the record: the upper bound is `48^62` and the
matching general lower bound is `6^24`, both worse than at `(5,3)`.  So the a
priori lever degrades with rank, in the direction that matters. -/
theorem effectiveLojasiewiczBounds_worsen_at_rank_six :
    (8 * 6 : ℕ) ^ (2 * (20 + 7)) < (8 * 6 : ℕ) ^ (2 * (24 + 7))
      ∧ (6 : ℕ) ^ 20 < (6 : ℕ) ^ 24 := by
  constructor
  · exact Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  · exact Nat.pow_lt_pow_right (by norm_num) (by norm_num)

end Gtz
