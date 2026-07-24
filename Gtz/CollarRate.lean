/-
# The collar-rate reduction machinery (residual 7 — NOT closed)

Residual 7 — the transverse collar rate `ρ(l̄)` of the funneling law near the
tie variety Z5 — is **NOT closed**. There is no proven `ρ(l̄) ≥ c/l̄` with an
`l̄`-independent constant: the near-clone (Jelonek) boundary erodes the
first-order transverse rate as `ρ ~ l̄^(−α)` with `α ≈ 1.46` (reproduced four
independent ways — exact once-split family, the SS115 128-worker scan, and the
SS135 planar `s₂ ~ 1/√l̄` analog). The named wall is a uniform continuum lower
bound on `λ_min·σ_min` — the Hoffman-conditioning of the near-clone difference
mode's smallest singular value — which is genuinely open.

What IS shipped here is the field-blind REDUCTION MACHINERY, together with the
honest reframe: the controlling quantity is the MINIMUM WEIGHT, not the maximum
leverage (`l_max` is a red herring). Every lemma below is stated
hypothesis-parameterized — the measured proportionality (`rate ≥ c·wmin^α`) and
the geometric inputs (compactness, the weight floor) enter as hypotheses, so
these are the abstract skeleton the numerics would feed, not a closed proof.

Genuine kernel consumption is exactly ONE decl: `collared_two_piece_law`
instantiates `two_piece_law_assembly` (`Gtz.LawEquivalence`). The other lemmas
are abstract over any ordered field / any compact carrier and do NOT hardwire the
kernel leverage ceiling or `isCompact_collaredSet` (they are designed to accept
those as hypotheses at the call site).

Field discipline: the Stiemke firing (`covector_forces_firing`,
`firing_margin_ge_of_covector_and_floor`) is FIELD-BLIND — correct over any
ordered field, since realness is consumed upstream at `Φ ≥ 1`. The rate LAW
`Φ − 1 ≥ ρ·dist` is real-only.

Honest constants, per audit: the once-split proportionality constant is the
AMBIENT-metric `2/(3√7) ≈ 0.252`; the W₂-transport-consistent value is smaller,
`≈ 0.206`. The eroded exponent `α ≈ 1.46` is the FIRST-ORDER transverse-rate
proxy; the actual consumed Łojasiewicz modulus `(Φ−1)/dist₅` erodes more mildly
(exponent between ~1.0 and ~1.2 over the reliable band), and its `l̄→∞` limit is
numerically inconclusive. Both are passed as hypotheses (`rateConst`, `exponent`),
so the lemmas commit to neither number.
-/
import Mathlib
import Gtz.LawEquivalence
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Finset

/-! ### The field-blind Stiemke firing engine -/

/-- **Certified transverse firing** (the Stiemke rate input). A nonnegative
covector summing to one that annihilates the active margin rates
(`Σ covector_C · marginRate_C = 0`) forces the firing margin `sup marginRate` to
be at least `covector chosen · (− marginRate chosen)` for every active `chosen`:
you cannot drive one active margin down without some active margin rising by at
least its covector weight times as much.  Field-blind (any ordered field). -/
theorem covector_forces_firing {index : Type*} [DecidableEq index]
    (active : Finset index) (chosen : index) (hchosen : chosen ∈ active)
    (covector marginRate : index → ℝ)
    (hCovectorNonneg : ∀ i ∈ active, 0 ≤ covector i)
    (hCovectorSumOne : ∑ i ∈ active, covector i = 1)
    (hBalance : ∑ i ∈ active, covector i * marginRate i = 0) :
    covector chosen * (- marginRate chosen)
      ≤ active.sup' ⟨chosen, hchosen⟩ marginRate := by
  set firingMargin := active.sup' ⟨chosen, hchosen⟩ marginRate with hfiring
  have hle : ∀ i ∈ active, marginRate i ≤ firingMargin := fun i hi =>
    Finset.le_sup' marginRate hi
  have hfiringNonneg : 0 ≤ firingMargin := by
    have hbound : ∑ i ∈ active, covector i * marginRate i
        ≤ ∑ i ∈ active, covector i * firingMargin := by
      refine Finset.sum_le_sum fun i hi => ?_
      exact mul_le_mul_of_nonneg_left (hle i hi) (hCovectorNonneg i hi)
    have hcollapse : ∑ i ∈ active, covector i * firingMargin = firingMargin := by
      rw [← Finset.sum_mul, hCovectorSumOne, one_mul]
    rw [hcollapse] at hbound
    linarith [hBalance, hbound]
  have hsplit : covector chosen * marginRate chosen
      + ∑ i ∈ active.erase chosen, covector i * marginRate i = 0 :=
    (Finset.add_sum_erase active (fun i => covector i * marginRate i) hchosen).trans
      hBalance
  have herased : ∑ i ∈ active.erase chosen, covector i * marginRate i
      = - (covector chosen * marginRate chosen) := by linarith [hsplit]
  have hboundErased : ∑ i ∈ active.erase chosen, covector i * marginRate i
      ≤ (1 - covector chosen) * firingMargin := by
    have hstep : ∑ i ∈ active.erase chosen, covector i * marginRate i
        ≤ ∑ i ∈ active.erase chosen, covector i * firingMargin := by
      refine Finset.sum_le_sum fun i hi => ?_
      exact mul_le_mul_of_nonneg_left (hle i (Finset.mem_of_mem_erase hi))
        (hCovectorNonneg i (Finset.mem_of_mem_erase hi))
    have hsumErased : ∑ i ∈ active.erase chosen, covector i = 1 - covector chosen := by
      have := Finset.add_sum_erase active covector hchosen
      linarith [hCovectorSumOne, this]
    calc ∑ i ∈ active.erase chosen, covector i * marginRate i
        ≤ ∑ i ∈ active.erase chosen, covector i * firingMargin := hstep
      _ = (∑ i ∈ active.erase chosen, covector i) * firingMargin := by rw [Finset.sum_mul]
      _ = (1 - covector chosen) * firingMargin := by rw [hsumErased]
  have hchosenNonneg : 0 ≤ covector chosen := hCovectorNonneg chosen hchosen
  have hfinal : (1 - covector chosen) * firingMargin ≤ firingMargin := by
    nlinarith [hfiringNonneg, hchosenNonneg]
  calc covector chosen * (- marginRate chosen)
      = - (covector chosen * marginRate chosen) := by ring
    _ = ∑ i ∈ active.erase chosen, covector i * marginRate i := herased.symm
    _ ≤ (1 - covector chosen) * firingMargin := hboundErased
    _ ≤ firingMargin := hfinal

/-- **The transverse-rate reduction** (`ρ ≥ λ_min · σ_min / √N`, per direction).
Given the Stiemke covector (positivity margin `positivityMargin ≤ covector chosen`,
`≤ 1`) and a singular floor at the dominant active index
(`bound ≤ |marginRate chosen|`, read: `σ_min/√N`), the firing margin is at least
`positivityMargin · bound`.  This is the case-split the numerics need: a negative
dominant entry still forces a positive firing via `covector_forces_firing`; a
positive one clears `bound` directly.  Field-blind. -/
theorem firing_margin_ge_of_covector_and_floor {index : Type*} [DecidableEq index]
    (active : Finset index) (chosen : index) (hchosen : chosen ∈ active)
    (covector marginRate : index → ℝ) (positivityMargin bound : ℝ)
    (hCovectorNonneg : ∀ i ∈ active, 0 ≤ covector i)
    (hCovectorSumOne : ∑ i ∈ active, covector i = 1)
    (hBalance : ∑ i ∈ active, covector i * marginRate i = 0)
    (hPosMargin : positivityMargin ≤ covector chosen)
    (hMarginNonneg : 0 ≤ positivityMargin) (hMarginLeOne : positivityMargin ≤ 1)
    (hBoundNonneg : 0 ≤ bound) (hFloor : bound ≤ |marginRate chosen|) :
    positivityMargin * bound ≤ active.sup' ⟨chosen, hchosen⟩ marginRate := by
  set firingMargin := active.sup' ⟨chosen, hchosen⟩ marginRate with hS
  have hfire := covector_forces_firing active chosen hchosen covector marginRate
    hCovectorNonneg hCovectorSumOne hBalance
  rcases le_total (marginRate chosen) 0 with hneg | hpos
  · have habs : |marginRate chosen| = - marginRate chosen := abs_of_nonpos hneg
    have hmrbound : bound ≤ - marginRate chosen := by rw [← habs]; exact hFloor
    have hchosenNonneg : 0 ≤ covector chosen := le_trans hMarginNonneg hPosMargin
    have hprod : positivityMargin * bound ≤ covector chosen * (- marginRate chosen) :=
      mul_le_mul hPosMargin hmrbound hBoundNonneg hchosenNonneg
    linarith [hfire, hprod]
  · have habs : |marginRate chosen| = marginRate chosen := abs_of_nonneg hpos
    have hmrbound : bound ≤ marginRate chosen := by rw [← habs]; exact hFloor
    have hSge : marginRate chosen ≤ firingMargin := Finset.le_sup' marginRate hchosen
    have hpb : positivityMargin * bound ≤ bound := by
      calc positivityMargin * bound ≤ 1 * bound :=
            mul_le_mul_of_nonneg_right hMarginLeOne hBoundNonneg
        _ = bound := one_mul _
    linarith [hSge, hmrbound, hpb]

/-! ### The weight-floor reframe (min-weight controls, not max-leverage) -/

/-- **The weight floor IS the leverage cap**: with leverage cap `l̄ = 1/τ₀` and
weight floor `τ₀ ≤ wmin`, the min weight is at least `1/l̄`.  The abstract
arithmetic behind the reframe — the controlling quantity is `wmin ≥ τ₀ = 1/l̄`,
not `l_max`.  Stated over bare reals; the collar's actual weight floor is the
hypothesis at the call site. -/
theorem minWeight_ge_inv_leverageCap {minWeight weightFloor leverageCap : ℝ}
    (hMin : weightFloor ≤ minWeight) (hCap : leverageCap = 1 / weightFloor) :
    1 / leverageCap ≤ minWeight := by
  rw [hCap, one_div_one_div]; exact hMin

/-- **The collar rate from the weight floor** (exponent one, the bounded-leverage
band).  The measured geometric law `rate ≥ rateConst · minWeight` (the transverse
rate proportional to the minimum weight — exact on the once-split band, the
proportionality constant supplied as the hypothesis `rateConst`, ambient value
`2/(3√7) ≈ 0.252`, W₂-consistent `≈ 0.206`) combines with the collar weight floor
`minWeight ≥ 1/leverageCap` to give the leverage-uniform rate
`rate ≥ rateConst / leverageCap`.  Holds ONLY where the exponent-one
proportionality holds (the bounded-leverage band); it degrades at the near-clone
boundary — see `rate_floor_of_weight_floor_rpow`. -/
theorem rate_floor_of_weight_floor
    {rate rateConst minWeight leverageCap : ℝ}
    (hRateConst : 0 < rateConst)
    (hProportional : rateConst * minWeight ≤ rate)
    (hWeightFloor : 1 / leverageCap ≤ minWeight) :
    rateConst / leverageCap ≤ rate := by
  have hstep : rateConst * (1 / leverageCap) ≤ rateConst * minWeight :=
    mul_le_mul_of_nonneg_left hWeightFloor hRateConst.le
  calc rateConst / leverageCap
      = rateConst * (1 / leverageCap) := by rw [mul_one_div]
    _ ≤ rateConst * minWeight := hstep
    _ ≤ rate := hProportional

/-- **The honest eroded rate** (`ρ(l̄) ≥ rateConst/l̄^α`, real exponent).  At the
heavy near-clone boundary the measured law is `rate ≥ rateConst·wmin^α` with
`α > 1` (the transverse-conditioning erosion — the named open wall), so the collar
rate is `rate ≥ rateConst / leverageCap^α`: positive but super-linearly decaying.
The exponent is a hypothesis; the FIRST-ORDER transverse-rate proxy is `α ≈ 1.46`,
while the actual consumed Łojasiewicz modulus erodes more mildly (`α ∈ [1.0, 1.2]`
over the reliable band, `l̄→∞` limit numerically inconclusive). This lemma commits
to neither number — it is the honest shape the W₂ numerics deliver. -/
theorem rate_floor_of_weight_floor_rpow
    {rate rateConst minWeight leverageCap exponent : ℝ}
    (hRateConst : 0 < rateConst) (hCap : 0 < leverageCap) (hExp : 0 ≤ exponent)
    (hProportional : rateConst * minWeight ^ exponent ≤ rate)
    (hWeightFloor : 1 / leverageCap ≤ minWeight) :
    rateConst / leverageCap ^ exponent ≤ rate := by
  have hinvNonneg : (0 : ℝ) ≤ 1 / leverageCap := by positivity
  have hpow : (1 / leverageCap) ^ exponent ≤ minWeight ^ exponent :=
    Real.rpow_le_rpow hinvNonneg hWeightFloor hExp
  have hrw : (1 / leverageCap) ^ exponent = 1 / leverageCap ^ exponent := by
    rw [Real.div_rpow zero_le_one hCap.le, Real.one_rpow]
  rw [hrw] at hpow
  calc rateConst / leverageCap ^ exponent
      = rateConst * (1 / leverageCap ^ exponent) := by rw [mul_one_div]
    _ ≤ rateConst * minWeight ^ exponent := mul_le_mul_of_nonneg_left hpow hRateConst.le
    _ ≤ rate := hProportional

/-- The collar rate is positive — the tube-rate slot of the two-piece assembly. -/
theorem collar_rate_positive {rateConst leverageCap : ℝ}
    (hRateConst : 0 < rateConst) (hLeverageCap : 0 < leverageCap) :
    0 < rateConst / leverageCap := by positivity

/-! ### Feeding the rate into the two-piece law + the off-tube gap -/

/-- **The collared two-piece law fires** (the one genuine kernel consumption).
The positive collar rate `rateConst/leverageCap` (any bounded-leverage cell) as
the tube rate, plus an off-tube gap and domain cap, assembles the global linear
funneling law with the explicit leverage-uniform constant
`min (rateConst/leverageCap) (offGap/domainCap)` — directly instantiating the
kernel `two_piece_law_assembly` (`Gtz.LawEquivalence`).  This is residual 4's
assembly with the tube modulus now a positive rate (itself conditional on the
open rate law). -/
theorem collared_two_piece_law
    {phi dist rateConst leverageCap tubeRadius offGap domainCap : ℝ}
    (hRateConst : 0 < rateConst) (hCap : 0 < leverageCap)
    (hoffGap : 0 < offGap) (hdomainCap : 0 < domainCap)
    (hdist : 0 ≤ dist) (hdomain : dist ≤ domainCap)
    (htube : dist ≤ tubeRadius → (rateConst / leverageCap) * dist ≤ phi)
    (hoff : tubeRadius ≤ dist → offGap ≤ phi) :
    min (rateConst / leverageCap) (offGap / domainCap) * dist ≤ phi :=
  two_piece_law_assembly (collar_rate_positive hRateConst hCap) hoffGap hdomainCap
    hdist hdomain htube hoff

/-- **The off-tube gap exists by compactness** (residual 4's second quantitative
input).  A continuous margin `phi`, strictly positive on a compact off-tube
region, attains a positive minimum there — the `offGap` the two-piece law needs.
Stated ABSTRACTLY over any compact carrier: `hCompact` is a hypothesis, NOT the
kernel `Gtz.isCompact_collaredSet` (which this lemma is designed to accept at the
call site, without importing or hardwiring it). -/
theorem offTubeGap_pos {carrier : Type*} [TopologicalSpace carrier]
    {offTube : Set carrier} (hCompact : IsCompact offTube) (hNe : offTube.Nonempty)
    {phi : carrier → ℝ} (hCont : ContinuousOn phi offTube)
    (hPos : ∀ point ∈ offTube, 0 < phi point) :
    ∃ offGap > 0, ∀ point ∈ offTube, offGap ≤ phi point := by
  obtain ⟨minimizer, hmem, hmin⟩ := hCompact.exists_isMinOn hNe hCont
  refine ⟨phi minimizer, hPos minimizer hmem, fun point hp => ?_⟩
  exact isMinOn_iff.mp hmin point hp

/-! ### The decay of the collar rate (residual 7's wall, quantified) -/

/-- **The collar rate DECAYS with leverage** — the honest shape of residual 7's
wall. For a fixed nonnegative proportionality constant and nonnegative exponent, the
guaranteed rate floor `rateConst/leverageCap^exponent` is ANTITONE in the leverage
cap: a higher-leverage cell has a strictly weaker guaranteed transverse rate. This is
exactly why the collar rate is not `l̄`-uniform — the named open wall is a leverage-
uniform continuum lower bound that this monotone decay forbids for any positive
exponent. Real field (rpow monotonicity). -/
theorem rate_floor_antitone_in_leverage
    {rateConst exponent leverageCap1 leverageCap2 : ℝ}
    (hRateConst : 0 ≤ rateConst) (hExp : 0 ≤ exponent)
    (hCap1 : 0 < leverageCap1) (hMono : leverageCap1 ≤ leverageCap2) :
    rateConst / leverageCap2 ^ exponent ≤ rateConst / leverageCap1 ^ exponent := by
  have hCap2 : 0 < leverageCap2 := lt_of_lt_of_le hCap1 hMono
  have hpow : leverageCap1 ^ exponent ≤ leverageCap2 ^ exponent :=
    Real.rpow_le_rpow hCap1.le hMono hExp
  have hpow1pos : 0 < leverageCap1 ^ exponent := Real.rpow_pos_of_pos hCap1 exponent
  exact div_le_div_of_nonneg_left hRateConst hpow1pos hpow

/-- **Adversarial erosion witness — the sample→consumption rate drop, exact.** At the
mild band exponent `1` with the W₂-consistent proportionality constant `≈ 0.206`
(`206/1000`), the guaranteed rate floor at the CONSUMPTION leverage `l̄ = 300` times
`12` equals the floor at the SAMPLE leverage `l̄ = 25` — a `12×` erosion, kernel-
checked as an exact rational identity. The honest magnitude of residual 7's gap: what
the numerics measure at `l̄ ≤ 25` is diluted twelve-fold before it is consumed at
`l̄ ≈ 300`, even at the MOST favorable measured exponent. No external engine. -/
theorem collar_erosion_ratio_exponent_one :
    ((206 / 1000 : ℝ) / 300) * 12 = (206 / 1000 : ℝ) / 25 := by norm_num

/-- The erosion is strict: the consumption-leverage rate floor sits strictly below the
sample-leverage floor (exact rational, adversarial cross-check). -/
theorem collar_erosion_strict :
    (206 / 1000 : ℝ) / 300 < (206 / 1000 : ℝ) / 25 := by norm_num

end Gtz
