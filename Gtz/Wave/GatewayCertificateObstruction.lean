/-
# The gateway target admits NO certificate of Handelman type, at any degree

`E1` — "some outside pair of a corner is admissible" — was reduced by this lane
to one polynomial target on a six-scalar box: with `a_i` the weighted leverage
excesses and `t_i` the outside weights,

  **target:  `a_1 + a_2 + a_3 <= 1`**

under the generators `a_i, t_i, A_i = 1 - t_i, c_i = A_i - a_i`, the weight
slack `S = 1 - t_1 - t_2 - t_3`, the three pair slacks, the three arithmetic
mean bounds, and the two determinants `Gtz.branchDetComplement` and
`Gtz.branchDetOutside`.

FIVE ROUNDS OF THIS CAMPAIGN RAN LINEAR PROGRAMS FOR THAT CERTIFICATE AND FOUND
INFEASIBILITY AT EVERY DEGREE THEY REACHED.  This module explains why, and the
explanation is not a degree bound: **no such certificate exists at any degree.**

## The tight family

Section 2 exhibits a TWO-PARAMETER family of box points at which the target
holds with EQUALITY while the weight slack stays strictly positive:

  `t = (0, t_2, t_3)` ,  `a = (1 - (t_2+t_3)/2, t_3/2, t_2/2)` .

Both determinants vanish identically on it (`Gtz.gatewayFamily_detComplement_zero`,
`Gtz.gatewayFamily_detOutside_zero`), the excesses total exactly one
(`Gtz.gatewayFamily_excess_sum`), and the three pair slacks are
`t_2 S / 2`, `t_3 S / 2` and `S (2 - t_2 - t_3) / 2` — all STRICTLY POSITIVE
(`Gtz.gatewayFamily_pairSlack_first` and its siblings).  So the family is deep
inside the pair polytope, not on its boundary.

Two recorded conjectures die here.  A bound `1 - sum a >= c * S` is FALSE for
every positive `c`, because the family has `1 - sum a = 0` at every value of
`S` in `(0,1)`.  And the emptiness question
`{detIM >= 0, detM >= 0, pair, sum t <= 1 - tau, sum a >= 1}` is NOT empty for
any `tau` in `(0,1)`, because the family sits inside it.

## The obstruction, and why it is degree-free

Section 1 proves a general lemma that any lane can reuse
(`Gtz.certValue_eq_zero_of_obstruction`).  Take two points of a system.  At the
first, every generator outside a set `Z` is strictly positive and the target
vanishes.  Then every monomial of a nonnegative certificate must carry a factor
from `Z`.  At the second, every generator of `Z` vanishes, so the whole
certificate vanishes there.  A target that is NOT zero at the second point
therefore has no certificate — at ANY degree, with ANY finite set of monomials.

Section 3 supplies the two points, in exact rationals, sharing one weight
vector `t = (0, 3/10, 1/4)`:

* `W1 = (29/40, 1/8, 3/20)` — on the family.  `sum a = 1`, both determinants
  zero, and every other generator strictly positive.  So `Z = {t_1, detIM, detM}`.
* `W2 = (0, 7/20, 3/8)` — the normalized excesses are `(0, 1/2, 1/2)`.  Both
  determinants vanish again, and `t_1` is again zero, but `sum a = 29/40`, so
  the target is `11/40`, not zero.

`Gtz.gateway_no_handelman_certificate` is the conclusion.

## What the lane must do instead

`W1` and `W2` both have `t_1 = 0`, and no design has a zero weight.  The box
discards the strict positivity of the outside weights, and that is exactly the
information the certificate needs.  Any further attempt must carry a WEIGHT
FLOOR `t_i >= tau` into the generator set — with it, `W1` and `W2` both leave
the system and this obstruction disappears.

[MEASURED, and every measurement below was then replaced by an exact statement.
Three million refined samples of the box system never produced `sum a > 1`; the
maximiser always drove `min t` to zero.  The tight system `{sum a = 1,
detIM = 0, detM = 0}` was solved EXACTLY at four rational weight vectors with
all weights positive: two complex roots and one root with negative components
each time, so the family really does live only on `t_1 t_2 t_3 = 0`.  A degree
four linear program over an enriched generator set of eighteen generators — the
set above, which no earlier round used — is decisively infeasible, which
corrects an earlier round's "numerically inconclusive" reading at that degree.]
-/
import Gtz.Wave.CornerEmptinessSlack

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Finset

/-! ## 1. A two-point obstruction to certificates of Handelman type

A certificate is a finite nonnegative combination of MONOMIALS in the
generators.  The lemma is stated for an arbitrary generator count, and it uses
no property of the system it is applied to. -/

/-- The value of a certificate: a finite set of exponent vectors, each carrying
a coefficient, read against a vector of generator values. -/
noncomputable def certValue {n : ℕ} (gen : Fin n → ℝ)
    (support : Finset (Fin n → ℕ)) (coef : (Fin n → ℕ) → ℝ) : ℝ :=
  ∑ e ∈ support, coef e * ∏ i, gen i ^ e i

/-- Each monomial of a certificate is nonnegative where the generators are. -/
theorem certTerm_nonneg {n : ℕ} {gen : Fin n → ℝ} (hgen : ∀ i, 0 ≤ gen i)
    {coef : (Fin n → ℕ) → ℝ} {e : Fin n → ℕ} (hc : 0 ≤ coef e) :
    0 ≤ coef e * ∏ i, gen i ^ e i :=
  mul_nonneg hc (Finset.prod_nonneg fun i _ => pow_nonneg (hgen i) _)

/-- **THE TWO-POINT OBSTRUCTION.**  If a certificate vanishes at a point where
every generator outside `Z` is strictly positive, then every monomial it carries
has a factor in `Z`, so the certificate vanishes at every point where `Z`
vanishes.  No degree bound and no finiteness assumption beyond the support. -/
theorem certValue_eq_zero_of_obstruction {n : ℕ} {Z : Finset (Fin n)}
    {gen₁ gen₂ : Fin n → ℝ}
    (h₁nonneg : ∀ i, 0 ≤ gen₁ i) (h₁pos : ∀ i, i ∉ Z → 0 < gen₁ i)
    (h₂zero : ∀ i ∈ Z, gen₂ i = 0)
    {support : Finset (Fin n → ℕ)} {coef : (Fin n → ℕ) → ℝ}
    (hcoef : ∀ e ∈ support, 0 ≤ coef e)
    (hvanish : certValue gen₁ support coef = 0) :
    certValue gen₂ support coef = 0 := by
  classical
  have hterm : ∀ e ∈ support, coef e * ∏ i, gen₁ i ^ e i = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hvanish
    exact fun e he => certTerm_nonneg h₁nonneg (hcoef e he)
  refine Finset.sum_eq_zero fun e he => ?_
  rcases eq_or_lt_of_le (hcoef e he) with hzero | hpos
  · rw [← hzero, zero_mul]
  · have hprod : (∏ i, gen₁ i ^ e i) = 0 := by
      rcases mul_eq_zero.mp (hterm e he) with h | h
      · exact absurd h (ne_of_gt hpos)
      · exact h
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hprod
    have hbase : gen₁ i = 0 := by
      by_contra hne
      exact absurd hi (pow_ne_zero _ hne)
    have hmem : i ∈ Z := by
      by_contra hnot
      exact absurd hbase (ne_of_gt (h₁pos i hnot))
    have hexp : e i ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hi
      exact one_ne_zero hi
    have : (∏ i, gen₂ i ^ e i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h₂zero i hmem, zero_pow hexp])
    rw [this, mul_zero]

/-! ## 2. The tight family of the box

Every statement here is one `ring` after unfolding. -/

/-- The pair slack of the box, in the excess and weight coordinates: the pair
constraint of the gateway is that this is not negative. -/
noncomputable def gatewayPairSlack (ai aj ti tj : ℝ) : ℝ :=
  (1 - ti) * (1 - tj) - ai * (1 - tj) - aj * (1 - ti)

/-- The first excess of the tight family. -/
noncomputable def gatewayFamilyFirst (t2 t3 : ℝ) : ℝ := 1 - (t2 + t3) / 2

/-- **THE COMPLEMENT DETERMINANT VANISHES ON THE FAMILY.** -/
theorem gatewayFamily_detComplement_zero (t2 t3 : ℝ) :
    branchDetComplement (gatewayFamilyFirst t2 t3) (t3 / 2) (t2 / 2) 0 t2 t3 = 0 := by
  unfold branchDetComplement gatewayFamilyFirst; ring

/-- **THE OUTSIDE DETERMINANT VANISHES ON THE FAMILY.** -/
theorem gatewayFamily_detOutside_zero (t2 t3 : ℝ) :
    branchDetOutside (gatewayFamilyFirst t2 t3) (t3 / 2) (t2 / 2) 0 t2 t3 = 0 := by
  unfold branchDetOutside gatewayFamilyFirst; ring

/-- **THE TARGET IS TIGHT ON THE FAMILY.**  The three excesses total exactly
one, for every pair of weights. -/
theorem gatewayFamily_excess_sum (t2 t3 : ℝ) :
    gatewayFamilyFirst t2 t3 + t3 / 2 + t2 / 2 = 1 := by
  unfold gatewayFamilyFirst; ring

/-- The weight slack of the family is whatever the two live weights leave. -/
theorem gatewayFamily_slack (t2 t3 : ℝ) :
    branchSlack 0 t2 t3 = 1 - t2 - t3 := by
  unfold branchSlack; ring

/-- The first pair slack of the family is the first live weight against the
weight slack, halved. -/
theorem gatewayFamily_pairSlack_first (t2 t3 : ℝ) :
    gatewayPairSlack (gatewayFamilyFirst t2 t3) (t3 / 2) 0 t2
      = t2 * (1 - t2 - t3) / 2 := by
  unfold gatewayPairSlack gatewayFamilyFirst; ring

/-- The second pair slack of the family. -/
theorem gatewayFamily_pairSlack_second (t2 t3 : ℝ) :
    gatewayPairSlack (gatewayFamilyFirst t2 t3) (t2 / 2) 0 t3
      = t3 * (1 - t2 - t3) / 2 := by
  unfold gatewayPairSlack gatewayFamilyFirst; ring

/-- The third pair slack of the family, between the two live atoms. -/
theorem gatewayFamily_pairSlack_third (t2 t3 : ℝ) :
    gatewayPairSlack (t3 / 2) (t2 / 2) t2 t3
      = (1 - t2 - t3) * (2 - t2 - t3) / 2 := by
  unfold gatewayPairSlack; ring

/-- **THE FAMILY IS DEEP INSIDE THE PAIR POLYTOPE.**  With two live weights in
the open unit interval and a positive weight slack, all three pair slacks are
strictly positive.  So the family is not a boundary artifact of the pair
constraints. -/
theorem gatewayFamily_pairSlack_pos {t2 t3 : ℝ} (h2 : 0 < t2) (h3 : 0 < t3)
    (hS : 0 < 1 - t2 - t3) :
    0 < gatewayPairSlack (gatewayFamilyFirst t2 t3) (t3 / 2) 0 t2
      ∧ 0 < gatewayPairSlack (gatewayFamilyFirst t2 t3) (t2 / 2) 0 t3
      ∧ 0 < gatewayPairSlack (t3 / 2) (t2 / 2) t2 t3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gatewayFamily_pairSlack_first]; positivity
  · rw [gatewayFamily_pairSlack_second]; positivity
  · rw [gatewayFamily_pairSlack_third]
    have : 0 < 2 - t2 - t3 := by linarith
    positivity

/-- **NO SLACK BOUND.**  A bound `1 - sum a >= c * S` fails for every positive
`c`, because the family holds the target at equality while the weight slack
ranges over the whole open unit interval. -/
theorem gatewayFamily_no_slack_bound {c : ℝ} (hc : 0 < c) :
    ∃ a1 a2 a3 t1 t2 t3 : ℝ,
      branchDetComplement a1 a2 a3 t1 t2 t3 = 0
        ∧ branchDetOutside a1 a2 a3 t1 t2 t3 = 0
        ∧ a1 + a2 + a3 = 1
        ∧ 0 < branchSlack t1 t2 t3
        ∧ ¬ (c * branchSlack t1 t2 t3 ≤ 1 - (a1 + a2 + a3)) := by
  refine ⟨gatewayFamilyFirst (1/4) (1/4), (1/4)/2, (1/4)/2, 0, 1/4, 1/4, ?_, ?_, ?_, ?_, ?_⟩
  · exact gatewayFamily_detComplement_zero (1/4) (1/4)
  · exact gatewayFamily_detOutside_zero (1/4) (1/4)
  · exact gatewayFamily_excess_sum (1/4) (1/4)
  · rw [gatewayFamily_slack]; norm_num
  · rw [gatewayFamily_slack, gatewayFamily_excess_sum]
    intro hle
    norm_num at hle
    linarith

/-! ## 3. The two witnesses, and the impossibility

Both witnesses carry the same weight vector `t = (0, 3/10, 1/4)`.  The generator
order is
`a₁ a₂ a₃ t₁ t₂ t₃ A₁ A₂ A₃ c₁ c₂ c₃ S p₁₂ p₁₃ p₂₃ m₁₂ m₁₃ m₂₃ detIM detM`,
with `c_i = A_i - a_i` the weight cap slack and `m_ij = A_iA_j - 4a_ia_j` the
arithmetic mean bound that the pair constraint implies but no PRODUCT of the
generators does. -/

/-- The generator values at the family witness. -/
noncomputable def gatewayGenW1 : Fin 21 → ℝ :=
  ![29/40, 1/8, 3/20, 0, 3/10, 1/4, 1, 7/10, 3/4, 11/40, 23/40, 3/5, 9/20,
    27/400, 9/160, 261/800, 27/80, 63/200, 9/20, 0, 0]

/-- The generator values at the second witness. -/
noncomputable def gatewayGenW2 : Fin 21 → ℝ :=
  ![0, 7/20, 3/8, 0, 3/10, 1/4, 1, 7/10, 3/4, 1, 7/20, 3/8, 9/20,
    7/20, 3/8, 0, 7/10, 3/4, 0, 0, 0]

/-- The generators that vanish at the family witness: the first weight and the
two determinants. -/
def gatewayZero : Finset (Fin 21) := {3, 19, 20}

/-- The family witness really is a point of the box: its determinants vanish. -/
theorem gatewayW1_detComplement :
    branchDetComplement (29/40) (1/8) (3/20) 0 (3/10) (1/4) = 0 := by
  unfold branchDetComplement; norm_num

theorem gatewayW1_detOutside :
    branchDetOutside (29/40) (1/8) (3/20) 0 (3/10) (1/4) = 0 := by
  unfold branchDetOutside; norm_num

/-- The second witness is a point of the box too. -/
theorem gatewayW2_detComplement :
    branchDetComplement 0 (7/20) (3/8) 0 (3/10) (1/4) = 0 := by
  unfold branchDetComplement; norm_num

theorem gatewayW2_detOutside :
    branchDetOutside 0 (7/20) (3/8) 0 (3/10) (1/4) = 0 := by
  unfold branchDetOutside; norm_num

/-- The target vanishes at the family witness. -/
theorem gatewayW1_target : 1 - ((29/40 : ℝ) + 1/8 + 3/20) = 0 := by norm_num

/-- The target is strictly positive at the second witness. -/
theorem gatewayW2_target : 1 - ((0 : ℝ) + 7/20 + 3/8) = 11/40 := by norm_num

theorem gatewayGenW1_nonneg (i : Fin 21) : 0 ≤ gatewayGenW1 i := by
  fin_cases i <;> norm_num [gatewayGenW1]

theorem gatewayGenW2_nonneg (i : Fin 21) : 0 ≤ gatewayGenW2 i := by
  fin_cases i <;> norm_num [gatewayGenW2]

/-- **EVERY OTHER GENERATOR IS STRICTLY POSITIVE AT THE FAMILY WITNESS.**  That
is what forces every monomial of a certificate to carry the first weight or one
of the two determinants. -/
theorem gatewayGenW1_pos_of_not_mem (i : Fin 21) (hi : i ∉ gatewayZero) :
    0 < gatewayGenW1 i := by
  fin_cases i <;>
    first
      | exact absurd (by decide : (_ : Fin 21) ∈ gatewayZero) hi
      | norm_num [gatewayGenW1]

/-- The three generators vanish at the second witness. -/
theorem gatewayGenW2_zero_of_mem (i : Fin 21) (hi : i ∈ gatewayZero) :
    gatewayGenW2 i = 0 := by
  fin_cases i <;>
    first
      | exact absurd hi (by decide)
      | norm_num [gatewayGenW2]

/-- **THE GATEWAY TARGET HAS NO CERTIFICATE OF HANDELMAN TYPE.**  For every
finite support and every nonnegative coefficient vector, a certificate that
reads zero at the family witness reads zero at the second witness — where the
target is `11/40`.  No degree bound appears, so no amount of degree buys the
certificate.

This is the structural reason five rounds of linear programs in this lane
returned infeasible.  The repair is a weight floor: both witnesses have a zero
weight, and no design does. -/
theorem gateway_no_handelman_certificate
    (support : Finset (Fin 21 → ℕ)) (coef : (Fin 21 → ℕ) → ℝ)
    (hcoef : ∀ e ∈ support, 0 ≤ coef e)
    (hW1 : certValue gatewayGenW1 support coef = 1 - ((29/40 : ℝ) + 1/8 + 3/20)) :
    certValue gatewayGenW2 support coef ≠ 1 - ((0 : ℝ) + 7/20 + 3/8) := by
  rw [gatewayW1_target] at hW1
  rw [gatewayW2_target]
  rw [certValue_eq_zero_of_obstruction (Z := gatewayZero) gatewayGenW1_nonneg
    gatewayGenW1_pos_of_not_mem gatewayGenW2_zero_of_mem hcoef hW1]
  norm_num

end Gtz
