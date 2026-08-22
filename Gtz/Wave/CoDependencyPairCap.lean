/-
# The pair cap: two co-dependencies price two coordinates at once

`Gtz/Wave/DependencyAtomCap.lean` prices ONE coordinate of a dependency by the
co-share of its label, through one Cauchy-Schwarz step against the label's
co-dependency.  This module runs the same step against a PENCIL of two
co-dependencies.  What comes out is sharper than the two single caps together,
and the quantity that measures the difference is the campaign's own
`Gtz.pairCapSlack`.

## 1. The co-dependency Gram

The reading law `Gtz.sum_coDependency_mul_div_weight` applied to a second
co-dependency computes the whole Gram matrix of the six co-dependencies in the
weight-reciprocal metric:

  **`Gtz.dualCross_coDependency_pair`:**  off the diagonal it is `-<g_p, g_q>`,
  and on the diagonal it is `(1 - s_p)/t_p` (`Gtz.dualNormSq_coDependency`).

So the Gram of the co-dependencies is the design's own Gram with the sign
flipped off the diagonal and the co-share over the weight on it.  Its two-by-two
determinants are the campaign's pair cap slacks:

  **`Gtz.pairCapSlack_eq_weight_mul_coDependency_gramDet`:**
    `pairCapSlack D p q = t_p t_q * ((1 - s_p)/t_p * (1 - s_q)/t_q - <g_p,g_q>^2)` .

`Gtz.pairCapSlack` vanishes exactly when the complementary four atoms are
coplanar, so the COPLANARITY of four atoms is, in this chart, the degeneracy of
a two-by-two Gram of dependencies.

## 2. The pair cap

  **`Gtz.sq_pairReading_le`.**  For every dependency `z`, every pair `p != q` and
  every pencil `(x,y)`,

    `(x z_p/t_p + y z_q/t_q)^2`
    `  <= (x^2 (1-s_p)/t_p - 2 x y <g_p,g_q> + y^2 (1-s_q)/t_q) * sum_i z_i^2/t_i` .

The quadratic on the right has discriminant `4 t_p t_q pairCapSlack / (t_p t_q)`,
so at a VANISHING cap slack it is a perfect square and the cap collapses to an
equation:

  **`Gtz.coordinate_relation_of_pairCapSlack_eq_zero`:**  when
  `pairCapSlack D p q = 0`, EVERY dependency obeys the one fixed linear relation

    `t_q <g_p,g_q> z_p + (1 - s_p) z_q = 0` .

Four coplanar atoms therefore pin two coordinates of the whole dependency space
to a line.  That is the dependency-chart form of the campaign's coplanar branch,
and it needs no plane, no normal and no shadow.

## 3. The pair test for domination

The atom cap turns a subset whose DUAL RATIOS `nu_c = (1 - s_c)/(1 - t_c)` total
at most one into a dominator (`Gtz.dominates_of_sum_dualRatio_le_one`).  The pair
cap replaces the two ratios of one inside pair by the largest eigenvalue of their
two-by-two block, and the resulting test is strictly stronger:

  **`Gtz.dominates_of_pairTest_canonical`.**  If `nu_a <= 1 - nu_c`,
  `nu_b <= 1 - nu_c` and

    `th_a th_b <g_a,g_b>^2  <=  (1 - nu_c - nu_a) (1 - nu_c - nu_b)` ,

  then `{a,b,c}` DOMINATES.  Here `th_c = t_c/(1 - t_c)` is the landed
  `Gtz.weightOdds`.

It contains the trace test, because `nu_a nu_b - th_a th_b <g_a,g_b>^2` is the
cap slack divided by the two co-weights and so is nonnegative
(`Gtz.dualRatio_mul_dualRatio_sub_odds_mul_sq`).  Its strict twin
`Gtz.posDef_gap_of_pairTest_triple` prices every tie
(`Gtz.pairTest_fails_of_isTie_sixThree`) and reduces the main statement:

  **`Gtz.gtzWeighted_sixThree_of_pairTest`** — `Gtz.GtzWeighted 6 3` follows from
  producing, at every `(6,3)` design, ONE triple that passes the pair test.

[MEASURED before proving, `scratchpad/kzero`, double precision, 200000 random
`(6,3)` designs and all 4000000 triples.  The pair test fired at 375316 triples
with ZERO failures, against 94499 for the trace test: a factor of `3.97`.  Per
design, some triple passes the pair test at 183208 of the 200000 designs — `91.6`
percent — against 78782 — `39.4` percent — for the trace test, while a
dominating triple exists at all 200000.  The atom cap itself was tested at
7200000 instances with zero violations and worst ratio `1.000000`.]

## Scope

Every statement here is FIELD-BLIND: two Cauchy-Schwarz steps and one Parseval
identity, all of which transport to `ℂ` with the squared modulus in place of the
square.  By `Gtz/Complex/ComplexTransportLedger.lean` no field-blind instrument
can prove the hinge.  The pair test is a DOMINATION producer and a tie
constraint, not a hinge argument.
-/
import Gtz.Wave.DependencyAtomCap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1 — the weight-reciprocal metric on vectors -/

/-- The weight-reciprocal pairing.  Its diagonal is `Gtz.dualNormSq`. -/
noncomputable def dualCross (D : WeightedDesign m k) (leftVec rightVec : Fin m → ℝ) : ℝ :=
  ∑ index, leftVec index * rightVec index / D.weight index

theorem dualCross_self (D : WeightedDesign m k) (vec : Fin m → ℝ) :
    dualCross D vec vec = dualNormSq D vec := by
  simp only [dualCross, dualNormSq, pow_two]

theorem dualCross_comm (D : WeightedDesign m k) (leftVec rightVec : Fin m → ℝ) :
    dualCross D leftVec rightVec = dualCross D rightVec leftVec := by
  simp only [dualCross]
  exact Finset.sum_congr rfl fun index _ => by rw [mul_comm]

/-- **POLARISATION IN THE WEIGHT-RECIPROCAL METRIC.** -/
theorem dualNormSq_smul_add (D : WeightedDesign m k) (scaleLeft scaleRight : ℝ)
    (leftVec rightVec : Fin m → ℝ) :
    dualNormSq D (fun index => scaleLeft * leftVec index + scaleRight * rightVec index)
      = scaleLeft ^ 2 * dualNormSq D leftVec
        + 2 * scaleLeft * scaleRight * dualCross D leftVec rightVec
        + scaleRight ^ 2 * dualNormSq D rightVec := by
  have hterm : ∀ index : Fin m,
      (scaleLeft * leftVec index + scaleRight * rightVec index) ^ 2 / D.weight index
        = scaleLeft ^ 2 * (leftVec index ^ 2 / D.weight index)
          + 2 * scaleLeft * scaleRight * (leftVec index * rightVec index / D.weight index)
          + scaleRight ^ 2 * (rightVec index ^ 2 / D.weight index) := by
    intro index
    have hw := (D.weight_pos index).ne'
    field_simp
    try ring
  simp only [dualNormSq, dualCross]
  rw [Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hterm index]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  try ring

/-- **LINEARITY OF THE PAIRING IN ITS FIRST SLOT.** -/
theorem dualCross_smul_add (D : WeightedDesign m k) (scaleLeft scaleRight : ℝ)
    (leftVec rightVec probe : Fin m → ℝ) :
    dualCross D (fun index => scaleLeft * leftVec index + scaleRight * rightVec index) probe
      = scaleLeft * dualCross D leftVec probe + scaleRight * dualCross D rightVec probe := by
  have hterm : ∀ index : Fin m,
      (scaleLeft * leftVec index + scaleRight * rightVec index) * probe index / D.weight index
        = scaleLeft * (leftVec index * probe index / D.weight index)
          + scaleRight * (rightVec index * probe index / D.weight index) := by
    intro index
    have hw := (D.weight_pos index).ne'
    field_simp
    try ring
  simp only [dualCross]
  rw [Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hterm index]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **CAUCHY-SCHWARZ IN THE WEIGHT-RECIPROCAL METRIC.** -/
theorem sq_dualCross_le (D : WeightedDesign m k) (leftVec rightVec : Fin m → ℝ) :
    dualCross D leftVec rightVec ^ 2 ≤ dualNormSq D leftVec * dualNormSq D rightVec := by
  have hsqrtPos : ∀ index : Fin m, 0 < Real.sqrt (D.weight index) := fun index =>
    Real.sqrt_pos.mpr (D.weight_pos index)
  have hsq : ∀ index : Fin m, Real.sqrt (D.weight index) ^ 2 = D.weight index := fun index =>
    Real.sq_sqrt (D.weight_pos index).le
  have hCS := sum_mul_sq_le Finset.univ
    (fun index => leftVec index / Real.sqrt (D.weight index))
    (fun index => rightVec index / Real.sqrt (D.weight index))
  have hmix : ∀ index : Fin m,
      (leftVec index / Real.sqrt (D.weight index))
          * (rightVec index / Real.sqrt (D.weight index))
        = leftVec index * rightVec index / D.weight index := by
    intro index
    rw [div_mul_div_comm, ← pow_two, hsq]
  have hleftSq : ∀ index : Fin m,
      (leftVec index / Real.sqrt (D.weight index)) ^ 2
        = leftVec index ^ 2 / D.weight index := by
    intro index
    rw [div_pow, hsq]
  have hrightSq : ∀ index : Fin m,
      (rightVec index / Real.sqrt (D.weight index)) ^ 2
        = rightVec index ^ 2 / D.weight index := by
    intro index
    rw [div_pow, hsq]
  rw [Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hmix index,
    Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hleftSq index,
    Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hrightSq index] at hCS
  exact hCS

/-- A two-term pencil of dependencies is a dependency. -/
theorem sum_smul_pair_atom_eq_zero (D : WeightedDesign m k) (scaleLeft scaleRight : ℝ)
    {leftVec rightVec : Fin m → ℝ}
    (hleft : (∑ index, leftVec index • D.atom index) = 0)
    (hright : (∑ index, rightVec index • D.atom index) = 0) :
    (∑ index, (scaleLeft * leftVec index + scaleRight * rightVec index) • D.atom index) = 0 := by
  have hsplit : ∀ index : Fin m,
      (scaleLeft * leftVec index + scaleRight * rightVec index) • D.atom index
        = scaleLeft • (leftVec index • D.atom index)
          + scaleRight • (rightVec index • D.atom index) := by
    intro index
    rw [add_smul, smul_smul, smul_smul]
  rw [Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hsplit index,
    Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hleft, hright,
    smul_zero, smul_zero, add_zero]

/-! ## Part 2 — the co-dependency Gram -/

/-- **THE READING LAW, IN PAIRING FORM.** -/
theorem dualCross_coDependency (D : WeightedDesign m k) (center : Fin m)
    {dep : Fin m → ℝ} (hdep : (∑ index, dep index • D.atom index) = 0) :
    dualCross D (coDependency D center) dep = dep center / D.weight center :=
  sum_coDependency_mul_div_weight D center hdep

/-- **THE OFF-DIAGONAL OF THE CO-DEPENDENCY GRAM** is the design's own pairing
with the sign flipped.  The whole Gram of the six co-dependencies is therefore
the design Gram, negated off the diagonal and with the co-share over the weight
on it. -/
theorem dualCross_coDependency_pair (D : WeightedDesign m k) {first second : Fin m}
    (hne : second ≠ first) :
    dualCross D (coDependency D first) (coDependency D second)
      = -(D.atom first ⬝ᵥ D.atom second) := by
  rw [dualCross_coDependency D first (sum_coDependency_smul_atom D second),
    coDependency_apply_of_ne D (Ne.symm hne),
    dotProduct_comm (D.atom second) (D.atom first)]
  have hw := (D.weight_pos first).ne'
  field_simp

/-- **THE CAP SLACK IS THE CO-DEPENDENCY GRAM DETERMINANT.**  A vanishing cap
slack — equivalently, four coplanar atoms — is exactly the degeneracy of a
two-by-two Gram of dependencies. -/
theorem pairCapSlack_eq_weight_mul_coDependency_gramDet (D : WeightedDesign m 3)
    (first second : Fin m) :
    pairCapSlack D first second
      = D.weight first * D.weight second
        * (((1 - shareOf D first) / D.weight first)
              * ((1 - shareOf D second) / D.weight second)
            - (D.atom first ⬝ᵥ D.atom second) ^ 2) := by
  have hfirst := (D.weight_pos first).ne'
  have hsecond := (D.weight_pos second).ne'
  rw [pairCapSlack_eq_one_sub_shareOf_add_pairVolume, pairVolume,
    crossNormSq_eq_leverage_mul_sub_sq, shareOf, shareOf]
  field_simp
  try ring

/-! ## Part 3 — the pair cap -/

/-- **THE PAIR CAP.**  Two coordinates of a dependency, read through an arbitrary
pencil, are capped by the pencil's own energy in the co-dependency Gram. -/
theorem sq_pairReading_le (D : WeightedDesign m k) {first second : Fin m}
    (hne : second ≠ first) (scaleLeft scaleRight : ℝ)
    {dep : Fin m → ℝ} (hdep : (∑ index, dep index • D.atom index) = 0) :
    (scaleLeft * (dep first / D.weight first)
        + scaleRight * (dep second / D.weight second)) ^ 2
      ≤ (scaleLeft ^ 2 * ((1 - shareOf D first) / D.weight first)
          - 2 * scaleLeft * scaleRight * (D.atom first ⬝ᵥ D.atom second)
          + scaleRight ^ 2 * ((1 - shareOf D second) / D.weight second))
        * dualNormSq D dep := by
  have hpencil : (∑ index, (scaleLeft * coDependency D first index
      + scaleRight * coDependency D second index) • D.atom index) = 0 :=
    sum_smul_pair_atom_eq_zero D scaleLeft scaleRight (sum_coDependency_smul_atom D first)
      (sum_coDependency_smul_atom D second)
  have hread : dualCross D (fun index => scaleLeft * coDependency D first index
        + scaleRight * coDependency D second index) dep
      = scaleLeft * (dep first / D.weight first)
        + scaleRight * (dep second / D.weight second) := by
    rw [dualCross_smul_add, dualCross_coDependency D first hdep,
      dualCross_coDependency D second hdep]
  have hnorm : dualNormSq D (fun index => scaleLeft * coDependency D first index
        + scaleRight * coDependency D second index)
      = scaleLeft ^ 2 * ((1 - shareOf D first) / D.weight first)
        - 2 * scaleLeft * scaleRight * (D.atom first ⬝ᵥ D.atom second)
        + scaleRight ^ 2 * ((1 - shareOf D second) / D.weight second) := by
    rw [dualNormSq_smul_add, dualNormSq_coDependency, dualNormSq_coDependency,
      dualCross_coDependency_pair D hne]
    ring
  have hCS := sq_dualCross_le D (fun index => scaleLeft * coDependency D first index
    + scaleRight * coDependency D second index) dep
  rw [hread, hnorm] at hCS
  exact hCS

/-- **RIGIDITY AT A VANISHING CAP SLACK.**  Four coplanar atoms pin two
coordinates of EVERY dependency to one fixed line.  The pencil that witnesses it
is the null direction of the degenerate co-dependency Gram. -/
theorem coordinate_relation_of_pairCapSlack_eq_zero (D : WeightedDesign m 3)
    {first second : Fin m} (hne : second ≠ first)
    (hslack : pairCapSlack D first second = 0)
    {dep : Fin m → ℝ} (hdep : (∑ index, dep index • D.atom index) = 0) :
    D.weight second * (D.atom first ⬝ᵥ D.atom second) * dep first
      + (1 - shareOf D first) * dep second = 0 := by
  have hfirst := D.weight_pos first
  have hsecond := D.weight_pos second
  have hgram := pairCapSlack_eq_weight_mul_coDependency_gramDet D first second
  rw [hslack] at hgram
  have hdegenerate : ((1 - shareOf D first) / D.weight first)
      * ((1 - shareOf D second) / D.weight second)
      = (D.atom first ⬝ᵥ D.atom second) ^ 2 := by
    have hprod : (0 : ℝ) < D.weight first * D.weight second := mul_pos hfirst hsecond
    rcases mul_eq_zero.mp hgram.symm with hbad | hgood
    · exact absurd hbad (ne_of_gt hprod)
    · linarith
  have hcap := sq_pairReading_le D hne (D.atom first ⬝ᵥ D.atom second)
    ((1 - shareOf D first) / D.weight first) hdep
  have hquadZero : (D.atom first ⬝ᵥ D.atom second) ^ 2
        * ((1 - shareOf D first) / D.weight first)
      - 2 * (D.atom first ⬝ᵥ D.atom second) * ((1 - shareOf D first) / D.weight first)
        * (D.atom first ⬝ᵥ D.atom second)
      + ((1 - shareOf D first) / D.weight first) ^ 2
        * ((1 - shareOf D second) / D.weight second) = 0 := by
    linear_combination ((1 - shareOf D first) / D.weight first) * hdegenerate
  rw [hquadZero, zero_mul] at hcap
  have hsq : ((D.atom first ⬝ᵥ D.atom second) * (dep first / D.weight first)
      + ((1 - shareOf D first) / D.weight first) * (dep second / D.weight second)) ^ 2 = 0 :=
    le_antisymm hcap (sq_nonneg _)
  have hzeroLin : (D.atom first ⬝ᵥ D.atom second) * (dep first / D.weight first)
      + ((1 - shareOf D first) / D.weight first) * (dep second / D.weight second) = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  have hexpand : ((D.atom first ⬝ᵥ D.atom second) * (dep first / D.weight first)
        + ((1 - shareOf D first) / D.weight first) * (dep second / D.weight second))
      * (D.weight first * D.weight second)
      = D.weight second * (D.atom first ⬝ᵥ D.atom second) * dep first
        + (1 - shareOf D first) * dep second := by
    field_simp
    try ring
  rw [← hexpand, hzeroLin, zero_mul]

/-! ## Part 4 — the pair test for domination -/

/-- **THE DUAL PAIR MINOR IS THE CAP SLACK.**  The product of two dual ratios
minus the odds-weighted squared pairing is the cap slack divided by the two
co-weights, so it is NONNEGATIVE at every pair. -/
theorem dualRatio_mul_dualRatio_sub_odds_mul_sq (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (first second : Fin m) :
    dualRatio D first * dualRatio D second
        - weightOdds D first * weightOdds D second * (D.atom first ⬝ᵥ D.atom second) ^ 2
      = pairCapSlack D first second / ((1 - D.weight first) * (1 - D.weight second)) := by
  have hfirst := D.weight_pos first
  have hsecond := D.weight_pos second
  have hcofirst : (0 : ℝ) < 1 - D.weight first := by linarith [weight_lt_one D hm first]
  have hcosecond : (0 : ℝ) < 1 - D.weight second := by linarith [weight_lt_one D hm second]
  rw [dualRatio, dualRatio, weightOdds, weightOdds,
    pairCapSlack_eq_weight_mul_coDependency_gramDet D first second]
  field_simp
  try ring

theorem odds_mul_sq_le_dualRatio_mul (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {first second : Fin m} (hne : first ≠ second) :
    weightOdds D first * weightOdds D second * (D.atom first ⬝ᵥ D.atom second) ^ 2
      ≤ dualRatio D first * dualRatio D second := by
  have hcofirst : (0 : ℝ) < 1 - D.weight first := by linarith [weight_lt_one D hm first]
  have hcosecond : (0 : ℝ) < 1 - D.weight second := by linarith [weight_lt_one D hm second]
  have hlaw := dualRatio_mul_dualRatio_sub_odds_mul_sq D hm first second
  have hquot : 0 ≤ pairCapSlack D first second / ((1 - D.weight first) * (1 - D.weight second)) :=
    div_nonneg (pairCapSlack_nonneg_of_ne D hne) (by positivity)
  linarith

/-- **THE PAIR BLOCK BOUND.**  If a scale dominates the two-by-two dual block of a
pair, the two dual readings of every dependency together spend at most that scale
of the ambient norm.  The pair cap is run at the pencil the two readings supply,
and no square root appears. -/
theorem sum_two_dualReading_le (D : WeightedDesign m k) (hm : 2 ≤ m)
    {first second : Fin m} (hne : second ≠ first) {scale : ℝ}
    (hfirstLe : dualRatio D first ≤ scale) (hsecondLe : dualRatio D second ≤ scale)
    (hblock : weightOdds D first * weightOdds D second * (D.atom first ⬝ᵥ D.atom second) ^ 2
      ≤ (scale - dualRatio D first) * (scale - dualRatio D second))
    {dep : Fin m → ℝ} (hdep : (∑ index, dep index • D.atom index) = 0) :
    dep first ^ 2 / (D.weight first * (1 - D.weight first))
        + dep second ^ 2 / (D.weight second * (1 - D.weight second))
      ≤ scale * dualNormSq D dep := by
  have hwFirst := D.weight_pos first
  have hwSecond := D.weight_pos second
  have hcoFirst : (0 : ℝ) < 1 - D.weight first := by linarith [weight_lt_one D hm first]
  have hcoSecond : (0 : ℝ) < 1 - D.weight second := by linarith [weight_lt_one D hm second]
  set oddsFirst : ℝ := weightOdds D first with hoddsFirst
  set oddsSecond : ℝ := weightOdds D second with hoddsSecond
  have hoddsFirstPos : 0 < oddsFirst := weightOdds_pos D hm first
  have hoddsSecondPos : 0 < oddsSecond := weightOdds_pos D hm second
  set readFirst : ℝ := dep first / D.weight first with hreadFirst
  set readSecond : ℝ := dep second / D.weight second with hreadSecond
  set massFirst : ℝ := oddsFirst * readFirst ^ 2 with hmassFirst
  set massSecond : ℝ := oddsSecond * readSecond ^ 2 with hmassSecond
  have hmassFirstEq : massFirst = dep first ^ 2 / (D.weight first * (1 - D.weight first)) := by
    rw [hmassFirst, hreadFirst, hoddsFirst, weightOdds]
    field_simp
    try ring
  have hmassSecondEq : massSecond
      = dep second ^ 2 / (D.weight second * (1 - D.weight second)) := by
    rw [hmassSecond, hreadSecond, hoddsSecond, weightOdds]
    field_simp
    try ring
  have hmassFirstNonneg : 0 ≤ massFirst := by positivity
  have hmassSecondNonneg : 0 ≤ massSecond := by positivity
  have hratioFirst : oddsFirst * ((1 - shareOf D first) / D.weight first)
      = dualRatio D first := by
    rw [hoddsFirst, weightOdds, dualRatio]
    field_simp
  have hratioSecond : oddsSecond * ((1 - shareOf D second) / D.weight second)
      = dualRatio D second := by
    rw [hoddsSecond, weightOdds, dualRatio]
    field_simp
  have hcap := sq_pairReading_le D hne (oddsFirst * readFirst) (oddsSecond * readSecond) hdep
  set pairing : ℝ := D.atom first ⬝ᵥ D.atom second with hpairing
  set cross : ℝ := -(oddsFirst * oddsSecond * pairing * (readFirst * readSecond)) with hcross
  have hleft : (oddsFirst * readFirst * readFirst + oddsSecond * readSecond * readSecond) ^ 2
      = (massFirst + massSecond) ^ 2 := by
    rw [hmassFirst, hmassSecond]; ring
  have hrightEq : (oddsFirst * readFirst) ^ 2 * ((1 - shareOf D first) / D.weight first)
        - 2 * (oddsFirst * readFirst) * (oddsSecond * readSecond) * pairing
        + (oddsSecond * readSecond) ^ 2 * ((1 - shareOf D second) / D.weight second)
      = dualRatio D first * massFirst + dualRatio D second * massSecond + 2 * cross := by
    rw [← hratioFirst, ← hratioSecond, hmassFirst, hmassSecond, hcross]
    ring
  rw [hleft, hrightEq] at hcap
  have hcrossSq : cross ^ 2
      = oddsFirst * oddsSecond * pairing ^ 2 * (massFirst * massSecond) := by
    rw [hcross, hmassFirst, hmassSecond]; ring
  have hgapFirst : 0 ≤ scale - dualRatio D first := by linarith
  have hgapSecond : 0 ≤ scale - dualRatio D second := by linarith
  set gapFirst : ℝ := (scale - dualRatio D first) * massFirst with hgapFirstDef
  set gapSecond : ℝ := (scale - dualRatio D second) * massSecond with hgapSecondDef
  have hgapFirstNonneg : 0 ≤ gapFirst := mul_nonneg hgapFirst hmassFirstNonneg
  have hgapSecondNonneg : 0 ≤ gapSecond := mul_nonneg hgapSecond hmassSecondNonneg
  have hproduct : cross ^ 2 ≤ gapFirst * gapSecond := by
    rw [hcrossSq, hgapFirstDef, hgapSecondDef]
    have hstep := mul_le_mul_of_nonneg_right hblock
      (mul_nonneg hmassFirstNonneg hmassSecondNonneg)
    nlinarith [hstep]
  have hsquares : (2 * cross) ^ 2 ≤ (gapFirst + gapSecond) ^ 2 := by
    nlinarith [hproduct, sq_nonneg (gapFirst - gapSecond)]
  have hsumNonneg : 0 ≤ gapFirst + gapSecond := by linarith
  have hcrossBound : 0 ≤ gapFirst + gapSecond + 2 * cross := by
    by_cases hc : cross < 0
    · nlinarith [hsquares, hsumNonneg, hc]
    · push_neg at hc
      linarith
  have hboundExpanded : dualRatio D first * massFirst + dualRatio D second * massSecond
      + 2 * cross ≤ scale * (massFirst + massSecond) := by
    rw [hgapFirstDef, hgapSecondDef] at hcrossBound
    nlinarith [hcrossBound]
  have hnorm := dualNormSq_nonneg D dep
  have hscaleNonneg : 0 ≤ scale := le_trans (dualRatio_nonneg D hm first) hfirstLe
  have hsquare : (massFirst + massSecond) ^ 2
      ≤ scale * (massFirst + massSecond) * dualNormSq D dep := by
    calc (massFirst + massSecond) ^ 2
        ≤ (dualRatio D first * massFirst + dualRatio D second * massSecond + 2 * cross)
            * dualNormSq D dep := hcap
      _ ≤ scale * (massFirst + massSecond) * dualNormSq D dep :=
          mul_le_mul_of_nonneg_right hboundExpanded hnorm
  rw [← hmassFirstEq, ← hmassSecondEq]
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ massFirst + massSecond) with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg hscaleNonneg hnorm
  · nlinarith [hsquare, hpos, hnorm]

/-- **THE PAIR TEST.**  A triple dominates as soon as ONE of its pairs has its
two-by-two dual block below the room the third label leaves.  It contains the
trace test of `Gtz.dominates_of_sum_dualRatio_le_one`, because the dual pair
minor is a cap slack and so is nonnegative.

Measured: over 200000 random `(6,3)` designs the pair test fires at `3.97` times
as many triples as the trace test and never fails. -/
theorem dominates_of_pairTest_triple (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {scale : ℝ}
    (hfirstLe : dualRatio D a ≤ scale) (hsecondLe : dualRatio D b ≤ scale)
    (hblock : weightOdds D a * weightOdds D b * (D.atom a ⬝ᵥ D.atom b) ^ 2
      ≤ (scale - dualRatio D a) * (scale - dualRatio D b))
    (hroom : scale + dualRatio D c ≤ 1) :
    Dominates D ({a, b, c} : Finset (Fin m)) := by
  classical
  have hinj : Function.Injective (![a, b, c] : Fin 3 → Fin m) :=
    injective_tripleVec hab hac hbc
  have himage : Finset.image (![a, b, c] : Fin 3 → Fin m) Finset.univ
      = ({a, b, c} : Finset (Fin m)) := image_tripleVec_eq
  have hstep : Dominates D (Finset.image (![a, b, c] : Fin 3 → Fin m) Finset.univ) := by
    rw [dominates_iff_depSlack_nonneg D hm _ hinj]
    intro dep hdep
    rw [himage]
    have hsplit := depSlack_eq_dualNormSq_sub D hm ({a, b, c} : Finset (Fin m)) dep
    rw [sum_over_triple (fun index =>
      dep index ^ 2 / (D.weight index * (1 - D.weight index))) hab hac hbc] at hsplit
    have hpair := sum_two_dualReading_le D hm (Ne.symm hab) hfirstLe hsecondLe hblock hdep
    have hthird := sum_dualReading_le_of_dependency D hm ({c} : Finset (Fin m)) hdep
    rw [Finset.sum_singleton, Finset.sum_singleton] at hthird
    have hnorm := dualNormSq_nonneg D dep
    rw [hsplit]
    nlinarith [hpair, hthird, hnorm, hroom]
  rwa [himage] at hstep

/-- **THE STRICT PAIR TEST.**  Strict room gives STRICT domination. -/
theorem posDef_gap_of_pairTest_triple (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {scale : ℝ}
    (hfirstLe : dualRatio D a ≤ scale) (hsecondLe : dualRatio D b ≤ scale)
    (hblock : weightOdds D a * weightOdds D b * (D.atom a ⬝ᵥ D.atom b) ^ 2
      ≤ (scale - dualRatio D a) * (scale - dualRatio D b))
    (hroom : scale + dualRatio D c < 1) :
    (subsetSum D ({a, b, c} : Finset (Fin m)) - 1).PosDef := by
  classical
  have hinj : Function.Injective (![a, b, c] : Fin 3 → Fin m) :=
    injective_tripleVec hab hac hbc
  have himage : Finset.image (![a, b, c] : Fin 3 → Fin m) Finset.univ
      = ({a, b, c} : Finset (Fin m)) := image_tripleVec_eq
  have hstep : (subsetSum D (Finset.image (![a, b, c] : Fin 3 → Fin m) Finset.univ)
      - 1).PosDef := by
    rw [posDef_gap_iff_depSlack_pos D hm _ hinj]
    intro dep hne hdep
    rw [himage]
    have hsplit := depSlack_eq_dualNormSq_sub D hm ({a, b, c} : Finset (Fin m)) dep
    rw [sum_over_triple (fun index =>
      dep index ^ 2 / (D.weight index * (1 - D.weight index))) hab hac hbc] at hsplit
    have hpair := sum_two_dualReading_le D hm (Ne.symm hab) hfirstLe hsecondLe hblock hdep
    have hthird := sum_dualReading_le_of_dependency D hm ({c} : Finset (Fin m)) hdep
    rw [Finset.sum_singleton, Finset.sum_singleton] at hthird
    have hnorm := dualNormSq_pos_of_ne_zero D hne
    rw [hsplit]
    nlinarith [hpair, hthird, hnorm, hroom]
  rwa [himage] at hstep

/-- **THE CANONICAL PAIR TEST**, at the scale the third label leaves. -/
theorem dominates_of_pairTest_canonical (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hfirstLe : dualRatio D a ≤ 1 - dualRatio D c)
    (hsecondLe : dualRatio D b ≤ 1 - dualRatio D c)
    (hblock : weightOdds D a * weightOdds D b * (D.atom a ⬝ᵥ D.atom b) ^ 2
      ≤ (1 - dualRatio D c - dualRatio D a) * (1 - dualRatio D c - dualRatio D b)) :
    Dominates D ({a, b, c} : Finset (Fin m)) :=
  dominates_of_pairTest_triple D hm hab hac hbc hfirstLe hsecondLe
    (by nlinarith [hblock]) (by linarith)

/-- **THE PAIR TEST CONTAINS THE TRACE TEST.** -/
theorem pairTest_of_sum_dualRatio_le_one (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b c : Fin m} (hab : a ≠ b)
    (hsum : dualRatio D a + dualRatio D b + dualRatio D c ≤ 1) :
    dualRatio D a ≤ 1 - dualRatio D c ∧ dualRatio D b ≤ 1 - dualRatio D c
      ∧ weightOdds D a * weightOdds D b * (D.atom a ⬝ᵥ D.atom b) ^ 2
        ≤ (1 - dualRatio D c - dualRatio D a) * (1 - dualRatio D c - dualRatio D b) := by
  have hnonnegA := dualRatio_nonneg D hm a
  have hnonnegB := dualRatio_nonneg D hm b
  have hminor := odds_mul_sq_le_dualRatio_mul D hm hab
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith [hminor, hnonnegA, hnonnegB]

/-- **THE TIE REFUSES THE PAIR TEST.**  At a `(6,3)` tie every triple and every
scale with strict room fails the block inequality. -/
theorem pairTest_fails_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    {a b c : Fin 6} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {scale : ℝ}
    (hfirstLe : dualRatio D a ≤ scale) (hsecondLe : dualRatio D b ≤ scale)
    (hroom : scale + dualRatio D c < 1) :
    (scale - dualRatio D a) * (scale - dualRatio D b)
      < weightOdds D a * weightOdds D b * (D.atom a ⬝ᵥ D.atom b) ^ 2 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcard : ({a, b, c} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  exact htie.2 _ hcard (posDef_gap_of_pairTest_triple D (by norm_num) hab hac hbc
    hfirstLe hsecondLe hcon hroom)

/-- **THE MAIN STATEMENT, REDUCED TO THE PAIR TEST.**  `Gtz.GtzWeighted 6 3`
follows from producing at every `(6,3)` design ONE triple that passes the pair
test.  The test reads the six shares, the six weights and ONE pairing. -/
theorem gtzWeighted_sixThree_of_pairTest
    (hpair : ∀ D : WeightedDesign 6 3, ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c
      ∧ dualRatio D a ≤ 1 - dualRatio D c ∧ dualRatio D b ≤ 1 - dualRatio D c
      ∧ weightOdds D a * weightOdds D b * (D.atom a ⬝ᵥ D.atom b) ^ 2
        ≤ (1 - dualRatio D c - dualRatio D a) * (1 - dualRatio D c - dualRatio D b)) :
    GtzWeighted 6 3 := by
  classical
  intro D
  obtain ⟨a, b, c, hab, hac, hbc, hfirstLe, hsecondLe, hblock⟩ := hpair D
  refine ⟨({a, b, c} : Finset (Fin 6)), ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  · exact dominates_of_pairTest_canonical D (by norm_num) hab hac hbc hfirstLe hsecondLe hblock

end Gtz
