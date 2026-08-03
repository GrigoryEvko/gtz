/-
PROVENANCE.  Harvested by the sweep from the think-capture adjudication rung, which
derived the subsumption identity, the rank-two equivalence and the rank-generic form
of the shipped two-moment certificate, and prototyped every statement below.  The
sweep re-compiled, re-audited and wired it; the mathematics is think-capture's.

NOTE ON SCOPE, carried from that rung's own verdict.  No DOMINATION criterion is
landed at rank three, and none should be: `twoMomentGap_eq_spreadGap_add` proves the
shipped `Gtz.dominates_of_twoMomentGap_nonneg` fires wherever a trace-spread criterion
would, so such a criterion would be a duplicate.  What is landed is the identity that
establishes that -- the honest negative -- together with the rank-two equivalence and
the general-rank core, which the tree does not have at any rank above three.

# think-capture scratch probe -- the capture-criterion ladder at rank three

READ-ONLY RUNG.  Nothing here is landed; this file exists so that successors
inherit COMPILING statements rather than sketches (R11).

What is prototyped, in the order a lander would want it:

1. `spreadGap` -- the DISPERSION leg of the trace-spread capture criterion, in the
   same six-scalar language `Gtz.twoMomentGap` already uses.
2. `twoMomentGap_eq_spreadGap_add` -- THE SUBSUMPTION IDENTITY,
      twoMomentGap = spreadGap + 4 * det (Gram_C - I),
   a pure `ring` fact.  Combined with soundness it proves that the SHIPPED
   criterion fires wherever the trace-spread one does, so the trace-spread
   criterion must NOT be landed at rank three.  This is the honest negative of
   this rung and it is what saves a duplicate.
3. `one_le_of_dispersion` -- the scalar core of the trace-spread criterion at
   rank three, proved from scratch (Cauchy-Schwarz on the two eigenvalues other
   than the smallest, then a quadratic sign argument).  General-shape, so a
   lander can see the rank-k pattern.
4. `rankTwo_dispersion_iff` -- at rank two the dispersion leg IS the determinant,
   so the criterion is an equivalence.  This is the k = 2 sanity check in Lean.
5. `generalRankThreshold` and `one_le_of_generalRank_amgm` -- the rank-generic
   form of the SHIPPED criterion,  D * (k-1)^(k-1) >= (L-1)^(k-1)  implies the
   smallest eigenvalue is at least one.  The AM-GM step is ISOLATED as an
   explicit hypothesis `hamgm` because Mathlib's
   `Real.geom_mean_le_arith_mean_weighted` is stated with real exponents and the
   integer-power form a lander wants is not directly available; everything after
   AM-GM is proved here.
-/
import Mathlib
import Gtz.Quantitative.TwoMomentCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

/-! ## 1-2.  The dispersion leg and the subsumption identity -/

/-- **The dispersion gap** of a triple, in the same six inner products
`Gtz.twoMomentGap` uses:  `4 * e_2(Gram_C - I) - e_1(Gram_C - I)^2`.  Degree TWO
in the Gram entries, and it never touches the triple product -- so it is
manifestly sign-blind, which is exactly why it cannot decide `icosaDesign`. -/
def spreadGap (levFirst levSecond levThird pairFirstSecond pairFirstThird
    pairSecondThird : ℝ) : ℝ :=
  4 * ((levFirst - 1) * (levSecond - 1) + (levFirst - 1) * (levThird - 1)
        + (levSecond - 1) * (levThird - 1)
        - pairFirstSecond ^ 2 - pairFirstThird ^ 2 - pairSecondThird ^ 2)
    - (levFirst + levSecond + levThird - 3) ^ 2

/-- **THE SUBSUMPTION IDENTITY.**  The shipped two-moment gap exceeds the
dispersion gap by exactly four times the determinant of the gap block. -/
theorem twoMomentGap_eq_spreadGap_add (levFirst levSecond levThird pairFirstSecond
    pairFirstThird pairSecondThird : ℝ) :
    twoMomentGap levFirst levSecond levThird pairFirstSecond pairFirstThird
        pairSecondThird
      = spreadGap levFirst levSecond levThird pairFirstSecond pairFirstThird
          pairSecondThird
        + 4 * ((levFirst - 1) * (levSecond - 1) * (levThird - 1)
              + 2 * pairFirstSecond * pairFirstThird * pairSecondThird
              - (levFirst - 1) * pairSecondThird ^ 2
              - (levSecond - 1) * pairFirstThird ^ 2
              - (levThird - 1) * pairFirstSecond ^ 2) := by
  simp only [twoMomentGap, spreadGap]
  ring

/-! ## 3.  The scalar core of the dispersion criterion -/

/-- **The dispersion criterion, scalar form at rank three.**  Three reals whose
sum is nonnegative and whose squared sum dominates twice their sum of squares are
each nonnegative.  Cauchy-Schwarz on the two others, then a quadratic sign
argument.  (Read `first, second, third` as the eigenvalues of `Gram_C - I`.) -/
theorem one_le_of_dispersion {first second third : ℝ}
    (hsum : 0 ≤ first + second + third)
    (hspread : 2 * (first ^ 2 + second ^ 2 + third ^ 2)
      ≤ (first + second + third) ^ 2) :
    0 ≤ first := by
  by_contra hcontra
  push Not at hcontra
  -- Cauchy-Schwarz on the other two: (second + third)^2 <= 2 (second^2 + third^2)
  have hcauchy : (second + third) ^ 2 ≤ 2 * (second ^ 2 + third ^ 2) := by
    nlinarith [sq_nonneg (second - third)]
  -- expand the hypothesis around `first`
  nlinarith [hcauchy, sq_nonneg first, sq_nonneg (second + third),
    mul_pos (neg_pos.mpr hcontra) (neg_pos.mpr hcontra),
    mul_nonneg hsum (neg_nonneg.mpr hcontra.le)]

/-! ## 4.  Rank two: the criterion is an equivalence -/

/-- At rank two the dispersion leg is exactly twice the determinant, so the
criterion `tr >= 0` and `dispersion >= 0` IS positive semidefiniteness.  This is
the k = 2 sanity check: the capture formulation absorbs rank two with no loss. -/
theorem rankTwo_dispersion_eq (first second : ℝ) :
    (first + second) ^ 2 - 1 * (first ^ 2 + second ^ 2) = 2 * (first * second) := by
  ring

/-- **THE RANK-TWO SANITY CHECK.**  At rank two the dispersion leg IS the determinant,
so the criterion is an EQUIVALENCE rather than a one-way certificate.  This is the
light-cone phenomenon: `PSD_2` is a Lorentz cone, and the dispersion leg is exactly its
defining quadratic. -/
theorem rankTwo_dispersion_iff {first second : ℝ}
    (hsum : 0 ≤ first + second) :
    (0 ≤ (first + second) ^ 2 - (first ^ 2 + second ^ 2))
      ↔ (0 ≤ first ∧ 0 ≤ second) := by
  constructor
  · intro hgap
    have hprod : 0 ≤ first * second := by nlinarith [hgap]
    constructor
    · nlinarith [hprod, hsum, sq_nonneg (first - second)]
    · nlinarith [hprod, hsum, sq_nonneg (first - second)]
  · rintro ⟨hfirst, hsecond⟩
    nlinarith [mul_nonneg hfirst hsecond]

/-! ## 5.  The rank-generic form of the SHIPPED criterion -/

/-- The rank-generic threshold: a `k`-subset whose Gram block has trace `L > k`
and determinant at least `((L-1)/(k-1))^(k-1)` dominates.  At `k = 3` this is
`4 D >= (L-1)^2`, i.e. `Gtz.twoMomentGap >= 0`; at `k = 2` it is `D >= L - 1`,
which is an equivalence. -/
noncomputable def generalRankThreshold (rank : ℕ) (leverageSum : ℝ) : ℝ :=
  ((leverageSum - 1) / (rank - 1 : ℝ)) ^ (rank - 1)

/-- **The monotonicity step at general rank, closed by BERNOULLI.**  For
`0 ≤ x < 1` and `L - x > c ≥ 1` one has `x * (L - x)^c < (L - 1)^c`.

This is the general-`k` replacement for the rank-three factorisation
`Gtz.twoMoment_factorisation`.  Writing `u = (1-x)/(L-x) ∈ (0,1)` and using
`(1-u)^c ≥ 1 - c*u`, the claim reduces to `1 - c*(1-x)/(L-x) > x`, i.e. to
`L - x > c`, which is exactly the heaviness hypothesis. -/
theorem mul_pow_lt_pow_of_lt_one {exponent : ℕ} {smallest leverageSum : ℝ}
    (hexp : 1 ≤ exponent) (hsmall : 0 ≤ smallest) (hlt : smallest < 1)
    (hheavy : (exponent : ℝ) < leverageSum - smallest) :
    smallest * (leverageSum - smallest) ^ exponent < (leverageSum - 1) ^ exponent := by
  have hexpOne : (1 : ℝ) ≤ (exponent : ℝ) := by exact_mod_cast hexp
  have hgapPos : (0 : ℝ) < leverageSum - smallest := by linarith
  have hgapNe : leverageSum - smallest ≠ 0 := ne_of_gt hgapPos
  have honePos : (0 : ℝ) < leverageSum - 1 := by linarith
  have hratioLt : (exponent : ℝ) / (leverageSum - smallest) < 1 :=
    (div_lt_one hgapPos).mpr hheavy
  have hsplit : leverageSum - 1
      = (leverageSum - smallest) * (1 - (1 - smallest) / (leverageSum - smallest)) := by
    field_simp; ring
  have hratioNonneg : 0 ≤ (1 - smallest) / (leverageSum - smallest) :=
    div_nonneg (by linarith) hgapPos.le
  have hratioLe : (1 - smallest) / (leverageSum - smallest) ≤ 1 := by
    rw [div_le_one hgapPos]; linarith
  have hbernoulli : 1 + (exponent : ℝ) * (-((1 - smallest) / (leverageSum - smallest)))
      ≤ (1 + -((1 - smallest) / (leverageSum - smallest))) ^ exponent :=
    one_add_mul_le_pow (by linarith) exponent
  have hstrict : smallest
      < 1 + (exponent : ℝ) * (-((1 - smallest) / (leverageSum - smallest))) := by
    have hproduct : (1 - smallest)
        * (1 - (exponent : ℝ) / (leverageSum - smallest)) > 0 :=
      mul_pos (by linarith) (by linarith)
    have hexpand : (1 - smallest) * (1 - (exponent : ℝ) / (leverageSum - smallest))
        = 1 + (exponent : ℝ) * (-((1 - smallest) / (leverageSum - smallest))) - smallest := by
      field_simp; ring
    linarith [hexpand ▸ hproduct]
  have hchain : smallest
      < (1 + -((1 - smallest) / (leverageSum - smallest))) ^ exponent := by linarith
  calc smallest * (leverageSum - smallest) ^ exponent
      < (1 + -((1 - smallest) / (leverageSum - smallest))) ^ exponent
          * (leverageSum - smallest) ^ exponent :=
        mul_lt_mul_of_pos_right hchain (pow_pos hgapPos exponent)
    _ = ((leverageSum - smallest)
          * (1 - (1 - smallest) / (leverageSum - smallest))) ^ exponent := by
        rw [← mul_pow]; ring_nf
    _ = (leverageSum - 1) ^ exponent := by rw [← hsplit]

/-- **The rank-generic core, everything after AM-GM.**  `smallest` is the least
eigenvalue of the Gram block and `leverageSum` its trace.  `hamgm` is exactly the
arithmetic-geometric step -- the product of the other `k-1` eigenvalues is at
most the `(k-1)`-st power of their mean -- supplied as a hypothesis because
Mathlib states AM-GM with real exponents and the integer-power form is not
directly available.  Everything after it is proved here, at general rank. -/
theorem one_le_of_generalRank_amgm {rank : ℕ} {smallest leverageSum determinant : ℝ}
    (hrank : 2 ≤ rank) (hsmall : 0 ≤ smallest) (hbig : (rank : ℝ) < leverageSum)
    (hamgm : determinant * ((rank : ℝ) - 1) ^ (rank - 1)
      ≤ smallest * (leverageSum - smallest) ^ (rank - 1))
    (hthreshold : (leverageSum - 1) ^ (rank - 1) ≤ determinant * ((rank : ℝ) - 1) ^ (rank - 1)) :
    1 ≤ smallest := by
  by_contra hcontra
  push Not at hcontra
  have hrankReal : (2 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
  have hexp : 1 ≤ rank - 1 := by omega
  have hcast : ((rank - 1 : ℕ) : ℝ) = (rank : ℝ) - 1 := by
    have : (1 : ℕ) ≤ rank := by omega
    push_cast [Nat.cast_sub this]; ring
  have hheavy : ((rank - 1 : ℕ) : ℝ) < leverageSum - smallest := by
    rw [hcast]; linarith
  have hkey := mul_pow_lt_pow_of_lt_one hexp hsmall hcontra hheavy
  linarith

end Gtz
