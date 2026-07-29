/-
# The elliptope interval: the exact criterion for one correlation triple, and the
complete failure taxonomy

`Gtz.Quantitative.GoodTripleGraph` reduced a rank-three triple to three numbers,
the normalized pairings `rho`, and named the degree-three form they must satisfy,
`Gtz.elliptopeBracket`. What it did NOT do is solve that form. This file does: it
factors the bracket completely, turns the covering condition into a two-sided
inequality on a single correlation, and classifies every way a triple can fail.

**The whole file rests on one `ring` identity.** For any three reals,

  `elliptopeBracket r1 r2 r3 = (1 − r1²)(1 − r2²) − (r3 − r1 r2)²`

(`elliptopeBracket_eq_completedSquare_third`, and its two siblings isolating the
other slots). Everything below is a consequence. The identity is RADICAL-FREE, which
is why the campaign's exact-rational decision discipline survives intact: the
discriminant that the classical criterion writes as `sqrt((1 − r1²)(1 − r2²))` never
has to be formed to DECIDE anything, only to NAME the endpoints. Given the sign
oscillation recorded in `GoodTripleGraph` — `mpmath` returns `−4.59e−41` at 40 digits
and `+2.11e−81` at 80 for a leg that is exactly zero — that matters.

**The interval criterion.** With `rootLower r1 r2 = r1 r2 − sqrt((1−r1²)(1−r2²))` and
`rootUpper` the reflected endpoint, a compatible pair `r1, r2` admits exactly the
third correlations in `[rootLower, rootUpper]`
(`elliptopeBracket_nonneg_iff_mem_rootInterval`), with equality exactly at the two
endpoints (`elliptopeBracket_eq_zero_iff_eq_root`) and strict positivity exactly on
the open interval. The endpoints obey Vieta — sum `2 r1 r2`, product `r1² + r2² − 1`
— so they are algebraic over the rational data with no radical in the coefficients,
and they never leave `[−1, 1]` (`neg_one_le_rootLower`, `rootUpper_le_one`, both
`(r1 ∓ r2)² ≥ 0` after squaring). That last fact upgrades to a genuine strengthening
of the shipped predicate: **two compatibility conditions plus the bracket imply the
third** (`isElliptopePoint_iff_two_sq_le_one`), so `IsElliptopeGoodTriangle` carries
one redundant conjunct, exactly as the `dominates_triple_iff_isElliptopeGoodTriangle`
docstring observed without proving.

**The box, sharp, with its equality set.** All three `|rho| ≤ 1/2` forces the bracket
nonnegative, and the proof is not a vertex enumeration: `−r1² − r2² − r3² ≥ −3/4` and
`2 r1 r2 r3 ≥ −2|r1 r2 r3| ≥ −1/4` add to `≥ 0` term by term. Equality therefore needs
BOTH bounds tight, i.e. `|r1| = |r2| = |r3| = 1/2` and `r1 r2 r3 < 0` — the four
Mercedes points `(∓1/2, ∓1/2, ∓1/2)` with an odd number of minus signs
(`elliptopeBracket_eq_zero_iff_mercedes` for the compact characterization,
`elliptopeBracket_eq_zero_iff_mercedesPoint` for the four points spelled out). The other four vertices give `1/2`. The
constant is sharp in the strongest sense: for every `c > 1/2` the symmetric point
`(−c, −c, −c)` has bracket `−(2c − 1)(c + 1)²< 0` (`elliptopeBracket_neg_of_half_lt`).

**The taxonomy, and it is sharper than the pen claim.** A triple that is not an
elliptope point is exactly one of three things, and `ElliptopeClass` with
`existsUnique_hasElliptopeClass` says so as a single `∃!`:

  * WILD — some `|rho| > 1`. Not a bracket failure at all: at `rho ≡ 3/2` the bracket
    is `+1` (`elliptopeBracket_threeHalves_eq_one`), which is why the compatibility
    conjunct is load-bearing and why `0 ≤ discriminantTie` alone certifies nothing.
  * COHERENT FAILURE — compatible, `r1 r2 r3 ≥ 0`, bracket negative. Then the two
    largest squares sum above one, hence **some `|rho| > 1/sqrt 2`**.
  * FRUSTRATED FAILURE — compatible, `r1 r2 r3 < 0`, bracket negative. Then
    **some `|rho| > 1/2`**.

The `≥ 0` in the coherent branch is not cosmetic: with a strict `> 0` the trichotomy
is not exhaustive, since `(0, r, r)` has product zero and is a genuine failure for
`r² > 1/2`. That witness also shows `1/sqrt 2` is SHARP for the coherent branch, and
the frustrated equilateral `(t, t, t)` with `t < −1/2` shows `1/2` is sharp for the
frustrated branch. So the two branches have genuinely different thresholds, a
separation the pen taxonomy did not record. The pen's alternative phrasing — the
least correlation drops below `rootLower` — is gauge-dependent and TRUE only after
switching to the all-nonnegative representative; it is stated here in that gauge
(`lt_rootLower_of_failure_of_least`, and for a genuine coherent failure
`abs_lt_rootLower_of_isCoherentFailingTriple`) and the gauge move itself is free,
since `elliptopeBracket |r1| |r2| |r3| = elliptopeBracket r1 r2 r3` whenever the
product is nonnegative (`elliptopeBracket_abs_of_coherent`). Outside the gauge the
phrasing is FALSE and `coherentFailure_rootLower_needs_gauge` carries the witness.

**Everything transports, with LOCAL hypotheses.** `dominates_triple_iff_isElliptopePoint`
is proved from the pivot-corner reduction directly, so it asks only that the three
atoms of the triple have positive excess, not `AllHeavy D`, and in the forward
direction it establishes only the two PIVOT edges — the third is free by
`sq_le_one_of_two_and_bracket_nonneg`. The interval criterion, the taxonomy and the
sharpened coherent threshold all inherit that hypothesis shape.

**Layering notes for the integrator.** This module sits in `Gtz/LinAlg/` but imports
`Gtz.Quantitative.GoodTripleGraph`, because the task of the file is precisely to make
the scalar vocabulary and the shipped design vocabulary interchangeable. Sections 1–7
are design-free real algebra and could be split out; section 8 is the design bridge. The
unit-diagonal MATRIX of a correlation triple, its determinant identity and the
congruence proof that domination is positive semidefiniteness of it belong to
`Gtz.Design.RhoNormalForm` (`correlationMatrixThree`,
`posSemidef_correlationMatrixThree_iff`) and are deliberately not repeated here; the
single lemma `isElliptopePoint_iff_sq_le_one_and_bracket_nonneg` matches that file's
criterion conjunct for conjunct, so the two compose without either importing the
other.

**What this does NOT buy.** Everything here reads three numbers per triple, so it is
subject to the same wall as the rest of the layer. The coherent branch in particular
is not a certificate: `dominates_of_coherentPairings` is empty at `icosaDesign`
(`icosaDesign_excessGap_of_distinct` is `−14/5`), and the sign-blind closure
`IsSignBlindGoodTriple` is refuted at every size at least six. What the taxonomy adds
is a sharp lower bound on the edge a failure must carry, per sign class — a
constraint on failures, not a certificate for successes.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.GoodTripleGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The completed square, and the symmetries

The bracket is totally symmetric, so all three completed squares hold; each is the
one to reach for when the corresponding slot is the unknown. -/

/-- **The load-bearing identity, isolating the pivot-free slot.** Pure `ring`. Given
the two pivot correlations, the bracket is a downward parabola in the third whose
maximum value is `(1 − rhoFirst²)(1 − rhoSecond²)`. -/
theorem elliptopeBracket_eq_completedSquare_third (rhoFirst rhoSecond rhoThird : ℝ) :
    elliptopeBracket rhoFirst rhoSecond rhoThird
      = (1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2)
        - (rhoThird - rhoFirst * rhoSecond) ^ 2 := by
  rw [elliptopeBracket]; ring

theorem elliptopeBracket_eq_completedSquare_first (rhoFirst rhoSecond rhoThird : ℝ) :
    elliptopeBracket rhoFirst rhoSecond rhoThird
      = (1 - rhoSecond ^ 2) * (1 - rhoThird ^ 2)
        - (rhoFirst - rhoSecond * rhoThird) ^ 2 := by
  rw [elliptopeBracket]; ring

theorem elliptopeBracket_eq_completedSquare_second (rhoFirst rhoSecond rhoThird : ℝ) :
    elliptopeBracket rhoFirst rhoSecond rhoThird
      = (1 - rhoFirst ^ 2) * (1 - rhoThird ^ 2)
        - (rhoSecond - rhoFirst * rhoThird) ^ 2 := by
  rw [elliptopeBracket]; ring

theorem elliptopeBracket_swap_firstSecond (rhoFirst rhoSecond rhoThird : ℝ) :
    elliptopeBracket rhoFirst rhoSecond rhoThird
      = elliptopeBracket rhoSecond rhoFirst rhoThird := by
  rw [elliptopeBracket, elliptopeBracket]; ring

theorem elliptopeBracket_swap_secondThird (rhoFirst rhoSecond rhoThird : ℝ) :
    elliptopeBracket rhoFirst rhoSecond rhoThird
      = elliptopeBracket rhoFirst rhoThird rhoSecond := by
  rw [elliptopeBracket, elliptopeBracket]; ring

theorem elliptopeBracket_swap_firstThird (rhoFirst rhoSecond rhoThird : ℝ) :
    elliptopeBracket rhoFirst rhoSecond rhoThird
      = elliptopeBracket rhoThird rhoSecond rhoFirst := by
  rw [elliptopeBracket, elliptopeBracket]; ring

/-- **Switching invariance.** Negating a vector of the underlying triple flips exactly
two of the three correlations, and the bracket does not see it. This is the scalar
shadow of the two-graph gauge symmetry: the bracket is a function of the SWITCHING
CLASS, not of the sign pattern. -/
theorem elliptopeBracket_neg_firstSecond (rhoFirst rhoSecond rhoThird : ℝ) :
    elliptopeBracket (-rhoFirst) (-rhoSecond) rhoThird
      = elliptopeBracket rhoFirst rhoSecond rhoThird := by
  rw [elliptopeBracket, elliptopeBracket]; ring

theorem elliptopeBracket_neg_firstThird (rhoFirst rhoSecond rhoThird : ℝ) :
    elliptopeBracket (-rhoFirst) rhoSecond (-rhoThird)
      = elliptopeBracket rhoFirst rhoSecond rhoThird := by
  rw [elliptopeBracket, elliptopeBracket]; ring

theorem elliptopeBracket_neg_secondThird (rhoFirst rhoSecond rhoThird : ℝ) :
    elliptopeBracket rhoFirst (-rhoSecond) (-rhoThird)
      = elliptopeBracket rhoFirst rhoSecond rhoThird := by
  rw [elliptopeBracket, elliptopeBracket]; ring

/-- **The absolute-value gauge, in one line.** The bracket differs from its
all-nonnegative representative by exactly `2 (r1 r2 r3 − |r1 r2 r3|)`. -/
theorem elliptopeBracket_abs (rhoFirst rhoSecond rhoThird : ℝ) :
    elliptopeBracket rhoFirst rhoSecond rhoThird
      = elliptopeBracket |rhoFirst| |rhoSecond| |rhoThird|
        - 2 * |rhoFirst * rhoSecond * rhoThird|
        + 2 * (rhoFirst * rhoSecond * rhoThird) := by
  rw [elliptopeBracket, elliptopeBracket, sq_abs, sq_abs, sq_abs, abs_mul, abs_mul]
  ring

/-- **A coherent triple may be taken all-nonnegative for free.** No case split: the
squares are unchanged by `abs` and the product is its own absolute value. -/
theorem elliptopeBracket_abs_of_coherent {rhoFirst rhoSecond rhoThird : ℝ}
    (hcoherent : 0 ≤ rhoFirst * rhoSecond * rhoThird) :
    elliptopeBracket |rhoFirst| |rhoSecond| |rhoThird|
      = elliptopeBracket rhoFirst rhoSecond rhoThird := by
  rw [elliptopeBracket_abs rhoFirst rhoSecond rhoThird,
    abs_of_nonneg hcoherent]
  ring

/-- **The discriminant of the bracket, read as a quadratic in the pivot-free slot,
is a PRODUCT.** Completing the square is what makes the classical
`sqrt((1 − r1²)(1 − r2²))` appear; this identity is the reason the radicand factors
and therefore the reason it is nonnegative exactly on the compatible square. -/
theorem elliptopeBracket_discriminant (rhoFirst rhoSecond : ℝ) :
    (2 * (rhoFirst * rhoSecond)) ^ 2 + 4 * (1 - rhoFirst ^ 2 - rhoSecond ^ 2)
      = 4 * ((1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2)) := by
  ring

/-! ## 2. The named endpoints and the interval criterion -/

/-- The **upper endpoint** of the interval of admissible third correlations. In angle
coordinates `r = cos phi` this is `cos(phiFirst − phiSecond)`. -/
noncomputable def rootUpper (rhoFirst rhoSecond : ℝ) : ℝ :=
  rhoFirst * rhoSecond + Real.sqrt ((1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2))

/-- The **lower endpoint**; in angle coordinates `cos(phiFirst + phiSecond)`. -/
noncomputable def rootLower (rhoFirst rhoSecond : ℝ) : ℝ :=
  rhoFirst * rhoSecond - Real.sqrt ((1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2))

/-- **Vieta, first coefficient.** No radical survives in the sum. -/
theorem rootLower_add_rootUpper (rhoFirst rhoSecond : ℝ) :
    rootLower rhoFirst rhoSecond + rootUpper rhoFirst rhoSecond
      = 2 * (rhoFirst * rhoSecond) := by
  rw [rootLower, rootUpper]; ring

/-- **Vieta, second coefficient.** No radical survives in the product either, so both
endpoints are algebraic over the rational data of the pair with rational
coefficients — which is what lets an exact decision procedure avoid them entirely. -/
theorem rootLower_mul_rootUpper {rhoFirst rhoSecond : ℝ}
    (hfirst : rhoFirst ^ 2 ≤ 1) (hsecond : rhoSecond ^ 2 ≤ 1) :
    rootLower rhoFirst rhoSecond * rootUpper rhoFirst rhoSecond
      = rhoFirst ^ 2 + rhoSecond ^ 2 - 1 := by
  have hradicand : (0 : ℝ) ≤ (1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hsquare : Real.sqrt ((1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2)) ^ 2
      = (1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2) := Real.sq_sqrt hradicand
  rw [rootLower, rootUpper]
  nlinarith [hsquare]

theorem rootLower_le_rootUpper (rhoFirst rhoSecond : ℝ) :
    rootLower rhoFirst rhoSecond ≤ rootUpper rhoFirst rhoSecond := by
  rw [rootLower, rootUpper]
  linarith [Real.sqrt_nonneg ((1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2))]

/-- **The interval never leaves the compatible range, upper side.** After squaring
this is exactly `(rhoFirst − rhoSecond)² ≥ 0`. -/
theorem rootUpper_le_one {rhoFirst rhoSecond : ℝ} (hfirst : rhoFirst ^ 2 ≤ 1)
    (hsecond : rhoSecond ^ 2 ≤ 1) : rootUpper rhoFirst rhoSecond ≤ 1 := by
  have hradicand : (0 : ℝ) ≤ (1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hsquare : Real.sqrt ((1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2)) ^ 2
      = (1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2) := Real.sq_sqrt hradicand
  have hnonneg : (0 : ℝ) ≤ Real.sqrt ((1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2)) :=
    Real.sqrt_nonneg _
  rw [rootUpper]
  nlinarith [hsquare, hnonneg, sq_nonneg (rhoFirst - rhoSecond)]

/-- **The interval never leaves the compatible range, lower side.** After squaring
this is `(rhoFirst + rhoSecond)² ≥ 0`. -/
theorem neg_one_le_rootLower {rhoFirst rhoSecond : ℝ} (hfirst : rhoFirst ^ 2 ≤ 1)
    (hsecond : rhoSecond ^ 2 ≤ 1) : -1 ≤ rootLower rhoFirst rhoSecond := by
  have hradicand : (0 : ℝ) ≤ (1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hsquare : Real.sqrt ((1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2)) ^ 2
      = (1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2) := Real.sq_sqrt hradicand
  have hnonneg : (0 : ℝ) ≤ Real.sqrt ((1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2)) :=
    Real.sqrt_nonneg _
  rw [rootLower]
  nlinarith [hsquare, hnonneg, sq_nonneg (rhoFirst + rhoSecond)]

/-- **The bracket factors through its two roots.** -/
theorem elliptopeBracket_eq_neg_mul_rootFactors {rhoFirst rhoSecond rhoThird : ℝ}
    (hfirst : rhoFirst ^ 2 ≤ 1) (hsecond : rhoSecond ^ 2 ≤ 1) :
    elliptopeBracket rhoFirst rhoSecond rhoThird
      = -((rhoThird - rootLower rhoFirst rhoSecond)
          * (rhoThird - rootUpper rhoFirst rhoSecond)) := by
  have hradicand : (0 : ℝ) ≤ (1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hsquare : Real.sqrt ((1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2)) ^ 2
      = (1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2) := Real.sq_sqrt hradicand
  rw [elliptopeBracket, rootLower, rootUpper]
  nlinarith [hsquare]

/-- **THE INTERVAL CRITERION.** Given two compatible correlations, the bracket is
nonnegative for exactly the third correlations in the closed interval between the two
roots. -/
theorem elliptopeBracket_nonneg_iff_mem_rootInterval {rhoFirst rhoSecond rhoThird : ℝ}
    (hfirst : rhoFirst ^ 2 ≤ 1) (hsecond : rhoSecond ^ 2 ≤ 1) :
    0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird
      ↔ rootLower rhoFirst rhoSecond ≤ rhoThird
        ∧ rhoThird ≤ rootUpper rhoFirst rhoSecond := by
  have hradicand : (0 : ℝ) ≤ (1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hsquare : Real.sqrt ((1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2)) ^ 2
      = (1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2) := Real.sq_sqrt hradicand
  have hnonneg : (0 : ℝ) ≤ Real.sqrt ((1 - rhoFirst ^ 2) * (1 - rhoSecond ^ 2)) :=
    Real.sqrt_nonneg _
  rw [elliptopeBracket_eq_completedSquare_third, rootLower, rootUpper]
  constructor
  · intro hbracket
    constructor <;> nlinarith [hbracket, hnonneg, hsquare]
  · rintro ⟨hlow, hhigh⟩
    nlinarith [hlow, hhigh, hnonneg, hsquare]

/-- **The strict interval criterion**: strict positivity is the open interval. -/
theorem elliptopeBracket_pos_iff_mem_openRootInterval
    {rhoFirst rhoSecond rhoThird : ℝ} (hfirst : rhoFirst ^ 2 ≤ 1)
    (hsecond : rhoSecond ^ 2 ≤ 1) :
    0 < elliptopeBracket rhoFirst rhoSecond rhoThird
      ↔ rootLower rhoFirst rhoSecond < rhoThird
        ∧ rhoThird < rootUpper rhoFirst rhoSecond := by
  rw [elliptopeBracket_eq_neg_mul_rootFactors hfirst hsecond]
  constructor
  · intro hpos
    have hlower := rootLower_le_rootUpper rhoFirst rhoSecond
    rcases lt_trichotomy rhoThird (rootLower rhoFirst rhoSecond) with hcase | hcase | hcase
    · nlinarith [hpos, hcase, hlower]
    · exfalso; rw [hcase] at hpos; simp at hpos
    · refine ⟨hcase, ?_⟩
      by_contra hle
      push Not at hle
      nlinarith [hpos, hcase, hle]
  · rintro ⟨hlow, hhigh⟩
    nlinarith [hlow, hhigh]

/-- **The equality case of the interval**: the bracket vanishes exactly at the two
endpoints. -/
theorem elliptopeBracket_eq_zero_iff_eq_root {rhoFirst rhoSecond rhoThird : ℝ}
    (hfirst : rhoFirst ^ 2 ≤ 1) (hsecond : rhoSecond ^ 2 ≤ 1) :
    elliptopeBracket rhoFirst rhoSecond rhoThird = 0
      ↔ rhoThird = rootLower rhoFirst rhoSecond
        ∨ rhoThird = rootUpper rhoFirst rhoSecond := by
  rw [elliptopeBracket_eq_neg_mul_rootFactors hfirst hsecond, neg_eq_zero, mul_eq_zero,
    sub_eq_zero, sub_eq_zero]

theorem elliptopeBracket_rootUpper_eq_zero {rhoFirst rhoSecond : ℝ}
    (hfirst : rhoFirst ^ 2 ≤ 1) (hsecond : rhoSecond ^ 2 ≤ 1) :
    elliptopeBracket rhoFirst rhoSecond (rootUpper rhoFirst rhoSecond) = 0 :=
  (elliptopeBracket_eq_zero_iff_eq_root hfirst hsecond).mpr (Or.inr rfl)

theorem elliptopeBracket_rootLower_eq_zero {rhoFirst rhoSecond : ℝ}
    (hfirst : rhoFirst ^ 2 ≤ 1) (hsecond : rhoSecond ^ 2 ≤ 1) :
    elliptopeBracket rhoFirst rhoSecond (rootLower rhoFirst rhoSecond) = 0 :=
  (elliptopeBracket_eq_zero_iff_eq_root hfirst hsecond).mpr (Or.inl rfl)

/-! ## 3. Elliptope membership, and the redundant conjunct -/

/-- Three correlations are **compatible** when each is at most one in absolute value —
the three `2x2` principal minors of the unit-diagonal correlation matrix, in squared
form. -/
def IsCompatibleTriple (rhoFirst rhoSecond rhoThird : ℝ) : Prop :=
  rhoFirst ^ 2 ≤ 1 ∧ rhoSecond ^ 2 ≤ 1 ∧ rhoThird ^ 2 ≤ 1

/-- A triple of correlations is an **elliptope point** when it is compatible and its
bracket is nonnegative. This is `IsElliptopeGoodTriangle` in pure scalars. -/
def IsElliptopePoint (rhoFirst rhoSecond rhoThird : ℝ) : Prop :=
  IsCompatibleTriple rhoFirst rhoSecond rhoThird
    ∧ 0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird

/-- **The third compatibility condition is redundant.** Two compatible edges plus a
nonnegative bracket force the third edge compatible. Mechanizes the observation in
the `dominates_triple_iff_isElliptopeGoodTriangle` docstring that "the edge conditions
are redundant one at a time". -/
theorem sq_le_one_of_two_and_bracket_nonneg {rhoFirst rhoSecond rhoThird : ℝ}
    (hfirst : rhoFirst ^ 2 ≤ 1) (hsecond : rhoSecond ^ 2 ≤ 1)
    (hbracket : 0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird) :
    rhoThird ^ 2 ≤ 1 := by
  rw [elliptopeBracket_eq_completedSquare_first] at hbracket
  rcases lt_or_eq_of_le hsecond with hstrict | hboundary
  · nlinarith [hbracket, sq_nonneg (rhoFirst - rhoSecond * rhoThird), hstrict, hfirst]
  · have hfactor : rhoFirst = rhoSecond * rhoThird := by
      have hzero : (rhoFirst - rhoSecond * rhoThird) ^ 2 ≤ 0 := by
        nlinarith [hbracket, hboundary]
      have := sq_nonneg (rhoFirst - rhoSecond * rhoThird)
      have heq : (rhoFirst - rhoSecond * rhoThird) ^ 2 = 0 := le_antisymm hzero this
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp heq
      linarith [this]
    nlinarith [hfirst, hfactor, hboundary]

/-- **Elliptope membership needs only two of the three compatibility conditions.** -/
theorem isElliptopePoint_iff_two_sq_le_one (rhoFirst rhoSecond rhoThird : ℝ) :
    IsElliptopePoint rhoFirst rhoSecond rhoThird
      ↔ rhoFirst ^ 2 ≤ 1 ∧ rhoSecond ^ 2 ≤ 1
        ∧ 0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird := by
  constructor
  · rintro ⟨⟨hfirst, hsecond, _⟩, hbracket⟩
    exact ⟨hfirst, hsecond, hbracket⟩
  · rintro ⟨hfirst, hsecond, hbracket⟩
    exact ⟨⟨hfirst, hsecond,
      sq_le_one_of_two_and_bracket_nonneg hfirst hsecond hbracket⟩, hbracket⟩

/-- **The elliptope is closed under switching.** Negating two of the three
correlations — the move induced by negating one underlying vector — leaves membership
alone, so the criterion is a statement about the switching class. -/
theorem isElliptopePoint_neg_firstSecond (rhoFirst rhoSecond rhoThird : ℝ) :
    IsElliptopePoint (-rhoFirst) (-rhoSecond) rhoThird
      ↔ IsElliptopePoint rhoFirst rhoSecond rhoThird := by
  rw [IsElliptopePoint, IsElliptopePoint, IsCompatibleTriple, IsCompatibleTriple,
    elliptopeBracket_neg_firstSecond, neg_pow, neg_pow]
  norm_num

theorem isElliptopePoint_neg_firstThird (rhoFirst rhoSecond rhoThird : ℝ) :
    IsElliptopePoint (-rhoFirst) rhoSecond (-rhoThird)
      ↔ IsElliptopePoint rhoFirst rhoSecond rhoThird := by
  rw [IsElliptopePoint, IsElliptopePoint, IsCompatibleTriple, IsCompatibleTriple,
    elliptopeBracket_neg_firstThird, neg_pow, neg_pow]
  norm_num

theorem isElliptopePoint_neg_secondThird (rhoFirst rhoSecond rhoThird : ℝ) :
    IsElliptopePoint rhoFirst (-rhoSecond) (-rhoThird)
      ↔ IsElliptopePoint rhoFirst rhoSecond rhoThird := by
  rw [IsElliptopePoint, IsElliptopePoint, IsCompatibleTriple, IsCompatibleTriple,
    elliptopeBracket_neg_secondThird, neg_pow, neg_pow]
  norm_num

/-- **A coherent triple is an elliptope point exactly when its absolute values are.**
The gauge move, at the level of membership. -/
theorem isElliptopePoint_abs_iff_of_coherent {rhoFirst rhoSecond rhoThird : ℝ}
    (hcoherent : 0 ≤ rhoFirst * rhoSecond * rhoThird) :
    IsElliptopePoint |rhoFirst| |rhoSecond| |rhoThird|
      ↔ IsElliptopePoint rhoFirst rhoSecond rhoThird := by
  rw [IsElliptopePoint, IsElliptopePoint, IsCompatibleTriple, IsCompatibleTriple,
    elliptopeBracket_abs_of_coherent hcoherent, sq_abs, sq_abs, sq_abs]

/-- **Elliptope membership as a two-sided inequality on one correlation.** -/
theorem isElliptopePoint_iff_mem_rootInterval {rhoFirst rhoSecond rhoThird : ℝ}
    (hfirst : rhoFirst ^ 2 ≤ 1) (hsecond : rhoSecond ^ 2 ≤ 1) :
    IsElliptopePoint rhoFirst rhoSecond rhoThird
      ↔ rootLower rhoFirst rhoSecond ≤ rhoThird
        ∧ rhoThird ≤ rootUpper rhoFirst rhoSecond := by
  rw [isElliptopePoint_iff_two_sq_le_one,
    elliptopeBracket_nonneg_iff_mem_rootInterval hfirst hsecond]
  exact ⟨fun hpoint => hpoint.2.2, fun hinterval => ⟨hfirst, hsecond, hinterval⟩⟩

/-! ## 4. The interface to the matrix normal form

`Gtz.Design.RhoNormalForm` owns the unit-diagonal correlation matrix, its determinant
identity, and the congruence proof that `Dominates` is positive semidefiniteness of
that matrix. Nothing here duplicates it. What is needed is one lemma per side so that
the two vocabularies compose: the right-hand side of that file's
`posSemidef_correlationMatrixThree_iff` is, conjunct for conjunct, this unfolding of
`IsElliptopePoint`. -/

/-- **The bridge to `Gtz.Design.RhoNormalForm`.** `IsElliptopePoint` unfolded into the
exact conjunction shape that the matrix-side criterion produces, so a consumer can
rewrite between "the correlation matrix is PSD" and "the correlation triple is an
elliptope point" in one step. -/
theorem isElliptopePoint_iff_sq_le_one_and_bracket_nonneg
    (rhoFirst rhoSecond rhoThird : ℝ) :
    IsElliptopePoint rhoFirst rhoSecond rhoThird
      ↔ rhoFirst ^ 2 ≤ 1 ∧ rhoSecond ^ 2 ≤ 1 ∧ rhoThird ^ 2 ≤ 1
        ∧ 0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird := by
  rw [IsElliptopePoint, IsCompatibleTriple]
  exact ⟨fun hpoint => ⟨hpoint.1.1, hpoint.1.2.1, hpoint.1.2.2, hpoint.2⟩,
    fun hunfolded => ⟨⟨hunfolded.1, hunfolded.2.1, hunfolded.2.2.1⟩, hunfolded.2.2.2⟩⟩

/-! ## 5. The box, sharp, with its four equality points -/

/-- **THE BOX COROLLARY, with a two-term proof.** Three correlations at most one half
in magnitude give a nonnegative bracket. The negative parts are bounded separately —
`−r1² − r2² − r3² ≥ −3/4` and `2 r1 r2 r3 ≥ −1/4` — and add to exactly zero, which is
why the bound is tight and why the equality set is what it is. -/
theorem elliptopeBracket_nonneg_of_sq_le_quarter {rhoFirst rhoSecond rhoThird : ℝ}
    (hfirst : rhoFirst ^ 2 ≤ 1 / 4) (hsecond : rhoSecond ^ 2 ≤ 1 / 4)
    (hthird : rhoThird ^ 2 ≤ 1 / 4) :
    0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird := by
  rw [elliptopeBracket]
  nlinarith [sq_nonneg (rhoFirst * rhoSecond - rhoThird),
    sq_nonneg (rhoFirst * rhoSecond + rhoThird), sq_nonneg (rhoFirst + rhoSecond),
    sq_nonneg (rhoFirst - rhoSecond), hfirst, hsecond, hthird]

theorem elliptopeBracket_nonneg_of_abs_le_half {rhoFirst rhoSecond rhoThird : ℝ}
    (hfirst : |rhoFirst| ≤ 1 / 2) (hsecond : |rhoSecond| ≤ 1 / 2)
    (hthird : |rhoThird| ≤ 1 / 2) :
    0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird := by
  refine elliptopeBracket_nonneg_of_sq_le_quarter ?_ ?_ ?_
  · nlinarith [sq_abs rhoFirst, abs_nonneg rhoFirst, hfirst]
  · nlinarith [sq_abs rhoSecond, abs_nonneg rhoSecond, hsecond]
  · nlinarith [sq_abs rhoThird, abs_nonneg rhoThird, hthird]

/-- **The box is inside the elliptope**, compatibility included. -/
theorem isElliptopePoint_of_sq_le_quarter {rhoFirst rhoSecond rhoThird : ℝ}
    (hfirst : rhoFirst ^ 2 ≤ 1 / 4) (hsecond : rhoSecond ^ 2 ≤ 1 / 4)
    (hthird : rhoThird ^ 2 ≤ 1 / 4) :
    IsElliptopePoint rhoFirst rhoSecond rhoThird :=
  ⟨⟨by linarith, by linarith, by linarith⟩,
    elliptopeBracket_nonneg_of_sq_le_quarter hfirst hsecond hthird⟩

/-- **EVERY FAILING TRIPLE CARRIES AN EDGE ABOVE ONE HALF.** The contrapositive of the
box corollary, stated because the campaign's write-up derives it through the failure
taxonomy when it needs nothing of the kind. -/
theorem exists_sq_gt_quarter_of_elliptopeBracket_neg {rhoFirst rhoSecond rhoThird : ℝ}
    (hfail : elliptopeBracket rhoFirst rhoSecond rhoThird < 0) :
    1 / 4 < rhoFirst ^ 2 ∨ 1 / 4 < rhoSecond ^ 2 ∨ 1 / 4 < rhoThird ^ 2 := by
  by_contra hall
  push Not at hall
  exact absurd (elliptopeBracket_nonneg_of_sq_le_quarter hall.1 hall.2.1 hall.2.2)
    (not_le.mpr hfail)

/-- **The four Mercedes points, the equality set of the box.** Equality in the box
bound forces both of its two term bounds tight: every square exactly `1/4`, and the
product exactly `−1/8`. -/
theorem elliptopeBracket_eq_zero_iff_mercedes {rhoFirst rhoSecond rhoThird : ℝ}
    (hfirst : rhoFirst ^ 2 ≤ 1 / 4) (hsecond : rhoSecond ^ 2 ≤ 1 / 4)
    (hthird : rhoThird ^ 2 ≤ 1 / 4) :
    elliptopeBracket rhoFirst rhoSecond rhoThird = 0
      ↔ rhoFirst ^ 2 = 1 / 4 ∧ rhoSecond ^ 2 = 1 / 4 ∧ rhoThird ^ 2 = 1 / 4
        ∧ rhoFirst * rhoSecond * rhoThird = -(1 / 8) := by
  constructor
  · intro hzero
    rw [elliptopeBracket] at hzero
    have habsFirst : |rhoFirst| ≤ 1 / 2 := by
      nlinarith [sq_abs rhoFirst, abs_nonneg rhoFirst, hfirst]
    have habsSecond : |rhoSecond| ≤ 1 / 2 := by
      nlinarith [sq_abs rhoSecond, abs_nonneg rhoSecond, hsecond]
    have habsThird : |rhoThird| ≤ 1 / 2 := by
      nlinarith [sq_abs rhoThird, abs_nonneg rhoThird, hthird]
    have hpairBound : |rhoFirst| * |rhoSecond| ≤ 1 / 4 := by
      nlinarith [abs_nonneg rhoFirst, abs_nonneg rhoSecond, habsFirst, habsSecond]
    have hproductBound : |rhoFirst * rhoSecond * rhoThird| ≤ 1 / 8 := by
      rw [abs_mul, abs_mul]
      nlinarith [hpairBound, abs_nonneg rhoThird, habsThird,
        mul_nonneg (abs_nonneg rhoFirst) (abs_nonneg rhoSecond)]
    have hproductLower : -(1 / 8 : ℝ) ≤ rhoFirst * rhoSecond * rhoThird := by
      have := neg_abs_le (rhoFirst * rhoSecond * rhoThird)
      linarith [hproductBound, this]
    have hsquareSum : rhoFirst ^ 2 + rhoSecond ^ 2 + rhoThird ^ 2 = 3 / 4 := by
      linarith [hzero, hproductLower, hfirst, hsecond, hthird]
    have hproductValue : rhoFirst * rhoSecond * rhoThird = -(1 / 8) := by linarith
    refine ⟨by linarith, by linarith, by linarith, hproductValue⟩
  · rintro ⟨hfirstEq, hsecondEq, hthirdEq, hproductEq⟩
    rw [elliptopeBracket, hfirstEq, hsecondEq, hthirdEq, hproductEq]
    norm_num

/-- **The four Mercedes points, enumerated.** The equality set of the box is exactly
the four sign patterns with an ODD number of minus signs — precisely the four vertices
at which the underlying vectors can be a regular simplex. -/
theorem elliptopeBracket_eq_zero_iff_mercedesPoint {rhoFirst rhoSecond rhoThird : ℝ}
    (hfirst : rhoFirst ^ 2 ≤ 1 / 4) (hsecond : rhoSecond ^ 2 ≤ 1 / 4)
    (hthird : rhoThird ^ 2 ≤ 1 / 4) :
    elliptopeBracket rhoFirst rhoSecond rhoThird = 0
      ↔ (rhoFirst = -(1 / 2) ∧ rhoSecond = -(1 / 2) ∧ rhoThird = -(1 / 2))
        ∨ (rhoFirst = -(1 / 2) ∧ rhoSecond = 1 / 2 ∧ rhoThird = 1 / 2)
        ∨ (rhoFirst = 1 / 2 ∧ rhoSecond = -(1 / 2) ∧ rhoThird = 1 / 2)
        ∨ (rhoFirst = 1 / 2 ∧ rhoSecond = 1 / 2 ∧ rhoThird = -(1 / 2)) := by
  constructor
  · intro hzero
    obtain ⟨hfirstSq, hsecondSq, hthirdSq, hproduct⟩ :=
      (elliptopeBracket_eq_zero_iff_mercedes hfirst hsecond hthird).mp hzero
    have hfirstSign : rhoFirst = 1 / 2 ∨ rhoFirst = -(1 / 2) := by
      have hfactor : (rhoFirst - 1 / 2) * (rhoFirst + 1 / 2) = 0 := by nlinarith [hfirstSq]
      rcases mul_eq_zero.mp hfactor with hroot | hroot
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hsecondSign : rhoSecond = 1 / 2 ∨ rhoSecond = -(1 / 2) := by
      have hfactor : (rhoSecond - 1 / 2) * (rhoSecond + 1 / 2) = 0 := by nlinarith [hsecondSq]
      rcases mul_eq_zero.mp hfactor with hroot | hroot
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hthirdSign : rhoThird = 1 / 2 ∨ rhoThird = -(1 / 2) := by
      have hfactor : (rhoThird - 1 / 2) * (rhoThird + 1 / 2) = 0 := by nlinarith [hthirdSq]
      rcases mul_eq_zero.mp hfactor with hroot | hroot
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hfirstSign with hfirstValue | hfirstValue <;>
      rcases hsecondSign with hsecondValue | hsecondValue <;>
      rcases hthirdSign with hthirdValue | hthirdValue <;>
      rw [hfirstValue, hsecondValue, hthirdValue] at hproduct ⊢ <;>
      revert hproduct <;> norm_num
  · rintro (⟨hfirstValue, hsecondValue, hthirdValue⟩ | ⟨hfirstValue, hsecondValue, hthirdValue⟩
      | ⟨hfirstValue, hsecondValue, hthirdValue⟩ | ⟨hfirstValue, hsecondValue, hthirdValue⟩) <;>
    rw [elliptopeBracket, hfirstValue, hsecondValue, hthirdValue] <;> norm_num

/-- The Mercedes point itself: three correlations at `−1/2` sit exactly on the
elliptope boundary. This is the regular tetrahedron's triple. -/
theorem elliptopeBracket_mercedes_allNegative :
    elliptopeBracket (-(1 / 2)) (-(1 / 2)) (-(1 / 2)) = 0 := by
  rw [elliptopeBracket]; norm_num

theorem elliptopeBracket_mercedes_firstNegative :
    elliptopeBracket (-(1 / 2)) (1 / 2) (1 / 2) = 0 := by
  rw [elliptopeBracket]; norm_num

theorem elliptopeBracket_mercedes_secondNegative :
    elliptopeBracket (1 / 2) (-(1 / 2)) (1 / 2) = 0 := by
  rw [elliptopeBracket]; norm_num

theorem elliptopeBracket_mercedes_thirdNegative :
    elliptopeBracket (1 / 2) (1 / 2) (-(1 / 2)) = 0 := by
  rw [elliptopeBracket]; norm_num

/-- The four box vertices with POSITIVE product are strictly interior, at value
`1/2` — so the minimum over the closed box really is attained only on the negative
orthant of sign patterns. -/
theorem elliptopeBracket_boxVertex_allPositive :
    elliptopeBracket (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by
  rw [elliptopeBracket]; norm_num

/-- **The constant one half is sharp.** For every larger symmetric radius the
symmetric NEGATIVE vertex leaves the elliptope, with the exact deficit
`−(2c − 1)(c + 1)²`. -/
theorem elliptopeBracket_symmetricNegative (radius : ℝ) :
    elliptopeBracket (-radius) (-radius) (-radius)
      = -((2 * radius - 1) * (radius + 1) ^ 2) := by
  rw [elliptopeBracket]; ring

theorem elliptopeBracket_neg_of_half_lt {radius : ℝ} (hradius : 1 / 2 < radius) :
    elliptopeBracket (-radius) (-radius) (-radius) < 0 := by
  rw [elliptopeBracket_symmetricNegative]
  have hshiftPos : (0 : ℝ) < (radius + 1) ^ 2 := pow_pos (by linarith) 2
  have hdeficit : (0 : ℝ) < (2 * radius - 1) * (radius + 1) ^ 2 :=
    mul_pos (by linarith) hshiftPos
  linarith

/-! ## 6. The equilateral slice -/

/-- **The equilateral factorization.** Pure `ring`. -/
theorem elliptopeBracket_equilateral (rho : ℝ) :
    elliptopeBracket rho rho rho = (1 - rho) ^ 2 * (1 + 2 * rho) := by
  rw [elliptopeBracket]; ring

/-- **The equilateral criterion, as an iff with no upper bound.** The bracket of an
equal-correlation triple is nonnegative exactly for `rho ≥ −1/2`; the pen statement
`rho ∈ [−1/2, 1]` carries a redundant right endpoint, which belongs to compatibility
rather than to the determinant. -/
theorem elliptopeBracket_equilateral_nonneg_iff (rho : ℝ) :
    0 ≤ elliptopeBracket rho rho rho ↔ -(1 / 2) ≤ rho := by
  rw [elliptopeBracket_equilateral]
  constructor
  · intro hnonneg
    by_contra hlt
    push Not at hlt
    have hshiftPos : (0 : ℝ) < (1 - rho) ^ 2 := pow_pos (by linarith) 2
    have hslopeNeg : (1 : ℝ) + 2 * rho < 0 := by linarith
    nlinarith [mul_pos hshiftPos (neg_pos.mpr hslopeNeg), hnonneg]
  · intro hbound
    nlinarith [hbound, sq_nonneg (1 - rho)]

/-- The equal-correlation elliptope slice is exactly `[−1/2, 1]`. -/
theorem isElliptopePoint_equilateral_iff (rho : ℝ) :
    IsElliptopePoint rho rho rho ↔ -(1 / 2) ≤ rho ∧ rho ≤ 1 := by
  rw [IsElliptopePoint, IsCompatibleTriple, elliptopeBracket_equilateral_nonneg_iff]
  constructor
  · rintro ⟨⟨hsquare, _, _⟩, hlow⟩
    exact ⟨hlow, by nlinarith [hsquare, hlow]⟩
  · rintro ⟨hlow, hhigh⟩
    have hsquare : rho ^ 2 ≤ 1 := by nlinarith [hlow, hhigh]
    exact ⟨⟨hsquare, hsquare, hsquare⟩, hlow⟩

/-- **The equal-magnitude slice: the verdict is carried by the SIGN alone.** When all
three squared correlations agree, the sign-blind part of the bracket collapses to the
constant `1 − 3 s` and everything else is the oriented product. This is the general
form of `icosaDesign_elliptopeBracket_of_distinct`, which is the case `s = 9/20`. -/
theorem elliptopeBracket_of_sq_eq {rhoFirst rhoSecond rhoThird squaredValue : ℝ}
    (hfirst : rhoFirst ^ 2 = squaredValue) (hsecond : rhoSecond ^ 2 = squaredValue)
    (hthird : rhoThird ^ 2 = squaredValue) :
    elliptopeBracket rhoFirst rhoSecond rhoThird
      = 1 - 3 * squaredValue + 2 * (rhoFirst * rhoSecond * rhoThird) := by
  rw [elliptopeBracket, hfirst, hsecond, hthird]; ring

/-- **The equal-magnitude criterion.** Domination of an equal-magnitude triple is one
inequality on the ORIENTED product, with a threshold depending only on the common
square. At `s = 9/20` this is `icosaDesign_dominates_iff_pairingProduct`; at
`s = 1/4` the threshold is `−1/8`, the Mercedes value. -/
theorem elliptopeBracket_nonneg_iff_of_sq_eq {rhoFirst rhoSecond rhoThird squaredValue : ℝ}
    (hfirst : rhoFirst ^ 2 = squaredValue) (hsecond : rhoSecond ^ 2 = squaredValue)
    (hthird : rhoThird ^ 2 = squaredValue) :
    0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird
      ↔ (3 * squaredValue - 1) / 2 ≤ rhoFirst * rhoSecond * rhoThird := by
  rw [elliptopeBracket_of_sq_eq hfirst hsecond hthird]
  constructor <;> intro hbound <;> linarith

/-- **The bracket alone certifies nothing.** Three parallel copies of a leverage-three
atom give `rho ≡ 3/2`, bracket `+1`, and no domination. Mechanizes the numerical claim
made in the `GoodTripleGraph` header and in the `elliptopeBracket` docstring. -/
theorem elliptopeBracket_threeHalves_eq_one :
    elliptopeBracket (3 / 2) (3 / 2) (3 / 2) = 1 := by
  rw [elliptopeBracket]; norm_num

theorem not_isElliptopePoint_threeHalves :
    ¬ IsElliptopePoint (3 / 2) (3 / 2) (3 / 2) := by
  rintro ⟨⟨hsquare, _, _⟩, _⟩
  norm_num at hsquare

/-! ## 7. The failure taxonomy

Three mutually exclusive ways to miss the elliptope, exhausting all of them, with a
sharp lower bound on the largest correlation in each failing class. -/

/-- **WILD**: some correlation exceeds one in magnitude. Equivalently, not compatible.
Independent of the bracket: the wild triple `rho ≡ 3/2` has bracket `+1`. -/
def IsWildTriple (rhoFirst rhoSecond rhoThird : ℝ) : Prop :=
  1 < rhoFirst ^ 2 ∨ 1 < rhoSecond ^ 2 ∨ 1 < rhoThird ^ 2

/-- **COHERENT FAILURE**: compatible, nonnegative oriented product, negative bracket.
The product hypothesis is `≥ 0` and not `> 0`; with a strict reading the trichotomy is
NOT exhaustive, and the product-zero witness `(0, r, r)` is a genuine failure. -/
def IsCoherentFailingTriple (rhoFirst rhoSecond rhoThird : ℝ) : Prop :=
  IsCompatibleTriple rhoFirst rhoSecond rhoThird
    ∧ 0 ≤ rhoFirst * rhoSecond * rhoThird
    ∧ elliptopeBracket rhoFirst rhoSecond rhoThird < 0

/-- **FRUSTRATED FAILURE**: compatible, negative oriented product, negative bracket. -/
def IsFrustratedFailingTriple (rhoFirst rhoSecond rhoThird : ℝ) : Prop :=
  IsCompatibleTriple rhoFirst rhoSecond rhoThird
    ∧ rhoFirst * rhoSecond * rhoThird < 0
    ∧ elliptopeBracket rhoFirst rhoSecond rhoThird < 0

theorem isWildTriple_iff_not_isCompatibleTriple (rhoFirst rhoSecond rhoThird : ℝ) :
    IsWildTriple rhoFirst rhoSecond rhoThird
      ↔ ¬ IsCompatibleTriple rhoFirst rhoSecond rhoThird := by
  rw [IsWildTriple, IsCompatibleTriple]
  constructor
  · rintro (hwild | hwild | hwild) ⟨hfirst, hsecond, hthird⟩ <;> linarith
  · intro hnot
    by_contra hall
    push Not at hall
    exact hnot ⟨hall.1, hall.2.1, hall.2.2⟩

/-! ### The classifier -/

/-- The four-valued verdict on a correlation triple. -/
inductive ElliptopeClass where
  | inside
  | wild
  | coherentFailure
  | frustratedFailure

/-- The Prop-valued classifier. -/
def HasElliptopeClass (rhoFirst rhoSecond rhoThird : ℝ) : ElliptopeClass → Prop
  | .inside => IsElliptopePoint rhoFirst rhoSecond rhoThird
  | .wild => IsWildTriple rhoFirst rhoSecond rhoThird
  | .coherentFailure => IsCoherentFailingTriple rhoFirst rhoSecond rhoThird
  | .frustratedFailure => IsFrustratedFailingTriple rhoFirst rhoSecond rhoThird

theorem not_isWildTriple_of_isElliptopePoint {rhoFirst rhoSecond rhoThird : ℝ}
    (hpoint : IsElliptopePoint rhoFirst rhoSecond rhoThird) :
    ¬ IsWildTriple rhoFirst rhoSecond rhoThird := by
  rw [isWildTriple_iff_not_isCompatibleTriple]
  exact not_not_intro hpoint.1

theorem not_isWildTriple_of_isCoherentFailingTriple {rhoFirst rhoSecond rhoThird : ℝ}
    (hcoherent : IsCoherentFailingTriple rhoFirst rhoSecond rhoThird) :
    ¬ IsWildTriple rhoFirst rhoSecond rhoThird := by
  rw [isWildTriple_iff_not_isCompatibleTriple]
  exact not_not_intro hcoherent.1

theorem not_isWildTriple_of_isFrustratedFailingTriple {rhoFirst rhoSecond rhoThird : ℝ}
    (hfrustrated : IsFrustratedFailingTriple rhoFirst rhoSecond rhoThird) :
    ¬ IsWildTriple rhoFirst rhoSecond rhoThird := by
  rw [isWildTriple_iff_not_isCompatibleTriple]
  exact not_not_intro hfrustrated.1

theorem not_isCoherentFailingTriple_of_isElliptopePoint {rhoFirst rhoSecond rhoThird : ℝ}
    (hpoint : IsElliptopePoint rhoFirst rhoSecond rhoThird) :
    ¬ IsCoherentFailingTriple rhoFirst rhoSecond rhoThird := by
  rintro ⟨_, _, hfail⟩
  linarith [hpoint.2]

theorem not_isFrustratedFailingTriple_of_isElliptopePoint {rhoFirst rhoSecond rhoThird : ℝ}
    (hpoint : IsElliptopePoint rhoFirst rhoSecond rhoThird) :
    ¬ IsFrustratedFailingTriple rhoFirst rhoSecond rhoThird := by
  rintro ⟨_, _, hfail⟩
  linarith [hpoint.2]

theorem not_isFrustratedFailingTriple_of_isCoherentFailingTriple
    {rhoFirst rhoSecond rhoThird : ℝ}
    (hcoherent : IsCoherentFailingTriple rhoFirst rhoSecond rhoThird) :
    ¬ IsFrustratedFailingTriple rhoFirst rhoSecond rhoThird := by
  rintro ⟨_, hnegative, _⟩
  linarith [hcoherent.2.1]

/-- **The classification is exhaustive.** -/
theorem exists_hasElliptopeClass (rhoFirst rhoSecond rhoThird : ℝ) :
    ∃ elliptopeClass, HasElliptopeClass rhoFirst rhoSecond rhoThird elliptopeClass := by
  by_cases hcompatible : IsCompatibleTriple rhoFirst rhoSecond rhoThird
  · rcases le_or_gt 0 (elliptopeBracket rhoFirst rhoSecond rhoThird) with hbracket | hbracket
    · exact ⟨ElliptopeClass.inside, hcompatible, hbracket⟩
    · rcases le_or_gt 0 (rhoFirst * rhoSecond * rhoThird) with hproduct | hproduct
      · exact ⟨ElliptopeClass.coherentFailure, hcompatible, hproduct, hbracket⟩
      · exact ⟨ElliptopeClass.frustratedFailure, hcompatible, hproduct, hbracket⟩
  · exact ⟨ElliptopeClass.wild,
      (isWildTriple_iff_not_isCompatibleTriple rhoFirst rhoSecond rhoThird).mpr hcompatible⟩

/-- **The classification is mutually exclusive.** -/
theorem hasElliptopeClass_unique {rhoFirst rhoSecond rhoThird : ℝ}
    {classFirst classSecond : ElliptopeClass}
    (hFirst : HasElliptopeClass rhoFirst rhoSecond rhoThird classFirst)
    (hSecond : HasElliptopeClass rhoFirst rhoSecond rhoThird classSecond) :
    classFirst = classSecond := by
  cases classFirst <;> cases classSecond
  · rfl
  · exact absurd hSecond (not_isWildTriple_of_isElliptopePoint hFirst)
  · exact absurd hSecond (not_isCoherentFailingTriple_of_isElliptopePoint hFirst)
  · exact absurd hSecond (not_isFrustratedFailingTriple_of_isElliptopePoint hFirst)
  · exact absurd hFirst (not_isWildTriple_of_isElliptopePoint hSecond)
  · rfl
  · exact absurd hFirst (not_isWildTriple_of_isCoherentFailingTriple hSecond)
  · exact absurd hFirst (not_isWildTriple_of_isFrustratedFailingTriple hSecond)
  · exact absurd hFirst (not_isCoherentFailingTriple_of_isElliptopePoint hSecond)
  · exact absurd hSecond (not_isWildTriple_of_isCoherentFailingTriple hFirst)
  · rfl
  · exact absurd hSecond (not_isFrustratedFailingTriple_of_isCoherentFailingTriple hFirst)
  · exact absurd hFirst (not_isFrustratedFailingTriple_of_isElliptopePoint hSecond)
  · exact absurd hSecond (not_isWildTriple_of_isFrustratedFailingTriple hFirst)
  · exact absurd hFirst (not_isFrustratedFailingTriple_of_isCoherentFailingTriple hSecond)
  · rfl

/-- **THE DECISION PROCEDURE.** Every correlation triple has exactly one verdict. -/
theorem existsUnique_hasElliptopeClass (rhoFirst rhoSecond rhoThird : ℝ) :
    ∃! elliptopeClass, HasElliptopeClass rhoFirst rhoSecond rhoThird elliptopeClass := by
  obtain ⟨elliptopeClass, hclass⟩ := exists_hasElliptopeClass rhoFirst rhoSecond rhoThird
  exact ⟨elliptopeClass, hclass, fun other hother => hasElliptopeClass_unique hother hclass⟩

/-- **Failure is exactly the three failing classes.** -/
theorem not_isElliptopePoint_iff_failingClass (rhoFirst rhoSecond rhoThird : ℝ) :
    ¬ IsElliptopePoint rhoFirst rhoSecond rhoThird
      ↔ IsWildTriple rhoFirst rhoSecond rhoThird
        ∨ IsCoherentFailingTriple rhoFirst rhoSecond rhoThird
        ∨ IsFrustratedFailingTriple rhoFirst rhoSecond rhoThird := by
  constructor
  · intro hnot
    obtain ⟨elliptopeClass, hclass⟩ := exists_hasElliptopeClass rhoFirst rhoSecond rhoThird
    cases elliptopeClass
    · exact absurd hclass hnot
    · exact Or.inl hclass
    · exact Or.inr (Or.inl hclass)
    · exact Or.inr (Or.inr hclass)
  · rintro (hwild | hcoherent | hfrustrated) hpoint
    · exact not_isWildTriple_of_isElliptopePoint hpoint hwild
    · exact not_isCoherentFailingTriple_of_isElliptopePoint hpoint hcoherent
    · exact not_isFrustratedFailingTriple_of_isElliptopePoint hpoint hfrustrated

/-! ### What each failing class costs

The pen taxonomy asserts a single threshold `1/2` for every failure. The two sign
classes in fact have DIFFERENT sharp thresholds, and both are attained. -/

/-- **The coherent clause, with its exact hypothesis.** A coherent failure whose
smallest correlation in magnitude is the first one has its other two squares summing
above one. No compatibility hypothesis is needed: `rhoSecond² + rhoThird² ≤ 1` already
supplies it. -/
theorem sum_sq_gt_one_of_coherentFailure_of_least {rhoFirst rhoSecond rhoThird : ℝ}
    (hcoherent : 0 ≤ rhoFirst * rhoSecond * rhoThird)
    (hleastSecond : rhoFirst ^ 2 ≤ rhoSecond ^ 2)
    (hleastThird : rhoFirst ^ 2 ≤ rhoThird ^ 2)
    (hfail : elliptopeBracket rhoFirst rhoSecond rhoThird < 0) :
    1 < rhoSecond ^ 2 + rhoThird ^ 2 := by
  rw [elliptopeBracket_eq_completedSquare_first] at hfail
  by_contra hle
  push Not at hle
  have hstep : 1 - rhoSecond ^ 2 - rhoThird ^ 2
      < rhoFirst ^ 2 - 2 * (rhoFirst * rhoSecond * rhoThird) := by nlinarith [hfail]
  have hgap : 0 < rhoFirst ^ 2 - 2 * (rhoFirst * rhoSecond * rhoThird) := by linarith
  have hsquare : (rhoFirst ^ 2) ^ 2
      > 4 * (rhoFirst ^ 2 * (rhoSecond ^ 2 * rhoThird ^ 2)) := by
    nlinarith [hgap, hcoherent, sq_nonneg (rhoFirst * rhoSecond * rhoThird)]
  have hfirstPos : 0 < rhoFirst ^ 2 := by nlinarith [hsquare, sq_nonneg (rhoFirst ^ 2)]
  have hsecondPos : 0 < rhoSecond ^ 2 := lt_of_lt_of_le hfirstPos hleastSecond
  have hthirdPos : 0 < rhoThird ^ 2 := lt_of_lt_of_le hfirstPos hleastThird
  have hcancel : 4 * (rhoSecond ^ 2 * rhoThird ^ 2) < rhoFirst ^ 2 := by
    nlinarith [hsquare, hfirstPos]
  have hthirdQuarter : rhoThird ^ 2 < 1 / 4 := by
    nlinarith [hcancel, hleastSecond, hsecondPos]
  have hsecondQuarter : rhoSecond ^ 2 < 1 / 4 := by
    nlinarith [hcancel, hleastThird, hthirdPos]
  linarith

/-- **The minimality hypothesis cannot be dropped.** At `(3/2, 1/10, 1/10)` the
product is strictly positive, the bracket strictly negative, and the other two squares
sum to `1/50`. The isolated correlation must be the SMALLEST in magnitude, not merely
some chosen one. -/
theorem coherentFailure_needs_least :
    0 < (3 / 2 : ℝ) * (1 / 10) * (1 / 10)
      ∧ elliptopeBracket (3 / 2) (1 / 10) (1 / 10) < 0
      ∧ ¬ (1 : ℝ) < (1 / 10 : ℝ) ^ 2 + (1 / 10 : ℝ) ^ 2 := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  rw [elliptopeBracket]; norm_num

/-- The class form: some pair of squares in a coherent failure sums above one. -/
theorem exists_pairSumSq_gt_one_of_isCoherentFailingTriple {rhoFirst rhoSecond rhoThird : ℝ}
    (hclass : IsCoherentFailingTriple rhoFirst rhoSecond rhoThird) :
    1 < rhoSecond ^ 2 + rhoThird ^ 2 ∨ 1 < rhoFirst ^ 2 + rhoThird ^ 2
      ∨ 1 < rhoFirst ^ 2 + rhoSecond ^ 2 := by
  obtain ⟨_, hcoherent, hfail⟩ := hclass
  have hcoherentSecond : 0 ≤ rhoSecond * rhoFirst * rhoThird := by
    rw [show rhoSecond * rhoFirst * rhoThird = rhoFirst * rhoSecond * rhoThird from by ring]
    exact hcoherent
  have hcoherentThird : 0 ≤ rhoThird * rhoFirst * rhoSecond := by
    rw [show rhoThird * rhoFirst * rhoSecond = rhoFirst * rhoSecond * rhoThird from by ring]
    exact hcoherent
  have hfailSecond : elliptopeBracket rhoSecond rhoFirst rhoThird < 0 := by
    rw [← elliptopeBracket_swap_firstSecond]; exact hfail
  have hfailThird : elliptopeBracket rhoThird rhoFirst rhoSecond < 0 := by
    rw [show elliptopeBracket rhoThird rhoFirst rhoSecond
        = elliptopeBracket rhoFirst rhoSecond rhoThird from by
      rw [elliptopeBracket, elliptopeBracket]; ring]
    exact hfail
  rcases le_total (rhoFirst ^ 2) (rhoSecond ^ 2) with hfirstSecond | hfirstSecond
  · rcases le_total (rhoFirst ^ 2) (rhoThird ^ 2) with hfirstThird | hfirstThird
    · exact Or.inl (sum_sq_gt_one_of_coherentFailure_of_least hcoherent hfirstSecond
        hfirstThird hfail)
    · exact Or.inr (Or.inr (sum_sq_gt_one_of_coherentFailure_of_least hcoherentThird
        hfirstThird (le_trans hfirstThird hfirstSecond) hfailThird))
  · rcases le_total (rhoSecond ^ 2) (rhoThird ^ 2) with hsecondThird | hsecondThird
    · exact Or.inr (Or.inl (sum_sq_gt_one_of_coherentFailure_of_least hcoherentSecond
        hfirstSecond hsecondThird hfailSecond))
    · exact Or.inr (Or.inr (sum_sq_gt_one_of_coherentFailure_of_least hcoherentThird
        (le_trans hsecondThird hfirstSecond) hsecondThird hfailThird))

/-- **A COHERENT FAILURE NEEDS AN EDGE ABOVE `1/sqrt 2`.** Strictly more than the `1/2`
the box refutation supplies, and the threshold is attained: see
`isCoherentFailingTriple_zeroPair`. -/
theorem exists_sq_gt_half_of_isCoherentFailingTriple {rhoFirst rhoSecond rhoThird : ℝ}
    (hclass : IsCoherentFailingTriple rhoFirst rhoSecond rhoThird) :
    1 / 2 < rhoFirst ^ 2 ∨ 1 / 2 < rhoSecond ^ 2 ∨ 1 / 2 < rhoThird ^ 2 := by
  rcases exists_pairSumSq_gt_one_of_isCoherentFailingTriple hclass with
    hpair | hpair | hpair
  · rcases le_total (rhoSecond ^ 2) (rhoThird ^ 2) with hcompare | hcompare
    · exact Or.inr (Or.inr (by linarith))
    · exact Or.inr (Or.inl (by linarith))
  · rcases le_total (rhoFirst ^ 2) (rhoThird ^ 2) with hcompare | hcompare
    · exact Or.inr (Or.inr (by linarith))
    · exact Or.inl (by linarith)
  · rcases le_total (rhoFirst ^ 2) (rhoSecond ^ 2) with hcompare | hcompare
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inl (by linarith)

/-- **A FRUSTRATED FAILURE NEEDS AN EDGE ABOVE `1/2`**, and no more: the threshold is
attained by the frustrated equilateral. -/
theorem exists_sq_gt_quarter_of_isFrustratedFailingTriple {rhoFirst rhoSecond rhoThird : ℝ}
    (hclass : IsFrustratedFailingTriple rhoFirst rhoSecond rhoThird) :
    1 / 4 < rhoFirst ^ 2 ∨ 1 / 4 < rhoSecond ^ 2 ∨ 1 / 4 < rhoThird ^ 2 :=
  exists_sq_gt_quarter_of_elliptopeBracket_neg hclass.2.2

/-- **The pen's `rootLower` phrasing, in the gauge where it is true, and without the
sign hypothesis the pen attaches to the isolated correlation.** If the other two
correlations lie in `[0, 1]` and the first is at most both of them, a failure puts
the first correlation strictly BELOW the lower root — never above the upper one. The
coherence hypothesis is not needed here; it is what puts a general failing triple
into this gauge, via `abs_lt_rootLower_of_isCoherentFailingTriple`. Outside the gauge
the pen phrasing is FALSE, and `coherentFailure_rootLower_needs_gauge` exhibits the
counterexample. -/
theorem lt_rootLower_of_failure_of_least {rhoFirst rhoSecond rhoThird : ℝ}
    (hsecondNonneg : 0 ≤ rhoSecond)
    (hthirdNonneg : 0 ≤ rhoThird) (hleastSecond : rhoFirst ≤ rhoSecond)
    (hleastThird : rhoFirst ≤ rhoThird) (hsecondCompatible : rhoSecond ^ 2 ≤ 1)
    (hthirdCompatible : rhoThird ^ 2 ≤ 1)
    (hfail : elliptopeBracket rhoFirst rhoSecond rhoThird < 0) :
    rhoFirst < rootLower rhoSecond rhoThird := by
  have hslot : elliptopeBracket rhoSecond rhoThird rhoFirst
      = elliptopeBracket rhoFirst rhoSecond rhoThird := by
    rw [elliptopeBracket, elliptopeBracket]; ring
  have hsecondLeOne : rhoSecond ≤ 1 := by nlinarith [hsecondCompatible, hsecondNonneg]
  have hthirdLeOne : rhoThird ≤ 1 := by nlinarith [hthirdCompatible, hthirdNonneg]
  by_contra hnotBelow
  push Not at hnotBelow
  have hupper : rhoFirst ≤ rootUpper rhoSecond rhoThird := by
    rcases le_or_gt rhoFirst (rhoSecond * rhoThird) with hbelowProduct | haboveProduct
    · rw [rootUpper]
      linarith [Real.sqrt_nonneg ((1 - rhoSecond ^ 2) * (1 - rhoThird ^ 2))]
    · exfalso
      have hgapPos : 0 < rhoFirst - rhoSecond * rhoThird := by linarith
      have hgapSecond : rhoFirst - rhoSecond * rhoThird ≤ rhoSecond * (1 - rhoThird) := by
        nlinarith [hleastSecond]
      have hgapThird : rhoFirst - rhoSecond * rhoThird ≤ rhoThird * (1 - rhoSecond) := by
        nlinarith [hleastThird]
      have hboundNonneg : (0 : ℝ) ≤ rhoSecond * (1 - rhoThird) :=
        mul_nonneg hsecondNonneg (by linarith)
      have hgapSquare : (rhoFirst - rhoSecond * rhoThird) * (rhoFirst - rhoSecond * rhoThird)
          ≤ rhoSecond * (1 - rhoThird) * (rhoThird * (1 - rhoSecond)) :=
        mul_le_mul hgapSecond hgapThird hgapPos.le hboundNonneg
      have hcornerBound : rhoSecond * (1 - rhoThird) * (rhoThird * (1 - rhoSecond))
          ≤ (1 - rhoSecond ^ 2) * (1 - rhoThird ^ 2) := by
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - rhoSecond)
            (by linarith : (0 : ℝ) ≤ 1 - rhoThird))
          (by linarith : (0 : ℝ) ≤ 1 + rhoSecond + rhoThird)]
      have hbracketNonneg : 0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird := by
        rw [elliptopeBracket_eq_completedSquare_first]
        nlinarith [hgapSquare, hcornerBound]
      linarith
  have hbracketNonneg : 0 ≤ elliptopeBracket rhoSecond rhoThird rhoFirst :=
    (elliptopeBracket_nonneg_iff_mem_rootInterval hsecondCompatible hthirdCompatible).mpr
      ⟨hnotBelow, hupper⟩
  rw [hslot] at hbracketNonneg
  linarith

/-- **The pen's `rootLower` phrasing, for a genuine coherent failure.** Coherence is
exactly what lets the triple be replaced by its absolute values for free, and in that
gauge the smallest correlation IN MAGNITUDE drops strictly below the lower root of the
other two. This is the honest form of the pen's hinge phrasing. -/
theorem abs_lt_rootLower_of_isCoherentFailingTriple {rhoFirst rhoSecond rhoThird : ℝ}
    (hclass : IsCoherentFailingTriple rhoFirst rhoSecond rhoThird)
    (hleastSecond : rhoFirst ^ 2 ≤ rhoSecond ^ 2)
    (hleastThird : rhoFirst ^ 2 ≤ rhoThird ^ 2) :
    |rhoFirst| < rootLower |rhoSecond| |rhoThird| := by
  obtain ⟨⟨_, hsecondCompatible, hthirdCompatible⟩, hcoherent, hfail⟩ := hclass
  have hgaugeSecond : |rhoSecond| ^ 2 ≤ 1 := by rw [sq_abs]; exact hsecondCompatible
  have hgaugeThird : |rhoThird| ^ 2 ≤ 1 := by rw [sq_abs]; exact hthirdCompatible
  have hleastGaugeSecond : |rhoFirst| ≤ |rhoSecond| := by
    nlinarith [abs_nonneg rhoFirst, abs_nonneg rhoSecond, sq_abs rhoFirst, sq_abs rhoSecond,
      hleastSecond]
  have hleastGaugeThird : |rhoFirst| ≤ |rhoThird| := by
    nlinarith [abs_nonneg rhoFirst, abs_nonneg rhoThird, sq_abs rhoFirst, sq_abs rhoThird,
      hleastThird]
  refine lt_rootLower_of_failure_of_least (abs_nonneg rhoSecond) (abs_nonneg rhoThird)
    hleastGaugeSecond hleastGaugeThird hgaugeSecond hgaugeThird ?_
  rw [elliptopeBracket_abs_of_coherent hcoherent]
  exact hfail

/-- **THE PEN'S GAUGE-FREE PHRASING IS FALSE.** At `(−1/10, −99/100, 99/100)` the
oriented product is strictly positive, the triple is compatible, the bracket is
strictly negative, and the first correlation is the smallest in magnitude — yet it
sits strictly ABOVE the upper root, not below the lower one. The `rootLower` reading
of the coherent branch is a statement about the all-nonnegative representative and
must be quoted with its gauge. -/
theorem coherentFailure_rootLower_needs_gauge :
    0 < (-(1 / 10) : ℝ) * (-(99 / 100)) * (99 / 100)
      ∧ IsCoherentFailingTriple (-(1 / 10)) (-(99 / 100)) (99 / 100)
      ∧ (-(1 / 10) : ℝ) ^ 2 ≤ (-(99 / 100) : ℝ) ^ 2
      ∧ (-(1 / 10) : ℝ) ^ 2 ≤ ((99 / 100) : ℝ) ^ 2
      ∧ rootUpper (-(99 / 100)) (99 / 100) < -(1 / 10) := by
  have hradicand : (1 - (-(99 / 100) : ℝ) ^ 2) * (1 - ((99 / 100) : ℝ) ^ 2)
      = (199 / 10000 : ℝ) ^ 2 := by norm_num
  refine ⟨by norm_num, ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, ?_⟩,
    by norm_num, by norm_num, ?_⟩
  · rw [elliptopeBracket]; norm_num
  · rw [rootUpper, hradicand, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 199 / 10000)]
    norm_num

/-! ### Both thresholds are attained -/

/-- **The coherent threshold `1/sqrt 2` is sharp.** The product-zero triple `(0, r, r)`
is compatible and coherent, and it fails exactly when `r² > 1/2`. This witness is also
why the coherent branch must be defined with `0 ≤ product` rather than `0 < product`:
with a strict reading the trichotomy loses this point entirely. -/
theorem elliptopeBracket_zeroPair (rho : ℝ) :
    elliptopeBracket 0 rho rho = 1 - 2 * rho ^ 2 := by
  rw [elliptopeBracket]; ring

theorem elliptopeBracket_zeroPair_neg_iff (rho : ℝ) :
    elliptopeBracket 0 rho rho < 0 ↔ 1 / 2 < rho ^ 2 := by
  rw [elliptopeBracket_zeroPair]
  constructor <;> intro hbound <;> linarith

theorem isCoherentFailingTriple_zeroPair {rho : ℝ} (hlow : 1 / 2 < rho ^ 2)
    (hhigh : rho ^ 2 ≤ 1) : IsCoherentFailingTriple 0 rho rho := by
  refine ⟨⟨by norm_num, hhigh, hhigh⟩, by norm_num, ?_⟩
  exact (elliptopeBracket_zeroPair_neg_iff rho).mpr hlow

/-- **The frustrated threshold `1/2` is sharp.** The equilateral triple `(t, t, t)`
with `−1 ≤ t < −1/2` is compatible, frustrated and failing, and its largest square
tends to `1/4`. -/
theorem isFrustratedFailingTriple_equilateral {rho : ℝ} (hlow : -1 ≤ rho)
    (hhigh : rho < -(1 / 2)) : IsFrustratedFailingTriple rho rho rho := by
  have hsquare : rho ^ 2 ≤ 1 := by nlinarith [hlow, hhigh]
  refine ⟨⟨hsquare, hsquare, hsquare⟩, by nlinarith [hlow, hhigh], ?_⟩
  rw [elliptopeBracket_equilateral]
  nlinarith [hhigh, sq_nonneg (1 - rho), hlow]

/-! ## 8. The bridge to the shipped design vocabulary

Every scalar statement above transports to `WeightedDesign m 3` through the shipped
normalization, so the two vocabularies are interchangeable and not merely parallel. -/


theorem isCompatiblePair_iff_normalizedPairing_sq_le_one (D : WeightedDesign m 3)
    {atomFirst atomSecond : Fin m} (hfirstPos : 0 < heavyExcess D atomFirst)
    (hsecondPos : 0 < heavyExcess D atomSecond) :
    IsCompatiblePair D atomFirst atomSecond
      ↔ normalizedPairing D atomFirst atomSecond ^ 2 ≤ 1 := by
  rw [isCompatiblePair_iff_abs_normalizedPairing_le_one D hfirstPos hsecondPos]
  constructor
  · intro habs
    nlinarith [sq_abs (normalizedPairing D atomFirst atomSecond),
      abs_nonneg (normalizedPairing D atomFirst atomSecond), habs]
  · intro hsquare
    nlinarith [sq_abs (normalizedPairing D atomFirst atomSecond),
      abs_nonneg (normalizedPairing D atomFirst atomSecond), hsquare]

/-- **The two vocabularies agree.** An elliptope-good triangle is exactly an elliptope
point in the three normalized pairings, in the shipped slot order. The hypotheses are
LOCAL — only the three atoms of the triple need positive excess, where
`dominates_triple_iff_isElliptopeGoodTriangle` asks for `AllHeavy D`. -/
theorem isElliptopeGoodTriangle_iff_isElliptopePoint (D : WeightedDesign m 3)
    {first second third : Fin m} (hfirstPos : 0 < heavyExcess D first)
    (hsecondPos : 0 < heavyExcess D second) (hthirdPos : 0 < heavyExcess D third) :
    IsElliptopeGoodTriangle D first second third
      ↔ IsElliptopePoint (normalizedPairing D first second)
          (normalizedPairing D first third) (normalizedPairing D second third) := by
  rw [IsElliptopeGoodTriangle, IsCompatibleTriangle, IsElliptopePoint, IsCompatibleTriple,
    isCompatiblePair_iff_normalizedPairing_sq_le_one D hfirstPos hsecondPos,
    isCompatiblePair_iff_normalizedPairing_sq_le_one D hfirstPos hthirdPos,
    isCompatiblePair_iff_normalizedPairing_sq_le_one D hsecondPos hthirdPos,
    discriminantTie_nonneg_iff_elliptopeBracket_nonneg D hfirstPos hsecondPos hthirdPos]

/-- **DOMINATION IS ELLIPTOPE MEMBERSHIP OF THE THREE CORRELATIONS.** Proved from the
pivot-corner reduction directly, so the hypotheses are LOCAL positivity of the three
excesses rather than `AllHeavy D`, and only the two PIVOT edges have to be shown
compatible in the forward direction — the third comes free from
`sq_le_one_of_two_and_bracket_nonneg`. `Gtz.Design.RhoNormalForm` carries the same
content in the design vocabulary
(`dominates_triple_iff_isCompatibleTriangle_and_elliptopeBracket_nonneg`), reached
through the matrix congruence rather than through the scalar legs; this one is the
entry point for the failure taxonomy below and the two can be collapsed by one
rewrite once both files are in the import list. -/
theorem dominates_triple_iff_isElliptopePoint (D : WeightedDesign m 3)
    {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hfirstPos : 0 < heavyExcess D first) (hsecondPos : 0 < heavyExcess D second)
    (hthirdPos : 0 < heavyExcess D third) :
    Dominates D {first, second, third}
      ↔ IsElliptopePoint (normalizedPairing D first second)
          (normalizedPairing D first third) (normalizedPairing D second third) := by
  have hfirstHeavy : 1 < leverageOf (D.atom first) := by
    rw [heavyExcess] at hfirstPos; linarith
  have hswapTail : ({first, third, second} : Finset (Fin m)) = {first, second, third} := by
    rw [Finset.pair_comm third second]
  rw [isElliptopePoint_iff_two_sq_le_one,
    ← isCompatiblePair_iff_normalizedPairing_sq_le_one D hfirstPos hsecondPos,
    ← isCompatiblePair_iff_normalizedPairing_sq_le_one D hfirstPos hthirdPos,
    ← discriminantTie_nonneg_iff_elliptopeBracket_nonneg D hfirstPos hsecondPos hthirdPos,
    dominates_triple_iff_discriminantSystem D hfirstSecond hfirstThird hsecondThird
      hfirstHeavy]
  constructor
  · rintro ⟨htrace, htie⟩
    have hdominates : Dominates D {first, second, third} :=
      (dominates_triple_iff_discriminantSystem D hfirstSecond hfirstThird hsecondThird
        hfirstHeavy).mpr ⟨htrace, htie⟩
    refine ⟨pairMinor_nonneg_of_dominates D hfirstSecond hfirstThird hsecondThird
      hfirstHeavy hdominates, ?_, htie⟩
    refine pairMinor_nonneg_of_dominates D hfirstThird hfirstSecond hsecondThird.symm
      hfirstHeavy ?_
    rw [hswapTail]
    exact hdominates
  · rintro ⟨hedgeFirstSecond, hedgeFirstThird, htie⟩
    refine ⟨?_, htie⟩
    rw [discriminantTrace_eq_pairMinor_add]
    rw [IsCompatiblePair] at hedgeFirstSecond hedgeFirstThird
    linarith

/-- **THE INTERVAL CRITERION AT THE DESIGN LEVEL.** With the two pivot edges
compatible, domination is one two-sided inequality on the pivot-free correlation. The
third compatibility condition is not a hypothesis: it is implied. -/
theorem dominates_triple_iff_mem_rootInterval (D : WeightedDesign m 3)
    {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hfirstPos : 0 < heavyExcess D first) (hsecondPos : 0 < heavyExcess D second)
    (hthirdPos : 0 < heavyExcess D third)
    (hpivotFirst : IsCompatiblePair D first second)
    (hpivotSecond : IsCompatiblePair D first third) :
    Dominates D {first, second, third}
      ↔ rootLower (normalizedPairing D first second) (normalizedPairing D first third)
            ≤ normalizedPairing D second third
        ∧ normalizedPairing D second third
            ≤ rootUpper (normalizedPairing D first second)
              (normalizedPairing D first third) := by
  have hpivotFirstSq : normalizedPairing D first second ^ 2 ≤ 1 :=
    (isCompatiblePair_iff_normalizedPairing_sq_le_one D hfirstPos hsecondPos).mp hpivotFirst
  have hpivotSecondSq : normalizedPairing D first third ^ 2 ≤ 1 :=
    (isCompatiblePair_iff_normalizedPairing_sq_le_one D hfirstPos hthirdPos).mp hpivotSecond
  rw [dominates_triple_iff_isElliptopePoint D hfirstSecond hfirstThird hsecondThird
      hfirstPos hsecondPos hthirdPos,
    isElliptopePoint_iff_mem_rootInterval hpivotFirstSq hpivotSecondSq]

/-- **A failing triple has a box-bad edge.** The contrapositive of
`dominates_of_dominantPairings`, written down because the failure taxonomy is usually
quoted for it and needs nothing of the kind. -/
theorem exists_not_isBoxGoodPair_of_not_dominates (D : WeightedDesign m 3)
    {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hfirstHeavy : 1 < leverageOf (D.atom first))
    (hsecondHeavy : 1 < leverageOf (D.atom second))
    (hthirdHeavy : 1 < leverageOf (D.atom third))
    (hfail : ¬ Dominates D {first, second, third}) :
    ¬ IsBoxGoodPair D first second ∨ ¬ IsBoxGoodPair D first third
      ∨ ¬ IsBoxGoodPair D second third := by
  by_contra hall
  push Not at hall
  exact hfail (dominates_of_dominantPairings D hfirstSecond hfirstThird hsecondThird
    hfirstHeavy hsecondHeavy hthirdHeavy hall.1 hall.2.1 hall.2.2)

/-- **The failure taxonomy at the design level.** -/
theorem not_dominates_triple_iff_failingClass (D : WeightedDesign m 3)
    {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hfirstPos : 0 < heavyExcess D first) (hsecondPos : 0 < heavyExcess D second)
    (hthirdPos : 0 < heavyExcess D third) :
    ¬ Dominates D {first, second, third}
      ↔ IsWildTriple (normalizedPairing D first second) (normalizedPairing D first third)
            (normalizedPairing D second third)
        ∨ IsCoherentFailingTriple (normalizedPairing D first second)
            (normalizedPairing D first third) (normalizedPairing D second third)
        ∨ IsFrustratedFailingTriple (normalizedPairing D first second)
            (normalizedPairing D first third) (normalizedPairing D second third) := by
  rw [dominates_triple_iff_isElliptopePoint D hfirstSecond hfirstThird hsecondThird
      hfirstPos hsecondPos hthirdPos,
    not_isElliptopePoint_iff_failingClass]

/-- **A COHERENT FAILURE OF A HEAVY TRIPLE NEEDS A CORRELATION ABOVE `1/sqrt 2`.** The
design-level payoff of the sharpened taxonomy: a failure whose oriented pairing product
is nonnegative is strictly more expensive than the box refutation records. Note this is
NOT a certificate: `icosaDesign` shows the coherent cell is empty at the sharpest
object, so the statement constrains failures, it does not certify successes. -/
theorem exists_normalizedPairing_sq_gt_half_of_coherent_not_dominates
    (D : WeightedDesign m 3) {first second third : Fin m}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hfirstPos : 0 < heavyExcess D first) (hsecondPos : 0 < heavyExcess D second)
    (hthirdPos : 0 < heavyExcess D third)
    (hcompatible : IsCompatibleTriangle D first second third)
    (hcoherent : 0 ≤ normalizedPairing D first second * normalizedPairing D first third
      * normalizedPairing D second third)
    (hfail : ¬ Dominates D {first, second, third}) :
    1 / 2 < normalizedPairing D first second ^ 2
      ∨ 1 / 2 < normalizedPairing D first third ^ 2
      ∨ 1 / 2 < normalizedPairing D second third ^ 2 := by
  obtain ⟨hedgeFirstSecond, hedgeFirstThird, hedgeSecondThird⟩ := hcompatible
  have hcompatibleTriple : IsCompatibleTriple (normalizedPairing D first second)
      (normalizedPairing D first third) (normalizedPairing D second third) :=
    ⟨(isCompatiblePair_iff_normalizedPairing_sq_le_one D hfirstPos hsecondPos).mp
        hedgeFirstSecond,
      (isCompatiblePair_iff_normalizedPairing_sq_le_one D hfirstPos hthirdPos).mp
        hedgeFirstThird,
      (isCompatiblePair_iff_normalizedPairing_sq_le_one D hsecondPos hthirdPos).mp
        hedgeSecondThird⟩
  have hbracket : elliptopeBracket (normalizedPairing D first second)
      (normalizedPairing D first third) (normalizedPairing D second third) < 0 := by
    by_contra hnonneg
    push Not at hnonneg
    exact hfail ((dominates_triple_iff_isElliptopePoint D hfirstSecond hfirstThird
      hsecondThird hfirstPos hsecondPos hthirdPos).mpr ⟨hcompatibleTriple, hnonneg⟩)
  exact exists_sq_gt_half_of_isCoherentFailingTriple ⟨hcompatibleTriple, hcoherent, hbracket⟩

end Gtz
