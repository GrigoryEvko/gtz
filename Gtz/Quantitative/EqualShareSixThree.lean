/-
# U6: the equal-share `(6,3)` cell has a dominating triple

The **equal-share `(6,3)` stratum** is the set of `Gtz.WeightedDesign 6 3` whose
every weight is `1/6` and whose every leverage is `3` — packaged as
`Gtz.IsEqualShare`.  Equivalently: six unit directions `u_1..u_6` in `R^3` with
`sum_c u_c u_c^T = 2 I`, a unit-norm tight frame with frame constant two.  Write
`gamma_cd` for the direction Gram (`Gtz.directionGram`), `w_cd = gamma_cd^2` for
the edge weight (`Gtz.edgeWeight`), and `M = Gamma - 1` for the hollow correlation
involution (`Gtz.correlationInvolution`).

**U6.**  Some triple `C` of the stratum satisfies `lambda_min(Gamma[C]) >= 1/3`,
equivalently `M[C] + (2/3) 1 ⪰ 0`, equivalently `Gtz.Dominates D C`.  This file
proves it — `Gtz.exists_dominating_triple_of_isEqualShare` — and with it
`Gtz.GtzWeighted 6 3` restricted to the stratum.

## The route, and what each layer supplies

The argument is the pen's four-case squeeze.  Three of its four layers were
landed before this file and are used verbatim.

* `Gtz.Quantitative.HollowInvolution` supplies the **norm cap (C2)**,
  `Gtz.directionGram_normCap_triple_six`: `sigma_C + 2 |P_C| <= 1` at every
  triple, where `sigma_C` is the sum of the three squared correlations and `P_C`
  their product.  It is the compression of the involution sandwich
  `-1 ⪯ M ⪯ 1`, and it is the ONLY place realness is consumed — §6 makes that
  precise by exhibiting a weight system that satisfies everything else and is
  excluded by the cap alone.  The same module supplies the **dictionary**
  `Gtz.dominates_triple_iff_posSemidef_hollowShift_six`.

* `Gtz.Quantitative.TripleCubicCriterion` supplies the **criterion (C1)**,
  `Gtz.posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper`:
  under the upper half of the cap, `M[C] + (2/3) 1 ⪰ 0` iff
  `sigma_C - 3 P_C <= 4/9`.

* `Gtz.Quantitative.WeightProductFloor` supplies the **squeeze**,
  `Gtz.signFreeTripleResidual_le_four_ninths_of_lightTriangle_or_heavyTriangle`:
  given a root `r >= 0`, a triangle whose edge weights are all at most `r^2` and a
  triangle whose edge weights are all at least `r^2` and which obeys the cap, one
  of the two has sign-free residual `h = sigma - 3 sqrt(p) <= 4/9`.

* `Gtz.Quantitative.MirrorLaw` supplies the **mirror**,
  `Gtz.directionTripleSigma_compl_eq` and
  `Gtz.directionTripleProduct_compl_eq_neg`: across a `3-3` split `sigma` is
  preserved and `P` changes sign.

## What this file adds

1. **The selection**, §1, over an ARBITRARY symmetric weight function on the six
   atoms.  `Gtz.maxMinWeight` is the maximum over the twenty triangles of the
   minimum edge weight.  The maximizing triangle is heavy by construction; the
   light triangle comes from `R(3,3) = 6`
   (`Gtz.exists_monochromaticTriple_of_pairPredicate`) applied to the predicate
   `w_e > maxMinWeight`, whose "all three above" branch contradicts maximality.
   This is the pen's `m`, and `r = sqrt m` is the root the squeeze consumes.

2. **The combinatorial core**, §2 — `(W6)`-with-cap:
   `Gtz.exists_signFreeTripleResidual_le_four_ninths` takes a nonnegative
   weight function on `Fin 6` satisfying `(C2)` at every triple and returns a
   triangle with `h <= 4/9`.  No design, no matrix, no involution.  §3
   instantiates it at a hollow symmetric involution and §4 at the stratum.

3. **The mirror step**, §5.  `h <= 4/9` bounds the SMALLER of the two sign
   readings, so it certifies the coherent side of the split.
   `Gtz.exists_coherent_orientedTripleResidual_le_four_ninths` converts
   `h(T) <= 4/9` into `sigma_S - 3 P_S <= 4/9` for `S` one of `T` and its
   complement; completing an abstract distinct triple of `Fin 6` to a bijection is
   `Gtz.exists_bijective_completion_of_distinct`.

4. **U6**, §5: `Gtz.exists_dominating_triple_of_isEqualShare` and the
   `GtzWeighted` form `Gtz.gtzWeighted_six_three_of_isEqualShare`.

5. **The sharpness pair**, §6.  `Gtz.tightEdgeWeight` is the pen's tight system —
   `4/9` on the six edges of two disjoint triangles, `1/27` on the nine cross
   edges.  Every vertex sum is `1`
   (`Gtz.sum_erase_tightEdgeWeight`) and ALL TWENTY of its triangles sit at
   `h = 4/9` exactly (`Gtz.signFreeTripleResidual_tightEdgeWeight`), so the
   constant `4/9` cannot be lowered and no strict form of `(W6)` is available;
   and its intra-triangle side has `sigma + 2 sqrt p = 52/27 > 1`
   (`Gtz.not_normCap_tightEdgeWeight`), so the stratum excludes it.  Read the
   pair carefully: the tight system SATISFIES `(W6)`, with equality, so it
   refutes nothing; it is the proof that the norm cap is load-bearing and that
   realness enters exactly there.

6. **The margin**, §7.  Cases 1 and 4 of the squeeze carry explicit slack, so the
   same machinery returns `h <= 4/9 - delta`:
   `Gtz.signFreeTripleResidual_le_sub_of_lightTriangle` (delta from a small
   maximizing weight) and
   `Gtz.signFreeTripleResidual_le_sub_of_heavyTriangle_of_capSlack` (delta from
   cap slack).  A positive margin upgrades domination to STRICT domination:
   `Gtz.posDef_of_orientedTripleResidual_lt_four_ninths`.  §7 also records where
   the light branch's inequality is TIGHT — the factorisation
   `Psi_m(3m) = -9 (m - 1/9)(m - 4/9)^2` has its double root at `m = 4/9`, whose
   equilateral triangle has `sigma = 4/3` and is excluded by the cap, so on the
   stratum the only light-branch tangency is the simple root `m = 1/9`, the
   tetrahedral tripod's weight.

7. **Calibration**, §8, at the level of `h`: the tetrahedral tripod at `2/9`
   (while its CRITERION is `4/9` — the gap between the two readings is the mirror
   made visible), the `K4` star at `3/8`, the icosahedron at
   `3/5 - 3 sqrt 5 / 25`.  `Gtz.exists_dominating_triple_icosaDesign` and
   `Gtz.exists_dominating_triple_octahedronDesign` check that U6 fires at the two
   named stratum members, the second of which has three PARALLEL pairs and so
   fails the pen's "pairwise non-parallel" hypothesis — which the proof here never
   uses.

8. **The equality locus**, §9, and it corrects a guess.  The campaign expected the
   bound to be tight only where the involution sandwich is tight (the coplanar
   locus).  That is FALSE at the level of a single triangle:
   `Gtz.exists_capSlack_signFreeTripleResidual_eq_four_ninths` exhibits
   `(2/9, 2/9, 0)`, which has `h = 4/9` exactly and cap slack `5/9` — the LARGEST
   slack any `h = 4/9` triangle can have, since `h <= sigma <= sigma + 2 sqrt p`.
   Tightness for `h` is a vanishing-PRODUCT phenomenon, not a saturated-cap one,
   so no quantitative U6 can be obtained by tracking cap slack alone.  On the
   equilateral locus, by contrast, the classification is exact and the margin is
   real: `h - 4/9 = -(1/9)(3r-2)^2(3r+1)`, the cap forces `r <= 1/2` exactly
   (`3 r^2 + 2 r^3 = 1` at `r = 1/2`), and therefore every equilateral triangle of
   the stratum has `h <= 3/8`
   (`Gtz.signFreeTripleResidual_equilateral_le_three_eighths`) with equality
   exactly at the `K4` star's weight `1/4`.  The margin `5/72` is attained, so
   `3/8` is sharp too.

9. **The exact light branch**, §10.  Cases 1 and 2 conclude `h <= 4/9`, but the
   endpoint machinery they run on proves the sharp
   `h <= max (2 r^2) (3 r^2 - 3 r^3)`
   (`Gtz.signFreeTripleResidual_le_max_of_lightTriangle`), on the whole light
   range and with both branches attained — the first at the degenerate triangle
   `(r^2, r^2, 0)`, the second at the equilateral one.  That is the light half's
   margin in closed form, and it explains §9's witness: `(2/9, 2/9, 0)` is the
   degenerate endpoint at the worst admissible root, where `2 r^2 = 4/9` on the
   nose.  Below that root the bound is strict:
   `Gtz.signFreeTripleResidual_lt_four_ninths_of_lightTriangle_of_lt`.

## Honest framing

`Gtz.gtzWeighted_six_three_of_seven_three` already makes `GtzWeighted 6 3` a
consequence of the `(7,3)` frontier, so U6 is a closed SUB-CELL of an object that
is already implied, not a step on the critical path.  What is new is the
certificate species: every per-triple cell shipped by this campaign
(`Gtz.dominates_of_isBoxGoodTriangle`, `Gtz.dominates_of_coherentHalfBoxTriangle`,
`Gtz.dominates_of_coherentLightCherryTriangle`) is empty at the `K4` graphic
`(6,3)` design, whose star triples sit at `rho^2 = 9/16`; U6 decides that design,
and every other member of the stratum, with no per-triple hypothesis at all.

The abstract involution layer of §3 stops at the combinatorial core.  Turning it
into an unconditional PSD statement about an arbitrary hollow symmetric
involution on `Fin 6` needs the mirror in the form `det J[K] = -det J[K-complement]`
— Jacobi's complementary-minor identity applied to `J^{-1} = J` and `det J = -1`
— which is not in this repository and not in mathlib.  The design route does not
need it: `Gtz.directionTripleProduct_compl_eq_neg` gets the sign flip from the
tight frame instead, where it is a two-line Weinstein–Aronszajn argument.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.DominationGates
import Gtz.Design.FrameConservation
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.TripleCubicCriterion
import Gtz.Quantitative.WeightProductFloor

namespace Gtz

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## 1. The selection: the max-min edge weight

The pen's `m = max over the twenty triangles of (min edge of the triangle)`,
stated for an arbitrary weight function so that the design layer and the abstract
involution layer share one proof.  Ordering the triple costs nothing — the
minimum of three edge weights is symmetric — and it saves the whole
`Finset.powersetCard` extraction. -/

/-- Ordered triples of pairwise-distinct indices among six. -/
def distinctTriples : Finset (Fin 6 × Fin 6 × Fin 6) :=
  Finset.univ.filter fun triple =>
    triple.1 ≠ triple.2.1 ∧ triple.1 ≠ triple.2.2 ∧ triple.2.1 ≠ triple.2.2

theorem mem_distinctTriples {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    (first, second, third) ∈ distinctTriples := by
  simp only [distinctTriples, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hfirstSecond, hfirstThird, hsecondThird⟩

theorem distinctTriples_nonempty : distinctTriples.Nonempty :=
  ⟨(0, 1, 2), mem_distinctTriples (by decide) (by decide) (by decide)⟩

/-- The smallest of a triangle's three edge weights. -/
def minTripleWeight (weightOf : Fin 6 → Fin 6 → ℝ) (triple : Fin 6 × Fin 6 × Fin 6) : ℝ :=
  min (min (weightOf triple.1 triple.2.1) (weightOf triple.1 triple.2.2))
    (weightOf triple.2.1 triple.2.2)

theorem minTripleWeight_nonneg {weightOf : Fin 6 → Fin 6 → ℝ}
    (hnonneg : ∀ first second, 0 ≤ weightOf first second) (triple : Fin 6 × Fin 6 × Fin 6) :
    0 ≤ minTripleWeight weightOf triple :=
  le_min (le_min (hnonneg _ _) (hnonneg _ _)) (hnonneg _ _)

/-- **THE PEN'S `m`**: the largest, over the twenty triangles, of the triangle's
smallest edge weight. -/
noncomputable def maxMinWeight (weightOf : Fin 6 → Fin 6 → ℝ) : ℝ :=
  distinctTriples.sup' distinctTriples_nonempty (minTripleWeight weightOf)

theorem minTripleWeight_le_maxMinWeight (weightOf : Fin 6 → Fin 6 → ℝ)
    {triple : Fin 6 × Fin 6 × Fin 6} (hmember : triple ∈ distinctTriples) :
    minTripleWeight weightOf triple ≤ maxMinWeight weightOf :=
  Finset.le_sup' (minTripleWeight weightOf) hmember

theorem maxMinWeight_nonneg {weightOf : Fin 6 → Fin 6 → ℝ}
    (hnonneg : ∀ first second, 0 ≤ weightOf first second) : 0 ≤ maxMinWeight weightOf :=
  le_trans (minTripleWeight_nonneg hnonneg (0, 1, 2))
    (minTripleWeight_le_maxMinWeight weightOf
      (mem_distinctTriples (by decide) (by decide) (by decide)))

/-- **THE HEAVY TRIANGLE.**  The maximizer has all three edge weights at least
`maxMinWeight`, because its smallest edge IS that value. -/
theorem exists_heavyTriple (weightOf : Fin 6 → Fin 6 → ℝ) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      maxMinWeight weightOf ≤ weightOf first second ∧
      maxMinWeight weightOf ≤ weightOf first third ∧
      maxMinWeight weightOf ≤ weightOf second third := by
  obtain ⟨triple, hmember, hvalue⟩ :=
    Finset.exists_mem_eq_sup' distinctTriples_nonempty (minTripleWeight weightOf)
  simp only [distinctTriples, Finset.mem_filter, Finset.mem_univ, true_and] at hmember
  refine ⟨triple.1, triple.2.1, triple.2.2, hmember.1, hmember.2.1, hmember.2.2, ?_, ?_, ?_⟩
  · rw [maxMinWeight, hvalue, minTripleWeight]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  · rw [maxMinWeight, hvalue, minTripleWeight]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  · rw [maxMinWeight, hvalue, minTripleWeight]
    exact min_le_right _ _

/-- **THE LIGHT TRIANGLE.**  By `R(3,3) = 6` the predicate `w_e > maxMinWeight`
either holds on all three edges of some triangle or fails on all three of some
triangle.  The first branch contradicts maximality — such a triangle's smallest
edge would exceed the maximum of the smallest edges — so the second holds, and it
is exactly a triangle all of whose edge weights are at most `maxMinWeight`.

This is the only use of Ramsey in the U6 argument, and it is why the stratum's
size SIX is load-bearing: at five atoms the pentagon
(`Gtz.exists_cliqueFree_three_and_compl_cliqueFree_three_five`) defeats the
dichotomy. -/
theorem exists_lightTriple (weightOf : Fin 6 → Fin 6 → ℝ) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      weightOf first second ≤ maxMinWeight weightOf ∧
      weightOf first third ≤ maxMinWeight weightOf ∧
      weightOf second third ≤ maxMinWeight weightOf := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hbranch⟩ :=
    exists_monochromaticTriple_of_pairPredicate
      (fun leftIndex rightIndex => maxMinWeight weightOf < weightOf leftIndex rightIndex)
      (id : Fin 6 → Fin 6)
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
  rcases hbranch with ⟨hone, htwo, hthree⟩ | ⟨hone, htwo, hthree⟩
  · exfalso
    have hmax := minTripleWeight_le_maxMinWeight weightOf
      (mem_distinctTriples hfirstSecond hfirstThird hsecondThird)
    rw [minTripleWeight] at hmax
    simp only [id_eq] at hone htwo hthree
    exact absurd hmax (not_le.mpr (lt_min (lt_min hone htwo) hthree))
  · simp only [id_eq, not_lt] at hone htwo hthree
    exact ⟨hone, htwo, hthree⟩

/-! ## 2. `(W6)`-with-cap: the combinatorial core

The four-case squeeze, assembled.  Nothing here but the selection of §1 and
`Gtz.signFreeTripleResidual_le_four_ninths_of_lightTriangle_or_heavyTriangle`.

The cap hypothesis is stated in its own coordinates, `sigma + 2 sqrt(p) <= 1`,
which is exactly `(C2)`; the squeeze wants it in the polynomial form
`sigma + 2 r^3 <= 1`, and the exchange is the one place a square root has to be
compared, done here once and at the level of squares. -/

/-- On a heavy triangle the square root of the weight product dominates `r^3`. -/
theorem pow_three_le_sqrt_edgeProduct {rootBound firstWeight secondWeight thirdWeight : ℝ}
    (hrootNonneg : 0 ≤ rootBound) (hfirst : rootBound ^ 2 ≤ firstWeight)
    (hsecond : rootBound ^ 2 ≤ secondWeight) (hthird : rootBound ^ 2 ≤ thirdWeight) :
    rootBound ^ 3 ≤ Real.sqrt (firstWeight * secondWeight * thirdWeight) := by
  have hproduct := sq_pow_three_le_edgeProduct_of_sq_le hfirst hsecond hthird
  have hcubeNonneg : (0 : ℝ) ≤ rootBound ^ 3 := pow_nonneg hrootNonneg 3
  calc rootBound ^ 3 = Real.sqrt ((rootBound ^ 3) ^ 2) := (Real.sqrt_sq hcubeNonneg).symm
    _ ≤ Real.sqrt (firstWeight * secondWeight * thirdWeight) := Real.sqrt_le_sqrt hproduct

/-- The cap in the squeeze's polynomial coordinates, from the cap in its own. -/
theorem normCap_pow_three_of_normCap_sqrt {rootBound firstWeight secondWeight thirdWeight : ℝ}
    (hrootNonneg : 0 ≤ rootBound) (hfirst : rootBound ^ 2 ≤ firstWeight)
    (hsecond : rootBound ^ 2 ≤ secondWeight) (hthird : rootBound ^ 2 ≤ thirdWeight)
    (hcap : firstWeight + secondWeight + thirdWeight
      + 2 * Real.sqrt (firstWeight * secondWeight * thirdWeight) ≤ 1) :
    firstWeight + secondWeight + thirdWeight + 2 * rootBound ^ 3 ≤ 1 := by
  have hroot := pow_three_le_sqrt_edgeProduct hrootNonneg hfirst hsecond hthird
  linarith

/-- **THE COMBINATORIAL CORE, `(W6)`-WITH-CAP.**  A nonnegative weight function on
the six atoms that obeys `(C2)` — `sigma_T + 2 sqrt(p_T) <= 1` at every triangle —
has a triangle with sign-free residual `h_T = sigma_T - 3 sqrt(p_T) <= 4/9`.

The root is `r = sqrt(maxMinWeight)`.  The light triangle of §1 has all edges at
most `r^2` and the heavy one all edges at least `r^2`; the cap applies to the
heavy one; and the squeeze returns one of the two.

The cap is NOT decoration.  `(W6)` as a statement about the fractional perfect
matching polytope of `K_6` alone is exactly tight — §6 exhibits a vertex-sum-one
weight system all twenty of whose triangles sit at `h = 4/9` — and the proof here
genuinely spends the cap in the heavy branch.  Attaching the cap is what makes the
statement provable AND what makes it a REAL statement: over `C` the cap fails and
so does everything downstream. -/
theorem exists_signFreeTripleResidual_le_four_ninths (weightOf : Fin 6 → Fin 6 → ℝ)
    (hnonneg : ∀ first second, 0 ≤ weightOf first second)
    (hcap : ∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
      weightOf first second + weightOf first third + weightOf second third
        + 2 * Real.sqrt (weightOf first second * weightOf first third
          * weightOf second third) ≤ 1) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      signFreeTripleResidual (weightOf first second) (weightOf first third)
        (weightOf second third) ≤ 4 / 9 := by
  obtain ⟨lightFirst, lightSecond, lightThird, hlightOneTwo, hlightOneThree, hlightTwoThree,
    hlightOne, hlightTwo, hlightThree⟩ := exists_lightTriple weightOf
  obtain ⟨heavyFirst, heavySecond, heavyThird, hheavyOneTwo, hheavyOneThree, hheavyTwoThree,
    hheavyOne, hheavyTwo, hheavyThree⟩ := exists_heavyTriple weightOf
  have hrootNonneg : (0 : ℝ) ≤ Real.sqrt (maxMinWeight weightOf) := Real.sqrt_nonneg _
  have hroot : Real.sqrt (maxMinWeight weightOf) ^ 2 = maxMinWeight weightOf :=
    Real.sq_sqrt (maxMinWeight_nonneg hnonneg)
  rw [← hroot] at hlightOne hlightTwo hlightThree hheavyOne hheavyTwo hheavyThree
  have hpolynomialCap := normCap_pow_three_of_normCap_sqrt hrootNonneg hheavyOne hheavyTwo
    hheavyThree (hcap heavyFirst heavySecond heavyThird hheavyOneTwo hheavyOneThree
      hheavyTwoThree)
  rcases signFreeTripleResidual_le_four_ninths_of_lightTriangle_or_heavyTriangle hrootNonneg
    (hnonneg lightSecond lightThird) hlightOne hlightTwo hlightThree hheavyOne hheavyTwo
    hheavyThree hpolynomialCap with hlight | hheavy
  · exact ⟨lightFirst, lightSecond, lightThird, hlightOneTwo, hlightOneThree, hlightTwoThree,
      hlight⟩
  · exact ⟨heavyFirst, heavySecond, heavyThird, hheavyOneTwo, hheavyOneThree, hheavyTwoThree,
      hheavy⟩

/-! ## 3. The abstract involution layer

A hollow symmetric involution on `Fin 6` supplies its own cap — the compression of
the sandwich `-1 ⪯ M ⪯ 1` — so §2 applies to the squared entries with no design in
sight.  This is as far as the abstract object goes; see the module docstring for
why the PSD conclusion needs the mirror and the mirror needs a frame. -/

/-- The abstract cap in the square-root coordinates §2 consumes. -/
theorem IsHollowInvolution.normCap_sqrt {invol : Matrix (Fin 6) (Fin 6) ℝ}
    (hinvol : IsHollowInvolution invol) {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    invol first second ^ 2 + invol first third ^ 2 + invol second third ^ 2
      + 2 * Real.sqrt (invol first second ^ 2 * invol first third ^ 2
        * invol second third ^ 2) ≤ 1 := by
  rw [sqrt_sq_mul_sq_mul_sq]
  exact hinvol.normCap_triple hfirstSecond hfirstThird hsecondThird

/-- **`(W6)`-WITH-CAP FOR A HOLLOW SYMMETRIC INVOLUTION.**  The squared entries of
any hollow symmetric involution on six indices carry a triangle with
`h = sigma - 3 sqrt(p) <= 4/9`.  No design, no frame, no equal-share hypothesis:
`M M = 1` with a vanishing diagonal is the whole input. -/
theorem exists_signFreeTripleResidual_le_four_ninths_of_isHollowInvolution
    {invol : Matrix (Fin 6) (Fin 6) ℝ} (hinvol : IsHollowInvolution invol) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      signFreeTripleResidual (invol first second ^ 2) (invol first third ^ 2)
        (invol second third ^ 2) ≤ 4 / 9 :=
  exists_signFreeTripleResidual_le_four_ninths (fun first second => invol first second ^ 2)
    (fun _ _ => sq_nonneg _)
    fun _ _ _ hfirstSecond hfirstThird hsecondThird =>
      hinvol.normCap_sqrt hfirstSecond hfirstThird hsecondThird

/-- **THE ABSTRACT CRITERION.**  A COHERENT triangle of a hollow symmetric
involution whose sign-free residual is at most `4/9` has `M[C] + (2/3) 1 ⪰ 0`.
Coherence is what identifies the sign-free residual with the criterion; on the
incoherent side the residual is the COMPLEMENT's criterion, which is what the
mirror of §5 supplies at the design and what has no abstract counterpart here. -/
theorem IsHollowInvolution.posSemidef_twoThirds_of_coherent_of_signFreeTripleResidual_le
    {invol : Matrix (Fin 6) (Fin 6) ℝ} (hinvol : IsHollowInvolution invol)
    {first second third : Fin 6} (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hcoherent : 0 ≤ invol first second * invol first third * invol second third)
    (hresidual : signFreeTripleResidual (invol first second ^ 2) (invol first third ^ 2)
      (invol second third ^ 2) ≤ 4 / 9) :
    (((2 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + invol.submatrix ![first, second, third] ![first, second, third]).PosSemidef := by
  have hpick : Function.Injective ![first, second, third] := by
    intro leftSlot rightSlot hvalue
    fin_cases leftSlot <;> fin_cases rightSlot <;>
      first
        | rfl
        | exact absurd hvalue (by assumption)
        | exact absurd hvalue.symm (by assumption)
  have hblock := hinvol.submatrix_three_eq_hollowMatrixThree first second third
  have hupper := hinvol.posSemidef_one_sub_submatrix ![first, second, third] hpick
  rw [hblock] at hupper ⊢
  rw [signFreeTripleResidual_sq_eq_of_nonneg_product hcoherent] at hresidual
  exact (posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper
    hupper).mpr hresidual

/-! ## 4. The stratum's cap, and the core at a design

The design layer's `(C2)` is `Gtz.directionGram_normCap_triple_six`, stated with
`|P|`; `Gtz.sqrt_edgeWeight_product_eq_abs` turns that into the square-root form
§2 consumes. -/

/-- **THE NORM CAP AT THE STRATUM**, in the square-root coordinates. -/
theorem edgeWeight_normCap_sqrt (D : WeightedDesign 6 3) (hequal : IsEqualShare D)
    {first second third : Fin 6} (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    edgeWeight D first second + edgeWeight D first third + edgeWeight D second third
      + 2 * Real.sqrt (edgeWeight D first second * edgeWeight D first third
        * edgeWeight D second third) ≤ 1 := by
  have hcap := directionGram_normCap_triple_six D hequal hfirstSecond hfirstThird hsecondThird
  rw [sqrt_edgeWeight_product_eq_abs D first second third, edgeWeight, edgeWeight, edgeWeight]
  exact hcap

/-- **`(W6)`-WITH-CAP AT THE STRATUM.**  Some triangle of an equal-share `(6,3)`
design has sign-free residual at most `4/9`. -/
theorem exists_triangleResidual_le_four_ninths (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      triangleResidual D first second third ≤ 4 / 9 :=
  exists_signFreeTripleResidual_le_four_ninths (edgeWeight D) (edgeWeight_nonneg D)
    fun _ _ _ hfirstSecond hfirstThird hsecondThird =>
      edgeWeight_normCap_sqrt D hequal hfirstSecond hfirstThird hsecondThird

/-! ## 5. The mirror step, and U6

`h(T) <= 4/9` bounds `min (sigma_T - 3 P_T) (sigma_T + 3 P_T)`.  On the coherent
side of the `3-3` split the minimum IS the criterion; the mirror
(`sigma` preserved, `P` negated) says the other reading is the complement's
criterion.  So one of the two sides of the split satisfies `(C1)`, and the
dictionary turns that into domination. -/

/-- Complete three distinct indices of `Fin 6` to a bijection.  The last three
slots are the complement's elements in their natural order; only their
distinctness from each other and from the first three is used, so the choice is
irrelevant. -/
theorem exists_bijective_completion_of_distinct {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    ∃ fourth fifth sixth : Fin 6,
      Function.Bijective ![first, second, third, fourth, fifth, sixth] := by
  classical
  have hcard : (({first, second, third} : Finset (Fin 6))ᶜ).card = 3 := by
    have hinner : ({first, second, third} : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
        Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]
    rw [Finset.card_compl, hinner, Fintype.card_fin]
  set complementIso := (({first, second, third} : Finset (Fin 6))ᶜ).orderIsoOfFin hcard with hdef
  have hnotMem : ∀ slot : Fin 3,
      ((complementIso slot : Fin 6) ≠ first ∧ (complementIso slot : Fin 6) ≠ second
        ∧ (complementIso slot : Fin 6) ≠ third) := by
    intro slot
    have hmember := (complementIso slot).2
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hmember
    exact hmember
  have hisoInjective : ∀ leftSlot rightSlot : Fin 3,
      (complementIso leftSlot : Fin 6) = (complementIso rightSlot : Fin 6) →
        leftSlot = rightSlot := fun leftSlot rightSlot hvalue =>
    complementIso.injective (Subtype.ext hvalue)
  refine ⟨(complementIso 0 : Fin 6), (complementIso 1 : Fin 6), (complementIso 2 : Fin 6), ?_⟩
  obtain ⟨hfourthFirst, hfourthSecond, hfourthThird⟩ := hnotMem 0
  obtain ⟨hfifthFirst, hfifthSecond, hfifthThird⟩ := hnotMem 1
  obtain ⟨hsixthFirst, hsixthSecond, hsixthThird⟩ := hnotMem 2
  have hfourthFifth : (complementIso 0 : Fin 6) ≠ (complementIso 1 : Fin 6) := fun hvalue =>
    absurd (hisoInjective 0 1 hvalue) (by decide)
  have hfourthSixth : (complementIso 0 : Fin 6) ≠ (complementIso 2 : Fin 6) := fun hvalue =>
    absurd (hisoInjective 0 2 hvalue) (by decide)
  have hfifthSixth : (complementIso 1 : Fin 6) ≠ (complementIso 2 : Fin 6) := fun hvalue =>
    absurd (hisoInjective 1 2 hvalue) (by decide)
  rw [← Finite.injective_iff_bijective]
  intro leftSlot rightSlot hvalue
  fin_cases leftSlot <;> fin_cases rightSlot <;>
    first
      | rfl
      | exact absurd hvalue (by assumption)
      | exact absurd hvalue.symm (by assumption)

/-- The oriented criterion value in the mirror's own vocabulary. -/
theorem orientedTripleResidual_eq_sigma_sub {m k : ℕ} (D : WeightedDesign m k)
    (first second third : Fin m) :
    orientedTripleResidual D first second third
      = directionTripleSigma D first second third
        - 3 * directionTripleProduct D first second third := by
  rw [orientedTripleResidual, directionTripleSigma, directionTripleProduct, edgeWeight,
    edgeWeight, edgeWeight]

/-- **THE MIRROR STEP.**  A triangle with `h <= 4/9` certifies the criterion on
the coherent side of its `3-3` split: either the triangle itself is coherent and
its own criterion value is the residual, or its complement is coherent and the
complement's criterion value is the residual.  Either way some triple of pairwise
distinct atoms satisfies `sigma - 3 P <= 4/9`. -/
theorem exists_coherent_orientedTripleResidual_le_of_triangleResidual_le
    (D : WeightedDesign 6 3) (hequal : IsEqualShare D) {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hresidual : triangleResidual D first second third ≤ 4 / 9) :
    ∃ leftIndex middleIndex rightIndex : Fin 6,
      leftIndex ≠ middleIndex ∧ leftIndex ≠ rightIndex ∧ middleIndex ≠ rightIndex ∧
        orientedTripleResidual D leftIndex middleIndex rightIndex ≤ 4 / 9 := by
  by_cases hcoherent : 0 ≤ directionTripleProduct D first second third
  · refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
    rwa [triangleResidual_eq_orientedTripleResidual_of_coherent D hcoherent] at hresidual
  obtain ⟨fourth, fifth, sixth, hbijective⟩ :=
    exists_bijective_completion_of_distinct hfirstSecond hfirstThird hsecondThird
  have huniform : ∀ atomIndex : Fin 6, atomShare D atomIndex = 1 / 2 := fun atomIndex => by
    rw [hequal.atomShare_eq atomIndex]; norm_num
  have hinjective : Function.Injective ![first, second, third, fourth, fifth, sixth] :=
    hbijective.1
  have hfourthFifth : fourth ≠ fifth := fun hvalue => by
    have := hinjective (a₁ := 3) (a₂ := 4) (by simpa using hvalue); exact absurd this (by decide)
  have hfourthSixth : fourth ≠ sixth := fun hvalue => by
    have := hinjective (a₁ := 3) (a₂ := 5) (by simpa using hvalue); exact absurd this (by decide)
  have hfifthSixth : fifth ≠ sixth := fun hvalue => by
    have := hinjective (a₁ := 4) (a₂ := 5) (by simpa using hvalue); exact absurd this (by decide)
  refine ⟨fourth, fifth, sixth, hfourthFifth, hfourthSixth, hfifthSixth, ?_⟩
  have hsigma := directionTripleSigma_compl_eq D huniform hbijective
  have hproduct := directionTripleProduct_compl_eq_neg D huniform hbijective
  rw [orientedTripleResidual_eq_sigma_sub, hsigma, hproduct]
  rw [triangleResidual, edgeWeight, edgeWeight, edgeWeight, signFreeTripleResidual_sq_eq_min]
    at hresidual
  rw [directionTripleSigma, directionTripleProduct]
  have hmin : min (directionGram D first second ^ 2 + directionGram D first third ^ 2
        + directionGram D second third ^ 2
      - 3 * (directionGram D first second * directionGram D first third
        * directionGram D second third))
      (directionGram D first second ^ 2 + directionGram D first third ^ 2
        + directionGram D second third ^ 2
      + 3 * (directionGram D first second * directionGram D first third
        * directionGram D second third)) ≤ 4 / 9 := hresidual
  have hsmall : directionGram D first second ^ 2 + directionGram D first third ^ 2
      + directionGram D second third ^ 2
      + 3 * (directionGram D first second * directionGram D first third
        * directionGram D second third) ≤ 4 / 9 := by
    rw [not_le, directionTripleProduct] at hcoherent
    rcases min_le_iff.mp hmin with hleft | hright
    · linarith
    · exact hright
  linarith

/-- **THE CRITERION AT THE STRATUM.**  A triple whose oriented criterion value is
at most `4/9` dominates.  The dictionary is
`Gtz.dominates_triple_iff_posSemidef_hollowShift_six`; the cap that makes the
criterion an equivalence is the compression of the involution sandwich. -/
theorem dominates_of_orientedTripleResidual_le_four_ninths (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hcriterion : orientedTripleResidual D first second third ≤ 4 / 9) :
    Dominates D {first, second, third} := by
  have hpick : Function.Injective ![first, second, third] := by
    intro leftSlot rightSlot hvalue
    fin_cases leftSlot <;> fin_cases rightSlot <;>
      first
        | rfl
        | exact absurd hvalue (by assumption)
        | exact absurd hvalue.symm (by assumption)
  have hinvol := isHollowInvolution_correlationInvolution_six D hequal
  have hupper := hinvol.posSemidef_one_sub_submatrix ![first, second, third] hpick
  rw [correlationInvolution_submatrix_three_eq_hollowMatrixThree D
    (fun atomIndex => hequal.leverage_pos (by norm_num) atomIndex) hfirstSecond hfirstThird
    hsecondThird] at hupper
  rw [dominates_triple_iff_posSemidef_hollowShift_six D hequal hfirstSecond hfirstThird
    hsecondThird, add_comm]
  refine (posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper
    hupper).mpr ?_
  rw [orientedTripleResidual, edgeWeight, edgeWeight, edgeWeight] at hcriterion
  exact hcriterion

/-- **U6, THE HEADLINE.**  Every equal-share `(6,3)` design has a dominating
triple: six unit directions in `R^3` with `sum_c u_c u_c^T = 2 I` always contain
three whose Gram has least eigenvalue at least `1/3`.

The calibration points, all landed elsewhere and all consistent with this: the
tetrahedral tripod sits at exactly `1/3` (the tie), the `K4` graphic design's
stars at `1/2`, the icosahedron's coherent triples at `1 - 1/sqrt 5`. -/
theorem exists_dominating_triple_of_isEqualShare (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      Dominates D {first, second, third} := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hresidual⟩ :=
    exists_triangleResidual_le_four_ninths D hequal
  obtain ⟨leftIndex, middleIndex, rightIndex, hleftMiddle, hleftRight, hmiddleRight,
    hcriterion⟩ := exists_coherent_orientedTripleResidual_le_of_triangleResidual_le D hequal
      hfirstSecond hfirstThird hsecondThird hresidual
  exact ⟨leftIndex, middleIndex, rightIndex, hleftMiddle, hleftRight, hmiddleRight,
    dominates_of_orientedTripleResidual_le_four_ninths D hequal hleftMiddle hleftRight
      hmiddleRight hcriterion⟩

/-- **U6 in the `Gtz.GtzWeighted` shape**: the conclusion of `GtzWeighted 6 3`,
restricted to the equal-share stratum.  `Gtz.GtzWeighted 6 3` itself is already a
consequence of the `(7,3)` frontier
(`Gtz.gtzWeighted_six_three_of_seven_three`); what is new is that this sub-cell is
closed unconditionally, with no per-triple hypothesis. -/
theorem gtzWeighted_six_three_of_isEqualShare (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) : ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hdominates⟩ :=
    exists_dominating_triple_of_isEqualShare D hequal
  refine ⟨{first, second, third}, ?_, hdominates⟩
  rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
    Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]

/-- **U6 in the least-eigenvalue shape**: some triple's direction Gram has least
eigenvalue at least `1/3`. -/
theorem exists_inv_three_le_lambdaMinMat_of_isEqualShare (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      (3 : ℝ)⁻¹ ≤ lambdaMinMat ((directionGramMatrix D).submatrix
        ![first, second, third] ![first, second, third]) := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hdominates⟩ :=
    exists_dominating_triple_of_isEqualShare D hequal
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    (dominates_triple_iff_inv_three_le_lambdaMinMat_six D hequal hfirstSecond hfirstThird
      hsecondThird).mp hdominates⟩

/-! ## 6. The sharpness pair

The pen's tight weight system: `4/9` on the six edges of the two disjoint
triangles `{0,1,2}` and `{3,4,5}`, `1/27` on the nine cross edges.  It is the
explicit convex combination `(8/9)` of the disjoint-triangle vertex of the
fractional perfect matching polytope of `K_6` and `(1/9)` of the barycentre of the
crossing `K_{3,3}`'s six perfect matchings.

Two theorems, and they say different things.  ALL TWENTY of its triangles sit at
`h = 4/9` exactly, so `4/9` cannot be lowered and no strict form of `(W6)` is
available — the tight system SATISFIES `(W6)`, with equality, and refutes nothing.
And its intra-triangle side has `sigma + 2 sqrt p = 4/3 + 16/27 = 52/27 > 1`, so
the norm cap excludes it from the stratum.  Together: the cap is load-bearing, and
since the cap is the only real-field input, realness enters there and nowhere
else. -/

/-- Which half of the `3+3` split an index lies in. -/
def tightSide (index : Fin 6) : Bool := index.val < 3

/-- **THE PEN'S TIGHT WEIGHT SYSTEM.**  `4/9` inside each half, `1/27` across. -/
noncomputable def tightEdgeWeight (first second : Fin 6) : ℝ :=
  if tightSide first = tightSide second then 4 / 9 else 1 / 27

theorem tightEdgeWeight_comm (first second : Fin 6) :
    tightEdgeWeight first second = tightEdgeWeight second first := by
  rw [tightEdgeWeight, tightEdgeWeight]
  by_cases hside : tightSide first = tightSide second
  · rw [if_pos hside, if_pos hside.symm]
  · rw [if_neg hside, if_neg fun hswapped => hside hswapped.symm]

theorem tightEdgeWeight_nonneg (first second : Fin 6) : 0 ≤ tightEdgeWeight first second := by
  rw [tightEdgeWeight]; split <;> norm_num

/-- The intra-half triangle sits at `h = 4/3 - 3 (8/27) = 4/9`. -/
theorem signFreeTripleResidual_intra :
    signFreeTripleResidual (4 / 9) (4 / 9) (4 / 9) = 4 / 9 := by
  rw [signFreeTripleResidual,
    show (4 / 9 : ℝ) * (4 / 9) * (4 / 9) = (8 / 27 : ℝ) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-- The mixed triangle sits at `h = 14/27 - 3 (2/81) = 4/9`, in every one of the
three slot positions the lone intra edge can occupy. -/
theorem signFreeTripleResidual_mixed_first :
    signFreeTripleResidual (4 / 9) (1 / 27) (1 / 27) = 4 / 9 := by
  rw [signFreeTripleResidual,
    show (4 / 9 : ℝ) * (1 / 27) * (1 / 27) = (2 / 81 : ℝ) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

theorem signFreeTripleResidual_mixed_second :
    signFreeTripleResidual (1 / 27) (4 / 9) (1 / 27) = 4 / 9 := by
  rw [signFreeTripleResidual,
    show (1 / 27 : ℝ) * (4 / 9) * (1 / 27) = (2 / 81 : ℝ) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

theorem signFreeTripleResidual_mixed_third :
    signFreeTripleResidual (1 / 27) (1 / 27) (4 / 9) = 4 / 9 := by
  rw [signFreeTripleResidual,
    show (1 / 27 : ℝ) * (1 / 27) * (4 / 9) = (2 / 81 : ℝ) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-- **THE TIGHT SYSTEM IS EXACTLY TIGHT.**  Every one of the twenty triangles of
`K_6` has `h = 4/9` under the tight weight system.  Three indices fall into two
halves, so the side pattern is either "all three together" or "two together and
one apart"; the first gives the intra value, the other three the mixed value, and
all four are `4/9`.  Distinctness is not needed — the identity holds at every
triple of indices. -/
theorem signFreeTripleResidual_tightEdgeWeight (first second third : Fin 6) :
    signFreeTripleResidual (tightEdgeWeight first second) (tightEdgeWeight first third)
      (tightEdgeWeight second third) = 4 / 9 := by
  simp only [tightEdgeWeight]
  rcases Bool.eq_false_or_eq_true (tightSide first) with hfirst | hfirst <;>
    rcases Bool.eq_false_or_eq_true (tightSide second) with hsecond | hsecond <;>
      rcases Bool.eq_false_or_eq_true (tightSide third) with hthird | hthird <;>
        simp only [hfirst, hsecond, hthird, if_true] <;>
        norm_num <;>
        first
          | exact signFreeTripleResidual_intra
          | exact signFreeTripleResidual_mixed_first
          | exact signFreeTripleResidual_mixed_second
          | exact signFreeTripleResidual_mixed_third

/-- **THE TIGHT SYSTEM OBEYS THE VERTEX-SUM LAW.**  Two same-half edges at `4/9`
and three cross edges at `1/27` give `8/9 + 1/9 = 1`, which is the stratum's row
law `Gtz.sum_sq_directionGram_erase_six`.  So the tight system is a legitimate
point of the fractional perfect matching polytope of `K_6` and is not excluded by
any vertex-sum consideration. -/
theorem sum_erase_tightEdgeWeight (index : Fin 6) :
    ∑ otherIndex ∈ Finset.univ.erase index, tightEdgeWeight index otherIndex = 1 := by
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun otherIndex => tightEdgeWeight index otherIndex) (Finset.mem_univ index)
  have hself : tightEdgeWeight index index = 4 / 9 := by simp [tightEdgeWeight]
  have hfull : ∑ otherIndex : Fin 6, tightEdgeWeight index otherIndex = 1 + 4 / 9 := by
    rw [Fin.sum_univ_six]
    fin_cases index <;> norm_num [tightEdgeWeight, tightSide]
  rw [hfull, hself] at hsplit
  linarith

/-- **AND THE NORM CAP EXCLUDES IT.**  The intra-half triangle has
`sigma + 2 sqrt p = 4/3 + 16/27 = 52/27 > 1`, so no equal-share `(6,3)` design has
these edge weights.  This is `(C2)` doing the work that `(W6)` cannot: the tight
system is a perfectly good point of the weight polytope and is killed by realness
alone. -/
theorem not_normCap_tightEdgeWeight :
    ¬ (tightEdgeWeight 0 1 + tightEdgeWeight 0 2 + tightEdgeWeight 1 2
      + 2 * Real.sqrt (tightEdgeWeight 0 1 * tightEdgeWeight 0 2 * tightEdgeWeight 1 2) ≤ 1) := by
  have hvalue : tightEdgeWeight 0 1 = 4 / 9 ∧ tightEdgeWeight 0 2 = 4 / 9
      ∧ tightEdgeWeight 1 2 = 4 / 9 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [tightEdgeWeight, tightSide]
  rw [hvalue.1, hvalue.2.1, hvalue.2.2,
    show (4 / 9 : ℝ) * (4 / 9) * (4 / 9) = (8 / 27 : ℝ) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-- The tight system is excluded already by the ROW of the cap that the squeeze
uses, in the exact hypothesis shape of
`Gtz.exists_signFreeTripleResidual_le_four_ninths`: the cap hypothesis fails at
`{0,1,2}`. -/
theorem not_cap_hypothesis_tightEdgeWeight :
    ¬ (∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
      tightEdgeWeight first second + tightEdgeWeight first third + tightEdgeWeight second third
        + 2 * Real.sqrt (tightEdgeWeight first second * tightEdgeWeight first third
          * tightEdgeWeight second third) ≤ 1) := fun hcap =>
  not_normCap_tightEdgeWeight (hcap 0 1 2 (by decide) (by decide) (by decide))

/-! ## 7. The margin, and where the bound is tight

U6 delivers `h <= 4/9`.  Two of the four cases carry explicit slack, and a
positive margin upgrades domination to STRICT domination.  This section extracts
both, and records the exact tangency structure of the light branch. -/

/-- **MARGIN FROM A LIGHT MAXIMIZING WEIGHT.**  When every edge of the triangle is
at most `bound`, the trivial estimate `h <= sigma` already gives `h <= 3 bound`,
whose margin below `4/9` is `4/9 - 3 bound`.  It is positive for
`bound < 4/27`, and this is the whole of the pen's Case 1. -/
theorem signFreeTripleResidual_le_sub_of_lightTriangle {bound firstWeight secondWeight
    thirdWeight : ℝ} (hfirst : firstWeight ≤ bound) (hsecond : secondWeight ≤ bound)
    (hthird : thirdWeight ≤ bound) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight ≤ 4 / 9 - (4 / 9 - 3 * bound) :=
  le_trans (signFreeTripleResidual_le_three_mul_of_le_bound hfirst hsecond hthird) (by linarith)

/-- **MARGIN FROM CAP SLACK.**  A heavy triangle with `9 r^3 >= 1` whose cap has
slack — `sigma + 2 r^3 <= 1 - slack` — has `h <= 4/9 - slack`.  So on the stratum
the residual falls below `4/9` by exactly the amount by which the involution
sandwich is not tight at the triple, which is the pen's Case 4 made quantitative. -/
theorem signFreeTripleResidual_le_sub_of_heavyTriangle_of_capSlack {rootBound slack firstWeight
    secondWeight thirdWeight : ℝ} (hrootNonneg : 0 ≤ rootBound) (hlarge : 1 ≤ 9 * rootBound ^ 3)
    (hfirst : rootBound ^ 2 ≤ firstWeight) (hsecond : rootBound ^ 2 ≤ secondWeight)
    (hthird : rootBound ^ 2 ≤ thirdWeight)
    (hcap : firstWeight + secondWeight + thirdWeight + 2 * rootBound ^ 3 ≤ 1 - slack) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight ≤ 4 / 9 - slack :=
  le_trans (signFreeTripleResidual_le_sub_of_normCap (pow_nonneg hrootNonneg 3)
    (sq_pow_three_le_edgeProduct_of_sq_le hfirst hsecond hthird) hcap) (by linarith)

/-- **STRICT DOMINATION FROM A STRICT CRITERION.**  When the oriented criterion
value is strictly below `4/9` the shifted block is positive DEFINITE, so
`lambda_min(Gamma[C]) > 1/3` with room.  The cap is the same one the
non-strict statement uses. -/
theorem posDef_of_orientedTripleResidual_lt_four_ninths (D : WeightedDesign 6 3)
    (hequal : IsEqualShare D) {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hcriterion : orientedTripleResidual D first second third < 4 / 9) :
    (((2 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree (directionGram D first second) (directionGram D first third)
        (directionGram D second third)).PosDef := by
  have hpick : Function.Injective ![first, second, third] := by
    intro leftSlot rightSlot hvalue
    fin_cases leftSlot <;> fin_cases rightSlot <;>
      first
        | rfl
        | exact absurd hvalue (by assumption)
        | exact absurd hvalue.symm (by assumption)
  have hinvol := isHollowInvolution_correlationInvolution_six D hequal
  have hupper := hinvol.posSemidef_one_sub_submatrix ![first, second, third] hpick
  rw [correlationInvolution_submatrix_three_eq_hollowMatrixThree D
    (fun atomIndex => hequal.leverage_pos (by norm_num) atomIndex) hfirstSecond hfirstThird
    hsecondThird] at hupper
  rw [← one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℝ)] at hupper
  refine posDef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper (by norm_num)
    (by norm_num) hupper |>.mpr ?_
  rw [orientedTripleResidual, edgeWeight, edgeWeight, edgeWeight] at hcriterion
  nlinarith [hcriterion]

/-- **WHERE THE LIGHT BRANCH IS TIGHT.**  The pen's cubic factors as
`rho(m) = 9 (m - 1/9) (m - 4/9)^2`, so the light branch's endpoint estimate
`Psi_m(3m) <= 0` holds with EQUALITY exactly at `m = 1/9` and `m = 4/9`.  The
simple root `1/9` is the square of the tetrahedral tripod's correlation `-1/3` —
the tie — and the DOUBLE root `4/9` is the square of `2/3`, the tangency where the
tight system of §6 sits. -/
theorem failureQuadratic_four_ninths_at_three_mul_eq_zero_iff (bound : ℝ) :
    failureQuadratic (4 / 9) bound (3 * bound) = 0 ↔ bound = 1 / 9 ∨ bound = 4 / 9 := by
  rw [failureQuadratic_four_ninths_at_three_mul, neg_eq_zero]
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hlinear | hsquare
    · rcases mul_eq_zero.mp hlinear with hnine | hlow
      · exact absurd hnine (by norm_num)
      · exact Or.inl (by linarith)
    · exact Or.inr (by have hroot := sq_eq_zero_iff.mp hsquare; linarith)
  · rintro (hlow | hhigh)
    · rw [hlow]; ring
    · rw [hhigh]; ring

/-- **AND WHY THE DOUBLE ROOT IS UNREACHABLE ON THE STRATUM.**  At the tangency
`m = 4/9` the equilateral triangle has `sigma = 3m = 4/3` and product
`sqrt p = m^{3/2} = 8/27`, so `sigma + 2 sqrt p = 52/27 > 1` and the norm cap
forbids it.  So the only light-branch tangency an equal-share `(6,3)` design can
realise is the simple root `m = 1/9`, and there the residual is `1/3 - 1/9 = 2/9`,
strictly below `4/9`. -/
theorem not_normCap_equilateral_four_ninths :
    ¬ ((4 / 9 : ℝ) + 4 / 9 + 4 / 9
      + 2 * Real.sqrt ((4 / 9 : ℝ) * (4 / 9) * (4 / 9)) ≤ 1) := by
  rw [show (4 / 9 : ℝ) * (4 / 9) * (4 / 9) = (8 / 27 : ℝ) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-! ## 8. Calibration

The three reference configurations of the campaign, at the level of the sign-free
residual `h`.  `Gtz.Quantitative.TripleCubicCriterion` already records them at the
level of the criterion `sigma - 3 P`; the pair of readings is what makes the
mirror visible, and the tetrahedral tripod is where they differ. -/

/-- **THE TETRAHEDRAL TRIPOD.**  Correlations `-1/3` pairwise, weights `1/9`.  Its
sign-free residual is `1/3 - 1/9 = 2/9` — because its oriented product is NEGATIVE,
so `h` reads the COMPLEMENT's criterion — while its own criterion value is exactly
`4/9`, the tie (`Gtz.criterion_hollowSymmetricThree_negThird_eq_fourNinths`).  The
gap between `2/9` and `4/9` is precisely the mirror at work. -/
theorem signFreeTripleResidual_tripod :
    signFreeTripleResidual (1 / 9) (1 / 9) (1 / 9) = 2 / 9 := by
  rw [signFreeTripleResidual,
    show (1 / 9 : ℝ) * (1 / 9) * (1 / 9) = (1 / 27 : ℝ) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-- **THE `K4` STAR.**  Correlations `1/2` pairwise, weights `1/4`.  Coherent, so
the sign-free residual and the criterion agree, both `3/8`, and
`lambda_min(Gamma) = 1/2`. -/
theorem signFreeTripleResidual_kFourStar :
    signFreeTripleResidual (1 / 4) (1 / 4) (1 / 4) = 3 / 8 := by
  rw [signFreeTripleResidual,
    show (1 / 4 : ℝ) * (1 / 4) * (1 / 4) = (1 / 8 : ℝ) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-- **THE ICOSAHEDRON.**  Weights `1/5` on all fifteen edges, so
`h = 3/5 - 3 sqrt 5 / 25`, which is `3 (1 - 1/sqrt 5) / ...` in the least-eigenvalue
reading `lambda_min(Gamma) = 1 - 1/sqrt 5`. -/
theorem signFreeTripleResidual_icosahedral :
    signFreeTripleResidual (1 / 5) (1 / 5) (1 / 5) = 3 / 5 - 3 * Real.sqrt 5 / 25 := by
  have hsquare : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpositive : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rw [signFreeTripleResidual,
    show (1 / 5 : ℝ) * (1 / 5) * (1 / 5) = (Real.sqrt 5 / 25 : ℝ) ^ 2 by
      field_simp; nlinarith [hsquare],
    Real.sqrt_sq (by positivity)]
  ring

/-- The icosahedral residual clears the threshold, with room: `3/5 - 3 sqrt 5/25`
is about `0.3317`, well under `4/9`.  The margin is real, which is why the
icosahedron is not the stratum's minimiser. -/
theorem signFreeTripleResidual_icosahedral_lt_four_ninths :
    signFreeTripleResidual (1 / 5) (1 / 5) (1 / 5) < 4 / 9 := by
  have hsquare : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpositive : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rw [signFreeTripleResidual_icosahedral]
  nlinarith [hsquare, hpositive]

/-- **U6 FIRES AT THE ICOSAHEDRON.**  `Gtz.icosaDesign` is on the stratum
(`Gtz.isEqualShare_icosaDesign`), so U6 applies; the shipped
`Gtz.icosaDesign_dominates` names `{0,2,4}` explicitly and pins the margin at
`2 - 3/sqrt 5`. -/
theorem exists_dominating_triple_icosaDesign :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      Dominates icosaDesign {first, second, third} :=
  exists_dominating_triple_of_isEqualShare icosaDesign isEqualShare_icosaDesign

/-- **U6 FIRES AT THE OCTAHEDRON.**  `Gtz.octahedronDesign` is the stratum's
degenerate member — three antipodal pairs, so three edge weights equal `1` and the
"pairwise non-parallel" hypothesis of the pen's statement FAILS.  U6 as proved
here does not use that hypothesis and covers it. -/
theorem exists_dominating_triple_octahedronDesign :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      Dominates octahedronDesign {first, second, third} :=
  exists_dominating_triple_of_isEqualShare octahedronDesign isEqualShare_octahedronDesign

/-! ## 9. The equality locus of `h = 4/9`

Which triangles achieve the bound?  Two answers, and the first one corrects a
guess the campaign carried into this workflow.

**Cap slack does NOT give a margin.**  The weight system `(2/9, 2/9, 0)` has
`sigma = 4/9`, `p = 0` and therefore `h = 4/9` on the nose, while its cap reads
`sigma + 2 sqrt p = 4/9`, a slack of `5/9` — the largest slack any triangle with
`h = 4/9` could have, since `h <= sigma <= sigma + 2 sqrt p`.  So the conjecture
that the bound is tight only where the involution sandwich is tight (equivalently
where the complementary triple is coplanar) is FALSE as a statement about a single
triangle: the tightest triangles for `h` are the ones with a VANISHING product,
not the ones with a saturated cap.  A quantitative U6 therefore cannot be obtained
by tracking cap slack alone; see
`Gtz.exists_capSlack_signFreeTripleResidual_eq_four_ninths`.

**On the equilateral locus the classification is exact and the margin is real.**
Writing `w = r^2` on all three edges, `h = 3 r^2 - 3 r^3` and

    h - 4/9 = -(1/9) (3r - 2)^2 (3r + 1),

so `h = 4/9` forces `r = 2/3`, i.e. `w = 4/9` — the tangency of §7, whose cap
reads `52/27 > 1`.  The cap in fact forces `r <= 1/2` exactly (`3 r^2 + 2 r^3 = 1`
at `r = 1/2`), and `h = 3 r^2 (1 - r)` is increasing there, so on the stratum
every equilateral triangle satisfies `h <= 3/8`, with equality exactly at
`w = 1/4` — the `K4` graphic design's star.  The margin `4/9 - 3/8 = 5/72` is
attained, so `3/8` cannot be lowered either. -/

/-- **NO MARGIN FROM CAP SLACK.**  A triangle with `h = 4/9` and cap slack `5/9`.
Exactly rational: `sigma = 4/9` and `p = 0`, so both readings are exact and no
floating point is involved. -/
theorem exists_capSlack_signFreeTripleResidual_eq_four_ninths :
    ∃ firstWeight secondWeight thirdWeight : ℝ,
      0 ≤ firstWeight ∧ 0 ≤ secondWeight ∧ 0 ≤ thirdWeight ∧
        firstWeight + secondWeight + thirdWeight
            + 2 * Real.sqrt (firstWeight * secondWeight * thirdWeight) ≤ 1 - 5 / 9 ∧
          signFreeTripleResidual firstWeight secondWeight thirdWeight = 4 / 9 := by
  refine ⟨2 / 9, 2 / 9, 0, by norm_num, by norm_num, le_refl 0, ?_, ?_⟩
  · rw [show (2 / 9 : ℝ) * (2 / 9) * 0 = 0 by ring, Real.sqrt_zero]
    norm_num
  · rw [signFreeTripleResidual, show (2 / 9 : ℝ) * (2 / 9) * 0 = 0 by ring, Real.sqrt_zero]
    norm_num

/-- The equilateral residual in the root coordinate: `h = 3 r^2 - 3 r^3`. -/
theorem signFreeTripleResidual_equilateral {rootBound : ℝ} (hrootNonneg : 0 ≤ rootBound) :
    signFreeTripleResidual (rootBound ^ 2) (rootBound ^ 2) (rootBound ^ 2)
      = 3 * rootBound ^ 2 - 3 * rootBound ^ 3 := by
  rw [signFreeTripleResidual,
    show rootBound ^ 2 * rootBound ^ 2 * rootBound ^ 2 = (rootBound ^ 3) ^ 2 by ring,
    Real.sqrt_sq (pow_nonneg hrootNonneg 3)]
  ring

/-- **THE EQUILATERAL EQUALITY IDENTITY.**  `h - 4/9 = -(1/9)(3r-2)^2(3r+1)`.  The
double root `r = 2/3` is the tangency of §7 — the square of the pen's `w = 4/9` —
and the simple root `r = -1/3` is outside the range of a root of a weight. -/
theorem signFreeTripleResidual_equilateral_sub_four_ninths {rootBound : ℝ}
    (hrootNonneg : 0 ≤ rootBound) :
    signFreeTripleResidual (rootBound ^ 2) (rootBound ^ 2) (rootBound ^ 2) - 4 / 9
      = -((1 / 9) * (3 * rootBound - 2) ^ 2 * (3 * rootBound + 1)) := by
  rw [signFreeTripleResidual_equilateral hrootNonneg]; ring

/-- **THE CAP PINS THE EQUILATERAL ROOT AT `1/2`.**  `3 r^2 + 2 r^3` is strictly
increasing on `r >= 0` and equals `1` exactly at `r = 1/2`, so the norm cap on an
equilateral triangle says precisely `w = r^2 <= 1/4`.  The `K4` graphic design's
star sits at that boundary and saturates the cap.  Nonnegativity of the root is
NOT needed: the cap alone forces the bound. -/
theorem le_half_of_normCap_equilateral {rootBound : ℝ}
    (hcap : 3 * rootBound ^ 2 + 2 * rootBound ^ 3 ≤ 1) : rootBound ≤ 1 / 2 := by
  by_contra hlarge
  rw [not_le] at hlarge
  nlinarith [hlarge, sq_nonneg (rootBound - 1 / 2), sq_nonneg rootBound]

/-- **THE EQUILATERAL CLASSIFICATION.**  Every equilateral triangle of the stratum
has `h <= 3/8`, a margin of `5/72` below `4/9`, with equality exactly at the `K4`
star's weight `1/4`.  So on this locus the bound of U6 is far from tight, and
`3/8` is itself sharp. -/
theorem signFreeTripleResidual_equilateral_le_three_eighths {rootBound : ℝ}
    (hrootNonneg : 0 ≤ rootBound) (hcap : 3 * rootBound ^ 2 + 2 * rootBound ^ 3 ≤ 1) :
    signFreeTripleResidual (rootBound ^ 2) (rootBound ^ 2) (rootBound ^ 2) ≤ 3 / 8 := by
  have hhalf := le_half_of_normCap_equilateral hcap
  rw [signFreeTripleResidual_equilateral hrootNonneg]
  nlinarith [hhalf, hrootNonneg, sq_nonneg (rootBound - 1 / 2),
    mul_nonneg hrootNonneg hrootNonneg]

/-- Sharpness of the equilateral classification: the `K4` star attains `3/8`. -/
theorem signFreeTripleResidual_equilateral_half :
    signFreeTripleResidual ((1 / 2 : ℝ) ^ 2) ((1 / 2 : ℝ) ^ 2) ((1 / 2 : ℝ) ^ 2) = 3 / 8 := by
  rw [signFreeTripleResidual_equilateral (by norm_num : (0 : ℝ) ≤ 1 / 2)]; norm_num

/-- ... and the cap it saturates is an equality there, so the `K4` star is the
extremal equilateral configuration in both readings at once. -/
theorem normCap_equilateral_half : 3 * ((1 : ℝ) / 2) ^ 2 + 2 * ((1 : ℝ) / 2) ^ 3 = 1 := by
  norm_num

/-- **STRICT RESIDUAL ON THE EQUILATERAL LOCUS**, in the form the strict-domination
bridge consumes: below `4/9` by at least `5/72`. -/
theorem signFreeTripleResidual_equilateral_lt_four_ninths {rootBound : ℝ}
    (hrootNonneg : 0 ≤ rootBound) (hcap : 3 * rootBound ^ 2 + 2 * rootBound ^ 3 ≤ 1) :
    signFreeTripleResidual (rootBound ^ 2) (rootBound ^ 2) (rootBound ^ 2) < 4 / 9 :=
  lt_of_le_of_lt (signFreeTripleResidual_equilateral_le_three_eighths hrootNonneg hcap)
    (by norm_num)

/-! ## 10. The exact light branch

The pen's Cases 1 and 2 conclude `h <= 4/9`, but the machinery they run on gives a
strictly sharper answer and gives it on the WHOLE light range rather than on
`r^2 <= 2/9`.  The failure quadratic's two endpoint values are

    Psi^t_m(t) = -9 m^2 (t - 2m),        Psi^t_m(3m) = (3m - t)^2 - 9 m^3,

so the smallest threshold `t` the endpoint argument can certify is exactly
`max (2m) (3m - 3 m^{3/2})` — the first endpoint asking `t >= 2m`, the second
asking `|3m - t| <= 3 m^{3/2}`.  Both values are attained: `2m` at the degenerate
triangle `(m, m, 0)`, whose product vanishes, and `3m - 3 m^{3/2}` at the
equilateral triangle `(m, m, m)`.  So the light branch is
`h <= max (2 r^2) (3 r^2 - 3 r^3)`, sharply, and `4/9` is what that becomes at the
worst admissible `r`.

This is where the margin of the light half of U6 lives, and it explains the
equality witness of §9: `(2/9, 2/9, 0)` is the degenerate endpoint at `r^2 = 2/9`,
where `2 r^2 = 4/9` exactly. -/

/-- **THE EXACT LIGHT-BRANCH BOUND.**  A triangle all of whose edge weights are at
most `r^2` has `h <= max (2 r^2) (3 r^2 - 3 r^3)`.  No cap, no coherence, no
restriction on `r` beyond nonnegativity — and both branches of the maximum are
attained, so the bound cannot be improved. -/
theorem signFreeTripleResidual_le_max_of_lightTriangle {rootBound firstWeight secondWeight
    thirdWeight : ℝ} (hrootNonneg : 0 ≤ rootBound) (hthirdNonneg : 0 ≤ thirdWeight)
    (hfirst : firstWeight ≤ rootBound ^ 2) (hsecond : secondWeight ≤ rootBound ^ 2)
    (hthird : thirdWeight ≤ rootBound ^ 2) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight
      ≤ max (2 * rootBound ^ 2) (3 * rootBound ^ 2 - 3 * rootBound ^ 3) := by
  have hlowBranch : 2 * rootBound ^ 2
      ≤ max (2 * rootBound ^ 2) (3 * rootBound ^ 2 - 3 * rootBound ^ 3) := le_max_left _ _
  have hhighBranch : 3 * rootBound ^ 2 - 3 * rootBound ^ 3
      ≤ max (2 * rootBound ^ 2) (3 * rootBound ^ 2 - 3 * rootBound ^ 3) := le_max_right _ _
  have hbelowThree : max (2 * rootBound ^ 2) (3 * rootBound ^ 2 - 3 * rootBound ^ 3)
      ≤ 3 * rootBound ^ 2 + 3 * rootBound ^ 3 :=
    max_le (by nlinarith [sq_nonneg rootBound, pow_nonneg hrootNonneg 3])
      (by nlinarith [pow_nonneg hrootNonneg 3])
  rcases le_or_gt (firstWeight + secondWeight + thirdWeight)
    (max (2 * rootBound ^ 2) (3 * rootBound ^ 2 - 3 * rootBound ^ 3)) with hsmallSum | hlargeSum
  · exact le_trans (signFreeTripleResidual_le_sum firstWeight secondWeight thirdWeight) hsmallSum
  refine signFreeTripleResidual_le_of_lightTriangle_endpoints
    (lower := max (2 * rootBound ^ 2) (3 * rootBound ^ 2 - 3 * rootBound ^ 3))
    (upper := 3 * rootBound ^ 2) hthirdNonneg hfirst hsecond hthird ?_ ?_ hlargeSum.le
    (by linarith)
  · rw [failureQuadratic_at_threshold]
    exact neg_nonpos.mpr (mul_nonneg (by positivity) (by linarith))
  · rw [failureQuadratic_at_three_mul]
    nlinarith [hhighBranch, hbelowThree, pow_nonneg hrootNonneg 3, sq_nonneg rootBound]

/-- The degenerate endpoint is attained: `(r^2, r^2, 0)` has `h = 2 r^2` exactly. -/
theorem signFreeTripleResidual_degenerate (rootBound : ℝ) :
    signFreeTripleResidual (rootBound ^ 2) (rootBound ^ 2) 0 = 2 * rootBound ^ 2 := by
  rw [signFreeTripleResidual, show rootBound ^ 2 * rootBound ^ 2 * 0 = 0 by ring, Real.sqrt_zero]
  ring

/-- **THE LIGHT BRANCH AT THE WORST ROOT.**  At `r^2 = 2/9` — the top of the pen's
light range — the exact bound is `max (4/9) (2/3 - 3 (2/9)^{3/2}) = 4/9`, so the
constant `4/9` of Cases 1 and 2 is precisely the degenerate endpoint's value there
and cannot be lowered.  Below that root the bound is strictly smaller: for
`r^2 < 2/9` the light branch gives `h < 4/9`. -/
theorem signFreeTripleResidual_lt_four_ninths_of_lightTriangle_of_lt {rootBound firstWeight
    secondWeight thirdWeight : ℝ} (hrootNonneg : 0 ≤ rootBound) (hthirdNonneg : 0 ≤ thirdWeight)
    (hsmallRoot : rootBound ^ 2 < 2 / 9) (hfirst : firstWeight ≤ rootBound ^ 2)
    (hsecond : secondWeight ≤ rootBound ^ 2) (hthird : thirdWeight ≤ rootBound ^ 2) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight < 4 / 9 := by
  refine lt_of_le_of_lt (signFreeTripleResidual_le_max_of_lightTriangle hrootNonneg hthirdNonneg
    hfirst hsecond hthird) (max_lt (by linarith) ?_)
  nlinarith [hsmallRoot, pow_nonneg hrootNonneg 3]

end Gtz
