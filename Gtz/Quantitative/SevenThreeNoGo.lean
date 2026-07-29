/-
# The (7,3) no-go corpus: dead routes closed in the kernel

Six structural obstructions at the `(7,3)` frontier, each landed as a theorem so
that no later campaign re-enters a dead route.  Everything is exact arithmetic;
the only algebraic number anywhere is `sqrt 3`, handled through its square.

## 1.  Kneser disjointness (the topology no-go)

For DISJOINT triples `T`, `T'` of a `(7,3)` design at uniform weight `1/7`,

    `S_T + S_T' = 7*1 - g_d g_d^T  >=  4*1`   (`d` the seventh atom, `l_d <= 3`),

so no direction can starve both triples: the 35 failure cones are pairwise
disjoint along the Kneser graph `K(7,3)`.  POLARITY, recorded here so nobody
tries again: Borsuk–Ulam-style arguments need overlapping bad sets to force a
covering obstruction; here DISJOINTNESS is forced and covering is exactly what
remains open, so the topological route cannot fire.

## 2.  The clustering no-go (axis spillover)

At uniform share `3/7` the unit directions satisfy
`sum_c <u_c, y>^2 = (7/3) |y|^2`, while a single direction carries at most
`|y|^2`.  Hence every axis leaks: after removing ANY two atoms the remaining
five still carry at least `(1/3) |y|^2` of every axis.  A `(3,2,2)` clustering
ansatz — each axis served by at most two atoms — is therefore not isotropic.

## 3.  The deflation cancellation (Schur-route no-go)

Schur-deflating a heavy atom and invoking rank-2 GTZ on the compressed design
buys the margin `t_1/(1-t_1)` and pays the coupling gate
`l_b gamma_1b^2 + l_c gamma_1c^2 <= s_1 (1 - 1/l_1)/(1 - t_1)`.  The kernel
content landed here: the raw gate bound COLLAPSES, `s_1 (1 - 1/l_1) = t_1 (l_1 - 1)`
identically, and at a FIXED share the collapsed bound
`deflationGateBound s l = s (l-1)/(l-s)` is strictly below the share `s` for
every leverage, with `s` as its unattained supremum — making the deflated atom
heavier buys nothing, even in the limit `l_1 = infinity`.  (The Schur-complement
derivation of the gate itself is pen-side; what is mechanized is the exact
cancellation and the no-freedom bounds, which are what kill the route.)

## 4.  Field-blindness of the interlacing family (MSS/paving no-go)

The `(4,2)` member of the 2025 interlacing family (Xu, arXiv:2508.10452) is
`6 t^2 - 6 t + 1`, with smallest root `(3 - sqrt 3)/6`; the bound it certifies is
`4 * (3 - sqrt 3)/6 = 2 - 2/sqrt 3 = Gtz.alphaRankTwo` — EXACTLY the sharp
COMPLEX constant attained by the `C^2` SIC that refutes complex GTZ.  A
field-blind method that is exact on `C` cannot prove the real statement, and R3
is precisely a real-versus-complex separation.  At `(7,3)` the family's cubic
`35 t^3 - 45 t^2 + 15 t - 1` already has a root below `1/7`, so its guarantee
sits strictly below the domination threshold there as well.  (The adjacent
mixture-root refutation `Gtz.not_mixedRootAtLeastOne_sevenThree` is ALREADY
LANDED in `Gtz/Reduction/MixedCharPolynomial.lean`; only the calibration against
`alphaRankTwo` is new.)

## 5.  The uniform-aggregate no-go at the capacity point

At uniform share `3/7` and the capacity slack `tau == 2/3`, the determinant
clauses of the ordered distinct triples total the frame-independent constant

    `sum_(a,b,c) det((2/3)*1 + M[{a,b,c}]) = -224/9 = 6 * (-112/27)`,

`-112/27` being the 35-clause unordered total.  Negative and CONSTANT: no
averaging or aggregate selector exists on the stratum.  The surviving reading is
localized: through EVERY pair the five completions total
`-8/27 - (4/3) w_ab < 0`, so every pair owns a failing completion at the
capacity point (`exists_involSlackDeterminant_capacity_neg_sevenThree`).
OVERLAP FLAG: a sibling module of this workflow lands the general weighted
aggregate identity (P2's C-AGG/C-PAIR); the lemmas here are the self-contained
capacity-point instances under distinct names, derived only from the landed row
law and supply chain.

## 6.  The deletion-corner fence (the R4 boundary's first pigeonhole)

A `(7,3)` design whose atoms include two ZERO vectors is a five-atom design in
disguise, and `Gtz.gtzWeighted_of_le_five` already dominates there: a dominating
triple exists unconditionally.  NOTE the honest transport: `Gtz.WeightedDesign`
forbids zero WEIGHTS (`weight_pos`), so the pen's "two atoms of weight zero"
corner is stated at zero ATOMS — the in-structure face of the same corner, an
atom of share zero.

## Not landed, and why

* The unordered 35-subset form of the `-112/27` total: the ordered-to-powersetCard
  bridge (each 3-subset counted `6` times) is a separate combinatorial lemma the
  ordered form does not need; the ordered total and the per-pair localization
  carry the mathematical content.
* A uniform-stratum sign-blind no-go: the landed
  `Gtz.not_signBlindGoodTripleCovering_seven` is refuted at the replicated
  icosahedron, whose shares are `1/4, 1/4, 1/2, ...` — OFF the uniform stratum —
  and on-stratum witnesses (basis-plus-tetrapod) contain sign-blind good
  triples, so the restricted question is genuinely open and no bridging
  corollary is honest.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Design.FrameConservation
import Gtz.Quantitative.WeightedBandCovering
import Gtz.Complex.SharpConstantLedger
import Gtz.Reduction.Reductions

namespace Gtz

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {m k : ℕ}

/-! ## 1. Kneser disjointness: disjoint triples can never share a failure witness -/

/-- **The whole-design atom sum at uniform weight `1/7` is `7 * I`.**  Parseval with
the weight pulled out: `sum_c g_c g_c^T = 7 * sum_c (1/7) g_c g_c^T = 7 * I`. -/
theorem subsetSum_univ_sevenThree_of_uniformWeight (D : WeightedDesign 7 3)
    (huniformWeight : ∀ atomIndex, D.weight atomIndex = 1 / 7) :
    subsetSum D Finset.univ = (7 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have hparseval := D.isParseval
  have hpull : ∑ atomIndex, D.weight atomIndex • atomMatrix (D.atom atomIndex)
      = (1 / 7 : ℝ) • ∑ atomIndex, atomMatrix (D.atom atomIndex) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun atomIndex _ => by rw [huniformWeight atomIndex]
  rw [hpull] at hparseval
  calc subsetSum D Finset.univ
      = ((7 : ℝ) * (1 / 7 : ℝ)) • subsetSum D Finset.univ := by norm_num
    _ = (7 : ℝ) • ((1 / 7 : ℝ) • ∑ atomIndex, atomMatrix (D.atom atomIndex)) := by
        rw [← smul_smul, subsetSum]
    _ = (7 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by rw [hparseval]

/-- **THE KNESER SPLIT.**  Two disjoint triples of a `(7,3)` design at uniform
weight `1/7` see the whole frame except the seventh atom:
`S_T + S_T' = 7*1 - g_d g_d^T`.  Pure additivity of `subsetSum` against the
Parseval total — no share, no leverage hypothesis. -/
theorem subsetSum_disjoint_add_eq_seven_smul_one_sub_atomMatrix (D : WeightedDesign 7 3)
    (huniformWeight : ∀ atomIndex, D.weight atomIndex = 1 / 7)
    {tripleLeft tripleRight : Finset (Fin 7)} (hdisjoint : Disjoint tripleLeft tripleRight)
    (hleftCard : tripleLeft.card = 3) (hrightCard : tripleRight.card = 3)
    {oddIndex : Fin 7} (hodd : oddIndex ∉ tripleLeft ∪ tripleRight) :
    subsetSum D tripleLeft + subsetSum D tripleRight
      = (7 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (D.atom oddIndex) := by
  have hunion : subsetSum D tripleLeft + subsetSum D tripleRight
      = subsetSum D (tripleLeft ∪ tripleRight) := by
    rw [subsetSum, subsetSum, subsetSum, ← Finset.sum_union hdisjoint]
  have hunionCard : (tripleLeft ∪ tripleRight).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisjoint, hleftCard, hrightCard]
  have hinsert : insert oddIndex (tripleLeft ∪ tripleRight) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem hodd, hunionCard, Fintype.card_fin]
  have hsplit : subsetSum D Finset.univ
      = atomMatrix (D.atom oddIndex) + subsetSum D (tripleLeft ∪ tripleRight) := by
    rw [← hinsert, subsetSum, subsetSum, Finset.sum_insert hodd]
  rw [subsetSum_univ_sevenThree_of_uniformWeight D huniformWeight] at hsplit
  rw [hunion, eq_sub_iff_add_eq, add_comm (subsetSum D (tripleLeft ∪ tripleRight))]
  exact hsplit.symm

/-- **A leverage cap makes the atom a Loewner cap**: `cap * 1 - g g^T` is positive
semidefinite as soon as `|g|^2 <= cap`.  Rank-generic; the Cauchy–Schwarz step is
the whole proof. -/
theorem posSemidef_smul_one_sub_atomMatrix_of_leverage_le {atomVector : Fin k → ℝ}
    {capValue : ℝ} (hcap : leverageOf atomVector ≤ capValue) :
    (capValue • (1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix atomVector).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · have hatom : (atomMatrix atomVector).IsHermitian := (posSemidef_atomMatrix atomVector).1
    have hone : ((capValue : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ)).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]
    exact hone.sub hatom
  · intro probe
    have hstar : star probe = probe := rfl
    rw [hstar, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul,
      smul_eq_mul, dotProduct_comm probe atomVector]
    have hcauchy := dotProduct_sq_le_mul atomVector probe
    rw [← leverageOf_eq_dotProduct] at hcauchy
    have hprobeNonneg : 0 ≤ probe ⬝ᵥ probe := by
      rw [← leverageOf_eq_dotProduct]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith [hcauchy, hcap, hprobeNonneg, sq_nonneg (atomVector ⬝ᵥ probe)]

/-- **THE KNESER FLOOR.**  With the seventh atom's leverage at most `3` — automatic
on the equal-share stratum, where every leverage is exactly `3` and the floor is
attained — the two disjoint triple sums together stay `>= 4 * 1` in the Loewner
order. -/
theorem posSemidef_subsetSum_disjoint_add_sub_four_sevenThree (D : WeightedDesign 7 3)
    (huniformWeight : ∀ atomIndex, D.weight atomIndex = 1 / 7)
    {tripleLeft tripleRight : Finset (Fin 7)} (hdisjoint : Disjoint tripleLeft tripleRight)
    (hleftCard : tripleLeft.card = 3) (hrightCard : tripleRight.card = 3)
    {oddIndex : Fin 7} (hodd : oddIndex ∉ tripleLeft ∪ tripleRight)
    (hoddLeverage : leverageOf (D.atom oddIndex) ≤ 3) :
    (subsetSum D tripleLeft + subsetSum D tripleRight
      - (4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  rw [subsetSum_disjoint_add_eq_seven_smul_one_sub_atomMatrix D huniformWeight hdisjoint
    hleftCard hrightCard hodd]
  have hshape : (7 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (D.atom oddIndex)
      - (4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = (3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (D.atom oddIndex) := by
    module
  rw [hshape]
  exact posSemidef_smul_one_sub_atomMatrix_of_leverage_le hoddLeverage

/-- **DISJOINT TRIPLES NEVER SHARE A FAILURE WITNESS.**  No nonzero direction can
be starved (`y^T S_T y < |y|^2`) by both of two disjoint triples: their sums
total at least `4 |y|^2 > 2 |y|^2`.  So the 35 failure cones are pairwise
disjoint along the Kneser graph `K(7,3)`.  POLARITY: this forces DISJOINTNESS,
not covering — Borsuk–Ulam-style topology, which needs overlapping bad sets,
cannot fire on this problem. -/
theorem not_dotProduct_lt_of_disjoint_triples_sevenThree (D : WeightedDesign 7 3)
    (huniformWeight : ∀ atomIndex, D.weight atomIndex = 1 / 7)
    {tripleLeft tripleRight : Finset (Fin 7)} (hdisjoint : Disjoint tripleLeft tripleRight)
    (hleftCard : tripleLeft.card = 3) (hrightCard : tripleRight.card = 3)
    {oddIndex : Fin 7} (hodd : oddIndex ∉ tripleLeft ∪ tripleRight)
    (hoddLeverage : leverageOf (D.atom oddIndex) ≤ 3)
    {probe : Fin 3 → ℝ} (hprobe : probe ≠ 0) :
    ¬ (probe ⬝ᵥ (subsetSum D tripleLeft *ᵥ probe) < probe ⬝ᵥ probe
        ∧ probe ⬝ᵥ (subsetSum D tripleRight *ᵥ probe) < probe ⬝ᵥ probe) := by
  rintro ⟨hleftStarved, hrightStarved⟩
  have hfloor := posSemidef_subsetSum_disjoint_add_sub_four_sevenThree D huniformWeight
    hdisjoint hleftCard hrightCard hodd hoddLeverage
  have hquad := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hfloor).2 probe
  have hstar : star probe = probe := rfl
  rw [hstar, Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at hquad
  have hpositive : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobe
  linarith

/-- **The equal-share reading**: on the `(7,3)` equal-share stratum — weights
`1/7`, leverages `3`, the stratum every classical witness inhabits — the cone
disjointness is unconditional: no hypothesis on the seventh atom survives,
because its leverage is pinned at exactly `3` and the floor `4 * 1` is attained. -/
theorem not_dotProduct_lt_of_disjoint_triples_of_isEqualShare (D : WeightedDesign 7 3)
    (hequal : IsEqualShare D)
    {tripleLeft tripleRight : Finset (Fin 7)} (hdisjoint : Disjoint tripleLeft tripleRight)
    (hleftCard : tripleLeft.card = 3) (hrightCard : tripleRight.card = 3)
    {oddIndex : Fin 7} (hodd : oddIndex ∉ tripleLeft ∪ tripleRight)
    {probe : Fin 3 → ℝ} (hprobe : probe ≠ 0) :
    ¬ (probe ⬝ᵥ (subsetSum D tripleLeft *ᵥ probe) < probe ⬝ᵥ probe
        ∧ probe ⬝ᵥ (subsetSum D tripleRight *ᵥ probe) < probe ⬝ᵥ probe) := by
  have huniformWeight : ∀ atomIndex : Fin 7, D.weight atomIndex = 1 / 7 := fun atomIndex => by
    rw [hequal.weight_eq atomIndex]
    norm_num
  have hoddLeverage : leverageOf (D.atom oddIndex) ≤ 3 := by
    rw [hequal.leverage_eq oddIndex]
    norm_num
  exact not_dotProduct_lt_of_disjoint_triples_sevenThree D huniformWeight hdisjoint
    hleftCard hrightCard hodd hoddLeverage hprobe

/-! ## 2. The clustering no-go: every axis spills over -/

/-- **The uniform-share axis-energy total**: at constant share `s` the unit
directions carry `sum_c <u_c, y>^2 = s⁻¹ |y|^2` on every probe.  The frame law
read as a quadratic form; size- and rank-generic. -/
theorem sum_sq_dotProduct_unitAtom_of_uniformShare (D : WeightedDesign m k)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hpositive : 0 < shareValue) (probe : Fin k → ℝ) :
    ∑ atomIndex, (unitAtom D atomIndex ⬝ᵥ probe) ^ 2
      = shareValue⁻¹ * (probe ⬝ᵥ probe) := by
  have hframe := frameLaw_bilinear D probe probe
  have hpull : ∑ atomIndex, atomShare D atomIndex
        * ((probe ⬝ᵥ unitAtom D atomIndex) * (unitAtom D atomIndex ⬝ᵥ probe))
      = shareValue * ∑ atomIndex, (unitAtom D atomIndex ⬝ᵥ probe) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [huniform atomIndex, dotProduct_comm probe (unitAtom D atomIndex), ← pow_two]
  rw [hpull] at hframe
  rw [inv_mul_eq_div, eq_div_iff hpositive.ne', mul_comm]
  exact hframe

/-- **A single direction carries at most `|y|^2` of any axis** — Cauchy–Schwarz
against `|u_c| <= 1`, with no hypothesis at all (a degenerate atom carries `0`). -/
theorem sq_dotProduct_unitAtom_le_dotProduct_self (D : WeightedDesign m k)
    (atomIndex : Fin m) (probe : Fin k → ℝ) :
    (unitAtom D atomIndex ⬝ᵥ probe) ^ 2 ≤ probe ⬝ᵥ probe := by
  have hcauchy := dotProduct_sq_le_mul (unitAtom D atomIndex) probe
  have hunit : unitAtom D atomIndex ⬝ᵥ unitAtom D atomIndex ≤ 1 := by
    rw [← leverageOf_eq_dotProduct]
    exact leverageOf_unitAtom_le_one D atomIndex
  have hunitNonneg : 0 ≤ unitAtom D atomIndex ⬝ᵥ unitAtom D atomIndex := by
    rw [← leverageOf_eq_dotProduct]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hprobeNonneg : 0 ≤ probe ⬝ᵥ probe := by
    rw [← leverageOf_eq_dotProduct]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [hcauchy, hunit, hunitNonneg, hprobeNonneg]

/-- **THE SPILLOVER LEMMA.**  At `(7,3)`-uniform share, remove ANY two atoms: the
remaining five directions still carry at least `(1/3) |y|^2` of every axis,
because the total is `(7/3) |y|^2` and each removed atom holds at most `|y|^2`.
This is the exact quantitative form of the clustering no-go: no axis is served
by just two atoms, so a `(3,2,2)` cluster pattern cannot be isotropic. -/
theorem third_le_sum_sdiff_sq_dotProduct_unitAtom_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {firstIndex secondIndex : Fin 7} (hdistinct : firstIndex ≠ secondIndex)
    (probe : Fin 3 → ℝ) :
    1 / 3 * (probe ⬝ᵥ probe)
      ≤ ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
          (unitAtom D otherIndex ⬝ᵥ probe) ^ 2 := by
  have htotal := sum_sq_dotProduct_unitAtom_of_uniformShare D huniform (by norm_num) probe
  rw [show ((3 : ℝ) / 7)⁻¹ = 7 / 3 by norm_num] at htotal
  have hsplit := Finset.sum_sdiff (f := fun otherIndex => (unitAtom D otherIndex ⬝ᵥ probe) ^ 2)
    (Finset.subset_univ ({firstIndex, secondIndex} : Finset (Fin 7)))
  rw [Finset.sum_pair hdistinct] at hsplit
  have hfirstCap := sq_dotProduct_unitAtom_le_dotProduct_self D firstIndex probe
  have hsecondCap := sq_dotProduct_unitAtom_le_dotProduct_self D secondIndex probe
  linarith [hsplit, htotal, hfirstCap, hsecondCap]

/-! ## 3. The deflation cancellation: making the pivot heavier buys nothing -/

/-- **The deflation gate bound** at share `s` and pivot leverage `l`:
`s (l - 1)/(l - s)`.  This is the raw Schur gate `s_1 (1 - 1/l_1)/(1 - t_1)`
after the cancellation of `deflationGate_cancellation`, reparameterized by the
share `s = t_1 l_1` (`deflationGateBound_eq_weight_gate`). -/
noncomputable def deflationGateBound (shareValue leverageOne : ℝ) : ℝ :=
  shareValue * (leverageOne - 1) / (leverageOne - shareValue)

/-- **THE CANCELLATION IDENTITY.**  The deflation gate's numerator collapses:
`s_1 (1 - nu_1) = (t_1 l_1)(1 - 1/l_1) = t_1 (l_1 - 1)` — the leverage entering
through the share cancels against the leverage entering through `nu_1 = 1/l_1`,
IDENTICALLY in `l_1`.  This is the exact reason Schur-deflating a heavier pivot
buys nothing: the pivot's leverage never survives into the gate. -/
theorem deflationGate_cancellation (weightOne leverageOne : ℝ)
    (hleverage : leverageOne ≠ 0) :
    weightOne * leverageOne * (1 - leverageOne⁻¹) / (1 - weightOne)
      = weightOne * (leverageOne - 1) / (1 - weightOne) := by
  have hnumerator : weightOne * leverageOne * (1 - leverageOne⁻¹)
      = weightOne * (leverageOne - 1) := by
    field_simp
  rw [hnumerator]

/-- The cancelled gate in weight coordinates equals `deflationGateBound` in share
coordinates: with `t_1 = s/l_1`, `t_1 (l_1 - 1)/(1 - t_1) = s (l_1 - 1)/(l_1 - s)`.
Both sides degenerate to `0` together when `l_1 = s` (weight one), so only
`l_1 /= 0` is needed. -/
theorem deflationGateBound_eq_weight_gate (shareValue leverageOne : ℝ)
    (hleverage : leverageOne ≠ 0) :
    shareValue / leverageOne * (leverageOne - 1) / (1 - shareValue / leverageOne)
      = deflationGateBound shareValue leverageOne := by
  rw [deflationGateBound]
  rcases eq_or_ne (leverageOne - shareValue) 0 with hboundary | hregular
  · have hdenominator : 1 - shareValue / leverageOne = 0 := by
      have hequal : leverageOne = shareValue := by linarith [sub_eq_zero.mp hboundary]
      rw [← hequal, div_self hleverage, sub_self]
    rw [hboundary, hdenominator, div_zero, div_zero]
  · have hdenominator : 1 - shareValue / leverageOne
        = (leverageOne - shareValue) / leverageOne := by
      field_simp
    rw [hdenominator, div_div_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
      mul_div_assoc, div_self hleverage, mul_one]

/-- **NO FREEDOM BELOW THE SHARE.**  At fixed share `0 < s < 1` the gate bound is
strictly below `s` for EVERY admissible pivot leverage: `s (l-1)/(l-s) < s`. -/
theorem deflationGateBound_lt_share {shareValue leverageOne : ℝ}
    (hsharePos : 0 < shareValue) (hshareLt : shareValue < 1)
    (hleverage : shareValue < leverageOne) :
    deflationGateBound shareValue leverageOne < shareValue := by
  have hdenominator : 0 < leverageOne - shareValue := sub_pos.mpr hleverage
  rw [deflationGateBound, div_lt_iff₀ hdenominator]
  have hnumerator : leverageOne - 1 < leverageOne - shareValue := by linarith
  exact mul_lt_mul_of_pos_left hnumerator hsharePos

/-- **AND `s` IS THE EXACT, UNATTAINED SUPREMUM**: the gate bound approaches the
share as the pivot leverage grows, so `l_1 = infinity` is the supremum and even
there the gate cannot exceed the share.  Together with
`deflationGateBound_lt_share` this is the kernel form of "the deflation route
costs exactly what it buys". -/
theorem exists_deflationGateBound_near_share {shareValue : ℝ}
    (hsharePos : 0 < shareValue) (hshareLt : shareValue < 1)
    {marginValue : ℝ} (hmargin : 0 < marginValue) :
    ∃ leverageOne : ℝ, shareValue < leverageOne
      ∧ shareValue - marginValue < deflationGateBound shareValue leverageOne := by
  have hnumerator : 0 < shareValue * (1 - shareValue) + marginValue := by nlinarith
  have hquotPos : 0 < (shareValue * (1 - shareValue) + marginValue) / marginValue :=
    div_pos hnumerator hmargin
  refine ⟨shareValue + (shareValue * (1 - shareValue) + marginValue) / marginValue,
    by linarith, ?_⟩
  have hgap : shareValue + (shareValue * (1 - shareValue) + marginValue) / marginValue
      - shareValue = (shareValue * (1 - shareValue) + marginValue) / marginValue := by
    ring
  rw [deflationGateBound, hgap, lt_div_iff₀ hquotPos]
  have hclear : marginValue * ((shareValue * (1 - shareValue) + marginValue) / marginValue)
      = shareValue * (1 - shareValue) + marginValue := by
    rw [mul_comm, div_mul_cancel₀ _ hmargin.ne']
  nlinarith [hclear, hquotPos, hmargin]

/-! ## 4. Field-blindness: the interlacing family's (4,2) constant IS the complex
SIC constant -/

/-- **The `(4,2)` interlacing quadratic `6 t^2 - 6 t + 1` has exactly the roots
`(3 -+ sqrt 3)/6`.**  The `(4,2)` member of the interlacing family of Xu
(arXiv:2508.10452), factored over its true splitting field. -/
theorem xuQuadraticFourTwo_eq_zero_iff (rootCandidate : ℝ) :
    6 * rootCandidate ^ 2 - 6 * rootCandidate + 1 = 0
      ↔ rootCandidate = (3 - Real.sqrt 3) / 6
        ∨ rootCandidate = (3 + Real.sqrt 3) / 6 := by
  have hsquare : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · intro hzero
    have hfactor : 6 * ((rootCandidate - (3 - Real.sqrt 3) / 6)
        * (rootCandidate - (3 + Real.sqrt 3) / 6)) = 0 := by
      linear_combination hzero - (1 / 6 : ℝ) * hsquare
    rcases mul_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left (by norm_num)) with
      hleft | hright
    · exact Or.inl (sub_eq_zero.mp hleft)
    · exact Or.inr (sub_eq_zero.mp hright)
  · rintro (rfl | rfl)
    · linear_combination (1 / 6 : ℝ) * hsquare
    · linear_combination (1 / 6 : ℝ) * hsquare

/-- The smaller root is positive — the family's constant is a genuine bound. -/
theorem xuQuadraticRootFourTwo_pos : 0 < (3 - Real.sqrt 3) / 6 := by
  have hsquare : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hnonneg := Real.sqrt_nonneg 3
  nlinarith [hsquare, hnonneg]

/-- And it is the SMALLEST root: `(3 - sqrt 3)/6 < (3 + sqrt 3)/6`. -/
theorem xuQuadraticRootFourTwo_lt_mirror :
    (3 - Real.sqrt 3) / 6 < (3 + Real.sqrt 3) / 6 := by
  have hpositive : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- **THE FIELD-BLINDNESS ONE-LINER.**  The `(4,2)` interlacing bound
`m * t_min = 4 * (3 - sqrt 3)/6` equals `Gtz.alphaRankTwo = 2 - 2/sqrt 3` — the
sharp COMPLEX rank-two constant, attained exactly at the `C^2` SIC that refutes
complex GTZ (`Gtz.sicPair_det_at_alphaRankTwo`).  So the interlacing family is
EXACT over `C` at `(4,2)`: being field-blind, it can never certify the real
value `1`, and rank-3 GTZ is precisely a real-versus-complex separation
(`Gtz.discriminantCovering_seven_iff_rank_three` reduces it to `(7,3)`, where
the complex statement fails).  The route is structurally dead, not merely
quantitatively short. -/
theorem four_mul_xuQuadraticRootFourTwo_eq_alphaRankTwo :
    4 * ((3 - Real.sqrt 3) / 6) = alphaRankTwo := by
  have hsquare : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpositive : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [alphaRankTwo]
  field_simp
  linear_combination (-4 : ℝ) * hsquare

/-- **The `(7,3)` member is already sub-threshold**: `35 t^3 - 45 t^2 + 15 t - 1`
has a root strictly inside `(0, 1/7)` (sign change `-1` to `16/49`), so the
family's guaranteed level `7 * t_min` sits strictly below the domination
threshold `1` at the frontier size as well. -/
theorem exists_xuCubicRoot_sevenThree_lt_inv_seven :
    ∃ rootValue : ℝ, 0 < rootValue ∧ rootValue < 1 / 7
      ∧ 35 * rootValue ^ 3 - 45 * rootValue ^ 2 + 15 * rootValue - 1 = 0 := by
  have hcontinuous : ContinuousOn
      (fun probeValue : ℝ => 35 * probeValue ^ 3 - 45 * probeValue ^ 2 + 15 * probeValue - 1)
      (Set.Icc 0 (1 / 7)) := by
    fun_prop
  have hmember : (0 : ℝ) ∈ Set.Ioo
      (35 * (0 : ℝ) ^ 3 - 45 * (0 : ℝ) ^ 2 + 15 * (0 : ℝ) - 1)
      (35 * (1 / 7 : ℝ) ^ 3 - 45 * (1 / 7 : ℝ) ^ 2 + 15 * (1 / 7 : ℝ) - 1) := by
    constructor <;> norm_num
  obtain ⟨rootValue, hrootInterval, hrootZero⟩ :=
    intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1 / 7) hcontinuous hmember
  exact ⟨rootValue, hrootInterval.1, hrootInterval.2, hrootZero⟩

/-! ## 5. The uniform-aggregate no-go at the capacity point `tau == 2/3`

Private copies of the two `(7,3)`-uniform conservation inputs (row law `4/3`,
supply chain `1/3 gamma`).  DUPLICATION FLAG for the integrator: the P2 sibling
module of this workflow lands the same two readings publicly; these stay
`private` here so the tree keeps a single public name for each law. -/

private theorem rowWeightSum_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (atomIndex : Fin 7) :
    ∑ otherIndex ∈ Finset.univ.erase atomIndex, edgeWeight D atomIndex otherIndex
      = 4 / 3 := by
  have hpositive : 0 < leverageOf (D.atom atomIndex) :=
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  rw [sum_erase_edgeWeight_eq_of_atomShare_eq D huniform hpositive]
  norm_num

private theorem sdiffPair_eq_erase_erase {firstIndex secondIndex : Fin 7} :
    Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7))
      = (Finset.univ.erase firstIndex).erase secondIndex := by
  ext member
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, not_or, Finset.mem_erase, and_true]
  tauto

private theorem sdiffWeightSum_left_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {firstIndex secondIndex : Fin 7} (hdistinct : firstIndex ≠ secondIndex) :
    ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
        edgeWeight D firstIndex otherIndex
      = 4 / 3 - edgeWeight D firstIndex secondIndex := by
  rw [sdiffPair_eq_erase_erase]
  have hmember : secondIndex ∈ Finset.univ.erase firstIndex :=
    Finset.mem_erase.mpr ⟨hdistinct.symm, Finset.mem_univ secondIndex⟩
  have hsplit := Finset.sum_erase_add (Finset.univ.erase firstIndex)
    (fun otherIndex => edgeWeight D firstIndex otherIndex) hmember
  have hrow := rowWeightSum_sevenThree D huniform firstIndex
  linarith [hsplit, hrow]

private theorem sdiffWeightSum_right_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {firstIndex secondIndex : Fin 7} (hdistinct : firstIndex ≠ secondIndex) :
    ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
        edgeWeight D secondIndex otherIndex
      = 4 / 3 - edgeWeight D firstIndex secondIndex := by
  rw [show ({firstIndex, secondIndex} : Finset (Fin 7)) = {secondIndex, firstIndex} from
    Finset.pair_comm firstIndex secondIndex]
  rw [sdiffWeightSum_left_sevenThree D huniform hdistinct.symm,
    edgeWeight_comm D secondIndex firstIndex]

private theorem chainSupplySum_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {firstIndex secondIndex : Fin 7} (hdistinct : firstIndex ≠ secondIndex) :
    ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
        directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex
      = 1 / 3 * directionGram D firstIndex secondIndex := by
  have hfirstPos : 0 < leverageOf (D.atom firstIndex) :=
    leverageOf_pos_of_atomShare_pos D (by rw [huniform firstIndex]; norm_num)
  have hsecondPos : 0 < leverageOf (D.atom secondIndex) :=
    leverageOf_pos_of_atomShare_pos D (by rw [huniform secondIndex]; norm_num)
  have hchain := sum_sdiff_atomShare_mul_directionGram_mul_directionGram D hdistinct
    hfirstPos hsecondPos
  have hpull : ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
        atomShare D otherIndex
          * (directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex)
      = 3 / 7 * ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
          directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun otherIndex _ => by rw [huniform otherIndex]
  rw [hpull, huniform firstIndex, huniform secondIndex] at hchain
  linarith [hchain]

/-- **THE `(7,3)` PAIR SUM AT THE CAPACITY POINT.**  Through every pair, the five
determinant clauses at the uniform capacity slack `tau == 2/3` total exactly
`-8/27 - (4/3) w_ab` — negative for EVERY frame and every pair, positive supply
notwithstanding.  The pair-sum gate is vacuous at `(7,3)` exactly as its
involution twin is at `(6,3)` (`Gtz.sum_involSlackDeterminant_through_pair`);
what survives is the starve-feed READING, `exists_involSlackDeterminant_capacity_neg_sevenThree`.
OVERLAP FLAG: the P2 sibling lands the general slack-vector identity; this is
the self-contained `tau == 2/3` instance under a distinct name. -/
theorem sum_sdiff_involSlackDeterminant_capacity_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {firstIndex secondIndex : Fin 7} (hdistinct : firstIndex ≠ secondIndex) :
    ∑ thirdIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
        involSlackDeterminant (correlationInvolution D) (fun _ => 2 / 3)
          firstIndex secondIndex thirdIndex
      = -(8 / 27) - 4 / 3 * edgeWeight D firstIndex secondIndex := by
  have hcard : (Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7))).card = 5 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_pair hdistinct]
  have hterm : ∀ thirdIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
      involSlackDeterminant (correlationInvolution D) (fun _ => 2 / 3)
          firstIndex secondIndex thirdIndex
        = (8 / 27 - 2 / 3 * edgeWeight D firstIndex secondIndex)
          + (-(2 / 3)) * edgeWeight D secondIndex thirdIndex
          + (-(2 / 3)) * edgeWeight D firstIndex thirdIndex
          + 2 * directionGram D firstIndex secondIndex
            * (directionGram D firstIndex thirdIndex
                * directionGram D thirdIndex secondIndex) := by
    intro thirdIndex hmember
    have hnotpair := (Finset.mem_sdiff.mp hmember).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnotpair
    rw [involSlackDeterminant, slackDeterminantThree,
      correlationInvolution_apply_of_ne D hdistinct,
      correlationInvolution_apply_of_ne D (Ne.symm hnotpair.1),
      correlationInvolution_apply_of_ne D (Ne.symm hnotpair.2)]
    simp only [edgeWeight]
    rw [directionGram_comm D thirdIndex secondIndex]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_const, hcard, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, sdiffWeightSum_right_sevenThree D huniform hdistinct,
    sdiffWeightSum_left_sevenThree D huniform hdistinct,
    chainSupplySum_sevenThree D huniform hdistinct, nsmul_eq_mul]
  simp only [edgeWeight]
  ring

/-- **THE ORDERED AGGREGATE IS THE FRAME-INDEPENDENT CONSTANT `-224/9`.**  Over
all ordered distinct triples of a `(7,3)`-uniform design, the determinant
clauses at the capacity slack `tau == 2/3` total `-224/9 = 6 * (-112/27)`;
`-112/27` is the unordered 35-clause total (each 3-subset appears six times).
Negative and CONSTANT across the entire stratum: no aggregate or averaging
selector can exist at `(7,3)`-uniform, closing the aggregation route exactly as
`Gtz.sum_involSlackDeterminant_six` closes it at `(6,3)`.  Consistency check
against the landed layer: at slack `tau == 1` the same expansion returns the
landed 35-triple total `343/27`
(`Gtz.sum_det_principalMinors_directionGramMatrix_sevenThree`). -/
theorem sum_ordered_involSlackDeterminant_capacity_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    ∑ firstIndex : Fin 7, ∑ secondIndex ∈ Finset.univ.erase firstIndex,
        ∑ thirdIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
          involSlackDeterminant (correlationInvolution D) (fun _ => 2 / 3)
            firstIndex secondIndex thirdIndex
      = -(224 / 9) := by
  have houter : ∀ firstIndex : Fin 7,
      ∑ secondIndex ∈ Finset.univ.erase firstIndex,
          ∑ thirdIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
            involSlackDeterminant (correlationInvolution D) (fun _ => 2 / 3)
              firstIndex secondIndex thirdIndex
        = -(32 / 9) := by
    intro firstIndex
    have hmid : ∀ secondIndex ∈ Finset.univ.erase firstIndex,
        ∑ thirdIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
            involSlackDeterminant (correlationInvolution D) (fun _ => 2 / 3)
              firstIndex secondIndex thirdIndex
          = -(8 / 27) - 4 / 3 * edgeWeight D firstIndex secondIndex := by
      intro secondIndex hmember
      exact sum_sdiff_involSlackDeterminant_capacity_sevenThree D huniform
        (Finset.mem_erase.mp hmember).1.symm
    have hcard : (Finset.univ.erase firstIndex).card = 6 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ firstIndex), Finset.card_univ,
        Fintype.card_fin]
    rw [Finset.sum_congr rfl hmid, Finset.sum_sub_distrib, Finset.sum_const, hcard,
      ← Finset.mul_sum, rowWeightSum_sevenThree D huniform firstIndex, nsmul_eq_mul]
    norm_num
  rw [Finset.sum_congr rfl fun firstIndex _ => houter firstIndex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **THE STARVE-FEED READING, `(7,3)` FORM.**  Because the pair sum is strictly
negative, EVERY pair of a `(7,3)`-uniform design owns a completion whose
determinant clause FAILS at the capacity point: the aggregate cannot select, but
it does localize failure.  This is the only surviving content of the
aggregation route, and it is frame-independent. -/
theorem exists_involSlackDeterminant_capacity_neg_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {firstIndex secondIndex : Fin 7} (hdistinct : firstIndex ≠ secondIndex) :
    ∃ thirdIndex : Fin 7, thirdIndex ≠ firstIndex ∧ thirdIndex ≠ secondIndex
      ∧ involSlackDeterminant (correlationInvolution D) (fun _ => 2 / 3)
          firstIndex secondIndex thirdIndex < 0 := by
  by_contra hnone
  push Not at hnone
  have hnonneg : 0 ≤ ∑ thirdIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
      involSlackDeterminant (correlationInvolution D) (fun _ => 2 / 3)
        firstIndex secondIndex thirdIndex := by
    refine Finset.sum_nonneg fun thirdIndex hmember => ?_
    have hnotpair := (Finset.mem_sdiff.mp hmember).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnotpair
    exact hnone thirdIndex hnotpair.1 hnotpair.2
  rw [sum_sdiff_involSlackDeterminant_capacity_sevenThree D huniform hdistinct] at hnonneg
  have hweightNonneg := edgeWeight_nonneg D firstIndex secondIndex
  linarith

/-! ## 6. The deletion-corner fence: two dead atoms hand `(7,3)` to the landed
five-atom theorem -/

private theorem atomMatrix_zeroVector : atomMatrix (0 : Fin 3 → ℝ) = 0 := by
  ext rowIndex colIndex
  simp only [atomMatrix, Matrix.vecMulVec_apply, Pi.zero_apply, Matrix.zero_apply, mul_zero]

/-- **THE TWO-ATOM DELETION CORNER IS CLOSED.**  A `(7,3)` design two of whose
atoms are the ZERO vector has a dominating triple, unconditionally: the five
live atoms are already isotropic (the dead atoms contribute nothing to
Parseval), rescaling them by the square root of the live mass produces an
honest five-atom design, `Gtz.gtzWeighted_of_le_five` dominates it, and the
domination transports back with room to spare (the rescaling only SHRINKS the
atoms, so undoing it enlarges the subset sum).

HONESTY NOTE on the transport from the pen: `Gtz.WeightedDesign.weight_pos`
forbids literal zero weights, so the free-weight simplex corner "two weights
vanish" enters the structure as "two atoms vanish" — an atom of share zero.
This is the `(7,3)` face of the R4 boundary the Mercedes-cone lesson points at,
and its first fence. -/
theorem exists_dominating_triple_of_two_zero_atoms_sevenThree (D : WeightedDesign 7 3)
    {zeroFirst zeroSecond : Fin 7} (hdistinct : zeroFirst ≠ zeroSecond)
    (hfirstZero : D.atom zeroFirst = 0) (hsecondZero : D.atom zeroSecond = 0) :
    ∃ dominatingSet : Finset (Fin 7), dominatingSet.card = 3 ∧ Dominates D dominatingSet := by
  classical
  set liveSet : Finset (Fin 7) :=
    Finset.univ \ ({zeroFirst, zeroSecond} : Finset (Fin 7)) with hliveSet
  have hliveCard : liveSet.card = 5 := by
    rw [hliveSet, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin, Finset.card_pair hdistinct]
  set pickMap : Fin 5 → Fin 7 := fun slot => ((liveSet.orderIsoOfFin hliveCard) slot : Fin 7)
    with hpickMap
  have hpickInj : Function.Injective pickMap := fun leftSlot rightSlot hvalue =>
    (liveSet.orderIsoOfFin hliveCard).injective (Subtype.ext hvalue)
  have hpickMem : ∀ slot : Fin 5, pickMap slot ∈ liveSet := fun slot =>
    ((liveSet.orderIsoOfFin hliveCard) slot).2
  have himage : Finset.image pickMap Finset.univ = liveSet := by
    apply Finset.eq_of_subset_of_card_le
    · intro member hmember
      obtain ⟨slot, -, rfl⟩ := Finset.mem_image.mp hmember
      exact hpickMem slot
    · rw [hliveCard, Finset.card_image_of_injective _ hpickInj, Finset.card_univ,
        Fintype.card_fin]
  have hsumPick : ∀ {valueType : Type} [AddCommMonoid valueType] (valueMap : Fin 7 → valueType),
      ∑ slot : Fin 5, valueMap (pickMap slot) = ∑ member ∈ liveSet, valueMap member := by
    intro valueType _ valueMap
    rw [← himage, Finset.sum_image fun leftSlot _ rightSlot _ hvalue => hpickInj hvalue]
  set liveMass : ℝ := ∑ member ∈ liveSet, D.weight member with hliveMass
  have hliveMassPos : 0 < liveMass := by
    rw [hliveMass]
    exact Finset.sum_pos (fun member _ => D.weight_pos member) ⟨pickMap 0, hpickMem 0⟩
  have hmassSplit := Finset.sum_sdiff (f := D.weight)
    (Finset.subset_univ ({zeroFirst, zeroSecond} : Finset (Fin 7)))
  rw [D.weight_sum_one, Finset.sum_pair hdistinct] at hmassSplit
  have hliveMassLt : liveMass < 1 := by
    have hfirstPos := D.weight_pos zeroFirst
    have hsecondPos := D.weight_pos zeroSecond
    rw [hliveMass, hliveSet]
    linarith [hmassSplit]
  have hsqrtSq : Real.sqrt liveMass ^ 2 = liveMass := Real.sq_sqrt hliveMassPos.le
  set restrictedDesign : WeightedDesign 5 3 :=
    { atom := fun slot => Real.sqrt liveMass • D.atom (pickMap slot)
      weight := fun slot => D.weight (pickMap slot) / liveMass
      weight_pos := fun slot => div_pos (D.weight_pos (pickMap slot)) hliveMassPos
      weight_sum_one := by
        rw [← Finset.sum_div, hsumPick D.weight, ← hliveMass, div_self hliveMassPos.ne']
      isParseval := by
        have hslot : ∀ slot : Fin 5,
            (D.weight (pickMap slot) / liveMass)
                • atomMatrix (Real.sqrt liveMass • D.atom (pickMap slot))
              = D.weight (pickMap slot) • atomMatrix (D.atom (pickMap slot)) := by
          intro slot
          rw [atomMatrix_smul, hsqrtSq, smul_smul, div_mul_cancel₀ _ hliveMassPos.ne']
        rw [Finset.sum_congr rfl fun slot _ => hslot slot,
          hsumPick fun member => D.weight member • atomMatrix (D.atom member)]
        have hfullSplit := Finset.sum_sdiff
          (f := fun member => D.weight member • atomMatrix (D.atom member))
          (Finset.subset_univ ({zeroFirst, zeroSecond} : Finset (Fin 7)))
        rw [D.isParseval, Finset.sum_pair hdistinct, hfirstZero, hsecondZero,
          atomMatrix_zeroVector, smul_zero, smul_zero, zero_add, add_zero] at hfullSplit
        rw [← hliveSet] at hfullSplit
        rw [hfullSplit] }
    with hrestrictedDesign
  obtain ⟨selectedSlots, hselectedCard, hselectedDominates⟩ :=
    gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num) restrictedDesign
  refine ⟨selectedSlots.map ⟨pickMap, hpickInj⟩, ?_, ?_⟩
  · rw [Finset.card_map, hselectedCard]
  · have hmappedSum : subsetSum D (selectedSlots.map ⟨pickMap, hpickInj⟩)
        = ∑ slot ∈ selectedSlots, atomMatrix (D.atom (pickMap slot)) := by
      rw [subsetSum, Finset.sum_map]
      rfl
    have hrestrictedSum : subsetSum restrictedDesign selectedSlots
        = liveMass • ∑ slot ∈ selectedSlots, atomMatrix (D.atom (pickMap slot)) := by
      rw [subsetSum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun slot _ => ?_
      show atomMatrix (Real.sqrt liveMass • D.atom (pickMap slot)) = _
      rw [atomMatrix_smul, hsqrtSq]
    have hmappedPsd : (∑ slot ∈ selectedSlots, atomMatrix (D.atom (pickMap slot))).PosSemidef :=
      Matrix.posSemidef_sum selectedSlots fun slot _ => posSemidef_atomMatrix _
    have hscaledPsd : ((1 - liveMass)
          • ∑ slot ∈ selectedSlots, atomMatrix (D.atom (pickMap slot))).PosSemidef :=
      hmappedPsd.smul (by linarith : (0 : ℝ) ≤ 1 - liveMass)
    have hdominatesRaw := hselectedDominates
    rw [Dominates, hrestrictedSum] at hdominatesRaw
    rw [Dominates, hmappedSum]
    have hshape : ∑ slot ∈ selectedSlots, atomMatrix (D.atom (pickMap slot))
          - (1 : Matrix (Fin 3) (Fin 3) ℝ)
        = (liveMass • ∑ slot ∈ selectedSlots, atomMatrix (D.atom (pickMap slot))
            - (1 : Matrix (Fin 3) (Fin 3) ℝ))
          + (1 - liveMass) • ∑ slot ∈ selectedSlots, atomMatrix (D.atom (pickMap slot)) := by
      rw [sub_smul, one_smul]
      abel
    rw [hshape]
    exact hdominatesRaw.add hscaledPsd

end Gtz
