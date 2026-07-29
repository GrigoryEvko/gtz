/-
# Frame conservation: the three laws in share/direction coordinates, and the
# heaviness profile

Every weighted design carries three exact conservation laws and one inequality
that together pin its leverage profile.  Write `s_c = t_c * l_c` for the SHARE
of an atom (`Gtz.atomShare`, the classical leverage score and the diagonal of
`Gtz.projectionOfDesign`), `u_c = g_c / |g_c|` for its DIRECTION
(`Gtz.unitAtom`), `gamma_cd = <u_c, u_d>` for the direction Gram
(`Gtz.directionGram`), and `x_c = l_c - 1` for the EXCESS.

## The three laws

* **FRAME.**  `sum_c s_c u_c u_c^T = I_k` — `sum_atomShare_smul_atomMatrix_unitAtom`.
  This is Parseval rewritten: `s_c u_c u_c^T = t_c g_c g_c^T` atom by atom.  It
  holds with NO hypothesis at all — a zero atom contributes zero to both sides,
  because `Gtz.unitAtom` divides by `sqrt 0 = 0` and Lean's `0⁻¹ = 0` sends the
  whole term to zero exactly when the raw term is zero.  Its trace reading
  `sum_c s_c = k` is already landed (`Gtz.sum_atomShare_eq_rank`) and is not
  re-proved here.

* **BUDGET.**  `sum_c s_c (1 - 1/l_c) = k - 1`
  (`sum_atomShare_mul_one_sub_inv_leverage`, needing only that no atom is zero),
  equivalently `sum_c s_c A_c^(-2) = k - 1` on an all-heavy design
  (`sum_atomShare_mul_inv_leverageAmplification_sq`), where
  `A_c = sqrt(1 + 1/x_c) > 1` is the AMPLIFICATION (`Gtz.leverageAmplification`).
  Both are transported from the landed unconditional form
  `sum_c t_c (l_c - 1) = k - 1` (`Gtz.sum_weight_mul_leverage_sub_one`); the
  reciprocals cancel identically, so no new Parseval input is consumed.  At
  `k = 3` this is the exact harmonic budget `sum_c s_c A_c^(-2) = 2`.

* **IDEMPOTENCY.**  `Gamma S Gamma = Gamma` with `S = diag(s)`
  (`directionGramMatrix_mul_diagonal_atomShare_mul_self` as a matrix identity,
  `sum_atomShare_mul_directionGram_mul_directionGram` entrywise).  Its two
  readings are the campaign's row law and supply-chain law:

  - **ROW LAW**  `s_a + sum_{d /= a} s_d gamma_ad^2 = 1`
    (`atomShare_add_sum_erase_atomShare_mul_sq_directionGram`).
  - **SUPPLY-CHAIN LAW**  `(1 - s_a - s_b) gamma_ab = sum_{d /= a,b} s_d gamma_ad gamma_db`
    (`sum_sdiff_atomShare_mul_directionGram_mul_directionGram`).

  Consequence, load-bearing downstream: **a strong edge is never private**
  (`atomShare_pair_eq_one_or_directionGram_eq_zero`, with the usable
  contrapositive `exists_directionGram_chain_ne_zero`).  If every third atom `d`
  has `gamma_ad gamma_db = 0`, then either `s_a + s_b = 1` or `gamma_ab = 0`.

  The equality case of the row law is the saturation lemma
  `atomShare_eq_one_iff_forall_atomPairing_eq_zero`: an atom of share exactly one
  — the boundary of the landed ceiling `Gtz.weighted_leverage_le_one` — is
  orthogonal to every other atom of the design, and conversely.

## The heaviness profile

`rank_sub_one_sub_threshold_le_sum_atomShare`: for every `tau >= -1` and every
subset containing all the atoms of excess at least `tau`, that subset carries
share at least `(k-1) - tau`.  The proof is division-free and per-atom:

    (1+tau) t_c x_c <= (1+tau) s_c      always      (since x_c <= l_c)
    (1+tau) t_c x_c <= tau      s_c      when x_c < tau

summed against `sum_c t_c x_c = k-1` and `sum_c s_c = k`.  The hypothesis
`-1 <= tau` is sharp: at `tau < -1` the unit design refutes the statement.

Four corollaries follow with no extra input.  `exists_excess_ge_of_lt_rank_sub_one`
— for every `tau < k-1` SOME atom has excess at least `tau` (take the subset
empty); `heavySet_nonempty_of_lt_rank_sub_one`; `sum_atomShare_le_one_of_light` —
the atoms of leverage below one carry share at most `1` (take `tau = 0` on the
complement); and `rank_sub_one_sub_threshold_le_card_heavySet`, the CARDINALITY
reading, since each share is at most one.  The limiting statement `l_max >= k` is
NOT proved from the profile (the profile's bound on `{x >= tau}` degenerates to
`0` as `tau -> k-1`); it is the landed `Gtz.exists_leverage_ge_rank`, sharpened
here to cap form as `rank_le_of_forall_leverage_le` and specialized at rank three
as `exists_leverage_three_le`.

The threshold hypothesis is not decoration: `HeavinessProfileAt` names the
statement at a fixed threshold, `heavinessProfileAt_of_neg_one_le` proves it from
`-1` upward, and `not_heavinessProfileAt_of_lt_neg_one` REFUTES it below `-1` at
`Gtz.unitDesign`.  The bound IS attained, at `tau = -1` with the full index set,
where it reads `k <= sum_c s_c = k`; for `tau > -1` and a nonempty heavy set it is
strict, because the heavy per-atom step `t_c x_c < t_c l_c` is then strict.  The
strict form is not separately mechanized.

## The pinning

`forall_leverage_eq_rank_of_forall_rank_le` and its dual: the weighted mean of
the leverages is exactly `k`, so a ONE-SIDED bound at `k` forces EVERY leverage
to equal `k`.  At rank three (`forall_leverage_eq_three_of_forall_two_le_excess`)
this is the campaign's observation that once every excess reaches `2` the
budget permits only the uniform stratum `l == 3` — which is why the tetrahedron,
`K_4`, the icosahedron and `splitSeven` all sit at leverage exactly three.  The
statement needs neither all-heaviness nor rank three; it is the equality case of
a weighted average and holds at every rank in both directions.

## Beyond the three laws

* `sum_coefficient_mul_atomOverlap_mul_atomOverlap` — the POLARIZED resolution
  identity for an arbitrary family resolving the identity.  It is strictly
  stronger than both the row law and the supply-chain law (which are its
  diagonal and off-diagonal readings at atom probes) and it is proved once and
  instantiated twice, at the raw atoms and at the unit directions.
* `posSemidef_directionGramMatrix` — the direction Gram is a correlation matrix
  at EVERY rank: positive semidefinite, unit diagonal off the degenerate atoms
  (`directionGram_self`), entries in `[-1,1]` (`abs_directionGram_le_one`).  This
  is the rank-generic elliptope statement whose rank-three shadow is
  `Gtz.IsElliptopeGoodTriangle`; the bridge to `Gtz.normalizedPairing` is left to
  the rank-three layer, which sits above this file in the import order.
* `rank_le_of_forall_leverage_le` / `le_rank_of_forall_le_leverage` — every
  uniform leverage cap is at least the rank and every uniform floor is at most
  the rank.  Stronger than the landed existence statements: they hold for any
  real bound, attained or not, with no `1 <= k`.
* `directionDesign` — the companion design on the same directions weighted by
  `s_c/k`, whose every leverage is exactly `k`.  It records that the frame law
  is itself a Parseval identity, and by the pinning theorem `k` is the only
  constant a companion could have.  It is NOT a reduction of the selection
  problem: the atoms are rescaled, so `Dominates` is a different statement about
  the companion.

## Scope

Everything here is stated at general rank `k` and general size `m`.  The
rank-three-only vocabulary of `Gtz/Quantitative/GoodTripleGraph.lean`
(`heavyExcess`, `atomPairing`, `normalizedPairing`, ...) is deliberately not
used: the three laws and the profile are rank-generic, and the `(7,3)` workflow
wants them in that form.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.LinAlg.ProjectionForm
import Gtz.Design.LeverageBound
import Gtz.Quantitative.ChartHadamard
import Gtz.Reduction.BranchTransferConstants
import Gtz.Reduction.Reductions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## Leverage hygiene: the degenerate atom -/

/-- The leverage is a sum of squares, hence nonnegative.  Kept `private`: the same
fact is already public as `Gtz.leverageOf_nonneg` in
`Gtz/Quantitative/FlooredSpreadRegion.lean`, which sits far above this file in the
import order, and a second global of that name would silently shadow it. -/
private theorem leverageOf_nonneg (vector : Fin k → ℝ) : 0 ≤ leverageOf vector :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Rescaling a vector scales its leverage quadratically. -/
theorem leverageOf_smul (scale : ℝ) (vector : Fin k → ℝ) :
    leverageOf (scale • vector) = scale ^ 2 * leverageOf vector := by
  rw [← trace_atomMatrix, atomMatrix_smul, Matrix.trace_smul, trace_atomMatrix, smul_eq_mul]

/-- Only the zero vector has vanishing leverage. -/
theorem eq_zero_of_leverageOf_eq_zero {vector : Fin k → ℝ} (hvanishes : leverageOf vector = 0) :
    vector = 0 :=
  eq_zero_of_dotProduct_self_eq_zero (by rw [← leverageOf_eq_dotProduct]; exact hvanishes)

/-- An atom of vanishing leverage contributes the zero matrix. -/
theorem atomMatrix_eq_zero_of_leverageOf_eq_zero {vector : Fin k → ℝ}
    (hvanishes : leverageOf vector = 0) : atomMatrix vector = 0 := by
  rw [eq_zero_of_leverageOf_eq_zero hvanishes]
  ext rowIndex colIndex
  simp only [atomMatrix, Matrix.vecMulVec_apply, Pi.zero_apply, Matrix.zero_apply, mul_zero]

/-! ## The polarized resolution identity

One lemma, proved once, instantiated twice: at the raw atoms it is Parseval read
as a bilinear form, at the unit directions it is the frame law read the same way.
Both the row law and the supply-chain law are readings of the second instance. -/

/-- **THE POLARIZED RESOLUTION IDENTITY.**  If a family of vectors resolves the
identity against a family of coefficients, then for every pair of probes

    sum_i coefficient_i <probeLeft, v_i> <v_i, probeRight> = <probeLeft, probeRight>.

Testing the resolution as a bilinear form, not merely as a quadratic form; the
quadratic form is the diagonal case `probeLeft = probeRight`. -/
theorem sum_coefficient_mul_atomOverlap_mul_atomOverlap {size dimension : ℕ}
    (coefficient : Fin size → ℝ) (vectorFamily : Fin size → (Fin dimension → ℝ))
    (hresolves : ∑ index, coefficient index • atomMatrix (vectorFamily index) = 1)
    (probeLeft probeRight : Fin dimension → ℝ) :
    ∑ index, coefficient index
        * ((probeLeft ⬝ᵥ vectorFamily index) * (vectorFamily index ⬝ᵥ probeRight))
      = probeLeft ⬝ᵥ probeRight := by
  have hcontract : probeLeft
        ⬝ᵥ ((∑ index, coefficient index • atomMatrix (vectorFamily index)) *ᵥ probeRight)
      = ∑ index, coefficient index
          * ((probeLeft ⬝ᵥ vectorFamily index) * (vectorFamily index ⬝ᵥ probeRight)) := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun index _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix, vecMulVec_mulVec_eq,
      dotProduct_smul, smul_eq_mul]
    ring
  rw [hresolves, Matrix.one_mulVec] at hcontract
  exact hcontract.symm

/-- **Parseval as a bilinear form**: `sum_c t_c <v, g_c> <g_c, w> = <v, w>`.  The
weight-side companion of `Gtz.parseval_weighted_sum_sq`, which is its diagonal. -/
theorem parseval_weighted_bilinear (D : WeightedDesign m k) (probeLeft probeRight : Fin k → ℝ) :
    ∑ atomIndex, D.weight atomIndex
        * ((probeLeft ⬝ᵥ D.atom atomIndex) * (D.atom atomIndex ⬝ᵥ probeRight))
      = probeLeft ⬝ᵥ probeRight :=
  sum_coefficient_mul_atomOverlap_mul_atomOverlap D.weight D.atom D.isParseval
    probeLeft probeRight

/-- **The transfer identity in raw coordinates**: `sum_e t_e b_ae b_ed = b_ad`.  This
is `G D_t G = G` (`Gtz.designTransfer_mul_gram`) read entry by entry, obtained here
directly from the bilinear form so that no matrix product has to be unfolded. -/
theorem sum_weight_mul_atomPairing_mul_atomPairing (D : WeightedDesign m k)
    (firstIndex secondIndex : Fin m) :
    ∑ otherIndex, D.weight otherIndex
        * ((D.atom firstIndex ⬝ᵥ D.atom otherIndex) * (D.atom otherIndex ⬝ᵥ D.atom secondIndex))
      = D.atom firstIndex ⬝ᵥ D.atom secondIndex :=
  parseval_weighted_bilinear D (D.atom firstIndex) (D.atom secondIndex)

/-! ## Directions -/

/-- **The direction of an atom**, `u_c = g_c / |g_c|`.  A zero atom is sent to the
zero vector (`sqrt 0 = 0` and `0⁻¹ = 0`), which is exactly the value that makes the
frame law below unconditional. -/
noncomputable def unitAtom (D : WeightedDesign m k) (atomIndex : Fin m) : Fin k → ℝ :=
  (Real.sqrt (leverageOf (D.atom atomIndex)))⁻¹ • D.atom atomIndex

/-- The direction's rank-one atom is the raw one divided by the leverage. -/
theorem atomMatrix_unitAtom (D : WeightedDesign m k) (atomIndex : Fin m) :
    atomMatrix (unitAtom D atomIndex)
      = (leverageOf (D.atom atomIndex))⁻¹ • atomMatrix (D.atom atomIndex) := by
  rw [unitAtom, atomMatrix_smul, inv_pow, Real.sq_sqrt (leverageOf_nonneg _)]

/-- A nonzero atom has a genuine unit direction. -/
theorem leverageOf_unitAtom (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) : leverageOf (unitAtom D atomIndex) = 1 := by
  rw [← trace_atomMatrix, atomMatrix_unitAtom, Matrix.trace_smul, trace_atomMatrix, smul_eq_mul,
    inv_mul_cancel₀ hpositive.ne']

/-- Every direction has leverage at most one — including the degenerate one, whose
leverage is zero. -/
theorem leverageOf_unitAtom_le_one (D : WeightedDesign m k) (atomIndex : Fin m) :
    leverageOf (unitAtom D atomIndex) ≤ 1 := by
  rcases eq_or_lt_of_le (leverageOf_nonneg (D.atom atomIndex)) with hvanishes | hpositive
  · rw [unitAtom, eq_zero_of_leverageOf_eq_zero hvanishes.symm, smul_zero]
    simp only [leverageOf, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero]
    exact zero_le_one
  · rw [leverageOf_unitAtom D hpositive]

/-- **The direction Gram** `gamma_cd = <u_c, u_d>`. -/
noncomputable def directionGram (D : WeightedDesign m k) (firstIndex secondIndex : Fin m) : ℝ :=
  unitAtom D firstIndex ⬝ᵥ unitAtom D secondIndex

/-- The direction Gram is symmetric. -/
theorem directionGram_comm (D : WeightedDesign m k) (firstIndex secondIndex : Fin m) :
    directionGram D firstIndex secondIndex = directionGram D secondIndex firstIndex :=
  dotProduct_comm _ _

/-- The direction Gram is the raw pairing rescaled by the two square-rooted
leverages. -/
theorem directionGram_eq_scaled_atomPairing (D : WeightedDesign m k)
    (firstIndex secondIndex : Fin m) :
    directionGram D firstIndex secondIndex
      = (Real.sqrt (leverageOf (D.atom firstIndex)))⁻¹
          * (Real.sqrt (leverageOf (D.atom secondIndex)))⁻¹
          * (D.atom firstIndex ⬝ᵥ D.atom secondIndex) := by
  simp only [directionGram, unitAtom, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- A nonzero atom has unit self-correlation. -/
theorem directionGram_self (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) : directionGram D atomIndex atomIndex = 1 := by
  rw [directionGram, ← leverageOf_eq_dotProduct, leverageOf_unitAtom D hpositive]

/-- **The direction Gram is a correlation matrix**: every entry lies in `[-1, 1]`,
with no hypothesis — a degenerate atom simply contributes a zero row. -/
theorem abs_directionGram_le_one (D : WeightedDesign m k) (firstIndex secondIndex : Fin m) :
    |directionGram D firstIndex secondIndex| ≤ 1 := by
  have hcauchy := dotProduct_sq_le_mul (unitAtom D firstIndex) (unitAtom D secondIndex)
  rw [← leverageOf_eq_dotProduct, ← leverageOf_eq_dotProduct, ← directionGram] at hcauchy
  have hfirst := leverageOf_unitAtom_le_one D firstIndex
  have hsecond := leverageOf_unitAtom_le_one D secondIndex
  have hfirstNonneg := leverageOf_nonneg (unitAtom D firstIndex)
  have hsecondNonneg := leverageOf_nonneg (unitAtom D secondIndex)
  have habs := sq_abs (directionGram D firstIndex secondIndex)
  have hnonneg := abs_nonneg (directionGram D firstIndex secondIndex)
  nlinarith [hcauchy, hfirst, hsecond, hfirstNonneg, hsecondNonneg, habs, hnonneg]

/-! ## (a) THE FRAME LAW -/

/-- The share-weighted direction atom IS the weight-weighted raw atom, atom by
atom: `s_c u_c u_c^T = t_c g_c g_c^T`.  Both sides vanish on a degenerate atom. -/
theorem atomShare_smul_atomMatrix_unitAtom (D : WeightedDesign m k) (atomIndex : Fin m) :
    atomShare D atomIndex • atomMatrix (unitAtom D atomIndex)
      = D.weight atomIndex • atomMatrix (D.atom atomIndex) := by
  rw [atomMatrix_unitAtom, atomShare, smul_smul]
  rcases eq_or_lt_of_le (leverageOf_nonneg (D.atom atomIndex)) with hvanishes | hpositive
  · rw [atomMatrix_eq_zero_of_leverageOf_eq_zero hvanishes.symm, smul_zero, smul_zero]
  · rw [mul_assoc, mul_inv_cancel₀ hpositive.ne', mul_one]

/-- **(a) THE FRAME LAW**: `sum_c s_c u_c u_c^T = I_k`.  Parseval rewritten in
share/direction coordinates, with NO hypothesis — the leverage that the share
carries is exactly the leverage the normalization removes.  Its trace reading
`sum_c s_c = k` is the landed `Gtz.sum_atomShare_eq_rank`. -/
theorem sum_atomShare_smul_atomMatrix_unitAtom (D : WeightedDesign m k) :
    ∑ atomIndex, atomShare D atomIndex • atomMatrix (unitAtom D atomIndex) = 1 := by
  rw [Finset.sum_congr rfl fun atomIndex _ => atomShare_smul_atomMatrix_unitAtom D atomIndex]
  exact D.isParseval

/-- **The frame law as a bilinear form**: `sum_c s_c <v, u_c> <u_c, w> = <v, w>`.
The second instance of the polarized resolution identity, and the engine of the
whole idempotency section. -/
theorem frameLaw_bilinear (D : WeightedDesign m k) (probeLeft probeRight : Fin k → ℝ) :
    ∑ atomIndex, atomShare D atomIndex
        * ((probeLeft ⬝ᵥ unitAtom D atomIndex) * (unitAtom D atomIndex ⬝ᵥ probeRight))
      = probeLeft ⬝ᵥ probeRight :=
  sum_coefficient_mul_atomOverlap_mul_atomOverlap (atomShare D) (unitAtom D)
    (sum_atomShare_smul_atomMatrix_unitAtom D) probeLeft probeRight

/-! ## (b) THE BUDGET LAW -/

/-- **(b) THE BUDGET LAW in share coordinates**: `sum_c s_c (1 - 1/l_c) = k - 1`.
Transported from the landed unconditional `Gtz.sum_weight_mul_leverage_sub_one`;
the only hypothesis is that no atom is degenerate, which is what makes `1/l_c`
mean anything. -/
theorem sum_atomShare_mul_one_sub_inv_leverage (D : WeightedDesign m k)
    (hpositive : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex)) :
    ∑ atomIndex, atomShare D atomIndex * (1 - (leverageOf (D.atom atomIndex))⁻¹)
      = (k : ℝ) - 1 := by
  rw [← sum_weight_mul_leverage_sub_one D]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  have hne : leverageOf (D.atom atomIndex) ≠ 0 := (hpositive atomIndex).ne'
  rw [atomShare]
  field_simp

/-- **The amplification** `A_c = sqrt(1 + 1/x_c)` of an atom of excess `x_c`.  On an
all-heavy design it exceeds one, and `A_c^(-2) = 1 - 1/l_c` is the atom's share of
the budget. -/
noncomputable def leverageAmplification (D : WeightedDesign m k) (atomIndex : Fin m) : ℝ :=
  Real.sqrt (1 + (leverageOf (D.atom atomIndex) - 1)⁻¹)

/-- The amplification squared is `l_c / x_c`. -/
theorem leverageAmplification_sq (D : WeightedDesign m k) {atomIndex : Fin m}
    (hheavy : 1 < leverageOf (D.atom atomIndex)) :
    leverageAmplification D atomIndex ^ 2
      = leverageOf (D.atom atomIndex) / (leverageOf (D.atom atomIndex) - 1) := by
  have hexcess : 0 < leverageOf (D.atom atomIndex) - 1 := by linarith
  have hexcessNe : leverageOf (D.atom atomIndex) - 1 ≠ 0 := hexcess.ne'
  have hinner : (0 : ℝ) ≤ 1 + (leverageOf (D.atom atomIndex) - 1)⁻¹ := by
    have := inv_pos.mpr hexcess
    linarith
  rw [leverageAmplification, Real.sq_sqrt hinner]
  field_simp
  ring

/-- **A heavy atom amplifies**: `A_c > 1` exactly when the excess is positive. -/
theorem one_lt_leverageAmplification (D : WeightedDesign m k) {atomIndex : Fin m}
    (hheavy : 1 < leverageOf (D.atom atomIndex)) : 1 < leverageAmplification D atomIndex := by
  have hexcess : 0 < leverageOf (D.atom atomIndex) - 1 := by linarith
  have hinvPositive : 0 < (leverageOf (D.atom atomIndex) - 1)⁻¹ := inv_pos.mpr hexcess
  have hinner : (1 : ℝ) < 1 + (leverageOf (D.atom atomIndex) - 1)⁻¹ := by linarith
  rw [leverageAmplification, show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  rw [Real.sqrt_one]
  calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
    _ < Real.sqrt (1 + (leverageOf (D.atom atomIndex) - 1)⁻¹) :=
        Real.sqrt_lt_sqrt (by norm_num) hinner

/-- The reciprocal square of the amplification is the atom's budget share. -/
theorem inv_leverageAmplification_sq (D : WeightedDesign m k) {atomIndex : Fin m}
    (hheavy : 1 < leverageOf (D.atom atomIndex)) :
    (leverageAmplification D atomIndex)⁻¹ ^ 2 = 1 - (leverageOf (D.atom atomIndex))⁻¹ := by
  have hexcess : leverageOf (D.atom atomIndex) - 1 ≠ 0 := by
    intro hcontra; linarith [hcontra]
  have hlev : leverageOf (D.atom atomIndex) ≠ 0 := by
    intro hcontra; rw [hcontra] at hheavy; linarith
  rw [inv_pow, leverageAmplification_sq D hheavy]
  field_simp

/-- **(b) THE BUDGET LAW in amplification coordinates**: on an all-heavy design
`sum_c s_c A_c^(-2) = k - 1`.  At rank three this is the exact harmonic budget
`sum_c s_c A_c^(-2) = 2`. -/
theorem sum_atomShare_mul_inv_leverageAmplification_sq (D : WeightedDesign m k)
    (hheavy : AllHeavy D) :
    ∑ atomIndex, atomShare D atomIndex * (leverageAmplification D atomIndex)⁻¹ ^ 2
      = (k : ℝ) - 1 := by
  rw [← sum_atomShare_mul_one_sub_inv_leverage D fun atomIndex =>
    lt_trans one_pos (hheavy atomIndex)]
  exact Finset.sum_congr rfl fun atomIndex _ => by
    rw [inv_leverageAmplification_sq D (hheavy atomIndex)]

/-- **The harmonic budget at rank three**: `sum_c s_c A_c^(-2) = 2`.  The rank the
`(7,3)` frontier reads, discharged from the rank-generic law. -/
theorem sum_atomShare_mul_inv_leverageAmplification_sq_three (D : WeightedDesign m 3)
    (hheavy : AllHeavy D) :
    ∑ atomIndex, atomShare D atomIndex * (leverageAmplification D atomIndex)⁻¹ ^ 2 = 2 := by
  rw [sum_atomShare_mul_inv_leverageAmplification_sq D hheavy]
  norm_num

/-! ## (c) THE IDEMPOTENCY LAW -/

/-- **(c) IDEMPOTENCY, entrywise**: `sum_d s_d gamma_ad gamma_db = gamma_ab`, the
`(a,b)` entry of `Gamma S Gamma = Gamma`.  Unconditional: it is the frame law
tested at the two directions. -/
theorem sum_atomShare_mul_directionGram_mul_directionGram (D : WeightedDesign m k)
    (firstIndex secondIndex : Fin m) :
    ∑ otherIndex, atomShare D otherIndex
        * (directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex)
      = directionGram D firstIndex secondIndex :=
  frameLaw_bilinear D (unitAtom D firstIndex) (unitAtom D secondIndex)

/-- The direction Gram, packaged as a matrix on the index space. -/
noncomputable def directionGramMatrix (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun firstIndex secondIndex => directionGram D firstIndex secondIndex

/-- The unit directions as the rows of an `m x k` matrix. -/
noncomputable def unitAtomRows (D : WeightedDesign m k) : Matrix (Fin m) (Fin k) ℝ :=
  Matrix.of fun atomIndex coord => unitAtom D atomIndex coord

/-- The direction Gram matrix is the row matrix against its own transpose. -/
theorem directionGramMatrix_eq_mul_transpose (D : WeightedDesign m k) :
    directionGramMatrix D = unitAtomRows D * (unitAtomRows D)ᵀ := by
  ext firstIndex secondIndex
  simp only [directionGramMatrix, unitAtomRows, Matrix.of_apply, directionGram, Matrix.mul_apply,
    Matrix.transpose_apply, dotProduct]

/-- **The direction Gram is a correlation matrix.**  It is positive semidefinite at
every rank, being a Gram matrix; together with `directionGram_self` (unit diagonal
off the degenerate atoms) and `abs_directionGram_le_one` this is the general-rank
statement that `Gamma` lies in the elliptope — the rank-three shadow of which is
`Gtz.IsElliptopeGoodTriangle`. -/
theorem posSemidef_directionGramMatrix (D : WeightedDesign m k) :
    (directionGramMatrix D).PosSemidef := by
  rw [directionGramMatrix_eq_mul_transpose]
  simpa using Matrix.posSemidef_self_mul_conjTranspose (unitAtomRows D)

/-- **(c) IDEMPOTENCY, as a matrix identity**: `Gamma S Gamma = Gamma` with
`S = diag(s)`.  The direction Gram is a generalized inverse of the share diagonal;
equivalently `S^(1/2) Gamma S^(1/2)` is the projection `Gtz.projectionOfDesign`. -/
theorem directionGramMatrix_mul_diagonal_atomShare_mul_self (D : WeightedDesign m k) :
    directionGramMatrix D * Matrix.diagonal (atomShare D) * directionGramMatrix D
      = directionGramMatrix D := by
  ext firstIndex secondIndex
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, directionGramMatrix, Matrix.of_apply]
  rw [← sum_atomShare_mul_directionGram_mul_directionGram D firstIndex secondIndex]
  exact Finset.sum_congr rfl fun otherIndex _ => by ring

/-- **(c) THE ROW LAW**: `sum_d s_d gamma_ad^2 = 1` for every nondegenerate atom. -/
theorem sum_atomShare_mul_sq_directionGram (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) :
    ∑ otherIndex, atomShare D otherIndex * directionGram D atomIndex otherIndex ^ 2 = 1 := by
  have hmaster := sum_atomShare_mul_directionGram_mul_directionGram D atomIndex atomIndex
  rw [directionGram_self D hpositive] at hmaster
  rw [← hmaster]
  refine Finset.sum_congr rfl fun otherIndex _ => ?_
  rw [directionGram_comm D otherIndex atomIndex, ← pow_two]

/-- **(c) THE ROW LAW, split at the diagonal**: `s_a + sum_{d /= a} s_d gamma_ad^2 = 1`.
The atom's own share plus the squared correlations to everything else is exactly
one — the sharp form of the landed ceiling `Gtz.weighted_leverage_le_one`. -/
theorem atomShare_add_sum_erase_atomShare_mul_sq_directionGram (D : WeightedDesign m k)
    {atomIndex : Fin m} (hpositive : 0 < leverageOf (D.atom atomIndex)) :
    atomShare D atomIndex
        + ∑ otherIndex ∈ Finset.univ.erase atomIndex,
            atomShare D otherIndex * directionGram D atomIndex otherIndex ^ 2
      = 1 := by
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun otherIndex => atomShare D otherIndex * directionGram D atomIndex otherIndex ^ 2)
    (Finset.mem_univ atomIndex)
  have hrow := sum_atomShare_mul_sq_directionGram D hpositive
  have hdiagonal : atomShare D atomIndex * directionGram D atomIndex atomIndex ^ 2
      = atomShare D atomIndex := by
    rw [directionGram_self D hpositive, one_pow, mul_one]
  rw [hdiagonal] at hsplit
  linarith [hsplit, hrow]

/-- **(c) THE SUPPLY-CHAIN LAW**:
`sum_{d /= a,b} s_d gamma_ad gamma_db = (1 - s_a - s_b) gamma_ab`.
The off-diagonal reading of `Gamma S Gamma = Gamma`: whatever correlation the two
endpoints do not carry themselves has to be supplied by the rest of the design. -/
theorem sum_sdiff_atomShare_mul_directionGram_mul_directionGram (D : WeightedDesign m k)
    {firstIndex secondIndex : Fin m} (hdistinct : firstIndex ≠ secondIndex)
    (hfirstPositive : 0 < leverageOf (D.atom firstIndex))
    (hsecondPositive : 0 < leverageOf (D.atom secondIndex)) :
    ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin m)),
        atomShare D otherIndex
          * (directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex)
      = (1 - atomShare D firstIndex - atomShare D secondIndex)
        * directionGram D firstIndex secondIndex := by
  have hsplit := Finset.sum_sdiff
    (f := fun otherIndex => atomShare D otherIndex
      * (directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex))
    (Finset.subset_univ ({firstIndex, secondIndex} : Finset (Fin m)))
  have hpair : ∑ otherIndex ∈ ({firstIndex, secondIndex} : Finset (Fin m)),
      atomShare D otherIndex
        * (directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex)
      = atomShare D firstIndex * directionGram D firstIndex secondIndex
        + atomShare D secondIndex * directionGram D firstIndex secondIndex := by
    rw [Finset.sum_pair hdistinct, directionGram_self D hfirstPositive,
      directionGram_self D hsecondPositive, one_mul, mul_one]
  have hmaster := sum_atomShare_mul_directionGram_mul_directionGram D firstIndex secondIndex
  rw [hpair] at hsplit
  rw [hmaster] at hsplit
  linear_combination hsplit

/-- **A STRONG EDGE IS NEVER PRIVATE.**  If every third atom breaks the chain from
`a` to `b` — `gamma_ad gamma_db = 0` for all `d /= a, b` — then either the two
endpoints exhaust the whole share budget (`s_a + s_b = 1`) or their correlation is
zero.  There is no configuration in which two atoms hold a nonzero correlation
privately. -/
theorem atomShare_pair_eq_one_or_directionGram_eq_zero (D : WeightedDesign m k)
    {firstIndex secondIndex : Fin m} (hdistinct : firstIndex ≠ secondIndex)
    (hfirstPositive : 0 < leverageOf (D.atom firstIndex))
    (hsecondPositive : 0 < leverageOf (D.atom secondIndex))
    (hprivate : ∀ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin m)),
      directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex = 0) :
    atomShare D firstIndex + atomShare D secondIndex = 1
      ∨ directionGram D firstIndex secondIndex = 0 := by
  have hchain := sum_sdiff_atomShare_mul_directionGram_mul_directionGram D hdistinct
    hfirstPositive hsecondPositive
  have hvanishes : ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin m)),
      atomShare D otherIndex
        * (directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex)
      = 0 :=
    Finset.sum_eq_zero fun otherIndex hmember => by
      rw [hprivate otherIndex hmember, mul_zero]
  rw [hvanishes] at hchain
  rcases mul_eq_zero.mp hchain.symm with hleft | hright
  · exact Or.inl (by linarith)
  · exact Or.inr hright

/-- **A strong edge has a supplier.**  The usable contrapositive of the previous
theorem: two atoms carrying a nonzero correlation without exhausting the share
budget must have a third atom correlated with both. -/
theorem exists_directionGram_chain_ne_zero (D : WeightedDesign m k)
    {firstIndex secondIndex : Fin m} (hdistinct : firstIndex ≠ secondIndex)
    (hfirstPositive : 0 < leverageOf (D.atom firstIndex))
    (hsecondPositive : 0 < leverageOf (D.atom secondIndex))
    (hshare : atomShare D firstIndex + atomShare D secondIndex ≠ 1)
    (hedge : directionGram D firstIndex secondIndex ≠ 0) :
    ∃ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin m)),
      directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex ≠ 0 := by
  by_contra hnone
  push Not at hnone
  rcases atomShare_pair_eq_one_or_directionGram_eq_zero D hdistinct hfirstPositive
    hsecondPositive hnone with hleft | hright
  · exact hshare hleft
  · exact hedge hright

/-- **THE EQUALITY CASE OF THE ROW LAW — a saturated atom is orthogonal to
everything.**  An atom whose share is exactly one sits on the boundary of the
landed ceiling `Gtz.weighted_leverage_le_one`, and the row law then forces every
other atom of the design to be orthogonal to it.  Stated in raw pairings so it
composes with anything, and needing no hypothesis on the other leverages. -/
theorem atomPairing_eq_zero_of_atomShare_eq_one (D : WeightedDesign m k)
    {saturatedIndex : Fin m} (hsaturated : atomShare D saturatedIndex = 1)
    {otherIndex : Fin m} (hdistinct : otherIndex ≠ saturatedIndex) :
    D.atom saturatedIndex ⬝ᵥ D.atom otherIndex = 0 := by
  have hrow := sum_weight_mul_sq_atomPairing D saturatedIndex
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun index => D.weight index * (D.atom saturatedIndex ⬝ᵥ D.atom index) ^ 2)
    (Finset.mem_univ saturatedIndex)
  have hdiagonal : D.weight saturatedIndex
        * (D.atom saturatedIndex ⬝ᵥ D.atom saturatedIndex) ^ 2
      = leverageOf (D.atom saturatedIndex) := by
    rw [← leverageOf_eq_dotProduct, pow_two, ← mul_assoc, ← atomShare, hsaturated, one_mul]
  rw [hdiagonal] at hsplit
  have hoffDiagonalVanishes : ∑ index ∈ Finset.univ.erase saturatedIndex,
      D.weight index * (D.atom saturatedIndex ⬝ᵥ D.atom index) ^ 2 = 0 := by
    linarith [hsplit, hrow]
  have hnonneg : ∀ index ∈ Finset.univ.erase saturatedIndex,
      0 ≤ D.weight index * (D.atom saturatedIndex ⬝ᵥ D.atom index) ^ 2 :=
    fun index _ => mul_nonneg (D.weight_pos index).le (sq_nonneg _)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hoffDiagonalVanishes otherIndex
    (Finset.mem_erase.mpr ⟨hdistinct, Finset.mem_univ otherIndex⟩)
  rcases mul_eq_zero.mp hterm with hweight | hpairing
  · exact absurd hweight (D.weight_pos otherIndex).ne'
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hpairing

/-- **SATURATION IS ORTHOGONALITY, both ways.**  A nondegenerate atom has share
exactly one — the boundary of `Gtz.weighted_leverage_le_one` — precisely when it is
orthogonal to every other atom.  The forward direction is the equality case of the
row law; the backward direction is the raw row law with every off-diagonal term
deleted, which leaves `t_a l_a^2 = l_a`. -/
theorem atomShare_eq_one_iff_forall_atomPairing_eq_zero (D : WeightedDesign m k)
    {atomIndex : Fin m} (hpositive : 0 < leverageOf (D.atom atomIndex)) :
    atomShare D atomIndex = 1
      ↔ ∀ otherIndex, otherIndex ≠ atomIndex → D.atom atomIndex ⬝ᵥ D.atom otherIndex = 0 := by
  constructor
  · exact fun hsaturated otherIndex hdistinct =>
      atomPairing_eq_zero_of_atomShare_eq_one D hsaturated hdistinct
  · intro horthogonal
    have hrow := sum_weight_mul_sq_atomPairing D atomIndex
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun index => D.weight index * (D.atom atomIndex ⬝ᵥ D.atom index) ^ 2)
      (Finset.mem_univ atomIndex)
    rw [hrow] at hsplit
    have hoffDiagonalVanishes : ∑ index ∈ Finset.univ.erase atomIndex,
        D.weight index * (D.atom atomIndex ⬝ᵥ D.atom index) ^ 2 = 0 :=
      Finset.sum_eq_zero fun index hmember => by
        rw [horthogonal index (Finset.mem_erase.mp hmember).1]
        norm_num
    rw [hoffDiagonalVanishes, zero_add, ← leverageOf_eq_dotProduct] at hsplit
    rw [atomShare]
    refine mul_right_cancel₀ hpositive.ne' ?_
    rw [one_mul]
    linear_combination hsplit

/-! ## THE HEAVINESS PROFILE -/

/-- **THE HEAVINESS PROFILE.**  For every threshold `tau >= -1` and every subset
containing all the atoms of excess at least `tau`, that subset carries share at
least `(k-1) - tau`.

The proof is two per-atom inequalities, both division-free.  Inside the subset,
`(1+tau) t_c x_c <= (1+tau) s_c` because `x_c <= l_c` and `1 + tau >= 0`.  Outside
it, `(1+tau) t_c x_c <= tau s_c` because `x_c < tau` and `t_c > 0`.  Summing
against the budget `sum_c t_c x_c = k-1` and the frame trace `sum_c s_c = k` gives
`(1+tau)(k-1) <= s(H) + tau k`, which is the claim.

The hypothesis `-1 <= tau` is sharp: `Gtz.unitDesign` has `k = 1` and one atom of
share one, so at `tau = -2` the claim would read `1 >= 2`. -/
theorem rank_sub_one_sub_threshold_le_sum_atomShare (D : WeightedDesign m k) {threshold : ℝ}
    (hthreshold : -1 ≤ threshold) (heavySet : Finset (Fin m))
    (hcovers : ∀ atomIndex, atomIndex ∉ heavySet →
      leverageOf (D.atom atomIndex) - 1 < threshold) :
    (k : ℝ) - 1 - threshold ≤ ∑ atomIndex ∈ heavySet, atomShare D atomIndex := by
  have hscaleNonneg : (0 : ℝ) ≤ 1 + threshold := by linarith
  have hsplitBudget := Finset.sum_sdiff
    (f := fun atomIndex => D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1))
    (Finset.subset_univ heavySet)
  have hsplitShare := Finset.sum_sdiff (f := fun atomIndex => atomShare D atomIndex)
    (Finset.subset_univ heavySet)
  rw [sum_weight_mul_leverage_sub_one D] at hsplitBudget
  rw [sum_atomShare_eq_rank D] at hsplitShare
  have hheavyBound : (1 + threshold)
        * ∑ atomIndex ∈ heavySet, D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1)
      ≤ (1 + threshold) * ∑ atomIndex ∈ heavySet, atomShare D atomIndex := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun atomIndex _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ hscaleNonneg
    rw [atomShare]
    nlinarith [(D.weight_pos atomIndex).le]
  have hlightBound : (1 + threshold)
        * ∑ atomIndex ∈ Finset.univ \ heavySet,
            D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1)
      ≤ threshold * ∑ atomIndex ∈ Finset.univ \ heavySet, atomShare D atomIndex := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun atomIndex hmember => ?_
    have hlight := hcovers atomIndex (Finset.mem_sdiff.mp hmember).2
    have hweightPositive := D.weight_pos atomIndex
    rw [atomShare]
    nlinarith [mul_pos hweightPositive (sub_pos.mpr hlight)]
  have hcombined : (1 + threshold) * ((k : ℝ) - 1)
      ≤ (∑ atomIndex ∈ heavySet, atomShare D atomIndex) + threshold * (k : ℝ) := by
    have hexpand : (1 + threshold) * ((k : ℝ) - 1)
        = (1 + threshold)
            * ∑ atomIndex ∈ Finset.univ \ heavySet,
                D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1)
          + (1 + threshold)
            * ∑ atomIndex ∈ heavySet, D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1) := by
      rw [← mul_add, hsplitBudget]
    rw [hexpand]
    have hlightShare : ∑ atomIndex ∈ Finset.univ \ heavySet, atomShare D atomIndex
        = (k : ℝ) - ∑ atomIndex ∈ heavySet, atomShare D atomIndex := by linarith [hsplitShare]
    nlinarith [hheavyBound, hlightBound, hlightShare]
  linarith [hcombined]

/-- **The heaviness profile, on the honest heavy set.**  The specialization of the
profile to the filter of atoms whose excess reaches the threshold. -/
theorem rank_sub_one_sub_threshold_le_sum_atomShare_filter (D : WeightedDesign m k)
    {threshold : ℝ} (hthreshold : -1 ≤ threshold) :
    (k : ℝ) - 1 - threshold
      ≤ ∑ atomIndex ∈
          Finset.univ.filter fun atomIndex => threshold ≤ leverageOf (D.atom atomIndex) - 1,
          atomShare D atomIndex := by
  refine rank_sub_one_sub_threshold_le_sum_atomShare D hthreshold _ fun atomIndex hmember => ?_
  by_contra hcontra
  exact hmember (Finset.mem_filter.mpr ⟨Finset.mem_univ atomIndex, not_lt.mp hcontra⟩)

/-- **The heaviness profile, counted.**  Each share is at most one
(`Gtz.weighted_leverage_le_one`), so the profile is also a CARDINALITY bound: any
subset containing the atoms of excess at least `tau` has at least `(k-1) - tau`
elements.  At rank three this says at least two atoms have leverage at least one,
and at least one atom has leverage at least two. -/
theorem rank_sub_one_sub_threshold_le_card_heavySet (D : WeightedDesign m k) {threshold : ℝ}
    (hthreshold : -1 ≤ threshold) (heavySet : Finset (Fin m))
    (hcovers : ∀ atomIndex, atomIndex ∉ heavySet →
      leverageOf (D.atom atomIndex) - 1 < threshold) :
    (k : ℝ) - 1 - threshold ≤ (heavySet.card : ℝ) := by
  have hprofile := rank_sub_one_sub_threshold_le_sum_atomShare D hthreshold heavySet hcovers
  have hceiling : ∑ atomIndex ∈ heavySet, atomShare D atomIndex
      ≤ ∑ _atomIndex ∈ heavySet, (1 : ℝ) :=
    Finset.sum_le_sum fun atomIndex _ => by
      rw [atomShare]; exact weighted_leverage_le_one D atomIndex
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hceiling
  linarith

/-- **Every threshold below `k-1` is reached.**  The empty-subset instance of the
profile: if every atom had excess below `tau` then the profile would force
`k - 1 - tau <= 0`.  At rank three this says some atom has leverage at least
`1 + tau` for every `tau < 2`; the limiting statement `l_max >= 3` is the landed
`Gtz.exists_leverage_ge_rank`, restated below. -/
theorem exists_excess_ge_of_lt_rank_sub_one (D : WeightedDesign m k) {threshold : ℝ}
    (hlow : -1 ≤ threshold) (hhigh : threshold < (k : ℝ) - 1) :
    ∃ atomIndex, threshold ≤ leverageOf (D.atom atomIndex) - 1 := by
  by_contra hnone
  push Not at hnone
  have hbound := rank_sub_one_sub_threshold_le_sum_atomShare D hlow ∅
    fun atomIndex _ => hnone atomIndex
  rw [Finset.sum_empty] at hbound
  linarith

/-- **Any covering heavy set below the top threshold is nonempty.**  The profile
gives it positive share, and the empty set has share zero. -/
theorem heavySet_nonempty_of_lt_rank_sub_one (D : WeightedDesign m k) {threshold : ℝ}
    (hlow : -1 ≤ threshold) (hhigh : threshold < (k : ℝ) - 1) (heavySet : Finset (Fin m))
    (hcovers : ∀ atomIndex, atomIndex ∉ heavySet →
      leverageOf (D.atom atomIndex) - 1 < threshold) :
    heavySet.Nonempty := by
  rcases Finset.eq_empty_or_nonempty heavySet with hempty | hnonempty
  · have hbound := rank_sub_one_sub_threshold_le_sum_atomShare D hlow heavySet hcovers
    rw [hempty, Finset.sum_empty] at hbound
    linarith
  · exact hnonempty

/-- **The light atoms carry share at most one.**  The `tau = 0` instance of the
profile, read on the complement: the atoms of leverage strictly below one own at
most a unit of the total share `k`. -/
theorem sum_atomShare_le_one_of_light (D : WeightedDesign m k) (lightSet : Finset (Fin m))
    (hlight : ∀ atomIndex ∈ lightSet, leverageOf (D.atom atomIndex) < 1) :
    ∑ atomIndex ∈ lightSet, atomShare D atomIndex ≤ 1 := by
  have hprofile := rank_sub_one_sub_threshold_le_sum_atomShare D (threshold := 0)
    (by norm_num) (Finset.univ \ lightSet) fun atomIndex hmember => by
      have hmemberLight : atomIndex ∈ lightSet := by
        by_contra hcontra
        exact hmember (Finset.mem_sdiff.mpr ⟨Finset.mem_univ atomIndex, hcontra⟩)
      linarith [hlight atomIndex hmemberLight]
  have hsplit := Finset.sum_sdiff (f := fun atomIndex => atomShare D atomIndex)
    (Finset.subset_univ lightSet)
  rw [sum_atomShare_eq_rank D] at hsplit
  linarith [hprofile, hsplit]

/-! ### The threshold hypothesis is sharp -/

/-- The heaviness profile at a FIXED threshold, quantified over every design of
every size and rank.  Naming the statement is what makes the sharpness of the
hypothesis `-1 <= tau` provable rather than merely asserted. -/
def HeavinessProfileAt (threshold : ℝ) : Prop :=
  ∀ (size rank : ℕ) (D : WeightedDesign size rank) (heavySet : Finset (Fin size)),
    (∀ atomIndex, atomIndex ∉ heavySet → leverageOf (D.atom atomIndex) - 1 < threshold) →
      (rank : ℝ) - 1 - threshold ≤ ∑ atomIndex ∈ heavySet, atomShare D atomIndex

/-- The profile holds at every threshold from `-1` upward. -/
theorem heavinessProfileAt_of_neg_one_le {threshold : ℝ} (hthreshold : -1 ≤ threshold) :
    HeavinessProfileAt threshold :=
  fun _size _rank D heavySet hcovers =>
    rank_sub_one_sub_threshold_le_sum_atomShare D hthreshold heavySet hcovers

/-- **AND IT FAILS BELOW `-1`.**  `Gtz.unitDesign` — one atom of leverage one and
weight one in `ℝ¹` — has total share `1`, while the profile at `tau < -1` would
demand `1 - 1 - tau = -tau > 1`.  So the hypothesis `-1 <= tau` of
`rank_sub_one_sub_threshold_le_sum_atomShare` cannot be dropped or weakened. -/
theorem not_heavinessProfileAt_of_lt_neg_one {threshold : ℝ} (hthreshold : threshold < -1) :
    ¬ HeavinessProfileAt threshold := by
  intro hprofile
  have hinstance := hprofile 1 1 unitDesign Finset.univ fun atomIndex hmember =>
    absurd (Finset.mem_univ atomIndex) hmember
  have hshare : ∑ atomIndex : Fin 1, atomShare unitDesign atomIndex = 1 := by
    rw [Fin.sum_univ_one, atomShare]
    show (1 : ℝ) * leverageOf (fun _ : Fin 1 => (1 : ℝ)) = 1
    rw [leverageOf, Fin.sum_univ_one]
    norm_num
  rw [hshare] at hinstance
  push_cast at hinstance
  linarith

/-! ## THE PINNING -/

/-- **EVERY LEVERAGE CAP IS AT LEAST THE RANK.**  The weighted mean of the leverages
is exactly `k` (`Gtz.sum_weighted_leverage`), so a uniform upper bound cannot fall
below `k`.  This is `Gtz.exists_leverage_ge_rank` in cap form, and it is stronger:
it holds for every real bound, attained or not, and needs no `1 <= k`. -/
theorem rank_le_of_forall_leverage_le (D : WeightedDesign m k) {cap : ℝ}
    (hcap : ∀ atomIndex, leverageOf (D.atom atomIndex) ≤ cap) : (k : ℝ) ≤ cap := by
  have hbound : ∑ atomIndex, D.weight atomIndex * leverageOf (D.atom atomIndex)
      ≤ ∑ atomIndex, D.weight atomIndex * cap :=
    Finset.sum_le_sum fun atomIndex _ =>
      mul_le_mul_of_nonneg_left (hcap atomIndex) (D.weight_pos atomIndex).le
  rwa [sum_weighted_leverage D, ← Finset.sum_mul, D.weight_sum_one, one_mul] at hbound

/-- **EVERY LEVERAGE FLOOR IS AT MOST THE RANK**, the dual reading — the cap form of
`Gtz.exists_leverage_le_rank`. -/
theorem le_rank_of_forall_le_leverage (D : WeightedDesign m k) {floor : ℝ}
    (hfloor : ∀ atomIndex, floor ≤ leverageOf (D.atom atomIndex)) : floor ≤ (k : ℝ) := by
  have hbound : ∑ atomIndex, D.weight atomIndex * floor
      ≤ ∑ atomIndex, D.weight atomIndex * leverageOf (D.atom atomIndex) :=
    Finset.sum_le_sum fun atomIndex _ =>
      mul_le_mul_of_nonneg_left (hfloor atomIndex) (D.weight_pos atomIndex).le
  rwa [← Finset.sum_mul, D.weight_sum_one, one_mul, sum_weighted_leverage D] at hbound

/-- **THE PINNING, from below.**  The weighted mean of the leverages is exactly the
rank, so if every leverage is at least the rank then every leverage EQUALS the
rank.  No all-heaviness, no rank restriction: this is the equality case of the
floor bound `le_rank_of_forall_le_leverage` at `floor = k`, and of a weighted
average with strictly positive weights. -/
theorem forall_leverage_eq_rank_of_forall_rank_le (D : WeightedDesign m k)
    (hheavy : ∀ atomIndex, (k : ℝ) ≤ leverageOf (D.atom atomIndex)) :
    ∀ atomIndex, leverageOf (D.atom atomIndex) = (k : ℝ) := by
  have hvanishes : ∑ atomIndex, D.weight atomIndex * (leverageOf (D.atom atomIndex) - (k : ℝ))
      = 0 := by
    have hexpand : ∀ atomIndex : Fin m,
        D.weight atomIndex * (leverageOf (D.atom atomIndex) - (k : ℝ))
          = D.weight atomIndex * leverageOf (D.atom atomIndex)
            - (k : ℝ) * D.weight atomIndex := fun atomIndex => by ring
    rw [Finset.sum_congr rfl fun atomIndex _ => hexpand atomIndex, Finset.sum_sub_distrib,
      sum_weighted_leverage D, ← Finset.mul_sum, D.weight_sum_one, mul_one, sub_self]
  have hnonneg : ∀ atomIndex ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ D.weight atomIndex * (leverageOf (D.atom atomIndex) - (k : ℝ)) :=
    fun atomIndex _ => mul_nonneg (D.weight_pos atomIndex).le (by linarith [hheavy atomIndex])
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hvanishes
  intro atomIndex
  rcases mul_eq_zero.mp (hterms atomIndex (Finset.mem_univ atomIndex)) with hweight | hleverage
  · exact absurd hweight (D.weight_pos atomIndex).ne'
  · linarith

/-- **THE PINNING, from above.**  The dual statement: every leverage at most the
rank forces every leverage to equal the rank. -/
theorem forall_leverage_eq_rank_of_forall_le_rank (D : WeightedDesign m k)
    (hlight : ∀ atomIndex, leverageOf (D.atom atomIndex) ≤ (k : ℝ)) :
    ∀ atomIndex, leverageOf (D.atom atomIndex) = (k : ℝ) := by
  have hvanishes : ∑ atomIndex, D.weight atomIndex * ((k : ℝ) - leverageOf (D.atom atomIndex))
      = 0 := by
    have hexpand : ∀ atomIndex : Fin m,
        D.weight atomIndex * ((k : ℝ) - leverageOf (D.atom atomIndex))
          = (k : ℝ) * D.weight atomIndex
            - D.weight atomIndex * leverageOf (D.atom atomIndex) := fun atomIndex => by ring
    rw [Finset.sum_congr rfl fun atomIndex _ => hexpand atomIndex, Finset.sum_sub_distrib,
      ← Finset.mul_sum, D.weight_sum_one, mul_one, sum_weighted_leverage D, sub_self]
  have hnonneg : ∀ atomIndex ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ D.weight atomIndex * ((k : ℝ) - leverageOf (D.atom atomIndex)) :=
    fun atomIndex _ => mul_nonneg (D.weight_pos atomIndex).le (by linarith [hlight atomIndex])
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hvanishes
  intro atomIndex
  rcases mul_eq_zero.mp (hterms atomIndex (Finset.mem_univ atomIndex)) with hweight | hleverage
  · exact absurd hweight (D.weight_pos atomIndex).ne'
  · linarith

/-- **The uniform stratum at rank three.**  Once every excess reaches `2` the
budget permits nothing but `x == 2`, i.e. leverage exactly three at every atom.
This is why every classical rank-three witness — the tetrahedron, `K_4`, the
icosahedron, `splitSeven` — lives on `l == 3`. -/
theorem forall_leverage_eq_three_of_forall_two_le_excess (D : WeightedDesign m 3)
    (hexcess : ∀ atomIndex, 2 ≤ leverageOf (D.atom atomIndex) - 1) :
    ∀ atomIndex, leverageOf (D.atom atomIndex) = 3 := by
  have hcast : ((3 : ℕ) : ℝ) = 3 := by norm_num
  have hpinned := forall_leverage_eq_rank_of_forall_rank_le D fun atomIndex => by
    rw [hcast]; linarith [hexcess atomIndex]
  intro atomIndex
  rw [hpinned atomIndex, hcast]

/-- **The leverage floor at rank three**, `l_max >= 3`: the landed
`Gtz.exists_leverage_ge_rank` specialized to the rank the `(7,3)` workflow reads.
Not a new proof — the numeral is discharged, nothing else. -/
theorem exists_leverage_three_le (D : WeightedDesign m 3) :
    ∃ atomIndex, (3 : ℝ) ≤ leverageOf (D.atom atomIndex) := by
  obtain ⟨atomIndex, hbound⟩ := exists_leverage_ge_rank D (by norm_num)
  refine ⟨atomIndex, ?_⟩
  rw [show ((3 : ℕ) : ℝ) = 3 from by norm_num] at hbound
  exact hbound

/-! ## The direction companion -/

/-- **The direction companion of a design**: the same directions, weighted by
`s_c / k`.  The frame law says this really is a weighted design, and its every
leverage is exactly the rank (`leverageOf_directionDesign_atom`) — the uniform
stratum the pinning theorem identifies as the only one a one-sided leverage bound
permits.

This is NOT a reduction of the selection problem: the atoms are rescaled by
`sqrt k / |g_c|`, so `Dominates` is a different statement about the companion. -/
noncomputable def directionDesign (D : WeightedDesign m k) (hrank : 1 ≤ k)
    (hpositive : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex)) : WeightedDesign m k where
  atom := fun atomIndex => Real.sqrt (k : ℝ) • unitAtom D atomIndex
  weight := fun atomIndex => atomShare D atomIndex / (k : ℝ)
  weight_pos := fun atomIndex => by
    have hrankPositive : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
    exact div_pos (mul_pos (D.weight_pos atomIndex) (hpositive atomIndex)) hrankPositive
  weight_sum_one := by
    have hrankPositive : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
    rw [← Finset.sum_div, sum_atomShare_eq_rank D, div_self hrankPositive.ne']
  isParseval := by
    have hrankNonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hrankPositive : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
    rw [← sum_atomShare_smul_atomMatrix_unitAtom D]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [atomMatrix_smul, Real.sq_sqrt hrankNonneg, smul_smul, div_mul_cancel₀ _ hrankPositive.ne']

/-- Every atom of the direction companion has leverage exactly the rank. -/
theorem leverageOf_directionDesign_atom (D : WeightedDesign m k) (hrank : 1 ≤ k)
    (hpositive : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex)) (atomIndex : Fin m) :
    leverageOf ((directionDesign D hrank hpositive).atom atomIndex) = (k : ℝ) := by
  have hrankNonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  show leverageOf (Real.sqrt (k : ℝ) • unitAtom D atomIndex) = (k : ℝ)
  rw [leverageOf_smul, Real.sq_sqrt hrankNonneg, leverageOf_unitAtom D (hpositive atomIndex),
    mul_one]

/-! ## Calibration at the regular tetrahedron

Definition-pinning in the sense of `Gtz/Core/Sanity.lean`: the campaign's canonical
tie object is run through every quantity of this file and the constants come out at
the pen's values.  `Gtz.tetraDesign` has weights `1/4` and leverages `3`, hence
shares `3/4`, excesses `2`, amplifications `A^2 = 3/2` and direction correlations
`gamma^2 = 1/9` (the `cos phi = -1/3` of the pen).  The budget is then computed
INDEPENDENTLY of the general law, `4 * (3/4) * (2/3) = 2`, and agrees with
`sum_atomShare_mul_inv_leverageAmplification_sq_three` at `k - 1 = 2`.  If a
refactor ever breaks one of these, a definition drifted from the mathematics. -/

/-- Every tetrahedron atom has leverage three. -/
theorem leverageOf_tetraDesign_atom (atomIndex : Fin 4) :
    leverageOf (tetraDesign.atom atomIndex) = 3 := by
  rw [leverageOf_eq_dotProduct]
  exact tetraAtom_dot_self atomIndex

/-- Every tetrahedron atom has share `3/4`. -/
theorem atomShare_tetraDesign (atomIndex : Fin 4) : atomShare tetraDesign atomIndex = 3 / 4 := by
  rw [atomShare, leverageOf_tetraDesign_atom]
  show (1 : ℝ) / 4 * 3 = 3 / 4
  norm_num

/-- Every tetrahedron amplification squares to `3/2`. -/
theorem leverageAmplification_sq_tetraDesign (atomIndex : Fin 4) :
    leverageAmplification tetraDesign atomIndex ^ 2 = 3 / 2 := by
  rw [leverageAmplification_sq tetraDesign
      (by rw [leverageOf_tetraDesign_atom]; norm_num),
    leverageOf_tetraDesign_atom]
  norm_num

/-- Distinct tetrahedron directions correlate at `gamma^2 = 1/9`, i.e.
`cos phi = -1/3` up to the sign the squared Gram data does not record. -/
theorem sq_directionGram_tetraDesign_of_ne {firstIndex secondIndex : Fin 4}
    (hdistinct : firstIndex ≠ secondIndex) :
    directionGram tetraDesign firstIndex secondIndex ^ 2 = 1 / 9 := by
  have hpairing : (tetraDesign.atom firstIndex ⬝ᵥ tetraDesign.atom secondIndex) ^ 2 = 1 :=
    tetraAtom_dot_sq_of_ne hdistinct
  have hinvSq : ((Real.sqrt (3 : ℝ))⁻¹) ^ 2 = (3 : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [directionGram_eq_scaled_atomPairing]
  simp only [leverageOf_tetraDesign_atom]
  rw [mul_pow, mul_pow, hinvSq, hpairing]
  norm_num

/-- **The budget at the tetrahedron, computed by hand**: four atoms of share `3/4`
and reciprocal amplification square `2/3` give exactly `2 = k - 1`. -/
theorem sum_atomShare_mul_inv_leverageAmplification_sq_tetraDesign :
    ∑ atomIndex, atomShare tetraDesign atomIndex
        * (leverageAmplification tetraDesign atomIndex)⁻¹ ^ 2 = 2 := by
  have hterm : ∀ atomIndex : Fin 4, atomShare tetraDesign atomIndex
      * (leverageAmplification tetraDesign atomIndex)⁻¹ ^ 2 = 1 / 2 := by
    intro atomIndex
    rw [atomShare_tetraDesign, inv_pow, leverageAmplification_sq_tetraDesign]
    norm_num
  rw [Finset.sum_congr rfl fun atomIndex _ => hterm atomIndex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- The tetrahedron sits on the pinning: every leverage equals the rank, so the
one-sided bound `3 <= l_c` already forces `l_c = 3`. -/
theorem forall_leverage_eq_three_tetraDesign (atomIndex : Fin 4) :
    leverageOf (tetraDesign.atom atomIndex) = 3 :=
  forall_leverage_eq_three_of_forall_two_le_excess tetraDesign
    (fun index => by rw [leverageOf_tetraDesign_atom]; norm_num) atomIndex

end Gtz
