/-
# The (7,3) metric reformulation, the Veronese no-go, and the exact extremal

Residual lane R-A of the July 2026 workflow.  Four deliverables, in descending
order of certainty.  Every constant below is an exact rational or an exact
element of `ℚ(√5)`; decimals appear only in this docstring, as renderings.

## PROVED, unconditionally

**(1) The metric reformulation.**  Put `Y_c = u_c u_cᵀ − (1/k) I` for the unit
direction `u_c` of an atom (`Gtz.veroneseTracelessPart`).  Then, exactly:

* `tr Y_c = 0` — `trace_veroneseTracelessPart`;
* `|Y_c|_F² = 1 − 1/k`, so `2/3` at rank three —
  `frobeniusNormSq_veroneseTracelessPart`;
* `⟨Y_c, Y_d⟩_F = γ_cd² − 1/k` — `frobeniusInner_veroneseTracelessPart`: the Gram
  matrix of the `Y`'s IS the Hadamard square of the direction Gram, shifted by
  `−1/k` on every entry;
* `Σ_c Y_c = 0` on the equal-share stratum —
  `sum_veroneseTracelessPart_eq_zero`;
* `Σ_{c ∈ T} Y_c = S_T − I` for any `k`-subset `T`, `S_T` the sum of the selected
  unit direction atoms — `sum_veroneseTracelessPart_subset_eq`;
* `|Y_a + Y_b + Y_c|_F² = 2 σ_T` at rank three —
  `frobeniusNormSq_tripleTracelessSum_eq_two_mul_tripleSigma`;
* the rank-one constraint itself, `Y² = (1 − 2/k) Y + (1/k − 1/k²) I` —
  `veroneseTracelessPart_sq`, which at rank three is `Y² = Y/3 + 2I/9`.

Consequence, the reformulation: on the (7,3) equal-share stratum a triple
DOMINATES as soon as `|Y_a + Y_b + Y_c|_F² ≤ 2/3 = |Y_c|_F²`
(`dominates_triple_of_frobeniusNormSq_le_two_thirds`).  Packaged as
`Gtz.MetricTripleBoundSevenThree`, one Frobenius inequality per design.  No
signs, no triangle products, no projections.

**(2) The Veronese no-go.**  Relax the reformulation to what the Gram matrix of
the `Y`'s alone can see — positive semidefiniteness, constant diagonal `2/3`,
vanishing row sums — and it becomes FALSE.  The relaxation genuinely implies the
metric bound (`metricTripleBoundSevenThree_of_abstract`), and it is refuted by
`Gtz.uniformVeroneseGramWitness = (7/9) I − (1/9) J`: positive semidefinite,
diagonal `2/3`, every row summing to zero, and yet EVERY triple carries block
mass `3·(2/3) + 6·(−1/9) = 4/3`, exactly twice the target
(`not_abstractMetricTripleBound_sevenThree`).  In sigma coordinates the witness
sits at `σ = 2/3` on every triple — precisely the constant at which the
campaign's four independent conservation/averaging arguments all stall.  So the
relaxation admits a point at `σ = 2/3` on every triple, and therefore CANNOT
prove any bound below `2/3` — the factor of two is a property of the relaxation,
not a weakness of those arguments.  (That `2/3` is the relaxation's OPTIMUM is
not claimed; only that it is achieved, which is what kills the route.)

And the witness is provably NOT realizable, so this is a no-go for
Gram-Hadamard-square methods and not a refutation of the metric bound.
`hadamardSquareDirectionGram_eq_veronese_mul` factors `Γ∘Γ` through the
six-dimensional space of symmetric `3×3` matrices, whence
`rank (Γ∘Γ) ≤ 6` for every `WeightedDesign m 3`
(`rank_hadamardSquareDirectionGram_le_six`), while the witness demands
`(7/9) I + (2/9) J`, positive definite of rank seven
(`rank_uniformHadamardSquareTarget`).  Hence no (7,3) design has all twenty-one
squared correlations equal to `2/9`
(`not_exists_design_with_uniform_edgeWeight_two_ninths`) — the `WeightedDesign`
case of Gerzon's bound, i.e. barrier B3, mechanized.  Note the scope: the landed
statement quantifies over `WeightedDesign 7 3`, so it rules out equiangular
PARSEVAL frames.  Seven equiangular lines in `ℝ³` need not be scalable to a
Parseval frame, so the classical "no seven equiangular lines in `ℝ³`" is NOT
formally a consequence of the statement as written — though the same rank
argument proves it, since `rank_hadamardSquareDirectionGram_le_six` uses only the
Veronese factorisation and never `isParseval`.

**(3) The extremal, in exact closed form.**  `Gtz.pentagonPairDesign` is the
`WeightedDesign 7 3` of two parallel copies of the cone axis plus a regular
pentagon on the cone with `cos² = 1/15`.  It is on the equal-share stratum
(weights `1/7`, leverages `3` — `pentagonPairDesign_atomShare`,
`pentagonPairDesign_leverage`), and its twenty-one edge weights are exactly

* `1` on the parallel pair,
* `1/15` on the ten axis-to-pentagon edges,
* `(27 − 7√5)/90` on the five pentagon sides,
* `(27 + 7√5)/90` on the five pentagon diagonals

(`edgeWeight_pentagonPairDesign`, via the integer tables
`pentagonPairEdgeNumerator` and `pentagonPairEdgeRootCoefficient` over the common
denominator `90`; every row sums to `7/3` including its diagonal `1`, so the
off-diagonal mass is `4/3` — `sum_edgeWeight_pentagonPairDesign`).  Its
thirty-five triple sigmas take
five values, of which the least is

  `min_T σ_T = (39 − 7√5)/90 = 0.2594169351…`

attained on "one axis atom plus two adjacent pentagon atoms"
(`pentagonPairDesign_min_tripleSigma`, an `IsLeast`).  So the closed form the
brief flagged as numerically identified is RE-DERIVED: it is exactly right, and
the reported `8·10⁻⁸` discrepancy was optimizer tolerance.

Two consequences.  The sharp constant `c` in "every equal-share (7,3) design has
a triple with `σ_T ≤ c`" satisfies `c ≥ (39 − 7√5)/90`
(`le_level_of_forall_exists_tripleSigma_le`), and in Frobenius coordinates the
target `2/3` cannot be lowered past `(39 − 7√5)/45 = 0.5188…`
(`le_level_of_forall_exists_frobeniusNormSq_le`).  And the sigma gate's threshold
`1/3` clears the extremal with exact margin `(7√5 − 9)/90 = 0.0739…`
(`pentagonPairDesign_tripleSigma_margin`), so the extremal is DOMINATED, by an
exhibited triple (`dominates_pentagonPairDesign_extremalTriple`).  The gate route
is not obstructed by the worst case.

**(4) The merge-boundary route.**  The extremal has a parallel pair
(`hasParallelPair_pentagonPairDesign`) — its atoms `0` and `1` are literally
equal — so it sits where `Gtz.dominating_of_parallel_pair` pays with no
quantitative hypothesis.  The exact statement that would turn that observation
into a proof is `Gtz.MergeBoundaryCollarSevenThree`, and
`gtzWeightedEqualShareSevenThree_of_mergeBoundaryCollar` shows what it buys:
together with `GtzWeighted 6 3` it closes the (7,3) equal-share cell.

## HYPOTHESIS

`MetricTripleBoundSevenThree`, `AbstractMetricTripleBoundSevenThree`,
`MergeBoundaryCollarSevenThree` and `GtzWeighted 6 3` are hypotheses wherever
they appear; nothing here proves any of them.  Equal-share side conditions
(`atomShare ≡ 3/7`, `leverage ≡ 3`) are carried explicitly wherever
`Gtz.Dominates` is touched, as in the sibling middle-band module.

## NOT PROVED

* **The metric bound itself.**  The residual is exactly:
  `min_T |Y_a + Y_b + Y_c|_F² ≤ 2/3` for every (7,3) equal-share design.  Item
  (2) proves that margin cannot be recovered from the `Y`-Gram alone; item (3)
  proves the target cannot be improved past `(39 − 7√5)/45`.
* **That `(39 − 7√5)/90` is the SUPREMUM.**  What is proved is that it is
  ATTAINED at `pentagonPairDesign`, hence a lower bound for the sharp constant.
  The numerical evidence for supremality (200 restarts, three settings) is not a
  proof and is not asserted as one.  Everything stated about the sharp constant
  is a one-sided bound.
* **The merge-boundary dichotomy.**  It does not follow from anything landed, and
  the obstruction is structural: `¬ HasParallelPair` is an OPEN condition, so the
  non-parallel stratum is not compact, its closure meets the parallel locus, and
  the supremum of `min_T σ_T` over it equals the supremum over the closure.
  The expected — not verified here — consequence is that separating the
  extremal's two axis atoms by `ε` yields non-parallel designs whose `min_T σ_T`
  tends to `(39 − 7√5)/90`, to which the merge branch does not apply; the exact
  rational versions of that separation at (6,3) and (7,3) are already recorded as
  no-go 1 of `Gtz/Reduction/SplitTransfer.lean`.  The extremal satisfies BOTH branches
  (`pentagonPairDesign_satisfies_both_mergeBoundaryBranches`), so it is no
  evidence either way.
* **The passage from a general (7,3) design to the equal-share stratum.**  No
  such reduction is landed anywhere in the tree; it is the campaign's
  "uniform-share / leverage pinning" residual.  Consequently the strongest
  consequence drawn from `MetricTripleBoundSevenThree` here is
  `GtzWeightedEqualShareSevenThree` — the CELL, not `GtzWeightedAll 3`
  (`gtzWeightedEqualShareSevenThree_of_metricTripleBound`).
* Nothing here touches the light-atom half, which is a theorem elsewhere.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.FrameConservation
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.Quantitative.WeightProductFloor
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.SevenThreeMiddleBand
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.StressWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The Frobenius pairing

Entrywise, so bilinearity is free; the trace bridge is a lemma, used only where
a matrix product genuinely has to be collapsed. -/

/-- The Frobenius (Hilbert–Schmidt) pairing of two square real matrices,
entrywise. -/
noncomputable def frobeniusInner (leftMatrix rightMatrix : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  ∑ rowIndex, ∑ colIndex, leftMatrix rowIndex colIndex * rightMatrix rowIndex colIndex

/-- The squared Frobenius norm. -/
noncomputable def frobeniusNormSq (target : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  frobeniusInner target target

theorem frobeniusInner_comm (leftMatrix rightMatrix : Matrix (Fin k) (Fin k) ℝ) :
    frobeniusInner leftMatrix rightMatrix = frobeniusInner rightMatrix leftMatrix :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem frobeniusInner_add_left (firstMatrix secondMatrix rightMatrix :
    Matrix (Fin k) (Fin k) ℝ) :
    frobeniusInner (firstMatrix + secondMatrix) rightMatrix
      = frobeniusInner firstMatrix rightMatrix + frobeniusInner secondMatrix rightMatrix := by
  simp only [frobeniusInner, Matrix.add_apply, add_mul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_add_distrib

theorem frobeniusInner_add_right (leftMatrix firstMatrix secondMatrix :
    Matrix (Fin k) (Fin k) ℝ) :
    frobeniusInner leftMatrix (firstMatrix + secondMatrix)
      = frobeniusInner leftMatrix firstMatrix + frobeniusInner leftMatrix secondMatrix := by
  rw [frobeniusInner_comm, frobeniusInner_add_left, frobeniusInner_comm firstMatrix,
    frobeniusInner_comm secondMatrix]

/-- **The three-term expansion.**  This is the only algebraic fact the metric
reformulation needs beyond the pairwise values. -/
theorem frobeniusNormSq_add_add (firstMatrix secondMatrix thirdMatrix :
    Matrix (Fin k) (Fin k) ℝ) :
    frobeniusNormSq (firstMatrix + secondMatrix + thirdMatrix)
      = frobeniusNormSq firstMatrix + frobeniusNormSq secondMatrix
          + frobeniusNormSq thirdMatrix
        + 2 * frobeniusInner firstMatrix secondMatrix
        + 2 * frobeniusInner firstMatrix thirdMatrix
        + 2 * frobeniusInner secondMatrix thirdMatrix := by
  simp only [frobeniusNormSq, frobeniusInner_add_left, frobeniusInner_add_right]
  rw [frobeniusInner_comm secondMatrix firstMatrix, frobeniusInner_comm thirdMatrix firstMatrix,
    frobeniusInner_comm thirdMatrix secondMatrix]
  ring

/-- The trace bridge: against a symmetric right argument the Frobenius pairing
is the trace of the plain product. -/
theorem frobeniusInner_eq_trace_mul (leftMatrix rightMatrix : Matrix (Fin k) (Fin k) ℝ)
    (hsymmetric : rightMatrixᵀ = rightMatrix) :
    frobeniusInner leftMatrix rightMatrix = Matrix.trace (leftMatrix * rightMatrix) := by
  simp only [frobeniusInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun rowIndex _ => Finset.sum_congr rfl fun colIndex _ => ?_
  have hentry : rightMatrix rowIndex colIndex = rightMatrix colIndex rowIndex := by
    rw [← Matrix.transpose_apply rightMatrix colIndex rowIndex, hsymmetric]
  rw [hentry]

/-! ## 2. The traceless Veronese part and the four exact identities

`Y_c = u_c u_cᵀ − (1/k) I`.  Everything in this section is an identity; no
inequality and no stratum hypothesis beyond nondegeneracy of the atoms
involved. -/

/-- **The traceless Veronese part** of an atom: its unit direction's rank-one
projection, recentred to trace zero. -/
noncomputable def veroneseTracelessPart (D : WeightedDesign m k) (atomIndex : Fin m) :
    Matrix (Fin k) (Fin k) ℝ :=
  atomMatrix (unitAtom D atomIndex) - ((k : ℝ)⁻¹) • 1

theorem transpose_atomMatrix (vector : Fin k → ℝ) :
    (atomMatrix vector)ᵀ = atomMatrix vector :=
  transpose_eq_of_isHermitian (posSemidef_atomMatrix vector).1

theorem transpose_veroneseTracelessPart (D : WeightedDesign m k) (atomIndex : Fin m) :
    (veroneseTracelessPart D atomIndex)ᵀ = veroneseTracelessPart D atomIndex := by
  rw [veroneseTracelessPart, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, transpose_atomMatrix]

/-- The trace of a product of two rank-one atoms is the squared pairing. -/
theorem trace_atomMatrix_mul_atomMatrix (firstVector secondVector : Fin k → ℝ) :
    Matrix.trace (atomMatrix firstVector * atomMatrix secondVector)
      = (firstVector ⬝ᵥ secondVector) ^ 2 := by
  rw [atomMatrix, atomMatrix, vecMulVec_mul_vecMulVec, Matrix.trace_smul,
    Matrix.trace_vecMulVec, smul_eq_mul, pow_two]

/-- **Identity 1: `Y_c` is traceless.** -/
theorem trace_veroneseTracelessPart (D : WeightedDesign m k) (hrank : 0 < k)
    {atomIndex : Fin m} (hnondegenerate : 0 < leverageOf (D.atom atomIndex)) :
    Matrix.trace (veroneseTracelessPart D atomIndex) = 0 := by
  have hrankNe : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hrank.ne'
  rw [veroneseTracelessPart, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    trace_atomMatrix, leverageOf_unitAtom D hnondegenerate, smul_eq_mul,
    Fintype.card_fin, inv_mul_cancel₀ hrankNe, sub_self]

/-- **Identity 3: the Gram matrix of the `Y`'s is the Hadamard square of the
direction Gram, shifted by `−1/k` on every entry.**  This is the identity that
makes the whole reformulation metric: all the campaign's edge weights
`w_cd = γ_cd²` are Frobenius pairings of the `Y`'s. -/
theorem frobeniusInner_veroneseTracelessPart (D : WeightedDesign m k) (hrank : 0 < k)
    {firstIndex secondIndex : Fin m}
    (hfirst : 0 < leverageOf (D.atom firstIndex))
    (hsecond : 0 < leverageOf (D.atom secondIndex)) :
    frobeniusInner (veroneseTracelessPart D firstIndex) (veroneseTracelessPart D secondIndex)
      = directionGram D firstIndex secondIndex ^ 2 - ((k : ℝ))⁻¹ := by
  have hrankNe : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hrank.ne'
  have hexpand : veroneseTracelessPart D firstIndex * veroneseTracelessPart D secondIndex
      = atomMatrix (unitAtom D firstIndex) * atomMatrix (unitAtom D secondIndex)
        - ((k : ℝ))⁻¹ • atomMatrix (unitAtom D firstIndex)
        - ((k : ℝ))⁻¹ • atomMatrix (unitAtom D secondIndex)
        + (((k : ℝ))⁻¹ * ((k : ℝ))⁻¹) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    simp only [veroneseTracelessPart, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_sub, smul_smul]
    abel
  rw [frobeniusInner_eq_trace_mul _ _ (transpose_veroneseTracelessPart D secondIndex), hexpand,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_smul, trace_atomMatrix_mul_atomMatrix,
    trace_atomMatrix, trace_atomMatrix, leverageOf_unitAtom D hfirst,
    leverageOf_unitAtom D hsecond, Matrix.trace_one, Fintype.card_fin, directionGram]
  simp only [smul_eq_mul, mul_one]
  field_simp
  ring

/-- **Identity 2: every `Y_c` has squared Frobenius norm `1 − 1/k`** — the value
`2/3` at rank three, which is the target constant of the metric bound. -/
theorem frobeniusNormSq_veroneseTracelessPart (D : WeightedDesign m k) (hrank : 0 < k)
    {atomIndex : Fin m} (hnondegenerate : 0 < leverageOf (D.atom atomIndex)) :
    frobeniusNormSq (veroneseTracelessPart D atomIndex) = 1 - ((k : ℝ))⁻¹ := by
  rw [frobeniusNormSq, frobeniusInner_veroneseTracelessPart D hrank hnondegenerate
    hnondegenerate, directionGram_self D hnondegenerate, one_pow]

/-- The unit direction atoms of an equal-share design resolve `(m/k) I`. -/
theorem sum_atomMatrix_unitAtom_of_equalShare (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ)) :
    ∑ atomIndex, atomMatrix (unitAtom D atomIndex)
      = (((m : ℝ)) / ((k : ℝ))) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  have hsizePos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hzero | hpositive
    · exfalso
      have hsum := D.weight_sum_one
      subst hzero
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
      exact absurd hsum (by norm_num)
    · exact hpositive
  have hsizeNe : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hsizePos.ne'
  have hrankNe : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hrank.ne'
  have hscaled : ((k : ℝ) / (m : ℝ)) • ∑ atomIndex, atomMatrix (unitAtom D atomIndex)
      = (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [Finset.smul_sum, ← D.isParseval]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [← huniform atomIndex, atomShare_smul_atomMatrix_unitAtom]
  have hratioNe : ((k : ℝ) / (m : ℝ)) ≠ 0 := div_ne_zero hrankNe hsizeNe
  rw [← hscaled, smul_smul, div_mul_div_comm, mul_comm ((m : ℝ)) ((k : ℝ)),
    div_self (mul_ne_zero hrankNe hsizeNe), one_smul]

/-- **Identity 4: the `Y`'s of an equal-share design sum to zero.**  This is the
frame law, recentred; it is what makes the abstract relaxation of section 4
carry a kernel vector. -/
theorem sum_veroneseTracelessPart_eq_zero (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ)) :
    ∑ atomIndex, veroneseTracelessPart D atomIndex = 0 := by
  have hrankNe : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hrank.ne'
  simp only [veroneseTracelessPart]
  rw [Finset.sum_sub_distrib, sum_atomMatrix_unitAtom_of_equalShare D hrank huniform,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, sub_eq_zero, div_eq_mul_inv]

/-- **The subset form of identity 4**: over a `k`-subset the `Y`'s sum to
`S_T − I`, where `S_T` is the sum of the unit direction atoms.  This is the
step that turns domination data into a Frobenius norm. -/
theorem sum_veroneseTracelessPart_subset_eq (D : WeightedDesign m k) (hrank : 0 < k)
    {selected : Finset (Fin m)} (hcard : selected.card = k) :
    ∑ atomIndex ∈ selected, veroneseTracelessPart D atomIndex
      = (∑ atomIndex ∈ selected, atomMatrix (unitAtom D atomIndex)) - 1 := by
  have hrankNe : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hrank.ne'
  simp only [veroneseTracelessPart]
  rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    mul_inv_cancel₀ hrankNe, one_smul]

/-- **The Veronese constraint, mechanized.**  `Y_c` satisfies the quadratic
`Y² = (1 − 2/k) Y + (1/k − 1/k²) I`, which is exactly the statement that
`Y_c + (1/k) I` is a rank-one projection.  At rank three:
`Y² = (1/3) Y + (2/9) I`.  Barrier B3 says any proof of the metric bound must
consume THIS; section 4 shows what happens when it is dropped. -/
theorem veroneseTracelessPart_sq (D : WeightedDesign m k)
    {atomIndex : Fin m} (hnondegenerate : 0 < leverageOf (D.atom atomIndex)) :
    veroneseTracelessPart D atomIndex * veroneseTracelessPart D atomIndex
      = (1 - 2 * ((k : ℝ))⁻¹) • veroneseTracelessPart D atomIndex
        + (((k : ℝ))⁻¹ - ((k : ℝ))⁻¹ * ((k : ℝ))⁻¹) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  have hidempotent : atomMatrix (unitAtom D atomIndex) * atomMatrix (unitAtom D atomIndex)
      = atomMatrix (unitAtom D atomIndex) := by
    rw [atomMatrix, vecMulVec_mul_vecMulVec, ← leverageOf_eq_dotProduct,
      leverageOf_unitAtom D hnondegenerate, one_smul]
  simp only [veroneseTracelessPart, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_sub, smul_smul, hidempotent]
  module

/-! ## 3. The reformulation at (7,3)

`|Y_a + Y_b + Y_c|_F² = 2 σ_T` at rank three, so the landed sigma gate becomes a
single Frobenius inequality against the per-atom norm `|Y_c|_F² = 2/3`. -/

/-- **THE METRIC IDENTITY.**  At rank three the squared Frobenius norm of a
triple's traceless sum is exactly twice the triple sigma.  Combining it with
`Gtz.sum_veroneseTracelessPart_subset_eq`: `|S_T − I|_F² = 2 σ_T`. -/
theorem frobeniusNormSq_tripleTracelessSum_eq_two_mul_tripleSigma (D : WeightedDesign m 3)
    {tripleFirst tripleSecond tripleThird : Fin m}
    (hfirst : 0 < leverageOf (D.atom tripleFirst))
    (hsecond : 0 < leverageOf (D.atom tripleSecond))
    (hthird : 0 < leverageOf (D.atom tripleThird)) :
    frobeniusNormSq (veroneseTracelessPart D tripleFirst + veroneseTracelessPart D tripleSecond
        + veroneseTracelessPart D tripleThird)
      = 2 * directionTripleSigma D tripleFirst tripleSecond tripleThird := by
  have hrank : 0 < 3 := by norm_num
  rw [frobeniusNormSq_add_add,
    frobeniusNormSq_veroneseTracelessPart D hrank hfirst,
    frobeniusNormSq_veroneseTracelessPart D hrank hsecond,
    frobeniusNormSq_veroneseTracelessPart D hrank hthird,
    frobeniusInner_veroneseTracelessPart D hrank hfirst hsecond,
    frobeniusInner_veroneseTracelessPart D hrank hfirst hthird,
    frobeniusInner_veroneseTracelessPart D hrank hsecond hthird,
    directionTripleSigma]
  norm_num
  ring

/-- **The sigma gate, restated metrically.**  On the (7,3) equal-share stratum a
triple whose traceless sum has squared Frobenius norm at most `2/3` — the norm of
a SINGLE `Y_c` — dominates.  No signs, no triangle product, no projections. -/
theorem dominates_triple_of_frobeniusNormSq_le_two_thirds (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {tripleFirst tripleSecond tripleThird : Fin 7}
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird)
    (hbound : frobeniusNormSq (veroneseTracelessPart D tripleFirst
        + veroneseTracelessPart D tripleSecond + veroneseTracelessPart D tripleThird)
      ≤ 2 / 3) :
    Dominates D {tripleFirst, tripleSecond, tripleThird} := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex => by
    rw [hleverage atomIndex]; norm_num
  rw [frobeniusNormSq_tripleTracelessSum_eq_two_mul_tripleSigma D (hpositive tripleFirst)
    (hpositive tripleSecond) (hpositive tripleThird)] at hbound
  exact dominates_triple_of_tripleSigma_le_third_bandSeven D huniform hleverage hfirstSecond
    hfirstThird hsecondThird (by linarith)

/-- **THE METRIC FRONTIER STATEMENT.**  One Frobenius inequality per design: some
triple's traceless sum is no longer than a single traceless part.  This is the
residual R-A of the campaign, packaged; nothing in this module proves it. -/
def MetricTripleBoundSevenThree : Prop :=
  ∀ D : WeightedDesign 7 3, (∀ atomIndex, atomShare D atomIndex = 3 / 7) →
    (∀ atomIndex, leverageOf (D.atom atomIndex) = 3) →
      ∃ tripleFirst tripleSecond tripleThird : Fin 7,
        tripleFirst ≠ tripleSecond ∧ tripleFirst ≠ tripleThird ∧ tripleSecond ≠ tripleThird ∧
          frobeniusNormSq (veroneseTracelessPart D tripleFirst
            + veroneseTracelessPart D tripleSecond + veroneseTracelessPart D tripleThird)
            ≤ 2 / 3

/-- Weighted GTZ restricted to the (7,3) equal-share stratum: weights `1/7`,
leverages `3`.  This is the cell the whole middle-band layer works in. -/
def GtzWeightedEqualShareSevenThree : Prop :=
  ∀ D : WeightedDesign 7 3, (∀ atomIndex, atomShare D atomIndex = 3 / 7) →
    (∀ atomIndex, leverageOf (D.atom atomIndex) = 3) →
      ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C

/-- **The metric bound closes the equal-share cell.**  What it does NOT close is
the passage from a general (7,3) design to the equal-share stratum: no such
reduction is landed anywhere in the tree, and it is exactly the
"uniform-share / leverage pinning" residual named in the campaign's chain.  So
this is the honest strength of the reformulation — the cell, not the conjecture. -/
theorem gtzWeightedEqualShareSevenThree_of_metricTripleBound
    (hmetric : MetricTripleBoundSevenThree) : GtzWeightedEqualShareSevenThree := by
  intro D huniform hleverage
  obtain ⟨tripleFirst, tripleSecond, tripleThird, hfirstSecond, hfirstThird, hsecondThird,
    hbound⟩ := hmetric D huniform hleverage
  refine ⟨{tripleFirst, tripleSecond, tripleThird}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
      Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]
  · exact dominates_triple_of_frobeniusNormSq_le_two_thirds D huniform hleverage hfirstSecond
      hfirstThird hsecondThird hbound

/-! ## 4. The exact extremal: a parallel pair plus a pentagon on a cone

The numerically identified worst case, reconstructed in closed form.  Two atoms
along the cone axis and five on the cone of half-angle `arccos (1/√15)`, at the
five fifth-roots of unity.  Everything below is exact in `ℚ(√5)`. -/

/-- `cos (2π/5)`, the pentagon's side cosine. -/
noncomputable def pentagonSideCosine : ℝ := (Real.sqrt 5 - 1) / 4

/-- `cos (4π/5)`, the pentagon's diagonal cosine. -/
noncomputable def pentagonDiagonalCosine : ℝ := -(Real.sqrt 5 + 1) / 4

/-- `sin (2π/5)`, taken as the positive root of `1 − cos²`; its nested-radical form
is never needed, only its square and its product with the diagonal sine. -/
noncomputable def pentagonSideSine : ℝ := Real.sqrt (1 - pentagonSideCosine ^ 2)

/-- `sin (4π/5)`, likewise. -/
noncomputable def pentagonDiagonalSine : ℝ := Real.sqrt (1 - pentagonDiagonalCosine ^ 2)

/-- The pentagon atoms' height along the cone axis, at leverage three:
`√(1/5)`.  Its square is `1/5`, and the cone half-angle it encodes has
`cos² = (1/5)/3 = 1/15`. -/
noncomputable def coneAxisHeight : ℝ := Real.sqrt (1 / 5)

/-- The pentagon atoms' radius in the plane orthogonal to the cone axis, at
leverage three: `√(14/5)`. -/
noncomputable def conePlaneRadius : ℝ := Real.sqrt (14 / 5)

theorem rootFive_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem rootThree_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem coneAxisHeight_sq : coneAxisHeight ^ 2 = 1 / 5 := Real.sq_sqrt (by norm_num)

theorem conePlaneRadius_sq : conePlaneRadius ^ 2 = 14 / 5 := Real.sq_sqrt (by norm_num)

theorem pentagonSideCosine_sq : pentagonSideCosine ^ 2 = (3 - Real.sqrt 5) / 8 := by
  rw [pentagonSideCosine]
  field_simp
  linear_combination (8 : ℝ) * rootFive_sq

theorem pentagonDiagonalCosine_sq : pentagonDiagonalCosine ^ 2 = (3 + Real.sqrt 5) / 8 := by
  rw [pentagonDiagonalCosine]
  field_simp
  linear_combination (8 : ℝ) * rootFive_sq

theorem rootFive_lt_three : Real.sqrt 5 < 3 := by
  nlinarith [rootFive_sq, Real.sqrt_nonneg 5]

theorem pentagonSideSine_sq : pentagonSideSine ^ 2 = (5 + Real.sqrt 5) / 8 := by
  rw [pentagonSideSine, Real.sq_sqrt (by
      rw [pentagonSideCosine_sq]; nlinarith [rootFive_lt_three, Real.sqrt_nonneg 5]),
    pentagonSideCosine_sq]
  ring

theorem pentagonDiagonalSine_sq : pentagonDiagonalSine ^ 2 = (5 - Real.sqrt 5) / 8 := by
  rw [pentagonDiagonalSine, Real.sq_sqrt (by
      rw [pentagonDiagonalCosine_sq]; nlinarith [rootFive_lt_three, Real.sqrt_nonneg 5]),
    pentagonDiagonalCosine_sq]
  ring

/-- The one product identity the pentagon needs: `sin(2π/5) sin(4π/5) = √5/4`.
It is what keeps every nested radical out of the edge-weight table. -/
theorem pentagonSine_mul : pentagonSideSine * pentagonDiagonalSine = Real.sqrt 5 / 4 := by
  rw [pentagonSideSine, pentagonDiagonalSine, ← Real.sqrt_mul (by
      rw [pentagonSideCosine_sq]; nlinarith [rootFive_lt_three, Real.sqrt_nonneg 5])]
  have hproduct : (1 - pentagonSideCosine ^ 2) * (1 - pentagonDiagonalCosine ^ 2)
      = (Real.sqrt 5 / 4) ^ 2 := by
    rw [pentagonSideCosine_sq, pentagonDiagonalCosine_sq, div_pow]
    linear_combination (-5 / 64 : ℝ) * rootFive_sq
  rw [hproduct, Real.sqrt_sq (by positivity)]

/-- **The extremal's seven atoms**, at leverage three throughout: indices `0, 1`
are the parallel pair on the cone axis, indices `2..6` the pentagon in cyclic
order. -/
noncomputable def pentagonPairAtom : Fin 7 → Fin 3 → ℝ :=
  ![ ![0, 0, Real.sqrt 3],
     ![0, 0, Real.sqrt 3],
     ![conePlaneRadius, 0, coneAxisHeight],
     ![conePlaneRadius * pentagonSideCosine, conePlaneRadius * pentagonSideSine, coneAxisHeight],
     ![conePlaneRadius * pentagonDiagonalCosine, conePlaneRadius * pentagonDiagonalSine,
       coneAxisHeight],
     ![conePlaneRadius * pentagonDiagonalCosine, -(conePlaneRadius * pentagonDiagonalSine),
       coneAxisHeight],
     ![conePlaneRadius * pentagonSideCosine, -(conePlaneRadius * pentagonSideSine),
       coneAxisHeight] ]

theorem leverageOf_pentagonPairAtom (atomIndex : Fin 7) :
    leverageOf (pentagonPairAtom atomIndex) = 3 := by
  fin_cases atomIndex <;>
    simp [leverageOf, pentagonPairAtom, Fin.sum_univ_three]
  · linear_combination conePlaneRadius_sq + coneAxisHeight_sq
  · linear_combination (pentagonSideCosine ^ 2 + pentagonSideSine ^ 2) * conePlaneRadius_sq
      + (14 / 5 : ℝ) * pentagonSideCosine_sq + (14 / 5 : ℝ) * pentagonSideSine_sq
      + coneAxisHeight_sq
  · linear_combination (pentagonDiagonalCosine ^ 2 + pentagonDiagonalSine ^ 2) * conePlaneRadius_sq
      + (14 / 5 : ℝ) * pentagonDiagonalCosine_sq + (14 / 5 : ℝ) * pentagonDiagonalSine_sq
      + coneAxisHeight_sq
  · linear_combination (pentagonDiagonalCosine ^ 2 + pentagonDiagonalSine ^ 2) * conePlaneRadius_sq
      + (14 / 5 : ℝ) * pentagonDiagonalCosine_sq + (14 / 5 : ℝ) * pentagonDiagonalSine_sq
      + coneAxisHeight_sq
  · linear_combination (pentagonSideCosine ^ 2 + pentagonSideSine ^ 2) * conePlaneRadius_sq
      + (14 / 5 : ℝ) * pentagonSideCosine_sq + (14 / 5 : ℝ) * pentagonSideSine_sq
      + coneAxisHeight_sq

/-- **The frame law of the extremal**: the seven atoms resolve `7 I`, so the
uniform weight `1/7` makes them a Parseval design.  Diagonal: `A²·5/2 = 7` in the
cone plane and `3 + 3 + 5 B² = 7` along the axis; off-diagonal: the pentagon's
fifth-root sums vanish. -/
theorem sum_atomMatrix_pentagonPairAtom :
    ∑ atomIndex, atomMatrix (pentagonPairAtom atomIndex)
      = (7 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowIndex colIndex
  rw [Matrix.sum_apply, Fin.sum_univ_seven]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [atomMatrix, Matrix.vecMulVec_apply, pentagonPairAtom]
  · linear_combination (1 + 2 * pentagonSideCosine ^ 2 + 2 * pentagonDiagonalCosine ^ 2)
      * conePlaneRadius_sq + (28 / 5 : ℝ) * pentagonSideCosine_sq
      + (28 / 5 : ℝ) * pentagonDiagonalCosine_sq
  · rw [pentagonSideCosine, pentagonDiagonalCosine]; ring
  · linear_combination (2 * pentagonSideSine ^ 2 + 2 * pentagonDiagonalSine ^ 2)
      * conePlaneRadius_sq + (28 / 5 : ℝ) * pentagonSideSine_sq
      + (28 / 5 : ℝ) * pentagonDiagonalSine_sq
  · rw [pentagonSideCosine, pentagonDiagonalCosine]; ring
  · linear_combination (5 : ℝ) * coneAxisHeight_sq

/-- **THE EXTREMAL DESIGN.**  A `WeightedDesign 7 3` on the equal-share stratum:
every weight `1/7`, every leverage `3`. -/
noncomputable def pentagonPairDesign : WeightedDesign 7 3 where
  atom := pentagonPairAtom
  weight := fun _ => 1 / 7
  weight_pos := fun _ => by norm_num
  weight_sum_one := by simp
  isParseval := by
    rw [← Finset.smul_sum, sum_atomMatrix_pentagonPairAtom, smul_smul]
    norm_num

theorem pentagonPairDesign_leverage (atomIndex : Fin 7) :
    leverageOf (pentagonPairDesign.atom atomIndex) = 3 :=
  leverageOf_pentagonPairAtom atomIndex

theorem pentagonPairDesign_atomShare (atomIndex : Fin 7) :
    atomShare pentagonPairDesign atomIndex = 3 / 7 := by
  rw [atomShare, pentagonPairDesign_leverage]
  norm_num [pentagonPairDesign]

/-- **The extremal sits on the merge boundary**: atoms `0` and `1` are literally
equal, so `Gtz.dominating_of_parallel_pair` discharges this design with no
quantitative hypothesis at all. -/
theorem hasParallelPair_pentagonPairDesign : HasParallelPair pentagonPairDesign :=
  ⟨0, 1, 1, by decide, by
    funext coordIndex
    fin_cases coordIndex <;> simp [pentagonPairDesign, pentagonPairAtom]⟩

/-! ### The exact edge-weight table

Three distinct off-diagonal pairings: `3` for the parallel pair, `√3·√(1/5)`
for the ten axis-to-pentagon edges, `(7√5 − 5)/10` for the five pentagon sides
and `−(7√5 + 5)/10` for the five pentagon diagonals. -/

noncomputable def axisPentagonPairing : ℝ := Real.sqrt 3 * coneAxisHeight

noncomputable def pentagonSidePairing : ℝ := (7 * Real.sqrt 5 - 5) / 10

noncomputable def pentagonDiagonalPairing : ℝ := -(7 * Real.sqrt 5 + 5) / 10

/-- The full `7×7` pairing table of the extremal's atoms. -/
noncomputable def pentagonPairPairing : Matrix (Fin 7) (Fin 7) ℝ :=
  !![3, 3, axisPentagonPairing, axisPentagonPairing, axisPentagonPairing,
       axisPentagonPairing, axisPentagonPairing;
     3, 3, axisPentagonPairing, axisPentagonPairing, axisPentagonPairing,
       axisPentagonPairing, axisPentagonPairing;
     axisPentagonPairing, axisPentagonPairing, 3, pentagonSidePairing,
       pentagonDiagonalPairing, pentagonDiagonalPairing, pentagonSidePairing;
     axisPentagonPairing, axisPentagonPairing, pentagonSidePairing, 3,
       pentagonSidePairing, pentagonDiagonalPairing, pentagonDiagonalPairing;
     axisPentagonPairing, axisPentagonPairing, pentagonDiagonalPairing,
       pentagonSidePairing, 3, pentagonSidePairing, pentagonDiagonalPairing;
     axisPentagonPairing, axisPentagonPairing, pentagonDiagonalPairing,
       pentagonDiagonalPairing, pentagonSidePairing, 3, pentagonSidePairing;
     axisPentagonPairing, axisPentagonPairing, pentagonSidePairing,
       pentagonDiagonalPairing, pentagonDiagonalPairing, pentagonSidePairing, 3]

/-- **The pairing table is exact.**  Forty-nine entries, eleven distinct algebraic
shapes; every one closes by a hand-multiplier `linear_combination` against the
seven defining square relations. -/
theorem dotProduct_pentagonPairAtom (firstIndex secondIndex : Fin 7) :
    pentagonPairAtom firstIndex ⬝ᵥ pentagonPairAtom secondIndex
      = pentagonPairPairing firstIndex secondIndex := by
  fin_cases firstIndex <;> fin_cases secondIndex <;>
    simp [pentagonPairAtom, pentagonPairPairing, dotProduct, Fin.sum_univ_three,
      axisPentagonPairing, pentagonSidePairing, pentagonDiagonalPairing,
      pentagonSideCosine, pentagonDiagonalCosine]
  all_goals
    first
      | ring1
      | linear_combination rootThree_sq
      | linear_combination conePlaneRadius_sq + coneAxisHeight_sq
      | linear_combination ((Real.sqrt 5 - 1) / 4) * conePlaneRadius_sq + coneAxisHeight_sq
      | linear_combination (-(Real.sqrt 5 + 1) / 4) * conePlaneRadius_sq + coneAxisHeight_sq
      | linear_combination ((Real.sqrt 5 - 1) / 4 * (-(Real.sqrt 5 + 1) / 4)
            + pentagonSideSine * pentagonDiagonalSine) * conePlaneRadius_sq
          + coneAxisHeight_sq + (14 / 5 : ℝ) * pentagonSine_mul
          + (-7 / 40 : ℝ) * rootFive_sq
      | linear_combination ((Real.sqrt 5 - 1) / 4 * (-(Real.sqrt 5 + 1) / 4)
            - pentagonSideSine * pentagonDiagonalSine) * conePlaneRadius_sq
          + coneAxisHeight_sq + (-14 / 5 : ℝ) * pentagonSine_mul
          + (-7 / 40 : ℝ) * rootFive_sq
      | linear_combination ((-(Real.sqrt 5 + 1) / 4) ^ 2 - pentagonDiagonalSine ^ 2)
            * conePlaneRadius_sq + coneAxisHeight_sq
          + (-14 / 5 : ℝ) * pentagonDiagonalSine_sq + (7 / 40 : ℝ) * rootFive_sq
      | linear_combination (((Real.sqrt 5 - 1) / 4) ^ 2 - pentagonSideSine ^ 2)
            * conePlaneRadius_sq + coneAxisHeight_sq
          + (-14 / 5 : ℝ) * pentagonSideSine_sq + (7 / 40 : ℝ) * rootFive_sq
      | linear_combination (((Real.sqrt 5 - 1) / 4) ^ 2 + pentagonSideSine ^ 2)
            * conePlaneRadius_sq + (14 / 5 : ℝ) * pentagonSideSine_sq + coneAxisHeight_sq
          + (7 / 40 : ℝ) * rootFive_sq
      | linear_combination ((-(Real.sqrt 5 + 1) / 4) ^ 2 + pentagonDiagonalSine ^ 2)
            * conePlaneRadius_sq + (14 / 5 : ℝ) * pentagonDiagonalSine_sq + coneAxisHeight_sq
          + (7 / 40 : ℝ) * rootFive_sq

theorem directionGram_pentagonPairDesign (firstIndex secondIndex : Fin 7) :
    directionGram pentagonPairDesign firstIndex secondIndex
      = pentagonPairPairing firstIndex secondIndex / 3 := by
  have hinverse : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = 1 / 3 := by
    rw [← mul_inv, ← pow_two, rootThree_sq]
    norm_num
  rw [directionGram_eq_scaled_atomPairing, pentagonPairDesign_leverage,
    pentagonPairDesign_leverage]
  show (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹
      * (pentagonPairAtom firstIndex ⬝ᵥ pentagonPairAtom secondIndex) = _
  rw [hinverse, dotProduct_pentagonPairAtom]
  ring

/-- The integer numerator of every edge weight, over the common denominator `90`.
The diagonal carries the true value `1 = 90/90`, so the table is unconditional. -/
def pentagonPairEdgeNumerator : Matrix (Fin 7) (Fin 7) ℤ :=
  !![90, 90,  6,  6,  6,  6,  6;
     90, 90,  6,  6,  6,  6,  6;
      6,  6, 90, 27, 27, 27, 27;
      6,  6, 27, 90, 27, 27, 27;
      6,  6, 27, 27, 90, 27, 27;
      6,  6, 27, 27, 27, 90, 27;
      6,  6, 27, 27, 27, 27, 90]

/-- The integer coefficient of `√5` in every edge weight, over the denominator
`90`: `−7` on the five pentagon sides, `+7` on the five diagonals, `0` elsewhere. -/
def pentagonPairEdgeRootCoefficient : Matrix (Fin 7) (Fin 7) ℤ :=
  !![0, 0,  0,  0,  0,  0,  0;
     0, 0,  0,  0,  0,  0,  0;
     0, 0,  0, -7,  7,  7, -7;
     0, 0, -7,  0, -7,  7,  7;
     0, 0,  7, -7,  0, -7,  7;
     0, 0,  7,  7, -7,  0, -7;
     0, 0, -7,  7,  7, -7,  0]

/-- **THE EXACT EDGE-WEIGHT TABLE.**  Every one of the twenty-one edges is
`(P + Q√5)/90` with `P ∈ {90, 6, 27}` and `Q ∈ {0, ±7}`: the parallel pair at
`1`, the ten axis-to-pentagon edges at `1/15`, the five pentagon sides at
`(27 − 7√5)/90` and the five diagonals at `(27 + 7√5)/90`. -/
theorem edgeWeight_pentagonPairDesign (firstIndex secondIndex : Fin 7) :
    edgeWeight pentagonPairDesign firstIndex secondIndex
      = (((pentagonPairEdgeNumerator firstIndex secondIndex : ℝ))
          + ((pentagonPairEdgeRootCoefficient firstIndex secondIndex : ℝ)) * Real.sqrt 5) / 90 := by
  rw [edgeWeight, directionGram_pentagonPairDesign]
  fin_cases firstIndex <;> fin_cases secondIndex <;>
    simp [pentagonPairPairing, pentagonPairEdgeNumerator, pentagonPairEdgeRootCoefficient,
      axisPentagonPairing, pentagonSidePairing, pentagonDiagonalPairing]
  all_goals
    first
      | (norm_num; done)
      | linear_combination (coneAxisHeight ^ 2 / 9) * rootThree_sq
          + (1 / 3 : ℝ) * coneAxisHeight_sq
      | linear_combination (49 / 900 : ℝ) * rootFive_sq

/-- **The integer shadow of the thirty-five triples.**  For every triple of
distinct atoms the numerator sum is at least `39` and the `√5`-coefficient sum is
at least `−7`, both attained simultaneously exactly on "one axis atom plus two
adjacent pentagon atoms".  Decided over `ℤ`, so no axioms at all. -/
theorem pentagonPairEdge_triple_shadow (firstIndex secondIndex thirdIndex : Fin 7)
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex) :
    39 ≤ pentagonPairEdgeNumerator firstIndex secondIndex
        + pentagonPairEdgeNumerator firstIndex thirdIndex
        + pentagonPairEdgeNumerator secondIndex thirdIndex
      ∧ -7 ≤ pentagonPairEdgeRootCoefficient firstIndex secondIndex
        + pentagonPairEdgeRootCoefficient firstIndex thirdIndex
        + pentagonPairEdgeRootCoefficient secondIndex thirdIndex := by
  revert hfirstSecond hfirstThird hsecondThird
  revert firstIndex secondIndex thirdIndex
  decide

/-- **The row law of the extremal, from the table.**  Every row of the edge-weight
table sums to `7/3` — including the diagonal `1`, so the off-diagonal mass is
`4/3`.  This is exactly what Parseval at uniform share forces, so it is an
independent consistency check on the twenty-one exact values. -/
theorem sum_edgeWeight_pentagonPairDesign (atomIndex : Fin 7) :
    ∑ otherIndex, edgeWeight pentagonPairDesign atomIndex otherIndex = 7 / 3 := by
  rw [Fin.sum_univ_seven]
  fin_cases atomIndex <;>
    simp [edgeWeight_pentagonPairDesign, pentagonPairEdgeNumerator,
      pentagonPairEdgeRootCoefficient] <;>
    ring

theorem directionTripleSigma_eq_sum_edgeWeight (D : WeightedDesign m k)
    (tripleFirst tripleSecond tripleThird : Fin m) :
    directionTripleSigma D tripleFirst tripleSecond tripleThird
      = edgeWeight D tripleFirst tripleSecond + edgeWeight D tripleFirst tripleThird
        + edgeWeight D tripleSecond tripleThird := rfl

/-- Reading one entry of the exact table at named integers. -/
theorem edgeWeight_pentagonPairDesign_entry (firstIndex secondIndex : Fin 7)
    (numerator rootCoefficient : ℤ)
    (hnumerator : pentagonPairEdgeNumerator firstIndex secondIndex = numerator)
    (hrootCoefficient : pentagonPairEdgeRootCoefficient firstIndex secondIndex = rootCoefficient) :
    edgeWeight pentagonPairDesign firstIndex secondIndex
      = ((numerator : ℝ) + (rootCoefficient : ℝ) * Real.sqrt 5) / 90 := by
  rw [edgeWeight_pentagonPairDesign, hnumerator, hrootCoefficient]

/-- **THE EXTREMAL VALUE IS ATTAINED.**  The triple "axis atom `0` plus the two
adjacent pentagon atoms `2, 3`" has `σ_T = (39 − 7√5)/90` exactly — the value the
optimizer reported to seven digits. -/
theorem directionTripleSigma_pentagonPairDesign_extremal :
    directionTripleSigma pentagonPairDesign 0 2 3 = (39 - 7 * Real.sqrt 5) / 90 := by
  rw [directionTripleSigma_eq_sum_edgeWeight,
    edgeWeight_pentagonPairDesign_entry 0 2 6 0 (by decide) (by decide),
    edgeWeight_pentagonPairDesign_entry 0 3 6 0 (by decide) (by decide),
    edgeWeight_pentagonPairDesign_entry 2 3 27 (-7) (by decide) (by decide)]
  push_cast
  ring

/-- **THE EXTREMAL VALUE IS THE MINIMUM.**  Every one of the thirty-five triples
carries `σ_T ≥ (39 − 7√5)/90`.  Engine: the integer shadow of the edge table plus
`√5 ≥ 0` — no numeric bound on `√5` is needed, because the numerator sum and the
`√5`-coefficient sum are separately bounded. -/
theorem directionTripleSigma_pentagonPairDesign_ge (tripleFirst tripleSecond tripleThird : Fin 7)
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird) :
    (39 - 7 * Real.sqrt 5) / 90
      ≤ directionTripleSigma pentagonPairDesign tripleFirst tripleSecond tripleThird := by
  obtain ⟨hnumerator, hrootCoefficient⟩ :=
    pentagonPairEdge_triple_shadow tripleFirst tripleSecond tripleThird hfirstSecond hfirstThird
      hsecondThird
  have hnumeratorReal : (39 : ℝ)
      ≤ ((pentagonPairEdgeNumerator tripleFirst tripleSecond : ℝ))
        + ((pentagonPairEdgeNumerator tripleFirst tripleThird : ℝ))
        + ((pentagonPairEdgeNumerator tripleSecond tripleThird : ℝ)) := by
    exact_mod_cast hnumerator
  have hrootReal : (-7 : ℝ)
      ≤ ((pentagonPairEdgeRootCoefficient tripleFirst tripleSecond : ℝ))
        + ((pentagonPairEdgeRootCoefficient tripleFirst tripleThird : ℝ))
        + ((pentagonPairEdgeRootCoefficient tripleSecond tripleThird : ℝ)) := by
    exact_mod_cast hrootCoefficient
  have hproduct : 0 ≤ (((pentagonPairEdgeRootCoefficient tripleFirst tripleSecond : ℝ))
      + ((pentagonPairEdgeRootCoefficient tripleFirst tripleThird : ℝ))
      + ((pentagonPairEdgeRootCoefficient tripleSecond tripleThird : ℝ)) + 7)
      * Real.sqrt 5 :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg 5)
  rw [directionTripleSigma_eq_sum_edgeWeight, edgeWeight_pentagonPairDesign,
    edgeWeight_pentagonPairDesign, edgeWeight_pentagonPairDesign]
  nlinarith [hproduct, hnumeratorReal, Real.sqrt_nonneg 5]

/-- The minimum is exactly `(39 − 7√5)/90`, packaged as an `IsLeast`. -/
theorem pentagonPairDesign_min_tripleSigma :
    IsLeast {sigmaValue : ℝ | ∃ tripleFirst tripleSecond tripleThird : Fin 7,
        tripleFirst ≠ tripleSecond ∧ tripleFirst ≠ tripleThird ∧ tripleSecond ≠ tripleThird ∧
          directionTripleSigma pentagonPairDesign tripleFirst tripleSecond tripleThird
            = sigmaValue}
      ((39 - 7 * Real.sqrt 5) / 90) := by
  refine ⟨⟨0, 2, 3, by decide, by decide, by decide,
    directionTripleSigma_pentagonPairDesign_extremal⟩, ?_⟩
  rintro sigmaValue ⟨tripleFirst, tripleSecond, tripleThird, hfirstSecond, hfirstThird,
    hsecondThird, hvalue⟩
  rw [← hvalue]
  exact directionTripleSigma_pentagonPairDesign_ge tripleFirst tripleSecond tripleThird
    hfirstSecond hfirstThird hsecondThird

theorem nine_lt_seven_mul_rootFive : (9 : ℝ) < 7 * Real.sqrt 5 := by
  nlinarith [rootFive_sq, Real.sqrt_nonneg 5]

/-- **THE MARGIN IS EXACTLY `(7√5 − 9)/90`, AND IT IS POSITIVE.**  So the sigma
gate's threshold `1/3` strictly clears the extremal: the numerically identified
worst case is NOT a counterexample to the sigma-gate route, and the route retains
`(7√5 − 9)/90 = 0.0739…` of room. -/
theorem pentagonPairDesign_tripleSigma_margin :
    1 / 3 - (39 - 7 * Real.sqrt 5) / 90 = (7 * Real.sqrt 5 - 9) / 90
      ∧ 0 < (7 * Real.sqrt 5 - 9) / 90 :=
  ⟨by ring, by
    have hlower := nine_lt_seven_mul_rootFive
    positivity⟩

/-- **The extremal is dominated.**  Its minimising triple passes the sigma gate,
so the design that the optimizer identified as the hardest equal-share (7,3)
configuration in fact has a dominating triple, exhibited. -/
theorem dominates_pentagonPairDesign_extremalTriple :
    Dominates pentagonPairDesign {0, 2, 3} := by
  refine dominates_triple_of_tripleSigma_le_third_bandSeven pentagonPairDesign
    pentagonPairDesign_atomShare pentagonPairDesign_leverage (by decide) (by decide) (by decide) ?_
  rw [directionTripleSigma_pentagonPairDesign_extremal]
  have hlower := nine_lt_seven_mul_rootFive
  linarith

/-- **SHARPNESS OF THE SIGMA CONSTANT.**  Any theorem of the shape "every
equal-share (7,3) design has a triple with `σ_T ≤ level`" forces
`level ≥ (39 − 7√5)/90`.  The sigma gate uses `level = 1/3`, so the gate is not
merely sufficient but within `(7√5 − 9)/90` of the best possible threshold on
this stratum. -/
theorem le_level_of_forall_exists_tripleSigma_le {level : ℝ}
    (hlevel : ∀ D : WeightedDesign 7 3, (∀ atomIndex, atomShare D atomIndex = 3 / 7) →
      (∀ atomIndex, leverageOf (D.atom atomIndex) = 3) →
        ∃ tripleFirst tripleSecond tripleThird : Fin 7,
          tripleFirst ≠ tripleSecond ∧ tripleFirst ≠ tripleThird ∧ tripleSecond ≠ tripleThird ∧
            directionTripleSigma D tripleFirst tripleSecond tripleThird ≤ level) :
    (39 - 7 * Real.sqrt 5) / 90 ≤ level := by
  obtain ⟨tripleFirst, tripleSecond, tripleThird, hfirstSecond, hfirstThird, hsecondThird,
    hsigma⟩ := hlevel pentagonPairDesign pentagonPairDesign_atomShare pentagonPairDesign_leverage
  exact le_trans (directionTripleSigma_pentagonPairDesign_ge tripleFirst tripleSecond tripleThird
    hfirstSecond hfirstThird hsecondThird) hsigma

/-- **SHARPNESS OF THE METRIC CONSTANT.**  In Frobenius coordinates the same
statement reads: the target `2/3` of `Gtz.MetricTripleBoundSevenThree` cannot be
lowered below `(39 − 7√5)/45 = 0.5188…`.  The gap between that and `2/3` is the
entire slack the metric route has. -/
theorem le_level_of_forall_exists_frobeniusNormSq_le {level : ℝ}
    (hlevel : ∀ D : WeightedDesign 7 3, (∀ atomIndex, atomShare D atomIndex = 3 / 7) →
      (∀ atomIndex, leverageOf (D.atom atomIndex) = 3) →
        ∃ tripleFirst tripleSecond tripleThird : Fin 7,
          tripleFirst ≠ tripleSecond ∧ tripleFirst ≠ tripleThird ∧ tripleSecond ≠ tripleThird ∧
            frobeniusNormSq (veroneseTracelessPart D tripleFirst
              + veroneseTracelessPart D tripleSecond + veroneseTracelessPart D tripleThird)
              ≤ level) :
    (39 - 7 * Real.sqrt 5) / 45 ≤ level := by
  obtain ⟨tripleFirst, tripleSecond, tripleThird, hfirstSecond, hfirstThird, hsecondThird,
    hnorm⟩ := hlevel pentagonPairDesign pentagonPairDesign_atomShare pentagonPairDesign_leverage
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (pentagonPairDesign.atom atomIndex) :=
    fun atomIndex => by rw [pentagonPairDesign_leverage]; norm_num
  rw [frobeniusNormSq_tripleTracelessSum_eq_two_mul_tripleSigma pentagonPairDesign
    (hpositive tripleFirst) (hpositive tripleSecond) (hpositive tripleThird)] at hnorm
  have hsigma := directionTripleSigma_pentagonPairDesign_ge tripleFirst tripleSecond tripleThird
    hfirstSecond hfirstThird hsecondThird
  linarith

/-! ## 5. The Veronese no-go

The metric statement, relaxed to what the Gram matrix of the `Y`'s alone can see,
is FALSE — and the relaxation's own optimum sits exactly at the averaging
ceiling `σ = 2/3`.  Then the Veronese rank bound, which proves the refuting
witness is not realizable, so the whole gap is rank-one content. -/

theorem frobeniusInner_sum_right {indexType : Type} [Fintype indexType]
    (leftMatrix : Matrix (Fin k) (Fin k) ℝ) (family : indexType → Matrix (Fin k) (Fin k) ℝ) :
    frobeniusInner leftMatrix (∑ index, family index)
      = ∑ index, frobeniusInner leftMatrix (family index) := by
  have hswap : ∀ rowIndex : Fin k,
      ∑ colIndex, ∑ index, leftMatrix rowIndex colIndex * family index rowIndex colIndex
        = ∑ index, ∑ colIndex, leftMatrix rowIndex colIndex * family index rowIndex colIndex :=
    fun _ => Finset.sum_comm
  simp only [frobeniusInner, Matrix.sum_apply, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun rowIndex _ => hswap rowIndex, Finset.sum_comm]

/-- The rows of the `Y`'s, flattened over coordinate pairs — the factorisation
that makes the `Y`-Gram positive semidefinite by construction. -/
noncomputable def veroneseTracelessRows (D : WeightedDesign m k) :
    Matrix (Fin m) (Fin k × Fin k) ℝ :=
  Matrix.of fun atomIndex coordPair =>
    veroneseTracelessPart D atomIndex coordPair.1 coordPair.2

/-- **The `Y`-Gram**: entry `(c,d)` is `⟨Y_c, Y_d⟩_F`, equivalently `γ_cd² − 1/k`
by `frobeniusInner_veroneseTracelessPart`. -/
noncomputable def veroneseGram (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun firstIndex secondIndex =>
    frobeniusInner (veroneseTracelessPart D firstIndex) (veroneseTracelessPart D secondIndex)

theorem posSemidef_veroneseGram (D : WeightedDesign m k) : (veroneseGram D).PosSemidef := by
  have hfactor : veroneseGram D
      = (veroneseTracelessRows D)ᵀᴴ * (veroneseTracelessRows D)ᵀ := by
    ext firstIndex secondIndex
    simp only [veroneseGram, Matrix.of_apply, frobeniusInner, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, veroneseTracelessRows, star_trivial,
      Fintype.sum_prod_type]
  rw [hfactor]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem veroneseGram_diag (D : WeightedDesign m k) (hrank : 0 < k) {atomIndex : Fin m}
    (hnondegenerate : 0 < leverageOf (D.atom atomIndex)) :
    veroneseGram D atomIndex atomIndex = 1 - ((k : ℝ))⁻¹ :=
  frobeniusNormSq_veroneseTracelessPart D hrank hnondegenerate

/-- **The `Y`-Gram is annihilated by the all-ones vector** on the equal-share
stratum: each row sums to zero.  This is the exact shadow of `Σ_c Y_c = 0`. -/
theorem sum_veroneseGram_row (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ))
    (atomIndex : Fin m) :
    ∑ otherIndex, veroneseGram D atomIndex otherIndex = 0 := by
  have hexpand : ∑ otherIndex, veroneseGram D atomIndex otherIndex
      = frobeniusInner (veroneseTracelessPart D atomIndex)
        (∑ otherIndex, veroneseTracelessPart D otherIndex) := by
    rw [frobeniusInner_sum_right]
    rfl
  rw [hexpand, sum_veroneseTracelessPart_eq_zero D hrank huniform]
  simp only [frobeniusInner, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]

/-- **THE ABSTRACT RELAXATION.**  Every property of the `Y`-Gram that a
conservation, averaging or spectral argument can use is one of these three:
positive semidefiniteness, the constant diagonal `2/3`, and the vanishing row
sums.  This is the metric frontier statement with the rank-one structure
FORGOTTEN. -/
def AbstractMetricTripleBoundSevenThree : Prop :=
  ∀ gramCandidate : Matrix (Fin 7) (Fin 7) ℝ, gramCandidate.PosSemidef →
    (∀ atomIndex, gramCandidate atomIndex atomIndex = 2 / 3) →
    (∀ atomIndex, ∑ otherIndex, gramCandidate atomIndex otherIndex = 0) →
      ∃ tripleFirst tripleSecond tripleThird : Fin 7,
        tripleFirst ≠ tripleSecond ∧ tripleFirst ≠ tripleThird ∧ tripleSecond ≠ tripleThird ∧
          gramCandidate tripleFirst tripleFirst + gramCandidate tripleSecond tripleSecond
              + gramCandidate tripleThird tripleThird
            + 2 * gramCandidate tripleFirst tripleSecond
            + 2 * gramCandidate tripleFirst tripleThird
            + 2 * gramCandidate tripleSecond tripleThird ≤ 2 / 3

/-- **The relaxation really does imply the metric bound**, so refuting it refutes
a whole class of routes rather than a straw man. -/
theorem metricTripleBoundSevenThree_of_abstract
    (habstract : AbstractMetricTripleBoundSevenThree) : MetricTripleBoundSevenThree := by
  intro D huniform hleverage
  have hrank : 0 < 3 := by norm_num
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex => by
    rw [hleverage atomIndex]; norm_num
  have hshare : ∀ atomIndex, atomShare D atomIndex = ((3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ) := by
    intro atomIndex
    rw [huniform atomIndex]
    norm_num
  obtain ⟨tripleFirst, tripleSecond, tripleThird, hfirstSecond, hfirstThird, hsecondThird,
    hblock⟩ := habstract (veroneseGram D) (posSemidef_veroneseGram D)
      (fun atomIndex => by
        rw [veroneseGram_diag D hrank (hpositive atomIndex)]; norm_num)
      (fun atomIndex => sum_veroneseGram_row D hrank hshare atomIndex)
  refine ⟨tripleFirst, tripleSecond, tripleThird, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
  rw [frobeniusNormSq_add_add]
  exact hblock

/-- **THE REFUTING WITNESS**: diagonal `2/3`, every off-diagonal `−1/9`.  As a
matrix it is `(7/9) I − (1/9) J`, i.e. `(7/9)` times the projection onto the
orthogonal complement of the all-ones vector. -/
noncomputable def uniformVeroneseGramWitness : Matrix (Fin 7) (Fin 7) ℝ :=
  (7 / 9 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ)
    - (1 / 9 : ℝ) • Matrix.vecMulVec (fun _ => 1) (fun _ => 1)

theorem uniformVeroneseGramWitness_diag (atomIndex : Fin 7) :
    uniformVeroneseGramWitness atomIndex atomIndex = 2 / 3 := by
  simp only [uniformVeroneseGramWitness, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, Matrix.vecMulVec_apply, smul_eq_mul]
  norm_num

theorem uniformVeroneseGramWitness_offDiag {firstIndex secondIndex : Fin 7}
    (hdistinct : firstIndex ≠ secondIndex) :
    uniformVeroneseGramWitness firstIndex secondIndex = -(1 / 9) := by
  simp only [uniformVeroneseGramWitness, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply_ne hdistinct, Matrix.vecMulVec_apply, smul_eq_mul]
  norm_num

theorem uniformVeroneseGramWitness_quadraticForm (testVector : Fin 7 → ℝ) :
    testVector ⬝ᵥ uniformVeroneseGramWitness *ᵥ testVector
      = 7 / 9 * (∑ coordIndex, testVector coordIndex ^ 2)
        - 1 / 9 * (∑ coordIndex, testVector coordIndex) ^ 2 := by
  simp [uniformVeroneseGramWitness, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply,
    Fin.sum_univ_seven]
  ring

theorem posSemidef_uniformVeroneseGramWitness : uniformVeroneseGramWitness.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_of_transpose_eq ?_, fun testVector => ?_⟩
  · rw [uniformVeroneseGramWitness, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_vecMulVec]
  · rw [star_trivial, uniformVeroneseGramWitness_quadraticForm]
    have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 7))
      (fun _ => (1 : ℝ)) testVector
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] at hcauchy
    linarith

theorem sum_uniformVeroneseGramWitness_row (atomIndex : Fin 7) :
    ∑ otherIndex, uniformVeroneseGramWitness atomIndex otherIndex = 0 := by
  fin_cases atomIndex <;>
    simp [uniformVeroneseGramWitness, Fin.sum_univ_seven, Matrix.vecMulVec_apply] <;>
    norm_num

/-- **THE VERONESE NO-GO.**  The abstract relaxation is FALSE: the uniform witness
satisfies all three hypotheses and yet every triple carries block mass
`3·(2/3) + 6·(−1/9) = 4/3`, exactly twice the target `2/3`.  In sigma coordinates
the witness sits at `σ = 2/3` on every triple — precisely the constant at which
the campaign's four independent conservation/averaging arguments all stall.  So
the factor of two is not a weakness of those arguments: it is the exact value of
the relaxation, and closing it REQUIRES the rank-one structure. -/
theorem not_abstractMetricTripleBound_sevenThree :
    ¬ AbstractMetricTripleBoundSevenThree := by
  intro habstract
  obtain ⟨tripleFirst, tripleSecond, tripleThird, hfirstSecond, hfirstThird, hsecondThird,
    hblock⟩ := habstract uniformVeroneseGramWitness posSemidef_uniformVeroneseGramWitness
      uniformVeroneseGramWitness_diag sum_uniformVeroneseGramWitness_row
  rw [uniformVeroneseGramWitness_diag, uniformVeroneseGramWitness_diag,
    uniformVeroneseGramWitness_diag, uniformVeroneseGramWitness_offDiag hfirstSecond,
    uniformVeroneseGramWitness_offDiag hfirstThird,
    uniformVeroneseGramWitness_offDiag hsecondThird] at hblock
  norm_num at hblock

/-! ### The witness is not realizable: the Veronese rank bound

`Γ∘Γ` factors through the six-dimensional space of symmetric `3×3` matrices, so
its rank never exceeds six.  The witness demands rank seven.  This is Gerzon's
bound in the exact form the lane needs — and it is the mechanized content of
barrier B3. -/

/-- The Veronese rows: `(x², y², z², xy, xz, yz)` of each unit direction.

Spelled `veroneseSquareRows`, not `veroneseRows`: the public name `Gtz.veroneseRows`
is owned by `Gtz/Quantitative/SevenThreeSyzygy.lean`, where it has width seven.
Declaring it here too makes the two modules impossible to import together. -/
noncomputable def veroneseSquareRows (D : WeightedDesign m 3) : Matrix (Fin m) (Fin 6) ℝ :=
  Matrix.of fun atomIndex coordIndex =>
    ![unitAtom D atomIndex 0 ^ 2, unitAtom D atomIndex 1 ^ 2, unitAtom D atomIndex 2 ^ 2,
      unitAtom D atomIndex 0 * unitAtom D atomIndex 1,
      unitAtom D atomIndex 0 * unitAtom D atomIndex 2,
      unitAtom D atomIndex 1 * unitAtom D atomIndex 2] coordIndex

/-- The dual Veronese rows, with the off-diagonal entries doubled.  Pairing the
two avoids any `√2` and keeps the factorisation exactly rational. -/
noncomputable def veroneseCoRows (D : WeightedDesign m 3) : Matrix (Fin m) (Fin 6) ℝ :=
  Matrix.of fun atomIndex coordIndex =>
    ![unitAtom D atomIndex 0 ^ 2, unitAtom D atomIndex 1 ^ 2, unitAtom D atomIndex 2 ^ 2,
      2 * (unitAtom D atomIndex 0 * unitAtom D atomIndex 1),
      2 * (unitAtom D atomIndex 0 * unitAtom D atomIndex 2),
      2 * (unitAtom D atomIndex 1 * unitAtom D atomIndex 2)] coordIndex

/-- The Hadamard square of the direction Gram, as a matrix. -/
noncomputable def hadamardSquareDirectionGram (D : WeightedDesign m k) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun firstIndex secondIndex => directionGram D firstIndex secondIndex ^ 2

/-- **THE VERONESE FACTORISATION.**  `Γ∘Γ = V W ᵀ` with `V, W` of width six. -/
theorem hadamardSquareDirectionGram_eq_veronese_mul (D : WeightedDesign m 3) :
    hadamardSquareDirectionGram D = veroneseSquareRows D * (veroneseCoRows D)ᵀ := by
  ext firstIndex secondIndex
  simp [hadamardSquareDirectionGram, Matrix.mul_apply, Matrix.transpose_apply,
    veroneseSquareRows, veroneseCoRows, Fin.sum_univ_six, directionGram, dotProduct,
    Fin.sum_univ_three]
  ring

/-- **THE VERONESE RANK BOUND (Gerzon).**  For every rank-three design the
Hadamard square of the direction Gram has rank at most six, whatever the number
of atoms.  Over `ℂ` the corresponding bound is nine, which is why the real
structure is the only available lever. -/
theorem rank_hadamardSquareDirectionGram_le_six (D : WeightedDesign m 3) :
    (hadamardSquareDirectionGram D).rank ≤ 6 := by
  rw [hadamardSquareDirectionGram_eq_veronese_mul]
  refine le_trans (Matrix.rank_mul_le_left (veroneseSquareRows D) ((veroneseCoRows D)ᵀ)) ?_
  simpa using Matrix.rank_le_card_width (veroneseSquareRows D)

/-- The Hadamard square the refuting witness would need: `(7/9) I + (2/9) J`,
which is the witness shifted by `(1/3)` on every entry — the exact inverse of the
`−1/k` shift of `frobeniusInner_veroneseTracelessPart`. -/
noncomputable def uniformHadamardSquareTarget : Matrix (Fin 7) (Fin 7) ℝ :=
  (7 / 9 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ)
    + (2 / 9 : ℝ) • Matrix.vecMulVec (fun _ => 1) (fun _ => 1)

theorem uniformHadamardSquareTarget_eq_witness_add :
    uniformHadamardSquareTarget
      = uniformVeroneseGramWitness
        + (1 / 3 : ℝ) • Matrix.vecMulVec (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
  rw [uniformHadamardSquareTarget, uniformVeroneseGramWitness]
  module

theorem uniformHadamardSquareTarget_quadraticForm (testVector : Fin 7 → ℝ) :
    testVector ⬝ᵥ uniformHadamardSquareTarget *ᵥ testVector
      = 7 / 9 * (∑ coordIndex, testVector coordIndex ^ 2)
        + 2 / 9 * (∑ coordIndex, testVector coordIndex) ^ 2 := by
  simp [uniformHadamardSquareTarget, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply,
    Fin.sum_univ_seven]
  ring

theorem posDef_uniformHadamardSquareTarget : uniformHadamardSquareTarget.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_of_transpose_eq ?_, fun {testVector} hnonzero => ?_⟩
  · rw [uniformHadamardSquareTarget, Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_vecMulVec]
  · rw [star_trivial, uniformHadamardSquareTarget_quadraticForm]
    have hlength : 0 < testVector ⬝ᵥ testVector := dotProduct_self_pos hnonzero
    rw [dotProduct_self_eq_sum_sq] at hlength
    nlinarith [sq_nonneg (∑ coordIndex, testVector coordIndex), hlength]

theorem rank_uniformHadamardSquareTarget : uniformHadamardSquareTarget.rank = 7 := by
  have hrank := Matrix.rank_of_isUnit uniformHadamardSquareTarget
    posDef_uniformHadamardSquareTarget.isUnit
  simpa using hrank

/-- **THE WITNESS IS NOT REALIZABLE.**  No (7,3) design has all twenty-one
squared correlations equal to `2/9` — the Hadamard square such a design would
carry is `(7/9) I + (2/9) J`, positive definite of rank seven, while every
rank-three Hadamard square has rank at most six.  This is the `WeightedDesign`
case of Gerzon's bound: it rules out equiangular PARSEVAL frames.  The classical
"no seven equiangular lines in `ℝ³`" is strictly wider — an equiangular family
need not be scalable to a Parseval frame — and is NOT formally implied by this
statement, although `rank_hadamardSquareDirectionGram_le_six` would prove it, as
that lemma never uses `isParseval`.

Consequence for the lane: the refutation of `AbstractMetricTripleBoundSevenThree`
is a genuine no-go for Gram-Hadamard-square methods and NOT a refutation of the
metric bound.  The whole factor of two between the averaging ceiling `σ = 2/3`
and the target `σ = 1/3` is rank-one content. -/
theorem not_exists_design_with_uniform_edgeWeight_two_ninths :
    ¬ ∃ D : WeightedDesign 7 3, (∀ atomIndex, 0 < leverageOf (D.atom atomIndex))
      ∧ ∀ firstIndex secondIndex, firstIndex ≠ secondIndex
          → edgeWeight D firstIndex secondIndex = 2 / 9 := by
  rintro ⟨D, hpositive, huniformEdge⟩
  have hidentify : hadamardSquareDirectionGram D = uniformHadamardSquareTarget := by
    ext firstIndex secondIndex
    rcases eq_or_ne firstIndex secondIndex with hequal | hdistinct
    · subst hequal
      simp only [hadamardSquareDirectionGram, Matrix.of_apply,
        directionGram_self D (hpositive firstIndex), one_pow, uniformHadamardSquareTarget,
        Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.vecMulVec_apply,
        smul_eq_mul]
      norm_num
    · have hedge := huniformEdge firstIndex secondIndex hdistinct
      rw [edgeWeight] at hedge
      simp only [hadamardSquareDirectionGram, Matrix.of_apply, hedge,
        uniformHadamardSquareTarget, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_ne hdistinct, Matrix.vecMulVec_apply, smul_eq_mul]
      norm_num
  have hbound := rank_hadamardSquareDirectionGram_le_six D
  rw [hidentify, rank_uniformHadamardSquareTarget] at hbound
  omega

/-! ## 6. The merge-boundary route, stated exactly

The extremal has a parallel pair, so it sits where `dominating_of_parallel_pair`
already pays.  This section says precisely what would have to be true for that
observation to become a proof, and records why it does not follow from anything
landed. -/

/-- **THE MERGE-BOUNDARY DICHOTOMY.**  Every equal-share (7,3) design either
carries an exactly parallel pair — where the merge branch pays with no
quantitative hypothesis — or has a triple passing the sigma gate.

This is the exact compactness statement the parallel-pair route needs, and it is
NOT available.  The reason is structural, not a gap in effort: `¬ HasParallelPair`
is an OPEN condition, so the non-parallel stratum is not compact, its closure
meets the parallel locus, and the supremum of `min_T σ_T` over it equals the
supremum over the closure.  So the dichotomy is not weaker than the global bound:
on the non-parallel side it is the SAME statement.  The exact rational
separations that exhibit this at (6,3) and (7,3) are no-go 1 of
`Gtz/Reduction/SplitTransfer.lean`; the corresponding perturbation of
`Gtz.pentagonPairDesign` is expected but is NOT verified here. -/
def MergeBoundaryCollarSevenThree : Prop :=
  ∀ D : WeightedDesign 7 3, (∀ atomIndex, atomShare D atomIndex = 3 / 7) →
    (∀ atomIndex, leverageOf (D.atom atomIndex) = 3) →
      HasParallelPair D
      ∨ ∃ tripleFirst tripleSecond tripleThird : Fin 7,
          tripleFirst ≠ tripleSecond ∧ tripleFirst ≠ tripleThird ∧ tripleSecond ≠ tripleThird ∧
            directionTripleSigma D tripleFirst tripleSecond tripleThird ≤ 1 / 3

/-- **What the dichotomy would buy: NOTHING BEYOND THE (6,3) CELL.**  The collar
hypothesis is REDUNDANT here, and this theorem is the demonstration.  Crystallization
sends `(6,3)` to `(7,3)` unconditionally (`Gtz.gtzWeighted_six_three_iff_seven_three`,
`3*(3+1)/2 = 6 < 7`), and the equal-share cell is `Gtz.GtzWeighted 7 3` with two
hypotheses discarded — so the merge branch's "exact contribution" is empty relative to
the cell that was already assumed alongside it.

The NAME is unchanged, and the binder it names is gone, because `Gtz/Audit.lean` is
append-only: renaming would strand the pin.  Read the name as a historical route
label.  `Gtz.MergeBoundaryCollarSevenThree` therefore has no consumer left that needs
it, which is the whole content of this edit. -/
theorem gtzWeightedEqualShareSevenThree_of_mergeBoundaryCollar
    (hsixThree : GtzWeighted 6 3) : GtzWeightedEqualShareSevenThree :=
  fun D _ _ => gtzWeighted_six_three_iff_seven_three.mp hsixThree D

/-- **The extremal satisfies BOTH branches** — it has a parallel pair AND its
minimising triple passes the gate.  So the numerically identified worst case
supplies no evidence for or against the dichotomy: it is discharged twice over,
and the open content lives strictly on the non-parallel side. -/
theorem pentagonPairDesign_satisfies_both_mergeBoundaryBranches :
    HasParallelPair pentagonPairDesign
      ∧ directionTripleSigma pentagonPairDesign 0 2 3 ≤ 1 / 3 := by
  refine ⟨hasParallelPair_pentagonPairDesign, ?_⟩
  rw [directionTripleSigma_pentagonPairDesign_extremal]
  have hlower := nine_lt_seven_mul_rootFive
  linarith

/-- **The merge branch does discharge the extremal, conditionally.**  Recorded for
completeness: the unconditional discharge is
`Gtz.dominates_pentagonPairDesign_extremalTriple`, which needs no recursion. -/
theorem exists_dominating_pentagonPairDesign_of_gtzWeighted_six
    (hsixThree : GtzWeighted 6 3) :
    ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates pentagonPairDesign C := by
  obtain ⟨keptLabel, dropLabel, ratio, hdistinct, hproportional⟩ :=
    hasParallelPair_pentagonPairDesign
  exact dominating_of_parallel_pair pentagonPairDesign hsixThree hdistinct hproportional

end Gtz
