/-
# The diagonal rungs, and the one criterion that reaches exactly them

The campaign's decided set already contains the whole diagonal band.  Three
statements that a naive reading of the problem lists as targets are landed
theorems in this repository, and this file adds none of them:

* `gtzWeighted_square` (`Gtz/Reduction/Reductions.lean`) — `GtzWeighted k k`.
  Take `C = univ`: `S_univ − I = Σ_c (1 − t_c) g_c g_cᵀ ⪰ 0` because each
  weight is at most one.
* `gtzWeighted_corank_one` (`Gtz/Reduction/Reductions.lean`) —
  `GtzWeighted (k+1) k` for every `k ≥ 1`, by Naimark duality to rank one.  A
  second, constructive route that NAMES the dropped atom is
  `corank_one_dominating_erasure` (`Gtz/Ties/CorankOneTieCriterion.lean`).
* `gtzWeightedFloor_inv_rank` (`Gtz/Reduction/RealVolumeFloor.lean`) — the
  `1/k` Loewner floor at every `(m, k)`, from maximal volume.

The ledger before this file therefore reads: `k ≤ 2` at every `m` — the repo's
own `gtz_rank_two`, a complete in-repo PROOF and not a citation — together with
`m = k`, `m = k + 1`, `m = k + 2` for `k ≥ 2` (`gtzWeighted_corank_two`), and the
`1/k` floor everywhere.  Rank three is open at exactly two sizes, `(6,3)` and
`(7,3)` (`rank_three_iff_the_two_residuals`).

## What is new here

ONE criterion, rank-free, at EVERY `m`.  Write

    u_c = 1 − t_c |g_c|²        (the co-leverage score: the diagonal of I − P)
    s_c = u_c / (1 − t_c)       (the co-leverage ratio)

with `P = projectionOfDesign D` the rank-`k` projection of `Gtz/LinAlg/
ProjectionForm.lean`.  Then

    Σ_{c ∈ C} s_c ≤ 1   ⟹   C dominates          (`dominates_of_sum_coLeverageRatio_le_one`)

for every `k`-subset `C`, at every `m`, with no rank or corank hypothesis.
The proof is three moves and no spectral theory: domination is
`P_C ⪰ diag t_C` (the committed congruence), that gap is
`diag (1 − t_C) − Q_C` with `Q = I − P ⪰ 0`, and a positive-semidefinite
quadratic form is dominated by its own diagonal through the `2 × 2` minors
plus Cauchy–Schwarz — `posSemidef_diagonal_sub_of_sum_diag_div_le_one`, which
is pure linear algebra and knows nothing about designs.

## What the criterion IS

Congruence by `diag(1 − t_C)^{-1/2}` carries the domination gap to `I − N_C`
with `N_C = diag(1 − t_C)^{-1/2} Q_C diag(1 − t_C)^{-1/2} ⪰ 0`.  Domination is
then exactly `λ_max(N_C) ≤ 1`, and the criterion is `trace(N_C) ≤ 1`: it is the
TRACE RELAXATION of the sharp spectral test, and nothing more.  That one
sentence predicts every phenomenon below.  `trace ≥ λ_max` with equality iff the
rank is at most one, and `rank Q_C ≤ min(k, m − k)`, so the relaxation is tight
at corank one and loses up to a rank factor elsewhere; on a balanced design the
trace is constant across subsets, which is the ceiling.  The proof below goes
through `2 × 2` minors and Cauchy–Schwarz instead, deliberately, to keep a
spectral theorem out of the dependency graph — so the identification in this
paragraph is a hand derivation and is NOT mechanized here.

## Where it reaches — and the theorem that it reaches no further

At `m = k + 1` the criterion fires by an argmax with no case
split.  The whole content is two identities: `Σ_c (1 − t_c) s_c = m − k`, so at
corank one `Σ_c s_c − Σ_c t_c s_c = 1`; and `Σ_c t_c s_c` is a convex
combination of the `s_c`, hence at most `max_c s_c`.  Dropping the argmax
gives `Σ_{c ≠ argmax} s_c ≤ 1` (`exists_erase_sum_coLeverageRatio_le_one`).
That re-derives `GtzWeighted (k+1) k` a third time — recorded here as the
criterion's non-vacuity witness, NOT as a new theorem.

The ceiling is the point of the file.  Call a design co-leverage BALANCED when
all its ratios agree (`IsCoLeverageBalanced`); uniform weights plus equal
leverages suffice, so every equal-norm Parseval frame — the exact shape the
1997 statement is posed in — is balanced
(`isCoLeverageBalanced_of_uniformWeight_of_equalLeverage`).  On a balanced
design every `k`-subset carries the same mass `k(m − k)/(m − 1)`, and

    Σ_{c ∈ C} s_c ≤ 1   ⟺   k(m − k) + 1 ≤ m   ⟺   k = 1  or  m = k + 1

(`sum_coLeverageRatio_le_one_iff_of_isCoLeverageBalanced`,
`classicalDenominator_le_frameSize_iff_diagonalRung`).  The middle condition is
the vanishing of the committed classical deficit `(k−1)(m−k−1)` of
`gtzDenominator_add_deficit_eq_classical`.  So this lever's reach on balanced
designs coincides EXACTLY with the locus where maximal volume already meets
GTZ, and no sharpening of the SELECTOR extends it: on a balanced design every
subset scores the same, so there is nothing to select.  That is a stop sign, and
it is the honest deliverable.

Read the stop sign for exactly what it says.  It bounds this lever, not the
problem.  Balanced designs are not hard instances and the ceiling claims nothing
of the kind — on the `(6,3)` witness below every triple is invisible to the
criterion and an explicit triple dominates anyway.

## Two witnesses at `(6,3)`, an OPEN rung

`balancedOctahedronDesign`, the six vectors `±√3 · e_i` at uniform weight `1/6`,
is balanced (`isCoLeverageBalanced_balancedOctahedronDesign`), so the criterion
fires on NO triple, each carrying mass `9/5`; and `{0, 2, 4}` dominates outright
with `S_C = 3·I`.  `balancedOctahedronDesign_dominated_and_criterion_blind`
proves both halves at once.  So the ceiling is not a statement about a class
that is empty where the problem is still open, and the criterion is provably
incomplete at a size that is still open.  `balancedPairDesign` — four atoms
`(1,1), (1,-1), (1,1), (1,-1)` at uniform weight `1/4`, mass `4/3` — is the same
phenomenon at `(4, 2)`, the smallest positive deficit, where GTZ is already
`gtz_rank_two`.

`selectiveAxisDesign`, the three coordinate axes at length `1` and at length `2`
with weights `1/9` and `2/9`, has ratios `1` and `1/7`.  The criterion FIRES on
the heavy triple `{3, 4, 5}` (mass `3/7`,
`dominates_selectiveAxisDesign_heavyTriple`) and is blind on the light triple
`{0, 1, 2}` (mass `3`, `selectiveAxisDesign_criterion_blindOnLightTriple`).  Off
the balanced class the criterion therefore discriminates genuinely, and it does
so at corank three — well past the corank-one rung where it is tight.

## Honest scope

* The criterion is SUFFICIENT only.  The converse `Dominates ⟹ mass ≤ 1` is
  false above corank one, and the two balanced witnesses refute it outright at
  `(6,3)` and at `(4,2)`.  At `m = k + 1` the converse IS true, because `Q` has
  rank one there and the `|Q_cd| ≤ √(Q_cc Q_dd)` step is an equality — but that
  iff is NOT proved in this file, and proving it needs `rank (I − P) = 1`, which
  nothing in the repository currently supplies.
* Nothing here decides any open rung, and nothing here is a new GTZ theorem.
  The `GtzWeighted (k+1) k` corollary duplicates two landed proofs.
* The criterion is Gershgorin/diagonal-dominance flavoured, and read as a trace
  relaxation it is the elementary bound `R ⪯ trace(D^{-1/2} R D^{-1/2}) · D`.  It
  was NOT checked against the numerical-linear-algebra literature; "new" here
  means "not in this repository", not "not in print", and the trace reading
  makes prior art likelier rather than less.
* Outside the balanced class the reach is exhibited by exactly one mechanized
  witness, `selectiveAxisDesign`, and otherwise measured only empirically (an
  experiment fired the criterion on 101/600 random `(7,3)` designs).  No general
  statement about that regime is proved.
* Blindness is exhibited at `(4,2)` and at `(6,3)`.  `(7,3)`, the other open
  residual, has no balanced witness here.  It admits one — balance is a positive
  linear condition on the weights and is solvable at that shape — but building it
  needs a rank-3 projection with a prescribed diagonal, and this file constructs
  none.
* Both balanced witnesses repeat rank-one atoms — `balancedPairDesign`
  duplicates two vectors outright, `balancedOctahedronDesign` uses antipodal
  pairs, and `g gᵀ` cannot tell a sign.  `WeightedDesign` imposes no distinctness
  and no statement here is affected, but a distinct-atom balanced design would be
  the drop-in should the conventions of `Gtz/Ties/RepeatedAtomExclusion.lean`
  ever matter downstream.
* The `1/k` floor cited above is a floor, not the rank constant: at `k = 2` the
  repository proves `α_2(ℝ) ≥ 1` (`gtz_rank_two`) where the floor gives `1/2`.
  The matching upper bound `α_2(ℝ) ≤ 1` appears nowhere in the repository, so
  `α_2(ℝ) = 1` is NOT a repo fact.
* Two of the cited statements have degenerate corners.  `WeightedDesign 0 k` is
  uninhabited (`isEmpty_weightedDesign_of_sizeZero`), so the `k = 0` instance of
  `gtzWeighted_square` is vacuous; from `k = 1` on the family is inhabited
  (`nonempty_weightedDesign_square_of_rank_pos`).  And `gtzWeightedFloor_inv_rank`
  at `k = 0` asserts a level-`0` bound on `0 × 0` matrices, since Lean reads
  `((0 : ℕ) : ℝ)⁻¹` as `0`; its "every size, every rank, no hypothesis" reading
  holds from `k = 1` on.
* This file is NOT in the build.  `lakefile.toml` declares
  `defaultTargets = ["Gtz"]` and `Gtz.lean` does not import it, so `lake build`
  never compiles it and no `#print axioms` line in `Gtz/Audit.lean` covers it.
  Wiring is the orchestrator's; until it happens nothing here is CI-protected
  and a Mathlib bump can break this file silently.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.MaximalVolume
import Gtz.Reduction.Reductions
import Gtz.Reduction.DescentLadder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## A positive semidefinite form is dominated by its own diagonal

Pure linear algebra, no designs.  The two ingredients are the `2 × 2` principal
minor (`sq_le_mul_diag_of_posSemidef`, committed in `MaximalVolume`) and
Cauchy–Schwarz weighted by the diagonal being subtracted from.
-/

variable {size : ℕ}

/-- **The off-diagonal is bounded by the diagonal**, in square-root form:
`|R_ij| ≤ √R_ii · √R_jj` for `R ⪰ 0`.  The `2 × 2` minor with a square root
taken. -/
theorem abs_le_sqrt_mul_sqrt_diag_of_posSemidef
    {residual : Matrix (Fin size) (Fin size) ℝ} (hpsd : residual.PosSemidef)
    (rowIndex colIndex : Fin size) :
    |residual rowIndex colIndex|
      ≤ Real.sqrt (residual rowIndex rowIndex) * Real.sqrt (residual colIndex colIndex) := by
  have hminor := sq_le_mul_diag_of_posSemidef hpsd rowIndex colIndex
  calc |residual rowIndex colIndex|
      = Real.sqrt (residual rowIndex colIndex ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (residual rowIndex rowIndex * residual colIndex colIndex) :=
        Real.sqrt_le_sqrt hminor
    _ = Real.sqrt (residual rowIndex rowIndex) * Real.sqrt (residual colIndex colIndex) :=
        Real.sqrt_mul hpsd.diag_nonneg _

/-- **The quadratic form is bounded by the square of the diagonal profile**:
`xᵀRx ≤ (Σ_i √R_ii |x_i|)²` for `R ⪰ 0`.  Summing the entrywise bound; no
eigenvalue, no trace. -/
theorem quadForm_le_sq_sum_sqrt_diag
    {residual : Matrix (Fin size) (Fin size) ℝ} (hpsd : residual.PosSemidef)
    (vec : Fin size → ℝ) :
    vec ⬝ᵥ (residual *ᵥ vec) ≤ (∑ i, Real.sqrt (residual i i) * |vec i|) ^ 2 := by
  have hexpand : vec ⬝ᵥ (residual *ᵥ vec)
      = ∑ i, ∑ j, vec i * (residual i j * vec j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hsquare : (∑ i, Real.sqrt (residual i i) * |vec i|) ^ 2
      = ∑ i, ∑ j, (Real.sqrt (residual i i) * |vec i|)
          * (Real.sqrt (residual j j) * |vec j|) := by
    rw [pow_two, Finset.sum_mul_sum]
  rw [hexpand, hsquare]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hbound := abs_le_sqrt_mul_sqrt_diag_of_posSemidef hpsd i j
  have hstep : vec i * (residual i j * vec j) ≤ |vec i| * |residual i j| * |vec j| := by
    calc vec i * (residual i j * vec j)
        ≤ |vec i * (residual i j * vec j)| := le_abs_self _
      _ = |vec i| * |residual i j| * |vec j| := by rw [abs_mul, abs_mul]; ring
  have habsNonneg : (0 : ℝ) ≤ |vec i| * |vec j| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith [hstep, hbound, habsNonneg, abs_nonneg (vec i), abs_nonneg (vec j)]

/-- **THE RANK-FREE CRITERION, in pure linear algebra.**  A positive
semidefinite residual is dominated by a positive diagonal as soon as the
residual's own diagonal, measured against that diagonal, has total mass at most
one:

    R ⪰ 0,  d_i > 0,  Σ_i R_ii / d_i ≤ 1   ⟹   diag d − R ⪰ 0.

Cauchy–Schwarz with the weights `√(R_ii)/√(d_i)` and `√(d_i)|x_i|` turns the
diagonal profile of `quadForm_le_sq_sum_sqrt_diag` into exactly that mass times
`Σ_i d_i x_i²`.

Named honestly: after congruence by `diag(d)^{-1/2}` the hypothesis is
`trace(D^{-1/2} R D^{-1/2}) ≤ 1` and the conclusion is
`λ_max(D^{-1/2} R D^{-1/2}) ≤ 1`, so this is the elementary trace bound
`λ_max ≤ trace` for a positive semidefinite matrix, dressed for a diagonal
comparison.  It is proved here from minors and Cauchy–Schwarz rather than from
the spectral theorem, which is why no eigenvalue appears.  The constant `1`
cannot be raised — `exists_residual_notPosSemidef_of_mass_gt_one` refutes every
larger threshold. -/
theorem posSemidef_diagonal_sub_of_sum_diag_div_le_one
    {residual : Matrix (Fin size) (Fin size) ℝ} (hpsd : residual.PosSemidef)
    {positiveDiagonal : Fin size → ℝ} (hpos : ∀ i, 0 < positiveDiagonal i)
    (hmass : ∑ i, residual i i / positiveDiagonal i ≤ 1) :
    (Matrix.diagonal positiveDiagonal - residual).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun vec => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_sub, Matrix.diagonal_transpose,
      transpose_eq_of_isHermitian hpsd.isHermitian]
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    set weightedSquares : ℝ := ∑ i, positiveDiagonal i * vec i ^ 2 with hweightedSquares
    have hdiagonalForm : vec ⬝ᵥ (Matrix.diagonal positiveDiagonal *ᵥ vec) = weightedSquares := by
      rw [hweightedSquares]
      simp only [dotProduct, Matrix.mulVec_diagonal]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hweightedNonneg : 0 ≤ weightedSquares :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hpos i).le (sq_nonneg _)
    have hmassNonneg : 0 ≤ ∑ i, residual i i / positiveDiagonal i :=
      Finset.sum_nonneg fun i _ => div_nonneg hpsd.diag_nonneg (hpos i).le
    have hcauchySchwarz : (∑ i, Real.sqrt (residual i i) * |vec i|) ^ 2
        ≤ (∑ i, residual i i / positiveDiagonal i) * weightedSquares := by
      have hsplit : (∑ i, Real.sqrt (residual i i) * |vec i|)
          = ∑ i, (Real.sqrt (residual i i) / Real.sqrt (positiveDiagonal i))
              * (Real.sqrt (positiveDiagonal i) * |vec i|) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hne : Real.sqrt (positiveDiagonal i) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
        field_simp
      have hbase := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i => Real.sqrt (residual i i) / Real.sqrt (positiveDiagonal i))
        (fun i => Real.sqrt (positiveDiagonal i) * |vec i|)
      have hleft : (∑ i, (Real.sqrt (residual i i) / Real.sqrt (positiveDiagonal i)) ^ 2)
          = ∑ i, residual i i / positiveDiagonal i :=
        Finset.sum_congr rfl fun i _ => by
          rw [div_pow, Real.sq_sqrt hpsd.diag_nonneg, Real.sq_sqrt (hpos i).le]
      have hright : (∑ i, (Real.sqrt (positiveDiagonal i) * |vec i|) ^ 2) = weightedSquares :=
        Finset.sum_congr rfl fun i _ => by
          rw [mul_pow, Real.sq_sqrt (hpos i).le, sq_abs]
      rw [hsplit, ← hleft, ← hright]
      exact hbase
    have hquadForm := quadForm_le_sq_sum_sqrt_diag hpsd vec
    rw [hdiagonalForm]
    nlinarith [hquadForm, hcauchySchwarz, hmass, hweightedNonneg, hmassNonneg]

/-- **The constant `1` cannot be raised.**  For every `c > 1` there is a
positive semidefinite residual and a positive diagonal whose criterion mass is
exactly `c` and whose gap is NOT positive semidefinite: take the all-ones rank
one residual against the constant diagonal `2/c`, and test the gap on the
all-ones vector, where it evaluates to `4/c − 4 < 0`.  So
`posSemidef_diagonal_sub_of_sum_diag_div_le_one` is sharp as stated, and the
equality case is rank one exactly as the trace reading predicts. -/
theorem exists_residual_notPosSemidef_of_mass_gt_one (level : ℝ) (hlevel : 1 < level) :
    ∃ (residual : Matrix (Fin 2) (Fin 2) ℝ) (positiveDiagonal : Fin 2 → ℝ),
      residual.PosSemidef ∧ (∀ i, 0 < positiveDiagonal i) ∧
        (∑ i, residual i i / positiveDiagonal i) = level ∧
        ¬ (Matrix.diagonal positiveDiagonal - residual).PosSemidef := by
  have hlevelPos : (0 : ℝ) < level := by linarith
  refine ⟨Matrix.vecMulVec ![1, 1] ![1, 1], fun _ => 2 / level, ?_,
    fun i => by positivity, ?_, ?_⟩
  · have hfactor : Matrix.vecMulVec (![1, 1] : Fin 2 → ℝ) ![1, 1]
        = (Matrix.of (fun (_ : Fin 1) (_ : Fin 2) => (1 : ℝ)))ᴴ
          * Matrix.of (fun (_ : Fin 1) (_ : Fin 2) => (1 : ℝ)) := by
      ext leftIndex rightIndex
      fin_cases leftIndex <;> fin_cases rightIndex <;>
        simp [Matrix.vecMulVec, Matrix.mul_apply]
    rw [hfactor]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · simp only [Fin.sum_univ_two, Matrix.vecMulVec_apply]
    norm_num
  · intro hpsd
    rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hpsd
    have hform := hpsd.2 (![1, 1] : Fin 2 → ℝ)
    rw [star_trivial] at hform
    have hvalue : (![1, 1] : Fin 2 → ℝ)
        ⬝ᵥ ((Matrix.diagonal (fun _ : Fin 2 => 2 / level)
              - Matrix.vecMulVec ![1, 1] ![1, 1]) *ᵥ ![1, 1]) = 4 / level - 4 := by
      simp only [dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.diagonal_apply,
        Matrix.vecMulVec_apply, Fin.sum_univ_two]
      norm_num
      ring
    rw [hvalue] at hform
    have hstrict : (4 : ℝ) / level < 4 := by
      rw [div_lt_iff₀ hlevelPos]
      nlinarith
    linarith

/-! ## The complementary projection and the co-leverage scores -/

/-- The complementary projection `Q = I − P` of a design, on the index space.
A rank-`(m − k)` orthogonal projection whose diagonal is the co-leverage. -/
noncomputable def complementProjection (D : WeightedDesign m k) :
    Matrix (Fin m) (Fin m) ℝ :=
  1 - projectionOfDesign D

/-- The complementary projection is symmetric. -/
theorem complementProjection_transpose (D : WeightedDesign m k) :
    (complementProjection D)ᵀ = complementProjection D := by
  rw [complementProjection, Matrix.transpose_sub, Matrix.transpose_one,
    projectionOfDesign_transpose]

/-- The complementary projection is idempotent — `(I − P)² = I − 2P + P² = I − P`. -/
theorem complementProjection_mul_self (D : WeightedDesign m k) :
    complementProjection D * complementProjection D = complementProjection D := by
  rw [complementProjection, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.one_mul, Matrix.mul_one, projectionOfDesign_mul_self]
  abel

/-- **The complementary projection is positive semidefinite** — symmetric and
idempotent, hence its own `QᵀQ`. -/
theorem complementProjection_posSemidef (D : WeightedDesign m k) :
    (complementProjection D).PosSemidef := by
  have hfactor : complementProjection D
      = (complementProjection D)ᴴ * complementProjection D := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, complementProjection_transpose,
      complementProjection_mul_self]
  rw [hfactor]
  exact Matrix.posSemidef_conjTranspose_mul_self (complementProjection D)

/-- The co-leverage score `u_c = 1 − t_c |g_c|²`: the mass of the index
direction `c` that the design's span misses. -/
noncomputable def coLeverageScore (D : WeightedDesign m k) (atomIndex : Fin m) : ℝ :=
  1 - D.weight atomIndex * leverageOf (D.atom atomIndex)

/-- The co-leverage score is the diagonal of the complementary projection. -/
theorem complementProjection_diagonal (D : WeightedDesign m k) (atomIndex : Fin m) :
    complementProjection D atomIndex atomIndex = coLeverageScore D atomIndex := by
  rw [complementProjection, Matrix.sub_apply, Matrix.one_apply_eq,
    projectionOfDesign_diagonal, coLeverageScore]

/-- The co-leverage score is nonnegative — a diagonal entry of a positive
semidefinite matrix. -/
theorem coLeverageScore_nonneg (D : WeightedDesign m k) (atomIndex : Fin m) :
    0 ≤ coLeverageScore D atomIndex := by
  rw [← complementProjection_diagonal]
  exact (complementProjection_posSemidef D).diag_nonneg

/-- **The co-leverage budget**: the co-leverage scores sum to the corank
`m − k`.  The trace identity read on `I − P`. -/
theorem sum_coLeverageScore (D : WeightedDesign m k) :
    ∑ atomIndex, coLeverageScore D atomIndex = (m : ℝ) - (k : ℝ) := by
  simp only [coLeverageScore]
  rw [Finset.sum_sub_distrib, sum_weight_mul_leverage, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-! ## The co-leverage ratio and the criterion -/

/-- The co-leverage ratio `s_c = u_c / (1 − t_c)` — the co-leverage score
measured against the co-weight, which is the diagonal the domination gap
actually offers. -/
noncomputable def coLeverageRatio (D : WeightedDesign m k) (atomIndex : Fin m) : ℝ :=
  coLeverageScore D atomIndex / (1 - D.weight atomIndex)

/-- The co-leverage ratio is nonnegative. -/
theorem coLeverageRatio_nonneg (D : WeightedDesign m k) (hm : 2 ≤ m) (atomIndex : Fin m) :
    0 ≤ coLeverageRatio D atomIndex :=
  div_nonneg (coLeverageScore_nonneg D atomIndex)
    (by linarith [weight_lt_one D hm atomIndex])

/-- Clearing the denominator: the co-weight times the ratio is the score. -/
theorem one_sub_weight_mul_coLeverageRatio (D : WeightedDesign m k) (hm : 2 ≤ m)
    (atomIndex : Fin m) :
    (1 - D.weight atomIndex) * coLeverageRatio D atomIndex = coLeverageScore D atomIndex := by
  rw [coLeverageRatio, mul_div_cancel₀]
  exact sub_ne_zero_of_ne (ne_of_gt (weight_lt_one D hm atomIndex))

/-- **The ratio budget**: weighted by the co-weights, the co-leverage ratios sum
to the corank.  This is `sum_coLeverageScore` with the denominators cleared, and
it is the whole arithmetic content of the corank-one selector below. -/
theorem sum_one_sub_weight_mul_coLeverageRatio (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ∑ atomIndex, (1 - D.weight atomIndex) * coLeverageRatio D atomIndex
      = (m : ℝ) - (k : ℝ) := by
  rw [← sum_coLeverageScore D]
  exact Finset.sum_congr rfl fun atomIndex _ =>
    one_sub_weight_mul_coLeverageRatio D hm atomIndex

/-- Summing a function over a `k`-subset is summing it along that subset's order
embedding. -/
theorem sum_orderEmbOfFin_eq_sum {selectionSize : ℕ} (selected : Finset (Fin m))
    (hcard : selected.card = selectionSize) (summand : Fin m → ℝ) :
    ∑ selectedIndex, summand (selected.orderEmbOfFin hcard selectedIndex)
      = ∑ atomIndex ∈ selected, summand atomIndex := by
  have himage : Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  conv_rhs => rw [← himage]
  rw [Finset.sum_image (selected.orderEmbOfFin hcard).injective.injOn]

/-- The domination gap in projection coordinates, rewritten so the criterion
applies: `P_C − diag t_C = diag (1 − t_C) − Q_C`. -/
theorem projectionBlock_sub_weightDiagonal_eq_coWeight_sub_complementBlock
    (D : WeightedDesign m k) {selectionSize : ℕ} (pick : Fin selectionSize → Fin m)
    (hinj : Function.Injective pick) :
    (projectionOfDesign D).submatrix pick pick
        - Matrix.diagonal (fun selectedIndex => D.weight (pick selectedIndex))
      = Matrix.diagonal (fun selectedIndex => 1 - D.weight (pick selectedIndex))
        - (complementProjection D).submatrix pick pick := by
  ext leftIndex rightIndex
  simp only [complementProjection, Matrix.sub_apply, Matrix.submatrix_apply,
    Matrix.diagonal_apply, Matrix.one_apply]
  rcases eq_or_ne leftIndex rightIndex with rfl | hne
  · rw [if_pos rfl, if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg hne, if_neg hne, if_neg (fun heq => hne (hinj heq))]
    ring

/-- **THE CO-LEVERAGE CRITERION.**  At every `m` and every `k`, a `k`-subset
whose co-leverage ratios have total mass at most one dominates:

    Σ_{c ∈ C} u_c/(1 − t_c) ≤ 1   ⟹   S_C ⪰ I.

No rank hypothesis, no corank hypothesis, no eigenvalue.  SUFFICIENT ONLY: the
converse fails from `(4,2)` up, refuted concretely by `balancedPairDesign` and
`balancedOctahedronDesign`.  At `m = k + 1` the converse does hold, since
`I − P` has rank one there and the `|Q_cd| ≤ √(Q_cc Q_dd)` step inside
`posSemidef_diagonal_sub_of_sum_diag_div_le_one` becomes an equality — that iff
is NOT proved here, and it would need `rank (I − P) = 1`, which the repository
does not supply. -/
theorem dominates_of_sum_coLeverageRatio_le_one (D : WeightedDesign m k) (hm : 2 ≤ m)
    (selected : Finset (Fin m)) (hcard : selected.card = k)
    (hmass : ∑ atomIndex ∈ selected, coLeverageRatio D atomIndex ≤ 1) :
    Dominates D selected := by
  rw [dominates_iff_posSemidef_projectionBlock_finset D selected hcard]
  have hinj : Function.Injective (selected.orderEmbOfFin hcard) :=
    (selected.orderEmbOfFin hcard).injective
  rw [projectionBlock_sub_weightDiagonal_eq_coWeight_sub_complementBlock D _ hinj]
  refine posSemidef_diagonal_sub_of_sum_diag_div_le_one
    ((complementProjection_posSemidef D).submatrix (selected.orderEmbOfFin hcard))
    (fun selectedIndex => ?_) ?_
  · linarith [weight_lt_one D hm (selected.orderEmbOfFin hcard selectedIndex)]
  · have hentry : ∀ selectedIndex : Fin k,
        ((complementProjection D).submatrix (selected.orderEmbOfFin hcard)
            (selected.orderEmbOfFin hcard)) selectedIndex selectedIndex
          / (1 - D.weight (selected.orderEmbOfFin hcard selectedIndex))
          = coLeverageRatio D (selected.orderEmbOfFin hcard selectedIndex) := by
      intro selectedIndex
      rw [Matrix.submatrix_apply, complementProjection_diagonal, coLeverageRatio]
    rw [Finset.sum_congr rfl fun selectedIndex _ => hentry selectedIndex,
      sum_orderEmbOfFin_eq_sum selected hcard]
    exact hmass

/-! ## Corank one: the criterion is sharp, and fires by an argmax -/

/-- A probability-weighted average is at most a maximum. -/
theorem sum_weight_mul_le_max (D : WeightedDesign m k) {summand : Fin m → ℝ}
    {peak : Fin m} (hpeak : ∀ atomIndex, summand atomIndex ≤ summand peak) :
    ∑ atomIndex, D.weight atomIndex * summand atomIndex ≤ summand peak := by
  calc ∑ atomIndex, D.weight atomIndex * summand atomIndex
      ≤ ∑ atomIndex, D.weight atomIndex * summand peak :=
        Finset.sum_le_sum fun atomIndex _ =>
          mul_le_mul_of_nonneg_left (hpeak atomIndex) (D.weight_pos atomIndex).le
    _ = summand peak := by rw [← Finset.sum_mul, D.weight_sum_one, one_mul]

/-- **THE CORANK-ONE SELECTOR.**  At `m = k + 1` the atom of largest
co-leverage ratio is droppable: erasing it leaves total mass at most one.

Two lines of arithmetic.  `Σ_c (1 − t_c) s_c = 1` at corank one, so
`Σ_c s_c = 1 + Σ_c t_c s_c`; and `Σ_c t_c s_c ≤ max_c s_c` because `t` is a
probability vector.  Subtracting the peak leaves `≤ 1`.  Equality throughout
when all the ratios agree, which is why the uniform design sits exactly on the
boundary — the inequality is tight and no lossy argument can prove it. -/
theorem exists_erase_sum_coLeverageRatio_le_one (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k) :
    ∃ dropped : Fin (k + 1),
      ∑ atomIndex ∈ Finset.univ.erase dropped, coLeverageRatio D atomIndex ≤ 1 := by
  have hm : 2 ≤ k + 1 := by omega
  obtain ⟨dropped, hdropped⟩ := Finite.exists_max (coLeverageRatio D)
  refine ⟨dropped, ?_⟩
  have hbudget : ∑ atomIndex, (1 - D.weight atomIndex) * coLeverageRatio D atomIndex = 1 := by
    rw [sum_one_sub_weight_mul_coLeverageRatio D hm]
    push_cast
    ring
  have hsplit : ∑ atomIndex, coLeverageRatio D atomIndex
      = 1 + ∑ atomIndex, D.weight atomIndex * coLeverageRatio D atomIndex := by
    rw [← hbudget, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => by ring
  have hpeak := sum_weight_mul_le_max D hdropped
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ dropped), hsplit]
  linarith

/-- The criterion is not vacuous: at corank one it fires, delivering a
dominating `k`-subset with the dropped atom NAMED by an argmax.  This is a third
route to the landed `gtzWeighted_corank_one`, recorded as a sharpness witness
for the criterion and not as a new theorem. -/
theorem exists_erase_dominates_of_corank_one (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k) :
    ∃ dropped : Fin (k + 1),
      (Finset.univ.erase dropped).card = k ∧ Dominates D (Finset.univ.erase dropped) := by
  obtain ⟨dropped, hmass⟩ := exists_erase_sum_coLeverageRatio_le_one hk D
  have hcard : (Finset.univ.erase dropped).card = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ dropped), Finset.card_univ, Fintype.card_fin]
    omega
  exact ⟨dropped, hcard,
    dominates_of_sum_coLeverageRatio_le_one D (by omega) _ hcard hmass⟩

/-! ## The ceiling: on a balanced design the criterion reaches exactly the
diagonal rungs -/

/-- A design is co-leverage balanced when every atom carries the same
co-leverage ratio. -/
def IsCoLeverageBalanced (D : WeightedDesign m k) : Prop :=
  ∀ firstIndex secondIndex : Fin m,
    coLeverageRatio D firstIndex = coLeverageRatio D secondIndex

/-- **The classical GTZ input is balanced.**  Uniform weights plus equal
leverages — an equal-norm Parseval frame, which is exactly the `t ≡ 1/n` shape
`rowDesign` produces from an orthonormal-column matrix with equal row norms —
give a co-leverage balanced design.  So the ceiling below applies precisely to
the setting the 1997 statement is posed in. -/
theorem isCoLeverageBalanced_of_uniformWeight_of_equalLeverage (D : WeightedDesign m k)
    (huniformWeight : ∀ atomIndex, D.weight atomIndex = (m : ℝ)⁻¹)
    (hequalLeverage : ∀ firstIndex secondIndex : Fin m,
      leverageOf (D.atom firstIndex) = leverageOf (D.atom secondIndex)) :
    IsCoLeverageBalanced D := by
  intro firstIndex secondIndex
  rw [coLeverageRatio, coLeverageRatio, coLeverageScore, coLeverageScore,
    huniformWeight firstIndex, huniformWeight secondIndex,
    hequalLeverage firstIndex secondIndex]

/-- On a balanced design every co-leverage ratio equals `(m − k)/(m − 1)`.
Forced: the ratios are constant and the co-weights sum to `m − 1`, so the
constant is pinned by the budget `Σ_c (1 − t_c) s_c = m − k`. -/
theorem coLeverageRatio_of_isCoLeverageBalanced (D : WeightedDesign m k) (hm : 2 ≤ m)
    (hbalanced : IsCoLeverageBalanced D) (atomIndex : Fin m) :
    coLeverageRatio D atomIndex = ((m : ℝ) - (k : ℝ)) / ((m : ℝ) - 1) := by
  have hmReal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hbudget := sum_one_sub_weight_mul_coLeverageRatio D hm
  have hconstant : ∑ other, (1 - D.weight other) * coLeverageRatio D other
      = coLeverageRatio D atomIndex * ((m : ℝ) - 1) := by
    rw [← sum_one_sub_weight D, Finset.mul_sum]
    exact Finset.sum_congr rfl fun other _ => by rw [hbalanced other atomIndex]; ring
  rw [hconstant] at hbudget
  rw [eq_div_iff (ne_of_gt (by linarith : (0 : ℝ) < (m : ℝ) - 1))]
  exact hbudget

/-- On a balanced design every `k`-subset carries the SAME criterion mass
`k(m − k)/(m − 1)` — the criterion cannot distinguish subsets, so no sharper
selector exists inside this class. -/
theorem sum_coLeverageRatio_of_isCoLeverageBalanced (D : WeightedDesign m k) (hm : 2 ≤ m)
    (hbalanced : IsCoLeverageBalanced D) (selected : Finset (Fin m))
    (hcard : selected.card = k) :
    ∑ atomIndex ∈ selected, coLeverageRatio D atomIndex
      = (k : ℝ) * ((m : ℝ) - (k : ℝ)) / ((m : ℝ) - 1) := by
  rw [Finset.sum_congr rfl fun atomIndex _ =>
      coLeverageRatio_of_isCoLeverageBalanced D hm hbalanced atomIndex,
    Finset.sum_const, hcard, nsmul_eq_mul]
  ring

/-- **The nat arithmetic of the ceiling.**  The classical maximal-volume
denominator drops to the frame size exactly at the diagonal rungs.  Read through
the committed deficit identity `m + (k−1)(m−k−1) = k(m−k) + 1`
(`gtzDenominator_add_deficit_eq_classical`), this says the deficit vanishes iff
`k = 1` or `m = k + 1`. -/
theorem classicalDenominator_le_frameSize_iff_diagonalRung
    {frameSize selectionRank : ℕ} (hrankPos : 1 ≤ selectionRank)
    (hcorankPos : selectionRank + 1 ≤ frameSize) :
    selectionRank * (frameSize - selectionRank) + 1 ≤ frameSize
      ↔ (selectionRank = 1 ∨ frameSize = selectionRank + 1) := by
  have hdeficit := gtzDenominator_add_deficit_eq_classical hrankPos hcorankPos
  have hvanish : (selectionRank - 1) * (frameSize - selectionRank - 1) = 0
      ↔ (selectionRank = 1 ∨ frameSize = selectionRank + 1) := by
    rw [Nat.mul_eq_zero]
    omega
  rw [← hvanish]
  generalize hdef : (selectionRank - 1) * (frameSize - selectionRank - 1) = deficit
    at hdeficit ⊢
  generalize hcls : selectionRank * (frameSize - selectionRank) = classicalDenominator
    at hdeficit ⊢
  omega

/-- **THE CEILING.**  On a balanced design the criterion fires exactly on the
diagonal rungs, and nowhere else:

    Σ_{c ∈ C} s_c ≤ 1   ⟺   k = 1  or  m = k + 1.

So this lever provably cannot reach `(6,3)`, `(7,3)`, or any other rung with a
positive classical deficit `(k−1)(m−k−1)`, no matter how the selector is
sharpened — on balanced designs every `k`-subset carries the same mass, so
there is nothing to select.  The reach coincides with the locus where maximal
volume already meets GTZ.

This bounds the LEVER, not the problem.  Balanced designs need not be hard:
`balancedOctahedronDesign_dominated_and_criterion_blind` exhibits one at the
open rung `(6,3)` where the criterion sees nothing and a dominating triple
exists anyway. -/
theorem sum_coLeverageRatio_le_one_iff_of_isCoLeverageBalanced (D : WeightedDesign m k)
    (hk : 1 ≤ k) (hkm : k + 1 ≤ m) (hbalanced : IsCoLeverageBalanced D)
    (selected : Finset (Fin m)) (hcard : selected.card = k) :
    (∑ atomIndex ∈ selected, coLeverageRatio D atomIndex ≤ 1)
      ↔ (k = 1 ∨ m = k + 1) := by
  have hm : 2 ≤ m := by omega
  have hmReal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hcorankCast : ((m - k : ℕ) : ℝ) = (m : ℝ) - (k : ℝ) :=
    Nat.cast_sub (by omega)
  rw [sum_coLeverageRatio_of_isCoLeverageBalanced D hm hbalanced selected hcard,
    div_le_one (by linarith), ← classicalDenominator_le_frameSize_iff_diagonalRung hk hkm]
  constructor
  · intro hle
    have hcast : ((k * (m - k) + 1 : ℕ) : ℝ) ≤ ((m : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one, hcorankCast]
      linarith
    exact_mod_cast hcast
  · intro hle
    have hcast : ((k * (m - k) + 1 : ℕ) : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast hle
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one, hcorankCast] at hcast
    linarith

/-! ## The ceiling is not vacuous: a design the criterion provably cannot see -/

/-- The `(4, 2)` balanced witness: four atoms `(1,1), (1,-1), (1,1), (1,-1)` at
uniform weight `1/4`.  Parseval holds because `2·(1,1)(1,1)ᵀ + 2·(1,-1)(1,-1)ᵀ
= 4·I`, and every leverage is `2`, so the design is balanced.  Its deficit
`(k−1)(m−k−1) = 1·1` is positive, which is the smallest place the criterion can
be blind. -/
noncomputable def balancedPairDesign : WeightedDesign 4 2 where
  atom := ![![1, 1], ![1, -1], ![1, 1], ![1, -1]]
  weight := fun _ => (4 : ℝ)⁻¹
  weight_pos := fun _ => by norm_num
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [atomMatrix, Matrix.vecMulVec, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] <;>
      norm_num

/-- The `(4, 2)` witness is balanced. -/
theorem isCoLeverageBalanced_balancedPairDesign : IsCoLeverageBalanced balancedPairDesign := by
  refine isCoLeverageBalanced_of_uniformWeight_of_equalLeverage balancedPairDesign
    (fun atomIndex => by norm_num [balancedPairDesign]) (fun firstIndex secondIndex => ?_)
  fin_cases firstIndex <;> fin_cases secondIndex <;>
    simp [balancedPairDesign, leverageOf, Fin.sum_univ_two]

/-- **THE CRITERION IS STRICTLY WEAKER THAN THE TRUTH, on a concrete design.**
`balancedPairDesign` has a dominating pair — `gtz_rank_two` supplies one, and
`{0, 1}` works by hand since `(1,1)(1,1)ᵀ + (1,-1)(1,-1)ᵀ = 2·I ⪰ I` — while the
co-leverage criterion fires on NO pair, its mass being `k(m−k)/(m−1) = 4/3`
uniformly.  So the ceiling above is not a statement about an empty class: the
criterion is genuinely incomplete already at `(4, 2)`, the smallest positive
deficit. -/
theorem balancedPairDesign_dominated_and_criterion_blind :
    (∃ selected : Finset (Fin 4), selected.card = 2 ∧ Dominates balancedPairDesign selected)
      ∧ ∀ selected : Finset (Fin 4), selected.card = 2 →
          ¬ (∑ atomIndex ∈ selected, coLeverageRatio balancedPairDesign atomIndex ≤ 1) := by
  refine ⟨gtz_rank_two 4 balancedPairDesign, fun selected hcard hmass => ?_⟩
  rcases (sum_coLeverageRatio_le_one_iff_of_isCoLeverageBalanced balancedPairDesign
      (by norm_num) (by norm_num) isCoLeverageBalanced_balancedPairDesign selected hcard).mp hmass
    with hrank | hsize
  · omega
  · omega

/-! ## The ceiling has content at an OPEN rung -/

/-- The balanced `(6, 3)` witness: the six vectors `±√3 · e_i` at uniform weight
`1/6`.  Parseval holds because each coordinate direction occurs twice and
`2 · (1/6) · 3 = 1`, and every leverage is `3`, so the design is balanced.  Its
classical deficit `(k−1)(m−k−1) = 2 · 2` is positive, and `(6, 3)` is one of the
exactly two sizes at which rank three is still open
(`rank_three_iff_the_two_residuals`) — so the ceiling below is not a statement
about a class that is empty where the problem is open. -/
noncomputable def balancedOctahedronDesign : WeightedDesign 6 3 where
  atom := ![![Real.sqrt 3, 0, 0], ![-Real.sqrt 3, 0, 0], ![0, Real.sqrt 3, 0],
            ![0, -Real.sqrt 3, 0], ![0, 0, Real.sqrt 3], ![0, 0, -Real.sqrt 3]]
  weight := fun _ => (6 : ℝ)⁻¹
  weight_pos := fun _ => by norm_num
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  isParseval := by
    have hroot : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [atomMatrix, Matrix.vecMulVec, Fin.sum_univ_six, hroot] <;>
      linarith [hroot]

/-- Every atom of the octahedron witness has leverage `3` — the equal-norm half
of balance. -/
theorem leverageOf_balancedOctahedronDesign (atomIndex : Fin 6) :
    leverageOf (balancedOctahedronDesign.atom atomIndex) = 3 := by
  fin_cases atomIndex <;>
    simp [balancedOctahedronDesign, leverageOf, Fin.sum_univ_three]

/-- The octahedron witness is co-leverage balanced: uniform weights, equal
leverages. -/
theorem isCoLeverageBalanced_balancedOctahedronDesign :
    IsCoLeverageBalanced balancedOctahedronDesign := by
  refine isCoLeverageBalanced_of_uniformWeight_of_equalLeverage balancedOctahedronDesign
    (fun atomIndex => by norm_num [balancedOctahedronDesign]) (fun firstIndex secondIndex => ?_)
  rw [leverageOf_balancedOctahedronDesign, leverageOf_balancedOctahedronDesign]

/-- Every triple carries the same mass `k(m − k)/(m − 1) = 9/5`, which is not
close to the threshold — the criterion misses by a factor near two. -/
theorem sum_coLeverageRatio_balancedOctahedronDesign (selected : Finset (Fin 6))
    (hcard : selected.card = 3) :
    ∑ atomIndex ∈ selected, coLeverageRatio balancedOctahedronDesign atomIndex = 9 / 5 := by
  rw [sum_coLeverageRatio_of_isCoLeverageBalanced balancedOctahedronDesign (by norm_num)
    isCoLeverageBalanced_balancedOctahedronDesign selected hcard]
  norm_num

/-- **The witness is not a hard instance.**  Taking one atom from each antipodal
pair gives `S_C = 3 · I`, so `{0, 2, 4}` dominates with room to spare.  The
design is invisible to the criterion, not difficult for GTZ — which is exactly
what the ceiling asserts and all that it asserts. -/
theorem dominates_balancedOctahedronDesign_coordinateTriple :
    Dominates balancedOctahedronDesign ({0, 2, 4} : Finset (Fin 6)) := by
  have hroot : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hgap : subsetSum balancedOctahedronDesign ({0, 2, 4} : Finset (Fin 6)) - 1
      = Matrix.diagonal (fun _ => (2 : ℝ)) := by
    rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [balancedOctahedronDesign, atomMatrix, Matrix.vecMulVec, hroot] <;> linarith [hroot]
  show (subsetSum balancedOctahedronDesign ({0, 2, 4} : Finset (Fin 6)) - 1).PosSemidef
  rw [hgap]
  exact Matrix.posSemidef_diagonal_iff.mpr fun _ => by norm_num

/-- The criterion fires on NO triple of the octahedron witness — the ceiling,
instantiated at an open rung. -/
theorem balancedOctahedronDesign_criterion_blind (selected : Finset (Fin 6))
    (hcard : selected.card = 3) :
    ¬ (∑ atomIndex ∈ selected, coLeverageRatio balancedOctahedronDesign atomIndex ≤ 1) := by
  intro hmass
  rcases (sum_coLeverageRatio_le_one_iff_of_isCoLeverageBalanced balancedOctahedronDesign
      (by norm_num) (by norm_num) isCoLeverageBalanced_balancedOctahedronDesign selected
      hcard).mp hmass with hrank | hsize
  · omega
  · omega

/-- **THE CRITERION IS STRICTLY WEAKER THAN THE TRUTH AT AN OPEN RUNG.**  On
`balancedOctahedronDesign` a dominating triple exists and the criterion fires on
none of the twenty.  `(6, 3)` is open, so this is not the `(4, 2)` situation
where GTZ was already a theorem: the incompleteness is exhibited exactly where
the campaign still needs an answer. -/
theorem balancedOctahedronDesign_dominated_and_criterion_blind :
    (∃ selected : Finset (Fin 6),
        selected.card = 3 ∧ Dominates balancedOctahedronDesign selected)
      ∧ ∀ selected : Finset (Fin 6), selected.card = 3 →
          ¬ (∑ atomIndex ∈ selected,
              coLeverageRatio balancedOctahedronDesign atomIndex ≤ 1) :=
  ⟨⟨{0, 2, 4}, by decide, dominates_balancedOctahedronDesign_coordinateTriple⟩,
    balancedOctahedronDesign_criterion_blind⟩

/-! ## Off the balanced class the criterion discriminates -/

/-- A `(6, 3)` design on which the criterion is SELECTIVE: the three coordinate
axes at length `1` and again at length `2`, weights `1/9` on the short atoms and
`2/9` on the long ones.  Parseval is `(1/9)·1 + (2/9)·4 = 1` per direction.  The
ratios split — `1` on the short atoms, `1/7` on the long ones — so the criterion
separates triples on a design of positive deficit, at `m = k + 3`. -/
noncomputable def selectiveAxisDesign : WeightedDesign 6 3 where
  atom := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]
  weight := ![(9 : ℝ)⁻¹, (9 : ℝ)⁻¹, (9 : ℝ)⁻¹, 2 / 9, 2 / 9, 2 / 9]
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp [Fin.sum_univ_six]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [atomMatrix, Matrix.vecMulVec, Fin.sum_univ_six, Matrix.vecHead,
        Matrix.vecTail] <;> norm_num

/-- The ratios of the selective witness: `1` on the three short atoms, `1/7` on
the three long ones. -/
theorem coLeverageRatio_selectiveAxisDesign (atomIndex : Fin 6) :
    coLeverageRatio selectiveAxisDesign atomIndex
      = if (atomIndex : ℕ) < 3 then 1 else 1 / 7 := by
  fin_cases atomIndex <;>
    simp [coLeverageRatio, coLeverageScore, selectiveAxisDesign, leverageOf,
      Fin.sum_univ_three] <;> norm_num

/-- The heavy triple carries mass `3/7`, comfortably under the threshold. -/
theorem sum_coLeverageRatio_selectiveAxisDesign_heavyTriple :
    ∑ atomIndex ∈ ({3, 4, 5} : Finset (Fin 6)),
        coLeverageRatio selectiveAxisDesign atomIndex ≤ 1 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    coLeverageRatio_selectiveAxisDesign, coLeverageRatio_selectiveAxisDesign,
    coLeverageRatio_selectiveAxisDesign]
  norm_num

/-- **The criterion decides an instance at `m = k + 3`.**  Firing outside corank
one is therefore not an empirical observation but a mechanized one. -/
theorem dominates_selectiveAxisDesign_heavyTriple :
    Dominates selectiveAxisDesign ({3, 4, 5} : Finset (Fin 6)) :=
  dominates_of_sum_coLeverageRatio_le_one selectiveAxisDesign (by norm_num) _
    (by decide) sum_coLeverageRatio_selectiveAxisDesign_heavyTriple

/-- …and the firing is genuinely selective rather than universal: the light
triple of the same design carries mass `3`, so the criterion rejects it. -/
theorem selectiveAxisDesign_criterion_blindOnLightTriple :
    ¬ (∑ atomIndex ∈ ({0, 1, 2} : Finset (Fin 6)),
        coLeverageRatio selectiveAxisDesign atomIndex ≤ 1) := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    coLeverageRatio_selectiveAxisDesign, coLeverageRatio_selectiveAxisDesign,
    coLeverageRatio_selectiveAxisDesign]
  norm_num

/-! ## The empty corner of the diagonal -/

/-- There is no design of size zero: the weights would have to sum to `1` over
an empty index type.  In particular `WeightedDesign 0 0` is uninhabited, so the
`k = 0` instance of `gtzWeighted_square` is vacuous. -/
theorem isEmpty_weightedDesign_of_sizeZero (k : ℕ) : IsEmpty (WeightedDesign 0 k) := by
  refine ⟨fun D => ?_⟩
  have hsum := D.weight_sum_one
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  exact absurd hsum (by norm_num)

/-- Past that corner the diagonal family has content: `WeightedDesign k k` is
inhabited for every `k ≥ 1`, by the repository's own `rowDesign` on the identity
matrix.  So only the `k = 0` instance of `gtzWeighted_square` is empty. -/
theorem nonempty_weightedDesign_square_of_rank_pos (k : ℕ) (hk : 1 ≤ k) :
    Nonempty (WeightedDesign k k) :=
  ⟨rowDesign hk (1 : Matrix (Fin k) (Fin k) ℝ) (by rw [Matrix.transpose_one, Matrix.one_mul])⟩

end Gtz
