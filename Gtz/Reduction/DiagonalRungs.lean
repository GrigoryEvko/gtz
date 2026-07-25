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

So the ledger before this file already reads: `k ≤ 2` (all `m`, CITED to the
repo's `gtz_rank_two`), `m = k`, `m = k + 1`, `m = k + 2` for `k ≥ 2`
(`gtzWeighted_corank_two`), and the `1/k` floor everywhere.

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

## Where it reaches — and the theorem that it reaches no further

At `m = k + 1` the criterion is SHARP and fires by an argmax with no case
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
GTZ, and it cannot be pushed to `(6,3)`, `(7,3)`, or any other rung of positive
deficit by sharpening the selector: on a balanced design every subset scores
the same, so there is nothing to select.  That is a stop sign, and it is the
honest deliverable.

The stop sign is not about an empty class.  `balancedPairDesign` is an explicit
balanced `(4, 2)` design — four atoms `(1,1), (1,-1), (1,1), (1,-1)` at uniform
weight `1/4` — and `balancedPairDesign_dominated_and_criterion_blind` proves
both halves at once: it HAS a dominating pair (via `gtz_rank_two`) and the
criterion fires on NO pair, the uniform mass being `4/3`.  `(4, 2)` is the
smallest positive deficit, so the criterion is demonstrably incomplete from the
first rung off the diagonal.

## Honest scope

* The criterion is SUFFICIENT only.  It is exact at `m = k + 1`, where `Q` has
  rank one and the `|Q_cd| ≤ √(Q_cc Q_dd)` step is an equality; above that it
  is lossy, and the ceiling above measures how lossy.
* Nothing here decides any open rung, and nothing here is a new GTZ theorem.
  The `GtzWeighted (k+1) k` corollary duplicates two landed proofs.
* The criterion is Gershgorin/diagonal-dominance flavoured.  It was NOT checked
  against the numerical-linear-algebra literature; "new" here means "not in
  this repository", not "not in print".
* The reach measurement outside the balanced class is empirical only (an
  experiment fired it on 101/600 random `(7,3)` designs) and is NOT mechanized.
  Only the balanced ceiling is a theorem.
* The blindness is exhibited at `(4, 2)` and only there.  Balanced designs at
  `(6,3)`, `(7,3)` and beyond are classical (equal-norm Parseval frames exist at
  every `k ≤ m`) but this file constructs none, so "cannot reach `(7,3)`" is the
  ceiling theorem read at that shape, not an instantiated statement.
* The `1/k` floor cited above is a floor, not the rank constant: at `k = 2` the
  real truth is `α_2(ℝ) = 1` (the repo's `gtz_rank_two`) where the floor gives
  `1/2`.
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
`Σ_i d_i x_i²`.  Sharp when `R` has rank one. -/
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

No rank hypothesis, no corank hypothesis, no eigenvalue.  Sufficient only, and
sharp exactly at `m = k + 1` (where `I − P` has rank one, so the
`|Q_cd| ≤ √(Q_cc Q_dd)` step inside
`posSemidef_diagonal_sub_of_sum_diag_div_le_one` is an equality). -/
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
volume already meets GTZ. -/
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

end Gtz
