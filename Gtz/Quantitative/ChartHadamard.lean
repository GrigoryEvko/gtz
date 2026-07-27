/-
# The UNCONDITIONAL chart identities — no stationarity, no hypothesis, no design side

`Gtz.Quantitative.ChartStationary` bundles the first-order data of the chart
objective and derives its consequences.  Everything in THIS file holds at every
chart point whatever, critical or not, and most of it at every symmetric idempotent
whatever, design or not.  So this module deliberately does NOT import that one, and
the import graph is three lines: `Gtz.Core.Basic` for designs,
`Gtz.LinAlg.PsdKit` for `dotProduct_self_eq_sum_sq`, and `Gtz.LinAlg.ProjectionForm`
for the chart `P = V Vᵀ` and its shipped API.  A module that needs less is worth
more, and identities that need nothing are worth the most.

Write `P` for the chart, `t` for the weights, `W = P - diag t` for the gap,
`s_c = P_cc` for the leverage score, `w_c = s_c - t_c` for the gap diagonal,
`l_c = |g_c|²` for the leverage and `b_cd = ⟨g_c, g_d⟩` for the atom pairing.

## PROVED here

**The projection layer** — a symmetric idempotent and a weight vector, no design.

* `trace_sub_weightDiagonal_eq_rank_sub_one` — **(I1)** `tr W = rank - 1`.
* `sum_sq_projectionRow_eq_diagonal` — **(I3)** the row sums of the entrywise square
  of `P` are its own diagonal, because that row sum is the `(c,c)` entry of `P Pᵀ`,
  which is the `(c,c)` entry of `P P`, which is `P_cc`.  Summed:
  `sum_sq_projectionEntry_eq_trace`, total mass `tr P`.
* `det_chartGapPair_eq` — **(I4)** the pair expression `w_c w_d - P_cd²` IS the
  determinant of the `2 x 2` principal block of `W`, so `chartGapPairMinorSum` is
  genuinely the second elementary symmetric function and not a formal expression
  named after one.
* `sum_chartGapPairMinorSum_powersetCard_three` — **(I6)**, summed over every
  three-element subset, in the CORRECTED general form (see below).
* `sum_det_shiftedChartMinors_eq` — **(I7) + (I8)**: for EVERY scalar shift `s`,
  `Σ_{|C| = rank} det(P[C] - s·1)` is a function of `(size, rank, s)` alone.

**The design layer** — the atoms enter, and only here.

* `sq_projectionOfDesign_apply` — `P_cd² = t_c t_d b_cd²`, the rank-generic form of
  the identity `Gtz.chartEntry_sq` proves for the rank-three copy of the chart.
* `sum_weight_mul_sq_atomPairing` — **Parseval as a quadratic form**,
  `Σ_d t_d b_cd² = l_c`.  The only place Parseval is used in this file.
* `chartObstruction` and **(I5a)** `weight_mul_chartObstruction_eq`,
  **(I5b)** `sum_weight_mul_chartObstruction`,
  **(I5c)** `sum_weight_mul_weight_mul_chartObstruction`.
* `sum_det_subsetSum_sub_one_uniform` — **(I8) on the atoms**, and its `(6,3)`
  instance `sum_det_subsetSum_sub_one_sixThree`, the campaign's `-56`.

## THREE CORRECTIONS, each one a claim in the campaign brief that is false as stated

**(I6)'s constant is `(rank-1)² - rank`, not `1`.**  The brief writes the triple sum
as `((size-2)/2)(1 + Σ_c t_c (2 s_c - t_c))`.  That is the RANK-THREE
specialisation and nothing more: `(3-1)² - 3 = 1`.  At `rank = 2` the constant is
`-1`, and the brief's form was measured to fail at every `rank ≠ 3` cell tested
[EXACT rational, outside Lean: 66 of 204 chart points pass the brief's form and those
66 are exactly the `rank = 3` cells; the general form passes 204 of 204].  The
constant is `rank² - 3 rank + 1` — the same one (I5c) produces, which is not a
coincidence: both are the `kappa`-mass of the design, once whole and once cut down to
pairs.  ONLY the general form is stated below.

**(I5b) is constant in `c` only at `rank = 2`.**  The row-sum law's right-hand side
carries the leverage with coefficient `2 - rank`.  Design-independent constancy is a
`rank = 2` phenomenon; at other ranks it holds exactly on constant-leverage designs,
which the named polytopes all are and random designs never are.  The theorem states
the law, and the rider is recorded on it rather than silently dropped.

**(I8) is proved in a DIFFERENT presentation from the brief's.**  The brief gives the
uniform invariant as `Σ_j (-1)^{rank-j} size^j C(size-j, rank-j) C(rank, j)`.  What is
proved here is the coefficient convolution of the generating function,
`Σ_j C(size-rank, j)(-s)^j C(rank, rank-j)(1-s)^{rank-j}` at `s = 1/size`, scaled by
`size^rank`.  The two agree numerically at every cell the campaign measured, but THEY
ARE NOT PROVED EQUAL HERE — that is a binomial identity, and it is not needed:
`sum_det_subsetSum_sub_one_sixThree` evaluates the proved form at `(6,3)` and gets
`-56` on the nose.

## A STALE HEADER, reported not repaired

`Gtz.LinAlg.ProjectionForm`'s own header announces two theorems it does not contain:
`det_one_add_X_smul_shifted` — the generating function of the shifted minor sums —
and `sum_det_shiftedProjectionMinors_designIndependent` following from it.  Neither
name exists anywhere in that file, whose last declaration is
`det_one_add_smul_shifted_real` and whose final section heading is empty.  The two
statements the header describes are `det_one_add_X_smul_shifted` and
`sum_det_shiftedChartMinors_eq` below, proved here because that file is not this
file's to edit.  The real-scalar version IS shipped there and is USED here, not
re-proved: the polynomial identity is obtained from it by evaluating at every real
point off the single degenerate one and invoking that a real polynomial with
infinitely many roots vanishes.  (The same header's `projectionOfDesign_tetraDesign`
is also absent from that file, though a differently-named cousin exists elsewhere.)

## HONESTY — what these identities do NOT do

**(I6)'s positivity is vacuous exactly where the problem is.**  Under all-heavy the
triple total is strictly positive, so SOME triple has `e_2 > 0`
(`exists_pos_chartGapPairMinorSum_of_allHeavy`).  That is the half of the
rank-three reformulation which carries no information: at BOTH known rank-three
counterexamples over `ℂ` — the trine at `(6,3)` and the Hesse SIC at `(9,3)` — every
triple passes the `e_2` test and none passes `e_3` [120 digits, outside Lean].  The
whole obstruction is `e_3`, and no argument that controls only `e_2` can close a cell.

**(I8) is a NO-GO, not a step.**  It says the averaging functional over all
`rank`-subsets cannot see the design at all at a uniform weight.  So no averaging
argument decides the open cells; the functional is dead by identity rather than by
counterexample.  At non-uniform weights the aggregate is genuinely design-dependent
— the `(6,3)` split tetrahedron gives `-64` against the uniform `-56` [EXACT, outside
Lean] — which is why the atom-side statement carries a uniformity hypothesis and the
chart-side one carries a scalar shift.

**Nothing here is conditional, and nothing here is a decision procedure.**  Not one
statement below carries a hypothesis about domination, about criticality, or about
the value of any objective.  That is the point of the module and also the limit of
it.

## NOT here, deliberately

* **No rank-three leg translation.**  `Gtz.chartMinorSum_eq` and `Gtz.chartTie_eq`
  (`Gtz.Quantitative.ProjectionChartLegs`) already carry `e_2` and `e_3` of a triple
  as weight-cleared chart polynomials, in that file's own rank-three copy of the
  chart (`Gtz.chartEntry`, `Gtz.chartGapDiagonal`).  They are cited and NOT
  re-derived; that file is not imported, so the bridge
  `chartEntry = projectionOfDesign` is not proved here either.
* **No eigenvalue anywhere.**  (I7) in the brief's phrasing — "the sum of the
  `rank`-subset minors is `e_rank` of the SPECTRUM of `W`" — is not stated, because
  with `e_rank` defined by the generating function it is literally Mathlib's
  `Matrix.coeff_det_one_add_X_smul_eq_sum_minors`, and with `e_rank` defined on
  eigenvalues it needs a spectral theorem this repository does not carry.  What is
  stated instead is the CLOSED FORM, which is the content.
* **No Cauchy–Binet.**  (I2), `Σ_{|C| = rank} det P[C] = 1`, is
  `Gtz.sum_det_projectionMinors_rank` and is not restated; it is the `s = 0` corner
  of `sum_det_shiftedChartMinors_eq`, whose right-hand side there collapses to
  `C(rank, rank) = 1`.
* **No new gap matrix.**  `Gtz.chartGap` (field-generic, takes a design) and
  `Gtz.chartStationaryGap` (raw matrix and raw weights) already exist; this file
  writes `P - diag t` out where it needs it rather than adding a third name.
* **No non-vacuity witness.**  `Gtz.icosaDesign` (`Gtz.Quantitative.RealnessEngine`)
  is a uniform `(6,3)` design and inhabits the hypothesis of
  `sum_det_subsetSum_sub_one_sixThree`; instantiating it here would drag six modules
  into an import graph of three, so it is cited instead.

## MEASURED (computed outside Lean, NOT proved here, stated as such)

Every identity below was verified in exact rational arithmetic before it was
mechanized: (I1), (I3), (I5a), (I5b), (I5c) and (I7) at 204 of 204 chart points
across nineteen cells with `rank` from two to six and `size` from four to ten, and
again at 120 digits on eighteen named designs with residuals at or below `1e-120`;
(I6) in the general form at 204 of 204 and the brief's form at 66; (I8) exactly on
every cell with `size ≤ 10` and `rank ≤ 4`, with the `(6,3)` value `-56` reproduced
independently on the octahedron, the icosahedron, the `D3` root design and the
bundled cycle, and over `ℂ` on the trine.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## (I1): the trace of the chart gap -/

/-- **(I1)**: `tr W = rank - 1` for `W = P - diag t`.  The one identity where the
trace of the chart and the normalisation of the weights meet, and the reason the
gap can never be negative definite once the rank exceeds one. -/
theorem trace_sub_weightDiagonal_eq_rank_sub_one
    {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
    (htraceRank : Matrix.trace projection = (rank : ℝ))
    (hweightSumOne : ∑ atomIndex : Fin size, weight atomIndex = 1) :
    Matrix.trace (projection - Matrix.diagonal weight) = (rank : ℝ) - 1 := by
  rw [Matrix.trace_sub, htraceRank, Matrix.trace_diagonal, hweightSumOne]

/-- **(I1) at a design's chart.**  Both hypotheses are shipped facts, so the
identity is unconditional there. -/
theorem trace_projectionOfDesign_sub_weightDiagonal (design : WeightedDesign size rank) :
    Matrix.trace (projectionOfDesign design - Matrix.diagonal design.weight) = (rank : ℝ) - 1 :=
  trace_sub_weightDiagonal_eq_rank_sub_one (trace_projectionOfDesign design)
    design.weight_sum_one

/-! ## (I3): the Hadamard row sums of a projection -/

/-- A symmetric matrix reads its entries either way round. -/
theorem projection_apply_comm {projection : Matrix (Fin size) (Fin size) ℝ}
    (hsymmetric : projectionᵀ = projection) (rowIndex colIndex : Fin size) :
    projection colIndex rowIndex = projection rowIndex colIndex := by
  have hentry := congrFun (congrFun hsymmetric rowIndex) colIndex
  rwa [Matrix.transpose_apply] at hentry

/-- **(I3)**: the row sums of the entrywise square of a symmetric idempotent are
its own diagonal.  The row sum at `c` is the `(c,c)` entry of `P Pᵀ`, which is the
`(c,c)` entry of `P P`, which is `P_cc`.  No spectral theory, no positivity — just
idempotence read once. -/
theorem sum_sq_projectionRow_eq_diagonal
    {projection : Matrix (Fin size) (Fin size) ℝ} (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection) (rowIndex : Fin size) :
    ∑ colIndex : Fin size, projection rowIndex colIndex ^ 2 = projection rowIndex rowIndex := by
  have hsquareEntry : (projection * projection) rowIndex rowIndex
      = ∑ colIndex : Fin size, projection rowIndex colIndex ^ 2 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun colIndex _ => ?_
    rw [projection_apply_comm hsymmetric rowIndex colIndex, pow_two]
  rw [← hsquareEntry, hidempotent]

/-- **(I3) summed**: the total mass of the entrywise square of a symmetric
idempotent is its trace, hence its rank.  This is the form (I6) consumes. -/
theorem sum_sq_projectionEntry_eq_trace
    {projection : Matrix (Fin size) (Fin size) ℝ} (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection) :
    ∑ rowIndex : Fin size, ∑ colIndex : Fin size, projection rowIndex colIndex ^ 2
      = Matrix.trace projection :=
  Finset.sum_congr rfl fun rowIndex _ =>
    sum_sq_projectionRow_eq_diagonal hsymmetric hidempotent rowIndex

/-- **(I3) at a design's chart**: the row sums of the squared chart entries are the
leverage scores `P_cc = t_c |g_c|²`. -/
theorem sum_sq_projectionOfDesign_row_eq_weight_mul_leverage (design : WeightedDesign size rank)
    (rowIndex : Fin size) :
    ∑ colIndex : Fin size, projectionOfDesign design rowIndex colIndex ^ 2
      = design.weight rowIndex * leverageOf (design.atom rowIndex) := by
  rw [sum_sq_projectionRow_eq_diagonal (projectionOfDesign_transpose design)
    (projectionOfDesign_mul_self design) rowIndex, projectionOfDesign_diagonal]

/-- **(I3) summed, at a design's chart**: the total mass is the rank. -/
theorem sum_sq_projectionOfDesign_entry_eq_rank (design : WeightedDesign size rank) :
    ∑ rowIndex : Fin size, ∑ colIndex : Fin size, projectionOfDesign design rowIndex colIndex ^ 2
      = (rank : ℝ) := by
  rw [sum_sq_projectionEntry_eq_trace (projectionOfDesign_transpose design)
    (projectionOfDesign_mul_self design), trace_projectionOfDesign]

/-! ## The chart entry, squared -/

/-- **The square of a chart entry clears both weight roots**:
`P_cd² = t_c t_d ⟨g_c, g_d⟩²`.  Every even monomial in the chart is a polynomial in
the weights and the atom pairings; this is the rank-generic form of the identity
`Gtz.chartEntry_sq` states for the rank-three copy of the chart. -/
theorem sq_projectionOfDesign_apply (design : WeightedDesign size rank)
    (firstIndex secondIndex : Fin size) :
    projectionOfDesign design firstIndex secondIndex ^ 2
      = design.weight firstIndex * design.weight secondIndex
        * (design.atom firstIndex ⬝ᵥ design.atom secondIndex) ^ 2 := by
  have hfirstRoot := Real.mul_self_sqrt (design.weight_pos firstIndex).le
  have hsecondRoot := Real.mul_self_sqrt (design.weight_pos secondIndex).le
  calc projectionOfDesign design firstIndex secondIndex ^ 2
      = (Real.sqrt (design.weight firstIndex) * Real.sqrt (design.weight firstIndex))
          * (Real.sqrt (design.weight secondIndex) * Real.sqrt (design.weight secondIndex))
          * (design.atom firstIndex ⬝ᵥ design.atom secondIndex) ^ 2 := by
        rw [projectionOfDesign_apply]; ring
    _ = _ := by rw [hfirstRoot, hsecondRoot]

/-! ## Parseval, read as a quadratic form -/

/-- The rank-one atom acts on a probe by its own pairing: `⟨p, (g gᵀ) p⟩ = ⟨g, p⟩²`. -/
theorem dotProduct_atomMatrix_mulVec_self {dimension : ℕ} (atomVector probe : Fin dimension → ℝ) :
    probe ⬝ᵥ (atomMatrix atomVector *ᵥ probe) = (atomVector ⬝ᵥ probe) ^ 2 := by
  have hrow : ∀ rowIndex : Fin dimension, (atomMatrix atomVector *ᵥ probe) rowIndex
      = atomVector rowIndex * (atomVector ⬝ᵥ probe) := by
    intro rowIndex
    simp only [Matrix.mulVec, atomMatrix, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun colIndex _ => by ring
  have hcollapse : ∑ rowIndex : Fin dimension,
        probe rowIndex * (atomMatrix atomVector *ᵥ probe) rowIndex
      = (∑ rowIndex : Fin dimension, probe rowIndex * atomVector rowIndex)
        * (atomVector ⬝ᵥ probe) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun rowIndex _ => by rw [hrow rowIndex]; ring
  rw [dotProduct, hcollapse, ← dotProduct, dotProduct_comm probe atomVector, pow_two]

/-- **PARSEVAL AS A QUADRATIC FORM**: `Σ_d t_d ⟨g_c, g_d⟩² = |g_c|²`.  The weighted
atoms resolve the identity, so testing that resolution against `g_c` on both sides
turns the weighted sum of squared pairings into the leverage.  This is the step
(I5b) rests on, and the only place Parseval enters this file. -/
theorem sum_weight_mul_sq_atomPairing (design : WeightedDesign size rank) (atomIndex : Fin size) :
    ∑ otherIndex : Fin size,
        design.weight otherIndex * (design.atom atomIndex ⬝ᵥ design.atom otherIndex) ^ 2
      = leverageOf (design.atom atomIndex) := by
  have hquadratic : ∀ otherIndex : Fin size,
      design.weight otherIndex * (design.atom atomIndex ⬝ᵥ design.atom otherIndex) ^ 2
        = design.atom atomIndex
          ⬝ᵥ ((design.weight otherIndex • atomMatrix (design.atom otherIndex))
              *ᵥ design.atom atomIndex) := by
    intro otherIndex
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      dotProduct_atomMatrix_mulVec_self,
      dotProduct_comm (design.atom otherIndex) (design.atom atomIndex)]
  rw [Finset.sum_congr rfl fun otherIndex _ => hquadratic otherIndex, ← dotProduct_sum,
    ← Matrix.sum_mulVec, design.isParseval, Matrix.one_mulVec, leverageOf,
    ← dotProduct_self_eq_sum_sq]

/-- The weighted excess leverages sum to `rank - 1`: the trace identity, shifted. -/
theorem sum_weight_mul_leverage_sub_one (design : WeightedDesign size rank) :
    ∑ atomIndex : Fin size, design.weight atomIndex * (leverageOf (design.atom atomIndex) - 1)
      = (rank : ℝ) - 1 := by
  have hsplit : ∀ atomIndex : Fin size,
      design.weight atomIndex * (leverageOf (design.atom atomIndex) - 1)
        = design.weight atomIndex * leverageOf (design.atom atomIndex) - design.weight atomIndex :=
    fun atomIndex => by ring
  rw [Finset.sum_congr rfl fun atomIndex _ => hsplit atomIndex, Finset.sum_sub_distrib,
    sum_weight_mul_leverage design, design.weight_sum_one]

/-! ## (I5): the obstruction matrix -/

/-- **The obstruction matrix `kappa`**: the squared atom pairing minus the product
of the two excess leverages,

    `kappa_cd = ⟨g_c, g_d⟩² - (|g_c|² - 1)(|g_d|² - 1)` .

It is the design-side companion of the chart's Hadamard square — (I5a) below says
the weight congruence carries one to the other — and its pair sums are the second
elementary symmetric functions of the chart gap blocks. -/
noncomputable def chartObstruction (design : WeightedDesign size rank)
    (firstIndex secondIndex : Fin size) : ℝ :=
  (design.atom firstIndex ⬝ᵥ design.atom secondIndex) ^ 2
    - (leverageOf (design.atom firstIndex) - 1) * (leverageOf (design.atom secondIndex) - 1)

/-- The obstruction matrix is symmetric. -/
theorem chartObstruction_comm (design : WeightedDesign size rank)
    (firstIndex secondIndex : Fin size) :
    chartObstruction design firstIndex secondIndex
      = chartObstruction design secondIndex firstIndex := by
  rw [chartObstruction, chartObstruction, dotProduct_comm (design.atom firstIndex)]
  ring

/-- **(I5a)**: `D kappa D = P^{∘2} - w wᵀ`, entry by entry and INCLUDING the
diagonal, where `w_c = P_cc - t_c` is the chart gap's diagonal.

Both sides are `t_c t_d (⟨g_c,g_d⟩² - (|g_c|²-1)(|g_d|²-1))`: on the left because
that is the definition, on the right because `P_cd² = t_c t_d ⟨g_c,g_d⟩²`
(`sq_projectionOfDesign_apply`) and `w_c = t_c (|g_c|² - 1)`
(`projectionOfDesign_diagonal`).  So the identity is a rewriting, not a theorem
about designs — which is why it holds at every entry with no hypothesis. -/
theorem weight_mul_chartObstruction_eq (design : WeightedDesign size rank)
    (firstIndex secondIndex : Fin size) :
    design.weight firstIndex * design.weight secondIndex
        * chartObstruction design firstIndex secondIndex
      = projectionOfDesign design firstIndex secondIndex ^ 2
        - (projectionOfDesign design firstIndex firstIndex - design.weight firstIndex)
          * (projectionOfDesign design secondIndex secondIndex - design.weight secondIndex) := by
  rw [chartObstruction, sq_projectionOfDesign_apply, projectionOfDesign_diagonal,
    projectionOfDesign_diagonal]
  ring

/-- **(I5b), THE ROW-SUM LAW**: `Σ_d t_d kappa_cd = (2 - rank)|g_c|² + (rank - 1)`.

Parseval turns `Σ_d t_d ⟨g_c,g_d⟩²` into `|g_c|²` and the trace identity turns
`Σ_d t_d (|g_d|² - 1)` into `rank - 1`; what is left is arithmetic.

READ THE RIDER.  The right-hand side is design-INDEPENDENTLY constant in `c`
exactly at `rank = 2`, where the leverage coefficient `2 - rank` vanishes.  At every
other rank it is constant only on constant-leverage designs — which the named
polytopes all are, and random designs never are. -/
theorem sum_weight_mul_chartObstruction (design : WeightedDesign size rank)
    (atomIndex : Fin size) :
    ∑ otherIndex : Fin size, design.weight otherIndex * chartObstruction design atomIndex otherIndex
      = (2 - (rank : ℝ)) * leverageOf (design.atom atomIndex) + ((rank : ℝ) - 1) := by
  have hsplit : ∀ otherIndex : Fin size,
      design.weight otherIndex * chartObstruction design atomIndex otherIndex
        = design.weight otherIndex * (design.atom atomIndex ⬝ᵥ design.atom otherIndex) ^ 2
          - (leverageOf (design.atom atomIndex) - 1)
            * (design.weight otherIndex * (leverageOf (design.atom otherIndex) - 1)) := by
    intro otherIndex
    rw [chartObstruction]
    ring
  rw [Finset.sum_congr rfl fun otherIndex _ => hsplit otherIndex, Finset.sum_sub_distrib,
    sum_weight_mul_sq_atomPairing design atomIndex, ← Finset.mul_sum,
    sum_weight_mul_leverage_sub_one design]
  ring

/-- **(I5c), THE TOTAL MASS**: `tᵀ kappa t = -(rank² - 3 rank + 1)`, a function of the
rank alone.  Weighting the row-sum law by `t_c` and summing collapses the leverage
term through the trace identity a second time.

The constant is `-1` at `rank = 3` and `+1` at `rank = 2`, and it is the same
`rank² - 3 rank + 1` that appears in (I6) — not a coincidence: both are the
`kappa`-mass of the whole design, once weighted and once cut down to pairs. -/
theorem sum_weight_mul_weight_mul_chartObstruction (design : WeightedDesign size rank) :
    ∑ firstIndex : Fin size, ∑ secondIndex : Fin size,
        design.weight firstIndex * design.weight secondIndex
          * chartObstruction design firstIndex secondIndex
      = -((rank : ℝ) ^ 2 - 3 * rank + 1) := by
  have hrow : ∀ firstIndex : Fin size,
      ∑ secondIndex : Fin size, design.weight firstIndex * design.weight secondIndex
          * chartObstruction design firstIndex secondIndex
        = design.weight firstIndex
          * ((2 - (rank : ℝ)) * leverageOf (design.atom firstIndex) + ((rank : ℝ) - 1)) := by
    intro firstIndex
    rw [← sum_weight_mul_chartObstruction design firstIndex, Finset.mul_sum]
    exact Finset.sum_congr rfl fun secondIndex _ => by ring
  have hexpand : ∀ firstIndex : Fin size,
      design.weight firstIndex
          * ((2 - (rank : ℝ)) * leverageOf (design.atom firstIndex) + ((rank : ℝ) - 1))
        = (2 - (rank : ℝ)) * (design.weight firstIndex * leverageOf (design.atom firstIndex))
          + ((rank : ℝ) - 1) * design.weight firstIndex :=
    fun firstIndex => by ring
  rw [Finset.sum_congr rfl fun firstIndex _ => hrow firstIndex,
    Finset.sum_congr rfl fun firstIndex _ => hexpand firstIndex, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_weight_mul_leverage design, design.weight_sum_one]
  ring

/-! ## (I4): the second symmetric function of a chart gap block -/

/-- **The `2 x 2` principal minor of the chart gap** at an ordered pair of atoms:
`w_c w_d - P_cd²`, where `w_c = P_cc - t_c`.  Written on the raw matrix and the raw
weight vector, so that it reads at a chart point with no design behind it. -/
noncomputable def chartGapPairMinor (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (firstIndex secondIndex : Fin size) : ℝ :=
  (projection firstIndex firstIndex - weight firstIndex)
      * (projection secondIndex secondIndex - weight secondIndex)
    - projection firstIndex secondIndex ^ 2

/-- **(I4), the minor reading.**  The pair expression IS the determinant of the
`2 x 2` principal block of `W = P - diag t` at two distinct atoms — the off-diagonal
weight contributes nothing and the symmetry of the chart turns `P_cd P_dc` into
`P_cd²`.  So the pair sums below are genuinely the second elementary symmetric
functions of the gap blocks, not a formal expression named after one. -/
theorem det_chartGapPair_eq {projection : Matrix (Fin size) (Fin size) ℝ}
    (hsymmetric : projectionᵀ = projection) (weight : Fin size → ℝ)
    {firstIndex secondIndex : Fin size} (hdistinct : firstIndex ≠ secondIndex) :
    ((projection - Matrix.diagonal weight).submatrix ![firstIndex, secondIndex]
        ![firstIndex, secondIndex]).det
      = chartGapPairMinor projection weight firstIndex secondIndex := by
  have hdiagonalEntry : ∀ atomIndex : Fin size,
      (projection - Matrix.diagonal weight) atomIndex atomIndex
        = projection atomIndex atomIndex - weight atomIndex := by
    intro atomIndex
    rw [Matrix.sub_apply, Matrix.diagonal_apply_eq]
  have hupperEntry : (projection - Matrix.diagonal weight) firstIndex secondIndex
      = projection firstIndex secondIndex := by
    rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hdistinct, sub_zero]
  have hlowerEntry : (projection - Matrix.diagonal weight) secondIndex firstIndex
      = projection firstIndex secondIndex := by
    rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ (Ne.symm hdistinct), sub_zero,
      projection_apply_comm hsymmetric]
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hdiagonalEntry, hdiagonalEntry, hupperEntry, hlowerEntry, chartGapPairMinor, pow_two]

/-- **The second elementary symmetric function of a chart gap block.**  The sum runs
over ORDERED pairs of distinct atoms of the subset, which counts each unordered pair
twice — hence the halving.  At rank three this is `Gtz.chartGapWeightedMinorSum`'s
unweighted sibling; that file's rank-three leg translation is not re-derived here. -/
noncomputable def chartGapPairMinorSum (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (chosenSubset : Finset (Fin size)) : ℝ :=
  2⁻¹ * ∑ pair ∈ chosenSubset.offDiag, chartGapPairMinor projection weight pair.1 pair.2

/-! ## The two counting lemmas (I6) needs -/

/-- Splitting a full double sum into its diagonal and its off-diagonal parts. -/
theorem sum_offDiag_eq_sum_sub_diagonal (summand : Fin size → Fin size → ℝ) :
    ∑ pair ∈ (Finset.univ : Finset (Fin size)).offDiag, summand pair.1 pair.2
      = (∑ rowIndex : Fin size, ∑ colIndex : Fin size, summand rowIndex colIndex)
        - ∑ rowIndex : Fin size, summand rowIndex rowIndex := by
  classical
  have hdiagSum : ∑ pair ∈ (Finset.univ : Finset (Fin size)).diag, summand pair.1 pair.2
      = ∑ rowIndex : Fin size, summand rowIndex rowIndex := by
    rw [Finset.diag_eq_filter, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun rowIndex _ => ?_
    rw [Finset.sum_ite_eq (Finset.univ : Finset (Fin size)) rowIndex
      fun colIndex => summand rowIndex colIndex]
    rw [if_pos (Finset.mem_univ rowIndex)]
  have hsplit : ∑ pair ∈ (Finset.univ : Finset (Fin size)).diag, summand pair.1 pair.2
        + ∑ pair ∈ (Finset.univ : Finset (Fin size)).offDiag, summand pair.1 pair.2
      = ∑ rowIndex : Fin size, ∑ colIndex : Fin size, summand rowIndex colIndex := by
    rw [← Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.diag_union_offDiag,
      Finset.sum_product]
  rw [hdiagSum] at hsplit
  linarith

/-- **THE TRIPLE DOUBLE COUNT.**  Every ordered pair of distinct atoms lies in
exactly `size - 2` of the three-element subsets, so summing any pair function over
the pairs inside each triple and then over the triples multiplies the total by
`size - 2`.

The real subtraction is correct at every size, including the degenerate ones: below
two atoms there are no ordered distinct pairs and both sides vanish, and at exactly
two atoms there are no triples and both sides vanish again. -/
theorem sum_powersetCard_three_offDiag (summand : Fin size → Fin size → ℝ) :
    ∑ chosenSubset ∈ (Finset.univ : Finset (Fin size)).powersetCard 3,
        ∑ pair ∈ chosenSubset.offDiag, summand pair.1 pair.2
      = ((size : ℝ) - 2)
        * ∑ pair ∈ (Finset.univ : Finset (Fin size)).offDiag, summand pair.1 pair.2 := by
  classical
  have hrestrict : ∀ chosenSubset ∈ (Finset.univ : Finset (Fin size)).powersetCard 3,
      ∑ pair ∈ chosenSubset.offDiag, summand pair.1 pair.2
        = ∑ pair ∈ (Finset.univ : Finset (Fin size)).offDiag,
            if pair.1 ∈ chosenSubset ∧ pair.2 ∈ chosenSubset then summand pair.1 pair.2 else 0 := by
    intro chosenSubset _
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext pair
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
    tauto
  have hcount : ∀ pair ∈ (Finset.univ : Finset (Fin size)).offDiag,
      ∑ chosenSubset ∈ (Finset.univ : Finset (Fin size)).powersetCard 3,
          (if pair.1 ∈ chosenSubset ∧ pair.2 ∈ chosenSubset then summand pair.1 pair.2 else 0)
        = ((size : ℝ) - 2) * summand pair.1 pair.2 := by
    intro pair hmem
    have hdistinct : pair.1 ≠ pair.2 := (Finset.mem_offDiag.mp hmem).2.2
    have hpairCard : ({pair.1, pair.2} : Finset (Fin size)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hdistinct), Finset.card_singleton]
    have hfilterEq : ((Finset.univ : Finset (Fin size)).powersetCard 3).filter
          (fun chosenSubset => pair.1 ∈ chosenSubset ∧ pair.2 ∈ chosenSubset)
        = ((Finset.univ : Finset (Fin size)).powersetCard 3).filter
          (fun chosenSubset => ({pair.1, pair.2} : Finset (Fin size)) ⊆ chosenSubset) := by
      refine Finset.filter_congr fun chosenSubset _ => ?_
      simp [Finset.insert_subset_iff]
    have hcardFilter : (((Finset.univ : Finset (Fin size)).powersetCard 3).filter
        (fun chosenSubset => pair.1 ∈ chosenSubset ∧ pair.2 ∈ chosenSubset)).card = size - 2 := by
      rw [hfilterEq, Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _)
        (by rw [hpairCard]; norm_num), hpairCard, Finset.card_univ, Fintype.card_fin]
      norm_num
    have hsizeTwo : 2 ≤ size := by
      have hfirstLt := pair.1.isLt
      have hsecondLt := pair.2.isLt
      have hvalDistinct : (pair.1 : ℕ) ≠ (pair.2 : ℕ) := fun heq => hdistinct (Fin.ext heq)
      omega
    have hcast : ((size - 2 : ℕ) : ℝ) = (size : ℝ) - 2 := by
      have hsubtraction := Nat.cast_sub (R := ℝ) hsizeTwo
      simpa using hsubtraction
    rw [← Finset.sum_filter, Finset.sum_const, hcardFilter, nsmul_eq_mul, hcast]
  rw [Finset.sum_congr rfl hrestrict, Finset.sum_comm, Finset.sum_congr rfl hcount,
    ← Finset.mul_sum]

/-! ## (I6): the triple sum of the second symmetric functions -/

/-- The off-diagonal mass of the pair minors, in closed form.  The diagonal part of
the double sum is what turns the naive `(rank-1)²` into the stated constant, and the
Hadamard row sums (I3) are what evaluate the squared-entry mass at `rank`. -/
theorem sum_offDiag_chartGapPairMinor
    {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
    (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection)
    (htraceRank : Matrix.trace projection = (rank : ℝ))
    (hweightSumOne : ∑ atomIndex : Fin size, weight atomIndex = 1) :
    ∑ pair ∈ (Finset.univ : Finset (Fin size)).offDiag,
        chartGapPairMinor projection weight pair.1 pair.2
      = ((rank : ℝ) - 1) ^ 2 - rank
        + ∑ atomIndex : Fin size,
            weight atomIndex * (2 * projection atomIndex atomIndex - weight atomIndex) := by
  have hgapSum : ∑ atomIndex : Fin size, (projection atomIndex atomIndex - weight atomIndex)
      = (rank : ℝ) - 1 := by
    rw [Finset.sum_sub_distrib, hweightSumOne, ← htraceRank]
    rfl
  have hfullSum : ∑ rowIndex : Fin size, ∑ colIndex : Fin size,
      chartGapPairMinor projection weight rowIndex colIndex
      = ((rank : ℝ) - 1) ^ 2 - rank := by
    have hrow : ∀ rowIndex : Fin size,
        ∑ colIndex : Fin size, chartGapPairMinor projection weight rowIndex colIndex
          = (projection rowIndex rowIndex - weight rowIndex) * ((rank : ℝ) - 1)
            - projection rowIndex rowIndex := by
      intro rowIndex
      simp only [chartGapPairMinor]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hgapSum,
        sum_sq_projectionRow_eq_diagonal hsymmetric hidempotent rowIndex]
    have htraceSum : ∑ rowIndex : Fin size, projection rowIndex rowIndex = (rank : ℝ) := htraceRank
    rw [Finset.sum_congr rfl fun rowIndex _ => hrow rowIndex, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hgapSum, htraceSum]
    ring
  have hdiagonalSum : ∑ rowIndex : Fin size,
      chartGapPairMinor projection weight rowIndex rowIndex
      = -∑ atomIndex : Fin size,
          weight atomIndex * (2 * projection atomIndex atomIndex - weight atomIndex) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun rowIndex _ => ?_
    simp only [chartGapPairMinor]
    ring
  rw [sum_offDiag_eq_sum_sub_diagonal, hfullSum, hdiagonalSum]
  ring

/-- **(I6), IN THE GENERAL FORM.**  Summing the second elementary symmetric function
over ALL three-element subsets gives

    `((size - 2)/2) * ((rank - 1)² - rank + Σ_c t_c (2 P_cc - t_c))` .

CORRECTING THE CAMPAIGN BRIEF, which states this with the constant `1` in place of
`(rank - 1)² - rank`.  The two agree exactly at `rank = 3`, where
`(3-1)² - 3 = 1`, and nowhere else that matters: at `rank = 2` the constant is `-1`,
and the brief's form was measured to fail at every `rank ≠ 3` cell.  The general
constant is `rank² - 3 rank + 1`, the same one (I5c) produces. -/
theorem sum_chartGapPairMinorSum_powersetCard_three
    {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
    (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection)
    (htraceRank : Matrix.trace projection = (rank : ℝ))
    (hweightSumOne : ∑ atomIndex : Fin size, weight atomIndex = 1) :
    ∑ chosenSubset ∈ (Finset.univ : Finset (Fin size)).powersetCard 3,
        chartGapPairMinorSum projection weight chosenSubset
      = ((size : ℝ) - 2) / 2
        * (((rank : ℝ) - 1) ^ 2 - rank
          + ∑ atomIndex : Fin size,
              weight atomIndex * (2 * projection atomIndex atomIndex - weight atomIndex)) := by
  simp only [chartGapPairMinorSum]
  rw [← Finset.mul_sum, sum_powersetCard_three_offDiag,
    sum_offDiag_chartGapPairMinor hsymmetric hidempotent htraceRank hweightSumOne]
  ring

/-- **(I6) at a design's chart**, with the correction term read on the atoms:
`Σ_c t_c (2 P_cc - t_c) = Σ_c t_c² (2|g_c|² - 1)`. -/
theorem sum_chartGapPairMinorSum_powersetCard_three_of_design (design : WeightedDesign size rank) :
    ∑ chosenSubset ∈ (Finset.univ : Finset (Fin size)).powersetCard 3,
        chartGapPairMinorSum (projectionOfDesign design) design.weight chosenSubset
      = ((size : ℝ) - 2) / 2
        * (((rank : ℝ) - 1) ^ 2 - rank
          + ∑ atomIndex : Fin size,
              design.weight atomIndex ^ 2 * (2 * leverageOf (design.atom atomIndex) - 1)) := by
  have hcorrection : ∀ atomIndex : Fin size,
      design.weight atomIndex
          * (2 * projectionOfDesign design atomIndex atomIndex - design.weight atomIndex)
        = design.weight atomIndex ^ 2 * (2 * leverageOf (design.atom atomIndex) - 1) := by
    intro atomIndex
    rw [projectionOfDesign_diagonal]
    ring
  rw [sum_chartGapPairMinorSum_powersetCard_three (projectionOfDesign_transpose design)
    (projectionOfDesign_mul_self design) (trace_projectionOfDesign design) design.weight_sum_one,
    Finset.sum_congr rfl fun atomIndex _ => hcorrection atomIndex]

/-- **(I6) UNDER ALL-HEAVY, AT RANK THREE**: the total is strictly positive.  Every
correction term is nonnegative once no atom is light, and the rank-three constant
`(3-1)² - 3` is `1`.

DISCLOSURE, so the reach is not overstated: this says only that SOME triple has a
positive second symmetric function, and that is measured to be exactly the half of
the rank-three reformulation which carries no information about the obstruction.  At
both known rank-three counterexamples over `ℂ` — the trine and the Hesse SIC — EVERY
triple passes the `e_2` test and NONE passes `e_3`.  The whole obstruction is `e_3`. -/
theorem sum_chartGapPairMinorSum_powersetCard_three_pos_of_allHeavy
    (design : WeightedDesign size 3) (hsizeThree : 2 < size)
    (hallHeavy : ∀ atomIndex : Fin size, 1 ≤ leverageOf (design.atom atomIndex)) :
    0 < ∑ chosenSubset ∈ (Finset.univ : Finset (Fin size)).powersetCard 3,
        chartGapPairMinorSum (projectionOfDesign design) design.weight chosenSubset := by
  have hsizeCast : (2 : ℝ) < (size : ℝ) := by exact_mod_cast hsizeThree
  have hcorrectionNonneg : (0 : ℝ) ≤ ∑ atomIndex : Fin size,
      design.weight atomIndex ^ 2 * (2 * leverageOf (design.atom atomIndex) - 1) := by
    refine Finset.sum_nonneg fun atomIndex _ => ?_
    have hheavy := hallHeavy atomIndex
    nlinarith [sq_nonneg (design.weight atomIndex)]
  rw [sum_chartGapPairMinorSum_powersetCard_three_of_design design]
  have hconstant : (((3 : ℕ) : ℝ) - 1) ^ 2 - ((3 : ℕ) : ℝ) = 1 := by norm_num
  rw [hconstant]
  have hfactor : (0 : ℝ) < ((size : ℝ) - 2) / 2 := by linarith
  nlinarith [hfactor, hcorrectionNonneg]

/-- **SOME TRIPLE HAS A POSITIVE SECOND SYMMETRIC FUNCTION**, at every all-heavy
rank-three design.  The (I6) total is positive, so not every summand can fail. -/
theorem exists_pos_chartGapPairMinorSum_of_allHeavy (design : WeightedDesign size 3)
    (hsizeThree : 2 < size)
    (hallHeavy : ∀ atomIndex : Fin size, 1 ≤ leverageOf (design.atom atomIndex)) :
    ∃ chosenSubset ∈ (Finset.univ : Finset (Fin size)).powersetCard 3,
      0 < chartGapPairMinorSum (projectionOfDesign design) design.weight chosenSubset := by
  have htotal :=
    sum_chartGapPairMinorSum_powersetCard_three_pos_of_allHeavy design hsizeThree hallHeavy
  have hzeroSum : ∑ _chosenSubset ∈ (Finset.univ : Finset (Fin size)).powersetCard 3, (0 : ℝ) = 0 :=
    Finset.sum_const_zero
  rw [← hzeroSum] at htotal
  exact Finset.exists_lt_of_sum_lt htotal

/-! ## (I7) and (I8): the shifted minor sum carries no information about the design -/

/-- The coefficients of `(1 + a X)^n` are the binomial ones.  Mathlib has the
special case `a = 1` (`Polynomial.coeff_one_add_X_pow`) and the monic case
(`Polynomial.coeff_X_add_C_pow`); neither covers a general scalar in the linear term,
and factoring one out is not available because the scalar may vanish. -/
theorem coeff_one_add_C_mul_X_pow (scalar : ℝ) (exponent degree : ℕ) :
    ((1 + Polynomial.C scalar * Polynomial.X) ^ exponent).coeff degree
      = (exponent.choose degree : ℝ) * scalar ^ degree := by
  have hexpand : (1 + Polynomial.C scalar * Polynomial.X) ^ exponent
      = ∑ splitIndex ∈ Finset.range (exponent + 1),
          Polynomial.C ((exponent.choose splitIndex : ℝ) * scalar ^ splitIndex)
            * Polynomial.X ^ splitIndex := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun splitIndex _ => ?_
    rw [mul_pow, one_pow, mul_one, ← Polynomial.C_pow, mul_right_comm,
      ← Polynomial.C_eq_natCast, ← Polynomial.C_mul, mul_comm (scalar ^ splitIndex)]
  have hterm : ∀ splitIndex ∈ Finset.range (exponent + 1),
      (Polynomial.C ((exponent.choose splitIndex : ℝ) * scalar ^ splitIndex)
          * Polynomial.X ^ splitIndex).coeff degree
        = if degree = splitIndex then (exponent.choose splitIndex : ℝ) * scalar ^ splitIndex
            else 0 := by
    intro splitIndex _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hmatch : degree = splitIndex
    · rw [if_pos hmatch, if_pos hmatch, mul_one]
    · rw [if_neg hmatch, if_neg hmatch, mul_zero]
  rw [hexpand, Polynomial.finsetSum_coeff, Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq (Finset.range (exponent + 1)) degree
      fun splitIndex => (exponent.choose splitIndex : ℝ) * scalar ^ splitIndex]
  by_cases hsmall : degree ∈ Finset.range (exponent + 1)
  · rw [if_pos hsmall]
  · rw [if_neg hsmall, Nat.choose_eq_zero_of_lt (by simpa using hsmall)]
    norm_num

/-- Evaluating the minor generating matrix at a real point undoes the coefficient
embedding: `(1 + X · M̃)|_{X = y} = 1 + y · M`. -/
theorem map_eval_one_add_X_smul {dimension : ℕ} (target : Matrix (Fin dimension) (Fin dimension) ℝ)
    (point : ℝ) :
    (1 + (Polynomial.X : Polynomial ℝ) • target.map Polynomial.C).map (Polynomial.eval point)
      = 1 + point • target := by
  ext rowIndex colIndex
  by_cases hdiagonal : rowIndex = colIndex
  · subst hdiagonal
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply,
      smul_eq_mul, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C]
  · simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply_ne hdiagonal,
      Matrix.smul_apply, smul_eq_mul, Polynomial.eval_add, Polynomial.eval_zero,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]

/-- **THE SHIFTED MINOR GENERATING FUNCTION**, over `ℝ[X]`:

    `det(1 + X (P - s·1)) = (1 - sX)^{size - rank} (1 + (1-s)X)^rank` .

`Gtz.det_one_add_smul_shifted_real` proves the same factorisation for a REAL
scalar, off the one degenerate value where the factoring divisor vanishes.  That
proof does not transport to `ℝ[X]` directly — `1 - sX` is not a unit there — so the
polynomial identity is obtained instead by evaluating both sides at every real point
off that single value and invoking that a real polynomial with infinitely many roots
is zero.

`Gtz.LinAlg.ProjectionForm`'s own header announces a theorem of this shape and a
`sum_det_shiftedProjectionMinors_designIndependent` following it.  NEITHER EXISTS IN
THAT FILE — the header is stale, and the two statements it describes are the one
above and `sum_det_shiftedChartMinors_eq` below. -/
theorem det_one_add_X_smul_shifted (design : WeightedDesign size rank) (shift : ℝ) :
    (1 + (Polynomial.X : Polynomial ℝ)
        • (projectionOfDesign design - shift • 1).map Polynomial.C).det
      = (1 + Polynomial.C (-shift) * Polynomial.X) ^ (size - rank)
        * (1 + Polynomial.C (1 - shift) * Polynomial.X) ^ rank := by
  have hdegenerateFinite : {point : ℝ | 1 - shift * point = 0}.Finite := by
    refine Set.Subsingleton.finite fun firstPoint hfirst secondPoint hsecond => ?_
    simp only [Set.mem_setOf_eq] at hfirst hsecond
    have hshiftNe : shift ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hfirst
      norm_num at hfirst
    have hscaled : shift * firstPoint = shift * secondPoint := by linarith
    exact mul_left_cancel₀ hshiftNe hscaled
  have hagree : {point : ℝ | 1 - shift * point = 0}ᶜ
      ⊆ {point : ℝ | Polynomial.eval point
            (1 + (Polynomial.X : Polynomial ℝ)
              • (projectionOfDesign design - shift • 1).map Polynomial.C).det
          = Polynomial.eval point ((1 + Polynomial.C (-shift) * Polynomial.X) ^ (size - rank)
              * (1 + Polynomial.C (1 - shift) * Polynomial.X) ^ rank)} := by
    intro point hpoint
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hpoint
    simp only [Set.mem_setOf_eq]
    have hmapDet := RingHom.map_det (Polynomial.evalRingHom point)
      (1 + (Polynomial.X : Polynomial ℝ)
        • (projectionOfDesign design - shift • 1).map Polynomial.C)
    simp only [Polynomial.coe_evalRingHom, RingHom.mapMatrix_apply] at hmapDet
    rw [hmapDet, map_eval_one_add_X_smul,
      det_one_add_smul_shifted_real design shift point hpoint]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  exact Polynomial.eq_of_infinite_eval_eq _ _
    (Set.Infinite.mono hagree hdegenerateFinite.infinite_compl)

/-- **(I7) + (I8), THE DESIGN-INDEPENDENT AGGREGATE.**  For every scalar shift the
sum of the `rank`-subset principal minors of `P - s·1` is a function of
`(size, rank, s)` ALONE:

    `Σ_{|C| = rank} det(P[C] - s·1) = Σ_j C(size-rank, j) (-s)^j C(rank, rank-j) (1-s)^{rank-j}` .

This is the identity the campaign calls the UNIFORM INVARIANT, in chart form.  At
uniform weights `t ≡ 1/size` the shift `s = 1/size` makes `P - s·1` exactly the chart
gap `W`, so the left side is `Σ det W[C]`, and the right side has no design in it —
the averaging functional is dead by identity, not by counterexample.

The design enters the proof only through the factorisation of the generating
function, i.e. only through `PᵀP = P` and `trace P = rank`; nothing about the atoms
survives.  That is also why the identity is FIELD-INDEPENDENT, which the campaign
verified separately over `ℂ`.

At NON-uniform weights the aggregate is NOT design-independent — the gap is then
`P - diag t` and no scalar shift presents it — and that failure was measured
(the `(6,3)` split tetrahedron gives `-64` against the uniform `-56`). -/
theorem sum_det_shiftedChartMinors_eq (design : WeightedDesign size rank) (shift : ℝ) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
        ((projectionOfDesign design - shift • 1).submatrix
            (Subtype.val : { c // c ∈ selected } → Fin size)
            (Subtype.val : { c // c ∈ selected } → Fin size)).det
      = ∑ splitIndex ∈ Finset.range (rank + 1),
          ((size - rank).choose splitIndex : ℝ) * (-shift) ^ splitIndex
            * ((rank.choose (rank - splitIndex) : ℝ) * (1 - shift) ^ (rank - splitIndex)) := by
  rw [← Matrix.coeff_det_one_add_X_smul_eq_sum_minors (projectionOfDesign design - shift • 1) rank,
    det_one_add_X_smul_shifted, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun splitIndex _ => ?_
  rw [coeff_one_add_C_mul_X_pow, coeff_one_add_C_mul_X_pow]

/-- **THE `(6,3)` ANCHOR.**  At the open cell, with uniform weights, the chart
aggregate is `-7/27` at EVERY design.  Scaled by `size^rank = 216` this is the
campaign's `-56`, the number the octahedron reproduces as `8·8 + 12·(-10)` and the
icosahedron as `10·(-28/5)`. -/
theorem sum_det_shiftedChartMinors_sixThree (design : WeightedDesign 6 3) :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        ((projectionOfDesign design - ((6 : ℝ)⁻¹) • 1).submatrix
            (Subtype.val : { c // c ∈ selected } → Fin 6)
            (Subtype.val : { c // c ∈ selected } → Fin 6)).det
      = -(7 / 27) := by
  rw [sum_det_shiftedChartMinors_eq design ((6 : ℝ)⁻¹)]
  norm_num [Finset.sum_range_succ]

/-! ## (I8) on the atoms: the same invariant read on `S_C - 1` -/

/-- A design has at least one atom: an empty index set carries no weights, so the
weight sum would be zero rather than one. -/
theorem size_pos_of_design (design : WeightedDesign size rank) : 0 < size := by
  by_contra hnonpositive
  have hsizeZero : size = 0 := Nat.le_zero.mp (not_lt.mp hnonpositive)
  subst hsizeZero
  have hweightSum := design.weight_sum_one
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hweightSum
  exact absurd hweightSum (by norm_num)

/-- **The square transpose flip, at determinant level**: `det(M Mᵀ - 1) = det(Mᵀ M - 1)`
for a SQUARE `M`.  Both sides are `(-1)^size` times a Weinstein–Aronszajn determinant,
and those two agree by `Matrix.det_one_add_mul_comm`.  This is the determinant
sibling of `Gtz.posSemidef_transpose_mul_sub_one_comm`, which the repository already
carries at the level of positive semidefiniteness. -/
theorem det_mul_transpose_sub_one_comm {dimension : ℕ}
    (square : Matrix (Fin dimension) (Fin dimension) ℝ) :
    (square * squareᵀ - 1).det = (squareᵀ * square - 1).det := by
  have hshapeLeft : (1 : Matrix (Fin dimension) (Fin dimension) ℝ) + (-square) * squareᵀ
      = -(square * squareᵀ - 1) := by
    rw [neg_mul, neg_sub, sub_eq_add_neg]
  have hshapeRight : (1 : Matrix (Fin dimension) (Fin dimension) ℝ) + squareᵀ * (-square)
      = -(squareᵀ * square - 1) := by
    rw [mul_neg, neg_sub, sub_eq_add_neg]
  have hweinstein := Matrix.det_one_add_mul_comm (-square) squareᵀ
  rw [hshapeLeft, hshapeRight, Matrix.det_neg, Matrix.det_neg, Fintype.card_fin] at hweinstein
  exact mul_left_cancel₀ (pow_ne_zero dimension (by norm_num : (-1 : ℝ) ≠ 0)) hweinstein

/-- **THE PER-SUBSET RESCALING AT A UNIFORM WEIGHT.**  A `rank`-block of the chart
gap and the selected atom sum carry the same determinant up to the weight product:

    `det(P[C] - (1/size)·1) = (1/size)^rank · det(S_C - 1)` .

Three shipped steps and one new one: reindex the subtype block along the subset's
order embedding (`Matrix.det_submatrix_equiv_self`), read the scalar shift as the
weight diagonal (uniformity), apply the positive-diagonal congruence
(`Gtz.det_projectionBlock_sub_weightDiagonal`), and flip the square transpose
(`det_mul_transpose_sub_one_comm`). -/
theorem det_shiftedChartBlock_eq_det_subsetSum_sub_one (design : WeightedDesign size rank)
    (huniform : ∀ atomIndex : Fin size, design.weight atomIndex = ((size : ℝ))⁻¹)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) :
    ((projectionOfDesign design - ((size : ℝ))⁻¹ • 1).submatrix
        (Subtype.val : { c // c ∈ selected } → Fin size)
        (Subtype.val : { c // c ∈ selected } → Fin size)).det
      = ((size : ℝ))⁻¹ ^ rank * (subsetSum design selected - 1).det := by
  classical
  have hreindex : ((projectionOfDesign design - ((size : ℝ))⁻¹ • 1).submatrix
        (Subtype.val : { c // c ∈ selected } → Fin size)
        (Subtype.val : { c // c ∈ selected } → Fin size)).det
      = ((projectionOfDesign design - ((size : ℝ))⁻¹ • 1).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)).det := by
    rw [← Matrix.det_submatrix_equiv_self (selected.orderIsoOfFin hcard).toEquiv,
      Matrix.submatrix_submatrix]
    rfl
  have hblockShape : (projectionOfDesign design - ((size : ℝ))⁻¹ • 1).submatrix
        (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)
      = (projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard)
        - Matrix.diagonal
            (fun selectedIndex => design.weight (selected.orderEmbOfFin hcard selectedIndex)) := by
    ext leftIndex rightIndex
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.diagonal_apply, huniform]
    by_cases hdiagonal : leftIndex = rightIndex
    · subst hdiagonal
      rw [Matrix.one_apply_eq, if_pos rfl, mul_one]
    · rw [Matrix.one_apply_ne (fun hcollide =>
        hdiagonal ((selected.orderEmbOfFin hcard).injective hcollide)), if_neg hdiagonal, mul_zero]
  have hweightProduct : ∏ selectedIndex : Fin rank,
      design.weight (selected.orderEmbOfFin hcard selectedIndex) = ((size : ℝ))⁻¹ ^ rank := by
    rw [Finset.prod_congr rfl fun selectedIndex _ =>
      huniform (selected.orderEmbOfFin hcard selectedIndex), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have himage : Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  rw [hreindex, hblockShape, det_projectionBlock_sub_weightDiagonal, hweightProduct,
    det_mul_transpose_sub_one_comm,
    transpose_mul_selectedAtomRows design _ (selected.orderEmbOfFin hcard).injective, himage]

/-- **(I8) ON THE ATOMS.**  At a uniform weight the sum over `rank`-subsets of
`det(S_C - 1)` is a function of `(size, rank)` ALONE — the campaign's UNIFORM
INVARIANT in the form the brief states it, with the design-free right-hand side
inherited from `sum_det_shiftedChartMinors_eq`. -/
theorem sum_det_subsetSum_sub_one_uniform (design : WeightedDesign size rank)
    (huniform : ∀ atomIndex : Fin size, design.weight atomIndex = ((size : ℝ))⁻¹) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
        (subsetSum design selected - 1).det
      = (size : ℝ) ^ rank
        * ∑ splitIndex ∈ Finset.range (rank + 1),
            ((size - rank).choose splitIndex : ℝ) * (-((size : ℝ))⁻¹) ^ splitIndex
              * ((rank.choose (rank - splitIndex) : ℝ)
                * (1 - ((size : ℝ))⁻¹) ^ (rank - splitIndex)) := by
  have hsizeNe : ((size : ℝ)) ≠ 0 := by
    have hsizePos : (0 : ℝ) < (size : ℝ) := by exact_mod_cast size_pos_of_design design
    exact ne_of_gt hsizePos
  have hscaleBack : ∀ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
      (subsetSum design selected - 1).det
        = (size : ℝ) ^ rank
          * ((projectionOfDesign design - ((size : ℝ))⁻¹ • 1).submatrix
              (Subtype.val : { c // c ∈ selected } → Fin size)
              (Subtype.val : { c // c ∈ selected } → Fin size)).det := by
    intro selected hmem
    rw [det_shiftedChartBlock_eq_det_subsetSum_sub_one design huniform
      (Finset.mem_powersetCard.mp hmem).2, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hsizeNe, one_pow, one_mul]
  rw [Finset.sum_congr rfl hscaleBack, ← Finset.mul_sum,
    sum_det_shiftedChartMinors_eq design ((size : ℝ))⁻¹]

/-- **THE `(6,3)` INVARIANT IS `-56`, AT EVERY UNIFORM DESIGN.**  The campaign's
cross-checks read this number off two very different designs: the octahedron as
`8·8 + 12·(-10)` and the icosahedron as `10·(-28/5)`.  Neither computation is needed
— the aggregate cannot see the design at all.

READ THE SCOPE.  This says the averaging functional over all twenty triples is
design-independent at the OPEN cell, which is exactly why no averaging argument can
decide it: the functional carries zero information.  It is a no-go, not a step. -/
theorem sum_det_subsetSum_sub_one_sixThree (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = ((6 : ℝ))⁻¹) :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        (subsetSum design selected - 1).det = -56 := by
  rw [sum_det_subsetSum_sub_one_uniform design huniform]
  norm_num [Finset.sum_range_succ]

end Gtz
