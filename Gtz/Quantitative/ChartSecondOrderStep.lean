/-
# The step, the curvature, and the compression form

`Gtz.Quantitative.ChartSecondOrder` names three things it does not carry, and this
file carries them.

## 1.  The step, DERIVED rather than supplied

`Gtz.chartObjective_lt_of_perturbedWeight` and
`Gtz.SixThreeCrux.exists_tight_annihilated_of_flatDirection` each ask their caller for a
nonzero step, for feasibility of the moved weights at that step, and for the
inactive-block condition `hstepSmall` at that step.  Their own docstring says the last is
"SUPPLIED here rather than derived".

`Gtz.exists_pos_step_feasible_and_gapPreserving` derives all three at once, at any chart
point whose weights are strictly positive.  The construction is a finite minimum and
nothing else.  The shipped `Gtz.exists_pos_le_forall_mem` turns the atoms' positive
weights into one floor and the inactive blocks' strictly positive gaps into another; the
shipped `Gtz.chartWeightCap` caps the direction's first-order effect uniformly over every
block and every unit vector at once; the step is the smaller floor divided by one more
than the cap.  No continuity, no compactness, no limit, and no smallness hypothesis
smuggled in as a hypothesis on the caller.

The consumer form is `Gtz.SixThreeCrux.exists_tight_annihilated_of_flatWeightDirection`:
a flat weight direction at a crux annihilates the tight vector of some argmax block, with
no side conditions at all beyond flatness.  `Gtz.eigenSquareRow_dotProduct` connects that
flatness to the shipped flat-direction PRODUCER
`Gtz.exists_flatDirection_of_card_add_one_lt`, whose functionals are plain vectors: the
eigen-square row is the vector whose dot product against a direction is the direction's
first-order effect on the block.

Read through full support the conclusion becomes
`Gtz.SixThreeCrux.exists_argmax_direction_eq_zero_of_flatWeightDirection`: a flat weight
direction VANISHES on some argmax block.  That is the shape an index argument consumes.  It
is not the index theorem -- turning it into a floor on the number of argmax blocks needs, on
top of this, that a real vector space is not a finite union of proper subspaces -- and the
shipped floor remains `Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily`.

Note what this is NOT.  `Gtz.exists_chartTangentCurve_descent` is the FIRST-order descent
along a Cayley curve in the full chart domain, and it needs every active tight slope
STRICTLY negative.  The escape here is the complementary case, where every slope is
exactly zero and first-order descent has nothing to say.

## 2.  The Grassmannian half

`ChartSecondOrder` records that "the projection variety contains no line, so the chart
directions carry curvature that this file never touches".
`Gtz.trace_mul_grassmannAcceleration` computes it.  For a curve of projections with
velocity `B` and acceleration `A` -- the pair constrained by differentiating `P * P = P`
twice -- and any `assembly` commuting with the projection,

  `trace (assembly * A) = -2 * trace (assembly * (2 P - 1) * B * B)`.

The right side depends on the VELOCITY alone, so the free part of the acceleration, which
is exactly the part a curve may choose, cancels.
`Gtz.trace_assembly_mul_acceleration_eq_of_sameVelocity` states that reading directly.

DISCLOSURE, so the reach is not overstated.  On a joint eigenbasis this is
`2 * sum over (i in range, j in kernel) of (a j - a i) * B i j ^ 2`, and summing it over an
orthonormal basis of Grassmannian velocities gives `rank - size * (value + 1/size)`, that is
`rank - 1 - size * value`, the arithmetic coming from the shipped
`Gtz.trace_projection_mul_multiplier_of_isChartStationaryData`.  At a crux the value is
negative, so that trace is POSITIVE: on average the Grassmannian directions are stabilising,
and the curvature cannot by itself contradict minimality.  Neither the eigenbasis form nor
the basis sum is proved here; both are orientation prose, and the second was MEASURED rather
than derived.  What is proved is the identity.

`Gtz.trace_assembly_mul_chartStationaryGap` is a COROLLARY of the shipped
`Gtz.trace_projection_mul_multiplier_of_isChartStationaryData`, not a second proof of it.
A draft of this file also carried the projection identity itself; it was dropped, being
the trace-commuted twin of the shipped one.

The identity's hypotheses are shown INHABITED before anything is built on them.
`Gtz.blockDiagonal_velocitySquare_of_grassmannTangent` says a Grassmannian tangent velocity
-- one whose two diagonal blocks vanish -- has a block-diagonal square, and
`Gtz.exists_acceleration_of_blockDiagonal_velocitySquare` then solves the curve constraint.
So the constraint is satisfiable at EVERY tangent direction, not at one lucky point, and
`Gtz.exists_grassmannCurvature_datum_nontrivial` exhibits an explicit instance with a
nonzero velocity and a nonzero conclusion.

## 3.  The compression form at a multiple eigenvalue

The weight-slice escape picks ONE unit tight vector per block and tests the scalar
`u . D u`.  That test is the wrong one at a MULTIPLE least eigenvalue, where a
perturbation can be flat against one eigenvector of the tight eigenspace and not against
another -- the trap `Gtz.icosaDesign` sits in.  `Gtz.tightCompression` is the right
object: the whole matrix `frame^T * perturbation * frame`.

`Gtz.mulVec_eq_zero_of_posSemidef_of_tightCompression_eq_zero` is the multiplicity
generalisation of `Gtz.mulVec_eq_zero_of_posSemidef_of_dotProduct_zero`, and it asks
nothing of the frame -- not orthonormality, not injectivity -- because only the diagonal
entries of the compression are used, one column at a time.
`Gtz.tightCompression_diagonal_apply` exhibits the first-order functionals at
multiplicity: a block of multiplicity `mult` contributes `mult * (mult + 1) / 2` of them
rather than one, which is what the rank check behind
`Gtz.eq_zero_of_flatDirection_of_span_top` must count.
`Gtz.tightCompression_replicateCol_eq_zero_iff` is the simple-case equivalence: at
multiplicity one the compression test IS the scalar test.

THE MECHANISM REMAINS FIELD-BLIND, and this is orientation prose rather than a theorem of
this file.  Every step runs verbatim over the complex numbers, so nothing here can close
the cell alone; it must be paired with a realness consumer.
-/

import Mathlib
import Gtz.Quantitative.ChartDescentFromMinimality
import Gtz.Quantitative.ChartSecondOrder
import Gtz.Quantitative.ChartStationary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

section StepExistence

variable {size rank : ℕ}

/-- The principal submatrix of a diagonal matrix along an order embedding is again
diagonal: the embedding is injective, so no off-diagonal entry can be woken up. -/
theorem submatrix_diagonal_orderEmbOfFin (direction : Fin size → ℝ)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) :
    (Matrix.diagonal direction).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard)
      = Matrix.diagonal fun blockIndex => direction (selected.orderEmbOfFin hcard blockIndex) := by
  ext rowIndex colIndex
  rcases eq_or_ne rowIndex colIndex with rfl | hoffDiagonal
  · rw [Matrix.submatrix_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  · rw [Matrix.submatrix_apply,
      Matrix.diagonal_apply_ne _ fun hcollide =>
        hoffDiagonal ((selected.orderEmbOfFin hcard).injective hcollide),
      Matrix.diagonal_apply_ne _ hoffDiagonal]

/-- The restricted diagonal's quadratic form at a block, written out in the block
coordinates: the direction sampled along the selection, weighted by the squared
entries of the vector. -/
theorem dotProduct_submatrix_diagonal_mulVec (direction : Fin size → ℝ)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) (vec : Fin rank → ℝ) :
    vec ⬝ᵥ ((Matrix.diagonal direction).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard) *ᵥ vec)
      = ∑ blockIndex, direction (selected.orderEmbOfFin hcard blockIndex)
          * vec blockIndex ^ 2 := by
  rw [submatrix_diagonal_orderEmbOfFin, dotProduct]
  refine Finset.sum_congr rfl fun blockIndex _ => ?_
  rw [Matrix.mulVec_diagonal]
  ring

/-- **A UNIFORM LOWER BOUND ON A BLOCK'S FIRST-ORDER RESPONSE.**  Whatever the block and
whatever the unit vector, the restricted diagonal's quadratic form cannot fall below
`-chartWeightCap direction`.  One cap for all `Nat.choose size rank` blocks at once, which is
what turns the per-block step conditions into a single scalar threshold. -/
theorem neg_chartWeightCap_le_dotProduct_submatrix_diagonal_mulVec (direction : Fin size → ℝ)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) {vec : Fin rank → ℝ}
    (hunit : vec ⬝ᵥ vec = 1) :
    -chartWeightCap direction
      ≤ vec ⬝ᵥ ((Matrix.diagonal direction).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard) *ᵥ vec) := by
  have hsquares : ∑ blockIndex : Fin rank, vec blockIndex ^ 2 = 1 := by
    rw [← dotProduct_self_eq_sum_sq, hunit]
  rw [dotProduct_submatrix_diagonal_mulVec]
  have hterm : ∀ blockIndex ∈ (Finset.univ : Finset (Fin rank)),
      -chartWeightCap direction * vec blockIndex ^ 2
        ≤ direction (selected.orderEmbOfFin hcard blockIndex) * vec blockIndex ^ 2 := by
    intro blockIndex _
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hbounds := abs_le.mp (abs_directionWeight_le_chartWeightCap direction
      (selected.orderEmbOfFin hcard blockIndex))
    linarith [hbounds.1]
  calc -chartWeightCap direction
      = ∑ blockIndex : Fin rank, -chartWeightCap direction * vec blockIndex ^ 2 := by
        rw [← Finset.mul_sum, hsquares, mul_one]
    _ ≤ _ := Finset.sum_le_sum hterm

/-- Falling outside the argmax family is falling STRICTLY below the objective: the family
is defined by a non-strict inequality against a `sup'`, so its complement is strict. -/
theorem chartBlockValue_lt_chartObjective_of_notMem_chartArgmaxFamily [Nonempty (Fin rank)]
    (point : ChartPoint size rank) {selected : Finset (Fin size)} (hcard : selected.card = rank)
    (hinactive : selected ∉ chartArgmaxFamily point) :
    chartBlockValue rank
        ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) selected
      < chartObjective point := by
  by_contra hcontra
  exact hinactive ((mem_chartArgmaxFamily_iff point selected).mpr ⟨hcard, not_lt.mp hcontra⟩)

/-- **THE STEP EXISTS.**  At a chart point with strictly positive weights, every weight
direction admits a strictly positive step that (i) keeps the weights nonnegative and
(ii) leaves every INACTIVE block's own strictly positive gap unspent.

Those are exactly the two slots that `Gtz.chartObjective_lt_of_perturbedWeight` and
`Gtz.SixThreeCrux.exists_tight_annihilated_of_flatDirection` SUPPLY rather than derive.
The construction is a finite minimum and nothing else: `Gtz.exists_pos_le_forall_mem`
turns the atoms' positive weights into one floor and the inactive blocks' positive gaps
into another, `Gtz.chartWeightCap` caps the direction's first-order effect uniformly over
all blocks and all unit vectors at once, and the step is the smaller floor divided by one
more than the cap.  No continuity, no compactness, no limit. -/
theorem exists_pos_step_feasible_and_gapPreserving [Nonempty (Fin rank)]
    (point : ChartPoint size rank)
    (hweightPos : ∀ atomIndex : Fin size, 0 < point.weight atomIndex)
    (direction : Fin size → ℝ) (tightVec : Finset (Fin size) → (Fin rank → ℝ))
    (hunit : ∀ selected : Finset (Fin size), selected.card = rank →
      tightVec selected ⬝ᵥ tightVec selected = 1) :
    ∃ step : ℝ, 0 < step
      ∧ (∀ atomIndex : Fin size, 0 ≤ point.weight atomIndex + step * direction atomIndex)
      ∧ ∀ (selected : Finset (Fin size)) (hcard : selected.card = rank),
          selected ∉ chartArgmaxFamily point →
            chartBlockValue rank
                ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ))
                selected - chartObjective point
              < step * (tightVec selected ⬝ᵥ ((Matrix.diagonal direction).submatrix
                  (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)
                    *ᵥ tightVec selected)) := by
  classical
  obtain ⟨weightFloor, hweightFloorPos, hweightFloor⟩ :=
    exists_pos_le_forall_mem (Finset.univ : Finset (Fin size)) point.weight
      fun atomIndex _ => hweightPos atomIndex
  obtain ⟨gapFloor, hgapFloorPos, hgapFloor⟩ :=
    exists_pos_le_forall_mem
      ((chartCandidates size rank).filter fun candidate => candidate ∉ chartArgmaxFamily point)
      (fun candidate => chartObjective point - chartBlockValue rank
        ((point.chart, point.weight) : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) candidate)
      (by
        intro candidate hmem
        rw [Finset.mem_filter, mem_chartCandidates_iff] at hmem
        have hstrict := chartBlockValue_lt_chartObjective_of_notMem_chartArgmaxFamily point
          hmem.1 hmem.2
        linarith)
  have hcapNonneg : 0 ≤ chartWeightCap direction := chartWeightCap_nonneg direction
  have hdenomPos : (0 : ℝ) < chartWeightCap direction + 1 := by linarith
  set floorValue : ℝ := min gapFloor weightFloor with hfloorValue
  have hfloorPos : 0 < floorValue := lt_min hgapFloorPos hweightFloorPos
  have hstepPos : 0 < floorValue / (chartWeightCap direction + 1) := div_pos hfloorPos hdenomPos
  have hspend : floorValue / (chartWeightCap direction + 1) * chartWeightCap direction
      < floorValue := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hdenomPos]
    nlinarith
  refine ⟨floorValue / (chartWeightCap direction + 1), hstepPos, ?_, ?_⟩
  · intro atomIndex
    have hlow : -chartWeightCap direction ≤ direction atomIndex := by
      have hbounds := abs_le.mp (abs_directionWeight_le_chartWeightCap direction atomIndex)
      linarith [hbounds.1]
    have hmul : floorValue / (chartWeightCap direction + 1) * -chartWeightCap direction
        ≤ floorValue / (chartWeightCap direction + 1) * direction atomIndex :=
      mul_le_mul_of_nonneg_left hlow (le_of_lt hstepPos)
    have hwFloor : weightFloor ≤ point.weight atomIndex :=
      hweightFloor atomIndex (Finset.mem_univ _)
    have hmin : floorValue ≤ weightFloor := min_le_right _ _
    nlinarith [hspend, hmul, hwFloor, hmin]
  · intro selected hcard hinactive
    have hmemFilter : selected ∈ (chartCandidates size rank).filter
        fun candidate => candidate ∉ chartArgmaxFamily point := by
      rw [Finset.mem_filter, mem_chartCandidates_iff]
      exact ⟨hcard, hinactive⟩
    have hgap := hgapFloor selected hmemFilter
    have hlow := neg_chartWeightCap_le_dotProduct_submatrix_diagonal_mulVec direction hcard
      (hunit selected hcard)
    have hmul := mul_le_mul_of_nonneg_left hlow (le_of_lt hstepPos)
    have hmin : floorValue ≤ gapFloor := min_le_left _ _
    nlinarith [hspend, hmul, hgap, hmin]

end StepExistence

/-- **THE WEIGHT-SLICE SECOND-ORDER CONDITION, CONSUMING A FLAT DIRECTION ALONE.**  The
shipped `Gtz.SixThreeCrux.exists_tight_annihilated_of_flatDirection` asks its caller for a
step, for feasibility at that step, and for the inactive-block condition at that step.
None of the three is a genuine hypothesis: `Gtz.exists_pos_step_feasible_and_gapPreserving`
manufactures all of them from the crux's own strictly positive weights.

So the second-order fact reads, with no side conditions beyond the direction being flat at
the argmax blocks: SOME argmax block has its tight vector ANNIHILATED by the direction's
restricted diagonal.  Vanishing at first order is not enough. -/
theorem SixThreeCrux.exists_tight_annihilated_of_flatWeightDirection (crux : SixThreeCrux)
    (direction : Fin 6 → ℝ) (hsum : ∑ atomIndex, direction atomIndex = 0)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hflat : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design) →
        tightVec selected ⬝ᵥ ((Matrix.diagonal direction).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)
            *ᵥ tightVec selected) = 0) :
    ∃ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
        ∧ (Matrix.diagonal direction).submatrix (selected.orderEmbOfFin hcard)
            (selected.orderEmbOfFin hcard) *ᵥ tightVec selected = 0 := by
  obtain ⟨step, hstepPos, hnonneg, hstepSmall⟩ :=
    exists_pos_step_feasible_and_gapPreserving (chartPointOfDesign crux.design)
      crux.weight_pos direction tightVec hunit
  exact crux.exists_tight_annihilated_of_flatDirection direction (ne_of_gt hstepPos) hnonneg hsum
    tightVec hunit hEigen hflat hstepSmall


/-! ### From annihilation to vanishing

The escape's conclusion is that the restricted diagonal ANNIHILATES a tight vector.  When
that tight vector has full support on its block -- no coordinate zero -- annihilation says
the direction itself vanishes at every atom of the block.  That is the form an index
argument consumes, and `Gtz.SixThreeCrux.exists_argmax_direction_eq_zero_of_flatWeightDirection`
states it.  It is NOT the index theorem: turning "the direction vanishes on SOME argmax
block" into a floor on the number of argmax blocks needs, on top of this, that a real
vector space is not a finite union of proper subspaces.  The shipped floor remains
`Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily`. -/

/-- A restricted diagonal annihilates a vector exactly when the direction vanishes wherever
the vector does not. -/
theorem eq_zero_of_submatrix_diagonal_mulVec_eq_zero {size rank : ℕ} (direction : Fin size → ℝ)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) {vec : Fin rank → ℝ}
    (hannihilated : (Matrix.diagonal direction).submatrix (selected.orderEmbOfFin hcard)
      (selected.orderEmbOfFin hcard) *ᵥ vec = 0)
    (hfullSupport : ∀ blockIndex : Fin rank, vec blockIndex ≠ 0)
    {atomIndex : Fin size} (hmem : atomIndex ∈ selected) :
    direction atomIndex = 0 := by
  have hpreimage : atomIndex ∈ Set.range (selected.orderEmbOfFin hcard) := by
    rw [Finset.range_orderEmbOfFin selected hcard]
    exact hmem
  obtain ⟨blockIndex, hblockIndex⟩ := hpreimage
  rw [submatrix_diagonal_orderEmbOfFin] at hannihilated
  have hcoordinate := congrFun hannihilated blockIndex
  rw [Matrix.mulVec_diagonal, Pi.zero_apply] at hcoordinate
  rcases mul_eq_zero.mp hcoordinate with hzero | hcontradiction
  · rw [← hblockIndex]
    exact hzero
  · exact absurd hcontradiction (hfullSupport blockIndex)

/-- **A FLAT WEIGHT DIRECTION VANISHES ON SOME ARGMAX BLOCK.**  The escape's conclusion read
through full support.  This is the shape an index argument consumes; supplying the index
floor itself is a separate obligation. -/
theorem SixThreeCrux.exists_argmax_direction_eq_zero_of_flatWeightDirection (crux : SixThreeCrux)
    (direction : Fin 6 → ℝ) (hsum : ∑ atomIndex, direction atomIndex = 0)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hflat : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design) →
        tightVec selected ⬝ᵥ ((Matrix.diagonal direction).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)
            *ᵥ tightVec selected) = 0)
    (hfullSupport : ∀ (selected : Finset (Fin 6)) (blockIndex : Fin 3),
      tightVec selected blockIndex ≠ 0) :
    ∃ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      ∀ atomIndex ∈ selected, direction atomIndex = 0 := by
  obtain ⟨selected, hcard, hactive, hannihilated⟩ :=
    crux.exists_tight_annihilated_of_flatWeightDirection direction hsum tightVec hunit hEigen hflat
  exact ⟨selected, hactive, fun atomIndex hmem =>
    eq_zero_of_submatrix_diagonal_mulVec_eq_zero direction hcard hannihilated
      (hfullSupport selected) hmem⟩

/-! ## The eigen-square row -/

section EigenSquareRow

variable {size rank : ℕ}

/-- **THE FIRST-ORDER FUNCTIONAL OF A BLOCK.**  The vector whose dot product against a
weight direction is that direction's first-order effect on the block. -/
def eigenSquareRow (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (vec : Fin rank → ℝ) : Fin size → ℝ :=
  fun atomIndex => ∑ blockIndex : Fin rank,
    if selected.orderEmbOfFin hcard blockIndex = atomIndex then vec blockIndex ^ 2 else 0

/-- **THE BRIDGE.**  Dotting the eigen-square row against a direction reproduces the
restricted diagonal's quadratic form, so flatness in the sense the ESCAPE consumes is
flatness in the sense the flat-direction PRODUCER delivers. -/
theorem eigenSquareRow_dotProduct (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (vec : Fin rank → ℝ) (direction : Fin size → ℝ) :
    eigenSquareRow selected hcard vec ⬝ᵥ direction
      = vec ⬝ᵥ ((Matrix.diagonal direction).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard) *ᵥ vec) := by
  rw [dotProduct_submatrix_diagonal_mulVec, dotProduct]
  simp only [eigenSquareRow, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun blockIndex _ => ?_
  rw [Finset.sum_ite_eq (Finset.univ : Finset (Fin size))
    (selected.orderEmbOfFin hcard blockIndex) fun atomIndex => vec blockIndex ^ 2 * direction atomIndex]
  rw [if_pos (Finset.mem_univ _)]
  ring

end EigenSquareRow

/-! ## The trace identities -/

section TraceIdentities

variable {size : ℕ} {activeIndex : Type*}
variable {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE GAP TRACE IDENTITY.**  The assembly reads the value straight off the gap.

A corollary of the shipped `Gtz.trace_projection_mul_multiplier_of_isChartStationaryData`
rather than a second proof of it: the projection identity costs `1/size`, the weight
diagonal returns exactly `1/size`, and the two cancel. -/
theorem trace_assembly_mul_chartStationaryGap
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    Matrix.trace (chartMultiplierAssembly activeSet activeWeight tightDir
        * chartStationaryGap projection weight) = value := by
  have hdiagonal : Matrix.trace (chartMultiplierAssembly activeSet activeWeight tightDir
      * Matrix.diagonal weight) = ((size : ℝ))⁻¹ := by
    have hentry : ∀ atomIndex : Fin size,
        (chartMultiplierAssembly activeSet activeWeight tightDir
            * Matrix.diagonal weight) atomIndex atomIndex
          = ((size : ℝ))⁻¹ * weight atomIndex := by
      intro atomIndex
      rw [Matrix.mul_diagonal, hdata.assembly_diagonal atomIndex]
    calc Matrix.trace (chartMultiplierAssembly activeSet activeWeight tightDir
            * Matrix.diagonal weight)
        = ∑ atomIndex : Fin size, ((size : ℝ))⁻¹ * weight atomIndex :=
          Finset.sum_congr rfl fun atomIndex _ => hentry atomIndex
      _ = ((size : ℝ))⁻¹ := by rw [← Finset.mul_sum, hdata.weight_sum_one, mul_one]
  have hprojection : Matrix.trace (chartMultiplierAssembly activeSet activeWeight tightDir
      * projection) = value + ((size : ℝ))⁻¹ := by
    rw [Matrix.trace_mul_comm]
    exact trace_projection_mul_multiplier_of_isChartStationaryData hdata
  rw [chartStationaryGap, Matrix.mul_sub, Matrix.trace_sub, hprojection, hdiagonal]
  ring

end TraceIdentities

/-! ## The Grassmannian curvature -/

section GrassmannCurvature

variable {ambient : ℕ}

/-- **THE MULTIPLIER-AVERAGED GRASSMANNIAN CURVATURE.**

`projection` is an idempotent, `assembly` commutes with it, and the pair
`(velocity, acceleration)` satisfies the constraint obtained by differentiating
`P s * P s = P s` twice.  Then the averaged curvature depends on the VELOCITY alone: the
free part of the acceleration -- exactly the part a curve may choose -- drops out, because
the assembly is block diagonal for the projection.

Read on a joint eigenbasis of `projection` and `assembly` this is the diagonal form
`2 * sum over (i in range, j in kernel) of (a j - a i) * velocity i j ^ 2`, so it is
positive semidefinite exactly when the assembly's kernel eigenvalues dominate its range
eigenvalues.  That reading is orientation prose; the identity below is what is proved. -/
theorem trace_mul_grassmannAcceleration
    (projection assembly velocity acceleration : Matrix (Fin ambient) (Fin ambient) ℝ)
    (hidempotent : projection * projection = projection)
    (hcommutes : projection * assembly = assembly * projection)
    (hcurve : acceleration * projection + projection * acceleration - acceleration
      = -(2 : ℝ) • (velocity * velocity)) :
    Matrix.trace (assembly * acceleration)
      = -(2 : ℝ) * Matrix.trace (assembly * ((2 : ℝ) • projection - 1)
          * (velocity * velocity)) := by
  have hrangeBlock : projection * assembly * projection = assembly * projection := by
    rw [hcommutes, Matrix.mul_assoc, hidempotent]
  have hkernelBlock : (1 - projection) * assembly * (1 - projection)
      = assembly * (1 - projection) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hcommutes,
      Matrix.mul_assoc, hidempotent]
    abel
  have hblockSplit : assembly
      = projection * assembly * projection + (1 - projection) * assembly * (1 - projection) := by
    rw [hrangeBlock, hkernelBlock, Matrix.mul_sub, Matrix.mul_one]
    abel
  have hrangeAccel : projection * acceleration * projection
      = -(2 : ℝ) • (projection * (velocity * velocity) * projection) := by
    have key := congrArg (fun blockMatrix => projection * blockMatrix * projection) hcurve
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc] at key
    rw [Matrix.mul_assoc (projection * acceleration) projection projection, hidempotent] at key
    simp only [← Matrix.mul_assoc]
    linear_combination (norm := module) key
  have hkernelAccel : (1 - projection) * acceleration * (1 - projection)
      = (2 : ℝ) • ((1 - projection) * (velocity * velocity) * (1 - projection)) := by
    have key := congrArg
      (fun blockMatrix => (1 - projection) * blockMatrix * (1 - projection)) hcurve
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
      ← Matrix.mul_assoc] at key
    rw [Matrix.mul_assoc acceleration projection projection,
      Matrix.mul_assoc (projection * acceleration) projection projection, hidempotent] at key
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      ← Matrix.mul_assoc]
    linear_combination (norm := module) -key
  have hcycleRange : Matrix.trace (projection * assembly * projection * acceleration)
      = Matrix.trace (assembly * (projection * acceleration * projection)) := by
    rw [show projection * assembly * projection * acceleration
        = projection * (assembly * projection * acceleration) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hcycleKernel :
      Matrix.trace ((1 - projection) * assembly * (1 - projection) * acceleration)
        = Matrix.trace (assembly * ((1 - projection) * acceleration * (1 - projection))) := by
    rw [show (1 - projection) * assembly * (1 - projection) * acceleration
        = (1 - projection) * (assembly * (1 - projection) * acceleration) by
          simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hrangeTrace :
      Matrix.trace (assembly * (projection * (velocity * velocity) * projection))
        = Matrix.trace (assembly * projection * (velocity * velocity)) := by
    rw [show assembly * (projection * (velocity * velocity) * projection)
        = assembly * projection * (velocity * velocity) * projection by
          simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show projection * (assembly * projection * (velocity * velocity))
        = projection * assembly * projection * (velocity * velocity) by
          simp only [Matrix.mul_assoc],
      hrangeBlock]
  have hkernelTrace :
      Matrix.trace (assembly * ((1 - projection) * (velocity * velocity) * (1 - projection)))
        = Matrix.trace (assembly * (1 - projection) * (velocity * velocity)) := by
    rw [show assembly * ((1 - projection) * (velocity * velocity) * (1 - projection))
        = assembly * (1 - projection) * (velocity * velocity) * (1 - projection) by
          simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show (1 - projection) * (assembly * (1 - projection) * (velocity * velocity))
        = (1 - projection) * assembly * (1 - projection) * (velocity * velocity) by
          simp only [Matrix.mul_assoc],
      hkernelBlock]
  calc Matrix.trace (assembly * acceleration)
      = Matrix.trace (projection * assembly * projection * acceleration)
        + Matrix.trace ((1 - projection) * assembly * (1 - projection) * acceleration) := by
        conv_lhs => rw [hblockSplit]
        rw [Matrix.add_mul, Matrix.trace_add]
    _ = -(2 : ℝ) * Matrix.trace (assembly * projection * (velocity * velocity))
        + (2 : ℝ) * Matrix.trace (assembly * (1 - projection) * (velocity * velocity)) := by
        rw [hcycleRange, hcycleKernel, hrangeAccel, hkernelAccel, Matrix.mul_smul,
          Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, hrangeTrace, hkernelTrace,
          smul_eq_mul, smul_eq_mul]
    _ = -(2 : ℝ) * Matrix.trace (assembly * ((2 : ℝ) • projection - 1)
          * (velocity * velocity)) := by
        rw [show assembly * ((2 : ℝ) • projection - 1) * (velocity * velocity)
            = (2 : ℝ) • (assembly * projection * (velocity * velocity))
              - assembly * (1 - projection) * (velocity * velocity)
              - assembly * projection * (velocity * velocity) by
              simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
                Matrix.mul_one]
              module,
          Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
        ring

/-- **THE CURVATURE IS INTRINSIC TO THE VELOCITY.**  Two curves through the same point with
the same velocity have the same multiplier-averaged curvature, whatever accelerations they
choose.  So the quantity is a function of the tangent direction, not of the curve. -/
theorem trace_assembly_mul_acceleration_eq_of_sameVelocity
    (projection assembly velocity firstAcceleration secondAcceleration :
      Matrix (Fin ambient) (Fin ambient) ℝ)
    (hidempotent : projection * projection = projection)
    (hcommutes : projection * assembly = assembly * projection)
    (hfirstCurve : firstAcceleration * projection + projection * firstAcceleration
      - firstAcceleration = -(2 : ℝ) • (velocity * velocity))
    (hsecondCurve : secondAcceleration * projection + projection * secondAcceleration
      - secondAcceleration = -(2 : ℝ) • (velocity * velocity)) :
    Matrix.trace (assembly * firstAcceleration)
      = Matrix.trace (assembly * secondAcceleration) := by
  rw [trace_mul_grassmannAcceleration projection assembly velocity firstAcceleration
      hidempotent hcommutes hfirstCurve,
    trace_mul_grassmannAcceleration projection assembly velocity secondAcceleration
      hidempotent hcommutes hsecondCurve]

/-! ### The hypotheses are inhabited

Precedent: a second-order escape once landed demanding flatness at twenty blocks at once --
twenty linear conditions on a five-dimensional space, true and useless.  So the curve
constraint above is shown SOLVABLE before anything is built on it, and not merely at one
lucky point but at every Grassmannian tangent velocity. -/

/-- If the velocity's square is block diagonal for the projection, the curve constraint
has a solution. -/
theorem exists_acceleration_of_blockDiagonal_velocitySquare
    (projection velocity : Matrix (Fin ambient) (Fin ambient) ℝ)
    (hidempotent : projection * projection = projection)
    (hblock : projection * (velocity * velocity) * projection
        + (1 - projection) * (velocity * velocity) * (1 - projection) = velocity * velocity) :
    ∃ acceleration : Matrix (Fin ambient) (Fin ambient) ℝ,
      acceleration * projection + projection * acceleration - acceleration
        = -(2 : ℝ) • (velocity * velocity) := by
  have hkill : projection * (1 - projection) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hidempotent, sub_self]
  have hkillOther : (1 - projection) * projection = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hidempotent, sub_self]
  set rangeBlock := projection * (velocity * velocity) * projection with hrangeDef
  set kernelBlock := (1 - projection) * (velocity * velocity) * (1 - projection) with hkernelDef
  have hrangeRight : rangeBlock * projection = rangeBlock := by
    rw [hrangeDef, Matrix.mul_assoc, hidempotent]
  have hrangeLeft : projection * rangeBlock = rangeBlock := by
    rw [hrangeDef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hidempotent]
  have hkernelRight : kernelBlock * projection = 0 := by
    rw [hkernelDef, Matrix.mul_assoc, hkillOther, Matrix.mul_zero]
  have hkernelLeft : projection * kernelBlock = 0 := by
    rw [hkernelDef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hkill, Matrix.zero_mul,
      Matrix.zero_mul]
  refine ⟨-(2 : ℝ) • rangeBlock + (2 : ℝ) • kernelBlock, ?_⟩
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_smul, hrangeRight, hrangeLeft, hkernelRight, hkernelLeft, ← hblock]
  module

/-- A Grassmannian tangent velocity -- one with both diagonal blocks vanishing -- has a
block-diagonal square, so the previous lemma applies to it. -/
theorem blockDiagonal_velocitySquare_of_grassmannTangent
    (projection velocity : Matrix (Fin ambient) (Fin ambient) ℝ)
    (hrangeBlock : projection * velocity * projection = 0)
    (hkernelBlock : (1 - projection) * velocity * (1 - projection) = 0) :
    projection * (velocity * velocity) * projection
        + (1 - projection) * (velocity * velocity) * (1 - projection) = velocity * velocity := by
  have hinsert : velocity * velocity
      = velocity * projection * velocity + velocity * (1 - projection) * velocity := by
    have hone : projection + (1 - projection) = 1 := by abel
    calc velocity * velocity
        = velocity * (projection + (1 - projection)) * velocity := by
          rw [hone, Matrix.mul_one]
      _ = velocity * projection * velocity + velocity * (1 - projection) * velocity := by
          simp only [Matrix.mul_add, Matrix.add_mul]
  have hoffRange : projection * (velocity * velocity) * (1 - projection) = 0 := by
    have hstep : projection * (velocity * velocity) * (1 - projection)
        = projection * velocity * projection * (velocity * (1 - projection))
          + projection * velocity * ((1 - projection) * velocity * (1 - projection)) := by
      conv_lhs => rw [hinsert]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [hstep, hrangeBlock, hkernelBlock, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  have hoffKernel : (1 - projection) * (velocity * velocity) * projection = 0 := by
    have hstep : (1 - projection) * (velocity * velocity) * projection
        = (1 - projection) * velocity * projection * (velocity * projection)
          + (1 - projection) * velocity * (1 - projection) * (velocity * projection) := by
      conv_lhs => rw [hinsert]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [hstep, hkernelBlock, Matrix.zero_mul, add_zero,
      Matrix.mul_assoc ((1 - projection) * velocity) projection (velocity * projection),
      ← Matrix.mul_assoc projection velocity projection, hrangeBlock, Matrix.mul_zero]
  have hfour : projection * (velocity * velocity) * projection
      + projection * (velocity * velocity) * (1 - projection)
      + ((1 - projection) * (velocity * velocity) * projection
        + (1 - projection) * (velocity * velocity) * (1 - projection)) = velocity * velocity := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [hoffRange, hoffKernel, add_zero, zero_add] at hfour
  exact hfour

/-- **P4 NON-VACUITY.**  The curvature identity's hypotheses are inhabited at a NONZERO
velocity, with a nonzero conclusion. -/
theorem exists_grassmannCurvature_datum_nontrivial :
    ∃ (projection assembly velocity acceleration : Matrix (Fin 2) (Fin 2) ℝ),
      projection * projection = projection
        ∧ projection * assembly = assembly * projection
        ∧ acceleration * projection + projection * acceleration - acceleration
            = -(2 : ℝ) • (velocity * velocity)
        ∧ velocity ≠ 0
        ∧ Matrix.trace (assembly * acceleration) ≠ 0 := by
  classical
  refine ⟨Matrix.diagonal ![1, 0], Matrix.diagonal ![1, 3],
    Matrix.of ![![0, 1], ![1, 0]], Matrix.diagonal ![-2, 2], ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext index
    fin_cases index <;> norm_num
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    ext index
    fin_cases index <;> norm_num
  · have hsquare : (Matrix.of ![![(0 : ℝ), 1], ![1, 0]]) * (Matrix.of ![![(0 : ℝ), 1], ![1, 0]])
        = 1 := by
      ext rowIndex colIndex
      fin_cases rowIndex <;> fin_cases colIndex <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hsquare]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.one_apply,
        Fin.ext_iff]
  · intro hzero
    have hentry : (Matrix.of ![![(0 : ℝ), 1], ![1, 0]]) 0 1 = 0 := by rw [hzero]; rfl
    norm_num at hentry
  · rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    norm_num [Fin.sum_univ_two]

end GrassmannCurvature

/-! ## The compression form at a multiple eigenvalue -/

section Compression

variable {dim mult : ℕ}

/-- **THE COMPRESSION OF A PERTURBATION ONTO A TIGHT FRAME.**  The correct first-order
object at a MULTIPLE least eigenvalue.  At multiplicity one it is the scalar quadratic
form; above multiplicity one the scalar form is the wrong test, because a perturbation can
be flat against one eigenvector and not against another in the same eigenspace. -/
def tightCompression (frame : Matrix (Fin dim) (Fin mult) ℝ)
    (perturbation : Matrix (Fin dim) (Fin dim) ℝ) : Matrix (Fin mult) (Fin mult) ℝ :=
  frameᵀ * perturbation * frame

/-- The compression's entries are the perturbation's bilinear form on pairs of frame
columns. -/
theorem tightCompression_apply (frame : Matrix (Fin dim) (Fin mult) ℝ)
    (perturbation : Matrix (Fin dim) (Fin dim) ℝ) (rowIndex colIndex : Fin mult) :
    tightCompression frame perturbation rowIndex colIndex
      = (fun ambientIndex => frame ambientIndex rowIndex)
          ⬝ᵥ (perturbation *ᵥ fun ambientIndex => frame ambientIndex colIndex) := by
  rw [tightCompression, Matrix.mul_apply, dotProduct]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Matrix.mulVec,
    dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ambientIndex _ => ?_
  refine Finset.sum_congr rfl fun otherIndex _ => ?_
  ring

/-- The compression of a SYMMETRIC perturbation is symmetric, so any rank or eigenvalue
reasoning downstream is reasoning about a symmetric matrix. -/
theorem tightCompression_transpose (frame : Matrix (Fin dim) (Fin mult) ℝ)
    {perturbation : Matrix (Fin dim) (Fin dim) ℝ} (hsymmetric : perturbationᵀ = perturbation) :
    (tightCompression frame perturbation)ᵀ = tightCompression frame perturbation := by
  rw [tightCompression, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    hsymmetric, ← Matrix.mul_assoc]

/-- **THE FIRST-ORDER FUNCTIONALS AT MULTIPLICITY.**  Compressing a DIAGONAL perturbation
is linear in the direction, entry by entry.  At multiplicity one this is
`Gtz.eigenSquareRow_dotProduct`; in general a block of multiplicity `mult` contributes
`mult * (mult + 1) / 2` independent functionals rather than one, which is exactly what the
rank check behind `Gtz.eq_zero_of_flatDirection_of_span_top` must count. -/
theorem tightCompression_diagonal_apply (frame : Matrix (Fin dim) (Fin mult) ℝ)
    (direction : Fin dim → ℝ) (rowIndex colIndex : Fin mult) :
    tightCompression frame (Matrix.diagonal direction) rowIndex colIndex
      = ∑ ambientIndex : Fin dim,
          direction ambientIndex * (frame ambientIndex rowIndex * frame ambientIndex colIndex) := by
  rw [tightCompression_apply, dotProduct]
  refine Finset.sum_congr rfl fun ambientIndex _ => ?_
  rw [Matrix.mulVec_diagonal]
  ring

/-- **A POSITIVE-SEMIDEFINITE MATRIX ANNIHILATES A FRAME ITS COMPRESSION KILLS.**  The
multiplicity generalisation of `Gtz.mulVec_eq_zero_of_posSemidef_of_dotProduct_zero`, and
it needs nothing of the frame -- not orthonormality, not injectivity.  Only the DIAGONAL
entries of the compression are used, one column at a time. -/
theorem mulVec_eq_zero_of_posSemidef_of_tightCompression_eq_zero
    {gapMatrix : Matrix (Fin dim) (Fin dim) ℝ} (hposSemidef : gapMatrix.PosSemidef)
    {frame : Matrix (Fin dim) (Fin mult) ℝ}
    (hcompression : tightCompression frame gapMatrix = 0) (colIndex : Fin mult) :
    gapMatrix *ᵥ (fun ambientIndex => frame ambientIndex colIndex) = 0 := by
  refine mulVec_eq_zero_of_posSemidef_of_dotProduct_zero hposSemidef ?_
  rw [← tightCompression_apply, hcompression, Matrix.zero_apply]

/-- The frame form of the same fact. -/
theorem mul_eq_zero_of_posSemidef_of_tightCompression_eq_zero
    {gapMatrix : Matrix (Fin dim) (Fin dim) ℝ} (hposSemidef : gapMatrix.PosSemidef)
    {frame : Matrix (Fin dim) (Fin mult) ℝ}
    (hcompression : tightCompression frame gapMatrix = 0) :
    gapMatrix * frame = 0 := by
  ext rowIndex colIndex
  have hcolumn := mulVec_eq_zero_of_posSemidef_of_tightCompression_eq_zero hposSemidef
    hcompression colIndex
  have hentry := congrFun hcolumn rowIndex
  rw [Matrix.zero_apply, Matrix.mul_apply]
  simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using hentry

/-- **THE SIMPLE-CASE EQUIVALENCE.**  At multiplicity one the compression is the one by one
matrix carrying the scalar quadratic form, so the compression test and the scalar flatness
test `u . D u = 0` are the same condition.  The one-column frame is Mathlib's
`Matrix.replicateCol (Fin 1)`, so no second name for it is introduced here. -/
theorem tightCompression_replicateCol (vec : Fin dim → ℝ)
    (perturbation : Matrix (Fin dim) (Fin dim) ℝ) (rowIndex colIndex : Fin 1) :
    tightCompression (Matrix.replicateCol (Fin 1) vec) perturbation rowIndex colIndex
      = vec ⬝ᵥ (perturbation *ᵥ vec) := by
  rw [tightCompression_apply]
  rfl

/-- The same equivalence, as an `Iff` between the two tests. -/
theorem tightCompression_replicateCol_eq_zero_iff (vec : Fin dim → ℝ)
    (perturbation : Matrix (Fin dim) (Fin dim) ℝ) :
    tightCompression (Matrix.replicateCol (Fin 1) vec) perturbation = 0
      ↔ vec ⬝ᵥ (perturbation *ᵥ vec) = 0 := by
  constructor
  · intro hzero
    rw [← tightCompression_replicateCol vec perturbation 0 0, hzero, Matrix.zero_apply]
  · intro hzero
    ext rowIndex colIndex
    rw [tightCompression_replicateCol, hzero, Matrix.zero_apply]

end Compression

end Gtz
