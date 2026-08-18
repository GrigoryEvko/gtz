/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Wave.WiringKFourWalls

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
AUDIT-UNWIRED (2026-08-17): this module is absent from the `Gtz.lean` umbrella
and NO module imports it.  Real consumer count is ZERO.  It nonetheless holds
the richest criterion set in the `M(K4)` lane, including
`Gtz.posDef_kFourLaplacian_iff_rawTriple`, the unconditional trace floor
`Gtz.exists_kFourSpanningTree_traceSum_pos`, the Loewner monotonicity
`Gtz.posDef_kFourLaplacian_of_le` and the reduced residual
`Gtz.KFourRawSecondAndDetTotal`.  Wire it before anyone writes a new line.

AUDIT-DUPLICATE (2026-08-17): `Gtz.KFourRawTripleTotal` is the FIFTH Prop proved
equivalent to `Gtz.KFourUniversalStrictTree`.  The others are
`Gtz.KFourForestTripleTotal` (Gtz/Wave/KirchhoffSignTower.lean),
`Gtz.KFourBlockAdmissibleDetTotal` (Gtz/Wave/WiringKFourWalls.lean),
`Gtz.KFourLevelShiftTotal` and `Gtz.KFourRawSecondAndDetTotal` (this file).
Each carries its own `_closes_all` bridge, so the four consumers are discharged
five times over.  Pick ONE residual and retire the rest, or the next fork
proves a sixth.

AUDIT-NOTE ON LINE NUMBERS (2026-08-17): these blocks cite DECLARATION NAMES
only, never line numbers.  Comment-only edits in this lane already invalidated
one round of line references within a single session.  Cite names and grep.

# The raw invariant triple of the `K4` signed Laplacian, and the scalar shift cell

The registered `A3` proposition is
`Gtz.KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict`.  Every
route to it passes through `Gtz.KFourUniversalStrictTree`: at every chart point
some listed spanning tree dominates strictly.  This module supplies three new
unconditional laws and one new certificate cell.

## 0. What is direction generic, and what is not

Two laws carry the module and NEITHER mentions `K4`.  Both fix the rank at three
and leave the size of the family free, so both transport verbatim to `(7, 3)`
and to each of the five registered chart classes.

* `Gtz.posDef_directionChartGap_of_dominatingWeight` — the domination engine.
  Any pointwise LOWER bound on the signed gap weight whose moment is positive
  definite certifies strict domination.  Every cell in this module is an
  instance, and the proof is Loewner monotonicity of the moment
  (`Gtz.posDef_sum_smul_atomMatrix_of_le`).
* `Gtz.trace_directionChartGap_pos_of_maximalBoost` — the trace floor.  The
  trace of the chart gap is strictly positive at EVERY selection of two or more
  atoms that holds an atom of maximal leverage boost.

The `K4` material below is the forest reading of these two laws.
`Gtz.kFourTraceSum_pos_of_maximalBoost` is proved as the instance and not again.

## 1. The raw triple

`Gtz.posDef_kFourLaplacian_iff_rawTriple` reads positive definiteness of the
`K4` signed Laplacian at an ARBITRARY signed conductance vector as three
polynomial signs of that vector alone:

* `Gtz.kFourTraceSum` — degree one, the atom leverages against the conductances
* `Gtz.kFourSecondForestSum` — degree two, the fifteen two-forests of `K4` with
  their component multiplicities
* `Gtz.kFourMassTreeSum` — degree three, the sixteen spanning trees.

The landed forest triple `Gtz.posDef_directionChartGap_iff_forestTriple` reads
the same fact with the MASS whitener inside, so its first two polynomials mix
the masses with the signed weights.  The triple here has no mass in it at all.
The engine is the unit conductance `Gtz.kFourUnitConductance`, whose Laplacian
is the identity, fed to the landed adjugate bridge
`Gtz.trace_adjugate_kFourLaplacian_mul`.

## 2. The sharp trace floor, with a designated edge

`Gtz.kFourTraceBoost` is the atom leverage times the mass over the weight.
`Gtz.kFourTraceSum_pos_of_maximalBoost` proves that EVERY listed tree through a
maximal-boost edge makes the first sign strictly positive.  The proof is two
lines of arithmetic and no tangent line: the weights are a probability vector,
so the boost average never passes the boost maximum, and a tree that holds the
maximal edge holds two more strictly positive boosts.

This is a SELECTION law and not only an existence law.  It cuts the first of
the three signs from sixteen trees to the eight through one designated edge, at
every chart point, with no hypothesis.  It designates NOTHING about the other
two signs, and no claim of strict domination is made here — the registry
records `Gtz.kFourMaxEdgeHostsStrictTree_refuted` for the neighbouring reading.

## 3. The scalar shift cell

`Gtz.posDef_directionChartGap_of_scalarShift` is a new sufficient certificate.
Fix a listed tree and a level that passes every weight on the tree.  Replace
each selected weight by that level.  If the three raw signs of the resulting
shift vector `Gtz.kFourShiftVector` are positive, the tree dominates strictly.

The cell is division free, matrix free and eigenvalue free.  It fires at the
tetrahedron (all four stars, level `1/6`) and at `Gtz.traceRefuterPoint` (the
tree `{0, 1, 3}`, level `1/8`), the point that kills every single-tree rule of
`Gtz/Wave/WiringKFourWalls.lean`.

MEASURED, AND NOT A THEOREM.  An exact-rational census of 20000 random chart
points with rational masses and rational weights fires the cell at 92.55
percent of them.  On the SAME 20000 points the landed cell
`Gtz.KFourPencilCellFires` fires at 20000, it fires at all 1490 points that the
scalar cell misses, and the scalar cell fires at NO point that the pencil cell
misses.  So this cell does not enlarge the certificate atlas on that sample, and
its value is the SHAPE and the direction-generic engine, not new coverage.
Neither cell is total: `Gtz.kFourPencilCell_not_total` refutes the pencil cell,
and section 6c refutes the scalar cell.

## 4. The sixteen-row table at the refuter

`Gtz.traceRefuterPoint_massTreeSum_table` gives all sixteen signed tree sums at
`Gtz.traceRefuterPoint` in exact rationals.  Seven of the sixteen are strictly
positive, so the disjunction over the tree list survives at the point where
every fixed local rule dies.

## 5. The two traps

`Gtz.KFourRawTripleTotal` IS equivalent to `Gtz.KFourUniversalStrictTree`, and
`Gtz.kFourUniversalStrictTree_iff_rawTripleTotal` says so.  Its value is the
SHAPE of the three polynomials and never the name.  The unconditional laws of
sections 2 and 3 are the deliverable.

No antecedent here is refuted.  The trace floor has no hypothesis at all.  The
scalar shift cell is inhabited twice, at `Gtz.tetrahedronChartPoint` and at
`Gtz.traceRefuterPoint`.
-/

namespace Gtz

open Finset Matrix

/-! ## 0. The direction-generic laws

Nothing in this section mentions `K4`.  The size of the family is free and only
the rank is fixed at three, so every statement transports verbatim to `(7, 3)`
and to each of the five registered chart classes.  The `K4` sections that follow
are the forest coordinates of these laws and never a separate argument.

Two laws carry the whole module.

* `Gtz.posDef_directionChartGap_of_dominatingWeight` — **the domination
  engine.**  Any pointwise LOWER bound on the signed gap weight whose moment is
  positive definite certifies strict domination.  The proof is one line of
  Loewner monotonicity and it has no case split, no basis and no determinant.
* `Gtz.trace_directionChartGap_pos_of_maximalBoost` — **the trace floor.**  The
  trace of the chart gap is strictly positive at EVERY selection of two or more
  atoms that holds an atom of maximal leverage boost.  The proof is that the
  weights are a probability vector, so the boost average never passes the boost
  maximum, while a selection of two or more atoms strictly passes it. -/

/-- **THE LEVERAGE BOOST OF AN ATOM.**  Its leverage times its mass over its
weight.  This is the quantity the trace of the chart gap reads. -/
noncomputable def chartTraceBoost {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (label : Fin size) : ℝ :=
  leverageOf (direction label) * mass label / weight label

/-- **THE TRACE OF A CHART GAP.**  The selected boosted leverages against the
total leverage share.  Direction generic. -/
theorem trace_directionChartGap {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) :
    Matrix.trace (directionChartGap direction mass weight selected)
      = (∑ label ∈ selected, mass label / weight label * leverageOf (direction label))
        - ∑ label, mass label * leverageOf (direction label) := by
  rw [directionChartGap, Matrix.trace_sub, Matrix.trace_sum, Matrix.trace_sum]
  congr 1
  · exact Finset.sum_congr rfl fun label _ => by
      rw [Matrix.trace_smul, smul_eq_mul, trace_atomMatrix]
  · exact Finset.sum_congr rfl fun label _ => by
      rw [Matrix.trace_smul, smul_eq_mul, trace_atomMatrix]

/-- The boost of an atom times its weight is its leverage share. -/
theorem chartTraceBoost_mul_weight {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (point : DirectionChartPoint size) (label : Fin size) :
    chartTraceBoost direction point.mass point.weight label * point.weight label
      = point.mass label * leverageOf (direction label) := by
  rw [chartTraceBoost, div_mul_cancel₀ _ (point.weight_pos label).ne']
  ring

/-- A selected boost is the boosted leverage that the trace reads. -/
theorem chartTraceBoost_eq_selectedTerm {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (point : DirectionChartPoint size) (label : Fin size) :
    chartTraceBoost direction point.mass point.weight label
      = point.mass label / point.weight label * leverageOf (direction label) := by
  rw [chartTraceBoost]
  field_simp

theorem chartTraceBoost_pos {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (point : DirectionChartPoint size)
    (hlev : ∀ label, 0 < leverageOf (direction label)) (label : Fin size) :
    0 < chartTraceBoost direction point.mass point.weight label := by
  rw [chartTraceBoost]
  exact div_pos (mul_pos (hlev label) (point.mass_pos label)) (point.weight_pos label)

/-- **THE BOOST AVERAGE NEVER PASSES THE BOOST MAXIMUM.**  The weights are a
probability vector, so the total leverage share is a convex average of the six
boosts. -/
theorem chartLeverageShare_le_maximalBoost {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    (star : Fin size)
    (hmax : ∀ label, chartTraceBoost direction point.mass point.weight label
      ≤ chartTraceBoost direction point.mass point.weight star) :
    ∑ label, point.mass label * leverageOf (direction label)
      ≤ chartTraceBoost direction point.mass point.weight star := by
  calc ∑ label, point.mass label * leverageOf (direction label)
      = ∑ label, chartTraceBoost direction point.mass point.weight label
          * point.weight label :=
        Finset.sum_congr rfl fun label _ =>
          (chartTraceBoost_mul_weight direction point label).symm
    _ ≤ ∑ label, chartTraceBoost direction point.mass point.weight star
          * point.weight label :=
        Finset.sum_le_sum fun label _ =>
          mul_le_mul_of_nonneg_right (hmax label) (point.weight_pos label).le
    _ = chartTraceBoost direction point.mass point.weight star
          * ∑ label, point.weight label := by rw [Finset.mul_sum]
    _ = chartTraceBoost direction point.mass point.weight star := by
        rw [point.weight_sum_one, mul_one]

/-- **A SELECTION OF TWO OR MORE STRICTLY PASSES THE BOOST MAXIMUM.** -/
theorem maximalBoost_lt_selectedBoostSum {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    (hlev : ∀ label, 0 < leverageOf (direction label))
    (selected : Finset (Fin size)) (hcard : 2 ≤ selected.card)
    (star : Fin size) (hstar : star ∈ selected) :
    chartTraceBoost direction point.mass point.weight star
      < ∑ label ∈ selected, chartTraceBoost direction point.mass point.weight label := by
  have hsub : ({star} : Finset (Fin size)) ⊆ selected := Finset.singleton_subset_iff.mpr hstar
  have hne : ({star} : Finset (Fin size)) ≠ selected := by
    intro heq
    rw [← heq, Finset.card_singleton] at hcard
    norm_num at hcard
  obtain ⟨other, hother, hnotmem⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hsub hne)
  have hlt := Finset.sum_lt_sum_of_subset hsub hother hnotmem
    (chartTraceBoost_pos direction point hlev other)
    (fun label _ _ => (chartTraceBoost_pos direction point hlev label).le)
  rwa [Finset.sum_singleton] at hlt

/-- **THE TRACE FLOOR, DIRECTION GENERIC.**  At every chart point of every
direction family whose atoms are nonzero, the trace of the chart gap is strictly
positive at EVERY selection of two or more atoms that holds an atom of maximal
leverage boost.  The statement carries no hypothesis on the family beyond
nonzero atoms, and no cardinality bound other than two.

This designates one atom for one necessary sign at every stratum.  It claims
NOTHING about strict domination, and `Gtz.not_kFourMaxTraceBoostEdgeHostsStrictTree`
records that the hosting reading of this designation is false. -/
theorem trace_directionChartGap_pos_of_maximalBoost {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    (hlev : ∀ label, 0 < leverageOf (direction label))
    (selected : Finset (Fin size)) (hcard : 2 ≤ selected.card)
    (star : Fin size) (hstar : star ∈ selected)
    (hmax : ∀ label, chartTraceBoost direction point.mass point.weight label
      ≤ chartTraceBoost direction point.mass point.weight star) :
    0 < Matrix.trace (directionChartGap direction point.mass point.weight selected) := by
  rw [trace_directionChartGap]
  have hselected : ∑ label ∈ selected, point.mass label / point.weight label
        * leverageOf (direction label)
      = ∑ label ∈ selected, chartTraceBoost direction point.mass point.weight label :=
    Finset.sum_congr rfl fun label _ =>
      (chartTraceBoost_eq_selectedTerm direction point label).symm
  rw [hselected]
  have hceil := chartLeverageShare_le_maximalBoost direction point star hmax
  have hfloor := maximalBoost_lt_selectedBoostSum direction point hlev selected hcard star hstar
  linarith

/-- **A NONPOSITIVE TRACE KILLS DOMINATION.**  Direction generic. -/
theorem not_posDef_directionChartGap_of_trace_nonpos {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size))
    (htrace : Matrix.trace (directionChartGap direction mass weight selected) ≤ 0) :
    ¬ (directionChartGap direction mass weight selected).PosDef :=
  fun hposDef => absurd hposDef.trace_pos (not_lt.mpr htrace)

/-- **THE MOMENT IS MONOTONE IN ITS SCALES.**  Raising any scale keeps positive
definiteness, because the increment is a nonnegative moment.  Direction
generic. -/
theorem posDef_sum_smul_atomMatrix_of_le {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    {small big : Fin size → ℝ} (hle : ∀ label, small label ≤ big label)
    (hsmall : (∑ label, small label • atomMatrix (direction label)).PosDef) :
    (∑ label, big label • atomMatrix (direction label)).PosDef := by
  have hsplit : ∑ label, big label • atomMatrix (direction label)
      = (∑ label, small label • atomMatrix (direction label))
        + ∑ label, (big label - small label) • atomMatrix (direction label) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [← add_smul]
    congr 1
    ring
  rw [hsplit]
  exact hsmall.add_posSemidef (posSemidef_sum_smul_atomMatrix direction _
    fun label => by linarith [hle label])

/-- **THE DOMINATION ENGINE, DIRECTION GENERIC.**  Any pointwise LOWER bound on
the signed gap weight whose moment is positive definite certifies strict
domination of the selection.  Every certificate cell in this module is an
instance of this one theorem, and the theorem needs no basis, no determinant, no
eigenvalue and no whitener.

The bound is free: at `lower = signedGapWeight` the hypothesis IS the
conclusion, so the schema is complete and carries no information by itself.  A
cell is exactly a CHOICE of lower bound that is easier to test than the signed
gap weight. -/
theorem posDef_directionChartGap_of_dominatingWeight {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    (selected : Finset (Fin size)) (lower : Fin size → ℝ)
    (hle : ∀ label, lower label ≤ signedGapWeight point.mass point.weight selected label)
    (hlower : (∑ label, lower label • atomMatrix (direction label)).PosDef) :
    (directionChartGap direction point.mass point.weight selected).PosDef := by
  rw [directionChartGap_eq_sum_signedGapWeight direction point.mass point.weight selected
    (fun label _ => (point.weight_pos label).ne')]
  exact posDef_sum_smul_atomMatrix_of_le direction hle hlower

/-! ## 1. The unit conductance of `K4` -/

/-- **THE UNIT CONDUCTANCE.**  The three edges at the grounded vertex carry one
unit each and the other three carry nothing.  Its Laplacian is the identity. -/
noncomputable def kFourUnitConductance : Fin 6 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 1
  | 5 => 1

theorem kFourUnitConductance_zero : kFourUnitConductance 0 = 0 := rfl
theorem kFourUnitConductance_one : kFourUnitConductance 1 = 0 := rfl
theorem kFourUnitConductance_two : kFourUnitConductance 2 = 0 := rfl
theorem kFourUnitConductance_three : kFourUnitConductance 3 = 1 := rfl
theorem kFourUnitConductance_four : kFourUnitConductance 4 = 1 := rfl
theorem kFourUnitConductance_five : kFourUnitConductance 5 = 1 := rfl

/-- **THE UNIT CONDUCTANCE LAPLACIAN IS THE IDENTITY.**  The three directions of
the canonical gauge star are the coordinate axes. -/
theorem kFourLaplacian_unitConductance :
    kFourLaplacian kFourUnitConductance = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowIndex colIndex
  rw [kFourLaplacian, Matrix.sum_apply]
  simp only [Fin.sum_univ_six, Matrix.smul_apply, smul_eq_mul, atomMatrix,
    Matrix.vecMulVec_apply, kFourUnitConductance_zero, kFourUnitConductance_one,
    kFourUnitConductance_two, kFourUnitConductance_three, kFourUnitConductance_four,
    kFourUnitConductance_five, kFourDirection_three, kFourDirection_four,
    kFourDirection_five, zero_mul, zero_add, one_mul]
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-! ## 2. The three raw invariants -/

/-- The atom leverage of each `K4` edge: two for the three edges that miss the
grounded vertex, one for the three edges at it. -/
noncomputable def kFourTraceAtomWeight : Fin 6 → ℝ
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | 4 => 1
  | 5 => 1

theorem kFourTraceAtomWeight_zero : kFourTraceAtomWeight 0 = 2 := rfl
theorem kFourTraceAtomWeight_one : kFourTraceAtomWeight 1 = 2 := rfl
theorem kFourTraceAtomWeight_two : kFourTraceAtomWeight 2 = 2 := rfl
theorem kFourTraceAtomWeight_three : kFourTraceAtomWeight 3 = 1 := rfl
theorem kFourTraceAtomWeight_four : kFourTraceAtomWeight 4 = 1 := rfl
theorem kFourTraceAtomWeight_five : kFourTraceAtomWeight 5 = 1 := rfl

/-- **THE FIRST RAW INVARIANT.**  The atom leverages against the conductances.
Degree one, and no mass occurs. -/
noncomputable def kFourTraceSum (vec : Fin 6 → ℝ) : ℝ :=
  2 * (vec 0 + vec 1 + vec 2) + (vec 3 + vec 4 + vec 5)

/-- **THE SECOND RAW INVARIANT.**  The three contraction polynomials of the
canonical gauge star.  Degree two. -/
noncomputable def kFourSecondForestSum (vec : Fin 6 → ℝ) : ℝ :=
  kFourContractionTreePolynomial vec 3 + kFourContractionTreePolynomial vec 4
    + kFourContractionTreePolynomial vec 5

/-- **THE SECOND INVARIANT IS THE TWO-FOREST SUM.**  All fifteen two-edge
forests of `K4` occur, with the multiplicity three on the triangle that misses
the grounded vertex, two on the three perfect matchings, and one on the other
nine.  The multiplicity counts the vertices that the forest separates from the
grounded vertex. -/
theorem kFourSecondForestSum_eq (vec : Fin 6 → ℝ) :
    kFourSecondForestSum vec
      = 3 * (vec 0 * vec 1 + vec 0 * vec 2 + vec 1 * vec 2)
        + 2 * (vec 0 * vec 5 + vec 1 * vec 4 + vec 2 * vec 3)
        + (vec 3 * vec 4 + vec 3 * vec 5 + vec 4 * vec 5
          + vec 0 * vec 3 + vec 0 * vec 4 + vec 1 * vec 3 + vec 1 * vec 5
          + vec 2 * vec 4 + vec 2 * vec 5) := by
  simp only [kFourSecondForestSum, kFourContractionTreePolynomial_three,
    kFourContractionTreePolynomial_four, kFourContractionTreePolynomial_five]
  ring

/-- The first raw invariant as a weighted sum over the six labels. -/
theorem kFourTraceSum_eq_weightedSum (vec : Fin 6 → ℝ) :
    kFourTraceSum vec = ∑ label, kFourTraceAtomWeight label * vec label := by
  simp only [Fin.sum_univ_six, kFourTraceAtomWeight_zero, kFourTraceAtomWeight_one,
    kFourTraceAtomWeight_two, kFourTraceAtomWeight_three, kFourTraceAtomWeight_four,
    kFourTraceAtomWeight_five, kFourTraceSum]
  ring

/-- **THE TRACE OF A `K4` LAPLACIAN IS THE FIRST RAW INVARIANT.**  The adjugate
bridge against the unit conductance carries the whole proof. -/
theorem trace_kFourLaplacian_eq_traceSum (vec : Fin 6 → ℝ) :
    Matrix.trace (kFourLaplacian vec) = kFourTraceSum vec := by
  have hbridge := trace_adjugate_kFourLaplacian_mul kFourUnitConductance vec
  rw [kFourLaplacian_unitConductance, Matrix.adjugate_one, Matrix.one_mul] at hbridge
  rw [hbridge, kFourTraceSum]
  simp only [Fin.sum_univ_six, kFourContractionTreePolynomial_zero,
    kFourContractionTreePolynomial_one, kFourContractionTreePolynomial_two,
    kFourContractionTreePolynomial_three, kFourContractionTreePolynomial_four,
    kFourContractionTreePolynomial_five, kFourUnitConductance_zero,
    kFourUnitConductance_one, kFourUnitConductance_two, kFourUnitConductance_three,
    kFourUnitConductance_four, kFourUnitConductance_five]
  ring

/-- **THE ADJUGATE TRACE OF A `K4` LAPLACIAN IS THE SECOND RAW INVARIANT.** -/
theorem trace_adjugate_kFourLaplacian_eq_secondForestSum (vec : Fin 6 → ℝ) :
    Matrix.trace (kFourLaplacian vec).adjugate = kFourSecondForestSum vec := by
  have hbridge := trace_adjugate_kFourLaplacian_mul vec kFourUnitConductance
  rw [kFourLaplacian_unitConductance, Matrix.mul_one] at hbridge
  rw [hbridge, kFourSecondForestSum]
  simp only [Fin.sum_univ_six, kFourUnitConductance_zero, kFourUnitConductance_one,
    kFourUnitConductance_two, kFourUnitConductance_three, kFourUnitConductance_four,
    kFourUnitConductance_five]
  ring

/-! ## 3. The raw triple criterion -/

/-- **THE RAW TRIPLE IS SUFFICIENT.**  Three polynomial signs of the signed
conductance vector force positive definiteness of the `K4` Laplacian.  No
whitener, no mass and no eigenvalue occur. -/
theorem posDef_kFourLaplacian_of_rawTriple (vec : Fin 6 → ℝ)
    (htrace : 0 < kFourTraceSum vec) (hsecond : 0 < kFourSecondForestSum vec)
    (hdet : 0 < kFourMassTreeSum vec) : (kFourLaplacian vec).PosDef := by
  refine posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos
    (isHermitian_of_transpose_eq (kFourLaplacian_transpose vec)) ?_ ?_ ?_
  · rw [trace_kFourLaplacian_eq_traceSum]
    exact htrace
  · rw [← trace_adjugate_eq_secondInvariant,
      trace_adjugate_kFourLaplacian_eq_secondForestSum]
    exact hsecond
  · rw [det_kFourLaplacian]
    exact hdet

/-- The first raw sign is necessary. -/
theorem kFourTraceSum_pos_of_posDef {vec : Fin 6 → ℝ}
    (hposDef : (kFourLaplacian vec).PosDef) : 0 < kFourTraceSum vec := by
  rw [← trace_kFourLaplacian_eq_traceSum]
  exact hposDef.trace_pos

/-- The second raw sign is necessary. -/
theorem kFourSecondForestSum_pos_of_posDef {vec : Fin 6 → ℝ}
    (hposDef : (kFourLaplacian vec).PosDef) : 0 < kFourSecondForestSum vec := by
  rw [← trace_adjugate_kFourLaplacian_eq_secondForestSum]
  exact (posDef_adjugate_fin_three hposDef).trace_pos

/-- The third raw sign is necessary. -/
theorem kFourMassTreeSum_pos_of_posDef {vec : Fin 6 → ℝ}
    (hposDef : (kFourLaplacian vec).PosDef) : 0 < kFourMassTreeSum vec := by
  rw [← det_kFourLaplacian]
  exact hposDef.det_pos

/-- **THE RAW TRIPLE CRITERION.**  Positive definiteness of the `K4` signed
Laplacian IS the positivity of one linear, one quadratic and one cubic form of
the conductance vector.  The statement carries no matrix. -/
theorem posDef_kFourLaplacian_iff_rawTriple (vec : Fin 6 → ℝ) :
    (kFourLaplacian vec).PosDef
      ↔ (0 < kFourTraceSum vec ∧ 0 < kFourSecondForestSum vec
        ∧ 0 < kFourMassTreeSum vec) :=
  ⟨fun hposDef => ⟨kFourTraceSum_pos_of_posDef hposDef,
      kFourSecondForestSum_pos_of_posDef hposDef,
      kFourMassTreeSum_pos_of_posDef hposDef⟩,
    fun htriple => posDef_kFourLaplacian_of_rawTriple vec htriple.1 htriple.2.1 htriple.2.2⟩

/-- **THE LAPLACIAN IS MONOTONE IN ITS CONDUCTANCES.**  Raising any conductance
keeps positive definiteness, because the increment is a nonnegative Laplacian.
This is the engine of every cell below. -/
theorem posDef_kFourLaplacian_of_le {small big : Fin 6 → ℝ}
    (hle : ∀ label, small label ≤ big label)
    (hsmall : (kFourLaplacian small).PosDef) : (kFourLaplacian big).PosDef := by
  have hsplit : big = small + (big - small) := by
    funext label
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hsplit, kFourLaplacian_add]
  refine hsmall.add_posSemidef (posSemidef_kFourLaplacian _ fun label => ?_)
  simp only [Pi.sub_apply]
  linarith [hle label]

/-! ## 4. The chart gap in raw form -/

/-- The chart gap of a `K4` selection IS the signed Laplacian of its signed gap
weight. -/
theorem directionChartGap_eq_kFourLaplacian_signed (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) (hweight : ∀ label ∈ selected, weight label ≠ 0) :
    directionChartGap kFourDirection mass weight selected
      = kFourLaplacian (signedGapWeight mass weight selected) := by
  rw [kFourLaplacian]
  exact directionChartGap_eq_sum_signedGapWeight kFourDirection mass weight selected hweight

/-- **THE CHART CRITERION IN RAW FORM.**  Strict domination of a listed
selection is three polynomial signs of the signed gap weight, and the masses
occur only inside that one vector. -/
theorem posDef_directionChartGap_iff_rawTriple (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) :
    (directionChartGap kFourDirection point.mass point.weight selected).PosDef
      ↔ (0 < kFourTraceSum (signedGapWeight point.mass point.weight selected)
        ∧ 0 < kFourSecondForestSum (signedGapWeight point.mass point.weight selected)
        ∧ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight selected)) := by
  rw [directionChartGap_eq_kFourLaplacian_signed point.mass point.weight selected
    (fun label _ => (point.weight_pos label).ne')]
  exact posDef_kFourLaplacian_iff_rawTriple _

/-! ## 5. The sharp trace floor and its designated edge -/

/-- **THE TRACE BOOST OF AN EDGE.**  Its atom leverage times its mass over its
weight.  This is the quantity the first raw sign reads. -/
noncomputable def kFourTraceBoost (mass weight : Fin 6 → ℝ) (label : Fin 6) : ℝ :=
  kFourTraceAtomWeight label * mass label / weight label

theorem kFourTraceAtomWeight_pos (label : Fin 6) : 0 < kFourTraceAtomWeight label := by
  rcases fin_six_cases label with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [kFourTraceAtomWeight_zero, kFourTraceAtomWeight_one,
      kFourTraceAtomWeight_two, kFourTraceAtomWeight_three, kFourTraceAtomWeight_four,
      kFourTraceAtomWeight_five] <;> norm_num

theorem kFourTraceBoost_pos (point : DirectionChartPoint 6) (label : Fin 6) :
    0 < kFourTraceBoost point.mass point.weight label := by
  rw [kFourTraceBoost]
  exact div_pos (mul_pos (kFourTraceAtomWeight_pos label) (point.mass_pos label))
    (point.weight_pos label)

/-- The boost of an edge times its weight is its atom leverage share. -/
theorem kFourTraceBoost_mul_weight (point : DirectionChartPoint 6) (label : Fin 6) :
    kFourTraceBoost point.mass point.weight label * point.weight label
      = kFourTraceAtomWeight label * point.mass label := by
  rw [kFourTraceBoost, div_mul_cancel₀]
  exact (point.weight_pos label).ne'

/-- **THE FIRST RAW SIGN IS A BOOST DEFECT.**  The selected boosts against the
total atom leverage share.  No matrix survives. -/
theorem kFourTraceSum_signedGapWeight (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) :
    kFourTraceSum (signedGapWeight point.mass point.weight tree)
      = (∑ label ∈ tree, kFourTraceBoost point.mass point.weight label)
        - ∑ label, kFourTraceAtomWeight label * point.mass label := by
  rw [kFourTraceSum_eq_weightedSum, ← Finset.sum_add_sum_compl tree]
  have hinside : ∑ label ∈ tree, kFourTraceAtomWeight label
        * signedGapWeight point.mass point.weight tree label
      = (∑ label ∈ tree, kFourTraceBoost point.mass point.weight label)
        - ∑ label ∈ tree, kFourTraceAtomWeight label * point.mass label := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun label hlabel => ?_
    rw [signedGapWeight_mem point.mass point.weight hlabel, kFourTraceBoost]
    have hne := (point.weight_pos label).ne'
    field_simp
  have houtside : ∑ label ∈ treeᶜ, kFourTraceAtomWeight label
        * signedGapWeight point.mass point.weight tree label
      = -∑ label ∈ treeᶜ, kFourTraceAtomWeight label * point.mass label := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun label hlabel => ?_
    rw [signedGapWeight_not_mem point.mass point.weight (Finset.mem_compl.mp hlabel)]
    ring
  have hwhole : ∑ label ∈ tree, kFourTraceAtomWeight label * point.mass label
      + ∑ label ∈ treeᶜ, kFourTraceAtomWeight label * point.mass label
      = ∑ label, kFourTraceAtomWeight label * point.mass label :=
    Finset.sum_add_sum_compl tree _
  rw [hinside, houtside]
  linarith [hwhole]

/-- **THE `K4` ATOM LEVERAGE.**  The three edges that miss the grounded vertex
have leverage two and the three at it have leverage one. -/
theorem leverageOf_kFourDirection (label : Fin 6) :
    leverageOf (kFourDirection label) = kFourTraceAtomWeight label := by
  rcases fin_six_cases label with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [leverageOf, Fin.sum_univ_three, kFourDirection_zero, kFourDirection_one,
      kFourDirection_two, kFourDirection_three, kFourDirection_four, kFourDirection_five,
      kFourTraceAtomWeight_zero, kFourTraceAtomWeight_one, kFourTraceAtomWeight_two,
      kFourTraceAtomWeight_three, kFourTraceAtomWeight_four, kFourTraceAtomWeight_five,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] <;>
    norm_num

/-- The `K4` trace boost IS the direction-generic leverage boost. -/
theorem kFourTraceBoost_eq_chartTraceBoost (mass weight : Fin 6 → ℝ) (label : Fin 6) :
    kFourTraceBoost mass weight label = chartTraceBoost kFourDirection mass weight label := by
  rw [kFourTraceBoost, chartTraceBoost, leverageOf_kFourDirection]

/-- The first raw invariant IS the trace of the chart gap. -/
theorem trace_directionChartGap_kFour (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) :
    Matrix.trace (directionChartGap kFourDirection point.mass point.weight tree)
      = kFourTraceSum (signedGapWeight point.mass point.weight tree) := by
  rw [directionChartGap_eq_kFourLaplacian_signed point.mass point.weight tree
      (fun label _ => (point.weight_pos label).ne'),
    trace_kFourLaplacian_eq_traceSum]

/-- **THE TRACE FLOOR IN `K4` FOREST COORDINATES.**  This is the instance of
`Gtz.trace_directionChartGap_pos_of_maximalBoost` at the `K4` chart, and it is
not a separate argument.  EVERY listed tree through an edge of maximal trace
boost makes the first raw sign strictly positive, at every chart point, with no
hypothesis.  It designates nothing about the second and third signs, and it
makes no claim of strict domination. -/
theorem kFourTraceSum_pos_of_maximalBoost (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (hcard : 2 ≤ tree.card) (star : Fin 6) (hstar : star ∈ tree)
    (hmax : ∀ label, kFourTraceBoost point.mass point.weight label
      ≤ kFourTraceBoost point.mass point.weight star) :
    0 < kFourTraceSum (signedGapWeight point.mass point.weight tree) := by
  rw [← trace_directionChartGap_kFour point tree]
  refine trace_directionChartGap_pos_of_maximalBoost kFourDirection point ?_ tree hcard
    star hstar ?_
  · intro label
    rw [leverageOf_kFourDirection]
    exact kFourTraceAtomWeight_pos label
  · intro label
    rw [← kFourTraceBoost_eq_chartTraceBoost, ← kFourTraceBoost_eq_chartTraceBoost]
    exact hmax label

/-- Every label sits in a listed spanning tree of at least two labels. -/
theorem exists_kFourSpanningTree_mem (label : Fin 6) :
    ∃ tree ∈ kFourSpanningTreeList, label ∈ tree ∧ 2 ≤ tree.card := by
  fin_cases label
  · exact ⟨{0, 1, 3}, by decide, by decide, by decide⟩
  · exact ⟨{0, 1, 3}, by decide, by decide, by decide⟩
  · exact ⟨{0, 2, 4}, by decide, by decide, by decide⟩
  · exact ⟨{0, 1, 3}, by decide, by decide, by decide⟩
  · exact ⟨{0, 2, 4}, by decide, by decide, by decide⟩
  · exact ⟨{1, 2, 5}, by decide, by decide, by decide⟩

/-- **THE FIRST RAW SIGN IS NEVER TOTAL.**  At every chart point some listed
spanning tree makes the first raw sign strictly positive, with no hypothesis. -/
theorem exists_kFourSpanningTree_traceSum_pos (point : DirectionChartPoint 6) :
    ∃ tree ∈ kFourSpanningTreeList,
      0 < kFourTraceSum (signedGapWeight point.mass point.weight tree) := by
  obtain ⟨star, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 6))
    (kFourTraceBoost point.mass point.weight) ⟨0, Finset.mem_univ 0⟩
  obtain ⟨tree, hmem, hstar, hcard⟩ := exists_kFourSpanningTree_mem star
  exact ⟨tree, hmem, kFourTraceSum_pos_of_maximalBoost point tree hcard star hstar
    fun label => hmax label (Finset.mem_univ label)⟩

/-- The first raw exclusion never refuses every listed tree. -/
theorem not_forall_kFourSpanningTree_traceSum_nonpos (point : DirectionChartPoint 6) :
    ¬ ∀ tree ∈ kFourSpanningTreeList,
        kFourTraceSum (signedGapWeight point.mass point.weight tree) ≤ 0 := by
  intro hall
  obtain ⟨tree, hmem, hpos⟩ := exists_kFourSpanningTree_traceSum_pos point
  exact absurd (hall tree hmem) (not_le.mpr hpos)

/-! ## 6. The scalar shift cell -/

/-- The masses carried by a selection, and nothing off it. -/
noncomputable def kFourTreeMass (mass : Fin 6 → ℝ) (tree : Finset (Fin 6)) : Fin 6 → ℝ :=
  fun label => if label ∈ tree then mass label else 0

/-- **THE SHIFT VECTOR OF A LEVEL.**  The tree masses less the level times all
the masses.  Its Laplacian is the tree moment less the level times the mass
moment. -/
noncomputable def kFourShiftVector (mass : Fin 6 → ℝ) (tree : Finset (Fin 6))
    (level : ℝ) : Fin 6 → ℝ :=
  fun label => kFourTreeMass mass tree label - level * mass label

theorem kFourShiftVector_mem (mass : Fin 6 → ℝ) {tree : Finset (Fin 6)} {label : Fin 6}
    (hmem : label ∈ tree) (level : ℝ) :
    kFourShiftVector mass tree level label = mass label - level * mass label := by
  simp only [kFourShiftVector, kFourTreeMass, hmem, ite_true]

theorem kFourShiftVector_not_mem (mass : Fin 6 → ℝ) {tree : Finset (Fin 6)} {label : Fin 6}
    (hmem : label ∉ tree) (level : ℝ) :
    kFourShiftVector mass tree level label = -(level * mass label) := by
  simp only [kFourShiftVector, kFourTreeMass, hmem, ite_false]
  ring

/-- **THE CONDUCTANCE DOMINATION.**  If a level passes every selected weight,
the signed gap weight passes the scaled shift vector at every label, with
EQUALITY off the selection.  Only the selected labels pay anything. -/
theorem scaledShiftVector_le_signedGapWeight (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) {level : ℝ} (hlevel : 0 < level)
    (hle : ∀ label ∈ tree, point.weight label ≤ level) (label : Fin 6) :
    level⁻¹ * kFourShiftVector point.mass tree level label
      ≤ signedGapWeight point.mass point.weight tree label := by
  by_cases hmem : label ∈ tree
  · rw [signedGapWeight_mem point.mass point.weight hmem,
      kFourShiftVector_mem point.mass hmem level, ← sub_nonneg]
    have hweight := point.weight_pos label
    have hmass := point.mass_pos label
    have hbound := hle label hmem
    have hid : point.mass label * (1 - point.weight label) / point.weight label
        - level⁻¹ * (point.mass label - level * point.mass label)
        = point.mass label * (level - point.weight label)
            / (point.weight label * level) := by
      field_simp
      ring
    rw [hid]
    exact div_nonneg (mul_nonneg hmass.le (by linarith))
      (by positivity)
  · rw [signedGapWeight_not_mem point.mass point.weight hmem,
      kFourShiftVector_not_mem point.mass hmem level]
    have hne : level ≠ 0 := hlevel.ne'
    have hstep : level⁻¹ * -(level * point.mass label) = -(point.mass label) := by
      field_simp
    rw [hstep]

/-- **THE SCALAR SHIFT CELL.**  Fix a listed selection and a level that passes
every weight on it.  If the three raw signs of the shift vector are positive,
the selection dominates strictly.

The proof spends nothing: the chart gap is the scaled shift Laplacian plus a
Laplacian of nonnegative conductances, and a positive definite matrix plus a
positive semidefinite one is positive definite.  No whitener, no square root,
no eigenvalue and no determinant division occur. -/
theorem posDef_directionChartGap_of_scalarShift (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) {level : ℝ} (hlevel : 0 < level)
    (hle : ∀ label ∈ tree, point.weight label ≤ level)
    (htrace : 0 < kFourTraceSum (kFourShiftVector point.mass tree level))
    (hsecond : 0 < kFourSecondForestSum (kFourShiftVector point.mass tree level))
    (hdet : 0 < kFourMassTreeSum (kFourShiftVector point.mass tree level)) :
    (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  have hshift : (kFourLaplacian (kFourShiftVector point.mass tree level)).PosDef :=
    posDef_kFourLaplacian_of_rawTriple _ htrace hsecond hdet
  have hscaled :
      (kFourLaplacian (level⁻¹ • kFourShiftVector point.mass tree level)).PosDef := by
    rw [kFourLaplacian_smul]
    exact hshift.smul (inv_pos.mpr hlevel)
  set rest : Fin 6 → ℝ := signedGapWeight point.mass point.weight tree
      - level⁻¹ • kFourShiftVector point.mass tree level with hrestDef
  have hrestNonneg : ∀ label, 0 ≤ rest label := by
    intro label
    have hdom := scaledShiftVector_le_signedGapWeight point tree hlevel hle label
    simp only [hrestDef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hsplit : signedGapWeight point.mass point.weight tree
      = level⁻¹ • kFourShiftVector point.mass tree level + rest := by
    funext label
    simp only [hrestDef, Pi.add_apply, Pi.sub_apply]
    ring
  rw [directionChartGap_eq_kFourLaplacian_signed point.mass point.weight tree
      (fun label _ => (point.weight_pos label).ne'), hsplit, kFourLaplacian_add]
  exact hscaled.add_posSemidef (posSemidef_kFourLaplacian rest hrestNonneg)

/-- **THE CELL IN ONE PACKAGE.**  A named cell for the atlas. -/
def KFourScalarShiftCellFires (point : DirectionChartPoint 6) (tree : Finset (Fin 6))
    (level : ℝ) : Prop :=
  0 < level ∧ (∀ label ∈ tree, point.weight label ≤ level)
    ∧ 0 < kFourTraceSum (kFourShiftVector point.mass tree level)
    ∧ 0 < kFourSecondForestSum (kFourShiftVector point.mass tree level)
    ∧ 0 < kFourMassTreeSum (kFourShiftVector point.mass tree level)

/-- A firing cell gives strict domination. -/
theorem posDef_directionChartGap_of_scalarShiftCell (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (level : ℝ)
    (hcell : KFourScalarShiftCellFires point tree level) :
    (directionChartGap kFourDirection point.mass point.weight tree).PosDef :=
  posDef_directionChartGap_of_scalarShift point tree hcell.1 hcell.2.1 hcell.2.2.1
    hcell.2.2.2.1 hcell.2.2.2.2

/-- A firing cell at a LISTED selection gives the universal strict tree at that
point. -/
theorem exists_strictTree_of_scalarShiftCell (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (hmem : tree ∈ kFourSpanningTreeList) (level : ℝ)
    (hcell : KFourScalarShiftCellFires point tree level) :
    ∃ selected ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight selected).PosDef :=
  ⟨tree, hmem, posDef_directionChartGap_of_scalarShiftCell point tree level hcell⟩

/-! ## 6b. The level vector family, and its completeness

The scalar shift cell replaces every selected weight by ONE level.  That single
scalar is the whole loss: a level VECTOR loses nothing.  This section states the
cell for a free level vector and proves the family COMPLETE — the member at
`level = point.weight` is the chart obligation itself.  So the certificate
schema covers the whole chart, and the scalar member is the computable part of
it.  MEASURED, AND NOT A THEOREM: an exact-rational census of 20000 random
chart points fires the scalar member at 92.55 percent of them. -/

/-- **THE LEVEL SHIFT VECTOR.**  Each selected label carries its mass against a
free level instead of against its own weight.  Each other label carries minus
its mass. -/
noncomputable def kFourLevelShiftVector (mass : Fin 6 → ℝ) (tree : Finset (Fin 6))
    (level : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun label => if label ∈ tree then mass label / level label - mass label else -(mass label)

theorem kFourLevelShiftVector_mem (mass : Fin 6 → ℝ) {tree : Finset (Fin 6)}
    {label : Fin 6} (hmem : label ∈ tree) (level : Fin 6 → ℝ) :
    kFourLevelShiftVector mass tree level label
      = mass label / level label - mass label := by
  simp only [kFourLevelShiftVector, hmem, ite_true]

theorem kFourLevelShiftVector_not_mem (mass : Fin 6 → ℝ) {tree : Finset (Fin 6)}
    {label : Fin 6} (hmem : label ∉ tree) (level : Fin 6 → ℝ) :
    kFourLevelShiftVector mass tree level label = -(mass label) := by
  simp only [kFourLevelShiftVector, hmem, ite_false]

/-- **THE WEIGHT IS A LEVEL VECTOR, AND IT IS THE EXACT ONE.**  At
`level = point.weight` the level shift vector IS the signed gap weight. -/
theorem kFourLevelShiftVector_weight (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) :
    kFourLevelShiftVector point.mass tree point.weight
      = signedGapWeight point.mass point.weight tree := by
  funext label
  by_cases hmem : label ∈ tree
  · rw [kFourLevelShiftVector_mem point.mass hmem,
      signedGapWeight_mem point.mass point.weight hmem]
    have hne := (point.weight_pos label).ne'
    field_simp
  · rw [kFourLevelShiftVector_not_mem point.mass hmem,
      signedGapWeight_not_mem point.mass point.weight hmem]

/-- **THE LEVEL SHIFT CELL.**  Fix a listed selection and a level vector that
passes every weight on it.  If the three raw signs of the level shift vector
are positive, the selection dominates strictly.  Laplacian monotonicity carries
the whole proof. -/
theorem posDef_directionChartGap_of_levelShift (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (level : Fin 6 → ℝ)
    (hpos : ∀ label ∈ tree, 0 < level label)
    (hle : ∀ label ∈ tree, point.weight label ≤ level label)
    (htrace : 0 < kFourTraceSum (kFourLevelShiftVector point.mass tree level))
    (hsecond : 0 < kFourSecondForestSum (kFourLevelShiftVector point.mass tree level))
    (hdet : 0 < kFourMassTreeSum (kFourLevelShiftVector point.mass tree level)) :
    (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  rw [directionChartGap_eq_kFourLaplacian_signed point.mass point.weight tree
    (fun label _ => (point.weight_pos label).ne')]
  refine posDef_kFourLaplacian_of_le (small := kFourLevelShiftVector point.mass tree level)
    ?_ (posDef_kFourLaplacian_of_rawTriple _ htrace hsecond hdet)
  intro label
  by_cases hmem : label ∈ tree
  · rw [kFourLevelShiftVector_mem point.mass hmem,
      signedGapWeight_mem point.mass point.weight hmem, ← sub_nonneg]
    have hweight := point.weight_pos label
    have hmass := point.mass_pos label
    have hlevel := hpos label hmem
    have hbound := hle label hmem
    have hid : point.mass label * (1 - point.weight label) / point.weight label
        - (point.mass label / level label - point.mass label)
        = point.mass label * (level label - point.weight label)
            / (point.weight label * level label) := by
      field_simp
      ring
    rw [hid]
    exact div_nonneg (mul_nonneg hmass.le (by linarith)) (by positivity)
  · rw [kFourLevelShiftVector_not_mem point.mass hmem,
      signedGapWeight_not_mem point.mass point.weight hmem]

/-- **THE LEVEL SHIFT SCHEMA.**  Some listed selection carries a level vector
whose three raw signs are positive. -/
def KFourLevelShiftTotal : Prop :=
  ∀ point : DirectionChartPoint 6, ∃ tree ∈ kFourSpanningTreeList, ∃ level : Fin 6 → ℝ,
    (∀ label ∈ tree, 0 < level label) ∧ (∀ label ∈ tree, point.weight label ≤ level label)
      ∧ 0 < kFourTraceSum (kFourLevelShiftVector point.mass tree level)
      ∧ 0 < kFourSecondForestSum (kFourLevelShiftVector point.mass tree level)
      ∧ 0 < kFourMassTreeSum (kFourLevelShiftVector point.mass tree level)

/-- **THE SCHEMA IS COMPLETE, AND THIS THEOREM SAYS SO.**  The level shift
family loses nothing: its member at `level = point.weight` is the chart
obligation itself.  So the schema covers the whole chart, and the scalar member
of section 6 is a proper part of it.  This is an EQUIVALENCE and never a
producer. -/
theorem kFourUniversalStrictTree_iff_levelShiftTotal :
    KFourUniversalStrictTree ↔ KFourLevelShiftTotal := by
  constructor
  · intro hstrict point
    obtain ⟨tree, hmem, hposDef⟩ := hstrict point
    obtain ⟨htrace, hsecond, hdet⟩ :=
      (posDef_directionChartGap_iff_rawTriple point tree).mp hposDef
    have hrw := kFourLevelShiftVector_weight point tree
    exact ⟨tree, hmem, point.weight, fun label _ => point.weight_pos label,
      fun label _ => le_refl _, by rw [hrw]; exact htrace, by rw [hrw]; exact hsecond,
      by rw [hrw]; exact hdet⟩
  · intro htotal point
    obtain ⟨tree, hmem, level, hpos, hle, htrace, hsecond, hdet⟩ := htotal point
    exact ⟨tree, hmem, posDef_directionChartGap_of_levelShift point tree level hpos hle
      htrace hsecond hdet⟩

/-- The complete schema closes all four registered consumers. -/
theorem kFourLevelShiftTotal_closes_all (htotal : KFourLevelShiftTotal) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict
      ∧ DirectionChartIsTieFree kFourDirection
      ∧ KFourFamilySelection
      ∧ KFourKnifeBandRefinedWeakToStrict :=
  kFourStrictTree_closes_all (kFourUniversalStrictTree_iff_levelShiftTotal.mpr htotal)

/-! ## 6c. The pivot member, and how far the schema can be relaxed

The scalar member of section 6 replaces ALL THREE selected weights by one
level.  The pivot member below keeps one selected weight exact and replaces the
other two by one level, so it relaxes at most ONE weight of the selection.  It
is strictly stronger than the scalar member.

MEASURED, AND NOT A THEOREM.  A floating-point census of 300000 random chart
points fires the scalar member at 97.72 percent and the pivot member at 300000
of 300000.  Uniform sampling is not evidence here.  A directed hunt of 260
restarts refutes the pivot member: at the masses `(1, 696, 456, 314, 332, 1)`
and the weights `(1, 467, 251, 1, 79, 1) / 800` the only dominating tree is
`{2, 3, 4}`, and all forty-eight pivot members fail, forty-three of them on the
determinant and five on the second sign.  The exact-rational census of 20000
points also fires the landed `Gtz.KFourPencilCellFires` at every point where the
pivot member fires, so neither new member enlarges the atlas on that sample.

So no member that relaxes one weight is total, and the schema reaches the whole
chart only at `level = point.weight`, where
`Gtz.kFourUniversalStrictTree_iff_levelShiftTotal` shows it IS the chart
obligation.  That equivalence is a restatement and never progress. -/

/-- **THE PIVOT LEVEL VECTOR.**  One designated selected label keeps its own
weight, and every other label takes a common level. -/
noncomputable def kFourPivotLevel (weight : Fin 6 → ℝ) (pivot : Fin 6) (level : ℝ) :
    Fin 6 → ℝ :=
  fun label => if label = pivot then weight label else level

theorem kFourPivotLevel_self (weight : Fin 6 → ℝ) (pivot : Fin 6) (level : ℝ) :
    kFourPivotLevel weight pivot level pivot = weight pivot := by
  simp only [kFourPivotLevel, if_true, eq_self_iff_true]

theorem kFourPivotLevel_ne (weight : Fin 6 → ℝ) {pivot label : Fin 6} (hne : label ≠ pivot)
    (level : ℝ) : kFourPivotLevel weight pivot level label = level := by
  simp only [kFourPivotLevel, if_neg hne]

/-- **THE PIVOT CELL.**  Keep the weight of one selected label and raise every
other selected weight to a common level.  If the three raw signs of the
resulting level shift vector are positive, the selection dominates strictly. -/
theorem posDef_directionChartGap_of_pivotShift (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (pivot : Fin 6) {level : ℝ} (hlevel : 0 < level)
    (hle : ∀ label ∈ tree, label ≠ pivot → point.weight label ≤ level)
    (htrace : 0 < kFourTraceSum (kFourLevelShiftVector point.mass tree
      (kFourPivotLevel point.weight pivot level)))
    (hsecond : 0 < kFourSecondForestSum (kFourLevelShiftVector point.mass tree
      (kFourPivotLevel point.weight pivot level)))
    (hdet : 0 < kFourMassTreeSum (kFourLevelShiftVector point.mass tree
      (kFourPivotLevel point.weight pivot level))) :
    (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  refine posDef_directionChartGap_of_levelShift point tree
    (kFourPivotLevel point.weight pivot level) ?_ ?_ htrace hsecond hdet
  · intro label _
    by_cases hpivot : label = pivot
    · subst hpivot
      rw [kFourPivotLevel_self]
      exact point.weight_pos label
    · rw [kFourPivotLevel_ne point.weight hpivot]
      exact hlevel
  · intro label hlabel
    by_cases hpivot : label = pivot
    · subst hpivot
      rw [kFourPivotLevel_self]
    · rw [kFourPivotLevel_ne point.weight hpivot]
      exact hle label hlabel hpivot

/-! ## 7. The cell is inhabited at the two mandatory points -/

/-- **THE CELL FIRES AT THE TETRAHEDRON.**  The canonical gauge star `{3, 4, 5}`
at the level `1/6` carries the shift vector `(-1/24, -1/24, -1/24, 5/24, 5/24,
5/24)`, whose three raw invariants are `3/8`, `1/24` and `5/3456`. -/
theorem tetrahedronChartPoint_scalarShiftCellFires :
    KFourScalarShiftCellFires tetrahedronChartPoint ({3, 4, 5} : Finset (Fin 6))
      (1 / 6) := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · intro label _
    show (1 / 6 : ℝ) ≤ 1 / 6
    norm_num
  · norm_num [kFourTraceSum, kFourShiftVector, kFourTreeMass, tetrahedronChartPoint,
      Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  · norm_num [kFourSecondForestSum_eq, kFourShiftVector, kFourTreeMass,
      tetrahedronChartPoint, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  · norm_num [kFourMassTreeSum, kFourShiftVector, kFourTreeMass, tetrahedronChartPoint,
      Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]

/-- The tetrahedron dominates strictly at the canonical gauge star, through the
new cell. -/
theorem tetrahedronChartPoint_posDef_threeFourFive :
    (directionChartGap kFourDirection tetrahedronChartPoint.mass
      tetrahedronChartPoint.weight ({3, 4, 5} : Finset (Fin 6))).PosDef :=
  posDef_directionChartGap_of_scalarShiftCell tetrahedronChartPoint _ _
    tetrahedronChartPoint_scalarShiftCellFires

/-- **THE CELL FIRES AT THE REFUTER.**  `Gtz.traceRefuterPoint` kills every
single-tree rule of `Gtz/Wave/WiringKFourWalls.lean`.  The cell still fires
there, at the tree `{0, 1, 3}` and the level `1/8`: the shift vector is
`(7/8, 7/8, -1/4, 7/8, -1/4, -1/8)` and its three raw invariants are `7/2`,
`57/64` and `21/512`. -/
theorem traceRefuterPoint_scalarShiftCellFires :
    KFourScalarShiftCellFires traceRefuterPoint ({0, 1, 3} : Finset (Fin 6)) (1 / 8) := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · intro label hlabel
    fin_cases label <;>
      simp_all [traceRefuterPoint, traceRefuterWeight, Finset.mem_insert,
        Finset.mem_singleton]
  · norm_num [kFourTraceSum, kFourShiftVector, kFourTreeMass, traceRefuterPoint,
      traceRefuterMass, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  · norm_num [kFourSecondForestSum_eq, kFourShiftVector, kFourTreeMass,
      traceRefuterPoint, traceRefuterMass, Finset.mem_insert, Finset.mem_singleton,
      Fin.ext_iff]
  · norm_num [kFourMassTreeSum, kFourShiftVector, kFourTreeMass, traceRefuterPoint,
      traceRefuterMass, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]

/-- **THE REFUTER STILL HAS A STRICTLY DOMINATING TREE.**  The tree `{0, 1, 3}`
dominates at `Gtz.traceRefuterPoint`, so the three refutations of
`Gtz/Wave/WiringKFourWalls.lean` are about the SELECTION RULES and never about
the chart obligation. -/
theorem traceRefuterPoint_posDef_zeroOneThree :
    (directionChartGap kFourDirection traceRefuterPoint.mass
      traceRefuterPoint.weight ({0, 1, 3} : Finset (Fin 6))).PosDef :=
  posDef_directionChartGap_of_scalarShiftCell traceRefuterPoint _ _
    traceRefuterPoint_scalarShiftCellFires

/-! ## 8. The sixteen signed tree sums at the refuter

The table below is the whole determinant column of `Gtz.traceRefuterPoint`.
Seven of the sixteen listed trees carry a strictly positive signed tree sum:
`{0,1,3}`, `{0,2,4}`, `{1,2,5}`, `{0,2,3}`, `{0,2,5}`, `{1,2,4}` and `{2,3,5}`.
So the disjunction over the tree list survives at the point that kills every
fixed local rule, and `Gtz.KFourBlockAdmissibleDetTotal` is not refuted there. -/

/-- **THE SIXTEEN-ROW TABLE.**  Every signed tree sum of
`Gtz.traceRefuterPoint`, in exact rationals, in the order of
`Gtz.kFourSpanningTreeList`. -/
theorem traceRefuterPoint_massTreeSum_table :
    kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({0, 1, 3} : Finset (Fin 6))) = 21
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({0, 2, 4} : Finset (Fin 6))) = 191 / 3
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({1, 2, 5} : Finset (Fin 6))) = 189
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({3, 4, 5} : Finset (Fin 6))) = -41 / 3
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({0, 1, 4} : Finset (Fin 6))) = -27
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({0, 1, 5} : Finset (Fin 6))) = -123
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({0, 2, 3} : Finset (Fin 6))) = 5
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({0, 2, 5} : Finset (Fin 6))) = 117
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({0, 3, 5} : Finset (Fin 6))) = -123
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({0, 4, 5} : Finset (Fin 6))) = -257 / 3
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({1, 2, 3} : Finset (Fin 6))) = -51
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({1, 2, 4} : Finset (Fin 6))) = 29
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({1, 3, 4} : Finset (Fin 6))) = -83
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({1, 4, 5} : Finset (Fin 6))) = -169 / 3
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({2, 3, 4} : Finset (Fin 6))) = -169 / 3
    ∧ kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass traceRefuterPoint.weight
        ({2, 3, 5} : Finset (Fin 6))) = 61 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [kFourMassTreeSum, signedGapWeight, traceRefuterPoint, traceRefuterMass,
      traceRefuterWeight, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]

/-- **SEVEN OF THE SIXTEEN SURVIVE.**  The determinant sign of the refuter admits
seven listed trees. -/
theorem traceRefuterPoint_massTreeSum_pos_count :
    0 < kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass
        traceRefuterPoint.weight ({0, 1, 3} : Finset (Fin 6)))
    ∧ 0 < kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass
        traceRefuterPoint.weight ({0, 2, 4} : Finset (Fin 6)))
    ∧ 0 < kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass
        traceRefuterPoint.weight ({1, 2, 5} : Finset (Fin 6)))
    ∧ 0 < kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass
        traceRefuterPoint.weight ({0, 2, 3} : Finset (Fin 6)))
    ∧ 0 < kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass
        traceRefuterPoint.weight ({0, 2, 5} : Finset (Fin 6)))
    ∧ 0 < kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass
        traceRefuterPoint.weight ({1, 2, 4} : Finset (Fin 6)))
    ∧ 0 < kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass
        traceRefuterPoint.weight ({2, 3, 5} : Finset (Fin 6))) := by
  obtain ⟨h0, h1, h2, -, -, -, h6, h7, -, -, -, h11, -, -, -, h15⟩ :=
    traceRefuterPoint_massTreeSum_table
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0]; norm_num
  · rw [h1]; norm_num
  · rw [h2]; norm_num
  · rw [h6]; norm_num
  · rw [h7]; norm_num
  · rw [h11]; norm_num
  · rw [h15]; norm_num

/-- **THE SCHUR RESIDUAL IS INHABITED AT THE REFUTER.**  The tree `{0, 1, 3}`
carries a positive definite leading block and a positive signed tree sum, so
the residual `Gtz.KFourBlockAdmissibleDetTotal` of
`Gtz/Wave/WiringKFourWalls.lean` holds at the hardest known point. -/
theorem traceRefuterPoint_blockAdmissibleDet :
    ∃ tree ∈ kFourSpanningTreeList,
      (leadingTwoBlock (directionChartGap kFourDirection traceRefuterPoint.mass
        traceRefuterPoint.weight tree)).PosDef
        ∧ 0 < kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass
            traceRefuterPoint.weight tree) := by
  refine ⟨{0, 1, 3}, by decide, ?_, ?_⟩
  · exact leadingTwoBlock_posDef_of_posDef
      (directionChartGap_transpose kFourDirection traceRefuterPoint.mass
        traceRefuterPoint.weight _)
      traceRefuterPoint_posDef_zeroOneThree
  · exact traceRefuterPoint_massTreeSum_pos_count.1

/-! ## 8b. The designated edge does NOT host a dominating tree

Section 5 designates one edge for the FIRST raw sign.  The obvious next reading
is that the same edge hosts a strictly dominating tree.  That reading is FALSE,
and this section kills it with an exact rational witness.  A floating-point
census of 200000 random chart points found the reading alive at 199999 of them,
which is the exact profile the campaign warns about.

At the masses `(1, 4, 1, 100, 6, 189)` and the weights
`(1, 3, 14, 53, 25, 144) / 240` the six trace boosts are
`480`, `640`, `240/7`, `24000/53`, `288/5` and `315`, so edge `1` is the unique
maximum.  All eight listed trees through edge `1` carry a strictly negative
signed tree sum.  The chart obligation stays INTACT there: the star `{3, 4, 5}`
dominates strictly.

The trace floor `Gtz.kFourTraceSum_pos_of_maximalBoost` is untouched.  It claims
the first raw sign and nothing else, and every one of those eight trees does
carry a strictly positive first sign. -/

/-- Masses of the point that refutes the designated-edge hosting reading. -/
noncomputable def kFourBoostRefuterMass : Fin 6 → ℝ
  | 0 => 1
  | 1 => 4
  | 2 => 1
  | 3 => 100
  | 4 => 6
  | 5 => 189

/-- Weights of the point that refutes the designated-edge hosting reading. -/
noncomputable def kFourBoostRefuterWeight : Fin 6 → ℝ
  | 0 => 1 / 240
  | 1 => 1 / 80
  | 2 => 7 / 120
  | 3 => 53 / 240
  | 4 => 5 / 48
  | 5 => 3 / 5

/-- The refuter is a genuine chart point. -/
noncomputable def kFourBoostRefuterPoint : DirectionChartPoint 6 where
  mass := kFourBoostRefuterMass
  weight := kFourBoostRefuterWeight
  mass_pos := by intro label; fin_cases label <;> norm_num [kFourBoostRefuterMass]
  weight_pos := by intro label; fin_cases label <;> norm_num [kFourBoostRefuterWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [kFourBoostRefuterWeight]

/-- **EDGE ONE IS THE MAXIMAL TRACE BOOST AT THE REFUTER.** -/
theorem kFourBoostRefuterPoint_boost_maximal (label : Fin 6) :
    kFourTraceBoost kFourBoostRefuterPoint.mass kFourBoostRefuterPoint.weight label
      ≤ kFourTraceBoost kFourBoostRefuterPoint.mass kFourBoostRefuterPoint.weight 1 := by
  rcases fin_six_cases label with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [kFourTraceBoost, kFourTraceAtomWeight_zero, kFourTraceAtomWeight_one,
      kFourTraceAtomWeight_two, kFourTraceAtomWeight_three, kFourTraceAtomWeight_four,
      kFourTraceAtomWeight_five, kFourBoostRefuterPoint, kFourBoostRefuterMass,
      kFourBoostRefuterWeight]

/-- **EVERY LISTED TREE THROUGH THE DESIGNATED EDGE FAILS ON THE DETERMINANT.**
All eight of them carry a strictly negative signed tree sum. -/
theorem kFourBoostRefuterPoint_massTreeSum_neg (tree : Finset (Fin 6))
    (hmem : tree ∈ kFourSpanningTreeList) (hstar : (1 : Fin 6) ∈ tree) :
    kFourMassTreeSum (signedGapWeight kFourBoostRefuterPoint.mass
      kFourBoostRefuterPoint.weight tree) < 0 := by
  simp only [kFourSpanningTreeList, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact absurd hstar (by decide)
      | norm_num [kFourMassTreeSum, signedGapWeight, kFourBoostRefuterPoint,
          kFourBoostRefuterMass, kFourBoostRefuterWeight, Finset.mem_insert,
          Finset.mem_singleton, Fin.ext_iff]

/-- **THE CHART OBLIGATION IS INTACT AT THE REFUTER.**  The canonical gauge star
dominates strictly, so the refutation is about the DESIGNATION and never about
the chart. -/
theorem kFourBoostRefuterPoint_posDef_threeFourFive :
    (directionChartGap kFourDirection kFourBoostRefuterPoint.mass
      kFourBoostRefuterPoint.weight ({3, 4, 5} : Finset (Fin 6))).PosDef := by
  refine (posDef_directionChartGap_iff_rawTriple kFourBoostRefuterPoint
    ({3, 4, 5} : Finset (Fin 6))).mpr ⟨?_, ?_, ?_⟩
  · norm_num [kFourTraceSum, signedGapWeight, kFourBoostRefuterPoint,
      kFourBoostRefuterMass, kFourBoostRefuterWeight, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
  · norm_num [kFourSecondForestSum_eq, signedGapWeight, kFourBoostRefuterPoint,
      kFourBoostRefuterMass, kFourBoostRefuterWeight, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
  · norm_num [kFourMassTreeSum, signedGapWeight, kFourBoostRefuterPoint,
      kFourBoostRefuterMass, kFourBoostRefuterWeight, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]

/-- **THE DESIGNATED-EDGE HOSTING READING.**  An edge of maximal trace boost
lies in a strictly dominating listed tree. -/
def KFourMaxTraceBoostEdgeHostsStrictTree : Prop :=
  ∀ (point : DirectionChartPoint 6) (star : Fin 6),
    (∀ label, kFourTraceBoost point.mass point.weight label
      ≤ kFourTraceBoost point.mass point.weight star) →
    ∃ tree ∈ kFourSpanningTreeList, star ∈ tree
      ∧ (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- **THE DESIGNATED-EDGE HOSTING READING IS FALSE.**  Do not reopen it. -/
theorem not_kFourMaxTraceBoostEdgeHostsStrictTree :
    ¬ KFourMaxTraceBoostEdgeHostsStrictTree := by
  intro hrule
  obtain ⟨tree, hmem, hstar, hposDef⟩ := hrule kFourBoostRefuterPoint 1
    kFourBoostRefuterPoint_boost_maximal
  have htriple := (posDef_directionChartGap_iff_rawTriple kFourBoostRefuterPoint tree).mp
    hposDef
  exact absurd htriple.2.2
    (not_lt.mpr (kFourBoostRefuterPoint_massTreeSum_neg tree hmem hstar).le)

/-- **THE FIRST SIGN IS STILL PAID AT THE REFUTER.**  Every listed tree through
the designated edge carries a strictly positive first raw sign, so the landed
trace floor and the refutation above agree. -/
theorem kFourBoostRefuterPoint_traceSum_pos (tree : Finset (Fin 6))
    (hmem : tree ∈ kFourSpanningTreeList) (hstar : (1 : Fin 6) ∈ tree) :
    0 < kFourTraceSum (signedGapWeight kFourBoostRefuterPoint.mass
      kFourBoostRefuterPoint.weight tree) :=
  kFourTraceSum_pos_of_maximalBoost kFourBoostRefuterPoint tree
    (by rw [card_eq_three_of_mem_kFourSpanningTreeList' hmem]; norm_num) 1 hstar
    kFourBoostRefuterPoint_boost_maximal

/-! ## 9. The raw residual, and the registered consumers -/

/-- **THE RAW RESIDUAL.**  At every chart point some listed tree makes the three
raw signs positive.  This proposition IS equivalent to
`Gtz.KFourUniversalStrictTree`, and the next theorem says so.  Its value is the
SHAPE: one linear, one quadratic and one cubic form of ONE vector. -/
def KFourRawTripleTotal : Prop :=
  ∀ point : DirectionChartPoint 6, ∃ tree ∈ kFourSpanningTreeList,
    0 < kFourTraceSum (signedGapWeight point.mass point.weight tree)
      ∧ 0 < kFourSecondForestSum (signedGapWeight point.mass point.weight tree)
      ∧ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)

/-- **THE RAW RESIDUAL IS AN EQUIVALENCE, AND THIS THEOREM SAYS SO.** -/
theorem kFourUniversalStrictTree_iff_rawTripleTotal :
    KFourUniversalStrictTree ↔ KFourRawTripleTotal := by
  constructor
  · intro hstrict point
    obtain ⟨tree, hmem, hposDef⟩ := hstrict point
    exact ⟨tree, hmem, (posDef_directionChartGap_iff_rawTriple point tree).mp hposDef⟩
  · intro htotal point
    obtain ⟨tree, hmem, htriple⟩ := htotal point
    exact ⟨tree, hmem, (posDef_directionChartGap_iff_rawTriple point tree).mpr htriple⟩

/-- The raw residual closes the registered `A3` proposition, the registered
chart obligation, the design-side family selection and the unrefined knife
band. -/
theorem kFourRawTripleTotal_closes_all (htotal : KFourRawTripleTotal) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict
      ∧ DirectionChartIsTieFree kFourDirection
      ∧ KFourFamilySelection
      ∧ KFourKnifeBandRefinedWeakToStrict :=
  kFourStrictTree_closes_all (kFourUniversalStrictTree_iff_rawTripleTotal.mpr htotal)

/-- **THE RESIDUAL AFTER THE TRACE FLOOR, IN RAW FORM.**  Section 5 proves the
first sign satisfiable at every chart point with no hypothesis, and at every
tree through one designated edge.  What remains is the second and third signs
on that admitted set. -/
def KFourRawSecondAndDetTotal : Prop :=
  ∀ point : DirectionChartPoint 6, ∃ star : Fin 6,
    (∀ label, kFourTraceBoost point.mass point.weight label
        ≤ kFourTraceBoost point.mass point.weight star)
      ∧ ∃ tree ∈ kFourSpanningTreeList, star ∈ tree
        ∧ 0 < kFourSecondForestSum (signedGapWeight point.mass point.weight tree)
        ∧ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)

/-- **THE TRACE FLOOR PAYS THE FIRST SIGN.**  The residual of section 5 gives the
raw residual, because the designated edge carries the first sign for free.  The
implication runs one way only: the residual demands a tree through the
designated edge and the raw residual accepts any listed tree. -/
theorem kFourRawTripleTotal_of_rawSecondAndDetTotal
    (htotal : KFourRawSecondAndDetTotal) : KFourRawTripleTotal := by
  intro point
  obtain ⟨star, hmax, tree, hmem, hstar, hsecond, hdet⟩ := htotal point
  have hcard : 2 ≤ tree.card := by
    have hthree := card_eq_three_of_mem_kFourSpanningTreeList' hmem
    omega
  exact ⟨tree, hmem,
    kFourTraceSum_pos_of_maximalBoost point tree hcard star hstar hmax, hsecond, hdet⟩

/-- The residual of section 5 closes all four registered consumers. -/
theorem kFourRawSecondAndDetTotal_closes_all (htotal : KFourRawSecondAndDetTotal) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict
      ∧ DirectionChartIsTieFree kFourDirection
      ∧ KFourFamilySelection
      ∧ KFourKnifeBandRefinedWeakToStrict :=
  kFourRawTripleTotal_closes_all (kFourRawTripleTotal_of_rawSecondAndDetTotal htotal)

end Gtz
