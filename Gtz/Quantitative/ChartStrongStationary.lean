/-
# The CHART stationarity system, quantified over EVERY tight selection

The strict refinement of `Gtz.Quantitative.ChartStationary`.  That file bundles the
first-order data of the chart objective

    G(P, t) = max_{|C| = rank} lambda_min(W[C]),   W = P - diag t,

with ONE tight direction named per active index.  This file replaces that single
named direction by a UNIVERSAL quantifier: the multiplier condition is required for
EVERY selection of unit tight directions, one from each active block.

**Where the analysis lives is the whole point, exactly as in the two siblings.**  The
nonsmooth first-order theory that would PRODUCE the system — Clarke subdifferentials,
the eigenvalue superdifferential, Danskin's theorem, the Grassmannian retraction, the
identification of the active set — stays OUTSIDE Lean, as a stated hypothesis.  What is
inside Lean is the pure linear algebra the hypothesis implies, plus one application of
the shipped Gordan alternative.  No derivative, no limit, no manifold, no
subdifferential appears anywhere below.

## Why the quantifier moves

`IsChartStationaryData` fixes one tight direction per active index and asks the
assembled multiplier to satisfy the two stationarity equations.  That is the exact
first-order condition when the tight eigenvalue is SIMPLE, and it is strictly weaker
when it is not: the true condition takes the inner minimum PER DIRECTION, so it must
hold for every choice of tight direction, not for one convenient choice.  The gap is
not academic — it is exactly the multiplicity stratum, and it is where the old system
is vacuous under symmetry, because symmetrising a feasible multiplier produces ONE
feasible point and therefore discharges an existential but never a universal.

Two consequences are proved here rather than asserted:

* `isChartStrongStationaryData_iff_of_simpleTightBlocks` — at simple multiplicity the
  two systems COINCIDE.  So this is a refinement of the shipped system, not a parallel
  development, and the whole of its added power sits on the multiplicity stratum.
* `exists_multiplier_isChartStationaryData_of_isChartStrongStationaryData` — the strong
  datum implies the weak one at every selection, so every consequence proved in
  `Gtz.Quantitative.ChartStationary` — the coverage law, the forced diagonal, the weight
  floor, the one-sided value bound — transfers verbatim.  Two are re-exported below as
  worked examples.

## The data

`IsChartStrongStationaryData rank projection weight value activeSet activeSubset` carries
the chart point and the active family exactly as the weak bundle does, and then TWO
fields in place of the weak bundle's multipliers and two stationarity equations:

* `exists_tightDir` — every active block genuinely HAS a unit tight direction.  Without
  it the universal field below is vacuously true and the bundle would be empty of
  content, which is a defect this repository has been bitten by before;
* `hasBalancedMultiplier_of_isChartTightSelection` — for EVERY selection of unit tight
  directions there exist nonnegative multipliers summing to one whose induced tangent
  functional VANISHES on the whole tangent space.  That is "zero lies in the convex hull
  of the induced linear functionals", written elementarily: no convex hull, no topology,
  no dual space.

The multipliers are therefore NOT a field.  They are produced per selection, which is
what makes the condition universal rather than existential.

## The tangent space is a DEFINITION here

`IsChartTangent` is the tangent space of the constraint manifold
Grassmannian x open simplex, written down directly: a symmetric direction matrix whose
range-block `P Pdot P` and kernel-block `(1 - P) Pdot (1 - P)` both vanish, together
with a sum-zero weight direction.  That IS the derivative of `P^2 = P`, `Pᵀ = P` and
`sum t = 1`, but nothing here proves that — no manifold, no chart, no derivative is
formalised, and the identification is the reader's, not the kernel's.

Nothing is lost by the parametrisation used for the Gordan step:
`chartOffBlockDirection_eq_self_of_isChartTangent` and
`chartCenteredWeight_eq_self_of_sum_eq_zero` prove that
`(param, s) ↦ (P param (1-P) + (1-P) paramᵀ P, s - mean s)` is ONTO the tangent space, so
the descent direction the alternative returns ranges over all of it.

The gap map `(P, t) ↦ P - diag t` is AFFINE, so its differential is itself; that is why
`chartTangentSlope` is the same `chartStationaryGap` applied to the direction rather
than to the point, and why no separate derivative object appears.

## PROVED here (unconditional, given that data)

* `isChartBalancedMultiplier_iff` — **THE ALGEBRAIC EQUIVALENCE.**  A multiplier vector
  is balanced against a selection exactly when its assembly `Xi` has constant diagonal
  `1/size` and commutes with the chart.  Vanishing against the sum-zero weight
  directions gives the diagonal; vanishing against the off-block directions gives the
  commutation, through `2 tr((1-P) Xi P N) = 0` at `N = (P Xi (1-P))`.  Pure linear
  algebra: no analysis, no convexity, and no Gordan.  This is the identity that makes
  the two systems comparable at all.
* `exists_multiplier_isChartStationaryData_of_isChartStrongStationaryData` — **the
  refinement**, at any named selection, with
  `exists_isChartStationaryData_of_isChartStrongStationaryData` the form that supplies its
  own selection.
* `exists_isChartTangent_forall_chartTangentSlope_neg` — **THE DESCENT LEMMA.**  If some
  tight selection admits NO balanced multiplier then there is a tangent direction along
  which EVERY active block's tight Rayleigh quotient strictly decreases.  This is the
  Gordan alternative of `Gtz.LinAlg.GordanAlternative`, applied to the Riesz vectors of
  the tangent functionals; `gordan_alternative_finsetFamily` is a REINDEXING of the
  shipped theorem, not a second proof of it.
* `not_hasBalancedMultiplier_of_forall_chartTangentSlope_neg` and
  `hasBalancedMultiplier_iff_not_exists_descent` — **THE CONVERSE**, so balance is EXACTLY
  the absence of a first-order descent direction.  The criterion is sharp at first order,
  and it says nothing at any order beyond it.
* `isChartStrongStationaryData_of_isChartStationaryData_of_simpleTightBlocks` and its
  `iff` — **THE REDUCTION.**
* `sum_multiplier_sq_eq_inv_size_of_isChartBalancedMultiplier` — the WEIGHT-SLICE
  reading: the barycentre of the squared-overlap vectors `(v_{C,c}^2)_c` is the uniform
  vector `1/size`.  This is the sub-family of directions where the cheap exclusion lives;
  the exclusion itself is not developed here.

## MECHANIZED WITNESS — the bundle is inhabited

`chartTetraProjection_isChartStrongStationaryData` — the `(4,3)` TETRAHEDRON at
`value = 0`.  Its four active blocks all have SIMPLE tight eigenvalue (proved:
`chartTetraTight_eq_smul_chartTetraTightDir` solves the three-term recurrence
`3 u_c = sum u` on each triple), so the reduction applies to the shipped weak datum
`Gtz.chartTetraProjection_isChartStationaryData` and returns a strong one.  Every
theorem below is therefore a statement about a non-empty class.

## HONESTY — five statements, each with what forces it

**(a) The variational derivation is not formalised.**  Every theorem takes the datum as
a HYPOTHESIS in its statement, never as something derived; the conditionality is in the
types, not only in this prose.  Turning the descent lemma's tangent direction into an
actual decrease of `G` needs THREE further ingredients, none of them here: a curve on
the Grassmannian realising the direction, the continuity of the inactive blocks' least
eigenvalue, and the identification of the active family with the argmax family.  The
second and third are what `IsChartInactiveStrict` and `Gtz.IsChartArgmaxValue` name; the
first is not named at all, because the repository carries no manifold.

**(b) The system inherits the DISJUNCTIVE admissibility weakness, undiminished.**  Like
the weak bundle it fixes an active family and cannot see that the family is not the
argmax.  `Gtz.IsChartArgmaxValue` is not a field here either, and nothing below consumes
it.  A datum at a value that no subset actually attains is still a datum.

**(c) It contains NO realness ingredient and closes no cell.**  At the three complex
counterexamples anyone has exhibited — the `(4,2)` SIC, the `(6,3)` trine, the `(9,3)`
Hesse configuration — every active tight eigenvalue is SIMPLE [EXACT, outside Lean, not
mechanized], so by the reduction the strong system holds there exactly when the weak one
does, which it does.  A necessary condition MUST accept genuine minima, so this is
correct behaviour and not a defect; what it means is that the strengthening cannot
separate the fields and must not be advertised as a route to `(6,3)` or `(7,3)`.

**(d) Where the strengthening does bite, measured.**  On a 246-point sample of the
`(6,3)` symmetric locus the strong system excludes 246 and the weak system 0.  The
octahedron of `Gtz.chartOctaProjection_isChartStationaryData` is the cleanest instance:
its rainbow blocks are `(1/3) I_3`, so every unit vector supported on one is tight and
the tight multiplicity is THREE, and it is one of four exactly-certified admissible
non-minima that the strong system rejects and the weak one accepts.  At `(7,3)` the
strengthening bites nowhere: the whole
symmetric locus there is a SINGLE chart point, all of whose blocks are simple and at
which the weak system already holds with the barycentric multiplier and no free
parameter [EXACT and measured, outside Lean, not mechanized].  So the symmetric-locus
hole is closed at the easier open cell and not at the harder one.

**(e) The counting law is deliberately absent.**  A solid-angle count over the cones
`{d : Q_C^T Wdot[C](d) Q_C ⪰ 0}` would give multiplicity-profile exclusions, and its
load-bearing step — that the normalised angle depends only on the tight multiplicity —
is refuted [measured, outside Lean].  No angle, no measure and no multiplicity-profile
statement appears in this file, and none may be added to it.

## NOT here, deliberately

* No eigenvalue function.  `Gtz.lambdaMinMat` is indexed by `Fin dim` and would force a
  submatrix reindexing at every statement; everything below is phrased through ambient
  Rayleigh quotients and `Matrix.PosSemidef`, matching `Gtz.Quantitative.CriticalQuadric`
  and `Gtz.Quantitative.ChartStationary`, which are the shipped vocabularies for exactly
  this job.  Tightness is `W[C] u = value u` read coordinatewise ON the subset, and
  multiplicity is a spanning statement about tight vectors, never a rank.
* No reproof of the Gordan alternative.  `Gtz.gordan_alternative_dotProduct` is imported;
  `gordan_alternative_finsetFamily` only moves it from `Fin n`-indexed families and
  `Fin k`-indexed coordinates to a `Finset`-indexed family over an arbitrary finite
  coordinate type, which is what the sum type `Fin size x Fin size ⊕ Fin size` needs.
* No new gap, chart or assembly definition.  `Gtz.chartStationaryGap` and
  `Gtz.chartMultiplierAssembly` are imported and reused, so the two systems are literally
  talking about the same matrices.
-/
import Mathlib
import Gtz.LinAlg.GordanAlternative
import Gtz.Quantitative.ChartStationary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}

/-! ## The Gordan alternative, reindexed

One wrapper, two reindexings, no new content.  `Gtz.gordan_alternative_dotProduct` takes
a `Fin n`-indexed family of `Fin k`-indexed vectors; the descent lemma below has a family
indexed by a `Finset` of an arbitrary type and coordinates indexed by
`Fin size x Fin size ⊕ Fin size`.  Both gaps are closed by `Fintype.equivFin`. -/

/-- **The Gordan alternative over a `Finset`-indexed family with an arbitrary finite
coordinate type**: either zero is a convex combination of the family, or some probe has
strictly negative overlap with every member.

A REINDEXING of `Gtz.gordan_alternative_dotProduct`, not a second proof of it — the
separation itself is imported and never re-derived. -/
theorem gordan_alternative_finsetFamily {coordIndex : Type*} [Fintype coordIndex]
    (activeSet : Finset activeIndex) (family : activeIndex → (coordIndex → ℝ)) :
    (∃ multiplier : activeIndex → ℝ, (∀ activeLabel ∈ activeSet, 0 ≤ multiplier activeLabel)
        ∧ (∑ activeLabel ∈ activeSet, multiplier activeLabel = 1)
        ∧ ∀ coord : coordIndex,
            ∑ activeLabel ∈ activeSet, multiplier activeLabel * family activeLabel coord = 0)
      ∨ ∃ probe : coordIndex → ℝ,
          ∀ activeLabel ∈ activeSet,
            ∑ coord : coordIndex, family activeLabel coord * probe coord < 0 := by
  classical
  let labelEquiv := Fintype.equivFin { chosen // chosen ∈ activeSet }
  let coordEquiv := Fintype.equivFin coordIndex
  rcases gordan_alternative_dotProduct
      (fun flatLabel flatCoord =>
        family ((labelEquiv.symm flatLabel) : activeIndex) (coordEquiv.symm flatCoord)) with
    ⟨flatCoeff, hflatNonneg, hflatSum, hflatCombination⟩ | ⟨flatProbe, hflatNeg⟩
  · left
    refine ⟨fun activeLabel =>
      if hmem : activeLabel ∈ activeSet then flatCoeff (labelEquiv ⟨activeLabel, hmem⟩) else 0,
      fun activeLabel hmem => by
        show (0 : ℝ) ≤ if hmem : activeLabel ∈ activeSet
          then flatCoeff (labelEquiv ⟨activeLabel, hmem⟩) else 0
        rw [dif_pos hmem]
        exact hflatNonneg _, ?_, ?_⟩
    · rw [← Finset.sum_coe_sort activeSet]
      calc ∑ chosen : { chosen // chosen ∈ activeSet },
              (if hmem : chosen.val ∈ activeSet then flatCoeff (labelEquiv ⟨chosen.val, hmem⟩)
                else 0)
            = ∑ chosen : { chosen // chosen ∈ activeSet }, flatCoeff (labelEquiv chosen) :=
              Finset.sum_congr rfl fun chosen _ => by rw [dif_pos chosen.property]
        _ = ∑ flatLabel, flatCoeff flatLabel := Equiv.sum_comp labelEquiv flatCoeff
        _ = 1 := hflatSum
    · intro coord
      have hcoordinate := congrFun hflatCombination (coordEquiv coord)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Equiv.symm_apply_apply] at hcoordinate
      rw [← Finset.sum_coe_sort activeSet]
      calc ∑ chosen : { chosen // chosen ∈ activeSet },
              (if hmem : chosen.val ∈ activeSet then flatCoeff (labelEquiv ⟨chosen.val, hmem⟩)
                else 0) * family chosen.val coord
            = ∑ chosen : { chosen // chosen ∈ activeSet },
                flatCoeff (labelEquiv chosen) * family ((labelEquiv.symm (labelEquiv chosen) :
                  { chosen // chosen ∈ activeSet }) : activeIndex) coord :=
              Finset.sum_congr rfl fun chosen _ => by
                rw [dif_pos chosen.property, Equiv.symm_apply_apply]
        _ = ∑ flatLabel, flatCoeff flatLabel
              * family ((labelEquiv.symm flatLabel) : activeIndex) coord :=
            Equiv.sum_comp labelEquiv
              (fun flatLabel => flatCoeff flatLabel
                * family ((labelEquiv.symm flatLabel) : activeIndex) coord)
        _ = 0 := hcoordinate
  · right
    refine ⟨fun coord => flatProbe (coordEquiv coord), fun activeLabel hmem => ?_⟩
    have hnegative := hflatNeg (labelEquiv ⟨activeLabel, hmem⟩)
    simp only [dotProduct, Equiv.symm_apply_apply] at hnegative
    calc ∑ coord : coordIndex, family activeLabel coord * flatProbe (coordEquiv coord)
        = ∑ flatCoord, family activeLabel (coordEquiv.symm flatCoord)
            * flatProbe (coordEquiv (coordEquiv.symm flatCoord)) :=
          (Equiv.sum_comp coordEquiv.symm
            (fun coord => family activeLabel coord * flatProbe (coordEquiv coord))).symm
      _ = ∑ flatCoord, family activeLabel (coordEquiv.symm flatCoord) * flatProbe flatCoord :=
          Finset.sum_congr rfl fun flatCoord _ => by rw [Equiv.apply_symm_apply]
      _ < 0 := hnegative

/-! ## The tangent directions of the chart -/

/-- **A tangent direction of the constraint manifold**, written down directly.

`directionMatrix` is the derivative of the projection and `directionWeight` of the
weights.  Differentiating `Pᵀ = P` gives symmetry; differentiating `P P = P` gives
`Pdot = Pdot P + P Pdot`, which is equivalent to the vanishing of both diagonal blocks;
differentiating `sum t = 1` gives the sum-zero condition.  None of that is proved here —
this is a DEFINITION, and the identification with a manifold tangent space is the
reader's. -/
structure IsChartTangent (projection directionMatrix : Matrix (Fin size) (Fin size) ℝ)
    (directionWeight : Fin size → ℝ) : Prop where
  /-- The direction matrix is symmetric. -/
  isSymmetric : directionMatrixᵀ = directionMatrix
  /-- The range block vanishes: the direction moves the range, it does not rotate it. -/
  rangeBlock_eq_zero : projection * directionMatrix * projection = 0
  /-- The kernel block vanishes, for the same reason on the complement. -/
  kernelBlock_eq_zero :
    (1 - projection) * directionMatrix * (1 - projection) = 0
  /-- The weight direction is tangent to the simplex. -/
  weight_sum_zero : ∑ atomIndex : Fin size, directionWeight atomIndex = 0

/-- The OFF-BLOCK direction built from an arbitrary matrix parameter: the symmetric part
of `P param (1 - P)`.  Every Grassmannian tangent direction has this shape, and
`chartOffBlockDirection_eq_self_of_isChartTangent` proves the parametrisation is onto. -/
def chartOffBlockDirection (projection param : Matrix (Fin size) (Fin size) ℝ) :
    Matrix (Fin size) (Fin size) ℝ :=
  projection * param * (1 - projection) + (1 - projection) * paramᵀ * projection

/-- The simplex-tangent weight direction built from an arbitrary weight parameter, by
subtracting its mean.  Onto the sum-zero vectors by
`chartCenteredWeight_eq_self_of_sum_eq_zero`. -/
noncomputable def chartCenteredWeight (rawWeight : Fin size → ℝ) : Fin size → ℝ :=
  fun atomIndex =>
    rawWeight atomIndex - (∑ otherIndex : Fin size, rawWeight otherIndex) / (size : ℝ)

theorem sum_chartCenteredWeight_eq_zero (rawWeight : Fin size → ℝ) :
    ∑ atomIndex : Fin size, chartCenteredWeight rawWeight atomIndex = 0 := by
  rcases Nat.eq_zero_or_pos size with hzero | hpositive
  · subst hzero
    simp
  · have hsizeNe : ((size : ℝ)) ≠ 0 := by
      have : (0 : ℝ) < (size : ℝ) := by exact_mod_cast hpositive
      exact ne_of_gt this
    simp only [chartCenteredWeight]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    ring

/-- **The difference of two atoms is a tangent direction** — with no motion of the
chart.  This is the sub-family that forces the assembly's diagonal. -/
theorem isChartTangent_weightDifference (projection : Matrix (Fin size) (Fin size) ℝ)
    (firstIndex secondIndex : Fin size) :
    IsChartTangent projection 0
      (fun atomIndex => (if atomIndex = firstIndex then (1 : ℝ) else 0)
        - (if atomIndex = secondIndex then (1 : ℝ) else 0)) where
  isSymmetric := Matrix.transpose_zero
  rangeBlock_eq_zero := by rw [Matrix.mul_zero, Matrix.zero_mul]
  kernelBlock_eq_zero := by rw [Matrix.mul_zero, Matrix.zero_mul]
  weight_sum_zero := by rw [Finset.sum_sub_distrib]; simp

/-- **The off-block direction is a tangent direction** — with no motion of the weights.
This is the sub-family that forces the commutation. -/
theorem isChartTangent_chartOffBlockDirection
    {projection : Matrix (Fin size) (Fin size) ℝ} (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection)
    (param : Matrix (Fin size) (Fin size) ℝ) :
    IsChartTangent projection (chartOffBlockDirection projection param) 0 := by
  have hcomplementSymmetric :
      (1 - projection : Matrix (Fin size) (Fin size) ℝ)ᵀ = 1 - projection := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsymmetric]
  have hrightAnnihilate :
      projection * (1 - projection : Matrix (Fin size) (Fin size) ℝ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hidempotent, sub_self]
  have hleftAnnihilate :
      (1 - projection : Matrix (Fin size) (Fin size) ℝ) * projection = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hidempotent, sub_self]
  refine ⟨?_, ?_, ?_, by simp⟩
  · rw [chartOffBlockDirection, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsymmetric,
      hcomplementSymmetric]
    simp only [Matrix.mul_assoc]
    exact add_comm _ _
  · rw [chartOffBlockDirection, Matrix.mul_add, Matrix.add_mul]
    have hrangeFirst : projection * (projection * param * (1 - projection)) * projection = 0 := by
      calc projection * (projection * param * (1 - projection)) * projection
          = projection * projection * param * ((1 - projection) * projection) := by
            simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hleftAnnihilate, Matrix.mul_zero]
    have hrangeSecond :
        projection * ((1 - projection) * paramᵀ * projection) * projection = 0 := by
      calc projection * ((1 - projection) * paramᵀ * projection) * projection
          = projection * (1 - projection) * (paramᵀ * (projection * projection)) := by
            simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hrightAnnihilate, Matrix.zero_mul]
    rw [hrangeFirst, hrangeSecond, add_zero]
  · rw [chartOffBlockDirection, Matrix.mul_add, Matrix.add_mul]
    have hkernelFirst :
        (1 - projection) * (projection * param * (1 - projection)) * (1 - projection) = 0 := by
      calc (1 - projection) * (projection * param * (1 - projection)) * (1 - projection)
          = (1 - projection) * projection * (param * ((1 - projection) * (1 - projection))) := by
            simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hleftAnnihilate, Matrix.zero_mul]
    have hkernelSecond :
        (1 - projection) * ((1 - projection) * paramᵀ * projection) * (1 - projection) = 0 := by
      calc (1 - projection) * ((1 - projection) * paramᵀ * projection) * (1 - projection)
          = (1 - projection) * (1 - projection) * paramᵀ * (projection * (1 - projection)) := by
            simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hrightAnnihilate, Matrix.mul_zero]
    rw [hkernelFirst, hkernelSecond, add_zero]

/-- **The off-block parametrisation is ONTO the Grassmannian tangent directions**: a
tangent direction is its own off-block image.  So the Gordan step below, which searches
only over parametrised directions, searches over the whole tangent space. -/
theorem chartOffBlockDirection_eq_self_of_isChartTangent
    {projection directionMatrix : Matrix (Fin size) (Fin size) ℝ}
    {directionWeight : Fin size → ℝ}
    (htangent : IsChartTangent projection directionMatrix directionWeight) :
    chartOffBlockDirection projection directionMatrix = directionMatrix := by
  have hsplit : directionMatrix
      = projection * directionMatrix * projection
        + projection * directionMatrix * (1 - projection)
        + (1 - projection) * directionMatrix * projection
        + (1 - projection) * directionMatrix * (1 - projection) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [chartOffBlockDirection, htangent.isSymmetric]
  conv_rhs => rw [hsplit, htangent.rangeBlock_eq_zero, htangent.kernelBlock_eq_zero]
  abel

/-- **The centred parametrisation is ONTO the simplex-tangent weight directions.** -/
theorem chartCenteredWeight_eq_self_of_sum_eq_zero {rawWeight : Fin size → ℝ}
    (hsum : ∑ atomIndex : Fin size, rawWeight atomIndex = 0) :
    chartCenteredWeight rawWeight = rawWeight := by
  funext atomIndex
  rw [chartCenteredWeight, hsum, zero_div, sub_zero]

/-! ## The tangent slope of a tight direction

The gap map `(P, t) ↦ P - diag t` is AFFINE, so its differential at any point is itself.
That is why the slope of a tight direction along a chart direction is the SAME
`Gtz.chartStationaryGap`, evaluated at the direction rather than at the point. -/

/-- **The first-order slope of a tight direction along a chart direction**:
`v ⟨Wdot v⟩` with `Wdot = directionMatrix - diag directionWeight`. -/
def chartTangentSlope (tightVec : Fin size → ℝ)
    (directionMatrix : Matrix (Fin size) (Fin size) ℝ) (directionWeight : Fin size → ℝ) : ℝ :=
  tightVec ⬝ᵥ (chartStationaryGap directionMatrix directionWeight *ᵥ tightVec)

theorem chartTangentSlope_eq_sub (tightVec : Fin size → ℝ)
    (directionMatrix : Matrix (Fin size) (Fin size) ℝ) (directionWeight : Fin size → ℝ) :
    chartTangentSlope tightVec directionMatrix directionWeight
      = tightVec ⬝ᵥ (directionMatrix *ᵥ tightVec)
        - ∑ atomIndex : Fin size, directionWeight atomIndex * tightVec atomIndex ^ 2 := by
  rw [chartTangentSlope, chartStationaryGap, Matrix.sub_mulVec, dotProduct_sub]
  congr 1
  simp only [Matrix.mulVec_diagonal, dotProduct]
  exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-- **The slope is QUADRATIC in the tight direction.**  This is why a one-dimensional
tight eigenspace makes the universal condition collapse to the single named one: the two
unit vectors of a line differ by a sign, and the sign is invisible here. -/
theorem chartTangentSlope_smul (scale : ℝ) (tightVec : Fin size → ℝ)
    (directionMatrix : Matrix (Fin size) (Fin size) ℝ) (directionWeight : Fin size → ℝ) :
    chartTangentSlope (scale • tightVec) directionMatrix directionWeight
      = scale ^ 2 * chartTangentSlope tightVec directionMatrix directionWeight := by
  rw [chartTangentSlope, chartTangentSlope, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul]
  ring

/-! ## The assembled multiplier, without the bundle

Three facts about `Gtz.chartMultiplierAssembly` that the shipped file proves only for a
full `Gtz.IsChartStationaryData`.  Here they are proved from the hypotheses they actually
need, which is what the universal system can supply. -/

/-- **A symmetric matrix reads a rank-one trace as a Rayleigh quotient.** -/
theorem trace_atomMatrix_mul_of_symmetric (tightVec : Fin size → ℝ)
    {directionMatrix : Matrix (Fin size) (Fin size) ℝ}
    (hsymmetric : directionMatrixᵀ = directionMatrix) :
    Matrix.trace (atomMatrix tightVec * directionMatrix)
      = tightVec ⬝ᵥ (directionMatrix *ᵥ tightVec) := by
  have hentry : ∀ rowIndex colIndex : Fin size,
      directionMatrix rowIndex colIndex = directionMatrix colIndex rowIndex := by
    intro rowIndex colIndex
    conv_lhs => rw [← hsymmetric]
    rfl
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun rowIndex _ => Finset.sum_congr rfl fun colIndex _ => ?_
  rw [hentry colIndex rowIndex]
  ring

/-- The assembly is symmetric — unconditionally, with no bundle in sight. -/
theorem transpose_chartMultiplierAssembly (activeSet : Finset activeIndex)
    (multiplier : activeIndex → ℝ) (selection : activeIndex → (Fin size → ℝ)) :
    (chartMultiplierAssembly activeSet multiplier selection)ᵀ
      = chartMultiplierAssembly activeSet multiplier selection := by
  rw [chartMultiplierAssembly, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun activeLabel _ => ?_
  rw [Matrix.transpose_smul, atomMatrix, Matrix.transpose_vecMulVec]

/-- The assembly's trace is the multiplier mass weighted by the squared lengths. -/
theorem trace_chartMultiplierAssembly_eq_sum (activeSet : Finset activeIndex)
    (multiplier : activeIndex → ℝ) (selection : activeIndex → (Fin size → ℝ)) :
    Matrix.trace (chartMultiplierAssembly activeSet multiplier selection)
      = ∑ activeLabel ∈ activeSet,
          multiplier activeLabel * (selection activeLabel ⬝ᵥ selection activeLabel) := by
  rw [chartMultiplierAssembly, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun activeLabel _ => ?_
  rw [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul]
  simp only [leverageOf]
  rw [← dotProduct_self_eq_sum_sq]

/-- The assembly's trace is one, from unit directions and normalised multipliers. -/
theorem trace_chartMultiplierAssembly_eq_one {activeSet : Finset activeIndex}
    {multiplier : activeIndex → ℝ} {selection : activeIndex → (Fin size → ℝ)}
    (hunit : ∀ activeLabel ∈ activeSet, selection activeLabel ⬝ᵥ selection activeLabel = 1)
    (hmass : ∑ activeLabel ∈ activeSet, multiplier activeLabel = 1) :
    Matrix.trace (chartMultiplierAssembly activeSet multiplier selection) = 1 := by
  rw [trace_chartMultiplierAssembly_eq_sum,
    Finset.sum_congr rfl fun activeLabel hmem => by rw [hunit activeLabel hmem, mul_one], hmass]

/-- **The multiplier-weighted slope, in closed form**: the assembly's trace against the
direction matrix, minus the assembly's diagonal against the direction weight.  Every
statement below is this identity read at a particular family of directions. -/
theorem sum_multiplier_chartTangentSlope_eq (activeSet : Finset activeIndex)
    (multiplier : activeIndex → ℝ) (selection : activeIndex → (Fin size → ℝ))
    {directionMatrix : Matrix (Fin size) (Fin size) ℝ}
    (hsymmetric : directionMatrixᵀ = directionMatrix) (directionWeight : Fin size → ℝ) :
    ∑ activeLabel ∈ activeSet,
        multiplier activeLabel
          * chartTangentSlope (selection activeLabel) directionMatrix directionWeight
      = Matrix.trace (chartMultiplierAssembly activeSet multiplier selection * directionMatrix)
        - ∑ atomIndex : Fin size, directionWeight atomIndex
            * chartMultiplierAssembly activeSet multiplier selection atomIndex atomIndex := by
  have hquadraticPart : ∑ activeLabel ∈ activeSet,
        multiplier activeLabel
          * (selection activeLabel ⬝ᵥ (directionMatrix *ᵥ selection activeLabel))
      = Matrix.trace
          (chartMultiplierAssembly activeSet multiplier selection * directionMatrix) := by
    rw [chartMultiplierAssembly, Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun activeLabel _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      trace_atomMatrix_mul_of_symmetric (selection activeLabel) hsymmetric]
  have hweightPart : ∑ activeLabel ∈ activeSet,
      multiplier activeLabel
        * ∑ atomIndex : Fin size, directionWeight atomIndex * selection activeLabel atomIndex ^ 2
      = ∑ atomIndex : Fin size, directionWeight atomIndex
          * chartMultiplierAssembly activeSet multiplier selection atomIndex atomIndex := by
    have hexpand : ∀ activeLabel : activeIndex,
        multiplier activeLabel
            * ∑ atomIndex : Fin size,
                directionWeight atomIndex * selection activeLabel atomIndex ^ 2
          = ∑ atomIndex : Fin size,
              directionWeight atomIndex
                * (multiplier activeLabel * selection activeLabel atomIndex ^ 2) := by
      intro activeLabel
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun atomIndex _ => by ring
    rw [Finset.sum_congr rfl fun activeLabel _ => hexpand activeLabel, Finset.sum_comm]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [← Finset.mul_sum, ← chartMultiplierAssembly_diagonal]
  calc ∑ activeLabel ∈ activeSet,
        multiplier activeLabel
          * chartTangentSlope (selection activeLabel) directionMatrix directionWeight
      = ∑ activeLabel ∈ activeSet,
          (multiplier activeLabel
              * (selection activeLabel ⬝ᵥ (directionMatrix *ᵥ selection activeLabel))
            - multiplier activeLabel
              * ∑ atomIndex : Fin size,
                  directionWeight atomIndex
                    * selection activeLabel atomIndex ^ 2) := by
        refine Finset.sum_congr rfl fun activeLabel _ => ?_
        rw [chartTangentSlope_eq_sub]
        ring
    _ = _ := by rw [Finset.sum_sub_distrib, hquadraticPart, hweightPart]

/-! ## The algebraic equivalence

The identity that makes the two systems comparable: a multiplier vector kills every
tangent functional exactly when its assembly has constant diagonal and commutes with the
chart — which are the two stationarity fields of `Gtz.IsChartStationaryData`. -/

/-- **A commuting matrix is trace-orthogonal to every tangent direction.**  The direction
has no diagonal blocks and the commutant has no off-diagonal ones, so the two never
meet.  Only idempotence is used; symmetry is not. -/
theorem trace_mul_eq_zero_of_commutes_of_isChartTangent
    {projection commuting directionMatrix : Matrix (Fin size) (Fin size) ℝ}
    {directionWeight : Fin size → ℝ}
    (hidempotent : projection * projection = projection)
    (hcommutes : projection * commuting = commuting * projection)
    (htangent : IsChartTangent projection directionMatrix directionWeight) :
    Matrix.trace (commuting * directionMatrix) = 0 := by
  have hrightAnnihilate :
      projection * (1 - projection : Matrix (Fin size) (Fin size) ℝ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hidempotent, sub_self]
  have hleftAnnihilate :
      (1 - projection : Matrix (Fin size) (Fin size) ℝ) * projection = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hidempotent, sub_self]
  have hmixedFirst : (1 - projection) * commuting * projection = 0 := by
    rw [Matrix.mul_assoc, ← hcommutes, ← Matrix.mul_assoc, hleftAnnihilate, Matrix.zero_mul]
  have hmixedSecond : projection * commuting * (1 - projection) = 0 := by
    rw [hcommutes, Matrix.mul_assoc, hrightAnnihilate, Matrix.mul_zero]
  have hsplit : directionMatrix
      = projection * directionMatrix * (1 - projection)
        + (1 - projection) * directionMatrix * projection := by
    have hfull : directionMatrix
        = projection * directionMatrix * projection
          + projection * directionMatrix * (1 - projection)
          + (1 - projection) * directionMatrix * projection
          + (1 - projection) * directionMatrix * (1 - projection) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      abel
    conv_lhs => rw [hfull, htangent.rangeBlock_eq_zero, htangent.kernelBlock_eq_zero]
    abel
  have hfirst :
      Matrix.trace (commuting * (projection * directionMatrix * (1 - projection))) = 0 := by
    calc Matrix.trace (commuting * (projection * directionMatrix * (1 - projection)))
        = Matrix.trace ((commuting * projection * directionMatrix) * (1 - projection)) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((1 - projection) * (commuting * projection * directionMatrix)) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace (((1 - projection) * commuting * projection) * directionMatrix) := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hmixedFirst, Matrix.zero_mul, Matrix.trace_zero]
  have hsecond :
      Matrix.trace (commuting * ((1 - projection) * directionMatrix * projection)) = 0 := by
    calc Matrix.trace (commuting * ((1 - projection) * directionMatrix * projection))
        = Matrix.trace ((commuting * (1 - projection) * directionMatrix) * projection) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (projection * (commuting * (1 - projection) * directionMatrix)) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((projection * commuting * (1 - projection)) * directionMatrix) := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hmixedSecond, Matrix.zero_mul, Matrix.trace_zero]
  conv_lhs => rw [hsplit]
  rw [Matrix.mul_add, Matrix.trace_add, hfirst, hsecond, add_zero]

/-- **The off-block trace, in closed form**: `tr(X . offBlock(N)) = 2 tr((1-P) X P N)`.
Both summands of the off-block direction contribute the same number, the second through
one transposition. -/
theorem trace_mul_chartOffBlockDirection_eq
    {projection commuting param : Matrix (Fin size) (Fin size) ℝ}
    (hprojectionSymmetric : projectionᵀ = projection)
    (hcommutingSymmetric : commutingᵀ = commuting) :
    Matrix.trace (commuting * chartOffBlockDirection projection param)
      = 2 * Matrix.trace ((1 - projection) * commuting * projection * param) := by
  have hcomplementSymmetric :
      (1 - projection : Matrix (Fin size) (Fin size) ℝ)ᵀ = 1 - projection := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hprojectionSymmetric]
  have hfirst : Matrix.trace (commuting * (projection * param * (1 - projection)))
      = Matrix.trace ((1 - projection) * commuting * projection * param) := by
    calc Matrix.trace (commuting * (projection * param * (1 - projection)))
        = Matrix.trace ((commuting * projection * param) * (1 - projection)) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((1 - projection) * (commuting * projection * param)) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((1 - projection) * commuting * projection * param) := by
          simp only [Matrix.mul_assoc]
  have hblockTranspose : projection * commuting * (1 - projection)
      = ((1 - projection) * commuting * projection)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hprojectionSymmetric, hcommutingSymmetric,
      hcomplementSymmetric]
    simp only [Matrix.mul_assoc]
  have hsecond : Matrix.trace (commuting * ((1 - projection) * paramᵀ * projection))
      = Matrix.trace ((1 - projection) * commuting * projection * param) := by
    calc Matrix.trace (commuting * ((1 - projection) * paramᵀ * projection))
        = Matrix.trace ((commuting * (1 - projection) * paramᵀ) * projection) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (projection * (commuting * (1 - projection) * paramᵀ)) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((projection * commuting * (1 - projection)) * paramᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (((1 - projection) * commuting * projection)ᵀ * paramᵀ) := by
          rw [hblockTranspose]
      _ = Matrix.trace ((1 - projection) * commuting * projection * param) := by
          rw [← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]
  rw [chartOffBlockDirection, Matrix.mul_add, Matrix.trace_add, hfirst, hsecond]
  ring

/-- **The Frobenius trace of a matrix against its own transpose is its sum of squares**,
which is how a vanishing trace identity becomes a vanishing matrix. -/
theorem trace_mul_transpose_self_eq_sum_sq (blockMatrix : Matrix (Fin size) (Fin size) ℝ) :
    Matrix.trace (blockMatrix * blockMatrixᵀ)
      = ∑ rowIndex : Fin size, ∑ colIndex : Fin size, blockMatrix rowIndex colIndex ^ 2 := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]

/-- **A vanishing off-diagonal block IS commutation**, for symmetric operands. -/
theorem commutes_of_offBlock_eq_zero
    {projection commuting : Matrix (Fin size) (Fin size) ℝ}
    (hprojectionSymmetric : projectionᵀ = projection)
    (hcommutingSymmetric : commutingᵀ = commuting)
    (hoffBlock : projection * commuting * (1 - projection) = 0) :
    projection * commuting = commuting * projection := by
  have hleft : projection * commuting = projection * commuting * projection := by
    have hexpand : projection * commuting - projection * commuting * projection = 0 := by
      rw [← hoffBlock, Matrix.mul_sub, Matrix.mul_one]
    exact sub_eq_zero.mp hexpand
  have hright : commuting * projection = projection * commuting * projection := by
    have htransposed := congrArg Matrix.transpose hleft
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, hprojectionSymmetric,
      hcommutingSymmetric] at htransposed
    simp only [Matrix.mul_assoc] at htransposed ⊢
    exact htransposed
  rw [hleft, hright]

/-- **The entrywise off-block assembly**: `(P Xi (1-P))` collects the outer products of
the range and kernel components of the tight directions.  This is the matrix the Gordan
family's block coordinates pair against. -/
theorem offBlock_chartMultiplierAssembly_apply
    {projection : Matrix (Fin size) (Fin size) ℝ} (hsymmetric : projectionᵀ = projection)
    (activeSet : Finset activeIndex) (multiplier : activeIndex → ℝ)
    (selection : activeIndex → (Fin size → ℝ)) (rowIndex colIndex : Fin size) :
    (projection * chartMultiplierAssembly activeSet multiplier selection * (1 - projection))
        rowIndex colIndex
      = ∑ activeLabel ∈ activeSet, multiplier activeLabel
          * ((projection *ᵥ selection activeLabel) rowIndex
            * ((1 - projection) *ᵥ selection activeLabel) colIndex) := by
  have hcomplementSymmetric :
      (1 - projection : Matrix (Fin size) (Fin size) ℝ)ᵀ = 1 - projection := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsymmetric]
  have hblock : projection * chartMultiplierAssembly activeSet multiplier selection
        * (1 - projection)
      = ∑ activeLabel ∈ activeSet, multiplier activeLabel •
          Matrix.vecMulVec (projection *ᵥ selection activeLabel)
            ((1 - projection) *ᵥ selection activeLabel) := by
    rw [chartMultiplierAssembly, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun activeLabel _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, atomMatrix, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      ← Matrix.mulVec_transpose, hcomplementSymmetric]
  rw [hblock]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]

/-- **A multiplier vector is BALANCED against a selection** when it is a convex
combination whose tangent functional vanishes identically.  This is "zero lies in the
convex hull of the induced linear functionals", written without a hull. -/
def IsChartBalancedMultiplier (projection : Matrix (Fin size) (Fin size) ℝ)
    (activeSet : Finset activeIndex) (multiplier : activeIndex → ℝ)
    (selection : activeIndex → (Fin size → ℝ)) : Prop :=
  (∀ activeLabel ∈ activeSet, 0 ≤ multiplier activeLabel)
    ∧ (∑ activeLabel ∈ activeSet, multiplier activeLabel = 1)
    ∧ ∀ (directionMatrix : Matrix (Fin size) (Fin size) ℝ) (directionWeight : Fin size → ℝ),
        IsChartTangent projection directionMatrix directionWeight →
        ∑ activeLabel ∈ activeSet,
          multiplier activeLabel
            * chartTangentSlope (selection activeLabel) directionMatrix directionWeight = 0

/-- The selection admits a balanced multiplier. -/
def HasBalancedMultiplier (projection : Matrix (Fin size) (Fin size) ℝ)
    (activeSet : Finset activeIndex) (selection : activeIndex → (Fin size → ℝ)) : Prop :=
  ∃ multiplier : activeIndex → ℝ,
    IsChartBalancedMultiplier projection activeSet multiplier selection

/-- **THE ALGEBRAIC EQUIVALENCE.**  For a convex multiplier vector against a unit
selection, balance is exactly the pair of stationarity conditions of the shipped bundle:
constant diagonal `1/size`, and commutation with the chart.

Forward, the diagonal comes from the sum-zero weight directions and the commutation from
the off-block directions at the parameter `P Xi (1-P)`, where the closed form
`2 tr((1-P) Xi P N)` becomes a sum of squares.  Backward, the diagonal collapses the
weight term against `sum dt = 0` and the commutation kills the trace term.

No analysis and no convexity enters — this is the definition of the tangent space plus
matrix algebra. -/
theorem isChartBalancedMultiplier_iff {projection : Matrix (Fin size) (Fin size) ℝ}
    {activeSet : Finset activeIndex} {multiplier : activeIndex → ℝ}
    {selection : activeIndex → (Fin size → ℝ)}
    (hsymmetric : projectionᵀ = projection) (hidempotent : projection * projection = projection)
    (hsizePos : 0 < size)
    (hnonneg : ∀ activeLabel ∈ activeSet, 0 ≤ multiplier activeLabel)
    (hmass : ∑ activeLabel ∈ activeSet, multiplier activeLabel = 1)
    (hunit : ∀ activeLabel ∈ activeSet, selection activeLabel ⬝ᵥ selection activeLabel = 1) :
    IsChartBalancedMultiplier projection activeSet multiplier selection
      ↔ ((∀ atomIndex : Fin size,
            chartMultiplierAssembly activeSet multiplier selection atomIndex atomIndex
              = ((size : ℝ))⁻¹)
          ∧ projection * chartMultiplierAssembly activeSet multiplier selection
              = chartMultiplierAssembly activeSet multiplier selection * projection) := by
  have hassemblySymmetric := transpose_chartMultiplierAssembly activeSet multiplier selection
  have htraceOne := trace_chartMultiplierAssembly_eq_one hunit hmass
  constructor
  · rintro ⟨-, -, hvanish⟩
    have hconstantDiagonal : ∀ firstIndex secondIndex : Fin size,
        chartMultiplierAssembly activeSet multiplier selection firstIndex firstIndex
          = chartMultiplierAssembly activeSet multiplier selection secondIndex secondIndex := by
      intro firstIndex secondIndex
      have hslope := hvanish 0
        (fun atomIndex => (if atomIndex = firstIndex then (1 : ℝ) else 0)
          - (if atomIndex = secondIndex then (1 : ℝ) else 0))
        (isChartTangent_weightDifference projection firstIndex secondIndex)
      rw [sum_multiplier_chartTangentSlope_eq activeSet multiplier selection
        Matrix.transpose_zero] at hslope
      rw [Matrix.mul_zero, Matrix.trace_zero, zero_sub, neg_eq_zero] at hslope
      have hdifference : ∑ atomIndex : Fin size,
          ((if atomIndex = firstIndex then (1 : ℝ) else 0)
            - (if atomIndex = secondIndex then (1 : ℝ) else 0))
            * chartMultiplierAssembly activeSet multiplier selection atomIndex atomIndex
          = chartMultiplierAssembly activeSet multiplier selection firstIndex firstIndex
            - chartMultiplierAssembly activeSet multiplier selection secondIndex secondIndex := by
        simp [sub_mul, Finset.sum_sub_distrib]
      rw [hdifference] at hslope
      linarith
    have hdiagonal := (diagonal_eq_inv_size_iff_diagonal_constant hsizePos _ htraceOne).mpr
      hconstantDiagonal
    refine ⟨hdiagonal, ?_⟩
    refine commutes_of_offBlock_eq_zero hsymmetric hassemblySymmetric ?_
    have hoffBlockZero : (1 - projection) * chartMultiplierAssembly activeSet multiplier selection
        * projection = 0 := by
      have hslope := hvanish
        (chartOffBlockDirection projection
          (projection * chartMultiplierAssembly activeSet multiplier selection * (1 - projection)))
        0
        (isChartTangent_chartOffBlockDirection hsymmetric hidempotent _)
      rw [sum_multiplier_chartTangentSlope_eq activeSet multiplier selection
        (isChartTangent_chartOffBlockDirection hsymmetric hidempotent _).isSymmetric] at hslope
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero] at hslope
      rw [trace_mul_chartOffBlockDirection_eq hsymmetric hassemblySymmetric] at hslope
      have hparamTranspose : projection * chartMultiplierAssembly activeSet multiplier selection
          * (1 - projection)
          = ((1 - projection) * chartMultiplierAssembly activeSet multiplier selection
              * projection)ᵀ := by
        have hcomplementSymmetric :
            (1 - projection : Matrix (Fin size) (Fin size) ℝ)ᵀ = 1 - projection := by
          rw [Matrix.transpose_sub, Matrix.transpose_one, hsymmetric]
        rw [Matrix.transpose_mul, Matrix.transpose_mul, hsymmetric, hassemblySymmetric,
          hcomplementSymmetric]
        simp only [Matrix.mul_assoc]
      rw [hparamTranspose] at hslope
      rw [trace_mul_transpose_self_eq_sum_sq] at hslope
      have hallZero : ∀ rowIndex : Fin size, ∀ colIndex : Fin size,
          ((1 - projection) * chartMultiplierAssembly activeSet multiplier selection * projection)
            rowIndex colIndex = 0 := by
        have houter : ∑ rowIndex : Fin size, ∑ colIndex : Fin size,
            ((1 - projection) * chartMultiplierAssembly activeSet multiplier selection
              * projection) rowIndex colIndex ^ 2 = 0 := by linarith
        intro rowIndex colIndex
        have hinner := (Finset.sum_eq_zero_iff_of_nonneg
          (fun someRow _ => Finset.sum_nonneg fun someCol _ => sq_nonneg _)).mp houter rowIndex
          (Finset.mem_univ rowIndex)
        have hentry := (Finset.sum_eq_zero_iff_of_nonneg
          (fun someCol _ => sq_nonneg _)).mp hinner colIndex (Finset.mem_univ colIndex)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hentry
      ext rowIndex colIndex
      rw [hallZero rowIndex colIndex, Matrix.zero_apply]
    have htransposedZero := congrArg Matrix.transpose hoffBlockZero
    have hcomplementSymmetric :
        (1 - projection : Matrix (Fin size) (Fin size) ℝ)ᵀ = 1 - projection := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, hsymmetric]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hsymmetric, hassemblySymmetric,
      hcomplementSymmetric, Matrix.transpose_zero] at htransposedZero
    simp only [Matrix.mul_assoc] at htransposedZero ⊢
    exact htransposedZero
  · rintro ⟨hdiagonal, hcommutes⟩
    refine ⟨hnonneg, hmass, fun directionMatrix directionWeight htangent => ?_⟩
    rw [sum_multiplier_chartTangentSlope_eq activeSet multiplier selection htangent.isSymmetric,
      trace_mul_eq_zero_of_commutes_of_isChartTangent hidempotent hcommutes htangent]
    have hweightTerm : ∑ atomIndex : Fin size, directionWeight atomIndex
        * chartMultiplierAssembly activeSet multiplier selection atomIndex atomIndex = 0 := by
      rw [Finset.sum_congr rfl fun atomIndex _ => by rw [hdiagonal atomIndex], ← Finset.sum_mul,
        htangent.weight_sum_zero, zero_mul]
    rw [hweightTerm, sub_zero]

/-- **THE WEIGHT-SLICE READING of balance**: the uniform vector `1/size` is the
multiplier barycentre of the squared-overlap vectors `(v_C(c)^2)_c`.

This is the sub-family of directions — chart held fixed, weights moved inside the simplex
— on which the cheap exclusions live.  Nothing further is developed from it here. -/
theorem sum_multiplier_sq_eq_inv_size_of_isChartBalancedMultiplier
    {projection : Matrix (Fin size) (Fin size) ℝ} {activeSet : Finset activeIndex}
    {multiplier : activeIndex → ℝ} {selection : activeIndex → (Fin size → ℝ)}
    (hsymmetric : projectionᵀ = projection) (hidempotent : projection * projection = projection)
    (hsizePos : 0 < size)
    (hunit : ∀ activeLabel ∈ activeSet, selection activeLabel ⬝ᵥ selection activeLabel = 1)
    (hbalanced : IsChartBalancedMultiplier projection activeSet multiplier selection)
    (atomIndex : Fin size) :
    ∑ activeLabel ∈ activeSet, multiplier activeLabel * selection activeLabel atomIndex ^ 2
      = ((size : ℝ))⁻¹ := by
  rw [← chartMultiplierAssembly_diagonal]
  exact ((isChartBalancedMultiplier_iff hsymmetric hidempotent hsizePos hbalanced.1 hbalanced.2.1
    hunit).mp hbalanced).1 atomIndex

/-! ## Tight directions and the strong bundle -/

/-- **A unit tight direction of one active block**: unit length, supported inside the
subset, and an eigenvector of the chart gap at `value` READ COORDINATEWISE ON the subset.
Nothing is asserted off the subset, where the ambient product is generally nonzero.

These are exactly the three tight fields of `Gtz.IsChartStationaryData`, factored out so
that the universal quantifier below has something to range over. -/
structure IsChartTightDirection (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (value : ℝ) (chosenSubset : Finset (Fin size))
    (tightVec : Fin size → ℝ) : Prop where
  /-- The direction is a unit vector. -/
  isUnit : tightVec ⬝ᵥ tightVec = 1
  /-- The direction is supported inside the subset. -/
  hasSupport : ∀ atomIndex : Fin size, atomIndex ∉ chosenSubset → tightVec atomIndex = 0
  /-- Tightness on the subset. -/
  isTight : ∀ atomIndex ∈ chosenSubset,
    (chartStationaryGap projection weight *ᵥ tightVec) atomIndex = value * tightVec atomIndex

/-- **The first-order stationarity data of the CHART objective, in the form that
quantifies over EVERY tight selection.**

The chart point and the active family are exactly the weak bundle's.  What replaces the
weak bundle's multiplier fields is: every active block HAS a unit tight direction, and
every SELECTION of such directions admits a balanced multiplier.

This is a HYPOTHESIS, never a theorem.  See the honesty section of the file header: the
system is NECESSARY only, it inherits the disjunctive admissibility weakness of the weak
bundle undiminished, it contains no realness ingredient, and instantiating it at a tie
presupposes `ChartGtz` near that tie. -/
structure IsChartStrongStationaryData (rank : ℕ) (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (value : ℝ) (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin size)) : Prop where
  /-- The chart is symmetric. -/
  isSymmetric : projectionᵀ = projection
  /-- The chart is idempotent — over ℝ with symmetry, an orthogonal projection. -/
  isIdempotent : projection * projection = projection
  /-- The chart's trace is the rank. -/
  hasTraceRank : Matrix.trace projection = (rank : ℝ)
  /-- The weights are strictly positive: this is the INTERIOR of the simplex. -/
  weight_pos : ∀ atomIndex : Fin size, 0 < weight atomIndex
  /-- The weights sum to one. -/
  weight_sum_one : ∑ atomIndex : Fin size, weight atomIndex = 1
  /-- Every active subset has exactly `rank` atoms. -/
  activeSubset_card : ∀ activeLabel ∈ activeSet, (activeSubset activeLabel).card = rank
  /-- Every active block genuinely carries a unit tight direction.  Without this field the
  universal one below would be vacuously true. -/
  exists_tightDir : ∀ activeLabel ∈ activeSet,
    ∃ tightVec : Fin size → ℝ,
      IsChartTightDirection projection weight value (activeSubset activeLabel) tightVec
  /-- **The universal multiplier condition**: EVERY selection of unit tight directions
  admits a balanced multiplier. -/
  hasBalancedMultiplier_of_isChartTightSelection :
    ∀ selection : activeIndex → (Fin size → ℝ),
      (∀ activeLabel ∈ activeSet,
        IsChartTightDirection projection weight value (activeSubset activeLabel)
          (selection activeLabel)) →
      HasBalancedMultiplier projection activeSet selection

variable {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
  {value : ℝ} {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}

/-- **The size is positive.**  An empty index set carries no weights, so the weight sum
would be zero rather than one.  Every division by `size` below is licensed by this. -/
theorem size_pos_of_isChartStrongStationaryData
    (hdata : IsChartStrongStationaryData rank projection weight value activeSet activeSubset) :
    0 < size := by
  by_contra hnonpositive
  have hsizeZero : size = 0 := Nat.le_zero.mp (not_lt.mp hnonpositive)
  subst hsizeZero
  have hsum := hdata.weight_sum_one
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  exact absurd hsum (by norm_num)

/-! ## The refinement: the strong system implies the weak one -/

/-- **THE REFINEMENT, at a named selection.**  Specialising the universal field to the
selection the weak bundle names produces multipliers, and the algebraic equivalence turns
balance into the weak bundle's two stationarity equations.

Every consequence of `Gtz.IsChartStationaryData` therefore transfers: the coverage law,
the forced diagonal, the weight floor, the one-sided value bound, the dual bound. -/
theorem exists_multiplier_isChartStationaryData_of_isChartStrongStationaryData
    (hdata : IsChartStrongStationaryData rank projection weight value activeSet activeSubset)
    (selection : activeIndex → (Fin size → ℝ))
    (hselection : ∀ activeLabel ∈ activeSet,
      IsChartTightDirection projection weight value (activeSubset activeLabel)
        (selection activeLabel)) :
    ∃ multiplier : activeIndex → ℝ,
      IsChartStationaryData rank projection weight value activeSet activeSubset multiplier
        selection := by
  obtain ⟨multiplier, hnonneg, hmass, hvanish⟩ :=
    hdata.hasBalancedMultiplier_of_isChartTightSelection selection hselection
  have hunit : ∀ activeLabel ∈ activeSet,
      selection activeLabel ⬝ᵥ selection activeLabel = 1 :=
    fun activeLabel hmem => (hselection activeLabel hmem).isUnit
  obtain ⟨hdiagonal, hcommutes⟩ :=
    (isChartBalancedMultiplier_iff hdata.isSymmetric hdata.isIdempotent
      (size_pos_of_isChartStrongStationaryData hdata) hnonneg hmass hunit).mp
      ⟨hnonneg, hmass, hvanish⟩
  exact ⟨multiplier,
    { isSymmetric := hdata.isSymmetric
      isIdempotent := hdata.isIdempotent
      hasTraceRank := hdata.hasTraceRank
      weight_pos := hdata.weight_pos
      weight_sum_one := hdata.weight_sum_one
      activeWeight_nonneg := hnonneg
      activeWeight_sum_one := hmass
      activeSubset_card := hdata.activeSubset_card
      tightDir_unit := hunit
      tightDir_support := fun activeLabel hmem => (hselection activeLabel hmem).hasSupport
      tightDir_isTight := fun activeLabel hmem => (hselection activeLabel hmem).isTight
      assembly_diagonal := hdiagonal
      assembly_commutes := hcommutes }⟩

/-- **THE REFINEMENT, with no selection supplied.**  The `exists_tightDir` field makes one
by choice, so a strong datum unconditionally produces a weak one. -/
theorem exists_isChartStationaryData_of_isChartStrongStationaryData
    (hdata : IsChartStrongStationaryData rank projection weight value activeSet activeSubset) :
    ∃ (multiplier : activeIndex → ℝ) (selection : activeIndex → (Fin size → ℝ)),
      IsChartStationaryData rank projection weight value activeSet activeSubset multiplier
        selection := by
  classical
  choose pickTightDir hpickTightDir using hdata.exists_tightDir
  have hselection : ∀ activeLabel ∈ activeSet,
      IsChartTightDirection projection weight value (activeSubset activeLabel)
        (fun atomIndex =>
          if hmem : activeLabel ∈ activeSet then pickTightDir activeLabel hmem atomIndex
          else 0) := by
    intro activeLabel hmem
    simpa only [dif_pos hmem] using hpickTightDir activeLabel hmem
  obtain ⟨multiplier, hweak⟩ :=
    exists_multiplier_isChartStationaryData_of_isChartStrongStationaryData hdata _ hselection
  exact ⟨multiplier, _, hweak⟩

/-! ## The descent lemma -/

/-- **The Riesz vector of a tight direction's tangent functional.**  The block
coordinates pair against the off-block matrix parameter and the atom coordinates against
the raw weight parameter; `sum_chartTangentRiesz_mul_eq_chartTangentSlope` proves the
pairing is exactly the slope. -/
noncomputable def chartTangentRiesz (projection : Matrix (Fin size) (Fin size) ℝ)
    (tightVec : Fin size → ℝ) :
    (Fin size × Fin size ⊕ Fin size) → ℝ :=
  Sum.elim
    (fun blockIndex =>
      2 * ((projection *ᵥ tightVec) blockIndex.1
        * ((1 - projection) *ᵥ tightVec) blockIndex.2))
    (fun atomIndex => ((size : ℝ))⁻¹ - tightVec atomIndex ^ 2)

/-- A bilinear form, expanded into its double sum. -/
theorem dotProduct_mulVec_eq_sum_sum (leftVec rightVec : Fin size → ℝ)
    (middleMatrix : Matrix (Fin size) (Fin size) ℝ) :
    leftVec ⬝ᵥ (middleMatrix *ᵥ rightVec)
      = ∑ rowIndex : Fin size, ∑ colIndex : Fin size,
          leftVec rowIndex * middleMatrix rowIndex colIndex * rightVec colIndex := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun rowIndex _ =>
    Finset.sum_congr rfl fun colIndex _ => by ring

/-- The off-block direction's Rayleigh quotient, expanded into the double sum the Riesz
vector pairs against. -/
theorem dotProduct_chartOffBlockDirection_mulVec
    {projection : Matrix (Fin size) (Fin size) ℝ} (hsymmetric : projectionᵀ = projection)
    (param : Matrix (Fin size) (Fin size) ℝ) (tightVec : Fin size → ℝ) :
    tightVec ⬝ᵥ (chartOffBlockDirection projection param *ᵥ tightVec)
      = 2 * ∑ rowIndex : Fin size, ∑ colIndex : Fin size,
          (projection *ᵥ tightVec) rowIndex * param rowIndex colIndex
            * ((1 - projection) *ᵥ tightVec) colIndex := by
  have hcomplementSymmetric :
      (1 - projection : Matrix (Fin size) (Fin size) ℝ)ᵀ = 1 - projection := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsymmetric]
  have hrange : tightVec ⬝ᵥ ((projection * param * (1 - projection)) *ᵥ tightVec)
      = (projection *ᵥ tightVec) ⬝ᵥ (param *ᵥ ((1 - projection) *ᵥ tightVec)) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← dotProduct_mulVec_transpose projection tightVec, hsymmetric]
  have hkernel : tightVec ⬝ᵥ (((1 - projection) * paramᵀ * projection) *ᵥ tightVec)
      = (projection *ᵥ tightVec) ⬝ᵥ (param *ᵥ ((1 - projection) *ᵥ tightVec)) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← dotProduct_mulVec_transpose (1 - projection) tightVec, hcomplementSymmetric,
      dotProduct_comm ((1 - projection) *ᵥ tightVec) (paramᵀ *ᵥ (projection *ᵥ tightVec)),
      dotProduct_mulVec_transpose param (projection *ᵥ tightVec)
        ((1 - projection) *ᵥ tightVec)]
  rw [chartOffBlockDirection, Matrix.add_mulVec, dotProduct_add, hrange, hkernel,
    dotProduct_mulVec_eq_sum_sum]
  ring

/-- **THE PAIRING IDENTITY.**  The Riesz vector of a unit tight direction pairs with an
arbitrary probe exactly to the slope along the tangent direction the probe parametrises.
This is what makes the Gordan alternative applicable, and it is where the unit
normalisation is spent. -/
theorem sum_chartTangentRiesz_mul_eq_chartTangentSlope
    {projection : Matrix (Fin size) (Fin size) ℝ} (hsymmetric : projectionᵀ = projection)
    {tightVec : Fin size → ℝ} (hunit : tightVec ⬝ᵥ tightVec = 1) (hsizePos : 0 < size)
    (probe : (Fin size × Fin size ⊕ Fin size) → ℝ) :
    ∑ coord : (Fin size × Fin size ⊕ Fin size),
        chartTangentRiesz projection tightVec coord * probe coord
      = chartTangentSlope tightVec
          (chartOffBlockDirection projection
            (Matrix.of fun rowIndex colIndex => probe (Sum.inl (rowIndex, colIndex))))
          (chartCenteredWeight fun atomIndex => probe (Sum.inr atomIndex)) := by
  have hsizeNe : ((size : ℝ)) ≠ 0 := by
    have hcast : (0 : ℝ) < (size : ℝ) := by exact_mod_cast hsizePos
    exact ne_of_gt hcast
  have hsquares : ∑ atomIndex : Fin size, tightVec atomIndex ^ 2 = 1 := by
    rw [← dotProduct_self_eq_sum_sq]
    exact hunit
  rw [chartTangentSlope_eq_sub,
    dotProduct_chartOffBlockDirection_mulVec hsymmetric _ tightVec,
    Fintype.sum_sum_type]
  simp only [chartTangentRiesz, Sum.elim_inl, Sum.elim_inr, Matrix.of_apply, chartCenteredWeight]
  rw [Fintype.sum_prod_type]
  have hblock : ∑ rowIndex : Fin size, ∑ colIndex : Fin size,
      2 * ((projection *ᵥ tightVec) rowIndex * ((1 - projection) *ᵥ tightVec) colIndex)
        * probe (Sum.inl (rowIndex, colIndex))
      = 2 * ∑ rowIndex : Fin size, ∑ colIndex : Fin size,
          (projection *ᵥ tightVec) rowIndex * probe (Sum.inl (rowIndex, colIndex))
            * ((1 - projection) *ᵥ tightVec) colIndex := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun rowIndex _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun colIndex _ => by ring
  have hatom : ∑ atomIndex : Fin size,
      (((size : ℝ))⁻¹ - tightVec atomIndex ^ 2) * probe (Sum.inr atomIndex)
      = -∑ atomIndex : Fin size,
          (probe (Sum.inr atomIndex)
            - (∑ otherIndex : Fin size, probe (Sum.inr otherIndex)) / (size : ℝ))
            * tightVec atomIndex ^ 2 := by
    have hsplitLeft : ∑ atomIndex : Fin size,
        (((size : ℝ))⁻¹ - tightVec atomIndex ^ 2) * probe (Sum.inr atomIndex)
        = ((size : ℝ))⁻¹ * ∑ atomIndex : Fin size, probe (Sum.inr atomIndex)
          - ∑ atomIndex : Fin size, tightVec atomIndex ^ 2 * probe (Sum.inr atomIndex) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun atomIndex _ => by ring
    have hsplitRight : ∑ atomIndex : Fin size,
        (probe (Sum.inr atomIndex)
          - (∑ otherIndex : Fin size, probe (Sum.inr otherIndex)) / (size : ℝ))
          * tightVec atomIndex ^ 2
        = ∑ atomIndex : Fin size, tightVec atomIndex ^ 2 * probe (Sum.inr atomIndex)
          - (∑ otherIndex : Fin size, probe (Sum.inr otherIndex)) / (size : ℝ)
            * ∑ atomIndex : Fin size, tightVec atomIndex ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun atomIndex _ => by ring
    rw [hsplitLeft, hsplitRight, hsquares, mul_one]
    field_simp
    ring
  rw [hblock, hatom]
  ring

/-- **THE DESCENT LEMMA.**  If a tight selection admits NO balanced multiplier then there
is a tangent direction along which EVERY active block's tight Rayleigh quotient strictly
decreases.

This is the Gordan alternative applied to the Riesz vectors of the tangent functionals:
the hull branch is exactly a balanced multiplier, so its failure hands back a separating
direction, and the pairing identity turns the separating probe into a genuine tangent
direction of the chart.

WHAT THIS IS NOT.  It is FIRST-ORDER data and nothing more.  Turning it into an actual
decrease of `G = max_C lambda_min(W[C])` needs three ingredients that live outside Lean:
a curve on the Grassmannian whose derivative is this direction; the continuity of
`lambda_min` on the INACTIVE blocks, so that a block strictly below the value stays below
it — that side condition is named `IsChartInactiveStrict` below rather than hidden; and
the identification of the active family with the argmax family, which is
`Gtz.IsChartArgmaxValue` and is not a field of either bundle. -/
theorem exists_isChartTangent_forall_chartTangentSlope_neg
    {selection : activeIndex → (Fin size → ℝ)}
    (hsymmetric : projectionᵀ = projection) (hidempotent : projection * projection = projection)
    (hsizePos : 0 < size)
    (hunit : ∀ activeLabel ∈ activeSet, selection activeLabel ⬝ᵥ selection activeLabel = 1)
    (hunbalanced : ¬ HasBalancedMultiplier projection activeSet selection) :
    ∃ (directionMatrix : Matrix (Fin size) (Fin size) ℝ) (directionWeight : Fin size → ℝ),
      IsChartTangent projection directionMatrix directionWeight
        ∧ ∀ activeLabel ∈ activeSet,
            chartTangentSlope (selection activeLabel) directionMatrix directionWeight < 0 := by
  rcases gordan_alternative_finsetFamily activeSet
      (fun activeLabel => chartTangentRiesz projection (selection activeLabel)) with
    ⟨multiplier, hnonneg, hmass, hcoordinate⟩ | ⟨probe, hnegative⟩
  · exfalso
    refine hunbalanced ⟨multiplier, hnonneg, hmass, ?_⟩
    have hdiagonal : ∀ atomIndex : Fin size,
        chartMultiplierAssembly activeSet multiplier selection atomIndex atomIndex
          = ((size : ℝ))⁻¹ := by
      intro atomIndex
      have hatom := hcoordinate (Sum.inr atomIndex)
      simp only [chartTangentRiesz, Sum.elim_inr] at hatom
      have hexpand : ∑ activeLabel ∈ activeSet,
          multiplier activeLabel * (((size : ℝ))⁻¹ - selection activeLabel atomIndex ^ 2)
          = ((size : ℝ))⁻¹ * ∑ activeLabel ∈ activeSet, multiplier activeLabel
            - ∑ activeLabel ∈ activeSet,
                multiplier activeLabel * selection activeLabel atomIndex ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun activeLabel _ => by ring
      rw [hexpand, hmass, mul_one] at hatom
      rw [chartMultiplierAssembly_diagonal]
      linarith
    have hoffBlockZero :
        projection * chartMultiplierAssembly activeSet multiplier selection * (1 - projection)
          = 0 := by
      ext rowIndex colIndex
      rw [offBlock_chartMultiplierAssembly_apply hsymmetric, Matrix.zero_apply]
      have hblock := hcoordinate (Sum.inl (rowIndex, colIndex))
      simp only [chartTangentRiesz, Sum.elim_inl] at hblock
      have hexpand : ∑ activeLabel ∈ activeSet,
          multiplier activeLabel
            * (2 * ((projection *ᵥ selection activeLabel) rowIndex
                * ((1 - projection) *ᵥ selection activeLabel) colIndex))
          = 2 * ∑ activeLabel ∈ activeSet, multiplier activeLabel
              * ((projection *ᵥ selection activeLabel) rowIndex
                * ((1 - projection) *ᵥ selection activeLabel) colIndex) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun activeLabel _ => by ring
      rw [hexpand] at hblock
      linarith
    have hcommutes := commutes_of_offBlock_eq_zero hsymmetric
      (transpose_chartMultiplierAssembly activeSet multiplier selection) hoffBlockZero
    exact ((isChartBalancedMultiplier_iff hsymmetric hidempotent hsizePos hnonneg hmass
      hunit).mpr ⟨hdiagonal, hcommutes⟩).2.2
  · refine ⟨chartOffBlockDirection projection
      (Matrix.of fun rowIndex colIndex => probe (Sum.inl (rowIndex, colIndex))),
      chartCenteredWeight fun atomIndex => probe (Sum.inr atomIndex), ?_, ?_⟩
    · exact ⟨(isChartTangent_chartOffBlockDirection hsymmetric hidempotent _).isSymmetric,
        (isChartTangent_chartOffBlockDirection hsymmetric hidempotent _).rangeBlock_eq_zero,
        (isChartTangent_chartOffBlockDirection hsymmetric hidempotent _).kernelBlock_eq_zero,
        sum_chartCenteredWeight_eq_zero _⟩
    · intro activeLabel hmem
      rw [← sum_chartTangentRiesz_mul_eq_chartTangentSlope hsymmetric (hunit activeLabel hmem)
        hsizePos probe]
      exact hnegative activeLabel hmem

/-- **THE CONVERSE OF THE DESCENT LEMMA.**  A strictly descending tangent direction rules
out every balanced multiplier: the multiplier-weighted slope would be a convex combination
of strictly negative numbers, hence strictly negative rather than zero.

Pure sign arithmetic, no Gordan.  It is what makes the criterion SHARP. -/
theorem not_hasBalancedMultiplier_of_forall_chartTangentSlope_neg
    {selection : activeIndex → (Fin size → ℝ)}
    {directionMatrix : Matrix (Fin size) (Fin size) ℝ} {directionWeight : Fin size → ℝ}
    (htangent : IsChartTangent projection directionMatrix directionWeight)
    (hnegative : ∀ activeLabel ∈ activeSet,
      chartTangentSlope (selection activeLabel) directionMatrix directionWeight < 0) :
    ¬ HasBalancedMultiplier projection activeSet selection := by
  rintro ⟨multiplier, hnonneg, hmass, hvanish⟩
  obtain ⟨positiveLabel, hpositiveMem, hpositive⟩ :
      ∃ activeLabel ∈ activeSet, 0 < multiplier activeLabel := by
    by_contra hnone
    simp only [not_exists, not_and, not_lt] at hnone
    have hvanishAll : ∀ activeLabel ∈ activeSet, multiplier activeLabel = 0 :=
      fun activeLabel hmem => le_antisymm (hnone activeLabel hmem) (hnonneg activeLabel hmem)
    rw [Finset.sum_congr rfl hvanishAll, Finset.sum_const_zero] at hmass
    exact absurd hmass (by norm_num)
  have hstrict : ∑ activeLabel ∈ activeSet,
      multiplier activeLabel
          * chartTangentSlope (selection activeLabel) directionMatrix directionWeight
        < ∑ _activeLabel ∈ activeSet, (0 : ℝ) := by
    refine Finset.sum_lt_sum (fun activeLabel hmem => ?_) ⟨positiveLabel, hpositiveMem, ?_⟩
    · have hweight := hnonneg activeLabel hmem
      have hslope := (hnegative activeLabel hmem).le
      nlinarith
    · exact mul_neg_of_pos_of_neg hpositive (hnegative positiveLabel hpositiveMem)
  rw [Finset.sum_const_zero, hvanish directionMatrix directionWeight htangent] at hstrict
  exact lt_irrefl 0 hstrict

/-- **BALANCE IS EXACTLY THE ABSENCE OF A FIRST-ORDER DESCENT DIRECTION.**  The descent
lemma and its converse, packaged.  This is the honest size of the criterion: it is a
NECESSARY condition for local minimality that is sharp at first order, and it says nothing
about any order beyond the first. -/
theorem hasBalancedMultiplier_iff_not_exists_descent
    {selection : activeIndex → (Fin size → ℝ)}
    (hsymmetric : projectionᵀ = projection) (hidempotent : projection * projection = projection)
    (hsizePos : 0 < size)
    (hunit : ∀ activeLabel ∈ activeSet, selection activeLabel ⬝ᵥ selection activeLabel = 1) :
    HasBalancedMultiplier projection activeSet selection
      ↔ ¬ ∃ (directionMatrix : Matrix (Fin size) (Fin size) ℝ) (directionWeight : Fin size → ℝ),
          IsChartTangent projection directionMatrix directionWeight
            ∧ ∀ activeLabel ∈ activeSet,
                chartTangentSlope (selection activeLabel) directionMatrix directionWeight < 0 :=
  ⟨fun hbalanced ⟨_, _, htangent, hnegative⟩ =>
      not_hasBalancedMultiplier_of_forall_chartTangentSlope_neg htangent hnegative hbalanced,
   fun hnoDescent => by
      by_contra hunbalanced
      exact hnoDescent (exists_isChartTangent_forall_chartTangentSlope_neg hsymmetric hidempotent
        hsizePos hunit hunbalanced)⟩

/-- **The inactive blocks' side condition**, named rather than hidden: every `rank`-subset
is either carried by the active family or STRICTLY below the value.

Continuity of the least eigenvalue then keeps such a block below the value along a short
curve, which is the second of the three ingredients the descent lemma's conclusion needs
and does not supply.  Nothing in this file proves that continuity, and nothing consumes
this predicate except the reading below. -/
def IsChartInactiveStrict (rank : ℕ) (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (value : ℝ) (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin size)) : Prop :=
  ∀ chosenSubset : Finset (Fin size), chosenSubset.card = rank →
    (∃ activeLabel ∈ activeSet, activeSubset activeLabel = chosenSubset)
      ∨ ∃ probe : Fin size → ℝ, probe ⬝ᵥ probe = 1
          ∧ (∀ atomIndex : Fin size, atomIndex ∉ chosenSubset → probe atomIndex = 0)
          ∧ probe ⬝ᵥ (chartStationaryGap projection weight *ᵥ probe) < value

/-- **The active family is complete**: a `rank`-subset with no strictly-below probe is
carried by the active family.  This is the whole content of the side condition, and it is
the reading under which "inactive" means what the name says. -/
theorem exists_eq_activeSubset_of_isChartInactiveStrict
    (hstrict : IsChartInactiveStrict rank projection weight value activeSet activeSubset)
    {chosenSubset : Finset (Fin size)} (hcard : chosenSubset.card = rank)
    (hnoStrictProbe : ¬ ∃ probe : Fin size → ℝ, probe ⬝ᵥ probe = 1
      ∧ (∀ atomIndex : Fin size, atomIndex ∉ chosenSubset → probe atomIndex = 0)
      ∧ probe ⬝ᵥ (chartStationaryGap projection weight *ᵥ probe) < value) :
    ∃ activeLabel ∈ activeSet, activeSubset activeLabel = chosenSubset :=
  (hstrict chosenSubset hcard).resolve_right hnoStrictProbe

/-! ## The reduction at simple multiplicity -/

/-- **THE REDUCTION, one direction.**  When every active tight eigenspace is spanned by
the named direction — the exact meaning of "the tight eigenvalue is simple" in the
vocabulary this file uses — a weak stationarity datum is a strong one.

The slope is quadratic in the tight direction and the two unit vectors of a line differ
by a sign, so every selection carries the same tangent functionals as the named one and
the same multipliers balance it. -/
theorem isChartStrongStationaryData_of_isChartStationaryData_of_simpleTightBlocks
    {multiplier : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset multiplier
      tightDir)
    (hsimple : ∀ activeLabel ∈ activeSet, ∀ probe : Fin size → ℝ,
      IsChartTightDirection projection weight value (activeSubset activeLabel) probe →
      ∃ scale : ℝ, probe = scale • tightDir activeLabel) :
    IsChartStrongStationaryData rank projection weight value activeSet activeSubset where
  isSymmetric := hdata.isSymmetric
  isIdempotent := hdata.isIdempotent
  hasTraceRank := hdata.hasTraceRank
  weight_pos := hdata.weight_pos
  weight_sum_one := hdata.weight_sum_one
  activeSubset_card := hdata.activeSubset_card
  exists_tightDir := fun activeLabel hmem =>
    ⟨tightDir activeLabel,
      { isUnit := hdata.tightDir_unit activeLabel hmem
        hasSupport := hdata.tightDir_support activeLabel hmem
        isTight := hdata.tightDir_isTight activeLabel hmem }⟩
  hasBalancedMultiplier_of_isChartTightSelection := by
    intro selection hselection
    have hnamedBalanced : IsChartBalancedMultiplier projection activeSet multiplier tightDir :=
      (isChartBalancedMultiplier_iff hdata.isSymmetric hdata.isIdempotent
        (size_pos_of_isChartStationaryData hdata) hdata.activeWeight_nonneg
        hdata.activeWeight_sum_one hdata.tightDir_unit).mpr
        ⟨hdata.assembly_diagonal, hdata.assembly_commutes⟩
    refine ⟨multiplier, hdata.activeWeight_nonneg, hdata.activeWeight_sum_one,
      fun directionMatrix directionWeight htangent => ?_⟩
    have hslopeEq : ∀ activeLabel ∈ activeSet,
        multiplier activeLabel
            * chartTangentSlope (selection activeLabel) directionMatrix directionWeight
          = multiplier activeLabel
            * chartTangentSlope (tightDir activeLabel) directionMatrix directionWeight := by
      intro activeLabel hmem
      obtain ⟨scale, hscale⟩ := hsimple activeLabel hmem (selection activeLabel)
        (hselection activeLabel hmem)
      have hscaleSq : scale ^ 2 = 1 := by
        have hselfProduct := (hselection activeLabel hmem).isUnit
        rw [hscale, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          hdata.tightDir_unit activeLabel hmem, mul_one] at hselfProduct
        rw [pow_two]
        exact hselfProduct
      rw [hscale, chartTangentSlope_smul, hscaleSq, one_mul]
    rw [Finset.sum_congr rfl hslopeEq]
    exact hnamedBalanced.2.2 directionMatrix directionWeight htangent

/-- **THE REDUCTION.**  At simple multiplicity the universal system and the shipped one
COINCIDE.  This is the theorem that makes the file a refinement rather than a parallel
development: everything the strong system adds lives on the multiplicity stratum, and
nothing it adds is visible where the tight eigenvalue is simple. -/
theorem isChartStrongStationaryData_iff_of_simpleTightBlocks
    {tightDir : activeIndex → (Fin size → ℝ)}
    (htight : ∀ activeLabel ∈ activeSet,
      IsChartTightDirection projection weight value (activeSubset activeLabel)
        (tightDir activeLabel))
    (hsimple : ∀ activeLabel ∈ activeSet, ∀ probe : Fin size → ℝ,
      IsChartTightDirection projection weight value (activeSubset activeLabel) probe →
      ∃ scale : ℝ, probe = scale • tightDir activeLabel) :
    IsChartStrongStationaryData rank projection weight value activeSet activeSubset
      ↔ ∃ multiplier : activeIndex → ℝ,
          IsChartStationaryData rank projection weight value activeSet activeSubset multiplier
            tightDir :=
  ⟨fun hstrong =>
    exists_multiplier_isChartStationaryData_of_isChartStrongStationaryData hstrong tightDir htight,
   fun ⟨_, hweak⟩ =>
    isChartStrongStationaryData_of_isChartStationaryData_of_simpleTightBlocks hweak hsimple⟩

/-! ## Two inherited consequences

Worked examples of the refinement, not new mathematics: they are the shipped theorems of
`Gtz.Quantitative.ChartStationary` read through
`exists_isChartStationaryData_of_isChartStrongStationaryData`. -/

/-- **THE COVERAGE LAW for the strong system**: every atom lies in some active subset. -/
theorem exists_mem_activeSubset_of_isChartStrongStationaryData
    (hdata : IsChartStrongStationaryData rank projection weight value activeSet activeSubset)
    (atomIndex : Fin size) :
    ∃ activeLabel ∈ activeSet, atomIndex ∈ activeSubset activeLabel := by
  obtain ⟨_, _, hweak⟩ := exists_isChartStationaryData_of_isChartStrongStationaryData hdata
  exact exists_mem_activeSubset_of_isChartStationaryData hweak atomIndex

/-- **THE ONE-SIDED VALUE BOUND for the strong system**: `-1/size ≤ value`. -/
theorem neg_inv_size_le_value_of_isChartStrongStationaryData
    (hdata : IsChartStrongStationaryData rank projection weight value activeSet activeSubset) :
    -((size : ℝ))⁻¹ ≤ value := by
  obtain ⟨_, _, hweak⟩ := exists_isChartStationaryData_of_isChartStrongStationaryData hdata
  exact neg_inv_size_le_value_of_isChartStationaryData hweak

/-! ## The bundle is inhabited — the tetrahedron at `(4,3)`

`Gtz.chartTetraProjection_isChartStationaryData` is the shipped weak datum: four atoms of
leverage three at uniform weight `1/4`, `value = 0`, four active triples, assembly
`I/12 + J/6`.  Its blocks are `W[C] = (3/4) I_3 - (1/4) J_3` on each triple, whose kernel
is the all-ones line — SIMPLE.  The reduction therefore upgrades it, and every theorem
above is a statement about a non-empty class.

The simplicity proof is the whole of the work: tightness at an atom of the triple reads
`3 u_c = sum u`, which forces `u` constant on the triple and hence proportional to the
named direction. -/

/-- The tetrahedron gap's action on an arbitrary probe: `3/4` of the coordinate minus a
quarter of the total. -/
theorem chartTetraGap_mulVec_apply (probe : Fin 4 → ℝ) (atomIndex : Fin 4) :
    (chartStationaryGap chartTetraProjection chartTetraWeight *ᵥ probe) atomIndex
      = 3 / 4 * probe atomIndex - (∑ otherIndex : Fin 4, probe otherIndex) / 4 := by
  have hentries : ∀ otherIndex : Fin 4,
      chartStationaryGap chartTetraProjection chartTetraWeight atomIndex otherIndex
          * probe otherIndex
        = (if atomIndex = otherIndex then (3 / 4 : ℝ) * probe otherIndex else 0)
          - probe otherIndex / 4 := by
    intro otherIndex
    rw [chartTetraGap_apply]
    by_cases hequal : atomIndex = otherIndex
    · rw [if_pos hequal, if_pos hequal]; ring
    · rw [if_neg hequal, if_neg hequal]; ring
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun otherIndex _ => hentries otherIndex, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, if_pos (Finset.mem_univ atomIndex), ← Finset.sum_div]

/-- The named tetrahedron directions are tight directions in the sense of this file. -/
theorem isChartTightDirection_chartTetraTightDir (missingIndex : Fin 4) :
    IsChartTightDirection chartTetraProjection chartTetraWeight 0
      (chartTetraSubset missingIndex) (chartTetraTightDir missingIndex) where
  isUnit :=
    chartTetraProjection_isChartStationaryData.tightDir_unit missingIndex (Finset.mem_univ _)
  hasSupport :=
    chartTetraProjection_isChartStationaryData.tightDir_support missingIndex (Finset.mem_univ _)
  isTight :=
    chartTetraProjection_isChartStationaryData.tightDir_isTight missingIndex (Finset.mem_univ _)

/-- **THE TETRAHEDRON'S TIGHT BLOCKS ARE SIMPLE.**  A tight direction of the triple that
misses `missingIndex` is a scalar multiple of the named all-ones direction.

Tightness at each atom of the triple says `3/4 u_c = (sum u)/4`, so every coordinate of
the triple equals a third of the total, and the missing coordinate vanishes by support. -/
theorem chartTetraTight_eq_smul_chartTetraTightDir (missingIndex : Fin 4) (probe : Fin 4 → ℝ)
    (htight : IsChartTightDirection chartTetraProjection chartTetraWeight 0
      (chartTetraSubset missingIndex) probe) :
    ∃ scale : ℝ, probe = scale • chartTetraTightDir missingIndex := by
  have hrootPos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hrootNe : Real.sqrt 3 ≠ 0 := ne_of_gt hrootPos
  have hmissing : probe missingIndex = 0 :=
    htight.hasSupport missingIndex (by simp [chartTetraSubset])
  have hthird : ∀ atomIndex : Fin 4, atomIndex ≠ missingIndex →
      probe atomIndex = (∑ otherIndex : Fin 4, probe otherIndex) / 3 := by
    intro atomIndex hdistinct
    have hmem : atomIndex ∈ chartTetraSubset missingIndex :=
      Finset.mem_erase.mpr ⟨hdistinct, Finset.mem_univ atomIndex⟩
    have hequation := htight.isTight atomIndex hmem
    rw [chartTetraGap_mulVec_apply, zero_mul] at hequation
    linarith
  refine ⟨(∑ otherIndex : Fin 4, probe otherIndex) * Real.sqrt 3 / 3, ?_⟩
  funext atomIndex
  by_cases hdistinct : atomIndex = missingIndex
  · simp [hdistinct, hmissing, chartTetraTightDir, chartTetraSupport]
  · simp only [chartTetraTightDir, chartTetraSupport, Pi.smul_apply, if_neg hdistinct,
      smul_eq_mul, mul_one]
    rw [hthird atomIndex hdistinct]
    field_simp

/-- **THE TETRAHEDRON IS A STRONG STATIONARITY DATUM.**  Rank three, four atoms,
`value = 0`, four active triples — the shipped weak datum upgraded through the reduction,
because every tight block is simple. -/
theorem chartTetraProjection_isChartStrongStationaryData :
    IsChartStrongStationaryData 3 chartTetraProjection chartTetraWeight 0
      (Finset.univ : Finset (Fin 4)) chartTetraSubset :=
  isChartStrongStationaryData_of_isChartStationaryData_of_simpleTightBlocks
    chartTetraProjection_isChartStationaryData
    fun missingIndex _ probe htight =>
      chartTetraTight_eq_smul_chartTetraTightDir missingIndex probe htight

/-- **The strong bundle is inhabited.**  Every theorem above is a statement about a
non-empty class — and the witness sits on the EXTREMAL locus, `value = 0`, where the chart
system restricts to the design-side quadric law. -/
theorem exists_isChartStrongStationaryData :
    ∃ (projection : Matrix (Fin 4) (Fin 4) ℝ) (weight : Fin 4 → ℝ)
      (activeSubset : Fin 4 → Finset (Fin 4)),
      IsChartStrongStationaryData 3 projection weight 0 (Finset.univ : Finset (Fin 4))
        activeSubset :=
  ⟨chartTetraProjection, chartTetraWeight, chartTetraSubset,
    chartTetraProjection_isChartStrongStationaryData⟩

end Gtz
