/-
# The COVERING form of the chart's first-order condition

The geometric face of `Gtz.Quantitative.ChartStrongStationary`.  That file states the
universal-selection condition as an EXISTENTIAL over multipliers nested inside a UNIVERSAL
over selections of unit tight directions.  Exchanging the two quantifiers turns it into a
statement about closed convex cones in the tangent space:

    the cones `S_C`, one per active block, COVER the tangent space.

This file defines the cones and proves the exchange in both directions.  Nothing here is
new mathematics — it is the same condition seen from the other side — but the two sides
are useful for different jobs, and the exchange is where the shipped Gordan alternative
does its work.

## The cones

For an active block `C` the cone is

    S_C = { d tangent : the compression of `Wdot(d)` to the tight eigenspace of `C` is psd }.

It is written here WITHOUT a basis: `0 ≤ v ⟨Wdot(d) v⟩` for EVERY tight vector `v` of the
block.  For any orthonormal basis `Q_C` of the eigenspace that is exactly
`Q_C^T Wdot(d) Q_C ⪰ 0`, and it avoids the submatrix reindexing a literal `Q_C` would
force — the same reason `Gtz.Quantitative.ChartStationary` phrases tightness through
ambient Rayleigh quotients rather than through `Gtz.lambdaMinMat`.  That the ambient
quotient IS the block quotient is proved, not assumed:
`chartTangentSlope_eq_subset_double_sum` shows a vector supported in `C` only ever sees
the `C x C` corner of the direction.

`Gtz.IsChartTightDirection` carries a unit-length field, so its inhabitants form the unit
SPHERE of the eigenspace rather than the eigenspace.  `IsChartTightVector` is the same
predicate with that field dropped; `chartTightSubspace` bundles it as a `Submodule`, which
is what makes "compression to the eigenspace" a legitimate description of the definition.
The two readings agree —
`mem_chartTightCone_iff_forall_isChartTightDirection` — because the slope is quadratic in
the tight vector and a nonzero tight vector normalises to a tight direction.

## PROVED here

* `chartTightCone` is a `ConvexCone`, is `Pointed`, and `isClosed_chartTightCone` — a
  CLOSED CONVEX CONE.  All three rest on the same two facts: the tangent set is a submodule
  (`chartTangentSubmodule`) and the slope is a LINEAR functional of the direction
  (`chartTangentSlopeFunctional`), so the cone is a subspace met with a family of closed
  halfspaces.  Finite dimension supplies the topology and nothing else.
* `isChartTightCovering_iff_forall_hasBalancedMultiplier` — **THE QUANTIFIER EXCHANGE**,
  and the whole point of the file.  The two directions are not symmetric:

  - covering ⟹ universal balance needs **GORDAN**, through
    `Gtz.exists_isChartTangent_forall_chartTangentSlope_neg`: an unbalanced selection hands
    back a tangent direction on which every active block's slope is strictly negative, and
    covering says some cone contains that direction, which contradicts the block's own
    negative slope.
  - universal balance ⟹ covering is **DIRECT**, through
    `Gtz.not_hasBalancedMultiplier_of_forall_chartTangentSlope_neg`: a direction missed by
    every cone hands back, per block, a tight vector of strictly negative slope; normalise
    it and the resulting selection is a selection no multiplier can balance.  Pure sign
    arithmetic, no separation theorem.

* `isChartStrongStationaryData_iff_isChartTightCovering` — the bundle-level reading, with
  the chart point, the active family and the nonemptiness of each tight eigenspace as
  explicit hypotheses, because covering does NOT imply them.
* `isChartTightCovering_iff_hasBalancedMultiplier_of_simple` — **THE HALFSPACE CASE.**  At
  simple tight multiplicity each cone is the tangent space met with a single closed
  halfspace (`chartTightCone_coe_eq_inter_of_simple`), and covering by those halfspaces is
  precisely the Gordan alternative for the ONE named selection.  Composed with the sibling's
  `Gtz.isChartBalancedMultiplier_iff` that makes covering, on this stratum, the two
  stationarity equations of the shipped `Gtz.IsChartStationaryData` and nothing more.

## HONESTY

**(a) Nothing analytic is formalised, here or upstream.**  `Gtz.IsChartTangent` is a
DEFINITION whose identification with a manifold tangent space is the reader's; the chart
objective, its local minima, Danskin's theorem, the Grassmannian retraction and the
identification of the active family all stay outside Lean, exactly as in the two sibling
files.  "Covering" below is covering of the DEFINED tangent set, and a direction in no
cone is a first-order descent candidate and nothing more.

**(b) COVERING IS VACUOUS AT A BLOCK WITH NO TIGHT DIRECTION.**  If some active block's
tight eigenspace is `{0}` then its cone is the whole tangent space and covering holds for
free — `isChartTightCovering_of_forall_isChartTightVector_eq_zero` proves it, rather than
leaving it to be discovered.  That is why
`Gtz.IsChartStrongStationaryData.exists_tightDir` stays a separate field and why the
bundle-level equivalence carries it as a hypothesis.  The universal-selection condition is
vacuous on exactly the same blocks, which is why the exchange survives.

**(c) The disjunctive admissibility weakness is inherited undiminished.**  Like both
siblings this fixes an active family and cannot see that the family is not the argmax.
`Gtz.IsChartArgmaxValue` is not a hypothesis anywhere below and nothing consumes it.

**(d) No realness ingredient, and no cell is closed.**  The covering form is equivalent to
the universal-selection form, which the sibling file records as holding at all three known
complex counterexamples; an equivalent condition cannot separate the fields.

**(e) No angle, no measure.**  A solid-angle count over these very cones would give
multiplicity-profile exclusions, and its load-bearing step — that the normalised angle
depends only on the tight multiplicity — is refuted [measured, outside Lean].  No measure,
no volume and no multiplicity-profile statement appears in this file, and none may be
added to it.

## NOT here, deliberately

* No reproof of the Gordan alternative, and no second application of it.
  `Gtz.LinAlg.GordanAlternative` is imported for the reader's benefit and the separation
  itself is consumed only through the shipped descent lemma of
  `Gtz.Quantitative.ChartStrongStationary`, which already wraps it.
* No new gap, assembly, tangent or slope definition.  `Gtz.chartStationaryGap`,
  `Gtz.IsChartTangent`, `Gtz.chartTangentSlope`, `Gtz.IsChartTightDirection` and
  `Gtz.HasBalancedMultiplier` are imported and reused, so the covering form and the
  universal form are literally talking about the same objects.
* No dual cone, no polar and no Farkas certificate.  The dual side of the covering
  statement is the balanced multiplier, which the sibling file already carries.
-/
import Mathlib
import Gtz.LinAlg.GordanAlternative
import Gtz.Quantitative.ChartStrongStationary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}

/-! ## The ambient of chart directions -/

/-- **A CHART DIRECTION**: a direction for the projection paired with a direction for the
weights.  `Gtz.IsChartTangent` cuts the tangent directions out of this ambient, and the
cones below live inside it. -/
abbrev ChartDirection (size : ℕ) : Type :=
  Matrix (Fin size) (Fin size) ℝ × (Fin size → ℝ)

/-! ## The tight eigenspace of a block

`Gtz.IsChartTightDirection` carries a unit-length field, so it names the unit sphere of the
tight eigenspace.  Dropping that field leaves a LINEAR condition, and the compression of a
direction to a subspace is what the cone below is about. -/

/-- **A TIGHT VECTOR of one block**: supported inside the subset, and an eigenvector of the
chart gap at `value` read coordinatewise ON the subset.  This is
`Gtz.IsChartTightDirection` with the unit-length field dropped, so that the tight vectors
of a block form a subspace rather than its unit sphere. -/
structure IsChartTightVector (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (value : ℝ) (chosenSubset : Finset (Fin size))
    (tightVec : Fin size → ℝ) : Prop where
  /-- The vector is supported inside the subset. -/
  hasSupport : ∀ atomIndex : Fin size, atomIndex ∉ chosenSubset → tightVec atomIndex = 0
  /-- Tightness on the subset.  Nothing is asserted off it. -/
  isTight : ∀ atomIndex ∈ chosenSubset,
    (chartStationaryGap projection weight *ᵥ tightVec) atomIndex = value * tightVec atomIndex

variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ} {value : ℝ}

/-- Every unit tight direction is a tight vector — the unit field is simply forgotten. -/
theorem isChartTightVector_of_isChartTightDirection {chosenSubset : Finset (Fin size)}
    {tightVec : Fin size → ℝ}
    (htight : IsChartTightDirection projection weight value chosenSubset tightVec) :
    IsChartTightVector projection weight value chosenSubset tightVec where
  hasSupport := htight.hasSupport
  isTight := htight.isTight

/-- The zero vector is tight, so the cone's defining condition is never empty of
instances — and never, on its own, informative. -/
theorem isChartTightVector_zero (chosenSubset : Finset (Fin size)) :
    IsChartTightVector projection weight value chosenSubset 0 where
  hasSupport := fun _ _ => rfl
  isTight := fun _ _ => by
    rw [Matrix.mulVec_zero]
    exact (mul_zero value).symm

theorem isChartTightVector_add {chosenSubset : Finset (Fin size)}
    {firstVec secondVec : Fin size → ℝ}
    (hfirst : IsChartTightVector projection weight value chosenSubset firstVec)
    (hsecond : IsChartTightVector projection weight value chosenSubset secondVec) :
    IsChartTightVector projection weight value chosenSubset (firstVec + secondVec) where
  hasSupport := fun atomIndex hnotMem => by
    rw [Pi.add_apply, hfirst.hasSupport atomIndex hnotMem, hsecond.hasSupport atomIndex hnotMem,
      add_zero]
  isTight := fun atomIndex hmem => by
    rw [Matrix.mulVec_add, Pi.add_apply, hfirst.isTight atomIndex hmem,
      hsecond.isTight atomIndex hmem, Pi.add_apply, mul_add]

theorem isChartTightVector_smul {chosenSubset : Finset (Fin size)} (scale : ℝ)
    {tightVec : Fin size → ℝ}
    (htight : IsChartTightVector projection weight value chosenSubset tightVec) :
    IsChartTightVector projection weight value chosenSubset (scale • tightVec) where
  hasSupport := fun atomIndex hnotMem => by
    rw [Pi.smul_apply, htight.hasSupport atomIndex hnotMem, smul_zero]
  isTight := fun atomIndex hmem => by
    rw [Matrix.mulVec_smul, Pi.smul_apply, htight.isTight atomIndex hmem, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul]
    ring

/-- **THE TIGHT EIGENSPACE**, bundled.  This is what "compression to the tight eigenspace"
below is a compression to, and the only reason it is written down: a predicate called an
eigenspace should be provably a subspace. -/
def chartTightSubspace (projection : Matrix (Fin size) (Fin size) ℝ) (weight : Fin size → ℝ)
    (value : ℝ) (chosenSubset : Finset (Fin size)) : Submodule ℝ (Fin size → ℝ) where
  carrier := {tightVec | IsChartTightVector projection weight value chosenSubset tightVec}
  zero_mem' := isChartTightVector_zero chosenSubset
  add_mem' := fun hfirst hsecond => isChartTightVector_add hfirst hsecond
  smul_mem' := fun scale _ htight => isChartTightVector_smul scale htight

theorem mem_chartTightSubspace_iff {chosenSubset : Finset (Fin size)} {tightVec : Fin size → ℝ} :
    tightVec ∈ chartTightSubspace projection weight value chosenSubset
      ↔ IsChartTightVector projection weight value chosenSubset tightVec := Iff.rfl

/-- **A NONZERO TIGHT VECTOR NORMALISES to a tight direction**, by a strictly positive
scale.  This is the whole content of the passage between the subspace reading of the cone
and the unit-sphere reading the sibling file's selections use. -/
theorem exists_pos_isChartTightDirection_smul_of_isChartTightVector
    {chosenSubset : Finset (Fin size)} {tightVec : Fin size → ℝ}
    (htight : IsChartTightVector projection weight value chosenSubset tightVec)
    (hnonzero : tightVec ≠ 0) :
    ∃ scale : ℝ, 0 < scale
      ∧ IsChartTightDirection projection weight value chosenSubset (scale • tightVec) := by
  have hnonneg : 0 ≤ tightVec ⬝ᵥ tightVec := by
    rw [dotProduct_self_eq_sum_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpositive : 0 < tightVec ⬝ᵥ tightVec := by
    refine lt_of_le_of_ne hnonneg fun hvanish => hnonzero ?_
    have hsquares : ∑ atomIndex : Fin size, tightVec atomIndex ^ 2 = 0 := by
      rw [← dotProduct_self_eq_sum_sq, ← hvanish]
    funext atomIndex
    have hentry := (Finset.sum_eq_zero_iff_of_nonneg
      (fun otherIndex _ => sq_nonneg (tightVec otherIndex))).mp hsquares atomIndex
      (Finset.mem_univ atomIndex)
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hentry
  have hrootPos : 0 < Real.sqrt (tightVec ⬝ᵥ tightVec) := Real.sqrt_pos.mpr hpositive
  refine ⟨(Real.sqrt (tightVec ⬝ᵥ tightVec))⁻¹, inv_pos.mpr hrootPos, ?_,
    (isChartTightVector_smul _ htight).hasSupport,
    (isChartTightVector_smul _ htight).isTight⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ← mul_inv, ← pow_two, Real.sq_sqrt hnonneg]
  exact inv_mul_cancel₀ (ne_of_gt hpositive)

/-! ## The slope is a LINEAR functional of the direction

`Gtz.chartTangentSlope` is quadratic in the tight vector — that is
`Gtz.chartTangentSlope_smul` — and LINEAR in the direction, which is what makes the cones
below convex and closed.  The gap map is affine, so its differential is itself, and the
three lemmas here are that observation carried through the definition. -/

/-- The slope, expanded into the double sum over the gap's entries.  This is the form the
block-restriction lemma below cuts down. -/
theorem chartTangentSlope_eq_double_sum (tightVec : Fin size → ℝ)
    (directionMatrix : Matrix (Fin size) (Fin size) ℝ) (directionWeight : Fin size → ℝ) :
    chartTangentSlope tightVec directionMatrix directionWeight
      = ∑ rowIndex : Fin size, ∑ colIndex : Fin size,
          tightVec rowIndex * chartStationaryGap directionMatrix directionWeight rowIndex colIndex
            * tightVec colIndex := by
  rw [chartTangentSlope, dotProduct_mulVec_eq_sum_sum]

/-- **THE COMPRESSION IS LITERALLY THE BLOCK'S.**  A vector supported in the subset reads
only the `C x C` corner of the direction, so the ambient Rayleigh quotient used throughout
this file IS the quotient of the compressed block.  Without this the phrase "compression
to the tight eigenspace" would be a description of the intended meaning rather than of the
definition. -/
theorem chartTangentSlope_eq_subset_double_sum {chosenSubset : Finset (Fin size)}
    {tightVec : Fin size → ℝ}
    (hsupport : ∀ atomIndex : Fin size, atomIndex ∉ chosenSubset → tightVec atomIndex = 0)
    (directionMatrix : Matrix (Fin size) (Fin size) ℝ) (directionWeight : Fin size → ℝ) :
    chartTangentSlope tightVec directionMatrix directionWeight
      = ∑ rowIndex ∈ chosenSubset, ∑ colIndex ∈ chosenSubset,
          tightVec rowIndex * chartStationaryGap directionMatrix directionWeight rowIndex colIndex
            * tightVec colIndex := by
  rw [chartTangentSlope_eq_double_sum]
  refine (Finset.sum_subset (Finset.subset_univ chosenSubset)
    fun rowIndex _ hnotMem => ?_).symm.trans (Finset.sum_congr rfl fun rowIndex _ => ?_)
  · refine Finset.sum_eq_zero fun colIndex _ => ?_
    rw [hsupport rowIndex hnotMem, zero_mul, zero_mul]
  · refine (Finset.sum_subset (Finset.subset_univ chosenSubset) fun colIndex _ hnotMem => ?_).symm
    rw [hsupport colIndex hnotMem, mul_zero]

theorem chartStationaryGap_add (firstMatrix secondMatrix : Matrix (Fin size) (Fin size) ℝ)
    (firstWeight secondWeight : Fin size → ℝ) :
    chartStationaryGap (firstMatrix + secondMatrix) (firstWeight + secondWeight)
      = chartStationaryGap firstMatrix firstWeight
        + chartStationaryGap secondMatrix secondWeight := by
  rw [chartStationaryGap, chartStationaryGap, chartStationaryGap,
    show firstWeight + secondWeight = fun atomIndex => firstWeight atomIndex
      + secondWeight atomIndex from rfl, ← Matrix.diagonal_add]
  abel

theorem chartStationaryGap_smul (scale : ℝ) (directionMatrix : Matrix (Fin size) (Fin size) ℝ)
    (directionWeight : Fin size → ℝ) :
    chartStationaryGap (scale • directionMatrix) (scale • directionWeight)
      = scale • chartStationaryGap directionMatrix directionWeight := by
  rw [chartStationaryGap, chartStationaryGap, Matrix.diagonal_smul, smul_sub]

theorem chartTangentSlope_add_direction (tightVec : Fin size → ℝ)
    (firstMatrix secondMatrix : Matrix (Fin size) (Fin size) ℝ)
    (firstWeight secondWeight : Fin size → ℝ) :
    chartTangentSlope tightVec (firstMatrix + secondMatrix) (firstWeight + secondWeight)
      = chartTangentSlope tightVec firstMatrix firstWeight
        + chartTangentSlope tightVec secondMatrix secondWeight := by
  rw [chartTangentSlope, chartTangentSlope, chartTangentSlope, chartStationaryGap_add,
    Matrix.add_mulVec, dotProduct_add]

theorem chartTangentSlope_smul_direction (scale : ℝ) (tightVec : Fin size → ℝ)
    (directionMatrix : Matrix (Fin size) (Fin size) ℝ) (directionWeight : Fin size → ℝ) :
    chartTangentSlope tightVec (scale • directionMatrix) (scale • directionWeight)
      = scale * chartTangentSlope tightVec directionMatrix directionWeight := by
  rw [chartTangentSlope, chartTangentSlope, chartStationaryGap_smul, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]

/-- The zero tight vector has zero slope, in every direction.  This is why the cone's
condition says nothing at a block whose tight eigenspace is trivial. -/
theorem chartTangentSlope_zero_vector (directionMatrix : Matrix (Fin size) (Fin size) ℝ)
    (directionWeight : Fin size → ℝ) :
    chartTangentSlope (0 : Fin size → ℝ) directionMatrix directionWeight = 0 := by
  rw [chartTangentSlope, zero_dotProduct]

/-- Every tight vector has zero slope along the zero direction, which is what makes the
cones pointed. -/
theorem chartTangentSlope_zero_direction (tightVec : Fin size → ℝ) :
    chartTangentSlope tightVec 0 0 = 0 := by
  rw [chartTangentSlope, chartStationaryGap,
    show Matrix.diagonal (0 : Fin size → ℝ) = 0 from Matrix.diagonal_zero, sub_zero,
    Matrix.zero_mulVec, dotProduct_zero]

/-- **THE SLOPE AS A CONTINUOUS LINEAR FUNCTIONAL** of the chart direction.  Everything
topological below — closedness of the cone — factors through this map and the finite
dimension of the ambient. -/
def chartTangentSlopeFunctional (tightVec : Fin size → ℝ) : ChartDirection size →ₗ[ℝ] ℝ where
  toFun := fun direction => chartTangentSlope tightVec direction.1 direction.2
  map_add' := fun firstDirection secondDirection =>
    chartTangentSlope_add_direction tightVec firstDirection.1 secondDirection.1
      firstDirection.2 secondDirection.2
  map_smul' := fun scale direction =>
    chartTangentSlope_smul_direction scale tightVec direction.1 direction.2

theorem chartTangentSlopeFunctional_apply (tightVec : Fin size → ℝ)
    (direction : ChartDirection size) :
    chartTangentSlopeFunctional tightVec direction
      = chartTangentSlope tightVec direction.1 direction.2 := rfl

/-! ## The tangent space as a submodule

`Gtz.IsChartTangent` is cut out by linear equations — symmetry, two vanishing blocks and a
vanishing weight sum — so the tangent directions form a subspace, and in finite dimension a
closed one.  Nothing here claims it is the tangent space of a manifold; see honesty (a). -/

theorem isChartTangent_zero (projection : Matrix (Fin size) (Fin size) ℝ) :
    IsChartTangent projection 0 0 where
  isSymmetric := Matrix.transpose_zero
  rangeBlock_eq_zero := by rw [Matrix.mul_zero, Matrix.zero_mul]
  kernelBlock_eq_zero := by rw [Matrix.mul_zero, Matrix.zero_mul]
  weight_sum_zero := by simp

theorem isChartTangent_add {firstMatrix secondMatrix : Matrix (Fin size) (Fin size) ℝ}
    {firstWeight secondWeight : Fin size → ℝ}
    (hfirst : IsChartTangent projection firstMatrix firstWeight)
    (hsecond : IsChartTangent projection secondMatrix secondWeight) :
    IsChartTangent projection (firstMatrix + secondMatrix) (firstWeight + secondWeight) where
  isSymmetric := by
    rw [Matrix.transpose_add, hfirst.isSymmetric, hsecond.isSymmetric]
  rangeBlock_eq_zero := by
    rw [Matrix.mul_add, Matrix.add_mul, hfirst.rangeBlock_eq_zero, hsecond.rangeBlock_eq_zero,
      add_zero]
  kernelBlock_eq_zero := by
    rw [Matrix.mul_add, Matrix.add_mul, hfirst.kernelBlock_eq_zero, hsecond.kernelBlock_eq_zero,
      add_zero]
  weight_sum_zero := by
    rw [show firstWeight + secondWeight = fun atomIndex => firstWeight atomIndex
      + secondWeight atomIndex from rfl, Finset.sum_add_distrib, hfirst.weight_sum_zero,
      hsecond.weight_sum_zero, add_zero]

theorem isChartTangent_smul (scale : ℝ) {directionMatrix : Matrix (Fin size) (Fin size) ℝ}
    {directionWeight : Fin size → ℝ}
    (htangent : IsChartTangent projection directionMatrix directionWeight) :
    IsChartTangent projection (scale • directionMatrix) (scale • directionWeight) where
  isSymmetric := by rw [Matrix.transpose_smul, htangent.isSymmetric]
  rangeBlock_eq_zero := by
    rw [Matrix.mul_smul, Matrix.smul_mul, htangent.rangeBlock_eq_zero, smul_zero]
  kernelBlock_eq_zero := by
    rw [Matrix.mul_smul, Matrix.smul_mul, htangent.kernelBlock_eq_zero, smul_zero]
  weight_sum_zero := by
    rw [show scale • directionWeight = fun atomIndex => scale * directionWeight atomIndex from rfl,
      ← Finset.mul_sum, htangent.weight_sum_zero, mul_zero]

/-- **THE TANGENT DIRECTIONS, bundled as a subspace.**  Its only job is to supply
closedness and convexity to the cones; the identification with a manifold tangent space is
not made anywhere. -/
def chartTangentSubmodule (projection : Matrix (Fin size) (Fin size) ℝ) :
    Submodule ℝ (ChartDirection size) where
  carrier := {direction | IsChartTangent projection direction.1 direction.2}
  zero_mem' := isChartTangent_zero projection
  add_mem' := fun hfirst hsecond => isChartTangent_add hfirst hsecond
  smul_mem' := fun scale _ htangent => isChartTangent_smul scale htangent

theorem mem_chartTangentSubmodule_iff {direction : ChartDirection size} :
    direction ∈ chartTangentSubmodule projection
      ↔ IsChartTangent projection direction.1 direction.2 := Iff.rfl

theorem isClosed_chartTangentSubmodule (projection : Matrix (Fin size) (Fin size) ℝ) :
    IsClosed (chartTangentSubmodule projection : Set (ChartDirection size)) :=
  (chartTangentSubmodule projection).closed_of_finiteDimensional

/-! ## The cones -/

/-- **THE CONE OF A BLOCK**: the tangent directions whose compression to the block's tight
eigenspace is positive semidefinite, written basis-free as nonnegativity of the Rayleigh
quotient at every tight vector.

This is `S_C` of the covering criterion.  At simple tight multiplicity it is the tangent
space met with a single halfspace — `chartTightCone_coe_eq_inter_of_simple`.  At higher
multiplicity it is cut by one inequality per tight vector rather than by one in total; that
those extra inequalities genuinely bite is measured, outside Lean, and is not proved
here. -/
def chartTightCone (projection : Matrix (Fin size) (Fin size) ℝ) (weight : Fin size → ℝ)
    (value : ℝ) (chosenSubset : Finset (Fin size)) : ConvexCone ℝ (ChartDirection size) where
  carrier := {direction | IsChartTangent projection direction.1 direction.2
    ∧ ∀ tightVec : Fin size → ℝ,
        IsChartTightVector projection weight value chosenSubset tightVec →
        0 ≤ chartTangentSlope tightVec direction.1 direction.2}
  smul_mem' := fun scale hscale direction hmem =>
    ⟨isChartTangent_smul scale hmem.1, fun tightVec htight => by
      rw [Prod.smul_fst, Prod.smul_snd, chartTangentSlope_smul_direction]
      exact mul_nonneg hscale.le (hmem.2 tightVec htight)⟩
  add_mem' := fun firstDirection hfirst secondDirection hsecond =>
    ⟨isChartTangent_add hfirst.1 hsecond.1, fun tightVec htight => by
      rw [Prod.fst_add, Prod.snd_add, chartTangentSlope_add_direction]
      exact add_nonneg (hfirst.2 tightVec htight) (hsecond.2 tightVec htight)⟩

theorem mem_chartTightCone_iff {chosenSubset : Finset (Fin size)}
    {direction : ChartDirection size} :
    direction ∈ chartTightCone projection weight value chosenSubset
      ↔ IsChartTangent projection direction.1 direction.2
        ∧ ∀ tightVec : Fin size → ℝ,
            IsChartTightVector projection weight value chosenSubset tightVec →
            0 ≤ chartTangentSlope tightVec direction.1 direction.2 := Iff.rfl

/-- The cone sits inside the tangent space, so covering can only ever be an equality with
it and never an overshoot. -/
theorem chartTightCone_coe_subset_chartTangentSubmodule (chosenSubset : Finset (Fin size)) :
    (chartTightCone projection weight value chosenSubset : Set (ChartDirection size))
      ⊆ (chartTangentSubmodule projection : Set (ChartDirection size)) :=
  fun _ hmem => hmem.1

/-- **THE CONE IS POINTED**: the zero direction lies in it. -/
theorem pointed_chartTightCone (chosenSubset : Finset (Fin size)) :
    (chartTightCone projection weight value chosenSubset).Pointed :=
  ⟨isChartTangent_zero projection, fun tightVec _ => by
    show 0 ≤ chartTangentSlope tightVec 0 0
    exact le_of_eq (chartTangentSlope_zero_direction tightVec).symm⟩

/-- **THE CONE IS CONVEX** — read off the bundling, which is where the cone axioms were
discharged. -/
theorem convex_chartTightCone (chosenSubset : Finset (Fin size)) :
    Convex ℝ (chartTightCone projection weight value chosenSubset : Set (ChartDirection size)) :=
  (chartTightCone projection weight value chosenSubset).convex

/-- **THE CONE IS CLOSED**: a subspace met with a family of closed halfspaces, one per tight
vector.  The slope is linear in the direction and the ambient is finite-dimensional, so
both ingredients are automatic. -/
theorem isClosed_chartTightCone (chosenSubset : Finset (Fin size)) :
    IsClosed (chartTightCone projection weight value chosenSubset : Set (ChartDirection size)) := by
  have hdecompose :
      (chartTightCone projection weight value chosenSubset : Set (ChartDirection size))
        = (chartTangentSubmodule projection : Set (ChartDirection size))
          ∩ ⋂ tightVec ∈ {probe : Fin size → ℝ |
              IsChartTightVector projection weight value chosenSubset probe},
            chartTangentSlopeFunctional tightVec ⁻¹' Set.Ici (0 : ℝ) := by
    ext direction
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_Ici, Set.mem_setOf_eq,
      SetLike.mem_coe, mem_chartTangentSubmodule_iff, mem_chartTightCone_iff,
      chartTangentSlopeFunctional_apply]
  rw [hdecompose]
  refine (isClosed_chartTangentSubmodule projection).inter (isClosed_iInter fun tightVec => ?_)
  exact isClosed_iInter fun _ =>
    IsClosed.preimage (chartTangentSlopeFunctional tightVec).continuous_of_finiteDimensional
      isClosed_Ici

/-- **THE UNIT-SPHERE READING of cone membership.**  Testing the compression on the unit
tight DIRECTIONS the sibling file's selections range over gives the same cone as testing it
on the whole eigenspace: the slope is quadratic in the tight vector, the zero vector has
zero slope, and every other tight vector normalises.

This is the bridge between the two vocabularies, and everything below crosses it. -/
theorem mem_chartTightCone_iff_forall_isChartTightDirection {chosenSubset : Finset (Fin size)}
    {direction : ChartDirection size} :
    direction ∈ chartTightCone projection weight value chosenSubset
      ↔ IsChartTangent projection direction.1 direction.2
        ∧ ∀ tightVec : Fin size → ℝ,
            IsChartTightDirection projection weight value chosenSubset tightVec →
            0 ≤ chartTangentSlope tightVec direction.1 direction.2 := by
  rw [mem_chartTightCone_iff]
  refine and_congr_right fun _ => ⟨fun hall tightVec htight =>
    hall tightVec (isChartTightVector_of_isChartTightDirection htight), fun hunitOnly => ?_⟩
  intro tightVec htight
  by_cases hzero : tightVec = 0
  · rw [hzero, chartTangentSlope_zero_vector]
  · obtain ⟨scale, hscalePos, hscaled⟩ :=
      exists_pos_isChartTightDirection_smul_of_isChartTightVector htight hzero
    have hscaledNonneg := hunitOnly (scale • tightVec) hscaled
    rw [chartTangentSlope_smul] at hscaledNonneg
    rcases le_or_gt 0 (chartTangentSlope tightVec direction.1 direction.2) with hnonneg | hnegative
    · exact hnonneg
    · have hproduct : scale ^ 2 * chartTangentSlope tightVec direction.1 direction.2 < 0 :=
        mul_neg_of_pos_of_neg (pow_pos hscalePos 2) hnegative
      linarith

/-! ## The covering condition -/

/-- **THE COVERING CONDITION**: every tangent direction lies in the cone of some active
block.

This is the quantifier-exchanged form of the universal-selection field of
`Gtz.IsChartStrongStationaryData`, and `isChartTightCovering_iff_forall_hasBalancedMultiplier`
is the exchange.  Read as a statement about sets it says the cones cover the tangent space,
which is `isChartTightCovering_iff_iUnion_eq`. -/
def IsChartTightCovering (projection : Matrix (Fin size) (Fin size) ℝ) (weight : Fin size → ℝ)
    (value : ℝ) (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin size)) : Prop :=
  ∀ direction : ChartDirection size, IsChartTangent projection direction.1 direction.2 →
    ∃ activeLabel ∈ activeSet,
      direction ∈ chartTightCone projection weight value (activeSubset activeLabel)

variable {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}

/-- **THE SET FORM**: covering says exactly that the union of the cones IS the tangent
space.  One inclusion is `chartTightCone_coe_subset_chartTangentSubmodule` and holds
always; the other is the condition. -/
theorem isChartTightCovering_iff_iUnion_eq :
    IsChartTightCovering projection weight value activeSet activeSubset
      ↔ ⋃ activeLabel ∈ activeSet,
          (chartTightCone projection weight value (activeSubset activeLabel) :
            Set (ChartDirection size))
        = (chartTangentSubmodule projection : Set (ChartDirection size)) := by
  constructor
  · intro hcovering
    refine Set.Subset.antisymm ?_ fun direction htangent => ?_
    · refine Set.iUnion_subset fun activeLabel => Set.iUnion_subset fun _ => ?_
      exact chartTightCone_coe_subset_chartTangentSubmodule (activeSubset activeLabel)
    · obtain ⟨activeLabel, hmem, hcone⟩ := hcovering direction htangent
      exact Set.mem_biUnion hmem hcone
  · intro hunion direction htangent
    have hmem : direction ∈ ⋃ activeLabel ∈ activeSet,
        (chartTightCone projection weight value (activeSubset activeLabel) :
          Set (ChartDirection size)) := by
      rw [hunion]
      exact htangent
    obtain ⟨activeLabel, hlabel, hcone⟩ := Set.mem_iUnion₂.mp hmem
    exact ⟨activeLabel, hlabel, hcone⟩

/-- **COVERING IS VACUOUS AT A BLOCK WITH NO TIGHT DIRECTION.**  A block whose tight
eigenspace is trivial imposes no condition at all, so its cone is the whole tangent space
and covering holds for free.

This is why `Gtz.IsChartStrongStationaryData.exists_tightDir` is a field of the bundle and
a hypothesis of the equivalence below, and not a consequence of covering.  The
universal-selection form is vacuous on exactly the same blocks — no selection satisfies its
antecedent — which is why the exchange survives the degeneracy. -/
theorem isChartTightCovering_of_forall_isChartTightVector_eq_zero {emptyLabel : activeIndex}
    (hmem : emptyLabel ∈ activeSet)
    (hzero : ∀ tightVec : Fin size → ℝ,
      IsChartTightVector projection weight value (activeSubset emptyLabel) tightVec →
      tightVec = 0) :
    IsChartTightCovering projection weight value activeSet activeSubset :=
  fun direction htangent => ⟨emptyLabel, hmem, htangent, fun tightVec htight => by
    rw [hzero tightVec htight, chartTangentSlope_zero_vector]⟩

/-! ## The quantifier exchange -/

/-- **COVERING IMPLIES UNIVERSAL BALANCE — the direction that needs GORDAN.**

If some selection admitted no balanced multiplier then
`Gtz.exists_isChartTangent_forall_chartTangentSlope_neg` — the shipped descent lemma, which
is the Gordan alternative applied to the Riesz vectors of the tangent functionals — would
return a tangent direction on which EVERY active block's tight slope is strictly negative.
Covering puts that direction in some active cone, whose defining condition is that the
block's slope there is nonnegative. -/
theorem forall_hasBalancedMultiplier_of_isChartTightCovering
    (hsymmetric : projectionᵀ = projection) (hidempotent : projection * projection = projection)
    (hsizePos : 0 < size)
    (hcovering : IsChartTightCovering projection weight value activeSet activeSubset)
    (selection : activeIndex → (Fin size → ℝ))
    (hselection : ∀ activeLabel ∈ activeSet,
      IsChartTightDirection projection weight value (activeSubset activeLabel)
        (selection activeLabel)) :
    HasBalancedMultiplier projection activeSet selection := by
  by_contra hunbalanced
  obtain ⟨directionMatrix, directionWeight, htangent, hnegative⟩ :=
    exists_isChartTangent_forall_chartTangentSlope_neg hsymmetric hidempotent hsizePos
      (fun activeLabel hmem => (hselection activeLabel hmem).isUnit) hunbalanced
  obtain ⟨activeLabel, hmem, hcone⟩ := hcovering (directionMatrix, directionWeight) htangent
  have hnonneg := hcone.2 (selection activeLabel)
    (isChartTightVector_of_isChartTightDirection (hselection activeLabel hmem))
  exact absurd hnonneg (not_le.mpr (hnegative activeLabel hmem))

/-- **UNIVERSAL BALANCE IMPLIES COVERING — the DIRECT direction.**

A tangent direction outside every active cone hands back, for each active block, a tight
vector of strictly negative slope.  Such a vector is nonzero, so it normalises to a unit
tight direction of the same sign, and the resulting selection is one that
`Gtz.not_hasBalancedMultiplier_of_forall_chartTangentSlope_neg` — pure sign arithmetic on a
convex combination, no separation theorem — forbids any multiplier from balancing. -/
theorem isChartTightCovering_of_forall_hasBalancedMultiplier
    (hbalance : ∀ selection : activeIndex → (Fin size → ℝ),
      (∀ activeLabel ∈ activeSet,
        IsChartTightDirection projection weight value (activeSubset activeLabel)
          (selection activeLabel)) →
      HasBalancedMultiplier projection activeSet selection) :
    IsChartTightCovering projection weight value activeSet activeSubset := by
  classical
  intro direction htangent
  by_contra hmissed
  have hnotCone : ∀ activeLabel : activeIndex, activeLabel ∈ activeSet →
      direction ∉ chartTightCone projection weight value (activeSubset activeLabel) :=
    fun activeLabel hmem hcone => hmissed ⟨activeLabel, hmem, hcone⟩
  have hwitness : ∀ activeLabel : activeIndex, activeLabel ∈ activeSet →
      ∃ tightVec : Fin size → ℝ,
        IsChartTightDirection projection weight value (activeSubset activeLabel) tightVec
          ∧ chartTangentSlope tightVec direction.1 direction.2 < 0 := by
    intro activeLabel hmem
    have hslopeFails : ∃ rawVec : Fin size → ℝ,
        IsChartTightVector projection weight value (activeSubset activeLabel) rawVec
          ∧ chartTangentSlope rawVec direction.1 direction.2 < 0 := by
      by_contra hnoWitness
      refine hnotCone activeLabel hmem (mem_chartTightCone_iff.mpr
        ⟨htangent, fun tightVec htight => ?_⟩)
      rcases le_or_gt 0 (chartTangentSlope tightVec direction.1 direction.2) with
        hnonneg | hnegative
      · exact hnonneg
      · exact absurd ⟨tightVec, htight, hnegative⟩ hnoWitness
    obtain ⟨rawVec, hrawTight, hrawNegative⟩ := hslopeFails
    have hrawNonzero : rawVec ≠ 0 := by
      intro hzero
      rw [hzero, chartTangentSlope_zero_vector] at hrawNegative
      exact lt_irrefl 0 hrawNegative
    obtain ⟨scale, hscalePos, hscaled⟩ :=
      exists_pos_isChartTightDirection_smul_of_isChartTightVector hrawTight hrawNonzero
    refine ⟨scale • rawVec, hscaled, ?_⟩
    rw [chartTangentSlope_smul]
    exact mul_neg_of_pos_of_neg (pow_pos hscalePos 2) hrawNegative
  choose pickTightDir hpickTight hpickNegative using hwitness
  set selection : activeIndex → (Fin size → ℝ) := fun activeLabel =>
    if hmem : activeLabel ∈ activeSet then pickTightDir activeLabel hmem else 0 with hselectionDef
  have hselectionTight : ∀ activeLabel ∈ activeSet,
      IsChartTightDirection projection weight value (activeSubset activeLabel)
        (selection activeLabel) := by
    intro activeLabel hmem
    simpa only [hselectionDef, dif_pos hmem] using hpickTight activeLabel hmem
  have hselectionNegative : ∀ activeLabel ∈ activeSet,
      chartTangentSlope (selection activeLabel) direction.1 direction.2 < 0 := by
    intro activeLabel hmem
    simpa only [hselectionDef, dif_pos hmem] using hpickNegative activeLabel hmem
  exact not_hasBalancedMultiplier_of_forall_chartTangentSlope_neg htangent hselectionNegative
    (hbalance selection hselectionTight)

/-- **THE QUANTIFIER EXCHANGE.**  Covering by the cones and the universal-selection
condition of `Gtz.Quantitative.ChartStrongStationary` are the SAME condition.

Left to right is Gordan; right to left is direct.  Both directions are proved above, and
neither is an instance of the other. -/
theorem isChartTightCovering_iff_forall_hasBalancedMultiplier
    (hsymmetric : projectionᵀ = projection) (hidempotent : projection * projection = projection)
    (hsizePos : 0 < size) :
    IsChartTightCovering projection weight value activeSet activeSubset
      ↔ ∀ selection : activeIndex → (Fin size → ℝ),
          (∀ activeLabel ∈ activeSet,
            IsChartTightDirection projection weight value (activeSubset activeLabel)
              (selection activeLabel)) →
          HasBalancedMultiplier projection activeSet selection :=
  ⟨fun hcovering => forall_hasBalancedMultiplier_of_isChartTightCovering hsymmetric hidempotent
      hsizePos hcovering,
   isChartTightCovering_of_forall_hasBalancedMultiplier⟩

/-- **THE EXCHANGE IN THE FORM IT IS USUALLY QUOTED**: the universal-selection condition
holds exactly when the UNION of the cones IS the tangent space.

A composite of `isChartTightCovering_iff_iUnion_eq` and the exchange, stated on its own
because it is the sentence the covering criterion is normally written as, and because a
composite nobody writes down is a composite nobody checks. -/
theorem iUnion_chartTightCone_eq_iff_forall_hasBalancedMultiplier
    (hsymmetric : projectionᵀ = projection) (hidempotent : projection * projection = projection)
    (hsizePos : 0 < size) :
    ⋃ activeLabel ∈ activeSet,
        (chartTightCone projection weight value (activeSubset activeLabel) :
          Set (ChartDirection size))
      = (chartTangentSubmodule projection : Set (ChartDirection size))
      ↔ ∀ selection : activeIndex → (Fin size → ℝ),
          (∀ activeLabel ∈ activeSet,
            IsChartTightDirection projection weight value (activeSubset activeLabel)
              (selection activeLabel)) →
          HasBalancedMultiplier projection activeSet selection :=
  isChartTightCovering_iff_iUnion_eq.symm.trans
    (isChartTightCovering_iff_forall_hasBalancedMultiplier hsymmetric hidempotent hsizePos)

/-! ## The bundle-level reading -/

variable {rank : ℕ}

/-- **A STRONG STATIONARITY DATUM COVERS.**  Its universal-selection field is the covering
condition read through the exchange. -/
theorem isChartTightCovering_of_isChartStrongStationaryData
    (hdata : IsChartStrongStationaryData rank projection weight value activeSet activeSubset) :
    IsChartTightCovering projection weight value activeSet activeSubset :=
  isChartTightCovering_of_forall_hasBalancedMultiplier
    hdata.hasBalancedMultiplier_of_isChartTightSelection

/-- **The size is positive**, from the weights alone: an empty index set carries no weights,
so their sum would be zero rather than one.  This is `Gtz.size_pos_of_isChartStrongStationaryData`
with the whole bundle traded for the one field it uses, which is what lets the equivalence
below drop `0 < size` from its hypotheses. -/
theorem size_pos_of_weight_sum_eq_one
    (hweightSum : ∑ atomIndex : Fin size, weight atomIndex = 1) : 0 < size := by
  by_contra hnonpositive
  have hsizeZero : size = 0 := Nat.le_zero.mp (not_lt.mp hnonpositive)
  subst hsizeZero
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hweightSum
  exact absurd hweightSum (by norm_num)

/-- **COVERING REBUILDS THE DATUM**, given the chart point, the active family and the
nonemptiness of each tight eigenspace.

Those seven hypotheses are exactly the fields covering does NOT see: covering is a
statement about cones and says nothing about the chart being a projection, about the
weights, about the cardinality of the active subsets, or about any block carrying a tight
direction at all — see `isChartTightCovering_of_forall_isChartTightVector_eq_zero`. -/
theorem isChartStrongStationaryData_of_isChartTightCovering
    (hsymmetric : projectionᵀ = projection) (hidempotent : projection * projection = projection)
    (htraceRank : Matrix.trace projection = (rank : ℝ))
    (hweightPos : ∀ atomIndex : Fin size, 0 < weight atomIndex)
    (hweightSum : ∑ atomIndex : Fin size, weight atomIndex = 1)
    (hcard : ∀ activeLabel ∈ activeSet, (activeSubset activeLabel).card = rank)
    (hexistsTight : ∀ activeLabel ∈ activeSet, ∃ tightVec : Fin size → ℝ,
      IsChartTightDirection projection weight value (activeSubset activeLabel) tightVec)
    (hcovering : IsChartTightCovering projection weight value activeSet activeSubset) :
    IsChartStrongStationaryData rank projection weight value activeSet activeSubset where
  isSymmetric := hsymmetric
  isIdempotent := hidempotent
  hasTraceRank := htraceRank
  weight_pos := hweightPos
  weight_sum_one := hweightSum
  activeSubset_card := hcard
  exists_tightDir := hexistsTight
  hasBalancedMultiplier_of_isChartTightSelection :=
    forall_hasBalancedMultiplier_of_isChartTightCovering hsymmetric hidempotent
      (size_pos_of_weight_sum_eq_one hweightSum) hcovering

/-- **THE BUNDLE-LEVEL EQUIVALENCE.**  With the chart point, the active family and the
nonempty tight eigenspaces fixed, the strong stationarity datum IS the covering condition. -/
theorem isChartStrongStationaryData_iff_isChartTightCovering
    (hsymmetric : projectionᵀ = projection) (hidempotent : projection * projection = projection)
    (htraceRank : Matrix.trace projection = (rank : ℝ))
    (hweightPos : ∀ atomIndex : Fin size, 0 < weight atomIndex)
    (hweightSum : ∑ atomIndex : Fin size, weight atomIndex = 1)
    (hcard : ∀ activeLabel ∈ activeSet, (activeSubset activeLabel).card = rank)
    (hexistsTight : ∀ activeLabel ∈ activeSet, ∃ tightVec : Fin size → ℝ,
      IsChartTightDirection projection weight value (activeSubset activeLabel) tightVec) :
    IsChartStrongStationaryData rank projection weight value activeSet activeSubset
      ↔ IsChartTightCovering projection weight value activeSet activeSubset :=
  ⟨isChartTightCovering_of_isChartStrongStationaryData,
   isChartStrongStationaryData_of_isChartTightCovering hsymmetric hidempotent htraceRank
     hweightPos hweightSum hcard hexistsTight⟩

/-! ## The halfspace case

At simple tight multiplicity the compression is one-dimensional, the cone collapses to the
tangent space met with a single closed halfspace, and covering by halfspaces is exactly
Gordan's alternative for the named selection.  This is the stratum on which the covering
criterion adds nothing to `Gtz.IsChartStationaryData`. -/

/-- **SIMPLICITY PASSES FROM DIRECTIONS TO VECTORS.**  If every unit tight direction of a
block is a multiple of one named direction then so is every tight vector: the zero vector
trivially, and every other by normalising and dividing back. -/
theorem exists_smul_of_isChartTightVector_of_simple {chosenSubset : Finset (Fin size)}
    {tightDir : Fin size → ℝ}
    (hsimple : ∀ probe : Fin size → ℝ,
      IsChartTightDirection projection weight value chosenSubset probe →
      ∃ scale : ℝ, probe = scale • tightDir)
    {tightVec : Fin size → ℝ}
    (htight : IsChartTightVector projection weight value chosenSubset tightVec) :
    ∃ scale : ℝ, tightVec = scale • tightDir := by
  by_cases hzero : tightVec = 0
  · exact ⟨0, by rw [hzero, zero_smul]⟩
  · obtain ⟨normalise, hnormalisePos, hnormalised⟩ :=
      exists_pos_isChartTightDirection_smul_of_isChartTightVector htight hzero
    obtain ⟨scale, hscale⟩ := hsimple (normalise • tightVec) hnormalised
    refine ⟨normalise⁻¹ * scale, ?_⟩
    have hrescaled := congrArg (fun probe : Fin size → ℝ => normalise⁻¹ • probe) hscale
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hnormalisePos), one_smul] using hrescaled

/-- **AT SIMPLE MULTIPLICITY THE CONE IS A HALFSPACE OF THE TANGENT SPACE.**  Membership is
one scalar inequality, at the named direction. -/
theorem mem_chartTightCone_iff_of_simple {chosenSubset : Finset (Fin size)}
    {tightDir : Fin size → ℝ}
    (htightDir : IsChartTightDirection projection weight value chosenSubset tightDir)
    (hsimple : ∀ probe : Fin size → ℝ,
      IsChartTightDirection projection weight value chosenSubset probe →
      ∃ scale : ℝ, probe = scale • tightDir)
    {direction : ChartDirection size} :
    direction ∈ chartTightCone projection weight value chosenSubset
      ↔ IsChartTangent projection direction.1 direction.2
        ∧ 0 ≤ chartTangentSlope tightDir direction.1 direction.2 := by
  rw [mem_chartTightCone_iff]
  refine and_congr_right fun _ => ⟨fun hall =>
    hall tightDir (isChartTightVector_of_isChartTightDirection htightDir), fun hnamed => ?_⟩
  intro tightVec htight
  obtain ⟨scale, hscale⟩ := exists_smul_of_isChartTightVector_of_simple hsimple htight
  rw [hscale, chartTangentSlope_smul]
  exact mul_nonneg (sq_nonneg scale) hnamed

/-- **THE CONE AS A SET, at simple multiplicity**: the tangent space met with one closed
halfspace.  This is the literal reading of "each `S_C` is a halfspace". -/
theorem chartTightCone_coe_eq_inter_of_simple {chosenSubset : Finset (Fin size)}
    {tightDir : Fin size → ℝ}
    (htightDir : IsChartTightDirection projection weight value chosenSubset tightDir)
    (hsimple : ∀ probe : Fin size → ℝ,
      IsChartTightDirection projection weight value chosenSubset probe →
      ∃ scale : ℝ, probe = scale • tightDir) :
    (chartTightCone projection weight value chosenSubset : Set (ChartDirection size))
      = (chartTangentSubmodule projection : Set (ChartDirection size))
        ∩ chartTangentSlopeFunctional tightDir ⁻¹' Set.Ici (0 : ℝ) := by
  ext direction
  rw [SetLike.mem_coe, mem_chartTightCone_iff_of_simple htightDir hsimple]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici, SetLike.mem_coe,
    mem_chartTangentSubmodule_iff, chartTangentSlopeFunctional_apply]

/-- **COVERING BY HALFSPACES IS GORDAN'S ALTERNATIVE.**  At simple tight multiplicity the
covering condition says exactly that the named selection admits a balanced multiplier.

Forward is Gordan, through `Gtz.hasBalancedMultiplier_iff_not_exists_descent`; backward is
the direct converse of the descent lemma.  The whole strengthening of the sibling file
therefore lives on the multiplicity stratum and nowhere else. -/
theorem isChartTightCovering_iff_hasBalancedMultiplier_of_simple
    (hsymmetric : projectionᵀ = projection) (hidempotent : projection * projection = projection)
    (hsizePos : 0 < size) {tightDir : activeIndex → (Fin size → ℝ)}
    (htightDir : ∀ activeLabel ∈ activeSet,
      IsChartTightDirection projection weight value (activeSubset activeLabel)
        (tightDir activeLabel))
    (hsimple : ∀ activeLabel ∈ activeSet, ∀ probe : Fin size → ℝ,
      IsChartTightDirection projection weight value (activeSubset activeLabel) probe →
      ∃ scale : ℝ, probe = scale • tightDir activeLabel) :
    IsChartTightCovering projection weight value activeSet activeSubset
      ↔ HasBalancedMultiplier projection activeSet tightDir := by
  have hunit : ∀ activeLabel ∈ activeSet,
      tightDir activeLabel ⬝ᵥ tightDir activeLabel = 1 :=
    fun activeLabel hmem => (htightDir activeLabel hmem).isUnit
  constructor
  · intro hcovering
    refine (hasBalancedMultiplier_iff_not_exists_descent hsymmetric hidempotent hsizePos
      hunit).mpr ?_
    rintro ⟨directionMatrix, directionWeight, htangent, hnegative⟩
    obtain ⟨activeLabel, hmem, hcone⟩ := hcovering (directionMatrix, directionWeight) htangent
    have hnonneg := ((mem_chartTightCone_iff_of_simple (htightDir activeLabel hmem)
      (hsimple activeLabel hmem)).mp hcone).2
    exact absurd hnonneg (not_le.mpr (hnegative activeLabel hmem))
  · intro hbalanced direction htangent
    by_contra hmissed
    have hnotCone : ∀ activeLabel : activeIndex, activeLabel ∈ activeSet →
        direction ∉ chartTightCone projection weight value (activeSubset activeLabel) :=
      fun activeLabel hmem hcone => hmissed ⟨activeLabel, hmem, hcone⟩
    have hallNegative : ∀ activeLabel ∈ activeSet,
        chartTangentSlope (tightDir activeLabel) direction.1 direction.2 < 0 := by
      intro activeLabel hmem
      refine not_le.mp fun hnonneg => hnotCone activeLabel hmem ?_
      exact (mem_chartTightCone_iff_of_simple (htightDir activeLabel hmem)
        (hsimple activeLabel hmem)).mpr ⟨htangent, hnonneg⟩
    exact not_hasBalancedMultiplier_of_forall_chartTangentSlope_neg htangent hallNegative hbalanced

/-! ## The covering condition is inhabited — the tetrahedron at `(4,3)`

`Gtz.chartTetraProjection_isChartStrongStationaryData` is the shipped strong datum: four
atoms of leverage three at uniform weight `1/4`, `value = 0`, four active triples, every
tight block simple.  Covering therefore holds there, and every theorem above is a statement
about a non-empty class. -/

/-- **THE TETRAHEDRON COVERS.**  Rank three, four atoms, `value = 0`, four active
triples — the shipped strong datum read through the exchange. -/
theorem chartTetraProjection_isChartTightCovering :
    IsChartTightCovering chartTetraProjection chartTetraWeight 0
      (Finset.univ : Finset (Fin 4)) chartTetraSubset :=
  isChartTightCovering_of_isChartStrongStationaryData
    chartTetraProjection_isChartStrongStationaryData

/-- **The covering condition is inhabited**, on the extremal locus `value = 0`. -/
theorem exists_isChartTightCovering :
    ∃ (projection : Matrix (Fin 4) (Fin 4) ℝ) (weight : Fin 4 → ℝ)
      (activeSubset : Fin 4 → Finset (Fin 4)),
      IsChartTightCovering projection weight 0 (Finset.univ : Finset (Fin 4)) activeSubset :=
  ⟨chartTetraProjection, chartTetraWeight, chartTetraSubset,
    chartTetraProjection_isChartTightCovering⟩

end Gtz
