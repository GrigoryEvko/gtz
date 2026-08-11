/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Quantitative.ChartStationary

/-!
# The joint first-order index floor

`Gtz.IsChartStationaryData` carries TWO first-order fields, and the shipped index ladder
reads only one of them.  `assembly_diagonal` is stationarity in the WEIGHTS and lives in the
`size`-dimensional weight space; `assembly_commutes` is stationarity in the GRASSMANNIAN and
lives in the `rank * (size - rank)`-dimensional tangent of the chart.  Both say the same
kind of thing — a family of gradients carries a vanishing combination whose coefficients are
the multipliers — so both are instances of one lemma, and so is their PAIR.

This file states the pair.  Writing

  `jointChartGradient P v = (tightSquareRow v - uniform, P * atomMatrix v * (1 - P))`,

both fields together say `∑ multiplier • jointChartGradient = 0` with the multipliers summing
to one, hence

  `finrank (span of the joint gradients) + 1 ≤ activeSet.card`,

and the two one-block floors are its images under the two coordinate projections.  A
projection cannot raise a rank, so the JOINT floor DOMINATES both halves; the Grassmannian
floor and the simplex floor below are corollaries of it, not siblings of it.

## What is and is not claimed

The floor is an UPPER bound on a rank read as a lower bound on a count.  Whether either span
is ever forced to be large at a counterexample is NOT settled here and no claim about it is
made.  What is settled is the ARITHMETIC of the two ambients: the simplex block cannot carry
more than `size - 1`, so a ladder counting there cannot exceed `size` however strong its kill
becomes, while the Grassmannian block carries up to `rank * (size - rank)` — `5` against `9`
at `(6,3)`, and `6` against `12` at `(7,3)`.

The gradient identification is not a guess: `grassmannGradient_eq_vecMulVec` shows the
Grassmannian block IS the outer product of the two halves of the tight direction, and
`dotProduct_mulVec_eq_two_mul_of_tangent` shows that along any tangent to the chart — any
symmetric `X` killed on both diagonal corners — the first-order motion of the block value
`v ⬝ᵥ X *ᵥ v` reads only that off-diagonal corner.

## Non-vacuity

`Gtz.chartTetraProjection_isChartStationaryData` instantiates both floors; the last two
theorems record it.
-/

namespace Gtz

open Matrix Module

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {size : ℕ} {activeIndex : Type*}

/-! ## A normalised vanishing combination costs a dimension -/

/-- **A NORMALISED VANISHING COMBINATION COSTS ONE DIMENSION.**  Coefficients summing to one
cannot all vanish, so the family is linearly dependent and its span is a proper subspace of
the one a linearly independent family of that size would span.  Pure linear algebra: no
chart, no positivity, no geometry. -/
theorem finrank_span_add_one_le_of_sum_smul_eq_zero {ambientType : Type*}
    [AddCommGroup ambientType] [Module ℝ ambientType] {count : ℕ}
    (vec : Fin count → ambientType) (coeff : Fin count → ℝ)
    (hsum : ∑ index, coeff index = 1)
    (hrelation : ∑ index, coeff index • vec index = 0) :
    finrank ℝ (Submodule.span ℝ (Set.range vec)) + 1 ≤ count := by
  classical
  have hnotIndependent : ¬ LinearIndependent ℝ vec := by
    intro hindependent
    have hzero : ∀ index, coeff index = 0 :=
      fun index => Fintype.linearIndependent_iff.mp hindependent coeff hrelation index
    have : (1 : ℝ) = 0 := by
      rw [← hsum]
      exact (Finset.sum_eq_zero fun index _ => hzero index)
    exact one_ne_zero this
  have hle : finrank ℝ (Submodule.span ℝ (Set.range vec)) ≤ count := by
    have hcard := finrank_span_le_card (R := ℝ) (Set.range vec)
    have hcardUniv : (Finset.univ : Finset (Fin count)).card = count := by
      rw [Finset.card_univ, Fintype.card_fin]
    have himage : (Finset.image vec Finset.univ).card ≤ count := by
      have hbound : (Finset.image vec Finset.univ).card
          ≤ (Finset.univ : Finset (Fin count)).card := Finset.card_image_le
      omega
    simp only [Set.toFinset_range] at hcard
    omega
  have hne : finrank ℝ (Submodule.span ℝ (Set.range vec)) ≠ count := by
    intro heq
    exact hnotIndependent (linearIndependent_iff_card_eq_finrank_span.mpr
      (by simp [Set.finrank, heq]))
  omega

/-- The same statement over a `Finset` of labels, which is the shape every floor below wants.
Factoring it out is what keeps the three floors one line each. -/
theorem finrank_span_add_one_le_card_of_activeRelation {ambientType : Type*}
    [AddCommGroup ambientType] [Module ℝ ambientType]
    (activeSet : Finset activeIndex) (coeff : activeIndex → ℝ) (vec : activeIndex → ambientType)
    (hsum : ∑ activeLabel ∈ activeSet, coeff activeLabel = 1)
    (hrelation : ∑ activeLabel ∈ activeSet, coeff activeLabel • vec activeLabel = 0) :
    finrank ℝ (Submodule.span ℝ (Set.range fun label : Fin activeSet.card =>
        vec (activeSet.equivFin.symm label : activeIndex))) + 1 ≤ activeSet.card := by
  classical
  refine finrank_span_add_one_le_of_sum_smul_eq_zero _
    (fun label : Fin activeSet.card => coeff (activeSet.equivFin.symm label : activeIndex)) ?_ ?_
  · rw [← hsum]
    exact (Fintype.sum_equiv activeSet.equivFin.symm _ _ (fun _ => rfl)).trans
      (Finset.sum_coe_sort activeSet coeff)
  · rw [← hrelation]
    exact (Fintype.sum_equiv activeSet.equivFin.symm _ _ (fun _ => rfl)).trans
      (Finset.sum_coe_sort activeSet (fun activeLabel => coeff activeLabel • vec activeLabel))

/-- **A COORDINATE PROJECTION CANNOT RAISE A RANK.**  This is the whole reason the joint floor
dominates its two halves. -/
theorem finrank_span_range_linearMap_le {leftType rightType : Type*}
    [AddCommGroup leftType] [Module ℝ leftType] [AddCommGroup rightType] [Module ℝ rightType]
    {count : ℕ} (linearMap : leftType →ₗ[ℝ] rightType) (vec : Fin count → leftType) :
    finrank ℝ (Submodule.span ℝ (Set.range fun index => linearMap (vec index)))
      ≤ finrank ℝ (Submodule.span ℝ (Set.range vec)) := by
  classical
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range vec)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range vec)
  have hcomp : (fun index => linearMap (vec index)) = (linearMap : leftType → rightType) ∘ vec :=
    rfl
  rw [hcomp, Set.range_comp, Submodule.span_image]
  exact Submodule.finrank_map_le linearMap (Submodule.span ℝ (Set.range vec))

/-! ## The Grassmannian block -/

/-- **THE GRASSMANNIAN GRADIENT.**  Moving the chart along a tangent `X` moves the least
eigenvalue of the block by `tightDir ⬝ᵥ X *ᵥ tightDir`, and the functional that reads off is
this off-diagonal corner of the tight direction's outer product. -/
noncomputable def grassmannGradient (projection : Matrix (Fin size) (Fin size) ℝ)
    (tightVector : Fin size → ℝ) : Matrix (Fin size) (Fin size) ℝ :=
  projection * atomMatrix tightVector * (1 - projection)

/-- **THE GRADIENT IS THE OUTER PRODUCT OF THE TWO HALVES OF THE TIGHT DIRECTION.**  So it is
rank at most one, and it vanishes exactly when the tight direction lies wholly inside the
chart's range or wholly inside its kernel. -/
theorem grassmannGradient_eq_vecMulVec {projection : Matrix (Fin size) (Fin size) ℝ}
    (hsymmetric : projectionᵀ = projection) (tightVector : Fin size → ℝ) :
    grassmannGradient projection tightVector
      = Matrix.vecMulVec (projection *ᵥ tightVector) ((1 - projection) *ᵥ tightVector) := by
  have htranspose : (1 - projection)ᵀ = 1 - projection := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsymmetric]
  have hcomplement : ∀ rowIndex colIndex : Fin size,
      (1 - projection) rowIndex colIndex = (1 - projection) colIndex rowIndex := by
    intro rowIndex colIndex
    have hentry := congrArg (fun mat : Matrix (Fin size) (Fin size) ℝ =>
      mat colIndex rowIndex) htranspose
    simpa [Matrix.transpose_apply] using hentry
  have hleft : ∀ rowIndex midIndex : Fin size,
      (projection * atomMatrix tightVector) rowIndex midIndex
        = (projection *ᵥ tightVector) rowIndex * tightVector midIndex := by
    intro rowIndex midIndex
    simp only [Matrix.mul_apply, atomMatrix, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun innerIndex _ => by ring
  ext rowIndex colIndex
  have hright : ((1 - projection) *ᵥ tightVector) colIndex
      = ∑ midIndex, tightVector midIndex * (1 - projection) midIndex colIndex := by
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun midIndex _ => by
      rw [hcomplement colIndex midIndex]; ring
  rw [grassmannGradient, Matrix.mul_apply, Matrix.vecMulVec_apply, hright, Finset.mul_sum]
  exact Finset.sum_congr rfl fun midIndex _ => by rw [hleft]; ring

/-- Quadratic forms cannot see a transpose. -/
theorem dotProduct_transpose_mulVec_self (mat : Matrix (Fin size) (Fin size) ℝ)
    (vec : Fin size → ℝ) : vec ⬝ᵥ (matᵀ *ᵥ vec) = vec ⬝ᵥ (mat *ᵥ vec) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun rowIndex _ => Finset.sum_congr rfl fun colIndex _ => by ring

/-- **THE FIRST-ORDER MOTION READS ONLY THE OFF-DIAGONAL CORNER.**  A tangent to the manifold
of rank-`rank` orthogonal projections is a symmetric matrix killed by both diagonal corners of
the chart, and against such a tangent the derivative of the block's least eigenvalue —
`tightDir ⬝ᵥ X *ᵥ tightDir` — is twice the corner pairing.  This is the identification the
Grassmannian gradient rests on, and it is two lines of algebra rather than a convention. -/
theorem dotProduct_mulVec_eq_two_mul_of_tangent
    {projection tangent : Matrix (Fin size) (Fin size) ℝ}
    (hchart : projectionᵀ = projection) (hsymmetric : tangentᵀ = tangent)
    (hrangeCorner : projection * tangent * projection = 0)
    (hkernelCorner : (1 - projection) * tangent * (1 - projection) = 0)
    (tightVector : Fin size → ℝ) :
    tightVector ⬝ᵥ (tangent *ᵥ tightVector)
      = 2 * (tightVector ⬝ᵥ ((projection * tangent * (1 - projection)) *ᵥ tightVector)) := by
  have hsplit : projection * tangent * projection + projection * tangent * (1 - projection)
      + (1 - projection) * tangent * projection + (1 - projection) * tangent * (1 - projection)
      = tangent := by noncomm_ring
  have hmirror : ((1 - projection) * tangent * projection)ᵀ
      = projection * tangent * (1 - projection) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hsymmetric, hchart, Matrix.transpose_sub,
      Matrix.transpose_one, hchart, Matrix.mul_assoc]
  have hcross : tightVector ⬝ᵥ (((1 - projection) * tangent * projection) *ᵥ tightVector)
      = tightVector ⬝ᵥ ((projection * tangent * (1 - projection)) *ᵥ tightVector) := by
    rw [← hmirror, dotProduct_transpose_mulVec_self]
  conv_lhs => rw [← hsplit]
  simp only [hrangeCorner, hkernelCorner, Matrix.add_mulVec, dotProduct_add, add_zero, zero_add]
  rw [hcross]
  ring

/-- The Grassmannian gradients of the active family assemble to the off-diagonal corner of the
multiplier assembly. -/
theorem sum_smul_grassmannGradient_eq_corner
    (projection : Matrix (Fin size) (Fin size) ℝ) (activeSet : Finset activeIndex)
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin size → ℝ)) :
    ∑ activeLabel ∈ activeSet,
        activeWeight activeLabel • grassmannGradient projection (tightDir activeLabel)
      = projection * chartMultiplierAssembly activeSet activeWeight tightDir
          * (1 - projection) := by
  classical
  rw [chartMultiplierAssembly, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun activeLabel _ => ?_
  simp only [grassmannGradient, Matrix.mul_smul, Matrix.smul_mul]

/-- **STATIONARITY IN THE GRASSMANNIAN IS A VANISHING COMBINATION.**  The commutation field
plus idempotence kill the off-diagonal corner, so the active Grassmannian gradients carry a
relation whose coefficients are the multipliers. -/
theorem sum_smul_grassmannGradient_eq_zero_of_isChartStationaryData
    {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
    {value : ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ∑ activeLabel ∈ activeSet,
        activeWeight activeLabel • grassmannGradient projection (tightDir activeLabel) = 0 := by
  classical
  set assembly := chartMultiplierAssembly activeSet activeWeight tightDir with hassembly
  have hsquare : projection * assembly * projection = projection * assembly := by
    rw [hdata.assembly_commutes, Matrix.mul_assoc, hdata.isIdempotent]
  rw [sum_smul_grassmannGradient_eq_corner, ← hassembly, Matrix.mul_sub, Matrix.mul_one,
    hsquare, sub_self]

/-! ## The simplex block -/

/-- The squared row of a tight direction: the gradient of its block's value in the weights,
up to sign. -/
def tightSquareRow (tightVector : Fin size → ℝ) : Fin size → ℝ :=
  fun atomIndex => tightVector atomIndex ^ 2

/-- **STATIONARITY IN THE WEIGHTS, READ AS A ROW IDENTITY.**  The assembly diagonal says
exactly that the multiplier-weighted squared rows average to the uniform row. -/
theorem sum_smul_tightSquareRow_eq_const_of_isChartStationaryData
    {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
    {value : ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ∑ activeLabel ∈ activeSet,
        activeWeight activeLabel • tightSquareRow (tightDir activeLabel)
      = fun _ : Fin size => ((size : ℝ))⁻¹ := by
  classical
  funext atomIndex
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, tightSquareRow, smul_eq_mul]
  rw [← chartMultiplierAssembly_diagonal activeSet activeWeight tightDir atomIndex,
    hdata.assembly_diagonal atomIndex]

/-- The squared row with the uniform row removed: the simplex gradient proper, living in the
`size - 1` dimensional space of rows summing to zero. -/
noncomputable def centredTightSquareRow (tightVector : Fin size → ℝ) : Fin size → ℝ :=
  tightSquareRow tightVector - fun _ : Fin size => ((size : ℝ))⁻¹

/-- **STATIONARITY IN THE WEIGHTS IS A VANISHING COMBINATION.** -/
theorem sum_smul_centredTightSquareRow_eq_zero_of_isChartStationaryData
    {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
    {value : ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ∑ activeLabel ∈ activeSet,
        activeWeight activeLabel • centredTightSquareRow (tightDir activeLabel) = 0 := by
  classical
  have hrow := sum_smul_tightSquareRow_eq_const_of_isChartStationaryData hdata
  have hone := hdata.activeWeight_sum_one
  simp only [centredTightSquareRow, smul_sub, Finset.sum_sub_distrib, hrow, ← Finset.sum_smul,
    hone, one_smul, sub_self]

/-! ## The joint gradient and its floor -/

/-- **THE JOINT FIRST-ORDER GRADIENT.**  The pair of the two blocks.  Both stationarity fields
are statements about this single object. -/
noncomputable def jointChartGradient (projection : Matrix (Fin size) (Fin size) ℝ)
    (tightVector : Fin size → ℝ) :
    (Fin size → ℝ) × Matrix (Fin size) (Fin size) ℝ :=
  (centredTightSquareRow tightVector, grassmannGradient projection tightVector)

/-- **BOTH STATIONARITY FIELDS AT ONCE.** -/
theorem sum_smul_jointChartGradient_eq_zero_of_isChartStationaryData
    {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
    {value : ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ∑ activeLabel ∈ activeSet,
        activeWeight activeLabel • jointChartGradient projection (tightDir activeLabel) = 0 := by
  classical
  have hfirst : (∑ activeLabel ∈ activeSet,
      activeWeight activeLabel • jointChartGradient projection (tightDir activeLabel)).1 = 0 := by
    rw [Prod.fst_sum]
    exact sum_smul_centredTightSquareRow_eq_zero_of_isChartStationaryData hdata
  have hsecond : (∑ activeLabel ∈ activeSet,
      activeWeight activeLabel • jointChartGradient projection (tightDir activeLabel)).2 = 0 := by
    rw [Prod.snd_sum]
    exact sum_smul_grassmannGradient_eq_zero_of_isChartStationaryData hdata
  exact Prod.ext hfirst hsecond

/-- **THE JOINT INDEX FLOOR.**  The span of the active joint gradients is one dimension short
of the active count.  This is the merge of the two one-block floors and it dominates both. -/
theorem finrank_span_jointChartGradient_add_one_le_card_of_isChartStationaryData
    {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
    {value : ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    finrank ℝ (Submodule.span ℝ (Set.range fun label : Fin activeSet.card =>
        jointChartGradient projection
          (tightDir (activeSet.equivFin.symm label : activeIndex))))
      + 1 ≤ activeSet.card :=
  finrank_span_add_one_le_card_of_activeRelation activeSet activeWeight
    (fun activeLabel => jointChartGradient projection (tightDir activeLabel))
    hdata.activeWeight_sum_one
    (sum_smul_jointChartGradient_eq_zero_of_isChartStationaryData hdata)

/-! ## The two one-block floors, as corollaries -/

/-- The Grassmannian span is a coordinate projection of the joint span. -/
theorem finrank_span_grassmannGradient_le_joint
    (projection : Matrix (Fin size) (Fin size) ℝ) (activeSet : Finset activeIndex)
    (tightDir : activeIndex → (Fin size → ℝ)) :
    finrank ℝ (Submodule.span ℝ (Set.range fun label : Fin activeSet.card =>
        grassmannGradient projection (tightDir (activeSet.equivFin.symm label : activeIndex))))
      ≤ finrank ℝ (Submodule.span ℝ (Set.range fun label : Fin activeSet.card =>
        jointChartGradient projection
          (tightDir (activeSet.equivFin.symm label : activeIndex)))) :=
  finrank_span_range_linearMap_le (LinearMap.snd ℝ (Fin size → ℝ)
    (Matrix (Fin size) (Fin size) ℝ))
    (fun label : Fin activeSet.card => jointChartGradient projection
      (tightDir (activeSet.equivFin.symm label : activeIndex)))

/-- The simplex span is the other coordinate projection of the joint span. -/
theorem finrank_span_centredTightSquareRow_le_joint
    (projection : Matrix (Fin size) (Fin size) ℝ) (activeSet : Finset activeIndex)
    (tightDir : activeIndex → (Fin size → ℝ)) :
    finrank ℝ (Submodule.span ℝ (Set.range fun label : Fin activeSet.card =>
        centredTightSquareRow (tightDir (activeSet.equivFin.symm label : activeIndex))))
      ≤ finrank ℝ (Submodule.span ℝ (Set.range fun label : Fin activeSet.card =>
        jointChartGradient projection
          (tightDir (activeSet.equivFin.symm label : activeIndex)))) :=
  finrank_span_range_linearMap_le (LinearMap.fst ℝ (Fin size → ℝ)
    (Matrix (Fin size) (Fin size) ℝ))
    (fun label : Fin activeSet.card => jointChartGradient projection
      (tightDir (activeSet.equivFin.symm label : activeIndex)))

/-- **THE GRASSMANNIAN INDEX FLOOR**, now a corollary of the joint one.  Its ceiling is the
Grassmannian dimension `rank * (size - rank)`, not the simplex dimension `size - 1`. -/
theorem finrank_span_grassmannGradient_add_one_le_card_of_isChartStationaryData
    {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
    {value : ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    finrank ℝ (Submodule.span ℝ (Set.range fun label : Fin activeSet.card =>
        grassmannGradient projection (tightDir (activeSet.equivFin.symm label : activeIndex))))
      + 1 ≤ activeSet.card :=
  le_trans (Nat.add_le_add_right
      (finrank_span_grassmannGradient_le_joint projection activeSet tightDir) 1)
    (finrank_span_jointChartGradient_add_one_le_card_of_isChartStationaryData hdata)

/-- **THE SIMPLEX INDEX FLOOR**, the twin the shipped ladder computes through the flat space,
here as the other corollary of the joint floor. -/
theorem finrank_span_centredTightSquareRow_add_one_le_card_of_isChartStationaryData
    {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
    {value : ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    finrank ℝ (Submodule.span ℝ (Set.range fun label : Fin activeSet.card =>
        centredTightSquareRow (tightDir (activeSet.equivFin.symm label : activeIndex))))
      + 1 ≤ activeSet.card :=
  le_trans (Nat.add_le_add_right
      (finrank_span_centredTightSquareRow_le_joint projection activeSet tightDir) 1)
    (finrank_span_jointChartGradient_add_one_le_card_of_isChartStationaryData hdata)

/-! ## Non-vacuity -/

/-- **THE HYPOTHESIS IS INHABITED.**  The shipped tetrahedron chart datum instantiates the
joint floor, so it is not a statement about an empty configuration. -/
theorem finrank_span_jointChartGradient_add_one_le_four_tetra :
    finrank ℝ (Submodule.span ℝ (Set.range fun label :
        Fin (Finset.univ : Finset (Fin 4)).card =>
        jointChartGradient chartTetraProjection
          (chartTetraTightDir ((Finset.univ : Finset (Fin 4)).equivFin.symm label : Fin 4))))
      + 1 ≤ (Finset.univ : Finset (Fin 4)).card :=
  finrank_span_jointChartGradient_add_one_le_card_of_isChartStationaryData
    chartTetraProjection_isChartStationaryData

/-- The same for the Grassmannian half. -/
theorem finrank_span_grassmannGradient_add_one_le_four_tetra :
    finrank ℝ (Submodule.span ℝ (Set.range fun label :
        Fin (Finset.univ : Finset (Fin 4)).card =>
        grassmannGradient chartTetraProjection
          (chartTetraTightDir ((Finset.univ : Finset (Fin 4)).equivFin.symm label : Fin 4))))
      + 1 ≤ (Finset.univ : Finset (Fin 4)).card :=
  finrank_span_grassmannGradient_add_one_le_card_of_isChartStationaryData
    chartTetraProjection_isChartStationaryData

end Gtz
