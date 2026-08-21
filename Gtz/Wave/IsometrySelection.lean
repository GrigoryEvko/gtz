/-
# The problem has no designs in it: `GtzWeighted m k` is a statement about isometries

`Gtz.dominates_iff_posSemidef_projectionBlock` reads domination off the design's
own projection form: for a selection of size exactly the rank,

  `Dominates D T  <->  P[T,T] >= diag(t_T)` ,   `P = V Vᵀ`,  `V = scaledAtomRows D` .

That is one half of a dictionary.  This module supplies the other half, which is
what makes it an EQUIVALENCE and therefore a change of subject rather than a
change of notation:

  **`Gtz.designOfIsometry`: every `m x k` matrix `V` with `Vᵀ V = 1` and every
  point `t` of the open simplex IS a design.**

The construction is forced and costs nothing -- put `g_c = t_c^{-1/2} · V_c`.
Parseval is then exactly `Vᵀ V = 1`, since the weights cancel the scaling
(`Gtz.designOfIsometry_isParseval` inside the structure), and the design's scaled
frame is `V` back again (`Gtz.scaledAtomRows_designOfIsometry`).

## The consequence

`Gtz.gtzWeighted_iff_isometrySelects`:

  **`GtzWeighted m k` holds if and only if for every `V` with `Vᵀ V = 1` and
  every positive `t` summing to one there is an injection `pick : Fin k -> Fin m`
  with `(V Vᵀ)[pick, pick] >= diag (t ∘ pick)`.**

No atoms, no Parseval, no Loewner order on the rank-`k` space -- one isometry,
one point of a simplex, one principal block.  At the open cell this is

  **`Gtz.gtzWeighted_six_three_iff_isometrySelects`**,

so the whole `(6,3)` frontier is the following question about a `6 x 3` matrix
with orthonormal columns: among the twenty principal `3 x 3` blocks of `V Vᵀ`,
must one of them dominate the corresponding diagonal block of the weights?

## Why the parameters are genuinely free, and what that buys

The two inputs are UNCOUPLED: `V` ranges over the whole Stiefel manifold and `t`
over the whole open simplex, independently.  Every constraint the design carried
-- Parseval, positivity, the weight sum -- has been absorbed into "`V` is an
isometry" and "`t` is a probability vector".  So a proof may move `V` and `t`
separately, which no formulation in the design coordinates allowed.

Two invariants come for free and are recorded here:
`Gtz.trace_projection_isometry` (the block diagonal totals the rank) and
`Gtz.sum_projectionDiag_sub_weight` (the budget `k - 1` the selection spends).

[MEASURED, scratchpad/NOTES-f73-etwo-selector.txt F73-2: the dictionary is
verified against genuine designs at `9.510e-13` with zero sign mismatches over
4000 designs and all twenty triples of each; and the abstract statement holds
with no failures at `(4,3)`, `(5,3)`, `(6,3)`, `(7,3)`, `(6,4)`, `(7,4)`,
`(8,4)`, `(10,4)`, minimum best margin `+0.0286`.]
-/
import Gtz.LinAlg.ProjectionForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. Every isometry with a simplex point is a design -/

/-- **THE REALIZATION.**  An `m x k` matrix with orthonormal columns and a point
of the open simplex assemble into a weighted design: divide each row by the
square root of its weight.  Parseval is exactly the orthonormality, because the
weight cancels the scaling. -/
noncomputable def designOfIsometry (V : Matrix (Fin m) (Fin k) ℝ)
    (t : Fin m → ℝ) (htpos : ∀ c, 0 < t c) (htsum : ∑ c, t c = 1)
    (hV : Vᵀ * V = 1) : WeightedDesign m k where
  atom := fun c => (Real.sqrt (t c))⁻¹ • V c
  weight := t
  weight_pos := htpos
  weight_sum_one := htsum
  isParseval := by
    have hstep : ∀ c : Fin m,
        t c • atomMatrix ((Real.sqrt (t c))⁻¹ • V c) = atomMatrix (V c) := by
      intro c
      rw [atomMatrix_smul, smul_smul, inv_pow, Real.sq_sqrt (htpos c).le,
        mul_inv_cancel₀ (htpos c).ne', one_smul]
    rw [Finset.sum_congr rfl fun c _ => hstep c, ← transpose_mul_self_eq_sum_rows, hV]

@[simp] theorem weight_designOfIsometry (V : Matrix (Fin m) (Fin k) ℝ)
    (t : Fin m → ℝ) (htpos : ∀ c, 0 < t c) (htsum : ∑ c, t c = 1) (hV : Vᵀ * V = 1) :
    (designOfIsometry V t htpos htsum hV).weight = t := rfl

/-- **THE SCALED FRAME COMES BACK.**  The realization is a section of
`Gtz.scaledAtomRows`: scaling the rows back up returns `V` itself. -/
theorem scaledAtomRows_designOfIsometry (V : Matrix (Fin m) (Fin k) ℝ)
    (t : Fin m → ℝ) (htpos : ∀ c, 0 < t c) (htsum : ∑ c, t c = 1) (hV : Vᵀ * V = 1) :
    scaledAtomRows (designOfIsometry V t htpos htsum hV) = V := by
  ext c coord
  show Real.sqrt (t c) * ((Real.sqrt (t c))⁻¹ * V c coord) = V c coord
  rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (htpos c)), one_mul]

/-- The realization's projection form is the isometry's own outer square. -/
theorem projectionOfDesign_designOfIsometry (V : Matrix (Fin m) (Fin k) ℝ)
    (t : Fin m → ℝ) (htpos : ∀ c, 0 < t c) (htsum : ∑ c, t c = 1) (hV : Vᵀ * V = 1) :
    projectionOfDesign (designOfIsometry V t htpos htsum hV) = V * Vᵀ := by
  rw [projectionOfDesign, scaledAtomRows_designOfIsometry]

/-! ## 2. The selection statement, with no design in it -/

/-- **THE SELECTION STATEMENT.**  For every `m x k` isometry and every point of
the open simplex, some `k` of the `m` indices carry a principal block of `V Vᵀ`
dominating their own weights. -/
def IsometrySelects (m k : ℕ) : Prop :=
  ∀ V : Matrix (Fin m) (Fin k) ℝ, Vᵀ * V = 1 →
    ∀ t : Fin m → ℝ, (∀ c, 0 < t c) → ∑ c, t c = 1 →
      ∃ pick : Fin k → Fin m, Function.Injective pick ∧
        ((V * Vᵀ).submatrix pick pick
          - Matrix.diagonal (fun selectedIndex => t (pick selectedIndex))).PosSemidef

/-- The selection statement produces weighted GTZ: read a design through its own
scaled frame. -/
theorem gtzWeighted_of_isometrySelects (h : IsometrySelects m k) : GtzWeighted m k := by
  intro D
  obtain ⟨pick, hinj, hpsd⟩ := h (scaledAtomRows D) (transpose_mul_scaledAtomRows D)
    D.weight D.weight_pos D.weight_sum_one
  refine ⟨Finset.image pick Finset.univ, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · rw [dominates_iff_posSemidef_projectionBlock D pick hinj]
    exact hpsd

/-- Weighted GTZ produces the selection statement: every isometry and simplex
point is a design, by `Gtz.designOfIsometry`. -/
theorem isometrySelects_of_gtzWeighted (h : GtzWeighted m k) : IsometrySelects m k := by
  intro V hV t htpos htsum
  obtain ⟨C, hcard, hdom⟩ := h (designOfIsometry V t htpos htsum hV)
  refine ⟨C.orderEmbOfFin hcard, (C.orderEmbOfFin hcard).injective, ?_⟩
  have hblock := (dominates_iff_posSemidef_projectionBlock_finset
    (designOfIsometry V t htpos htsum hV) C hcard).mp hdom
  rwa [projectionOfDesign_designOfIsometry] at hblock

/-- **THE EQUIVALENCE.**  Weighted GTZ at size `m` and rank `k` IS the selection
statement about `m x k` isometries.  Nothing about designs survives: the two
inputs are an isometry and a probability vector, and they are uncoupled. -/
theorem gtzWeighted_iff_isometrySelects : GtzWeighted m k ↔ IsometrySelects m k :=
  ⟨isometrySelects_of_gtzWeighted, gtzWeighted_of_isometrySelects⟩

/-- **THE OPEN CELL, WITHOUT DESIGNS.**  The `(6,3)` frontier is a question about
a `6 x 3` matrix with orthonormal columns and six positive weights summing to
one: must one of the twenty principal `3 x 3` blocks of `V Vᵀ` dominate its own
diagonal weight block? -/
theorem gtzWeighted_six_three_iff_isometrySelects :
    GtzWeighted 6 3 ↔ IsometrySelects 6 3 :=
  gtzWeighted_iff_isometrySelects

/-! ## 3. The two free invariants -/

/-- The projection form of an isometry has trace equal to the rank. -/
theorem trace_projection_isometry (V : Matrix (Fin m) (Fin k) ℝ) (hV : Vᵀ * V = 1) :
    (V * Vᵀ).trace = (k : ℝ) := by
  rw [Matrix.trace_mul_comm, hV, Matrix.trace_one, Fintype.card_fin]

/-- **THE BUDGET.**  Across all indices the projection diagonal beats the weights
by exactly `k - 1`.  Every selection statement is a statement about how this
surplus is distributed, and at `k = 1` the surplus is zero, which is why the
rank-one case is an equality pigeonhole. -/
theorem sum_projectionDiag_sub_weight (V : Matrix (Fin m) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (t : Fin m → ℝ) (htsum : ∑ c, t c = 1) :
    ∑ c, ((V * Vᵀ) c c - t c) = (k : ℝ) - 1 := by
  have htr : ∑ c, (V * Vᵀ) c c = (k : ℝ) := by
    rw [show (∑ c, (V * Vᵀ) c c) = (V * Vᵀ).trace from rfl, trace_projection_isometry V hV]
  rw [Finset.sum_sub_distrib, htsum, htr]

/-- **THE DIAGONAL IS THE WEIGHTED LEVERAGE.**  Under the realization the
projection diagonal is the design's own leverage score, so the abstract
statement's diagonal data is the campaign's `t_c * l_c`. -/
theorem projectionDiag_designOfIsometry (V : Matrix (Fin m) (Fin k) ℝ)
    (t : Fin m → ℝ) (htpos : ∀ c, 0 < t c) (htsum : ∑ c, t c = 1) (hV : Vᵀ * V = 1)
    (c : Fin m) :
    (V * Vᵀ) c c
      = t c * leverageOf ((designOfIsometry V t htpos htsum hV).atom c) := by
  rw [← projectionOfDesign_designOfIsometry V t htpos htsum hV,
    projectionOfDesign_diagonal]
  rfl

end Gtz
