/-
# The field-generic weighted design

The campaign's real layer (`Gtz.WeightedDesign`, `Gtz/Core/Basic.lean`) and its
complex layer (`Gtz.ComplexWeightedDesign`, `Gtz/Complex/ComplexWitness.lean`)
are two copies of one structure.  This file writes that structure ONCE over an
arbitrary `RCLike` field and proves the field-blind half of the size axis here,
so neither copy has to grow a duplicate.

**PROVENANCE — what is new and what is not.**  Over ℝ the two rungs proved
below are already shipped, rank-generically:

  * `size = rank`     : `Gtz.gtzWeighted_square`      (`Gtz/Reduction/Reductions.lean`)
  * `size = rank + 1` : `Gtz.gtzWeighted_corank_one`  (same file, three lines,
    via `Gtz.weighted_naimark_duality`), and independently
    `Gtz.corank_one_dominating_erasure` (`Gtz/Ties/CorankOneTieCriterion.lean`)
    and `Gtz.exists_erase_dominates_of_corank_one` (`Gtz/Reduction/DiagonalRungs.lean`).

Over ℂ neither existed.  `Gtz.complexGtzWeighted_rankOne`
(`Gtz/Complex/PerRankConstantLedger.lean`) and the refutations were the whole
complex ledger; there is no complex Naimark duality and no complex chart in the
repository.  The field-generic route below therefore delivers the complex
positive half as a genuinely new result, and reproves the real rungs as a free
instance — with the real files left untouched, since they are `ᵀ`-shaped and
green.

**THE ROUTE, and why it is not the projection chart.**  Corank one is a TRACE
budget against the co-Parseval operator

    coParsevalOperator = Σ_c (1 - t_c) g_c g_cᴴ = (Σ_c g_c g_cᴴ) - 1,

positive definite as soon as there are two atoms.  Writing
`pivotScalar c = g_cᴴ coParsevalOperator⁻¹ g_c = tr(coParsevalOperator⁻¹ g_c g_cᴴ)`,
one trace computation gives `Σ_c (1 - t_c) pivotScalar c = tr(1) = rank`, while
`Σ_c (1 - t_c) = size - 1`.  At `size = rank + 1` the two right-hand sides
coincide, so the pivots have co-weighted mean exactly one and some pivot is at
most one; the rank-one Schur criterion then says the erasure of that atom
dominates.  No kernel vector, no projection chart, no Naimark duality, no
whitening, no matrix square root.  The same identity over ℝ is
`Gtz.descent_identity` (`Gtz/Reduction/DescentLadder.lean`), whose own header
already records that it "is field-blind by construction".

The projection chart, A1, A2 and the inertia no-go live in
`Gtz/Design/ProjectionChart.lean`; the Jensen reading of corank one and the
total-tie criterion live in `Gtz/Field/CorankOne.lean`; the complex size-axis
headline lives in `Gtz/Complex/SizeAxis.lean`.

**Edge cases, stated not hidden.**  `fieldGtzWeighted_square` is unconditional in
the rank, but the two degenerate cells are unconditional for OPPOSITE reasons and
must not be conflated:

  * `size = 0` (hence `size = rank = 0`) carries NO content — there is no design
    at all, because `weight_sum_one` reads `0 = 1` over an empty index set.  That
    is shipped as `fieldWeightedDesign_zero_size_isEmpty` rather than described,
    so the cell cannot be advertised as a witness.
  * `size = rank = 1` IS inhabited — `Gtz.degenerateSingletonDesign` in
    `Gtz/Design/ProjectionChart.lean` is the unique such design — and there the
    theorem has content.  That same design is the counterexample pinning the
    `2 ≤ size` hypothesis on A2 and on the Jensen criterion.

`fieldGtzWeighted_corank_one` needs `1 ≤ rank`: at rank zero there is no
corank-one cell, which is exactly the hypothesis the shipped real
`Gtz.gtzWeighted_corank_one` carries.
-/
import Mathlib
import Gtz.Core.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix
open scoped ComplexOrder

variable {Scalar : Type*} [RCLike Scalar]

/-! ## The atom and its leverage -/

/-- The rank-one atom `g gᴴ` over an `RCLike` field.  The conjugation sits on the
SECOND (column) index, matching `Gtz.atomMatrix` over ℝ and `Gtz.complexAtom`
over ℂ. -/
def fieldAtom {rank : ℕ} (vector : Fin rank → Scalar) : Matrix (Fin rank) (Fin rank) Scalar :=
  Matrix.vecMulVec vector (star vector)

@[simp] theorem fieldAtom_apply {rank : ℕ} (vector : Fin rank → Scalar)
    (rowIndex colIndex : Fin rank) :
    fieldAtom vector rowIndex colIndex = vector rowIndex * star (vector colIndex) := rfl

/-- At `Scalar = ℝ` the generic atom IS the repo's real atom — definitionally, so
every real consumer transports for free. -/
theorem fieldAtom_eq_atomMatrix {rank : ℕ} (vector : Fin rank → ℝ) :
    fieldAtom vector = atomMatrix vector := rfl

theorem fieldAtom_posSemidef {rank : ℕ} (vector : Fin rank → Scalar) :
    (fieldAtom vector).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star vector

theorem fieldAtom_isHermitian {rank : ℕ} (vector : Fin rank → Scalar) :
    (fieldAtom vector).IsHermitian :=
  (fieldAtom_posSemidef vector).isHermitian

/-- The leverage `|g|²` of an atom vector, as a REAL number over any field. -/
def fieldLeverageOf {rank : ℕ} (vector : Fin rank → Scalar) : ℝ :=
  ∑ coordinate, ‖vector coordinate‖ ^ 2

theorem fieldLeverageOf_nonneg {rank : ℕ} (vector : Fin rank → Scalar) :
    0 ≤ fieldLeverageOf vector :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- At `Scalar = ℝ` the generic leverage is the repo's `Gtz.leverageOf`. -/
theorem fieldLeverageOf_eq_leverageOf {rank : ℕ} (vector : Fin rank → ℝ) :
    fieldLeverageOf vector = leverageOf vector := by
  rw [fieldLeverageOf, leverageOf]
  exact Finset.sum_congr rfl fun coordinate _ => by rw [Real.norm_eq_abs, sq_abs]

/-- The Hermitian square of a vector is its leverage. -/
theorem dotProduct_star_self_eq_fieldLeverage {rank : ℕ} (vector : Fin rank → Scalar) :
    star vector ⬝ᵥ vector = ((fieldLeverageOf vector : ℝ) : Scalar) := by
  rw [dotProduct, fieldLeverageOf, RCLike.ofReal_sum]
  refine Finset.sum_congr rfl fun coordinate _ => ?_
  rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]

/-- The trace of an atom is its leverage. -/
theorem trace_fieldAtom {rank : ℕ} (vector : Fin rank → Scalar) :
    Matrix.trace (fieldAtom vector) = ((fieldLeverageOf vector : ℝ) : Scalar) := by
  rw [fieldAtom, Matrix.trace_vecMulVec, dotProduct, fieldLeverageOf,
    RCLike.ofReal_sum]
  refine Finset.sum_congr rfl fun coordinate _ => ?_
  rw [Pi.star_apply, RCLike.star_def, RCLike.mul_conj, RCLike.ofReal_pow]

/-! ## The design -/

/-- A weighted design over an `RCLike` field: real positive weights summing to
one, Hermitian rank-one atoms resolving the identity. -/
structure FieldWeightedDesign (Scalar : Type*) [RCLike Scalar] (size rank : ℕ) where
  atom : Fin size → (Fin rank → Scalar)
  weight : Fin size → ℝ
  weight_pos : ∀ atomIndex, 0 < weight atomIndex
  weight_sum_one : ∑ atomIndex, weight atomIndex = 1
  isParseval :
    ∑ atomIndex, ((weight atomIndex : ℝ) : Scalar) • fieldAtom (atom atomIndex) = 1

/-- The UNWEIGHTED atom sum over a subset.  Domination is weight-free; the
weights enter only through Parseval. -/
def fieldSubsetSum {size rank : ℕ} (design : FieldWeightedDesign Scalar size rank)
    (selected : Finset (Fin size)) : Matrix (Fin rank) (Fin rank) Scalar :=
  ∑ atomIndex ∈ selected, fieldAtom (design.atom atomIndex)

/-- A subset dominates when its unweighted atom sum is Loewner-above the
identity. -/
def FieldDominates {size rank : ℕ} (design : FieldWeightedDesign Scalar size rank)
    (selected : Finset (Fin size)) : Prop :=
  (fieldSubsetSum design selected - 1).PosSemidef

/-- Weighted GTZ over a fixed field, at one size and rank. -/
def FieldGtzWeighted (Scalar : Type*) [RCLike Scalar] (size rank : ℕ) : Prop :=
  ∀ design : FieldWeightedDesign Scalar size rank,
    ∃ selected : Finset (Fin size), selected.card = rank ∧ FieldDominates design selected

/-! ### Weight bounds -/

theorem fieldWeight_le_one {size rank : ℕ} (design : FieldWeightedDesign Scalar size rank)
    (atomIndex : Fin size) : design.weight atomIndex ≤ 1 := by
  rw [← design.weight_sum_one]
  exact Finset.single_le_sum (fun other _ => (design.weight_pos other).le)
    (Finset.mem_univ atomIndex)

/-- Every weight is STRICTLY below one once there are at least two atoms.  The
hypothesis `2 ≤ size` is load-bearing and reappears in A2. -/
theorem fieldWeight_lt_one {size rank : ℕ} (design : FieldWeightedDesign Scalar size rank)
    (hsize : 2 ≤ size) (atomIndex : Fin size) : design.weight atomIndex < 1 := by
  classical
  obtain ⟨other, hother⟩ : ∃ other : Fin size, other ≠ atomIndex := by
    haveI : Nontrivial (Fin size) := Fin.nontrivial_iff_two_le.mpr hsize
    exact exists_ne atomIndex
  have hpair : design.weight atomIndex + design.weight other
      ≤ ∑ index, design.weight index := by
    have hsum : ∑ index ∈ ({atomIndex, other} : Finset (Fin size)), design.weight index
        = design.weight atomIndex + design.weight other :=
      Finset.sum_pair (Ne.symm hother)
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun index _ _ => (design.weight_pos index).le
  rw [design.weight_sum_one] at hpair
  linarith [design.weight_pos other]

/-- The co-weights `1 - t_c` sum to `size - 1`. -/
theorem sum_coWeight {size rank : ℕ} (design : FieldWeightedDesign Scalar size rank) :
    ∑ atomIndex, (1 - design.weight atomIndex) = (size : ℝ) - 1 := by
  rw [Finset.sum_sub_distrib, design.weight_sum_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **The trace identity**: the weighted leverages sum to the rank.  Read off the
trace of Parseval; this is the field-generic `Gtz.sum_weight_mul_leverage`. -/
theorem sum_weight_mul_fieldLeverage {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) :
    ∑ atomIndex, design.weight atomIndex * fieldLeverageOf (design.atom atomIndex)
      = (rank : ℝ) := by
  have htrace := congrArg Matrix.trace design.isParseval
  rw [Matrix.trace_sum, Matrix.trace_one, Fintype.card_fin] at htrace
  have hterms : ∀ atomIndex : Fin size,
      Matrix.trace (((design.weight atomIndex : ℝ) : Scalar) • fieldAtom (design.atom atomIndex))
        = ((design.weight atomIndex * fieldLeverageOf (design.atom atomIndex) : ℝ) : Scalar) :=
    fun atomIndex => by
      rw [Matrix.trace_smul, smul_eq_mul, trace_fieldAtom, RCLike.ofReal_mul]
  rw [Finset.sum_congr rfl fun atomIndex _ => hterms atomIndex, ← RCLike.ofReal_sum] at htrace
  exact_mod_cast htrace

/-! ## The rank-one Schur criterion, field-generically

The repo's real `Gtz.posSemidef_sub_vecMulVec_iff` (`Gtz/LinAlg/SchurRankOne.lean`,
246 lines) is `ᵀ`-shaped and hand-polarized; its own header records
"Mathlib v4.32 has NO PSD Schur-complement block criterion".  That note looks in
the wrong file: `Matrix.PosDef.fromBlocks₁₁` and `Matrix.PosDef.fromBlocks₂₂`
(`Mathlib/LinearAlgebra/Matrix/PosDef.lean`) are field-generic PSD block
criteria.  Chaining the two on the SAME bordered matrix gives the criterion in
both directions in twenty lines. -/

/-- The atom as a column times its conjugate transpose. -/
theorem fieldAtom_eq_replicateCol_mul_conjTranspose {rank : ℕ} (vector : Fin rank → Scalar) :
    fieldAtom vector
      = Matrix.replicateCol (Fin 1) vector * (Matrix.replicateCol (Fin 1) vector)ᴴ := by
  rw [fieldAtom, Matrix.vecMulVec_eq (Fin 1), Matrix.conjTranspose_replicateCol]
  rfl

/-- A `1 × 1` matrix is positive semidefinite exactly when its entry is
nonnegative. -/
theorem posSemidef_oneByOne_iff (block : Matrix (Fin 1) (Fin 1) Scalar) :
    block.PosSemidef ↔ 0 ≤ block 0 0 := by
  have hdiagonal : block = Matrix.diagonal (fun _ : Fin 1 => block 0 0) := by
    ext rowIndex colIndex
    have hrow : rowIndex = 0 := Subsingleton.elim rowIndex 0
    have hcol : colIndex = 0 := Subsingleton.elim colIndex 0
    subst hrow; subst hcol
    simp
  rw [hdiagonal, Matrix.posSemidef_diagonal_iff]
  exact ⟨fun hall => hall 0, fun hzero _ => hzero⟩

/-- **The rank-one criterion.**  For a positive definite base, `base - g gᴴ` is
positive semidefinite exactly when `gᴴ base⁻¹ g ≤ 1`.  Both directions come from
chaining Mathlib's two block criteria on the bordered matrix
`[[base, g], [gᴴ, 1]]`. -/
theorem posSemidef_sub_fieldAtom_iff {rank : ℕ} (base : Matrix (Fin rank) (Fin rank) Scalar)
    (hbase : base.PosDef) (vector : Fin rank → Scalar) :
    (base - fieldAtom vector).PosSemidef
      ↔ star vector ⬝ᵥ (base⁻¹ *ᵥ vector) ≤ 1 := by
  classical
  haveI : Invertible base := hbase.isUnit.invertible
  haveI : Invertible (1 : Matrix (Fin 1) (Fin 1) Scalar) := invertibleOne
  set column : Matrix (Fin rank) (Fin 1) Scalar := Matrix.replicateCol (Fin 1) vector
    with hcolumn
  have hbordered := Matrix.PosDef.fromBlocks₂₂ (R' := Scalar) base column
    (D := (1 : Matrix (Fin 1) (Fin 1) Scalar)) Matrix.PosDef.one
  have hborderedLeft := Matrix.PosDef.fromBlocks₁₁ (R' := Scalar) column
    (1 : Matrix (Fin 1) (Fin 1) Scalar) hbase
  have hlower : base - column * (1 : Matrix (Fin 1) (Fin 1) Scalar)⁻¹ * columnᴴ
      = base - fieldAtom vector := by
    rw [hcolumn, fieldAtom_eq_replicateCol_mul_conjTranspose, inv_one, Matrix.mul_one]
  have hbilinear : (columnᴴ * base⁻¹ * column) 0 0 = star vector ⬝ᵥ (base⁻¹ *ᵥ vector) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcolumn,
      Matrix.replicateCol_apply, Matrix.mulVec, dotProduct, Pi.star_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hupperEntry : ((1 : Matrix (Fin 1) (Fin 1) Scalar) - columnᴴ * base⁻¹ * column) 0 0
      = 1 - star vector ⬝ᵥ (base⁻¹ *ᵥ vector) := by
    rw [Matrix.sub_apply, Matrix.one_apply_eq, hbilinear]
  rw [← hlower, ← hbordered, hborderedLeft, posSemidef_oneByOne_iff, hupperEntry,
    sub_nonneg]

/-! ## The two congruence transfers, field-generically -/

/-- The repo's hand-rolled `Gtz.posSemidef_congr_right` has a `ᴴ`-shaped Mathlib
counterpart needing no Hermitian hypothesis on the conjugated matrix. -/
theorem posSemidef_congr_conjTranspose {size : ℕ}
    {form basis : Matrix (Fin size) (Fin size) Scalar} (hbasis : IsUnit basis) :
    (basisᴴ * form * basis).PosSemidef ↔ form.PosSemidef :=
  Matrix.IsUnit.posSemidef_star_left_conjugate_iff hbasis

/-- The definite twin, same source. -/
theorem posDef_congr_conjTranspose {size : ℕ}
    {form basis : Matrix (Fin size) (Fin size) Scalar} (hbasis : IsUnit basis) :
    (basisᴴ * form * basis).PosDef ↔ form.PosDef :=
  Matrix.IsUnit.posDef_star_left_conjugate_iff hbasis

/-! ## The two flips: contraction and expansion

Both are needed by A1 in `Gtz/Design/ProjectionChart.lean`, which compares the
`size × size` chart block with the `rank × rank` atom sum. -/

/-- **The contraction flip**, rectangular and field-generic:
`1 - MᴴM ⪰ 0 ⟺ 1 - MMᴴ ⪰ 0`.  Both sides are the two Schur complements of the
SAME bordered matrix `[[1, Mᴴ], [M, 1]]`, so Mathlib's two block criteria give
the equivalence with no Cauchy–Schwarz by hand. -/
theorem posSemidef_one_sub_conjTranspose_mul_comm {rows cols : ℕ}
    (rect : Matrix (Fin rows) (Fin cols) Scalar) :
    ((1 : Matrix (Fin cols) (Fin cols) Scalar) - rectᴴ * rect).PosSemidef
      ↔ ((1 : Matrix (Fin rows) (Fin rows) Scalar) - rect * rectᴴ).PosSemidef := by
  classical
  haveI : Invertible (1 : Matrix (Fin cols) (Fin cols) Scalar) := invertibleOne
  haveI : Invertible (1 : Matrix (Fin rows) (Fin rows) Scalar) := invertibleOne
  have hleft := Matrix.PosDef.fromBlocks₁₁ (R' := Scalar) rectᴴ
    (1 : Matrix (Fin rows) (Fin rows) Scalar) (Matrix.PosDef.one)
  have hright := Matrix.PosDef.fromBlocks₂₂ (R' := Scalar)
    (1 : Matrix (Fin cols) (Fin cols) Scalar) rectᴴ
    (D := (1 : Matrix (Fin rows) (Fin rows) Scalar)) Matrix.PosDef.one
  simp only [Matrix.conjTranspose_conjTranspose, inv_one, Matrix.mul_one] at hleft hright
  rw [← hright, hleft]

/-- The gap of an expansive square matrix forces invertibility: `MᴴM ⪰ 1 ≻ 0`. -/
theorem isUnit_of_posSemidef_conjTranspose_mul_sub_one {size : ℕ}
    {square : Matrix (Fin size) (Fin size) Scalar}
    (hgap : (squareᴴ * square - 1).PosSemidef) : IsUnit square := by
  have hposDef : (squareᴴ * square).PosDef := by
    have hsplit := Matrix.PosDef.posSemidef_add hgap (Matrix.PosDef.one)
    rwa [sub_add_cancel] at hsplit
  have hdet : IsUnit (squareᴴ * square).det :=
    Matrix.isUnit_iff_isUnit_det _ |>.mp hposDef.isUnit
  rw [Matrix.det_mul] at hdet
  exact Matrix.isUnit_iff_isUnit_det _ |>.mpr (isUnit_of_mul_isUnit_right hdet)

/-- The inverse of a unit matrix is a unit. -/
theorem isUnit_nonsing_inv {size : ℕ} {square : Matrix (Fin size) (Fin size) Scalar}
    (hunit : IsUnit square) : IsUnit square⁻¹ :=
  Matrix.isUnit_nonsing_inv_iff.mpr hunit

/-- The conjugate transpose of a unit matrix is a unit. -/
theorem isUnit_conjTranspose {size : ℕ} {square : Matrix (Fin size) (Fin size) Scalar}
    (hunit : IsUnit square) : IsUnit squareᴴ := by
  refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
  rw [Matrix.det_conjTranspose]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).star

/-- The congruence that turns an expansion statement into a contraction
statement: for invertible `M`, conjugating `MᴴM - 1` by `M⁻¹` gives
`1 - (M Mᴴ)⁻¹`. -/
theorem conjTranspose_inv_mul_gap_mul_inv {size : ℕ}
    (square : Matrix (Fin size) (Fin size) Scalar) (hunit : IsUnit square) :
    (square⁻¹)ᴴ * (squareᴴ * square - 1) * square⁻¹ = 1 - (square * squareᴴ)⁻¹ := by
  have hdet : IsUnit square.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hright : square * square⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hleftAdj : (square⁻¹)ᴴ * squareᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hright, Matrix.conjTranspose_one]
  have hproduct : (square⁻¹)ᴴ * square⁻¹ = (square * squareᴴ)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.mul_inv_rev]
  calc (square⁻¹)ᴴ * (squareᴴ * square - 1) * square⁻¹
      = ((square⁻¹)ᴴ * squareᴴ) * (square * square⁻¹) - (square⁻¹)ᴴ * square⁻¹ := by
        noncomm_ring
    _ = 1 - (square * squareᴴ)⁻¹ := by
        rw [hleftAdj, hright, Matrix.one_mul, hproduct]

/-- **The expansion flip**, square and field-generic: `MᴴM ⪰ 1 ⟺ M Mᴴ ⪰ 1`.
Each side is congruent (by the relevant inverse) to a contraction statement, and
the two contraction statements are exchanged by
`posSemidef_one_sub_conjTranspose_mul_comm`.  This is the field-generic
counterpart of the repo's real `Gtz.posSemidef_transpose_mul_sub_one_comm`. -/
theorem posSemidef_conjTranspose_mul_sub_one_comm {size : ℕ}
    (square : Matrix (Fin size) (Fin size) Scalar) :
    (squareᴴ * square - 1).PosSemidef ↔ (square * squareᴴ - 1).PosSemidef := by
  have hforward : ∀ candidate : Matrix (Fin size) (Fin size) Scalar,
      (candidateᴴ * candidate - 1).PosSemidef → (candidate * candidateᴴ - 1).PosSemidef := by
    intro candidate hgap
    have hunit : IsUnit candidate := isUnit_of_posSemidef_conjTranspose_mul_sub_one hgap
    have hunitAdj : IsUnit candidateᴴ := isUnit_conjTranspose hunit
    have hinvUnit : IsUnit candidate⁻¹ := isUnit_nonsing_inv hunit
    have hinvAdjUnit : IsUnit (candidateᴴ)⁻¹ := isUnit_nonsing_inv hunitAdj
    have hcontract : ((1 : Matrix (Fin size) (Fin size) Scalar)
        - (candidate * candidateᴴ)⁻¹).PosSemidef := by
      rw [← conjTranspose_inv_mul_gap_mul_inv candidate hunit]
      exact (posSemidef_congr_conjTranspose hinvUnit).mpr hgap
    have hshapeLeft : (candidate * candidateᴴ)⁻¹ = (candidate⁻¹)ᴴ * candidate⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv, Matrix.mul_inv_rev]
    have hshapeRight : (candidateᴴ * candidate)⁻¹ = candidate⁻¹ * (candidate⁻¹)ᴴ := by
      rw [Matrix.conjTranspose_nonsing_inv, Matrix.mul_inv_rev]
    rw [hshapeLeft] at hcontract
    have hflipped := (posSemidef_one_sub_conjTranspose_mul_comm candidate⁻¹).mp hcontract
    rw [← hshapeRight] at hflipped
    have hidentityAdj := conjTranspose_inv_mul_gap_mul_inv candidateᴴ hunitAdj
    rw [Matrix.conjTranspose_conjTranspose] at hidentityAdj
    rw [← hidentityAdj] at hflipped
    exact (posSemidef_congr_conjTranspose hinvAdjUnit).mp hflipped
  refine ⟨hforward square, fun hgap => ?_⟩
  have hback := hforward squareᴴ (by rwa [Matrix.conjTranspose_conjTranspose])
  rwa [Matrix.conjTranspose_conjTranspose] at hback

/-! ## The co-Parseval operator -/

/-- `coParsevalOperator = Σ_c (1 - t_c) g_c g_cᴴ`. -/
noncomputable def coParsevalOperator {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) : Matrix (Fin rank) (Fin rank) Scalar :=
  ∑ atomIndex, ((1 - design.weight atomIndex : ℝ) : Scalar)
    • fieldAtom (design.atom atomIndex)

/-- **Parseval read as a complement dictionary**: the co-Parseval operator is the
universal atom sum minus the identity. -/
theorem coParsevalOperator_eq_universalGap {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) :
    coParsevalOperator design = fieldSubsetSum design Finset.univ - 1 := by
  rw [coParsevalOperator, fieldSubsetSum, ← design.isParseval, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [RCLike.ofReal_sub, sub_smul, RCLike.ofReal_one, one_smul]

theorem coParsevalOperator_posSemidef {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) :
    (coParsevalOperator design).PosSemidef := by
  rw [coParsevalOperator]
  refine Matrix.posSemidef_sum Finset.univ fun atomIndex _ => ?_
  refine (fieldAtom_posSemidef (design.atom atomIndex)).smul ?_
  exact RCLike.ofReal_nonneg.mpr (by linarith [fieldWeight_le_one design atomIndex])

/-- **The co-Parseval operator is positive definite** once there are two atoms.
Subtracting `shift · 1 = shift · Σ_c t_c g_c g_cᴴ` leaves
`Σ_c ((1 - t_c) - shift · t_c) g_c g_cᴴ`, which is positive semidefinite for
`shift = min_c (1 - t_c)/t_c > 0`; the sum of that with `shift · 1` is positive
definite. -/
theorem coParsevalOperator_posDef {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (hsize : 2 ≤ size) :
    (coParsevalOperator design).PosDef := by
  classical
  haveI : Nonempty (Fin size) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨argmin, hargmin⟩ :=
    Finite.exists_min (fun index => (1 - design.weight index) / design.weight index)
  set shift : ℝ := (1 - design.weight argmin) / design.weight argmin with hshift
  have hshiftPos : 0 < shift := by
    rw [hshift]
    exact div_pos (by linarith [fieldWeight_lt_one design hsize argmin])
      (design.weight_pos argmin)
  have hcoefNonneg : ∀ index : Fin size,
      0 ≤ (1 - design.weight index) - shift * design.weight index := by
    intro index
    have hbound : shift ≤ (1 - design.weight index) / design.weight index := hargmin index
    rw [le_div_iff₀ (design.weight_pos index)] at hbound
    linarith
  have hgap : (coParsevalOperator design
      - Matrix.diagonal (fun _ : Fin rank => (shift : Scalar))).PosSemidef := by
    have hidentity : Matrix.diagonal (fun _ : Fin rank => (shift : Scalar))
        = ∑ index, ((shift * design.weight index : ℝ) : Scalar)
            • fieldAtom (design.atom index) := by
      have hpull : ∑ index, ((shift * design.weight index : ℝ) : Scalar)
            • fieldAtom (design.atom index)
          = (shift : Scalar) • ∑ index, ((design.weight index : ℝ) : Scalar)
              • fieldAtom (design.atom index) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun index _ => by rw [RCLike.ofReal_mul, smul_smul]
      rw [hpull, design.isParseval, Matrix.smul_one_eq_diagonal]
    have hshape : coParsevalOperator design
          - Matrix.diagonal (fun _ : Fin rank => (shift : Scalar))
        = ∑ index, (((1 - design.weight index) - shift * design.weight index : ℝ) : Scalar)
            • fieldAtom (design.atom index) := by
      rw [coParsevalOperator, hidentity, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun index _ => ?_
      rw [← sub_smul]
      congr 1
      push_cast
      ring
    rw [hshape]
    refine Matrix.posSemidef_sum Finset.univ fun index _ => ?_
    exact (fieldAtom_posSemidef (design.atom index)).smul
      (RCLike.ofReal_nonneg.mpr (hcoefNonneg index))
  have hdiagonalPosDef : (Matrix.diagonal (fun _ : Fin rank => (shift : Scalar))).PosDef :=
    Matrix.posDef_diagonal_iff.mpr fun _ => RCLike.ofReal_pos.mpr hshiftPos
  have hsplit := Matrix.PosDef.posSemidef_add hgap hdiagonalPosDef
  rwa [sub_add_cancel] at hsplit

/-! ## A5: the square rung -/

/-- **A5.**  At `size = rank` the universal subset dominates: the excess is
`Σ_c (1 - t_c) g_c g_cᴴ`, a nonnegative combination of positive semidefinite
atoms.  Unconditional in the rank, including the degenerate rank zero.  This is
the field-generic `Gtz.gtzWeighted_square`. -/
theorem fieldGtzWeighted_square (rank : ℕ) : FieldGtzWeighted Scalar rank rank := by
  intro design
  refine ⟨Finset.univ, by rw [Finset.card_univ, Fintype.card_fin], ?_⟩
  show (fieldSubsetSum design Finset.univ - 1).PosSemidef
  rw [← coParsevalOperator_eq_universalGap]
  exact coParsevalOperator_posSemidef design

/-! ## The vacuity boundary: below the rank, and at size zero, there is no design -/

/-- **At size zero there is no design, at any rank.**  The weights would have to
sum to one over an empty index set, i.e. `0 = 1`.  Shipped as a theorem rather
than described in prose, because the `size = rank = 0` cell of
`fieldGtzWeighted_square` is otherwise easy to mistake for a witness: the theorem
holds there, but VACUOUSLY, and the `0 × 0` excess it would exhibit belongs to no
design. -/
theorem fieldWeightedDesign_zero_size_isEmpty (rank : ℕ) :
    IsEmpty (FieldWeightedDesign Scalar 0 rank) := by
  refine ⟨fun design => ?_⟩
  have hsum := design.weight_sum_one
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  exact absurd hsum zero_ne_one

/-- **Parseval forces `rank ≤ size`.**  The map sending a coefficient vector to
its list of atom pairings is injective — a vector killed by every atom is killed
by Parseval, hence zero — so `rank ≤ size` by rank-nullity.  Consequence: any
"iff" statement about `FieldGtzWeighted Scalar size rank` below `size = rank` is
true for a VACUOUS reason, and the headline docstrings say so. -/
theorem rank_le_size_of_fieldDesign {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) : rank ≤ size := by
  classical
  set pairWithAtoms : (Fin rank → Scalar) →ₗ[Scalar] (Fin size → Scalar) :=
    { toFun := fun coefficient atomIndex => star (design.atom atomIndex) ⬝ᵥ coefficient
      map_add' := fun left right => by
        funext atomIndex
        simp [dotProduct_add]
      map_smul' := fun scalar vector => by
        funext atomIndex
        simp [dotProduct_smul] } with hpairWithAtoms
  have hinjective : Function.Injective pairWithAtoms := by
    refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun coefficient hzero => ?_)
    have hall : ∀ atomIndex, star (design.atom atomIndex) ⬝ᵥ coefficient = 0 :=
      fun atomIndex => congrFun hzero atomIndex
    have hparseval := congrArg (fun form => star coefficient ⬝ᵥ (form *ᵥ coefficient))
      design.isParseval
    simp only [Matrix.one_mulVec] at hparseval
    have hexpand : star coefficient
        ⬝ᵥ ((∑ atomIndex, ((design.weight atomIndex : ℝ) : Scalar)
              • fieldAtom (design.atom atomIndex)) *ᵥ coefficient) = 0 := by
      rw [Matrix.sum_mulVec, dotProduct_sum]
      refine Finset.sum_eq_zero fun atomIndex _ => ?_
      have hatom : (fieldAtom (design.atom atomIndex)) *ᵥ coefficient
          = (star (design.atom atomIndex) ⬝ᵥ coefficient) • design.atom atomIndex := by
        funext coordinate
        simp only [fieldAtom, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
          Pi.smul_apply, smul_eq_mul, Pi.star_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [Matrix.smul_mulVec, hatom, hall atomIndex, zero_smul, smul_zero, dotProduct_zero]
    rw [hexpand] at hparseval
    exact dotProduct_star_self_eq_zero.mp hparseval.symm
  have hle := LinearMap.finrank_le_finrank_of_injective hinjective
  rwa [Module.finrank_pi, Module.finrank_pi, Fintype.card_fin, Fintype.card_fin] at hle

end Gtz
