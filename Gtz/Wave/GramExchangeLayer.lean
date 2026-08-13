import Gtz.Wave.SupportTwoClosure
import Gtz.Reduction.MaximalVolume

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The Gram exchange layer — the second exchange law of the basis frame

The representation `P B = B M` carries the chart onto the coefficient
frame.  The frame kept the left-inverse metric `H = L Ξ Lᵀ` but never
kept the direction Gram `Γ = Bᵀ B`.  This module lands the Gram side.
The product `Γ M` equals `Bᵀ P B`, thus it is symmetric and positive
semidefinite.  The complement `Γ - Γ M` equals `(1 - M)ᵀ Γ (1 - M)`,
thus it is also positive semidefinite.  The diagonal reads give the
energy window `0 ≤ value + Σ w q² ≤ 1` at each basis slot.

Every numeric frame leak of the pattern kills traces to the absence of
this layer.  The closure modules consume the entry calculus: the
symmetric cross sums, the support reads, the two-by-two minors, and the
trace window.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.gram_exchange` — **THE SECOND EXCHANGE LAW** `Γ M = Mᵀ (Γ M)`.
* `Gtz.gram_exchange_posSemidef`, `Gtz.gram_complement_posSemidef` —
  the two positivity laws.
* `Gtz.gram_exchange_diag_read` — the diagonal read
  `(Γ M)_jj = value + Σ w q_j²`.
* `Gtz.gram_energy_window_upper` — the new energy ceiling
  `value + Σ w q_j² ≤ 1`.
* `Gtz.gram_exchange_read_of_support` — the off-diagonal support read.
* `Gtz.gram_exchange_entry_sq_le`, `Gtz.gram_complement_entry_sq_le` —
  the two-by-two minors.
* `Gtz.gram_exchange_trace_read` — the trace read with its window.

## Vacuity

Nothing here quantifies over a crux.  The algebra layer holds at every
symmetric idempotent with a representation.  The read layer holds at
every stationary datum with a chosen basis.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the direction Gram

The Gram matrix of the chosen basis directions.  Each entry is one dot
product of two tight directions, thus each entry is frame-computable
from the coordinates on the shared support. -/

/-- The direction Gram `Γ = Bᵀ B` of the chosen basis columns. -/
noncomputable def basisGram (tightDir : activeIndex → (Fin size → ℝ))
    (basisLabel : Fin basisCount → activeIndex) :
    Matrix (Fin basisCount) (Fin basisCount) ℝ :=
  (tightBasisColumns tightDir basisLabel)ᵀ * tightBasisColumns tightDir basisLabel

/-- Each Gram entry is the dot product of the two basis directions. -/
theorem basisGram_apply (basisLabel : Fin basisCount → activeIndex)
    (rowSlot colSlot : Fin basisCount) :
    basisGram tightDir basisLabel rowSlot colSlot
      = tightDir (basisLabel rowSlot) ⬝ᵥ tightDir (basisLabel colSlot) := by
  rw [basisGram, Matrix.mul_apply, dotProduct]
  exact Finset.sum_congr rfl fun atomIndex _ => by rw [Matrix.transpose_apply]; rfl

/-- The Gram entry as an explicit coordinate sum. -/
theorem basisGram_apply_sum (basisLabel : Fin basisCount → activeIndex)
    (rowSlot colSlot : Fin basisCount) :
    basisGram tightDir basisLabel rowSlot colSlot
      = ∑ atomIndex : Fin size, tightDir (basisLabel rowSlot) atomIndex
          * tightDir (basisLabel colSlot) atomIndex := by
  rw [basisGram_apply]
  rfl

/-- The Gram entry restricted to the row block: the coordinate sum runs
on the support of the row direction only. -/
theorem basisGram_apply_support_left
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {rowSlot colSlot : Fin basisCount} (hmem : basisLabel rowSlot ∈ activeSet) :
    basisGram tightDir basisLabel rowSlot colSlot
      = ∑ atomIndex ∈ activeSubset (basisLabel rowSlot),
          tightDir (basisLabel rowSlot) atomIndex
            * tightDir (basisLabel colSlot) atomIndex := by
  rw [basisGram_apply_sum]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro atomIndex _ hnotMem
  rw [hdata.tightDir_support (basisLabel rowSlot) hmem atomIndex hnotMem, zero_mul]

/-- The Gram entry restricted to the column block: the coordinate sum
runs on the support of the column direction only. -/
theorem basisGram_apply_support_right
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {rowSlot colSlot : Fin basisCount} (hmem : basisLabel colSlot ∈ activeSet) :
    basisGram tightDir basisLabel rowSlot colSlot
      = ∑ atomIndex ∈ activeSubset (basisLabel colSlot),
          tightDir (basisLabel rowSlot) atomIndex
            * tightDir (basisLabel colSlot) atomIndex := by
  rw [basisGram_apply_sum]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro atomIndex _ hnotMem
  rw [hdata.tightDir_support (basisLabel colSlot) hmem atomIndex hnotMem, mul_zero]

/-- The direction Gram is symmetric. -/
theorem basisGram_transpose (basisLabel : Fin basisCount → activeIndex) :
    (basisGram tightDir basisLabel)ᵀ = basisGram tightDir basisLabel := by
  rw [basisGram, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- The direction Gram is positive semidefinite. -/
theorem basisGram_posSemidef (basisLabel : Fin basisCount → activeIndex) :
    (basisGram tightDir basisLabel).PosSemidef := by
  have hpsd :=
    Matrix.posSemidef_conjTranspose_mul_self (tightBasisColumns tightDir basisLabel)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hpsd

/-- The Gram diagonal at an active slot is one: the unit norm of the
tight direction. -/
theorem basisGram_diagonal_of_mem
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {slotIndex : Fin basisCount} (hmem : basisLabel slotIndex ∈ activeSet) :
    basisGram tightDir basisLabel slotIndex slotIndex = 1 := by
  rw [basisGram_apply]
  exact hdata.tightDir_unit (basisLabel slotIndex) hmem

/-- The Gram entry window: each off-diagonal square is at most one. -/
theorem basisGram_entry_sq_le_one
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {rowSlot colSlot : Fin basisCount}
    (hmemRow : basisLabel rowSlot ∈ activeSet)
    (hmemCol : basisLabel colSlot ∈ activeSet) :
    basisGram tightDir basisLabel rowSlot colSlot ^ 2 ≤ 1 := by
  have hminor := sq_le_mul_diag_of_posSemidef
    (basisGram_posSemidef basisLabel (tightDir := tightDir)) rowSlot colSlot
  rwa [basisGram_diagonal_of_mem hdata basisLabel hmemRow,
    basisGram_diagonal_of_mem hdata basisLabel hmemCol, mul_one] at hminor

/-! ## Layer 2 — the exchange product

The representation contracts the chart between the basis columns.  The
product `Γ M` is the contracted chart `Bᵀ P B`, thus the square shape
`(P B)ᵀ (P B)` makes it symmetric and positive semidefinite.  The same
shape gives the metric idempotency `Γ M M = Γ M` without any
idempotency hypothesis on `M` itself. -/

/-- The chart entry against a basis column, read as a matrix-vector
product. -/
theorem projection_mul_basis_apply (basisLabel : Fin basisCount → activeIndex)
    (atomIndex : Fin size) (slotIndex : Fin basisCount) :
    (projection * tightBasisColumns tightDir basisLabel) atomIndex slotIndex
      = (projection *ᵥ tightDir (basisLabel slotIndex)) atomIndex := by
  rw [Matrix.mul_apply]
  rfl

/-- **THE COLUMN PRODUCT.**  The contracted chart is the Gram times the
coefficient matrix: `Bᵀ (P B) = Γ M`. -/
theorem gram_column_product (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M) :
    (tightBasisColumns tightDir basisLabel)ᵀ
        * (projection * tightBasisColumns tightDir basisLabel)
      = basisGram tightDir basisLabel * M := by
  rw [hrepresentation, basisGram, Matrix.mul_assoc]

/-- **THE SQUARE SHAPE.**  The exchange product is the square of the
projected columns: `Γ M = (P B)ᵀ (P B)`. -/
theorem gram_rep_square (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M) :
    basisGram tightDir basisLabel * M
      = (projection * tightBasisColumns tightDir basisLabel)ᵀ
        * (projection * tightBasisColumns tightDir basisLabel) := by
  have hkey : (projection * tightBasisColumns tightDir basisLabel)ᵀ
      * (projection * tightBasisColumns tightDir basisLabel)
      = (tightBasisColumns tightDir basisLabel)ᵀ
        * (projection * tightBasisColumns tightDir basisLabel) := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc projectionᵀ projection (tightBasisColumns tightDir basisLabel),
      hsym, hidem]
  rw [hkey, gram_column_product basisLabel hrepresentation]

/-- **THE SECOND EXCHANGE LAW.**  The exchange product reproduces
itself under the coefficient conjugation: `Γ M = Mᵀ (Γ M)`. -/
theorem gram_exchange (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M) :
    basisGram tightDir basisLabel * M
      = Mᵀ * (basisGram tightDir basisLabel * M) := by
  conv_lhs => rw [gram_rep_square basisLabel hsym hidem hrepresentation, hrepresentation,
    Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (tightBasisColumns tightDir basisLabel)ᵀ
      (tightBasisColumns tightDir basisLabel) M]
  rw [basisGram]

/-- The exchange product is symmetric. -/
theorem gram_exchange_transpose (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M) :
    (basisGram tightDir basisLabel * M)ᵀ
      = basisGram tightDir basisLabel * M := by
  rw [gram_rep_square basisLabel hsym hidem hrepresentation, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- The exchange entries in symmetric position agree. -/
theorem gram_exchange_apply_symm (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (rowSlot colSlot : Fin basisCount) :
    (basisGram tightDir basisLabel * M) rowSlot colSlot
      = (basisGram tightDir basisLabel * M) colSlot rowSlot := by
  conv_lhs => rw [← gram_exchange_transpose basisLabel hsym hidem hrepresentation]
  rw [Matrix.transpose_apply]

/-- **THE SYMMETRIC CROSS SUMS.**  The entry symmetry of the exchange
product, in the consumable sum form. -/
theorem gram_exchange_sum_symm (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (rowSlot colSlot : Fin basisCount) :
    ∑ middleSlot : Fin basisCount,
        basisGram tightDir basisLabel rowSlot middleSlot * M middleSlot colSlot
      = ∑ middleSlot : Fin basisCount,
          basisGram tightDir basisLabel colSlot middleSlot * M middleSlot rowSlot := by
  have hsymm :=
    gram_exchange_apply_symm basisLabel hsym hidem hrepresentation rowSlot colSlot
  rwa [Matrix.mul_apply, Matrix.mul_apply] at hsymm

/-- The exchange product is positive semidefinite. -/
theorem gram_exchange_posSemidef (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M) :
    (basisGram tightDir basisLabel * M).PosSemidef := by
  rw [gram_rep_square basisLabel hsym hidem hrepresentation]
  have hpsd := Matrix.posSemidef_conjTranspose_mul_self
    (projection * tightBasisColumns tightDir basisLabel)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hpsd

/-- Each exchange entry is the dot product of the two projected
directions. -/
theorem gram_exchange_projected_dot (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (rowSlot colSlot : Fin basisCount) :
    (basisGram tightDir basisLabel * M) rowSlot colSlot
      = (projection *ᵥ tightDir (basisLabel rowSlot))
        ⬝ᵥ (projection *ᵥ tightDir (basisLabel colSlot)) := by
  rw [gram_rep_square basisLabel hsym hidem hrepresentation, Matrix.mul_apply, dotProduct]
  exact Finset.sum_congr rfl fun atomIndex _ => by
    rw [Matrix.transpose_apply, projection_mul_basis_apply basisLabel,
      projection_mul_basis_apply basisLabel]

/-- **THE METRIC IDEMPOTENCY.**  The exchange product absorbs one more
coefficient factor: `Γ M M = Γ M`. -/
theorem gram_exchange_mul_self (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M) :
    basisGram tightDir basisLabel * M * M
      = basisGram tightDir basisLabel * M := by
  rw [← gram_column_product basisLabel hrepresentation,
    Matrix.mul_assoc (tightBasisColumns tightDir basisLabel)ᵀ
      (projection * tightBasisColumns tightDir basisLabel) M,
    Matrix.mul_assoc projection (tightBasisColumns tightDir basisLabel) M,
    ← hrepresentation,
    ← Matrix.mul_assoc projection projection (tightBasisColumns tightDir basisLabel),
    hidem]

/-! ## Layer 3 — the complement

The Gram minus the exchange product is the conjugated Gram of the
complement coefficient `1 - M`.  Thus the complement is positive
semidefinite, and the exchange diagonal sits in the unit window. -/

/-- The coefficient transpose moves across the Gram:
`Mᵀ Γ = Γ M`. -/
theorem gram_transpose_commute (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M) :
    Mᵀ * basisGram tightDir basisLabel
      = basisGram tightDir basisLabel * M := by
  have htranspose : (basisGram tightDir basisLabel * M)ᵀ
      = Mᵀ * (basisGram tightDir basisLabel)ᵀ :=
    Matrix.transpose_mul _ _
  rw [gram_exchange_transpose basisLabel hsym hidem hrepresentation,
    basisGram_transpose basisLabel] at htranspose
  exact htranspose.symm

/-- **THE COMPLEMENT LAW.**  The Gram minus the exchange product is the
complement conjugation: `Γ - Γ M = (1 - M)ᵀ Γ (1 - M)`. -/
theorem gram_complement_conj (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M) :
    basisGram tightDir basisLabel - basisGram tightDir basisLabel * M
      = (1 - M)ᵀ * basisGram tightDir basisLabel * (1 - M) := by
  have hexpand : (1 - M)ᵀ * basisGram tightDir basisLabel * (1 - M)
      = basisGram tightDir basisLabel - basisGram tightDir basisLabel * M
        - (Mᵀ * basisGram tightDir basisLabel
            - Mᵀ * basisGram tightDir basisLabel * M) := by
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [hexpand, gram_transpose_commute basisLabel hsym hidem hrepresentation,
    gram_exchange_mul_self basisLabel hidem hrepresentation, sub_self, sub_zero]

/-- The complement is positive semidefinite. -/
theorem gram_complement_posSemidef (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M) :
    (basisGram tightDir basisLabel
      - basisGram tightDir basisLabel * M).PosSemidef := by
  rw [gram_complement_conj basisLabel hsym hidem hrepresentation]
  have hpsd := (basisGram_posSemidef basisLabel
    (tightDir := tightDir)).conjTranspose_mul_mul_same (1 - M)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hpsd

/-- The exchange diagonal is nonnegative. -/
theorem gram_exchange_diag_nonneg (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (slotIndex : Fin basisCount) :
    0 ≤ (basisGram tightDir basisLabel * M) slotIndex slotIndex :=
  (gram_exchange_posSemidef basisLabel hsym hidem hrepresentation).diag_nonneg

/-- The exchange diagonal at an active slot is at most one. -/
theorem gram_exchange_diag_le_one
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {slotIndex : Fin basisCount} (hmem : basisLabel slotIndex ∈ activeSet) :
    (basisGram tightDir basisLabel * M) slotIndex slotIndex ≤ 1 := by
  have hcomplement := (gram_complement_posSemidef basisLabel hdata.isSymmetric
    hdata.isIdempotent hrepresentation).diag_nonneg (i := slotIndex)
  rw [Matrix.sub_apply, basisGram_diagonal_of_mem hdata basisLabel hmem]
    at hcomplement
  linarith

/-! ## Layer 4 — the diagonal reads and the energy window

The tight equation evaluates the exchange diagonal: the value plus the
weighted energy of the slot direction.  The unit window of layer 3 then
squeezes the energy from the two sides.  The floor reproves the landed
energy floor.  The ceiling is new supply. -/

/-- **THE DIAGONAL READ.**  The exchange diagonal at an active slot is
the value plus the weighted energy. -/
theorem gram_exchange_diag_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {slotIndex : Fin basisCount} (hmem : basisLabel slotIndex ∈ activeSet) :
    (basisGram tightDir basisLabel * M) slotIndex slotIndex
      = value + ∑ atomIndex : Fin size,
          weight atomIndex * tightDir (basisLabel slotIndex) atomIndex ^ 2 := by
  have hentry : (basisGram tightDir basisLabel * M) slotIndex slotIndex
      = tightDir (basisLabel slotIndex)
        ⬝ᵥ (projection *ᵥ tightDir (basisLabel slotIndex)) := by
    rw [← gram_column_product basisLabel hrepresentation, Matrix.mul_apply, dotProduct]
    exact Finset.sum_congr rfl fun atomIndex _ => by
      rw [Matrix.transpose_apply, projection_mul_basis_apply basisLabel]
      rfl
  rw [hentry, tight_energy_read hdata hmem]

/-- **THE ENERGY FLOOR, GRAM ROUTE.**  The value plus the weighted
energy is nonnegative at each active slot. -/
theorem gram_energy_window_lower
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {slotIndex : Fin basisCount} (hmem : basisLabel slotIndex ∈ activeSet) :
    0 ≤ value + ∑ atomIndex : Fin size,
        weight atomIndex * tightDir (basisLabel slotIndex) atomIndex ^ 2 := by
  rw [← gram_exchange_diag_read hdata basisLabel hrepresentation hmem]
  exact gram_exchange_diag_nonneg basisLabel hdata.isSymmetric hdata.isIdempotent
    hrepresentation slotIndex

/-- **THE ENERGY CEILING.**  The value plus the weighted energy is at
most one at each active slot. -/
theorem gram_energy_window_upper
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {slotIndex : Fin basisCount} (hmem : basisLabel slotIndex ∈ activeSet) :
    value + ∑ atomIndex : Fin size,
        weight atomIndex * tightDir (basisLabel slotIndex) atomIndex ^ 2 ≤ 1 := by
  rw [← gram_exchange_diag_read hdata basisLabel hrepresentation hmem]
  exact gram_exchange_diag_le_one hdata basisLabel hrepresentation hmem

/-! ## Layer 5 — the off-diagonal reads

When the row direction is supported in the column block, the tight
equation evaluates the full exchange entry.  The entry symmetry then
constrains the transposed entry from the other side. -/

/-- **THE SUPPORT READ.**  When the row direction is supported in the
column block, the exchange entry is the value times the Gram entry plus
the weighted overlap. -/
theorem gram_exchange_read_of_support
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {rowSlot colSlot : Fin basisCount}
    (hmem : basisLabel colSlot ∈ activeSet)
    (hsupport : ∀ atomIndex : Fin size,
      atomIndex ∉ activeSubset (basisLabel colSlot) →
        tightDir (basisLabel rowSlot) atomIndex = 0) :
    (basisGram tightDir basisLabel * M) rowSlot colSlot
      = value * basisGram tightDir basisLabel rowSlot colSlot
        + ∑ atomIndex : Fin size,
            weight atomIndex * (tightDir (basisLabel rowSlot) atomIndex
              * tightDir (basisLabel colSlot) atomIndex) := by
  have hterm : ∀ atomIndex : Fin size,
      tightDir (basisLabel rowSlot) atomIndex
          * (projection *ᵥ tightDir (basisLabel colSlot)) atomIndex
        = value * (tightDir (basisLabel rowSlot) atomIndex
              * tightDir (basisLabel colSlot) atomIndex)
          + weight atomIndex * (tightDir (basisLabel rowSlot) atomIndex
              * tightDir (basisLabel colSlot) atomIndex) := by
    intro atomIndex
    by_cases hin : atomIndex ∈ activeSubset (basisLabel colSlot)
    · rw [projection_mulVec_tightDir_of_mem hdata hmem hin]
      ring
    · rw [hsupport atomIndex hin]
      ring
  have hentry : (basisGram tightDir basisLabel * M) rowSlot colSlot
      = ∑ atomIndex : Fin size, tightDir (basisLabel rowSlot) atomIndex
          * (projection *ᵥ tightDir (basisLabel colSlot)) atomIndex := by
    rw [← gram_column_product basisLabel hrepresentation, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun atomIndex _ => by
      rw [Matrix.transpose_apply, projection_mul_basis_apply basisLabel]
      rfl
  calc (basisGram tightDir basisLabel * M) rowSlot colSlot
      = ∑ atomIndex : Fin size,
          (value * (tightDir (basisLabel rowSlot) atomIndex
              * tightDir (basisLabel colSlot) atomIndex)
            + weight atomIndex * (tightDir (basisLabel rowSlot) atomIndex
              * tightDir (basisLabel colSlot) atomIndex)) := by
        rw [hentry]
        exact Finset.sum_congr rfl fun atomIndex _ => hterm atomIndex
    _ = value * basisGram tightDir basisLabel rowSlot colSlot
        + ∑ atomIndex : Fin size,
            weight atomIndex * (tightDir (basisLabel rowSlot) atomIndex
              * tightDir (basisLabel colSlot) atomIndex) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, basisGram_apply_sum]

/-- **THE SYMMETRIC SUPPORT READ.**  The support read also evaluates
the transposed exchange entry. -/
theorem gram_exchange_symm_read_of_support
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {rowSlot colSlot : Fin basisCount}
    (hmem : basisLabel colSlot ∈ activeSet)
    (hsupport : ∀ atomIndex : Fin size,
      atomIndex ∉ activeSubset (basisLabel colSlot) →
        tightDir (basisLabel rowSlot) atomIndex = 0) :
    (basisGram tightDir basisLabel * M) colSlot rowSlot
      = value * basisGram tightDir basisLabel rowSlot colSlot
        + ∑ atomIndex : Fin size,
            weight atomIndex * (tightDir (basisLabel rowSlot) atomIndex
              * tightDir (basisLabel colSlot) atomIndex) := by
  rw [← gram_exchange_apply_symm basisLabel hdata.isSymmetric hdata.isIdempotent
    hrepresentation rowSlot colSlot]
  exact gram_exchange_read_of_support hdata basisLabel hrepresentation hmem hsupport

/-! ## Layer 6 — the two-by-two minors

The two positivity laws give one minor inequality for each entry pair.
At active slots the Gram diagonal is one, and the complement minor
becomes the unit-window product bound. -/

/-- The exchange minor: each entry square is bounded by the diagonal
product. -/
theorem gram_exchange_entry_sq_le (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (rowSlot colSlot : Fin basisCount) :
    (basisGram tightDir basisLabel * M) rowSlot colSlot ^ 2
      ≤ (basisGram tightDir basisLabel * M) rowSlot rowSlot
        * (basisGram tightDir basisLabel * M) colSlot colSlot :=
  sq_le_mul_diag_of_posSemidef
    (gram_exchange_posSemidef basisLabel hsym hidem hrepresentation) rowSlot colSlot

/-- The complement minor: each complement entry square is bounded by
the complement diagonal product. -/
theorem gram_complement_entry_sq_le (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (rowSlot colSlot : Fin basisCount) :
    (basisGram tightDir basisLabel rowSlot colSlot
        - (basisGram tightDir basisLabel * M) rowSlot colSlot) ^ 2
      ≤ (basisGram tightDir basisLabel rowSlot rowSlot
          - (basisGram tightDir basisLabel * M) rowSlot rowSlot)
        * (basisGram tightDir basisLabel colSlot colSlot
          - (basisGram tightDir basisLabel * M) colSlot colSlot) := by
  have hminor := sq_le_mul_diag_of_posSemidef
    (gram_complement_posSemidef basisLabel hsym hidem hrepresentation) rowSlot colSlot
  simpa [Matrix.sub_apply] using hminor

/-- The complement minor at active slots: the unit-window product
bound. -/
theorem gram_complement_entry_sq_le_of_unit
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {rowSlot colSlot : Fin basisCount}
    (hmemRow : basisLabel rowSlot ∈ activeSet)
    (hmemCol : basisLabel colSlot ∈ activeSet) :
    (basisGram tightDir basisLabel rowSlot colSlot
        - (basisGram tightDir basisLabel * M) rowSlot colSlot) ^ 2
      ≤ (1 - (basisGram tightDir basisLabel * M) rowSlot rowSlot)
        * (1 - (basisGram tightDir basisLabel * M) colSlot colSlot) := by
  have hminor := gram_complement_entry_sq_le basisLabel hdata.isSymmetric
    hdata.isIdempotent hrepresentation rowSlot colSlot
  rwa [basisGram_diagonal_of_mem hdata basisLabel hmemRow,
    basisGram_diagonal_of_mem hdata basisLabel hmemCol] at hminor

/-! ## Layer 7 — the trace layer

The trace of the exchange product sums the diagonal reads.  The unit
windows bound the trace between zero and the slot count, and the sum
form is the failure-sum supply of the closure kills. -/

/-- **THE TRACE READ.**  The exchange trace is the slot count times the
value plus the total weighted energy. -/
theorem gram_exchange_trace_read
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hall : ∀ slotIndex : Fin basisCount, basisLabel slotIndex ∈ activeSet) :
    Matrix.trace (basisGram tightDir basisLabel * M)
      = (basisCount : ℝ) * value
        + ∑ slotIndex : Fin basisCount, ∑ atomIndex : Fin size,
            weight atomIndex * tightDir (basisLabel slotIndex) atomIndex ^ 2 := by
  have hsum : ∑ slotIndex : Fin basisCount,
      (basisGram tightDir basisLabel * M) slotIndex slotIndex
      = ∑ slotIndex : Fin basisCount,
          (value + ∑ atomIndex : Fin size,
            weight atomIndex * tightDir (basisLabel slotIndex) atomIndex ^ 2) :=
    Finset.sum_congr rfl fun slotIndex _ =>
      gram_exchange_diag_read hdata basisLabel hrepresentation (hall slotIndex)
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [hsum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- The exchange trace is nonnegative. -/
theorem gram_exchange_trace_nonneg (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsym : projectionᵀ = projection)
    (hidem : projection * projection = projection)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M) :
    0 ≤ Matrix.trace (basisGram tightDir basisLabel * M) := by
  rw [Matrix.trace]
  refine Finset.sum_nonneg fun slotIndex _ => ?_
  exact gram_exchange_diag_nonneg basisLabel hsym hidem hrepresentation slotIndex

/-- The exchange trace is at most the slot count. -/
theorem gram_exchange_trace_le_card
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hall : ∀ slotIndex : Fin basisCount, basisLabel slotIndex ∈ activeSet) :
    Matrix.trace (basisGram tightDir basisLabel * M) ≤ (basisCount : ℝ) := by
  rw [Matrix.trace]
  calc ∑ slotIndex : Fin basisCount,
        Matrix.diag (basisGram tightDir basisLabel * M) slotIndex
      ≤ ∑ _slotIndex : Fin basisCount, (1 : ℝ) :=
        Finset.sum_le_sum fun slotIndex _ =>
          gram_exchange_diag_le_one hdata basisLabel hrepresentation (hall slotIndex)
    _ = (basisCount : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **THE FAILURE-SUM FLOOR.**  The slot count times the value plus the
total weighted energy is nonnegative. -/
theorem gram_energy_sum_window_lower
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hall : ∀ slotIndex : Fin basisCount, basisLabel slotIndex ∈ activeSet) :
    0 ≤ (basisCount : ℝ) * value
      + ∑ slotIndex : Fin basisCount, ∑ atomIndex : Fin size,
          weight atomIndex * tightDir (basisLabel slotIndex) atomIndex ^ 2 := by
  rw [← gram_exchange_trace_read hdata basisLabel hrepresentation hall]
  exact gram_exchange_trace_nonneg basisLabel hdata.isSymmetric hdata.isIdempotent
    hrepresentation

/-- **THE FAILURE-SUM CEILING.**  The slot count times the value plus
the total weighted energy is at most the slot count. -/
theorem gram_energy_sum_window_upper
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hall : ∀ slotIndex : Fin basisCount, basisLabel slotIndex ∈ activeSet) :
    (basisCount : ℝ) * value
        + ∑ slotIndex : Fin basisCount, ∑ atomIndex : Fin size,
            weight atomIndex * tightDir (basisLabel slotIndex) atomIndex ^ 2
      ≤ (basisCount : ℝ) := by
  rw [← gram_exchange_trace_read hdata basisLabel hrepresentation hall]
  exact gram_exchange_trace_le_card hdata basisLabel hrepresentation hall

end Gtz
