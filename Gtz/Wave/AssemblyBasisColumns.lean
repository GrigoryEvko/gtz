import Gtz.Wave.AssemblyBasisSelection

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The basis columns — the matrix carrier of the coefficient coordinates

The labelled basis of `Gtz.Wave.AssemblyBasisSelection` becomes a `size × r`
matrix `B` whose columns are the basis directions.  This file lands the four
matrix facts every coefficient-coordinate argument consumes:

* the column space of `B` IS `range Ξ`,
* `B` has full column rank `r`,
* `B` admits a matrix left inverse `L` (the `Fin 4` statement of
  `Gtz.exists_matrix_leftInverse_of_finrank_range_eq_four`, freed from its
  dimension), and
* **ABSORPTION**: `B * (L * X) = X` for every matrix `X` whose column space
  sits inside the column space of `B`.

Absorption is the engine of the H-form: `range Ξ` is invariant under the
chart by commutation, so `P * B`, `Ξ` and `Ξ * anything` all absorb, and the
coefficient matrices `M = L * P * B` and `H = L * Ξ * Lᵀ` inherit their laws
from one identity.  The H-form itself is the next file.

## Vacuity

Nothing here quantifies over a crux.  The statements hold at every stationary
datum and, for the generic half, at every real matrix.
-/

namespace Gtz

open Matrix

/-! ## The generic layer: left inverse and absorption -/

/-- Full-column-rank matrices admit a matrix left inverse — the
`Gtz.exists_matrix_leftInverse_of_finrank_range_eq_four` statement at every
column count. -/
theorem exists_matrix_leftInverse_of_finrank_range_eq
    {ambient : Type*} [Fintype ambient] {dimension : ℕ}
    (B : Matrix ambient (Fin dimension) ℝ)
    (hrange : Module.finrank ℝ (LinearMap.range (Matrix.toLin' B)) = dimension) :
    ∃ L : Matrix (Fin dimension) ambient ℝ, L * B = 1 := by
  classical
  let columnMap : (Fin dimension → ℝ) →ₗ[ℝ] (ambient → ℝ) := Matrix.toLin' B
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker columnMap
  have hdomain : Module.finrank ℝ (Fin dimension → ℝ) = dimension := by
    simp
  have hkernelRank : Module.finrank ℝ (LinearMap.ker columnMap) = 0 := by
    change Module.finrank ℝ (LinearMap.range (Matrix.toLin' B))
        + Module.finrank ℝ (LinearMap.ker columnMap) =
      Module.finrank ℝ (Fin dimension → ℝ) at hrankNullity
    omega
  have hkernel : LinearMap.ker columnMap = ⊥ := Submodule.finrank_eq_zero.mp hkernelRank
  obtain ⟨leftInverse, hleftInverse⟩ := columnMap.exists_leftInverse_of_injective hkernel
  refine ⟨LinearMap.toMatrix' leftInverse, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  simpa only [columnMap, Matrix.toLin'_one] using hleftInverse

/-- **ABSORPTION.**  A left inverse makes `B * L` the identity on every matrix
whose column space sits inside the column space of `B`. -/
theorem mul_leftInverse_mul_eq_of_range_le
    {ambient columnIndex otherIndex : Type*}
    [Fintype ambient] [Fintype columnIndex] [Fintype otherIndex]
    [DecidableEq ambient] [DecidableEq columnIndex] [DecidableEq otherIndex]
    (B : Matrix ambient columnIndex ℝ) (L : Matrix columnIndex ambient ℝ)
    (X : Matrix ambient otherIndex ℝ) (hleft : L * B = 1)
    (hrange : LinearMap.range (Matrix.toLin' X) ≤ LinearMap.range (Matrix.toLin' B)) :
    B * (L * X) = X := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun coeffVec => ?_
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply]
  obtain ⟨preimage, hpreimage⟩ := hrange ⟨coeffVec, Matrix.toLin'_apply X coeffVec⟩
  rw [Matrix.toLin'_apply] at hpreimage
  rw [← hpreimage, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hleft,
    Matrix.mul_one]

/-! ## The basis columns of a stationary datum -/

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- The `size × r` matrix whose columns are the chosen basis directions. -/
def tightBasisColumns (tightDir : activeIndex → (Fin size → ℝ))
    (basisLabel : Fin basisCount → activeIndex) : Matrix (Fin size) (Fin basisCount) ℝ :=
  fun atomIndex columnIndex => tightDir (basisLabel columnIndex) atomIndex

/-- A product of the basis columns is the coefficient combination of the basis
directions. -/
theorem tightBasisColumns_mulVec (basisLabel : Fin basisCount → activeIndex)
    (coeffVec : Fin basisCount → ℝ) :
    tightBasisColumns tightDir basisLabel *ᵥ coeffVec
      = ∑ columnIndex, coeffVec columnIndex • tightDir (basisLabel columnIndex) := by
  funext atomIndex
  simp only [tightBasisColumns, Matrix.mulVec, dotProduct, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun columnIndex _ => mul_comm _ _

/-- Each basis direction is a column. -/
theorem tightBasisColumns_mulVec_single (basisLabel : Fin basisCount → activeIndex)
    (columnIndex : Fin basisCount) :
    tightBasisColumns tightDir basisLabel *ᵥ Pi.single columnIndex 1
      = tightDir (basisLabel columnIndex) := by
  rw [tightBasisColumns_mulVec]
  rw [Finset.sum_eq_single columnIndex]
  · rw [Pi.single_eq_same, one_smul]
  · intro otherIndex _ hne
    rw [Pi.single_eq_of_ne hne, zero_smul]
  · intro hnotMem
    exact absurd (Finset.mem_univ columnIndex) hnotMem

/-- **THE COLUMN SPACE IS THE ASSEMBLY RANGE.**  When the basis directions are
positively weighted and span `range Ξ`, the column space of `B` equals
`range Ξ`. -/
theorem range_tightBasisColumns_eq
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir))) :
    LinearMap.range (Matrix.toLin' (tightBasisColumns tightDir basisLabel))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)) := by
  rw [← hbasisSpan]
  apply le_antisymm
  · rintro vec ⟨coeffVec, rfl⟩
    rw [Matrix.toLin'_apply, tightBasisColumns_mulVec]
    exact Submodule.sum_mem _ fun columnIndex _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨columnIndex, rfl⟩)
  · rw [Submodule.span_le]
    rintro vec ⟨columnIndex, rfl⟩
    exact ⟨Pi.single columnIndex 1, by
      rw [Matrix.toLin'_apply, tightBasisColumns_mulVec_single]⟩

/-- **FULL COLUMN RANK.**  Independent basis directions give the columns full
rank. -/
theorem finrank_range_tightBasisColumns_eq
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisIndep : LinearIndependent ℝ
      (fun columnIndex => tightDir (basisLabel columnIndex)))
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir))) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (tightBasisColumns tightDir basisLabel)))
      = basisCount := by
  rw [range_tightBasisColumns_eq basisLabel hbasisSpan, ← hbasisSpan,
    finrank_span_eq_card hbasisIndep, Fintype.card_fin]

/-- The basis columns admit a left inverse. -/
theorem exists_leftInverse_tightBasisColumns
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisIndep : LinearIndependent ℝ
      (fun columnIndex => tightDir (basisLabel columnIndex)))
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir))) :
    ∃ L : Matrix (Fin basisCount) (Fin size) ℝ,
      L * tightBasisColumns tightDir basisLabel = 1 :=
  exists_matrix_leftInverse_of_finrank_range_eq _
    (finrank_range_tightBasisColumns_eq basisLabel hbasisIndep hbasisSpan)

end Gtz
