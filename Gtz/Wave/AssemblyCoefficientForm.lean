import Gtz.Wave.AssemblyBasisColumns

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The coefficient H-form — `Ξ = B H Bᵀ` with `P B = B M`, `M² = M`, `Hᵀ = H`

The four-active coefficient projection identified `B Bᵀ` with the whole
assembly, which breaks the moment the active family outgrows the basis.  The
repair is the H-form: with `B` the labelled basis columns and `L` a left
inverse, the coefficient matrices

    `M = L * (P * B)`   and   `H = L * Ξ * Lᵀ`

satisfy `P B = B M`, `M² = M`, `B H Bᵀ = Ξ` and `Hᵀ = H` — at EVERY active
count.  Everything follows from one identity, the absorption
`B * (L * X) = X` on matrices whose column space sits inside `range Ξ`:
the chart preserves `range Ξ` by commutation, so `P * B` absorbs, and `Ξ`
and `Ξ * Lᵀ` absorb outright.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.range_mul_le_of_commutes_of_range_eq` — chart invariance of the
  column space: `P * B` has columns inside the column space of `B`.
* `Gtz.exists_coefficientForm_of_basis` — **THE H-FORM.**  The left inverse,
  the coefficient projection and the coordinate Gram, with their four laws.

## NOT PROVED here, and named

The positive-definiteness of `H` (kernel triviality from the rank chain),
the exchange law `M H = H Mᵀ`, and the trace law `tr M = rank(P Ξ)` are the
second half of the campaign's step twelve and follow in a separate module.

## Vacuity

Nothing here quantifies over a crux.  The statements hold at every stationary
datum with a chosen basis.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- **CHART INVARIANCE OF THE COLUMN SPACE.**  When the chart commutes with the
assembly and the column space of `B` is the assembly's range, the columns of
`P * B` stay inside the column space of `B`. -/
theorem range_mul_le_of_commutes_of_range_eq
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hrangeB : LinearMap.range (Matrix.toLin' (tightBasisColumns tightDir basisLabel))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir))) :
    LinearMap.range (Matrix.toLin' (projection * tightBasisColumns tightDir basisLabel))
      ≤ LinearMap.range (Matrix.toLin' (tightBasisColumns tightDir basisLabel)) := by
  rintro vec ⟨coeffVec, rfl⟩
  rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  have hcolumn : tightBasisColumns tightDir basisLabel *ᵥ coeffVec
      ∈ LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)) := by
    rw [← hrangeB]
    exact ⟨coeffVec, Matrix.toLin'_apply _ _⟩
  obtain ⟨preimage, hpreimage⟩ := hcolumn
  rw [Matrix.toLin'_apply] at hpreimage
  rw [← hpreimage, Matrix.mulVec_mulVec, hdata.assembly_commutes, ← Matrix.mulVec_mulVec]
  rw [hrangeB]
  exact ⟨projection *ᵥ preimage, Matrix.toLin'_apply _ _⟩

/-- **THE H-FORM.**  A labelled basis of the assembly range yields a left
inverse `L`, a coefficient projection `M` and a coordinate Gram `H` with

    `L B = 1`,  `P B = B M`,  `M² = M`,  `B H Bᵀ = Ξ`,  `Hᵀ = H`.

The identification `B Bᵀ = Ξ` of the four-active file is the special case in
which the basis carries the whole positive support with unit coordinate
Gram. -/
theorem exists_coefficientForm_of_basis
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisIndep : LinearIndependent ℝ
      (fun columnIndex => tightDir (basisLabel columnIndex)))
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir))) :
    ∃ (L : Matrix (Fin basisCount) (Fin size) ℝ)
      (M H : Matrix (Fin basisCount) (Fin basisCount) ℝ),
      L * tightBasisColumns tightDir basisLabel = 1
        ∧ projection * tightBasisColumns tightDir basisLabel
            = tightBasisColumns tightDir basisLabel * M
        ∧ M * M = M
        ∧ tightBasisColumns tightDir basisLabel * H
              * (tightBasisColumns tightDir basisLabel)ᵀ
            = chartMultiplierAssembly activeSet activeWeight tightDir
        ∧ Hᵀ = H := by
  classical
  set B := tightBasisColumns tightDir basisLabel with hBdef
  set assembly := chartMultiplierAssembly activeSet activeWeight tightDir with hassemblyDef
  have hsymmAssembly : assemblyᵀ = assembly :=
    transpose_chartMultiplierAssembly_of_isChartStationaryData hdata
  have hrangeB : LinearMap.range (Matrix.toLin' B) = LinearMap.range (Matrix.toLin' assembly) :=
    range_tightBasisColumns_eq basisLabel hbasisSpan
  obtain ⟨L, hleft⟩ :=
    exists_leftInverse_tightBasisColumns basisLabel hbasisIndep hbasisSpan
  -- absorption instances
  have habsorbPB : B * (L * (projection * B)) = projection * B :=
    mul_leftInverse_mul_eq_of_range_le B L (projection * B) hleft
      (range_mul_le_of_commutes_of_range_eq hdata basisLabel hrangeB)
  have habsorbAssembly : B * (L * assembly) = assembly := by
    refine mul_leftInverse_mul_eq_of_range_le B L assembly hleft ?_
    rw [hrangeB]
  have habsorbAssemblyL : B * (L * (assembly * Lᵀ)) = assembly * Lᵀ := by
    refine mul_leftInverse_mul_eq_of_range_le B L (assembly * Lᵀ) hleft ?_
    rw [hrangeB, Matrix.toLin'_mul]
    exact LinearMap.range_comp_le_range _ _
  -- the transposed absorption: the assembly absorbs `Lᵀ Bᵀ` on the right
  have habsorbRight : assembly * Lᵀ * Bᵀ = assembly := by
    have htransposed := congrArg Matrix.transpose habsorbAssembly
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hsymmAssembly] at htransposed
    exact htransposed
  refine ⟨L, L * (projection * B), L * assembly * Lᵀ, hleft, habsorbPB.symm, ?_, ?_, ?_⟩
  · -- idempotence, through the landed left-inverse transport
    exact coefficient_idempotent_of_leftInverse projection B L (L * (projection * B))
      hleft hdata.isIdempotent habsorbPB.symm
  · -- B H Bᵀ = Ξ
    calc B * (L * assembly * Lᵀ) * Bᵀ
        = B * (L * (assembly * Lᵀ)) * Bᵀ := by rw [Matrix.mul_assoc L assembly Lᵀ]
      _ = assembly * Lᵀ * Bᵀ := by rw [habsorbAssemblyL]
      _ = assembly := habsorbRight
  · -- symmetry of H
    calc (L * assembly * Lᵀ)ᵀ
        = Lᵀᵀ * (L * assembly)ᵀ := Matrix.transpose_mul _ _
      _ = L * assembly * Lᵀ := by
          rw [Matrix.transpose_transpose, Matrix.transpose_mul, hsymmAssembly,
            Matrix.mul_assoc]

end Gtz
