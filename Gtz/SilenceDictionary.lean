/-
# The silence dictionary

The single translation the whole planar layer rests on: for two heavy planar
atoms, the pair fails to dominate exactly when the coherence beats the
co-leverage product,

  `(ℓ_g − 1)(ℓ_h − 1) < ⟨g,h⟩²`,   equivalently   `ν_g·ν_h < cos²θ`,

and tightness is the equality case. The proof is the 2×2 excess read through
its trace and determinant: the trace is `ℓ_g + ℓ_h − 2 > 0` for heavy atoms,
so positive semidefiniteness is exactly the determinant sign, and the
determinant is the Gram identity `(ℓ_g−1)(ℓ_h−1) − ⟨g,h⟩²`. Every informal
"silence dictionary" step — the conic form, the tight-graph edges, the
per-pair level law's zero locus — now decodes through one kernel-checked
equivalence.
-/
import Mathlib
import Gtz.Basic
import Gtz.TwoByTwo

namespace Gtz

open Matrix

/-! ### The pair excess in Gram data -/

/-- The planar pair excess determinant is the co-leverage/coherence gap. -/
theorem det_pair_excess_planar (g h : Fin 2 → ℝ) :
    (atomMatrix g + atomMatrix h - 1).det
      = (g ⬝ᵥ g - 1) * (h ⬝ᵥ h - 1) - (g ⬝ᵥ h) ^ 2 := by
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.sub_apply,
    atomMatrix, Matrix.vecMulVec_apply, Matrix.one_apply, dotProduct,
    Fin.sum_univ_two]
  norm_num
  ring

/-- The planar pair excess is symmetric. -/
theorem pair_excess_transpose (g h : Fin 2 → ℝ) :
    (atomMatrix g + atomMatrix h - 1)ᵀ = atomMatrix g + atomMatrix h - 1 := by
  rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
    transpose_eq_of_isHermitian (posSemidef_atomMatrix g).1,
    transpose_eq_of_isHermitian (posSemidef_atomMatrix h).1]

/-- The diagonal of the pair excess sums to the leverage excess. -/
theorem pair_excess_trace (g h : Fin 2 → ℝ) :
    (atomMatrix g + atomMatrix h - 1) 0 0 + (atomMatrix g + atomMatrix h - 1) 1 1
      = g ⬝ᵥ g + h ⬝ᵥ h - 2 := by
  simp only [Matrix.add_apply, Matrix.sub_apply, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_two]
  norm_num
  ring

/-! ### The dictionary -/

/-- **The silence dictionary**: for heavy planar atoms the pair dominates
exactly when the co-leverage product carries the coherence,
`⟨g,h⟩² ≤ (ℓ_g − 1)(ℓ_h − 1)`. Silence is the strict reverse; tightness is
equality. -/
theorem pair_dominates_iff_coherence_le (g h : Fin 2 → ℝ)
    (hgHeavy : 1 < g ⬝ᵥ g) (hhHeavy : 1 < h ⬝ᵥ h) :
    (atomMatrix g + atomMatrix h - 1).PosSemidef
      ↔ (g ⬝ᵥ h) ^ 2 ≤ (g ⬝ᵥ g - 1) * (h ⬝ᵥ h - 1) := by
  have htrace : 0 < (atomMatrix g + atomMatrix h - 1) 0 0
      + (atomMatrix g + atomMatrix h - 1) 1 1 := by
    rw [pair_excess_trace]
    linarith
  rw [posSemidef_two_iff_of_trace_pos (pair_excess_transpose g h) htrace]
  -- align the entrywise determinant with the Gram identity
  have hdetEntry : (atomMatrix g + atomMatrix h - 1) 0 0
        * (atomMatrix g + atomMatrix h - 1) 1 1
      - (atomMatrix g + atomMatrix h - 1) 0 1 ^ 2
      = (g ⬝ᵥ g - 1) * (h ⬝ᵥ h - 1) - (g ⬝ᵥ h) ^ 2 := by
    have hdet := det_pair_excess_planar g h
    rw [Matrix.det_fin_two] at hdet
    have hoffdiag : (atomMatrix g + atomMatrix h - 1) 0 1
        = (atomMatrix g + atomMatrix h - 1) 1 0 := by
      have := congrFun (congrFun (pair_excess_transpose g h) 0) 1
      simpa [Matrix.transpose_apply] using this.symm
    rw [← hdet, hoffdiag]
    ring
  rw [hdetEntry]
  constructor <;> intro hside <;> linarith

/-- **Silence, spelled out**: a heavy planar pair fails to dominate exactly
when the coherence strictly beats the co-leverage product. -/
theorem pair_silent_iff_coherence_gt (g h : Fin 2 → ℝ)
    (hgHeavy : 1 < g ⬝ᵥ g) (hhHeavy : 1 < h ⬝ᵥ h) :
    ¬ (atomMatrix g + atomMatrix h - 1).PosSemidef
      ↔ (g ⬝ᵥ g - 1) * (h ⬝ᵥ h - 1) < (g ⬝ᵥ h) ^ 2 := by
  rw [pair_dominates_iff_coherence_le g h hgHeavy hhHeavy, not_le]

/-- **The normalized dictionary**: dividing by the leverage product turns the
threshold into the conic form `ν_g·ν_h` vs `cos²θ` — the exact statement the
tight-graph and chord layers consume. -/
theorem pair_dominates_iff_conic (g h : Fin 2 → ℝ)
    (hgHeavy : 1 < g ⬝ᵥ g) (hhHeavy : 1 < h ⬝ᵥ h) :
    (atomMatrix g + atomMatrix h - 1).PosSemidef
      ↔ (g ⬝ᵥ h) ^ 2 / ((g ⬝ᵥ g) * (h ⬝ᵥ h))
        ≤ (1 - 1 / (g ⬝ᵥ g)) * (1 - 1 / (h ⬝ᵥ h)) := by
  rw [pair_dominates_iff_coherence_le g h hgHeavy hhHeavy]
  have hgPos : (0 : ℝ) < g ⬝ᵥ g := by linarith
  have hhPos : (0 : ℝ) < h ⬝ᵥ h := by linarith
  have hproduct : 0 < (g ⬝ᵥ g) * (h ⬝ᵥ h) := mul_pos hgPos hhPos
  rw [div_le_iff₀ hproduct]
  constructor <;> intro hside
  · calc (g ⬝ᵥ h) ^ 2 ≤ (g ⬝ᵥ g - 1) * (h ⬝ᵥ h - 1) := hside
      _ = (1 - 1 / (g ⬝ᵥ g)) * (1 - 1 / (h ⬝ᵥ h))
          * ((g ⬝ᵥ g) * (h ⬝ᵥ h)) := by
        field_simp
  · calc (g ⬝ᵥ h) ^ 2
        ≤ (1 - 1 / (g ⬝ᵥ g)) * (1 - 1 / (h ⬝ᵥ h))
          * ((g ⬝ᵥ g) * (h ⬝ᵥ h)) := hside
      _ = (g ⬝ᵥ g - 1) * (h ⬝ᵥ h - 1) := by
        field_simp

end Gtz
