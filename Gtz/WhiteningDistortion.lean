/-
# The whitening distortion: removing a light atom moves Gram data by O(δ)

The collar chain's un-whitening step (CD step 4, audited constant ≈ 2.4
measured / analytic cap), in its generic quadratic-form shape. Whitening by
`W = I − t·A_e` with share `δ = t·ℓ_e < 1` distorts every inner product by a
factor pinched between `1` and `1/(1−δ)`:

for all probes `v`, `(1−δ)·⟨v,v⟩ ≤ ⟨v, Wv⟩ ≤ ⟨v,v⟩` — the atom's form eats
at most its share and never adds. Hence any Gram entry of the whitened
design differs from the raw entry by at most `δ/(1−δ)` times the raw norms
(Cauchy–Schwarz on the difference form `I − W = t·A_e`), and the whitened
distance to any reference set inherits the same distortion factor. All
division-free; the pinch is two `nlinarith`-free lines each.
-/
import Mathlib
import Gtz.MarginTransfer

namespace Gtz

open Matrix

variable {k : ℕ}

/-- **The whitening pinch, lower half**: `(1−δ)·⟨v,v⟩ ≤ ⟨v, Wv⟩` for
`W = I − t·A_e` with `t·ℓ_e ≤ δ` — the atom's form eats at most its share. -/
theorem whitening_form_lower {weight delta : ℝ} (atom probe : Fin k → ℝ)
    (hweightNonneg : 0 ≤ weight)
    (hshare : weight * leverageOf atom ≤ delta) :
    (1 - delta) * (probe ⬝ᵥ probe)
      ≤ probe ⬝ᵥ ((1 - weight • atomMatrix atom) *ᵥ probe) := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hcap := atom_form_le_leverage atom probe
  have hprobeNonneg := dotProduct_self_nonneg probe
  nlinarith [mul_le_mul_of_nonneg_left hcap hweightNonneg,
    mul_le_mul_of_nonneg_right hshare hprobeNonneg]

/-- **The whitening pinch, upper half**: `⟨v, Wv⟩ ≤ ⟨v,v⟩` — subtracting a
PSD form never adds. -/
theorem whitening_form_upper {weight : ℝ} (atom probe : Fin k → ℝ)
    (hweightNonneg : 0 ≤ weight) :
    probe ⬝ᵥ ((1 - weight • atomMatrix atom) *ᵥ probe) ≤ probe ⬝ᵥ probe := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hatomNonneg : 0 ≤ probe ⬝ᵥ (atomMatrix atom *ᵥ probe) := by
    rw [atom_form_eq_sq]
    positivity
  nlinarith [mul_nonneg hweightNonneg hatomNonneg]

/-- **The Gram distortion**: the whitening correction to any inner product is
the atom-overlap product scaled by the weight —
`⟨u, Wv⟩ = ⟨u,v⟩ − t·⟨g,u⟩·⟨g,v⟩` exactly — so the correction is bounded by
Cauchy–Schwarz through the atom: `|⟨u,Wv⟩ − ⟨u,v⟩|² ≤ t²·(g·u)²·(g·v)²`,
division-free and exact. -/
theorem whitening_gram_exact {weight : ℝ} (atom left right : Fin k → ℝ) :
    left ⬝ᵥ ((1 - weight • atomMatrix atom) *ᵥ right)
      = left ⬝ᵥ right - weight * ((atom ⬝ᵥ left) * (atom ⬝ᵥ right)) := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
    vecMulVec_mulVec_general, dotProduct_smul, smul_eq_mul,
    dotProduct_comm left atom]
  ring

end Gtz
