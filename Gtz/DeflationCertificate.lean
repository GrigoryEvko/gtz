/-
# The deflation certificate: congruence PSD transfers to the range

The σ₉-continuum engines certify PSD of the DEFLATED matrix
`Ms = Tᵀ(dFᵀdF − s²·I)T` — the congruence of the shifted Gram by a
null-space basis `T` (whose columns span `ker C` cell-wide, certified by
interval elimination). The two generic consumption facts:

* **congruence transfer**: `TᵀMT ⪰ 0` gives `⟨u, Mu⟩ ≥ 0` for every
  `u = Tw` in the range of `T` — pure adjoint bookkeeping;
* **the singular floor**: at `M = jacᵀ·jac − rate²·I` the transfer reads
  `|jac·u|² ≥ rate²·|u|²` on `range T` — "every singular value of the
  restricted Jacobian is at least `rate`", the exact shape
  `σ₉(F_tan) ≥ 1/5` instantiates on the window.
-/
import Mathlib
import Gtz.PsdKit
import Gtz.ResolventPerturbation

namespace Gtz

open Matrix

variable {k n m : ℕ}

/-- **Congruence transfer**: `TᵀMT ⪰ 0` certifies the quadratic form of
`M` at every vector in the range of `T`. -/
theorem congruence_psd_transfer (formMatrix : Matrix (Fin k) (Fin k) ℝ)
    (nullBasis : Matrix (Fin k) (Fin n) ℝ)
    (hPSD : (nullBasisᵀ * formMatrix * nullBasis).PosSemidef)
    (coeff : Fin n → ℝ) :
    0 ≤ (nullBasis *ᵥ coeff) ⬝ᵥ (formMatrix *ᵥ (nullBasis *ᵥ coeff)) := by
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hPSD).2 coeff
  rw [star_trivial] at hform
  have hassoc : (nullBasisᵀ * formMatrix * nullBasis) *ᵥ coeff
      = nullBasisᵀ *ᵥ (formMatrix *ᵥ (nullBasis *ᵥ coeff)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hadjoint : coeff ⬝ᵥ (nullBasisᵀ *ᵥ (formMatrix *ᵥ (nullBasis *ᵥ coeff)))
      = (nullBasis *ᵥ coeff) ⬝ᵥ (formMatrix *ᵥ (nullBasis *ᵥ coeff)) := by
    rw [dotProduct_comm, dotProduct_mulVec_transpose, dotProduct_comm]
  rw [hassoc, hadjoint] at hform
  exact hform

/-- **The deflated singular floor**: PSD of the deflated shifted Gram
`Tᵀ(jacᵀjac − rate²·I)T` floors the Jacobian on the deflated subspace —
`|jac·u|² ≥ rate²·|u|²` for every `u = Tw`. -/
theorem deflated_singular_floor (jacobian : Matrix (Fin m) (Fin k) ℝ)
    (nullBasis : Matrix (Fin k) (Fin n) ℝ) (rate : ℝ)
    (hPSD : (nullBasisᵀ
        * (jacobianᵀ * jacobian - rate ^ 2 • (1 : Matrix (Fin k) (Fin k) ℝ))
        * nullBasis).PosSemidef)
    (coeff : Fin n → ℝ) :
    rate ^ 2 * ((nullBasis *ᵥ coeff) ⬝ᵥ (nullBasis *ᵥ coeff))
      ≤ (jacobian *ᵥ (nullBasis *ᵥ coeff))
          ⬝ᵥ (jacobian *ᵥ (nullBasis *ᵥ coeff)) := by
  have htransfer := congruence_psd_transfer
    (jacobianᵀ * jacobian - rate ^ 2 • (1 : Matrix (Fin k) (Fin k) ℝ))
    nullBasis hPSD coeff
  have hgram : (nullBasis *ᵥ coeff)
      ⬝ᵥ ((jacobianᵀ * jacobian - rate ^ 2 • (1 : Matrix (Fin k) (Fin k) ℝ))
        *ᵥ (nullBasis *ᵥ coeff))
      = (jacobian *ᵥ (nullBasis *ᵥ coeff))
          ⬝ᵥ (jacobian *ᵥ (nullBasis *ᵥ coeff))
        - rate ^ 2 * ((nullBasis *ᵥ coeff) ⬝ᵥ (nullBasis *ᵥ coeff)) := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
    congr 1
    · rw [← Matrix.mulVec_mulVec, dotProduct_comm, dotProduct_mulVec_transpose]
    · rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
        smul_eq_mul]
  rw [hgram] at htransfer
  linarith

/-- **The kernel-triviality reading** (the rank statement): with a strictly
positive rate, the certificate makes the Jacobian INJECTIVE on the deflated
subspace — `jac·(Tw) = 0` forces `Tw = 0`. This is the certificate's
"`ker(dF) ∩ range(T) = 0`, hence rank `K = 22`" consequence. -/
theorem deflated_floor_kills_kernel (jacobian : Matrix (Fin m) (Fin k) ℝ)
    (nullBasis : Matrix (Fin k) (Fin n) ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hPSD : (nullBasisᵀ
        * (jacobianᵀ * jacobian - rate ^ 2 • (1 : Matrix (Fin k) (Fin k) ℝ))
        * nullBasis).PosSemidef)
    (coeff : Fin n → ℝ)
    (hkernel : jacobian *ᵥ (nullBasis *ᵥ coeff) = 0) :
    nullBasis *ᵥ coeff = 0 := by
  have hfloor := deflated_singular_floor jacobian nullBasis rate hPSD coeff
  rw [hkernel, dotProduct_zero] at hfloor
  have hselfNonneg : 0 ≤ (nullBasis *ᵥ coeff) ⬝ᵥ (nullBasis *ᵥ coeff) :=
    dotProduct_self_nonneg _
  have hratePos : 0 < rate ^ 2 := pow_pos hrate 2
  have hselfNonpos : (nullBasis *ᵥ coeff) ⬝ᵥ (nullBasis *ᵥ coeff) ≤ 0 := by
    nlinarith [hfloor, hratePos]
  exact eq_zero_of_dotProduct_self_eq_zero
    (le_antisymm hselfNonpos hselfNonneg)

end Gtz
