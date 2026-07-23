/-
# Theorem RC's engine: the idempotent splitting of the design differential

The constraint-rank theorem's whole mechanism, k-general and spectra-free.
At a design, the Gram-side transfer matrix `E = G·D_t` is idempotent (multiply
the design equation `G·D_t·G = G` by `D_t`), and the G-block of the design
differential is the Sylvester map `T(X) = X·Eᵀ + E·X − X`. The splitting:

* unconditionally, `T(X) = E·X·Eᵀ − (I−E)·X·(I−Eᵀ)` — the signed projector
  sandwich — and `X` decomposes into the four projector blocks;
* under idempotency, `T` is `+id` on the range block `E·X·Eᵀ`, `−id` on the
  corange block `(I−E)·X·(I−Eᵀ)`, and `0` on both mixed blocks — so `T³ = T`
  (spectrum `{+1, −1, 0}` without a single eigenvalue computation), `T²` is
  the block-diagonal projector, and `ker T` is exactly the mixed subspace;
* on the design side, `E·G = G` (the atom images are fixed — the artifact's
  `E·s_a = s_a`, so the `t`-columns add nothing to the `Φ`-rows), and
  `tr E = Σ t_c·ℓ_c = k` (the projector rank equals the ambient rank, read
  off the trace with no spectral theorem).

This is everything the artifact's Theorem RC proof uses except the final
block-dimension count `12 + 1 = 13` at `(m,k) = (6,3)`, which is a linear
dimension chase over the explicit blocks.
-/
import Mathlib
import Gtz.Basic
import Gtz.CornerResolvent

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ### The Sylvester map and its unconditional shape -/

/-- The G-block of the design differential at transfer matrix `E`:
`T(X) = X·Eᵀ + E·X − X`. -/
def sylvesterMap (transfer probe : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  probe * transferᵀ + transfer * probe - probe

/-- **The signed projector sandwich**: `T(X) = E·X·Eᵀ − (I−E)·X·(I−Eᵀ)`,
for every `E` — idempotency not needed. -/
theorem sylvesterMap_eq_signed_blocks
    (transfer probe : Matrix (Fin m) (Fin m) ℝ) :
    sylvesterMap transfer probe
      = transfer * probe * transferᵀ
        - (1 - transfer) * probe * (1 - transferᵀ) := by
  rw [sylvesterMap]; noncomm_ring

/-- Every matrix splits into the four projector blocks. -/
theorem blocks_decompose (transfer probe : Matrix (Fin m) (Fin m) ℝ) :
    probe = transfer * probe * transferᵀ
      + transfer * probe * (1 - transferᵀ)
      + (1 - transfer) * probe * transferᵀ
      + (1 - transfer) * probe * (1 - transferᵀ) := by
  noncomm_ring

/-- The Sylvester map is additive. -/
theorem sylvesterMap_add (transfer left right : Matrix (Fin m) (Fin m) ℝ) :
    sylvesterMap transfer (left + right)
      = sylvesterMap transfer left + sylvesterMap transfer right := by
  simp only [sylvesterMap]; noncomm_ring

/-- The Sylvester map respects differences. -/
theorem sylvesterMap_sub (transfer left right : Matrix (Fin m) (Fin m) ℝ) :
    sylvesterMap transfer (left - right)
      = sylvesterMap transfer left - sylvesterMap transfer right := by
  simp only [sylvesterMap]; noncomm_ring

/-! ### The splitting under idempotency -/

section Idempotent

variable {transfer : Matrix (Fin m) (Fin m) ℝ}
  (hidem : transfer * transfer = transfer)

include hidem

/-- The transpose of an idempotent is idempotent. -/
theorem transpose_idempotent : transferᵀ * transferᵀ = transferᵀ := by
  rw [← Matrix.transpose_mul, hidem]

/-- The complement annihilates on the left: `E·(I−E) = 0`. -/
theorem idem_mul_compl : transfer * (1 - transfer) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, hidem, sub_self]

/-- The complement annihilates on the right: `(I−E)·E = 0`. -/
theorem compl_mul_idem : (1 - transfer) * transfer = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, hidem, sub_self]

/-- The transposed complement annihilates: `(I−Eᵀ)·Eᵀ = 0`. -/
theorem complT_mul_idemT : (1 - transferᵀ) * transferᵀ = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, transpose_idempotent hidem, sub_self]

/-- **`T` fixes the range block**: `T(E·X·Eᵀ) = E·X·Eᵀ`. -/
theorem sylvesterMap_range_block (probe : Matrix (Fin m) (Fin m) ℝ) :
    sylvesterMap transfer (transfer * probe * transferᵀ)
      = transfer * probe * transferᵀ := by
  calc sylvesterMap transfer (transfer * probe * transferᵀ)
      = transfer * probe * (transferᵀ * transferᵀ)
        + (transfer * transfer) * probe * transferᵀ
        - transfer * probe * transferᵀ := by
        rw [sylvesterMap]; noncomm_ring
    _ = transfer * probe * transferᵀ := by
        rw [transpose_idempotent hidem, hidem]; abel

/-- **`T` negates the corange block**: `T((I−E)·X·(I−Eᵀ)) = −(I−E)·X·(I−Eᵀ)`. -/
theorem sylvesterMap_corange_block (probe : Matrix (Fin m) (Fin m) ℝ) :
    sylvesterMap transfer ((1 - transfer) * probe * (1 - transferᵀ))
      = -((1 - transfer) * probe * (1 - transferᵀ)) := by
  calc sylvesterMap transfer ((1 - transfer) * probe * (1 - transferᵀ))
      = (1 - transfer) * probe * ((1 - transferᵀ) * transferᵀ)
        + (transfer * (1 - transfer)) * probe * (1 - transferᵀ)
        - (1 - transfer) * probe * (1 - transferᵀ) := by
        rw [sylvesterMap]; noncomm_ring
    _ = -((1 - transfer) * probe * (1 - transferᵀ)) := by
        rw [complT_mul_idemT hidem, idem_mul_compl hidem, Matrix.mul_zero,
          Matrix.zero_mul, Matrix.zero_mul]
        abel

/-- **`T` kills the upper mixed block**: `T(E·X·(I−Eᵀ)) = 0`. -/
theorem sylvesterMap_upper_mixed (probe : Matrix (Fin m) (Fin m) ℝ) :
    sylvesterMap transfer (transfer * probe * (1 - transferᵀ)) = 0 := by
  calc sylvesterMap transfer (transfer * probe * (1 - transferᵀ))
      = transfer * probe * ((1 - transferᵀ) * transferᵀ)
        + (transfer * transfer) * probe * (1 - transferᵀ)
        - transfer * probe * (1 - transferᵀ) := by
        rw [sylvesterMap]; noncomm_ring
    _ = 0 := by
        rw [complT_mul_idemT hidem, hidem, Matrix.mul_zero]
        abel

/-- **`T` kills the lower mixed block**: `T((I−E)·X·Eᵀ) = 0`. -/
theorem sylvesterMap_lower_mixed (probe : Matrix (Fin m) (Fin m) ℝ) :
    sylvesterMap transfer ((1 - transfer) * probe * transferᵀ) = 0 := by
  calc sylvesterMap transfer ((1 - transfer) * probe * transferᵀ)
      = (1 - transfer) * probe * (transferᵀ * transferᵀ)
        + (transfer * (1 - transfer)) * probe * transferᵀ
        - (1 - transfer) * probe * transferᵀ := by
        rw [sylvesterMap]; noncomm_ring
    _ = 0 := by
        rw [transpose_idempotent hidem, idem_mul_compl hidem,
          Matrix.zero_mul, Matrix.zero_mul]
        abel

/-- **`T²` is the block-diagonal projector**:
`T(T(X)) = E·X·Eᵀ + (I−E)·X·(I−Eᵀ)`. -/
theorem sylvesterMap_sq (probe : Matrix (Fin m) (Fin m) ℝ) :
    sylvesterMap transfer (sylvesterMap transfer probe)
      = transfer * probe * transferᵀ
        + (1 - transfer) * probe * (1 - transferᵀ) := by
  rw [sylvesterMap_eq_signed_blocks transfer probe, sylvesterMap_sub,
    sylvesterMap_range_block hidem, sylvesterMap_corange_block hidem,
    sub_neg_eq_add]

/-- **The tripotent law `T³ = T`**: the spectrum is `{+1, −1, 0}` with no
eigenvalue computation. -/
theorem sylvesterMap_tripotent (probe : Matrix (Fin m) (Fin m) ℝ) :
    sylvesterMap transfer
        (sylvesterMap transfer (sylvesterMap transfer probe))
      = sylvesterMap transfer probe := by
  rw [sylvesterMap_sq hidem probe, sylvesterMap_add,
    sylvesterMap_range_block hidem, sylvesterMap_corange_block hidem,
    ← sub_eq_add_neg, ← sylvesterMap_eq_signed_blocks]

/-- **The kernel is exactly the mixed subspace**: `T(X) = 0` iff both the
range and corange blocks of `X` vanish. -/
theorem sylvesterMap_eq_zero_iff (probe : Matrix (Fin m) (Fin m) ℝ) :
    sylvesterMap transfer probe = 0
      ↔ transfer * probe * transferᵀ = 0
        ∧ (1 - transfer) * probe * (1 - transferᵀ) = 0 := by
  constructor
  · intro hzero
    have hrange : transfer * probe * transferᵀ = 0 := by
      have hsandwich : transfer * sylvesterMap transfer probe * transferᵀ
          = transfer * probe * transferᵀ := by
        calc transfer * sylvesterMap transfer probe * transferᵀ
            = (transfer * transfer) * probe * (transferᵀ * transferᵀ)
              - (transfer * (1 - transfer)) * probe
                * ((1 - transferᵀ) * transferᵀ) := by
              rw [sylvesterMap]; noncomm_ring
          _ = transfer * probe * transferᵀ := by
              rw [hidem, transpose_idempotent hidem, idem_mul_compl hidem,
                complT_mul_idemT hidem, Matrix.zero_mul, Matrix.zero_mul,
                sub_zero]
      rw [hzero, Matrix.mul_zero, Matrix.zero_mul] at hsandwich
      exact hsandwich.symm
    have hcorange : transfer * probe * transferᵀ
        - (1 - transfer) * probe * (1 - transferᵀ) = 0 := by
      rw [← sylvesterMap_eq_signed_blocks]; exact hzero
    rw [hrange, zero_sub, neg_eq_zero] at hcorange
    exact ⟨hrange, hcorange⟩
  · rintro ⟨hrange, hcorange⟩
    rw [sylvesterMap_eq_signed_blocks, hrange, hcorange, sub_zero]

end Idempotent

/-! ### The design side: `E = G·D_t` is idempotent with `E·G = G`, `tr E = k` -/

/-- The Gram matrix of a weighted design. -/
def designGram (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun c d => D.atom c ⬝ᵥ D.atom d

/-- The Gram-side transfer matrix `E = G·D_t`. -/
noncomputable def designTransfer (D : WeightedDesign m k) :
    Matrix (Fin m) (Fin m) ℝ :=
  designGram D * Matrix.diagonal D.weight

/-- **The Gram-side design equation**: `G·D_t·G = G` — the Parseval identity
read through two atoms. This is simultaneously `E·G = G`: the atom images are
fixed points of the transfer, so the `t`-columns of the design differential
add nothing beyond the `Φ`-rows. -/
theorem designTransfer_mul_gram (D : WeightedDesign m k) :
    designTransfer D * designGram D = designGram D := by
  rw [designTransfer, Matrix.mul_assoc]
  ext c d
  have hframe := congrArg
    (fun M : Matrix (Fin k) (Fin k) ℝ => D.atom c ⬝ᵥ (M *ᵥ D.atom d))
    D.isParseval
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, atomMatrix,
    vecMulVec_mulVec_general, Matrix.one_mulVec, dotProduct_sum,
    dotProduct_smul, smul_eq_mul, smul_smul] at hframe
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, designGram, Matrix.of_apply]
  exact Eq.trans (Finset.sum_congr rfl fun e _ => by ring) hframe

/-- **The transfer is idempotent**: `E² = (G·D_t·G)·D_t = G·D_t = E`. -/
theorem designTransfer_idempotent (D : WeightedDesign m k) :
    designTransfer D * designTransfer D = designTransfer D := by
  calc designTransfer D * designTransfer D
      = (designTransfer D * designGram D) * Matrix.diagonal D.weight := by
        rw [designTransfer, ← Matrix.mul_assoc]
    _ = designTransfer D := by rw [designTransfer_mul_gram]; rfl

/-- **The weighted leverage sum is the rank**: `Σ t_c·ℓ_c = k` — the trace of
the Parseval identity. -/
theorem design_weighted_leverage_sum (D : WeightedDesign m k) :
    ∑ c, D.weight c * leverageOf (D.atom c) = k := by
  have htrace := congrArg Matrix.trace D.isParseval
  rw [Matrix.trace_sum, Matrix.trace_one] at htrace
  simp only [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul] at htrace
  simpa using htrace

/-- **The transfer has trace `k`**: the idempotent's rank is the ambient rank,
read off the trace with no spectral theorem. -/
theorem designTransfer_trace (D : WeightedDesign m k) :
    Matrix.trace (designTransfer D) = k := by
  have hdiag : ∀ c, designTransfer D c c
      = D.weight c * leverageOf (D.atom c) := by
    intro c
    simp only [designTransfer, designGram, Matrix.mul_diagonal,
      Matrix.of_apply, leverageOf, dotProduct]
    rw [mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
  calc Matrix.trace (designTransfer D)
      = ∑ c, D.weight c * leverageOf (D.atom c) := by
        rw [Matrix.trace]
        exact Finset.sum_congr rfl fun c _ => by
          rw [Matrix.diag_apply, hdiag c]
    _ = k := design_weighted_leverage_sum D

end Gtz
