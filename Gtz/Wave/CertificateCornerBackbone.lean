import Gtz.Wave.DenseEigenpairTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The certificate corner backbone — the shared laws of the two dense kills

The K4 certificate (`KFourCertificate`) and the seam certificate
(`CycleSeamCertificate`) state the two dense rank-four kills as
polynomial statements.  This module supplies the exact laws that any
proof of the two certificates consumes.  Every lemma sits at the level
of the certificate variables: real numbers and literal matrices, with
no crux and no frame.

## The corner calculus

Each read pair at a shared atom makes the atom row a left eigen row of
a two-by-two corner.  The product law prices the two off-corner
entries.  The pair trace law and the pair det law price an independent
doubled pair.  The idempotent trace laws price the sum of the six
corner determinants: the sum is one.  The excess identities combine
the two layers.  For K4 the balance reads: the corner excess sum
equals one, while the six shifted weights sum to `6 * value + 1`.
Thus the whole K4 kill reduces to one inequality on the corner excess.

## The uncarried corners

The seam pattern leaves four matrix entries without reads.
Idempotency solves each uncarried entry against the complementary
trace `M 0 0 + M 3 3 - 1`, in exact form and without division.

## The Gamma factorization

The Gamma literal of each certificate is the Gram matrix of an
explicit pattern matrix with six rows and four columns.  The
factorization turns the exchange symmetry and idempotency into the two
positive semidefinite laws: `Γ * M` and `Γ - Γ * M` are both positive
semidefinite.  These are the real-specific laws of the two kills: over
the complex field the same factorization gives no positivity.

## Key results

* `Gtz.corner_product_of_reads` — **THE CORNER PRODUCT LAW.**
* `Gtz.pair_trace_of_reads`, `Gtz.pair_det_of_reads` — the independent
  doubled pair prices its corner trace and determinant.
* `Gtz.esum_pairs_of_idempotent_trace` — **THE CORNER DET SUM.**  The
  six principal two-by-two minors of a trace-two idempotent sum to one.
* `Gtz.kfour_corner_excess_sum` — **THE K4 BALANCE.**
* `Gtz.seam_corner_excess_sum` — **THE SEAM BALANCE.**
* `Gtz.gramMul_posSemidef_of_factor`,
  `Gtz.gramComplement_posSemidef_of_factor` — **THE PSD LAYER.**
* `Gtz.kfour_gram_factorization`, `Gtz.seam_gram_factorization` — the
  two Gamma literals are Gram matrices.

## Vacuity

Every lemma is an unconditional statement about real numbers and real
matrices.  No crux hypothesis appears.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the scalar corner calculus -/

/-- **THE CORNER PRODUCT LAW.**  A read pair at a shared atom prices
the product of the two off-corner entries.  The law is division-free:
the two nonzero coordinates cancel from the product. -/
theorem corner_product_of_reads {a b tii tjj mij mji d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : a * tii + b * mji = d * a) (h2 : a * mij + b * tjj = d * b) :
    mij * mji = (d - tii) * (d - tjj) := by
  have k1 : b * mji = (d - tii) * a := by linear_combination h1
  have k2 : a * mij = (d - tjj) * b := by linear_combination h2
  have h3 : a * b * (mij * mji) = a * b * ((d - tii) * (d - tjj)) := by
    linear_combination (a * mij) * k1 + (d - tii) * a * k2
  exact mul_left_cancel₀ (mul_ne_zero ha hb) h3

/-- **THE PAIR TRACE LAW.**  Two reads at two atoms of one shared pair
with a nonzero cross determinant price the corner trace: the two left
eigen rows exhaust the corner spectrum. -/
theorem pair_trace_of_reads {a0 b0 a1 b1 t00 t11 m01 m10 d0 d1 : ℝ}
    (h00 : a0 * t00 + b0 * m10 = d0 * a0)
    (h01 : a0 * m01 + b0 * t11 = d0 * b0)
    (h10 : a1 * t00 + b1 * m10 = d1 * a1)
    (h11 : a1 * m01 + b1 * t11 = d1 * b1)
    (hdet : a0 * b1 - a1 * b0 ≠ 0) :
    t00 + t11 = d0 + d1 := by
  have hv : (!![t00, m10; m01, t11] : Matrix (Fin 2) (Fin 2) ℝ)
      *ᵥ ![a0, b0] = d0 • ![a0, b0] := by
    funext rowIndex
    fin_cases rowIndex
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination h00
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination h01
  have hw : (!![t00, m10; m01, t11] : Matrix (Fin 2) (Fin 2) ℝ)
      *ᵥ ![a1, b1] = d1 • ![a1, b1] := by
    funext rowIndex
    fin_cases rowIndex
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination h10
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination h11
  have hdetPair : (![a0, b0] : Fin 2 → ℝ) 0 * (![a1, b1] : Fin 2 → ℝ) 1
      - (![a0, b0] : Fin 2 → ℝ) 1 * (![a1, b1] : Fin 2 → ℝ) 0 ≠ 0 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    intro hzero
    exact hdet (by linear_combination hzero)
  have htrace := trace_eq_add_of_eigen_pair hv hw hdetPair
  rw [Matrix.trace_fin_two] at htrace
  simpa using htrace

/-- **THE PAIR DET LAW.**  Two reads at two atoms of one shared pair
with a nonzero cross determinant price the corner determinant as the
product of the two shifted weights.  The proof is division-free: the
corner conjugates the eigenvalue diagonal through the coordinate
matrix, and the determinant of the coordinate matrix cancels. -/
theorem pair_det_of_reads {a0 b0 a1 b1 t00 t11 m01 m10 d0 d1 : ℝ}
    (h00 : a0 * t00 + b0 * m10 = d0 * a0)
    (h01 : a0 * m01 + b0 * t11 = d0 * b0)
    (h10 : a1 * t00 + b1 * m10 = d1 * a1)
    (h11 : a1 * m01 + b1 * t11 = d1 * b1)
    (hdet : a0 * b1 - a1 * b0 ≠ 0) :
    t00 * t11 - m01 * m10 = d0 * d1 := by
  have hprod : (!![t00, m10; m01, t11] : Matrix (Fin 2) (Fin 2) ℝ)
      * !![a0, a1; b0, b1] = !![a0, a1; b0, b1] * !![d0, 0; 0, d1] := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination h00
    · linear_combination h10
    · linear_combination h01
    · linear_combination h11
  have hdet2 := congrArg Matrix.det hprod
  rw [Matrix.det_mul, Matrix.det_mul] at hdet2
  have hVdet : (!![a0, a1; b0, b1] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simpa using hdet
  have hcancel : (!![t00, m10; m01, t11] : Matrix (Fin 2) (Fin 2) ℝ).det
      = (!![d0, 0; 0, d1] : Matrix (Fin 2) (Fin 2) ℝ).det := by
    have hswap : (!![a0, a1; b0, b1] : Matrix (Fin 2) (Fin 2) ℝ).det
        * (!![t00, m10; m01, t11] : Matrix (Fin 2) (Fin 2) ℝ).det
        = (!![a0, a1; b0, b1] : Matrix (Fin 2) (Fin 2) ℝ).det
          * (!![d0, 0; 0, d1] : Matrix (Fin 2) (Fin 2) ℝ).det := by
      linear_combination hdet2
    exact mul_left_cancel₀ hVdet hswap
  rw [Matrix.det_fin_two_of, Matrix.det_fin_two_of] at hcancel
  linear_combination hcancel

/-! ## Layer 2 — the idempotent trace laws on four slots -/

/-- **THE CORNER DET SUM.**  The six principal two-by-two minors of a
trace-two idempotent sum to one.  The proof consumes only the four
diagonal entries of idempotency and the trace. -/
theorem esum_pairs_of_idempotent_trace {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hidem : M * M = M)
    (htr : M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2) :
    (M 0 0 * M 1 1 - M 0 1 * M 1 0) + (M 0 0 * M 2 2 - M 0 2 * M 2 0)
      + (M 0 0 * M 3 3 - M 0 3 * M 3 0) + (M 1 1 * M 2 2 - M 1 2 * M 2 1)
      + (M 1 1 * M 3 3 - M 1 3 * M 3 1) + (M 2 2 * M 3 3 - M 2 3 * M 3 2)
      = 1 := by
  have h00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 0 2 * M 2 0
      + M 0 3 * M 3 0 = M 0 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 0) 0
  have h11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 + M 1 2 * M 2 1
      + M 1 3 * M 3 1 = M 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 1) 1
  have h22 : M 2 0 * M 0 2 + M 2 1 * M 1 2 + M 2 2 * M 2 2
      + M 2 3 * M 3 2 = M 2 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 2) 2
  have h33 : M 3 0 * M 0 3 + M 3 1 * M 1 3 + M 3 2 * M 2 3
      + M 3 3 * M 3 3 = M 3 3 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 3) 3
  linear_combination ((M 0 0 + M 1 1 + M 2 2 + M 3 3 + 1) / 2) * htr
    - (1 / 2) * h00 - (1 / 2) * h11 - (1 / 2) * h22 - (1 / 2) * h33

/-- **THE UNCARRIED SOLVE AT (0, 3).**  Idempotency prices the entry
`M 0 3` against the complementary trace, without division. -/
theorem offdiag_solve_zero_three {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hidem : M * M = M) :
    M 0 3 * (M 0 0 + M 3 3 - 1) = -(M 0 1 * M 1 3 + M 0 2 * M 2 3) := by
  have h03 : M 0 0 * M 0 3 + M 0 1 * M 1 3 + M 0 2 * M 2 3
      + M 0 3 * M 3 3 = M 0 3 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 0) 3
  linear_combination h03

/-- **THE UNCARRIED SOLVE AT (3, 0).** -/
theorem offdiag_solve_three_zero {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hidem : M * M = M) :
    M 3 0 * (M 0 0 + M 3 3 - 1) = -(M 3 1 * M 1 0 + M 3 2 * M 2 0) := by
  have h30 : M 3 0 * M 0 0 + M 3 1 * M 1 0 + M 3 2 * M 2 0
      + M 3 3 * M 3 0 = M 3 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 3) 0
  linear_combination h30

/-- **THE UNCARRIED SOLVE AT (1, 2).** -/
theorem offdiag_solve_one_two {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hidem : M * M = M) :
    M 1 2 * (M 1 1 + M 2 2 - 1) = -(M 1 0 * M 0 2 + M 1 3 * M 3 2) := by
  have h12 : M 1 0 * M 0 2 + M 1 1 * M 1 2 + M 1 2 * M 2 2
      + M 1 3 * M 3 2 = M 1 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 1) 2
  linear_combination h12

/-- **THE UNCARRIED SOLVE AT (2, 1).** -/
theorem offdiag_solve_two_one {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hidem : M * M = M) :
    M 2 1 * (M 1 1 + M 2 2 - 1) = -(M 2 0 * M 0 1 + M 2 3 * M 3 1) := by
  have h21 : M 2 0 * M 0 1 + M 2 1 * M 1 1 + M 2 2 * M 2 1
      + M 2 3 * M 3 1 = M 2 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four]
      using congrFun (congrFun hidem 2) 1
  linear_combination h21

/-! ## Layer 3 — the excess balances of the two certificates -/

/-- **THE K4 BALANCE.**  At the K4 certificate hypotheses, the corner
excess sum equals one.  Each term prices one edge: the shifted weight
times the corner trace minus the shifted weight.  The balance and the
weight sum `6 * value + 1` reduce the whole K4 kill to one inequality
on the excess. -/
theorem kfour_corner_excess_sum
    {value w01 w02 w03 w12 w13 w23 : ℝ}
    {a01 b01 a02 b02 a03 b03 a12 b12 a13 b13 a23 b23 : ℝ}
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hidem : M * M = M)
    (htr : M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2)
    (h01a : a01 * M 0 0 + b01 * M 1 0 = (value + w01) * a01)
    (h01b : a01 * M 0 1 + b01 * M 1 1 = (value + w01) * b01)
    (h02a : a02 * M 0 0 + b02 * M 2 0 = (value + w02) * a02)
    (h02b : a02 * M 0 2 + b02 * M 2 2 = (value + w02) * b02)
    (h03a : a03 * M 0 0 + b03 * M 3 0 = (value + w03) * a03)
    (h03b : a03 * M 0 3 + b03 * M 3 3 = (value + w03) * b03)
    (h12a : a12 * M 1 1 + b12 * M 2 1 = (value + w12) * a12)
    (h12b : a12 * M 1 2 + b12 * M 2 2 = (value + w12) * b12)
    (h13a : a13 * M 1 1 + b13 * M 3 1 = (value + w13) * a13)
    (h13b : a13 * M 1 3 + b13 * M 3 3 = (value + w13) * b13)
    (h23a : a23 * M 2 2 + b23 * M 3 2 = (value + w23) * a23)
    (h23b : a23 * M 2 3 + b23 * M 3 3 = (value + w23) * b23)
    (ha01 : a01 ≠ 0) (hb01 : b01 ≠ 0) (ha02 : a02 ≠ 0) (hb02 : b02 ≠ 0)
    (ha03 : a03 ≠ 0) (hb03 : b03 ≠ 0) (ha12 : a12 ≠ 0) (hb12 : b12 ≠ 0)
    (ha13 : a13 ≠ 0) (hb13 : b13 ≠ 0) (ha23 : a23 ≠ 0) (hb23 : b23 ≠ 0) :
    (value + w01) * (M 0 0 + M 1 1 - (value + w01))
      + (value + w02) * (M 0 0 + M 2 2 - (value + w02))
      + (value + w03) * (M 0 0 + M 3 3 - (value + w03))
      + (value + w12) * (M 1 1 + M 2 2 - (value + w12))
      + (value + w13) * (M 1 1 + M 3 3 - (value + w13))
      + (value + w23) * (M 2 2 + M 3 3 - (value + w23)) = 1 := by
  have p01 := corner_product_of_reads ha01 hb01 h01a h01b
  have p02 := corner_product_of_reads ha02 hb02 h02a h02b
  have p03 := corner_product_of_reads ha03 hb03 h03a h03b
  have p12 := corner_product_of_reads ha12 hb12 h12a h12b
  have p13 := corner_product_of_reads ha13 hb13 h13a h13b
  have p23 := corner_product_of_reads ha23 hb23 h23a h23b
  have hesum := esum_pairs_of_idempotent_trace hidem htr
  linear_combination hesum + p01 + p02 + p03 + p12 + p13 + p23

/-- **THE SEAM BALANCE.**  At the seam certificate hypotheses, the
corner excess sum equals one.  The independent pair contributes the
product of its two shifted weights, the three read corners contribute
their excesses, and the two uncarried corners stay symbolic. -/
theorem seam_corner_excess_sum
    {value w0 w1 wc w4 w5 : ℝ}
    {qK0 qK1 qK4 qL0 qL1 qL5 qM2 qM4 qN2 qN5 : ℝ}
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hidem : M * M = M)
    (htr : M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2)
    (h0a : qK0 * M 0 0 + qL0 * M 1 0 = (value + w0) * qK0)
    (h0b : qK0 * M 0 1 + qL0 * M 1 1 = (value + w0) * qL0)
    (h1a : qK1 * M 0 0 + qL1 * M 1 0 = (value + w1) * qK1)
    (h1b : qK1 * M 0 1 + qL1 * M 1 1 = (value + w1) * qL1)
    (h2a : qM2 * M 2 2 + qN2 * M 3 2 = (value + wc) * qM2)
    (h2b : qM2 * M 2 3 + qN2 * M 3 3 = (value + wc) * qN2)
    (h4a : qK4 * M 0 0 + qM4 * M 2 0 = (value + w4) * qK4)
    (h4b : qK4 * M 0 2 + qM4 * M 2 2 = (value + w4) * qM4)
    (h5a : qL5 * M 1 1 + qN5 * M 3 1 = (value + w5) * qL5)
    (h5b : qL5 * M 1 3 + qN5 * M 3 3 = (value + w5) * qN5)
    (hdetKL : qK0 * qL1 - qK1 * qL0 ≠ 0)
    (hqM2 : qM2 ≠ 0) (hqN2 : qN2 ≠ 0)
    (hqK4 : qK4 ≠ 0) (hqM4 : qM4 ≠ 0) (hqL5 : qL5 ≠ 0) (hqN5 : qN5 ≠ 0) :
    (value + w0) * (value + w1)
      + (value + wc) * (M 2 2 + M 3 3 - (value + wc))
      + (value + w4) * (M 0 0 + M 2 2 - (value + w4))
      + (value + w5) * (M 1 1 + M 3 3 - (value + w5))
      + (M 0 0 * M 3 3 - M 0 3 * M 3 0)
      + (M 1 1 * M 2 2 - M 1 2 * M 2 1) = 1 := by
  have pKL := pair_det_of_reads h0a h0b h1a h1b hdetKL
  have pMN := corner_product_of_reads hqM2 hqN2 h2a h2b
  have p4 := corner_product_of_reads hqK4 hqM4 h4a h4b
  have p5 := corner_product_of_reads hqL5 hqN5 h5a h5b
  have hesum := esum_pairs_of_idempotent_trace hidem htr
  linear_combination hesum - pKL + pMN + p4 + p5

/-! ## Layer 4 — the Gamma factorization and the PSD laws -/

/-- The exchange symmetry and idempotency turn the conjugated Gram
into the plain product: `Mᵀ * Γ * M = Γ * M`. -/
theorem gramMul_conj_of_symm_idem {n : ℕ}
    {Γ M : Matrix (Fin n) (Fin n) ℝ}
    (hΓ : Γᵀ = Γ) (hsym : (Γ * M)ᵀ = Γ * M) (hidem : M * M = M) :
    Mᵀ * Γ * M = Γ * M := by
  have hswap : Mᵀ * Γ = Γ * M := by
    calc Mᵀ * Γ = (Γᵀ * M)ᵀ := by
          rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      _ = (Γ * M)ᵀ := by rw [hΓ]
      _ = Γ * M := hsym
  calc Mᵀ * Γ * M = (Γ * M) * M := by rw [hswap]
    _ = Γ * (M * M) := by rw [Matrix.mul_assoc]
    _ = Γ * M := by rw [hidem]

/-- **THE EXCHANGE PSD LAW.**  If the Gamma matrix factors as a Gram
matrix, the exchange symmetry and idempotency make `Γ * M` positive
semidefinite.  This law is real-specific: the factorization gives the
form `(B * M)ᵀ * (B * M)`. -/
theorem gramMul_posSemidef_of_factor {m n : ℕ}
    {B : Matrix (Fin m) (Fin n) ℝ} {Γ M : Matrix (Fin n) (Fin n) ℝ}
    (hfac : Γ = Bᵀ * B)
    (hsym : (Γ * M)ᵀ = Γ * M) (hidem : M * M = M) :
    (Γ * M).PosSemidef := by
  have hΓ : Γᵀ = Γ := by
    rw [hfac, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hconj := gramMul_conj_of_symm_idem hΓ hsym hidem
  have hpsd := Matrix.posSemidef_conjTranspose_mul_self (B * M)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hpsd
  have hexpand : (B * M)ᵀ * (B * M) = Γ * M := by
    calc (B * M)ᵀ * (B * M) = Mᵀ * Bᵀ * (B * M) := by
          rw [Matrix.transpose_mul]
      _ = Mᵀ * (Bᵀ * B) * M := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Mᵀ * Γ * M := by rw [← hfac]
      _ = Γ * M := hconj
  rwa [hexpand] at hpsd

/-- **THE COMPLEMENT PSD LAW.**  Under the same hypotheses the
complement `Γ - Γ * M` is positive semidefinite: it factors through
the complementary idempotent. -/
theorem gramComplement_posSemidef_of_factor {m n : ℕ}
    {B : Matrix (Fin m) (Fin n) ℝ} {Γ M : Matrix (Fin n) (Fin n) ℝ}
    (hfac : Γ = Bᵀ * B)
    (hsym : (Γ * M)ᵀ = Γ * M) (hidem : M * M = M) :
    (Γ - Γ * M).PosSemidef := by
  have hΓ : Γᵀ = Γ := by
    rw [hfac, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hconj := gramMul_conj_of_symm_idem hΓ hsym hidem
  have hswap : Mᵀ * Γ = Γ * M := by
    calc Mᵀ * Γ = (Γᵀ * M)ᵀ := by
          rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      _ = (Γ * M)ᵀ := by rw [hΓ]
      _ = Γ * M := hsym
  have hpsd := Matrix.posSemidef_conjTranspose_mul_self (B - B * M)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hpsd
  have hexpand : (B - B * M)ᵀ * (B - B * M) = Γ - Γ * M := by
    have hone : (B - B * M)ᵀ * (B - B * M)
        = Bᵀ * B - Bᵀ * B * M - Mᵀ * (Bᵀ * B) + Mᵀ * (Bᵀ * B) * M := by
      rw [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_sub, Matrix.transpose_mul]
      have hassoc1 : Mᵀ * Bᵀ * B = Mᵀ * (Bᵀ * B) := by
        rw [Matrix.mul_assoc]
      have hassoc2 : Mᵀ * Bᵀ * (B * M) = Mᵀ * (Bᵀ * B) * M := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      have hassoc3 : Bᵀ * (B * M) = Bᵀ * B * M :=
        (Matrix.mul_assoc Bᵀ B M).symm
      rw [hassoc1, hassoc2, hassoc3]
      abel
    rw [hone, ← hfac, hconj, hswap]
    abel
  rwa [hexpand] at hpsd

/-- **THE K4 GRAM FACTORIZATION.**  The K4 Gamma literal is the Gram
matrix of the six-row edge pattern.  The four unit norms supply the
unit diagonal. -/
theorem kfour_gram_factorization
    {a01 b01 a02 b02 a03 b03 a12 b12 a13 b13 a23 b23 : ℝ}
    (h0 : a01 ^ 2 + a02 ^ 2 + a03 ^ 2 = 1)
    (h1 : b01 ^ 2 + a12 ^ 2 + a13 ^ 2 = 1)
    (h2 : b02 ^ 2 + b12 ^ 2 + a23 ^ 2 = 1)
    (h3 : b03 ^ 2 + b13 ^ 2 + b23 ^ 2 = 1) :
    (!![1, a01 * b01, a02 * b02, a03 * b03;
        a01 * b01, 1, a12 * b12, a13 * b13;
        a02 * b02, a12 * b12, 1, a23 * b23;
        a03 * b03, a13 * b13, a23 * b23, 1] : Matrix (Fin 4) (Fin 4) ℝ)
      = (!![a01, b01, 0, 0;
            a02, 0, b02, 0;
            a03, 0, 0, b03;
            0, a12, b12, 0;
            0, a13, 0, b13;
            0, 0, a23, b23] : Matrix (Fin 6) (Fin 4) ℝ)ᵀ
        * !![a01, b01, 0, 0;
             a02, 0, b02, 0;
             a03, 0, 0, b03;
             0, a12, b12, 0;
             0, a13, 0, b13;
             0, 0, a23, b23] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six] <;>
    first | ring1 | linear_combination -h0 | linear_combination -h1 | linear_combination -h2 | linear_combination -h3

/-- **THE SEAM GRAM FACTORIZATION.**  The seam Gamma literal is the
Gram matrix of the six-row cycle pattern, with the two zero entries at
the empty shares. -/
theorem seam_gram_factorization
    {qK0 qK1 qK4 qL0 qL1 qL5 qM2 qM3 qM4 qN2 qN3 qN5 : ℝ}
    (hK : qK0 ^ 2 + qK1 ^ 2 + qK4 ^ 2 = 1)
    (hL : qL0 ^ 2 + qL1 ^ 2 + qL5 ^ 2 = 1)
    (hM : qM2 ^ 2 + qM3 ^ 2 + qM4 ^ 2 = 1)
    (hN : qN2 ^ 2 + qN3 ^ 2 + qN5 ^ 2 = 1) :
    (!![1, qK0 * qL0 + qK1 * qL1, qK4 * qM4, 0;
        qK0 * qL0 + qK1 * qL1, 1, 0, qL5 * qN5;
        qK4 * qM4, 0, 1, qM2 * qN2 + qM3 * qN3;
        0, qL5 * qN5, qM2 * qN2 + qM3 * qN3, 1]
        : Matrix (Fin 4) (Fin 4) ℝ)
      = (!![qK0, qL0, 0, 0;
            qK1, qL1, 0, 0;
            0, 0, qM2, qN2;
            0, 0, qM3, qN3;
            qK4, 0, qM4, 0;
            0, qL5, 0, qN5] : Matrix (Fin 6) (Fin 4) ℝ)ᵀ
        * !![qK0, qL0, 0, 0;
             qK1, qL1, 0, 0;
             0, 0, qM2, qN2;
             0, 0, qM3, qN3;
             qK4, 0, qM4, 0;
             0, qL5, 0, qN5] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six] <;>
    first | ring1 | linear_combination -hK | linear_combination -hL | linear_combination -hM | linear_combination -hN

end Gtz
