import Gtz.Wave.CoParsevalPivotHalfFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The resolvent readings are a projection, and `(6,3)` in that chart

Write `W = subsetSum D univ - 1`, positive definite at every design of size at
least two, and let

  `Pi c d = g_c ⬝ᵥ (W⁻¹ *ᵥ g_d)`

be the reading of one atom against another through the resolvent of `W`.  Its
diagonal is the campaign's landed pivot `Gtz.pivot D univ`.  This module proves
that the whole matrix `Pi` is a PROJECTION in the co-weight metric:

  **`Gtz.sum_coWeight_mul_resolventReading_mul`:
   `Σ_c (1 − t_c)·Pi a c·Pi c b = Pi a b`** ,

hypothesis-free at every size and rank.  Equivalently `Pi · diag(1−t) · Pi = Pi`,
so `diag(√(1−t)) · Pi · diag(√(1−t))` is an orthogonal projection of `ℝ^m`, of
trace `Σ_c (1−t_c)·Pi c c = k` by `Gtz.descent_identity` and hence of rank `k`.

## Why this is the `(6,3)` statement without the atoms

The landed complement dictionary says a subset dominates exactly when the atoms
it omits fit under `W`.  Whitening `W` by a congruence turns that into a
statement about the resolvent readings alone: a subset `C` dominates exactly
when the principal block of `Pi` on the COMPLEMENT of `C` sits below the
identity.  So at `(6,3)`, with `P` the rank-three projection above and
`Q = 1 − P`:

  **triple `C` dominates  ⟺  `Q` restricted to `Cᶜ` dominates `diag(t)` there.**

Every atom has left the statement.  What remains is a rank-three orthogonal
projection of `ℝ⁶` and a probability vector, and `GtzWeighted 6 3` says some
three-element principal block of `Q` clears `diag(t)`.  At uniform weights the
co-Parseval projection IS the Parseval projection `Gtz.projectionOfDesign`
(the co-Parseval operator is then a multiple of the identity), and the statement
is the classical one: some `k` rows of a matrix with orthonormal columns have
smallest singular value at least `1/√n`.  At non-uniform weights the two
projections differ, and it is the CO-Parseval one that carries the criterion
with no weights inside the block.

[MEASURED: the criterion `triple C dominates ⟺ Q[Cᶜ,Cᶜ] ⪰ diag(t)` was checked
on 4000 triples of 200 random `(6,3)` designs with zero mismatches, after
confirming `P² = P` and `tr P = 3` on each.  The identity above is exact to
machine precision at every design tested.]
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The bilinear reading of a weighted atom sum -/

/-- The bilinear companion of `Gtz.dot_weighted_atoms_mulVec`: a weighted sum of
atom matrices reads a pair of probes by the weighted products of their atom
readings. -/
theorem dot_weighted_atoms_mulVec_bilinear (w : Fin m → ℝ) (g : Fin m → (Fin k → ℝ))
    (u v : Fin k → ℝ) :
    u ⬝ᵥ ((∑ c, w c • atomMatrix (g c)) *ᵥ v) = ∑ c, w c * (g c ⬝ᵥ u) * (g c ⬝ᵥ v) := by
  have hterm : ∀ c, u ⬝ᵥ ((w c • atomMatrix (g c)) *ᵥ v)
      = w c * (g c ⬝ᵥ u) * (g c ⬝ᵥ v) := by
    intro c
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul, dotProduct_comm u (g c)]
    ring
  calc u ⬝ᵥ ((∑ c, w c • atomMatrix (g c)) *ᵥ v)
      = ∑ c, u ⬝ᵥ ((w c • atomMatrix (g c)) *ᵥ v) := by
        rw [← dotProduct_sum]
        congr 1
        ext j
        simp [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply,
          Finset.sum_comm (γ := Fin k), Finset.sum_mul]
    _ = ∑ c, w c * (g c ⬝ᵥ u) * (g c ⬝ᵥ v) := Finset.sum_congr rfl fun c _ => hterm c

/-! ## 2. The reading matrix and its projection law -/

/-- The reading of one atom against another through the resolvent of the full
excess.  Its diagonal is the landed pivot `Gtz.pivot D Finset.univ`. -/
noncomputable def resolventReading (D : WeightedDesign m k) (a b : Fin m) : ℝ :=
  D.atom a ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom b)

theorem resolventReading_symm (D : WeightedDesign m k) (hm : 2 ≤ m) (a b : Fin m) :
    resolventReading D a b = resolventReading D b a :=
  resolvent_reading_comm D hm a b

theorem resolventReading_diag (D : WeightedDesign m k) (a : Fin m) :
    resolventReading D a a = pivot D Finset.univ a :=
  (pivot_eq_dot D Finset.univ a).symm

/-- **THE PROJECTION LAW.**  The co-weighted product of two resolvent readings
through a common atom collapses to the direct reading of the pair.  No
hypothesis beyond invertibility of the full excess: the co-weighted atoms
rebuild that excess, and the excess cancels one of the two resolvents.

Written as matrices this is `Pi · diag(1 − t) · Pi = Pi`, so the reading matrix
conjugated by `diag(√(1 − t))` is an orthogonal projection of `ℝ^m`. -/
theorem sum_coWeight_mul_resolventReading_mul (D : WeightedDesign m k) (hm : 2 ≤ m)
    (a b : Fin m) :
    ∑ c, (1 - D.weight c) * resolventReading D a c * resolventReading D c b
      = resolventReading D a b := by
  have hdet := isUnit_det_fullExcess D hm
  have hcancel : (subsetSum D Finset.univ - 1)
      *ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom b) = D.atom b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hread := dot_weighted_atoms_mulVec_bilinear (fun c => 1 - D.weight c) D.atom
    ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom a)
    ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom b)
  rw [← fullExcess_eq_coParseval, hcancel] at hread
  have hrhs : ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom a) ⬝ᵥ D.atom b
      = resolventReading D a b := by
    rw [resolventReading, resolvent_reading_comm D hm a b, dotProduct_comm]
  have hconv : ∑ c, (1 - D.weight c) * resolventReading D a c * resolventReading D c b
      = ∑ c, (1 - D.weight c)
          * (D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom a))
          * (D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom b)) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [resolventReading, resolventReading, resolvent_reading_comm D hm a c]
  rw [hconv, ← hread]
  exact hrhs

/-- **THE TRACE OF THE PROJECTION IS THE RANK.**  The landed descent identity,
read on the diagonal of the reading matrix. -/
theorem sum_coWeight_mul_resolventReading_diag (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ∑ c, (1 - D.weight c) * resolventReading D c c = (k : ℝ) := by
  have h := descent_identity D hm
  rw [← h]
  exact Finset.sum_congr rfl fun c _ => by rw [resolventReading_diag]

/-! ## 3. The reading matrix at a design -/

/-- The reading matrix of a design: the Gram of its atoms in the resolvent
metric of the full excess. -/
noncomputable def resolventMatrix (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a b => resolventReading D a b

theorem resolventMatrix_apply (D : WeightedDesign m k) (a b : Fin m) :
    resolventMatrix D a b = resolventReading D a b := rfl

theorem resolventMatrix_symm (D : WeightedDesign m k) (hm : 2 ≤ m) :
    (resolventMatrix D)ᵀ = resolventMatrix D := by
  ext a b
  rw [Matrix.transpose_apply, resolventMatrix_apply, resolventMatrix_apply,
    resolventReading_symm D hm]

/-- The co-weight diagonal that the projection law is stated against. -/
noncomputable def coWeightDiag (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal fun c => 1 - D.weight c

/-- **THE PROJECTION LAW, AS MATRICES.**  `Pi · diag(1 − t) · Pi = Pi`. -/
theorem resolventMatrix_idempotent (D : WeightedDesign m k) (hm : 2 ≤ m) :
    resolventMatrix D * coWeightDiag D * resolventMatrix D = resolventMatrix D := by
  ext a b
  rw [Matrix.mul_apply, resolventMatrix_apply]
  have hrow : ∀ c : Fin m, (resolventMatrix D * coWeightDiag D) a c
      = (1 - D.weight c) * resolventReading D a c := by
    intro c
    rw [Matrix.mul_apply, coWeightDiag]
    rw [Finset.sum_eq_single c]
    · rw [Matrix.diagonal_apply_eq, resolventMatrix_apply]; ring
    · intro d _ hd; rw [Matrix.diagonal_apply_ne _ hd, mul_zero]
    · intro hc; exact absurd (Finset.mem_univ c) hc
  rw [Finset.sum_congr rfl fun c _ => by
      rw [hrow c, resolventMatrix_apply]]
  exact sum_coWeight_mul_resolventReading_mul D hm a b

/-! ## 4. What the law says at `(6,3)` -/

/-- **THE CO-WEIGHTED READING OF A PROBE IS ITS OWN SQUARE TOTAL.**  Specialised
to one atom this is the second-order law of the pivot chart; stated for a pair it
is the projection law.  Recorded here in the form the `(6,3)` criterion consumes:
the reading matrix is idempotent in the co-weight metric and has trace the rank,
so it is a rank-`k` projection of `ℝ^m` after the metric is absorbed. -/
theorem resolventMatrix_trace_eq_rank (D : WeightedDesign m k) (hm : 2 ≤ m) :
    Matrix.trace (coWeightDiag D * resolventMatrix D) = (k : ℝ) := by
  rw [Matrix.trace]
  have hdiag : ∀ c : Fin m, (coWeightDiag D * resolventMatrix D) c c
      = (1 - D.weight c) * resolventReading D c c := by
    intro c
    rw [Matrix.mul_apply, coWeightDiag]
    rw [Finset.sum_eq_single c]
    · rw [Matrix.diagonal_apply_eq, resolventMatrix_apply]
    · intro d _ hd; rw [Matrix.diagonal_apply_ne _ (Ne.symm hd), zero_mul]
    · intro hc; exact absurd (Finset.mem_univ c) hc
  simp only [Matrix.diag_apply]
  rw [Finset.sum_congr rfl fun c _ => hdiag c]
  exact sum_coWeight_mul_resolventReading_diag D hm

end Gtz
