/-
# The Goreinov–Tyrtyshnikov–Zamarashkin (GTZ / "Moscow") problem — core definitions

**Conjecture (GTZ 1997).** For every real n×k matrix A with orthonormal columns
(AᵀA = I, 1 ≤ k < n) there is a k×k row submatrix A_I with σ_min(A_I) ≥ 1/√n.

Known: k ≤ 2 proven (Sengupta–Pautov, arXiv:2604.05944); FALSE over ℂ (sharp complex
constant α = 2 − 2/√3, SIC extremal).

**The weighted-design form** (the campaign's working form; the weight absorbs n):
vectors g_1..g_m ∈ ℝᵏ and weights t_c > 0 with Σ t_c = 1 and Σ t_c g_c g_cᵀ = I_k;
GTZ(k) for all n  ⟺  every weighted design has a k-subset C with Σ_{c∈C} g_c g_cᵀ ⪰ I_k
("C dominates").

This file defines designs, domination, and the problem statements in both forms.
The reduction between them, and the whole proven ledger, live in the sibling modules —
see the README for the module map and status.
-/
import Mathlib

namespace Gtz

open Matrix

variable {m k n : ℕ}

/-- The rank-one atom g gᵀ of a vector g ∈ ℝᵏ, as a k×k real matrix. -/
def atomMatrix (g : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.vecMulVec g g

/-- The leverage |g|² of an atom vector. -/
def leverageOf (g : Fin k → ℝ) : ℝ :=
  ∑ i, g i ^ 2

/-- A weighted design: m vectors in ℝᵏ with positive weights summing to 1 whose
weighted rank-one atoms resolve the identity (a weighted Parseval frame /
isotropic measure). -/
structure WeightedDesign (m k : ℕ) where
  atom : Fin m → (Fin k → ℝ)
  weight : Fin m → ℝ
  weight_pos : ∀ c, 0 < weight c
  weight_sum_one : ∑ c, weight c = 1
  isParseval : ∑ c, weight c • atomMatrix (atom c) = 1

/-- The unweighted atom sum S_C = Σ_{c∈C} g_c g_cᵀ of a subset of atoms.
Note it is weight-free: domination depends only on the vectors. -/
def subsetSum (D : WeightedDesign m k) (C : Finset (Fin m)) : Matrix (Fin k) (Fin k) ℝ :=
  ∑ c ∈ C, atomMatrix (D.atom c)

/-- Subset C dominates: S_C ⪰ I (Loewner). For |C| = k this says the k×k block
Gram of the selected vectors has all eigenvalues ≥ 1. -/
def Dominates (D : WeightedDesign m k) (C : Finset (Fin m)) : Prop :=
  (subsetSum D C - 1).PosSemidef

/-- Weighted GTZ at size (m, k): every weighted (m,k)-design has a dominating
k-subset. This is the campaign's canonical finite statement. -/
def GtzWeighted (m k : ℕ) : Prop :=
  ∀ D : WeightedDesign m k, ∃ C : Finset (Fin m), C.card = k ∧ Dominates D C

/-- Weighted GTZ at rank k, all sizes. Equivalent to original GTZ(k) for all n. -/
def GtzWeightedAll (k : ℕ) : Prop :=
  ∀ m, GtzWeighted m k

/-- The original 1997 statement: every n×k orthonormal-column matrix has a k-row
submatrix B with BᵀB ⪰ (1/n)·I, i.e. σ_min ≥ 1/√n. -/
def GtzOriginal (n k : ℕ) : Prop :=
  ∀ A : Matrix (Fin n) (Fin k) ℝ, Aᵀ * A = 1 →
    ∃ rowPick : Fin k → Fin n, Function.Injective rowPick ∧
      ((A.submatrix rowPick id)ᵀ * (A.submatrix rowPick id) - (n : ℝ)⁻¹ • 1).PosSemidef

/-- The pigeonhole pivot value q_c = g_cᵀ (S_Q − I)⁻¹ g_c = tr((S_Q − I)⁻¹ g_c g_cᵀ),
the certificate's per-atom quantity for a base set Q with S_Q ≻ I.
(Stated via trace to keep the definition inverse-notation-only.) -/
noncomputable def pivot (D : WeightedDesign m k) (Q : Finset (Fin m)) (c : Fin m) : ℝ :=
  Matrix.trace ((subsetSum D Q - 1)⁻¹ * atomMatrix (D.atom c))

/-- The trace of an atom is its leverage. -/
theorem trace_atomMatrix (g : Fin k → ℝ) :
    Matrix.trace (atomMatrix g) = leverageOf g := by
  rw [atomMatrix, Matrix.trace_vecMulVec]
  simp only [dotProduct, leverageOf]
  exact Finset.sum_congr rfl fun i _ => (pow_two (g i)).symm

end Gtz
