/-
# Rank 2, Case B: heavy designs always contain a dominating pair

The de-spectralized Sengupta–Pautov pairing (diary §§0, 61), weighted and
m-free. For a weighted (m,2) design with every leverage > 1:

* double-angle vectors w_c = (x²−y², 2xy) with |w_c|² = ℓ_c², balanced by
  Parseval (Σ t·w = 0, Σ t·ℓ = 2, so z_c := ℓ_c − 2 has Σ t·z = 0);
* a pair {c,d} dominates iff the 2×2 determinant of S_{cd} − I is ≥ 0
  (positive trace kills the diagonal clause), i.e. iff the obstruction
  K_{cd} := ⟨w_c,w_d⟩ − z_c·z_d + 2 is ≤ 0;
* if ALL pairs fail (all K > 0): the row sums Σ_d t_d·K_{cd} = 2 collapse by
  balance, so term-wise AM–GM gives the STRICT core inequality
  Q_K(u) < 2·Σt·u² for every nonconstant u, where
  Q_K(u) = |Σt·u·w|² − (Σt·u·z)² + 2(Σt·u)²;
* the witness u_c := ⟨w_c, r⟩ for a whitened column r of the double-angle
  frame operator Ω = Σ t·w·wᵀ makes Q_K(u) − 2Σtu² the Ψ-form at r,
  Ψ := Ω² − ζζᵀ − 2Ω, and the two columns of the whitening R (RᵀΩR = I)
  satisfy Σ_j r_jᵀΨr_j = trΩ − |Rᵀζ|² − 4 ≥ trΩ − σ − 4 = 0 using
  σ = Σt·z² = trΩ − 4 and the Cauchy–Schwarz-free bound
  σ − |Rᵀζ|² = Σt·(⟨w, RRᵀζ⟩ − z)² ≥ 0 — some column contradicts the core;
* degenerate Ω (all w on a line): balance forces an opposite-sign pair, where
  K = −2(ℓ−1)(ℓ'−1) < 0 — that pair dominates outright.

No spectral theorem, no Perron–Frobenius, no eigenvalues: sums and squares.
-/
import Mathlib
import Gtz.Basic
import Gtz.Sanity
import Gtz.SchurRankOne
import Gtz.PsdKit
import Gtz.TwoByTwo
import Gtz.Naimark

namespace Gtz

open Matrix

variable {m : ℕ}

section CaseB

variable (D : WeightedDesign m 2)

/-- The double-angle vector of an atom. -/
private noncomputable def wvec (c : Fin m) : Fin 2 → ℝ :=
  ![D.atom c 0 ^ 2 - D.atom c 1 ^ 2, 2 * D.atom c 0 * D.atom c 1]

/-- The centered leverage. -/
private noncomputable def zval (c : Fin m) : ℝ :=
  leverageOf (D.atom c) - 2

/-- The scalar pair obstruction: positive exactly when the pair fails. -/
private noncomputable def obstruction (c d : Fin m) : ℝ :=
  wvec D c ⬝ᵥ wvec D d - zval D c * zval D d + 2

private theorem wvec_dot (c d : Fin m) :
    wvec D c ⬝ᵥ wvec D d
      = (D.atom c 0 ^ 2 - D.atom c 1 ^ 2) * (D.atom d 0 ^ 2 - D.atom d 1 ^ 2)
        + (2 * D.atom c 0 * D.atom c 1) * (2 * D.atom d 0 * D.atom d 1) := by
  simp [wvec, dotProduct, Fin.sum_univ_two]

private theorem lev_expand (c : Fin m) :
    leverageOf (D.atom c) = D.atom c 0 ^ 2 + D.atom c 1 ^ 2 := by
  rw [leverageOf, Fin.sum_univ_two]

/-- The three scalar Parseval identities. -/
private theorem parseval_xx : ∑ c, D.weight c * D.atom c 0 ^ 2 = 1 := by
  have h := congrFun (congrFun D.isParseval 0) 0
  simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.one_apply, smul_eq_mul, if_true] at h
  rw [← h]
  exact Finset.sum_congr rfl fun c _ => by ring

private theorem parseval_yy : ∑ c, D.weight c * D.atom c 1 ^ 2 = 1 := by
  have h := congrFun (congrFun D.isParseval 1) 1
  simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.one_apply, smul_eq_mul, if_true] at h
  rw [← h]
  exact Finset.sum_congr rfl fun c _ => by ring

private theorem parseval_xy : ∑ c, D.weight c * (D.atom c 0 * D.atom c 1) = 0 := by
  have h := congrFun (congrFun D.isParseval 0) 1
  simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.one_apply, smul_eq_mul] at h
  rw [if_neg (by decide : ¬((0 : Fin 2) = 1))] at h
  exact h

/-- Balance of the double-angle coordinates. -/
private theorem balance_wx :
    ∑ c, D.weight c * (D.atom c 0 ^ 2 - D.atom c 1 ^ 2) = 0 := by
  simp only [show ∀ c, D.weight c * (D.atom c 0 ^ 2 - D.atom c 1 ^ 2)
      = D.weight c * D.atom c 0 ^ 2 - D.weight c * D.atom c 1 ^ 2 from
    fun c => by ring]
  rw [Finset.sum_sub_distrib, parseval_xx, parseval_yy]
  ring

private theorem balance_wy :
    ∑ c, D.weight c * (2 * D.atom c 0 * D.atom c 1) = 0 := by
  simp only [show ∀ c, D.weight c * (2 * D.atom c 0 * D.atom c 1)
      = 2 * (D.weight c * (D.atom c 0 * D.atom c 1)) from fun c => by ring]
  rw [← Finset.mul_sum, parseval_xy]
  ring

private theorem trace_two : ∑ c, D.weight c * leverageOf (D.atom c) = 2 := by
  have hxx := parseval_xx D
  have hyy := parseval_yy D
  simp only [show ∀ c, D.weight c * leverageOf (D.atom c)
      = D.weight c * D.atom c 0 ^ 2 + D.weight c * D.atom c 1 ^ 2 from
    fun c => by rw [lev_expand]; ring]
  rw [Finset.sum_add_distrib, hxx, hyy]
  norm_num

private theorem balance_z : ∑ c, D.weight c * zval D c = 0 := by
  simp only [show ∀ c, D.weight c * zval D c
      = D.weight c * leverageOf (D.atom c) - 2 * D.weight c from
    fun c => by rw [zval]; ring]
  rw [Finset.sum_sub_distrib, trace_two, ← Finset.mul_sum, D.weight_sum_one]
  ring

/-- Pair failure converts to a positive obstruction (heavy pair). -/
private theorem obstruction_pos_of_not_dominates {c d : Fin m} (hcd : c ≠ d)
    (hc : 1 < leverageOf (D.atom c)) (hd : 1 < leverageOf (D.atom d))
    (hnot : ¬ Dominates D {c, d}) : 0 < obstruction D c d := by
  have hsum : subsetSum D {c, d}
      = atomMatrix (D.atom c) + atomMatrix (D.atom d) := by
    rw [subsetSum, Finset.sum_pair hcd]
  set X : Matrix (Fin 2) (Fin 2) ℝ :=
    atomMatrix (D.atom c) + atomMatrix (D.atom d) - 1 with hX
  have hXT : Xᵀ = X := by
    rw [hX, Matrix.transpose_sub, Matrix.transpose_add,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom c)).1,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom d)).1,
      Matrix.transpose_one]
  have hXentries :
      X 0 0 = D.atom c 0 ^ 2 + D.atom d 0 ^ 2 - 1 ∧
      X 1 1 = D.atom c 1 ^ 2 + D.atom d 1 ^ 2 - 1 ∧
      X 0 1 = D.atom c 0 * D.atom c 1 + D.atom d 0 * D.atom d 1 := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [hX, Matrix.sub_apply, Matrix.add_apply, atomMatrix,
        Matrix.vecMulVec_apply] <;> ring
  obtain ⟨h00, h11, h01⟩ := hXentries
  have htr : 0 < X 0 0 + X 1 1 := by
    rw [h00, h11]
    rw [lev_expand] at hc hd
    linarith
  have hdomiff : Dominates D {c, d} ↔ 0 ≤ X 0 0 * X 1 1 - X 0 1 ^ 2 := by
    rw [Dominates, hsum, ← hX]
    exact posSemidef_two_iff_of_trace_pos hXT htr
  have hdet : X 0 0 * X 1 1 - X 0 1 ^ 2 < 0 := by
    by_contra hge
    exact hnot (hdomiff.mpr (by linarith [not_lt.mp hge]))
  -- the determinant is −K/2: a ring identity in the coordinates
  have hiden : X 0 0 * X 1 1 - X 0 1 ^ 2 = -(obstruction D c d) / 2 := by
    rw [h00, h11, h01, obstruction, wvec_dot, zval, zval, lev_expand, lev_expand]
    ring
  rw [hiden] at hdet
  linarith

/-- The obstruction row sums collapse to 2 by balance. -/
private theorem obstruction_row_sum (c : Fin m) :
    ∑ d, D.weight d * obstruction D c d = 2 := by
  have hwx := balance_wx D
  have hwy := balance_wy D
  have hz := balance_z D
  have hone := D.weight_sum_one
  simp only [show ∀ d, D.weight d * obstruction D c d
      = (D.atom c 0 ^ 2 - D.atom c 1 ^ 2)
          * (D.weight d * (D.atom d 0 ^ 2 - D.atom d 1 ^ 2))
        + (2 * D.atom c 0 * D.atom c 1)
          * (D.weight d * (2 * D.atom d 0 * D.atom d 1))
        - zval D c * (D.weight d * zval D d) + 2 * D.weight d from
    fun d => by rw [obstruction, wvec_dot]; ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    hwx, hwy, hz, hone]
  ring

/-- **The strict core inequality.** If every pair fails and u is nonconstant,
the obstruction quadratic form stays strictly below 2·Σt·u². -/
private theorem core_strict (hK : ∀ c d, c ≠ d → 0 < obstruction D c d)
    (u : Fin m → ℝ) {c0 d0 : Fin m} (hne : u c0 ≠ u d0) :
    ∑ c, D.weight c * (u c * ∑ d, D.weight d * (u d * obstruction D c d))
      < 2 * ∑ c, D.weight c * u c ^ 2 := by
  have hc0d0 : c0 ≠ d0 := fun h => hne (h ▸ rfl)
  -- compare the double sums termwise: AM–GM against the row-sum collapse
  have hterm : ∀ c d, D.weight c * (D.weight d
        * (u c * u d * obstruction D c d))
      ≤ D.weight c * (D.weight d
        * ((u c ^ 2 + u d ^ 2) / 2 * obstruction D c d)) := by
    intro c d
    rcases eq_or_ne c d with rfl | hcd
    · have : u c * u c * obstruction D c c
          = (u c ^ 2 + u c ^ 2) / 2 * obstruction D c c := by ring
      rw [this]
    · have hKcd := hK c d hcd
      have hsq : 0 ≤ (u c - u d) ^ 2 := sq_nonneg _
      have hin : u c * u d * obstruction D c d
          ≤ (u c ^ 2 + u d ^ 2) / 2 * obstruction D c d := by nlinarith
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hin (D.weight_pos d).le)
        (D.weight_pos c).le
  have hstrict : D.weight c0 * (D.weight d0
        * (u c0 * u d0 * obstruction D c0 d0))
      < D.weight c0 * (D.weight d0
        * ((u c0 ^ 2 + u d0 ^ 2) / 2 * obstruction D c0 d0)) := by
    have hKcd := hK c0 d0 hc0d0
    have hsq : 0 < (u c0 - u d0) ^ 2 := by positivity
    have hin : u c0 * u d0 * obstruction D c0 d0
        < (u c0 ^ 2 + u d0 ^ 2) / 2 * obstruction D c0 d0 := by nlinarith
    exact mul_lt_mul_of_pos_left
      (mul_lt_mul_of_pos_left hin (D.weight_pos d0))
      (D.weight_pos c0)
  -- the double sums, nested
  have hlt : ∑ c, ∑ d, D.weight c * (D.weight d
        * (u c * u d * obstruction D c d))
      < ∑ c, ∑ d, D.weight c * (D.weight d
        * ((u c ^ 2 + u d ^ 2) / 2 * obstruction D c d)) := by
    refine Finset.sum_lt_sum (fun c _ => Finset.sum_le_sum
      fun d _ => hterm c d) ⟨c0, Finset.mem_univ c0, ?_⟩
    exact Finset.sum_lt_sum (fun d _ => hterm c0 d)
      ⟨d0, Finset.mem_univ d0, hstrict⟩
  -- identify both sides
  have hlhs : ∑ c, ∑ d, D.weight c * (D.weight d
        * (u c * u d * obstruction D c d))
      = ∑ c, D.weight c * (u c * ∑ d, D.weight d
          * (u d * obstruction D c d)) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  have hrhs : ∑ c, ∑ d, D.weight c * (D.weight d
        * ((u c ^ 2 + u d ^ 2) / 2 * obstruction D c d))
      = 2 * ∑ c, D.weight c * u c ^ 2 := by
    -- split (u_c² + u_d²)/2 and use the row sums twice (once transposed)
    have hsplit : ∀ c d, D.weight c * (D.weight d
          * ((u c ^ 2 + u d ^ 2) / 2 * obstruction D c d))
        = (D.weight c * u c ^ 2) * (D.weight d * obstruction D c d) / 2
          + (D.weight d * u d ^ 2) * (D.weight c * obstruction D c d) / 2 := by
      intro c d
      ring
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl
      fun d _ => hsplit c d]
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
    have hfirst : ∑ c, ∑ d, (D.weight c * u c ^ 2)
          * (D.weight d * obstruction D c d) / 2
        = ∑ c, D.weight c * u c ^ 2 := by
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [show ∀ d, (D.weight c * u c ^ 2) * (D.weight d * obstruction D c d) / 2
          = (D.weight c * u c ^ 2 / 2) * (D.weight d * obstruction D c d) from
        fun d => by ring]
      rw [← Finset.mul_sum, obstruction_row_sum D c]
      ring
    have hsecond : ∑ c, ∑ d, (D.weight d * u d ^ 2)
          * (D.weight c * obstruction D c d) / 2
        = ∑ c, D.weight c * u c ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [show ∀ c, (D.weight d * u d ^ 2) * (D.weight c * obstruction D c d) / 2
          = (D.weight d * u d ^ 2 / 2) * (D.weight c * obstruction D d c) from
        fun c => by
          rw [show obstruction D c d = obstruction D d c from by
            rw [obstruction, obstruction, dotProduct_comm]; ring]
          ring]
      rw [← Finset.mul_sum, obstruction_row_sum D d]
      ring
    rw [hfirst, hsecond]
    ring
  rw [hlhs, hrhs] at hlt
  exact hlt

end CaseB

end Gtz
