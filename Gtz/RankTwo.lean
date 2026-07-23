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

set_option maxHeartbeats 1600000

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

/-- Raw double-angle coordinates (bridging `wvec`'s components). -/
private noncomputable def wxv (c : Fin m) : ℝ := D.atom c 0 ^ 2 - D.atom c 1 ^ 2

private noncomputable def wyv (c : Fin m) : ℝ := 2 * D.atom c 0 * D.atom c 1

private theorem obstruction_eq (c d : Fin m) :
    obstruction D c d
      = wxv D c * wxv D d + wyv D c * wyv D d - zval D c * zval D d + 2 := by
  rw [obstruction, wvec_dot, wxv, wxv, wyv, wyv]

private theorem wlen_sq (c : Fin m) :
    wxv D c ^ 2 + wyv D c ^ 2 = leverageOf (D.atom c) ^ 2 := by
  rw [wxv, wyv, lev_expand]
  ring

private theorem balance_wxv : ∑ c, D.weight c * wxv D c = 0 := by
  simp only [wxv]
  exact balance_wx D

private theorem balance_wyv : ∑ c, D.weight c * wyv D c = 0 := by
  simp only [wyv]
  exact balance_wy D

/-- **The collinear branch**: all double-angle vectors perpendicular to one
nonzero direction contradicts all-pairs failure — the sign-mixed pair has
K = −2(ℓ−1)(ℓ′−1) < 0. -/
private theorem collinear_contradiction
    (hK : ∀ c d, c ≠ d → 0 < obstruction D c d)
    (hheavy : ∀ c, 1 < leverageOf (D.atom c)) (hm1 : 0 < m)
    (r0 r1 : ℝ) (hr : 0 < r0 ^ 2 + r1 ^ 2)
    (hperp : ∀ c, wxv D c * r0 + wyv D c * r1 = 0) : False := by
  set mu : Fin m → ℝ := fun c => wyv D c * r0 - wxv D c * r1 with hmu
  have hmusq : ∀ c, mu c ^ 2
      = leverageOf (D.atom c) ^ 2 * (r0 ^ 2 + r1 ^ 2) := by
    intro c
    have hlen := wlen_sq D c
    simp only [hmu]
    linear_combination (-(wxv D c * r0 + wyv D c * r1)) * hperp c
      + (r0 ^ 2 + r1 ^ 2) * hlen
  have hlevpos : ∀ c, 0 < leverageOf (D.atom c) := fun c => by
    linarith [hheavy c]
  have hmune : ∀ c, mu c ≠ 0 := by
    intro c h0
    have hsq := hmusq c
    rw [h0] at hsq
    nlinarith [mul_pos (pow_pos (hlevpos c) 2) hr]
  have hbalmu : ∑ c, D.weight c * mu c = 0 := by
    simp only [hmu, show ∀ c, D.weight c * (wyv D c * r0 - wxv D c * r1)
        = r0 * (D.weight c * wyv D c) - r1 * (D.weight c * wxv D c) from
      fun c => by ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      balance_wyv, balance_wxv]
    ring
  -- the tangential components must change sign
  have hposex : ∃ c, 0 < mu c := by
    by_contra hall
    push Not at hall
    have hlt : ∑ c, D.weight c * mu c < 0 := by
      refine Finset.sum_neg (fun c _ => mul_neg_of_pos_of_neg (D.weight_pos c)
        (lt_of_le_of_ne (hall c) (hmune c))) ⟨⟨0, hm1⟩, Finset.mem_univ _⟩
    linarith [hbalmu]
  obtain ⟨cpos, hcpos⟩ := hposex
  have hnegex : ∃ d, mu d < 0 := by
    by_contra hall
    push Not at hall
    have hgt : 0 < ∑ c, D.weight c * mu c :=
      Finset.sum_pos' (fun c _ => mul_nonneg (D.weight_pos c).le (hall c))
        ⟨cpos, Finset.mem_univ _, mul_pos (D.weight_pos cpos) hcpos⟩
    linarith [hbalmu]
  obtain ⟨dneg, hdneg⟩ := hnegex
  have hcd : cpos ≠ dneg := fun h => by rw [h] at hcpos; linarith
  -- the pair's double-angle dot is exactly −ℓℓ′
  have hprod : (wxv D cpos * wxv D dneg + wyv D cpos * wyv D dneg)
        * (r0 ^ 2 + r1 ^ 2) = mu cpos * mu dneg := by
    simp only [hmu]
    linear_combination (wxv D dneg * r0 + wyv D dneg * r1) * hperp cpos
  have hsq : (wxv D cpos * wxv D dneg + wyv D cpos * wyv D dneg) ^ 2
      = leverageOf (D.atom cpos) ^ 2 * leverageOf (D.atom dneg) ^ 2 := by
    have h2 := hmusq cpos
    have h3 := hmusq dneg
    have hclear : (wxv D cpos * wxv D dneg + wyv D cpos * wyv D dneg) ^ 2
          * (r0 ^ 2 + r1 ^ 2) ^ 2
        = leverageOf (D.atom cpos) ^ 2 * leverageOf (D.atom dneg) ^ 2
          * (r0 ^ 2 + r1 ^ 2) ^ 2 := by
      linear_combination
        ((wxv D cpos * wxv D dneg + wyv D cpos * wyv D dneg)
            * (r0 ^ 2 + r1 ^ 2) + mu cpos * mu dneg) * hprod
          + mu dneg ^ 2 * h2
          + leverageOf (D.atom cpos) ^ 2 * (r0 ^ 2 + r1 ^ 2) * h3
    exact mul_right_cancel₀ (by positivity) hclear
  have hmm : mu cpos * mu dneg < 0 := mul_neg_of_pos_of_neg hcpos hdneg
  have hwneg : wxv D cpos * wxv D dneg + wyv D cpos * wyv D dneg < 0 := by
    nlinarith [hprod, hmm, hr]
  have hll : 0 < leverageOf (D.atom cpos) * leverageOf (D.atom dneg) :=
    mul_pos (hlevpos cpos) (hlevpos dneg)
  have hdot : wxv D cpos * wxv D dneg + wyv D cpos * wyv D dneg
      = -(leverageOf (D.atom cpos) * leverageOf (D.atom dneg)) := by
    have hfact : (wxv D cpos * wxv D dneg + wyv D cpos * wyv D dneg
          + leverageOf (D.atom cpos) * leverageOf (D.atom dneg))
        * (wxv D cpos * wxv D dneg + wyv D cpos * wyv D dneg
          - leverageOf (D.atom cpos) * leverageOf (D.atom dneg)) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfact with h | h
    · linarith
    · linarith
  -- the pair obstruction is −2(ℓ−1)(ℓ′−1) < 0, contradicting failure
  have hobs := hK cpos dneg hcd
  have hKval : obstruction D cpos dneg
      = -2 * (leverageOf (D.atom cpos) - 1)
        * (leverageOf (D.atom dneg) - 1) := by
    rw [obstruction_eq]
    simp only [zval]
    linear_combination hdot
  rw [hKval] at hobs
  nlinarith [hheavy cpos, hheavy dneg]

/-- **The positive-definite branch**: with the double-angle frame operator
nondegenerate, the adjugate-paired trace of Ψ = Ω² − ζζᵀ − 2Ω is nonnegative
by the cleared Schur bound, while all-pairs failure forces it negative
through the strict core at the witness u = ⟨w, r⟩. -/
private theorem pd_contradiction
    (hK : ∀ c d, c ≠ d → 0 < obstruction D c d)
    (hheavy : ∀ c, 1 < leverageOf (D.atom c))
    (hnocol : ∀ r0 r1 : ℝ, 0 < r0 ^ 2 + r1 ^ 2 →
      ∃ c, wxv D c * r0 + wyv D c * r1 ≠ 0) : False := by
  -- the six moment scalars
  set O00 : ℝ := ∑ c, D.weight c * wxv D c ^ 2 with hO00
  set O01 : ℝ := ∑ c, D.weight c * (wxv D c * wyv D c) with hO01
  set O11 : ℝ := ∑ c, D.weight c * wyv D c ^ 2 with hO11
  set Z0 : ℝ := ∑ c, D.weight c * (zval D c * wxv D c) with hZ0
  set Z1 : ℝ := ∑ c, D.weight c * (zval D c * wyv D c) with hZ1
  set sig : ℝ := ∑ c, D.weight c * zval D c ^ 2 with hsig
  -- the Ω quadratic form
  have hform : ∀ r0 r1 : ℝ, ∑ c, D.weight c
        * (wxv D c * r0 + wyv D c * r1) ^ 2
      = O00 * r0 ^ 2 + 2 * O01 * (r0 * r1) + O11 * r1 ^ 2 := by
    intro r0 r1
    simp only [show ∀ c, D.weight c * (wxv D c * r0 + wyv D c * r1) ^ 2
        = (D.weight c * wxv D c ^ 2) * r0 ^ 2
          + (D.weight c * (wxv D c * wyv D c)) * (2 * (r0 * r1))
          + (D.weight c * wyv D c ^ 2) * r1 ^ 2 from fun c => by ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul, ← Finset.sum_mul, hO00, hO01, hO11]
    ring
  -- nondegeneracy of the moments
  have hO00pos : 0 < O00 := by
    rw [hO00]
    rcases (Finset.sum_nonneg fun c (_ : c ∈ Finset.univ) =>
      mul_nonneg (D.weight_pos c).le (sq_nonneg (wxv D c))).lt_or_eq
      with h | h
    · exact h
    · exfalso
      obtain ⟨c, hc⟩ := hnocol 1 0 (by norm_num)
      have hall := (Finset.sum_eq_zero_iff_of_nonneg fun c _ =>
        mul_nonneg (D.weight_pos c).le (sq_nonneg (wxv D c))).mp h.symm
      have hzero := hall c (Finset.mem_univ c)
      have hwx0 : wxv D c = 0 := by
        have := (D.weight_pos c).ne'
        rcases mul_eq_zero.mp hzero with h' | h'
        · exact absurd h' this
        · exact pow_eq_zero_iff (n := 2) (by omega) |>.mp h'
      apply hc
      rw [hwx0]
      ring
  have hdetpos : 0 < O00 * O11 - O01 ^ 2 := by
    rcases lt_or_ge 0 (O00 * O11 - O01 ^ 2) with h | h
    · exact h
    · exfalso
      have hrpos : 0 < O01 ^ 2 + (-O00) ^ 2 := by
        nlinarith [sq_nonneg O01, mul_pos hO00pos hO00pos]
      have hf := hform O01 (-O00)
      have hval : O00 * O01 ^ 2 + 2 * O01 * (O01 * -O00) + O11 * (-O00) ^ 2
          = O00 * (O00 * O11 - O01 ^ 2) := by ring
      rw [hval] at hf
      have hle : O00 * (O00 * O11 - O01 ^ 2) ≤ 0 := by nlinarith [hO00pos]
      have hzero : ∑ c, D.weight c
          * (wxv D c * O01 + wyv D c * -O00) ^ 2 = 0 := by
        have hnn : 0 ≤ ∑ c, D.weight c
            * (wxv D c * O01 + wyv D c * -O00) ^ 2 :=
          Finset.sum_nonneg fun c _ =>
            mul_nonneg (D.weight_pos c).le (sq_nonneg _)
        linarith [hf, hle, hnn]
      obtain ⟨c, hc⟩ := hnocol O01 (-O00) hrpos
      have hall := (Finset.sum_eq_zero_iff_of_nonneg fun c _ =>
        mul_nonneg (D.weight_pos c).le (sq_nonneg _)).mp hzero
      have hzc := hall c (Finset.mem_univ c)
      apply hc
      rcases mul_eq_zero.mp hzc with h' | h'
      · exact absurd h' (D.weight_pos c).ne'
      · exact pow_eq_zero_iff (n := 2) (by omega) |>.mp h'
  -- σ = trΩ − 4
  have htrsig : sig = O00 + O11 - 4 := by
    have htr2 := trace_two D
    have hone := D.weight_sum_one
    have hsplit : ∑ c, D.weight c
        * (wxv D c ^ 2 + wyv D c ^ 2 - leverageOf (D.atom c) ^ 2) = 0 :=
      Finset.sum_eq_zero fun c _ => by rw [wlen_sq]; ring
    have hzz : ∑ c, D.weight c * (zval D c ^ 2
        - leverageOf (D.atom c) ^ 2 + 4 * leverageOf (D.atom c) - 4) = 0 :=
      Finset.sum_eq_zero fun c _ => by rw [zval]; ring
    have e1 : ∑ c, D.weight c * (wxv D c ^ 2 + wyv D c ^ 2
        - leverageOf (D.atom c) ^ 2)
        = O00 + O11 - ∑ c, D.weight c * leverageOf (D.atom c) ^ 2 := by
      simp only [show ∀ c, D.weight c * (wxv D c ^ 2 + wyv D c ^ 2
          - leverageOf (D.atom c) ^ 2)
          = D.weight c * wxv D c ^ 2 + D.weight c * wyv D c ^ 2
            - D.weight c * leverageOf (D.atom c) ^ 2 from fun c => by ring]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hO00, hO11]
    have e2 : ∑ c, D.weight c * (zval D c ^ 2
        - leverageOf (D.atom c) ^ 2 + 4 * leverageOf (D.atom c) - 4)
        = sig - ∑ c, D.weight c * leverageOf (D.atom c) ^ 2
          + 4 * ∑ c, D.weight c * leverageOf (D.atom c)
          - 4 * ∑ c, D.weight c := by
      simp only [show ∀ c, D.weight c * (zval D c ^ 2
          - leverageOf (D.atom c) ^ 2 + 4 * leverageOf (D.atom c) - 4)
          = D.weight c * zval D c ^ 2
            - D.weight c * leverageOf (D.atom c) ^ 2
            + 4 * (D.weight c * leverageOf (D.atom c)) - 4 * D.weight c from
        fun c => by ring]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsig]
    rw [e1] at hsplit
    rw [e2, htr2, hone] at hzz
    linarith
  -- the cleared Schur bound: detΩ·σ ≥ ζᵀ·adjΩ·ζ
  have hP1 : 0 ≤ (O00 * O11 - O01 ^ 2) * sig
      - (O11 * Z0 ^ 2 - 2 * O01 * (Z0 * Z1) + O00 * Z1 ^ 2) := by
    set A : ℝ := O11 * Z0 - O01 * Z1 with hA
    set B : ℝ := O00 * Z1 - O01 * Z0 with hB
    set det : ℝ := O00 * O11 - O01 ^ 2 with hdet
    have hSOS : 0 ≤ ∑ c, D.weight c
        * (det * zval D c - wxv D c * A - wyv D c * B) ^ 2 :=
      Finset.sum_nonneg fun c _ =>
        mul_nonneg (D.weight_pos c).le (sq_nonneg _)
    have hexpand : ∑ c, D.weight c
        * (det * zval D c - wxv D c * A - wyv D c * B) ^ 2
        = det ^ 2 * sig - 2 * det * (A * Z0 + B * Z1)
          + (A ^ 2 * O00 + 2 * (A * B) * O01 + B ^ 2 * O11) := by
      simp only [show ∀ c, D.weight c
          * (det * zval D c - wxv D c * A - wyv D c * B) ^ 2
          = det ^ 2 * (D.weight c * zval D c ^ 2)
            - 2 * det * A * (D.weight c * (zval D c * wxv D c))
            - 2 * det * B * (D.weight c * (zval D c * wyv D c))
            + A ^ 2 * (D.weight c * wxv D c ^ 2)
            + 2 * (A * B) * (D.weight c * (wxv D c * wyv D c))
            + B ^ 2 * (D.weight c * wyv D c ^ 2) from fun c => by ring]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum, hsig, hZ0, hZ1, hO00, hO01, hO11]
      ring
    rw [hexpand] at hSOS
    -- the expansion collapses to det·(det·σ − ζᵀadjΩζ)
    have hcollapse : det ^ 2 * sig - 2 * det * (A * Z0 + B * Z1)
          + (A ^ 2 * O00 + 2 * (A * B) * O01 + B ^ 2 * O11)
        = det * (det * sig
            - (O11 * Z0 ^ 2 - 2 * O01 * (Z0 * Z1) + O00 * Z1 ^ 2)) := by
      rw [hA, hB, hdet]
      ring
    rw [hcollapse] at hSOS
    nlinarith [hSOS, hdetpos]
  -- the Ψ entries
  set P00 : ℝ := O00 ^ 2 + O01 ^ 2 - Z0 ^ 2 - 2 * O00 with hP00
  set P01 : ℝ := O00 * O01 + O01 * O11 - Z0 * Z1 - 2 * O01 with hP01
  set P11 : ℝ := O01 ^ 2 + O11 ^ 2 - Z1 ^ 2 - 2 * O11 with hP11
  -- the adjugate-paired trace is nonnegative
  have hTnn : 0 ≤ O11 * P00 - 2 * O01 * P01 + O00 * P11 := by
    have hT : O11 * P00 - 2 * O01 * P01 + O00 * P11
        = (O00 * O11 - O01 ^ 2) * (O00 + O11 - 4)
          - (O11 * Z0 ^ 2 - 2 * O01 * (Z0 * Z1) + O00 * Z1 ^ 2) := by
      rw [hP00, hP01, hP11]
      ring
    rw [hT, ← htrsig]
    exact hP1
  -- split on the sign behaviour of the Ψ form
  by_cases hpsi : ∀ r0 r1 : ℝ, 0 < r0 ^ 2 + r1 ^ 2 →
      P00 * r0 ^ 2 + 2 * P01 * (r0 * r1) + P11 * r1 ^ 2 < 0
  · -- Ψ negative definite: the adjugate pairing goes strictly negative
    have h00 : P00 < 0 := by
      have := hpsi 1 0 (by norm_num)
      nlinarith [this]
    have h11 : P11 < 0 := by
      have := hpsi 0 1 (by norm_num)
      nlinarith [this]
    have hdetPsi : 0 < P00 * P11 - P01 ^ 2 := by
      have hr : 0 < P01 ^ 2 + (-P00) ^ 2 := by
        nlinarith [sq_nonneg P01, mul_pos_of_neg_of_neg h00 h00]
      have := hpsi P01 (-P00) hr
      nlinarith [this, h00]
    -- tr(adjΩ·(−Ψ)) > 0 by the polynomial pairing certificate
    have hformadj : 0 < O11 * (-P00) ^ 2 - 2 * O01 * ((-P00) * (-P01))
        + O00 * (-P01) ^ 2 := by
      -- O00·form = (O00·P01 − O01·P00)² + detΩ·P00² > 0 since P00 ≠ 0
      nlinarith [sq_nonneg (O00 * P01 - O01 * P00), hO00pos,
        mul_pos hdetpos (mul_pos_of_neg_of_neg h00 h00)]
    have hTneg : O11 * P00 - 2 * O01 * P01 + O00 * P11 < 0 := by
      -- P00·T = adjΩ-form(−P00,−P01) + O00·detΨ > 0 with P00 < 0
      nlinarith [hformadj, mul_pos hO00pos hdetPsi, h00]
    linarith [hTnn, hTneg]
  · -- some direction has Ψ-form ≥ 0: the core witness fires
    push Not at hpsi
    obtain ⟨r0, r1, hrpos, hpsige⟩ := hpsi
    set u : Fin m → ℝ := fun c => wxv D c * r0 + wyv D c * r1 with hu
    -- the balance kills Σt·u
    have hU0 : ∑ c, D.weight c * u c = 0 := by
      simp only [hu, show ∀ c, D.weight c * (wxv D c * r0 + wyv D c * r1)
          = r0 * (D.weight c * wxv D c) + r1 * (D.weight c * wyv D c) from
        fun c => by ring]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        balance_wxv, balance_wyv]
      ring
    -- nonconstancy from nondegeneracy
    obtain ⟨c1, hc1⟩ := hnocol r0 r1 hrpos
    have hnonconst : ∃ c0 d0 : Fin m, u c0 ≠ u d0 := by
      by_contra hall
      push Not at hall
      have hconstsum : ∑ c, D.weight c * u c = u c1 := by
        simp only [show ∀ c, D.weight c * u c = D.weight c * u c1 from
          fun c => by rw [hall c c1], ← Finset.sum_mul, D.weight_sum_one,
          one_mul]
      rw [hU0] at hconstsum
      exact hc1 hconstsum.symm
    obtain ⟨c0, d0, hne⟩ := hnonconst
    have hcore := core_strict D hK u hne
    -- the moment components of the witness
    have hSW0 : ∑ c, D.weight c * (u c * wxv D c) = O00 * r0 + O01 * r1 := by
      simp only [hu, show ∀ c, D.weight c
          * ((wxv D c * r0 + wyv D c * r1) * wxv D c)
          = (D.weight c * wxv D c ^ 2) * r0
            + (D.weight c * (wxv D c * wyv D c)) * r1 from fun c => by ring]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        hO00, hO01]
    have hSW1 : ∑ c, D.weight c * (u c * wyv D c) = O01 * r0 + O11 * r1 := by
      simp only [hu, show ∀ c, D.weight c
          * ((wxv D c * r0 + wyv D c * r1) * wyv D c)
          = (D.weight c * (wxv D c * wyv D c)) * r0
            + (D.weight c * wyv D c ^ 2) * r1 from fun c => by ring]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        hO01, hO11]
    have hSZ : ∑ c, D.weight c * (u c * zval D c) = Z0 * r0 + Z1 * r1 := by
      simp only [hu, show ∀ c, D.weight c
          * ((wxv D c * r0 + wyv D c * r1) * zval D c)
          = (D.weight c * (zval D c * wxv D c)) * r0
            + (D.weight c * (zval D c * wyv D c)) * r1 from fun c => by ring]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        hZ0, hZ1]
    have hUU : ∑ c, D.weight c * u c ^ 2
        = O00 * r0 ^ 2 + 2 * O01 * (r0 * r1) + O11 * r1 ^ 2 := by
      simp only [hu]
      exact hform r0 r1
    -- identify the core's left side with the Ψ form plus 2·q(r)
    have hinner : ∀ c, ∑ d, D.weight d * (u d * obstruction D c d)
        = wxv D c * (O00 * r0 + O01 * r1) + wyv D c * (O01 * r0 + O11 * r1)
          - zval D c * (Z0 * r0 + Z1 * r1) := by
      intro c
      simp only [show ∀ d, D.weight d * (u d * obstruction D c d)
          = wxv D c * (D.weight d * (u d * wxv D d))
            + wyv D c * (D.weight d * (u d * wyv D d))
            - zval D c * (D.weight d * (u d * zval D d))
            + 2 * (D.weight d * u d) from fun d => by
        rw [obstruction_eq]; ring]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum, hSW0, hSW1, hSZ, hU0]
      ring
    have houter : ∑ c, D.weight c
        * (u c * ∑ d, D.weight d * (u d * obstruction D c d))
        = (O00 * r0 + O01 * r1) ^ 2 + (O01 * r0 + O11 * r1) ^ 2
          - (Z0 * r0 + Z1 * r1) ^ 2 := by
      simp only [show ∀ c, D.weight c
          * (u c * ∑ d, D.weight d * (u d * obstruction D c d))
          = (O00 * r0 + O01 * r1) * (D.weight c * (u c * wxv D c))
            + (O01 * r0 + O11 * r1) * (D.weight c * (u c * wyv D c))
            - (Z0 * r0 + Z1 * r1) * (D.weight c * (u c * zval D c)) from
        fun c => by rw [hinner c]; ring]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum, hSW0, hSW1, hSZ]
      ring
    rw [houter, hUU] at hcore
    -- hcore now contradicts the chosen direction's Ψ-form ≥ 0
    nlinarith [hcore, hpsige]

/-- **Case B**: a heavy weighted (m,2) design always contains a dominating
pair. -/
theorem exists_dominating_pair_of_heavy
    (hheavy : ∀ c, 1 < leverageOf (D.atom c)) :
    ∃ C : Finset (Fin m), C.card = 2 ∧ Dominates D C := by
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · exact absurd D.weight_sum_one (by simp)
  by_contra hno
  push Not at hno
  have hK : ∀ c d, c ≠ d → 0 < obstruction D c d := fun c d hcd =>
    obstruction_pos_of_not_dominates D hcd (hheavy c) (hheavy d)
      (hno {c, d} (Finset.card_pair hcd))
  by_cases hcol : ∃ r0 r1 : ℝ, 0 < r0 ^ 2 + r1 ^ 2 ∧
      ∀ c, wxv D c * r0 + wyv D c * r1 = 0
  · obtain ⟨r0, r1, hr, hperp⟩ := hcol
    exact collinear_contradiction D hK hheavy hm1 r0 r1 hr hperp
  · push Not at hcol
    exact pd_contradiction D hK hheavy hcol

end CaseB

end Gtz
