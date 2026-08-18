import Mathlib.LinearAlgebra.CrossProduct
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Plane Cramer and the spread bound

Frame-free two-dimensional linear algebra on the plane orthogonal to a unit
vector `u` in `ℝ³`, through the scalar `D(a,b) := u ⬝ᵥ (a ×₃ b)` — the signed
plane determinant.  No basis of the plane is ever chosen.

* `quadruple_product` — the four-vector dependency of `ℝ³`, a polynomial
  identity: `D(a,b)•q = (q·(a×b))•u + D(q,b)•a + D(a,q)•b`.
* `triple_product_eq_zero_of_orth` — three plane vectors have vanishing
  triple product; follows from the quadruple identity dotted with `u`.
* `plane_cramer` — Cramer's rule in the plane:
  `D(a,b)•q = D(q,b)•a + D(a,q)•b` for plane vectors.
* `planeDet_sq_le` — `D(a,b)² ≤ |a|²|b|²`, Cauchy–Schwarz through the
  Binet–Cauchy identity.
* `spread_sq_bound` — **the spread bound**: a plane vector reading small
  against two plane directions bounds their determinant,
  `D(w₂,w₃)²·|q|² ≤ 2(|w₃|²(q·w₂)² + |w₂|²(q·w₃)²)`.
  A long vector with two small readings forces the two directions towards a
  common line.  This is the instrument of the planar corank-two endgame: the
  thin-pair witnesses of a hypothetical tie would all collapse onto one
  direction, where the reading floor forbids quiet.
-/

namespace Gtz

open Matrix

/-- **The four-vector dependency of `ℝ³`.**  A polynomial identity: any four
vectors satisfy
`(u·(a×b))•q = (q·(a×b))•u + (u·(q×b))•a + (u·(a×q))•b`. -/
theorem quadruple_product (u a b q : Fin 3 → ℝ) :
    (u ⬝ᵥ crossProduct a b) • q
      = (q ⬝ᵥ crossProduct a b) • u + (u ⬝ᵥ crossProduct q b) • a
        + (u ⬝ᵥ crossProduct a q) • b := by
  funext i
  fin_cases i <;>
    simp [cross_apply, dotProduct, Fin.sum_univ_three, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] <;>
    ring

/-- **Three plane vectors have vanishing triple product.**  Dot the quadruple
identity with the unit normal. -/
theorem triple_product_eq_zero_of_orth {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    {a b q : Fin 3 → ℝ} (ha : a ⬝ᵥ u = 0) (hb : b ⬝ᵥ u = 0)
    (hq : q ⬝ᵥ u = 0) : q ⬝ᵥ crossProduct a b = 0 := by
  have h := congrArg (fun v => v ⬝ᵥ u) (quadruple_product u a b q)
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, hunit, ha, hb, hq,
    mul_zero, mul_one, add_zero, zero_add] at h
  linarith [h]

/-- **Cramer's rule in the plane.**  For plane vectors the quadruple identity
loses its normal component:
`D(a,b)•q = D(q,b)•a + D(a,q)•b`. -/
theorem plane_cramer {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    {a b q : Fin 3 → ℝ} (ha : a ⬝ᵥ u = 0) (hb : b ⬝ᵥ u = 0)
    (hq : q ⬝ᵥ u = 0) :
    (u ⬝ᵥ crossProduct a b) • q
      = (u ⬝ᵥ crossProduct q b) • a + (u ⬝ᵥ crossProduct a q) • b := by
  have h := quadruple_product u a b q
  rw [triple_product_eq_zero_of_orth hunit ha hb hq, zero_smul, zero_add] at h
  exact h

/-- The self-dotted plane Cramer:
`D(a,b)·(q·q) = D(q,b)·(a·q) + D(a,q)·(b·q)`. -/
theorem plane_cramer_selfdot {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    {a b q : Fin 3 → ℝ} (ha : a ⬝ᵥ u = 0) (hb : b ⬝ᵥ u = 0)
    (hq : q ⬝ᵥ u = 0) :
    (u ⬝ᵥ crossProduct a b) * (q ⬝ᵥ q)
      = (u ⬝ᵥ crossProduct q b) * (a ⬝ᵥ q)
        + (u ⬝ᵥ crossProduct a q) * (b ⬝ᵥ q) := by
  have h := congrArg (fun v => v ⬝ᵥ q) (plane_cramer hunit ha hb hq)
  simpa [add_dotProduct, smul_dotProduct, smul_eq_mul] using h

/-- **The plane determinant is capped by the norms**:
`D(a,b)² ≤ |a|²·|b|²`.  Cauchy–Schwarz against the unit normal, then
Binet–Cauchy. -/
theorem planeDet_sq_le {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (a b : Fin 3 → ℝ) :
    (u ⬝ᵥ crossProduct a b) ^ 2 ≤ (a ⬝ᵥ a) * (b ⬝ᵥ b) := by
  have hcs := dotProduct_sq_le_mul u (crossProduct a b)
  rw [hunit, one_mul] at hcs
  have hbc := cross_dot_cross a b a b
  have hcomm : b ⬝ᵥ a = a ⬝ᵥ b := dotProduct_comm b a
  rw [hcomm] at hbc
  nlinarith [hcs, hbc, sq_nonneg (a ⬝ᵥ b)]

/-- **THE SPREAD BOUND.**  A plane vector's readings against two plane
directions bound their determinant:

  `D(w₂,w₃)²·|q|² ≤ 2·(|w₃|²·(q·w₂)² + |w₂|²·(q·w₃)²)` .

A long `q` with two small readings forces `w₂` and `w₃` towards a common
line. -/
theorem spread_sq_bound {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    {q w₂ w₃ : Fin 3 → ℝ} (hq : q ⬝ᵥ u = 0) (h2 : w₂ ⬝ᵥ u = 0)
    (h3 : w₃ ⬝ᵥ u = 0) :
    (u ⬝ᵥ crossProduct w₂ w₃) ^ 2 * (q ⬝ᵥ q)
      ≤ 2 * ((w₃ ⬝ᵥ w₃) * (q ⬝ᵥ w₂) ^ 2 + (w₂ ⬝ᵥ w₂) * (q ⬝ᵥ w₃) ^ 2) := by
  rcases eq_or_ne q 0 with rfl | hqne
  · simp only [zero_dotProduct]
    have h2n := dotProduct_self_nonneg w₂
    have h3n := dotProduct_self_nonneg w₃
    nlinarith
  · have hqpos := dotProduct_self_pos hqne
    have hsd := plane_cramer_selfdot hunit h2 h3 hq
    have hb1 := planeDet_sq_le hunit q w₃
    have hb2 := planeDet_sq_le hunit w₂ q
    have haq : w₂ ⬝ᵥ q = q ⬝ᵥ w₂ := dotProduct_comm w₂ q
    have hbq : w₃ ⬝ᵥ q = q ⬝ᵥ w₃ := dotProduct_comm w₃ q
    rw [haq, hbq] at hsd
    have hsq : ((u ⬝ᵥ crossProduct w₂ w₃) * (q ⬝ᵥ q)) ^ 2
        ≤ 2 * ((u ⬝ᵥ crossProduct q w₃) ^ 2 * (q ⬝ᵥ w₂) ^ 2
          + (u ⬝ᵥ crossProduct w₂ q) ^ 2 * (q ⬝ᵥ w₃) ^ 2) := by
      calc ((u ⬝ᵥ crossProduct w₂ w₃) * (q ⬝ᵥ q)) ^ 2
          = ((u ⬝ᵥ crossProduct q w₃) * (q ⬝ᵥ w₂)
              + (u ⬝ᵥ crossProduct w₂ q) * (q ⬝ᵥ w₃)) ^ 2 := by
            rw [hsd]
        _ ≤ 2 * ((u ⬝ᵥ crossProduct q w₃) ^ 2 * (q ⬝ᵥ w₂) ^ 2
              + (u ⬝ᵥ crossProduct w₂ q) ^ 2 * (q ⬝ᵥ w₃) ^ 2) := by
            nlinarith [sq_nonneg ((u ⬝ᵥ crossProduct q w₃) * (q ⬝ᵥ w₂)
              - (u ⬝ᵥ crossProduct w₂ q) * (q ⬝ᵥ w₃))]
    have hchain : ((u ⬝ᵥ crossProduct w₂ w₃) * (q ⬝ᵥ q)) ^ 2
        ≤ 2 * ((q ⬝ᵥ q) * (w₃ ⬝ᵥ w₃) * (q ⬝ᵥ w₂) ^ 2
          + (w₂ ⬝ᵥ w₂) * (q ⬝ᵥ q) * (q ⬝ᵥ w₃) ^ 2) := by
      have hm1 := mul_le_mul_of_nonneg_right hb1 (sq_nonneg (q ⬝ᵥ w₂))
      have hm2 := mul_le_mul_of_nonneg_right hb2 (sq_nonneg (q ⬝ᵥ w₃))
      nlinarith [hsq, hm1, hm2]
    have hfactor : ((u ⬝ᵥ crossProduct w₂ w₃) ^ 2 * (q ⬝ᵥ q)) * (q ⬝ᵥ q)
        ≤ (2 * ((w₃ ⬝ᵥ w₃) * (q ⬝ᵥ w₂) ^ 2
          + (w₂ ⬝ᵥ w₂) * (q ⬝ᵥ w₃) ^ 2)) * (q ⬝ᵥ q) := by
      nlinarith [hchain]
    exact le_of_mul_le_mul_right hfactor hqpos

end Gtz
