import Gtz.Wave.DualFrameBudget
import Gtz.Wave.WeightGapDeterminant
import Gtz.Wave.InvariantTaxTeeth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The erased-energy ledger

The weight-gap determinant law prices the both-light roof in seven weighted
terms.  This module pins the terms that carry the erased atom: the witness
components `ω_d = g_d·g_x` obey an exact weighted Parseval pin, the erased
outside energy `kxx` is their square total minus one, the corner scale cap
makes every `λ`-carrying term weight-polynomial, and the Cayley adjugate
turns the erased adjugate reading into plain `ω`-data.

* `Gtz.corner_erased_outside_energy_pin` — `Σ_d t_d·(g_d·g_x)² = 1 − t_x`.
* `Gtz.corner_erased_energy_eq` — `kxx = Σ_d (g_d·g_x)² − 1` at `(6,3)`.
* `Gtz.corner_erased_energy_cap` / `_floor` — the two-sided weight control
  `t_min·(kxx+1) ≤ 1 − t_x ≤ t_max·(kxx+1)`.
* `Gtz.corner_bothLight_kxx_pos` — on the both-light cell `kxx > 0`: the
  `y`-four-set reads the erased atom only through `kxx`.
* `Gtz.corner_lambda_weight_cap` — `t_yt_z·(1+λ) ≤ t_y + t_z − t_yt_z`:
  the corner scale cap makes the `λ`-terms weight-polynomial.
* `Gtz.corner_bothLight_lambda_terms_cap` — the two `λ`-carrying terms of
  the weight-gap law together obey
  `(1+λ)·(t_yt_z·kxx + t_xt_yt_z) ≤ (t_y + t_z − t_yt_z)·(kxx + t_x)`.
* `Gtz.corner_erased_adjugate_cayley` — `KRx = |K·g_x|² − tr K·kxx + e₂(K)`.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The witness pin -/

/-- **THE WITNESS PIN.**  Parseval read at the erased atom: the weighted
squares of the outside witness components total the erased weight slack:

  `Σ_{d ∈ Cᶜ} t_d·(g_d·g_x)² = 1 − t_x` . -/
theorem corner_erased_outside_energy_pin {m : ℕ} (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) (hxz0 : D.atom x ⬝ᵥ D.atom z = 0) :
    (∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * (D.atom d ⬝ᵥ D.atom x) ^ 2)
      = 1 - D.weight x := by
  classical
  have heig := corner_weightedComplement_eigen D hxy hxz hyz hxunit hxy0 hxz0
  have hread := congrArg (fun v => D.atom x ⬝ᵥ v) heig
  rw [dotProduct_smul, smul_eq_mul, hxunit, mul_one] at hread
  rw [← hread]
  rw [show (∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d • atomMatrix (D.atom d)) *ᵥ D.atom x
      = ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          (D.weight d • atomMatrix (D.atom d)) *ᵥ D.atom x from by
    rw [Matrix.sum_mulVec]]
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_mulVec,
    show atomMatrix (D.atom d) *ᵥ D.atom x
      = (D.atom d ⬝ᵥ D.atom x) • D.atom d from vecMulVec_mulVec_eq _ _ _,
    dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [dotProduct_comm (D.atom x) (D.atom d)]
  ring

/-! ## 2. The erased outside energy -/

/-- **THE ERASED ENERGY.**  At `(6,3)` the erased energy of the outside gap
is the witness square total minus one:

  `g_xᵀ(S_{Cᶜ} − 1)g_x = Σ_d (g_d·g_x)² − 1` . -/
theorem corner_erased_energy_eq (D : WeightedDesign 6 3)
    {x y z d4 d5 d6 : Fin 6}
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6})
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1) :
    D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
        *ᵥ D.atom x)
      = (D.atom d4 ⬝ᵥ D.atom x) ^ 2 + (D.atom d5 ⬝ᵥ D.atom x) ^ 2
        + (D.atom d6 ⬝ᵥ D.atom x) ^ 2 - 1 := by
  rw [hcompl, subsetSum, Finset.sum_insert (by simp [h45, h46]),
    Finset.sum_insert (by simp [h56]), Finset.sum_singleton,
    Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add,
    show atomMatrix (D.atom d4) *ᵥ D.atom x
      = (D.atom d4 ⬝ᵥ D.atom x) • D.atom d4 from vecMulVec_mulVec_eq _ _ _,
    show atomMatrix (D.atom d5) *ᵥ D.atom x
      = (D.atom d5 ⬝ᵥ D.atom x) • D.atom d5 from vecMulVec_mulVec_eq _ _ _,
    show atomMatrix (D.atom d6) *ᵥ D.atom x
      = (D.atom d6 ⬝ᵥ D.atom x) • D.atom d6 from vecMulVec_mulVec_eq _ _ _,
    dotProduct_smul, dotProduct_smul, dotProduct_smul, hxunit]
  simp only [smul_eq_mul]
  rw [dotProduct_comm (D.atom x) (D.atom d4),
    dotProduct_comm (D.atom x) (D.atom d5),
    dotProduct_comm (D.atom x) (D.atom d6)]
  ring

/-- **THE ERASED ENERGY CAP.**  The witness pin bounds the erased weight
slack by the largest outside weight against the erased energy:

  `1 − t_x ≤ t_max·(kxx + 1)` . -/
theorem corner_erased_energy_cap (D : WeightedDesign 6 3)
    {x y z d4 d5 d6 : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6})
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) (hxz0 : D.atom x ⬝ᵥ D.atom z = 0)
    {tcap : ℝ} (hc4 : D.weight d4 ≤ tcap) (hc5 : D.weight d5 ≤ tcap)
    (hc6 : D.weight d6 ≤ tcap) :
    1 - D.weight x
      ≤ tcap * ((D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ)
          - 1) *ᵥ D.atom x)) + 1) := by
  have hpin := corner_erased_outside_energy_pin D hxy hxz hyz hxunit hxy0 hxz0
  rw [hcompl, Finset.sum_insert (by simp [h45, h46]),
    Finset.sum_insert (by simp [h56]), Finset.sum_singleton] at hpin
  have henergy := corner_erased_energy_eq D h45 h46 h56 hcompl hxunit
  rw [henergy]
  nlinarith [hpin, sq_nonneg (D.atom d4 ⬝ᵥ D.atom x),
    sq_nonneg (D.atom d5 ⬝ᵥ D.atom x), sq_nonneg (D.atom d6 ⬝ᵥ D.atom x)]

/-- **THE ERASED ENERGY FLOOR.**  The mirror bound with the smallest outside
weight: `t_min·(kxx + 1) ≤ 1 − t_x`. -/
theorem corner_erased_energy_floor (D : WeightedDesign 6 3)
    {x y z d4 d5 d6 : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6})
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) (hxz0 : D.atom x ⬝ᵥ D.atom z = 0)
    {tfloor : ℝ}
    (hc4 : tfloor ≤ D.weight d4) (hc5 : tfloor ≤ D.weight d5)
    (hc6 : tfloor ≤ D.weight d6) :
    tfloor * ((D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ)
          - 1) *ᵥ D.atom x)) + 1)
      ≤ 1 - D.weight x := by
  have hpin := corner_erased_outside_energy_pin D hxy hxz hyz hxunit hxy0 hxz0
  rw [hcompl, Finset.sum_insert (by simp [h45, h46]),
    Finset.sum_insert (by simp [h56]), Finset.sum_singleton] at hpin
  have henergy := corner_erased_energy_eq D h45 h46 h56 hcompl hxunit
  rw [henergy]
  nlinarith [hpin, sq_nonneg (D.atom d4 ⬝ᵥ D.atom x),
    sq_nonneg (D.atom d5 ⬝ᵥ D.atom x), sq_nonneg (D.atom d6 ⬝ᵥ D.atom x)]

/-! ## 3. The positive erased energy of the both-light cell -/

/-- **`kxx` IS POSITIVE ON THE BOTH-LIGHT CELL.**  The `y`-four-set gap reads
the erased atom only through the outside gap, because the corner erases the
`g_y` component.  Positive definiteness then forces `kxx > 0`. -/
theorem corner_bothLight_kxx_pos {m : ℕ} (D : WeightedDesign m 3)
    {x y z : Fin m}
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1).PosDef)
    (hynot : y ∉ (({x, y, z} : Finset (Fin m))ᶜ))
    (hxne : D.atom x ≠ 0)
    (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) :
    0 < D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) - 1)
        *ᵥ D.atom x) := by
  have hsplit : subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ))
      = atomMatrix (D.atom y) + subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) := by
    rw [subsetSum, subsetSum, Finset.sum_insert hynot]
  have hread := hAy.dotProduct_mulVec_pos hxne
  rw [star_trivial, hsplit] at hread
  rw [show (atomMatrix (D.atom y)
      + subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) - 1) *ᵥ D.atom x
      = atomMatrix (D.atom y) *ᵥ D.atom x
        + (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) - 1) *ᵥ D.atom x from by
    rw [← Matrix.add_mulVec]
    congr 1
    abel] at hread
  rw [dotProduct_add,
    show atomMatrix (D.atom y) *ᵥ D.atom x
      = (D.atom y ⬝ᵥ D.atom x) • D.atom y from vecMulVec_mulVec_eq _ _ _,
    dotProduct_smul, dotProduct_comm (D.atom y) (D.atom x), hxy0] at hread
  simpa using hread

/-! ## 4. The weight-polynomial scale cap -/

/-- **THE `λ`-WEIGHT CAP.**  The corner scale cap makes the paired inside
weights swallow the scale: `t_yt_z·(1+λ) ≤ t_y + t_z − t_yt_z`. -/
theorem corner_lambda_weight_cap {m : ℕ} (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1) :
    D.weight y * D.weight z * (1 + lam)
      ≤ D.weight y + D.weight z - D.weight y * D.weight z := by
  have hcap := corner_scale_cap D hxy hxz hyz hunit hgap hxunit
  have hy := D.weight_pos y
  have hz := D.weight_pos z
  have hyinv : D.weight y * (1 / D.weight y) = 1 := by
    field_simp
  have hzinv : D.weight z * (1 / D.weight z) = 1 := by
    field_simp
  nlinarith [hcap, mul_pos hy hz, hyinv, hzinv]

/-- **THE `λ`-TERMS CAP.**  The two `λ`-carrying terms of the weight-gap law
are together weight-polynomial against the positive erased energy:

  `(1+λ)·(t_yt_z·kxx + t_xt_yt_z) ≤ (t_y + t_z − t_yt_z)·(kxx + t_x)` . -/
theorem corner_bothLight_lambda_terms_cap (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hkxx : 0 < D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
        *ᵥ D.atom x)) :
    (1 + lam) * (D.weight y * D.weight z
          * (D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
              *ᵥ D.atom x))
        + D.weight x * D.weight y * D.weight z)
      ≤ (D.weight y + D.weight z - D.weight y * D.weight z)
        * ((D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
            *ᵥ D.atom x)) + D.weight x) := by
  have hcap := corner_lambda_weight_cap D hxy hxz hyz hunit hgap hxunit
  have hx := D.weight_pos x
  nlinarith [hcap, hkxx, hx, mul_pos (D.weight_pos y) (D.weight_pos z)]

/-! ## 5. The Cayley form of the erased adjugate reading -/

/-- **THE ERASED ADJUGATE READING, CAYLEY FORM.**  At a unit erased atom the
adjugate reading of the outside gap is plain quadratic data:

  `g_xᵀ(adj K)g_x = |K·g_x|² − tr K·kxx + e₂(K)` . -/
theorem corner_erased_adjugate_cayley (D : WeightedDesign 6 3)
    {x y z : Fin 6}
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1) :
    D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).adjugate
        *ᵥ D.atom x)
      = ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1) *ᵥ D.atom x) ⬝ᵥ
          ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1) *ᵥ D.atom x)
        - Matrix.trace (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
          * (D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
              *ᵥ D.atom x))
        + ((Matrix.trace (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)) ^ 2
            - Matrix.trace ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
              * (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1))) / 2 := by
  classical
  set K : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1 with hKDef
  have hKsym : Kᵀ = K := by
    rw [hKDef, Matrix.transpose_sub, Matrix.transpose_one, subsetSum,
      Matrix.transpose_sum]
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    exact transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom d)).1
  rw [adjugate_eq_fin_three_cayley K, Matrix.add_mulVec, Matrix.sub_mulVec,
    dotProduct_add, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
    Matrix.smul_mulVec, dotProduct_smul, Matrix.one_mulVec, hxunit,
    ← Matrix.mulVec_mulVec]
  have hsq : D.atom x ⬝ᵥ (K *ᵥ (K *ᵥ D.atom x))
      = (K *ᵥ D.atom x) ⬝ᵥ (K *ᵥ D.atom x) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hKsym]
  rw [hsq]
  simp only [smul_eq_mul, mul_one]

end Gtz
