/-
# Stress-certificate weak duality

A tie's frame multiplier, when it exists, is a nonnegative "stress certificate": a
family of directions `dir_i` and weights `coeff_i ≥ 0` whose squared-projection sums
reproduce the design weights, `∑_i coeff_i ⟨g_c, dir_i⟩² = t_c` for every atom `c`.
`no_separating_slope_of_stressCertificate` is the weak-duality half of the associated
theorem of alternatives: whenever such a certificate exists, no slope `y` can keep the
combined form `∑_c y_c ⟨g_c, dir_i⟩²` nonnegative on the certificate directions while
driving the weight-pairing `∑_c t_c y_c` negative — one line of `Finset.sum_comm`.

`tetraDesign` is the regular tetrahedron `(4,3)` tight frame (uniform weights `1/4`),
in which every 3-subset ties at `λ_min = 1`; `tetra_no_separating_slope` discharges the
alternative there unconditionally with the explicit certificate `coeff ≡ 1/48`
(multiplier `Λ = I/12`).
-/
import Mathlib
import Gtz.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz
open Matrix
variable {m k : ℕ}

/-- **Weak duality for the stress certificate.** Given nonnegative `coeff` over a
direction family whose squared-projection sums reproduce the weights
(`∑_i coeff_i ⟨g_c, dir_i⟩² = t_c`), any slope nonnegative on the certificate
directions has nonnegative weight-pairing `∑_c t_c y_c`. -/
theorem no_separating_slope_of_stressCertificate
    (D : WeightedDesign m k)
    {index : Type*} (family : Finset index)
    (dir : index → Fin k → ℝ) (coeff : index → ℝ)
    (hcoeff : ∀ i ∈ family, 0 ≤ coeff i)
    (hcert : ∀ c : Fin m,
      ∑ i ∈ family, coeff i * (D.atom c ⬝ᵥ dir i) ^ 2 = D.weight c)
    (slope : Fin m → ℝ)
    (hslope : ∀ i ∈ family, 0 ≤ ∑ c, slope c * (D.atom c ⬝ᵥ dir i) ^ 2) :
    0 ≤ ∑ c, D.weight c * slope c := by
  have hnonneg :
      0 ≤ ∑ i ∈ family, coeff i * (∑ c, slope c * (D.atom c ⬝ᵥ dir i) ^ 2) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hcoeff i hi) (hslope i hi)
  have heq :
      ∑ i ∈ family, coeff i * (∑ c, slope c * (D.atom c ⬝ᵥ dir i) ^ 2)
        = ∑ c, D.weight c * slope c := by
    have hinner : ∀ i, coeff i * (∑ c, slope c * (D.atom c ⬝ᵥ dir i) ^ 2)
        = ∑ c, slope c * (coeff i * (D.atom c ⬝ᵥ dir i) ^ 2) := by
      intro i
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun c _ => by ring)
    simp_rw [hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← Finset.mul_sum, hcert c, mul_comm]
  rw [heq] at hnonneg
  exact hnonneg

/-- **No separating slope exists, given a stress certificate** (the contrapositive):
no slope keeps the combined form nonnegative on the certificate directions while
strictly decreasing the weight-pairing `∑_c t_c y_c`. -/
theorem no_separatingSlope_exists_of_stressCertificate
    (D : WeightedDesign m k)
    {index : Type*} (family : Finset index)
    (dir : index → Fin k → ℝ) (coeff : index → ℝ)
    (hcoeff : ∀ i ∈ family, 0 ≤ coeff i)
    (hcert : ∀ c : Fin m,
      ∑ i ∈ family, coeff i * (D.atom c ⬝ᵥ dir i) ^ 2 = D.weight c) :
    ¬ ∃ slope : Fin m → ℝ,
        (∀ i ∈ family, 0 ≤ ∑ c, slope c * (D.atom c ⬝ᵥ dir i) ^ 2)
        ∧ (∑ c, D.weight c * slope c < 0) := by
  rintro ⟨slope, hslope, hneg⟩
  exact absurd
    (no_separating_slope_of_stressCertificate D family dir coeff hcoeff hcert slope hslope)
    (not_le.mpr hneg)

/-! ### A concrete certified tie: the regular tetrahedron

The `(4,3)` regular tetrahedron `g_c ∈ {(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)}` with
uniform weights `1/4` is a genuine weighted design (`∑ (1/4) g_c g_cᵀ = I`, a tight
frame) in which every 3-subset ties at `λ_min = 1`. Its stress multiplier is
`Λ = I/12 = (1/48) ∑_l g_l g_lᵀ`, with Frobenius pairing `⟨Λ, g_c g_cᵀ⟩ = 1/4 = t_c`. -/

/-- The four tetrahedron atoms. -/
def tetraAtom : Fin 4 → Fin 3 → ℝ :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

/-- The regular tetrahedron as a weighted `(4,3)` design (a tight frame). -/
noncomputable def tetraDesign : WeightedDesign 4 3 where
  atom := tetraAtom
  weight := fun _ => (1 : ℝ) / 4
  weight_pos := fun _ => by norm_num
  weight_sum_one := by rw [Fin.sum_univ_four]; norm_num
  isParseval := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_four, smul_eq_mul]
    fin_cases i <;> fin_cases j <;>
      simp [tetraAtom] <;> norm_num

/-- **The alternative is discharged at the tetrahedron tie, unconditionally.** With the
explicit stress certificate `coeff ≡ 1/48` over the four vertex directions, every slope
nonnegative on the four tight directions has nonnegative weight-pairing — no separating
slope exists. The multiplier `Λ = I/12` is exhibited. -/
theorem tetra_no_separating_slope (slope : Fin 4 → ℝ)
    (hslope : ∀ l : Fin 4,
      0 ≤ ∑ c, slope c * (tetraDesign.atom c ⬝ᵥ tetraDesign.atom l) ^ 2) :
    0 ≤ ∑ c, tetraDesign.weight c * slope c := by
  refine no_separating_slope_of_stressCertificate tetraDesign Finset.univ
    tetraDesign.atom (fun _ => (1 : ℝ) / 48) ?_ ?_ slope (fun i _ => hslope i)
  · intro i _; norm_num
  · intro c
    fin_cases c <;>
      simp [tetraDesign, tetraAtom, dotProduct, Fin.sum_univ_four, Fin.sum_univ_three] <;>
      norm_num

end Gtz
