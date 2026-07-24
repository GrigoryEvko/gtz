/-
# Domination does not imply a stress certificate

A rational `(6,3)` weighted design whose subset `{0,1,2}` dominates (`S_C − I` is PSD),
yet which admits NO stress certificate / frame multiplier. The witness is a slope `α`
that is nonnegative on every direction — its squared-projection form is
`∑_c α_c ⟨g_c, d⟩² = (d 0)²`, i.e. `∑_c α_c g_c g_cᵀ = e₀e₀ᵀ` (rank-one PSD) — while its
weight pairing is strictly negative, `∑_c t_c α_c = −1171/34848 < 0`. By the contrapositive
of `Gtz.no_separating_slope_of_stressCertificate`, no certificate can exist.

So stress-certificate existence is STRICTLY STRONGER than domination: a design can carry a
dominating subset yet have no PSD `Λ` with `⟨Λ, g_c g_cᵀ⟩ = t_c` for every atom. The
converse of the weak-duality lemma fails.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.StressCertificate
import Gtz.Reduction.RayleighCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz
open Matrix

/-- The six atoms of the witness design (each of leverage 3, so Parseval forces the
weights to sum to 1). -/
noncomputable def witnessAtom : Fin 6 → Fin 3 → ℝ :=
  ![![1, 1, 1], ![1, 1, -1], ![1, -1, 1],
    ![1, -7/5, -1/5], ![-1/5, 1, -7/5], ![-7/5, 1/5, 1]]

/-- The exact rational `(6,3)` weighted design witnessing that domination does not imply a
stress certificate. -/
noncomputable def witnessDesign : WeightedDesign 6 3 where
  atom := witnessAtom
  weight := ![10/33, 1/11, 5/132, 25/132, 25/132, 25/132]
  weight_pos := by intro c; fin_cases c <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val,
      Matrix.tail_cons]
    norm_num
  isParseval := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_six, smul_eq_mul, witnessAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

/-- **The subset `{0,1,2}` dominates** — `S_C − I` is PSD via the sum of squares
`⟨g₀,x⟩² + ⟨g₁,x⟩² + ⟨g₂,x⟩² − |x|² = (x₀+x₁)² + (x₀+x₂)² + (x₁−x₂)²`. So the design carries
a dominating subset: the certificate failure below is not an artifact of non-domination. -/
theorem witnessDesign_dominates : Dominates witnessDesign {0, 1, 2} := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
  · have htr : (subsetSum witnessDesign {0, 1, 2}
        - (1 : Matrix (Fin 3) (Fin 3) ℝ))ᵀ = subsetSum witnessDesign {0, 1, 2} - 1 := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum, Matrix.transpose_sum]
      refine congrArg (· - 1) (Finset.sum_congr rfl fun c _ => ?_)
      ext a b
      simp [atomMatrix, Matrix.transpose_apply, Matrix.vecMulVec_apply, mul_comm]
    exact isHermitian_of_transpose_eq htr
  · rw [star_trivial, dominationGap_form,
      show ({0, 1, 2} : Finset (Fin 6)) = insert 0 (insert 1 {2}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [witnessDesign, witnessAtom, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 + x 2), sq_nonneg (x 1 - x 2)]

/-- The separating slope `α` (mixed signs). Its squared-projection form is
`∑_c α_c ⟨g_c, d⟩² = (d 0)²` for every direction — i.e. `∑_c α_c g_c g_cᵀ = e₀e₀ᵀ`, a
rank-one PSD matrix, so the slope is nonnegative on every direction. -/
noncomputable def witnessSlope : Fin 6 → ℝ :=
  ![7/132, 19/88, 71/132, -125/792, -50/99, 25/132]

/-- **The slope's form is the first-coordinate square:** `∑_c α_c ⟨g_c, d⟩² = (d 0)²`
for every `d`. The rank-one right-hand side is manifestly a square, so `α` is nonnegative
on every direction — the PSD side of the theorem of alternatives. -/
theorem witnessSlope_form (d : Fin 3 → ℝ) :
    ∑ c, witnessSlope c * (witnessDesign.atom c ⬝ᵥ d) ^ 2 = (d 0) ^ 2 := by
  simp only [witnessDesign, witnessSlope, witnessAtom, Fin.sum_univ_six, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val,
    Matrix.tail_cons]
  ring

/-- **The weight pairing is strictly negative:** `∑_c t_c α_c = −1171/34848 < 0`. -/
theorem witnessSlope_weightPairing :
    ∑ c, witnessDesign.weight c * witnessSlope c = -1171/34848 := by
  simp only [witnessDesign, witnessSlope, Fin.sum_univ_six, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
  norm_num

/-- **No stress certificate exists for this dominating design.** Any nonnegative `coeff`
over any direction family with `∑_i coeff_i ⟨g_c, dir_i⟩² = t_c` for every atom would, via
`no_separating_slope_of_stressCertificate` applied to the slope `α`, force
`0 ≤ ∑_c t_c α_c`; but that pairing is `−1171/34848 < 0`. So there is no PSD `Λ` with
`⟨Λ, g_c g_cᵀ⟩ = t_c` for every atom — certificate existence is strictly stronger than
domination. -/
theorem witnessDesign_noStressCertificate {index : Type*} (family : Finset index)
    (dir : index → Fin 3 → ℝ) (coeff : index → ℝ)
    (hcoeff : ∀ i ∈ family, 0 ≤ coeff i)
    (hcert : ∀ c : Fin 6,
      ∑ i ∈ family, coeff i * (witnessDesign.atom c ⬝ᵥ dir i) ^ 2 = witnessDesign.weight c) :
    False := by
  have hslope : ∀ i ∈ family,
      0 ≤ ∑ c, witnessSlope c * (witnessDesign.atom c ⬝ᵥ dir i) ^ 2 := by
    intro i _
    rw [witnessSlope_form]
    exact sq_nonneg _
  have hnn := no_separating_slope_of_stressCertificate witnessDesign family dir coeff
    hcoeff hcert witnessSlope hslope
  rw [witnessSlope_weightPairing] at hnn
  norm_num at hnn

end Gtz
