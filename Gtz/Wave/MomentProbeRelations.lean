import Gtz.Wave.AnchorTransportPairs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The probe relations of the inverse moment identity

The inverse moment identity `Σ_{a∈F} A⁻¹G_a − Σ_c t_c·A⁻¹G_c = 1` is a matrix
equation (`Gtz.fourSet_inverse_moment_identity`).  Read against a pair of
probes it becomes the relation that ties the `A⁻¹`-Gram of the atoms to their
RAW Gram (`Gtz.fourSet_inverse_moment_probe`):

  `Σ_{a∈F} (vᵀA⁻¹g_a)(g_a·w) − Σ_c t_c·(vᵀA⁻¹g_c)(g_c·w) = v·w` .

Every ambient equality that a certificate over the transported arena needs is
a specialization of this one: the reading total is the trace form, the
weighted Parseval rail is the `A⁻¹`-weighted form, and the corner relations
come from probing with the corner atoms.

## The erased corner relation

At a `Z1` corner the erased atom is a unit vector orthogonal to both
axis-carrying inside atoms, so probing the identity with `g_x` on both sides
kills every inside term except the erased one and leaves the OUTSIDE
coweights against the erased components (`Gtz.corner_oneAxisZero_erased_probe`):

  `Σ_{d ∈ Cᶜ} (1 − t_d)·c_{xd}·ξ_d = 1 + t_x·r_x` ,

with `c_{xd} = g_xᵀA_y⁻¹g_d` the erased cross readings, `ξ_d = g_d·g_x` the
erased components, and `r_x = g_xᵀA_y⁻¹g_x`.  This is the corner's own
coweight law in the transported coordinates: it couples the `A_y⁻¹` cross
readings to the raw erased components that the deflation instruments already
control, and it degenerates correctly as the outside weights approach one.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The probe form of the moment identity -/

/-- Reading a left-multiplied atom at two probes factors into two readings. -/
theorem inv_mul_atomMatrix_probe {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (g v w : Fin k → ℝ) :
    v ⬝ᵥ ((A⁻¹ * atomMatrix g) *ᵥ w) = (v ⬝ᵥ (A⁻¹ *ᵥ g)) * (g ⬝ᵥ w) := by
  rw [← Matrix.mulVec_mulVec,
    show atomMatrix g = Matrix.vecMulVec g g from rfl, vecMulVec_mulVec_eq,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

/-- **THE PROBE RELATION.**  The inverse moment identity, read at two probes:

  `Σ_{a∈F} (vᵀA⁻¹g_a)(g_a·w) − Σ_c t_c·(vᵀA⁻¹g_c)(g_c·w) = v·w` .

Every ambient equality of the transported arena is a specialization of this
one relation. -/
theorem fourSet_inverse_moment_probe (D : WeightedDesign m 3)
    (F : Finset (Fin m)) (hdet : IsUnit (subsetSum D F - 1).det)
    (v w : Fin 3 → ℝ) :
    (∑ a ∈ F, (v ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom a)) * (D.atom a ⬝ᵥ w))
        - ∑ c, D.weight c
            * ((v ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom c)) * (D.atom c ⬝ᵥ w))
      = v ⬝ᵥ w := by
  classical
  set A : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hA
  have hid := fourSet_inverse_moment_identity D F hdet
  have hread := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => v ⬝ᵥ (M *ᵥ w)) hid
  simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec,
    dotProduct_sum, Matrix.one_mulVec] at hread
  rw [← hread, ← hA]
  congr 1
  · exact Finset.sum_congr rfl fun a _ =>
      (inv_mul_atomMatrix_probe A (D.atom a) v w).symm
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      inv_mul_atomMatrix_probe A (D.atom c) v w]

/-! ## 2. The erased corner relation -/

/-- **THE ERASED PROBE RELATION.**  At a `Z1` corner, probing the moment
identity of the surviving four-set with the erased atom on both sides leaves
only the outside coweights against the erased components:

  `Σ_{d ∈ Cᶜ} (1 − t_d)·(g_xᵀA_y⁻¹g_d)·(g_d·g_x) = 1 + t_x·r_x` .

The inside atoms drop out because the erased atom is orthogonal to both of
them, and its own leverage is one.  The relation couples the transported
cross readings to the raw erased components that the landed deflation
instruments control. -/
theorem corner_oneAxisZero_erased_probe (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        (1 - D.weight d)
          * ((D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom d)) * (D.atom d ⬝ᵥ D.atom x))
      = 1 + D.weight x
          * (D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom x)) := by
  classical
  set K : Finset (Fin 6) := (({x, y, z} : Finset (Fin 6))ᶜ) with hK
  set A : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D (insert y K) - 1 with hA
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hAy.det_pos)
  have hyK : y ∉ K := by rw [hK]; simp
  -- the corner orthogonality and the unit leverage of the erased atom
  have horth := corner_oneAxisZero_xOrthogonal D hxy hxz hyz hlam hunit hgap hax
  have hyx : D.atom y ⬝ᵥ D.atom x = 0 := by
    rw [dotProduct_comm]; exact horth.1
  have hzx : D.atom z ⬝ᵥ D.atom x = 0 := by
    rw [dotProduct_comm]; exact horth.2
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin 6))) hax
  -- the probe relation at v = w = g_x
  have hprobe := fourSet_inverse_moment_probe D (insert y K) hdet
    (D.atom x) (D.atom x)
  rw [← hA] at hprobe
  -- the member sum loses its y term
  have hmem : ∑ a ∈ insert y K,
      (D.atom x ⬝ᵥ (A⁻¹ *ᵥ D.atom a)) * (D.atom a ⬝ᵥ D.atom x)
      = ∑ d ∈ K, (D.atom x ⬝ᵥ (A⁻¹ *ᵥ D.atom d)) * (D.atom d ⬝ᵥ D.atom x) := by
    rw [Finset.sum_insert hyK, hyx, mul_zero, zero_add]
  -- the weighted sum keeps the erased term and the outside terms only
  have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin 6))
    (fun c => D.weight c
      * ((D.atom x ⬝ᵥ (A⁻¹ *ᵥ D.atom c)) * (D.atom c ⬝ᵥ D.atom x)))
  rw [sum_triple_eq hxy hxz hyz, hyx, hzx] at hsplit
  simp only [mul_zero, zero_mul, add_zero] at hsplit
  rw [dotProduct_self_eq_sum_sq] at hlev
  have hxx : D.atom x ⬝ᵥ D.atom x = 1 := by
    rw [dotProduct_self_eq_sum_sq]; exact hlev
  rw [hxx, mul_one] at hsplit
  rw [hmem] at hprobe
  rw [hxx] at hprobe
  rw [← hsplit] at hprobe
  -- assemble: the coweights are the member sum minus the weighted sum
  have hcow : ∑ d ∈ K, (1 - D.weight d)
      * ((D.atom x ⬝ᵥ (A⁻¹ *ᵥ D.atom d)) * (D.atom d ⬝ᵥ D.atom x))
      = (∑ d ∈ K, (D.atom x ⬝ᵥ (A⁻¹ *ᵥ D.atom d)) * (D.atom d ⬝ᵥ D.atom x))
        - ∑ d ∈ K, D.weight d
            * ((D.atom x ⬝ᵥ (A⁻¹ *ᵥ D.atom d)) * (D.atom d ⬝ᵥ D.atom x)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hcow]
  linarith [hprobe]

end Gtz
