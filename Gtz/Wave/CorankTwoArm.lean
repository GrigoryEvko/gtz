import Gtz.Wave.GhostBlockCore
import Gtz.Wave.CorankTwoPlanarClosure
import Gtz.Wave.CorankDecomposition
import Gtz.LinAlg.RankOneForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The corank-two arm: a two-dimensional gap kernel is impossible

A weak dominator of a `(6,3)` tie has a gap `S_C − 1` that is positive
semidefinite and singular, so its corank is one, two, or three.  Corank three
is dead outright (`Gtz.subsetSum_ne_one_of_isTie_sixThree`).  This module kills
corank TWO, modulo one scalar statement about a two-by-two block.

## The passage from a two-dimensional kernel to the rank-one normal form

A symmetric matrix with two independent kernel vectors has vanishing two-by-two
minors (`Gtz.minorVanishes_of_symm_twoKernel`), and a positive semidefinite
matrix with vanishing minors is a nonnegative multiple of an atom
(`Gtz.exists_rankOne_of_posSemidef_of_minorVanishes`).  Rescaling the axis to
unit length (`Gtz.exists_rankOneGap_of_twoKernel`) puts the gap in the corner's
normal form `lam • u uᵀ` with `u` a unit vector and `lam ≥ 0`, which is exactly
the hypothesis shape the two corner closures consume.  No eigenvalue and no
spectral theorem appear anywhere in the passage.

## The dispatch

With the gap in normal form the arm splits three ways, and two of the three are
already closed in the tree:

* `lam = 0` — the gap vanishes, so `S_C = 1`, which no tie permits;
* `lam > 0` and every outside atom orthogonal to `u` — the PLANAR corner,
  `Gtz.corankTwoPlanar_absurd`;
* `lam > 0` and some outside atom reading `u` — the NON-PLANAR corner, which
  `Gtz.corankTwoNonplanar_absurd_of_ghostBlock'` closes from a short ghost
  block.

So the whole arm rests on `Gtz.NonplanarGhostResidual`: at every non-planar
corner of the design, some inside atom leaves a ghost pair whose two-by-two
block of six-set pivots is short.  `Gtz.corankTwoGap_absurd` is the assembly and
`Gtz.gapKernel_subsingleton_of_isTie` is the arm statement it produces — every
weak dominator of a primitive tie has a gap kernel with no two independent
vectors, that is, corank exactly one.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The rank-one normal form of a corank-two gap -/

/-- **A two-dimensional kernel puts the gap in corner normal form.**  A positive
semidefinite `3 x 3` matrix with two kernel vectors of nonzero cross product is
`lam • u uᵀ` for a unit `u` and `lam ≥ 0`. -/
theorem exists_rankOneGap_of_twoKernel {gap : Matrix (Fin 3) (Fin 3) ℝ}
    (hpsd : gap.PosSemidef) (hsymm : gapᵀ = gap)
    {kernelOne kernelTwo : Fin 3 → ℝ}
    (hone : gap *ᵥ kernelOne = 0) (htwo : gap *ᵥ kernelTwo = 0)
    (hcross : crossProduct kernelOne kernelTwo ≠ 0) :
    ∃ (lam : ℝ) (u : Fin 3 → ℝ), 0 ≤ lam ∧ u ⬝ᵥ u = 1 ∧ gap = lam • atomMatrix u := by
  classical
  obtain ⟨axis, scale, hscale, hform⟩ :=
    exists_rankOne_of_posSemidef_of_minorVanishes hpsd
      (minorVanishes_of_symm_twoKernel hsymm hone htwo hcross)
  by_cases haxis : axis = 0
  · -- a zero axis makes the gap vanish; any unit vector carries `lam = 0`
    refine ⟨0, ![1, 0, 0], le_refl 0, ?_, ?_⟩
    · simp [dotProduct, Fin.sum_univ_three]
    · have hzero : atomMatrix (axis) = 0 := by
        rw [haxis]
        ext i j
        simp [atomMatrix, Matrix.vecMulVec_apply]
      rw [hform, hzero, smul_zero, zero_smul]
  · have hpos : 0 < axis ⬝ᵥ axis := dotProduct_self_pos haxis
    have hnorm : 0 < Real.sqrt (axis ⬝ᵥ axis) := Real.sqrt_pos.mpr hpos
    set n : ℝ := Real.sqrt (axis ⬝ᵥ axis) with hn
    have hsq : n * n = axis ⬝ᵥ axis := Real.mul_self_sqrt hpos.le
    have hnne : n ≠ 0 := ne_of_gt hnorm
    refine ⟨scale * (axis ⬝ᵥ axis), n⁻¹ • axis, mul_nonneg hscale hpos.le, ?_, ?_⟩
    · rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← hsq]
      field_simp
    · rw [hform, atomMatrix_smul, smul_smul, inv_pow]
      congr 1
      rw [← hsq]
      field_simp

/-! ## 2. The residual, named -/

/-- **The residual of the corank-two arm.**  At every non-planar corner of the
design, some inside atom leaves a ghost pair with a short block of six-set
pivots.  `Gtz.GhostBlockShort` is the four scalar conditions, and
`Gtz.corankTwoNonplanar_absurd_of_ghostBlock'` closes the corner from it. -/
def NonplanarGhostResidual (D : WeightedDesign 6 3) : Prop :=
  ∀ C : Finset (Fin 6), C.card = 3 → ∀ lam : ℝ, 0 < lam → ∀ u : Fin 3 → ℝ,
    u ⬝ᵥ u = 1 → subsetSum D C - 1 = lam • atomMatrix u →
    (∃ d ∈ Cᶜ, D.atom d ⬝ᵥ u ≠ 0) →
    ∃ e ∈ C, ∃ f h : Fin 6, f ≠ h ∧ C.erase e = {f, h} ∧ GhostBlockShort D f h

/-! ## 3. The arm -/

/-- **A corank-two gap is impossible.**  A primitive `(6,3)` tie has no weak
dominator whose gap kernel contains two vectors with nonzero cross product. -/
theorem corankTwoGap_absurd (D : WeightedDesign 6 3) (htie : IsTie D)
    (hprimitive : IsPrimitiveDesign D) (hres : NonplanarGhostResidual D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) (hdom : Dominates D C)
    {kernelOne kernelTwo : Fin 3 → ℝ}
    (hone : (subsetSum D C - 1) *ᵥ kernelOne = 0)
    (htwo : (subsetSum D C - 1) *ᵥ kernelTwo = 0)
    (hcross : crossProduct kernelOne kernelTwo ≠ 0) : False := by
  classical
  obtain ⟨lam, u, hlam, hunit, hgap⟩ :=
    exists_rankOneGap_of_twoKernel hdom
      (transpose_subsetSum_sub_one D C) hone htwo hcross
  rcases eq_or_lt_of_le hlam with hzero | hpos
  · -- the gap vanishes, so the dominator's atom sum is the identity
    refine subsetSum_ne_one_of_isTie_sixThree D htie C hcard ?_
    have hgapzero : subsetSum D C - 1 = 0 := by
      rw [hgap, ← hzero, zero_smul]
    exact sub_eq_zero.mp hgapzero
  · by_cases hplanar : ∀ d ∈ Cᶜ, D.atom d ⬝ᵥ u = 0
    · exact corankTwoPlanar_absurd D htie hprimitive C hcard hlam hunit hgap hplanar
    · push_neg at hplanar
      obtain ⟨d0, hd0, hread⟩ := hplanar
      obtain ⟨e, he, f, h, hfh, herase, hshort⟩ :=
        hres C hcard lam hpos u hunit hgap ⟨d0, hd0, hread⟩
      exact corankTwoNonplanar_absurd_of_ghostBlock' D htie C hcard he hfh herase hshort

/-- **The arm statement.**  Every weak dominator of a primitive `(6,3)` tie has a
gap of corank exactly one: no two kernel vectors are independent. -/
theorem gapKernel_subsingleton_of_isTie (D : WeightedDesign 6 3) (htie : IsTie D)
    (hprimitive : IsPrimitiveDesign D) (hres : NonplanarGhostResidual D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) (hdom : Dominates D C)
    (kernelOne kernelTwo : Fin 3 → ℝ)
    (hone : (subsetSum D C - 1) *ᵥ kernelOne = 0)
    (htwo : (subsetSum D C - 1) *ᵥ kernelTwo = 0) :
    crossProduct kernelOne kernelTwo = 0 := by
  by_contra hcross
  exact corankTwoGap_absurd D htie hprimitive hres C hcard hdom hone htwo hcross

end Gtz
