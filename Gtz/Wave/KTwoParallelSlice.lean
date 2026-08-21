/-
# The parallel slice of the two-zero stratum

`Gtz.k2FiveTwoZero_kill` carries one design-level hypothesis: the outside atom
is not parallel to the axis, so its plane part does not vanish.  This module
settles the slice where that fails, and the answer is a dichotomy with no new
mathematics — both branches are already dead.

## The dichotomy

The collinearity `Gtz.k2FiveAxis_collinear` says that against every probe
orthogonal to the axis,

  `t_d·α·(g_d·u) + t_e·β·(g_e·u) = 0` .

If the first outside atom is parallel to the axis its plane part vanishes, so
its own term drops for every such probe, and what is left is
`t_e·β·(g_e·u) = 0` for all `u` orthogonal to the axis.  Weights are positive,
so at each probe either the axis reading `β` vanishes or the plane reading does.
Since the plane readings of a fixed atom cannot all vanish unless its plane part
does, the slice splits into exactly two cases
(`Gtz.k2FiveAxis_parallel_dichotomy`):

* the second outside atom also has vanishing axis reading, or
* the second outside atom is parallel to the axis as well.

The second branch is the all-parallel outside, which
`Gtz.k2_not_isTie_of_outside_parallel_all` already forbids at a tie.  The first
branch contradicts the stratum's own nonvanishing hypothesis on the axis
pairings, which the kill carries as `hax`.

## Why this completes the slice

Nothing here is a limit argument.  The channel the campaign recorded as `ch2`
— the outside weight tending to one and its atom tending to the null direction
— reaches this exact slice, and at the slice the dichotomy applies verbatim.  So
the boundary needs no separate estimate: it is covered by two landed theorems
and one reading of the collinearity.
-/
import Gtz.Wave.KTwoProbeNormalise

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. A vanishing plane part kills every orthogonal reading -/

/-- An atom parallel to the axis reads every probe orthogonal to the axis at
zero. -/
theorem dotProduct_eq_zero_of_planePart_eq_zero {x a u : Fin 3 → ℝ}
    (hzero : planePart x a = 0) (hu : x ⬝ᵥ u = 0) : a ⬝ᵥ u = 0 := by
  rw [eq_smul_of_planePart_eq_zero hzero, smul_dotProduct, smul_eq_mul, hu,
    mul_zero]

/-- Conversely, an atom reading every probe orthogonal to the axis at zero has
vanishing plane part: read the plane part against itself. -/
theorem planePart_eq_zero_of_forall_dotProduct_eq_zero {x a : Fin 3 → ℝ}
    (hxx : x ⬝ᵥ x = 1)
    (hall : ∀ u : Fin 3 → ℝ, x ⬝ᵥ u = 0 → a ⬝ᵥ u = 0) :
    planePart x a = 0 := by
  have hself := hall (planePart x a) (dotProduct_planePart x a hxx)
  have hqq : planePart x a ⬝ᵥ planePart x a = 0 := by
    have hax : a ⬝ᵥ planePart x a = planePart x a ⬝ᵥ planePart x a := by
      simp only [planePart, dotProduct_sub, sub_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul, hxx, mul_one, dotProduct_comm x a]
      ring
    rw [← hax]; exact hself
  exact dotProduct_self_eq_zero.mp hqq

/-! ## 2. The dichotomy at the slice -/

/-- **THE PARALLEL SLICE IS A DICHOTOMY.**  If the first outside atom is
parallel to the axis, then either the second outside atom has vanishing axis
pairing, or it is parallel to the axis as well.

The collinearity loses its first term at every probe orthogonal to the axis, so
the second term vanishes there; positive weights then force the axis pairing or
the plane reading to vanish at each probe, and a fixed atom whose plane readings
all vanish has no plane part. -/
theorem k2FiveAxis_parallel_dichotomy (D : WeightedDesign 5 3)
    (hunit : leverageOf (D.atom 0) = 1)
    (hy : atomPairing D 0 1 = 0) (hz : atomPairing D 0 2 = 0)
    (hpar : planePart (D.atom 0) (D.atom 3) = 0) :
    atomPairing D 4 0 = 0 ∨ planePart (D.atom 0) (D.atom 4) = 0 := by
  by_cases hbeta : atomPairing D 4 0 = 0
  · exact Or.inl hbeta
  · refine Or.inr (planePart_eq_zero_of_forall_dotProduct_eq_zero ?_ ?_)
    · simpa only [leverageOf, dotProduct, Fin.sum_univ_three, sq] using hunit
    · intro u hu
      have hu0 : D.atom 0 ⬝ᵥ u = 0 := hu
      have hcol := k2FiveAxis_collinear D hunit hy hz u hu0
      have h3u : D.atom 3 ⬝ᵥ u = 0 :=
        dotProduct_eq_zero_of_planePart_eq_zero hpar hu0
      rw [h3u, mul_zero, mul_zero, zero_add] at hcol
      have hw4 := D.weight_pos 4
      rcases mul_eq_zero.mp hcol with h | h
      · exact absurd h hw4.ne'
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hbeta
        · exact h'

/-! ## 3. The slice, with the axis pairings nonzero -/

/-- **AT THE SLICE, BOTH OUTSIDE ATOMS ARE PARALLEL.**  With both axis pairings
nonzero — the standing hypothesis of the kill — the first branch of the
dichotomy is excluded, so a parallel first outside atom forces the second one
parallel too.  That is the all-parallel outside. -/
theorem k2FiveAxis_parallel_both (D : WeightedDesign 5 3)
    (hunit : leverageOf (D.atom 0) = 1)
    (hy : atomPairing D 0 1 = 0) (hz : atomPairing D 0 2 = 0)
    (hax : atomPairing D 4 0 ≠ 0)
    (hpar : planePart (D.atom 0) (D.atom 3) = 0) :
    planePart (D.atom 0) (D.atom 4) = 0 := by
  rcases k2FiveAxis_parallel_dichotomy D hunit hy hz hpar with h | h
  · exact absurd h hax
  · exact h

end Gtz
