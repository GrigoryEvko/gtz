/-
# The first probe of the adapted frame

`Gtz.k2Five_kill` quantifies over an orthonormal pair `vh, nh` of the axis
complement with `vh` carrying the outside line, and `Gtz.k2Probe_cross_spec`
supplies the second probe as the cross product of the axis with the first.  This
module supplies the first, and with it the two-zero stratum of a `(5,3)` design
is empty with no probe hypothesis at all.

## The normalisation

The first probe is the unit vector along the outside atom's plane part.  Write
`q = a - (a·x)·x` for that part, where `x` is the unit axis.  Then `q` is
orthogonal to `x`, and `q` vanishes exactly when `a` lies on the axis — which
the stratum excludes, since an outside atom parallel to the axis is a parallel
pair.  Dividing by the square root of `q·q` gives the probe
(`Gtz.k2Probe_planePart_spec`), and the decomposition

  `a = (a·x)·x + Real.sqrt (q·q) • vh`

comes out of the same computation, which is exactly the span hypothesis the
cross-product probe wants.

## What the reading buys

The kill also asks that the outside atom read the first probe nontrivially.
That is free here: the reading IS the square root, `a·vh = Real.sqrt (q·q)`, so
it is positive precisely when the plane part does not vanish
(`Gtz.k2Probe_reading_pos`).  No separate hypothesis is needed.

Assembling, `Gtz.k2FiveTwoZero_kill` closes the stratum from design-level data
alone: a unit axis atom orthogonal to the two plane atoms, two outside atoms not
parallel to the axis, the plane gap positive definite through its two Sylvester
data, and the four refusals.
-/
import Gtz.Wave.KTwoProbePair

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. The plane part -/

/-- The plane part of a vector against a unit axis: what is left after removing
the axis component. -/
noncomputable def planePart (x a : Fin 3 → ℝ) : Fin 3 → ℝ :=
  a - (a ⬝ᵥ x) • x

/-- The plane part is orthogonal to the axis. -/
theorem dotProduct_planePart (x a : Fin 3 → ℝ) (hxx : x ⬝ᵥ x = 1) :
    x ⬝ᵥ planePart x a = 0 := by
  simp only [planePart, dotProduct_sub, dotProduct_smul, smul_eq_mul, hxx,
    mul_one, dotProduct_comm x a, sub_self]

/-- The plane part's own square length, in terms of the vector and its axis
reading. -/
theorem planePart_dotProduct_self (x a : Fin 3 → ℝ) (hxx : x ⬝ᵥ x = 1) :
    planePart x a ⬝ᵥ planePart x a = a ⬝ᵥ a - (a ⬝ᵥ x)^2 := by
  simp only [planePart, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hxx, mul_one, dotProduct_comm x a]
  ring

/-- A vanishing plane part means the vector lies on the axis. -/
theorem eq_smul_of_planePart_eq_zero {x a : Fin 3 → ℝ}
    (hzero : planePart x a = 0) : a = (a ⬝ᵥ x) • x :=
  sub_eq_zero.mp hzero

/-! ## 2. The first probe -/

/-- **THE FIRST PROBE.**  Normalising the plane part of the outside atom gives a
unit vector orthogonal to the axis, and the atom decomposes along the axis and
the probe with the square root as its probe reading. -/
theorem k2Probe_planePart_spec {x a : Fin 3 → ℝ} (hxx : x ⬝ᵥ x = 1)
    (hne : planePart x a ≠ 0) :
    let s := Real.sqrt (planePart x a ⬝ᵥ planePart x a)
    let vh := s⁻¹ • planePart x a
    vh ⬝ᵥ vh = 1 ∧ x ⬝ᵥ vh = 0 ∧ a = (a ⬝ᵥ x) • x + s • vh ∧ a ⬝ᵥ vh = s := by
  intro s vh
  have hqq : 0 < planePart x a ⬝ᵥ planePart x a :=
    dotProduct_self_pos hne
  have hs : 0 < s := Real.sqrt_pos.mpr hqq
  have hs2 : s * s = planePart x a ⬝ᵥ planePart x a := by
    have := Real.sq_sqrt hqq.le
    simpa only [sq] using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the probe is a unit vector
    show (s⁻¹ • planePart x a) ⬝ᵥ (s⁻¹ • planePart x a) = 1
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hs2]
    field_simp
  · -- the probe is orthogonal to the axis
    show x ⬝ᵥ (s⁻¹ • planePart x a) = 0
    rw [dotProduct_smul, smul_eq_mul, dotProduct_planePart x a hxx, mul_zero]
  · -- the decomposition
    show a = (a ⬝ᵥ x) • x + s • (s⁻¹ • planePart x a)
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul, planePart]
    abel
  · -- the reading is the square root
    show a ⬝ᵥ (s⁻¹ • planePart x a) = s
    rw [dotProduct_smul, smul_eq_mul]
    have hax : a ⬝ᵥ planePart x a = planePart x a ⬝ᵥ planePart x a := by
      simp only [planePart, dotProduct_sub, sub_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul, hxx, mul_one, dotProduct_comm x a]
      ring
    rw [hax, ← hs2]
    field_simp

/-! ## 3. The stratum, with no probe hypothesis -/

/-- **THE TWO-ZERO STRATUM OF A `(5,3)` DESIGN IS EMPTY, FROM DESIGN DATA
ALONE.**  The probes of `Gtz.k2Five_kill` are produced rather than assumed: the
first is the normalised plane part of the outside atom, the second its cross
product with the axis.  The only new hypothesis is that the outside atom's plane
part does not vanish — that is, the atom is not parallel to the axis, which the
stratum excludes as a parallel pair.

The reading hypothesis of the kill is discharged for free: the outside atom
reads its own probe at the square root of the plane part's length, which is
positive exactly when that part is nonzero. -/
theorem k2FiveTwoZero_kill (D : WeightedDesign 5 3)
    (hunit : leverageOf (D.atom 0) = 1)
    (hy : atomPairing D 0 1 = 0) (hz : atomPairing D 0 2 = 0)
    (hne : planePart (D.atom 0) (D.atom 3) ≠ 0)
    (hal : atomPairing D 3 0 ≠ 0) (hax : atomPairing D 4 0 ≠ 0)
    (hB11 : 0 < (D.atom 1 ⬝ᵥ (Real.sqrt (planePart (D.atom 0) (D.atom 3)
              ⬝ᵥ planePart (D.atom 0) (D.atom 3)))⁻¹
            • planePart (D.atom 0) (D.atom 3))^2
        + (D.atom 2 ⬝ᵥ (Real.sqrt (planePart (D.atom 0) (D.atom 3)
              ⬝ᵥ planePart (D.atom 0) (D.atom 3)))⁻¹
            • planePart (D.atom 0) (D.atom 3))^2 - 1)
    (hdet : 0 < ((D.atom 1 ⬝ᵥ (Real.sqrt (planePart (D.atom 0) (D.atom 3)
                ⬝ᵥ planePart (D.atom 0) (D.atom 3)))⁻¹
              • planePart (D.atom 0) (D.atom 3))^2
          + (D.atom 2 ⬝ᵥ (Real.sqrt (planePart (D.atom 0) (D.atom 3)
                ⬝ᵥ planePart (D.atom 0) (D.atom 3)))⁻¹
              • planePart (D.atom 0) (D.atom 3))^2 - 1)
        * ((D.atom 1 ⬝ᵥ bracketNormal (D.atom 0)
              ((Real.sqrt (planePart (D.atom 0) (D.atom 3)
                ⬝ᵥ planePart (D.atom 0) (D.atom 3)))⁻¹
              • planePart (D.atom 0) (D.atom 3)))^2
          + (D.atom 2 ⬝ᵥ bracketNormal (D.atom 0)
              ((Real.sqrt (planePart (D.atom 0) (D.atom 3)
                ⬝ᵥ planePart (D.atom 0) (D.atom 3)))⁻¹
              • planePart (D.atom 0) (D.atom 3)))^2 - 1)
        - ((D.atom 1 ⬝ᵥ (Real.sqrt (planePart (D.atom 0) (D.atom 3)
                ⬝ᵥ planePart (D.atom 0) (D.atom 3)))⁻¹
              • planePart (D.atom 0) (D.atom 3))
            * (D.atom 1 ⬝ᵥ bracketNormal (D.atom 0)
              ((Real.sqrt (planePart (D.atom 0) (D.atom 3)
                ⬝ᵥ planePart (D.atom 0) (D.atom 3)))⁻¹
              • planePart (D.atom 0) (D.atom 3)))
          + (D.atom 2 ⬝ᵥ (Real.sqrt (planePart (D.atom 0) (D.atom 3)
                ⬝ᵥ planePart (D.atom 0) (D.atom 3)))⁻¹
              • planePart (D.atom 0) (D.atom 3))
            * (D.atom 2 ⬝ᵥ bracketNormal (D.atom 0)
              ((Real.sqrt (planePart (D.atom 0) (D.atom 3)
                ⬝ᵥ planePart (D.atom 0) (D.atom 3)))⁻¹
              • planePart (D.atom 0) (D.atom 3))))^2)
    (hRyzd : tripleGapDet (D.atom 1) (D.atom 2) (D.atom 3) ≤ 0)
    (hRyze : tripleGapDet (D.atom 1) (D.atom 2) (D.atom 4) ≤ 0)
    (hRyde : tripleGapDet (D.atom 1) (D.atom 3) (D.atom 4) ≤ 0)
    (hRzde : tripleGapDet (D.atom 2) (D.atom 3) (D.atom 4) ≤ 0) :
    False := by
  have hxx : D.atom 0 ⬝ᵥ D.atom 0 = 1 := by
    simpa only [leverageOf, dotProduct, Fin.sum_univ_three, sq] using hunit
  obtain ⟨hvv, hxv, hdecomp, hread⟩ :=
    k2Probe_planePart_spec (x := D.atom 0) (a := D.atom 3) hxx hne
  set s := Real.sqrt (planePart (D.atom 0) (D.atom 3)
    ⬝ᵥ planePart (D.atom 0) (D.atom 3)) with hs_def
  set vh := s⁻¹ • planePart (D.atom 0) (D.atom 3) with hvh_def
  obtain ⟨hnn, hxn, hvn, hdn⟩ :=
    k2Probe_cross_spec (x := D.atom 0) (vh := vh) (a := D.atom 3)
      (c₁ := D.atom 3 ⬝ᵥ D.atom 0) (c₂ := s) hxx hvv hxv hdecomp
  have hqq : 0 < planePart (D.atom 0) (D.atom 3)
      ⬝ᵥ planePart (D.atom 0) (D.atom 3) := dotProduct_self_pos hne
  have hs : 0 < s := Real.sqrt_pos.mpr hqq
  refine k2Five_kill D hunit hy hz vh (bracketNormal (D.atom 0) vh)
    hvv hnn ?_ ?_ ?_ hdn hal hax ?_ hB11 hdet hRyzd hRyze hRyde hRzde
  · exact hvn
  · exact hxv
  · exact hxn
  · rw [hread]; exact hs.ne'

end Gtz
