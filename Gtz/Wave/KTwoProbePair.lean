/-
# The second probe of the adapted frame

`Gtz.k2Five_kill` quantifies over a pair of probes `vh, nh`.  Only the first is
a choice: `vh` must be the unit vector along the outside plane part.  The second
is then forced, and this module supplies it.

Take `nh` to be the cross product of the axis with the first probe.  Being a
bracket with a repeated slot, it annihilates both of them; being a cross product
of two orthogonal unit vectors it is itself a unit vector, by Lagrange; and it
annihilates anything in their span, so it annihilates the outside atom.  Those
are exactly the four properties the kill asks of `nh`
(`Gtz.k2Probe_cross_spec`).

What this leaves is the first probe alone.  `vh` is the normalisation of
`a − (a·x)·x`, so producing it is a square root and a nonvanishing hypothesis —
the outside atom must not be parallel to the axis, which the stratum already
excludes through the parallel laws.
-/
import Gtz.Wave.KTwoDesignKill

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-- The cross product is linear in the probe it is read against. -/
theorem dotProduct_bracketNormal_combo (x y : Fin 3 → ℝ) (c₁ c₂ : ℝ) :
    (c₁ • x + c₂ • y) ⬝ᵥ bracketNormal x y = 0 := by
  simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_three, bracketNormal, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- **THE SECOND PROBE IS THE CROSS PRODUCT OF THE FIRST WITH THE AXIS.**  It is
a unit vector orthogonal to both, and it annihilates every vector in their span
— in particular the outside atom, which is the property the kill needs. -/
theorem k2Probe_cross_spec {x vh a : Fin 3 → ℝ} {c₁ c₂ : ℝ}
    (hxx : x ⬝ᵥ x = 1) (hvv : vh ⬝ᵥ vh = 1) (hxv : x ⬝ᵥ vh = 0)
    (ha : a = c₁ • x + c₂ • vh) :
    bracketNormal x vh ⬝ᵥ bracketNormal x vh = 1
      ∧ x ⬝ᵥ bracketNormal x vh = 0
      ∧ vh ⬝ᵥ bracketNormal x vh = 0
      ∧ a ⬝ᵥ bracketNormal x vh = 0 := by
  refine ⟨?_, dotProduct_bracketNormal_left x vh,
    dotProduct_bracketNormal_right x vh, ?_⟩
  · have hL : crossNormSq x vh = leverageOf x * leverageOf vh - (x ⬝ᵥ vh)^2 :=
      crossNormSq_eq_leverage_mul_sub_sq x vh
    have hlx : leverageOf x = 1 := by
      simpa only [leverageOf, dotProduct, Fin.sum_univ_three, sq] using hxx
    have hlv : leverageOf vh = 1 := by
      simpa only [leverageOf, dotProduct, Fin.sum_univ_three, sq] using hvv
    rw [hlx, hlv, hxv] at hL
    have : (1:ℝ) * 1 - (0:ℝ)^2 = 1 := by norm_num
    rw [this] at hL
    simpa only [crossNormSq] using hL
  · rw [ha]; exact dotProduct_bracketNormal_combo x vh c₁ c₂

end Gtz
