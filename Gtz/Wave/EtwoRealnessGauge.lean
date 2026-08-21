/-
# The corner design carries a residual gauge, and the outside does not see it

The corank-two arm has spent three rounds asking what determines the repayment
fact `E2`.  A gauge theorem of the coherent-horn lane showed that the inside
frame of a CORNER can be rotated without moving any corner-pair invariant, so
no certificate written in those invariants can decide repayment.  The natural
objection was that the rotation leaves the corner but not the DESIGN: Parseval
pins the sixth atom, and a rotation that breaks Parseval proves nothing about
designs.

This module answers the objection.  A residual gauge survives INSIDE the design
locus, and it is the commutant of the inside weights.

## The invariance

Write the inside atoms as the columns of a frame `V`, and let `D` be the
diagonal matrix of inside weights.  Two moments carry the whole outside of the
design: the corner `V Vᵀ` and the inside moment `V D Vᵀ`, the second because the
outside moment is `1 − V D Vᵀ` and every outside atom is built from it.

For an orthogonal `R` (`Gtz.gaugeFrame_moment_eq`, `Gtz.gaugeFrame_corner_eq`):

* `(V R) (V R)ᵀ = V Vᵀ` — always, so the corner is gauge-free.
* **`(V R) D (V R)ᵀ = V D Vᵀ` whenever `R` COMMUTES with `D`.**

Two lines each: `R Rᵀ = 1` collapses the first, and `R D = D R` moves `D` past
`R` before the same collapse.  The second is the load-bearing one, and its
hypothesis is exactly commutation — nothing about eigenplanes, nothing about
three dimensions.

## The gauge is not empty

When two inside weights agree the commutant is positive-dimensional.
`Gtz.planarGauge` is the rotation of the first two coordinates,
`Gtz.planarGauge_orthogonal` gives `R Rᵀ = 1` from `c² + s² = 1`, and
`Gtz.planarGauge_commutes_diagonal` gives `R D = D R` for `D = diag(t, t, s)`
with NO condition relating `t` and `s`.  Chaining them
(`Gtz.planarGauge_moment_eq`, `Gtz.planarGauge_outside_moment_eq`) leaves the
inside moment and hence the outside moment fixed along a full circle of
designs.

## What it costs the arm

The corner, every inside weight, the whole outside moment, hence every outside
atom, every outside pair minor and the complement triple are all constant along
the circle.  The inside atoms are not.  So **no function of the outside data and
the weights can decide anything about the inside atoms**, and a repayment
certificate must read the individual inside readings.  That is the design-locus
form of the coherent-horn lane's gauge theorem, which it left open as its
sharpest next step.

[MEASURED on twelve complement-refusing corners built from the general corner
design chart, sweeping the circle at 721 points each.  The outside moment drifts
by at most `1.1e-16` and the complement's refusal never changes, while the
inside atoms move by up to `6.8` and an inside leverage swings from `4.64` to
`1.0003`.  The identity of the repaying inside atom CHANGES along the circle --
one orbit hands the pair `{3,4}` from atom `0` to atom `1` -- and up to eight
distinct repaying sets occur on a single orbit.  The number of repaying slots
never reaches zero: its minimum over each orbit is at least one.  So the WITNESS
of repayment is gauge-dependent while its EXISTENCE is gauge-invariant, which is
why the arm's criterion for repayment is an existential with no selector.]
-/
import Gtz.Wave.OppositeHornSelect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. The two moments under an orthogonal change of frame -/

/-- **THE CORNER IS GAUGE-FREE.**  An orthogonal change of the inside frame
leaves the unweighted moment, hence the corner, unchanged. -/
theorem gaugeFrame_corner_eq (V R : Matrix (Fin 3) (Fin 3) ℝ)
    (horth : R * Rᵀ = 1) :
    (V * R) * (V * R)ᵀ = V * Vᵀ := by
  rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc V R,
    horth, Matrix.mul_one]

/-- **THE INSIDE MOMENT IS GAUGE-FREE ON THE COMMUTANT.**  An orthogonal change
of the inside frame that COMMUTES with the inside weights leaves the weighted
moment unchanged.  This is the invariance that survives Parseval: the outside
moment is one less this, so the entire outside of the design is fixed. -/
theorem gaugeFrame_moment_eq (V R D : Matrix (Fin 3) (Fin 3) ℝ)
    (horth : R * Rᵀ = 1) (hcomm : R * D = D * R) :
    (V * R) * D * (V * R)ᵀ = V * D * Vᵀ := by
  have key : R * (D * (Rᵀ * Vᵀ)) = D * Vᵀ := by
    rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, ← Matrix.mul_assoc R,
      horth, Matrix.one_mul]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [key]

/-- **THE OUTSIDE MOMENT IS GAUGE-FREE ON THE COMMUTANT.**  Parseval writes the
outside moment as one less the inside moment, so it inherits the invariance. -/
theorem gaugeFrame_outside_moment_eq (V R D : Matrix (Fin 3) (Fin 3) ℝ)
    (horth : R * Rᵀ = 1) (hcomm : R * D = D * R) :
    1 - (V * R) * D * (V * R)ᵀ = 1 - V * D * Vᵀ := by
  rw [gaugeFrame_moment_eq V R D horth hcomm]

/-! ## 2. The commutant is not trivial -/

/-- The rotation of the first two coordinates. -/
def planarGauge (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![![c, -s, 0], ![s, c, 0], ![0, 0, 1]]

/-- The planar rotation is orthogonal exactly on the circle. -/
theorem planarGauge_orthogonal {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    planarGauge c s * (planarGauge c s)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planarGauge, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three] <;>
    nlinarith [hcs]

/-- **THE PLANAR ROTATION COMMUTES WITH ANY TWO-EQUAL-WEIGHT DIAGONAL.**  No
relation between the repeated weight and the third is needed. -/
theorem planarGauge_commutes_diagonal (c s t w : ℝ) :
    planarGauge c s * Matrix.diagonal ![t, t, w]
      = Matrix.diagonal ![t, t, w] * planarGauge c s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planarGauge, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

/-- **THE CIRCLE OF DESIGNS.**  On the two-equal-weight locus the inside moment
is constant along the planar rotation. -/
theorem planarGauge_moment_eq (V : Matrix (Fin 3) (Fin 3) ℝ) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (t w : ℝ) :
    (V * planarGauge c s) * Matrix.diagonal ![t, t, w]
        * (V * planarGauge c s)ᵀ
      = V * Matrix.diagonal ![t, t, w] * Vᵀ :=
  gaugeFrame_moment_eq V (planarGauge c s) _ (planarGauge_orthogonal hcs)
    (planarGauge_commutes_diagonal c s t w)

/-- The outside moment is constant along the same circle, so every outside atom
of the design is. -/
theorem planarGauge_outside_moment_eq (V : Matrix (Fin 3) (Fin 3) ℝ) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (t w : ℝ) :
    1 - (V * planarGauge c s) * Matrix.diagonal ![t, t, w]
        * (V * planarGauge c s)ᵀ
      = 1 - V * Matrix.diagonal ![t, t, w] * Vᵀ := by
  rw [planarGauge_moment_eq V hcs t w]

/-- The corner is constant along the circle too, so the whole orbit sits over
one corner. -/
theorem planarGauge_corner_eq (V : Matrix (Fin 3) (Fin 3) ℝ) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (V * planarGauge c s) * (V * planarGauge c s)ᵀ = V * Vᵀ :=
  gaugeFrame_corner_eq V (planarGauge c s) (planarGauge_orthogonal hcs)

/-! ## 3. The gauge moves the inside atoms -/

/-- **THE ORBIT IS NOT CONSTANT.**  A quarter turn exchanges the first two
inside atoms up to sign, so the frame genuinely moves while every moment above
stands still.  The gauge is a real freedom of the design, not a relabelling. -/
theorem planarGauge_quarterTurn_frame (V : Matrix (Fin 3) (Fin 3) ℝ)
    (i : Fin 3) :
    (V * planarGauge 0 1) i 0 = V i 1
      ∧ (V * planarGauge 0 1) i 1 = -V i 0
      ∧ (V * planarGauge 0 1) i 2 = V i 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [planarGauge, Matrix.mul_apply, Fin.sum_univ_three]

end Gtz
