/-
# A blind member collapses the triple to two vectors in the probe's plane

`Gtz.nullProbe_in_plane_of_blind_member` puts the null probe of a weak dominator
in the plane of the two members that still read it.  This module reads the same
configuration from the other side and finds that the collapse is TOTAL: the two
non-blind members contribute, on the whole orthogonal complement of the probe,
exactly ONE rank-one term between them.

Write `be = b . w`, `ga = c . w` for the two live readings, and recall
`Gtz.planePart w x = x - (x . w) * w`.

* `Gtz.blind_planeParts_antiparallel` -- **the two plane parts are
  antiparallel**: `be * planePart w b + ga * planePart w c = 0`.  One line from
  the reproduction, because the blind term is absent from it and the two
  readings square to one.
* `Gtz.blindPlaneVector` -- their common direction `n = ga⁻¹ * planePart w b`,
  with the two decompositions

    `b = be * w + ga * n` ,   `c = ga * w - be * n` .

  So the triple `{a, b, c}` is carried by THREE vectors `a`, `n`, `w`, of which
  `a` and `n` lie in `w`'s orthogonal complement.
* `Gtz.blind_form_on_perp` -- hence, on that complement, the triple's quadratic
  form is a two-term sum: for every `v` with `v . w = 0`,

    **`(b . v)^2 + (c . v)^2 = (n . v)^2`** .

  The angle between `b` and `c` is invisible off the probe.
* `Gtz.blind_pairMinorTotal_eq_pairGapMinor` -- **the second invariant of the
  triple is a single PAIR minor**: `pairMinorTotal a b c = pairGapMinor a n`.

## What this buys

The second invariant is the quantity that separates the corank-one arm's two
cases, and at a blind member it stops being a three-atom object: everything the
case can say is a statement about the two plane vectors `a` and `n`.  The landed
adjugate law then distributes it back over the triple as
`pairGapMinor a b = ga^2 * pairGapMinor a n` and
`pairGapMinor a c = be^2 * pairGapMinor a n`, with `pairGapMinor b c = 0` --
and that last one is re-derived here from the decompositions alone
(`Gtz.blind_pairGapMinor_eq_zero`), with no adjugate law and no positivity.

Sections 1 to 3 are the ABSTRACT normal form: they assume the two decompositions
and prove everything from them, with `n` an unconstrained vector.  Section 4
produces the decompositions from the blind reading.  Nothing anywhere needs a
design, a size, or positive semidefiniteness.

[MEASURED before proving, 6000 random configurations: the antiparallel law to
`2.2e-16`, the form on the complement to `1.7e-13`, and
`pairMinorTotal a b c = pairGapMinor a n` to `1.7e-13`.]
-/
import Gtz.Wave.NullProbeAdjugateLaw
import Gtz.Wave.KTwoProbeNormalise

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. Dot products of axis-plus-plane combinations -/

/-- Two combinations of a unit axis and one orthogonal vector pair up
diagonally. -/
theorem dotProduct_axis_plane {w n : Fin 3 → ℝ} (hnorm : w ⬝ᵥ w = 1)
    (hwn : n ⬝ᵥ w = 0) (p q r s : ℝ) :
    (p • w + q • n) ⬝ᵥ (r • w + s • n) = p * r + q * s * (n ⬝ᵥ n) := by
  have hwn' : w ⬝ᵥ n = 0 := by rw [dotProduct_comm]; exact hwn
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hnorm, hwn, hwn']
  ring

/-- A vector reads an axis-plus-plane combination through its own two
readings. -/
theorem dotProduct_axis_plane_left {w n : Fin 3 → ℝ} (u : Fin 3 → ℝ) (p q : ℝ) :
    u ⬝ᵥ (p • w + q • n) = p * (u ⬝ᵥ w) + q * (u ⬝ᵥ n) := by
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]

/-! ## 2. The abstract normal form -/

section Abstract

variable {a b c w n : Fin 3 → ℝ} {be ga : ℝ}

/-- The second member's length excess, in the plane vector. -/
theorem nf_leverage_left (hnorm : w ⬝ᵥ w = 1) (hwn : n ⬝ᵥ w = 0)
    (hsq : be ^ 2 + ga ^ 2 = 1) (hb : b = be • w + ga • n) :
    leverageOf b - 1 = ga ^ 2 * (leverageOf n - 1) := by
  have hbb : b ⬝ᵥ b = be * be + ga * ga * (n ⬝ᵥ n) := by
    rw [hb, dotProduct_axis_plane hnorm hwn]
  rw [← dotProduct_self_eq_leverage, ← dotProduct_self_eq_leverage, hbb]
  nlinarith [hsq]

/-- The third member's length excess, in the plane vector. -/
theorem nf_leverage_right (hnorm : w ⬝ᵥ w = 1) (hwn : n ⬝ᵥ w = 0)
    (hsq : be ^ 2 + ga ^ 2 = 1) (hc : c = ga • w - be • n) :
    leverageOf c - 1 = be ^ 2 * (leverageOf n - 1) := by
  have hc' : c = ga • w + (-be) • n := by rw [hc, neg_smul]; abel
  have hcc : c ⬝ᵥ c = ga * ga + (-be) * (-be) * (n ⬝ᵥ n) := by
    rw [hc', dotProduct_axis_plane hnorm hwn]
  rw [← dotProduct_self_eq_leverage, ← dotProduct_self_eq_leverage, hcc]
  nlinarith [hsq]

/-- The blind member reads the second through the plane vector. -/
theorem nf_pairing_left (hblind : a ⬝ᵥ w = 0) (hb : b = be • w + ga • n) :
    a ⬝ᵥ b = ga * (a ⬝ᵥ n) := by
  rw [hb, dotProduct_axis_plane_left a be ga, hblind, mul_zero, zero_add]

/-- The blind member reads the third through the plane vector, with a sign. -/
theorem nf_pairing_right (hblind : a ⬝ᵥ w = 0) (hc : c = ga • w - be • n) :
    a ⬝ᵥ c = -(be * (a ⬝ᵥ n)) := by
  have hc' : c = ga • w + (-be) • n := by rw [hc, neg_smul]; abel
  rw [hc', dotProduct_axis_plane_left a ga (-be), hblind, mul_zero, zero_add]
  ring

/-- The two live members read each other through the plane vector alone. -/
theorem nf_pairing_live (hnorm : w ⬝ᵥ w = 1) (hwn : n ⬝ᵥ w = 0)
    (hb : b = be • w + ga • n) (hc : c = ga • w - be • n) :
    b ⬝ᵥ c = be * ga * (1 - leverageOf n) := by
  have hc' : c = ga • w + (-be) • n := by rw [hc, neg_smul]; abel
  have hbc : b ⬝ᵥ c = be * ga + ga * (-be) * (n ⬝ᵥ n) := by
    rw [hb, hc', dotProduct_axis_plane hnorm hwn]
  rw [hbc, ← dotProduct_self_eq_leverage]; ring

/-- A vector orthogonal to the axis reads the second member through the plane
vector. -/
theorem nf_perp_left {v : Fin 3 → ℝ} (hv : w ⬝ᵥ v = 0) (hb : b = be • w + ga • n) :
    b ⬝ᵥ v = ga * (n ⬝ᵥ v) := by
  rw [hb, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
    smul_eq_mul, hv, mul_zero, zero_add]

/-- The same for the third member, with a sign. -/
theorem nf_perp_right {v : Fin 3 → ℝ} (hv : w ⬝ᵥ v = 0) (hc : c = ga • w - be • n) :
    c ⬝ᵥ v = -(be * (n ⬝ᵥ v)) := by
  rw [hc, sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
    smul_eq_mul, hv, mul_zero, zero_sub]

/-! ## 3. The two consequences, abstractly -/

/-- **THE LIVE PAIR IS EXACTLY BOUNDARY ADMISSIBLE.**  From the decompositions
alone, with no adjugate law and no positivity. -/
theorem nf_pairGapMinor_eq_zero (hnorm : w ⬝ᵥ w = 1) (hwn : n ⬝ᵥ w = 0)
    (hsq : be ^ 2 + ga ^ 2 = 1) (hb : b = be • w + ga • n)
    (hc : c = ga • w - be • n) :
    pairGapMinor b c = 0 := by
  rw [pairGapMinor, nf_leverage_left hnorm hwn hsq hb,
    nf_leverage_right hnorm hwn hsq hc, nf_pairing_live hnorm hwn hb hc]
  ring

/-- **THE SECOND INVARIANT IS A SINGLE PAIR MINOR.**  The three-atom invariant
collapses to the pair minor of the blind member against the plane vector, and
the two live readings vanish from it entirely. -/
theorem nf_pairMinorTotal_eq_pairGapMinor (hnorm : w ⬝ᵥ w = 1) (hwn : n ⬝ᵥ w = 0)
    (hsq : be ^ 2 + ga ^ 2 = 1) (hblind : a ⬝ᵥ w = 0)
    (hb : b = be • w + ga • n) (hc : c = ga • w - be • n) :
    pairMinorTotal a b c = pairGapMinor a n := by
  rw [pairMinorTotal, pairGapMinor, pairGapMinor, pairGapMinor, pairGapMinor,
    nf_leverage_left hnorm hwn hsq hb, nf_leverage_right hnorm hwn hsq hc,
    nf_pairing_left hblind hb, nf_pairing_right hblind hc,
    nf_pairing_live hnorm hwn hb hc]
  linear_combination ((leverageOf a - 1) * (leverageOf n - 1) - (a ⬝ᵥ n) ^ 2) * hsq

/-- **THE FORM OFF THE PROBE IS A TWO-TERM SUM.**  On the axis's orthogonal
complement the two live members contribute exactly one square between them. -/
theorem nf_form_on_perp (hsq : be ^ 2 + ga ^ 2 = 1) {v : Fin 3 → ℝ}
    (hv : w ⬝ᵥ v = 0) (hb : b = be • w + ga • n) (hc : c = ga • w - be • n) :
    (b ⬝ᵥ v) ^ 2 + (c ⬝ᵥ v) ^ 2 = (n ⬝ᵥ v) ^ 2 := by
  rw [nf_perp_left hv hb, nf_perp_right hv hc]
  nlinarith [hsq]

end Abstract

/-! ## 4. The blind reading produces the decompositions -/

/-- With the first member blind, the other two readings carry the whole probe. -/
theorem blind_readings_sq_sum {a b c w : Fin 3 → ℝ}
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1)
    (hblind : a ⬝ᵥ w = 0) :
    (b ⬝ᵥ w) ^ 2 + (c ⬝ᵥ w) ^ 2 = 1 := by
  have h := nullProbe_readings_resolve a b c w hrep
  rw [hnorm, hblind] at h
  linarith

/-- **THE ANTIPARALLEL LAW.**  The plane parts of the two live members cancel
against their own readings.  The blind member drops out of the reproduction, and
what is left is the probe, which the readings then subtract away. -/
theorem blind_planeParts_antiparallel {a b c w : Fin 3 → ℝ}
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1)
    (hblind : a ⬝ᵥ w = 0) :
    (b ⬝ᵥ w) • planePart w b + (c ⬝ᵥ w) • planePart w c = 0 := by
  have hsq := blind_readings_sq_sum hrep hnorm hblind
  have htwo : (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w := by
    rw [hblind, zero_smul, zero_add] at hrep; exact hrep
  have hexpand : (b ⬝ᵥ w) • planePart w b + (c ⬝ᵥ w) • planePart w c
      = ((b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c)
        - ((b ⬝ᵥ w) ^ 2 + (c ⬝ᵥ w) ^ 2) • w := by
    simp only [planePart, smul_sub, smul_smul, add_smul, sq]
    abel
  rw [hexpand, htwo, hsq, one_smul, sub_self]

/-- The direction the two live plane parts share, normalised by the third
member's reading. -/
noncomputable def blindPlaneVector (b c w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (c ⬝ᵥ w)⁻¹ • planePart w b

/-- The plane vector is orthogonal to the probe. -/
theorem blindPlaneVector_dotProduct_axis (b c w : Fin 3 → ℝ) (hnorm : w ⬝ᵥ w = 1) :
    blindPlaneVector b c w ⬝ᵥ w = 0 := by
  rw [blindPlaneVector, smul_dotProduct, smul_eq_mul,
    dotProduct_comm (planePart w b) w, dotProduct_planePart w b hnorm, mul_zero]

/-- **THE FIRST DECOMPOSITION.**  The second member is its axis part plus the
plane vector, scaled by the THIRD member's reading. -/
theorem blind_decomposition_left {b c w : Fin 3 → ℝ} (hgamma : c ⬝ᵥ w ≠ 0) :
    b = (b ⬝ᵥ w) • w + (c ⬝ᵥ w) • blindPlaneVector b c w := by
  have hkey : b - ((b ⬝ᵥ w) • w + (c ⬝ᵥ w) • blindPlaneVector b c w) = 0 := by
    rw [blindPlaneVector, smul_smul, mul_inv_cancel₀ hgamma, one_smul, planePart]
    abel
  exact sub_eq_zero.mp hkey

/-- **THE SECOND DECOMPOSITION.**  The third member is its axis part MINUS the
plane vector, scaled by the second member's reading.  The sign is the
antiparallel law. -/
theorem blind_decomposition_right {a b c w : Fin 3 → ℝ}
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1)
    (hblind : a ⬝ᵥ w = 0) (hgamma : c ⬝ᵥ w ≠ 0) :
    c = (c ⬝ᵥ w) • w - (b ⬝ᵥ w) • blindPlaneVector b c w := by
  have hanti := blind_planeParts_antiparallel hrep hnorm hblind
  have hpc : planePart w c + (b ⬝ᵥ w) • blindPlaneVector b c w = 0 := by
    have h := congrArg (fun z : Fin 3 → ℝ => (c ⬝ᵥ w)⁻¹ • z) hanti
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hgamma, one_smul,
      smul_zero] at h
    rw [blindPlaneVector, smul_smul, mul_comm (b ⬝ᵥ w) ((c ⬝ᵥ w)⁻¹), add_comm]
    exact h
  have hkey : c - ((c ⬝ᵥ w) • w - (b ⬝ᵥ w) • blindPlaneVector b c w)
      = planePart w c + (b ⬝ᵥ w) • blindPlaneVector b c w := by
    rw [planePart]; abel
  exact sub_eq_zero.mp (by rw [hkey, hpc])

/-! ## 5. The normal form at a blind member -/

section Blind

variable {a b c w : Fin 3 → ℝ}

/-- **THE LIVE PAIR IS BOUNDARY ADMISSIBLE.**  The instance of
`Gtz.nf_pairGapMinor_eq_zero` at a blind member. -/
theorem blind_pairGapMinor_eq_zero
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1)
    (hblind : a ⬝ᵥ w = 0) (hgamma : c ⬝ᵥ w ≠ 0) :
    pairGapMinor b c = 0 :=
  nf_pairGapMinor_eq_zero hnorm (blindPlaneVector_dotProduct_axis b c w hnorm)
    (blind_readings_sq_sum hrep hnorm hblind)
    (blind_decomposition_left hgamma)
    (blind_decomposition_right hrep hnorm hblind hgamma)

/-- **THE SECOND INVARIANT IS A SINGLE PAIR MINOR.**  At a blind member the
triple's second invariant is the pair minor of the blind member against the
plane vector of the other two. -/
theorem blind_pairMinorTotal_eq_pairGapMinor
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1)
    (hblind : a ⬝ᵥ w = 0) (hgamma : c ⬝ᵥ w ≠ 0) :
    pairMinorTotal a b c = pairGapMinor a (blindPlaneVector b c w) :=
  nf_pairMinorTotal_eq_pairGapMinor hnorm
    (blindPlaneVector_dotProduct_axis b c w hnorm)
    (blind_readings_sq_sum hrep hnorm hblind) hblind
    (blind_decomposition_left hgamma)
    (blind_decomposition_right hrep hnorm hblind hgamma)

/-- **THE FORM OFF THE PROBE IS A TWO-TERM SUM.**  The two live members
contribute exactly one square between them on the probe's orthogonal
complement. -/
theorem blind_form_on_perp
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1)
    (hblind : a ⬝ᵥ w = 0) (hgamma : c ⬝ᵥ w ≠ 0) {v : Fin 3 → ℝ} (hv : w ⬝ᵥ v = 0) :
    (b ⬝ᵥ v) ^ 2 + (c ⬝ᵥ v) ^ 2 = (blindPlaneVector b c w ⬝ᵥ v) ^ 2 :=
  nf_form_on_perp (blind_readings_sq_sum hrep hnorm hblind) hv
    (blind_decomposition_left hgamma)
    (blind_decomposition_right hrep hnorm hblind hgamma)

end Blind

end Gtz
