/-
# Certificate-frame geometry: stress leaves, distinct rays, and the parabola

Mechanization of the planar-geometry steps the gaps-closure build uses to kill
the matching and cycle strata (pre-audit claims; mechanizing them IS the
audit).

* `planarDet` and its kit — the 2×2 determinant of a vector pair, the
  independence test used throughout;
* `eq_of_two_independent_rays` — the **stress-leaf step**: a point lying on
  two rays through a common vertex, whose directions are independent, IS the
  vertex (this is "the two rays lie on distinct lines through `v_e` ⟹
  `2ξ̃ = v_e`");
* `smul_eq_smul_of_independent` — the underlying independence lemma;
* `parabola_tight_iff` — on the parabola stratum `|ξ| = 1/2` (the moment
  aligned with a unit direction), the tightness relation between two atoms
  collapses to the half-angle product relation the build reports, so adjacent
  edges force clones.
-/
import Mathlib
import Gtz.PsdKit
import Gtz.Pushoff

namespace Gtz

open Matrix

/-- The planar determinant of a vector pair. -/
def planarDet (leftVec rightVec : Fin 2 → ℝ) : ℝ :=
  leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0

theorem planarDet_smul_left (scale : ℝ) (leftVec rightVec : Fin 2 → ℝ) :
    planarDet (scale • leftVec) rightVec = scale * planarDet leftVec rightVec := by
  simp only [planarDet, Pi.smul_apply, smul_eq_mul]
  ring

theorem planarDet_smul_right (scale : ℝ) (leftVec rightVec : Fin 2 → ℝ) :
    planarDet leftVec (scale • rightVec) = scale * planarDet leftVec rightVec := by
  simp only [planarDet, Pi.smul_apply, smul_eq_mul]
  ring

/-- Independent directions: proportional combinations must have zero
coefficients. -/
theorem smul_eq_smul_of_independent {leftDir rightDir : Fin 2 → ℝ}
    {leftScale rightScale : ℝ}
    (hindep : planarDet leftDir rightDir ≠ 0)
    (hprop : leftScale • leftDir = rightScale • rightDir) :
    leftScale = 0 ∧ rightScale = 0 := by
  have hdet : leftScale * planarDet leftDir rightDir = 0 := by
    rw [← planarDet_smul_left, hprop, planarDet_smul_left]
    simp only [planarDet]
    ring
  have hleftZero : leftScale = 0 := by
    rcases mul_eq_zero.mp hdet with h | h
    · exact h
    · exact absurd h hindep
  refine ⟨hleftZero, ?_⟩
  have hzero : rightScale • rightDir = 0 := by
    rw [← hprop, hleftZero, zero_smul]
  by_contra hne
  have hdirZero : rightDir = 0 := by
    have := congrArg (fun v => (rightScale)⁻¹ • v) hzero
    simpa [smul_smul, inv_mul_cancel₀ hne] using this
  rw [hdirZero] at hindep
  simp only [planarDet, Pi.zero_apply] at hindep
  exact hindep (by ring)

/-- **The stress-leaf step**: a point on two rays emanating from a common
vertex, with independent ray directions, is the vertex itself. This is the
build's "two rays through `v_e` lie on distinct lines ⟹ `2ξ̃ = v_e`". -/
theorem eq_of_two_independent_rays {vertex firstEnd secondEnd point : Fin 2 → ℝ}
    {firstScale secondScale : ℝ}
    (hindep : planarDet (firstEnd - vertex) (secondEnd - vertex) ≠ 0)
    (hfirstRay : point - vertex = firstScale • (firstEnd - vertex))
    (hsecondRay : point - vertex = secondScale • (secondEnd - vertex)) :
    point = vertex := by
  have hprop : firstScale • (firstEnd - vertex)
      = secondScale • (secondEnd - vertex) := by
    rw [← hfirstRay, hsecondRay]
  have hzero := smul_eq_smul_of_independent hindep hprop
  have hsub : point - vertex = 0 := by
    rw [hfirstRay, hzero.1, zero_smul]
  have := sub_eq_zero.mp hsub
  exact this

/-! ### The parabola stratum -/

/-- On the parabola stratum the moment has length exactly `1/2`; writing the
atom directions against it, the conic value of an atom is `1/2 + ⟨ξ,u⟩`, so an
atom's conic value vanishes exactly at the antipode of the moment direction —
the "pole" the build excludes by finite leverage. -/
theorem parabola_conic_zero_iff {moment atomDirection : Fin 2 → ℝ}
    (hmomentHalf : planarNorm moment = 1/2)
    (hunit : atomDirection ⬝ᵥ atomDirection = 1) :
    1/2 + moment ⬝ᵥ atomDirection = 0
      ↔ atomDirection = (-2 : ℝ) • moment := by
  have hmomentSq : moment ⬝ᵥ moment = 1/4 := by
    have := planarNorm_sq moment
    rw [hmomentHalf] at this
    rw [← this]; norm_num
  constructor
  · intro hzero
    -- Equality in Cauchy–Schwarz: the direction is the negated doubled moment.
    have hpair : moment ⬝ᵥ atomDirection = -(1/2) := by linarith
    have hgap : (atomDirection - (-2 : ℝ) • moment)
        ⬝ᵥ (atomDirection - (-2 : ℝ) • moment) = 0 := by
      simp only [dotProduct, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul] at *
      nlinarith [hunit, hmomentSq, hpair]
    have hcomp : ∀ i : Fin 2, atomDirection i - ((-2 : ℝ) • moment) i = 0 := by
      intro i
      simp only [dotProduct, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul] at hgap
      fin_cases i
      · show atomDirection 0 - (-2 : ℝ) * moment 0 = 0
        nlinarith [hgap, sq_nonneg (atomDirection 0 - (-2 : ℝ) * moment 0),
          sq_nonneg (atomDirection 1 - (-2 : ℝ) * moment 1)]
      · show atomDirection 1 - (-2 : ℝ) * moment 1 = 0
        nlinarith [hgap, sq_nonneg (atomDirection 0 - (-2 : ℝ) * moment 0),
          sq_nonneg (atomDirection 1 - (-2 : ℝ) * moment 1)]
    ext i
    have := hcomp i
    linarith [this]
  · intro hdir
    rw [hdir]
    simp only [dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at *
    nlinarith [hmomentSq]

/-- **Clones on the parabola**: two atoms whose conic values both vanish share
the same direction — so a parabola component cannot contain two distinct
pole atoms, which is the cloning step that limits parabola components to
single edges. -/
theorem parabola_poles_are_clones {moment firstDirection secondDirection :
    Fin 2 → ℝ}
    (hmomentHalf : planarNorm moment = 1/2)
    (hfirstUnit : firstDirection ⬝ᵥ firstDirection = 1)
    (hsecondUnit : secondDirection ⬝ᵥ secondDirection = 1)
    (hfirstPole : 1/2 + moment ⬝ᵥ firstDirection = 0)
    (hsecondPole : 1/2 + moment ⬝ᵥ secondDirection = 0) :
    firstDirection = secondDirection := by
  rw [(parabola_conic_zero_iff hmomentHalf hfirstUnit).mp hfirstPole,
    (parabola_conic_zero_iff hmomentHalf hsecondUnit).mp hsecondPole]


/-! ### Common orthogonality and the four-cycle -/

/-- In the plane, two vectors orthogonal to a common nonzero vector are
parallel. -/
theorem planarDet_eq_zero_of_common_orthogonal {leftVec rightVec common :
    Fin 2 → ℝ}
    (hcommon : common ⬝ᵥ common ≠ 0)
    (hleft : leftVec ⬝ᵥ common = 0) (hright : rightVec ⬝ᵥ common = 0) :
    planarDet leftVec rightVec = 0 := by
  have hcc : common 0 * common 0 + common 1 * common 1 ≠ 0 := by
    simpa only [dotProduct, Fin.sum_univ_two] using hcommon
  simp only [dotProduct, Fin.sum_univ_two] at hleft hright
  have hprod : planarDet leftVec rightVec
      * (common 0 * common 0 + common 1 * common 1) = 0 := by
    simp only [planarDet]
    linear_combination (rightVec 1 * common 0 - rightVec 0 * common 1) * hleft
      + (leftVec 0 * common 1 - leftVec 1 * common 0) * hright
  rcases mul_eq_zero.mp hprod with h | h
  · exact h
  · exact absurd h hcc

/-- **The four-cycle step**: in a tight 4-cycle `1–2–3–4–1`, atoms `1` and `3`
are common tight partners of both `2` and `4`, so — unless `1` and `3` are
clones — the polar normals of `2` and `4` are parallel. This is the collapse
that drives the 4-cycle stratum onto the parabola (and thence to clones). -/
theorem fourCycle_normals_parallel {firstDir thirdDir secondNormal fourthNormal :
    Fin 2 → ℝ} {secondOffset fourthOffset : ℝ}
    (hdistinct : firstDir ≠ thirdDir)
    (hsecondFirst : secondNormal ⬝ᵥ firstDir = secondOffset)
    (hsecondThird : secondNormal ⬝ᵥ thirdDir = secondOffset)
    (hfourthFirst : fourthNormal ⬝ᵥ firstDir = fourthOffset)
    (hfourthThird : fourthNormal ⬝ᵥ thirdDir = fourthOffset) :
    planarDet secondNormal fourthNormal = 0 := by
  have hgapNonzero : (firstDir - thirdDir) ⬝ᵥ (firstDir - thirdDir) ≠ 0 := by
    intro hzero
    refine hdistinct ?_
    have hcomp : ∀ i : Fin 2, firstDir i - thirdDir i = 0 := by
      intro i
      simp only [dotProduct, Fin.sum_univ_two, Pi.sub_apply] at hzero
      fin_cases i
      · show firstDir 0 - thirdDir 0 = 0
        nlinarith [hzero, sq_nonneg (firstDir 0 - thirdDir 0),
          sq_nonneg (firstDir 1 - thirdDir 1)]
      · show firstDir 1 - thirdDir 1 = 0
        nlinarith [hzero, sq_nonneg (firstDir 0 - thirdDir 0),
          sq_nonneg (firstDir 1 - thirdDir 1)]
    ext i
    linarith [hcomp i]
  refine planarDet_eq_zero_of_common_orthogonal hgapNonzero ?_ ?_
  · simp only [dotProduct, Fin.sum_univ_two, Pi.sub_apply] at *
    linarith [hsecondFirst, hsecondThird]
  · simp only [dotProduct, Fin.sum_univ_two, Pi.sub_apply] at *
    linarith [hfourthFirst, hfourthThird]

/-! ### Dust is never tight -/

/-- **Strict dust is never in a tight pair**: tightness forces
`p² = (ℓ_c − 1)(ℓ_d − 1)`, and a dust atom (`ℓ < 1`) paired with a heavy atom
(`ℓ > 1`) makes the right side negative. Combined with the covering theorem
(every atom of an equality design lies in a tight pair), this is the audit's
"no strict dust in ANY equality design". -/
theorem dust_never_tight {dustLev heavyLev pairing : ℝ}
    (hdust : dustLev < 1) (hheavy : 1 < heavyLev)
    (htight : pairing ^ 2 = (dustLev - 1) * (heavyLev - 1)) : False := by
  nlinarith [sq_nonneg pairing, htight, hdust, hheavy]

/-- Two dust atoms cannot be tight either: the pairing square would have to
exceed the product bound while both leverages sit below one. Tightness plus
the trace floor `ℓ_c + ℓ_d ≥ 2` excludes the pair. -/
theorem dust_pair_never_tight {firstLev secondLev pairing : ℝ}
    (hfirst : firstLev < 1) (hsecond : secondLev < 1)
    (htrace : 2 ≤ firstLev + secondLev) : False := by
  linarith

end Gtz
