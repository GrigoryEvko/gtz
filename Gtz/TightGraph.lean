/-
# The tight graph: at most two tight partners per atom

Mechanization of the **max-degree theorem** of the certificate frame (the
engine of the zero-set classification: tight graphs are disjoint paths and
cycles, so the star `K₁,₃` is dead in one line).

The informal argument is "tight partners of `c` lie on its polar chord, and a
chord meets the circle twice". Mechanizing it pins down what that needs:

* the tightness relation `cos²(γ/2) = ν_c ν_d` combined with the focal-conic
  relation `ν_d = 1/2 + ⟨ξ,u_d⟩` is an AFFINE condition on the partner
  direction — `⟨polarNormal, u_d⟩ = (ν_c − 1)/2` (`tight_iff_polar`);
* the chord's normal is nonzero exactly when `|ξ| < 1/2` bounds the atom's
  own pull — the side condition the prose leaves implicit, and precisely
  where the (now unconditional) `|ξ| < 1/2` corollary is load-bearing
  (`polarNormal_ne_zero`);
* a line meets the unit circle at most twice (`unitCircle_line_le_two`), from
  which the max-degree bound and the death of `K₁,₃` follow.
-/
import Mathlib
import Gtz.PsdKit
import Gtz.Pushoff

namespace Gtz

open Matrix

/-! ### A line meets the unit circle at most twice -/

/-- The signed area coordinate against a normal: the component of `planarVec`
along the normal's perpendicular. -/
def perpCoord (normal planarVec : Fin 2 → ℝ) : ℝ :=
  normal 1 * planarVec 0 - normal 0 * planarVec 1

/-- Pythagoras against a normal: the along- and across-components of a unit
vector determine each other. -/
theorem perpCoord_sq_of_unit {normal planarVec : Fin 2 → ℝ}
    (hunit : planarVec ⬝ᵥ planarVec = 1) :
    perpCoord normal planarVec ^ 2
      = normal ⬝ᵥ normal - (normal ⬝ᵥ planarVec) ^ 2 := by
  simp only [perpCoord, dotProduct, Fin.sum_univ_two] at *
  nlinarith [hunit]

/-- Two unit vectors with the same along- and across-components coincide. -/
theorem eq_of_coords_eq {normal leftVec rightVec : Fin 2 → ℝ}
    (hnormal : normal ⬝ᵥ normal ≠ 0)
    (halong : normal ⬝ᵥ leftVec = normal ⬝ᵥ rightVec)
    (hacross : perpCoord normal leftVec = perpCoord normal rightVec) :
    leftVec = rightVec := by
  have hnn : normal 0 * normal 0 + normal 1 * normal 1 ≠ 0 := by
    simpa only [dotProduct, Fin.sum_univ_two] using hnormal
  simp only [dotProduct, Fin.sum_univ_two] at halong
  simp only [perpCoord] at hacross
  ext i
  fin_cases i
  · show leftVec 0 = rightVec 0
    have hcomb : (normal 0 * normal 0 + normal 1 * normal 1)
        * (leftVec 0 - rightVec 0) = 0 := by
      linear_combination normal 0 * halong + normal 1 * hacross
    rcases mul_eq_zero.mp hcomb with h | h
    · exact absurd h hnn
    · linarith
  · show leftVec 1 = rightVec 1
    have hcomb : (normal 0 * normal 0 + normal 1 * normal 1)
        * (leftVec 1 - rightVec 1) = 0 := by
      linear_combination normal 1 * halong - normal 0 * hacross
    rcases mul_eq_zero.mp hcomb with h | h
    · exact absurd h hnn
    · linarith

/-- **A line meets the unit circle at most twice**: three unit vectors with a
common along-component against a nonzero normal cannot be pairwise distinct. -/
theorem unitCircle_line_le_two {normal firstVec secondVec thirdVec : Fin 2 → ℝ}
    (hnormal : normal ⬝ᵥ normal ≠ 0)
    (hfirst : firstVec ⬝ᵥ firstVec = 1) (hsecond : secondVec ⬝ᵥ secondVec = 1)
    (hthird : thirdVec ⬝ᵥ thirdVec = 1)
    (halongSecond : normal ⬝ᵥ firstVec = normal ⬝ᵥ secondVec)
    (halongThird : normal ⬝ᵥ firstVec = normal ⬝ᵥ thirdVec) :
    firstVec = secondVec ∨ firstVec = thirdVec ∨ secondVec = thirdVec := by
  -- All three across-components have the same square.
  have hsqFirst := perpCoord_sq_of_unit (normal := normal) hfirst
  have hsqSecond := perpCoord_sq_of_unit (normal := normal) hsecond
  have hsqThird := perpCoord_sq_of_unit (normal := normal) hthird
  have hsecondEq : perpCoord normal secondVec ^ 2
      = perpCoord normal firstVec ^ 2 := by
    rw [hsqSecond, hsqFirst, halongSecond]
  have hthirdEq : perpCoord normal thirdVec ^ 2
      = perpCoord normal firstVec ^ 2 := by
    rw [hsqThird, hsqFirst, halongThird]
  -- Equal squares force equal-or-opposite across-components; three of them
  -- cannot be pairwise opposite.
  have hsecondCases : perpCoord normal secondVec = perpCoord normal firstVec
      ∨ perpCoord normal secondVec = -perpCoord normal firstVec := by
    have hfactor : (perpCoord normal secondVec - perpCoord normal firstVec)
        * (perpCoord normal secondVec + perpCoord normal firstVec) = 0 := by
      nlinarith [hsecondEq]
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hthirdCases : perpCoord normal thirdVec = perpCoord normal firstVec
      ∨ perpCoord normal thirdVec = -perpCoord normal firstVec := by
    have hfactor : (perpCoord normal thirdVec - perpCoord normal firstVec)
        * (perpCoord normal thirdVec + perpCoord normal firstVec) = 0 := by
      nlinarith [hthirdEq]
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hsecondCases with hsecondSame | hsecondOpp
  · exact Or.inl (eq_of_coords_eq hnormal halongSecond hsecondSame.symm)
  · rcases hthirdCases with hthirdSame | hthirdOpp
    · exact Or.inr (Or.inl (eq_of_coords_eq hnormal halongThird hthirdSame.symm))
    · refine Or.inr (Or.inr (eq_of_coords_eq hnormal ?_ ?_))
      · rw [← halongSecond, halongThird]
      · rw [hsecondOpp, hthirdOpp]

/-! ### Tightness is an affine condition on the partner direction -/

/-- The polar normal of an atom against the conic moment: `u_c/2 − ν_c ξ`. -/
noncomputable def polarNormal (moment ownDirection : Fin 2 → ℝ)
    (ownConic : ℝ) : Fin 2 → ℝ :=
  fun i => ownDirection i / 2 - ownConic * moment i

/-- **Tightness is affine in the partner direction.** With the tightness
relation `(1 + ⟨u_c,u_d⟩)/2 = ν_c ν_d` and the focal conic `ν_d = 1/2 +
⟨ξ,u_d⟩`, the partner direction satisfies `⟨polarNormal, u_d⟩ = (ν_c − 1)/2`
— the polar chord of the atom. -/
theorem tight_iff_polar (moment ownDirection partnerDirection : Fin 2 → ℝ)
    (ownConic partnerConic : ℝ)
    (hconic : partnerConic = 1/2 + moment ⬝ᵥ partnerDirection) :
    (1 + ownDirection ⬝ᵥ partnerDirection) / 2 = ownConic * partnerConic
      ↔ polarNormal moment ownDirection ownConic ⬝ᵥ partnerDirection
        = (ownConic - 1) / 2 := by
  subst hconic
  simp only [polarNormal, dotProduct, Fin.sum_univ_two]
  constructor <;> intro h <;> nlinarith [h]

/-- **The polar normal is nonzero** whenever the moment is short (`|ξ| < 1/2`,
now an unconditional corollary of the chord theorem) and the atom's conic
value is in `[0,1]`. This is the side condition the informal "a chord meets
the circle twice" argument leaves implicit. -/
theorem polarNormal_ne_zero {moment ownDirection : Fin 2 → ℝ} {ownConic : ℝ}
    (hunit : ownDirection ⬝ᵥ ownDirection = 1)
    (hmomentShort : planarNorm moment < 1/2)
    (hconicNonneg : 0 ≤ ownConic) (hconicLeOne : ownConic ≤ 1) :
    polarNormal moment ownDirection ownConic
        ⬝ᵥ polarNormal moment ownDirection ownConic ≠ 0 := by
  have hmomentSq : planarNorm moment ^ 2 = moment ⬝ᵥ moment := planarNorm_sq _
  have hmomentNonneg : 0 ≤ planarNorm moment := planarNorm_nonneg _
  -- Cauchy–Schwarz against the unit direction: the pull is at most `|ξ|`.
  have hunitNorm : planarNorm ownDirection = 1 :=
    planarNorm_eq_of_sq (by norm_num) (by rw [hunit]; norm_num)
  have hcs : ownDirection ⬝ᵥ moment ≤ planarNorm moment := by
    have hbound := dotProduct_le_planarNorm_mul ownDirection moment
    rwa [hunitNorm, one_mul] at hbound
  -- The conic value cannot amplify a short moment past the half-length.
  have hpull : ownConic * planarNorm moment < 1/2 := by
    nlinarith [hconicLeOne, hconicNonneg, hmomentNonneg, hmomentShort]
  have hexpand : polarNormal moment ownDirection ownConic
      ⬝ᵥ polarNormal moment ownDirection ownConic
      = 1/4 - ownConic * (ownDirection ⬝ᵥ moment)
        + ownConic ^ 2 * (moment ⬝ᵥ moment) := by
    simp only [polarNormal, dotProduct, Fin.sum_univ_two] at *
    nlinarith [hunit]
  -- Completing the square: `|n|² = (1/2 − ν|ξ|)² + ν(|ξ| − ⟨u,ξ⟩) > 0`.
  have hsplit : 1/4 - ownConic * (ownDirection ⬝ᵥ moment)
      + ownConic ^ 2 * (moment ⬝ᵥ moment)
      = (1/2 - ownConic * planarNorm moment) ^ 2
        + ownConic * (planarNorm moment - ownDirection ⬝ᵥ moment) := by
    rw [← hmomentSq]; ring
  have hsquarePos : 0 < (1/2 - ownConic * planarNorm moment) ^ 2 :=
    pow_pos (by linarith) 2
  have hrest : 0 ≤ ownConic * (planarNorm moment - ownDirection ⬝ᵥ moment) :=
    mul_nonneg hconicNonneg (sub_nonneg.mpr hcs)
  rw [hexpand, hsplit]
  intro hzero
  linarith

/-- **The max-degree theorem**: an atom has at most two tight partners. Three
tight partner directions must contain a repeat (a clone), so the tight graph
has maximum degree two — hence its components are paths and cycles, and the
star `K₁,₃` cannot occur. -/
theorem tight_partners_le_two {moment ownDirection : Fin 2 → ℝ}
    {firstPartner secondPartner thirdPartner : Fin 2 → ℝ}
    {ownConic firstConic secondConic thirdConic : ℝ}
    (hownUnit : ownDirection ⬝ᵥ ownDirection = 1)
    (hmomentShort : planarNorm moment < 1/2)
    (hconicNonneg : 0 ≤ ownConic) (hconicLeOne : ownConic ≤ 1)
    (hfirstUnit : firstPartner ⬝ᵥ firstPartner = 1)
    (hsecondUnit : secondPartner ⬝ᵥ secondPartner = 1)
    (hthirdUnit : thirdPartner ⬝ᵥ thirdPartner = 1)
    (hfirstConic : firstConic = 1/2 + moment ⬝ᵥ firstPartner)
    (hsecondConic : secondConic = 1/2 + moment ⬝ᵥ secondPartner)
    (hthirdConic : thirdConic = 1/2 + moment ⬝ᵥ thirdPartner)
    (hfirstTight : (1 + ownDirection ⬝ᵥ firstPartner) / 2
      = ownConic * firstConic)
    (hsecondTight : (1 + ownDirection ⬝ᵥ secondPartner) / 2
      = ownConic * secondConic)
    (hthirdTight : (1 + ownDirection ⬝ᵥ thirdPartner) / 2
      = ownConic * thirdConic) :
    firstPartner = secondPartner ∨ firstPartner = thirdPartner
      ∨ secondPartner = thirdPartner := by
  have hpolarFirst := (tight_iff_polar moment ownDirection firstPartner
    ownConic firstConic hfirstConic).mp hfirstTight
  have hpolarSecond := (tight_iff_polar moment ownDirection secondPartner
    ownConic secondConic hsecondConic).mp hsecondTight
  have hpolarThird := (tight_iff_polar moment ownDirection thirdPartner
    ownConic thirdConic hthirdConic).mp hthirdTight
  refine unitCircle_line_le_two
    (polarNormal_ne_zero hownUnit hmomentShort hconicNonneg hconicLeOne)
    hfirstUnit hsecondUnit hthirdUnit ?_ ?_
  · rw [hpolarFirst, hpolarSecond]
  · rw [hpolarFirst, hpolarThird]

/-- **The star `K₁,₃` is dead**: no atom has three PAIRWISE DISTINCT tight
partners. (Stated as the contrapositive of the max-degree theorem, which is
how the classification consumes it.) -/
theorem star_three_impossible {moment ownDirection : Fin 2 → ℝ}
    {firstPartner secondPartner thirdPartner : Fin 2 → ℝ}
    {ownConic firstConic secondConic thirdConic : ℝ}
    (hownUnit : ownDirection ⬝ᵥ ownDirection = 1)
    (hmomentShort : planarNorm moment < 1/2)
    (hconicNonneg : 0 ≤ ownConic) (hconicLeOne : ownConic ≤ 1)
    (hfirstUnit : firstPartner ⬝ᵥ firstPartner = 1)
    (hsecondUnit : secondPartner ⬝ᵥ secondPartner = 1)
    (hthirdUnit : thirdPartner ⬝ᵥ thirdPartner = 1)
    (hfirstConic : firstConic = 1/2 + moment ⬝ᵥ firstPartner)
    (hsecondConic : secondConic = 1/2 + moment ⬝ᵥ secondPartner)
    (hthirdConic : thirdConic = 1/2 + moment ⬝ᵥ thirdPartner)
    (hfirstTight : (1 + ownDirection ⬝ᵥ firstPartner) / 2
      = ownConic * firstConic)
    (hsecondTight : (1 + ownDirection ⬝ᵥ secondPartner) / 2
      = ownConic * secondConic)
    (hthirdTight : (1 + ownDirection ⬝ᵥ thirdPartner) / 2
      = ownConic * thirdConic)
    (hdistinctFirstSecond : firstPartner ≠ secondPartner)
    (hdistinctFirstThird : firstPartner ≠ thirdPartner)
    (hdistinctSecondThird : secondPartner ≠ thirdPartner) : False := by
  rcases tight_partners_le_two hownUnit hmomentShort hconicNonneg hconicLeOne
    hfirstUnit hsecondUnit hthirdUnit hfirstConic hsecondConic hthirdConic
    hfirstTight hsecondTight hthirdTight with h | h | h
  · exact hdistinctFirstSecond h
  · exact hdistinctFirstThird h
  · exact hdistinctSecondThird h

end Gtz
