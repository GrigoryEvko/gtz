import Mathlib
import Gtz.Core.Basic
import Gtz.Design.PrimitiveTightClassification
import Gtz.Reduction.HingeFunnel

/-!
# Theorem A: stresses of diamond-shape extensions are never full-support

Five directions in `ℝ³` realize the DIAMOND SHAPE when two three-element
circuits `{0,1,2}` and `{0,3,4}` are each coplanar, the two circuit planes are
distinct, and no two of the five directions are parallel.  We state the shape
through its operational data: a normal for each circuit plane, the vanishing
pairings of the in-plane atoms, the NON-vanishing pairings of the off-plane
atoms (this is where "planes distinct + pairwise non-parallel" bites — an atom
of one circuit lying in the other plane would sit on the intersection line,
i.e. be parallel to the shared atom), and linear independence of each
off-plane pair.

**Theorem A** (the diamond-rigidity lane's boundary theorem, formalized): for
ANY sixth direction, every stress of the six atom matrices has its support
inside one coplanar four-set — `{0,1,2,5}` or `{0,3,4,5}`.  Stated as: the
stress coefficients vanish on `{3,4}` or on `{1,2}`.  In particular no
extension of a diamond-shape family carries a full-support stress, so no such
design ever sits in the balanced stratum (branch (ii)) of
`sixThree_stress_trichotomy`: the `t_min → 0` escape of the balanced stratum
must bend OFF the diamond shape.

The proof is the five-line polarization argument: a stress annihilates every
quadratic probe, so hitting the stress identity with a plane normal kills that
plane's atoms and leaves a two- or three-term vanishing combination of the
off-plane directions; independence and the non-vanishing pairings finish.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

/-- **The polarization identity for stresses.**  A stress annihilates the whole
matrix pencil, so applying it to any probe vector turns it into a vanishing
linear combination of the atoms themselves, weighted by the probe pairings.
This is the workhorse of every support argument at every size and rank. -/
theorem stress_probe_combination_eq_zero {atomCount rank : ℕ}
    {atomFamily : Fin atomCount → Fin rank → ℝ}
    {stressCoeff : Fin atomCount → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0)
    (probe : Fin rank → ℝ) :
    ∑ c, (stressCoeff c * (atomFamily c ⬝ᵥ probe)) • atomFamily c = 0 := by
  have happlied :
      ∑ c, Matrix.mulVec (stressCoeff c • atomMatrix (atomFamily c)) probe = 0 := by
    rw [← Matrix.sum_mulVec, hstress, Matrix.zero_mulVec]
  calc ∑ c, (stressCoeff c * (atomFamily c ⬝ᵥ probe)) • atomFamily c
      = ∑ c, Matrix.mulVec (stressCoeff c • atomMatrix (atomFamily c)) probe :=
        Finset.sum_congr rfl fun c _ => (smul_atomMatrix_mulVec _ _ _).symm
    _ = 0 := happlied

section DiamondShape

variable (atomFamily : Fin 6 → Fin 3 → ℝ)
variable (planeNormalOne planeNormalTwo : Fin 3 → ℝ)

/-- **Theorem A, support form.**  Under the diamond-shape data on the first
five atoms, every stress of any six-atom extension vanishes on the off-plane
pair `{3,4}` or on the off-plane pair `{1,2}` — its support lies inside one
coplanar four-set. -/
theorem diamondExtension_stress_support
    (hsharedOne : atomFamily 0 ⬝ᵥ planeNormalOne = 0)
    (hfirstOne : atomFamily 1 ⬝ᵥ planeNormalOne = 0)
    (hsecondOne : atomFamily 2 ⬝ᵥ planeNormalOne = 0)
    (hsharedTwo : atomFamily 0 ⬝ᵥ planeNormalTwo = 0)
    (hthirdTwo : atomFamily 3 ⬝ᵥ planeNormalTwo = 0)
    (hfourthTwo : atomFamily 4 ⬝ᵥ planeNormalTwo = 0)
    (hthirdOffOne : atomFamily 3 ⬝ᵥ planeNormalOne ≠ 0)
    (hfourthOffOne : atomFamily 4 ⬝ᵥ planeNormalOne ≠ 0)
    (hfirstOffTwo : atomFamily 1 ⬝ᵥ planeNormalTwo ≠ 0)
    (hsecondOffTwo : atomFamily 2 ⬝ᵥ planeNormalTwo ≠ 0)
    (hpairTwoIndep : ∀ firstScale secondScale : ℝ,
        firstScale • atomFamily 3 + secondScale • atomFamily 4 = 0 →
        firstScale = 0 ∧ secondScale = 0)
    (hpairOneIndep : ∀ firstScale secondScale : ℝ,
        firstScale • atomFamily 1 + secondScale • atomFamily 2 = 0 →
        firstScale = 0 ∧ secondScale = 0)
    {stressCoeff : Fin 6 → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0) :
    (stressCoeff 3 = 0 ∧ stressCoeff 4 = 0)
      ∨ (stressCoeff 1 = 0 ∧ stressCoeff 2 = 0) := by
  have hpolarOne := stress_probe_combination_eq_zero hstress planeNormalOne
  rw [Fin.sum_univ_six, hsharedOne, hfirstOne, hsecondOne] at hpolarOne
  simp only [mul_zero, zero_smul, zero_add] at hpolarOne
  by_cases hextensionOne : atomFamily 5 ⬝ᵥ planeNormalOne = 0
  · -- the extension lies in plane one: the polarized identity is a vanishing
    -- combination of the two plane-two off-plane atoms alone.
    rw [hextensionOne] at hpolarOne
    simp only [mul_zero, zero_smul, add_zero] at hpolarOne
    obtain ⟨hthirdProduct, hfourthProduct⟩ := hpairTwoIndep _ _ hpolarOne
    exact Or.inl
      ⟨(mul_eq_zero.mp hthirdProduct).resolve_right hthirdOffOne,
       (mul_eq_zero.mp hfourthProduct).resolve_right hfourthOffOne⟩
  · by_cases hextensionTwo : atomFamily 5 ⬝ᵥ planeNormalTwo = 0
    · -- the extension lies in plane two: polarize at the second normal.
      have hpolarTwo := stress_probe_combination_eq_zero hstress planeNormalTwo
      rw [Fin.sum_univ_six, hsharedTwo, hthirdTwo, hfourthTwo,
        hextensionTwo] at hpolarTwo
      simp only [mul_zero, zero_smul, zero_add, add_zero] at hpolarTwo
      obtain ⟨hfirstProduct, hsecondProduct⟩ := hpairOneIndep _ _ hpolarTwo
      exact Or.inr
        ⟨(mul_eq_zero.mp hfirstProduct).resolve_right hfirstOffTwo,
         (mul_eq_zero.mp hsecondProduct).resolve_right hsecondOffTwo⟩
    · -- the extension lies in neither plane: pair the plane-one polarization
      -- against the second normal to kill the extension coefficient outright.
      have hdotted := congrArg (fun leftVec => leftVec ⬝ᵥ planeNormalTwo) hpolarOne
      simp only [add_dotProduct, smul_dotProduct, zero_dotProduct,
        smul_eq_mul] at hdotted
      rw [hthirdTwo, hfourthTwo] at hdotted
      simp only [mul_zero, zero_add] at hdotted
      have hextensionCoeff : stressCoeff 5 = 0 := by
        rcases mul_eq_zero.mp hdotted with hleftFactor | hlastPairing
        · rcases mul_eq_zero.mp hleftFactor with hcoeff | hfirstPairing
          · exact hcoeff
          · exact absurd hfirstPairing hextensionOne
        · exact absurd hlastPairing hextensionTwo
      rw [hextensionCoeff] at hpolarOne
      simp only [zero_mul, zero_smul, add_zero] at hpolarOne
      obtain ⟨hthirdProduct, hfourthProduct⟩ := hpairTwoIndep _ _ hpolarOne
      exact Or.inl
        ⟨(mul_eq_zero.mp hthirdProduct).resolve_right hthirdOffOne,
         (mul_eq_zero.mp hfourthProduct).resolve_right hfourthOffOne⟩

/-- **Theorem A, full-support form.**  No six-atom extension of a
diamond-shape family carries a full-support stress. -/
theorem diamondExtension_no_fullSupport_stress
    (hsharedOne : atomFamily 0 ⬝ᵥ planeNormalOne = 0)
    (hfirstOne : atomFamily 1 ⬝ᵥ planeNormalOne = 0)
    (hsecondOne : atomFamily 2 ⬝ᵥ planeNormalOne = 0)
    (hsharedTwo : atomFamily 0 ⬝ᵥ planeNormalTwo = 0)
    (hthirdTwo : atomFamily 3 ⬝ᵥ planeNormalTwo = 0)
    (hfourthTwo : atomFamily 4 ⬝ᵥ planeNormalTwo = 0)
    (hthirdOffOne : atomFamily 3 ⬝ᵥ planeNormalOne ≠ 0)
    (hfourthOffOne : atomFamily 4 ⬝ᵥ planeNormalOne ≠ 0)
    (hfirstOffTwo : atomFamily 1 ⬝ᵥ planeNormalTwo ≠ 0)
    (hsecondOffTwo : atomFamily 2 ⬝ᵥ planeNormalTwo ≠ 0)
    (hpairTwoIndep : ∀ firstScale secondScale : ℝ,
        firstScale • atomFamily 3 + secondScale • atomFamily 4 = 0 →
        firstScale = 0 ∧ secondScale = 0)
    (hpairOneIndep : ∀ firstScale secondScale : ℝ,
        firstScale • atomFamily 1 + secondScale • atomFamily 2 = 0 →
        firstScale = 0 ∧ secondScale = 0)
    {stressCoeff : Fin 6 → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0)
    (hfullSupport : ∀ c, stressCoeff c ≠ 0) : False := by
  rcases diamondExtension_stress_support atomFamily planeNormalOne planeNormalTwo
      hsharedOne hfirstOne hsecondOne hsharedTwo hthirdTwo hfourthTwo
      hthirdOffOne hfourthOffOne hfirstOffTwo hsecondOffTwo
      hpairTwoIndep hpairOneIndep hstress with hoffTwo | hoffOne
  · exact hfullSupport 3 hoffTwo.1
  · exact hfullSupport 1 hoffOne.1

/-- **The stratum-(ii) exclusion.**  A `(6,3)` design whose atoms extend a
diamond-shape five-family falls into branch (i) or branch (iii) of
`sixThree_stress_trichotomy` — the balanced full-support branch is
impossible.  This is the boundary theorem of the `t_min → 0` escape: exact
diamond-shape limits are never inside the balanced stratum, so the escape
path must leave the diamond shape. -/
theorem diamondExtension_stressFree_or_coplanarStress
    (design : WeightedDesign 6 3)
    (hsharedOne : design.atom 0 ⬝ᵥ planeNormalOne = 0)
    (hfirstOne : design.atom 1 ⬝ᵥ planeNormalOne = 0)
    (hsecondOne : design.atom 2 ⬝ᵥ planeNormalOne = 0)
    (hsharedTwo : design.atom 0 ⬝ᵥ planeNormalTwo = 0)
    (hthirdTwo : design.atom 3 ⬝ᵥ planeNormalTwo = 0)
    (hfourthTwo : design.atom 4 ⬝ᵥ planeNormalTwo = 0)
    (hthirdOffOne : design.atom 3 ⬝ᵥ planeNormalOne ≠ 0)
    (hfourthOffOne : design.atom 4 ⬝ᵥ planeNormalOne ≠ 0)
    (hfirstOffTwo : design.atom 1 ⬝ᵥ planeNormalTwo ≠ 0)
    (hsecondOffTwo : design.atom 2 ⬝ᵥ planeNormalTwo ≠ 0)
    (hpairTwoIndep : ∀ firstScale secondScale : ℝ,
        firstScale • design.atom 3 + secondScale • design.atom 4 = 0 →
        firstScale = 0 ∧ secondScale = 0)
    (hpairOneIndep : ∀ firstScale secondScale : ℝ,
        firstScale • design.atom 1 + secondScale • design.atom 2 = 0 →
        firstScale = 0 ∧ secondScale = 0) :
    (∀ stressCoeff : Fin 6 → ℝ,
        (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → stressCoeff = 0)
    ∨ (∃ (stressCoeff : Fin 6 → ℝ) (probe : Fin 3 → ℝ),
        stressCoeff ≠ 0 ∧ probe ≠ 0
        ∧ (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0
        ∧ ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0) := by
  rcases sixThree_stress_trichotomy design with hstressFree | hbalanced | hcoplanar
  · exact Or.inl hstressFree
  · exfalso
    obtain ⟨stressCoeff, hstress, hfullSupport, -⟩ := hbalanced
    exact diamondExtension_no_fullSupport_stress design.atom
      planeNormalOne planeNormalTwo
      hsharedOne hfirstOne hsecondOne hsharedTwo hthirdTwo hfourthTwo
      hthirdOffOne hfourthOffOne hfirstOffTwo hsecondOffTwo
      hpairTwoIndep hpairOneIndep hstress hfullSupport
  · exact Or.inr hcoplanar

end DiamondShape

end Gtz
