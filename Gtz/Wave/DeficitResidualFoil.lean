import Gtz.Wave.TiePivotCensus
import Gtz.Wave.CorankTwoNonplanarFixture

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# The tie hypothesis of the deficit residual is necessary, and the residual is
the corner emptiness from both sides

`Gtz.NonplanarDeficitResidual` carries a tie hypothesis and a primitivity
hypothesis.  Two questions decide whether that shape is right.

**Can the conclusion be reached at a tie?**  No.  `Gtz.not_ghostDeficitShort_of_isTie`
shows that the refusal ledger of a pair forbids a ghost-deficient pair at every
`(6,3)` tie, so the residual holds exactly when the corner is empty
(`Gtz.nonplanarDeficitResidual_iff_no_corner`).

**Can the tie hypothesis be dropped?**  No.  This module states the residual
without it (`Gtz.UnconditionalNonplanarDeficitResidual`) and refutes it at the
LANDED rational fixture `Gtz.corankTwoNonplanarDesign`
(`Gtz.not_unconditionalNonplanarDeficitResidual`).  The fixture inhabits a
non-planar corank-two corner exactly — `S_{0,1,2} − 1 = 3 • atomMatrix ![0,0,1]`
and the atom `5` reads the gap direction at one — and none of its three inside
pairs is deficient:

* the pair `{0,1}` has pair minor `−1720/15039 < 0`, so it is inadmissible;
* the pair `{0,2}` has deficit form `215723/2105460 > 0`;
* the pair `{1,2}` has deficit form `52609/526365 > 0`.

The six-set gap of the fixture is the integer matrix
`!![30, −26, 5; −26, 41, −6; 5, −6, 4]` of determinant `1671`, and its inverse is
`(1/1671) • !![128, 74, −49; 74, 95, 50; −49, 50, 554]`, so every pivot above is
an exact rational and every comparison is a `norm_num` step.

The landed foil `Gtz.residualFoil` does NOT settle this question: it refutes the
SHORT BLOCK residual `Gtz.NonplanarGhostResidual`, while its own pair `{0,1}`
IS deficient, so it leaves the weighted surface untouched.  The fixture is the
first witness on the weighted surface.

Together the two halves pin the residual exactly: its hypotheses cannot be
weakened and its conclusion cannot be produced, so `corankTwoGap_absurd'` can be
discharged only by emptying the corner.
-/

namespace Gtz

open Matrix Finset

namespace DeficitFoil

/-- The six-set gap of the non-planar fixture, in closed form. -/
noncomputable def gapMat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![30, -26, 5; -26, 41, -6; 5, -6, 4]

/-- The inverse of the six-set gap of the non-planar fixture, in closed form. -/
noncomputable def gapInvMat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![128/1671, 74/1671, -(49/1671);
     74/1671, 95/1671, 50/1671;
     -(49/1671), 50/1671, 554/1671]

end DeficitFoil

open DeficitFoil

/-! ## 1. The closed forms of the fixture -/

/-- The six-set gap of the non-planar fixture. -/
theorem corankTwoNonplanar_gapMat :
    subsetSum corankTwoNonplanarDesign Finset.univ - 1 = gapMat := by
  rw [subsetSum, Fin.sum_univ_six]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [corankTwoNonplanarDesign, corankTwoNonplanarAtom, atomMatrix,
      Matrix.vecMulVec_apply, Matrix.one_apply, gapMat] <;>
    norm_num

/-- The inverse of the six-set gap of the non-planar fixture. -/
theorem corankTwoNonplanar_gapInv :
    (subsetSum corankTwoNonplanarDesign Finset.univ - 1)⁻¹ = gapInvMat := by
  rw [corankTwoNonplanar_gapMat]
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gapMat, gapInvMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
    norm_num

/-! ## 2. The inside pivot block of the fixture -/

/-- The pivot of a pair of fixture atoms, read through the closed-form inverse. -/
theorem corankTwoNonplanar_pivot (a b : Fin 6) :
    sixSetPivot corankTwoNonplanarDesign a b
      = corankTwoNonplanarAtom a ⬝ᵥ (gapInvMat *ᵥ corankTwoNonplanarAtom b) := by
  rw [sixSetPivot, corankTwoNonplanar_gapInv]
  rfl

theorem corankTwoNonplanar_pivot_zero_zero :
    sixSetPivot corankTwoNonplanarDesign 0 0 = 9260 / 15039 := by
  rw [corankTwoNonplanar_pivot]
  simp [corankTwoNonplanarAtom, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  norm_num

theorem corankTwoNonplanar_pivot_one_one :
    sixSetPivot corankTwoNonplanarDesign 1 1 = 9383 / 15039 := by
  rw [corankTwoNonplanar_pivot]
  simp [corankTwoNonplanarAtom, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  norm_num

theorem corankTwoNonplanar_pivot_two_two :
    sixSetPivot corankTwoNonplanarDesign 2 2 = 3308 / 15039 := by
  rw [corankTwoNonplanar_pivot]
  simp [corankTwoNonplanarAtom, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  norm_num

theorem corankTwoNonplanar_pivot_zero_one :
    sixSetPivot corankTwoNonplanarDesign 0 1 = -(7652 / 15039) := by
  rw [corankTwoNonplanar_pivot]
  simp [corankTwoNonplanarAtom, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  norm_num

theorem corankTwoNonplanar_pivot_zero_two :
    sixSetPivot corankTwoNonplanarDesign 0 2 = 5146 / 15039 := by
  rw [corankTwoNonplanar_pivot]
  simp [corankTwoNonplanarAtom, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  norm_num

theorem corankTwoNonplanar_pivot_one_two :
    sixSetPivot corankTwoNonplanarDesign 1 2 = -(4954 / 15039) := by
  rw [corankTwoNonplanar_pivot]
  simp [corankTwoNonplanarAtom, gapInvMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  norm_num

/-! ## 3. No inside pair of the fixture is deficient -/

/-- The deficit is symmetric in the pair. -/
theorem ghostDeficitShort_comm (D : WeightedDesign 6 3) {f h : Fin 6}
    (hdef : GhostDeficitShort D f h) : GhostDeficitShort D h f := by
  obtain ⟨ha, hb, hdet, hbr⟩ := hdef
  have hc : sixSetPivot D h f = sixSetPivot D f h := sixSetPivot_comm D h f
  refine ⟨hb, ha, ?_, ?_⟩ <;> rw [hc]
  · nlinarith [hdet]
  · linarith [hbr]

/-- The pair `{0,1}` of the fixture is inadmissible: its pair minor is negative. -/
theorem corankTwoNonplanar_not_deficient_zero_one :
    ¬ GhostDeficitShort corankTwoNonplanarDesign 0 1 := by
  rintro ⟨-, -, hdet, -⟩
  rw [corankTwoNonplanar_pivot_zero_zero, corankTwoNonplanar_pivot_one_one,
    corankTwoNonplanar_pivot_zero_one] at hdet
  norm_num at hdet

/-- The pair `{0,2}` of the fixture has a positive deficit form. -/
theorem corankTwoNonplanar_not_deficient_zero_two :
    ¬ GhostDeficitShort corankTwoNonplanarDesign 0 2 := by
  rintro ⟨-, -, -, hbr⟩
  rw [corankTwoNonplanar_pivot_zero_zero, corankTwoNonplanar_pivot_two_two,
    corankTwoNonplanar_pivot_zero_two, corankTwoNonplanarDesign_weight] at hbr
  simp only [corankTwoNonplanarWeight] at hbr
  norm_num at hbr

/-- The pair `{1,2}` of the fixture has a positive deficit form. -/
theorem corankTwoNonplanar_not_deficient_one_two :
    ¬ GhostDeficitShort corankTwoNonplanarDesign 1 2 := by
  rintro ⟨-, -, -, hbr⟩
  rw [corankTwoNonplanar_pivot_one_one, corankTwoNonplanar_pivot_two_two,
    corankTwoNonplanar_pivot_one_two, corankTwoNonplanarDesign_weight] at hbr
  simp only [corankTwoNonplanarWeight] at hbr
  norm_num at hbr

/-! ## 4. The residual without the tie -/

/-- **The deficit residual with the tie hypothesis dropped.**  It asks for a
ghost-deficient pair at every non-planar corank-two corner of every design. -/
def UnconditionalNonplanarDeficitResidual (D : WeightedDesign 6 3) : Prop :=
  ∀ C : Finset (Fin 6), C.card = 3 → ∀ lam : ℝ, 0 < lam → ∀ u : Fin 3 → ℝ,
    u ⬝ᵥ u = 1 → subsetSum D C - 1 = lam • atomMatrix u →
    (∃ d ∈ Cᶜ, D.atom d ⬝ᵥ u ≠ 0) →
    ∃ e ∈ C, ∃ f h : Fin 6, f ≠ h ∧ C.erase e = {f, h} ∧ GhostDeficitShort D f h

/-- **The tie hypothesis cannot be dropped.**  The landed rational fixture
inhabits a non-planar corank-two corner and carries no deficient inside pair. -/
theorem not_unconditionalNonplanarDeficitResidual :
    ¬ UnconditionalNonplanarDeficitResidual corankTwoNonplanarDesign := by
  classical
  intro hres
  have hcard : ({0, 1, 2} : Finset (Fin 6)).card = 3 := by decide
  have hunit : (![0, 0, 1] : Fin 3 → ℝ) ⬝ᵥ ![0, 0, 1] = 1 := by
    simp [dotProduct, Fin.sum_univ_three]
  have hnp : ∃ d ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ,
      corankTwoNonplanarDesign.atom d ⬝ᵥ (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 :=
    ⟨5, corankTwoNonplanar_offPlane_mem, by
      rw [corankTwoNonplanar_offPlane_witness]; norm_num⟩
  obtain ⟨e, he, f, h, hfh, herase, hdef⟩ :=
    hres ({0, 1, 2} : Finset (Fin 6)) hcard 3 (by norm_num) ![0, 0, 1] hunit
      corankTwoNonplanarDesign_gap hnp
  have hcase : e = 0 ∨ e = 1 ∨ e = 2 := by
    have := he
    fin_cases this <;> simp
  -- in each case the erased pair is explicit, so `f` and `h` are pinned
  have hpair : ∀ a b : Fin 6, ({0, 1, 2} : Finset (Fin 6)).erase e = {a, b} → a ≠ b →
      (f = a ∧ h = b) ∨ (f = b ∧ h = a) := by
    intro a b hab _
    have hfm : f ∈ ({a, b} : Finset (Fin 6)) := by rw [← hab, herase]; simp
    have hhm : h ∈ ({a, b} : Finset (Fin 6)) := by rw [← hab, herase]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfm hhm
    rcases hfm with rfl | rfl <;> rcases hhm with rfl | rfl <;> simp_all
  rcases hcase with rfl | rfl | rfl
  · have h12 : ({0, 1, 2} : Finset (Fin 6)).erase 0 = {1, 2} := by decide
    rcases hpair 1 2 h12 (by decide) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact corankTwoNonplanar_not_deficient_one_two hdef
    · exact corankTwoNonplanar_not_deficient_one_two (ghostDeficitShort_comm _ hdef)
  · have h02 : ({0, 1, 2} : Finset (Fin 6)).erase 1 = {0, 2} := by decide
    rcases hpair 0 2 h02 (by decide) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact corankTwoNonplanar_not_deficient_zero_two hdef
    · exact corankTwoNonplanar_not_deficient_zero_two (ghostDeficitShort_comm _ hdef)
  · have h01 : ({0, 1, 2} : Finset (Fin 6)).erase 2 = {0, 1} := by decide
    rcases hpair 0 1 h01 (by decide) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact corankTwoNonplanar_not_deficient_zero_one hdef
    · exact corankTwoNonplanar_not_deficient_zero_one (ghostDeficitShort_comm _ hdef)

/-- **The residual is pinned from both sides.**  Dropping the tie makes the
statement false, and keeping it makes the conclusion unreachable, so the residual
carries exactly the emptiness of the corner and nothing else. -/
theorem deficitResidual_two_sided :
    (¬ ∀ D : WeightedDesign 6 3, UnconditionalNonplanarDeficitResidual D)
      ∧ (∀ D : WeightedDesign 6 3, IsTie D → ∀ f h : Fin 6, f ≠ h →
          ¬ GhostDeficitShort D f h) :=
  ⟨fun hall => not_unconditionalNonplanarDeficitResidual (hall _),
   fun D htie f h hfh => not_ghostDeficitShort_of_isTie D htie hfh⟩

end Gtz
