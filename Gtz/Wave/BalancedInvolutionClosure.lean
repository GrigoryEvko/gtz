import Gtz.Quantitative.EqualShareSixThreeMargin
import Gtz.Wave.BalancedCutSelection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The balanced Wave target is already an abstract U6 theorem

The Wave presentation starts from six rows `atom : Fin 6 → Fin 3 → ℝ` with
orthonormal columns and balanced row mass `1/2`.  Its open-looking target
`AtomBalancedDetWin` asks for a principal triple of the row Gram above the
one-sixth diagonal.

The older quantitative presentation has already proved a stronger theorem:
every hollow symmetric involution on six coordinates has a principal triple
whose block, shifted by `2/3`, is positive semidefinite.  The two presentations
are the same object.  If `G` is the row Gram, then

    H = 2 G - I,

and the frame and balance laws say exactly that `H` is a hollow symmetric
involution.  On a triple,

    (2/3) I + H[T] = 2 (G[T] - (1/6) I).

This module lands that missing bridge.  It discharges the full balanced
determinant target, hence also the strict-subcritical residual, and carries the
result through the Wave spectral and carrier interfaces.  No numerical
certificate and no new proposition are needed.
-/

namespace Gtz

open Matrix

/-! ## 1. The balanced frame involution -/

/-- The index Gram as an actual matrix.  `atomGram` is kept as the entry API in
the Wave files; this wrapper lets the already-landed involution algebra consume
it without changing coordinates. -/
noncomputable def balancedAtomGramMatrix
    (atom : Fin 6 → (Fin 3 → ℝ)) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun rowIndex colIndex => atomGram atom rowIndex colIndex

@[simp]
theorem balancedAtomGramMatrix_apply (atom : Fin 6 → (Fin 3 → ℝ))
    (rowIndex colIndex : Fin 6) :
    balancedAtomGramMatrix atom rowIndex colIndex = atomGram atom rowIndex colIndex :=
  rfl

/-- The frame law is precisely idempotence of the index Gram. -/
theorem balancedAtomGramMatrix_mul_self
    {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction))
        = probe ⬝ᵥ direction) :
    balancedAtomGramMatrix atom * balancedAtomGramMatrix atom
      = balancedAtomGramMatrix atom := by
  ext rowIndex colIndex
  simpa only [Matrix.mul_apply, balancedAtomGramMatrix_apply] using
    atomGram_idempotent hframe rowIndex colIndex

/-- The balanced frame involution `H = 2G - I`. -/
noncomputable def balancedAtomInvolution
    (atom : Fin 6 → (Fin 3 → ℝ)) : Matrix (Fin 6) (Fin 6) ℝ :=
  (2 : ℝ) • balancedAtomGramMatrix atom - 1

theorem balancedAtomInvolution_apply (atom : Fin 6 → (Fin 3 → ℝ))
    (rowIndex colIndex : Fin 6) :
    balancedAtomInvolution atom rowIndex colIndex
      = 2 * atomGram atom rowIndex colIndex - if rowIndex = colIndex then 1 else 0 := by
  simp [balancedAtomInvolution, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]

/-- `2G-I` is a hollow symmetric involution whenever `G` is the Gram of a
balanced six-by-three Parseval frame. -/
theorem isHollowInvolution_balancedAtomInvolution
    {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction))
        = probe ⬝ᵥ direction)
    (hbal : ∀ slot : Fin 6, atomGram atom slot slot = 1 / 2) :
    IsHollowInvolution (balancedAtomInvolution atom) where
  symmetric := by
    ext rowIndex colIndex
    rw [Matrix.transpose_apply, balancedAtomInvolution_apply,
      balancedAtomInvolution_apply, atomGram_comm]
    by_cases h : rowIndex = colIndex
    · simp [h]
    · simp [h, Ne.symm h]
  square_eq_one := by
    have hgram := balancedAtomGramMatrix_mul_self hframe
    rw [balancedAtomInvolution, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_smul, hgram]
    module
  diagonal_eq_zero := by
    intro slot
    rw [balancedAtomInvolution_apply, hbal]
    norm_num

/-! ## 2. The abstract U6 block is the Wave shifted block -/

/-- On a selected triple the abstract involution shift is exactly twice the
Wave one-sixth Gram shift. -/
theorem twoThirds_one_add_balancedAtomInvolution_submatrix
    (atom : Fin 6 → (Fin 3 → ℝ))
    (first second third : Fin 6)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    (2 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + (balancedAtomInvolution atom).submatrix
            ![first, second, third] ![first, second, third]
      = (2 : ℝ) • atomShiftBlockMatrix atom first second third := by
  ext rowIndex colIndex
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.submatrix_apply, balancedAtomInvolution_apply,
    Matrix.smul_apply, atomShiftBlockMatrix_apply]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [hfirstSecond, hfirstThird, hsecondThird, Ne.symm hfirstSecond,
      Ne.symm hfirstThird, Ne.symm hsecondThird] <;> ring

/-- The older abstract-U6 theorem supplies a positive semidefinite Wave block,
not merely a nonnegative determinant. -/
theorem exists_atomShiftBlockMatrix_posSemidef_of_balanced
    (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction))
        = probe ⬝ᵥ direction)
    (hbal : ∀ slot : Fin 6, atomGram atom slot slot = 1 / 2) :
    ∃ first second third : Fin 6,
      first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
        (atomShiftBlockMatrix atom first second third).PosSemidef := by
  let invol := balancedAtomInvolution atom
  have hinvol : IsHollowInvolution invol :=
    isHollowInvolution_balancedAtomInvolution hframe hbal
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hpsd⟩ :=
    hinvol.exists_posSemidef_twoThirds_shift
  have hshape := twoThirds_one_add_balancedAtomInvolution_submatrix atom
    first second third hfirstSecond hfirstThird hsecondThird
  have hscaled : ((2 : ℝ) • atomShiftBlockMatrix atom first second third).PosSemidef := by
    rw [← hshape]
    exact hpsd
  have hback := hscaled.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [smul_smul] at hback
  norm_num at hback
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hback⟩

/-! ## 3. The balanced targets and their consumers are closed -/

/-- **THE BALANCED DETERMINANT TARGET, UNCONDITIONALLY.** -/
theorem atomBalancedDetWin_holds : AtomBalancedDetWin := by
  intro atom hframe hbal
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hpsd⟩ :=
    exists_atomShiftBlockMatrix_posSemidef_of_balanced atom hframe hbal
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
  rw [← atomShiftBlockMatrix_det]
  exact hpsd.det_nonneg

/-- The strict-subcritical target is a restriction of the now-unconditional
balanced target, so its edge hypothesis is unnecessary. -/
theorem atomBalancedSubcriticalDetWin_holds : AtomBalancedSubcriticalDetWin := by
  intro atom hframe hbal _hsubcritical
  exact atomBalancedDetWin_holds atom hframe hbal

/-- Every balanced frame has the Wave's sharp one-sixth blend floor. -/
theorem exists_atomBlendFloor_sixth_of_balanced
    (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction))
        = probe ⬝ᵥ direction)
    (hbal : ∀ slot : Fin 6, atomGram atom slot slot = 1 / 2) :
    ∃ first second third : Fin 6,
      first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
        AtomBlendFloor atom first second third (1 / 6) :=
  exists_atomBlendFloor_sixth_of_balancedDetWin
    atomBalancedDetWin_holds atom hframe hbal

/-- **THE BALANCED LIGHT CELL, UNCONDITIONALLY.**  At arbitrary positive scales
bounded by one sixth, the triple supplied by abstract U6 is an actual carrier.
This is the left arm that `DescentWeld` previously obtained only in the
heavy-edge region. -/
theorem exists_atomCarrier_of_balanced_sixth
    (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction))
        = probe ⬝ᵥ direction)
    (hbal : ∀ slot : Fin 6, atomGram atom slot slot = 1 / 2)
    (hscale : ∀ slot, scale slot ≤ 1 / 6) :
    ∃ carrier : Finset (Fin 6), carrier.card = 3 ∧
      ∀ probe : Fin 6 → ℝ, (∀ slot ∉ carrier, probe slot = 0) →
        (∑ slot, scale slot * probe slot ^ 2)
          ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hfloor⟩ :=
    exists_atomBlendFloor_sixth_of_balanced atom hframe hbal
  exact exists_atomCarrier_of_blendFloor atom scale hfirstSecond hfirstThird hsecondThird
    hfloor hscale

end Gtz
