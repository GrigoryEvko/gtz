import Gtz.Wave.SixSetCorner
import Gtz.Wave.SixSetDowndate
import Gtz.Wave.CorankTwoNonplanarDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The four-set core is a 2×2 condition on the six-set ghost block

The non-planar corner closes from the four-set core
(`Gtz.corankTwoNonplanar_absurd_of_core`), whose inverse-free producer
(`Gtz.nonplanarFourSetCore_of_swapPD`) asks for positive definiteness of the
two SWAP matrices `B_e − g_f g_fᵀ`.  This module prices those swaps in the
six-set metric and finds them to be plain depth-two downdates of `W`:

  `B_e − g_f g_fᵀ = W − (√2 g_f)(√2 g_f)ᵀ − g_h g_hᵀ` ,

because the four-set gap `B_e = W − g_f g_fᵀ − g_h g_hᵀ` already carries one
copy of the ghost atom.  The depth-two dictionary
(`Gtz.posDef_sub_two_vecMulVec_iff`) then reads the swap through the ghost
2×2 block of the six-set pivot matrix alone:

  `2·P_ff < 1` and `2·P_fh² < (1 − 2 P_ff)(1 − P_hh)` .

The residual of the whole non-planar corner is thereby reduced to a
statement about ONE symmetric 2×2 matrix of six-set pivots
(`Gtz.GhostBlockShort`): both ghost pivots are below one half and their
off-diagonal is controlled.  `Gtz.corankTwoNonplanar_absurd_of_ghostBlock`
closes the corner from it.

The reduction is exact — no inverse of a four-set gap appears — and the
ghost block is a block of the rank-three co-weighted projection of
`Gtz.pivot_coweight_projection`, so the residual lives entirely in the
projection calculus.  The four-set needs the complement triple, so nothing
here can be stated at `(5,3)`.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-- The six-set pivot `P_{ab} = g_aᵀ W⁻¹ g_b` of a pair of labels. -/
noncomputable def sixSetPivot (D : WeightedDesign m 3) (a b : Fin m) : ℝ :=
  D.atom a ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom b)

/-- The pivot matrix is symmetric. -/
theorem sixSetPivot_comm (D : WeightedDesign m 3) (a b : Fin m) :
    sixSetPivot D a b = sixSetPivot D b a := by
  have hWsymm : (subsetSum D Finset.univ - 1)ᵀ = subsetSum D Finset.univ - 1 :=
    transpose_subsetSum_sub_one D Finset.univ
  have hWinvsymm : ((subsetSum D Finset.univ - 1)⁻¹)ᵀ
      = (subsetSum D Finset.univ - 1)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hWsymm]
  exact dot_mulVec_comm hWinvsymm _ _

/-- **The four-set gap is the six-set gap downdated by the ghost pair.** -/
theorem fourSetGap_eq_sixSet_downdate (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) {e f h : Fin 6} (he : e ∈ C) (hfh : f ≠ h)
    (herase : C.erase e = {f, h}) :
    subsetSum D (insert e Cᶜ) - 1
      = (subsetSum D Finset.univ - 1)
        - Matrix.vecMulVec (D.atom f) (D.atom f)
        - Matrix.vecMulVec (D.atom h) (D.atom h) := by
  classical
  have hcompl : insert e Cᶜ = (C.erase e)ᶜ := by
    rw [← compl_insert_compl C he, compl_compl]
  have hdown := tripleGap_eq_sixSet_downdate D (C.erase e)
  rw [← hcompl] at hdown
  rw [hdown, herase, Finset.sum_insert (by simp [hfh]), Finset.sum_singleton,
    atomMatrix, atomMatrix]
  abel

/-- **The swap matrix is a depth-two downdate of the six-set gap.**  The
swap at the ghost `f` removes the atom `√2 g_f` and the atom `g_h`. -/
theorem swap_eq_sixSet_downdate (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) {e f h : Fin 6} (he : e ∈ C) (hfh : f ≠ h)
    (herase : C.erase e = {f, h}) :
    (subsetSum D (insert e Cᶜ) - 1)
        - Matrix.vecMulVec (D.atom f) (D.atom f)
      = (subsetSum D Finset.univ - 1)
        - Matrix.vecMulVec (Real.sqrt 2 • D.atom f) (Real.sqrt 2 • D.atom f)
        - Matrix.vecMulVec (D.atom h) (D.atom h) := by
  have hdouble : Matrix.vecMulVec (Real.sqrt 2 • D.atom f)
        (Real.sqrt 2 • D.atom f)
      = (2 : ℝ) • Matrix.vecMulVec (D.atom f) (D.atom f) := by
    rw [show Matrix.vecMulVec (Real.sqrt 2 • D.atom f) (Real.sqrt 2 • D.atom f)
        = atomMatrix (Real.sqrt 2 • D.atom f) from rfl, atomMatrix_smul,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rfl
  rw [fourSetGap_eq_sixSet_downdate D C he hfh herase, hdouble, two_smul]
  abel

/-- **The swap reads the ghost block.**  The swap at `f` is positive
definite exactly when the doubled ghost pivot is below one and the
off-diagonal obeys the Sylvester bound. -/
theorem swapPD_iff_ghostBlock (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) {e f h : Fin 6} (he : e ∈ C) (hfh : f ≠ h)
    (herase : C.erase e = {f, h})
    (hPD : (subsetSum D Finset.univ - 1).PosDef) :
    ((subsetSum D (insert e Cᶜ) - 1)
        - Matrix.vecMulVec (D.atom f) (D.atom f)).PosDef
      ↔ 2 * sixSetPivot D f f < 1
        ∧ 2 * sixSetPivot D f h ^ 2
            < (1 - 2 * sixSetPivot D f f) * (1 - sixSetPivot D h h) := by
  have hreadsq : Real.sqrt 2 • D.atom f
      ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ (Real.sqrt 2 • D.atom f))
      = 2 * sixSetPivot D f f := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2),
      sixSetPivot]
  have hreadcross : Real.sqrt 2 • D.atom f
      ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom h)
      = Real.sqrt 2 * sixSetPivot D f h := by
    rw [smul_dotProduct, smul_eq_mul, sixSetPivot]
  rw [swap_eq_sixSet_downdate D C he hfh herase,
    posDef_sub_two_vecMulVec_iff _ hPD, hreadsq, hreadcross,
    show (Real.sqrt 2 * sixSetPivot D f h) ^ 2 = 2 * sixSetPivot D f h ^ 2 from by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)],
    show D.atom h ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom h)
      = sixSetPivot D h h from rfl]

/-- **The ghost block is short.**  Both ghost pivots of the six-set metric
sit below one half, and their off-diagonal obeys both Sylvester bounds of
the doubled block. -/
def GhostBlockShort (D : WeightedDesign 6 3) (f h : Fin 6) : Prop :=
  2 * sixSetPivot D f f < 1 ∧ 2 * sixSetPivot D h h < 1
    ∧ 2 * sixSetPivot D f h ^ 2
        < (1 - 2 * sixSetPivot D f f) * (1 - sixSetPivot D h h)
    ∧ 2 * sixSetPivot D f h ^ 2
        < (1 - 2 * sixSetPivot D h h) * (1 - sixSetPivot D f f)

/-- **The core from the ghost block.**  A short ghost block produces the
four-set core at the inside atom it leaves out. -/
theorem nonplanarFourSetCore_of_ghostBlockShort (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {e f h : Fin 6} (he : e ∈ C)
    (hfh : f ≠ h) (herase : C.erase e = {f, h})
    (hPD : (subsetSum D Finset.univ - 1).PosDef)
    (hshort : GhostBlockShort D f h) :
    NonplanarFourSetCore D C := by
  classical
  obtain ⟨hf2, hh2, hcf, hch⟩ := hshort
  have herase' : C.erase e = {h, f} := by
    rw [herase, Finset.pair_comm]
  refine nonplanarFourSetCore_of_swapPD D C hcard he ?_
  intro g hg
  rw [herase] at hg
  simp only [Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl
  · exact (swapPD_iff_ghostBlock D C he hfh herase hPD).mpr ⟨hf2, hcf⟩
  · refine (swapPD_iff_ghostBlock D C he (Ne.symm hfh) herase' hPD).mpr
      ⟨hh2, ?_⟩
    rw [sixSetPivot_comm D g f]
    exact hch

/-- **The non-planar corner closes from a short ghost block.**  A `(6,3)`
tie whose dominator carries a positive definite six-set gap and an inside
atom whose ghost pair has a short block is impossible. -/
theorem corankTwoNonplanar_absurd_of_ghostBlock (D : WeightedDesign 6 3)
    (htie : IsTie D) (C : Finset (Fin 6)) (hcard : C.card = 3)
    {e f h : Fin 6} (he : e ∈ C) (hfh : f ≠ h) (herase : C.erase e = {f, h})
    (hPD : (subsetSum D Finset.univ - 1).PosDef)
    (hshort : GhostBlockShort D f h) : False :=
  corankTwoNonplanar_absurd_of_core D htie C hcard
    (nonplanarFourSetCore_of_ghostBlockShort D C hcard he hfh herase hPD hshort)

end Gtz
