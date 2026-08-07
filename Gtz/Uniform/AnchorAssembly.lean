/-
# Closing the anchor: the diagonal tail, assembled

Works the obligation `DiagonalTailAtCell` left open by `AnchorBookkeeping`:
an indexed family of `extra` tail atoms, pairwise non-parallel, none
axis-parallel, whose weighted outer products sum to a DIAGONAL matrix.

A SIMPLIFICATION over the block plan sketched in `DiagonalTailAtCell`'s
docstring.  That plan placed a planar pair in each of several coordinate
2-planes and used a three-atom block to absorb an odd count -- which needs
block decomposition and a parity split.  Neither is necessary.  Put EVERY
tail atom in the SAME coordinate 2-plane:

    tailAtomVec c = basis 0 + c * basis 1

Then the tail sum is supported on the top-left two-by-two block, its only
off-diagonal entry is `sum of (weight * coeff)`, and diagonality is the single
scalar equation `sum of (weight * coeff) = 0`.  Distinct nonzero coefficients
make the atoms pairwise non-parallel, and each atom has TWO nonzero coordinates
so none is axis-parallel.  No blocks, no parity split, no case analysis on the
count -- one formula for every `extra >= 2`.

The coefficients: slot `castSucc i` carries `i + 1` with weight `1 / (i + 1)`,
and the final slot carries `-1` with weight `tailCount`.  Every non-final slot
contributes exactly `+1` to `sum of (weight * coeff)` and the final slot
contributes `-tailCount`, so the sum telescopes to zero with no Gauss identity.
-/
import Gtz.Uniform.AnchorBookkeeping

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz
namespace UniformPositionBridge

open Matrix Finset

/-! ## The coefficient family -/

/-- Tail coefficients: the final slot carries `-1`, slot `castSucc i` carries
`i + 1`.  All distinct, all nonzero. -/
noncomputable def tailCoeff (tailCount : ℕ) : Fin (tailCount + 1) → ℝ :=
  Fin.lastCases (-1) (fun index => ((index : ℕ) : ℝ) + 1)

/-- Tail weights, chosen so that every non-final slot contributes exactly `+1`
to the off-diagonal sum and the final slot cancels all of them at once. -/
noncomputable def tailRawWeight (tailCount : ℕ) : Fin (tailCount + 1) → ℝ :=
  Fin.lastCases (tailCount : ℝ) (fun index => 1 / (((index : ℕ) : ℝ) + 1))

@[simp] theorem tailCoeff_last (tailCount : ℕ) :
    tailCoeff tailCount (Fin.last tailCount) = -1 := by
  rw [tailCoeff, Fin.lastCases_last]

@[simp] theorem tailCoeff_castSucc (tailCount : ℕ) (index : Fin tailCount) :
    tailCoeff tailCount index.castSucc = ((index : ℕ) : ℝ) + 1 := by
  rw [tailCoeff, Fin.lastCases_castSucc]

@[simp] theorem tailRawWeight_last (tailCount : ℕ) :
    tailRawWeight tailCount (Fin.last tailCount) = (tailCount : ℝ) := by
  rw [tailRawWeight, Fin.lastCases_last]

@[simp] theorem tailRawWeight_castSucc (tailCount : ℕ) (index : Fin tailCount) :
    tailRawWeight tailCount index.castSucc = 1 / (((index : ℕ) : ℝ) + 1) := by
  rw [tailRawWeight, Fin.lastCases_castSucc]

theorem tailRawWeight_pos {tailCount : ℕ} (hcount : 1 ≤ tailCount)
    (slot : Fin (tailCount + 1)) : 0 < tailRawWeight tailCount slot := by
  refine Fin.lastCases ?_ ?_ slot
  · rw [tailRawWeight_last]
    exact_mod_cast hcount
  · intro index
    rw [tailRawWeight_castSucc]
    positivity

theorem tailCoeff_ne_zero (tailCount : ℕ) (slot : Fin (tailCount + 1)) :
    tailCoeff tailCount slot ≠ 0 := by
  refine Fin.lastCases ?_ ?_ slot
  · rw [tailCoeff_last]; norm_num
  · intro index
    rw [tailCoeff_castSucc]
    positivity

/-- The coefficients are pairwise distinct: the non-final ones are the distinct
positive integers, and the final one is the only negative value. -/
theorem tailCoeff_injective (tailCount : ℕ) :
    Function.Injective (tailCoeff tailCount) := by
  intro leftSlot rightSlot hequal
  obtain ⟨leftIndex, rfl⟩ | rfl := leftSlot.eq_castSucc_or_eq_last <;>
    obtain ⟨rightIndex, rfl⟩ | rfl := rightSlot.eq_castSucc_or_eq_last
  · rw [tailCoeff_castSucc, tailCoeff_castSucc] at hequal
    have hnat : (leftIndex : ℕ) = (rightIndex : ℕ) := by
      have hreal : ((leftIndex : ℕ) : ℝ) = ((rightIndex : ℕ) : ℝ) := by linarith
      exact_mod_cast hreal
    exact congrArg Fin.castSucc (Fin.ext hnat)
  · rw [tailCoeff_castSucc, tailCoeff_last] at hequal
    have hpos : (0 : ℝ) < ((leftIndex : ℕ) : ℝ) + 1 := by positivity
    linarith
  · rw [tailCoeff_last, tailCoeff_castSucc] at hequal
    have hpos : (0 : ℝ) < ((rightIndex : ℕ) : ℝ) + 1 := by positivity
    linarith
  · rfl

/-- **THE DIAGONALITY EQUATION.**  The weighted coefficients cancel: every
non-final slot contributes exactly `+1`, the final slot contributes
`-tailCount`.  No Gauss identity is used. -/
theorem sum_tailRawWeight_mul_tailCoeff (tailCount : ℕ) :
    ∑ slot, tailRawWeight tailCount slot * tailCoeff tailCount slot = 0 := by
  rw [Fin.sum_univ_castSucc]
  have hterm : ∀ index : Fin tailCount,
      tailRawWeight tailCount index.castSucc * tailCoeff tailCount index.castSucc = 1 := by
    intro index
    rw [tailRawWeight_castSucc, tailCoeff_castSucc]
    have hne : ((index : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl fun index _ => hterm index, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    tailRawWeight_last, tailCoeff_last]
  ring

/-! ## The atom shapes -/

/-- A tail atom: `basis 0 + coeff * basis 1`, written by underlying index so no
`Fin` literals are needed at general rank. -/
def tailAtomVec {rank : ℕ} (coeff : ℝ) : Fin rank → ℝ :=
  fun coord => if (coord : ℕ) = 0 then 1 else if (coord : ℕ) = 1 then coeff else 0

/-- A core atom: `sqrt coreScaleSq` along one axis. -/
noncomputable def coreAtomVec {rank : ℕ} (coreScaleSq : ℝ) (axis : Fin rank) :
    Fin rank → ℝ :=
  fun coord => if coord = axis then Real.sqrt coreScaleSq else 0

/-- The tail atom's leading coordinate is one. -/
theorem tailAtomVec_apply_zero {rank : ℕ} (hrank : 2 ≤ rank) (coeff : ℝ) :
    tailAtomVec (rank := rank) coeff ⟨0, by omega⟩ = 1 := by
  simp [tailAtomVec]

/-- The tail atom's second coordinate is its coefficient. -/
theorem tailAtomVec_apply_one {rank : ℕ} (hrank : 2 ≤ rank) (coeff : ℝ) :
    tailAtomVec (rank := rank) coeff ⟨1, by omega⟩ = coeff := by
  simp [tailAtomVec]

theorem coreAtomVec_apply {rank : ℕ} (coreScaleSq : ℝ) (axis coord : Fin rank) :
    coreAtomVec coreScaleSq axis coord
      = if coord = axis then Real.sqrt coreScaleSq else 0 := rfl

/-- Every tail atom has TWO nonzero coordinates, so it is parallel to no axis
vector -- in particular to no core atom. -/
theorem tailAtomVec_ne_smul_coreAtomVec {rank : ℕ} (hrank : 2 ≤ rank) {coeff : ℝ}
    (hcoeff : coeff ≠ 0) {coreScaleSq : ℝ} (axis : Fin rank) (ratio : ℝ) :
    tailAtomVec (rank := rank) coeff ≠ ratio • coreAtomVec coreScaleSq axis := by
  intro hequal
  have hatZero := congrFun hequal ⟨0, by omega⟩
  have hatOne := congrFun hequal ⟨1, by omega⟩
  rw [tailAtomVec_apply_zero hrank] at hatZero
  rw [tailAtomVec_apply_one hrank] at hatOne
  by_cases hzeroAxis : (⟨0, by omega⟩ : Fin rank) = axis
  · have honeAxis : (⟨1, by omega⟩ : Fin rank) ≠ axis := by
      rw [← hzeroAxis]
      intro hcontra
      exact absurd (congrArg Fin.val hcontra) (by norm_num)
    rw [Pi.smul_apply, coreAtomVec_apply, if_neg honeAxis, smul_eq_mul, mul_zero] at hatOne
    exact hcoeff hatOne
  · rw [Pi.smul_apply, coreAtomVec_apply, if_neg hzeroAxis, smul_eq_mul, mul_zero] at hatZero
    exact absurd hatZero one_ne_zero

/-- Distinct coefficients give non-parallel tail atoms: the leading coordinate
pins the ratio to one. -/
theorem tailAtomVec_ne_smul_tailAtomVec {rank : ℕ} (hrank : 2 ≤ rank)
    {leftCoeff rightCoeff : ℝ} (hdistinct : leftCoeff ≠ rightCoeff) (ratio : ℝ) :
    tailAtomVec (rank := rank) leftCoeff ≠ ratio • tailAtomVec rightCoeff := by
  intro hequal
  have hatZero := congrFun hequal ⟨0, by omega⟩
  have hatOne := congrFun hequal ⟨1, by omega⟩
  rw [tailAtomVec_apply_zero hrank, Pi.smul_apply, tailAtomVec_apply_zero hrank,
    smul_eq_mul, mul_one] at hatZero
  rw [tailAtomVec_apply_one hrank, Pi.smul_apply, tailAtomVec_apply_one hrank,
    smul_eq_mul, ← hatZero, one_mul] at hatOne
  exact hdistinct hatOne

/-- Distinct axes give non-parallel core atoms. -/
theorem coreAtomVec_ne_smul_coreAtomVec {rank : ℕ} {coreScaleSq : ℝ}
    (hscalePos : 0 < coreScaleSq) {leftAxis rightAxis : Fin rank}
    (hdistinct : leftAxis ≠ rightAxis) (ratio : ℝ) :
    coreAtomVec coreScaleSq leftAxis ≠ ratio • coreAtomVec coreScaleSq rightAxis := by
  intro hequal
  have hatLeft := congrFun hequal leftAxis
  rw [coreAtomVec_apply, if_pos rfl, Pi.smul_apply, coreAtomVec_apply,
    if_neg hdistinct, smul_eq_mul, mul_zero] at hatLeft
  exact absurd hatLeft (ne_of_gt (Real.sqrt_pos.mpr hscalePos))

/-! ## The two diagonal sums

The core atoms sum to a diagonal matrix because each is supported on one axis;
the tail atoms sum to a diagonal matrix because their only off-diagonal entry is
the weighted coefficient sum, which `sum_tailRawWeight_mul_tailCoeff` kills. -/

/-- The axis indicator vector. -/
def axisVec {rank : ℕ} (axis : Fin rank) : Fin rank → ℝ :=
  fun coord => if coord = axis then 1 else 0

theorem coreAtomVec_eq_smul {rank : ℕ} (coreScaleSq : ℝ) (axis : Fin rank) :
    coreAtomVec coreScaleSq axis = Real.sqrt coreScaleSq • axisVec axis := by
  funext coord
  simp only [coreAtomVec, axisVec, Pi.smul_apply, smul_eq_mul]
  split <;> ring

/-- Axis atoms sum to the diagonal of their scales. -/
theorem sum_axis_atomMatrix {rank : ℕ} (scale : Fin rank → ℝ) :
    (∑ axis, scale axis • atomMatrix (axisVec axis)) = Matrix.diagonal scale := by
  ext leftIndex rightIndex
  rw [Matrix.sum_apply, Matrix.diagonal_apply]
  have hterm : ∀ axis : Fin rank,
      (scale axis • atomMatrix (axisVec axis)) leftIndex rightIndex
        = if axis = leftIndex then (if leftIndex = rightIndex then scale axis else 0)
          else 0 := by
    intro axis
    simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, axisVec,
      smul_eq_mul]
    by_cases hleft : leftIndex = axis
    · subst hleft
      by_cases hright : rightIndex = leftIndex
      · subst hright; simp
      · simp [hright, Ne.symm hright]
    · simp [hleft, Ne.symm hleft]
  rw [Finset.sum_congr rfl fun axis _ => hterm axis, Finset.sum_ite_eq']
  by_cases hsame : leftIndex = rightIndex
  · subst hsame; simp
  · simp [hsame]

/-- **The core block is diagonal**: each core atom carries `coreScaleSq` on its
own axis and nothing elsewhere. -/
theorem sum_core_atomMatrix {rank : ℕ} {coreScaleSq : ℝ}
    (hscaleNonneg : 0 ≤ coreScaleSq) (coreWeight : Fin rank → ℝ) :
    (∑ axis, coreWeight axis • atomMatrix (coreAtomVec coreScaleSq axis))
      = Matrix.diagonal (fun axis => coreWeight axis * coreScaleSq) := by
  have hrewrite : ∀ axis : Fin rank,
      coreWeight axis • atomMatrix (coreAtomVec coreScaleSq axis)
        = (coreWeight axis * coreScaleSq) • atomMatrix (axisVec axis) := by
    intro axis
    rw [coreAtomVec_eq_smul, atomMatrix_smul, Real.sq_sqrt hscaleNonneg, smul_smul]
  rw [Finset.sum_congr rfl fun axis _ => hrewrite axis, sum_axis_atomMatrix]

/-- The diagonal profile of the tail block: the leading axis carries the total
tail weight, the second axis carries the weighted squared coefficients, and
every other axis carries nothing. -/
noncomputable def tailDiagonalProfile (rank tailCount : ℕ) : Fin rank → ℝ :=
  fun coord =>
    if (coord : ℕ) = 0 then ∑ slot, tailRawWeight tailCount slot
    else if (coord : ℕ) = 1 then
      ∑ slot, tailRawWeight tailCount slot * tailCoeff tailCount slot ^ 2
    else 0

theorem tailDiagonalProfile_nonneg {rank tailCount : ℕ} (hcount : 1 ≤ tailCount)
    (coord : Fin rank) : 0 ≤ tailDiagonalProfile rank tailCount coord := by
  rw [tailDiagonalProfile]
  split
  · exact Finset.sum_nonneg fun slot _ => (tailRawWeight_pos hcount slot).le
  · split
    · exact Finset.sum_nonneg fun slot _ =>
        mul_nonneg (tailRawWeight_pos hcount slot).le (sq_nonneg _)
    · exact le_refl 0

/-- Pointwise value of a tail atom. -/
theorem tailAtomVec_apply {rank : ℕ} (coeff : ℝ) (coord : Fin rank) :
    tailAtomVec coeff coord
      = if (coord : ℕ) = 0 then 1 else if (coord : ℕ) = 1 then coeff else 0 := rfl

/-! ### The tail block's diagonality, as a matrix identity

The nine-way case split this file once recorded as blocked: each matrix entry
of the weighted tail sum is decided by the underlying indices of its two
coordinates, and the single cancellation `sum of (weight * coeff) = 0` kills
both off-diagonal survivors at `(0,1)` and `(1,0)`.  Proved at GENERAL rank and
GENERAL slot count, for ANY coefficient and weight families satisfying the
cancellation -- the named `tailCoeff`/`tailRawWeight` family is one instance. -/

/-- **The diagonality identity.**  Tail atoms all in the same coordinate
2-plane: one scalar cancellation makes their weighted outer products sum to a
diagonal matrix, at every rank and every slot count. -/
theorem sum_tail_atomMatrix {rank extra : ℕ} (coeff weight : Fin extra → ℝ)
    (hcancel : ∑ slot, weight slot * coeff slot = 0) :
    (∑ slot, weight slot • atomMatrix (tailAtomVec (rank := rank) (coeff slot)))
      = Matrix.diagonal (fun coord : Fin rank =>
          if (coord : ℕ) = 0 then ∑ slot, weight slot
          else if (coord : ℕ) = 1 then ∑ slot, weight slot * coeff slot ^ 2
          else 0) := by
  ext rowIndex colIndex
  simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
    smul_eq_mul, Matrix.diagonal_apply, tailAtomVec]
  by_cases hrowZero : (rowIndex : ℕ) = 0
  · by_cases hcolZero : (colIndex : ℕ) = 0
    · have hsame : rowIndex = colIndex := Fin.ext (by omega)
      simp [hcolZero, hsame]
    · by_cases hcolOne : (colIndex : ℕ) = 1
      · have hdiffer : rowIndex ≠ colIndex := fun heq => hcolZero (heq ▸ hrowZero)
        simpa [hrowZero, hcolZero, hcolOne, hdiffer] using hcancel
      · have hdiffer : rowIndex ≠ colIndex := fun heq => hcolZero (heq ▸ hrowZero)
        simp [hrowZero, hcolZero, hcolOne, hdiffer]
  · by_cases hrowOne : (rowIndex : ℕ) = 1
    · by_cases hcolZero : (colIndex : ℕ) = 0
      · have hdiffer : rowIndex ≠ colIndex := fun heq => hrowZero (heq ▸ hcolZero)
        simpa [hrowZero, hrowOne, hcolZero, hdiffer, mul_comm] using hcancel
      · by_cases hcolOne : (colIndex : ℕ) = 1
        · have hsame : rowIndex = colIndex := Fin.ext (by omega)
          simp [hcolOne, hsame, sq]
        · have hdiffer : rowIndex ≠ colIndex := fun heq => hcolOne (heq ▸ hrowOne)
          simp [hrowOne, hcolZero, hcolOne, hdiffer]
    · by_cases hsame : rowIndex = colIndex
      · subst hsame
        simp [hrowZero, hrowOne]
      · simp [hrowZero, hrowOne, hsame]

/-- **The tail block is diagonal** -- the identity this file once self-declared
unproved, at the named coefficient and weight families.  The diagonal is
exactly `tailDiagonalProfile`, definitionally. -/
theorem sum_tailRawWeight_atomMatrix (rank tailCount : ℕ) :
    (∑ slot, tailRawWeight tailCount slot •
        atomMatrix (tailAtomVec (rank := rank) (tailCoeff tailCount slot)))
      = Matrix.diagonal (tailDiagonalProfile rank tailCount) :=
  sum_tail_atomMatrix (tailCoeff tailCount) (tailRawWeight tailCount)
    (sum_tailRawWeight_mul_tailCoeff tailCount)

/-- The axis clause of `DiagonalTailAtCell`, against the bare axis indicator:
a tail atom with nonzero coefficient has TWO nonzero coordinates, so it is
parallel to no axis. -/
theorem tailAtomVec_ne_smul_axisVec {rank : ℕ} (hrank : 2 ≤ rank) {coeff : ℝ}
    (hcoeff : coeff ≠ 0) (axis : Fin rank) (ratio : ℝ) :
    tailAtomVec (rank := rank) coeff
      ≠ ratio • (fun coord : Fin rank => if coord = axis then (1 : ℝ) else 0) := by
  intro hparallel
  by_cases haxisIsZero : axis = (⟨0, by omega⟩ : Fin rank)
  · have hatOne := congrFun hparallel ⟨1, by omega⟩
    rw [tailAtomVec_apply_one hrank] at hatOne
    have honeNeAxis : (⟨1, by omega⟩ : Fin rank) ≠ axis := by
      rw [haxisIsZero]
      exact fun hcollide => absurd (congrArg Fin.val hcollide) (by norm_num)
    simp [honeNeAxis] at hatOne
    exact hcoeff hatOne
  · have hatZero := congrFun hparallel ⟨0, by omega⟩
    rw [tailAtomVec_apply_zero hrank] at hatZero
    have hzeroNeAxis : (⟨0, by omega⟩ : Fin rank) ≠ axis :=
      fun hcollide => haxisIsZero hcollide.symm
    simp [hzeroNeAxis] at hatZero

/-! ### The obligation, discharged at every count from two up -/

/-- **`DiagonalTailAtCell` holds at every `2 <= extra` and every `2 <= rank`.**
No parity split, no block decomposition, no `rank >= 3`: the single-plane
family with the telescoping cancellation does every count at once.  The guard
`2 <= extra` is SHARP -- see `not_diagonalTailAtCell_one` -- and the sharp
window supplies it for free, since `extra = size - rank >= rank` there. -/
theorem diagonalTailAtCell_of_two_le {extra rank : ℕ} (hextra : 2 ≤ extra)
    (hrank : 2 ≤ rank) : DiagonalTailAtCell extra rank := by
  obtain ⟨tailCount, rfl⟩ : ∃ tailCount, extra = tailCount + 1 := ⟨extra - 1, by omega⟩
  have hcount : 1 ≤ tailCount := by omega
  refine ⟨fun slot => tailAtomVec (tailCoeff tailCount slot), tailRawWeight tailCount,
    tailDiagonalProfile rank tailCount, tailRawWeight_pos hcount,
    tailDiagonalProfile_nonneg hcount, sum_tailRawWeight_atomMatrix rank tailCount,
    ?_, ?_⟩
  · intro slot axis ratio
    exact tailAtomVec_ne_smul_axisVec hrank (tailCoeff_ne_zero tailCount slot) axis ratio
  · intro leftSlot rightSlot ratio hdifferent
    exact tailAtomVec_ne_smul_tailAtomVec hrank
      (fun hequal => hdifferent (tailCoeff_injective tailCount hequal)) ratio

/-! ### And refuted at count one -/

/-- **A single tail vector cannot work**: its outer product is diagonal only if
at most one coordinate is nonzero, i.e. only if it is axis-parallel -- which
the obligation's axis clause forbids.  So `2 <= extra` is the correct guard and
any `1 <= extra` strengthening is refutable. -/
theorem not_diagonalTailAtCell_one {rank : ℕ} (hrank : 1 ≤ rank) :
    ¬ DiagonalTailAtCell 1 rank := by
  classical
  rintro ⟨tailAtom, tailWeight, tailDiagonal, hweightPos, _, hsum, hnotAxisParallel, _⟩
  have hentry : ∀ rowIndex colIndex : Fin rank, rowIndex ≠ colIndex →
      tailWeight 0 * (tailAtom 0 rowIndex * tailAtom 0 colIndex) = 0 := by
    intro rowIndex colIndex hdifferent
    have hpointwise := congrFun (congrFun hsum rowIndex) colIndex
    simpa [Fin.sum_univ_one, atomMatrix, Matrix.vecMulVec_apply, Matrix.diagonal_apply,
      hdifferent] using hpointwise
  have hproductZero : ∀ rowIndex colIndex : Fin rank, rowIndex ≠ colIndex →
      tailAtom 0 rowIndex * tailAtom 0 colIndex = 0 := by
    intro rowIndex colIndex hdifferent
    have := hentry rowIndex colIndex hdifferent
    rcases mul_eq_zero.mp this with hweightZero | hproduct
    · exact absurd hweightZero (ne_of_gt (hweightPos 0))
    · exact hproduct
  by_cases hallZero : ∀ coord : Fin rank, tailAtom 0 coord = 0
  · refine hnotAxisParallel 0 ⟨0, by omega⟩ 0 (funext fun coord => ?_)
    simp [hallZero coord]
  · obtain ⟨axis, haxisNonzero⟩ := not_forall.mp hallZero
    refine hnotAxisParallel 0 axis (tailAtom 0 axis) (funext fun coord => ?_)
    by_cases hcoordIsAxis : coord = axis
    · simp [hcoordIsAxis]
    · have := hproductZero coord axis hcoordIsAxis
      rcases mul_eq_zero.mp this with hcoordZero | hcontradiction
      · simp [hcoordIsAxis, hcoordZero]
      · exact absurd hcontradiction haxisNonzero

/-! ### The honest residual

With the tail block diagonal (`diagonalTailAtCell_of_two_le`), the core block
diagonal (`sum_core_atomMatrix`), the weights feasible
(`coreTailBookkeeping_feasible`) and the domination free
(`posSemidef_smul_one_sub_one`), what remains of route (b)'s anchor half is
pure ASSEMBLY: reindex the core and tail families along
`Fin size ≃ Fin rank ⊕ Fin (size - rank)`, check Parseval for the combined
family, and package the result as the weak parallel-free dominator that
`windowAnchorReachFree_of_weakWitness` consumes.  Nothing mathematical is
open in that step; it is bookkeeping over the equivalence, recorded here
rather than claimed. -/

end UniformPositionBridge
end Gtz
