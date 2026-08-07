/-
# The core-tail anchor: the Parseval bookkeeping does NOT die

Attacks the ONE obligation left of route (b)'s anchor half after
`exists_strictAnchor_of_weakDominator` reduced it to weak domination:
exhibit, at each canonical-window cell, a parallel-free design with a weakly
dominating rank-subset.

The proposed shape is core-plus-tail: `rank` core atoms along an orthonormal
basis, the remaining `size - rank` atoms in general position.  Writing the core
atom on axis `index` as `sqrt coreScaleSq` times the basis vector, the core
subset's matrix is `coreScaleSq` times the identity — DIAGONAL, so weak
domination is `1 <= coreScaleSq` with no eigenvalue work at all.

The question is whether Parseval can be balanced.  It can, with room to spare,
and this file proves it: `coreTailBookkeeping_feasible`.  Two facts drive it.

1. The core weights are FORCED once the tail is fixed — `coreWeight index *
   coreScaleSq = 1 - tailShrink * tailDiagonal index` — so the only genuinely
   free scalar is the common `coreScaleSq`, pinned by the weight sum to
   `(rank - tailMoment) / (1 - tailWeight)`.
2. Shrinking the tail's weights by a single factor drives `tailMoment` and
   `tailWeight` to zero together, so `coreScaleSq` rises to `rank`.  At
   `rank >= 2` that is comfortably above the required `1`.  The explicit witness
   below takes `tailShrink = 1 / (1 + tailMass + diagonalTotal)`.

WHERE THE CONSTRUCTION ACTUALLY PINCHES — and it is NOT the weights: the core
atoms are axis-aligned, so they can only supply a DIAGONAL residual.  The
tail's weighted outer products must therefore sum to a diagonal matrix.  That
obligation, `DiagonalTailAtCell`, is DISCHARGED in `AnchorAssembly` at every
count from two up (`diagonalTailAtCell_of_two_le`, single-plane construction,
no parity split) and REFUTED at count one (`not_diagonalTailAtCell_one`), so
`2 <= extra` is the sharp guard.  The planar-pair and three-vector-block
witnesses below are the superseded block plan, kept as verified exemplars.
-/
import Gtz.Uniform.RouteBProps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz
namespace UniformPositionBridge

open Matrix Finset

/-- **A core scale at least one dominates weakly.**  The core subset's matrix is
`coreScaleSq` times the identity, so domination is the scalar inequality — this
is the "pure diagonality, no eigenvalue work" step. -/
theorem posSemidef_smul_one_sub_one {rank : ℕ} {coreScaleSq : ℝ}
    (hcoreScale : 1 ≤ coreScaleSq) :
    (coreScaleSq • (1 : Matrix (Fin rank) (Fin rank) ℝ) - 1).PosSemidef := by
  have hdiagonal : coreScaleSq • (1 : Matrix (Fin rank) (Fin rank) ℝ) - 1
      = Matrix.diagonal (fun _ : Fin rank => coreScaleSq - 1) := by
    ext leftIndex rightIndex
    by_cases hsame : leftIndex = rightIndex
    · subst hsame; simp [Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    · simp [Matrix.one_apply_ne hsame, Matrix.diagonal_apply_ne _ hsame]
  rw [hdiagonal]
  exact Matrix.posSemidef_diagonal_iff.mpr fun _ => by linarith

/-- **THE PARSEVAL BOOKKEEPING IS FEASIBLE, at every rank `>= 2`.**

Given any tail — summarised by its diagonal profile `tailDiagonal` (the diagonal
matrix its weighted outer products sum to) and its total weight `tailMass` —
there is a single shrink factor for the tail, a common core scale AT LEAST ONE,
and positive core weights, such that

  * each core weight is exactly what Parseval forces
    (`coreWeight index * coreScaleSq = 1 - tailShrink * tailDiagonal index`,
    i.e. core atom `index` supplies precisely the residual on axis `index`), and
  * all the weights sum to one.

`1 <= coreScaleSq` is what makes the core subset dominate
(`posSemidef_smul_one_sub_one`).  So the construction does NOT die on the
bookkeeping: the system is not merely solvable, it is solvable with the core
scale bounded below by roughly `rank`. -/
theorem coreTailBookkeeping_feasible {rank : ℕ} (hrank : 2 ≤ rank)
    (tailDiagonal : Fin rank → ℝ) (htailNonneg : ∀ index, 0 ≤ tailDiagonal index)
    (tailMass : ℝ) (htailMassPos : 0 < tailMass) :
    ∃ (tailShrink coreScaleSq : ℝ) (coreWeight : Fin rank → ℝ),
      0 < tailShrink ∧ 1 ≤ coreScaleSq ∧ (∀ index, 0 < coreWeight index)
        ∧ (∀ index, coreWeight index * coreScaleSq
            = 1 - tailShrink * tailDiagonal index)
        ∧ (∑ index, coreWeight index) + tailShrink * tailMass = 1 := by
  classical
  set diagonalTotal : ℝ := ∑ index, tailDiagonal index with hdiagonalTotalDef
  have hdiagonalTotalNonneg : 0 ≤ diagonalTotal :=
    Finset.sum_nonneg fun index _ => htailNonneg index
  set bound : ℝ := 1 + tailMass + diagonalTotal with hboundDef
  have hboundPos : 0 < bound := by rw [hboundDef]; linarith
  set tailShrink : ℝ := 1 / bound with hshrinkDef
  have hshrinkPos : 0 < tailShrink := by rw [hshrinkDef]; positivity
  have hshrinkMassLt : tailShrink * tailMass < 1 := by
    rw [hshrinkDef, div_mul_eq_mul_div, one_mul, div_lt_one hboundPos, hboundDef]
    linarith
  have hshrinkMassPos : 0 < tailShrink * tailMass := mul_pos hshrinkPos htailMassPos
  have hshrinkDiagonalLt : tailShrink * diagonalTotal < 1 := by
    rw [hshrinkDef, div_mul_eq_mul_div, one_mul, div_lt_one hboundPos, hboundDef]
    linarith
  have hshrinkDiagonalNonneg : 0 ≤ tailShrink * diagonalTotal :=
    mul_nonneg hshrinkPos.le hdiagonalTotalNonneg
  have hrankReal : (2 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
  set residualMass : ℝ := 1 - tailShrink * tailMass with hresidualMassDef
  have hresidualMassPos : 0 < residualMass := by rw [hresidualMassDef]; linarith
  set coreScaleSq : ℝ := ((rank : ℝ) - tailShrink * diagonalTotal) / residualMass
    with hcoreScaleDef
  have hnumeratorGeOne : 1 ≤ (rank : ℝ) - tailShrink * diagonalTotal := by linarith
  have hcoreScaleGeOne : 1 ≤ coreScaleSq := by
    rw [hcoreScaleDef, le_div_iff₀ hresidualMassPos, one_mul, hresidualMassDef]
    linarith
  have hcoreScalePos : 0 < coreScaleSq := by linarith
  refine ⟨tailShrink, coreScaleSq,
    fun index => (1 - tailShrink * tailDiagonal index) / coreScaleSq,
    hshrinkPos, hcoreScaleGeOne, ?_, ?_, ?_⟩
  · intro index
    have hdiagonalLe : tailDiagonal index ≤ diagonalTotal :=
      Finset.single_le_sum (fun other _ => htailNonneg other) (Finset.mem_univ index)
    have hshrinkEntryLt : tailShrink * tailDiagonal index < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hdiagonalLe hshrinkPos.le) hshrinkDiagonalLt
    exact div_pos (by linarith) hcoreScalePos
  · intro index
    rw [div_mul_cancel₀ _ (ne_of_gt hcoreScalePos)]
  · have hsumNumerator : ∑ index, (1 - tailShrink * tailDiagonal index)
        = (rank : ℝ) - tailShrink * diagonalTotal := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hdiagonalTotalDef,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hnumeratorNe : ((rank : ℝ) - tailShrink * diagonalTotal) ≠ 0 := by linarith
    rw [← Finset.sum_div, hsumNumerator, hcoreScaleDef, div_div_eq_mul_div,
      mul_comm ((rank : ℝ) - tailShrink * diagonalTotal) residualMass,
      mul_div_assoc, div_self hnumeratorNe, mul_one, hresidualMassDef]
    ring

/-- **The core-tail anchor's remaining obligation, named.**  A tail at a cell:
`extra` vectors, pairwise non-parallel, none of them axis-parallel (so no tail
atom is parallel to a core atom), whose weighted outer products sum to a
DIAGONAL matrix.  Everything else in the core-tail construction is discharged —
the weights by `coreTailBookkeeping_feasible`, the domination by
`posSemidef_smul_one_sub_one`.

Diagonality is the binding constraint, and it is DISCHARGED in `AnchorAssembly`
at every `2 <= extra` and every `2 <= rank` (`diagonalTailAtCell_of_two_le`):
every tail atom sits in the SAME coordinate 2-plane, so diagonality is one
scalar cancellation and no count analysis is needed.  The predicate is FALSE at
`extra = 1` (`not_diagonalTailAtCell_one`) — a single outer product is diagonal
only for an axis-parallel vector, which the axis clause forbids — so
`2 <= extra` is the sharp guard, and the window supplies it for free since
`extra = size - rank >= rank` there. -/
def DiagonalTailAtCell (extra rank : ℕ) : Prop :=
  ∃ (tailAtom : Fin extra → (Fin rank → ℝ)) (tailWeight : Fin extra → ℝ)
    (tailDiagonal : Fin rank → ℝ),
    (∀ slot, 0 < tailWeight slot)
      ∧ (∀ slot, 0 ≤ tailDiagonal slot)
      ∧ (∑ slot, tailWeight slot • atomMatrix (tailAtom slot))
          = Matrix.diagonal tailDiagonal
      ∧ (∀ slot (axis : Fin rank) (ratio : ℝ),
          tailAtom slot ≠ ratio • (fun coord => if coord = axis then (1 : ℝ) else 0))
      ∧ (∀ (leftSlot rightSlot : Fin extra) (ratio : ℝ), leftSlot ≠ rightSlot →
          tailAtom leftSlot ≠ ratio • tailAtom rightSlot)

/-- SUPERSEDED by the single-plane construction in `AnchorAssembly`
(`diagonalTailAtCell_of_two_le`); kept as a verified exemplar of the block
plan.  The three-vector block that absorbs an ODD tail count: `(1,1,1)`,
`(1,-1,-1)`, `(0,2,-1)` have outer products summing to `diagonal (2, 6, 3)`.
None is axis-parallel and no two are parallel, so this is a legitimate tail
block wherever `rank >= 3`. -/
theorem oddTailBlock_sums_diagonal :
    atomMatrix ![(1 : ℝ), 1, 1] + atomMatrix ![(1 : ℝ), -1, -1]
        + atomMatrix ![(0 : ℝ), 2, -1]
      = Matrix.diagonal ![(2 : ℝ), 6, 3] := by
  ext leftIndex rightIndex
  fin_cases leftIndex <;> fin_cases rightIndex <;>
    simp [atomMatrix, Matrix.vecMulVec, Matrix.diagonal] <;> norm_num

/-- SUPERSEDED by the single-plane construction in `AnchorAssembly`
(`diagonalTailAtCell_of_two_le`); kept as a verified exemplar of the block
plan.  The planar pair that absorbs an EVEN tail step, at the representative
plane: `(1, c)` and `(1, -c)` have outer products summing to
`diagonal (2, 2 c^2)`.  Both are off both axes for `c` nonzero, and they are
non-parallel to each other. -/
theorem evenTailPair_sums_diagonal (offAxis : ℝ) :
    atomMatrix ![(1 : ℝ), offAxis] + atomMatrix ![(1 : ℝ), -offAxis]
      = Matrix.diagonal ![(2 : ℝ), 2 * offAxis ^ 2] := by
  ext leftIndex rightIndex
  fin_cases leftIndex <;> fin_cases rightIndex <;>
    simp [atomMatrix, Matrix.vecMulVec, Matrix.diagonal] <;> ring

end UniformPositionBridge
end Gtz
