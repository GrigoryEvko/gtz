import Gtz.Design.StressFreeMatroidStratification
import Gtz.Design.LinePatternSixCasesTwo
import Gtz.Design.StratumEmptinessLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The five-class split of the stress-free hinge: non-vacuity and losslessness

Two kernel facts about `Gtz.StressFreeHingeHoldsSixThree` that the split of the
rank-three obligation into its five matroid classes rests on.

**Non-vacuity.**  The stress-free `(6,3)` stratum -- designs whose six rank-one
atom matrices are a BASIS of the six-dimensional space of symmetric
three-by-three matrices -- is INHABITED.  The witness is the six
coordinate-plane diagonals `(1,±1,0)`, `(1,0,±1)`, `(0,1,±1)`, scaled so the
uniform weight `1/6` resolves the identity.  Summing and differencing within
each sign pair produces the three off-diagonal symmetrisers and the three
pairwise diagonal sums, and those six span.  So the hinge is not a theorem in
disguise about an empty domain.  Geometrically the six diagonals are the edge
directions of a regular tetrahedron: exactly four dependent triples, one per
face, so the witness realizes the `M(K4)` line pattern -- consistent with
`Gtz.stratumIsStressFree_graphicKFour`, and a concrete inhabitant for that
class in particular.

**Losslessness.**  Tie-freeness of the five residual classes of
`Gtz.stressFreeResidualFamiliesSix` is EQUIVALENT to the hinge, not merely
sufficient: the hinge implies `Gtz.StressFreeStratumIsTieFree` at EVERY
pattern, because its tie-emptiness reading
(`Gtz.stressFreeHingeHoldsSixThree_iff_no_stressFree_tie`) carries no pattern
hypothesis at all.  So each class obligation is strictly weaker than the hinge
and their conjunction is exactly it -- the split loses nothing.
-/

namespace Gtz

open Matrix

/-! ## The witness -/

/-- The common scale.  Each pattern vector has squared length two, so the
uniform weight `1/6` resolves the identity exactly when the squared scale is
`3/2`. -/
noncomputable def diagonalScale : ℝ := Real.sqrt (3 / 2)

theorem diagonalScale_sq : diagonalScale * diagonalScale = 3 / 2 :=
  Real.mul_self_sqrt (by norm_num)

/-- The six coordinate-plane diagonals -- equivalently, the six edge directions
of a regular tetrahedron -- as sign patterns. -/
def diagonalPattern : Fin 6 → Fin 3 → ℝ :=
  ![![1, 1, 0], ![1, -1, 0], ![1, 0, 1], ![1, 0, -1], ![0, 1, 1], ![0, 1, -1]]

/-! Per-label evaluation.  Without these the outer `Fin 6` index survives `simp`
eta-expansion of the vector literal's tail and the six scalar equations never
become numeric. -/

@[local simp] theorem diagonalPattern_zero : diagonalPattern 0 = ![1, 1, 0] := rfl
@[local simp] theorem diagonalPattern_one : diagonalPattern 1 = ![1, -1, 0] := rfl
@[local simp] theorem diagonalPattern_two : diagonalPattern 2 = ![1, 0, 1] := rfl
@[local simp] theorem diagonalPattern_three : diagonalPattern 3 = ![1, 0, -1] := rfl
@[local simp] theorem diagonalPattern_four : diagonalPattern 4 = ![0, 1, 1] := rfl
@[local simp] theorem diagonalPattern_five : diagonalPattern 5 = ![0, 1, -1] := rfl

/-- The atoms: the sign patterns at the common scale. -/
noncomputable def diagonalAtom (atomLabel : Fin 6) : Fin 3 → ℝ :=
  fun coordinate => diagonalScale * diagonalPattern atomLabel coordinate

/-- **A `(6,3)` design on the six coordinate-plane diagonals.** -/
noncomputable def coordinateDiagonalDesign : WeightedDesign 6 3 where
  atom := diagonalAtom
  weight := fun _ => 1 / 6
  weight_pos := by intro _; norm_num
  weight_sum_one := by simp
  isParseval := by
    ext rowIndex columnIndex
    have hscale := diagonalScale_sq
    fin_cases rowIndex <;> fin_cases columnIndex <;>
      simp [Fin.sum_univ_six, atomMatrix, Matrix.vecMulVec, diagonalAtom,
        diagonalPattern] <;> nlinarith [hscale]

/-! ## Stress-freeness

A stress is a linear dependence among the six atom matrices.  Reading the six
independent entries of the vanishing sum gives six scalar equations that force
every coefficient to zero. -/

/-- Each atom matrix entry, in closed rational form: the irrational scale enters
only through its square. -/
theorem coordinateDiagonalDesign_atomMatrix_entry
    (atomLabel : Fin 6) (rowIndex columnIndex : Fin 3) :
    atomMatrix (coordinateDiagonalDesign.atom atomLabel) rowIndex columnIndex
      = 3 / 2 * (diagonalPattern atomLabel rowIndex * diagonalPattern atomLabel columnIndex) := by
  show diagonalAtom atomLabel rowIndex * diagonalAtom atomLabel columnIndex = _
  simp only [diagonalAtom]
  have hregroup :
      diagonalScale * diagonalPattern atomLabel rowIndex *
          (diagonalScale * diagonalPattern atomLabel columnIndex)
        = diagonalScale * diagonalScale *
          (diagonalPattern atomLabel rowIndex * diagonalPattern atomLabel columnIndex) := by
    ring
  rw [hregroup, diagonalScale_sq]

/-- **The witness is STRESS-FREE**: its six atom matrices are linearly
independent, hence a basis of the symmetric three-by-three matrices. -/
theorem coordinateDiagonalDesign_isStressFree :
    ∀ stress : Fin 6 → ℝ,
      (∑ atomLabel, stress atomLabel • atomMatrix (coordinateDiagonalDesign.atom atomLabel)) = 0 →
        stress = 0 := by
  intro stress hvanishes
  have hentry : ∀ rowIndex columnIndex : Fin 3,
      (∑ atomLabel, stress atomLabel *
        (3 / 2 * (diagonalPattern atomLabel rowIndex
          * diagonalPattern atomLabel columnIndex))) = 0 := by
    intro rowIndex columnIndex
    have hpointwise := congrFun (congrFun hvanishes rowIndex) columnIndex
    simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      coordinateDiagonalDesign_atomMatrix_entry] using hpointwise
  have hoffOneTwo := hentry 0 1
  have hoffOneThree := hentry 0 2
  have hoffTwoThree := hentry 1 2
  have hdiagOne := hentry 0 0
  have hdiagTwo := hentry 1 1
  have hdiagThree := hentry 2 2
  simp only [Fin.sum_univ_six, diagonalPattern_zero, diagonalPattern_one, diagonalPattern_two,
    diagonalPattern_three, diagonalPattern_four, diagonalPattern_five] at hoffOneTwo hoffOneThree hoffTwoThree hdiagOne hdiagTwo hdiagThree
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hoffOneTwo hoffOneThree hoffTwoThree hdiagOne hdiagTwo hdiagThree
  -- The six equations now read: the sign pairs are equal, and the three pairwise
  -- diagonal sums vanish.  That forces every coefficient to zero.
  have hzero : stress 0 = 0 := by linarith
  have hone : stress 1 = 0 := by linarith
  have htwo : stress 2 = 0 := by linarith
  have hthree : stress 3 = 0 := by linarith
  have hfour : stress 4 = 0 := by linarith
  have hfive : stress 5 = 0 := by linarith
  funext atomLabel
  fin_cases atomLabel <;> simp only [Pi.zero_apply] <;> assumption

/-- **The stress-free `(6,3)` stratum is inhabited**, so
`Gtz.StressFreeHingeHoldsSixThree` quantifies over a nonempty domain and cannot
be vacuously true. -/
theorem stressFreeStratumSixThreeIsInhabited :
    ∃ design : WeightedDesign 6 3,
      ∀ stress : Fin 6 → ℝ,
        (∑ atomLabel, stress atomLabel • atomMatrix (design.atom atomLabel)) = 0 →
          stress = 0 :=
  ⟨coordinateDiagonalDesign, coordinateDiagonalDesign_isStressFree⟩

/-- The witness is also parallel-free, as `Gtz.isPrimitiveDesign_of_stressFree`
forces for every member of the stratum. -/
theorem coordinateDiagonalDesign_hasNoParallelPair :
    ¬ HasParallelPair coordinateDiagonalDesign :=
  (isPrimitiveDesign_iff_not_hasParallelPair coordinateDiagonalDesign).mp
    (isPrimitiveDesign_of_stressFree coordinateDiagonalDesign
      coordinateDiagonalDesign_isStressFree)

/-! ## The five-class split is lossless -/

/-- The hinge implies the class obligation at EVERY line pattern: its
tie-emptiness reading carries no pattern hypothesis, so no class assumes
anything the hinge does not already give. -/
theorem stressFreeStratumIsTieFree_of_stressFreeHinge
    (hinge : StressFreeHingeHoldsSixThree) (pattern : LinePattern 6) :
    StressFreeStratumIsTieFree pattern :=
  fun design _relabel hstressFree _hpattern =>
    stressFreeHingeHoldsSixThree_iff_no_stressFree_tie.mp hinge design hstressFree

/-- **The five-class split is an equivalence.**  Forward is the enumeration
route (`stressFreeHingeHoldsSixThree_of_residualFamilies` with the completeness
premise discharged by `linearSpaceListIsComplete_six`); backward is the
pattern-free tie-emptiness reading.  Discharging the classes one by one loses
nothing and every class discharge is genuine progress on the hinge. -/
theorem stressFreeResidualFamilies_tieFree_iff_stressFreeHinge :
    (∀ lines ∈ stressFreeResidualFamiliesSix,
        StressFreeStratumIsTieFree (lineFamilyPattern lines))
      ↔ StressFreeHingeHoldsSixThree := by
  constructor
  · intro hclasses
    exact stressFreeHingeHoldsSixThree_of_residualFamilies
      linearSpaceListIsComplete_six hclasses
  · intro hinge lines _
    exact stressFreeStratumIsTieFree_of_stressFreeHinge hinge _

end Gtz
