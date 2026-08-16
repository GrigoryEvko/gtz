/-
# The share cap of branch (i) is not uniform

`Gtz.atomShare_lt_one_of_stressFree` caps every atom share of a stress-free
`(6,3)` design strictly below one.  This module shows that the cap admits no
uniform defect.  The family `Gtz.tiltedDesign` carries one pole atom and five
atoms of a plane that a parameter lifts out of that plane.  The pole share is
`1 - tilt^2/3`, and the family stays stress-free at every parameter value that
the two hypotheses admit.

At the parameter value zero the five lifted atoms fall back into one plane, and
the six directions acquire a conic.  That conic is the product of the plane of
the five atoms with a plane through the pole.  The approach to share one is an
approach to that conic, so the closure of branch (i) meets the share-one locus.
Nothing here decides branch (i).
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.StressFreeStratum
import Gtz.Reduction.BranchTransferConstants

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Finset Matrix

/-- The height of the pole atom. -/
noncomputable def tiltHeight (tilt : ℝ) : ℝ := Real.sqrt ((3 - tilt ^ 2) / 2)

theorem tiltHeight_sq (tilt : ℝ) (hsmall : tilt ^ 2 < 3) :
    tiltHeight tilt ^ 2 = (3 - tilt ^ 2) / 2 :=
  Real.sq_sqrt (by linarith)

theorem tiltHeight_ne_zero (tilt : ℝ) (hsmall : tilt ^ 2 < 3) : tiltHeight tilt ≠ 0 := by
  have hsq : tiltHeight tilt ^ 2 = (3 - tilt ^ 2) / 2 := tiltHeight_sq tilt hsmall
  intro hzero
  rw [hzero] at hsq
  linarith [hsq]

/-- One pole atom and five atoms that the parameter lifts out of a plane. -/
noncomputable def tiltedAtoms (tilt : ℝ) : Fin 6 → Fin 3 → ℝ :=
  ![![0, 0, tiltHeight tilt],
    ![2, 0, tilt],
    ![0, 2, tilt],
    ![-2, -2, tilt],
    ![2, -2, tilt],
    ![-2, 2, tilt]]

/-- The weights that resolve the identity against `Gtz.tiltedAtoms`. -/
noncomputable def tiltedWeights : Fin 6 → ℝ := ![2 / 3, 1 / 12, 1 / 12, 1 / 12, 1 / 24, 1 / 24]

theorem tiltedWeights_pos : ∀ label, 0 < tiltedWeights label := by
  intro label
  fin_cases label <;> norm_num [tiltedWeights]

theorem sum_tiltedWeights : ∑ label, tiltedWeights label = 1 := by
  simp [tiltedWeights, Fin.sum_univ_six]
  norm_num

theorem tiltedAtoms_isParseval (tilt : ℝ) (hsmall : tilt ^ 2 < 3) :
    ∑ label, tiltedWeights label • atomMatrix (tiltedAtoms tilt label) = 1 := by
  have hz2 : tiltHeight tilt ^ 2 = (3 - tilt ^ 2) / 2 := tiltHeight_sq tilt hsmall
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply, Fin.sum_univ_six,
      tiltedAtoms, tiltedWeights] <;>
    linarith [hz2]

/-- The tilted family, as a weighted design. -/
noncomputable def tiltedDesign (tilt : ℝ) (hpos : 0 < tilt) (hsmall : tilt ^ 2 < 3) :
    WeightedDesign 6 3 where
  atom := tiltedAtoms tilt
  weight := tiltedWeights
  weight_pos := tiltedWeights_pos
  weight_sum_one := sum_tiltedWeights
  isParseval := tiltedAtoms_isParseval tilt hsmall

theorem tiltedDesign_atom (tilt : ℝ) (hpos : 0 < tilt) (hsmall : tilt ^ 2 < 3) :
    (tiltedDesign tilt hpos hsmall).atom = tiltedAtoms tilt := rfl

theorem tiltedDesign_weight (tilt : ℝ) (hpos : 0 < tilt) (hsmall : tilt ^ 2 < 3) :
    (tiltedDesign tilt hpos hsmall).weight = tiltedWeights := rfl

/-- **THE SIX DIRECTIONS LIE ON NO CONIC.**  The pole kills the `z^2` entry, the
two axis atoms tie the two square entries to the two mixed height entries, and
the three diagonal atoms overdetermine the `xy` entry. -/
theorem tiltedAtoms_stressFree (tilt : ℝ) (hpos : 0 < tilt) (hsmall : tilt ^ 2 < 3) :
    ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (tiltedAtoms tilt atomIndex)) = 0 →
        stressCoeff = 0 := by
  rw [stressFree_iff_no_conic_sixThree]
  intro conic hsymm hvanish
  have hs10 : conic 1 0 = conic 0 1 := by
    have hentry := congrFun (congrFun hsymm 0) 1
    simpa [Matrix.transpose_apply] using hentry
  have hs20 : conic 2 0 = conic 0 2 := by
    have hentry := congrFun (congrFun hsymm 0) 2
    simpa [Matrix.transpose_apply] using hentry
  have hs21 : conic 2 1 = conic 1 2 := by
    have hentry := congrFun (congrFun hsymm 1) 2
    simpa [Matrix.transpose_apply] using hentry
  have h0 := hvanish 0
  have h1 := hvanish 1
  have h2 := hvanish 2
  have h3 := hvanish 3
  have h4 := hvanish 4
  have h5 := hvanish 5
  simp [tiltedAtoms, dotProduct, Matrix.mulVec, Fin.sum_univ_three, hs10, hs20, hs21]
    at h0 h1 h2 h3 h4 h5
  have hq33 : conic 2 2 = 0 := by
    rcases h0 with hzero | hentry | hzero
    · exact absurd hzero (tiltHeight_ne_zero tilt hsmall)
    · exact hentry
    · exact absurd hzero (tiltHeight_ne_zero tilt hsmall)
  rw [hq33] at h1 h2 h3 h4 h5
  ring_nf at h1 h2 h3 h4 h5
  have hq12 : conic 0 1 = 0 := by linarith
  have hheight : tilt * conic 0 2 = 0 := by linarith
  have hwidth : tilt * conic 1 2 = 0 := by linarith
  have hq13 : conic 0 2 = 0 := by
    rcases mul_eq_zero.mp hheight with hzero | hentry
    · exact absurd hzero (ne_of_gt hpos)
    · exact hentry
  have hq23 : conic 1 2 = 0 := by
    rcases mul_eq_zero.mp hwidth with hzero | hentry
    · exact absurd hzero (ne_of_gt hpos)
    · exact hentry
  have hq11 : conic 0 0 = 0 := by linarith [hheight]
  have hq22 : conic 1 1 = 0 := by linarith [hwidth]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [hq11, hq22, hq33, hq12, hq13, hq23, hs10, hs20, hs21]

theorem tiltedDesign_stressFree (tilt : ℝ) (hpos : 0 < tilt) (hsmall : tilt ^ 2 < 3) :
    ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex
          • atomMatrix ((tiltedDesign tilt hpos hsmall).atom atomIndex)) = 0 →
        stressCoeff = 0 := by
  rw [tiltedDesign_atom]
  exact tiltedAtoms_stressFree tilt hpos hsmall

theorem atomShare_tiltedDesign_zero (tilt : ℝ) (hpos : 0 < tilt) (hsmall : tilt ^ 2 < 3) :
    atomShare (tiltedDesign tilt hpos hsmall) 0 = 1 - tilt ^ 2 / 3 := by
  have hz2 : tiltHeight tilt ^ 2 = (3 - tilt ^ 2) / 2 := tiltHeight_sq tilt hsmall
  simp [atomShare, tiltedDesign_atom, tiltedDesign_weight, leverageOf, tiltedAtoms,
    tiltedWeights, Fin.sum_univ_three]
  linarith [hz2]

/-- **THE STRICT SHARE CAP OF BRANCH (i) IS NOT UNIFORM.**  For every positive
defect some stress-free `(6,3)` design carries an atom whose share exceeds
`1 - defect`. -/
theorem not_uniform_atomShare_cap_of_stressFree (defect : ℝ) (hdefect : 0 < defect) :
    ∃ (design : WeightedDesign 6 3) (label : Fin 6),
      (∀ stressCoeff : Fin 6 → ℝ,
          (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
            stressCoeff = 0)
        ∧ 1 - defect < atomShare design label := by
  have hsqrtPos : 0 < Real.sqrt defect := Real.sqrt_pos.mpr hdefect
  have hsqrtSq : Real.sqrt defect ^ 2 = defect := Real.sq_sqrt hdefect.le
  set tilt : ℝ := min 1 (Real.sqrt defect) with htiltDef
  have hpos : 0 < tilt := lt_min one_pos hsqrtPos
  have hle_one : tilt ≤ 1 := min_le_left _ _
  have hle_sqrt : tilt ≤ Real.sqrt defect := min_le_right _ _
  have hsqLeOne : tilt ^ 2 ≤ 1 := by nlinarith [hpos.le, hle_one]
  have hsmall : tilt ^ 2 < 3 := by linarith
  have hsqLeDefect : tilt ^ 2 ≤ defect := by
    nlinarith [hpos.le, hle_sqrt, Real.sqrt_nonneg defect, hsqrtSq]
  refine ⟨tiltedDesign tilt hpos hsmall, 0, tiltedDesign_stressFree tilt hpos hsmall, ?_⟩
  rw [atomShare_tiltedDesign_zero tilt hpos hsmall]
  have hsqPos : 0 < tilt ^ 2 := by positivity
  linarith

end Gtz
