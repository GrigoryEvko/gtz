/-
# The complex `(6,3)` counterexample is INTERIOR to the parallel-free locus

Where the realness in `Gtz.HingeHoldsAtSize 6 3` is spent, as a kernel fact
rather than a measurement.  `Gtz.trineDesign` is the complex `(6,3)` design with
no dominating triple (`Gtz.trine_no_dominating_triple`); it is proved here to have
NO PARALLEL PAIR.  So the complex parallel-free locus at `(6,3)` carries a design
that no triple dominates, while `Gtz.icosaDesign` — real, hence complex, and
parallel-free — is strictly dominating.

Two things follow.  The hinge is FALSE over `ℂ`, so any route to it must consume
realness, and this witness says exactly where.  And the connectedness route of
`Gtz/Reduction/ConnectednessRoute.lean` is field-blind in every input except the
hinge, so this is also the reason that route cannot be run over `ℂ` — its
conclusion would be false there.

The proof is the vanishing of the `2 × 2` minors: proportional atoms force
`a_d i · a_k j = a_k i · a_d j` for every coordinate pair.  Two atoms on
DIFFERENT axes fail it at `(0,1)` because `0 = √2 · √2`; two on the SAME axis fail
it at `(0,2)` because the amplitude cancels and the phases must then agree.
-/
import Mathlib
import Gtz.Complex.ComplexWitness
import Gtz.Complex.SharpConstantLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz


private theorem topAmpC_ne_zero : topAmpC ≠ 0 := fun hzero => by
  have htwo : (2 : ℂ) = 0 := by rw [← topAmpC_sq, hzero, mul_zero]
  norm_num at htwo

private theorem omegaRoot_ne_one : omegaRoot ≠ 1 := fun hone => by
  have hthree : (3 : ℂ) = 0 := by
    linear_combination omegaRoot_sum - hone - (omegaRoot + 1) * hone
  norm_num at hthree

private theorem omegaRootSq_ne_one : omegaRoot ^ 2 ≠ 1 := fun hone =>
  omegaRoot_ne_one (by linear_combination omegaRoot_cube - omegaRoot * hone)

private theorem omegaRoot_ne_negOne : omegaRoot ≠ -1 := fun hneg => by
  have hcontra : (-1 : ℂ) = 1 := by
    linear_combination omegaRoot_cube - (1 - omegaRoot + omegaRoot ^ 2) * hneg
  norm_num at hcontra

private theorem omegaRoot_ne_omegaRootSq : omegaRoot ≠ omegaRoot ^ 2 := fun heq =>
  omegaRootSq_ne_one (by linear_combination omegaRoot * heq + omegaRoot_cube)

/-- **THE SHARED-AXIS TRINE HAS NO PARALLEL PAIR.** -/
theorem trineDesign_isPrimitive (keptLabel dropLabel : Fin 6) (ratio : ℂ)
    (hdistinct : keptLabel ≠ dropLabel) :
    trineDesign.atom dropLabel ≠ ratio • trineDesign.atom keptLabel := by
  intro hparallel
  have hcoordZero := congrFun hparallel 0
  have hcoordOne := congrFun hparallel 1
  have hcoordTwo := congrFun hparallel 2
  have hminorZeroOne : trineDesign.atom dropLabel 0 * trineDesign.atom keptLabel 1
      = trineDesign.atom keptLabel 0 * trineDesign.atom dropLabel 1 := by
    rw [hcoordZero, hcoordOne]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hminorZeroTwo : trineDesign.atom dropLabel 0 * trineDesign.atom keptLabel 2
      = trineDesign.atom keptLabel 0 * trineDesign.atom dropLabel 2 := by
    rw [hcoordZero, hcoordTwo]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hminorOneTwo : trineDesign.atom dropLabel 1 * trineDesign.atom keptLabel 2
      = trineDesign.atom keptLabel 1 * trineDesign.atom dropLabel 2 := by
    rw [hcoordOne, hcoordTwo]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  clear hparallel hcoordZero hcoordOne hcoordTwo
  have hamp := topAmpC_ne_zero
  have hsq := topAmpC_sq
  fin_cases keptLabel <;> fin_cases dropLabel <;>
    simp [trineDesign, trineAtom, trineLeft, trineRight,
      omegaPow_zero, omegaPow_one, omegaPow_two, hsq, hamp,
      omegaRoot_ne_one, omegaRoot_ne_negOne,
      omegaRoot_ne_omegaRootSq, omegaRoot_ne_omegaRootSq.symm]
      at hminorZeroOne hminorZeroTwo hminorOneTwo <;>
    exact hdistinct rfl

end Gtz
