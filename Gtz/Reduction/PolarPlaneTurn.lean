/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.PolarCrossWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The quarter turn of the pole plane, the direct cover, and the arithmetic tie law

The witnessed Schur kill of `Gtz.Reduction.PolarCrossWitness` opens its gate
through a PAIR CERTIFICATE and a weight cap.  That gate is Parseval plus one
Cauchy-Schwarz, and the probes show it refuses a quarter of the pole and
triple combinations that the survivor plane actually covers.  This file
replaces the gate by the exact one and removes every vector from the kill.

## 1. The quarter turn

`Gtz.polarTurnVec` is the cross product of the pole with an atom.  It reads
zero at the pole, it reads an atom as the anchored bracket, and the Lagrange
identity `Gtz.polarTurnVec_dotProduct_pair` reads a pair of turns as the
leverage times the shadow pairing.  Over the reals the turn is an isometry of
the pole plane composed with a quarter rotation.  Over the complex field the
determinant is bilinear while the metric is sesquilinear, thus no such map
exists, and the probes confirm that the untwisted contraction laws below hold
in no phase gauge of a complex tie.

## 2. The turned frame and the contraction laws

`Gtz.sum_weight_turn_read_smul_polarTurnVec` is Parseval carried through the
quarter turn: the turned atoms rebuild the leverage times a vector, minus its
pole component.  Reading it at atoms, at shadows and at turns gives the five
contraction laws of the pole plane
(`Gtz.sum_weight_pairing_mul_tripleBracket`,
`Gtz.sum_weight_tripleBracket_mul_tripleBracket`,
`Gtz.sum_weight_planeShadowPairing_mul_tripleBracket`,
`Gtz.sum_weight_planeShadowPairing_mul_planeShadowPairing`,
`Gtz.sum_weight_pairing_mul_planeShadowPairing`).  Each one couples a bracket
or a pairing to a pole reading, and each one is division free.

## 3. The plane Cayley-Hamilton law and the direct cover

`Gtz.planeReadVec` is the survivor plane form applied to a vector.
`Gtz.planeReadVec_planeReadVec` applies it twice and collapses the result
through the shadow trace and the plane Gram determinant, for EVERY vector of
the pole plane.  With one Cauchy-Schwarz step this gives
`Gtz.polarPlaneCover_of_traceGramDet`: a survivor set whose shadow trace and
plane Gram determinant clear the two division-free bounds covers the pole
plane with the excess, and `Gtz.polarPlaneDet_pos_of_traceGramDet` supplies
the positive plane determinant for free.  No eigenvalue, no square root, no
spectral theorem, and no weight cap.

## 4. The arithmetic form of the sharp tie law

`Gtz.polarShadowAdjugate` is the reading of the coupling vector against the
closed cross witness, written in the shadow data alone
(`Gtz.polarCouplingVec_dotProduct_polarCrossWitnessVec`).  Thus
`Gtz.not_isTie_of_planeShadowSchur_rank_three` is a kill of rank three at
EVERY size whose every hypothesis is a polynomial inequality in the leverage,
the pole readings, the shadow energies and the shadow pairings.  Its
contrapositive `Gtz.tie_planeShadowSchur_six_three` is the arithmetic tie law
of the deciding cell.

The probes calibrate the kill.  On the complex tie family the Hermitian chain
keeps its best margin at or below `0.006` at every one of 572 endpoints, and
at or below `0.001` at 570 of them, thus the kill saturates over the complex
field and is a lossless reformulation and not a realness cut.  On the real
family it fires at 800 of 800 endpoints with a margin floor of `0.08`, and the
direct cover gate opens 42428 of 48000 combinations where the landed pair gate
opens 31486 and refuses none that the direct gate refuses.  The adversary that
minimises the worse of the tie gap and the kill margin reaches no endpoint
below `0.06` on four slices, and the two signs agree at 14556 of 14556
adversarial endpoints.

## 5. The residual, narrowed a sixth time

The arithmetic law is free at every tie
(`Gtz.polarPlaneShadowBound_of_isTie`), thus `Gtz.PolarTiltSelectionPlane`
hands it to the prover as a sixth bundle.  Every consumer of the shipped
residual runs on the six-bundle one, the `(5,3)` instance stays FALSE, and
the diamond guardrail stays checked.
-/

namespace Gtz

open Matrix Finset

/-! ## Part 1: the quarter turn of the pole plane -/

section QuarterTurn

/-- The bracket normal reads zero at its own second slot. -/
theorem bracketNormal_dotProduct_right (leftVec rightVec : Fin 3 → ℝ) :
    bracketNormal leftVec rightVec ⬝ᵥ rightVec = 0 := by
  simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The bracket normal of a vector with itself is the zero vector. -/
theorem bracketNormal_self (leftVec : Fin 3 → ℝ) : bracketNormal leftVec leftVec = 0 := by
  funext coord
  fin_cases coord <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, bracketNormal, Pi.zero_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] <;>
    ring

/-- The bracket normal of a zero second slot is the zero vector. -/
theorem bracketNormal_zero_right (leftVec : Fin 3 → ℝ) : bracketNormal leftVec 0 = 0 := by
  funext coord
  fin_cases coord <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, bracketNormal, Pi.zero_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] <;>
    ring

/-- The bracket normal is additive in its second slot. -/
theorem bracketNormal_add_right (leftVec firstVec secondVec : Fin 3 → ℝ) :
    bracketNormal leftVec (firstVec + secondVec)
      = bracketNormal leftVec firstVec + bracketNormal leftVec secondVec := by
  funext coord
  fin_cases coord <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, bracketNormal, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] <;>
    ring

/-- The bracket normal is homogeneous in its second slot. -/
theorem bracketNormal_smul_right (leftVec rightVec : Fin 3 → ℝ) (ratio : ℝ) :
    bracketNormal leftVec (ratio • rightVec) = ratio • bracketNormal leftVec rightVec := by
  funext coord
  fin_cases coord <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, bracketNormal, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] <;>
    ring

/-- The bracket normal commutes with a finite sum in its second slot. -/
theorem bracketNormal_sum_right {ι : Type*} (leftVec : Fin 3 → ℝ) (index : Finset ι)
    (family : ι → Fin 3 → ℝ) :
    bracketNormal leftVec (∑ c ∈ index, family c)
      = ∑ c ∈ index, bracketNormal leftVec (family c) := by
  classical
  induction index using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, bracketNormal_zero_right]
  | insert head tail hhead ih =>
      rw [Finset.sum_insert hhead, Finset.sum_insert hhead, bracketNormal_add_right, ih]

/-- **THE LAGRANGE IDENTITY.**  Two bracket normals that share a first slot
pair through the Gram data of the three vectors alone. -/
theorem bracketNormal_lagrange (leftVec firstVec secondVec : Fin 3 → ℝ) :
    bracketNormal leftVec firstVec ⬝ᵥ bracketNormal leftVec secondVec
      = (leftVec ⬝ᵥ leftVec) * (firstVec ⬝ᵥ secondVec)
        - (leftVec ⬝ᵥ firstVec) * (leftVec ⬝ᵥ secondVec) := by
  simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **THE DOUBLE TURN.**  Turning twice about the same first slot spreads the
vector over the first slot and itself: the classical expansion of a repeated
cross product. -/
theorem bracketNormal_double_turn (leftVec rightVec : Fin 3 → ℝ) :
    bracketNormal leftVec (bracketNormal leftVec rightVec)
      = (leftVec ⬝ᵥ rightVec) • leftVec - (leftVec ⬝ᵥ leftVec) • rightVec := by
  funext coord
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, bracketNormal, dotProduct,
    Fin.sum_univ_three]
  fin_cases coord <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    ring

variable {m : ℕ}

/-- **THE QUARTER TURN OF THE POLE PLANE.**  The cross product of the pole
with an atom.  It lives in the pole plane, it reads an atom as the anchored
bracket, and it is the real-only carrier of the polar lane: the determinant
that defines it is bilinear, while the metric that measures it is not. -/
def polarTurnVec (design : WeightedDesign m 3) (pole label : Fin m) : Fin 3 → ℝ :=
  bracketNormal (design.atom pole) (design.atom label)

/-- The turn lives in the pole plane. -/
theorem polarTurnVec_dotProduct_pole (design : WeightedDesign m 3) (pole label : Fin m) :
    polarTurnVec design pole label ⬝ᵥ design.atom pole = 0 :=
  bracketNormal_dotProduct_left _ _

/-- The turn reads its own atom as zero. -/
theorem polarTurnVec_dotProduct_own (design : WeightedDesign m 3) (pole label : Fin m) :
    polarTurnVec design pole label ⬝ᵥ design.atom label = 0 :=
  bracketNormal_dotProduct_right _ _

/-- **THE TURN READS AN ATOM AS THE ANCHORED BRACKET.** -/
theorem polarTurnVec_dotProduct_atom (design : WeightedDesign m 3)
    (pole first second : Fin m) :
    polarTurnVec design pole first ⬝ᵥ design.atom second
      = tripleBracket (design.atom pole) (design.atom first) (design.atom second) :=
  (tripleBracket_eq_bracketNormal_dotProduct _ _ _).symm

/-- The pole turns to the zero vector. -/
theorem polarTurnVec_self (design : WeightedDesign m 3) (pole : Fin m) :
    polarTurnVec design pole pole = 0 :=
  bracketNormal_self _

/-- **THE TURN PAIRING.**  Two turns pair as the leverage times the shadow
pairing.  This is the Lagrange identity in the shadow calculus, and it is the
law that no phase gauge of a complex tie repairs. -/
theorem polarTurnVec_dotProduct_pair (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (first second : Fin m) :
    polarTurnVec design pole first ⬝ᵥ polarTurnVec design pole second
      = (design.atom pole ⬝ᵥ design.atom pole)
        * planeShadowPairing design pole first second := by
  have hLne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  rw [polarTurnVec, polarTurnVec, bracketNormal_lagrange, planeShadowPairing,
    dotProduct_comm (design.atom pole) (design.atom first),
    dotProduct_comm (design.atom pole) (design.atom second)]
  field_simp

/-- The squared length of a turn is the leverage times the shadow energy. -/
theorem polarTurnVec_dotProduct_self (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (label : Fin m) :
    polarTurnVec design pole label ⬝ᵥ polarTurnVec design pole label
      = (design.atom pole ⬝ᵥ design.atom pole) * planeShadowSq design pole label := by
  rw [polarTurnVec_dotProduct_pair design hpole label label,
    planeShadowPairing_self design pole label]

end QuarterTurn

/-! ## Part 2: the turned frame and the contraction laws

Parseval carried through the quarter turn.  Reading the turned frame at atoms,
at shadows and at turns produces the five contraction laws of the pole plane,
each one a coupling of a bracket or a pairing to a pole reading. -/

section TurnedFrame

variable {m : ℕ}

/-- **THE TURNED FRAME.**  The weighted read-and-rebuild through the quarter
turn returns the leverage times the vector, minus its pole component.  This is
the frame reconstruction of `Gtz.sum_weight_read_smul_atom`, conjugated by the
turn. -/
theorem sum_weight_turn_read_smul_polarTurnVec (design : WeightedDesign m 3)
    (pole : Fin m) (vec : Fin 3 → ℝ) :
    ∑ c, (design.weight c * (polarTurnVec design pole c ⬝ᵥ vec)) • polarTurnVec design pole c
      = (design.atom pole ⬝ᵥ design.atom pole) • vec
        - (design.atom pole ⬝ᵥ vec) • design.atom pole := by
  have hread : ∀ c : Fin m, polarTurnVec design pole c ⬝ᵥ vec
      = -(design.atom c ⬝ᵥ bracketNormal (design.atom pole) vec) := by
    intro c
    rw [polarTurnVec, dotProduct_comm (design.atom c) (bracketNormal (design.atom pole) vec),
      ← tripleBracket_eq_bracketNormal_dotProduct,
      ← tripleBracket_eq_bracketNormal_dotProduct]
    exact tripleBracket_swapRight (design.atom pole) (design.atom c) vec
  have hstep : ∀ c : Fin m,
      (design.weight c * (polarTurnVec design pole c ⬝ᵥ vec)) • polarTurnVec design pole c
        = bracketNormal (design.atom pole)
            ((-(design.weight c
                * (design.atom c ⬝ᵥ bracketNormal (design.atom pole) vec))) • design.atom c) := by
    intro c
    rw [bracketNormal_smul_right, hread c, polarTurnVec]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun c _ => hstep c, ← bracketNormal_sum_right]
  have hinner : ∑ c, (-(design.weight c
        * (design.atom c ⬝ᵥ bracketNormal (design.atom pole) vec))) • design.atom c
      = -bracketNormal (design.atom pole) vec := by
    have hrecon := sum_weight_read_smul_atom design (bracketNormal (design.atom pole) vec)
    have hcancel : (∑ c, (-(design.weight c
          * (design.atom c ⬝ᵥ bracketNormal (design.atom pole) vec))) • design.atom c)
        + (∑ c, (design.weight c
            * (design.atom c ⬝ᵥ bracketNormal (design.atom pole) vec)) • design.atom c)
        = 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun c _ => by module
    rw [hrecon] at hcancel
    exact eq_neg_of_add_eq_zero_left hcancel
  rw [hinner]
  have hneg : bracketNormal (design.atom pole) (-bracketNormal (design.atom pole) vec)
      = -bracketNormal (design.atom pole) (bracketNormal (design.atom pole) vec) := by
    rw [← neg_one_smul ℝ (bracketNormal (design.atom pole) vec), bracketNormal_smul_right,
      neg_one_smul]
  rw [hneg, bracketNormal_double_turn]
  module

/-- **THE TURNED CROSS MOMENT.**  The pairing-weighted turns of all labels add
to the zero vector. -/
theorem sum_weight_pairing_smul_polarTurnVec (design : WeightedDesign m 3) (pole : Fin m) :
    ∑ c, (design.weight c * (design.atom c ⬝ᵥ design.atom pole))
        • polarTurnVec design pole c = 0 := by
  have hstep : ∀ c : Fin m,
      (design.weight c * (design.atom c ⬝ᵥ design.atom pole)) • polarTurnVec design pole c
        = bracketNormal (design.atom pole)
            ((design.weight c * (design.atom c ⬝ᵥ design.atom pole)) • design.atom c) := by
    intro c
    rw [bracketNormal_smul_right, polarTurnVec]
  rw [Finset.sum_congr rfl fun c _ => hstep c, ← bracketNormal_sum_right,
    sum_weight_read_smul_atom design (design.atom pole), bracketNormal_self]

/-- **THE TURNED SHADOW RECONSTRUCTION.**  The bracket-weighted turns rebuild
the leverage times a shadow. -/
theorem sum_weight_tripleBracket_smul_polarTurnVec (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (label : Fin m) :
    ∑ c, (design.weight c
        * tripleBracket (design.atom pole) (design.atom c) (design.atom label))
        • polarTurnVec design pole c
      = (design.atom pole ⬝ᵥ design.atom pole) • planeShadowVec design pole label := by
  have hLne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  have hframe := sum_weight_turn_read_smul_polarTurnVec design pole (design.atom label)
  have hleft : ∀ c : Fin m,
      (design.weight c
          * tripleBracket (design.atom pole) (design.atom c) (design.atom label))
          • polarTurnVec design pole c
        = (design.weight c * (polarTurnVec design pole c ⬝ᵥ design.atom label))
          • polarTurnVec design pole c := by
    intro c
    rw [polarTurnVec_dotProduct_atom]
  rw [Finset.sum_congr rfl fun c _ => hleft c, hframe, planeShadowVec, smul_sub, smul_smul,
    dotProduct_comm (design.atom pole) (design.atom label)]
  congr 2
  field_simp

/-! ### The five contraction laws -/

/-- **THE CROSS MOMENT AGAINST A BRACKET.**  The pole readings weighted by the
anchored brackets cancel exactly.  Over the reals the four terms of a row
therefore carry both signs, and this is the signed cancellation the polar lane
owns. -/
theorem sum_weight_pairing_mul_tripleBracket (design : WeightedDesign m 3)
    (pole label : Fin m) :
    ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom pole)
        * tripleBracket (design.atom pole) (design.atom c) (design.atom label) = 0 := by
  have hvec := sum_weight_pairing_smul_polarTurnVec design pole
  have hread : (∑ c, (design.weight c * (design.atom c ⬝ᵥ design.atom pole))
      • polarTurnVec design pole c) ⬝ᵥ design.atom label
      = ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom pole)
          * tripleBracket (design.atom pole) (design.atom c) (design.atom label) := by
    rw [sum_dotProduct]
    exact Finset.sum_congr rfl fun c _ => by
      rw [smul_dotProduct, smul_eq_mul, polarTurnVec_dotProduct_atom]
  rw [← hread, hvec, zero_dotProduct]

/-- **THE CROSS MOMENT AGAINST A PAIRING.**  The same cancellation read
against a shadow. -/
theorem sum_weight_pairing_mul_planeShadowPairing (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (label : Fin m) :
    ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom pole)
        * planeShadowPairing design pole c label = 0 := by
  have hvec := sum_weight_pairing_smul_planeShadowVec design hpole
  have hread : (∑ c, (design.weight c * (design.atom c ⬝ᵥ design.atom pole))
      • planeShadowVec design pole c) ⬝ᵥ planeShadowVec design pole label
      = ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom pole)
          * planeShadowPairing design pole c label := by
    rw [sum_dotProduct]
    exact Finset.sum_congr rfl fun c _ => by
      rw [smul_dotProduct, smul_eq_mul, planeShadowVec_dotProduct_pair design hpole c label]
  rw [← hread, hvec, zero_dotProduct]

/-- **THE BRACKET CONTRACTION.**  Two anchored brackets contract through the
frame to the leverage times a shadow pairing.  The untwisted shape of this law
is exactly what the complex tie family breaks in every phase gauge. -/
theorem sum_weight_tripleBracket_mul_tripleBracket (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (first second : Fin m) :
    ∑ c, design.weight c
        * tripleBracket (design.atom pole) (design.atom c) (design.atom first)
        * tripleBracket (design.atom pole) (design.atom c) (design.atom second)
      = (design.atom pole ⬝ᵥ design.atom pole)
        * planeShadowPairing design pole first second := by
  have hvec := sum_weight_tripleBracket_smul_polarTurnVec design hpole first
  have hread : (∑ c, (design.weight c
        * tripleBracket (design.atom pole) (design.atom c) (design.atom first))
        • polarTurnVec design pole c) ⬝ᵥ design.atom second
      = ∑ c, design.weight c
          * tripleBracket (design.atom pole) (design.atom c) (design.atom first)
          * tripleBracket (design.atom pole) (design.atom c) (design.atom second) := by
    rw [sum_dotProduct]
    exact Finset.sum_congr rfl fun c _ => by
      rw [smul_dotProduct, smul_eq_mul, polarTurnVec_dotProduct_atom]
  rw [← hread, hvec, smul_dotProduct, smul_eq_mul,
    dotProduct_comm (planeShadowVec design pole first) (design.atom second),
    atom_dotProduct_planeShadowVec design pole second first,
    planeShadowPairing_comm design pole second first]

/-- **THE PAIRING CONTRACTION AGAINST A BRACKET.**  A shadow pairing and a
bracket contract through the frame to the bracket itself. -/
theorem sum_weight_planeShadowPairing_mul_tripleBracket (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (first second : Fin m) :
    ∑ c, design.weight c * planeShadowPairing design pole c first
        * tripleBracket (design.atom pole) (design.atom c) (design.atom second)
      = tripleBracket (design.atom pole) (design.atom first) (design.atom second) := by
  have hrecon := sum_weight_read_smul_atom design (planeShadowVec design pole first)
  have hturn : bracketNormal (design.atom pole) (planeShadowVec design pole first)
      = ∑ c, (design.weight c * planeShadowPairing design pole c first)
          • polarTurnVec design pole c := by
    rw [← hrecon, bracketNormal_sum_right]
    exact Finset.sum_congr rfl fun c _ => by
      rw [bracketNormal_smul_right, polarTurnVec, atom_dotProduct_planeShadowVec]
  have hread : (∑ c, (design.weight c * planeShadowPairing design pole c first)
      • polarTurnVec design pole c) ⬝ᵥ design.atom second
      = ∑ c, design.weight c * planeShadowPairing design pole c first
          * tripleBracket (design.atom pole) (design.atom c) (design.atom second) := by
    rw [sum_dotProduct]
    exact Finset.sum_congr rfl fun c _ => by
      rw [smul_dotProduct, smul_eq_mul, polarTurnVec_dotProduct_atom]
  have hLne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  rw [← hread, ← hturn, ← tripleBracket_eq_bracketNormal_dotProduct, planeShadowVec]
  rw [show design.atom first
        - ((design.atom first ⬝ᵥ design.atom pole)
            / (design.atom pole ⬝ᵥ design.atom pole)) • design.atom pole
      = design.atom first
        + (-((design.atom first ⬝ᵥ design.atom pole)
            / (design.atom pole ⬝ᵥ design.atom pole))) • design.atom pole by module]
  simp only [tripleBracket_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **THE PAIRING CONTRACTION.**  Two shadow pairings contract through the
frame to a shadow pairing: the plane frame is idempotent. -/
theorem sum_weight_planeShadowPairing_mul_planeShadowPairing (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (first second : Fin m) :
    ∑ c, design.weight c * planeShadowPairing design pole c first
        * planeShadowPairing design pole c second
      = planeShadowPairing design pole first second := by
  have hrecon := sum_weight_read_smul_atom design (planeShadowVec design pole first)
  have hread : (∑ c, (design.weight c * (design.atom c ⬝ᵥ planeShadowVec design pole first))
      • design.atom c) ⬝ᵥ planeShadowVec design pole second
      = ∑ c, design.weight c * planeShadowPairing design pole c first
          * planeShadowPairing design pole c second := by
    rw [sum_dotProduct]
    exact Finset.sum_congr rfl fun c _ => by
      rw [smul_dotProduct, smul_eq_mul, atom_dotProduct_planeShadowVec,
        atom_dotProduct_planeShadowVec]
  rw [← hread, hrecon, planeShadowVec_dotProduct_pair design hpole first second]

/-- The diagonal bracket contraction: the anchored brackets against one label
carry the leverage times that label's shadow energy. -/
theorem sum_weight_tripleBracket_sq (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (label : Fin m) :
    ∑ c, design.weight c
        * tripleBracket (design.atom pole) (design.atom c) (design.atom label) ^ 2
      = (design.atom pole ⬝ᵥ design.atom pole) * planeShadowSq design pole label := by
  rw [← planeShadowPairing_self design pole label,
    ← sum_weight_tripleBracket_mul_tripleBracket design hpole label label]
  exact Finset.sum_congr rfl fun c _ => by ring

end TurnedFrame

/-! ## Part 3: the plane Cayley-Hamilton law and the direct cover

The survivor plane form applied twice collapses through the shadow trace and
the plane Gram determinant.  One Cauchy-Schwarz step turns that collapse into
a division-free cover criterion with no eigenvalue anywhere. -/

section DirectCover

variable {m : ℕ}

/-- **THE SURVIVOR PLANE FORM.**  A vector read by every selected atom and
rebuilt along the selected shadows. -/
noncomputable def planeReadVec (design : WeightedDesign m 3) (pole : Fin m)
    (selected : Finset (Fin m)) (readVec : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ∑ d ∈ selected, (design.atom d ⬝ᵥ readVec) • planeShadowVec design pole d

/-- **THE PLANE GRAM DETERMINANT.**  The determinant of the survivor plane
form, division free: the halved double sum of the pair Gram minors. -/
noncomputable def polarPlaneGramDet {size rank : ℕ} (design : WeightedDesign size rank)
    (pole : Fin size) (selected : Finset (Fin size)) : ℝ :=
  (∑ c ∈ selected, ∑ d ∈ selected,
      (planeShadowSq design pole c * planeShadowSq design pole d
        - planeShadowPairing design pole c d ^ 2)) / 2

/-- The plane determinant is one, minus the shadow trace, plus the plane Gram
determinant. -/
theorem polarPlaneDet_eq {size rank : ℕ} (design : WeightedDesign size rank)
    (pole : Fin size) (selected : Finset (Fin size)) :
    polarPlaneDet design pole selected
      = 1 - (∑ c ∈ selected, planeShadowSq design pole c)
        + polarPlaneGramDet design pole selected := rfl

/-- The survivor plane form lands in the pole plane. -/
theorem planeReadVec_dotProduct_pole (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (selected : Finset (Fin m))
    (readVec : Fin 3 → ℝ) :
    planeReadVec design pole selected readVec ⬝ᵥ design.atom pole = 0 := by
  rw [planeReadVec, sum_dotProduct]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [smul_dotProduct, planeShadowVec_dotProduct_pole design hpole d, smul_eq_mul, mul_zero]

/-- **THE SURVIVOR PLANE FORM IS SYMMETRIC.**  On the pole plane it moves
across a pairing unchanged. -/
theorem planeReadVec_dotProduct_symm (design : WeightedDesign m 3) (pole : Fin m)
    (selected : Finset (Fin m)) {leftVec rightVec : Fin 3 → ℝ}
    (hleft : leftVec ⬝ᵥ design.atom pole = 0) (hright : rightVec ⬝ᵥ design.atom pole = 0) :
    planeReadVec design pole selected leftVec ⬝ᵥ rightVec
      = leftVec ⬝ᵥ planeReadVec design pole selected rightVec := by
  rw [planeReadVec, planeReadVec, sum_dotProduct, dotProduct_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    planeShadowVec_dotProduct_polar design pole d hright,
    dotProduct_comm leftVec (planeShadowVec design pole d),
    planeShadowVec_dotProduct_polar design pole d hleft]
  ring

/-- The coupling vector is the survivor plane form read at the pole. -/
theorem polarCouplingVec_eq_planeReadVec (design : WeightedDesign m 3) (pole : Fin m)
    (selected : Finset (Fin m)) :
    polarCouplingVec design pole selected
      = planeReadVec design pole selected (design.atom pole) := by
  rw [polarCouplingVec, planeReadVec]

/-- **THE PLANE CAYLEY-HAMILTON LAW.**  The survivor plane form applied twice
to a vector of the pole plane collapses through the shadow trace and the plane
Gram determinant.  The Gram Cramer decomposition supplies the identity pair by
pair and the bracket corrections die on the plane, thus the proof has no
eigenvalue, no matrix inverse and no plane coordinates. -/
theorem planeReadVec_planeReadVec (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (selected : Finset (Fin m))
    {readVec : Fin 3 → ℝ} (hread : readVec ⬝ᵥ design.atom pole = 0) :
    planeReadVec design pole selected (planeReadVec design pole selected readVec)
      = (∑ c ∈ selected, planeShadowSq design pole c)
          • planeReadVec design pole selected readVec
        - polarPlaneGramDet design pole selected • readVec := by
  classical
  simp only [planeReadVec, polarPlaneGramDet]
  have hpoleRead : design.atom pole ⬝ᵥ readVec = 0 := by
    rw [dotProduct_comm]; exact hread
  have hshadowRead : ∀ c : Fin m,
      planeShadowVec design pole c ⬝ᵥ readVec = design.atom c ⬝ᵥ readVec := by
    intro c
    rw [planeShadowVec, sub_dotProduct, smul_dotProduct, smul_eq_mul, hpoleRead, mul_zero,
      sub_zero]
  have hreadSum : ∀ c : Fin m,
      design.atom c ⬝ᵥ ∑ d ∈ selected, (design.atom d ⬝ᵥ readVec) • planeShadowVec design pole d
      = ∑ d ∈ selected,
          (design.atom d ⬝ᵥ readVec) * planeShadowPairing design pole c d := by
    intro c
    rw [dotProduct_sum]
    exact Finset.sum_congr rfl fun d _ => by
      rw [dotProduct_smul, smul_eq_mul, atom_dotProduct_planeShadowVec]
  have hterm : ∀ c ∈ selected, ∀ d ∈ selected,
      (planeShadowSq design pole c * planeShadowSq design pole d
          - planeShadowPairing design pole c d ^ 2) • readVec
        = ((design.atom c ⬝ᵥ readVec) * planeShadowSq design pole d
              - (design.atom d ⬝ᵥ readVec) * planeShadowPairing design pole c d)
            • planeShadowVec design pole c
          + ((design.atom d ⬝ᵥ readVec) * planeShadowSq design pole c
              - (design.atom c ⬝ᵥ readVec) * planeShadowPairing design pole c d)
            • planeShadowVec design pole d := by
    intro c _ d _
    have hdecomp := gramDet_smul_decomp (planeShadowVec design pole c)
      (planeShadowVec design pole d) readVec
    rw [planeShadowVec_dotProduct_self design hpole c,
      planeShadowVec_dotProduct_self design hpole d,
      planeShadowVec_dotProduct_pair design hpole c d, hshadowRead c, hshadowRead d,
      tripleBracket_eq_zero_of_pole_orthogonal _ _ _ hpole
        (planeShadowVec_dotProduct_pole design hpole c)
        (planeShadowVec_dotProduct_pole design hpole d) hread,
      zero_smul, add_zero] at hdecomp
    exact hdecomp
  have hexpand : (∑ c ∈ selected, ∑ d ∈ selected,
      (planeShadowSq design pole c * planeShadowSq design pole d
        - planeShadowPairing design pole c d ^ 2)) • readVec
      = ∑ c ∈ selected, ∑ d ∈ selected,
          ((design.atom c ⬝ᵥ readVec) * planeShadowSq design pole d
              - (design.atom d ⬝ᵥ readVec) * planeShadowPairing design pole c d)
            • planeShadowVec design pole c
        + ∑ c ∈ selected, ∑ d ∈ selected,
            ((design.atom d ⬝ᵥ readVec) * planeShadowSq design pole c
                - (design.atom c ⬝ᵥ readVec) * planeShadowPairing design pole c d)
              • planeShadowVec design pole d := by
    calc (∑ c ∈ selected, ∑ d ∈ selected,
        (planeShadowSq design pole c * planeShadowSq design pole d
          - planeShadowPairing design pole c d ^ 2)) • readVec
        = ∑ c ∈ selected, ∑ d ∈ selected,
            (planeShadowSq design pole c * planeShadowSq design pole d
              - planeShadowPairing design pole c d ^ 2) • readVec := by
          rw [Finset.sum_smul]
          exact Finset.sum_congr rfl fun c _ => Finset.sum_smul
      _ = ∑ c ∈ selected, ∑ d ∈ selected,
            (((design.atom c ⬝ᵥ readVec) * planeShadowSq design pole d
                  - (design.atom d ⬝ᵥ readVec) * planeShadowPairing design pole c d)
                • planeShadowVec design pole c
              + ((design.atom d ⬝ᵥ readVec) * planeShadowSq design pole c
                  - (design.atom c ⬝ᵥ readVec) * planeShadowPairing design pole c d)
                • planeShadowVec design pole d) :=
          Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => hterm c hc d hd
      _ = _ := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => Finset.sum_add_distrib
  have hswap : ∑ c ∈ selected, ∑ d ∈ selected,
      ((design.atom d ⬝ᵥ readVec) * planeShadowSq design pole c
          - (design.atom c ⬝ᵥ readVec) * planeShadowPairing design pole c d)
        • planeShadowVec design pole d
      = ∑ c ∈ selected, ∑ d ∈ selected,
          ((design.atom c ⬝ᵥ readVec) * planeShadowSq design pole d
              - (design.atom d ⬝ᵥ readVec) * planeShadowPairing design pole c d)
            • planeShadowVec design pole c := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
      rw [planeShadowPairing_comm design pole d c]
  have hinner : ∑ c ∈ selected, ∑ d ∈ selected,
      ((design.atom c ⬝ᵥ readVec) * planeShadowSq design pole d
          - (design.atom d ⬝ᵥ readVec) * planeShadowPairing design pole c d)
        • planeShadowVec design pole c
      = (∑ c ∈ selected, planeShadowSq design pole c)
          • (∑ d ∈ selected, (design.atom d ⬝ᵥ readVec) • planeShadowVec design pole d)
        - ∑ c ∈ selected,
            (design.atom c ⬝ᵥ ∑ d ∈ selected,
                (design.atom d ⬝ᵥ readVec) • planeShadowVec design pole d)
              • planeShadowVec design pole c := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hreadSum c, ← Finset.sum_smul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    module
  have hdouble : (∑ c ∈ selected, ∑ d ∈ selected,
      (planeShadowSq design pole c * planeShadowSq design pole d
        - planeShadowPairing design pole c d ^ 2)) • readVec
      = (2 : ℝ) • ((∑ c ∈ selected, planeShadowSq design pole c)
            • (∑ d ∈ selected, (design.atom d ⬝ᵥ readVec) • planeShadowVec design pole d)
          - ∑ c ∈ selected,
              (design.atom c ⬝ᵥ ∑ d ∈ selected,
                  (design.atom d ⬝ᵥ readVec) • planeShadowVec design pole d)
                • planeShadowVec design pole c) := by
    rw [hexpand, hswap, hinner, two_smul]
  have hhalf : ((∑ c ∈ selected, ∑ d ∈ selected,
      (planeShadowSq design pole c * planeShadowSq design pole d
        - planeShadowPairing design pole c d ^ 2)) / 2) • readVec
      = (∑ c ∈ selected, planeShadowSq design pole c)
          • (∑ d ∈ selected, (design.atom d ⬝ᵥ readVec) • planeShadowVec design pole d)
        - ∑ c ∈ selected,
            (design.atom c ⬝ᵥ ∑ d ∈ selected,
                (design.atom d ⬝ᵥ readVec) • planeShadowVec design pole d)
              • planeShadowVec design pole c := by
    have hdiv : ((∑ c ∈ selected, ∑ d ∈ selected,
        (planeShadowSq design pole c * planeShadowSq design pole d
          - planeShadowPairing design pole c d ^ 2)) / 2) • readVec
        = (1 / 2 : ℝ) • ((∑ c ∈ selected, ∑ d ∈ selected,
            (planeShadowSq design pole c * planeShadowSq design pole d
              - planeShadowPairing design pole c d ^ 2)) • readVec) := by
      rw [smul_smul]
      congr 1
      ring
    rw [hdiv, hdouble, smul_smul]
    norm_num
  rw [hhalf]
  abel


/-- **THE DIRECT PLANE COVER.**  A survivor set whose shadow trace clears
twice the excess and whose plane Gram determinant clears the companion bound
covers the pole plane with that excess.  The plane Cayley-Hamilton law plus one
Cauchy-Schwarz step replace the eigenvalue argument, and no weight cap and no
pair certificate are spent. -/
theorem polarPlaneCover_of_traceGramDet (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (selected : Finset (Fin m))
    {excess : ℝ}
    (htrace : 2 * (1 + excess) ≤ ∑ c ∈ selected, planeShadowSq design pole c)
    (hgram : (1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + excess) ^ 2
        ≤ polarPlaneGramDet design pole selected) :
    ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + excess) * (probe ⬝ᵥ probe)
        ≤ ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2 := by
  intro probe hprobe
  have hturnPole : planeReadVec design pole selected probe ⬝ᵥ design.atom pole = 0 :=
    planeReadVec_dotProduct_pole design hpole selected probe
  have hmix : probe ⬝ᵥ planeReadVec design pole selected probe
      = ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [planeReadVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [dotProduct_smul, smul_eq_mul,
      dotProduct_comm probe (planeShadowVec design pole d),
      planeShadowVec_dotProduct_polar design pole d hprobe]
    ring
  have hnorm : planeReadVec design pole selected probe
        ⬝ᵥ planeReadVec design pole selected probe
      = (∑ c ∈ selected, planeShadowSq design pole c)
          * (∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2)
        - polarPlaneGramDet design pole selected * (probe ⬝ᵥ probe) := by
    have hch := planeReadVec_planeReadVec design hpole selected hprobe
    have hself : planeReadVec design pole selected probe
          ⬝ᵥ planeReadVec design pole selected probe
        = probe ⬝ᵥ planeReadVec design pole selected
            (planeReadVec design pole selected probe) :=
      planeReadVec_dotProduct_symm design pole selected hprobe hturnPole
    rw [hself, hch, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, hmix]
  have hcs : (probe ⬝ᵥ planeReadVec design pole selected probe) ^ 2
      ≤ (probe ⬝ᵥ probe)
        * (planeReadVec design pole selected probe
            ⬝ᵥ planeReadVec design pole selected probe) :=
    dotProduct_sq_le_mul_self probe (planeReadVec design pole selected probe)
  rw [hmix, hnorm] at hcs
  have hnonneg : (0 : ℝ) ≤ probe ⬝ᵥ probe := selfDotProduct_nonneg probe
  by_contra hcontra
  have hlt : ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2
      < (1 + excess) * (probe ⬝ᵥ probe) := not_le.mp hcontra
  have hgramScaled : 0 ≤ (probe ⬝ᵥ probe) ^ 2
      * (polarPlaneGramDet design pole selected
        - ((1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + excess) ^ 2)) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hkey : (∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2
        - (1 + excess) * (probe ⬝ᵥ probe))
      * ((∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2)
        + (1 + excess) * (probe ⬝ᵥ probe)
        - (probe ⬝ᵥ probe) * (∑ c ∈ selected, planeShadowSq design pole c)) ≤ 0 := by
    nlinarith [hcs, hgramScaled]
  have hnegLeft : ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2
      - (1 + excess) * (probe ⬝ᵥ probe) < 0 := by linarith
  have hposRight : 0 ≤ (∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2)
      + (1 + excess) * (probe ⬝ᵥ probe)
      - (probe ⬝ᵥ probe) * (∑ c ∈ selected, planeShadowSq design pole c) := by
    by_contra hbad
    have hneg := not_le.mp hbad
    nlinarith [hkey, hnegLeft, hneg]
  have htraceScaled : (probe ⬝ᵥ probe) * (2 * (1 + excess))
      ≤ (probe ⬝ᵥ probe) * (∑ c ∈ selected, planeShadowSq design pole c) :=
    mul_le_mul_of_nonneg_left htrace hnonneg
  linarith

/-- **THE PLANE DETERMINANT IS POSITIVE UNDER THE DIRECT COVER.**  The same
two bounds already force the survivor plane form to beat the identity
strictly, thus the closed kill needs no separate hypothesis. -/
theorem polarPlaneDet_pos_of_traceGramDet {size rank : ℕ} (design : WeightedDesign size rank)
    (pole : Fin size) (selected : Finset (Fin size)) {excess : ℝ} (hexcessPos : 0 < excess)
    (htrace : 2 * (1 + excess) ≤ ∑ c ∈ selected, planeShadowSq design pole c)
    (hgram : (1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + excess) ^ 2
        ≤ polarPlaneGramDet design pole selected) :
    0 < polarPlaneDet design pole selected := by
  rw [polarPlaneDet_eq]
  nlinarith [htrace, hgram, hexcessPos]

/-! ### The wedge form of the plane Gram determinant and the signed cancellation -/

/-- **THE PLANE GRAM DETERMINANT IS A SUM OF SQUARED WEDGES.**  Twice the
leverage times the plane Gram determinant of a set is the double sum of the
squared anchored brackets of the set.  Thus the cover hypothesis of the direct
kill reads: the survivors are mutually spread in the pole plane. -/
theorem sum_tripleBracket_sq_eq_planeGramDet (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (selected : Finset (Fin m)) :
    ∑ c ∈ selected, ∑ d ∈ selected,
        tripleBracket (design.atom pole) (design.atom c) (design.atom d) ^ 2
      = 2 * (design.atom pole ⬝ᵥ design.atom pole)
        * polarPlaneGramDet design pole selected := by
  have hterm : ∀ c ∈ selected, ∀ d ∈ selected,
      tripleBracket (design.atom pole) (design.atom c) (design.atom d) ^ 2
        = (design.atom pole ⬝ᵥ design.atom pole)
          * (planeShadowSq design pole c * planeShadowSq design pole d
            - planeShadowPairing design pole c d ^ 2) := fun c _ d _ =>
    tripleBracket_sq_eq_planeShadow design hpole c d
  rw [polarPlaneGramDet, Finset.sum_congr rfl fun c hc =>
    Finset.sum_congr rfl fun d hd => hterm c hc d hd]
  have hinner : ∀ c : Fin m,
      (∑ d ∈ selected, (design.atom pole ⬝ᵥ design.atom pole)
          * (planeShadowSq design pole c * planeShadowSq design pole d
            - planeShadowPairing design pole c d ^ 2))
        = (design.atom pole ⬝ᵥ design.atom pole)
          * ∑ d ∈ selected, (planeShadowSq design pole c * planeShadowSq design pole d
            - planeShadowPairing design pole c d ^ 2) := by
    intro c
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun c _ => hinner c, ← Finset.mul_sum]
  ring

/-- The plane Gram determinant of a set is never negative. -/
theorem polarPlaneGramDet_nonneg (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (selected : Finset (Fin m)) :
    0 ≤ polarPlaneGramDet design pole selected := by
  have hsum : 0 ≤ ∑ c ∈ selected, ∑ d ∈ selected,
      tripleBracket (design.atom pole) (design.atom c) (design.atom d) ^ 2 :=
    Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => sq_nonneg _
  rw [sum_tripleBracket_sq_eq_planeGramDet design hpole selected] at hsum
  nlinarith [hsum, hpole]

/-- **THE SIGNED CANCELLATION AGAINST A BRACKET.**  The cross moment against a
bracket is a sum of terms carried by positive weights, thus over the reals the
terms cannot all be positive.  The complex law carries the CONJUGATE of the
pole reading, thus it gives no sign at all: this is the real-only exit of the
pole plane. -/
theorem exists_nonpos_pairing_mul_tripleBracket (design : WeightedDesign m 3)
    (pole label : Fin m) :
    ∃ c : Fin m, (design.atom c ⬝ᵥ design.atom pole)
        * tripleBracket (design.atom pole) (design.atom c) (design.atom label) ≤ 0 := by
  by_contra hcontra
  have hpos : ∀ c : Fin m, 0 < (design.atom c ⬝ᵥ design.atom pole)
      * tripleBracket (design.atom pole) (design.atom c) (design.atom label) := by
    intro c
    exact not_le.mp fun hle => hcontra ⟨c, hle⟩
  have hsum : 0 < ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom pole)
      * tripleBracket (design.atom pole) (design.atom c) (design.atom label) := by
    refine Finset.sum_pos (fun c _ => ?_) ⟨pole, Finset.mem_univ pole⟩
    have := mul_pos (design.weight_pos c) (hpos c)
    calc (0 : ℝ) < design.weight c * ((design.atom c ⬝ᵥ design.atom pole)
          * tripleBracket (design.atom pole) (design.atom c) (design.atom label)) := this
      _ = design.weight c * (design.atom c ⬝ᵥ design.atom pole)
          * tripleBracket (design.atom pole) (design.atom c) (design.atom label) := by ring
  rw [sum_weight_pairing_mul_tripleBracket design pole label] at hsum
  exact lt_irrefl 0 hsum

/-- The mirror of the signed cancellation: the terms cannot all be negative. -/
theorem exists_nonneg_pairing_mul_tripleBracket (design : WeightedDesign m 3)
    (pole label : Fin m) :
    ∃ c : Fin m, 0 ≤ (design.atom c ⬝ᵥ design.atom pole)
        * tripleBracket (design.atom pole) (design.atom c) (design.atom label) := by
  by_contra hcontra
  have hneg : ∀ c : Fin m, (design.atom c ⬝ᵥ design.atom pole)
      * tripleBracket (design.atom pole) (design.atom c) (design.atom label) < 0 := by
    intro c
    exact not_le.mp fun hle => hcontra ⟨c, hle⟩
  have hsum : ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom pole)
      * tripleBracket (design.atom pole) (design.atom c) (design.atom label) < 0 := by
    refine Finset.sum_neg (fun c _ => ?_) ⟨pole, Finset.mem_univ pole⟩
    have := mul_neg_of_pos_of_neg (design.weight_pos c) (hneg c)
    calc design.weight c * (design.atom c ⬝ᵥ design.atom pole)
          * tripleBracket (design.atom pole) (design.atom c) (design.atom label)
        = design.weight c * ((design.atom c ⬝ᵥ design.atom pole)
          * tripleBracket (design.atom pole) (design.atom c) (design.atom label)) := by ring
      _ < 0 := this
  rw [sum_weight_pairing_mul_tripleBracket design pole label] at hsum
  exact lt_irrefl 0 hsum

/-- **THE SIGNED CANCELLATION AGAINST A PAIRING.**  The same law read against a
shadow: the pairing-weighted shadow row of a label cannot be one-signed. -/
theorem exists_nonpos_pairing_mul_planeShadowPairing (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (label : Fin m) :
    ∃ c : Fin m, (design.atom c ⬝ᵥ design.atom pole)
        * planeShadowPairing design pole c label ≤ 0 := by
  by_contra hcontra
  have hpos : ∀ c : Fin m, 0 < (design.atom c ⬝ᵥ design.atom pole)
      * planeShadowPairing design pole c label := by
    intro c
    exact not_le.mp fun hle => hcontra ⟨c, hle⟩
  have hsum : 0 < ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom pole)
      * planeShadowPairing design pole c label := by
    refine Finset.sum_pos (fun c _ => ?_) ⟨pole, Finset.mem_univ pole⟩
    have := mul_pos (design.weight_pos c) (hpos c)
    calc (0 : ℝ) < design.weight c * ((design.atom c ⬝ᵥ design.atom pole)
          * planeShadowPairing design pole c label) := this
      _ = design.weight c * (design.atom c ⬝ᵥ design.atom pole)
          * planeShadowPairing design pole c label := by ring
  rw [sum_weight_pairing_mul_planeShadowPairing design hpole label] at hsum
  exact lt_irrefl 0 hsum

end DirectCover


/-! ## Part 4: the arithmetic form of the sharp tie law

The reading of the coupling vector against the closed cross witness is the
leverage times a polynomial in the shadow data.  Thus the witnessed Schur kill
loses its last vector, and the sharp tie law of the deciding cell becomes
arithmetic. -/

section ArithmeticLaw

variable {m : ℕ}

/-- **THE SHADOW ADJUGATE FORM.**  The adjugate of the survivor plane form
applied to the coupling vector, in the shadow data alone: the shadow trace
minus one, times the coupling energy, minus the sum of the squared survivor
readings of the coupling vector. -/
noncomputable def polarShadowAdjugate {size rank : ℕ} (design : WeightedDesign size rank)
    (pole : Fin size) (selected : Finset (Fin size)) : ℝ :=
  ((∑ c ∈ selected, planeShadowSq design pole c) - 1)
      * (∑ c ∈ selected, ∑ d ∈ selected,
          (design.atom c ⬝ᵥ design.atom pole) * (design.atom d ⬝ᵥ design.atom pole)
            * planeShadowPairing design pole c d)
    - ∑ c ∈ selected,
        (∑ d ∈ selected,
          (design.atom d ⬝ᵥ design.atom pole) * planeShadowPairing design pole c d) ^ 2

/-- An atom reads the coupling vector as the pairing-weighted shadow row. -/
theorem atom_dotProduct_polarCouplingVec (design : WeightedDesign m 3) (pole : Fin m)
    (selected : Finset (Fin m)) (label : Fin m) :
    design.atom label ⬝ᵥ polarCouplingVec design pole selected
      = ∑ d ∈ selected,
          (design.atom d ⬝ᵥ design.atom pole) * planeShadowPairing design pole label d := by
  rw [polarCouplingVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun d _ => by
    rw [dotProduct_smul, smul_eq_mul, atom_dotProduct_planeShadowVec]

/-- A shadow reads the coupling vector as the same row. -/
theorem planeShadowVec_dotProduct_polarCouplingVec (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (selected : Finset (Fin m)) (label : Fin m) :
    polarCouplingVec design pole selected ⬝ᵥ planeShadowVec design pole label
      = ∑ d ∈ selected,
          (design.atom d ⬝ᵥ design.atom pole) * planeShadowPairing design pole label d := by
  rw [polarCouplingVec, sum_dotProduct]
  exact Finset.sum_congr rfl fun d _ => by
    rw [smul_dotProduct, smul_eq_mul, planeShadowVec_dotProduct_pair design hpole d label,
      planeShadowPairing_comm design pole d label]

/-- The coupling energy in the shadow data. -/
theorem polarCouplingVec_dotProduct_self (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (selected : Finset (Fin m)) :
    polarCouplingVec design pole selected ⬝ᵥ polarCouplingVec design pole selected
      = ∑ c ∈ selected, ∑ d ∈ selected,
          (design.atom c ⬝ᵥ design.atom pole) * (design.atom d ⬝ᵥ design.atom pole)
            * planeShadowPairing design pole c d := by
  have hone : polarCouplingVec design pole selected
      = ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole)
          • planeShadowVec design pole c := rfl
  calc polarCouplingVec design pole selected ⬝ᵥ polarCouplingVec design pole selected
      = (∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole)
            • planeShadowVec design pole c)
          ⬝ᵥ polarCouplingVec design pole selected := by rw [hone]
    _ = ∑ c ∈ selected, ∑ d ∈ selected,
          (design.atom c ⬝ᵥ design.atom pole) * (design.atom d ⬝ᵥ design.atom pole)
            * planeShadowPairing design pole c d := by
        rw [sum_dotProduct]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [smul_dotProduct, smul_eq_mul,
          dotProduct_comm (planeShadowVec design pole c)
            (polarCouplingVec design pole selected),
          planeShadowVec_dotProduct_polarCouplingVec design hpole selected c,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by ring

/-- **THE WITNESSED TEST IS ARITHMETIC.**  The coupling vector reads the closed
cross witness as the leverage times the shadow adjugate form.  Every vector
leaves the sharp tie law here. -/
theorem polarCouplingVec_dotProduct_polarCrossWitnessVec (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (selected : Finset (Fin m)) :
    polarCouplingVec design pole selected ⬝ᵥ polarCrossWitnessVec design pole selected
      = (design.atom pole ⬝ᵥ design.atom pole)
        * polarShadowAdjugate design pole selected := by
  rw [polarCrossWitnessVec_eq_adj design hpole selected, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, dotProduct_smul, smul_eq_mul, dotProduct_sum,
    polarCouplingVec_dotProduct_self design hpole selected, polarShadowAdjugate]
  have hterm : ∀ c ∈ selected,
      polarCouplingVec design pole selected
          ⬝ᵥ (design.atom c ⬝ᵥ polarCouplingVec design pole selected)
            • planeShadowVec design pole c
        = (∑ d ∈ selected,
            (design.atom d ⬝ᵥ design.atom pole)
              * planeShadowPairing design pole c d) ^ 2 := by
    intro c _
    rw [dotProduct_smul, smul_eq_mul, atom_dotProduct_polarCouplingVec,
      planeShadowVec_dotProduct_polarCouplingVec design hpole selected c]
    ring
  rw [Finset.sum_congr rfl hterm]
  ring

/-- **THE ARITHMETIC SCHUR KILL OF RANK THREE.**  At every size, a tie carries
no pole and no triple whose shadow trace and plane Gram determinant clear the
two cover bounds, whose pole mass beats the leverage, and whose shadow
adjugate form stays below the plane determinant times the gap.  Every
hypothesis is a polynomial inequality in the leverage, the pole readings, the
shadow energies and the shadow pairings: no vector, no weight cap, no pair
certificate, and no witness. -/
theorem not_isTie_of_planeShadowSchur_rank_three (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {selected : Finset (Fin m)} (hcard : selected.card = 3)
    {excess : ℝ} (hexcessPos : 0 < excess)
    (htrace : 2 * (1 + excess) ≤ ∑ c ∈ selected, planeShadowSq design pole c)
    (hgram : (1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + excess) ^ 2
        ≤ polarPlaneGramDet design pole selected)
    (hz : design.atom pole ⬝ᵥ design.atom pole
        < ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
    (htest : polarShadowAdjugate design pole selected
        < polarPlaneDet design pole selected
          * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
            - design.atom pole ⬝ᵥ design.atom pole)) :
    ¬ IsTie design := by
  intro htie
  have hcover := polarPlaneCover_of_traceGramDet design hpole selected htrace hgram
  have hplaneDetPos := polarPlaneDet_pos_of_traceGramDet design pole selected hexcessPos
    htrace hgram
  have hkappa : 0 < (design.atom pole ⬝ᵥ design.atom pole)
      * polarPlaneDet design pole selected := mul_pos hpole hplaneDetPos
  have hVu : polarCouplingVec design pole selected
        ⬝ᵥ polarCrossWitnessVec design pole selected
      < ((design.atom pole ⬝ᵥ design.atom pole) * polarPlaneDet design pole selected)
        * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
          - design.atom pole ⬝ᵥ design.atom pole) := by
    rw [polarCouplingVec_dotProduct_polarCrossWitnessVec design hpole selected]
    calc (design.atom pole ⬝ᵥ design.atom pole) * polarShadowAdjugate design pole selected
        < (design.atom pole ⬝ᵥ design.atom pole)
            * (polarPlaneDet design pole selected
              * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
                - design.atom pole ⬝ᵥ design.atom pole)) :=
          mul_lt_mul_of_pos_left htest hpole
      _ = ((design.atom pole ⬝ᵥ design.atom pole) * polarPlaneDet design pole selected)
            * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
              - design.atom pole ⬝ᵥ design.atom pole) := by ring
  have hposDef := posDef_of_polarWitnessSchur_scaled design hpole hexcessPos hcover hz hkappa
    (polarCrossWitnessVec_dotProduct_pole design hpole selected)
    (polarCrossWitnessVec_witness design hpole selected) hVu
  exact htie.2 selected hcard hposDef

/-- The arithmetic kill at the deciding cell. -/
theorem not_isTie_of_planeShadowSchur_six_three (design : WeightedDesign 6 3)
    {pole : Fin 6} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    {excess : ℝ} (hexcessPos : 0 < excess)
    (htrace : 2 * (1 + excess) ≤ ∑ c ∈ selected, planeShadowSq design pole c)
    (hgram : (1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + excess) ^ 2
        ≤ polarPlaneGramDet design pole selected)
    (hz : design.atom pole ⬝ᵥ design.atom pole
        < ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
    (htest : polarShadowAdjugate design pole selected
        < polarPlaneDet design pole selected
          * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
            - design.atom pole ⬝ᵥ design.atom pole)) :
    ¬ IsTie design :=
  not_isTie_of_planeShadowSchur_rank_three design hpole hcard hexcessPos htrace hgram hz htest

/-- **THE ARITHMETIC TIE LAW OF THE DECIDING CELL.**  At every `(6,3)` tie,
every pole of positive leverage, every triple whose shadow trace and plane
Gram determinant clear the two cover bounds: the triple keeps its pole mass at
or below the leverage, or its shadow adjugate form already spends the whole
plane budget.  The banked `Gtz.tie_crossWitnessSchur_six_three` still carries
a pair certificate, a weight cap and two vectors; this law carries none of
them.  The probes show the complex ties of the deciding cell saturate it with
equality, and that the real family clears it with margin. -/
theorem tie_planeShadowSchur_six_three (design : WeightedDesign 6 3) (htie : IsTie design)
    {pole : Fin 6} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    {excess : ℝ} (hexcessPos : 0 < excess)
    (htrace : 2 * (1 + excess) ≤ ∑ c ∈ selected, planeShadowSq design pole c)
    (hgram : (1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + excess) ^ 2
        ≤ polarPlaneGramDet design pole selected) :
    (∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
        ≤ design.atom pole ⬝ᵥ design.atom pole
      ∨ polarPlaneDet design pole selected
          * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
            - design.atom pole ⬝ᵥ design.atom pole)
        ≤ polarShadowAdjugate design pole selected := by
  by_contra hcontra
  rw [not_or, not_le, not_le] at hcontra
  exact not_isTie_of_planeShadowSchur_six_three design hpole hcard hexcessPos htrace hgram
    hcontra.1 hcontra.2 htie

end ArithmeticLaw

/-! ## Part 5: the residual, narrowed a sixth time

The arithmetic law costs nothing at a tie, thus the residual can hand it to
the prover.  The guard `rank = 3` sits inside the bundle, thus the bundle is
vacuously free at every other rank and every calibration transports. -/

section PlaneBundle

variable {size rank : ℕ}

/-- **THE PLANE SHADOW BOUND.**  What a tie supplies at a pole of rank three:
for every triple whose shadow trace and plane Gram determinant clear the two
cover bounds, the triple keeps its pole mass at or below the leverage or its
shadow adjugate form spends the whole plane budget. -/
def PolarPlaneShadowBound (design : WeightedDesign size rank) (pole : Fin size) : Prop :=
  rank = 3 → 0 < design.atom pole ⬝ᵥ design.atom pole →
    ∀ selected : Finset (Fin size), selected.card = 3 →
      ∀ excess : ℝ, 0 < excess →
        2 * (1 + excess) ≤ ∑ c ∈ selected, planeShadowSq design pole c →
        (1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + excess) ^ 2
            ≤ polarPlaneGramDet design pole selected →
          (∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
              ≤ design.atom pole ⬝ᵥ design.atom pole
            ∨ polarPlaneDet design pole selected
                * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
                  - design.atom pole ⬝ᵥ design.atom pole)
              ≤ polarShadowAdjugate design pole selected

/-- **THE PLANE SHADOW BOUND IS FREE AT EVERY TIE.**  No predecessor rank, no
primitivity, no overshooting pole and no size guard are consumed. -/
theorem polarPlaneShadowBound_of_isTie (design : WeightedDesign size rank)
    (htie : IsTie design) (pole : Fin size) : PolarPlaneShadowBound design pole := by
  intro hrank hpole selected hcard excess hexcessPos htrace hgram
  subst hrank
  by_contra hcontra
  rw [not_or, not_le, not_le] at hcontra
  exact not_isTie_of_planeShadowSchur_rank_three design hpole hcard hexcessPos htrace hgram
    hcontra.1 hcontra.2 htie

/-- **THE SIX-BUNDLE TILT RESIDUAL.**  `Gtz.PolarTiltSelectionWitness` with the
arithmetic plane shadow bound handed to the prover as well. -/
def PolarTiltSelectionPlane (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (pole : Fin size) (covering : Finset (Fin size))
      (margin : ℝ),
    IsPrimitiveDesign design →
    IsTie design →
    1 < design.atom pole ⬝ᵥ design.atom pole →
    PolarSaturationBudget design pole →
    PolarDeletionHeavy design pole →
    PolarSetDeletionHeavy design pole →
    PolarSpreadSurvivorHeavy design pole →
    PolarWitnessSchurBound design pole →
    PolarPlaneShadowBound design pole →
    0 < margin →
    covering.card = rank - 1 → pole ∉ covering →
    (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) →
    ∃ selected : Finset (Fin size), selected.card = rank - 1 ∧ pole ∉ selected
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2)
      ∧ ∑ label ∈ selected, (design.atom label ⬝ᵥ design.atom pole) ^ 2
          < margin * (design.atom pole ⬝ᵥ design.atom pole)
              * (design.atom pole ⬝ᵥ design.atom pole - 1)

/-- The six-bundle residual is weaker than the five-bundle one. -/
theorem polarTiltSelectionPlane_of_polarTiltSelectionWitness
    (htilt : PolarTiltSelectionWitness size rank) : PolarTiltSelectionPlane size rank :=
  fun design pole covering margin hprimitive htie hlong hbudget hheavy hset hspread hwitness
    _hplane hmargin hcard hnotMem hcover =>
    htilt design pole covering margin hprimitive htie hlong hbudget hheavy hset hspread
      hwitness hmargin hcard hnotMem hcover

/-- The six-bundle residual is weaker than the four-bundle one. -/
theorem polarTiltSelectionPlane_of_polarTiltSelectionSpread
    (htilt : PolarTiltSelectionSpread size rank) : PolarTiltSelectionPlane size rank :=
  polarTiltSelectionPlane_of_polarTiltSelectionWitness
    (polarTiltSelectionWitness_of_polarTiltSelectionSpread htilt)

/-- The six-bundle residual is weaker than the shipped one. -/
theorem polarTiltSelectionPlane_of_polarTiltSelection
    (htilt : PolarTiltSelection size rank) : PolarTiltSelectionPlane size rank :=
  polarTiltSelectionPlane_of_polarTiltSelectionWitness
    (polarTiltSelectionWitness_of_polarTiltSelection htilt)

/-- **THE HINGE FROM THE SIX-BUNDLE RESIDUAL.**  All six bundles are theorems
at a tie, thus the sixth narrowing costs nothing downstream. -/
theorem hingeHoldsAtSize_of_polarTiltPlane (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionPlane size rank) : HingeHoldsAtSize size rank := by
  classical
  intro design htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  obtain ⟨pole, hlong⟩ := exists_overshooting_atom design hrank
  obtain ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin hrank hpredecessor design hlong
  obtain ⟨selected, hselCard, hselNotMem, hselCover, hselTilt⟩ :=
    htilt design pole covering margin hprimitive htie hlong
      (polarSaturationBudget_of_isTie hrank hpredecessor design htie hlong)
      (polarDeletionHeavy_of_isTie hrank hpredecessor design htie hlong hroom)
      (polarSetDeletionHeavy_of_isTie hrank hpredecessor design htie hlong)
      (polarSpreadSurvivorHeavy_of_isTie hrank hpredecessor design htie hlong)
      (polarWitnessSchurBound_of_isTie design htie pole)
      (polarPlaneShadowBound_of_isTie design htie pole)
      hmarginPos hcard hnotMem hcover
  have hposDef := posDef_insert_of_polarCover design hselNotMem hlong hmarginPos hselCover
    hselTilt
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hselNotMem, hselCard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-! ### Every consumer of the shipped residual, on the six-bundle one -/

/-- Arm (i). -/
theorem stressFreeArmAt_of_polarTiltPlane (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionPlane size rank) : StressFreeArmAt size rank :=
  fun design _hfree htie =>
    hingeHoldsAtSize_of_polarTiltPlane hrank hpredecessor hroom htilt design htie

/-- Arm (ii). -/
theorem balancedArmAt_of_polarTiltPlane (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionPlane size rank) : BalancedArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltPlane hrank hpredecessor hroom htilt design htie

/-- Arm (iii). -/
theorem degenerateArmAt_of_polarTiltPlane (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionPlane size rank) : DegenerateArmAt size rank :=
  fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
    hingeHoldsAtSize_of_polarTiltPlane hrank hpredecessor hroom htilt design htie

/-- The partial-support sub-arm. -/
theorem balancedPartialSupportArmAt_of_polarTiltPlane (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionPlane size rank) : BalancedPartialSupportArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hunsupported _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltPlane hrank hpredecessor hroom htilt design htie

/-- The full-support sub-arm. -/
theorem balancedFullSupportArmAt_of_polarTiltPlane (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionPlane size rank) : BalancedFullSupportArmAt size rank :=
  fun design _stressCoeff _hstress _hfull htie =>
    hingeHoldsAtSize_of_polarTiltPlane hrank hpredecessor hroom htilt design htie

/-- The repaired degenerate cover. -/
theorem degenerateHyperplaneCover_of_polarTiltPlane (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionPlane size rank) : DegenerateHyperplaneCover size rank := by
  intro design _stressCoeff _unitNormal _pole hprimitive htie _hstressNe _hunit _hstress
    _hsupport _hpole
  exact absurd
    (hingeHoldsAtSize_of_polarTiltPlane hrank hpredecessor hroom htilt design htie)
    ((isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive)

/-- **THE COLLAPSE, ON THE SIX-BUNDLE RESIDUAL.** -/
theorem polarTiltPlane_closes_every_arm (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionPlane size rank) :
    HingeHoldsAtSize size rank ∧ StressFreeArmAt size rank ∧ BalancedArmAt size rank
      ∧ DegenerateArmAt size rank ∧ BalancedPartialSupportArmAt size rank
      ∧ BalancedFullSupportArmAt size rank ∧ DegenerateHyperplaneCover size rank :=
  ⟨hingeHoldsAtSize_of_polarTiltPlane hrank hpredecessor hroom htilt,
    stressFreeArmAt_of_polarTiltPlane hrank hpredecessor hroom htilt,
    balancedArmAt_of_polarTiltPlane hrank hpredecessor hroom htilt,
    degenerateArmAt_of_polarTiltPlane hrank hpredecessor hroom htilt,
    balancedPartialSupportArmAt_of_polarTiltPlane hrank hpredecessor hroom htilt,
    balancedFullSupportArmAt_of_polarTiltPlane hrank hpredecessor hroom htilt,
    degenerateHyperplaneCover_of_polarTiltPlane hrank hpredecessor hroom htilt⟩

/-! ### The registry obligations, on the six-bundle residual -/

/-- The threshold cell obligation of the registry. -/
theorem thresholdCellHingeRankFourAndUp_of_polarTiltPlane
    (htilt : ∀ rank : ℕ, 4 ≤ rank → PolarTiltSelectionPlane (thresholdSize rank) rank) :
    ∀ rank : ℕ, 4 ≤ rank → GtzWeightedAll (rank - 1) →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor _hcell design htie
  have hroom : rank + 1 ≤ rank * (rank + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc (rank + 1) * 2 ≤ (rank + 1) * rank := Nat.mul_le_mul_left _ (by omega)
      _ = rank * (rank + 1) := Nat.mul_comm _ _
  exact hingeHoldsAtSize_of_polarTiltPlane (by omega) hpredecessor hroom (htilt rank hrank)
    design htie

/-- The sub-threshold band obligation of the registry. -/
theorem subThresholdBandHinge_of_polarTiltPlane
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size < thresholdSize rank →
      PolarTiltSelectionPlane size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor size hlow hhigh _hcell design htie
  exact hingeHoldsAtSize_of_polarTiltPlane (by omega) hpredecessor (by omega)
    (htilt rank size hrank hlow hhigh) design htie

/-- The whole sharp window, from one six-bundle residual per cell. -/
theorem sharpWindowHinge_of_polarTiltPlane
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size ≤ thresholdSize rank →
      PolarTiltSelectionPlane size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        HingeHoldsAtSize size rank := by
  intro rank hrank hpredecessor size hlow hhigh
  exact hingeHoldsAtSize_of_polarTiltPlane (by omega) hpredecessor (by omega)
    (htilt rank size hrank hlow hhigh)

/-- Arm (i) at the deciding cell of a rank. -/
theorem thresholdStressFreeArm_of_polarTiltPlane (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionPlane (thresholdSize rank) rank) :
    ThresholdStressFreeArm rank :=
  stressFreeArmAt_of_polarTiltPlane hrank hpredecessor hroom htilt

/-- Arm (ii) at the deciding cell of a rank. -/
theorem thresholdBalancedArm_of_polarTiltPlane (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionPlane (thresholdSize rank) rank) :
    ThresholdBalancedArm rank :=
  balancedArmAt_of_polarTiltPlane hrank hpredecessor hroom htilt

/-- Arm (iii) at the deciding cell of a rank. -/
theorem thresholdDegenerateArm_of_polarTiltPlane (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionPlane (thresholdSize rank) rank) :
    ThresholdDegenerateArm rank :=
  degenerateArmAt_of_polarTiltPlane hrank hpredecessor hroom htilt

end PlaneBundle

/-! ## Part 6: the deciding cell, the calibration, and the guardrail -/

section PlaneSixThree

/-- **THE DECIDING CELL OF RANK THREE FROM THE SIX-BUNDLE RESIDUAL ALONE.** -/
theorem hingeHoldsAtSize_six_three_of_polarTiltPlane
    (htilt : PolarTiltSelectionPlane 6 3) : HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_polarTiltPlane (by norm_num) gtz_rank_two (by norm_num) htilt

/-- The three rank-three arms from the six-bundle residual. -/
theorem thresholdArms_rank_three_of_polarTiltPlane (htilt : PolarTiltSelectionPlane 6 3) :
    ThresholdStressFreeArm 3 ∧ ThresholdBalancedArm 3 ∧ ThresholdDegenerateArm 3 := by
  have hhinge := hingeHoldsAtSize_six_three_of_polarTiltPlane htilt
  exact ⟨fun design _hfree htie => hhinge design htie,
    fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie => hhinge design htie,
    fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
      hhinge design htie⟩

/-- **THE DECIDING CELL, FROM THE SIX-BUNDLE RESIDUAL ALONE.** -/
theorem gtzWeighted_six_three_of_polarTiltPlane
    (htilt : PolarTiltSelectionPlane 6 3) : GtzWeighted 6 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltPlane htilt
  exact GeneralRankReach.gtzWeighted_six_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **ALL OF RANK THREE, FROM THE SIX-BUNDLE RESIDUAL ALONE.** -/
theorem gtzWeightedAll_three_of_polarTiltPlane
    (htilt : PolarTiltSelectionPlane 6 3) : GtzWeightedAll 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltPlane htilt
  exact GeneralRankReach.gtzWeightedAll_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **THE SIX-BUNDLE RESIDUAL IS FALSE AT `(5,3)`.**  The plane shadow bound is
free at every tie of every size, thus the calibration transports through the
sixth narrowing unchanged. -/
theorem not_polarTiltSelectionPlane_five_three : ¬ PolarTiltSelectionPlane 5 3 :=
  fun htilt => not_hingeHoldsAtSize_five_three
    (hingeHoldsAtSize_of_polarTiltPlane (by norm_num) gtz_rank_two (by norm_num) htilt)

/-- **THE GUARDRAIL.**  The `(6,3)` tie in the tree is not primitive, thus it
does not touch the six-bundle residual, and the last-stage Prop stays
refuted. -/
theorem sixSplitDiamondDesign_spares_polarTiltPlane :
    ¬ RankSuccShrinks 6 3 ∧ IsTie sixSplitDiamondDesign
      ∧ ¬ IsPrimitiveDesign sixSplitDiamondDesign
      ∧ ¬ PolarTiltSelectionPlane 5 3 :=
  ⟨not_rankSuccShrinks_six_three, sixSplitDiamondDesign_isTie,
    not_isPrimitiveDesign_sixSplitDiamondDesign, not_polarTiltSelectionPlane_five_three⟩

end PlaneSixThree

end Gtz
