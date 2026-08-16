/-
# The second-invariant layer of the twenty triples is weight-free

`Gtz.sum_powersetCard_secondInvariant_pos` reads the twenty-triple total of the
second invariant as a positive combination of the fifteen wedge energies, and it
pays for the positivity with the hypothesis `weight label < 1 / 5` at every
label.  This file removes that hypothesis and shows why it was never the right
one.

**The total does not see the weights at all.**  The fifteen coefficients
`4 - 10 (w_c + w_d) + 20 w_c w_d` are genuinely weight-dependent one pair at a
time, and the fifteen wedge energies are genuinely design-dependent, but the
whole contraction collapses:

  `sum_C e2(S_C - 1)  =  4 e2(N) - 20 tr N + 60` ,   `N = sum_c a_c a_c^T` .

The right side names no weight.  Two designs with the same unweighted moment
have the same layer total, whatever their weights are.  So no hypothesis on the
weights alone can be necessary for the positivity, and `hspread` is a proxy.

## What replaces the weight hypothesis

The identity turns the positivity into one scalar test on the unweighted moment,
with no eigenvalue and no weight:

  `0 < sum_C e2(S_C - 1)   <->   5 tr N < e2(N) + 15` .

That is an equivalence, so it is the sharp form.  `Gtz.subsetSum_univ_sub_one_posSemidef`
records the standing fact that `N` is at least the identity, which is what makes
the shifted spectrum nonnegative and the test readable.

## HONESTY — this closes the lane rather than opening it

The determinant layer at `(6, 3)` is already known to be a change of variables
rather than a constraint: `Gtz.sum_det_subsetSum_sub_one_sixThree_eq` reads it as
`det N - 4 e2(N) + 10 tr N - 20`, with no design hypothesis, and
`Gtz/Quantitative/WindowCofactorBridge.lean` records that such an identity
cannot separate a tie from a non-tie.  The law below shows the SECOND invariant
layer has exactly the same character.  The claim in section 9 of
`Gtz/Wave/WedgeBalanceAdjugate.lean` that the second invariant "behaves in the
opposite way" is true about the SIGN and false about the CONTENT: both layers are
weight-free functions of one three by three moment.

So this file does not advance the selector.  It states the sharp form of a landed
positivity, deletes a hypothesis from it, and records that the twenty-triple
second-invariant total is subject to the same no-go as the determinant total.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.WindowPolarity
import Gtz.Quantitative.CauchyBinetLayerSum
import Gtz.Wave.WedgeBalanceAdjugate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Finset Matrix

/-! ## 1. The second invariant of a three by three matrix, and the unit shift

`Gtz.secondInvariantOfThree` and `Gtz.principalMinorTotal _ 2` are the same
number at rank three.  The campaign carries both vocabularies, and the layer
sums are stated in the second, so the bridge is what lets the first reach them. -/

/-- The nine entries of a unit-shifted three by three matrix.  The diagonal drops
by one and the off-diagonal is unchanged.  Both shift laws below run on this. -/
theorem sub_one_apply_fin_three (form : Matrix (Fin 3) (Fin 3) ℝ) :
    (form - 1) 0 0 = form 0 0 - 1 ∧ (form - 1) 0 1 = form 0 1 ∧ (form - 1) 0 2 = form 0 2
      ∧ (form - 1) 1 0 = form 1 0 ∧ (form - 1) 1 1 = form 1 1 - 1 ∧ (form - 1) 1 2 = form 1 2
      ∧ (form - 1) 2 0 = form 2 0 ∧ (form - 1) 2 1 = form 2 1
      ∧ (form - 1) 2 2 = form 2 2 - 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.sub_apply]

/-- The determinant of a unit-shifted three by three matrix, in the three
elementary invariants.  Entrywise, hypothesis-free. -/
theorem det_sub_one_eq_secondInvariantOfThree (form : Matrix (Fin 3) (Fin 3) ℝ) :
    (form - 1).det
      = form.det - secondInvariantOfThree form + Matrix.trace form - 1 := by
  obtain ⟨e00, e01, e02, e10, e11, e12, e20, e21, e22⟩ := sub_one_apply_fin_three form
  simp only [Matrix.det_fin_three, secondInvariantOfThree, Matrix.trace_fin_three,
    e00, e01, e02, e10, e11, e12, e20, e21, e22]
  ring

/-- **THE BRIDGE.**  At rank three the level-two principal-minor total is the
second invariant.  Both names are in the corpus and neither reduces to the
other by `rfl`. -/
theorem principalMinorTotal_two_eq_secondInvariantOfThree (form : Matrix (Fin 3) (Fin 3) ℝ) :
    principalMinorTotal form 2 = secondInvariantOfThree form := by
  have hlevel := principalMinorTotal_two_fin_three form
  have hshift := det_sub_one_eq_secondInvariantOfThree form
  rw [hlevel, hshift]
  ring

/-- **THE UNIT SHIFT OF THE SECOND INVARIANT.**  `e2(M - 1) = e2 M - 2 tr M + 3`.
This is the middle coefficient of the characteristic cubic moved by one, and it
is the only place the shift enters the layer law. -/
theorem secondInvariantOfThree_sub_one (form : Matrix (Fin 3) (Fin 3) ℝ) :
    secondInvariantOfThree (form - 1)
      = secondInvariantOfThree form - 2 * Matrix.trace form + 3 := by
  obtain ⟨e00, e01, e02, e10, e11, e12, e20, e21, e22⟩ := sub_one_apply_fin_three form
  simp only [secondInvariantOfThree, Matrix.trace_fin_three,
    e00, e01, e02, e10, e11, e12, e20, e21, e22]
  ring

/-! ## 2. The layer law

Two landed layer counts do the work: each pair of `Fin 6` lies in four of the
twenty triples and each label lies in ten of them.  The shift contributes the
constant, because there are twenty triples. -/

/-- **THE SECOND-INVARIANT LAYER LAW AT `(6, 3)`.**  The twenty second invariants
of the gaps total `4 e2(N) - 20 tr N + 60`, where `N` is the unweighted moment
`sum_c a_c a_c^T` of the whole design.

The right side names NO weight.  The fifteen pair coefficients of
`Gtz.sum_powersetCard_secondInvariant_pos` are individually weight-dependent, and
their contraction against the fifteen wedge energies is not. -/
theorem sum_secondInvariantOfThree_subsetSum_sub_one_sixThree (design : WeightedDesign 6 3) :
    ∑ block ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        secondInvariantOfThree (subsetSum design block - 1)
      = 4 * secondInvariantOfThree (subsetSum design Finset.univ)
        - 20 * Matrix.trace (subsetSum design Finset.univ) + 60 := by
  classical
  have hpointwise : ∀ block : Finset (Fin 6),
      secondInvariantOfThree (subsetSum design block - 1)
        = principalMinorTotal (subsetSum design block) 2
          - 2 * Matrix.trace (subsetSum design block) + 3 := by
    intro block
    rw [secondInvariantOfThree_sub_one,
      principalMinorTotal_two_eq_secondInvariantOfThree]
  rw [Finset.sum_congr rfl fun block _ => hpointwise block]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_principalMinorTotal_two_subsetSum_sixThree design,
    sum_trace_subsetSum_sixThree design,
    principalMinorTotal_two_eq_secondInvariantOfThree (subsetSum design Finset.univ)]
  rw [Finset.sum_const, card_powersetCard_three_six]
  ring

/-! ## 3. The sharp test, and the deletion of the weight hypothesis -/

/-- **THE SHARP POSITIVITY TEST.**  An equivalence, so nothing is lost and no
weight appears.  The landed `Gtz.sum_powersetCard_secondInvariant_pos` is the
implication from `hspread` to the left side, and this is the exact condition. -/
theorem sum_secondInvariantOfThree_subsetSum_sub_one_pos_iff (design : WeightedDesign 6 3) :
    (0 < ∑ block ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        secondInvariantOfThree (subsetSum design block - 1))
      ↔ 5 * Matrix.trace (subsetSum design Finset.univ)
          < secondInvariantOfThree (subsetSum design Finset.univ) + 15 := by
  rw [sum_secondInvariantOfThree_subsetSum_sub_one_sixThree design]
  constructor
  · intro hpos; linarith
  · intro htest; linarith

/-- **SPREAD WEIGHTS FORCE A MOMENT INEQUALITY.**  The landed positivity is stated
with a hypothesis on the weights and a conclusion about the twenty gaps.  Read
through the layer law it becomes a statement in which NO weight appears at all:
a primitive design whose every weight is below one fifth has an unweighted moment
whose trace is controlled by its second invariant.

This is the exact content the weight hypothesis was buying, and it shows the
hypothesis was never about the layer.  It was a sufficient condition for one
inequality between two invariants of a single three by three matrix. -/
theorem trace_lt_secondInvariantOfThree_of_spread (design : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign design)
    (hspread : ∀ label : Fin 6, design.weight label < 1 / 5) :
    5 * Matrix.trace (subsetSum design Finset.univ)
      < secondInvariantOfThree (subsetSum design Finset.univ) + 15 :=
  (sum_secondInvariantOfThree_subsetSum_sub_one_pos_iff design).mp
    (sum_powersetCard_secondInvariant_pos design hprimitive hspread)

/-- **THE POSITIVITY, WITH NO WEIGHT HYPOTHESIS.**  The replacement for
`Gtz.sum_powersetCard_secondInvariant_pos`.  Primitivity is not needed either:
the moment test alone carries the conclusion. -/
theorem sum_secondInvariantOfThree_subsetSum_sub_one_pos_of_moment
    (design : WeightedDesign 6 3)
    (hmoment : 5 * Matrix.trace (subsetSum design Finset.univ)
      < secondInvariantOfThree (subsetSum design Finset.univ) + 15) :
    0 < ∑ block ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      secondInvariantOfThree (subsetSum design block - 1) :=
  (sum_secondInvariantOfThree_subsetSum_sub_one_pos_iff design).mpr hmoment

/-- **THE LAYER IS BLIND TO THE WEIGHTS.**  Two designs with the same unweighted
moment carry the same twenty-triple second-invariant total, whatever their
weights.  So no condition on the weights alone can be NECESSARY for the
positivity, and the hypothesis `weight label < 1 / 5` of
`Gtz.sum_powersetCard_secondInvariant_pos` is a proxy for a condition on `N`. -/
theorem sum_secondInvariantOfThree_congr_of_subsetSum_univ_eq
    (design other : WeightedDesign 6 3)
    (hmoment : subsetSum design Finset.univ = subsetSum other Finset.univ) :
    ∑ block ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        secondInvariantOfThree (subsetSum design block - 1)
      = ∑ block ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        secondInvariantOfThree (subsetSum other block - 1) := by
  rw [sum_secondInvariantOfThree_subsetSum_sub_one_sixThree design,
    sum_secondInvariantOfThree_subsetSum_sub_one_sixThree other, hmoment]

/-- **THE MOMENT DOMINATES THE IDENTITY.**  Every weight is at most one, so the
unweighted moment is at least the weighted one, which is the identity.  This is
what makes the shifted spectrum of `N` nonnegative. -/
theorem subsetSum_univ_sub_one_posSemidef {size rank : ℕ} (design : WeightedDesign size rank) :
    (subsetSum design Finset.univ - 1).PosSemidef := by
  classical
  have hweightLe : ∀ label : Fin size, design.weight label ≤ 1 := by
    intro label
    have hsum := design.weight_sum_one
    have hother : ∑ other ∈ Finset.univ.erase label, design.weight other
        = 1 - design.weight label := by
      have hinsert := Finset.add_sum_erase Finset.univ design.weight
        (Finset.mem_univ label)
      linarith [hinsert, hsum]
    have hnonneg : 0 ≤ ∑ other ∈ Finset.univ.erase label, design.weight other :=
      Finset.sum_nonneg fun other _ => (design.weight_pos other).le
    linarith [hother, hnonneg]
  have hsplit : subsetSum design Finset.univ - 1
      = ∑ label : Fin size, (1 - design.weight label) • atomMatrix (design.atom label) := by
    have hparseval := design.isParseval
    simp only [subsetSum, sub_smul, one_smul]
    rw [Finset.sum_sub_distrib, hparseval]
  rw [hsplit]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun left right => ?_)
    (Matrix.PosSemidef.zero) (fun label _ => ?_)
  · exact fun hleft hright => hleft.add hright
  · exact (posSemidef_atomMatrix (design.atom label)).smul (by linarith [hweightLe label])

/-! ## 4. The moment test is not automatic -/

/-- The stretched moment used to show the test has content. -/
def stretchedMoment : Matrix (Fin 3) (Fin 3) ℝ :=
  !![15, 0, 0; 0, 1, 0; 0, 0, 1]

/-- The stretched moment is at least the identity, so it obeys the standing
constraint of `Gtz.subsetSum_univ_sub_one_posSemidef`. -/
theorem stretchedMoment_sub_one_eq :
    stretchedMoment - 1 = !![14, 0, 0; 0, 0, 0; 0, 0, 0] := by
  ext row col
  fin_cases row <;> fin_cases col <;>
    norm_num [stretchedMoment, Matrix.sub_apply]

/-- **THE TEST HAS CONTENT.**  At the stretched moment the test fails, so the
layer law does not prove the positivity by itself.  The excess over the identity
is `diag(14, 0, 0)`, which is nonnegative, so the failure happens inside the
region the design constraint allows.

Whether a PRIMITIVE `(6, 3)` design realizes such a moment is NOT settled here.
A directed search over four hundred thousand strictly primitive designs found no
non-positive layer, and the only non-positive witnesses found carried an exactly
parallel pair [MEASURED, outside Lean]. -/
theorem not_moment_test_stretchedMoment :
    ¬ (5 * Matrix.trace stretchedMoment < secondInvariantOfThree stretchedMoment + 15) := by
  simp only [stretchedMoment, secondInvariantOfThree, Matrix.trace_fin_three,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_fin_const, Matrix.of_apply, Fin.isValue]
  norm_num

/-! ## 5. What the law says about the lane

The layer sum is an identity in the unweighted moment with no design hypothesis
on its right side.  `Gtz.sum_det_subsetSum_sub_one_sixThree_eq` is the same shape
one level up.  A functional of that shape is a change of variables, and the
campaign has already recorded that such a functional cannot separate a tie from a
non-tie.  The statement below is the formal version of that reading for the
second invariant: the whole twenty-triple total is recovered from three numbers
attached to a single three by three matrix. -/

/-- **THE TWO LAYERS TOGETHER.**  The second-invariant total and the determinant
total are both affine in the invariants of the SAME moment `N`, and their sum
eliminates `e2(N)` entirely.  Nothing on the right side mentions a weight, a
subset, or an atom. -/
theorem sum_secondInvariant_add_sum_det_sixThree (design : WeightedDesign 6 3) :
    (∑ block ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        secondInvariantOfThree (subsetSum design block - 1))
      + ∑ block ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        (subsetSum design block - 1).det
      = (subsetSum design Finset.univ).det
        - 10 * Matrix.trace (subsetSum design Finset.univ) + 40 := by
  have hsecond := sum_secondInvariantOfThree_subsetSum_sub_one_sixThree design
  have hdet := sum_det_subsetSum_sub_one_sixThree_eq design
  rw [hsecond, hdet, principalMinorTotal_two_eq_secondInvariantOfThree]
  ring

end Gtz
