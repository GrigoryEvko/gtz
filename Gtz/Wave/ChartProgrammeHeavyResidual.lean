/-
# The chart programme meets the tenth floor

`Gtz.stressFreeHingeHoldsSixThree_of_designUpgrade` reduces the rank-three
residual to ONE design-level statement: every weakly dominated design carries a
strictly dominating triple.  That statement is asked of every design, and part
of it is already proved.

`Gtz.exists_posDef_triple_of_weights_lt_tenth` produces a strictly dominating
triple for every design whose six weights are below one tenth, with NO weak
domination antecedent.  Spending it against the atlas gives the upgrade on the
HEAVY region only:

  every weakly dominated design that carries a weight of one tenth or more
  has a strictly dominating triple.

## The tenth floor is vacuous at six labels

The narrowing above is FORMAL, and this file proves that it is.  A weighted
design carries a probability vector on six labels, so its largest weight is at
least one sixth, and one sixth is larger than one tenth.  No design of six
labels has all six weights below one tenth.

`Gtz.not_forall_weight_lt_tenth` is that statement.  The light branch of the
tenth floor never fires at this size, so the heavy hypothesis is not weaker than
the plain one and the tenth floor buys nothing here.  The honest residual stays
`Gtz.stressFreeHingeHoldsSixThree_of_designUpgrade`, with no weight side
condition at all.

The heavy forms are still worth landing.  A prover that reaches the residual
through a weight-graded argument has the bound in hand, and these theorems
record that spending it costs nothing.  What the controls buy is the correction:
the tenth floor is not one of the layers that narrows this residual.
-/
import Gtz.Design.ChartProgrammeAssembly
import Gtz.Wave.ProjectionDictionary

namespace Gtz

/-- **THE ATLAS FROM THE HEAVY UPGRADE ALONE.**  Every admissible atlas point is
tie-free as soon as the weak-to-strict upgrade holds at designs that carry a
weight of one tenth or more.  The light designs are discharged by the landed
tenth floor. -/
theorem directionChartIsTieFree_atlas_of_heavyDesignUpgrade
    (hupgrade : ∀ design : WeightedDesign 6 3,
      (∃ label : Fin 6, 1 / 10 ≤ design.weight label) →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef)
    (point : StressFreeChartPoint) :
    DirectionChartIsTieFree point.direction := by
  refine directionChartIsTieFree_atlas_of_designUpgrade ?_ point
  intro design hweak
  by_cases hheavy : ∃ label : Fin 6, 1 / 10 ≤ design.weight label
  · exact hupgrade design hheavy hweak
  · push Not at hheavy
    exact exists_posDef_triple_of_weights_lt_tenth design hheavy

/-- The residual list from the heavy upgrade alone. -/
theorem stressFreeResidualFamiliesSix_tieFree_of_heavyDesignUpgrade
    (hupgrade : ∀ design : WeightedDesign 6 3,
      (∃ label : Fin 6, 1 / 10 ≤ design.weight label) →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    ∀ lines ∈ stressFreeResidualFamiliesSix,
      StressFreeStratumIsTieFree (lineFamilyPattern lines) :=
  stressFreeResidualFamiliesSix_tieFree_of_atlas
    fun point _ => directionChartIsTieFree_atlas_of_heavyDesignUpgrade hupgrade point

/-- **THE RANK-THREE HINGE FROM THE HEAVY UPGRADE ALONE.**  The stress-free
hinge at six labels and rank three follows from the enumeration input plus the
weak-to-strict upgrade asked ONLY of designs that carry a weight of one tenth or
more.  Every lighter design is already closed in the corpus. -/
theorem stressFreeHingeHoldsSixThree_of_heavyDesignUpgrade
    (hcomplete : LinearSpaceListIsComplete 6 linePatternListSix)
    (hupgrade : ∀ design : WeightedDesign 6 3,
      (∃ label : Fin 6, 1 / 10 ≤ design.weight label) →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    StressFreeHingeHoldsSixThree :=
  stressFreeHingeHoldsSixThree_of_atlas hcomplete
    fun point _ => directionChartIsTieFree_atlas_of_heavyDesignUpgrade hupgrade point

/-- **THE RANK-THREE HINGE FROM ONE DETERMINANT SIGN ON THE HEAVY REGION.**  The
sharpest statement of the rank-three residual the tree carries at this commit:
at every weakly dominated design that reaches the tenth floor, every live pair
completes to a strictly positive tie leg.  The whole chart programme, the five
coverings, the moment discharge and the tenth floor are spent together.

**#BOGUS — THIS DOOR CANNOT OPEN.**  `Gtz.not_heavyLivePairTieResidual`
(Gtz/Wave/WiringSynonymClass.lean) refutes the residual.  The tenth floor does
not rescue the door, because the landed witness
`Gtz.livePairTieRefuterDesign` carries weight `23/96` at label zero.  This is a
**#DUPLICATION** of `Gtz.stressFreeHingeHoldsSixThree_of_livePairTie`
(Gtz/Design/ChartProgrammeAssembly.lean:354), which dies to the same witness. -/
theorem stressFreeHingeHoldsSixThree_of_heavyLivePairTie
    (hcomplete : LinearSpaceListIsComplete 6 linePatternListSix)
    (hresidual : ∀ design : WeightedDesign 6 3,
      (∃ label : Fin 6, 1 / 10 ≤ design.weight label) →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∀ pivotLabel pairFirst : Fin 6, pivotLabel ≠ pairFirst →
        IsLivePair design pivotLabel pairFirst →
        ∃ pairSecond : Fin 6, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond) :
    StressFreeHingeHoldsSixThree :=
  stressFreeHingeHoldsSixThree_of_heavyDesignUpgrade hcomplete
    fun design hheavy hweak =>
      exists_posDef_cardThree_of_forall_livePair design (hresidual design hheavy hweak)

/-! ## Controls

The narrowing would be worthless if the heavy hypothesis were vacuous, or if it
were everything. -/

/-- **THE SIXTH FLOOR IS FREE.**  The weights are a probability vector on six
labels, so the largest of them is at least one sixth.  No hypothesis is needed
and none of the six weights can be small on its own account. -/
theorem exists_weight_one_sixth_le (design : WeightedDesign 6 3) :
    ∃ label : Fin 6, (1 : ℝ) / 6 ≤ design.weight label := by
  by_contra hsmall
  push Not at hsmall
  have hsum : ∑ label : Fin 6, design.weight label < ∑ _label : Fin 6, (1 : ℝ) / 6 :=
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩
      fun label _ => hsmall label
  rw [design.weight_sum_one] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  norm_num at hsum

/-- **THE TENTH FLOOR IS VACUOUS AT SIX LABELS.**  One sixth is larger than one
tenth, so no weighted design of six labels has all six weights below one tenth.
The light branch of `Gtz.exists_posDef_triple_of_weights_lt_tenth` never fires
at this size.  The heavy hypothesis above is therefore not weaker than the plain
design-level upgrade, and the tenth floor does not narrow this residual. -/
theorem not_forall_weight_lt_tenth (design : WeightedDesign 6 3) :
    ¬ (∀ label : Fin 6, design.weight label < 1 / 10) := by
  intro hlight
  obtain ⟨label, hlabel⟩ := exists_weight_one_sixth_le design
  have hten := hlight label
  norm_num at hlabel
  linarith

end Gtz
