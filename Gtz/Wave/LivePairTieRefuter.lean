import Gtz.Quantitative.TieRowLaw
import Gtz.Design.DepthCapAxisParseval
import Gtz.Design.KFourBandAtlas
import Gtz.Design.LivePairExistence
import Gtz.Wave.ConsolidatedStrictTriple

/-!
# The live-pair tie residual is false

`Gtz.stressFreeHingeHoldsSixThree_of_livePairTie` reduces the rank-three hinge to
a completeness input and one residual: at every weakly dominated design, every
live pair completes to a strictly positive tie leg.  The completeness input is
discharged (`Gtz.linearSpaceListIsComplete_six`), so the residual carried the
whole route.

This file refutes the residual with one exact rational design.  The design is
strictly dominated, so it is no counterexample to rank three -- what fails is
only the demand that EVERY live pair complete.

The witness carries the live pair `(0, 3)`, whose four completions all give a
strictly negative tie leg, while the triples `{0,1,2}`, `{0,1,4}` and `{0,1,5}`
each dominate strictly.

The failure is not a boundary effect.  An exact rational census over 693,878 live
pairs at three boxes finds no completion for `9.8` to `10.1` percent of them, and
`53.9` to `54.3` percent of weakly dominated designs carry at least one such pair.

The landed barrier `Gtz.sum_offPair_weight_mul_discriminantTie_neg` says the
weighted off-pair average of the tie leg is negative whenever the pivot carries
negative share surplus.  At size six the surpluses total `5 - 6 = -1`
(`Gtz.sum_shareSurplus`), so some label always carries a negative surplus
(`Gtz.exists_shareSurplus_neg` below).  In the census the failure rate inside
the barrier region is `17.2` to `17.6` percent, against `10` percent outside it.
The witness below is NOT in that region -- its pivot surplus is `65/96`, which is
positive -- so the barrier explains part of the phenomenon and not this instance.
-/

namespace Gtz

/-- The atoms of the refuter.  Six rational vectors in `ℝ³`. -/
noncomputable def livePairTieRefuterAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![-4/3, -4/3, 2/3]
  | 1 => ![-2/3, 0, -4/3]
  | 2 => ![-2/3, 4/3, 0]
  | 3 => ![0, 4/3, 2/3]
  | 4 => ![2/3, -4/3, -4/3]
  | 5 => ![-4/3, 4/3, 2/3]

/-- The weights of the refuter, a rational probability vector. -/
noncomputable def livePairTieRefuterWeight : Fin 6 → ℝ
  | 0 => 23/96
  | 1 => 7/16
  | 2 => 3/32
  | 3 => 1/32
  | 4 => 1/96
  | 5 => 3/16

/-- **The refuting design.**  Exact rational atoms and weights, Parseval on the
nose. -/
noncomputable def livePairTieRefuterDesign : WeightedDesign 6 3 where
  atom := livePairTieRefuterAtom
  weight := livePairTieRefuterWeight
  weight_pos := by
    intro label
    fin_cases label <;>
      norm_num [livePairTieRefuterWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    norm_num [livePairTieRefuterWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [livePairTieRefuterAtom, livePairTieRefuterWeight, atomMatrix,
        Matrix.cons_val_two] <;> norm_num

/-- The leverages of the refuter: `4, 20/9, 20/9, 20/9, 4, 4`. -/
theorem livePairTieRefuter_leverage (label : Fin 6) :
    leverageOf (livePairTieRefuterDesign.atom label)
      = ![4, 20/9, 20/9, 20/9, 4, 4] label := by
  fin_cases label <;>
    simp only [livePairTieRefuterDesign, livePairTieRefuterAtom, leverageOf,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] <;> norm_num

/-- **The pair `(0,3)` is live.**  Both gap excesses are positive and the two by
two gap minor is `17/9`. -/
theorem livePairTieRefuter_isLivePair :
    IsLivePair livePairTieRefuterDesign 0 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [gapExcessOf, pairGapExcessOf, gapPairingOf, leverageOf,
      livePairTieRefuterDesign, livePairTieRefuterAtom, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] <;> norm_num

/-- The tie leg at the completion `1`. -/
theorem livePairTieRefuter_tie_one :
    discriminantTie livePairTieRefuterDesign 0 3 1 = -5/81 := by
  simp only [discriminantTie, heavyExcess, atomPairing, leverageOf,
    livePairTieRefuterDesign, livePairTieRefuterAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

/-- The tie leg at the completion `2`. -/
theorem livePairTieRefuter_tie_two :
    discriminantTie livePairTieRefuterDesign 0 3 2 = -2861/729 := by
  simp only [discriminantTie, heavyExcess, atomPairing, leverageOf,
    livePairTieRefuterDesign, livePairTieRefuterAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

/-- The tie leg at the completion `4`. -/
theorem livePairTieRefuter_tie_four :
    discriminantTie livePairTieRefuterDesign 0 3 4 = -47/3 := by
  simp only [discriminantTie, heavyExcess, atomPairing, leverageOf,
    livePairTieRefuterDesign, livePairTieRefuterAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

/-- The tie leg at the completion `5`. -/
theorem livePairTieRefuter_tie_five :
    discriminantTie livePairTieRefuterDesign 0 3 5 = -8765/729 := by
  simp only [discriminantTie, heavyExcess, atomPairing, leverageOf,
    livePairTieRefuterDesign, livePairTieRefuterAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

/-- **No completion of the live pair `(0,3)` is strict.**  All four genuine
completions carry a strictly negative tie leg. -/
theorem livePairTieRefuter_no_completion (pairSecond : Fin 6)
    (hpivot : (0 : Fin 6) ≠ pairSecond) (hfirst : (3 : Fin 6) ≠ pairSecond) :
    ¬ (0 < discriminantTie livePairTieRefuterDesign 0 3 pairSecond) := by
  fin_cases pairSecond
  · exact absurd rfl hpivot
  · show ¬ (0 < discriminantTie livePairTieRefuterDesign 0 3 1)
    rw [livePairTieRefuter_tie_one]; norm_num
  · show ¬ (0 < discriminantTie livePairTieRefuterDesign 0 3 2)
    rw [livePairTieRefuter_tie_two]; norm_num
  · exact absurd rfl hfirst
  · show ¬ (0 < discriminantTie livePairTieRefuterDesign 0 3 4)
    rw [livePairTieRefuter_tie_four]; norm_num
  · show ¬ (0 < discriminantTie livePairTieRefuterDesign 0 3 5)
    rw [livePairTieRefuter_tie_five]; norm_num

/-- The gap of the triple `{0,1,2}`, read entrywise. -/
theorem livePairTieRefuter_gap_zeroOneTwo :
    subsetSum livePairTieRefuterDesign ({0, 1, 2} : Finset (Fin 6)) - 1
      = !![5/3, 8/9, 0; 8/9, 23/9, -8/9; 0, -8/9, 11/9] := by
  ext rowIndex colIndex
  rw [subsetSum]
  rw [show ({0, 1, 2} : Finset (Fin 6)) = {0, 1, 2} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [livePairTieRefuterDesign, livePairTieRefuterAtom, atomMatrix,
      Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.of_apply] <;> norm_num

/-- **The witness is strictly dominated at `{0,1,2}`.**  Sylvester on the explicit
gap: the leading minors are `5/3`, `281/81` and `2131/729`. -/
theorem livePairTieRefuter_posDef_zeroOneTwo :
    (subsetSum livePairTieRefuterDesign ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef := by
  rw [livePairTieRefuter_gap_zeroOneTwo]
  rw [posDef_finThree_iff_leadingMinors _ (by ext i j; fin_cases i <;> fin_cases j <;> norm_num)]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply, Matrix.cons_val'] <;> norm_num

/-- **The antecedent holds.**  The witness carries a dominating card-three
subset, so it is a weakly dominated design. -/
theorem livePairTieRefuter_dominates :
    ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧
      Dominates livePairTieRefuterDesign dominator :=
  ⟨({0, 1, 2} : Finset (Fin 6)), by decide,
    livePairTieRefuter_posDef_zeroOneTwo.posSemidef⟩

/-- **THE LIVE-PAIR TIE RESIDUAL IS FALSE.**  The hypothesis of
`Gtz.stressFreeHingeHoldsSixThree_of_livePairTie` fails at an exact rational
design that is itself strictly dominated. -/
theorem not_livePairTieResidual :
    ¬ (∀ design : WeightedDesign 6 3,
        (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
        ∀ pivotLabel pairFirst : Fin 6, pivotLabel ≠ pairFirst →
          IsLivePair design pivotLabel pairFirst →
          ∃ pairSecond, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
            ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond) := by
  intro hresidual
  obtain ⟨pairSecond, hpivot, hfirst, hpos⟩ :=
    hresidual livePairTieRefuterDesign livePairTieRefuter_dominates 0 3 (by decide)
      livePairTieRefuter_isLivePair
  exact livePairTieRefuter_no_completion pairSecond hpivot hfirst hpos

/-! ## The barrier region is never empty -/

/-- **Some label always carries a negative share surplus, past size five.**  The
surpluses total `5 - m` (`Gtz.sum_shareSurplus`), so beyond size five the total is
negative and one label must be.  This is the standing hypothesis of the landed
barrier `Gtz.sum_offPair_weight_mul_discriminantTie_neg`, so that barrier has a
nonempty region at every size the campaign cares about. -/
theorem exists_shareSurplus_neg {m : ℕ} (D : WeightedDesign m 3) (hsize : 5 < m) :
    ∃ atomIndex : Fin m, shareSurplus D atomIndex < 0 := by
  by_contra hnone
  push Not at hnone
  have hnonneg : (0 : ℝ) ≤ ∑ atomIndex, shareSurplus D atomIndex :=
    Finset.sum_nonneg fun atomIndex _ => hnone atomIndex
  rw [sum_shareSurplus D] at hnonneg
  have hcast : (5 : ℝ) < (m : ℝ) := by exact_mod_cast hsize
  linarith

/-! ## The repair: the existential form, which is Lane A-prime -/

/-- **The existential live-pair tie.**  The residual of
`Gtz.stressFreeHingeHoldsSixThree_of_livePairTie` asks every live pair to
complete.  This asks only that SOME live pair complete, which is what
`Gtz.exists_livePair_determinantOnly` leaves open. -/
def ExistsLivePairTieDesign : Prop :=
  ∀ design : WeightedDesign 6 3,
    ∃ pivotLabel pairFirst pairSecond : Fin 6,
      pivotLabel ≠ pairFirst ∧ pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
        ∧ 0 < heavyExcess design pivotLabel
        ∧ 0 < pairGapExcessOf design pivotLabel pairFirst
        ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond

/-- **The repaired route lands in the design consolidation.**  The existential
form supplies a strictly dominating card-three subset at every design, which is
exactly `Gtz.ConsolidatedStrictTripleDesign` -- and that statement discharges the
line-free, one-line and two-meeting-lines obligations together.  So the live-pair
route, once weakened from `∀` to `∃` as the refutation above forces, is not a new
lane: it is the design lane. -/
theorem consolidatedStrictTripleDesign_of_existsLivePairTie
    (hexists : ExistsLivePairTieDesign) : ConsolidatedStrictTripleDesign := by
  intro design _hprimitive
  obtain ⟨pivotLabel, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
    hpivotHeavy, hlive, hdeterminant⟩ := hexists design
  refine ⟨{pivotLabel, pairFirst, pairSecond}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hpivotFirst, hpivotSecond]),
      Finset.card_insert_of_notMem (by simp [hpairDistinct]), Finset.card_singleton]
  · exact posDef_subsetSum_sub_one_of_livePair design hpivotFirst hpivotSecond hpairDistinct
      hpivotHeavy hlive hdeterminant

/-- **The route is dead in its landed form and alive only as the design lane.**
The completeness input of `Gtz.stressFreeHingeHoldsSixThree_of_livePairTie` is
already discharged by `Gtz.linearSpaceListIsComplete_six`, so its residual carried
the whole route.  That residual is false, and the existential repair is the design
consolidation. -/
theorem livePairTieRoute_verdict :
    ¬ (∀ design : WeightedDesign 6 3,
        (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
        ∀ pivotLabel pairFirst : Fin 6, pivotLabel ≠ pairFirst →
          IsLivePair design pivotLabel pairFirst →
          ∃ pairSecond, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
            ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond)
      ∧ (ExistsLivePairTieDesign → ConsolidatedStrictTripleDesign) :=
  ⟨not_livePairTieResidual, consolidatedStrictTripleDesign_of_existsLivePairTie⟩

end Gtz
