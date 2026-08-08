/-
# The pair-cap engine: Sylvester transport of the tie leg, and the cap blind spot

`Gtz/Quantitative/TieRowLaw.lean` carries the pair-averaging layer already -- the
`e_3` pair row law `Gtz.sum_weight_mul_discriminantTie`, its off-pair form
`Gtz.sum_offPair_weight_mul_discriminantTie`, the positive criterion
`Gtz.exists_pos_discriminantTie_of_pos_surplusForm`, the surplus budget
`Gtz.sum_shareSurplus = 5 - m`, and the barrier
`Gtz.sum_offPair_weight_mul_discriminantTie_neg`.  None of that is re-derived
here.

The shipped criterion stops at `0 < discriminantTie`, which is only the THIRD
leading minor of the triple gap.  What this file adds:

* `surplusForm_eq_pairCapExcess` -- the surplus coordinates of the shipped
  off-pair law and the pair-cap coordinates are the SAME polynomial.  A `ring`
  identity, recorded so the two readings can never drift apart as two objects.
* `schurDeterminant_eq_heavyExcess_mul_discriminantTie` -- the Schur
  factorisation of the gap.  It makes the MIDDLE Sylvester minor a consequence
  of the corner and the tie leg rather than a hypothesis.
* `subsetSum_posDef_of_heavyPivot_of_minor_of_tie` -- Sylvester in the
  discriminant scalars: a heavy pivot, a positive leading pair minor and a
  positive tie leg give a genuinely strictly dominating triple.  This is the
  transport the shipped criterion was missing.
* `exists_posDef_triple_of_pairCapExcess` -- the engine with a positive definite
  conclusion and with BOTH Sylvester side conditions removed: under heaviness the
  cap excess alone forces the corner and the block minor.
* `pairCapExcess_le_of_no_strict_triple` -- the contrapositive tie law, a cap on
  every pair of a heavy design carrying no strictly dominating triple.  It is
  ATTAINED at the regular tetrahedron (`tetraDesign_pairCap_attained`), so it
  cannot be sharpened.
* `IsCapBlindSpot` and `patternHeavyWeakToStrict_of_capBlindSpot` -- the honest
  residual.  The whole chartless obligation, at ANY line pattern, follows from
  the cap blind spot alone: the designs at which no pair has positive cap excess.

The engine is not vacuous: it fires at the shipped one-line witness
`Gtz.narrowConeDesign` on the pair `{4, 5}`.
-/
import Gtz.Quantitative.TieRowLaw
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Design.RhoNormalForm
import Gtz.Reduction.RealVolumeFloor
import Gtz.Design.InPlaneRestriction
import Gtz.Design.LineClassObstructions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## Part 1: the two readings of the off-pair row law are one polynomial -/

/-- **The surplus form and the pair-cap excess agree.**  The scalar that
`Gtz.sum_offPair_weight_mul_discriminantTie` evaluates the off-pair average to,
written in `(heavyExcess, shareSurplus, atomPairing)`, equals the same scalar
written in `(heavyExcess, weight, gap form)`. -/
theorem surplusForm_eq_pairCapExcess (D : WeightedDesign m 3) (pivot pairFirst : Fin m) :
    heavyExcess D pairFirst * shareSurplus D pivot
        + heavyExcess D pivot * shareSurplus D pairFirst
        - 2 * atomPairing D pivot pairFirst ^ 2 * (D.weight pivot + D.weight pairFirst)
      = 2 * (D.weight pivot + D.weight pairFirst)
          * (heavyExcess D pivot * heavyExcess D pairFirst
              - atomPairing D pivot pairFirst ^ 2)
        - (1 - D.weight pairFirst) * heavyExcess D pivot
        - (1 - D.weight pivot) * heavyExcess D pairFirst := by
  simp only [shareSurplus, atomShare, heavyExcess]
  ring

/-! ## Part 2: Sylvester, transported onto `subsetSum` -/

/-- The Schur determinant of the gap factors as the pivot's heavy excess times
the gap determinant.  Restated here because the sibling proof is `private`. -/
theorem schurDeterminant_eq_heavyExcess_mul_discriminantTie (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    (heavyExcess D pivot * heavyExcess D pairFirst
          - atomPairing D pivot pairFirst ^ 2)
        * (heavyExcess D pivot * heavyExcess D pairSecond
          - atomPairing D pivot pairSecond ^ 2)
      - (heavyExcess D pivot * atomPairing D pairFirst pairSecond
          - atomPairing D pivot pairFirst * atomPairing D pivot pairSecond) ^ 2
      = heavyExcess D pivot * discriminantTie D pivot pairFirst pairSecond := by
  simp only [discriminantTie]
  ring

/-- **SYLVESTER, in the discriminant scalars.**  A heavy pivot, a positive
leading pair minor and a positive gap determinant force the triple's gap to be
positive definite.  The middle minor comes free: the Schur factorisation makes
its positivity a consequence of the other two, so the trace leg of
`Gtz.dominates_triple_iff_discriminantSystem` never has to be assumed. -/
theorem subsetSum_posDef_of_heavyPivot_of_minor_of_tie (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m}
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hminorPos : 0 < heavyExcess D pivot * heavyExcess D pairFirst
      - atomPairing D pivot pairFirst ^ 2)
    (htiePos : 0 < discriminantTie D pivot pairFirst pairSecond) :
    (subsetSum D {pivot, pairFirst, pairSecond} - 1).PosDef := by
  have hexcessPos : 0 < heavyExcess D pivot := by
    rw [heavyExcess]; linarith
  have hschur := schurDeterminant_eq_heavyExcess_mul_discriminantTie D pivot pairFirst pairSecond
  have hproductPos : 0 < heavyExcess D pivot * discriminantTie D pivot pairFirst pairSecond :=
    mul_pos hexcessPos htiePos
  have hotherMinorPos : 0 < heavyExcess D pivot * heavyExcess D pairSecond
      - atomPairing D pivot pairSecond ^ 2 := by
    nlinarith [hschur, hproductPos, hminorPos,
      sq_nonneg (heavyExcess D pivot * atomPairing D pairFirst pairSecond
        - atomPairing D pivot pairFirst * atomPairing D pivot pairSecond)]
  have htraceNonneg : 0 ≤ discriminantTrace D pivot pairFirst pairSecond := by
    rw [discriminantTrace]; linarith
  have hdominates : Dominates D {pivot, pairFirst, pairSecond} :=
    (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond hpairDistinct
      hpivotHeavy).mpr ⟨htraceNonneg, le_of_lt htiePos⟩
  refine (Matrix.PosSemidef.posDef_iff_det_ne_zero hdominates).mpr ?_
  rw [det_subsetSum_sub_one_eq_discriminantTie D hpivotFirst hpivotSecond hpairDistinct]
  exact ne_of_gt htiePos

/-! ## Part 3: the engine, with a strict conclusion and no side conditions

Under heaviness the cap excess is self-supporting.  The left side of the cap is
nonnegative, so a positive excess forces the gap form positive, and a positive gap
form at nonnegative excesses forces BOTH excesses strictly positive.  So the two
Sylvester side conditions are consequences, not hypotheses. -/

/-- The weights of two distinct atoms leave room: each is strictly below one. -/
theorem weight_lt_one_of_ne (D : WeightedDesign m 3) {pivot pairFirst : Fin m}
    (hdistinct : pivot ≠ pairFirst) : D.weight pivot < 1 := by
  have hpairSum : ∑ label ∈ ({pivot, pairFirst} : Finset (Fin m)), D.weight label
      = D.weight pivot + D.weight pairFirst := Finset.sum_pair hdistinct
  have hbound := sum_weight_subset_le_one D ({pivot, pairFirst} : Finset (Fin m))
  rw [hpairSum] at hbound
  linarith [D.weight_pos pairFirst]

/-- **THE ENGINE, strict and side-condition free.**  On a heavy design, a pair whose
pair-cap excess is positive completes to a STRICTLY dominating triple.  The
existence half is the shipped `Gtz.exists_pos_discriminantTie_of_pos_surplusForm`;
what is added is the change of coordinates, the derivation of the two Sylvester
side conditions from heaviness, and the positive-definite transport. -/
theorem exists_posDef_triple_of_pairCapExcess (D : WeightedDesign m 3)
    {pivot pairFirst : Fin m} (hdistinct : pivot ≠ pairFirst)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (hcapExcess : (1 - D.weight pairFirst) * heavyExcess D pivot
        + (1 - D.weight pivot) * heavyExcess D pairFirst
      < 2 * (D.weight pivot + D.weight pairFirst)
          * (heavyExcess D pivot * heavyExcess D pairFirst
              - atomPairing D pivot pairFirst ^ 2)) :
    ∃ pairSecond : Fin m, pairSecond ≠ pivot ∧ pairSecond ≠ pairFirst
      ∧ (subsetSum D {pivot, pairFirst, pairSecond} - 1).PosDef := by
  have hpivotExcess : 0 ≤ heavyExcess D pivot := by
    have := hheavy pivot; simp only [heavyExcess]; linarith
  have hpartnerExcess : 0 ≤ heavyExcess D pairFirst := by
    have := hheavy pairFirst; simp only [heavyExcess]; linarith
  have hpivotWeight : D.weight pivot < 1 := weight_lt_one_of_ne D hdistinct
  have hpartnerWeight : D.weight pairFirst < 1 :=
    weight_lt_one_of_ne D (Ne.symm hdistinct)
  have hleftNonneg : 0 ≤ (1 - D.weight pairFirst) * heavyExcess D pivot
      + (1 - D.weight pivot) * heavyExcess D pairFirst := by
    have hfirst : 0 ≤ (1 - D.weight pairFirst) * heavyExcess D pivot :=
      mul_nonneg (by linarith) hpivotExcess
    have hsecond : 0 ≤ (1 - D.weight pivot) * heavyExcess D pairFirst :=
      mul_nonneg (by linarith) hpartnerExcess
    linarith
  have hweightSumPos : 0 < D.weight pivot + D.weight pairFirst :=
    add_pos (D.weight_pos pivot) (D.weight_pos pairFirst)
  have hblockMinor : 0 < heavyExcess D pivot * heavyExcess D pairFirst
      - atomPairing D pivot pairFirst ^ 2 := by
    nlinarith [hcapExcess, hleftNonneg, hweightSumPos]
  have hcorner : 0 < heavyExcess D pivot := by
    nlinarith [hblockMinor, hpivotExcess, hpartnerExcess,
      sq_nonneg (atomPairing D pivot pairFirst)]
  have hpivotHeavy : 1 < leverageOf (D.atom pivot) := by
    have hcornerCopy := hcorner
    simp only [heavyExcess] at hcornerCopy
    linarith
  have hsurplus : 0 < heavyExcess D pairFirst * shareSurplus D pivot
      + heavyExcess D pivot * shareSurplus D pairFirst
      - 2 * atomPairing D pivot pairFirst ^ 2 * (D.weight pivot + D.weight pairFirst) := by
    rw [surplusForm_eq_pairCapExcess]
    linarith
  obtain ⟨pairSecond, hoffPivot, hoffPartner, hdetLeg⟩ :=
    exists_pos_discriminantTie_of_pos_surplusForm D hdistinct hsurplus
  exact ⟨pairSecond, hoffPivot, hoffPartner,
    subsetSum_posDef_of_heavyPivot_of_minor_of_tie D hdistinct (Ne.symm hoffPivot)
      (Ne.symm hoffPartner) hpivotHeavy hblockMinor hdetLeg⟩

/-! ## Part 4: the tie law -- the cap on every pair -/

/-- **THE RANK-THREE PAIR CAP.**  A HEAVY design carrying no strictly dominating
card-three subset obeys, at EVERY pair, a single scalar inequality between the
pair's excess product and its two heavy excesses.  This is the contrapositive of
`exists_posDef_triple_of_pairCapExcess`, and it is the rank-three twin of
`Gtz.weightedLeverage_le_nesterenkoBound_of_isTie`.

It is ATTAINED -- see `tetraDesign_pairCap_attained` -- so it cannot be
sharpened. -/
theorem pairCapExcess_le_of_no_strict_triple (D : WeightedDesign m 3)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (hnoStrict : ∀ selected : Finset (Fin m), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef)
    {pairFirst pairSecond : Fin m} (hdistinct : pairFirst ≠ pairSecond) :
    2 * (D.weight pairFirst + D.weight pairSecond)
        * (heavyExcess D pairFirst * heavyExcess D pairSecond
            - atomPairing D pairFirst pairSecond ^ 2)
      ≤ (1 - D.weight pairSecond) * heavyExcess D pairFirst
        + (1 - D.weight pairFirst) * heavyExcess D pairSecond := by
  classical
  by_contra hviolated
  push Not at hviolated
  obtain ⟨third, hthirdNeFirst, hthirdNeSecond, hposDef⟩ :=
    exists_posDef_triple_of_pairCapExcess D hdistinct hheavy hviolated
  refine hnoStrict {pairFirst, pairSecond, third} ?_ hposDef
  rw [Finset.card_insert_of_notMem (by simp [hdistinct, Ne.symm hthirdNeFirst]),
    Finset.card_insert_of_notMem (by simp [Ne.symm hthirdNeSecond]), Finset.card_singleton]

/-! ## Part 5: the cap is ATTAINED at the regular tetrahedron -/

/-- **THE CAP IS SHARP.**  At the regular tetrahedron -- the canonical rank-three
tie, where every triple has `Gtz.discriminantTie` exactly zero
(`Gtz.tetraDesign_discriminantTie`) -- the pair cap holds with EQUALITY.  So no
strengthening of `pairCapExcess_le_of_no_strict_triple` can hold, and the engine
`exists_posDef_triple_of_pairCapExcess` fires on the largest region any
inequality of this shape could reach. -/
theorem tetraDesign_pairCap_attained :
    2 * (tetraDesign.weight 0 + tetraDesign.weight 1)
        * (heavyExcess tetraDesign 0 * heavyExcess tetraDesign 1
            - atomPairing tetraDesign 0 1 ^ 2)
      = (1 - tetraDesign.weight 1) * heavyExcess tetraDesign 0
        + (1 - tetraDesign.weight 0) * heavyExcess tetraDesign 1 := by
  rw [tetraDesign_heavyExcess, tetraDesign_heavyExcess, tetraDesign_atomPairing_zeroOne]
  norm_num [tetraDesign]

/-! ## Part 6: the engine is NOT vacuous -- it fires on a shipped witness -/

/-- **THE ENGINE FIRES.**  At the shipped one-line witness `Gtz.narrowConeDesign`
the pair `{4, 5}` overflows the cap by `107/12`, so the engine returns a strictly
dominating triple through it with no selector and no case analysis. -/
theorem narrowConeDesign_pairFourFive_overflows :
    (1 - narrowConeDesign.weight 5) * heavyExcess narrowConeDesign 4
        + (1 - narrowConeDesign.weight 4) * heavyExcess narrowConeDesign 5
      < 2 * (narrowConeDesign.weight 4 + narrowConeDesign.weight 5)
          * (heavyExcess narrowConeDesign 4 * heavyExcess narrowConeDesign 5
              - atomPairing narrowConeDesign 4 5 ^ 2) := by
  norm_num [heavyExcess, atomPairing, leverageOf, narrowConeDesign, narrowConeAtom,
    narrowConeWeight, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem narrowConeDesign_engine_returns_strict_triple :
    ∃ third : Fin 6, third ≠ 4 ∧ third ≠ 5
      ∧ (subsetSum narrowConeDesign {4, 5, third} - 1).PosDef :=
  exists_posDef_triple_of_pairCapExcess narrowConeDesign (by decide)
    narrowConeDesign_heavy narrowConeDesign_pairFourFive_overflows

/-! ## Part 7: the exact residual -- the cap blind spot

The chartless obligation at ANY line pattern reduces to the designs the engine
cannot see.  Nothing pattern-specific enters, so the reduction serves the one-line
and two-meeting-lines classes identically. -/

/-- **The residual, named.**  A design of the stratum lies in the CAP BLIND SPOT
when no pair has positive pair-cap excess. -/
def IsCapBlindSpot (D : WeightedDesign m 3) : Prop :=
  ∀ pivot pairFirst : Fin m, pivot ≠ pairFirst →
    2 * (D.weight pivot + D.weight pairFirst)
        * (heavyExcess D pivot * heavyExcess D pairFirst
            - atomPairing D pivot pairFirst ^ 2)
      ≤ (1 - D.weight pairFirst) * heavyExcess D pivot
        + (1 - D.weight pivot) * heavyExcess D pairFirst

/-- **THE REDUCTION.**  The whole chartless obligation follows from the cap blind
spot alone: outside it the engine already produces a strictly dominating triple,
and it needs neither the pattern nor the weak dominator to do so.  So the open
content of `Gtz.PatternHeavyWeakToStrict` at any line pattern is exactly the
blind-spot case. -/
theorem patternHeavyWeakToStrict_of_capBlindSpot {size : ℕ} (pattern : LinePattern size)
    (hblind : ∀ design : WeightedDesign size 3, HasLinePattern design pattern →
      (∀ label : Fin size, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      (∃ dominator : Finset (Fin size), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin size), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    PatternHeavyWeakToStrict pattern := by
  intro design hpattern hheavy hweak
  by_cases hblindSpot : IsCapBlindSpot design
  · exact hblind design hpattern hheavy hblindSpot hweak
  · simp only [IsCapBlindSpot] at hblindSpot
    push Not at hblindSpot
    obtain ⟨pivot, pairFirst, hdistinct, hexcess⟩ := hblindSpot
    obtain ⟨pairSecond, hoffPivot, hoffPartner, hposDef⟩ :=
      exists_posDef_triple_of_pairCapExcess design hdistinct hheavy hexcess
    refine ⟨{pivot, pairFirst, pairSecond}, ?_, hposDef⟩
    rw [Finset.card_insert_of_notMem (by simp [hdistinct, Ne.symm hoffPivot]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hoffPartner]),
      Finset.card_singleton]

/-- The reduction at the TWO-MEETING-LINES pattern, which is what
`Skeleton.obligationHeavyWeakToStrictTwoMeetingLines` demands. -/
theorem twoMeetingLines_heavyWeakToStrict_of_capBlindSpot
    (hblind : ∀ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) →
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  patternHeavyWeakToStrict_of_capBlindSpot _ hblind

end Gtz
