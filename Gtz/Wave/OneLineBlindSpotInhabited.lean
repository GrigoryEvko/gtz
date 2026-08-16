import Gtz.Wave.OneLineSurvivorWiring
import Gtz.Reduction.RayleighCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# The one-line joint blind spot is inhabited

`Skeleton.obligationHeavyWeakToStrictOneLine` is the proposition
`Gtz.OneLineTenthHeavyJointBlindLineSparse`.  Its antecedent asks for a design
that lies on the one-line stratum, is leverage heavy, carries a label of raw
weight at least `1/10`, carries a weakly dominating card-three subset, and lies
in BOTH `Gtz.IsCapBlindSpot` and `Gtz.IsOneLineNormalBlindSpot`.  Until this
module no design was known to meet all six conditions at the same time, so the
obligation could have been a door with no key: an axiom whose antecedent is
empty type-checks and reads as an asset.

This module closes that question.  `Gtz.jointBlindDesign` meets all six
conditions, with exact rational atoms and exact rational weights and Parseval on
the nose.  So the obligation is a genuine statement about a nonempty region.

The design also satisfies the CONCLUSION: `{0,3,4}` is one of the ten
line-sparse candidates and it dominates strictly.  So this module supports the
obligation rather than refuting it.

## How the blind spot is decided

The three line atoms lie in the plane `z = 0` and the first two of them span
that plane, so every unit normal flat against the whole line has first two
coordinates zero and third coordinate of square one
(`Gtz.jointBlindDesign_normal_coordinates`).  The shadow Gram then reduces to
the plane dot product with no square root and no sign choice
(`Gtz.jointBlindDesign_shadowPairing_eq`).

At that normal exactly one pair, `{0,2}`, has a positive shadow-gap
determinant (`Gtz.jointBlindDesign_shadowGapDeterminant_nonpos_or_zeroTwo`).
For that one pair the landed equivalence
`Gtz.posDef_tripleGap_iff_pos_liftMargin` turns a positive lift margin into a
strictly dominating triple through `{0,2}`, and each of the four such triples
has an explicit probe where its gap reads negative.  So the criterion is silent
and no case analysis over the lift margin polynomial is needed.

## What the design measures

Its two strictly dominating triples are `{0,3,4}` and `{0,4,5}`.  Neither
contains the pair `{0,2}`, which is exactly why the line-normal criterion cannot
see them: a strictly dominating triple is visible at a normal only when one of
its own pairs strictly dominates the plane orthogonal to that normal.
-/

namespace Gtz

open Matrix

/-! ## Part 1: the design -/

/-- Three line atoms in the plane `z = 0`, three free atoms off it.  Atom `0` is
long and light, which is what makes the pair `{0,2}` strictly dominate the plane
while the cap engine stays silent. -/
noncomputable def jointBlindAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, 184 / 5, 0]
  | 1 => ![-1, -2 / 5, 0]
  | 2 => ![1, -11 / 18, 0]
  | 3 => ![-1, 0, -17 / 4]
  | 4 => ![-1, -8 / 15, 2]
  | 5 => ![-1, -2 / 3, -11 / 4]

/-- The weights.  They are forced by Parseval once the atoms are fixed. -/
noncomputable def jointBlindWeight : Fin 6 → ℝ
  | 0 => 709120 / 1335443109
  | 1 => 14229755 / 36093057
  | 2 => 195545772 / 445147703
  | 3 => 16 / 1717
  | 4 => 10 / 101
  | 5 => 64 / 1111

/-- The witness design.  Parseval holds exactly. -/
noncomputable def jointBlindDesign : WeightedDesign 6 3 where
  atom := jointBlindAtom
  weight := jointBlindWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [jointBlindWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [jointBlindWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [jointBlindAtom, jointBlindWeight, atomMatrix, Matrix.cons_val_two] <;> norm_num

theorem jointBlindDesign_atom : jointBlindDesign.atom = jointBlindAtom := rfl

theorem jointBlindDesign_weight : jointBlindDesign.weight = jointBlindWeight := rfl

/-! ## Part 2: the six antecedent conditions, one at a time -/

/-- The design sits on the one-line stratum: `{0,1,2}` is its only dependent
triple. -/
theorem jointBlindDesign_hasLinePattern :
    HasLinePattern jointBlindDesign (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, jointBlindDesign, jointBlindAtom,
            Matrix.cons_val_two])
          (by decide)
      | exact iff_of_true
          (by norm_num [atomBracket, tripleBracket_eq, jointBlindDesign, jointBlindAtom,
            Matrix.cons_val_two])
          (by decide)

/-- **Every atom is heavy.**  The leverages are `33881/25`, `29/25`, `445/324`,
`305/16`, `1189/225` and `1297/144`. -/
theorem jointBlindDesign_allHeavy (label : Fin 6) :
    1 ≤ leverageOf (jointBlindDesign.atom label) := by
  fin_cases label <;>
    norm_num [leverageOf, Fin.sum_univ_three, jointBlindDesign, jointBlindAtom,
      Matrix.cons_val_two]

/-- Label `2` carries raw weight `195545772/445147703`, which is more than one
tenth. -/
theorem jointBlindDesign_tenthHeavy :
    ∃ heavyLabel : Fin 6, 1 / 10 ≤ jointBlindDesign.weight heavyLabel :=
  ⟨2, by norm_num [jointBlindDesign, jointBlindWeight]⟩

/-- **The cap engine is silent.**  No ordered pair overflows the pair cap. -/
theorem jointBlindDesign_isCapBlindSpot : IsCapBlindSpot jointBlindDesign := by
  intro pivot pairFirst hdistinct
  fin_cases pivot <;> fin_cases pairFirst <;>
    first
      | exact absurd rfl hdistinct
      | norm_num [heavyExcess, atomPairing, leverageOf, Fin.sum_univ_three, dotProduct,
          jointBlindDesign, jointBlindAtom, jointBlindWeight, Matrix.cons_val_two]

/-! ## Part 3: the strictly dominating triple `{0,3,4}` -/

/-- The gap of `{0,3,4}` written as a sum of three squares. -/
theorem jointBlind_dominatorGap_form (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ ((subsetSum jointBlindDesign {0, 3, 4} - 1) *ᵥ probeVec)
      = 2 * (probeVec 0 + 56 / 3 * probeVec 1 + 9 / 8 * probeVec 2) ^ 2
        + 147743 / 225 * (probeVec 1 - 9690 / 147743 * probeVec 2) ^ 2
        + 74257487 / 4727776 * probeVec 2 ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [jointBlindDesign, jointBlindAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

/-- `{0,3,4}` dominates strictly.  The three squares vanish together only at the
zero probe, because the linear forms are triangular in the coordinates. -/
theorem jointBlind_posDef_zeroThreeFour :
    (subsetSum jointBlindDesign {0, 3, 4} - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one jointBlindDesign _),
      fun probeVec hprobeNe => ?_⟩
  rw [star_trivial, jointBlind_dominatorGap_form]
  have hsome : probeVec 0 + 56 / 3 * probeVec 1 + 9 / 8 * probeVec 2 ≠ 0
      ∨ probeVec 1 - 9690 / 147743 * probeVec 2 ≠ 0 ∨ probeVec 2 ≠ 0 := by
    by_contra hcontra
    push Not at hcontra
    obtain ⟨htop, hmid, hbot⟩ := hcontra
    refine hprobeNe (funext fun index => ?_)
    have hone : probeVec 1 = 0 := by rw [hbot] at hmid; linarith
    have hzero : probeVec 0 = 0 := by rw [hone, hbot] at htop; linarith
    fin_cases index <;> simp [hzero, hone, hbot]
  have hsq : ∀ value : ℝ, value ≠ 0 → 0 < value ^ 2 := fun value hvalue =>
    (sq_nonneg value).lt_of_ne (Ne.symm (pow_ne_zero 2 hvalue))
  rcases hsome with hne | hne | hne
  · nlinarith [hsq _ hne, sq_nonneg (probeVec 1 - 9690 / 147743 * probeVec 2),
      sq_nonneg (probeVec 2)]
  · nlinarith [hsq _ hne, sq_nonneg (probeVec 0 + 56 / 3 * probeVec 1 + 9 / 8 * probeVec 2),
      sq_nonneg (probeVec 2)]
  · nlinarith [hsq _ hne, sq_nonneg (probeVec 0 + 56 / 3 * probeVec 1 + 9 / 8 * probeVec 2),
      sq_nonneg (probeVec 1 - 9690 / 147743 * probeVec 2)]

/-- The design carries a weakly dominating card-three subset. -/
theorem jointBlindDesign_hasWeakDominator :
    ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates jointBlindDesign dominator :=
  ⟨{0, 3, 4}, by decide, jointBlind_posDef_zeroThreeFour.posSemidef⟩

/-- The design satisfies the CONCLUSION of the obligation. -/
theorem jointBlindDesign_planeBranchTenCandidate :
    PlaneBranchTenCandidate jointBlindDesign :=
  Or.inl jointBlind_posDef_zeroThreeFour

/-! ## Part 4: the unit line normal -/

/-- **The normal is pinned.**  Atoms `0` and `1` span the plane `z = 0`, so a
unit vector flat against the whole line has its first two coordinates zero and
its third coordinate of square one.  No square root and no sign choice enter. -/
theorem jointBlindDesign_normal_coordinates {normalVec : Fin 3 → ℝ}
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      jointBlindDesign.atom lineLabel ⬝ᵥ normalVec = 0) :
    normalVec 0 = 0 ∧ normalVec 1 = 0 ∧ normalVec 2 ^ 2 = 1 := by
  have hzero := hflat 0 (by decide)
  have hone := hflat 1 (by decide)
  simp only [jointBlindDesign, jointBlindAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hzero hone
  have hsecond : normalVec 1 = 0 := by linarith
  have hfirst : normalVec 0 = 0 := by linarith
  refine ⟨hfirst, hsecond, ?_⟩
  simp only [dotProduct, Fin.sum_univ_three, hfirst, hsecond] at hunit
  linarith [hunit]

/-- **The shadow Gram is the plane dot product.**  At any normal pinned by
`Gtz.jointBlindDesign_normal_coordinates` the third coordinates cancel. -/
theorem jointBlindDesign_shadowPairing_eq {normalVec : Fin 3 → ℝ}
    (hfirst : normalVec 0 = 0) (hsecond : normalVec 1 = 0) (hthird : normalVec 2 ^ 2 = 1)
    (leftLabel rightLabel : Fin 6) :
    shadowPairing jointBlindDesign normalVec leftLabel rightLabel
      = jointBlindDesign.atom leftLabel 0 * jointBlindDesign.atom rightLabel 0
        + jointBlindDesign.atom leftLabel 1 * jointBlindDesign.atom rightLabel 1 := by
  simp only [shadowPairing, normalReading, dotProduct, Fin.sum_univ_three, hfirst, hsecond,
    mul_zero, add_zero, zero_add]
  linear_combination
    (-(jointBlindDesign.atom leftLabel 2 * jointBlindDesign.atom rightLabel 2)) * hthird

/-! ## Part 5: only the pair `{0,2}` survives the first two conjuncts -/

/-- **The pair sweep.**  At the line normal every ordered pair of distinct labels
has a nonpositive shadow-gap determinant, except the pair `{0,2}`, whose value is
`1979/45`. -/
theorem jointBlindDesign_shadowGapDeterminant_nonpos_or_zeroTwo {normalVec : Fin 3 → ℝ}
    (hfirst : normalVec 0 = 0) (hsecond : normalVec 1 = 0) (hthird : normalVec 2 ^ 2 = 1)
    (pairFirst pairSecond : Fin 6) (hdistinct : pairFirst ≠ pairSecond) :
    shadowGapDeterminant jointBlindDesign normalVec pairFirst pairSecond ≤ 0
      ∨ ((pairFirst = 0 ∧ pairSecond = 2) ∨ (pairFirst = 2 ∧ pairSecond = 0)) := by
  simp only [shadowGapDeterminant, shadowGapDeterminantOf,
    jointBlindDesign_shadowPairing_eq hfirst hsecond hthird]
  fin_cases pairFirst <;> fin_cases pairSecond <;>
    first
      | exact absurd rfl hdistinct
      | exact Or.inr (by decide)
      | exact Or.inl (by
          norm_num [jointBlindDesign, jointBlindAtom, Matrix.cons_val_two])

/-! ## Part 6: no triple through `{0,2}` dominates strictly -/

/-- The gap of `{0,2,1}` at the vertical probe: the whole line is flat there. -/
theorem jointBlind_zeroTwoOne_gap :
    (![0, 0, 1] : Fin 3 → ℝ) ⬝ᵥ ((subsetSum jointBlindDesign {0, 2, 1} - 1) *ᵥ ![0, 0, 1])
      = -1 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [jointBlindDesign, jointBlindAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem jointBlind_zeroTwoThree_gap :
    (![-33, 1, 8] : Fin 3 → ℝ) ⬝ᵥ ((subsetSum jointBlindDesign {0, 2, 3} - 1) *ᵥ ![-33, 1, 8])
      = -71711 / 8100 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [jointBlindDesign, jointBlindAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem jointBlind_zeroTwoFour_gap :
    (![-27, 1, -12] : Fin 3 → ℝ)
        ⬝ᵥ ((subsetSum jointBlindDesign {0, 2, 4} - 1) *ᵥ ![-27, 1, -12])
      = -76967 / 8100 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [jointBlindDesign, jointBlindAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem jointBlind_zeroTwoFive_gap :
    (![-29, 1, 10] : Fin 3 → ℝ)
        ⬝ᵥ ((subsetSum jointBlindDesign {0, 2, 5} - 1) *ᵥ ![-29, 1, 10])
      = -14773 / 4050 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [jointBlindDesign, jointBlindAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-- **No triple through the surviving pair dominates strictly.**  Each of the
four triples `{0,2,z}` reads negative at an explicit probe. -/
theorem jointBlind_not_posDef_through_zeroTwo (thirdLabel : Fin 6)
    (hzero : thirdLabel ≠ 0) (htwo : thirdLabel ≠ 2) :
    ¬ (subsetSum jointBlindDesign {0, 2, thirdLabel} - 1).PosDef := by
  have hcases : thirdLabel = 1 ∨ thirdLabel = 3 ∨ thirdLabel = 4 ∨ thirdLabel = 5 := by
    fin_cases thirdLabel <;>
      first
        | exact absurd rfl hzero
        | exact absurd rfl htwo
        | decide
  intro hposDef
  have hform := Matrix.posDef_iff_dotProduct_mulVec.mp hposDef
  rcases hcases with rfl | rfl | rfl | rfl
  · have hpos := hform.2 (x := (![0, 0, 1] : Fin 3 → ℝ))
      (by
        intro hnull
        have hentry := congrFun hnull 2
        norm_num [Matrix.cons_val_two, Matrix.tail_cons] at hentry)
    rw [star_trivial, jointBlind_zeroTwoOne_gap] at hpos
    norm_num at hpos
  · have hpos := hform.2 (x := (![-33, 1, 8] : Fin 3 → ℝ))
      (by
        intro hnull
        have hentry := congrFun hnull 0
        norm_num at hentry)
    rw [star_trivial, jointBlind_zeroTwoThree_gap] at hpos
    norm_num at hpos
  · have hpos := hform.2 (x := (![-27, 1, -12] : Fin 3 → ℝ))
      (by
        intro hnull
        have hentry := congrFun hnull 0
        norm_num at hentry)
    rw [star_trivial, jointBlind_zeroTwoFour_gap] at hpos
    norm_num at hpos
  · have hpos := hform.2 (x := (![-29, 1, 10] : Fin 3 → ℝ))
      (by
        intro hnull
        have hentry := congrFun hnull 0
        norm_num at hentry)
    rw [star_trivial, jointBlind_zeroTwoFive_gap] at hpos
    norm_num at hpos

/-! ## Part 7: the line-normal blind spot -/

/-- **THE LINE-NORMAL CRITERION IS SILENT.**  At every unit normal flat against
the whole line, no ordered pair and third label produce a guarded positive
margin. -/
theorem jointBlindDesign_isOneLineNormalBlindSpot :
    IsOneLineNormalBlindSpot jointBlindDesign := by
  intro normalVec hunit hflat pairFirst pairSecond thirdLabel hFirstSecond hFirstThird
    hSecondThird hfire
  obtain ⟨hcorner, hdet, hmargin⟩ := hfire
  obtain ⟨hfirst, hsecond, hthird⟩ := jointBlindDesign_normal_coordinates hunit hflat
  have hposDef : (subsetSum jointBlindDesign {pairFirst, pairSecond, thirdLabel} - 1).PosDef :=
    (posDef_tripleGap_iff_pos_liftMargin jointBlindDesign hunit pairFirst pairSecond
      thirdLabel hFirstSecond hFirstThird hSecondThird hcorner hdet).mpr hmargin
  rcases jointBlindDesign_shadowGapDeterminant_nonpos_or_zeroTwo hfirst hsecond hthird
    pairFirst pairSecond hFirstSecond with hdead | hpair
  · exact absurd hdet (not_lt.mpr hdead)
  · rcases hpair with ⟨hzero, htwo⟩ | ⟨htwo, hzero⟩
    · subst hzero; subst htwo
      exact jointBlind_not_posDef_through_zeroTwo thirdLabel (Ne.symm hFirstThird)
        (Ne.symm hSecondThird) hposDef
    · subst hzero; subst htwo
      rw [Finset.insert_comm] at hposDef
      exact jointBlind_not_posDef_through_zeroTwo thirdLabel (Ne.symm hSecondThird)
        (Ne.symm hFirstThird) hposDef

/-! ## Part 8: the antecedent is nonempty -/

/-- **THE OBLIGATION IS NOT A DOOR WITHOUT A KEY.**  The antecedent of
`Gtz.OneLineTenthHeavyJointBlindLineSparse`, which is
`Skeleton.obligationHeavyWeakToStrictOneLine`, is satisfied by an explicit
design.  So the axiom is a statement about a nonempty region, and it is not
vacuously true. -/
theorem exists_oneLine_tenthHeavy_jointBlind_weaklyDominated :
    ∃ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) ∧
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) ∧
      (∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel) ∧
      IsCapBlindSpot design ∧
      IsOneLineNormalBlindSpot design ∧
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) :=
  ⟨jointBlindDesign, jointBlindDesign_hasLinePattern, jointBlindDesign_allHeavy,
    jointBlindDesign_tenthHeavy, jointBlindDesign_isCapBlindSpot,
    jointBlindDesign_isOneLineNormalBlindSpot, jointBlindDesign_hasWeakDominator⟩

/-- The witness also meets the conclusion, so it does not refute the
obligation. -/
theorem jointBlind_witness_meets_conclusion :
    HasLinePattern jointBlindDesign (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) ∧
      IsCapBlindSpot jointBlindDesign ∧ IsOneLineNormalBlindSpot jointBlindDesign ∧
      PlaneBranchTenCandidate jointBlindDesign :=
  ⟨jointBlindDesign_hasLinePattern, jointBlindDesign_isCapBlindSpot,
    jointBlindDesign_isOneLineNormalBlindSpot, jointBlindDesign_planeBranchTenCandidate⟩

/-- **THE CAP BLIND SPOT IS INHABITED TOO**, on the same stratum and by the same
design.  Both halves of the joint hypothesis are nonempty. -/
theorem exists_oneLine_capBlindSpot :
    ∃ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) ∧
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) ∧ IsCapBlindSpot design :=
  ⟨jointBlindDesign, jointBlindDesign_hasLinePattern, jointBlindDesign_allHeavy,
    jointBlindDesign_isCapBlindSpot⟩

end Gtz
