/-
# The two-meeting-lines covering: entry `#3` sits on its own chart

`Gtz.twoMeetingLinesDirection` charts entry `#3` of
`Gtz.stressFreeResidualFamiliesSix` at two parameters.  This file proves the
COVERING half: every primitive design realizing the pattern `[[0,1,2],[0,3,4]]`
is a chart point at some admissible parameter.  With
`Gtz.stressFreeStratumIsTieFree_of_parameterizedChart` the entry `#3` obligation
becomes tie-freeness of a two-parameter chart, which is the same shape the
campaign already carries at entries `#4` and `#5`.

## The three bracket identities

Write `bigDelta = [013]` and read the seven expansion coefficients of
`Gtz.exists_twoMeetingLinesCoordinates` in the basis `{0,1,3}`:

  `bigDelta . v2 = A . v0 + B . v1`,
  `bigDelta . v4 = C . v0 + D . v3`,
  `bigDelta . v5 = E . v0 + F . v1 + G . v3`.

Multilinearity of the bracket then pins the three triples that decide
admissibility, each of them a triple the pattern forbids to vanish:

  `bigDelta * [235] = B E - A F`,
  `bigDelta * [145] = D E - C G`,
  `bigDelta ^ 2 * [245] = B D E - A D F - B C G`.

## The parameters and the frame

The columns `E . v0`, `F . v1`, `G . v3` carry atom `5` to `(1,1,1)` by
construction, and the two parameters come out as

  `p = B E / (A F)`,   `q = D E / (C G)`.

Both are introduced by a POLYNOMIAL spec rather than a quotient, so every
downstream step is division-free.  The five admissibility exclusions are then
read off: `p != 0` and `q != 0` from `B != 0` and `D != 0`, `p != 1` and
`q != 1` from `[235] != 0` and `[145] != 0`, and `p q != p + q` from
`[245] != 0`.

PRIMITIVITY IS NOT USED.  The `#4` covering needs a non-parallel hypothesis to
exclude its degenerate parameters; here every exclusion already follows from a
bracket the pattern forbids to vanish, so the covering holds on the bracket
hypotheses alone.

## #REGISTRY-STALE — the ATTACK field of the axiom denies this file exists

`Skeleton.obligationSeededTransversalTwoMeetingLines`
(Skeleton/Obligations.lean:283) carries a WHY-OPEN field that reads "no chart
exists for this pattern".  That is FALSE.
`Gtz.parameterizedChartCovers_twoMeetingLinesDirection` (:283 of this file) is
unconditional and sorry-free, `Gtz.stressFreeStratumIsTieFree_twoMeetingLines_of_chart`
(:336) consumes it, and `Gtz.twoMeetingLinesOnPath_of_chart`
(Gtz/Wave/WiringLineChartRoads.lean:164) carries the road all the way to the
registry Prop.  Do not brief a fork from that field.

## #ZERO-CONSUMER

Outside this file and the two umbrellas, nothing cites
`Gtz.exists_twoMeetingLinesRealization_of_brackets`,
`Gtz.tripleBracket_twoThreeFive_of_expansions`,
`Gtz.tripleBracket_oneFourFive_of_expansions`,
`Gtz.tripleBracket_twoFourFive_of_expansions`, `Gtz.twoMeetingLinesScale`,
`Gtz.twoMeetingLinesSelected`, `Gtz.twoMeetingLinesCoeff`,
`Gtz.readsThrough_twoMeetingLinesDirection`,
`Gtz.posDef_directionChartGap_twoMeetingLines_of_coverCell` or
`Gtz.twoMeetingLinesFamily_mem_stressFreeResidualFamiliesSix`.
-/
import Gtz.Design.TwoMeetingLinesChart
import Gtz.Design.GeneralCoverCell

namespace Gtz

open Matrix

/-! ## The three bracket identities -/

/-- The `{2,3,5}` bracket in the basis `{0,1,3}`.  Atom `2` spends its two
coefficients and atom `5` its three, and every repeated-slot term dies. -/
theorem tripleBracket_twoThreeFive_of_expansions
    (vecZero vecOne vecTwo vecThree vecFive : Fin 3 → ℝ)
    (bigDelta coefA coefB coefE coefF coefG : ℝ)
    (hexpandTwo : bigDelta • vecTwo = coefA • vecZero + coefB • vecOne)
    (hexpandFive : bigDelta • vecFive
      = coefE • vecZero + coefF • vecOne + coefG • vecThree) :
    bigDelta ^ 2 * tripleBracket vecTwo vecThree vecFive
      = (coefB * coefE - coefA * coefF) * tripleBracket vecZero vecOne vecThree := by
  have hkey : tripleBracket (bigDelta • vecTwo) vecThree (bigDelta • vecFive)
      = tripleBracket (coefA • vecZero + coefB • vecOne) vecThree
          (coefE • vecZero + coefF • vecOne + coefG • vecThree) := by
    rw [hexpandTwo, hexpandFive]
  simp only [tripleBracket_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hkey
  simp only [tripleBracket_eq]
  linear_combination hkey

/-- The `{1,4,5}` bracket in the same basis. -/
theorem tripleBracket_oneFourFive_of_expansions
    (vecZero vecOne vecThree vecFour vecFive : Fin 3 → ℝ)
    (bigDelta coefC coefD coefE coefF coefG : ℝ)
    (hexpandFour : bigDelta • vecFour = coefC • vecZero + coefD • vecThree)
    (hexpandFive : bigDelta • vecFive
      = coefE • vecZero + coefF • vecOne + coefG • vecThree) :
    bigDelta ^ 2 * tripleBracket vecOne vecFour vecFive
      = (coefD * coefE - coefC * coefG) * tripleBracket vecZero vecOne vecThree := by
  have hkey : tripleBracket vecOne (bigDelta • vecFour) (bigDelta • vecFive)
      = tripleBracket vecOne (coefC • vecZero + coefD • vecThree)
          (coefE • vecZero + coefF • vecOne + coefG • vecThree) := by
    rw [hexpandFour, hexpandFive]
  simp only [tripleBracket_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hkey
  simp only [tripleBracket_eq]
  linear_combination hkey

/-- The `{2,4,5}` bracket, the three-line interface.  All three atoms spend
their coefficients at once, so the identity carries `bigDelta` cubed. -/
theorem tripleBracket_twoFourFive_of_expansions
    (vecZero vecOne vecTwo vecThree vecFour vecFive : Fin 3 → ℝ)
    (bigDelta coefA coefB coefC coefD coefE coefF coefG : ℝ)
    (hexpandTwo : bigDelta • vecTwo = coefA • vecZero + coefB • vecOne)
    (hexpandFour : bigDelta • vecFour = coefC • vecZero + coefD • vecThree)
    (hexpandFive : bigDelta • vecFive
      = coefE • vecZero + coefF • vecOne + coefG • vecThree) :
    bigDelta ^ 3 * tripleBracket vecTwo vecFour vecFive
      = (coefB * coefD * coefE - coefA * coefD * coefF - coefB * coefC * coefG)
        * tripleBracket vecZero vecOne vecThree := by
  have hkey : tripleBracket (bigDelta • vecTwo) (bigDelta • vecFour) (bigDelta • vecFive)
      = tripleBracket (coefA • vecZero + coefB • vecOne)
          (coefC • vecZero + coefD • vecThree)
          (coefE • vecZero + coefF • vecOne + coefG • vecThree) := by
    rw [hexpandTwo, hexpandFour, hexpandFive]
  simp only [tripleBracket_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hkey
  simp only [tripleBracket_eq]
  linear_combination hkey

/-! ## The per-atom scales -/

/-- The per-atom scales of the `#3` realization, against the frame
`E . v0`, `F . v1`, `G . v3`. -/
noncomputable def twoMeetingLinesScale
    (coefA coefC coefE coefF coefG bigDelta : ℝ) : Fin 6 → ℝ
  | 0 => 1 / coefE
  | 1 => 1 / coefF
  | 2 => coefA / (coefE * bigDelta)
  | 3 => 1 / coefG
  | 4 => coefC / (coefE * bigDelta)
  | 5 => 1 / bigDelta

/-! ## The realization, on bare vectors -/

set_option maxHeartbeats 1000000 in
/-- **THE `#3` RIGIDITY THEOREM, on bare vectors.**  Eight nonvanishing brackets
and the two line relations put an arbitrary configuration on the chart.  The two
parameters are `p = B E / (A F)` and `q = D E / (C G)`, introduced by polynomial
specs so that nothing downstream divides. -/
theorem exists_twoMeetingLinesRealization_of_brackets (vec : Fin 6 → (Fin 3 → ℝ))
    (hbasisNe : tripleBracket (vec 0) (vec 1) (vec 3) ≠ 0)
    (hcoefANe : tripleBracket (vec 2) (vec 1) (vec 3) ≠ 0)
    (hcoefBNe : tripleBracket (vec 0) (vec 2) (vec 3) ≠ 0)
    (hcoefCNe : tripleBracket (vec 4) (vec 1) (vec 3) ≠ 0)
    (hcoefDNe : tripleBracket (vec 0) (vec 1) (vec 4) ≠ 0)
    (hcoefENe : tripleBracket (vec 5) (vec 1) (vec 3) ≠ 0)
    (hcoefFNe : tripleBracket (vec 0) (vec 5) (vec 3) ≠ 0)
    (hcoefGNe : tripleBracket (vec 0) (vec 1) (vec 5) ≠ 0)
    (hoffTwoThreeFive : tripleBracket (vec 2) (vec 3) (vec 5) ≠ 0)
    (hoffOneFourFive : tripleBracket (vec 1) (vec 4) (vec 5) ≠ 0)
    (hoffTwoFourFive : tripleBracket (vec 2) (vec 4) (vec 5) ≠ 0)
    (hlineFirst : tripleBracket (vec 0) (vec 1) (vec 2) = 0)
    (hlineSecond : tripleBracket (vec 0) (vec 3) (vec 4) = 0) :
    ∃ param : ℝ × ℝ, IsAdmissibleTwoMeetingLinesParameter param ∧
      ∃ basisChange : Matrix (Fin 3) (Fin 3) ℝ, ∃ scale : Fin 6 → ℝ,
        IsUnit basisChange.det ∧ (∀ index, scale index ≠ 0) ∧
          ∀ index, vec index
            = scale index • (basisChange *ᵥ twoMeetingLinesDirection param index) := by
  set bigDelta := tripleBracket (vec 0) (vec 1) (vec 3) with hbigDeltaDef
  set coefA := tripleBracket (vec 2) (vec 1) (vec 3) with hcoefADef
  set coefB := tripleBracket (vec 0) (vec 2) (vec 3) with hcoefBDef
  set coefC := tripleBracket (vec 4) (vec 1) (vec 3) with hcoefCDef
  set coefD := tripleBracket (vec 0) (vec 1) (vec 4) with hcoefDDef
  set coefE := tripleBracket (vec 5) (vec 1) (vec 3) with hcoefEDef
  set coefF := tripleBracket (vec 0) (vec 5) (vec 3) with hcoefFDef
  set coefG := tripleBracket (vec 0) (vec 1) (vec 5) with hcoefGDef
  have hexpandTwo : bigDelta • vec 2 = coefA • vec 0 + coefB • vec 1 :=
    smul_two_expansion vec hlineFirst
  have hexpandFour : bigDelta • vec 4 = coefC • vec 0 + coefD • vec 3 :=
    smul_four_expansion vec hlineSecond
  have hexpandFive : bigDelta • vec 5 = coefE • vec 0 + coefF • vec 1 + coefG • vec 3 :=
    smul_five_expansion vec
  -- The two parameters, pinned by polynomial specs.
  obtain ⟨firstParam, hfirstSpec⟩ : ∃ firstParam : ℝ,
      firstParam * (coefA * coefF) = coefB * coefE :=
    ⟨coefB * coefE / (coefA * coefF), by field_simp⟩
  obtain ⟨secondParam, hsecondSpec⟩ : ∃ secondParam : ℝ,
      secondParam * (coefC * coefG) = coefD * coefE :=
    ⟨coefD * coefE / (coefC * coefG), by field_simp⟩
  -- The three off-pattern brackets become the three nondegeneracy facts.
  have hbracketTwoThreeFive := tripleBracket_twoThreeFive_of_expansions (vec 0) (vec 1)
    (vec 2) (vec 3) (vec 5) bigDelta coefA coefB coefE coefF coefG hexpandTwo hexpandFive
  have hbracketOneFourFive := tripleBracket_oneFourFive_of_expansions (vec 0) (vec 1)
    (vec 3) (vec 4) (vec 5) bigDelta coefC coefD coefE coefF coefG hexpandFour hexpandFive
  have hbracketTwoFourFive := tripleBracket_twoFourFive_of_expansions (vec 0) (vec 1)
    (vec 2) (vec 3) (vec 4) (vec 5) bigDelta coefA coefB coefC coefD coefE coefF coefG
    hexpandTwo hexpandFour hexpandFive
  have hfirstNe : firstParam ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hfirstSpec
    exact (mul_ne_zero hcoefBNe hcoefENe) hfirstSpec.symm
  have hsecondNe : secondParam ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hsecondSpec
    exact (mul_ne_zero hcoefDNe hcoefENe) hsecondSpec.symm
  have hfirstNeOne : firstParam ≠ 1 := by
    intro hone
    refine hoffTwoThreeFive ?_
    have hvanish : coefB * coefE - coefA * coefF = 0 := by
      rw [hone, one_mul] at hfirstSpec; linarith
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 2) (vec 3) (vec 5) = 0 := by
      rw [hbracketTwoThreeFive, hvanish, zero_mul]
    exact by
      have hpowNe : bigDelta ^ 2 ≠ 0 := pow_ne_zero 2 hbasisNe
      exact (mul_eq_zero.mp hsquare).resolve_left hpowNe
  have hsecondNeOne : secondParam ≠ 1 := by
    intro hone
    refine hoffOneFourFive ?_
    have hvanish : coefD * coefE - coefC * coefG = 0 := by
      rw [hone, one_mul] at hsecondSpec; linarith
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 1) (vec 4) (vec 5) = 0 := by
      rw [hbracketOneFourFive, hvanish, zero_mul]
    exact by
      have hpowNe : bigDelta ^ 2 ≠ 0 := pow_ne_zero 2 hbasisNe
      exact (mul_eq_zero.mp hsquare).resolve_left hpowNe
  have hinterfaceNe :
      firstParam * secondParam - firstParam - secondParam ≠ 0 := by
    intro hzero
    refine hoffTwoFourFive ?_
    have hvanish :
        coefB * coefD * coefE - coefA * coefD * coefF - coefB * coefC * coefG = 0 := by
      have hprod : (firstParam * secondParam - firstParam - secondParam)
          * ((coefA * coefF) * (coefC * coefG))
          = coefE * (coefB * coefD * coefE - coefA * coefD * coefF
              - coefB * coefC * coefG) := by
        linear_combination (secondParam * (coefC * coefG) - coefC * coefG) * hfirstSpec
          + (coefB * coefE - coefA * coefF) * hsecondSpec
      rw [hzero, zero_mul] at hprod
      exact (mul_eq_zero.mp hprod.symm).resolve_left hcoefENe
    have hcube : bigDelta ^ 3 * tripleBracket (vec 2) (vec 4) (vec 5) = 0 := by
      rw [hbracketTwoFourFive, hvanish, zero_mul]
    exact by
      have hpowNe : bigDelta ^ 3 ≠ 0 := pow_ne_zero 3 hbasisNe
      exact (mul_eq_zero.mp hcube).resolve_left hpowNe
  refine ⟨(firstParam, secondParam),
    ⟨hfirstNe, hsecondNe, hfirstNeOne, hsecondNeOne, hinterfaceNe⟩,
    columnMatrix (coefE • vec 0) (coefF • vec 1) (coefG • vec 3),
    twoMeetingLinesScale coefA coefC coefE coefF coefG bigDelta, ?_, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero, det_columnMatrix, tripleBracket_smul_slots]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hcoefENe hcoefFNe) hcoefGNe) hbasisNe
  · intro index
    rcases fin_six_cases index with rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_div_ne_zero hcoefENe
    · exact one_div_ne_zero hcoefFNe
    · exact div_ne_zero hcoefANe (mul_ne_zero hcoefENe hbasisNe)
    · exact one_div_ne_zero hcoefGNe
    · exact div_ne_zero hcoefCNe (mul_ne_zero hcoefENe hbasisNe)
    · exact one_div_ne_zero hbasisNe
  · intro index
    rcases fin_six_cases index with rfl | rfl | rfl | rfl | rfl | rfl
    · refine eq_div_smul_of_smul_eq_smul hcoefENe ?_
      rw [columnMatrix_mulVec, twoMeetingLinesDirection_zero]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      module
    · refine eq_div_smul_of_smul_eq_smul hcoefFNe ?_
      rw [columnMatrix_mulVec, twoMeetingLinesDirection_one]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      module
    · refine eq_div_smul_of_smul_eq_smul (mul_ne_zero hcoefENe hbasisNe) ?_
      rw [columnMatrix_mulVec, twoMeetingLinesDirection_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [mul_smul, hexpandTwo]
      match_scalars <;>
        first | ring1 | linear_combination hfirstSpec | linear_combination -hfirstSpec
    · refine eq_div_smul_of_smul_eq_smul hcoefGNe ?_
      rw [columnMatrix_mulVec, twoMeetingLinesDirection_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      module
    · refine eq_div_smul_of_smul_eq_smul (mul_ne_zero hcoefENe hbasisNe) ?_
      rw [columnMatrix_mulVec, twoMeetingLinesDirection_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [mul_smul, hexpandFour]
      match_scalars <;>
        first | ring1 | linear_combination hsecondSpec | linear_combination -hsecondSpec
    · refine eq_div_smul_of_smul_eq_smul hbasisNe ?_
      rw [columnMatrix_mulVec, twoMeetingLinesDirection_five]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [hexpandFive]
      module

/-! ## The covering -/

set_option maxHeartbeats 1000000 in
/-- **THE `#3` COVERING.**  Every primitive design realizing the two-meeting-lines
pattern sits on the `#3` chart at some admissible parameter. -/
theorem parameterizedChartCovers_twoMeetingLinesDirection :
    ParameterizedChartCovers twoMeetingLinesDirection
      IsAdmissibleTwoMeetingLinesParameter (lineFamilyPattern twoMeetingLinesFamily) := by
  intro design relabel _hprimitive hpattern
  have hsymmNe : ∀ leftIndex rightIndex : Fin 6, leftIndex ≠ rightIndex →
      relabel.symm leftIndex ≠ relabel.symm rightIndex := by
    intro leftIndex rightIndex hne heq
    exact hne (by simpa using congrArg relabel heq)
  have hbracket : ∀ leftIndex midIndex rightIndex : Fin 6,
      leftIndex ≠ midIndex → leftIndex ≠ rightIndex → midIndex ≠ rightIndex →
      (tripleBracket (design.atom (relabel.symm leftIndex))
          (design.atom (relabel.symm midIndex)) (design.atom (relabel.symm rightIndex)) = 0
        ↔ lineFamilyPattern twoMeetingLinesFamily leftIndex midIndex rightIndex) := by
    intro leftIndex midIndex rightIndex hleftMid hleftRight hmidRight
    have hraw := hpattern (relabel.symm leftIndex) (relabel.symm midIndex)
      (relabel.symm rightIndex) (hsymmNe _ _ hleftMid) (hsymmNe _ _ hleftRight)
      (hsymmNe _ _ hmidRight)
    simpa only [atomBracket, Equiv.apply_symm_apply] using hraw
  obtain ⟨param, hadmissible, basisChange, scale, hunit, hscaleNe, hrealize⟩ :=
    exists_twoMeetingLinesRealization_of_brackets
      (fun index => design.atom (relabel.symm index))
      (fun hzero => (by decide : ¬ lineFamilyPattern twoMeetingLinesFamily 0 1 3)
        ((hbracket 0 1 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern twoMeetingLinesFamily 2 1 3)
        ((hbracket 2 1 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern twoMeetingLinesFamily 0 2 3)
        ((hbracket 0 2 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern twoMeetingLinesFamily 4 1 3)
        ((hbracket 4 1 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern twoMeetingLinesFamily 0 1 4)
        ((hbracket 0 1 4 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern twoMeetingLinesFamily 5 1 3)
        ((hbracket 5 1 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern twoMeetingLinesFamily 0 5 3)
        ((hbracket 0 5 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern twoMeetingLinesFamily 0 1 5)
        ((hbracket 0 1 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern twoMeetingLinesFamily 2 3 5)
        ((hbracket 2 3 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern twoMeetingLinesFamily 1 4 5)
        ((hbracket 1 4 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern twoMeetingLinesFamily 2 4 5)
        ((hbracket 2 4 5 (by decide) (by decide) (by decide)).mp hzero))
      ((hbracket 0 1 2 (by decide) (by decide) (by decide)).mpr (by decide))
      ((hbracket 0 3 4 (by decide) (by decide) (by decide)).mpr (by decide))
  refine ⟨param, hadmissible, basisChange, fun label => scale (relabel label), hunit,
    fun label => hscaleNe (relabel label), fun label => ?_⟩
  have hstep := hrealize (relabel label)
  rwa [Equiv.symm_apply_apply] at hstep

/-- **THE `#3` STRATUM OBLIGATION FROM THE CHART.**  Tie-freeness of the
two-parameter `#3` chart at every admissible parameter gives the tree's residual
obligation for entry `#3`. -/
theorem stressFreeStratumIsTieFree_twoMeetingLines_of_chart
    (hchart : ∀ param : ℝ × ℝ, IsAdmissibleTwoMeetingLinesParameter param →
      DirectionChartIsTieFree (twoMeetingLinesDirection param)) :
    StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  stressFreeStratumIsTieFree_of_parameterizedChart hchart
    parameterizedChartCovers_twoMeetingLinesDirection

/-- The pattern discharged above is entry `#3` of the tree's residual list. -/
theorem twoMeetingLinesFamily_mem_stressFreeResidualFamiliesSix :
    ([[(0 : Fin 6), 1, 2], [0, 3, 4]] : List (List (Fin 6)))
      ∈ stressFreeResidualFamiliesSix := by decide

/-! ## A first chart-level cell at entry `#3`

The chart makes the landed general covering cell instantiable here for the first
time.  The basis triple `{0,1,3}` reads every label: atom `2` at `(1,p,0)`, atom
`4` at `(1,0,q)`, and the free atom `5` at `(1,1,1)`. -/

/-- The selected triple: the chart's own basis. -/
def twoMeetingLinesSelected : Finset (Fin 6) := {0, 1, 3}

/-- The combination coefficients of every label against the basis `{0,1,3}`. -/
def twoMeetingLinesCoeff (param : ℝ × ℝ) : Fin 6 → Fin 6 → ℝ
  | 0 => ![1, 0, 0, 0, 0, 0]
  | 1 => ![0, 1, 0, 0, 0, 0]
  | 2 => ![1, param.1, 0, 0, 0, 0]
  | 3 => ![0, 0, 0, 1, 0, 0]
  | 4 => ![1, 0, 0, param.2, 0, 0]
  | 5 => ![1, 1, 0, 1, 0, 0]

/-- The basis triple reads every label of the chart. -/
theorem readsThrough_twoMeetingLinesDirection (param : ℝ × ℝ) :
    ReadsThrough (twoMeetingLinesDirection param) twoMeetingLinesSelected
      (twoMeetingLinesCoeff param) := by
  intro label probe
  have hsum : twoMeetingLinesSelected = ({0, 1, 3} : Finset (Fin 6)) := rfl
  fin_cases label <;>
    simp [hsum, twoMeetingLinesDirection, twoMeetingLinesCoeff, dotProduct,
      Fin.sum_univ_three, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      add_assoc]

/-- **The general covering cell at entry `#3`.**  If every label's cover cost
against the basis triple is at most one, the basis triple is strictly
dominating.  This is the first chart-level cell available at this entry, and it
exists only because the chart does.

#UNFED-HYPOTHESIS.  The `hspan` argument is not open: labels `0`, `1` and `3` of
this chart are the coordinate axes, which is the same fact
`Gtz.posDef_massMoment_twoMeetingLinesDirection`
(Gtz/Design/ChartProgrammeAssembly.lean:254) already proves.  A caller must
still supply it by hand, and no caller exists. -/
theorem posDef_directionChartGap_twoMeetingLines_of_coverCell (param : ℝ × ℝ)
    (mass weight : Fin 6 → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label) (hsum : ∑ label, weight label = 1)
    (hspan : ∀ probe : Fin 3 → ℝ,
      (∀ label, twoMeetingLinesDirection param label ⬝ᵥ probe = 0) → probe = 0)
    (hcell : GeneralCoverCellFires (fun label => mass label / weight label)
      twoMeetingLinesSelected (twoMeetingLinesCoeff param)) :
    (directionChartGap (twoMeetingLinesDirection param) mass weight
      twoMeetingLinesSelected).PosDef :=
  posDef_directionChartGap_of_generalCoverCell (twoMeetingLinesDirection param) mass weight
    hmass hweight hsum hspan (by decide) (twoMeetingLinesCoeff param)
    (readsThrough_twoMeetingLinesDirection param) hcell

end Gtz
