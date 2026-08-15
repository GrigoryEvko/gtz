/-
# The one-line covering: entry `#2` sits on its own chart

`Gtz.oneLineDirection` charts entry `#2` of `Gtz.stressFreeResidualFamiliesSix`
at three parameters.  This file proves the COVERING half: every primitive design
realizing the pattern `[[0,1,2]]` is a chart point at some admissible parameter.
With `Gtz.stressFreeStratumIsTieFree_of_parameterizedChart` the entry `#2`
obligation becomes tie-freeness of a three-parameter chart, which is the shape
the campaign already carries at entries `#3`, `#4` and `#5`.

## The six bracket identities

Write `bigDelta = [013]` and read the nine expansion coefficients of
`Gtz.exists_oneLineCoordinates` in the basis `{0,1,3}`:

  `bigDelta . v2 = A . v0 + B . v1`,
  `bigDelta . v4 = C . v0 + D . v1 + E . v3`,
  `bigDelta . v5 = F . v0 + G . v1 + H . v3`.

Multilinearity of the bracket then pins the six triples that decide
admissibility, each of them a triple the pattern forbids to vanish:

  `bigDelta ^ 2 * [234] = (B C - A D) * bigDelta`,
  `bigDelta ^ 2 * [235] = (B F - A G) * bigDelta`,
  `bigDelta ^ 2 * [045] = (D H - E G) * bigDelta`,
  `bigDelta ^ 2 * [145] = (E F - C H) * bigDelta`,
  `bigDelta ^ 2 * [345] = (C G - D F) * bigDelta`,
  `bigDelta ^ 3 * [245] = (A D H - A E G - B C H + B E F) * bigDelta`.

Each is one `linear_combination` after rewriting the expansions into a bracket.

## The parameters and the frame

The columns `C . v0`, `D . v1`, `E . v3` carry atom `4` to `(1,1,1)` by
construction, and the three parameters come out as

  `slide = B C / (A D)`,  `freeMid = G C / (F D)`,  `freeLast = H C / (F E)`.

All three are introduced by a POLYNOMIAL spec rather than a quotient, so every
downstream step is division-free.  The nine admissibility exclusions are then
read off: `slide`, `freeMid` and `freeLast` nonzero from the coefficients alone,
and the remaining six from the six identities above.

FIFTEEN nonvanishing brackets are used — the nine coefficients and the six
off-pattern triples — against the eleven the `#3` covering needed.  The count
grows with the moduli, exactly as the frame does.

PRIMITIVITY IS NOT USED, as at entry `#3`: every exclusion already follows from
a bracket the pattern forbids to vanish.
-/
import Gtz.Design.OneLineChart
import Gtz.Design.GeneralCoverCell

namespace Gtz

open Matrix

/-! ## The six bracket identities -/

/-- The `{2,3,4}` bracket in the basis `{0,1,3}`.  Atom `2` spends its two
coefficients and atom `4` its three, and every repeated-slot term dies. -/
theorem tripleBracket_twoThreeFour_of_oneLineExpansions
    (vecZero vecOne vecTwo vecThree vecFour : Fin 3 → ℝ)
    (bigDelta coefA coefB coefC coefD coefE : ℝ)
    (hexpandTwo : bigDelta • vecTwo = coefA • vecZero + coefB • vecOne)
    (hexpandFour : bigDelta • vecFour
      = coefC • vecZero + coefD • vecOne + coefE • vecThree) :
    bigDelta ^ 2 * tripleBracket vecTwo vecThree vecFour
      = (coefB * coefC - coefA * coefD) * tripleBracket vecZero vecOne vecThree := by
  have hkey : tripleBracket (bigDelta • vecTwo) vecThree (bigDelta • vecFour)
      = tripleBracket (coefA • vecZero + coefB • vecOne) vecThree
          (coefC • vecZero + coefD • vecOne + coefE • vecThree) := by
    rw [hexpandTwo, hexpandFour]
  simp only [tripleBracket_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hkey
  simp only [tripleBracket_eq]
  linear_combination hkey

/-- The `{2,3,5}` bracket, the same shape with atom `5` in place of atom `4`. -/
theorem tripleBracket_twoThreeFive_of_oneLineExpansions
    (vecZero vecOne vecTwo vecThree vecFive : Fin 3 → ℝ)
    (bigDelta coefA coefB coefF coefG coefH : ℝ)
    (hexpandTwo : bigDelta • vecTwo = coefA • vecZero + coefB • vecOne)
    (hexpandFive : bigDelta • vecFive
      = coefF • vecZero + coefG • vecOne + coefH • vecThree) :
    bigDelta ^ 2 * tripleBracket vecTwo vecThree vecFive
      = (coefB * coefF - coefA * coefG) * tripleBracket vecZero vecOne vecThree := by
  have hkey : tripleBracket (bigDelta • vecTwo) vecThree (bigDelta • vecFive)
      = tripleBracket (coefA • vecZero + coefB • vecOne) vecThree
          (coefF • vecZero + coefG • vecOne + coefH • vecThree) := by
    rw [hexpandTwo, hexpandFive]
  simp only [tripleBracket_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hkey
  simp only [tripleBracket_eq]
  linear_combination hkey

/-- The `{0,4,5}` bracket: the two free atoms against the first basis vector. -/
theorem tripleBracket_zeroFourFive_of_oneLineExpansions
    (vecZero vecOne vecThree vecFour vecFive : Fin 3 → ℝ)
    (bigDelta coefC coefD coefE coefF coefG coefH : ℝ)
    (hexpandFour : bigDelta • vecFour
      = coefC • vecZero + coefD • vecOne + coefE • vecThree)
    (hexpandFive : bigDelta • vecFive
      = coefF • vecZero + coefG • vecOne + coefH • vecThree) :
    bigDelta ^ 2 * tripleBracket vecZero vecFour vecFive
      = (coefD * coefH - coefE * coefG) * tripleBracket vecZero vecOne vecThree := by
  have hkey : tripleBracket vecZero (bigDelta • vecFour) (bigDelta • vecFive)
      = tripleBracket vecZero (coefC • vecZero + coefD • vecOne + coefE • vecThree)
          (coefF • vecZero + coefG • vecOne + coefH • vecThree) := by
    rw [hexpandFour, hexpandFive]
  simp only [tripleBracket_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hkey
  simp only [tripleBracket_eq]
  linear_combination hkey

/-- The `{1,4,5}` bracket: the two free atoms against the second basis vector. -/
theorem tripleBracket_oneFourFive_of_oneLineExpansions
    (vecZero vecOne vecThree vecFour vecFive : Fin 3 → ℝ)
    (bigDelta coefC coefD coefE coefF coefG coefH : ℝ)
    (hexpandFour : bigDelta • vecFour
      = coefC • vecZero + coefD • vecOne + coefE • vecThree)
    (hexpandFive : bigDelta • vecFive
      = coefF • vecZero + coefG • vecOne + coefH • vecThree) :
    bigDelta ^ 2 * tripleBracket vecOne vecFour vecFive
      = (coefE * coefF - coefC * coefH) * tripleBracket vecZero vecOne vecThree := by
  have hkey : tripleBracket vecOne (bigDelta • vecFour) (bigDelta • vecFive)
      = tripleBracket vecOne (coefC • vecZero + coefD • vecOne + coefE • vecThree)
          (coefF • vecZero + coefG • vecOne + coefH • vecThree) := by
    rw [hexpandFour, hexpandFive]
  simp only [tripleBracket_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hkey
  simp only [tripleBracket_eq]
  linear_combination hkey

/-- The `{3,4,5}` bracket: the two free atoms against the third basis vector. -/
theorem tripleBracket_threeFourFive_of_oneLineExpansions
    (vecZero vecOne vecThree vecFour vecFive : Fin 3 → ℝ)
    (bigDelta coefC coefD coefE coefF coefG coefH : ℝ)
    (hexpandFour : bigDelta • vecFour
      = coefC • vecZero + coefD • vecOne + coefE • vecThree)
    (hexpandFive : bigDelta • vecFive
      = coefF • vecZero + coefG • vecOne + coefH • vecThree) :
    bigDelta ^ 2 * tripleBracket vecThree vecFour vecFive
      = (coefC * coefG - coefD * coefF) * tripleBracket vecZero vecOne vecThree := by
  have hkey : tripleBracket vecThree (bigDelta • vecFour) (bigDelta • vecFive)
      = tripleBracket vecThree (coefC • vecZero + coefD • vecOne + coefE • vecThree)
          (coefF • vecZero + coefG • vecOne + coefH • vecThree) := by
    rw [hexpandFour, hexpandFive]
  simp only [tripleBracket_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hkey
  simp only [tripleBracket_eq]
  linear_combination hkey

/-- The `{2,4,5}` bracket, the two-meeting-lines interface.  All three off-basis
atoms spend their coefficients at once, so the identity carries `bigDelta`
cubed. -/
theorem tripleBracket_twoFourFive_of_oneLineExpansions
    (vecZero vecOne vecTwo vecThree vecFour vecFive : Fin 3 → ℝ)
    (bigDelta coefA coefB coefC coefD coefE coefF coefG coefH : ℝ)
    (hexpandTwo : bigDelta • vecTwo = coefA • vecZero + coefB • vecOne)
    (hexpandFour : bigDelta • vecFour
      = coefC • vecZero + coefD • vecOne + coefE • vecThree)
    (hexpandFive : bigDelta • vecFive
      = coefF • vecZero + coefG • vecOne + coefH • vecThree) :
    bigDelta ^ 3 * tripleBracket vecTwo vecFour vecFive
      = (coefA * coefD * coefH - coefA * coefE * coefG - coefB * coefC * coefH
          + coefB * coefE * coefF) * tripleBracket vecZero vecOne vecThree := by
  have hkey : tripleBracket (bigDelta • vecTwo) (bigDelta • vecFour) (bigDelta • vecFive)
      = tripleBracket (coefA • vecZero + coefB • vecOne)
          (coefC • vecZero + coefD • vecOne + coefE • vecThree)
          (coefF • vecZero + coefG • vecOne + coefH • vecThree) := by
    rw [hexpandTwo, hexpandFour, hexpandFive]
  simp only [tripleBracket_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hkey
  simp only [tripleBracket_eq]
  linear_combination hkey

/-! ## The per-atom scales -/

/-- The per-atom scales of the `#2` realization, against the frame
`C . v0`, `D . v1`, `E . v3`. -/
noncomputable def oneLineScale (coefA coefC coefD coefE coefF bigDelta : ℝ) : Fin 6 → ℝ
  | 0 => 1 / coefC
  | 1 => 1 / coefD
  | 2 => coefA / (coefC * bigDelta)
  | 3 => 1 / coefE
  | 4 => 1 / bigDelta
  | 5 => coefF / (coefC * bigDelta)

/-! ## The realization, on bare vectors -/

set_option maxHeartbeats 1000000 in
/-- **THE `#2` RIGIDITY THEOREM, on bare vectors.**  Fifteen nonvanishing
brackets and the one line relation put an arbitrary configuration on the chart.
The three parameters are `slide = B C / (A D)`, `freeMid = G C / (F D)` and
`freeLast = H C / (F E)`, introduced by polynomial specs so that nothing
downstream divides. -/
theorem exists_oneLineRealization_of_brackets (vec : Fin 6 → (Fin 3 → ℝ))
    (hbasisNe : tripleBracket (vec 0) (vec 1) (vec 3) ≠ 0)
    (hcoefANe : tripleBracket (vec 2) (vec 1) (vec 3) ≠ 0)
    (hcoefBNe : tripleBracket (vec 0) (vec 2) (vec 3) ≠ 0)
    (hcoefCNe : tripleBracket (vec 4) (vec 1) (vec 3) ≠ 0)
    (hcoefDNe : tripleBracket (vec 0) (vec 4) (vec 3) ≠ 0)
    (hcoefENe : tripleBracket (vec 0) (vec 1) (vec 4) ≠ 0)
    (hcoefFNe : tripleBracket (vec 5) (vec 1) (vec 3) ≠ 0)
    (hcoefGNe : tripleBracket (vec 0) (vec 5) (vec 3) ≠ 0)
    (hcoefHNe : tripleBracket (vec 0) (vec 1) (vec 5) ≠ 0)
    (hoffTwoThreeFour : tripleBracket (vec 2) (vec 3) (vec 4) ≠ 0)
    (hoffTwoThreeFive : tripleBracket (vec 2) (vec 3) (vec 5) ≠ 0)
    (hoffZeroFourFive : tripleBracket (vec 0) (vec 4) (vec 5) ≠ 0)
    (hoffOneFourFive : tripleBracket (vec 1) (vec 4) (vec 5) ≠ 0)
    (hoffThreeFourFive : tripleBracket (vec 3) (vec 4) (vec 5) ≠ 0)
    (hoffTwoFourFive : tripleBracket (vec 2) (vec 4) (vec 5) ≠ 0)
    (hline : tripleBracket (vec 0) (vec 1) (vec 2) = 0) :
    ∃ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param ∧
      ∃ basisChange : Matrix (Fin 3) (Fin 3) ℝ, ∃ scale : Fin 6 → ℝ,
        IsUnit basisChange.det ∧ (∀ index, scale index ≠ 0) ∧
          ∀ index, vec index
            = scale index • (basisChange *ᵥ oneLineDirection param index) := by
  set bigDelta := tripleBracket (vec 0) (vec 1) (vec 3) with hbigDeltaDef
  set coefA := tripleBracket (vec 2) (vec 1) (vec 3) with hcoefADef
  set coefB := tripleBracket (vec 0) (vec 2) (vec 3) with hcoefBDef
  set coefC := tripleBracket (vec 4) (vec 1) (vec 3) with hcoefCDef
  set coefD := tripleBracket (vec 0) (vec 4) (vec 3) with hcoefDDef
  set coefE := tripleBracket (vec 0) (vec 1) (vec 4) with hcoefEDef
  set coefF := tripleBracket (vec 5) (vec 1) (vec 3) with hcoefFDef
  set coefG := tripleBracket (vec 0) (vec 5) (vec 3) with hcoefGDef
  set coefH := tripleBracket (vec 0) (vec 1) (vec 5) with hcoefHDef
  have hexpandTwo : bigDelta • vec 2 = coefA • vec 0 + coefB • vec 1 :=
    smul_oneLine_two_expansion vec hline
  have hexpandFour : bigDelta • vec 4 = coefC • vec 0 + coefD • vec 1 + coefE • vec 3 :=
    smul_oneLine_four_expansion vec
  have hexpandFive : bigDelta • vec 5 = coefF • vec 0 + coefG • vec 1 + coefH • vec 3 :=
    smul_oneLine_five_expansion vec
  -- The three parameters, pinned by polynomial specs.
  obtain ⟨slide, hslideSpec⟩ : ∃ slide : ℝ, slide * (coefA * coefD) = coefB * coefC :=
    ⟨coefB * coefC / (coefA * coefD), by field_simp⟩
  obtain ⟨freeMid, hmidSpec⟩ : ∃ freeMid : ℝ, freeMid * (coefF * coefD) = coefG * coefC :=
    ⟨coefG * coefC / (coefF * coefD), by field_simp⟩
  obtain ⟨freeLast, hlastSpec⟩ : ∃ freeLast : ℝ, freeLast * (coefF * coefE) = coefH * coefC :=
    ⟨coefH * coefC / (coefF * coefE), by field_simp⟩
  -- The six off-pattern brackets become the six nondegeneracy facts.
  have hbracketTwoThreeFour := tripleBracket_twoThreeFour_of_oneLineExpansions (vec 0)
    (vec 1) (vec 2) (vec 3) (vec 4) bigDelta coefA coefB coefC coefD coefE
    hexpandTwo hexpandFour
  have hbracketTwoThreeFive := tripleBracket_twoThreeFive_of_oneLineExpansions (vec 0)
    (vec 1) (vec 2) (vec 3) (vec 5) bigDelta coefA coefB coefF coefG coefH
    hexpandTwo hexpandFive
  have hbracketZeroFourFive := tripleBracket_zeroFourFive_of_oneLineExpansions (vec 0)
    (vec 1) (vec 3) (vec 4) (vec 5) bigDelta coefC coefD coefE coefF coefG coefH
    hexpandFour hexpandFive
  have hbracketOneFourFive := tripleBracket_oneFourFive_of_oneLineExpansions (vec 0)
    (vec 1) (vec 3) (vec 4) (vec 5) bigDelta coefC coefD coefE coefF coefG coefH
    hexpandFour hexpandFive
  have hbracketThreeFourFive := tripleBracket_threeFourFive_of_oneLineExpansions (vec 0)
    (vec 1) (vec 3) (vec 4) (vec 5) bigDelta coefC coefD coefE coefF coefG coefH
    hexpandFour hexpandFive
  have hbracketTwoFourFive := tripleBracket_twoFourFive_of_oneLineExpansions (vec 0)
    (vec 1) (vec 2) (vec 3) (vec 4) (vec 5) bigDelta coefA coefB coefC coefD coefE
    coefF coefG coefH hexpandTwo hexpandFour hexpandFive
  have hsquareNe : bigDelta ^ 2 ≠ 0 := pow_ne_zero 2 hbasisNe
  have hcubeNe : bigDelta ^ 3 ≠ 0 := pow_ne_zero 3 hbasisNe
  -- The three vanishing exclusions, straight from the specs.
  have hslideNe : slide ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hslideSpec
    exact (mul_ne_zero hcoefBNe hcoefCNe) hslideSpec.symm
  have hmidNe : freeMid ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hmidSpec
    exact (mul_ne_zero hcoefGNe hcoefCNe) hmidSpec.symm
  have hlastNe : freeLast ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hlastSpec
    exact (mul_ne_zero hcoefHNe hcoefCNe) hlastSpec.symm
  -- The three unit exclusions, one identity each.
  have hslideNeOne : slide ≠ 1 := by
    intro hone
    refine hoffTwoThreeFour ?_
    have hvanish : coefB * coefC - coefA * coefD = 0 := by
      rw [hone, one_mul] at hslideSpec; linarith
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 2) (vec 3) (vec 4) = 0 := by
      rw [hbracketTwoThreeFour, hvanish, zero_mul]
    exact (mul_eq_zero.mp hsquare).resolve_left hsquareNe
  have hmidNeOne : freeMid ≠ 1 := by
    intro hone
    refine hoffThreeFourFive ?_
    have hvanish : coefC * coefG - coefD * coefF = 0 := by
      rw [hone, one_mul] at hmidSpec; linarith
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 3) (vec 4) (vec 5) = 0 := by
      rw [hbracketThreeFourFive, hvanish, zero_mul]
    exact (mul_eq_zero.mp hsquare).resolve_left hsquareNe
  have hlastNeOne : freeLast ≠ 1 := by
    intro hone
    refine hoffOneFourFive ?_
    have hvanish : coefE * coefF - coefC * coefH = 0 := by
      rw [hone, one_mul] at hlastSpec; linarith
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 1) (vec 4) (vec 5) = 0 := by
      rw [hbracketOneFourFive, hvanish, zero_mul]
    exact (mul_eq_zero.mp hsquare).resolve_left hsquareNe
  -- The two difference exclusions.
  have hlastMidNe : freeLast - freeMid ≠ 0 := by
    intro hzero
    refine hoffZeroFourFive ?_
    have hvanish : coefD * coefH - coefE * coefG = 0 := by
      have hprod : coefC * (coefD * coefH - coefE * coefG)
          = coefD * coefE * coefF * (freeLast - freeMid) := by
        linear_combination coefE * hmidSpec - coefD * hlastSpec
      rw [hzero, mul_zero] at hprod
      exact (mul_eq_zero.mp hprod).resolve_left hcoefCNe
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 0) (vec 4) (vec 5) = 0 := by
      rw [hbracketZeroFourFive, hvanish, zero_mul]
    exact (mul_eq_zero.mp hsquare).resolve_left hsquareNe
  have hslideMidNe : slide - freeMid ≠ 0 := by
    intro hzero
    refine hoffTwoThreeFive ?_
    have hvanish : coefB * coefF - coefA * coefG = 0 := by
      have hprod : coefC * (coefB * coefF - coefA * coefG)
          = coefA * coefD * coefF * (slide - freeMid) := by
        linear_combination coefA * hmidSpec - coefF * hslideSpec
      rw [hzero, mul_zero] at hprod
      exact (mul_eq_zero.mp hprod).resolve_left hcoefCNe
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 2) (vec 3) (vec 5) = 0 := by
      rw [hbracketTwoThreeFive, hvanish, zero_mul]
    exact (mul_eq_zero.mp hsquare).resolve_left hsquareNe
  -- The interface exclusion.
  have hinterfaceNe :
      slide + freeLast - freeMid - slide * freeLast ≠ 0 := by
    intro hzero
    refine hoffTwoFourFive ?_
    have hvanish : coefA * coefD * coefH - coefA * coefE * coefG
        - coefB * coefC * coefH + coefB * coefE * coefF = 0 := by
      have hprod : (slide + freeLast - freeMid - slide * freeLast)
          * (coefA * coefD * coefF * coefE)
          = coefC * (coefA * coefD * coefH - coefA * coefE * coefG
              - coefB * coefC * coefH + coefB * coefE * coefF) := by
        linear_combination (coefF * coefE - freeLast * (coefF * coefE)) * hslideSpec
          + (coefA * coefD - coefB * coefC) * hlastSpec
          - coefA * coefE * hmidSpec
      rw [hzero, zero_mul] at hprod
      exact (mul_eq_zero.mp hprod.symm).resolve_left hcoefCNe
    have hcube : bigDelta ^ 3 * tripleBracket (vec 2) (vec 4) (vec 5) = 0 := by
      rw [hbracketTwoFourFive, hvanish, zero_mul]
    exact (mul_eq_zero.mp hcube).resolve_left hcubeNe
  refine ⟨(slide, freeMid, freeLast),
    ⟨hslideNe, hslideNeOne, hmidNe, hmidNeOne, hlastNe, hlastNeOne,
      hlastMidNe, hslideMidNe, hinterfaceNe⟩,
    columnMatrix (coefC • vec 0) (coefD • vec 1) (coefE • vec 3),
    oneLineScale coefA coefC coefD coefE coefF bigDelta, ?_, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero, det_columnMatrix, tripleBracket_smul_slots]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hcoefCNe hcoefDNe) hcoefENe) hbasisNe
  · intro index
    rcases fin_six_cases index with rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_div_ne_zero hcoefCNe
    · exact one_div_ne_zero hcoefDNe
    · exact div_ne_zero hcoefANe (mul_ne_zero hcoefCNe hbasisNe)
    · exact one_div_ne_zero hcoefENe
    · exact one_div_ne_zero hbasisNe
    · exact div_ne_zero hcoefFNe (mul_ne_zero hcoefCNe hbasisNe)
  · intro index
    rcases fin_six_cases index with rfl | rfl | rfl | rfl | rfl | rfl
    · refine eq_div_smul_of_smul_eq_smul hcoefCNe ?_
      rw [columnMatrix_mulVec, oneLineDirection_zero]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      module
    · refine eq_div_smul_of_smul_eq_smul hcoefDNe ?_
      rw [columnMatrix_mulVec, oneLineDirection_one]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      module
    · refine eq_div_smul_of_smul_eq_smul (mul_ne_zero hcoefCNe hbasisNe) ?_
      rw [columnMatrix_mulVec, oneLineDirection_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [mul_smul, hexpandTwo]
      match_scalars <;>
        first | ring1 | linear_combination hslideSpec | linear_combination -hslideSpec
    · refine eq_div_smul_of_smul_eq_smul hcoefENe ?_
      rw [columnMatrix_mulVec, oneLineDirection_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      module
    · refine eq_div_smul_of_smul_eq_smul hbasisNe ?_
      rw [columnMatrix_mulVec, oneLineDirection_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [hexpandFour]
      module
    · refine eq_div_smul_of_smul_eq_smul (mul_ne_zero hcoefCNe hbasisNe) ?_
      rw [columnMatrix_mulVec, oneLineDirection_five]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [mul_smul, hexpandFive]
      match_scalars <;>
        first
          | ring1
          | linear_combination hmidSpec | linear_combination -hmidSpec
          | linear_combination hlastSpec | linear_combination -hlastSpec

/-! ## The covering -/

set_option maxHeartbeats 1000000 in
/-- **THE `#2` COVERING.**  Every primitive design realizing the one-line pattern
sits on the `#2` chart at some admissible parameter. -/
theorem parameterizedChartCovers_oneLineDirection :
    ParameterizedChartCovers oneLineDirection
      IsAdmissibleOneLineParameter (lineFamilyPattern oneLineFamily) := by
  intro design relabel _hprimitive hpattern
  have hsymmNe : ∀ leftIndex rightIndex : Fin 6, leftIndex ≠ rightIndex →
      relabel.symm leftIndex ≠ relabel.symm rightIndex := by
    intro leftIndex rightIndex hne heq
    exact hne (by simpa using congrArg relabel heq)
  have hbracket : ∀ leftIndex midIndex rightIndex : Fin 6,
      leftIndex ≠ midIndex → leftIndex ≠ rightIndex → midIndex ≠ rightIndex →
      (tripleBracket (design.atom (relabel.symm leftIndex))
          (design.atom (relabel.symm midIndex)) (design.atom (relabel.symm rightIndex)) = 0
        ↔ lineFamilyPattern oneLineFamily leftIndex midIndex rightIndex) := by
    intro leftIndex midIndex rightIndex hleftMid hleftRight hmidRight
    have hraw := hpattern (relabel.symm leftIndex) (relabel.symm midIndex)
      (relabel.symm rightIndex) (hsymmNe _ _ hleftMid) (hsymmNe _ _ hleftRight)
      (hsymmNe _ _ hmidRight)
    simpa only [atomBracket, Equiv.apply_symm_apply] using hraw
  obtain ⟨param, hadmissible, basisChange, scale, hunit, hscaleNe, hrealize⟩ :=
    exists_oneLineRealization_of_brackets
      (fun index => design.atom (relabel.symm index))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 0 1 3)
        ((hbracket 0 1 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 2 1 3)
        ((hbracket 2 1 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 0 2 3)
        ((hbracket 0 2 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 4 1 3)
        ((hbracket 4 1 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 0 4 3)
        ((hbracket 0 4 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 0 1 4)
        ((hbracket 0 1 4 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 5 1 3)
        ((hbracket 5 1 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 0 5 3)
        ((hbracket 0 5 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 0 1 5)
        ((hbracket 0 1 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 2 3 4)
        ((hbracket 2 3 4 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 2 3 5)
        ((hbracket 2 3 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 0 4 5)
        ((hbracket 0 4 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 1 4 5)
        ((hbracket 1 4 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 3 4 5)
        ((hbracket 3 4 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern oneLineFamily 2 4 5)
        ((hbracket 2 4 5 (by decide) (by decide) (by decide)).mp hzero))
      ((hbracket 0 1 2 (by decide) (by decide) (by decide)).mpr (by decide))
  refine ⟨param, hadmissible, basisChange, fun label => scale (relabel label), hunit,
    fun label => hscaleNe (relabel label), fun label => ?_⟩
  have hstep := hrealize (relabel label)
  rwa [Equiv.symm_apply_apply] at hstep

/-- **THE `#2` STRATUM OBLIGATION FROM THE CHART.**  Tie-freeness of the
three-parameter `#2` chart at every admissible parameter gives the tree's
residual obligation for entry `#2`. -/
theorem stressFreeStratumIsTieFree_oneLine_of_chart
    (hchart : ∀ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param →
      DirectionChartIsTieFree (oneLineDirection param)) :
    StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  stressFreeStratumIsTieFree_of_parameterizedChart hchart
    parameterizedChartCovers_oneLineDirection

/-- The pattern discharged above is entry `#2` of the tree's residual list. -/
theorem oneLineFamily_mem_stressFreeResidualFamiliesSix :
    ([[(0 : Fin 6), 1, 2]] : List (List (Fin 6))) ∈ stressFreeResidualFamiliesSix := by
  decide

/-! ## A first chart-level cell at entry `#2`

The chart makes the landed general covering cell instantiable here for the first
time.  The basis triple `{0,1,3}` is the chart's own standard frame, so it reads
every label: atom `2` at `(1, slide, 0)`, atom `4` at `(1,1,1)`, and atom `5` at
`(1, freeMid, freeLast)`. -/

/-- The selected triple: the chart's own basis. -/
def oneLineSelected : Finset (Fin 6) := {0, 1, 3}

/-- The combination coefficients of every label against the basis `{0,1,3}`. -/
def oneLineCoeff (param : ℝ × ℝ × ℝ) : Fin 6 → Fin 6 → ℝ
  | 0 => ![1, 0, 0, 0, 0, 0]
  | 1 => ![0, 1, 0, 0, 0, 0]
  | 2 => ![1, param.1, 0, 0, 0, 0]
  | 3 => ![0, 0, 0, 1, 0, 0]
  | 4 => ![1, 1, 0, 1, 0, 0]
  | 5 => ![1, param.2.1, 0, param.2.2, 0, 0]

/-- The basis triple reads every label of the chart. -/
theorem readsThrough_oneLineDirection (param : ℝ × ℝ × ℝ) :
    ReadsThrough (oneLineDirection param) oneLineSelected (oneLineCoeff param) := by
  intro label probe
  have hsum : oneLineSelected = ({0, 1, 3} : Finset (Fin 6)) := rfl
  fin_cases label <;>
    simp [hsum, oneLineDirection, oneLineCoeff, dotProduct, Fin.sum_univ_three,
      Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, add_assoc]

/-- **The general covering cell at entry `#2`.**  If every label's cover cost
against the basis triple is at most one, the basis triple is strictly
dominating.  This is the first chart-level cell available at this entry, and it
exists only because the chart does. -/
theorem posDef_directionChartGap_oneLine_of_coverCell (param : ℝ × ℝ × ℝ)
    (mass weight : Fin 6 → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label) (hsum : ∑ label, weight label = 1)
    (hspan : ∀ probe : Fin 3 → ℝ,
      (∀ label, oneLineDirection param label ⬝ᵥ probe = 0) → probe = 0)
    (hcell : GeneralCoverCellFires (fun label => mass label / weight label)
      oneLineSelected (oneLineCoeff param)) :
    (directionChartGap (oneLineDirection param) mass weight oneLineSelected).PosDef :=
  posDef_directionChartGap_of_generalCoverCell (oneLineDirection param) mass weight
    hmass hweight hsum hspan (by decide) (oneLineCoeff param)
    (readsThrough_oneLineDirection param) hcell

end Gtz
