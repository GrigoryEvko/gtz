/-
# The line-free covering: entry `#1` sits on its own chart

`Gtz.lineFreeDirection` charts entry `#1` of `Gtz.stressFreeResidualFamiliesSix`
at four parameters.  This file proves the COVERING half: every primitive design
realizing the empty pattern is a chart point at some admissible parameter.  With
`Gtz.stressFreeStratumIsTieFree_of_parameterizedChart` the entry `#1` obligation
becomes tie-freeness of a four-parameter chart — the shape the campaign already
carries at entries `#2`, `#3`, `#4` and `#5`, and this is the last of the five.

## Four expansion laws, not ten identities

Write `bigDelta = [012]` and read the nine expansion coefficients of
`Gtz.exists_lineFreeCoordinates` in the basis `{0,1,2}`:

  `bigDelta . v3 = A . v0 + B . v1 + C . v2`,
  `bigDelta . v4 = D . v0 + E . v1 + F . v2`,
  `bigDelta . v5 = G . v0 + H . v1 + K . v2`.

Ten triples carry two or three off-basis atoms, and the empty pattern forbids
each of them to vanish.  All ten follow from FOUR laws, and all four follow from
the frame transform law `Gtz.tripleBracket_transpose_mulVec`, which the corpus
already carries.  Three laws take two expansions and read the bracket against
one frame vector, and the fourth takes three expansions:

  `bigDelta ^ 2 * [P X Y] = (x2 y3 - x3 y2) * [P Q R]`,
  `bigDelta ^ 2 * [Q X Y] = (x3 y1 - x1 y3) * [P Q R]`,
  `bigDelta ^ 2 * [R X Y] = (x1 y2 - x2 y1) * [P Q R]`,
  `bigDelta ^ 3 * [X Y Z] = det (x, y, z) * [P Q R]`.

The minor is the Cramer cofactor of the omitted frame slot.  The ten uses are
`P, Q, R = v0, v1, v2` against the three pairs from `{v3, v4, v5}`, plus the
three-expansion law once.

## The parameters and the frame

The columns `A . v0`, `B . v1`, `C . v2` carry atom `3` to `(1,1,1)` by
construction, and the four parameters come out as

  `fourMid  = E A / (D B)`,  `fourLast = F A / (D C)`,
  `fiveMid  = H A / (G B)`,  `fiveLast = K A / (G C)`.

All four are introduced by a POLYNOMIAL spec rather than a quotient, so every
downstream step is division-free.  The fourteen admissibility exclusions are
then read off: the four vanishing ones from the coefficients alone, and the
remaining ten from the ten identities above, one each.

TWENTY nonvanishing brackets are used — the ten coefficients and the ten
off-basis triples — which is every triple there is, because line-freeness
forbids all twenty to vanish.  The count grew eleven, fifteen, twenty across the
three coverings the campaign built, exactly as the frame did.

PRIMITIVITY IS NOT USED, as at entries `#2` and `#3`: every exclusion already
follows from a bracket the pattern forbids to vanish.
-/
import Gtz.Design.LineFreeChart
import Gtz.Design.GeneralCoverCell
import Gtz.Design.LineBranchLineFreeCoordinates

namespace Gtz

open Matrix

/-! ## The four expansion laws -/

/-- **The frame law.**  Three coordinate vectors read through a frame carry the
bracket of the coordinates times the bracket of the frame.  This is the corpus
transform law `Gtz.tripleBracket_transpose_mulVec` in column form. -/
theorem tripleBracket_columnMatrix_mulVec
    (colFirst colMid colLast xcoord ycoord zcoord : Fin 3 → ℝ) :
    tripleBracket (columnMatrix colFirst colMid colLast *ᵥ xcoord)
        (columnMatrix colFirst colMid colLast *ᵥ ycoord)
        (columnMatrix colFirst colMid colLast *ᵥ zcoord)
      = tripleBracket xcoord ycoord zcoord
        * tripleBracket colFirst colMid colLast := by
  have hkey := tripleBracket_transpose_mulVec
    (columnMatrix colFirst colMid colLast)ᵀ xcoord ycoord zcoord
  rw [Matrix.transpose_transpose, Matrix.det_transpose, det_columnMatrix] at hkey
  exact hkey

/-- **The first slot.**  Two expansions against the first frame vector give the
Cramer cofactor of the first column. -/
theorem tripleBracket_firstSlot_of_expansions
    (baseFirst baseMid baseLast probeLeft probeRight : Fin 3 → ℝ)
    (bigDelta leftFirst leftMid leftLast rightFirst rightMid rightLast : ℝ)
    (hleft : bigDelta • probeLeft
      = leftFirst • baseFirst + leftMid • baseMid + leftLast • baseLast)
    (hright : bigDelta • probeRight
      = rightFirst • baseFirst + rightMid • baseMid + rightLast • baseLast) :
    bigDelta ^ 2 * tripleBracket baseFirst probeLeft probeRight
      = (leftMid * rightLast - leftLast * rightMid)
        * tripleBracket baseFirst baseMid baseLast := by
  have hframe := tripleBracket_columnMatrix_mulVec baseFirst baseMid baseLast
    ![1, 0, 0] ![leftFirst, leftMid, leftLast] ![rightFirst, rightMid, rightLast]
  rw [columnMatrix_mulVec, columnMatrix_mulVec, columnMatrix_mulVec] at hframe
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, one_smul, zero_smul, add_zero] at hframe
  rw [← hleft, ← hright] at hframe
  have hscale : tripleBracket baseFirst (bigDelta • probeLeft) (bigDelta • probeRight)
      = bigDelta ^ 2 * tripleBracket baseFirst probeLeft probeRight := by
    simp only [tripleBracket_eq, Pi.smul_apply, smul_eq_mul]; ring
  rw [hscale] at hframe
  rw [hframe]
  simp only [tripleBracket_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **The second slot.**  The Cramer cofactor of the second column. -/
theorem tripleBracket_secondSlot_of_expansions
    (baseFirst baseMid baseLast probeLeft probeRight : Fin 3 → ℝ)
    (bigDelta leftFirst leftMid leftLast rightFirst rightMid rightLast : ℝ)
    (hleft : bigDelta • probeLeft
      = leftFirst • baseFirst + leftMid • baseMid + leftLast • baseLast)
    (hright : bigDelta • probeRight
      = rightFirst • baseFirst + rightMid • baseMid + rightLast • baseLast) :
    bigDelta ^ 2 * tripleBracket baseMid probeLeft probeRight
      = (leftLast * rightFirst - leftFirst * rightLast)
        * tripleBracket baseFirst baseMid baseLast := by
  have hframe := tripleBracket_columnMatrix_mulVec baseFirst baseMid baseLast
    ![0, 1, 0] ![leftFirst, leftMid, leftLast] ![rightFirst, rightMid, rightLast]
  rw [columnMatrix_mulVec, columnMatrix_mulVec, columnMatrix_mulVec] at hframe
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, one_smul, zero_smul, add_zero,
    zero_add] at hframe
  rw [← hleft, ← hright] at hframe
  have hscale : tripleBracket baseMid (bigDelta • probeLeft) (bigDelta • probeRight)
      = bigDelta ^ 2 * tripleBracket baseMid probeLeft probeRight := by
    simp only [tripleBracket_eq, Pi.smul_apply, smul_eq_mul]; ring
  rw [hscale] at hframe
  rw [hframe]
  simp only [tripleBracket_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **The third slot.**  The Cramer cofactor of the third column. -/
theorem tripleBracket_thirdSlot_of_expansions
    (baseFirst baseMid baseLast probeLeft probeRight : Fin 3 → ℝ)
    (bigDelta leftFirst leftMid leftLast rightFirst rightMid rightLast : ℝ)
    (hleft : bigDelta • probeLeft
      = leftFirst • baseFirst + leftMid • baseMid + leftLast • baseLast)
    (hright : bigDelta • probeRight
      = rightFirst • baseFirst + rightMid • baseMid + rightLast • baseLast) :
    bigDelta ^ 2 * tripleBracket baseLast probeLeft probeRight
      = (leftFirst * rightMid - leftMid * rightFirst)
        * tripleBracket baseFirst baseMid baseLast := by
  have hframe := tripleBracket_columnMatrix_mulVec baseFirst baseMid baseLast
    ![0, 0, 1] ![leftFirst, leftMid, leftLast] ![rightFirst, rightMid, rightLast]
  rw [columnMatrix_mulVec, columnMatrix_mulVec, columnMatrix_mulVec] at hframe
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, one_smul, zero_smul, add_zero,
    zero_add] at hframe
  rw [← hleft, ← hright] at hframe
  have hscale : tripleBracket baseLast (bigDelta • probeLeft) (bigDelta • probeRight)
      = bigDelta ^ 2 * tripleBracket baseLast probeLeft probeRight := by
    simp only [tripleBracket_eq, Pi.smul_apply, smul_eq_mul]; ring
  rw [hscale] at hframe
  rw [hframe]
  simp only [tripleBracket_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **The three-expansion law.**  All three off-frame atoms at once, so the
bracket carries `bigDelta` cubed and the minor is the full determinant. -/
theorem tripleBracket_of_three_expansions
    (baseFirst baseMid baseLast probeOne probeTwo probeThree : Fin 3 → ℝ)
    (bigDelta oneFirst oneMid oneLast twoFirst twoMid twoLast
      threeFirst threeMid threeLast : ℝ)
    (hone : bigDelta • probeOne
      = oneFirst • baseFirst + oneMid • baseMid + oneLast • baseLast)
    (htwo : bigDelta • probeTwo
      = twoFirst • baseFirst + twoMid • baseMid + twoLast • baseLast)
    (hthree : bigDelta • probeThree
      = threeFirst • baseFirst + threeMid • baseMid + threeLast • baseLast) :
    bigDelta ^ 3 * tripleBracket probeOne probeTwo probeThree
      = (oneFirst * (twoMid * threeLast - twoLast * threeMid)
          - oneMid * (twoFirst * threeLast - twoLast * threeFirst)
          + oneLast * (twoFirst * threeMid - twoMid * threeFirst))
        * tripleBracket baseFirst baseMid baseLast := by
  have hframe := tripleBracket_columnMatrix_mulVec baseFirst baseMid baseLast
    ![oneFirst, oneMid, oneLast] ![twoFirst, twoMid, twoLast]
    ![threeFirst, threeMid, threeLast]
  rw [columnMatrix_mulVec, columnMatrix_mulVec, columnMatrix_mulVec] at hframe
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hframe
  rw [← hone, ← htwo, ← hthree, tripleBracket_smul_slots] at hframe
  rw [show bigDelta ^ 3 = bigDelta * bigDelta * bigDelta by ring, hframe]
  simp only [tripleBracket_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-! ## The per-atom scales -/

/-- The per-atom scales of the `#1` realization, against the frame
`A . v0`, `B . v1`, `C . v2`. -/
noncomputable def lineFreeScale (coefA coefB coefC coefD coefG bigDelta : ℝ) :
    Fin 6 → ℝ
  | 0 => 1 / coefA
  | 1 => 1 / coefB
  | 2 => 1 / coefC
  | 3 => 1 / bigDelta
  | 4 => coefD / (coefA * bigDelta)
  | 5 => coefG / (coefA * bigDelta)

/-! ## The realization, on bare vectors -/

set_option maxHeartbeats 2000000 in
/-- **THE `#1` RIGIDITY THEOREM, on bare vectors.**  Twenty nonvanishing
brackets — every triple there is — put an arbitrary configuration on the chart.
The four parameters are `fourMid = E A / (D B)`, `fourLast = F A / (D C)`,
`fiveMid = H A / (G B)` and `fiveLast = K A / (G C)`, introduced by polynomial
specs so that nothing downstream divides. -/
theorem exists_lineFreeRealization_of_brackets (vec : Fin 6 → (Fin 3 → ℝ))
    (hbasisNe : tripleBracket (vec 0) (vec 1) (vec 2) ≠ 0)
    (hcoefANe : tripleBracket (vec 3) (vec 1) (vec 2) ≠ 0)
    (hcoefBNe : tripleBracket (vec 0) (vec 3) (vec 2) ≠ 0)
    (hcoefCNe : tripleBracket (vec 0) (vec 1) (vec 3) ≠ 0)
    (hcoefDNe : tripleBracket (vec 4) (vec 1) (vec 2) ≠ 0)
    (hcoefENe : tripleBracket (vec 0) (vec 4) (vec 2) ≠ 0)
    (hcoefFNe : tripleBracket (vec 0) (vec 1) (vec 4) ≠ 0)
    (hcoefGNe : tripleBracket (vec 5) (vec 1) (vec 2) ≠ 0)
    (hcoefHNe : tripleBracket (vec 0) (vec 5) (vec 2) ≠ 0)
    (hcoefKNe : tripleBracket (vec 0) (vec 1) (vec 5) ≠ 0)
    (hoffZeroThreeFour : tripleBracket (vec 0) (vec 3) (vec 4) ≠ 0)
    (hoffZeroThreeFive : tripleBracket (vec 0) (vec 3) (vec 5) ≠ 0)
    (hoffZeroFourFive : tripleBracket (vec 0) (vec 4) (vec 5) ≠ 0)
    (hoffOneThreeFour : tripleBracket (vec 1) (vec 3) (vec 4) ≠ 0)
    (hoffOneThreeFive : tripleBracket (vec 1) (vec 3) (vec 5) ≠ 0)
    (hoffOneFourFive : tripleBracket (vec 1) (vec 4) (vec 5) ≠ 0)
    (hoffTwoThreeFour : tripleBracket (vec 2) (vec 3) (vec 4) ≠ 0)
    (hoffTwoThreeFive : tripleBracket (vec 2) (vec 3) (vec 5) ≠ 0)
    (hoffTwoFourFive : tripleBracket (vec 2) (vec 4) (vec 5) ≠ 0)
    (hoffThreeFourFive : tripleBracket (vec 3) (vec 4) (vec 5) ≠ 0) :
    ∃ param : ℝ × ℝ × ℝ × ℝ, IsAdmissibleLineFreeParameter param ∧
      ∃ basisChange : Matrix (Fin 3) (Fin 3) ℝ, ∃ scale : Fin 6 → ℝ,
        IsUnit basisChange.det ∧ (∀ index, scale index ≠ 0) ∧
          ∀ index, vec index
            = scale index • (basisChange *ᵥ lineFreeDirection param index) := by
  set bigDelta := tripleBracket (vec 0) (vec 1) (vec 2) with hbigDeltaDef
  set coefA := tripleBracket (vec 3) (vec 1) (vec 2) with hcoefADef
  set coefB := tripleBracket (vec 0) (vec 3) (vec 2) with hcoefBDef
  set coefC := tripleBracket (vec 0) (vec 1) (vec 3) with hcoefCDef
  set coefD := tripleBracket (vec 4) (vec 1) (vec 2) with hcoefDDef
  set coefE := tripleBracket (vec 0) (vec 4) (vec 2) with hcoefEDef
  set coefF := tripleBracket (vec 0) (vec 1) (vec 4) with hcoefFDef
  set coefG := tripleBracket (vec 5) (vec 1) (vec 2) with hcoefGDef
  set coefH := tripleBracket (vec 0) (vec 5) (vec 2) with hcoefHDef
  set coefK := tripleBracket (vec 0) (vec 1) (vec 5) with hcoefKDef
  have hexpandThree : bigDelta • vec 3 = coefA • vec 0 + coefB • vec 1 + coefC • vec 2 :=
    smul_lineFree_three_expansion vec
  have hexpandFour : bigDelta • vec 4 = coefD • vec 0 + coefE • vec 1 + coefF • vec 2 :=
    smul_lineFree_four_expansion vec
  have hexpandFive : bigDelta • vec 5 = coefG • vec 0 + coefH • vec 1 + coefK • vec 2 :=
    smul_lineFree_five_expansion vec
  -- The four parameters, pinned by polynomial specs.
  obtain ⟨fourMid, hfourMidSpec⟩ :
      ∃ fourMid : ℝ, fourMid * (coefD * coefB) = coefE * coefA :=
    ⟨coefE * coefA / (coefD * coefB), by field_simp⟩
  obtain ⟨fourLast, hfourLastSpec⟩ :
      ∃ fourLast : ℝ, fourLast * (coefD * coefC) = coefF * coefA :=
    ⟨coefF * coefA / (coefD * coefC), by field_simp⟩
  obtain ⟨fiveMid, hfiveMidSpec⟩ :
      ∃ fiveMid : ℝ, fiveMid * (coefG * coefB) = coefH * coefA :=
    ⟨coefH * coefA / (coefG * coefB), by field_simp⟩
  obtain ⟨fiveLast, hfiveLastSpec⟩ :
      ∃ fiveLast : ℝ, fiveLast * (coefG * coefC) = coefK * coefA :=
    ⟨coefK * coefA / (coefG * coefC), by field_simp⟩
  -- The ten off-basis brackets become the ten nondegeneracy facts.
  have hbrZeroThreeFour := tripleBracket_firstSlot_of_expansions (vec 0) (vec 1)
    (vec 2) (vec 3) (vec 4) bigDelta coefA coefB coefC coefD coefE coefF
    hexpandThree hexpandFour
  have hbrZeroThreeFive := tripleBracket_firstSlot_of_expansions (vec 0) (vec 1)
    (vec 2) (vec 3) (vec 5) bigDelta coefA coefB coefC coefG coefH coefK
    hexpandThree hexpandFive
  have hbrZeroFourFive := tripleBracket_firstSlot_of_expansions (vec 0) (vec 1)
    (vec 2) (vec 4) (vec 5) bigDelta coefD coefE coefF coefG coefH coefK
    hexpandFour hexpandFive
  have hbrOneThreeFour := tripleBracket_secondSlot_of_expansions (vec 0) (vec 1)
    (vec 2) (vec 3) (vec 4) bigDelta coefA coefB coefC coefD coefE coefF
    hexpandThree hexpandFour
  have hbrOneThreeFive := tripleBracket_secondSlot_of_expansions (vec 0) (vec 1)
    (vec 2) (vec 3) (vec 5) bigDelta coefA coefB coefC coefG coefH coefK
    hexpandThree hexpandFive
  have hbrOneFourFive := tripleBracket_secondSlot_of_expansions (vec 0) (vec 1)
    (vec 2) (vec 4) (vec 5) bigDelta coefD coefE coefF coefG coefH coefK
    hexpandFour hexpandFive
  have hbrTwoThreeFour := tripleBracket_thirdSlot_of_expansions (vec 0) (vec 1)
    (vec 2) (vec 3) (vec 4) bigDelta coefA coefB coefC coefD coefE coefF
    hexpandThree hexpandFour
  have hbrTwoThreeFive := tripleBracket_thirdSlot_of_expansions (vec 0) (vec 1)
    (vec 2) (vec 3) (vec 5) bigDelta coefA coefB coefC coefG coefH coefK
    hexpandThree hexpandFive
  have hbrTwoFourFive := tripleBracket_thirdSlot_of_expansions (vec 0) (vec 1)
    (vec 2) (vec 4) (vec 5) bigDelta coefD coefE coefF coefG coefH coefK
    hexpandFour hexpandFive
  have hbrThreeFourFive := tripleBracket_of_three_expansions (vec 0) (vec 1)
    (vec 2) (vec 3) (vec 4) (vec 5) bigDelta coefA coefB coefC coefD coefE
    coefF coefG coefH coefK hexpandThree hexpandFour hexpandFive
  have hsquareNe : bigDelta ^ 2 ≠ 0 := pow_ne_zero 2 hbasisNe
  have hcubeNe : bigDelta ^ 3 ≠ 0 := pow_ne_zero 3 hbasisNe
  -- The four vanishing exclusions, straight from the specs.
  have hfourMidNe : fourMid ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hfourMidSpec
    exact (mul_ne_zero hcoefENe hcoefANe) hfourMidSpec.symm
  have hfourLastNe : fourLast ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hfourLastSpec
    exact (mul_ne_zero hcoefFNe hcoefANe) hfourLastSpec.symm
  have hfiveMidNe : fiveMid ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hfiveMidSpec
    exact (mul_ne_zero hcoefHNe hcoefANe) hfiveMidSpec.symm
  have hfiveLastNe : fiveLast ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hfiveLastSpec
    exact (mul_ne_zero hcoefKNe hcoefANe) hfiveLastSpec.symm
  -- The four unit exclusions, one identity each.
  have hfourMidNeOne : fourMid ≠ 1 := by
    intro hone
    refine hoffTwoThreeFour ?_
    have hvanish : coefA * coefE - coefB * coefD = 0 := by
      rw [hone, one_mul] at hfourMidSpec; linarith
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 2) (vec 3) (vec 4) = 0 := by
      rw [hbrTwoThreeFour, hvanish, zero_mul]
    exact (mul_eq_zero.mp hsquare).resolve_left hsquareNe
  have hfourLastNeOne : fourLast ≠ 1 := by
    intro hone
    refine hoffOneThreeFour ?_
    have hvanish : coefC * coefD - coefA * coefF = 0 := by
      rw [hone, one_mul] at hfourLastSpec; linarith
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 1) (vec 3) (vec 4) = 0 := by
      rw [hbrOneThreeFour, hvanish, zero_mul]
    exact (mul_eq_zero.mp hsquare).resolve_left hsquareNe
  have hfiveMidNeOne : fiveMid ≠ 1 := by
    intro hone
    refine hoffTwoThreeFive ?_
    have hvanish : coefA * coefH - coefB * coefG = 0 := by
      rw [hone, one_mul] at hfiveMidSpec; linarith
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 2) (vec 3) (vec 5) = 0 := by
      rw [hbrTwoThreeFive, hvanish, zero_mul]
    exact (mul_eq_zero.mp hsquare).resolve_left hsquareNe
  have hfiveLastNeOne : fiveLast ≠ 1 := by
    intro hone
    refine hoffOneThreeFive ?_
    have hvanish : coefC * coefG - coefA * coefK = 0 := by
      rw [hone, one_mul] at hfiveLastSpec; linarith
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 1) (vec 3) (vec 5) = 0 := by
      rw [hbrOneThreeFive, hvanish, zero_mul]
    exact (mul_eq_zero.mp hsquare).resolve_left hsquareNe
  -- The four difference exclusions.
  have hfourDiffNe : fourLast - fourMid ≠ 0 := by
    intro hzero
    refine hoffZeroThreeFour ?_
    have hvanish : coefB * coefF - coefC * coefE = 0 := by
      have hprod : coefA * (coefB * coefF - coefC * coefE)
          = coefD * coefB * coefC * (fourLast - fourMid) := by
        linear_combination coefC * hfourMidSpec - coefB * hfourLastSpec
      rw [hzero, mul_zero] at hprod
      exact (mul_eq_zero.mp hprod).resolve_left hcoefANe
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 0) (vec 3) (vec 4) = 0 := by
      rw [hbrZeroThreeFour, hvanish, zero_mul]
    exact (mul_eq_zero.mp hsquare).resolve_left hsquareNe
  have hfiveDiffNe : fiveLast - fiveMid ≠ 0 := by
    intro hzero
    refine hoffZeroThreeFive ?_
    have hvanish : coefB * coefK - coefC * coefH = 0 := by
      have hprod : coefA * (coefB * coefK - coefC * coefH)
          = coefG * coefB * coefC * (fiveLast - fiveMid) := by
        linear_combination coefC * hfiveMidSpec - coefB * hfiveLastSpec
      rw [hzero, mul_zero] at hprod
      exact (mul_eq_zero.mp hprod).resolve_left hcoefANe
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 0) (vec 3) (vec 5) = 0 := by
      rw [hbrZeroThreeFive, hvanish, zero_mul]
    exact (mul_eq_zero.mp hsquare).resolve_left hsquareNe
  have hlastDiffNe : fourLast - fiveLast ≠ 0 := by
    intro hzero
    refine hoffOneFourFive ?_
    have hvanish : coefF * coefG - coefD * coefK = 0 := by
      have hprod : coefA * (coefF * coefG - coefD * coefK)
          = coefD * coefG * coefC * (fourLast - fiveLast) := by
        linear_combination coefD * hfiveLastSpec - coefG * hfourLastSpec
      rw [hzero, mul_zero] at hprod
      exact (mul_eq_zero.mp hprod).resolve_left hcoefANe
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 1) (vec 4) (vec 5) = 0 := by
      rw [hbrOneFourFive, hvanish, zero_mul]
    exact (mul_eq_zero.mp hsquare).resolve_left hsquareNe
  have hmidDiffNe : fiveMid - fourMid ≠ 0 := by
    intro hzero
    refine hoffTwoFourFive ?_
    have hvanish : coefD * coefH - coefE * coefG = 0 := by
      have hprod : coefA * (coefD * coefH - coefE * coefG)
          = coefD * coefG * coefB * (fiveMid - fourMid) := by
        linear_combination coefG * hfourMidSpec - coefD * hfiveMidSpec
      rw [hzero, mul_zero] at hprod
      exact (mul_eq_zero.mp hprod).resolve_left hcoefANe
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 2) (vec 4) (vec 5) = 0 := by
      rw [hbrTwoFourFive, hvanish, zero_mul]
    exact (mul_eq_zero.mp hsquare).resolve_left hsquareNe
  -- The two determinant exclusions.
  have hminorNe : fourMid * fiveLast - fourLast * fiveMid ≠ 0 := by
    intro hzero
    refine hoffZeroFourFive ?_
    have hvanish : coefE * coefK - coefF * coefH = 0 := by
      have hprod : coefA ^ 2 * (coefE * coefK - coefF * coefH)
          = coefD * coefG * coefB * coefC
            * (fourMid * fiveLast - fourLast * fiveMid) := by
        linear_combination (fiveMid * (coefG * coefB)) * hfourLastSpec
          + (coefF * coefA) * hfiveMidSpec
          - (fiveLast * (coefG * coefC)) * hfourMidSpec
          - (coefE * coefA) * hfiveLastSpec
      rw [hzero, mul_zero] at hprod
      exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 hcoefANe)
    have hsquare : bigDelta ^ 2 * tripleBracket (vec 0) (vec 4) (vec 5) = 0 := by
      rw [hbrZeroFourFive, hvanish, zero_mul]
    exact (mul_eq_zero.mp hsquare).resolve_left hsquareNe
  have hcubicNe : fourMid * fiveLast - fourLast * fiveMid
      - fiveLast + fourLast + fiveMid - fourMid ≠ 0 := by
    intro hzero
    refine hoffThreeFourFive ?_
    have hvanish : coefA * (coefE * coefK - coefF * coefH)
        - coefB * (coefD * coefK - coefF * coefG)
        + coefC * (coefD * coefH - coefE * coefG) = 0 := by
      have hprod : coefA * (coefA * (coefE * coefK - coefF * coefH)
            - coefB * (coefD * coefK - coefF * coefG)
            + coefC * (coefD * coefH - coefE * coefG))
          = coefD * coefG * coefB * coefC
            * (fourMid * fiveLast - fourLast * fiveMid
                - fiveLast + fourLast + fiveMid - fourMid) := by
        linear_combination (coefG * coefC * (1 - fiveLast)) * hfourMidSpec
          + (coefG * coefB * (fiveMid - 1)) * hfourLastSpec
          + (coefF * coefA - coefC * coefD) * hfiveMidSpec
          + (coefB * coefD - coefE * coefA) * hfiveLastSpec
      rw [hzero, mul_zero] at hprod
      exact (mul_eq_zero.mp hprod).resolve_left hcoefANe
    have hcube : bigDelta ^ 3 * tripleBracket (vec 3) (vec 4) (vec 5) = 0 := by
      rw [hbrThreeFourFive, hvanish, zero_mul]
    exact (mul_eq_zero.mp hcube).resolve_left hcubeNe
  refine ⟨(fourMid, fourLast, fiveMid, fiveLast),
    ⟨hfourMidNe, hfourMidNeOne, hfourLastNe, hfourLastNeOne,
      hfiveMidNe, hfiveMidNeOne, hfiveLastNe, hfiveLastNeOne,
      hfourDiffNe, hfiveDiffNe, hlastDiffNe, hmidDiffNe, hminorNe, hcubicNe⟩,
    columnMatrix (coefA • vec 0) (coefB • vec 1) (coefC • vec 2),
    lineFreeScale coefA coefB coefC coefD coefG bigDelta, ?_, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero, det_columnMatrix, tripleBracket_smul_slots]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hcoefANe hcoefBNe) hcoefCNe) hbasisNe
  · intro index
    rcases fin_six_cases index with rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_div_ne_zero hcoefANe
    · exact one_div_ne_zero hcoefBNe
    · exact one_div_ne_zero hcoefCNe
    · exact one_div_ne_zero hbasisNe
    · exact div_ne_zero hcoefDNe (mul_ne_zero hcoefANe hbasisNe)
    · exact div_ne_zero hcoefGNe (mul_ne_zero hcoefANe hbasisNe)
  · intro index
    rcases fin_six_cases index with rfl | rfl | rfl | rfl | rfl | rfl
    · refine eq_div_smul_of_smul_eq_smul hcoefANe ?_
      rw [columnMatrix_mulVec, lineFreeDirection_zero]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      module
    · refine eq_div_smul_of_smul_eq_smul hcoefBNe ?_
      rw [columnMatrix_mulVec, lineFreeDirection_one]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      module
    · refine eq_div_smul_of_smul_eq_smul hcoefCNe ?_
      rw [columnMatrix_mulVec, lineFreeDirection_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      module
    · refine eq_div_smul_of_smul_eq_smul hbasisNe ?_
      rw [columnMatrix_mulVec, lineFreeDirection_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [hexpandThree]
      module
    · refine eq_div_smul_of_smul_eq_smul (mul_ne_zero hcoefANe hbasisNe) ?_
      rw [columnMatrix_mulVec, lineFreeDirection_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [mul_smul, hexpandFour]
      match_scalars <;>
        first
          | ring1
          | linear_combination hfourMidSpec | linear_combination -hfourMidSpec
          | linear_combination hfourLastSpec | linear_combination -hfourLastSpec
    · refine eq_div_smul_of_smul_eq_smul (mul_ne_zero hcoefANe hbasisNe) ?_
      rw [columnMatrix_mulVec, lineFreeDirection_five]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [mul_smul, hexpandFive]
      match_scalars <;>
        first
          | ring1
          | linear_combination hfiveMidSpec | linear_combination -hfiveMidSpec
          | linear_combination hfiveLastSpec | linear_combination -hfiveLastSpec

/-! ## The covering -/

set_option maxHeartbeats 2000000 in
/-- **THE `#1` COVERING.**  Every primitive design realizing the empty pattern
sits on the `#1` chart at some admissible parameter.  This is the last of the
five cells to be charted. -/
theorem parameterizedChartCovers_lineFreeDirection :
    ParameterizedChartCovers lineFreeDirection
      IsAdmissibleLineFreeParameter (lineFamilyPattern lineFreeFamily) := by
  intro design relabel _hprimitive hpattern
  have hsymmNe : ∀ leftIndex rightIndex : Fin 6, leftIndex ≠ rightIndex →
      relabel.symm leftIndex ≠ relabel.symm rightIndex := by
    intro leftIndex rightIndex hne heq
    exact hne (by simpa using congrArg relabel heq)
  have hbracket : ∀ leftIndex midIndex rightIndex : Fin 6,
      leftIndex ≠ midIndex → leftIndex ≠ rightIndex → midIndex ≠ rightIndex →
      (tripleBracket (design.atom (relabel.symm leftIndex))
          (design.atom (relabel.symm midIndex))
          (design.atom (relabel.symm rightIndex)) = 0
        ↔ lineFamilyPattern lineFreeFamily leftIndex midIndex rightIndex) := by
    intro leftIndex midIndex rightIndex hleftMid hleftRight hmidRight
    have hraw := hpattern (relabel.symm leftIndex) (relabel.symm midIndex)
      (relabel.symm rightIndex) (hsymmNe _ _ hleftMid) (hsymmNe _ _ hleftRight)
      (hsymmNe _ _ hmidRight)
    simpa only [atomBracket, Equiv.apply_symm_apply] using hraw
  obtain ⟨param, hadmissible, basisChange, scale, hunit, hscaleNe, hrealize⟩ :=
    exists_lineFreeRealization_of_brackets
      (fun index => design.atom (relabel.symm index))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 0 1 2)
        ((hbracket 0 1 2 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 3 1 2)
        ((hbracket 3 1 2 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 0 3 2)
        ((hbracket 0 3 2 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 0 1 3)
        ((hbracket 0 1 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 4 1 2)
        ((hbracket 4 1 2 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 0 4 2)
        ((hbracket 0 4 2 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 0 1 4)
        ((hbracket 0 1 4 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 5 1 2)
        ((hbracket 5 1 2 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 0 5 2)
        ((hbracket 0 5 2 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 0 1 5)
        ((hbracket 0 1 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 0 3 4)
        ((hbracket 0 3 4 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 0 3 5)
        ((hbracket 0 3 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 0 4 5)
        ((hbracket 0 4 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 1 3 4)
        ((hbracket 1 3 4 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 1 3 5)
        ((hbracket 1 3 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 1 4 5)
        ((hbracket 1 4 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 2 3 4)
        ((hbracket 2 3 4 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 2 3 5)
        ((hbracket 2 3 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 2 4 5)
        ((hbracket 2 4 5 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern lineFreeFamily 3 4 5)
        ((hbracket 3 4 5 (by decide) (by decide) (by decide)).mp hzero))
  refine ⟨param, hadmissible, basisChange, fun label => scale (relabel label), hunit,
    fun label => hscaleNe (relabel label), fun label => ?_⟩
  have hstep := hrealize (relabel label)
  rwa [Equiv.symm_apply_apply] at hstep

/-- **THE `#1` STRATUM OBLIGATION FROM THE CHART.**  Tie-freeness of the
four-parameter `#1` chart at every admissible parameter gives the tree's
residual obligation for entry `#1`, the line-free cell. -/
theorem stressFreeStratumIsTieFree_lineFree_of_chart
    (hchart : ∀ param : ℝ × ℝ × ℝ × ℝ, IsAdmissibleLineFreeParameter param →
      DirectionChartIsTieFree (lineFreeDirection param)) :
    StressFreeStratumIsTieFree (lineFamilyPattern ([] : List (List (Fin 6)))) :=
  stressFreeStratumIsTieFree_of_parameterizedChart hchart
    parameterizedChartCovers_lineFreeDirection

/-- The pattern discharged above is entry `#1` of the tree's residual list. -/
theorem lineFreeFamily_mem_stressFreeResidualFamiliesSix :
    ([] : List (List (Fin 6))) ∈ stressFreeResidualFamiliesSix := by
  decide

/-! ## A first chart-level cell at entry `#1`

The chart makes the landed general covering cell instantiable here for the first
time.  The basis triple `{0,1,2}` is the chart's own standard frame, so it reads
every label: atom `3` at `(1,1,1)`, atom `4` at `(1, fourMid, fourLast)` and
atom `5` at `(1, fiveMid, fiveLast)`. -/

/-- The selected triple: the chart's own basis. -/
def lineFreeSelected : Finset (Fin 6) := {0, 1, 2}

/-- The combination coefficients of every label against the basis `{0,1,2}`. -/
def lineFreeCoeff (param : ℝ × ℝ × ℝ × ℝ) : Fin 6 → Fin 6 → ℝ
  | 0 => ![1, 0, 0, 0, 0, 0]
  | 1 => ![0, 1, 0, 0, 0, 0]
  | 2 => ![0, 0, 1, 0, 0, 0]
  | 3 => ![1, 1, 1, 0, 0, 0]
  | 4 => ![1, param.1, param.2.1, 0, 0, 0]
  | 5 => ![1, param.2.2.1, param.2.2.2, 0, 0, 0]

/-- The basis triple reads every label of the chart. -/
theorem readsThrough_lineFreeDirection (param : ℝ × ℝ × ℝ × ℝ) :
    ReadsThrough (lineFreeDirection param) lineFreeSelected (lineFreeCoeff param) := by
  intro label probe
  have hsum : lineFreeSelected = ({0, 1, 2} : Finset (Fin 6)) := rfl
  fin_cases label <;>
    simp [hsum, lineFreeDirection, lineFreeCoeff, dotProduct, Fin.sum_univ_three,
      Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, add_assoc]

/-- **The general covering cell at entry `#1`.**  If every label's cover cost
against the basis triple is at most one, the basis triple is strictly
dominating.  This is the first chart-level cell available at this entry, and it
exists only because the chart does. -/
theorem posDef_directionChartGap_lineFree_of_coverCell (param : ℝ × ℝ × ℝ × ℝ)
    (mass weight : Fin 6 → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label) (hsum : ∑ label, weight label = 1)
    (hspan : ∀ probe : Fin 3 → ℝ,
      (∀ label, lineFreeDirection param label ⬝ᵥ probe = 0) → probe = 0)
    (hcell : GeneralCoverCellFires (fun label => mass label / weight label)
      lineFreeSelected (lineFreeCoeff param)) :
    (directionChartGap (lineFreeDirection param) mass weight lineFreeSelected).PosDef :=
  posDef_directionChartGap_of_generalCoverCell (lineFreeDirection param) mass weight
    hmass hweight hsum hspan (by decide) (lineFreeCoeff param)
    (readsThrough_lineFreeDirection param) hcell

end Gtz
