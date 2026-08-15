/-
# The line-free chart: entry `#1`, moduli dimension four

Entry `#1` of `Gtz.stressFreeResidualFamiliesSix` is `[]` — no three-point line
at all, the widest stratum of the five and the last one the campaign charts.
Its realization space is FOUR parameters wide and this file constructs it.

## Why four parameters

With no line relation the four atoms `0, 1, 2, 3` are in general position on
their own, so `PGL(3)` is simply transitive on them and normalizes

  `0 -> (1,0,0)`,  `1 -> (0,1,0)`,  `2 -> (0,0,1)`,  `3 -> (1,1,1)`.

The two remaining atoms are free, two parameters each:

  `4 -> (1, fourMid, fourLast)`,  `5 -> (1, fiveMid, fiveLast)`.

That is the moduli count `4 - k` at `k = 0` lines, and it is the largest cell of
the stratification.

## The admissible region, and what each exclusion is

The twenty triple brackets of the chart are, in the order `012 013 014 015 023
024 025 034 035 045 123 124 125 134 135 145 234 235 245 345`,

  `1, 1, b, d, -1, -a, -c, b-a, d-c, ad-bc, 1, 1, 1, 1-b, 1-d, b-d, a-1, c-1,
   c-a, (ad-bc) - (d-b) + (c-a)`,

writing `a` for `fourMid`, `b` for `fourLast`, `c` for `fiveMid` and `d` for
`fiveLast`.  SIX of the twenty are constant and never vanish, so line-freeness
is exactly FOURTEEN conditions, and each is a degeneration OFF this stratum:

* `a = 0`, `b = 0`, `c = 0`, `d = 0` each put a free atom on one of the three
  coordinate lines through two frame atoms — a first line, so a different
  matroid.
* `a = 1`, `b = 1`, `c = 1`, `d = 1` each make a free atom collinear with atom
  `3` and one frame atom.
* `b = a` and `d = c` put atom `4` or atom `5` on the join of atoms `0` and `3`.
* `b = d` and `c = a` put atoms `4` and `5` together with atom `1` or atom `2`.
* `ad = bc` puts atoms `0`, `4` and `5` on a line.
* `(ad-bc) - (d-b) + (c-a) = 0` puts atoms `3`, `4` and `5` on a line, the last
  triple of the twenty.

Every one of the twenty brackets is used, because line-freeness forbids all
twenty to vanish.  All fourteen exclusions are PROVED in `Gtz.LineFreeCovering`
rather than assumed, as `Gtz.IsAdmissibleLineFreeParameter`.

## Coordinates

`Gtz.exists_lineFreeCoordinates` reads NINE expansion coefficients off an
arbitrary realization in the basis `{0,1,2}` — three for each of the three
off-basis atoms, since no atom lies on a line and every expansion keeps all
three Cramer terms.
-/
import Gtz.Design.RigidityBridge

namespace Gtz

open Matrix

/-! ## The chart -/

/-- The entry `#1` directions: the frame `0, 1, 2, 3` normalized, with atoms `4`
and `5` free in two directions each. -/
def lineFreeDirection (param : ℝ × ℝ × ℝ × ℝ) : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![0, 0, 1]
  | 3 => ![1, 1, 1]
  | 4 => ![1, param.1, param.2.1]
  | 5 => ![1, param.2.2.1, param.2.2.2]

theorem lineFreeDirection_zero (param : ℝ × ℝ × ℝ × ℝ) :
    lineFreeDirection param 0 = ![1, 0, 0] := rfl
theorem lineFreeDirection_one (param : ℝ × ℝ × ℝ × ℝ) :
    lineFreeDirection param 1 = ![0, 1, 0] := rfl
theorem lineFreeDirection_two (param : ℝ × ℝ × ℝ × ℝ) :
    lineFreeDirection param 2 = ![0, 0, 1] := rfl
theorem lineFreeDirection_three (param : ℝ × ℝ × ℝ × ℝ) :
    lineFreeDirection param 3 = ![1, 1, 1] := rfl
theorem lineFreeDirection_four (param : ℝ × ℝ × ℝ × ℝ) :
    lineFreeDirection param 4 = ![1, param.1, param.2.1] := rfl
theorem lineFreeDirection_five (param : ℝ × ℝ × ℝ × ℝ) :
    lineFreeDirection param 5 = ![1, param.2.2.1, param.2.2.2] := rfl

/-- The fourteen forbidden loci: eight coordinate and frame incidences, four
pair coincidences, and the two determinant conditions `ad = bc` and
`(ad-bc) - (d-b) + (c-a) = 0`. -/
def IsAdmissibleLineFreeParameter (param : ℝ × ℝ × ℝ × ℝ) : Prop :=
  param.1 ≠ 0 ∧ param.1 ≠ 1 ∧
    param.2.1 ≠ 0 ∧ param.2.1 ≠ 1 ∧
      param.2.2.1 ≠ 0 ∧ param.2.2.1 ≠ 1 ∧
        param.2.2.2 ≠ 0 ∧ param.2.2.2 ≠ 1 ∧
          param.2.1 - param.1 ≠ 0 ∧ param.2.2.2 - param.2.2.1 ≠ 0 ∧
            param.2.1 - param.2.2.2 ≠ 0 ∧ param.2.2.1 - param.1 ≠ 0 ∧
              param.1 * param.2.2.2 - param.2.1 * param.2.2.1 ≠ 0 ∧
                param.1 * param.2.2.2 - param.2.1 * param.2.2.1
                  - param.2.2.2 + param.2.1 + param.2.2.1 - param.1 ≠ 0

/-- The line-free family of entry `#1`: no lines at all. -/
def lineFreeFamily : List (List (Fin 6)) := []

set_option maxHeartbeats 2000000 in
/-- **The `#1` chart is on the right stratum**, at every admissible parameter:
no triple is dependent.  The empty family makes the right side of the
equivalence identically false, so this says all twenty brackets are nonzero. -/
theorem tripleBracket_lineFreeDirection_eq_zero_iff (param : ℝ × ℝ × ℝ × ℝ)
    (hadmissible : IsAdmissibleLineFreeParameter param)
    (leftLabel midLabel rightLabel : Fin 6)
    (hleftMid : leftLabel ≠ midLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hmidRight : midLabel ≠ rightLabel) :
    tripleBracket (lineFreeDirection param leftLabel)
        (lineFreeDirection param midLabel)
        (lineFreeDirection param rightLabel) = 0
      ↔ lineFamilyPattern lineFreeFamily leftLabel midLabel rightLabel := by
  obtain ⟨hfourMidNe, hfourMidNeOne, hfourLastNe, hfourLastNeOne,
    hfiveMidNe, hfiveMidNeOne, hfiveLastNe, hfiveLastNeOne,
    hfourDiffNe, hfiveDiffNe, hlastDiffNe, hmidDiffNe,
    hminorNe, hcubicNe⟩ := hadmissible
  rcases fin_six_cases leftLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin_six_cases midLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin_six_cases rightLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hleftMid
          | exact absurd rfl hleftRight
          | exact absurd rfl hmidRight
          | (simp only [lineFreeDirection, tripleBracket_eq, lineFamilyPattern,
              lineFreeFamily, List.not_mem_nil, false_and, exists_false,
              iff_false, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
             intro hcontra
             first
               | exact hfourMidNe (by linarith)
               | exact hfourMidNeOne (by linarith)
               | exact hfourLastNe (by linarith)
               | exact hfourLastNeOne (by linarith)
               | exact hfiveMidNe (by linarith)
               | exact hfiveMidNeOne (by linarith)
               | exact hfiveLastNe (by linarith)
               | exact hfiveLastNeOne (by linarith)
               | exact hfourDiffNe (by linarith)
               | exact hfiveDiffNe (by linarith)
               | exact hlastDiffNe (by linarith)
               | exact hmidDiffNe (by linarith)
               | exact hminorNe (by linarith)
               | exact hcubicNe (by linarith))

/-! ## Coordinates of an arbitrary realization -/

/-- The atom `3` expansion in the basis `{0,1,2}`: free, so all three Cramer
coefficients survive. -/
theorem smul_lineFree_three_expansion (vec : Fin 6 → (Fin 3 → ℝ)) :
    tripleBracket (vec 0) (vec 1) (vec 2) • vec 3
      = tripleBracket (vec 3) (vec 1) (vec 2) • vec 0
        + tripleBracket (vec 0) (vec 3) (vec 2) • vec 1
        + tripleBracket (vec 0) (vec 1) (vec 3) • vec 2 :=
  tripleBracket_smul_eq_cramer (vec 0) (vec 1) (vec 2) (vec 3)

/-- The atom `4` expansion in the basis `{0,1,2}`. -/
theorem smul_lineFree_four_expansion (vec : Fin 6 → (Fin 3 → ℝ)) :
    tripleBracket (vec 0) (vec 1) (vec 2) • vec 4
      = tripleBracket (vec 4) (vec 1) (vec 2) • vec 0
        + tripleBracket (vec 0) (vec 4) (vec 2) • vec 1
        + tripleBracket (vec 0) (vec 1) (vec 4) • vec 2 :=
  tripleBracket_smul_eq_cramer (vec 0) (vec 1) (vec 2) (vec 4)

/-- The atom `5` expansion in the basis `{0,1,2}`. -/
theorem smul_lineFree_five_expansion (vec : Fin 6 → (Fin 3 → ℝ)) :
    tripleBracket (vec 0) (vec 1) (vec 2) • vec 5
      = tripleBracket (vec 5) (vec 1) (vec 2) • vec 0
        + tripleBracket (vec 0) (vec 5) (vec 2) • vec 1
        + tripleBracket (vec 0) (vec 1) (vec 5) • vec 2 :=
  tripleBracket_smul_eq_cramer (vec 0) (vec 1) (vec 2) (vec 5)

/-- **The coordinates of a line-free configuration.**  In the basis `{0,1,2}`
the three off-basis atoms carry nine expansion coefficients, each of them a
bracket the empty pattern forbids to vanish.  No atom lies on a line, so every
expansion keeps all three terms — the feature that separates this cell from the
four charted before it. -/
theorem exists_lineFreeCoordinates (vec : Fin 6 → (Fin 3 → ℝ))
    (hbasisNe : tripleBracket (vec 0) (vec 1) (vec 2) ≠ 0)
    (hcoefANe : tripleBracket (vec 3) (vec 1) (vec 2) ≠ 0)
    (hcoefBNe : tripleBracket (vec 0) (vec 3) (vec 2) ≠ 0)
    (hcoefCNe : tripleBracket (vec 0) (vec 1) (vec 3) ≠ 0)
    (hcoefDNe : tripleBracket (vec 4) (vec 1) (vec 2) ≠ 0)
    (hcoefENe : tripleBracket (vec 0) (vec 4) (vec 2) ≠ 0)
    (hcoefFNe : tripleBracket (vec 0) (vec 1) (vec 4) ≠ 0)
    (hcoefGNe : tripleBracket (vec 5) (vec 1) (vec 2) ≠ 0)
    (hcoefHNe : tripleBracket (vec 0) (vec 5) (vec 2) ≠ 0)
    (hcoefKNe : tripleBracket (vec 0) (vec 1) (vec 5) ≠ 0) :
    ∃ bigDelta coefA coefB coefC coefD coefE coefF coefG coefH coefK : ℝ,
      bigDelta ≠ 0 ∧ coefA ≠ 0 ∧ coefB ≠ 0 ∧ coefC ≠ 0 ∧ coefD ≠ 0 ∧
        coefE ≠ 0 ∧ coefF ≠ 0 ∧ coefG ≠ 0 ∧ coefH ≠ 0 ∧ coefK ≠ 0 ∧
          bigDelta • vec 3 = coefA • vec 0 + coefB • vec 1 + coefC • vec 2 ∧
            bigDelta • vec 4 = coefD • vec 0 + coefE • vec 1 + coefF • vec 2 ∧
              bigDelta • vec 5 = coefG • vec 0 + coefH • vec 1 + coefK • vec 2 :=
  ⟨_, _, _, _, _, _, _, _, _, _, hbasisNe, hcoefANe, hcoefBNe, hcoefCNe, hcoefDNe,
    hcoefENe, hcoefFNe, hcoefGNe, hcoefHNe, hcoefKNe,
    smul_lineFree_three_expansion vec, smul_lineFree_four_expansion vec,
    smul_lineFree_five_expansion vec⟩

end Gtz
