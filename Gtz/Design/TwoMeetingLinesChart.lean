/-
# The two-meeting-lines chart: entry `#3`, moduli dimension two

Entry `#3` of `Gtz.stressFreeResidualFamiliesSix` is `[[0,1,2],[0,3,4]]` — two
three-point lines meeting at the shared atom `0`.  Its realization space is TWO
parameters wide, and this file builds the chart and proves the covering half.

## Why two parameters

The four atoms `0, 1, 3, 5` are in general position: `0` and `1` span the first
line, `0` and `3` the second, and `5` lies on neither.  `PGL(3)` is simply
transitive on such a frame, so normalize

  `0 -> (1,0,0)`,  `1 -> (0,1,0)`,  `3 -> (0,0,1)`,  `5 -> (1,1,1)`.

The first line is then the plane `z = 0` and the second the plane `y = 0`.  Atom
`2` sits on the first line and atom `4` on the second, so

  `2 -> (1, p, 0)`,  `4 -> (1, 0, q)`,

and the pair `(p, q)` is the whole remaining freedom.  That is the moduli count
`4 - k` at `k = 2` lines.

## The admissible region, and what each exclusion is

The twenty triple brackets of the chart are, in the order `012 013 014 015 023
024 025 034 035 045 123 124 125 134 135 145 234 235 245 345`,

  `0, 1, q, 1, p, pq, p, 0, -1, -q, -1, -q, -1, 1, 1, q-1, p, p-1, pq-p-q, 1`.

So the vanishing set is exactly the two lines precisely when

  `p != 0`, `q != 0`, `p != 1`, `q != 1`, `pq - p - q != 0`.

Each exclusion is a degeneration OFF this stratum, never a gap in it:

* `p = 0` sends atom `2` onto atom `0`, and `q = 0` sends atom `4` onto atom `0`
  — a parallel pair, forbidden by primitivity.
* `p = 1` makes `{2,3,5}` collinear and `q = 1` makes `{1,4,5}` collinear — a
  THIRD line, so a different pattern, forbidden because `Gtz.HasLinePattern` is
  an iff.
* `pq = p + q` makes `{2,4,5}` collinear.  That locus is exactly the interface
  with entry `#4`, the three-line stratum.

All five exclusions are PROVED below rather than assumed: they come out of the
covering as `Gtz.IsAdmissibleTwoMeetingLinesParameter`.

## The covering

`Gtz.exists_twoMeetingLinesCoordinates` reads seven expansion coefficients off
an arbitrary realization in the basis `{0,1,3}` — two for atom `2`, two for atom
`4`, three for atom `5` — and proves all seven nonzero, each from one triple the
pattern does NOT contain.  The parameters come out as

  `p = coefB * coefE / (coefA * coefF)`,   `q = coefD * coefE / (coefC * coefG)`,

and the basis change is the rescaled frame `coefE . v0`, `coefF . v1`,
`coefG . v3`, which carries atom `5` to `(1,1,1)` by construction.

## #MISSING — the twenty brackets are PROSE here, not lemmas

The bracket list at the top of this docstring is a comment.  No declaration in
the corpus evaluates `tripleBracket (twoMeetingLinesDirection param i) ...` to a
polynomial in `(p, q)`.  The only landed bracket fact at this chart is
`Gtz.tripleBracket_twoMeetingLinesDirection_eq_zero_iff`, which decides
VANISHING and nothing else.  Compare `Gtz.tripleBracket_threeLinesDirection_vertexTriple`,
`Gtz.tripleBracket_threeLinesDirection_freeTriple` and
`Gtz.tripleBracket_threeLinesDirection_oneTwoFive`
(Gtz/Design/ThreeLinesAtlas.lean:267, :274, :283), which give VALUES at the
one-parameter chart.  A two-parameter table is the first brick of this lane.

## #MISSING — the over-levered closure is not instantiated here

`Gtz.posDef_directionChartGap_of_leverageTrace`,
`Gtz.two_add_weight_lt_sum_leverage_of_overLevered_triple`,
`Gtz.three_le_card_overLevered`, `Gtz.weight_lt_chartMassLeverage_of_posDef_gap`
and `Gtz.sum_leverage_le_two_of_dependent`
(Gtz/Wave/ThreeLinesSlideElimination.lean) are DIRECTION-GENERIC.  The three-lines
chart instantiates them at `Gtz.exists_posDef_threeLines_of_overLevered_triple`
(:1409), whose only chart-specific input is
`Gtz.posDef_chartMassMoment_threeLines` (:864), itself one term.  The twin input
at this chart is landed: `Gtz.posDef_massMoment_twoMeetingLinesDirection`
(Gtz/Design/ChartProgrammeAssembly.lean:254), and `Gtz.chartMassMoment_eq` is
`rfl`.  The two-meeting-lines instantiation does not exist.
-/
import Gtz.Design.RigidityBridge

namespace Gtz

open Matrix

/-! ## The chart -/

/-- The entry `#3` directions: the frame `0, 1, 3, 5` normalized, with atom `2`
sliding along the first line and atom `4` along the second. -/
def twoMeetingLinesDirection (param : ℝ × ℝ) : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![1, param.1, 0]
  | 3 => ![0, 0, 1]
  | 4 => ![1, 0, param.2]
  | 5 => ![1, 1, 1]

theorem twoMeetingLinesDirection_zero (param : ℝ × ℝ) :
    twoMeetingLinesDirection param 0 = ![1, 0, 0] := rfl
theorem twoMeetingLinesDirection_one (param : ℝ × ℝ) :
    twoMeetingLinesDirection param 1 = ![0, 1, 0] := rfl
theorem twoMeetingLinesDirection_two (param : ℝ × ℝ) :
    twoMeetingLinesDirection param 2 = ![1, param.1, 0] := rfl
theorem twoMeetingLinesDirection_three (param : ℝ × ℝ) :
    twoMeetingLinesDirection param 3 = ![0, 0, 1] := rfl
theorem twoMeetingLinesDirection_four (param : ℝ × ℝ) :
    twoMeetingLinesDirection param 4 = ![1, 0, param.2] := rfl
theorem twoMeetingLinesDirection_five (param : ℝ × ℝ) :
    twoMeetingLinesDirection param 5 = ![1, 1, 1] := rfl

/-- The five forbidden loci: two parallel pairs, two third lines through atom
`5`, and the three-line interface `pq = p + q`. -/
def IsAdmissibleTwoMeetingLinesParameter (param : ℝ × ℝ) : Prop :=
  param.1 ≠ 0 ∧ param.2 ≠ 0 ∧ param.1 ≠ 1 ∧ param.2 ≠ 1 ∧
    param.1 * param.2 - param.1 - param.2 ≠ 0

/-- The two-line family of entry `#3`. -/
def twoMeetingLinesFamily : List (List (Fin 6)) := [[0, 1, 2], [0, 3, 4]]

set_option maxHeartbeats 1000000 in
/-- **The `#3` chart is on the right stratum**, at every admissible parameter:
the dependent triples are exactly the two listed lines. -/
theorem tripleBracket_twoMeetingLinesDirection_eq_zero_iff (param : ℝ × ℝ)
    (hadmissible : IsAdmissibleTwoMeetingLinesParameter param)
    (leftLabel midLabel rightLabel : Fin 6)
    (hleftMid : leftLabel ≠ midLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hmidRight : midLabel ≠ rightLabel) :
    tripleBracket (twoMeetingLinesDirection param leftLabel)
        (twoMeetingLinesDirection param midLabel)
        (twoMeetingLinesDirection param rightLabel) = 0
      ↔ lineFamilyPattern twoMeetingLinesFamily leftLabel midLabel rightLabel := by
  obtain ⟨hfirstNe, hsecondNe, hfirstNeOne, hsecondNeOne, hinterfaceNe⟩ := hadmissible
  rcases fin_six_cases leftLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin_six_cases midLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin_six_cases rightLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hleftMid
          | exact absurd rfl hleftRight
          | exact absurd rfl hmidRight
          | (simp [twoMeetingLinesDirection, tripleBracket_eq, lineFamilyPattern,
              twoMeetingLinesFamily, hfirstNe, hsecondNe, hfirstNeOne, hsecondNeOne,
              sub_eq_zero] <;>
              try (intro hcontra
                   first
                     | exact hfirstNe (by linarith)
                     | exact hsecondNe (by linarith)
                     | exact hfirstNeOne (by linarith)
                     | exact hsecondNeOne (by linarith)
                     | exact hinterfaceNe (by linarith)))

/-! ## Coordinates of an arbitrary realization -/

/-- The three-term Cramer expansion in a bracket basis, cleared of denominators.
An arbitrary vector is the bracket-weighted combination of a basis triple. -/
theorem smul_eq_three_term_expansion (baseFirst baseMid baseLast probe : Fin 3 → ℝ) :
    tripleBracket baseFirst baseMid baseLast • probe
      = tripleBracket probe baseMid baseLast • baseFirst
        + tripleBracket baseFirst probe baseLast • baseMid
        + tripleBracket baseFirst baseMid probe • baseLast := by
  funext row
  fin_cases row <;> simp [tripleBracket_eq] <;> ring

/-- The atom `5` expansion of an arbitrary configuration in the basis `{0,1,3}`,
with the three coefficients named as brackets. -/
theorem smul_five_expansion (vec : Fin 6 → (Fin 3 → ℝ)) :
    tripleBracket (vec 0) (vec 1) (vec 3) • vec 5
      = tripleBracket (vec 5) (vec 1) (vec 3) • vec 0
        + tripleBracket (vec 0) (vec 5) (vec 3) • vec 1
        + tripleBracket (vec 0) (vec 1) (vec 5) • vec 3 :=
  smul_eq_three_term_expansion (vec 0) (vec 1) (vec 3) (vec 5)

/-- The atom `2` expansion: it lies on the first line, so its `vec 3` coefficient
vanishes and the three-term Cramer expansion collapses to two terms. -/
theorem smul_two_expansion (vec : Fin 6 → (Fin 3 → ℝ))
    (hlineFirst : tripleBracket (vec 0) (vec 1) (vec 2) = 0) :
    tripleBracket (vec 0) (vec 1) (vec 3) • vec 2
      = tripleBracket (vec 2) (vec 1) (vec 3) • vec 0
        + tripleBracket (vec 0) (vec 2) (vec 3) • vec 1 := by
  have hfull := smul_eq_three_term_expansion (vec 0) (vec 1) (vec 3) (vec 2)
  rw [hlineFirst, zero_smul, add_zero] at hfull
  exact hfull

/-- The atom `4` expansion: it lies on the second line, so its `vec 1`
coefficient vanishes. -/
theorem smul_four_expansion (vec : Fin 6 → (Fin 3 → ℝ))
    (hlineSecond : tripleBracket (vec 0) (vec 3) (vec 4) = 0) :
    tripleBracket (vec 0) (vec 1) (vec 3) • vec 4
      = tripleBracket (vec 4) (vec 1) (vec 3) • vec 0
        + tripleBracket (vec 0) (vec 1) (vec 4) • vec 3 := by
  have hmidZero : tripleBracket (vec 0) (vec 4) (vec 3) = 0 := by
    rw [tripleBracket_swapRight, hlineSecond, neg_zero]
  have hfull := smul_eq_three_term_expansion (vec 0) (vec 1) (vec 3) (vec 4)
  rw [hmidZero, zero_smul, add_zero] at hfull
  exact hfull

/-- **The coordinates of a two-meeting-lines configuration.**  In the basis
`{0,1,3}` the three off-basis atoms carry seven expansion coefficients, each of
them a bracket the pattern forbids to vanish.  Atom `2` uses two of them, atom
`4` two more, and the free atom `5` the remaining three. -/
theorem exists_twoMeetingLinesCoordinates (vec : Fin 6 → (Fin 3 → ℝ))
    (hbasisNe : tripleBracket (vec 0) (vec 1) (vec 3) ≠ 0)
    (hcoefANe : tripleBracket (vec 2) (vec 1) (vec 3) ≠ 0)
    (hcoefBNe : tripleBracket (vec 0) (vec 2) (vec 3) ≠ 0)
    (hcoefCNe : tripleBracket (vec 4) (vec 1) (vec 3) ≠ 0)
    (hcoefDNe : tripleBracket (vec 0) (vec 1) (vec 4) ≠ 0)
    (hcoefENe : tripleBracket (vec 5) (vec 1) (vec 3) ≠ 0)
    (hcoefFNe : tripleBracket (vec 0) (vec 5) (vec 3) ≠ 0)
    (hcoefGNe : tripleBracket (vec 0) (vec 1) (vec 5) ≠ 0)
    (hlineFirst : tripleBracket (vec 0) (vec 1) (vec 2) = 0)
    (hlineSecond : tripleBracket (vec 0) (vec 3) (vec 4) = 0) :
    ∃ bigDelta coefA coefB coefC coefD coefE coefF coefG : ℝ,
      bigDelta ≠ 0 ∧ coefA ≠ 0 ∧ coefB ≠ 0 ∧ coefC ≠ 0 ∧ coefD ≠ 0 ∧
        coefE ≠ 0 ∧ coefF ≠ 0 ∧ coefG ≠ 0 ∧
        bigDelta • vec 2 = coefA • vec 0 + coefB • vec 1 ∧
        bigDelta • vec 4 = coefC • vec 0 + coefD • vec 3 ∧
        bigDelta • vec 5 = coefE • vec 0 + coefF • vec 1 + coefG • vec 3 :=
  ⟨_, _, _, _, _, _, _, _, hbasisNe, hcoefANe, hcoefBNe, hcoefCNe, hcoefDNe,
    hcoefENe, hcoefFNe, hcoefGNe, smul_two_expansion vec hlineFirst,
    smul_four_expansion vec hlineSecond, smul_five_expansion vec⟩

end Gtz
