/-
# The one-line chart: entry `#2`, moduli dimension three

Entry `#2` of `Gtz.stressFreeResidualFamiliesSix` is `[[0,1,2]]` — a single
three-point line, with the three remaining atoms free.  Its realization space is
THREE parameters wide, the widest chart the campaign has built, and this file
constructs it.

## Why three parameters

The four atoms `0, 1, 3, 4` are in general position: `0` and `1` span the line,
and `3` and `4` lie off it and off each other's join with the line.  `PGL(3)` is
simply transitive on such a frame, so normalize

  `0 -> (1,0,0)`,  `1 -> (0,1,0)`,  `3 -> (0,0,1)`,  `4 -> (1,1,1)`.

The line is then the plane `z = 0`.  Atom `2` sits on it and atom `5` is free,
so

  `2 -> (1, slide, 0)`,  `5 -> (1, freeMid, freeLast)`,

and the triple `(slide, freeMid, freeLast)` is the whole remaining freedom.
That is the moduli count `4 - k` at `k = 1` line.

## The admissible region, and what each exclusion is

The twenty triple brackets of the chart are, in the order `012 013 014 015 023
024 025 034 035 045 123 124 125 134 135 145 234 235 245 345`,

  `0, 1, 1, w, s, s, s w, -1, -m, w-m, -1, -1, -w, 1, 1, 1-w, s-1, s-m,
   s + w - m - s w, m-1`,

writing `s` for `slide`, `m` for `freeMid` and `w` for `freeLast`.  So the
vanishing set is exactly the one listed line precisely when NINE conditions
hold, and each is a degeneration OFF this stratum rather than a gap in it:

* `s = 0` sends atom `2` onto atom `0`, a parallel pair.
* `w = 0` puts atom `5` on the plane `z = 0`, joining the line and making it a
  FOUR-point line, a different matroid.
* `m = 0`, `m = 1`, `w = 1`, `s = 1`, `w = m` and `s = m` each make one further
  triple collinear — a SECOND line, so a different pattern, forbidden because
  `Gtz.HasLinePattern` is an iff.
* `s + w = m + s w` makes `{2,4,5}` collinear.  That locus is the interface with
  entry `#3`, the two-meeting-lines stratum.

All nine exclusions are PROVED in `Gtz.OneLineCovering` rather than assumed:
they come out of the covering as `Gtz.IsAdmissibleOneLineParameter`.

## Coordinates

`Gtz.exists_oneLineCoordinates` reads NINE expansion coefficients off an
arbitrary realization in the basis `{0,1,3}` — two for atom `2`, which lies on
the line, and three each for the free atoms `4` and `5` — and proves all nine
nonzero, each from one triple the pattern does NOT contain.
-/
import Gtz.Design.RigidityBridge

namespace Gtz

open Matrix

/-! ## The chart -/

/-- The entry `#2` directions: the frame `0, 1, 3, 4` normalized, with atom `2`
sliding along the line and atom `5` free in two directions. -/
def oneLineDirection (param : ℝ × ℝ × ℝ) : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![1, param.1, 0]
  | 3 => ![0, 0, 1]
  | 4 => ![1, 1, 1]
  | 5 => ![1, param.2.1, param.2.2]

theorem oneLineDirection_zero (param : ℝ × ℝ × ℝ) :
    oneLineDirection param 0 = ![1, 0, 0] := rfl
theorem oneLineDirection_one (param : ℝ × ℝ × ℝ) :
    oneLineDirection param 1 = ![0, 1, 0] := rfl
theorem oneLineDirection_two (param : ℝ × ℝ × ℝ) :
    oneLineDirection param 2 = ![1, param.1, 0] := rfl
theorem oneLineDirection_three (param : ℝ × ℝ × ℝ) :
    oneLineDirection param 3 = ![0, 0, 1] := rfl
theorem oneLineDirection_four (param : ℝ × ℝ × ℝ) :
    oneLineDirection param 4 = ![1, 1, 1] := rfl
theorem oneLineDirection_five (param : ℝ × ℝ × ℝ) :
    oneLineDirection param 5 = ![1, param.2.1, param.2.2] := rfl

/-- The nine forbidden loci: one parallel pair, one four-point line, six second
lines, and the two-meeting-lines interface `s + w = m + s w`. -/
def IsAdmissibleOneLineParameter (param : ℝ × ℝ × ℝ) : Prop :=
  param.1 ≠ 0 ∧ param.1 ≠ 1 ∧
    param.2.1 ≠ 0 ∧ param.2.1 ≠ 1 ∧
      param.2.2 ≠ 0 ∧ param.2.2 ≠ 1 ∧
        param.2.2 - param.2.1 ≠ 0 ∧ param.1 - param.2.1 ≠ 0 ∧
          param.1 + param.2.2 - param.2.1 - param.1 * param.2.2 ≠ 0

/-- The one-line family of entry `#2`. -/
def oneLineFamily : List (List (Fin 6)) := [[0, 1, 2]]

set_option maxHeartbeats 1000000 in
/-- **The `#2` chart is on the right stratum**, at every admissible parameter:
the dependent triples are exactly the single listed line. -/
theorem tripleBracket_oneLineDirection_eq_zero_iff (param : ℝ × ℝ × ℝ)
    (hadmissible : IsAdmissibleOneLineParameter param)
    (leftLabel midLabel rightLabel : Fin 6)
    (hleftMid : leftLabel ≠ midLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hmidRight : midLabel ≠ rightLabel) :
    tripleBracket (oneLineDirection param leftLabel)
        (oneLineDirection param midLabel)
        (oneLineDirection param rightLabel) = 0
      ↔ lineFamilyPattern oneLineFamily leftLabel midLabel rightLabel := by
  obtain ⟨hslideNe, hslideNeOne, hmidNe, hmidNeOne, hlastNe, hlastNeOne,
    hlastMidNe, hslideMidNe, hinterfaceNe⟩ := hadmissible
  rcases fin_six_cases leftLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin_six_cases midLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin_six_cases rightLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hleftMid
          | exact absurd rfl hleftRight
          | exact absurd rfl hmidRight
          | (simp [oneLineDirection, tripleBracket_eq, lineFamilyPattern,
              oneLineFamily, hslideNe, hmidNe, hlastNe, sub_eq_zero] <;>
              try (intro hcontra
                   first
                     | exact hslideNe (by linarith)
                     | exact hslideNeOne (by linarith)
                     | exact hmidNe (by linarith)
                     | exact hmidNeOne (by linarith)
                     | exact hlastNe (by linarith)
                     | exact hlastNeOne (by linarith)
                     | exact hlastMidNe (by linarith)
                     | exact hslideMidNe (by linarith)
                     | exact hinterfaceNe (by linarith)))

/-! ## Coordinates of an arbitrary realization -/

/-- The atom `2` expansion: it lies on the line, so its `vec 3` coefficient
vanishes and the Cramer expansion collapses to two terms. -/
theorem smul_oneLine_two_expansion (vec : Fin 6 → (Fin 3 → ℝ))
    (hline : tripleBracket (vec 0) (vec 1) (vec 2) = 0) :
    tripleBracket (vec 0) (vec 1) (vec 3) • vec 2
      = tripleBracket (vec 2) (vec 1) (vec 3) • vec 0
        + tripleBracket (vec 0) (vec 2) (vec 3) • vec 1 :=
  smul_eq_two_term_expansion (vec 0) (vec 1) (vec 3) (vec 2) hline

/-- The atom `4` expansion: free, so all three Cramer coefficients survive. -/
theorem smul_oneLine_four_expansion (vec : Fin 6 → (Fin 3 → ℝ)) :
    tripleBracket (vec 0) (vec 1) (vec 3) • vec 4
      = tripleBracket (vec 4) (vec 1) (vec 3) • vec 0
        + tripleBracket (vec 0) (vec 4) (vec 3) • vec 1
        + tripleBracket (vec 0) (vec 1) (vec 4) • vec 3 :=
  tripleBracket_smul_eq_cramer (vec 0) (vec 1) (vec 3) (vec 4)

/-- The atom `5` expansion: free, so all three Cramer coefficients survive. -/
theorem smul_oneLine_five_expansion (vec : Fin 6 → (Fin 3 → ℝ)) :
    tripleBracket (vec 0) (vec 1) (vec 3) • vec 5
      = tripleBracket (vec 5) (vec 1) (vec 3) • vec 0
        + tripleBracket (vec 0) (vec 5) (vec 3) • vec 1
        + tripleBracket (vec 0) (vec 1) (vec 5) • vec 3 :=
  tripleBracket_smul_eq_cramer (vec 0) (vec 1) (vec 3) (vec 5)

/-- **The coordinates of a one-line configuration.**  In the basis `{0,1,3}` the
three off-basis atoms carry nine expansion coefficients, each of them a bracket
the pattern forbids to vanish.  Atom `2` uses two of them, and the free atoms
`4` and `5` three each. -/
theorem exists_oneLineCoordinates (vec : Fin 6 → (Fin 3 → ℝ))
    (hbasisNe : tripleBracket (vec 0) (vec 1) (vec 3) ≠ 0)
    (hcoefANe : tripleBracket (vec 2) (vec 1) (vec 3) ≠ 0)
    (hcoefBNe : tripleBracket (vec 0) (vec 2) (vec 3) ≠ 0)
    (hcoefCNe : tripleBracket (vec 4) (vec 1) (vec 3) ≠ 0)
    (hcoefDNe : tripleBracket (vec 0) (vec 4) (vec 3) ≠ 0)
    (hcoefENe : tripleBracket (vec 0) (vec 1) (vec 4) ≠ 0)
    (hcoefFNe : tripleBracket (vec 5) (vec 1) (vec 3) ≠ 0)
    (hcoefGNe : tripleBracket (vec 0) (vec 5) (vec 3) ≠ 0)
    (hcoefHNe : tripleBracket (vec 0) (vec 1) (vec 5) ≠ 0)
    (hline : tripleBracket (vec 0) (vec 1) (vec 2) = 0) :
    ∃ bigDelta coefA coefB coefC coefD coefE coefF coefG coefH : ℝ,
      bigDelta ≠ 0 ∧ coefA ≠ 0 ∧ coefB ≠ 0 ∧ coefC ≠ 0 ∧ coefD ≠ 0 ∧
        coefE ≠ 0 ∧ coefF ≠ 0 ∧ coefG ≠ 0 ∧ coefH ≠ 0 ∧
          bigDelta • vec 2 = coefA • vec 0 + coefB • vec 1 ∧
            bigDelta • vec 4 = coefC • vec 0 + coefD • vec 1 + coefE • vec 3 ∧
              bigDelta • vec 5 = coefF • vec 0 + coefG • vec 1 + coefH • vec 3 :=
  ⟨_, _, _, _, _, _, _, _, _, hbasisNe, hcoefANe, hcoefBNe, hcoefCNe, hcoefDNe,
    hcoefENe, hcoefFNe, hcoefGNe, hcoefHNe, smul_oneLine_two_expansion vec hline,
    smul_oneLine_four_expansion vec, smul_oneLine_five_expansion vec⟩

end Gtz
