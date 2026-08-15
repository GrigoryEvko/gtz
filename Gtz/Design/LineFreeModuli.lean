/-
# The line-free moduli are exact, and they are honest

`Gtz.lineFreeDirection` charts entry `#1` of `Gtz.stressFreeResidualFamiliesSix`
at four parameters, and `Gtz.parameterizedChartCovers_lineFreeDirection` proves
that the chart catches every realization.  Two questions stay open after that,
and this file answers both.

## Is the admissible region exactly the cell?

`Gtz.tripleBracket_lineFreeDirection_eq_zero_iff` runs one way: an admissible
parameter gives a line-free configuration.  The converse is not automatic, and
without it the chart could cover the cell while excluding part of it.  The
converse is `Gtz.isAdmissibleLineFreeParameter_of_brackets`, and it comes from
the fourteen WALLS: each forbidden locus is named by the ONE triple of the
twenty that dies on it.

  `a = 0` kills `[024]`,   `b = 0` kills `[014]`,
  `c = 0` kills `[025]`,   `d = 0` kills `[015]`,
  `a = 1` kills `[234]`,   `b = 1` kills `[134]`,
  `c = 1` kills `[235]`,   `d = 1` kills `[135]`,
  `b = a` kills `[034]`,   `d = c` kills `[035]`,
  `b = d` kills `[145]`,   `c = a` kills `[245]`,
  `ad = bc` kills `[045]`, and the cubic kills `[345]`.

Each wall kills exactly one triple, so each is a codimension-one face and the
generic point of each face carries exactly ONE line.  The whole boundary of the
line-free cell in this chart is the ONE-LINE cell, entry `#2`.

## Are the four parameters honest?

They are, and the reason is that each of them is a RATIO OF TWO BRACKET
PRODUCTS WITH THE SAME LABEL MULTISET.  Under a frame change and a per-atom
scaling every bracket picks up the three scales of its labels and one
determinant, so a balanced ratio picks up nothing at all.
`Gtz.bracketRatio_invariant_of_balanced` proves this for any balanced ratio, and
the four parameters are four instances:

  `a = [042][312] / ([412][032])`,   `b = [014][312] / ([412][013])`,
  `c = [052][312] / ([512][032])`,   `d = [015][312] / ([512][013])`.

The chart evaluates all ten of these brackets to `1, 1, 1, 1, a, b, 1, c, d` and
`1`, so each ratio returns its own parameter.  Two chart points related by a
frame change and a per-atom scaling therefore carry the same parameter:
`Gtz.lineFreeDirection_param_injective`.  The four moduli carry no redundancy,
and the cell is four-dimensional on the nose.
-/
import Gtz.Design.LineFreeCovering

namespace Gtz

open Matrix

/-! ## The chart spans, with no hypothesis -/

/-- The chart carries the three coordinate directions, so nothing is orthogonal
to all six atoms.  Every consumer that demands a spanning hypothesis at entry
`#1` gets it free. -/
theorem lineFreeDirection_span (param : ℝ × ℝ × ℝ × ℝ) (probe : Fin 3 → ℝ)
    (hprobe : ∀ label, lineFreeDirection param label ⬝ᵥ probe = 0) : probe = 0 := by
  have hzero := hprobe 0
  have hone := hprobe 1
  have htwo := hprobe 2
  simp only [lineFreeDirection, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    one_mul, zero_mul, add_zero, zero_add] at hzero hone htwo
  funext index
  fin_cases index
  · exact hzero
  · exact hone
  · exact htwo

/-! ## The ten frame brackets of the chart -/

/-- The chart normalizes the frame so hard that nine of the ten expansion
brackets are `1` or a bare parameter.  `[312] = [032] = [013] = [412] = [512]
= [012] = 1`, `[042] = a`, `[014] = b`, `[052] = c`, `[015] = d`. -/
theorem lineFreeChartCoefficients (param : ℝ × ℝ × ℝ × ℝ) :
    tripleBracket (lineFreeDirection param 0) (lineFreeDirection param 1)
        (lineFreeDirection param 2) = 1
      ∧ tripleBracket (lineFreeDirection param 3) (lineFreeDirection param 1)
        (lineFreeDirection param 2) = 1
      ∧ tripleBracket (lineFreeDirection param 0) (lineFreeDirection param 3)
        (lineFreeDirection param 2) = 1
      ∧ tripleBracket (lineFreeDirection param 0) (lineFreeDirection param 1)
        (lineFreeDirection param 3) = 1
      ∧ tripleBracket (lineFreeDirection param 4) (lineFreeDirection param 1)
        (lineFreeDirection param 2) = 1
      ∧ tripleBracket (lineFreeDirection param 0) (lineFreeDirection param 4)
        (lineFreeDirection param 2) = param.1
      ∧ tripleBracket (lineFreeDirection param 0) (lineFreeDirection param 1)
        (lineFreeDirection param 4) = param.2.1
      ∧ tripleBracket (lineFreeDirection param 5) (lineFreeDirection param 1)
        (lineFreeDirection param 2) = 1
      ∧ tripleBracket (lineFreeDirection param 0) (lineFreeDirection param 5)
        (lineFreeDirection param 2) = param.2.2.1
      ∧ tripleBracket (lineFreeDirection param 0) (lineFreeDirection param 1)
        (lineFreeDirection param 5) = param.2.2.2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] <;> ring

/-! ## The fourteen walls, and exactness of the admissible region -/

set_option maxHeartbeats 1000000 in
/-- **THE CONVERSE OF THE CHART TABLE.**  If every distinct triple of the chart
is independent, the parameter is admissible.  Each of the fourteen conjuncts
comes from ONE named triple, so each forbidden locus is a single wall and the
admissible region is exactly the line-free locus, not a proper subset of it. -/
theorem isAdmissibleLineFreeParameter_of_brackets (param : ℝ × ℝ × ℝ × ℝ)
    (hindependent : ∀ leftLabel midLabel rightLabel : Fin 6,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
      tripleBracket (lineFreeDirection param leftLabel)
        (lineFreeDirection param midLabel)
        (lineFreeDirection param rightLabel) ≠ 0) :
    IsAdmissibleLineFreeParameter param := by
  have hwall : ∀ leftLabel midLabel rightLabel : Fin 6,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
      tripleBracket (lineFreeDirection param leftLabel)
        (lineFreeDirection param midLabel)
        (lineFreeDirection param rightLabel) ≠ 0 := hindependent
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    exact hwall 0 2 4 (by decide) (by decide) (by decide) (by
      simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; linarith)
  · intro hone
    exact hwall 2 3 4 (by decide) (by decide) (by decide) (by
      simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; linarith)
  · intro hzero
    exact hwall 0 1 4 (by decide) (by decide) (by decide) (by
      simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; linarith)
  · intro hone
    exact hwall 1 3 4 (by decide) (by decide) (by decide) (by
      simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; linarith)
  · intro hzero
    exact hwall 0 2 5 (by decide) (by decide) (by decide) (by
      simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; linarith)
  · intro hone
    exact hwall 2 3 5 (by decide) (by decide) (by decide) (by
      simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; linarith)
  · intro hzero
    exact hwall 0 1 5 (by decide) (by decide) (by decide) (by
      simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; linarith)
  · intro hone
    exact hwall 1 3 5 (by decide) (by decide) (by decide) (by
      simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; linarith)
  · intro hdiff
    exact hwall 0 3 4 (by decide) (by decide) (by decide) (by
      simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; linarith)
  · intro hdiff
    exact hwall 0 3 5 (by decide) (by decide) (by decide) (by
      simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; linarith)
  · intro hdiff
    exact hwall 1 4 5 (by decide) (by decide) (by decide) (by
      simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; linarith)
  · intro hdiff
    exact hwall 2 4 5 (by decide) (by decide) (by decide) (by
      simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; linarith)
  · intro hminor
    exact hwall 0 4 5 (by decide) (by decide) (by decide) (by
      simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; linarith)
  · intro hcubic
    exact hwall 3 4 5 (by decide) (by decide) (by decide) (by
      simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; linarith)

/-- **THE ADMISSIBLE REGION IS THE CELL.**  Admissibility and line-freeness of
the chart are the same condition, so the four-parameter chart is the whole
stratum and not a piece of it. -/
theorem isAdmissibleLineFreeParameter_iff_brackets (param : ℝ × ℝ × ℝ × ℝ) :
    IsAdmissibleLineFreeParameter param ↔
      ∀ leftLabel midLabel rightLabel : Fin 6,
        leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        tripleBracket (lineFreeDirection param leftLabel)
          (lineFreeDirection param midLabel)
          (lineFreeDirection param rightLabel) ≠ 0 := by
  refine ⟨fun hadmissible leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
      hzero => ?_, isAdmissibleLineFreeParameter_of_brackets param⟩
  have hiff := tripleBracket_lineFreeDirection_eq_zero_iff param hadmissible
    leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  have hpattern := hiff.mp hzero
  simp only [lineFreeFamily, lineFamilyPattern, List.not_mem_nil, false_and,
    exists_false] at hpattern

/-! ## The moduli are honest -/

/-- The bracket under a frame change and a per-atom scaling: three scales and
one determinant, and nothing else. -/
theorem tripleBracket_of_basisChange_smul (basisChange : Matrix (Fin 3) (Fin 3) ℝ)
    (scaleLeft scaleMid scaleRight : ℝ) (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket (scaleLeft • (basisChange *ᵥ leftVec))
        (scaleMid • (basisChange *ᵥ midVec))
        (scaleRight • (basisChange *ᵥ rightVec))
      = scaleLeft * scaleMid * scaleRight * basisChange.det
        * tripleBracket leftVec midVec rightVec := by
  rw [tripleBracket_smul_slots]
  have hkey := tripleBracket_transpose_mulVec basisChangeᵀ leftVec midVec rightVec
  rw [Matrix.transpose_transpose, Matrix.det_transpose] at hkey
  rw [hkey]
  ring

/-- **BALANCED BRACKET RATIOS ARE ABSOLUTE INVARIANTS.**  A ratio of two bracket
products against two bracket products survives every frame change and every
per-atom scaling, as soon as the two scale products agree.  The statement is
cross-multiplied, so it needs no nonvanishing hypothesis anywhere. -/
theorem bracketRatio_invariant_of_balanced
    (vecBase vecImage : Fin 6 → (Fin 3 → ℝ))
    (basisChange : Matrix (Fin 3) (Fin 3) ℝ) (scale : Fin 6 → ℝ)
    (hframe : ∀ label, vecImage label = scale label • (basisChange *ᵥ vecBase label))
    (numLeft numMid numRight numLeft' numMid' numRight'
      denLeft denMid denRight denLeft' denMid' denRight' : Fin 6)
    (hbalanced : scale numLeft * scale numMid * scale numRight
        * (scale numLeft' * scale numMid' * scale numRight')
      = scale denLeft * scale denMid * scale denRight
        * (scale denLeft' * scale denMid' * scale denRight')) :
    tripleBracket (vecImage numLeft) (vecImage numMid) (vecImage numRight)
        * tripleBracket (vecImage numLeft') (vecImage numMid') (vecImage numRight')
        * (tripleBracket (vecBase denLeft) (vecBase denMid) (vecBase denRight)
          * tripleBracket (vecBase denLeft') (vecBase denMid') (vecBase denRight'))
      = tripleBracket (vecBase numLeft) (vecBase numMid) (vecBase numRight)
        * tripleBracket (vecBase numLeft') (vecBase numMid') (vecBase numRight')
        * (tripleBracket (vecImage denLeft) (vecImage denMid) (vecImage denRight)
          * tripleBracket (vecImage denLeft') (vecImage denMid') (vecImage denRight')) := by
  simp only [hframe, tripleBracket_of_basisChange_smul]
  linear_combination (basisChange.det ^ 2
      * (tripleBracket (vecBase numLeft) (vecBase numMid) (vecBase numRight)
        * tripleBracket (vecBase numLeft') (vecBase numMid') (vecBase numRight')
        * (tripleBracket (vecBase denLeft) (vecBase denMid) (vecBase denRight)
          * tripleBracket (vecBase denLeft') (vecBase denMid') (vecBase denRight'))))
    * hbalanced

set_option maxHeartbeats 1000000 in
/-- **THE CHART HAS NO REDUNDANCY.**  Two chart points related by a frame change
and a per-atom scaling carry the same parameter.  Each coordinate is read off by
one balanced bracket ratio, and the chart evaluates every bracket in that ratio
to `1` or to the coordinate itself. -/
theorem lineFreeDirection_param_injective (paramBase paramImage : ℝ × ℝ × ℝ × ℝ)
    (basisChange : Matrix (Fin 3) (Fin 3) ℝ) (scale : Fin 6 → ℝ)
    (hframe : ∀ label, lineFreeDirection paramImage label
      = scale label • (basisChange *ᵥ lineFreeDirection paramBase label)) :
    paramBase = paramImage := by
  obtain ⟨hbaseBasis, hbaseA, hbaseB, hbaseC, hbaseD, hbaseE, hbaseF,
    hbaseG, hbaseH, hbaseK⟩ := lineFreeChartCoefficients paramBase
  obtain ⟨himageBasis, himageA, himageB, himageC, himageD, himageE, himageF,
    himageG, himageH, himageK⟩ := lineFreeChartCoefficients paramImage
  have hmid := bracketRatio_invariant_of_balanced (lineFreeDirection paramBase)
    (lineFreeDirection paramImage) basisChange scale hframe 0 4 2 3 1 2 4 1 2 0 3 2
    (by ring)
  have hlast := bracketRatio_invariant_of_balanced (lineFreeDirection paramBase)
    (lineFreeDirection paramImage) basisChange scale hframe 0 1 4 3 1 2 4 1 2 0 1 3
    (by ring)
  have hfiveMid := bracketRatio_invariant_of_balanced (lineFreeDirection paramBase)
    (lineFreeDirection paramImage) basisChange scale hframe 0 5 2 3 1 2 5 1 2 0 3 2
    (by ring)
  have hfiveLast := bracketRatio_invariant_of_balanced (lineFreeDirection paramBase)
    (lineFreeDirection paramImage) basisChange scale hframe 0 1 5 3 1 2 5 1 2 0 1 3
    (by ring)
  rw [himageE, himageA, hbaseD, hbaseB, hbaseE, hbaseA, himageD, himageB] at hmid
  rw [himageF, himageA, hbaseD, hbaseC, hbaseF, hbaseA, himageD, himageC] at hlast
  rw [himageH, himageA, hbaseG, hbaseB, hbaseH, hbaseA, himageG, himageB] at hfiveMid
  rw [himageK, himageA, hbaseG, hbaseC, hbaseK, hbaseA, himageG, himageC] at hfiveLast
  obtain ⟨baseMid, baseLast, baseFiveMid, baseFiveLast⟩ := paramBase
  obtain ⟨imageMid, imageLast, imageFiveMid, imageFiveLast⟩ := paramImage
  simp only [Prod.mk.injEq]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## The atlas is not empty -/

/-- An explicit admissible parameter.  The line-free chart has real points, so
the entry `#1` obligation is not vacuous. -/
theorem isAdmissibleLineFreeParameter_two_three_five_seven :
    IsAdmissibleLineFreeParameter ((2 : ℝ), (3 : ℝ), (5 : ℝ), (7 : ℝ)) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

/-- The control in the other direction: a parameter ON a wall is not admissible,
so the fourteen exclusions are not vacuous either. -/
theorem not_isAdmissibleLineFreeParameter_one_three_five_seven :
    ¬ IsAdmissibleLineFreeParameter ((1 : ℝ), (3 : ℝ), (5 : ℝ), (7 : ℝ)) := by
  intro hadmissible
  exact hadmissible.2.1 rfl

end Gtz
