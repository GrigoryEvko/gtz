import Gtz.Design.ThreeLinesTriangleCell
import Gtz.Design.OneDeterminantReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The three-lines chart: one universal gap matrix, one determinant law

`Gtz.ChartTieFreeThreeLinesFundamentalDomain` is the obligation on the chart
whose six directions are

  `v0 = (1,0,0)  v1 = (0,1,0)  v2 = (1,1,0)  v3 = (0,0,1)  v4 = (1,0,1)  v5 = (0,1,slide)`

and whose three dependent triples are the three coordinate planes,
`Gtz.threeLinesFamily = [[0,1,2],[0,3,4],[1,3,5]]`.  The tree already carries the
coordinate triple `{0,1,3}` in closed form (`Gtz.threeLinesGap_triangle_eq`) and a
diagonal-dominance cell built on it.

This module replaces the per-triple approach with a UNIVERSAL one.  Every
weighted sum of the six atoms is one explicit `3 x 3` matrix in the six
coefficients and the slide, so ALL twenty card-three subsets get their closed
form from a single lemma, and each one's positive definiteness becomes three
explicit polynomial signs through the landed Sylvester equivalence.  On top of
that the module lands the Cauchy-Binet basis expansion of the determinant, the
exact `Z/3` rotation symmetry of the chart at fixed slide, a kernel refutation of
the two-cell atlas, a kernel no-go for diagonal dominance at the free triple, and
the reduction of the target obligation to polynomial sign conditions.
-/

namespace Gtz

open Matrix Finset

/-! ## Part 1.  The universal coefficient matrix

Every combination `sum_c coefficient_c * v_c v_c^T` of the six three-lines atoms
is the SAME explicit matrix, read off the six coefficients and the slide.  The
structure is a grounded graph Laplacian on three vertices: `coefficient 2`
couples the first two coordinates, `coefficient 4` the first and third,
`coefficient 5` the second and third with gain `slide`, and `coefficient 0`,
`coefficient 1`, `coefficient 3` sit alone on the diagonal. -/

/-- **The universal three-lines matrix.**  `sum_c coefficient_c * v_c v_c^T`. -/
def threeLinesCoefficientMatrix (slide : ℝ) (coefficient : Fin 6 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![coefficient 0 + coefficient 2 + coefficient 4, coefficient 2, coefficient 4;
     coefficient 2, coefficient 1 + coefficient 2 + coefficient 5, slide * coefficient 5;
     coefficient 4, slide * coefficient 5,
       coefficient 3 + coefficient 4 + slide ^ 2 * coefficient 5]

theorem threeLinesCoefficientMatrix_eq (slide : ℝ) (coefficient : Fin 6 → ℝ) :
    threeLinesCoefficientMatrix slide coefficient
      = !![coefficient 0 + coefficient 2 + coefficient 4, coefficient 2, coefficient 4;
           coefficient 2, coefficient 1 + coefficient 2 + coefficient 5, slide * coefficient 5;
           coefficient 4, slide * coefficient 5,
             coefficient 3 + coefficient 4 + slide ^ 2 * coefficient 5] := rfl

/-- **The universal reading.**  Any weighted sum of the six three-lines atoms is
the universal matrix at those weights. -/
theorem sum_smul_atomMatrix_threeLinesDirection (slide : ℝ) (coefficient : Fin 6 → ℝ) :
    (∑ label, coefficient label • atomMatrix (threeLinesDirection slide label))
      = threeLinesCoefficientMatrix slide coefficient := by
  rw [Fin.sum_univ_six, threeLinesCoefficientMatrix]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [atomMatrix, threeLinesDirection_zero, threeLinesDirection_one,
      threeLinesDirection_two, threeLinesDirection_three, threeLinesDirection_four,
      threeLinesDirection_five, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] <;>
    ring

/-- The quadratic form of the universal matrix: the six READINGS of the probe
against the six three-lines directions, each squared and weighted. -/
theorem dotProduct_threeLinesCoefficientMatrix_mulVec (slide : ℝ) (coefficient : Fin 6 → ℝ)
    (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ (threeLinesCoefficientMatrix slide coefficient *ᵥ probeVec)
      = coefficient 0 * probeVec 0 ^ 2 + coefficient 1 * probeVec 1 ^ 2
        + coefficient 2 * (probeVec 0 + probeVec 1) ^ 2
        + coefficient 3 * probeVec 2 ^ 2
        + coefficient 4 * (probeVec 0 + probeVec 2) ^ 2
        + coefficient 5 * (probeVec 1 + slide * probeVec 2) ^ 2 := by
  rw [threeLinesCoefficientMatrix]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- The coefficient a chart point attaches to a label for a given selection: the
weight EXCESS on the selected labels, MINUS the raw mass off them.  This is the
landed excess split `Gtz.directionChartGap_eq_excessSplit` packaged as one
function of the label. -/
noncomputable def threeLinesChartCoefficient (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) (label : Fin 6) : ℝ :=
  if label ∈ selected then chartExcess mass weight label else -mass label

theorem threeLinesChartCoefficient_of_mem (mass weight : Fin 6 → ℝ)
    {selected : Finset (Fin 6)} {label : Fin 6} (hmem : label ∈ selected) :
    threeLinesChartCoefficient mass weight selected label = chartExcess mass weight label := by
  rw [threeLinesChartCoefficient, if_pos hmem]

theorem threeLinesChartCoefficient_of_notMem (mass weight : Fin 6 → ℝ)
    {selected : Finset (Fin 6)} {label : Fin 6} (hnotMem : label ∉ selected) :
    threeLinesChartCoefficient mass weight selected label = -mass label := by
  rw [threeLinesChartCoefficient, if_neg hnotMem]

/-- **The whole chart in one formula.**  The chart gap of ANY card-three subset
-- indeed of any subset at all -- is the universal matrix at the selection
coefficients.  Every closed form the campaign needs is an instance. -/
theorem directionChartGap_threeLines_eq (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0) (selected : Finset (Fin 6)) :
    directionChartGap (threeLinesDirection slide) mass weight selected
      = threeLinesCoefficientMatrix slide (threeLinesChartCoefficient mass weight selected) := by
  classical
  rw [← sum_smul_atomMatrix_threeLinesDirection,
    directionChartGap_eq_excessSplit _ mass weight hweightNe,
    ← Finset.sum_add_sum_compl selected
      (fun label => threeLinesChartCoefficient mass weight selected label •
        atomMatrix (threeLinesDirection slide label))]
  have hselected : ∑ label ∈ selected,
        (mass label * (1 - weight label) / weight label) •
          atomMatrix (threeLinesDirection slide label)
      = ∑ label ∈ selected, threeLinesChartCoefficient mass weight selected label •
          atomMatrix (threeLinesDirection slide label) :=
    Finset.sum_congr rfl fun label hmem => by
      rw [threeLinesChartCoefficient_of_mem mass weight hmem, chartExcess]
  have hcomplement : ∑ label ∈ selectedᶜ, threeLinesChartCoefficient mass weight selected label •
        atomMatrix (threeLinesDirection slide label)
      = -∑ label ∈ selectedᶜ, mass label • atomMatrix (threeLinesDirection slide label) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun label hmem => by
      rw [threeLinesChartCoefficient_of_notMem mass weight (Finset.mem_compl.mp hmem), neg_smul]
  rw [hselected, hcomplement, sub_eq_add_neg]

/-- **Consistency with the landed triangle formula.**  Specialised at the
coordinate triple, the universal formula reproduces `Gtz.threeLinesGap_triangle_eq`
entry for entry. -/
theorem threeLinesCoefficientMatrix_triangle_eq (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0) :
    threeLinesCoefficientMatrix slide (threeLinesChartCoefficient mass weight {0, 1, 3})
      = !![chartExcess mass weight 0 - mass 2 - mass 4, -mass 2, -mass 4;
           -mass 2, chartExcess mass weight 1 - mass 2 - mass 5, -(slide * mass 5);
           -mass 4, -(slide * mass 5),
             chartExcess mass weight 3 - mass 4 - slide ^ 2 * mass 5] := by
  rw [← directionChartGap_threeLines_eq slide mass weight hweightNe,
    threeLinesGap_triangle_eq slide mass weight hweightNe]

/-! ## Part 2.  Sylvester in closed form

Each leading minor of the universal matrix is a Cauchy-Binet sum over the
independent sub-configurations of the matching size: three labels for the corner,
eight pairs for the block, seventeen triples for the determinant, each weighted
by its squared bracket.  The three DEPENDENT triples -- the three lines
`{0,1,2}`, `{0,3,4}`, `{1,3,5}` -- carry coefficient zero and are absent. -/

/-- The first leading minor: the three labels whose first coordinate is nonzero. -/
def threeLinesCornerMinor (coefficient : Fin 6 → ℝ) : ℝ :=
  coefficient 0 + coefficient 2 + coefficient 4

/-- The second leading minor, in Cauchy-Binet form: the sum over the EIGHT pairs
whose shadow on the first two coordinates is independent.  The seven missing
pairs are those sharing a shadow -- `{0,3}`, `{0,4}`, `{1,3}`, `{1,5}`, `{2,3}`,
`{3,4}`, `{3,5}`. -/
def threeLinesBlockMinor (coefficient : Fin 6 → ℝ) : ℝ :=
  coefficient 0 * coefficient 1 + coefficient 0 * coefficient 2
    + coefficient 0 * coefficient 5 + coefficient 1 * coefficient 2
    + coefficient 1 * coefficient 4 + coefficient 2 * coefficient 4
    + coefficient 2 * coefficient 5 + coefficient 4 * coefficient 5

/-- **The determinant law.**  The Cauchy-Binet expansion over the SEVENTEEN
independent triples.  The squared bracket is `1` on twelve of them, `slide ^ 2`
on the four triples `{0,1,5}`, `{0,2,5}`, `{1,2,5}`, `{1,4,5}`, and
`(1 + slide) ^ 2` on the free triple `{2,4,5}`.  The two slides admissibility
excludes are exactly the two vanishings: `slide = 0` kills those four, and
`slide = -1` kills `{2,4,5}`. -/
def threeLinesBasisDeterminant (slide : ℝ) (coefficient : Fin 6 → ℝ) : ℝ :=
  coefficient 0 * coefficient 1 * coefficient 3
    + coefficient 0 * coefficient 1 * coefficient 4
    + slide ^ 2 * (coefficient 0 * coefficient 1 * coefficient 5)
    + coefficient 0 * coefficient 2 * coefficient 3
    + coefficient 0 * coefficient 2 * coefficient 4
    + slide ^ 2 * (coefficient 0 * coefficient 2 * coefficient 5)
    + coefficient 0 * coefficient 3 * coefficient 5
    + coefficient 0 * coefficient 4 * coefficient 5
    + coefficient 1 * coefficient 2 * coefficient 3
    + coefficient 1 * coefficient 2 * coefficient 4
    + slide ^ 2 * (coefficient 1 * coefficient 2 * coefficient 5)
    + coefficient 1 * coefficient 3 * coefficient 4
    + slide ^ 2 * (coefficient 1 * coefficient 4 * coefficient 5)
    + coefficient 2 * coefficient 3 * coefficient 4
    + coefficient 2 * coefficient 3 * coefficient 5
    + (1 + slide) ^ 2 * (coefficient 2 * coefficient 4 * coefficient 5)
    + coefficient 3 * coefficient 4 * coefficient 5

/-- The determinant of an explicit symmetric `3 x 3`, with no index reduction
left for the caller. -/
theorem det_symmetricFinThree_eq_expansion (entryOneOne entryOneTwo entryOneThree
    entryTwoTwo entryTwoThree entryThreeThree : ℝ) :
    (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).det
      = entryOneOne * entryTwoTwo * entryThreeThree - entryOneOne * entryTwoThree ^ 2
        - entryOneTwo ^ 2 * entryThreeThree + 2 * entryOneTwo * entryOneThree * entryTwoThree
        - entryOneThree ^ 2 * entryTwoTwo := by
  simp [Matrix.det_fin_three]
  ring

/-- **Cauchy-Binet for the three-lines chart.**  The determinant of the universal
matrix IS the basis expansion. -/
theorem det_threeLinesCoefficientMatrix (slide : ℝ) (coefficient : Fin 6 → ℝ) :
    (threeLinesCoefficientMatrix slide coefficient).det
      = threeLinesBasisDeterminant slide coefficient := by
  rw [threeLinesCoefficientMatrix, det_symmetricFinThree_eq_expansion,
    threeLinesBasisDeterminant]
  ring

/-- **Three polynomial signs decide every subset.**  Positive definiteness of the
universal matrix is exactly the positivity of the corner, the block and the
basis determinant. -/
theorem posDef_threeLinesCoefficientMatrix_iff (slide : ℝ) (coefficient : Fin 6 → ℝ) :
    (threeLinesCoefficientMatrix slide coefficient).PosDef
      ↔ 0 < threeLinesCornerMinor coefficient ∧ 0 < threeLinesBlockMinor coefficient
        ∧ 0 < threeLinesBasisDeterminant slide coefficient := by
  rw [threeLinesCoefficientMatrix, leadingMinors_pos_iff_posDef_fin_three,
    threeLinesCornerMinor, threeLinesBlockMinor, threeLinesBasisDeterminant]
  constructor
  · rintro ⟨hcorner, hblock, hdet⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hcorner, hblock, hdet⟩
    exact ⟨by linarith, by linarith, by linarith⟩

/-- **The chart obligation as polynomial arithmetic.**  At any chart point, a
card-three subset dominates STRICTLY exactly when its three closed-form minors
are positive. -/
theorem posDef_directionChartGap_threeLines_iff (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0) (selected : Finset (Fin 6)) :
    (directionChartGap (threeLinesDirection slide) mass weight selected).PosDef
      ↔ 0 < threeLinesCornerMinor (threeLinesChartCoefficient mass weight selected)
        ∧ 0 < threeLinesBlockMinor (threeLinesChartCoefficient mass weight selected)
        ∧ 0 < threeLinesBasisDeterminant slide
            (threeLinesChartCoefficient mass weight selected) := by
  rw [directionChartGap_threeLines_eq slide mass weight hweightNe,
    posDef_threeLinesCoefficientMatrix_iff]

/-- The chart gap's quadratic form at a probe, in the six readings. -/
theorem dotProduct_directionChartGap_threeLines_mulVec (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0) (selected : Finset (Fin 6))
    (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ (directionChartGap (threeLinesDirection slide) mass weight selected *ᵥ probeVec)
      = threeLinesChartCoefficient mass weight selected 0 * probeVec 0 ^ 2
        + threeLinesChartCoefficient mass weight selected 1 * probeVec 1 ^ 2
        + threeLinesChartCoefficient mass weight selected 2 * (probeVec 0 + probeVec 1) ^ 2
        + threeLinesChartCoefficient mass weight selected 3 * probeVec 2 ^ 2
        + threeLinesChartCoefficient mass weight selected 4 * (probeVec 0 + probeVec 2) ^ 2
        + threeLinesChartCoefficient mass weight selected 5
            * (probeVec 1 + slide * probeVec 2) ^ 2 := by
  rw [directionChartGap_threeLines_eq slide mass weight hweightNe,
    dotProduct_threeLinesCoefficientMatrix_mulVec]

/-! ## Part 3.  The two canonical triples

The `Z/3` rotation of Part 5 fixes exactly two card-three subsets: the VERTEX
triple `{0,1,3}` (the three coordinate axes, each on two of the lines) and the
FREE triple `{2,4,5}` (the three points lying on one line each).  Both are
independent for every admissible slide, and the two slides admissibility excludes
are exactly the two degenerations. -/

theorem tripleBracket_threeLinesDirection_vertexTriple (slide : ℝ) :
    tripleBracket (threeLinesDirection slide 0) (threeLinesDirection slide 1)
        (threeLinesDirection slide 3) = 1 := by
  simp [tripleBracket_eq, threeLinesDirection_zero, threeLinesDirection_one,
    threeLinesDirection_three]

/-- **The free triple degenerates exactly at `slide = -1`.** -/
theorem tripleBracket_threeLinesDirection_freeTriple (slide : ℝ) :
    tripleBracket (threeLinesDirection slide 2) (threeLinesDirection slide 4)
        (threeLinesDirection slide 5) = -(1 + slide) := by
  simp [tripleBracket_eq, threeLinesDirection_two, threeLinesDirection_four,
    threeLinesDirection_five]
  ring

/-- **The other admissibility exclusion.**  The triple `{1,2,5}` degenerates
exactly at `slide = 0`. -/
theorem tripleBracket_threeLinesDirection_oneTwoFive (slide : ℝ) :
    tripleBracket (threeLinesDirection slide 1) (threeLinesDirection slide 2)
        (threeLinesDirection slide 5) = -slide := by
  simp [tripleBracket_eq, threeLinesDirection_one, threeLinesDirection_two,
    threeLinesDirection_five]

/-- With the three SIDE coefficients switched off, the basis determinant is the
bare vertex product. -/
theorem threeLinesBasisDeterminant_of_sideFree (slide : ℝ) (coefficient : Fin 6 → ℝ)
    (htwo : coefficient 2 = 0) (hfour : coefficient 4 = 0) (hfive : coefficient 5 = 0) :
    threeLinesBasisDeterminant slide coefficient
      = coefficient 0 * coefficient 1 * coefficient 3 := by
  rw [threeLinesBasisDeterminant, htwo, hfour, hfive]
  ring

/-- With the three VERTEX coefficients switched off, the basis determinant is the
free product with the exact leading factor `(1 + slide) ^ 2`.  This is why
`Gtz.IsAdmissibleThreeLinesParameter` excludes `slide = -1`. -/
theorem threeLinesBasisDeterminant_of_vertexFree (slide : ℝ) (coefficient : Fin 6 → ℝ)
    (hzero : coefficient 0 = 0) (hone : coefficient 1 = 0) (hthree : coefficient 3 = 0) :
    threeLinesBasisDeterminant slide coefficient
      = (1 + slide) ^ 2 * (coefficient 2 * coefficient 4 * coefficient 5) := by
  rw [threeLinesBasisDeterminant, hzero, hone, hthree]
  ring

/-- **The free triple in closed form.**  Read against the vertex triple's landed
formula the signs are reversed: here the OFF-diagonal entries carry the selected
excesses and the outside masses sit alone on the diagonal. -/
theorem threeLinesGap_freeTriple_eq (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0) :
    directionChartGap (threeLinesDirection slide) mass weight {2, 4, 5}
      = !![chartExcess mass weight 2 + chartExcess mass weight 4 - mass 0,
           chartExcess mass weight 2, chartExcess mass weight 4;
           chartExcess mass weight 2,
             chartExcess mass weight 2 + chartExcess mass weight 5 - mass 1,
             slide * chartExcess mass weight 5;
           chartExcess mass weight 4, slide * chartExcess mass weight 5,
             chartExcess mass weight 4 + slide ^ 2 * chartExcess mass weight 5 - mass 3] := by
  rw [directionChartGap_threeLines_eq slide mass weight hweightNe, threeLinesCoefficientMatrix,
    threeLinesChartCoefficient_of_notMem mass weight
      (show (0 : Fin 6) ∉ ({2, 4, 5} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_notMem mass weight
      (show (1 : Fin 6) ∉ ({2, 4, 5} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_notMem mass weight
      (show (3 : Fin 6) ∉ ({2, 4, 5} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_mem mass weight
      (show (2 : Fin 6) ∈ ({2, 4, 5} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_mem mass weight
      (show (4 : Fin 6) ∈ ({2, 4, 5} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_mem mass weight
      (show (5 : Fin 6) ∈ ({2, 4, 5} : Finset (Fin 6)) by decide)]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] <;> ring

/-- **Diagonal dominance provably cannot produce the free triple.**  Any bound
admissible for the landed dominance producer `Gtz.posDef_of_dominance_fin_three`
is at least the off-diagonal entry it bounds, and at the free triple the two
off-diagonals of the first row are exactly the two excesses the first diagonal
entry is built from -- so the first dominance inequality asks the outside mass at
label `0` to be negative.  The free triple needs the leading-minor route. -/
theorem threeLines_freeTriple_not_diagonallyDominant (mass weight : Fin 6 → ℝ)
    (hmassZeroPos : 0 < mass 0) (boundOneTwo boundOneThree : ℝ)
    (hboundOneTwoNonneg : 0 ≤ boundOneTwo) (hboundOneThreeNonneg : 0 ≤ boundOneThree)
    (hsquareOneTwo : chartExcess mass weight 2 ^ 2 ≤ boundOneTwo ^ 2)
    (hsquareOneThree : chartExcess mass weight 4 ^ 2 ≤ boundOneThree ^ 2) :
    ¬ (boundOneTwo + boundOneThree
        < chartExcess mass weight 2 + chartExcess mass weight 4 - mass 0) := by
  intro hdominate
  have hexcessTwo : chartExcess mass weight 2 ≤ boundOneTwo := by
    nlinarith [hsquareOneTwo, hboundOneTwoNonneg]
  have hexcessFour : chartExcess mass weight 4 ≤ boundOneThree := by
    nlinarith [hsquareOneThree, hboundOneThreeNonneg]
  linarith

/-! ## Part 4.  Both canonical triples fail -- in kernel

The `Z/3` rotation of Part 5 fixes exactly two card-three subsets: the VERTEX
triple `{0,1,3}` (the three coordinate axes, each lying on two of the lines) and
the FREE triple `{2,4,5}` (the three points lying on one line each).  They are
the campaign's two natural candidate cells.  The chart point below, at
`slide = 2` and so inside the fundamental domain `1 <= |slide|`, has NEITHER of
them even weakly dominating and still carries a strictly dominating triple.  A
two-cell atlas on the canonical pair is therefore impossible, and since those two
are exactly the rotation-fixed subsets, any atlas must reach into the moved
orbits. -/

/-- A negative reading of the quadratic form refutes weak domination. -/
theorem not_posSemidef_of_neg_dotProduct {matrixArg : Matrix (Fin 3) (Fin 3) ℝ}
    {probeVec : Fin 3 → ℝ} (hneg : probeVec ⬝ᵥ (matrixArg *ᵥ probeVec) < 0) :
    ¬ matrixArg.PosSemidef := by
  intro hposSemidef
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hposSemidef).2 probeVec
  rw [star_trivial] at hnonneg
  linarith

/-- The third coordinate axis, as a probe. -/
def verticalProbe : Fin 3 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 1

/-- The first coordinate axis, as a probe. -/
def firstAxisProbe : Fin 3 → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 0

noncomputable def canonicalPairFailureMass : Fin 6 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1 / 10
  | 3 => 1
  | 4 => 1 / 10
  | 5 => 1

noncomputable def canonicalPairFailureWeight : Fin 6 → ℝ
  | 0 => 1 / 99
  | 1 => 1 / 99
  | 2 => 32 / 99
  | 3 => 32 / 99
  | 4 => 32 / 99
  | 5 => 1 / 99

theorem canonicalPairFailureMass_pos (label : Fin 6) : 0 < canonicalPairFailureMass label := by
  fin_cases label <;> norm_num [canonicalPairFailureMass]

theorem canonicalPairFailureWeight_pos (label : Fin 6) :
    0 < canonicalPairFailureWeight label := by
  fin_cases label <;> norm_num [canonicalPairFailureWeight]

theorem canonicalPairFailureWeight_ne (label : Fin 6) : canonicalPairFailureWeight label ≠ 0 :=
  ne_of_gt (canonicalPairFailureWeight_pos label)

theorem canonicalPairFailureWeight_sum : ∑ label, canonicalPairFailureWeight label = 1 := by
  rw [Fin.sum_univ_six]
  norm_num [canonicalPairFailureWeight]

/-- The chart point at which both rotation-fixed triples fail. -/
noncomputable def canonicalPairFailurePoint : DirectionChartPoint 6 where
  mass := canonicalPairFailureMass
  weight := canonicalPairFailureWeight
  mass_pos := canonicalPairFailureMass_pos
  weight_pos := canonicalPairFailureWeight_pos
  weight_sum_one := canonicalPairFailureWeight_sum

/-- The vertex triple's form at the vertical probe: `67/32 - 1/10 - 4`. -/
theorem canonicalPairFailure_vertexTriple_verticalForm :
    verticalProbe ⬝ᵥ (directionChartGap (threeLinesDirection 2) canonicalPairFailureMass
        canonicalPairFailureWeight {0, 1, 3} *ᵥ verticalProbe) = -(321 / 160) := by
  rw [dotProduct_directionChartGap_threeLines_mulVec 2 canonicalPairFailureMass
      canonicalPairFailureWeight canonicalPairFailureWeight_ne,
    threeLinesChartCoefficient_of_mem canonicalPairFailureMass canonicalPairFailureWeight
      (show (0 : Fin 6) ∈ ({0, 1, 3} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_mem canonicalPairFailureMass canonicalPairFailureWeight
      (show (1 : Fin 6) ∈ ({0, 1, 3} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_notMem canonicalPairFailureMass canonicalPairFailureWeight
      (show (2 : Fin 6) ∉ ({0, 1, 3} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_mem canonicalPairFailureMass canonicalPairFailureWeight
      (show (3 : Fin 6) ∈ ({0, 1, 3} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_notMem canonicalPairFailureMass canonicalPairFailureWeight
      (show (4 : Fin 6) ∉ ({0, 1, 3} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_notMem canonicalPairFailureMass canonicalPairFailureWeight
      (show (5 : Fin 6) ∉ ({0, 1, 3} : Finset (Fin 6)) by decide)]
  norm_num [chartExcess, canonicalPairFailureMass, canonicalPairFailureWeight, verticalProbe]

theorem canonicalPairFailure_vertexTriple_not_posSemidef :
    ¬ (directionChartGap (threeLinesDirection 2) canonicalPairFailureMass
        canonicalPairFailureWeight {0, 1, 3}).PosSemidef :=
  not_posSemidef_of_neg_dotProduct
    (by rw [canonicalPairFailure_vertexTriple_verticalForm]; norm_num)

/-- The free triple's form at the first axis probe: `67/320 + 67/320 - 1`. -/
theorem canonicalPairFailure_freeTriple_axisForm :
    firstAxisProbe ⬝ᵥ (directionChartGap (threeLinesDirection 2) canonicalPairFailureMass
        canonicalPairFailureWeight {2, 4, 5} *ᵥ firstAxisProbe) = -(93 / 160) := by
  rw [dotProduct_directionChartGap_threeLines_mulVec 2 canonicalPairFailureMass
      canonicalPairFailureWeight canonicalPairFailureWeight_ne,
    threeLinesChartCoefficient_of_notMem canonicalPairFailureMass canonicalPairFailureWeight
      (show (0 : Fin 6) ∉ ({2, 4, 5} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_notMem canonicalPairFailureMass canonicalPairFailureWeight
      (show (1 : Fin 6) ∉ ({2, 4, 5} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_mem canonicalPairFailureMass canonicalPairFailureWeight
      (show (2 : Fin 6) ∈ ({2, 4, 5} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_notMem canonicalPairFailureMass canonicalPairFailureWeight
      (show (3 : Fin 6) ∉ ({2, 4, 5} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_mem canonicalPairFailureMass canonicalPairFailureWeight
      (show (4 : Fin 6) ∈ ({2, 4, 5} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_mem canonicalPairFailureMass canonicalPairFailureWeight
      (show (5 : Fin 6) ∈ ({2, 4, 5} : Finset (Fin 6)) by decide)]
  norm_num [chartExcess, canonicalPairFailureMass, canonicalPairFailureWeight, firstAxisProbe]

theorem canonicalPairFailure_freeTriple_not_posSemidef :
    ¬ (directionChartGap (threeLinesDirection 2) canonicalPairFailureMass
        canonicalPairFailureWeight {2, 4, 5}).PosSemidef :=
  not_posSemidef_of_neg_dotProduct
    (by rw [canonicalPairFailure_freeTriple_axisForm]; norm_num)

/-- A third triple IS strictly dominating there, so the point refutes only the
two-cell strategy, never the obligation. -/
theorem canonicalPairFailure_zeroOneFive_posDef :
    (directionChartGap (threeLinesDirection 2) canonicalPairFailureMass
      canonicalPairFailureWeight {0, 1, 5}).PosDef := by
  have hzero := threeLinesChartCoefficient_of_mem canonicalPairFailureMass
    canonicalPairFailureWeight (show (0 : Fin 6) ∈ ({0, 1, 5} : Finset (Fin 6)) by decide)
  have hone := threeLinesChartCoefficient_of_mem canonicalPairFailureMass
    canonicalPairFailureWeight (show (1 : Fin 6) ∈ ({0, 1, 5} : Finset (Fin 6)) by decide)
  have htwo := threeLinesChartCoefficient_of_notMem canonicalPairFailureMass
    canonicalPairFailureWeight (show (2 : Fin 6) ∉ ({0, 1, 5} : Finset (Fin 6)) by decide)
  have hthree := threeLinesChartCoefficient_of_notMem canonicalPairFailureMass
    canonicalPairFailureWeight (show (3 : Fin 6) ∉ ({0, 1, 5} : Finset (Fin 6)) by decide)
  have hfour := threeLinesChartCoefficient_of_notMem canonicalPairFailureMass
    canonicalPairFailureWeight (show (4 : Fin 6) ∉ ({0, 1, 5} : Finset (Fin 6)) by decide)
  have hfive := threeLinesChartCoefficient_of_mem canonicalPairFailureMass
    canonicalPairFailureWeight (show (5 : Fin 6) ∈ ({0, 1, 5} : Finset (Fin 6)) by decide)
  rw [posDef_directionChartGap_threeLines_iff 2 canonicalPairFailureMass
    canonicalPairFailureWeight canonicalPairFailureWeight_ne]
  refine ⟨?_, ?_, ?_⟩
  · rw [threeLinesCornerMinor, hzero, htwo, hfour]
    norm_num [chartExcess, canonicalPairFailureMass, canonicalPairFailureWeight]
  · rw [threeLinesBlockMinor, hzero, hone, htwo, hfour, hfive]
    norm_num [chartExcess, canonicalPairFailureMass, canonicalPairFailureWeight]
  · rw [threeLinesBasisDeterminant, hzero, hone, htwo, hthree, hfour, hfive]
    norm_num [chartExcess, canonicalPairFailureMass, canonicalPairFailureWeight]

/-- **THE REFUTATION.**  Inside the fundamental domain there is a chart point at
which neither rotation-fixed triple weakly dominates, and some other triple
dominates strictly. -/
theorem exists_threeLinesChartPoint_bothCanonicalTriplesFail :
    ∃ slide : ℝ, IsAdmissibleThreeLinesParameter slide ∧ 1 ≤ |slide| ∧
      ∃ point : DirectionChartPoint 6,
        ¬ (directionChartGap (threeLinesDirection slide) point.mass point.weight
            {0, 1, 3}).PosSemidef ∧
        ¬ (directionChartGap (threeLinesDirection slide) point.mass point.weight
            {2, 4, 5}).PosSemidef ∧
        ∃ selected : Finset (Fin 6), selected.card = 3 ∧
          (directionChartGap (threeLinesDirection slide) point.mass point.weight
            selected).PosDef :=
  ⟨2, ⟨by norm_num, by norm_num⟩,
    by rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; norm_num,
    canonicalPairFailurePoint, canonicalPairFailure_vertexTriple_not_posSemidef,
    canonicalPairFailure_freeTriple_not_posSemidef,
    {0, 1, 5}, by decide, canonicalPairFailure_zeroOneFive_posDef⟩

/-! ## Part 5.  The chart has an exact `Z/3` rotation symmetry

The three-lines configuration is a triangle with vertices `0`, `1`, `3` and one
extra point on each side (`2` on `{0,1}`, `4` on `{0,3}`, `5` on `{1,3}`), so the
symmetric group of the three lines acts on it.  Transpositions send the slide to
`1 / slide` -- that is the landed involution whose fundamental domain the target
is stated on.  The THREE-CYCLE, by contrast, FIXES the slide: it is an exact
symmetry of the chart at every fixed parameter, realised by one invertible change
of basis of determinant `slide`.

Consequence for atlas work: the twenty card-three subsets fall into seven orbits
-- the two fixed subsets `{0,1,3}` and `{2,4,5}`, the orbit of the three lines,
and five orbits of size three -- and a certificate for one member of an orbit
transports to the other two. -/

/-- The label three-cycle `(0 1 3)(2 5 4)`. -/
def threeLinesRotationLabel : Fin 6 → Fin 6
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 0
  | 4 => 2
  | 5 => 4

/-- Its inverse, `(0 3 1)(2 4 5)`. -/
def threeLinesRotationLabelInverse : Fin 6 → Fin 6
  | 0 => 3
  | 1 => 0
  | 2 => 4
  | 3 => 1
  | 4 => 5
  | 5 => 2

/-- The three-cycle as a permutation. -/
def threeLinesRotation : Equiv.Perm (Fin 6) where
  toFun := threeLinesRotationLabel
  invFun := threeLinesRotationLabelInverse
  left_inv := by decide
  right_inv := by decide

theorem threeLinesRotation_apply (label : Fin 6) :
    threeLinesRotation label = threeLinesRotationLabel label := rfl

theorem threeLinesRotation_symm_apply (label : Fin 6) :
    threeLinesRotation.symm label = threeLinesRotationLabelInverse label := rfl

/-- The rotation permutes the three lines cyclically. -/
theorem threeLinesRotation_map_firstLine :
    ({0, 1, 2} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {1, 3, 5} := by decide

theorem threeLinesRotation_map_secondLine :
    ({0, 3, 4} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {0, 1, 2} := by decide

theorem threeLinesRotation_map_thirdLine :
    ({1, 3, 5} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {0, 3, 4} := by decide

/-- The vertex triple is FIXED by the rotation. -/
theorem threeLinesRotation_map_vertexTriple :
    ({0, 1, 3} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {0, 1, 3} := by decide

/-- The free triple is FIXED by the rotation. -/
theorem threeLinesRotation_map_freeTriple :
    ({2, 4, 5} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {2, 4, 5} := by decide

/-- The scale the rotation attaches to each direction. -/
def threeLinesRotationScale (slide : ℝ) : Fin 6 → ℝ
  | 0 => 1
  | 1 => slide
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => slide

theorem threeLinesRotationScale_eq_one_or_slide (slide : ℝ) (label : Fin 6) :
    threeLinesRotationScale slide label = 1 ∨ threeLinesRotationScale slide label = slide := by
  fin_cases label
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem threeLinesRotationScale_sq_pos (slide : ℝ) (hslideNe : slide ≠ 0) (label : Fin 6) :
    0 < threeLinesRotationScale slide label ^ 2 := by
  rcases threeLinesRotationScale_eq_one_or_slide slide label with hvalue | hvalue <;> rw [hvalue]
  · norm_num
  · positivity

/-- The change of basis realising the rotation: it sends the first axis to the
second, the second to `slide` times the third, and the third to the first. -/
def threeLinesRotationBasis (slide : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 1; 1, 0, 0; 0, slide, 0]

theorem det_threeLinesRotationBasis (slide : ℝ) :
    (threeLinesRotationBasis slide).det = slide := by
  rw [threeLinesRotationBasis, Matrix.det_fin_three]
  simp

/-- **The configuration is self-similar at fixed slide.**  One invertible map
carries every three-lines direction to a positive multiple of the direction at
the rotated label. -/
theorem threeLinesRotationBasis_mulVec_direction (slide : ℝ) (label : Fin 6) :
    threeLinesRotationBasis slide *ᵥ threeLinesDirection slide label
      = threeLinesRotationScale slide label •
        threeLinesDirection slide (threeLinesRotation label) := by
  fin_cases label <;>
    (funext coordIndex;
      fin_cases coordIndex <;>
        simp [threeLinesRotationBasis, threeLinesRotationScale, threeLinesRotation_apply,
          threeLinesRotationLabel, threeLinesDirection, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three])

/-- **The rotation conjugates the universal matrix into itself**, with the
coefficients permuted and rescaled by the squared scales. -/
theorem threeLinesCoefficientMatrix_rotate (slide : ℝ) (coefficient : Fin 6 → ℝ) :
    threeLinesRotationBasis slide * threeLinesCoefficientMatrix slide coefficient
        * (threeLinesRotationBasis slide)ᵀ
      = threeLinesCoefficientMatrix slide (fun label =>
          coefficient (threeLinesRotation.symm label)
            * threeLinesRotationScale slide (threeLinesRotation.symm label) ^ 2) := by
  simp only [threeLinesCoefficientMatrix, threeLinesRotationBasis, threeLinesRotation_symm_apply,
    threeLinesRotationLabelInverse, threeLinesRotationScale]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- The chart point the rotation produces: weights permuted, masses permuted and
rescaled. -/
noncomputable def rotatedThreeLinesChartPoint (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) : DirectionChartPoint 6 where
  mass := fun label => point.mass (threeLinesRotation.symm label)
    * threeLinesRotationScale slide (threeLinesRotation.symm label) ^ 2
  weight := fun label => point.weight (threeLinesRotation.symm label)
  mass_pos := fun label =>
    mul_pos (point.mass_pos _) (threeLinesRotationScale_sq_pos slide hslideNe _)
  weight_pos := fun label => point.weight_pos _
  weight_sum_one := by
    rw [Equiv.sum_comp threeLinesRotation.symm point.weight]
    exact point.weight_sum_one

theorem rotatedThreeLinesChartPoint_mass (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) (label : Fin 6) :
    (rotatedThreeLinesChartPoint slide hslideNe point).mass label
      = point.mass (threeLinesRotation.symm label)
        * threeLinesRotationScale slide (threeLinesRotation.symm label) ^ 2 := rfl

theorem rotatedThreeLinesChartPoint_weight (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) (label : Fin 6) :
    (rotatedThreeLinesChartPoint slide hslideNe point).weight label
      = point.weight (threeLinesRotation.symm label) := rfl

theorem threeLinesChartCoefficient_rotated (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6)) (label : Fin 6) :
    threeLinesChartCoefficient (rotatedThreeLinesChartPoint slide hslideNe point).mass
        (rotatedThreeLinesChartPoint slide hslideNe point).weight
        (selected.map threeLinesRotation.toEmbedding) label
      = threeLinesChartCoefficient point.mass point.weight selected
            (threeLinesRotation.symm label)
        * threeLinesRotationScale slide (threeLinesRotation.symm label) ^ 2 := by
  by_cases hmem : threeLinesRotation.symm label ∈ selected
  · rw [threeLinesChartCoefficient_of_mem _ _ (Finset.mem_map_equiv.mpr hmem),
      threeLinesChartCoefficient_of_mem _ _ hmem, chartExcess, chartExcess,
      rotatedThreeLinesChartPoint_mass, rotatedThreeLinesChartPoint_weight]
    ring
  · rw [threeLinesChartCoefficient_of_notMem _ _
        (fun hcontra => hmem (Finset.mem_map_equiv.mp hcontra)),
      threeLinesChartCoefficient_of_notMem _ _ hmem, rotatedThreeLinesChartPoint_mass]
    ring

/-- **The gap conjugation.**  The chart gap at a subset, conjugated by the
rotation basis, is the chart gap of the rotated subset at the rotated point. -/
theorem directionChartGap_threeLines_rotate (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6)) :
    threeLinesRotationBasis slide
        * directionChartGap (threeLinesDirection slide) point.mass point.weight selected
        * (threeLinesRotationBasis slide)ᵀ
      = directionChartGap (threeLinesDirection slide)
          (rotatedThreeLinesChartPoint slide hslideNe point).mass
          (rotatedThreeLinesChartPoint slide hslideNe point).weight
          (selected.map threeLinesRotation.toEmbedding) := by
  rw [directionChartGap_threeLines_eq slide point.mass point.weight
      (fun label => ne_of_gt (point.weight_pos label)) selected,
    directionChartGap_threeLines_eq slide (rotatedThreeLinesChartPoint slide hslideNe point).mass
      (rotatedThreeLinesChartPoint slide hslideNe point).weight
      (fun label =>
        ne_of_gt ((rotatedThreeLinesChartPoint slide hslideNe point).weight_pos label))
      (selected.map threeLinesRotation.toEmbedding),
    threeLinesCoefficientMatrix_rotate]
  congr 1
  funext label
  exact (threeLinesChartCoefficient_rotated slide hslideNe point selected label).symm

/-- **Strict domination transports along the rotation.** -/
theorem posDef_directionChartGap_threeLines_rotate_iff (slide : ℝ) (hslideNe : slide ≠ 0)
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6)) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight selected).PosDef
      ↔ (directionChartGap (threeLinesDirection slide)
          (rotatedThreeLinesChartPoint slide hslideNe point).mass
          (rotatedThreeLinesChartPoint slide hslideNe point).weight
          (selected.map threeLinesRotation.toEmbedding)).PosDef := by
  rw [← directionChartGap_threeLines_rotate slide hslideNe point selected]
  have hunit : IsUnit ((threeLinesRotationBasis slide)ᵀ).det := by
    rw [Matrix.det_transpose, det_threeLinesRotationBasis]
    exact isUnit_iff_ne_zero.mpr hslideNe
  have hcongr := posDef_congr_right (X := directionChartGap (threeLinesDirection slide)
      point.mass point.weight selected) (P := (threeLinesRotationBasis slide)ᵀ)
    (directionChartGap_transpose (threeLinesDirection slide) point.mass point.weight selected)
    hunit
  rw [Matrix.transpose_transpose] at hcongr
  exact hcongr

/-- The rotated subset has the same cardinality, so a card-three certificate
transports to a card-three certificate. -/
theorem card_map_threeLinesRotation (selected : Finset (Fin 6)) :
    (selected.map threeLinesRotation.toEmbedding).card = selected.card :=
  Finset.card_map _

/-! ## Part 6.  The free triple does win somewhere, and the orbit transports

Two consumers of the machinery.  First, a second chart point at which the FREE
triple is strictly dominating -- the closed form of Part 3 and the sharp
Sylvester test of Part 2 are not vacuous.  Second, the rotation carried out
concretely: the strict triple `{0,1,5}` of Part 4 becomes a strict `{1,3,4}` at
the rotated point, with no new arithmetic. -/

noncomputable def freeTripleWitnessMass : Fin 6 → ℝ
  | 0 => 1 / 10
  | 1 => 1 / 10
  | 2 => 1
  | 3 => 1 / 10
  | 4 => 1
  | 5 => 1

noncomputable def freeTripleWitnessWeight : Fin 6 → ℝ
  | 0 => 32 / 99
  | 1 => 32 / 99
  | 2 => 1 / 99
  | 3 => 32 / 99
  | 4 => 1 / 99
  | 5 => 1 / 99

theorem freeTripleWitnessMass_pos (label : Fin 6) : 0 < freeTripleWitnessMass label := by
  fin_cases label <;> norm_num [freeTripleWitnessMass]

theorem freeTripleWitnessWeight_pos (label : Fin 6) : 0 < freeTripleWitnessWeight label := by
  fin_cases label <;> norm_num [freeTripleWitnessWeight]

theorem freeTripleWitnessWeight_ne (label : Fin 6) : freeTripleWitnessWeight label ≠ 0 :=
  ne_of_gt (freeTripleWitnessWeight_pos label)

theorem freeTripleWitnessWeight_sum : ∑ label, freeTripleWitnessWeight label = 1 := by
  rw [Fin.sum_univ_six]
  norm_num [freeTripleWitnessWeight]

/-- A chart point at which the free triple is strictly dominating. -/
noncomputable def freeTripleWitnessPoint : DirectionChartPoint 6 where
  mass := freeTripleWitnessMass
  weight := freeTripleWitnessWeight
  mass_pos := freeTripleWitnessMass_pos
  weight_pos := freeTripleWitnessWeight_pos
  weight_sum_one := freeTripleWitnessWeight_sum

/-- **Non-vacuity of the free-triple cell.**  Minors `1959/10`, `2877281/100`
and `8453449619/1000`. -/
theorem freeTripleWitness_freeTriple_posDef :
    (directionChartGap (threeLinesDirection 2) freeTripleWitnessMass
      freeTripleWitnessWeight {2, 4, 5}).PosDef := by
  have hzero := threeLinesChartCoefficient_of_notMem freeTripleWitnessMass
    freeTripleWitnessWeight (show (0 : Fin 6) ∉ ({2, 4, 5} : Finset (Fin 6)) by decide)
  have hone := threeLinesChartCoefficient_of_notMem freeTripleWitnessMass
    freeTripleWitnessWeight (show (1 : Fin 6) ∉ ({2, 4, 5} : Finset (Fin 6)) by decide)
  have htwo := threeLinesChartCoefficient_of_mem freeTripleWitnessMass
    freeTripleWitnessWeight (show (2 : Fin 6) ∈ ({2, 4, 5} : Finset (Fin 6)) by decide)
  have hthree := threeLinesChartCoefficient_of_notMem freeTripleWitnessMass
    freeTripleWitnessWeight (show (3 : Fin 6) ∉ ({2, 4, 5} : Finset (Fin 6)) by decide)
  have hfour := threeLinesChartCoefficient_of_mem freeTripleWitnessMass
    freeTripleWitnessWeight (show (4 : Fin 6) ∈ ({2, 4, 5} : Finset (Fin 6)) by decide)
  have hfive := threeLinesChartCoefficient_of_mem freeTripleWitnessMass
    freeTripleWitnessWeight (show (5 : Fin 6) ∈ ({2, 4, 5} : Finset (Fin 6)) by decide)
  rw [posDef_directionChartGap_threeLines_iff 2 freeTripleWitnessMass
    freeTripleWitnessWeight freeTripleWitnessWeight_ne]
  refine ⟨?_, ?_, ?_⟩
  · rw [threeLinesCornerMinor, hzero, htwo, hfour]
    norm_num [chartExcess, freeTripleWitnessMass, freeTripleWitnessWeight]
  · rw [threeLinesBlockMinor, hzero, hone, htwo, hfour, hfive]
    norm_num [chartExcess, freeTripleWitnessMass, freeTripleWitnessWeight]
  · rw [threeLinesBasisDeterminant, hzero, hone, htwo, hthree, hfour, hfive]
    norm_num [chartExcess, freeTripleWitnessMass, freeTripleWitnessWeight]

/-- The rotation orbit of `{0,1,5}` is `{0,1,5} -> {1,3,4} -> {0,2,3}`. -/
theorem threeLinesRotation_map_zeroOneFive :
    ({0, 1, 5} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {1, 3, 4} := by decide

theorem threeLinesRotation_map_oneThreeFour :
    ({1, 3, 4} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {0, 2, 3} := by decide

theorem threeLinesRotation_map_zeroTwoThree :
    ({0, 2, 3} : Finset (Fin 6)).map threeLinesRotation.toEmbedding = {0, 1, 5} := by decide

/-- **The transport, carried out.**  The strict triple of Part 4 becomes a strict
`{1,3,4}` at the rotated point, with no new arithmetic. -/
theorem canonicalPairFailure_rotated_oneThreeFour_posDef :
    (directionChartGap (threeLinesDirection 2)
      (rotatedThreeLinesChartPoint 2 (by norm_num) canonicalPairFailurePoint).mass
      (rotatedThreeLinesChartPoint 2 (by norm_num) canonicalPairFailurePoint).weight
      {1, 3, 4}).PosDef := by
  have hrotated := (posDef_directionChartGap_threeLines_rotate_iff 2 (by norm_num)
    canonicalPairFailurePoint {0, 1, 5}).mp canonicalPairFailure_zeroOneFive_posDef
  rw [threeLinesRotation_map_zeroOneFive] at hrotated
  exact hrotated

/-! ## Part 7.  The three lines are never candidates

Each line's three atoms span a plane, so at the line's normal the chart gap reads
minus the outside masses.  Exactly SEVENTEEN of the twenty card-three subsets can
ever dominate, and they are the seventeen the Cauchy-Binet determinant law of
Part 2 gives a nonzero bracket. -/

/-- The second coordinate axis, as a probe. -/
def secondAxisProbe : Fin 3 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 0

theorem directionChartGap_threeLines_firstLine_not_posSemidef (slide : ℝ)
    (mass weight : Fin 6 → ℝ) (hweightNe : ∀ label, weight label ≠ 0)
    (hmassThree : 0 < mass 3) (hmassFour : 0 < mass 4) (hmassFive : 0 ≤ mass 5) :
    ¬ (directionChartGap (threeLinesDirection slide) mass weight {0, 1, 2}).PosSemidef := by
  refine not_posSemidef_of_neg_dotProduct (probeVec := verticalProbe) ?_
  rw [dotProduct_directionChartGap_threeLines_mulVec slide mass weight hweightNe,
    threeLinesChartCoefficient_of_notMem mass weight
      (show (3 : Fin 6) ∉ ({0, 1, 2} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_notMem mass weight
      (show (4 : Fin 6) ∉ ({0, 1, 2} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_notMem mass weight
      (show (5 : Fin 6) ∉ ({0, 1, 2} : Finset (Fin 6)) by decide)]
  simp only [verticalProbe]
  nlinarith [sq_nonneg slide, mul_nonneg (sq_nonneg slide) hmassFive]

theorem directionChartGap_threeLines_secondLine_not_posSemidef (slide : ℝ)
    (mass weight : Fin 6 → ℝ) (hweightNe : ∀ label, weight label ≠ 0)
    (hmassOne : 0 < mass 1) (hmassTwo : 0 < mass 2) (hmassFive : 0 < mass 5) :
    ¬ (directionChartGap (threeLinesDirection slide) mass weight {0, 3, 4}).PosSemidef := by
  refine not_posSemidef_of_neg_dotProduct (probeVec := secondAxisProbe) ?_
  rw [dotProduct_directionChartGap_threeLines_mulVec slide mass weight hweightNe,
    threeLinesChartCoefficient_of_notMem mass weight
      (show (1 : Fin 6) ∉ ({0, 3, 4} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_notMem mass weight
      (show (2 : Fin 6) ∉ ({0, 3, 4} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_notMem mass weight
      (show (5 : Fin 6) ∉ ({0, 3, 4} : Finset (Fin 6)) by decide)]
  simp only [secondAxisProbe]
  nlinarith [hmassOne, hmassTwo, hmassFive]

theorem directionChartGap_threeLines_thirdLine_not_posSemidef (slide : ℝ)
    (mass weight : Fin 6 → ℝ) (hweightNe : ∀ label, weight label ≠ 0)
    (hmassZero : 0 < mass 0) (hmassTwo : 0 < mass 2) (hmassFour : 0 < mass 4) :
    ¬ (directionChartGap (threeLinesDirection slide) mass weight {1, 3, 5}).PosSemidef := by
  refine not_posSemidef_of_neg_dotProduct (probeVec := firstAxisProbe) ?_
  rw [dotProduct_directionChartGap_threeLines_mulVec slide mass weight hweightNe,
    threeLinesChartCoefficient_of_notMem mass weight
      (show (0 : Fin 6) ∉ ({1, 3, 5} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_notMem mass weight
      (show (2 : Fin 6) ∉ ({1, 3, 5} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_notMem mass weight
      (show (4 : Fin 6) ∉ ({1, 3, 5} : Finset (Fin 6)) by decide)]
  simp only [firstAxisProbe]
  nlinarith [hmassZero, hmassTwo, hmassFour]

/-! ## Part 8.  The target as polynomial arithmetic

Parts 1 and 2 together turn the obligation into a statement about the signs of
three explicit polynomials in twelve real variables -- the slide, the six masses
and the six weights.  Nothing is weakened: the Sylvester step is an equivalence,
so the reduction runs in both directions. -/

/-- The three closed-form minors of a selection at a chart point are positive. -/
def HasPositiveThreeLinesMinors (slide : ℝ) (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) : Prop :=
  0 < threeLinesCornerMinor (threeLinesChartCoefficient point.mass point.weight selected)
    ∧ 0 < threeLinesBlockMinor (threeLinesChartCoefficient point.mass point.weight selected)
    ∧ 0 < threeLinesBasisDeterminant slide
        (threeLinesChartCoefficient point.mass point.weight selected)

theorem posDef_directionChartGap_iff_hasPositiveThreeLinesMinors (slide : ℝ)
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6)) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight selected).PosDef
      ↔ HasPositiveThreeLinesMinors slide point selected :=
  posDef_directionChartGap_threeLines_iff slide point.mass point.weight
    (fun label => ne_of_gt (point.weight_pos label)) selected

/-- **THE REDUCTION.**  The target obligation is EQUIVALENT to: at every
admissible slide of the fundamental domain and every chart point carrying a
weakly dominating triple, some card-three subset has all three closed-form minors
positive. -/
theorem chartTieFreeThreeLinesFundamentalDomain_iff_minorSigns :
    ChartTieFreeThreeLinesFundamentalDomain
      ↔ ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
          ∀ point : DirectionChartPoint 6,
            (∃ weakSet : Finset (Fin 6), weakSet.card = 3 ∧
              (directionChartGap (threeLinesDirection slide) point.mass point.weight
                weakSet).PosSemidef) →
            ∃ selected : Finset (Fin 6), selected.card = 3 ∧
              HasPositiveThreeLinesMinors slide point selected := by
  constructor
  · intro hdomain slide hadmissible hbound point hweak
    obtain ⟨selected, hcard, hposDef⟩ := hdomain slide hadmissible hbound point hweak
    exact ⟨selected, hcard,
      (posDef_directionChartGap_iff_hasPositiveThreeLinesMinors slide point selected).mp hposDef⟩
  · intro hminors slide hadmissible hbound point hweak
    obtain ⟨selected, hcard, hsigns⟩ := hminors slide hadmissible hbound point hweak
    exact ⟨selected, hcard,
      (posDef_directionChartGap_iff_hasPositiveThreeLinesMinors slide point selected).mpr hsigns⟩

end Gtz
