import Gtz.Design.ThreeLinesDescentPort
import Gtz.Design.ThreeLinesAtlas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The axis law of the three-lines chart

The three dependent lines of the chart are the three COORDINATE PLANES.  The
directions are `v0 = e1`, `v1 = e2`, `v3 = e3` with the joins `v2 = v0 + v1`,
`v4 = v0 + v3` and `v5 = v1 + slide * v3`, so the line `{0,1,2}` lies in the
first two coordinates, the line `{0,3,4}` in the first and third, and the line
`{1,3,5}` in the second and third.

Their normals are therefore the three COORDINATE AXES, which the atlas already
carries as `verticalProbe`, `secondAxisProbe` and `firstAxisProbe`.  Reading the
gap at those three probes collapses the six-term quadratic form to a THREE-TERM
sum each time:

  vertical (third axis)  sees `{3,4,5}` with squared readings `(1, 1, slide^2)`
  second axis            sees `{1,2,5}` with squared readings `(1, 1, 1)`
  first axis             sees `{0,2,4}` with squared readings `(1, 1, 1)`

The three sets seen are exactly the COMPLEMENTS of the three lines.  Each
coordinate label `0`, `1`, `3` is seen by ONE axis and each join label `2`, `4`,
`5` by TWO.  Two consequences follow at once.

**Each line dies at its own axis.**  A line contributes no selected label to the
axis that kills it, so the whole reading is minus a sum of masses.  This
re-derives the three landed exclusions uniformly, in one line of arithmetic each
instead of three separate probe arguments.

**The vertex triple and the free triple are structurally unequal.**  The free
triple `{2,4,5}` meets every axis in TWO labels, so each axis threshold is
challenged by a sum of two excesses.  The vertex triple `{0,1,3}` meets every
axis in ONE label, so each threshold has to be beaten by a single excess.  That
incidence is the structural reason the free triple dominates far more often, and
it is visible without any probe.

Everything here is SIGN-ONLY.  No margin, no slack and no positive constant
appears on the right of any inequality, which is what the stratum demands: the
escape margin of this chart has infimum zero, so no uniform-slack criterion can
survive.
-/

namespace Gtz

open Matrix Finset

/-! ## The three axis readings -/

/-- **The vertical axis reading.**  At the normal of the line `{0,1,2}` the gap
reads the three labels `3`, `4`, `5`, and the slide enters squared. -/
theorem threeLines_verticalReading (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0) (selected : Finset (Fin 6)) :
    verticalProbe ⬝ᵥ (directionChartGap (threeLinesDirection slide) mass weight selected
        *ᵥ verticalProbe)
      = threeLinesChartCoefficient mass weight selected 3
        + threeLinesChartCoefficient mass weight selected 4
        + slide ^ 2 * threeLinesChartCoefficient mass weight selected 5 := by
  rw [dotProduct_directionChartGap_threeLines_mulVec slide mass weight hweightNe]
  norm_num [verticalProbe]
  ring

/-- **The second axis reading.**  At the normal of the line `{0,3,4}` the gap
reads the three labels `1`, `2`, `5`, all with unit weight. -/
theorem threeLines_secondAxisReading (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0) (selected : Finset (Fin 6)) :
    secondAxisProbe ⬝ᵥ (directionChartGap (threeLinesDirection slide) mass weight selected
        *ᵥ secondAxisProbe)
      = threeLinesChartCoefficient mass weight selected 1
        + threeLinesChartCoefficient mass weight selected 2
        + threeLinesChartCoefficient mass weight selected 5 := by
  rw [dotProduct_directionChartGap_threeLines_mulVec slide mass weight hweightNe]
  norm_num [secondAxisProbe]

/-- **The first axis reading.**  At the normal of the line `{1,3,5}` the gap
reads the three labels `0`, `2`, `4`, all with unit weight.  The slide does not
appear. -/
theorem threeLines_firstAxisReading (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0) (selected : Finset (Fin 6)) :
    firstAxisProbe ⬝ᵥ (directionChartGap (threeLinesDirection slide) mass weight selected
        *ᵥ firstAxisProbe)
      = threeLinesChartCoefficient mass weight selected 0
        + threeLinesChartCoefficient mass weight selected 2
        + threeLinesChartCoefficient mass weight selected 4 := by
  rw [dotProduct_directionChartGap_threeLines_mulVec slide mass weight hweightNe]
  norm_num [firstAxisProbe]

/-! ## The probes are nonzero -/

theorem verticalProbe_ne_zero : verticalProbe ≠ 0 := by
  intro hzero
  have := congrFun hzero 2
  norm_num [verticalProbe] at this

theorem secondAxisProbe_ne_zero : secondAxisProbe ≠ 0 := by
  intro hzero
  have := congrFun hzero 1
  norm_num [secondAxisProbe] at this

theorem firstAxisProbe_ne_zero : firstAxisProbe ≠ 0 := by
  intro hzero
  have := congrFun hzero 0
  norm_num [firstAxisProbe] at this

/-! ## The three necessary conditions

A positive definite selection reads strictly positively at every nonzero probe,
so in particular at each of the three axes.  These are three explicit scalar
inequalities in the chart coefficients, and they are sign-only. -/

/-- A positive definite selection clears the vertical axis. -/
theorem threeLines_verticalAxis_pos_of_posDef (slide : ℝ) (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6))
    (hposDef : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      selected).PosDef) :
    0 < threeLinesChartCoefficient point.mass point.weight selected 3
      + threeLinesChartCoefficient point.mass point.weight selected 4
      + slide ^ 2 * threeLinesChartCoefficient point.mass point.weight selected 5 := by
  have hread := threeLines_verticalReading slide point.mass point.weight
    (fun label => ne_of_gt (point.weight_pos label)) selected
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 verticalProbe_ne_zero
  rw [star_trivial, hread] at hpos
  exact hpos

/-- A positive definite selection clears the second axis. -/
theorem threeLines_secondAxis_pos_of_posDef (slide : ℝ) (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6))
    (hposDef : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      selected).PosDef) :
    0 < threeLinesChartCoefficient point.mass point.weight selected 1
      + threeLinesChartCoefficient point.mass point.weight selected 2
      + threeLinesChartCoefficient point.mass point.weight selected 5 := by
  have hread := threeLines_secondAxisReading slide point.mass point.weight
    (fun label => ne_of_gt (point.weight_pos label)) selected
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 secondAxisProbe_ne_zero
  rw [star_trivial, hread] at hpos
  exact hpos

/-- A positive definite selection clears the first axis. -/
theorem threeLines_firstAxis_pos_of_posDef (slide : ℝ) (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6))
    (hposDef : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      selected).PosDef) :
    0 < threeLinesChartCoefficient point.mass point.weight selected 0
      + threeLinesChartCoefficient point.mass point.weight selected 2
      + threeLinesChartCoefficient point.mass point.weight selected 4 := by
  have hread := threeLines_firstAxisReading slide point.mass point.weight
    (fun label => ne_of_gt (point.weight_pos label)) selected
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 firstAxisProbe_ne_zero
  rw [star_trivial, hread] at hpos
  exact hpos

/-! ## Each line dies at its own axis

A line contributes no selected label to the axis that kills it, so the whole
reading collapses to minus a sum of masses. -/

/-- The first line reads minus a mass sum at the vertical axis. -/
theorem threeLines_firstLine_verticalReading (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0) :
    verticalProbe ⬝ᵥ (directionChartGap (threeLinesDirection slide) mass weight {0, 1, 2}
        *ᵥ verticalProbe)
      = -(mass 3) - mass 4 - slide ^ 2 * mass 5 := by
  rw [threeLines_verticalReading slide mass weight hweightNe,
    threeLinesChartCoefficient, threeLinesChartCoefficient, threeLinesChartCoefficient,
    if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  ring

/-- The second line reads minus a mass sum at the second axis. -/
theorem threeLines_secondLine_secondAxisReading (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0) :
    secondAxisProbe ⬝ᵥ (directionChartGap (threeLinesDirection slide) mass weight {0, 3, 4}
        *ᵥ secondAxisProbe)
      = -(mass 1) - mass 2 - mass 5 := by
  rw [threeLines_secondAxisReading slide mass weight hweightNe,
    threeLinesChartCoefficient, threeLinesChartCoefficient, threeLinesChartCoefficient,
    if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  ring

/-- The third line reads minus a mass sum at the first axis. -/
theorem threeLines_thirdLine_firstAxisReading (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0) :
    firstAxisProbe ⬝ᵥ (directionChartGap (threeLinesDirection slide) mass weight {1, 3, 5}
        *ᵥ firstAxisProbe)
      = -(mass 0) - mass 2 - mass 4 := by
  rw [threeLines_firstAxisReading slide mass weight hweightNe,
    threeLinesChartCoefficient, threeLinesChartCoefficient, threeLinesChartCoefficient,
    if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  ring

/-! ## The full selection clears every axis

The landed full-selection law says the gap of `univ` is positive definite, so
every axis threshold is beaten by the whole family.  The escape asks for a
THREE-label subfamily that beats all three, and this is the surplus it has to
redistribute. -/

/-- The whole family clears the vertical axis. -/
theorem threeLines_univ_verticalAxis_pos (slide : ℝ) (point : DirectionChartPoint 6) :
    0 < threeLinesChartCoefficient point.mass point.weight Finset.univ 3
      + threeLinesChartCoefficient point.mass point.weight Finset.univ 4
      + slide ^ 2 * threeLinesChartCoefficient point.mass point.weight Finset.univ 5 :=
  threeLines_verticalAxis_pos_of_posDef slide point Finset.univ
    (posDef_directionChartGap_univ_threeLines slide point)

/-- The whole family clears the second axis. -/
theorem threeLines_univ_secondAxis_pos (slide : ℝ) (point : DirectionChartPoint 6) :
    0 < threeLinesChartCoefficient point.mass point.weight Finset.univ 1
      + threeLinesChartCoefficient point.mass point.weight Finset.univ 2
      + threeLinesChartCoefficient point.mass point.weight Finset.univ 5 :=
  threeLines_secondAxis_pos_of_posDef slide point Finset.univ
    (posDef_directionChartGap_univ_threeLines slide point)

/-- The whole family clears the first axis. -/
theorem threeLines_univ_firstAxis_pos (slide : ℝ) (point : DirectionChartPoint 6) :
    0 < threeLinesChartCoefficient point.mass point.weight Finset.univ 0
      + threeLinesChartCoefficient point.mass point.weight Finset.univ 2
      + threeLinesChartCoefficient point.mass point.weight Finset.univ 4 :=
  threeLines_firstAxis_pos_of_posDef slide point Finset.univ
    (posDef_directionChartGap_univ_threeLines slide point)

/-! ## The bridge to the landed Sylvester criterion

One of the three landed minors is an axis reading, and the other two are not.
That places the axis law exactly: it recovers one third of the criterion for
free and supplies two conditions the criterion never states. -/

/-- **The corner minor IS the first axis reading.**  The landed Sylvester
criterion for this chart tests the corner minor, the block minor and the basis
determinant.  The corner minor is a DIAGONAL entry of the gap, namely its
reading at the normal of the third line.  The vertical and second-axis readings
are the other two diagonal entries and appear in no leading minor. -/
theorem threeLinesCornerMinor_eq_firstAxisReading (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) :
    threeLinesCornerMinor (threeLinesChartCoefficient mass weight selected)
      = threeLinesChartCoefficient mass weight selected 0
        + threeLinesChartCoefficient mass weight selected 2
        + threeLinesChartCoefficient mass weight selected 4 := rfl

/-- **The axis sum.**  Adding the three readings weights each coordinate label
once, each join label twice, and the sliding label by `1 + slide ^ 2`.  That
multiplicity is the incidence of the label in the three axis sets, and it is the
structural statement that the joins are seen twice. -/
theorem threeLines_axisSum_pos_of_posDef (slide : ℝ) (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6))
    (hposDef : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      selected).PosDef) :
    0 < threeLinesChartCoefficient point.mass point.weight selected 0
      + threeLinesChartCoefficient point.mass point.weight selected 1
      + 2 * threeLinesChartCoefficient point.mass point.weight selected 2
      + threeLinesChartCoefficient point.mass point.weight selected 3
      + 2 * threeLinesChartCoefficient point.mass point.weight selected 4
      + (1 + slide ^ 2) * threeLinesChartCoefficient point.mass point.weight selected 5 := by
  have h1 := threeLines_verticalAxis_pos_of_posDef slide point selected hposDef
  have h2 := threeLines_secondAxis_pos_of_posDef slide point selected hposDef
  have h3 := threeLines_firstAxis_pos_of_posDef slide point selected hposDef
  linarith

/-! ## The vertex triple and the free triple are structurally unequal

The free triple meets every axis in two labels, the vertex triple in one.  These
are the six explicit inequalities, and the asymmetry is visible without any
probe. -/

/-- **The vertex triple pays with single excesses.**  Each axis threshold has to
be beaten by ONE excess, because `{0,1,3}` meets each axis set in one label. -/
theorem threeLines_vertexTriple_axis_conditions (slide : ℝ) (point : DirectionChartPoint 6)
    (hposDef : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      {0, 1, 3}).PosDef) :
    point.mass 3 * (1 - point.weight 3) / point.weight 3
        > point.mass 4 + slide ^ 2 * point.mass 5
      ∧ point.mass 1 * (1 - point.weight 1) / point.weight 1
        > point.mass 2 + point.mass 5
      ∧ point.mass 0 * (1 - point.weight 0) / point.weight 0
        > point.mass 2 + point.mass 4 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := threeLines_verticalAxis_pos_of_posDef slide point {0, 1, 3} hposDef
    rw [threeLinesChartCoefficient, threeLinesChartCoefficient, threeLinesChartCoefficient,
      if_pos (by decide), if_neg (by decide), if_neg (by decide), chartExcess] at h
    linarith
  · have h := threeLines_secondAxis_pos_of_posDef slide point {0, 1, 3} hposDef
    rw [threeLinesChartCoefficient, threeLinesChartCoefficient, threeLinesChartCoefficient,
      if_pos (by decide), if_neg (by decide), if_neg (by decide), chartExcess] at h
    linarith
  · have h := threeLines_firstAxis_pos_of_posDef slide point {0, 1, 3} hposDef
    rw [threeLinesChartCoefficient, threeLinesChartCoefficient, threeLinesChartCoefficient,
      if_pos (by decide), if_neg (by decide), if_neg (by decide), chartExcess] at h
    linarith

/-- **The free triple pays with paired excesses.**  Each axis threshold is
challenged by TWO excesses, because `{2,4,5}` meets each axis set in two labels.
The single mass on the right is the one coordinate label that axis sees. -/
theorem threeLines_freeTriple_axis_conditions (slide : ℝ) (point : DirectionChartPoint 6)
    (hposDef : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      {2, 4, 5}).PosDef) :
    point.mass 4 * (1 - point.weight 4) / point.weight 4
        + slide ^ 2 * (point.mass 5 * (1 - point.weight 5) / point.weight 5)
        > point.mass 3
      ∧ point.mass 2 * (1 - point.weight 2) / point.weight 2
        + point.mass 5 * (1 - point.weight 5) / point.weight 5 > point.mass 1
      ∧ point.mass 2 * (1 - point.weight 2) / point.weight 2
        + point.mass 4 * (1 - point.weight 4) / point.weight 4 > point.mass 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := threeLines_verticalAxis_pos_of_posDef slide point {2, 4, 5} hposDef
    rw [threeLinesChartCoefficient, threeLinesChartCoefficient, threeLinesChartCoefficient,
      if_neg (by decide), if_pos (by decide), if_pos (by decide), chartExcess, chartExcess] at h
    linarith
  · have h := threeLines_secondAxis_pos_of_posDef slide point {2, 4, 5} hposDef
    rw [threeLinesChartCoefficient, threeLinesChartCoefficient, threeLinesChartCoefficient,
      if_neg (by decide), if_pos (by decide), if_pos (by decide), chartExcess, chartExcess] at h
    linarith
  · have h := threeLines_firstAxis_pos_of_posDef slide point {2, 4, 5} hposDef
    rw [threeLinesChartCoefficient, threeLinesChartCoefficient, threeLinesChartCoefficient,
      if_neg (by decide), if_pos (by decide), if_pos (by decide), chartExcess, chartExcess] at h
    linarith

end Gtz
