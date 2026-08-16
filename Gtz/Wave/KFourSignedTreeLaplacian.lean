import Gtz.Wave.KFourTreeLaplacian
import Gtz.Design.KFourDescentLadder
import Gtz.Wave.KFourGaugeStarTransportWiring
import Gtz.LinAlg.RankOneForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The chart gap is a signed reduced Laplacian, and the corank-two gauge wall is a
rational variety

Two results carry this module.

**The signed Laplacian law.**  At every selection, the chart gap of a graphic
direction family is the reduced Laplacian of ONE signed edge vector.  The vector
carries the heavy mass `m_c (1 - w_c) / w_c` on the selection and minus the plain
mass off it.  `Gtz.directionChartGap_eq_signedLaplacian` states it for `K4`,
and `Gtz.directionChartGap_eq_sum_signedGapWeight` states the direction-free half
for every size and every direction family.  The landed congruence
`Gtz.directionChartGap_star_eq` needs a basis matrix and covers ONE star.  This
law needs no basis and covers all twenty selections at one time.

The law has an immediate consequence that the campaign has not had before.
Kirchhoff's theorem holds for arbitrary real edge weights, so
`Gtz.det_directionChartGap_eq_kFourMassTreeSum` reads EVERY selection
determinant as the sum over the sixteen spanning trees of a product of three
signed weights.  The landed `Gtz.det_kFourMassMoment_eq_treeSum` is the
all-negative corner of this law.

**The corank-two gauge wall is a rational variety.**  The wall hypothesis of
`Gtz.KFourGaugeStarWallAtlasFires` asks the gap at the canonical gauge star
`{3, 4, 5}` to be positive semidefinite with a two-dimensional kernel.  That pair
of conditions looks like a stratum cut out by inequalities.  It is not.  With
positive masses the wall is EXACTLY three division-free equations, which
`Gtz.KFourGaugeWallEquations` names and `Gtz.kFourGaugeWallEquations_of_corankTwo`
and `Gtz.corankTwo_of_kFourGaugeWallEquations` prove equivalent to it:

  `d3 * m2 = m0 * m1`,  `d4 * m1 = m0 * m2`,  `d5 * m0 = m1 * m2`,

where `d3 = h3 - m0 - m1` and the other two follow the same pattern.  On that
variety `Gtz.smul_kFourGaugeStarGap_of_wall` writes the gap as one explicit outer
product with no square root:

  `(m0 * m1 * m2) • gap = atomMatrix ![m0 * m1, m0 * m2, m1 * m2]`,

and the two kernel directions are the rational vectors `![m2, -m1, 0]` and
`![m2, 0, -m0]`.

**The isotropic cell can never fire on the wall.**  The cell of
`Gtz.posDef_kFourStarGap_of_isotropic` needs a strictly positive slack.
`Gtz.kFourGaugeWall_slack_nonpos` proves that on the wall the slack is never
positive, and `Gtz.kFourGaugeWall_slack_eq_zero_of_massEq` proves that it reaches zero
at `m0 = m1 = m2`.  So the isotropic cell is sharp, and the wall is its
exact boundary.  The proof of the first half is one line of arithmetic: if the
three heavy masses all beat the mass sum, the product of the three strict
inequalities reads `(m0 * m1 * m2) ^ 2 < (m0 * m1 * m2) ^ 2`.

**The wall is inhabited.**  `Gtz.kFourGaugeWallPoint` is a chart point with unit
masses and weights `(1/12, 1/12, 1/12, 1/4, 1/4, 1/4)`.  Its gauge-star gap is
the all-ones matrix.  The registry records that the uniform-WEIGHT gauge wall is
impossible.  This point shows that the uniform-MASS gauge wall is where the wall
lives.
-/

namespace Gtz

open Finset Matrix

/-! ## 1. The signed gap weight, and the direction-free half of the law -/

/-- **The signed edge weight of a selection.**  Each selected label carries its
heavy mass `m_c (1 - w_c) / w_c`.  Each other label carries minus its mass. -/
noncomputable def signedGapWeight {size : ℕ} (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) (label : Fin size) : ℝ :=
  if label ∈ selected then mass label * (1 - weight label) / weight label
  else -(mass label)

/-- **THE CHART GAP IS ONE SIGNED ATOM SUM.**  The gap of a selection is the sum
of every atom matrix against the signed gap weight.  The selection leaves the
statement, and only the sign pattern of one vector remembers it.  Nothing here is
`K4`-specific. -/
theorem directionChartGap_eq_sum_signedGapWeight {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) (hweight : ∀ label ∈ selected, weight label ≠ 0) :
    directionChartGap direction mass weight selected
      = ∑ label, signedGapWeight mass weight selected label
          • atomMatrix (direction label) := by
  classical
  have hswap : ∑ label ∈ selected,
        (mass label / weight label) • atomMatrix (direction label)
      = ∑ label, (if label ∈ selected
          then (mass label / weight label) • atomMatrix (direction label) else 0) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hterm : ∀ label ∈ (Finset.univ : Finset (Fin size)),
      ((if label ∈ selected
          then (mass label / weight label) • atomMatrix (direction label) else 0)
        - mass label • atomMatrix (direction label))
      = signedGapWeight mass weight selected label • atomMatrix (direction label) := by
    intro label _
    by_cases hmem : label ∈ selected
    · have hne : weight label ≠ 0 := hweight label hmem
      simp only [signedGapWeight, hmem, ite_true]
      rw [← sub_smul]
      congr 1
      field_simp
    · simp only [signedGapWeight, hmem, ite_false, zero_sub, ← neg_smul]
  rw [directionChartGap, hswap, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl hterm

/-! ## 2. The signed law at the `K4` chart, and Kirchhoff at every selection -/

/-- **THE SIGNED LAPLACIAN LAW AT THE `K4` CHART.**  At every selection the chart
gap is the reduced Laplacian of ONE signed edge vector.  The landed
`Gtz.sum_smul_atomMatrix_kFourDirection` supplies the Laplacian shape for a free
edge vector.  The new content is the signed gap weight, which removes the
selection from the statement and leaves only a sign pattern. -/
theorem directionChartGap_eq_signedLaplacian (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) (hweight : ∀ label ∈ selected, weight label ≠ 0) :
    directionChartGap kFourDirection mass weight selected
      = Matrix.of
          ![![signedGapWeight mass weight selected 0
                + signedGapWeight mass weight selected 1
                + signedGapWeight mass weight selected 3,
              -signedGapWeight mass weight selected 0,
              -signedGapWeight mass weight selected 1],
            ![-signedGapWeight mass weight selected 0,
              signedGapWeight mass weight selected 0
                + signedGapWeight mass weight selected 2
                + signedGapWeight mass weight selected 4,
              -signedGapWeight mass weight selected 2],
            ![-signedGapWeight mass weight selected 1,
              -signedGapWeight mass weight selected 2,
              signedGapWeight mass weight selected 1
                + signedGapWeight mass weight selected 2
                + signedGapWeight mass weight selected 5]] := by
  rw [directionChartGap_eq_sum_signedGapWeight kFourDirection mass weight selected hweight,
    sum_smul_atomMatrix_kFourDirection]

/-- **KIRCHHOFF AT EVERY SELECTION.**  The chart gap determinant of any selection
is the sixteen-term spanning-tree sum of the signed gap weight.  The landed
`Gtz.det_sum_smul_atomMatrix_kFourDirection` holds at every sign pattern, and the
signed gap weight is the pattern that a selection produces.  The determinant
ledger of the campaign becomes one polynomial with sixteen terms. -/
theorem det_directionChartGap_eq_kFourMassTreeSum (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) (hweight : ∀ label ∈ selected, weight label ≠ 0) :
    (directionChartGap kFourDirection mass weight selected).det
      = kFourMassTreeSum (signedGapWeight mass weight selected) := by
  rw [directionChartGap_eq_sum_signedGapWeight kFourDirection mass weight selected hweight,
    det_sum_smul_atomMatrix_kFourDirection]

/-! ## 4. The heavy mass, and the four vertex-star normal forms -/

/-- The heavy mass of a label: `m_c (1 - w_c) / w_c`. -/
noncomputable def kFourHeavyMass (mass weight : Fin 6 → ℝ) (label : Fin 6) : ℝ :=
  mass label * (1 - weight label) / weight label

theorem signedGapWeight_mem {size : ℕ} (mass weight : Fin size → ℝ)
    {selected : Finset (Fin size)} {label : Fin size} (hmem : label ∈ selected) :
    signedGapWeight mass weight selected label
      = mass label * (1 - weight label) / weight label := by
  simp only [signedGapWeight, hmem, ite_true]

theorem signedGapWeight_not_mem {size : ℕ} (mass weight : Fin size → ℝ)
    {selected : Finset (Fin size)} {label : Fin size} (hmem : label ∉ selected) :
    signedGapWeight mass weight selected label = -(mass label) := by
  simp only [signedGapWeight, hmem, ite_false]

/-- The canonical gauge star `{3, 4, 5}` in normal form.  The three directions of
that star are the coordinate axes, so no basis matrix is needed and the chart gap
IS the tree-coordinate gap. -/
noncomputable def kFourGaugeStarGap (mass weight : Fin 6 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of
    ![![kFourHeavyMass mass weight 3 - mass 0 - mass 1, mass 0, mass 1],
      ![mass 0, kFourHeavyMass mass weight 4 - mass 0 - mass 2, mass 2],
      ![mass 1, mass 2, kFourHeavyMass mass weight 5 - mass 1 - mass 2]]

theorem signedGapWeight_gaugeStar (mass weight : Fin 6 → ℝ) (label : Fin 6) :
    signedGapWeight mass weight {3, 4, 5} label
      = ![-(mass 0), -(mass 1), -(mass 2), kFourHeavyMass mass weight 3,
          kFourHeavyMass mass weight 4, kFourHeavyMass mass weight 5] label := by
  fin_cases label
  · rw [signedGapWeight_not_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_not_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_not_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_mem mass weight (by decide)]; rfl

/-- **THE GAUGE STAR NEEDS NO CONGRUENCE.**  At `{3, 4, 5}` the chart gap already
IS the loaded triangle: the diagonal carries the heavy mass of each star edge less
the two opposite triangle masses that meet it, and the off-diagonal carries the
opposite triangle masses.  The landed `Gtz.directionChartGap_star_eq` needs a
determinant-one basis matrix at `{0, 1, 3}`.  Here the basis is the identity. -/
theorem directionChartGap_gaugeStar_eq (mass weight : Fin 6 → ℝ)
    (hweight3 : weight 3 ≠ 0) (hweight4 : weight 4 ≠ 0) (hweight5 : weight 5 ≠ 0) :
    directionChartGap kFourDirection mass weight {3, 4, 5}
      = kFourGaugeStarGap mass weight := by
  have hweight : ∀ label ∈ ({3, 4, 5} : Finset (Fin 6)), weight label ≠ 0 := by
    intro label hmem
    fin_cases label <;> first
      | exact absurd hmem (by decide)
      | assumption
  rw [directionChartGap_eq_sum_signedGapWeight kFourDirection mass weight _ hweight,
    sum_smul_atomMatrix_kFourDirection]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourGaugeStarGap, signedGapWeight_gaugeStar] <;> ring

/-- The star at vertex `1`, in chart coordinates. -/
noncomputable def kFourVertexOneStarGap (mass weight : Fin 6 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of
    ![![kFourHeavyMass mass weight 0 + kFourHeavyMass mass weight 1
          + kFourHeavyMass mass weight 3,
        -kFourHeavyMass mass weight 0, -kFourHeavyMass mass weight 1],
      ![-kFourHeavyMass mass weight 0,
        kFourHeavyMass mass weight 0 - mass 2 - mass 4, mass 2],
      ![-kFourHeavyMass mass weight 1, mass 2,
        kFourHeavyMass mass weight 1 - mass 2 - mass 5]]

/-- The star at vertex `2`, in chart coordinates. -/
noncomputable def kFourVertexTwoStarGap (mass weight : Fin 6 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of
    ![![kFourHeavyMass mass weight 0 - mass 1 - mass 3,
        -kFourHeavyMass mass weight 0, mass 1],
      ![-kFourHeavyMass mass weight 0,
        kFourHeavyMass mass weight 0 + kFourHeavyMass mass weight 2
          + kFourHeavyMass mass weight 4,
        -kFourHeavyMass mass weight 2],
      ![mass 1, -kFourHeavyMass mass weight 2,
        kFourHeavyMass mass weight 2 - mass 1 - mass 5]]

/-- The star at vertex `3`, in chart coordinates. -/
noncomputable def kFourVertexThreeStarGap (mass weight : Fin 6 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of
    ![![kFourHeavyMass mass weight 1 - mass 0 - mass 3, mass 0,
        -kFourHeavyMass mass weight 1],
      ![mass 0, kFourHeavyMass mass weight 2 - mass 0 - mass 4,
        -kFourHeavyMass mass weight 2],
      ![-kFourHeavyMass mass weight 1, -kFourHeavyMass mass weight 2,
        kFourHeavyMass mass weight 1 + kFourHeavyMass mass weight 2
          + kFourHeavyMass mass weight 5]]

theorem signedGapWeight_vertexOneStar (mass weight : Fin 6 → ℝ) (label : Fin 6) :
    signedGapWeight mass weight {0, 1, 3} label
      = ![kFourHeavyMass mass weight 0, kFourHeavyMass mass weight 1, -(mass 2),
          kFourHeavyMass mass weight 3, -(mass 4), -(mass 5)] label := by
  fin_cases label
  · rw [signedGapWeight_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_not_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_not_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_not_mem mass weight (by decide)]; rfl

theorem signedGapWeight_vertexTwoStar (mass weight : Fin 6 → ℝ) (label : Fin 6) :
    signedGapWeight mass weight {0, 2, 4} label
      = ![kFourHeavyMass mass weight 0, -(mass 1), kFourHeavyMass mass weight 2,
          -(mass 3), kFourHeavyMass mass weight 4, -(mass 5)] label := by
  fin_cases label
  · rw [signedGapWeight_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_not_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_not_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_not_mem mass weight (by decide)]; rfl

theorem signedGapWeight_vertexThreeStar (mass weight : Fin 6 → ℝ) (label : Fin 6) :
    signedGapWeight mass weight {1, 2, 5} label
      = ![-(mass 0), kFourHeavyMass mass weight 1, kFourHeavyMass mass weight 2,
          -(mass 3), -(mass 4), kFourHeavyMass mass weight 5] label := by
  fin_cases label
  · rw [signedGapWeight_not_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_not_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_not_mem mass weight (by decide)]; rfl
  · rw [signedGapWeight_mem mass weight (by decide)]; rfl

/-- The vertex-`1` star gap in closed form.  Note the free leading minor: the
corner entry is a sum of three heavy masses and is positive at every chart
point. -/
theorem directionChartGap_vertexOneStar_eq (mass weight : Fin 6 → ℝ)
    (hweight0 : weight 0 ≠ 0) (hweight1 : weight 1 ≠ 0) (hweight3 : weight 3 ≠ 0) :
    directionChartGap kFourDirection mass weight {0, 1, 3}
      = kFourVertexOneStarGap mass weight := by
  have hweight : ∀ label ∈ ({0, 1, 3} : Finset (Fin 6)), weight label ≠ 0 := by
    intro label hmem
    fin_cases label <;> first
      | exact absurd hmem (by decide)
      | assumption
  rw [directionChartGap_eq_sum_signedGapWeight kFourDirection mass weight _ hweight,
    sum_smul_atomMatrix_kFourDirection]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourVertexOneStarGap, signedGapWeight_vertexOneStar] <;>
    ring

theorem directionChartGap_vertexTwoStar_eq (mass weight : Fin 6 → ℝ)
    (hweight0 : weight 0 ≠ 0) (hweight2 : weight 2 ≠ 0) (hweight4 : weight 4 ≠ 0) :
    directionChartGap kFourDirection mass weight {0, 2, 4}
      = kFourVertexTwoStarGap mass weight := by
  have hweight : ∀ label ∈ ({0, 2, 4} : Finset (Fin 6)), weight label ≠ 0 := by
    intro label hmem
    fin_cases label <;> first
      | exact absurd hmem (by decide)
      | assumption
  rw [directionChartGap_eq_sum_signedGapWeight kFourDirection mass weight _ hweight,
    sum_smul_atomMatrix_kFourDirection]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourVertexTwoStarGap, signedGapWeight_vertexTwoStar] <;>
    ring

theorem directionChartGap_vertexThreeStar_eq (mass weight : Fin 6 → ℝ)
    (hweight1 : weight 1 ≠ 0) (hweight2 : weight 2 ≠ 0) (hweight5 : weight 5 ≠ 0) :
    directionChartGap kFourDirection mass weight {1, 2, 5}
      = kFourVertexThreeStarGap mass weight := by
  have hweight : ∀ label ∈ ({1, 2, 5} : Finset (Fin 6)), weight label ≠ 0 := by
    intro label hmem
    fin_cases label <;> first
      | exact absurd hmem (by decide)
      | assumption
  rw [directionChartGap_eq_sum_signedGapWeight kFourDirection mass weight _ hweight,
    sum_smul_atomMatrix_kFourDirection]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourVertexThreeStarGap, signedGapWeight_vertexThreeStar] <;>
    ring

/-! ## 5. Two independent kernel directions kill every principal minor -/

/-- **THE ELIMINATION ENGINE.**  Take two rows of a symmetric three-by-three
matrix and a vector in the kernel.  If the principal minor of those two rows is
nonzero, the kernel is at most one-dimensional.  The statement below is pure
scalar algebra, and each of the three principal minors is one instance of it. -/
theorem principalMinor_eq_zero_of_kernelPair
    {diagOne diagTwo edgeOne edgeTwo edgeThree : ℝ}
    {firstOne firstTwo firstThree secondOne secondTwo secondThree : ℝ}
    (hfirstRowOne : diagOne * firstOne + edgeOne * firstTwo + edgeTwo * firstThree = 0)
    (hfirstRowTwo : edgeOne * firstOne + diagTwo * firstTwo + edgeThree * firstThree = 0)
    (hsecondRowOne :
      diagOne * secondOne + edgeOne * secondTwo + edgeTwo * secondThree = 0)
    (hsecondRowTwo :
      edgeOne * secondOne + diagTwo * secondTwo + edgeThree * secondThree = 0)
    (hfirstNe : ¬ (firstOne = 0 ∧ firstTwo = 0 ∧ firstThree = 0))
    (hindependent : ∀ scale : ℝ,
      ¬ (secondOne = scale * firstOne ∧ secondTwo = scale * firstTwo
        ∧ secondThree = scale * firstThree)) :
    diagOne * diagTwo - edgeOne ^ 2 = 0 := by
  by_contra hminor
  set minor : ℝ := diagOne * diagTwo - edgeOne ^ 2 with hminorDef
  -- The combination `secondThree • first - firstThree • second` kills the third slot.
  have hcombOne : minor * (secondThree * firstOne - firstThree * secondOne) = 0 := by
    have := hfirstRowOne
    linear_combination (secondThree * diagTwo) * hfirstRowOne
      - (secondThree * edgeOne) * hfirstRowTwo
      - (firstThree * diagTwo) * hsecondRowOne
      + (firstThree * edgeOne) * hsecondRowTwo
  have hcombTwo : minor * (secondThree * firstTwo - firstThree * secondTwo) = 0 := by
    linear_combination (secondThree * diagOne) * hfirstRowTwo
      - (secondThree * edgeOne) * hfirstRowOne
      - (firstThree * diagOne) * hsecondRowTwo
      + (firstThree * edgeOne) * hsecondRowOne
  have hone : secondThree * firstOne - firstThree * secondOne = 0 := by
    rcases mul_eq_zero.mp hcombOne with h | h
    · exact absurd h hminor
    · exact h
  have htwo : secondThree * firstTwo - firstThree * secondTwo = 0 := by
    rcases mul_eq_zero.mp hcombTwo with h | h
    · exact absurd h hminor
    · exact h
  by_cases hthird : firstThree = 0
  · -- The first kernel vector lies in the two eliminated slots.
    by_cases hsecondThird : secondThree = 0
    · -- Both kernel vectors sit in the plane, and the minor makes the plane free.
      have hfirstOne : minor * firstOne = 0 := by
        linear_combination diagTwo * hfirstRowOne - edgeOne * hfirstRowTwo
          - (edgeTwo * diagTwo - edgeOne * edgeThree) * hthird
      have hfirstTwo : minor * firstTwo = 0 := by
        linear_combination diagOne * hfirstRowTwo - edgeOne * hfirstRowOne
          - (edgeThree * diagOne - edgeOne * edgeTwo) * hthird
      refine hfirstNe ⟨?_, ?_, hthird⟩
      · rcases mul_eq_zero.mp hfirstOne with h | h
        · exact absurd h hminor
        · exact h
      · rcases mul_eq_zero.mp hfirstTwo with h | h
        · exact absurd h hminor
        · exact h
    · -- The second vector has a live third slot, and it forces the first to vanish.
      have hfirstOne : firstOne = 0 := by
        have hprod : secondThree * firstOne = 0 := by
          rw [hthird] at hone; linarith [hone]
        rcases mul_eq_zero.mp hprod with h | h
        · exact absurd h hsecondThird
        · exact h
      have hfirstTwo : firstTwo = 0 := by
        have hprod : secondThree * firstTwo = 0 := by
          rw [hthird] at htwo; linarith [htwo]
        rcases mul_eq_zero.mp hprod with h | h
        · exact absurd h hsecondThird
        · exact h
      exact hfirstNe ⟨hfirstOne, hfirstTwo, hthird⟩
  · -- The first vector has a live third slot, and the second is proportional to it.
    refine hindependent (secondThree / firstThree) ⟨?_, ?_, ?_⟩
    · field_simp
      linarith [hone]
    · field_simp
      linarith [htwo]
    · field_simp

/-! ## 6. The corank-two gauge wall is a rational variety -/

/-- **THE THREE WALL EQUATIONS.**  Division-free, and each one couples one star
diagonal with two opposite triangle masses. -/
def KFourGaugeWallEquations (mass weight : Fin 6 → ℝ) : Prop :=
  (kFourHeavyMass mass weight 3 - mass 0 - mass 1) * mass 2 = mass 0 * mass 1
    ∧ (kFourHeavyMass mass weight 4 - mass 0 - mass 2) * mass 1 = mass 0 * mass 2
    ∧ (kFourHeavyMass mass weight 5 - mass 1 - mass 2) * mass 0 = mass 1 * mass 2

theorem kFourGaugeStarGap_apply_row (mass weight : Fin 6 → ℝ) (probe : Fin 3 → ℝ)
    (hkernel : kFourGaugeStarGap mass weight *ᵥ probe = 0) :
    (kFourHeavyMass mass weight 3 - mass 0 - mass 1) * probe 0
        + mass 0 * probe 1 + mass 1 * probe 2 = 0
      ∧ mass 0 * probe 0
        + (kFourHeavyMass mass weight 4 - mass 0 - mass 2) * probe 1
        + mass 2 * probe 2 = 0
      ∧ mass 1 * probe 0 + mass 2 * probe 1
        + (kFourHeavyMass mass weight 5 - mass 1 - mass 2) * probe 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := congrFun hkernel 0
    simpa [kFourGaugeStarGap, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  · have h := congrFun hkernel 1
    simpa [kFourGaugeStarGap, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  · have h := congrFun hkernel 2
    simpa [kFourGaugeStarGap, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h

/-- **THE WALL IS CUT OUT BY THREE EQUATIONS.**  A positive semidefinite gauge-star
gap with two independent kernel directions satisfies the three division-free wall
equations.  Positive masses are the only extra input. -/
theorem kFourGaugeWallEquations_of_corankTwo (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label)
    (hpsd : (kFourGaugeStarGap mass weight).PosSemidef)
    (first second : Fin 3 → ℝ) (hfirstNe : first ≠ 0)
    (hfirstKernel : kFourGaugeStarGap mass weight *ᵥ first = 0)
    (hsecondKernel : kFourGaugeStarGap mass weight *ᵥ second = 0)
    (hindependent : ¬ ∃ scale : ℝ, second = scale • first) :
    KFourGaugeWallEquations mass weight := by
  obtain ⟨hfirstOne, hfirstTwo, hfirstThree⟩ :=
    kFourGaugeStarGap_apply_row mass weight first hfirstKernel
  obtain ⟨hsecondOne, hsecondTwo, hsecondThree⟩ :=
    kFourGaugeStarGap_apply_row mass weight second hsecondKernel
  set diagThree : ℝ := kFourHeavyMass mass weight 3 - mass 0 - mass 1 with hdiagThree
  set diagFour : ℝ := kFourHeavyMass mass weight 4 - mass 0 - mass 2 with hdiagFour
  set diagFive : ℝ := kFourHeavyMass mass weight 5 - mass 1 - mass 2 with hdiagFive
  have hnotAllZero : ¬ (first 0 = 0 ∧ first 1 = 0 ∧ first 2 = 0) := by
    rintro ⟨ha, hb, hc⟩
    refine hfirstNe ?_
    funext slot
    fin_cases slot <;> simpa using ‹_›
  have hindep : ∀ scale : ℝ,
      ¬ (second 0 = scale * first 0 ∧ second 1 = scale * first 1
        ∧ second 2 = scale * first 2) := by
    intro scale ⟨ha, hb, hc⟩
    refine hindependent ⟨scale, ?_⟩
    funext slot
    fin_cases slot <;> simpa using ‹_›
  -- The three principal minors of the loaded triangle vanish.
  have hminorThreeFour : diagThree * diagFour - mass 0 ^ 2 = 0 :=
    principalMinor_eq_zero_of_kernelPair
      (diagOne := diagThree) (diagTwo := diagFour) (edgeOne := mass 0)
      (edgeTwo := mass 1) (edgeThree := mass 2)
      (firstOne := first 0) (firstTwo := first 1) (firstThree := first 2)
      (secondOne := second 0) (secondTwo := second 1) (secondThree := second 2)
      (by linarith [hfirstOne]) (by linarith [hfirstTwo])
      (by linarith [hsecondOne]) (by linarith [hsecondTwo])
      hnotAllZero hindep
  have hminorThreeFive : diagThree * diagFive - mass 1 ^ 2 = 0 :=
    principalMinor_eq_zero_of_kernelPair
      (diagOne := diagThree) (diagTwo := diagFive) (edgeOne := mass 1)
      (edgeTwo := mass 0) (edgeThree := mass 2)
      (firstOne := first 0) (firstTwo := first 2) (firstThree := first 1)
      (secondOne := second 0) (secondTwo := second 2) (secondThree := second 1)
      (by linarith [hfirstOne]) (by linarith [hfirstThree])
      (by linarith [hsecondOne]) (by linarith [hsecondThree])
      (by rintro ⟨ha, hb, hc⟩; exact hnotAllZero ⟨ha, hc, hb⟩)
      (by
        intro scale ⟨ha, hb, hc⟩
        exact hindep scale ⟨ha, hc, hb⟩)
  have hminorFourFive : diagFour * diagFive - mass 2 ^ 2 = 0 :=
    principalMinor_eq_zero_of_kernelPair
      (diagOne := diagFour) (diagTwo := diagFive) (edgeOne := mass 2)
      (edgeTwo := mass 0) (edgeThree := mass 1)
      (firstOne := first 1) (firstTwo := first 2) (firstThree := first 0)
      (secondOne := second 1) (secondTwo := second 2) (secondThree := second 0)
      (by linarith [hfirstTwo]) (by linarith [hfirstThree])
      (by linarith [hsecondTwo]) (by linarith [hsecondThree])
      (by rintro ⟨ha, hb, hc⟩; exact hnotAllZero ⟨hc, ha, hb⟩)
      (by
        intro scale ⟨ha, hb, hc⟩
        exact hindep scale ⟨hc, ha, hb⟩)
  -- Positive semidefiniteness makes each diagonal entry nonnegative.
  have hdiagThreeNonneg : 0 ≤ diagThree := by
    have h := hpsd.diag_nonneg (i := (0 : Fin 3))
    simpa [kFourGaugeStarGap, hdiagThree] using h
  have hdiagFourNonneg : 0 ≤ diagFour := by
    have h := hpsd.diag_nonneg (i := (1 : Fin 3))
    simpa [kFourGaugeStarGap, hdiagFour] using h
  have hdiagFiveNonneg : 0 ≤ diagFive := by
    have h := hpsd.diag_nonneg (i := (2 : Fin 3))
    simpa [kFourGaugeStarGap, hdiagFive] using h
  have hzero := hmass 0
  have hone := hmass 1
  have htwo := hmass 2
  -- No diagonal entry can vanish, because every off-diagonal mass is positive.
  have hdiagThreePos : 0 < diagThree := by
    rcases hdiagThreeNonneg.lt_or_eq with h | h
    · exact h
    · exfalso; nlinarith [hminorThreeFour]
  have hdiagFourPos : 0 < diagFour := by
    rcases hdiagFourNonneg.lt_or_eq with h | h
    · exact h
    · exfalso; nlinarith [hminorThreeFour]
  have hdiagFivePos : 0 < diagFive := by
    rcases hdiagFiveNonneg.lt_or_eq with h | h
    · exact h
    · exfalso; nlinarith [hminorThreeFive]
  -- The product of the three diagonal entries is the product of the three masses.
  have hsquare : (diagThree * diagFour * diagFive) ^ 2
      = (mass 0 * mass 1 * mass 2) ^ 2 := by
    linear_combination (diagThree * diagFive * (diagFour * diagFive)) * hminorThreeFour
      + (mass 0 ^ 2 * (diagFour * diagFive)) * hminorThreeFive
      + (mass 0 ^ 2 * mass 1 ^ 2) * hminorFourFive
  have hproduct : diagThree * diagFour * diagFive = mass 0 * mass 1 * mass 2 := by
    have hfactor : (diagThree * diagFour * diagFive - mass 0 * mass 1 * mass 2)
        * (diagThree * diagFour * diagFive + mass 0 * mass 1 * mass 2) = 0 := by
      linear_combination hsquare
    rcases mul_eq_zero.mp hfactor with h | h
    · linarith
    · exfalso
      nlinarith [mul_pos (mul_pos hdiagThreePos hdiagFourPos) hdiagFivePos,
        mul_pos (mul_pos hzero hone) htwo]
  refine ⟨?_, ?_, ?_⟩
  · have hkey : mass 0 * mass 1 * (diagThree * mass 2 - mass 0 * mass 1) = 0 := by
      linear_combination (-diagThree) * hproduct
        + (diagThree * diagFive) * hminorThreeFour + (mass 0 ^ 2) * hminorThreeFive
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h (ne_of_gt (mul_pos hzero hone))
    · linarith
  · have hkey : mass 0 * mass 2 * (diagFour * mass 1 - mass 0 * mass 2) = 0 := by
      linear_combination (-diagFour) * hproduct
        + (diagFour * diagFive) * hminorThreeFour + (mass 0 ^ 2) * hminorFourFive
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h (ne_of_gt (mul_pos hzero htwo))
    · linarith
  · have hkey : mass 1 * mass 2 * (diagFive * mass 0 - mass 1 * mass 2) = 0 := by
      linear_combination (-diagFive) * hproduct
        + (diagFour * diagFive) * hminorThreeFive + (mass 1 ^ 2) * hminorFourFive
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h (ne_of_gt (mul_pos hone htwo))
    · linarith

/-! ## 7. The wall in closed form: one outer product, two rational kernel rays -/

/-- The rational axis of the wall.  On the wall the gauge-star gap is a positive
multiple of the atom matrix of this vector. -/
noncomputable def kFourGaugeWallAxis (mass : Fin 6 → ℝ) : Fin 3 → ℝ :=
  ![mass 0 * mass 1, mass 0 * mass 2, mass 1 * mass 2]

/-- **THE WALL IN CLOSED FORM.**  No square root and no division. -/
theorem smul_kFourGaugeStarGap_of_wall (mass weight : Fin 6 → ℝ)
    (hwall : KFourGaugeWallEquations mass weight) :
    (mass 0 * mass 1 * mass 2) • kFourGaugeStarGap mass weight
      = atomMatrix (kFourGaugeWallAxis mass) := by
  obtain ⟨hthree, hfour, hfive⟩ := hwall
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourGaugeStarGap, kFourGaugeWallAxis, atomMatrix, Matrix.vecMulVec_apply]
  · linear_combination (mass 0 * mass 1) * hthree
  · ring
  · ring
  · ring
  · linear_combination (mass 0 * mass 2) * hfour
  · ring
  · ring
  · ring
  · linear_combination (mass 1 * mass 2) * hfive

/-- On the wall the gauge-star gap is positive semidefinite.  No inequality is
needed beyond positive masses. -/
theorem posSemidef_kFourGaugeStarGap_of_wall (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label)
    (hwall : KFourGaugeWallEquations mass weight) :
    (kFourGaugeStarGap mass weight).PosSemidef := by
  have hscale : 0 < mass 0 * mass 1 * mass 2 :=
    mul_pos (mul_pos (hmass 0) (hmass 1)) (hmass 2)
  have hform : kFourGaugeStarGap mass weight
      = (mass 0 * mass 1 * mass 2)⁻¹ • atomMatrix (kFourGaugeWallAxis mass) := by
    rw [← smul_kFourGaugeStarGap_of_wall mass weight hwall, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hscale), one_smul]
  rw [hform]
  exact posSemidef_smul_atomMatrix (le_of_lt (inv_pos.mpr hscale)) _

/-- The first rational kernel ray of the wall. -/
theorem kFourGaugeStarGap_mulVec_kernelOne (mass weight : Fin 6 → ℝ)
    (hwall : KFourGaugeWallEquations mass weight) :
    kFourGaugeStarGap mass weight *ᵥ ![mass 2, -(mass 1), 0] = 0 := by
  obtain ⟨hthree, hfour, _⟩ := hwall
  funext slot
  fin_cases slot <;>
    simp [kFourGaugeStarGap, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · linear_combination hthree
  · linear_combination -hfour
  · ring

/-- The second rational kernel ray of the wall. -/
theorem kFourGaugeStarGap_mulVec_kernelTwo (mass weight : Fin 6 → ℝ)
    (hwall : KFourGaugeWallEquations mass weight) :
    kFourGaugeStarGap mass weight *ᵥ ![mass 2, 0, -(mass 0)] = 0 := by
  obtain ⟨hthree, _, hfive⟩ := hwall
  funext slot
  fin_cases slot <;>
    simp [kFourGaugeStarGap, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · linear_combination hthree
  · ring
  · linear_combination -hfive

/-- The two rays are independent.  Their second and third slots make a
determinant `mass 0 * mass 1`, which is positive. -/
theorem kFourGaugeWallKernel_independent (mass : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) :
    ¬ ∃ scale : ℝ,
      (![mass 2, 0, -(mass 0)] : Fin 3 → ℝ) = scale • ![mass 2, -(mass 1), 0] := by
  rintro ⟨scale, hscale⟩
  have hthird := congrFun hscale 2
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply,
    smul_eq_mul, mul_zero, neg_eq_zero] at hthird
  exact absurd hthird (hmass 0).ne'

/-- **THE CONVERSE HALF.**  The three equations put the gauge-star gap exactly on
the corank-two wall: positive semidefinite, with two independent rational kernel
rays. -/
theorem corankTwo_of_kFourGaugeWallEquations (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label)
    (hwall : KFourGaugeWallEquations mass weight) :
    (kFourGaugeStarGap mass weight).PosSemidef
      ∧ kFourGaugeStarGap mass weight *ᵥ ![mass 2, -(mass 1), 0] = 0
      ∧ kFourGaugeStarGap mass weight *ᵥ ![mass 2, 0, -(mass 0)] = 0
      ∧ ¬ ∃ scale : ℝ,
        (![mass 2, 0, -(mass 0)] : Fin 3 → ℝ) = scale • ![mass 2, -(mass 1), 0] :=
  ⟨posSemidef_kFourGaugeStarGap_of_wall mass weight hmass hwall,
    kFourGaugeStarGap_mulVec_kernelOne mass weight hwall,
    kFourGaugeStarGap_mulVec_kernelTwo mass weight hwall,
    kFourGaugeWallKernel_independent mass hmass⟩

/-- On the wall the gauge-star gap is singular.  The signed tree sum of the wall
weights is zero. -/
theorem det_kFourGaugeStarGap_of_wall (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label)
    (hwall : KFourGaugeWallEquations mass weight) :
    (kFourGaugeStarGap mass weight).det = 0 := by
  have hscale : 0 < mass 0 * mass 1 * mass 2 :=
    mul_pos (mul_pos (hmass 0) (hmass 1)) (hmass 2)
  have hform : kFourGaugeStarGap mass weight
      = (mass 0 * mass 1 * mass 2)⁻¹ • atomMatrix (kFourGaugeWallAxis mass) := by
    rw [← smul_kFourGaugeStarGap_of_wall mass weight hwall, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hscale), one_smul]
  rw [hform, Matrix.det_smul]
  have hatom : (atomMatrix (kFourGaugeWallAxis mass)).det = 0 := by
    simp [atomMatrix, Matrix.vecMulVec_apply, Matrix.det_fin_three]
    ring
  rw [hatom, mul_zero]

/-! ## 8. The isotropic cell is sharp, and the wall is its exact boundary -/

/-- The gauge-star analogue of `Gtz.starIsotropicSlack`: the smallest heavy star
mass, less the total mass of the opposite triangle. -/
noncomputable def kFourGaugeStarSlack (mass weight : Fin 6 → ℝ) : ℝ :=
  min (kFourHeavyMass mass weight 3)
      (min (kFourHeavyMass mass weight 4) (kFourHeavyMass mass weight 5))
    - (mass 0 + mass 1 + mass 2)

/-- **THE ELEMENTARY PIGEONHOLE.**  Three positive reals cannot all have a product
of the other two strictly above their own square.  Multiplying the three strict
inequalities gives `(m0 * m1 * m2) ^ 2 < (m0 * m1 * m2) ^ 2`. -/
theorem exists_massSquare_ge (mass : Fin 6 → ℝ) (hmass : ∀ label, 0 < mass label) :
    mass 0 * mass 1 ≤ mass 2 ^ 2 ∨ mass 0 * mass 2 ≤ mass 1 ^ 2
      ∨ mass 1 * mass 2 ≤ mass 0 ^ 2 := by
  by_contra hcontra
  simp only [not_or, not_le] at hcontra
  obtain ⟨hone, htwo, hthree⟩ := hcontra
  have hzero := hmass 0
  have hfirst := hmass 1
  have hsecond := hmass 2
  nlinarith [hone, htwo, hthree, mul_pos hzero hfirst, mul_pos hfirst hsecond,
    mul_pos hzero hsecond]

/-- **THE ISOTROPIC CELL NEVER FIRES ON THE WALL.**  The cell of
`Gtz.posDef_kFourStarGap_of_isotropic` needs a strictly positive slack.  On the
corank-two gauge wall the slack is never positive.  So the cell and the wall are
disjoint, and the wall is exactly where the cell stops. -/
theorem kFourGaugeWall_slack_nonpos (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label)
    (hwall : KFourGaugeWallEquations mass weight) :
    kFourGaugeStarSlack mass weight ≤ 0 := by
  obtain ⟨hthree, hfour, hfive⟩ := hwall
  have hzero := hmass 0
  have hone := hmass 1
  have htwo := hmass 2
  rw [kFourGaugeStarSlack, sub_nonpos]
  rcases exists_massSquare_ge mass hmass with h | h | h
  · refine le_trans (min_le_left _ _) ?_
    nlinarith [hthree]
  · refine le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) ?_
    nlinarith [hfour]
  · refine le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) ?_
    nlinarith [hfive]

/-- The wall difference of two heavy star masses, in division-free form. -/
theorem kFourGaugeWall_heavy_sub (mass weight : Fin 6 → ℝ)
    (hwall : KFourGaugeWallEquations mass weight) :
    (kFourHeavyMass mass weight 3 - kFourHeavyMass mass weight 4) * (mass 1 * mass 2)
      = (mass 1 - mass 2) * (mass 0 * (mass 1 + mass 2) + mass 1 * mass 2) := by
  obtain ⟨hthree, hfour, _⟩ := hwall
  linear_combination mass 1 * hthree - mass 2 * hfour

/-- **THE ISOTROPIC POINT OF THE WALL.**  On the wall the three heavy star masses
agree exactly when the three opposite triangle masses agree. -/
theorem kFourGaugeWall_heavyEq_iff_massEq (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label)
    (hwall : KFourGaugeWallEquations mass weight) :
    kFourHeavyMass mass weight 3 = kFourHeavyMass mass weight 4 ↔ mass 1 = mass 2 := by
  have hkey := kFourGaugeWall_heavy_sub mass weight hwall
  have hone := hmass 1
  have htwo := hmass 2
  have hzero := hmass 0
  constructor
  · intro heq
    rw [heq, sub_self, zero_mul] at hkey
    have hpos : 0 < mass 0 * (mass 1 + mass 2) + mass 1 * mass 2 := by
      have := mul_pos hzero (add_pos hone htwo)
      have := mul_pos hone htwo
      linarith
    rcases mul_eq_zero.mp hkey.symm with h | h
    · linarith
    · exact absurd h (ne_of_gt hpos)
  · intro heq
    rw [heq, sub_self, zero_mul] at hkey
    have hpos : 0 < mass 2 * mass 2 := mul_pos htwo htwo
    rcases mul_eq_zero.mp hkey with h | h
    · linarith
    · exact absurd h (ne_of_gt hpos)

/-- **THE SLACK REACHES ZERO EXACTLY AT THE SYMMETRIC POINT.**  On the wall the
slack vanishes when the three opposite triangle masses agree. -/
theorem kFourGaugeWall_slack_eq_zero_of_massEq (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label)
    (hwall : KFourGaugeWallEquations mass weight)
    (hsymOne : mass 0 = mass 1) (hsymTwo : mass 1 = mass 2) :
    kFourGaugeStarSlack mass weight = 0 := by
  obtain ⟨hthree, hfour, hfive⟩ := hwall
  have hzero := hmass 0
  have hone := hmass 1
  have htwo := hmass 2
  have hheavyThree : kFourHeavyMass mass weight 3 = mass 0 + mass 1 + mass 2 := by
    have hne : mass 2 ≠ 0 := ne_of_gt htwo
    field_simp at hthree ⊢
    nlinarith [hthree]
  have hheavyFour : kFourHeavyMass mass weight 4 = mass 0 + mass 1 + mass 2 := by
    have hne : mass 1 ≠ 0 := ne_of_gt hone
    field_simp at hfour ⊢
    nlinarith [hfour]
  have hheavyFive : kFourHeavyMass mass weight 5 = mass 0 + mass 1 + mass 2 := by
    have hne : mass 0 ≠ 0 := ne_of_gt hzero
    field_simp at hfive ⊢
    nlinarith [hfive]
  rw [kFourGaugeStarSlack, hheavyThree, hheavyFour, hheavyFive, min_self, min_self,
    sub_self]

/-! ## 9. The wall is inhabited, at uniform mass -/

/-- The canonical wall witness carries unit mass on every label. -/
noncomputable def kFourGaugeWallMass : Fin 6 → ℝ := fun _ => 1

/-- The weights of the canonical wall witness. -/
noncomputable def kFourGaugeWallWeight : Fin 6 → ℝ
  | 0 => 1 / 12
  | 1 => 1 / 12
  | 2 => 1 / 12
  | 3 => 1 / 4
  | 4 => 1 / 4
  | 5 => 1 / 4

theorem kFourGaugeWallWeight_sum : ∑ label, kFourGaugeWallWeight label = 1 := by
  rw [Fin.sum_univ_six]
  norm_num [kFourGaugeWallWeight]

/-- The canonical wall witness is a genuine chart point. -/
noncomputable def kFourGaugeWallPoint : DirectionChartPoint 6 where
  mass := kFourGaugeWallMass
  weight := kFourGaugeWallWeight
  mass_pos := by intro label; norm_num [kFourGaugeWallMass]
  weight_pos := by
    intro label
    fin_cases label <;> norm_num [kFourGaugeWallWeight]
  weight_sum_one := kFourGaugeWallWeight_sum

/-- **THE WALL IS NOT EMPTY.**  The canonical witness satisfies the three wall
equations.  The registry records that the uniform-WEIGHT gauge wall is impossible.
This point shows that the uniform-MASS gauge wall is exactly where the wall
lives. -/
theorem kFourGaugeWallPoint_wall :
    KFourGaugeWallEquations kFourGaugeWallPoint.mass kFourGaugeWallPoint.weight := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [KFourGaugeWallEquations, kFourGaugeWallPoint, kFourGaugeWallMass,
      kFourGaugeWallWeight, kFourHeavyMass]

/-- At the canonical witness the gauge-star gap is the all-ones matrix, which is
the atom matrix of the all-ones vector. -/
theorem kFourGaugeWallPoint_gap :
    kFourGaugeStarGap kFourGaugeWallPoint.mass kFourGaugeWallPoint.weight
      = !![1, 1, 1; 1, 1, 1; 1, 1, 1] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [kFourGaugeStarGap, kFourGaugeWallPoint, kFourGaugeWallMass,
      kFourGaugeWallWeight, kFourHeavyMass]

/-- **THE WALL CLOSURE HOLDS AT THE WITNESS.**  At the canonical wall point the
star at vertex `1` is strictly positive definite.  The exchange out of the
singular gauge star is explicit, and its Sylvester triple is `(25, 104, 64)`. -/
theorem kFourGaugeWallPoint_vertexOneStar_posDef :
    (directionChartGap kFourDirection kFourGaugeWallPoint.mass
      kFourGaugeWallPoint.weight {0, 1, 3}).PosDef := by
  have hgap : directionChartGap kFourDirection kFourGaugeWallPoint.mass
      kFourGaugeWallPoint.weight {0, 1, 3}
      = !![(25 : ℝ), -11, -11; -11, 9, 1; -11, 1, 9] := by
    rw [directionChartGap_vertexOneStar_eq _ _
      (by norm_num [kFourGaugeWallPoint, kFourGaugeWallWeight])
      (by norm_num [kFourGaugeWallPoint, kFourGaugeWallWeight])
      (by norm_num [kFourGaugeWallPoint, kFourGaugeWallWeight])]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [kFourVertexOneStarGap, kFourGaugeWallPoint, kFourGaugeWallMass,
        kFourGaugeWallWeight, kFourHeavyMass]
  rw [hgap, leadingMinors_pos_iff_posDef_fin_three]
  norm_num

/-- **THE WALL POINT IS A CORANK-TWO POINT.**  The canonical witness carries the
full singular package at the gauge star: positive semidefinite, singular, and with
two independent rational kernel rays. -/
theorem kFourGaugeWallPoint_corankTwo :
    (directionChartGap kFourDirection kFourGaugeWallPoint.mass
        kFourGaugeWallPoint.weight {3, 4, 5}).PosSemidef
      ∧ (directionChartGap kFourDirection kFourGaugeWallPoint.mass
        kFourGaugeWallPoint.weight {3, 4, 5}).det = 0 := by
  have hweight : ∀ label : Fin 6, kFourGaugeWallPoint.weight label ≠ 0 := by
    intro label
    fin_cases label <;> norm_num [kFourGaugeWallPoint, kFourGaugeWallWeight]
  have hgap : directionChartGap kFourDirection kFourGaugeWallPoint.mass
      kFourGaugeWallPoint.weight {3, 4, 5}
      = kFourGaugeStarGap kFourGaugeWallPoint.mass kFourGaugeWallPoint.weight :=
    directionChartGap_gaugeStar_eq _ _ (hweight 3) (hweight 4) (hweight 5)
  rw [hgap]
  exact ⟨posSemidef_kFourGaugeStarGap_of_wall _ _ kFourGaugeWallPoint.mass_pos
      kFourGaugeWallPoint_wall,
    det_kFourGaugeStarGap_of_wall _ _ kFourGaugeWallPoint.mass_pos
      kFourGaugeWallPoint_wall⟩

/-! ## 10. The wall spreads the three heavy gauge masses -/

/-- **THE SECOND LEADING MINOR IS A ROOTED FOREST SUM.**  Eight terms, one for
each two-edge spanning forest of `K4` whose two components hold exactly one of the
two roots.  With the sixteen-term determinant this makes every Sylvester test of a
chart gap a polynomial with a combinatorial reading. -/
theorem leadingMinorTwo_kFourSignedLaplacian (edge : Fin 6 → ℝ) :
    (edge 3 + edge 0 + edge 1) * (edge 4 + edge 0 + edge 2) - edge 0 ^ 2
      = edge 3 * edge 4 + edge 0 * edge 3 + edge 2 * edge 3
        + edge 0 * edge 4 + edge 1 * edge 4
        + edge 0 * edge 1 + edge 0 * edge 2 + edge 1 * edge 2 := by
  ring

/-- **THE WALL SPREAD.**  On the wall the three heavy gauge masses sum to at least
three times the total opposite triangle mass.  Together with
`Gtz.kFourGaugeWall_slack_nonpos`, which puts the SMALLEST of the three at or
below that same total, the wall is a spread condition and never a uniform one.
The proof reduces to `x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x` at
`x = m0 * m1`, `y = m0 * m2`, `z = m1 * m2`. -/
theorem kFourGaugeWall_heavySum_ge (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label)
    (hwall : KFourGaugeWallEquations mass weight) :
    3 * (mass 0 + mass 1 + mass 2)
      ≤ kFourHeavyMass mass weight 3 + kFourHeavyMass mass weight 4
        + kFourHeavyMass mass weight 5 := by
  obtain ⟨hthree, hfour, hfive⟩ := hwall
  have hzero := hmass 0
  have hone := hmass 1
  have htwo := hmass 2
  have hproduct : 0 < mass 0 * mass 1 * mass 2 := mul_pos (mul_pos hzero hone) htwo
  have hdiagThree : (kFourHeavyMass mass weight 3 - mass 0 - mass 1)
      * (mass 0 * mass 1 * mass 2) = (mass 0 * mass 1) ^ 2 := by
    linear_combination (mass 0 * mass 1) * hthree
  have hdiagFour : (kFourHeavyMass mass weight 4 - mass 0 - mass 2)
      * (mass 0 * mass 1 * mass 2) = (mass 0 * mass 2) ^ 2 := by
    linear_combination (mass 0 * mass 2) * hfour
  have hdiagFive : (kFourHeavyMass mass weight 5 - mass 1 - mass 2)
      * (mass 0 * mass 1 * mass 2) = (mass 1 * mass 2) ^ 2 := by
    linear_combination (mass 1 * mass 2) * hfive
  have hmul : (mass 0 + mass 1 + mass 2) * (mass 0 * mass 1 * mass 2)
      ≤ ((kFourHeavyMass mass weight 3 - mass 0 - mass 1)
          + (kFourHeavyMass mass weight 4 - mass 0 - mass 2)
          + (kFourHeavyMass mass weight 5 - mass 1 - mass 2))
        * (mass 0 * mass 1 * mass 2) := by
    nlinarith [hdiagThree, hdiagFour, hdiagFive,
      sq_nonneg (mass 0 * mass 1 - mass 0 * mass 2),
      sq_nonneg (mass 0 * mass 2 - mass 1 * mass 2),
      sq_nonneg (mass 0 * mass 1 - mass 1 * mass 2)]
  have hsum := le_of_mul_le_mul_right hmul hproduct
  linarith

/-! ## 11. The wall hypothesis of the registered obligation IS the variety -/

/-- The singular package of the registered component route gives exactly the two
independent kernel rays that the wall extraction needs. -/
theorem kFourGaugeWallEquations_of_corankTwoData (point : DirectionChartPoint 6)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef)
    (hdata : KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6))) :
    KFourGaugeWallEquations point.mass point.weight := by
  obtain ⟨tight, second, pointer, htightNe, _, htightKernel, _, _, hsecondKernel,
    _, hindependent⟩ := hdata
  have hgap : directionChartGap kFourDirection point.mass point.weight {3, 4, 5}
      = kFourGaugeStarGap point.mass point.weight :=
    directionChartGap_gaugeStar_eq _ _ (point.weight_pos 3).ne'
      (point.weight_pos 4).ne' (point.weight_pos 5).ne'
  rw [hgap] at hpsd htightKernel hsecondKernel
  exact kFourGaugeWallEquations_of_corankTwo point.mass point.weight point.mass_pos
    hpsd tight second htightNe htightKernel hsecondKernel hindependent

/-- **THE COMPONENT OBLIGATION BECOMES A POLYNOMIAL PROBLEM.**  The canonical
gauge-star corank-two wall closure follows from a statement with no matrix
hypothesis at all: at every chart point that satisfies the three division-free
wall equations, some spanning tree is strictly dominating.  The semidefinite
hypothesis and the two-dimensional kernel hypothesis are both spent. -/
theorem kFourGaugeStarCorankWallClosure_of_wallVariety
    (hvariety : ∀ point : DirectionChartPoint 6,
      KFourGaugeWallEquations point.mass point.weight →
        ∃ tree ∈ kFourSpanningTreeList,
          (directionChartGap kFourDirection point.mass point.weight tree).PosDef) :
    KFourGaugeStarCorankWallClosure := by
  intro point hpsd hdata
  exact hvariety point (kFourGaugeWallEquations_of_corankTwoData point hpsd hdata)

/-- The reduced statement holds at the canonical wall witness, with the vertex-`1`
star as the strict tree.  So the polynomial problem is live and not refuted at the
one point where the wall is known to be inhabited. -/
theorem kFourGaugeWallPoint_variety :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection kFourGaugeWallPoint.mass
        kFourGaugeWallPoint.weight tree).PosDef :=
  ⟨{0, 1, 3}, by decide, kFourGaugeWallPoint_vertexOneStar_posDef⟩

/-! ## 12. The rank obstruction: on the wall only nine selections can survive

The gauge-star gap is a single atom matrix on the wall.  Every selection differs
from the gauge star by the same number of added triangle labels and removed gauge
labels.  A selection that keeps two gauge labels can add at most one triangle
label, so its positive part is a sum of TWO atom matrices, and a three-by-three
sum of two atom matrices is singular.  A vector in that kernel reads the whole gap
as minus a nonnegative number.  Seven of the sixteen spanning trees die at one
time, and the residual is the nine trees that hold exactly one gauge label.
-/

/-- The boosted conductance of a label. -/
noncomputable def kFourConductance (mass weight : Fin 6 → ℝ) (label : Fin 6) : ℝ :=
  mass label / weight label

/-- **A THREE-BY-THREE SUM OF TWO ATOM MATRICES IS SINGULAR.**  Two rank-one terms
cannot fill three dimensions. -/
theorem det_add_smul_atomMatrix_pair (axisOne axisTwo : Fin 3 → ℝ)
    (scaleOne scaleTwo : ℝ) :
    (scaleOne • atomMatrix axisOne + scaleTwo • atomMatrix axisTwo).det = 0 := by
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul]
  ring

/-- **THE OBSTRUCTION ENGINE.**  A singular matrix less a positive semidefinite one
is never positive definite.  A kernel vector of the first term reads the difference
as minus a nonnegative number. -/
theorem not_posDef_sub_of_det_eq_zero {size : ℕ}
    {plus minus : Matrix (Fin size) (Fin size) ℝ}
    (hdet : plus.det = 0) (hminus : minus.PosSemidef) :
    ¬ (plus - minus).PosDef := by
  intro hposDef
  obtain ⟨probe, hprobeNe, hprobe⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hplus : probe ⬝ᵥ (plus *ᵥ probe) = 0 := by rw [hprobe, dotProduct_zero]
  have hminusNonneg : 0 ≤ probe ⬝ᵥ (minus *ᵥ probe) :=
    quadForm_nonneg_of_posSemidef_rankOne hminus probe
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobeNe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hplus] at hpos
  linarith

/-- Every selection is the gauge star plus one added atom and less one removed
atom, whenever its signed weight vector has that shape. -/
theorem directionChartGap_eq_gaugeStar_exchange (mass weight : Fin 6 → ℝ)
    (hweight : ∀ label, weight label ≠ 0)
    (selected : Finset (Fin 6)) (triangleLabel gaugeOut : Fin 6)
    (hshape : ∀ label, signedGapWeight mass weight selected label
      = signedGapWeight mass weight {3, 4, 5} label
        + (if label = triangleLabel then kFourConductance mass weight triangleLabel else 0)
        - (if label = gaugeOut then kFourConductance mass weight gaugeOut else 0)) :
    directionChartGap kFourDirection mass weight selected
      = (kFourGaugeStarGap mass weight
          + kFourConductance mass weight triangleLabel
            • atomMatrix (kFourDirection triangleLabel))
        - kFourConductance mass weight gaugeOut
          • atomMatrix (kFourDirection gaugeOut) := by
  have hpick : ∀ (value : ℝ) (target : Fin 6),
      ∑ label, (if label = target then value else 0) • atomMatrix (kFourDirection label)
        = value • atomMatrix (kFourDirection target) := by
    intro value target
    rw [Finset.sum_eq_single target]
    · simp
    · intro label _ hne
      simp [hne]
    · intro hnot
      exact absurd (Finset.mem_univ target) hnot
  have hgauge : kFourGaugeStarGap mass weight
      = ∑ label, signedGapWeight mass weight {3, 4, 5} label
          • atomMatrix (kFourDirection label) := by
    rw [← directionChartGap_eq_sum_signedGapWeight kFourDirection mass weight _
      (fun label _ => hweight label),
      directionChartGap_gaugeStar_eq mass weight (hweight 3) (hweight 4) (hweight 5)]
  rw [directionChartGap_eq_sum_signedGapWeight kFourDirection mass weight selected
    (fun label _ => hweight label), hgauge]
  rw [show (∑ label, signedGapWeight mass weight selected label
        • atomMatrix (kFourDirection label))
      = ∑ label, (signedGapWeight mass weight {3, 4, 5} label
            • atomMatrix (kFourDirection label)
          + (if label = triangleLabel then kFourConductance mass weight triangleLabel
              else 0) • atomMatrix (kFourDirection label)
          - (if label = gaugeOut then kFourConductance mass weight gaugeOut else 0)
              • atomMatrix (kFourDirection label)) from ?_]
  · rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hpick, hpick]
  · refine Finset.sum_congr rfl fun label _ => ?_
    rw [hshape label, sub_smul, add_smul]

/-- **THE RANK OBSTRUCTION.**  On the wall a selection that keeps two gauge labels
and adds one triangle label is never strictly dominating. -/
theorem not_posDef_of_gaugeWall_exchange (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (hwall : KFourGaugeWallEquations mass weight)
    (selected : Finset (Fin 6)) (triangleLabel gaugeOut : Fin 6)
    (hshape : ∀ label, signedGapWeight mass weight selected label
      = signedGapWeight mass weight {3, 4, 5} label
        + (if label = triangleLabel then kFourConductance mass weight triangleLabel else 0)
        - (if label = gaugeOut then kFourConductance mass weight gaugeOut else 0)) :
    ¬ (directionChartGap kFourDirection mass weight selected).PosDef := by
  have hscale : 0 < mass 0 * mass 1 * mass 2 :=
    mul_pos (mul_pos (hmass 0) (hmass 1)) (hmass 2)
  have hform : kFourGaugeStarGap mass weight
      = (mass 0 * mass 1 * mass 2)⁻¹ • atomMatrix (kFourGaugeWallAxis mass) := by
    rw [← smul_kFourGaugeStarGap_of_wall mass weight hwall, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hscale), one_smul]
  rw [directionChartGap_eq_gaugeStar_exchange mass weight
    (fun label => (hweight label).ne') selected triangleLabel gaugeOut hshape, hform]
  refine not_posDef_sub_of_det_eq_zero (det_add_smul_atomMatrix_pair _ _ _ _) ?_
  exact posSemidef_smul_atomMatrix
    (le_of_lt (div_pos (hmass gaugeOut) (hweight gaugeOut))) _

/-- On the wall the gauge star itself is never strictly dominating.  It is
singular. -/
theorem not_posDef_gaugeStar_of_wall (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (hwall : KFourGaugeWallEquations mass weight) :
    ¬ (directionChartGap kFourDirection mass weight {3, 4, 5}).PosDef := by
  rw [directionChartGap_gaugeStar_eq mass weight (hweight 3).ne' (hweight 4).ne'
    (hweight 5).ne']
  intro hposDef
  have hdet := det_kFourGaugeStarGap_of_wall mass weight hmass hwall
  exact absurd hdet (ne_of_gt hposDef.det_pos)

/-- The nine selections that hold exactly one gauge label.  On the wall no other
spanning tree can be strictly dominating. -/
def kFourOneGaugeEdgeTreeList : List (Finset (Fin 6)) :=
  [{0, 1, 3}, {0, 2, 3}, {1, 2, 3},
   {0, 1, 4}, {0, 2, 4}, {1, 2, 4},
   {0, 1, 5}, {0, 2, 5}, {1, 2, 5}]

theorem kFourOneGaugeEdgeTreeList_subset :
    ∀ tree ∈ kFourOneGaugeEdgeTreeList, tree ∈ kFourSpanningTreeList := by
  decide

/-- The exchange shape of the two-gauge selection `{1, 3, 4}`. -/
theorem signedGapWeight_twoGaugeOne (mass weight : Fin 6 → ℝ)
    (hweight : ∀ label, weight label ≠ 0) (label : Fin 6) :
    signedGapWeight mass weight ({1, 3, 4} : Finset (Fin 6)) label
      = signedGapWeight mass weight {3, 4, 5} label
        + (if label = (1 : Fin 6) then kFourConductance mass weight 1 else 0)
        - (if label = (5 : Fin 6) then kFourConductance mass weight 5 else 0) := by
  have hzero := hweight 0
  have hone := hweight 1
  have htwo := hweight 2
  have hthree := hweight 3
  have hfour := hweight 4
  have hfive := hweight 5
  fin_cases label <;>
    simp [signedGapWeight, kFourConductance] <;> field_simp <;> ring

/-- On the wall the two-gauge selection `{1, 3, 4}` is never strictly dominating. -/
theorem not_posDef_twoGaugeOne_of_wall (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (hwall : KFourGaugeWallEquations mass weight) :
    ¬ (directionChartGap kFourDirection mass weight ({1, 3, 4} : Finset (Fin 6))).PosDef :=
  not_posDef_of_gaugeWall_exchange mass weight hmass hweight hwall
    ({1, 3, 4} : Finset (Fin 6)) (1 : Fin 6) (5 : Fin 6)
    (signedGapWeight_twoGaugeOne mass weight (fun slot => (hweight slot).ne'))

/-- The exchange shape of the two-gauge selection `{2, 3, 4}`. -/
theorem signedGapWeight_twoGaugeTwo (mass weight : Fin 6 → ℝ)
    (hweight : ∀ label, weight label ≠ 0) (label : Fin 6) :
    signedGapWeight mass weight ({2, 3, 4} : Finset (Fin 6)) label
      = signedGapWeight mass weight {3, 4, 5} label
        + (if label = (2 : Fin 6) then kFourConductance mass weight 2 else 0)
        - (if label = (5 : Fin 6) then kFourConductance mass weight 5 else 0) := by
  have hzero := hweight 0
  have hone := hweight 1
  have htwo := hweight 2
  have hthree := hweight 3
  have hfour := hweight 4
  have hfive := hweight 5
  fin_cases label <;>
    simp [signedGapWeight, kFourConductance] <;> field_simp <;> ring

/-- On the wall the two-gauge selection `{2, 3, 4}` is never strictly dominating. -/
theorem not_posDef_twoGaugeTwo_of_wall (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (hwall : KFourGaugeWallEquations mass weight) :
    ¬ (directionChartGap kFourDirection mass weight ({2, 3, 4} : Finset (Fin 6))).PosDef :=
  not_posDef_of_gaugeWall_exchange mass weight hmass hweight hwall
    ({2, 3, 4} : Finset (Fin 6)) (2 : Fin 6) (5 : Fin 6)
    (signedGapWeight_twoGaugeTwo mass weight (fun slot => (hweight slot).ne'))

/-- The exchange shape of the two-gauge selection `{0, 3, 5}`. -/
theorem signedGapWeight_twoGaugeThree (mass weight : Fin 6 → ℝ)
    (hweight : ∀ label, weight label ≠ 0) (label : Fin 6) :
    signedGapWeight mass weight ({0, 3, 5} : Finset (Fin 6)) label
      = signedGapWeight mass weight {3, 4, 5} label
        + (if label = (0 : Fin 6) then kFourConductance mass weight 0 else 0)
        - (if label = (4 : Fin 6) then kFourConductance mass weight 4 else 0) := by
  have hzero := hweight 0
  have hone := hweight 1
  have htwo := hweight 2
  have hthree := hweight 3
  have hfour := hweight 4
  have hfive := hweight 5
  fin_cases label <;>
    simp [signedGapWeight, kFourConductance] <;> field_simp <;> ring

/-- On the wall the two-gauge selection `{0, 3, 5}` is never strictly dominating. -/
theorem not_posDef_twoGaugeThree_of_wall (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (hwall : KFourGaugeWallEquations mass weight) :
    ¬ (directionChartGap kFourDirection mass weight ({0, 3, 5} : Finset (Fin 6))).PosDef :=
  not_posDef_of_gaugeWall_exchange mass weight hmass hweight hwall
    ({0, 3, 5} : Finset (Fin 6)) (0 : Fin 6) (4 : Fin 6)
    (signedGapWeight_twoGaugeThree mass weight (fun slot => (hweight slot).ne'))

/-- The exchange shape of the two-gauge selection `{2, 3, 5}`. -/
theorem signedGapWeight_twoGaugeFour (mass weight : Fin 6 → ℝ)
    (hweight : ∀ label, weight label ≠ 0) (label : Fin 6) :
    signedGapWeight mass weight ({2, 3, 5} : Finset (Fin 6)) label
      = signedGapWeight mass weight {3, 4, 5} label
        + (if label = (2 : Fin 6) then kFourConductance mass weight 2 else 0)
        - (if label = (4 : Fin 6) then kFourConductance mass weight 4 else 0) := by
  have hzero := hweight 0
  have hone := hweight 1
  have htwo := hweight 2
  have hthree := hweight 3
  have hfour := hweight 4
  have hfive := hweight 5
  fin_cases label <;>
    simp [signedGapWeight, kFourConductance] <;> field_simp <;> ring

/-- On the wall the two-gauge selection `{2, 3, 5}` is never strictly dominating. -/
theorem not_posDef_twoGaugeFour_of_wall (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (hwall : KFourGaugeWallEquations mass weight) :
    ¬ (directionChartGap kFourDirection mass weight ({2, 3, 5} : Finset (Fin 6))).PosDef :=
  not_posDef_of_gaugeWall_exchange mass weight hmass hweight hwall
    ({2, 3, 5} : Finset (Fin 6)) (2 : Fin 6) (4 : Fin 6)
    (signedGapWeight_twoGaugeFour mass weight (fun slot => (hweight slot).ne'))

/-- The exchange shape of the two-gauge selection `{0, 4, 5}`. -/
theorem signedGapWeight_twoGaugeFive (mass weight : Fin 6 → ℝ)
    (hweight : ∀ label, weight label ≠ 0) (label : Fin 6) :
    signedGapWeight mass weight ({0, 4, 5} : Finset (Fin 6)) label
      = signedGapWeight mass weight {3, 4, 5} label
        + (if label = (0 : Fin 6) then kFourConductance mass weight 0 else 0)
        - (if label = (3 : Fin 6) then kFourConductance mass weight 3 else 0) := by
  have hzero := hweight 0
  have hone := hweight 1
  have htwo := hweight 2
  have hthree := hweight 3
  have hfour := hweight 4
  have hfive := hweight 5
  fin_cases label <;>
    simp [signedGapWeight, kFourConductance] <;> field_simp <;> ring

/-- On the wall the two-gauge selection `{0, 4, 5}` is never strictly dominating. -/
theorem not_posDef_twoGaugeFive_of_wall (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (hwall : KFourGaugeWallEquations mass weight) :
    ¬ (directionChartGap kFourDirection mass weight ({0, 4, 5} : Finset (Fin 6))).PosDef :=
  not_posDef_of_gaugeWall_exchange mass weight hmass hweight hwall
    ({0, 4, 5} : Finset (Fin 6)) (0 : Fin 6) (3 : Fin 6)
    (signedGapWeight_twoGaugeFive mass weight (fun slot => (hweight slot).ne'))

/-- The exchange shape of the two-gauge selection `{1, 4, 5}`. -/
theorem signedGapWeight_twoGaugeSix (mass weight : Fin 6 → ℝ)
    (hweight : ∀ label, weight label ≠ 0) (label : Fin 6) :
    signedGapWeight mass weight ({1, 4, 5} : Finset (Fin 6)) label
      = signedGapWeight mass weight {3, 4, 5} label
        + (if label = (1 : Fin 6) then kFourConductance mass weight 1 else 0)
        - (if label = (3 : Fin 6) then kFourConductance mass weight 3 else 0) := by
  have hzero := hweight 0
  have hone := hweight 1
  have htwo := hweight 2
  have hthree := hweight 3
  have hfour := hweight 4
  have hfive := hweight 5
  fin_cases label <;>
    simp [signedGapWeight, kFourConductance] <;> field_simp <;> ring

/-- On the wall the two-gauge selection `{1, 4, 5}` is never strictly dominating. -/
theorem not_posDef_twoGaugeSix_of_wall (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (hwall : KFourGaugeWallEquations mass weight) :
    ¬ (directionChartGap kFourDirection mass weight ({1, 4, 5} : Finset (Fin 6))).PosDef :=
  not_posDef_of_gaugeWall_exchange mass weight hmass hweight hwall
    ({1, 4, 5} : Finset (Fin 6)) (1 : Fin 6) (3 : Fin 6)
    (signedGapWeight_twoGaugeSix mass weight (fun slot => (hweight slot).ne'))

/-- **THE RESIDUAL IS EXACTLY NINE TREES.**  On the corank-two gauge wall every
strictly dominating spanning tree holds exactly one gauge label.  Seven of the
sixteen are excluded: the gauge star is singular, and each of the six two-gauge
trees has a positive part of rank at most two. -/
theorem mem_kFourOneGaugeEdgeTreeList_of_posDef_of_wall (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (hwall : KFourGaugeWallEquations mass weight)
    (tree : Finset (Fin 6)) (hmem : tree ∈ kFourSpanningTreeList)
    (hposDef : (directionChartGap kFourDirection mass weight tree).PosDef) :
    tree ∈ kFourOneGaugeEdgeTreeList := by
  simp only [kFourSpanningTreeList, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · exact absurd hposDef (not_posDef_gaugeStar_of_wall mass weight hmass hweight hwall)
  · decide
  · decide
  · decide
  · decide
  · exact absurd hposDef (not_posDef_twoGaugeThree_of_wall mass weight hmass hweight hwall)
  · exact absurd hposDef (not_posDef_twoGaugeFive_of_wall mass weight hmass hweight hwall)
  · decide
  · decide
  · exact absurd hposDef (not_posDef_twoGaugeOne_of_wall mass weight hmass hweight hwall)
  · exact absurd hposDef (not_posDef_twoGaugeSix_of_wall mass weight hmass hweight hwall)
  · exact absurd hposDef (not_posDef_twoGaugeTwo_of_wall mass weight hmass hweight hwall)
  · exact absurd hposDef (not_posDef_twoGaugeFour_of_wall mass weight hmass hweight hwall)

/-- **THE SHARPEST REDUCTION OF THE REGISTERED COMPONENT.**  The canonical
gauge-star corank-two wall closure follows from a statement with no matrix
hypothesis and only NINE named trees: at every chart point that satisfies the
three division-free wall equations, one of the nine one-gauge-edge trees is
strictly dominating.  Both the semidefinite hypothesis and the corank hypothesis
are spent, and seven of the sixteen trees are spent with them. -/
theorem kFourGaugeStarCorankWallClosure_of_nineTrees
    (hnine : ∀ point : DirectionChartPoint 6,
      KFourGaugeWallEquations point.mass point.weight →
        ∃ tree ∈ kFourOneGaugeEdgeTreeList,
          (directionChartGap kFourDirection point.mass point.weight tree).PosDef) :
    KFourGaugeStarCorankWallClosure := by
  intro point hpsd hdata
  obtain ⟨tree, hmem, hposDef⟩ :=
    hnine point (kFourGaugeWallEquations_of_corankTwoData point hpsd hdata)
  exact ⟨tree, kFourOneGaugeEdgeTreeList_subset tree hmem, hposDef⟩

/-- The nine-tree statement holds at the canonical wall witness. -/
theorem kFourGaugeWallPoint_nineTrees :
    ∃ tree ∈ kFourOneGaugeEdgeTreeList,
      (directionChartGap kFourDirection kFourGaugeWallPoint.mass
        kFourGaugeWallPoint.weight tree).PosDef :=
  ⟨{0, 1, 3}, by decide, kFourGaugeWallPoint_vertexOneStar_posDef⟩

/-! ## 13. The unseen-direction law, at every size and every stratum

The rank obstruction of section 12 is a `K4` instance of one general fact.  A
selection whose directions all miss a probe reads the chart gap at that probe as
minus the mass energy, and minus a nonnegative number is never positive.  Nothing
in the statement mentions `K4`, the wall, or a spanning tree, so the law is
available at `U(3,6)`, at every line pattern, and at every chart the campaign
builds later.
-/

/-- **THE GENERAL OBSTRUCTION ENGINE.**  A matrix that kills a probe, less a
positive semidefinite matrix, is never positive definite.  The statement assumes
no size and no shape. -/
theorem not_posDef_sub_of_mulVec_eq_zero {size : ℕ}
    {plus minus : Matrix (Fin size) (Fin size) ℝ} {probe : Fin size → ℝ}
    (hprobeNe : probe ≠ 0) (hplus : plus *ᵥ probe = 0) (hminus : minus.PosSemidef) :
    ¬ (plus - minus).PosDef := by
  intro hposDef
  have hplusRead : probe ⬝ᵥ (plus *ᵥ probe) = 0 := by rw [hplus, dotProduct_zero]
  have hminusNonneg : 0 ≤ probe ⬝ᵥ (minus *ᵥ probe) :=
    quadForm_nonneg_of_posSemidef_rankOne hminus probe
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobeNe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hplusRead] at hpos
  linarith

/-- The mass moment of any direction family is positive semidefinite. -/
theorem posSemidef_sum_smul_atomMatrix {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (scale : Fin size → ℝ)
    (hscale : ∀ label, 0 ≤ scale label) :
    (∑ label, scale label • atomMatrix (direction label)).PosSemidef := by
  classical
  refine Finset.sum_induction _ _ (fun _ _ hone htwo => hone.add htwo)
    Matrix.PosSemidef.zero ?_
  intro label _
  exact posSemidef_smul_atomMatrix (hscale label) _

/-- **THE UNSEEN-DIRECTION LAW.**  At every size and every direction family, a
selection whose directions all miss a probe is never strictly dominating.  The
selected moment kills the probe, and what remains is minus the mass energy.  This
is the stratum-free source of the `K4` rank obstruction, and it applies verbatim
to every other chart in the campaign. -/
theorem not_posDef_directionChartGap_of_blindProbe {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 ≤ mass label)
    (selected : Finset (Fin size)) (probe : Fin 3 → ℝ) (hprobeNe : probe ≠ 0)
    (hblind : ∀ label ∈ selected, direction label ⬝ᵥ probe = 0) :
    ¬ (directionChartGap direction mass weight selected).PosDef := by
  rw [directionChartGap]
  refine not_posDef_sub_of_mulVec_eq_zero hprobeNe ?_
    (posSemidef_sum_smul_atomMatrix direction mass hmass)
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun label hmem => ?_
  rw [smul_atomMatrix_mulVec, hblind label hmem, mul_zero, zero_smul]

/-- **A SELECTION INSIDE A PLANE NEVER DOMINATES.**  The plane normal is the
probe.  This is the stratum-free form of the campaign's dependent-triple
exclusion, and it needs no cardinality bound on the selection. -/
theorem not_posDef_directionChartGap_of_coplanar {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 ≤ mass label)
    (selected : Finset (Fin size)) (normal : Fin 3 → ℝ) (hnormalNe : normal ≠ 0)
    (hplane : ∀ label ∈ selected, direction label ⬝ᵥ normal = 0) :
    ¬ (directionChartGap direction mass weight selected).PosDef :=
  not_posDef_directionChartGap_of_blindProbe direction mass weight hmass selected
    normal hnormalNe hplane

end Gtz
