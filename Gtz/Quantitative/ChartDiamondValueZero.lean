/-
THE DIAMOND CHART DATUM AT VALUE ZERO -- five atoms, rank three.

`Gtz.IsChartStationaryData` is a HYPOTHESIS bundle of thirteen fields, and the
question of which sizes inhabit it is not decided by any of them.  Before this
file the bundle was known inhabited at four atoms (`Gtz.chartTetraProjection`,
`Gtz.chartCorankOneProjection`) and at six (`Gtz.chartSplitSixProjection`,
`Gtz.chartTwoBlockTripleProjection`); at FIVE atoms it was measured outside Lean
and never mechanized.  This file closes that: `Gtz.diamondChart_isChartStationaryData`
carries all thirteen fields at five atoms, rank three, value exactly zero, with
eight active triples and a chart exact in the field `Q(sqrt 6)`.

WHY IT MATTERS.  The value-zero interface of `Gtz.ChartValueZeroLocus` reads its
obligations at whatever size it is instantiated at, and a size-non-generic
obligation is one that a five-atom object can already satisfy.  This datum is
that five-atom object: it is chart-stationary at value zero with every atom
strictly heavy (leverages `2` and `13/4`), so any strengthening of the value-zero
leaves that hopes to be size-generic has to survive it.  It is also the first
inhabitant of the bundle whose multiplier is neither a scalar nor a scalar plus
a rank-one pattern -- the two products `P * Xi` and `Xi * P` agree because chart
and multiplier are simultaneously diagonal, not because either is trivial.

THE ARITHMETIC IS SPECTRAL, NOT TABULAR, AND THAT IS THE POINT.  The chart is
defined as a sum of rank-one atoms of PAIRWISE-ORTHOGONAL explicit directions,
never as an entry table.  Symmetry, idempotence, the trace and the commutation
then need no matrix index at all: each is a rank-one manipulation through
`Gtz.vecMulVec_mulVec_eq` plus the eigenbasis Gram table.  The entry-table
definition was tried first and abandoned -- inside this import environment its
`ext`/`fin_cases` idempotence proof does not finish at four million heartbeats,
where the same proof over plain Mathlib costs sixteen seconds.  Any future chart
witness in this tree should be built the same way.

ADMISSIBILITY TOO.  `Gtz.diamondChart_isChartArgmaxValue` proves the second
chart-side field: no triple beats the value.  Eight of the ten triples attain zero
exactly -- they carry their own tight direction -- and the two triangles sit at
`-1/5`.  So the diamond is the complete chart-side value-zero object at five
atoms, stationary AND admissible, and the two size-five facts a size-generic
value-zero obligation would have to survive are both theorems rather than
measurements.

WHAT THIS FILE DOES NOT DO.  It does not identify this chart with
`Gtz.projectionOfDesign Gtz.diamondDesign`, so the three DESIGN-side fields of
`Gtz.IsChartValueZeroLimit` -- a dominating triple, `Gtz.AllHeavy`, no parallel
pair -- are not reached here; the bridge needs `whitener * whitenerᵀ =
(fullLaplacian)⁻¹` and is one lemma away, not below.  Read the statements, not
this header.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.Quantitative.ChartStationary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The single irrationality -/

/-- `√6` — the only irrational entry of the diamond chart. -/
noncomputable def rootSix : ℝ := Real.sqrt 6

theorem rootSix_sq : rootSix ^ 2 = 6 := Real.sq_sqrt (by norm_num)

/-! ## The eigenbasis

Five pairwise-orthogonal directions.  The first three span the range of the
chart, the last two its kernel; the chart and its multiplier are diagonal in
this ONE basis, which is what makes every structural obligation below
index-free. -/

/-- Range direction of squared length `2`. -/
def diamondAxisFirst : Fin 5 → ℝ := ![0, 1, 0, 1, 0]

/-- Range direction of squared length `2`. -/
def diamondAxisSecond : Fin 5 → ℝ := ![0, 0, 1, 0, 1]

/-- Range direction of squared length `40` — the only one meeting the spine. -/
noncomputable def diamondAxisThird : Fin 5 → ℝ :=
  ![4, rootSix, rootSix, -rootSix, -rootSix]

/-- Kernel direction of squared length `4`. -/
def diamondAxisFourth : Fin 5 → ℝ := ![0, 1, -1, -1, 1]

/-- Kernel direction of squared length `10`. -/
noncomputable def diamondAxisFifth : Fin 5 → ℝ := ![-rootSix, 1, 1, -1, -1]

/-! The whole Gram table of the eigenbasis, in one place: the five squared
lengths and the ten orthogonalities. -/

theorem diamondAxisFirst_dot_first : diamondAxisFirst ⬝ᵥ diamondAxisFirst = 2 := by
  simp only [dotProduct, Fin.sum_univ_five, diamondAxisFirst, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons]
  norm_num

theorem diamondAxisSecond_dot_second : diamondAxisSecond ⬝ᵥ diamondAxisSecond = 2 := by
  simp only [dotProduct, Fin.sum_univ_five, diamondAxisSecond, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons]
  norm_num

theorem diamondAxisThird_dot_third : diamondAxisThird ⬝ᵥ diamondAxisThird = 40 := by
  simp only [dotProduct, Fin.sum_univ_five, diamondAxisThird, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons]
  all_goals nlinarith [rootSix_sq]

theorem diamondAxisFirst_dot_second : diamondAxisFirst ⬝ᵥ diamondAxisSecond = 0 := by
  simp only [dotProduct, Fin.sum_univ_five, diamondAxisFirst, diamondAxisSecond,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
  norm_num

theorem diamondAxisFirst_dot_third : diamondAxisFirst ⬝ᵥ diamondAxisThird = 0 := by
  simp only [dotProduct, Fin.sum_univ_five, diamondAxisFirst, diamondAxisThird,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
  ring

theorem diamondAxisSecond_dot_third : diamondAxisSecond ⬝ᵥ diamondAxisThird = 0 := by
  simp only [dotProduct, Fin.sum_univ_five, diamondAxisSecond, diamondAxisThird,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
  ring

theorem diamondAxisFirst_dot_fourth : diamondAxisFirst ⬝ᵥ diamondAxisFourth = 0 := by
  simp [dotProduct, Fin.sum_univ_five, diamondAxisFirst, diamondAxisFourth]

theorem diamondAxisFirst_dot_fifth : diamondAxisFirst ⬝ᵥ diamondAxisFifth = 0 := by
  simp [dotProduct, Fin.sum_univ_five, diamondAxisFirst, diamondAxisFifth]

theorem diamondAxisSecond_dot_fourth : diamondAxisSecond ⬝ᵥ diamondAxisFourth = 0 := by
  simp [dotProduct, Fin.sum_univ_five, diamondAxisSecond, diamondAxisFourth]

theorem diamondAxisSecond_dot_fifth : diamondAxisSecond ⬝ᵥ diamondAxisFifth = 0 := by
  simp [dotProduct, Fin.sum_univ_five, diamondAxisSecond, diamondAxisFifth]

theorem diamondAxisThird_dot_fourth : diamondAxisThird ⬝ᵥ diamondAxisFourth = 0 := by
  simp [dotProduct, Fin.sum_univ_five, diamondAxisThird, diamondAxisFourth]

theorem diamondAxisThird_dot_fifth : diamondAxisThird ⬝ᵥ diamondAxisFifth = 0 := by
  simp [dotProduct, Fin.sum_univ_five, diamondAxisThird, diamondAxisFifth]
  all_goals nlinarith [rootSix_sq]

theorem diamondAxisFourth_dot_fourth : diamondAxisFourth ⬝ᵥ diamondAxisFourth = 4 := by
  simp [dotProduct, Fin.sum_univ_five, diamondAxisFourth]
  norm_num

theorem diamondAxisFifth_dot_fifth : diamondAxisFifth ⬝ᵥ diamondAxisFifth = 10 := by
  simp [dotProduct, Fin.sum_univ_five, diamondAxisFifth]
  all_goals nlinarith [rootSix_sq]

theorem diamondAxisFourth_dot_fifth : diamondAxisFourth ⬝ᵥ diamondAxisFifth = 0 := by
  simp [dotProduct, Fin.sum_univ_five, diamondAxisFourth, diamondAxisFifth]

/-! ## Two reusable rank-one absorption laws

These are the whole reason the spectral definition is cheap: they turn
"this vector is an eigenvector" into "this matrix absorbs that atom", on
either side, with no matrix index anywhere. -/

/-- **An eigenvector absorbs its own atom from the left.** -/
theorem mul_atomMatrix_of_mulVec_smul {target : Matrix (Fin 5) (Fin 5) ℝ}
    {probe : Fin 5 → ℝ} {eigenvalue : ℝ} (haction : target *ᵥ probe = eigenvalue • probe) :
    target * atomMatrix probe = eigenvalue • atomMatrix probe := by
  rw [atomMatrix, Matrix.mul_vecMulVec, haction, Matrix.smul_vecMulVec]

/-- **An eigenvector of a SYMMETRIC matrix absorbs its own atom from the right.** -/
theorem atomMatrix_mul_of_mulVec_smul {target : Matrix (Fin 5) (Fin 5) ℝ}
    {probe : Fin 5 → ℝ} {eigenvalue : ℝ} (hsymmetric : targetᵀ = target)
    (haction : target *ᵥ probe = eigenvalue • probe) :
    atomMatrix probe * target = eigenvalue • atomMatrix probe := by
  have htranspose : (atomMatrix probe * target)ᵀ = eigenvalue • atomMatrix probe := by
    rw [Matrix.transpose_mul, hsymmetric,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix probe).1,
      mul_atomMatrix_of_mulVec_smul haction]
  rw [← Matrix.transpose_transpose (atomMatrix probe * target), htranspose,
    Matrix.transpose_smul, transpose_eq_of_isHermitian (posSemidef_atomMatrix probe).1]

/-! ## The chart -/

/-- The diamond's chart `P`, spectrally: the orthogonal projection onto the span
of the first three eigen-directions. -/
noncomputable def diamondChartProjection : Matrix (Fin 5) (Fin 5) ℝ :=
  (2 : ℝ)⁻¹ • atomMatrix diamondAxisFirst + (2 : ℝ)⁻¹ • atomMatrix diamondAxisSecond
    + (40 : ℝ)⁻¹ • atomMatrix diamondAxisThird

theorem diamondChartProjection_transpose :
    diamondChartProjectionᵀ = diamondChartProjection := by
  rw [diamondChartProjection, Matrix.transpose_add, Matrix.transpose_add,
    Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_smul,
    transpose_eq_of_isHermitian (posSemidef_atomMatrix diamondAxisFirst).1,
    transpose_eq_of_isHermitian (posSemidef_atomMatrix diamondAxisSecond).1,
    transpose_eq_of_isHermitian (posSemidef_atomMatrix diamondAxisThird).1]

/-- **The chart's action on any probe**, in eigen-coordinates. -/
theorem diamondChartProjection_mulVec (probe : Fin 5 → ℝ) :
    diamondChartProjection *ᵥ probe
      = (2 : ℝ)⁻¹ • ((diamondAxisFirst ⬝ᵥ probe) • diamondAxisFirst)
        + (2 : ℝ)⁻¹ • ((diamondAxisSecond ⬝ᵥ probe) • diamondAxisSecond)
        + (40 : ℝ)⁻¹ • ((diamondAxisThird ⬝ᵥ probe) • diamondAxisThird) := by
  rw [diamondChartProjection, Matrix.add_mulVec, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, atomMatrix, atomMatrix,
    atomMatrix, vecMulVec_mulVec_eq, vecMulVec_mulVec_eq, vecMulVec_mulVec_eq]

theorem diamondChartProjection_mulVec_axisFirst :
    diamondChartProjection *ᵥ diamondAxisFirst = diamondAxisFirst := by
  rw [diamondChartProjection_mulVec, diamondAxisFirst_dot_first,
    dotProduct_comm diamondAxisSecond diamondAxisFirst, diamondAxisFirst_dot_second,
    dotProduct_comm diamondAxisThird diamondAxisFirst, diamondAxisFirst_dot_third]
  simp only [zero_smul, smul_zero, add_zero, smul_smul]
  norm_num

theorem diamondChartProjection_mulVec_axisSecond :
    diamondChartProjection *ᵥ diamondAxisSecond = diamondAxisSecond := by
  rw [diamondChartProjection_mulVec, diamondAxisFirst_dot_second, diamondAxisSecond_dot_second,
    dotProduct_comm diamondAxisThird diamondAxisSecond, diamondAxisSecond_dot_third]
  simp only [zero_smul, smul_zero, zero_add, add_zero, smul_smul]
  norm_num

theorem diamondChartProjection_mulVec_axisThird :
    diamondChartProjection *ᵥ diamondAxisThird = diamondAxisThird := by
  rw [diamondChartProjection_mulVec, diamondAxisFirst_dot_third, diamondAxisSecond_dot_third,
    diamondAxisThird_dot_third]
  simp only [zero_smul, smul_zero, add_zero, smul_smul]
  norm_num

theorem diamondChartProjection_mul_self :
    diamondChartProjection * diamondChartProjection = diamondChartProjection := by
  conv_lhs => rw [diamondChartProjection]
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
    mul_atomMatrix_of_mulVec_smul
      (eigenvalue := 1) (by rw [one_smul]; exact diamondChartProjection_mulVec_axisFirst),
    mul_atomMatrix_of_mulVec_smul
      (eigenvalue := 1) (by rw [one_smul]; exact diamondChartProjection_mulVec_axisSecond),
    mul_atomMatrix_of_mulVec_smul
      (eigenvalue := 1) (by rw [one_smul]; exact diamondChartProjection_mulVec_axisThird),
    one_smul, one_smul, one_smul, diamondChartProjection]

theorem diamondChartProjection_trace :
    Matrix.trace diamondChartProjection = ((3 : ℕ) : ℝ) := by
  rw [diamondChartProjection, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_smul, trace_atomMatrix, trace_atomMatrix,
    trace_atomMatrix, leverageOf, leverageOf, leverageOf,
    ← dotProduct_self_eq_sum_sq, ← dotProduct_self_eq_sum_sq, ← dotProduct_self_eq_sum_sq,
    diamondAxisFirst_dot_first, diamondAxisSecond_dot_second, diamondAxisThird_dot_third]
  norm_num

/-! ## The eight tied blocks

The diamond graph has eight spanning trees, and each contributes one active
triple of edges.  The kernel direction of a block is written RAW (integer
entries, or integers against `√6`) and normalised only at the last step; the
gap image of each raw direction is exactly zero on its own block and nonzero
off it, which is precisely the shape the bundle's tightness field asks for. -/

/-- The uniform diamond weights. -/
noncomputable def diamondChartWeight : Fin 5 → ℝ := fun _ => (5 : ℝ)⁻¹

/-- Raw kernel direction of the block it names. -/
noncomputable def diamondRawSpineFirst : Fin 5 → ℝ := ![-rootSix, 1, 1, 0, 0]

/-- Raw kernel direction of the block it names. -/
noncomputable def diamondRawSpineSecond : Fin 5 → ℝ := ![rootSix, -1, 0, 0, 1]

/-- Raw kernel direction of the block it names. -/
noncomputable def diamondRawSpineThird : Fin 5 → ℝ := ![rootSix, 0, -1, 1, 0]

/-- Raw kernel direction of the block it names. -/
noncomputable def diamondRawSpineFourth : Fin 5 → ℝ := ![rootSix, 0, 0, 1, 1]

/-- Raw kernel direction of the block it names. -/
def diamondRawRimFirst : Fin 5 → ℝ := ![0, -3, 2, 3, 0]

/-- Raw kernel direction of the block it names. -/
def diamondRawRimSecond : Fin 5 → ℝ := ![0, 2, -3, 0, 3]

/-- Raw kernel direction of the block it names. -/
def diamondRawRimThird : Fin 5 → ℝ := ![0, 3, 0, -3, 2]

/-- Raw kernel direction of the block it names. -/
def diamondRawRimFourth : Fin 5 → ℝ := ![0, 0, -3, -2, 3]

/-- The eight spanning trees of the diamond, as edge triples. -/
def diamondChartSubset (activeLabel : Fin 8) : Finset (Fin 5) :=
  ![{0, 1, 2}, {0, 1, 4}, {0, 2, 3}, {0, 3, 4},
    {1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}] activeLabel

/-- The eight raw tight directions, tabulated. -/
noncomputable def diamondChartRawDirection (activeLabel : Fin 8) : Fin 5 → ℝ :=
  ![diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird, diamondRawSpineFourth,
    diamondRawRimFirst, diamondRawRimSecond, diamondRawRimThird,
    diamondRawRimFourth] activeLabel

/-- Squared lengths: `8` through the spine, `22` around it. -/
def diamondChartNormSquare (activeLabel : Fin 8) : ℝ :=
  ![8, 8, 8, 8, 22, 22, 22, 22] activeLabel

theorem diamondChartNormSquare_pos (activeLabel : Fin 8) :
    0 < diamondChartNormSquare activeLabel := by
  fin_cases activeLabel <;> norm_num [diamondChartNormSquare]

/-- The gap acts on any probe through the chart minus the uniform weight. -/
theorem diamondChartGap_mulVec (probe : Fin 5 → ℝ) :
    chartStationaryGap diamondChartProjection diamondChartWeight *ᵥ probe
      = (2 : ℝ)⁻¹ • ((diamondAxisFirst ⬝ᵥ probe) • diamondAxisFirst)
        + (2 : ℝ)⁻¹ • ((diamondAxisSecond ⬝ᵥ probe) • diamondAxisSecond)
        + (40 : ℝ)⁻¹ • ((diamondAxisThird ⬝ᵥ probe) • diamondAxisThird)
        - (5 : ℝ)⁻¹ • probe := by
  rw [chartStationaryGap, Matrix.sub_mulVec, diamondChartProjection_mulVec]
  congr 1
  funext coord
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rfl

/-- The gap image of `diamondRawSpineFirst`: zero exactly on its own block. -/
theorem diamondRawSpineFirst_gapImage :
    chartStationaryGap diamondChartProjection diamondChartWeight *ᵥ diamondRawSpineFirst
      = ![0, 0, 0, 4/5, 4/5] := by
  funext coord
  rw [diamondChartGap_mulVec]
  fin_cases coord <;>
    simp [dotProduct, Fin.sum_univ_five, diamondAxisFirst, diamondAxisSecond,
      diamondAxisThird, diamondRawSpineFirst] <;>
    nlinarith [rootSix_sq]

/-- The gap image of `diamondRawSpineSecond`: zero exactly on its own block. -/
theorem diamondRawSpineSecond_gapImage :
    chartStationaryGap diamondChartProjection diamondChartWeight *ᵥ diamondRawSpineSecond
      = ![0, 0, 4/5, -(4/5), 0] := by
  funext coord
  rw [diamondChartGap_mulVec]
  fin_cases coord <;>
    simp [dotProduct, Fin.sum_univ_five, diamondAxisFirst, diamondAxisSecond,
      diamondAxisThird, diamondRawSpineSecond] <;>
    nlinarith [rootSix_sq]

/-- The gap image of `diamondRawSpineThird`: zero exactly on its own block. -/
theorem diamondRawSpineThird_gapImage :
    chartStationaryGap diamondChartProjection diamondChartWeight *ᵥ diamondRawSpineThird
      = ![0, 4/5, 0, 0, -(4/5)] := by
  funext coord
  rw [diamondChartGap_mulVec]
  fin_cases coord <;>
    simp [dotProduct, Fin.sum_univ_five, diamondAxisFirst, diamondAxisSecond,
      diamondAxisThird, diamondRawSpineThird] <;>
    nlinarith [rootSix_sq]

/-- The gap image of `diamondRawSpineFourth`: zero exactly on its own block. -/
theorem diamondRawSpineFourth_gapImage :
    chartStationaryGap diamondChartProjection diamondChartWeight *ᵥ diamondRawSpineFourth
      = ![0, 4/5, 4/5, 0, 0] := by
  funext coord
  rw [diamondChartGap_mulVec]
  fin_cases coord <;>
    simp [dotProduct, Fin.sum_univ_five, diamondAxisFirst, diamondAxisSecond,
      diamondAxisThird, diamondRawSpineFourth] <;>
    nlinarith [rootSix_sq]

/-- The gap image of `diamondRawRimFirst`: zero exactly on its own block. -/
theorem diamondRawRimFirst_gapImage :
    chartStationaryGap diamondChartProjection diamondChartWeight *ᵥ diamondRawRimFirst
      = ![-(2*rootSix/5), 0, 0, 0, 8/5] := by
  funext coord
  rw [diamondChartGap_mulVec]
  fin_cases coord <;>
    simp [dotProduct, Fin.sum_univ_five, diamondAxisFirst, diamondAxisSecond,
      diamondAxisThird, diamondRawRimFirst] <;>
    nlinarith [rootSix_sq]

/-- The gap image of `diamondRawRimSecond`: zero exactly on its own block. -/
theorem diamondRawRimSecond_gapImage :
    chartStationaryGap diamondChartProjection diamondChartWeight *ᵥ diamondRawRimSecond
      = ![-(2*rootSix/5), 0, 0, 8/5, 0] := by
  funext coord
  rw [diamondChartGap_mulVec]
  fin_cases coord <;>
    simp [dotProduct, Fin.sum_univ_five, diamondAxisFirst, diamondAxisSecond,
      diamondAxisThird, diamondRawRimSecond] <;>
    nlinarith [rootSix_sq]

/-- The gap image of `diamondRawRimThird`: zero exactly on its own block. -/
theorem diamondRawRimThird_gapImage :
    chartStationaryGap diamondChartProjection diamondChartWeight *ᵥ diamondRawRimThird
      = ![2*rootSix/5, 0, 8/5, 0, 0] := by
  funext coord
  rw [diamondChartGap_mulVec]
  fin_cases coord <;>
    simp [dotProduct, Fin.sum_univ_five, diamondAxisFirst, diamondAxisSecond,
      diamondAxisThird, diamondRawRimThird] <;>
    nlinarith [rootSix_sq]

/-- The gap image of `diamondRawRimFourth`: zero exactly on its own block. -/
theorem diamondRawRimFourth_gapImage :
    chartStationaryGap diamondChartProjection diamondChartWeight *ᵥ diamondRawRimFourth
      = ![-(2*rootSix/5), -(8/5), 0, 0, 0] := by
  funext coord
  rw [diamondChartGap_mulVec]
  fin_cases coord <;>
    simp [dotProduct, Fin.sum_univ_five, diamondAxisFirst, diamondAxisSecond,
      diamondAxisThird, diamondRawRimFourth] <;>
    nlinarith [rootSix_sq]

/-- The tight directions: raw kernel vectors, normalised. -/
noncomputable def diamondChartTightDir (activeLabel : Fin 8) : Fin 5 → ℝ :=
  (Real.sqrt (diamondChartNormSquare activeLabel))⁻¹ • diamondChartRawDirection activeLabel

/-- Multipliers: `1/15` on the four spine trees, `11/60` on the four others. -/
noncomputable def diamondChartMultiplierWeight (activeLabel : Fin 8) : ℝ :=
  ![1/15, 1/15, 1/15, 1/15, 11/60, 11/60, 11/60, 11/60] activeLabel

/-- **Every ratio `multiplier / squared length` is the SAME number `1/120`** —
the collapse that makes the assembly a single scalar times a sum of atoms.  The
multiplier family of a chart datum is not determined by the point (here a whole
segment of multipliers satisfies all thirteen fields); `1/15` and `11/60` is the
unique member for which this ratio is constant, and that is why it was chosen. -/
theorem diamondChartMultiplierWeight_div_normSquare (activeLabel : Fin 8) :
    diamondChartMultiplierWeight activeLabel * (diamondChartNormSquare activeLabel)⁻¹
      = (120 : ℝ)⁻¹ := by
  fin_cases activeLabel <;>
    norm_num [diamondChartMultiplierWeight, diamondChartNormSquare]

theorem diamondChartRawDirection_dotProduct_self (activeLabel : Fin 8) :
    diamondChartRawDirection activeLabel ⬝ᵥ diamondChartRawDirection activeLabel
      = diamondChartNormSquare activeLabel := by
  fin_cases activeLabel <;>
    simp [dotProduct, Fin.sum_univ_five, diamondChartRawDirection,
      diamondChartNormSquare, diamondRawSpineFirst, diamondRawSpineSecond,
      diamondRawSpineThird, diamondRawSpineFourth, diamondRawRimFirst,
      diamondRawRimSecond, diamondRawRimThird, diamondRawRimFourth] <;>
    nlinarith [rootSix_sq]

/-- **The assembly collapses to ONE scalar.** -/
theorem diamondChartAssembly_eq :
    chartMultiplierAssembly (Finset.univ : Finset (Fin 8)) diamondChartMultiplierWeight
        diamondChartTightDir
      = (120 : ℝ)⁻¹ • ∑ activeLabel : Fin 8,
          atomMatrix (diamondChartRawDirection activeLabel) := by
  rw [chartMultiplierAssembly, Finset.smul_sum]
  refine Finset.sum_congr rfl fun activeLabel _ => ?_
  rw [diamondChartTightDir, atomMatrix_smul, inv_pow,
    Real.sq_sqrt (diamondChartNormSquare_pos activeLabel).le, smul_smul,
    diamondChartMultiplierWeight_div_normSquare]

/-! ## The multiplier -/

/-- **The assembled multiplier**, as the single scalar times the eight tied atoms. -/
noncomputable def diamondChartMultiplier : Matrix (Fin 5) (Fin 5) ℝ :=
  (120 : ℝ)⁻¹ • ∑ activeLabel : Fin 8, atomMatrix (diamondChartRawDirection activeLabel)

theorem diamondChartMultiplier_transpose :
    diamondChartMultiplierᵀ = diamondChartMultiplier := by
  rw [diamondChartMultiplier, Matrix.transpose_smul, Matrix.transpose_sum]
  exact congrArg _ (Finset.sum_congr rfl fun activeLabel _ =>
    transpose_eq_of_isHermitian
      (posSemidef_atomMatrix (diamondChartRawDirection activeLabel)).1)

/-- The multiplier's eigen-action on a RANGE direction of the chart. -/
theorem diamondChartMultiplier_mulVec_axisFirst :
    diamondChartMultiplier *ᵥ diamondAxisFirst = (20 : ℝ)⁻¹ • diamondAxisFirst := by
  funext coord
  fin_cases coord <;>
    simp [diamondChartMultiplier, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
      Fin.sum_univ_eight, atomMatrix, diamondChartRawDirection, diamondAxisFirst,
      diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
      diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
      diamondRawRimThird, diamondRawRimFourth] <;>
    all_goals nlinarith [rootSix_sq]

/-- The multiplier's eigen-action on a RANGE direction of the chart. -/
theorem diamondChartMultiplier_mulVec_axisSecond :
    diamondChartMultiplier *ᵥ diamondAxisSecond = (20 : ℝ)⁻¹ • diamondAxisSecond := by
  funext coord
  fin_cases coord <;>
    simp [diamondChartMultiplier, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
      Fin.sum_univ_eight, atomMatrix, diamondChartRawDirection, diamondAxisSecond,
      diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
      diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
      diamondRawRimThird, diamondRawRimFourth] <;>
    all_goals nlinarith [rootSix_sq]

/-- The multiplier's eigen-action on a RANGE direction of the chart. -/
theorem diamondChartMultiplier_mulVec_axisThird :
    diamondChartMultiplier *ᵥ diamondAxisThird = (10 : ℝ)⁻¹ • diamondAxisThird := by
  funext coord
  fin_cases coord <;>
    simp [diamondChartMultiplier, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
      Fin.sum_univ_eight, atomMatrix, diamondChartRawDirection, diamondAxisThird,
      diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
      diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
      diamondRawRimThird, diamondRawRimFourth] <;>
    all_goals nlinarith [rootSix_sq]

/-- **STATIONARITY IN THE GRASSMANNIAN**, index-free.  Chart and multiplier share
the eigen-directions `first, second, third`, so every rank-one summand of the chart
is an eigen-atom of the multiplier from BOTH sides and the two products collapse to
the same combination.  Note that the multiplier is NOT a scalar and NOT a scalar
plus a rank-one pattern -- its five eigenvalues are `1/20, 1/20, 1/10` on the
chart's range and `8/15, 4/15` on its kernel -- so the commutation is a genuine
condition here rather than an artefact of a trivial assembly. -/
theorem diamondChartProjection_mul_multiplier_comm :
    diamondChartProjection * diamondChartMultiplier
      = diamondChartMultiplier * diamondChartProjection := by
  conv_lhs => rw [diamondChartProjection]
  conv_rhs => rw [diamondChartProjection]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    atomMatrix_mul_of_mulVec_smul diamondChartMultiplier_transpose
      diamondChartMultiplier_mulVec_axisFirst,
    atomMatrix_mul_of_mulVec_smul diamondChartMultiplier_transpose
      diamondChartMultiplier_mulVec_axisSecond,
    atomMatrix_mul_of_mulVec_smul diamondChartMultiplier_transpose
      diamondChartMultiplier_mulVec_axisThird,
    mul_atomMatrix_of_mulVec_smul diamondChartMultiplier_mulVec_axisFirst,
    mul_atomMatrix_of_mulVec_smul diamondChartMultiplier_mulVec_axisSecond,
    mul_atomMatrix_of_mulVec_smul diamondChartMultiplier_mulVec_axisThird]

/-- Tightness at the table level. -/
theorem diamondChartGap_mulVec_rawDirection_eq_zero (activeLabel : Fin 8)
    (atomIndex : Fin 5) (hmem : atomIndex ∈ diamondChartSubset activeLabel) :
    (chartStationaryGap diamondChartProjection diamondChartWeight *ᵥ
      diamondChartRawDirection activeLabel) atomIndex = 0 := by
  fin_cases activeLabel <;> fin_cases atomIndex <;>
    simp_all [diamondChartSubset, diamondChartRawDirection, diamondRawSpineFirst_gapImage,
      diamondRawSpineSecond_gapImage, diamondRawSpineThird_gapImage,
      diamondRawSpineFourth_gapImage, diamondRawRimFirst_gapImage,
      diamondRawRimSecond_gapImage, diamondRawRimThird_gapImage,
      diamondRawRimFourth_gapImage]

/-! ## The datum -/

/-- **THE DIAMOND DATUM.**  Rank three, five atoms, `value = 0`, eight active
spanning trees, assembly of constant diagonal `1/5 = 1/size`. -/
theorem diamondChart_isChartStationaryData :
    IsChartStationaryData 3 diamondChartProjection diamondChartWeight 0
      (Finset.univ : Finset (Fin 8)) diamondChartSubset diamondChartMultiplierWeight
      diamondChartTightDir where
  isSymmetric := diamondChartProjection_transpose
  isIdempotent := diamondChartProjection_mul_self
  hasTraceRank := diamondChartProjection_trace
  weight_pos := by intro atomIndex; norm_num [diamondChartWeight]
  weight_sum_one := by norm_num [diamondChartWeight, Fin.sum_univ_five]
  activeWeight_nonneg := by
    intro activeLabel _
    fin_cases activeLabel <;> norm_num [diamondChartMultiplierWeight]
  activeWeight_sum_one := by
    simp [Fin.sum_univ_eight, diamondChartMultiplierWeight]
    norm_num
  activeSubset_card := by
    intro activeLabel _
    fin_cases activeLabel <;> decide
  tightDir_unit := by
    intro activeLabel _
    have hpositive := diamondChartNormSquare_pos activeLabel
    rw [diamondChartTightDir, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, ← mul_inv, ← pow_two, Real.sq_sqrt hpositive.le,
      diamondChartRawDirection_dotProduct_self, inv_mul_cancel₀ hpositive.ne']
  tightDir_support := by
    intro activeLabel _ atomIndex hnotMem
    rw [diamondChartTightDir, Pi.smul_apply, smul_eq_mul]
    have hzero : diamondChartRawDirection activeLabel atomIndex = 0 := by
      revert hnotMem
      fin_cases activeLabel <;> fin_cases atomIndex <;>
        simp [diamondChartSubset, diamondChartRawDirection, diamondRawSpineFirst,
          diamondRawSpineSecond, diamondRawSpineThird, diamondRawSpineFourth,
          diamondRawRimFirst, diamondRawRimSecond, diamondRawRimThird,
          diamondRawRimFourth]
    rw [hzero, mul_zero]
  tightDir_isTight := by
    intro activeLabel _ atomIndex hmem
    rw [zero_mul, diamondChartTightDir, Matrix.mulVec_smul, Pi.smul_apply,
      diamondChartGap_mulVec_rawDirection_eq_zero activeLabel atomIndex hmem,
      smul_zero]
  assembly_diagonal := by
    intro atomIndex
    rw [diamondChartAssembly_eq]
    fin_cases atomIndex <;>
      simp [Matrix.smul_apply, Fin.sum_univ_eight, atomMatrix, diamondChartRawDirection,
        diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
        diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
        diamondRawRimThird, diamondRawRimFourth] <;>
      all_goals nlinarith [rootSix_sq]
  assembly_commutes := by
    rw [diamondChartAssembly_eq, ← diamondChartMultiplier]
    exact diamondChartProjection_mul_multiplier_comm

/-- **The bundle is inhabited at value ZERO with FIVE atoms** -- strictly between
the `(4,3)` tetrahedron and the open cell, and with a chart that is neither a
scalar nor a scalar-plus-rank-one pattern. -/
theorem exists_isChartStationaryData_five_value_eq_zero :
    ∃ (projection : Matrix (Fin 5) (Fin 5) ℝ) (weight : Fin 5 → ℝ)
      (activeSubset : Fin 8 → Finset (Fin 5)) (activeWeight : Fin 8 → ℝ)
      (tightDir : Fin 8 → (Fin 5 → ℝ)),
      IsChartStationaryData 3 projection weight 0 (Finset.univ : Finset (Fin 8))
        activeSubset activeWeight tightDir :=
  ⟨diamondChartProjection, diamondChartWeight, diamondChartSubset,
    diamondChartMultiplierWeight, diamondChartTightDir,
    diamondChart_isChartStationaryData⟩

/-! ## Conic vacuity at five atoms

`Gtz.SixThreeCrux.no_commonQuadric` says the six directions of a `(6,3)` crux lie
on NO conic of `RP^2`, and that is a genuine restriction because `dim Sym_3(R) = 6`
is exactly the atom count.  At FIVE atoms the same count runs the other way:
`5 < 6`, so the evaluation map has a kernel and EVERY five-atom family in `R^3`
lies on a conic.

The consequence is a vacuity, and it is the reason the diamond above is worth
mechanizing.  Strengthening a value-zero or tie-freeness obligation by "and the
atoms admit no common quadric" makes that obligation unfalsifiable at `(5,3)`:
the diamond's refutation of the plain hinge (`Gtz.not_hingeHoldsAtSize_five_three`)
would evaporate, but so would every scrap of evidence FOR the strengthened form,
because no five-atom object can ever violate it.  A conic-strengthened hinge is
therefore a SIZE-SIX question and must be tested at size six, where stress-freeness
makes the six Veronese images a basis and `no_commonQuadric` has content. -/

/-- The eight linear coordinates a common-quadric search reads off a `3x3` form:
the five quadric evaluations, then the three skew coordinates.  Sending the skew
part to zero alongside the evaluations is what forces the kernel element to be
SYMMETRIC without ever constructing the symmetric subspace. -/
def quadricEvaluationMap (atom : Fin 5 → (Fin 3 → ℝ)) :
    Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun form :=
    ![atom 0 ⬝ᵥ (form *ᵥ atom 0), atom 1 ⬝ᵥ (form *ᵥ atom 1), atom 2 ⬝ᵥ (form *ᵥ atom 2),
      atom 3 ⬝ᵥ (form *ᵥ atom 3), atom 4 ⬝ᵥ (form *ᵥ atom 4),
      form 0 1 - form 1 0, form 0 2 - form 2 0, form 1 2 - form 2 1]
  map_add' firstForm secondForm := by
    funext coord
    fin_cases coord <;>
      simp [Matrix.add_mulVec, dotProduct_add, Matrix.add_apply] <;> ring
  map_smul' scale form := by
    funext coord
    fin_cases coord <;>
      simp [Matrix.smul_mulVec, dotProduct_smul, Matrix.smul_apply, smul_eq_mul] <;> ring

/-- **EVERY FIVE ATOMS IN `R^3` LIE ON A CONIC.**  `dim Sym_3(R) = 6 > 5`, so the
five quadric evaluations plus the three skew coordinates are eight linear
conditions on a nine-dimensional space.  Compare `Gtz.SixThreeCrux.no_commonQuadric`:
at SIX atoms the same count is `6 = 6` and the conclusion reverses. -/
theorem exists_commonQuadric_of_five_atoms (atom : Fin 5 → (Fin 3 → ℝ)) :
    ∃ form : Matrix (Fin 3) (Fin 3) ℝ, form ≠ 0 ∧ formᵀ = form
      ∧ ∀ atomIndex : Fin 5, atom atomIndex ⬝ᵥ (form *ᵥ atom atomIndex) = 0 := by
  have hnotInjective : ¬ Function.Injective (quadricEvaluationMap atom) := by
    intro hinjective
    have hbound := LinearMap.finrank_le_finrank_of_injective hinjective
    rw [Module.finrank_matrix, Module.finrank_pi] at hbound
    simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hbound
    omega
  rw [← LinearMap.ker_eq_bot] at hnotInjective
  obtain ⟨form, hmem, hnonzero⟩ := (Submodule.ne_bot_iff _).mp hnotInjective
  have hcoords : quadricEvaluationMap atom form = 0 := LinearMap.mem_ker.mp hmem
  have hcoord : ∀ coord : Fin 8, quadricEvaluationMap atom form coord = 0 := fun coord => by
    rw [hcoords]; rfl
  refine ⟨form, hnonzero, ?_, ?_⟩
  · have hskewFirst := hcoord 5
    have hskewSecond := hcoord 6
    have hskewThird := hcoord 7
    simp only [quadricEvaluationMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val,
      sub_eq_zero] at hskewFirst hskewSecond hskewThird
    ext rowIndex colIndex
    rw [Matrix.transpose_apply]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp_all
  · intro atomIndex
    have hzero := hcoord atomIndex.castSucc.castSucc.castSucc
    revert hzero
    fin_cases atomIndex <;>
      simp only [quadricEvaluationMap, LinearMap.coe_mk, AddHom.coe_mk] <;>
      exact id

/-- The same statement for a genuine `(5,3)` design -- the exact contrast with
`Gtz.SixThreeCrux.no_commonQuadric` at `(6,3)`. -/
theorem exists_commonQuadric_of_design_five (design : WeightedDesign 5 3) :
    ∃ form : Matrix (Fin 3) (Fin 3) ℝ, form ≠ 0 ∧ formᵀ = form
      ∧ ∀ atomIndex : Fin 5, design.atom atomIndex
          ⬝ᵥ (form *ᵥ design.atom atomIndex) = 0 :=
  exists_commonQuadric_of_five_atoms design.atom

/-! ## The Rayleigh quotient of a tight direction

One size- and rank-generic brick, stated here because `Gtz.ChartStationary` is a
shipped module and this campaign adds by extension only.  Nothing in the bundle
says outright what a tight direction's Rayleigh quotient against the gap IS --
`tightDir_isTight` gives the eigen-equation coordinatewise ON the subset and
`tightDir_support` gives vanishing OFF it, and the two together pin the quotient
to the value exactly.  It is the brick that turns the eight tied blocks of the
diamond into eight admissibility witnesses, and it is the pointwise content
behind `trace (Xi * W) = value`. -/

/-- **A TIGHT DIRECTION'S RAYLEIGH QUOTIENT AGAINST THE GAP IS THE VALUE.**  Split
the dot product over the active subset and its complement: off the subset the
direction vanishes, on it the gap acts as multiplication by the value, and the
direction is a unit vector. -/
theorem dotProduct_chartStationaryGap_mulVec_tightDir
    {size rank : ℕ} {activeIndex : Type*} [Fintype activeIndex] [DecidableEq activeIndex]
    {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ} {value : ℝ}
    {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
    {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet) :
    tightDir activeLabel ⬝ᵥ (chartStationaryGap projection weight *ᵥ tightDir activeLabel)
      = value := by
  have hpointwise : ∀ atomIndex : Fin size,
      tightDir activeLabel atomIndex
          * (chartStationaryGap projection weight *ᵥ tightDir activeLabel) atomIndex
        = value * (tightDir activeLabel atomIndex * tightDir activeLabel atomIndex) := by
    intro atomIndex
    by_cases hmemSubset : atomIndex ∈ activeSubset activeLabel
    · rw [hdata.tightDir_isTight activeLabel hmem atomIndex hmemSubset]; ring
    · rw [hdata.tightDir_support activeLabel hmem atomIndex hmemSubset]; ring
  rw [dotProduct, Finset.sum_congr rfl fun atomIndex _ => hpointwise atomIndex,
    ← Finset.mul_sum, ← dotProduct, hdata.tightDir_unit activeLabel hmem, mul_one]

/-! ## Admissibility at the diamond

`Gtz.IsChartArgmaxValue` asks, at every `rank`-subset, for a unit probe supported
there whose Rayleigh quotient against the gap does not exceed the value.  At the
diamond the value is zero and the ten triples split two ways: the EIGHT spanning
trees carry their own tight direction, whose quotient is exactly zero by the brick
above, and the two TRIANGLES `{0,1,3}` and `{0,2,4}` carry an explicit probe whose
quotient is exactly `-1/5`, comfortably under.  Both triangles are the same object
up to relabelling the two rim pairs, which is why their probes are mirror images. -/

/-- The probe of the triangle `{0,1,3}`, unnormalised: squared length `14`. -/
noncomputable def diamondRawTriangleFirst : Fin 5 → ℝ := ![rootSix, -2, 0, 2, 0]

/-- The probe of the triangle `{0,2,4}`, unnormalised: squared length `14`. -/
noncomputable def diamondRawTriangleSecond : Fin 5 → ℝ := ![rootSix, 0, -2, 0, 2]

theorem diamondRawTriangleFirst_dotProduct_self :
    diamondRawTriangleFirst ⬝ᵥ diamondRawTriangleFirst = 14 := by
  simp [dotProduct, Fin.sum_univ_five, diamondRawTriangleFirst]
  nlinarith [rootSix_sq]

theorem diamondRawTriangleSecond_dotProduct_self :
    diamondRawTriangleSecond ⬝ᵥ diamondRawTriangleSecond = 14 := by
  simp [dotProduct, Fin.sum_univ_five, diamondRawTriangleSecond]
  nlinarith [rootSix_sq]

/-- The triangle probe's Rayleigh quotient before normalisation: `-14/5`, i.e.
`-1/5` once divided by the squared length. -/
theorem diamondRawTriangleFirst_quotient :
    diamondRawTriangleFirst
        ⬝ᵥ (chartStationaryGap diamondChartProjection diamondChartWeight
          *ᵥ diamondRawTriangleFirst) = -(14/5) := by
  rw [diamondChartGap_mulVec]
  simp [dotProduct, Fin.sum_univ_five, diamondAxisFirst, diamondAxisSecond,
    diamondAxisThird, diamondRawTriangleFirst]
  nlinarith [rootSix_sq]

theorem diamondRawTriangleSecond_quotient :
    diamondRawTriangleSecond
        ⬝ᵥ (chartStationaryGap diamondChartProjection diamondChartWeight
          *ᵥ diamondRawTriangleSecond) = -(14/5) := by
  rw [diamondChartGap_mulVec]
  simp [dotProduct, Fin.sum_univ_five, diamondAxisFirst, diamondAxisSecond,
    diamondAxisThird, diamondRawTriangleSecond]
  nlinarith [rootSix_sq]

/-! ## Admissibility: the diamond attains its value at every triple

`Gtz.IsChartArgmaxValue` asks, at EVERY `rank`-subset, for a unit probe supported
there whose Rayleigh quotient against the gap does not exceed the value.  With the
value zero and five atoms there are ten triples, and they split two ways: the
EIGHT spanning trees carry their own raw tight direction, whose quotient is exactly
zero, and the two TRIANGLES carry the explicit probes above at exactly `-1/5`.

The enumeration runs over the COMPLEMENT, which has two elements -- the shipped
idiom of `Gtz.diamondDesign_no_strictDominator`.  It is the reason the ten cases
appear as twenty-five: each unordered pair is met in both orders, and the five
diagonal cases die on distinctness. -/

/-- **NORMALISING A RAW PROBE.**  Every admissibility witness below is an integer
(or `√6`-integer) vector; this divides by its length once, so no case has to carry
a square root. -/
theorem exists_diamondProbe_of_raw {chosenSubset : Finset (Fin 5)} (raw : Fin 5 → ℝ)
    (hpos : 0 < raw ⬝ᵥ raw)
    (hsupport : ∀ atomIndex : Fin 5, atomIndex ∉ chosenSubset → raw atomIndex = 0)
    (hquotient : raw ⬝ᵥ (chartStationaryGap diamondChartProjection diamondChartWeight
      *ᵥ raw) ≤ 0) :
    ∃ probe : Fin 5 → ℝ, probe ⬝ᵥ probe = 1
      ∧ (∀ atomIndex : Fin 5, atomIndex ∉ chosenSubset → probe atomIndex = 0)
      ∧ probe ⬝ᵥ (chartStationaryGap diamondChartProjection diamondChartWeight
          *ᵥ probe) ≤ 0 := by
  refine ⟨(Real.sqrt (raw ⬝ᵥ raw))⁻¹ • raw, ?_, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← mul_inv, ← pow_two, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  · intro atomIndex hnotMem
    rw [Pi.smul_apply, smul_eq_mul, hsupport atomIndex hnotMem, mul_zero]
  · rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, ← mul_inv, ← pow_two, Real.sq_sqrt hpos.le]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hquotient

/-- **A RAW TIGHT DIRECTION HAS ZERO RAYLEIGH QUOTIENT.**  It vanishes off its own
block and the gap image vanishes on it, so every summand of the dot product dies.
This is `Gtz.dotProduct_chartStationaryGap_mulVec_tightDir` read before
normalisation, at the value zero. -/
theorem diamondChartRawDirection_quotient (activeLabel : Fin 8) :
    diamondChartRawDirection activeLabel
        ⬝ᵥ (chartStationaryGap diamondChartProjection diamondChartWeight
          *ᵥ diamondChartRawDirection activeLabel) = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero fun atomIndex _ => ?_
  by_cases hmem : atomIndex ∈ diamondChartSubset activeLabel
  · rw [diamondChartGap_mulVec_rawDirection_eq_zero activeLabel atomIndex hmem, mul_zero]
  · have hzero : diamondChartRawDirection activeLabel atomIndex = 0 := by
      revert hmem
      fin_cases activeLabel <;> fin_cases atomIndex <;>
        simp [diamondChartSubset, diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth]
    rw [hzero, zero_mul]

/-- **THE DIAMOND IS ADMISSIBLE AT ITS VALUE.**  With
`Gtz.diamondChart_isChartStationaryData` this is the full chart-side value-zero
object at five atoms: stationary AND admissible, at value exactly zero. -/
theorem diamondChart_isChartArgmaxValue :
    IsChartArgmaxValue 3 diamondChartProjection diamondChartWeight 0 := by
  intro chosenSubset hcard
  have hcompl : chosenSubsetᶜ.card = 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  obtain ⟨first, second, hdistinct, hpair⟩ := Finset.card_eq_two.mp hcompl
  have hset : chosenSubset = ({first, second} : Finset (Fin 5))ᶜ := by
    rw [← hpair, compl_compl]
  subst hset
  fin_cases first <;> fin_cases second
  · exact absurd rfl hdistinct
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 7)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 7)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 7))
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 6)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 6)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 6))
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 5)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 5)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 5))
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 4)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 4)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 4))
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 7)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 7)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 7))
  · exact absurd rfl hdistinct
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 3)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 3)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 3))
  · exact exists_diamondProbe_of_raw diamondRawTriangleSecond
      (by rw [diamondRawTriangleSecond_dotProduct_self]; norm_num)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;> simp_all [diamondRawTriangleSecond])
      (by rw [diamondRawTriangleSecond_quotient]; norm_num)
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 2)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 2)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 2))
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 6)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 6)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 6))
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 3)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 3)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 3))
  · exact absurd rfl hdistinct
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 1)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 1)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 1))
  · exact exists_diamondProbe_of_raw diamondRawTriangleFirst
      (by rw [diamondRawTriangleFirst_dotProduct_self]; norm_num)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;> simp_all [diamondRawTriangleFirst])
      (by rw [diamondRawTriangleFirst_quotient]; norm_num)
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 5)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 5)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 5))
  · exact exists_diamondProbe_of_raw diamondRawTriangleSecond
      (by rw [diamondRawTriangleSecond_dotProduct_self]; norm_num)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;> simp_all [diamondRawTriangleSecond])
      (by rw [diamondRawTriangleSecond_quotient]; norm_num)
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 1)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 1)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 1))
  · exact absurd rfl hdistinct
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 0)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 0)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 0))
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 4)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 4)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 4))
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 2)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 2)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 2))
  · exact exists_diamondProbe_of_raw diamondRawTriangleFirst
      (by rw [diamondRawTriangleFirst_dotProduct_self]; norm_num)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;> simp_all [diamondRawTriangleFirst])
      (by rw [diamondRawTriangleFirst_quotient]; norm_num)
  · exact exists_diamondProbe_of_raw (diamondChartRawDirection 0)
      (by rw [diamondChartRawDirection_dotProduct_self]
          exact diamondChartNormSquare_pos 0)
      (by intro atomIndex hnotMem
          fin_cases atomIndex <;>
            simp_all [diamondChartRawDirection, diamondRawSpineFirst, diamondRawSpineSecond, diamondRawSpineThird,
          diamondRawSpineFourth, diamondRawRimFirst, diamondRawRimSecond,
          diamondRawRimThird, diamondRawRimFourth])
      (le_of_eq (diamondChartRawDirection_quotient 0))
  · exact absurd rfl hdistinct

end Gtz
