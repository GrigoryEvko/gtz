/-
# The rank-three floor `1/3` is SHARP for the maximal-volume rule

`Gtz.gtzWeightedFloor_inv_rank` (`Gtz/Reduction/RealVolumeFloor.lean`) proves that
every weighted `(m, k)`-design has a `k`-subset `C` with `S_C ⪰ (1/k)·I`, and its
complex twin `Gtz.complexRankConstantAtLeast_rankInverse`
(`Gtz/Complex/PerRankConstantLedger.lean`) proves the same constant over `ℂ`.  At
rank three both read `α_3 ≥ 1/3`, and the standing question — Problem 3 of the
paper — is whether that constant can be raised.

**This file answers the question FOR THAT PROOF'S SELECTION RULE, in the
negative.**  Both proofs pick the MAXIMAL-VOLUME `k`-subset.  Below is an exact
two-parameter family of `(4, 3)`-designs on which the maximal-volume triple is
unique as a subset (`image_eq_leadingTriple_of_isMaximalVolume`) and the level it
certifies is at most `diagonalScale ^ 2`, a quantity the parameters drive to `1/3`
from above.  So no refinement of the maximal-volume estimate can ever certify a
level above `1/3` at rank three
(`not_forall_maximalVolumePick_posSemidef_sub_smul_one` and its `_complex` twin;
`exists_design_forall_maximalVolumePick_not_posSemidef` says it in the form the
selection rule meets it — EVERY volume maximizer on the design fails).

## What is NOT proved here, and must not be read into it

* This is NOT `α_3 = 1/3`, and it does NOT refute `Gtz.GtzWeightedFloor 4 3 level`
  for any `level ≤ 1`.  `GtzWeightedFloor` quantifies EXISTENTIALLY over subsets;
  the family below satisfies GTZ outright, and the file says so with a proof —
  `maximalVolumeSharpDesign_hasDominatingSubset`, three lines through the shipped
  `Gtz.gtzWeighted_corank_one`.  The design is a perfectly good design; it is the
  maximal-volume SUBSET of it that is worthless.
* This says nothing about `α_3(ℂ)` itself, whose conjectured value is the Hesse
  margin `3(1 - cos(2π/9)) = 0.7018…` already in the kernel
  (`Gtz.hesseMarginRankThree`, `Gtz.hesseMargin_isAttainedAndLeast`).  The upper
  bound is untouched here; only the lower-bound ROUTE is closed.
* No claim is made about any other selection rule.  What is closed is the one the
  two shipped floors use.
* The mechanized statement about the leading triple is the ONE-SIDED one:
  `λ_min(S_C) ≤ s²`, obtained by probing the all-ones direction, which is all
  sharpness needs.  The exact identity `λ_min(S_C) = s²` — true, because
  `S_C = a²·I + ((s² - a²)/3)·J` has spectrum `{a², a², s²}` and `s < a` — was
  checked in exact rational arithmetic but is not mechanized here, and no theorem
  below asserts it.

## The family

Two real parameters, `axisScale` (call it `a`) and `diagonalScale` (call it `s`),
with `0 < s < a`, `3 < a²` and `a² + 8s² < 3a²s²`.  Put

    offset = (s - a)/3,   apex = √((a² - s²) / (3(a² - 3))),

    g_i = a·e_i + offset·(1,1,1)   for i = 0,1,2,      g_3 = apex·(1,1,1),
    t   = (1/a², 1/a², 1/a², 1 - 3/a²).

Every atom sits in the symmetric matrix `M = a·I + offset·J`, whose eigenvalues
are `a` twice and `a + 3·offset = s` once along `(1,1,1)`; the fourth atom is
`(apex/s)·M(1,1,1)`.  Parseval is the pair of scalar identities `a²·t_0 = 1` and
`3·offset² + 2a·offset + (a² - 3)·apex² = 0`, and the second is exactly the
definition of `apex` — hence `maximalVolumeSharpDesign` is a design with no side
condition beyond the four inequalities above.

Then:

* `subsetSum` on the leading triple is `M² = a²·I + ((s² - a²)/3)·J`, so the
  all-ones direction sees `3s²` (`sum_entries_subsetSum_maximalVolumeSharpDesign`)
  and no level above `s²` is dominated
  (`not_posSemidef_subsetSum_maximalVolumeSharpDesign_sub_smul_one`).
* Every `3 × 3` row selection has `|det| ≤ a²·s`
  (`abs_det_maximalVolumeSharpTriple_le`) with equality on the leading triple
  (`det_maximalVolumeSharpTriple_lead`), and every selection that takes the apex
  row has `|det| ≤ a²·apex` (`abs_det_maximalVolumeSharpTriple_le_apex`), where
  `apex < s` is the hypothesis `a² + 8s² < 3a²s²` rearranged
  (`maximalVolumeSharpApex_lt_diagonal`).  So the leading triple is the STRICT
  maximal-volume selection, and the only one.
* `1/3 < s²` is forced, not assumed
  (`IsMaximalVolumeSharpParameter.rankInverse_lt_diagonalSq`): it follows from the
  volume hypothesis, which is the floor theorem seen from inside the family.

## Provenance and calibration

The family is campaign 3's; this file is its first mechanization.  Before writing
any Lean it was re-checked in exact rational arithmetic at six parameter pairs
(`a = 3 … 10⁴`), verifying Parseval entry by entry, the least eigenvalue of the
leading triple, the twenty-four injective row selections and their determinants,
and that `{0,1,2}` is the unique volume maximizer; the smallest recorded level is
`1/3 + 8.44e-7`.  The same exact code was calibrated on the regular tetrahedron,
where it recovers the kernel's answer `λ_min = 1` on all four triples and a flat
volume profile.  No floating-point arithmetic enters any statement below.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Complex.SizeAxis
import Gtz.Field.WeightedDesign
import Gtz.Reduction.MaximalVolume
import Gtz.Reduction.RealVolumeFloor
import Gtz.Reduction.Reductions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix
open scoped ComplexOrder

/-! ## The four rows, with the apex entry left abstract

Keeping `apexEntry` a free real through the determinant analysis is what makes
that analysis square-root-free: the square root enters only in `apexScale`, and
only through the two facts `0 ≤ apex` and `apex ≤ diagonalScale`. -/

/-- The shared offset `(s - a)/3` every one of the first three atoms carries along
`(1,1,1)`.  It is negative in the regime of interest. -/
noncomputable def maximalVolumeSharpOffset (axisScale diagonalScale : ℝ) : ℝ :=
  (diagonalScale - axisScale) / 3

/-- The four atom rows of the family, with the apex entry supplied. -/
noncomputable def maximalVolumeSharpRow (axisScale diagonalScale apexEntry : ℝ) :
    Fin 4 → Fin 3 → ℝ :=
  ![![axisScale + maximalVolumeSharpOffset axisScale diagonalScale,
      maximalVolumeSharpOffset axisScale diagonalScale,
      maximalVolumeSharpOffset axisScale diagonalScale],
    ![maximalVolumeSharpOffset axisScale diagonalScale,
      axisScale + maximalVolumeSharpOffset axisScale diagonalScale,
      maximalVolumeSharpOffset axisScale diagonalScale],
    ![maximalVolumeSharpOffset axisScale diagonalScale,
      maximalVolumeSharpOffset axisScale diagonalScale,
      axisScale + maximalVolumeSharpOffset axisScale diagonalScale],
    ![apexEntry, apexEntry, apexEntry]]

/-- The coordinate sum of each of the first three rows is `a + 3·offset = s`. -/
theorem sum_maximalVolumeSharpRow_lead (axisScale diagonalScale apexEntry : ℝ)
    (leadIndex : Fin 3) :
    ∑ coord, maximalVolumeSharpRow axisScale diagonalScale apexEntry leadIndex.castSucc coord
      = diagonalScale := by
  fin_cases leadIndex <;>
    simp [maximalVolumeSharpRow, maximalVolumeSharpOffset, Fin.sum_univ_three] <;> ring

/-! ## The twenty-four row selections and their volumes -/

/-- The four atom indices, as literals.  `fin_cases` would produce `Fin.mk` forms
that the `Matrix.cons_val_*` rewrites do not see; these are the literals they
want. -/
private theorem eq_zero_or_one_or_two_or_three (index : Fin 4) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega

/-- The three coordinates, as literals — same reason. -/
private theorem eq_zero_or_one_or_two (coord : Fin 3) :
    coord = 0 ∨ coord = 1 ∨ coord = 2 := by omega

/-- **Every triple of distinct rows has `|det| ≤ a²·s`.**  The determinant is
`±a²·s` on the leading triple and `±a²·apex` on every triple containing the apex
row, so the bound is `apex ≤ s`.  Twenty-four cases, each a `3 × 3` determinant of
an explicit matrix; the sixty-four-case split includes the forty repeats, killed
by distinctness. -/
theorem abs_det_maximalVolumeSharpTriple_le (axisScale diagonalScale apexEntry : ℝ)
    (haxisPos : 0 < axisScale) (hdiagonalPos : 0 < diagonalScale)
    (hapexNonneg : 0 ≤ apexEntry) (hapexLe : apexEntry ≤ diagonalScale)
    (firstIndex secondIndex thirdIndex : Fin 4)
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex) :
    |(Matrix.of ![maximalVolumeSharpRow axisScale diagonalScale apexEntry firstIndex,
        maximalVolumeSharpRow axisScale diagonalScale apexEntry secondIndex,
        maximalVolumeSharpRow axisScale diagonalScale apexEntry thirdIndex] :
          Matrix (Fin 3) (Fin 3) ℝ).det|
      ≤ axisScale ^ 2 * diagonalScale := by
  have hapexProductNonneg : 0 ≤ axisScale ^ 2 * apexEntry := mul_nonneg (sq_nonneg _) hapexNonneg
  have hapexProductLe : axisScale ^ 2 * apexEntry ≤ axisScale ^ 2 * diagonalScale :=
    mul_le_mul_of_nonneg_left hapexLe (sq_nonneg _)
  have hleadPos : 0 < axisScale ^ 2 * diagonalScale := mul_pos (pow_pos haxisPos 2) hdiagonalPos
  rcases eq_zero_or_one_or_two_or_three firstIndex with rfl | rfl | rfl | rfl <;>
    rcases eq_zero_or_one_or_two_or_three secondIndex with rfl | rfl | rfl | rfl <;>
    rcases eq_zero_or_one_or_two_or_three thirdIndex with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hfirstSecond
      | exact absurd rfl hfirstThird
      | exact absurd rfl hsecondThird
      | · rw [Matrix.det_fin_three, abs_le]
          simp only [maximalVolumeSharpRow, maximalVolumeSharpOffset, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue]
          constructor <;> nlinarith [hapexProductNonneg, hapexProductLe, hleadPos]

/-- **A triple containing the apex row has `|det| ≤ a²·apex`**, strictly below the
leading triple's `a²·s`.  This is what makes the leading triple the UNIQUE volume
maximizer, not merely one of them. -/
theorem abs_det_maximalVolumeSharpTriple_le_apex (axisScale diagonalScale apexEntry : ℝ)
    (hapexNonneg : 0 ≤ apexEntry)
    (firstIndex secondIndex thirdIndex : Fin 4)
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex)
    (hcontainsApex : firstIndex = 3 ∨ secondIndex = 3 ∨ thirdIndex = 3) :
    |(Matrix.of ![maximalVolumeSharpRow axisScale diagonalScale apexEntry firstIndex,
        maximalVolumeSharpRow axisScale diagonalScale apexEntry secondIndex,
        maximalVolumeSharpRow axisScale diagonalScale apexEntry thirdIndex] :
          Matrix (Fin 3) (Fin 3) ℝ).det|
      ≤ axisScale ^ 2 * apexEntry := by
  have hapexProductNonneg : 0 ≤ axisScale ^ 2 * apexEntry := mul_nonneg (sq_nonneg _) hapexNonneg
  rcases eq_zero_or_one_or_two_or_three firstIndex with rfl | rfl | rfl | rfl <;>
    rcases eq_zero_or_one_or_two_or_three secondIndex with rfl | rfl | rfl | rfl <;>
    rcases eq_zero_or_one_or_two_or_three thirdIndex with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hfirstSecond
      | exact absurd rfl hfirstThird
      | exact absurd rfl hsecondThird
      | exact absurd hcontainsApex (by decide)
      | · rw [Matrix.det_fin_three, abs_le]
          simp only [maximalVolumeSharpRow, maximalVolumeSharpOffset, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue]
          constructor <;> nlinarith [hapexProductNonneg]

/-- **The leading triple attains `a²·s` exactly.** -/
theorem det_maximalVolumeSharpTriple_lead (axisScale diagonalScale apexEntry : ℝ) :
    (Matrix.of ![maximalVolumeSharpRow axisScale diagonalScale apexEntry 0,
        maximalVolumeSharpRow axisScale diagonalScale apexEntry 1,
        maximalVolumeSharpRow axisScale diagonalScale apexEntry 2] :
          Matrix (Fin 3) (Fin 3) ℝ).det
      = axisScale ^ 2 * diagonalScale := by
  rw [Matrix.det_fin_three]
  simp only [maximalVolumeSharpRow, maximalVolumeSharpOffset, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Fin.isValue]
  ring

/-! ## The parameter regime -/

/-- The four inequalities the family needs.  `hasVolumeGap` is exactly
`apex < diagonalScale`, cleared of its square root and its denominators; it is the
hypothesis that makes the leading triple the STRICT volume maximizer. -/
structure IsMaximalVolumeSharpParameter (axisScale diagonalScale : ℝ) : Prop where
  isDiagonalPositive : 0 < diagonalScale
  isDiagonalBelowAxis : diagonalScale < axisScale
  isAxisAboveRank : 3 < axisScale ^ 2
  hasVolumeGap : axisScale ^ 2 + 8 * diagonalScale ^ 2 < 3 * axisScale ^ 2 * diagonalScale ^ 2

theorem IsMaximalVolumeSharpParameter.isAxisPositive {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale) : 0 < axisScale :=
  hparameter.isDiagonalPositive.trans hparameter.isDiagonalBelowAxis

/-- **The floor, seen from inside the family**: the volume hypothesis already
forces `1/3 < s²`.  Nothing assumes it. -/
theorem IsMaximalVolumeSharpParameter.rankInverse_lt_diagonalSq {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale) :
    (3 : ℝ)⁻¹ < diagonalScale ^ 2 := by
  have haxisSq : (0 : ℝ) < axisScale ^ 2 := by nlinarith [hparameter.isAxisAboveRank]
  nlinarith [hparameter.hasVolumeGap, sq_nonneg diagonalScale, haxisSq]

/-- The apex entry `√((a² - s²)/(3(a² - 3)))`. -/
noncomputable def maximalVolumeSharpApex (axisScale diagonalScale : ℝ) : ℝ :=
  Real.sqrt ((axisScale ^ 2 - diagonalScale ^ 2) / (3 * (axisScale ^ 2 - 3)))

theorem maximalVolumeSharpApex_nonneg (axisScale diagonalScale : ℝ) :
    0 ≤ maximalVolumeSharpApex axisScale diagonalScale := Real.sqrt_nonneg _

/-- The defining identity of the apex entry, cleared of denominators.  This one
equation IS the off-diagonal half of Parseval. -/
theorem maximalVolumeSharpApex_sq {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale) :
    maximalVolumeSharpApex axisScale diagonalScale
        * maximalVolumeSharpApex axisScale diagonalScale
      = (axisScale ^ 2 - diagonalScale ^ 2) / (3 * (axisScale ^ 2 - 3)) := by
  have hdenominatorPos : (0 : ℝ) < 3 * (axisScale ^ 2 - 3) := by
    nlinarith [hparameter.isAxisAboveRank]
  have hnumeratorNonneg : (0 : ℝ) ≤ axisScale ^ 2 - diagonalScale ^ 2 := by
    nlinarith [hparameter.isDiagonalPositive, hparameter.isDiagonalBelowAxis]
  rw [← sq, maximalVolumeSharpApex, Real.sq_sqrt (by positivity)]

/-- **The apex entry is strictly below the diagonal scale** — the strict
maximal-volume statement, with the square root discharged. -/
theorem maximalVolumeSharpApex_lt_diagonal {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale) :
    maximalVolumeSharpApex axisScale diagonalScale < diagonalScale := by
  have hdenominatorPos : (0 : ℝ) < 3 * (axisScale ^ 2 - 3) := by
    nlinarith [hparameter.isAxisAboveRank]
  rw [maximalVolumeSharpApex, Real.sqrt_lt' hparameter.isDiagonalPositive,
    div_lt_iff₀ hdenominatorPos]
  nlinarith [hparameter.hasVolumeGap]

/-! ## The design -/

/-- The atom rows of the family at its own apex entry. -/
noncomputable def maximalVolumeSharpAtom (axisScale diagonalScale : ℝ) : Fin 4 → Fin 3 → ℝ :=
  maximalVolumeSharpRow axisScale diagonalScale (maximalVolumeSharpApex axisScale diagonalScale)

/-- The weights `(1/a², 1/a², 1/a², 1 - 3/a²)`. -/
noncomputable def maximalVolumeSharpWeight (axisScale : ℝ) : Fin 4 → ℝ :=
  ![(axisScale ^ 2)⁻¹, (axisScale ^ 2)⁻¹, (axisScale ^ 2)⁻¹, 1 - 3 * (axisScale ^ 2)⁻¹]

/-- **THE FAMILY.**  A weighted `(4, 3)`-design for every parameter pair in the
regime.  Parseval is two scalar identities; the second is the definition of the
apex entry. -/
noncomputable def maximalVolumeSharpDesign {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale) :
    WeightedDesign 4 3 where
  atom := maximalVolumeSharpAtom axisScale diagonalScale
  weight := maximalVolumeSharpWeight axisScale
  weight_pos := by
    have haxisSqPos : (0 : ℝ) < axisScale ^ 2 := by nlinarith [hparameter.isAxisAboveRank]
    have htailPos : (0 : ℝ) < 1 - 3 * (axisScale ^ 2)⁻¹ := by
      rw [sub_pos, mul_inv_lt_iff₀ haxisSqPos, one_mul]
      exact hparameter.isAxisAboveRank
    intro atomIndex
    rcases eq_zero_or_one_or_two_or_three atomIndex with rfl | rfl | rfl | rfl
    · exact inv_pos.mpr haxisSqPos
    · exact inv_pos.mpr haxisSqPos
    · exact inv_pos.mpr haxisSqPos
    · exact htailPos
  weight_sum_one := by
    simp only [maximalVolumeSharpWeight, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Fin.isValue]
    ring
  isParseval := by
    have haxisNeZero : axisScale ≠ 0 := ne_of_gt hparameter.isAxisPositive
    have hshiftNeZero : axisScale ^ 2 - 3 ≠ 0 := by nlinarith [hparameter.isAxisAboveRank]
    have hapexSq := maximalVolumeSharpApex_sq hparameter
    ext rowIndex colIndex
    rcases eq_zero_or_one_or_two rowIndex with rfl | rfl | rfl <;>
      rcases eq_zero_or_one_or_two colIndex with rfl | rfl | rfl <;>
      simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
        Fin.sum_univ_four, smul_eq_mul, maximalVolumeSharpWeight, maximalVolumeSharpAtom,
        maximalVolumeSharpRow, maximalVolumeSharpOffset, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.tail_cons, Fin.isValue, Matrix.one_apply, Fin.reduceEq, reduceIte] <;>
      rw [hapexSq] <;> field_simp <;> ring

@[simp] theorem maximalVolumeSharpDesign_atom {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale) :
    (maximalVolumeSharpDesign hparameter).atom = maximalVolumeSharpAtom axisScale diagonalScale :=
  rfl

@[simp] theorem maximalVolumeSharpDesign_weight {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale) :
    (maximalVolumeSharpDesign hparameter).weight = maximalVolumeSharpWeight axisScale :=
  rfl

/-! ## The maximal-volume selection -/

/-- The leading pick `(0, 1, 2)`, whose image is the leading triple. -/
def leadingTriplePick : Fin 3 → Fin 4 := Fin.castSucc

theorem leadingTriplePick_injective : Function.Injective leadingTriplePick :=
  Fin.castSucc_injective 3

theorem image_leadingTriplePick :
    Finset.image leadingTriplePick Finset.univ = ({0, 1, 2} : Finset (Fin 4)) := by
  decide

/-- A row selection of the atom matrix, written as an explicit triple of rows. -/
theorem selectedFrameRows_maximalVolumeSharp {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale)
    (pick : Fin 3 → Fin 4) :
    selectedFrameRows (atomRowMatrix (maximalVolumeSharpDesign hparameter)) pick
      = (Matrix.of ![maximalVolumeSharpAtom axisScale diagonalScale (pick 0),
          maximalVolumeSharpAtom axisScale diagonalScale (pick 1),
          maximalVolumeSharpAtom axisScale diagonalScale (pick 2)] :
            Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> rfl

/-- **The leading triple's volume**, exactly `a²·s`. -/
theorem det_selectedFrameRows_leadingTriplePick {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale) :
    (selectedFrameRows (atomRowMatrix (maximalVolumeSharpDesign hparameter))
        leadingTriplePick).det = axisScale ^ 2 * diagonalScale := by
  rw [selectedFrameRows_maximalVolumeSharp hparameter leadingTriplePick]
  exact det_maximalVolumeSharpTriple_lead axisScale diagonalScale _

/-- **THE LEADING TRIPLE IS A MAXIMAL-VOLUME SELECTION** — the hypothesis
`Gtz.exists_maximalVolumePick_of_witness` returns and the floor proof consumes. -/
theorem isMaximalVolume_leadingTriplePick {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale)
    (other : Fin 3 → Fin 4) (hotherInjective : Function.Injective other) :
    |(selectedFrameRows (atomRowMatrix (maximalVolumeSharpDesign hparameter)) other).det|
      ≤ |(selectedFrameRows (atomRowMatrix (maximalVolumeSharpDesign hparameter))
          leadingTriplePick).det| := by
  have hleadPos : (0 : ℝ) < axisScale ^ 2 * diagonalScale :=
    mul_pos (pow_pos hparameter.isAxisPositive 2) hparameter.isDiagonalPositive
  rw [det_selectedFrameRows_leadingTriplePick hparameter, abs_of_pos hleadPos,
    selectedFrameRows_maximalVolumeSharp hparameter other]
  exact abs_det_maximalVolumeSharpTriple_le axisScale diagonalScale _
    hparameter.isAxisPositive hparameter.isDiagonalPositive
    (maximalVolumeSharpApex_nonneg axisScale diagonalScale)
    (maximalVolumeSharpApex_lt_diagonal hparameter).le
    (other 0) (other 1) (other 2)
    (fun hequal => absurd (hotherInjective hequal) (by decide))
    (fun hequal => absurd (hotherInjective hequal) (by decide))
    (fun hequal => absurd (hotherInjective hequal) (by decide))

/-- The leading selection is nonsingular. -/
theorem det_selectedFrameRows_leadingTriplePick_ne_zero {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale) :
    (selectedFrameRows (atomRowMatrix (maximalVolumeSharpDesign hparameter))
      leadingTriplePick).det ≠ 0 := by
  rw [det_selectedFrameRows_leadingTriplePick hparameter]
  exact ne_of_gt (mul_pos (pow_pos hparameter.isAxisPositive 2) hparameter.isDiagonalPositive)

/-- **A selection that takes the apex atom is strictly smaller in volume.** -/
theorem abs_det_selectedFrameRows_lt_of_takes_apex {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale)
    (pick : Fin 3 → Fin 4) (hpickInjective : Function.Injective pick)
    {selectedIndex : Fin 3} (hapexTaken : pick selectedIndex = 3) :
    |(selectedFrameRows (atomRowMatrix (maximalVolumeSharpDesign hparameter)) pick).det|
      < axisScale ^ 2 * diagonalScale := by
  have hapexBound : |(selectedFrameRows (atomRowMatrix (maximalVolumeSharpDesign hparameter))
      pick).det| ≤ axisScale ^ 2 * maximalVolumeSharpApex axisScale diagonalScale := by
    rw [selectedFrameRows_maximalVolumeSharp hparameter pick]
    refine abs_det_maximalVolumeSharpTriple_le_apex axisScale diagonalScale _
      (maximalVolumeSharpApex_nonneg axisScale diagonalScale) (pick 0) (pick 1) (pick 2)
      (fun hequal => absurd (hpickInjective hequal) (by decide))
      (fun hequal => absurd (hpickInjective hequal) (by decide))
      (fun hequal => absurd (hpickInjective hequal) (by decide)) ?_
    rcases eq_zero_or_one_or_two selectedIndex with rfl | rfl | rfl
    · exact Or.inl hapexTaken
    · exact Or.inr (Or.inl hapexTaken)
    · exact Or.inr (Or.inr hapexTaken)
  have hstrict : axisScale ^ 2 * maximalVolumeSharpApex axisScale diagonalScale
      < axisScale ^ 2 * diagonalScale :=
    mul_lt_mul_of_pos_left (maximalVolumeSharpApex_lt_diagonal hparameter)
      (pow_pos hparameter.isAxisPositive 2)
  exact lt_of_le_of_lt hapexBound hstrict

/-- **THE LEADING TRIPLE IS THE ONLY MAXIMAL-VOLUME SELECTION.**  Every injective
pick whose volume is at least the leading one's has image exactly `{0,1,2}`, so
the floor proof's selection rule cannot avoid the bad triple by choosing a
different maximizer — there is none. -/
theorem image_eq_leadingTriple_of_isMaximalVolume {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale)
    (pick : Fin 3 → Fin 4) (hpickInjective : Function.Injective pick)
    (hattains : axisScale ^ 2 * diagonalScale
      ≤ |(selectedFrameRows (atomRowMatrix (maximalVolumeSharpDesign hparameter)) pick).det|) :
    Finset.image pick Finset.univ = ({0, 1, 2} : Finset (Fin 4)) := by
  classical
  have hnoApex : ∀ selectedIndex : Fin 3, pick selectedIndex ≠ 3 := fun selectedIndex hapexTaken =>
    absurd hattains
      (not_le.mpr (abs_det_selectedFrameRows_lt_of_takes_apex hparameter pick hpickInjective
        hapexTaken))
  have hsubset : Finset.image pick Finset.univ ⊆ ({0, 1, 2} : Finset (Fin 4)) := by
    intro atomIndex hmember
    obtain ⟨selectedIndex, -, hvalue⟩ := Finset.mem_image.mp hmember
    have hnotThree : atomIndex ≠ 3 := by
      rw [← hvalue]
      exact hnoApex selectedIndex
    rcases eq_zero_or_one_or_two_or_three atomIndex with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · exact absurd rfl hnotThree
  refine Finset.eq_of_subset_of_card_le hsubset ?_
  rw [Finset.card_image_of_injective _ hpickInjective, Finset.card_univ, Fintype.card_fin]
  decide

/-! ## The level the maximal-volume selection certifies -/

/-- The all-ones quadratic form of a `3 × 3` matrix over any commutative ring is
the sum of its entries. -/
private theorem dotProduct_ones_mulVec_ones {Scalar : Type*} [CommRing Scalar]
    (form : Matrix (Fin 3) (Fin 3) Scalar) :
    (fun _ : Fin 3 => (1 : Scalar)) ⬝ᵥ (form *ᵥ fun _ : Fin 3 => (1 : Scalar))
      = ∑ rowIndex, ∑ colIndex, form rowIndex colIndex := by
  simp [dotProduct, Matrix.mulVec]

/-- **The leading triple's entries sum to `3s²`.**  `S_C = a²·I + ((s² - a²)/3)·J`
there, so the entry sum is `3a² + 9(s² - a²)/3 = 3s²`.  This one scalar is the
whole obstruction — over `ℝ` and, after coercion, over `ℂ`. -/
theorem sum_entries_subsetSum_maximalVolumeSharpDesign {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale) :
    ∑ rowIndex, ∑ colIndex,
        subsetSum (maximalVolumeSharpDesign hparameter) ({0, 1, 2} : Finset (Fin 4))
          rowIndex colIndex
      = 3 * diagonalScale ^ 2 := by
  rw [subsetSum, show ({0, 1, 2} : Finset (Fin 4)) = insert 0 (insert 1 {2}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [maximalVolumeSharpDesign_atom, maximalVolumeSharpAtom, maximalVolumeSharpRow,
    maximalVolumeSharpOffset, atomMatrix, Matrix.add_apply, Matrix.vecMulVec_apply,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  ring

/-- **The all-ones direction sees exactly `3s²`.** -/
theorem dotProduct_subsetSum_maximalVolumeSharpDesign_ones {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale) :
    (fun _ : Fin 3 => (1 : ℝ)) ⬝ᵥ
        (subsetSum (maximalVolumeSharpDesign hparameter) ({0, 1, 2} : Finset (Fin 4))
          *ᵥ fun _ : Fin 3 => (1 : ℝ))
      = 3 * diagonalScale ^ 2 := by
  rw [dotProduct_ones_mulVec_ones]
  exact sum_entries_subsetSum_maximalVolumeSharpDesign hparameter

/-- **THE SHARPNESS STATEMENT, on one design.**  Above the level `s²` the leading
triple — the maximal-volume selection — does not dominate. -/
theorem not_posSemidef_subsetSum_maximalVolumeSharpDesign_sub_smul_one
    {axisScale diagonalScale level : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale)
    (hlevel : diagonalScale ^ 2 < level) :
    ¬(subsetSum (maximalVolumeSharpDesign hparameter) ({0, 1, 2} : Finset (Fin 4))
        - level • 1).PosSemidef := by
  intro hposSemidef
  have hprobe := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hposSemidef).2
    (fun _ : Fin 3 => (1 : ℝ))
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul, dotProduct_subsetSum_maximalVolumeSharpDesign_ones
      hparameter] at hprobe
  have hones : (fun _ : Fin 3 => (1 : ℝ)) ⬝ᵥ (fun _ : Fin 3 => (1 : ℝ)) = 3 := by
    simp [dotProduct]
  rw [hones] at hprobe
  linarith

/-! ## The design is not a counterexample — the honesty guard

Nothing above says GTZ fails on the family, and it does not: the size is
`rank + 1`, so `Gtz.gtzWeighted_corank_one` hands over a dominating triple.  Only
the maximal-volume triple is bad. -/

/-- **The family satisfies GTZ.**  Some triple dominates outright; it is simply
never the maximal-volume one, once `s² < 1`. -/
theorem maximalVolumeSharpDesign_hasDominatingSubset {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale) :
    ∃ selected : Finset (Fin 4), selected.card = 3 ∧
      Dominates (maximalVolumeSharpDesign hparameter) selected :=
  gtzWeighted_corank_one 3 (by norm_num) (maximalVolumeSharpDesign hparameter)

/-! ## Driving the level to `1/3`

Given any target above `1/3`, the parameters `s² = 1/3 + gap` and `a² = 1/gap + 3`
sit in the regime for every `gap ∈ (0, 1]`, and the four inequalities reduce to
`3 < 1/gap + 3`, `1/3 + gap ≤ 4/3 < 4 ≤ 1/gap + 3` and `0 < 1/3 + gap`. -/

/-- The parameter pair realizing a prescribed gap above `1/3`. -/
theorem isMaximalVolumeSharpParameter_ofGap {gap : ℝ} (hgapPos : 0 < gap) (hgapLe : gap ≤ 1) :
    IsMaximalVolumeSharpParameter (Real.sqrt (gap⁻¹ + 3)) (Real.sqrt (3⁻¹ + gap)) := by
  have hgapInvOne : (1 : ℝ) ≤ gap⁻¹ := one_le_inv_iff₀.mpr ⟨hgapPos, hgapLe⟩
  have haxisSq : Real.sqrt (gap⁻¹ + 3) ^ 2 = gap⁻¹ + 3 := Real.sq_sqrt (by linarith)
  have hdiagonalSq : Real.sqrt (3⁻¹ + gap) ^ 2 = 3⁻¹ + gap := Real.sq_sqrt (by linarith)
  refine ⟨Real.sqrt_pos.mpr (by linarith), ?_, ?_, ?_⟩
  · exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  · rw [haxisSq]; linarith
  · rw [haxisSq, hdiagonalSq]
    have hgapInvIdentity : gap⁻¹ * gap = 1 := inv_mul_cancel₀ (ne_of_gt hgapPos)
    nlinarith [hgapInvIdentity, hgapPos, hgapInvOne]

/-- **THE HEADLINE, positive form.**  For every level above `1/3` there is a
weighted `(4, 3)`-design and a maximal-volume selection on it whose atom sum fails
to dominate that level. -/
theorem exists_design_maximalVolumePick_not_posSemidef {level : ℝ} (hlevel : (3 : ℝ)⁻¹ < level) :
    ∃ (design : WeightedDesign 4 3) (pick : Fin 3 → Fin 4),
      Function.Injective pick ∧
      (selectedFrameRows (atomRowMatrix design) pick).det ≠ 0 ∧
      (∀ other : Fin 3 → Fin 4, Function.Injective other →
        |(selectedFrameRows (atomRowMatrix design) other).det|
          ≤ |(selectedFrameRows (atomRowMatrix design) pick).det|) ∧
      ¬(subsetSum design (Finset.image pick Finset.univ) - level • 1).PosSemidef := by
  set gap : ℝ := min ((level - 3⁻¹) / 2) 1 with hgapDef
  have hgapPos : 0 < gap := lt_min (by linarith) one_pos
  have hgapLe : gap ≤ 1 := min_le_right _ _
  have hgapSmall : 3⁻¹ + gap < level := by
    have := min_le_left ((level - 3⁻¹) / 2) 1
    rw [← hgapDef] at this
    linarith
  have hparameter := isMaximalVolumeSharpParameter_ofGap hgapPos hgapLe
  refine ⟨maximalVolumeSharpDesign hparameter, leadingTriplePick, leadingTriplePick_injective,
    det_selectedFrameRows_leadingTriplePick_ne_zero hparameter,
    isMaximalVolume_leadingTriplePick hparameter, ?_⟩
  rw [image_leadingTriplePick]
  refine not_posSemidef_subsetSum_maximalVolumeSharpDesign_sub_smul_one hparameter ?_
  rw [Real.sq_sqrt (by linarith)]
  exact hgapSmall

/-- **THE HEADLINE, in the form the selection rule sees it: EVERY maximal-volume
selection on the family fails above `1/3`.**  Stronger than the existential above,
and it is what closes the route: the floor proof picks SOME volume maximizer, and
on this design every one of them has image `{0,1,2}`. -/
theorem exists_design_forall_maximalVolumePick_not_posSemidef {level : ℝ}
    (hlevel : (3 : ℝ)⁻¹ < level) :
    ∃ design : WeightedDesign 4 3, ∀ pick : Fin 3 → Fin 4, Function.Injective pick →
      (∀ other : Fin 3 → Fin 4, Function.Injective other →
        |(selectedFrameRows (atomRowMatrix design) other).det|
          ≤ |(selectedFrameRows (atomRowMatrix design) pick).det|) →
      ¬(subsetSum design (Finset.image pick Finset.univ) - level • 1).PosSemidef := by
  set gap : ℝ := min ((level - 3⁻¹) / 2) 1 with hgapDef
  have hgapPos : 0 < gap := lt_min (by linarith) one_pos
  have hgapLe : gap ≤ 1 := min_le_right _ _
  have hgapSmall : 3⁻¹ + gap < level := by
    have := min_le_left ((level - 3⁻¹) / 2) 1
    rw [← hgapDef] at this
    linarith
  have hparameter := isMaximalVolumeSharpParameter_ofGap hgapPos hgapLe
  refine ⟨maximalVolumeSharpDesign hparameter, fun pick hpickInjective hmaximal => ?_⟩
  have hattains : Real.sqrt (gap⁻¹ + 3) ^ 2 * Real.sqrt (3⁻¹ + gap)
      ≤ |(selectedFrameRows (atomRowMatrix (maximalVolumeSharpDesign hparameter)) pick).det| := by
    have hleading := hmaximal leadingTriplePick leadingTriplePick_injective
    rwa [det_selectedFrameRows_leadingTriplePick hparameter,
      abs_of_pos (mul_pos (pow_pos hparameter.isAxisPositive 2)
        hparameter.isDiagonalPositive)] at hleading
  rw [image_eq_leadingTriple_of_isMaximalVolume hparameter pick hpickInjective hattains]
  refine not_posSemidef_subsetSum_maximalVolumeSharpDesign_sub_smul_one hparameter ?_
  rw [Real.sq_sqrt (by linarith)]
  exact hgapSmall

/-- **THE HEADLINE, negative form: the maximal-volume rule certifies no level
above `1/3` at rank three.**  `Gtz.gtzWeightedFloor_inv_rank` and its complex twin
both select the maximal-volume `k`-subset; at `k = 3` that selection is worthless
above `1/3`, so `1/3` is the largest constant those proofs can ever deliver.  This
does NOT bound `α_3` — see the header. -/
theorem not_forall_maximalVolumePick_posSemidef_sub_smul_one {level : ℝ}
    (hlevel : (3 : ℝ)⁻¹ < level) :
    ¬∀ (design : WeightedDesign 4 3) (pick : Fin 3 → Fin 4), Function.Injective pick →
        (∀ other : Fin 3 → Fin 4, Function.Injective other →
          |(selectedFrameRows (atomRowMatrix design) other).det|
            ≤ |(selectedFrameRows (atomRowMatrix design) pick).det|) →
        (subsetSum design (Finset.image pick Finset.univ) - level • 1).PosSemidef := by
  obtain ⟨design, pick, hinjective, -, hmaximal, hfails⟩ :=
    exists_design_maximalVolumePick_not_posSemidef hlevel
  exact fun hall => hfails (hall design pick hinjective hmaximal)

/-! ## The same obstruction over ℂ

The complex floor `Gtz.complexRankConstantAtLeast_rankInverse` is proved by the
same three steps — maximal volume, `[-1, 1]` solve coefficients, Parseval
averaging — on `Gtz.ComplexWeightedDesign` rather than on the real structure.
Coercing the family with the shipped `Gtz.complexifyDesign` transports both halves
of the obstruction verbatim, because every atom of the family is REAL: the
determinants coerce through `RingHom.map_det` and the all-ones quadratic form is
the coercion of a real number.  So the maximal-volume rule certifies no level
above `1/3` over `ℂ` either, and `α_3(ℂ) > 1/3` — if true, and the Hesse margin
says it should be `0.7018…` — needs a different argument entirely. -/

/-- The `rank × rank` block a pick selects from a field design's atoms.  Its
`‖det‖` is the selection's volume; over `ℝ` this is `Gtz.selectedFrameRows` of the
atom matrix. -/
def fieldSelectedAtomRows {Scalar : Type*} [RCLike Scalar] {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (pick : Fin rank → Fin size) :
    Matrix (Fin rank) (Fin rank) Scalar :=
  Matrix.of fun selectedIndex coord => design.atom (pick selectedIndex) coord

/-- Selecting rows commutes with complexifying the design. -/
theorem fieldSelectedAtomRows_complexifyDesign {size rank : ℕ}
    (design : WeightedDesign size rank) (pick : Fin rank → Fin size) :
    fieldSelectedAtomRows (complexifyDesign design) pick
      = complexifyMatrix (selectedFrameRows (atomRowMatrix design) pick) := rfl

/-- Coercing a real matrix coerces its determinant. -/
theorem det_complexifyMatrix {order : ℕ} (form : Matrix (Fin order) (Fin order) ℝ) :
    (complexifyMatrix form).det = ((form.det : ℝ) : ℂ) :=
  (RingHom.map_det Complex.ofRealHom form).symm

/-- The atom sum of a complexified design is the complexified atom sum. -/
theorem fieldSubsetSum_complexifyDesign {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    fieldSubsetSum (complexifyDesign design) selected
      = complexifyMatrix (subsetSum design selected) := by
  ext rowIndex colIndex
  simp only [fieldSubsetSum, subsetSum, Matrix.sum_apply, complexifyMatrix_apply, fieldAtom,
    atomMatrix, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal,
    complexifyDesign, Complex.ofReal_sum, Complex.ofReal_mul]

/-- **THE COMPLEX FAMILY.**  The real family read over `ℂ`, atom for atom. -/
noncomputable def complexMaximalVolumeSharpDesign {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale) :
    FieldWeightedDesign ℂ 4 3 :=
  complexifyDesign (maximalVolumeSharpDesign hparameter)

/-- **The complex volume of a selection is the real one.**  Every atom of the
family is real, so `‖det‖` over `ℂ` is `|det|` over `ℝ` — the whole volume analysis
transports through this one line. -/
theorem norm_det_fieldSelectedAtomRows_complexMaximalVolumeSharpDesign
    {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale)
    (pick : Fin 3 → Fin 4) :
    ‖(fieldSelectedAtomRows (complexMaximalVolumeSharpDesign hparameter) pick).det‖
      = |(selectedFrameRows (atomRowMatrix (maximalVolumeSharpDesign hparameter)) pick).det| := by
  rw [complexMaximalVolumeSharpDesign, fieldSelectedAtomRows_complexifyDesign,
    det_complexifyMatrix, Complex.norm_real, Real.norm_eq_abs]

/-- **The leading triple is a maximal-volume selection over `ℂ` too.** -/
theorem isMaximalVolume_leadingTriplePick_complex {axisScale diagonalScale : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale)
    (other : Fin 3 → Fin 4) (hotherInjective : Function.Injective other) :
    ‖(fieldSelectedAtomRows (complexMaximalVolumeSharpDesign hparameter) other).det‖
      ≤ ‖(fieldSelectedAtomRows (complexMaximalVolumeSharpDesign hparameter)
          leadingTriplePick).det‖ := by
  rw [norm_det_fieldSelectedAtomRows_complexMaximalVolumeSharpDesign,
    norm_det_fieldSelectedAtomRows_complexMaximalVolumeSharpDesign]
  exact isMaximalVolume_leadingTriplePick hparameter other hotherInjective

/-- **THE SHARPNESS STATEMENT OVER `ℂ`.**  Above the level `s²` the leading triple
does not dominate in the complex Loewner order either. -/
theorem not_posSemidef_fieldSubsetSum_complexMaximalVolumeSharpDesign_sub_smul_one
    {axisScale diagonalScale level : ℝ}
    (hparameter : IsMaximalVolumeSharpParameter axisScale diagonalScale)
    (hlevel : diagonalScale ^ 2 < level) :
    ¬(fieldSubsetSum (complexMaximalVolumeSharpDesign hparameter)
        ({0, 1, 2} : Finset (Fin 4)) - ((level : ℝ) : ℂ) • 1).PosSemidef := by
  intro hposSemidef
  have hprobe := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hposSemidef).2
    (fun _ : Fin 3 => (1 : ℂ))
  have hstar : star (fun _ : Fin 3 => (1 : ℂ)) = fun _ : Fin 3 => (1 : ℂ) := by
    funext coord
    simp
  rw [hstar, dotProduct_ones_mulVec_ones] at hprobe
  have hentrySum : ∑ rowIndex, ∑ colIndex,
      (fieldSubsetSum (complexMaximalVolumeSharpDesign hparameter)
        ({0, 1, 2} : Finset (Fin 4)) - ((level : ℝ) : ℂ) • 1) rowIndex colIndex
      = ((3 * diagonalScale ^ 2 - 3 * level : ℝ) : ℂ) := by
    rw [complexMaximalVolumeSharpDesign, fieldSubsetSum_complexifyDesign]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, complexifyMatrix_apply,
      smul_eq_mul, Fin.sum_univ_three, Fin.isValue, Fin.reduceEq, reduceIte]
    have hreal := sum_entries_subsetSum_maximalVolumeSharpDesign hparameter
    simp only [Fin.sum_univ_three, Fin.isValue] at hreal
    have hrealComplex := congrArg (fun value : ℝ => (value : ℂ)) hreal
    push_cast at hrealComplex
    push_cast
    linear_combination hrealComplex
  rw [hentrySum] at hprobe
  have hrealNonneg : (0 : ℝ) ≤ 3 * diagonalScale ^ 2 - 3 * level :=
    RCLike.ofReal_nonneg.mp hprobe
  linarith

/-- **EVERY maximal-volume selection on the complex family fails above `1/3`.** -/
theorem exists_design_forall_maximalVolumePick_not_posSemidef_complex {level : ℝ}
    (hlevel : (3 : ℝ)⁻¹ < level) :
    ∃ design : FieldWeightedDesign ℂ 4 3, ∀ pick : Fin 3 → Fin 4, Function.Injective pick →
      (∀ other : Fin 3 → Fin 4, Function.Injective other →
        ‖(fieldSelectedAtomRows design other).det‖ ≤ ‖(fieldSelectedAtomRows design pick).det‖) →
      ¬(fieldSubsetSum design (Finset.image pick Finset.univ)
        - ((level : ℝ) : ℂ) • 1).PosSemidef := by
  set gap : ℝ := min ((level - 3⁻¹) / 2) 1 with hgapDef
  have hgapPos : 0 < gap := lt_min (by linarith) one_pos
  have hgapLe : gap ≤ 1 := min_le_right _ _
  have hgapSmall : 3⁻¹ + gap < level := by
    have := min_le_left ((level - 3⁻¹) / 2) 1
    rw [← hgapDef] at this
    linarith
  have hparameter := isMaximalVolumeSharpParameter_ofGap hgapPos hgapLe
  refine ⟨complexMaximalVolumeSharpDesign hparameter, fun pick hpickInjective hmaximal => ?_⟩
  have hattains : Real.sqrt (gap⁻¹ + 3) ^ 2 * Real.sqrt (3⁻¹ + gap)
      ≤ |(selectedFrameRows (atomRowMatrix (maximalVolumeSharpDesign hparameter)) pick).det| := by
    have hleading := hmaximal leadingTriplePick leadingTriplePick_injective
    rw [norm_det_fieldSelectedAtomRows_complexMaximalVolumeSharpDesign,
      norm_det_fieldSelectedAtomRows_complexMaximalVolumeSharpDesign,
      det_selectedFrameRows_leadingTriplePick hparameter,
      abs_of_pos (mul_pos (pow_pos hparameter.isAxisPositive 2)
        hparameter.isDiagonalPositive)] at hleading
    exact hleading
  rw [image_eq_leadingTriple_of_isMaximalVolume hparameter pick hpickInjective hattains]
  refine not_posSemidef_fieldSubsetSum_complexMaximalVolumeSharpDesign_sub_smul_one
    hparameter ?_
  rw [Real.sq_sqrt (by linarith)]
  exact hgapSmall

/-- **THE COMPLEX HEADLINE: the maximal-volume rule certifies no level above
`1/3` at rank three over `ℂ`.**  Same family, same triple, coerced. -/
theorem not_forall_maximalVolumePick_posSemidef_sub_smul_one_complex {level : ℝ}
    (hlevel : (3 : ℝ)⁻¹ < level) :
    ¬∀ (design : FieldWeightedDesign ℂ 4 3) (pick : Fin 3 → Fin 4), Function.Injective pick →
        (∀ other : Fin 3 → Fin 4, Function.Injective other →
          ‖(fieldSelectedAtomRows design other).det‖
            ≤ ‖(fieldSelectedAtomRows design pick).det‖) →
        (fieldSubsetSum design (Finset.image pick Finset.univ)
          - ((level : ℝ) : ℂ) • 1).PosSemidef := by
  set gap : ℝ := min ((level - 3⁻¹) / 2) 1 with hgapDef
  have hgapPos : 0 < gap := lt_min (by linarith) one_pos
  have hgapLe : gap ≤ 1 := min_le_right _ _
  have hgapSmall : 3⁻¹ + gap < level := by
    have := min_le_left ((level - 3⁻¹) / 2) 1
    rw [← hgapDef] at this
    linarith
  have hparameter := isMaximalVolumeSharpParameter_ofGap hgapPos hgapLe
  intro hall
  refine not_posSemidef_fieldSubsetSum_complexMaximalVolumeSharpDesign_sub_smul_one
    hparameter (level := level) ?_ ?_
  · rw [Real.sq_sqrt (by linarith)]
    exact hgapSmall
  · have hdominates := hall (complexMaximalVolumeSharpDesign hparameter) leadingTriplePick
      leadingTriplePick_injective (isMaximalVolume_leadingTriplePick_complex hparameter)
    rwa [image_leadingTriplePick] at hdominates

end Gtz
