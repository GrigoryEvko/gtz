/-
# The Cauchy–Binet floor at `(7,3)`-uniform — `λ_min(Γ[T#]) > 31/150` at a maximal-volume pick

The maximal-volume selector's trace route (one-row exchange bounds, giving
`tr Γ⁻¹ ≤ 45/7`) proves the FIFTHS floor `λ_min(Γ[T#]) > 1/5`.  This file goes
beyond it with the CAUCHY–BINET refinement: two- and three-row exchange bounds
cap not just the trace of the outside coordinate mass `R = X_oᵀX_o` but its
higher elementary symmetric functions, and the sharpened constraint set forces

    `λ_min(Γ[T#]) > 31/150 = 0.2066…`  (`posDef_unitPickGram_sub_cauchyBinetFloor_sevenThree`),

strictly above `1/5 = 30/150`, at every `(7,3)`-uniform design and every
volume-maximal nonsingular pick of the unit-atom rows
(`exists_pick_posDef_unitPickGram_sub_cauchyBinetFloor_sevenThree` supplies the
pick unconditionally).

## The relaxation, and the erratum it corrects

At uniform share `3/7` the outside coordinate matrix `X_o` (four rows, the
unpicked atoms in the picked basis) satisfies, at a maximal-volume pick,

  * `e₁(R) ≤ 12`  — twelve entries, each in `[−1,1]` (one-row swaps);
  * `e₂(R) ≤ 18`  — eighteen `2×2` minors, each in `[−1,1]` (two-row swaps);
  * `e₃(R) ≤ 4`   — four `3×3` minors, each in `[−1,1]` (three-row swaps);
  * isotropy: `R = (7/3)·Γ⁻¹ − 1`, i.e. `Σᵢ 1/(1+rᵢ) = 9/7`.

Maximizing `λ_max(R)` under these constraints: `e₁ = 12` and `e₃ = 4` are tight
and isotropy then FORCES `e₂ = 18` (any two of the three tight bounds force the
third, since `5e₁ − 2e₂ − 9e₃ + 12 = 0`), so the extremal spectrum of `R` is
exactly the root set of

    `u³ − 12u² + 18u − 4`,   roots `≈ {0.26958, 1.44220, 10.28822}`,

and the true relaxation floor is `g* = 7/(3(1+u*)) ≈ 0.2067052` — the smallest
root of the image cubic `C(x) = 135x³ − 405x² + 315x − 49`
(`relaxationCubic_image_eq_cauchyBinetFloorCubic_sevenThree`; the sign bracket
`C(31/150) < 0 < C(21/100)` locates `g*` in `(31/150, 21/100)`).

ERRATUM, re-verified in exact arithmetic before this file was written (all
seventy checks in `SevenThreeCBFloor_verify.py` pass): an earlier campaign
sitting reported the refined floor as `≈ 0.2543`.  That figure is the maximum
of the SYMMETRIC slice `r₁ = r₂` with only `e₃ = 4` active (there
`r₃ ≈ 8.1696`, `e₁ ≈ 9.57` and `e₂ ≈ 11.92` both slack, floor `≈ 0.25446`);
the genuine optimum is asymmetric (`r ≈ (0.270, 1.442, 10.288)`) with all
three exchange bounds active, and the correct value is `≈ 0.2067052`.
Boundary branches: the fifths spectrum `r = (2/3, 2/3, 32/3)` violates
`e₃ ≤ 4` (its `e₃ = 128/27`), which is exactly why the three-row bound pushes
the floor above `1/5`; and the degenerate branch `r₁ = 0` is INFEASIBLE
outright once `e₂ ≤ 18` is imposed (isotropy forces `e₂ = (12 + 5(r₂+r₃))/2`,
so `e₂ ≤ 18` needs `r₂ + r₃ ≤ 24/5` while realness of the pair needs
`r₂ + r₃ ≥ 12`; the earlier note's point `(0, 6, 6)` has `e₂ = 36`).

## What is mechanized here

In the `(σ, P)` entry coordinates of the picked unit Gram
(`σ = γ₀₁² + γ₀₂² + γ₁₂²`, `P = γ₀₁γ₀₂γ₁₂`) the two constraints that cut out
the floor read `38σ − 24 ≤ 90P` (TRACE GATE, from `e₁ ≤ 12`) and
`36σ − 22 ≤ 135P` (VOLUME GATE, from `e₃ ≤ 4`), meeting at the corner
`(σ, P) = (2/3, 2/135)`.  The `e₂(R) ≤ 18` bound is NOT needed for the floor —
the corner is cut out by the trace and volume gates alone — so this file lands
the two-row minor bounds (`abs_twoRowMinor_solveMatrix_le_one_of_maximalVolume`)
as exchange theory but never consumes them downstream.  The floor argument is
eigenvalue-free throughout:

  * `abs_det_solveMatrix_submatrix_le_one_of_maximalVolume` — the UNIFIED
    exchange bound: at a maximal-volume pick, EVERY square row-submatrix of the
    solve matrix has determinant in `[−1,1]` (entries, `2×2` minors and `3×3`
    minors are all instances, via basis rows of the solve matrix);
  * `det_transpose_mul_self_four_rows_eq_sum_sq_minors` — Cauchy–Binet for a
    `4×3` block: `det(XᵀX)` is the sum of the four squared `3×3` row minors;
  * the gates `traceGate_of_maximalVolume_sevenThree` and
    `volumeGate_of_maximalVolume_sevenThree` in the `(σ, P)` vocabulary of
    `directionTripleSigma` / `directionTripleProduct`;
  * the σ-CAP `σ(T#) ≤ 4/3` (`directionTripleSigma_le_fourThirds_of_maximalVolume_sevenThree`)
    from the trace gate plus the AM–GM certificate `27P² ≤ σ³`, through the
    EXACT factorization `300σ³ − (38σ−24)² = 300(σ−12/25)(σ−4/3)(σ−3)`;
  * positive definiteness of `Γ[T#] − (31/150)·1` by the elementary-symmetric
    criterion: `e₁ = 3(1−t) > 0`, `e₂ = 3(1−t)² − σ > 0` (from the σ-cap), and
    `det = (1−t)³ − (1−t)σ + 2P > 0` (LINEAR in `(σ, P)` — the two gates leave
    the exact margin `ψ(31/150) = 159/3375000` at the corner).

## The `(6,3)` calibration twin

Same skeleton at share `1/2` (three outside rows): the volume gate DEGENERATES
to `P(T#) ≥ 0` (`nonneg_directionTripleProduct_of_maximalVolume_sixThree` — at
a `(6,3)`-uniform maximal-volume pick the triple product is nonnegative; on the
icosahedral design this is the statement that the maximal triples are FACES),
the σ-cap is `5/4`, and the landed floor is `9/40 = 0.225`
(`posDef_unitPickGram_sub_cauchyBinetFloor_sixThree`), strictly above the
trace-route floor `(5 − √17)/4 ≈ 0.21922` and just below the exact relaxation
optimum `(5 − √15)/5 ≈ 0.22540` — the smallest root of `5x³ − 15x² + 12x − 2`,
bracketed here by `C₆(9/40) < 0 < C₆(1/4)`.  U6 is already a theorem on this
stratum, so every `(6,3)` statement here has a proved ground truth above it.

## Conjecture M7 and the rigidity frontier

`MaxVolumeGramThirdFloorSevenThree` names the conjecture: at `(7,3)`-uniform
share the maximal-volume pick always has `λ_min(Γ[T#]) ≥ 1/3`.  It implies a
dominating triple on the uniform-share leverage-3 stratum
(`exists_dominating_triple_of_maxVolumeGramThirdFloor`, through the landed
domination dictionary; on mixed-leverage uniform-share designs the Gram floor
alone does not translate to domination, so the Prop is stated Gram-side).  The
march is

    `1/5  <  31/150  ≤  g* ≈ 0.2067052  <  1/3`,

with equality at `1/3` calibrated by the tetrahedral tie: the all-`(−1/3)`
correlation matrix has determinant `16/27` and spectrum `(1/3, 4/3, 4/3)`
(`det_tetrahedralCorrelationThree`, `sq_det_tetrapodUnitTriple`); on the
basis-plus-tetrapod witness the MAXIMAL-volume triple is the orthonormal basis
(Gram determinant `1 > 16/27`), so the tie sits on a non-maximal triple there.
The rigidity step beyond `g*`: at the relaxation corner `e₁ = 12` forces all
twelve outside coordinates to `±1` and `e₃ = 4` forces the four outside sign
classes to be distinct, and then the four unit-norm quadrics are INCONSISTENT
— summing the four even-class equations gives `0 = −4`
(`fourEvenSignVectors_unitNorm_inconsistent`).  Converting that equality-case
kill into a floor strictly above `31/150` needs a quantitative perturbation of
the tightness forcing, which these inequality certificates do not perform;
that residual, and M7 itself, are left open and named.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.MaximalVolume
import Gtz.Reduction.RealVolumeFloor
import Gtz.Design.FrameConservation
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.TripleCubicCriterion
import Gtz.Quantitative.GTransformGate
import Gtz.Quantitative.HollowInvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. Scalar certificates: the floor cubics, the transform, the σ-caps -/

/-- **The relaxation cubic and the floor cubic are the same object.**  Under the
substitution `u = (7 − 3x)/(3x)` (i.e. `x = 7/(3(1+u))`, the eigenvalue
dictionary between the outside mass `R` and the picked Gram `Γ`), the
relaxation cubic `u³ − 12u² + 18u − 4` becomes `−7` times the floor cubic
`C(x) = 135x³ − 405x² + 315x − 49`, cleared of denominators.  So the largest
root `u* ≈ 10.28822` of the former corresponds exactly to the smallest root
`g* ≈ 0.2067052` of the latter. -/
theorem relaxationCubic_image_eq_cauchyBinetFloorCubic_sevenThree (floorValue : ℝ) :
    (7 - 3 * floorValue) ^ 3 - 12 * (3 * floorValue) * (7 - 3 * floorValue) ^ 2
        + 18 * (3 * floorValue) ^ 2 * (7 - 3 * floorValue) - 4 * (3 * floorValue) ^ 3
      = -7 * (135 * floorValue ^ 3 - 405 * floorValue ^ 2 + 315 * floorValue - 49) := by
  ring

/-- The floor cubic is negative at the landed rational floor `31/150`: the true
Cauchy–Binet floor `g*` lies strictly ABOVE `31/150`.  Exact value
`C(31/150) = −159/25000`. -/
theorem cauchyBinetFloorCubic_sevenThree_neg_at_landedFloor :
    135 * ((31 : ℝ) / 150) ^ 3 - 405 * ((31 : ℝ) / 150) ^ 2 + 315 * ((31 : ℝ) / 150) - 49
      = -(159 / 25000) := by
  norm_num

/-- The floor cubic is positive at `21/100`: the true Cauchy–Binet floor `g*`
lies strictly BELOW `0.21`.  Together with the previous sign this brackets
`g* ∈ (31/150, 21/100)`. -/
theorem cauchyBinetFloorCubic_sevenThree_pos_at_upperBracket :
    0 < 135 * ((21 : ℝ) / 100) ^ 3 - 405 * ((21 : ℝ) / 100) ^ 2 + 315 * ((21 : ℝ) / 100) - 49 := by
  norm_num

/-- The `(6,3)` floor cubic `5x³ − 15x² + 12x − 2` (whose smallest root is the
exact `(6,3)` relaxation floor `(5 − √15)/5 ≈ 0.22540`) is negative at the
landed rational floor `9/40`: exact value `C₆(9/40) = −31/12800`. -/
theorem cauchyBinetFloorCubic_sixThree_neg_at_landedFloor :
    5 * ((9 : ℝ) / 40) ^ 3 - 15 * ((9 : ℝ) / 40) ^ 2 + 12 * ((9 : ℝ) / 40) - 2
      = -(31 / 12800) := by
  norm_num

/-- The `(6,3)` floor cubic is positive at `1/4`: together with the previous
sign, the exact `(6,3)` relaxation floor is bracketed in `(9/40, 1/4)`. -/
theorem cauchyBinetFloorCubic_sixThree_pos_at_quarter :
    0 < 5 * ((1 : ℝ) / 4) ^ 3 - 15 * ((1 : ℝ) / 4) ^ 2 + 12 * ((1 : ℝ) / 4) - 2 := by
  norm_num

/-- **The σ-cap scalar core at `(7,3)`.**  The trace gate `38σ − 24 ≤ 90P`, the
AM–GM certificate `27P² ≤ σ³`, the correlation range `σ ≤ 3` and strict
positivity of the Gram determinant `1 − σ + 2P` force `σ ≤ 4/3`.  The engine is
the EXACT factorization `300σ³ − (38σ − 24)² = 300(σ − 12/25)(σ − 4/3)(σ − 3)`:
on `(4/3, 3)` the right side is negative while squaring the gate makes the left
side nonnegative, and the isolated coherent corner `σ = 3, P = 1` is killed by
the strict determinant. -/
theorem squareSum_le_fourThirds_of_traceGate {squareSum tripleProduct : ℝ}
    (htraceGate : 38 * squareSum - 24 ≤ 90 * tripleProduct)
    (hamgm : 27 * tripleProduct ^ 2 ≤ squareSum ^ 3)
    (hthree : squareSum ≤ 3)
    (hdetPos : 0 < 1 - squareSum + 2 * tripleProduct) :
    squareSum ≤ 4 / 3 := by
  by_contra hlarge
  rw [not_le] at hlarge
  have hgatePos : (0 : ℝ) < 38 * squareSum - 24 := by linarith
  have hsquared : (38 * squareSum - 24) ^ 2 ≤ (90 * tripleProduct) ^ 2 := by
    have hproductPos : (0 : ℝ) < 90 * tripleProduct := lt_of_lt_of_le hgatePos htraceGate
    nlinarith [htraceGate, hgatePos, hproductPos]
  have hcubicNonneg : 0 ≤ 300 * squareSum ^ 3 - (38 * squareSum - 24) ^ 2 := by
    nlinarith [hamgm, hsquared]
  have hfactored : 300 * squareSum ^ 3 - (38 * squareSum - 24) ^ 2
      = 300 * ((squareSum - 12 / 25) * ((squareSum - 4 / 3) * (squareSum - 3))) := by
    ring
  have hproductNonneg :
      0 ≤ (squareSum - 12 / 25) * ((squareSum - 4 / 3) * (squareSum - 3)) := by
    nlinarith [hcubicNonneg, hfactored]
  have hfirstPos : (0 : ℝ) < squareSum - 12 / 25 := by linarith
  have hsecondPos : (0 : ℝ) < squareSum - 4 / 3 := by linarith
  have htailNonneg : 0 ≤ (squareSum - 4 / 3) * (squareSum - 3) :=
    (mul_nonneg_iff_of_pos_left hfirstPos).mp hproductNonneg
  have hlastNonneg : 0 ≤ squareSum - 3 :=
    (mul_nonneg_iff_of_pos_left hsecondPos).mp htailNonneg
  have hthreeEq : squareSum = 3 := le_antisymm hthree (by linarith)
  rw [hthreeEq] at htraceGate hamgm hdetPos
  -- at σ = 3: the gate gives P ≥ 1, the determinant gives P > 1, AM–GM gives P² ≤ 1
  nlinarith [htraceGate, hamgm, hdetPos]

/-- **The σ-cap scalar core at `(6,3)`.**  Same shape as the `(7,3)` cap with
the trace gate `5σ − 3 ≤ 12P`, through the exact factorization
`16σ³ − 3(5σ − 3)² = (σ − 3)(16σ² − 27σ + 9)` and the linearization
`16σ² − 27σ + 9 = 16(σ − 5/4)² + 13σ − 16 > 0` on `σ > 5/4`. -/
theorem squareSum_le_fiveFourths_of_traceGate {squareSum tripleProduct : ℝ}
    (htraceGate : 5 * squareSum - 3 ≤ 12 * tripleProduct)
    (hamgm : 27 * tripleProduct ^ 2 ≤ squareSum ^ 3)
    (hthree : squareSum ≤ 3)
    (hdetPos : 0 < 1 - squareSum + 2 * tripleProduct) :
    squareSum ≤ 5 / 4 := by
  by_contra hlarge
  rw [not_le] at hlarge
  have hgatePos : (0 : ℝ) < 5 * squareSum - 3 := by linarith
  have hsquared : (5 * squareSum - 3) ^ 2 ≤ (12 * tripleProduct) ^ 2 := by
    have hproductPos : (0 : ℝ) < 12 * tripleProduct := lt_of_lt_of_le hgatePos htraceGate
    nlinarith [htraceGate, hgatePos, hproductPos]
  have hcubicNonneg : 0 ≤ 16 * squareSum ^ 3 - 3 * (5 * squareSum - 3) ^ 2 := by
    nlinarith [hamgm, hsquared]
  have hfactored : 16 * squareSum ^ 3 - 3 * (5 * squareSum - 3) ^ 2
      = (squareSum - 3) * (16 * squareSum ^ 2 - 27 * squareSum + 9) := by
    ring
  have hquadPos : (0 : ℝ) < 16 * squareSum ^ 2 - 27 * squareSum + 9 := by
    nlinarith [sq_nonneg (squareSum - 5 / 4)]
  have hlastNonneg : 0 ≤ squareSum - 3 := by
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [hcubicNonneg, hfactored, mul_neg_of_neg_of_pos (by linarith : squareSum - 3 < 0)
      hquadPos]
  have hthreeEq : squareSum = 3 := le_antisymm hthree (by linarith)
  rw [hthreeEq] at htraceGate hamgm hdetPos
  nlinarith [htraceGate, hamgm, hdetPos]

/-- **The four-sign-class rigidity kill.**  At the Cauchy–Binet relaxation
corner, tightness of `e₁ = 12` forces every outside coordinate to `±1` and
tightness of `e₃ = 4` forces the four outside sign vectors into the four
DISTINCT even classes `(+++), (+−−), (−+−), (−−+)`.  Unit norm of an outside
atom `x` against the picked Gram reads `3 + 2(γ₀₁q₀q₁ + γ₀₂q₀q₂ + γ₁₂q₁q₂) = 1`
per class.  The four resulting equations are INCONSISTENT for every value of
the three correlations: the class products sum to zero columnwise, so summing
gives `0 = −4`.  This is the parity obstruction that must push the true floor
strictly above `g*`; quantifying it is the named open residual. -/
theorem fourEvenSignVectors_unitNorm_inconsistent (gramOne gramTwo gramThree : ℝ)
    (hallPlus : 3 + 2 * (gramOne + gramTwo + gramThree) = 1)
    (hfirstClass : 3 + 2 * (gramOne - gramTwo - gramThree) = 1)
    (hsecondClass : 3 + 2 * (-gramOne + gramTwo - gramThree) = 1)
    (hthirdClass : 3 + 2 * (-gramOne - gramTwo + gramThree) = 1) : False := by
  linarith

/-- The tetrahedral tie Gram: the all-`(−1/3)` correlation matrix of a tetrapod
triple has determinant `16/27` — the calibration point of conjecture M7
(spectrum `(1/3, 4/3, 4/3)`, so `λ_min` is exactly `1/3` there). -/
theorem det_tetrahedralCorrelationThree :
    (!![(1 : ℝ), -(1 / 3), -(1 / 3); -(1 / 3), 1, -(1 / 3); -(1 / 3), -(1 / 3), 1]).det
      = 16 / 27 := by
  rw [Matrix.det_fin_three]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- The tetrapod unit triple (three even-sign vertices of the cube, normalized
by `√3`) has squared volume `16/27` — strictly below the orthonormal basis
triple's squared volume `1`, so on the basis-plus-tetrapod witness the
maximal-volume triple is the BASIS, and the tetrahedral tie sits on a
non-maximal triple. -/
theorem sq_det_tetrapodUnitTriple :
    ((Real.sqrt 3)⁻¹ • !![(1 : ℝ), 1, 1; 1, -1, -1; -1, 1, -1]).det ^ 2 = 16 / 27 := by
  have hsign : (!![(1 : ℝ), 1, 1; 1, -1, -1; -1, 1, -1]).det = 4 := by
    rw [Matrix.det_fin_three]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
  rw [Matrix.det_smul, hsign, Fintype.card_fin, mul_pow, ← pow_mul, inv_pow,
    show (3 * 2 : ℕ) = 2 * 3 by norm_num, pow_mul,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-! ## 2. The exchange layer: every square row-submatrix of the solve matrix -/

/-- **THE UNIFIED EXCHANGE BOUND.**  At a maximal-volume pick, EVERY square
row-submatrix of the solve matrix has determinant in `[−1, 1]`: a repeated row
gives determinant zero, and an injective row selection factors as
`(selected frame rows) · (picked block)⁻¹`, whose determinant is the volume
ratio that maximality caps at one.  Entries (`abs_solveMatrix_le_one_…`),
`2×2` minors and `3×3` minors of the outside coordinate block are all
instances, obtained by including basis rows of the solve matrix. -/
theorem abs_det_solveMatrix_submatrix_le_one_of_maximalVolume
    {frameSize selectionRank : ℕ} (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (pick : Fin selectionRank → Fin frameSize)
    (hunit : IsUnit (selectedFrameRows frame pick).det)
    (hmax : ∀ other : Fin selectionRank → Fin frameSize, Function.Injective other →
      |(selectedFrameRows frame other).det| ≤ |(selectedFrameRows frame pick).det|)
    (rows : Fin selectionRank → Fin frameSize) :
    |((solveMatrix frame pick).submatrix rows id).det| ≤ 1 := by
  by_cases hinjRows : Function.Injective rows
  · have hfactor : (solveMatrix frame pick).submatrix rows id
        = selectedFrameRows frame rows * (selectedFrameRows frame pick)⁻¹ := by
      ext rowSlot colSlot
      simp only [solveMatrix, selectedFrameRows, Matrix.submatrix_apply, Matrix.mul_apply, id_eq]
    rw [hfactor, Matrix.det_mul, abs_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_inv]
    have hdetPos : 0 < |(selectedFrameRows frame pick).det| := abs_pos.mpr hunit.ne_zero
    calc |(selectedFrameRows frame rows).det| * |(selectedFrameRows frame pick).det|⁻¹
        ≤ |(selectedFrameRows frame pick).det| * |(selectedFrameRows frame pick).det|⁻¹ :=
          mul_le_mul_of_nonneg_right (hmax rows hinjRows) (inv_nonneg.mpr (abs_nonneg _))
      _ = 1 := mul_inv_cancel₀ hdetPos.ne'
  · obtain ⟨leftSlot, rightSlot, hvalueEq, hslotNe⟩ := Function.not_injective_iff.mp hinjRows
    have hrowEq : ((solveMatrix frame pick).submatrix rows id) leftSlot
        = ((solveMatrix frame pick).submatrix rows id) rightSlot := by
      funext colIndex
      simp only [Matrix.submatrix_apply, hvalueEq]
    rw [Matrix.det_zero_of_row_eq hslotNe hrowEq, abs_zero]
    exact zero_le_one

/-- The solve-matrix entry at a picked row is the identity entry. -/
private theorem solveMatrix_entry_at_pick {frameSize selectionRank : ℕ}
    (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    (pick : Fin selectionRank → Fin frameSize)
    (hunit : IsUnit (selectedFrameRows frame pick).det) (slot colIndex : Fin selectionRank) :
    solveMatrix frame pick (pick slot) colIndex
      = (1 : Matrix (Fin selectionRank) (Fin selectionRank) ℝ) slot colIndex := by
  have hidentity := congrFun (congrFun (solveMatrix_submatrix_pick frame pick hunit) slot) colIndex
  simpa [Matrix.submatrix_apply] using hidentity

section TwoRowMinor

variable {frameSize : ℕ} (frame : Matrix (Fin frameSize) (Fin 3) ℝ)
  (pick : Fin 3 → Fin frameSize)

/-- The `(0,1)` two-row minor is the solve-submatrix determinant completed by
the third basis row. -/
private theorem twoRowMinor_col_zero_one
    (hunit : IsUnit (selectedFrameRows frame pick).det)
    (hmax : ∀ other : Fin 3 → Fin frameSize, Function.Injective other →
      |(selectedFrameRows frame other).det| ≤ |(selectedFrameRows frame pick).det|)
    (rowFirst rowSecond : Fin frameSize) :
    |solveMatrix frame pick rowFirst 0 * solveMatrix frame pick rowSecond 1
      - solveMatrix frame pick rowFirst 1 * solveMatrix frame pick rowSecond 0| ≤ 1 := by
  have hbound := abs_det_solveMatrix_submatrix_le_one_of_maximalVolume frame pick hunit hmax
    ![rowFirst, rowSecond, pick 2]
  have hbasisZero : solveMatrix frame pick (pick 2) 0 = 0 := by
    rw [solveMatrix_entry_at_pick frame pick hunit]
    exact Matrix.one_apply_ne (by decide)
  have hbasisOne : solveMatrix frame pick (pick 2) 1 = 0 := by
    rw [solveMatrix_entry_at_pick frame pick hunit]
    exact Matrix.one_apply_ne (by decide)
  have hbasisTwo : solveMatrix frame pick (pick 2) 2 = 1 := by
    rw [solveMatrix_entry_at_pick frame pick hunit]
    exact Matrix.one_apply_eq 2
  have hdetValue : ((solveMatrix frame pick).submatrix ![rowFirst, rowSecond, pick 2] id).det
      = solveMatrix frame pick rowFirst 0 * solveMatrix frame pick rowSecond 1
        - solveMatrix frame pick rowFirst 1 * solveMatrix frame pick rowSecond 0 := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, id_eq,
      hbasisZero, hbasisOne, hbasisTwo]
    ring
  rw [hdetValue] at hbound
  exact hbound

/-- The `(0,2)` two-row minor, via the middle basis row. -/
private theorem twoRowMinor_col_zero_two
    (hunit : IsUnit (selectedFrameRows frame pick).det)
    (hmax : ∀ other : Fin 3 → Fin frameSize, Function.Injective other →
      |(selectedFrameRows frame other).det| ≤ |(selectedFrameRows frame pick).det|)
    (rowFirst rowSecond : Fin frameSize) :
    |solveMatrix frame pick rowFirst 0 * solveMatrix frame pick rowSecond 2
      - solveMatrix frame pick rowFirst 2 * solveMatrix frame pick rowSecond 0| ≤ 1 := by
  have hbound := abs_det_solveMatrix_submatrix_le_one_of_maximalVolume frame pick hunit hmax
    ![rowFirst, rowSecond, pick 1]
  have hbasisZero : solveMatrix frame pick (pick 1) 0 = 0 := by
    rw [solveMatrix_entry_at_pick frame pick hunit]
    exact Matrix.one_apply_ne (by decide)
  have hbasisOne : solveMatrix frame pick (pick 1) 1 = 1 := by
    rw [solveMatrix_entry_at_pick frame pick hunit]
    exact Matrix.one_apply_eq 1
  have hbasisTwo : solveMatrix frame pick (pick 1) 2 = 0 := by
    rw [solveMatrix_entry_at_pick frame pick hunit]
    exact Matrix.one_apply_ne (by decide)
  have hdetValue : ((solveMatrix frame pick).submatrix ![rowFirst, rowSecond, pick 1] id).det
      = -(solveMatrix frame pick rowFirst 0 * solveMatrix frame pick rowSecond 2
          - solveMatrix frame pick rowFirst 2 * solveMatrix frame pick rowSecond 0) := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, id_eq,
      hbasisZero, hbasisOne, hbasisTwo]
    ring
  rw [hdetValue, abs_neg] at hbound
  exact hbound

/-- The `(1,2)` two-row minor, via the first basis row. -/
private theorem twoRowMinor_col_one_two
    (hunit : IsUnit (selectedFrameRows frame pick).det)
    (hmax : ∀ other : Fin 3 → Fin frameSize, Function.Injective other →
      |(selectedFrameRows frame other).det| ≤ |(selectedFrameRows frame pick).det|)
    (rowFirst rowSecond : Fin frameSize) :
    |solveMatrix frame pick rowFirst 1 * solveMatrix frame pick rowSecond 2
      - solveMatrix frame pick rowFirst 2 * solveMatrix frame pick rowSecond 1| ≤ 1 := by
  have hbound := abs_det_solveMatrix_submatrix_le_one_of_maximalVolume frame pick hunit hmax
    ![rowFirst, rowSecond, pick 0]
  have hbasisZero : solveMatrix frame pick (pick 0) 0 = 1 := by
    rw [solveMatrix_entry_at_pick frame pick hunit]
    exact Matrix.one_apply_eq 0
  have hbasisOne : solveMatrix frame pick (pick 0) 1 = 0 := by
    rw [solveMatrix_entry_at_pick frame pick hunit]
    exact Matrix.one_apply_ne (by decide)
  have hbasisTwo : solveMatrix frame pick (pick 0) 2 = 0 := by
    rw [solveMatrix_entry_at_pick frame pick hunit]
    exact Matrix.one_apply_ne (by decide)
  have hdetValue : ((solveMatrix frame pick).submatrix ![rowFirst, rowSecond, pick 0] id).det
      = solveMatrix frame pick rowFirst 1 * solveMatrix frame pick rowSecond 2
        - solveMatrix frame pick rowFirst 2 * solveMatrix frame pick rowSecond 1 := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, id_eq,
      hbasisZero, hbasisOne, hbasisTwo]
    ring
  rw [hdetValue] at hbound
  exact hbound

/-- **The two-row exchange bound, rank three.**  At a maximal-volume pick every
`2×2` minor of any two solve-matrix rows is in `[−1, 1]`: completing the two
rows with the basis row of the omitted column turns the minor into a `3×3`
solve-submatrix determinant, and the unified exchange bound applies.  These
eighteen bounds give `e₂(X_oᵀX_o) ≤ 18`, which the floor below does NOT need —
landed as exchange theory (the `e₂` constraint is inactive at the relaxation
corner). -/
theorem abs_twoRowMinor_solveMatrix_le_one_of_maximalVolume
    (hunit : IsUnit (selectedFrameRows frame pick).det)
    (hmax : ∀ other : Fin 3 → Fin frameSize, Function.Injective other →
      |(selectedFrameRows frame other).det| ≤ |(selectedFrameRows frame pick).det|)
    (rowFirst rowSecond : Fin frameSize) {colFirst colSecond : Fin 3}
    (hcolNe : colFirst ≠ colSecond) :
    |solveMatrix frame pick rowFirst colFirst * solveMatrix frame pick rowSecond colSecond
      - solveMatrix frame pick rowFirst colSecond * solveMatrix frame pick rowSecond colFirst|
      ≤ 1 := by
  fin_cases colFirst <;> fin_cases colSecond
  · exact absurd rfl hcolNe
  · exact twoRowMinor_col_zero_one frame pick hunit hmax rowFirst rowSecond
  · exact twoRowMinor_col_zero_two frame pick hunit hmax rowFirst rowSecond
  · rw [abs_sub_comm]
    exact twoRowMinor_col_zero_one frame pick hunit hmax rowFirst rowSecond
  · exact absurd rfl hcolNe
  · exact twoRowMinor_col_one_two frame pick hunit hmax rowFirst rowSecond
  · rw [abs_sub_comm]
    exact twoRowMinor_col_zero_two frame pick hunit hmax rowFirst rowSecond
  · rw [abs_sub_comm]
    exact twoRowMinor_col_one_two frame pick hunit hmax rowFirst rowSecond
  · exact absurd rfl hcolNe

end TwoRowMinor

/-! ## 3. Cauchy–Binet for a `4×3` block, and the trace bound -/

/-- **Cauchy–Binet, `4×3`.**  The Gram determinant of a four-row block in rank
three is the sum of the four squared `3×3` row minors.  Proved by brute
polynomial expansion — twelve variables, all cancellation exact. -/
theorem det_transpose_mul_self_four_rows_eq_sum_sq_minors
    (outsideBlock : Matrix (Fin 4) (Fin 3) ℝ) :
    (outsideBlockᵀ * outsideBlock).det
      = (outsideBlock.submatrix ![1, 2, 3] id).det ^ 2
        + (outsideBlock.submatrix ![0, 2, 3] id).det ^ 2
        + (outsideBlock.submatrix ![0, 1, 3] id).det ^ 2
        + (outsideBlock.submatrix ![0, 1, 2] id).det ^ 2 := by
  rw [Matrix.det_fin_three, Matrix.det_fin_three, Matrix.det_fin_three, Matrix.det_fin_three,
    Matrix.det_fin_three]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, id_eq, Fin.sum_univ_four]
  ring

/-- The trace of a Gram block whose entries are all in `[−1, 1]` is at most the
entry count. -/
theorem trace_transpose_mul_self_le_of_abs_entries_le_one {rowCount colCount : ℕ}
    (block : Matrix (Fin rowCount) (Fin colCount) ℝ)
    (hentries : ∀ rowIndex colIndex, |block rowIndex colIndex| ≤ 1) :
    Matrix.trace (blockᵀ * block) ≤ (rowCount : ℝ) * colCount := by
  have htraceSum : Matrix.trace (blockᵀ * block)
      = ∑ colIndex, ∑ rowIndex, block rowIndex colIndex * block rowIndex colIndex := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [htraceSum]
  calc ∑ colIndex : Fin colCount, ∑ rowIndex : Fin rowCount,
          block rowIndex colIndex * block rowIndex colIndex
      ≤ ∑ _colIndex : Fin colCount, ∑ _rowIndex : Fin rowCount, (1 : ℝ) := by
        refine Finset.sum_le_sum fun colIndex _ => Finset.sum_le_sum fun rowIndex _ => ?_
        have hsq : block rowIndex colIndex ^ 2 ≤ 1 :=
          (sq_le_one_iff_abs_le_one _).mpr (hentries rowIndex colIndex)
        nlinarith [hsq]
    _ = (colCount : ℝ) * rowCount := by
        simp [Finset.sum_const, Finset.card_univ, mul_comm]
    _ = (rowCount : ℝ) * colCount := by ring

/-! ## 4. The abstract floors: two exchange gates on a correlation matrix -/

/-- Diagonal entry of a shifted matrix. -/
private theorem sub_smul_one_apply_diag (gram : Matrix (Fin 3) (Fin 3) ℝ) (shift : ℝ)
    (index : Fin 3) : (gram - shift • 1) index index = gram index index - shift := by
  simp [Matrix.sub_apply, Matrix.smul_apply]

/-- Off-diagonal entry of a shifted matrix. -/
private theorem sub_smul_one_apply_off (gram : Matrix (Fin 3) (Fin 3) ℝ) (shift : ℝ)
    {rowIndex colIndex : Fin 3} (hne : rowIndex ≠ colIndex) :
    (gram - shift • 1) rowIndex colIndex = gram rowIndex colIndex := by
  simp [Matrix.sub_apply, Matrix.smul_apply, hne]

/-- The shifted determinant of a symmetric unit-diagonal `3×3` matrix, in
`(σ, P)` coordinates: `det(Γ − t·1) = (1−t)³ − (1−t)σ + 2P`. -/
private theorem det_sub_smul_one_of_symm_unitDiag {gram : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymmetric : gramᵀ = gram)
    (hdiagZero : gram 0 0 = 1) (hdiagOne : gram 1 1 = 1) (hdiagTwo : gram 2 2 = 1)
    (shift : ℝ) :
    (gram - shift • 1).det
      = (1 - shift) ^ 3
        - (1 - shift) * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
        + 2 * (gram 0 1 * gram 0 2 * gram 1 2) := by
  have hflipOne : gram 1 0 = gram 0 1 := congrFun (congrFun hsymmetric 0) 1
  have hflipTwo : gram 2 0 = gram 0 2 := congrFun (congrFun hsymmetric 0) 2
  have hflipThree : gram 2 1 = gram 1 2 := congrFun (congrFun hsymmetric 1) 2
  rw [Matrix.det_fin_three,
    sub_smul_one_apply_diag, sub_smul_one_apply_diag, sub_smul_one_apply_diag,
    sub_smul_one_apply_off gram shift (by decide : (0 : Fin 3) ≠ 1),
    sub_smul_one_apply_off gram shift (by decide : (0 : Fin 3) ≠ 2),
    sub_smul_one_apply_off gram shift (by decide : (1 : Fin 3) ≠ 0),
    sub_smul_one_apply_off gram shift (by decide : (1 : Fin 3) ≠ 2),
    sub_smul_one_apply_off gram shift (by decide : (2 : Fin 3) ≠ 0),
    sub_smul_one_apply_off gram shift (by decide : (2 : Fin 3) ≠ 1),
    hdiagZero, hdiagOne, hdiagTwo, hflipOne, hflipTwo, hflipThree]
  ring

/-- **THE ABSTRACT CAUCHY–BINET FLOOR, `(7,3)`.**  A symmetric unit-diagonal
`3×3` correlation matrix with positive determinant satisfying the TRACE GATE
`38σ − 24 ≤ 90P` and the VOLUME GATE `36σ − 22 ≤ 135P` (the two exchange
constraints of a `(7,3)`-uniform maximal-volume pick, in `(σ, P)` entry
coordinates) is positive definite past `31/150`.  Eigenvalue-free: the
elementary-symmetric criterion needs `e₂ = 3(1−t)² − σ > 0`, which the σ-cap
`σ ≤ 4/3` supplies, and `det = (1−t)³ − (1−t)σ + 2P > 0`, which is LINEAR in
`(σ, P)` with exact margin `159/3375000` at the gates' corner
`(σ, P) = (2/3, 2/135)`. -/
theorem posDef_sub_cauchyBinetFloor_of_exchangeGates_sevenThree
    {gram : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : gramᵀ = gram)
    (hdiagZero : gram 0 0 = 1) (hdiagOne : gram 1 1 = 1) (hdiagTwo : gram 2 2 = 1)
    (hdetPos : 0 < gram.det)
    (hentryRange : gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2 ≤ 3)
    (htraceGate : 38 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) - 24
      ≤ 90 * (gram 0 1 * gram 0 2 * gram 1 2))
    (hvolumeGate : 36 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) - 22
      ≤ 135 * (gram 0 1 * gram 0 2 * gram 1 2)) :
    (gram - (31 / 150 : ℝ) • 1).PosDef := by
  have hflipOne : gram 1 0 = gram 0 1 := congrFun (congrFun hsymmetric 0) 1
  have hflipTwo : gram 2 0 = gram 0 2 := congrFun (congrFun hsymmetric 0) 2
  have hflipThree : gram 2 1 = gram 1 2 := congrFun (congrFun hsymmetric 1) 2
  have hdetFormula : gram.det
      = (1 - (0 : ℝ)) ^ 3 - (1 - 0) * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
        + 2 * (gram 0 1 * gram 0 2 * gram 1 2) := by
    have hzeroShift := det_sub_smul_one_of_symm_unitDiag hsymmetric hdiagZero hdiagOne hdiagTwo 0
    rw [zero_smul, sub_zero] at hzeroShift
    exact hzeroShift
  have hdetCoord : 0 < 1 - (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
      + 2 * (gram 0 1 * gram 0 2 * gram 1 2) := by
    rw [hdetFormula] at hdetPos
    linarith [hdetPos]
  have hamgm : 27 * (gram 0 1 * gram 0 2 * gram 1 2) ^ 2
      ≤ (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) ^ 3 := by
    have hcube := twentySeven_mul_sq_tripleProduct_le_cube_squareSum
      (gram 0 1) (gram 0 2) (gram 1 2)
    nlinarith [hcube]
  have hsigmaCap := squareSum_le_fourThirds_of_traceGate htraceGate hamgm hentryRange hdetCoord
  have hsymShift : (gram - (31 / 150 : ℝ) • 1)ᵀ = gram - (31 / 150 : ℝ) • 1 := by
    rw [Matrix.transpose_sub, hsymmetric, Matrix.transpose_smul, Matrix.transpose_one]
  refine posDef_three_of_elementarySymmetric hsymShift ?_ ?_ ?_
  · rw [sub_smul_one_apply_diag, sub_smul_one_apply_diag, sub_smul_one_apply_diag,
      hdiagZero, hdiagOne, hdiagTwo]
    norm_num
  · rw [sub_smul_one_apply_diag, sub_smul_one_apply_diag, sub_smul_one_apply_diag,
      sub_smul_one_apply_off gram _ (by decide : (0 : Fin 3) ≠ 1),
      sub_smul_one_apply_off gram _ (by decide : (0 : Fin 3) ≠ 2),
      sub_smul_one_apply_off gram _ (by decide : (1 : Fin 3) ≠ 0),
      sub_smul_one_apply_off gram _ (by decide : (1 : Fin 3) ≠ 2),
      sub_smul_one_apply_off gram _ (by decide : (2 : Fin 3) ≠ 0),
      sub_smul_one_apply_off gram _ (by decide : (2 : Fin 3) ≠ 1),
      hdiagZero, hdiagOne, hdiagTwo, hflipOne, hflipTwo, hflipThree]
    nlinarith [hsigmaCap]
  · rw [det_sub_smul_one_of_symm_unitDiag hsymmetric hdiagZero hdiagOne hdiagTwo]
    linarith [htraceGate, hvolumeGate]

/-- **THE ABSTRACT CAUCHY–BINET FLOOR, `(6,3)`.**  Same skeleton at share
`1/2`: the trace gate is `5σ − 3 ≤ 12P`, the volume gate degenerates to
`P ≥ 0`, the σ-cap is `5/4`, and the floor is `9/40`, with exact determinant
margin `31/64000` at the gates' corner `(σ, P) = (3/5, 0)`. -/
theorem posDef_sub_cauchyBinetFloor_of_exchangeGates_sixThree
    {gram : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : gramᵀ = gram)
    (hdiagZero : gram 0 0 = 1) (hdiagOne : gram 1 1 = 1) (hdiagTwo : gram 2 2 = 1)
    (hdetPos : 0 < gram.det)
    (hentryRange : gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2 ≤ 3)
    (htraceGate : 5 * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) - 3
      ≤ 12 * (gram 0 1 * gram 0 2 * gram 1 2))
    (hproductGate : 0 ≤ gram 0 1 * gram 0 2 * gram 1 2) :
    (gram - (9 / 40 : ℝ) • 1).PosDef := by
  have hflipOne : gram 1 0 = gram 0 1 := congrFun (congrFun hsymmetric 0) 1
  have hflipTwo : gram 2 0 = gram 0 2 := congrFun (congrFun hsymmetric 0) 2
  have hflipThree : gram 2 1 = gram 1 2 := congrFun (congrFun hsymmetric 1) 2
  have hdetFormula : gram.det
      = (1 - (0 : ℝ)) ^ 3 - (1 - 0) * (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
        + 2 * (gram 0 1 * gram 0 2 * gram 1 2) := by
    have hzeroShift := det_sub_smul_one_of_symm_unitDiag hsymmetric hdiagZero hdiagOne hdiagTwo 0
    rw [zero_smul, sub_zero] at hzeroShift
    exact hzeroShift
  have hdetCoord : 0 < 1 - (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2)
      + 2 * (gram 0 1 * gram 0 2 * gram 1 2) := by
    rw [hdetFormula] at hdetPos
    linarith [hdetPos]
  have hamgm : 27 * (gram 0 1 * gram 0 2 * gram 1 2) ^ 2
      ≤ (gram 0 1 ^ 2 + gram 0 2 ^ 2 + gram 1 2 ^ 2) ^ 3 := by
    have hcube := twentySeven_mul_sq_tripleProduct_le_cube_squareSum
      (gram 0 1) (gram 0 2) (gram 1 2)
    nlinarith [hcube]
  have hsigmaCap := squareSum_le_fiveFourths_of_traceGate htraceGate hamgm hentryRange hdetCoord
  have hsymShift : (gram - (9 / 40 : ℝ) • 1)ᵀ = gram - (9 / 40 : ℝ) • 1 := by
    rw [Matrix.transpose_sub, hsymmetric, Matrix.transpose_smul, Matrix.transpose_one]
  refine posDef_three_of_elementarySymmetric hsymShift ?_ ?_ ?_
  · rw [sub_smul_one_apply_diag, sub_smul_one_apply_diag, sub_smul_one_apply_diag,
      hdiagZero, hdiagOne, hdiagTwo]
    norm_num
  · rw [sub_smul_one_apply_diag, sub_smul_one_apply_diag, sub_smul_one_apply_diag,
      sub_smul_one_apply_off gram _ (by decide : (0 : Fin 3) ≠ 1),
      sub_smul_one_apply_off gram _ (by decide : (0 : Fin 3) ≠ 2),
      sub_smul_one_apply_off gram _ (by decide : (1 : Fin 3) ≠ 0),
      sub_smul_one_apply_off gram _ (by decide : (1 : Fin 3) ≠ 2),
      sub_smul_one_apply_off gram _ (by decide : (2 : Fin 3) ≠ 0),
      sub_smul_one_apply_off gram _ (by decide : (2 : Fin 3) ≠ 1),
      hdiagZero, hdiagOne, hdiagTwo, hflipOne, hflipTwo, hflipThree]
    nlinarith [hsigmaCap]
  · rw [det_sub_smul_one_of_symm_unitDiag hsymmetric hdiagZero hdiagOne hdiagTwo]
    linarith [htraceGate, hproductGate]

/-! ## 5. The shared design plumbing: frame law, solve Gram, adjugate, row split -/

/-- A design with nondegenerate atoms admits an injective nonsingular selection
of its UNIT-atom rows: the unit block is the raw block under an invertible
diagonal congruence. -/
theorem exists_injective_pick_det_unitAtomRows_ne_zero {m k : ℕ} (D : WeightedDesign m k)
    (hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex)) :
    ∃ pick : Fin k → Fin m, Function.Injective pick ∧
      (selectedFrameRows (unitAtomRows D) pick).det ≠ 0 := by
  obtain ⟨pick, hinj, hrawDet⟩ := exists_injective_pick_det_atomRowMatrix_ne_zero D
  refine ⟨pick, hinj, ?_⟩
  have hdiagFactor : selectedFrameRows (unitAtomRows D) pick
      = Matrix.diagonal (fun slot => (Real.sqrt (leverageOf (D.atom (pick slot))))⁻¹)
        * selectedFrameRows (atomRowMatrix D) pick := by
    ext rowSlot colSlot
    rw [Matrix.diagonal_mul]
    simp only [selectedFrameRows, Matrix.submatrix_apply, unitAtomRows, Matrix.of_apply,
      unitAtom, Pi.smul_apply, smul_eq_mul, atomRowMatrix, id_eq]
  rw [hdiagFactor, Matrix.det_mul, Matrix.det_diagonal]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun slot _ => ?_) hrawDet
  exact inv_ne_zero (Real.sqrt_pos.mpr (hlevPos (pick slot))).ne'

/-- **A maximal-volume pick of the unit-atom rows exists** on any design with
nondegenerate atoms: the diagonal congruence transfers a nonsingular witness
from the raw rows, and the finitely many injective picks contain a maximizer. -/
theorem exists_maximalVolume_pick_unitAtomRows {m k : ℕ} (D : WeightedDesign m k)
    (hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex)) :
    ∃ pick : Fin k → Fin m, Function.Injective pick ∧
      (selectedFrameRows (unitAtomRows D) pick).det ≠ 0 ∧
      ∀ other : Fin k → Fin m, Function.Injective other →
        |(selectedFrameRows (unitAtomRows D) other).det|
          ≤ |(selectedFrameRows (unitAtomRows D) pick).det| := by
  obtain ⟨witnessPick, hwitnessInj, hwitnessDet⟩ :=
    exists_injective_pick_det_unitAtomRows_ne_zero D hlevPos
  exact exists_maximalVolumePick_of_witness (unitAtomRows D) hwitnessInj hwitnessDet

/-- The unit picked Gram is the picked block of the direction Gram matrix. -/
theorem unitPickGram_eq_directionGramMatrix_submatrix {m k : ℕ} (D : WeightedDesign m k)
    (pick : Fin k → Fin m) :
    selectedFrameRows (unitAtomRows D) pick * (selectedFrameRows (unitAtomRows D) pick)ᵀ
      = (directionGramMatrix D).submatrix pick pick := by
  rw [directionGramMatrix_eq_mul_transpose, projectionBlock_eq_selectedFrameRows_mul_transpose]

/-- An entry of the unit picked Gram is the direction correlation of the two
picked atoms. -/
private theorem unitPickGram_entry {m k : ℕ} (D : WeightedDesign m k) (pick : Fin k → Fin m)
    (rowSlot colSlot : Fin k) :
    (selectedFrameRows (unitAtomRows D) pick * (selectedFrameRows (unitAtomRows D) pick)ᵀ)
        rowSlot colSlot
      = directionGram D (pick rowSlot) (pick colSlot) := by
  rw [Matrix.mul_apply, directionGram, dotProduct]
  exact Finset.sum_congr rfl fun coord _ => rfl

/-- The unit picked Gram is symmetric. -/
private theorem unitPickGram_transpose {m k : ℕ} (D : WeightedDesign m k)
    (pick : Fin k → Fin m) :
    (selectedFrameRows (unitAtomRows D) pick * (selectedFrameRows (unitAtomRows D) pick)ᵀ)ᵀ
      = selectedFrameRows (unitAtomRows D) pick * (selectedFrameRows (unitAtomRows D) pick)ᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- **The frame law of the unit rows at uniform share**: `UᵀU = s⁻¹·1`. -/
private theorem transpose_mul_unitAtomRows_of_uniformShare {m k : ℕ} (D : WeightedDesign m k)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hsharePos : 0 < shareValue) :
    (unitAtomRows D)ᵀ * unitAtomRows D = shareValue⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  calc (unitAtomRows D)ᵀ * unitAtomRows D
      = ∑ atomIndex, atomMatrix (unitAtomRows D atomIndex) :=
        transpose_mul_self_eq_sum_rows (unitAtomRows D)
    _ = shareValue⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ) :=
        sum_atomMatrix_unitAtom_of_uniformShare D huniform hsharePos

/-- **The solve Gram is the rescaled inverse picked Gram**:
`YᵀY = s⁻¹ · (B Bᵀ)⁻¹` at uniform share `s`, where `Y` is the solve matrix and
`B` the picked block of the unit rows.  This is the isotropy-in-coordinates
identity `R + 1 = s⁻¹ Γ⁻¹` of the pen campaign. -/
private theorem solveGram_eq_smul_inv_unitPickGram {m k : ℕ} (D : WeightedDesign m k)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hsharePos : 0 < shareValue) (pick : Fin k → Fin m) :
    (solveMatrix (unitAtomRows D) pick)ᵀ * solveMatrix (unitAtomRows D) pick
      = shareValue⁻¹ • (selectedFrameRows (unitAtomRows D) pick
          * (selectedFrameRows (unitAtomRows D) pick)ᵀ)⁻¹ := by
  rw [solveMatrix, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (unitAtomRows D)ᵀ,
    transpose_mul_unitAtomRows_of_uniformShare D huniform hsharePos,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]

/-- The determinant of the unit picked Gram is a nonzero square. -/
private theorem det_unitPickGram_pos {m k : ℕ} (D : WeightedDesign m k)
    {pick : Fin k → Fin m}
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det) :
    0 < (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ).det := by
  rw [Matrix.det_mul, Matrix.det_transpose, ← sq]
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hunit.ne_zero))

/-- **The adjugate of the unit picked Gram is the rescaled solve Gram**:
`adj(B Bᵀ) = det(B Bᵀ) · s · YᵀY`.  Cramer's rule, with the inverse supplied by
the solve-Gram identity. -/
private theorem adjugate_unitPickGram {m k : ℕ} (D : WeightedDesign m k)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hsharePos : 0 < shareValue) {pick : Fin k → Fin m}
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det) :
    (selectedFrameRows (unitAtomRows D) pick
        * (selectedFrameRows (unitAtomRows D) pick)ᵀ).adjugate
      = (selectedFrameRows (unitAtomRows D) pick
          * (selectedFrameRows (unitAtomRows D) pick)ᵀ).det
        • (shareValue • ((solveMatrix (unitAtomRows D) pick)ᵀ
            * solveMatrix (unitAtomRows D) pick)) := by
  set pickGram := selectedFrameRows (unitAtomRows D) pick
    * (selectedFrameRows (unitAtomRows D) pick)ᵀ with hpickGramDef
  have hunitPickGram : IsUnit pickGram.det := by
    rw [hpickGramDef, Matrix.det_mul, Matrix.det_transpose]
    exact hunit.mul hunit
  have hmulLeft : pickGram * (shareValue • ((solveMatrix (unitAtomRows D) pick)ᵀ
      * solveMatrix (unitAtomRows D) pick)) = 1 := by
    rw [solveGram_eq_smul_inv_unitPickGram D huniform hsharePos pick, smul_smul,
      mul_inv_cancel₀ hsharePos.ne', one_smul, ← hpickGramDef,
      Matrix.mul_nonsing_inv pickGram hunitPickGram]
  calc pickGram.adjugate
      = pickGram.adjugate * 1 := (Matrix.mul_one _).symm
    _ = pickGram.adjugate * (pickGram * (shareValue • ((solveMatrix (unitAtomRows D) pick)ᵀ
          * solveMatrix (unitAtomRows D) pick))) := by rw [hmulLeft]
    _ = (pickGram.adjugate * pickGram) * (shareValue • ((solveMatrix (unitAtomRows D) pick)ᵀ
          * solveMatrix (unitAtomRows D) pick)) := (Matrix.mul_assoc _ _ _).symm
    _ = (pickGram.det • 1) * (shareValue • ((solveMatrix (unitAtomRows D) pick)ᵀ
          * solveMatrix (unitAtomRows D) pick)) := by rw [Matrix.adjugate_mul]
    _ = pickGram.det • (shareValue • ((solveMatrix (unitAtomRows D) pick)ᵀ
          * solveMatrix (unitAtomRows D) pick)) := by rw [Matrix.smul_mul, Matrix.one_mul]

/-- The trace of a `3×3` adjugate is the second elementary symmetric function
of the matrix — the sum of the three diagonal cofactors. -/
private theorem trace_adjugate_three (block : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace block.adjugate
      = (block 1 1 * block 2 2 - block 1 2 * block 2 1)
        + (block 0 0 * block 2 2 - block 0 2 * block 2 0)
        + (block 0 0 * block 1 1 - block 0 1 * block 1 0) := by
  rw [Matrix.adjugate_fin_three, Matrix.trace_fin_three_of]

/-- **The row split of the solve Gram**: `YᵀY = 1 + X_oᵀX_o`, with the picked
rows contributing the identity (they are basis rows of the solve matrix) and
`X_o` the outside coordinate block along any enumeration of the complement. -/
private theorem solveGram_split {frameSize selectionRank outCard : ℕ}
    (frame : Matrix (Fin frameSize) (Fin selectionRank) ℝ)
    {pick : Fin selectionRank → Fin frameSize} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows frame pick).det)
    {outEnum : Fin outCard → Fin frameSize} (houtInj : Function.Injective outEnum)
    (himage : Finset.image outEnum Finset.univ = (Finset.image pick Finset.univ)ᶜ) :
    (solveMatrix frame pick)ᵀ * solveMatrix frame pick
      = 1 + ((solveMatrix frame pick).submatrix outEnum id)ᵀ
          * (solveMatrix frame pick).submatrix outEnum id := by
  ext leftCoord rightCoord
  rw [Matrix.mul_apply, Matrix.add_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  rw [← Finset.sum_add_sum_compl (Finset.image pick Finset.univ)
      (fun rowIndex => solveMatrix frame pick rowIndex leftCoord
        * solveMatrix frame pick rowIndex rightCoord),
    ← himage, Finset.sum_image (fun _ _ _ _ heq => houtInj heq),
    Finset.sum_image (fun _ _ _ _ heq => hinj heq)]
  congr 1
  calc ∑ slot, solveMatrix frame pick (pick slot) leftCoord
        * solveMatrix frame pick (pick slot) rightCoord
      = ∑ slot, (1 : Matrix (Fin selectionRank) (Fin selectionRank) ℝ) slot leftCoord
          * (1 : Matrix (Fin selectionRank) (Fin selectionRank) ℝ) slot rightCoord :=
        Finset.sum_congr rfl fun slot _ => by
          rw [solveMatrix_entry_at_pick frame pick hunit slot leftCoord,
            solveMatrix_entry_at_pick frame pick hunit slot rightCoord]
    _ = ((1 : Matrix (Fin selectionRank) (Fin selectionRank) ℝ)ᵀ
          * (1 : Matrix (Fin selectionRank) (Fin selectionRank) ℝ)) leftCoord rightCoord := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun slot _ => rfl
    _ = (1 : Matrix (Fin selectionRank) (Fin selectionRank) ℝ) leftCoord rightCoord := by
        rw [Matrix.transpose_one, Matrix.one_mul]

/-- The factored determinant of the shifted solve Gram:
`det(YᵀY − 1) = det(BBᵀ)⁻¹ · det(s⁻¹·1 − BBᵀ)`. -/
private theorem det_solveGram_sub_one {m k : ℕ} (D : WeightedDesign m k)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hsharePos : 0 < shareValue) {pick : Fin k → Fin m}
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det) :
    ((solveMatrix (unitAtomRows D) pick)ᵀ * solveMatrix (unitAtomRows D) pick - 1).det
      = (selectedFrameRows (unitAtomRows D) pick
          * (selectedFrameRows (unitAtomRows D) pick)ᵀ).det⁻¹
        * (shareValue⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)
            - selectedFrameRows (unitAtomRows D) pick
              * (selectedFrameRows (unitAtomRows D) pick)ᵀ).det := by
  set pickGram := selectedFrameRows (unitAtomRows D) pick
    * (selectedFrameRows (unitAtomRows D) pick)ᵀ with hpickGramDef
  have hunitPickGram : IsUnit pickGram.det := by
    rw [hpickGramDef, Matrix.det_mul, Matrix.det_transpose]
    exact hunit.mul hunit
  have hfactor : (solveMatrix (unitAtomRows D) pick)ᵀ * solveMatrix (unitAtomRows D) pick - 1
      = pickGram⁻¹ * (shareValue⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ) - pickGram) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      Matrix.nonsing_inv_mul pickGram hunitPickGram,
      solveGram_eq_smul_inv_unitPickGram D huniform hsharePos pick]
  rw [hfactor, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

/-! ## 6. The `(7,3)` assembly -/

section SevenThreeAssembly

variable (D : WeightedDesign 7 3)

/-- The two exchange gates and Gram positivity of a `(7,3)`-uniform
maximal-volume pick, in `(σ, P)` coordinates.  The trace gate encodes
`e₁(X_oᵀX_o) ≤ 12` (twelve one-row exchange bounds), the volume gate
`e₃(X_oᵀX_o) ≤ 4` (four three-row exchange bounds through Cauchy–Binet). -/
private theorem exchangeGates_sevenThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pick : Fin 3 → Fin 7} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 7, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    0 < 1 - directionTripleSigma D (pick 0) (pick 1) (pick 2)
        + 2 * directionTripleProduct D (pick 0) (pick 1) (pick 2)
    ∧ 38 * directionTripleSigma D (pick 0) (pick 1) (pick 2) - 24
        ≤ 90 * directionTripleProduct D (pick 0) (pick 1) (pick 2)
    ∧ 36 * directionTripleSigma D (pick 0) (pick 1) (pick 2) - 22
        ≤ 135 * directionTripleProduct D (pick 0) (pick 1) (pick 2) := by
  classical
  have hsharePos : (0 : ℝ) < 3 / 7 := by norm_num
  have hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  set solveY := solveMatrix (unitAtomRows D) pick with hsolveDef
  set pickGram := selectedFrameRows (unitAtomRows D) pick
    * (selectedFrameRows (unitAtomRows D) pick)ᵀ with hpickGramDef
  -- entry dictionary
  have hsymmG : pickGramᵀ = pickGram := unitPickGram_transpose D pick
  have hentry : ∀ rowSlot colSlot : Fin 3,
      pickGram rowSlot colSlot = directionGram D (pick rowSlot) (pick colSlot) :=
    fun rowSlot colSlot => unitPickGram_entry D pick rowSlot colSlot
  have hdiagZero : pickGram 0 0 = 1 := by
    rw [hentry 0 0]; exact directionGram_self D (hlevPos (pick 0))
  have hdiagOne : pickGram 1 1 = 1 := by
    rw [hentry 1 1]; exact directionGram_self D (hlevPos (pick 1))
  have hdiagTwo : pickGram 2 2 = 1 := by
    rw [hentry 2 2]; exact directionGram_self D (hlevPos (pick 2))
  have hsigmaEq : directionTripleSigma D (pick 0) (pick 1) (pick 2)
      = pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2 := by
    rw [directionTripleSigma, hentry 0 1, hentry 0 2, hentry 1 2]
  have hproductEq : directionTripleProduct D (pick 0) (pick 1) (pick 2)
      = pickGram 0 1 * pickGram 0 2 * pickGram 1 2 := by
    rw [directionTripleProduct, hentry 0 1, hentry 0 2, hentry 1 2]
  -- determinant of the picked Gram in coordinates
  have hGdetPos : 0 < pickGram.det := det_unitPickGram_pos D hunit
  have hdetCoord : pickGram.det
      = 1 - directionTripleSigma D (pick 0) (pick 1) (pick 2)
        + 2 * directionTripleProduct D (pick 0) (pick 1) (pick 2) := by
    have hshift := det_sub_smul_one_of_symm_unitDiag hsymmG hdiagZero hdiagOne hdiagTwo 0
    rw [zero_smul, sub_zero] at hshift
    rw [hshift, hsigmaEq, hproductEq]
    ring
  -- the complement enumeration
  set outSet := ((Finset.image pick Finset.univ)ᶜ : Finset (Fin 7)) with houtSetDef
  have hcardOut : outSet.card = 4 := by
    rw [houtSetDef, Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simp
  set outEnum := fun outIndex => outSet.orderEmbOfFin hcardOut outIndex with houtEnumDef
  have houtInj : Function.Injective outEnum := fun _ _ heq =>
    (outSet.orderEmbOfFin hcardOut).injective heq
  have himageOut : Finset.image outEnum Finset.univ = (Finset.image pick Finset.univ)ᶜ := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← houtSetDef]
    exact Finset.range_orderEmbOfFin outSet hcardOut
  have hsplit := solveGram_split (unitAtomRows D) hinj hunit houtInj himageOut
  set outsideBlock := solveY.submatrix outEnum id with houtsideBlockDef
  -- entry bounds on the whole solve matrix
  have hallEntries : ∀ rowIndex colIndex, |solveY rowIndex colIndex| ≤ 1 :=
    fun rowIndex colIndex =>
      abs_solveMatrix_le_one_of_maximalVolume_row (unitAtomRows D) pick hinj hunit hmax
        rowIndex colIndex
  -- E1: the solve Gram trace is at most 15
  have htraceSolve : Matrix.trace (solveYᵀ * solveY) ≤ 15 := by
    rw [hsplit, Matrix.trace_add, Matrix.trace_one]
    have houtTrace : Matrix.trace (outsideBlockᵀ * outsideBlock) ≤ (4 : ℝ) * 3 := by
      refine trace_transpose_mul_self_le_of_abs_entries_le_one outsideBlock
        fun rowIndex colIndex => ?_
      rw [houtsideBlockDef]
      simp only [Matrix.submatrix_apply, id_eq]
      exact hallEntries _ _
    have hcardCast : ((Fintype.card (Fin 3) : ℕ) : ℝ) = 3 := by simp
    rw [hcardCast]
    linarith [houtTrace]
  -- E3: the outside Gram determinant is at most 4
  have hdetOutside : (solveYᵀ * solveY - 1).det ≤ 4 := by
    have hcancel : solveYᵀ * solveY - 1 = outsideBlockᵀ * outsideBlock := by
      rw [hsplit]
      exact add_sub_cancel_left 1 _
    rw [hcancel, det_transpose_mul_self_four_rows_eq_sum_sq_minors]
    have hminorBound : ∀ tripleRows : Fin 3 → Fin 4,
        (outsideBlock.submatrix tripleRows id).det ^ 2 ≤ 1 := by
      intro tripleRows
      have hcomp : outsideBlock.submatrix tripleRows id
          = solveY.submatrix (fun slot => outEnum (tripleRows slot)) id := by
        rw [houtsideBlockDef, Matrix.submatrix_submatrix]
        rfl
      rw [hcomp]
      exact (sq_le_one_iff_abs_le_one _).mpr
        (abs_det_solveMatrix_submatrix_le_one_of_maximalVolume (unitAtomRows D) pick hunit
          hmax _)
    linarith [hminorBound ![1, 2, 3], hminorBound ![0, 2, 3], hminorBound ![0, 1, 3],
      hminorBound ![0, 1, 2]]
  -- the trace gate: e₂(Γ) = 3 − σ ≤ (45/7)·det Γ
  have hadj := adjugate_unitPickGram D huniform hsharePos hunit
  have htraceAdj : Matrix.trace pickGram.adjugate
      = pickGram.det * ((3 / 7) * Matrix.trace (solveYᵀ * solveY)) := by
    rw [hadj, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, hsolveDef]
  have htraceAdjCoord : Matrix.trace pickGram.adjugate
      = 3 - directionTripleSigma D (pick 0) (pick 1) (pick 2) := by
    have hflipOne : pickGram 1 0 = pickGram 0 1 := congrFun (congrFun hsymmG 0) 1
    have hflipTwo : pickGram 2 0 = pickGram 0 2 := congrFun (congrFun hsymmG 0) 2
    have hflipThree : pickGram 2 1 = pickGram 1 2 := congrFun (congrFun hsymmG 1) 2
    rw [trace_adjugate_three, hdiagZero, hdiagOne, hdiagTwo, hflipOne, hflipTwo, hflipThree,
      hsigmaEq]
    ring
  have htraceGate : 3 - directionTripleSigma D (pick 0) (pick 1) (pick 2)
      ≤ (45 / 7) * pickGram.det := by
    rw [← htraceAdjCoord, htraceAdj]
    have hscalePos : 0 ≤ pickGram.det * (3 / 7) := by positivity
    calc pickGram.det * ((3 / 7) * Matrix.trace (solveYᵀ * solveY))
        = pickGram.det * (3 / 7) * Matrix.trace (solveYᵀ * solveY) := by ring
      _ ≤ pickGram.det * (3 / 7) * 15 := mul_le_mul_of_nonneg_left htraceSolve hscalePos
      _ = (45 / 7) * pickGram.det := by ring
  -- the volume gate: det((7/3)·1 − Γ) ≤ 4·det Γ
  have hdetShift : ((3 / 7 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) - pickGram).det
      = 64 / 27 - (4 / 3) * directionTripleSigma D (pick 0) (pick 1) (pick 2)
        - 2 * directionTripleProduct D (pick 0) (pick 1) (pick 2) := by
    have hcoeff : ((3 / 7 : ℝ))⁻¹ = 7 / 3 := by norm_num
    have hneg : (3 / 7 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) - pickGram
        = -(pickGram - (7 / 3 : ℝ) • 1) := by
      rw [hcoeff, neg_sub]
    rw [hneg, Matrix.det_neg, Fintype.card_fin,
      det_sub_smul_one_of_symm_unitDiag hsymmG hdiagZero hdiagOne hdiagTwo (7 / 3),
      ← hsigmaEq, ← hproductEq]
    ring
  have hvolumeGate : 64 / 27 - (4 / 3) * directionTripleSigma D (pick 0) (pick 1) (pick 2)
      - 2 * directionTripleProduct D (pick 0) (pick 1) (pick 2) ≤ 4 * pickGram.det := by
    have hfactored := det_solveGram_sub_one D huniform hsharePos hunit
    rw [hfactored] at hdetOutside
    rw [← hdetShift]
    have hbound := (inv_mul_le_iff₀ hGdetPos).mp hdetOutside
    linarith [hbound]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hdetCoord]
    exact hGdetPos
  · rw [hdetCoord] at htraceGate
    linarith [htraceGate]
  · rw [hdetCoord] at hvolumeGate
    linarith [hvolumeGate]

/-- **THE TRACE GATE at `(7,3)`-uniform**: at a maximal-volume nonsingular pick
of the unit rows, `38σ − 24 ≤ 90P` — the `(σ,P)` reading of the twelve one-row
exchange bounds `tr(X_oᵀX_o) ≤ 12` through isotropy. -/
theorem traceGate_of_maximalVolume_sevenThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pick : Fin 3 → Fin 7} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 7, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    38 * directionTripleSigma D (pick 0) (pick 1) (pick 2) - 24
      ≤ 90 * directionTripleProduct D (pick 0) (pick 1) (pick 2) :=
  (exchangeGates_sevenThree D huniform hinj hunit hmax).2.1

/-- **THE VOLUME GATE at `(7,3)`-uniform**: at a maximal-volume nonsingular
pick, `36σ − 22 ≤ 135P` — the `(σ,P)` reading of the four three-row exchange
bounds `det(X_oᵀX_o) ≤ 4` through Cauchy–Binet and isotropy.  This is the gate
the fifths route does not have, and the reason the floor moves from `1/5` to
`31/150`. -/
theorem volumeGate_of_maximalVolume_sevenThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pick : Fin 3 → Fin 7} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 7, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    36 * directionTripleSigma D (pick 0) (pick 1) (pick 2) - 22
      ≤ 135 * directionTripleProduct D (pick 0) (pick 1) (pick 2) :=
  (exchangeGates_sevenThree D huniform hinj hunit hmax).2.2

/-- **The σ-cap at a `(7,3)`-uniform maximal-volume pick**: the picked triple's
correlation mass is at most `4/3`.  Trace gate + AM–GM through the exact cubic
factorization; compare the landed global cap `σ ≤ 13/9` on ALL triples — the
maximal-volume selector buys `4/3 < 13/9`. -/
theorem directionTripleSigma_le_fourThirds_of_maximalVolume_sevenThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pick : Fin 3 → Fin 7} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 7, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    directionTripleSigma D (pick 0) (pick 1) (pick 2) ≤ 4 / 3 := by
  obtain ⟨hdetPos, htraceGate, _⟩ := exchangeGates_sevenThree D huniform hinj hunit hmax
  have hamgm : 27 * directionTripleProduct D (pick 0) (pick 1) (pick 2) ^ 2
      ≤ directionTripleSigma D (pick 0) (pick 1) (pick 2) ^ 3 := by
    rw [directionTripleSigma, directionTripleProduct]
    exact twentySeven_mul_sq_tripleProduct_le_cube_squareSum _ _ _
  have hrange : directionTripleSigma D (pick 0) (pick 1) (pick 2) ≤ 3 := by
    rw [directionTripleSigma]
    have hboundOne := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 0) (pick 1))
    have hboundTwo := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 0) (pick 2))
    have hboundThree := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 1) (pick 2))
    linarith [hboundOne, hboundTwo, hboundThree]
  exact squareSum_le_fourThirds_of_traceGate htraceGate hamgm hrange hdetPos

/-- **THE CAUCHY–BINET FLOOR, `(7,3)`.**  At every `(7,3)`-uniform design and
every maximal-volume nonsingular pick of the unit-atom rows, the picked unit
Gram is positive definite past `31/150`:

    `λ_min(Γ[T#]) > 31/150 = 0.20666… `,

strictly above the fifths floor `1/5 = 30/150` and within `4·10⁻⁵` of the
relaxation optimum `g* ≈ 0.2067052`.  The `e₂ ≤ 18` exchange bound is not
consumed: the trace and volume gates alone cut the corner. -/
theorem posDef_unitPickGram_sub_cauchyBinetFloor_sevenThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pick : Fin 3 → Fin 7} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 7, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    (selectedFrameRows (unitAtomRows D) pick * (selectedFrameRows (unitAtomRows D) pick)ᵀ
      - (31 / 150 : ℝ) • 1).PosDef := by
  have hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  obtain ⟨hdetPos, htraceGate, hvolumeGate⟩ :=
    exchangeGates_sevenThree D huniform hinj hunit hmax
  set pickGram := selectedFrameRows (unitAtomRows D) pick
    * (selectedFrameRows (unitAtomRows D) pick)ᵀ with hpickGramDef
  have hsymmG : pickGramᵀ = pickGram := unitPickGram_transpose D pick
  have hentry : ∀ rowSlot colSlot : Fin 3,
      pickGram rowSlot colSlot = directionGram D (pick rowSlot) (pick colSlot) :=
    fun rowSlot colSlot => unitPickGram_entry D pick rowSlot colSlot
  have hdiagZero : pickGram 0 0 = 1 := by
    rw [hentry 0 0]; exact directionGram_self D (hlevPos (pick 0))
  have hdiagOne : pickGram 1 1 = 1 := by
    rw [hentry 1 1]; exact directionGram_self D (hlevPos (pick 1))
  have hdiagTwo : pickGram 2 2 = 1 := by
    rw [hentry 2 2]; exact directionGram_self D (hlevPos (pick 2))
  have hGdetPos : 0 < pickGram.det := det_unitPickGram_pos D hunit
  have hentryRange : pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2 ≤ 3 := by
    rw [hentry 0 1, hentry 0 2, hentry 1 2]
    have hboundOne := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 0) (pick 1))
    have hboundTwo := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 0) (pick 2))
    have hboundThree := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 1) (pick 2))
    linarith [hboundOne, hboundTwo, hboundThree]
  refine posDef_sub_cauchyBinetFloor_of_exchangeGates_sevenThree hsymmG
    hdiagZero hdiagOne hdiagTwo hGdetPos hentryRange ?_ ?_
  · rw [hentry 0 1, hentry 0 2, hentry 1 2]
    rw [directionTripleSigma, directionTripleProduct] at htraceGate
    exact htraceGate
  · rw [hentry 0 1, hentry 0 2, hentry 1 2]
    rw [directionTripleSigma, directionTripleProduct] at hvolumeGate
    exact hvolumeGate

/-- The Cauchy–Binet floor read on the direction Gram matrix block. -/
theorem posDef_directionGramMatrix_submatrix_sub_cauchyBinetFloor_sevenThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pick : Fin 3 → Fin 7} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 7, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    ((directionGramMatrix D).submatrix pick pick - (31 / 150 : ℝ) • 1).PosDef := by
  rw [← unitPickGram_eq_directionGramMatrix_submatrix]
  exact posDef_unitPickGram_sub_cauchyBinetFloor_sevenThree D huniform hinj hunit hmax

/-- **The floor with the pick supplied**: every `(7,3)`-uniform design has a
maximal-volume pick, and at it the unit Gram clears `31/150`.  The march
`1/5 < 31/150 ≤ g* < 1/3` in one existence statement. -/
theorem exists_pick_posDef_unitPickGram_sub_cauchyBinetFloor_sevenThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    ∃ pick : Fin 3 → Fin 7, Function.Injective pick ∧
      (selectedFrameRows (unitAtomRows D) pick * (selectedFrameRows (unitAtomRows D) pick)ᵀ
        - (31 / 150 : ℝ) • 1).PosDef := by
  have hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  obtain ⟨pick, hinj, hdet, hmax⟩ := exists_maximalVolume_pick_unitAtomRows D hlevPos
  exact ⟨pick, hinj, posDef_unitPickGram_sub_cauchyBinetFloor_sevenThree D huniform hinj
    (isUnit_iff_ne_zero.mpr hdet) hmax⟩

end SevenThreeAssembly

/-! ## 7. The `(6,3)` calibration twin -/

section SixThreeAssembly

variable (D : WeightedDesign 6 3)

/-- The `(6,3)` exchange gates: Gram positivity, the trace gate `5σ − 3 ≤ 12P`,
and the DEGENERATE volume gate `P ≥ 0` — at share `1/2` the single three-row
exchange bound `det(X_oᵀX_o) = det(X_o)² ≤ 1` says exactly that the picked
triple product is nonnegative. -/
private theorem exchangeGates_sixThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 6, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    0 < 1 - directionTripleSigma D (pick 0) (pick 1) (pick 2)
        + 2 * directionTripleProduct D (pick 0) (pick 1) (pick 2)
    ∧ 5 * directionTripleSigma D (pick 0) (pick 1) (pick 2) - 3
        ≤ 12 * directionTripleProduct D (pick 0) (pick 1) (pick 2)
    ∧ 0 ≤ directionTripleProduct D (pick 0) (pick 1) (pick 2) := by
  classical
  have hsharePos : (0 : ℝ) < 1 / 2 := by norm_num
  have hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  set solveY := solveMatrix (unitAtomRows D) pick with hsolveDef
  set pickGram := selectedFrameRows (unitAtomRows D) pick
    * (selectedFrameRows (unitAtomRows D) pick)ᵀ with hpickGramDef
  have hsymmG : pickGramᵀ = pickGram := unitPickGram_transpose D pick
  have hentry : ∀ rowSlot colSlot : Fin 3,
      pickGram rowSlot colSlot = directionGram D (pick rowSlot) (pick colSlot) :=
    fun rowSlot colSlot => unitPickGram_entry D pick rowSlot colSlot
  have hdiagZero : pickGram 0 0 = 1 := by
    rw [hentry 0 0]; exact directionGram_self D (hlevPos (pick 0))
  have hdiagOne : pickGram 1 1 = 1 := by
    rw [hentry 1 1]; exact directionGram_self D (hlevPos (pick 1))
  have hdiagTwo : pickGram 2 2 = 1 := by
    rw [hentry 2 2]; exact directionGram_self D (hlevPos (pick 2))
  have hsigmaEq : directionTripleSigma D (pick 0) (pick 1) (pick 2)
      = pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2 := by
    rw [directionTripleSigma, hentry 0 1, hentry 0 2, hentry 1 2]
  have hproductEq : directionTripleProduct D (pick 0) (pick 1) (pick 2)
      = pickGram 0 1 * pickGram 0 2 * pickGram 1 2 := by
    rw [directionTripleProduct, hentry 0 1, hentry 0 2, hentry 1 2]
  have hGdetPos : 0 < pickGram.det := det_unitPickGram_pos D hunit
  have hdetCoord : pickGram.det
      = 1 - directionTripleSigma D (pick 0) (pick 1) (pick 2)
        + 2 * directionTripleProduct D (pick 0) (pick 1) (pick 2) := by
    have hshift := det_sub_smul_one_of_symm_unitDiag hsymmG hdiagZero hdiagOne hdiagTwo 0
    rw [zero_smul, sub_zero] at hshift
    rw [hshift, hsigmaEq, hproductEq]
    ring
  -- the complement enumeration: three outside atoms
  set outSet := ((Finset.image pick Finset.univ)ᶜ : Finset (Fin 6)) with houtSetDef
  have hcardOut : outSet.card = 3 := by
    rw [houtSetDef, Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simp
  set outEnum := fun outIndex => outSet.orderEmbOfFin hcardOut outIndex with houtEnumDef
  have houtInj : Function.Injective outEnum := fun _ _ heq =>
    (outSet.orderEmbOfFin hcardOut).injective heq
  have himageOut : Finset.image outEnum Finset.univ = (Finset.image pick Finset.univ)ᶜ := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← houtSetDef]
    exact Finset.range_orderEmbOfFin outSet hcardOut
  have hsplit := solveGram_split (unitAtomRows D) hinj hunit houtInj himageOut
  set outsideBlock := solveY.submatrix outEnum id with houtsideBlockDef
  have hallEntries : ∀ rowIndex colIndex, |solveY rowIndex colIndex| ≤ 1 :=
    fun rowIndex colIndex =>
      abs_solveMatrix_le_one_of_maximalVolume_row (unitAtomRows D) pick hinj hunit hmax
        rowIndex colIndex
  -- E1: the solve Gram trace is at most 12
  have htraceSolve : Matrix.trace (solveYᵀ * solveY) ≤ 12 := by
    rw [hsplit, Matrix.trace_add, Matrix.trace_one]
    have houtTrace : Matrix.trace (outsideBlockᵀ * outsideBlock) ≤ (3 : ℝ) * 3 := by
      refine trace_transpose_mul_self_le_of_abs_entries_le_one outsideBlock
        fun rowIndex colIndex => ?_
      rw [houtsideBlockDef]
      simp only [Matrix.submatrix_apply, id_eq]
      exact hallEntries _ _
    have hcardCast : ((Fintype.card (Fin 3) : ℕ) : ℝ) = 3 := by simp
    rw [hcardCast]
    linarith [houtTrace]
  -- E3: the outside Gram determinant is at most 1 (a single squared volume)
  have hdetOutside : (solveYᵀ * solveY - 1).det ≤ 1 := by
    have hcancel : solveYᵀ * solveY - 1 = outsideBlockᵀ * outsideBlock := by
      rw [hsplit]
      exact add_sub_cancel_left 1 _
    rw [hcancel, Matrix.det_mul, Matrix.det_transpose, ← sq]
    exact (sq_le_one_iff_abs_le_one _).mpr
      (abs_det_solveMatrix_submatrix_le_one_of_maximalVolume (unitAtomRows D) pick hunit
        hmax outEnum)
  -- the trace gate
  have hadj := adjugate_unitPickGram D huniform hsharePos hunit
  have htraceAdj : Matrix.trace pickGram.adjugate
      = pickGram.det * ((1 / 2) * Matrix.trace (solveYᵀ * solveY)) := by
    rw [hadj, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, hsolveDef]
  have htraceAdjCoord : Matrix.trace pickGram.adjugate
      = 3 - directionTripleSigma D (pick 0) (pick 1) (pick 2) := by
    have hflipOne : pickGram 1 0 = pickGram 0 1 := congrFun (congrFun hsymmG 0) 1
    have hflipTwo : pickGram 2 0 = pickGram 0 2 := congrFun (congrFun hsymmG 0) 2
    have hflipThree : pickGram 2 1 = pickGram 1 2 := congrFun (congrFun hsymmG 1) 2
    rw [trace_adjugate_three, hdiagZero, hdiagOne, hdiagTwo, hflipOne, hflipTwo, hflipThree,
      hsigmaEq]
    ring
  have htraceGate : 3 - directionTripleSigma D (pick 0) (pick 1) (pick 2)
      ≤ 6 * pickGram.det := by
    rw [← htraceAdjCoord, htraceAdj]
    have hscalePos : 0 ≤ pickGram.det * (1 / 2) := by positivity
    calc pickGram.det * ((1 / 2) * Matrix.trace (solveYᵀ * solveY))
        = pickGram.det * (1 / 2) * Matrix.trace (solveYᵀ * solveY) := by ring
      _ ≤ pickGram.det * (1 / 2) * 12 := mul_le_mul_of_nonneg_left htraceSolve hscalePos
      _ = 6 * pickGram.det := by ring
  -- the volume gate degenerates to P ≥ 0
  have hdetShift : ((1 / 2 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) - pickGram).det
      = 1 - directionTripleSigma D (pick 0) (pick 1) (pick 2)
        - 2 * directionTripleProduct D (pick 0) (pick 1) (pick 2) := by
    have hcoeff : ((1 / 2 : ℝ))⁻¹ = 2 := by norm_num
    have hneg : (1 / 2 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) - pickGram
        = -(pickGram - (2 : ℝ) • 1) := by
      rw [hcoeff, neg_sub]
    rw [hneg, Matrix.det_neg, Fintype.card_fin,
      det_sub_smul_one_of_symm_unitDiag hsymmG hdiagZero hdiagOne hdiagTwo 2,
      ← hsigmaEq, ← hproductEq]
    ring
  have hproductGate : 0 ≤ directionTripleProduct D (pick 0) (pick 1) (pick 2) := by
    have hfactored := det_solveGram_sub_one D huniform hsharePos hunit
    rw [hfactored] at hdetOutside
    have hbound := (inv_mul_le_iff₀ hGdetPos).mp hdetOutside
    rw [hdetShift, mul_one, hdetCoord] at hbound
    linarith [hbound]
  refine ⟨?_, ?_, hproductGate⟩
  · rw [← hdetCoord]
    exact hGdetPos
  · rw [hdetCoord] at htraceGate
    linarith [htraceGate]

/-- The `(6,3)` trace gate: `5σ − 3 ≤ 12P` at a maximal-volume pick. -/
theorem traceGate_of_maximalVolume_sixThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 6, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    5 * directionTripleSigma D (pick 0) (pick 1) (pick 2) - 3
      ≤ 12 * directionTripleProduct D (pick 0) (pick 1) (pick 2) :=
  (exchangeGates_sixThree D huniform hinj hunit hmax).2.1

/-- **The `(6,3)` volume gate degenerates to coherence**: at a `(6,3)`-uniform
maximal-volume pick the triple product is NONNEGATIVE.  On the icosahedral
design this is exactly the statement that maximal-volume triples are faces
(faces carry `P = +β`, non-faces `P = −β`). -/
theorem nonneg_directionTripleProduct_of_maximalVolume_sixThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 6, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    0 ≤ directionTripleProduct D (pick 0) (pick 1) (pick 2) :=
  (exchangeGates_sixThree D huniform hinj hunit hmax).2.2

/-- The `(6,3)` σ-cap: correlation mass at most `5/4` at a maximal-volume pick. -/
theorem directionTripleSigma_le_fiveFourths_of_maximalVolume_sixThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 6, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    directionTripleSigma D (pick 0) (pick 1) (pick 2) ≤ 5 / 4 := by
  obtain ⟨hdetPos, htraceGate, _⟩ := exchangeGates_sixThree D huniform hinj hunit hmax
  have hamgm : 27 * directionTripleProduct D (pick 0) (pick 1) (pick 2) ^ 2
      ≤ directionTripleSigma D (pick 0) (pick 1) (pick 2) ^ 3 := by
    rw [directionTripleSigma, directionTripleProduct]
    exact twentySeven_mul_sq_tripleProduct_le_cube_squareSum _ _ _
  have hrange : directionTripleSigma D (pick 0) (pick 1) (pick 2) ≤ 3 := by
    rw [directionTripleSigma]
    have hboundOne := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 0) (pick 1))
    have hboundTwo := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 0) (pick 2))
    have hboundThree := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 1) (pick 2))
    linarith [hboundOne, hboundTwo, hboundThree]
  exact squareSum_le_fiveFourths_of_traceGate htraceGate hamgm hrange hdetPos

/-- **THE CAUCHY–BINET FLOOR, `(6,3)`** — the calibration twin, on the stratum
where U6 is already proved: at every `(6,3)`-uniform design and maximal-volume
nonsingular pick, `λ_min(Γ[T#]) > 9/40 = 0.225`, strictly above the trace-route
floor `(5 − √17)/4 ≈ 0.21922` and just below the relaxation optimum
`(5 − √15)/5 ≈ 0.22540`. -/
theorem posDef_unitPickGram_sub_cauchyBinetFloor_sixThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick)
    (hunit : IsUnit (selectedFrameRows (unitAtomRows D) pick).det)
    (hmax : ∀ other : Fin 3 → Fin 6, Function.Injective other →
      |(selectedFrameRows (unitAtomRows D) other).det|
        ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) :
    (selectedFrameRows (unitAtomRows D) pick * (selectedFrameRows (unitAtomRows D) pick)ᵀ
      - (9 / 40 : ℝ) • 1).PosDef := by
  have hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  obtain ⟨hdetPos, htraceGate, hproductGate⟩ :=
    exchangeGates_sixThree D huniform hinj hunit hmax
  set pickGram := selectedFrameRows (unitAtomRows D) pick
    * (selectedFrameRows (unitAtomRows D) pick)ᵀ with hpickGramDef
  have hsymmG : pickGramᵀ = pickGram := unitPickGram_transpose D pick
  have hentry : ∀ rowSlot colSlot : Fin 3,
      pickGram rowSlot colSlot = directionGram D (pick rowSlot) (pick colSlot) :=
    fun rowSlot colSlot => unitPickGram_entry D pick rowSlot colSlot
  have hdiagZero : pickGram 0 0 = 1 := by
    rw [hentry 0 0]; exact directionGram_self D (hlevPos (pick 0))
  have hdiagOne : pickGram 1 1 = 1 := by
    rw [hentry 1 1]; exact directionGram_self D (hlevPos (pick 1))
  have hdiagTwo : pickGram 2 2 = 1 := by
    rw [hentry 2 2]; exact directionGram_self D (hlevPos (pick 2))
  have hGdetPos : 0 < pickGram.det := det_unitPickGram_pos D hunit
  have hentryRange : pickGram 0 1 ^ 2 + pickGram 0 2 ^ 2 + pickGram 1 2 ^ 2 ≤ 3 := by
    rw [hentry 0 1, hentry 0 2, hentry 1 2]
    have hboundOne := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 0) (pick 1))
    have hboundTwo := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 0) (pick 2))
    have hboundThree := (sq_le_one_iff_abs_le_one _).mpr
      (abs_directionGram_le_one D (pick 1) (pick 2))
    linarith [hboundOne, hboundTwo, hboundThree]
  refine posDef_sub_cauchyBinetFloor_of_exchangeGates_sixThree hsymmG
    hdiagZero hdiagOne hdiagTwo hGdetPos hentryRange ?_ ?_
  · rw [hentry 0 1, hentry 0 2, hentry 1 2]
    rw [directionTripleSigma, directionTripleProduct] at htraceGate
    exact htraceGate
  · rw [hentry 0 1, hentry 0 2, hentry 1 2]
    rw [directionTripleProduct] at hproductGate
    exact hproductGate

/-- The `(6,3)` floor with the pick supplied. -/
theorem exists_pick_posDef_unitPickGram_sub_cauchyBinetFloor_sixThree
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2) :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
      (selectedFrameRows (unitAtomRows D) pick * (selectedFrameRows (unitAtomRows D) pick)ᵀ
        - (9 / 40 : ℝ) • 1).PosDef := by
  have hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  obtain ⟨pick, hinj, hdet, hmax⟩ := exists_maximalVolume_pick_unitAtomRows D hlevPos
  exact ⟨pick, hinj, posDef_unitPickGram_sub_cauchyBinetFloor_sixThree D huniform hinj
    (isUnit_iff_ne_zero.mpr hdet) hmax⟩

end SixThreeAssembly

/-- **The `(6,3)` floor is non-vacuous**: the icosahedral design lies on the
uniform-share stratum (`atomShare_icosaDesign`), so it carries a maximal-volume
pick whose unit Gram clears `9/40`.  The `(7,3)` twin's stratum witness (the
basis-plus-tetrapod design) is landed by the sibling workflow module and
instantiates `exists_pick_posDef_unitPickGram_sub_cauchyBinetFloor_sevenThree`
the same way. -/
theorem exists_pick_posDef_sub_cauchyBinetFloor_icosaDesign :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
      (selectedFrameRows (unitAtomRows icosaDesign) pick
          * (selectedFrameRows (unitAtomRows icosaDesign) pick)ᵀ
        - (9 / 40 : ℝ) • 1).PosDef :=
  exists_pick_posDef_unitPickGram_sub_cauchyBinetFloor_sixThree icosaDesign
    atomShare_icosaDesign

/-! ## 8. Conjecture M7 and its GTZ consequence -/

/-- **CONJECTURE M7** (open): at `(7,3)`-uniform share, EVERY maximal-volume
nonsingular pick of the unit rows has `λ_min(Γ[T#]) ≥ 1/3`, i.e. the picked
block of the direction Gram matrix clears the domination level.  Equality is
attained at tetrahedral ties (`det_tetrahedralCorrelationThree`).  This file's
floor is the `31/150` weakening; the march to `1/3` runs through the rigidity
obstruction `fourEvenSignVectors_unitNorm_inconsistent`. -/
def MaxVolumeGramThirdFloorSevenThree : Prop :=
  ∀ D : WeightedDesign 7 3, (∀ atomIndex, atomShare D atomIndex = 3 / 7) →
    ∀ pick : Fin 3 → Fin 7, Function.Injective pick →
      IsUnit (selectedFrameRows (unitAtomRows D) pick).det →
      (∀ other : Fin 3 → Fin 7, Function.Injective other →
        |(selectedFrameRows (unitAtomRows D) other).det|
          ≤ |(selectedFrameRows (unitAtomRows D) pick).det|) →
      ((directionGramMatrix D).submatrix pick pick - (3 : ℝ)⁻¹ • 1).PosSemidef

/-- **M7 implies R3 on the leverage-3 stratum**: if the maximal-volume pick
always clears `1/3`, then every `(7,3)` design at uniform share `3/7` and
uniform leverage `3` has a dominating triple — through the landed domination
dictionary `Γ[C] ⪰ (1/3)·1 ↔ Dominates`.  (On mixed-leverage uniform-share
designs the Gram floor alone does not decide domination, which is why M7 is a
Gram-side statement.) -/
theorem exists_dominating_triple_of_maxVolumeGramThirdFloor
    (hthirdFloor : MaxVolumeGramThirdFloorSevenThree) (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3) :
    ∃ dominatingTriple : Finset (Fin 7), dominatingTriple.card = 3
      ∧ Dominates D dominatingTriple := by
  have hlevPos : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  obtain ⟨pick, hinj, hdet, hmax⟩ := exists_maximalVolume_pick_unitAtomRows D hlevPos
  have hpsd := hthirdFloor D huniform pick hinj (isUnit_iff_ne_zero.mpr hdet) hmax
  have hfirstSecond : pick 0 ≠ pick 1 := hinj.ne (by decide)
  have hfirstThird : pick 0 ≠ pick 2 := hinj.ne (by decide)
  have hsecondThird : pick 1 ≠ pick 2 := hinj.ne (by decide)
  have hvecEq : (![pick 0, pick 1, pick 2] : Fin 3 → Fin 7) = pick := by
    funext slot
    fin_cases slot <;> rfl
  refine ⟨{pick 0, pick 1, pick 2}, ?_, ?_⟩
  · exact Finset.card_eq_three.mpr ⟨pick 0, pick 1, pick 2, hfirstSecond, hfirstThird,
      hsecondThird, rfl⟩
  · refine (dominates_triple_iff_posSemidef_directionGramMatrix_submatrix D hleverage
      hfirstSecond hfirstThird hsecondThird).mpr ?_
    rw [hvecEq]
    exact hpsd

end Gtz
