/-
# The Cayley atlas on the orthogonal group

Module 1 of the genericity reduction for the open `(6,3)` cell: the sign-chart
atlas `Q = E · cay(A)` covering every orthogonal matrix, at GENERAL size.
Everything here is elementary linear algebra — no manifolds, no submersions, no
eigenvalues, no analytic identity theorem.

The shipped Cayley engine of `Gtz.Quantitative.ChartDescentFromMinimality` is
CONSUMED, not re-proved, through the dictionary `Gtz.cayleyOf` `= chartCayley (-1)`:
invertibility of the denominator at every step is the shipped
`Gtz.isUnit_det_chartCayleyDenominator`, orthogonality is the shipped
`Gtz.chartCayley_transpose_mul_self`.  This file lands only the deltas the
genericity run needs:

* **K1 strengthening** — `det_one_add_smul_pos_of_skew`: the Cayley denominator
  determinant is POSITIVE, not merely nonzero, at every scale.  Route: the map
  from the scale to the determinant is continuous, equals `1` at scale zero, and
  never vanishes (shipped unit lemma), so a negative value would force a root by
  the intermediate value theorem.  Positivity keeps every inequality direction
  under denominator clearing in the pullback module.
* **K2 deltas** — `det_cayleyOf_of_skew` (the transform lands in the SPECIAL
  orthogonal group), `inverseCayley` with `transpose_inverseCayley` (the inverse
  chart map is skew) and BOTH round trips `cayleyOf_inverseCayley`,
  `inverseCayley_cayleyOf`.
* **K3, existence form** — `exists_signVector_det_diagonal_add_ne_zero`: every
  matrix with nonzero determinant admits a diagonal sign matrix `E` with
  `det(E + Q) ≠ 0`.  Proof: `det(diag d + Q)` is AFFINE in each diagonal entry
  (determinant column linearity), and an affine function vanishing at `+1` and
  `-1` vanishes everywhere on the line, so signs can be fixed one coordinate at
  a time — the midpoint trick, run as a downward induction with no `2⁻⁶`
  identity.  `exists_skew_of_det_sign_add_ne_zero` upgrades chart membership to
  the exact representation `Q = E · cay(A)`, `det_eq_det_diagonal_of_det_add_ne_zero`
  is the parity bonus (a chart only contains matrices of its own determinant
  sign), and `exists_positive_chart` packages both for special orthogonal `Q`.
* **K4, generic two-flip overlap witness** — `det_flipTwoSign_add_cayleyOf_ne_zero`:
  for every pair of indices the J-block skew matrix `flipTwoWitnessSkew` lies in
  the overlap of the identity chart and the two-flip chart.  The determinant is
  computed WITHOUT permutation-sign bookkeeping: with `P` the coordinate-pair
  projector, the cleared numerator is `2·(1 − P − J)` and `(1 − P − J)² = F`
  (`P² = P`, `PJ = JP = J`, `J² = −P`), so its determinant squares to a nonzero
  quantity.  The 32-case one-step overlap star is DELIBERATELY not landed:
  two-flip steps chain to every positive chart (recon-certified design choice),
  and the opposite clearing orientation is the same lemma at the swapped index
  pair, because swapping negates the J-block.
* **Coordinates and the sign kit** — `skewOfRaw` (raw strictly-upper coordinates
  onto the full skew space, with exact recovery `skewOfRaw_entries_of_skew`) and
  the `IsSignVector` algebra the propagation module consumes.

Every identity landed here beyond the recon battery was verified in exact
rational arithmetic before landing (1131 checks: the general clearing identity,
the pair-projector decomposition at both index orders and two sizes, the affine
coordinate split, the parity mechanism; `/tmp/gtz-p1/land-cayley/identity_check.py`).

Honest scope: this module is size-generic linear algebra with NO design content
and NO openness statements; charts here are algebraic (`det ≠ 0` conditions),
and the topological and polynomial consequences live in the propagation module.

Backtick convention for this file's docstrings: multi-character backticked
tokens are declaration names (kernel-checked); single-letter backticked tokens
(`A`, `B`, `E`, `F`, `J`, `M`, `P`, `Q`) and the parameter name `raw` are local
mathematical notation, NOT constants.
-/
import Mathlib
import Gtz.Quantitative.ChartDescentFromMinimality

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## Cancellation helpers for nonsingular factors -/

/-- Right-cancel a factor with nonzero determinant: from `X·C = Y·C` conclude
`X = Y` by multiplying with the nonsingular inverse. -/
theorem eq_of_mul_eq_mul_right_of_isUnit_det
    {factor left right : Matrix (Fin size) (Fin size) ℝ}
    (hunit : IsUnit factor.det) (heq : left * factor = right * factor) :
    left = right := by
  calc left = left * (factor * factor⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
    _ = (left * factor) * factor⁻¹ := by rw [Matrix.mul_assoc]
    _ = (right * factor) * factor⁻¹ := by rw [heq]
    _ = right * (factor * factor⁻¹) := by rw [Matrix.mul_assoc]
    _ = right := by rw [Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]

/-- A nonsingular matrix commuting with another matrix has a commuting inverse.
This is the shipped `Gtz.inverse_chartCayleyDenominator_mul_comm` argument at
arbitrary factors. -/
theorem nonsing_inv_mul_comm_of_mul_comm
    {left right : Matrix (Fin size) (Fin size) ℝ}
    (hunit : IsUnit left.det) (hcomm : left * right = right * left) :
    left⁻¹ * right = right * left⁻¹ := by
  calc left⁻¹ * right
      = left⁻¹ * right * (left * left⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
    _ = left⁻¹ * (right * left) * left⁻¹ := by simp only [Matrix.mul_assoc]
    _ = left⁻¹ * (left * right) * left⁻¹ := by rw [hcomm]
    _ = (left⁻¹ * left) * (right * left⁻¹) := by simp only [Matrix.mul_assoc]
    _ = right * left⁻¹ := by rw [Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]

/-! ## Raw coordinates on the skew space -/

/-- Assemble a skew matrix from a raw square of coordinates: the strictly upper
triangle is read verbatim, the strictly lower triangle is its negated mirror,
the diagonal is zero.  The lower triangle and diagonal of `raw` are dummy
coordinates — harmless for the polynomial pullback, which only ever evaluates. -/
def skewOfRaw (raw : Fin size → Fin size → ℝ) : Matrix (Fin size) (Fin size) ℝ :=
  Matrix.of fun rowIndex colIndex =>
    if rowIndex < colIndex then raw rowIndex colIndex
    else if colIndex < rowIndex then -(raw colIndex rowIndex) else 0

/-- `skewOfRaw` always lands in the skew space, whatever the raw coordinates. -/
theorem transpose_skewOfRaw (raw : Fin size → Fin size → ℝ) :
    (skewOfRaw raw)ᵀ = -(skewOfRaw raw) := by
  ext rowIndex colIndex
  simp only [transpose_apply, skewOfRaw, of_apply]
  rcases lt_trichotomy rowIndex colIndex with hlt | heq | hgt
  · simp [hlt, asymm hlt]
  · simp [heq]
  · simp [hgt, asymm hgt]

/-- Exact recovery: a skew matrix is `skewOfRaw` of its own entries.  So the raw
coordinates are surjective onto the skew space — the chart parametrization
misses nothing. -/
theorem skewOfRaw_entries_of_skew {skew : Matrix (Fin size) (Fin size) ℝ}
    (hskew : skewᵀ = -skew) :
    skewOfRaw (fun rowIndex colIndex => skew rowIndex colIndex) = skew := by
  have hentry : ∀ rowIndex colIndex,
      skew colIndex rowIndex = -(skew rowIndex colIndex) := by
    intro rowIndex colIndex
    have happ : skewᵀ rowIndex colIndex = (-skew) rowIndex colIndex := by rw [hskew]
    simpa [transpose_apply, neg_apply] using happ
  ext rowIndex colIndex
  simp only [skewOfRaw, of_apply]
  rcases lt_trichotomy rowIndex colIndex with hlt | heq | hgt
  · simp [hlt]
  · subst heq
    have hdiag := hentry rowIndex rowIndex
    simp only [lt_irrefl, if_false]
    linarith
  · simp only [asymm hgt, if_false, hgt, if_true]
    rw [hentry colIndex rowIndex]

/-! ## K1 deltas: the denominator determinant is positive at every scale -/

/-- The shipped unit lemma read at scale `-scale`: `1 + scale • skew` has unit
determinant for every real scale. -/
theorem isUnit_det_one_add_smul_of_skew {skew : Matrix (Fin size) (Fin size) ℝ}
    (hskew : skewᵀ = -skew) (scale : ℝ) :
    IsUnit ((1 : Matrix (Fin size) (Fin size) ℝ) + scale • skew).det := by
  have hunit := isUnit_det_chartCayleyDenominator hskew (-scale)
  rwa [chartCayleyDenominator, neg_smul, sub_neg_eq_add] at hunit

/-- The shipped unit lemma at scale one: `1 + skew` is nonsingular. -/
theorem isUnit_det_one_add_of_skew {skew : Matrix (Fin size) (Fin size) ℝ}
    (hskew : skewᵀ = -skew) :
    IsUnit ((1 : Matrix (Fin size) (Fin size) ℝ) + skew).det := by
  have hunit := isUnit_det_one_add_smul_of_skew hskew 1
  rwa [one_smul] at hunit

/-- **THE DENOMINATOR DETERMINANT IS POSITIVE**, at every scale.  The scale-to-
determinant map is continuous and never zero (shipped unit lemma), and equals
`1` at scale zero; a nonpositive value anywhere would force a root in between by
the intermediate value theorem.  Positivity — not mere nonvanishing — is what
lets the pullback module clear denominators without flipping inequalities. -/
theorem det_one_add_smul_pos_of_skew {skew : Matrix (Fin size) (Fin size) ℝ}
    (hskew : skewᵀ = -skew) (scale : ℝ) :
    0 < ((1 : Matrix (Fin size) (Fin size) ℝ) + scale • skew).det := by
  have hnever : ∀ other : ℝ,
      ((1 : Matrix (Fin size) (Fin size) ℝ) + other • skew).det ≠ 0 := fun other =>
    isUnit_iff_ne_zero.mp (isUnit_det_one_add_smul_of_skew hskew other)
  have hcont : Continuous fun other : ℝ =>
      ((1 : Matrix (Fin size) (Fin size) ℝ) + other • skew).det :=
    Continuous.matrix_det (continuous_const.add (continuous_id.smul continuous_const))
  have hzero : ((1 : Matrix (Fin size) (Fin size) ℝ) + (0 : ℝ) • skew).det = 1 := by
    rw [zero_smul, add_zero, det_one]
  by_contra hnotpos
  push Not at hnotpos
  have hneg : ((1 : Matrix (Fin size) (Fin size) ℝ) + scale • skew).det < 0 :=
    lt_of_le_of_ne hnotpos (hnever scale)
  have hmem : (0 : ℝ) ∈ Set.Icc
      (((1 : Matrix (Fin size) (Fin size) ℝ) + scale • skew).det)
      (((1 : Matrix (Fin size) (Fin size) ℝ) + (0 : ℝ) • skew).det) := by
    rw [Set.mem_Icc, hzero]
    exact ⟨hneg.le, zero_le_one⟩
  rcases le_total 0 scale with hscale | hscale
  · obtain ⟨root, _, hroot⟩ := intermediate_value_Icc' hscale hcont.continuousOn hmem
    exact hnever root hroot
  · obtain ⟨root, _, hroot⟩ := intermediate_value_Icc hscale hcont.continuousOn hmem
    exact hnever root hroot

/-- Positivity at scale one, the form the atlas consumes. -/
theorem det_one_add_pos_of_skew {skew : Matrix (Fin size) (Fin size) ℝ}
    (hskew : skewᵀ = -skew) :
    0 < ((1 : Matrix (Fin size) (Fin size) ℝ) + skew).det := by
  have hpos := det_one_add_smul_pos_of_skew hskew 1
  rwa [one_smul] at hpos

/-- Positivity for the numerator factor `1 - skew` as well: it is the
denominator at the opposite scale. -/
theorem det_one_sub_pos_of_skew {skew : Matrix (Fin size) (Fin size) ℝ}
    (hskew : skewᵀ = -skew) :
    0 < ((1 : Matrix (Fin size) (Fin size) ℝ) - skew).det := by
  have hpos := det_one_add_smul_pos_of_skew hskew (-1)
  rwa [neg_smul, one_smul, ← sub_eq_add_neg] at hpos

/-- Nonvanishing form of `Gtz.det_one_add_pos_of_skew`, for clearing steps that
only need a nonzero denominator. -/
theorem det_one_add_ne_zero_of_skew {skew : Matrix (Fin size) (Fin size) ℝ}
    (hskew : skewᵀ = -skew) :
    ((1 : Matrix (Fin size) (Fin size) ℝ) + skew).det ≠ 0 :=
  ne_of_gt (det_one_add_pos_of_skew hskew)

/-! ## The Cayley transform, in the atlas orientation -/

/-- **THE CAYLEY TRANSFORM** in the atlas orientation
`cay(A) = (1 - A)·(1 + A)⁻¹`, defined as the shipped `Gtz.chartCayley` at step
`-1` so that every shipped step-parametrized theorem applies verbatim. -/
noncomputable def cayleyOf (skew : Matrix (Fin size) (Fin size) ℝ) :
    Matrix (Fin size) (Fin size) ℝ :=
  chartCayley (-1) skew

/-- The dictionary, proved: `Gtz.cayleyOf` is literally `(1 - A)·(1 + A)⁻¹`. -/
theorem cayleyOf_eq (skew : Matrix (Fin size) (Fin size) ℝ) :
    cayleyOf skew = (1 - skew) * (1 + skew)⁻¹ := by
  rw [cayleyOf, chartCayley, neg_neg, chartCayleyDenominator, chartCayleyDenominator,
    one_smul, neg_smul, one_smul, sub_neg_eq_add]

/-- The identity chart is centred: the zero skew matrix maps to the identity. -/
theorem cayleyOf_zero :
    cayleyOf (0 : Matrix (Fin size) (Fin size) ℝ) = 1 := by
  rw [cayleyOf_eq, sub_zero, add_zero]
  exact Matrix.mul_nonsing_inv _ (by rw [det_one]; exact isUnit_one)

/-- Orthogonality of the transform, consumed from the shipped engine. -/
theorem cayleyOf_transpose_mul_self {skew : Matrix (Fin size) (Fin size) ℝ}
    (hskew : skewᵀ = -skew) :
    (cayleyOf skew)ᵀ * cayleyOf skew = 1 :=
  chartCayley_transpose_mul_self hskew (-1)

/-- Orthogonality of the transform, opposite product order. -/
theorem cayleyOf_mul_transpose_self {skew : Matrix (Fin size) (Fin size) ℝ}
    (hskew : skewᵀ = -skew) :
    cayleyOf skew * (cayleyOf skew)ᵀ = 1 :=
  chartCayley_mul_transpose_self hskew (-1)

/-- The transpose of the transform is the transform of the negated skew
matrix — the shipped step-flip identity read through the dictionary. -/
theorem transpose_cayleyOf {skew : Matrix (Fin size) (Fin size) ℝ}
    (hskew : skewᵀ = -skew) :
    (cayleyOf skew)ᵀ = cayleyOf (-skew) := by
  rw [cayleyOf, transpose_chartCayley hskew, neg_neg, cayleyOf, chartCayley, chartCayley,
    chartCayleyDenominator, chartCayleyDenominator, chartCayleyDenominator,
    chartCayleyDenominator]
  simp only [neg_smul, one_smul, smul_neg, neg_neg, sub_neg_eq_add]

/-- **THE TRANSFORM LANDS IN THE SPECIAL ORTHOGONAL GROUP**: `det cay(A) = 1`,
because `1 - A` is the transpose of `1 + A` for skew `A`, so numerator and
denominator determinants cancel exactly. -/
theorem det_cayleyOf_of_skew {skew : Matrix (Fin size) (Fin size) ℝ}
    (hskew : skewᵀ = -skew) :
    (cayleyOf skew).det = 1 := by
  have hflip : ((1 : Matrix (Fin size) (Fin size) ℝ) - skew).det
      = ((1 : Matrix (Fin size) (Fin size) ℝ) + skew).det := by
    calc ((1 : Matrix (Fin size) (Fin size) ℝ) - skew).det
        = (((1 : Matrix (Fin size) (Fin size) ℝ) - skew)ᵀ).det := (det_transpose _).symm
      _ = ((1 : Matrix (Fin size) (Fin size) ℝ) + skew).det := by
          rw [transpose_sub, transpose_one, hskew, sub_neg_eq_add]
  rw [cayleyOf_eq, det_mul, det_nonsing_inv, hflip,
    Ring.mul_inverse_cancel _ (isUnit_det_one_add_of_skew hskew)]

/-! ## Denominator clearing -/

/-- **THE GENERAL CLEARING IDENTITY**: for ANY block `B`,
`(B + cay(A))·(1 + A) = (B + 1) + (B - 1)·A`.  This is how every chart-overlap
and pullback statement trades the rational transform for a polynomial one; the
hypothesis is only nonvanishing of the denominator determinant. -/
theorem add_cayleyOf_mul_one_add (block : Matrix (Fin size) (Fin size) ℝ)
    {skew : Matrix (Fin size) (Fin size) ℝ}
    (hdet : ((1 : Matrix (Fin size) (Fin size) ℝ) + skew).det ≠ 0) :
    (block + cayleyOf skew) * (1 + skew) = (block + 1) + (block - 1) * skew := by
  have hcancel : (1 - skew) * (1 + skew)⁻¹ * (1 + skew) = 1 - skew := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.mul_one]
  rw [cayleyOf_eq, add_mul, hcancel]
  noncomm_ring

/-- The clearing identity at the identity block: `(1 + cay(A))·(1 + A) = 2`. -/
theorem one_add_cayleyOf_mul_one_add {skew : Matrix (Fin size) (Fin size) ℝ}
    (hdet : ((1 : Matrix (Fin size) (Fin size) ℝ) + skew).det ≠ 0) :
    (1 + cayleyOf skew) * (1 + skew) = 1 + 1 := by
  have hclear := add_cayleyOf_mul_one_add 1 hdet
  simpa using hclear

/-- Every Cayley point lies in the identity chart: `det(1 + cay(A)) ≠ 0`.  This
is the chain's base camp — the chart of the identity sign matrix sees the whole
image of the transform. -/
theorem det_one_add_cayleyOf_ne_zero {skew : Matrix (Fin size) (Fin size) ℝ}
    (hskew : skewᵀ = -skew) :
    ((1 : Matrix (Fin size) (Fin size) ℝ) + cayleyOf skew).det ≠ 0 := by
  have hdet := det_one_add_ne_zero_of_skew hskew
  have hclear := one_add_cayleyOf_mul_one_add hdet
  have htwo : ((1 : Matrix (Fin size) (Fin size) ℝ) + 1).det ≠ 0 := by
    have hsmul : ((1 : Matrix (Fin size) (Fin size) ℝ) + 1) = (2 : ℝ) • 1 :=
      (two_smul ℝ (1 : Matrix (Fin size) (Fin size) ℝ)).symm
    rw [hsmul, det_smul, det_one, mul_one]
    exact pow_ne_zero _ two_ne_zero
  intro hzero
  apply htwo
  rw [← hclear, det_mul, hzero, zero_mul]

/-! ## The inverse chart map -/

/-- **THE INVERSE CHART MAP** `icay(M) = (1 - M)·(1 + M)⁻¹` — the same rational
formula as the transform itself, read at an orthogonal matrix instead of a skew
one.  Meaningful on the chart domain `det(1 + M) ≠ 0`. -/
noncomputable def inverseCayley (ortho : Matrix (Fin size) (Fin size) ℝ) :
    Matrix (Fin size) (Fin size) ℝ :=
  (1 - ortho) * (1 + ortho)⁻¹

/-- **THE INVERSE CHART MAP IS SKEW** on its domain: for orthogonal `M` with
`det(1 + M) ≠ 0`, `icay(M)ᵀ = -icay(M)`.  Uses only `MᵀM = 1` and the
commutation of `1 - M` with `(1 + M)⁻¹`. -/
theorem transpose_inverseCayley {ortho : Matrix (Fin size) (Fin size) ℝ}
    (horth : orthoᵀ * ortho = 1)
    (hdet : ((1 : Matrix (Fin size) (Fin size) ℝ) + ortho).det ≠ 0) :
    (inverseCayley ortho)ᵀ = -(inverseCayley ortho) := by
  have hunit : IsUnit ((1 : Matrix (Fin size) (Fin size) ℝ) + ortho).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hunitOrtho : IsUnit ortho.det := by
    have hdetProd := congrArg Matrix.det horth
    rw [det_mul, det_transpose, det_one] at hdetProd
    refine isUnit_iff_ne_zero.mpr fun hzero => ?_
    rw [hzero, mul_zero] at hdetProd
    exact zero_ne_one hdetProd
  have hunitOrthoT : IsUnit (orthoᵀ).det := by rwa [det_transpose]
  have haddT : ((1 : Matrix (Fin size) (Fin size) ℝ) + ortho)ᵀ
      = orthoᵀ * (1 + ortho) := by
    rw [transpose_add, transpose_one, mul_add, mul_one, horth, add_comm]
  have hsubT : ((1 : Matrix (Fin size) (Fin size) ℝ) - ortho)ᵀ
      = -(orthoᵀ * (1 - ortho)) := by
    rw [transpose_sub, transpose_one, mul_sub, mul_one, horth, neg_sub]
  have hcancelT : (orthoᵀ)⁻¹ * (orthoᵀ * (1 - ortho)) = 1 - ortho := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunitOrthoT, Matrix.one_mul]
  have hcommInv : (1 + ortho)⁻¹ * (1 - ortho) = (1 - ortho) * (1 + ortho)⁻¹ :=
    nonsing_inv_mul_comm_of_mul_comm hunit (by noncomm_ring)
  calc (inverseCayley ortho)ᵀ
      = ((1 + ortho)ᵀ)⁻¹ * (1 - ortho)ᵀ := by
        rw [inverseCayley, transpose_mul, transpose_nonsing_inv]
    _ = (orthoᵀ * (1 + ortho))⁻¹ * -(orthoᵀ * (1 - ortho)) := by rw [haddT, hsubT]
    _ = -((1 + ortho)⁻¹ * ((orthoᵀ)⁻¹ * (orthoᵀ * (1 - ortho)))) := by
        rw [Matrix.mul_inv_rev, mul_neg, Matrix.mul_assoc]
    _ = -((1 - ortho) * (1 + ortho)⁻¹) := by rw [hcancelT, hcommInv]
    _ = -(inverseCayley ortho) := by rw [inverseCayley]

/-- **ROUND TRIP, CHART TO GROUP**: `cay(icay(M)) = M` on the chart domain.
With `A := icay(M)` one has `(1 - A)·(1 + M) = M·(1 + A)·(1 + M)` by direct
expansion, and the nonsingular factor `1 + M` cancels. -/
theorem cayleyOf_inverseCayley {ortho : Matrix (Fin size) (Fin size) ℝ}
    (horth : orthoᵀ * ortho = 1)
    (hdet : ((1 : Matrix (Fin size) (Fin size) ℝ) + ortho).det ≠ 0) :
    cayleyOf (inverseCayley ortho) = ortho := by
  have hunit : IsUnit ((1 : Matrix (Fin size) (Fin size) ℝ) + ortho).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hskewIC : (inverseCayley ortho)ᵀ = -(inverseCayley ortho) :=
    transpose_inverseCayley horth hdet
  have hdetIC : ((1 : Matrix (Fin size) (Fin size) ℝ) + inverseCayley ortho).det ≠ 0 :=
    det_one_add_ne_zero_of_skew hskewIC
  have hicay : inverseCayley ortho * (1 + ortho) = 1 - ortho := by
    rw [inverseCayley, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]
  have hprodLeft : (1 - inverseCayley ortho) * (1 + ortho) = ortho + ortho := by
    rw [Matrix.sub_mul, Matrix.one_mul, hicay]
    abel
  have hprodRight : (ortho * (1 + inverseCayley ortho)) * (1 + ortho)
      = ortho + ortho := by
    have hsum : ((1 : Matrix (Fin size) (Fin size) ℝ) + inverseCayley ortho)
        * (1 + ortho) = 1 + 1 := by
      rw [Matrix.add_mul, Matrix.one_mul, hicay]
      abel
    rw [Matrix.mul_assoc, hsum, Matrix.mul_add]
    simp only [Matrix.mul_one]
  have hkey : (1 : Matrix (Fin size) (Fin size) ℝ) - inverseCayley ortho
      = ortho * (1 + inverseCayley ortho) :=
    eq_of_mul_eq_mul_right_of_isUnit_det hunit (hprodLeft.trans hprodRight.symm)
  rw [cayleyOf_eq, hkey, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetIC), Matrix.mul_one]

/-- **ROUND TRIP, GROUP TO CHART**: `icay(cay(A)) = A` for every skew `A` —
unconditionally, because the transform never leaves the identity chart
(`Gtz.det_one_add_cayleyOf_ne_zero`). -/
theorem inverseCayley_cayleyOf {skew : Matrix (Fin size) (Fin size) ℝ}
    (hskew : skewᵀ = -skew) :
    inverseCayley (cayleyOf skew) = skew := by
  have hdet := det_one_add_ne_zero_of_skew hskew
  have hunit : IsUnit ((1 : Matrix (Fin size) (Fin size) ℝ) + skew).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hdetC := det_one_add_cayleyOf_ne_zero hskew
  have hcay : cayleyOf skew * (1 + skew) = 1 - skew := by
    rw [cayleyOf_eq, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]
  have hprodLeft : (1 - cayleyOf skew) * (1 + skew) = skew + skew := by
    rw [Matrix.sub_mul, Matrix.one_mul, hcay]
    abel
  have hprodRight : (skew * (1 + cayleyOf skew)) * (1 + skew) = skew + skew := by
    rw [Matrix.mul_assoc, one_add_cayleyOf_mul_one_add hdet, Matrix.mul_add]
    simp only [Matrix.mul_one]
  have hkey : (1 : Matrix (Fin size) (Fin size) ℝ) - cayleyOf skew
      = skew * (1 + cayleyOf skew) :=
    eq_of_mul_eq_mul_right_of_isUnit_det hunit (hprodLeft.trans hprodRight.symm)
  rw [inverseCayley, hkey, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetC), Matrix.mul_one]

/-! ## Sign vectors -/

/-- A vector of chart signs: every entry is `+1` or `-1`.  The diagonal matrix
of such a vector is one of the `2^size` chart labels. -/
def IsSignVector (signs : Fin size → ℝ) : Prop :=
  ∀ index, signs index = 1 ∨ signs index = -1

/-- Each sign squares to one. -/
theorem IsSignVector.mul_self {signs : Fin size → ℝ} (hsigns : IsSignVector signs)
    (index : Fin size) : signs index * signs index = 1 := by
  rcases hsigns index with hval | hval <;> rw [hval] <;> norm_num

/-- The pointwise product of sign vectors is a sign vector — the label algebra
the two-flip chain walks on. -/
theorem IsSignVector.mul {signsLeft signsRight : Fin size → ℝ}
    (hleft : IsSignVector signsLeft) (hright : IsSignVector signsRight) :
    IsSignVector (fun index => signsLeft index * signsRight index) := by
  intro index
  show signsLeft index * signsRight index = 1 ∨ signsLeft index * signsRight index = -1
  rcases hleft index with hl | hl <;> rcases hright index with hr | hr <;>
    rw [hl, hr] <;> norm_num

/-- A sign diagonal is an involution: `E · E = 1`. -/
theorem IsSignVector.diagonal_mul_self {signs : Fin size → ℝ}
    (hsigns : IsSignVector signs) :
    diagonal signs * diagonal signs = 1 := by
  rw [diagonal_mul_diagonal]
  have hsq : (fun index => signs index * signs index) = fun _ : Fin size => (1 : ℝ) :=
    funext fun index => hsigns.mul_self index
  rw [hsq]
  exact Matrix.diagonal_one

/-- A sign diagonal is nonsingular, with no sign bookkeeping: its determinant is
a product of nonzero factors. -/
theorem IsSignVector.det_diagonal_ne_zero {signs : Fin size → ℝ}
    (hsigns : IsSignVector signs) :
    (diagonal signs).det ≠ 0 := by
  rw [det_diagonal]
  refine Finset.prod_ne_zero_iff.mpr fun index _ => ?_
  rcases hsigns index with hval | hval <;> rw [hval] <;> norm_num

/-- Factor a sign diagonal out of a two-chart sum:
`E + E'·M = E'·(diag(ε'·ε) + M)`.  This is the one-line dressing that reduces
membership of an `E'`-chart point in the `E`-chart to a product-sign chart
condition — the shape the two-flip chain consumes. -/
theorem diagonal_add_diagonal_mul_of_isSignVector {signsLeft signsRight : Fin size → ℝ}
    (hright : IsSignVector signsRight) (inner : Matrix (Fin size) (Fin size) ℝ) :
    diagonal signsLeft + diagonal signsRight * inner
      = diagonal signsRight
        * (diagonal (fun index => signsRight index * signsLeft index) + inner) := by
  rw [Matrix.mul_add, diagonal_mul_diagonal]
  have hleft : (fun index => signsRight index * (signsRight index * signsLeft index))
      = signsLeft := by
    funext index
    rw [← mul_assoc, hright.mul_self, one_mul]
  rw [hleft]

/-! ## K3: every nonsingular matrix lies in some sign chart -/

/-- **THE PER-COORDINATE MIDPOINT STEP.**  The determinant of `diag(d) + Q` is
affine in each diagonal entry (determinant column linearity), so if it is
nonzero at the current value of one coordinate, it is nonzero after fixing that
coordinate to `+1` or to `-1`: an affine function vanishing at both endpoints
vanishes on the whole line. -/
theorem exists_sign_update_det_ne_zero (target : Matrix (Fin size) (Fin size) ℝ)
    (signs : Fin size → ℝ) (pivot : Fin size)
    (hdet : (diagonal signs + target).det ≠ 0) :
    ∃ value : ℝ, (value = 1 ∨ value = -1) ∧
      (diagonal (Function.update signs pivot value) + target).det ≠ 0 := by
  classical
  have hupdate : ∀ value : ℝ,
      diagonal (Function.update signs pivot value) + target
        = (diagonal signs + target).updateCol pivot
            ((fun rowIndex => target rowIndex pivot)
              + value • fun rowIndex => if rowIndex = pivot then (1 : ℝ) else 0) := by
    intro value
    ext rowIndex colIndex
    simp only [Matrix.add_apply, Matrix.diagonal_apply, Matrix.updateCol_apply,
      Function.update_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hcol : colIndex = pivot
    · subst hcol
      by_cases hrow : rowIndex = colIndex
      · subst hrow
        simp [add_comm]
      · simp [hrow]
    · by_cases hrow : rowIndex = colIndex
      · subst hrow
        simp [hcol]
      · simp [hrow, hcol]
  have hsplit : ∀ value : ℝ,
      (diagonal (Function.update signs pivot value) + target).det
        = ((diagonal signs + target).updateCol pivot
            fun rowIndex => target rowIndex pivot).det
          + value * ((diagonal signs + target).updateCol pivot
            fun rowIndex => if rowIndex = pivot then (1 : ℝ) else 0).det := by
    intro value
    rw [hupdate value, Matrix.det_updateCol_add, Matrix.det_updateCol_smul]
  have hself : Function.update signs pivot (signs pivot) = signs := by
    funext index
    rw [Function.update_apply]
    split_ifs with hidx
    · rw [hidx]
    · rfl
  have hbase := hsplit (signs pivot)
  rw [hself] at hbase
  by_contra hnone
  push Not at hnone
  have hplus := hnone 1 (Or.inl rfl)
  have hminus := hnone (-1) (Or.inr rfl)
  rw [hsplit 1, one_mul] at hplus
  rw [hsplit (-1)] at hminus
  apply hdet
  rw [hbase]
  have hconst : ((diagonal signs + target).updateCol pivot
      fun rowIndex => target rowIndex pivot).det = 0 := by linarith
  have hunit : ((diagonal signs + target).updateCol pivot
      fun rowIndex => if rowIndex = pivot then (1 : ℝ) else 0).det = 0 := by linarith
  rw [hconst, hunit, mul_zero, add_zero]

/-- **K3, EXISTENCE FORM (sign-chart coverage).**  Every matrix with nonzero
determinant admits a sign vector `ε` with `det(diag ε + Q) ≠ 0`: starting from
the all-zero diagonal (value `det Q ≠ 0`), fix coordinates to signs one at a
time by the midpoint step.  This is the whole content of the `2⁻⁶` averaging
identity, with no averaging left in the statement. -/
theorem exists_signVector_det_diagonal_add_ne_zero
    (target : Matrix (Fin size) (Fin size) ℝ) (hdet : target.det ≠ 0) :
    ∃ signs : Fin size → ℝ, IsSignVector signs ∧ (diagonal signs + target).det ≠ 0 := by
  classical
  suffices hstep : ∀ (unset : Finset (Fin size)) (signs : Fin size → ℝ),
      (∀ index, index ∉ unset → signs index = 1 ∨ signs index = -1) →
      (diagonal signs + target).det ≠ 0 →
      ∃ finalSigns : Fin size → ℝ, IsSignVector finalSigns ∧
        (diagonal finalSigns + target).det ≠ 0 by
    refine hstep Finset.univ (fun _ => 0)
      (fun index hindex => absurd (Finset.mem_univ index) hindex) ?_
    rw [Matrix.diagonal_zero, zero_add]
    exact hdet
  intro unset
  induction unset using Finset.induction_on with
  | empty =>
      intro signs hsigns hdetSigns
      exact ⟨signs, fun index => hsigns index (by simp), hdetSigns⟩
  | @insert pivot rest hpivot ih =>
      intro signs hsigns hdetSigns
      obtain ⟨value, hvalue, hdetUpdate⟩ :=
        exists_sign_update_det_ne_zero target signs pivot hdetSigns
      refine ih (Function.update signs pivot value) (fun index hindex => ?_) hdetUpdate
      rcases eq_or_ne index pivot with rfl | hne
      · rwa [Function.update_self]
      · rw [Function.update_of_ne hne]
        refine hsigns index ?_
        rw [Finset.mem_insert]
        push Not
        exact ⟨hne, hindex⟩

/-- **CHART MEMBERSHIP, EXACT FORM.**  An orthogonal matrix in the sign chart
`det(E + Q) ≠ 0` is EXACTLY `E · cay(A)` for a skew `A` — namely
`A = icay(E·Q)`, whose domain condition is the chart condition because
`1 + E·Q = E·(E + Q)`. -/
theorem exists_skew_of_det_sign_add_ne_zero {target : Matrix (Fin size) (Fin size) ℝ}
    {signs : Fin size → ℝ} (horth : targetᵀ * target = 1)
    (hsigns : IsSignVector signs) (hdet : (diagonal signs + target).det ≠ 0) :
    ∃ skew : Matrix (Fin size) (Fin size) ℝ, skewᵀ = -skew ∧
      target = diagonal signs * cayleyOf skew := by
  have horthProd : (diagonal signs * target)ᵀ * (diagonal signs * target) = 1 := by
    rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal signs) (diagonal signs) target,
      hsigns.diagonal_mul_self, Matrix.one_mul, horth]
  have hfactor : (1 : Matrix (Fin size) (Fin size) ℝ) + diagonal signs * target
      = diagonal signs * (diagonal signs + target) := by
    rw [Matrix.mul_add, hsigns.diagonal_mul_self]
  have hdetProd : ((1 : Matrix (Fin size) (Fin size) ℝ)
      + diagonal signs * target).det ≠ 0 := by
    rw [hfactor, det_mul]
    exact mul_ne_zero hsigns.det_diagonal_ne_zero hdet
  refine ⟨inverseCayley (diagonal signs * target),
    transpose_inverseCayley horthProd hdetProd, ?_⟩
  rw [cayleyOf_inverseCayley horthProd hdetProd,
    ← Matrix.mul_assoc, hsigns.diagonal_mul_self, Matrix.one_mul]

/-- **THE PARITY BONUS.**  A sign chart only contains orthogonal matrices of its
own determinant sign: membership factors `Q = E·cay(A)` and `det cay(A) = 1`.
No eigenvalue argument. -/
theorem det_eq_det_diagonal_of_det_add_ne_zero {target : Matrix (Fin size) (Fin size) ℝ}
    {signs : Fin size → ℝ} (horth : targetᵀ * target = 1)
    (hsigns : IsSignVector signs) (hdet : (diagonal signs + target).det ≠ 0) :
    target.det = (diagonal signs).det := by
  obtain ⟨skew, hskew, htarget⟩ := exists_skew_of_det_sign_add_ne_zero horth hsigns hdet
  rw [htarget, det_mul, det_cayleyOf_of_skew hskew, mul_one]

/-- **K3 PACKAGED FOR THE PROPAGATION MODULE**: every special orthogonal matrix
lies in a POSITIVE sign chart (`det E = 1`), automatically — the covering chart
inherits the determinant sign by parity. -/
theorem exists_positive_chart {target : Matrix (Fin size) (Fin size) ℝ}
    (horth : targetᵀ * target = 1) (hdetOne : target.det = 1) :
    ∃ signs : Fin size → ℝ, IsSignVector signs ∧ (diagonal signs).det = 1 ∧
      (diagonal signs + target).det ≠ 0 := by
  obtain ⟨signs, hsigns, hne⟩ := exists_signVector_det_diagonal_add_ne_zero target
    (by rw [hdetOne]; exact one_ne_zero)
  refine ⟨signs, hsigns, ?_, hne⟩
  rw [← det_eq_det_diagonal_of_det_add_ne_zero horth hsigns hne, hdetOne]

/-! ## K4: the generic two-flip overlap witness -/

/-- The two-flip sign vector: `-1` exactly at the two flipped coordinates.  As a
diagonal matrix it is the transition label between two charts differing in one
index pair. -/
def flipTwoSign (first second : Fin size) : Fin size → ℝ :=
  fun index => if index = first ∨ index = second then -1 else 1

/-- The two-flip label is a sign vector. -/
theorem isSignVector_flipTwoSign (first second : Fin size) :
    IsSignVector (flipTwoSign first second) := by
  intro index
  simp only [flipTwoSign]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **THE J-BLOCK OVERLAP WITNESS**: the elementary skew matrix supported on one
index pair, `+1` at `(first, second)` and `-1` at `(second, first)`.  Swapping
the two indices negates it, which is exactly the opposite clearing orientation. -/
def flipTwoWitnessSkew (first second : Fin size) : Matrix (Fin size) (Fin size) ℝ :=
  Matrix.of fun rowIndex colIndex =>
    (if rowIndex = first ∧ colIndex = second then (1 : ℝ) else 0)
      - (if rowIndex = second ∧ colIndex = first then (1 : ℝ) else 0)

/-- The witness is skew, unconditionally — at equal indices it is the zero
matrix. -/
theorem transpose_flipTwoWitnessSkew (first second : Fin size) :
    (flipTwoWitnessSkew first second)ᵀ = -(flipTwoWitnessSkew first second) := by
  ext rowIndex colIndex
  simp only [transpose_apply, flipTwoWitnessSkew, of_apply]
  by_cases hrf : rowIndex = first <;> by_cases hrs : rowIndex = second <;>
    by_cases hcf : colIndex = first <;> by_cases hcs : colIndex = second <;>
    simp [hrf, hrs, hcf, hcs, and_comm]

/-- **THE CLEARED TWO-FLIP OVERLAP DETERMINANT IS NONZERO.**  With
`F = diag(flipTwoSign)` and `J` the witness, the cleared numerator
`(F + 1) + (F - 1)·J` equals `2·(1 - P - J)` for `P` the coordinate-pair
projector, and `(1 - P - J)² = F` by the four relations `P² = P`, `PJ = J`,
`JP = J`, `J² = -P`; so its determinant squares to `det F ≠ 0`.  No permutation
signs, no cofactor expansion, any size, either index order. -/
theorem det_flipTwoNumerator_ne_zero {first second : Fin size} (hne : first ≠ second) :
    ((diagonal (flipTwoSign first second) + 1)
      + (diagonal (flipTwoSign first second) - 1) * flipTwoWitnessSkew first second).det
      ≠ 0 := by
  classical
  set pairProj : Matrix (Fin size) (Fin size) ℝ :=
    diagonal (fun index => if index = first ∨ index = second then (1 : ℝ) else 0)
    with hpairProj
  set witness : Matrix (Fin size) (Fin size) ℝ := flipTwoWitnessSkew first second
    with hwitness
  have hFdecomp : diagonal (flipTwoSign first second) = 1 - pairProj - pairProj := by
    rw [hpairProj]
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply, flipTwoSign]
    by_cases hrc : rowIndex = colIndex
    · subst hrc
      by_cases hpair : rowIndex = first ∨ rowIndex = second
      · simp [hpair]
      · simp [hpair]
    · simp [hrc]
  have hPP : pairProj * pairProj = pairProj := by
    rw [hpairProj, diagonal_mul_diagonal]
    congr 1
    funext index
    by_cases hpair : index = first ∨ index = second
    · simp [hpair]
    · simp [hpair]
  have hPJ : pairProj * witness = witness := by
    rw [hpairProj, hwitness]
    ext rowIndex colIndex
    rw [Matrix.diagonal_mul]
    simp only [flipTwoWitnessSkew, of_apply]
    by_cases hrow : rowIndex = first ∨ rowIndex = second
    · simp [hrow]
    · push Not at hrow
      simp [hrow.1, hrow.2]
  have hJP : witness * pairProj = witness := by
    rw [hpairProj, hwitness]
    ext rowIndex colIndex
    rw [Matrix.mul_diagonal]
    simp only [flipTwoWitnessSkew, of_apply]
    by_cases hcol : colIndex = first ∨ colIndex = second
    · simp [hcol]
    · push Not at hcol
      simp [hcol.1, hcol.2]
  have hJJ : witness * witness = -pairProj := by
    rw [hwitness, hpairProj]
    ext rowIndex colIndex
    rw [Matrix.mul_apply, Matrix.neg_apply, Matrix.diagonal_apply]
    by_cases hrowFirst : rowIndex = first
    · rw [Finset.sum_eq_single second
        (fun other _ hother => by
          simp [flipTwoWitnessSkew, hother, hrowFirst, hne])
        (fun habs => absurd (Finset.mem_univ second) habs)]
      by_cases hcol : colIndex = first
      · norm_num [flipTwoWitnessSkew, hrowFirst, hcol, hne, Ne.symm hne]
      · norm_num [flipTwoWitnessSkew, hrowFirst, hcol, hne, Ne.symm hne, Ne.symm hcol]
    · by_cases hrowSecond : rowIndex = second
      · rw [Finset.sum_eq_single first
          (fun other _ hother => by
            simp [flipTwoWitnessSkew, hother, hrowSecond, Ne.symm hne])
          (fun habs => absurd (Finset.mem_univ first) habs)]
        by_cases hcol : colIndex = second
        · norm_num [flipTwoWitnessSkew, hrowSecond, hcol, hne, Ne.symm hne]
        · norm_num [flipTwoWitnessSkew, hrowSecond, hcol, hne, Ne.symm hne, Ne.symm hcol]
      · rw [Finset.sum_eq_zero
          (fun other _ => by simp [flipTwoWitnessSkew, hrowFirst, hrowSecond])]
        simp [hrowFirst, hrowSecond]
  have hXfactor : (diagonal (flipTwoSign first second) + 1)
        + (diagonal (flipTwoSign first second) - 1) * flipTwoWitnessSkew first second
      = (2 : ℝ) • (1 - pairProj - witness) := by
    rw [hFdecomp, ← hwitness]
    calc ((1 - pairProj - pairProj) + 1) + ((1 - pairProj - pairProj) - 1) * witness
        = ((1 + 1) - (pairProj + pairProj))
            - ((pairProj * witness) + (pairProj * witness)) := by noncomm_ring
      _ = ((1 + 1) - (pairProj + pairProj)) - (witness + witness) := by rw [hPJ]
      _ = (2 : ℝ) • (1 - pairProj - witness) := by
          rw [two_smul ℝ (1 - pairProj - witness : Matrix (Fin size) (Fin size) ℝ)]
          abel
  rw [hXfactor, det_smul]
  refine mul_ne_zero (pow_ne_zero _ two_ne_zero) ?_
  have hsquare : (1 - pairProj - witness) * (1 - pairProj - witness)
      = diagonal (flipTwoSign first second) := by
    calc (1 - pairProj - witness) * (1 - pairProj - witness)
        = 1 - pairProj - witness - pairProj + pairProj * pairProj + pairProj * witness
            - witness + witness * pairProj + witness * witness := by noncomm_ring
      _ = diagonal (flipTwoSign first second) := by
          rw [hPP, hPJ, hJP, hJJ, hFdecomp]
          abel
  have hdetSquare : (1 - pairProj - witness).det * (1 - pairProj - witness).det ≠ 0 := by
    rw [← det_mul, hsquare]
    exact (isSignVector_flipTwoSign first second).det_diagonal_ne_zero
  exact mul_self_ne_zero.mp hdetSquare

/-- **K4 CONSUMABLE**: the J-block witness lies in the overlap — the Cayley
point of the witness skew matrix belongs to the two-flip chart.  Together with
`Gtz.diagonal_add_diagonal_mul_of_isSignVector` this is the one-step overlap
between any two charts whose labels differ in exactly one index pair; the
opposite clearing orientation is this lemma at the swapped pair. -/
theorem det_flipTwoSign_add_cayleyOf_ne_zero {first second : Fin size}
    (hne : first ≠ second) :
    (diagonal (flipTwoSign first second)
      + cayleyOf (flipTwoWitnessSkew first second)).det ≠ 0 := by
  have hskewJ := transpose_flipTwoWitnessSkew first second
  have hdetJ : ((1 : Matrix (Fin size) (Fin size) ℝ)
      + flipTwoWitnessSkew first second).det ≠ 0 :=
    det_one_add_ne_zero_of_skew hskewJ
  have hclear := add_cayleyOf_mul_one_add (diagonal (flipTwoSign first second)) hdetJ
  have hnum := det_flipTwoNumerator_ne_zero hne
  intro hzero
  apply hnum
  rw [← hclear, det_mul, hzero, zero_mul]

end Gtz
