/-
# The `(7,3)` Veronese syzygy: the field-sensitive lever

**PROVED, unconditionally (no uniform-share hypothesis).**  For every
`WeightedDesign size 3` the Hadamard square of the direction Gram,
`W_ab = gamma_ab^2`, is the Gram matrix of the Veronese images
`u_c u_c^T` inside the six-dimensional space of symmetric `3 x 3` matrices:
`hadamardSquareGram_eq_veroneseRows_mul_transpose`.  Hence `W` is positive
semidefinite at every size (`posSemidef_hadamardSquareGram`) and its rank is at
most `6` (`rank_hadamardSquareGram_le_six`).  At size `7` that is a strict
deficiency, so `W` is SINGULAR (`det_hadamardSquareGram_eq_zero`) and a nonzero
real syzygy exists: some `theta /= 0` has `sum_c theta_c u_c u_c^T = 0`
(`exists_veroneseSyzygy`).  **This is the field-sensitive step.**  Over `C` the
Hermitian analogue lives in a `9`-dimensional space and `7 <= 9`, so no syzygy is
forced — which is exactly why barriers B1 (field-blind ceiling `0.0886`), B2
(counting-family cap, saturated at `(4,2)` and field-blind) and B3 (Veronese
requirement) do not reach this lever.

**PROVED, on the uniform-share stratum `atomShare = 3/7`.**  Both ends of the
spectrum of `W`, stated without any sorted-eigenvalue API (this repo has none):

* the row law `sum_b W_ab = 7/3` (`sum_hadamardSquareGram_row_of_uniformShare`),
  so the all-ones vector is an eigenvector at `7/3`
  (`hadamardSquareGram_mulVec_ones_of_uniformShare`);
* the Perron cap `(7/3) . 1 - W >= 0`
  (`posSemidef_smul_one_sub_hadamardSquareGram`), proved by the elementary
  certificate `sum_ab W_ab (x_a - x_b)^2 >= 0` — no interlacing, no spectral
  theory;
* `W >= 0` and `det W = 0` from the paragraph above.

Together: `0 <= spec(W) <= 7/3` with BOTH ends attained.  In hollow coordinates
`M = W - 1` this reads `lambda_min(M) = -1` exactly and `lambda_max(M) = 4/3`;
the eigenvalue-free spelling `M + 1 >= 0 and singular` is what downstream
consumers need and is what is landed.

**PROVED: the cap and the syzygy combine.**  The syzygy direction is free in the
cap, so the form may be evaluated at `x` while the norm is measured at any shift
`x + s . theta` (`dotProduct_hadamardSquareGram_mulVec_le_shifted`); optimising
the shift deflates the cap outright,
`x^T W x <= (1/shareValue) (|x|^2 - <x, theta>^2 / |theta|^2)`
(`dotProduct_hadamardSquareGram_mulVec_le_kernelDeflated`).  That inequality IS
the `tau`-to-`sigma` bridge, in a form free of any triple bookkeeping.

**PROVED: the trace guard.**  `sum_c theta_c = 0` is FORCED, not a choice
(`sum_eq_zero_of_momentCombination_eq_zero`): take traces of the syzygy and use
`|u_c| = 1`.  A retracted draft of this campaign proposed a syzygy with
`sum theta_c = 14`; that is impossible, and this theorem is the guard.

**PROVED: Gerzon at `(7,3)`.**  No uniform-share `(7,3)` design is equiangular
(`not_equiangular_uniformShare_sevenThree`): equiangularity makes
`W = (1 - alpha) . 1 + alpha . J`, the row law pins `alpha = 2/9`, and then
`W theta = (7/9) theta = 0` forces `theta = 0`.  Equivalently: there are no
seven equiangular lines in `R^3`.  This is the credibility check on the layer.

**PROVED: the second-moment floor.**  On the uniform-share stratum
`sum_a sum_b gamma_ab^4 >= 49/5` (`fourth_moment_ge_of_uniformShare`), hence the
ORDERED off-diagonal total `sum_a sum_{b /= a} w_ab^2 >= 14/5`
(`edge_second_moment_ge_of_uniformShare`); halving by symmetry gives the
unordered-edge floor `sum over the 21 edges of w_e^2 >= 7/5`, and that halving is
NOT separately mechanized.  The naive Cauchy-Schwarz floor from the row law alone
is `(14/3)^2 / 21 = 28/27 = 1.037...` (`naiveEdgeFloor_lt_syzygyEdgeFloor`
records the strict comparison; that `28/27` is the Cauchy-Schwarz optimum is
elementary and not mechanized).  Certificate: the exact test matrix
`Y_ab = 14 N [a = b] + 3 N - 14 theta_a theta_b` with `N = |theta|^2` has
`<W, Y> = 147 N` and `|Y|^2 = 2205 N^2`, so expanding
`sum_ab (W_ab - Y_ab/(15 N))^2 >= 0` gives the floor.  CONSEQUENCE: uniform edge
weights are IMPOSSIBLE on this stratum — `w == 2/9` would give
`lambda_min(M) = -2/9`, not `-1` — so the weights are always forced away from
uniform by a definite amount.

**PROVED: the sigma gate.**  `sigma_T <= 1/3` implies `sigma_T - 3 P_T <= 4/9`
(`sigma_sub_three_mul_product_le_four_ninths_of_sigma_le_third`), hence, through
the landed C1-IFF criterion, that `T` DOMINATES
(`dominates_triple_of_directionTripleSigma_le_third`).  Sharp: equality holds at
`sigma = 1/3, P = -1/27`, which is exactly the tetrahedral tie of the landed
witness.  The certificate is the three-variable AM-GM
`27 (abc)^2 <= (a^2+b^2+c^2)^3` plus the factorisation
`27 s^3 - 81 s^2 + 72 s - 16 = (3s - 1)(3s - 4)^2`.

**PROVED: the witness calibration.**  On `Gtz.sevenThreeBasisTetrapodDesign` all
forty-nine Hadamard-square entries are computed
(`hadamardSquareGram_sevenThreeBasisTetrapodDesign`: `1` on the diagonal, `0` on
an axis-axis edge, `1/3` mixed, `1/9` tetrapod-tetrapod).  The fourth-moment
total is exactly `265/27`, clearing the floor `49/5` by exactly `2/135`
(`fourth_moment_sevenThreeBasisTetrapodDesign`,
`fourth_moment_sevenThreeBasisTetrapodDesign_sub_floor`), and the ordered
off-diagonal total is `76/27` (unordered `38/27`).  So the floor is within
`2/135` of the truth on this stratum, and every uniform-share theorem here is
non-vacuous (`fourth_moment_ge_sevenThreeBasisTetrapodDesign`).

**NOT PROVED — the exact remaining gap.**  The syzygy is not turned into a
dominating triple.  Writing `tau_T = sum_{c in T} theta_c` and
`z_T = 1_T - (3/7) . ones`, the deflated cap specialised at `x = z_T` — using
`|z_T|^2 = 12/7`, `<z_T, theta> = tau_T` and `z_T^T W z_T = 2 sigma_T` — gives
`sigma_T <= 2 - (7/6) tau_T^2 / |theta|^2`, so `tau_T^2 / |theta|^2 >= 10/7`
would fire the sigma gate.  That specialisation is pure indicator bookkeeping and
is NOT mechanized here; neither is the counting identity
`sum over the 35 triples of tau_T^2 = 10 |theta|^2`, which is what shows the route
is SHORT: it yields only `max_T tau_T^2 >= (2/7) |theta|^2`, a factor of five
below the gate.  Both the general bridge
(`dotProduct_hadamardSquareGram_mulVec_le_kernelDeflated`) and the gate it feeds
(`dominates_triple_of_directionTripleSigma_le_third`) ARE mechanized; only the
bookkeeping between them is not.  And note the `tau`-maximizing triple is
relabelling-invariant, so it can never be a SELECTOR: that is refuted by
`Gtz.exists_symmetry_with_no_fixed_dominatingSubset`.  As a GATE the route is
untouched; as a selector it is dead.

**NOT PROVED — barrier B2.**  The counting-family ceiling is recorded here only
as exact arithmetic: the closed form `countingFamilyCeiling`, its three values
`-1/6`, `-5/36`, `-38/315` at `(4,2)`, `(6,3)`, `(7,3)`, the saturation identity
`countingFamilyCeiling 4 2 = Gtz.combinedValueFloor 4 2`, and the strict
inequalities `countingFamilyCeiling 4 2 < 1/4 - sqrt 3 / 6 < 0` against the
complex `(4,2)` SIC value.  The no-go CONTENT — that no member of the
elementary / Cauchy-Binet counting family can exceed the ceiling — is NOT
mechanized, and the identification of `1/4 - sqrt 3 / 6` with the SIC value is
cited from the campaign ledger, not proved.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.FrameConservation
import Gtz.LinAlg.SchurRankOne
import Gtz.Quantitative.ElementaryValueFloor
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.SevenThreeInvolution

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## 1. The Veronese embedding of `R^3` into a six-dimensional coordinate space

`veroneseCoordinate` sends `x` to the six products `x_i x_j` (`i <= j`), the
off-diagonal ones weighted by `sqrt 2` so that the plain dot product of two
images is the SQUARE of the dot product of the arguments.  A seventh coordinate
is carried and is identically zero: it makes the row matrix square at size
seven, which is what turns the dimension count into a determinant. -/

/-- The Veronese coordinates of a vector in `R^3`, padded to seven slots with a
final zero.  The six live slots are `x_0^2, x_1^2, x_2^2` and
`sqrt 2 x_0 x_1, sqrt 2 x_0 x_2, sqrt 2 x_1 x_2`. -/
noncomputable def veroneseCoordinate (vector : Fin 3 → ℝ) (coordIndex : Fin 7) : ℝ :=
  ![vector 0 ^ 2, vector 1 ^ 2, vector 2 ^ 2,
    Real.sqrt 2 * (vector 0 * vector 1),
    Real.sqrt 2 * (vector 0 * vector 2),
    Real.sqrt 2 * (vector 1 * vector 2),
    0] coordIndex

@[simp] theorem veroneseCoordinate_zero (vector : Fin 3 → ℝ) :
    veroneseCoordinate vector 0 = vector 0 ^ 2 := rfl

@[simp] theorem veroneseCoordinate_one (vector : Fin 3 → ℝ) :
    veroneseCoordinate vector 1 = vector 1 ^ 2 := rfl

@[simp] theorem veroneseCoordinate_two (vector : Fin 3 → ℝ) :
    veroneseCoordinate vector 2 = vector 2 ^ 2 := rfl

@[simp] theorem veroneseCoordinate_three (vector : Fin 3 → ℝ) :
    veroneseCoordinate vector 3 = Real.sqrt 2 * (vector 0 * vector 1) := rfl

@[simp] theorem veroneseCoordinate_four (vector : Fin 3 → ℝ) :
    veroneseCoordinate vector 4 = Real.sqrt 2 * (vector 0 * vector 2) := rfl

@[simp] theorem veroneseCoordinate_five (vector : Fin 3 → ℝ) :
    veroneseCoordinate vector 5 = Real.sqrt 2 * (vector 1 * vector 2) := rfl

@[simp] theorem veroneseCoordinate_six (vector : Fin 3 → ℝ) :
    veroneseCoordinate vector 6 = 0 := rfl

/-- **THE VERONESE IDENTITY.**  `<v(x), v(y)> = <x, y>^2`.  This one `ring`
identity (plus `sqrt 2 . sqrt 2 = 2`) is the entire content of the Veronese
lever: squaring a Gram entry is taking a Gram entry of the squared vectors. -/
theorem veroneseCoordinate_dotProduct (leftVector rightVector : Fin 3 → ℝ) :
    veroneseCoordinate leftVector ⬝ᵥ veroneseCoordinate rightVector
      = (leftVector ⬝ᵥ rightVector) ^ 2 := by
  have hsqrtSquare : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [dotProduct, Fin.sum_univ_seven, Fin.sum_univ_three, veroneseCoordinate_zero,
    veroneseCoordinate_one, veroneseCoordinate_two, veroneseCoordinate_three,
    veroneseCoordinate_four, veroneseCoordinate_five, veroneseCoordinate_six]
  linear_combination (leftVector 0 * leftVector 1 * rightVector 0 * rightVector 1
    + leftVector 0 * leftVector 2 * rightVector 0 * rightVector 2
    + leftVector 1 * leftVector 2 * rightVector 1 * rightVector 2) * hsqrtSquare

/-- The Veronese images of a design's unit directions, as the rows of a
`size x 7` matrix whose last column vanishes.  Internal scaffolding only: the
dead seventh column exists solely to make the row matrix square at size seven,
which is what turns the dimension count into a determinant.  Kept `private`
because this name once collided with a public `Gtz.veroneseRows` in
`Gtz/Quantitative/SevenThreeMetricBound.lean`, a collision that was a HARD
umbrella-import failure, not a silent shadow.  It is now resolved on BOTH sides:
this one is `private` and that one was renamed `Gtz.veroneseSquareRows`, so no
public `Gtz.veroneseRows` exists anywhere in the tree -- do not reintroduce one.
The public six-column form here is `veroneseSixRows`. -/
private noncomputable def veroneseRows
    (design : WeightedDesign size 3) : Matrix (Fin size) (Fin 7) ℝ :=
  Matrix.of fun atomIndex coordIndex =>
    veroneseCoordinate (unitAtom design atomIndex) coordIndex

/-- The same rows with the dead seventh column dropped: an honest `size x 6`
matrix, which is what carries the rank bound. -/
noncomputable def veroneseSixRows (design : WeightedDesign size 3) :
    Matrix (Fin size) (Fin 6) ℝ :=
  Matrix.of fun atomIndex coordIndex =>
    veroneseCoordinate (unitAtom design atomIndex) coordIndex.castSucc

/-! ## 2. The Hadamard square of the direction Gram is a Veronese Gram -/

/-- **The Hadamard square of the direction Gram**, `W_ab = gamma_ab^2`. -/
noncomputable def hadamardSquareGram (design : WeightedDesign size 3) :
    Matrix (Fin size) (Fin size) ℝ :=
  Matrix.of fun firstIndex secondIndex => directionGram design firstIndex secondIndex ^ 2

@[simp] theorem hadamardSquareGram_apply (design : WeightedDesign size 3)
    (firstIndex secondIndex : Fin size) :
    hadamardSquareGram design firstIndex secondIndex
      = directionGram design firstIndex secondIndex ^ 2 := rfl

/-- Every entry is nonnegative — it is a square. -/
theorem hadamardSquareGram_nonneg (design : WeightedDesign size 3)
    (firstIndex secondIndex : Fin size) :
    0 ≤ hadamardSquareGram design firstIndex secondIndex := by
  rw [hadamardSquareGram_apply]
  positivity

theorem hadamardSquareGram_comm (design : WeightedDesign size 3)
    (firstIndex secondIndex : Fin size) :
    hadamardSquareGram design firstIndex secondIndex
      = hadamardSquareGram design secondIndex firstIndex := by
  rw [hadamardSquareGram_apply, hadamardSquareGram_apply, directionGram_comm]

/-- The diagonal is one off the degenerate atoms. -/
theorem hadamardSquareGram_diagonal (design : WeightedDesign size 3) {atomIndex : Fin size}
    (hpositive : 0 < leverageOf (design.atom atomIndex)) :
    hadamardSquareGram design atomIndex atomIndex = 1 := by
  rw [hadamardSquareGram_apply, directionGram_self design hpositive, one_pow]

theorem isHermitian_hadamardSquareGram (design : WeightedDesign size 3) :
    (hadamardSquareGram design).IsHermitian := by
  refine isHermitian_of_transpose_eq ?_
  ext firstIndex secondIndex
  rw [Matrix.transpose_apply, hadamardSquareGram_comm design secondIndex firstIndex]

/-- **THE VERONESE FACTORISATION.**  `W = V V^T` with `V` the Veronese row
matrix.  Unconditional, at every size. -/
theorem hadamardSquareGram_eq_veroneseRows_mul_transpose (design : WeightedDesign size 3) :
    hadamardSquareGram design = veroneseRows design * (veroneseRows design)ᵀ := by
  ext firstIndex secondIndex
  rw [Matrix.mul_apply]
  simp only [hadamardSquareGram, veroneseRows, Matrix.of_apply, Matrix.transpose_apply]
  rw [directionGram, ← veroneseCoordinate_dotProduct]
  rfl

/-- The dead seventh column may be dropped: the six-column factorisation is the
same matrix. -/
theorem hadamardSquareGram_eq_veroneseSixRows_mul_transpose (design : WeightedDesign size 3) :
    hadamardSquareGram design = veroneseSixRows design * (veroneseSixRows design)ᵀ := by
  rw [hadamardSquareGram_eq_veroneseRows_mul_transpose]
  ext firstIndex secondIndex
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [veroneseRows, veroneseSixRows, Matrix.of_apply, Matrix.transpose_apply,
    show (Fin.last 6) = (6 : Fin 7) from rfl, veroneseCoordinate_six]
  rw [mul_zero, add_zero]

/-- **THE HADAMARD SQUARE IS POSITIVE SEMIDEFINITE**, at every size, with no
hypothesis: it is a Gram matrix of Veronese images.  (Equivalently the Schur
product theorem specialised to squaring a correlation matrix — but proved here
constructively, so nothing depends on a Schur-product API this rev does not
have.) -/
theorem posSemidef_hadamardSquareGram (design : WeightedDesign size 3) :
    (hadamardSquareGram design).PosSemidef := by
  rw [hadamardSquareGram_eq_veroneseRows_mul_transpose]
  simpa using Matrix.posSemidef_self_mul_conjTranspose (veroneseRows design)

/-- **THE RANK BOUND**: `rank W <= 6 = binom(3+1, 2)`, at every size.  This is
the field-sensitive statement.  Over `C` the corresponding bound is `k^2 = 9`,
which is why the complex problem admits configurations the real one cannot. -/
theorem rank_hadamardSquareGram_le_six (design : WeightedDesign size 3) :
    (hadamardSquareGram design).rank ≤ 6 := by
  rw [hadamardSquareGram_eq_veroneseSixRows_mul_transpose]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  simpa using Matrix.rank_le_card_width (veroneseSixRows design)

/-! ## 3. At size seven the rank deficiency is strict: the syzygy -/

theorem det_veroneseRows_eq_zero (design : WeightedDesign 7 3) :
    (veroneseRows design).det = 0 := by
  rw [← Matrix.det_transpose]
  refine Matrix.det_eq_zero_of_row_eq_zero 6 fun atomIndex => ?_
  simp only [Matrix.transpose_apply, veroneseRows, Matrix.of_apply, veroneseCoordinate_six]

/-- **THE HADAMARD SQUARE IS SINGULAR AT `(7,3)`** — unconditional, no
uniform-share hypothesis.  Seven Veronese images cannot be independent in a
six-dimensional space.  Together with `posSemidef_hadamardSquareGram` this is
the eigenvalue-free statement `lambda_min(W) = 0`, equivalently
`lambda_min(W - 1) = -1`. -/
theorem det_hadamardSquareGram_eq_zero (design : WeightedDesign 7 3) :
    (hadamardSquareGram design).det = 0 := by
  rw [hadamardSquareGram_eq_veroneseRows_mul_transpose, Matrix.det_mul, Matrix.det_transpose,
    det_veroneseRows_eq_zero]
  ring

/-- A real linear combination of the design's rank-one direction atoms. -/
noncomputable def momentCombination (design : WeightedDesign size 3)
    (coefficient : Fin size → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ atomIndex, coefficient atomIndex • atomMatrix (unitAtom design atomIndex)

theorem momentCombination_apply (design : WeightedDesign size 3) (coefficient : Fin size → ℝ)
    (rowIndex colIndex : Fin 3) :
    momentCombination design coefficient rowIndex colIndex
      = ∑ atomIndex, coefficient atomIndex
          * (unitAtom design atomIndex rowIndex * unitAtom design atomIndex colIndex) := by
  simp only [momentCombination, Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul]

/-- **THE SYZYGY EXISTS AT `(7,3)`.**  Some nonzero real `theta` satisfies
`sum_c theta_c u_c u_c^T = 0`.  Only `7 > binom(3+1,2) = 6` is used — no
isotropy, no uniform share, no equal weights.  Over `C` the same count gives
`7 <= 3^2 = 9` and no syzygy is forced: this is the one lever in the campaign
that sees the field. -/
theorem exists_veroneseSyzygy (design : WeightedDesign 7 3) :
    ∃ coefficient : Fin 7 → ℝ, coefficient ≠ 0 ∧ momentCombination design coefficient = 0 := by
  obtain ⟨coefficient, hnonzero, hkernel⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr
      (by rw [Matrix.det_transpose]; exact det_veroneseRows_eq_zero design :
        ((veroneseRows design)ᵀ).det = 0)
  refine ⟨coefficient, hnonzero, ?_⟩
  have hsqrtNonzero : Real.sqrt 2 ≠ 0 := by positivity
  have hcoord : ∀ coordIndex : Fin 7,
      ∑ atomIndex, veroneseCoordinate (unitAtom design atomIndex) coordIndex
        * coefficient atomIndex = 0 := by
    intro coordIndex
    have hentry := congrFun hkernel coordIndex
    simpa [Matrix.mulVec, dotProduct, veroneseRows] using hentry
  have hzeroZero : ∑ atomIndex, coefficient atomIndex
      * (unitAtom design atomIndex 0 * unitAtom design atomIndex 0) = 0 := by
    have hbase := hcoord 0
    simp only [veroneseCoordinate_zero] at hbase
    rw [← hbase]
    exact Finset.sum_congr rfl fun index _ => by ring
  have honeOne : ∑ atomIndex, coefficient atomIndex
      * (unitAtom design atomIndex 1 * unitAtom design atomIndex 1) = 0 := by
    have hbase := hcoord 1
    simp only [veroneseCoordinate_one] at hbase
    rw [← hbase]
    exact Finset.sum_congr rfl fun index _ => by ring
  have htwoTwo : ∑ atomIndex, coefficient atomIndex
      * (unitAtom design atomIndex 2 * unitAtom design atomIndex 2) = 0 := by
    have hbase := hcoord 2
    simp only [veroneseCoordinate_two] at hbase
    rw [← hbase]
    exact Finset.sum_congr rfl fun index _ => by ring
  have hzeroOne : ∑ atomIndex, coefficient atomIndex
      * (unitAtom design atomIndex 0 * unitAtom design atomIndex 1) = 0 := by
    have hbase := hcoord 3
    simp only [veroneseCoordinate_three] at hbase
    have hscaled : Real.sqrt 2 * ∑ atomIndex, coefficient atomIndex
        * (unitAtom design atomIndex 0 * unitAtom design atomIndex 1) = 0 := by
      rw [Finset.mul_sum, ← hbase]
      exact Finset.sum_congr rfl fun index _ => by ring
    exact (mul_eq_zero.mp hscaled).resolve_left hsqrtNonzero
  have hzeroTwo : ∑ atomIndex, coefficient atomIndex
      * (unitAtom design atomIndex 0 * unitAtom design atomIndex 2) = 0 := by
    have hbase := hcoord 4
    simp only [veroneseCoordinate_four] at hbase
    have hscaled : Real.sqrt 2 * ∑ atomIndex, coefficient atomIndex
        * (unitAtom design atomIndex 0 * unitAtom design atomIndex 2) = 0 := by
      rw [Finset.mul_sum, ← hbase]
      exact Finset.sum_congr rfl fun index _ => by ring
    exact (mul_eq_zero.mp hscaled).resolve_left hsqrtNonzero
  have honeTwo : ∑ atomIndex, coefficient atomIndex
      * (unitAtom design atomIndex 1 * unitAtom design atomIndex 2) = 0 := by
    have hbase := hcoord 5
    simp only [veroneseCoordinate_five] at hbase
    have hscaled : Real.sqrt 2 * ∑ atomIndex, coefficient atomIndex
        * (unitAtom design atomIndex 1 * unitAtom design atomIndex 2) = 0 := by
      rw [Finset.mul_sum, ← hbase]
      exact Finset.sum_congr rfl fun index _ => by ring
    exact (mul_eq_zero.mp hscaled).resolve_left hsqrtNonzero
  have hflip : ∀ firstIndex secondIndex : Fin 3,
      (∑ atomIndex, coefficient atomIndex
          * (unitAtom design atomIndex firstIndex * unitAtom design atomIndex secondIndex)) = 0 →
      (∑ atomIndex, coefficient atomIndex
          * (unitAtom design atomIndex secondIndex
              * unitAtom design atomIndex firstIndex)) = 0 :=
    fun _ _ hbase => Eq.trans (Finset.sum_congr rfl fun index _ => by ring) hbase
  ext rowIndex colIndex
  rw [momentCombination_apply, Matrix.zero_apply]
  fin_cases rowIndex <;> fin_cases colIndex
  · exact hzeroZero
  · exact hzeroOne
  · exact hzeroTwo
  · exact hflip 0 1 hzeroOne
  · exact honeOne
  · exact honeTwo
  · exact hflip 0 2 hzeroTwo
  · exact hflip 1 2 honeTwo
  · exact htwoTwo

/-- A syzygy kills every direction's quadratic form: `sum_c theta_c <u_c, x>^2 = 0`
for every test vector.  This is the only consequence of the syzygy the rest of
the file uses. -/
theorem sum_mul_sq_dotProduct_of_momentCombination_eq_zero (design : WeightedDesign size 3)
    {coefficient : Fin size → ℝ} (hsyzygy : momentCombination design coefficient = 0)
    (testVector : Fin 3 → ℝ) :
    ∑ atomIndex, coefficient atomIndex * (unitAtom design atomIndex ⬝ᵥ testVector) ^ 2 = 0 := by
  have hentry : ∀ rowIndex colIndex : Fin 3,
      ∑ atomIndex, coefficient atomIndex
        * (unitAtom design atomIndex rowIndex * unitAtom design atomIndex colIndex) = 0 := by
    intro rowIndex colIndex
    rw [← momentCombination_apply, hsyzygy, Matrix.zero_apply]
  have hexpand : ∑ atomIndex, coefficient atomIndex
        * (unitAtom design atomIndex ⬝ᵥ testVector) ^ 2
      = testVector 0 * testVector 0
          * (∑ atomIndex, coefficient atomIndex
              * (unitAtom design atomIndex 0 * unitAtom design atomIndex 0))
        + testVector 1 * testVector 1
          * (∑ atomIndex, coefficient atomIndex
              * (unitAtom design atomIndex 1 * unitAtom design atomIndex 1))
        + testVector 2 * testVector 2
          * (∑ atomIndex, coefficient atomIndex
              * (unitAtom design atomIndex 2 * unitAtom design atomIndex 2))
        + 2 * (testVector 0 * testVector 1)
          * (∑ atomIndex, coefficient atomIndex
              * (unitAtom design atomIndex 0 * unitAtom design atomIndex 1))
        + 2 * (testVector 0 * testVector 2)
          * (∑ atomIndex, coefficient atomIndex
              * (unitAtom design atomIndex 0 * unitAtom design atomIndex 2))
        + 2 * (testVector 1 * testVector 2)
          * (∑ atomIndex, coefficient atomIndex
              * (unitAtom design atomIndex 1 * unitAtom design atomIndex 2)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    simp only [dotProduct, Fin.sum_univ_three]
    ring
  rw [hexpand, hentry 0 0, hentry 1 1, hentry 2 2, hentry 0 1, hentry 0 2, hentry 1 2]
  ring

/-- **THE TRACE GUARD.**  `sum_c theta_c = 0` is FORCED by any syzygy on unit
directions — take the trace of `sum_c theta_c u_c u_c^T = 0` and use
`tr(u_c u_c^T) = |u_c|^2 = 1`.  A retracted draft of this campaign proposed a
`(7,3)` syzygy with `sum theta_c = 14`; this theorem is why that is impossible,
and it must be checked before any candidate `theta` is used. -/
theorem sum_eq_zero_of_momentCombination_eq_zero (design : WeightedDesign size 3)
    (hleverage : ∀ atomIndex, 0 < leverageOf (design.atom atomIndex))
    {coefficient : Fin size → ℝ} (hsyzygy : momentCombination design coefficient = 0) :
    ∑ atomIndex, coefficient atomIndex = 0 := by
  have htrace : Matrix.trace (momentCombination design coefficient)
      = ∑ atomIndex, coefficient atomIndex := by
    rw [momentCombination, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [Matrix.trace_smul, trace_atomMatrix, leverageOf_unitAtom design (hleverage atomIndex),
      smul_eq_mul, mul_one]
  rw [← htrace, hsyzygy, Matrix.trace_zero]

/-- The syzygy lies in the kernel of the Hadamard square: `W theta = 0`. -/
theorem hadamardSquareGram_mulVec_eq_zero (design : WeightedDesign size 3)
    {coefficient : Fin size → ℝ} (hsyzygy : momentCombination design coefficient = 0) :
    hadamardSquareGram design *ᵥ coefficient = 0 := by
  funext atomIndex
  rw [Matrix.mulVec, Pi.zero_apply, dotProduct,
    ← sum_mul_sq_dotProduct_of_momentCombination_eq_zero design hsyzygy (unitAtom design atomIndex)]
  refine Finset.sum_congr rfl fun otherIndex _ => ?_
  rw [hadamardSquareGram_apply, directionGram_comm, directionGram]
  ring

/-- Hence the syzygy is a null vector of the form: `theta^T W theta = 0`. -/
theorem dotProduct_hadamardSquareGram_mulVec_eq_zero (design : WeightedDesign size 3)
    {coefficient : Fin size → ℝ} (hsyzygy : momentCombination design coefficient = 0) :
    coefficient ⬝ᵥ (hadamardSquareGram design *ᵥ coefficient) = 0 := by
  rw [hadamardSquareGram_mulVec_eq_zero design hsyzygy, dotProduct_zero]

/-! ## 4. The two ends of the spectrum, without a sorted-eigenvalue API -/

/-- Pull three scalars out of a sum of the shape `f - c1 g + c2 h`. -/
theorem sum_sub_scaled_add_scaled {position : Type*} [Fintype position]
    (firstFun secondFun thirdFun : position → ℝ) (firstScale secondScale : ℝ) :
    ∑ index, (firstFun index - firstScale * secondFun index + secondScale * thirdFun index)
      = (∑ index, firstFun index) - firstScale * ∑ index, secondFun index
        + secondScale * ∑ index, thirdFun index := by
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The expansion of a scaled-difference square sum: the whole content of an
"expand a square" positivity certificate. -/
theorem sum_sq_sub_scaled {position : Type*} [Fintype position]
    (leftFun rightFun : position → ℝ) (scale : ℝ) :
    ∑ index, (leftFun index - scale * rightFun index) ^ 2
      = (∑ index, leftFun index ^ 2)
        - 2 * scale * ∑ index, leftFun index * rightFun index
        + scale ^ 2 * ∑ index, rightFun index ^ 2 := by
  rw [Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) =>
    show (leftFun index - scale * rightFun index) ^ 2
      = leftFun index ^ 2 - (2 * scale) * (leftFun index * rightFun index)
        + scale ^ 2 * rightFun index ^ 2 from by ring]
  exact sum_sub_scaled_add_scaled (fun index => leftFun index ^ 2)
    (fun index => leftFun index * rightFun index) (fun index => rightFun index ^ 2)
    (2 * scale) (scale ^ 2)

theorem dotProduct_mulVec_eq_entrySum (form : Matrix (Fin size) (Fin size) ℝ)
    (testVector : Fin size → ℝ) :
    testVector ⬝ᵥ (form *ᵥ testVector)
      = ∑ firstIndex, ∑ secondIndex, form firstIndex secondIndex
          * (testVector firstIndex * testVector secondIndex) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun firstIndex _ =>
    Finset.sum_congr rfl fun secondIndex _ => by ring

/-- **THE ROW LAW.**  At a uniform share the squared correlations out of any atom
total `1/shareValue` — at `(7,3)` that is `7/3`.  This is the shipped
`Gtz.sum_atomShare_mul_sq_directionGram` with the share pulled out. -/
theorem sum_hadamardSquareGram_row_of_uniformShare (design : WeightedDesign size 3)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare design atomIndex = shareValue)
    (hpositive : 0 < shareValue) (atomIndex : Fin size) :
    ∑ otherIndex, hadamardSquareGram design atomIndex otherIndex = shareValue⁻¹ := by
  have hleverage : 0 < leverageOf (design.atom atomIndex) :=
    leverageOf_pos_of_atomShare_pos design (by rw [huniform atomIndex]; exact hpositive)
  have hrow := sum_atomShare_mul_sq_directionGram design hleverage
  have hpulled : shareValue
      * ∑ otherIndex, directionGram design atomIndex otherIndex ^ 2 = 1 := by
    rw [Finset.mul_sum, ← hrow]
    exact Finset.sum_congr rfl fun otherIndex _ => by rw [huniform otherIndex]
  have hnonzero : shareValue ≠ 0 := hpositive.ne'
  simp only [hadamardSquareGram_apply]
  field_simp
  linear_combination hpulled

theorem sum_hadamardSquareGram_column_of_uniformShare (design : WeightedDesign size 3)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare design atomIndex = shareValue)
    (hpositive : 0 < shareValue) (otherIndex : Fin size) :
    ∑ atomIndex, hadamardSquareGram design atomIndex otherIndex = shareValue⁻¹ := by
  rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) =>
    hadamardSquareGram_comm design atomIndex otherIndex]
  exact sum_hadamardSquareGram_row_of_uniformShare design huniform hpositive otherIndex

/-- **THE PERRON EIGENVECTOR.**  The all-ones vector is an eigenvector of `W` at
the common row sum `1/shareValue`, so that value IS in the spectrum. -/
theorem hadamardSquareGram_mulVec_ones_of_uniformShare (design : WeightedDesign size 3)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare design atomIndex = shareValue)
    (hpositive : 0 < shareValue) (atomIndex : Fin size) :
    (hadamardSquareGram design *ᵥ fun _ => (1 : ℝ)) atomIndex = shareValue⁻¹ := by
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun otherIndex (_ : otherIndex ∈ Finset.univ) =>
    mul_one (hadamardSquareGram design atomIndex otherIndex)]
  exact sum_hadamardSquareGram_row_of_uniformShare design huniform hpositive atomIndex

/-- **THE PERRON CAP, as a quadratic-form bound.**  Nothing in the spectrum of
`W` exceeds the common row sum.  Certificate: `sum_ab W_ab (x_a - x_b)^2 >= 0`,
using only that the entries are nonnegative and the row sums are constant.  No
interlacing, no eigenvalues. -/
theorem dotProduct_hadamardSquareGram_mulVec_le (design : WeightedDesign size 3)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare design atomIndex = shareValue)
    (hpositive : 0 < shareValue) (testVector : Fin size → ℝ) :
    testVector ⬝ᵥ (hadamardSquareGram design *ᵥ testVector)
      ≤ shareValue⁻¹ * ∑ atomIndex, testVector atomIndex ^ 2 := by
  have hrowTotal : ∀ atomIndex : Fin size,
      ∑ otherIndex, hadamardSquareGram design atomIndex otherIndex = shareValue⁻¹ :=
    sum_hadamardSquareGram_row_of_uniformShare design huniform hpositive
  have hrowBound : ∀ firstIndex : Fin size,
      ∑ secondIndex, hadamardSquareGram design firstIndex secondIndex
          * (testVector firstIndex * testVector secondIndex)
        ≤ (1 / 2) * (shareValue⁻¹ * testVector firstIndex ^ 2)
          + (1 / 2) * ∑ secondIndex, hadamardSquareGram design firstIndex secondIndex
              * testVector secondIndex ^ 2 := by
    intro firstIndex
    have hpointwise : ∀ secondIndex ∈ (Finset.univ : Finset (Fin size)),
        hadamardSquareGram design firstIndex secondIndex
            * (testVector firstIndex * testVector secondIndex)
          ≤ (1 / 2) * (hadamardSquareGram design firstIndex secondIndex
              * testVector firstIndex ^ 2)
            + (1 / 2) * (hadamardSquareGram design firstIndex secondIndex
                * testVector secondIndex ^ 2) := by
      intro secondIndex _
      nlinarith [hadamardSquareGram_nonneg design firstIndex secondIndex,
        sq_nonneg (testVector firstIndex - testVector secondIndex)]
    refine (Finset.sum_le_sum hpointwise).trans_eq ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul,
      hrowTotal firstIndex]
  have hswap : ∑ firstIndex, ∑ secondIndex, hadamardSquareGram design firstIndex secondIndex
        * testVector secondIndex ^ 2
      = shareValue⁻¹ * ∑ secondIndex, testVector secondIndex ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun secondIndex _ => by
      rw [← Finset.sum_mul,
        sum_hadamardSquareGram_column_of_uniformShare design huniform hpositive secondIndex]
  rw [dotProduct_mulVec_eq_entrySum]
  refine (Finset.sum_le_sum fun firstIndex (_ : firstIndex ∈ Finset.univ) =>
    hrowBound firstIndex).trans_eq ?_
  rw [Finset.sum_add_distrib,
    show ∑ firstIndex, (1 / 2 : ℝ) * (shareValue⁻¹ * testVector firstIndex ^ 2)
        = (1 / 2) * shareValue⁻¹ * ∑ firstIndex, testVector firstIndex ^ 2 from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun firstIndex _ => by ring,
    show ∑ firstIndex, (1 / 2 : ℝ) * ∑ secondIndex,
          hadamardSquareGram design firstIndex secondIndex * testVector secondIndex ^ 2
        = (1 / 2) * ∑ firstIndex, ∑ secondIndex,
          hadamardSquareGram design firstIndex secondIndex * testVector secondIndex ^ 2 from by
      rw [Finset.mul_sum],
    hswap]
  ring

/-- **THE PERRON CAP, as a Loewner statement**: `(1/shareValue) . 1 - W >= 0`.
At `(7,3)`: `(7/3) . 1 - W >= 0`.  With `posSemidef_hadamardSquareGram` and
`det_hadamardSquareGram_eq_zero` this sandwiches the spectrum in `[0, 7/3]` with
both ends attained. -/
theorem posSemidef_smul_one_sub_hadamardSquareGram (design : WeightedDesign size 3)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare design atomIndex = shareValue)
    (hpositive : 0 < shareValue) :
    (shareValue⁻¹ • (1 : Matrix (Fin size) (Fin size) ℝ) - hadamardSquareGram design).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun testVector => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
      transpose_eq_of_isHermitian (isHermitian_hadamardSquareGram design)]
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, sub_nonneg]
    refine (dotProduct_hadamardSquareGram_mulVec_le design huniform hpositive testVector).trans ?_
    refine le_of_eq (congrArg (fun total => shareValue⁻¹ * total) ?_)
    exact Finset.sum_congr rfl fun atomIndex _ => pow_two (testVector atomIndex)

/-- **THE SHARPENED CAP.**  The syzygy direction is FREE in the Perron cap: the
form may be evaluated at `x` while the norm is measured at any shift
`x + shift . theta`.  This is where the syzygy meets the spectral bound, and it
is the general form of the `tau`-to-`sigma` bridge. -/
theorem dotProduct_hadamardSquareGram_mulVec_le_shifted (design : WeightedDesign size 3)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare design atomIndex = shareValue)
    (hpositive : 0 < shareValue) {coefficient : Fin size → ℝ}
    (hsyzygy : momentCombination design coefficient = 0)
    (testVector : Fin size → ℝ) (shift : ℝ) :
    testVector ⬝ᵥ (hadamardSquareGram design *ᵥ testVector)
      ≤ shareValue⁻¹
        * ∑ atomIndex, (testVector atomIndex + shift * coefficient atomIndex) ^ 2 := by
  have hkernel := hadamardSquareGram_mulVec_eq_zero design hsyzygy
  have hshiftInvariant : (testVector + shift • coefficient) ⬝ᵥ
        (hadamardSquareGram design *ᵥ (testVector + shift • coefficient))
      = testVector ⬝ᵥ (hadamardSquareGram design *ᵥ testVector) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hkernel, smul_zero, add_zero, add_dotProduct,
      smul_dotProduct, smul_eq_mul,
      dot_mulVec_comm (transpose_eq_of_isHermitian (isHermitian_hadamardSquareGram design))
        coefficient testVector,
      hkernel, dotProduct_zero, mul_zero, add_zero]
  rw [← hshiftInvariant]
  refine (dotProduct_hadamardSquareGram_mulVec_le design huniform hpositive
    (testVector + shift • coefficient)).trans (le_of_eq ?_)
  refine congrArg (fun total => shareValue⁻¹ * total) ?_
  exact Finset.sum_congr rfl fun atomIndex _ => rfl

/-- **THE KERNEL-DEFLATED CAP.**  Optimising the shift in the sharpened cap
subtracts the syzygy's share of the test vector outright:
`x^T W x <= (1/shareValue) (|x|^2 - <x, theta>^2 / |theta|^2)`.

This is the exact bridge the `tau` route needs.  Specialising `x` to the triple
deviation vector `1_T - (3/7) . ones` — which has `|x|^2 = 12/7`,
`<x, theta> = tau_T` and `x^T W x = 2 sigma_T` — turns this into
`sigma_T <= 2 - (7/6) tau_T^2 / |theta|^2`, so `tau_T^2 / |theta|^2 >= 10/7`
fires the sigma gate of section 7.  That specialisation (pure indicator
bookkeeping) is NOT mechanized here, and neither is the counting identity
`sum over the 35 triples of tau_T^2 = 10 |theta|^2`, which is what shows the
route is short: it yields only `max_T tau_T^2 >= (2/7) |theta|^2`, a factor of
five below the gate. -/
theorem dotProduct_hadamardSquareGram_mulVec_le_kernelDeflated (design : WeightedDesign size 3)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare design atomIndex = shareValue)
    (hpositive : 0 < shareValue) {coefficient : Fin size → ℝ}
    (hsyzygy : momentCombination design coefficient = 0)
    (hnormPositive : 0 < ∑ atomIndex, coefficient atomIndex ^ 2)
    (testVector : Fin size → ℝ) :
    testVector ⬝ᵥ (hadamardSquareGram design *ᵥ testVector)
      ≤ shareValue⁻¹ * ((∑ atomIndex, testVector atomIndex ^ 2)
          - (∑ atomIndex, testVector atomIndex * coefficient atomIndex) ^ 2
            / ∑ atomIndex, coefficient atomIndex ^ 2) := by
  have hshifted := dotProduct_hadamardSquareGram_mulVec_le_shifted design huniform hpositive
    hsyzygy testVector
    (-((∑ atomIndex, testVector atomIndex * coefficient atomIndex)
      / ∑ atomIndex, coefficient atomIndex ^ 2))
  refine hshifted.trans (le_of_eq (congrArg (fun total => shareValue⁻¹ * total) ?_))
  have hnormNonzero : (∑ atomIndex, coefficient atomIndex ^ 2) ≠ 0 := hnormPositive.ne'
  calc ∑ atomIndex, (testVector atomIndex
        + -((∑ index, testVector index * coefficient index)
          / ∑ index, coefficient index ^ 2) * coefficient atomIndex) ^ 2
      = ∑ atomIndex, (testVector atomIndex
          - ((∑ index, testVector index * coefficient index)
            / ∑ index, coefficient index ^ 2) * coefficient atomIndex) ^ 2 :=
        Finset.sum_congr rfl fun atomIndex _ => by ring
    _ = (∑ atomIndex, testVector atomIndex ^ 2)
        - 2 * ((∑ index, testVector index * coefficient index)
            / ∑ index, coefficient index ^ 2)
          * (∑ atomIndex, testVector atomIndex * coefficient atomIndex)
        + ((∑ index, testVector index * coefficient index)
            / ∑ index, coefficient index ^ 2) ^ 2
          * ∑ atomIndex, coefficient atomIndex ^ 2 :=
        sum_sq_sub_scaled testVector coefficient _
    _ = (∑ atomIndex, testVector atomIndex ^ 2)
        - (∑ atomIndex, testVector atomIndex * coefficient atomIndex) ^ 2
          / ∑ atomIndex, coefficient atomIndex ^ 2 := by
        field_simp
        ring

/-! ## 5. Gerzon at `(7,3)`: no seven equiangular lines in `R^3` -/

/-- **GERZON AT `(7,3)`.**  No uniform-share `(7,3)` design has all its squared
direction correlations equal.  Equiangularity makes `W = (1 - alpha) . 1 + alpha . J`;
the row law pins `alpha = 2/9`; the syzygy then satisfies
`0 = W theta = (1 - alpha) theta = (7/9) theta`, so `theta = 0` — contradicting
the syzygy's nontriviality.  In classical language: `R^3` carries at most six
equiangular lines, and this is the one-line proof of the `m <= binom(k+1,2)`
half of Gerzon's bound at `k = 3`.  It is the credibility check on this layer:
machinery that cannot produce this corollary is wrong. -/
theorem not_equiangular_uniformShare_sevenThree (design : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare design atomIndex = 3 / 7) {commonSquare : ℝ}
    (hequiangular : ∀ firstIndex secondIndex : Fin 7, firstIndex ≠ secondIndex →
      hadamardSquareGram design firstIndex secondIndex = commonSquare) : False := by
  have hshareNonzero : (0 : ℝ) < 3 / 7 := by norm_num
  have hleverage : ∀ atomIndex : Fin 7, 0 < leverageOf (design.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos design (by rw [huniform atomIndex]; norm_num)
  have hdiagonal : ∀ atomIndex : Fin 7,
      hadamardSquareGram design atomIndex atomIndex = 1 := fun atomIndex =>
    hadamardSquareGram_diagonal design (hleverage atomIndex)
  have hentrySplit : ∀ firstIndex secondIndex : Fin 7,
      hadamardSquareGram design firstIndex secondIndex
        = commonSquare + (if firstIndex = secondIndex then 1 - commonSquare else 0) := by
    intro firstIndex secondIndex
    by_cases hequal : firstIndex = secondIndex
    · rw [if_pos hequal, hequal, hdiagonal secondIndex]
      ring
    · rw [if_neg hequal, hequiangular firstIndex secondIndex hequal, add_zero]
  have hcommonValue : commonSquare = 2 / 9 := by
    have hrow := sum_hadamardSquareGram_row_of_uniformShare design huniform hshareNonzero 0
    rw [Finset.sum_congr rfl fun secondIndex (_ : secondIndex ∈ Finset.univ) =>
      hentrySplit 0 secondIndex, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_eq Finset.univ (0 : Fin 7) fun _ => 1 - commonSquare,
      if_pos (Finset.mem_univ (0 : Fin 7))] at hrow
    norm_num at hrow
    linarith [hrow]
  obtain ⟨coefficient, hnonzero, hsyzygy⟩ := exists_veroneseSyzygy design
  have hzeroTotal : ∑ atomIndex, coefficient atomIndex = 0 :=
    sum_eq_zero_of_momentCombination_eq_zero design hleverage hsyzygy
  have hkernel := hadamardSquareGram_mulVec_eq_zero design hsyzygy
  refine hnonzero (funext fun atomIndex => ?_)
  have hrowValue : ∑ otherIndex, hadamardSquareGram design atomIndex otherIndex
      * coefficient otherIndex = 0 := by
    have hentry := congrFun hkernel atomIndex
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply] at hentry
    exact hentry
  rw [Finset.sum_congr rfl fun otherIndex (_ : otherIndex ∈ Finset.univ) => by
    rw [hentrySplit atomIndex otherIndex]] at hrowValue
  rw [Finset.sum_congr rfl fun otherIndex (_ : otherIndex ∈ Finset.univ) =>
    show (commonSquare + (if atomIndex = otherIndex then 1 - commonSquare else 0))
        * coefficient otherIndex
      = commonSquare * coefficient otherIndex
        + (if atomIndex = otherIndex then (1 - commonSquare) * coefficient otherIndex
            else 0) from by
    by_cases hequal : atomIndex = otherIndex
    · rw [if_pos hequal, if_pos hequal]; ring
    · rw [if_neg hequal, if_neg hequal]; ring,
    Finset.sum_add_distrib, ← Finset.mul_sum, hzeroTotal, mul_zero, zero_add,
    Finset.sum_ite_eq Finset.univ atomIndex
      fun otherIndex => (1 - commonSquare) * coefficient otherIndex,
    if_pos (Finset.mem_univ atomIndex), hcommonValue] at hrowValue
  rw [Pi.zero_apply]
  linarith [hrowValue]

/-! ## 6. The second-moment floor: the weights are forced away from uniform -/

/-- **THE EXACT TEST FORM.**  `Y_ab = 14 N [a = b] + 3 N - 14 theta_a theta_b`,
where `N = |theta|^2`.  Its three coefficients `(14, 3, -14)` are the optimum of
the two-parameter problem `max <W, Y>^2 / |Y|^2` over the span of the identity,
the all-ones matrix and the syzygy projector — the unique combination that turns
the `(7,3)` syzygy into the sharp second-moment floor `49/5`.  For the record,
and NOT mechanized: the same optimisation restricted to the span of the identity
and the syzygy projector alone peaks at `49/6`, and restricted to the identity
and the all-ones matrix alone at `1225/135` (equivalently the edge floor
`28/27`), so both the all-ones and the syzygy component are load-bearing. -/
noncomputable def syzygyTestEntry (coefficient : Fin 7 → ℝ) (normValue : ℝ)
    (firstIndex secondIndex : Fin 7) : ℝ :=
  14 * normValue * (if firstIndex = secondIndex then 1 else 0) + 3 * normValue
    - 14 * (coefficient firstIndex * coefficient secondIndex)

/-- The test form pairs with every row of `W` to the SAME value `21 N`.  Uses the
unit diagonal, the row law and the kernel relation; the normalisation of
`normValue` is irrelevant here. -/
theorem sum_hadamardSquareGram_mul_syzygyTestEntry_row (design : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare design atomIndex = 3 / 7)
    {coefficient : Fin 7 → ℝ} (hsyzygy : momentCombination design coefficient = 0)
    (normValue : ℝ) (firstIndex : Fin 7) :
    ∑ secondIndex, hadamardSquareGram design firstIndex secondIndex
        * syzygyTestEntry coefficient normValue firstIndex secondIndex
      = 21 * normValue := by
  have hsharePositive : (0 : ℝ) < 3 / 7 := by norm_num
  have hleverage : 0 < leverageOf (design.atom firstIndex) :=
    leverageOf_pos_of_atomShare_pos design (by rw [huniform firstIndex]; norm_num)
  have hrowTotal : ∑ secondIndex, hadamardSquareGram design firstIndex secondIndex = 7 / 3 := by
    rw [sum_hadamardSquareGram_row_of_uniformShare design huniform hsharePositive firstIndex]
    norm_num
  have hkernelRow : ∑ secondIndex, hadamardSquareGram design firstIndex secondIndex
      * coefficient secondIndex = 0 := by
    have hentry := congrFun (hadamardSquareGram_mulVec_eq_zero design hsyzygy) firstIndex
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply] at hentry
    exact hentry
  rw [Finset.sum_congr rfl fun secondIndex (_ : secondIndex ∈ Finset.univ) =>
    show hadamardSquareGram design firstIndex secondIndex
        * syzygyTestEntry coefficient normValue firstIndex secondIndex
      = (if firstIndex = secondIndex then
            14 * normValue * hadamardSquareGram design firstIndex secondIndex else 0)
        + 3 * normValue * hadamardSquareGram design firstIndex secondIndex
        - (14 * coefficient firstIndex)
          * (hadamardSquareGram design firstIndex secondIndex * coefficient secondIndex) from by
    rw [syzygyTestEntry]
    by_cases hequal : firstIndex = secondIndex
    · rw [if_pos hequal, if_pos hequal]; ring
    · rw [if_neg hequal, if_neg hequal]; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq Finset.univ firstIndex
      fun secondIndex => 14 * normValue * hadamardSquareGram design firstIndex secondIndex,
    if_pos (Finset.mem_univ firstIndex), ← Finset.mul_sum, ← Finset.mul_sum,
    hadamardSquareGram_diagonal design hleverage, hrowTotal, hkernelRow]
  ring

/-- Each row of the test form has the same square total up to a `theta_a^2`
correction: `sum_b Y_ab^2 = 343 N^2 - 196 N theta_a^2`.  Uses `sum theta = 0`
and `sum theta^2 = N`. -/
theorem sum_syzygyTestEntry_sq_row {coefficient : Fin 7 → ℝ} {normValue : ℝ}
    (hnorm : normValue = ∑ index, coefficient index ^ 2)
    (hzeroTotal : ∑ index, coefficient index = 0) (firstIndex : Fin 7) :
    ∑ secondIndex, syzygyTestEntry coefficient normValue firstIndex secondIndex ^ 2
      = 343 * normValue ^ 2 - 196 * normValue * coefficient firstIndex ^ 2 := by
  have hbulk : ∑ secondIndex,
        (3 * normValue - 14 * (coefficient firstIndex * coefficient secondIndex)) ^ 2
      = 63 * normValue ^ 2 + 196 * coefficient firstIndex ^ 2 * normValue := by
    rw [Finset.sum_congr rfl fun secondIndex (_ : secondIndex ∈ Finset.univ) =>
      show (3 * normValue - 14 * (coefficient firstIndex * coefficient secondIndex)) ^ 2
        = 9 * normValue ^ 2
          - (84 * normValue * coefficient firstIndex) * coefficient secondIndex
          + (196 * coefficient firstIndex ^ 2) * coefficient secondIndex ^ 2 from by ring,
      sum_sub_scaled_add_scaled, hzeroTotal, ← hnorm, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun secondIndex (_ : secondIndex ∈ Finset.univ) =>
    show syzygyTestEntry coefficient normValue firstIndex secondIndex ^ 2
      = (3 * normValue - 14 * (coefficient firstIndex * coefficient secondIndex)) ^ 2
        + (if firstIndex = secondIndex then
            (17 * normValue - 14 * coefficient firstIndex ^ 2) ^ 2
              - (3 * normValue - 14 * coefficient firstIndex ^ 2) ^ 2 else 0) from by
    rw [syzygyTestEntry]
    by_cases hequal : firstIndex = secondIndex
    · rw [if_pos hequal, if_pos hequal, ← hequal]; ring
    · rw [if_neg hequal, if_neg hequal]; ring]
  rw [Finset.sum_add_distrib, hbulk,
    Finset.sum_ite_eq Finset.univ firstIndex
      fun _ => (17 * normValue - 14 * coefficient firstIndex ^ 2) ^ 2
        - (3 * normValue - 14 * coefficient firstIndex ^ 2) ^ 2,
    if_pos (Finset.mem_univ firstIndex)]
  ring

/-- **THE SECOND-MOMENT FLOOR.**  On the `(7,3)` uniform-share stratum
`sum_a sum_b gamma_ab^4 >= 49/5`.  The row law alone (with the all-ones and
identity test directions) gives only `1225/135 = 9.074...`; the syzygy raises the
floor to `49/5 = 9.8`.  Certificate: `<W, Y> = 147 N`, `|Y|^2 = 2205 N^2`, so
`0 <= sum_ab (W_ab - Y_ab/(15 N))^2 = sum_ab W_ab^2 - 49/5`. -/
theorem fourth_moment_ge_of_uniformShare (design : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare design atomIndex = 3 / 7) :
    49 / 5 ≤ ∑ firstIndex, ∑ secondIndex,
      hadamardSquareGram design firstIndex secondIndex ^ 2 := by
  have hleverage : ∀ atomIndex : Fin 7, 0 < leverageOf (design.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos design (by rw [huniform atomIndex]; norm_num)
  obtain ⟨coefficient, hnonzero, hsyzygy⟩ := exists_veroneseSyzygy design
  have hzeroTotal : ∑ index, coefficient index = 0 :=
    sum_eq_zero_of_momentCombination_eq_zero design hleverage hsyzygy
  have hnormPositive : 0 < ∑ index, coefficient index ^ 2 := by
    obtain ⟨witnessIndex, hwitness⟩ := Function.ne_iff.mp hnonzero
    rw [Pi.zero_apply] at hwitness
    refine lt_of_lt_of_le (?_ : (0 : ℝ) < coefficient witnessIndex ^ 2) ?_
    · exact lt_of_le_of_ne (sq_nonneg _) fun heq => hwitness (pow_eq_zero_iff two_ne_zero |>.mp heq.symm)
    · exact Finset.single_le_sum (fun index _ => sq_nonneg (coefficient index))
        (Finset.mem_univ witnessIndex)
  have hinnerTotal : ∑ firstIndex, ∑ secondIndex,
      hadamardSquareGram design firstIndex secondIndex
        * syzygyTestEntry coefficient (∑ index, coefficient index ^ 2) firstIndex secondIndex
      = 147 * ∑ index, coefficient index ^ 2 := by
    rw [Finset.sum_congr rfl fun firstIndex (_ : firstIndex ∈ Finset.univ) =>
      sum_hadamardSquareGram_mul_syzygyTestEntry_row design huniform hsyzygy _ firstIndex,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have htestTotal : ∑ firstIndex, ∑ secondIndex,
      syzygyTestEntry coefficient (∑ index, coefficient index ^ 2) firstIndex secondIndex ^ 2
      = 2205 * (∑ index, coefficient index ^ 2) ^ 2 := by
    rw [Finset.sum_congr rfl fun firstIndex (_ : firstIndex ∈ Finset.univ) =>
      sum_syzygyTestEntry_sq_row rfl hzeroTotal firstIndex,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  have hcertificate : 0 ≤ ∑ firstIndex, ∑ secondIndex,
      (hadamardSquareGram design firstIndex secondIndex
        - (15 * ∑ index, coefficient index ^ 2)⁻¹
          * syzygyTestEntry coefficient (∑ index, coefficient index ^ 2)
              firstIndex secondIndex) ^ 2 :=
    Finset.sum_nonneg fun firstIndex _ => Finset.sum_nonneg fun secondIndex _ => sq_nonneg _
  rw [Finset.sum_congr rfl fun firstIndex (_ : firstIndex ∈ Finset.univ) =>
    sum_sq_sub_scaled _ _ ((15 * ∑ index, coefficient index ^ 2)⁻¹),
    sum_sub_scaled_add_scaled, hinnerTotal, htestTotal] at hcertificate
  have hnonzero15 : (15 * ∑ index, coefficient index ^ 2) ≠ 0 := by positivity
  have hinverse : (15 * ∑ index, coefficient index ^ 2)⁻¹
      * (15 * ∑ index, coefficient index ^ 2) = 1 := inv_mul_cancel₀ hnonzero15
  nlinarith [hcertificate, hinverse, hnormPositive,
    sq_nonneg ((15 * ∑ index, coefficient index ^ 2)⁻¹)]

/-- The fourth-moment total splits at the unit diagonal. -/
theorem fourth_moment_eq_seven_add_offDiagonal (design : WeightedDesign 7 3)
    (hleverage : ∀ atomIndex, 0 < leverageOf (design.atom atomIndex)) :
    ∑ firstIndex, ∑ secondIndex, hadamardSquareGram design firstIndex secondIndex ^ 2
      = 7 + ∑ firstIndex, ∑ secondIndex ∈ Finset.univ.erase firstIndex,
          hadamardSquareGram design firstIndex secondIndex ^ 2 := by
  have hsplit : ∀ firstIndex : Fin 7,
      ∑ secondIndex, hadamardSquareGram design firstIndex secondIndex ^ 2
        = 1 + ∑ secondIndex ∈ Finset.univ.erase firstIndex,
            hadamardSquareGram design firstIndex secondIndex ^ 2 := by
    intro firstIndex
    rw [← Finset.add_sum_erase Finset.univ
      (fun secondIndex => hadamardSquareGram design firstIndex secondIndex ^ 2)
      (Finset.mem_univ firstIndex),
      hadamardSquareGram_diagonal design (hleverage firstIndex), one_pow]
  rw [Finset.sum_congr rfl fun firstIndex (_ : firstIndex ∈ Finset.univ) => hsplit firstIndex,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **THE EDGE FLOOR.**  The off-diagonal total of squared edge weights is at
least `14/5`, i.e. the unordered-edge total `sum over the 21 edges of w_e^2` is
at least `7/5`.  The naive Cauchy-Schwarz floor from the edge total `14/3` alone
is `28/27 = 1.037...`.  CONSEQUENCE: uniform edge weights `w == 2/9` are
IMPOSSIBLE on this stratum, since they give an off-diagonal total
`42 . (2/9)^2 = 56/27 = 2.074... < 14/5`.  So the weights are always forced away
from uniform by a definite amount, and the dichotomy branch "the `w_e` are
near-uniform" describes an empty configuration. -/
theorem edge_second_moment_ge_of_uniformShare (design : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare design atomIndex = 3 / 7) :
    14 / 5 ≤ ∑ firstIndex, ∑ secondIndex ∈ Finset.univ.erase firstIndex,
      hadamardSquareGram design firstIndex secondIndex ^ 2 := by
  have hleverage : ∀ atomIndex : Fin 7, 0 < leverageOf (design.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos design (by rw [huniform atomIndex]; norm_num)
  have htotal := fourth_moment_ge_of_uniformShare design huniform
  rw [fourth_moment_eq_seven_add_offDiagonal design hleverage] at htotal
  linarith [htotal]

/-! ## 7. The sigma gate: `sigma_T <= 1/3` alone forces domination -/

/-- Three-variable AM-GM: `27 xyz <= (x + y + z)^3` for nonnegative `x, y, z`.
Exact positive certificate:
`(x+y+z)^3 - 27xyz = (1/2)(x+y+z)[(x-y)^2+(y-z)^2+(z-x)^2] + 3[x(y-z)^2+y(z-x)^2+z(x-y)^2]`. -/
theorem twentySeven_mul_prod_le_cube_sum {firstValue secondValue thirdValue : ℝ}
    (hfirst : 0 ≤ firstValue) (hsecond : 0 ≤ secondValue) (hthird : 0 ≤ thirdValue) :
    27 * (firstValue * secondValue * thirdValue) ≤ (firstValue + secondValue + thirdValue) ^ 3 := by
  nlinarith [mul_nonneg hfirst (sq_nonneg (secondValue - thirdValue)),
    mul_nonneg hsecond (sq_nonneg (thirdValue - firstValue)),
    mul_nonneg hthird (sq_nonneg (firstValue - secondValue)),
    mul_nonneg (add_nonneg (add_nonneg hfirst hsecond) hthird) (sq_nonneg (firstValue - secondValue)),
    mul_nonneg (add_nonneg (add_nonneg hfirst hsecond) hthird) (sq_nonneg (secondValue - thirdValue)),
    mul_nonneg (add_nonneg (add_nonneg hfirst hsecond) hthird) (sq_nonneg (thirdValue - firstValue))]

/-- **THE SIGMA GATE, scalar form.**  `sigma <= 1/3` implies `sigma - 3 P <= 4/9`
for any three reals with `sigma` their sum of squares and `P` their product.
SHARP: equality at `edge = -1/3` throughout, i.e. `sigma = 1/3, P = -1/27` — the
tetrahedral tie.  Certificate: AM-GM gives `(3P)^2 <= sigma^3 / 3`, and
`3(4/9 - sigma)^2 - sigma^3 = -(1/27)(3 sigma - 1)(3 sigma - 4)^2 >= 0` on
`sigma <= 1/3`. -/
theorem sigma_sub_three_mul_product_le_four_ninths_of_sigma_le_third
    {firstEdge secondEdge thirdEdge : ℝ}
    (hsigma : firstEdge ^ 2 + secondEdge ^ 2 + thirdEdge ^ 2 ≤ 1 / 3) :
    (firstEdge ^ 2 + secondEdge ^ 2 + thirdEdge ^ 2)
        - 3 * (firstEdge * secondEdge * thirdEdge) ≤ 4 / 9 := by
  have hamgm : 27 * (firstEdge ^ 2 * secondEdge ^ 2 * thirdEdge ^ 2)
      ≤ (firstEdge ^ 2 + secondEdge ^ 2 + thirdEdge ^ 2) ^ 3 :=
    twentySeven_mul_prod_le_cube_sum (sq_nonneg firstEdge) (sq_nonneg secondEdge)
      (sq_nonneg thirdEdge)
  have hsigmaNonneg : 0 ≤ firstEdge ^ 2 + secondEdge ^ 2 + thirdEdge ^ 2 := by positivity
  have hgap : 0 ≤ 4 / 9 - (firstEdge ^ 2 + secondEdge ^ 2 + thirdEdge ^ 2) := by linarith
  have hcubeBound : (firstEdge ^ 2 + secondEdge ^ 2 + thirdEdge ^ 2) ^ 3
      ≤ 3 * (4 / 9 - (firstEdge ^ 2 + secondEdge ^ 2 + thirdEdge ^ 2)) ^ 2 := by
    nlinarith [sq_nonneg (3 * (firstEdge ^ 2 + secondEdge ^ 2 + thirdEdge ^ 2) - 4), hsigma,
      hsigmaNonneg]
  have hproductSq : (3 * (firstEdge * secondEdge * thirdEdge)) ^ 2
      ≤ (4 / 9 - (firstEdge ^ 2 + secondEdge ^ 2 + thirdEdge ^ 2)) ^ 2 := by
    nlinarith [hamgm, hcubeBound]
  nlinarith [hproductSq, hgap]

/-- **THE SIGMA GATE, geometric form.**  On the `(7,3)` uniform-share stratum
with uniform leverage `3`, a triple of distinct atoms whose squared-correlation
total is at most `1/3` DOMINATES.  One scalar hypothesis, no product term, no
`theta`.  It is sharp: the landed tetrapod triple sits exactly at
`sigma = 1/3, P = -1/27` and dominates with margin zero
(`Gtz.tetrapodTriple_tie_sevenThreeBasisTetrapodDesign`).

This is the gate the syzygy route would fire.  What is NOT proved here is that
some triple achieves `sigma_T <= 1/3`: see the header's statement of the exact
remaining gap. -/
theorem dominates_triple_of_directionTripleSigma_le_third (design : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare design atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (design.atom atomIndex) = 3)
    {firstIndex secondIndex thirdIndex : Fin 7} (hfirstSecond : firstIndex ≠ secondIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (hsecondThird : secondIndex ≠ thirdIndex)
    (hsigma : directionTripleSigma design firstIndex secondIndex thirdIndex ≤ 1 / 3) :
    Dominates design {firstIndex, secondIndex, thirdIndex} := by
  refine (dominates_triple_iff_sigma_sub_three_mul_product_sevenThree design huniform hleverage
    hfirstSecond hfirstThird hsecondThird).mpr ?_
  rw [directionTripleSigma] at hsigma
  rw [directionTripleSigma, directionTripleProduct]
  exact sigma_sub_three_mul_product_le_four_ninths_of_sigma_le_third hsigma

/-! ## 8. Calibration on the landed `(7,3)` witness

`Gtz.sevenThreeBasisTetrapodDesign` is the shipped basis-plus-tetrapod design:
three axis atoms `sqrt 3 . e_i` and the four even-sign tetrapod vertices, all at
weight `1/7`, every share `3/7`.  It inhabits the uniform-share stratum
(`Gtz.atomShare_sevenThreeBasisTetrapodDesign`), so every theorem above is
non-vacuous, and its fourth-moment total shows the floor `49/5` is very nearly
tight. -/

/-- The witness's raw pairings, squared: `9` on the diagonal, `0` between two
axis atoms, `3` between an axis atom and a tetrapod atom, `1` between two
distinct tetrapod atoms.  Atom indices `0,1,2` are the axes. -/
noncomputable def tetrapodPairingSquare (firstIndex secondIndex : Fin 7) : ℝ :=
  if firstIndex = secondIndex then 9
  else if firstIndex.val ≤ 2 then (if secondIndex.val ≤ 2 then 0 else 3)
  else (if secondIndex.val ≤ 2 then 3 else 1)

/-- All forty-nine squared pairings of the witness, in one enumeration. -/
theorem sq_atomPairing_sevenThreeBasisTetrapodDesign (firstIndex secondIndex : Fin 7) :
    (sevenThreeBasisTetrapodAtom firstIndex ⬝ᵥ sevenThreeBasisTetrapodAtom secondIndex) ^ 2
      = tetrapodPairingSquare firstIndex secondIndex := by
  have hsqrtSquare : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  fin_cases firstIndex <;> fin_cases secondIndex <;>
    norm_num [tetrapodPairingSquare, dotProduct, Fin.sum_univ_three, hsqrtSquare,
      sevenThreeBasisTetrapodAtom, tetraAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
      Matrix.cons_val_four]

/-- The witness's Hadamard square in closed form: `1` on the diagonal, `0` on an
axis-axis edge, `1/3` on a mixed edge, `1/9` on a tetrapod-tetrapod edge. -/
theorem hadamardSquareGram_sevenThreeBasisTetrapodDesign (firstIndex secondIndex : Fin 7) :
    hadamardSquareGram sevenThreeBasisTetrapodDesign firstIndex secondIndex
      = tetrapodPairingSquare firstIndex secondIndex / 9 := by
  have hpairing := sq_atomPairing_sevenThreeBasisTetrapodDesign firstIndex secondIndex
  rw [hadamardSquareGram_apply, directionGram_sevenThreeBasisTetrapodDesign]
  linear_combination hpairing / 9

/-- **THE WITNESS CLEARS THE FLOOR, ALMOST EXACTLY.**  Its fourth-moment total is
`265/27 = 9.8148...` against the floor `49/5 = 9.8`. -/
theorem fourth_moment_sevenThreeBasisTetrapodDesign :
    ∑ firstIndex, ∑ secondIndex,
      hadamardSquareGram sevenThreeBasisTetrapodDesign firstIndex secondIndex ^ 2
      = 265 / 27 := by
  rw [Finset.sum_congr rfl fun firstIndex (_ : firstIndex ∈ Finset.univ) =>
    Finset.sum_congr rfl fun secondIndex (_ : secondIndex ∈ Finset.univ) => by
      rw [hadamardSquareGram_sevenThreeBasisTetrapodDesign firstIndex secondIndex]]
  simp only [Fin.sum_univ_seven, tetrapodPairingSquare, Fin.reduceEq, if_true, if_false]
  norm_num

/-- **THE FLOOR IS NEARLY TIGHT**: the witness's slack above `49/5` is exactly
`2/135 = 0.0148...`.  Any improvement of the floor beyond `49/5` must therefore
stay below `265/27`, and an improvement past `265/27` would REFUTE the witness —
so `49/5` is within `2/135` of the truth on this stratum. -/
theorem fourth_moment_sevenThreeBasisTetrapodDesign_sub_floor :
    (∑ firstIndex, ∑ secondIndex,
      hadamardSquareGram sevenThreeBasisTetrapodDesign firstIndex secondIndex ^ 2) - 49 / 5
      = 2 / 135 := by
  rw [fourth_moment_sevenThreeBasisTetrapodDesign]
  norm_num

/-- The witness's off-diagonal total is `76/27`, i.e. the unordered-edge total is
`38/27 = 1.4074...` against the edge floor `7/5 = 1.4`. -/
theorem edge_second_moment_sevenThreeBasisTetrapodDesign :
    ∑ firstIndex, ∑ secondIndex ∈ Finset.univ.erase firstIndex,
      hadamardSquareGram sevenThreeBasisTetrapodDesign firstIndex secondIndex ^ 2
      = 76 / 27 := by
  have hleverage : ∀ atomIndex : Fin 7,
      0 < leverageOf (sevenThreeBasisTetrapodDesign.atom atomIndex) := fun atomIndex => by
    rw [leverageOf_sevenThreeBasisTetrapodDesign]
    norm_num
  have hsplit := fourth_moment_eq_seven_add_offDiagonal sevenThreeBasisTetrapodDesign hleverage
  rw [fourth_moment_sevenThreeBasisTetrapodDesign] at hsplit
  linarith [hsplit]

/-- **NON-VACUITY, in one line.**  The floor is a statement about an inhabited
stratum: the witness is uniform-share at `3/7` and satisfies it. -/
theorem fourth_moment_ge_sevenThreeBasisTetrapodDesign :
    49 / 5 ≤ ∑ firstIndex, ∑ secondIndex,
      hadamardSquareGram sevenThreeBasisTetrapodDesign firstIndex secondIndex ^ 2 :=
  fourth_moment_ge_of_uniformShare sevenThreeBasisTetrapodDesign
    atomShare_sevenThreeBasisTetrapodDesign

/-- **UNIFORM EDGE WEIGHTS ARE IMPOSSIBLE**, in the sharpest form available here:
the witness is uniform-share yet NOT equiangular, and more strongly no
uniform-share `(7,3)` design is (`not_equiangular_uniformShare_sevenThree`).  The
would-be common value `2/9` gives an off-diagonal total `42 . (2/9)^2 = 56/27`,
strictly below the floor `14/5`. -/
theorem uniform_edge_total_lt_edge_floor : (42 : ℝ) * (2 / 9) ^ 2 < 14 / 5 := by
  norm_num

/-- **THE SYZYGY STRICTLY IMPROVES THE ROW-LAW FLOOR.**  Cauchy-Schwarz applied
to the twenty-one edges with total `14/3` (the row law, halved) gives only
`(14/3)^2 / 21 = 28/27`; the syzygy floor is `7/5`.  (That `28/27` IS the
Cauchy-Schwarz optimum is elementary and not mechanized here; the arithmetic
comparison is.) -/
theorem naiveEdgeFloor_lt_syzygyEdgeFloor : (14 / 3 : ℝ) ^ 2 / 21 < 7 / 5 := by
  norm_num

/-! ## 9. Barrier B2, recorded as exact arithmetic only

The counting-family ceiling of the campaign's pen brief.  **The no-go CONTENT —
that no floor produced by the elementary / Cauchy-Binet counting family can
exceed this value — is NOT proved here.**  Only the closed-form constant and its
three exact evaluations are, so a later lane can cite the numbers instead of
re-deriving them. -/

/-- `Ceil(size, rank) = (1/size) . (size / (rank . ((size - rank)(rank - 1) + size)) - 1)`,
the counting-family ceiling.  It is `Gtz.valueFloorOfCount` evaluated at the
generally NON-INTEGER count `rank . ((size-rank)(rank-1) + size) / size`, which is
why it is defined here as its own real-valued function rather than reusing the
natural-number-indexed shipped floor. -/
noncomputable def countingFamilyCeiling (size rank : ℕ) : ℝ :=
  ((size : ℝ))⁻¹
    * ((size : ℝ)
        / ((rank : ℝ) * (((size : ℝ) - (rank : ℝ)) * ((rank : ℝ) - 1) + (size : ℝ))) - 1)

/-- At `(4,2)` the ceiling is `-1/6`. -/
theorem countingFamilyCeiling_fourTwo : countingFamilyCeiling 4 2 = -(1 / 6) := by
  rw [countingFamilyCeiling]
  norm_num

/-- **THE CEILING IS SATURATED AT `(4,2)`**: it agrees exactly with the shipped
`Gtz.combinedValueFloor` there, which is what makes the closed form credible —
the family's best floor already sits on the ceiling at that one cell. -/
theorem countingFamilyCeiling_fourTwo_eq_combinedValueFloor :
    countingFamilyCeiling 4 2 = combinedValueFloor 4 2 := by
  rw [countingFamilyCeiling_fourTwo, combinedValueFloor, combinedCount, elementaryCount,
    valueFloorOfCount]
  norm_num

theorem countingFamilyCeiling_sixThree : countingFamilyCeiling 6 3 = -(5 / 36) := by
  rw [countingFamilyCeiling]
  norm_num

theorem countingFamilyCeiling_sevenThree : countingFamilyCeiling 7 3 = -(38 / 315) := by
  rw [countingFamilyCeiling]
  norm_num

/-- Every value of the ceiling recorded here is strictly negative, so no member of
the counting family can reach `0` — the target the campaign needs. -/
theorem countingFamilyCeiling_sevenThree_neg : countingFamilyCeiling 7 3 < 0 := by
  rw [countingFamilyCeiling_sevenThree]
  norm_num

/-- **WHY THE FAMILY IS STRUCTURALLY CAPPED, NOT MERELY SHORT.**  The family is
field-blind, so it also caps every Hermitian variant.  At `(4,2)` the complex
`C^2` SIC sits at the exact algebraic value `1/4 - sqrt 3 / 6 = -0.0387...`,
which is itself NEGATIVE — a genuine complex counterexample — and the family's
own SATURATED floor `-1/6` lies strictly below it.  So at the one cell where the
family is sharp it already fails to separate a known counterexample from the
target, and no amount of tightening inside the family can.  (The identification
of `1/4 - sqrt 3 / 6` with the `C^2` SIC value is cited from the campaign ledger,
not proved here; the two inequalities are.) -/
theorem countingFamilyCeiling_fourTwo_lt_complexSicValue :
    countingFamilyCeiling 4 2 < 1 / 4 - Real.sqrt 3 / 6 := by
  have hsquare : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  rw [countingFamilyCeiling_fourTwo]
  nlinarith [hsquare, hnonneg]

theorem complexSicValue_fourTwo_neg : 1 / 4 - Real.sqrt 3 / 6 < 0 := by
  have hsquare : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  nlinarith [hsquare, hnonneg]

end Gtz
