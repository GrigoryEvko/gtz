/-
# The mirror law — complementary blocks of a tight frame have reflected spectra

Let `U` be a `k x m` matrix whose columns are the atoms of a design and suppose the
columns split into two blocks `L` (the selected set `C`) and `R` (its complement),
so that the tight-frame identity reads

    L Lᵀ + R Rᵀ  =  level . I_k                                              (TIGHT)

in COORDINATE space.  The two Gram matrices `Lᵀ L` and `Rᵀ R` live in SLOT space and
are what domination is actually about (`Gtz.dominates_triple_iff_posSemidef_tripleGapMatrix`).
The mirror law says their spectra are reflections of one another about `level / 2`.

**The cheap route, and why it is confined to `|C| = k`.**  For a SQUARE block `B` the
Gram `Bᵀ B` and the frame operator `B Bᵀ` have the same characteristic polynomial
(`Matrix.charpoly_mul_comm`), so

    spec(Gram C)  =  spec(S_C),   spec(S_Cᶜ) = level − spec(S_C),

and the second equality is (TIGHT) read as `S_Cᶜ = level . I − S_C`.  Composing gives
`spec(Gram Cᶜ) = level − spec(Gram C)`.  Nothing here is a Schur complement; the whole
proof is `AB` versus `BA` plus one sign.  It needs `|C| = |Cᶜ| = k` only so that BOTH
blocks are square — at `|Cᶜ| > k` the transfer costs a factor `X^(|Cᶜ| − k)`, which is
exactly the `(7,3)` statement recorded below
(`pow_mul_det_shift_gram_mirror_ofSquareLeft`, `det_shift_gram_mirror_sevenThree`):
the complement picks up `|Cᶜ| − k` extra zero eigenvalues.

The headline is `det_shift_gram_mirror`; its Loewner reading is
`posSemidef_gram_sub_smul_one_iff_ofTightSplit`, its polynomial reading
`charpoly_gram_mirror`, and the cheapest reading of all —
`dominates_iff_posSemidef_smul_one_sub_subsetSum_compl`, domination of `C` as an
eigenvalue CEILING on `Cᶜ` — needs no `AB`/`BA` transfer whatsoever.

**At the equal-share `(6,3)` stratum** every share is `1/2`, so the unit directions
satisfy `Σ_c u_c u_cᵀ = 2 . I` and (TIGHT) holds at `level = 2` for every 3–3 split.
Note the hypothesis carried below is `atomShare = 1/2` ALONE: it does not force the
uniform weight `1/6` and leverage `3` the pen assumes (a share is a product, and only
the product is pinned), so every `(6,3)` statement here is strictly more general than
the pen's.  Writing `Γ` for the direction Gram (unit diagonal) and `M = Γ − 1`, the
mirror becomes `spec(M[Cᶜ]) = −spec(M[C])`, whose two scalar readings are the pen's

    sigma_Cᶜ = sigma_C,        P_Cᶜ = −P_C,

`sigma` the sum of the three squared correlations and `P` the oriented triangle
product.  Both are landed below, and the division of labour is worth recording:
the determinant mirror is spent ENTIRELY on `P`.  `sigma` never needs it — it is
landed twice from the row law alone, once in six-index form for the `(6,3)` split
(`directionTripleSigma_compl_eq`) and once as a `Finset` statement at arbitrary size
and arbitrary subset (`directionSquareMass_compl_eq`), the latter surviving at `(7,3)`
with the exact correction `(|C| − |Cᶜ|)(rowMass − 1) / 2`, i.e. `sigma_Cᶜ = sigma_C +
2/3` there (`directionSquareMass_compl_sub_sevenThree`).

**The general symmetric involution: the naive statement is FALSE.**  It is tempting
to drop the frame hypothesis and assert that for any symmetric involution `J` and any
subset `K`, `spec(J[Kᶜ]) = −spec(J[K])`.  That is refuted here at `J = 1` on `Fin 2`
with `|K| = |Kᶜ| = 1` (`not_forall_det_shift_mirror_ofSymmetricInvolution`), where the
sizes match exactly so no "extra ±1 eigenvalues" bookkeeping can rescue it.  The
diagnosis — the `+1`-eigenspace of `J` must have dimension `|K|`, equivalently
`trace J = 0` — is NOT mechanized here; only its necessity is, by that counterexample.
What (TIGHT) supplies in its place IS mechanized: `trace_gram_add_trace_gram` says the
two Gram traces add to `rank · level`, which at `level = 2` is exactly `trace M = 0`.

Two positive general substitutes are landed.  The frame form above needs no genericity
at all.  The intertwining form `det_shift_eq_of_intertwine` needs no involution and no
symmetry: `A B = B C` with `B` invertible makes `A` and `C` similar, and since `J² = 1`
forces `A B = −B D` on the blocks, an invertible off-diagonal block turns the mirror
into a one-line conjugation (`det_shift_mirror_of_symmetricInvolutionBlocks`).
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.FrameConservation
import Gtz.Quantitative.RealnessEngine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The shifted determinant

Everything in this section is stated with the shift written `shift • 1` rather than
`Matrix.scalar _ shift`, matching `Gtz.Dominates` and `Gtz.HasLeastEigenvalueAtLeast`.
-/

/-- `Matrix.scalar` is the scalar multiple of the identity, over any commutative ring
and any index type.  (`Gtz.scalar_eq_smul_one` is the `Fin k`-at-`ℝ` instance of this;
the general form is what the mirror law below needs.) -/
theorem matrixScalar_eq_smul_one {ringCarrier : Type*} [CommRing ringCarrier]
    {indexType : Type*} [DecidableEq indexType] [Fintype indexType] (level : ringCarrier) :
    (Matrix.scalar indexType) level = level • (1 : Matrix indexType indexType ringCarrier) := by
  rw [Matrix.smul_one_eq_diagonal]
  rfl

/-- The shifted determinant IS the characteristic polynomial evaluated at the shift.
This is the only bridge to `Polynomial` used below. -/
theorem det_smul_one_sub_eq_evalCharpoly {ringCarrier : Type*} [CommRing ringCarrier]
    {indexType : Type*} [DecidableEq indexType] [Fintype indexType]
    (block : Matrix indexType indexType ringCarrier) (shift : ringCarrier) :
    (shift • (1 : Matrix indexType indexType ringCarrier) - block).det
      = Polynomial.eval shift block.charpoly := by
  rw [Matrix.eval_charpoly, matrixScalar_eq_smul_one]

/-- **`AB` versus `BA` at every shift, square case.**  The Gram `Bᵀ B` and the frame
operator `B Bᵀ` of a SQUARE block have the same shifted determinant — the cheap
ingredient of the mirror, and the reason the mirror is a `|C| = k` statement. -/
theorem det_shift_gram_eq_det_shift_frame {ringCarrier : Type*} [CommRing ringCarrier]
    {size : ℕ} (block : Matrix (Fin size) (Fin size) ringCarrier) (shift : ringCarrier) :
    (shift • (1 : Matrix (Fin size) (Fin size) ringCarrier) - blockᵀ * block).det
      = (shift • (1 : Matrix (Fin size) (Fin size) ringCarrier) - block * blockᵀ).det := by
  rw [det_smul_one_sub_eq_evalCharpoly, det_smul_one_sub_eq_evalCharpoly,
    Matrix.charpoly_mul_comm]

/-! ## 2. The frame reflection and the mirror law

`det_shift_frame_mirror` is the coordinate-space half — pure algebra on (TIGHT), valid
for blocks of any two widths.  `det_shift_gram_mirror` is S2 proper: composing it with
the square `AB`/`BA` transfer on both sides moves the statement into slot space.
-/

/-- **The frame reflection.**  Under (TIGHT) the two frame operators are affine
reflections of one another, so their shifted determinants are reflections about
`level / 2` up to the parity sign.  No squareness, no rank hypothesis: the two blocks
may have any widths. -/
theorem det_shift_frame_mirror {ringCarrier : Type*} [CommRing ringCarrier]
    {rank leftWidth rightWidth : ℕ} (leftBlock : Matrix (Fin rank) (Fin leftWidth) ringCarrier)
    (rightBlock : Matrix (Fin rank) (Fin rightWidth) ringCarrier) (level : ringCarrier)
    (htight : leftBlock * leftBlockᵀ + rightBlock * rightBlockᵀ
      = level • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)) (shift : ringCarrier) :
    (shift • (1 : Matrix (Fin rank) (Fin rank) ringCarrier) - rightBlock * rightBlockᵀ).det
      = (-1) ^ rank
        * ((level - shift) • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
            - leftBlock * leftBlockᵀ).det := by
  have hrightFrame : rightBlock * rightBlockᵀ
      = level • (1 : Matrix (Fin rank) (Fin rank) ringCarrier) - leftBlock * leftBlockᵀ := by
    rw [← htight]; abel
  have hreflect : shift • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
        - (level • (1 : Matrix (Fin rank) (Fin rank) ringCarrier) - leftBlock * leftBlockᵀ)
      = -((level - shift) • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
          - leftBlock * leftBlockᵀ) := by
    rw [sub_smul]; abel
  rw [hrightFrame, hreflect, Matrix.det_neg, Fintype.card_fin]

/-- **S2, THE MIRROR LAW.**  Two SQUARE blocks whose frame operators sum to
`level . I` have Gram matrices with reflected spectra:

    det(z . I − Gram Cᶜ)  =  (−1)^k · det((level − z) . I − Gram C).

Proof: the square `AB`/`BA` transfer on the right block, the frame reflection, and
the square `AB`/`BA` transfer back on the left block.  No Schur complement, no
eigenvalues, no spectral theorem, any commutative ring.

The squareness of BOTH blocks is essential and is exactly the hypothesis `|C| = |Cᶜ|
= k`, i.e. `m = 2k`.  The rectangular statement, which costs a power of the shift, is
`det_shift_gram_mirror_ofSquareLeft`. -/
theorem det_shift_gram_mirror {ringCarrier : Type*} [CommRing ringCarrier] {rank : ℕ}
    (leftBlock rightBlock : Matrix (Fin rank) (Fin rank) ringCarrier) (level : ringCarrier)
    (htight : leftBlock * leftBlockᵀ + rightBlock * rightBlockᵀ
      = level • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)) (shift : ringCarrier) :
    (shift • (1 : Matrix (Fin rank) (Fin rank) ringCarrier) - rightBlockᵀ * rightBlock).det
      = (-1) ^ rank
        * ((level - shift) • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
            - leftBlockᵀ * leftBlock).det := by
  rw [det_shift_gram_eq_det_shift_frame rightBlock shift,
    det_shift_frame_mirror leftBlock rightBlock level htight shift,
    det_shift_gram_eq_det_shift_frame leftBlock (level - shift)]

/-- **The mirror law on the GAP matrices** `Gram − 1`, which is the object the
domination criterion is stated on.  The reflection centre moves from `level / 2` to
`level / 2 − 1`. -/
theorem det_shift_gap_mirror {ringCarrier : Type*} [CommRing ringCarrier] {rank : ℕ}
    (leftBlock rightBlock : Matrix (Fin rank) (Fin rank) ringCarrier) (level : ringCarrier)
    (htight : leftBlock * leftBlockᵀ + rightBlock * rightBlockᵀ
      = level • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)) (shift : ringCarrier) :
    (shift • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
        - (rightBlockᵀ * rightBlock - 1)).det
      = (-1) ^ rank
        * ((level - 2 - shift) • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
            - (leftBlockᵀ * leftBlock - 1)).det := by
  have hshiftLeft : shift • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
        - (rightBlockᵀ * rightBlock - 1)
      = (shift + 1) • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
          - rightBlockᵀ * rightBlock := by
    rw [add_smul, one_smul]; abel
  have hshiftRight : (level - 2 - shift) • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
        - (leftBlockᵀ * leftBlock - 1)
      = (level - (shift + 1)) • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
          - leftBlockᵀ * leftBlock := by
    rw [show level - 2 - shift = (level - (shift + 1)) - 1 by ring, sub_smul, one_smul]
    abel
  rw [hshiftLeft, hshiftRight, det_shift_gram_mirror leftBlock rightBlock level htight]

/-- **The spectrum negates**, the `level = 2` reading of the gap mirror: at the
equal-share stratum the two hollow blocks `M[C] = Γ[C] − 1` and `M[Cᶜ]` satisfy
`spec(M[Cᶜ]) = −spec(M[C])` verbatim. -/
theorem det_shift_gap_mirror_ofLevelTwo {ringCarrier : Type*} [CommRing ringCarrier] {rank : ℕ}
    (leftBlock rightBlock : Matrix (Fin rank) (Fin rank) ringCarrier)
    (htight : leftBlock * leftBlockᵀ + rightBlock * rightBlockᵀ
      = (2 : ringCarrier) • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)) (shift : ringCarrier) :
    (shift • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
        - (rightBlockᵀ * rightBlock - 1)).det
      = (-1) ^ rank
        * ((-shift) • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
            - (leftBlockᵀ * leftBlock - 1)).det := by
  have hmirror := det_shift_gap_mirror leftBlock rightBlock 2 htight shift
  rwa [show (2 : ringCarrier) - 2 - shift = -shift by ring] at hmirror

/-- The `shift = 0` reading: the complement's Gram determinant is the left Gram's
characteristic polynomial evaluated at the level. -/
theorem det_gram_eq_det_level_smul_one_sub_gram {ringCarrier : Type*} [CommRing ringCarrier]
    {rank : ℕ} (leftBlock rightBlock : Matrix (Fin rank) (Fin rank) ringCarrier)
    (level : ringCarrier)
    (htight : leftBlock * leftBlockᵀ + rightBlock * rightBlockᵀ
      = level • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)) :
    (rightBlockᵀ * rightBlock).det
      = (level • (1 : Matrix (Fin rank) (Fin rank) ringCarrier) - leftBlockᵀ * leftBlock).det := by
  have hmirror := det_shift_gram_mirror leftBlock rightBlock level htight 0
  rw [zero_smul, zero_sub, Matrix.det_neg, Fintype.card_fin, sub_zero] at hmirror
  have hsign : ((-1 : ringCarrier)) ^ rank * (-1 : ringCarrier) ^ rank = 1 := by
    rw [← mul_pow]; norm_num
  calc (rightBlockᵀ * rightBlock).det
      = 1 * (rightBlockᵀ * rightBlock).det := (one_mul _).symm
    _ = ((-1 : ringCarrier)) ^ rank * ((-1 : ringCarrier) ^ rank
          * (rightBlockᵀ * rightBlock).det) := by rw [← mul_assoc, hsign]
    _ = ((-1 : ringCarrier)) ^ rank * ((-1) ^ rank
          * (level • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
              - leftBlockᵀ * leftBlock).det) := by rw [hmirror]
    _ = (level • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
          - leftBlockᵀ * leftBlock).det := by rw [← mul_assoc, hsign, one_mul]

/-- **The trace mirror.**  Unlike the determinant mirror this needs NO squareness at
all: `trace(Aᵀ A) = trace(A Aᵀ)` holds rectangularly, so the two Gram traces always
add to `rank · level`.  At the equal-share `(6,3)` stratum both traces are `3`, which
is the trace-zero condition the general involution statement is missing. -/
theorem trace_gram_add_trace_gram {ringCarrier : Type*} [CommRing ringCarrier]
    {rank leftWidth rightWidth : ℕ} (leftBlock : Matrix (Fin rank) (Fin leftWidth) ringCarrier)
    (rightBlock : Matrix (Fin rank) (Fin rightWidth) ringCarrier) (level : ringCarrier)
    (htight : leftBlock * leftBlockᵀ + rightBlock * rightBlockᵀ
      = level • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)) :
    (leftBlockᵀ * leftBlock).trace + (rightBlockᵀ * rightBlock).trace = rank * level := by
  rw [Matrix.trace_mul_comm leftBlockᵀ leftBlock, Matrix.trace_mul_comm rightBlockᵀ rightBlock,
    ← Matrix.trace_add, htight, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul]
  ring

/-- **The mirror as a polynomial identity.**  Over `ℝ` the shift may be abstracted and
the mirror becomes a single equation in `ℝ[X]`: the complement's characteristic
polynomial is the selected block's reflected in `X = level / 2`.  Convenient when the
consumer wants to compare coefficients (trace, the minor sum, the determinant) rather
than evaluate. -/
theorem charpoly_gram_mirror {rank : ℕ} (leftBlock rightBlock : Matrix (Fin rank) (Fin rank) ℝ)
    (level : ℝ)
    (htight : leftBlock * leftBlockᵀ + rightBlock * rightBlockᵀ
      = level • (1 : Matrix (Fin rank) (Fin rank) ℝ)) :
    (rightBlockᵀ * rightBlock).charpoly
      = Polynomial.C ((-1) ^ rank)
        * ((leftBlockᵀ * leftBlock).charpoly.comp (Polynomial.C level - Polynomial.X)) := by
  refine Polynomial.funext fun probe => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X]
  rw [← det_smul_one_sub_eq_evalCharpoly, ← det_smul_one_sub_eq_evalCharpoly]
  exact det_shift_gram_mirror leftBlock rightBlock level htight probe

/-- **The mirror in Loewner form** — the reading domination actually uses.  A least
eigenvalue floor on the complement's Gram is a largest eigenvalue ceiling on the
selected block's frame operator, at the reflected level.  Only the RIGHT block has to
be square (the `AB`/`BA` Loewner flip `Gtz.posSemidef_transpose_mul_sub_smul_one_comm`
is a square statement); `leftBlock` may have any width, so this covers `(7,3)` read
from the four-set side as well. -/
theorem posSemidef_gram_sub_smul_one_iff_ofTightSplit {rank leftWidth : ℕ}
    (leftBlock : Matrix (Fin rank) (Fin leftWidth) ℝ)
    (rightBlock : Matrix (Fin rank) (Fin rank) ℝ) (level : ℝ)
    (htight : leftBlock * leftBlockᵀ + rightBlock * rightBlockᵀ
      = level • (1 : Matrix (Fin rank) (Fin rank) ℝ)) {threshold : ℝ} (hthreshold : 0 < threshold) :
    (rightBlockᵀ * rightBlock - threshold • 1).PosSemidef
      ↔ ((level - threshold) • (1 : Matrix (Fin rank) (Fin rank) ℝ)
          - leftBlock * leftBlockᵀ).PosSemidef := by
  rw [posSemidef_transpose_mul_sub_smul_one_comm rightBlock hthreshold]
  have hrightFrame : rightBlock * rightBlockᵀ
      = level • (1 : Matrix (Fin rank) (Fin rank) ℝ) - leftBlock * leftBlockᵀ := by
    rw [← htight]; abel
  rw [hrightFrame, sub_smul]
  refine Iff.of_eq (congrArg Matrix.PosSemidef ?_)
  abel

/-! ## 3. The rectangular mirror — what `(7,3)` needs

When the complement is wider than the rank the `AB`/`BA` transfer is no longer free:
`Matrix.charpoly_mul_comm'` costs `X ^ (width − rank)`.  Those are the forced extra
zero eigenvalues of a Gram of a too-wide block, and they are exactly the "extra
eigenvalues" the general mirror has to account for.
-/

/-- **The rectangular mirror**, with the transfer factors written out.  `leftBlock`
and `rightBlock` may have any widths. -/
theorem pow_mul_det_shift_gram_mirror {ringCarrier : Type*} [CommRing ringCarrier]
    {rank leftWidth rightWidth : ℕ} (leftBlock : Matrix (Fin rank) (Fin leftWidth) ringCarrier)
    (rightBlock : Matrix (Fin rank) (Fin rightWidth) ringCarrier) (level : ringCarrier)
    (htight : leftBlock * leftBlockᵀ + rightBlock * rightBlockᵀ
      = level • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)) (shift : ringCarrier) :
    shift ^ rank
        * (shift • (1 : Matrix (Fin rightWidth) (Fin rightWidth) ringCarrier)
            - rightBlockᵀ * rightBlock).det
      = shift ^ rightWidth * ((-1) ^ rank
          * ((level - shift) • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
              - leftBlock * leftBlockᵀ).det) := by
  have htransfer : Polynomial.X ^ Fintype.card (Fin rank) * (rightBlockᵀ * rightBlock).charpoly
      = Polynomial.X ^ Fintype.card (Fin rightWidth) * (rightBlock * rightBlockᵀ).charpoly :=
    Matrix.charpoly_mul_comm' rightBlockᵀ rightBlock
  have hevaluated := congrArg (Polynomial.eval shift) htransfer
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Fintype.card_fin] at hevaluated
  rw [← det_smul_one_sub_eq_evalCharpoly, ← det_smul_one_sub_eq_evalCharpoly] at hevaluated
  rw [hevaluated, det_shift_frame_mirror leftBlock rightBlock level htight shift]

/-- The rectangular mirror with a SQUARE left block — the shape `(7,3)` presents: the
selected set has exactly `rank` atoms, its complement more. -/
theorem pow_mul_det_shift_gram_mirror_ofSquareLeft {ringCarrier : Type*} [CommRing ringCarrier]
    {rank rightWidth : ℕ} (leftBlock : Matrix (Fin rank) (Fin rank) ringCarrier)
    (rightBlock : Matrix (Fin rank) (Fin rightWidth) ringCarrier) (level : ringCarrier)
    (htight : leftBlock * leftBlockᵀ + rightBlock * rightBlockᵀ
      = level • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)) (shift : ringCarrier) :
    shift ^ rank
        * (shift • (1 : Matrix (Fin rightWidth) (Fin rightWidth) ringCarrier)
            - rightBlockᵀ * rightBlock).det
      = shift ^ rightWidth * ((-1) ^ rank
          * ((level - shift) • (1 : Matrix (Fin rank) (Fin rank) ringCarrier)
              - leftBlockᵀ * leftBlock).det) := by
  rw [pow_mul_det_shift_gram_mirror leftBlock rightBlock level htight shift,
    det_shift_gram_eq_det_shift_frame leftBlock (level - shift)]

/-- **The `(7,3)` mirror**, with the transfer factor cancelled.  A `3`-set against its
`4`-set complement inside a `7`-atom design: the complement's Gram carries one forced
zero eigenvalue and the remaining three reflect the selected triple's.

Stated over `ℝ` because the cancellation runs in the polynomial ring `ℝ[X]`, where
`X ^ 3` is a nonzerodivisor; that is also what makes the identity valid AT `shift = 0`,
where the naive division would be illegal.  This is the statement the `(7,3)` workflow
consumes: at equal shares there `level = 7/3`. -/
theorem det_shift_gram_mirror_sevenThree (leftBlock : Matrix (Fin 3) (Fin 3) ℝ)
    (rightBlock : Matrix (Fin 3) (Fin 4) ℝ) (level : ℝ)
    (htight : leftBlock * leftBlockᵀ + rightBlock * rightBlockᵀ
      = level • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (shift : ℝ) :
    (shift • (1 : Matrix (Fin 4) (Fin 4) ℝ) - rightBlockᵀ * rightBlock).det
      = -shift * ((level - shift) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
          - leftBlockᵀ * leftBlock).det := by
  have hpolynomial : Polynomial.X ^ 3 * (rightBlockᵀ * rightBlock).charpoly
      = Polynomial.X ^ 3
        * (Polynomial.C (-1 : ℝ) * Polynomial.X
            * ((leftBlockᵀ * leftBlock).charpoly.comp (Polynomial.C level - Polynomial.X))) := by
    refine Polynomial.funext fun probe => ?_
    have hraw := pow_mul_det_shift_gram_mirror_ofSquareLeft leftBlock rightBlock level htight probe
    rw [det_smul_one_sub_eq_evalCharpoly, det_smul_one_sub_eq_evalCharpoly] at hraw
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_comp, Polynomial.eval_sub]
    rw [hraw]
    ring
  have hcancel := mul_left_cancel₀
    (pow_ne_zero 3 (Polynomial.X_ne_zero (R := ℝ))) hpolynomial
  have hevaluated := congrArg (Polynomial.eval shift) hcancel
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_sub] at hevaluated
  rw [det_smul_one_sub_eq_evalCharpoly, det_smul_one_sub_eq_evalCharpoly, hevaluated]
  ring

/-! ## 4. The general symmetric involution

The naive general statement is FALSE; a positive substitute holds whenever the
off-diagonal block is invertible, with no involution hypothesis at all.
-/

/-- **The intertwining mirror.**  If `A B = B C` with `B` invertible then `A` and `C`
are similar, so their shifted determinants agree — no symmetry, no involution, no rank
condition, arbitrary square `A` and `C` over any integral domain.  Applied to the
blocks of a symmetric involution, where `J ^ 2 = 1` forces `A B = −(B D)`, this makes
the mirror a one-line conjugation whenever `B` is invertible; see
`det_shift_mirror_of_anticommutingBlocks`. -/
theorem det_shift_eq_of_intertwine {ringCarrier : Type*} [CommRing ringCarrier]
    [IsDomain ringCarrier] {size : ℕ}
    (sourceBlock targetBlock intertwiner : Matrix (Fin size) (Fin size) ringCarrier)
    (hintertwinerUnit : intertwiner.det ≠ 0)
    (hintertwine : sourceBlock * intertwiner = intertwiner * targetBlock) (shift : ringCarrier) :
    (shift • (1 : Matrix (Fin size) (Fin size) ringCarrier) - sourceBlock).det
      = (shift • (1 : Matrix (Fin size) (Fin size) ringCarrier) - targetBlock).det := by
  have hcommute : (shift • (1 : Matrix (Fin size) (Fin size) ringCarrier) - sourceBlock)
      * intertwiner
      = intertwiner * (shift • (1 : Matrix (Fin size) (Fin size) ringCarrier) - targetBlock) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hintertwine]
  have hdet := congrArg Matrix.det hcommute
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  exact mul_right_cancel₀ hintertwinerUnit (by rw [hdet]; ring)

/-- **The mirror for anticommuting blocks.**  `J ^ 2 = 1` on a block matrix
`[[A, B], [Bᵀ, D]]` gives `A B + B D = 0`; when `B` is invertible that alone forces
`spec(D) = −spec(A)`.  Stated on the anticommutation relation directly, so it needs
neither the involution nor the symmetry. -/
theorem det_shift_mirror_of_anticommutingBlocks {ringCarrier : Type*} [CommRing ringCarrier]
    [IsDomain ringCarrier] {size : ℕ}
    (diagonalFirst diagonalSecond offDiagonal : Matrix (Fin size) (Fin size) ringCarrier)
    (hoffDiagonalUnit : offDiagonal.det ≠ 0)
    (hanticommute : diagonalFirst * offDiagonal + offDiagonal * diagonalSecond = 0)
    (shift : ringCarrier) :
    (shift • (1 : Matrix (Fin size) (Fin size) ringCarrier) - diagonalFirst).det
      = (shift • (1 : Matrix (Fin size) (Fin size) ringCarrier) + diagonalSecond).det := by
  have hintertwine : diagonalFirst * offDiagonal = offDiagonal * (-diagonalSecond) := by
    rw [Matrix.mul_neg, eq_neg_iff_add_eq_zero]
    exact hanticommute
  have hmirror := det_shift_eq_of_intertwine diagonalFirst (-diagonalSecond) offDiagonal
    hoffDiagonalUnit hintertwine shift
  rwa [sub_neg_eq_add] at hmirror

/-- **The general symmetric involution, packaged.**  A symmetric involution presented
in block form `[[A, B], [Bᵀ, D]]` with `B` invertible has `spec(D) = −spec(A)`.  The
`(1,2)` block of `J ^ 2 = 1` is the anticommutation `A B + B D = 0`, and that is the
whole input.  This is the honest general statement the pen's Schur route was reaching
for; the price is the invertibility of `B`, which the frame form
`det_shift_gram_mirror` does not pay. -/
theorem det_shift_mirror_of_symmetricInvolutionBlocks {ringCarrier : Type*} [CommRing ringCarrier]
    [IsDomain ringCarrier] {size : ℕ}
    (diagonalFirst diagonalSecond offDiagonal : Matrix (Fin size) (Fin size) ringCarrier)
    (hoffDiagonalUnit : offDiagonal.det ≠ 0)
    (hinvolution :
      Matrix.fromBlocks diagonalFirst offDiagonal offDiagonalᵀ diagonalSecond
          * Matrix.fromBlocks diagonalFirst offDiagonal offDiagonalᵀ diagonalSecond = 1)
    (shift : ringCarrier) :
    (shift • (1 : Matrix (Fin size) (Fin size) ringCarrier) - diagonalFirst).det
      = (shift • (1 : Matrix (Fin size) (Fin size) ringCarrier) + diagonalSecond).det := by
  have hanticommute : diagonalFirst * offDiagonal + offDiagonal * diagonalSecond = 0 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one (l := Fin size) (m := Fin size)]
      at hinvolution
    have hblock := congrArg Matrix.toBlocks₁₂ hinvolution
    rwa [Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₁₂] at hblock
  exact det_shift_mirror_of_anticommutingBlocks diagonalFirst diagonalSecond offDiagonal
    hoffDiagonalUnit hanticommute shift

/-- **REFUTATION.**  The general symmetric-involution mirror is FALSE without a rank
hypothesis.  Take `J = 1` on `Fin 2`, which is symmetric with `J ^ 2 = 1`, and split
`Fin 2` into the two singletons — the two sides have EQUAL size, so no bookkeeping of
"extra ±1 eigenvalues in equal excess" can absorb the failure.  Both principal blocks
are `[1]`, so `spec(J[Kᶜ]) = {1}` while `−spec(J[K]) = {−1}`.  At `shift = 0` the two
determinants are `−1` and `+1`.

What is missing is a rank condition — `trace J = 0`, equivalently `rank(J + 1) = 2·|K|`.
Its NECESSITY is what this theorem proves; its sufficiency is classical but is not
mechanized in this file.  What the frame identity (TIGHT) supplies in its place IS
mechanized (`trace_gram_add_trace_gram`), which is why `det_shift_gram_mirror` needs no
genericity while the statement below is simply untrue. -/
theorem not_forall_det_shift_mirror_ofSymmetricInvolution :
    ¬ ∀ invol : Matrix (Fin 2) (Fin 2) ℝ, involᵀ = invol → invol * invol = 1 →
        ∀ shift : ℝ,
          (shift • (1 : Matrix (Fin 1) (Fin 1) ℝ) - invol.submatrix ![1] ![1]).det
            = (-1) ^ 1
              * ((-shift) • (1 : Matrix (Fin 1) (Fin 1) ℝ) - invol.submatrix ![0] ![0]).det := by
  intro hmirror
  have hinstance := hmirror 1 Matrix.transpose_one (Matrix.one_mul 1) 0
  rw [Matrix.det_fin_one, Matrix.det_fin_one] at hinstance
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, neg_zero] at hinstance
  norm_num at hinstance

/-! ## 5. The design layer — the `(6,3)` equal-share stratum

The `WeightedDesign` interface.  A `3`–`3` split of `Fin 6` is presented as six indices
together with the single hypothesis that the tuple `![.., .., .., .., .., ..]` is a
bijection of `Fin 6`; for concrete indices that is `by decide`.
-/

/-- The unit directions of a chosen list of atoms, as the COLUMNS of a `rank x selSize`
matrix.  `directionFrame D pick * (directionFrame D pick)ᵀ` is the selected frame
operator in coordinate space and `(directionFrame D pick)ᵀ * directionFrame D pick` is
the selected direction Gram in slot space — the two sides of the mirror. -/
noncomputable def directionFrame (D : WeightedDesign m k) {selSize : ℕ}
    (pick : Fin selSize → Fin m) : Matrix (Fin k) (Fin selSize) ℝ :=
  Matrix.of fun coordIndex slot => unitAtom D (pick slot) coordIndex

/-- Coordinate space: the frame operator of the selected directions. -/
theorem directionFrame_mul_transpose (D : WeightedDesign m k) {selSize : ℕ}
    (pick : Fin selSize → Fin m) :
    directionFrame D pick * (directionFrame D pick)ᵀ
      = ∑ slot, atomMatrix (unitAtom D (pick slot)) := by
  ext coordRow coordCol
  simp only [directionFrame, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply]

/-- Slot space: the direction Gram of the selected directions, entry by entry. -/
theorem transpose_mul_directionFrame_apply (D : WeightedDesign m k) {selSize : ℕ}
    (pick : Fin selSize → Fin m) (slotRow slotCol : Fin selSize) :
    ((directionFrame D pick)ᵀ * directionFrame D pick) slotRow slotCol
      = directionGram D (pick slotRow) (pick slotCol) := by
  simp only [directionFrame, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    directionGram, dotProduct]

/-- A share-`1/2` atom is nondegenerate. -/
theorem leverageOf_pos_of_atomShare_pos (D : WeightedDesign m k) {atomIndex : Fin m}
    (hshare : 0 < atomShare D atomIndex) : 0 < leverageOf (D.atom atomIndex) := by
  by_contra hnonpos
  rw [not_lt] at hnonpos
  have hnonneg : 0 ≤ leverageOf (D.atom atomIndex) :=
    Finset.sum_nonneg fun coordIndex _ => sq_nonneg _
  have hzero : leverageOf (D.atom atomIndex) = 0 := le_antisymm hnonpos hnonneg
  rw [atomShare, hzero, mul_zero] at hshare
  exact lt_irrefl 0 hshare

/-- **(TIGHT) in raw coordinates.**  At a uniform weight the RAW atom sums of a subset
and its complement add to `weight⁻¹ . I` — the same split the mirror consumes, but
stated on `Gtz.subsetSum`, which is what `Gtz.Dominates` is about.  General in `m`, `k`
and the subset; at the equal-share `(6,3)` stratum with weight `1/6` the level is `6`. -/
theorem subsetSum_add_subsetSum_compl_of_uniformWeight (D : WeightedDesign m k)
    {weightValue : ℝ} (huniform : ∀ atomIndex, D.weight atomIndex = weightValue)
    (selected : Finset (Fin m)) :
    subsetSum D selected + subsetSum D selectedᶜ
      = weightValue⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  have hcardWeight : (m : ℝ) * weightValue = 1 := by
    have hsum := D.weight_sum_one
    rw [Finset.sum_congr rfl fun atomIndex _ => huniform atomIndex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    exact hsum
  have hpositive : 0 < weightValue := by
    rcases lt_trichotomy weightValue 0 with hnegative | hzero | hpositive
    · exact absurd hcardWeight (by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    · exact absurd hcardWeight (by rw [hzero, mul_zero]; norm_num)
    · exact hpositive
  have hparseval := D.isParseval
  rw [Finset.sum_congr rfl fun atomIndex _ => by rw [huniform atomIndex], ← Finset.smul_sum]
    at hparseval
  rw [subsetSum, subsetSum, Finset.sum_add_sum_compl, ← hparseval, smul_smul,
    inv_mul_cancel₀ hpositive.ne', one_smul]

/-- **The mirror in domination form.**  `C` dominates exactly when the complement's raw
atom sum is capped at `weight⁻¹ − 1`.  Pure algebra on the raw tight split — no
`AB`/`BA`, no squareness, no rank hypothesis, arbitrary subset — and it is the cheapest
mirror statement in the file: domination of `C` is a LARGEST-eigenvalue ceiling on `Cᶜ`.
At the equal-share `(6,3)` stratum the cap is `5`. -/
theorem dominates_iff_posSemidef_smul_one_sub_subsetSum_compl (D : WeightedDesign m k)
    {weightValue : ℝ} (huniform : ∀ atomIndex, D.weight atomIndex = weightValue)
    (selected : Finset (Fin m)) :
    Dominates D selected
      ↔ ((weightValue⁻¹ - 1) • (1 : Matrix (Fin k) (Fin k) ℝ)
          - subsetSum D selectedᶜ).PosSemidef := by
  have hsplit := subsetSum_add_subsetSum_compl_of_uniformWeight D huniform selected
  have hselected : subsetSum D selected
      = weightValue⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ) - subsetSum D selectedᶜ := by
    rw [← hsplit]; abel
  rw [Dominates, hselected, sub_smul, one_smul]
  refine Iff.of_eq (congrArg Matrix.PosSemidef ?_)
  abel

/-- **The raw-to-direction rescale.**  At a uniform leverage the raw atom sum is the
direction frame operator scaled by the leverage.  This is the only bridge a consumer
needs between `Gtz.Dominates` (raw, coordinate space) and `directionFrame` (unit, the
object the mirror is stated on): at leverage `3`, `subsetSum D C ⪰ 1` is exactly
`Σ_{c ∈ C} u_c u_cᵀ ⪰ (1/3) . I`. -/
theorem subsetSum_eq_smul_sum_atomMatrix_unitAtom (D : WeightedDesign m k) {leverageValue : ℝ}
    (huniform : ∀ atomIndex, leverageOf (D.atom atomIndex) = leverageValue)
    (hpositive : 0 < leverageValue) (selected : Finset (Fin m)) :
    subsetSum D selected
      = leverageValue • ∑ atomIndex ∈ selected, atomMatrix (unitAtom D atomIndex) := by
  rw [Finset.smul_sum, subsetSum]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [atomMatrix_unitAtom, huniform atomIndex, smul_smul, mul_inv_cancel₀ hpositive.ne', one_smul]

/-- **The triple's raw atom sum IS its direction frame operator, rescaled.**  Closes the
loop for a consumer holding `Gtz.Dominates D {a, b, c}`: at uniform leverage that is
`leverageValue • (directionFrame · directionFrameᵀ) ⪰ 1`, and `directionFrame` is the
block every mirror statement above is phrased on. -/
theorem subsetSum_triple_eq_smul_directionFrame_mul_transpose (D : WeightedDesign m k)
    {leverageValue : ℝ} (huniform : ∀ atomIndex, leverageOf (D.atom atomIndex) = leverageValue)
    (hpositive : 0 < leverageValue) {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    subsetSum D {first, second, third}
      = leverageValue • (directionFrame D ![first, second, third]
          * (directionFrame D ![first, second, third])ᵀ) := by
  rw [subsetSum_eq_smul_sum_atomMatrix_unitAtom D huniform hpositive,
    directionFrame_mul_transpose, Fin.sum_univ_three,
    Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [add_assoc]

/-- **The equal-share frame law.**  When every share is `shareValue` the unit
directions form a tight frame at level `shareValue⁻¹`.  At the `(6,3)` stratum
`shareValue = 1/2` and the level is `2`. -/
theorem sum_atomMatrix_unitAtom_of_uniformShare (D : WeightedDesign m k) {shareValue : ℝ}
    (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue) (hpositive : 0 < shareValue) :
    ∑ atomIndex, atomMatrix (unitAtom D atomIndex)
      = shareValue⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  have hframe := sum_atomShare_smul_atomMatrix_unitAtom D
  rw [Finset.sum_congr rfl fun atomIndex _ => by rw [huniform atomIndex], ← Finset.smul_sum] at hframe
  rw [← hframe, smul_smul, inv_mul_cancel₀ hpositive.ne', one_smul]

/-- The six-index expansion supplied by a bijective tuple. -/
theorem sum_eq_of_bijective_six {valueType : Type*} [AddCommMonoid valueType]
    {leftFirst leftSecond leftThird rightFirst rightSecond rightThird : Fin 6}
    (hbijective :
      Function.Bijective ![leftFirst, leftSecond, leftThird, rightFirst, rightSecond, rightThird])
    (summand : Fin 6 → valueType) :
    ∑ atomIndex, summand atomIndex
      = summand leftFirst + summand leftSecond + summand leftThird
        + summand rightFirst + summand rightSecond + summand rightThird := by
  rw [← Equiv.sum_comp (Equiv.ofBijective _ hbijective) summand, Fin.sum_univ_six]
  simp only [Equiv.ofBijective_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four]
  abel

/-- **(TIGHT) at the equal-share `(6,3)` stratum.**  Every `3`–`3` split of a design
whose shares are all `1/2` gives two square direction frames whose frame operators sum
to `2 . I`.  This is the hypothesis every mirror statement above consumes. -/
theorem directionFrame_tightSplit_six (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {leftFirst leftSecond leftThird rightFirst rightSecond rightThird : Fin 6}
    (hbijective :
      Function.Bijective ![leftFirst, leftSecond, leftThird, rightFirst, rightSecond, rightThird]) :
    directionFrame D ![leftFirst, leftSecond, leftThird]
          * (directionFrame D ![leftFirst, leftSecond, leftThird])ᵀ
        + directionFrame D ![rightFirst, rightSecond, rightThird]
          * (directionFrame D ![rightFirst, rightSecond, rightThird])ᵀ
      = (2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have hframe := sum_atomMatrix_unitAtom_of_uniformShare D huniform (by norm_num)
  rw [sum_eq_of_bijective_six hbijective] at hframe
  rw [directionFrame_mul_transpose, directionFrame_mul_transpose, Fin.sum_univ_three,
    Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [show ((1 : ℝ) / 2)⁻¹ = (2 : ℝ) by norm_num] at hframe
  rw [← hframe]
  abel

/-! ### The two scalars of a triple -/

/-- `sigma_C`, the sum of the three squared direction correlations of a triple. -/
noncomputable def directionTripleSigma (D : WeightedDesign m k)
    (first second third : Fin m) : ℝ :=
  directionGram D first second ^ 2 + directionGram D first third ^ 2
    + directionGram D second third ^ 2

/-- `P_C`, the oriented triangle product of a triple's three direction correlations. -/
noncomputable def directionTripleProduct (D : WeightedDesign m k)
    (first second third : Fin m) : ℝ :=
  directionGram D first second * directionGram D first third * directionGram D second third

/-- The shifted determinant of a triple's direction Gram at shift `1`: the hollow
matrix `1 − Γ[C]` has determinant `−2 P_C`.  This is what turns the mirror into the
sign flip of `P`. -/
theorem det_one_smul_sub_directionGram_triple (D : WeightedDesign m k)
    {first second third : Fin m} (hfirst : 0 < leverageOf (D.atom first))
    (hsecond : 0 < leverageOf (D.atom second)) (hthird : 0 < leverageOf (D.atom third)) :
    ((1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (directionFrame D ![first, second, third])ᵀ
          * directionFrame D ![first, second, third]).det
      = -2 * directionTripleProduct D first second third := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    transpose_mul_directionFrame_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.reduceEq, if_true, if_false,
    mul_one, mul_zero]
  rw [directionGram_self D hfirst, directionGram_self D hsecond, directionGram_self D hthird,
    directionGram_comm D second first, directionGram_comm D third first,
    directionGram_comm D third second, directionTripleProduct]
  ring

/-- **P FLIPS SIGN UNDER THE MIRROR.**  For a `3`–`3` split of an equal-share `(6,3)`
design the two oriented triangle products are negatives of one another.  This is the
pen's `P_Cᶜ = −P_C`, and it is what makes the coherent side of a mirror pair
well-defined — see `exists_nonneg_directionTripleProduct_ofSplit`. -/
theorem directionTripleProduct_compl_eq_neg (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {leftFirst leftSecond leftThird rightFirst rightSecond rightThird : Fin 6}
    (hbijective :
      Function.Bijective ![leftFirst, leftSecond, leftThird, rightFirst, rightSecond, rightThird]) :
    directionTripleProduct D rightFirst rightSecond rightThird
      = -directionTripleProduct D leftFirst leftSecond leftThird := by
  have hleverage : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hmirror := det_shift_gap_mirror_ofLevelTwo
    (directionFrame D ![leftFirst, leftSecond, leftThird])
    (directionFrame D ![rightFirst, rightSecond, rightThird])
    (directionFrame_tightSplit_six D huniform hbijective) 0
  rw [show ∀ block : Matrix (Fin 3) (Fin 3) ℝ,
      (0 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - (block - 1)
        = (1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - block from fun block => by
      rw [zero_smul, one_smul]; abel,
    show ∀ block : Matrix (Fin 3) (Fin 3) ℝ,
      (-0 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - (block - 1)
        = (1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - block from fun block => by
      rw [neg_zero, zero_smul, one_smul]; abel] at hmirror
  rw [det_one_smul_sub_directionGram_triple D (hleverage rightFirst) (hleverage rightSecond)
      (hleverage rightThird),
    det_one_smul_sub_directionGram_triple D (hleverage leftFirst) (hleverage leftSecond)
      (hleverage leftThird)] at hmirror
  norm_num at hmirror
  linarith [hmirror]

/-- **Every mirror pair has a coherent side.**  Immediate from the sign flip, and it is
the selection step the heavy-cell criterion `(C3)` needs: the bound
`sigma − 3P ≤ 1 − 5|P|` is a one-sided statement, valid only where `P ≥ 0`. -/
theorem exists_nonneg_directionTripleProduct_ofSplit (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {leftFirst leftSecond leftThird rightFirst rightSecond rightThird : Fin 6}
    (hbijective :
      Function.Bijective ![leftFirst, leftSecond, leftThird, rightFirst, rightSecond, rightThird]) :
    0 ≤ directionTripleProduct D leftFirst leftSecond leftThird
      ∨ 0 ≤ directionTripleProduct D rightFirst rightSecond rightThird := by
  by_cases hnonneg : 0 ≤ directionTripleProduct D leftFirst leftSecond leftThird
  · exact Or.inl hnonneg
  · refine Or.inr ?_
    rw [not_le] at hnonneg
    rw [directionTripleProduct_compl_eq_neg D huniform hbijective]
    linarith

/-! ### `sigma` is mirror-invariant — the row-law proof

The determinant mirror is not needed for `sigma`.  Summing the row law over `C` and
over `Cᶜ` gives `2 sigma_C + X = |C| (rowMass − 1)` with the SAME cross mass `X` on
both sides, so the two `sigma`s differ by `(|C| − |Cᶜ|)(rowMass − 1) / 2` — zero
exactly when the split is balanced.  Nothing here is a matrix statement, and the
argument survives verbatim at `(7,3)`, where it returns `sigma_Cᶜ = sigma_C + 2/3`.
-/

/-- **The row law at a uniform share**, expanded over a bijective six-tuple: for every
atom the six squared correlations to the whole design sum to `shareValue⁻¹`. -/
theorem sum_directionGram_sq_split (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {leftFirst leftSecond leftThird rightFirst rightSecond rightThird : Fin 6}
    (hbijective :
      Function.Bijective ![leftFirst, leftSecond, leftThird, rightFirst, rightSecond, rightThird])
    (atomIndex : Fin 6) :
    directionGram D atomIndex leftFirst ^ 2 + directionGram D atomIndex leftSecond ^ 2
        + directionGram D atomIndex leftThird ^ 2 + directionGram D atomIndex rightFirst ^ 2
        + directionGram D atomIndex rightSecond ^ 2 + directionGram D atomIndex rightThird ^ 2
      = 2 := by
  have hleverage : ∀ index : Fin 6, 0 < leverageOf (D.atom index) := fun index =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform index]; norm_num)
  have hrow := sum_atomShare_mul_sq_directionGram D (hleverage atomIndex)
  rw [Finset.sum_congr rfl fun otherIndex _ => by rw [huniform otherIndex],
    sum_eq_of_bijective_six hbijective] at hrow
  linarith [hrow]

/-- **SIGMA IS MIRROR-INVARIANT.**  For a `3`–`3` split of an equal-share `(6,3)`
design the two triples carry the same squared-correlation mass — the pen's
`sigma_Cᶜ = sigma_C`.  Proved from the row law alone: no determinant, no
characteristic polynomial, no matrix. -/
theorem directionTripleSigma_compl_eq (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {leftFirst leftSecond leftThird rightFirst rightSecond rightThird : Fin 6}
    (hbijective :
      Function.Bijective ![leftFirst, leftSecond, leftThird, rightFirst, rightSecond, rightThird]) :
    directionTripleSigma D rightFirst rightSecond rightThird
      = directionTripleSigma D leftFirst leftSecond leftThird := by
  have hleverage : ∀ index : Fin 6, 0 < leverageOf (D.atom index) := fun index =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform index]; norm_num)
  have hrowLeftFirst := sum_directionGram_sq_split D huniform hbijective leftFirst
  have hrowLeftSecond := sum_directionGram_sq_split D huniform hbijective leftSecond
  have hrowLeftThird := sum_directionGram_sq_split D huniform hbijective leftThird
  have hrowRightFirst := sum_directionGram_sq_split D huniform hbijective rightFirst
  have hrowRightSecond := sum_directionGram_sq_split D huniform hbijective rightSecond
  have hrowRightThird := sum_directionGram_sq_split D huniform hbijective rightThird
  rw [directionGram_self D (hleverage leftFirst)] at hrowLeftFirst
  rw [directionGram_self D (hleverage leftSecond), directionGram_comm D leftSecond leftFirst]
    at hrowLeftSecond
  rw [directionGram_self D (hleverage leftThird), directionGram_comm D leftThird leftFirst,
    directionGram_comm D leftThird leftSecond] at hrowLeftThird
  rw [directionGram_self D (hleverage rightFirst), directionGram_comm D rightFirst leftFirst,
    directionGram_comm D rightFirst leftSecond, directionGram_comm D rightFirst leftThird]
    at hrowRightFirst
  rw [directionGram_self D (hleverage rightSecond), directionGram_comm D rightSecond leftFirst,
    directionGram_comm D rightSecond leftSecond, directionGram_comm D rightSecond leftThird,
    directionGram_comm D rightSecond rightFirst] at hrowRightSecond
  rw [directionGram_self D (hleverage rightThird), directionGram_comm D rightThird leftFirst,
    directionGram_comm D rightThird leftSecond, directionGram_comm D rightThird leftThird,
    directionGram_comm D rightThird rightFirst, directionGram_comm D rightThird rightSecond]
    at hrowRightThird
  rw [directionTripleSigma, directionTripleSigma]
  linarith [hrowLeftFirst, hrowLeftSecond, hrowLeftThird, hrowRightFirst, hrowRightSecond,
    hrowRightThird]

/-! ## 6. The `sigma` mirror in full generality

The six-index proof above is the `(6,3)` instance of a statement about ARBITRARY sizes
and ARBITRARY subsets, and the general form is what carries to `(7,3)`.  Write

    mass(C)   = Σ_{x,y ∈ C} gamma_xy²        (the diagonal included: `|C| + 2 sigma_C`),
    cross(C)  = Σ_{x ∈ C, y ∈ Cᶜ} gamma_xy².

The row law says every row's total square mass is `shareValue⁻¹`, so summing it over `C`
gives `mass(C) + cross(C) = |C| · shareValue⁻¹`; and `cross` is symmetric under
complementation because `gamma` is.  Subtracting the two readings:

    mass(C) − mass(Cᶜ)  =  (|C| − |Cᶜ|) · shareValue⁻¹,

zero exactly on a balanced split.  No matrices, no determinants, no `m = 2k`.
-/

/-- The total squared direction-correlation mass INSIDE a subset, diagonal included. -/
noncomputable def directionSquareMass (D : WeightedDesign m k) (selected : Finset (Fin m)) : ℝ :=
  ∑ rowIndex ∈ selected, ∑ colIndex ∈ selected, directionGram D rowIndex colIndex ^ 2

/-- The total squared direction-correlation mass ACROSS the cut. -/
noncomputable def directionCrossSquareMass (D : WeightedDesign m k)
    (selected : Finset (Fin m)) : ℝ :=
  ∑ rowIndex ∈ selected, ∑ colIndex ∈ selectedᶜ, directionGram D rowIndex colIndex ^ 2

/-- **The row law at a uniform share**, in its divisionless reading: every atom's
squared correlations to the whole design total `shareValue⁻¹`.  At the `(6,3)` stratum
that is `2`; at the equal-share `(7,3)` stratum, where `shareValue = 3/7`, it is `7/3`. -/
theorem sum_directionGram_sq_of_uniformShare (D : WeightedDesign m k) {shareValue : ℝ}
    (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue) (hpositive : 0 < shareValue)
    (atomIndex : Fin m) :
    ∑ otherIndex, directionGram D atomIndex otherIndex ^ 2 = shareValue⁻¹ := by
  have hrow := sum_atomShare_mul_sq_directionGram D
    (leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; exact hpositive))
  rw [Finset.sum_congr rfl fun otherIndex _ => by rw [huniform otherIndex], ← Finset.mul_sum]
    at hrow
  have hnonzero : shareValue ≠ 0 := hpositive.ne'
  field_simp
  linear_combination hrow

/-- Summing the row law over the subset: inside mass plus cross mass is
`|C| · shareValue⁻¹`. -/
theorem directionSquareMass_add_directionCrossSquareMass (D : WeightedDesign m k)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hpositive : 0 < shareValue) (selected : Finset (Fin m)) :
    directionSquareMass D selected + directionCrossSquareMass D selected
      = selected.card * shareValue⁻¹ := by
  rw [directionSquareMass, directionCrossSquareMass, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun rowIndex _ => by
      rw [Finset.sum_add_sum_compl,
        sum_directionGram_sq_of_uniformShare D huniform hpositive rowIndex],
    Finset.sum_const, nsmul_eq_mul]

/-- The cross mass does not see which side of the cut it is read from — the direction
Gram is symmetric.  This is the step that makes the two row-law readings comparable. -/
theorem directionCrossSquareMass_compl (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    directionCrossSquareMass D selectedᶜ = directionCrossSquareMass D selected := by
  rw [directionCrossSquareMass, directionCrossSquareMass, compl_compl, Finset.sum_comm]
  exact Finset.sum_congr rfl fun rowIndex _ =>
    Finset.sum_congr rfl fun colIndex _ => by rw [directionGram_comm]

/-- **THE GENERAL SIGMA MIRROR.**  The inside square masses of a subset and its
complement differ by exactly `(|C| − |Cᶜ|) · shareValue⁻¹`.  Arbitrary size, arbitrary
rank, arbitrary subset; the balanced case is `directionSquareMass_compl_eq`. -/
theorem directionSquareMass_sub_directionSquareMass_compl (D : WeightedDesign m k)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hpositive : 0 < shareValue) (selected : Finset (Fin m)) :
    directionSquareMass D selected - directionSquareMass D selectedᶜ
      = ((selected.card : ℝ) - (selectedᶜ.card : ℝ)) * shareValue⁻¹ := by
  have hselected :=
    directionSquareMass_add_directionCrossSquareMass D huniform hpositive selected
  have hcomplement :=
    directionSquareMass_add_directionCrossSquareMass D huniform hpositive selectedᶜ
  rw [directionCrossSquareMass_compl] at hcomplement
  linear_combination hselected - hcomplement

/-- **SIGMA IS MIRROR-INVARIANT, general form.**  A balanced split of an equal-share
design carries equal square mass on both sides — the pen's `sigma_Cᶜ = sigma_C` with no
size restriction beyond `|C| = |Cᶜ|`. -/
theorem directionSquareMass_compl_eq (D : WeightedDesign m k) {shareValue : ℝ}
    (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue) (hpositive : 0 < shareValue)
    (selected : Finset (Fin m)) (hbalanced : selected.card = selectedᶜ.card) :
    directionSquareMass D selectedᶜ = directionSquareMass D selected := by
  have hdifference :=
    directionSquareMass_sub_directionSquareMass_compl D huniform hpositive selected
  rw [hbalanced, sub_self, zero_mul] at hdifference
  linarith

/-- The dictionary between the subset mass and the triple's `sigma`: the diagonal
contributes `3` and every off-diagonal pair is counted twice. -/
theorem directionSquareMass_triple (D : WeightedDesign m k) {first second third : Fin m}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hfirstPositive : 0 < leverageOf (D.atom first))
    (hsecondPositive : 0 < leverageOf (D.atom second))
    (hthirdPositive : 0 < leverageOf (D.atom third)) :
    directionSquareMass D {first, second, third}
      = 3 + 2 * directionTripleSigma D first second third := by
  have hexpand : ∀ summand : Fin m → ℝ,
      ∑ atomIndex ∈ ({first, second, third} : Finset (Fin m)), summand atomIndex
        = summand first + summand second + summand third := by
    intro summand
    rw [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
      Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton, add_assoc]
  rw [directionSquareMass, hexpand, hexpand, hexpand, hexpand,
    directionGram_self D hfirstPositive, directionGram_self D hsecondPositive,
    directionGram_self D hthirdPositive, directionGram_comm D second first,
    directionGram_comm D third first, directionGram_comm D third second, directionTripleSigma]
  ring

/-- **The `(7,3)` sigma correction, exactly.**  At the equal-share `(7,3)` stratum a
triple and its four-atom complement do NOT carry the same mass: the imbalance
`|Cᶜ| − |C| = 1` costs `shareValue⁻¹ = 7/3`.  Reading it in `sigma` coordinates —
`mass(C) = 3 + 2 sigma_C` by `directionSquareMass_triple`, and `mass(Cᶜ) = 4 + 2
sigma_Cᶜ` with `sigma_Cᶜ` the sum over the complement's SIX pairs, an object this file
does not name — gives `sigma_Cᶜ = sigma_C + 2/3`, the exact statement the `(7,3)`
workflow inherits in place of the `(6,3)` equality.  The mass form above is the landed
one; the `sigma` reading is arithmetic on top of it. -/
theorem directionSquareMass_compl_sub_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (selected : Finset (Fin 7))
    (hcard : selected.card = 3) :
    directionSquareMass D selectedᶜ - directionSquareMass D selected = 7 / 3 := by
  have hcomplementCard : selectedᶜ.card = 4 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  have hdifference :=
    directionSquareMass_sub_directionSquareMass_compl D huniform (by norm_num) selected
  rw [hcard, hcomplementCard] at hdifference
  norm_num at hdifference
  linarith

/-! ## 7. Non-vacuity — the mirror at the icosahedron

The equal-share `(6,3)` stratum is not an empty hypothesis set.  `Gtz.icosaDesign`, the
six icosahedral diagonals at weight `1/6` and leverage `3`, sits on it, and the two
scalar mirror laws fire there against the coherent triple `{0,2,4}` and its complement
`{1,3,5}` — the split `Gtz.icosaDesign_dominates` selects.
-/

/-- Every icosahedral diagonal has share `1/2`: weight `1/6` times leverage `3`.  So
`icosaDesign` lies on the equal-share `(6,3)` stratum every theorem of section 5
quantifies over. -/
theorem atomShare_icosaDesign (atomIndex : Fin 6) : atomShare icosaDesign atomIndex = 1 / 2 := by
  rw [atomShare, leverageOf_eq_dotProduct, icosaDesign_atom, icosaAtom_leverage]
  show (1 : ℝ) / 6 * 3 = 1 / 2
  norm_num

/-- **The sigma mirror, instantiated.**  The icosahedron's coherent triple `{0,2,4}`
and its complement `{1,3,5}` carry the same squared-correlation mass. -/
theorem directionTripleSigma_icosaDesign_mirror :
    directionTripleSigma icosaDesign 1 3 5 = directionTripleSigma icosaDesign 0 2 4 :=
  directionTripleSigma_compl_eq icosaDesign atomShare_icosaDesign (by decide)

/-- **The product mirror, instantiated.**  The two oriented triangle products of the
icosahedron's `{0,2,4}` / `{1,3,5}` split are negatives — the sign flip that makes
exactly one of the two triples coherent. -/
theorem directionTripleProduct_icosaDesign_mirror :
    directionTripleProduct icosaDesign 1 3 5 = -directionTripleProduct icosaDesign 0 2 4 :=
  directionTripleProduct_compl_eq_neg icosaDesign atomShare_icosaDesign (by decide)

end Gtz
