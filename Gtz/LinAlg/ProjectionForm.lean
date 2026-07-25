/-
# The projection form of a weighted design

Set `v_c = √t_c · g_c`.  Parseval `Σ_c t_c g_c g_cᵀ = I_k` says exactly that the
`m × k` matrix `V` whose rows are the `v_c` has orthonormal COLUMNS, `VᵀV = I_k`.
Therefore

    P := V Vᵀ  ∈  ℝ^{m×m}

is a symmetric idempotent of trace `k` — a rank-`k` orthogonal projection on the
INDEX space — whose diagonal is the classical leverage score `P_cc = t_c · |g_c|²`.
The design is thereby transported from `(atoms in ℝ^k, weights)` to
`(a projection on ℝ^m, weights)`, and the selection problem becomes a question
about principal blocks of a projection.

## The headline

For a selection of atoms indexed by `pick`, the positive-diagonal congruence

    Gram_pick − I  =  D^{-1/2} (P_pick − diag t_pick) D^{-1/2},   D = diag t_pick

holds UNCONDITIONALLY in the number of selected atoms
(`projectionBlock_sub_weightDiagonal`), so

    (Gram_pick − I) ⪰ 0   ⟺   P_pick ⪰ diag t_pick

at every selection size (`posSemidef_projectionBlock_iff`).  When the selection
size is exactly the rank `k` the selected-row matrix is SQUARE, so `MᵀM ⪰ I` and
`MMᵀ ⪰ I` are interchangeable (`posSemidef_transpose_mul_sub_one_comm`), and the
two sides join up:

    Dominates D C   ⟺   P_C ⪰ diag t_C        (`dominates_iff_posSemidef_projectionBlock`)

**The size hypothesis is not decoration.**  `Dominates` is the `k × k` statement
`Σ_{c ∈ C} g_c g_cᵀ ⪰ I_k = MᵀM ⪰ I_k`, while the block statement is the
`|C| × |C|` statement `MMᵀ ⪰ I_{|C|}`.  For `|C| < k` the left side has rank
`≤ |C| < k` and can never dominate, while the block side is unconstrained; for
`|C| > k` the block side has rank `≤ k < |C|` and never holds, while domination
can.  Both failures are pure rank effects and both were measured (4508/8400 and
7614/14000 at `(7,3)`); `|C| = k` is the only size where the equivalence has
content in both directions.  The two one-sided halves at the other sizes are not
recorded here because at those sizes one side is uniformly false.

## What else is here

* `sum_det_projectionMinors` — the VOLUME SAMPLING identity: the sum of the
  `j × j` principal minors of `P` is `C(k, j)`, in particular `1` at `j = k`.
  Proved from the Weinstein–Aronszajn identity `det(1 + AB) = det(1 + BA)` over
  `ℝ[X]` plus Mathlib's `coeff_det_one_add_X_smul_eq_sum_minors`; no spectral
  theorem, no Cauchy–Binet (which Mathlib does not have).
* `det_one_add_X_smul_shifted` — the generating function of the SHIFTED minor
  sums, `det(1 + X·(P − s·I)) = (1 − sX)^{m−k}(1 + (1−s)X)^k`, and hence
  `sum_det_shiftedProjectionMinors_designIndependent`: at a uniform weight the
  averaging aggregate `Σ_{|T|=k} det(P_T − s·I_T)` is a function of `(m, k, s)`
  ALONE.  This is strictly stronger than the campaign's refutation by witness:
  the averaging functional carries zero information about the design, so it is
  dead by identity and not by counterexample.  Coefficient extraction at
  `(m, k, s) = (7, 3, 1/7)` gives `−112/343`, matching the measured
  `e_3(N) = −112` on the `(4,1,1,1)` tie stratum; that arithmetic is NOT
  mechanized here, only the identity it is extracted from.
* `det_projectionBlock_sub_weightDiagonal` — the minor-by-minor rescaling
  `det(P_S − diag t_S) = (∏_{c ∈ S} t_c) · det(Gram_S − I)`.  A strictly positive
  factor, so the two decision procedures agree principal minor by principal
  minor, with no eigenvalues anywhere.  This is the float-safe oracle.
* the uniform case: `gtzOriginal_iff_frameProjectionCovering` and
  `gtzOriginal_of_projectionCovering`.
* `projectionOfDesign_tetraDesign` — the `(4,3)` four-cycle, the unique
  series-parallel class at `m = k + 1`, whose projection is exactly `I − J/4`
  and whose every `3`-block ties at margin exactly `0`.

## Honest scope

`ProjectionCovering n k → GtzOriginal n k` runs ONE way.  The reverse needs every
symmetric idempotent of trace `k` to factor as `A Aᵀ` with `AᵀA = I` — a spectral
factorization that neither this file nor the repo has; the repo's bridge
(`original_of_weighted_single`) also runs one way, weighted ⟹ original.  What IS
an iff is `gtzOriginal_iff_frameProjectionCovering`, the same statement with the
projection presented as `A Aᵀ`; the gap between the two is exactly the
surjectivity of `A ↦ A Aᵀ` onto rank-`k` projections, and nothing else.

The averaging closed form is proved for a SCALAR shift `s · I` only.  For a
general diagonal shift `diag t` the aggregate does not factor — measured to vary
over designs at fixed non-uniform `t` — so the design-independence above is
exactly a uniform-weight phenomenon and is not stated more generally.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.Design.StressCertificate
import Gtz.Reduction.Reductions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The scaled frame and the projection it generates -/

/-- The Parseval frame in scaled form: the `m × k` matrix whose `c`-th row is
`√t_c · g_c`. -/
noncomputable def scaledAtomRows (D : WeightedDesign m k) : Matrix (Fin m) (Fin k) ℝ :=
  Matrix.of fun atomIndex coord => Real.sqrt (D.weight atomIndex) * D.atom atomIndex coord

/-- A row of the scaled frame is the atom rescaled by the square root of its weight. -/
theorem scaledAtomRows_row (D : WeightedDesign m k) (atomIndex : Fin m) :
    scaledAtomRows D atomIndex = Real.sqrt (D.weight atomIndex) • D.atom atomIndex := rfl

/-- **Parseval is orthonormality of the scaled frame's columns**: `VᵀV = I_k`. -/
theorem transpose_mul_scaledAtomRows (D : WeightedDesign m k) :
    (scaledAtomRows D)ᵀ * scaledAtomRows D = 1 := by
  rw [transpose_mul_self_eq_sum_rows, ← D.isParseval]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [scaledAtomRows_row, atomMatrix_smul, Real.sq_sqrt (D.weight_pos atomIndex).le]

/-- The projection form of a design: `P = V Vᵀ` on the INDEX space `ℝ^m`. -/
noncomputable def projectionOfDesign (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  scaledAtomRows D * (scaledAtomRows D)ᵀ

/-- The entries of the projection form: `P_cd = √t_c √t_d ⟨g_c, g_d⟩`. -/
theorem projectionOfDesign_apply (D : WeightedDesign m k) (rowIndex colIndex : Fin m) :
    projectionOfDesign D rowIndex colIndex
      = Real.sqrt (D.weight rowIndex) * Real.sqrt (D.weight colIndex)
        * (D.atom rowIndex ⬝ᵥ D.atom colIndex) := by
  simp only [projectionOfDesign, scaledAtomRows, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun coord _ => by ring

/-- **(a) The projection form is symmetric.** -/
theorem projectionOfDesign_transpose (D : WeightedDesign m k) :
    (projectionOfDesign D)ᵀ = projectionOfDesign D := by
  rw [projectionOfDesign, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- **(a) The projection form is idempotent** — this step, and only this step,
consumes Parseval. -/
theorem projectionOfDesign_mul_self (D : WeightedDesign m k) :
    projectionOfDesign D * projectionOfDesign D = projectionOfDesign D := by
  rw [projectionOfDesign, Matrix.mul_assoc, ← Matrix.mul_assoc (scaledAtomRows D)ᵀ,
    transpose_mul_scaledAtomRows, Matrix.one_mul]

/-- **(b) The diagonal of the projection form is the leverage score**
`P_cc = t_c · |g_c|²`. -/
theorem projectionOfDesign_diagonal (D : WeightedDesign m k) (atomIndex : Fin m) :
    projectionOfDesign D atomIndex atomIndex
      = D.weight atomIndex * leverageOf (D.atom atomIndex) := by
  rw [projectionOfDesign_apply, Real.mul_self_sqrt (D.weight_pos atomIndex).le, leverageOf,
    dotProduct_self_eq_sum_sq]

/-- **(c) The trace of the projection form is the rank.** -/
theorem trace_projectionOfDesign (D : WeightedDesign m k) :
    Matrix.trace (projectionOfDesign D) = (k : ℝ) := by
  rw [projectionOfDesign, Matrix.trace_mul_comm, transpose_mul_scaledAtomRows,
    Matrix.trace_one, Fintype.card_fin]

/-- The leverage scores sum to the rank — the trace identity, read off the
diagonal of the projection form. -/
theorem sum_weight_mul_leverage (D : WeightedDesign m k) :
    ∑ atomIndex, D.weight atomIndex * leverageOf (D.atom atomIndex) = (k : ℝ) := by
  rw [← trace_projectionOfDesign D, Matrix.trace]
  exact Finset.sum_congr rfl fun atomIndex _ =>
    (projectionOfDesign_diagonal D atomIndex).symm

/-! ## The positive-diagonal congruence -/

/-- The unscaled atoms selected along an index map, as the rows of a
`size × k` matrix. -/
def selectedAtomRows (D : WeightedDesign m k) {size : ℕ} (pick : Fin size → Fin m) :
    Matrix (Fin size) (Fin k) ℝ :=
  Matrix.of fun selectedIndex coord => D.atom (pick selectedIndex) coord

/-- The congruence basis: the positive diagonal of square-rooted selected weights. -/
noncomputable def sqrtWeightDiagonal (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) : Matrix (Fin size) (Fin size) ℝ :=
  Matrix.diagonal fun selectedIndex => Real.sqrt (D.weight (pick selectedIndex))

/-- The congruence basis is invertible: every square-rooted weight is positive. -/
theorem isUnit_det_sqrtWeightDiagonal (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) : IsUnit (sqrtWeightDiagonal D pick).det := by
  rw [sqrtWeightDiagonal, Matrix.det_diagonal, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun selectedIndex _ =>
    (Real.sqrt_pos.mpr (D.weight_pos (pick selectedIndex))).ne'

/-- The selected Gram gap `Gram − I` is symmetric. -/
theorem selectedGramGap_transpose (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) :
    (selectedAtomRows D pick * (selectedAtomRows D pick)ᵀ - 1)ᵀ
      = selectedAtomRows D pick * (selectedAtomRows D pick)ᵀ - 1 := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- **THE CONGRUENCE**, unconditional in the selection size:

    P_pick − diag t_pick  =  D^{1/2} (Gram_pick − I) D^{1/2},   D^{1/2} = diag √t_pick.

The congruence basis is a POSITIVE diagonal, so no inverse square root and no
matrix square root appears anywhere; the identity is entrywise arithmetic on
`√t_c √t_c = t_c`. -/
theorem projectionBlock_sub_weightDiagonal (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) :
    (projectionOfDesign D).submatrix pick pick
        - Matrix.diagonal (fun selectedIndex => D.weight (pick selectedIndex))
      = (sqrtWeightDiagonal D pick)ᵀ
          * (selectedAtomRows D pick * (selectedAtomRows D pick)ᵀ - 1)
          * sqrtWeightDiagonal D pick := by
  rw [sqrtWeightDiagonal, Matrix.diagonal_transpose]
  ext leftIndex rightIndex
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Matrix.mul_apply, Matrix.transpose_apply, selectedAtomRows, Matrix.of_apply]
  rw [projectionOfDesign_apply, dotProduct]
  rcases eq_or_ne leftIndex rightIndex with rfl | hne
  · rw [if_pos rfl, if_pos rfl]
    have hsquare := Real.mul_self_sqrt (D.weight_pos (pick leftIndex)).le
    have hexpand : ∑ coord, D.atom (pick leftIndex) coord * D.atom (pick leftIndex) coord
        = ∑ coord, D.atom (pick leftIndex) coord * D.atom (pick leftIndex) coord := rfl
    nlinarith [hsquare, hexpand]
  · rw [if_neg hne, if_neg hne]
    ring

/-- **The two decisions agree, at every selection size**: the selected Gram
dominates the identity iff the projection block dominates the weight diagonal.
Positive-diagonal congruence, both directions. -/
theorem posSemidef_projectionBlock_iff (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) :
    ((projectionOfDesign D).submatrix pick pick
        - Matrix.diagonal (fun selectedIndex => D.weight (pick selectedIndex))).PosSemidef
      ↔ (selectedAtomRows D pick * (selectedAtomRows D pick)ᵀ - 1).PosSemidef := by
  rw [projectionBlock_sub_weightDiagonal]
  exact (posSemidef_congr_right (selectedGramGap_transpose D pick)
    (isUnit_det_sqrtWeightDiagonal D pick)).symm

/-- **The minor-by-minor rescaling**: taking determinants in the congruence,
`det(P_S − diag t_S) = (∏_{c ∈ S} t_c) · det(Gram_S − I)`.  The factor is
strictly positive, so the two decision procedures agree principal minor by
principal minor — no eigenvalues, no pivoting, no genericity assumption. -/
theorem det_projectionBlock_sub_weightDiagonal (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) :
    ((projectionOfDesign D).submatrix pick pick
        - Matrix.diagonal (fun selectedIndex => D.weight (pick selectedIndex))).det
      = (∏ selectedIndex, D.weight (pick selectedIndex))
        * (selectedAtomRows D pick * (selectedAtomRows D pick)ᵀ - 1).det := by
  rw [projectionBlock_sub_weightDiagonal, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    sqrtWeightDiagonal, Matrix.det_diagonal]
  have hsqrtProductSquared :
      (∏ selectedIndex, Real.sqrt (D.weight (pick selectedIndex)))
        * (∏ selectedIndex, Real.sqrt (D.weight (pick selectedIndex)))
      = ∏ selectedIndex, D.weight (pick selectedIndex) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun selectedIndex _ =>
      Real.mul_self_sqrt (D.weight_pos (pick selectedIndex)).le
  rw [← hsqrtProductSquared]
  ring

/-! ## The headline: domination is a projection-block inequality -/

/-- The selected atom sum is the Gram's transpose product: `MᵀM = Σ_{c ∈ C} g_c g_cᵀ`. -/
theorem transpose_mul_selectedAtomRows (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) (hinj : Function.Injective pick) :
    (selectedAtomRows D pick)ᵀ * selectedAtomRows D pick
      = subsetSum D (Finset.image pick Finset.univ) := by
  rw [transpose_mul_self_eq_sum_rows, subsetSum,
    Finset.sum_image fun left _ right _ hlr => hinj hlr]
  rfl

/-- **THE HEADLINE.**  At selection size exactly the rank, domination of the
selected atoms is EXACTLY the Loewner inequality `P_C ⪰ diag t_C` on the
projection form.  Two steps: the positive-diagonal congruence
(`posSemidef_projectionBlock_iff`, any size) and the square transpose flip
(`posSemidef_transpose_mul_sub_one_comm`, which needs the selected-row matrix to
be square, i.e. needs the size to be `k`). -/
theorem dominates_iff_posSemidef_projectionBlock (D : WeightedDesign m k)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    Dominates D (Finset.image pick Finset.univ)
      ↔ ((projectionOfDesign D).submatrix pick pick
          - Matrix.diagonal (fun selectedIndex => D.weight (pick selectedIndex))).PosSemidef := by
  rw [posSemidef_projectionBlock_iff, Dominates, ← transpose_mul_selectedAtomRows D pick hinj]
  exact (posSemidef_transpose_mul_sub_one_comm (selectedAtomRows D pick)).symm.symm

/-- **The headline, indexed by the subset itself.**  For every `k`-subset `C`,
domination is the projection-block inequality read along `C`'s order embedding. -/
theorem dominates_iff_posSemidef_projectionBlock_finset (D : WeightedDesign m k)
    (selected : Finset (Fin m)) (hcard : selected.card = k) :
    Dominates D selected
      ↔ Matrix.PosSemidef
          ((projectionOfDesign D).submatrix (selected.orderEmbOfFin hcard)
              (selected.orderEmbOfFin hcard)
            - Matrix.diagonal
                (fun selectedIndex =>
                  D.weight (selected.orderEmbOfFin hcard selectedIndex))) := by
  have himage : Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  conv_lhs => rw [← himage]
  exact dominates_iff_posSemidef_projectionBlock D _
    (selected.orderEmbOfFin hcard).injective

/-! ## The uniform case: classical GTZ is `t ≡ 1/n` -/

/-- Positive scaling does not change positive semidefiniteness. -/
theorem posSemidef_smul_iff {size : ℕ} {form : Matrix (Fin size) (Fin size) ℝ} {scale : ℝ}
    (hscale : 0 < scale) : (scale • form).PosSemidef ↔ form.PosSemidef := by
  refine ⟨fun hpsd => ?_, fun hpsd => hpsd.smul hscale.le⟩
  have hback := hpsd.smul (inv_nonneg.mpr hscale.le)
  rwa [smul_smul, inv_mul_cancel₀ hscale.ne', one_smul] at hback

/-- **The scaled square transpose flip**: `MᵀM ⪰ c·I ⟺ MMᵀ ⪰ c·I` for square `M`
and `c > 0`.  Reduces to the unscaled flip by rescaling `M` by `√(1/c)`. -/
theorem posSemidef_transpose_mul_sub_smul_one_comm {size : ℕ}
    (square : Matrix (Fin size) (Fin size) ℝ) {scale : ℝ} (hscale : 0 < scale) :
    (squareᵀ * square - scale • 1).PosSemidef ↔ (square * squareᵀ - scale • 1).PosSemidef := by
  set rescale : ℝ := Real.sqrt scale⁻¹ with hrescale
  have hsq : rescale ^ 2 = scale⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hscale.le)
  have hshape : ∀ left right : Matrix (Fin size) (Fin size) ℝ,
      (rescale • left)ᵀ * (rescale • right) - 1
        = scale⁻¹ • (leftᵀ * right - scale • 1) := by
    intro left right
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      show rescale * rescale = scale⁻¹ from by rw [← pow_two]; exact hsq,
      smul_sub, smul_smul, inv_mul_cancel₀ hscale.ne', one_smul]
  have hleft : ((rescale • square)ᵀ * (rescale • square) - 1).PosSemidef
      ↔ (squareᵀ * square - scale • 1).PosSemidef := by
    rw [hshape square square]
    exact posSemidef_smul_iff (inv_pos.mpr hscale)
  have hright : ((rescale • square) * (rescale • square)ᵀ - 1).PosSemidef
      ↔ (square * squareᵀ - scale • 1).PosSemidef := by
    have hflip : (rescale • square) * (rescale • square)ᵀ - 1
        = scale⁻¹ • (square * squareᵀ - scale • 1) := by
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        show rescale * rescale = scale⁻¹ from by rw [← pow_two]; exact hsq,
        smul_sub, smul_smul, inv_mul_cancel₀ hscale.ne', one_smul]
    rw [hflip]
    exact posSemidef_smul_iff (inv_pos.mpr hscale)
  rw [← hleft, ← hright]
  exact posSemidef_transpose_mul_sub_one_comm (rescale • square)

/-- The classical statement in projection form, with the projection presented
intrinsically: every symmetric idempotent of trace `k` on `ℝ^n` has a `k`-subset
whose principal block dominates `(1/n)·I`. -/
def ProjectionCovering (n k : ℕ) : Prop :=
  ∀ projection : Matrix (Fin n) (Fin n) ℝ, projectionᵀ = projection →
    projection * projection = projection → Matrix.trace projection = (k : ℝ) →
      ∃ rowPick : Fin k → Fin n, Function.Injective rowPick ∧
        (projection.submatrix rowPick rowPick - (n : ℝ)⁻¹ • 1).PosSemidef

/-- The same statement with the projection presented as `A Aᵀ` for an
orthonormal-column `A`.  This is the form that is EQUIVALENT to classical GTZ. -/
def FrameProjectionCovering (n k : ℕ) : Prop :=
  ∀ frame : Matrix (Fin n) (Fin k) ℝ, frameᵀ * frame = 1 →
    ∃ rowPick : Fin k → Fin n, Function.Injective rowPick ∧
      ((frame * frameᵀ).submatrix rowPick rowPick - (n : ℝ)⁻¹ • 1).PosSemidef

/-- The principal block of `A Aᵀ` along a row pick is the selected block's own
`B Bᵀ`. -/
theorem submatrix_mul_transpose_eq {n : ℕ} (frame : Matrix (Fin n) (Fin k) ℝ)
    (rowPick : Fin k → Fin n) :
    (frame * frameᵀ).submatrix rowPick rowPick
      = (frame.submatrix rowPick id) * (frame.submatrix rowPick id)ᵀ := by
  ext leftIndex rightIndex
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, id]

/-- `A Aᵀ` is symmetric. -/
theorem mul_transpose_transpose {n : ℕ} (frame : Matrix (Fin n) (Fin k) ℝ) :
    (frame * frameᵀ)ᵀ = frame * frameᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- `A Aᵀ` is idempotent when `A` has orthonormal columns. -/
theorem mul_transpose_mul_self {n : ℕ} (frame : Matrix (Fin n) (Fin k) ℝ)
    (hortho : frameᵀ * frame = 1) :
    (frame * frameᵀ) * (frame * frameᵀ) = frame * frameᵀ := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc frameᵀ, hortho, Matrix.one_mul]

/-- `A Aᵀ` has trace `k` when `A` has orthonormal columns. -/
theorem trace_mul_transpose {n : ℕ} (frame : Matrix (Fin n) (Fin k) ℝ)
    (hortho : frameᵀ * frame = 1) : Matrix.trace (frame * frameᵀ) = (k : ℝ) := by
  rw [Matrix.trace_mul_comm, hortho, Matrix.trace_one, Fintype.card_fin]

/-- **Classical GTZ IS the frame projection covering statement** — a genuine iff.
The row block `B` is square, so `BᵀB ⪰ (1/n)·I` and `BBᵀ ⪰ (1/n)·I` are
interchangeable, and `BBᵀ` is exactly the principal block of `A Aᵀ`. -/
theorem gtzOriginal_iff_frameProjectionCovering (n : ℕ) (hn : 0 < n) :
    GtzOriginal n k ↔ FrameProjectionCovering n k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hstep : ∀ (frame : Matrix (Fin n) (Fin k) ℝ) (rowPick : Fin k → Fin n),
      ((frame.submatrix rowPick id)ᵀ * (frame.submatrix rowPick id)
          - (n : ℝ)⁻¹ • 1).PosSemidef
        ↔ ((frame * frameᵀ).submatrix rowPick rowPick - (n : ℝ)⁻¹ • 1).PosSemidef := by
    intro frame rowPick
    rw [submatrix_mul_transpose_eq]
    exact posSemidef_transpose_mul_sub_smul_one_comm (frame.submatrix rowPick id)
      (inv_pos.mpr hnR)
  constructor
  · intro horiginal frame hortho
    obtain ⟨rowPick, hinj, hpsd⟩ := horiginal frame hortho
    exact ⟨rowPick, hinj, (hstep frame rowPick).mp hpsd⟩
  · intro hcover frame hortho
    obtain ⟨rowPick, hinj, hpsd⟩ := hcover frame hortho
    exact ⟨rowPick, hinj, (hstep frame rowPick).mpr hpsd⟩

/-- **The intrinsic projection form implies classical GTZ.**  One direction only:
`A ↦ A Aᵀ` lands inside the symmetric idempotents of trace `k`, but its
surjectivity onto them is the spectral factorization this repo does not have. -/
theorem gtzOriginal_of_projectionCovering (n : ℕ) (hn : 0 < n)
    (hcover : ProjectionCovering n k) : GtzOriginal n k := by
  refine (gtzOriginal_iff_frameProjectionCovering n hn).mpr fun frame hortho => ?_
  exact hcover (frame * frameᵀ) (mul_transpose_transpose frame)
    (mul_transpose_mul_self frame hortho) (trace_mul_transpose frame hortho)

/-- The projection form of the uniform row design of an orthonormal-column matrix
is `A Aᵀ` — the `√n` in the atoms and the `1/n` in the weights cancel exactly.
So the classical statement is the `t ≡ 1/n` slice of the projection form, with no
residual scaling. -/
theorem projectionOfDesign_rowDesign {n : ℕ} (hn : 0 < n) (frame : Matrix (Fin n) (Fin k) ℝ)
    (hortho : frameᵀ * frame = 1) :
    projectionOfDesign (rowDesign hn frame hortho) = frame * frameᵀ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrows : scaledAtomRows (rowDesign hn frame hortho) = frame := by
    ext atomIndex coord
    show Real.sqrt ((n : ℝ)⁻¹) * (Real.sqrt (n : ℝ) • frame atomIndex) coord
      = frame atomIndex coord
    rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Real.sqrt_mul (inv_nonneg.mpr hnR.le),
      inv_mul_cancel₀ hnR.ne', Real.sqrt_one, one_mul]
  rw [projectionOfDesign, hrows]

/-- **Weighted GTZ at size `n` gives the frame projection covering statement at
`(n, k)`** — the uniform case of the reformulation, routed through the repo's
weighted ⟹ original bridge. -/
theorem frameProjectionCovering_of_gtzWeighted {n : ℕ} (hn : 0 < n)
    (hweighted : GtzWeighted n k) : FrameProjectionCovering n k :=
  (gtzOriginal_iff_frameProjectionCovering n hn).mp
    (original_of_weighted_single hweighted hn)

/-! ## Volume sampling: the principal minors of a projection are binomial -/

/-- The Weinstein–Aronszajn identity in frame form, over any commutative ring:
`det(1 + y·A Aᵀ) = (1 + y)^k` when `AᵀA = I_k`. -/
theorem det_one_add_smul_mul_transpose {Ring : Type*} [CommRing Ring] {rows cols : ℕ}
    (frame : Matrix (Fin rows) (Fin cols) Ring) (hortho : frameᵀ * frame = 1) (scalar : Ring) :
    (1 + scalar • (frame * frameᵀ)).det = (1 + scalar) ^ cols := by
  rw [show scalar • (frame * frameᵀ) = (scalar • frame) * frameᵀ from
      (Matrix.smul_mul scalar frame frameᵀ).symm,
    Matrix.det_one_add_mul_comm, Matrix.mul_smul, hortho, ← one_smul Ring
      (1 : Matrix (Fin cols) (Fin cols) Ring), smul_smul, mul_one, ← add_smul, Matrix.det_smul,
    Matrix.det_one, mul_one, Fintype.card_fin]

/-- Mapping the scaled frame into `ℝ[X]` preserves orthonormality of columns. -/
theorem transpose_mul_scaledAtomRows_map (D : WeightedDesign m k) :
    ((scaledAtomRows D).map Polynomial.C)ᵀ * ((scaledAtomRows D).map Polynomial.C) = 1 := by
  rw [← Matrix.transpose_map, ← Matrix.map_mul (f := (Polynomial.C : ℝ →+* Polynomial ℝ)),
    transpose_mul_scaledAtomRows]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- The projection form, mapped into `ℝ[X]`, is still a frame square. -/
theorem projectionOfDesign_map (D : WeightedDesign m k) :
    (projectionOfDesign D).map Polynomial.C
      = ((scaledAtomRows D).map Polynomial.C) * ((scaledAtomRows D).map Polynomial.C)ᵀ := by
  rw [projectionOfDesign, Matrix.map_mul (f := (Polynomial.C : ℝ →+* Polynomial ℝ)),
    Matrix.transpose_map]

/-- **The minor generating function of a design's projection**:
`det(1 + X·P) = (1 + X)^k` in `ℝ[X]`. -/
theorem det_one_add_X_smul_projectionOfDesign (D : WeightedDesign m k) :
    (1 + (Polynomial.X : Polynomial ℝ) • (projectionOfDesign D).map Polynomial.C).det
      = (1 + Polynomial.X) ^ k := by
  rw [projectionOfDesign_map]
  exact det_one_add_smul_mul_transpose ((scaledAtomRows D).map Polynomial.C)
    (transpose_mul_scaledAtomRows_map D) Polynomial.X

/-- **VOLUME SAMPLING.**  The sum of the `size × size` principal minors of a
design's projection form is `C(k, size)`; at `size = k` it is `1`, which is the
statement that the `k`-subset determinants `det(P_T)` form a probability measure
on `k`-subsets (whose marginals are the leverage scores, by
`projectionOfDesign_diagonal`). -/
theorem sum_det_projectionMinors (D : WeightedDesign m k) (size : ℕ) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard size,
        ((projectionOfDesign D).submatrix (Subtype.val : { c // c ∈ selected } → Fin m)
          (Subtype.val : { c // c ∈ selected } → Fin m)).det
      = (k.choose size : ℝ) := by
  rw [← Matrix.coeff_det_one_add_X_smul_eq_sum_minors (projectionOfDesign D) size,
    det_one_add_X_smul_projectionOfDesign, Polynomial.coeff_one_add_X_pow]

/-- The `k`-subset determinants of the projection form sum to one. -/
theorem sum_det_projectionMinors_rank (D : WeightedDesign m k) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        ((projectionOfDesign D).submatrix (Subtype.val : { c // c ∈ selected } → Fin m)
          (Subtype.val : { c // c ∈ selected } → Fin m)).det
      = 1 := by
  rw [sum_det_projectionMinors D k, Nat.choose_self, Nat.cast_one]

/-! ## The averaging aggregate at a uniform weight -/

/-- The scalar-shifted determinant of a projection form, for every shift and
every real scalar off the single degenerate value: `det(1 + y(P − s·I)) =
(1 − sy)^{m−k}(1 + (1−s)y)^k`.  Note the exponent split is the only place the
rank enters. -/
theorem det_one_add_smul_shifted_real (D : WeightedDesign m k) (shift scalar : ℝ)
    (hbase : 1 - shift * scalar ≠ 0) :
    (1 + scalar • (projectionOfDesign D - shift • 1)).det
      = (1 - shift * scalar) ^ (m - k) * (1 + (1 - shift) * scalar) ^ k := by
  have hrank : k ≤ m := rank_le_of_design D
  set base : ℝ := 1 - shift * scalar with hbasedef
  -- Sylvester: the m-sided determinant of a shifted projection is a k-sided one.
  have hsylvester : ∀ coefficient : ℝ,
      ((1 : Matrix (Fin m) (Fin m) ℝ) + coefficient • projectionOfDesign D).det
        = (1 + coefficient) ^ k := by
    intro coefficient
    have hsplit : (coefficient • projectionOfDesign D)
        = (coefficient • scaledAtomRows D) * (scaledAtomRows D)ᵀ := by
      rw [projectionOfDesign, Matrix.smul_mul]
    rw [hsplit, Matrix.det_one_add_mul_comm, Matrix.mul_smul,
      transpose_mul_scaledAtomRows,
      show (1 : Matrix (Fin k) (Fin k) ℝ) + coefficient • 1 = (1 + coefficient) • 1 from by
        rw [add_smul, one_smul],
      Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hfactor : (1 : Matrix (Fin m) (Fin m) ℝ) + scalar • (projectionOfDesign D - shift • 1)
      = base • (1 + (scalar / base) • projectionOfDesign D) := by
    rw [smul_add, smul_smul, mul_div_cancel₀ scalar hbase, smul_sub, smul_smul,
      Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal, hbasedef,
      mul_comm scalar shift]
    ext rowIndex colIndex
    by_cases hdiag : rowIndex = colIndex
    · subst hdiag
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_apply_eq,
        Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul]
      ring
    · simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hdiag,
        Matrix.one_apply_ne hdiag, Matrix.smul_apply, smul_eq_mul]
      ring
  rw [hfactor, Matrix.det_smul, Fintype.card_fin, hsylvester (scalar / base)]
  have hbasePow : base ^ m = base ^ (m - k) * base ^ k := by
    rw [← pow_add]; congr 1; omega
  rw [hbasePow]
  have hcollapse : base ^ k * (1 + scalar / base) ^ k = (base + scalar) ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  rw [mul_assoc, hcollapse]
  have hshiftIdentity : base + scalar = 1 + (1 - shift) * scalar := by
    show (1 - shift * scalar) + scalar = 1 + (1 - shift) * scalar
    ring
  rw [hshiftIdentity]

/-! ## The four-cycle: the unique series-parallel class at `m = k + 1` -/

end Gtz
