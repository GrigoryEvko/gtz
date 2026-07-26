/-
# The projection chart, field-generically: A1, A2 and the inertia no-go

Let `V` be the `size × rank` matrix whose row `c` is `√t_c · conj(g_c)`.  Parseval
says exactly `Vᴴ V = 1`, so `P := V Vᴴ` is a Hermitian idempotent on the INDEX
space with `trace P = rank` and `P_cc = t_c · |g_c|²`.  Writing `D = diag t` and
`W = P - D`:

  * **A1** `FieldDominates design C ⟺ W[C] ⪰ 0` (at `|C| = rank`).
  * **A2** `W` is positive definite on `range P` and negative definite on `ker P`
    — the two Rayleigh statements, NOT an eigenvalue count.
  * **A3** the no-go: the bare inertia of `W` does not decide anything; a real
    symmetric matrix of inertia `(k, m-k, 0)` can have NO positive semidefinite
    principal submatrix at all.  So the `P - D` structure is load-bearing, and no
    proof of GTZ can run on inertia alone.

**PROVENANCE — what is imported, what is re-derived, and the agreement.**
Over ℝ the chart is already shipped, rank-generically, in
`Gtz/LinAlg/ProjectionForm.lean`: `Gtz.scaledAtomRows`,
`Gtz.projectionOfDesign`, `Gtz.projectionOfDesign_transpose`,
`Gtz.projectionOfDesign_mul_self`, `Gtz.projectionOfDesign_diagonal`,
`Gtz.trace_projectionOfDesign`, `Gtz.projectionBlock_sub_weightDiagonal`
(the congruence, at ANY selection size), `Gtz.posSemidef_projectionBlock_iff`,
`Gtz.det_projectionBlock_sub_weightDiagonal` and
`Gtz.dominates_iff_posSemidef_projectionBlock{,_finset}`.  That file is imported
here, NOT duplicated, and the agreement is proved:
`scaledFrame_eq_scaledAtomRows`, `projectionChart_eq_projectionOfDesign`,
`chartGap_eq_projectionBlockGap` and `fieldDominates_iff_dominates` pin the
generic construction to the real one on the nose.

What IS re-derived is the `ᴴ`-shaped copy over an arbitrary `RCLike` field,
because nothing complex existed: `Gtz/Complex/` has no chart.  (Its
`Gtz.indexShadow`, `Gtz/Complex/PerRankConstantLedger.lean`, is `A · (Aᴴ · diag t)`
— NOT Hermitian, used for minors and volumes; it is not the chart and must not
be mistaken for one.)

A separate note on duplication INSIDE the real layer, reported not repaired.
There are THREE rank-three specialisations of the rank-generic `ProjectionForm`
layer, and a consumer of chart facts should import `Gtz.LinAlg.ProjectionForm`
rather than any of them:

  * `Gtz/Quantitative/SpreadCertificateSixThree.lean` — `chartFrame`,
    `chartMatrix`, `chartFrame_transpose_mul_self`, `chartMatrix_isIdempotent`,
    `chartMatrix_isSymm`, `chartMatrix_trace`;
  * `Gtz/Quantitative/ProjectionChartLegs.lean` — `chartBasis`, `chartEntry`,
    `chartEntry_self` (the diagonal law `P_cc = t_c |g_c|²`), and a chart-GAP
    layer of its own: `chartGapDiagonal`, `chartGapDiagonal_eq`,
    `chartGapMatrix_eq`, `chartGapDeterminant`, `chartGapWeightedMinorSum`.
    This is the copy nearest to the material below and the one most likely to be
    re-derived by accident;
  * `Gtz/Complex/PerRankConstantLedger.lean` — `conjugateAtomRows`,
    `weightDiagonal`, `indexShadow`.  `indexShadow` is `A · (Aᴴ · diag t)`, which
    is NOT Hermitian; it is a minor/volume device, not the chart.

None of those names collides with anything below; the defect they constitute is
duplication, not ambiguity.

**THE A2 CORRECTION.**  A2 is stated in the campaign brief unconditionally.  It
is FALSE unconditionally, at exactly one shape: at `size = rank = 1` the only
design has `t = 1` and `|g|² = 1`, so `P = 1`, `D = 1`, `W = 0` and the Rayleigh
form vanishes on the range instead of being positive.  Every statement below
carries `2 ≤ size`, and the failure is shipped as a theorem
(`degenerateSingleton_chartGap_eq_zero`) so the hypothesis cannot be dropped by
accident.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Field.WeightedDesign
import Gtz.LinAlg.ProjectionForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix
open scoped ComplexOrder

variable {Scalar : Type*} [RCLike Scalar]

/-! ## The Stiefel factor and the chart -/

/-- The scaled frame `V`: row `c` is `√t_c · conj(g_c)`.  This is the shape that
makes Parseval read `Vᴴ V = 1`. -/
noncomputable def scaledFrame {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) : Matrix (Fin size) (Fin rank) Scalar :=
  Matrix.of fun atomIndex coordinate =>
    ((Real.sqrt (design.weight atomIndex) : ℝ) : Scalar)
      * star (design.atom atomIndex coordinate)

/-- **Parseval IS orthonormality of the scaled frame's columns.**  This step, and
only this step, consumes the design axiom. -/
theorem conjTranspose_mul_scaledFrame {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) :
    (scaledFrame design)ᴴ * scaledFrame design = 1 := by
  have hparseval := design.isParseval
  ext rowIndex colIndex
  have hentry : ((scaledFrame design)ᴴ * scaledFrame design) rowIndex colIndex
      = ∑ atomIndex, ((design.weight atomIndex : ℝ) : Scalar)
          * (design.atom atomIndex rowIndex * star (design.atom atomIndex colIndex)) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, scaledFrame, Matrix.of_apply,
      map_mul, RCLike.star_def, RCLike.conj_ofReal, RCLike.conj_conj]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    have hsquare : ((Real.sqrt (design.weight atomIndex) : ℝ) : Scalar)
          * ((Real.sqrt (design.weight atomIndex) : ℝ) : Scalar)
        = ((design.weight atomIndex : ℝ) : Scalar) := by
      rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (design.weight_pos atomIndex).le]
    linear_combination (design.atom atomIndex rowIndex
      * (starRingEnd Scalar) (design.atom atomIndex colIndex)) * hsquare
  rw [hentry]
  have hsumEntry := congrFun (congrFun hparseval rowIndex) colIndex
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, fieldAtom,
    Matrix.vecMulVec_apply, Pi.star_apply] at hsumEntry
  exact hsumEntry

/-- The Hermitian projection chart `P = V Vᴴ` on the index space. -/
noncomputable def projectionChart {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) : Matrix (Fin size) (Fin size) Scalar :=
  scaledFrame design * (scaledFrame design)ᴴ

/-- `P_cd = √t_c √t_d ⟨g_c, g_d⟩`.  No matrix square root and no matrix inverse
appears: the congruence basis below is a POSITIVE diagonal. -/
theorem projectionChart_apply {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (rowIndex colIndex : Fin size) :
    projectionChart design rowIndex colIndex
      = ((Real.sqrt (design.weight rowIndex) : ℝ) : Scalar)
        * ((Real.sqrt (design.weight colIndex) : ℝ) : Scalar)
        * (star (design.atom rowIndex) ⬝ᵥ design.atom colIndex) := by
  simp only [projectionChart, scaledFrame, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, dotProduct, Pi.star_apply, Finset.mul_sum, map_mul, RCLike.star_def,
    RCLike.conj_ofReal, RCLike.conj_conj]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The chart is Hermitian.** -/
theorem projectionChart_conjTranspose {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) :
    (projectionChart design)ᴴ = projectionChart design := by
  rw [projectionChart, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem projectionChart_isHermitian {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) :
    (projectionChart design).IsHermitian :=
  projectionChart_conjTranspose design

/-- **The chart is idempotent** — this step, and only this step, consumes
Parseval. -/
theorem projectionChart_mul_self {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) :
    projectionChart design * projectionChart design = projectionChart design := by
  rw [projectionChart, Matrix.mul_assoc, ← Matrix.mul_assoc (scaledFrame design)ᴴ,
    conjTranspose_mul_scaledFrame, Matrix.one_mul]

/-- The chart is a projector on vectors: `P (P y) = P y`. -/
theorem projectionChart_mulVec_mulVec {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (vector : Fin size → Scalar) :
    projectionChart design *ᵥ (projectionChart design *ᵥ vector)
      = projectionChart design *ᵥ vector := by
  rw [Matrix.mulVec_mulVec, projectionChart_mul_self]

/-- **The diagonal of the chart is the weighted leverage**: `P_cc = t_c · |g_c|²`. -/
theorem projectionChart_diagonal {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (atomIndex : Fin size) :
    projectionChart design atomIndex atomIndex
      = ((design.weight atomIndex * fieldLeverageOf (design.atom atomIndex) : ℝ) : Scalar) := by
  rw [projectionChart_apply, dotProduct_star_self_eq_fieldLeverage, ← RCLike.ofReal_mul,
    ← RCLike.ofReal_mul, Real.mul_self_sqrt (design.weight_pos atomIndex).le]

/-- **The trace of the chart is the rank.** -/
theorem trace_projectionChart {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) :
    Matrix.trace (projectionChart design) = ((rank : ℝ) : Scalar) := by
  rw [projectionChart, Matrix.trace_mul_comm, conjTranspose_mul_scaledFrame,
    Matrix.trace_one, Fintype.card_fin]
  norm_cast

/-! ## Provenance: the generic chart agrees with the shipped real chart -/

/-- A real `Gtz.WeightedDesign` read as a field-generic design at `Scalar = ℝ`.
Every structure field is accepted as-is, because `fieldAtom` over ℝ is
definitionally `Gtz.atomMatrix`. -/
def ofRealDesign {size rank : ℕ} (design : WeightedDesign size rank) :
    FieldWeightedDesign ℝ size rank where
  atom := design.atom
  weight := design.weight
  weight_pos := design.weight_pos
  weight_sum_one := design.weight_sum_one
  isParseval := design.isParseval

theorem scaledFrame_eq_scaledAtomRows {size rank : ℕ} (design : WeightedDesign size rank) :
    scaledFrame (ofRealDesign design) = scaledAtomRows design := rfl

/-- **The agreement theorem**: over ℝ the generic chart IS the shipped
`Gtz.projectionOfDesign`.  Nothing above re-derives a real fact; the real facts
in `Gtz/LinAlg/ProjectionForm.lean` transport through this equality. -/
theorem projectionChart_eq_projectionOfDesign {size rank : ℕ}
    (design : WeightedDesign size rank) :
    projectionChart (ofRealDesign design) = projectionOfDesign design := by
  rw [projectionChart, projectionOfDesign, scaledFrame_eq_scaledAtomRows]
  congr 1

theorem fieldSubsetSum_eq_subsetSum {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    fieldSubsetSum (ofRealDesign design) selected = subsetSum design selected := rfl

theorem fieldDominates_iff_dominates {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    FieldDominates (ofRealDesign design) selected ↔ Dominates design selected := Iff.rfl

/-! ## The positive-diagonal congruence and A1 -/

/-- The selected atoms, CONJUGATED, as the rows of a `selectionSize × rank`
matrix.  The conjugation is what makes `rowsᴴ * rows` the unweighted atom sum. -/
def selectedFieldRows {size rank : ℕ} (design : FieldWeightedDesign Scalar size rank)
    {selectionSize : ℕ} (pick : Fin selectionSize → Fin size) :
    Matrix (Fin selectionSize) (Fin rank) Scalar :=
  Matrix.of fun selectedIndex coordinate => star (design.atom (pick selectedIndex) coordinate)

/-- The congruence basis: the positive diagonal of square-rooted selected
weights.  No inverse square root anywhere. -/
noncomputable def sqrtWeightDiagonalField {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) {selectionSize : ℕ}
    (pick : Fin selectionSize → Fin size) :
    Matrix (Fin selectionSize) (Fin selectionSize) Scalar :=
  Matrix.diagonal fun selectedIndex =>
    ((Real.sqrt (design.weight (pick selectedIndex)) : ℝ) : Scalar)

theorem sqrtWeightDiagonalField_conjTranspose {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) {selectionSize : ℕ}
    (pick : Fin selectionSize → Fin size) :
    (sqrtWeightDiagonalField design pick)ᴴ = sqrtWeightDiagonalField design pick := by
  ext leftIndex rightIndex
  rcases eq_or_ne leftIndex rightIndex with rfl | hne
  · simp only [sqrtWeightDiagonalField, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq,
      RCLike.star_def, RCLike.conj_ofReal]
  · simp only [sqrtWeightDiagonalField, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply_ne _ (Ne.symm hne), Matrix.diagonal_apply_ne _ hne, star_zero]

theorem isUnit_sqrtWeightDiagonalField {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) {selectionSize : ℕ}
    (pick : Fin selectionSize → Fin size) :
    IsUnit (sqrtWeightDiagonalField design pick) := by
  refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
  rw [sqrtWeightDiagonalField, Matrix.det_diagonal, isUnit_iff_ne_zero]
  refine Finset.prod_ne_zero_iff.mpr fun selectedIndex _ => ?_
  exact RCLike.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (design.weight_pos (pick selectedIndex))).ne'

/-- The selected conjugated rows recover the unweighted atom sum. -/
theorem conjTranspose_mul_selectedFieldRows {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) {selectionSize : ℕ}
    (pick : Fin selectionSize → Fin size) (hinjective : Function.Injective pick) :
    (selectedFieldRows design pick)ᴴ * selectedFieldRows design pick
      = fieldSubsetSum design (Finset.image pick Finset.univ) := by
  classical
  have himage : fieldSubsetSum design (Finset.image pick Finset.univ)
      = ∑ selectedIndex, fieldAtom (design.atom (pick selectedIndex)) := by
    rw [fieldSubsetSum]
    exact Finset.sum_image fun left _ right _ hlr => hinjective hlr
  rw [himage]
  ext rowIndex colIndex
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, selectedFieldRows, Matrix.of_apply,
    Matrix.sum_apply, fieldAtom, Matrix.vecMulVec_apply, Pi.star_apply, star_star]

/-- **THE CONGRUENCE**, unconditional in the selection size:

    P[C] − diag t_C  =  diag(√t_C) (Gram_C − 1) diag(√t_C).

The basis is a POSITIVE diagonal, so the identity is entrywise arithmetic on
`√t_c √t_c = t_c`.  This is the field-generic
`Gtz.projectionBlock_sub_weightDiagonal`. -/
theorem chartBlock_sub_weightDiagonal {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) {selectionSize : ℕ}
    (pick : Fin selectionSize → Fin size) :
    (projectionChart design).submatrix pick pick
        - Matrix.diagonal (fun selectedIndex =>
            ((design.weight (pick selectedIndex) : ℝ) : Scalar))
      = (sqrtWeightDiagonalField design pick)ᴴ
          * (selectedFieldRows design pick * (selectedFieldRows design pick)ᴴ - 1)
          * sqrtWeightDiagonalField design pick := by
  rw [sqrtWeightDiagonalField_conjTranspose, sqrtWeightDiagonalField]
  ext leftIndex rightIndex
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, selectedFieldRows, Matrix.of_apply,
    star_star]
  rw [projectionChart_apply]
  simp only [dotProduct, Pi.star_apply]
  rcases eq_or_ne leftIndex rightIndex with rfl | hne
  · rw [if_pos rfl, if_pos rfl]
    have hsquare : ((Real.sqrt (design.weight (pick leftIndex)) : ℝ) : Scalar)
          * ((Real.sqrt (design.weight (pick leftIndex)) : ℝ) : Scalar)
        = ((design.weight (pick leftIndex) : ℝ) : Scalar) := by
      rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (design.weight_pos (pick leftIndex)).le]
    linear_combination hsquare
  · rw [if_neg hne, if_neg hne]
    ring

/-- **The two decisions agree at every selection size**: the selected Gram
dominates the identity iff the chart block dominates the weight diagonal. -/
theorem posSemidef_chartBlock_iff {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) {selectionSize : ℕ}
    (pick : Fin selectionSize → Fin size) :
    ((projectionChart design).submatrix pick pick
        - Matrix.diagonal (fun selectedIndex =>
            ((design.weight (pick selectedIndex) : ℝ) : Scalar))).PosSemidef
      ↔ (selectedFieldRows design pick * (selectedFieldRows design pick)ᴴ - 1).PosSemidef := by
  rw [chartBlock_sub_weightDiagonal]
  exact posSemidef_congr_conjTranspose (isUnit_sqrtWeightDiagonalField design pick)

/-- **A1.**  At selection size exactly the rank, domination of the selected atoms
is EXACTLY the Loewner inequality `P[C] ⪰ diag t_C` on the chart.  Two steps: the
positive-diagonal congruence (any size) and the square expansion flip (which
needs the selected-row matrix to be square, i.e. needs the size to be the rank).

Division-free: every ingredient is a positive diagonal or a product; no inverse,
no matrix square root, no eigenvalue. -/
theorem fieldDominates_iff_posSemidef_chartBlock {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick) :
    FieldDominates design (Finset.image pick Finset.univ)
      ↔ ((projectionChart design).submatrix pick pick
          - Matrix.diagonal (fun selectedIndex =>
              ((design.weight (pick selectedIndex) : ℝ) : Scalar))).PosSemidef := by
  rw [posSemidef_chartBlock_iff, FieldDominates,
    ← conjTranspose_mul_selectedFieldRows design pick hinjective]
  exact posSemidef_conjTranspose_mul_sub_one_comm (selectedFieldRows design pick)

/-- **A1, indexed by the subset itself.**  For every `rank`-subset, domination is
the chart-block inequality read along the subset's order embedding. -/
theorem fieldDominates_iff_posSemidef_chartBlock_finset {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (selected : Finset (Fin size))
    (hcard : selected.card = rank) :
    FieldDominates design selected
      ↔ Matrix.PosSemidef
          ((projectionChart design).submatrix (selected.orderEmbOfFin hcard)
              (selected.orderEmbOfFin hcard)
            - Matrix.diagonal (fun selectedIndex =>
                ((design.weight (selected.orderEmbOfFin hcard selectedIndex) : ℝ) : Scalar))) := by
  have himage : Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  conv_lhs => rw [← himage]
  exact fieldDominates_iff_posSemidef_chartBlock design _
    (selected.orderEmbOfFin hcard).injective

/-! ## A2: the two Rayleigh statements

`W = P - D`.  A2 says `W` is positive definite on `range P` and negative definite
on `ker P`.  Stated as the two quadratic-form inequalities, not as an inertia
triple — the inertia triple is exactly what A3 shows carries no information. -/

/-- The chart gap `W = P − diag t`. -/
noncomputable def chartGap {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) : Matrix (Fin size) (Fin size) Scalar :=
  projectionChart design
    - Matrix.diagonal (fun atomIndex => ((design.weight atomIndex : ℝ) : Scalar))

/-- The gap read along a selection is the selection's block of the gap — so A1's
`P[C] − diag t_C` and `W[C]` are the same matrix, and A1 has exactly ONE
non-trivial implication, not three. -/
theorem chartGap_submatrix {size rank : ℕ} (design : FieldWeightedDesign Scalar size rank)
    {selectionSize : ℕ} (pick : Fin selectionSize → Fin size)
    (hinjective : Function.Injective pick) :
    (chartGap design).submatrix pick pick
      = (projectionChart design).submatrix pick pick
        - Matrix.diagonal (fun selectedIndex =>
            ((design.weight (pick selectedIndex) : ℝ) : Scalar)) := by
  ext leftIndex rightIndex
  simp only [chartGap, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.diagonal_apply]
  rcases eq_or_ne leftIndex rightIndex with rfl | hne
  · rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hne, if_neg (fun heq => hne (hinjective heq))]

/-- Over ℝ the generic gap is the shipped real projection-block gap. -/
theorem chartGap_eq_projectionBlockGap {size rank : ℕ} (design : WeightedDesign size rank) :
    chartGap (ofRealDesign design)
      = projectionOfDesign design
        - Matrix.diagonal (fun atomIndex => design.weight atomIndex) := by
  rw [chartGap, projectionChart_eq_projectionOfDesign]
  rfl

/-- The Rayleigh quotient of the gap, as a real number. -/
noncomputable def chartGapRayleigh {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (vector : Fin size → Scalar) : ℝ :=
  RCLike.re (star vector ⬝ᵥ (chartGap design *ᵥ vector))

/-- The weight-diagonal part of the Rayleigh quotient is `Σ_c t_c |u_c|²`. -/
theorem re_dotProduct_weightDiagonal_mulVec {size : ℕ} (weight : Fin size → ℝ)
    (vector : Fin size → Scalar) :
    RCLike.re (star vector
        ⬝ᵥ ((Matrix.diagonal (fun atomIndex => ((weight atomIndex : ℝ) : Scalar))) *ᵥ vector))
      = ∑ atomIndex, weight atomIndex * ‖vector atomIndex‖ ^ 2 := by
  have hshape : star vector
      ⬝ᵥ ((Matrix.diagonal (fun atomIndex => ((weight atomIndex : ℝ) : Scalar))) *ᵥ vector)
      = ((∑ atomIndex, weight atomIndex * ‖vector atomIndex‖ ^ 2 : ℝ) : Scalar) := by
    rw [dotProduct, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [Pi.star_apply, Matrix.mulVec_diagonal, RCLike.ofReal_mul]
    have hconj : star (vector atomIndex) * vector atomIndex
        = ((‖vector atomIndex‖ ^ 2 : ℝ) : Scalar) := by
      rw [RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]
    calc star (vector atomIndex) * (((weight atomIndex : ℝ) : Scalar) * vector atomIndex)
        = ((weight atomIndex : ℝ) : Scalar) * (star (vector atomIndex) * vector atomIndex) := by
          ring
      _ = ((weight atomIndex : ℝ) : Scalar) * ((‖vector atomIndex‖ ^ 2 : ℝ) : Scalar) := by
          rw [hconj]
  rw [hshape, RCLike.ofReal_re]

/-- The chart part of the Rayleigh quotient on a fixed vector of the projector is
`Σ_c |u_c|²`. -/
theorem re_dotProduct_projectionChart_mulVec_of_fixed {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) {vector : Fin size → Scalar}
    (hfixed : projectionChart design *ᵥ vector = vector) :
    RCLike.re (star vector ⬝ᵥ (projectionChart design *ᵥ vector))
      = ∑ atomIndex, ‖vector atomIndex‖ ^ 2 := by
  rw [hfixed, dotProduct_star_self_eq_fieldLeverage, RCLike.ofReal_re, fieldLeverageOf]

/-- **A2, the range half.**  On a fixed vector of the projector the gap's Rayleigh
quotient is `Σ_c (1 - t_c)|u_c|²`, hence STRICTLY positive for `u ≠ 0` once there
are at least two atoms.  The hypothesis `2 ≤ size` is load-bearing — see
`degenerateSingleton_chartGap_eq_zero`. -/
theorem chartGapRayleigh_eq_of_fixed {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) {vector : Fin size → Scalar}
    (hfixed : projectionChart design *ᵥ vector = vector) :
    chartGapRayleigh design vector
      = ∑ atomIndex, (1 - design.weight atomIndex) * ‖vector atomIndex‖ ^ 2 := by
  rw [chartGapRayleigh, chartGap, Matrix.sub_mulVec, dotProduct_sub, map_sub,
    re_dotProduct_projectionChart_mulVec_of_fixed design hfixed,
    re_dotProduct_weightDiagonal_mulVec, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun atomIndex _ => by ring

theorem chartGapRayleigh_pos_of_fixed {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (hsize : 2 ≤ size)
    {vector : Fin size → Scalar} (hfixed : projectionChart design *ᵥ vector = vector)
    (hnonzero : vector ≠ 0) : 0 < chartGapRayleigh design vector := by
  classical
  obtain ⟨witness, hwitness⟩ : ∃ witness, vector witness ≠ 0 := by
    rcases Function.ne_iff.mp hnonzero with ⟨witness, hne⟩
    exact ⟨witness, by simpa using hne⟩
  rw [chartGapRayleigh_eq_of_fixed design hfixed]
  refine Finset.sum_pos' (fun atomIndex _ => ?_) ⟨witness, Finset.mem_univ witness, ?_⟩
  · exact mul_nonneg (by linarith [fieldWeight_le_one design atomIndex]) (sq_nonneg _)
  · refine mul_pos (by linarith [fieldWeight_lt_one design hsize witness]) ?_
    exact pow_pos (norm_pos_iff.mpr hwitness) 2

/-- **A2, the kernel half.**  On a vector killed by the projector the gap's
Rayleigh quotient is `−Σ_c t_c |u_c|²`, hence STRICTLY negative for `u ≠ 0`.  No
size hypothesis is needed here: the weights are positive by definition. -/
theorem chartGapRayleigh_eq_of_killed {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) {vector : Fin size → Scalar}
    (hkilled : projectionChart design *ᵥ vector = 0) :
    chartGapRayleigh design vector
      = -∑ atomIndex, design.weight atomIndex * ‖vector atomIndex‖ ^ 2 := by
  rw [chartGapRayleigh, chartGap, Matrix.sub_mulVec, dotProduct_sub, map_sub, hkilled,
    dotProduct_zero, map_zero, re_dotProduct_weightDiagonal_mulVec, zero_sub]

theorem chartGapRayleigh_neg_of_killed {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) {vector : Fin size → Scalar}
    (hkilled : projectionChart design *ᵥ vector = 0) (hnonzero : vector ≠ 0) :
    chartGapRayleigh design vector < 0 := by
  classical
  obtain ⟨witness, hwitness⟩ : ∃ witness, vector witness ≠ 0 := by
    rcases Function.ne_iff.mp hnonzero with ⟨witness, hne⟩
    exact ⟨witness, by simpa using hne⟩
  rw [chartGapRayleigh_eq_of_killed design hkilled, neg_lt, neg_zero]
  refine Finset.sum_pos' (fun atomIndex _ => ?_) ⟨witness, Finset.mem_univ witness, ?_⟩
  · exact mul_nonneg (design.weight_pos atomIndex).le (sq_nonneg _)
  · exact mul_pos (design.weight_pos witness) (pow_pos (norm_pos_iff.mpr hwitness) 2)

/-! ### The A2 edge case, shipped so the hypothesis cannot be dropped -/

/-- The unique `(1,1)` design: one atom of unit length carrying all the weight. -/
def degenerateSingletonDesign : FieldWeightedDesign Scalar 1 1 where
  atom := fun _ _ => 1
  weight := fun _ => 1
  weight_pos := fun _ => one_pos
  weight_sum_one := by simp
  isParseval := by
    ext rowIndex colIndex
    have hrow : rowIndex = 0 := Subsingleton.elim rowIndex 0
    have hcol : colIndex = 0 := Subsingleton.elim colIndex 0
    subst hrow; subst hcol
    simp [fieldAtom, Matrix.vecMulVec_apply]

/-- **A2 IS FALSE WITHOUT `2 ≤ size`.**  At `size = rank = 1` the chart gap is the
zero matrix, so its Rayleigh quotient vanishes on the range instead of being
positive: the brief's unconditional inertia claim `(rank, size − rank, 0)` reads
`(1, 0, 0)` here while the true inertia is `(0, 0, 1)`.  This is the smallest
design there is, and it is the ONLY shape where A2 fails. -/
theorem degenerateSingleton_chartGap_eq_zero :
    chartGap (degenerateSingletonDesign (Scalar := Scalar)) = 0 := by
  ext rowIndex colIndex
  have hrow : rowIndex = 0 := Subsingleton.elim rowIndex 0
  have hcol : colIndex = 0 := Subsingleton.elim colIndex 0
  subst hrow; subst hcol
  rw [chartGap, Matrix.sub_apply, projectionChart_diagonal]
  simp [degenerateSingletonDesign, fieldLeverageOf]

theorem degenerateSingleton_chartGapRayleigh_eq_zero (vector : Fin 1 → Scalar) :
    chartGapRayleigh (degenerateSingletonDesign (Scalar := Scalar)) vector = 0 := by
  rw [chartGapRayleigh, degenerateSingleton_chartGap_eq_zero, Matrix.zero_mulVec,
    dotProduct_zero, map_zero]

/-! ## A3: the inertia no-go

A2 pins the inertia of `W` to `(rank, size − rank, 0)` for `2 ≤ size`.  A3 says
that fact ALONE proves nothing: there are real symmetric matrices with exactly
that inertia and NO positive semidefinite principal submatrix.  Hence the `P − D`
structure is load-bearing, and no proof of GTZ can run on inertia alone. -/

/-- **A general reason the no-go bites**: a positive semidefinite matrix has a
nonnegative diagonal, so a symmetric matrix whose diagonal is everywhere negative
has NO positive semidefinite principal submatrix of ANY nonempty size.  Both
witnesses below are built that way. -/
theorem no_posSemidef_principal_of_diag_neg {ambient selectionSize : ℕ}
    (form : Matrix (Fin ambient) (Fin ambient) ℝ)
    (hdiagNeg : ∀ index : Fin ambient, form index index < 0)
    (pick : Fin selectionSize → Fin ambient) (hnonempty : 0 < selectionSize) :
    ¬ (form.submatrix pick pick).PosSemidef := by
  intro hpsd
  have hdiag : (0 : ℝ) ≤ form.submatrix pick pick ⟨0, hnonempty⟩ ⟨0, hnonempty⟩ :=
    hpsd.diag_nonneg (i := ⟨0, hnonempty⟩)
  rw [Matrix.submatrix_apply] at hdiag
  exact absurd hdiag (not_le.mpr (hdiagNeg (pick ⟨0, hnonempty⟩)))

/-- **The A3 witness at `(size, rank) = (2, 1)`**, the brief's matrix.  Inertia
`(1, 1, 0)` — one positive direction and one negative direction, exhibited
explicitly below — and neither `1 × 1` principal submatrix is positive
semidefinite, because both diagonal entries are `−1`. -/
def inertiaNoGoMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 3; 3, -1]

theorem inertiaNoGoMatrix_isHermitian : inertiaNoGoMatrix.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> simp [inertiaNoGoMatrix]

theorem inertiaNoGoMatrix_det : inertiaNoGoMatrix.det = -8 := by
  rw [inertiaNoGoMatrix, Matrix.det_fin_two_of]
  norm_num

theorem inertiaNoGoMatrix_det_neg : inertiaNoGoMatrix.det < 0 := by
  rw [inertiaNoGoMatrix_det]; norm_num

/-- One positive direction: `q(1, 1) = 4 > 0`. -/
theorem inertiaNoGoMatrix_positive_direction :
    0 < (![1, 1] : Fin 2 → ℝ) ⬝ᵥ (inertiaNoGoMatrix *ᵥ ![1, 1]) := by
  norm_num [inertiaNoGoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- One negative direction: `q(1, −1) = −8 < 0`.  With the positive direction above
this pins the inertia of the `2 × 2` symmetric witness to `(1, 1, 0)` without any
spectral theory. -/
theorem inertiaNoGoMatrix_negative_direction :
    (![1, -1] : Fin 2 → ℝ) ⬝ᵥ (inertiaNoGoMatrix *ᵥ ![1, -1]) < 0 := by
  norm_num [inertiaNoGoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem inertiaNoGoMatrix_diag_neg (index : Fin 2) : inertiaNoGoMatrix index index < 0 := by
  fin_cases index <;> norm_num [inertiaNoGoMatrix]

/-- **A3, the no-go itself at `(2, 1)`**: no principal submatrix of any nonempty
size — in particular neither `1 × 1` one — is positive semidefinite.  So a matrix
can have exactly the inertia A2 gives and still admit no dominating selection. -/
theorem inertiaNoGoMatrix_no_posSemidef_principal {selectionSize : ℕ}
    (pick : Fin selectionSize → Fin 2) (hnonempty : 0 < selectionSize) :
    ¬ (inertiaNoGoMatrix.submatrix pick pick).PosSemidef :=
  no_posSemidef_principal_of_diag_neg inertiaNoGoMatrix inertiaNoGoMatrix_diag_neg pick hnonempty

/-- **The A3 witness at `(size, rank) = (3, 2)`** — the higher-rank strengthening.
Inertia `(2, 1, 0)`: the quadratic form restricted to the plane spanned by
`(1,1,0)` and `(1,0,1)` is `2a² + 2ab + 2b²`, positive definite, and the
determinant is `−5 < 0`, so exactly one eigenvalue is negative.  Every diagonal
entry is `−1`, so NO principal submatrix of any nonempty size is positive
semidefinite: the bare-inertia statement fails at rank two as well as at rank
one. -/
def inertiaNoGoMatrixThree : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, 2, 2; 2, -1, -2; 2, -2, -1]

theorem inertiaNoGoMatrixThree_isHermitian : inertiaNoGoMatrixThree.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> simp [inertiaNoGoMatrixThree]

theorem inertiaNoGoMatrixThree_det : inertiaNoGoMatrixThree.det = -5 := by
  simp only [inertiaNoGoMatrixThree, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  norm_num

theorem inertiaNoGoMatrixThree_det_neg : inertiaNoGoMatrixThree.det < 0 := by
  rw [inertiaNoGoMatrixThree_det]; norm_num

theorem inertiaNoGoMatrixThree_diag_neg (index : Fin 3) :
    inertiaNoGoMatrixThree index index < 0 := by
  fin_cases index <;> norm_num [inertiaNoGoMatrixThree]

/-- **A3 at `(3, 2)`**: no principal submatrix of any nonempty size is positive
semidefinite, in particular no `2 × 2` one — while the inertia is exactly the
`(rank, size − rank, 0)` that A2 delivers. -/
theorem inertiaNoGoMatrixThree_no_posSemidef_principal {selectionSize : ℕ}
    (pick : Fin selectionSize → Fin 3) (hnonempty : 0 < selectionSize) :
    ¬ (inertiaNoGoMatrixThree.submatrix pick pick).PosSemidef :=
  no_posSemidef_principal_of_diag_neg inertiaNoGoMatrixThree
    inertiaNoGoMatrixThree_diag_neg pick hnonempty

/-- The positive two-plane of the `(3, 2)` witness: on `span{(1,1,0), (1,0,1)}` the
quadratic form is `2a² + 2ab + 2b² = (a+b)² + a² + b²`.  Positive definite there,
so the inertia has at least two positive entries; with `det = −5 < 0` the inertia
is exactly `(2, 1, 0)`. -/
theorem inertiaNoGoMatrixThree_positive_plane (first second : ℝ) :
    (![first + second, first, second] : Fin 3 → ℝ)
        ⬝ᵥ (inertiaNoGoMatrixThree *ᵥ ![first + second, first, second])
      = (first + second) ^ 2 + first ^ 2 + second ^ 2 := by
  simp only [inertiaNoGoMatrixThree, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const]
  ring

theorem inertiaNoGoMatrixThree_positive_plane_pos {first second : ℝ}
    (hnonzero : first ≠ 0 ∨ second ≠ 0) :
    0 < (![first + second, first, second] : Fin 3 → ℝ)
        ⬝ᵥ (inertiaNoGoMatrixThree *ᵥ ![first + second, first, second]) := by
  rw [inertiaNoGoMatrixThree_positive_plane]
  rcases hnonzero with hfirst | hsecond
  · have hpos : 0 < first ^ 2 := by rw [pow_two]; exact mul_self_pos.mpr hfirst
    nlinarith [sq_nonneg (first + second), sq_nonneg second]
  · have hpos : 0 < second ^ 2 := by rw [pow_two]; exact mul_self_pos.mpr hsecond
    nlinarith [sq_nonneg (first + second), sq_nonneg first]

/-! ### Why the chart escapes A3

The A3 witnesses all have a strictly negative diagonal.  A chart gap never does:
`W_cc = t_c(ℓ_c − 1)` and `Σ_c t_c ℓ_c = rank` while `Σ_c t_c = 1`, so
`Σ_c t_c (ℓ_c − 1) = rank − 1 ≥ 0` and some diagonal entry is nonnegative.  That
separation is exactly what the `P − D` structure buys, and it is the reason the
no-go does not refute GTZ. -/

/-- **The chart gap always has a nonnegative diagonal entry** (at rank at least
one).  Equivalently `max_c ℓ_c ≥ 1`: the maximum leverage is at least its
`t`-weighted average, which is the rank.  The A3 family — every diagonal entry
strictly negative — is therefore disjoint from every chart. -/
theorem exists_chartGap_diagonal_nonneg {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (hrank : 1 ≤ rank)
    (hsize : 0 < size) :
    ∃ atomIndex : Fin size,
      0 ≤ design.weight atomIndex * fieldLeverageOf (design.atom atomIndex)
        - design.weight atomIndex := by
  classical
  haveI : Nonempty (Fin size) := Fin.pos_iff_nonempty.mp hsize
  by_contra hall
  push Not at hall
  have hsumNeg : ∑ atomIndex, (design.weight atomIndex
      * fieldLeverageOf (design.atom atomIndex) - design.weight atomIndex) < 0 := by
    refine Finset.sum_neg (fun atomIndex _ => hall atomIndex) ?_
    exact ⟨Classical.arbitrary (Fin size), Finset.mem_univ _⟩
  rw [Finset.sum_sub_distrib, sum_weight_mul_fieldLeverage design,
    design.weight_sum_one] at hsumNeg
  have hrankReal : (1 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
  linarith

/-- **The `rank = 1` positive fact that contrasts with A3**: at rank one the
weighted leverages sum to one, so some atom has leverage at least one — the
maximum is at least the weighted average, and that single atom already dominates.
This is the reason A3 is a statement about inertia and not about charts. -/
theorem exists_one_le_fieldLeverage {size : ℕ}
    (design : FieldWeightedDesign Scalar size 1) (hsize : 0 < size) :
    ∃ atomIndex : Fin size, 1 ≤ fieldLeverageOf (design.atom atomIndex) := by
  classical
  haveI : Nonempty (Fin size) := Fin.pos_iff_nonempty.mp hsize
  by_contra hall
  push Not at hall
  have hstrict : ∑ atomIndex, design.weight atomIndex
        * fieldLeverageOf (design.atom atomIndex)
      < ∑ atomIndex, design.weight atomIndex := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun atomIndex _ => ?_
    calc design.weight atomIndex * fieldLeverageOf (design.atom atomIndex)
        < design.weight atomIndex * 1 :=
          mul_lt_mul_of_pos_left (hall atomIndex) (design.weight_pos atomIndex)
      _ = design.weight atomIndex := mul_one _
  rw [sum_weight_mul_fieldLeverage design, design.weight_sum_one] at hstrict
  norm_num at hstrict

end Gtz
