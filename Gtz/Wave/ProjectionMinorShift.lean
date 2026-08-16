import Gtz.Wave.ProjectionBlockObjective
import Gtz.Quantitative.CauchyBinetValueFloor
import Gtz.Quantitative.ChartHadamard

/-!
# The diagonal shift of a design's projection form

`Gtz.posDef_subsetSum_iff_posDef_projectionBlock` turns strict domination at a
selection into `P_S ≻ diagonal w_S`, where `P = Gtz.projectionOfDesign` is the
symmetric idempotent of trace `rank`.  The objective therefore reads the shifted
matrix

  `Z = P − diagonal w`

and asks for a `rank`-subset whose principal block is positive definite.

The corpus knows this object only through a SCALAR shift.
`Gtz.det_one_add_smul_shifted_real` and `Gtz.sum_det_shiftedChartMinors_eq` give
the whole minor-total ladder of `P − s·1` in closed form, and
`Gtz.sum_det_shiftedChartMinors_sixThree` reads off `−7/27` at `s = 1/6`.  That
is exactly the uniform weight, which is one point of the weight simplex.  The
DIAGONAL shift carries the other five dimensions, and no closed form for it was
known.

## What this file proves

The three power traces of `Z`, at every size and rank, in the four weight
invariants

  `L = ∑_c w_c P_cc`,   `Q = ∑_c w_c²`,   `R = ∑_c P_cc w_c²`,   `C = ∑_c w_c³`:

* `Gtz.trace_diagonalShift`      — `tr Z = rank − 1`
* `Gtz.trace_sq_diagonalShift`   — `tr Z² = rank − 2L + Q`
* `Gtz.trace_cube_diagonalShift` — `tr Z³ = rank − 3L + 3R − C`

Idempotence is spent exactly three times, once per level, and it is what removes
every power of `P` above the first.  These are the complete second-order and
third-order spectral data of the objective's matrix.

## The pair engine

`Gtz.sum_pairMinorAt_eq_trace_sq_sub` is the general identity
`∑_{a,b} (M_aa M_bb − M_ab²) = (tr M)² − tr M²` for a symmetric form.  Applied to
`P` row by row it gives `Gtz.sum_pairMinor_projection`:

  `∑_d (P_cc P_dd − P_cd²) = (rank − 1) · P_cc`,

so a projection's pair minors along a row are pinned by that row's diagonal
entry alone.  Applied to `Z` with the trace laws it gives the level-two minor
total of the diagonal shift, `Gtz.sum_pairMinorAt_diagonalShift`.

## Calibration

At the uniform weight `L = rank/size`, `Q = 1/size`, `R = rank/size²` and
`C = 1/size²`, and `Gtz.trace_sq_diagonalShift_uniform` together with
`Gtz.sum_pairMinorAt_diagonalShift_uniform` reproduce the numbers the landed
scalar-shift ladder already carries.  The general formulas are therefore pinned
against kernel-checked values at that point.

## The determinant cell

`Gtz.posDef_subsetSum_of_forall_weight_lt_det`: if the block determinant
`det P_S` strictly exceeds every weight carried by `S`, then `S` strictly
dominates.  The bound `det ≤ quadratic form` for a contraction is landed
(`Gtz.det_le_dotProduct_mulVec_of_posSemidef_of_posSemidef_one_sub`), and the two
semidefiniteness hypotheses come from `P` and `1 − P` both being symmetric
idempotents.  The cell reads ONE determinant against `rank` weights and needs no
eigenvalue.
-/

namespace Gtz

open Finset Matrix

variable {size rank : ℕ}

/-! ## Part 0 — blocks of a symmetric idempotent -/

/-- Every principal block of a real symmetric idempotent is positive
semidefinite: the block is `Bᵀ B` for the matching column selection. -/
theorem posSemidef_submatrix_of_transpose_of_mul_self {dim selSize : ℕ}
    {form : Matrix (Fin dim) (Fin dim) ℝ} (hsymm : form.transpose = form)
    (hidem : form * form = form) (pick : Fin selSize → Fin dim) :
    (form.submatrix pick pick).PosSemidef := by
  have hblock : form.submatrix pick pick
      = (form.submatrix id pick).transpose * (form.submatrix id pick) := by
    ext leftIndex rightIndex
    have hentry : (form.transpose * form) (pick leftIndex) (pick rightIndex)
        = form (pick leftIndex) (pick rightIndex) := by rw [hsymm, hidem]
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, id]
    simpa only [Matrix.mul_apply, Matrix.transpose_apply] using hentry.symm
  rw [hblock]
  simpa using Matrix.posSemidef_conjTranspose_mul_self (form.submatrix id pick)

/-- Every principal block of a design's projection form is positive
semidefinite. -/
theorem posSemidef_submatrix_projectionOfDesign (design : WeightedDesign size rank)
    {selSize : ℕ} (pick : Fin selSize → Fin size) :
    ((projectionOfDesign design).submatrix pick pick).PosSemidef :=
  posSemidef_submatrix_of_transpose_of_mul_self (projectionOfDesign_transpose design)
    (projectionOfDesign_mul_self design) pick

/-- Every principal block of a design's projection form is a CONTRACTION.  The
complement `1 − P` is a symmetric idempotent, and its blocks are the complements
of the blocks. -/
theorem posSemidef_one_sub_submatrix_projectionOfDesign (design : WeightedDesign size rank)
    {selSize : ℕ} (pick : Fin selSize → Fin size) (hinjective : Function.Injective pick) :
    ((1 : Matrix (Fin selSize) (Fin selSize) ℝ)
        - (projectionOfDesign design).submatrix pick pick).PosSemidef := by
  have hcomplement : ((1 : Matrix (Fin size) (Fin size) ℝ)
      - projectionOfDesign design).submatrix pick pick
      = (1 : Matrix (Fin selSize) (Fin selSize) ℝ)
        - (projectionOfDesign design).submatrix pick pick := by
    ext leftIndex rightIndex
    rcases eq_or_ne leftIndex rightIndex with hdiag | hdiag
    · subst hdiag
      simp [Matrix.submatrix_apply, Matrix.one_apply_eq]
    · have hpick : pick leftIndex ≠ pick rightIndex := fun heq => hdiag (hinjective heq)
      simp [Matrix.submatrix_apply, Matrix.one_apply_ne hdiag, Matrix.one_apply_ne hpick]
  rw [← hcomplement]
  exact posSemidef_submatrix_of_transpose_of_mul_self
    (transpose_one_sub_projectionOfDesign design)
    (one_sub_projectionOfDesign_mul_self design) pick

/-! ## Part 1 — the pair engine -/

/-- The two-by-two principal minor of a form at a pair of labels, written with no
submatrix so that it survives `ring`. -/
def pairMinorAt (form : Matrix (Fin size) (Fin size) ℝ) (first second : Fin size) : ℝ :=
  form first first * form second second - form first second ^ 2

theorem pairMinorAt_self (form : Matrix (Fin size) (Fin size) ℝ) (label : Fin size) :
    pairMinorAt form label label = 0 := by
  simp only [pairMinorAt]; ring

/-- **THE GLOBAL PAIR IDENTITY.**  For a symmetric form the ordered double sum of
the two-by-two principal minors is `(tr M)² − tr M²`.  Every unordered pair is
counted twice and the diagonal contributes nothing, so this is the level-two
minor total up to the factor two.  No hypothesis beyond symmetry. -/
theorem sum_pairMinorAt_eq_trace_sq_sub (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymm : form.transpose = form) :
    ∑ first : Fin size, ∑ second : Fin size, pairMinorAt form first second
      = Matrix.trace form * Matrix.trace form - Matrix.trace (form * form) := by
  have hentry : ∀ first second : Fin size, form second first = form first second := by
    intro first second
    conv_lhs => rw [← hsymm]
    rfl
  have hleft : ∑ first : Fin size, ∑ second : Fin size,
      form first first * form second second
        = Matrix.trace form * Matrix.trace form := by
    simp only [Matrix.trace, Matrix.diag, ← Finset.sum_mul_sum]
  have hright : ∑ first : Fin size, ∑ second : Fin size, form first second ^ 2
      = Matrix.trace (form * form) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun first _ => Finset.sum_congr rfl fun second _ => ?_
    rw [hentry first second]
    ring
  simp only [pairMinorAt, Finset.sum_sub_distrib]
  rw [hleft, hright]

/-- The full row energy of a design's projection form: the squares along a row
total that row's diagonal entry.  This is `Gtz.sum_erase_sq_projectionRow` with
the diagonal square put back. -/
theorem sum_sq_projectionRow_full (design : WeightedDesign size rank) (label : Fin size) :
    ∑ other : Fin size, projectionOfDesign design label other ^ 2
      = projectionOfDesign design label label := by
  classical
  have herase := sum_erase_sq_projectionRow design label
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun other : Fin size => projectionOfDesign design label other ^ 2)
    (Finset.mem_univ label)
  rw [herase] at hsplit
  rw [← hsplit]
  ring

/-- The trace of a design's projection form, as a plain diagonal sum. -/
theorem sum_projectionDiagonal_eq_rank (design : WeightedDesign size rank) :
    ∑ label : Fin size, projectionOfDesign design label label = (rank : ℝ) := by
  have htrace := trace_projectionOfDesign design
  simpa only [Matrix.trace, Matrix.diag] using htrace

/-- **THE PAIR ENGINE.**  Along any row of a design's projection form the
two-by-two principal minors total `(rank − 1)` times that row's diagonal entry.

Only two facts enter: the row energy and the trace.  Neither the atoms nor the
weights survive, so a projection's pair minors along a row are pinned by the
single number `P_cc`. -/
theorem sum_pairMinor_projection (design : WeightedDesign size rank) (label : Fin size) :
    ∑ other : Fin size, pairMinorAt (projectionOfDesign design) label other
      = ((rank : ℝ) - 1) * projectionOfDesign design label label := by
  have hrow := sum_sq_projectionRow_full design label
  have htrace := sum_projectionDiagonal_eq_rank design
  have hexpand : ∑ other : Fin size, pairMinorAt (projectionOfDesign design) label other
      = projectionOfDesign design label label
          * (∑ other : Fin size, projectionOfDesign design other other)
        - ∑ other : Fin size, projectionOfDesign design label other ^ 2 := by
    simp only [pairMinorAt, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hexpand, hrow, htrace]
  ring

/-- The level-two total of a design's projection form, from the pair engine.  The
ordered double sum counts every unordered pair twice, so the unordered total is
`C(rank, 2)`.  Cauchy--Binet gives the same number and this proof does not use
it. -/
theorem sum_pairMinor_projection_double (design : WeightedDesign size rank) :
    ∑ label : Fin size, ∑ other : Fin size,
        pairMinorAt (projectionOfDesign design) label other
      = ((rank : ℝ) - 1) * (rank : ℝ) := by
  rw [Finset.sum_congr rfl fun label _ => sum_pairMinor_projection design label,
    ← Finset.mul_sum, sum_projectionDiagonal_eq_rank design]

/-! ## Part 2 — the diagonal shift and its power traces -/

/-- The diagonal shift of a design's projection form: `Z = P − diagonal w`.  This
is the matrix whose positive definite `rank`-blocks the objective asks for. -/
noncomputable def diagonalShiftForm (design : WeightedDesign size rank) :
    Matrix (Fin size) (Fin size) ℝ :=
  projectionOfDesign design - Matrix.diagonal design.weight

theorem diagonalShiftForm_transpose (design : WeightedDesign size rank) :
    (diagonalShiftForm design).transpose = diagonalShiftForm design := by
  rw [diagonalShiftForm, Matrix.transpose_sub, Matrix.diagonal_transpose,
    projectionOfDesign_transpose]

theorem diagonalShiftForm_diag (design : WeightedDesign size rank) (label : Fin size) :
    diagonalShiftForm design label label
      = projectionOfDesign design label label - design.weight label := by
  simp [diagonalShiftForm, Matrix.diagonal_apply_eq]

theorem diagonalShiftForm_offDiag (design : WeightedDesign size rank)
    {first second : Fin size} (hne : first ≠ second) :
    diagonalShiftForm design first second = projectionOfDesign design first second := by
  simp [diagonalShiftForm, Matrix.diagonal_apply_ne _ hne]

/-- **LEVEL ONE.**  The trace of the diagonal shift is `rank − 1`: the projection
contributes its rank and the weights contribute their total.  This is the only
level at which the design and the weights do not interact.

This level is LANDED as `Gtz.trace_projectionOfDesign_sub_weightDiagonal`, and
this statement is that theorem read in the `Gtz.diagonalShiftForm` vocabulary the
higher levels use.  It is recorded here so the three levels read as one ladder. -/
theorem trace_diagonalShift (design : WeightedDesign size rank) :
    Matrix.trace (diagonalShiftForm design) = (rank : ℝ) - 1 :=
  trace_projectionOfDesign_sub_weightDiagonal design

/-- The weighted leverage `L = ∑_c w_c P_cc`, the first invariant in which the
design and the weights interact. -/
noncomputable def shiftLeverage (design : WeightedDesign size rank) : ℝ :=
  ∑ label : Fin size, design.weight label * projectionOfDesign design label label

/-- The weight energy `Q = ∑_c w_c²`. -/
noncomputable def weightEnergy (design : WeightedDesign size rank) : ℝ :=
  ∑ label : Fin size, design.weight label ^ 2

/-- The second weighted leverage `R = ∑_c P_cc w_c²`. -/
noncomputable def shiftLeverageTwo (design : WeightedDesign size rank) : ℝ :=
  ∑ label : Fin size, projectionOfDesign design label label * design.weight label ^ 2

/-- The weight cube total `C = ∑_c w_c³`. -/
noncomputable def weightCube (design : WeightedDesign size rank) : ℝ :=
  ∑ label : Fin size, design.weight label ^ 3

/-- **LEVEL TWO.**  `tr Z² = rank − 2L + Q`.

Idempotence enters through the row energy, which collapses `tr P²` to `tr P`.
The cross term `tr (P · diagonal w)` is the weighted leverage, and it is the only
place the geometry and the weights meet at this level. -/
theorem trace_sq_diagonalShift (design : WeightedDesign size rank) :
    Matrix.trace (diagonalShiftForm design * diagonalShiftForm design)
      = (rank : ℝ) - 2 * shiftLeverage design + weightEnergy design := by
  classical
  have hentry : ∀ first second : Fin size,
      projectionOfDesign design second first = projectionOfDesign design first second := by
    intro first second
    conv_lhs => rw [← projectionOfDesign_transpose design]
    rfl
  have hexpand : Matrix.trace (diagonalShiftForm design * diagonalShiftForm design)
      = ∑ first : Fin size, ∑ second : Fin size,
          diagonalShiftForm design first second * diagonalShiftForm design first second := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun first _ => Finset.sum_congr rfl fun second _ => ?_
    have hsymmShift : diagonalShiftForm design second first
        = diagonalShiftForm design first second := by
      conv_lhs => rw [← diagonalShiftForm_transpose design]
      rfl
    rw [hsymmShift]
  rw [hexpand]
  have hsplit : ∀ first : Fin size,
      ∑ second : Fin size,
          diagonalShiftForm design first second * diagonalShiftForm design first second
        = (∑ second : Fin size,
              projectionOfDesign design first second * projectionOfDesign design first second)
          - 2 * design.weight first * projectionOfDesign design first first
          + design.weight first ^ 2 := by
    intro first
    have hpoint : ∀ second : Fin size,
        diagonalShiftForm design first second * diagonalShiftForm design first second
          = projectionOfDesign design first second * projectionOfDesign design first second
            + (if first = second then
                (- 2 * design.weight first * projectionOfDesign design first first
                  + design.weight first ^ 2) else 0) := by
      intro second
      rcases eq_or_ne first second with hdiag | hdiag
      · subst hdiag
        rw [diagonalShiftForm_diag design first, if_pos rfl]
        ring
      · rw [diagonalShiftForm_offDiag design hdiag, if_neg hdiag]
        ring
    rw [Finset.sum_congr rfl fun second _ => hpoint second, Finset.sum_add_distrib,
      Finset.sum_ite_eq Finset.univ first]
    simp only [Finset.mem_univ, if_true]
    ring
  rw [Finset.sum_congr rfl fun first _ => hsplit first]
  have hrow : ∀ first : Fin size,
      ∑ second : Fin size,
          projectionOfDesign design first second * projectionOfDesign design first second
        = projectionOfDesign design first first := by
    intro first
    have := sum_sq_projectionRow_full design first
    simpa only [pow_two] using this
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun first _ => hrow first, sum_projectionDiagonal_eq_rank design]
  have hcross : ∑ first : Fin size,
      2 * design.weight first * projectionOfDesign design first first
        = 2 * shiftLeverage design := by
    rw [shiftLeverage, Finset.mul_sum]
    exact Finset.sum_congr rfl fun first _ => by ring
  rw [hcross]
  rfl

/-- **THE LEVEL-TWO MINOR TOTAL OF THE DIAGONAL SHIFT.**  Combining the global
pair identity with the two trace laws:

  `∑_{a,b} (Z_aa Z_bb − Z_ab²) = (rank − 1)² − rank + 2L − Q`.

The ordered double sum is twice the level-two principal-minor total, so this is
the complete second symmetric function of the objective's matrix, in closed form,
at every size and rank and at every weight. -/
theorem sum_pairMinorAt_diagonalShift (design : WeightedDesign size rank) :
    ∑ first : Fin size, ∑ second : Fin size,
        pairMinorAt (diagonalShiftForm design) first second
      = ((rank : ℝ) - 1) * ((rank : ℝ) - 1) - (rank : ℝ)
        + 2 * shiftLeverage design - weightEnergy design := by
  rw [sum_pairMinorAt_eq_trace_sq_sub (diagonalShiftForm design)
      (diagonalShiftForm_transpose design),
    trace_diagonalShift design, trace_sq_diagonalShift design]
  ring

/-! ## Part 2b — the third power trace -/

/-- The trace of a form against a diagonal reads the diagonal only. -/
theorem trace_mul_diagonal (form : Matrix (Fin size) (Fin size) ℝ) (vector : Fin size → ℝ) :
    Matrix.trace (form * Matrix.diagonal vector)
      = ∑ label : Fin size, form label label * vector label := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]

/-- The trace of a form against two diagonals reads the diagonal squared. -/
theorem trace_mul_diagonal_diagonal (form : Matrix (Fin size) (Fin size) ℝ)
    (vector : Fin size → ℝ) :
    Matrix.trace (form * Matrix.diagonal vector * Matrix.diagonal vector)
      = ∑ label : Fin size, form label label * vector label ^ 2 := by
  rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, trace_mul_diagonal]
  exact Finset.sum_congr rfl fun label _ => by ring

/-- The trace of the diagonal cube. -/
theorem trace_diagonal_cube (vector : Fin size → ℝ) :
    Matrix.trace (Matrix.diagonal vector * Matrix.diagonal vector * Matrix.diagonal vector)
      = ∑ label : Fin size, vector label ^ 3 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  exact Finset.sum_congr rfl fun label _ => by ring

/-- **LEVEL THREE.**  `tr Z³ = rank − 3L + 3R − C`.

The eight terms of `(P − D)³` collapse to four by cyclicity of the trace and
idempotence.  Every term carrying two or three copies of `P` reduces to one copy,
which is why the answer is linear in the projection and the design enters only
through `L` and `R`.  Together with `Gtz.trace_diagonalShift` and
`Gtz.trace_sq_diagonalShift` this is the complete third-order spectral data of
the objective's matrix. -/
theorem trace_cube_diagonalShift (design : WeightedDesign size rank) :
    Matrix.trace (diagonalShiftForm design * diagonalShiftForm design
        * diagonalShiftForm design)
      = (rank : ℝ) - 3 * shiftLeverage design + 3 * shiftLeverageTwo design
        - weightCube design := by
  classical
  set proj := projectionOfDesign design with hproj
  set diag := Matrix.diagonal design.weight with hdiag
  have hidem : proj * proj = proj := by rw [hproj]; exact projectionOfDesign_mul_self design
  have hexpand : diagonalShiftForm design * diagonalShiftForm design
      * diagonalShiftForm design
      = proj * proj * proj - proj * proj * diag - proj * diag * proj - diag * proj * proj
        + proj * diag * diag + diag * proj * diag + diag * diag * proj
        - diag * diag * diag := by
    simp only [diagonalShiftForm, ← hproj, ← hdiag, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hexpand]
  simp only [Matrix.trace_sub, Matrix.trace_add]
  have hcube : Matrix.trace (proj * proj * proj) = (rank : ℝ) := by
    rw [hidem, hidem, hproj]; exact trace_projectionOfDesign design
  have hsquareDiag : Matrix.trace (proj * proj * diag) = shiftLeverage design := by
    rw [hidem, hdiag, trace_mul_diagonal, shiftLeverage, ← hproj]
    exact Finset.sum_congr rfl fun label _ => by ring
  have hmiddle : Matrix.trace (proj * diag * proj) = shiftLeverage design := by
    rw [Matrix.trace_mul_comm (proj * diag) proj, ← Matrix.mul_assoc, hidem, hdiag,
      trace_mul_diagonal, shiftLeverage, ← hproj]
    exact Finset.sum_congr rfl fun label _ => by ring
  have hleftPair : Matrix.trace (diag * proj * proj) = shiftLeverage design := by
    rw [Matrix.mul_assoc, hidem, Matrix.trace_mul_comm diag proj, hdiag,
      trace_mul_diagonal, shiftLeverage, ← hproj]
    exact Finset.sum_congr rfl fun label _ => by ring
  have hprojDiagDiag : Matrix.trace (proj * diag * diag) = shiftLeverageTwo design := by
    rw [hdiag, trace_mul_diagonal_diagonal, shiftLeverageTwo, ← hproj]
  have hdiagDiagProj : Matrix.trace (diag * diag * proj) = shiftLeverageTwo design := by
    rw [Matrix.trace_mul_comm (diag * diag) proj, ← Matrix.mul_assoc, hdiag,
      trace_mul_diagonal_diagonal, shiftLeverageTwo, ← hproj]
  have hdiagProjDiag : Matrix.trace (diag * proj * diag) = shiftLeverageTwo design := by
    rw [Matrix.trace_mul_comm (diag * proj) diag, ← Matrix.mul_assoc]
    exact hdiagDiagProj
  have hcubeDiag : Matrix.trace (diag * diag * diag) = weightCube design := by
    rw [hdiag, trace_diagonal_cube, weightCube]
  rw [hcube, hsquareDiag, hmiddle, hleftPair, hprojDiagDiag, hdiagProjDiag, hdiagDiagProj,
    hcubeDiag]
  ring

/-! ## Part 2c — the sign of the level-two total, and the contrast with level three -/

/-- The weighted leverage is non-negative: both factors are. -/
theorem shiftLeverage_nonneg (design : WeightedDesign size rank) :
    0 ≤ shiftLeverage design :=
  Finset.sum_nonneg fun label _ =>
    mul_nonneg (design.weight_pos label).le (projectionOfDesign_diagonal_nonneg design label)

/-- The weight energy is strictly less than one.  Every weight is strictly below
one because the weights are positive and total one, so each square is strictly
below its own weight. -/
theorem weightEnergy_lt_one (design : WeightedDesign size rank) (htwo : 2 ≤ size) :
    weightEnergy design < 1 := by
  classical
  have hnonempty : (Finset.univ : Finset (Fin size)).Nonempty := by
    refine Finset.univ_nonempty_iff.mpr ?_
    exact Fin.pos_iff_nonempty.mp (by omega)
  have hterm : ∀ label : Fin size,
      design.weight label ^ 2 < design.weight label := by
    intro label
    have hpos := design.weight_pos label
    have hlt := weight_lt_one design htwo label
    nlinarith [hpos, hlt]
  have hsplit : weightEnergy design < ∑ label : Fin size, design.weight label :=
    Finset.sum_lt_sum_of_nonempty hnonempty fun label _ => hterm label
  rwa [design.weight_sum_one] at hsplit

/-- **THE LEVEL-TWO TOTAL IS STRICTLY POSITIVE AT RANK THREE.**

`∑_{a,b} (Z_aa Z_bb − Z_ab²) = 1 + 2L − Q`, and `L ≥ 0` while `Q < 1`, so the
total is strictly positive with no hypothesis on the design or on the weights.

Set this beside `Gtz.sum_det_shiftedChartMinors_sixThree`, which says the
level-THREE total is `−7/27` at the uniform weight.  The second symmetric
function of the objective's matrix averages POSITIVE over the pairs and the third
averages NEGATIVE over the triples.  Any argument that hopes to find a positive
triple determinant by averaging is therefore reading the wrong level. -/
theorem sum_pairMinorAt_diagonalShift_pos (design : WeightedDesign size 3) :
    0 < ∑ first : Fin size, ∑ second : Fin size,
        pairMinorAt (diagonalShiftForm design) first second := by
  rw [sum_pairMinorAt_diagonalShift design]
  have hlev := shiftLeverage_nonneg design
  have hthree : 3 ≤ size := rank_le_of_design design
  have henergy := weightEnergy_lt_one design (by omega)
  norm_num
  linarith [hlev, henergy]

/-- Some pair of labels carries a strictly positive two-by-two principal minor of
the shifted form.  This is the level-two existence statement, and it is
unconditional. -/
theorem exists_pairMinorAt_diagonalShift_pos (design : WeightedDesign size 3) :
    ∃ first second : Fin size, 0 < pairMinorAt (diagonalShiftForm design) first second := by
  by_contra hnone
  push Not at hnone
  have hnonpos : ∑ first : Fin size, ∑ second : Fin size,
      pairMinorAt (diagonalShiftForm design) first second ≤ 0 :=
    Finset.sum_nonpos fun first _ => Finset.sum_nonpos fun second _ => hnone first second
  exact absurd (sum_pairMinorAt_diagonalShift_pos design) (not_lt.mpr hnonpos)

/-! ## Part 2d — calibration at the uniform weight -/

/-- At the uniform weight the weighted leverage is `rank / size`: the weight
factors out of the trace. -/
theorem shiftLeverage_uniform (design : WeightedDesign size rank)
    (huniform : ∀ label : Fin size, design.weight label = (size : ℝ)⁻¹) :
    shiftLeverage design = (size : ℝ)⁻¹ * (rank : ℝ) := by
  rw [shiftLeverage, Finset.sum_congr rfl fun label _ => by
    rw [huniform label], ← Finset.mul_sum, sum_projectionDiagonal_eq_rank design]

/-- At the uniform weight the weight energy is `1 / size`. -/
theorem weightEnergy_uniform (design : WeightedDesign size rank)
    (huniform : ∀ label : Fin size, design.weight label = (size : ℝ)⁻¹) (hpos : 0 < size) :
    weightEnergy design = (size : ℝ)⁻¹ := by
  have hsizeNe : (size : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  rw [weightEnergy, Finset.sum_congr rfl fun label _ => by rw [huniform label]]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- At the uniform weight the second weighted leverage is `rank / size²`. -/
theorem shiftLeverageTwo_uniform (design : WeightedDesign size rank)
    (huniform : ∀ label : Fin size, design.weight label = (size : ℝ)⁻¹) :
    shiftLeverageTwo design = (size : ℝ)⁻¹ * (size : ℝ)⁻¹ * (rank : ℝ) := by
  have hterm : ∀ label : Fin size,
      projectionOfDesign design label label * design.weight label ^ 2
        = ((size : ℝ)⁻¹ * (size : ℝ)⁻¹) * projectionOfDesign design label label := by
    intro label; rw [huniform label]; ring
  rw [shiftLeverageTwo, Finset.sum_congr rfl fun label _ => hterm label, ← Finset.mul_sum,
    sum_projectionDiagonal_eq_rank design]

/-- **THE CALIBRATION.**  At the uniform weight the level-two total of the
diagonal shift is `(rank − 1)² − rank + 2·rank/size − 1/size`.

At `(6,3)` this is `11/6`, so the unordered level-two total is `11/12`.  That
number also drops out of the landed scalar-shift ladder
`Gtz.sum_det_shiftedChartMinors_eq` at shift `1/6`, which pins the general
formula of `Gtz.sum_pairMinorAt_diagonalShift` against kernel-checked values at
one point of the weight simplex. -/
theorem sum_pairMinorAt_diagonalShift_uniform (design : WeightedDesign size rank)
    (huniform : ∀ label : Fin size, design.weight label = (size : ℝ)⁻¹) (hpos : 0 < size) :
    ∑ first : Fin size, ∑ second : Fin size,
        pairMinorAt (diagonalShiftForm design) first second
      = ((rank : ℝ) - 1) * ((rank : ℝ) - 1) - (rank : ℝ)
        + 2 * ((size : ℝ)⁻¹ * (rank : ℝ)) - (size : ℝ)⁻¹ := by
  rw [sum_pairMinorAt_diagonalShift design, shiftLeverage_uniform design huniform,
    weightEnergy_uniform design huniform hpos]

/-- The third power trace at the uniform weight, in `(size, rank)` only.  The
design has vanished, exactly as it does in the landed scalar-shift ladder. -/
theorem trace_cube_diagonalShift_uniform (design : WeightedDesign size rank)
    (huniform : ∀ label : Fin size, design.weight label = (size : ℝ)⁻¹) (hpos : 0 < size) :
    Matrix.trace (diagonalShiftForm design * diagonalShiftForm design
        * diagonalShiftForm design)
      = (rank : ℝ) - 3 * ((size : ℝ)⁻¹ * (rank : ℝ))
        + 3 * ((size : ℝ)⁻¹ * (size : ℝ)⁻¹ * (rank : ℝ))
        - (size : ℝ)⁻¹ * (size : ℝ)⁻¹ := by
  have hsizeNe : (size : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  rw [trace_cube_diagonalShift design, shiftLeverage_uniform design huniform,
    shiftLeverageTwo_uniform design huniform]
  have hcube : weightCube design = (size : ℝ)⁻¹ * (size : ℝ)⁻¹ := by
    rw [weightCube, Finset.sum_congr rfl fun label _ => by rw [huniform label],
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hcube]

/-! ## Part 3 — the determinant cell -/

/-- The quadratic form of a design's projection block is at least its
determinant times the squared length of the probe.  This is the landed
contraction bound `Gtz.det_le_dotProduct_mulVec_of_posSemidef_of_posSemidef_one_sub`
rescaled off the unit sphere. -/
theorem det_mul_dotProduct_le_projectionBlock_form (design : WeightedDesign size rank)
    {selSize : ℕ} (pick : Fin selSize → Fin size) (hinjective : Function.Injective pick)
    (probe : Fin selSize → ℝ) :
    ((projectionOfDesign design).submatrix pick pick).det * (probe ⬝ᵥ probe)
      ≤ probe ⬝ᵥ (((projectionOfDesign design).submatrix pick pick) *ᵥ probe) := by
  classical
  set block := (projectionOfDesign design).submatrix pick pick with hblock
  have hpsd : block.PosSemidef := posSemidef_submatrix_projectionOfDesign design pick
  have hcontraction : ((1 : Matrix (Fin selSize) (Fin selSize) ℝ) - block).PosSemidef :=
    posSemidef_one_sub_submatrix_projectionOfDesign design pick hinjective
  rcases eq_or_ne probe 0 with hzero | hzero
  · subst hzero
    simp
  · have hnorm : 0 < probe ⬝ᵥ probe := by
      rcases Function.ne_iff.mp hzero with ⟨slot, hslot⟩
      have hnonneg : ∀ other : Fin selSize, 0 ≤ probe other * probe other :=
        fun other => mul_self_nonneg _
      have hpos : 0 < probe slot * probe slot := by
        have : probe slot ≠ 0 := by simpa using hslot
        exact mul_self_pos.mpr this
      calc (0 : ℝ) < probe slot * probe slot := hpos
        _ ≤ ∑ other : Fin selSize, probe other * probe other :=
            Finset.single_le_sum (fun other _ => hnonneg other) (Finset.mem_univ slot)
        _ = probe ⬝ᵥ probe := rfl
    set scale : ℝ := Real.sqrt (probe ⬝ᵥ probe) with hscale
    have hscalePos : 0 < scale := Real.sqrt_pos.mpr hnorm
    have hscaleSq : scale * scale = probe ⬝ᵥ probe := Real.mul_self_sqrt hnorm.le
    set unit : Fin selSize → ℝ := fun slot => scale⁻¹ * probe slot with hunit
    have hscaleNe : scale ≠ 0 := hscalePos.ne'
    have hunitNorm : unit ⬝ᵥ unit = 1 := by
      have hexpand : unit ⬝ᵥ unit = scale⁻¹ * scale⁻¹ * (probe ⬝ᵥ probe) := by
        simp only [hunit, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun slot _ => by ring
      rw [hexpand, ← hscaleSq]
      have hcancel : scale⁻¹ * scale = 1 := inv_mul_cancel₀ hscaleNe
      calc scale⁻¹ * scale⁻¹ * (scale * scale)
          = (scale⁻¹ * scale) * (scale⁻¹ * scale) := by ring
        _ = 1 := by rw [hcancel]; ring
    have hbound := det_le_dotProduct_mulVec_of_posSemidef_of_posSemidef_one_sub hpsd
      hcontraction hunitNorm
    have hscaleForm : unit ⬝ᵥ (block *ᵥ unit)
        = scale⁻¹ * scale⁻¹ * (probe ⬝ᵥ (block *ᵥ probe)) := by
      simp only [hunit, dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun leftSlot _ =>
        Finset.sum_congr rfl fun rightSlot _ => by ring
    rw [hscaleForm] at hbound
    have hcancel : scale * scale * (scale⁻¹ * scale⁻¹ * (probe ⬝ᵥ (block *ᵥ probe)))
        = probe ⬝ᵥ (block *ᵥ probe) := by
      have hone : scale * scale⁻¹ = 1 := mul_inv_cancel₀ hscaleNe
      calc scale * scale * (scale⁻¹ * scale⁻¹ * (probe ⬝ᵥ (block *ᵥ probe)))
          = (scale * scale⁻¹) * (scale * scale⁻¹) * (probe ⬝ᵥ (block *ᵥ probe)) := by ring
        _ = probe ⬝ᵥ (block *ᵥ probe) := by rw [hone]; ring
    have hmul := mul_le_mul_of_nonneg_left hbound
      (le_of_lt (mul_pos hscalePos hscalePos))
    rw [hcancel] at hmul
    have hcomm : block.det * (probe ⬝ᵥ probe) = scale * scale * block.det := by
      rw [← hscaleSq]; ring
    rw [hcomm]
    exact hmul

/-- **THE DETERMINANT CELL.**  If the block determinant `det P_S` strictly
exceeds every weight carried by `S`, then the shifted block is positive
definite.

The proof reads one determinant against `rank` weights.  No eigenvalue appears in
the statement, and the only spectral input is the landed contraction bound, which
holds because `P` and `1 − P` are both symmetric idempotents. -/
theorem posDef_projectionBlock_of_forall_weight_lt_det (design : WeightedDesign size rank)
    {selSize : ℕ} (pick : Fin selSize → Fin size) (hinjective : Function.Injective pick)
    (hweight : ∀ slot : Fin selSize,
      design.weight (pick slot) < ((projectionOfDesign design).submatrix pick pick).det) :
    ((projectionOfDesign design).submatrix pick pick
        - Matrix.diagonal (fun slot => design.weight (pick slot))).PosDef := by
  classical
  set block := (projectionOfDesign design).submatrix pick pick with hblock
  set shifted := block - Matrix.diagonal (fun slot => design.weight (pick slot)) with hshifted
  have hsymm : shifted.IsHermitian := by
    have hblockSymm : block.transpose = block := by
      rw [hblock]
      ext leftIndex rightIndex
      have hentry : projectionOfDesign design (pick rightIndex) (pick leftIndex)
          = projectionOfDesign design (pick leftIndex) (pick rightIndex) := by
        conv_lhs => rw [← projectionOfDesign_transpose design]
        rfl
      simpa only [Matrix.transpose_apply, Matrix.submatrix_apply] using hentry
    show shifted.transpose = shifted
    rw [hshifted, Matrix.transpose_sub, Matrix.diagonal_transpose, hblockSymm]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hsymm, fun probe hprobe => ?_⟩
  have hdiagForm : probe ⬝ᵥ ((Matrix.diagonal (fun slot => design.weight (pick slot))) *ᵥ probe)
      = ∑ slot : Fin selSize, design.weight (pick slot) * (probe slot * probe slot) := by
    simp only [Matrix.mulVec_diagonal, dotProduct]
    exact Finset.sum_congr rfl fun slot _ => by ring
  have hsplit : probe ⬝ᵥ (shifted *ᵥ probe)
      = probe ⬝ᵥ (block *ᵥ probe)
        - ∑ slot : Fin selSize, design.weight (pick slot) * (probe slot * probe slot) := by
    rw [hshifted, Matrix.sub_mulVec, dotProduct_sub, hdiagForm]
  have hlower := det_mul_dotProduct_le_projectionBlock_form design pick hinjective probe
  have hgap : 0 < ∑ slot : Fin selSize,
      (block.det - design.weight (pick slot)) * (probe slot * probe slot) := by
    rcases Function.ne_iff.mp hprobe with ⟨slot, hslot⟩
    have hnonneg : ∀ other : Fin selSize,
        0 ≤ (block.det - design.weight (pick other)) * (probe other * probe other) := by
      intro other
      exact mul_nonneg (by linarith [hweight other]) (mul_self_nonneg _)
    have hpos : 0 < (block.det - design.weight (pick slot)) * (probe slot * probe slot) := by
      have hne : probe slot ≠ 0 := by simpa using hslot
      exact mul_pos (by linarith [hweight slot]) (mul_self_pos.mpr hne)
    calc (0 : ℝ) < (block.det - design.weight (pick slot)) * (probe slot * probe slot) := hpos
      _ ≤ _ := Finset.single_le_sum (fun other _ => hnonneg other) (Finset.mem_univ slot)
  have hexpandGap : ∑ slot : Fin selSize,
      (block.det - design.weight (pick slot)) * (probe slot * probe slot)
      = block.det * (probe ⬝ᵥ probe)
        - ∑ slot : Fin selSize, design.weight (pick slot) * (probe slot * probe slot) := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun slot _ => by ring
  rw [hexpandGap] at hgap
  simp only [star_trivial]
  rw [hsplit]
  linarith [hlower, hgap]

/-- **THE CELL, ON THE OBJECTIVE.**  A selection whose projection-block
determinant beats every weight it carries strictly dominates.  This is the cell
chained through `Gtz.posDef_subsetSum_iff_posDef_projectionBlock` to the atom
side, which is what `Gtz.ConsolidatedStrictTripleDesign` quantifies over. -/
theorem posDef_subsetSum_of_forall_weight_lt_det (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (hweight : ∀ slot : Fin rank,
      design.weight (pick slot) < ((projectionOfDesign design).submatrix pick pick).det) :
    (subsetSum design (Finset.image pick Finset.univ) - 1).PosDef := by
  rw [posDef_subsetSum_iff_posDef_projectionBlock design pick hinjective]
  exact posDef_projectionBlock_of_forall_weight_lt_det design pick hinjective hweight

/-- The cell in the form the consolidated statement consumes: a `rank`-subset
whose block determinant beats its own weights supplies the required selection. -/
theorem exists_posDef_subsetSum_of_forall_weight_lt_det (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (hweight : ∀ slot : Fin rank,
      design.weight (pick slot) < ((projectionOfDesign design).submatrix pick pick).det) :
    ∃ selected : Finset (Fin size), selected.card = rank
      ∧ (subsetSum design selected - 1).PosDef := by
  refine ⟨Finset.image pick Finset.univ, ?_,
    posDef_subsetSum_of_forall_weight_lt_det design pick hinjective hweight⟩
  rw [Finset.card_image_of_injective _ hinjective, Finset.card_univ, Fintype.card_fin]

end Gtz
