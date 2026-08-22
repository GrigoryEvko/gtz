/-
# The primitive tie package, and the doubled co-leverage criterion

Two things live here.  The first is an ASSEMBLY: the hypotheses the campaign
carries separately on the `(6,3)` residual are one theorem about primitivity.
The second is NEW: a domination criterion that doubles the landed co-leverage
threshold at the cost of a single determinant sign.

## 1. The doubled criterion

`Gtz.dominates_of_sum_coLeverageRatio_le_one` (Gtz/Reduction/DiagonalRungs.lean)
is the landed criterion: a `k`-subset whose co-leverage ratios total at most ONE
dominates.  Its threshold is exactly the point where a diagonal beats a positive
semidefinite residual by the crudest possible argument, and the campaign has
never moved it.

`Gtz.posSemidef_one_sub_of_det_nonneg_of_trace_le_two`
(Gtz/Wave/PencilTraceLaw.lean) replaces the seven Sylvester conditions of a
`3 x 3` contraction by TWO.  Its header advertises a version against an
arbitrary positive diagonal, `Gtz.posSemidef_diagonal_sub_of_det_nonneg_of_weightedTrace_le_two`,
which the file does not contain.  Part 1 lands it, by the congruence
`diag(z^{1/2})` that normalises the diagonal away.

Feeding the design's own chart to that law gives the criterion of Part 2:

  **`Gtz.dominates_of_sum_coLeverageRatio_le_two`.**  At rank three, a triple
  whose co-leverage ratios total at most TWO and whose chart gap block has
  nonnegative determinant dominates.

The threshold has doubled and the price is one polynomial sign.  On the range
`(1, 2]` the criterion is genuinely new: below one the landed criterion already
fires with no determinant hypothesis at all, and
`Gtz.dominates_iff_det_nonneg_of_sum_coLeverageRatio_le_two` shows the
determinant sign is then not merely sufficient but EQUIVALENT to domination.

## 2. Why two is the right threshold at `(6,3)`

The co-leverage ratios obey an exact budget,
`sum_c (1 - t_c) * s_c = m - k` (`Gtz.sum_one_sub_weight_mul_coLeverageRatio`),
and a design is ALL-HEAVY exactly when every ratio is below one
(`Gtz.coLeverageRatio_lt_one_iff`).  Splitting the budget:

    **`sum_c s_c  =  (m - k)  +  sum_c t_c s_c  <  (m - k) + 1`**

at every all-heavy design (`Gtz.sum_coLeverageRatio_lt_of_allHeavy`).  At `(6,3)`
the total is below FOUR, so a triple and its complement cannot both carry two:

  **`Gtz.exists_compl_sum_coLeverageRatio_lt_two`** -- at every all-heavy
  `(6,3)` design, one of any complementary pair of triples has ratio total below
  two, so the criterion of Part 2 applies to it.

Chaining gives the collapse this module is for:

  **`Gtz.exists_triple_dominates_iff_tripleChartGapDet_nonneg`.**  Every
  all-heavy `(6,3)` design carries a triple at which domination is EXACTLY the
  sign of one determinant.

`Gtz.hingeHoldsAtSize_six_three_of_allHeavy` says all-heavy is the whole open
cell, so this is a statement about the residual and not about a stratum of it.

## 3. The seventh clause

At a TIE no triple dominates strictly, so the collapsed determinant cannot be
positive:

  **`Gtz.tripleChartGapDet_nonpos_of_isTie_of_sum_le_two`** and its `(6,3)`
  existential `Gtz.exists_triple_tripleChartGapDet_nonpos_of_isTie_allHeavy`.

`Gtz.sixThree_primitiveTie_normalForm` (Gtz/Wave/TieStratumClassification.lean)
pins a counterexample by six unconditional clauses.  This is a SEVENTH, and it
has a shape none of the six has: an existential over triples carrying a
determinant sign, rather than a global scalar or a coplanarity count.
`Gtz.sixThree_primitiveTie_sharpNormalForm` states the eight together.
INDEPENDENCE OF THE SEVENTH CLAUSE IS NOT PROVED and no separating design is
exhibited.

## 4. The package

`Gtz.allHeavy_of_isPrimitiveDesign_of_isTie_sixThree` -- a primitive `(6,3)` tie
is ALL-HEAVY.  Two landed facts meet: the tie dichotomy
`Gtz.allHeavy_or_exists_leverage_eq_one_of_isTie_sixThree` and the funnel closure
`Gtz.hasParallelPair_of_isTie_sixThree_of_unitAtom`.  The campaign carried
all-heaviness as a HYPOTHESIS on the residual; against primitivity it is a
theorem, and the residual's hypothesis pile shrinks by one.

## What this module does NOT claim

* It does not claim that a primitive `(6,3)` tie has only `K0` dominators.  A
  coordinator brief asserted this; it is FALSE as an assertion, because
  primitivity excludes neither a `K1` dominator (one vanishing inside pair minor)
  nor a corner (three vanishing).  The `192/192` `K0` census at the split
  diamonds is EVIDENCE and not a theorem.  What is available is the landed
  trichotomy, and this module states the three cases rather than folding them in.
* It does not land "every five-set of a primitive tie dominates strictly", nor
  "the sharp dual of a primitive tie is a primitive tie".  Both need `IsTie` to
  transport across the sharp duality, and the STRICT half of that transport is
  not in the tree: `Gtz.dominates_iff_dominates_naimarkSharpDesign_compl`
  (Gtz/Wave/SharpDesignInvolution.lean) is stated for `Gtz.Dominates` alone, and
  `Gtz.IsTie` also quantifies a `PosDef` over every triple.  The pieces for that
  transport ARE all landed -- `Gtz.posDef_congr_right`,
  `Gtz.posDef_one_sub_transpose_comm` -- so it is a bounded job for a successor,
  and it is the only missing link in the chain
  `primitive tie -> dual primitive tie -> dual all-heavy -> every five-set strict`.
  The PAIR-LAYER EXCHANGE that chain also needs is NOT missing: it is landed as
  `Gtz.fourCoplanar_iff_crossNormSq_naimarkSharpAtom`, and Part 5 spends it to
  prove the dual is primitive, which needs no tie transport at all.
-/
import Gtz.Wave.PencilTraceLaw
import Gtz.Reduction.DiagonalRungs
import Gtz.Wave.UnitAtomFunnelClosure
import Gtz.Wave.TieStratumClassification
import Gtz.Wave.SharpDesignInvolution
import Gtz.Wave.TieParallelPairWeightRegular
import Gtz.Wave.ChartComplementBlockLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1 — the trace-and-determinant law against a positive diagonal

`Gtz.posSemidef_one_sub_of_det_nonneg_of_trace_le_two` is stated against the
identity.  A design's chart gap is a positive diagonal minus a positive
semidefinite block, so the law has to be moved onto an arbitrary positive
diagonal.  One congruence by the diagonal square root does it, and the
congruence is invertible, so nothing is lost in either direction. -/

/-- The entrywise positive square root of a positive diagonal. -/
noncomputable def diagRoot {size : ℕ} (diagEntry : Fin size → ℝ) : Fin size → ℝ :=
  fun slot => Real.sqrt (diagEntry slot)

theorem diagRoot_pos {size : ℕ} {diagEntry : Fin size → ℝ}
    (hpos : ∀ slot, 0 < diagEntry slot) (slot : Fin size) :
    0 < diagRoot diagEntry slot :=
  Real.sqrt_pos.mpr (hpos slot)

theorem diagRoot_mul_self {size : ℕ} {diagEntry : Fin size → ℝ}
    (hpos : ∀ slot, 0 < diagEntry slot) (slot : Fin size) :
    diagRoot diagEntry slot * diagRoot diagEntry slot = diagEntry slot :=
  Real.mul_self_sqrt (hpos slot).le

/-- The residual, normalised by the diagonal:
`R = diag(z^{-1/2}) * Y * diag(z^{-1/2})`. -/
noncomputable def diagNormalize {size : ℕ} (diagEntry : Fin size → ℝ)
    (residual : Matrix (Fin size) (Fin size) ℝ) : Matrix (Fin size) (Fin size) ℝ :=
  Matrix.diagonal (fun slot => (diagRoot diagEntry slot)⁻¹) * residual
    * Matrix.diagonal (fun slot => (diagRoot diagEntry slot)⁻¹)

theorem diagNormalize_apply {size : ℕ} (diagEntry : Fin size → ℝ)
    (residual : Matrix (Fin size) (Fin size) ℝ) (row col : Fin size) :
    diagNormalize diagEntry residual row col
      = (diagRoot diagEntry row)⁻¹ * residual row col * (diagRoot diagEntry col)⁻¹ := by
  rw [diagNormalize, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- The normalised residual is positive semidefinite: it is a congruence of the
residual by an invertible diagonal. -/
theorem posSemidef_diagNormalize {size : ℕ} {diagEntry : Fin size → ℝ}
    (hpos : ∀ slot, 0 < diagEntry slot) {residual : Matrix (Fin size) (Fin size) ℝ}
    (hres : residual.PosSemidef) : (diagNormalize diagEntry residual).PosSemidef := by
  have hunit : IsUnit (Matrix.diagonal (fun slot => (diagRoot diagEntry slot)⁻¹)).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun slot _ =>
      inv_ne_zero (ne_of_gt (diagRoot_pos hpos slot))
  have hsymm : residualᵀ = residual := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hres.1
  have hcongr := (posSemidef_congr_right (X := residual)
    (P := Matrix.diagonal (fun slot => (diagRoot diagEntry slot)⁻¹)) hsymm hunit).mp hres
  rwa [Matrix.diagonal_transpose, ← diagNormalize] at hcongr

/-- **THE CONGRUENCE.**  Conjugating the normalised gap by the diagonal square
root returns the gap itself. -/
theorem congr_one_sub_diagNormalize {size : ℕ} {diagEntry : Fin size → ℝ}
    (hpos : ∀ slot, 0 < diagEntry slot) (residual : Matrix (Fin size) (Fin size) ℝ) :
    (Matrix.diagonal (diagRoot diagEntry))ᵀ
        * ((1 : Matrix (Fin size) (Fin size) ℝ) - diagNormalize diagEntry residual)
        * Matrix.diagonal (diagRoot diagEntry)
      = Matrix.diagonal diagEntry - residual := by
  ext row col
  rw [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply,
    Matrix.sub_apply, Matrix.one_apply, diagNormalize_apply, Matrix.diagonal_apply]
  have hrowNe : diagRoot diagEntry row ≠ 0 := ne_of_gt (diagRoot_pos hpos row)
  have hcolNe : diagRoot diagEntry col ≠ 0 := ne_of_gt (diagRoot_pos hpos col)
  by_cases hslot : row = col
  · subst hslot
    rw [if_pos rfl, if_pos rfl]
    field_simp
    linarith [diagRoot_mul_self hpos row]
  · rw [if_neg hslot, if_neg hslot]
    field_simp
    ring

/-- **THE TRACE-AND-DETERMINANT LAW AGAINST A POSITIVE DIAGONAL.**  For a
positive diagonal `z` and a positive semidefinite `Y` of size three,

    `det (diag z - Y) >= 0`   and   `sum_c Y_cc / z_c <= 2`

force `diag z - Y >= 0`.  Two hypotheses replace the seven Sylvester conditions,
and neither of them is an eigenvalue.

This is the statement `Gtz/Wave/PencilTraceLaw.lean` advertises in its header
under the name `posSemidef_sub_of_det_nonneg_of_weightedTrace_le_two` and does
not contain. -/
theorem posSemidef_diagonal_sub_of_det_nonneg_of_weightedTrace_le_two
    {diagEntry : Fin 3 → ℝ} (hpos : ∀ slot, 0 < diagEntry slot)
    {residual : Matrix (Fin 3) (Fin 3) ℝ} (hres : residual.PosSemidef)
    (hdet : 0 ≤ (Matrix.diagonal diagEntry - residual).det)
    (htrace : ∑ slot, residual slot slot / diagEntry slot ≤ 2) :
    (Matrix.diagonal diagEntry - residual).PosSemidef := by
  set normalised := diagNormalize diagEntry residual with hnormalised
  have hrootPos : ∀ slot, 0 < diagRoot diagEntry slot := diagRoot_pos hpos
  have hrootDet : (0 : ℝ) < (Matrix.diagonal (diagRoot diagEntry)).det := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_pos fun slot _ => hrootPos slot
  have hunit : IsUnit (Matrix.diagonal (diagRoot diagEntry)).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hrootDet)
  have hnormPsd : normalised.PosSemidef := posSemidef_diagNormalize hpos hres
  -- the trace of the normalised residual is the weighted trace
  have htraceEq : Matrix.trace normalised = ∑ slot, residual slot slot / diagEntry slot := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun slot _ => ?_
    rw [Matrix.diag_apply, hnormalised, diagNormalize_apply]
    have hsq := diagRoot_mul_self hpos slot
    have hinv : (diagRoot diagEntry slot)⁻¹ * (diagRoot diagEntry slot)⁻¹
        = (diagEntry slot)⁻¹ := by rw [← mul_inv, hsq]
    calc (diagRoot diagEntry slot)⁻¹ * residual slot slot * (diagRoot diagEntry slot)⁻¹
        = residual slot slot
            * ((diagRoot diagEntry slot)⁻¹ * (diagRoot diagEntry slot)⁻¹) := by ring
      _ = residual slot slot / diagEntry slot := by rw [hinv, div_eq_mul_inv]
  -- the determinant of the normalised gap has the same sign
  have hcongr := congr_one_sub_diagNormalize hpos residual
  have hdetSplit : (Matrix.diagonal diagEntry - residual).det
      = (Matrix.diagonal (diagRoot diagEntry)).det ^ 2
        * ((1 : Matrix (Fin 3) (Fin 3) ℝ) - normalised).det := by
    rw [← hcongr, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hnormalised]
    ring
  have hdetNorm : 0 ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ) - normalised).det := by
    by_contra hneg
    push_neg at hneg
    have hsq : (0 : ℝ) < (Matrix.diagonal (diagRoot diagEntry)).det ^ 2 := by positivity
    nlinarith [hdetSplit, hdet, hneg, hsq]
  have hgap := posSemidef_one_sub_of_det_nonneg_of_trace_le_two hnormPsd hdetNorm
    (by rw [htraceEq]; exact htrace)
  have hsymm : ((1 : Matrix (Fin 3) (Fin 3) ℝ) - normalised)ᵀ = 1 - normalised := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hgap.1
  have hmoved := (posSemidef_congr_right (X := (1 : Matrix (Fin 3) (Fin 3) ℝ) - normalised)
    (P := Matrix.diagonal (diagRoot diagEntry)) hsymm hunit).mp hgap
  rwa [hcongr] at hmoved

/-- **THE DEFINITE VERSION.**  A strictly positive determinant upgrades the
conclusion: the weighted trace bound and a positive determinant force strict
domination. -/
theorem posDef_diagonal_sub_of_det_pos_of_weightedTrace_le_two
    {diagEntry : Fin 3 → ℝ} (hpos : ∀ slot, 0 < diagEntry slot)
    {residual : Matrix (Fin 3) (Fin 3) ℝ} (hres : residual.PosSemidef)
    (hdet : 0 < (Matrix.diagonal diagEntry - residual).det)
    (htrace : ∑ slot, residual slot slot / diagEntry slot ≤ 2) :
    (Matrix.diagonal diagEntry - residual).PosDef := by
  have hpsd := posSemidef_diagonal_sub_of_det_nonneg_of_weightedTrace_le_two hpos hres
    (le_of_lt hdet) htrace
  exact hpsd.posDef_iff_det_ne_zero.mpr (ne_of_gt hdet)

/-! ## Part 2 — the doubled co-leverage criterion

The design's chart gap block at a triple is a positive diagonal minus a block of
the complementary projection (`Gtz.projectionBlock_sub_weightDiagonal_eq_coWeight_sub_complementBlock`),
the diagonal is the CO-WEIGHTS, and the residual's diagonal entries divided by
that diagonal are exactly the co-leverage ratios.  Part 1 applies verbatim. -/

/-- **THE CHART GAP BLOCK** of a triple: the projection block minus the weight
diagonal.  Domination of the triple is its positive semidefiniteness. -/
noncomputable def tripleChartGap (D : WeightedDesign m 3) (selected : Finset (Fin m))
    (hcard : selected.card = 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (projectionOfDesign D).submatrix (selected.orderEmbOfFin hcard)
      (selected.orderEmbOfFin hcard)
    - Matrix.diagonal (fun slot => D.weight (selected.orderEmbOfFin hcard slot))

theorem dominates_iff_posSemidef_tripleChartGap (D : WeightedDesign m 3)
    (selected : Finset (Fin m)) (hcard : selected.card = 3) :
    Dominates D selected ↔ (tripleChartGap D selected hcard).PosSemidef :=
  dominates_iff_posSemidef_projectionBlock_finset D selected hcard

/-- The chart gap block written as a positive diagonal minus a positive
semidefinite residual. -/
theorem tripleChartGap_eq (D : WeightedDesign m 3) (selected : Finset (Fin m))
    (hcard : selected.card = 3) :
    tripleChartGap D selected hcard
      = Matrix.diagonal (fun slot => 1 - D.weight (selected.orderEmbOfFin hcard slot))
        - (complementProjection D).submatrix (selected.orderEmbOfFin hcard)
            (selected.orderEmbOfFin hcard) :=
  projectionBlock_sub_weightDiagonal_eq_coWeight_sub_complementBlock D _
    (selected.orderEmbOfFin hcard).injective

/-- The residual's weighted trace is the co-leverage ratio total of the triple. -/
theorem sum_complementBlock_div_coWeight (D : WeightedDesign m 3)
    (selected : Finset (Fin m)) (hcard : selected.card = 3) :
    (∑ slot, ((complementProjection D).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard)) slot slot
        / (1 - D.weight (selected.orderEmbOfFin hcard slot)))
      = ∑ atomIndex ∈ selected, coLeverageRatio D atomIndex := by
  have hentry : ∀ slot : Fin 3,
      ((complementProjection D).submatrix (selected.orderEmbOfFin hcard)
            (selected.orderEmbOfFin hcard)) slot slot
          / (1 - D.weight (selected.orderEmbOfFin hcard slot))
        = coLeverageRatio D (selected.orderEmbOfFin hcard slot) := by
    intro slot
    rw [Matrix.submatrix_apply, complementProjection_diagonal, coLeverageRatio]
  rw [Finset.sum_congr rfl fun slot _ => hentry slot,
    sum_orderEmbOfFin_eq_sum selected hcard]

/-- **THE DOUBLED CO-LEVERAGE CRITERION.**  At rank three, a triple whose
co-leverage ratios total at most TWO and whose chart gap block has nonnegative
determinant DOMINATES.

The landed `Gtz.dominates_of_sum_coLeverageRatio_le_one` stops at one and needs
no determinant.  This doubles the threshold and pays exactly one polynomial
sign, and on the range `(1, 2]` it is the only criterion the tree has. -/
theorem dominates_of_sum_coLeverageRatio_le_two (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (selected : Finset (Fin m)) (hcard : selected.card = 3)
    (hmass : ∑ atomIndex ∈ selected, coLeverageRatio D atomIndex ≤ 2)
    (hdet : 0 ≤ (tripleChartGap D selected hcard).det) :
    Dominates D selected := by
  rw [dominates_iff_posSemidef_tripleChartGap D selected hcard, tripleChartGap_eq D selected hcard]
  refine posSemidef_diagonal_sub_of_det_nonneg_of_weightedTrace_le_two
    (fun slot => by linarith [weight_lt_one D hm (selected.orderEmbOfFin hcard slot)])
    ((complementProjection_posSemidef D).submatrix (selected.orderEmbOfFin hcard))
    (by rwa [← tripleChartGap_eq D selected hcard]) ?_
  rw [sum_complementBlock_div_coWeight D selected hcard]
  exact hmass

/-- **THE STRICT DOUBLED CRITERION.**  A strictly positive determinant under the
same trace bound gives STRICT domination. -/
theorem posDef_tripleChartGap_of_sum_coLeverageRatio_le_two (D : WeightedDesign m 3)
    (hm : 2 ≤ m) (selected : Finset (Fin m)) (hcard : selected.card = 3)
    (hmass : ∑ atomIndex ∈ selected, coLeverageRatio D atomIndex ≤ 2)
    (hdet : 0 < (tripleChartGap D selected hcard).det) :
    (tripleChartGap D selected hcard).PosDef := by
  have hpsd := (dominates_iff_posSemidef_tripleChartGap D selected hcard).mp
    (dominates_of_sum_coLeverageRatio_le_two D hm selected hcard hmass (le_of_lt hdet))
  exact hpsd.posDef_iff_det_ne_zero.mpr (ne_of_gt hdet)

/-- **BELOW THE THRESHOLD, THE DETERMINANT SIGN IS EQUIVALENT TO DOMINATION.**
One direction is the criterion; the other is that a positive semidefinite matrix
has nonnegative determinant.  So under the trace bound the whole of domination
is ONE polynomial sign. -/
theorem dominates_iff_det_nonneg_of_sum_coLeverageRatio_le_two (D : WeightedDesign m 3)
    (hm : 2 ≤ m) (selected : Finset (Fin m)) (hcard : selected.card = 3)
    (hmass : ∑ atomIndex ∈ selected, coLeverageRatio D atomIndex ≤ 2) :
    Dominates D selected ↔ 0 ≤ (tripleChartGap D selected hcard).det := by
  constructor
  · intro hdom
    exact ((dominates_iff_posSemidef_tripleChartGap D selected hcard).mp hdom).det_nonneg
  · intro hdet
    exact dominates_of_sum_coLeverageRatio_le_two D hm selected hcard hmass hdet

/-! ## Part 3 — the co-leverage budget of an all-heavy design

The ratios carry an exact budget against the CO-weights.  Splitting the weight
off that budget turns it into a plain total, and heaviness caps every summand of
the correction by its own weight. -/

/-- **HEAVINESS IS THE RATIO BELOW ONE.**  An atom is strictly heavy exactly when
its co-leverage ratio is below one. -/
theorem coLeverageRatio_lt_one_iff (D : WeightedDesign m k) (hm : 2 ≤ m) (atomIndex : Fin m) :
    coLeverageRatio D atomIndex < 1 ↔ 1 < leverageOf (D.atom atomIndex) := by
  have hco : (0 : ℝ) < 1 - D.weight atomIndex := by
    linarith [weight_lt_one D hm atomIndex]
  have hclear := one_sub_weight_mul_coLeverageRatio D hm atomIndex
  have hweight := D.weight_pos atomIndex
  rw [coLeverageScore] at hclear
  constructor
  · intro hlt
    nlinarith [hclear, hlt, hco, hweight]
  · intro hheavy
    nlinarith [hclear, hheavy, hco, hweight]

/-- **THE RATIO TOTAL OF AN ALL-HEAVY DESIGN.**  The co-weighted budget is the
corank; splitting the weight off and capping each correction by its own weight
gives a plain total below `corank + 1`.

At `(6,3)` this reads `sum_c s_c < 4`, and that is the number the doubled
criterion needs. -/
theorem sum_coLeverageRatio_lt_of_allHeavy (D : WeightedDesign m k) (hm : 2 ≤ m)
    (hheavy : AllHeavy D) :
    (∑ atomIndex, coLeverageRatio D atomIndex) < (m : ℝ) - (k : ℝ) + 1 := by
  have hbudget := sum_one_sub_weight_mul_coLeverageRatio D hm
  have hsplit : (∑ atomIndex, coLeverageRatio D atomIndex)
      = ((m : ℝ) - (k : ℝ)) + ∑ atomIndex, D.weight atomIndex * coLeverageRatio D atomIndex := by
    rw [← hbudget, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => by ring
  have hcorrection : (∑ atomIndex, D.weight atomIndex * coLeverageRatio D atomIndex)
      < ∑ atomIndex : Fin m, D.weight atomIndex := by
    have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty := by
      rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset (Fin m)) with hempty | hne
      · exfalso
        have hsum := D.weight_sum_one
        rw [hempty, Finset.sum_empty] at hsum
        exact zero_ne_one hsum
      · exact hne
    refine Finset.sum_lt_sum_of_nonempty hnonempty fun atomIndex _ => ?_
    have hratio := (coLeverageRatio_lt_one_iff D hm atomIndex).mpr (hheavy atomIndex)
    nlinarith [D.weight_pos atomIndex, hratio]
  rw [D.weight_sum_one] at hcorrection
  linarith [hsplit, hcorrection]

/-- The `(6,3)` reading: the six co-leverage ratios of an all-heavy design total
strictly less than four. -/
theorem sum_coLeverageRatio_lt_four_of_allHeavy_sixThree (D : WeightedDesign 6 3)
    (hheavy : AllHeavy D) : (∑ atomIndex, coLeverageRatio D atomIndex) < 4 := by
  have hbound := sum_coLeverageRatio_lt_of_allHeavy D (by norm_num) hheavy
  norm_num at hbound
  exact hbound

/-- **A TRIPLE AND ITS COMPLEMENT CANNOT BOTH CARRY TWO.**  At an all-heavy
`(6,3)` design the six ratios total below four, so of any complementary pair of
triples at least one has ratio total below two — and the doubled criterion
applies to it. -/
theorem exists_compl_sum_coLeverageRatio_lt_two (D : WeightedDesign 6 3)
    (hheavy : AllHeavy D) (selected : Finset (Fin 6)) :
    (∑ atomIndex ∈ selected, coLeverageRatio D atomIndex) < 2
      ∨ (∑ atomIndex ∈ selectedᶜ, coLeverageRatio D atomIndex) < 2 := by
  by_contra hboth
  push_neg at hboth
  obtain ⟨hleft, hright⟩ := hboth
  have hsplit := Finset.sum_add_sum_compl selected (fun atomIndex => coLeverageRatio D atomIndex)
  have htotal := sum_coLeverageRatio_lt_four_of_allHeavy_sixThree D hheavy
  linarith [hsplit, htotal, hleft, hright]

/-- **THE COLLAPSE.**  Every all-heavy `(6,3)` design carries a triple at which
domination is EXACTLY the sign of one determinant.

`Gtz.hingeHoldsAtSize_six_three_of_allHeavy` says the all-heavy designs are the
whole open cell, so this is a statement about the residual and not about a
stratum of it. -/
theorem exists_triple_dominates_iff_tripleChartGapDet_nonneg (D : WeightedDesign 6 3)
    (hheavy : AllHeavy D) :
    ∃ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (∑ atomIndex ∈ selected, coLeverageRatio D atomIndex) < 2
        ∧ (Dominates D selected ↔ 0 ≤ (tripleChartGap D selected hcard).det) := by
  classical
  have hstart : (Finset.univ.filter fun label : Fin 6 => (label : ℕ) < 3).card = 3 := by decide
  set base : Finset (Fin 6) := Finset.univ.filter fun label : Fin 6 => (label : ℕ) < 3 with hbase
  rcases exists_compl_sum_coLeverageRatio_lt_two D hheavy base with hleft | hright
  · exact ⟨base, hstart, hleft,
      dominates_iff_det_nonneg_of_sum_coLeverageRatio_le_two D (by norm_num) base hstart
        (le_of_lt hleft)⟩
  · exact ⟨baseᶜ, card_compl_eq_three_of_card_eq_three base hstart, hright,
      dominates_iff_det_nonneg_of_sum_coLeverageRatio_le_two D (by norm_num) baseᶜ
        (card_compl_eq_three_of_card_eq_three base hstart) (le_of_lt hright)⟩

/-- **THE CRITERION FORM.**  Weighted GTZ on the all-heavy `(6,3)` designs
follows from ONE polynomial sign: the chart gap determinant at any triple whose
co-leverage ratios total below two.

`Gtz.hingeHoldsAtSize_six_three_of_allHeavy` says the all-heavy designs carry the
whole open cell, so this is the residual restated, not a stratum of it. -/
theorem gtzWeightedHeavy_six_three_of_tripleChartGapDet_nonneg
    (hdet : ∀ D : WeightedDesign 6 3, AllHeavy D →
      ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
        (∑ atomIndex ∈ selected, coLeverageRatio D atomIndex) < 2 →
        0 ≤ (tripleChartGap D selected hcard).det) :
    GtzWeightedHeavy 6 3 := by
  intro D hheavy
  obtain ⟨selected, hcard, hmass, hiff⟩ :=
    exists_triple_dominates_iff_tripleChartGapDet_nonneg D hheavy
  exact ⟨selected, hcard, hiff.mpr (hdet D hheavy selected hcard hmass)⟩

/-- **THE CHART GAP BLOCK IS THE BLOCK OF THE CHART GAP.**  `Gtz.tripleChartGap`
is `Gtz.chartGapOfDesign` restricted to the triple, so every law the tree states
about `M = P - diag t` reads directly on the collapsed determinant.

The complementary block law `Gtz.sixThree_complementary_block_law'` does NOT price
this determinant: it prices `det (M_C + diag t_C) = det P_C` against the
complementary block, which is a DIFFERENT number.  Recorded because the shapes are
one `diag t` apart and the confusion is easy to make. -/
theorem tripleChartGap_eq_chartGapOfDesign_submatrix (D : WeightedDesign m 3)
    (selected : Finset (Fin m)) (hcard : selected.card = 3) :
    tripleChartGap D selected hcard
      = (chartGapOfDesign D).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard) := by
  rw [tripleChartGap, chartGapOfDesign_submatrix D (selected.orderEmbOfFin hcard).injective]

/-! ## Part 4 — the seventh clause of a `(6,3)` counterexample

A tie refuses every STRICT dominator, so the collapsed determinant of Part 3
cannot be positive.  That is a clause on the residual whose shape is new: an
existential over triples carrying a polynomial sign. -/

/-- **STRICT DOMINATION IS THE DEFINITE CHART GAP BLOCK.**  The Finset reading of
`Gtz.posDef_gap_iff_posDef_projectionBlock`. -/
theorem posDef_gap_iff_posDef_tripleChartGap (D : WeightedDesign m 3)
    (selected : Finset (Fin m)) (hcard : selected.card = 3) :
    (subsetSum D selected - 1).PosDef ↔ (tripleChartGap D selected hcard).PosDef := by
  have hbridge := posDef_gap_iff_posDef_projectionBlock D (selected.orderEmbOfFin hcard)
    (selected.orderEmbOfFin hcard).injective
  have himage : Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  rwa [himage] at hbridge

/-- **A TIE FORCES THE COLLAPSED DETERMINANT NONPOSITIVE.**  Under the doubled
threshold, a positive determinant would be a strict dominator, which a tie
forbids. -/
theorem tripleChartGapDet_nonpos_of_isTie_of_sum_le_two (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (htie : IsTie D) (selected : Finset (Fin m)) (hcard : selected.card = 3)
    (hmass : ∑ atomIndex ∈ selected, coLeverageRatio D atomIndex ≤ 2) :
    (tripleChartGap D selected hcard).det ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  have hposDef := posDef_tripleChartGap_of_sum_coLeverageRatio_le_two D hm selected hcard
    hmass hpos
  exact htie.2 selected hcard ((posDef_gap_iff_posDef_tripleChartGap D selected hcard).mpr hposDef)

/-- **THE SEVENTH CLAUSE.**  Every all-heavy `(6,3)` tie carries a triple whose
co-leverage ratios total below two and whose chart gap block has NONPOSITIVE
determinant — and at that triple, domination is exactly the vanishing of that
determinant. -/
theorem exists_triple_tripleChartGapDet_nonpos_of_isTie_allHeavy (D : WeightedDesign 6 3)
    (hheavy : AllHeavy D) (htie : IsTie D) :
    ∃ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (∑ atomIndex ∈ selected, coLeverageRatio D atomIndex) < 2
        ∧ (tripleChartGap D selected hcard).det ≤ 0
        ∧ (Dominates D selected ↔ (tripleChartGap D selected hcard).det = 0) := by
  obtain ⟨selected, hcard, hmass, hiff⟩ :=
    exists_triple_dominates_iff_tripleChartGapDet_nonneg D hheavy
  have hnonpos := tripleChartGapDet_nonpos_of_isTie_of_sum_le_two D (by norm_num) htie
    selected hcard (le_of_lt hmass)
  refine ⟨selected, hcard, hmass, hnonpos, ?_⟩
  constructor
  · intro hdom
    exact le_antisymm hnonpos (hiff.mp hdom)
  · intro hzero
    exact hiff.mpr (le_of_eq hzero.symm)

/-! ## Part 5 — the package

The residual's hypotheses, assembled.  All-heaviness stops being an assumption
against primitivity, and the sharp dual of a primitive `(6,3)` tie is primitive
with no tie transport needed. -/

/-- **A PRIMITIVE `(6,3)` TIE IS ALL-HEAVY.**  The tie dichotomy leaves a unit
atom as the only alternative, and the funnel closure turns a unit atom into a
parallel pair.  The campaign carried all-heaviness as a HYPOTHESIS on the
residual; against primitivity it is a theorem. -/
theorem allHeavy_of_isPrimitiveDesign_of_isTie_sixThree (D : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign D) (htie : IsTie D) : AllHeavy D := by
  rcases allHeavy_or_exists_leverage_eq_one_of_isTie_sixThree D htie with hall | ⟨label, hunit⟩
  · exact hall
  · exact absurd (hasParallelPair_of_isTie_sixThree_of_unitAtom D htie label hunit)
      ((isPrimitiveDesign_iff_not_hasParallelPair D).mp hprimitive)

/-- Four labels of a primitive `(6,3)` tie are never coplanar.  `Gtz.FourCoplanar`
says the four brackets vanish; primitivity makes the cross axis of the first two
atoms a nonzero normal, and the two remaining brackets read the other two atoms
against it.  The landed `Gtz.card_coplanar_le_three_of_isPrimitiveDesign_of_isTie`
then closes it. -/
theorem not_fourCoplanar_of_isPrimitiveDesign_of_isTie (D : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign D) (htie : IsTie D) {x y z w : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hflat : FourCoplanar D x y z w) : False := by
  classical
  obtain ⟨hxyz, hxyw, -, -⟩ := hflat
  set normalVec := bracketNormal (D.atom x) (D.atom y) with hnormalVec
  have hnormalNe : normalVec ≠ 0 :=
    bracketNormal_atom_ne_zero_of_isPrimitiveDesign (by norm_num) D hprimitive x y hxy
  have hcoplanar : ∀ label ∈ ({x, y, z, w} : Finset (Fin 6)),
      D.atom label ⬝ᵥ normalVec = 0 := by
    intro label hlabel
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
    rcases hlabel with rfl | rfl | rfl | rfl
    · rw [dotProduct_comm, hnormalVec]; exact bracketNormal_dotProduct_left _ _
    · rw [dotProduct_comm, hnormalVec]; exact bracketNormal_dotProduct_right _ _
    · rw [dotProduct_comm, hnormalVec, ← tripleBracket_eq_bracketNormal_dotProduct]; exact hxyz
    · rw [dotProduct_comm, hnormalVec, ← tripleBracket_eq_bracketNormal_dotProduct]; exact hxyw
  have hcard : ({x, y, z, w} : Finset (Fin 6)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz, hxw]),
      Finset.card_insert_of_notMem (by simp [hyz, hyw]),
      Finset.card_insert_of_notMem (by simp [hzw]), Finset.card_singleton]
  have hbound := card_coplanar_le_three_of_isPrimitiveDesign_of_isTie D hprimitive htie
    ({x, y, z, w} : Finset (Fin 6)) hnormalNe hcoplanar
  omega

set_option maxRecDepth 20000 in
/-- Two distinct labels of a six-element ground set leave four, pairwise distinct
and distinct from the pair.  A finite check. -/
theorem exists_complementary_four (p q : Fin 6) (hpq : p ≠ q) :
    ∃ x y z w : Fin 6, x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w
      ∧ p ≠ x ∧ p ≠ y ∧ p ≠ z ∧ p ≠ w ∧ q ≠ x ∧ q ≠ y ∧ q ≠ z ∧ q ≠ w := by
  revert hpq
  revert p q
  decide

/-- **THE SHARP DUAL OF A PRIMITIVE `(6,3)` TIE IS PRIMITIVE.**  A parallel pair
of the sharp design is four coplanar atoms of the design
(`Gtz.fourCoplanar_iff_crossNormSq_naimarkSharpAtom`), and a primitive tie has
none.  No transport of `Gtz.IsTie` across the duality is used, so this needs
nothing the tree does not have. -/
theorem isPrimitiveDesign_naimarkSharpDesign_of_isPrimitiveDesign_of_isTie
    (D : WeightedDesign 6 3) (N : NaimarkDual D 3) (F : SharpFrame N) (hsix : (2 : ℕ) ≤ 6)
    (hprimitive : IsPrimitiveDesign D) (htie : IsTie D) :
    IsPrimitiveDesign (naimarkSharpDesign F hsix) := by
  classical
  rw [isPrimitiveDesign_iff_not_hasParallelPair]
  rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
  -- the sharp pair has vanishing area
  have harea : crossNormSq (naimarkSharpAtom F keptLabel) (naimarkSharpAtom F dropLabel) = 0 := by
    refine (crossNormSq_eq_zero_iff_dependent _ _).mpr (Or.inr ⟨ratio, ?_⟩)
    have hkept : (naimarkSharpDesign F hsix).atom keptLabel = naimarkSharpAtom F keptLabel := rfl
    have hdrop : (naimarkSharpDesign F hsix).atom dropLabel = naimarkSharpAtom F dropLabel := rfl
    rw [← hkept, ← hdrop]
    exact hparallel
  -- name the complementary four labels
  obtain ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, hpx, hpy, hpz, hpw, hqx, hqy, hqz, hqw⟩ :=
    exists_complementary_four keptLabel dropLabel hdistinct
  have hflat : FourCoplanar D x y z w :=
    (fourCoplanar_iff_crossNormSq_naimarkSharpAtom D N F hdistinct hpx hpy hpz hpw
      hqx hqy hqz hqw hxy hxz hxw hyz hyw hzw).mpr harea
  exact not_fourCoplanar_of_isPrimitiveDesign_of_isTie D hprimitive htie hxy hxz hxw hyz hyw hzw
    hflat

/-- **THE SHARPENED NORMAL FORM.**  The six unconditional clauses of
`Gtz.sixThree_primitiveTie_normalForm`, plus all-heaviness, plus the seventh
clause of Part 4.

INDEPENDENCE OF THE SEVENTH CLAUSE IS NOT PROVED and no separating design is
exhibited.  The clause is recorded as a clause, not as progress. -/
theorem sixThree_primitiveTie_sharpNormalForm (D : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign D) (htie : IsTie D) :
    AllHeavy D
      ∧ IsStressFreeDesign D
      ∧ HasNoCommonQuadric D.atom
      ∧ (∀ (coplanarSet : Finset (Fin 6)) (normalVec : Fin 3 → ℝ), normalVec ≠ 0 →
          (∀ label ∈ coplanarSet, D.atom label ⬝ᵥ normalVec = 0) → coplanarSet.card ≤ 3)
      ∧ (∑ label, (leverageOf (D.atom label))⁻¹) < 4
      ∧ (∑ label, (D.weight label * leverageOf (D.atom label)) ^ 2) ≤ 3
      ∧ (∑ label, coLeverageRatio D label) < 4
      ∧ ∃ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
          (∑ atomIndex ∈ selected, coLeverageRatio D atomIndex) < 2
            ∧ (tripleChartGap D selected hcard).det ≤ 0 := by
  have hheavy := allHeavy_of_isPrimitiveDesign_of_isTie_sixThree D hprimitive htie
  obtain ⟨hstress, hconic, hplane, _, hharmonic, hsecond⟩ :=
    sixThree_primitiveTie_normalForm D hprimitive htie
  obtain ⟨selected, hcard, hmass, hdet, _⟩ :=
    exists_triple_tripleChartGapDet_nonpos_of_isTie_allHeavy D hheavy htie
  exact ⟨hheavy, hstress, hconic, hplane, hharmonic, hsecond,
    sum_coLeverageRatio_lt_four_of_allHeavy_sixThree D hheavy,
    selected, hcard, hmass, hdet⟩

end Gtz
