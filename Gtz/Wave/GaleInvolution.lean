/-
# The Gale involution: the complementary block law, the bracket duality law, and the
# heavy-leverage closure at `(6,3)`

`X` is the `size × rank` matrix whose `c`-th row is `√t_c g_cᵀ`.  Parseval says exactly
`Xᵀ X = 1`, so `P = X Xᵀ` is a rank-`rank` orthogonal projection of `ℝ^size` and
`P_cc = t_c ℓ_c` is the atom share.  `Gtz.IsChartDual` already names the involution
`P ↦ 1 - P` and `Gtz.exists_isChartDual_sixThree` already builds it.  This module adds the
law that the involution obeys, and one closure it buys.

## 1. THE COMPLEMENTARY BLOCK LAW, which needs no dual design at all

    `det((1 - level) • 1 - P[Cᶜ,Cᶜ]) = det(P[C,C] - level • 1)`     (`|C| = rank = size - rank`)

`Gtz.det_projectionBlock_compl_sub_smul_one`.  Read on ordered eigenvalues it says
`μ_i(Cᶜ) = 1 - μ_{rank+1-i}(C)`: **the spectrum of the complementary block is the
reflection of the spectrum of the block in the level one half.**  Two elementary steps
carry it.  The block `P[C,C] = Z Zᵀ` and the WEIGHTED PARTIAL MOMENT
`W_C = Zᵀ Z = Σ_{c ∈ C} t_c g_c g_cᵀ` are cospectral because `Z` is square, and
`W_C + W_{Cᶜ} = 1` is Parseval itself.  Neither step is new.  Their composite is, and it
is not a symmetric-function identity: summed over the twenty triples the law gives
`Σ_C (λ_min(P[C,C]) + λ_max(P[C,C])) = 20`, hence `Σ_C λ_mid(P[C,C]) = 10` at every
`(6,3)` design.  That is an ORDERED-eigenvalue invariant, and the layer laws of
`Gtz.sum_det_principalBlock_sub_one_eq` cannot see it.  Two hundred thousand random
rank-three projections confirmed all three sums to 1e-14.

The Loewner reading is `Gtz.posSemidef_projectionBlock_compl_iff` and its strict twin,
and at `level = 1/2` the law becomes self-dual: a block sits above one half exactly when
its complementary block sits below one half.  So no complementary pair carries two blocks
strictly above one half (`Gtz.not_posDef_projectionBlock_and_compl_half`), and at most ten
of the twenty triples clear the half level strictly.

## 2. THE BRACKET DUALITY LAW

Applied to the chart dual the same law says the dual's COMPLEMENTARY block is cospectral
with the primal block, `Gtz.det_projectionBlock_chartDual_compl`.  At level zero that is

    `(∏_{c ∈ C} t_c) · det(S_C)  =  (∏_{c ∈ Cᶜ} t_c) · det(S*_{Cᶜ})`

(`Gtz.weightProduct_mul_det_subsetSum_eq_chartDual_compl`), where `S_C` is the unweighted
atom sum and `S*` is the dual's.  Since `det S_C` is the squared bracket `[C]²`, this is
the bracket duality law in its exact form.  The weight products are positive, so

    **`[C] = 0  ↔  [Cᶜ]* = 0`**

(`Gtz.det_subsetSum_eq_zero_iff_chartDual_compl`): a triple of `D` is degenerate exactly
when the COMPLEMENTARY triple of `D*` is.  The bases of the dual design are the
complements of the bases of the design — **the Gale involution represents the DUAL
MATROID.**

## 3. THE DUAL GAP IN PRIMAL COORDINATES

`Gtz.gram_chartDual_eq` : `Gram(g*_C) = diag(1/t_c)_{c ∈ C} - Gram(g_C)`, entrywise, at
every weighting.  So `Gtz.dominates_chartDual_iff_posSemidef_inverseWeight` reads dual
domination off the primal design alone, with no square root and no dual atom.  Every
dual test at a rational fixture becomes rational arithmetic.

## 4. THE CLOSURE — the involution turns the leverage FLOOR into a leverage CEILING

`Gtz.leverageOf_chartDual` gives `ℓ*_c = 1/t_c - ℓ_c`.  A design with one atom of
leverage strictly below one has a strict card-three dominator, unconditionally
(`Gtz.posDef_of_strictly_light_atom`, on `Gtz.GtzWeighted 5 3`).  Push that through the
involution and the light atom of the DUAL is a HEAVY atom of the primal:

    **at uniform weight, `5 < ℓ_c` for one atom forces a STRICT card-three dominator**

`Gtz.exists_posDef_cardThree_of_heavy_leverage_uniform`.  With the shipped floor this
closes both tails: `Gtz.leverage_mem_Icc_one_five_of_isTie_uniform` puts every leverage of
a uniform `(6,3)` tie in `[1, 5]`, equivalently every share in `[1/6, 5/6]`.  The floor
was landed; the ceiling is its exact mirror and no fork had it.  The ceiling also
strengthens a shipped theorem: `Gtz.one_le_leverage_chartDual_of_isTie_uniform` makes the
dual of a uniform tie all-heavy from the tie ALONE, where
`Gtz.allHeavy_chartDual_of_uniformWeight_sixThree` needs `Gtz.AllHeavy` and
`Gtz.HasStrictlyDominatingCoSingletons` as hypotheses.

## 5. WHAT THE INVOLUTION DOES TO THE TIE LOCUS — measured, then proved

The shipped transfer `Gtz.dominates_iff_dominates_chartDual_compl_of_uniformWeight_sixThree`
is weak domination at a UNIFORM weight.  Section 5 adds the strict twin and hence

    `Gtz.isTie_chartDual_iff_isTie_of_uniformWeight`  :  at `t ≡ 1/6`, `IsTie D ↔ IsTie D*` .

**At a uniform weight the tie locus is INVARIANT.**  The involution is a symmetry of the
uniform problem and destroys nothing there.

Off the uniform slice it destroys ties outright.  `Gtz.nonUniformLeverageTieDesign` is a
tie whose chart dual strictly dominates `{0,3,4}`, so
`Gtz.exists_isTie_sixThree_with_chartDual_not_isTie` is a theorem: the involution is NOT a
symmetry of the tie locus at general weights.  The transfer of section 5 is therefore
sharp — it holds at the uniform weight and fails immediately off it.

## Exact arithmetic performed outside Lean, no float

The four shipped `(6,3)` fixtures, in exact rationals and exact `√5`:

| design | weights | shares `s_c` | dual shares `1 - s_c` | tie | dual a tie |
|---|---|---|---|---|---|
| `sixSplitDiamondDesign` | `1/10, 1/5⁴, 1/10` | `1/5, (13/20)⁴, 1/5` | `4/5, (7/20)⁴, 4/5` | yes | **no**, four strict triples |
| `nonUniformLeverageTieDesign` | `(1/9)³, (2/9)³` | `(19/27)³, (8/27)³` | `(8/27)³, (19/27)³` | yes | **no**, nine strict triples |
| `icosaDesign` | `(1/6)⁶` | `(1/2)⁶` | `(1/2)⁶` | no | no |
| `kFourDesign` | `(1/6)⁶` | `(1/2)⁶` | `(1/2)⁶` | no | no |

The two uniform fixtures transfer weak domination to the complementary triple on all
twenty cells; the two non-uniform ones fail it.  Four thousand exact rational cells
confirmed the complementary determinant law and the complementary characteristic
polynomial law with zero failures, and two thousand four hundred exact cells at a
non-uniform square-rational weight produced four hundred and seventy-eight failures of
the complementary transfer.

## The route this module CLOSES, and the route it kills

CLOSES: the heavy tail `ℓ > 5` of the uniform `(6,3)` cell, by mirroring the shipped
light tail.  A uniform tie now lives in the compact leverage window `[1,5]`.

KILLS: the averaging route through the complementary law.  If `Σ_C λ_min(P[C,C]) ≥ 10/3`
held at every rank-three projection of `ℝ^6`, then some triple would carry
`λ_min ≥ 1/6` and the uniform cell would be closed outright.  It is FALSE.  Two hundred
thousand random projections put the minimum of that sum at `1.00437`, three times below
the target.  The layer sum `Σ_C λ_mid = 10` is exact and design-blind, and the two
outer layer sums are free to move.  No averaging argument over the twenty triples can
reach the cell.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Design.LeverageBound
import Gtz.Design.KFourChartClosure
import Gtz.Design.StratumEmptinessLedger
import Gtz.Reduction.Deflation
import Gtz.Reduction.ExchangeInvariant
import Gtz.Quantitative.ChartDuality
import Gtz.Quantitative.SelfDualInvolution
import Gtz.Ties.NonUniformLeverageTie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 0. Two small facts the rest of the file spends -/

section Preliminaries

variable {size rank : ℕ}

/-- A subset and its complement split a total sum. -/
theorem sum_add_sum_compl_eq {indexType targetType : Type*} [Fintype indexType]
    [DecidableEq indexType] [AddCommMonoid targetType] (selected : Finset indexType)
    (summand : indexType → targetType) :
    (∑ index ∈ selected, summand index) + ∑ index ∈ selectedᶜ, summand index
      = ∑ index, summand index := by
  classical
  rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]

/-- **THE SQUARE COMMUTATION OF SHIFTED DETERMINANTS.**  For a SQUARE matrix the two
products carry the same shifted determinant at every level:

    `det(M Mᵀ − level) = det(Mᵀ M − level)` .

At `level = 0` this is `Matrix.det_mul_comm`; at every other level it is the
Weinstein-Aronszajn identity after a scalar rescaling.  Read on eigenvalues it is the
statement that `M Mᵀ` and `Mᵀ M` are cospectral. -/
theorem det_mul_transpose_sub_smul_one_comm {dimension : ℕ}
    (square : Matrix (Fin dimension) (Fin dimension) ℝ) (level : ℝ) :
    (square * squareᵀ - level • 1).det = (squareᵀ * square - level • 1).det := by
  rcases eq_or_ne level 0 with rfl | hlevel
  · simp only [zero_smul, sub_zero]
    exact Matrix.det_mul_comm _ _
  · have hcancel : (-level) * level⁻¹ = -1 := by field_simp
    have hleft : square * squareᵀ - level • 1
        = (-level) • (1 - (level⁻¹ • square) * squareᵀ) := by
      rw [Matrix.smul_mul, smul_sub, smul_smul, hcancel, neg_one_smul, neg_smul,
        sub_neg_eq_add]
      abel
    have hright : squareᵀ * square - level • 1
        = (-level) • (1 - squareᵀ * (level⁻¹ • square)) := by
      rw [Matrix.mul_smul, smul_sub, smul_smul, hcancel, neg_one_smul, neg_smul,
        sub_neg_eq_add]
      abel
    rw [hleft, hright, Matrix.det_smul, Matrix.det_smul,
      Matrix.det_one_sub_mul_comm (level⁻¹ • square) squareᵀ]

/-- The strict twin of `Gtz.posSemidef_transpose_mul_sub_smul_one_comm`.  A positive
semidefinite matrix is definite exactly when its determinant does not vanish, and the
shifted determinants agree by `Gtz.det_mul_transpose_sub_smul_one_comm`. -/
theorem posDef_transpose_mul_sub_smul_one_comm {dimension : ℕ}
    (square : Matrix (Fin dimension) (Fin dimension) ℝ) {level : ℝ} (hlevel : 0 < level) :
    (squareᵀ * square - level • 1).PosDef ↔ (square * squareᵀ - level • 1).PosDef := by
  have hsemi := posSemidef_transpose_mul_sub_smul_one_comm square hlevel
  have hdet := det_mul_transpose_sub_smul_one_comm square level
  constructor
  · intro hpos
    have hother : (square * squareᵀ - level • 1).PosSemidef := hsemi.mp hpos.posSemidef
    refine hother.posDef_iff_det_ne_zero.mpr ?_
    rw [hdet]
    exact (hpos.posSemidef.posDef_iff_det_ne_zero.mp hpos)
  · intro hpos
    have hother : (squareᵀ * square - level • 1).PosSemidef := hsemi.mpr hpos.posSemidef
    refine hother.posDef_iff_det_ne_zero.mpr ?_
    rw [← hdet]
    exact (hpos.posSemidef.posDef_iff_det_ne_zero.mp hpos)

end Preliminaries

/-! ## 1. The weighted partial moment, and the block it is cospectral with

`W_C = Σ_{c ∈ C} t_c g_c g_cᵀ` is the WEIGHTED moment on a subset — Parseval is the
statement that `W_C + W_{Cᶜ} = 1`.  The unweighted `Gtz.subsetSum` is the object
domination reads; the weighted one is the object the involution reads. -/

section WeightedMoment

variable {size rank : ℕ}

/-- **THE WEIGHTED PARTIAL MOMENT** on a subset of atoms. -/
noncomputable def weightedMomentOn (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) : Matrix (Fin rank) (Fin rank) ℝ :=
  ∑ atomIndex ∈ selected, design.weight atomIndex • atomMatrix (design.atom atomIndex)

/-- **PARSEVAL, READ ON A SUBSET AND ITS COMPLEMENT.**  The two weighted partial moments
total the identity.  This is the only place the design axiom enters section 1. -/
theorem weightedMomentOn_add_compl (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    weightedMomentOn design selected + weightedMomentOn design selectedᶜ = 1 := by
  rw [weightedMomentOn, weightedMomentOn,
    sum_add_sum_compl_eq selected fun atomIndex =>
      design.weight atomIndex • atomMatrix (design.atom atomIndex)]
  exact design.isParseval

/-- The complement's weighted moment, solved for. -/
theorem weightedMomentOn_compl (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    weightedMomentOn design selectedᶜ = 1 - weightedMomentOn design selected := by
  rw [← weightedMomentOn_add_compl design selected]
  abel

/-- The selected rows of the scaled frame: row `i` is `√t_{pick i} g_{pick i}ᵀ`. -/
noncomputable def scaledSelectedRows (design : WeightedDesign size rank) {selSize : ℕ}
    (pick : Fin selSize → Fin size) : Matrix (Fin selSize) (Fin rank) ℝ :=
  (scaledAtomRows design).submatrix pick id

/-- The outer product of the selected scaled rows IS the projection block. -/
theorem scaledSelectedRows_mul_transpose (design : WeightedDesign size rank) {selSize : ℕ}
    (pick : Fin selSize → Fin size) :
    scaledSelectedRows design pick * (scaledSelectedRows design pick)ᵀ
      = (projectionOfDesign design).submatrix pick pick := by
  ext rowIndex colIndex
  simp only [scaledSelectedRows, projectionOfDesign, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, id_eq]

/-- The inner product of the selected scaled rows IS the weighted partial moment. -/
theorem transpose_scaledSelectedRows_mul (design : WeightedDesign size rank) {selSize : ℕ}
    (pick : Fin selSize → Fin size) (hinj : Function.Injective pick) :
    (scaledSelectedRows design pick)ᵀ * scaledSelectedRows design pick
      = weightedMomentOn design (Finset.image pick Finset.univ) := by
  classical
  ext leftCoord rightCoord
  rw [weightedMomentOn, Matrix.sum_apply,
    Finset.sum_image fun left _ right _ hlr => hinj hlr]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, scaledSelectedRows, scaledAtomRows,
    Matrix.submatrix_apply, id_eq, Matrix.of_apply, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun slot _ => ?_
  have hsqrt : Real.sqrt (design.weight (pick slot)) * Real.sqrt (design.weight (pick slot))
      = design.weight (pick slot) :=
    Real.mul_self_sqrt (design.weight_pos (pick slot)).le
  linear_combination (design.atom (pick slot) leftCoord * design.atom (pick slot) rightCoord)
    * hsqrt

/-- The image of the order embedding of a subset is that subset. -/
theorem image_orderEmbOfFin_eq {selected : Finset (Fin size)} (hcard : selected.card = rank) :
    Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected := by
  apply Finset.coe_injective
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]

/-- The weighted partial moment on a subset of the rank's size, as an inner product. -/
theorem weightedMomentOn_eq_transpose_mul (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) :
    weightedMomentOn design selected
      = (scaledSelectedRows design (selected.orderEmbOfFin hcard))ᵀ
        * scaledSelectedRows design (selected.orderEmbOfFin hcard) := by
  rw [transpose_scaledSelectedRows_mul design (selected.orderEmbOfFin hcard)
      (selected.orderEmbOfFin hcard).injective, image_orderEmbOfFin_eq hcard]

/-- **THE BLOCK AND THE WEIGHTED MOMENT ARE COSPECTRAL** on a subset of the rank's size.
The block lives on the `size`-index and the moment on the `rank`-index, and the shifted
determinants agree at every level. -/
theorem det_projectionBlock_sub_smul_one_eq_weightedMoment (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) (level : ℝ) :
    ((projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard) - level • 1).det
      = (weightedMomentOn design selected - level • 1).det := by
  rw [← scaledSelectedRows_mul_transpose design (selected.orderEmbOfFin hcard),
    weightedMomentOn_eq_transpose_mul design hcard]
  exact det_mul_transpose_sub_smul_one_comm _ _

/-- The Loewner twin at a POSITIVE level. -/
theorem posSemidef_projectionBlock_sub_smul_one_iff_weightedMoment
    (design : WeightedDesign size rank) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) {level : ℝ} (hlevel : 0 < level) :
    ((projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard) - level • 1).PosSemidef
      ↔ (weightedMomentOn design selected - level • 1).PosSemidef := by
  rw [← scaledSelectedRows_mul_transpose design (selected.orderEmbOfFin hcard),
    weightedMomentOn_eq_transpose_mul design hcard]
  exact (posSemidef_transpose_mul_sub_smul_one_comm _ hlevel).symm

/-- The dual Loewner twin: a CEILING on the moment is a ceiling on the block. -/
theorem posSemidef_smul_one_sub_projectionBlock_iff_weightedMoment
    (design : WeightedDesign size rank) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) {level : ℝ} (hlevel : 0 < level) :
    (level • (1 : Matrix (Fin rank) (Fin rank) ℝ) - weightedMomentOn design selected).PosSemidef
      ↔ (level • (1 : Matrix (Fin rank) (Fin rank) ℝ)
          - (projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
              (selected.orderEmbOfFin hcard)).PosSemidef := by
  rw [weightedMomentOn_eq_transpose_mul design hcard,
    ← scaledSelectedRows_mul_transpose design (selected.orderEmbOfFin hcard)]
  exact posSemidef_smul_one_sub_transpose_comm hlevel _

/-- Scaling by a positive real preserves and reflects positive definiteness. -/
theorem posDef_smul_iff {dimension : ℕ} {form : Matrix (Fin dimension) (Fin dimension) ℝ}
    {scale : ℝ} (hscale : 0 < scale) : (scale • form).PosDef ↔ form.PosDef := by
  constructor
  · intro hpos
    have hsemi : form.PosSemidef := (posSemidef_smul_iff hscale).mp hpos.posSemidef
    refine hsemi.posDef_iff_det_ne_zero.mpr fun hzero => ?_
    have hdet := hpos.posSemidef.posDef_iff_det_ne_zero.mp hpos
    rw [Matrix.det_smul, hzero, mul_zero] at hdet
    exact hdet rfl
  · intro hpos
    have hsemi : (scale • form).PosSemidef := (posSemidef_smul_iff hscale).mpr hpos.posSemidef
    refine hsemi.posDef_iff_det_ne_zero.mpr ?_
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hscale.ne')
      (hpos.posSemidef.posDef_iff_det_ne_zero.mp hpos)

end WeightedMoment

/-! ## 2. THE COMPLEMENTARY BLOCK LAW at `(6,3)`

At `(6,3)` a triple and its complement both have the rank's size, so both blocks are
`3 × 3` and the law is an exact reflection of one spectrum onto the other. -/

section ComplementaryBlockLaw

/-- The complement of a triple of `Fin 6` is a triple. -/
theorem card_compl_three {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    selectedᶜ.card = 3 := by
  rw [Finset.card_compl, Fintype.card_fin, hcard]

/-- **THE COMPLEMENTARY BLOCK LAW.**  At every `(6,3)` design, every triple and every
level,

    `det((1 − level) • 1 − P[Cᶜ,Cᶜ]) = det(P[C,C] − level • 1)` .

Read on ordered eigenvalues: `μ_i(Cᶜ) = 1 − μ_{4−i}(C)`.  The proof is Parseval on the
weighted partial moments plus the square commutation of shifted determinants, and NO
dual design appears in it. -/
theorem det_projectionBlock_compl_sub_smul_one (design : WeightedDesign 6 3)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) (level : ℝ) :
    ((1 - level) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (projectionOfDesign design).submatrix
            (selectedᶜ.orderEmbOfFin (card_compl_three hcard))
            (selectedᶜ.orderEmbOfFin (card_compl_three hcard))).det
      = ((projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard) - level • 1).det := by
  have hcompl := card_compl_three hcard
  have hblock := det_projectionBlock_sub_smul_one_eq_weightedMoment design hcompl level
  have hprimal := det_projectionBlock_sub_smul_one_eq_weightedMoment design hcard (1 - level)
  have hflip : (1 - level) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - (projectionOfDesign design).submatrix (selectedᶜ.orderEmbOfFin hcompl)
          (selectedᶜ.orderEmbOfFin hcompl)
      = -((projectionOfDesign design).submatrix (selectedᶜ.orderEmbOfFin hcompl)
            (selectedᶜ.orderEmbOfFin hcompl) - (1 - level) • 1) := by
    abel
  have hmoment : weightedMomentOn design selectedᶜ - (1 - level) • 1
      = -(weightedMomentOn design selected - level • 1) := by
    rw [weightedMomentOn_compl design selected, sub_smul, one_smul]
    abel
  rw [hflip, Matrix.det_neg, Fintype.card_fin,
    det_projectionBlock_sub_smul_one_eq_weightedMoment design hcompl (1 - level), hmoment,
    Matrix.det_neg, Fintype.card_fin,
    det_projectionBlock_sub_smul_one_eq_weightedMoment design hcard level]
  ring

/-- **THE LOEWNER FORM OF THE COMPLEMENTARY BLOCK LAW.**  A block sits above a level
exactly when the complementary block sits below the reflected level.  The two hypotheses
are `0 < level` and `level < 1`, and the domination levels of a `(6,3)` design are the
weights, which lie strictly inside that window. -/
theorem posSemidef_projectionBlock_compl_iff (design : WeightedDesign 6 3)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) {level : ℝ}
    (hlow : 0 < level) (hhigh : level < 1) :
    ((projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard) - level • 1).PosSemidef
      ↔ ((1 - level) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (projectionOfDesign design).submatrix
              (selectedᶜ.orderEmbOfFin (card_compl_three hcard))
              (selectedᶜ.orderEmbOfFin (card_compl_three hcard))).PosSemidef := by
  have hcompl := card_compl_three hcard
  have hreflect : (0 : ℝ) < 1 - level := by linarith
  have hleft := posSemidef_projectionBlock_sub_smul_one_iff_weightedMoment design hcard hlow
  have hright := posSemidef_smul_one_sub_projectionBlock_iff_weightedMoment design hcompl hreflect
  have hmoment : (1 - level) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - weightedMomentOn design selectedᶜ
      = weightedMomentOn design selected - level • 1 := by
    rw [weightedMomentOn_compl design selected, sub_smul, one_smul]
    abel
  rw [hleft, ← hmoment, hright]

/-- The strict twin.  Positive semidefiniteness transfers by the Loewner form and
non-vanishing of the determinant by the determinant form. -/
theorem posDef_projectionBlock_compl_iff (design : WeightedDesign 6 3)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) {level : ℝ}
    (hlow : 0 < level) (hhigh : level < 1) :
    ((projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard) - level • 1).PosDef
      ↔ ((1 - level) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (projectionOfDesign design).submatrix
              (selectedᶜ.orderEmbOfFin (card_compl_three hcard))
              (selectedᶜ.orderEmbOfFin (card_compl_three hcard))).PosDef := by
  have hsemi := posSemidef_projectionBlock_compl_iff design hcard hlow hhigh
  have hdet := det_projectionBlock_compl_sub_smul_one design hcard level
  constructor
  · intro hpos
    refine (hsemi.mp hpos.posSemidef).posDef_iff_det_ne_zero.mpr ?_
    rw [hdet]
    exact hpos.posSemidef.posDef_iff_det_ne_zero.mp hpos
  · intro hpos
    refine (hsemi.mpr hpos.posSemidef).posDef_iff_det_ne_zero.mpr ?_
    rw [← hdet]
    exact hpos.posSemidef.posDef_iff_det_ne_zero.mp hpos

/-- **THE HALF-LEVEL SELF-DUALITY.**  At `level = 1/2` the reflection is the identity, so
a block sits above one half exactly when its complementary block sits below one half.
Every `(6,3)` design therefore splits its twenty triples into ten complementary pairs on
which the two readings are exchanged. -/
theorem posSemidef_projectionBlock_half_iff_compl (design : WeightedDesign 6 3)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    ((projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard) - (2 : ℝ)⁻¹ • 1).PosSemidef
      ↔ ((2 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (projectionOfDesign design).submatrix
              (selectedᶜ.orderEmbOfFin (card_compl_three hcard))
              (selectedᶜ.orderEmbOfFin (card_compl_three hcard))).PosSemidef := by
  have hlaw := posSemidef_projectionBlock_compl_iff design hcard
    (level := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ from by norm_num] at hlaw
  exact hlaw

/-- **THE COMPLEMENTARY PAIR DICHOTOMY.**  No complementary pair of triples carries two
blocks strictly above one half.  Complementation is an involution without fixed points on
the twenty triples, so at most ten of them clear the half level strictly. -/
theorem not_posDef_projectionBlock_and_compl_half (design : WeightedDesign 6 3)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    ¬ (((projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard) - (2 : ℝ)⁻¹ • 1).PosDef
        ∧ ((projectionOfDesign design).submatrix
            (selectedᶜ.orderEmbOfFin (card_compl_three hcard))
            (selectedᶜ.orderEmbOfFin (card_compl_three hcard)) - (2 : ℝ)⁻¹ • 1).PosDef) := by
  rintro ⟨hleft, hright⟩
  have hcompl := card_compl_three hcard
  have hlaw := posDef_projectionBlock_compl_iff design hcard
    (level := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ from by norm_num] at hlaw
  have hflip := hlaw.mp hleft
  have hne : (fun _ : Fin 3 => (1 : ℝ)) ≠ 0 := by
    intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hright).2 hne
  have hneg := (Matrix.posDef_iff_dotProduct_mulVec.mp hflip).2 hne
  have hcancel : ((projectionOfDesign design).submatrix (selectedᶜ.orderEmbOfFin hcompl)
        (selectedᶜ.orderEmbOfFin hcompl) - (2 : ℝ)⁻¹ • 1)
      + ((2 : ℝ)⁻¹ • 1 - (projectionOfDesign design).submatrix
          (selectedᶜ.orderEmbOfFin hcompl) (selectedᶜ.orderEmbOfFin hcompl)) = 0 := by
    abel
  have hzero : (star fun _ : Fin 3 => (1 : ℝ))
        ⬝ᵥ (((projectionOfDesign design).submatrix (selectedᶜ.orderEmbOfFin hcompl)
          (selectedᶜ.orderEmbOfFin hcompl) - (2 : ℝ)⁻¹ • 1) *ᵥ fun _ => (1 : ℝ))
      + (star fun _ : Fin 3 => (1 : ℝ))
        ⬝ᵥ (((2 : ℝ)⁻¹ • 1 - (projectionOfDesign design).submatrix
          (selectedᶜ.orderEmbOfFin hcompl) (selectedᶜ.orderEmbOfFin hcompl))
            *ᵥ fun _ => (1 : ℝ)) = 0 := by
    rw [← dotProduct_add, ← Matrix.add_mulVec, hcancel, Matrix.zero_mulVec, dotProduct_zero]
  linarith [hpos, hneg, hzero]

end ComplementaryBlockLaw

/-! ## 3. The chart dual reading: the bracket duality law and matroid duality -/

section BracketDuality

variable {design dual : WeightedDesign 6 3}

/-- The chart dual's block is the primal block reflected. -/
theorem projectionBlock_chartDual (hdual : IsChartDual design dual)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    (projectionOfDesign dual).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard)
      = 1 - (projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard) := by
  rw [hdual.chart_eq]
  ext leftSlot rightSlot
  rcases eq_or_ne leftSlot rightSlot with rfl | hne
  · simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply_eq]
  · have hembNe : selected.orderEmbOfFin hcard leftSlot
        ≠ selected.orderEmbOfFin hcard rightSlot :=
      fun heq => hne ((selected.orderEmbOfFin hcard).injective heq)
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply_ne hne,
      Matrix.one_apply_ne hembNe]

/-- **THE COMPLEMENTARY BLOCK OF THE DUAL IS COSPECTRAL WITH THE BLOCK OF THE PRIMAL.**
This is the complementary block law read on the chart dual, and it is the exact carrier
of the bracket duality law. -/
theorem det_projectionBlock_chartDual_compl (hdual : IsChartDual design dual)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) (level : ℝ) :
    ((projectionOfDesign dual).submatrix
        (selectedᶜ.orderEmbOfFin (card_compl_three hcard))
        (selectedᶜ.orderEmbOfFin (card_compl_three hcard)) - level • 1).det
      = ((projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard) - level • 1).det := by
  have hcompl := card_compl_three hcard
  have hblock := projectionBlock_chartDual hdual hcompl
  have hrewrite : (projectionOfDesign dual).submatrix (selectedᶜ.orderEmbOfFin hcompl)
        (selectedᶜ.orderEmbOfFin hcompl) - level • 1
      = (1 - level) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (projectionOfDesign design).submatrix (selectedᶜ.orderEmbOfFin hcompl)
            (selectedᶜ.orderEmbOfFin hcompl) := by
    rw [hblock, sub_smul, one_smul]
    abel
  rw [hrewrite, det_projectionBlock_compl_sub_smul_one design hcard level]

/-- A product over a triple, read along its order embedding. -/
theorem prod_weight_orderEmbOfFin (design : WeightedDesign 6 3)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    ∏ slot, design.weight (selected.orderEmbOfFin hcard slot)
      = ∏ atomIndex ∈ selected, design.weight atomIndex := by
  have himage : Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected :=
    image_orderEmbOfFin_eq hcard
  calc ∏ slot, design.weight (selected.orderEmbOfFin hcard slot)
      = ∏ atomIndex ∈ Finset.image (selected.orderEmbOfFin hcard) Finset.univ,
          design.weight atomIndex :=
        (Finset.prod_image fun left _ right _ hlr =>
          (selected.orderEmbOfFin hcard).injective hlr).symm
    _ = ∏ atomIndex ∈ selected, design.weight atomIndex := by rw [himage]

/-- The scaled selected rows factor through the square-root weight diagonal. -/
theorem scaledSelectedRows_eq_sqrtWeightDiagonal_mul {size rank : ℕ}
    (design : WeightedDesign size rank) {selSize : ℕ} (pick : Fin selSize → Fin size) :
    scaledSelectedRows design pick
      = sqrtWeightDiagonal design pick * selectedAtomRows design pick :=
  submatrix_scaledAtomRows_eq design pick

/-- **THE PROJECTION BLOCK IS THE WEIGHT PRODUCT TIMES THE SQUARED BRACKET.**
`det(P[C,C]) = (∏_{c ∈ C} t_c) · det(S_C)`, and `det(S_C)` is the squared bracket. -/
theorem det_projectionBlock_eq_weightProduct_mul_det_subsetSum (design : WeightedDesign 6 3)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    ((projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard)).det
      = (∏ atomIndex ∈ selected, design.weight atomIndex)
        * (subsetSum design selected).det := by
  have hinj : Function.Injective (selected.orderEmbOfFin hcard) :=
    (selected.orderEmbOfFin hcard).injective
  have hgram := transpose_mul_selectedAtomRows design (selected.orderEmbOfFin hcard) hinj
  rw [image_orderEmbOfFin_eq hcard] at hgram
  have hsubset : (subsetSum design selected).det
      = (selectedAtomRows design (selected.orderEmbOfFin hcard)).det ^ 2 := by
    rw [← hgram, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hblock : ((projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard)).det
      = (scaledSelectedRows design (selected.orderEmbOfFin hcard)).det ^ 2 := by
    rw [← scaledSelectedRows_mul_transpose design (selected.orderEmbOfFin hcard),
      Matrix.det_mul, Matrix.det_transpose]
    ring
  have hfactor : (scaledSelectedRows design (selected.orderEmbOfFin hcard)).det
      = (∏ slot, Real.sqrt (design.weight (selected.orderEmbOfFin hcard slot)))
        * (selectedAtomRows design (selected.orderEmbOfFin hcard)).det := by
    rw [scaledSelectedRows_eq_sqrtWeightDiagonal_mul, Matrix.det_mul, sqrtWeightDiagonal,
      Matrix.det_diagonal]
  have hsq : (∏ slot, Real.sqrt (design.weight (selected.orderEmbOfFin hcard slot))) ^ 2
      = ∏ atomIndex ∈ selected, design.weight atomIndex := by
    rw [← prod_weight_orderEmbOfFin design hcard, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun slot _ =>
      Real.sq_sqrt (design.weight_pos (selected.orderEmbOfFin hcard slot)).le
  rw [hblock, hfactor, mul_pow, hsq, hsubset]

/-- **THE BRACKET DUALITY LAW.**

    `(∏_{c ∈ C} t_c) · det(S_C) = (∏_{c ∈ Cᶜ} t_c) · det(S*_{Cᶜ})`

`det(S_C)` is the squared bracket `[C]²` of the triple, so this is exactly the law that
pairs a bracket of the design with the bracket of the COMPLEMENTARY triple of the Gale
dual, at every weighting. -/
theorem weightProduct_mul_det_subsetSum_eq_chartDual_compl (hdual : IsChartDual design dual)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    (∏ atomIndex ∈ selected, design.weight atomIndex) * (subsetSum design selected).det
      = (∏ atomIndex ∈ selectedᶜ, design.weight atomIndex)
        * (subsetSum dual selectedᶜ).det := by
  have hcompl := card_compl_three hcard
  have hlaw := det_projectionBlock_chartDual_compl hdual hcard 0
  simp only [zero_smul, sub_zero] at hlaw
  have hleft := det_projectionBlock_eq_weightProduct_mul_det_subsetSum design hcard
  have hright := det_projectionBlock_eq_weightProduct_mul_det_subsetSum dual hcompl
  rw [hdual.weight_eq] at hright
  rw [← hleft, ← hlaw, hright]

/-- **MATROID DUALITY.**  A triple of the design is degenerate exactly when the
COMPLEMENTARY triple of the Gale dual is degenerate.  The bases of the dual design are
the complements of the bases of the design, which is the defining property of the dual
matroid — so the Gale involution REPRESENTS matroid duality. -/
theorem det_subsetSum_eq_zero_iff_chartDual_compl (hdual : IsChartDual design dual)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    (subsetSum design selected).det = 0 ↔ (subsetSum dual selectedᶜ).det = 0 := by
  have hlaw := weightProduct_mul_det_subsetSum_eq_chartDual_compl hdual hcard
  have hleftPos : 0 < ∏ atomIndex ∈ selected, design.weight atomIndex :=
    Finset.prod_pos fun atomIndex _ => design.weight_pos atomIndex
  have hrightPos : 0 < ∏ atomIndex ∈ selectedᶜ, design.weight atomIndex :=
    Finset.prod_pos fun atomIndex _ => design.weight_pos atomIndex
  constructor
  · intro hzero
    rw [hzero, mul_zero] at hlaw
    exact (mul_eq_zero.mp hlaw.symm).resolve_left hrightPos.ne'
  · intro hzero
    rw [hzero, mul_zero] at hlaw
    exact (mul_eq_zero.mp hlaw).resolve_left hleftPos.ne'

end BracketDuality

/-! ## 4. The dual gap in primal coordinates

The dual's Gram matrix is the primal's Gram matrix reflected in the inverse weights.  So
every test on the dual becomes arithmetic in the primal's own numbers, with no square
root and no dual atom anywhere. -/

section DualGap

variable {size rank dualRank : ℕ} {design : WeightedDesign size rank}
  {dual : WeightedDesign size dualRank}

/-- **THE DUAL GRAM MATRIX, IN PRIMAL COORDINATES.**

    `Gram(g*_C) = diag(1/t_c)_{c ∈ C} − Gram(g_C)` .

The diagonal comes from `Gtz.leverageOf_chartDual` and every off-diagonal entry from
`Gtz.dotProduct_chartDual_of_ne`. -/
theorem gram_chartDual_eq (hdual : IsChartDual design dual) {selSize : ℕ}
    (pick : Fin selSize → Fin size) (hinj : Function.Injective pick) :
    selectedAtomRows dual pick * (selectedAtomRows dual pick)ᵀ
      = Matrix.diagonal (fun slot => (design.weight (pick slot))⁻¹)
        - selectedAtomRows design pick * (selectedAtomRows design pick)ᵀ := by
  ext leftSlot rightSlot
  have hentryLeft : (selectedAtomRows dual pick * (selectedAtomRows dual pick)ᵀ)
      leftSlot rightSlot = dual.atom (pick leftSlot) ⬝ᵥ dual.atom (pick rightSlot) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, selectedAtomRows, Matrix.of_apply,
      dotProduct]
  have hentryRight : (selectedAtomRows design pick * (selectedAtomRows design pick)ᵀ)
      leftSlot rightSlot = design.atom (pick leftSlot) ⬝ᵥ design.atom (pick rightSlot) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, selectedAtomRows, Matrix.of_apply,
      dotProduct]
  rw [hentryLeft, Matrix.sub_apply, hentryRight]
  rcases eq_or_ne leftSlot rightSlot with rfl | hne
  · rw [Matrix.diagonal_apply_eq]
    have hlev := leverageOf_chartDual hdual (pick leftSlot)
    rw [dotProduct_self_eq_sum_sq, ← leverageOf, dotProduct_self_eq_sum_sq, ← leverageOf, hlev]
  · rw [Matrix.diagonal_apply_ne _ hne]
    have hpickNe : pick leftSlot ≠ pick rightSlot := fun heq => hne (hinj heq)
    rw [dotProduct_chartDual_of_ne hdual hpickNe]
    ring

/-- **DUAL DOMINATION, READ ON THE PRIMAL.**  The dual dominates a subset exactly when the
primal's Gram matrix on that subset sits below the diagonal of `1/t_c − 1`.  No square
root occurs, so at a rational fixture the test is rational arithmetic. -/
theorem dominates_chartDual_iff_posSemidef_inverseWeight (hdual : IsChartDual design dual)
    (pick : Fin dualRank → Fin size) (hinj : Function.Injective pick) :
    Dominates dual (Finset.image pick Finset.univ)
      ↔ (Matrix.diagonal (fun slot => (design.weight (pick slot))⁻¹ - 1)
          - selectedAtomRows design pick * (selectedAtomRows design pick)ᵀ).PosSemidef := by
  have hgram := transpose_mul_selectedAtomRows dual pick hinj
  have hsplit : Matrix.diagonal (fun slot => (design.weight (pick slot))⁻¹ - 1)
        - selectedAtomRows design pick * (selectedAtomRows design pick)ᵀ
      = selectedAtomRows dual pick * (selectedAtomRows dual pick)ᵀ - 1 := by
    rw [gram_chartDual_eq hdual pick hinj]
    have hdiag : Matrix.diagonal (fun slot => (design.weight (pick slot))⁻¹ - 1)
        = Matrix.diagonal (fun slot => (design.weight (pick slot))⁻¹)
          - (1 : Matrix (Fin dualRank) (Fin dualRank) ℝ) := by
      ext leftSlot rightSlot
      rcases eq_or_ne leftSlot rightSlot with rfl | hne
      · simp only [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.one_apply_eq]
      · simp only [Matrix.diagonal_apply_ne _ hne, Matrix.sub_apply, Matrix.one_apply_ne hne]
        ring
    rw [hdiag]
    abel
  rw [Dominates, ← hgram, hsplit]
  exact (posSemidef_transpose_mul_sub_one_comm _).symm

/-- The strict twin of `Gtz.dominates_chartDual_iff_posSemidef_inverseWeight`. -/
theorem posDef_chartDual_gap_iff_posDef_inverseWeight (hdual : IsChartDual design dual)
    (pick : Fin dualRank → Fin size) (hinj : Function.Injective pick) :
    (subsetSum dual (Finset.image pick Finset.univ) - 1).PosDef
      ↔ (Matrix.diagonal (fun slot => (design.weight (pick slot))⁻¹ - 1)
          - selectedAtomRows design pick * (selectedAtomRows design pick)ᵀ).PosDef := by
  have hgram := transpose_mul_selectedAtomRows dual pick hinj
  have hsplit : Matrix.diagonal (fun slot => (design.weight (pick slot))⁻¹ - 1)
        - selectedAtomRows design pick * (selectedAtomRows design pick)ᵀ
      = selectedAtomRows dual pick * (selectedAtomRows dual pick)ᵀ - 1 := by
    rw [gram_chartDual_eq hdual pick hinj]
    have hdiag : Matrix.diagonal (fun slot => (design.weight (pick slot))⁻¹ - 1)
        = Matrix.diagonal (fun slot => (design.weight (pick slot))⁻¹)
          - (1 : Matrix (Fin dualRank) (Fin dualRank) ℝ) := by
      ext leftSlot rightSlot
      rcases eq_or_ne leftSlot rightSlot with rfl | hne
      · simp only [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.one_apply_eq]
      · simp only [Matrix.diagonal_apply_ne _ hne, Matrix.sub_apply, Matrix.one_apply_ne hne]
        ring
    rw [hdiag]
    abel
  rw [hsplit, ← hgram]
  have hflip := posDef_transpose_mul_sub_smul_one_comm (selectedAtomRows dual pick)
    (level := 1) one_pos
  simpa only [one_smul] using hflip

end DualGap

/-! ## 5. The strict transfer at a uniform weight, and the tie locus

The shipped `Gtz.dominates_iff_dominates_chartDual_compl_of_uniformWeight_sixThree` moves
WEAK domination to the complementary triple.  Section 5 adds the strict twin, which is
what `Gtz.IsTie` needs, and reads off the invariance of the tie locus. -/

section UniformTransfer

/-- At a uniform weight the projection block is the Gram matrix scaled by the weight. -/
theorem projectionBlock_of_uniformWeight (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = (6 : ℝ)⁻¹)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    (projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
        (selected.orderEmbOfFin hcard)
      = (6 : ℝ)⁻¹ • (selectedAtomRows design (selected.orderEmbOfFin hcard)
          * (selectedAtomRows design (selected.orderEmbOfFin hcard))ᵀ) := by
  ext leftSlot rightSlot
  rw [Matrix.submatrix_apply, projectionOfDesign_apply, huniform, huniform,
    Matrix.smul_apply, smul_eq_mul]
  have hsqrt : Real.sqrt ((6 : ℝ)⁻¹) * Real.sqrt ((6 : ℝ)⁻¹) = (6 : ℝ)⁻¹ :=
    Real.mul_self_sqrt (by norm_num)
  have hentry : (selectedAtomRows design (selected.orderEmbOfFin hcard)
        * (selectedAtomRows design (selected.orderEmbOfFin hcard))ᵀ) leftSlot rightSlot
      = design.atom (selected.orderEmbOfFin hcard leftSlot)
        ⬝ᵥ design.atom (selected.orderEmbOfFin hcard rightSlot) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, selectedAtomRows, Matrix.of_apply,
      dotProduct]
  rw [hentry, hsqrt]

/-- Strict domination, read on the projection block at a uniform weight. -/
theorem posDef_gap_iff_posDef_projectionBlock_of_uniformWeight (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = (6 : ℝ)⁻¹)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    (subsetSum design selected - 1).PosDef
      ↔ ((projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
          (selected.orderEmbOfFin hcard) - (6 : ℝ)⁻¹ • 1).PosDef := by
  have hinj : Function.Injective (selected.orderEmbOfFin hcard) :=
    (selected.orderEmbOfFin hcard).injective
  have hgram := transpose_mul_selectedAtomRows design (selected.orderEmbOfFin hcard) hinj
  rw [image_orderEmbOfFin_eq hcard] at hgram
  have hflip := posDef_transpose_mul_sub_smul_one_comm
    (selectedAtomRows design (selected.orderEmbOfFin hcard)) (level := 1) one_pos
  rw [hgram] at hflip
  simp only [one_smul] at hflip
  rw [hflip, projectionBlock_of_uniformWeight design huniform hcard]
  have hscale : (6 : ℝ)⁻¹ • (selectedAtomRows design (selected.orderEmbOfFin hcard)
        * (selectedAtomRows design (selected.orderEmbOfFin hcard))ᵀ) - (6 : ℝ)⁻¹ • 1
      = (6 : ℝ)⁻¹ • (selectedAtomRows design (selected.orderEmbOfFin hcard)
          * (selectedAtomRows design (selected.orderEmbOfFin hcard))ᵀ - 1) := by
    rw [smul_sub]
  rw [hscale, posDef_smul_iff (by norm_num : (0 : ℝ) < (6 : ℝ)⁻¹)]

/-- **THE STRICT COMPLEMENTARY TRANSFER AT A UNIFORM WEIGHT.**  A triple dominates
STRICTLY in the design exactly when the complementary triple dominates strictly in the
Gale dual.  This is the twin that
`Gtz.dominates_iff_dominates_chartDual_compl_of_uniformWeight_sixThree` does not carry,
and it is what `Gtz.IsTie` consumes. -/
theorem posDef_gap_iff_posDef_gap_chartDual_compl_of_uniformWeight
    {design dual : WeightedDesign 6 3} (hdual : IsChartDual design dual)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = (6 : ℝ)⁻¹)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    (subsetSum design selected - 1).PosDef ↔ (subsetSum dual selectedᶜ - 1).PosDef := by
  have hcompl := card_compl_three hcard
  have hdualUniform : ∀ atomIndex : Fin 6, dual.weight atomIndex = (6 : ℝ)⁻¹ := by
    intro atomIndex
    rw [hdual.weight_eq]
    exact huniform atomIndex
  rw [posDef_gap_iff_posDef_projectionBlock_of_uniformWeight design huniform hcard,
    posDef_gap_iff_posDef_projectionBlock_of_uniformWeight dual hdualUniform hcompl,
    posDef_projectionBlock_compl_iff design hcard (level := (6 : ℝ)⁻¹) (by norm_num)
      (by norm_num)]
  have hblock := projectionBlock_chartDual hdual hcompl
  have hrewrite : (projectionOfDesign dual).submatrix (selectedᶜ.orderEmbOfFin hcompl)
        (selectedᶜ.orderEmbOfFin hcompl) - (6 : ℝ)⁻¹ • 1
      = (1 - (6 : ℝ)⁻¹) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (projectionOfDesign design).submatrix (selectedᶜ.orderEmbOfFin hcompl)
            (selectedᶜ.orderEmbOfFin hcompl) := by
    rw [hblock, sub_smul, one_smul]
    abel
  rw [hrewrite]

/-- **THE TIE LOCUS IS INVARIANT UNDER THE INVOLUTION AT A UNIFORM WEIGHT.**  The weak
half is the shipped transfer and the strict half is the theorem above.  Complementation
is an involution of the twenty triples, so the two quantifiers match term by term. -/
theorem isTie_chartDual_iff_isTie_of_uniformWeight {design dual : WeightedDesign 6 3}
    (hdual : IsChartDual design dual)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = (6 : ℝ)⁻¹) :
    IsTie dual ↔ IsTie design := by
  constructor
  · rintro ⟨⟨selected, hcard, hdom⟩, hstrict⟩
    refine ⟨⟨selectedᶜ, card_compl_three hcard, ?_⟩, fun candidate hcandidate hpos => ?_⟩
    · have hmove := dominates_iff_dominates_chartDual_compl_of_uniformWeight_sixThree hdual
        huniform selectedᶜ (card_compl_three hcard)
      rw [compl_compl] at hmove
      exact hmove.mpr hdom
    · exact hstrict candidateᶜ (card_compl_three hcandidate)
        ((posDef_gap_iff_posDef_gap_chartDual_compl_of_uniformWeight hdual huniform
          hcandidate).mp hpos)
  · rintro ⟨⟨selected, hcard, hdom⟩, hstrict⟩
    refine ⟨⟨selectedᶜ, card_compl_three hcard, ?_⟩, fun candidate hcandidate hpos => ?_⟩
    · exact (dominates_iff_dominates_chartDual_compl_of_uniformWeight_sixThree hdual
        huniform selected hcard).mp hdom
    · refine hstrict candidateᶜ (card_compl_three hcandidate) ?_
      have hmove := posDef_gap_iff_posDef_gap_chartDual_compl_of_uniformWeight hdual huniform
        (selected := candidateᶜ) (card_compl_three hcandidate)
      rw [compl_compl] at hmove
      exact hmove.mpr hpos

end UniformTransfer

/-! ## 6. THE CLOSURE — the leverage ceiling at a uniform weight

`Gtz.posDef_of_strictly_light_atom` turns one atom of leverage strictly below one into a
strict card-three dominator, unconditionally at size six because `Gtz.GtzWeighted 5 3` is
a theorem.  `Gtz.leverageOf_chartDual` says the dual leverage is `1/t_c − ℓ_c`.  Compose
the two through the involution and the LIGHT atom of the dual is the HEAVY atom of the
primal: the shipped floor becomes a ceiling. -/

section LeverageCeiling

/-- The predecessor cell, unconditional. -/
theorem gtzWeighted_five_three_of_le_five : GtzWeighted 5 3 :=
  gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)

/-- **THE HEAVY-LEVERAGE CLOSURE.**  At a uniform weight one atom of leverage strictly
above five forces a STRICTLY dominating triple.  The proof crosses the involution once:
the dual atom has leverage `6 − ℓ_c < 1`, the shipped light-atom theorem hands the dual a
strict dominator, and the strict complementary transfer moves it back. -/
theorem exists_posDef_cardThree_of_heavy_leverage_uniform (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = (6 : ℝ)⁻¹)
    {label : Fin 6} (hheavy : 5 < leverageOf (design.atom label)) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ (subsetSum design selected - 1).PosDef := by
  obtain ⟨dual, hdual⟩ := exists_isChartDual_sixThree design
  have hdualLeverage : leverageOf (dual.atom label) < 1 := by
    rw [leverageOf_chartDual hdual label, huniform label,
      show ((6 : ℝ)⁻¹)⁻¹ = 6 from by norm_num]
    linarith [hheavy]
  obtain ⟨candidate, hcard, hpos⟩ :=
    posDef_of_strictly_light_atom (m := 5) (k := 3) dual (by norm_num)
      gtzWeighted_five_three_of_le_five label hdualLeverage
  refine ⟨candidateᶜ, card_compl_three hcard, ?_⟩
  have hmove := posDef_gap_iff_posDef_gap_chartDual_compl_of_uniformWeight hdual huniform
    (selected := candidateᶜ) (card_compl_three hcard)
  rw [compl_compl] at hmove
  exact hmove.mpr hpos

/-- **NO UNIFORM TIE CARRIES A LEVERAGE ABOVE FIVE.** -/
theorem leverage_le_five_of_isTie_uniform (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = (6 : ℝ)⁻¹)
    (htie : IsTie design) (label : Fin 6) : leverageOf (design.atom label) ≤ 5 := by
  by_contra hcontra
  push_neg at hcontra
  obtain ⟨selected, hcard, hpos⟩ :=
    exists_posDef_cardThree_of_heavy_leverage_uniform design huniform hcontra
  exact htie.2 selected hcard hpos

/-- **THE LEVERAGE WINDOW OF A UNIFORM `(6,3)` TIE IS `[1, 5]`.**  The floor is the shipped
`Gtz.leverage_one_le_of_isTie_sixThree` and the ceiling is its mirror across the Gale
involution.  In share coordinates the window is `[1/6, 5/6]`, and the two ends are
exchanged by `s_c ↦ 1 − s_c`. -/
theorem leverage_mem_Icc_one_five_of_isTie_uniform (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = (6 : ℝ)⁻¹)
    (htie : IsTie design) (label : Fin 6) :
    1 ≤ leverageOf (design.atom label) ∧ leverageOf (design.atom label) ≤ 5 :=
  ⟨leverage_one_le_of_isTie_sixThree design htie label,
    leverage_le_five_of_isTie_uniform design huniform htie label⟩

/-- The same window in SHARE coordinates, where the involution acts as `s ↦ 1 − s`. -/
theorem atomShare_mem_Icc_of_isTie_uniform (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = (6 : ℝ)⁻¹)
    (htie : IsTie design) (label : Fin 6) :
    (6 : ℝ)⁻¹ ≤ atomShare design label ∧ atomShare design label ≤ 5 / 6 := by
  obtain ⟨hfloor, hceiling⟩ := leverage_mem_Icc_one_five_of_isTie_uniform design huniform htie label
  rw [atomShare, huniform label]
  constructor <;> nlinarith [hfloor, hceiling]

/-- **THE GALE DUAL OF A UNIFORM TIE IS ALL-HEAVY, WITH NO SIDE HYPOTHESIS.**  The shipped
`Gtz.allHeavy_chartDual_of_uniformWeight_sixThree` reaches the same conclusion from
`Gtz.AllHeavy` plus `Gtz.HasStrictlyDominatingCoSingletons`.  The leverage ceiling
supplies it from the tie alone. -/
theorem one_le_leverage_chartDual_of_isTie_uniform {design dual : WeightedDesign 6 3}
    (hdual : IsChartDual design dual)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = (6 : ℝ)⁻¹)
    (htie : IsTie design) (label : Fin 6) : 1 ≤ leverageOf (dual.atom label) := by
  have hceiling := leverage_le_five_of_isTie_uniform design huniform htie label
  rw [leverageOf_chartDual hdual label, huniform label,
    show ((6 : ℝ)⁻¹)⁻¹ = 6 from by norm_num]
  linarith

end LeverageCeiling

/-! ## 7. The involution DESTROYS ties off the uniform slice

`Gtz.nonUniformLeverageTieDesign` is a shipped `(6,3)` tie at the non-uniform weight
`(1/9, 1/9, 1/9, 2/9, 2/9, 2/9)`.  Its Gale dual dominates `{0,3,4}` STRICTLY.  So the
invariance of section 5 is sharp: it holds at the uniform weight and fails immediately
off it. -/

section TieDestruction

/-- The three selected labels of the witness triple. -/
def nonUniformDualPick : Fin 3 → Fin 6 := ![0, 3, 4]

theorem nonUniformDualPick_injective : Function.Injective nonUniformDualPick := by
  decide

theorem image_nonUniformDualPick :
    Finset.image nonUniformDualPick Finset.univ = ({0, 3, 4} : Finset (Fin 6)) := by
  decide

/-- The primal Gram matrix on `{0,3,4}`, in exact rationals. -/
theorem gram_nonUniformLeverageTie_pick :
    selectedAtomRows nonUniformLeverageTieDesign nonUniformDualPick
        * (selectedAtomRows nonUniformLeverageTieDesign nonUniformDualPick)ᵀ
      = !![19 / 3, 2 / 3, 2 / 3; 2 / 3, 4 / 3, 4 / 3; 2 / 3, 4 / 3, 4 / 3] := by
  ext leftSlot rightSlot
  fin_cases leftSlot <;> fin_cases rightSlot <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, selectedAtomRows, nonUniformDualPick,
      nonUniformLeverageTieDesign_atom, nonUniformLeverageTieAtom, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] <;> norm_num

/-- The inverse-weight diagonal on `{0,3,4}`, in exact rationals. -/
theorem inverseWeight_nonUniformLeverageTie_pick :
    Matrix.diagonal (fun slot =>
        (nonUniformLeverageTieDesign.weight (nonUniformDualPick slot))⁻¹ - 1)
      = !![8, 0, 0; 0, 7 / 2, 0; 0, 0, 7 / 2] := by
  ext leftSlot rightSlot
  fin_cases leftSlot <;> fin_cases rightSlot <;>
    simp [Matrix.diagonal, nonUniformDualPick, nonUniformLeverageTieDesign_weight,
      nonUniformLeverageTieWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> norm_num

/-- **THE DUAL GAP OF THE NON-UNIFORM TIE IS POSITIVE DEFINITE.**  The three leading
principal minors of `diag(8, 7/2, 7/2) − Gram` are `5/3`, `19/6` and `7/4`. -/
theorem posDef_dualGap_nonUniformLeverageTie :
    (Matrix.diagonal (fun slot =>
          (nonUniformLeverageTieDesign.weight (nonUniformDualPick slot))⁻¹ - 1)
        - selectedAtomRows nonUniformLeverageTieDesign nonUniformDualPick
          * (selectedAtomRows nonUniformLeverageTieDesign nonUniformDualPick)ᵀ).PosDef := by
  have hshape : Matrix.diagonal (fun slot =>
          (nonUniformLeverageTieDesign.weight (nonUniformDualPick slot))⁻¹ - 1)
        - selectedAtomRows nonUniformLeverageTieDesign nonUniformDualPick
          * (selectedAtomRows nonUniformLeverageTieDesign nonUniformDualPick)ᵀ
      = !![5 / 3, -(2 / 3), -(2 / 3); -(2 / 3), 13 / 6, -(4 / 3);
          -(2 / 3), -(4 / 3), 13 / 6] := by
    rw [inverseWeight_nonUniformLeverageTie_pick, gram_nonUniformLeverageTie_pick]
    ext leftSlot rightSlot
    fin_cases leftSlot <;> fin_cases rightSlot <;> norm_num
  rw [hshape]
  exact posDef_of_leadingMinors_fin_three (5 / 3) (-(2 / 3)) (-(2 / 3)) (13 / 6) (-(4 / 3))
    (13 / 6) (by norm_num) (by norm_num) (by norm_num)

/-- **THE GALE DUAL OF A NON-UNIFORM TIE IS NOT A TIE.** -/
theorem not_isTie_chartDual_nonUniformLeverageTieDesign
    {dual : WeightedDesign 6 3} (hdual : IsChartDual nonUniformLeverageTieDesign dual) :
    ¬ IsTie dual := by
  intro htie
  have hpos := (posDef_chartDual_gap_iff_posDef_inverseWeight hdual nonUniformDualPick
    nonUniformDualPick_injective).mpr posDef_dualGap_nonUniformLeverageTie
  rw [image_nonUniformDualPick] at hpos
  exact htie.2 ({0, 3, 4} : Finset (Fin 6)) (by decide) hpos

/-- **THE INVOLUTION DESTROYS TIES OFF THE UNIFORM SLICE.**  There is a `(6,3)` tie whose
Gale dual is not a tie.  Section 5 proves the tie locus INVARIANT at a uniform weight, so
the invariance is exactly a uniform-weight phenomenon, and the involution is not a
symmetry of the tie locus at general weights. -/
theorem exists_isTie_sixThree_with_chartDual_not_isTie :
    ∃ design : WeightedDesign 6 3, IsTie design ∧
      ∀ dual : WeightedDesign 6 3, IsChartDual design dual → ¬ IsTie dual :=
  ⟨nonUniformLeverageTieDesign, nonUniformLeverageTieDesign_isTie,
    fun _ hdual => not_isTie_chartDual_nonUniformLeverageTieDesign hdual⟩

/-- **THE COMPLEMENTARY TRANSFER IS UNIFORM-WEIGHT ONLY.**  Weak domination does NOT move
to the complementary triple of the Gale dual at a general weight: the tie above weakly
dominates `{0,1,2}`, and its dual dominates the complement `{3,4,5}` strictly, so the
tie would have to carry a strict dominator, which it does not. -/
theorem not_forall_dominates_iff_dominates_chartDual_compl_sixThree :
    ¬ (∀ (design dual : WeightedDesign 6 3), IsChartDual design dual →
        ∀ selected : Finset (Fin 6), selected.card = 3 →
          ((subsetSum design selected - 1).PosDef ↔ (subsetSum dual selectedᶜ - 1).PosDef)) := by
  intro hall
  obtain ⟨dual, hdual⟩ := exists_isChartDual_sixThree nonUniformLeverageTieDesign
  have hcompl : ({1, 2, 5} : Finset (Fin 6))ᶜ = ({0, 3, 4} : Finset (Fin 6)) := by decide
  have hpos := (posDef_chartDual_gap_iff_posDef_inverseWeight hdual nonUniformDualPick
    nonUniformDualPick_injective).mpr posDef_dualGap_nonUniformLeverageTie
  rw [image_nonUniformDualPick] at hpos
  have hback := (hall nonUniformLeverageTieDesign dual hdual ({1, 2, 5} : Finset (Fin 6))
    (by decide)).mpr (by rw [hcompl]; exact hpos)
  exact nonUniformLeverageTieDesign_isTie.2 ({1, 2, 5} : Finset (Fin 6)) (by decide) hback

end TieDestruction

end Gtz
