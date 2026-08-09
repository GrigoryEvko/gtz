/-
# The complement frame theorem

Fix a weighted design and a base subset `B` of its labels whose weighted atom
mass leaves an invertible residual

    residual  =  1 - Σ_{c ∈ B} t_c g_c g_cᵀ .

Parseval turns that residual into the weighted atom mass of the COMPLEMENT, so
whenever the complement carries exactly as many labels as the rank there is a
square matrix `F` -- columns `√t_k · g_k`, one per complement label -- with

    F Fᵀ = residual .

The residual is then invertible exactly when `F` is, and in that case

    Fᵀ residual⁻¹ F = Fᵀ (F Fᵀ)⁻¹ F = Fᵀ (Fᵀ)⁻¹ F⁻¹ F = 1 ,

whose `(k, l)` entry reads `√(t_k t_l) · ⟨g_k, residual⁻¹ g_l⟩ = δ_kl`.  Positive
weights clear the square roots: the complement atoms are WEIGHTED ORTHONORMAL in
the residual-inverse metric,

    t_k · ⟨g_k, residual⁻¹ g_k⟩ = 1 ,      ⟨g_k, residual⁻¹ g_l⟩ = 0  (k ≠ l).

So at a fixed weak dominator the residual configuration is pinned by the base
Gram data, the weights, and one rotation: the square root lives only inside the
proof, and no matrix square root is used anywhere.

The same factorisation decides the degenerate edge.  `F Fᵀ` is positive
semidefinite for free, `det (F Fᵀ) = (∏ t_k) · (det columns)²`, and therefore the
residual is positive definite exactly when the complement atoms are linearly
independent -- at rank three, exactly when their triple bracket is nonzero, i.e.
when they are not coplanar.

Everything below is stated at general rank and general size; the rank-three
bracket reading and the `(6,3)` instance on `Gtz.selectiveAxisDesign` are
corollaries.
-/
import Gtz.Design.ComplementEngine
import Gtz.Design.OneLineShadow
import Gtz.Design.PrimitiveTightClassification
import Gtz.LinAlg.PsdKit
import Gtz.Reduction.DiagonalRungs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Part 1 — the factorisation identity, design-free

Only two facts about `F Fᵀ = R` are used, and neither mentions a design. -/

/-- A square factor of an invertible product is invertible: `det F · det F = det R`. -/
theorem isUnit_det_of_mul_transpose_eq (frameMatrix residualMatrix : Matrix (Fin rank) (Fin rank) ℝ)
    (hfactor : frameMatrix * frameMatrixᵀ = residualMatrix)
    (hunit : IsUnit residualMatrix.det) :
    IsUnit frameMatrix.det := by
  have hdet : frameMatrix.det * frameMatrix.det = residualMatrix.det := by
    rw [← hfactor, Matrix.det_mul, Matrix.det_transpose]
  have hne : frameMatrix.det * frameMatrix.det ≠ 0 := by
    rw [hdet]
    exact isUnit_iff_ne_zero.mp hunit
  exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hne)

/-- **The identity the whole file rests on.**  If `F Fᵀ = R` with `R` invertible then
`Fᵀ R⁻¹ F = 1`: the columns of `F` are orthonormal in the `R⁻¹` metric. -/
theorem transpose_mul_inv_mul_eq_one_of_mul_transpose_eq
    (frameMatrix residualMatrix : Matrix (Fin rank) (Fin rank) ℝ)
    (hfactor : frameMatrix * frameMatrixᵀ = residualMatrix)
    (hunit : IsUnit residualMatrix.det) :
    frameMatrixᵀ * residualMatrix⁻¹ * frameMatrix = 1 := by
  have hframeUnit : IsUnit frameMatrix.det :=
    isUnit_det_of_mul_transpose_eq frameMatrix residualMatrix hfactor hunit
  have htransposeUnit : IsUnit (frameMatrixᵀ).det := by
    rw [Matrix.det_transpose]
    exact hframeUnit
  rw [← hfactor, Matrix.mul_inv_rev,
    show frameMatrixᵀ * ((frameMatrixᵀ)⁻¹ * frameMatrix⁻¹) * frameMatrix
        = (frameMatrixᵀ * (frameMatrixᵀ)⁻¹) * (frameMatrix⁻¹ * frameMatrix) by
      simp only [Matrix.mul_assoc],
    Matrix.mul_nonsing_inv _ htransposeUnit, Matrix.nonsing_inv_mul _ hframeUnit,
    Matrix.one_mul]

/-! ## Part 2 — the weighted frame of a pick

A `pick` is an enumeration of `rank` labels of the design.  Two square matrices
are attached to it: the raw atom columns, and the same columns scaled by the
square roots of the weights. -/

/-- The atoms selected by `pick`, written as the COLUMNS of a square matrix. -/
def atomColumnsOfPick (design : WeightedDesign size rank) (pick : Fin rank → Fin size) :
    Matrix (Fin rank) (Fin rank) ℝ :=
  Matrix.of fun coordIndex slotIndex => design.atom (pick slotIndex) coordIndex

/-- Reading the columns back off is definitional. -/
theorem col_atomColumnsOfPick (design : WeightedDesign size rank) (pick : Fin rank → Fin size) :
    (atomColumnsOfPick design pick).col = fun slotIndex => design.atom (pick slotIndex) := rfl

/-- **The weighted frame of a pick**: column `j` is `√t_{pick j} · g_{pick j}`.
The square root appears here and nowhere in any statement below. -/
noncomputable def weightedFrameOfPick (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) : Matrix (Fin rank) (Fin rank) ℝ :=
  Matrix.of fun coordIndex slotIndex =>
    Real.sqrt (design.weight (pick slotIndex)) * design.atom (pick slotIndex) coordIndex

/-- **The frame factorises the picked weighted mass**: `F Fᵀ = Σ_j t_j g_j g_jᵀ`. -/
theorem weightedFrameOfPick_mul_transpose (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) :
    weightedFrameOfPick design pick * (weightedFrameOfPick design pick)ᵀ
      = ∑ slotIndex,
          design.weight (pick slotIndex) • atomMatrix (design.atom (pick slotIndex)) := by
  ext rowCoord colCoord
  simp only [Matrix.mul_apply, Matrix.transpose_apply, weightedFrameOfPick, Matrix.of_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply]
  refine Finset.sum_congr rfl fun slotIndex _ => ?_
  have hsquare :
      Real.sqrt (design.weight (pick slotIndex)) * Real.sqrt (design.weight (pick slotIndex))
        = design.weight (pick slotIndex) :=
    Real.mul_self_sqrt (design.weight_pos (pick slotIndex)).le
  have hregroup : Real.sqrt (design.weight (pick slotIndex)) * design.atom (pick slotIndex) rowCoord
        * (Real.sqrt (design.weight (pick slotIndex)) * design.atom (pick slotIndex) colCoord)
      = Real.sqrt (design.weight (pick slotIndex)) * Real.sqrt (design.weight (pick slotIndex))
        * (design.atom (pick slotIndex) rowCoord * design.atom (pick slotIndex) colCoord) := by ring
  rw [hregroup, hsquare]

/-- Entrywise reading of the congruence `Fᵀ M F`: the `(j, l)` entry is the
`M`-pairing of the two picked atoms, scaled by the two weight square roots. -/
theorem weightedFrameOfPick_conjugate_apply (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (metricMatrix : Matrix (Fin rank) (Fin rank) ℝ)
    (slotFirst slotSecond : Fin rank) :
    ((weightedFrameOfPick design pick)ᵀ * metricMatrix * weightedFrameOfPick design pick)
        slotFirst slotSecond
      = Real.sqrt (design.weight (pick slotFirst)) * Real.sqrt (design.weight (pick slotSecond))
        * (design.atom (pick slotFirst) ⬝ᵥ (metricMatrix *ᵥ design.atom (pick slotSecond))) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, weightedFrameOfPick, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun rowCoord _ => Finset.sum_congr rfl fun colCoord _ => by ring

/-- The frame is the atom columns rescaled by a diagonal of weight square roots. -/
theorem weightedFrameOfPick_eq_atomColumnsOfPick_mul_diagonal (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) :
    weightedFrameOfPick design pick
      = atomColumnsOfPick design pick
        * Matrix.diagonal (fun slotIndex => Real.sqrt (design.weight (pick slotIndex))) := by
  ext coordIndex slotIndex
  rw [Matrix.mul_diagonal]
  simp [weightedFrameOfPick, atomColumnsOfPick, mul_comm]

/-- Determinant of the frame: the atom-column determinant times the weight square roots. -/
theorem det_weightedFrameOfPick (design : WeightedDesign size rank) (pick : Fin rank → Fin size) :
    (weightedFrameOfPick design pick).det
      = (atomColumnsOfPick design pick).det
        * ∏ slotIndex, Real.sqrt (design.weight (pick slotIndex)) := by
  rw [weightedFrameOfPick_eq_atomColumnsOfPick_mul_diagonal, Matrix.det_mul, Matrix.det_diagonal]

/-- Squaring the product of weight square roots returns the product of the weights. -/
theorem sq_prod_sqrt_weight_eq_prod_weight (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) :
    (∏ slotIndex, Real.sqrt (design.weight (pick slotIndex))) ^ 2
      = ∏ slotIndex, design.weight (pick slotIndex) := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun slotIndex _ =>
    Real.sq_sqrt (design.weight_pos (pick slotIndex)).le

/-- The quadratic form of a picked weighted mass is the weighted sum of squared
projections. -/
theorem dotProduct_pickSum_mulVec (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (probe : Fin rank → ℝ) :
    probe ⬝ᵥ ((∑ slotIndex,
        design.weight (pick slotIndex) • atomMatrix (design.atom (pick slotIndex))) *ᵥ probe)
      = ∑ slotIndex,
          design.weight (pick slotIndex) * (design.atom (pick slotIndex) ⬝ᵥ probe) ^ 2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun slotIndex _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [atomMatrix, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, sq,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-! ## Part 3 — the complement frame theorem, pick form -/

/-- **Weighted orthonormality in an inverse metric.**  Every listed atom has
inverse-metric leverage exactly `1 / t`, and distinct listed atoms are
inverse-metric orthogonal. -/
def IsInverseMetricOrthonormalOn (design : WeightedDesign size rank) (labelSet : Finset (Fin size))
    (residualMetric : Matrix (Fin rank) (Fin rank) ℝ) : Prop :=
  (∀ label ∈ labelSet,
      design.weight label * (design.atom label ⬝ᵥ (residualMetric⁻¹ *ᵥ design.atom label)) = 1)
  ∧ ∀ labelFirst ∈ labelSet, ∀ labelSecond ∈ labelSet, labelFirst ≠ labelSecond →
      design.atom labelFirst ⬝ᵥ (residualMetric⁻¹ *ᵥ design.atom labelSecond) = 0

/-- The diagonal half, in pick form: a picked atom's inverse-metric leverage is
the reciprocal of its weight. -/
theorem weight_mul_inverseMetricPairing_eq_one_of_pickSum (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (residualMetric : Matrix (Fin rank) (Fin rank) ℝ)
    (hfactor : residualMetric
      = ∑ slotIndex, design.weight (pick slotIndex) • atomMatrix (design.atom (pick slotIndex)))
    (hunit : IsUnit residualMetric.det) (slotIndex : Fin rank) :
    design.weight (pick slotIndex)
        * (design.atom (pick slotIndex) ⬝ᵥ (residualMetric⁻¹ *ᵥ design.atom (pick slotIndex)))
      = 1 := by
  have hframe : weightedFrameOfPick design pick * (weightedFrameOfPick design pick)ᵀ
      = residualMetric := by
    rw [weightedFrameOfPick_mul_transpose, hfactor]
  have hidentity := transpose_mul_inv_mul_eq_one_of_mul_transpose_eq
    (weightedFrameOfPick design pick) residualMetric hframe hunit
  have hentry := congrFun (congrFun hidentity slotIndex) slotIndex
  rw [weightedFrameOfPick_conjugate_apply, Matrix.one_apply_eq] at hentry
  have hsquare :
      Real.sqrt (design.weight (pick slotIndex)) * Real.sqrt (design.weight (pick slotIndex))
        = design.weight (pick slotIndex) :=
    Real.mul_self_sqrt (design.weight_pos (pick slotIndex)).le
  rwa [hsquare] at hentry

/-- The off-diagonal half, in pick form: distinct picked atoms are
inverse-metric orthogonal. -/
theorem inverseMetricPairing_eq_zero_of_pickSum (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (residualMetric : Matrix (Fin rank) (Fin rank) ℝ)
    (hfactor : residualMetric
      = ∑ slotIndex, design.weight (pick slotIndex) • atomMatrix (design.atom (pick slotIndex)))
    (hunit : IsUnit residualMetric.det) {slotFirst slotSecond : Fin rank}
    (hslotNe : slotFirst ≠ slotSecond) :
    design.atom (pick slotFirst) ⬝ᵥ (residualMetric⁻¹ *ᵥ design.atom (pick slotSecond)) = 0 := by
  have hframe : weightedFrameOfPick design pick * (weightedFrameOfPick design pick)ᵀ
      = residualMetric := by
    rw [weightedFrameOfPick_mul_transpose, hfactor]
  have hidentity := transpose_mul_inv_mul_eq_one_of_mul_transpose_eq
    (weightedFrameOfPick design pick) residualMetric hframe hunit
  have hentry := congrFun (congrFun hidentity slotFirst) slotSecond
  rw [weightedFrameOfPick_conjugate_apply, Matrix.one_apply_ne hslotNe] at hentry
  have hrootsPos : 0 < Real.sqrt (design.weight (pick slotFirst))
      * Real.sqrt (design.weight (pick slotSecond)) :=
    mul_pos (Real.sqrt_pos.mpr (design.weight_pos (pick slotFirst)))
      (Real.sqrt_pos.mpr (design.weight_pos (pick slotSecond)))
  rcases mul_eq_zero.mp hentry with hrootsZero | hpairingZero
  · exact absurd hrootsZero (ne_of_gt hrootsPos)
  · exact hpairingZero

/-! ## Part 4 — Parseval discharge: the residual of a base subset -/

/-- The residual left by a base subset: the identity minus the base's weighted
atom mass. -/
def baseResidual (design : WeightedDesign size rank) (baseSet : Finset (Fin size)) :
    Matrix (Fin rank) (Fin rank) ℝ :=
  1 - ∑ label ∈ baseSet, design.weight label • atomMatrix (design.atom label)

/-- **Parseval reads the residual as the complement's weighted mass.** -/
theorem baseResidual_eq_complementSum (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) :
    baseResidual design baseSet
      = ∑ label ∈ baseSetᶜ, design.weight label • atomMatrix (design.atom label) := by
  classical
  have hsplit := Finset.sum_add_sum_compl baseSet
    (fun label => design.weight label • atomMatrix (design.atom label))
  rw [design.isParseval] at hsplit
  rw [baseResidual, ← hsplit]
  abel

/-- An injective pick whose image is the complement enumerates the complement sum. -/
theorem sum_compl_eq_sum_over_pick (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = baseSetᶜ) :
    ∑ label ∈ baseSetᶜ, design.weight label • atomMatrix (design.atom label)
      = ∑ slotIndex,
          design.weight (pick slotIndex) • atomMatrix (design.atom (pick slotIndex)) := by
  classical
  rw [← himage, Finset.sum_image (fun _ _ _ _ hequal => hinjective hequal)]

/-- The residual of a base subset, factorised through a complement enumeration. -/
theorem baseResidual_eq_pickSum (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = baseSetᶜ) :
    baseResidual design baseSet
      = ∑ slotIndex,
          design.weight (pick slotIndex) • atomMatrix (design.atom (pick slotIndex)) := by
  rw [baseResidual_eq_complementSum,
    sum_compl_eq_sum_over_pick design baseSet pick hinjective himage]

/-- A counting substitute for the image hypothesis: an injective pick that
misses the base set and has the right cardinality already enumerates the
complement. -/
theorem image_eq_compl_of_injective_of_card (baseSet : Finset (Fin size))
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (houtside : ∀ slotIndex, pick slotIndex ∉ baseSet)
    (hcard : baseSet.card + rank = size) :
    Finset.image pick Finset.univ = baseSetᶜ := by
  classical
  have hsubset : Finset.image pick Finset.univ ⊆ baseSetᶜ := by
    intro label hlabel
    obtain ⟨slotIndex, _, hslot⟩ := Finset.mem_image.mp hlabel
    rw [← hslot]
    exact Finset.mem_compl.mpr (houtside slotIndex)
  have hcardImage : (Finset.image pick Finset.univ).card = rank := by
    rw [Finset.card_image_of_injective _ hinjective, Finset.card_univ, Fintype.card_fin]
  have hcardCompl : (baseSetᶜ).card = rank := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  exact Finset.eq_of_subset_of_card_le hsubset (le_of_eq (by rw [hcardImage, hcardCompl]))

/-- **THE COMPLEMENT FRAME THEOREM.**  If the weighted mass of a base subset
leaves a positive definite residual, and the complement carries exactly `rank`
labels, then the complement atoms are weighted-orthonormal in the
residual-inverse metric. -/
theorem complementFrame_of_baseSet (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = baseSetᶜ)
    (hposDef : (baseResidual design baseSet).PosDef) :
    IsInverseMetricOrthonormalOn design baseSetᶜ (baseResidual design baseSet) := by
  classical
  have hunit : IsUnit (baseResidual design baseSet).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  have hfactor := baseResidual_eq_pickSum design baseSet pick hinjective himage
  refine ⟨fun label hlabel => ?_, fun labelFirst hmemFirst labelSecond hmemSecond hlabelNe => ?_⟩
  · obtain ⟨slotIndex, _, hslot⟩ := Finset.mem_image.mp (himage ▸ hlabel)
    rw [← hslot]
    exact weight_mul_inverseMetricPairing_eq_one_of_pickSum design pick _ hfactor hunit slotIndex
  · obtain ⟨slotFirst, _, hslotFirst⟩ := Finset.mem_image.mp (himage ▸ hmemFirst)
    obtain ⟨slotSecond, _, hslotSecond⟩ := Finset.mem_image.mp (himage ▸ hmemSecond)
    have hslotNe : slotFirst ≠ slotSecond := by
      intro hslotEq
      exact hlabelNe (by rw [← hslotFirst, ← hslotSecond, hslotEq])
    rw [← hslotFirst, ← hslotSecond]
    exact inverseMetricPairing_eq_zero_of_pickSum design pick _ hfactor hunit hslotNe

/-- The complement frame theorem with the image hypothesis replaced by counting:
the pick must be injective, must avoid the base set, and the two label counts
must add up to the size. -/
theorem complementFrame_of_disjointPick (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick)
    (houtside : ∀ slotIndex, pick slotIndex ∉ baseSet)
    (hcard : baseSet.card + rank = size)
    (hposDef : (baseResidual design baseSet).PosDef) :
    IsInverseMetricOrthonormalOn design baseSetᶜ (baseResidual design baseSet) :=
  complementFrame_of_baseSet design baseSet pick hinjective
    (image_eq_compl_of_injective_of_card baseSet pick hinjective houtside hcard) hposDef

/-- **The complement frame theorem with no enumeration at all.**  Counting alone
supplies the pick: whenever the base subset leaves exactly `rank` labels outside
it and a positive definite residual, the outside atoms are weighted-orthonormal
in the residual-inverse metric. -/
theorem complementFrame_of_card (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) (hcard : baseSet.card + rank = size)
    (hposDef : (baseResidual design baseSet).PosDef) :
    IsInverseMetricOrthonormalOn design baseSetᶜ (baseResidual design baseSet) := by
  classical
  have hcomplCard : (baseSetᶜ).card = rank := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  refine complementFrame_of_disjointPick design baseSet
    (fun slotIndex => (baseSetᶜ).orderEmbOfFin hcomplCard slotIndex) ?_ ?_ hcard hposDef
  · exact fun slotFirst slotSecond hequal =>
      ((baseSetᶜ).orderEmbOfFin hcomplCard).injective hequal
  · intro slotIndex
    exact Finset.mem_compl.mp (Finset.orderEmbOfFin_mem _ hcomplCard slotIndex)

/-- **The `(6, 3)` reading, exactly as the campaign states it.**  A base triple
of a six-atom rank-three design whose weighted mass leaves a positive definite
residual has its three complementary atoms weighted-orthonormal in the
residual-inverse metric. -/
theorem complementFrame_sixThree (design : WeightedDesign 6 3) (baseTriple : Finset (Fin 6))
    (hcard : baseTriple.card = 3)
    (hposDef : (baseResidual design baseTriple).PosDef) :
    IsInverseMetricOrthonormalOn design baseTripleᶜ (baseResidual design baseTriple) :=
  complementFrame_of_card design baseTriple (by omega) hposDef

/-- **Parseval in the residual metric.**  The complement is not merely
orthonormal for `residual⁻¹`; it resolves that inner product, so the residual
configuration is coordinatized by the `rank` numbers `⟨g_k, residual⁻¹ x⟩`. -/
theorem dotProduct_inv_baseResidual_eq_sum_sq_of_pick (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = baseSetᶜ)
    (hposDef : (baseResidual design baseSet).PosDef) (probe : Fin rank → ℝ) :
    probe ⬝ᵥ ((baseResidual design baseSet)⁻¹ *ᵥ probe)
      = ∑ slotIndex, design.weight (pick slotIndex)
          * (design.atom (pick slotIndex)
              ⬝ᵥ ((baseResidual design baseSet)⁻¹ *ᵥ probe)) ^ 2 := by
  have hunit : IsUnit (baseResidual design baseSet).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  have hfactor := baseResidual_eq_pickSum design baseSet pick hinjective himage
  have hrecover : (baseResidual design baseSet)
      *ᵥ ((baseResidual design baseSet)⁻¹ *ᵥ probe) = probe := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  calc probe ⬝ᵥ ((baseResidual design baseSet)⁻¹ *ᵥ probe)
      = ((baseResidual design baseSet) *ᵥ ((baseResidual design baseSet)⁻¹ *ᵥ probe))
          ⬝ᵥ ((baseResidual design baseSet)⁻¹ *ᵥ probe) := by rw [hrecover]
    _ = ((baseResidual design baseSet)⁻¹ *ᵥ probe)
          ⬝ᵥ ((baseResidual design baseSet) *ᵥ ((baseResidual design baseSet)⁻¹ *ᵥ probe)) :=
        dotProduct_comm _ _
    _ = ∑ slotIndex, design.weight (pick slotIndex)
          * (design.atom (pick slotIndex)
              ⬝ᵥ ((baseResidual design baseSet)⁻¹ *ᵥ probe)) ^ 2 := by
        rw [hfactor, dotProduct_pickSum_mulVec]

/-! ## Part 5 — the degenerate edge

`F Fᵀ` is positive semidefinite for free and its determinant is the weight
product times the squared atom-column determinant, so the residual is positive
definite exactly when the complement atoms are independent. -/

/-- The picked weighted mass is positive semidefinite, unconditionally. -/
theorem posSemidef_pickSum (design : WeightedDesign size rank) (pick : Fin rank → Fin size) :
    (∑ slotIndex,
      design.weight (pick slotIndex) • atomMatrix (design.atom (pick slotIndex))).PosSemidef := by
  rw [← weightedFrameOfPick_mul_transpose]
  simpa using Matrix.posSemidef_self_mul_conjTranspose (weightedFrameOfPick design pick)

/-- The residual determinant in closed form: weight product times squared
atom-column determinant. -/
theorem det_pickSum_eq_prod_weight_mul_det_sq (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) :
    (∑ slotIndex, design.weight (pick slotIndex) • atomMatrix (design.atom (pick slotIndex))).det
      = (∏ slotIndex, design.weight (pick slotIndex))
        * (atomColumnsOfPick design pick).det ^ 2 := by
  rw [← weightedFrameOfPick_mul_transpose, Matrix.det_mul, Matrix.det_transpose,
    det_weightedFrameOfPick]
  have hexpand : ((atomColumnsOfPick design pick).det
          * ∏ slotIndex, Real.sqrt (design.weight (pick slotIndex)))
        * ((atomColumnsOfPick design pick).det
          * ∏ slotIndex, Real.sqrt (design.weight (pick slotIndex)))
      = (∏ slotIndex, Real.sqrt (design.weight (pick slotIndex))) ^ 2
        * (atomColumnsOfPick design pick).det ^ 2 := by ring
  rw [hexpand, sq_prod_sqrt_weight_eq_prod_weight]

/-- Independence of the picked atoms is exactly nonvanishing of the atom-column
determinant. -/
theorem linearIndependent_pick_iff_det_atomColumnsOfPick_ne_zero (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) :
    LinearIndependent ℝ (fun slotIndex => design.atom (pick slotIndex))
      ↔ (atomColumnsOfPick design pick).det ≠ 0 := by
  rw [← col_atomColumnsOfPick, Matrix.linearIndependent_cols_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- **The degenerate edge, determinant form.** -/
theorem posDef_pickSum_iff_det_atomColumnsOfPick_ne_zero (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) :
    (∑ slotIndex, design.weight (pick slotIndex) • atomMatrix (design.atom (pick slotIndex))).PosDef
      ↔ (atomColumnsOfPick design pick).det ≠ 0 := by
  rw [(posSemidef_pickSum design pick).posDef_iff_det_ne_zero,
    det_pickSum_eq_prod_weight_mul_det_sq]
  have hprodPos : 0 < ∏ slotIndex, design.weight (pick slotIndex) :=
    Finset.prod_pos fun slotIndex _ => design.weight_pos (pick slotIndex)
  constructor
  · intro hdetNe hcolumnsZero
    exact hdetNe (by rw [hcolumnsZero]; ring)
  · intro hcolumnsNe hproductZero
    rcases mul_eq_zero.mp hproductZero with hweightZero | hsquareZero
    · exact absurd hweightZero (ne_of_gt hprodPos)
    · exact hcolumnsNe (sq_eq_zero_iff.mp hsquareZero)

/-- **The degenerate edge.**  The residual left by a base subset is positive
definite exactly when the complement atoms are linearly independent; singular
residual and degenerate complement are the same event. -/
theorem posDef_baseResidual_iff_linearIndependent (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = baseSetᶜ) :
    (baseResidual design baseSet).PosDef
      ↔ LinearIndependent ℝ (fun slotIndex => design.atom (pick slotIndex)) := by
  rw [baseResidual_eq_pickSum design baseSet pick hinjective himage,
    posDef_pickSum_iff_det_atomColumnsOfPick_ne_zero,
    linearIndependent_pick_iff_det_atomColumnsOfPick_ne_zero]

/-! ### Rank three: the bracket reading -/

/-- At rank three the atom-column determinant is the triple bracket. -/
theorem det_atomColumnsOfPick_eq_tripleBracket (design : WeightedDesign size 3)
    (pick : Fin 3 → Fin size) :
    (atomColumnsOfPick design pick).det
      = tripleBracket (design.atom (pick 0)) (design.atom (pick 1)) (design.atom (pick 2)) := by
  rw [tripleBracket, ← Matrix.det_transpose]
  congr 1
  ext slotIndex coordIndex
  fin_cases slotIndex <;> rfl

/-- **Residual singular is complement coplanar.**  At rank three the residual of a
base subset is positive definite exactly when the three complement atoms have
nonzero triple bracket, i.e. exactly when they do not lie in a common plane. -/
theorem posDef_baseResidual_iff_tripleBracket_ne_zero (design : WeightedDesign size 3)
    (baseSet : Finset (Fin size)) (pick : Fin 3 → Fin size)
    (hinjective : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = baseSetᶜ) :
    (baseResidual design baseSet).PosDef
      ↔ tripleBracket (design.atom (pick 0)) (design.atom (pick 1)) (design.atom (pick 2)) ≠ 0 := by
  rw [baseResidual_eq_pickSum design baseSet pick hinjective himage,
    posDef_pickSum_iff_det_atomColumnsOfPick_ne_zero, det_atomColumnsOfPick_eq_tripleBracket]

/-- The coplanar direction spelled out: three complement atoms drawn from one
plane leave a singular residual, so no weak dominator has them as complement. -/
theorem not_posDef_baseResidual_of_spannedByPair (design : WeightedDesign size 3)
    (baseSet : Finset (Fin size)) (pick : Fin 3 → Fin size)
    (hinjective : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = baseSetᶜ)
    (planeFirst planeSecond : Fin 3 → ℝ)
    (hspanned : ∀ slotIndex : Fin 3, ∃ alongFirst alongSecond : ℝ,
      design.atom (pick slotIndex) = alongFirst • planeFirst + alongSecond • planeSecond) :
    ¬ (baseResidual design baseSet).PosDef := by
  rw [posDef_baseResidual_iff_tripleBracket_ne_zero design baseSet pick hinjective himage]
  exact not_not.mpr (tripleBracket_eq_zero_of_spannedByPair planeFirst planeSecond
    (design.atom (pick 0)) (design.atom (pick 1)) (design.atom (pick 2))
    (hspanned 0) (hspanned 1) (hspanned 2))

/-- The bracket criterion with the image hypothesis replaced by counting, so it
takes the same hypotheses as `Gtz.complementFrame_of_disjointPick`. -/
theorem posDef_baseResidual_iff_tripleBracket_ne_zero_of_disjointPick
    (design : WeightedDesign size 3) (baseSet : Finset (Fin size)) (pick : Fin 3 → Fin size)
    (hinjective : Function.Injective pick)
    (houtside : ∀ slotIndex, pick slotIndex ∉ baseSet)
    (hcard : baseSet.card + 3 = size) :
    (baseResidual design baseSet).PosDef
      ↔ tripleBracket (design.atom (pick 0)) (design.atom (pick 1)) (design.atom (pick 2)) ≠ 0 :=
  posDef_baseResidual_iff_tripleBracket_ne_zero design baseSet pick hinjective
    (image_eq_compl_of_injective_of_card baseSet pick hinjective houtside hcard)

/-! ## Part 6 — non-vacuity at `(6, 3)`

`Gtz.selectiveAxisDesign` is the three coordinate axes at length one with weight
`1/9` and again at length two with weight `2/9`.  Taking the three long atoms as
base leaves residual `(1/9) · 1`, and the theorem's conclusion is confirmed
independently by direct arithmetic. -/

/-- The short axis triple, read as atom columns, is the identity. -/
theorem atomColumnsOfPick_selectiveAxisDesign_shortAxes :
    atomColumnsOfPick selectiveAxisDesign (![0, 1, 2] : Fin 3 → Fin 6)
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext coordIndex slotIndex
  fin_cases coordIndex <;> fin_cases slotIndex <;>
    simp [atomColumnsOfPick, selectiveAxisDesign]

/-- The long axis triple leaves a positive definite residual, via the degenerate
edge criterion. -/
theorem posDef_baseResidual_selectiveAxisDesign_longAxes :
    (baseResidual selectiveAxisDesign ({3, 4, 5} : Finset (Fin 6))).PosDef := by
  rw [posDef_baseResidual_iff_linearIndependent selectiveAxisDesign _
      (![0, 1, 2] : Fin 3 → Fin 6) (by decide) (by decide),
    linearIndependent_pick_iff_det_atomColumnsOfPick_ne_zero,
    atomColumnsOfPick_selectiveAxisDesign_shortAxes, Matrix.det_one]
  norm_num

/-- **The complement frame theorem fires on a shipped `(6, 3)` design.** -/
theorem complementFrame_selectiveAxisDesign_longAxes :
    IsInverseMetricOrthonormalOn selectiveAxisDesign (({3, 4, 5} : Finset (Fin 6))ᶜ)
      (baseResidual selectiveAxisDesign ({3, 4, 5} : Finset (Fin 6))) :=
  complementFrame_of_baseSet selectiveAxisDesign _ (![0, 1, 2] : Fin 3 → Fin 6)
    (by decide) (by decide) posDef_baseResidual_selectiveAxisDesign_longAxes

/-- The residual in closed form. -/
theorem baseResidual_selectiveAxisDesign_longAxes :
    baseResidual selectiveAxisDesign ({3, 4, 5} : Finset (Fin 6))
      = (1 / 9 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [baseResidual, show ({3, 4, 5} : Finset (Fin 6)) = insert 3 (insert 4 {5}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [selectiveAxisDesign, atomMatrix, Matrix.vecMulVec] <;> norm_num

/-- Inverting a nonzero scaling of the identity. -/
theorem inv_smul_one_of_ne_zero (scale : ℝ) (hscale : scale ≠ 0) :
    ((scale • (1 : Matrix (Fin rank) (Fin rank) ℝ))⁻¹)
      = scale⁻¹ • (1 : Matrix (Fin rank) (Fin rank) ℝ) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    mul_inv_cancel₀ hscale, one_smul]

/-- Independent arithmetic confirmation on the first short atom: weight `1/9`,
squared length `1`, residual inverse `9 · 1`, product exactly one. -/
theorem weight_mul_inverseMetricPairing_selectiveAxisDesign_shortAxis :
    selectiveAxisDesign.weight 0
        * (selectiveAxisDesign.atom 0 ⬝ᵥ
            ((baseResidual selectiveAxisDesign ({3, 4, 5} : Finset (Fin 6)))⁻¹
              *ᵥ selectiveAxisDesign.atom 0)) = 1 := by
  rw [baseResidual_selectiveAxisDesign_longAxes, inv_smul_one_of_ne_zero _ (by norm_num),
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  simp [selectiveAxisDesign, dotProduct, Fin.sum_univ_three]

end Gtz
