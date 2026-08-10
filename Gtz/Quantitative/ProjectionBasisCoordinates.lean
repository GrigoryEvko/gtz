import Gtz.Quantitative.PlueckerRealness
import Gtz.Quantitative.ProjectionOnePointMarginal
import Gtz.Quantitative.ChartHadamard
import Gtz.Design.DepthCapAxisParseval
import Gtz.Design.PlaneBranchNormalForm
import Gtz.Ties.StratumFirstOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# Rank-three domination in weighted squared-Pluecker coordinates

For a rank-three design, put

  `p(i,j,k) = t_i t_j t_k [i,j,k]^2`.

These are the ordered versions of the twenty projection-DPP basis masses.  This
file records the missing local dictionary: the one-, two-, and three-dimensional
principal minors of the design projection are respectively marginals of `p`, and
the three Sylvester tests for a selected gap are affine expressions in those
marginals and the weights.

The point is not another averaging argument.  It turns the full twenty-candidate
covering problem into a polyhedral covering problem on the *real squared
Grassmannian*, where `Gtz.shadowDeterminantProducts_heronDegenerate` supplies a
nonlinear relation that is false over the complex counterexamples.
-/

namespace Gtz

open Matrix

variable {size : ℕ}

/-- The strict companion of `posSemidef_projectionBlock_iff`: positive
definiteness is also preserved in both directions by the positive diagonal
congruence.  The existing projection API only stated the semidefinite version. -/
theorem posDef_projectionBlock_iff_basisGap
    {rank selectionSize : ℕ} (design : WeightedDesign size rank)
    (pick : Fin selectionSize → Fin size) :
    ((projectionOfDesign design).submatrix pick pick
        - Matrix.diagonal (fun selectedIndex => design.weight (pick selectedIndex))).PosDef
      ↔ (selectedAtomRows design pick * (selectedAtomRows design pick)ᵀ - 1).PosDef := by
  rw [projectionBlock_sub_weightDiagonal]
  exact (posDef_congr_right (selectedGramGap_transpose design pick)
    (isUnit_det_sqrtWeightDiagonal design pick)).symm

/-- At selection size equal to the rank, strict domination is exactly strict
positivity of the corresponding weighted projection block. -/
theorem posDef_subsetSum_iff_posDef_projectionBlock
    {rank : ℕ} (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick) :
    (subsetSum design (Finset.image pick Finset.univ) - 1).PosDef
      ↔ ((projectionOfDesign design).submatrix pick pick
          - Matrix.diagonal (fun selectedIndex => design.weight (pick selectedIndex))).PosDef := by
  rw [posDef_projectionBlock_iff_basisGap,
    ← transpose_mul_selectedAtomRows design pick hinjective]
  exact posDef_transpose_mul_sub_one_comm (selectedAtomRows design pick)

/-- The ordered projection-DPP basis mass at a triple of labels.  Repeated labels
give zero automatically through the alternating bracket. -/
noncomputable def orderedBasisMass (design : WeightedDesign size 3)
    (first second third : Fin size) : ℝ :=
  design.weight first * design.weight second * design.weight third
    * atomBracket design first second third ^ 2

/-- The weighted projection gap on an ordered triple. -/
noncomputable def orderedProjectionGap (design : WeightedDesign size 3)
    (first second third : Fin size) : Matrix (Fin 3) (Fin 3) ℝ :=
  let pick : Fin 3 → Fin size := ![first, second, third]
  (projectionOfDesign design).submatrix pick pick
    - Matrix.diagonal (fun slot => design.weight (pick slot))

/-- The first centered inclusion moment of the projection-DPP basis indicator. -/
noncomputable def centeredBasisFirst (design : WeightedDesign size 3)
    (first : Fin size) : ℝ :=
  projectionOfDesign design first first - design.weight first

/-- The two-dimensional projection minor in ambient coordinates. -/
noncomputable def projectionPairMass (design : WeightedDesign size 3)
    (first second : Fin size) : ℝ :=
  projectionOfDesign design first first * projectionOfDesign design second second
    - projectionOfDesign design first second ^ 2

/-- The second centered inclusion moment of two projection-DPP basis indicators. -/
noncomputable def centeredBasisPair (design : WeightedDesign size 3)
    (first second : Fin size) : ℝ :=
  projectionPairMass design first second
    - design.weight first * projectionOfDesign design second second
    - design.weight second * projectionOfDesign design first first
    + design.weight first * design.weight second

/-- The third centered inclusion moment of three projection-DPP basis indicators. -/
noncomputable def centeredBasisTriple (design : WeightedDesign size 3)
    (first second third : Fin size) : ℝ :=
  orderedBasisMass design first second third
    - design.weight first * projectionPairMass design second third
    - design.weight second * projectionPairMass design first third
    - design.weight third * projectionPairMass design first second
    + design.weight first * design.weight second
        * projectionOfDesign design third third
    + design.weight first * design.weight third
        * projectionOfDesign design second second
    + design.weight second * design.weight third
        * projectionOfDesign design first first
    - design.weight first * design.weight second * design.weight third

/-- Summing the ordered basis mass over its third label gives the weighted
two-dimensional Gram minor of the first pair. -/
theorem sum_orderedBasisMass_third (design : WeightedDesign size 3)
    (first second : Fin size) :
    (∑ third, orderedBasisMass design first second third)
      = design.weight first * design.weight second
          * crossAxisBudget design first second := by
  simp only [orderedBasisMass]
  calc
    (∑ third,
        design.weight first * design.weight second * design.weight third
          * atomBracket design first second third ^ 2) =
        design.weight first * design.weight second
          * ∑ third,
              design.weight third * atomBracket design first second third ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro third _
          ring
    _ = design.weight first * design.weight second
          * crossAxisBudget design first second := by
      rw [sum_weight_mul_atomBracket_sq]

/-- The projection pair minor is the weighted cross-axis budget. -/
theorem projectionPairMass_eq_weight_mul_crossAxisBudget
    (design : WeightedDesign size 3) (first second : Fin size) :
    projectionPairMass design first second
      = design.weight first * design.weight second
          * crossAxisBudget design first second := by
  rw [projectionPairMass, projectionOfDesign_diagonal,
    projectionOfDesign_diagonal, sq_projectionOfDesign_apply,
    crossAxisBudget, atomPairing]
  ring

/-- **The two-point DPP marginal, in ordered coordinates.**  The basis masses
through a fixed pair sum to the corresponding principal minor of the projection.
No distinctness hypothesis is needed. -/
theorem sum_orderedBasisMass_third_eq_projectionPairMass
    (design : WeightedDesign size 3) (first second : Fin size) :
    (∑ third, orderedBasisMass design first second third)
      = projectionPairMass design first second := by
  rw [sum_orderedBasisMass_third,
    projectionPairMass_eq_weight_mul_crossAxisBudget]

/-- A three-dimensional principal projection minor is exactly one ordered basis
mass.  This is Cauchy--Binet at the selected three rows, with the square roots
cleared by the positive weights. -/
theorem det_projectionBlock_three_eq_orderedBasisMass
    (design : WeightedDesign size 3) (first second third : Fin size) :
    ((projectionOfDesign design).submatrix ![first, second, third]
        ![first, second, third]).det
      = orderedBasisMass design first second third := by
  rw [det_projectionBlock_of_design, Matrix.det_mul, Matrix.det_transpose,
    det_selectedAtomRows_three_eq_atomBracket]
  rw [Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  unfold orderedBasisMass
  ring

theorem orderedProjectionGap_transpose (design : WeightedDesign size 3)
    (first second third : Fin size) :
    (orderedProjectionGap design first second third)ᵀ
      = orderedProjectionGap design first second third := by
  unfold orderedProjectionGap
  rw [Matrix.transpose_sub, Matrix.transpose_submatrix,
    projectionOfDesign_transpose, Matrix.diagonal_transpose]

theorem orderedProjectionGap_zero_zero
    (design : WeightedDesign size 3) (first second third : Fin size) :
    orderedProjectionGap design first second third 0 0
      = centeredBasisFirst design first := by
  simp [orderedProjectionGap, centeredBasisFirst]

/-- The leading pair minor of the ordered projection gap is the second
centered basis-inclusion moment. -/
theorem orderedProjectionGap_leadingPair
    (design : WeightedDesign size 3) (first second third : Fin size) :
    orderedProjectionGap design first second third 0 0
          * orderedProjectionGap design first second third 1 1
        - orderedProjectionGap design first second third 0 1 ^ 2
      = centeredBasisPair design first second := by
  simp [orderedProjectionGap, centeredBasisPair, projectionPairMass]
  ring

/-- **The real Grassmann--Pluecker constraint on projection-DPP basis masses.**
For five labels, the three products of complementary basis masses obey the
degenerate Heron equality.  This is the first direct consumer of the tree's
realness identity in the probability coordinates read by the domination
tests.  Over the shipped complex counterexamples the corresponding equality
is strict, so this is not a field-blind marginal identity. -/
theorem orderedBasisMassProducts_heronDegenerate
    (design : WeightedDesign size 3)
    (base first second third fourth : Fin size) :
    (orderedBasisMass design base first second
          * orderedBasisMass design base third fourth
      + orderedBasisMass design base first third
          * orderedBasisMass design base second fourth
      + orderedBasisMass design base first fourth
          * orderedBasisMass design base second third) ^ 2
      = 4 *
          ((orderedBasisMass design base first second
              * orderedBasisMass design base third fourth)
            * (orderedBasisMass design base first third
              * orderedBasisMass design base second fourth)
          + (orderedBasisMass design base first third
              * orderedBasisMass design base second fourth)
            * (orderedBasisMass design base first fourth
              * orderedBasisMass design base second third)
          + (orderedBasisMass design base first fourth
              * orderedBasisMass design base second third)
            * (orderedBasisMass design base first second
              * orderedBasisMass design base third fourth)) := by
  have hreal := squaredBracketProducts_heronDegenerate design
    base first second third fourth
  simp only [orderedBasisMass]
  linear_combination
    (design.weight base ^ 2 * design.weight first * design.weight second
      * design.weight third * design.weight fourth) ^ 2 * hreal

/-- The determinant of a symmetric `3 x 3` matrix after subtracting a diagonal,
expanded in its principal minors. -/
theorem det_sub_diagonal_fin_three
    (form : Matrix (Fin 3) (Fin 3) ℝ) (diagonal : Fin 3 → ℝ)
    (hsymmetric : form.transpose = form) :
    (form - Matrix.diagonal diagonal).det
      = form.det
        - diagonal 0 * (form 1 1 * form 2 2 - form 1 2 ^ 2)
        - diagonal 1 * (form 0 0 * form 2 2 - form 0 2 ^ 2)
        - diagonal 2 * (form 0 0 * form 1 1 - form 0 1 ^ 2)
        + diagonal 0 * diagonal 1 * form 2 2
        + diagonal 0 * diagonal 2 * form 1 1
        + diagonal 1 * diagonal 2 * form 0 0
        - diagonal 0 * diagonal 1 * diagonal 2 := by
  have h10 : form 1 0 = form 0 1 := by
    have := congrFun (congrFun hsymmetric 0) 1
    simpa [Matrix.transpose_apply] using this
  have h20 : form 2 0 = form 0 2 := by
    have := congrFun (congrFun hsymmetric 0) 2
    simpa [Matrix.transpose_apply] using this
  have h21 : form 2 1 = form 1 2 := by
    have := congrFun (congrFun hsymmetric 1) 2
    simpa [Matrix.transpose_apply] using this
  simp [Matrix.det_fin_three, Matrix.sub_apply, h10, h20, h21]
  ring

/-- The determinant of the ordered projection gap is the third centered
basis-inclusion moment. -/
theorem orderedProjectionGap_det_eq_centeredBasisTriple
    (design : WeightedDesign size 3) (first second third : Fin size) :
    (orderedProjectionGap design first second third).det
      = centeredBasisTriple design first second third := by
  let pick : Fin 3 → Fin size := ![first, second, third]
  have hsymm : ((projectionOfDesign design).submatrix pick pick)ᵀ
      = (projectionOfDesign design).submatrix pick pick := by
    rw [Matrix.transpose_submatrix, projectionOfDesign_transpose]
  rw [orderedProjectionGap, det_sub_diagonal_fin_three _ _ hsymm,
    det_projectionBlock_three_eq_orderedBasisMass]
  simp [pick, centeredBasisTriple, projectionPairMass]

/-- **Strict domination in centered projection-DPP coordinates.**  An ordered
triple is positive definite exactly when its first, second, and third centered
inclusion moments are positive. -/
theorem orderedProjectionGap_posDef_iff_centeredBasisMoments
    (design : WeightedDesign size 3) (first second third : Fin size) :
    (orderedProjectionGap design first second third).PosDef
      ↔ 0 < centeredBasisFirst design first
        ∧ 0 < centeredBasisPair design first second
        ∧ 0 < centeredBasisTriple design first second third := by
  let gap := orderedProjectionGap design first second third
  have hsymm : gapᵀ = gap := orderedProjectionGap_transpose design first second third
  have hdet :
      gap 0 0 * gap 1 1 * gap 2 2 - gap 0 0 * gap 1 2 ^ 2
          - gap 0 1 ^ 2 * gap 2 2
          + 2 * gap 0 1 * gap 0 2 * gap 1 2
          - gap 0 2 ^ 2 * gap 1 1 = gap.det := by
    have h10 : gap 1 0 = gap 0 1 := by
      have := congrFun (congrFun hsymm 0) 1
      simpa only [Matrix.transpose_apply] using this
    have h20 : gap 2 0 = gap 0 2 := by
      have := congrFun (congrFun hsymm 0) 2
      simpa only [Matrix.transpose_apply] using this
    have h21 : gap 2 1 = gap 1 2 := by
      have := congrFun (congrFun hsymm 1) 2
      simpa only [Matrix.transpose_apply] using this
    rw [Matrix.det_fin_three, h10, h20, h21]
    ring
  rw [posDef_finThree_iff_reindexedLeadingMinors gap hsymm (Equiv.refl (Fin 3))]
  simp only [Equiv.refl_apply]
  rw [hdet]
  change
    (0 < orderedProjectionGap design first second third 0 0
      ∧ 0 < orderedProjectionGap design first second third 0 0
            * orderedProjectionGap design first second third 1 1
          - orderedProjectionGap design first second third 0 1 ^ 2
      ∧ 0 < (orderedProjectionGap design first second third).det)
      ↔ _
  constructor
  · rintro ⟨hfirst, hpair, htriple⟩
    exact ⟨by simpa only [orderedProjectionGap_zero_zero] using hfirst,
      by simpa only [orderedProjectionGap_leadingPair] using hpair,
      by simpa only [orderedProjectionGap_det_eq_centeredBasisTriple] using htriple⟩
  · rintro ⟨hfirst, hpair, htriple⟩
    exact ⟨by simpa only [orderedProjectionGap_zero_zero] using hfirst,
      by simpa only [orderedProjectionGap_leadingPair] using hpair,
      by simpa only [orderedProjectionGap_det_eq_centeredBasisTriple] using htriple⟩

/-- The same criterion on the tree's unordered triple subset. -/
theorem tripleGap_posDef_iff_centeredBasisMoments
    (design : WeightedDesign size 3) (first second third : Fin size)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    (subsetSum design {first, second, third} - 1).PosDef
      ↔ 0 < centeredBasisFirst design first
        ∧ 0 < centeredBasisPair design first second
        ∧ 0 < centeredBasisTriple design first second third := by
  let pick : Fin 3 → Fin size := ![first, second, third]
  have hinjective : Function.Injective pick := by
    intro left right heq
    fin_cases left <;> fin_cases right <;> simp_all [pick]
  have himage : Finset.image pick Finset.univ = {first, second, third} := by
    ext label
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨slot, hslot⟩
      fin_cases slot <;> simp_all [pick]
    · intro hlabel
      rcases hlabel with rfl | rfl | rfl
      · exact ⟨0, by simp [pick]⟩
      · exact ⟨1, by simp [pick]⟩
      · exact ⟨2, by simp [pick]⟩
  rw [← himage, posDef_subsetSum_iff_posDef_projectionBlock design pick hinjective]
  change (orderedProjectionGap design first second third).PosDef ↔ _
  exact orderedProjectionGap_posDef_iff_centeredBasisMoments design first second third

/-- A gap's leading pair minor is affine in the one- and two-point basis
marginals. -/
theorem chartGapPairMinor_eq_basisMarginals
    (design : WeightedDesign size 3) (first second : Fin size) :
    chartGapPairMinor (projectionOfDesign design) design.weight first second
      = projectionPairMass design first second
        - design.weight first * projectionOfDesign design second second
        - design.weight second * projectionOfDesign design first first
        + design.weight first * design.weight second := by
  rw [chartGapPairMinor, projectionPairMass]
  ring

/-- **The top Sylvester leg in basis coordinates.**  For three distinct labels,
the weighted determinant of their design gap is the inclusion--exclusion affine
form in the one-, two-, and three-point projection-DPP marginals. -/
theorem weightProduct_mul_det_gap_eq_basisMarginals
    (design : WeightedDesign size 3) (first second third : Fin size)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    design.weight first * design.weight second * design.weight third
        * (subsetSum design {first, second, third} - 1).det
      = orderedBasisMass design first second third
        - design.weight first * projectionPairMass design second third
        - design.weight second * projectionPairMass design first third
        - design.weight third * projectionPairMass design first second
        + design.weight first * design.weight second
            * projectionOfDesign design third third
        + design.weight first * design.weight third
            * projectionOfDesign design second second
        + design.weight second * design.weight third
            * projectionOfDesign design first first
        - design.weight first * design.weight second * design.weight third := by
  let pick : Fin 3 → Fin size := ![first, second, third]
  have hinjective : Function.Injective pick := by
    intro left right heq
    fin_cases left <;> fin_cases right <;> simp_all [pick]
  have himage : Finset.image pick Finset.univ = {first, second, third} := by
    ext label
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨slot, hslot⟩
      fin_cases slot <;> simp_all [pick]
    · intro hlabel
      rcases hlabel with rfl | rfl | rfl
      · exact ⟨0, by simp [pick]⟩
      · exact ⟨1, by simp [pick]⟩
      · exact ⟨2, by simp [pick]⟩
  have hblock := det_projectionBlock_sub_weightDiagonal design pick
  have hsymm : ((projectionOfDesign design).submatrix pick pick).transpose
      = (projectionOfDesign design).submatrix pick pick := by
    rw [Matrix.transpose_submatrix, projectionOfDesign_transpose]
  rw [det_mul_transpose_sub_one_comm,
    transpose_mul_selectedAtomRows design pick hinjective, himage] at hblock
  have hblock' :
      design.weight first * design.weight second * design.weight third
          * (subsetSum design {first, second, third} - 1).det
        = ((projectionOfDesign design).submatrix pick pick
            - Matrix.diagonal (fun selectedIndex => design.weight (pick selectedIndex))).det := by
    simpa [Fin.prod_univ_three, pick, mul_assoc] using hblock.symm
  rw [hblock']
  rw [det_sub_diagonal_fin_three _ _ hsymm,
    det_projectionBlock_three_eq_orderedBasisMass]
  simp only [Matrix.submatrix_apply, pick, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [projectionPairMass, projectionPairMass, projectionPairMass]

end Gtz
