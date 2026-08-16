import Gtz.Design.KFourChartClosure
import Gtz.Design.OneDeterminantReduction
import Gtz.Design.ThreeLinesTriangleCell
import Gtz.LinAlg.SchurRankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The M(K4) band atlas: the chart gap without division, and the band collapse

The K4 chart obligation `Gtz.KFourKnifeBandRefinedWeakToStrict` demands a
strictly dominating spanning tree only at chart points that are weakly
dominated and lie off BOTH covered regions (the twenty Layer-A cells and the
Layer-B exchange star).  This file proves that the three restrictions carry no
information: the refined residual is EQUIVALENT to the antecedent-free,
cell-free statement that every K4 chart point has a strictly dominating
spanning tree.

The mechanism is a connectedness argument, not a new certificate.  The set of
chart parameters at which some tree is strictly dominating is open; the set at
which no tree is even weakly dominating is open; the obligation says the two
cover the parameter set; the parameter set is convex, hence preconnected; and
the first set is inhabited.  So the second is empty.

To make "open" elementary the gap is rescaled by the product of the selected
weights, which clears every division and leaves a polynomial matrix.
-/

namespace Gtz

open Matrix

/-! ## Part A. The division-free chart gap -/

/-- **The scaled K4 chart gap.**  `(prod of the selected weights) * G_C`, written
without a single division, hence polynomial in the eleven chart coordinates.
Positive scaling changes neither definiteness, so every definiteness question
about the chart gap is a question about this polynomial matrix. -/
noncomputable def kFourScaledGap (selected : Finset (Fin 6)) (mass weight : Fin 6 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (∑ label ∈ selected,
      (mass label * ∏ other ∈ selected.erase label, weight other)
        • atomMatrix (kFourDirection label))
    - (∏ label ∈ selected, weight label)
        • ∑ label, mass label • atomMatrix (kFourDirection label)

/-- The scaled gap is the chart gap times the product of the selected weights. -/
theorem kFourScaledGap_eq_smul_directionChartGap (selected : Finset (Fin 6))
    (mass weight : Fin 6 → ℝ) (hweightNe : ∀ label, weight label ≠ 0) :
    kFourScaledGap selected mass weight
      = (∏ label ∈ selected, weight label)
          • directionChartGap kFourDirection mass weight selected := by
  have hselectedSum : (∑ label ∈ selected,
        (mass label * ∏ other ∈ selected.erase label, weight other)
          • atomMatrix (kFourDirection label))
      = (∏ label ∈ selected, weight label)
          • ∑ label ∈ selected, (mass label / weight label)
              • atomMatrix (kFourDirection label) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun label hlabel => ?_
    rw [smul_smul]
    congr 1
    rw [← Finset.mul_prod_erase selected weight hlabel]
    field_simp [hweightNe label]
  rw [kFourScaledGap, directionChartGap, smul_sub, hselectedSum]

/-- The scaled gap is symmetric. -/
theorem transpose_kFourScaledGap (selected : Finset (Fin 6)) (mass weight : Fin 6 → ℝ) :
    (kFourScaledGap selected mass weight)ᵀ = kFourScaledGap selected mass weight := by
  rw [kFourScaledGap, Matrix.transpose_sub, Matrix.transpose_smul]
  congr 1
  · rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun label _ => by
      rw [Matrix.transpose_smul, transpose_atomMatrix]
  · congr 1
    rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun label _ => by
      rw [Matrix.transpose_smul, transpose_atomMatrix]

/-- Positive rescaling preserves and reflects positive definiteness. -/
theorem posDef_smul_iff_pos_factor {size : ℕ} {form : Matrix (Fin size) (Fin size) ℝ}
    {factor : ℝ} (hfactor : 0 < factor) : (factor • form).PosDef ↔ form.PosDef := by
  constructor
  · intro hscaled
    have hback := hscaled.smul (a := factor⁻¹) (inv_pos.mpr hfactor)
    rwa [smul_smul, inv_mul_cancel₀ hfactor.ne', one_smul] at hback
  · intro hform
    exact hform.smul hfactor

/-- Positive rescaling preserves and reflects positive semidefiniteness. -/
theorem posSemidef_smul_iff_pos_factor {size : ℕ} {form : Matrix (Fin size) (Fin size) ℝ}
    {factor : ℝ} (hfactor : 0 < factor) : (factor • form).PosSemidef ↔ form.PosSemidef := by
  constructor
  · intro hscaled
    have hback := hscaled.smul (a := factor⁻¹) (inv_pos.mpr hfactor).le
    rwa [smul_smul, inv_mul_cancel₀ hfactor.ne', one_smul] at hback
  · intro hform
    exact hform.smul hfactor.le

/-- The selected-weight product is positive at a chart point. -/
theorem prod_weight_pos (selected : Finset (Fin 6)) (weight : Fin 6 → ℝ)
    (hweightPos : ∀ label, 0 < weight label) : 0 < ∏ label ∈ selected, weight label :=
  Finset.prod_pos fun label _ => hweightPos label

/-- Strict domination of a subset is exactly positive definiteness of the
division-free gap. -/
theorem kFourScaledGap_posDef_iff (selected : Finset (Fin 6)) (mass weight : Fin 6 → ℝ)
    (hweightPos : ∀ label, 0 < weight label) :
    (kFourScaledGap selected mass weight).PosDef
      ↔ (directionChartGap kFourDirection mass weight selected).PosDef := by
  rw [kFourScaledGap_eq_smul_directionChartGap selected mass weight
      fun label => (hweightPos label).ne']
  exact posDef_smul_iff_pos_factor (prod_weight_pos selected weight hweightPos)

/-- Weak domination of a subset is exactly positive semidefiniteness of the
division-free gap. -/
theorem kFourScaledGap_posSemidef_iff (selected : Finset (Fin 6)) (mass weight : Fin 6 → ℝ)
    (hweightPos : ∀ label, 0 < weight label) :
    (kFourScaledGap selected mass weight).PosSemidef
      ↔ (directionChartGap kFourDirection mass weight selected).PosSemidef := by
  rw [kFourScaledGap_eq_smul_directionChartGap selected mass weight
      fun label => (hweightPos label).ne']
  exact posSemidef_smul_iff_pos_factor (prod_weight_pos selected weight hweightPos)

/-! ## Part B. The scaled gap is continuous in the chart coordinates -/

/-- The mass coordinate of a chart parameter is continuous. -/
theorem continuous_kFourMassCoordinate (label : Fin 6) :
    Continuous fun parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) => parameter.1 label :=
  (continuous_apply label).comp continuous_fst

/-- The weight coordinate of a chart parameter is continuous. -/
theorem continuous_kFourWeightCoordinate (label : Fin 6) :
    Continuous fun parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) => parameter.2 label :=
  (continuous_apply label).comp continuous_snd

/-- Every entry of the division-free gap is a polynomial in the chart
coordinates, hence continuous. -/
theorem continuous_kFourScaledGapEntry (selected : Finset (Fin 6))
    (rowIndex colIndex : Fin 3) :
    Continuous fun parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) =>
      kFourScaledGap selected parameter.1 parameter.2 rowIndex colIndex := by
  simp only [kFourScaledGap, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply]
  have hmass : ∀ label : Fin 6,
      Continuous fun parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) => parameter.1 label :=
    continuous_kFourMassCoordinate
  have hweight : ∀ label : Fin 6,
      Continuous fun parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) => parameter.2 label :=
    continuous_kFourWeightCoordinate
  refine Continuous.sub ?_ ?_
  · refine continuous_finsetSum selected fun label _ => ?_
    exact ((hmass label).mul
      (continuous_finsetProd (selected.erase label) fun other _ => hweight other)).mul
      continuous_const
  · refine Continuous.mul (continuous_finsetProd selected fun label _ => hweight label) ?_
    exact continuous_finsetSum Finset.univ fun label _ => (hmass label).mul continuous_const

/-- The quadratic form of a square matrix as an iterated sum. -/
theorem dotProduct_mulVec_expand_sum {size : ℕ} (form : Matrix (Fin size) (Fin size) ℝ)
    (probe : Fin size → ℝ) :
    probe ⬝ᵥ (form *ᵥ probe)
      = ∑ rowIndex, ∑ colIndex, probe rowIndex * (form rowIndex colIndex * probe colIndex) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum]

/-- At a fixed probe the scaled gap's quadratic form is continuous in the chart
coordinates. -/
theorem continuous_kFourScaledGapForm (selected : Finset (Fin 6)) (probe : Fin 3 → ℝ) :
    Continuous fun parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) =>
      probe ⬝ᵥ (kFourScaledGap selected parameter.1 parameter.2 *ᵥ probe) := by
  have hentry : ∀ rowIndex colIndex : Fin 3,
      Continuous fun parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) =>
        kFourScaledGap selected parameter.1 parameter.2 rowIndex colIndex :=
    continuous_kFourScaledGapEntry selected
  simp only [dotProduct_mulVec_expand_sum]
  refine continuous_finsetSum Finset.univ fun rowIndex _ => ?_
  refine continuous_finsetSum Finset.univ fun colIndex _ => ?_
  exact continuous_const.mul ((hentry rowIndex colIndex).mul continuous_const)

/-- A symmetric `3 x 3` matrix is its own upper-triangular expansion. -/
theorem symmetricFinThree_eq_explicit (form : Matrix (Fin 3) (Fin 3) ℝ)
    (hsymmetric : formᵀ = form) :
    form = !![form 0 0, form 0 1, form 0 2;
              form 0 1, form 1 1, form 1 2;
              form 0 2, form 1 2, form 2 2] := by
  have hlower : ∀ rowIndex colIndex : Fin 3, form colIndex rowIndex = form rowIndex colIndex :=
    fun rowIndex colIndex => congrFun (congrFun hsymmetric rowIndex) colIndex
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [hlower 0 1, hlower 0 2, hlower 1 2]

/-- Sylvester at `Fin 3` for an arbitrary symmetric matrix, as an equivalence. -/
theorem posDef_finThree_iff_leadingMinors (form : Matrix (Fin 3) (Fin 3) ℝ)
    (hsymmetric : formᵀ = form) :
    form.PosDef ↔ (0 < form 0 0
      ∧ 0 < form 0 0 * form 1 1 - form 0 1 ^ 2
      ∧ 0 < form 0 0 * form 1 1 * form 2 2 - form 0 0 * form 1 2 ^ 2
          - form 0 1 ^ 2 * form 2 2 + 2 * form 0 1 * form 0 2 * form 1 2
          - form 0 2 ^ 2 * form 1 1) := by
  conv_lhs => rw [symmetricFinThree_eq_explicit form hsymmetric]
  exact leadingMinors_pos_iff_posDef_fin_three (form 0 0) (form 0 1) (form 0 2)
    (form 1 1) (form 1 2) (form 2 2)

/-- **The strict cell of one tree is open.** -/
theorem isOpen_kFourScaledGapPosDef (selected : Finset (Fin 6)) :
    IsOpen {parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) |
      (kFourScaledGap selected parameter.1 parameter.2).PosDef} := by
  have hentry : ∀ rowIndex colIndex : Fin 3,
      Continuous fun parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) =>
        kFourScaledGap selected parameter.1 parameter.2 rowIndex colIndex :=
    continuous_kFourScaledGapEntry selected
  have hsplit : {parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) |
        (kFourScaledGap selected parameter.1 parameter.2).PosDef}
      = ({parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) |
            0 < kFourScaledGap selected parameter.1 parameter.2 0 0}
        ∩ {parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) |
            0 < kFourScaledGap selected parameter.1 parameter.2 0 0
                * kFourScaledGap selected parameter.1 parameter.2 1 1
              - kFourScaledGap selected parameter.1 parameter.2 0 1 ^ 2})
        ∩ {parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) |
            0 < kFourScaledGap selected parameter.1 parameter.2 0 0
                  * kFourScaledGap selected parameter.1 parameter.2 1 1
                  * kFourScaledGap selected parameter.1 parameter.2 2 2
                - kFourScaledGap selected parameter.1 parameter.2 0 0
                  * kFourScaledGap selected parameter.1 parameter.2 1 2 ^ 2
                - kFourScaledGap selected parameter.1 parameter.2 0 1 ^ 2
                  * kFourScaledGap selected parameter.1 parameter.2 2 2
                + 2 * kFourScaledGap selected parameter.1 parameter.2 0 1
                  * kFourScaledGap selected parameter.1 parameter.2 0 2
                  * kFourScaledGap selected parameter.1 parameter.2 1 2
                - kFourScaledGap selected parameter.1 parameter.2 0 2 ^ 2
                  * kFourScaledGap selected parameter.1 parameter.2 1 1} := by
    ext parameter
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
    exact posDef_finThree_iff_leadingMinors _ (transpose_kFourScaledGap _ _ _)
  rw [hsplit]
  refine IsOpen.inter (IsOpen.inter (isOpen_lt continuous_const (hentry 0 0)) ?_) ?_
  · exact isOpen_lt continuous_const
      (((hentry 0 0).mul (hentry 1 1)).sub ((hentry 0 1).pow 2))
  · exact isOpen_lt continuous_const
      (((((((hentry 0 0).mul (hentry 1 1)).mul (hentry 2 2)).sub
        ((hentry 0 0).mul ((hentry 1 2).pow 2))).sub
        (((hentry 0 1).pow 2).mul (hentry 2 2))).add
        (((continuous_const.mul (hentry 0 1)).mul (hentry 0 2)).mul (hentry 1 2))).sub
        (((hentry 0 2).pow 2).mul (hentry 1 1)))

/-- **The weak cell of one tree is closed.** -/
theorem isClosed_kFourScaledGapPosSemidef (selected : Finset (Fin 6)) :
    IsClosed {parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) |
      (kFourScaledGap selected parameter.1 parameter.2).PosSemidef} := by
  have hsplit : {parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) |
        (kFourScaledGap selected parameter.1 parameter.2).PosSemidef}
      = ⋂ probe : Fin 3 → ℝ, {parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ) |
          0 ≤ probe ⬝ᵥ (kFourScaledGap selected parameter.1 parameter.2 *ᵥ probe)} := by
    ext parameter
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hposSemidef probe
      have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hposSemidef).2 probe
      rwa [star_trivial] at hvalue
    · intro hall
      refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
        ⟨isHermitian_of_transpose_eq (transpose_kFourScaledGap selected _ _), fun probe => ?_⟩
      rw [star_trivial]
      exact hall probe
  rw [hsplit]
  exact isClosed_iInter fun probe =>
    isClosed_le continuous_const (continuous_kFourScaledGapForm selected probe)

/-! ## Part C. The band collapses

The refined residual is EQUIVALENT to the antecedent-free, cell-free statement.
Neither the weak-domination antecedent nor either covered region carries any
information: a cell atlas that covers the residual band must cover the whole
chart. -/

/-- The K4 chart parameter set: positive masses, positive weights summing to
one.  Convex, hence preconnected -- that is the whole content. -/
def kFourChartParameterSet : Set ((Fin 6 → ℝ) × (Fin 6 → ℝ)) :=
  {parameter | (∀ label, 0 < parameter.1 label) ∧ (∀ label, 0 < parameter.2 label)
    ∧ ∑ label, parameter.2 label = 1}

theorem convex_kFourChartParameterSet : Convex ℝ kFourChartParameterSet := by
  rintro first ⟨hmassFirst, hweightFirst, hsumFirst⟩ second
    ⟨hmassSecond, hweightSecond, hsumSecond⟩ scaleFirst scaleSecond hscaleFirst
    hscaleSecond hscaleSum
  have hsomePos : 0 < scaleFirst ∨ 0 < scaleSecond := by
    rcases hscaleFirst.lt_or_eq with hpos | hzero
    · exact Or.inl hpos
    · exact Or.inr (by linarith)
  refine ⟨fun label => ?_, fun label => ?_, ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hsomePos with hpos | hpos
    · exact add_pos_of_pos_of_nonneg (mul_pos hpos (hmassFirst label))
        (mul_nonneg hscaleSecond (hmassSecond label).le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hscaleFirst (hmassFirst label).le)
        (mul_pos hpos (hmassSecond label))
  · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hsomePos with hpos | hpos
    · exact add_pos_of_pos_of_nonneg (mul_pos hpos (hweightFirst label))
        (mul_nonneg hscaleSecond (hweightSecond label).le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hscaleFirst (hweightFirst label).le)
        (mul_pos hpos (hweightSecond label))
  · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsumFirst, hsumSecond]
    linarith

/-- Parameters at which SOME spanning tree strictly dominates. -/
def kFourStrictTreeSet : Set ((Fin 6 → ℝ) × (Fin 6 → ℝ)) :=
  ⋃ tree ∈ {tree : Finset (Fin 6) | tree ∈ kFourSpanningTreeList},
    {parameter | (kFourScaledGap tree parameter.1 parameter.2).PosDef}

/-- Parameters at which NO spanning tree even weakly dominates. -/
def kFourNoWeakTreeSet : Set ((Fin 6 → ℝ) × (Fin 6 → ℝ)) :=
  (⋃ tree ∈ {tree : Finset (Fin 6) | tree ∈ kFourSpanningTreeList},
    {parameter | (kFourScaledGap tree parameter.1 parameter.2).PosSemidef})ᶜ

theorem isOpen_kFourStrictTreeSet : IsOpen kFourStrictTreeSet :=
  isOpen_biUnion fun tree _ => isOpen_kFourScaledGapPosDef tree

theorem isOpen_kFourNoWeakTreeSet : IsOpen kFourNoWeakTreeSet :=
  isOpen_compl_iff.mpr (Set.Finite.isClosed_biUnion (List.finite_toSet _)
    fun tree _ => isClosed_kFourScaledGapPosSemidef tree)

/-- A strictly dominating parameter never lies in the no-weak-tree set. -/
theorem notMem_kFourNoWeakTreeSet_of_mem_kFourStrictTreeSet
    (parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ)) (hstrict : parameter ∈ kFourStrictTreeSet) :
    parameter ∉ kFourNoWeakTreeSet := by
  rw [kFourStrictTreeSet, Set.mem_iUnion₂] at hstrict
  obtain ⟨tree, htreeMem, hposDef⟩ := hstrict
  intro hnoWeak
  exact hnoWeak (Set.mem_biUnion htreeMem hposDef.posSemidef)

/-- Every parameter of the set is a chart point. -/
noncomputable def kFourChartPointOfParameters (parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ))
    (hmember : parameter ∈ kFourChartParameterSet) : DirectionChartPoint 6 where
  mass := parameter.1
  weight := parameter.2
  mass_pos := hmember.1
  weight_pos := hmember.2.1
  weight_sum_one := hmember.2.2

theorem kFourChartPointOfParameters_mass (parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ))
    (hmember : parameter ∈ kFourChartParameterSet) :
    (kFourChartPointOfParameters parameter hmember).mass = parameter.1 := rfl

theorem kFourChartPointOfParameters_weight (parameter : (Fin 6 → ℝ) × (Fin 6 → ℝ))
    (hmember : parameter ∈ kFourChartParameterSet) :
    (kFourChartPointOfParameters parameter hmember).weight = parameter.2 := rfl

/-- A strictly dominating card-three subset of the K4 chart is a spanning tree:
the four triangles are never even weakly dominating. -/
theorem kFourStrictTriple_isSpanningTree (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (hposDef : (directionChartGap kFourDirection point.mass point.weight selected).PosDef) :
    selected ∈ kFourSpanningTreeList := by
  rcases cardThreeSubset_isSpanningTreeOrDependentTriple selected hcard with htree | htriangle
  · exact htree
  · exact absurd hposDef.posSemidef
      (kFourDependentTriple_gap_not_posSemidef point selected htriangle)

/-- On either covered region a strictly dominating SPANNING TREE is already
delivered by the landed dispatchers. -/
theorem exists_strictTree_of_kFourCoveredCell (point : DirectionChartPoint 6)
    (hcovered : KFourLayerACellFires point ∨ KFourExchangeStarCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  rcases hcovered with hlayer | hstar
  · obtain ⟨selected, hcard, hposDef⟩ := kFourAtlas_hasStrictTriple_of_layerAFires point hlayer
    exact ⟨selected, kFourStrictTriple_isSpanningTree point selected hcard hposDef, hposDef⟩
  · exact kFourAtlas_hasStrictTree_of_exchangeStarCell point hstar

/-- The uniform chart point: all masses one, all weights one sixth.  This is the
regular tetrahedron's six edge directions with equal weights. -/
noncomputable def kFourUniformPoint : DirectionChartPoint 6 where
  mass := fun _ => 1
  weight := fun _ => 1 / 6
  mass_pos := by intro label; norm_num
  weight_pos := by intro label; norm_num
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num

/-- At the uniform point the gauge tree's gap is the explicit matrix
`3, 1, 1; 1, 3, 1; 1, 1, 3`. -/
theorem kFourUniformPoint_gaugeTreeGap :
    directionChartGap kFourDirection kFourUniformPoint.mass kFourUniformPoint.weight {3, 4, 5}
      = !![(3 : ℝ), 1, 1; 1, 3, 1; 1, 1, 3] := by
  rw [kFourGap_treeThreeFourFive_eq]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [kFourUniformPoint]

/-- The strict set is inhabited: the uniform point has a strictly dominating
spanning tree.  Without this the connectedness argument would be vacuous. -/
theorem kFourUniformPoint_hasStrictTree :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection kFourUniformPoint.mass
        kFourUniformPoint.weight tree).PosDef := by
  refine ⟨{3, 4, 5}, by decide, ?_⟩
  rw [kFourUniformPoint_gaugeTreeGap]
  exact posDef_of_leadingMinors_fin_three 3 1 1 3 1 3 (by norm_num) (by norm_num) (by norm_num)

/-- **The antecedent-free K4 chart statement.**  Every chart point has a
strictly dominating spanning tree -- no weak-domination hypothesis, no cell
exclusion. -/
def KFourEveryPointHasStrictTree : Prop :=
  ∀ point : DirectionChartPoint 6,
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- The easy direction. -/
theorem kFourKnifeBandRefined_of_everyPointHasStrictTree
    (hstrict : KFourEveryPointHasStrictTree) : KFourKnifeBandRefinedWeakToStrict :=
  fun point _ _ _ => hstrict point

/-- The residual, with the two cell exclusions absorbed by the landed
dispatchers: at ANY weakly dominated chart point it already yields a strictly
dominating spanning tree.  Case analysis is by `Classical.em`, never by
`by_cases`, because instance search on the Layer-A region is astronomically
expensive. -/
theorem exists_strictTree_of_weakTree_of_kFourKnifeBandRefined
    (hrefined : KFourKnifeBandRefinedWeakToStrict) (point : DirectionChartPoint 6)
    (hweak : ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  rcases Classical.em (KFourLayerACellFires point) with hlayer | hlayer
  · exact exists_strictTree_of_kFourCoveredCell point (Or.inl hlayer)
  rcases Classical.em (KFourExchangeStarCellFires point) with hstar | hstar
  · exact exists_strictTree_of_kFourCoveredCell point (Or.inr hstar)
  exact hrefined point hlayer hstar hweak

/-- **THE BAND COLLAPSE.**  The refined K4 residual already forces the
antecedent-free statement.  The weak-domination antecedent, the twenty Layer-A
cells and the Layer-B exchange star are all free: any proof of the residual is
a proof that EVERY K4 chart point has a strictly dominating spanning tree.

The argument is topological, not a certificate.  The set of parameters with a
strict tree is open (Sylvester on the division-free gap), the set with no weak
tree is open (a finite union of closed quadratic-form conditions), the residual
says the two cover the convex -- hence preconnected -- parameter set, and the
first is inhabited at the uniform point.  So the second is empty. -/
theorem everyPointHasStrictTree_of_kFourKnifeBandRefined
    (hrefined : KFourKnifeBandRefinedWeakToStrict) : KFourEveryPointHasStrictTree := by
  have hcover : kFourChartParameterSet ⊆ kFourStrictTreeSet ∪ kFourNoWeakTreeSet := by
    intro parameter hmember
    have hweightPos : ∀ label, 0 < parameter.2 label := hmember.2.1
    rcases Classical.em (∃ tree ∈ kFourSpanningTreeList,
        (kFourScaledGap tree parameter.1 parameter.2).PosSemidef) with hweak | hweak
    · left
      obtain ⟨tree, htreeMem, hposSemidef⟩ := hweak
      have hgapSemidef : (directionChartGap kFourDirection parameter.1 parameter.2
          tree).PosSemidef :=
        (kFourScaledGap_posSemidef_iff tree parameter.1 parameter.2 hweightPos).mp hposSemidef
      obtain ⟨strictTree, hstrictMem, hstrictPosDef⟩ :=
        exists_strictTree_of_weakTree_of_kFourKnifeBandRefined hrefined
          (kFourChartPointOfParameters parameter hmember) ⟨tree, htreeMem, hgapSemidef⟩
      exact Set.mem_biUnion hstrictMem
        ((kFourScaledGap_posDef_iff strictTree parameter.1 parameter.2 hweightPos).mpr
          hstrictPosDef)
    · right
      intro hmem
      rw [Set.mem_iUnion₂] at hmem
      obtain ⟨tree, htreeMem, hposSemidef⟩ := hmem
      exact hweak ⟨tree, htreeMem, hposSemidef⟩
  have huniformMember : (kFourUniformPoint.mass, kFourUniformPoint.weight)
      ∈ kFourChartParameterSet :=
    ⟨kFourUniformPoint.mass_pos, kFourUniformPoint.weight_pos,
      kFourUniformPoint.weight_sum_one⟩
  have huniformStrict : (kFourUniformPoint.mass, kFourUniformPoint.weight)
      ∈ kFourStrictTreeSet := by
    obtain ⟨tree, htreeMem, hposDef⟩ := kFourUniformPoint_hasStrictTree
    exact Set.mem_biUnion htreeMem
      ((kFourScaledGap_posDef_iff tree kFourUniformPoint.mass kFourUniformPoint.weight
        kFourUniformPoint.weight_pos).mpr hposDef)
  have hnoWeakEmpty : ∀ parameter ∈ kFourChartParameterSet,
      parameter ∉ kFourNoWeakTreeSet := by
    intro parameter hparameter hnoWeak
    obtain ⟨common, hcommonSet, hcommonBoth⟩ :=
      convex_kFourChartParameterSet.isPreconnected kFourStrictTreeSet kFourNoWeakTreeSet
        isOpen_kFourStrictTreeSet isOpen_kFourNoWeakTreeSet hcover
        ⟨_, huniformMember, huniformStrict⟩ ⟨parameter, hparameter, hnoWeak⟩
    exact notMem_kFourNoWeakTreeSet_of_mem_kFourStrictTreeSet common hcommonBoth.1
      hcommonBoth.2
  intro point
  have hmember : (point.mass, point.weight) ∈ kFourChartParameterSet :=
    ⟨point.mass_pos, point.weight_pos, point.weight_sum_one⟩
  have hstrict : (point.mass, point.weight) ∈ kFourStrictTreeSet := by
    rcases hcover hmember with hcase | hcase
    · exact hcase
    · exact absurd hcase (hnoWeakEmpty _ hmember)
  rw [kFourStrictTreeSet, Set.mem_iUnion₂] at hstrict
  obtain ⟨tree, htreeMem, hposDef⟩ := hstrict
  exact ⟨tree, htreeMem,
    (kFourScaledGap_posDef_iff tree point.mass point.weight point.weight_pos).mp hposDef⟩

/-- **The K4 residual, restated with no antecedent and no cells.** -/
theorem kFourKnifeBandRefined_iff_everyPointHasStrictTree :
    KFourKnifeBandRefinedWeakToStrict ↔ KFourEveryPointHasStrictTree :=
  ⟨everyPointHasStrictTree_of_kFourKnifeBandRefined,
    kFourKnifeBandRefined_of_everyPointHasStrictTree⟩

/-! ## Part D. The determinant of a tree gap is a signed spanning-tree polynomial

Cauchy-Binet applied to `G_T = sum_{c in T} E_c v_c v_c^T - sum_{c not in T} m_c v_c v_c^T`
with `E_c = chartExcess`.  The K4 chart directions are a UNIMODULAR representation
of `M(K4)`, so `det [v_a, v_b, v_c]^2` is one on a spanning tree and zero on a
triangle, and Kirchhoff's matrix-tree theorem gives

  `det G_T = sum over the sixteen spanning trees S of
     (prod over S cap T of E) * (prod over S minus T of (-m))`.

Below are the four STAR trees, where the complement is a triangle, so the
sixteen-term sum collapses to a three-plus-six-plus-three pattern: the tree
product, minus each pair of excesses against the triangle degree at the missing
vertex, plus the excess sum against the triangle's second elementary symmetric
function.  Together with `Gtz.leadingMinors_pos_iff_posDef_fin_three` and the
substrate's live-pair reduction this turns strict domination of a tree into ONE
polynomial sign. -/

/-- The determinant of an explicit `3 x 3` matrix, with no index reduction left
for the caller.  Rewriting with this turns a landed entrywise gap lemma straight
into a polynomial identity. -/
theorem det_explicitFinThree (entryOneOne entryOneTwo entryOneThree entryTwoOne entryTwoTwo
    entryTwoThree entryThreeOne entryThreeTwo entryThreeThree : ℝ) :
    (!![entryOneOne, entryOneTwo, entryOneThree;
        entryTwoOne, entryTwoTwo, entryTwoThree;
        entryThreeOne, entryThreeTwo, entryThreeThree] : Matrix (Fin 3) (Fin 3) ℝ).det
      = entryOneOne * entryTwoTwo * entryThreeThree
        - entryOneOne * entryTwoThree * entryThreeTwo
        - entryOneTwo * entryTwoOne * entryThreeThree
        + entryOneTwo * entryTwoThree * entryThreeOne
        + entryOneThree * entryTwoOne * entryThreeTwo
        - entryOneThree * entryTwoTwo * entryThreeOne := by
  simp [Matrix.det_fin_three]

/-- The gauge star `{3,4,5}`: determinant as a signed spanning-tree polynomial. -/
theorem kFourGapDet_treeThreeFourFive_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {3, 4, 5}).det
      = chartExcess point.mass point.weight 3 * chartExcess point.mass point.weight 4
          * chartExcess point.mass point.weight 5
        - chartExcess point.mass point.weight 3 * chartExcess point.mass point.weight 4
            * (point.mass 1 + point.mass 2)
        - chartExcess point.mass point.weight 3 * chartExcess point.mass point.weight 5
            * (point.mass 0 + point.mass 2)
        - chartExcess point.mass point.weight 4 * chartExcess point.mass point.weight 5
            * (point.mass 0 + point.mass 1)
        + (chartExcess point.mass point.weight 3 + chartExcess point.mass point.weight 4
            + chartExcess point.mass point.weight 5)
          * (point.mass 0 * point.mass 1 + point.mass 0 * point.mass 2
            + point.mass 1 * point.mass 2) := by
  have hthree := (point.weight_pos 3).ne'
  have hfour := (point.weight_pos 4).ne'
  have hfive := (point.weight_pos 5).ne'
  rw [kFourGap_treeThreeFourFive_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The star `{1,2,5}` at node three. -/
theorem kFourGapDet_treeOneTwoFive_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {1, 2, 5}).det
      = chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 2
          * chartExcess point.mass point.weight 5
        - chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 2
            * (point.mass 3 + point.mass 4)
        - chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 5
            * (point.mass 0 + point.mass 4)
        - chartExcess point.mass point.weight 2 * chartExcess point.mass point.weight 5
            * (point.mass 0 + point.mass 3)
        + (chartExcess point.mass point.weight 1 + chartExcess point.mass point.weight 2
            + chartExcess point.mass point.weight 5)
          * (point.mass 0 * point.mass 3 + point.mass 0 * point.mass 4
            + point.mass 3 * point.mass 4) := by
  have hone := (point.weight_pos 1).ne'
  have htwo := (point.weight_pos 2).ne'
  have hfive := (point.weight_pos 5).ne'
  rw [kFourGap_treeOneTwoFive_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The star `{0,2,4}` at node two. -/
theorem kFourGapDet_treeZeroTwoFour_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {0, 2, 4}).det
      = chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 2
          * chartExcess point.mass point.weight 4
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 2
            * (point.mass 3 + point.mass 5)
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 4
            * (point.mass 1 + point.mass 5)
        - chartExcess point.mass point.weight 2 * chartExcess point.mass point.weight 4
            * (point.mass 1 + point.mass 3)
        + (chartExcess point.mass point.weight 0 + chartExcess point.mass point.weight 2
            + chartExcess point.mass point.weight 4)
          * (point.mass 1 * point.mass 3 + point.mass 1 * point.mass 5
            + point.mass 3 * point.mass 5) := by
  have hzero := (point.weight_pos 0).ne'
  have htwo := (point.weight_pos 2).ne'
  have hfour := (point.weight_pos 4).ne'
  rw [kFourGap_treeZeroTwoFour_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The star `{0,1,3}` at node one. -/
theorem kFourGapDet_treeZeroOneThree_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {0, 1, 3}).det
      = chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 1
          * chartExcess point.mass point.weight 3
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 1
            * (point.mass 4 + point.mass 5)
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 3
            * (point.mass 2 + point.mass 5)
        - chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 3
            * (point.mass 2 + point.mass 4)
        + (chartExcess point.mass point.weight 0 + chartExcess point.mass point.weight 1
            + chartExcess point.mass point.weight 3)
          * (point.mass 2 * point.mass 4 + point.mass 2 * point.mass 5
            + point.mass 4 * point.mass 5) := by
  have hzero := (point.weight_pos 0).ne'
  have hone := (point.weight_pos 1).ne'
  have hthree := (point.weight_pos 3).ne'
  rw [kFourGap_treeZeroOneThree_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The path tree `{0, 1, 4}`: determinant as a signed spanning-tree polynomial. -/
theorem kFourGapDet_treeZeroOneFour_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {0, 1, 4}).det
      = chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 1
          * chartExcess point.mass point.weight 4
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 1
            * (point.mass 3 + point.mass 5)
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 4
            * (point.mass 2 + point.mass 5)
        - chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 4
            * (point.mass 2 + point.mass 3 + point.mass 5)
        + chartExcess point.mass point.weight 0
            * (point.mass 2 * point.mass 3 + point.mass 2 * point.mass 5 +
              point.mass 3 * point.mass 5)
        + chartExcess point.mass point.weight 1
            * (point.mass 2 * point.mass 3 + point.mass 2 * point.mass 5)
        + chartExcess point.mass point.weight 4
            * (point.mass 2 * point.mass 3 + point.mass 3 * point.mass 5)
        - point.mass 2 * point.mass 3 * point.mass 5 := by
  have hweightZero := (point.weight_pos 0).ne'
  have hweightOne := (point.weight_pos 1).ne'
  have hweightFour := (point.weight_pos 4).ne'
  rw [kFourGap_treeZeroOneFour_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The path tree `{0, 1, 5}`: determinant as a signed spanning-tree polynomial. -/
theorem kFourGapDet_treeZeroOneFive_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {0, 1, 5}).det
      = chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 1
          * chartExcess point.mass point.weight 5
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 1
            * (point.mass 3 + point.mass 4)
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 5
            * (point.mass 2 + point.mass 3 + point.mass 4)
        - chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 5
            * (point.mass 2 + point.mass 4)
        + chartExcess point.mass point.weight 0
            * (point.mass 2 * point.mass 3 + point.mass 2 * point.mass 4)
        + chartExcess point.mass point.weight 1
            * (point.mass 2 * point.mass 3 + point.mass 2 * point.mass 4 +
              point.mass 3 * point.mass 4)
        + chartExcess point.mass point.weight 5
            * (point.mass 2 * point.mass 3 + point.mass 3 * point.mass 4)
        - point.mass 2 * point.mass 3 * point.mass 4 := by
  have hweightZero := (point.weight_pos 0).ne'
  have hweightOne := (point.weight_pos 1).ne'
  have hweightFive := (point.weight_pos 5).ne'
  rw [kFourGap_treeZeroOneFive_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The path tree `{0, 2, 3}`: determinant as a signed spanning-tree polynomial. -/
theorem kFourGapDet_treeZeroTwoThree_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {0, 2, 3}).det
      = chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 2
          * chartExcess point.mass point.weight 3
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 2
            * (point.mass 4 + point.mass 5)
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 3
            * (point.mass 1 + point.mass 5)
        - chartExcess point.mass point.weight 2 * chartExcess point.mass point.weight 3
            * (point.mass 1 + point.mass 4 + point.mass 5)
        + chartExcess point.mass point.weight 0
            * (point.mass 1 * point.mass 4 + point.mass 1 * point.mass 5 +
              point.mass 4 * point.mass 5)
        + chartExcess point.mass point.weight 2
            * (point.mass 1 * point.mass 4 + point.mass 1 * point.mass 5)
        + chartExcess point.mass point.weight 3
            * (point.mass 1 * point.mass 4 + point.mass 4 * point.mass 5)
        - point.mass 1 * point.mass 4 * point.mass 5 := by
  have hweightZero := (point.weight_pos 0).ne'
  have hweightTwo := (point.weight_pos 2).ne'
  have hweightThree := (point.weight_pos 3).ne'
  rw [kFourGap_treeZeroTwoThree_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The path tree `{0, 2, 5}`: determinant as a signed spanning-tree polynomial. -/
theorem kFourGapDet_treeZeroTwoFive_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {0, 2, 5}).det
      = chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 2
          * chartExcess point.mass point.weight 5
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 2
            * (point.mass 3 + point.mass 4)
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 5
            * (point.mass 1 + point.mass 3 + point.mass 4)
        - chartExcess point.mass point.weight 2 * chartExcess point.mass point.weight 5
            * (point.mass 1 + point.mass 3)
        + chartExcess point.mass point.weight 0
            * (point.mass 1 * point.mass 3 + point.mass 1 * point.mass 4)
        + chartExcess point.mass point.weight 2
            * (point.mass 1 * point.mass 3 + point.mass 1 * point.mass 4 +
              point.mass 3 * point.mass 4)
        + chartExcess point.mass point.weight 5
            * (point.mass 1 * point.mass 4 + point.mass 3 * point.mass 4)
        - point.mass 1 * point.mass 3 * point.mass 4 := by
  have hweightZero := (point.weight_pos 0).ne'
  have hweightTwo := (point.weight_pos 2).ne'
  have hweightFive := (point.weight_pos 5).ne'
  rw [kFourGap_treeZeroTwoFive_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The path tree `{0, 3, 5}`: determinant as a signed spanning-tree polynomial. -/
theorem kFourGapDet_treeZeroThreeFive_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {0, 3, 5}).det
      = chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 3
          * chartExcess point.mass point.weight 5
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 3
            * (point.mass 1 + point.mass 2)
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 5
            * (point.mass 1 + point.mass 2 + point.mass 4)
        - chartExcess point.mass point.weight 3 * chartExcess point.mass point.weight 5
            * (point.mass 2 + point.mass 4)
        + chartExcess point.mass point.weight 0
            * (point.mass 1 * point.mass 4 + point.mass 2 * point.mass 4)
        + chartExcess point.mass point.weight 3
            * (point.mass 1 * point.mass 2 + point.mass 1 * point.mass 4 +
              point.mass 2 * point.mass 4)
        + chartExcess point.mass point.weight 5
            * (point.mass 1 * point.mass 2 + point.mass 1 * point.mass 4)
        - point.mass 1 * point.mass 2 * point.mass 4 := by
  have hweightZero := (point.weight_pos 0).ne'
  have hweightThree := (point.weight_pos 3).ne'
  have hweightFive := (point.weight_pos 5).ne'
  rw [kFourGap_treeZeroThreeFive_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The path tree `{0, 4, 5}`: determinant as a signed spanning-tree polynomial. -/
theorem kFourGapDet_treeZeroFourFive_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {0, 4, 5}).det
      = chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 4
          * chartExcess point.mass point.weight 5
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 4
            * (point.mass 1 + point.mass 2)
        - chartExcess point.mass point.weight 0 * chartExcess point.mass point.weight 5
            * (point.mass 1 + point.mass 2 + point.mass 3)
        - chartExcess point.mass point.weight 4 * chartExcess point.mass point.weight 5
            * (point.mass 1 + point.mass 3)
        + chartExcess point.mass point.weight 0
            * (point.mass 1 * point.mass 3 + point.mass 2 * point.mass 3)
        + chartExcess point.mass point.weight 4
            * (point.mass 1 * point.mass 2 + point.mass 1 * point.mass 3 +
              point.mass 2 * point.mass 3)
        + chartExcess point.mass point.weight 5
            * (point.mass 1 * point.mass 2 + point.mass 2 * point.mass 3)
        - point.mass 1 * point.mass 2 * point.mass 3 := by
  have hweightZero := (point.weight_pos 0).ne'
  have hweightFour := (point.weight_pos 4).ne'
  have hweightFive := (point.weight_pos 5).ne'
  rw [kFourGap_treeZeroFourFive_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The path tree `{1, 2, 3}`: determinant as a signed spanning-tree polynomial. -/
theorem kFourGapDet_treeOneTwoThree_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {1, 2, 3}).det
      = chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 2
          * chartExcess point.mass point.weight 3
        - chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 2
            * (point.mass 4 + point.mass 5)
        - chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 3
            * (point.mass 0 + point.mass 4)
        - chartExcess point.mass point.weight 2 * chartExcess point.mass point.weight 3
            * (point.mass 0 + point.mass 4 + point.mass 5)
        + chartExcess point.mass point.weight 1
            * (point.mass 0 * point.mass 4 + point.mass 0 * point.mass 5 +
              point.mass 4 * point.mass 5)
        + chartExcess point.mass point.weight 2
            * (point.mass 0 * point.mass 4 + point.mass 0 * point.mass 5)
        + chartExcess point.mass point.weight 3
            * (point.mass 0 * point.mass 5 + point.mass 4 * point.mass 5)
        - point.mass 0 * point.mass 4 * point.mass 5 := by
  have hweightOne := (point.weight_pos 1).ne'
  have hweightTwo := (point.weight_pos 2).ne'
  have hweightThree := (point.weight_pos 3).ne'
  rw [kFourGap_treeOneTwoThree_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The path tree `{1, 2, 4}`: determinant as a signed spanning-tree polynomial. -/
theorem kFourGapDet_treeOneTwoFour_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {1, 2, 4}).det
      = chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 2
          * chartExcess point.mass point.weight 4
        - chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 2
            * (point.mass 3 + point.mass 5)
        - chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 4
            * (point.mass 0 + point.mass 3 + point.mass 5)
        - chartExcess point.mass point.weight 2 * chartExcess point.mass point.weight 4
            * (point.mass 0 + point.mass 3)
        + chartExcess point.mass point.weight 1
            * (point.mass 0 * point.mass 3 + point.mass 0 * point.mass 5)
        + chartExcess point.mass point.weight 2
            * (point.mass 0 * point.mass 3 + point.mass 0 * point.mass 5 +
              point.mass 3 * point.mass 5)
        + chartExcess point.mass point.weight 4
            * (point.mass 0 * point.mass 5 + point.mass 3 * point.mass 5)
        - point.mass 0 * point.mass 3 * point.mass 5 := by
  have hweightOne := (point.weight_pos 1).ne'
  have hweightTwo := (point.weight_pos 2).ne'
  have hweightFour := (point.weight_pos 4).ne'
  rw [kFourGap_treeOneTwoFour_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The path tree `{1, 3, 4}`: determinant as a signed spanning-tree polynomial. -/
theorem kFourGapDet_treeOneThreeFour_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {1, 3, 4}).det
      = chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 3
          * chartExcess point.mass point.weight 4
        - chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 3
            * (point.mass 0 + point.mass 2)
        - chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 4
            * (point.mass 0 + point.mass 2 + point.mass 5)
        - chartExcess point.mass point.weight 3 * chartExcess point.mass point.weight 4
            * (point.mass 2 + point.mass 5)
        + chartExcess point.mass point.weight 1
            * (point.mass 0 * point.mass 5 + point.mass 2 * point.mass 5)
        + chartExcess point.mass point.weight 3
            * (point.mass 0 * point.mass 2 + point.mass 0 * point.mass 5 +
              point.mass 2 * point.mass 5)
        + chartExcess point.mass point.weight 4
            * (point.mass 0 * point.mass 2 + point.mass 0 * point.mass 5)
        - point.mass 0 * point.mass 2 * point.mass 5 := by
  have hweightOne := (point.weight_pos 1).ne'
  have hweightThree := (point.weight_pos 3).ne'
  have hweightFour := (point.weight_pos 4).ne'
  rw [kFourGap_treeOneThreeFour_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The path tree `{1, 4, 5}`: determinant as a signed spanning-tree polynomial. -/
theorem kFourGapDet_treeOneFourFive_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {1, 4, 5}).det
      = chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 4
          * chartExcess point.mass point.weight 5
        - chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 4
            * (point.mass 0 + point.mass 2 + point.mass 3)
        - chartExcess point.mass point.weight 1 * chartExcess point.mass point.weight 5
            * (point.mass 0 + point.mass 2)
        - chartExcess point.mass point.weight 4 * chartExcess point.mass point.weight 5
            * (point.mass 0 + point.mass 3)
        + chartExcess point.mass point.weight 1
            * (point.mass 0 * point.mass 3 + point.mass 2 * point.mass 3)
        + chartExcess point.mass point.weight 4
            * (point.mass 0 * point.mass 2 + point.mass 2 * point.mass 3)
        + chartExcess point.mass point.weight 5
            * (point.mass 0 * point.mass 2 + point.mass 0 * point.mass 3 +
              point.mass 2 * point.mass 3)
        - point.mass 0 * point.mass 2 * point.mass 3 := by
  have hweightOne := (point.weight_pos 1).ne'
  have hweightFour := (point.weight_pos 4).ne'
  have hweightFive := (point.weight_pos 5).ne'
  rw [kFourGap_treeOneFourFive_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The path tree `{2, 3, 4}`: determinant as a signed spanning-tree polynomial. -/
theorem kFourGapDet_treeTwoThreeFour_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {2, 3, 4}).det
      = chartExcess point.mass point.weight 2 * chartExcess point.mass point.weight 3
          * chartExcess point.mass point.weight 4
        - chartExcess point.mass point.weight 2 * chartExcess point.mass point.weight 3
            * (point.mass 0 + point.mass 1 + point.mass 5)
        - chartExcess point.mass point.weight 2 * chartExcess point.mass point.weight 4
            * (point.mass 0 + point.mass 1)
        - chartExcess point.mass point.weight 3 * chartExcess point.mass point.weight 4
            * (point.mass 1 + point.mass 5)
        + chartExcess point.mass point.weight 2
            * (point.mass 0 * point.mass 5 + point.mass 1 * point.mass 5)
        + chartExcess point.mass point.weight 3
            * (point.mass 0 * point.mass 1 + point.mass 0 * point.mass 5)
        + chartExcess point.mass point.weight 4
            * (point.mass 0 * point.mass 1 + point.mass 0 * point.mass 5 +
              point.mass 1 * point.mass 5)
        - point.mass 0 * point.mass 1 * point.mass 5 := by
  have hweightTwo := (point.weight_pos 2).ne'
  have hweightThree := (point.weight_pos 3).ne'
  have hweightFour := (point.weight_pos 4).ne'
  rw [kFourGap_treeTwoThreeFour_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-- The path tree `{2, 3, 5}`: determinant as a signed spanning-tree polynomial. -/
theorem kFourGapDet_treeTwoThreeFive_signedTreePolynomial (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {2, 3, 5}).det
      = chartExcess point.mass point.weight 2 * chartExcess point.mass point.weight 3
          * chartExcess point.mass point.weight 5
        - chartExcess point.mass point.weight 2 * chartExcess point.mass point.weight 3
            * (point.mass 0 + point.mass 1 + point.mass 4)
        - chartExcess point.mass point.weight 2 * chartExcess point.mass point.weight 5
            * (point.mass 0 + point.mass 1)
        - chartExcess point.mass point.weight 3 * chartExcess point.mass point.weight 5
            * (point.mass 0 + point.mass 4)
        + chartExcess point.mass point.weight 2
            * (point.mass 0 * point.mass 4 + point.mass 1 * point.mass 4)
        + chartExcess point.mass point.weight 3
            * (point.mass 0 * point.mass 1 + point.mass 1 * point.mass 4)
        + chartExcess point.mass point.weight 5
            * (point.mass 0 * point.mass 1 + point.mass 0 * point.mass 4 +
              point.mass 1 * point.mass 4)
        - point.mass 0 * point.mass 1 * point.mass 4 := by
  have hweightTwo := (point.weight_pos 2).ne'
  have hweightThree := (point.weight_pos 3).ne'
  have hweightFive := (point.weight_pos 5).ne'
  rw [kFourGap_treeTwoThreeFive_eq, det_explicitFinThree]
  simp only [chartExcess]
  field_simp
  ring

/-! ## Part E. The target as a purely polynomial statement, and its scaling normal form -/

/-- The determinant of a symmetric `3 x 3` matrix in leading-minor coordinates. -/
theorem det_finThree_of_symmetric (form : Matrix (Fin 3) (Fin 3) ℝ)
    (hsymmetric : formᵀ = form) :
    form.det = form 0 0 * form 1 1 * form 2 2 - form 0 0 * form 1 2 ^ 2
      - form 0 1 ^ 2 * form 2 2 + 2 * form 0 1 * form 0 2 * form 1 2
      - form 0 2 ^ 2 * form 1 1 := by
  conv_lhs => rw [symmetricFinThree_eq_explicit form hsymmetric]
  rw [det_explicitFinThree]
  ring

/-- Sylvester at `Fin 3` with the third condition read as a determinant. -/
theorem posDef_finThree_iff_cornerBlockDet (form : Matrix (Fin 3) (Fin 3) ℝ)
    (hsymmetric : formᵀ = form) :
    form.PosDef ↔ (0 < form 0 0 ∧ 0 < form 0 0 * form 1 1 - form 0 1 ^ 2 ∧ 0 < form.det) := by
  rw [posDef_finThree_iff_leadingMinors form hsymmetric,
    det_finThree_of_symmetric form hsymmetric]

/-- The strict-tree statement IS the landed selection-free lift threshold: the
corner and the leading two-by-two block are read straight off the landed
entrywise gap lemmas, the determinant is the signed spanning-tree polynomial of
Part D. -/
theorem kFourEveryPointHasStrictTree_iff_someTreeLiftThreshold :
    KFourEveryPointHasStrictTree ↔ KFourSomeTreeLiftThreshold := by
  constructor
  · intro hstrict point
    obtain ⟨tree, htreeMem, hposDef⟩ := hstrict point
    obtain ⟨hcorner, hblock, hdet⟩ :=
      (posDef_finThree_iff_cornerBlockDet _
        (directionChartGap_transpose kFourDirection point.mass point.weight tree)).mp hposDef
    exact ⟨tree, htreeMem, hcorner, hblock, hdet⟩
  · intro hlift point
    obtain ⟨tree, htreeMem, hcorner, hblock, hdet⟩ := hlift point
    exact ⟨tree, htreeMem,
      (posDef_finThree_iff_cornerBlockDet _
        (directionChartGap_transpose kFourDirection point.mass point.weight tree)).mpr
        ⟨hcorner, hblock, hdet⟩⟩

/-- **THE K4 AXIOM AND THE LIFT THRESHOLD ARE THE SAME PROBLEM.**  The landed
`Gtz.kFourKnifeBandRefined_of_someTreeLiftThreshold` says the selection-free lift
threshold discharges the residual.  The converse holds too: the residual, with
its weak antecedent and BOTH cell exclusions, already forces the threshold at
every chart point.  So no cell atlas confined to the residual band can ever
suffice -- an atlas must cover the whole eleven-coordinate chart. -/
theorem kFourKnifeBandRefined_iff_someTreeLiftThreshold :
    KFourKnifeBandRefinedWeakToStrict ↔ KFourSomeTreeLiftThreshold :=
  kFourKnifeBandRefined_iff_everyPointHasStrictTree.trans
    kFourEveryPointHasStrictTree_iff_someTreeLiftThreshold

/-- Scaling every mass by one positive factor scales the chart gap. -/
theorem directionChartGap_smul_mass {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) (factor : ℝ) :
    directionChartGap direction (fun label => factor * mass label) weight selected
      = factor • directionChartGap direction mass weight selected := by
  rw [directionChartGap, directionChartGap, smul_sub, Finset.smul_sum, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun label _ => ?_
    rw [smul_smul]
    congr 1
    ring
  · refine Finset.sum_congr rfl fun label _ => ?_
    rw [smul_smul]

/-- Strict domination is invariant under a common positive rescaling of the
masses: the eleven chart coordinates carry only ten degrees of freedom. -/
theorem posDef_directionChartGap_smul_mass_iff {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) {factor : ℝ} (hfactor : 0 < factor) :
    (directionChartGap direction (fun label => factor * mass label) weight selected).PosDef
      ↔ (directionChartGap direction mass weight selected).PosDef := by
  rw [directionChartGap_smul_mass]
  exact posDef_smul_iff_pos_factor hfactor

/-- The chart point with all masses scaled by one positive factor. -/
noncomputable def kFourScaledMassPoint (point : DirectionChartPoint 6) (factor : ℝ)
    (hfactor : 0 < factor) : DirectionChartPoint 6 where
  mass := fun label => factor * point.mass label
  weight := point.weight
  mass_pos := fun label => mul_pos hfactor (point.mass_pos label)
  weight_pos := point.weight_pos
  weight_sum_one := point.weight_sum_one

/-- The mass-scaling normal form: a strict tree at one point is a strict tree at
every positive rescaling of it. -/
theorem posDef_kFourScaledMassPoint_iff (point : DirectionChartPoint 6) (factor : ℝ)
    (hfactor : 0 < factor) (tree : Finset (Fin 6)) :
    (directionChartGap kFourDirection (kFourScaledMassPoint point factor hfactor).mass
        (kFourScaledMassPoint point factor hfactor).weight tree).PosDef
      ↔ (directionChartGap kFourDirection point.mass point.weight tree).PosDef :=
  posDef_directionChartGap_smul_mass_iff kFourDirection point.mass point.weight tree hfactor

/-! ## Part F. The determinant alone does not decide, even with the block minor

The substrate's live-pair reduction supplies TWO of the three Sylvester
conditions and leaves one determinant.  The witness below shows the hypothesis
is not decoration: there is a K4 chart point and a spanning tree whose gap has
BOTH a positive leading two-by-two block AND a positive determinant, yet is not
positive definite, because its corner is negative.  Any future certificate that
signs only the determinant is therefore incomplete. -/

noncomputable def detPositiveIndefiniteMass : Fin 6 → ℝ
  | 0 => 10000 / 7
  | 1 => 1
  | 2 => 4
  | 3 => 1 / 10
  | 4 => 10000 / 3
  | 5 => 2

noncomputable def detPositiveIndefiniteWeight : Fin 6 → ℝ
  | 0 => 100 / 221
  | 1 => 1 / 221
  | 2 => 15 / 221
  | 3 => 1 / 221
  | 4 => 100 / 221
  | 5 => 4 / 221

noncomputable def detPositiveIndefinitePoint : DirectionChartPoint 6 where
  mass := detPositiveIndefiniteMass
  weight := detPositiveIndefiniteWeight
  mass_pos := by intro label; fin_cases label <;> norm_num [detPositiveIndefiniteMass]
  weight_pos := by intro label; fin_cases label <;> norm_num [detPositiveIndefiniteWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [detPositiveIndefiniteWeight]

theorem detPositiveIndefinitePoint_treeOneTwoFive_gap :
    directionChartGap kFourDirection detPositiveIndefinitePoint.mass
        detPositiveIndefinitePoint.weight {1, 2, 5}
      = !![(-84607 / 70 : ℝ), 10000 / 7, -220;
           10000 / 7, -164744 / 35, -824 / 15;
           -220, -824 / 15, 11503 / 30] := by
  rw [kFourGap_treeOneTwoFive_eq]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [detPositiveIndefinitePoint, detPositiveIndefiniteMass,
      detPositiveIndefiniteWeight]

theorem detPositiveIndefinitePoint_treeZeroTwoFour_gap :
    directionChartGap kFourDirection detPositiveIndefinitePoint.mass
        detPositiveIndefinitePoint.weight {0, 2, 4}
      = !![(120923 / 70 : ℝ), -12100 / 7, 1;
           -12100 / 7, 610768 / 105, -824 / 15;
           1, -824 / 15, 779 / 15] := by
  rw [kFourGap_treeZeroTwoFour_eq]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [detPositiveIndefinitePoint, detPositiveIndefiniteMass,
      detPositiveIndefiniteWeight]

/-- **Positive determinant plus positive block minor still misses.**  At this
chart point the tree `{1,2,5}` has block minor `638463972/175 > 0` and
determinant `2622216365218/1575 > 0`, and is nevertheless indefinite. -/
theorem exists_kFourChartPoint_tree_positiveBlockAndDet_not_posDef :
    ∃ point : DirectionChartPoint 6, ∃ tree ∈ kFourSpanningTreeList,
      0 < directionChartGap kFourDirection point.mass point.weight tree 0 0
          * directionChartGap kFourDirection point.mass point.weight tree 1 1
        - directionChartGap kFourDirection point.mass point.weight tree 0 1 ^ 2
      ∧ 0 < (directionChartGap kFourDirection point.mass point.weight tree).det
      ∧ ¬ (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  refine ⟨detPositiveIndefinitePoint, {1, 2, 5}, by decide, ?_, ?_, ?_⟩
  · rw [detPositiveIndefinitePoint_treeOneTwoFive_gap]
    norm_num
  · rw [detPositiveIndefinitePoint_treeOneTwoFive_gap, det_explicitFinThree]
    norm_num
  · rw [detPositiveIndefinitePoint_treeOneTwoFive_gap]
    intro hposDef
    have hcorner := posDef_fin_three_corner_pos hposDef
    norm_num at hcorner

/-- ...and the same point is NOT a counterexample to the axiom: the tree
`{0,2,4}` is strictly dominating there. -/
theorem detPositiveIndefinitePoint_hasStrictTree :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection detPositiveIndefinitePoint.mass
        detPositiveIndefinitePoint.weight tree).PosDef := by
  refine ⟨{0, 2, 4}, by decide, ?_⟩
  rw [detPositiveIndefinitePoint_treeZeroTwoFour_gap]
  exact posDef_of_leadingMinors_fin_three (120923 / 70) (-12100 / 7) 1 (610768 / 105)
    (-824 / 15) (779 / 15) (by norm_num) (by norm_num) (by norm_num)

/-! ## Part G. The K4 endgame in the one-determinant shape

Every K4 chart point realizes a design (its moment matrix is positive definite
because labels three, four and five are the coordinate axes), and every rank
three design carries a LIVE PAIR.  On a live pair two of the three Sylvester
conditions are free, so the residual is exactly: exhibit ONE label off the pair
whose tie leg is positive.  This is the same residual shape the one-line, the
two-meeting-lines and the U(3,6) classes were reduced to. -/

/-- **The K4 residual in the one-determinant shape.**  If at every chart point
the design's live pair admits a third label with positive tie leg, then every
chart point has a strictly dominating spanning tree -- and hence, by the band
collapse, the refined K4 residual holds. -/
theorem kFourEveryPointHasStrictTree_of_livePairCompletes
    (hcompletes : ∀ (point : DirectionChartPoint 6) (design : WeightedDesign 6 3),
      design.weight = point.weight →
      (∀ selected : Finset (Fin 6), (subsetSum design selected - 1).PosDef
          ↔ (directionChartGap kFourDirection point.mass point.weight selected).PosDef) →
      ∀ pivotLabel pairFirst : Fin 6, pivotLabel ≠ pairFirst →
        0 < heavyExcess design pivotLabel → 0 < heavyExcess design pairFirst →
        0 < pairGapExcessOf design pivotLabel pairFirst →
          ∃ pairSecond : Fin 6, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
            ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond) :
    KFourEveryPointHasStrictTree := by
  intro point
  obtain ⟨design, hweight, hbridge⟩ := exists_design_of_chartPoint kFourDirection point
    (posDef_massMoment_kFourDirection point)
  obtain ⟨pivotLabel, pairFirst, hne, hpivot, hpair, hminor, hdeterminantOnly⟩ :=
    exists_livePair_determinantOnly design
  obtain ⟨pairSecond, hpivotSecond, hpairSecond, htie⟩ :=
    hcompletes point design hweight (fun selected => (hbridge selected).1) pivotLabel pairFirst
      hne hpivot hpair hminor
  have hdesignPosDef :=
    (hdeterminantOnly pairSecond hpivotSecond hpairSecond htie).1
  have hchartPosDef := ((hbridge {pivotLabel, pairFirst, pairSecond}).1).mp hdesignPosDef
  exact ⟨{pivotLabel, pairFirst, pairSecond},
    kFourStrictTriple_isSpanningTree point _
      (card_labelTriple_eq_three hne hpivotSecond hpairSecond) hchartPosDef,
    hchartPosDef⟩

/-- The same residual discharges the Skeleton obligation itself. -/
theorem kFourKnifeBandRefined_of_livePairCompletes
    (hcompletes : ∀ (point : DirectionChartPoint 6) (design : WeightedDesign 6 3),
      design.weight = point.weight →
      (∀ selected : Finset (Fin 6), (subsetSum design selected - 1).PosDef
          ↔ (directionChartGap kFourDirection point.mass point.weight selected).PosDef) →
      ∀ pivotLabel pairFirst : Fin 6, pivotLabel ≠ pairFirst →
        0 < heavyExcess design pivotLabel → 0 < heavyExcess design pairFirst →
        0 < pairGapExcessOf design pivotLabel pairFirst →
          ∃ pairSecond : Fin 6, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
            ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond) :
    KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefined_of_everyPointHasStrictTree
    (kFourEveryPointHasStrictTree_of_livePairCompletes hcompletes)

/-! ## Part H. Non-vacuity at the canonical band inhabitant -/

/-- The star `{0,1,3}` gap at `Gtz.bandResidualWitnessPoint`, in exact rationals. -/
theorem bandResidualWitnessPoint_starGap :
    directionChartGap kFourDirection bandResidualWitnessPoint.mass
        bandResidualWitnessPoint.weight {0, 1, 3}
      = !![(196 : ℝ), -7, -144; -7, 3, 1; -144, 1, 141] := by
  rw [kFourGap_treeZeroOneThree_eq]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [bandResidualWitnessMass, bandResidualWitnessWeight]

/-- **The canonical band inhabitant is not a counterexample.**  The chart point
that fires no Layer-A cell and no exchange star still carries a strictly
dominating spanning tree, namely the star `{0,1,3}` at node one. -/
theorem bandResidualWitnessPoint_hasStrictTree_atlas :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection bandResidualWitnessPoint.mass
        bandResidualWitnessPoint.weight tree).PosDef := by
  refine ⟨{0, 1, 3}, by decide, ?_⟩
  rw [bandResidualWitnessPoint_starGap]
  exact posDef_of_leadingMinors_fin_three 196 (-7) (-144) 3 1 141
    (by norm_num) (by norm_num) (by norm_num)

/-- The band inhabitant witnesses that the antecedent-free statement is not
vacuously about an empty region: the residual band is inhabited and the
conclusion holds there. -/
theorem bandResidualWitnessPoint_offBothCoveredRegions_hasStrictTree :
    ¬ KFourLayerACellFires bandResidualWitnessPoint
      ∧ ¬ KFourExchangeStarCellFires bandResidualWitnessPoint
      ∧ ∃ tree ∈ kFourSpanningTreeList,
          (directionChartGap kFourDirection bandResidualWitnessPoint.mass
            bandResidualWitnessPoint.weight tree).PosDef :=
  ⟨bandResidualWitnessPoint_notLayerACellFires,
    bandResidualWitnessPoint_notExchangeStarCellFires,
    bandResidualWitnessPoint_hasStrictTree_atlas⟩

end Gtz
