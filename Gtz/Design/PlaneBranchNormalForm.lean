import Gtz.Design.AxisBaseOffConic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace Gtz

open Matrix

noncomputable def baseThreeLabel : Fin 3 -> Fin 6 := ![0, 1, 2]

theorem baseThreeLabel_injective : Function.Injective baseThreeLabel := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [baseThreeLabel] at hij ⊢

/-- Applying an invertible linear map to every atom preserves off-conicity. -/
theorem hasNoCommonQuadric_congrAtom
    (atom : Fin 6 -> Fin 3 -> ℝ) (P : Matrix (Fin 3) (Fin 3) ℝ)
    (hP : IsUnit P.det) (hoffConic : HasNoCommonQuadric atom) :
    HasNoCommonQuadric (fun label => Pᵀ *ᵥ atom label) := by
  intro form hformSymm hquadric
  let pulled := P * form * Pᵀ
  have hpulledSymm : pulledᵀ = pulled := by
    dsimp [pulled]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hformSymm, Matrix.mul_assoc]
  have hpulledQuadric : ∀ label,
      dotProduct (atom label) (pulled *ᵥ atom label) = 0 := by
    intro label
    have hcongr := dotProduct_congruence form Pᵀ (atom label)
    rw [Matrix.transpose_transpose] at hcongr
    rw [hcongr]
    exact hquadric label
  have hpulledZero : pulled = 0 :=
    hoffConic pulled hpulledSymm hpulledQuadric
  have hPT : IsUnit Pᵀ.det := by
    rwa [Matrix.det_transpose]
  calc
    form = (P⁻¹ * P) * form * (Pᵀ * (Pᵀ)⁻¹) := by
      rw [Matrix.nonsing_inv_mul P hP, Matrix.mul_nonsing_inv Pᵀ hPT,
        Matrix.one_mul, Matrix.mul_one]
    _ = P⁻¹ * pulled * (Pᵀ)⁻¹ := by
      dsimp [pulled]
      noncomm_ring
    _ = 0 := by rw [hpulledZero, Matrix.mul_zero, Matrix.zero_mul]

/-- Congruence transports every strict-subset test to the transformed atoms,
provided the identity is transported to the metric `PᵀP`. -/
theorem posDef_congrAtom_sub_metric_iff
    (design : WeightedDesign 6 3) (P : Matrix (Fin 3) (Fin 3) ℝ)
    (hP : IsUnit P.det) (selected : Finset (Fin 6)) :
    ((∑ label ∈ selected, atomMatrix (Pᵀ *ᵥ design.atom label)) - Pᵀ * P).PosDef
      ↔ (subsetSum design selected - 1).PosDef := by
  have hrewrite :
      (∑ label ∈ selected, atomMatrix (Pᵀ *ᵥ design.atom label)) - Pᵀ * P
        = Pᵀ * (subsetSum design selected - 1) * P := by
    rw [sum_atomMatrix_conj, subsetSum]
    noncomm_ring
  rw [hrewrite]
  exact (posDef_congr_right (transpose_gap_eq_gap design selected) hP).symm

/-- The square matrix whose rows are the three co-weighted base atoms. -/
noncomputable def planeBaseFrame (design : WeightedDesign 6 3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun baseIndex coordinate =>
    Real.sqrt (1 - design.weight (baseThreeLabel baseIndex))
      * design.atom (baseThreeLabel baseIndex) coordinate

/-- The frame operator of `planeBaseFrame` is exactly the positive
complementary-weighted base triple used by the plane branch. -/
theorem planeBaseFrame_transpose_mul_self (design : WeightedDesign 6 3) :
    (planeBaseFrame design)ᵀ * planeBaseFrame design
      = (1 - design.weight 0) • atomMatrix (design.atom 0)
          + (1 - design.weight 1) • atomMatrix (design.atom 1)
          + (1 - design.weight 2) • atomMatrix (design.atom 2) := by
  ext row col
  simp only [Matrix.mul_apply, Matrix.transpose_apply, planeBaseFrame,
    Matrix.of_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.smul_apply,
    atomMatrix, Matrix.vecMulVec_apply, baseThreeLabel, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    smul_eq_mul]
  have hzero : 0 ≤ 1 - design.weight 0 := by
    linarith [weight_lt_one design (by norm_num) 0]
  have hone : 0 ≤ 1 - design.weight 1 := by
    linarith [weight_lt_one design (by norm_num) 1]
  have htwo : 0 ≤ 1 - design.weight 2 := by
    linarith [weight_lt_one design (by norm_num) 2]
  rw [show Real.sqrt (1 - design.weight 0) * design.atom 0 row
        * (Real.sqrt (1 - design.weight 0) * design.atom 0 col)
      = (Real.sqrt (1 - design.weight 0) * Real.sqrt (1 - design.weight 0))
          * (design.atom 0 row * design.atom 0 col) by ring,
    show Real.sqrt (1 - design.weight 1) * design.atom 1 row
        * (Real.sqrt (1 - design.weight 1) * design.atom 1 col)
      = (Real.sqrt (1 - design.weight 1) * Real.sqrt (1 - design.weight 1))
          * (design.atom 1 row * design.atom 1 col) by ring,
    show Real.sqrt (1 - design.weight 2) * design.atom 2 row
        * (Real.sqrt (1 - design.weight 2) * design.atom 2 col)
      = (Real.sqrt (1 - design.weight 2) * Real.sqrt (1 - design.weight 2))
          * (design.atom 2 row * design.atom 2 col) by ring,
    Real.mul_self_sqrt hzero, Real.mul_self_sqrt hone,
    Real.mul_self_sqrt htwo]

/-- Line-freeness makes the co-weighted base row frame invertible. -/
theorem planeBaseFrame_det_isUnit (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    IsUnit (planeBaseFrame design).det := by
  have hpd := complementaryWeightedBaseTriple_posDef_of_lineFree design hlineFree
  have hdetPos := hpd.det_pos
  rw [← planeBaseFrame_transpose_mul_self design, Matrix.det_mul,
    Matrix.det_transpose] at hdetPos
  rw [isUnit_iff_ne_zero]
  intro hzero
  rw [hzero] at hdetPos
  norm_num at hdetPos

/-- The direct normalizer: invert the square co-weighted base row frame. -/
noncomputable def planeBaseNormalizer (design : WeightedDesign 6 3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (planeBaseFrame design)⁻¹

theorem planeBaseNormalizer_det_isUnit (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    IsUnit (planeBaseNormalizer design).det := by
  exact (planeBaseFrame design).isUnit_nonsing_inv_det
    (planeBaseFrame_det_isUnit design hlineFree)

/-- After applying the direct normalizer, each co-weighted base atom is the
corresponding coordinate vector. -/
theorem planeBaseNormalizer_baseAtom (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (baseIndex : Fin 3) :
    Real.sqrt (1 - design.weight (baseThreeLabel baseIndex)) •
        ((planeBaseNormalizer design)ᵀ *ᵥ
          design.atom (baseThreeLabel baseIndex))
      = Pi.single baseIndex 1 := by
  have hinverse := Matrix.mul_nonsing_inv (planeBaseFrame design)
    (planeBaseFrame_det_isUnit design hlineFree)
  ext coordinate
  have hentry := congrFun (congrFun hinverse baseIndex) coordinate
  simp only [planeBaseNormalizer, planeBaseFrame, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul] at hentry ⊢
  rw [Finset.mul_sum]
  by_cases heq : coordinate = baseIndex
  · subst coordinate
    simpa [Pi.single_apply, Matrix.one_apply, mul_comm, mul_left_comm, mul_assoc]
      using hentry
  · have hne : baseIndex ≠ coordinate := Ne.symm heq
    simpa [Pi.single_apply, Matrix.one_apply, heq, hne, mul_comm, mul_left_comm,
      mul_assoc] using hentry

/-- Axis length of the normalized base atom. -/
noncomputable def planeBaseScale (design : WeightedDesign 6 3) (baseIndex : Fin 3) : ℝ :=
  (Real.sqrt (1 - design.weight (baseThreeLabel baseIndex)))⁻¹

/-- The three transformed free atoms. -/
noncomputable def planeNormalizedFreeAtom (design : WeightedDesign 6 3) :
    Fin 3 -> Fin 3 -> ℝ :=
  fun freeIndex => (planeBaseNormalizer design)ᵀ *ᵥ
    design.atom (freeThreeLabel freeIndex)

theorem planeBaseScale_ne_zero (design : WeightedDesign 6 3) (baseIndex : Fin 3) :
    planeBaseScale design baseIndex ≠ 0 := by
  apply inv_ne_zero
  apply Real.sqrt_ne_zero'.mpr
  linarith [weight_lt_one design (by norm_num) (baseThreeLabel baseIndex)]

/-- Removing the nonzero square-root factor identifies each transformed base
atom itself with its scaled coordinate vector. -/
theorem planeBaseNormalizer_baseAtom_eq_smul_single
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (baseIndex : Fin 3) :
    (planeBaseNormalizer design)ᵀ *ᵥ
        design.atom (baseThreeLabel baseIndex)
      = planeBaseScale design baseIndex • Pi.single baseIndex 1 := by
  let root := Real.sqrt (1 - design.weight (baseThreeLabel baseIndex))
  have hroot : root ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    linarith [weight_lt_one design (by norm_num) (baseThreeLabel baseIndex)]
  have hscaled := planeBaseNormalizer_baseAtom design hlineFree baseIndex
  calc
    (planeBaseNormalizer design)ᵀ *ᵥ design.atom (baseThreeLabel baseIndex)
        = (root⁻¹ * root) •
            ((planeBaseNormalizer design)ᵀ *ᵥ
              design.atom (baseThreeLabel baseIndex)) := by
              rw [inv_mul_cancel₀ hroot, one_smul]
    _ = root⁻¹ • (root •
            ((planeBaseNormalizer design)ᵀ *ᵥ
              design.atom (baseThreeLabel baseIndex))) := by
          rw [smul_smul]
    _ = root⁻¹ • Pi.single baseIndex 1 := by rw [hscaled]
    _ = planeBaseScale design baseIndex • Pi.single baseIndex 1 := rfl

/-- **The actual plane branch in axis coordinates.**  The normalizer sends the
entire six-atom family, not merely its frame operator, to `axisBaseAtom`.
Thus every subsequent coordinate calculation is definitionally about the
same transformed GTZ instance. -/
theorem planeBaseNormalizer_atom_eq_axisBaseAtom
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    (fun label => (planeBaseNormalizer design)ᵀ *ᵥ design.atom label)
      = axisBaseAtom (planeBaseScale design) (planeNormalizedFreeAtom design) := by
  funext label
  fin_cases label
  · have h := planeBaseNormalizer_baseAtom_eq_smul_single design hlineFree 0
    change (planeBaseNormalizer design)ᵀ *ᵥ design.atom 0 =
      axisBaseAtom (planeBaseScale design) (planeNormalizedFreeAtom design) 0
    simp [baseThreeLabel] at h
    rw [h]
    ext coordinate
    fin_cases coordinate <;>
      simp [axisBaseAtom, planeBaseScale, baseThreeLabel]
  · have h := planeBaseNormalizer_baseAtom_eq_smul_single design hlineFree 1
    change (planeBaseNormalizer design)ᵀ *ᵥ design.atom 1 =
      axisBaseAtom (planeBaseScale design) (planeNormalizedFreeAtom design) 1
    simp [baseThreeLabel] at h
    rw [h]
    ext coordinate
    fin_cases coordinate <;>
      simp [axisBaseAtom, planeBaseScale, baseThreeLabel]
  · have h := planeBaseNormalizer_baseAtom_eq_smul_single design hlineFree 2
    change (planeBaseNormalizer design)ᵀ *ᵥ design.atom 2 =
      axisBaseAtom (planeBaseScale design) (planeNormalizedFreeAtom design) 2
    simp [baseThreeLabel] at h
    rw [h]
    ext coordinate
    fin_cases coordinate <;>
      simp [axisBaseAtom, planeBaseScale, baseThreeLabel]
  · change (planeBaseNormalizer design)ᵀ *ᵥ design.atom 3 =
      planeNormalizedFreeAtom design 0
    rfl
  · change (planeBaseNormalizer design)ᵀ *ᵥ design.atom 4 =
      planeNormalizedFreeAtom design 1
    rfl
  · change (planeBaseNormalizer design)ᵀ *ᵥ design.atom 5 =
      planeNormalizedFreeAtom design 2
    rfl

/-- **The plane branch's off-conicity is one explicit 3x3 determinant.** -/
theorem planeNormalizedFreeAtom_offDiagonalGrid_det_ne_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom) :
    (freeOffDiagonalGrid (planeNormalizedFreeAtom design)).det ≠ 0 := by
  have hnormalOffConic : HasNoCommonQuadric
      (fun label => (planeBaseNormalizer design)ᵀ *ᵥ design.atom label) :=
    hasNoCommonQuadric_congrAtom design.atom (planeBaseNormalizer design)
      (planeBaseNormalizer_det_isUnit design hlineFree) hoffConic
  rw [planeBaseNormalizer_atom_eq_axisBaseAtom design hlineFree] at hnormalOffConic
  exact freeOffDiagonalGrid_det_ne_zero_of_hasNoCommonQuadric
    (planeBaseScale design) (planeNormalizedFreeAtom design) hnormalOffConic

/-- Line-freeness independently says that the three normalized free atoms are a
basis.  This is not a consequence of the off-diagonal-grid determinant and is
needed when the full-complement candidate is put in free-frame coordinates. -/
theorem planeNormalizedFreeAtom_tripleBracket_ne_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    tripleBracket (planeNormalizedFreeAtom design 0)
      (planeNormalizedFreeAtom design 1) (planeNormalizedFreeAtom design 2) ≠ 0 := by
  have horiginal : tripleBracket (design.atom 3) (design.atom 4) (design.atom 5) ≠ 0 :=
    atomBracket_ne_zero_of_lineFree design hlineFree (by decide) (by decide) (by decide)
  let P := planeBaseNormalizer design
  have hPne : P.det ≠ 0 :=
    (isUnit_iff_ne_zero.mp (planeBaseNormalizer_det_isUnit design hlineFree))
  have htransform :
      tripleBracket (Pᵀ *ᵥ design.atom 3) (Pᵀ *ᵥ design.atom 4)
          (Pᵀ *ᵥ design.atom 5)
        = tripleBracket (design.atom 3) (design.atom 4) (design.atom 5) * P.det := by
    rw [tripleBracket, tripleBracket, ← Matrix.det_mul]
    congr 1
    ext row col
    fin_cases row
    · simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
    · simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
    · simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  change tripleBracket (Pᵀ *ᵥ design.atom 3) (Pᵀ *ᵥ design.atom 4)
      (Pᵀ *ᵥ design.atom 5) ≠ 0
  rw [htransform]
  exact mul_ne_zero horiginal hPne

/-- Row frame of the three normalized free atoms. -/
noncomputable def planeNormalizedFreeFrame (design : WeightedDesign 6 3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![planeNormalizedFreeAtom design 0,
    planeNormalizedFreeAtom design 1, planeNormalizedFreeAtom design 2]

theorem planeNormalizedFreeFrame_det_ne_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    (planeNormalizedFreeFrame design).det ≠ 0 := by
  simpa [planeNormalizedFreeFrame, tripleBracket] using
    planeNormalizedFreeAtom_tripleBracket_ne_zero design hlineFree

/-- The direct normalizer whitens the complementary-weighted base operator. -/
theorem planeBaseNormalizer_whitens (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    (planeBaseNormalizer design)ᵀ
        * ((1 - design.weight 0) • atomMatrix (design.atom 0)
          + (1 - design.weight 1) • atomMatrix (design.atom 1)
          + (1 - design.weight 2) • atomMatrix (design.atom 2))
        * planeBaseNormalizer design = 1 := by
  have hframe := planeBaseFrame_det_isUnit design hlineFree
  rw [← planeBaseFrame_transpose_mul_self design, planeBaseNormalizer,
    Matrix.transpose_nonsing_inv, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (by rwa [Matrix.det_transpose] :
      IsUnit (planeBaseFrame design)ᵀ.det),
    Matrix.one_mul, Matrix.mul_nonsing_inv _ hframe]

/-- The unweighted sum of the three axis-base atoms is diagonal. -/
theorem axisBaseAtom_baseTripleSum
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ) :
    (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)),
        atomMatrix (axisBaseAtom baseScale freeAtom label))
      = Matrix.diagonal (fun index => (baseScale index) ^ 2) := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [axisBaseAtom, atomMatrix, pow_two]

/-- In normal coordinates the transported identity metric is diagonal minus
the hidden rank-one gap atom. -/
theorem planeBaseNormalizer_metric_eq_diagonal_sub_hidden
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {hiddenRaw : Fin 3 -> ℝ}
    (hgap : subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1
      = atomMatrix hiddenRaw) :
    (planeBaseNormalizer design)ᵀ * planeBaseNormalizer design
      = Matrix.diagonal (fun index => (planeBaseScale design index) ^ 2)
          - atomMatrix ((planeBaseNormalizer design)ᵀ *ᵥ hiddenRaw) := by
  let P := planeBaseNormalizer design
  have hcongr := congrArg (fun matrix => Pᵀ * matrix * P) hgap
  have htransformedGap :
      (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)),
          atomMatrix (Pᵀ *ᵥ design.atom label)) - Pᵀ * P
        = atomMatrix (Pᵀ *ᵥ hiddenRaw) := by
    rw [subsetSum] at hcongr
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_one] at hcongr
    simp_rw [transpose_mul_atomMatrix_mul] at hcongr
    exact hcongr
  have hatomFamily := planeBaseNormalizer_atom_eq_axisBaseAtom design hlineFree
  have hbaseSum :
      (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)),
          atomMatrix (Pᵀ *ᵥ design.atom label))
        = Matrix.diagonal (fun index => (planeBaseScale design index) ^ 2) := by
    change (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      atomMatrix ((fun c => Pᵀ *ᵥ design.atom c) label)) = _
    rw [hatomFamily]
    exact axisBaseAtom_baseTripleSum
      (planeBaseScale design) (planeNormalizedFreeAtom design)
  change Pᵀ * P = _
  rw [hbaseSum] at htransformedGap
  calc
    Pᵀ * P = Matrix.diagonal (fun index => (planeBaseScale design index) ^ 2)
        - (Matrix.diagonal (fun index => (planeBaseScale design index) ^ 2)
          - Pᵀ * P) := by noncomm_ring
    _ = Matrix.diagonal (fun index => (planeBaseScale design index) ^ 2)
        - atomMatrix (Pᵀ *ᵥ hiddenRaw) := by rw [htransformedGap]

/-- **Complete axis normal form of the off-conic plane branch.**  It packages
the three facts needed by an exact polynomial endgame: a four-vector Parseval
identity, the diagonal-minus-rank-one metric, and the nonzero off-diagonal
Veronese determinant.  The final conjunct says every original GTZ candidate
is equivalent to the corresponding metric-relative candidate here. -/
theorem exists_planeBranch_axisNormalForm
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ∃ hidden : Fin 3 -> ℝ,
      atomMatrix hidden
          + (design.weight 3 • atomMatrix (planeNormalizedFreeAtom design 0)
            + design.weight 4 • atomMatrix (planeNormalizedFreeAtom design 1)
            + design.weight 5 • atomMatrix (planeNormalizedFreeAtom design 2)) = 1
      ∧ (planeBaseNormalizer design)ᵀ * planeBaseNormalizer design
          = Matrix.diagonal (fun index => (planeBaseScale design index) ^ 2)
              - atomMatrix hidden
      ∧ (freeOffDiagonalGrid (planeNormalizedFreeAtom design)).det ≠ 0
      ∧ ∀ selected : Finset (Fin 6),
          ((∑ label ∈ selected,
              atomMatrix ((planeBaseNormalizer design)ᵀ *ᵥ design.atom label))
              - (planeBaseNormalizer design)ᵀ * planeBaseNormalizer design).PosDef
            ↔ (subsetSum design selected - 1).PosDef := by
  obtain ⟨axis, scale, _haxisUnit, hscalePos, hgap⟩ :=
    exists_unitAxis_gapAtom_of_offConic_planeBranch design hoffConic
      hdominates hfree
  let hiddenRaw := Real.sqrt scale • axis
  let P := planeBaseNormalizer design
  let hidden := Pᵀ *ᵥ hiddenRaw
  refine ⟨hidden, ?_, ?_,
    planeNormalizedFreeAtom_offDiagonalGrid_det_ne_zero design hlineFree hoffConic,
    fun selected => posDef_congrAtom_sub_metric_iff design P
      (planeBaseNormalizer_det_isUnit design hlineFree) selected⟩
  · have hdecomposition :=
      dominationGap_add_weightedComplement_eq_complementaryWeightedSelected design
        ({0, 1, 2} : Finset (Fin 6))
    change subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1
      = atomMatrix hiddenRaw at hgap
    rw [hgap] at hdecomposition
    have hcomplement : ({0, 1, 2} : Finset (Fin 6))ᶜ = {3, 4, 5} := by decide
    rw [hcomplement, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at hdecomposition
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at hdecomposition
    have hfreeConj :
        Pᵀ * (design.weight 3 • atomMatrix (design.atom 3)
            + (design.weight 4 • atomMatrix (design.atom 4)
              + design.weight 5 • atomMatrix (design.atom 5))) * P
          = design.weight 3 • atomMatrix (Pᵀ *ᵥ design.atom 3)
            + (design.weight 4 • atomMatrix (Pᵀ *ᵥ design.atom 4)
              + design.weight 5 • atomMatrix (Pᵀ *ᵥ design.atom 5)) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul, transpose_mul_atomMatrix_mul,
        Matrix.mul_smul, Matrix.smul_mul, transpose_mul_atomMatrix_mul,
        Matrix.mul_smul, Matrix.smul_mul, transpose_mul_atomMatrix_mul]
    have hleftConj :
        Pᵀ * (atomMatrix hiddenRaw
            + (design.weight 3 • atomMatrix (design.atom 3)
              + (design.weight 4 • atomMatrix (design.atom 4)
                + design.weight 5 • atomMatrix (design.atom 5)))) * P
          = atomMatrix (Pᵀ *ᵥ hiddenRaw)
            + (design.weight 3 • atomMatrix (Pᵀ *ᵥ design.atom 3)
              + (design.weight 4 • atomMatrix (Pᵀ *ᵥ design.atom 4)
                + design.weight 5 • atomMatrix (Pᵀ *ᵥ design.atom 5))) := by
      rw [Matrix.mul_add, Matrix.add_mul, transpose_mul_atomMatrix_mul, hfreeConj]
    have hbaseWhiten :
        Pᵀ * ((1 - design.weight 0) • atomMatrix (design.atom 0)
            + ((1 - design.weight 1) • atomMatrix (design.atom 1)
              + (1 - design.weight 2) • atomMatrix (design.atom 2))) * P = 1 := by
      simpa [P, add_assoc] using planeBaseNormalizer_whitens design hlineFree
    change atomMatrix (Pᵀ *ᵥ hiddenRaw)
        + (design.weight 3 • atomMatrix (Pᵀ *ᵥ design.atom 3)
          + design.weight 4 • atomMatrix (Pᵀ *ᵥ design.atom 4)
          + design.weight 5 • atomMatrix (Pᵀ *ᵥ design.atom 5)) = 1
    rw [add_assoc]
    calc
      atomMatrix (Pᵀ *ᵥ hiddenRaw)
          + (design.weight 3 • atomMatrix (Pᵀ *ᵥ design.atom 3)
            + (design.weight 4 • atomMatrix (Pᵀ *ᵥ design.atom 4)
              + design.weight 5 • atomMatrix (Pᵀ *ᵥ design.atom 5)))
          = Pᵀ * (atomMatrix hiddenRaw
              + (design.weight 3 • atomMatrix (design.atom 3)
                + (design.weight 4 • atomMatrix (design.atom 4)
                  + design.weight 5 • atomMatrix (design.atom 5)))) * P :=
              hleftConj.symm
      _ = Pᵀ * ((1 - design.weight 0) • atomMatrix (design.atom 0)
              + ((1 - design.weight 1) • atomMatrix (design.atom 1)
                + (1 - design.weight 2) • atomMatrix (design.atom 2))) * P := by
            rw [hdecomposition]
      _ = 1 := hbaseWhiten
  · exact planeBaseNormalizer_metric_eq_diagonal_sub_hidden design hlineFree hgap

/-- The transported identity metric in the axis normal form. -/
def planeAxisMetric (baseScale : Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (fun index => (baseScale index) ^ 2) - atomMatrix hidden

/-- A candidate gap in the axis normal form.  This is an explicit polynomial
matrix after unfolding `axisBaseAtom`, `planeAxisMetric`, and `atomMatrix`. -/
def planeAxisSubsetGap (baseScale : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ)
    (selected : Finset (Fin 6)) : Matrix (Fin 3) (Fin 3) ℝ :=
  (∑ label ∈ selected, atomMatrix (axisBaseAtom baseScale freeAtom label))
    - planeAxisMetric baseScale hidden

/-- The exact ten surviving plane-branch candidates in axis coordinates. -/
def AxisPlaneTenCandidate (baseScale : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ) : Prop :=
  (planeAxisSubsetGap baseScale freeAtom hidden {0, 3, 4}).PosDef
    ∨ (planeAxisSubsetGap baseScale freeAtom hidden {0, 3, 5}).PosDef
    ∨ (planeAxisSubsetGap baseScale freeAtom hidden {0, 4, 5}).PosDef
    ∨ (planeAxisSubsetGap baseScale freeAtom hidden {1, 3, 4}).PosDef
    ∨ (planeAxisSubsetGap baseScale freeAtom hidden {1, 3, 5}).PosDef
    ∨ (planeAxisSubsetGap baseScale freeAtom hidden {1, 4, 5}).PosDef
    ∨ (planeAxisSubsetGap baseScale freeAtom hidden {2, 3, 4}).PosDef
    ∨ (planeAxisSubsetGap baseScale freeAtom hidden {2, 3, 5}).PosDef
    ∨ (planeAxisSubsetGap baseScale freeAtom hidden {2, 4, 5}).PosDef
    ∨ (planeAxisSubsetGap baseScale freeAtom hidden {3, 4, 5}).PosDef

/-- Diagonal penalty from the two omitted base axes. -/
def planeAxisPenaltyExcept (baseScale : Fin 3 -> ℝ) (retainedBase : Fin 3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal fun coordinate =>
    if coordinate = retainedBase then 0 else (baseScale coordinate) ^ 2

/-- A distance-two candidate after cancelling the retained base axis against
the same diagonal entry of the transported metric. -/
def planeAxisDistanceTwoGap (baseScale : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ)
    (retainedBase freeOne freeTwo : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  atomMatrix hidden + atomMatrix (freeAtom freeOne) + atomMatrix (freeAtom freeTwo)
    - planeAxisPenaltyExcept baseScale retainedBase

/-- The full-complement candidate after the same metric cancellation. -/
def planeAxisComplementGap (baseScale : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  atomMatrix hidden + atomMatrix (freeAtom 0) + atomMatrix (freeAtom 1)
      + atomMatrix (freeAtom 2)
    - Matrix.diagonal (fun coordinate => (baseScale coordinate) ^ 2)

/-- The four-vector Parseval identity cancels the hidden atom out of the full
complement gap.  What remains is the complementary free weights against the
three diagonal base penalties. -/
theorem planeAxisComplementGap_eq_complementaryWeightedFree
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ) (freeWeight : Fin 3 -> ℝ)
    (hframe : atomMatrix hidden
        + (freeWeight 0 • atomMatrix (freeAtom 0)
          + freeWeight 1 • atomMatrix (freeAtom 1)
          + freeWeight 2 • atomMatrix (freeAtom 2)) = 1) :
    planeAxisComplementGap baseScale freeAtom hidden
      = (1 - freeWeight 0) • atomMatrix (freeAtom 0)
          + (1 - freeWeight 1) • atomMatrix (freeAtom 1)
          + (1 - freeWeight 2) • atomMatrix (freeAtom 2)
          - Matrix.diagonal (fun coordinate => (baseScale coordinate) ^ 2 - 1) := by
  ext row col
  have hentry := congrFun (congrFun hframe row) col
  by_cases heq : row = col
  · subst col
    simp only [Matrix.add_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, smul_eq_mul, Matrix.one_apply, if_pos] at hentry ⊢
    dsimp only [planeAxisComplementGap]
    simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix,
      Matrix.vecMulVec_apply, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul,
      if_pos]
    linarith
  · simp only [Matrix.add_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, smul_eq_mul, Matrix.one_apply, if_neg heq] at hentry ⊢
    dsimp only [planeAxisComplementGap]
    simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix,
      Matrix.vecMulVec_apply, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul,
      if_neg heq]
    linarith

/-- The ten normalized gaps are literally nine double-swap matrices plus the
full complement. -/
theorem axisPlaneTenCandidate_iff_explicit
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ) :
    AxisPlaneTenCandidate baseScale freeAtom hidden ↔
      (planeAxisDistanceTwoGap baseScale freeAtom hidden 0 0 1).PosDef
      ∨ (planeAxisDistanceTwoGap baseScale freeAtom hidden 0 0 2).PosDef
      ∨ (planeAxisDistanceTwoGap baseScale freeAtom hidden 0 1 2).PosDef
      ∨ (planeAxisDistanceTwoGap baseScale freeAtom hidden 1 0 1).PosDef
      ∨ (planeAxisDistanceTwoGap baseScale freeAtom hidden 1 0 2).PosDef
      ∨ (planeAxisDistanceTwoGap baseScale freeAtom hidden 1 1 2).PosDef
      ∨ (planeAxisDistanceTwoGap baseScale freeAtom hidden 2 0 1).PosDef
      ∨ (planeAxisDistanceTwoGap baseScale freeAtom hidden 2 0 2).PosDef
      ∨ (planeAxisDistanceTwoGap baseScale freeAtom hidden 2 1 2).PosDef
      ∨ (planeAxisComplementGap baseScale freeAtom hidden).PosDef := by
  unfold AxisPlaneTenCandidate
  have h034 : planeAxisSubsetGap baseScale freeAtom hidden {0, 3, 4}
      = planeAxisDistanceTwoGap baseScale freeAtom hidden 0 0 1 := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [planeAxisSubsetGap, planeAxisMetric, planeAxisDistanceTwoGap,
        planeAxisPenaltyExcept, axisBaseAtom, atomMatrix] <;> ring
  have h035 : planeAxisSubsetGap baseScale freeAtom hidden {0, 3, 5}
      = planeAxisDistanceTwoGap baseScale freeAtom hidden 0 0 2 := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [planeAxisSubsetGap, planeAxisMetric, planeAxisDistanceTwoGap,
        planeAxisPenaltyExcept, axisBaseAtom, atomMatrix] <;> ring
  have h045 : planeAxisSubsetGap baseScale freeAtom hidden {0, 4, 5}
      = planeAxisDistanceTwoGap baseScale freeAtom hidden 0 1 2 := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [planeAxisSubsetGap, planeAxisMetric, planeAxisDistanceTwoGap,
        planeAxisPenaltyExcept, axisBaseAtom, atomMatrix] <;> ring
  have h134 : planeAxisSubsetGap baseScale freeAtom hidden {1, 3, 4}
      = planeAxisDistanceTwoGap baseScale freeAtom hidden 1 0 1 := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [planeAxisSubsetGap, planeAxisMetric, planeAxisDistanceTwoGap,
        planeAxisPenaltyExcept, axisBaseAtom, atomMatrix] <;> ring
  have h135 : planeAxisSubsetGap baseScale freeAtom hidden {1, 3, 5}
      = planeAxisDistanceTwoGap baseScale freeAtom hidden 1 0 2 := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [planeAxisSubsetGap, planeAxisMetric, planeAxisDistanceTwoGap,
        planeAxisPenaltyExcept, axisBaseAtom, atomMatrix] <;> ring
  have h145 : planeAxisSubsetGap baseScale freeAtom hidden {1, 4, 5}
      = planeAxisDistanceTwoGap baseScale freeAtom hidden 1 1 2 := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [planeAxisSubsetGap, planeAxisMetric, planeAxisDistanceTwoGap,
        planeAxisPenaltyExcept, axisBaseAtom, atomMatrix] <;> ring
  have h234 : planeAxisSubsetGap baseScale freeAtom hidden {2, 3, 4}
      = planeAxisDistanceTwoGap baseScale freeAtom hidden 2 0 1 := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [planeAxisSubsetGap, planeAxisMetric, planeAxisDistanceTwoGap,
        planeAxisPenaltyExcept, axisBaseAtom, atomMatrix] <;> ring
  have h235 : planeAxisSubsetGap baseScale freeAtom hidden {2, 3, 5}
      = planeAxisDistanceTwoGap baseScale freeAtom hidden 2 0 2 := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [planeAxisSubsetGap, planeAxisMetric, planeAxisDistanceTwoGap,
        planeAxisPenaltyExcept, axisBaseAtom, atomMatrix] <;> ring
  have h245 : planeAxisSubsetGap baseScale freeAtom hidden {2, 4, 5}
      = planeAxisDistanceTwoGap baseScale freeAtom hidden 2 1 2 := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [planeAxisSubsetGap, planeAxisMetric, planeAxisDistanceTwoGap,
        planeAxisPenaltyExcept, axisBaseAtom, atomMatrix] <;> ring
  have h345 : planeAxisSubsetGap baseScale freeAtom hidden {3, 4, 5}
      = planeAxisComplementGap baseScale freeAtom hidden := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [planeAxisSubsetGap, planeAxisMetric, planeAxisComplementGap,
        axisBaseAtom, atomMatrix] <;> ring
  rw [h034, h035, h045, h134, h135, h145, h234, h235, h245, h345]

/-- Two distinct free atoms cannot both vanish in one coordinate when the
off-diagonal Veronese grid is nonsingular. -/
theorem not_both_freeAtom_coordinate_eq_zero_of_offDiagonalGrid_det_ne_zero
    (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hdet : (freeOffDiagonalGrid freeAtom).det ≠ 0)
    {freeOne freeTwo coordinate : Fin 3} (hne : freeOne ≠ freeTwo) :
    ¬ (freeAtom freeOne coordinate = 0 ∧ freeAtom freeTwo coordinate = 0) := by
  rintro ⟨hone, htwo⟩
  apply hdet
  fin_cases freeOne <;> fin_cases freeTwo <;> try { exact (hne rfl).elim }
  all_goals fin_cases coordinate
  all_goals simp at hone htwo
  all_goals simp [freeOffDiagonalGrid, Matrix.det_fin_three, hone, htwo]

/-- Hence the retained-axis corner of every distance-two candidate is
strictly positive.  One Sylvester sign disappears from each of the nine
candidate tests before any use of the Parseval identity. -/
theorem planeAxisDistanceTwoGap_retained_corner_pos
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ)
    (hdet : (freeOffDiagonalGrid freeAtom).det ≠ 0)
    {retainedBase freeOne freeTwo : Fin 3} (hne : freeOne ≠ freeTwo) :
    0 < planeAxisDistanceTwoGap baseScale freeAtom hidden
      retainedBase freeOne freeTwo retainedBase retainedBase := by
  have hnotBoth :=
    not_both_freeAtom_coordinate_eq_zero_of_offDiagonalGrid_det_ne_zero
      freeAtom hdet hne (coordinate := retainedBase)
  rw [planeAxisDistanceTwoGap]
  simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix,
    Matrix.vecMulVec_apply, planeAxisPenaltyExcept, Matrix.diagonal_apply,
    if_pos]
  by_cases hone : freeAtom freeOne retainedBase = 0
  · have htwo : freeAtom freeTwo retainedBase ≠ 0 := by
      intro hzero
      exact hnotBoth ⟨hone, hzero⟩
    nlinarith [sq_nonneg (hidden retainedBase),
      sq_nonneg (freeAtom freeOne retainedBase), sq_pos_of_ne_zero htwo]
  · nlinarith [sq_nonneg (hidden retainedBase), sq_pos_of_ne_zero hone,
      sq_nonneg (freeAtom freeTwo retainedBase)]

/-! ### Two-sign Sylvester tests for the nine distance-two candidates -/

/-- Positive definiteness is invariant under simultaneously reindexing rows and
columns by an equivalence.  Mathlib exposes the forward submatrix theorem; this
small equivalence is convenient for choosing any retained axis as the first
Sylvester coordinate. -/
theorem posDef_submatrix_equiv_real {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (form : Matrix n n ℝ) (reindex : m ≃ n) :
    (form.submatrix reindex reindex).PosDef ↔ form.PosDef := by
  constructor
  · intro hpos
    have hback := hpos.submatrix reindex.symm.injective
    have heq : (form.submatrix reindex reindex).submatrix reindex.symm reindex.symm
        = form := by
      ext row col
      simp [Matrix.submatrix_apply]
    rw [heq] at hback
    exact hback
  · intro hpos
    exact hpos.submatrix reindex.injective

/-- Sylvester's criterion after an arbitrary coordinate permutation. -/
theorem posDef_finThree_iff_reindexedLeadingMinors
    (form : Matrix (Fin 3) (Fin 3) ℝ) (hsymmetric : formᵀ = form)
    (reindex : Fin 3 ≃ Fin 3) :
    form.PosDef ↔
      (0 < form (reindex 0) (reindex 0)
        ∧ 0 < form (reindex 0) (reindex 0) * form (reindex 1) (reindex 1)
            - form (reindex 0) (reindex 1) ^ 2
        ∧ 0 < form (reindex 0) (reindex 0) * form (reindex 1) (reindex 1)
              * form (reindex 2) (reindex 2)
            - form (reindex 0) (reindex 0) * form (reindex 1) (reindex 2) ^ 2
            - form (reindex 0) (reindex 1) ^ 2 * form (reindex 2) (reindex 2)
            + 2 * form (reindex 0) (reindex 1) * form (reindex 0) (reindex 2)
                * form (reindex 1) (reindex 2)
            - form (reindex 0) (reindex 2) ^ 2 * form (reindex 1) (reindex 1)) := by
  have hsubSymmetric : (form.submatrix reindex reindex)ᵀ
      = form.submatrix reindex reindex := by
    ext row col
    have hentry := congrFun (congrFun hsymmetric (reindex col)) (reindex row)
    simpa only [Matrix.transpose_apply, Matrix.submatrix_apply] using hentry.symm
  rw [← posDef_submatrix_equiv_real form reindex]
  have hexplicit : form.submatrix reindex reindex =
      !![form (reindex 0) (reindex 0), form (reindex 0) (reindex 1),
          form (reindex 0) (reindex 2);
          form (reindex 0) (reindex 1), form (reindex 1) (reindex 1),
          form (reindex 1) (reindex 2);
          form (reindex 0) (reindex 2), form (reindex 1) (reindex 2),
          form (reindex 2) (reindex 2)] := by
    have hlower : ∀ row col : Fin 3,
        form (reindex col) (reindex row) = form (reindex row) (reindex col) := by
      intro row col
      have hentry := congrFun (congrFun hsymmetric (reindex row)) (reindex col)
      simpa only [Matrix.transpose_apply] using hentry
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [Matrix.submatrix_apply, hlower 0 1, hlower 0 2, hlower 1 2]
  rw [hexplicit, leadingMinors_pos_iff_posDef_fin_three]

/-- Once the first reindexed corner is known positive, a symmetric `3 x 3`
matrix is positive definite exactly when the remaining block minor and
determinant polynomial are positive. -/
theorem posDef_finThree_iff_two_reindexedMinors_of_corner_pos
    (form : Matrix (Fin 3) (Fin 3) ℝ) (hsymmetric : formᵀ = form)
    (reindex : Fin 3 ≃ Fin 3) (hcorner : 0 < form (reindex 0) (reindex 0)) :
    form.PosDef ↔
      (0 < form (reindex 0) (reindex 0) * form (reindex 1) (reindex 1)
          - form (reindex 0) (reindex 1) ^ 2
        ∧ 0 < form (reindex 0) (reindex 0) * form (reindex 1) (reindex 1)
              * form (reindex 2) (reindex 2)
            - form (reindex 0) (reindex 0) * form (reindex 1) (reindex 2) ^ 2
            - form (reindex 0) (reindex 1) ^ 2 * form (reindex 2) (reindex 2)
            + 2 * form (reindex 0) (reindex 1) * form (reindex 0) (reindex 2)
                * form (reindex 1) (reindex 2)
            - form (reindex 0) (reindex 2) ^ 2 * form (reindex 1) (reindex 1)) := by
  rw [posDef_finThree_iff_reindexedLeadingMinors form hsymmetric reindex,
    and_iff_right hcorner]

/-- Every distance-two gap is symmetric. -/
theorem planeAxisDistanceTwoGap_transpose
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ) (retainedBase freeOne freeTwo : Fin 3) :
    (planeAxisDistanceTwoGap baseScale freeAtom hidden
      retainedBase freeOne freeTwo)ᵀ
      = planeAxisDistanceTwoGap baseScale freeAtom hidden
          retainedBase freeOne freeTwo := by
  unfold planeAxisDistanceTwoGap planeAxisPenaltyExcept atomMatrix
  rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_add,
    Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec,
    Matrix.transpose_vecMulVec, diagonal_transpose]

/-- **THE NINE-CANDIDATE SYLVESTER REDUCTION.**  Choose any permutation whose
first coordinate is the retained base axis.  Off-conicity supplies its positive
corner, so the candidate is governed by exactly two explicit polynomial signs. -/
theorem planeAxisDistanceTwoGap_posDef_iff_two_reindexedMinors
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ)
    (hdet : (freeOffDiagonalGrid freeAtom).det ≠ 0)
    {retainedBase freeOne freeTwo : Fin 3} (hne : freeOne ≠ freeTwo)
    (reindex : Fin 3 ≃ Fin 3) (hreindex : reindex 0 = retainedBase) :
    let gap := planeAxisDistanceTwoGap baseScale freeAtom hidden
      retainedBase freeOne freeTwo
    gap.PosDef ↔
      (0 < gap (reindex 0) (reindex 0) * gap (reindex 1) (reindex 1)
          - gap (reindex 0) (reindex 1) ^ 2
        ∧ 0 < gap (reindex 0) (reindex 0) * gap (reindex 1) (reindex 1)
              * gap (reindex 2) (reindex 2)
            - gap (reindex 0) (reindex 0) * gap (reindex 1) (reindex 2) ^ 2
            - gap (reindex 0) (reindex 1) ^ 2 * gap (reindex 2) (reindex 2)
            + 2 * gap (reindex 0) (reindex 1) * gap (reindex 0) (reindex 2)
                * gap (reindex 1) (reindex 2)
            - gap (reindex 0) (reindex 2) ^ 2 * gap (reindex 1) (reindex 1)) := by
  dsimp only
  apply posDef_finThree_iff_two_reindexedMinors_of_corner_pos
  · exact planeAxisDistanceTwoGap_transpose baseScale freeAtom hidden
      retainedBase freeOne freeTwo
  · rw [hreindex]
    exact planeAxisDistanceTwoGap_retained_corner_pos baseScale freeAtom hidden hdet hne

/-- Canonical coordinate permutation putting `retainedBase` first. -/
def planeAxisFrontEquiv (retainedBase : Fin 3) : Fin 3 ≃ Fin 3 :=
  Equiv.swap 0 retainedBase

@[simp] theorem planeAxisFrontEquiv_zero (retainedBase : Fin 3) :
    planeAxisFrontEquiv retainedBase 0 = retainedBase := by
  simp [planeAxisFrontEquiv]

/-- The surviving two-by-two principal minor of a normalized double swap. -/
def planeAxisDistanceTwoBlockMinor
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ) (retainedBase freeOne freeTwo : Fin 3) : ℝ :=
  let gap := planeAxisDistanceTwoGap baseScale freeAtom hidden
    retainedBase freeOne freeTwo
  let order := planeAxisFrontEquiv retainedBase
  gap (order 0) (order 0) * gap (order 1) (order 1)
    - gap (order 0) (order 1) ^ 2

/-- The determinant polynomial of a normalized double swap, written in the
same retained-axis-first order as its block minor. -/
def planeAxisDistanceTwoDetCriterion
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ) (retainedBase freeOne freeTwo : Fin 3) : ℝ :=
  let gap := planeAxisDistanceTwoGap baseScale freeAtom hidden
    retainedBase freeOne freeTwo
  let order := planeAxisFrontEquiv retainedBase
  gap (order 0) (order 0) * gap (order 1) (order 1) * gap (order 2) (order 2)
    - gap (order 0) (order 0) * gap (order 1) (order 2) ^ 2
    - gap (order 0) (order 1) ^ 2 * gap (order 2) (order 2)
    + 2 * gap (order 0) (order 1) * gap (order 0) (order 2)
        * gap (order 1) (order 2)
    - gap (order 0) (order 2) ^ 2 * gap (order 1) (order 1)

/-- The named determinant criterion is exactly the matrix determinant. -/
theorem planeAxisDistanceTwoDetCriterion_eq_det
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ) (retainedBase freeOne freeTwo : Fin 3) :
    planeAxisDistanceTwoDetCriterion baseScale freeAtom hidden
        retainedBase freeOne freeTwo
      = (planeAxisDistanceTwoGap baseScale freeAtom hidden
          retainedBase freeOne freeTwo).det := by
  let gap := planeAxisDistanceTwoGap baseScale freeAtom hidden
    retainedBase freeOne freeTwo
  let order := planeAxisFrontEquiv retainedBase
  have hsym : gapᵀ = gap :=
    planeAxisDistanceTwoGap_transpose baseScale freeAtom hidden
      retainedBase freeOne freeTwo
  have hlower : ∀ row col : Fin 3, gap col row = gap row col := by
    intro row col
    have hentry := congrFun (congrFun hsym row) col
    simpa only [Matrix.transpose_apply] using hentry
  change gap (order 0) (order 0) * gap (order 1) (order 1) * gap (order 2) (order 2)
      - gap (order 0) (order 0) * gap (order 1) (order 2) ^ 2
      - gap (order 0) (order 1) ^ 2 * gap (order 2) (order 2)
      + 2 * gap (order 0) (order 1) * gap (order 0) (order 2)
          * gap (order 1) (order 2)
      - gap (order 0) (order 2) ^ 2 * gap (order 1) (order 1) = gap.det
  rw [← Matrix.det_submatrix_equiv_self order gap]
  rw [Matrix.det_fin_three]
  simp only [Matrix.submatrix_apply]
  rw [hlower (order 0) (order 1), hlower (order 0) (order 2),
    hlower (order 1) (order 2)]
  ring

/-- Off-conicity turns each normalized double-swap test into exactly the two
named polynomial inequalities. -/
theorem planeAxisDistanceTwoGap_posDef_iff_blockMinor_and_det
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ)
    (hdet : (freeOffDiagonalGrid freeAtom).det ≠ 0)
    {retainedBase freeOne freeTwo : Fin 3} (hne : freeOne ≠ freeTwo) :
    (planeAxisDistanceTwoGap baseScale freeAtom hidden
        retainedBase freeOne freeTwo).PosDef ↔
      (0 < planeAxisDistanceTwoBlockMinor baseScale freeAtom hidden
          retainedBase freeOne freeTwo
        ∧ 0 < planeAxisDistanceTwoDetCriterion baseScale freeAtom hidden
          retainedBase freeOne freeTwo) := by
  simpa only [planeAxisDistanceTwoBlockMinor, planeAxisDistanceTwoDetCriterion] using
    (planeAxisDistanceTwoGap_posDef_iff_two_reindexedMinors
      baseScale freeAtom hidden hdet hne (planeAxisFrontEquiv retainedBase)
      (planeAxisFrontEquiv_zero retainedBase))

/-- Finite polynomial form of the remaining plane-branch selector: one of the
nine unordered double swaps passes its two signs, or the full complement is
positive definite. -/
def AxisPlanePolynomialCandidate (baseScale : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ) : Prop :=
  (∃ retainedBase freeOne freeTwo : Fin 3, freeOne < freeTwo ∧
      0 < planeAxisDistanceTwoBlockMinor baseScale freeAtom hidden
        retainedBase freeOne freeTwo ∧
      0 < planeAxisDistanceTwoDetCriterion baseScale freeAtom hidden
        retainedBase freeOne freeTwo)
    ∨ (planeAxisComplementGap baseScale freeAtom hidden).PosDef

/-- The exact ten-candidate conclusion is the finite polynomial selector above.
This is the interface for a hand equality analysis or an exact SOS certificate. -/
theorem axisPlaneTenCandidate_iff_polynomial
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ)
    (hdet : (freeOffDiagonalGrid freeAtom).det ≠ 0) :
    AxisPlaneTenCandidate baseScale freeAtom hidden ↔
      AxisPlanePolynomialCandidate baseScale freeAtom hidden := by
  rw [axisPlaneTenCandidate_iff_explicit]
  unfold AxisPlanePolynomialCandidate
  simp_rw [planeAxisDistanceTwoGap_posDef_iff_blockMinor_and_det
    baseScale freeAtom hidden hdet (by decide : (0 : Fin 3) ≠ 1)]
  simp_rw [planeAxisDistanceTwoGap_posDef_iff_blockMinor_and_det
    baseScale freeAtom hidden hdet (by decide : (0 : Fin 3) ≠ 2)]
  simp_rw [planeAxisDistanceTwoGap_posDef_iff_blockMinor_and_det
    baseScale freeAtom hidden hdet (by decide : (1 : Fin 3) ≠ 2)]
  constructor
  · rintro (h | h | h | h | h | h | h | h | h | h)
    · exact Or.inl ⟨0, 0, 1, by decide, h⟩
    · exact Or.inl ⟨0, 0, 2, by decide, h⟩
    · exact Or.inl ⟨0, 1, 2, by decide, h⟩
    · exact Or.inl ⟨1, 0, 1, by decide, h⟩
    · exact Or.inl ⟨1, 0, 2, by decide, h⟩
    · exact Or.inl ⟨1, 1, 2, by decide, h⟩
    · exact Or.inl ⟨2, 0, 1, by decide, h⟩
    · exact Or.inl ⟨2, 0, 2, by decide, h⟩
    · exact Or.inl ⟨2, 1, 2, by decide, h⟩
    · exact Or.inr h
  · rintro (⟨retainedBase, freeOne, freeTwo, hlt, h⟩ | h)
    · fin_cases retainedBase <;> fin_cases freeOne <;> fin_cases freeTwo <;>
        norm_num at hlt <;> aesop
    · aesop

/-- Fixed-axis first corner of the full-complement gap. -/
def planeAxisComplementCorner (baseScale : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ) : ℝ :=
  planeAxisComplementGap baseScale freeAtom hidden 0 0

/-- Fixed-axis leading two-by-two minor of the full-complement gap. -/
def planeAxisComplementBlockMinor (baseScale : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ) : ℝ :=
  let gap := planeAxisComplementGap baseScale freeAtom hidden
  gap 0 0 * gap 1 1 - gap 0 1 ^ 2

/-- Determinant sign used by the full-complement test. -/
def planeAxisComplementDetCriterion (baseScale : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ) : ℝ :=
  (planeAxisComplementGap baseScale freeAtom hidden).det

theorem planeAxisComplementGap_transpose
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ) :
    (planeAxisComplementGap baseScale freeAtom hidden)ᵀ
      = planeAxisComplementGap baseScale freeAtom hidden := by
  unfold planeAxisComplementGap atomMatrix
  rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_add,
    Matrix.transpose_add, Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec,
    Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec, diagonal_transpose]

/-- The complement is governed by three explicit polynomial signs. -/
theorem planeAxisComplementGap_posDef_iff_three_signs
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ) :
    (planeAxisComplementGap baseScale freeAtom hidden).PosDef ↔
      (0 < planeAxisComplementCorner baseScale freeAtom hidden
        ∧ 0 < planeAxisComplementBlockMinor baseScale freeAtom hidden
        ∧ 0 < planeAxisComplementDetCriterion baseScale freeAtom hidden) := by
  let gap := planeAxisComplementGap baseScale freeAtom hidden
  have hsym : gapᵀ = gap := planeAxisComplementGap_transpose baseScale freeAtom hidden
  have hlead := posDef_finThree_iff_reindexedLeadingMinors gap hsym (Equiv.refl (Fin 3))
  have hlower : ∀ row col : Fin 3, gap col row = gap row col := by
    intro row col
    have hentry := congrFun (congrFun hsym row) col
    simpa only [Matrix.transpose_apply] using hentry
  have hdet : gap 0 0 * gap 1 1 * gap 2 2 - gap 0 0 * gap 1 2 ^ 2
          - gap 0 1 ^ 2 * gap 2 2 + 2 * gap 0 1 * gap 0 2 * gap 1 2
          - gap 0 2 ^ 2 * gap 1 1 = gap.det := by
    rw [Matrix.det_fin_three, hlower 0 1, hlower 0 2, hlower 1 2]
    ring
  simpa only [Equiv.refl_apply, planeAxisComplementCorner,
    planeAxisComplementBlockMinor, planeAxisComplementDetCriterion, gap, hdet] using hlead

/-- Exact closed obstruction presented by a hypothetical failure of all ten
plane-branch candidates.  Every unordered double swap must fail either its
surviving block minor or its determinant, and the full complement must fail. -/
def AxisPlanePolynomialFailure (baseScale : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ) : Prop :=
  (∀ retainedBase freeOne freeTwo : Fin 3, freeOne < freeTwo →
      planeAxisDistanceTwoBlockMinor baseScale freeAtom hidden
          retainedBase freeOne freeTwo ≤ 0
        ∨ planeAxisDistanceTwoDetCriterion baseScale freeAtom hidden
          retainedBase freeOne freeTwo ≤ 0)
    ∧ (planeAxisComplementCorner baseScale freeAtom hidden ≤ 0
      ∨ planeAxisComplementBlockMinor baseScale freeAtom hidden ≤ 0
      ∨ planeAxisComplementDetCriterion baseScale freeAtom hidden ≤ 0)

/-- Negating the ten-candidate selector has no hidden quantifiers left beyond a
finite `Fin 3` census. -/
theorem not_axisPlaneTenCandidate_iff_polynomialFailure
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ)
    (hdet : (freeOffDiagonalGrid freeAtom).det ≠ 0) :
    ¬ AxisPlaneTenCandidate baseScale freeAtom hidden ↔
      AxisPlanePolynomialFailure baseScale freeAtom hidden := by
  rw [axisPlaneTenCandidate_iff_polynomial baseScale freeAtom hidden hdet]
  unfold AxisPlanePolynomialCandidate AxisPlanePolynomialFailure
  rw [planeAxisComplementGap_posDef_iff_three_signs]
  constructor
  · intro hfail
    have hparts :
        ¬ (∃ retainedBase freeOne freeTwo : Fin 3, freeOne < freeTwo ∧
            0 < planeAxisDistanceTwoBlockMinor baseScale freeAtom hidden
              retainedBase freeOne freeTwo ∧
            0 < planeAxisDistanceTwoDetCriterion baseScale freeAtom hidden
              retainedBase freeOne freeTwo)
          ∧ ¬ (0 < planeAxisComplementCorner baseScale freeAtom hidden
            ∧ 0 < planeAxisComplementBlockMinor baseScale freeAtom hidden
            ∧ 0 < planeAxisComplementDetCriterion baseScale freeAtom hidden) :=
      not_or.mp hfail
    refine ⟨?_, ?_⟩
    intro retainedBase freeOne freeTwo hlt
    by_contra hboth
    push Not at hboth
    exact hparts.1 ⟨retainedBase, freeOne, freeTwo, hlt, hboth.1, hboth.2⟩
    by_cases hcorner : planeAxisComplementCorner baseScale freeAtom hidden ≤ 0
    · exact Or.inl hcorner
    by_cases hblock : planeAxisComplementBlockMinor baseScale freeAtom hidden ≤ 0
    · exact Or.inr (Or.inl hblock)
    by_cases hdetFailure : planeAxisComplementDetCriterion baseScale freeAtom hidden ≤ 0
    · exact Or.inr (Or.inr hdetFailure)
    exact False.elim (hparts.2 ⟨lt_of_not_ge hcorner,
      lt_of_not_ge hblock, lt_of_not_ge hdetFailure⟩)
  · rintro ⟨hswaps, hcomplement⟩
    apply not_or.mpr
    refine ⟨?_, ?_⟩
    rintro ⟨retainedBase, freeOne, freeTwo, hlt, hblock, hdetCriterion⟩
    rcases hswaps retainedBase freeOne freeTwo hlt with hblockFail | hdetFail
    · linarith
    · linarith
    rintro ⟨hcorner, hblock, hdetPositive⟩
    rcases hcomplement with hcornerFail | hblockFail | hdetFail
    · linarith
    · linarith
    · linarith

/-- Every original subset test is exactly its axis-normal-form test. -/
theorem posDef_gap_iff_planeAxisSubsetGap
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hidden : Fin 3 -> ℝ)
    (hmetric : (planeBaseNormalizer design)ᵀ * planeBaseNormalizer design
      = planeAxisMetric (planeBaseScale design) hidden)
    (selected : Finset (Fin 6)) :
    (subsetSum design selected - 1).PosDef ↔
      (planeAxisSubsetGap (planeBaseScale design)
        (planeNormalizedFreeAtom design) hidden selected).PosDef := by
  have hiff := posDef_congrAtom_sub_metric_iff design
    (planeBaseNormalizer design)
    (planeBaseNormalizer_det_isUnit design hlineFree) selected
  have hatom : ∀ label,
      (planeBaseNormalizer design)ᵀ *ᵥ design.atom label
        = axisBaseAtom (planeBaseScale design)
            (planeNormalizedFreeAtom design) label :=
    congrFun (planeBaseNormalizer_atom_eq_axisBaseAtom design hlineFree)
  simp_rw [hatom] at hiff
  rw [hmetric] at hiff
  unfold planeAxisSubsetGap
  exact hiff.symm

/-- The finite plane-branch frontier is unchanged by normalization. -/
theorem planeBranchTenCandidate_iff_axisPlaneTenCandidate
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hidden : Fin 3 -> ℝ)
    (hmetric : (planeBaseNormalizer design)ᵀ * planeBaseNormalizer design
      = planeAxisMetric (planeBaseScale design) hidden) :
    PlaneBranchTenCandidate design ↔
      AxisPlaneTenCandidate (planeBaseScale design)
        (planeNormalizedFreeAtom design) hidden := by
  unfold PlaneBranchTenCandidate AxisPlaneTenCandidate
  simp only [posDef_gap_iff_planeAxisSubsetGap design hlineFree hidden hmetric]

/-- The fully explicit algebraic target attached to a plane-branch design. -/
def PlaneBranchAxisSelector (design : WeightedDesign 6 3) : Prop :=
  ∃ hidden : Fin 3 -> ℝ,
    atomMatrix hidden
        + (design.weight 3 • atomMatrix (planeNormalizedFreeAtom design 0)
          + design.weight 4 • atomMatrix (planeNormalizedFreeAtom design 1)
          + design.weight 5 • atomMatrix (planeNormalizedFreeAtom design 2)) = 1
    ∧ (planeBaseNormalizer design)ᵀ * planeBaseNormalizer design
        = planeAxisMetric (planeBaseScale design) hidden
    ∧ (freeOffDiagonalGrid (planeNormalizedFreeAtom design)).det ≠ 0
    ∧ AxisPlaneTenCandidate (planeBaseScale design)
        (planeNormalizedFreeAtom design) hidden

/-- **Exact polynomial frontier for the plane branch.**  Under precisely the
skeleton hypotheses, the original ten-candidate conclusion is equivalent to
the axis selector: the three displayed matrix identities, one nonzero 3x3
determinant, and one explicit ten-way PosDef disjunction. -/
theorem planeBranchTenCandidate_iff_axisSelector
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    PlaneBranchTenCandidate design ↔ PlaneBranchAxisSelector design := by
  constructor
  · intro hcandidates
    obtain ⟨hidden, hparseval, hmetricRaw, hdet, _⟩ :=
      exists_planeBranch_axisNormalForm design hlineFree hoffConic hdominates hfree
    have hmetric : (planeBaseNormalizer design)ᵀ * planeBaseNormalizer design
        = planeAxisMetric (planeBaseScale design) hidden := by
      exact hmetricRaw
    exact ⟨hidden, hparseval, hmetric, hdet,
      (planeBranchTenCandidate_iff_axisPlaneTenCandidate design hlineFree hidden
        hmetric).mp hcandidates⟩
  · rintro ⟨hidden, _hparseval, hmetric, _hdet, hcandidates⟩
    exact (planeBranchTenCandidate_iff_axisPlaneTenCandidate design hlineFree hidden
      hmetric).mpr hcandidates

/-- The final contradiction target, with all geometric transport erased. -/
def PlaneBranchAxisFailureWitness (design : WeightedDesign 6 3) : Prop :=
  ∃ hidden : Fin 3 -> ℝ,
    atomMatrix hidden
        + (design.weight 3 • atomMatrix (planeNormalizedFreeAtom design 0)
          + design.weight 4 • atomMatrix (planeNormalizedFreeAtom design 1)
          + design.weight 5 • atomMatrix (planeNormalizedFreeAtom design 2)) = 1
    ∧ (planeBaseNormalizer design)ᵀ * planeBaseNormalizer design
        = planeAxisMetric (planeBaseScale design) hidden
    ∧ (freeOffDiagonalGrid (planeNormalizedFreeAtom design)).det ≠ 0
    ∧ (planeNormalizedFreeFrame design).det ≠ 0
    ∧ AxisPlanePolynomialFailure (planeBaseScale design)
        (planeNormalizedFreeAtom design) hidden

/-- **EXACT NORMAL-FORM OBSTRUCTION FOR THE PLANE BRANCH.**  Under the original
Skeleton hypotheses, failure of all ten surviving triples is equivalent to one
finite algebraic witness.  The only remaining non-polynomial leaf is the
full-complement `PosDef` refusal, whose hidden atom cancels by
`planeAxisComplementGap_eq_complementaryWeightedFree`. -/
theorem not_planeBranchTenCandidate_iff_axisFailureWitness
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ¬ PlaneBranchTenCandidate design ↔ PlaneBranchAxisFailureWitness design := by
  constructor
  · intro hfailure
    obtain ⟨hidden, hparseval, hmetricRaw, hdet, _⟩ :=
      exists_planeBranch_axisNormalForm design hlineFree hoffConic hdominates hfree
    have hmetric : (planeBaseNormalizer design)ᵀ * planeBaseNormalizer design
        = planeAxisMetric (planeBaseScale design) hidden := hmetricRaw
    have haxisFailure : ¬ AxisPlaneTenCandidate (planeBaseScale design)
        (planeNormalizedFreeAtom design) hidden := by
      exact fun haxis => hfailure
        ((planeBranchTenCandidate_iff_axisPlaneTenCandidate design hlineFree hidden
          hmetric).mpr haxis)
    exact ⟨hidden, hparseval, hmetric, hdet,
      planeNormalizedFreeFrame_det_ne_zero design hlineFree,
      (not_axisPlaneTenCandidate_iff_polynomialFailure
        (planeBaseScale design) (planeNormalizedFreeAtom design) hidden hdet).mp
          haxisFailure⟩
  · rintro ⟨hidden, _hparseval, hmetric, hdet, _hfreeFrame, hfailure⟩
    have haxisFailure : ¬ AxisPlaneTenCandidate (planeBaseScale design)
        (planeNormalizedFreeAtom design) hidden :=
      (not_axisPlaneTenCandidate_iff_polynomialFailure
        (planeBaseScale design) (planeNormalizedFreeAtom design) hidden hdet).mpr
          hfailure
    exact fun hcandidates => haxisFailure
      ((planeBranchTenCandidate_iff_axisPlaneTenCandidate design hlineFree hidden
        hmetric).mp hcandidates)

end Gtz
