import Gtz.Design.PlaneBranchUnitAxisNormalForm
import Gtz.Reduction.DiagonalRungs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz

open Matrix

/-! ## The four-window bridge in unit-axis coordinates

In the plane branch the transformed base atoms are the three coordinate axes.
The Parseval identity has the form

`hh^T + sum_l u_l f_l f_l^T = diag (1 - b_i)`.

The complement gap is

`C = sum_l (1-u_l) f_l f_l^T - diag b`.

This file proves that one of the four-vector windows `C + e_i e_i^T` is
positive definite.  It is the exact first stage suggested by the rank-one
census; no numerical hypothesis appears below.
-/

def unitAxisFreeWeightedFrame (freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  freeWeight 0 • atomMatrix (freeAtom 0)
    + freeWeight 1 • atomMatrix (freeAtom 1)
    + freeWeight 2 • atomMatrix (freeAtom 2)

def unitAxisCofreeFrame (freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 - freeWeight 0) • atomMatrix (freeAtom 0)
    + (1 - freeWeight 1) • atomMatrix (freeAtom 1)
    + (1 - freeWeight 2) • atomMatrix (freeAtom 2)

def unitAxisWeightedComplementGap (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  unitAxisCofreeFrame freeWeight freeAtom - Matrix.diagonal baseWeight

def unitAxisFourWindowGap (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (retained : Fin 3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  unitAxisWeightedComplementGap baseWeight freeWeight freeAtom
    + atomMatrix (Pi.single retained 1)

def unitAxisBaseMass (baseWeight : Fin 3 -> ℝ) : ℝ :=
  baseWeight 0 + baseWeight 1 + baseWeight 2

noncomputable def unitAxisBaseWeight (design : WeightedDesign 6 3) : Fin 3 -> ℝ :=
  fun baseIndex => design.weight (baseThreeLabel baseIndex)

noncomputable def unitAxisFreeWeight (design : WeightedDesign 6 3) : Fin 3 -> ℝ :=
  fun freeIndex => design.weight (freeThreeLabel freeIndex)

def freeAtomRowFrame (freeAtom : Fin 3 -> Fin 3 -> ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![freeAtom 0, freeAtom 1, freeAtom 2]

noncomputable def unitAxisHiddenMass (baseWeight : Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ) : ℝ :=
  hidden 0 ^ 2 / (1 - baseWeight 0)
    + hidden 1 ^ 2 / (1 - baseWeight 1)
    + hidden 2 ^ 2 / (1 - baseWeight 2)

noncomputable def unitAxisWindowRankOneMass (baseWeight : Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ) (retained : Fin 3) : ℝ :=
  let b := unitAxisBaseMass baseWeight
  ∑ coordinate : Fin 3,
    if coordinate = retained then
      b * hidden coordinate ^ 2 / (1 - baseWeight coordinate)
    else
      b * hidden coordinate ^ 2 / (b - baseWeight coordinate)

def unitAxisWindowDiagonal (baseWeight : Fin 3 -> ℝ)
    (retained : Fin 3) : Fin 3 -> ℝ :=
  let b := unitAxisBaseMass baseWeight
  fun coordinate =>
    if coordinate = retained then 1 - baseWeight coordinate
    else b - baseWeight coordinate

noncomputable def unitAxisWindowLowerGap (baseWeight : Fin 3 -> ℝ)
    (hidden : Fin 3 -> ℝ) (retained : Fin 3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  let b := unitAxisBaseMass baseWeight
  (1 / (1 - b)) •
    (Matrix.diagonal (unitAxisWindowDiagonal baseWeight retained)
      - b • atomMatrix hidden)

noncomputable def unitAxisWindowSlackWeight (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeIndex : Fin 3) : ℝ :=
  let b := unitAxisBaseMass baseWeight
  (1 - b - freeWeight freeIndex) / (1 - b)

noncomputable def unitAxisWindowSlackFrame (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  unitAxisFreeWeightedFrame (unitAxisWindowSlackWeight baseWeight freeWeight)
    freeAtom

noncomputable def planeBranchFourWindow (retained : Fin 3) : Finset (Fin 6) :=
  insert (baseThreeLabel retained) ({3, 4, 5} : Finset (Fin 6))

theorem unitAxisFreeWeightedFrame_transpose
    (freeWeight : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ) :
    (unitAxisFreeWeightedFrame freeWeight freeAtom)ᵀ
      = unitAxisFreeWeightedFrame freeWeight freeAtom := by
  unfold unitAxisFreeWeightedFrame atomMatrix
  rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_vecMulVec,
    Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec]

theorem unitAxisCofreeFrame_transpose
    (freeWeight : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ) :
    (unitAxisCofreeFrame freeWeight freeAtom)ᵀ
      = unitAxisCofreeFrame freeWeight freeAtom := by
  unfold unitAxisCofreeFrame atomMatrix
  rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_vecMulVec,
    Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec]

theorem unitAxisWeightedComplementGap_transpose
    (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) :
    (unitAxisWeightedComplementGap baseWeight freeWeight freeAtom)ᵀ
      = unitAxisWeightedComplementGap baseWeight freeWeight freeAtom := by
  unfold unitAxisWeightedComplementGap
  rw [Matrix.transpose_sub, unitAxisCofreeFrame_transpose,
    Matrix.diagonal_transpose]

theorem unitAxisFourWindowGap_transpose
    (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (retained : Fin 3) :
    (unitAxisFourWindowGap baseWeight freeWeight freeAtom retained)ᵀ
      = unitAxisFourWindowGap baseWeight freeWeight freeAtom retained := by
  unfold unitAxisFourWindowGap atomMatrix
  rw [Matrix.transpose_add, unitAxisWeightedComplementGap_transpose,
    Matrix.transpose_vecMulVec]

/-- The weighted free frame is a diagonal congruence by the row frame. -/
theorem unitAxisFreeWeightedFrame_eq_congruence
    (freeWeight : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ) :
    unitAxisFreeWeightedFrame freeWeight freeAtom
      = (freeAtomRowFrame freeAtom)ᵀ * Matrix.diagonal freeWeight
          * freeAtomRowFrame freeAtom := by
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [unitAxisFreeWeightedFrame, freeAtomRowFrame, atomMatrix,
      Matrix.vecMulVec_apply, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- Positive weights and an invertible free frame make the weighted free
moment positive definite. -/
theorem unitAxisFreeWeightedFrame_posDef
    (freeWeight : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hweight : ∀ index, 0 < freeWeight index)
    (hdet : (freeAtomRowFrame freeAtom).det ≠ 0) :
    (unitAxisFreeWeightedFrame freeWeight freeAtom).PosDef := by
  rw [unitAxisFreeWeightedFrame_eq_congruence]
  exact (posDef_congr_right (Matrix.diagonal_transpose freeWeight)
    (isUnit_iff_ne_zero.mpr hdet)).mp (Matrix.PosDef.diagonal hweight)

/-- The concrete free-frame definition used by the design normal form is the
generic row frame above. -/
theorem freeAtomRowFrame_unitAxisFreeAtom
    (design : WeightedDesign 6 3) :
    freeAtomRowFrame (unitAxisFreeAtom design) = unitAxisFreeFrame design := by
  rfl

/-- The hidden rank-one atom has strictly less than unit mass in the diagonal
metric.  This is the determinant-lemma inequality
`hᵀ diag(1-b)^{-1} h < 1`, proved from positivity of the weighted free
frame so that no inverse matrix is introduced. -/
theorem unitAxisHiddenMass_lt_one
    (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ)
    (hbaseLt : ∀ index, baseWeight index < 1)
    (hfreePos : ∀ index, 0 < freeWeight index)
    (hframe : atomMatrix hidden
        + unitAxisFreeWeightedFrame freeWeight freeAtom
          = Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate))
    (hdet : (freeAtomRowFrame freeAtom).det ≠ 0) :
    unitAxisHiddenMass baseWeight hidden < 1 := by
  let freeFrame := unitAxisFreeWeightedFrame freeWeight freeAtom
  have hfreeFramePos : freeFrame.PosDef :=
    unitAxisFreeWeightedFrame_posDef freeWeight freeAtom hfreePos hdet
  have hfreeFrameEq : freeFrame
      = Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate)
          - atomMatrix hidden := by
    calc
      freeFrame = (atomMatrix hidden + freeFrame) - atomMatrix hidden := by abel
      _ = Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate)
            - atomMatrix hidden := by rw [hframe]
  by_cases hhidden : hidden = 0
  · subst hidden
    simp [unitAxisHiddenMass]
  · let probe : Fin 3 -> ℝ := ![
      hidden 0 / (1 - baseWeight 0),
      hidden 1 / (1 - baseWeight 1),
      hidden 2 / (1 - baseWeight 2)]
    have hdenZero : ∀ index : Fin 3, 1 - baseWeight index ≠ 0 := by
      intro index
      exact ne_of_gt (sub_pos.mpr (hbaseLt index))
    have hprobeNe : probe ≠ 0 := by
      intro hprobe
      apply hhidden
      funext coordinate
      fin_cases coordinate
      · have hentry := congrFun hprobe 0
        simp only [probe, Matrix.cons_val_zero] at hentry
        exact (div_eq_zero_iff.mp hentry).resolve_right (hdenZero 0)
      · have hentry := congrFun hprobe 1
        simp only [probe, Matrix.cons_val_one] at hentry
        exact (div_eq_zero_iff.mp hentry).resolve_right (hdenZero 1)
      · have hentry := congrFun hprobe 2
        simp only [probe, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons] at hentry
        exact (div_eq_zero_iff.mp hentry).resolve_right (hdenZero 2)
    have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hfreeFramePos).2 hprobeNe
    rw [star_trivial, hfreeFrameEq] at hform
    have hformIdentity :
        probe ⬝ᵥ ((Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate)
              - atomMatrix hidden) *ᵥ probe)
          = unitAxisHiddenMass baseWeight hidden
              - unitAxisHiddenMass baseWeight hidden ^ 2 := by
      rw [Matrix.sub_mulVec, dotProduct_sub, atom_form_eq_sq]
      simp only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three,
        probe, unitAxisHiddenMass,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      field_simp [hdenZero 0, hdenZero 1, hdenZero 2]
    rw [hformIdentity] at hform
    nlinarith [sq_nonneg (unitAxisHiddenMass baseWeight hidden)]

/-- The three retained-axis rank-one masses average to the hidden mass, with
weights `b_i / (b_0+b_1+b_2)`. -/
theorem unitAxisWindowRankOneMass_weighted_average
    (baseWeight : Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ)
    (hbasePos : ∀ index, 0 < baseWeight index)
    (hbaseLt : ∀ index, baseWeight index < 1) :
    let b := unitAxisBaseMass baseWeight
    (baseWeight 0 / b) * unitAxisWindowRankOneMass baseWeight hidden 0
      + (baseWeight 1 / b) * unitAxisWindowRankOneMass baseWeight hidden 1
      + (baseWeight 2 / b) * unitAxisWindowRankOneMass baseWeight hidden 2
        = unitAxisHiddenMass baseWeight hidden := by
  dsimp only
  have hb : 0 < unitAxisBaseMass baseWeight := by
    unfold unitAxisBaseMass
    nlinarith [hbasePos 0, hbasePos 1, hbasePos 2]
  have hb0 : unitAxisBaseMass baseWeight - baseWeight 0 ≠ 0 := by
    unfold unitAxisBaseMass
    nlinarith [hbasePos 1, hbasePos 2]
  have hb1 : unitAxisBaseMass baseWeight - baseWeight 1 ≠ 0 := by
    unfold unitAxisBaseMass
    nlinarith [hbasePos 0, hbasePos 2]
  have hb2 : unitAxisBaseMass baseWeight - baseWeight 2 ≠ 0 := by
    unfold unitAxisBaseMass
    nlinarith [hbasePos 0, hbasePos 1]
  have hd0 : 1 - baseWeight 0 ≠ 0 := ne_of_gt (sub_pos.mpr (hbaseLt 0))
  have hd1 : 1 - baseWeight 1 ≠ 0 := ne_of_gt (sub_pos.mpr (hbaseLt 1))
  have hd2 : 1 - baseWeight 2 ≠ 0 := ne_of_gt (sub_pos.mpr (hbaseLt 2))
  simp only [unitAxisWindowRankOneMass, Fin.sum_univ_three,
    unitAxisHiddenMass, if_true,
    if_neg (by decide : (0 : Fin 3) ≠ 1),
    if_neg (by decide : (0 : Fin 3) ≠ 2),
    if_neg (by decide : (1 : Fin 3) ≠ 0),
    if_neg (by decide : (1 : Fin 3) ≠ 2),
    if_neg (by decide : (2 : Fin 3) ≠ 0),
    if_neg (by decide : (2 : Fin 3) ≠ 1)]
  unfold unitAxisBaseMass at hb hb0 hb1 hb2 ⊢
  field_simp [hb.ne', hb0, hb1, hb2, hd0, hd1, hd2]
  ring

/-- Consequently one retained axis has rank-one comparison mass below one.
This is the exact three-way weighted pigeonhole behind the four-window
selector. -/
theorem exists_unitAxisWindowRankOneMass_lt_one
    (baseWeight : Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ)
    (hbasePos : ∀ index, 0 < baseWeight index)
    (hbaseLt : ∀ index, baseWeight index < 1)
    (hhidden : unitAxisHiddenMass baseWeight hidden < 1) :
    ∃ retained : Fin 3,
      unitAxisWindowRankOneMass baseWeight hidden retained < 1 := by
  let b := unitAxisBaseMass baseWeight
  have hb : 0 < b := by
    dsimp [b, unitAxisBaseMass]
    nlinarith [hbasePos 0, hbasePos 1, hbasePos 2]
  have havg := unitAxisWindowRankOneMass_weighted_average
    baseWeight hidden hbasePos hbaseLt
  dsimp only at havg
  by_contra hnone
  push Not at hnone
  have hzero := hnone 0
  have hone := hnone 1
  have htwo := hnone 2
  have hwzero : baseWeight 0 / b ≤
      (baseWeight 0 / b) * unitAxisWindowRankOneMass baseWeight hidden 0 := by
    have hcoeff : 0 ≤ baseWeight 0 / b :=
      div_nonneg (hbasePos 0).le hb.le
    nlinarith
  have hwone : baseWeight 1 / b ≤
      (baseWeight 1 / b) * unitAxisWindowRankOneMass baseWeight hidden 1 := by
    have hcoeff : 0 ≤ baseWeight 1 / b :=
      div_nonneg (hbasePos 1).le hb.le
    nlinarith
  have hwtwo : baseWeight 2 / b ≤
      (baseWeight 2 / b) * unitAxisWindowRankOneMass baseWeight hidden 2 := by
    have hcoeff : 0 ≤ baseWeight 2 / b :=
      div_nonneg (hbasePos 2).le hb.le
    nlinarith
  have hcoeffSum : baseWeight 0 / b + baseWeight 1 / b
      + baseWeight 2 / b = 1 := by
    calc
      baseWeight 0 / b + baseWeight 1 / b + baseWeight 2 / b
          = (baseWeight 0 + baseWeight 1 + baseWeight 2) / b := by ring
      _ = b / b := by rfl
      _ = 1 := div_self hb.ne'
  nlinarith

/-- Strict companion to `posSemidef_diagonal_sub_of_sum_diag_div_le_one`.
Normalized trace strictly below one gives a positive definite diagonal gap. -/
theorem posDef_diagonal_sub_of_sum_diag_div_lt_one
    {size : ℕ} {residual : Matrix (Fin size) (Fin size) ℝ}
    (hpsd : residual.PosSemidef)
    {positiveDiagonal : Fin size -> ℝ}
    (hpos : ∀ index, 0 < positiveDiagonal index)
    (hmass : ∑ index, residual index index / positiveDiagonal index < 1) :
    (Matrix.diagonal positiveDiagonal - residual).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hprobe => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_sub, Matrix.diagonal_transpose,
      transpose_eq_of_isHermitian hpsd.isHermitian]
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    set weightedSquares : ℝ := ∑ index, positiveDiagonal index * probe index ^ 2
      with hweightedSquares
    have hdiagonalForm :
        probe ⬝ᵥ (Matrix.diagonal positiveDiagonal *ᵥ probe) = weightedSquares := by
      rw [hweightedSquares]
      simp only [dotProduct, Matrix.mulVec_diagonal]
      exact Finset.sum_congr rfl fun index _ => by ring
    have hweightedPos : 0 < weightedSquares := by
      have hstrict := (Matrix.posDef_iff_dotProduct_mulVec.mp
        (Matrix.PosDef.diagonal hpos)).2 hprobe
      rwa [star_trivial, hdiagonalForm] at hstrict
    have hmassNonneg : 0 ≤ ∑ index, residual index index / positiveDiagonal index :=
      Finset.sum_nonneg fun index _ =>
        div_nonneg hpsd.diag_nonneg (hpos index).le
    have hcauchy :
        (∑ index, Real.sqrt (residual index index) * |probe index|) ^ 2
          ≤ (∑ index, residual index index / positiveDiagonal index)
              * weightedSquares := by
      have hsplit :
          (∑ index, Real.sqrt (residual index index) * |probe index|)
            = ∑ index,
                (Real.sqrt (residual index index) /
                    Real.sqrt (positiveDiagonal index))
                  * (Real.sqrt (positiveDiagonal index) * |probe index|) := by
        refine Finset.sum_congr rfl fun index _ => ?_
        have hsqrtNe : Real.sqrt (positiveDiagonal index) ≠ 0 :=
          (Real.sqrt_pos.mpr (hpos index)).ne'
        field_simp
      have hbase := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun index => Real.sqrt (residual index index) /
          Real.sqrt (positiveDiagonal index))
        (fun index => Real.sqrt (positiveDiagonal index) * |probe index|)
      have hleft :
          (∑ index, (Real.sqrt (residual index index) /
              Real.sqrt (positiveDiagonal index)) ^ 2)
            = ∑ index, residual index index / positiveDiagonal index :=
        Finset.sum_congr rfl fun index _ => by
          rw [div_pow, Real.sq_sqrt hpsd.diag_nonneg,
            Real.sq_sqrt (hpos index).le]
      have hright :
          (∑ index, (Real.sqrt (positiveDiagonal index)
              * |probe index|) ^ 2) = weightedSquares :=
        Finset.sum_congr rfl fun index _ => by
          rw [mul_pow, Real.sq_sqrt (hpos index).le, sq_abs]
      rw [hsplit, ← hleft, ← hright]
      exact hbase
    have hquad := quadForm_le_sq_sum_sqrt_diag hpsd probe
    rw [hdiagonalForm]
    nlinarith

/-- Every coordinate of the retained-window comparison diagonal is positive. -/
theorem unitAxisWindowDiagonal_pos
    (baseWeight : Fin 3 -> ℝ) (retained : Fin 3)
    (hbasePos : ∀ index, 0 < baseWeight index)
    (hbaseLt : ∀ index, baseWeight index < 1) :
    ∀ coordinate, 0 < unitAxisWindowDiagonal baseWeight retained coordinate := by
  intro coordinate
  fin_cases retained <;> fin_cases coordinate <;>
    simp [unitAxisWindowDiagonal, unitAxisBaseMass] <;>
    nlinarith [hbasePos 0, hbasePos 1, hbasePos 2,
      hbaseLt 0, hbaseLt 1, hbaseLt 2]

/-- The trace mass of the rank-one residual against the window diagonal is
exactly the selector mass. -/
theorem unitAxisWindowResidualMass_eq
    (baseWeight : Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ)
    (retained : Fin 3) :
    (∑ coordinate : Fin 3,
        (unitAxisBaseMass baseWeight • atomMatrix hidden) coordinate coordinate /
          unitAxisWindowDiagonal baseWeight retained coordinate)
      = unitAxisWindowRankOneMass baseWeight hidden retained := by
  fin_cases retained <;>
    simp [unitAxisWindowRankOneMass, unitAxisWindowDiagonal,
      unitAxisBaseMass, Fin.sum_univ_three, atomMatrix,
      Matrix.vecMulVec_apply] <;> ring

/-- A selector mass below one makes the explicit rank-one lower comparison
positive definite. -/
theorem unitAxisWindowLowerGap_posDef
    (baseWeight : Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ)
    (retained : Fin 3)
    (hbasePos : ∀ index, 0 < baseWeight index)
    (hbaseLt : ∀ index, baseWeight index < 1)
    (hbaseMassLt : unitAxisBaseMass baseWeight < 1)
    (hmass : unitAxisWindowRankOneMass baseWeight hidden retained < 1) :
    (unitAxisWindowLowerGap baseWeight hidden retained).PosDef := by
  let b := unitAxisBaseMass baseWeight
  have hbPos : 0 < b := by
    dsimp [b, unitAxisBaseMass]
    nlinarith [hbasePos 0, hbasePos 1, hbasePos 2]
  have hscale : 0 < 1 / (1 - b) := by
    exact one_div_pos.mpr (sub_pos.mpr hbaseMassLt)
  have hresidualPsd : (b • atomMatrix hidden).PosSemidef :=
    (posSemidef_atomMatrix hidden).smul hbPos.le
  have hdiagPos := unitAxisWindowDiagonal_pos baseWeight retained hbasePos hbaseLt
  have htrace :
      ∑ coordinate : Fin 3,
          (b • atomMatrix hidden) coordinate coordinate /
            unitAxisWindowDiagonal baseWeight retained coordinate < 1 := by
    rw [show b = unitAxisBaseMass baseWeight by rfl,
      unitAxisWindowResidualMass_eq]
    exact hmass
  have hgap :
      (Matrix.diagonal (unitAxisWindowDiagonal baseWeight retained)
        - b • atomMatrix hidden).PosDef :=
    posDef_diagonal_sub_of_sum_diag_div_lt_one hresidualPsd hdiagPos htrace
  exact hgap.smul hscale

/-- Each slack coefficient is the mass of the other two free labels divided
by the total free mass, hence is strictly positive. -/
theorem unitAxisWindowSlackWeight_pos
    (baseWeight freeWeight : Fin 3 -> ℝ)
    (hfreePos : ∀ index, 0 < freeWeight index)
    (hweightSum : unitAxisBaseMass baseWeight + freeWeight 0
        + freeWeight 1 + freeWeight 2 = 1) :
    ∀ freeIndex, 0 < unitAxisWindowSlackWeight baseWeight freeWeight freeIndex := by
  have hden : 0 < 1 - unitAxisBaseMass baseWeight := by
    nlinarith [hfreePos 0, hfreePos 1, hfreePos 2]
  intro freeIndex
  fin_cases freeIndex
  · change 0 < (1 - unitAxisBaseMass baseWeight - freeWeight 0) /
      (1 - unitAxisBaseMass baseWeight)
    apply div_pos
    · nlinarith [hfreePos 1, hfreePos 2]
    · exact hden
  · change 0 < (1 - unitAxisBaseMass baseWeight - freeWeight 1) /
      (1 - unitAxisBaseMass baseWeight)
    apply div_pos
    · nlinarith [hfreePos 0, hfreePos 2]
    · exact hden
  · change 0 < (1 - unitAxisBaseMass baseWeight - freeWeight 2) /
      (1 - unitAxisBaseMass baseWeight)
    apply div_pos
    · nlinarith [hfreePos 0, hfreePos 1]
    · exact hden

/-- The comparison slack is itself positive definite, not merely semidefinite. -/
theorem unitAxisWindowSlackFrame_posDef
    (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hfreePos : ∀ index, 0 < freeWeight index)
    (hweightSum : unitAxisBaseMass baseWeight + freeWeight 0
        + freeWeight 1 + freeWeight 2 = 1)
    (hdet : (freeAtomRowFrame freeAtom).det ≠ 0) :
    (unitAxisWindowSlackFrame baseWeight freeWeight freeAtom).PosDef := by
  exact unitAxisFreeWeightedFrame_posDef
    (unitAxisWindowSlackWeight baseWeight freeWeight) freeAtom
    (unitAxisWindowSlackWeight_pos baseWeight freeWeight hfreePos hweightSum) hdet

/-- Algebraic decomposition of the retained comparison diagonal. -/
theorem unitAxisWindowDiagonal_matrix_eq
    (baseWeight : Fin 3 -> ℝ) (retained : Fin 3) :
    Matrix.diagonal (unitAxisWindowDiagonal baseWeight retained)
      = unitAxisBaseMass baseWeight •
          Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate)
        + (1 - unitAxisBaseMass baseWeight) •
          (atomMatrix (Pi.single retained 1) - Matrix.diagonal baseWeight) := by
  ext row col
  fin_cases retained <;> fin_cases row <;> fin_cases col <;>
    simp [unitAxisWindowDiagonal, unitAxisBaseMass, atomMatrix,
      Matrix.vecMulVec_apply] <;> ring

/-- The lower comparison is the scaled weighted free frame plus the retained
coordinate correction. -/
theorem unitAxisWindowLowerGap_eq_scaledFree
    (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ)
    (retained : Fin 3)
    (hbaseMassLt : unitAxisBaseMass baseWeight < 1)
    (hframe : atomMatrix hidden
        + unitAxisFreeWeightedFrame freeWeight freeAtom
          = Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate)) :
    unitAxisWindowLowerGap baseWeight hidden retained
      = (unitAxisBaseMass baseWeight /
            (1 - unitAxisBaseMass baseWeight)) •
          unitAxisFreeWeightedFrame freeWeight freeAtom
        + (atomMatrix (Pi.single retained 1) - Matrix.diagonal baseWeight) := by
  let b := unitAxisBaseMass baseWeight
  let diagonalFrame :=
    Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate)
  let retainedCorrection :=
    atomMatrix (Pi.single retained 1) - Matrix.diagonal baseWeight
  have hden : 1 - b ≠ 0 := ne_of_gt (sub_pos.mpr hbaseMassLt)
  have hweighted : diagonalFrame - atomMatrix hidden
      = unitAxisFreeWeightedFrame freeWeight freeAtom := by
    calc
      diagonalFrame - atomMatrix hidden
          = (atomMatrix hidden + unitAxisFreeWeightedFrame freeWeight freeAtom)
              - atomMatrix hidden := by rw [hframe]
      _ = unitAxisFreeWeightedFrame freeWeight freeAtom := by abel
  have hone : (1 / (1 - b)) * (1 - b) = 1 := by
    field_simp
  have hbscale : (1 / (1 - b)) * b = b / (1 - b) := by ring
  unfold unitAxisWindowLowerGap
  change (1 / (1 - b)) •
      (Matrix.diagonal (unitAxisWindowDiagonal baseWeight retained)
        - b • atomMatrix hidden) = _
  rw [unitAxisWindowDiagonal_matrix_eq]
  change (1 / (1 - b)) •
      (b • diagonalFrame + (1 - b) • retainedCorrection
        - b • atomMatrix hidden) = _
  rw [smul_sub, smul_add, smul_smul, smul_smul, smul_smul,
    hone, hbscale, one_smul]
  calc
    (b / (1 - b)) • diagonalFrame + retainedCorrection
          - (b / (1 - b)) • atomMatrix hidden
        = (b / (1 - b)) • (diagonalFrame - atomMatrix hidden)
            + retainedCorrection := by rw [smul_sub]; abel
    _ = (unitAxisBaseMass baseWeight /
            (1 - unitAxisBaseMass baseWeight)) •
          unitAxisFreeWeightedFrame freeWeight freeAtom
        + (atomMatrix (Pi.single retained 1) - Matrix.diagonal baseWeight) := by
      rw [hweighted]

/-- Scaled weighted free mass plus the comparison slack is exactly the cofree
frame. -/
theorem unitAxisScaledFree_add_slack_eq_cofree
    (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hbaseMassLt : unitAxisBaseMass baseWeight < 1) :
    (unitAxisBaseMass baseWeight /
        (1 - unitAxisBaseMass baseWeight)) •
        unitAxisFreeWeightedFrame freeWeight freeAtom
      + unitAxisWindowSlackFrame baseWeight freeWeight freeAtom
        = unitAxisCofreeFrame freeWeight freeAtom := by
  have hden : 1 - unitAxisBaseMass baseWeight ≠ 0 :=
    ne_of_gt (sub_pos.mpr hbaseMassLt)
  ext row col
  simp only [unitAxisFreeWeightedFrame, unitAxisWindowSlackFrame,
    unitAxisWindowSlackWeight, unitAxisCofreeFrame, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  field_simp [hden]
  ring

/-- **Exact four-window decomposition.**  The desired window is the sum of
the positive rank-one lower comparison and the positive free-frame slack. -/
theorem unitAxisFourWindowGap_eq_lower_add_slack
    (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ)
    (retained : Fin 3)
    (hbaseMassLt : unitAxisBaseMass baseWeight < 1)
    (hframe : atomMatrix hidden
        + unitAxisFreeWeightedFrame freeWeight freeAtom
          = Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate)) :
    unitAxisFourWindowGap baseWeight freeWeight freeAtom retained
      = unitAxisWindowLowerGap baseWeight hidden retained
          + unitAxisWindowSlackFrame baseWeight freeWeight freeAtom := by
  rw [unitAxisWindowLowerGap_eq_scaledFree baseWeight freeWeight freeAtom
    hidden retained hbaseMassLt hframe]
  have hcofree := unitAxisScaledFree_add_slack_eq_cofree
    baseWeight freeWeight freeAtom hbaseMassLt
  unfold unitAxisFourWindowGap unitAxisWeightedComplementGap
  rw [← hcofree]
  abel

/-- The hidden-plus-free complement formula is the cofree-minus-base formula
once the unit-axis Parseval identity is used. -/
theorem planeAxisComplementGap_one_eq_unitAxisWeightedComplementGap
    (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ)
    (hframe : atomMatrix hidden
        + unitAxisFreeWeightedFrame freeWeight freeAtom
          = Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate)) :
    planeAxisComplementGap (fun _ : Fin 3 => (1 : ℝ)) freeAtom hidden
      = unitAxisWeightedComplementGap baseWeight freeWeight freeAtom := by
  ext row col
  have hentry := congrFun (congrFun hframe row) col
  fin_cases row <;> fin_cases col <;>
    simp [planeAxisComplementGap, unitAxisWeightedComplementGap,
      unitAxisCofreeFrame, unitAxisFreeWeightedFrame, atomMatrix,
      Matrix.vecMulVec_apply] at hentry ⊢ <;> linarith

/-- Adding the retained coordinate to the complement gap is exactly the
four-label transformed subset gap. -/
theorem planeAxisSubsetGap_fourWindow_eq_complement_add_coordinate
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ)
    (retained : Fin 3) :
    planeAxisSubsetGap (fun _ : Fin 3 => (1 : ℝ)) freeAtom hidden
        (planeBranchFourWindow retained)
      = planeAxisComplementGap (fun _ : Fin 3 => (1 : ℝ)) freeAtom hidden
          + atomMatrix (Pi.single retained 1) := by
  ext row col
  fin_cases retained <;> fin_cases row <;> fin_cases col <;>
    simp [planeBranchFourWindow, planeAxisSubsetGap, planeAxisComplementGap,
      planeAxisMetric, axisBaseAtom, baseThreeLabel, atomMatrix,
      Matrix.vecMulVec_apply] <;> ring

/-- The abstract positive four-window is literally the transformed original
four-label subset gap. -/
theorem planeAxisSubsetGap_fourWindow_eq_unitAxisFourWindowGap
    (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ)
    (retained : Fin 3)
    (hframe : atomMatrix hidden
        + unitAxisFreeWeightedFrame freeWeight freeAtom
          = Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate)) :
    planeAxisSubsetGap (fun _ : Fin 3 => (1 : ℝ)) freeAtom hidden
        (planeBranchFourWindow retained)
      = unitAxisFourWindowGap baseWeight freeWeight freeAtom retained := by
  rw [planeAxisSubsetGap_fourWindow_eq_complement_add_coordinate,
    planeAxisComplementGap_one_eq_unitAxisWeightedComplementGap
      baseWeight freeWeight freeAtom hidden hframe]
  rfl

/-- **FOUR-WINDOW SELECTOR, abstract unit-axis form.**  Under the exact
rank-one Parseval identity, one of the three windows consisting of a retained
base axis and all three free atoms has positive-definite gap. -/
theorem exists_unitAxisFourWindowGap_posDef
    (baseWeight freeWeight : Fin 3 -> ℝ)
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) (hidden : Fin 3 -> ℝ)
    (hbasePos : ∀ index, 0 < baseWeight index)
    (hbaseLt : ∀ index, baseWeight index < 1)
    (hfreePos : ∀ index, 0 < freeWeight index)
    (hweightSum : unitAxisBaseMass baseWeight + freeWeight 0
        + freeWeight 1 + freeWeight 2 = 1)
    (hframe : atomMatrix hidden
        + unitAxisFreeWeightedFrame freeWeight freeAtom
          = Matrix.diagonal (fun coordinate => 1 - baseWeight coordinate))
    (hdet : (freeAtomRowFrame freeAtom).det ≠ 0) :
    ∃ retained : Fin 3,
      (unitAxisFourWindowGap baseWeight freeWeight freeAtom retained).PosDef := by
  have hbaseMassLt : unitAxisBaseMass baseWeight < 1 := by
    nlinarith [hfreePos 0, hfreePos 1, hfreePos 2]
  have hhiddenMass : unitAxisHiddenMass baseWeight hidden < 1 :=
    unitAxisHiddenMass_lt_one baseWeight freeWeight freeAtom hidden hbaseLt
      hfreePos hframe hdet
  obtain ⟨retained, hselector⟩ :=
    exists_unitAxisWindowRankOneMass_lt_one baseWeight hidden hbasePos hbaseLt
      hhiddenMass
  have hlower := unitAxisWindowLowerGap_posDef baseWeight hidden retained
    hbasePos hbaseLt hbaseMassLt hselector
  have hslack := unitAxisWindowSlackFrame_posDef baseWeight freeWeight freeAtom
    hfreePos hweightSum hdet
  refine ⟨retained, ?_⟩
  rw [unitAxisFourWindowGap_eq_lower_add_slack baseWeight freeWeight freeAtom
    hidden retained hbaseMassLt hframe]
  exact hlower.add hslack

/-- The six design weights split into the three unit-axis base weights and the
three free weights. -/
theorem unitAxis_weight_split (design : WeightedDesign 6 3) :
    unitAxisBaseMass (unitAxisBaseWeight design)
        + unitAxisFreeWeight design 0 + unitAxisFreeWeight design 1
        + unitAxisFreeWeight design 2 = 1 := by
  have hsum := design.weight_sum_one
  rw [Fin.sum_univ_six] at hsum
  simpa [unitAxisBaseMass, unitAxisBaseWeight, unitAxisFreeWeight,
    baseThreeLabel, freeThreeLabel, add_assoc] using hsum

/-- **FOUR-WINDOW SELECTOR, design form.**  Every line-free, off-conic
rank-one plane-branch antecedent has a positive four-label window consisting
of one base label and all three free labels. -/
theorem exists_posDef_unitAxisFourWindow_of_planeBranch
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ∃ hidden : Fin 3 -> ℝ, ∃ retained : Fin 3,
      atomMatrix hidden
          + unitAxisFreeWeightedFrame (unitAxisFreeWeight design)
              (unitAxisFreeAtom design)
        = Matrix.diagonal (fun coordinate =>
            1 - unitAxisBaseWeight design coordinate)
      ∧ (unitAxisBaseNormalizer design)ᵀ * unitAxisBaseNormalizer design
          = 1 - atomMatrix hidden
      ∧ (unitAxisFourWindowGap (unitAxisBaseWeight design)
          (unitAxisFreeWeight design) (unitAxisFreeAtom design) retained).PosDef := by
  obtain ⟨hidden, hframeRaw, hmetric, _hoffDiagonal, hfreeDet⟩ :=
    exists_planeBranch_unitAxisNormalForm design hlineFree hoffConic hdominates hfree
  have hframe : atomMatrix hidden
      + unitAxisFreeWeightedFrame (unitAxisFreeWeight design)
          (unitAxisFreeAtom design)
        = Matrix.diagonal (fun coordinate =>
            1 - unitAxisBaseWeight design coordinate) := by
    simpa [unitAxisFreeWeightedFrame, unitAxisBaseWeight, unitAxisFreeWeight,
      baseThreeLabel, freeThreeLabel, add_assoc] using hframeRaw
  have hbasePos : ∀ index, 0 < unitAxisBaseWeight design index := by
    intro index
    exact design.weight_pos (baseThreeLabel index)
  have hbaseLt : ∀ index, unitAxisBaseWeight design index < 1 := by
    intro index
    exact weight_lt_one design (by norm_num) (baseThreeLabel index)
  have hfreePos : ∀ index, 0 < unitAxisFreeWeight design index := by
    intro index
    exact design.weight_pos (freeThreeLabel index)
  have hdet : (freeAtomRowFrame (unitAxisFreeAtom design)).det ≠ 0 := by
    rw [freeAtomRowFrame_unitAxisFreeAtom]
    exact hfreeDet
  obtain ⟨retained, hwindow⟩ := exists_unitAxisFourWindowGap_posDef
    (unitAxisBaseWeight design) (unitAxisFreeWeight design)
    (unitAxisFreeAtom design) hidden hbasePos hbaseLt hfreePos
    (unitAxis_weight_split design) hframe hdet
  exact ⟨hidden, retained, hframe, hmetric, hwindow⟩

@[simp] theorem planeBranchFourWindow_card (retained : Fin 3) :
    (planeBranchFourWindow retained).card = 4 := by
  fin_cases retained <;>
    simp [planeBranchFourWindow, baseThreeLabel]

/-- **FOUR-WINDOW SELECTOR, original coordinates.**  The positive window is
an honest four-label subset of the original design, not only a normal-form
matrix. -/
theorem exists_posDef_fourWindow_of_planeBranch
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ∃ window : Finset (Fin 6), window.card = 4
      ∧ (subsetSum design window - 1).PosDef := by
  obtain ⟨hidden, retained, hframe, hmetric, hwindow⟩ :=
    exists_posDef_unitAxisFourWindow_of_planeBranch design hlineFree hoffConic
      hdominates hfree
  let window := planeBranchFourWindow retained
  have haxis :
      (planeAxisSubsetGap (fun _ : Fin 3 => (1 : ℝ))
        (unitAxisFreeAtom design) hidden window).PosDef := by
    rw [show window = planeBranchFourWindow retained by rfl,
      planeAxisSubsetGap_fourWindow_eq_unitAxisFourWindowGap
        (unitAxisBaseWeight design) (unitAxisFreeWeight design)
        (unitAxisFreeAtom design) hidden retained hframe]
    exact hwindow
  refine ⟨window, ?_, ?_⟩
  · exact planeBranchFourWindow_card retained
  · exact (posDef_gap_iff_unitAxisSubsetGap design hlineFree hidden hmetric
      window).mpr haxis

end Gtz
