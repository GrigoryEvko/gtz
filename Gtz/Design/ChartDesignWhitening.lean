import Gtz.Design.ZMatrixAlternative
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The chart-design whitening

The K4 chart is the complete-quadrilateral stratum of the design problem.
This module makes the identification a theorem chain: every chart point
whitens to a mass-one weighted design with the same weights, domination
transfers through the whitening as an equivalence, the four triangles are
never strict on either side, and therefore any design-level strict selection
discharges the K4 registry obligation.

* `kFourMomentMatrix_posDef` — the moment matrix of a chart point is positive
  definite, from the span of the six directions.
* `exists_kFourWhitenedDesign` — the whitening: a `WeightedDesign 6 3` with
  the chart weights whose subset gaps are congruent to the chart gaps.  The
  congruence witness comes from the landed `exists_congruence_to_one`.
* `kFourTriangle_gap_not_posDef` — the four dependent triples are never
  strict: each carries an explicit normal direction that reads zero inside
  and a negative total.
* `mem_kFourSpanningTreeList_of_card_three` — a three-set that is not one of
  the four triangles is a spanning tree.
* `kFourKnifeBandRefinedTenthHeavy_of_designSelection` — **the weld**: a
  design-level strict selection theorem at mass one discharges the committed
  A3 axiom verbatim.
-/

namespace Gtz

open Matrix

/-! ## The conjugation reading of an atom matrix -/

/-- Conjugating a rank-one atom matrix by a transposed matrix action. -/
theorem atomMatrix_transpose_mulVec (R : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    atomMatrix (Rᵀ *ᵥ x) = Rᵀ * atomMatrix x * R := by
  ext i j
  simp only [atomMatrix, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec,
    Matrix.transpose_apply, dotProduct, Fin.sum_univ_three]
  ring

/-! ## The moment matrix of a chart point -/

/-- The moment matrix `S = Σ m_c v_c v_cᵀ` of a K4 chart point. -/
noncomputable def kFourMomentMatrix (point : DirectionChartPoint 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ label, point.mass label • atomMatrix (kFourDirection label)

/-- The moment matrix is symmetric. -/
theorem kFourMomentMatrix_transpose (point : DirectionChartPoint 6) :
    (kFourMomentMatrix point)ᵀ = kFourMomentMatrix point := by
  ext i j
  simp only [kFourMomentMatrix, Matrix.transpose_apply, Matrix.sum_apply,
    Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The moment matrix quadratic form is the mass-weighted energy. -/
theorem dotProduct_kFourMomentMatrix_mulVec (point : DirectionChartPoint 6)
    (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (kFourMomentMatrix point *ᵥ probe)
      = ∑ label, point.mass label * (kFourDirection label ⬝ᵥ probe) ^ 2 := by
  rw [kFourMomentMatrix, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun label _ => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]

/-- **The moment matrix is positive definite**: the six K4 directions span. -/
theorem kFourMomentMatrix_posDef (point : DirectionChartPoint 6) :
    (kFourMomentMatrix point).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (kFourMomentMatrix_transpose point), fun probe hne => ?_⟩
  rw [star_trivial, dotProduct_kFourMomentMatrix_mulVec]
  have hnonneg : ∀ label ∈ Finset.univ,
      0 ≤ point.mass label * (kFourDirection label ⬝ᵥ probe) ^ 2 :=
    fun label _ => mul_nonneg (point.mass_pos label).le (sq_nonneg _)
  obtain ⟨witness, hwitness⟩ : ∃ label, kFourDirection label ⬝ᵥ probe ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (kFourDirection_span probe hall)
  have hsq : 0 < (kFourDirection witness ⬝ᵥ probe) ^ 2 := by
    rcases lt_or_gt_of_ne hwitness with h | h <;> nlinarith
  exact Finset.sum_pos' hnonneg
    ⟨witness, Finset.mem_univ witness, mul_pos (point.mass_pos witness) hsq⟩

/-! ## The whitened design -/

/-- **The whitening.**  Every K4 chart point produces a mass-one weighted
design with the chart weights whose subset gaps are positive definite exactly
when the chart gaps are. -/
theorem exists_kFourWhitenedDesign (point : DirectionChartPoint 6) :
    ∃ D : WeightedDesign 6 3, D.weight = point.weight
      ∧ ∀ C : Finset (Fin 6),
          ((subsetSum D C - 1).PosDef
            ↔ (directionChartGap kFourDirection point.mass point.weight C).PosDef) := by
  obtain ⟨R, hRdet, hRone⟩ := exists_congruence_to_one (kFourMomentMatrix_posDef point)
  set scaleOf : Fin 6 → ℝ :=
    fun label => Real.sqrt (point.mass label / point.weight label) with hscaleOf
  have hscaleSq : ∀ label, scaleOf label ^ 2 = point.mass label / point.weight label :=
    fun label => Real.sq_sqrt
      (div_nonneg (point.mass_pos label).le (point.weight_pos label).le)
  have hatomEq : ∀ label,
      atomMatrix (Rᵀ *ᵥ (scaleOf label • kFourDirection label))
        = (point.mass label / point.weight label)
            • (Rᵀ * atomMatrix (kFourDirection label) * R) := by
    intro label
    rw [atomMatrix_transpose_mulVec, atomMatrix_smul, ← hscaleSq label]
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hsubsetEq : ∀ C : Finset (Fin 6),
      (∑ label ∈ C, atomMatrix (Rᵀ *ᵥ (scaleOf label • kFourDirection label)))
        = Rᵀ * (∑ label ∈ C,
            (point.mass label / point.weight label) • atomMatrix (kFourDirection label)) * R := by
    intro C
    rw [Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun label _ => by
      rw [hatomEq label, Matrix.mul_smul, Matrix.smul_mul]
  have hparseval :
      (∑ label, point.weight label
          • atomMatrix (Rᵀ *ᵥ (scaleOf label • kFourDirection label))) = 1 := by
    have hmassEq : ∀ label,
        point.weight label • atomMatrix (Rᵀ *ᵥ (scaleOf label • kFourDirection label))
          = point.mass label • (Rᵀ * atomMatrix (kFourDirection label) * R) := by
      intro label
      rw [hatomEq label, smul_smul,
        mul_div_cancel₀ _ (point.weight_pos label).ne']
    calc (∑ label, point.weight label
          • atomMatrix (Rᵀ *ᵥ (scaleOf label • kFourDirection label)))
        = ∑ label, point.mass label • (Rᵀ * atomMatrix (kFourDirection label) * R) :=
          Finset.sum_congr rfl fun label _ => hmassEq label
      _ = Rᵀ * kFourMomentMatrix point * R := by
          rw [kFourMomentMatrix, Matrix.mul_sum, Matrix.sum_mul]
          exact Finset.sum_congr rfl fun label _ => by
            rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = 1 := hRone
  refine ⟨⟨fun label => Rᵀ *ᵥ (scaleOf label • kFourDirection label),
    point.weight, point.weight_pos, point.weight_sum_one, hparseval⟩, rfl, fun C => ?_⟩
  have hgapEq : subsetSum ⟨fun label => Rᵀ *ᵥ (scaleOf label • kFourDirection label),
      point.weight, point.weight_pos, point.weight_sum_one, hparseval⟩ C - 1
      = Rᵀ * directionChartGap kFourDirection point.mass point.weight C * R := by
    show (∑ label ∈ C, atomMatrix (Rᵀ *ᵥ (scaleOf label • kFourDirection label))) - 1
      = Rᵀ * directionChartGap kFourDirection point.mass point.weight C * R
    rw [hsubsetEq C, ← hRone, directionChartGap, Matrix.mul_sub, Matrix.sub_mul]
    rfl
  rw [hgapEq]
  exact (posDef_congr_right
    (directionChartGap_transpose kFourDirection point.mass point.weight C) hRdet).symm

/-! ## The four triangles are never strict -/

/-- The chart gap of a dependent triple is refuted by its normal direction:
the inside readings vanish and one outside reading is a unit. -/
theorem kFourTriangle_gap_not_posDef_of_normal (point : DirectionChartPoint 6)
    (C : Finset (Fin 6)) (normal : Fin 3 → ℝ) (outLabel : Fin 6)
    (hinside : ∀ label ∈ C, kFourDirection label ⬝ᵥ normal = 0)
    (houtside : (kFourDirection outLabel ⬝ᵥ normal) ^ 2 = 1)
    (hne : normal ≠ 0) :
    ¬ (directionChartGap kFourDirection point.mass point.weight C).PosDef := by
  intro hpd
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hne
  rw [star_trivial, dotProduct_directionChartGap_mulVec_eq] at hform
  have hinsideSum : (∑ label ∈ C,
      point.mass label / point.weight label * (kFourDirection label ⬝ᵥ normal) ^ 2) = 0 :=
    Finset.sum_eq_zero fun label hmem => by rw [hinside label hmem]; ring
  have houtBound : point.mass outLabel
      ≤ ∑ label, point.mass label * (kFourDirection label ⬝ᵥ normal) ^ 2 := by
    have hterm : point.mass outLabel * (kFourDirection outLabel ⬝ᵥ normal) ^ 2
        = point.mass outLabel := by rw [houtside, mul_one]
    calc point.mass outLabel
        = point.mass outLabel * (kFourDirection outLabel ⬝ᵥ normal) ^ 2 := hterm.symm
      _ ≤ ∑ label, point.mass label * (kFourDirection label ⬝ᵥ normal) ^ 2 :=
          Finset.single_le_sum
            (f := fun label => point.mass label * (kFourDirection label ⬝ᵥ normal) ^ 2)
            (fun label _ => mul_nonneg (point.mass_pos label).le (sq_nonneg _))
            (Finset.mem_univ outLabel)
  rw [hinsideSum] at hform
  linarith [point.mass_pos outLabel]

/-- **The four triangles are never strict.** -/
theorem kFourTriangle_gap_not_posDef (point : DirectionChartPoint 6)
    (C : Finset (Fin 6))
    (htriangle : C = {0, 1, 2} ∨ C = {0, 3, 4} ∨ C = {1, 3, 5} ∨ C = {2, 4, 5}) :
    ¬ (directionChartGap kFourDirection point.mass point.weight C).PosDef := by
  rcases htriangle with h | h | h | h <;> subst h
  · refine kFourTriangle_gap_not_posDef_of_normal point _ ![1, 1, 1] 3 ?_ ?_ ?_
    · intro label hmem
      fin_cases hmem <;>
        simp [kFourDirection, dotProduct, Fin.sum_univ_three]
    · simp [kFourDirection, dotProduct, Fin.sum_univ_three]
    · intro h0
      have := congrFun h0 0
      simp at this
  · refine kFourTriangle_gap_not_posDef_of_normal point _ ![0, 0, 1] 5 ?_ ?_ ?_
    · intro label hmem
      fin_cases hmem <;>
        simp [kFourDirection, dotProduct, Fin.sum_univ_three]
    · simp [kFourDirection, dotProduct, Fin.sum_univ_three]
    · intro h0
      have := congrFun h0 2
      simp at this
  · refine kFourTriangle_gap_not_posDef_of_normal point _ ![0, 1, 0] 4 ?_ ?_ ?_
    · intro label hmem
      fin_cases hmem <;>
        simp [kFourDirection, dotProduct, Fin.sum_univ_three]
    · simp [kFourDirection, dotProduct, Fin.sum_univ_three]
    · intro h0
      have := congrFun h0 1
      simp at this
  · refine kFourTriangle_gap_not_posDef_of_normal point _ ![1, 0, 0] 3 ?_ ?_ ?_
    · intro label hmem
      fin_cases hmem <;>
        simp [kFourDirection, dotProduct, Fin.sum_univ_three]
    · simp [kFourDirection, dotProduct, Fin.sum_univ_three]
    · intro h0
      have := congrFun h0 0
      simp at this

/-- A three-set of labels that is not one of the four triangles is a K4
spanning tree. -/
theorem mem_kFourSpanningTreeList_of_card_three (C : Finset (Fin 6))
    (hcard : C.card = 3)
    (htri : ¬ (C = {0, 1, 2} ∨ C = {0, 3, 4} ∨ C = {1, 3, 5} ∨ C = {2, 4, 5})) :
    C ∈ kFourSpanningTreeList := by
  revert hcard htri
  revert C
  decide

/-! ## The weld -/

/-- A design-level strict selection hands every chart point a strict spanning
tree.  The whitening transfers the strict triple to the chart, and the
triangle refuters land it on the tree list. -/
theorem kFourStrictTree_of_designSelection
    (hsel : ∀ D : WeightedDesign 6 3, ∃ C : Finset (Fin 6),
      C.card = 3 ∧ (subsetSum D C - 1).PosDef)
    (point : DirectionChartPoint 6) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨D, _, hiff⟩ := exists_kFourWhitenedDesign point
  obtain ⟨C, hcard, hpd⟩ := hsel D
  have hchart := (hiff C).mp hpd
  refine ⟨C, mem_kFourSpanningTreeList_of_card_three C hcard ?_, hchart⟩
  intro htriangle
  exact kFourTriangle_gap_not_posDef point C htriangle hchart

/-- **THE WELD.**  A design-level strict selection theorem at mass one
discharges the committed A3 axiom verbatim. -/
theorem kFourKnifeBandRefinedTenthHeavy_of_designSelection
    (hsel : ∀ D : WeightedDesign 6 3, ∃ C : Finset (Fin 6),
      C.card = 3 ∧ (subsetSum D C - 1).PosDef) :
    KFourKnifeBandRefinedTenthHeavyWeakToStrict :=
  kFourKnifeBandRefinedTenthHeavy_of_strictTree
    (kFourStrictTree_of_designSelection hsel)

end Gtz
