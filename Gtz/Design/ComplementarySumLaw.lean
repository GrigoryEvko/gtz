import Gtz.Design.ThreeLinesCircuitSpine
import Gtz.Design.StarOnlyLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The complementary sum law of the chart gap

Every landed law reads the chart gap at ONE selection.  This module reads it at a
selection and its complement AT ONCE, and the two are locked together by an
identity that does not mention the selection:

  `directionChartGap S + directionChartGap Sᶜ = ∑ c, (m c / w c - 2 * m c) • atom c`

The right-hand side is the same matrix for all `2 ^ size` selections.  Call it the
COMPLEMENT SUM.  Three consequences follow, and all of them are generic in the
size and in the direction family, so they serve the K4 chart, the three-lines
chart, and the design-level descent alike.

**The sign of the complement sum is the half-weight test.**  The coefficient
`m c / w c - 2 * m c` is `m c * (1 - 2 * w c) / w c`, which is positive exactly
when the weight is below one half.  Weights sum to one, so at most one label of a
chart point can carry weight above one half: the complement sum is positive
definite on the nose in the generic case, and a rank-one downdate of a positive
definite matrix in the one exceptional case.

**Two complementary selections cannot both fail at the same probe.**  When the
complement sum is positive definite, every nonzero probe reads at least one of
the two selections strictly positively.  A selection whose gap is negative
semidefinite therefore hands its complement a positive definite gap outright.

**The pairing is an involution on the twenty card-three selections of a
six-label chart**, which splits them into ten complementary pairs.  At the
three-lines chart the pair of rotation-fixed triples, the vertex `{0,1,3}` and
the free `{2,4,5}`, is one of those ten.
-/

namespace Gtz

open Matrix Finset

/-! ## The complement coefficient -/

/-- The coefficient of the COMPLEMENT SUM at a label: the selected excess minus
the unselected mass, `m (1 - 2 w) / w`.  It is positive exactly below weight one
half. -/
noncomputable def chartComplementCoefficient {size : ℕ} (mass weight : Fin size → ℝ)
    (label : Fin size) : ℝ :=
  mass label / weight label - 2 * mass label

theorem chartComplementCoefficient_pos_of_weight_lt_half {size : ℕ}
    (mass weight : Fin size → ℝ) (label : Fin size)
    (hmassPos : 0 < mass label) (hweightPos : 0 < weight label)
    (hweightHalf : weight label < 1 / 2) :
    0 < chartComplementCoefficient mass weight label := by
  rw [chartComplementCoefficient, sub_pos, lt_div_iff₀ hweightPos]
  nlinarith

/-! ## The law -/

/-- **THE COMPLEMENTARY SUM LAW.**  The chart gap of a selection and the chart
gap of its complement add to a matrix that does not depend on the selection.

Every term of the gap that mentions the selection cancels: the two selected
excess sums join into the full sum over all labels, and the two full mass sums
double.  The law holds at every size, every direction family, and every mass and
weight, with no positivity and no span hypothesis. -/
theorem directionChartGap_add_compl {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) :
    directionChartGap direction mass weight selected
        + directionChartGap direction mass weight selectedᶜ
      = ∑ label, chartComplementCoefficient mass weight label
          • atomMatrix (direction label) := by
  classical
  have hjoin : (∑ label ∈ selected, (mass label / weight label)
        • atomMatrix (direction label))
      + ∑ label ∈ selectedᶜ, (mass label / weight label)
        • atomMatrix (direction label)
      = ∑ label, (mass label / weight label) • atomMatrix (direction label) :=
    Finset.sum_add_sum_compl selected _
  rw [directionChartGap, directionChartGap, sub_add_sub_comm, hjoin,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [chartComplementCoefficient, sub_smul, two_mul, add_smul]

/-- **The complementary sum law at a probe.**  The two readings add to the
weighted sum of squared readings of the whole direction family. -/
theorem dotProduct_directionChartGap_add_compl {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe)
        + probe ⬝ᵥ (directionChartGap direction mass weight selectedᶜ *ᵥ probe)
      = ∑ label, chartComplementCoefficient mass weight label
          * (direction label ⬝ᵥ probe) ^ 2 := by
  classical
  rw [dotProduct_directionChartGap_mulVec_eq, dotProduct_directionChartGap_mulVec_eq]
  have hjoin : (∑ label ∈ selected, mass label / weight label
        * (direction label ⬝ᵥ probe) ^ 2)
      + ∑ label ∈ selectedᶜ, mass label / weight label
        * (direction label ⬝ᵥ probe) ^ 2
      = ∑ label, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 :=
    Finset.sum_add_sum_compl selected _
  rw [show ∀ a b c : ℝ, a - c + (b - c) = a + b - (c + c) from fun a b c => by ring,
    hjoin, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [chartComplementCoefficient]
  ring

/-! ## The half-weight test -/

/-- Two distinct labels of a chart point carry at most one unit of weight
between them, because the weights are a probability vector. -/
theorem directionChartPoint_weight_add_le_one {size : ℕ} (point : DirectionChartPoint size)
    {first second : Fin size} (hne : first ≠ second) :
    point.weight first + point.weight second ≤ 1 := by
  classical
  have hsub : ({first, second} : Finset (Fin size)) ⊆ Finset.univ := Finset.subset_univ _
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun label _ _ => le_of_lt (point.weight_pos label))
  rw [Finset.sum_pair hne, point.weight_sum_one] at hle
  exact hle

/-- **THE HALF-WEIGHT TEST.**  At most one label of a chart point carries weight
above one half.  This is what makes the complement sum positive definite in the
generic case, and it costs nothing beyond the probability constraint. -/
theorem directionChartPoint_not_both_gt_half {size : ℕ} (point : DirectionChartPoint size)
    {first second : Fin size} (hne : first ≠ second) :
    ¬ (1 / 2 < point.weight first ∧ 1 / 2 < point.weight second) := by
  rintro ⟨hfirst, hsecond⟩
  have := directionChartPoint_weight_add_le_one point hne
  linarith

/-! ## The complement sum is positive definite -/

/-- **THE COMPLEMENT SUM IS POSITIVE DEFINITE** whenever every weight is below
one half and the directions span.  By the half-weight test at most one label can
fail the hypothesis, so this is the generic case of a chart point. -/
theorem posDef_chartComplementSum_of_weights_lt_half {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    (hhalf : ∀ label, point.weight label < 1 / 2)
    (hspan : ∀ probe : Fin 3 → ℝ, (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0) :
    (∑ label, chartComplementCoefficient point.mass point.weight label
      • atomMatrix (direction label)).PosDef := by
  classical
  have hcoeff : ∀ label, 0 < chartComplementCoefficient point.mass point.weight label :=
    fun label => chartComplementCoefficient_pos_of_weight_lt_half point.mass point.weight
      label (point.mass_pos label) (point.weight_pos label) (hhalf label)
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hne => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun label _ => by
      rw [Matrix.transpose_smul, atomMatrix_transpose]
  · rw [star_trivial, dotProduct_sum_smul_atomMatrix_mulVec]
    obtain ⟨witness, hwitness⟩ : ∃ label, direction label ⬝ᵥ probe ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (hspan probe hall)
    refine Finset.sum_pos' (fun label _ => ?_) ⟨witness, Finset.mem_univ _, ?_⟩
    · exact mul_nonneg (le_of_lt (hcoeff label)) (sq_nonneg _)
    · exact mul_pos (hcoeff witness) (by positivity)

/-! ## The consequence for a complementary pair -/

/-- **THE COMPLEMENTARY DISJUNCTION.**  When the complement sum is positive
definite, every nonzero probe reads at least one of two complementary selections
strictly positively.  Two complementary selections can fail, but never at the
same direction. -/
theorem exists_pos_reading_of_complementary {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    (hsum : (∑ label, chartComplementCoefficient point.mass point.weight label
      • atomMatrix (direction label)).PosDef)
    (selected : Finset (Fin size)) {probe : Fin 3 → ℝ} (hne : probe ≠ 0) :
    0 < probe ⬝ᵥ (directionChartGap direction point.mass point.weight selected *ᵥ probe)
      ∨ 0 < probe ⬝ᵥ (directionChartGap direction point.mass point.weight
        selectedᶜ *ᵥ probe) := by
  by_contra hboth
  push Not at hboth
  obtain ⟨hleft, hright⟩ := hboth
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hsum).2 hne
  rw [star_trivial, dotProduct_sum_smul_atomMatrix_mulVec,
    ← dotProduct_directionChartGap_add_compl direction point.mass point.weight
      selected probe] at hpos
  linarith

/-- **A NEGATIVE SEMIDEFINITE SELECTION HANDS ITS COMPLEMENT A STRICT GAP.**
This is the sharpest usable form of the law: it turns total failure at one
selection into outright success at the complementary one. -/
theorem posDef_compl_of_nonpos_reading {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    (hsum : (∑ label, chartComplementCoefficient point.mass point.weight label
      • atomMatrix (direction label)).PosDef)
    (selected : Finset (Fin size))
    (hnonpos : ∀ probe : Fin 3 → ℝ,
      probe ⬝ᵥ (directionChartGap direction point.mass point.weight selected *ᵥ probe) ≤ 0) :
    (directionChartGap direction point.mass point.weight selectedᶜ).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (directionChartGap_transpose _ _ _ _), fun probe hne => ?_⟩
  rw [star_trivial]
  rcases exists_pos_reading_of_complementary direction point hsum selected hne with
    hleft | hright
  · exact absurd hleft (not_lt.mpr (hnonpos probe))
  · exact hright

/-! ## The three-lines instance -/

/-- The vertex triple and the free triple of the three-lines chart are
complementary.  They are exactly the two card-three selections the `Z/3` rotation
fixes, so the law pairs the chart's two canonical cells. -/
theorem threeLines_vertexTriple_compl :
    (({0, 1, 3} : Finset (Fin 6)))ᶜ = ({2, 4, 5} : Finset (Fin 6)) := by
  decide

/-- **THE CANONICAL PAIR LAW.**  At the three-lines chart the vertex gap and the
free gap add to the complement sum.  The campaign already knows that neither cell
covers alone and that a two-cell atlas on this pair is impossible; the law says
what the pair does control, namely that the two never fail at one probe once the
weights are below one half. -/
theorem threeLines_vertexTriple_add_freeTriple (slide : ℝ) (point : DirectionChartPoint 6) :
    directionChartGap (threeLinesDirection slide) point.mass point.weight {0, 1, 3}
        + directionChartGap (threeLinesDirection slide) point.mass point.weight {2, 4, 5}
      = ∑ label, chartComplementCoefficient point.mass point.weight label
          • atomMatrix (threeLinesDirection slide label) := by
  rw [← threeLines_vertexTriple_compl]
  exact directionChartGap_add_compl _ _ _ _

end Gtz
