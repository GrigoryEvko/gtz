import Gtz.Wave.WedgeBalanceAdjugate
import Gtz.Wave.KirchhoffSignTower
import Gtz.Wave.DeflatedCellTotal

/-!
# The `K4` wedge law, and the forest triple on the produced tree

Two landed pairs of the `K4` class speak the same mathematics in different
vocabularies and were never joined.

* `Gtz.adjugate_sum_smul_atomMatrix` is the adjugate of an ARBITRARY signed atom
  sum at rank three.  `Gtz.kFourLaplacian` is exactly such a sum, over the six
  `K4` directions.  So the general law applies verbatim, and it hands the
  contraction tree polynomial a closed form: a HALVED DOUBLE SUM OF SQUARED
  BRACKETS, one term for each ordered pair of edges.  The corpus carried only the
  trace reading of the adjugate and the explicit eight-term polynomial.
* `Gtz.kFour_exists_chartDeflatedTree` produces, at every chart point and every
  label, a spanning tree whose strict domination IS one determinant sign.
  `Gtz.posDef_directionChartGap_iff_forestTriple` decides the same strict
  domination by THREE spanning-forest sums.  On the produced tree the two meet,
  and the triple collapses to its third component alone.

Nothing in the two source modules imports the other.  This module is the join.

AUDIT-UNCONSUMED (2026-08-17): NO module imports this file except the `Gtz.lean`
umbrella.  Real consumer count is ZERO.  That is a mis-shelving, not a shortage
of content: `Gtz.kFour_exists_tree_posDef_iff_massTreeSum` is the SHARPEST
landed reduction of the whole `M(K4)` class.  It is UNCONDITIONAL, and it carries
NO block conjunct, so it strictly dominates
`Gtz.KFourBlockAdmissibleDetTotal` (Gtz/Wave/WiringKFourWalls.lean), which
still pays for a `leadingTwoBlock` positive definiteness side condition.
Read against it, `Gtz.KFourUniversalStrictTree` becomes: at every chart point,
for SOME drop label, the produced tree has a positive signed tree sum.  ONE
polynomial inequality, no matrix.
-/

namespace Gtz

open Matrix

/-! ## 1. The wedge is the bracket

`Gtz.atomWedge` is the cross product and `Gtz.tripleBracket` is the three by three
determinant.  Read against a third vector the first IS the second. -/

/-- **THE WEDGE READ AGAINST A THIRD VECTOR IS THE BRACKET.**  The scalar triple
product, in the two vocabularies the tree uses for it. -/
theorem atomWedge_dotProduct_eq_tripleBracket (leftVec midVec rightVec : Fin 3 → ℝ) :
    atomWedge leftVec midVec ⬝ᵥ rightVec = tripleBracket leftVec midVec rightVec := by
  obtain ⟨hzero, hone, htwo⟩ := atomWedge_apply leftVec midVec
  simp only [dotProduct, Fin.sum_univ_three, hzero, hone, htwo]
  rw [tripleBracket_eq]
  ring

/-! ## 2. The adjugate of the `K4` Laplacian

The `K4` Laplacian is a signed atom sum over the six directions, so the general
adjugate law of `Gtz.Wave.WedgeBalanceAdjugate` applies with no work. -/

/-- **THE `K4` LAPLACIAN ADJUGATE IS THE HALVED PAIR WEDGE TOTAL.**  The general
rank-three law at an arbitrary signed measure, read on the six `K4` directions.
The edge weights may take either sign. -/
theorem adjugate_kFourLaplacian (edgeWeight : Fin 6 → ℝ) :
    (kFourLaplacian edgeWeight).adjugate
      = (2 : ℝ)⁻¹ • ∑ leftEdge, ∑ rightEdge, (edgeWeight leftEdge * edgeWeight rightEdge)
          • atomMatrix (atomWedge (kFourDirection leftEdge) (kFourDirection rightEdge)) := by
  rw [kFourLaplacian]
  exact adjugate_sum_smul_atomMatrix Finset.univ edgeWeight kFourDirection

/-! ## 3. The contraction tree polynomial, in closed form

The tree polynomial of an edge is the adjugate read at that edge's own direction.
Expanding the adjugate by the wedge law turns it into a quadratic form in the edge
weights whose matrix entries are the SQUARED BRACKETS of the two edges against
the reading edge. -/

/-- **THE TREE POLYNOMIAL IS A SQUARED-BRACKET QUADRATIC FORM.**  For any signed
edge weight and any edge,

  `P_edge(s) = (1/2) sum_c sum_d s_c s_d [g_c, g_d, g_edge]^2` .

The eight-term case definition of `Gtz.kFourContractionTreePolynomial` gives no
sign information.  This form gives all of it. -/
theorem kFourContractionTreePolynomial_eq_halfSum_sq_bracket (slack : Fin 6 → ℝ)
    (edge : Fin 6) :
    kFourContractionTreePolynomial slack edge
      = (2 : ℝ)⁻¹ * ∑ leftEdge, ∑ rightEdge, slack leftEdge * slack rightEdge
          * tripleBracket (kFourDirection leftEdge) (kFourDirection rightEdge)
              (kFourDirection edge) ^ 2 := by
  have hterm : ∀ leftEdge rightEdge : Fin 6,
      kFourDirection edge ⬝ᵥ (((slack leftEdge * slack rightEdge)
            • atomMatrix (atomWedge (kFourDirection leftEdge) (kFourDirection rightEdge)))
          *ᵥ kFourDirection edge)
        = slack leftEdge * slack rightEdge
          * tripleBracket (kFourDirection leftEdge) (kFourDirection rightEdge)
              (kFourDirection edge) ^ 2 := by
    intro leftEdge rightEdge
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      dotProduct_atomMatrix_mulVec_cross, atomWedge_dotProduct_eq_tripleBracket]
    ring
  rw [← dotProduct_adjugate_kFourDirection slack edge,
    adjugate_sum_smul_atomMatrix Finset.univ slack kFourDirection,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun leftEdge _ => ?_
  rw [Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun rightEdge _ => hterm leftEdge rightEdge

/-- **A NONNEGATIVE EDGE WEIGHT MAKES THE TREE POLYNOMIAL NONNEGATIVE.**  Every
term of the closed form is a product of two nonnegative weights and a square.  No
spanning hypothesis and no determinant. -/
theorem kFourContractionTreePolynomial_nonneg_of_nonneg (slack : Fin 6 → ℝ)
    (hnonneg : ∀ label : Fin 6, 0 ≤ slack label) (edge : Fin 6) :
    0 ≤ kFourContractionTreePolynomial slack edge := by
  rw [kFourContractionTreePolynomial_eq_halfSum_sq_bracket]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun leftEdge _ => ?_)
  refine Finset.sum_nonneg fun rightEdge _ => ?_
  exact mul_nonneg (mul_nonneg (hnonneg leftEdge) (hnonneg rightEdge)) (sq_nonneg _)

/-- The mass of a chart point is positive, so every mass tree polynomial is
nonnegative. -/
theorem kFourContractionTreePolynomial_mass_nonneg (point : DirectionChartPoint 6)
    (edge : Fin 6) : 0 ≤ kFourContractionTreePolynomial point.mass edge :=
  kFourContractionTreePolynomial_nonneg_of_nonneg point.mass
    (fun label => (point.mass_pos label).le) edge

/-! ## 4. The forest triple collapses under the deflated bound

`Gtz.posDef_directionChartGap_iff_forestTriple` needs three forest sums.  Under
the chart deflated bound the gap determinant alone decides strict domination, and
the determinant IS the third forest sum.  So the first two are free. -/

/-- **THE DEFLATED BOUND PAYS THE FIRST TWO FOREST SUMS.**  With the chart
deflated bound at any label, a positive signed tree sum forces the two adjugate
forest sums positive as well.  Three inequalities become one. -/
theorem kFour_forestTriple_of_chartDeflatedGapBound (point : DirectionChartPoint 6)
    (dropLabel : Fin 6) (selected : Finset (Fin 6))
    (hbound : ChartDeflatedGapBound kFourDirection point.mass point.weight dropLabel selected)
    (hforest : 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight selected)) :
    0 < ∑ label, signedGapWeight point.mass point.weight selected label
          * kFourContractionTreePolynomial point.mass label
      ∧ 0 < ∑ label, point.mass label
          * kFourContractionTreePolynomial
              (signedGapWeight point.mass point.weight selected) label := by
  have hweightNe : ∀ label ∈ selected, point.weight label ≠ 0 :=
    fun label _ => (point.weight_pos label).ne'
  have hdet : 0 < (directionChartGap kFourDirection point.mass point.weight selected).det := by
    rwa [det_directionChartGap_eq_kFourMassTreeSum point.mass point.weight selected hweightNe]
  have hposDef := (posDef_directionChartGap_kFour_iff_det_pos_of_chartDeflatedGapBound point
    dropLabel selected hbound).mpr hdet
  obtain ⟨hfirst, hsecond, -⟩ :=
    (posDef_directionChartGap_iff_forestTriple point selected).mp hposDef
  exact ⟨hfirst, hsecond⟩

/-- **THE PRODUCED TREE DECIDES ON ONE FOREST SUM.**  At every `K4` chart point
and every label the deflation returns a spanning tree avoiding that label on which
the complete three-forest criterion collapses to its third component alone.  No
matrix, no determinant and no positive definiteness survives in the statement. -/
theorem kFour_exists_tree_forestTriple_iff_massTreeSum (point : DirectionChartPoint 6)
    (dropLabel : Fin 6) :
    ∃ tree ∈ kFourSpanningTreeList, dropLabel ∉ tree ∧
      ((0 < ∑ label, signedGapWeight point.mass point.weight tree label
              * kFourContractionTreePolynomial point.mass label
          ∧ 0 < ∑ label, point.mass label
              * kFourContractionTreePolynomial
                  (signedGapWeight point.mass point.weight tree) label
          ∧ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree))
        ↔ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)) := by
  obtain ⟨tree, hmem, hnotMem, hbound, -⟩ := kFour_exists_chartDeflatedTree point dropLabel
  refine ⟨tree, hmem, hnotMem, ⟨fun htriple => htriple.2.2, fun hforest => ?_⟩⟩
  obtain ⟨hfirst, hsecond⟩ :=
    kFour_forestTriple_of_chartDeflatedGapBound point dropLabel tree hbound hforest
  exact ⟨hfirst, hsecond, hforest⟩

/-- **STRICT DOMINATION OF THE PRODUCED TREE IS ONE SIGNED TREE SUM.**  The same
statement read on the gap itself.  This is the sharpest form of the `K4`
deflation residual: one polynomial in the chart masses and weights. -/
theorem kFour_exists_tree_posDef_iff_massTreeSum (point : DirectionChartPoint 6)
    (dropLabel : Fin 6) :
    ∃ tree ∈ kFourSpanningTreeList, dropLabel ∉ tree ∧
      ((directionChartGap kFourDirection point.mass point.weight tree).PosDef
        ↔ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)) := by
  obtain ⟨tree, hmem, hnotMem, hbound, hiff⟩ := kFour_exists_chartDeflatedTree point dropLabel
  have hweightNe : ∀ label ∈ tree, point.weight label ≠ 0 :=
    fun label _ => (point.weight_pos label).ne'
  refine ⟨tree, hmem, hnotMem, ?_⟩
  rwa [det_directionChartGap_eq_kFourMassTreeSum point.mass point.weight tree hweightNe] at hiff

end Gtz
