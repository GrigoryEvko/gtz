import Gtz.Design.KFourChartClosure
import Gtz.Design.KFourBandAtlas
import Gtz.Reduction.DescentLadder
import Gtz.Ties.CorankOneTieCriterion
import Gtz.Quantitative.GeneralPositionWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The forced-edge law of the M(K4) chart

The chart gap of a subset is a difference of two graph Laplacians of `K4`, so the
whole class is an electrical-network statement.  Writing `a_c = m_c / w_c` for the
BOOSTED conductance and

    s_c = m_c / w_c - m_c = a_c (1 - w_c)                     (`Gtz.chartSlack`)

for the SLACK conductance, the chart gap has a complement form: it is the slack
Laplacian minus the boosted atoms OUTSIDE the selected set,

    directionChartGap dir m w S = L(s) - sum_{c not in S} a_c A_c .

Testing positive definiteness against the single probe `adj L(s) *v d_out` turns
that identity into a NECESSARY CONDITION on every label left out of a strictly
dominating set:

    a_out * (d_out . adj L(s) d_out)  <  det L(s) .

At the K4 chart both sides are landed polynomials -- the adjugate reading is
`Gtz.kFourContractionTreePolynomial` and the determinant is
`Gtz.kFourMassTreeSum`, both evaluated at the SLACK vector -- so the condition
reads

    a_out * Q_out(s)  <  T(s),

that is, `kappa_out := a_out * R_s(out) < 1` where `R_s` is the effective
resistance in the slack network.  Contrapositive: EVERY strictly dominating
subset CONTAINS every label whose boosted slack leverage reaches one.  This is a
selection with no argmax in it, so it is untouched by the campaign's refuted
per-label orderings, and it is a different network from the landed leverage edge
(`Gtz.IsMaxLeverageEdge`), which reads the MASS Laplacian.

Foster's theorem, already landed as the polynomial identity
`Gtz.kFourLeverage_sumIdentity`, caps the forced set: at the slack vector it says
`sum_c s_c Q_c(s) = 3 T(s)`, i.e. `sum_c kappa_c (1 - w_c) = 3`, so at most three
labels can be forced.  `Gtz.forcedStarWitnessPoint` shows the law is not vacuous
and that three labels really can be forced at once: there the law alone pins the
strictly dominating subset to `{3, 4, 5}` without evaluating a single candidate.

The module also records the SCALED master exchange identity, which is what a
spanning-tree exchange needs -- the landed `Gtz.det_mul_det_swapAtom` carries
unscaled atoms, and a tree exchange drops `a_u A_u` and inserts `a_v A_v`.
-/

namespace Gtz

open Matrix

/-! ## The scaled master exchange identity -/

/-- **The master identity with scalars.**  A spanning-tree exchange drops one
atom with a positive coefficient and inserts another with a positive
coefficient, so the two rank-one updates carry scalars.  No square root is
needed: the scalars pass through as a polynomial factor. -/
theorem det_mul_det_swapScaledAtom (form : Matrix (Fin 3) (Fin 3) ℝ)
    (droppedScale insertedScale : ℝ) (dropped inserted : Fin 3 → ℝ) :
    form.det
        * (form - droppedScale • atomMatrix dropped
            + insertedScale • atomMatrix inserted).det
      = (form - droppedScale • atomMatrix dropped).det
          * (form + insertedScale • atomMatrix inserted).det
        + droppedScale * insertedScale
            * ((dropped ⬝ᵥ (form.adjugate *ᵥ inserted))
              * (inserted ⬝ᵥ (form.adjugate *ᵥ dropped))) := by
  simp only [Matrix.det_fin_three, Matrix.adjugate_fin_three, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## The slack Laplacian and the complement form of the chart gap -/

/-- The SLACK conductance of a chart label: `s_c = m_c / w_c - m_c`. -/
noncomputable def chartSlack {size : ℕ} (mass weight : Fin size → ℝ)
    (label : Fin size) : ℝ :=
  mass label / weight label - mass label

theorem chartSlack_pos {size : ℕ} (mass weight : Fin size → ℝ) (label : Fin size)
    (hmass : 0 < mass label) (hweight : 0 < weight label)
    (hweightLt : weight label < 1) : 0 < chartSlack mass weight label := by
  have hdiv : mass label < mass label / weight label := by
    rw [lt_div_iff₀ hweight]
    nlinarith
  simpa [chartSlack] using sub_pos.mpr hdiv

/-- The SLACK LAPLACIAN of the chart: the graph Laplacian whose conductances are
the slacks. -/
noncomputable def slackLaplacian {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ label, chartSlack mass weight label • atomMatrix (direction label)

/-- **THE COMPLEMENT FORM OF THE CHART GAP**, read on the quadratic form: the
chart gap is the slack Laplacian less the boosted atoms outside the selected
set. -/
theorem dotProduct_directionChartGap_mulVec_eq_slack {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe)
      = probe ⬝ᵥ (slackLaplacian direction mass weight *ᵥ probe)
        - ∑ label ∈ selectedᶜ,
            (mass label / weight label) * (direction label ⬝ᵥ probe) ^ 2 := by
  classical
  have hsplit :
      ∑ label ∈ selected, (mass label / weight label) * (direction label ⬝ᵥ probe) ^ 2
        + ∑ label ∈ selectedᶜ,
            (mass label / weight label) * (direction label ⬝ᵥ probe) ^ 2
      = ∑ label, (mass label / weight label) * (direction label ⬝ᵥ probe) ^ 2 :=
    Finset.sum_add_sum_compl selected _
  have hgap : probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe)
      = (∑ label ∈ selected,
            (mass label / weight label) * (direction label ⬝ᵥ probe) ^ 2)
        - ∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2 := by
    rw [directionChartGap, Matrix.sub_mulVec, dotProduct_sub,
      dotProduct_sum_smul_atomMatrix_mulVec, dotProduct_sum_smul_atomMatrix_mulVec]
  have hslack : probe ⬝ᵥ (slackLaplacian direction mass weight *ᵥ probe)
      = ∑ label, chartSlack mass weight label * (direction label ⬝ᵥ probe) ^ 2 := by
    rw [slackLaplacian, dotProduct_sum_smul_atomMatrix_mulVec]
  have hchart : ∑ label, chartSlack mass weight label * (direction label ⬝ᵥ probe) ^ 2
      = (∑ label, (mass label / weight label) * (direction label ⬝ᵥ probe) ^ 2)
        - ∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by simp [chartSlack]; ring
  rw [hgap, hslack, hchart, ← hsplit]
  ring

/-! ## The probe inequality -/

/-- **The outside label is capped by the slack energy.**  If the chart gap of
`selected` is positive definite and `outside` is not selected, then at every
nonzero probe the outside label's boosted drop energy is strictly below the whole
slack energy. -/
theorem boostedOutside_lt_slackEnergy_of_posDef {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) (outside : Fin size) (houtside : outside ∉ selected)
    (hposDef : (directionChartGap direction mass weight selected).PosDef)
    (probe : Fin 3 → ℝ) (hprobe : probe ≠ 0) :
    (mass outside / weight outside) * (direction outside ⬝ᵥ probe) ^ 2
      < probe ⬝ᵥ (slackLaplacian direction mass weight *ᵥ probe) := by
  classical
  have hgapPos : 0 < probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe) := by
    have := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
    simpa using this
  rw [dotProduct_directionChartGap_mulVec_eq_slack] at hgapPos
  have hmem : outside ∈ selectedᶜ := Finset.mem_compl.mpr houtside
  have hsingle :
      (mass outside / weight outside) * (direction outside ⬝ᵥ probe) ^ 2
        ≤ ∑ label ∈ selectedᶜ,
            (mass label / weight label) * (direction label ⬝ᵥ probe) ^ 2 :=
    Finset.single_le_sum
      (f := fun label => (mass label / weight label) * (direction label ⬝ᵥ probe) ^ 2)
      (fun label _ =>
        mul_nonneg (le_of_lt (div_pos (hmass label) (hweight label))) (sq_nonneg _)) hmem
  linarith

/-- **THE FORCED-EDGE LAW, general form.**  Probe with the adjugate column of the
slack Laplacian: the boosted conductance of a label left outside a strictly
dominating set is capped by the reciprocal of its slack effective resistance. -/
theorem boostedConductance_mul_adjugateReading_lt_det_of_posDef {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) (outside : Fin size) (houtside : outside ∉ selected)
    (hposDef : (directionChartGap direction mass weight selected).PosDef)
    (hreading : 0 < direction outside ⬝ᵥ
        ((slackLaplacian direction mass weight).adjugate *ᵥ direction outside)) :
    (mass outside / weight outside)
        * (direction outside ⬝ᵥ
            ((slackLaplacian direction mass weight).adjugate *ᵥ direction outside))
      < (slackLaplacian direction mass weight).det := by
  classical
  set laplacian := slackLaplacian direction mass weight with hlaplacian
  set probe := laplacian.adjugate *ᵥ direction outside with hprobeDef
  set reading := direction outside ⬝ᵥ probe with hreadingDef
  have hprobeNe : probe ≠ 0 := by
    intro hzero
    rw [hreadingDef, hzero, dotProduct_zero] at hreading
    exact lt_irrefl 0 hreading
  have hdrop : direction outside ⬝ᵥ probe = reading := rfl
  have hEnergy : probe ⬝ᵥ (laplacian *ᵥ probe) = laplacian.det * reading := by
    have hmul : laplacian *ᵥ probe = laplacian.det • direction outside := by
      rw [hprobeDef, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [hmul, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  have hmain := boostedOutside_lt_slackEnergy_of_posDef direction mass weight hmass hweight
    selected outside houtside hposDef probe hprobeNe
  rw [hdrop, hEnergy] at hmain
  have hcancel : (mass outside / weight outside) * reading * reading
      < laplacian.det * reading := by nlinarith [hmain]
  exact lt_of_mul_lt_mul_right (by nlinarith [hcancel]) (le_of_lt hreading)

/-! ## The K4 instance: both sides are the landed tree polynomials -/

/-- The slack Laplacian of the K4 chart, entry by entry.  It is the reduced
Laplacian of `K4` grounded at the vertex `d` of the labelling
`0 = ab, 1 = ac, 2 = bc, 3 = ad, 4 = bd, 5 = cd`. -/
theorem sum_smul_atomMatrix_kFourDirection (slack : Fin 6 → ℝ) :
    (∑ label, slack label • atomMatrix (kFourDirection label))
      = Matrix.of ![![slack 0 + slack 1 + slack 3, -slack 0, -slack 1],
          ![-slack 0, slack 0 + slack 2 + slack 4, -slack 2],
          ![-slack 1, -slack 2, slack 1 + slack 2 + slack 5]] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Fin.sum_univ_six, atomMatrix, Matrix.vecMulVec_apply, kFourDirection,
      Matrix.sum_apply, Matrix.smul_apply]

/-- **Kirchhoff at the slack network.**  The determinant of the slack Laplacian
is the landed sixteen-term spanning-tree polynomial. -/
theorem det_sum_smul_atomMatrix_kFourDirection (slack : Fin 6 → ℝ) :
    (∑ label, slack label • atomMatrix (kFourDirection label)).det
      = kFourMassTreeSum slack := by
  rw [sum_smul_atomMatrix_kFourDirection, Matrix.det_fin_three]
  simp only [kFourMassTreeSum, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **The adjugate reading is the contraction polynomial.**  `d_e . adj L(s) d_e`
is the landed eight-term tree polynomial of `K4/e`, so the effective resistance
across the edge is `Q_e(s) / T(s)`. -/
theorem dotProduct_adjugate_kFourDirection (slack : Fin 6 → ℝ) (edge : Fin 6) :
    kFourDirection edge ⬝ᵥ
        ((∑ label, slack label • atomMatrix (kFourDirection label)).adjugate
          *ᵥ kFourDirection edge)
      = kFourContractionTreePolynomial slack edge := by
  rw [sum_smul_atomMatrix_kFourDirection]
  fin_cases edge <;>
    simp [Matrix.adjugate_fin_three, kFourDirection, dotProduct, Matrix.mulVec,
      Fin.sum_univ_three, kFourContractionTreePolynomial] <;> ring

/-- The contraction polynomial is positive at positive conductances. -/
theorem kFourContractionTreePolynomial_pos (slack : Fin 6 → ℝ)
    (hpos : ∀ label, 0 < slack label) (edge : Fin 6) :
    0 < kFourContractionTreePolynomial slack edge := by
  have hzero := hpos 0
  have hone := hpos 1
  have htwo := hpos 2
  have hthree := hpos 3
  have hfour := hpos 4
  have hfive := hpos 5
  fin_cases edge <;>
    simp only [kFourContractionTreePolynomial] <;>
    positivity

/-- Six positive weights summing to one leave every one of them below one. -/
theorem chartPoint_weight_lt_one (point : DirectionChartPoint 6) (label : Fin 6) :
    point.weight label < 1 := by
  classical
  have hsplit : point.weight label
      + ∑ other ∈ Finset.univ.erase label, point.weight other = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ label)]
    exact point.weight_sum_one
  have hnonempty : (Finset.univ.erase label).Nonempty := by
    refine Finset.card_pos.mp ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ label), Finset.card_univ,
      Fintype.card_fin]
    norm_num
  have hrest : 0 < ∑ other ∈ Finset.univ.erase label, point.weight other :=
    Finset.sum_pos (fun other _ => point.weight_pos other) hnonempty
  linarith

theorem chartSlack_pos_of_chartPoint (point : DirectionChartPoint 6) (label : Fin 6) :
    0 < chartSlack point.mass point.weight label :=
  chartSlack_pos point.mass point.weight label (point.mass_pos label)
    (point.weight_pos label) (chartPoint_weight_lt_one point label)

/-- **THE FORCED-EDGE LAW AT THE K4 CHART.**  If some subset omitting `outside`
has a strictly dominating chart gap, then the boosted slack leverage of
`outside` is strictly below one:

    (m_out / w_out) * Q_out(s)  <  T(s),   s = chartSlack.

Both polynomials are the landed ones, evaluated at the SLACK vector; the ratio
`Q_out(s) / T(s)` is the effective resistance across `out` in the slack
network. -/
theorem kFourBoostedSlackLeverage_lt_of_posDef (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (outside : Fin 6) (houtside : outside ∉ selected)
    (hposDef : (directionChartGap kFourDirection point.mass point.weight selected).PosDef) :
    point.mass outside / point.weight outside
        * kFourContractionTreePolynomial (chartSlack point.mass point.weight) outside
      < kFourMassTreeSum (chartSlack point.mass point.weight) := by
  have hreading : 0 < kFourDirection outside ⬝ᵥ
      ((slackLaplacian kFourDirection point.mass point.weight).adjugate
        *ᵥ kFourDirection outside) := by
    simp only [slackLaplacian]
    rw [dotProduct_adjugate_kFourDirection]
    exact kFourContractionTreePolynomial_pos _ (chartSlack_pos_of_chartPoint point) outside
  have hmain := boostedConductance_mul_adjugateReading_lt_det_of_posDef
    kFourDirection point.mass point.weight point.mass_pos point.weight_pos
    selected outside houtside hposDef hreading
  simp only [slackLaplacian] at hmain
  rw [dotProduct_adjugate_kFourDirection, det_sum_smul_atomMatrix_kFourDirection] at hmain
  exact hmain

/-- **Contrapositive: the forced edge is inside every strictly dominating set.** -/
theorem kFourForcedEdge_mem_of_posDef (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (outside : Fin 6)
    (hposDef : (directionChartGap kFourDirection point.mass point.weight selected).PosDef)
    (hforced : kFourMassTreeSum (chartSlack point.mass point.weight)
      ≤ point.mass outside / point.weight outside
        * kFourContractionTreePolynomial (chartSlack point.mass point.weight) outside) :
    outside ∈ selected := by
  by_contra hnot
  exact absurd (kFourBoostedSlackLeverage_lt_of_posDef point selected outside hnot hposDef)
    (not_lt.mpr hforced)

/-! ## The law is not vacuous: a chart point with a fully forced tree -/

/-- Masses of the forced-star witness. -/
noncomputable def forcedStarWitnessMass : Fin 6 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 10
  | 4 => 10
  | 5 => 10

/-- Weights of the forced-star witness. -/
noncomputable def forcedStarWitnessWeight : Fin 6 → ℝ
  | 0 => 3 / 10
  | 1 => 3 / 10
  | 2 => 3 / 10
  | 3 => 1 / 30
  | 4 => 1 / 30
  | 5 => 1 / 30

/-- **A chart point at which the forced-edge law alone selects the tree.**  The
slacks are `7/3` on the triangle `{0,1,2}` and `290` on the star `{3,4,5}`, so
each star edge has boosted slack leverage `8770/8613 > 1` and each triangle edge
only `20/891`. -/
noncomputable def forcedStarWitnessPoint : DirectionChartPoint 6 where
  mass := forcedStarWitnessMass
  weight := forcedStarWitnessWeight
  mass_pos := by intro label; fin_cases label <;> norm_num [forcedStarWitnessMass]
  weight_pos := by intro label; fin_cases label <;> norm_num [forcedStarWitnessWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [forcedStarWitnessWeight]

theorem forcedStarWitnessPoint_mass : forcedStarWitnessPoint.mass = forcedStarWitnessMass := rfl

theorem forcedStarWitnessPoint_weight :
    forcedStarWitnessPoint.weight = forcedStarWitnessWeight := rfl

theorem forcedStarWitness_forces (edge : Fin 6) (hedge : edge = 3 ∨ edge = 4 ∨ edge = 5) :
    kFourMassTreeSum (chartSlack forcedStarWitnessMass forcedStarWitnessWeight)
      ≤ forcedStarWitnessMass edge / forcedStarWitnessWeight edge
        * kFourContractionTreePolynomial
            (chartSlack forcedStarWitnessMass forcedStarWitnessWeight) edge := by
  rcases hedge with rfl | rfl | rfl <;>
    norm_num [kFourMassTreeSum, kFourContractionTreePolynomial_three,
      kFourContractionTreePolynomial_four, kFourContractionTreePolynomial_five,
      chartSlack, forcedStarWitnessMass, forcedStarWitnessWeight]

/-- **The forced-edge law alone pins the strictly dominating triple.**  At the
witness no candidate determinant is evaluated: the three star edges are forced,
and a three-element set containing them IS the star. -/
theorem forcedStarWitness_posDef_cardThree_eq (selected : Finset (Fin 6))
    (hcard : selected.card = 3)
    (hposDef : (directionChartGap kFourDirection forcedStarWitnessPoint.mass
      forcedStarWitnessPoint.weight selected).PosDef) :
    selected = {3, 4, 5} := by
  have hthree := kFourForcedEdge_mem_of_posDef forcedStarWitnessPoint selected 3 hposDef
    (forcedStarWitness_forces 3 (Or.inl rfl))
  have hfour := kFourForcedEdge_mem_of_posDef forcedStarWitnessPoint selected 4 hposDef
    (forcedStarWitness_forces 4 (Or.inr (Or.inl rfl)))
  have hfive := kFourForcedEdge_mem_of_posDef forcedStarWitnessPoint selected 5 hposDef
    (forcedStarWitness_forces 5 (Or.inr (Or.inr rfl)))
  have hsubset : ({3, 4, 5} : Finset (Fin 6)) ⊆ selected := by
    intro label hlabel
    fin_cases hlabel
    · exact hthree
    · exact hfour
    · exact hfive
  exact (Finset.eq_of_subset_of_card_le hsubset (by rw [hcard]; decide)).symm

/-! ## The same law at the design level: the FORCED-ATOM LAW

The chart argument used nothing about `kFourDirection`.  At a weighted design the
complement form is the landed insider/outsider split with the two coefficients
recombined -- `(1 - t_c) + t_c = 1` -- so the reference form is the FULL-SET gap
`subsetSum D univ - 1 = sum_c (1 - t_c) g_c g_c^T`, and the same single probe
gives a necessary condition on every atom left outside a strictly dominating
subset, at every size and every rank.
-/

/-- **THE FORCED-ATOM LAW.**  If some subset omitting the atom `outside` is
strictly dominating, then the atom's reading against the adjugate of the FULL-SET
gap is strictly below that gap's determinant.  Dividing by the determinant, the
reading of `g_out` against `(sum_c (1 - t_c) g_c g_c^T)^{-1}` is strictly below
one.

Nothing here is special to rank three or to the K4 chart: this is the
design-level twin of `Gtz.kFourBoostedSlackLeverage_lt_of_posDef`, obtained from
the landed insider/outsider split by recombining `(1 - t_c) + t_c = 1` and
probing with one adjugate column. -/
theorem dotProduct_adjugate_univGap_lt_det_of_posDef {size rank : ℕ}
    (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (selected : Finset (Fin size)) (outside : Fin size) (houtside : outside ∉ selected)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    design.atom outside ⬝ᵥ
        ((subsetSum design Finset.univ - 1).adjugate *ᵥ design.atom outside)
      < (subsetSum design Finset.univ - 1).det := by
  classical
  have hfullPosDef : (subsetSum design Finset.univ - 1).PosDef :=
    posDef_subsetSum_univ_sub_one design hsize
  have hdetPos : 0 < (subsetSum design Finset.univ - 1).det := hfullPosDef.det_pos
  by_cases hatomZero : design.atom outside = 0
  · rw [hatomZero, zero_dotProduct]
    exact hdetPos
  have hadjugate : (subsetSum design Finset.univ - 1).adjugate
      = (subsetSum design Finset.univ - 1).det • (subsetSum design Finset.univ - 1)⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv',
      mul_inv_cancel₀ (ne_of_gt hdetPos), one_smul]
  have hinvPos : 0 < design.atom outside ⬝ᵥ
      ((subsetSum design Finset.univ - 1)⁻¹ *ᵥ design.atom outside) := by
    have := (Matrix.posDef_iff_dotProduct_mulVec.mp hfullPosDef.inv).2 hatomZero
    simpa using this
  have hreadingPos : 0 < design.atom outside ⬝ᵥ
      ((subsetSum design Finset.univ - 1).adjugate *ᵥ design.atom outside) := by
    rw [hadjugate, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_pos hdetPos hinvPos
  set probe := (subsetSum design Finset.univ - 1).adjugate *ᵥ design.atom outside
    with hprobeDef
  have hprobeNe : probe ≠ 0 := by
    intro hzeroVec
    rw [hzeroVec, dotProduct_zero] at hreadingPos
    exact lt_irrefl 0 hreadingPos
  have hcomplement :
      probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe)
        = probe ⬝ᵥ ((subsetSum design Finset.univ - 1) *ᵥ probe)
          - ∑ label ∈ selectedᶜ, (design.atom label ⬝ᵥ probe) ^ 2 := by
    rw [dotProduct_subsetSum_sub_one_mulVec, dotProduct_subsetSum_sub_one_mulVec]
    simp only [Finset.compl_univ, Finset.sum_empty, sub_zero]
    have hsplit := Finset.sum_add_sum_compl selected
      (fun label => (1 - design.weight label) * (design.atom label ⬝ᵥ probe) ^ 2)
    have houtsideSum : ∑ label ∈ selectedᶜ,
          design.weight label * (design.atom label ⬝ᵥ probe) ^ 2
        = (∑ label ∈ selectedᶜ, (design.atom label ⬝ᵥ probe) ^ 2)
          - ∑ label ∈ selectedᶜ,
              (1 - design.weight label) * (design.atom label ⬝ᵥ probe) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun label _ => by ring
    rw [houtsideSum]
    linarith [hsplit]
  have hgapPos : 0 < probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) := by
    have := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobeNe
    simpa using this
  rw [hcomplement] at hgapPos
  have hsingle : (design.atom outside ⬝ᵥ probe) ^ 2
      ≤ ∑ label ∈ selectedᶜ, (design.atom label ⬝ᵥ probe) ^ 2 :=
    Finset.single_le_sum (f := fun label => (design.atom label ⬝ᵥ probe) ^ 2)
      (fun label _ => sq_nonneg _) (Finset.mem_compl.mpr houtside)
  have hEnergy : probe ⬝ᵥ ((subsetSum design Finset.univ - 1) *ᵥ probe)
      = (subsetSum design Finset.univ - 1).det * (design.atom outside ⬝ᵥ probe) := by
    have hmul : (subsetSum design Finset.univ - 1) *ᵥ probe
        = (subsetSum design Finset.univ - 1).det • design.atom outside := by
      rw [hprobeDef, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [hmul, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  rw [hEnergy] at hgapPos
  have hpos : 0 < design.atom outside ⬝ᵥ probe := hreadingPos
  nlinarith [hgapPos, hsingle, hpos]

/-!
## PART II -- THE DESCENT LADDER

The forced-edge law above is the TOP RUNG of a ladder the tree already owns at
the design level, and the merge below is what makes that visible.

Three landed facts do the work.  `Gtz.posDef_fullExcess` says the gap of the FULL
atom set is positive definite; `Gtz.erase_strictDominates_iff_pivot_lt_one` says
that from a positive definite base, erasing one label stays positive definite
exactly when that label's `Gtz.pivot` is below one; and `Gtz.descent_identity`
says the co-weighted pivots against the full set total the rank, so the smallest
is at most `k/(m-1)` -- `3/5` at `(6,3)`, attained at the octahedron, which is
the same `3/5` the K4 chart shows at every edge of `Gtz.tetrahedronChartPoint`.
The missing ingredient was never the rung: it was STRICT MONOTONICITY, which the
tree carries only in its weak form (`Gtz.Dominates.mono`).  Supplying it turns
the landed equivalence into a ladder in one line, on both sides of the chart.

What that buys, concretely:

* `Gtz.pivot_univ_lt_one_of_posDef_of_notMem` is the design-level forced-atom law
  of Part I derived from the landed EQUIVALENCE instead of from an adjugate
  probe.  Same statement, two lines, and the landed form is sharper because it
  is an iff.
* `Gtz.posDef_directionChartGap_erase_iff` upgrades the chart-level law from a
  one-way implication to an EQUIVALENCE, which is what makes the ladder a
  decision procedure rather than a filter.
* Because the positive definite subsets form an UP-SET, the rung applies at every
  level, not only at the top.  Rung one -- omit a single label -- is the
  forced-edge law.  Rung two -- omit a PAIR -- is strictly stronger, and it is
  the rung that bites: at `Gtz.bandResidualWitnessPoint`, the canonical
  inhabitant of the residual band, rung one is EMPTY (every `kappa` is below one,
  the largest being `249760/251541`) while rung two pins the strictly dominating
  trees EXACTLY, and both facts are kernel-checked below.

The ladder's own wall is documented where it belongs, in
`Gtz/Reduction/DescentLadder.lean`: the trace identity at a general base carries
an OUTSIDER term, so the counting bound that supplies descent moves is sharp only
at the top rung, and the last rung -- getting from a positive definite
`(k+1)`-set to a `k`-set -- is exactly where a pivot can sit at one.  At every
landed tie fixture it does: at `Gtz.tetraDesign` and
`Gtz.nonUniformLeverageTieDesign` every insider pivot of every positive definite
four-set is EXACTLY one, and at `Gtz.splitTetraDesign` two of the four are.  The
ladder therefore refuses at a tie by an exact equality and never by a margin,
which is the strongest form the soundness gate can take.
-/

/-! ### Strict monotonicity: the strictly dominating subsets form an up-set -/

/-- **Strict monotonicity of domination.**  The strict twin of the landed
`Gtz.Dominates.mono`: enlarging a strictly dominating subset keeps it strictly
dominating, because the added atoms contribute positive semidefinite rank-ones.
The tree carries the weak form only. -/
theorem posDef_subsetSum_sub_one_of_subset {size rank : ℕ} {design : WeightedDesign size rank}
    {selected larger : Finset (Fin size)} (hsubset : selected ⊆ larger)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    (subsetSum design larger - 1).PosDef := by
  have hsplit : subsetSum design larger - 1
      = (subsetSum design selected - 1)
        + ∑ label ∈ larger \ selected, atomMatrix (design.atom label) := by
    unfold subsetSum
    rw [← Finset.sum_sdiff hsubset]
    abel
  rw [hsplit]
  exact hposDef.add_posSemidef
    (Matrix.posSemidef_sum (larger \ selected)
      fun label _ => posSemidef_atomMatrix (design.atom label))

/-- **The forced-atom law, from the landed equivalence.**  Two lines: monotonicity
lifts a strictly dominating subset to the co-singleton of any label it omits, and
`Gtz.erase_strictDominates_iff_pivot_lt_one` reads that co-singleton off as a
pivot below one.  This is `Gtz.dotProduct_adjugate_univGap_lt_det_of_posDef` of
Part I in the tree's own `Gtz.pivot` vocabulary, and the landed input is an IFF,
so nothing is lost on the way. -/
theorem pivot_univ_lt_one_of_posDef_of_notMem {size rank : ℕ}
    (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    {selected : Finset (Fin size)} (hposDef : (subsetSum design selected - 1).PosDef)
    {outside : Fin size} (houtside : outside ∉ selected) :
    pivot design Finset.univ outside < 1 := by
  refine (erase_strictDominates_iff_pivot_lt_one design Finset.univ
    (posDef_fullExcess design hsize) (Finset.mem_univ outside)).mp ?_
  refine posDef_subsetSum_sub_one_of_subset (fun label hlabel => ?_) hposDef
  exact Finset.mem_erase.mpr ⟨fun heq => houtside (heq ▸ hlabel), Finset.mem_univ label⟩

/-! ### The scaled rank-one Schur step -/

/-- **The rank-one Schur step with a scalar in front.**  The landed
`Gtz.posDef_sub_vecMulVec_iff` subtracts an UNSCALED rank-one; a chart erasure
subtracts `(m/w)` times one, and absorbing that factor into the vector would need
a square root.  The statement below is square-root free -- the root appears only
inside the proof -- so the chart ladder never leaves the rationals. -/
theorem posDef_sub_smul_vecMulVec_iff {rank : ℕ} {form : Matrix (Fin rank) (Fin rank) ℝ}
    (hform : form.PosDef) {scale : ℝ} (hscale : 0 < scale) (probe : Fin rank → ℝ) :
    (form - scale • Matrix.vecMulVec probe probe).PosDef
      ↔ scale * (probe ⬝ᵥ form⁻¹ *ᵥ probe) < 1 := by
  have hroot : Real.sqrt scale * Real.sqrt scale = scale := Real.mul_self_sqrt hscale.le
  have hmat : scale • Matrix.vecMulVec probe probe
      = Matrix.vecMulVec (Real.sqrt scale • probe) (Real.sqrt scale • probe) := by
    ext rowIndex colIndex
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(probe rowIndex * probe colIndex)) * hroot
  have hdot : (Real.sqrt scale • probe) ⬝ᵥ form⁻¹ *ᵥ (Real.sqrt scale • probe)
      = scale * (probe ⬝ᵥ form⁻¹ *ᵥ probe) := by
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, hroot]
  rw [hmat, posDef_sub_vecMulVec_iff form hform, hdot]

/-! ### The chart ladder -/

/-- Erasing a label from the selected set subtracts its boosted atom. -/
theorem directionChartGap_erase {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (base : Finset (Fin size)) {label : Fin size}
    (hmem : label ∈ base) :
    directionChartGap direction mass weight (base.erase label)
      = directionChartGap direction mass weight base
        - (mass label / weight label) • atomMatrix (direction label) := by
  unfold directionChartGap
  rw [← Finset.sum_erase_add base _ hmem]
  abel

/-- **Strict monotonicity on the chart.**  The chart twin of
`Gtz.posDef_subsetSum_sub_one_of_subset`: the positive definite subsets of a
direction chart form an up-set. -/
theorem posDef_directionChartGap_of_subset {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label)
    {selected larger : Finset (Fin size)} (hsubset : selected ⊆ larger)
    (hposDef : (directionChartGap direction mass weight selected).PosDef) :
    (directionChartGap direction mass weight larger).PosDef := by
  have hsplit : directionChartGap direction mass weight larger
      = directionChartGap direction mass weight selected
        + ∑ label ∈ larger \ selected,
            (mass label / weight label) • atomMatrix (direction label) := by
    unfold directionChartGap
    rw [← Finset.sum_sdiff hsubset]
    abel
  rw [hsplit]
  refine hposDef.add_posSemidef (Matrix.posSemidef_sum _ fun label _ => ?_)
  exact (posSemidef_atomMatrix (direction label)).smul
    (div_pos (hmass label) (hweight label)).le

/-- The chart's own pivot: the boosted conductance read against the inverse of the
gap at the CURRENT base.  At `base = Finset.univ` this is the `kappa` of Part I. -/
noncomputable def chartLadderPivot {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (base : Finset (Fin size)) (label : Fin size) : ℝ :=
  (mass label / weight label)
    * (direction label ⬝ᵥ (directionChartGap direction mass weight base)⁻¹
        *ᵥ direction label)

/-- **THE CHART LADDER RUNG, AS AN EQUIVALENCE.**  From a positive definite base,
erasing a label keeps positive definiteness exactly when that label's chart pivot
is below one.  The chart transport of `Gtz.erase_strictDominates_iff_pivot_lt_one`,
and the strengthening of the forced-edge law of Part I from an implication to an
iff. -/
theorem posDef_directionChartGap_erase_iff {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label) (base : Finset (Fin size)) {label : Fin size}
    (hmem : label ∈ base)
    (hbase : (directionChartGap direction mass weight base).PosDef) :
    (directionChartGap direction mass weight (base.erase label)).PosDef
      ↔ chartLadderPivot direction mass weight base label < 1 := by
  rw [directionChartGap_erase direction mass weight base hmem]
  have hatom : atomMatrix (direction label)
      = Matrix.vecMulVec (direction label) (direction label) := rfl
  rw [hatom, posDef_sub_smul_vecMulVec_iff hbase (div_pos (hmass label) (hweight label))]
  rfl

/-- **The ladder at every rung.**  A strictly dominating subset forces the chart
pivot of every label it omits to stay below one -- against ANY positive definite
base that contains the subset and the label.  Rung one takes the base to be the
whole edge set and recovers the forced-edge law of Part I; rung two takes a base
of five labels and is strictly stronger. -/
theorem chartLadderPivot_lt_one_of_posDef_of_notMem {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) {label : Fin size} (hmem : label ∈ base)
    (hbase : (directionChartGap direction mass weight base).PosDef)
    {selected : Finset (Fin size)} (hsubset : selected ⊆ base.erase label)
    (hposDef : (directionChartGap direction mass weight selected).PosDef) :
    chartLadderPivot direction mass weight base label < 1 :=
  (posDef_directionChartGap_erase_iff direction mass weight hmass hweight base hmem hbase).mp
    (posDef_directionChartGap_of_subset direction mass weight hmass hweight hsubset hposDef)

/-! ### The top of the ladder at K4 -/

/-- At the full edge set the chart gap IS the slack Laplacian. -/
theorem directionChartGap_univ_eq_slackLaplacian {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ) :
    directionChartGap direction mass weight Finset.univ
      = slackLaplacian direction mass weight := by
  unfold directionChartGap slackLaplacian chartSlack
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun label _ => (sub_smul _ _ _).symm

/-- **THE TOP OF THE LADDER IS ALWAYS OCCUPIED.**  The full-edge-set chart gap of
any K4 chart point is positive definite: it is a Laplacian of strictly positive
slack conductances, so it is positive semidefinite with determinant the strictly
positive matrix-tree sum.  Every descent starts here, so the ladder is never
vacuous. -/
theorem posDef_directionChartGap_univ_kFour (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight Finset.univ).PosDef := by
  have hsemidef :
      (directionChartGap kFourDirection point.mass point.weight Finset.univ).PosSemidef := by
    rw [directionChartGap_univ_eq_slackLaplacian, slackLaplacian]
    exact Matrix.posSemidef_sum _ fun label _ =>
      (posSemidef_atomMatrix (kFourDirection label)).smul
        (chartSlack_pos_of_chartPoint point label).le
  refine (Matrix.PosSemidef.posDef_iff_det_ne_zero hsemidef).mpr ?_
  rw [directionChartGap_univ_eq_slackLaplacian, slackLaplacian,
    det_sum_smul_atomMatrix_kFourDirection]
  exact ne_of_gt (kFourMassTreeSum_pos _ fun label => chartSlack_pos_of_chartPoint point label)

/-! ### The total mass never exceeds the largest boosted conductance -/

/-- **The mass bound.**  Since the weights are a probability vector, the total
mass is a weighted average of the boosted conductances and so never exceeds the
largest of them.  This is the load-bearing half of the max-conductance pruning
observation: for a subset containing a maximising label, the summed conductance
already beats the total mass. -/
theorem sum_mass_le_boostedConductance {size : ℕ} (mass weight : Fin size → ℝ)
    (hweight : ∀ label, 0 < weight label) (hsum : ∑ label, weight label = 1)
    (top : Fin size)
    (hmax : ∀ label, mass label / weight label ≤ mass top / weight top) :
    ∑ label, mass label ≤ mass top / weight top := by
  calc ∑ label, mass label
      = ∑ label, weight label * (mass label / weight label) := by
        refine Finset.sum_congr rfl fun label _ => ?_
        have hne : weight label ≠ 0 := ne_of_gt (hweight label)
        rw [mul_div_assoc', mul_comm (weight label) (mass label), mul_div_assoc,
          div_self hne, mul_one]
    _ ≤ ∑ label, weight label * (mass top / weight top) :=
        Finset.sum_le_sum fun label _ =>
          mul_le_mul_of_nonneg_left (hmax label) (hweight label).le
    _ = mass top / weight top := by rw [← Finset.sum_mul, hsum, one_mul]

/-! ### Rung two fires on the residual band, where rung one is empty

At `Gtz.bandResidualWitnessPoint` every `kappa` is strictly below one, so the
forced-edge law of Part I prunes nothing at all.  Five of the fifteen PAIRS have
a non-positive-definite four-set complement, and by strict monotonicity each of
them is a clause on the strictly dominating trees.  The five clauses together
pin the strictly dominating trees exactly. -/

theorem bandWitness_gap_twoThreeFourFive_det_neg :
    (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight {2, 3, 4, 5}).det < 0 := by
  simp only [directionChartGap, bandResidualWitnessPoint_mass_eq,
    bandResidualWitnessPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [bandResidualWitnessMass, bandResidualWitnessWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem bandWitness_gap_zeroThreeFourFive_det_neg :
    (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight {0, 3, 4, 5}).det < 0 := by
  simp only [directionChartGap, bandResidualWitnessPoint_mass_eq,
    bandResidualWitnessPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [bandResidualWitnessMass, bandResidualWitnessWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem bandWitness_gap_zeroTwoFourFive_det_neg :
    (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight {0, 2, 4, 5}).det < 0 := by
  simp only [directionChartGap, bandResidualWitnessPoint_mass_eq,
    bandResidualWitnessPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [bandResidualWitnessMass, bandResidualWitnessWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem bandWitness_gap_zeroTwoThreeFour_det_neg :
    (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight {0, 2, 3, 4}).det < 0 := by
  simp only [directionChartGap, bandResidualWitnessPoint_mass_eq,
    bandResidualWitnessPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [bandResidualWitnessMass, bandResidualWitnessWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem bandWitness_gap_zeroOneTwoFour_det_neg :
    (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight {0, 1, 2, 4}).det < 0 := by
  simp only [directionChartGap, bandResidualWitnessPoint_mass_eq,
    bandResidualWitnessPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [bandResidualWitnessMass, bandResidualWitnessWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- **A forced-pair clause.**  Every strictly dominating subset of the band
witness meets `{0, 1}`: a subset avoiding both would sit inside `{2,3,4,5}`, whose
gap has negative determinant. -/
theorem bandWitness_posDef_meets_zeroOne (tree : Finset (Fin 6))
    (hposDef : (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight tree).PosDef) :
    (0 : Fin 6) ∈ tree ∨ (1 : Fin 6) ∈ tree := by
  by_contra hcontra
  obtain ⟨hzero, hone⟩ := not_or.mp hcontra
  have hsubset : tree ⊆ ({2, 3, 4, 5} : Finset (Fin 6)) := by
    intro label hlabel
    have hne0 : label ≠ 0 := fun heq => hzero (heq ▸ hlabel)
    have hne1 : label ≠ 1 := fun heq => hone (heq ▸ hlabel)
    revert hne0 hne1
    fin_cases label <;> decide
  exact absurd (posDef_directionChartGap_of_subset kFourDirection _ _
      bandResidualWitnessPoint.mass_pos bandResidualWitnessPoint.weight_pos
      hsubset hposDef).det_pos (not_lt.mpr bandWitness_gap_twoThreeFourFive_det_neg.le)

theorem bandWitness_posDef_meets_oneTwo (tree : Finset (Fin 6))
    (hposDef : (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight tree).PosDef) :
    (1 : Fin 6) ∈ tree ∨ (2 : Fin 6) ∈ tree := by
  by_contra hcontra
  obtain ⟨hone, htwo⟩ := not_or.mp hcontra
  have hsubset : tree ⊆ ({0, 3, 4, 5} : Finset (Fin 6)) := by
    intro label hlabel
    have hne1 : label ≠ 1 := fun heq => hone (heq ▸ hlabel)
    have hne2 : label ≠ 2 := fun heq => htwo (heq ▸ hlabel)
    revert hne1 hne2
    fin_cases label <;> decide
  exact absurd (posDef_directionChartGap_of_subset kFourDirection _ _
      bandResidualWitnessPoint.mass_pos bandResidualWitnessPoint.weight_pos
      hsubset hposDef).det_pos (not_lt.mpr bandWitness_gap_zeroThreeFourFive_det_neg.le)

theorem bandWitness_posDef_meets_oneThree (tree : Finset (Fin 6))
    (hposDef : (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight tree).PosDef) :
    (1 : Fin 6) ∈ tree ∨ (3 : Fin 6) ∈ tree := by
  by_contra hcontra
  obtain ⟨hone, hthree⟩ := not_or.mp hcontra
  have hsubset : tree ⊆ ({0, 2, 4, 5} : Finset (Fin 6)) := by
    intro label hlabel
    have hne1 : label ≠ 1 := fun heq => hone (heq ▸ hlabel)
    have hne3 : label ≠ 3 := fun heq => hthree (heq ▸ hlabel)
    revert hne1 hne3
    fin_cases label <;> decide
  exact absurd (posDef_directionChartGap_of_subset kFourDirection _ _
      bandResidualWitnessPoint.mass_pos bandResidualWitnessPoint.weight_pos
      hsubset hposDef).det_pos (not_lt.mpr bandWitness_gap_zeroTwoFourFive_det_neg.le)

theorem bandWitness_posDef_meets_oneFive (tree : Finset (Fin 6))
    (hposDef : (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight tree).PosDef) :
    (1 : Fin 6) ∈ tree ∨ (5 : Fin 6) ∈ tree := by
  by_contra hcontra
  obtain ⟨hone, hfive⟩ := not_or.mp hcontra
  have hsubset : tree ⊆ ({0, 2, 3, 4} : Finset (Fin 6)) := by
    intro label hlabel
    have hne1 : label ≠ 1 := fun heq => hone (heq ▸ hlabel)
    have hne5 : label ≠ 5 := fun heq => hfive (heq ▸ hlabel)
    revert hne1 hne5
    fin_cases label <;> decide
  exact absurd (posDef_directionChartGap_of_subset kFourDirection _ _
      bandResidualWitnessPoint.mass_pos bandResidualWitnessPoint.weight_pos
      hsubset hposDef).det_pos (not_lt.mpr bandWitness_gap_zeroTwoThreeFour_det_neg.le)

theorem bandWitness_posDef_meets_threeFive (tree : Finset (Fin 6))
    (hposDef : (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight tree).PosDef) :
    (3 : Fin 6) ∈ tree ∨ (5 : Fin 6) ∈ tree := by
  by_contra hcontra
  obtain ⟨hthree, hfive⟩ := not_or.mp hcontra
  have hsubset : tree ⊆ ({0, 1, 2, 4} : Finset (Fin 6)) := by
    intro label hlabel
    have hne3 : label ≠ 3 := fun heq => hthree (heq ▸ hlabel)
    have hne5 : label ≠ 5 := fun heq => hfive (heq ▸ hlabel)
    revert hne3 hne5
    fin_cases label <;> decide
  exact absurd (posDef_directionChartGap_of_subset kFourDirection _ _
      bandResidualWitnessPoint.mass_pos bandResidualWitnessPoint.weight_pos
      hsubset hposDef).det_pos (not_lt.mpr bandWitness_gap_zeroOneTwoFour_det_neg.le)

/-- The combinatorial half: the five clauses cut the sixteen spanning trees to six. -/
theorem kFourTrees_meeting_bandDeadPairs :
    ∀ tree ∈ kFourSpanningTreeList,
      ((0 : Fin 6) ∈ tree ∨ (1 : Fin 6) ∈ tree) →
      ((1 : Fin 6) ∈ tree ∨ (2 : Fin 6) ∈ tree) →
      ((1 : Fin 6) ∈ tree ∨ (3 : Fin 6) ∈ tree) →
      ((1 : Fin 6) ∈ tree ∨ (5 : Fin 6) ∈ tree) →
      ((3 : Fin 6) ∈ tree ∨ (5 : Fin 6) ∈ tree) →
      tree = {0, 1, 3} ∨ tree = {1, 2, 5} ∨ tree = {0, 1, 5} ∨
        tree = {1, 2, 3} ∨ tree = {1, 3, 4} ∨ tree = {1, 4, 5} := by decide

/-- **RUNG TWO IS EXACT AT THE BAND WITNESS.**  Rung one is empty there -- every
`kappa` is strictly below one -- yet the five forced-pair clauses already pin the
strictly dominating spanning trees to a list of six, and all six really are
strictly dominating.  This is the residual band's canonical inhabitant, so it is
exactly where a pruning law has to work. -/
theorem bandWitness_posDef_tree_mem (tree : Finset (Fin 6))
    (hmem : tree ∈ kFourSpanningTreeList)
    (hposDef : (directionChartGap kFourDirection bandResidualWitnessPoint.mass
      bandResidualWitnessPoint.weight tree).PosDef) :
    tree = {0, 1, 3} ∨ tree = {1, 2, 5} ∨ tree = {0, 1, 5} ∨
      tree = {1, 2, 3} ∨ tree = {1, 3, 4} ∨ tree = {1, 4, 5} :=
  kFourTrees_meeting_bandDeadPairs tree hmem
    (bandWitness_posDef_meets_zeroOne tree hposDef)
    (bandWitness_posDef_meets_oneTwo tree hposDef)
    (bandWitness_posDef_meets_oneThree tree hposDef)
    (bandWitness_posDef_meets_oneFive tree hposDef)
    (bandWitness_posDef_meets_threeFive tree hposDef)

/-! ### The four vertex stars are not a sufficient candidate family

Under the `S4` action the sixteen spanning trees of `K4` fall into two orbits --
four vertex stars and twelve paths -- and neither orbit may be dropped.  At
`Gtz.tetrahedronChartPoint` the strictly dominating trees are exactly the four
stars, so the paths cannot carry the class alone.  The point below is the mirror:
its heavy conductance sits on a PERFECT MATCHING, every star therefore has a light
edge at a heavy vertex, and no star is strictly dominating while a path is. -/

noncomputable def starOrbitRefuterMass : Fin 6 → ℝ
  | 0 => 1 / 60
  | 1 => 5 / 3
  | 2 => 1 / 60
  | 3 => 1 / 60
  | 4 => 5 / 3
  | 5 => 1 / 60

noncomputable def starOrbitRefuterWeight : Fin 6 → ℝ := fun _ => 1 / 6

/-- Uniform weights with the heavy mass on the perfect matching `{1, 4}`. -/
noncomputable def starOrbitRefuterPoint : DirectionChartPoint 6 where
  mass := starOrbitRefuterMass
  weight := starOrbitRefuterWeight
  mass_pos := by intro label; fin_cases label <;> norm_num [starOrbitRefuterMass]
  weight_pos := by intro label; norm_num [starOrbitRefuterWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [starOrbitRefuterWeight]

theorem starOrbitRefuterPoint_mass_eq : starOrbitRefuterPoint.mass = starOrbitRefuterMass := rfl

theorem starOrbitRefuterPoint_weight_eq :
    starOrbitRefuterPoint.weight = starOrbitRefuterWeight := rfl

theorem starOrbitRefuter_gap_zeroOneThree_det_neg :
    (directionChartGap kFourDirection starOrbitRefuterPoint.mass
      starOrbitRefuterPoint.weight {0, 1, 3}).det < 0 := by
  simp only [directionChartGap, starOrbitRefuterPoint_mass_eq, starOrbitRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [starOrbitRefuterMass, starOrbitRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem starOrbitRefuter_gap_zeroTwoFour_det_neg :
    (directionChartGap kFourDirection starOrbitRefuterPoint.mass
      starOrbitRefuterPoint.weight {0, 2, 4}).det < 0 := by
  simp only [directionChartGap, starOrbitRefuterPoint_mass_eq, starOrbitRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [starOrbitRefuterMass, starOrbitRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem starOrbitRefuter_gap_oneTwoFive_det_neg :
    (directionChartGap kFourDirection starOrbitRefuterPoint.mass
      starOrbitRefuterPoint.weight {1, 2, 5}).det < 0 := by
  simp only [directionChartGap, starOrbitRefuterPoint_mass_eq, starOrbitRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [starOrbitRefuterMass, starOrbitRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem starOrbitRefuter_gap_threeFourFive_det_neg :
    (directionChartGap kFourDirection starOrbitRefuterPoint.mass
      starOrbitRefuterPoint.weight {3, 4, 5}).det < 0 := by
  simp only [directionChartGap, starOrbitRefuterPoint_mass_eq, starOrbitRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [starOrbitRefuterMass, starOrbitRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem starOrbitRefuter_gap_zeroOneFour_posDef :
    (directionChartGap kFourDirection starOrbitRefuterPoint.mass
      starOrbitRefuterPoint.weight {0, 1, 4}).PosDef := by
  rw [posDef_finThree_iff_cornerBlockDet _
    (directionChartGap_transpose kFourDirection starOrbitRefuterPoint.mass
      starOrbitRefuterPoint.weight {0, 1, 4})]
  simp only [directionChartGap, starOrbitRefuterPoint_mass_eq, starOrbitRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [starOrbitRefuterMass, starOrbitRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- **NO VERTEX STAR IS STRICTLY DOMINATING AT THE MATCHING POINT.** -/
theorem starOrbitRefuter_no_star_posDef (star : Finset (Fin 6))
    (hstar : star = {0, 1, 3} ∨ star = {0, 2, 4} ∨ star = {1, 2, 5} ∨ star = {3, 4, 5}) :
    ¬ (directionChartGap kFourDirection starOrbitRefuterPoint.mass
        starOrbitRefuterPoint.weight star).PosDef := by
  rcases hstar with heq | heq | heq | heq <;> subst heq <;> intro hposDef
  · exact absurd hposDef.det_pos (not_lt.mpr starOrbitRefuter_gap_zeroOneThree_det_neg.le)
  · exact absurd hposDef.det_pos (not_lt.mpr starOrbitRefuter_gap_zeroTwoFour_det_neg.le)
  · exact absurd hposDef.det_pos (not_lt.mpr starOrbitRefuter_gap_oneTwoFive_det_neg.le)
  · exact absurd hposDef.det_pos (not_lt.mpr starOrbitRefuter_gap_threeFourFive_det_neg.le)

/-- **THE STAR ORBIT IS NOT A SUFFICIENT CANDIDATE FAMILY.**  At the matching point
a path is strictly dominating and no star is, so no cell atlas and no elimination
may restrict the tree quantifier to the four vertex stars. -/
theorem starOrbitRefuter_path_posDef_and_no_star :
    (directionChartGap kFourDirection starOrbitRefuterPoint.mass
        starOrbitRefuterPoint.weight {0, 1, 4}).PosDef
      ∧ ∀ star : Finset (Fin 6),
          (star = {0, 1, 3} ∨ star = {0, 2, 4} ∨ star = {1, 2, 5} ∨ star = {3, 4, 5}) →
          ¬ (directionChartGap kFourDirection starOrbitRefuterPoint.mass
              starOrbitRefuterPoint.weight star).PosDef :=
  ⟨starOrbitRefuter_gap_zeroOneFour_posDef, starOrbitRefuter_no_star_posDef⟩

end Gtz
