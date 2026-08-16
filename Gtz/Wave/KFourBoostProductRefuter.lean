import Gtz.Wave.KFourTreeLaplacian
import Gtz.Wave.TripleDeterminantCells

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The boost-product designation at `M(K4)`, refuted, and the star as a permanently
coherent third minor

The registry ledger for `Gtz.obligationKnifeBandRefinedKFour` records a kernel
refutation of every designation tried at the moduli-zero class: the max-conductance
edge, the dominant mass pair, the max-alpha edge, the max-leverage edge, determinant
argmax and its pair variant, and all four invariant-argmax rules on `D1`, `D2`, `D3`.
`Gtz.kFourMinThresholdHostsStrictTree_refuted` added the minimum-threshold rule.

## The boost product, and why it looked right

On this stratum the six edge vectors are totally unimodular, so by
`Gtz.det_kFourSelectedMoment_star` the selected determinant of a spanning tree is
the plain product of its three boosts `m_c / w_c`.  The boost product IS the chart's
determinantal weight here, which is exactly the reading the projection lane uses.
It is also the one rule the ledger does not already refute.

**It is FALSE.**  `Gtz.KFourMaxBoostHostsStrictTree_refuted` exhibits a chart point
with integer masses `(2, 10, 6, 1, 5, 2)` where the tree `{0, 4, 5}` carries boost
product `108000`, more than twice the `45000` of `{0, 1, 4}`, and `{0, 1, 4}`
dominates while `{0, 4, 5}` does not.  The failure is on the third minor alone: at
`{0, 4, 5}` the two leading minors are `47` and `255`, both positive, and the
determinant is `-5642`.

Neither tree is a vertex star, so the natural tiebreaker "prefer a star" cannot
repair the rule.

## The star, and the structure that survives

`Gtz.det_kFourStarGap_eq_tripleDetForm` reads the canonical star's gap determinant
as the campaign's scalar `Gtz.tripleDetForm`, with the three surpluses the diagonal
of `D - L` and **the three pairings the three off-tree masses**.  Two consequences:

* `Gtz.kFourStarGap_cross_pos` — the cross term is `2 * m 2 * m 4 * m 5`, and the
  masses of a chart point are positive, so **the canonical star is permanently in
  the COHERENT branch of the third minor.**  The incoherent branch, which is the
  expensive one and which costs the campaign a factor of two throughout, never
  occurs at a star.
* `Gtz.posDef_kFourStarGap_iff` — the star branch of the obligation is Sylvester on
  three explicit polynomials in three heavy tree masses and three off-tree masses.

`Gtz.quadForm_kFourStarGap` gives the reading behind both: the star's quadratic form
is the heavy tree masses against the CYCLE ENERGY of the off-tree edges,
`a (v0 - v1)^2 + b (v0 - v2)^2 + c (v1 - v2)^2`.  The landed
`Gtz.starHeaviness_of_posDef` is the diagonal of that statement, and
`Gtz.exists_starDiagonal_pos_not_posDef` shows it is strictly weaker: the diagonal
can be positive at all three slots while the star still fails.
-/

namespace Gtz

open Matrix

/-! ## 1. The boost product -/

/-- The chart's determinantal weight on the graphic stratum.  By
`Gtz.det_kFourSelectedMoment_star` this is the selected determinant of a spanning
tree, because total unimodularity makes the bracket contribute one. -/
noncomputable def kFourBoostProduct (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) : ℝ :=
  ∏ label ∈ selected, mass label / weight label

theorem kFourBoostProduct_triple (mass weight : Fin 6 → ℝ)
    (labelA labelB labelC : Fin 6) (hab : labelA ≠ labelB) (hac : labelA ≠ labelC)
    (hbc : labelB ≠ labelC) :
    kFourBoostProduct mass weight {labelA, labelB, labelC}
      = (mass labelA / weight labelA) * (mass labelB / weight labelB)
          * (mass labelC / weight labelC) := by
  rw [kFourBoostProduct, Finset.prod_insert (by simp [hab, hac]),
    Finset.prod_insert (by simp [hbc]), Finset.prod_singleton, mul_assoc]

/-! ## 2. The refuting chart point -/

/-- Masses of the boost-product refuter: all integers. -/
noncomputable def boostRefuterMass : Fin 6 → ℝ
  | 0 => 2
  | 1 => 10
  | 2 => 6
  | 3 => 1
  | 4 => 5
  | 5 => 2

/-- Weights of the boost-product refuter, thirtieths summing to one. -/
noncomputable def boostRefuterWeight : Fin 6 → ℝ
  | 0 => 1 / 30
  | 1 => 2 / 5
  | 2 => 7 / 30
  | 3 => 2 / 15
  | 4 => 1 / 6
  | 5 => 1 / 30

@[simp] theorem boostRefuterMass_zero : boostRefuterMass 0 = 2 := rfl
@[simp] theorem boostRefuterMass_one : boostRefuterMass 1 = 10 := rfl
@[simp] theorem boostRefuterMass_two : boostRefuterMass 2 = 6 := rfl
@[simp] theorem boostRefuterMass_three : boostRefuterMass 3 = 1 := rfl
@[simp] theorem boostRefuterMass_four : boostRefuterMass 4 = 5 := rfl
@[simp] theorem boostRefuterMass_five : boostRefuterMass 5 = 2 := rfl

@[simp] theorem boostRefuterWeight_zero : boostRefuterWeight 0 = 1 / 30 := rfl
@[simp] theorem boostRefuterWeight_one : boostRefuterWeight 1 = 2 / 5 := rfl
@[simp] theorem boostRefuterWeight_two : boostRefuterWeight 2 = 7 / 30 := rfl
@[simp] theorem boostRefuterWeight_three : boostRefuterWeight 3 = 2 / 15 := rfl
@[simp] theorem boostRefuterWeight_four : boostRefuterWeight 4 = 1 / 6 := rfl
@[simp] theorem boostRefuterWeight_five : boostRefuterWeight 5 = 1 / 30 := rfl

/-- The refuting chart point. -/
noncomputable def boostRefuterPoint : DirectionChartPoint 6 where
  mass := boostRefuterMass
  weight := boostRefuterWeight
  mass_pos := by intro label; fin_cases label <;> norm_num [boostRefuterMass]
  weight_pos := by intro label; fin_cases label <;> norm_num [boostRefuterWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [boostRefuterWeight]

@[simp] theorem boostRefuterPoint_mass_eq : boostRefuterPoint.mass = boostRefuterMass := rfl
@[simp] theorem boostRefuterPoint_weight_eq :
    boostRefuterPoint.weight = boostRefuterWeight := rfl

/-! ## 3. The two boost products, and the two gaps -/

theorem boostRefuter_boost_zeroFourFive :
    kFourBoostProduct boostRefuterMass boostRefuterWeight {0, 4, 5} = 108000 := by
  rw [kFourBoostProduct_triple _ _ 0 4 5 (by decide) (by decide) (by decide)]
  norm_num

theorem boostRefuter_boost_zeroOneFour :
    kFourBoostProduct boostRefuterMass boostRefuterWeight {0, 1, 4} = 45000 := by
  rw [kFourBoostProduct_triple _ _ 0 1 4 (by decide) (by decide) (by decide)]
  norm_num

/-- **THE ARGMAX IS STRICTLY LARGER.** -/
theorem boostRefuter_boost_lt :
    kFourBoostProduct boostRefuterMass boostRefuterWeight {0, 1, 4}
      < kFourBoostProduct boostRefuterMass boostRefuterWeight {0, 4, 5} := by
  rw [boostRefuter_boost_zeroOneFour, boostRefuter_boost_zeroFourFive]
  norm_num

theorem boostRefuter_gap_zeroFourFive_det :
    (directionChartGap kFourDirection boostRefuterMass boostRefuterWeight
      {0, 4, 5}).det = -5642 := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [boostRefuterMass, boostRefuterWeight, kFourDirection, atomMatrix,
    Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The failure is on the THIRD minor only: the first leading minor is positive. -/
theorem boostRefuter_gap_zeroFourFive_diag :
    (directionChartGap kFourDirection boostRefuterMass boostRefuterWeight
      {0, 4, 5}) 0 0 = 47 := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [boostRefuterMass, boostRefuterWeight, kFourDirection, atomMatrix]

/-- **THE ARGMAX-BOOST TREE DOES NOT DOMINATE.** -/
theorem boostRefuter_not_posDef_zeroFourFive :
    ¬ (directionChartGap kFourDirection boostRefuterMass boostRefuterWeight
        {0, 4, 5}).PosDef := by
  intro hpd
  have hdet := hpd.det_pos
  rw [boostRefuter_gap_zeroFourFive_det] at hdet
  norm_num at hdet

/-- The competitor with the smaller boost product DOES dominate. -/
theorem boostRefuter_posDef_zeroOneFour :
    (directionChartGap kFourDirection boostRefuterMass boostRefuterWeight
      {0, 1, 4}).PosDef := by
  rw [posDef_finThree_iff_leadingMinors _ (directionChartGap_transpose _ _ _ _)]
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [directionChartGap]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton, Fin.sum_univ_six]
      norm_num [boostRefuterMass, boostRefuterWeight, kFourDirection, atomMatrix,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-! ## 4. The designation, refuted -/

/-- The designation this module tests: a spanning tree whose boost product is at
least another's inherits that other's domination.  Every rule of the form "prefer
the larger boost product" implies it, and by
`Gtz.det_kFourSelectedMoment_star` the boost product is the chart's determinantal
weight on this stratum. -/
def KFourMaxBoostHostsStrictTree : Prop :=
  ∀ point : DirectionChartPoint 6, ∀ treeHigh treeLow : Finset (Fin 6),
    kFourBoostProduct point.mass point.weight treeLow
        ≤ kFourBoostProduct point.mass point.weight treeHigh →
      (directionChartGap kFourDirection point.mass point.weight treeLow).PosDef →
        (directionChartGap kFourDirection point.mass point.weight treeHigh).PosDef

/-- **THE MAXIMUM-BOOST-PRODUCT DESIGNATION IS REFUTED.**  At
`Gtz.boostRefuterPoint` the tree `{0, 4, 5}` carries boost product `108000` against
the `45000` of `{0, 1, 4}`, and `{0, 1, 4}` dominates while `{0, 4, 5}` does not.

With `Gtz.kFourMinThresholdHostsStrictTree_refuted` this closes BOTH halves of the
pair the projection lane reads: the bracket is constant at one on every spanning
tree by total unimodularity, so a max-bracket rule cannot designate at all, and the
two determinantal readings that remain are now each refuted. -/
theorem KFourMaxBoostHostsStrictTree_refuted : ¬ KFourMaxBoostHostsStrictTree := by
  intro hrule
  refine boostRefuter_not_posDef_zeroFourFive ?_
  refine hrule boostRefuterPoint {0, 4, 5} {0, 1, 4} ?_ boostRefuter_posDef_zeroOneFour
  simpa using boostRefuter_boost_lt.le

/-! ## 5. The star's third minor is a `tripleDetForm` with a positive cross term -/

/-- **THE STAR GAP DETERMINANT IS THE CAMPAIGN'S SCALAR THIRD MINOR.**  The three
surpluses are the diagonal of `D - L`, and **the three pairings are exactly the
three off-tree masses**. -/
theorem det_kFourStarGap_eq_tripleDetForm (mass weight : Fin 6 → ℝ) :
    (kFourStarGap mass weight).det
      = tripleDetForm
          (mass 0 * (1 - weight 0) / weight 0 - mass 2 - mass 4)
          (mass 1 * (1 - weight 1) / weight 1 - mass 2 - mass 5)
          (mass 3 * (1 - weight 3) / weight 3 - mass 4 - mass 5)
          (mass 2) (mass 4) (mass 5) := by
  rw [kFourStarGap, Matrix.det_fin_three, tripleDetForm]
  simp [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **THE CANONICAL STAR IS PERMANENTLY COHERENT.**  Its cross term is twice the
product of the three off-tree masses, and the masses of a chart point are positive.
The incoherent branch of the third minor — the expensive one, worth a factor of two
throughout this campaign — never occurs at a vertex star. -/
theorem kFourStarGap_cross_pos (point : DirectionChartPoint 6) :
    0 < point.mass 2 * point.mass 4 * point.mass 5 := by
  have h2 := point.mass_pos 2
  have h4 := point.mass_pos 4
  have h5 := point.mass_pos 5
  positivity

/-- Sylvester at the canonical star, in closed form: three explicit polynomials in
three heavy tree masses and three off-tree masses.  This is the star branch of
`Gtz.obligationKnifeBandRefinedKFour` with no frame, no whitener, no square root and
no eigenvalue. -/
@[simp] theorem kFourStarGap_zero_zero (mass weight : Fin 6 → ℝ) :
    kFourStarGap mass weight 0 0
      = mass 0 * (1 - weight 0) / weight 0 - mass 2 - mass 4 := rfl

@[simp] theorem kFourStarGap_zero_one (mass weight : Fin 6 → ℝ) :
    kFourStarGap mass weight 0 1 = mass 2 := rfl

@[simp] theorem kFourStarGap_zero_two (mass weight : Fin 6 → ℝ) :
    kFourStarGap mass weight 0 2 = mass 4 := rfl

@[simp] theorem kFourStarGap_one_one (mass weight : Fin 6 → ℝ) :
    kFourStarGap mass weight 1 1
      = mass 1 * (1 - weight 1) / weight 1 - mass 2 - mass 5 := rfl

@[simp] theorem kFourStarGap_one_two (mass weight : Fin 6 → ℝ) :
    kFourStarGap mass weight 1 2 = mass 5 := rfl

@[simp] theorem kFourStarGap_two_two (mass weight : Fin 6 → ℝ) :
    kFourStarGap mass weight 2 2
      = mass 3 * (1 - weight 3) / weight 3 - mass 4 - mass 5 := rfl

theorem posDef_kFourStarGap_iff (mass weight : Fin 6 → ℝ) :
    (kFourStarGap mass weight).PosDef
      ↔ 0 < mass 0 * (1 - weight 0) / weight 0 - mass 2 - mass 4
        ∧ 0 < (mass 0 * (1 - weight 0) / weight 0 - mass 2 - mass 4)
              * (mass 1 * (1 - weight 1) / weight 1 - mass 2 - mass 5) - mass 2 ^ 2
        ∧ 0 < tripleDetForm
              (mass 0 * (1 - weight 0) / weight 0 - mass 2 - mass 4)
              (mass 1 * (1 - weight 1) / weight 1 - mass 2 - mass 5)
              (mass 3 * (1 - weight 3) / weight 3 - mass 4 - mass 5)
              (mass 2) (mass 4) (mass 5) := by
  have hsymm : (kFourStarGap mass weight)ᵀ = kFourStarGap mass weight := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [kFourStarGap, Matrix.transpose_apply]
  rw [posDef_finThree_iff_leadingMinors _ hsymm]
  simp only [kFourStarGap_zero_zero, kFourStarGap_zero_one, kFourStarGap_zero_two,
    kFourStarGap_one_one, kFourStarGap_one_two, kFourStarGap_two_two, tripleDetForm]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor <;> intro hpos <;> nlinarith [hpos]

/-- **THE STAR CELL.**  Quarter slack on the three off-tree masses against the three
heavy diagonal entries forces the canonical star to dominate.  It reads only masses
and weights, and it needs no sign information, because
`Gtz.kFourStarGap_cross_pos` already puts the star in the coherent branch. -/
theorem posDef_directionChartGap_star_of_quarterSlack (mass weight : Fin 6 → ℝ)
    (h0 : weight 0 ≠ 0) (h1 : weight 1 ≠ 0) (h3 : weight 3 ≠ 0)
    (hx : 0 < mass 0 * (1 - weight 0) / weight 0 - mass 2 - mass 4)
    (hy : 0 < mass 1 * (1 - weight 1) / weight 1 - mass 2 - mass 5)
    (hz : 0 < mass 3 * (1 - weight 3) / weight 3 - mass 4 - mass 5)
    (hu : 4 * mass 2 ^ 2
      < (mass 0 * (1 - weight 0) / weight 0 - mass 2 - mass 4)
        * (mass 1 * (1 - weight 1) / weight 1 - mass 2 - mass 5))
    (hv : 4 * mass 4 ^ 2
      < (mass 0 * (1 - weight 0) / weight 0 - mass 2 - mass 4)
        * (mass 3 * (1 - weight 3) / weight 3 - mass 4 - mass 5))
    (hw : 4 * mass 5 ^ 2
      < (mass 1 * (1 - weight 1) / weight 1 - mass 2 - mass 5)
        * (mass 3 * (1 - weight 3) / weight 3 - mass 4 - mass 5)) :
    (directionChartGap kFourDirection mass weight {0, 1, 3}).PosDef := by
  rw [posDef_directionChartGap_star_iff mass weight h0 h1 h3, posDef_kFourStarGap_iff]
  refine ⟨hx, ?_, tripleDetForm_pos_of_quarterSlack _ _ _ _ _ _ hx hy hz hu hv hw⟩
  nlinarith [hx, hy, hu]

/-! ## 6. The cycle-energy reading, and the diagonal is not enough -/

/-- The cycle energy of the three off-tree edges at a vector: the quadratic form of
the triangle Laplacian whose edge weights are the off-tree masses. -/
noncomputable def starCycleEnergy (mass : Fin 6 → ℝ) (vecArg : Fin 3 → ℝ) : ℝ :=
  mass 2 * (vecArg 0 - vecArg 1) ^ 2 + mass 4 * (vecArg 0 - vecArg 2) ^ 2
    + mass 5 * (vecArg 1 - vecArg 2) ^ 2

/-- **THE STAR IS HEAVY MASS AGAINST CYCLE ENERGY.**  The quadratic form of the
canonical star's gap is the heavy tree masses on the squared coordinates, less the
cycle energy of the three off-tree edges.  Every statement in this section is a
reading of this identity. -/
theorem quadForm_kFourStarGap (mass weight : Fin 6 → ℝ) (vecArg : Fin 3 → ℝ) :
    vecArg ⬝ᵥ (kFourStarGap mass weight *ᵥ vecArg)
      = mass 0 * (1 - weight 0) / weight 0 * vecArg 0 ^ 2
        + mass 1 * (1 - weight 1) / weight 1 * vecArg 1 ^ 2
        + mass 3 * (1 - weight 3) / weight 3 * vecArg 2 ^ 2
        - starCycleEnergy mass vecArg := by
  simp [kFourStarGap, starCycleEnergy, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The cycle energy is non-negative at positive off-tree masses. -/
theorem starCycleEnergy_nonneg (point : DirectionChartPoint 6) (vecArg : Fin 3 → ℝ) :
    0 ≤ starCycleEnergy point.mass vecArg := by
  have h2 := (point.mass_pos 2).le
  have h4 := (point.mass_pos 4).le
  have h5 := (point.mass_pos 5).le
  unfold starCycleEnergy
  positivity

/-- Masses of the star-diagonal witness. -/
noncomputable def starDiagonalWitnessMass : Fin 6 → ℝ
  | 0 => 4
  | 1 => 1
  | 2 => 1
  | 3 => 4
  | 4 => 7
  | 5 => 1

/-- Weights of the star-diagonal witness, ninths summing to one. -/
noncomputable def starDiagonalWitnessWeight : Fin 6 → ℝ
  | 0 => 2 / 9
  | 1 => 2 / 9
  | 2 => 1 / 9
  | 3 => 2 / 9
  | 4 => 1 / 9
  | 5 => 1 / 9

theorem starDiagonalWitness_weight_sum :
    ∑ label, starDiagonalWitnessWeight label = 1 := by
  rw [Fin.sum_univ_six]; norm_num [starDiagonalWitnessWeight]

/-- **THE LANDED DIAGONAL CONDITION IS STRICTLY WEAKER THAN DOMINATION.**  At this
witness the canonical star has all three diagonal entries of `D - L` strictly
positive — `6`, `3/2` and `6`, so `Gtz.starHeaviness_of_posDef` is satisfied — and
its leading two-by-two minor is `8`, also positive.  The determinant is `-35/2`, so
the star does NOT dominate.  Neither the diagonal reading nor the two leading minors
can decide the star branch, and the third minor is where the content is. -/
theorem exists_starDiagonal_pos_not_posDef :
    0 < starDiagonalWitnessMass 0 * (1 - starDiagonalWitnessWeight 0)
          / starDiagonalWitnessWeight 0
        - starDiagonalWitnessMass 2 - starDiagonalWitnessMass 4
      ∧ 0 < starDiagonalWitnessMass 1 * (1 - starDiagonalWitnessWeight 1)
          / starDiagonalWitnessWeight 1
        - starDiagonalWitnessMass 2 - starDiagonalWitnessMass 5
      ∧ 0 < starDiagonalWitnessMass 3 * (1 - starDiagonalWitnessWeight 3)
          / starDiagonalWitnessWeight 3
        - starDiagonalWitnessMass 4 - starDiagonalWitnessMass 5
      ∧ (kFourStarGap starDiagonalWitnessMass starDiagonalWitnessWeight).det = -35 / 2
      ∧ ¬ (kFourStarGap starDiagonalWitnessMass starDiagonalWitnessWeight).PosDef := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [starDiagonalWitnessMass, starDiagonalWitnessWeight]
  · norm_num [starDiagonalWitnessMass, starDiagonalWitnessWeight]
  · norm_num [starDiagonalWitnessMass, starDiagonalWitnessWeight]
  · rw [det_kFourStarGap_eq_tripleDetForm, tripleDetForm]
    norm_num [starDiagonalWitnessMass, starDiagonalWitnessWeight]
  · intro hpd
    have hdet := hpd.det_pos
    rw [det_kFourStarGap_eq_tripleDetForm, tripleDetForm] at hdet
    norm_num [starDiagonalWitnessMass, starDiagonalWitnessWeight] at hdet

/-! ## 7. The window between the necessary and the sufficient reading

The landed `Gtz.starHeaviness_of_posDef` says a dominating star has heavy mass
beating the sum of its two incident off-tree masses — the factor one.  Strict
diagonal dominance of `D - L` is the factor two.  Section 8 shows the truth sits
strictly between them, at the factor three halves on the equilateral locus. -/

/-- **THE SCALAR DOMINANCE CELL.**  Strict diagonal dominance of the symmetric
`3 x 3` matrix with surpluses on the diagonal and non-negative pairings off it
forces the third minor positive.  The proof is the classical descent: the leading
`2 x 2` cofactor beats the pairing energy, and what remains splits into two products
of non-negative slack plus a non-negative remainder. -/
theorem tripleDetForm_pos_of_dominant (surplusX surplusY surplusZ
    pairU pairV pairW : ℝ)
    (hu : 0 ≤ pairU) (hv : 0 ≤ pairV) (hw : 0 ≤ pairW)
    (hx : pairU + pairV < surplusX) (hy : pairU + pairW < surplusY)
    (hz : pairV + pairW < surplusZ) :
    0 < tripleDetForm surplusX surplusY surplusZ pairU pairV pairW := by
  have hxpos : 0 < surplusX := by linarith
  have hypos : 0 < surplusY := by linarith
  have hzpos : 0 < surplusZ := by linarith
  have hcof : 0 < surplusY * surplusZ - pairW ^ 2 := by nlinarith
  have hslackY : 0 ≤ surplusY - pairU - pairW := by linarith
  have hslackZ : 0 ≤ surplusZ - pairV - pairW := by linarith
  have hterm1 : 0 ≤ pairU * surplusZ * (surplusY - pairU - pairW) :=
    mul_nonneg (mul_nonneg hu hzpos.le) hslackY
  have hterm2 : 0 ≤ pairV * surplusY * (surplusZ - pairV - pairW) :=
    mul_nonneg (mul_nonneg hv hypos.le) hslackZ
  have hbracket : 0 ≤ pairW * (pairU * (surplusZ - pairW) + pairV * (surplusY - pairW)
      + 2 * (pairU * pairV)) := by
    have h1 : 0 ≤ pairU * (surplusZ - pairW) := mul_nonneg hu (by linarith)
    have h2 : 0 ≤ pairV * (surplusY - pairW) := mul_nonneg hv (by linarith)
    have h3 : 0 ≤ 2 * (pairU * pairV) := by positivity
    exact mul_nonneg hw (by linarith)
  have hlow : 0 ≤ (pairU + pairV) * (surplusY * surplusZ - pairW ^ 2)
      - pairU ^ 2 * surplusZ - surplusY * pairV ^ 2
      + 2 * (pairU * pairV * pairW) := by nlinarith [hterm1, hterm2, hbracket]
  have hstep : (pairU + pairV) * (surplusY * surplusZ - pairW ^ 2)
      < surplusX * (surplusY * surplusZ - pairW ^ 2) :=
    mul_lt_mul_of_pos_right hx hcof
  rw [tripleDetForm]; nlinarith [hlow, hstep]

/-- **THE FACTOR-TWO CELL.**  Strict diagonal dominance of `D - L` is exactly the
statement that each heavy tree mass beats TWICE the sum of its two incident off-tree
masses, and it forces the canonical star to dominate.  Compare the landed
`Gtz.starHeaviness_of_posDef`, which is the same statement at factor one and is only
necessary. -/
theorem posDef_kFourStarGap_of_diagonalDominant (mass weight : Fin 6 → ℝ)
    (h2 : 0 ≤ mass 2) (h4 : 0 ≤ mass 4) (h5 : 0 ≤ mass 5)
    (hd0 : mass 2 + mass 4
      < mass 0 * (1 - weight 0) / weight 0 - mass 2 - mass 4)
    (hd1 : mass 2 + mass 5
      < mass 1 * (1 - weight 1) / weight 1 - mass 2 - mass 5)
    (hd3 : mass 4 + mass 5
      < mass 3 * (1 - weight 3) / weight 3 - mass 4 - mass 5) :
    (kFourStarGap mass weight).PosDef := by
  rw [posDef_kFourStarGap_iff]
  refine ⟨by linarith, by nlinarith [hd0, hd1, h2, h4, h5], ?_⟩
  exact tripleDetForm_pos_of_dominant _ _ _ _ _ _ h2 h4 h5 hd0 hd1 hd3

/-! ## 8. The equilateral locus, where the sharp constant is three -/

/-- On the equilateral locus of the star — all three off-tree masses one — the third
minor factors as `(p - 1) ^ 2 * (p + 2)`.  This is the landed coherent branch
`Gtz.tripleDetForm_equilateral_coherent` at unit pairing, and it is NON-NEGATIVE for
every `p` at least `-2`: at a star the determinant is never the binding constraint. -/
theorem tripleDetForm_star_equilateral (surplus : ℝ) :
    tripleDetForm surplus surplus surplus 1 1 1
      = (surplus - 1) ^ 2 * (surplus + 2) := by
  rw [tripleDetForm]; ring

theorem tripleDetForm_star_equilateral_nonneg (surplus : ℝ) (hsurplus : -2 ≤ surplus) :
    0 ≤ tripleDetForm surplus surplus surplus 1 1 1 := by
  rw [tripleDetForm_star_equilateral]
  have : (0 : ℝ) ≤ surplus + 2 := by linarith
  positivity

/-- **THE BINDING CONSTRAINT AT AN EQUILATERAL STAR IS THE SECOND MINOR, NOT THE
DETERMINANT.**  With all three off-tree masses one and all three surpluses equal, the
star dominates exactly when the surplus exceeds one — that is, exactly when the
leading two-by-two minor is positive.  The determinant clause is implied and never
binds. -/
theorem posDef_starEquilateral_iff (surplus : ℝ) :
    (0 < surplus ∧ 0 < surplus * surplus - 1 ^ 2
        ∧ 0 < tripleDetForm surplus surplus surplus 1 1 1)
      ↔ 1 < surplus := by
  constructor
  · rintro ⟨hfirst, hsecond, -⟩; nlinarith [hfirst, hsecond]
  · intro hone
    refine ⟨by linarith, by nlinarith, ?_⟩
    rw [tripleDetForm_star_equilateral]
    have hne : surplus - 1 ≠ 0 := by intro hzero; rw [sub_eq_zero] at hzero; simp [hzero] at hone
    have hsq : 0 < (surplus - 1) ^ 2 := by positivity
    nlinarith [hsq]

/-- **THE FACTOR-TWO CELL IS NOT SHARP, AND THE GAP IS EXACTLY THREE HALVES.**  At an
equilateral star with unit off-tree masses, `Gtz.starHeaviness_of_posDef` needs heavy
mass above `2`, `Gtz.posDef_kFourStarGap_of_diagonalDominant` needs it above `4`, and
the truth is `3`.  So the necessary reading is loose by a factor of three halves and
the diagonal-dominance reading by a factor of four thirds, and the true constant sits
strictly between them. -/
theorem starEquilateral_sharp_constant :
    ¬ (0 < (29 : ℝ) / 10 - 2 ∧ 0 < ((29 : ℝ) / 10 - 2) * ((29 : ℝ) / 10 - 2) - 1 ^ 2
        ∧ 0 < tripleDetForm ((29 : ℝ) / 10 - 2) ((29 : ℝ) / 10 - 2)
              ((29 : ℝ) / 10 - 2) 1 1 1)
      ∧ (0 < (31 : ℝ) / 10 - 2 ∧ 0 < ((31 : ℝ) / 10 - 2) * ((31 : ℝ) / 10 - 2) - 1 ^ 2
        ∧ 0 < tripleDetForm ((31 : ℝ) / 10 - 2) ((31 : ℝ) / 10 - 2)
              ((31 : ℝ) / 10 - 2) 1 1 1) := by
  constructor
  · rw [posDef_starEquilateral_iff]; norm_num
  · rw [posDef_starEquilateral_iff]; norm_num

/-- **DETERMINANT POSITIVITY DOES NOT IMPLY DOMINATION AT THE STAR EITHER.**  At the
equilateral star with heavy mass `29/10` the third minor is `29/1000`, strictly
positive, while the leading two-by-two minor is `-19/100`.  The ledger records this
failure mode for the general chart, and it occurs at the gauge star itself. -/
theorem starEquilateral_detPos_notPosDef :
    0 < tripleDetForm ((29 : ℝ) / 10 - 2) ((29 : ℝ) / 10 - 2) ((29 : ℝ) / 10 - 2) 1 1 1
      ∧ ((29 : ℝ) / 10 - 2) * ((29 : ℝ) / 10 - 2) - 1 ^ 2 < 0 := by
  constructor
  · rw [tripleDetForm_star_equilateral]; norm_num
  · norm_num

end Gtz
