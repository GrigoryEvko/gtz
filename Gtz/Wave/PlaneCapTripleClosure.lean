import Gtz.Wave.PlaneCapHelly

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The three-atom cap residue is a theorem, and the campaign chain closes

The cap module collapsed the plane residue to `Gtz.PlaneCapTripleClosed`, and
the leaf split left one leaf: three half planes with no disc.  This module
proves that leaf, wires the second Helly call, and closes the chain.

The half-plane leaf is a Farkas statement.  Three plane vectors carry one
linear relation, and its coefficients are the wedges.  When the wedges have
mixed signs, a vertex of two boundary lines is a point of all three half
planes.  When the wedges share a sign, the pair law caps the wedge form of the
levels at zero, and a vertex again is a point.  The wedge bound is the crux.
Its proof splits each doubled reading with two half quantities, and the sum
laws of the half quantities turn the bound into two vertex evaluations that
are exactly zero.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.planeWedge`, `Gtz.planeWedge_sq_add_dot_sq`,
  `Gtz.planeWedge_mul_planeWedge` — the wedge calculus of the plane.
* `Gtz.planeReflect`, `Gtz.planeReflect_dot`, `Gtz.planeWedge_planeReflect` —
  the reflection that turns one wedge sign into the other.
* `Gtz.halfSin`, `Gtz.halfCos`, `Gtz.halfSin_mul_halfCos`,
  `Gtz.halfSin_add_eq`, `Gtz.halfCos_diff_eq` — **THE HALF CALCULUS.**  The
  two sum laws hold with no angle, from the Lagrange identity and the
  Binet-Cauchy identity alone.
* `Gtz.half_form_le_of_tight`, `Gtz.half_form_le_of_pivot` — **THE TWO VERTEX
  EVALUATIONS.**  The tight vertex and the capped vertex both price the wedge
  form at exactly zero.
* `Gtz.half_wedge_form_nonpos`, `Gtz.planeWedge_form_nonpos` — **THE CRUX.**
  Unit readings with nonnegative wedges and the pair law keep the wedge form
  of the levels nonpositive.
* `Gtz.exists_point_of_vertex`, `Gtz.exists_point_of_collinear`,
  `Gtz.exists_point_of_unit_triple` — the Farkas dispatch: a vertex, a line,
  or a reflected crux always supplies the point.
* `Gtz.planeHalfTripleClosed_holds` — **THE HALF-PLANE LEAF IS A THEOREM.**
* `Gtz.planeCapTripleClosed_of_halfTriple` — **THE SECOND HELLY CALL.**  The
  four-set family of the disc and the three half planes.
* `Gtz.planeCapTripleClosed_holds` — **THE THREE-ATOM RESIDUE IS A THEOREM.**
* `Gtz.atomPairGramClosed_holds`, `Gtz.atomPairCeilingClosed_holds`,
  `Gtz.rankFiveDenseHeavyFiveClosed_holds`,
  `Gtz.rankFiveDenseHeavyFiveDistinctClosed_holds`,
  `Gtz.forall_shifted_weight_pos`, `Gtz.SixThreeCrux.shifted_weight_pos`,
  `Gtz.SixThreeCrux.false_of_shift_zero` — **THE CAMPAIGN CHAIN, WITH NO
  HYPOTHESIS.**  The pair Gram residue, the pair ceiling, profile A at rank
  five in both forms, campaign interiority, and the boundary crux kill.
-/

namespace Gtz

open scoped BigOperators Matrix

/-! ## Layer 1 — the wedge calculus of the plane -/

/-- The wedge of two plane vectors: the determinant of their coordinates. -/
def planeWedge (vecOne vecTwo : Fin 2 → ℝ) : ℝ :=
  vecOne 0 * vecTwo 1 - vecOne 1 * vecTwo 0

/-- **THE LAGRANGE IDENTITY OF THE PLANE.**  The wedge square plus the dot
square is the product of the two energies. -/
theorem planeWedge_sq_add_dot_sq (vecOne vecTwo : Fin 2 → ℝ) :
    planeWedge vecOne vecTwo ^ 2 + (vecOne ⬝ᵥ vecTwo) ^ 2
      = (vecOne ⬝ᵥ vecOne) * (vecTwo ⬝ᵥ vecTwo) := by
  rw [dot_fin_two, dot_fin_two, dot_fin_two]
  simp only [planeWedge]
  ring

/-- **THE BINET-CAUCHY IDENTITY OF THE PLANE.**  A product of two wedges is a
difference of two dot products. -/
theorem planeWedge_mul_planeWedge (vecOne vecTwo vecThree vecFour : Fin 2 → ℝ) :
    planeWedge vecOne vecTwo * planeWedge vecThree vecFour
      = (vecOne ⬝ᵥ vecThree) * (vecTwo ⬝ᵥ vecFour)
        - (vecOne ⬝ᵥ vecFour) * (vecTwo ⬝ᵥ vecThree) := by
  rw [dot_fin_two, dot_fin_two, dot_fin_two, dot_fin_two]
  simp only [planeWedge]
  ring

/-- The reflection of a plane vector in the first axis. -/
def planeReflect (vec : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![vec 0, -vec 1]

/-- The reflection keeps every dot product. -/
theorem planeReflect_dot (vecOne vecTwo : Fin 2 → ℝ) :
    planeReflect vecOne ⬝ᵥ planeReflect vecTwo = vecOne ⬝ᵥ vecTwo := by
  rw [dot_fin_two, dot_fin_two]
  simp only [planeReflect, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The reflection changes the sign of every wedge. -/
theorem planeWedge_planeReflect (vecOne vecTwo : Fin 2 → ℝ) :
    planeWedge (planeReflect vecOne) (planeReflect vecTwo) = -planeWedge vecOne vecTwo := by
  simp only [planeWedge, planeReflect, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-! ## Layer 2 — two square laws -/

/-- Two nonnegative reals with equal squares are equal. -/
theorem eq_of_sq_eq_sq_of_nonneg {left right : ℝ} (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hsq : left ^ 2 = right ^ 2) : left = right := by
  have hfactor : (left - right) * (left + right) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfactor with hzero | hzero
  · linarith
  · linarith

/-- A real below a nonnegative real in the square is below it outright. -/
theorem le_of_sq_le_sq_of_nonneg {left right : ℝ} (hright : 0 ≤ right)
    (hsq : left ^ 2 ≤ right ^ 2) : left ≤ right := by
  nlinarith

/-! ## Layer 3 — the half calculus -/

/-- The cosine half quantity of a dot product. -/
noncomputable def halfCos (dot : ℝ) : ℝ :=
  Real.sqrt ((1 + dot) / 2)

/-- The sine half quantity of a dot product. -/
noncomputable def halfSin (dot : ℝ) : ℝ :=
  Real.sqrt ((1 - dot) / 2)

theorem halfCos_nonneg (dot : ℝ) : 0 ≤ halfCos dot :=
  Real.sqrt_nonneg _

theorem halfSin_nonneg (dot : ℝ) : 0 ≤ halfSin dot :=
  Real.sqrt_nonneg _

/-- The square of the cosine half quantity. -/
theorem halfCos_sq {dot : ℝ} (hdot : dot ^ 2 ≤ 1) : halfCos dot ^ 2 = (1 + dot) / 2 := by
  have hnonneg : (0 : ℝ) ≤ (1 + dot) / 2 := by nlinarith [sq_nonneg (dot + 1)]
  show Real.sqrt ((1 + dot) / 2) ^ 2 = (1 + dot) / 2
  rw [sq, Real.mul_self_sqrt hnonneg]

/-- The square of the sine half quantity. -/
theorem halfSin_sq {dot : ℝ} (hdot : dot ^ 2 ≤ 1) : halfSin dot ^ 2 = (1 - dot) / 2 := by
  have hnonneg : (0 : ℝ) ≤ (1 - dot) / 2 := by nlinarith [sq_nonneg (dot - 1)]
  show Real.sqrt ((1 - dot) / 2) ^ 2 = (1 - dot) / 2
  rw [sq, Real.mul_self_sqrt hnonneg]

/-- **THE PRODUCT LAW.**  The product of the two half quantities is half the
wedge, when the wedge is nonnegative. -/
theorem halfSin_mul_halfCos {dot wedge : ℝ} (hpy : wedge ^ 2 + dot ^ 2 = 1)
    (hwedge : 0 ≤ wedge) : halfSin dot * halfCos dot = wedge / 2 := by
  have hdot : dot ^ 2 ≤ 1 := by nlinarith [sq_nonneg wedge]
  refine eq_of_sq_eq_sq_of_nonneg
    (mul_nonneg (halfSin_nonneg dot) (halfCos_nonneg dot)) (by linarith) ?_
  have hexpand : (halfSin dot * halfCos dot) ^ 2 = halfSin dot ^ 2 * halfCos dot ^ 2 := by
    ring
  rw [hexpand, halfSin_sq hdot, halfCos_sq hdot]
  linear_combination (-1 / 4 : ℝ) * hpy

/-- **THE SINE SUM LAW.**  The half quantities of two dot products add to the
half quantity of the Binet-Cauchy combination.  No angle is necessary. -/
theorem halfSin_add_eq {dotBase dotLeft dotRight wedgeLeft wedgeRight : ℝ}
    (hpyLeft : wedgeLeft ^ 2 + dotLeft ^ 2 = 1)
    (hpyRight : wedgeRight ^ 2 + dotRight ^ 2 = 1)
    (hcross : wedgeLeft * wedgeRight = dotLeft * dotRight - dotBase)
    (hwLeft : 0 ≤ wedgeLeft) (hwRight : 0 ≤ wedgeRight) :
    halfSin dotLeft * halfCos dotRight + halfCos dotLeft * halfSin dotRight
      = halfSin dotBase := by
  have hdotLeft : dotLeft ^ 2 ≤ 1 := by nlinarith [sq_nonneg wedgeLeft]
  have hdotRight : dotRight ^ 2 ≤ 1 := by nlinarith [sq_nonneg wedgeRight]
  have hcompl : (1 : ℝ) - dotBase ^ 2
      = (dotLeft * wedgeRight + wedgeLeft * dotRight) ^ 2 := by
    linear_combination (-(dotRight ^ 2 + wedgeRight ^ 2)) * hpyLeft - hpyRight
      - (dotLeft * dotRight - wedgeLeft * wedgeRight + dotBase) * hcross
  have hdotBase : dotBase ^ 2 ≤ 1 := by
    nlinarith [hcompl, sq_nonneg (dotLeft * wedgeRight + wedgeLeft * dotRight)]
  refine eq_of_sq_eq_sq_of_nonneg
    (add_nonneg (mul_nonneg (halfSin_nonneg _) (halfCos_nonneg _))
      (mul_nonneg (halfCos_nonneg _) (halfSin_nonneg _)))
    (halfSin_nonneg _) ?_
  have hprodLeft := halfSin_mul_halfCos hpyLeft hwLeft
  have hprodRight := halfSin_mul_halfCos hpyRight hwRight
  have hexpand : (halfSin dotLeft * halfCos dotRight + halfCos dotLeft * halfSin dotRight) ^ 2
      = halfSin dotLeft ^ 2 * halfCos dotRight ^ 2
        + halfCos dotLeft ^ 2 * halfSin dotRight ^ 2
        + 2 * ((halfSin dotLeft * halfCos dotLeft) * (halfSin dotRight * halfCos dotRight)) := by
    ring
  rw [hexpand, halfSin_sq hdotLeft, halfCos_sq hdotLeft, halfSin_sq hdotRight,
    halfCos_sq hdotRight, halfSin_sq hdotBase, hprodLeft, hprodRight]
  linear_combination (1 / 2 : ℝ) * hcross

/-- **THE COSINE SUM LAW.**  The difference form of the half quantities gives
the cosine half quantity of the Binet-Cauchy combination, when the two dot
products have a nonpositive sum. -/
theorem halfCos_diff_eq {dotBase dotLeft dotRight wedgeLeft wedgeRight : ℝ}
    (hpyLeft : wedgeLeft ^ 2 + dotLeft ^ 2 = 1)
    (hpyRight : wedgeRight ^ 2 + dotRight ^ 2 = 1)
    (hcross : wedgeLeft * wedgeRight = dotLeft * dotRight - dotBase)
    (hwLeft : 0 ≤ wedgeLeft) (hwRight : 0 ≤ wedgeRight)
    (hsign : dotLeft + dotRight ≤ 0) :
    halfSin dotLeft * halfSin dotRight - halfCos dotLeft * halfCos dotRight
      = halfCos dotBase := by
  have hdotLeft : dotLeft ^ 2 ≤ 1 := by nlinarith [sq_nonneg wedgeLeft]
  have hdotRight : dotRight ^ 2 ≤ 1 := by nlinarith [sq_nonneg wedgeRight]
  have hcompl : (1 : ℝ) - dotBase ^ 2
      = (dotLeft * wedgeRight + wedgeLeft * dotRight) ^ 2 := by
    linear_combination (-(dotRight ^ 2 + wedgeRight ^ 2)) * hpyLeft - hpyRight
      - (dotLeft * dotRight - wedgeLeft * wedgeRight + dotBase) * hcross
  have hdotBase : dotBase ^ 2 ≤ 1 := by
    nlinarith [hcompl, sq_nonneg (dotLeft * wedgeRight + wedgeLeft * dotRight)]
  have horder : halfCos dotLeft * halfCos dotRight ≤ halfSin dotLeft * halfSin dotRight := by
    refine le_of_sq_le_sq_of_nonneg
      (mul_nonneg (halfSin_nonneg _) (halfSin_nonneg _)) ?_
    have hcc : (halfCos dotLeft * halfCos dotRight) ^ 2
        = halfCos dotLeft ^ 2 * halfCos dotRight ^ 2 := by ring
    have hss : (halfSin dotLeft * halfSin dotRight) ^ 2
        = halfSin dotLeft ^ 2 * halfSin dotRight ^ 2 := by ring
    rw [hcc, hss, halfCos_sq hdotLeft, halfCos_sq hdotRight, halfSin_sq hdotLeft,
      halfSin_sq hdotRight]
    nlinarith [hsign]
  refine eq_of_sq_eq_sq_of_nonneg (by linarith) (halfCos_nonneg _) ?_
  have hprodLeft := halfSin_mul_halfCos hpyLeft hwLeft
  have hprodRight := halfSin_mul_halfCos hpyRight hwRight
  have hexpand : (halfSin dotLeft * halfSin dotRight - halfCos dotLeft * halfCos dotRight) ^ 2
      = halfSin dotLeft ^ 2 * halfSin dotRight ^ 2
        + halfCos dotLeft ^ 2 * halfCos dotRight ^ 2
        - 2 * ((halfSin dotLeft * halfCos dotLeft) * (halfSin dotRight * halfCos dotRight)) := by
    ring
  rw [hexpand, halfSin_sq hdotLeft, halfCos_sq hdotLeft, halfSin_sq hdotRight,
    halfCos_sq hdotRight, halfCos_sq hdotBase, hprodLeft, hprodRight]
  linear_combination (-1 / 2 : ℝ) * hcross

/-! ## Layer 4 — the two vertex evaluations -/

/-- **THE TIGHT VERTEX.**  When every capped product stays below the opposite
cosine product, the three terms price out termwise, and the sum laws collapse
the budget to the sine product exactly. -/
theorem half_form_le_of_tight (sinOne cosOne sinTwo cosTwo sinThree cosThree
    ratioOne ratioTwo ratioThree : ℝ)
    (hsinOne : 0 ≤ sinOne) (hsinTwo : 0 ≤ sinTwo) (hsinThree : 0 ≤ sinThree)
    (haddOne : sinTwo * cosThree + cosTwo * sinThree = sinOne)
    (hdiffOne : sinTwo * sinThree - cosTwo * cosThree = cosOne)
    (hcaseOne : cosOne * ratioOne ≤ cosTwo * cosThree)
    (hcaseTwo : cosTwo * ratioTwo ≤ cosThree * cosOne)
    (hcaseThree : cosThree * ratioThree ≤ cosOne * cosTwo) :
    sinOne * (cosOne * ratioOne) + sinTwo * (cosTwo * ratioTwo)
      + sinThree * (cosThree * ratioThree) ≤ sinOne * (sinTwo * sinThree) := by
  have honeLe := mul_le_mul_of_nonneg_left hcaseOne hsinOne
  have htwoLe := mul_le_mul_of_nonneg_left hcaseTwo hsinTwo
  have hthreeLe := mul_le_mul_of_nonneg_left hcaseThree hsinThree
  have hcollect : sinOne * (cosTwo * cosThree) + sinTwo * (cosThree * cosOne)
      + sinThree * (cosOne * cosTwo) = sinOne * (sinTwo * sinThree) := by
    linear_combination cosOne * haddOne - sinOne * hdiffOne
  linarith

/-- **THE CAPPED VERTEX.**  When one cosine product crosses its capped product,
that index is the pivot.  Its two pair laws price the other terms, the box
bound closes the quadratic factor, and the sum laws collapse the budget. -/
theorem half_form_le_of_pivot (sinPivot cosPivot sinLeft cosLeft sinRight cosRight
    ratioPivot ratioLeft ratioRight : ℝ)
    (hsinPivot : 0 ≤ sinPivot) (hsinLeft : 0 ≤ sinLeft) (hsinRight : 0 ≤ sinRight)
    (hcosPivot : 0 ≤ cosPivot) (hcosLeft : 0 < cosLeft) (hcosRight : 0 < cosRight)
    (hratioPivot : ratioPivot ≤ 1)
    (haddPivot : sinLeft * cosRight + cosLeft * sinRight = sinPivot)
    (hdiffPivot : sinLeft * sinRight - cosLeft * cosRight = cosPivot)
    (hpairLeft : ratioPivot * ratioLeft ≤ cosRight ^ 2)
    (hpairRight : ratioPivot * ratioRight ≤ cosLeft ^ 2)
    (hpivot : cosLeft * cosRight ≤ cosPivot * ratioPivot) :
    sinPivot * (cosPivot * ratioPivot) + sinLeft * (cosLeft * ratioLeft)
      + sinRight * (cosRight * ratioRight) ≤ sinPivot * (sinLeft * sinRight) := by
  have hratioPos : 0 < ratioPivot := by
    nlinarith [mul_pos hcosLeft hcosRight]
  have hchainLeft : sinLeft * cosLeft * (ratioPivot * ratioLeft)
      ≤ sinLeft * cosLeft * cosRight ^ 2 :=
    mul_le_mul_of_nonneg_left hpairLeft (mul_nonneg hsinLeft hcosLeft.le)
  have hchainRight : sinRight * cosRight * (ratioPivot * ratioRight)
      ≤ sinRight * cosRight * cosLeft ^ 2 :=
    mul_le_mul_of_nonneg_left hpairRight (mul_nonneg hsinRight hcosRight.le)
  have hcollect : sinLeft * cosLeft * cosRight ^ 2 + sinRight * cosRight * cosLeft ^ 2
      = sinPivot * (cosLeft * cosRight) := by
    linear_combination (cosLeft * cosRight) * haddPivot
  have hquad : cosPivot * ratioPivot ^ 2 + cosLeft * cosRight
      ≤ (cosPivot + cosLeft * cosRight) * ratioPivot := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hratioPivot) (sub_nonneg.mpr hpivot)]
  have hstep := mul_le_mul_of_nonneg_left hquad hsinPivot
  have hstepEq : sinPivot * ((cosPivot + cosLeft * cosRight) * ratioPivot)
      = sinPivot * (sinLeft * sinRight) * ratioPivot := by
    have hdiff' : cosPivot + cosLeft * cosRight = sinLeft * sinRight := by linarith
    rw [hdiff']
    ring
  have hmain : (sinPivot * (cosPivot * ratioPivot) + sinLeft * (cosLeft * ratioLeft)
      + sinRight * (cosRight * ratioRight)) * ratioPivot
      ≤ sinPivot * (sinLeft * sinRight) * ratioPivot := by
    nlinarith [hchainLeft, hchainRight, hcollect, hstep, hstepEq]
  have hcancel := le_of_mul_le_mul_right hmain hratioPos
  linarith

/-! ## Layer 5 — the crux: the wedge form is nonpositive -/

/-- **THE ABSTRACT CRUX.**  Three dot products and three positive wedges tied
by the Lagrange and Binet-Cauchy identities, three ratios below one under the
pair law: the wedge form of the levels is nonpositive.

The half calculus opens here.  The case split follows the capped products: the
tight vertex when none crosses, the capped vertex at the crossing index. -/
theorem half_wedge_form_nonpos (dotOne dotTwo dotThree wedgeOne wedgeTwo wedgeThree
    ratioOne ratioTwo ratioThree : ℝ)
    (hpyOne : wedgeOne ^ 2 + dotOne ^ 2 = 1)
    (hpyTwo : wedgeTwo ^ 2 + dotTwo ^ 2 = 1)
    (hpyThree : wedgeThree ^ 2 + dotThree ^ 2 = 1)
    (hbcOne : wedgeTwo * wedgeThree = dotTwo * dotThree - dotOne)
    (hbcTwo : wedgeThree * wedgeOne = dotThree * dotOne - dotTwo)
    (hbcThree : wedgeOne * wedgeTwo = dotOne * dotTwo - dotThree)
    (hratioOneLe : ratioOne ≤ 1) (hratioTwoLe : ratioTwo ≤ 1)
    (hratioThreeLe : ratioThree ≤ 1)
    (hpairOne : 2 * ratioTwo * ratioThree - 1 ≤ dotOne)
    (hpairTwo : 2 * ratioOne * ratioThree - 1 ≤ dotTwo)
    (hpairThree : 2 * ratioOne * ratioTwo - 1 ≤ dotThree)
    (hposOne : 0 < wedgeOne) (hposTwo : 0 < wedgeTwo) (hposThree : 0 < wedgeThree) :
    wedgeOne * (2 * ratioOne - 1) + wedgeTwo * (2 * ratioTwo - 1)
      + wedgeThree * (2 * ratioThree - 1) ≤ 0 := by
  have hdsqOne : dotOne ^ 2 ≤ 1 := by nlinarith [sq_nonneg wedgeOne]
  have hdsqTwo : dotTwo ^ 2 ≤ 1 := by nlinarith [sq_nonneg wedgeTwo]
  have hdsqThree : dotThree ^ 2 ≤ 1 := by nlinarith [sq_nonneg wedgeThree]
  have hsignOne : dotTwo + dotThree ≤ 0 := by
    have hkey : wedgeOne * (wedgeTwo + wedgeThree) = (dotOne - 1) * (dotTwo + dotThree) := by
      linear_combination hbcThree + hbcTwo
    have hdotLt : dotOne < 1 := by
      nlinarith [hpyOne, mul_pos hposOne hposOne, sq_nonneg (dotOne - 1)]
    nlinarith [hkey, mul_pos hposOne (add_pos hposTwo hposThree), hdotLt]
  have hsignTwo : dotThree + dotOne ≤ 0 := by
    have hkey : wedgeTwo * (wedgeThree + wedgeOne) = (dotTwo - 1) * (dotThree + dotOne) := by
      linear_combination hbcOne + hbcThree
    have hdotLt : dotTwo < 1 := by
      nlinarith [hpyTwo, mul_pos hposTwo hposTwo, sq_nonneg (dotTwo - 1)]
    nlinarith [hkey, mul_pos hposTwo (add_pos hposThree hposOne), hdotLt]
  have hsignThree : dotOne + dotTwo ≤ 0 := by
    have hkey : wedgeThree * (wedgeOne + wedgeTwo) = (dotThree - 1) * (dotOne + dotTwo) := by
      linear_combination hbcTwo + hbcOne
    have hdotLt : dotThree < 1 := by
      nlinarith [hpyThree, mul_pos hposThree hposThree, sq_nonneg (dotThree - 1)]
    nlinarith [hkey, mul_pos hposThree (add_pos hposOne hposTwo), hdotLt]
  have hcosOnePos : 0 < halfCos dotOne := by
    refine Real.sqrt_pos.mpr ?_
    nlinarith [hpyOne, mul_pos hposOne hposOne, sq_nonneg (dotOne + 1)]
  have hcosTwoPos : 0 < halfCos dotTwo := by
    refine Real.sqrt_pos.mpr ?_
    nlinarith [hpyTwo, mul_pos hposTwo hposTwo, sq_nonneg (dotTwo + 1)]
  have hcosThreePos : 0 < halfCos dotThree := by
    refine Real.sqrt_pos.mpr ?_
    nlinarith [hpyThree, mul_pos hposThree hposThree, sq_nonneg (dotThree + 1)]
  have haddOne := halfSin_add_eq hpyTwo hpyThree hbcOne hposTwo.le hposThree.le
  have haddTwo := halfSin_add_eq hpyThree hpyOne hbcTwo hposThree.le hposOne.le
  have haddThree := halfSin_add_eq hpyOne hpyTwo hbcThree hposOne.le hposTwo.le
  have hdiffOne := halfCos_diff_eq hpyTwo hpyThree hbcOne hposTwo.le hposThree.le hsignOne
  have hdiffTwo := halfCos_diff_eq hpyThree hpyOne hbcTwo hposThree.le hposOne.le hsignTwo
  have hdiffThree := halfCos_diff_eq hpyOne hpyTwo hbcThree hposOne.le hposTwo.le hsignThree
  have hprodOne := halfSin_mul_halfCos hpyOne hposOne.le
  have hprodTwo := halfSin_mul_halfCos hpyTwo hposTwo.le
  have hprodThree := halfSin_mul_halfCos hpyThree hposThree.le
  have hhalfPairOne : ratioTwo * ratioThree ≤ halfCos dotOne ^ 2 := by
    rw [halfCos_sq hdsqOne]
    linarith [hpairOne]
  have hhalfPairTwo : ratioOne * ratioThree ≤ halfCos dotTwo ^ 2 := by
    rw [halfCos_sq hdsqTwo]
    linarith [hpairTwo]
  have hhalfPairThree : ratioOne * ratioTwo ≤ halfCos dotThree ^ 2 := by
    rw [halfCos_sq hdsqThree]
    linarith [hpairThree]
  have hunitHalfTwo : halfSin dotTwo ^ 2 + halfCos dotTwo ^ 2 = 1 := by
    rw [halfSin_sq hdsqTwo, halfCos_sq hdsqTwo]
    ring
  have hunitHalfThree : halfSin dotThree ^ 2 + halfCos dotThree ^ 2 = 1 := by
    rw [halfSin_sq hdsqThree, halfCos_sq hdsqThree]
    ring
  have hsumHalf : halfSin dotOne * halfCos dotOne + halfSin dotTwo * halfCos dotTwo
      + halfSin dotThree * halfCos dotThree
      = 2 * (halfSin dotOne * (halfSin dotTwo * halfSin dotThree)) := by
    rw [← haddOne, ← hdiffOne]
    linear_combination (-(halfSin dotThree * halfCos dotThree)) * hunitHalfTwo
      + (-(halfSin dotTwo * halfCos dotTwo)) * hunitHalfThree
  have hwedgeOneEq : wedgeOne = 2 * (halfSin dotOne * halfCos dotOne) := by
    rw [hprodOne]
    ring
  have hwedgeTwoEq : wedgeTwo = 2 * (halfSin dotTwo * halfCos dotTwo) := by
    rw [hprodTwo]
    ring
  have hwedgeThreeEq : wedgeThree = 2 * (halfSin dotThree * halfCos dotThree) := by
    rw [hprodThree]
    ring
  rw [hwedgeOneEq, hwedgeTwoEq, hwedgeThreeEq]
  rcases le_or_gt (halfCos dotOne * ratioOne) (halfCos dotTwo * halfCos dotThree) with
    hcaseOne | hcaseOne
  · rcases le_or_gt (halfCos dotTwo * ratioTwo) (halfCos dotThree * halfCos dotOne) with
      hcaseTwo | hcaseTwo
    · rcases le_or_gt (halfCos dotThree * ratioThree) (halfCos dotOne * halfCos dotTwo) with
        hcaseThree | hcaseThree
      · have hbound := half_form_le_of_tight (halfSin dotOne) (halfCos dotOne)
          (halfSin dotTwo) (halfCos dotTwo) (halfSin dotThree) (halfCos dotThree)
          ratioOne ratioTwo ratioThree (halfSin_nonneg _) (halfSin_nonneg _)
          (halfSin_nonneg _) haddOne hdiffOne hcaseOne hcaseTwo hcaseThree
        linarith [hbound, hsumHalf]
      · have hbound := half_form_le_of_pivot (halfSin dotThree) (halfCos dotThree)
          (halfSin dotOne) (halfCos dotOne) (halfSin dotTwo) (halfCos dotTwo)
          ratioThree ratioOne ratioTwo (halfSin_nonneg _) (halfSin_nonneg _)
          (halfSin_nonneg _) (halfCos_nonneg _) hcosOnePos hcosTwoPos hratioThreeLe
          haddThree hdiffThree
          (by rw [mul_comm ratioThree ratioOne]; exact hhalfPairTwo)
          (by rw [mul_comm ratioThree ratioTwo]; exact hhalfPairOne)
          hcaseThree.le
        linarith [hbound, hsumHalf]
    · have hbound := half_form_le_of_pivot (halfSin dotTwo) (halfCos dotTwo)
        (halfSin dotThree) (halfCos dotThree) (halfSin dotOne) (halfCos dotOne)
        ratioTwo ratioThree ratioOne (halfSin_nonneg _) (halfSin_nonneg _)
        (halfSin_nonneg _) (halfCos_nonneg _) hcosThreePos hcosOnePos hratioTwoLe
        haddTwo hdiffTwo
        hhalfPairOne
        (by rw [mul_comm ratioTwo ratioOne]; exact hhalfPairThree)
        hcaseTwo.le
      linarith [hbound, hsumHalf]
  · have hbound := half_form_le_of_pivot (halfSin dotOne) (halfCos dotOne)
      (halfSin dotTwo) (halfCos dotTwo) (halfSin dotThree) (halfCos dotThree)
      ratioOne ratioTwo ratioThree (halfSin_nonneg _) (halfSin_nonneg _)
      (halfSin_nonneg _) (halfCos_nonneg _) hcosTwoPos hcosThreePos hratioOneLe
      haddOne hdiffOne hhalfPairThree hhalfPairTwo hcaseOne.le
    linarith [hbound, hsumHalf]

/-- The crux at a vanished first wedge.  The two remaining readings are equal
or opposite, and the pair law kills one ratio in the opposite case. -/
theorem planeWedge_form_nonpos_of_first_zero
    (unitOne unitTwo unitThree : Fin 2 → ℝ) (ratioOne ratioTwo ratioThree : ℝ)
    (hunitTwo : unitTwo ⬝ᵥ unitTwo = 1) (hunitThree : unitThree ⬝ᵥ unitThree = 1)
    (hratioTwoNonneg : 0 ≤ ratioTwo) (hratioThreeNonneg : 0 ≤ ratioThree)
    (hratioTwoLe : ratioTwo ≤ 1) (hratioThreeLe : ratioThree ≤ 1)
    (hpairTwoThree : 2 * ratioTwo * ratioThree - 1 ≤ unitTwo ⬝ᵥ unitThree)
    (hwedgeTwo : 0 ≤ planeWedge unitThree unitOne)
    (hwedgeThree : 0 ≤ planeWedge unitOne unitTwo)
    (hzero : planeWedge unitTwo unitThree = 0) :
    planeWedge unitTwo unitThree * (2 * ratioOne - 1)
      + planeWedge unitThree unitOne * (2 * ratioTwo - 1)
      + planeWedge unitOne unitTwo * (2 * ratioThree - 1) ≤ 0 := by
  have hpy := planeWedge_sq_add_dot_sq unitTwo unitThree
  rw [hunitTwo, hunitThree, hzero] at hpy
  have hfactor : ((unitTwo ⬝ᵥ unitThree) - 1) * ((unitTwo ⬝ᵥ unitThree) + 1) = 0 := by
    linear_combination hpy
  rcases mul_eq_zero.mp hfactor with hplus | hminus
  · -- the two readings are equal, thus the two remaining wedges cancel
    have hdot : unitTwo ⬝ᵥ unitThree = 1 := by linarith
    have henergy : (unitTwo 0 - unitThree 0) ^ 2 + (unitTwo 1 - unitThree 1) ^ 2 = 0 := by
      rw [dot_fin_two] at hunitTwo hunitThree hdot
      linear_combination hunitTwo + hunitThree - 2 * hdot
    have hcompA : unitTwo 0 - unitThree 0 = 0 := by
      have hsq : (unitTwo 0 - unitThree 0) ^ 2 = 0 :=
        le_antisymm (by nlinarith [sq_nonneg (unitTwo 1 - unitThree 1)]) (sq_nonneg _)
      exact sq_eq_zero_iff.mp hsq
    have hcompB : unitTwo 1 - unitThree 1 = 0 := by
      have hsq : (unitTwo 1 - unitThree 1) ^ 2 = 0 :=
        le_antisymm (by nlinarith [sq_nonneg (unitTwo 0 - unitThree 0)]) (sq_nonneg _)
      exact sq_eq_zero_iff.mp hsq
    have hwsum : planeWedge unitThree unitOne + planeWedge unitOne unitTwo = 0 := by
      simp only [planeWedge]
      linear_combination (-(unitOne 1)) * hcompA + unitOne 0 * hcompB
    have hwTwoZero : planeWedge unitThree unitOne = 0 := by linarith
    have hwThreeZero : planeWedge unitOne unitTwo = 0 := by linarith
    rw [hzero, hwTwoZero, hwThreeZero]
    norm_num
  · -- the two readings are opposite, thus one ratio vanishes
    have hdot : unitTwo ⬝ᵥ unitThree = -1 := by linarith
    have hratioProd : ratioTwo * ratioThree = 0 := by
      refine le_antisymm ?_ (mul_nonneg hratioTwoNonneg hratioThreeNonneg)
      rw [hdot] at hpairTwoThree
      linarith
    have henergy : (unitTwo 0 + unitThree 0) ^ 2 + (unitTwo 1 + unitThree 1) ^ 2 = 0 := by
      rw [dot_fin_two] at hunitTwo hunitThree hdot
      linear_combination hunitTwo + hunitThree + 2 * hdot
    have hcompA : unitTwo 0 + unitThree 0 = 0 := by
      have hsq : (unitTwo 0 + unitThree 0) ^ 2 = 0 :=
        le_antisymm (by nlinarith [sq_nonneg (unitTwo 1 + unitThree 1)]) (sq_nonneg _)
      exact sq_eq_zero_iff.mp hsq
    have hcompB : unitTwo 1 + unitThree 1 = 0 := by
      have hsq : (unitTwo 1 + unitThree 1) ^ 2 = 0 :=
        le_antisymm (by nlinarith [sq_nonneg (unitTwo 0 + unitThree 0)]) (sq_nonneg _)
      exact sq_eq_zero_iff.mp hsq
    have hwmatch : planeWedge unitThree unitOne = planeWedge unitOne unitTwo := by
      simp only [planeWedge]
      linear_combination unitOne 1 * hcompA - unitOne 0 * hcompB
    rw [hzero, hwmatch]
    rcases mul_eq_zero.mp hratioProd with hratioZero | hratioZero
    · rw [hratioZero]
      nlinarith [hwedgeThree, hratioThreeLe]
    · rw [hratioZero]
      nlinarith [hwedgeThree, hratioTwoLe]

/-- **THE CRUX.**  Three unit readings of the plane with nonnegative wedges,
three ratios of the unit interval, and the pair law: the wedge form of the
levels is nonpositive.

The probe measures the bound as an exact equality manifold: the tight vertex
and the capped vertex both evaluate to zero. -/
theorem planeWedge_form_nonpos (unitOne unitTwo unitThree : Fin 2 → ℝ)
    (ratioOne ratioTwo ratioThree : ℝ)
    (hunitOne : unitOne ⬝ᵥ unitOne = 1) (hunitTwo : unitTwo ⬝ᵥ unitTwo = 1)
    (hunitThree : unitThree ⬝ᵥ unitThree = 1)
    (hratioOneNonneg : 0 ≤ ratioOne) (hratioTwoNonneg : 0 ≤ ratioTwo)
    (hratioThreeNonneg : 0 ≤ ratioThree)
    (hratioOneLe : ratioOne ≤ 1) (hratioTwoLe : ratioTwo ≤ 1)
    (hratioThreeLe : ratioThree ≤ 1)
    (hpairOneTwo : 2 * ratioOne * ratioTwo - 1 ≤ unitOne ⬝ᵥ unitTwo)
    (hpairOneThree : 2 * ratioOne * ratioThree - 1 ≤ unitOne ⬝ᵥ unitThree)
    (hpairTwoThree : 2 * ratioTwo * ratioThree - 1 ≤ unitTwo ⬝ᵥ unitThree)
    (hwedgeOne : 0 ≤ planeWedge unitTwo unitThree)
    (hwedgeTwo : 0 ≤ planeWedge unitThree unitOne)
    (hwedgeThree : 0 ≤ planeWedge unitOne unitTwo) :
    planeWedge unitTwo unitThree * (2 * ratioOne - 1)
      + planeWedge unitThree unitOne * (2 * ratioTwo - 1)
      + planeWedge unitOne unitTwo * (2 * ratioThree - 1) ≤ 0 := by
  rcases eq_or_lt_of_le hwedgeOne with hzeroOne | hposOne
  · exact planeWedge_form_nonpos_of_first_zero unitOne unitTwo unitThree
      ratioOne ratioTwo ratioThree hunitTwo hunitThree hratioTwoNonneg hratioThreeNonneg
      hratioTwoLe hratioThreeLe hpairTwoThree hwedgeTwo hwedgeThree hzeroOne.symm
  rcases eq_or_lt_of_le hwedgeTwo with hzeroTwo | hposTwo
  · have hrot := planeWedge_form_nonpos_of_first_zero unitTwo unitThree unitOne
      ratioTwo ratioThree ratioOne hunitThree hunitOne hratioThreeNonneg hratioOneNonneg
      hratioThreeLe hratioOneLe
      (by rw [dotProduct_comm unitThree unitOne]; linarith [hpairOneThree])
      hwedgeThree hwedgeOne hzeroTwo.symm
    linarith
  rcases eq_or_lt_of_le hwedgeThree with hzeroThree | hposThree
  · have hrot := planeWedge_form_nonpos_of_first_zero unitThree unitOne unitTwo
      ratioThree ratioOne ratioTwo hunitOne hunitTwo hratioOneNonneg hratioTwoNonneg
      hratioOneLe hratioTwoLe (by linarith [hpairOneTwo]) hwedgeOne hwedgeTwo hzeroThree.symm
    linarith
  have hpyOne : planeWedge unitTwo unitThree ^ 2 + (unitTwo ⬝ᵥ unitThree) ^ 2 = 1 := by
    have hpy := planeWedge_sq_add_dot_sq unitTwo unitThree
    rw [hunitTwo, hunitThree] at hpy
    linarith
  have hpyTwo : planeWedge unitThree unitOne ^ 2 + (unitOne ⬝ᵥ unitThree) ^ 2 = 1 := by
    have hpy := planeWedge_sq_add_dot_sq unitThree unitOne
    rw [hunitThree, hunitOne, dotProduct_comm unitThree unitOne] at hpy
    linarith
  have hpyThree : planeWedge unitOne unitTwo ^ 2 + (unitOne ⬝ᵥ unitTwo) ^ 2 = 1 := by
    have hpy := planeWedge_sq_add_dot_sq unitOne unitTwo
    rw [hunitOne, hunitTwo] at hpy
    linarith
  have hbcOne : planeWedge unitThree unitOne * planeWedge unitOne unitTwo
      = (unitOne ⬝ᵥ unitThree) * (unitOne ⬝ᵥ unitTwo) - unitTwo ⬝ᵥ unitThree := by
    have hraw := planeWedge_mul_planeWedge unitThree unitOne unitOne unitTwo
    rw [hunitOne, dotProduct_comm unitThree unitOne, dotProduct_comm unitThree unitTwo] at hraw
    linarith
  have hbcTwo : planeWedge unitOne unitTwo * planeWedge unitTwo unitThree
      = (unitOne ⬝ᵥ unitTwo) * (unitTwo ⬝ᵥ unitThree) - unitOne ⬝ᵥ unitThree := by
    have hraw := planeWedge_mul_planeWedge unitOne unitTwo unitTwo unitThree
    rw [hunitTwo] at hraw
    linarith
  have hbcThree : planeWedge unitTwo unitThree * planeWedge unitThree unitOne
      = (unitTwo ⬝ᵥ unitThree) * (unitOne ⬝ᵥ unitThree) - unitOne ⬝ᵥ unitTwo := by
    have hraw := planeWedge_mul_planeWedge unitTwo unitThree unitThree unitOne
    rw [hunitThree, dotProduct_comm unitThree unitOne, dotProduct_comm unitTwo unitOne] at hraw
    linarith
  exact half_wedge_form_nonpos (unitTwo ⬝ᵥ unitThree) (unitOne ⬝ᵥ unitThree)
    (unitOne ⬝ᵥ unitTwo) (planeWedge unitTwo unitThree) (planeWedge unitThree unitOne)
    (planeWedge unitOne unitTwo) ratioOne ratioTwo ratioThree hpyOne hpyTwo hpyThree
    hbcOne hbcTwo hbcThree hratioOneLe hratioTwoLe hratioThreeLe hpairTwoThree
    hpairOneThree hpairOneTwo hposOne hposTwo hposThree

/-! ## Layer 6 — the Farkas dispatch -/

/-- **THE VERTEX.**  When one wedge is nonzero and the wedge form of the levels
sits on the correct side, the vertex of the first two boundary lines is a point
of all three half planes. -/
theorem exists_point_of_vertex (vecOne vecTwo vecThree : Fin 2 → ℝ)
    (levelOne levelTwo levelThree : ℝ)
    (hwedge : planeWedge vecOne vecTwo ≠ 0)
    (hsign : (planeWedge vecTwo vecThree * levelOne + planeWedge vecThree vecOne * levelTwo
        + planeWedge vecOne vecTwo * levelThree) * planeWedge vecOne vecTwo ≤ 0) :
    ∃ point : Fin 2 → ℝ, levelOne ≤ point ⬝ᵥ vecOne ∧ levelTwo ≤ point ⬝ᵥ vecTwo
      ∧ levelThree ≤ point ⬝ᵥ vecThree := by
  refine ⟨![(levelOne * vecTwo 1 - levelTwo * vecOne 1) / planeWedge vecOne vecTwo,
    (levelTwo * vecOne 0 - levelOne * vecTwo 0) / planeWedge vecOne vecTwo], ?_, ?_, ?_⟩
  · rw [dot_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hvalue : (levelOne * vecTwo 1 - levelTwo * vecOne 1) / planeWedge vecOne vecTwo
          * vecOne 0
        + (levelTwo * vecOne 0 - levelOne * vecTwo 0) / planeWedge vecOne vecTwo
          * vecOne 1 = levelOne := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hwedge]
      simp only [planeWedge]
      ring
    rw [hvalue]
  · rw [dot_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hvalue : (levelOne * vecTwo 1 - levelTwo * vecOne 1) / planeWedge vecOne vecTwo
          * vecTwo 0
        + (levelTwo * vecOne 0 - levelOne * vecTwo 0) / planeWedge vecOne vecTwo
          * vecTwo 1 = levelTwo := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hwedge]
      simp only [planeWedge]
      ring
    rw [hvalue]
  · rw [dot_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hvalue : ((levelOne * vecTwo 1 - levelTwo * vecOne 1) / planeWedge vecOne vecTwo
          * vecThree 0
        + (levelTwo * vecOne 0 - levelOne * vecTwo 0) / planeWedge vecOne vecTwo
          * vecThree 1 - levelThree) * planeWedge vecOne vecTwo ^ 2
        = -((planeWedge vecTwo vecThree * levelOne + planeWedge vecThree vecOne * levelTwo
            + planeWedge vecOne vecTwo * levelThree) * planeWedge vecOne vecTwo) := by
      field_simp
      simp only [planeWedge]
      ring
    have hwsq : 0 < planeWedge vecOne vecTwo ^ 2 := by positivity
    nlinarith [hvalue, hsign, hwsq]

/-- **THE LINE.**  When the second and the third wedge vanish, the three
readings share one line, and a multiple of the first reading is the point.  The
pair law supplies the interval consistency. -/
theorem exists_point_of_collinear (unitOne unitTwo unitThree : Fin 2 → ℝ)
    (ratioOne ratioTwo ratioThree : ℝ)
    (hunitOne : unitOne ⬝ᵥ unitOne = 1) (hunitTwo : unitTwo ⬝ᵥ unitTwo = 1)
    (hunitThree : unitThree ⬝ᵥ unitThree = 1)
    (hratioOneNonneg : 0 ≤ ratioOne) (hratioTwoNonneg : 0 ≤ ratioTwo)
    (hratioThreeNonneg : 0 ≤ ratioThree)
    (hratioOneLe : ratioOne ≤ 1) (hratioTwoLe : ratioTwo ≤ 1)
    (hratioThreeLe : ratioThree ≤ 1)
    (hpairOneTwo : 2 * ratioOne * ratioTwo - 1 ≤ unitOne ⬝ᵥ unitTwo)
    (hpairOneThree : 2 * ratioOne * ratioThree - 1 ≤ unitOne ⬝ᵥ unitThree)
    (hpairTwoThree : 2 * ratioTwo * ratioThree - 1 ≤ unitTwo ⬝ᵥ unitThree)
    (hwedgeThree : planeWedge unitOne unitTwo = 0)
    (hwedgeTwo : planeWedge unitThree unitOne = 0) :
    ∃ point : Fin 2 → ℝ, 2 * ratioOne - 1 ≤ point ⬝ᵥ unitOne
      ∧ 2 * ratioTwo - 1 ≤ point ⬝ᵥ unitTwo
      ∧ 2 * ratioThree - 1 ≤ point ⬝ᵥ unitThree := by
  have hsumLe : ∀ ratioA ratioB : ℝ, 0 ≤ ratioA → 0 ≤ ratioB → ratioA ≤ 1 → ratioB ≤ 1 →
      ratioA * ratioB ≤ 0 → ratioA + ratioB ≤ 1 := by
    intro ratioA ratioB hA hB hA' hB' hprod
    have hzero : ratioA * ratioB = 0 := le_antisymm hprod (mul_nonneg hA hB)
    rcases mul_eq_zero.mp hzero with hcase | hcase
    · rw [hcase]; linarith
    · rw [hcase]; linarith
  have hpyTwo := planeWedge_sq_add_dot_sq unitOne unitTwo
  rw [hunitOne, hunitTwo, hwedgeThree] at hpyTwo
  have hfacTwo : ((unitOne ⬝ᵥ unitTwo) - 1) * ((unitOne ⬝ᵥ unitTwo) + 1) = 0 := by
    linear_combination hpyTwo
  have hpyThree := planeWedge_sq_add_dot_sq unitThree unitOne
  rw [hunitThree, hunitOne, hwedgeTwo] at hpyThree
  have hfacThree : ((unitThree ⬝ᵥ unitOne) - 1) * ((unitThree ⬝ᵥ unitOne) + 1) = 0 := by
    linear_combination hpyThree
  have hcross : unitTwo ⬝ᵥ unitThree = (unitOne ⬝ᵥ unitTwo) * (unitThree ⬝ᵥ unitOne) := by
    have hraw := planeWedge_mul_planeWedge unitTwo unitOne unitThree unitOne
    have hanti : planeWedge unitTwo unitOne = -planeWedge unitOne unitTwo := by
      simp only [planeWedge]
      ring
    rw [hanti, hwedgeThree, neg_zero, hunitOne, dotProduct_comm unitTwo unitOne,
      dotProduct_comm unitOne unitThree] at hraw
    nlinarith [hraw]
  have hreadOne : ∀ level : ℝ, (level • unitOne) ⬝ᵥ unitOne = level := by
    intro level
    rw [smul_dotProduct, hunitOne, smul_eq_mul, mul_one]
  have hreadTwo : ∀ level : ℝ, (level • unitOne) ⬝ᵥ unitTwo
      = level * (unitOne ⬝ᵥ unitTwo) := by
    intro level
    rw [smul_dotProduct, smul_eq_mul]
  have hreadThree : ∀ level : ℝ, (level • unitOne) ⬝ᵥ unitThree
      = level * (unitThree ⬝ᵥ unitOne) := by
    intro level
    rw [smul_dotProduct, smul_eq_mul, dotProduct_comm unitOne unitThree]
  rcases mul_eq_zero.mp hfacTwo with hTwoPos | hTwoNeg
  · have hdotTwo : unitOne ⬝ᵥ unitTwo = 1 := by linarith
    rcases mul_eq_zero.mp hfacThree with hThreePos | hThreeNeg
    · have hdotThree : unitThree ⬝ᵥ unitOne = 1 := by linarith
      refine ⟨(max (2 * ratioOne - 1) (max (2 * ratioTwo - 1) (2 * ratioThree - 1)))
        • unitOne, ?_, ?_, ?_⟩
      · rw [hreadOne]
        exact le_max_left _ _
      · rw [hreadTwo, hdotTwo, mul_one]
        exact le_trans (le_max_left _ _) (le_max_right _ _)
      · rw [hreadThree, hdotThree, mul_one]
        exact le_trans (le_max_right _ _) (le_max_right _ _)
    · have hdotThree : unitThree ⬝ᵥ unitOne = -1 := by linarith
      have hconsOneThree : ratioOne + ratioThree ≤ 1 := by
        refine hsumLe ratioOne ratioThree hratioOneNonneg hratioThreeNonneg
          hratioOneLe hratioThreeLe ?_
        have hval : unitOne ⬝ᵥ unitThree = -1 := by
          rw [dotProduct_comm unitOne unitThree]
          exact hdotThree
        rw [hval] at hpairOneThree
        linarith
      have hconsTwoThree : ratioTwo + ratioThree ≤ 1 := by
        refine hsumLe ratioTwo ratioThree hratioTwoNonneg hratioThreeNonneg
          hratioTwoLe hratioThreeLe ?_
        rw [hcross, hdotTwo, hdotThree] at hpairTwoThree
        linarith
      refine ⟨(max (2 * ratioOne - 1) (2 * ratioTwo - 1)) • unitOne, ?_, ?_, ?_⟩
      · rw [hreadOne]
        exact le_max_left _ _
      · rw [hreadTwo, hdotTwo, mul_one]
        exact le_max_right _ _
      · rw [hreadThree, hdotThree]
        have hcap : max (2 * ratioOne - 1) (2 * ratioTwo - 1) ≤ 1 - 2 * ratioThree :=
          max_le (by linarith) (by linarith)
        linarith
  · have hdotTwo : unitOne ⬝ᵥ unitTwo = -1 := by linarith
    have hconsOneTwo : ratioOne + ratioTwo ≤ 1 := by
      refine hsumLe ratioOne ratioTwo hratioOneNonneg hratioTwoNonneg
        hratioOneLe hratioTwoLe ?_
      rw [hdotTwo] at hpairOneTwo
      linarith
    rcases mul_eq_zero.mp hfacThree with hThreePos | hThreeNeg
    · have hdotThree : unitThree ⬝ᵥ unitOne = 1 := by linarith
      have hconsTwoThree : ratioTwo + ratioThree ≤ 1 := by
        refine hsumLe ratioTwo ratioThree hratioTwoNonneg hratioThreeNonneg
          hratioTwoLe hratioThreeLe ?_
        rw [hcross, hdotTwo, hdotThree] at hpairTwoThree
        linarith
      refine ⟨(max (2 * ratioOne - 1) (2 * ratioThree - 1)) • unitOne, ?_, ?_, ?_⟩
      · rw [hreadOne]
        exact le_max_left _ _
      · rw [hreadTwo, hdotTwo]
        have hcap : max (2 * ratioOne - 1) (2 * ratioThree - 1) ≤ 1 - 2 * ratioTwo :=
          max_le (by linarith) (by linarith)
        linarith
      · rw [hreadThree, hdotThree, mul_one]
        exact le_max_right _ _
    · have hdotThree : unitThree ⬝ᵥ unitOne = -1 := by linarith
      have hconsOneThree : ratioOne + ratioThree ≤ 1 := by
        refine hsumLe ratioOne ratioThree hratioOneNonneg hratioThreeNonneg
          hratioOneLe hratioThreeLe ?_
        have hval : unitOne ⬝ᵥ unitThree = -1 := by
          rw [dotProduct_comm unitOne unitThree]
          exact hdotThree
        rw [hval] at hpairOneThree
        linarith
      refine ⟨(2 * ratioOne - 1) • unitOne, ?_, ?_, ?_⟩
      · rw [hreadOne]
      · rw [hreadTwo, hdotTwo]
        linarith
      · rw [hreadThree, hdotThree]
        linarith

/-- **THE DISPATCH.**  Three unit readings with ratios of the unit interval and
the pair law always admit a point of the three half planes.  The crux and its
reflection pin the sign of the wedge form, and a vertex or a line supplies the
point. -/
theorem exists_point_of_unit_triple (unitOne unitTwo unitThree : Fin 2 → ℝ)
    (ratioOne ratioTwo ratioThree : ℝ)
    (hunitOne : unitOne ⬝ᵥ unitOne = 1) (hunitTwo : unitTwo ⬝ᵥ unitTwo = 1)
    (hunitThree : unitThree ⬝ᵥ unitThree = 1)
    (hratioOneNonneg : 0 ≤ ratioOne) (hratioTwoNonneg : 0 ≤ ratioTwo)
    (hratioThreeNonneg : 0 ≤ ratioThree)
    (hratioOneLe : ratioOne ≤ 1) (hratioTwoLe : ratioTwo ≤ 1)
    (hratioThreeLe : ratioThree ≤ 1)
    (hpairOneTwo : 2 * ratioOne * ratioTwo - 1 ≤ unitOne ⬝ᵥ unitTwo)
    (hpairOneThree : 2 * ratioOne * ratioThree - 1 ≤ unitOne ⬝ᵥ unitThree)
    (hpairTwoThree : 2 * ratioTwo * ratioThree - 1 ≤ unitTwo ⬝ᵥ unitThree) :
    ∃ point : Fin 2 → ℝ, 2 * ratioOne - 1 ≤ point ⬝ᵥ unitOne
      ∧ 2 * ratioTwo - 1 ≤ point ⬝ᵥ unitTwo
      ∧ 2 * ratioThree - 1 ≤ point ⬝ᵥ unitThree := by
  classical
  have hcruxPos : 0 ≤ planeWedge unitTwo unitThree → 0 ≤ planeWedge unitThree unitOne →
      0 ≤ planeWedge unitOne unitTwo →
      planeWedge unitTwo unitThree * (2 * ratioOne - 1)
        + planeWedge unitThree unitOne * (2 * ratioTwo - 1)
        + planeWedge unitOne unitTwo * (2 * ratioThree - 1) ≤ 0 :=
    fun hOne hTwo hThree => planeWedge_form_nonpos unitOne unitTwo unitThree
      ratioOne ratioTwo ratioThree hunitOne hunitTwo hunitThree hratioOneNonneg
      hratioTwoNonneg hratioThreeNonneg hratioOneLe hratioTwoLe hratioThreeLe
      hpairOneTwo hpairOneThree hpairTwoThree hOne hTwo hThree
  have hcruxNeg : planeWedge unitTwo unitThree ≤ 0 → planeWedge unitThree unitOne ≤ 0 →
      planeWedge unitOne unitTwo ≤ 0 →
      0 ≤ planeWedge unitTwo unitThree * (2 * ratioOne - 1)
        + planeWedge unitThree unitOne * (2 * ratioTwo - 1)
        + planeWedge unitOne unitTwo * (2 * ratioThree - 1) := by
    intro hOne hTwo hThree
    have hkey := planeWedge_form_nonpos (planeReflect unitOne) (planeReflect unitTwo)
      (planeReflect unitThree) ratioOne ratioTwo ratioThree
      (by rw [planeReflect_dot]; exact hunitOne)
      (by rw [planeReflect_dot]; exact hunitTwo)
      (by rw [planeReflect_dot]; exact hunitThree)
      hratioOneNonneg hratioTwoNonneg hratioThreeNonneg
      hratioOneLe hratioTwoLe hratioThreeLe
      (by rw [planeReflect_dot]; exact hpairOneTwo)
      (by rw [planeReflect_dot]; exact hpairOneThree)
      (by rw [planeReflect_dot]; exact hpairTwoThree)
      (by rw [planeWedge_planeReflect]; linarith)
      (by rw [planeWedge_planeReflect]; linarith)
      (by rw [planeWedge_planeReflect]; linarith)
    rw [planeWedge_planeReflect, planeWedge_planeReflect, planeWedge_planeReflect] at hkey
    linarith
  set formTotal := planeWedge unitTwo unitThree * (2 * ratioOne - 1)
    + planeWedge unitThree unitOne * (2 * ratioTwo - 1)
    + planeWedge unitOne unitTwo * (2 * ratioThree - 1) with hformDef
  rcases lt_trichotomy formTotal 0 with hform | hform | hform
  · rcases le_or_gt (planeWedge unitOne unitTwo) 0 with hwedgeThreeNonpos | hwedge
    · rcases le_or_gt (planeWedge unitTwo unitThree) 0 with hwedgeOneNonpos | hwedge
      · rcases le_or_gt (planeWedge unitThree unitOne) 0 with hwedgeTwoNonpos | hwedge
        · exact absurd (hcruxNeg hwedgeOneNonpos hwedgeTwoNonpos hwedgeThreeNonpos)
            (not_le.mpr hform)
        · obtain ⟨point, hThree, hOne, hTwo⟩ := exists_point_of_vertex unitThree unitOne
            unitTwo (2 * ratioThree - 1) (2 * ratioOne - 1) (2 * ratioTwo - 1)
            (ne_of_gt hwedge) (by nlinarith [hform, hformDef, hwedge])
          exact ⟨point, hOne, hTwo, hThree⟩
      · obtain ⟨point, hTwo, hThree, hOne⟩ := exists_point_of_vertex unitTwo unitThree
          unitOne (2 * ratioTwo - 1) (2 * ratioThree - 1) (2 * ratioOne - 1)
          (ne_of_gt hwedge) (by nlinarith [hform, hformDef, hwedge])
        exact ⟨point, hOne, hTwo, hThree⟩
    · obtain ⟨point, hOne, hTwo, hThree⟩ := exists_point_of_vertex unitOne unitTwo unitThree
        (2 * ratioOne - 1) (2 * ratioTwo - 1) (2 * ratioThree - 1) (ne_of_gt hwedge)
        (by nlinarith [hform, hformDef, hwedge])
      exact ⟨point, hOne, hTwo, hThree⟩
  · have hsumZero : planeWedge unitTwo unitThree * (2 * ratioOne - 1)
        + planeWedge unitThree unitOne * (2 * ratioTwo - 1)
        + planeWedge unitOne unitTwo * (2 * ratioThree - 1) = 0 := by
      rw [← hformDef]
      exact hform
    rcases eq_or_ne (planeWedge unitOne unitTwo) 0 with hzeroThree | hneThree
    · rcases eq_or_ne (planeWedge unitThree unitOne) 0 with hzeroTwo | hneTwo
      · exact exists_point_of_collinear unitOne unitTwo unitThree ratioOne ratioTwo
          ratioThree hunitOne hunitTwo hunitThree hratioOneNonneg hratioTwoNonneg
          hratioThreeNonneg hratioOneLe hratioTwoLe hratioThreeLe hpairOneTwo
          hpairOneThree hpairTwoThree hzeroThree hzeroTwo
      · obtain ⟨point, hThree, hOne, hTwo⟩ := exists_point_of_vertex unitThree unitOne
          unitTwo (2 * ratioThree - 1) (2 * ratioOne - 1) (2 * ratioTwo - 1) hneTwo
          (le_of_eq (by linear_combination planeWedge unitThree unitOne * hsumZero))
        exact ⟨point, hOne, hTwo, hThree⟩
    · obtain ⟨point, hOne, hTwo, hThree⟩ := exists_point_of_vertex unitOne unitTwo unitThree
        (2 * ratioOne - 1) (2 * ratioTwo - 1) (2 * ratioThree - 1) hneThree
        (le_of_eq (by linear_combination planeWedge unitOne unitTwo * hsumZero))
      exact ⟨point, hOne, hTwo, hThree⟩
  · rcases le_or_gt 0 (planeWedge unitOne unitTwo) with hwedgeThreeNonneg | hwedge
    · rcases le_or_gt 0 (planeWedge unitTwo unitThree) with hwedgeOneNonneg | hwedge
      · rcases le_or_gt 0 (planeWedge unitThree unitOne) with hwedgeTwoNonneg | hwedge
        · exact absurd (hcruxPos hwedgeOneNonneg hwedgeTwoNonneg hwedgeThreeNonneg)
            (not_le.mpr hform)
        · obtain ⟨point, hThree, hOne, hTwo⟩ := exists_point_of_vertex unitThree unitOne
            unitTwo (2 * ratioThree - 1) (2 * ratioOne - 1) (2 * ratioTwo - 1)
            (ne_of_lt hwedge) (by nlinarith [hform, hformDef, hwedge])
          exact ⟨point, hOne, hTwo, hThree⟩
      · obtain ⟨point, hTwo, hThree, hOne⟩ := exists_point_of_vertex unitTwo unitThree
          unitOne (2 * ratioTwo - 1) (2 * ratioThree - 1) (2 * ratioOne - 1)
          (ne_of_lt hwedge) (by nlinarith [hform, hformDef, hwedge])
        exact ⟨point, hOne, hTwo, hThree⟩
    · obtain ⟨point, hOne, hTwo, hThree⟩ := exists_point_of_vertex unitOne unitTwo unitThree
        (2 * ratioOne - 1) (2 * ratioTwo - 1) (2 * ratioThree - 1) (ne_of_lt hwedge)
        (by nlinarith [hform, hformDef, hwedge])
      exact ⟨point, hOne, hTwo, hThree⟩

/-! ## Layer 7 — the half-plane leaf is a theorem -/

/-- **THE HALF-PLANE LEAF IS A THEOREM.**  Three half planes of the doubled
reading, tied by the pair law, always meet.  This closes the one leaf that the
leaf split left open. -/
theorem planeHalfTripleClosed_holds : PlaneHalfTripleClosed := by
  intro read energy gap henergy hgapNonneg hgapLe hpair
  classical
  have henergyNonneg : ∀ index, (0 : ℝ) ≤ energy index := fun index =>
    le_trans (hgapNonneg index) (hgapLe index)
  have hvanish : ∀ index, energy index = 0 → ∀ point : Fin 2 → ℝ,
      2 * gap index - energy index ≤ point ⬝ᵥ read index := by
    intro index hzero point
    have hread : read index = 0 := by
      apply dotProduct_self_eq_zero.mp
      rw [henergy index, hzero]
      ring
    have hgapZero : gap index = 0 := by
      have hle := hgapLe index
      rw [hzero] at hle
      exact le_antisymm hle (hgapNonneg index)
    rw [hread, dotProduct_zero, hgapZero, hzero]
    norm_num
  rcases eq_or_lt_of_le (henergyNonneg 0) with hzeroA | hposA
  · obtain ⟨point, _, hOne, hTwo⟩ := exists_capPoint_of_two (read 1) (read 2)
      (energy 1) (energy 2) (gap 1) (gap 2) (henergy 1) (henergy 2) (hgapNonneg 1)
      (hgapNonneg 2) (hgapLe 1) (hgapLe 2) (hpair 1 2)
    refine ⟨point, fun index => ?_⟩
    fin_cases index
    · simpa using hvanish 0 hzeroA.symm point
    · simpa using hOne
    · simpa using hTwo
  rcases eq_or_lt_of_le (henergyNonneg 1) with hzeroB | hposB
  · obtain ⟨point, _, hOne, hTwo⟩ := exists_capPoint_of_two (read 0) (read 2)
      (energy 0) (energy 2) (gap 0) (gap 2) (henergy 0) (henergy 2) (hgapNonneg 0)
      (hgapNonneg 2) (hgapLe 0) (hgapLe 2) (hpair 0 2)
    refine ⟨point, fun index => ?_⟩
    fin_cases index
    · simpa using hOne
    · simpa using hvanish 1 hzeroB.symm point
    · simpa using hTwo
  rcases eq_or_lt_of_le (henergyNonneg 2) with hzeroC | hposC
  · obtain ⟨point, _, hOne, hTwo⟩ := exists_capPoint_of_two (read 0) (read 1)
      (energy 0) (energy 1) (gap 0) (gap 1) (henergy 0) (henergy 1) (hgapNonneg 0)
      (hgapNonneg 1) (hgapLe 0) (hgapLe 1) (hpair 0 1)
    refine ⟨point, fun index => ?_⟩
    fin_cases index
    · simpa using hOne
    · simpa using hTwo
    · simpa using hvanish 2 hzeroC.symm point
  have hpos : ∀ index : Fin 3, 0 < energy index := by
    intro index
    fin_cases index
    · simpa using hposA
    · simpa using hposB
    · simpa using hposC
  have hunit : ∀ index, ((energy index)⁻¹ • read index) ⬝ᵥ ((energy index)⁻¹ • read index)
      = 1 := by
    intro index
    have hne := ne_of_gt (hpos index)
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, henergy index]
    field_simp
  have hpairNorm : ∀ indexOne indexTwo : Fin 3,
      2 * (gap indexOne / energy indexOne) * (gap indexTwo / energy indexTwo) - 1
        ≤ ((energy indexOne)⁻¹ • read indexOne) ⬝ᵥ ((energy indexTwo)⁻¹ • read indexTwo) := by
    intro indexOne indexTwo
    have hneOne := ne_of_gt (hpos indexOne)
    have hneTwo := ne_of_gt (hpos indexTwo)
    have hcross : ((energy indexOne)⁻¹ • read indexOne)
          ⬝ᵥ ((energy indexTwo)⁻¹ • read indexTwo)
        = (read indexOne ⬝ᵥ read indexTwo) / (energy indexOne * energy indexTwo) := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      field_simp
    rw [hcross, le_div_iff₀ (mul_pos (hpos indexOne) (hpos indexTwo))]
    have hexpand : (2 * (gap indexOne / energy indexOne) * (gap indexTwo / energy indexTwo)
          - 1) * (energy indexOne * energy indexTwo)
        = 2 * gap indexOne * gap indexTwo - energy indexOne * energy indexTwo := by
      field_simp
    rw [hexpand]
    exact hpair indexOne indexTwo
  obtain ⟨point, hOne, hTwo, hThree⟩ := exists_point_of_unit_triple
    ((energy 0)⁻¹ • read 0) ((energy 1)⁻¹ • read 1) ((energy 2)⁻¹ • read 2)
    (gap 0 / energy 0) (gap 1 / energy 1) (gap 2 / energy 2)
    (hunit 0) (hunit 1) (hunit 2)
    (div_nonneg (hgapNonneg 0) (henergyNonneg 0))
    (div_nonneg (hgapNonneg 1) (henergyNonneg 1))
    (div_nonneg (hgapNonneg 2) (henergyNonneg 2))
    ((div_le_one (hpos 0)).mpr (hgapLe 0))
    ((div_le_one (hpos 1)).mpr (hgapLe 1))
    ((div_le_one (hpos 2)).mpr (hgapLe 2))
    (hpairNorm 0 1) (hpairNorm 0 2) (hpairNorm 1 2)
  have htransport : ∀ index : Fin 3,
      2 * (gap index / energy index) - 1 ≤ point ⬝ᵥ ((energy index)⁻¹ • read index) →
      2 * gap index - energy index ≤ point ⬝ᵥ read index := by
    intro index hbound
    have hne := ne_of_gt (hpos index)
    rw [dotProduct_smul, smul_eq_mul] at hbound
    have hkey := mul_le_mul_of_nonneg_left hbound (henergyNonneg index)
    have hleft : energy index * (2 * (gap index / energy index) - 1)
        = 2 * gap index - energy index := by
      field_simp
    have hright : energy index * ((energy index)⁻¹ * (point ⬝ᵥ read index))
        = point ⬝ᵥ read index := by
      field_simp
    rw [hleft, hright] at hkey
    exact hkey
  refine ⟨point, fun index => ?_⟩
  fin_cases index
  · simpa using htransport 0 hOne
  · simpa using htransport 1 hTwo
  · simpa using htransport 2 hThree

/-! ## Layer 8 — the second Helly call, and the residue closes -/

/-- **THE SECOND HELLY CALL.**  The four-set family of the disc and the three
half planes: every three-subset with the disc is the disc leaf, and the one
without the disc is the half-plane leaf. -/
theorem planeCapTripleClosed_of_halfTriple (hhalf : PlaneHalfTripleClosed) :
    PlaneCapTripleClosed := by
  classical
  intro read energy gap henergy hgapNonneg hgapLe hpair
  set family : Fin 4 → Set (Fin 2 → ℝ) :=
    ![planeCap 0 0,
      planeHalf (read 0) (2 * gap 0 - energy 0),
      planeHalf (read 1) (2 * gap 1 - energy 1),
      planeHalf (read 2) (2 * gap 2 - energy 2)] with hfamilyDef
  have hrank : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by simp
  have hcard : Module.finrank ℝ (Fin 2 → ℝ) + 1
      ≤ (Finset.univ : Finset (Fin 4)).card := by
    rw [hrank, Finset.card_univ, Fintype.card_fin]
    norm_num
  have hconvex : ∀ index ∈ (Finset.univ : Finset (Fin 4)), Convex ℝ (family index) := by
    intro index _
    rw [hfamilyDef]
    fin_cases index
    · exact convex_planeCap 0 0
    · exact convex_planeHalf (read 0) (2 * gap 0 - energy 0)
    · exact convex_planeHalf (read 1) (2 * gap 1 - energy 1)
    · exact convex_planeHalf (read 2) (2 * gap 2 - energy 2)
  have hinter : ∀ subset ⊆ (Finset.univ : Finset (Fin 4)),
      subset.card = Module.finrank ℝ (Fin 2 → ℝ) + 1 →
      (⋂ index ∈ subset, family index).Nonempty := by
    intro subset _ hsize
    rw [hrank] at hsize
    have hcompl : subsetᶜ.card = 1 := by
      rw [Finset.card_compl, hsize, Fintype.card_fin]
    obtain ⟨missing, hmissing⟩ := Finset.card_eq_one.mp hcompl
    have hmem : ∀ index : Fin 4, index ∈ subset ↔ index ≠ missing := by
      intro index
      rw [show subset = ({missing}ᶜ : Finset (Fin 4)) by
        rw [← compl_compl subset, hmissing], Finset.mem_compl, Finset.mem_singleton]
    fin_cases missing
    · obtain ⟨point, hpoint⟩ := hhalf read energy gap henergy hgapNonneg hgapLe hpair
      refine ⟨point, ?_⟩
      rw [Set.mem_iInter₂]
      intro index hindex
      have hne := (hmem index).mp hindex
      rw [hfamilyDef]
      fin_cases index
      · exact absurd rfl hne
      · exact hpoint 0
      · exact hpoint 1
      · exact hpoint 2
    · obtain ⟨point, hdisc, hOne, hTwo⟩ := exists_capPoint_of_two (read 1) (read 2)
        (energy 1) (energy 2) (gap 1) (gap 2) (henergy 1) (henergy 2) (hgapNonneg 1)
        (hgapNonneg 2) (hgapLe 1) (hgapLe 2) (hpair 1 2)
      refine ⟨point, ?_⟩
      rw [Set.mem_iInter₂]
      intro index hindex
      have hne := (hmem index).mp hindex
      rw [hfamilyDef]
      fin_cases index
      · exact (planeCap_zero_eq_disc point).mpr hdisc
      · exact absurd rfl hne
      · exact hOne
      · exact hTwo
    · obtain ⟨point, hdisc, hOne, hTwo⟩ := exists_capPoint_of_two (read 0) (read 2)
        (energy 0) (energy 2) (gap 0) (gap 2) (henergy 0) (henergy 2) (hgapNonneg 0)
        (hgapNonneg 2) (hgapLe 0) (hgapLe 2) (hpair 0 2)
      refine ⟨point, ?_⟩
      rw [Set.mem_iInter₂]
      intro index hindex
      have hne := (hmem index).mp hindex
      rw [hfamilyDef]
      fin_cases index
      · exact (planeCap_zero_eq_disc point).mpr hdisc
      · exact hOne
      · exact absurd rfl hne
      · exact hTwo
    · obtain ⟨point, hdisc, hOne, hTwo⟩ := exists_capPoint_of_two (read 0) (read 1)
        (energy 0) (energy 1) (gap 0) (gap 1) (henergy 0) (henergy 1) (hgapNonneg 0)
        (hgapNonneg 1) (hgapLe 0) (hgapLe 1) (hpair 0 1)
      refine ⟨point, ?_⟩
      rw [Set.mem_iInter₂]
      intro index hindex
      have hne := (hmem index).mp hindex
      rw [hfamilyDef]
      fin_cases index
      · exact (planeCap_zero_eq_disc point).mpr hdisc
      · exact hOne
      · exact hTwo
      · exact absurd rfl hne
  obtain ⟨point, hpoint⟩ := Convex.helly_theorem (𝕜 := ℝ) (F := family) hcard hconvex hinter
  rw [Set.mem_iInter₂] at hpoint
  rw [hfamilyDef] at hpoint
  have hdisc : point ⬝ᵥ point ≤ 1 :=
    (planeCap_zero_eq_disc point).mp (hpoint 0 (Finset.mem_univ 0))
  refine ⟨point, hdisc, fun index => ?_⟩
  fin_cases index
  · exact hpoint 1 (Finset.mem_univ 1)
  · exact hpoint 2 (Finset.mem_univ 2)
  · exact hpoint 3 (Finset.mem_univ 3)

/-- **THE THREE-ATOM RESIDUE IS A THEOREM.** -/
theorem planeCapTripleClosed_holds : PlaneCapTripleClosed :=
  planeCapTripleClosed_of_halfTriple planeHalfTripleClosed_holds

/-! ## Layer 9 — the campaign chain, with no hypothesis -/

/-- **THE PAIR GRAM RESIDUE IS A THEOREM.**  Six plane atoms of total scale
below one always carry a dominating pair. -/
theorem atomPairGramClosed_holds : AtomPairGramClosed :=
  atomPairGramClosed_of_capTriple planeCapTripleClosed_holds

/-- **THE PLANE PAIR CEILING IS A THEOREM.** -/
theorem atomPairCeilingClosed_holds : AtomPairCeilingClosed :=
  atomPairCeilingClosed_of_gram atomPairGramClosed_holds

/-- **PROFILE A AT RANK FIVE IS A THEOREM.** -/
theorem rankFiveDenseHeavyFiveClosed_holds : RankFiveDenseHeavyFiveClosed :=
  rankFiveDenseHeavyFiveClosed_of_atomPairGram atomPairGramClosed_holds

/-- **THE RESIDUAL CYCLE CELL OF PROFILE A IS A THEOREM.** -/
theorem rankFiveDenseHeavyFiveDistinctClosed_holds : RankFiveDenseHeavyFiveDistinctClosed :=
  rankFiveDenseHeavyFiveDistinctClosed_of_atomPairGram atomPairGramClosed_holds

/-- **CAMPAIGN INTERIORITY IS A THEOREM.**  Every crux is interior: at every
crux and every atom the shifted weight is positive, with no hypothesis. -/
theorem forall_shifted_weight_pos :
    ∀ (crux : SixThreeCrux) (atomIndex : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex :=
  forall_shifted_weight_pos_of_atomPairGram atomPairGramClosed_holds

/-- The interiority of one crux, with no hypothesis. -/
theorem SixThreeCrux.shifted_weight_pos (crux : SixThreeCrux) (atomIndex : Fin 6) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex :=
  forall_shifted_weight_pos crux atomIndex

/-- **THE BOUNDARY CRUX KILL, WITH NO HYPOTHESIS.**  A crux with a vanished
shifted weight is a contradiction. -/
theorem SixThreeCrux.false_of_shift_zero (crux : SixThreeCrux) {boundary : Fin 6}
    (hzero : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight boundary = 0) : False :=
  crux.false_of_capTriple_of_shift_zero planeCapTripleClosed_holds hzero

end Gtz
