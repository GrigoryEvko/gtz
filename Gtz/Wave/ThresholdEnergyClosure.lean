import Gtz.Wave.MassMomentClosure
import Gtz.Wave.ComplementDualLane
import Gtz.Design.KFourChartClosure
import Gtz.Quantitative.CauchyBinetValueFloor

/-!
# The threshold energy in closed form

`Gtz.jointCrossMoment_eq` discharged the cross term of `Gtz.gapSecondMoment_eq`.
This file discharges the threshold energy, leaving `Gtz.massSecondMoment` as the
only quantity in the second-moment theory of the objective that is not a
polynomial in the two invariants `Gtz.pairSecondMoment` and
`Gtz.levSecondMoment`.

The determinant-weighted sums extended to the full index cube for free, because a
block determinant vanishes on every diagonal of the cube.  The threshold does
NOT vanish there, so the extension costs an inclusion-exclusion over the three
degenerate diagonals.

The engine is a two-slot decomposition.  Writing

    thresholdPairForm a b = 36 * pairMinor a b - 3 * diag a - 3 * diag b

the threshold splits as `t a b + t a c + t b c + 1`, and every full-cube sum of a
product of two such factors collapses onto ONE of three scalars: the double sum
`Gtz.sum_thresholdPairForm_double`, the energy `Gtz.sum_sq_thresholdPairForm`,
and the row energy `Gtz.sum_sq_row_thresholdPairForm`.  The row itself is affine
in the leverage (`Gtz.sum_thresholdPairForm_row`), which is what makes all three
close.

The result is `Gtz.thresholdSecondMoment_eq`:

    thresholdSecondMoment = 7776 * pairSecondMoment + 16848 * levSecondMoment - 12408

in the corpus's ORDERED convention, where `pairSecondMoment` runs over ordered
distinct pairs and the moment itself over ordered distinct triples.
-/

namespace Gtz

open Finset Matrix

/-! ## 1. The pair minor is symmetric

A symmetric form's two-by-two principal minor does not know the order of its two
labels.  Everything below needs this and the corpus does not carry it. -/

section PairMinorComm

variable {size : ℕ}

/-- For a symmetric form the pair minor is symmetric in its two labels. -/
theorem pairMinorAt_comm (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first second : Fin size) :
    pairMinorAt form first second = pairMinorAt form second first := by
  have hentry : form second first = form first second := by
    have := congrFun (congrFun hsymmetric first) second
    simpa only [Matrix.transpose_apply] using this
  simp only [pairMinorAt, hentry]; ring

end PairMinorComm

/-! ## 2. The two-slot piece of the threshold

The threshold is a sum of three copies of one symmetric two-slot form, plus one.
-/

section PairForm

variable (design : WeightedDesign 6 3)

/-- The two-slot piece of the threshold. -/
noncomputable def thresholdPairForm (first second : Fin 6) : ℝ :=
  36 * pairMinorAt (projectionOfDesign design) first second
    - 3 * projectionOfDesign design first first
    - 3 * projectionOfDesign design second second

/-- The two-slot piece is symmetric. -/
theorem thresholdPairForm_comm (first second : Fin 6) :
    thresholdPairForm design first second = thresholdPairForm design second first := by
  simp only [thresholdPairForm,
    pairMinorAt_comm (projectionOfDesign design) (projectionOfDesign_transpose design)
      first second]
  ring

/-- **THE DECOMPOSITION.**  The threshold is the three pair forms of its three
pairs of slots, plus one. -/
theorem projThresholdAt_eq_pairForm (first second third : Fin 6) :
    projThresholdAt (projectionOfDesign design) first second third
      = thresholdPairForm design first second + thresholdPairForm design first third
        + thresholdPairForm design second third + 1 := by
  simp only [projThresholdAt, thresholdPairForm]; ring

end PairForm

/-! ## 3. The three scalars

Every full-cube sum below collapses onto one of these.  The row of the pair form
is affine in the leverage, which is the whole reason the theory closes. -/

section Scalars

variable (design : WeightedDesign 6 3)

private theorem doubleConstMul (value : ℝ) (summand : Fin 6 → Fin 6 → ℝ) :
    ∑ first : Fin 6, ∑ second : Fin 6, value * summand first second
      = value * ∑ first : Fin 6, ∑ second : Fin 6, summand first second := by
  simp only [← Finset.mul_sum]

private theorem tripleConstMul (value : ℝ) (summand : Fin 6 → Fin 6 → Fin 6 → ℝ) :
    ∑ first : Fin 6, ∑ second : Fin 6, ∑ third : Fin 6, value * summand first second third
      = value * ∑ first : Fin 6, ∑ second : Fin 6, ∑ third : Fin 6,
          summand first second third := by
  simp only [← Finset.mul_sum]

/-- **THE ROW OF THE PAIR FORM IS AFFINE IN THE LEVERAGE.** -/
theorem sum_thresholdPairForm_row (label : Fin 6) :
    ∑ other : Fin 6, thresholdPairForm design label other
      = 54 * projectionOfDesign design label label - 9 := by
  classical
  have hmin := sum_pairMinor_projection design label
  have htrace := sum_projectionDiagonal design
  have hsplit : ∑ other : Fin 6, thresholdPairForm design label other
      = 36 * (∑ other : Fin 6, pairMinorAt (projectionOfDesign design) label other)
        - 3 * (∑ _other : Fin 6, projectionOfDesign design label label)
        - 3 * (∑ other : Fin 6, projectionOfDesign design other other) := by
    simp only [thresholdPairForm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsplit, hmin, htrace]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  ring

/-- The double sum of the pair form. -/
theorem sum_thresholdPairForm_double :
    ∑ first : Fin 6, ∑ second : Fin 6, thresholdPairForm design first second = 108 := by
  rw [Finset.sum_congr rfl fun first _ => sum_thresholdPairForm_row design first]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_projectionDiagonal design,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- The diagonal square sum over the full index square, second slot. -/
theorem sum_sq_diag_second_double :
    ∑ _first : Fin 6, ∑ second : Fin 6, projectionOfDesign design second second ^ 2
      = 6 * levSecondMoment design := by
  simp only [levSecondMoment, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  norm_num

/-- The diagonal square sum over the full index square, first slot. -/
theorem sum_sq_diag_first_double :
    ∑ first : Fin 6, ∑ _second : Fin 6, projectionOfDesign design first first ^ 2
      = 6 * levSecondMoment design := by
  have hinner : ∀ first : Fin 6,
      ∑ _second : Fin 6, projectionOfDesign design first first ^ 2
        = 6 * projectionOfDesign design first first ^ 2 := by
    intro first
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [Finset.sum_congr rfl fun first _ => hinner first, ← Finset.mul_sum]
  simp only [levSecondMoment]

/-- The mixed diagonal product over the full index square. -/
theorem sum_diag_mul_diag_full :
    ∑ first : Fin 6, ∑ second : Fin 6,
        projectionOfDesign design first first * projectionOfDesign design second second
      = 9 := by
  have htrace := sum_projectionDiagonal design
  simp only [← Finset.mul_sum, ← Finset.sum_mul, htrace]
  norm_num

/-- The pair minor against the FIRST slot's diagonal. -/
theorem sum_pairMinor_mul_diag_first :
    ∑ first : Fin 6, ∑ second : Fin 6,
        pairMinorAt (projectionOfDesign design) first second
          * projectionOfDesign design first first
      = 2 * levSecondMoment design := by
  have hstep : ∀ first : Fin 6,
      ∑ second : Fin 6, pairMinorAt (projectionOfDesign design) first second
            * projectionOfDesign design first first
        = 2 * projectionOfDesign design first first ^ 2 := by
    intro first
    rw [← Finset.sum_mul, sum_pairMinor_projection design first]
    norm_num; ring
  rw [Finset.sum_congr rfl fun first _ => hstep first, ← Finset.mul_sum]
  simp only [levSecondMoment]

/-- The pair minor against the SECOND slot's diagonal, through the symmetry. -/
theorem sum_pairMinor_mul_diag_second :
    ∑ first : Fin 6, ∑ second : Fin 6,
        pairMinorAt (projectionOfDesign design) first second
          * projectionOfDesign design second second
      = 2 * levSecondMoment design := by
  classical
  have hswap : ∀ first second : Fin 6,
      pairMinorAt (projectionOfDesign design) first second
          * projectionOfDesign design second second
        = pairMinorAt (projectionOfDesign design) second first
          * projectionOfDesign design second second := by
    intro first second
    rw [pairMinorAt_comm (projectionOfDesign design) (projectionOfDesign_transpose design)
      first second]
  rw [Finset.sum_congr rfl fun first _ =>
    Finset.sum_congr rfl fun second _ => hswap first second, Finset.sum_comm]
  exact sum_pairMinor_mul_diag_first design

/-- **THE ENERGY OF THE PAIR FORM.** -/
theorem sum_sq_thresholdPairForm :
    ∑ first : Fin 6, ∑ second : Fin 6, thresholdPairForm design first second ^ 2
      = 1296 * pairSecondMoment design - 756 * levSecondMoment design + 162 := by
  classical
  have hexp : ∀ first second : Fin 6,
      thresholdPairForm design first second ^ 2
        = 1296 * pairMinorAt (projectionOfDesign design) first second ^ 2
          + 9 * projectionOfDesign design first first ^ 2
          + 9 * projectionOfDesign design second second ^ 2
          - 216 * (pairMinorAt (projectionOfDesign design) first second
              * projectionOfDesign design first first)
          - 216 * (pairMinorAt (projectionOfDesign design) first second
              * projectionOfDesign design second second)
          + 18 * (projectionOfDesign design first first
              * projectionOfDesign design second second) := by
    intro first second; simp only [thresholdPairForm]; ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, doubleConstMul]
  rw [sum_sq_pairMinor_full design, sum_diag_mul_diag_full design,
    sum_pairMinor_mul_diag_first design, sum_pairMinor_mul_diag_second design,
    sum_sq_diag_first_double design, sum_sq_diag_second_double design]
  ring

/-- **THE ROW ENERGY OF THE PAIR FORM.** -/
theorem sum_sq_row_thresholdPairForm :
    ∑ first : Fin 6, (∑ second : Fin 6, thresholdPairForm design first second) ^ 2
      = 2916 * levSecondMoment design - 2430 := by
  have htrace := sum_projectionDiagonal design
  have hstep : ∀ first : Fin 6,
      (∑ second : Fin 6, thresholdPairForm design first second) ^ 2
        = 2916 * projectionOfDesign design first first ^ 2
          - 972 * projectionOfDesign design first first + 81 := by
    intro first
    rw [sum_thresholdPairForm_row design first]; ring
  rw [Finset.sum_congr rfl fun first _ => hstep first]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, htrace,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, levSecondMoment]
  ring

/-- The pair form's row weighted by the leverage. -/
theorem sum_diag_mul_row_thresholdPairForm :
    ∑ first : Fin 6, projectionOfDesign design first first
        * (∑ second : Fin 6, thresholdPairForm design first second)
      = 54 * levSecondMoment design - 27 := by
  have htrace := sum_projectionDiagonal design
  have hstep : ∀ first : Fin 6,
      projectionOfDesign design first first
          * (∑ second : Fin 6, thresholdPairForm design first second)
        = 54 * projectionOfDesign design first first ^ 2
          - 9 * projectionOfDesign design first first := by
    intro first
    rw [sum_thresholdPairForm_row design first]; ring
  rw [Finset.sum_congr rfl fun first _ => hstep first]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, htrace, levSecondMoment]
  ring

end Scalars

/-! ## 4. The full index cube

Six factorizations, each collapsing a cube sum onto one of the three scalars.
The symmetry of the pair form is what lets the same scalar serve every slot. -/

section Cube

variable (design : WeightedDesign 6 3)

private theorem constThird (value : ℝ) : ∑ _third : Fin 6, value = 6 * value := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- The first-second pair form over the cube. -/
theorem cube_sum_pair_first_second :
    ∑ first : Fin 6, ∑ second : Fin 6, ∑ _third : Fin 6,
        thresholdPairForm design first second = 648 := by
  simp only [constThird, ← Finset.mul_sum, sum_thresholdPairForm_double design]
  norm_num

/-- The first-third pair form over the cube. -/
theorem cube_sum_pair_first_third :
    ∑ first : Fin 6, ∑ _second : Fin 6, ∑ third : Fin 6,
        thresholdPairForm design first third = 648 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, sum_thresholdPairForm_double design]
  norm_num

/-- The second-third pair form over the cube. -/
theorem cube_sum_pair_second_third :
    ∑ _first : Fin 6, ∑ second : Fin 6, ∑ third : Fin 6,
        thresholdPairForm design second third = 648 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_thresholdPairForm_double design]
  norm_num

/-- The first-second energy over the cube. -/
theorem cube_sum_sq_first_second :
    ∑ first : Fin 6, ∑ second : Fin 6, ∑ _third : Fin 6,
        thresholdPairForm design first second ^ 2
      = 6 * (1296 * pairSecondMoment design - 756 * levSecondMoment design + 162) := by
  simp only [constThird, ← Finset.mul_sum, sum_sq_thresholdPairForm design]

/-- The first-third energy over the cube. -/
theorem cube_sum_sq_first_third :
    ∑ first : Fin 6, ∑ _second : Fin 6, ∑ third : Fin 6,
        thresholdPairForm design first third ^ 2
      = 6 * (1296 * pairSecondMoment design - 756 * levSecondMoment design + 162) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, sum_sq_thresholdPairForm design]
  norm_num

/-- The second-third energy over the cube. -/
theorem cube_sum_sq_second_third :
    ∑ _first : Fin 6, ∑ second : Fin 6, ∑ third : Fin 6,
        thresholdPairForm design second third ^ 2
      = 6 * (1296 * pairSecondMoment design - 756 * levSecondMoment design + 162) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_sq_thresholdPairForm design]
  norm_num

/-- Two pair forms sharing the FIRST slot. -/
theorem cube_prod_share_first :
    ∑ first : Fin 6, ∑ second : Fin 6, ∑ third : Fin 6,
        thresholdPairForm design first second * thresholdPairForm design first third
      = 2916 * levSecondMoment design - 2430 := by
  have hstep : ∀ first : Fin 6,
      ∑ second : Fin 6, ∑ third : Fin 6,
          thresholdPairForm design first second * thresholdPairForm design first third
        = (∑ second : Fin 6, thresholdPairForm design first second) ^ 2 := by
    intro first
    rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun first _ => hstep first,
    sum_sq_row_thresholdPairForm design]

/-- Two pair forms sharing the SECOND slot. -/
theorem cube_prod_share_second :
    ∑ first : Fin 6, ∑ second : Fin 6, ∑ third : Fin 6,
        thresholdPairForm design first second * thresholdPairForm design second third
      = 2916 * levSecondMoment design - 2430 := by
  classical
  have hswap : ∀ first second third : Fin 6,
      thresholdPairForm design first second * thresholdPairForm design second third
        = thresholdPairForm design second first * thresholdPairForm design second third := by
    intro first second third
    rw [thresholdPairForm_comm design first second]
  rw [Finset.sum_congr rfl fun first _ => Finset.sum_congr rfl fun second _ =>
    Finset.sum_congr rfl fun third _ => hswap first second third, Finset.sum_comm]
  have hstep : ∀ second : Fin 6,
      ∑ first : Fin 6, ∑ third : Fin 6,
          thresholdPairForm design second first * thresholdPairForm design second third
        = (∑ first : Fin 6, thresholdPairForm design second first) ^ 2 := by
    intro second
    rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun second _ => hstep second,
    sum_sq_row_thresholdPairForm design]

/-- Two pair forms sharing the THIRD slot. -/
theorem cube_prod_share_third :
    ∑ first : Fin 6, ∑ second : Fin 6, ∑ third : Fin 6,
        thresholdPairForm design first third * thresholdPairForm design second third
      = 2916 * levSecondMoment design - 2430 := by
  classical
  have hswap : ∀ first second third : Fin 6,
      thresholdPairForm design first third * thresholdPairForm design second third
        = thresholdPairForm design third first * thresholdPairForm design third second := by
    intro first second third
    rw [thresholdPairForm_comm design first third, thresholdPairForm_comm design second third]
  rw [Finset.sum_congr rfl fun first _ => Finset.sum_congr rfl fun second _ =>
    Finset.sum_congr rfl fun third _ => hswap first second third]
  have hcomm : ∀ first : Fin 6,
      ∑ second : Fin 6, ∑ third : Fin 6,
          thresholdPairForm design third first * thresholdPairForm design third second
        = ∑ third : Fin 6, ∑ second : Fin 6,
          thresholdPairForm design third first * thresholdPairForm design third second :=
    fun _ => Finset.sum_comm
  rw [Finset.sum_congr rfl fun first _ => hcomm first, Finset.sum_comm]
  have hstep : ∀ third : Fin 6,
      ∑ first : Fin 6, ∑ second : Fin 6,
          thresholdPairForm design third first * thresholdPairForm design third second
        = (∑ first : Fin 6, thresholdPairForm design third first) ^ 2 := by
    intro third
    rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun third _ => hstep third,
    sum_sq_row_thresholdPairForm design]

/-- **THE THRESHOLD ENERGY OVER THE FULL INDEX CUBE.** -/
theorem sum_sq_projThreshold_cube :
    ∑ first : Fin 6, ∑ second : Fin 6, ∑ third : Fin 6,
        projThresholdAt (projectionOfDesign design) first second third ^ 2
      = 23328 * pairSecondMoment design + 3888 * levSecondMoment design - 7560 := by
  classical
  have hexp : ∀ first second third : Fin 6,
      projThresholdAt (projectionOfDesign design) first second third ^ 2
        = thresholdPairForm design first second ^ 2
          + thresholdPairForm design first third ^ 2
          + thresholdPairForm design second third ^ 2
          + 2 * (thresholdPairForm design first second
              * thresholdPairForm design first third)
          + 2 * (thresholdPairForm design first second
              * thresholdPairForm design second third)
          + 2 * (thresholdPairForm design first third
              * thresholdPairForm design second third)
          + 2 * thresholdPairForm design first second
          + 2 * thresholdPairForm design first third
          + 2 * thresholdPairForm design second third
          + 1 := by
    intro first second third
    rw [projThresholdAt_eq_pairForm design first second third]; ring
  have hone : ∑ _first : Fin 6, ∑ _second : Fin 6, ∑ _third : Fin 6, (1 : ℝ) = 216 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  simp only [hexp, Finset.sum_add_distrib, tripleConstMul]
  rw [cube_sum_sq_first_second design, cube_sum_sq_first_third design,
    cube_sum_sq_second_third design, cube_prod_share_first design,
    cube_prod_share_second design, cube_prod_share_third design,
    cube_sum_pair_first_second design, cube_sum_pair_first_third design,
    cube_sum_pair_second_third design, hone]
  ring

end Cube

/-! ## 5. The two degenerate diagonals

The threshold does not vanish when slots agree, so each diagonal of the cube
contributes and must be computed. -/

section Degenerate

variable (design : WeightedDesign 6 3)

/-- **THE PAIR DIAGONAL.**  The threshold energy when the first two slots agree,
over the full index square. -/
theorem sum_sq_projThreshold_diagPair :
    ∑ first : Fin 6, ∑ third : Fin 6,
        projThresholdAt (projectionOfDesign design) first first third ^ 2
      = 5184 * pairSecondMoment design - 4104 * levSecondMoment design + 1548 := by
  classical
  have hself : ∀ first : Fin 6,
      thresholdPairForm design first first
        = -6 * projectionOfDesign design first first := by
    intro first
    simp only [thresholdPairForm, pairMinorAt_self]; ring
  have hexp : ∀ first third : Fin 6,
      projThresholdAt (projectionOfDesign design) first first third ^ 2
        = 36 * projectionOfDesign design first first ^ 2
          + 4 * thresholdPairForm design first third ^ 2
          + 1
          - 24 * (projectionOfDesign design first first
              * thresholdPairForm design first third)
          - 12 * projectionOfDesign design first first
          + 4 * thresholdPairForm design first third := by
    intro first third
    rw [projThresholdAt_eq_pairForm design first first third, hself first]; ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_sq_thresholdPairForm design, sum_thresholdPairForm_double design,
    sum_diag_mul_row_thresholdPairForm design]
  have hdiagsq : ∑ first : Fin 6, ∑ _third : Fin 6,
      projectionOfDesign design first first ^ 2 = 6 * levSecondMoment design :=
    sum_sq_diag_first_double design
  have hdiag : ∑ first : Fin 6, ∑ _third : Fin 6,
      projectionOfDesign design first first = 18 := by
    have hinner : ∀ first : Fin 6,
        ∑ _third : Fin 6, projectionOfDesign design first first
          = 6 * projectionOfDesign design first first := by
      intro first
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
    rw [Finset.sum_congr rfl fun first _ => hinner first, ← Finset.mul_sum,
      sum_projectionDiagonal design]
    norm_num
  rw [hdiagsq, hdiag]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  ring

/-- **THE TRIPLE DIAGONAL.**  The threshold energy when all three slots agree. -/
theorem sum_sq_projThreshold_diagTriple :
    ∑ label : Fin 6,
        projThresholdAt (projectionOfDesign design) label label label ^ 2
      = 324 * levSecondMoment design - 102 := by
  have htrace := sum_projectionDiagonal design
  have hself : ∀ label : Fin 6,
      projThresholdAt (projectionOfDesign design) label label label ^ 2
        = 324 * projectionOfDesign design label label ^ 2
          - 36 * projectionOfDesign design label label + 1 := by
    intro label
    simp only [projThresholdAt, pairMinorAt_self]; ring
  rw [Finset.sum_congr rfl fun label _ => hself label]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, htrace,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, levSecondMoment]
  ring

end Degenerate

/-! ## 6. The threshold slot symmetry

The threshold is symmetric in its three slots, which identifies the three pair
diagonals of the cube with one another. -/

section ThresholdSymmetry

variable (design : WeightedDesign 6 3)

/-- Swapping the last two slots leaves the threshold alone. -/
theorem projThresholdAt_swap_second_third (first second third : Fin 6) :
    projThresholdAt (projectionOfDesign design) first third second
      = projThresholdAt (projectionOfDesign design) first second third := by
  simp only [projThresholdAt,
    pairMinorAt_comm (projectionOfDesign design) (projectionOfDesign_transpose design)
      third second]
  ring

/-- Swapping the outer two slots leaves the threshold alone. -/
theorem projThresholdAt_swap_first_third (first second third : Fin 6) :
    projThresholdAt (projectionOfDesign design) third second first
      = projThresholdAt (projectionOfDesign design) first second third := by
  simp only [projThresholdAt,
    pairMinorAt_comm (projectionOfDesign design) (projectionOfDesign_transpose design)
      third second,
    pairMinorAt_comm (projectionOfDesign design) (projectionOfDesign_transpose design)
      third first,
    pairMinorAt_comm (projectionOfDesign design) (projectionOfDesign_transpose design)
      second first]
  ring

end ThresholdSymmetry

/-! ## 7. Inclusion-exclusion, and the closed form

Erasing the repeats from the cube costs three pair diagonals and returns two
triple diagonals, because each pair diagonal already contains the triple one. -/

section Closure

variable (design : WeightedDesign 6 3)

/-- **INCLUSION-EXCLUSION.**  The ordered distinct sum against the full cube. -/
theorem thresholdSecondMoment_eq_cube_sub :
    thresholdSecondMoment design
      = (∑ first : Fin 6, ∑ second : Fin 6, ∑ third : Fin 6,
          projThresholdAt (projectionOfDesign design) first second third ^ 2)
        - 3 * (∑ first : Fin 6, ∑ third : Fin 6,
          projThresholdAt (projectionOfDesign design) first first third ^ 2)
        + 2 * (∑ label : Fin 6,
          projThresholdAt (projectionOfDesign design) label label label ^ 2) := by
  classical
  have hinner : ∀ first second : Fin 6, second ≠ first →
      ∑ third ∈ ((univ : Finset (Fin 6)).erase first).erase second,
          projThresholdAt (projectionOfDesign design) first second third ^ 2
        = (∑ third : Fin 6,
            projThresholdAt (projectionOfDesign design) first second third ^ 2)
          - projThresholdAt (projectionOfDesign design) first second first ^ 2
          - projThresholdAt (projectionOfDesign design) first second second ^ 2 := by
    intro first second hne
    rw [Finset.sum_erase_eq_sub (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ second⟩),
      Finset.sum_erase_eq_sub (Finset.mem_univ first)]
  have houter : ∀ first : Fin 6,
      ∑ second ∈ (univ : Finset (Fin 6)).erase first,
        ∑ third ∈ ((univ : Finset (Fin 6)).erase first).erase second,
          projThresholdAt (projectionOfDesign design) first second third ^ 2
        = (∑ second : Fin 6,
            ((∑ third : Fin 6,
              projThresholdAt (projectionOfDesign design) first second third ^ 2)
            - projThresholdAt (projectionOfDesign design) first second first ^ 2
            - projThresholdAt (projectionOfDesign design) first second second ^ 2))
          - ((∑ third : Fin 6,
              projThresholdAt (projectionOfDesign design) first first third ^ 2)
            - projThresholdAt (projectionOfDesign design) first first first ^ 2
            - projThresholdAt (projectionOfDesign design) first first first ^ 2) := by
    intro first
    rw [← Finset.sum_erase_eq_sub (Finset.mem_univ first)]
    exact Finset.sum_congr rfl fun second hsecond =>
      hinner first second (Finset.mem_erase.mp hsecond).1
  -- The two off-diagonal repeats each reindex onto the SAME pair diagonal.  A
  -- `simp` cannot do this: both rewrites are permutative, so `simp` refuses to
  -- orient them and silently drops the second.  The reindexing is explicit.
  have hA : ∑ first : Fin 6, ∑ second : Fin 6,
        projThresholdAt (projectionOfDesign design) first second first ^ 2
      = ∑ first : Fin 6, ∑ third : Fin 6,
        projThresholdAt (projectionOfDesign design) first first third ^ 2 :=
    Finset.sum_congr rfl fun first _ => Finset.sum_congr rfl fun second _ => by
      rw [projThresholdAt_swap_second_third design first first second]
  have hB : ∑ first : Fin 6, ∑ second : Fin 6,
        projThresholdAt (projectionOfDesign design) first second second ^ 2
      = ∑ first : Fin 6, ∑ third : Fin 6,
        projThresholdAt (projectionOfDesign design) first first third ^ 2 := by
    have hstep : ∀ first second : Fin 6,
        projThresholdAt (projectionOfDesign design) first second second ^ 2
          = projThresholdAt (projectionOfDesign design) second second first ^ 2 := by
      intro first second
      rw [projThresholdAt_swap_first_third design second second first]
    rw [Finset.sum_congr rfl fun first _ =>
      Finset.sum_congr rfl fun second _ => hstep first second]
    exact Finset.sum_comm
  simp only [thresholdSecondMoment]
  rw [Finset.sum_congr rfl fun first _ => houter first]
  simp only [Finset.sum_sub_distrib]
  rw [hA, hB]
  ring

/-- **THE THRESHOLD ENERGY IS CLOSED FORM.**  Two invariants and a constant, in
the ORDERED convention throughout: `Gtz.pairSecondMoment` runs over ordered
distinct pairs and `Gtz.thresholdSecondMoment` over ordered distinct triples. -/
theorem thresholdSecondMoment_eq :
    thresholdSecondMoment design
      = 7776 * pairSecondMoment design + 16848 * levSecondMoment design - 12408 := by
  rw [thresholdSecondMoment_eq_cube_sub design, sum_sq_projThreshold_cube design,
    sum_sq_projThreshold_diagPair design, sum_sq_projThreshold_diagTriple design]
  ring

/-- **THE REDUCTION, AS A THEOREM.**  Everything in the second-moment theory of
the objective is a polynomial in the two invariants except the mass energy. -/
theorem massSecondMoment_eq_closed :
    massSecondMoment design
      = gapSecondMoment design
        + 38880 * pairSecondMoment design
        - 32400 * levSecondMoment design
        + 15000 := by
  rw [massSecondMoment_eq_gap_add_closed design, thresholdSecondMoment_eq design]
  ring

/-- The gap energy in terms of the mass energy alone. -/
theorem gapSecondMoment_eq_closed :
    gapSecondMoment design
      = massSecondMoment design
        - 38880 * pairSecondMoment design
        + 32400 * levSecondMoment design
        - 15000 := by
  rw [massSecondMoment_eq_closed design]; ring

/-- **THE MASS ENERGY IS BOUNDED BELOW BY A CLOSED FORM**, because the gap energy
is a sum of squares.  This is the first lower bound on the Plucker energy that
reads only the two invariants. -/
theorem massSecondMoment_ge_closed :
    38880 * pairSecondMoment design - 32400 * levSecondMoment design + 15000
      ≤ massSecondMoment design := by
  have hgap := gapSecondMoment_nonneg design
  have hclosed := massSecondMoment_eq_closed design
  linarith

end Closure

/-! ## 8. The Plucker mass as a nonnegative weight

The second-moment criterion compares the gap energy against the SQUARE of the gap
total, and it needs a spread of about eleven times the mean.  A linear criterion
needs no spread at all.  If every gap were nonpositive then every sum of gaps
against a NONNEGATIVE weight would be nonpositive, so a single positive weighted
sum forces a positive gap.

The block determinant is such a weight: `Gtz.det_tripleBlock_nonneg` holds because
the projection is positive semidefinite.  Weighting by it is what removes the
mass energy, because the weighted gap is the mass energy minus the cross term and
those two share their leading behaviour. -/

section MassWeighted

variable (design : WeightedDesign 6 3)

/-- The gap summed against its own Plucker mass, over ordered distinct triples. -/
noncomputable def massWeightedGap : ℝ :=
  ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
    ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det)
        * projGapAt (projectionOfDesign design) outer mid inner

/-- The weighted gap is the mass energy minus the cross term. -/
theorem massWeightedGap_eq_split :
    massWeightedGap design = massSecondMoment design - jointCrossMoment design := by
  classical
  have key : ∀ outer mid inner : Fin 6,
      (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det)
          * projGapAt (projectionOfDesign design) outer mid inner
        = (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det) ^ 2
          - (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det)
            * projThresholdAt (projectionOfDesign design) outer mid inner := by
    intro outer mid inner; rw [projGapAt]; ring
  simp only [massWeightedGap, massSecondMoment, jointCrossMoment]
  simp only [key, Finset.sum_sub_distrib]

/-- **THE MASS ENERGY CANCELS.**  The weighted gap is the gap energy plus a
polynomial in the two invariants.  The mass energy, the one quantity in the
second-moment theory that is not closed form, does not appear. -/
theorem massWeightedGap_eq_gapEnergy :
    massWeightedGap design
      = gapSecondMoment design
        + 15552 * pairSecondMoment design
        - 24624 * levSecondMoment design
        + 13704 := by
  rw [massWeightedGap_eq_split design, massSecondMoment_eq design,
    jointCrossMoment_eq design, thresholdSecondMoment_eq design]
  ring

/-- The weighted gap read against the mass energy. -/
theorem massWeightedGap_eq_closed :
    massWeightedGap design
      = massSecondMoment design
        - 23328 * pairSecondMoment design
        + 7776 * levSecondMoment design
        - 1296 := by
  rw [massWeightedGap_eq_split design, jointCrossMoment_eq design]; ring

/-- **A TWO-LOCAL FLOOR ON THE WEIGHTED GAP**, because the gap energy is a sum of
squares.  Every quantity here reads only the pair minors and the leverages. -/
theorem massWeightedGap_ge_twoLocal :
    15552 * pairSecondMoment design - 24624 * levSecondMoment design + 13704
      ≤ massWeightedGap design := by
  have hgap := gapSecondMoment_nonneg design
  have hclosed := massWeightedGap_eq_gapEnergy design
  linarith

end MassWeighted

/-! ## 9. The sign producer

A positive weighted gap forces a positive gap, by a sign argument alone.  No
Cauchy-Schwarz, no spread hypothesis, and no appeal to the size of the mass
energy. -/

section SignProducer

variable (design : WeightedDesign 6 3)

/-- **THE GENERAL WEIGHTED SIGN PRODUCER.**  Against ANY nonnegative weight, a
positive weighted gap exhibits an ordered distinct triple whose Plucker mass beats
its own threshold.  Every criterion in this file is an instance, and any future
weight plugs in here without repeating the argument. -/
theorem exists_pos_projGap_of_weighted (weight : Fin 6 → Fin 6 → Fin 6 → ℝ)
    (hnonneg : ∀ outer mid inner : Fin 6, 0 ≤ weight outer mid inner)
    (hpos : 0 < ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        weight outer mid inner
          * projGapAt (projectionOfDesign design) outer mid inner) :
    ∃ outer : Fin 6, ∃ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        0 < projGapAt (projectionOfDesign design) outer mid inner := by
  classical
  by_contra hraw
  have hsigns : ∀ outer : Fin 6, ∀ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∀ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        projGapAt (projectionOfDesign design) outer mid inner ≤ 0 := by
    intro outer mid hmid inner hinner
    by_contra hgood
    exact hraw ⟨outer, mid, hmid, inner, hinner, not_le.mp hgood⟩
  have hle : ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        weight outer mid inner
          * projGapAt (projectionOfDesign design) outer mid inner ≤ 0 := by
    refine Finset.sum_nonpos fun outer _ => Finset.sum_nonpos fun mid hmid =>
      Finset.sum_nonpos fun inner hinner => ?_
    nlinarith [hnonneg outer mid inner, hsigns outer mid hmid inner hinner]
  linarith

/-- The Plucker mass is a legal weight, because it is a principal minor of a
positive semidefinite form. -/
theorem exists_pos_projGap_of_massWeightedGap (hpos : 0 < massWeightedGap design) :
    ∃ outer : Fin 6, ∃ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        0 < projGapAt (projectionOfDesign design) outer mid inner := by
  refine exists_pos_projGap_of_weighted design
    (fun outer mid inner =>
      216 * (tripleBlock (projectionOfDesign design) outer mid inner).det)
    (fun outer mid inner => by
      have := det_tripleBlock_nonneg design outer mid inner; linarith) ?_
  simpa only [massWeightedGap] using hpos

/-- **THE MASS-FREE CRITERION.**  A single inequality between the two invariants
forces a good triple.  This is the first sufficient condition for the objective's
third minor that reads NO unclosed quantity. -/
theorem exists_pos_projGap_of_twoLocal
    (hcert : 24624 * levSecondMoment design
      < 15552 * pairSecondMoment design + 13704) :
    ∃ outer : Fin 6, ∃ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        0 < projGapAt (projectionOfDesign design) outer mid inner := by
  refine exists_pos_projGap_of_massWeightedGap design ?_
  have hfloor := massWeightedGap_ge_twoLocal design
  linarith

/-- The same criterion read against the mass energy, for a caller that already
controls the Plucker energy. -/
theorem exists_pos_projGap_of_massSecondMoment
    (hcert : 23328 * pairSecondMoment design - 7776 * levSecondMoment design + 1296
      < massSecondMoment design) :
    ∃ outer : Fin 6, ∃ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        0 < projGapAt (projectionOfDesign design) outer mid inner := by
  refine exists_pos_projGap_of_massWeightedGap design ?_
  have hclosed := massWeightedGap_eq_closed design
  linarith

end SignProducer

/-! ## 10. The gap energy is bounded below, and the floor is strict

The gap total is `-336` over 120 ordered distinct triples.  Cauchy-Schwarz against
the constant one then floors the gap energy at `336 ^ 2 / 120`.  The index set is
a triple nest of erased universes, so the bound applies once for each level with
cardinalities 6, 5 and 4. -/

section Pigeon

/-- Cauchy-Schwarz against the constant one, self contained. -/
private theorem sq_sum_le_card_mul_sum_sq {ι : Type*} [DecidableEq ι]
    (labels : Finset ι) (value : ι → ℝ) :
    (∑ i ∈ labels, value i) ^ 2 ≤ labels.card * ∑ i ∈ labels, value i ^ 2 := by
  classical
  induction labels using Finset.induction_on with
  | empty => simp
  | @insert head rest hnot ih =>
      rw [Finset.sum_insert hnot, Finset.sum_insert hnot,
        Finset.card_insert_of_notMem hnot]
      have hrest : (0 : ℝ) ≤ ∑ i ∈ rest, value i ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      rcases Nat.eq_zero_or_pos rest.card with hzero | hposcard
      · rw [hzero] at ih ⊢
        have hflat : ∑ i ∈ rest, value i = 0 := by
          have hsq : (∑ i ∈ rest, value i) ^ 2 ≤ 0 := by simpa using ih
          nlinarith [sq_nonneg (∑ i ∈ rest, value i)]
        rw [hflat]
        push_cast
        nlinarith [hrest]
      · have hcardpos : (0 : ℝ) < (rest.card : ℝ) := by exact_mod_cast hposcard
        push_cast
        have hprod : (0 : ℝ)
            ≤ (rest.card : ℝ)
              * ((rest.card : ℝ) * (∑ i ∈ rest, value i ^ 2) - (∑ i ∈ rest, value i) ^ 2) :=
          mul_nonneg (le_of_lt hcardpos) (sub_nonneg.mpr ih)
        nlinarith [ih, hrest, hcardpos, hprod,
          sq_nonneg ((rest.card : ℝ) * value head - ∑ i ∈ rest, value i)]

private theorem card_erase_univ_six (outer : Fin 6) :
    ((univ : Finset (Fin 6)).erase outer).card = 5 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ outer), Finset.card_univ, Fintype.card_fin]

private theorem card_erase_erase_univ_six {outer mid : Fin 6}
    (hmid : mid ∈ (univ : Finset (Fin 6)).erase outer) :
    (((univ : Finset (Fin 6)).erase outer).erase mid).card = 4 := by
  rw [Finset.card_erase_of_mem hmid, card_erase_univ_six outer]

variable (design : WeightedDesign 6 3)

/-- **THE GAP ENERGY HAS A UNIVERSAL FLOOR.**  The gap total is `-336` over 120
ordered distinct triples, so the energy is at least `336 ^ 2 / 120`. -/
theorem gapSecondMoment_ge_pigeon : (4704 : ℝ) / 5 ≤ gapSecondMoment design := by
  classical
  have hinner : ∀ outer : Fin 6, ∀ mid ∈ (univ : Finset (Fin 6)).erase outer,
      (∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projGapAt (projectionOfDesign design) outer mid inner) ^ 2
        ≤ 4 * ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
            projGapAt (projectionOfDesign design) outer mid inner ^ 2 := by
    intro outer mid hmid
    have hbase := sq_sum_le_card_mul_sum_sq
      (((univ : Finset (Fin 6)).erase outer).erase mid)
      (fun inner => projGapAt (projectionOfDesign design) outer mid inner)
    rw [card_erase_erase_univ_six hmid] at hbase
    exact_mod_cast hbase
  have hmidlevel : ∀ outer : Fin 6,
      (∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
          ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
            projGapAt (projectionOfDesign design) outer mid inner) ^ 2
        ≤ 5 * ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
            (∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
              projGapAt (projectionOfDesign design) outer mid inner) ^ 2 := by
    intro outer
    have hbase := sq_sum_le_card_mul_sum_sq ((univ : Finset (Fin 6)).erase outer)
      (fun mid => ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        projGapAt (projectionOfDesign design) outer mid inner)
    rw [card_erase_univ_six outer] at hbase
    exact_mod_cast hbase
  have houter :
      (∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
          ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
            projGapAt (projectionOfDesign design) outer mid inner) ^ 2
        ≤ 6 * ∑ outer : Fin 6,
            (∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
              ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
                projGapAt (projectionOfDesign design) outer mid inner) ^ 2 := by
    have hbase := sq_sum_le_card_mul_sum_sq (univ : Finset (Fin 6))
      (fun outer => ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
        ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projGapAt (projectionOfDesign design) outer mid inner)
    rw [Finset.card_univ, Fintype.card_fin] at hbase
    exact_mod_cast hbase
  have hchain : ∑ outer : Fin 6,
      (∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
        ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projGapAt (projectionOfDesign design) outer mid inner) ^ 2
      ≤ 20 * gapSecondMoment design := by
    have hstep : ∀ outer ∈ (univ : Finset (Fin 6)),
        (∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
          ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
            projGapAt (projectionOfDesign design) outer mid inner) ^ 2
        ≤ 20 * ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
            ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
              projGapAt (projectionOfDesign design) outer mid inner ^ 2 := by
      intro outer _
      have hlift : ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
          (∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
            projGapAt (projectionOfDesign design) outer mid inner) ^ 2
          ≤ ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
              4 * ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
                projGapAt (projectionOfDesign design) outer mid inner ^ 2 :=
        Finset.sum_le_sum fun mid hmid => hinner outer mid hmid
      rw [← Finset.mul_sum] at hlift
      have := hmidlevel outer
      linarith
    have hsum := Finset.sum_le_sum hstep
    rw [← Finset.mul_sum] at hsum
    simpa only [gapSecondMoment] using hsum
  have htotal := sum_projGap design
  rw [htotal] at houter
  have hsquare : ((-336 : ℝ)) ^ 2 = 112896 := by norm_num
  rw [hsquare] at houter
  linarith

/-- **THE GAP ENERGY IS STRICTLY POSITIVE.**  No design has every gap equal to
zero, because the gap total is not zero. -/
theorem gapSecondMoment_pos : 0 < gapSecondMoment design := by
  have := gapSecondMoment_ge_pigeon design; linarith

/-- **A STRICT REFINEMENT OF THE MASS FLOOR.**  The landed two-local bound on the
Plucker energy is never attained, and the deficit is at least `336 ^ 2 / 120`. -/
theorem massSecondMoment_gt_closed :
    38880 * pairSecondMoment design - 32400 * levSecondMoment design
        + 15000 + 4704 / 5
      ≤ massSecondMoment design := by
  have hpigeon := gapSecondMoment_ge_pigeon design
  have hclosed := massSecondMoment_eq_closed design
  linarith

/-- The refined two-local floor on the weighted gap. -/
theorem massWeightedGap_ge_refined :
    15552 * pairSecondMoment design - 24624 * levSecondMoment design + 73224 / 5
      ≤ massWeightedGap design := by
  have hpigeon := gapSecondMoment_ge_pigeon design
  have hclosed := massWeightedGap_eq_gapEnergy design
  linarith

/-- **THE REFINED MASS-FREE CRITERION.**  The universal gap floor widens the
region of the two invariants on which a good triple is forced.  The constant
grows from `13704` to `73224 / 5`, which is `14644.8`. -/
theorem exists_pos_projGap_of_twoLocal_refined
    (hcert : 24624 * levSecondMoment design
      < 15552 * pairSecondMoment design + 73224 / 5) :
    ∃ outer : Fin 6, ∃ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        0 < projGapAt (projectionOfDesign design) outer mid inner := by
  refine exists_pos_projGap_of_massWeightedGap design ?_
  have hfloor := massWeightedGap_ge_refined design
  have hpigeon := gapSecondMoment_ge_pigeon design
  have hclosed := massWeightedGap_eq_gapEnergy design
  linarith

end Pigeon

/-! ## 11. The marginal floor, and the sharp criterion

The pigeonhole floor spends the gap total as ONE number.  The thirty pair
marginals are each closed form, and each is a sum of four gaps, so Cauchy-Schwarz
applies once for each pair instead of once overall.  The resulting floor is
quadratic in the two invariants rather than constant, and it is what carries the
criterion from half of the design space to three quarters of it. -/

section MarginalFloor

variable (design : WeightedDesign 6 3)

/-- Each pair marginal is a sum of four gaps, so the marginal energy is at most
four times the gap energy. -/
theorem pairMarginalEnergy_le_four_mul_gapSecondMoment :
    pairMarginalEnergy design ≤ 4 * gapSecondMoment design := by
  classical
  have hstep : ∀ first ∈ (univ : Finset (Fin 6)),
      ∑ second ∈ (univ : Finset (Fin 6)).erase first, pairMarginal design first second ^ 2
        ≤ 4 * ∑ second ∈ (univ : Finset (Fin 6)).erase first,
            ∑ inner ∈ ((univ : Finset (Fin 6)).erase first).erase second,
              projGapAt (projectionOfDesign design) first second inner ^ 2 := by
    intro first _
    have hinner : ∀ second ∈ (univ : Finset (Fin 6)).erase first,
        pairMarginal design first second ^ 2
          ≤ 4 * ∑ inner ∈ ((univ : Finset (Fin 6)).erase first).erase second,
              projGapAt (projectionOfDesign design) first second inner ^ 2 := by
      intro second hsecond
      have hbase := sq_sum_le_card_mul_sum_sq
        (((univ : Finset (Fin 6)).erase first).erase second)
        (fun inner => projGapAt (projectionOfDesign design) first second inner)
      rw [sum_projGap_eq_pairMarginal design first second hsecond,
        card_erase_erase_univ_six hsecond] at hbase
      exact_mod_cast hbase
    have hlift := Finset.sum_le_sum hinner
    rwa [← Finset.mul_sum] at hlift
  have hsum := Finset.sum_le_sum hstep
  rw [← Finset.mul_sum] at hsum
  simpa only [pairMarginalEnergy, gapSecondMoment] using hsum

/-- **THE MARGINAL FLOOR ON THE GAP ENERGY.**  Two-local and quadratic, and it
dominates the pigeonhole floor at every design. -/
theorem gapSecondMoment_ge_marginal :
    5184 * pairSecondMoment design - 9720 * levSecondMoment design + 9300
      ≤ gapSecondMoment design := by
  have hcs := pairMarginalEnergy_le_four_mul_gapSecondMoment design
  have heq := pairMarginalEnergy_eq design
  linarith

/-- The weighted gap under the marginal floor. -/
theorem massWeightedGap_ge_marginal :
    20736 * pairSecondMoment design - 34344 * levSecondMoment design + 23004
      ≤ massWeightedGap design := by
  have hfloor := gapSecondMoment_ge_marginal design
  have hclosed := massWeightedGap_eq_gapEnergy design
  linarith

/-- The Plucker energy under the marginal floor, sharper than the landed bound. -/
theorem massSecondMoment_ge_marginal :
    44064 * pairSecondMoment design - 42120 * levSecondMoment design + 24300
      ≤ massSecondMoment design := by
  have hfloor := gapSecondMoment_ge_marginal design
  have hclosed := massSecondMoment_eq_closed design
  linarith

/-- **THE SHARP MASS-FREE CRITERION.**  One inequality between the pair-minor
energy and the leverage energy forces a triple whose Plucker mass beats its own
threshold.  Nothing here reads the Plucker energy. -/
theorem exists_pos_projGap_of_twoLocal_sharp
    (hcert : 34344 * levSecondMoment design
      < 20736 * pairSecondMoment design + 23004) :
    ∃ outer : Fin 6, ∃ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        0 < projGapAt (projectionOfDesign design) outer mid inner := by
  refine exists_pos_projGap_of_massWeightedGap design ?_
  have hfloor := massWeightedGap_ge_marginal design
  linarith

end MarginalFloor

/-! ## 12. The squared mass, and the objective as one scalar inequality

The Plucker mass is a legal weight, but the criterion it carries is not universal.
A numerical sweep puts the mass weight at zero percent ON the icosahedron and
throughout a neighbourhood of it, so that weight is blind exactly where the
objective is hardest.  The SQUARED mass is a legal weight too, and it concentrates
the sum onto the triples that carry the objective.  It fires at the icosahedron
and it reaches about one failure in sixty thousand, but it is NOT universal
either.  Refer to the warning on `Gtz.MassSquaredGapPositive`. -/

section SquaredMass

variable (design : WeightedDesign 6 3)

/-- The third moment of the Plucker mass over ordered distinct triples. -/
noncomputable def massThirdMoment : ℝ :=
  ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
    ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det) ^ 3

/-- The squared Plucker mass against the threshold. -/
noncomputable def massSquaredCrossMoment : ℝ :=
  ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
    ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det) ^ 2
        * projThresholdAt (projectionOfDesign design) outer mid inner

/-- The gap summed against the SQUARED Plucker mass. -/
noncomputable def massSquaredWeightedGap : ℝ :=
  ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
    ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det) ^ 2
        * projGapAt (projectionOfDesign design) outer mid inner

/-- **THE RESIDUAL, NAMED.**  The squared-mass weighted gap is the third moment of
the Plucker measure minus its squared cross term. -/
theorem massSquaredWeightedGap_eq_split :
    massSquaredWeightedGap design
      = massThirdMoment design - massSquaredCrossMoment design := by
  classical
  have key : ∀ outer mid inner : Fin 6,
      (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det) ^ 2
          * projGapAt (projectionOfDesign design) outer mid inner
        = (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det) ^ 3
          - (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det) ^ 2
            * projThresholdAt (projectionOfDesign design) outer mid inner := by
    intro outer mid inner; rw [projGapAt]; ring
  simp only [massSquaredWeightedGap, massThirdMoment, massSquaredCrossMoment]
  simp only [key, Finset.sum_sub_distrib]

/-- **THE SQUARED MASS IS A LEGAL WEIGHT.**  A square is nonnegative, so this
needs no appeal to positive semidefiniteness at all. -/
theorem exists_pos_projGap_of_massSquaredWeightedGap
    (hpos : 0 < massSquaredWeightedGap design) :
    ∃ outer : Fin 6, ∃ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        0 < projGapAt (projectionOfDesign design) outer mid inner := by
  refine exists_pos_projGap_of_weighted design
    (fun outer mid inner =>
      (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det) ^ 2)
    (fun _ _ _ => sq_nonneg _) ?_
  simpa only [massSquaredWeightedGap] using hpos

end SquaredMass

/-! ## 13. The flat locus, where the registry lives

Uniform weight forces a flat leverage, and a flat leverage is exactly the minimum
of the leverage energy.  The whole criterion collapses there onto ONE threshold on
the pair-minor energy, and the pair marginals collapse onto one formula.  That
formula is negative by a margin of four at every pair, so no pair-level
certificate can ever fire on the flat locus.  This section proves both. -/

section FlatLocus

variable (design : WeightedDesign 6 3)

/-- **THE LEVERAGE ENERGY IS AT LEAST THREE HALVES**, because six diagonal entries
total three.  Equality is the flat locus. -/
theorem levSecondMoment_ge_three_halves : (3 : ℝ) / 2 ≤ levSecondMoment design := by
  have hbase := sq_sum_le_card_mul_sum_sq (univ : Finset (Fin 6))
    (fun label => projectionOfDesign design label label)
  rw [Finset.card_univ, Fintype.card_fin, sum_projectionDiagonal design] at hbase
  norm_num at hbase
  simpa only [levSecondMoment] using by linarith [hbase]

/-- **THE FLAT LOCUS IS THE EQUALITY CASE.**  A leverage energy of three halves
forces every diagonal entry to one half. -/
theorem projectionDiagonal_eq_half_of_flat
    (hflat : levSecondMoment design = 3 / 2) (label : Fin 6) :
    projectionOfDesign design label label = 1 / 2 := by
  classical
  have hsq : ∑ other : Fin 6,
      (projectionOfDesign design other other - 1 / 2) ^ 2 = 0 := by
    have hexpand : ∀ other : Fin 6,
        (projectionOfDesign design other other - 1 / 2) ^ 2
          = projectionOfDesign design other other ^ 2
            - projectionOfDesign design other other + 1 / 4 := by
      intro other; ring
    rw [Finset.sum_congr rfl fun other _ => hexpand other]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_projectionDiagonal design]
    have hlev : ∑ other : Fin 6, projectionOfDesign design other other ^ 2 = 3 / 2 := hflat
    rw [hlev]
    norm_num
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun other _ => sq_nonneg (projectionOfDesign design other other - 1 / 2))).mp hsq
  have := hzero label (Finset.mem_univ label)
  have hsub : projectionOfDesign design label label - 1 / 2 = 0 := by
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

/-- **EVERY PAIR MARGINAL IS AT MOST MINUS FOUR ON THE FLAT LOCUS.**  No weight on
the thirty pairs is nonnegative and beats this, so a pair-level certificate cannot
fire on the flat locus at all.  The deficit grows with the off-diagonal entry. -/
theorem pairMarginal_eq_of_flat (hflat : levSecondMoment design = 3 / 2)
    (first second : Fin 6) :
    pairMarginal design first second
      = -4 - 144 * projectionOfDesign design first second ^ 2 := by
  rw [pairMarginal_apply, pairMinorAt,
    projectionDiagonal_eq_half_of_flat design hflat first,
    projectionDiagonal_eq_half_of_flat design hflat second]
  ring

theorem pairMarginal_le_neg_four_of_flat (hflat : levSecondMoment design = 3 / 2)
    (first second : Fin 6) : pairMarginal design first second ≤ -4 := by
  rw [pairMarginal_eq_of_flat design hflat first second]
  nlinarith [sq_nonneg (projectionOfDesign design first second)]

/-- **THE CRITERION ON THE FLAT LOCUS.**  One threshold on the pair-minor energy,
with every other quantity fixed by flatness. -/
theorem exists_pos_projGap_of_flat
    (hflat : levSecondMoment design = 3 / 2)
    (hcert : 11 / 8 < pairSecondMoment design) :
    ∃ outer : Fin 6, ∃ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        0 < projGapAt (projectionOfDesign design) outer mid inner := by
  refine exists_pos_projGap_of_twoLocal_sharp design ?_
  rw [hflat]; linarith

/-- **THE GAP IN CLOSED FORM ON THE FLAT LOCUS.**  Every leverage is one half, so
the whole gap functional collapses onto the three off-diagonal entries of the
triple.  `S` is their squared total and `Q` is their product. -/
theorem projGapAt_eq_of_flat (hflat : levSecondMoment design = 3 / 2)
    (first second third : Fin 6) :
    projGapAt (projectionOfDesign design) first second third
      = 8 - 72 * (projectionOfDesign design first second ^ 2
            + projectionOfDesign design first third ^ 2
            + projectionOfDesign design second third ^ 2)
        + 432 * (projectionOfDesign design first second
            * projectionOfDesign design first third
            * projectionOfDesign design second third) := by
  have hone := projectionDiagonal_eq_half_of_flat design hflat first
  have htwo := projectionDiagonal_eq_half_of_flat design hflat second
  have hthree := projectionDiagonal_eq_half_of_flat design hflat third
  rw [projGapAt, det_tripleBlock (projectionOfDesign design)
      (projectionOfDesign_transpose design) first second third]
  simp only [projThresholdAt, pairMinorAt, hone, htwo, hthree]
  ring

/-- **THE OBJECTIVE ON THE FLAT LOCUS IS A SIGN CONDITION.**  A good triple is one
whose three off-diagonal entries have a product large enough to beat their squared
total.  Nothing else survives flatness. -/
theorem exists_pos_projGap_of_flat_triple_product
    (hflat : levSecondMoment design = 3 / 2)
    (hbeat : ∃ outer : Fin 6, ∃ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        72 * (projectionOfDesign design outer mid ^ 2
            + projectionOfDesign design outer inner ^ 2
            + projectionOfDesign design mid inner ^ 2)
          < 8 + 432 * (projectionOfDesign design outer mid
              * projectionOfDesign design outer inner
              * projectionOfDesign design mid inner)) :
    ∃ outer : Fin 6, ∃ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        0 < projGapAt (projectionOfDesign design) outer mid inner := by
  obtain ⟨outer, mid, hmid, inner, hinner, hlt⟩ := hbeat
  refine ⟨outer, mid, hmid, inner, hinner, ?_⟩
  rw [projGapAt_eq_of_flat design hflat outer mid inner]
  linarith

/-! ### The block gap on the flat locus, and the registry

At uniform weight the block gap of a triple has one third on every diagonal entry
and the projection entries off it.  Its three leading minors are then explicit.
The corner is one third and needs nothing.  The second is a single square against
one ninth.  The third is the gap functional, already closed above.  So the whole
positive definiteness the registry wants reduces to TWO scalar inequalities. -/

theorem blockGapAt_diagonal_of_flat_uniform
    (hflat : levSecondMoment design = 3 / 2)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹) (label : Fin 6) :
    projectionOfDesign design label label - design.weight label = 1 / 3 := by
  rw [projectionDiagonal_eq_half_of_flat design hflat label, huniform label]; norm_num

/-- **THE BLOCK GAP IS POSITIVE DEFINITE FROM TWO SCALARS.**  On the flat locus at
uniform weight, one square below one ninth and a positive gap give the positive
definiteness that `Gtz.allFiveOnPath_of_blockGapAt` consumes. -/
theorem posDef_blockGapAt_of_flat_uniform
    (hflat : levSecondMoment design = 3 / 2)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹)
    (outer mid inner : Fin 6)
    (hminor : projectionOfDesign design outer mid ^ 2 < 1 / 9)
    (hgap : 0 < projGapAt (projectionOfDesign design) outer mid inner) :
    (blockGapAt (projectionOfDesign design) design.weight ![outer, mid, inner]).PosDef := by
  classical
  have hsymm := projectionOfDesign_transpose design
  have hflip : ∀ left right : Fin 6,
      projectionOfDesign design right left = projectionOfDesign design left right := by
    intro left right
    simpa only [Matrix.transpose_apply] using congrFun (congrFun hsymm left) right
  have hmat : blockGapAt (projectionOfDesign design) design.weight ![outer, mid, inner]
      = !![1 / 3, projectionOfDesign design outer mid, projectionOfDesign design outer inner;
          projectionOfDesign design outer mid, 1 / 3, projectionOfDesign design mid inner;
          projectionOfDesign design outer inner, projectionOfDesign design mid inner, 1 / 3] := by
    have hdiag := blockGapAt_diagonal_of_flat_uniform design hflat huniform
    ext left right
    rcases eq_or_ne left right with rfl | hne
    · rw [blockGapAt_apply_diag]
      fin_cases left <;> simp [hdiag]
    · rw [blockGapAt_apply_offDiag _ _ _ hne]
      fin_cases left <;> fin_cases right <;> simp_all
  rw [hmat]
  refine posDef_of_leadingMinors_fin_three _ _ _ _ _ _ (by norm_num) (by nlinarith [hminor]) ?_
  have hclosed := projGapAt_eq_of_flat design hflat outer mid inner
  rw [hclosed] at hgap
  nlinarith [hgap]

/-! ### A dead end, recorded on purpose

An earlier revision of this file carried `allFiveOnPath_of_flat_uniform_selection`,
which asked every primitive design to be flat AND to carry the uniform weight.
`Gtz.IsPrimitiveDesign` constrains no weight at all, so that antecedent is
UNSATISFIABLE and the statement was a door that cannot open.  It is deleted.  The
ledger of `obligationBaseTripleTightUThreeSix` already records weight-uniform
threshold certificates as refuted, with margin infimum zero.

Everything below stays per design.  A caller supplies flatness and the uniform
weight FOR ONE design and receives positive definiteness for that design.  No
statement here quantifies flatness or uniformity over all primitive designs. -/

/-- The off-diagonal squares along a row total one quarter on the flat locus. -/
theorem sum_offDiagonal_sq_row_of_flat (hflat : levSecondMoment design = 3 / 2)
    (first : Fin 6) :
    ∑ second ∈ (univ : Finset (Fin 6)).erase first,
      projectionOfDesign design first second ^ 2 = 1 / 4 := by
  classical
  have hrow := sum_pairMinor_erase design first
  rw [projectionDiagonal_eq_half_of_flat design hflat first] at hrow
  have hentry : ∀ second ∈ (univ : Finset (Fin 6)).erase first,
      pairMinorAt (projectionOfDesign design) first second
        = 1 / 4 - projectionOfDesign design first second ^ 2 := by
    intro second _
    rw [pairMinorAt, projectionDiagonal_eq_half_of_flat design hflat first,
      projectionDiagonal_eq_half_of_flat design hflat second]
    ring
  rw [Finset.sum_congr rfl hentry, Finset.sum_sub_distrib, Finset.sum_const,
    card_erase_univ_six first, nsmul_eq_mul] at hrow
  push_cast at hrow
  linarith

/-- The off-diagonal squares total three halves on the flat locus. -/
theorem sum_offDiagonal_sq_of_flat (hflat : levSecondMoment design = 3 / 2) :
    ∑ first : Fin 6, ∑ second ∈ (univ : Finset (Fin 6)).erase first,
      projectionOfDesign design first second ^ 2 = 3 / 2 := by
  rw [Finset.sum_congr rfl fun first _ => sum_offDiagonal_sq_row_of_flat design hflat first]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- The pair-minor energy on the flat locus is nine eighths plus the fourth power
total of the off-diagonal entries. -/
theorem pairSecondMoment_eq_of_flat (hflat : levSecondMoment design = 3 / 2) :
    pairSecondMoment design
      = 9 / 8 + ∑ first : Fin 6, ∑ second ∈ (univ : Finset (Fin 6)).erase first,
        projectionOfDesign design first second ^ 4 := by
  classical
  have hrow : ∀ first : Fin 6,
      ∑ second ∈ (univ : Finset (Fin 6)).erase first,
          pairMinorAt (projectionOfDesign design) first second ^ 2
        = 3 / 16 + ∑ second ∈ (univ : Finset (Fin 6)).erase first,
            projectionOfDesign design first second ^ 4 := by
    intro first
    have hentry : ∀ second ∈ (univ : Finset (Fin 6)).erase first,
        pairMinorAt (projectionOfDesign design) first second ^ 2
          = 1 / 16 - projectionOfDesign design first second ^ 2 / 2
            + projectionOfDesign design first second ^ 4 := by
      intro second _
      rw [pairMinorAt, projectionDiagonal_eq_half_of_flat design hflat first,
        projectionDiagonal_eq_half_of_flat design hflat second]
      ring
    rw [Finset.sum_congr rfl hentry, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, card_erase_univ_six first, nsmul_eq_mul,
      ← Finset.sum_div, sum_offDiagonal_sq_row_of_flat design hflat first]
    push_cast
    ring
  simp only [pairSecondMoment]
  rw [Finset.sum_congr rfl fun first _ => hrow first, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **THE TWO ROUTES ARE INCOMPATIBLE ON THE FLAT LOCUS.**  A pair-minor energy
beyond eleven eighths FORCES an off-diagonal square of at least one sixth, which
is already past the one ninth that the second leading minor needs.  So the
two-local energy criterion and a small first entry can never hold together, and
the frontier cell they would cut out is empty. -/
theorem exists_large_offDiagonal_of_flat_of_energy
    (hflat : levSecondMoment design = 3 / 2)
    (hEnergy : 11 / 8 < pairSecondMoment design) :
    ∃ first : Fin 6, ∃ second ∈ (univ : Finset (Fin 6)).erase first,
      1 / 6 ≤ projectionOfDesign design first second ^ 2 := by
  classical
  by_contra hraw
  have hsmall : ∀ first : Fin 6, ∀ second ∈ (univ : Finset (Fin 6)).erase first,
      projectionOfDesign design first second ^ 2 < 1 / 6 := by
    intro first second hsecond
    by_contra hbig
    exact hraw ⟨first, second, hsecond, not_lt.mp hbig⟩
  have hquart : ∑ first : Fin 6, ∑ second ∈ (univ : Finset (Fin 6)).erase first,
      projectionOfDesign design first second ^ 4
      ≤ ∑ first : Fin 6, ∑ second ∈ (univ : Finset (Fin 6)).erase first,
        projectionOfDesign design first second ^ 2 / 6 := by
    refine Finset.sum_le_sum fun first _ => Finset.sum_le_sum fun second hsecond => ?_
    have hle := le_of_lt (hsmall first second hsecond)
    nlinarith [sq_nonneg (projectionOfDesign design first second)]
  have hdiv : ∑ first : Fin 6, ∑ second ∈ (univ : Finset (Fin 6)).erase first,
      projectionOfDesign design first second ^ 2 / 6 = 1 / 4 := by
    rw [Finset.sum_congr rfl fun first _ => (Finset.sum_div _ _ _).symm, ← Finset.sum_div,
      sum_offDiagonal_sq_of_flat design hflat]
    norm_num
  rw [hdiv] at hquart
  have hclosed := pairSecondMoment_eq_of_flat design hflat
  linarith

/-! ### The complement kills the second minor obstruction

The projection is a contraction, so `1 - P` is positive semidefinite and every one
of its principal blocks has a nonnegative determinant.  On the flat locus that
determinant is `1/8 - S/2 - 2Q`, which caps the product `Q` against the squared
total `S`.  Feeding the cap into the gap formula gives `g <= 35 - 180 S`.  A
positive gap therefore forces `S < 7/36`, and three squares that each reach one
ninth would total at least `1/3`.  So EVERY good triple carries a small pair, and
the second leading minor costs nothing after a reordering. -/

private theorem injective_triple_pick {outer mid inner : Fin 6}
    (hom : outer ≠ mid) (hoi : outer ≠ inner) (hmi : mid ≠ inner) :
    Function.Injective ![outer, mid, inner] := by
  intro left right hlr
  fin_cases left <;> fin_cases right <;> simp_all

/-- The complement block of a triple has a nonnegative determinant. -/
theorem det_one_sub_tripleBlock_nonneg (outer mid inner : Fin 6)
    (hinj : Function.Injective ![outer, mid, inner]) :
    0 ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - tripleBlock (projectionOfDesign design) outer mid inner).det := by
  have hcomplement := (posSemidef_one_sub_projectionOfDesign design).submatrix
    ![outer, mid, inner]
  have hsplit : ((1 : Matrix (Fin 6) (Fin 6) ℝ) - projectionOfDesign design).submatrix
        ![outer, mid, inner] ![outer, mid, inner]
      = (1 : Matrix (Fin 6) (Fin 6) ℝ).submatrix ![outer, mid, inner] ![outer, mid, inner]
        - tripleBlock (projectionOfDesign design) outer mid inner := rfl
  rw [hsplit, Matrix.submatrix_one _ hinj] at hcomplement
  exact hcomplement.det_nonneg

/-- The complement block determinant on the flat locus. -/
theorem det_one_sub_tripleBlock_eq_of_flat (hflat : levSecondMoment design = 3 / 2)
    (outer mid inner : Fin 6) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - tripleBlock (projectionOfDesign design) outer mid inner).det
      = 1 / 8
        - (projectionOfDesign design outer mid ^ 2
            + projectionOfDesign design outer inner ^ 2
            + projectionOfDesign design mid inner ^ 2) / 2
        - 2 * (projectionOfDesign design outer mid
            * projectionOfDesign design outer inner
            * projectionOfDesign design mid inner) := by
  have hsymm := projectionOfDesign_transpose design
  have hflip : ∀ left right : Fin 6,
      projectionOfDesign design right left = projectionOfDesign design left right := by
    intro left right
    simpa only [Matrix.transpose_apply] using congrFun (congrFun hsymm left) right
  have hdiag := projectionDiagonal_eq_half_of_flat design hflat
  have hentry : ∀ left right : Fin 3,
      ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - tripleBlock (projectionOfDesign design) outer mid inner) left right
        = (if left = right then (1 : ℝ) else 0)
          - projectionOfDesign design (![outer, mid, inner] left)
              (![outer, mid, inner] right) := by
    intro left right
    rw [Matrix.sub_apply, Matrix.one_apply]
    simp only [tripleBlock, Matrix.submatrix_apply]
  rw [Matrix.det_fin_three]
  simp only [hentry]
  simp [hdiag, hflip]
  ring

/-- **A POSITIVE GAP CAPS THE SQUARED TOTAL.**  The complement cap and the gap
formula together force the three off-diagonal squares below seven thirty-sixths. -/
theorem sum_sq_lt_of_flat_of_gap (hflat : levSecondMoment design = 3 / 2)
    {outer mid inner : Fin 6} (hinj : Function.Injective ![outer, mid, inner])
    (hgap : 0 < projGapAt (projectionOfDesign design) outer mid inner) :
    projectionOfDesign design outer mid ^ 2
        + projectionOfDesign design outer inner ^ 2
        + projectionOfDesign design mid inner ^ 2 < 7 / 36 := by
  have hcap := det_one_sub_tripleBlock_nonneg design outer mid inner hinj
  rw [det_one_sub_tripleBlock_eq_of_flat design hflat outer mid inner] at hcap
  rw [projGapAt_eq_of_flat design hflat outer mid inner] at hgap
  linarith

/-- **EVERY GOOD TRIPLE CARRIES A SMALL PAIR.**  Three squares that each reach one
ninth would total at least one third, and a positive gap caps the total at seven
thirty-sixths. -/
theorem exists_small_pair_of_flat_of_gap (hflat : levSecondMoment design = 3 / 2)
    {outer mid inner : Fin 6} (hinj : Function.Injective ![outer, mid, inner])
    (hgap : 0 < projGapAt (projectionOfDesign design) outer mid inner) :
    projectionOfDesign design outer mid ^ 2 < 1 / 9
      ∨ projectionOfDesign design outer inner ^ 2 < 1 / 9
      ∨ projectionOfDesign design mid inner ^ 2 < 1 / 9 := by
  by_contra hraw
  have hone : ¬ projectionOfDesign design outer mid ^ 2 < 1 / 9 := fun h => hraw (Or.inl h)
  have htwo : ¬ projectionOfDesign design outer inner ^ 2 < 1 / 9 :=
    fun h => hraw (Or.inr (Or.inl h))
  have hthree : ¬ projectionOfDesign design mid inner ^ 2 < 1 / 9 :=
    fun h => hraw (Or.inr (Or.inr h))
  have htotal := sum_sq_lt_of_flat_of_gap design hflat hinj hgap
  linarith [not_lt.mp hone, not_lt.mp htwo, not_lt.mp hthree]

/-- The gap on the flat locus is symmetric, because its closed form is. -/
theorem projGapAt_swap_of_flat (hflat : levSecondMoment design = 3 / 2)
    (outer mid inner : Fin 6) :
    projGapAt (projectionOfDesign design) outer inner mid
      = projGapAt (projectionOfDesign design) outer mid inner := by
  have hsymm := projectionOfDesign_transpose design
  have hflip : ∀ left right : Fin 6,
      projectionOfDesign design right left = projectionOfDesign design left right := by
    intro left right
    simpa only [Matrix.transpose_apply] using congrFun (congrFun hsymm left) right
  rw [projGapAt_eq_of_flat design hflat, projGapAt_eq_of_flat design hflat, hflip inner mid]
  ring

theorem projGapAt_rotate_of_flat (hflat : levSecondMoment design = 3 / 2)
    (outer mid inner : Fin 6) :
    projGapAt (projectionOfDesign design) mid inner outer
      = projGapAt (projectionOfDesign design) outer mid inner := by
  have hsymm := projectionOfDesign_transpose design
  have hflip : ∀ left right : Fin 6,
      projectionOfDesign design right left = projectionOfDesign design left right := by
    intro left right
    simpa only [Matrix.transpose_apply] using congrFun (congrFun hsymm left) right
  rw [projGapAt_eq_of_flat design hflat, projGapAt_eq_of_flat design hflat,
    hflip mid outer, hflip inner outer]
  ring

/-- **THE SECOND MINOR IS FREE.**  A positive gap alone gives the whole positive
definiteness the registry wants, after the triple is ordered so that its small
pair comes first. -/
theorem exists_posDef_blockGapAt_of_flat_uniform_of_gap
    (hflat : levSecondMoment design = 3 / 2)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹)
    {outer mid inner : Fin 6}
    (hom : outer ≠ mid) (hoi : outer ≠ inner) (hmi : mid ≠ inner)
    (hgap : 0 < projGapAt (projectionOfDesign design) outer mid inner) :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
      (blockGapAt (projectionOfDesign design) design.weight pick).PosDef := by
  have hinj := injective_triple_pick hom hoi hmi
  rcases exists_small_pair_of_flat_of_gap design hflat hinj hgap with hsmall | hsmall | hsmall
  · exact ⟨![outer, mid, inner], hinj,
      posDef_blockGapAt_of_flat_uniform design hflat huniform outer mid inner hsmall hgap⟩
  · refine ⟨![outer, inner, mid], injective_triple_pick hoi hom hmi.symm,
      posDef_blockGapAt_of_flat_uniform design hflat huniform outer inner mid hsmall ?_⟩
    rw [projGapAt_swap_of_flat design hflat]; exact hgap
  · refine ⟨![mid, inner, outer], injective_triple_pick hmi hom.symm hoi.symm,
      posDef_blockGapAt_of_flat_uniform design hflat huniform mid inner outer hsmall ?_⟩
    rw [projGapAt_rotate_of_flat design hflat]; exact hgap

end FlatLocus

/-! ## 14. The criterion reaches the objective's own form

`Gtz.JointMassBeatsThreshold` is the objective's third Sylvester minor, stated in
the corpus's joint form.  The two remaining minors are the corner and the pair
minor of the block gap, and they are NOT supplied here. -/

section Door

/-- **THE DOOR.**  A two-local inequality between the pair-minor energy and the
leverage energy, holding on every primitive design, gives the objective in joint
form.  The criterion reads no unclosed quantity. -/
theorem jointMassBeatsThreshold_of_twoLocal
    (hcert : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      24624 * levSecondMoment design
        < 15552 * pairSecondMoment design + 73224 / 5) :
    JointMassBeatsThreshold := by
  rw [jointMassBeatsThreshold_iff_projGap]
  intro design hprim
  exact exists_pos_projGap_of_twoLocal_refined design (hcert design hprim)

/-- **THE OBJECTIVE AS ONE SCALAR INEQUALITY.**  A single positivity, one number
for each design, with no selection and no case analysis.

WARNING, and it is the reason this stays a hypothesis.  A numerical sweep of
200000 designs, over five families, found counterexamples to this positivity at a
rate near one in sixty thousand among designs of low leverage energy.  Do NOT
spend a cycle on a proof of it.  The same sweep refutes every fixed power of the
Plucker mass as a universal weight, and it refutes the statement that the triple
of maximum Plucker mass is always a good triple.  The weighted method reaches
each of these rates and no more, so the residual is structural and not a missing
constant.  `Gtz.exists_pos_projGap_of_twoLocal_sharp` is the unconditional part
of this file, and it carries about three quarters of the design space. -/
def MassSquaredGapPositive : Prop :=
  ∀ candidate : WeightedDesign 6 3, IsPrimitiveDesign candidate →
    0 < massSquaredWeightedGap candidate

/-- The squared-mass positivity gives the objective in joint form outright.  The
weight is a square, so its legality is free.  Refer to the warning on
`Gtz.MassSquaredGapPositive` before you try to discharge the hypothesis. -/
theorem jointMassBeatsThreshold_of_massSquaredGapPositive
    (hcert : MassSquaredGapPositive) : JointMassBeatsThreshold := by
  rw [jointMassBeatsThreshold_iff_projGap]
  intro design hprim
  exact exists_pos_projGap_of_massSquaredWeightedGap design (hcert design hprim)

/-- The same door, stated against the named third-moment residual. -/
theorem jointMassBeatsThreshold_of_massThirdMoment
    (hcert : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      massSquaredCrossMoment design < massThirdMoment design) :
    JointMassBeatsThreshold := by
  refine jointMassBeatsThreshold_of_massSquaredGapPositive ?_
  intro design hprim
  have hsplit := massSquaredWeightedGap_eq_split design
  have := hcert design hprim
  linarith

/-- **THE SHARP DOOR.**  The marginal floor carries the criterion, and it is the
widest of the three this file supplies. -/
theorem jointMassBeatsThreshold_of_twoLocal_sharp
    (hcert : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      34344 * levSecondMoment design
        < 20736 * pairSecondMoment design + 23004) :
    JointMassBeatsThreshold := by
  rw [jointMassBeatsThreshold_iff_projGap]
  intro design hprim
  exact exists_pos_projGap_of_twoLocal_sharp design (hcert design hprim)

/-- The same door, driven by the Plucker energy instead of the two invariants. -/
theorem jointMassBeatsThreshold_of_massSecondMoment
    (hcert : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      23328 * pairSecondMoment design - 7776 * levSecondMoment design + 1296
        < massSecondMoment design) :
    JointMassBeatsThreshold := by
  rw [jointMassBeatsThreshold_iff_projGap]
  intro design hprim
  exact exists_pos_projGap_of_massSecondMoment design (hcert design hprim)

end Door

end Gtz
