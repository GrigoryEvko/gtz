import Gtz.Wave.MassMomentClosure

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

end Gtz
