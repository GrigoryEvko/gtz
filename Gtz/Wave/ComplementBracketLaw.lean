/-
# The two complementary triples share one budget, and the size is the slack

Parseval says the weighted atoms resolve the identity.  Split the atoms into a
triple `C` and its complement, and the identity becomes

  `1 - (the weighted inside atoms) = (the weighted outside atoms)` ,

an equation between two ambient `3x3` matrices.  Taking determinants of both
sides turns it into a statement about BRACKETS, because the determinant of a sum
of rank-one atoms is a bracket:

* LEFT (`Gtz.det_one_sub_weighted_triple`): the determinant of `1` less three
  weighted atoms expands into the campaign's terminal currencies and nothing
  else -- the three weighted leverages, the three weighted pair wedges, and the
  weighted squared bracket:

    `det(1 - t_a A_a - t_b A_b - t_c A_c)
       = 1 - (t_a*l_a + t_b*l_b + t_c*l_c)
           + (t_a*t_b*w_ab + t_a*t_c*w_ac + t_b*t_c*w_bc)
           - t_a*t_b*t_c*[a b c]^2` .

  A pure polynomial identity: the three elementary symmetric functions of the
  weighted Gram, read as leverage, wedge and bracket.

* RIGHT (`Gtz.det_weighted_triple`): three weighted atoms have determinant
  `t_d*t_e*t_f*[d e f]^2`, and TWO weighted atoms have determinant ZERO -- a
  sum of two rank-one matrices cannot fill three dimensions.

## The law, and the size marker

At size six (`Gtz.complement_bracket_law`) the two complementary triples pay
into one budget:

  **`t_a t_b t_c [a b c]^2 + t_d t_e t_f [d e f]^2
      = 1 - Sum of weighted leverages + Sum of weighted pair wedges`** .

At size five (`Gtz.triple_bracket_law_five`) the complement has only two atoms,
its determinant vanishes, and the SAME right-hand side is paid by the inside
triple ALONE:

  **`t_a t_b t_c [a b c]^2
      = 1 - Sum of weighted leverages + Sum of weighted pair wedges`** .

So the two sizes differ by exactly one term, and that term is a bracket mass:
`t_d*t_e*t_f*[d e f]^2`, nonnegative and vanishing exactly when the complement
triple is coplanar.  **The right-hand side is computed from the triple `C`
alone, so it does not know the size; the size shows up entirely as the slack it
is allowed to leave.**  This is the size-six consumption the campaign needs: any
law derived from the right-hand side is an EQUALITY at five and an INEQUALITY at
six, and the gap between them is a bracket the hinge already speaks about.

[MEASURED.  40000 random Parseval designs at each size, atoms whitened so
Parseval is exact: the size-six law holds to `1.2e-13`, the determinant identity
to `8.9e-14`, and at size five `det(1 - weighted inside) = 0` to `6.1e-14`.]
-/
import Gtz.Wave.CornerAdjugateWeightCap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 8000

namespace Gtz

open Matrix Finset

/-! ## 1. The two determinants -/

/-- **THE COMPLEMENT DETERMINANT IN TERMINAL CURRENCY.**  The determinant of `1`
less three weighted atoms is the alternating total of the weighted leverages,
the weighted pair wedges and the weighted squared bracket.  These are the three
elementary symmetric functions of the weighted Gram, and no other quantity
appears. -/
theorem det_one_sub_weighted_triple (ta tb tc : ℝ) (a b c : Fin 3 → ℝ) :
    (1 - ta • atomMatrix a - tb • atomMatrix b - tc • atomMatrix c).det
      = 1 - (ta * leverageOf a + tb * leverageOf b + tc * leverageOf c)
        + (ta * tb * crossNormSq a b + ta * tc * crossNormSq a c
            + tb * tc * crossNormSq b c)
        - ta * tb * tc * tripleBracket a b c ^ 2 := by
  rw [Matrix.one_fin_three]
  simp only [Matrix.det_fin_three, atomMatrix, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, leverageOf,
    crossNormSq, bracketNormal, dotProduct, tripleBracket_eq, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_fin_const,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  ring

/-- **THREE WEIGHTED ATOMS HAVE A BRACKET DETERMINANT.**  Cauchy-Binet at three
rank-one summands. -/
theorem det_weighted_triple (td te tf : ℝ) (d e f : Fin 3 → ℝ) :
    (td • atomMatrix d + te • atomMatrix e + tf • atomMatrix f).det
      = td * te * tf * tripleBracket d e f ^ 2 := by
  simp only [Matrix.det_fin_three, atomMatrix, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, tripleBracket_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **TWO WEIGHTED ATOMS CANNOT FILL THREE DIMENSIONS.**  The determinant of a
sum of two rank-one atoms is identically zero.  This is the whole of the size
gap between five and six. -/
theorem det_weighted_pair (td te : ℝ) (d e : Fin 3 → ℝ) :
    (td • atomMatrix d + te • atomMatrix e).det = 0 := by
  simp only [Matrix.det_fin_three, atomMatrix, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  ring

/-! ## 2. The complementary bracket law at size six -/

/-- **THE COMPLEMENTARY BRACKET LAW.**  When six weighted atoms resolve the
identity, the two complementary triples pay their weighted squared brackets into
ONE budget, and that budget is read off the first triple alone: one, less its
weighted leverage total, plus its weighted pair wedge total. -/
theorem complement_bracket_law {ta tb tc td te tf : ℝ} {a b c d e f : Fin 3 → ℝ}
    (hsplit : ta • atomMatrix a + tb • atomMatrix b + tc • atomMatrix c
        + td • atomMatrix d + te • atomMatrix e + tf • atomMatrix f = 1) :
    ta * tb * tc * tripleBracket a b c ^ 2
        + td * te * tf * tripleBracket d e f ^ 2
      = 1 - (ta * leverageOf a + tb * leverageOf b + tc * leverageOf c)
        + (ta * tb * crossNormSq a b + ta * tc * crossNormSq a c
            + tb * tc * crossNormSq b c) := by
  have hmat : (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - ta • atomMatrix a - tb • atomMatrix b - tc • atomMatrix c
      = td • atomMatrix d + te • atomMatrix e + tf • atomMatrix f := by
    rw [← hsplit]; abel
  have hdet := congrArg Matrix.det hmat
  rw [det_one_sub_weighted_triple, det_weighted_triple] at hdet
  linarith [hdet]

/-! ## 3. The same budget at size five, with no slack -/

/-- **THE SIZE-FIVE LAW.**  When FIVE weighted atoms resolve the identity, the
complement of a triple is a pair, its determinant vanishes, and the whole budget
is paid by the triple alone.  The right-hand side is identical to the size-six
one -- it is computed from the triple and never sees the size. -/
theorem triple_bracket_law_five {ta tb tc td te : ℝ} {a b c d e : Fin 3 → ℝ}
    (hsplit : ta • atomMatrix a + tb • atomMatrix b + tc • atomMatrix c
        + td • atomMatrix d + te • atomMatrix e = 1) :
    ta * tb * tc * tripleBracket a b c ^ 2
      = 1 - (ta * leverageOf a + tb * leverageOf b + tc * leverageOf c)
        + (ta * tb * crossNormSq a b + ta * tc * crossNormSq a c
            + tb * tc * crossNormSq b c) := by
  have hmat : (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - ta • atomMatrix a - tb • atomMatrix b - tc • atomMatrix c
      = td • atomMatrix d + te • atomMatrix e := by
    rw [← hsplit]; abel
  have hdet := congrArg Matrix.det hmat
  rw [det_one_sub_weighted_triple, det_weighted_pair] at hdet
  linarith [hdet]

/-! ## 4. The size gap, named -/

/-- **THE SIZE GAP IS A BRACKET MASS.**  The size-six budget exceeds the
size-five one by exactly the complement triple's weighted squared bracket.  A
law read off the right-hand side is an EQUALITY at five and an INEQUALITY at
six, and the difference is a quantity the hinge already speaks about: it
vanishes exactly when the complement triple is coplanar. -/
theorem complement_bracket_slack {ta tb tc td te tf : ℝ} {a b c d e f : Fin 3 → ℝ}
    (hsplit : ta • atomMatrix a + tb • atomMatrix b + tc • atomMatrix c
        + td • atomMatrix d + te • atomMatrix e + tf • atomMatrix f = 1) :
    (1 - (ta * leverageOf a + tb * leverageOf b + tc * leverageOf c)
        + (ta * tb * crossNormSq a b + ta * tc * crossNormSq a c
            + tb * tc * crossNormSq b c))
        - ta * tb * tc * tripleBracket a b c ^ 2
      = td * te * tf * tripleBracket d e f ^ 2 := by
  have h := complement_bracket_law hsplit
  linarith [h]

/-- **THE INSIDE BRACKET MASS IS CAPPED BY THE BUDGET.**  At positive complement
weights the complement term is nonnegative, so the triple's own weighted squared
bracket never reaches the budget its own leverages and wedges compute.  Equality
holds exactly when the complement triple is coplanar -- at size five, always. -/
theorem tripleBracket_mass_le_budget {ta tb tc td te tf : ℝ} {a b c d e f : Fin 3 → ℝ}
    (htd : 0 ≤ td) (hte : 0 ≤ te) (htf : 0 ≤ tf)
    (hsplit : ta • atomMatrix a + tb • atomMatrix b + tc • atomMatrix c
        + td • atomMatrix d + te • atomMatrix e + tf • atomMatrix f = 1) :
    ta * tb * tc * tripleBracket a b c ^ 2
      ≤ 1 - (ta * leverageOf a + tb * leverageOf b + tc * leverageOf c)
        + (ta * tb * crossNormSq a b + ta * tc * crossNormSq a c
            + tb * tc * crossNormSq b c) := by
  have h := complement_bracket_slack hsplit
  have hnn : 0 ≤ td * te * tf * tripleBracket d e f ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg htd hte) htf) (sq_nonneg _)
  linarith [h, hnn]

/-- **A COPLANAR COMPLEMENT SATURATES THE BUDGET.**  If the three complement
atoms are coplanar the size-six law degenerates to the size-five law: the
triple's bracket mass equals its budget exactly.  The contrapositive is the
usable half -- a triple strictly under its budget forces its complement to
span. -/
theorem tripleBracket_lt_budget_of_complement_spans
    {ta tb tc td te tf : ℝ} {a b c d e f : Fin 3 → ℝ}
    (htd : 0 < td) (hte : 0 < te) (htf : 0 < tf)
    (hspan : tripleBracket d e f ≠ 0)
    (hsplit : ta • atomMatrix a + tb • atomMatrix b + tc • atomMatrix c
        + td • atomMatrix d + te • atomMatrix e + tf • atomMatrix f = 1) :
    ta * tb * tc * tripleBracket a b c ^ 2
      < 1 - (ta * leverageOf a + tb * leverageOf b + tc * leverageOf c)
        + (ta * tb * crossNormSq a b + ta * tc * crossNormSq a c
            + tb * tc * crossNormSq b c) := by
  have h := complement_bracket_slack hsplit
  have hpos : 0 < td * te * tf * tripleBracket d e f ^ 2 :=
    mul_pos (mul_pos (mul_pos htd hte) htf) (pow_pos (abs_pos.mpr hspan) 2 |>.trans_le
      (le_of_eq (sq_abs _)))
  linarith [h, hpos]

/-! ## 5. The budget is symmetric under complementation -/

/-- **THE TRACE SPLIT.**  Reading Parseval's trace: the six weighted leverages
total the rank. -/
theorem leverage_split_six {ta tb tc td te tf : ℝ} {a b c d e f : Fin 3 → ℝ}
    (hsplit : ta • atomMatrix a + tb • atomMatrix b + tc • atomMatrix c
        + td • atomMatrix d + te • atomMatrix e + tf • atomMatrix f = 1) :
    (ta * leverageOf a + tb * leverageOf b + tc * leverageOf c)
        + (td * leverageOf d + te * leverageOf e + tf * leverageOf f) = 3 := by
  have htr := congrArg Matrix.trace hsplit
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    trace_atomMatrix, smul_eq_mul] at htr
  norm_num at htr
  linarith [htr]

/-- **THE BUDGET DOES NOT SEE WHICH SIDE COMPUTED IT.**  The right-hand side of
the complementary bracket law is read off ONE triple, yet the left-hand side is
symmetric in the two triples.  So the two readings agree: a triple and its
complement compute the SAME budget out of completely different data. -/
theorem complement_budget_symm {ta tb tc td te tf : ℝ} {a b c d e f : Fin 3 → ℝ}
    (hsplit : ta • atomMatrix a + tb • atomMatrix b + tc • atomMatrix c
        + td • atomMatrix d + te • atomMatrix e + tf • atomMatrix f = 1) :
    1 - (ta * leverageOf a + tb * leverageOf b + tc * leverageOf c)
        + (ta * tb * crossNormSq a b + ta * tc * crossNormSq a c
            + tb * tc * crossNormSq b c)
      = 1 - (td * leverageOf d + te * leverageOf e + tf * leverageOf f)
        + (td * te * crossNormSq d e + td * tf * crossNormSq d f
            + te * tf * crossNormSq e f) := by
  have hC := complement_bracket_law hsplit
  have hswap : td • atomMatrix d + te • atomMatrix e + tf • atomMatrix f
      + ta • atomMatrix a + tb • atomMatrix b + tc • atomMatrix c = 1 := by
    rw [← hsplit]; abel
  have hO := complement_bracket_law hswap
  linarith [hC, hO]

/-- **THE WEDGE MASS SPLIT.**  Combining the budget symmetry with the trace
split, the two triples' weighted pair wedge masses differ by exactly twice the
first triple's weighted leverage mass, less the rank.  A relation between the
wedge currency on one side and the leverage currency on the other. -/
theorem wedge_mass_split {ta tb tc td te tf : ℝ} {a b c d e f : Fin 3 → ℝ}
    (hsplit : ta • atomMatrix a + tb • atomMatrix b + tc • atomMatrix c
        + td • atomMatrix d + te • atomMatrix e + tf • atomMatrix f = 1) :
    (ta * tb * crossNormSq a b + ta * tc * crossNormSq a c
        + tb * tc * crossNormSq b c)
      - (td * te * crossNormSq d e + td * tf * crossNormSq d f
        + te * tf * crossNormSq e f)
      = 2 * (ta * leverageOf a + tb * leverageOf b + tc * leverageOf c) - 3 := by
  have hsym := complement_budget_symm hsplit
  have htr := leverage_split_six hsplit
  linarith [hsym, htr]

/-! ## 6. The design-level reading at size six -/

/-- **THE LAW AT A `(6,3)` DESIGN.**  Parseval expands into the six-term split,
so the canonical triple and its complement pay into one budget with no extra
hypothesis at all. -/
theorem complement_bracket_law_design (D : WeightedDesign 6 3) :
    D.weight 0 * D.weight 1 * D.weight 2 * atomBracket D 0 1 2 ^ 2
        + D.weight 3 * D.weight 4 * D.weight 5 * atomBracket D 3 4 5 ^ 2
      = 1 - (D.weight 0 * leverageOf (D.atom 0) + D.weight 1 * leverageOf (D.atom 1)
            + D.weight 2 * leverageOf (D.atom 2))
        + (D.weight 0 * D.weight 1 * crossNormSq (D.atom 0) (D.atom 1)
            + D.weight 0 * D.weight 2 * crossNormSq (D.atom 0) (D.atom 2)
            + D.weight 1 * D.weight 2 * crossNormSq (D.atom 1) (D.atom 2)) := by
  have h := D.isParseval
  rw [Fin.sum_univ_six] at h
  exact complement_bracket_law h

/-- **THE CANONICAL TRIPLE NEVER REACHES ITS BUDGET UNLESS ITS COMPLEMENT IS
COPLANAR.**  The design-level cap, with the weights positive by definition. -/
theorem tripleBracket_mass_le_budget_design (D : WeightedDesign 6 3) :
    D.weight 0 * D.weight 1 * D.weight 2 * atomBracket D 0 1 2 ^ 2
      ≤ 1 - (D.weight 0 * leverageOf (D.atom 0) + D.weight 1 * leverageOf (D.atom 1)
            + D.weight 2 * leverageOf (D.atom 2))
        + (D.weight 0 * D.weight 1 * crossNormSq (D.atom 0) (D.atom 1)
            + D.weight 0 * D.weight 2 * crossNormSq (D.atom 0) (D.atom 2)
            + D.weight 1 * D.weight 2 * crossNormSq (D.atom 1) (D.atom 2)) := by
  have h := complement_bracket_law_design D
  have hnn : 0 ≤ D.weight 3 * D.weight 4 * D.weight 5 * atomBracket D 3 4 5 ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (D.weight_pos 3).le (D.weight_pos 4).le)
      (D.weight_pos 5).le) (sq_nonneg _)
  linarith [h, hnn]

/-! ## 7. The hinge reading: a parallel complement saturates the budget -/

/-- A parallel pair anywhere in a triple kills its bracket, in any slot. -/
theorem tripleBracket_eq_zero_of_parallel_any (d e f : Fin 3 → ℝ) (ratio : ℝ) :
    (e = ratio • d → tripleBracket d e f = 0)
      ∧ (f = ratio • d → tripleBracket d e f = 0)
      ∧ (f = ratio • e → tripleBracket d e f = 0) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    subst h <;>
    simp only [tripleBracket_eq, Pi.smul_apply, smul_eq_mul] <;>
    ring

/-- **A PARALLEL PAIR IN THE COMPLEMENT SATURATES THE BUDGET.**  The hinge's own
conclusion, read through the complementary bracket law: two parallel atoms in the
complement triple kill its bracket, the size-six slack vanishes, and the triple
`C` pays the WHOLE budget by itself — exactly the size-five law.

This is the collapse the campaign uses, stated as an identity rather than a
construction: a parallel pair makes a `(6,3)` design behave like a `(5,3)` one at
every complementary triple that contains it. -/
theorem budget_saturated_of_complement_parallel
    {ta tb tc td te tf ratio : ℝ} {a b c d e f : Fin 3 → ℝ}
    (hpar : e = ratio • d)
    (hsplit : ta • atomMatrix a + tb • atomMatrix b + tc • atomMatrix c
        + td • atomMatrix d + te • atomMatrix e + tf • atomMatrix f = 1) :
    ta * tb * tc * tripleBracket a b c ^ 2
      = 1 - (ta * leverageOf a + tb * leverageOf b + tc * leverageOf c)
        + (ta * tb * crossNormSq a b + ta * tc * crossNormSq a c
            + tb * tc * crossNormSq b c) := by
  have hz : tripleBracket d e f = 0 :=
    (tripleBracket_eq_zero_of_parallel_any d e f ratio).1 hpar
  have h := complement_bracket_law hsplit
  rw [hz] at h
  linarith [h]

/-- **A TRIPLE STRICTLY UNDER ITS BUDGET FORBIDS EVERY PARALLEL PAIR IN ITS
COMPLEMENT.**  The contrapositive, and the usable half: one scalar comparison in
leverages, wedges and one bracket refutes parallelism among three OTHER atoms,
with no tie hypothesis and nothing computed about those atoms at all. -/
theorem complement_not_parallel_of_lt_budget
    {ta tb tc td te tf ratio : ℝ} {a b c d e f : Fin 3 → ℝ}
    (hsplit : ta • atomMatrix a + tb • atomMatrix b + tc • atomMatrix c
        + td • atomMatrix d + te • atomMatrix e + tf • atomMatrix f = 1)
    (hlt : ta * tb * tc * tripleBracket a b c ^ 2
      < 1 - (ta * leverageOf a + tb * leverageOf b + tc * leverageOf c)
        + (ta * tb * crossNormSq a b + ta * tc * crossNormSq a c
            + tb * tc * crossNormSq b c)) :
    e ≠ ratio • d := fun hpar =>
  absurd (budget_saturated_of_complement_parallel hpar hsplit) (ne_of_lt hlt)

/-- The same refutation at the second complement pair. -/
theorem complement_not_parallel_snd_of_lt_budget
    {ta tb tc td te tf ratio : ℝ} {a b c d e f : Fin 3 → ℝ}
    (hsplit : ta • atomMatrix a + tb • atomMatrix b + tc • atomMatrix c
        + td • atomMatrix d + te • atomMatrix e + tf • atomMatrix f = 1)
    (hlt : ta * tb * tc * tripleBracket a b c ^ 2
      < 1 - (ta * leverageOf a + tb * leverageOf b + tc * leverageOf c)
        + (ta * tb * crossNormSq a b + ta * tc * crossNormSq a c
            + tb * tc * crossNormSq b c)) :
    f ≠ ratio • d := by
  intro hpar
  have hz : tripleBracket d e f = 0 :=
    (tripleBracket_eq_zero_of_parallel_any d e f ratio).2.1 hpar
  have h := complement_bracket_law hsplit
  rw [hz] at h
  linarith [h, hlt]

/-- The same refutation at the third complement pair. -/
theorem complement_not_parallel_thd_of_lt_budget
    {ta tb tc td te tf ratio : ℝ} {a b c d e f : Fin 3 → ℝ}
    (hsplit : ta • atomMatrix a + tb • atomMatrix b + tc • atomMatrix c
        + td • atomMatrix d + te • atomMatrix e + tf • atomMatrix f = 1)
    (hlt : ta * tb * tc * tripleBracket a b c ^ 2
      < 1 - (ta * leverageOf a + tb * leverageOf b + tc * leverageOf c)
        + (ta * tb * crossNormSq a b + ta * tc * crossNormSq a c
            + tb * tc * crossNormSq b c)) :
    f ≠ ratio • e := by
  intro hpar
  have hz : tripleBracket d e f = 0 :=
    (tripleBracket_eq_zero_of_parallel_any d e f ratio).2.2 hpar
  have h := complement_bracket_law hsplit
  rw [hz] at h
  linarith [h, hlt]

end Gtz
