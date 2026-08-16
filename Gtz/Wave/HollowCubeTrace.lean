import Gtz.Wave.ProjectionMinorShift

/-!
# The hollow cube trace law: an off-diagonal cubic read from the diagonal alone

`Gtz.tripleDetForm_neg_first` proves the sign of the triple pairing product
`u v w` is INTRINSIC to a selection, and `Gtz.tripleDetForm_equilateral` shows
that sign is exactly what kills the third Sylvester minor.  Every landed cell
that reaches the third minor is sign-free and pays a constant for it.

This file supplies the missing sign information from the DIAGONAL.

Write `Pi` for the projection form of a design, `t_c = Pi_cc` for the leverage
and `N = Pi - diagonal t` for the hollow part.  The law is

  `trace (N N N) = trace Pi - 3 * sum_c t_c ^ 2 + 2 * sum_c t_c ^ 3`

and its proof needs only `Pi Pi = Pi` and the cyclic invariance of the trace.
No row law, no eigenvalue, no square root, no symmetry.

`trace (N N N)` is the sum over ORDERED index triples of `N_ab N_bc N_ca`, and
every term with a repeated index vanishes because `N` is hollow.  So a positive
trace forces a triple of DISTINCT labels whose three pairings multiply
positive, which is the sign hypothesis of `Gtz.tripleDetForm_pos_of_nonneg_cross`.

At `(6, 3)` the leverage total is the rank, so `3` may be replaced by
`sum_c t_c` and the whole right-hand side collapses to a sum of ONE-VARIABLE
cubics, `Gtz.leverageCubic t = t * (t - 1) * (2 * t - 1)`.  That cubic is
antisymmetric about `1 / 2`, it is NON-NEGATIVE on `[0, 1/2]`, and it is
NON-POSITIVE on `[1/2, 1]`.

The naive reading of that sign is VACUOUS and this file proves so.  At a label
count of twice the rank the leverage average IS one half, so the leverages can
neither all sit below it nor all sit above it (`Gtz.not_forall_lt_half`).  What
survives is the CENTRED form: the linear and quadratic parts cancel identically
and the total becomes twice the third moment of the leverages about one half
(`Gtz.sum_leverageCubic_eq_two_mul_sum_cube`).  So the sign question is a
SKEWNESS question about six numbers, and skewness is not obstructed.

The stronger half of the file is PER VERTEX.  The same eight-word expansion read
on a diagonal entry rather than on the trace gives

  `(N N N)_cc = t_c (1 - t_c) ^ 2 - sum over the other labels of t_d Pi_cd ^ 2`

and a positive value names a coherent triangle THROUGH `c`.  Pricing the weighted
row energy by a cap on the other leverages leaves `t_c (1 - t_c) (1 - t_c - cap)`,
so a vertex hosts a coherent triangle as soon as `t_c + cap < 1`.  That reads TWO
diagonal numbers.

Both readings go silent at the equal-share profile `t = 1 / 2`, where the vertex
law cancels exactly and the cap condition misses by one unit of slack.  That
profile is the equiangular configuration, `Gtz.icosaDesign`, and two further
landed certificates go silent at the same point.
-/

namespace Gtz

open Matrix Finset

section HollowPart

variable {size : ℕ}

/-- **THE HOLLOW PART.**  The form with its diagonal deleted. -/
def hollowPart (form : Matrix (Fin size) (Fin size) ℝ) : Matrix (Fin size) (Fin size) ℝ :=
  form - Matrix.diagonal (fun index => form index index)

theorem hollowPart_apply (form : Matrix (Fin size) (Fin size) ℝ)
    (rowIndex colIndex : Fin size) :
    hollowPart form rowIndex colIndex
      = if rowIndex = colIndex then 0 else form rowIndex colIndex := by
  rw [hollowPart, Matrix.sub_apply, Matrix.diagonal_apply]
  split_ifs with hmatch
  · subst hmatch; ring
  · ring

@[simp] theorem hollowPart_diagonal (form : Matrix (Fin size) (Fin size) ℝ)
    (index : Fin size) : hollowPart form index index = 0 := by
  rw [hollowPart_apply, if_pos rfl]

theorem hollowPart_off (form : Matrix (Fin size) (Fin size) ℝ)
    {rowIndex colIndex : Fin size} (hne : rowIndex ≠ colIndex) :
    hollowPart form rowIndex colIndex = form rowIndex colIndex := by
  rw [hollowPart_apply, if_neg hne]

theorem hollowPart_transpose (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymm : formᵀ = form) : (hollowPart form)ᵀ = hollowPart form := by
  ext rowIndex colIndex
  rw [Matrix.transpose_apply, hollowPart_apply, hollowPart_apply]
  split_ifs with hleft hright
  · rfl
  · exact absurd hleft.symm hright
  · next hright => exact absurd hright.symm hleft
  · exact (congrFun (congrFun hsymm rowIndex) colIndex : form colIndex rowIndex = _)

theorem hollowPart_add_diagonal (form : Matrix (Fin size) (Fin size) ℝ) :
    hollowPart form + Matrix.diagonal (fun index => form index index) = form := by
  rw [hollowPart, sub_add_cancel]

end HollowPart

section TraceHelpers

variable {size : ℕ}

/-- The diagonal-cube trace specialised to a form's own diagonal.  The general
statements `Gtz.trace_mul_diagonal`, `Gtz.trace_mul_diagonal_diagonal` and
`Gtz.trace_diagonal_cube` are landed in `Gtz/Wave/ProjectionMinorShift.lean` and
consumed here rather than repeated. -/
theorem trace_mul_diagonal_mul_diagonal (form : Matrix (Fin size) (Fin size) ℝ) :
    (form * Matrix.diagonal (fun index => form index index)
        * Matrix.diagonal (fun index => form index index)).trace
      = ∑ index, form index index ^ 3 := by
  rw [trace_mul_diagonal_diagonal]
  exact Finset.sum_congr rfl fun index _ => by ring

end TraceHelpers

section CubeLaw

variable {size : ℕ}

/-- The mixed trace with one diagonal factor collapses onto the diagonal. -/
theorem trace_mul_self_mul_diagonal (form : Matrix (Fin size) (Fin size) ℝ)
    (hidem : form * form = form) :
    (form * form * Matrix.diagonal (fun index => form index index)).trace
      = ∑ index, form index index ^ 2 := by
  rw [hidem, trace_mul_diagonal]
  exact Finset.sum_congr rfl fun index _ => by ring

/-- The middle word of weight one shares the trace of the right-hand word. -/
theorem trace_word_middle_one (form other : Matrix (Fin size) (Fin size) ℝ) :
    (form * other * form).trace = (form * form * other).trace := by
  rw [Matrix.trace_mul_comm (form * other) form, ← Matrix.mul_assoc]

/-- The left word of weight one shares the trace of the right-hand word. -/
theorem trace_word_left_one (form other : Matrix (Fin size) (Fin size) ℝ) :
    (other * form * form).trace = (form * form * other).trace := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]

/-- The middle word of weight two shares the trace of the left-hand word. -/
theorem trace_word_middle_two (form other : Matrix (Fin size) (Fin size) ℝ) :
    (other * form * other).trace = (form * other * other).trace := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]

/-- The right word of weight two shares the trace of the left-hand word. -/
theorem trace_word_right_two (form other : Matrix (Fin size) (Fin size) ℝ) :
    (other * other * form).trace = (form * other * other).trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]

/-- **THE HOLLOW CUBE TRACE LAW.**  For any idempotent form the cube trace of its
hollow part is a cubic in the diagonal and nothing else.

The proof expands the eight words of `(Pi - D) (Pi - D) (Pi - D)`, uses `Pi Pi = Pi`
on the three words of weight zero and one, and the cyclic invariance of the trace
to merge each weight class.  Symmetry is never used. -/
theorem trace_hollowPart_cube_of_idempotent (form : Matrix (Fin size) (Fin size) ℝ)
    (hidem : form * form = form) :
    (hollowPart form * hollowPart form * hollowPart form).trace
      = form.trace - 3 * (∑ index, form index index ^ 2)
        + 2 * ∑ index, form index index ^ 3 := by
  classical
  set diagForm : Matrix (Fin size) (Fin size) ℝ :=
    Matrix.diagonal (fun index => form index index) with hdiagForm
  have hexpand : hollowPart form * hollowPart form * hollowPart form
      = form * form * form
        - (form * form * diagForm + form * diagForm * form + diagForm * form * form)
        + (form * diagForm * diagForm + diagForm * form * diagForm
            + diagForm * diagForm * form)
        - diagForm * diagForm * diagForm := by
    simp only [hollowPart, hdiagForm]
    noncomm_ring
  have hcube : (form * form * form).trace = form.trace := by
    rw [hidem, hidem]
  have hsquareTerm : (form * form * diagForm).trace = ∑ index, form index index ^ 2 := by
    rw [hdiagForm]; exact trace_mul_self_mul_diagonal form hidem
  have hcubeTerm : (form * diagForm * diagForm).trace = ∑ index, form index index ^ 3 := by
    rw [hdiagForm]; exact trace_mul_diagonal_mul_diagonal form
  have hdiagCube : (diagForm * diagForm * diagForm).trace = ∑ index, form index index ^ 3 := by
    rw [hdiagForm]; exact trace_diagonal_cube _
  rw [hexpand]
  simp only [Matrix.trace_sub, Matrix.trace_add]
  rw [hcube, trace_word_middle_one form diagForm, trace_word_left_one form diagForm,
    trace_word_middle_two form diagForm, trace_word_right_two form diagForm,
    hsquareTerm, hcubeTerm, hdiagCube]
  ring

end CubeLaw

section LeverageCubic

/-- **THE LEVERAGE CUBIC.**  The one-variable cubic the hollow cube trace
collapses to when the diagonal total equals the rank. -/
def leverageCubic (leverage : ℝ) : ℝ := leverage * (leverage - 1) * (2 * leverage - 1)

theorem leverageCubic_expand (leverage : ℝ) :
    leverageCubic leverage = 2 * leverage ^ 3 - 3 * leverage ^ 2 + leverage := by
  rw [leverageCubic]; ring

@[simp] theorem leverageCubic_zero : leverageCubic 0 = 0 := by
  rw [leverageCubic]; ring

@[simp] theorem leverageCubic_one : leverageCubic 1 = 0 := by
  rw [leverageCubic]; ring

@[simp] theorem leverageCubic_half : leverageCubic (1 / 2) = 0 := by
  rw [leverageCubic]; ring

/-- **THE ANTISYMMETRY.**  The cubic reverses sign under reflection in one half.
This is why every leverage profile symmetric about one half gives zero, and it is
the reason the law carries no information at the equal-share stratum. -/
theorem leverageCubic_reflect (leverage : ℝ) :
    leverageCubic (1 - leverage) = -leverageCubic leverage := by
  rw [leverageCubic, leverageCubic]; ring

/-- **THE SIGN, BELOW ONE HALF.**  A leverage in `[0, 1/2]` contributes
NON-NEGATIVELY.  Both later factors are non-positive there, so their product is
non-negative. -/
theorem leverageCubic_nonneg_of_le_half {leverage : ℝ} (hlow : 0 ≤ leverage)
    (hhigh : leverage ≤ 1 / 2) : 0 ≤ leverageCubic leverage := by
  rw [leverageCubic]
  have hfirst : leverage - 1 ≤ 0 := by linarith
  have hsecond : 2 * leverage - 1 ≤ 0 := by linarith
  nlinarith [mul_nonneg (neg_nonneg.mpr hfirst) (neg_nonneg.mpr hsecond)]

/-- **THE SIGN, STRICTLY BELOW ONE HALF.**  A leverage strictly inside
`(0, 1/2)` contributes STRICTLY POSITIVELY. -/
theorem leverageCubic_pos_of_lt_half {leverage : ℝ} (hlow : 0 < leverage)
    (hhigh : leverage < 1 / 2) : 0 < leverageCubic leverage := by
  rw [leverageCubic]
  have hfirst : leverage - 1 < 0 := by linarith
  have hsecond : 2 * leverage - 1 < 0 := by linarith
  nlinarith [mul_pos (neg_pos.mpr hfirst) (neg_pos.mpr hsecond)]

/-- **THE SIGN, ABOVE ONE HALF.**  A leverage in `[1/2, 1]` contributes
NON-POSITIVELY.  This is the opposite of the naive reading, and it says a heavy
leverage profile pushes the coherent-triangle total DOWN, not up. -/
theorem leverageCubic_nonpos_of_half_le {leverage : ℝ} (hlow : 1 / 2 ≤ leverage)
    (hhigh : leverage ≤ 1) : leverageCubic leverage ≤ 0 := by
  rw [leverageCubic]
  have hfirst : leverage - 1 ≤ 0 := by linarith
  have hsecond : 0 ≤ 2 * leverage - 1 := by linarith
  nlinarith [mul_nonneg (neg_nonneg.mpr hfirst) hsecond]

/-- **THE SIGN, STRICTLY ABOVE ONE HALF.** -/
theorem leverageCubic_neg_of_half_lt {leverage : ℝ} (hlow : 1 / 2 < leverage)
    (hhigh : leverage < 1) : leverageCubic leverage < 0 := by
  rw [leverageCubic]
  have hfirst : leverage - 1 < 0 := by linarith
  have hsecond : 0 < 2 * leverage - 1 := by linarith
  nlinarith [mul_pos (neg_pos.mpr hfirst) hsecond]

end LeverageCubic

section ProfileForm

variable {size : ℕ}

/-- **THE PROFILE FORM.**  When the diagonal total equals the trace, the hollow
cube trace is a sum of leverage cubics.  This is the step that removes the rank
from the right-hand side and leaves six one-variable terms. -/
theorem trace_hollowPart_cube_eq_sum_leverageCubic
    (form : Matrix (Fin size) (Fin size) ℝ) (hidem : form * form = form) :
    (hollowPart form * hollowPart form * hollowPart form).trace
      = ∑ index, leverageCubic (form index index) := by
  rw [trace_hollowPart_cube_of_idempotent form hidem]
  rw [show form.trace = ∑ index, form index index from rfl]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun index _ => by rw [leverageCubic_expand]; ring

end ProfileForm

section SignConsequence

variable {size : ℕ}

/-- The cube trace is the ordered triple sum of the hollow entries. -/
theorem trace_hollowPart_cube_eq_orderedSum (form : Matrix (Fin size) (Fin size) ℝ) :
    (hollowPart form * hollowPart form * hollowPart form).trace
      = ∑ first, ∑ third, ∑ second,
          hollowPart form first second * hollowPart form second third
            * hollowPart form third first := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun first _ => ?_
  refine Finset.sum_congr rfl fun third _ => ?_
  rw [Finset.sum_mul]

/-- Every ordered triple with a repeated index contributes nothing. -/
theorem hollowPart_orderedTerm_eq_zero_of_not_distinct
    (form : Matrix (Fin size) (Fin size) ℝ) {first second third : Fin size}
    (hrepeat : first = second ∨ second = third ∨ third = first) :
    hollowPart form first second * hollowPart form second third
      * hollowPart form third first = 0 := by
  rcases hrepeat with hcase | hcase | hcase
  · subst hcase; rw [hollowPart_diagonal]; ring
  · subst hcase; rw [hollowPart_diagonal]; ring
  · subst hcase; rw [hollowPart_diagonal]; ring

/-- **THE SIGN CONSEQUENCE.**  A positive hollow cube trace forces a triple of
DISTINCT labels whose three pairings multiply strictly positive.

The proof is the contrapositive and it never counts the six orderings: if every
distinct ordered triple were non-positive then every summand of the cube trace
would be non-positive, because the repeated ones vanish. -/
theorem exists_coherent_triple_of_trace_pos (form : Matrix (Fin size) (Fin size) ℝ)
    (hpos : 0 < (hollowPart form * hollowPart form * hollowPart form).trace) :
    ∃ first second third : Fin size, first ≠ second ∧ second ≠ third ∧ third ≠ first ∧
      0 < form first second * form second third * form third first := by
  classical
  by_contra hnone
  push Not at hnone
  have hterm : ∀ first third second : Fin size,
      hollowPart form first second * hollowPart form second third
        * hollowPart form third first ≤ 0 := by
    intro first third second
    by_cases hone : first = second
    · exact le_of_eq (hollowPart_orderedTerm_eq_zero_of_not_distinct form (Or.inl hone))
    by_cases htwo : second = third
    · exact le_of_eq (hollowPart_orderedTerm_eq_zero_of_not_distinct form (Or.inr (Or.inl htwo)))
    by_cases hthree : third = first
    · exact le_of_eq
        (hollowPart_orderedTerm_eq_zero_of_not_distinct form (Or.inr (Or.inr hthree)))
    rw [hollowPart_off form hone, hollowPart_off form htwo, hollowPart_off form hthree]
    exact hnone first second third hone htwo hthree
  have hsum : (hollowPart form * hollowPart form * hollowPart form).trace ≤ 0 := by
    rw [trace_hollowPart_cube_eq_orderedSum]
    refine Finset.sum_nonpos fun first _ => ?_
    refine Finset.sum_nonpos fun third _ => ?_
    exact Finset.sum_nonpos fun second _ => hterm first third second
  linarith

/-- **THE MIRROR.**  A negative hollow cube trace forces an INCOHERENT triple. -/
theorem exists_incoherent_triple_of_trace_neg (form : Matrix (Fin size) (Fin size) ℝ)
    (hneg : (hollowPart form * hollowPart form * hollowPart form).trace < 0) :
    ∃ first second third : Fin size, first ≠ second ∧ second ≠ third ∧ third ≠ first ∧
      form first second * form second third * form third first < 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hterm : ∀ first third second : Fin size,
      0 ≤ hollowPart form first second * hollowPart form second third
        * hollowPart form third first := by
    intro first third second
    by_cases hone : first = second
    · exact ge_of_eq (hollowPart_orderedTerm_eq_zero_of_not_distinct form (Or.inl hone))
    by_cases htwo : second = third
    · exact ge_of_eq (hollowPart_orderedTerm_eq_zero_of_not_distinct form (Or.inr (Or.inl htwo)))
    by_cases hthree : third = first
    · exact ge_of_eq
        (hollowPart_orderedTerm_eq_zero_of_not_distinct form (Or.inr (Or.inr hthree)))
    rw [hollowPart_off form hone, hollowPart_off form htwo, hollowPart_off form hthree]
    exact hnone first second third hone htwo hthree
  have hsum : 0 ≤ (hollowPart form * hollowPart form * hollowPart form).trace := by
    rw [trace_hollowPart_cube_eq_orderedSum]
    refine Finset.sum_nonneg fun first _ => ?_
    refine Finset.sum_nonneg fun third _ => ?_
    exact Finset.sum_nonneg fun second _ => hterm first third second
  linarith

end SignConsequence

section CentredForm

variable {size : ℕ}

/-- **THE CENTRED FORM.**  When the leverage total is HALF the label count the
cubic total is twice the third moment of the leverages about one half.

The linear and quadratic parts cancel identically, and only the cube survives.
This is the form the law is usable in, because it turns a sign question about
twenty triples into a SKEWNESS question about six numbers. -/
theorem sum_leverageCubic_eq_two_mul_sum_cube (profile : Fin size → ℝ)
    (htotal : ∑ index, profile index = (size : ℝ) / 2) :
    ∑ index, leverageCubic (profile index)
      = 2 * ∑ index, (profile index - 1 / 2) ^ 3 := by
  classical
  have hconst : ((size : ℝ) * (1 / 4)) = ∑ _index : Fin size, (1 / 4 : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hstep : ∑ index, leverageCubic (profile index)
      = 2 * (∑ index, (profile index - 1 / 2) ^ 3)
        - (1 / 2) * (∑ index, profile index) + (size : ℝ) * (1 / 4) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, hconst,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun index _ => by rw [leverageCubic]; ring
  rw [hstep, htotal]
  ring

/-- **THE STRADDLE.**  At a label count of twice the rank the leverages cannot all
sit strictly below one half, and they cannot all sit strictly above it.  The
average IS one half.

This is why the naive "all leverages small" certificate is VACUOUS at `(6, 3)`
and why the centred form above is the one to use. -/
theorem not_forall_lt_half (profile : Fin size → ℝ) (hsize : 0 < size)
    (htotal : ∑ index, profile index = (size : ℝ) / 2) :
    ¬ (∀ index, profile index < 1 / 2) := by
  classical
  intro hall
  have hstrict : ∑ index : Fin size, profile index < ∑ _index : Fin size, (1 : ℝ) / 2 :=
    Finset.sum_lt_sum_of_nonempty
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hsize))
      fun index _ => hall index
  rw [htotal] at hstrict
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hstrict
  linarith

/-- The mirror straddle. -/
theorem not_forall_half_lt (profile : Fin size → ℝ) (hsize : 0 < size)
    (htotal : ∑ index, profile index = (size : ℝ) / 2) :
    ¬ (∀ index, (1 : ℝ) / 2 < profile index) := by
  classical
  intro hall
  have hstrict : ∑ _index : Fin size, (1 : ℝ) / 2 < ∑ index : Fin size, profile index :=
    Finset.sum_lt_sum_of_nonempty
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hsize))
      fun index _ => hall index
  rw [htotal] at hstrict
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hstrict
  linarith

/-- **THE EQUAL-SHARE SILENCE.**  A leverage profile constant at one half gives a
vanishing cubic total, so the law says nothing there.

The equiangular configuration has exactly this profile.  Two other landed
certificates go silent at the same point, which is what identifies that locus as
the crux rather than as one hard case among many. -/
theorem sum_leverageCubic_eq_zero_of_forall_half (profile : Fin size → ℝ)
    (hhalf : ∀ index, profile index = 1 / 2) :
    ∑ index, leverageCubic (profile index) = 0 := by
  rw [Finset.sum_congr rfl fun index _ => by rw [hhalf index, leverageCubic_half]]
  exact Finset.sum_const_zero

/-- **THE SKEW CERTIFICATE.**  One label deviating upward past the cube-scaled
total of every other downward deviation forces a positive cubic total.

The bound is crude on purpose: it is a sum of cubes against a single cube, so it
costs one monotonicity step per label and no power mean. -/
theorem sum_cube_pos_of_dominant_deviation (deviation : Fin size → ℝ)
    {witness : Fin size} {bound : ℝ}
    (hother : ∀ index, index ≠ witness → -bound ≤ deviation index)
    (hwitness : ((size : ℝ) - 1) * bound ^ 3 < deviation witness ^ 3) :
    0 < ∑ index, deviation index ^ 3 := by
  classical
  have hcube : ∀ index, index ≠ witness → -(bound ^ 3) ≤ deviation index ^ 3 := by
    intro index hne
    have hstep := hother index hne
    nlinarith [sq_nonneg (deviation index), sq_nonneg (deviation index + bound),
      sq_nonneg (deviation index - bound), sq_nonneg bound]
  have hsplit : ∑ index, deviation index ^ 3
      = deviation witness ^ 3
        + ∑ index ∈ Finset.univ.erase witness, deviation index ^ 3 :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ witness)).symm
  have hcard : (Finset.univ.erase witness).card = size - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ witness), Finset.card_univ,
      Fintype.card_fin]
  have hlower : -(((size : ℝ) - 1) * bound ^ 3)
      ≤ ∑ index ∈ Finset.univ.erase witness, deviation index ^ 3 := by
    have hterm : ∀ index ∈ Finset.univ.erase witness, -(bound ^ 3) ≤ deviation index ^ 3 :=
      fun index hmem => hcube index (Finset.ne_of_mem_erase hmem)
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at hsum
    have hsizePos : 1 ≤ size := by
      by_contra hcontra
      push Not at hcontra
      interval_cases size
      · exact absurd witness.isLt (by omega)
    have hcast : ((size - 1 : ℕ) : ℝ) = (size : ℝ) - 1 := by
      have := Nat.cast_sub (R := ℝ) hsizePos
      simpa using this
    rw [hcast] at hsum
    linarith
  rw [hsplit]
  linarith

end CentredForm

section DesignCertificate

variable {size rank : ℕ}

/-- The hollow cube trace of a design's projection form, in profile terms. -/
theorem trace_hollowPart_projection_eq_sum_leverageCubic (design : WeightedDesign size rank) :
    (hollowPart (projectionOfDesign design) * hollowPart (projectionOfDesign design)
        * hollowPart (projectionOfDesign design)).trace
      = ∑ index, leverageCubic (projectionOfDesign design index index) :=
  trace_hollowPart_cube_eq_sum_leverageCubic _ (projectionOfDesign_mul_self design)

/-- **THE DESIGN-LEVEL SIGN CERTIFICATE.**  A design whose leverage profile has a
strictly positive cubic total carries a COHERENT triple: three distinct labels
whose three pairings multiply strictly positive.

That is exactly the hypothesis `Gtz.tripleDetForm_pos_of_nonneg_cross` consumes,
and it is read off the diagonal of the projection form alone. -/
theorem exists_coherent_triple_of_sum_leverageCubic_pos (design : WeightedDesign size rank)
    (hprofile : 0 < ∑ index, leverageCubic (projectionOfDesign design index index)) :
    ∃ first second third : Fin size, first ≠ second ∧ second ≠ third ∧ third ≠ first ∧
      0 < projectionOfDesign design first second * projectionOfDesign design second third
        * projectionOfDesign design third first := by
  refine exists_coherent_triple_of_trace_pos (projectionOfDesign design) ?_
  rw [trace_hollowPart_projection_eq_sum_leverageCubic design]
  exact hprofile

/-- The mirror: a strictly negative cubic total forces an incoherent triple. -/
theorem exists_incoherent_triple_of_sum_leverageCubic_neg (design : WeightedDesign size rank)
    (hprofile : ∑ index, leverageCubic (projectionOfDesign design index index) < 0) :
    ∃ first second third : Fin size, first ≠ second ∧ second ≠ third ∧ third ≠ first ∧
      projectionOfDesign design first second * projectionOfDesign design second third
        * projectionOfDesign design third first < 0 := by
  refine exists_incoherent_triple_of_trace_neg (projectionOfDesign design) ?_
  rw [trace_hollowPart_projection_eq_sum_leverageCubic design]
  exact hprofile

/-- **THE SKEW CERTIFICATE AT A DESIGN.**  At twice-the-rank labels, one leverage
deviating upward past the cube-scaled downward deviations of the rest forces a
coherent triple. -/
theorem exists_coherent_triple_of_dominant_leverage (design : WeightedDesign size rank)
    (htotal : ∑ index, projectionOfDesign design index index = (size : ℝ) / 2)
    {witness : Fin size} {bound : ℝ}
    (hother : ∀ index, index ≠ witness →
      1 / 2 - bound ≤ projectionOfDesign design index index)
    (hwitness : ((size : ℝ) - 1) * bound ^ 3
      < (projectionOfDesign design witness witness - 1 / 2) ^ 3) :
    ∃ first second third : Fin size, first ≠ second ∧ second ≠ third ∧ third ≠ first ∧
      0 < projectionOfDesign design first second * projectionOfDesign design second third
        * projectionOfDesign design third first := by
  refine exists_coherent_triple_of_sum_leverageCubic_pos design ?_
  rw [sum_leverageCubic_eq_two_mul_sum_cube _ htotal]
  have hdev : 0 < ∑ index, (projectionOfDesign design index index - 1 / 2) ^ 3 := by
    refine sum_cube_pos_of_dominant_deviation
      (fun index => projectionOfDesign design index index - 1 / 2) ?_ hwitness
    intro index hne
    have := hother index hne
    linarith
  linarith

end DesignCertificate

section VertexLaw

variable {size : ℕ}

theorem symm_apply (form : Matrix (Fin size) (Fin size) ℝ) (hsymm : formᵀ = form)
    (rowIndex colIndex : Fin size) : form colIndex rowIndex = form rowIndex colIndex :=
  congrFun (congrFun hsymm rowIndex) colIndex

/-- The row-square total of a symmetric idempotent is its own diagonal entry. -/
theorem sum_sq_row_of_idempotent (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymm : formᵀ = form) (hidem : form * form = form) (rowIndex : Fin size) :
    ∑ colIndex, form rowIndex colIndex ^ 2 = form rowIndex rowIndex := by
  have hentry : (form * form) rowIndex rowIndex = form rowIndex rowIndex := by rw [hidem]
  rw [Matrix.mul_apply] at hentry
  rw [← hentry]
  exact Finset.sum_congr rfl fun colIndex _ => by
    rw [sq, symm_apply form hsymm rowIndex colIndex]

/-- The off-diagonal row energy of a symmetric idempotent. -/
theorem sum_erase_sq_row_of_idempotent (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymm : formᵀ = form) (hidem : form * form = form) (rowIndex : Fin size) :
    ∑ colIndex ∈ Finset.univ.erase rowIndex, form rowIndex colIndex ^ 2
      = form rowIndex rowIndex - form rowIndex rowIndex ^ 2 := by
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun colIndex => form rowIndex colIndex ^ 2) (Finset.mem_univ rowIndex)
  rw [sum_sq_row_of_idempotent form hsymm hidem rowIndex] at hsplit
  linarith [hsplit]

/-- The middle-word diagonal entry reads the whole row against the diagonal. -/
theorem diag_mul_diagonal_mul_apply (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymm : formᵀ = form) (scaleVec : Fin size → ℝ) (rowIndex : Fin size) :
    (form * Matrix.diagonal scaleVec * form) rowIndex rowIndex
      = ∑ colIndex, scaleVec colIndex * form rowIndex colIndex ^ 2 := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun colIndex _ => by
    rw [Matrix.mul_diagonal, sq, symm_apply form hsymm rowIndex colIndex]
    ring

/-- **THE PER-VERTEX HOLLOW CUBE LAW.**  For a symmetric idempotent the diagonal
of the hollow cube is a cubic in the vertex leverage MINUS the row energy weighted
by the other leverages.

This is strictly stronger than the trace law, which is its total.  It names the
vertex, and the vertex is what a selection needs. -/
theorem hollowPart_cube_diag_of_idempotent (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymm : formᵀ = form) (hidem : form * form = form) (vertex : Fin size) :
    (hollowPart form * hollowPart form * hollowPart form) vertex vertex
      = form vertex vertex - 2 * form vertex vertex ^ 2 + 2 * form vertex vertex ^ 3
        - ∑ other, form other other * form vertex other ^ 2 := by
  classical
  set diagForm : Matrix (Fin size) (Fin size) ℝ :=
    Matrix.diagonal (fun index => form index index) with hdiagForm
  have hexpand : hollowPart form * hollowPart form * hollowPart form
      = form * form * form
        - (form * form * diagForm + form * diagForm * form + diagForm * form * form)
        + (form * diagForm * diagForm + diagForm * form * diagForm
            + diagForm * diagForm * form)
        - diagForm * diagForm * diagForm := by
    simp only [hollowPart, hdiagForm]
    noncomm_ring
  have hcube : (form * form * form) vertex vertex = form vertex vertex := by
    rw [hidem, hidem]
  have hsquareRight : (form * form * diagForm) vertex vertex = form vertex vertex ^ 2 := by
    rw [hidem, hdiagForm, Matrix.mul_diagonal]; ring
  have hsquareLeft : (diagForm * form * form) vertex vertex = form vertex vertex ^ 2 := by
    rw [Matrix.mul_assoc, hidem, hdiagForm, Matrix.diagonal_mul]; ring
  have hmiddle : (form * diagForm * form) vertex vertex
      = ∑ other, form other other * form vertex other ^ 2 :=
    diag_mul_diagonal_mul_apply form hsymm _ vertex
  have hcubeRight : (form * diagForm * diagForm) vertex vertex = form vertex vertex ^ 3 := by
    rw [Matrix.mul_assoc, hdiagForm, Matrix.diagonal_mul_diagonal, Matrix.mul_diagonal]; ring
  have hcubeMiddle : (diagForm * form * diagForm) vertex vertex
      = form vertex vertex ^ 3 := by
    rw [hdiagForm, Matrix.mul_diagonal, Matrix.diagonal_mul]; ring
  have hcubeLeft : (diagForm * diagForm * form) vertex vertex = form vertex vertex ^ 3 := by
    rw [hdiagForm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul]; ring
  have hdiagCube : (diagForm * diagForm * diagForm) vertex vertex
      = form vertex vertex ^ 3 := by
    rw [hdiagForm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq]; ring
  rw [hexpand]
  simp only [Matrix.sub_apply, Matrix.add_apply]
  rw [hcube, hsquareRight, hsquareLeft, hmiddle, hcubeRight, hcubeMiddle, hcubeLeft,
    hdiagCube]
  ring

/-- **THE PER-VERTEX LAW IN CLOSED FORM.**  Deleting the vertex from the weighted
row energy leaves a perfect square times the leverage.

`(N N N)_cc = t_c (1 - t_c) ^ 2 - sum over the other labels of t_d Pi_cd ^ 2`.

At the equal-share profile `t = 1/2` the two sides cancel exactly, which is the
landed observation that the equiangular Seidel cube has zero diagonal. -/
theorem hollowPart_cube_diag_eq (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymm : formᵀ = form) (hidem : form * form = form) (vertex : Fin size) :
    (hollowPart form * hollowPart form * hollowPart form) vertex vertex
      = form vertex vertex * (1 - form vertex vertex) ^ 2
        - ∑ other ∈ Finset.univ.erase vertex, form other other * form vertex other ^ 2 := by
  classical
  rw [hollowPart_cube_diag_of_idempotent form hsymm hidem vertex]
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun other => form other other * form vertex other ^ 2) (Finset.mem_univ vertex)
  have hself : form vertex vertex * form vertex vertex ^ 2 = form vertex vertex ^ 3 := by ring
  rw [hself] at hsplit
  rw [← hsplit]
  ring

end VertexLaw

section VertexSign

variable {size : ℕ}

/-- The hollow cube diagonal is the ordered sum over paths through the vertex. -/
theorem hollowPart_cube_diag_eq_orderedSum (form : Matrix (Fin size) (Fin size) ℝ)
    (vertex : Fin size) :
    (hollowPart form * hollowPart form * hollowPart form) vertex vertex
      = ∑ third, ∑ second,
          hollowPart form vertex second * hollowPart form second third
            * hollowPart form third vertex := by
  simp only [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun third _ => by rw [Finset.sum_mul]

/-- **THE PER-VERTEX SIGN CONSEQUENCE.**  A positive hollow cube diagonal at a
vertex forces a coherent triangle THROUGH THAT VERTEX.

The trace version only promises a coherent triangle somewhere.  This one names
one of its three labels, and that is what pairs with the landed heavy-set
pinning, which says every strict dominator sits inside the heavy set. -/
theorem exists_coherent_triple_through_of_diag_pos (form : Matrix (Fin size) (Fin size) ℝ)
    {vertex : Fin size}
    (hpos : 0 < (hollowPart form * hollowPart form * hollowPart form) vertex vertex) :
    ∃ second third : Fin size, vertex ≠ second ∧ second ≠ third ∧ third ≠ vertex ∧
      0 < form vertex second * form second third * form third vertex := by
  classical
  by_contra hnone
  push Not at hnone
  have hterm : ∀ third second : Fin size,
      hollowPart form vertex second * hollowPart form second third
        * hollowPart form third vertex ≤ 0 := by
    intro third second
    by_cases hone : vertex = second
    · exact le_of_eq (hollowPart_orderedTerm_eq_zero_of_not_distinct form (Or.inl hone))
    by_cases htwo : second = third
    · exact le_of_eq (hollowPart_orderedTerm_eq_zero_of_not_distinct form (Or.inr (Or.inl htwo)))
    by_cases hthree : third = vertex
    · exact le_of_eq
        (hollowPart_orderedTerm_eq_zero_of_not_distinct form (Or.inr (Or.inr hthree)))
    rw [hollowPart_off form hone, hollowPart_off form htwo, hollowPart_off form hthree]
    exact hnone second third hone htwo hthree
  have hsum : (hollowPart form * hollowPart form * hollowPart form) vertex vertex ≤ 0 := by
    rw [hollowPart_cube_diag_eq_orderedSum]
    refine Finset.sum_nonpos fun third _ => ?_
    exact Finset.sum_nonpos fun second _ => hterm third second
  linarith

end VertexSign

section VertexCertificate

variable {size : ℕ}

/-- **THE TWO-LABEL DIAGONAL CERTIFICATE.**  If a vertex leverage lies strictly
inside `(0, 1)` and its sum with a cap on every OTHER leverage stays below one,
then the hollow cube diagonal at that vertex is strictly positive.

The proof prices the weighted row energy by the cap, then consumes the landed row
law.  The residue factors as `t_c (1 - t_c) (1 - t_c - cap)`, and every factor is
strictly positive under the hypotheses.

This reads TWO diagonal numbers.  It reads no pairing, no determinant and no
eigenvalue. -/
theorem hollowPart_cube_diag_pos_of_cap (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymm : formᵀ = form) (hidem : form * form = form) {vertex : Fin size} {cap : ℝ}
    (hlow : 0 < form vertex vertex) (hhigh : form vertex vertex < 1)
    (hcap : ∀ other, other ≠ vertex → form other other ≤ cap)
    (hsum : form vertex vertex + cap < 1) :
    0 < (hollowPart form * hollowPart form * hollowPart form) vertex vertex := by
  classical
  rw [hollowPart_cube_diag_eq form hsymm hidem vertex]
  have hbound : ∑ other ∈ Finset.univ.erase vertex, form other other * form vertex other ^ 2
      ≤ cap * (form vertex vertex - form vertex vertex ^ 2) := by
    have hterm : ∀ other ∈ Finset.univ.erase vertex,
        form other other * form vertex other ^ 2 ≤ cap * form vertex other ^ 2 := by
      intro other hmem
      exact mul_le_mul_of_nonneg_right (hcap other (Finset.ne_of_mem_erase hmem))
        (sq_nonneg _)
    have hstep := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum, sum_erase_sq_row_of_idempotent form hsymm hidem vertex] at hstep
    exact hstep
  have hpositive : 0 < form vertex vertex * (1 - form vertex vertex) ^ 2
      - cap * (form vertex vertex - form vertex vertex ^ 2) := by
    have hfactor : form vertex vertex * (1 - form vertex vertex) ^ 2
        - cap * (form vertex vertex - form vertex vertex ^ 2)
        = form vertex vertex * (1 - form vertex vertex)
          * (1 - form vertex vertex - cap) := by ring
    rw [hfactor]
    have hone : 0 < 1 - form vertex vertex := by linarith
    have htwo : 0 < 1 - form vertex vertex - cap := by linarith
    exact mul_pos (mul_pos hlow hone) htwo
  linarith

/-- **THE EQUAL-SHARE SILENCE, PER VERTEX.**  A leverage profile constant at one
half makes the hollow cube diagonal vanish at every vertex.

The cap certificate above needs `t_c + cap < 1` and reads `1/2 + 1/2 = 1` there,
so it is silent by exactly one unit of slack.  Two other landed certificates go
silent at the same configuration. -/
theorem hollowPart_cube_diag_eq_zero_of_forall_half (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymm : formᵀ = form) (hidem : form * form = form)
    (hhalf : ∀ index, form index index = 1 / 2) (vertex : Fin size) :
    (hollowPart form * hollowPart form * hollowPart form) vertex vertex = 0 := by
  classical
  rw [hollowPart_cube_diag_eq form hsymm hidem vertex, hhalf vertex]
  have hrewrite : ∑ other ∈ Finset.univ.erase vertex,
      form other other * form vertex other ^ 2
      = (1 / 2) * ∑ other ∈ Finset.univ.erase vertex, form vertex other ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun other _ => by rw [hhalf other]
  rw [hrewrite, sum_erase_sq_row_of_idempotent form hsymm hidem vertex, hhalf vertex]
  ring

end VertexCertificate

section VertexDesign

variable {size rank : ℕ}

/-- **THE DESIGN-LEVEL VERTEX CERTIFICATE.**  A design carrying a label whose
leverage plus a cap on every other leverage stays below one hosts a COHERENT
triangle through that label.

Everything on the left of the hypothesis is a diagonal entry of the projection
form, so the certificate reads the leverage profile and nothing else. -/
theorem exists_coherent_triple_through_of_leverage_cap (design : WeightedDesign size rank)
    {vertex : Fin size} {cap : ℝ}
    (hlow : 0 < projectionOfDesign design vertex vertex)
    (hhigh : projectionOfDesign design vertex vertex < 1)
    (hcap : ∀ other, other ≠ vertex → projectionOfDesign design other other ≤ cap)
    (hsum : projectionOfDesign design vertex vertex + cap < 1) :
    ∃ second third : Fin size, vertex ≠ second ∧ second ≠ third ∧ third ≠ vertex ∧
      0 < projectionOfDesign design vertex second * projectionOfDesign design second third
        * projectionOfDesign design third vertex :=
  exists_coherent_triple_through_of_diag_pos (projectionOfDesign design)
    (hollowPart_cube_diag_pos_of_cap (projectionOfDesign design)
      (projectionOfDesign_transpose design) (projectionOfDesign_mul_self design)
      hlow hhigh hcap hsum)

/-- The per-vertex law at a design, in closed form. -/
theorem hollowPart_cube_diag_projection_eq (design : WeightedDesign size rank)
    (vertex : Fin size) :
    (hollowPart (projectionOfDesign design) * hollowPart (projectionOfDesign design)
        * hollowPart (projectionOfDesign design)) vertex vertex
      = projectionOfDesign design vertex vertex
          * (1 - projectionOfDesign design vertex vertex) ^ 2
        - ∑ other ∈ Finset.univ.erase vertex,
            projectionOfDesign design other other
              * projectionOfDesign design vertex other ^ 2 :=
  hollowPart_cube_diag_eq (projectionOfDesign design) (projectionOfDesign_transpose design)
    (projectionOfDesign_mul_self design) vertex

/-- The equal-share silence at a design. -/
theorem hollowPart_cube_diag_projection_eq_zero_of_forall_half
    (design : WeightedDesign size rank)
    (hhalf : ∀ index, projectionOfDesign design index index = 1 / 2) (vertex : Fin size) :
    (hollowPart (projectionOfDesign design) * hollowPart (projectionOfDesign design)
        * hollowPart (projectionOfDesign design)) vertex vertex = 0 :=
  hollowPart_cube_diag_eq_zero_of_forall_half (projectionOfDesign design)
    (projectionOfDesign_transpose design) (projectionOfDesign_mul_self design) hhalf vertex

end VertexDesign

section NonnegTriangle

variable {size : ℕ}

/-- At three or more labels every vertex has two further distinct companions. -/
theorem exists_distinct_pair_ne (hsize : 3 ≤ size) (vertex : Fin size) :
    ∃ second third : Fin size, vertex ≠ second ∧ second ≠ third ∧ third ≠ vertex := by
  classical
  have hcard : 1 < (Finset.univ.erase vertex).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ vertex), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨first, hfirst, second, hsecond, hne⟩ := Finset.one_lt_card.mp hcard
  exact ⟨first, second, (Finset.ne_of_mem_erase hfirst).symm, hne,
    Finset.ne_of_mem_erase hsecond⟩

/-- **THE NON-NEGATIVE TRIANGLE AT A VERTEX.**  A hollow cube diagonal that is
merely NON-NEGATIVE already forces a triangle through the vertex whose three
pairings multiply non-negatively.

Strict positivity is not needed.  This is the form that reaches the equal-share
profile, where the diagonal is exactly zero. -/
theorem exists_nonneg_triple_through_of_diag_nonneg (form : Matrix (Fin size) (Fin size) ℝ)
    (hsize : 3 ≤ size) {vertex : Fin size}
    (hnonneg : 0 ≤ (hollowPart form * hollowPart form * hollowPart form) vertex vertex) :
    ∃ second third : Fin size, vertex ≠ second ∧ second ≠ third ∧ third ≠ vertex ∧
      0 ≤ form vertex second * form second third * form third vertex := by
  classical
  by_contra hnone
  push Not at hnone
  obtain ⟨witnessSecond, witnessThird, hvs, hst, htv⟩ := exists_distinct_pair_ne hsize vertex
  have hterm : ∀ third second : Fin size,
      hollowPart form vertex second * hollowPart form second third
        * hollowPart form third vertex ≤ 0 := by
    intro third second
    by_cases hone : vertex = second
    · exact le_of_eq (hollowPart_orderedTerm_eq_zero_of_not_distinct form (Or.inl hone))
    by_cases htwo : second = third
    · exact le_of_eq (hollowPart_orderedTerm_eq_zero_of_not_distinct form (Or.inr (Or.inl htwo)))
    by_cases hthree : third = vertex
    · exact le_of_eq
        (hollowPart_orderedTerm_eq_zero_of_not_distinct form (Or.inr (Or.inr hthree)))
    rw [hollowPart_off form hone, hollowPart_off form htwo, hollowPart_off form hthree]
    exact (hnone second third hone htwo hthree).le
  have hstrictTerm : hollowPart form vertex witnessSecond
      * hollowPart form witnessSecond witnessThird
      * hollowPart form witnessThird vertex < 0 := by
    rw [hollowPart_off form hvs, hollowPart_off form hst, hollowPart_off form htv]
    exact hnone witnessSecond witnessThird hvs hst htv
  have hinnerStrict : (∑ second, hollowPart form vertex second
      * hollowPart form second witnessThird * hollowPart form witnessThird vertex) < 0 := by
    have hstep := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin size)))
      (f := fun second => hollowPart form vertex second
        * hollowPart form second witnessThird * hollowPart form witnessThird vertex)
      (g := fun _ => (0 : ℝ))
      (fun second _ => hterm witnessThird second)
      ⟨witnessSecond, Finset.mem_univ witnessSecond, hstrictTerm⟩
    simpa using hstep
  have houter : (hollowPart form * hollowPart form * hollowPart form) vertex vertex < 0 := by
    rw [hollowPart_cube_diag_eq_orderedSum]
    have hstep := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin size)))
      (f := fun third => ∑ second, hollowPart form vertex second
        * hollowPart form second third * hollowPart form third vertex)
      (g := fun _ => (0 : ℝ))
      (fun third _ => Finset.sum_nonpos fun second _ => hterm third second)
      ⟨witnessThird, Finset.mem_univ witnessThird, hinnerStrict⟩
    simpa using hstep
  linarith

/-- **THE EQUAL-SHARE RESOLUTION.**  At a leverage profile constant at one half
EVERY vertex hosts a triangle whose three pairings multiply non-negatively.

The per-vertex law makes the diagonal vanish exactly there, and a vanishing
diagonal is non-negative.  So the sign obstruction cannot bite at any vertex of
the equiangular configuration, and the triple product cannot be negative all the
way round. -/
theorem exists_nonneg_triple_through_of_forall_half (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymm : formᵀ = form) (hidem : form * form = form) (hsize : 3 ≤ size)
    (hhalf : ∀ index, form index index = 1 / 2) (vertex : Fin size) :
    ∃ second third : Fin size, vertex ≠ second ∧ second ≠ third ∧ third ≠ vertex ∧
      0 ≤ form vertex second * form second third * form third vertex := by
  refine exists_nonneg_triple_through_of_diag_nonneg form hsize ?_
  rw [hollowPart_cube_diag_eq_zero_of_forall_half form hsymm hidem hhalf vertex]

/-- **THE DIAGONAL-ONLY FORM.**  A non-negative per-vertex law reads only the
leverage of the vertex and the weighted row energy of its row. -/
theorem exists_nonneg_triple_through_of_row_bound (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymm : formᵀ = form) (hidem : form * form = form) (hsize : 3 ≤ size)
    {vertex : Fin size}
    (hrow : ∑ other ∈ Finset.univ.erase vertex, form other other * form vertex other ^ 2
      ≤ form vertex vertex * (1 - form vertex vertex) ^ 2) :
    ∃ second third : Fin size, vertex ≠ second ∧ second ≠ third ∧ third ≠ vertex ∧
      0 ≤ form vertex second * form second third * form third vertex := by
  refine exists_nonneg_triple_through_of_diag_nonneg form hsize ?_
  rw [hollowPart_cube_diag_eq form hsymm hidem vertex]
  linarith

end NonnegTriangle

section NonnegTriangleDesign

variable {size rank : ℕ}

/-- **THE DESIGN-LEVEL EQUAL-SHARE RESOLUTION.**  Every label of a design whose
leverages are all one half hosts a non-negative triangle.

This is the configuration two landed magnitude certificates go silent at, and the
one the campaign names as the crux.  The sign question there is settled: the
twenty triple products cannot all be negative, at any vertex. -/
theorem exists_nonneg_triple_through_of_leverage_half (design : WeightedDesign size rank)
    (hsize : 3 ≤ size)
    (hhalf : ∀ index, projectionOfDesign design index index = 1 / 2) (vertex : Fin size) :
    ∃ second third : Fin size, vertex ≠ second ∧ second ≠ third ∧ third ≠ vertex ∧
      0 ≤ projectionOfDesign design vertex second * projectionOfDesign design second third
        * projectionOfDesign design third vertex :=
  exists_nonneg_triple_through_of_forall_half (projectionOfDesign design)
    (projectionOfDesign_transpose design) (projectionOfDesign_mul_self design) hsize hhalf vertex

/-- The aggregate reading: a non-negative cubic total forces a non-negative
triangle somewhere. -/
theorem exists_nonneg_triple_of_sum_leverageCubic_nonneg (design : WeightedDesign size rank)
    (hsize : 3 ≤ size)
    (hprofile : 0 ≤ ∑ index, leverageCubic (projectionOfDesign design index index)) :
    ∃ first second third : Fin size, first ≠ second ∧ second ≠ third ∧ third ≠ first ∧
      0 ≤ projectionOfDesign design first second * projectionOfDesign design second third
        * projectionOfDesign design third first := by
  classical
  by_contra hnone
  push Not at hnone
  have hneg : (hollowPart (projectionOfDesign design)
      * hollowPart (projectionOfDesign design)
      * hollowPart (projectionOfDesign design)).trace < 0 := by
    obtain ⟨second, third, hvs, hst, htv⟩ :=
      exists_distinct_pair_ne hsize (⟨0, by omega⟩ : Fin size)
    have hterm : ∀ first third second : Fin size,
        hollowPart (projectionOfDesign design) first second
          * hollowPart (projectionOfDesign design) second third
          * hollowPart (projectionOfDesign design) third first ≤ 0 := by
      intro first third second
      by_cases hone : first = second
      · exact le_of_eq (hollowPart_orderedTerm_eq_zero_of_not_distinct _ (Or.inl hone))
      by_cases htwo : second = third
      · exact le_of_eq (hollowPart_orderedTerm_eq_zero_of_not_distinct _ (Or.inr (Or.inl htwo)))
      by_cases hthree : third = first
      · exact le_of_eq (hollowPart_orderedTerm_eq_zero_of_not_distinct _ (Or.inr (Or.inr hthree)))
      rw [hollowPart_off _ hone, hollowPart_off _ htwo, hollowPart_off _ hthree]
      exact (hnone first second third hone htwo hthree).le
    have hstrictTerm : hollowPart (projectionOfDesign design) ⟨0, by omega⟩ second
        * hollowPart (projectionOfDesign design) second third
        * hollowPart (projectionOfDesign design) third ⟨0, by omega⟩ < 0 := by
      rw [hollowPart_off _ hvs, hollowPart_off _ hst, hollowPart_off _ htv]
      exact hnone _ second third hvs hst htv
    rw [trace_hollowPart_cube_eq_orderedSum]
    have hinner : (∑ second', hollowPart (projectionOfDesign design) ⟨0, by omega⟩ second'
        * hollowPart (projectionOfDesign design) second' third
        * hollowPart (projectionOfDesign design) third ⟨0, by omega⟩) < 0 := by
      have hstep := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin size)))
        (f := fun second' => hollowPart (projectionOfDesign design) ⟨0, by omega⟩ second'
          * hollowPart (projectionOfDesign design) second' third
          * hollowPart (projectionOfDesign design) third ⟨0, by omega⟩)
        (g := fun _ => (0 : ℝ))
        (fun second' _ => hterm _ third second')
        ⟨second, Finset.mem_univ second, hstrictTerm⟩
      simpa using hstep
    have houterInner : ∀ first : Fin size,
        (∑ third', ∑ second', hollowPart (projectionOfDesign design) first second'
          * hollowPart (projectionOfDesign design) second' third'
          * hollowPart (projectionOfDesign design) third' first) ≤ 0 := by
      intro first
      exact Finset.sum_nonpos fun third' _ =>
        Finset.sum_nonpos fun second' _ => hterm first third' second'
    have hrowStrict : (∑ third', ∑ second',
        hollowPart (projectionOfDesign design) ⟨0, by omega⟩ second'
          * hollowPart (projectionOfDesign design) second' third'
          * hollowPart (projectionOfDesign design) third' ⟨0, by omega⟩) < 0 := by
      have hstep := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin size)))
        (f := fun third' => ∑ second',
          hollowPart (projectionOfDesign design) ⟨0, by omega⟩ second'
            * hollowPart (projectionOfDesign design) second' third'
            * hollowPart (projectionOfDesign design) third' ⟨0, by omega⟩)
        (g := fun _ => (0 : ℝ))
        (fun third' _ => Finset.sum_nonpos fun second' _ => hterm _ third' second')
        ⟨third, Finset.mem_univ third, hinner⟩
      simpa using hstep
    have hstep := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin size)))
      (f := fun first => ∑ third', ∑ second',
        hollowPart (projectionOfDesign design) first second'
          * hollowPart (projectionOfDesign design) second' third'
          * hollowPart (projectionOfDesign design) third' first)
      (g := fun _ => (0 : ℝ))
      (fun first _ => houterInner first)
      ⟨⟨0, by omega⟩, Finset.mem_univ _, hrowStrict⟩
    simpa using hstep
  rw [trace_hollowPart_projection_eq_sum_leverageCubic design] at hneg
  linarith

end NonnegTriangleDesign

end Gtz
