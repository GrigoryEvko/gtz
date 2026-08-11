/-
# The dual-conic frame, used LINEARLY: the exact information it carries, and the
barrier that follows.

The stress-free `(6,3)` stratum carries a DUAL CONIC FRAME: one symmetric form
`K_x` per atom, pairing to one at its own atom and to zero at every other
(`Gtz.exists_dualConic_of_stressFree`).  The landed laws read one conic at a
time — its trace is its atom's weight, and it pairs with every subset gap to the
indicator minus that weight.  This file reads the SIX JOINTLY, and the answer is
a barrier rather than a tool.

* `trace_gap_linearConicCombination` — EVERY linear functional of the frame,
  applied to a subset gap, is an ADDITIVE (modular) set function: with
  coefficients `a_x` its value at `C` is `∑_{x ∈ C} a_x − ∑_x a_x t_x`.  So the
  entire six-dimensional space of linear conic functionals sees exactly six
  numbers per label and nothing about how the labels interact.  That is the
  shape of a per-label score, which is the shape the campaign's refuted
  selector corpus is made of.
* `trace_gap_sumDualConic` — the coefficient-free specialisation: the SUMMED
  conic returns `card C − 1` at every subset, hence is constant on every
  cardinality and can never distinguish two candidates of the same size.
* `dualConicFrame_coefficient_eq_zero_of_sum_eq_zero` — the frame is linearly
  independent, so the space of such functionals really is six-dimensional and
  the additive law is exhaustive, not a special case.
* `atomPairing_smul_of_atom_smul` — rescaling the atoms rescales the frame.
  The conic's PROJECTIVE class therefore depends only on the atom DIRECTIONS,
  and the weights enter only through the traces.
* `quadrilateralScoreIdentity` and `not_forall_lt_quadrilateralScore` — the
  combinatorial barrier: the four subsets `{0,2,4} {0,3,5} {1,2,5} {1,3,4}` and
  the two subsets `{0,1,2} {3,4,5}` have proportional indicator totals, so no
  additive score puts the first family strictly above the second.  At the tree's
  landed stress-free inhabitant `coordinateDiagonalDesign` the first family is
  exactly the strictly dominating triples and the second is not dominating at
  all, which is `no_linearConicFunctional_separates_coordinateDiagonal`.

The composite statement is the negative verdict of the joint-conic route in its
linear half: at a landed stress-free design, no linear functional of the six
dual conics separates the strictly dominating triples from the rest.
-/

import Gtz.Design.TwoFamilyTightFrame
import Gtz.Design.StressFreeClassSplit
import Gtz.Design.KFourChartClosure
import Gtz.Quantitative.VolumeAverageLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Part 1 — the linear law -/

/-- **EVERY LINEAR FUNCTIONAL OF A DUAL FRAME IS AN ADDITIVE SET FUNCTION.**
For any coefficients `a`, the combination `∑ a_x K_x` pairs with the gap of
`C` to `∑_{x ∈ C} a_x − ∑_x a_x t_x`.  The subset enters only through the sum
of six per-label numbers: no linear reading of the six conics sees any
interaction between labels. -/
theorem trace_gap_linearConicCombination (design : WeightedDesign size rank)
    (conic : Fin size → Matrix (Fin rank) (Fin rank) ℝ)
    (coefficient : Fin size → ℝ)
    (hpairing : ∀ chosen atomIndex : Fin size,
      design.atom atomIndex ⬝ᵥ (conic chosen *ᵥ design.atom atomIndex)
        = if atomIndex = chosen then 1 else 0)
    (selected : Finset (Fin size)) :
    Matrix.trace ((subsetSum design selected - 1)
        * ∑ chosen, coefficient chosen • conic chosen)
      = (∑ chosen ∈ selected, coefficient chosen)
        - ∑ chosen, coefficient chosen * design.weight chosen := by
  have hterm : ∀ chosen : Fin size,
      Matrix.trace ((subsetSum design selected - 1) * (coefficient chosen • conic chosen))
        = coefficient chosen
            * ((if chosen ∈ selected then (1 : ℝ) else 0) - design.weight chosen) := by
    intro chosen
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      trace_gapPairing_of_atomPairing design (hpairing chosen) selected]
  have hindicator :
      (∑ chosen, coefficient chosen * (if chosen ∈ selected then (1 : ℝ) else 0))
        = ∑ chosen ∈ selected, coefficient chosen := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem Finset.univ selected coefficient, Finset.univ_inter]
  calc Matrix.trace ((subsetSum design selected - 1)
          * ∑ chosen, coefficient chosen • conic chosen)
      = ∑ chosen, Matrix.trace ((subsetSum design selected - 1)
          * (coefficient chosen • conic chosen)) := by
        rw [Matrix.mul_sum, Matrix.trace_sum]
    _ = ∑ chosen, (coefficient chosen * (if chosen ∈ selected then (1 : ℝ) else 0)
          - coefficient chosen * design.weight chosen) :=
        Finset.sum_congr rfl fun chosen _ => by rw [hterm chosen, mul_sub]
    _ = (∑ chosen, coefficient chosen * (if chosen ∈ selected then (1 : ℝ) else 0))
          - ∑ chosen, coefficient chosen * design.weight chosen := by
        rw [Finset.sum_sub_distrib]
    _ = (∑ chosen ∈ selected, coefficient chosen)
          - ∑ chosen, coefficient chosen * design.weight chosen := by rw [hindicator]

/-- **THE SUMMED CONIC IS A PROVABLE NON-SELECTOR.**  With every coefficient one
the linear law collapses to `card C − 1`, a function of the CARDINALITY alone.
A single functional taking one value on all twenty triples cannot distinguish
any two of them. -/
theorem trace_gap_sumDualConic (design : WeightedDesign size rank)
    (conic : Fin size → Matrix (Fin rank) (Fin rank) ℝ)
    (hpairing : ∀ chosen atomIndex : Fin size,
      design.atom atomIndex ⬝ᵥ (conic chosen *ᵥ design.atom atomIndex)
        = if atomIndex = chosen then 1 else 0)
    (selected : Finset (Fin size)) :
    Matrix.trace ((subsetSum design selected - 1) * ∑ chosen, conic chosen)
      = (selected.card : ℝ) - 1 := by
  have hone : (∑ chosen, (1 : ℝ) • conic chosen) = ∑ chosen, conic chosen := by
    simp
  have hlaw := trace_gap_linearConicCombination design conic (fun _ => (1 : ℝ))
    hpairing selected
  rw [hone] at hlaw
  rw [hlaw]
  simp [design.weight_sum_one]

/-- Two subsets whose coefficient totals agree are indistinguishable to every
linear functional of the frame at once. -/
theorem trace_gap_linearConicCombination_eq_of_sum_eq (design : WeightedDesign size rank)
    (conic : Fin size → Matrix (Fin rank) (Fin rank) ℝ)
    (coefficient : Fin size → ℝ)
    (hpairing : ∀ chosen atomIndex : Fin size,
      design.atom atomIndex ⬝ᵥ (conic chosen *ᵥ design.atom atomIndex)
        = if atomIndex = chosen then 1 else 0)
    {firstSubset secondSubset : Finset (Fin size)}
    (hsum : (∑ chosen ∈ firstSubset, coefficient chosen)
      = ∑ chosen ∈ secondSubset, coefficient chosen) :
    Matrix.trace ((subsetSum design firstSubset - 1)
        * ∑ chosen, coefficient chosen • conic chosen)
      = Matrix.trace ((subsetSum design secondSubset - 1)
        * ∑ chosen, coefficient chosen • conic chosen) := by
  rw [trace_gap_linearConicCombination design conic coefficient hpairing firstSubset,
    trace_gap_linearConicCombination design conic coefficient hpairing secondSubset, hsum]

/-- **THE FRAME IS LINEARLY INDEPENDENT.**  Pairing a vanishing combination
against the atoms recovers each coefficient, so the space of linear conic
functionals is exactly `size`-dimensional and the additive law above describes
all of it. -/
theorem dualConicFrame_coefficient_eq_zero_of_sum_eq_zero (design : WeightedDesign size rank)
    (conic : Fin size → Matrix (Fin rank) (Fin rank) ℝ)
    (coefficient : Fin size → ℝ)
    (hpairing : ∀ chosen atomIndex : Fin size,
      design.atom atomIndex ⬝ᵥ (conic chosen *ᵥ design.atom atomIndex)
        = if atomIndex = chosen then 1 else 0)
    (hvanishes : (∑ chosen, coefficient chosen • conic chosen) = 0)
    (atomIndex : Fin size) : coefficient atomIndex = 0 := by
  have hzero : design.atom atomIndex
      ⬝ᵥ ((∑ chosen, coefficient chosen • conic chosen) *ᵥ design.atom atomIndex) = 0 := by
    rw [hvanishes]
    simp
  rw [Matrix.sum_mulVec, dotProduct_sum] at hzero
  have hentry : ∀ chosen : Fin size,
      design.atom atomIndex
          ⬝ᵥ ((coefficient chosen • conic chosen) *ᵥ design.atom atomIndex)
        = if atomIndex = chosen then coefficient chosen else 0 := by
    intro chosen
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hpairing chosen atomIndex]
    by_cases hcase : atomIndex = chosen <;> simp [hcase]
  rw [Finset.sum_congr rfl fun chosen _ => hentry chosen] at hzero
  rw [Finset.sum_ite_eq Finset.univ atomIndex coefficient] at hzero
  simpa using hzero

/-- **THE FRAME RESCALES WITH THE ATOMS.**  If every atom is scaled, the dual
frame is the frame of the directions divided by the squared scale — so the
PROJECTIVE class of each dual conic, and therefore its rank, its inertia and
every incidence among the six, depends on the atom DIRECTIONS alone.  The
weights enter only through the traces. -/
theorem atomPairing_smul_of_atom_smul (designOne designTwo : WeightedDesign size rank)
    (scale : Fin size → ℝ) (hatom : ∀ label, designTwo.atom label = scale label • designOne.atom label)
    (conic : Matrix (Fin rank) (Fin rank) ℝ) {chosen : Fin size}
    (hscale : scale chosen ≠ 0)
    (hpairing : ∀ atomIndex : Fin size,
      designOne.atom atomIndex ⬝ᵥ (conic *ᵥ designOne.atom atomIndex)
        = if atomIndex = chosen then 1 else 0)
    (atomIndex : Fin size) :
    designTwo.atom atomIndex ⬝ᵥ (((scale chosen ^ 2)⁻¹ • conic) *ᵥ designTwo.atom atomIndex)
      = if atomIndex = chosen then 1 else 0 := by
  have hrewrite : designTwo.atom atomIndex
      ⬝ᵥ (((scale chosen ^ 2)⁻¹ • conic) *ᵥ designTwo.atom atomIndex)
      = (scale chosen ^ 2)⁻¹ * (scale atomIndex * scale atomIndex)
        * (designOne.atom atomIndex ⬝ᵥ (conic *ᵥ designOne.atom atomIndex)) := by
    rw [hatom atomIndex]
    simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]
    ring
  rw [hrewrite, hpairing atomIndex]
  by_cases hcase : atomIndex = chosen
  · subst hcase
    rw [if_pos rfl, mul_one, pow_two]
    field_simp
  · rw [if_neg hcase, mul_zero]

/-! ## Part 2 — the combinatorial barrier -/

/-- The sum of a three-element literal set. -/
theorem sum_tripleFinset (coefficient : Fin size → ℝ) {first second third : Fin size}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    (∑ label ∈ ({first, second, third} : Finset (Fin size)), coefficient label)
      = coefficient first + coefficient second + coefficient third := by
  rw [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton, add_assoc]

/-- **THE TWO-VERSUS-TWO BALANCE BARRIER, in general form.**  If two subsets and
two other subsets have equal coefficient totals in pairs, no threshold puts the
first pair strictly above and the second pair at or below.  Four of the six
landed stress-free `(6,3)` fixtures carry such a balance between their strictly
dominating triples and the rest, each with a two-versus-two certificate. -/
theorem lt_or_lt_of_scoreBalance (coefficient : Fin size → ℝ) (threshold : ℝ)
    {strictFirst strictSecond otherFirst otherSecond : Finset (Fin size)}
    (hbalance : (∑ label ∈ strictFirst, coefficient label)
        + ∑ label ∈ strictSecond, coefficient label
      = (∑ label ∈ otherFirst, coefficient label)
        + ∑ label ∈ otherSecond, coefficient label)
    (hfirst : threshold < ∑ label ∈ strictFirst, coefficient label)
    (hsecond : threshold < ∑ label ∈ strictSecond, coefficient label) :
    threshold < (∑ label ∈ otherFirst, coefficient label)
      ∨ threshold < ∑ label ∈ otherSecond, coefficient label := by
  by_contra hcontra
  have hleft : ¬ (threshold < ∑ label ∈ otherFirst, coefficient label) :=
    fun hlt => hcontra (Or.inl hlt)
  have hright : ¬ (threshold < ∑ label ∈ otherSecond, coefficient label) :=
    fun hlt => hcontra (Or.inr hlt)
  rw [not_lt] at hleft hright
  linarith

/-- **THE COMPLETE-QUADRILATERAL SCORE IDENTITY.**  The four triples
`{0,2,4} {0,3,5} {1,2,5} {1,3,4}` cover every label exactly twice and the two
triples `{0,1,2} {3,4,5}` cover every label exactly once, so the two families
have proportional indicator totals and every additive score obeys one linear
relation between them. -/
theorem quadrilateralScoreIdentity (coefficient : Fin 6 → ℝ) :
    (∑ label ∈ ({0, 2, 4} : Finset (Fin 6)), coefficient label)
      + (∑ label ∈ ({0, 3, 5} : Finset (Fin 6)), coefficient label)
      + (∑ label ∈ ({1, 2, 5} : Finset (Fin 6)), coefficient label)
      + (∑ label ∈ ({1, 3, 4} : Finset (Fin 6)), coefficient label)
      = 2 * ((∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), coefficient label)
        + ∑ label ∈ ({3, 4, 5} : Finset (Fin 6)), coefficient label) := by
  rw [sum_tripleFinset coefficient (by decide) (by decide) (by decide),
    sum_tripleFinset coefficient (by decide) (by decide) (by decide),
    sum_tripleFinset coefficient (by decide) (by decide) (by decide),
    sum_tripleFinset coefficient (by decide) (by decide) (by decide),
    sum_tripleFinset coefficient (by decide) (by decide) (by decide),
    sum_tripleFinset coefficient (by decide) (by decide) (by decide)]
  ring

/-- **THE BARRIER.**  No additive score puts all four of `{0,2,4} {0,3,5}
`{1,2,5} {1,3,4}` strictly above a threshold that also bounds `{0,1,2}` and
`{3,4,5}`: the identity forces one of the latter two above it as well. -/
theorem not_forall_lt_quadrilateralScore (coefficient : Fin 6 → ℝ) (threshold : ℝ)
    (hfirst : threshold < ∑ label ∈ ({0, 2, 4} : Finset (Fin 6)), coefficient label)
    (hsecond : threshold < ∑ label ∈ ({0, 3, 5} : Finset (Fin 6)), coefficient label)
    (hthird : threshold < ∑ label ∈ ({1, 2, 5} : Finset (Fin 6)), coefficient label)
    (hfourth : threshold < ∑ label ∈ ({1, 3, 4} : Finset (Fin 6)), coefficient label) :
    threshold < (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), coefficient label)
      ∨ threshold < ∑ label ∈ ({3, 4, 5} : Finset (Fin 6)), coefficient label := by
  have hidentity := quadrilateralScoreIdentity coefficient
  by_contra hcontra
  have hleft : ¬ (threshold < ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), coefficient label) :=
    fun hlt => hcontra (Or.inl hlt)
  have hright : ¬ (threshold < ∑ label ∈ ({3, 4, 5} : Finset (Fin 6)), coefficient label) :=
    fun hlt => hcontra (Or.inr hlt)
  rw [not_lt] at hleft hright
  linarith

/-! ## Part 3 — the design facts at the landed stress-free inhabitant -/

/-- Every entry of a triple gap of the coordinate-diagonal witness, in closed
rational form: the irrational scale enters only through its square. -/
theorem coordinateDiagonalDesign_gap_apply {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) (rowIndex columnIndex : Fin 3) :
    (subsetSum coordinateDiagonalDesign {first, second, third} - 1) rowIndex columnIndex
      = 3 / 2 * (diagonalPattern first rowIndex * diagonalPattern first columnIndex
          + diagonalPattern second rowIndex * diagonalPattern second columnIndex
          + diagonalPattern third rowIndex * diagonalPattern third columnIndex)
        - (if rowIndex = columnIndex then 1 else 0) := by
  rw [subsetSum_triple coordinateDiagonalDesign hfirstSecond hfirstThird hsecondThird]
  simp only [Matrix.sub_apply, Matrix.add_apply, coordinateDiagonalDesign_atomMatrix_entry,
    Matrix.one_apply]
  ring

theorem coordinateDiagonalDesign_gap_zeroTwoFour :
    subsetSum coordinateDiagonalDesign {0, 2, 4} - 1
      = !![2, 3 / 2, 3 / 2; 3 / 2, 2, 3 / 2; 3 / 2, 3 / 2, 2] := by
  ext rowIndex columnIndex
  rw [coordinateDiagonalDesign_gap_apply (by decide) (by decide) (by decide)]
  have hfirst : diagonalPattern 0 = ![1, 1, 0] := rfl
  have hsecond : diagonalPattern 2 = ![1, 0, 1] := rfl
  have hthird : diagonalPattern 4 = ![0, 1, 1] := rfl
  rw [hfirst, hsecond, hthird]
  fin_cases rowIndex <;> fin_cases columnIndex <;>
    norm_num [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

theorem coordinateDiagonalDesign_gap_zeroThreeFive :
    subsetSum coordinateDiagonalDesign {0, 3, 5} - 1
      = !![2, 3 / 2, -(3 / 2); 3 / 2, 2, -(3 / 2); -(3 / 2), -(3 / 2), 2] := by
  ext rowIndex columnIndex
  rw [coordinateDiagonalDesign_gap_apply (by decide) (by decide) (by decide)]
  have hfirst : diagonalPattern 0 = ![1, 1, 0] := rfl
  have hsecond : diagonalPattern 3 = ![1, 0, -1] := rfl
  have hthird : diagonalPattern 5 = ![0, 1, -1] := rfl
  rw [hfirst, hsecond, hthird]
  fin_cases rowIndex <;> fin_cases columnIndex <;>
    norm_num [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

theorem coordinateDiagonalDesign_gap_oneTwoFive :
    subsetSum coordinateDiagonalDesign {1, 2, 5} - 1
      = !![2, -(3 / 2), 3 / 2; -(3 / 2), 2, -(3 / 2); 3 / 2, -(3 / 2), 2] := by
  ext rowIndex columnIndex
  rw [coordinateDiagonalDesign_gap_apply (by decide) (by decide) (by decide)]
  have hfirst : diagonalPattern 1 = ![1, -1, 0] := rfl
  have hsecond : diagonalPattern 2 = ![1, 0, 1] := rfl
  have hthird : diagonalPattern 5 = ![0, 1, -1] := rfl
  rw [hfirst, hsecond, hthird]
  fin_cases rowIndex <;> fin_cases columnIndex <;>
    norm_num [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

theorem coordinateDiagonalDesign_gap_oneThreeFour :
    subsetSum coordinateDiagonalDesign {1, 3, 4} - 1
      = !![2, -(3 / 2), -(3 / 2); -(3 / 2), 2, 3 / 2; -(3 / 2), 3 / 2, 2] := by
  ext rowIndex columnIndex
  rw [coordinateDiagonalDesign_gap_apply (by decide) (by decide) (by decide)]
  have hfirst : diagonalPattern 1 = ![1, -1, 0] := rfl
  have hsecond : diagonalPattern 3 = ![1, 0, -1] := rfl
  have hthird : diagonalPattern 4 = ![0, 1, 1] := rfl
  rw [hfirst, hsecond, hthird]
  fin_cases rowIndex <;> fin_cases columnIndex <;>
    norm_num [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

theorem coordinateDiagonalDesign_gap_zeroOneTwo :
    subsetSum coordinateDiagonalDesign {0, 1, 2} - 1
      = !![7 / 2, 0, 3 / 2; 0, 2, 0; 3 / 2, 0, 1 / 2] := by
  ext rowIndex columnIndex
  rw [coordinateDiagonalDesign_gap_apply (by decide) (by decide) (by decide)]
  have hfirst : diagonalPattern 0 = ![1, 1, 0] := rfl
  have hsecond : diagonalPattern 1 = ![1, -1, 0] := rfl
  have hthird : diagonalPattern 2 = ![1, 0, 1] := rfl
  rw [hfirst, hsecond, hthird]
  fin_cases rowIndex <;> fin_cases columnIndex <;>
    norm_num [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

theorem coordinateDiagonalDesign_gap_threeFourFive :
    subsetSum coordinateDiagonalDesign {3, 4, 5} - 1
      = !![1 / 2, 0, -(3 / 2); 0, 2, 0; -(3 / 2), 0, 7 / 2] := by
  ext rowIndex columnIndex
  rw [coordinateDiagonalDesign_gap_apply (by decide) (by decide) (by decide)]
  have hfirst : diagonalPattern 3 = ![1, 0, -1] := rfl
  have hsecond : diagonalPattern 4 = ![0, 1, 1] := rfl
  have hthird : diagonalPattern 5 = ![0, 1, -1] := rfl
  rw [hfirst, hsecond, hthird]
  fin_cases rowIndex <;> fin_cases columnIndex <;>
    norm_num [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- The four complements of the complete quadrilateral's lines are strictly
dominating: leading minors `2`, `7/4`, `5/4` at every one. -/
theorem coordinateDiagonalDesign_posDef_zeroTwoFour :
    (subsetSum coordinateDiagonalDesign {0, 2, 4} - 1).PosDef := by
  rw [coordinateDiagonalDesign_gap_zeroTwoFour]
  exact posDef_of_leadingMinors_fin_three 2 (3 / 2) (3 / 2) 2 (3 / 2) 2
    (by norm_num) (by norm_num) (by norm_num)

theorem coordinateDiagonalDesign_posDef_zeroThreeFive :
    (subsetSum coordinateDiagonalDesign {0, 3, 5} - 1).PosDef := by
  rw [coordinateDiagonalDesign_gap_zeroThreeFive]
  exact posDef_of_leadingMinors_fin_three 2 (3 / 2) (-(3 / 2)) 2 (-(3 / 2)) 2
    (by norm_num) (by norm_num) (by norm_num)

theorem coordinateDiagonalDesign_posDef_oneTwoFive :
    (subsetSum coordinateDiagonalDesign {1, 2, 5} - 1).PosDef := by
  rw [coordinateDiagonalDesign_gap_oneTwoFive]
  exact posDef_of_leadingMinors_fin_three 2 (-(3 / 2)) (3 / 2) 2 (-(3 / 2)) 2
    (by norm_num) (by norm_num) (by norm_num)

theorem coordinateDiagonalDesign_posDef_oneThreeFour :
    (subsetSum coordinateDiagonalDesign {1, 3, 4} - 1).PosDef := by
  rw [coordinateDiagonalDesign_gap_oneThreeFour]
  exact posDef_of_leadingMinors_fin_three 2 (-(3 / 2)) (-(3 / 2)) 2 (3 / 2) 2
    (by norm_num) (by norm_num) (by norm_num)

/-- The two triples the score identity pairs them against are NOT strictly
dominating: the probe `(1,0,-3)` reads `-1` at the first and `(3,0,1)` reads
`-1` at the second. -/
theorem coordinateDiagonalDesign_not_posDef_zeroOneTwo :
    ¬ (subsetSum coordinateDiagonalDesign {0, 1, 2} - 1).PosDef := by
  rw [coordinateDiagonalDesign_gap_zeroOneTwo]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![1, 0, -3] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]

theorem coordinateDiagonalDesign_not_posDef_threeFourFive :
    ¬ (subsetSum coordinateDiagonalDesign {3, 4, 5} - 1).PosDef := by
  rw [coordinateDiagonalDesign_gap_threeFourFive]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![3, 0, 1] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]

/-! ## Part 4 — the composite: the linear half of the joint-conic route is dead -/

/-- **NO LINEAR FUNCTIONAL OF THE SIX DUAL CONICS SEPARATES THE STRICTLY
DOMINATING TRIPLES FROM THE REST, AT THE TREE'S LANDED STRESS-FREE INHABITANT.**

Suppose a dual frame is given, coefficients `a` are chosen, and a threshold is
supposed to detect strict domination through the value of `∑ a_x K_x` on the
gap.  The linear law turns that value into the additive score `∑_{x ∈ C} a_x`
shifted by a constant; the complete-quadrilateral identity then forces one of
`{0,1,2}`, `{3,4,5}` above the threshold as well, and neither is strictly
dominating.  So the detector cannot exist, whatever the frame and whatever the
coefficients. -/
theorem no_linearConicFunctional_separates_coordinateDiagonal
    (conic : Fin 6 → Matrix (Fin 3) (Fin 3) ℝ) (coefficient : Fin 6 → ℝ) (threshold : ℝ)
    (hpairing : ∀ chosen atomIndex : Fin 6,
      coordinateDiagonalDesign.atom atomIndex
          ⬝ᵥ (conic chosen *ᵥ coordinateDiagonalDesign.atom atomIndex)
        = if atomIndex = chosen then 1 else 0)
    (hdetects : ∀ selected : Finset (Fin 6),
      (subsetSum coordinateDiagonalDesign selected - 1).PosDef →
        threshold < Matrix.trace ((subsetSum coordinateDiagonalDesign selected - 1)
          * ∑ chosen, coefficient chosen • conic chosen))
    (hrejects : ∀ selected : Finset (Fin 6),
      ¬ (subsetSum coordinateDiagonalDesign selected - 1).PosDef →
        Matrix.trace ((subsetSum coordinateDiagonalDesign selected - 1)
          * ∑ chosen, coefficient chosen • conic chosen) ≤ threshold) :
    False := by
  set constantShift : ℝ :=
    ∑ chosen, coefficient chosen * coordinateDiagonalDesign.weight chosen with hshift
  have hvalue : ∀ selected : Finset (Fin 6),
      Matrix.trace ((subsetSum coordinateDiagonalDesign selected - 1)
          * ∑ chosen, coefficient chosen • conic chosen)
        = (∑ chosen ∈ selected, coefficient chosen) - constantShift := fun selected =>
    trace_gap_linearConicCombination coordinateDiagonalDesign conic coefficient hpairing selected
  have hstrict : ∀ selected : Finset (Fin 6),
      (subsetSum coordinateDiagonalDesign selected - 1).PosDef →
        threshold + constantShift < ∑ chosen ∈ selected, coefficient chosen := by
    intro selected hposDef
    have := hdetects selected hposDef
    rw [hvalue selected] at this
    linarith
  have hweak : ∀ selected : Finset (Fin 6),
      ¬ (subsetSum coordinateDiagonalDesign selected - 1).PosDef →
        (∑ chosen ∈ selected, coefficient chosen) ≤ threshold + constantShift := by
    intro selected hnot
    have := hrejects selected hnot
    rw [hvalue selected] at this
    linarith
  have hbarrier := not_forall_lt_quadrilateralScore coefficient (threshold + constantShift)
    (hstrict _ coordinateDiagonalDesign_posDef_zeroTwoFour)
    (hstrict _ coordinateDiagonalDesign_posDef_zeroThreeFive)
    (hstrict _ coordinateDiagonalDesign_posDef_oneTwoFive)
    (hstrict _ coordinateDiagonalDesign_posDef_oneThreeFour)
  rcases hbarrier with hleft | hright
  · exact absurd hleft (not_lt.mpr (hweak _ coordinateDiagonalDesign_not_posDef_zeroOneTwo))
  · exact absurd hright (not_lt.mpr (hweak _ coordinateDiagonalDesign_not_posDef_threeFourFive))

end Gtz
