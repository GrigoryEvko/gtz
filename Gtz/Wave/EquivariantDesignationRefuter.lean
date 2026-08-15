/-
# No relabelling-equivariant rule can designate

`Gtz.consolidatedStrictTriple_iff_complementMinors` reduced the whole on-path
registry to one sentence: at every chart point some triple of labels has three
positive complement minors.  What remains is entirely the DESIGNATION -- a rule
naming, at each chart point, a triple that works.

Every rule the campaign has tried reads only label-free data: the largest
conductance, the largest determinant, the leverage edge, the four invariant
argmaxes, the rung argmax and its tie-aware variant, the own monomial.  All are
refuted, one witness at a time.

This file refutes the whole class at once.  A rule is EQUIVARIANT when relabelling
the chart point relabels its answer.  At a chart point carrying a relabelling
symmetry an equivariant rule must return a triple the symmetry fixes, because the
point is its own relabelling.  So a chart point whose symmetry fixes only FAILING
triples defeats every equivariant rule at the same time.

`Gtz.witnessPoint` is such a point.  Its six directions are two orbits of the
cyclic coordinate shift, its weights are constant on each orbit, and the shift
`(0 1 2)(3 4 5)` fixes exactly two of the twenty triples -- the two orbits
themselves.  Both fail.  Six other triples work, in two free orbits of three.

The construction behind the witness is general.  Whitening the full gap sends the
selection gap to `1 - sum of q q^T` over the OMITTED labels, with `q_c` the
whitened boosted direction, and the chart condition becomes `sum d_c q_c q_c^T =
1` with `d_c = 1 - w_c`.  Choosing the `q_c` as two orbits of a rational rotation
makes every entry rational and the symmetry exact.

## What this does not do

It does not refute the designation problem.  A rule reading the label names, or a
rule choosing from a set rather than a point, escapes the argument entirely, and
`Gtz.witnessPoint` carries six working triples.  What it says is that the
symmetry must be broken by something outside the chart data, which is exactly
what every refuted rule failed to do.
-/
import Gtz.Wave.ConsolidatedMinorForm

namespace Gtz

open Finset Matrix

/-! ## 1. The witness

The directions are the orbits of `(x,y,z) -> (z,x,y)` through `(-2,-2,2)` and
`(-2,-1,-1)`.  The masses are the weights scaled by the single constant `9/140`,
which is what makes the full gap the identity.
-/

/-- The six directions: two orbits of the cyclic coordinate shift. -/
noncomputable def witnessDirection : Fin 6 → (Fin 3 → ℝ) :=
  ![![-2, -2, 2], ![2, -2, -2], ![-2, 2, -2],
    ![-2, -1, -1], ![-1, -2, -1], ![-1, -1, -2]]

/-- The weights: constant on each orbit, summing to one. -/
noncomputable def witnessWeight : Fin 6 → ℝ := ![2/27, 2/27, 2/27, 7/27, 7/27, 7/27]

/-- The masses: the weights scaled by `9/140`, so every boost equals `9/140`. -/
noncomputable def witnessMass : Fin 6 → ℝ := ![1/210, 1/210, 1/210, 1/60, 1/60, 1/60]

theorem witnessWeight_pos (label : Fin 6) : 0 < witnessWeight label := by
  fin_cases label <;> simp [witnessWeight]

theorem witnessMass_pos (label : Fin 6) : 0 < witnessMass label := by
  fin_cases label <;> simp [witnessMass]

theorem witnessWeight_sum_one : ∑ label, witnessWeight label = 1 := by
  simp [Fin.sum_univ_six, witnessWeight]; norm_num

/-- **Every boost is the same constant `9/140`.**  This is what pins the full gap
to the identity, and it is why the complement matrix is a scalar multiple of
`1` minus the Gram of the directions. -/
theorem witnessBoost (label : Fin 6) :
    witnessMass label / witnessWeight label = 9 / 140 := by
  fin_cases label <;> simp [witnessMass, witnessWeight] <;> norm_num

theorem witnessBoost_pos (label : Fin 6) :
    0 < witnessMass label / witnessWeight label := by
  rw [witnessBoost]; norm_num

/-- The witness as a chart point. -/
noncomputable def witnessPoint : DirectionChartPoint 6 where
  mass := witnessMass
  weight := witnessWeight
  mass_pos := witnessMass_pos
  weight_pos := witnessWeight_pos
  weight_sum_one := witnessWeight_sum_one

/-! ## 2. The full gap is the identity

The two orbit sums on the integer directions are `16 * 1 - 4 J` and `1 + 5 J`
with `J` the all-ones matrix.  The boost is constant, so the gap is `(9/140)`
times `17 * 1 + J` minus the mass-weighted sum, and the two `J` parts cancel.
-/

/-- **The full-selection gap is the identity matrix.**  Everything downstream
reads off this: the inverse form is the plain dot product of the directions. -/
theorem witnessGapUniv :
    directionChartGap witnessDirection witnessMass witnessWeight Finset.univ = 1 := by
  ext i j
  simp only [directionChartGap, Matrix.sub_apply, atomMatrix, Fin.sum_univ_six]
  fin_cases i <;> fin_cases j <;>
    simp [witnessDirection, witnessMass, witnessWeight] <;> norm_num

/-- The inverse of the full gap is the identity. -/
theorem witnessGapUniv_inv :
    (directionChartGap witnessDirection witnessMass witnessWeight Finset.univ)⁻¹ = 1 := by
  rw [witnessGapUniv, inv_one]

/-- The full gap of the witness is positive definite. -/
theorem witnessGapUniv_posDef :
    (directionChartGap witnessDirection witnessMass witnessWeight Finset.univ).PosDef := by
  rw [witnessGapUniv]; exact Matrix.PosDef.one

/-- **The inverse form is the plain dot product.**  With the gap equal to the
identity there is no inverse left to take. -/
theorem witnessInverseForm (i j : Fin 6) :
    fullInverseForm witnessDirection witnessMass witnessWeight i j
      = witnessDirection i ⬝ᵥ witnessDirection j := by
  rw [fullInverseForm, witnessGapUniv_inv, Matrix.one_mulVec]

/-! ## 3. The complement matrix

`complementMatrixEntry i j = b * delta - b^2 * (n_i dot n_j)` with `b = 9/140`
constant, so the complement matrix is `9/140` times `1` minus the Gram of the
scaled directions.  Every entry is an explicit rational.
-/

/-- The explicit complement matrix of the witness. -/
noncomputable def witnessEntry : Fin 6 → Fin 6 → ℝ :=
  ![![18/1225, 81/4900, 81/4900, -81/4900, -81/4900, 0],
    ![81/4900, 18/1225, 81/4900, 0, -81/4900, -81/4900],
    ![81/4900, 81/4900, 18/1225, -81/4900, 0, -81/4900],
    ![-81/4900, 0, -81/4900, 387/9800, -81/3920, -81/3920],
    ![-81/4900, -81/4900, 0, -81/3920, 387/9800, -81/3920],
    ![0, -81/4900, -81/4900, -81/3920, -81/3920, 387/9800]]

/-- **The complement matrix of the witness, entry by entry.** -/
theorem witnessComplementEntry (i j : Fin 6) :
    complementMatrixEntry witnessDirection witnessMass witnessWeight i j
      = witnessEntry i j := by
  rw [complementMatrixEntry, witnessInverseForm, witnessBoost, witnessBoost]
  fin_cases i <;> fin_cases j <;>
    simp [witnessDirection, witnessEntry, dotProduct, Fin.sum_univ_three] <;> norm_num

/-- **The minor predicate reads positive definiteness of the complement gap.**
The right-hand side depends on the triple as a SET, so the predicate is invariant
under permuting `i`, `j`, `k` even though its statement fixes an order. -/
theorem minors_iff_posDef (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ChartComplementMinors witnessDirection witnessMass witnessWeight i j k
      ↔ (directionChartGap witnessDirection witnessMass witnessWeight
          (Finset.univ \ ({i, j, k} : Finset (Fin 6)))).PosDef :=
  (posDef_compl_triple_iff_chartComplementMinors witnessDirection witnessMass witnessWeight
    hij hik hjk (witnessBoost_pos i) (witnessBoost_pos j) (witnessBoost_pos k)
    witnessGapUniv_posDef).symm

/-! ## 4. The relabelling symmetry

`sigmaLabel` is the three-cycle on each orbit.  It fixes the whole witness: the
weights and masses are constant on orbits, and the complement matrix is invariant
because the directions are permuted by an orthogonal map.
-/

/-- The relabelling `(0 1 2)(3 4 5)`. -/
def sigmaLabel : Fin 6 → Fin 6 := ![1, 2, 0, 4, 5, 3]

/-- **The complement matrix is invariant under the relabelling.**  Thirty-six
entrywise identities, and they are what make the symmetry argument work. -/
theorem witnessEntry_sigma (i j : Fin 6) :
    witnessEntry (sigmaLabel i) (sigmaLabel j) = witnessEntry i j := by
  fin_cases i <;> fin_cases j <;> simp [witnessEntry, sigmaLabel]

/-- **The minor predicate is invariant under the relabelling.**  This is the whole
content of "the witness is its own relabelling". -/
theorem chartComplementMinors_sigma (i j k : Fin 6) :
    ChartComplementMinors witnessDirection witnessMass witnessWeight
        (sigmaLabel i) (sigmaLabel j) (sigmaLabel k)
      ↔ ChartComplementMinors witnessDirection witnessMass witnessWeight i j k := by
  simp only [ChartComplementMinors, complementTripleDeterminant, witnessComplementEntry,
    witnessEntry_sigma]

/-! ## 5. The two invariant triples, and both fail -/

/-- **Only the two orbits are invariant three-element sets.**  Sixty-four subsets,
decided outright. -/
theorem sigmaLabel_invariant_card_three (S : Finset (Fin 6))
    (hcard : S.card = 3) (hinv : S.image sigmaLabel = S) :
    S = {0, 1, 2} ∨ S = {3, 4, 5} := by
  revert hcard hinv; revert S; decide

/-- The first orbit fails: its two-by-two minor is negative. -/
theorem not_minors_zeroOneTwo :
    ¬ ChartComplementMinors witnessDirection witnessMass witnessWeight 0 1 2 := by
  intro h
  have h2 := h.2.1
  simp only [witnessComplementEntry] at h2
  simp [witnessEntry] at h2
  norm_num at h2

/-- The second orbit fails: its determinant is negative. -/
theorem not_minors_threeFourFive :
    ¬ ChartComplementMinors witnessDirection witnessMass witnessWeight 3 4 5 := by
  intro h
  have h3 := h.2.2
  simp only [complementTripleDeterminant, witnessComplementEntry, ternaryDeterminant] at h3
  simp [witnessEntry] at h3
  norm_num at h3

/-- **The witness is not a counterexample.**  The triple `{0,3,5}` has all three
minors positive, so a working triple exists and only the SYMMETRIC ones are
missing. -/
theorem minors_zeroThreeFive :
    ChartComplementMinors witnessDirection witnessMass witnessWeight 0 3 5 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [witnessComplementEntry]; simp [witnessEntry]
  · simp only [witnessComplementEntry]; simp [witnessEntry]; norm_num
  · simp only [complementTripleDeterminant, witnessComplementEntry, ternaryDeterminant]
    simp [witnessEntry]; norm_num

/-! ## 6. The refutation -/

/-- **NO INVARIANT TRIPLE WORKS AT THE WITNESS.**  Every three-element set the
relabelling fixes fails the minor test.  The proof reads the predicate through
positive definiteness of the gap on the COMPLEMENT, which depends on the triple
as a set and not on the order it is listed in. -/
theorem no_working_invariant_triple (S : Finset (Fin 6))
    (hcard : S.card = 3) (hinv : S.image sigmaLabel = S)
    (i j k : Fin 6) (hS : S = {i, j, k}) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ ChartComplementMinors witnessDirection witnessMass witnessWeight i j k := by
  rw [minors_iff_posDef i j k hij hik hjk, ← hS]
  rcases sigmaLabel_invariant_card_three S hcard hinv with h | h <;> rw [h]
  · have hfail := not_minors_zeroOneTwo
    rwa [minors_iff_posDef 0 1 2 (by decide) (by decide) (by decide)] at hfail
  · have hfail := not_minors_threeFourFive
    rwa [minors_iff_posDef 3 4 5 (by decide) (by decide) (by decide)] at hfail

/-- **NO EQUIVARIANT RULE DESIGNATES.**  A rule that commutes with relabelling
returns, at the witness, a set the relabelling fixes -- because the witness is
its own relabelling -- and every such set of three labels fails.

The hypothesis `hfixed` is exactly equivariance evaluated at the witness: the
rule's answer is carried to itself by the symmetry.  Every label-free rule the
campaign has refuted satisfies it. -/
theorem no_equivariant_designation
    (rule : (Fin 6 → (Fin 3 → ℝ)) → (Fin 6 → ℝ) → (Fin 6 → ℝ) → Finset (Fin 6))
    (hcard : (rule witnessDirection witnessMass witnessWeight).card = 3)
    (hfixed : (rule witnessDirection witnessMass witnessWeight).image sigmaLabel
      = rule witnessDirection witnessMass witnessWeight)
    (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hS : rule witnessDirection witnessMass witnessWeight = {i, j, k}) :
    ¬ ChartComplementMinors witnessDirection witnessMass witnessWeight i j k :=
  no_working_invariant_triple _ hcard hfixed i j k hS hij hik hjk

/-- **The witness carries a working selection.**  Some card-three selection is
strictly positive definite, so the consolidated statement holds at the witness
and what fails is only the equivariant DESIGNATION. -/
theorem witness_hasWorkingSelection :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap witnessDirection witnessMass witnessWeight selected).PosDef := by
  refine ⟨Finset.univ \ ({0, 3, 5} : Finset (Fin 6)), by decide, ?_⟩
  exact (minors_iff_posDef 0 3 5 (by decide) (by decide) (by decide)).mp minors_zeroThreeFive

end Gtz
