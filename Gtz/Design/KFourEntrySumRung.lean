/-
# The entry-sum rung of the K4 chart gap

`Gtz.posDef_iff_invariantTriple` decides a symmetric `3x3` matrix by the three
invariant pencil coefficients `D1`, `D2`, `D3`.  The third is the determinant,
and every determinant-driven selection the campaign has tried reads `D3` alone.
This module evaluates the FIRST coefficient in closed form on the K4 chart.

The reading is uniform.  `Gtz.invariantOne` is the sum of the six entries of a
symmetric `3x3`, it is linear, and every one of the six `Gtz.kFourDirection`
atom matrices has entry sum exactly `1` -- the three triangle directions and the
three star directions alike.  So the first coefficient of a tree gap is

    D1 = (sum over the tree of mass / weight) - (total mass),

one inequality of the SAME shape at every one of the sixteen spanning trees.

This is NOT the trace.  `Gtz.kFourTrace_eq_explicit` carries the squared lengths
`(2,2,2,1,1,1)`, because the trace weights a triangle direction twice and a star
direction once.  The entry sum does not: the grounding cancels in it.  A tree
that fails the trace rung and a tree that fails the entry-sum rung need not be
the same tree, and the entry-sum rung is the one the pencil actually uses.

The consequence is a matroid statement.  `D1` is a modular set function of the
tree, so the tree maximizing `D1` is the maximum-weight spanning tree for the
edge weights `mass / weight`, and a greedy pass decides whether ANY tree clears
the rung.
-/
import Mathlib
import Gtz.Design.KFourTreeInvariantGoals

namespace Gtz

open Matrix

/-! ## `invariantOne` is linear -/

theorem invariantOne_add (matA matB : Matrix (Fin 3) (Fin 3) ℝ) :
    invariantOne (matA + matB) = invariantOne matA + invariantOne matB := by
  simp only [invariantOne, Matrix.add_apply]
  ring

theorem invariantOne_sub (matA matB : Matrix (Fin 3) (Fin 3) ℝ) :
    invariantOne (matA - matB) = invariantOne matA - invariantOne matB := by
  simp only [invariantOne, Matrix.sub_apply]
  ring

theorem invariantOne_smul (scale : ℝ) (mat : Matrix (Fin 3) (Fin 3) ℝ) :
    invariantOne (scale • mat) = scale * invariantOne mat := by
  simp only [invariantOne, Matrix.smul_apply, smul_eq_mul]
  ring

theorem invariantOne_zero : invariantOne (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  simp [invariantOne]

theorem invariantOne_sum {index : Type*} (support : Finset index)
    (family : index → Matrix (Fin 3) (Fin 3) ℝ) :
    invariantOne (∑ item ∈ support, family item)
      = ∑ item ∈ support, invariantOne (family item) := by
  classical
  induction support using Finset.induction_on with
  | empty => simp [invariantOne_zero]
  | insert item rest hnotMem hstep =>
      rw [Finset.sum_insert hnotMem, Finset.sum_insert hnotMem, invariantOne_add, hstep]

/-! ## The entry sum of an atom matrix -/

/-- The entry sum of a rank-one atom is the square of the coordinate sum, plus
the squared length, halved.  Both summands are nonnegative, so an atom matrix
never has negative entry sum. -/
theorem invariantOne_atomMatrix (vec : Fin 3 → ℝ) :
    invariantOne (atomMatrix vec)
      = vec 0 ^ 2 + vec 1 ^ 2 + vec 2 ^ 2
        + vec 0 * vec 1 + vec 0 * vec 2 + vec 1 * vec 2 := by
  simp only [invariantOne, atomMatrix, Matrix.vecMulVec_apply]
  ring

theorem two_mul_invariantOne_atomMatrix (vec : Fin 3 → ℝ) :
    2 * invariantOne (atomMatrix vec)
      = (vec 0 + vec 1 + vec 2) ^ 2 + (vec 0 ^ 2 + vec 1 ^ 2 + vec 2 ^ 2) := by
  rw [invariantOne_atomMatrix]; ring

theorem invariantOne_atomMatrix_nonneg (vec : Fin 3 → ℝ) :
    0 ≤ invariantOne (atomMatrix vec) := by
  nlinarith [two_mul_invariantOne_atomMatrix vec, sq_nonneg (vec 0 + vec 1 + vec 2),
    sq_nonneg (vec 0), sq_nonneg (vec 1), sq_nonneg (vec 2)]

/-! ## Every K4 atom contributes exactly one -/

/-- **The uniformity.**  All six `kFourDirection` atoms have entry sum `1`.  The
three triangle directions have coordinate sum `0` and squared length `2`, the
three star directions have coordinate sum `1` and squared length `1`, and the
halved-square reading sends both to `1`. -/
theorem kFourDirection_invariantOne (label : Fin 6) :
    invariantOne (atomMatrix (kFourDirection label)) = 1 := by
  fin_cases label <;> simp [invariantOne_atomMatrix, kFourDirection]

/-! ## The closed form -/

/-- **The chart law, at every direction family and every size.**  The first
invariant coefficient of a chart gap prices each label by the entry sum of its
own atom matrix.  No pattern hypothesis, no rank-three content, no K4. -/
theorem invariantOne_directionChartGap {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (tree : Finset (Fin size)) :
    invariantOne (directionChartGap direction mass weight tree)
      = (∑ label ∈ tree, mass label / weight label
            * invariantOne (atomMatrix (direction label)))
        - ∑ label, mass label * invariantOne (atomMatrix (direction label)) := by
  rw [directionChartGap, invariantOne_sub, invariantOne_sum, invariantOne_sum]
  simp only [invariantOne_smul]

/-- **The entry-sum rung.**  The first invariant coefficient of a K4 chart tree
gap is the tree's mass-to-weight sum minus the total mass.  The shape does not
depend on the tree, because every K4 atom prices at `1`. -/
theorem kFourInvariantOne_eq (mass weight : Fin 6 → ℝ) (tree : Finset (Fin 6)) :
    invariantOne (directionChartGap kFourDirection mass weight tree)
      = (∑ label ∈ tree, mass label / weight label) - ∑ label, mass label := by
  rw [invariantOne_directionChartGap]
  simp only [kFourDirection_invariantOne, mul_one]

theorem kFourTreeInvariantOne_eq (point : DirectionChartPoint 6) (tree : Finset (Fin 6)) :
    kFourTreeInvariantOne point tree
      = (∑ label ∈ tree, point.mass label / point.weight label) - ∑ label, point.mass label :=
  kFourInvariantOne_eq point.mass point.weight tree

/-- The mass-to-weight sum of a selection: the modular set function whose
greedy maximum decides the rung. -/
noncomputable def kFourRatioSum (point : DirectionChartPoint 6) (tree : Finset (Fin 6)) : ℝ :=
  ∑ label ∈ tree, point.mass label / point.weight label

/-- The total mass of a chart point: the rung's threshold, independent of the
selection. -/
noncomputable def kFourTotalMass (point : DirectionChartPoint 6) : ℝ :=
  ∑ label, point.mass label

theorem kFourTreeInvariantOne_eq_ratioSum (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) :
    kFourTreeInvariantOne point tree = kFourRatioSum point tree - kFourTotalMass point :=
  kFourTreeInvariantOne_eq point tree

/-- **The rung as an inequality.**  One threshold, one modular function, every
tree. -/
theorem kFourTreeInvariantOne_pos_iff (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) :
    0 < kFourTreeInvariantOne point tree ↔ kFourTotalMass point < kFourRatioSum point tree := by
  rw [kFourTreeInvariantOne_eq_ratioSum, sub_pos]

/-! ## The rung is necessary -/

/-- **Necessity.**  A positive definite tree gap clears the entry-sum rung. -/
theorem kFourRatioSum_gt_of_posDef (point : DirectionChartPoint 6) (tree : Finset (Fin 6))
    (hposDef : (directionChartGap kFourDirection point.mass point.weight tree).PosDef) :
    kFourTotalMass point < kFourRatioSum point tree := by
  have htriple := (kFourTree_posDef_iff_invariant point tree).mp hposDef
  exact (kFourTreeInvariantOne_pos_iff point tree).mp htriple.1

/-- **The kill.**  A tree whose mass-to-weight sum does not exceed the total mass
is not positive definite, whatever its determinant is. -/
theorem kFourTree_not_posDef_of_ratioSum_le (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (hle : kFourRatioSum point tree ≤ kFourTotalMass point) :
    ¬ (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  intro hposDef
  exact absurd (kFourRatioSum_gt_of_posDef point tree hposDef) (not_lt.mpr hle)

/-! ## The greedy consequence -/

/-- **Monotone in the modular function.**  Between two selections the rung is
decided by the mass-to-weight sums alone. -/
theorem kFourTreeInvariantOne_le_iff (point : DirectionChartPoint 6)
    (treeA treeB : Finset (Fin 6)) :
    kFourTreeInvariantOne point treeA ≤ kFourTreeInvariantOne point treeB
      ↔ kFourRatioSum point treeA ≤ kFourRatioSum point treeB := by
  rw [kFourTreeInvariantOne_eq_ratioSum, kFourTreeInvariantOne_eq_ratioSum,
    sub_le_sub_iff_right]

/-- **The maximum decides the family.**  If the selection of largest
mass-to-weight sum in a family fails the rung, then no selection of that family
is positive definite.  One greedy pass settles a whole family. -/
theorem kFourFamily_no_posDef_of_max_ratioSum_le (point : DirectionChartPoint 6)
    (family : Finset (Finset (Fin 6))) (best : Finset (Fin 6))
    (hmax : ∀ tree ∈ family, kFourRatioSum point tree ≤ kFourRatioSum point best)
    (hfail : kFourRatioSum point best ≤ kFourTotalMass point) :
    ∀ tree ∈ family, ¬ (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  intro tree hmem
  exact kFourTree_not_posDef_of_ratioSum_le point tree
    ((hmax tree hmem).trans hfail)

/-- **The leaf needs the rung.**  If some selection of a family is positive
definite then the family's largest mass-to-weight sum exceeds the total mass. -/
theorem kFourFamily_max_ratioSum_gt_of_exists_posDef (point : DirectionChartPoint 6)
    (family : Finset (Finset (Fin 6))) (best : Finset (Fin 6))
    (hmax : ∀ tree ∈ family, kFourRatioSum point tree ≤ kFourRatioSum point best)
    (tree : Finset (Fin 6)) (hmem : tree ∈ family)
    (hposDef : (directionChartGap kFourDirection point.mass point.weight tree).PosDef) :
    kFourTotalMass point < kFourRatioSum point best :=
  lt_of_lt_of_le (kFourRatioSum_gt_of_posDef point tree hposDef) (hmax tree hmem)

/-! ## The selection vector and the explicit K4 dictionary

The chart gap is a single combination of the six atom matrices, with the
selected labels priced at `mass / weight - mass` and the omitted ones at
`- mass`.  Writing that combination out at `kFourDirection` gives the reduced K4
Laplacian shape: each diagonal entry is the sum over one vertex star, and each
off-diagonal entry is minus one triangle label. -/

/-- The selection value of a label: its boost on the tree, minus its mass off
the tree. -/
noncomputable def selectionValue {size : ℕ} (mass weight : Fin size → ℝ)
    (tree : Finset (Fin size)) (label : Fin size) : ℝ :=
  if label ∈ tree then mass label / weight label - mass label else - mass label

/-- **The gap is one combination of the atoms.**  Generic in the size and the
direction family. -/
theorem directionChartGap_entry_selection {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (tree : Finset (Fin size)) (rowIndex colIndex : Fin 3) :
    directionChartGap direction mass weight tree rowIndex colIndex
      = ∑ label, selectionValue mass weight tree label
          * direction label rowIndex * direction label colIndex := by
  classical
  rw [directionChartGap_entry]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun label => label ∈ tree)
    (fun label => selectionValue mass weight tree label
      * direction label rowIndex * direction label colIndex)]
  have hleft : (Finset.univ.filter (fun label => label ∈ tree)) = tree := by
    ext label; simp
  have hsub : ∀ label ∈ tree, selectionValue mass weight tree label
      * direction label rowIndex * direction label colIndex
      = mass label / weight label * direction label rowIndex * direction label colIndex
        - mass label * direction label rowIndex * direction label colIndex := by
    intro label hmem
    simp only [selectionValue, if_pos hmem]
    ring
  have hout : ∀ label ∈ (Finset.univ.filter (fun label => ¬ label ∈ tree)),
      selectionValue mass weight tree label
        * direction label rowIndex * direction label colIndex
      = - (mass label * direction label rowIndex * direction label colIndex) := by
    intro label hmem
    simp only [Finset.mem_filter] at hmem
    simp only [selectionValue, if_neg hmem.2]
    ring
  rw [hleft, Finset.sum_congr rfl hsub, Finset.sum_congr rfl hout, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  have hsplit : ∑ label, mass label * direction label rowIndex * direction label colIndex
      = (∑ label ∈ tree, mass label * direction label rowIndex * direction label colIndex)
        + ∑ label ∈ (Finset.univ.filter (fun label => ¬ label ∈ tree)),
            mass label * direction label rowIndex * direction label colIndex := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun label => label ∈ tree)
      (fun label => mass label * direction label rowIndex * direction label colIndex), hleft]
  rw [hsplit]
  ring

/-- The first diagonal entry collects the star of the first vertex: labels
`0`, `1` and `3`. -/
theorem kFourGap_zero_zero (mass weight : Fin 6 → ℝ) (tree : Finset (Fin 6)) :
    directionChartGap kFourDirection mass weight tree 0 0
      = selectionValue mass weight tree 0 + selectionValue mass weight tree 1
        + selectionValue mass weight tree 3 := by
  rw [directionChartGap_entry_selection]
  simp [Fin.sum_univ_six, kFourDirection]

theorem kFourGap_one_one (mass weight : Fin 6 → ℝ) (tree : Finset (Fin 6)) :
    directionChartGap kFourDirection mass weight tree 1 1
      = selectionValue mass weight tree 0 + selectionValue mass weight tree 2
        + selectionValue mass weight tree 4 := by
  rw [directionChartGap_entry_selection]
  simp [Fin.sum_univ_six, kFourDirection]

theorem kFourGap_two_two (mass weight : Fin 6 → ℝ) (tree : Finset (Fin 6)) :
    directionChartGap kFourDirection mass weight tree 2 2
      = selectionValue mass weight tree 1 + selectionValue mass weight tree 2
        + selectionValue mass weight tree 5 := by
  rw [directionChartGap_entry_selection]
  simp [Fin.sum_univ_six, kFourDirection]

/-- Each off-diagonal entry is minus a single triangle label. -/
theorem kFourGap_zero_one (mass weight : Fin 6 → ℝ) (tree : Finset (Fin 6)) :
    directionChartGap kFourDirection mass weight tree 0 1
      = - selectionValue mass weight tree 0 := by
  rw [directionChartGap_entry_selection]
  simp [Fin.sum_univ_six, kFourDirection]

theorem kFourGap_zero_two (mass weight : Fin 6 → ℝ) (tree : Finset (Fin 6)) :
    directionChartGap kFourDirection mass weight tree 0 2
      = - selectionValue mass weight tree 1 := by
  rw [directionChartGap_entry_selection]
  simp [Fin.sum_univ_six, kFourDirection]

theorem kFourGap_one_two (mass weight : Fin 6 → ℝ) (tree : Finset (Fin 6)) :
    directionChartGap kFourDirection mass weight tree 1 2
      = - selectionValue mass weight tree 2 := by
  rw [directionChartGap_entry_selection]
  simp [Fin.sum_univ_six, kFourDirection]

/-- **The entry-sum rung read off the dictionary.**  The three star sums add
every label once, the three off-diagonal entries subtract the triangle labels
once, and what survives is the plain sum of the six selection values. -/
theorem kFourInvariantOne_eq_sum_selectionValue (mass weight : Fin 6 → ℝ)
    (tree : Finset (Fin 6)) :
    invariantOne (directionChartGap kFourDirection mass weight tree)
      = ∑ label, selectionValue mass weight tree label := by
  simp only [invariantOne, kFourGap_zero_zero, kFourGap_one_one, kFourGap_two_two,
    kFourGap_zero_one, kFourGap_zero_two, kFourGap_one_two, Fin.sum_univ_six]
  ring

/-! ## The rung transports to every uniform chart family

Nothing above about the rung is K4 content except one fact: the six atom entry
sums are equal.  Any direction family whose atoms share an entry sum carries the
same rung, with the shared value as an overall factor.  The rung is therefore a
property of the chart construction and not of the K4 pattern. -/

/-- **The uniform rung, at every size and every direction family.**  If all the
atom entry sums agree, the first invariant coefficient is that shared value
times the mass-to-weight surplus of the selection. -/
theorem invariantOne_directionChartGap_of_uniform {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (tree : Finset (Fin size)) (unit : ℝ)
    (huniform : ∀ label, invariantOne (atomMatrix (direction label)) = unit) :
    invariantOne (directionChartGap direction mass weight tree)
      = unit * ((∑ label ∈ tree, mass label / weight label) - ∑ label, mass label) := by
  rw [invariantOne_directionChartGap]
  simp only [huniform]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- At a uniform family with positive shared entry sum, the rung is exactly the
mass-to-weight surplus, with the shared value scaled away. -/
theorem invariantOne_pos_iff_of_uniform {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (tree : Finset (Fin size)) (unit : ℝ) (hunit : 0 < unit)
    (huniform : ∀ label, invariantOne (atomMatrix (direction label)) = unit) :
    0 < invariantOne (directionChartGap direction mass weight tree)
      ↔ (∑ label, mass label) < ∑ label ∈ tree, mass label / weight label := by
  rw [invariantOne_directionChartGap_of_uniform direction mass weight tree unit huniform,
    mul_pos_iff_of_pos_left hunit, sub_pos]

/-- The K4 family is uniform with shared entry sum one. -/
theorem kFourDirection_uniform :
    ∀ label : Fin 6, invariantOne (atomMatrix (kFourDirection label)) = 1 :=
  kFourDirection_invariantOne

/-! ## The sign law of the selection vector

At a genuine chart point every weight lies strictly between zero and one, so the
selection value is positive exactly on the selected labels and negative off
them.  The sign pattern of the six values is therefore the tree itself, and the
spanning-tree polynomial below has exactly one monomial -- the selected tree's
own -- whose three factors are all positive. -/

/-- On the tree the selection value is the strictly positive boost
`mass * (1 - weight) / weight`. -/
theorem selectionValue_pos_of_mem (point : DirectionChartPoint 6) (tree : Finset (Fin 6))
    (label : Fin 6) (hmem : label ∈ tree) :
    0 < selectionValue point.mass point.weight tree label := by
  simp only [selectionValue, if_pos hmem]
  have hweight := point.weight_pos label
  have hmass := point.mass_pos label
  have hlt := chartPoint_weight_lt_one point label
  have hkey : point.mass label < point.mass label / point.weight label := by
    rw [lt_div_iff₀ hweight]
    nlinarith
  linarith

/-- Off the tree the selection value is minus the mass, strictly negative. -/
theorem selectionValue_neg_of_not_mem (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (label : Fin 6) (hnot : label ∉ tree) :
    selectionValue point.mass point.weight tree label < 0 := by
  simp only [selectionValue, if_neg hnot]
  exact neg_neg_iff_pos.mpr (point.mass_pos label)

/-- **The sign pattern is the tree.**  A label carries positive selection value
exactly when the tree selects it. -/
theorem selectionValue_pos_iff_mem (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (label : Fin 6) :
    0 < selectionValue point.mass point.weight tree label ↔ label ∈ tree := by
  classical
  constructor
  · intro hpos
    by_contra hnot
    exact absurd hpos (not_lt.mpr (selectionValue_neg_of_not_mem point tree label hnot).le)
  · exact selectionValue_pos_of_mem point tree label

/-! ## The other two coefficients, in closed form

With the dictionary the remaining two invariant coefficients are polynomials in
the six selection values, and both carry K4 combinatorics on the nose.

The second coefficient prices a pair of labels by whether the two K4 edges meet.
The three OPPOSITE pairs -- `{0,5}`, `{1,4}`, `{2,3}`, the three perfect
matchings of K4 -- carry weight `4`, and the twelve ADJACENT pairs carry
weight `3`.

The third coefficient is the determinant, and it is the spanning-tree polynomial
of K4: one monomial for each of the sixteen spanning trees, and no monomial for
any of the four triangles.  That is the Matrix-Tree theorem for this chart, and
it is why a dependent triple can never be positive definite -- its monomial is
simply absent. -/

/-- The three perfect matchings of K4 pair the labels `{0,5}`, `{1,4}`, `{2,3}`:
each pair is two disjoint edges. -/
noncomputable def kFourPairForm (value : Fin 6 → ℝ) : ℝ :=
  4 * (value 0 * value 5 + value 1 * value 4 + value 2 * value 3)
    + 3 * (value 0 * value 1 + value 0 * value 2 + value 0 * value 3 + value 0 * value 4
        + value 1 * value 2 + value 1 * value 3 + value 1 * value 5
        + value 2 * value 4 + value 2 * value 5
        + value 3 * value 4 + value 3 * value 5 + value 4 * value 5)

/-- The spanning-tree polynomial of K4: one monomial for each of the sixteen
spanning trees.  The four triangles `{0,1,2}`, `{0,3,4}`, `{1,3,5}`, `{2,4,5}`
contribute nothing. -/
noncomputable def kFourTreePolynomial (value : Fin 6 → ℝ) : ℝ :=
  value 0 * value 1 * value 3 + value 0 * value 1 * value 4 + value 0 * value 1 * value 5
    + value 0 * value 2 * value 3 + value 0 * value 2 * value 4 + value 0 * value 2 * value 5
    + value 0 * value 3 * value 5 + value 0 * value 4 * value 5
    + value 1 * value 2 * value 3 + value 1 * value 2 * value 4 + value 1 * value 2 * value 5
    + value 1 * value 3 * value 4 + value 1 * value 4 * value 5
    + value 2 * value 3 * value 4 + value 2 * value 3 * value 5
    + value 3 * value 4 * value 5

/-- **The second coefficient reads the K4 edge-pair structure.** -/
theorem kFourInvariantTwo_eq (mass weight : Fin 6 → ℝ) (tree : Finset (Fin 6)) :
    invariantTwo (directionChartGap kFourDirection mass weight tree)
      = kFourPairForm (selectionValue mass weight tree) := by
  simp only [invariantTwo, kFourGap_zero_zero, kFourGap_one_one, kFourGap_two_two,
    kFourGap_zero_one, kFourGap_zero_two, kFourGap_one_two, kFourPairForm]
  ring

/-- **The Matrix-Tree theorem for the K4 chart.**  The determinant of the gap is
the spanning-tree polynomial of the selection values. -/
theorem kFourInvariantThree_eq (mass weight : Fin 6 → ℝ) (tree : Finset (Fin 6)) :
    invariantThree (directionChartGap kFourDirection mass weight tree)
      = kFourTreePolynomial (selectionValue mass weight tree) := by
  simp only [invariantThree, kFourGap_zero_zero, kFourGap_one_one, kFourGap_two_two,
    kFourGap_zero_one, kFourGap_zero_two, kFourGap_one_two, kFourTreePolynomial]
  ring

/-- **A3's leaf with no matrices.**  A K4 chart tree gap is positive definite
exactly when three explicit polynomials in the six selection values are
positive: their plain sum, the edge-pair form, and the spanning-tree
polynomial. -/
theorem kFourTree_posDef_iff_polynomial (mass weight : Fin 6 → ℝ) (tree : Finset (Fin 6)) :
    (directionChartGap kFourDirection mass weight tree).PosDef
      ↔ 0 < ∑ label, selectionValue mass weight tree label
        ∧ 0 < kFourPairForm (selectionValue mass weight tree)
        ∧ 0 < kFourTreePolynomial (selectionValue mass weight tree) := by
  rw [posDef_iff_invariantTriple (directionChartGap_transpose kFourDirection mass weight tree),
    kFourInvariantOne_eq_sum_selectionValue, kFourInvariantTwo_eq, kFourInvariantThree_eq]

/-! ## Why determinant selection fails at the heavy-pair witness

`Gtz.heavyPairRefuterPoint` is one of the campaign's mandatory test points.  The
tree of largest determinant there is `{1,2,5}`, and that tree is not positive
definite.  The reason is the entry-sum rung and nothing else: the three labels
`1`, `2`, `5` carry mass and weight both equal to `1/60`, so each prices at
exactly `1` and the whole tree reaches `3`, while the total mass is `1481/20`.

A determinant-driven selection cannot see this, because the determinant is the
THIRD invariant coefficient.  The rung below is the first. -/

theorem heavyPairRefuter_totalMass : kFourTotalMass heavyPairRefuterPoint = 1481 / 20 := by
  simp only [kFourTotalMass, Fin.sum_univ_six, heavyPairRefuterPoint]
  norm_num [heavyPairRefuterMass]

theorem heavyPairRefuter_ratioSum_detArgmax :
    kFourRatioSum heavyPairRefuterPoint {1, 2, 5} = 3 := by
  simp only [kFourRatioSum, heavyPairRefuterPoint]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [heavyPairRefuterMass, maxEdgeRefuterWeight]

/-- **The determinant-argmax tree at the heavy-pair witness fails the first
rung.**  Its mass-to-weight sum is `3`, far below the total mass `1481/20`. -/
theorem heavyPairRefuter_detArgmax_not_posDef :
    ¬ (directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {1, 2, 5}).PosDef := by
  refine kFourTree_not_posDef_of_ratioSum_le heavyPairRefuterPoint {1, 2, 5} ?_
  rw [heavyPairRefuter_ratioSum_detArgmax, heavyPairRefuter_totalMass]
  norm_num

end Gtz
