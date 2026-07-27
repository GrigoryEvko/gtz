/-
# The TWO-BLOCK branch of the chart stationarity system

A companion to `Gtz.Quantitative.ChartStationary`, closing one branch of the case
analysis that file leaves open: the branch where the active family of a chart
stationarity datum consists of exactly TWO complementary subsets, `C` and its
complement.

**IT DOES NOT CLOSE THE PAPER'S PARTITION BOX, and must not be cited as if it
did.**  The paper's third-elementary-symmetric-function corollary leaves a
partition branch open on the DESIGN side, and the two branches are about different
systems.  The chart argument below turns on the multipliers of the two blocks being
forced EQUAL by the constant diagonal; on the design side the corresponding
multipliers are the two BLOCK WEIGHTS, which are not equal in general — that is
precisely the step that makes the chart argument work and the design argument not.
Nothing here transfers across that gap, and nothing here should be read as
transferring.

## What is proved

Let `IsChartStationaryData rank projection weight value ...` hold and let every
active subset be either `chosenSubset` or `chosenSubsetᶜ`.  If the weights inside
`chosenSubset` are pairwise distinct AND the weights inside `chosenSubsetᶜ` are
pairwise distinct, then

    `value = (rank - 1) / size`,   and with both blocks of card `rank`,
    `value = (rank - 1) / (2 * rank) ≥ 0` .

So NO two-block datum with pairwise distinct weights inside each block carries a
negative value — `zero_le_value_of_isChartTwoBlockFamily`.  Since a counterexample
to the conjecture would have to sit at a NEGATIVE value, that branch of the search
is eliminated, under the distinctness side condition and no other.

## The route, and where it departs from the sketch it was built from

The campaign brief routes the argument through subspaces: `Xi` is block diagonal,
so commutation with the chart localises to `[P[C], Theta_C] = 0`; hence `P[C]`
preserves `range Theta_C`, on which tightness makes it act as `D[C] + value`; hence
that range is `D[C]`-invariant and has full coordinate support; hence, with the
weights in `C` pairwise distinct, it is everything.

Everything below happens one level lower, at the level of matrix ENTRIES, and the
subspaces never appear.  The reason is not economy but honesty about what the
hypothesis actually supplies: what is in hand is a COMMUTING MATRIX, not an
invariant subspace, and the passage from the first to the second is exactly the
step the brief's phrasing hides.  Concretely:

* `projection_mul_multiplier_apply_of_split` — the eigen-relation
  `(P Xi)_{cd} = (value + t_c) Xi_{cd}`, valid whenever at every active index
  either the ROW atom lies in that index's subset or the tight direction vanishes
  at the COLUMN atom.  This generalises the forced diagonal of
  `Gtz.diagonal_projection_mul_multiplier_of_isChartStationaryData`, which is the
  case `c = d`.
* `projection_mul_multiplier_apply_of_sameBlock` — under the two-block hypothesis
  that condition holds for any two atoms in the SAME block.
* `multiplier_mul_weightDiagonal_comm` — combining the two readings of
  `(P Xi)_{cd} = (Xi P)_{cd}` gives `(t_c - t_d) Xi_{cd} = 0` inside a block, while
  ACROSS blocks `Xi_{cd}` vanishes outright.  Both cases together say exactly
  `Xi * diag t = diag t * Xi`.  This one equation is the whole of the brief's
  steps 2 to 4: it IS `D`-invariance, in the form the data supplies it.
* `offDiagonal_eq_zero_of_commute_diagonal` — step 6, in matrix form: a matrix
  commuting with a diagonal matrix separates the indices whose diagonal entries
  differ.  Two lines, no submodules.
* `projection_apply_of_mem_block` and `chartStationaryGap_apply_of_mem_block` —
  step 6's conclusion, `W[C] = value • 1`, from distinctness inside `C` ALONE.  The
  other block's weights are not used and the other block's entries are not claimed.
* `projection_diagonal_eq_value_add_weight` — every atom lies in one of the two
  blocks, so step 6 applied to each in turn gives `P_cc = value + t_c` everywhere,
  and the trace of `P` then reads off the value.  THIS is the only place the second
  distinctness hypothesis is used.
* `chartMultiplierAssembly_eq_smul_one` — a byproduct, not on the main line: with
  both blocks distinct the multiplier itself is forced to be `(1/size) • 1`, so the
  branch determines the datum and not merely its value.

## Steps 3 and 5 of the sketch do not appear, and that is the point

Step 3 ("a matrix commuting with a positive semidefinite matrix preserves its
range") and step 5 ("the range has full coordinate support, since every diagonal
entry of `Theta_C` is `1/rank`") are consumed by the entry-level route rather than
proved: the coordinate support that step 5 extracts is exactly the bundle's
constant-diagonal field, which the entry-level argument uses directly, and the
range preservation of step 3 is exactly the commutation the entry-level argument
uses directly.  Nothing is assumed that the sketch proves; two of its seven steps
are simply not on the shortest path.

Nor is the multiplier normalisation `lambda_C = rank/size` of the sketch's step 5
proved, for the same reason: it is a statement about how the assembly SPLITS across
the two blocks, and no lemma below ever needs the split — the assembly is used
whole, through its constant diagonal and its commutation.  What the sketch extracts
from `lambda_C = rank/size` (namely `Theta_C = 1/rank` on the diagonal, hence full
coordinate support) is the constant diagonal, already a field.

## THE HYPOTHESES ARE BOTH LOAD-BEARING, and both witnesses are mechanized

* `chartTwoBlockSplitProjection_isChartStationaryData` — a `(4,2)` chart point with
  weights `(11/100, 39/100, 11/100, 39/100)`, pairwise distinct inside each block,
  carrying a genuine two-block datum at `value = 1/4 = (rank - 1)/(2 * rank)`.  So
  the theorem is NOT vacuous.  The point is also ADMISSIBLE
  (`chartTwoBlockSplit_isChartArgmaxValue`), which matters: admissibility is what
  the sibling module's strictness theorem needs, and a non-vacuity witness that
  failed it would prove much less.  Everything about it is RATIONAL — the
  off-block entry is `12/25`, because `(9/25)(16/25)` is a square.
* `chartTwoBlockUniformProjection_isChartStationaryData` — a `(4,2)` chart point
  with UNIFORM weights, so distinctness fails in both blocks, carrying a two-block
  datum at `value = -1/4 = -1/size`, which is NEGATIVE.  So the distinctness
  hypothesis cannot be dropped:
  `not_forall_zero_le_value_of_isChartTwoBlockFamily` states exactly that.

That second witness carries a NEGATIVE value, where the sibling module's two
witnesses sit at `0` (tetrahedron) and `1/3` (octahedron), and it lands at exactly
the extreme value permitted by
`Gtz.neg_inv_size_le_value_of_isChartStationaryData`.  It is INADMISSIBLE — the
true chart objective at that point is `+1/4`, attained at four of the six pairs —
which is why it does not contradict
`Gtz.not_isChartStationaryData_of_value_eq_neg_inv_size`; it is, rather, a
mechanized demonstration that that theorem's `Gtz.IsChartArgmaxValue` hypothesis
is not decoration.  [The value `+1/4` of the true objective there is EXACT
arithmetic outside Lean and is not mechanized; what is mechanized is the datum.]

## OUT OF SCOPE, deliberately and permanently in this file: repeated weights

The complementary branch — a two-block datum with a repeated weight inside a block
— is NOT treated here, is not sorried, and must not be claimed.  It needs real
casework and the casework is not done.  What survives the theorem below is exactly
"a repeated weight inside AT LEAST ONE block", since the theorem asks for
distinctness in both.

What is KNOWN about that branch is a numerical census, quoted so that no reader
mistakes silence for absence, and quoted as numerics:

  a multistart solve of the unique two-block class at `(6,3)`, 20000 starts with a
  free symmetric multiplier block per part, accepted at residual `1e-10`, produced
  6922 distinct feasible roots.  By weight-coincidence pattern inside the two
  blocks: `(111,111)` 848 roots, `(21,21)` 2489, `(3,3)` 3585.  ALL of them sit at
  `value = 1/3 = (k-1)/(2k)` except six, every one of pattern `(3,3)`: three where
  the value is not the least eigenvalue, and three at `value = -1/6 = -1/size` with
  all six weights equal, all INADMISSIBLE, all with a singular off-block `P12`
  [floating-point multistart numerics, outside Lean, NOT mechanized].

If the sharpened one-block form flagged below is true — the numerics says it is —
then the surviving branch is narrower still, a repeated weight inside EVERY block,
i.e. pattern in `{21, 3} x {21, 3}` at `(6,3)`.  That narrowing is NOT proved here.
Either way the branch is INHABITED: the `(4,2)` uniform witness below is an
instance of it, at the smallest size where one can exist, so the casework is
genuinely needed and not a formality.

## ALSO NOT PROVED, and named so that the gap is citable

Distinctness inside ONE block is enough for the VALUE too, and that is not proved
here.  What is proved from one block is step 6 at that block,
`chartStationaryGap_apply_of_mem_block`; what is missing is the transfer of the
same conclusion to the OTHER block, which is what step 7's trace needs.  The
transfer runs through the OFF-DIAGONAL half of the commutation —
`Theta_C P12 = P12 Theta_{Cᶜ}`, the half every lemma below leaves untouched, since
the same-block half already carries the two-block argument — combined with the
Schur identity `P12 P12ᵀ = diag(s_c (1 - s_c))` forced by idempotence and the
lemma "a symmetric matrix of rank at most one with a zero diagonal is zero".  That
last step needs a rank argument this development does not carry, which is why the
value theorem below asks for distinctness in BOTH blocks: strictly more than the
mathematics needs, and the excess is exactly one block's worth.

## Inherited honesty

Every statement here is conditional on `Gtz.IsChartStationaryData`, which is a
HYPOTHESIS: the variational derivation that would produce it is not formalized,
the system is NECESSARY only (the max rule is a Clarke inclusion because
`lambda_min` is concave, hence not regular where the least eigenvalue is
multiple), and it is satisfied at admissible non-minima.  Read the header of
`Gtz.Quantitative.ChartStationary` before reading anything below as a statement
about the conjecture.
-/
import Mathlib
import Gtz.Quantitative.ChartStationary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}

/-! ## Step 6, in the matrix form the argument actually supplies -/

/-- **A matrix commuting with a diagonal matrix separates indices whose diagonal
entries differ.**

This is the brief's step 6 — "a subspace invariant under a diagonal matrix with
pairwise distinct entries is spanned by standard basis vectors" — in the form the
stationarity data actually hands over.  The subspace formulation would need the
range of the multiplier block as a submodule and an invariance argument; the
commuting matrix is right there, and the entry computation is two lines. -/
theorem offDiagonal_eq_zero_of_commute_diagonal {matrixSize : ℕ}
    (target : Matrix (Fin matrixSize) (Fin matrixSize) ℝ) (scale : Fin matrixSize → ℝ)
    (hcommute : target * Matrix.diagonal scale = Matrix.diagonal scale * target)
    {rowAtom colAtom : Fin matrixSize} (hdistinct : scale rowAtom ≠ scale colAtom) :
    target rowAtom colAtom = 0 := by
  have hentry : (target * Matrix.diagonal scale) rowAtom colAtom
      = (Matrix.diagonal scale * target) rowAtom colAtom := by rw [hcommute]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  have hfactor : (scale colAtom - scale rowAtom) * target rowAtom colAtom = 0 := by
    linear_combination hentry
  rcases mul_eq_zero.mp hfactor with hscale | htarget
  · exact absurd (sub_eq_zero.mp hscale).symm hdistinct
  · exact htarget

/-! ## The two-block hypothesis -/

/-- **The active family is two complementary blocks.**  Every active subset is
either `chosenSubset` or its complement.  Nothing is asserted about which of the
two occurs, nor that both do — that both do is a CONSEQUENCE of the bundle's
constant diagonal, recorded as `card_eq_rank_of_isChartTwoBlockFamily`. -/
def IsChartTwoBlockFamily (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin size)) (chosenSubset : Finset (Fin size)) : Prop :=
  ∀ activeLabel ∈ activeSet,
    activeSubset activeLabel = chosenSubset ∨ activeSubset activeLabel = chosenSubsetᶜ

/-- The two-block hypothesis is symmetric in the two blocks: naming the other one
is the same hypothesis.  This is what lets every block lemma below be proved once
and applied twice. -/
theorem isChartTwoBlockFamily_compl {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {chosenSubset : Finset (Fin size)}
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset) :
    IsChartTwoBlockFamily activeSet activeSubset chosenSubsetᶜ := by
  intro activeLabel hmem
  rcases hfamily activeLabel hmem with hblock | hblock
  · exact Or.inr (by rw [compl_compl]; exact hblock)
  · exact Or.inl hblock

/-- **Pairwise distinct weights inside a block.**  The side condition of the main
theorem, and the one the repeated-weight branch violates. -/
def HasDistinctWeightsOn (weight : Fin size → ℝ) (chosenSubset : Finset (Fin size)) : Prop :=
  ∀ firstAtom ∈ chosenSubset, ∀ secondAtom ∈ chosenSubset,
    firstAtom ≠ secondAtom → weight firstAtom ≠ weight secondAtom

/-! ## Step 1: the assembly is block diagonal -/

/-- The assembly's entries are symmetric, with no bundle in sight — it is a sum of
rank-one projectors. -/
theorem chartMultiplierAssembly_apply_comm (activeSet : Finset activeIndex)
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin size → ℝ))
    (rowAtom colAtom : Fin size) :
    chartMultiplierAssembly activeSet activeWeight tightDir rowAtom colAtom
      = chartMultiplierAssembly activeSet activeWeight tightDir colAtom rowAtom := by
  rw [chartMultiplierAssembly_apply, chartMultiplierAssembly_apply]
  exact Finset.sum_congr rfl fun _ _ => by ring

variable {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
  {value : ℝ} {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
  {chosenSubset : Finset (Fin size)}

/-- **STEP 1.**  Across the two blocks the assembly vanishes: each active index
contributes a tight direction supported in ONE block, so a product of its
coordinates at atoms in different blocks always has a zero factor. -/
theorem chartMultiplierAssembly_apply_eq_zero_of_crossBlock
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    {rowAtom colAtom : Fin size} (hrow : rowAtom ∈ chosenSubset) (hcol : colAtom ∉ chosenSubset) :
    chartMultiplierAssembly activeSet activeWeight tightDir rowAtom colAtom = 0 := by
  rw [chartMultiplierAssembly_apply]
  refine Finset.sum_eq_zero fun activeLabel hmem => ?_
  rcases hfamily activeLabel hmem with hblock | hblock
  · rw [hdata.tightDir_support activeLabel hmem colAtom (by rw [hblock]; exact hcol)]
    ring
  · rw [hdata.tightDir_support activeLabel hmem rowAtom
      (by rw [hblock, Finset.notMem_compl]; exact hrow)]
    ring

/-! ## Steps 2 to 4: the assembly commutes with the weight diagonal -/

/-- **The block eigen-relation.**  If at every active index either the ROW atom
lies in that index's subset or the tight direction vanishes at the COLUMN atom,
then

    `(P Xi)_{cd} = (value + t_c) * Xi_{cd}` .

The first alternative turns the tight eigen-equation into
`(P u)_c = (value + t_c) u_c` through
`Gtz.projection_mulVec_tightDir_of_mem`; the second kills the term outright.  The
forced diagonal `Gtz.diagonal_projection_mul_multiplier_of_isChartStationaryData`
is the special case `c = d`, where the hypothesis holds automatically. -/
theorem projection_mul_multiplier_apply_of_split
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {rowAtom colAtom : Fin size}
    (hsplit : ∀ activeLabel ∈ activeSet,
      rowAtom ∈ activeSubset activeLabel ∨ tightDir activeLabel colAtom = 0) :
    (projection * chartMultiplierAssembly activeSet activeWeight tightDir) rowAtom colAtom
      = (value + weight rowAtom)
        * chartMultiplierAssembly activeSet activeWeight tightDir rowAtom colAtom := by
  have hexpand : (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
      rowAtom colAtom
      = ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * ((projection *ᵥ tightDir activeLabel) rowAtom * tightDir activeLabel colAtom) := by
    rw [Matrix.mul_apply]
    simp only [chartMultiplierAssembly_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun activeLabel _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hexpand, chartMultiplierAssembly_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun activeLabel hmem => ?_
  rcases hsplit activeLabel hmem with hmemSubset | hvanish
  · rw [projection_mulVec_tightDir_of_mem hdata hmem hmemSubset]; ring
  · rw [hvanish]; ring

/-- **STEP 2 to 4 for one entry.**  Two atoms in the SAME block satisfy the
splitting hypothesis: an active index whose subset is the block containing them
covers the row atom, and one whose subset is the other block misses the column
atom. -/
theorem projection_mul_multiplier_apply_of_sameBlock
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    {rowAtom colAtom : Fin size} (hsame : rowAtom ∈ chosenSubset ↔ colAtom ∈ chosenSubset) :
    (projection * chartMultiplierAssembly activeSet activeWeight tightDir) rowAtom colAtom
      = (value + weight rowAtom)
        * chartMultiplierAssembly activeSet activeWeight tightDir rowAtom colAtom := by
  refine projection_mul_multiplier_apply_of_split hdata fun activeLabel hmem => ?_
  rcases hfamily activeLabel hmem with hblock | hblock
  · by_cases hrow : rowAtom ∈ chosenSubset
    · exact Or.inl (by rw [hblock]; exact hrow)
    · exact Or.inr (hdata.tightDir_support activeLabel hmem colAtom
        (by rw [hblock]; exact fun hcol => hrow (hsame.mpr hcol)))
  · by_cases hrow : rowAtom ∈ chosenSubset
    · exact Or.inr (hdata.tightDir_support activeLabel hmem colAtom
        (by rw [hblock, Finset.notMem_compl]; exact hsame.mp hrow))
    · exact Or.inl (by rw [hblock]; exact Finset.mem_compl.mpr hrow)

/-- **STEPS 2 TO 4, ASSEMBLED**: the multiplier commutes with the weight diagonal.

Inside a block, reading `(P Xi)_{cd} = (Xi P)_{cd}` through the block eigen-relation
in both directions gives `(value + t_c) Xi_{cd} = (value + t_d) Xi_{cd}`, i.e.
`(t_c - t_d) Xi_{cd} = 0`.  Across blocks the entry vanishes.  Those two cases are
precisely the entries of `Xi * diag t = diag t * Xi`.

This single equation is the whole content of the brief's steps 2, 3 and 4 — its
`D[C]`-invariance of the range of the multiplier block — in the form the data
supplies.  Note that only the SAME-BLOCK half of the commutation field is used;
the off-block half is not touched here, which is exactly why the theorem below
needs distinctness in both blocks rather than one. -/
theorem multiplier_mul_weightDiagonal_comm
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset) :
    chartMultiplierAssembly activeSet activeWeight tightDir * Matrix.diagonal weight
      = Matrix.diagonal weight * chartMultiplierAssembly activeSet activeWeight tightDir := by
  ext rowAtom colAtom
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hsame : rowAtom ∈ chosenSubset ↔ colAtom ∈ chosenSubset
  · have hmixed : (chartMultiplierAssembly activeSet activeWeight tightDir * projection)
        rowAtom colAtom
        = (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
          colAtom rowAtom := by
      have htranspose : (chartMultiplierAssembly activeSet activeWeight tightDir * projection)ᵀ
          = projection * chartMultiplierAssembly activeSet activeWeight tightDir := by
        rw [Matrix.transpose_mul, hdata.isSymmetric,
          transpose_chartMultiplierAssembly_of_isChartStationaryData hdata]
      calc (chartMultiplierAssembly activeSet activeWeight tightDir * projection) rowAtom colAtom
          = ((chartMultiplierAssembly activeSet activeWeight tightDir * projection)ᵀ)
              colAtom rowAtom := rfl
        _ = (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
              colAtom rowAtom := by rw [htranspose]
    have hforward := projection_mul_multiplier_apply_of_sameBlock hdata hfamily hsame
    have hbackward := projection_mul_multiplier_apply_of_sameBlock hdata hfamily hsame.symm
    have hcommute : (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
        rowAtom colAtom
        = (chartMultiplierAssembly activeSet activeWeight tightDir * projection)
          rowAtom colAtom := by rw [hdata.assembly_commutes]
    rw [hmixed, hforward, hbackward,
      chartMultiplierAssembly_apply_comm activeSet activeWeight tightDir colAtom rowAtom]
      at hcommute
    linear_combination -hcommute
  · have hzero : chartMultiplierAssembly activeSet activeWeight tightDir rowAtom colAtom = 0 := by
      by_cases hrow : rowAtom ∈ chosenSubset
      · exact chartMultiplierAssembly_apply_eq_zero_of_crossBlock hdata hfamily hrow
          fun hcol => hsame ⟨fun _ => hcol, fun _ => hrow⟩
      · have hcol : colAtom ∈ chosenSubset := by
          by_contra hnotMem
          exact hsame ⟨fun hmem => absurd hmem hrow, fun hmem => absurd hmem hnotMem⟩
        rw [chartMultiplierAssembly_apply_comm]
        exact chartMultiplierAssembly_apply_eq_zero_of_crossBlock hdata hfamily hcol hrow
    rw [hzero]
    ring

/-! ## Step 6, and it needs distinctness in ONE block only -/

/-- **STEP 6 for the multiplier, one block at a time.**  With pairwise distinct
weights inside a block, the multiplier's column at an atom OF THAT BLOCK is
concentrated on that atom: every other entry of the column vanishes, whether the
other atom is in the block (distinct weights, separated by the commutation) or out
of it (separated by the block structure).

Only the named block's weights are used.  The other block is untouched. -/
theorem chartMultiplierAssembly_apply_eq_zero_of_ne_of_mem
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hdistinct : HasDistinctWeightsOn weight chosenSubset)
    {rowAtom colAtom : Fin size} (hcol : colAtom ∈ chosenSubset) (hdifferent : rowAtom ≠ colAtom) :
    chartMultiplierAssembly activeSet activeWeight tightDir rowAtom colAtom = 0 := by
  by_cases hrow : rowAtom ∈ chosenSubset
  · exact offDiagonal_eq_zero_of_commute_diagonal _ weight
      (multiplier_mul_weightDiagonal_comm hdata hfamily)
      (hdistinct rowAtom hrow colAtom hcol hdifferent)
  · rw [chartMultiplierAssembly_apply_comm]
    exact chartMultiplierAssembly_apply_eq_zero_of_crossBlock hdata hfamily hcol hrow

/-- **STEP 6, IN THE SHARP FORM THE SKETCH STATES IT.**  With pairwise distinct
weights inside a block, the chart is DIAGONAL on that block, with the forced
entries:

    `P_cd = value + t_c` at `c = d`, and `0` at `c ≠ d`, for `c, d` in the block.

Distinctness inside the OTHER block is not used, and the other block's entries are
not claimed.  So the sketch's step 6 — "the only `D[C]`-invariant subspace with
full coordinate support is everything, hence `W[C] = G I`" — holds under exactly
the hypothesis the sketch states, distinctness inside `C` alone; it is step 7, the
trace, that needs both blocks.

Proof: the block eigen-relation reads `(P Xi)_{cd} = (value + t_c) Xi_{cd}`, and
with the column at `d` concentrated on `d` the left side collapses to
`P_{cd} Xi_{dd} = P_{cd}/size`.  At `c = d` the right side is `(value + t_c)/size`;
at `c ≠ d` it is zero. -/
theorem projection_apply_of_mem_block
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hdistinct : HasDistinctWeightsOn weight chosenSubset)
    {rowAtom colAtom : Fin size} (hrow : rowAtom ∈ chosenSubset) (hcol : colAtom ∈ chosenSubset) :
    projection rowAtom colAtom = if rowAtom = colAtom then value + weight rowAtom else 0 := by
  have hsizePos := size_cast_pos_of_isChartStationaryData hdata
  have hcollapse : (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
      rowAtom colAtom = projection rowAtom colAtom * ((size : ℝ))⁻¹ := by
    rw [Matrix.mul_apply, Finset.sum_eq_single colAtom]
    · rw [hdata.assembly_diagonal]
    · intro otherAtom _ hdifferent
      rw [chartMultiplierAssembly_apply_eq_zero_of_ne_of_mem hdata hfamily hdistinct hcol
        hdifferent, mul_zero]
    · intro hnotMem
      exact absurd (Finset.mem_univ colAtom) hnotMem
  have hblock := projection_mul_multiplier_apply_of_sameBlock hdata hfamily (iff_of_true hrow hcol)
  rw [hcollapse] at hblock
  by_cases hequal : rowAtom = colAtom
  · subst hequal
    rw [if_pos rfl]
    rw [hdata.assembly_diagonal] at hblock
    field_simp at hblock
    linarith
  · rw [if_neg hequal]
    rw [chartMultiplierAssembly_apply_eq_zero_of_ne_of_mem hdata hfamily hdistinct hcol hequal,
      mul_zero] at hblock
    field_simp at hblock
    linarith

/-- **The gap is the value times the identity on a block with distinct weights**:
`W[C] = value • 1`.  This is the sketch's step 6 verbatim, and the reason the
two-block branch has no freedom left in it. -/
theorem chartStationaryGap_apply_of_mem_block
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hdistinct : HasDistinctWeightsOn weight chosenSubset)
    {rowAtom colAtom : Fin size} (hrow : rowAtom ∈ chosenSubset) (hcol : colAtom ∈ chosenSubset) :
    chartStationaryGap projection weight rowAtom colAtom
      = if rowAtom = colAtom then value else 0 := by
  rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply,
    projection_apply_of_mem_block hdata hfamily hdistinct hrow hcol]
  by_cases hequal : rowAtom = colAtom
  · rw [if_pos hequal, if_pos hequal, if_pos hequal]
    subst hequal
    ring
  · rw [if_neg hequal, if_neg hequal, if_neg hequal]
    ring

/-- **The assembly is forced to be the scalar `(1/size) • 1`** once BOTH blocks have
pairwise distinct weights.  Its diagonal was already pinned by the bundle's
simplex-stationarity field; step 6, applied to each block in turn, kills everything
else.

Not needed for the value below — that runs through the chart's diagonal directly —
but worth recording: the two-block branch determines the multiplier as well as the
value, so nothing in the datum is free. -/
theorem chartMultiplierAssembly_eq_smul_one
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hdistinct : HasDistinctWeightsOn weight chosenSubset)
    (hdistinctCompl : HasDistinctWeightsOn weight chosenSubsetᶜ) :
    chartMultiplierAssembly activeSet activeWeight tightDir
      = ((size : ℝ))⁻¹ • (1 : Matrix (Fin size) (Fin size) ℝ) := by
  ext rowAtom colAtom
  by_cases hequal : rowAtom = colAtom
  · subst hequal
    rw [hdata.assembly_diagonal, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  · rw [Matrix.smul_apply, Matrix.one_apply_ne hequal, smul_zero]
    by_cases hcol : colAtom ∈ chosenSubset
    · exact chartMultiplierAssembly_apply_eq_zero_of_ne_of_mem hdata hfamily hdistinct hcol hequal
    · exact chartMultiplierAssembly_apply_eq_zero_of_ne_of_mem hdata
        (isChartTwoBlockFamily_compl hfamily) hdistinctCompl (Finset.mem_compl.mpr hcol) hequal

/-! ## Step 7: the value, and here both blocks are needed -/

/-- **The chart's diagonal is forced at every atom**: `P_cc = value + t_c`.

Step 6 supplies this inside whichever block the atom lies in — and every atom lies
in one of the two.  THIS is where the second distinctness hypothesis enters, and it
is the only place: an atom of the complement is reached by applying step 6 to the
complementary block. -/
theorem projection_diagonal_eq_value_add_weight
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hdistinct : HasDistinctWeightsOn weight chosenSubset)
    (hdistinctCompl : HasDistinctWeightsOn weight chosenSubsetᶜ) (atomIndex : Fin size) :
    projection atomIndex atomIndex = value + weight atomIndex := by
  by_cases hmem : atomIndex ∈ chosenSubset
  · have hblock := projection_apply_of_mem_block hdata hfamily hdistinct hmem hmem
    rwa [if_pos rfl] at hblock
  · have hblock := projection_apply_of_mem_block hdata (isChartTwoBlockFamily_compl hfamily)
      hdistinctCompl (Finset.mem_compl.mpr hmem) (Finset.mem_compl.mpr hmem)
    rwa [if_pos rfl] at hblock

/-- **THE TWO-BLOCK VALUE.**  A chart stationarity datum whose active family is two
complementary blocks, with pairwise distinct weights inside each, has

    `value = (rank - 1) / size` .

The chart's diagonal is `value + t_c` at every atom, the weights sum to one, and
the trace of the chart is the rank; so `rank = size * value + 1`.

This is the entire two-block branch, in one equation: the value is DETERMINED, not
merely bounded.  In particular it cannot be negative once `rank ≥ 1` — see
`zero_le_value_of_isChartTwoBlockFamily`, which is the form the search argument
consumes. -/
theorem value_eq_rank_sub_one_div_size_of_isChartTwoBlockFamily
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hdistinct : HasDistinctWeightsOn weight chosenSubset)
    (hdistinctCompl : HasDistinctWeightsOn weight chosenSubsetᶜ) :
    value = ((rank : ℝ) - 1) / (size : ℝ) := by
  have hsizePos := size_cast_pos_of_isChartStationaryData hdata
  have hdiagSum : Matrix.trace projection = ∑ atomIndex : Fin size, (value + weight atomIndex) :=
    Finset.sum_congr rfl fun atomIndex _ =>
      projection_diagonal_eq_value_add_weight hdata hfamily hdistinct hdistinctCompl atomIndex
  rw [hdata.hasTraceRank, Finset.sum_add_distrib, hdata.weight_sum_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hdiagSum
  field_simp
  linarith

/-! ## The rank is positive, and both blocks are realised -/

/-- **The rank is positive.**  Every active index carries a UNIT tight direction
supported inside a subset of `rank` atoms; at rank zero that subset is empty and
the direction is the zero vector, which is not a unit vector. -/
theorem rank_pos_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    0 < rank := by
  obtain ⟨activeLabel, hmem⟩ := activeSet_nonempty_of_isChartStationaryData hdata
  by_contra hnonpositive
  have hrankZero : rank = 0 := Nat.le_zero.mp (not_lt.mp hnonpositive)
  have hcard := hdata.activeSubset_card activeLabel hmem
  rw [hrankZero, Finset.card_eq_zero] at hcard
  have hvanish : tightDir activeLabel = 0 := by
    funext atomIndex
    exact hdata.tightDir_support activeLabel hmem atomIndex
      (by rw [hcard]; exact Finset.notMem_empty atomIndex)
  have hunit := hdata.tightDir_unit activeLabel hmem
  rw [hvanish, zero_dotProduct] at hunit
  exact absurd hunit (by norm_num)

/-- **A nonempty block has exactly `rank` atoms.**  Coverage puts each of its atoms
in some active subset, and the two-block hypothesis makes that subset the block
itself — the other block misses the atom.  So the block is an active subset, and
active subsets have `rank` atoms. -/
theorem card_eq_rank_of_isChartTwoBlockFamily
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hnonempty : chosenSubset.Nonempty) :
    chosenSubset.card = rank := by
  obtain ⟨someAtom, hsomeAtom⟩ := hnonempty
  obtain ⟨activeLabel, hmem, hmemSubset⟩ :=
    exists_mem_activeSubset_of_isChartStationaryData hdata someAtom
  rcases hfamily activeLabel hmem with hblock | hblock
  · rw [← hblock]
    exact hdata.activeSubset_card activeLabel hmem
  · rw [hblock, Finset.mem_compl] at hmemSubset
    exact absurd hsomeAtom hmemSubset

/-- **Both blocks nonempty forces `size = 2 * rank`.**  Each block has `rank` atoms
and the two partition the index set. -/
theorem size_eq_two_mul_rank_of_isChartTwoBlockFamily
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hnonempty : chosenSubset.Nonempty) (hnonemptyCompl : chosenSubsetᶜ.Nonempty) :
    size = 2 * rank := by
  have hcard := card_eq_rank_of_isChartTwoBlockFamily hdata hfamily hnonempty
  have hcardCompl :=
    card_eq_rank_of_isChartTwoBlockFamily hdata (isChartTwoBlockFamily_compl hfamily)
      hnonemptyCompl
  have hsplit : chosenSubset.card + chosenSubsetᶜ.card = size := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  rw [hcard, hcardCompl] at hsplit
  omega

/-- **THE TWO-BLOCK VALUE at `size = 2 * rank`**, which is the shape the branch
takes: `value = (rank - 1) / (2 * rank)`. -/
theorem value_eq_of_isChartTwoBlockFamily
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hdistinct : HasDistinctWeightsOn weight chosenSubset)
    (hdistinctCompl : HasDistinctWeightsOn weight chosenSubsetᶜ)
    (hnonempty : chosenSubset.Nonempty) (hnonemptyCompl : chosenSubsetᶜ.Nonempty) :
    value = ((rank : ℝ) - 1) / (2 * (rank : ℝ)) := by
  have hsize := size_eq_two_mul_rank_of_isChartTwoBlockFamily hdata hfamily hnonempty hnonemptyCompl
  have hvalue :=
    value_eq_rank_sub_one_div_size_of_isChartTwoBlockFamily hdata hfamily hdistinct hdistinctCompl
  rw [hvalue, hsize]
  push_cast
  ring

/-- **THE CLOSURE OF THE TWO-BLOCK BRANCH**: the value is NONNEGATIVE.

A counterexample to the conjecture would sit at a negative value; this says that
no two-block datum with pairwise distinct weights inside each block is one.  The
side condition is real and is not removable by this proof — the uniform witness
below satisfies all THIRTEEN fields of `Gtz.IsChartStationaryData` and the
two-block structure, at `value = -1/size`. -/
theorem zero_le_value_of_isChartTwoBlockFamily
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hdistinct : HasDistinctWeightsOn weight chosenSubset)
    (hdistinctCompl : HasDistinctWeightsOn weight chosenSubsetᶜ) :
    0 ≤ value := by
  have hsizePos := size_cast_pos_of_isChartStationaryData hdata
  have hrankPos : (1 : ℝ) ≤ (rank : ℝ) := by
    exact_mod_cast rank_pos_of_isChartStationaryData hdata
  rw [value_eq_rank_sub_one_div_size_of_isChartTwoBlockFamily hdata hfamily hdistinct
    hdistinctCompl]
  exact div_nonneg (by linarith) hsizePos.le

/-! ## The hypotheses are inhabited — a `(4,2)` datum with distinct weights

Four atoms, blocks `{0,1}` and `{2,3}`, weights `(11/100, 39/100, 11/100, 39/100)`
— pairwise distinct inside each block, which is exactly what the theorem asks.
The chart is

    `9/25` and `16/25` alternating on the diagonal, `12/25` at the four entries
    where the two indices sum to three, and zero everywhere else,

so it pairs atom `0` with atom `3` and atom `1` with atom `2` ACROSS the blocks and
is diagonal INSIDE them.  Everything is rational because `(9/25)(16/25)` is the
square of `12/25`; the general shape of this branch forces the off-block Gram to be
`diag(s_c (1 - s_c))` with `s_c = value + t_c`, and a rational square there is a
matter of choosing `9/25` rather than, say, `1/2`.

The gap is `(1/4) I` on each block, so every coordinate direction is tight at
`value = 1/4`, which is `(rank - 1)/(2 * rank)` at `rank = 2` — exactly the value
the closure predicts.  The assembly is `(1/4) • 1`, matching the forced diagonal, and
being scalar it commutes with the chart for free.

The point is ADMISSIBLE as well (`chartTwoBlockSplit_isChartArgmaxValue`): every
coordinate direction has Rayleigh quotient exactly `1/4` against the gap, so no
pair beats the value.  [That the true chart objective there IS `1/4`, attained at
four of the six pairs while the two cross pairs sit at `-23/100`, is EXACT
arithmetic outside Lean and is not mechanized.] -/

/-- The split chart: `9/25`, `16/25` alternating on the diagonal, `12/25` where the
indices sum to three. -/
noncomputable def chartTwoBlockSplitProjection : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun rowIndex colIndex =>
    if rowIndex = colIndex then (if (rowIndex : ℕ) % 2 = 0 then 9 / 25 else 16 / 25)
    else if (rowIndex : ℕ) + (colIndex : ℕ) = 3 then 12 / 25 else 0

/-- The split weights `(11/100, 39/100, 11/100, 39/100)`: distinct inside each
block, and equal to `P_cc - 1/4` as the two-block value law demands. -/
noncomputable def chartTwoBlockSplitWeight : Fin 4 → ℝ :=
  fun atomIndex => if (atomIndex : ℕ) % 2 = 0 then 11 / 100 else 39 / 100

/-- The block carrying each active index: labels `0, 1` take `{0,1}`, labels `2, 3`
take `{2,3}`. -/
def chartTwoBlockSplitSubset (activeLabel : Fin 4) : Finset (Fin 4) :=
  if (activeLabel : ℕ) < 2 then {0, 1} else {2, 3}

/-- The uniform split multipliers. -/
noncomputable def chartTwoBlockSplitMultiplierWeight : Fin 4 → ℝ := fun _ => (4 : ℝ)⁻¹

/-- The tight directions: the four coordinate directions.  Each block's gap is a
scalar matrix, so every direction supported inside it is tight. -/
noncomputable def chartTwoBlockSplitTightDir (activeLabel : Fin 4) : Fin 4 → ℝ :=
  Pi.single activeLabel 1

theorem chartTwoBlockSplitProjection_transpose :
    chartTwoBlockSplitProjectionᵀ = chartTwoBlockSplitProjection := by
  ext rowIndex colIndex
  simp only [Matrix.transpose_apply, chartTwoBlockSplitProjection, Matrix.of_apply]
  by_cases hequal : rowIndex = colIndex
  · rw [hequal]
  · rw [if_neg (Ne.symm hequal), if_neg hequal]
    by_cases hpair : (rowIndex : ℕ) + (colIndex : ℕ) = 3
    · rw [if_pos (by omega), if_pos hpair]
    · rw [if_neg (by omega), if_neg hpair]

theorem chartTwoBlockSplitProjection_mul_self :
    chartTwoBlockSplitProjection * chartTwoBlockSplitProjection = chartTwoBlockSplitProjection := by
  ext rowIndex colIndex
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [chartTwoBlockSplitProjection, Fin.ext_iff]

/-- The split gap: `1/4` on the diagonal, `12/25` where the indices sum to three,
zero elsewhere.  Both blocks are therefore scalar. -/
theorem chartTwoBlockSplitGap_apply (rowIndex colIndex : Fin 4) :
    chartStationaryGap chartTwoBlockSplitProjection chartTwoBlockSplitWeight rowIndex colIndex
      = if rowIndex = colIndex then (4 : ℝ)⁻¹
        else if (rowIndex : ℕ) + (colIndex : ℕ) = 3 then 12 / 25 else 0 := by
  simp only [chartStationaryGap, Matrix.sub_apply, chartTwoBlockSplitProjection, Matrix.of_apply,
    Matrix.diagonal_apply, chartTwoBlockSplitWeight]
  by_cases hequal : rowIndex = colIndex
  · subst hequal
    by_cases hparity : (rowIndex : ℕ) % 2 = 0 <;> simp [hparity] <;> norm_num
  · rw [if_neg hequal, if_neg hequal, if_neg hequal, sub_zero]

/-- The split assembly is the scalar `(1/4) • 1`: the four coordinate projectors
with multiplier `1/4` resolve the identity. -/
theorem chartTwoBlockSplitMultiplierAssembly_eq :
    chartMultiplierAssembly (Finset.univ : Finset (Fin 4)) chartTwoBlockSplitMultiplierWeight
        chartTwoBlockSplitTightDir
      = (4 : ℝ)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext rowIndex colIndex
  rw [chartMultiplierAssembly_apply, Fin.sum_univ_four]
  simp only [chartTwoBlockSplitMultiplierWeight, chartTwoBlockSplitTightDir, Pi.single_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Fin.ext_iff]

/-- **THE SPLIT DATUM.**  Rank two, four atoms, `value = 1/4`, two complementary
blocks, pairwise distinct weights inside each, assembly `(1/4) • 1`. -/
theorem chartTwoBlockSplitProjection_isChartStationaryData :
    IsChartStationaryData 2 chartTwoBlockSplitProjection chartTwoBlockSplitWeight (4 : ℝ)⁻¹
      (Finset.univ : Finset (Fin 4)) chartTwoBlockSplitSubset chartTwoBlockSplitMultiplierWeight
      chartTwoBlockSplitTightDir where
  isSymmetric := chartTwoBlockSplitProjection_transpose
  isIdempotent := chartTwoBlockSplitProjection_mul_self
  hasTraceRank := by
    show ∑ atomIndex : Fin 4, chartTwoBlockSplitProjection atomIndex atomIndex = ((2 : ℕ) : ℝ)
    rw [Fin.sum_univ_four]
    norm_num [chartTwoBlockSplitProjection]
  weight_pos := by
    intro atomIndex
    by_cases hparity : (atomIndex : ℕ) % 2 = 0 <;> simp [chartTwoBlockSplitWeight, hparity]
  weight_sum_one := by
    rw [Fin.sum_univ_four]
    norm_num [chartTwoBlockSplitWeight]
  activeWeight_nonneg := by intro activeLabel _; norm_num [chartTwoBlockSplitMultiplierWeight]
  activeWeight_sum_one := by
    rw [Fin.sum_univ_four]
    norm_num [chartTwoBlockSplitMultiplierWeight]
  activeSubset_card := by
    intro activeLabel _
    fin_cases activeLabel <;> decide
  tightDir_unit := by
    intro activeLabel _
    simp [chartTwoBlockSplitTightDir]
  tightDir_support := by
    intro activeLabel _ atomIndex hnotMem
    have hdistinct : atomIndex ≠ activeLabel := by
      intro hequal
      rw [hequal] at hnotMem
      revert hnotMem
      fin_cases activeLabel <;> decide
    rw [chartTwoBlockSplitTightDir, Pi.single_apply, if_neg hdistinct]
  tightDir_isTight := by
    intro activeLabel _ atomIndex hmem
    have hcolumn : (chartStationaryGap chartTwoBlockSplitProjection chartTwoBlockSplitWeight
        *ᵥ chartTwoBlockSplitTightDir activeLabel) atomIndex
        = chartStationaryGap chartTwoBlockSplitProjection chartTwoBlockSplitWeight
            atomIndex activeLabel := by
      rw [chartTwoBlockSplitTightDir, Matrix.mulVec_single_one]
      rfl
    rw [hcolumn, chartTwoBlockSplitTightDir, Pi.single_apply, chartTwoBlockSplitGap_apply]
    revert hmem
    fin_cases activeLabel <;> fin_cases atomIndex <;>
      simp [chartTwoBlockSplitSubset, Fin.ext_iff]
  assembly_diagonal := by
    intro atomIndex
    rw [chartTwoBlockSplitMultiplierAssembly_eq, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one]
    norm_num
  assembly_commutes := by
    rw [chartTwoBlockSplitMultiplierAssembly_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]

/-- The split family is two complementary blocks, `{0,1}` and `{2,3}`. -/
theorem chartTwoBlockSplit_isChartTwoBlockFamily :
    IsChartTwoBlockFamily (Finset.univ : Finset (Fin 4)) chartTwoBlockSplitSubset
      ({0, 1} : Finset (Fin 4)) := by
  intro activeLabel _
  fin_cases activeLabel <;> simp [chartTwoBlockSplitSubset] <;> decide

/-- The split weights are pairwise distinct inside the first block. -/
theorem chartTwoBlockSplitWeight_hasDistinctWeightsOn :
    HasDistinctWeightsOn chartTwoBlockSplitWeight ({0, 1} : Finset (Fin 4)) := by
  intro firstAtom hfirst secondAtom hsecond hdistinct
  fin_cases hfirst <;> fin_cases hsecond <;> simp_all [chartTwoBlockSplitWeight]

/-- The split weights are pairwise distinct inside the second block. -/
theorem chartTwoBlockSplitWeight_hasDistinctWeightsOn_compl :
    HasDistinctWeightsOn chartTwoBlockSplitWeight ({0, 1} : Finset (Fin 4))ᶜ := by
  intro firstAtom hfirst secondAtom hsecond hdistinct
  rw [Finset.mem_compl] at hfirst hsecond
  fin_cases firstAtom <;> fin_cases secondAtom <;> simp_all [chartTwoBlockSplitWeight]

/-- **THE HYPOTHESES OF THE TWO-BLOCK THEOREM ARE INHABITED.**  There is a chart
stationarity datum whose active family is two complementary blocks with pairwise
distinct weights inside each — so the closure above is not a statement about the
empty set. -/
theorem exists_isChartStationaryData_isChartTwoBlockFamily :
    ∃ (projection : Matrix (Fin 4) (Fin 4) ℝ) (weight : Fin 4 → ℝ)
      (activeSubset : Fin 4 → Finset (Fin 4)) (activeWeight : Fin 4 → ℝ)
      (tightDir : Fin 4 → (Fin 4 → ℝ)) (chosenSubset : Finset (Fin 4)),
      IsChartStationaryData 2 projection weight (4 : ℝ)⁻¹ (Finset.univ : Finset (Fin 4))
          activeSubset activeWeight tightDir ∧
        IsChartTwoBlockFamily (Finset.univ : Finset (Fin 4)) activeSubset chosenSubset ∧
        HasDistinctWeightsOn weight chosenSubset ∧
        HasDistinctWeightsOn weight chosenSubsetᶜ :=
  ⟨chartTwoBlockSplitProjection, chartTwoBlockSplitWeight, chartTwoBlockSplitSubset,
    chartTwoBlockSplitMultiplierWeight, chartTwoBlockSplitTightDir, {0, 1},
    chartTwoBlockSplitProjection_isChartStationaryData, chartTwoBlockSplit_isChartTwoBlockFamily,
    chartTwoBlockSplitWeight_hasDistinctWeightsOn,
    chartTwoBlockSplitWeight_hasDistinctWeightsOn_compl⟩

/-- **The split datum is ADMISSIBLE.**  Every coordinate direction has Rayleigh
quotient exactly `1/4` against the split gap, and every pair contains one, so no
pair beats the value.

This matters because the sibling module's strictness theorem consumes
`Gtz.IsChartArgmaxValue`, and a non-vacuity witness that failed it would leave open
the possibility that the two-block branch is inhabited only by data the rest of the
development already discards. -/
theorem chartTwoBlockSplit_isChartArgmaxValue :
    IsChartArgmaxValue 2 chartTwoBlockSplitProjection chartTwoBlockSplitWeight (4 : ℝ)⁻¹ := by
  intro chosenSubset hcard
  obtain ⟨someAtom, hsomeAtom⟩ : chosenSubset.Nonempty := by
    rw [← Finset.card_pos, hcard]
    norm_num
  refine ⟨Pi.single someAtom 1, by simp, ?_, ?_⟩
  · intro atomIndex hnotMem
    have hdistinct : atomIndex ≠ someAtom := by
      intro hequal
      rw [hequal] at hnotMem
      exact hnotMem hsomeAtom
    rw [Pi.single_apply, if_neg hdistinct]
  · rw [Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col_apply,
      chartTwoBlockSplitGap_apply, if_pos rfl]

/-! ## The distinctness hypothesis cannot be dropped — a `(4,2)` datum at a
NEGATIVE value

Four atoms at UNIFORM weight `1/4`, blocks `{0,1}` and `{2,3}`, and the chart

    `1/2` on the diagonal, `-1/2` between the two atoms of a block, `0` across,

which is the direct sum of two copies of `[[1/2, -1/2], [-1/2, 1/2]]` — the same
shape the octahedron witness of the sibling module carries on three axes rather
than two.  The gap is then `1/4` on the diagonal and `-1/2` inside a block, so each
block's all-ones direction is tight at

    `1/4 - 1/2 = -1/4 = -1/size` ,

and the two normalised all-ones directions with multiplier `1/2` each assemble to
the matrix that is `1/4` inside the blocks and `0` across.  That has constant
diagonal `1/4 = 1/size`, and the chart annihilates both tight directions, so the
assembly commutes with the chart because BOTH products vanish.

The weights are uniform, so distinctness fails inside each block — and the value is
`-1/4 < 0`.  So `zero_le_value_of_isChartTwoBlockFamily` is FALSE without its side
condition, which is `not_forall_zero_le_value_of_isChartTwoBlockFamily` below, and
the repeated-weight branch that this file declares out of scope is INHABITED, at
the smallest size where it can be.

Two further readings of the same witness, both stated because they are what a
reader of the sibling module will want:

* it is a `Gtz.IsChartStationaryData` with a NEGATIVE value, where the sibling
  module's two witnesses sit at `0` and `1/3`, and it sits at exactly the floor
  `Gtz.neg_inv_size_le_value_of_isChartStationaryData` permits;
* it therefore shows that the `Gtz.IsChartArgmaxValue` hypothesis of
  `Gtz.not_isChartStationaryData_of_value_eq_neg_inv_size` is load-bearing: drop it
  and that theorem is refuted by this datum.  [It is INADMISSIBLE: the true chart
  objective here is `+1/4`, attained at the four pairs that straddle the two
  blocks, while the two within-block pairs sit at `-1/4`.  EXACT arithmetic outside
  Lean, not mechanized — what is mechanized is the datum.] -/

/-- The block of an atom: `0, 1` share block `0` and `2, 3` share block `1`. -/
def chartTwoBlockPairAxis (atomIndex : Fin 4) : ℕ := (atomIndex : ℕ) / 2

/-- The uniform chart: `1/2` on the diagonal, `-1/2` inside a block, `0` across. -/
noncomputable def chartTwoBlockUniformProjection : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun rowIndex colIndex =>
    if rowIndex = colIndex then 1 / 2
    else if chartTwoBlockPairAxis rowIndex = chartTwoBlockPairAxis colIndex then -(1 / 2) else 0

/-- The uniform weights — the reason distinctness fails. -/
noncomputable def chartTwoBlockUniformWeight : Fin 4 → ℝ := fun _ => (4 : ℝ)⁻¹

/-- The two blocks. -/
def chartTwoBlockUniformSubset (blockLabel : Fin 2) : Finset (Fin 4) :=
  if blockLabel = 0 then {0, 1} else {2, 3}

/-- The uniform multipliers, one half on each block. -/
noncomputable def chartTwoBlockUniformMultiplierWeight : Fin 2 → ℝ := fun _ => (2 : ℝ)⁻¹

/-- The UNNORMALISED tight direction: the indicator of a block, of squared length
two. -/
def chartTwoBlockUniformSupport (blockLabel : Fin 2) : Fin 4 → ℝ :=
  fun atomIndex => if chartTwoBlockPairAxis atomIndex = (blockLabel : ℕ) then 1 else 0

/-- The tight direction: a block's all-ones direction, normalised. -/
noncomputable def chartTwoBlockUniformTightDir (blockLabel : Fin 2) : Fin 4 → ℝ :=
  (Real.sqrt 2)⁻¹ • chartTwoBlockUniformSupport blockLabel

/-- The uniform assembly: `1/4` inside each block, `0` across. -/
noncomputable def chartTwoBlockUniformMultiplier : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun rowIndex colIndex =>
    if chartTwoBlockPairAxis rowIndex = chartTwoBlockPairAxis colIndex then 1 / 4 else 0

theorem chartTwoBlockUniformProjection_transpose :
    chartTwoBlockUniformProjectionᵀ = chartTwoBlockUniformProjection := by
  ext rowIndex colIndex
  simp only [Matrix.transpose_apply, chartTwoBlockUniformProjection, Matrix.of_apply]
  by_cases hequal : rowIndex = colIndex
  · rw [hequal]
  · rw [if_neg (Ne.symm hequal), if_neg hequal]
    by_cases haxis : chartTwoBlockPairAxis rowIndex = chartTwoBlockPairAxis colIndex
    · rw [if_pos haxis.symm, if_pos haxis]
    · rw [if_neg fun hflip => haxis hflip.symm, if_neg haxis]

theorem chartTwoBlockUniformProjection_mul_self :
    chartTwoBlockUniformProjection * chartTwoBlockUniformProjection
      = chartTwoBlockUniformProjection := by
  ext rowIndex colIndex
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [chartTwoBlockUniformProjection, chartTwoBlockPairAxis, Fin.ext_iff]

/-- The uniform gap: `1/4` on the diagonal, `-1/2` inside a block, `0` across. -/
theorem chartTwoBlockUniformGap_apply (rowIndex colIndex : Fin 4) :
    chartStationaryGap chartTwoBlockUniformProjection chartTwoBlockUniformWeight rowIndex colIndex
      = if rowIndex = colIndex then (4 : ℝ)⁻¹
        else if chartTwoBlockPairAxis rowIndex = chartTwoBlockPairAxis colIndex then -(1 / 2)
          else 0 := by
  simp only [chartStationaryGap, Matrix.sub_apply, chartTwoBlockUniformProjection, Matrix.of_apply,
    Matrix.diagonal_apply, chartTwoBlockUniformWeight]
  by_cases hequal : rowIndex = colIndex
  · rw [if_pos hequal, if_pos hequal, if_pos hequal]
    norm_num
  · rw [if_neg hequal, if_neg hequal, if_neg hequal, sub_zero]

/-- An atom of a block has block index that block. -/
theorem chartTwoBlockUniformAxis_of_mem (blockLabel : Fin 2) (atomIndex : Fin 4)
    (hmem : atomIndex ∈ chartTwoBlockUniformSubset blockLabel) :
    chartTwoBlockPairAxis atomIndex = (blockLabel : ℕ) := by
  fin_cases blockLabel <;> fin_cases atomIndex <;>
    simp_all [chartTwoBlockUniformSubset, chartTwoBlockPairAxis]

/-- An atom outside a block does not have that block index. -/
theorem chartTwoBlockUniformAxis_ne_of_notMem (blockLabel : Fin 2) (atomIndex : Fin 4)
    (hnotMem : atomIndex ∉ chartTwoBlockUniformSubset blockLabel) :
    chartTwoBlockPairAxis atomIndex ≠ (blockLabel : ℕ) := by
  fin_cases blockLabel <;> fin_cases atomIndex <;>
    simp_all [chartTwoBlockUniformSubset, chartTwoBlockPairAxis]

/-- The indicator of a block has squared length two. -/
theorem chartTwoBlockUniformSupport_dotProduct_self (blockLabel : Fin 2) :
    chartTwoBlockUniformSupport blockLabel ⬝ᵥ chartTwoBlockUniformSupport blockLabel = 2 := by
  simp only [dotProduct, chartTwoBlockUniformSupport, chartTwoBlockPairAxis, Fin.sum_univ_four]
  fin_cases blockLabel <;> norm_num

/-- **The chart annihilates each block's all-ones direction, at the value
`-1/4`.**  Inside the block the gap contributes `1/4` at the atom itself and `-1/2`
at its partner; across blocks it contributes nothing. -/
theorem chartTwoBlockUniformGap_mulVec_support (blockLabel : Fin 2) (atomIndex : Fin 4)
    (hmem : atomIndex ∈ chartTwoBlockUniformSubset blockLabel) :
    (chartStationaryGap chartTwoBlockUniformProjection chartTwoBlockUniformWeight
        *ᵥ chartTwoBlockUniformSupport blockLabel) atomIndex = -(4 : ℝ)⁻¹ := by
  simp only [Matrix.mulVec, dotProduct, chartTwoBlockUniformGap_apply,
    chartTwoBlockUniformSupport, chartTwoBlockPairAxis, Fin.sum_univ_four]
  revert hmem
  fin_cases blockLabel <;> fin_cases atomIndex <;>
    simp [chartTwoBlockUniformSubset, Fin.ext_iff] <;> norm_num

/-- The uniform assembly is `1/4` inside the blocks and `0` across: each block's
normalised all-ones projector carries multiplier `1/2`, and `(1/2)(1/2) = 1/4`. -/
theorem chartTwoBlockUniformMultiplierAssembly_eq :
    chartMultiplierAssembly (Finset.univ : Finset (Fin 2)) chartTwoBlockUniformMultiplierWeight
        chartTwoBlockUniformTightDir
      = chartTwoBlockUniformMultiplier := by
  have hsquare : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hscale : ∀ blockLabel : Fin 2,
      chartTwoBlockUniformMultiplierWeight blockLabel
          • atomMatrix (chartTwoBlockUniformTightDir blockLabel)
        = (4 : ℝ)⁻¹ • atomMatrix (chartTwoBlockUniformSupport blockLabel) := by
    intro blockLabel
    rw [chartTwoBlockUniformTightDir, atomMatrix_smul, inv_pow, hsquare, smul_smul,
      chartTwoBlockUniformMultiplierWeight]
    norm_num
  rw [chartMultiplierAssembly, Finset.sum_congr rfl fun blockLabel _ => hscale blockLabel]
  ext rowIndex colIndex
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply,
    chartTwoBlockUniformSupport, chartTwoBlockUniformMultiplier, Matrix.of_apply,
    chartTwoBlockPairAxis, Fin.sum_univ_two]
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num

/-- **THE UNIFORM DATUM.**  Rank two, four atoms, `value = -1/4 = -1/size`, two
complementary blocks, uniform weights, assembly `1/4` inside the blocks. -/
theorem chartTwoBlockUniformProjection_isChartStationaryData :
    IsChartStationaryData 2 chartTwoBlockUniformProjection chartTwoBlockUniformWeight
      (-(4 : ℝ)⁻¹) (Finset.univ : Finset (Fin 2)) chartTwoBlockUniformSubset
      chartTwoBlockUniformMultiplierWeight chartTwoBlockUniformTightDir where
  isSymmetric := chartTwoBlockUniformProjection_transpose
  isIdempotent := chartTwoBlockUniformProjection_mul_self
  hasTraceRank := by
    show ∑ atomIndex : Fin 4, chartTwoBlockUniformProjection atomIndex atomIndex = ((2 : ℕ) : ℝ)
    rw [Fin.sum_univ_four]
    norm_num [chartTwoBlockUniformProjection]
  weight_pos := by intro atomIndex; norm_num [chartTwoBlockUniformWeight]
  weight_sum_one := by norm_num [chartTwoBlockUniformWeight, Fin.sum_univ_four]
  activeWeight_nonneg := by intro blockLabel _; norm_num [chartTwoBlockUniformMultiplierWeight]
  activeWeight_sum_one := by
    norm_num [chartTwoBlockUniformMultiplierWeight, Fin.sum_univ_two]
  activeSubset_card := by intro blockLabel _; fin_cases blockLabel <;> decide
  tightDir_unit := by
    intro blockLabel _
    have hinvRoot : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
      rw [← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [chartTwoBlockUniformTightDir, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, hinvRoot, chartTwoBlockUniformSupport_dotProduct_self]
    norm_num
  tightDir_support := by
    intro blockLabel _ atomIndex hnotMem
    rw [chartTwoBlockUniformTightDir, Pi.smul_apply, chartTwoBlockUniformSupport,
      if_neg (chartTwoBlockUniformAxis_ne_of_notMem blockLabel atomIndex hnotMem), smul_zero]
  tightDir_isTight := by
    intro blockLabel _ atomIndex hmem
    rw [chartTwoBlockUniformTightDir, Matrix.mulVec_smul, Pi.smul_apply,
      chartTwoBlockUniformGap_mulVec_support blockLabel atomIndex hmem, Pi.smul_apply,
      chartTwoBlockUniformSupport,
      if_pos (chartTwoBlockUniformAxis_of_mem blockLabel atomIndex hmem)]
    simp only [smul_eq_mul]
    ring
  assembly_diagonal := by
    intro atomIndex
    rw [chartTwoBlockUniformMultiplierAssembly_eq, chartTwoBlockUniformMultiplier,
      Matrix.of_apply, if_pos rfl]
    norm_num
  assembly_commutes := by
    rw [chartTwoBlockUniformMultiplierAssembly_eq]
    ext rowIndex colIndex
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [chartTwoBlockUniformProjection, chartTwoBlockUniformMultiplier,
        chartTwoBlockPairAxis, Fin.ext_iff]

/-- The uniform family is two complementary blocks, `{0,1}` and `{2,3}`. -/
theorem chartTwoBlockUniform_isChartTwoBlockFamily :
    IsChartTwoBlockFamily (Finset.univ : Finset (Fin 2)) chartTwoBlockUniformSubset
      ({0, 1} : Finset (Fin 4)) := by
  intro blockLabel _
  fin_cases blockLabel <;> simp only [chartTwoBlockUniformSubset] <;> decide

/-- **A CHART STATIONARITY DATUM WITH A NEGATIVE VALUE EXISTS**, at
`value = -1/size` exactly — the floor of
`Gtz.neg_inv_size_le_value_of_isChartStationaryData`.

Consequence for the sibling module:
`Gtz.not_isChartStationaryData_of_value_eq_neg_inv_size` excludes exactly this
value, and it can only do so because it carries `Gtz.IsChartArgmaxValue`.  This
witness is the mechanized reason that hypothesis is not decoration. -/
theorem exists_isChartStationaryData_value_eq_neg_inv_size :
    ∃ (projection : Matrix (Fin 4) (Fin 4) ℝ) (weight : Fin 4 → ℝ)
      (activeSubset : Fin 2 → Finset (Fin 4)) (activeWeight : Fin 2 → ℝ)
      (tightDir : Fin 2 → (Fin 4 → ℝ)),
      IsChartStationaryData 2 projection weight (-(4 : ℝ)⁻¹) (Finset.univ : Finset (Fin 2))
        activeSubset activeWeight tightDir :=
  ⟨chartTwoBlockUniformProjection, chartTwoBlockUniformWeight, chartTwoBlockUniformSubset,
    chartTwoBlockUniformMultiplierWeight, chartTwoBlockUniformTightDir,
    chartTwoBlockUniformProjection_isChartStationaryData⟩

/-- **THE DISTINCTNESS HYPOTHESIS CANNOT BE DROPPED.**  Two complementary blocks
alone do NOT force a nonnegative value: the uniform witness has every equation of
the bundle, the two-block structure, and `value = -1/4`.

So `zero_le_value_of_isChartTwoBlockFamily` is sharp in its hypotheses, the
repeated-weight branch this file declares out of scope is INHABITED, and no later
edit may silently delete the two `HasDistinctWeightsOn` arguments without tripping
this theorem. -/
theorem not_forall_zero_le_value_of_isChartTwoBlockFamily :
    ¬ ∀ (size rank : ℕ) (blockIndex : Type) (projection : Matrix (Fin size) (Fin size) ℝ)
        (weight : Fin size → ℝ) (value : ℝ) (activeSet : Finset blockIndex)
        (activeSubset : blockIndex → Finset (Fin size)) (activeWeight : blockIndex → ℝ)
        (tightDir : blockIndex → (Fin size → ℝ)) (chosenSubset : Finset (Fin size)),
        IsChartStationaryData rank projection weight value activeSet activeSubset activeWeight
            tightDir →
          IsChartTwoBlockFamily activeSet activeSubset chosenSubset → 0 ≤ value := by
  intro hbound
  have huniform := hbound 4 2 (Fin 2) chartTwoBlockUniformProjection chartTwoBlockUniformWeight
    (-(4 : ℝ)⁻¹) (Finset.univ : Finset (Fin 2)) chartTwoBlockUniformSubset
    chartTwoBlockUniformMultiplierWeight chartTwoBlockUniformTightDir ({0, 1} : Finset (Fin 4))
    chartTwoBlockUniformProjection_isChartStationaryData
    chartTwoBlockUniform_isChartTwoBlockFamily
  norm_num at huniform

end Gtz
