/-
# The layer window, read in the polarity the campaign can consume

The `(6,3)` layer aggregate `sum_{|C|=3} det(S_C - 1)` and its Gale-dual reweighting
`sum_{|C|=3} (prod_{c in C} t_c/(1-t_c)) det(S_C - 1)` have been used in ONE direction:
domination of all twenty triples forces the aggregate nonnegative, so a negative aggregate
refutes "all twenty dominate".  That direction is polarity-dead for GTZ.  `GtzWeighted 6 3`
asks for SOME dominating triple; a counterexample has NONE, and therefore satisfies
"not all twenty dominate" outright.  The no-go's conclusion is a CONSEQUENCE of the
counterexample hypothesis, so the two can never be combined.  This is
`forall_dominates_refuted_by_crux` below, and the campaign's own `-56` docstring says the
same thing in prose: the functional carries zero information, it is a no-go not a step.

This file turns the same aggregate around.  The consumable shapes are
`exists selected, selected.card = 3 and (subsetSum design selected - 1).PosDef` (which
refutes `IsTie` through its second clause, hence feeds `HingeHoldsAtSize`) and
`exists selected, selected.card = 3 and Dominates design selected` (which is
`GtzWeighted 6 3` at that design).  Both are reached here from a layer aggregate that is
STRICTLY POSITIVE -- the opposite sign to the one the shipped no-goes exploit.

    `exists_posDef_gap_of_weightedLayerSum_pos`
    `not_isTie_of_weightedLayerSum_pos`
    `exists_dominates_of_weightedLayerSum_pos`

## Why the sign flips, and what the side conditions are for

A positive aggregate of the twenty gap determinants, under ANY strictly positive cell
weights, forces at least one gap determinant strictly positive.  A `3 x 3` real symmetric
matrix with positive determinant is either positive definite or has exactly two negative
eigenvalues; the second alternative is excluded by the trace and the second invariant, so
`trace > 0`, `secondInvariant > 0`, `det > 0` is exactly positive definiteness
(`posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos`, proved by evaluating the
characteristic polynomial at a nonpositive eigenvalue).  That is the whole bridge, and it
is why the useful sign is the positive one: only a positive determinant can be upgraded.

## The cell weights are arbitrary, so both windows are instances

`exists_det_pos_of_weightedLayerSum_pos` takes an arbitrary strictly positive
`cellWeight`.  Taking `cellWeight = 1` gives the primal layer window; taking
`cellWeight C = prod_{c in C} t_c / (1 - t_c)` gives the Gale-dual window with its sign
reversed, since the shipped per-cell bridge reads
`det(R_C - 1) = -(prod_{c in C} t_c/s_c) * det(S_C - 1)` at rank three.  So the dual
window is useful exactly when it is NEGATIVE, and the shipped no-go exploits it when it is
POSITIVE; the two directions are disjoint.

## Where the instrument is provably silent

On the uniform slice the primal aggregate is the design-blind `-56`, so the positive-sign
hypothesis is unsatisfiable there: `not_layerWindow_pos_of_uniform_weights`.  Dually the
uniform Gale-dual window is `+56/125`, which is the useless sign.  The instrument is
therefore blind on exactly the stratum the aggregates were designed to kill -- stated here
as a theorem rather than left as an expectation.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Reduction.ExchangeInvariant
import Gtz.Certificates.ResidueDissolution
import Gtz.Quantitative.ChartHadamard
import Gtz.Design.StressFreeNormalizer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## The second invariant of a three-by-three matrix

The middle coefficient of the characteristic polynomial: the total of the three
`2 x 2` principal minors.  Written out on entries so that the characteristic identity
below is a `ring` step and no spectral machinery is needed to state it. -/

/-- **The second invariant** `e_2` of a `3 x 3` matrix: the total of its three `2 x 2`
principal minors.  For a symmetric matrix this is the sum of the pairwise products of
the eigenvalues. -/
def secondInvariantOfThree (form : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (form 0 0 * form 1 1 - form 0 1 * form 1 0)
    + (form 0 0 * form 2 2 - form 0 2 * form 2 0)
    + (form 1 1 * form 2 2 - form 1 2 * form 2 1)

/-- **The characteristic cubic on entries.**  For every `3 x 3` real matrix and every
real point,

    `det(point * 1 - M) = point^3 - tr M * point^2 + e_2(M) * point - det M` .

No symmetry, no positivity: this is the expansion of a `3 x 3` determinant. -/
theorem det_scalar_sub_eq_characteristicCubic (form : Matrix (Fin 3) (Fin 3) ℝ)
    (point : ℝ) :
    (Matrix.scalar (Fin 3) point - form).det
      = point ^ 3 - Matrix.trace form * point ^ 2
        + secondInvariantOfThree form * point - form.det := by
  have hdiagonal : ∀ index : Fin 3,
      (Matrix.scalar (Fin 3) point - form) index index = point - form index index := by
    intro index
    simp [Matrix.scalar_apply]
  have hoffDiagonal : ∀ rowIndex colIndex : Fin 3, rowIndex ≠ colIndex →
      (Matrix.scalar (Fin 3) point - form) rowIndex colIndex
        = - form rowIndex colIndex := by
    intro rowIndex colIndex hdistinct
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hdistinct]
  have hzeroZero := hdiagonal 0
  have honeOne := hdiagonal 1
  have htwoTwo := hdiagonal 2
  have hzeroOne := hoffDiagonal 0 1 (by decide)
  have hzeroTwo := hoffDiagonal 0 2 (by decide)
  have honeZero := hoffDiagonal 1 0 (by decide)
  have honeTwo := hoffDiagonal 1 2 (by decide)
  have htwoZero := hoffDiagonal 2 0 (by decide)
  have htwoOne := hoffDiagonal 2 1 (by decide)
  simp only [Matrix.det_fin_three, Matrix.trace_fin_three, secondInvariantOfThree,
    hzeroZero, honeOne, htwoTwo, hzeroOne, hzeroTwo, honeZero, honeTwo, htwoZero, htwoOne]
  ring

/-- **THE INERTIA BRIDGE.**  A real symmetric `3 x 3` matrix whose trace, second
invariant and determinant are all strictly positive is positive definite.

This is the step that makes a determinant sign usable.  A positive determinant leaves two
possibilities for a symmetric `3 x 3` matrix -- all three eigenvalues positive, or exactly
two negative -- and the trace and the second invariant rule the second one out.  The proof
is Descartes on the characteristic cubic: at a nonpositive point every term of
`point^3 - tr * point^2 + e_2 * point - det` is nonpositive and the last is strictly
negative, so the cubic cannot vanish there, so no eigenvalue is nonpositive. -/
theorem posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hhermitian : form.IsHermitian)
    (htrace : 0 < Matrix.trace form) (hsecond : 0 < secondInvariantOfThree form)
    (hdet : 0 < form.det) :
    form.PosDef := by
  rw [hhermitian.posDef_iff_eigenvalues_pos]
  intro index
  by_contra hnotpositive
  push Not at hnotpositive
  have hroot : form.charpoly.eval (hhermitian.eigenvalues index) = 0 := by
    rw [hhermitian.charpoly_eq, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ index) (by simp)
  rw [Matrix.eval_charpoly, det_scalar_sub_eq_characteristicCubic] at hroot
  have hsquareNonneg : 0 ≤ hhermitian.eigenvalues index ^ 2 := sq_nonneg _
  have hcubeNonpos : hhermitian.eigenvalues index ^ 3 ≤ 0 := by nlinarith
  have hquadNonneg : 0 ≤ Matrix.trace form * hhermitian.eigenvalues index ^ 2 :=
    mul_nonneg htrace.le hsquareNonneg
  have hlinearNonpos :
      secondInvariantOfThree form * hhermitian.eigenvalues index ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hsecond.le hnotpositive
  linarith

/-! ## A strictly positive layer aggregate forces one strictly positive gap determinant

The cell weights are arbitrary and strictly positive, so this covers the primal window
(`cellWeight = 1`) and the Gale-dual window (`cellWeight C = prod t_c / (1 - t_c)`) in one
statement, and any future reweighting as well. -/

/-- **A POSITIVE WEIGHTED LAYER AGGREGATE PRODUCES A POSITIVE GAP DETERMINANT.**  If the
twenty gap determinants, combined with arbitrary strictly positive cell weights, total
something strictly positive, then at least one of them is strictly positive.  Nothing but
the sign of the weights is used. -/
theorem exists_det_pos_of_weightedLayerSum_pos {size : ℕ} (design : WeightedDesign size 3)
    (cellWeight : Finset (Fin size) → ℝ)
    (hcellPositive : ∀ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard 3,
      0 < cellWeight selected)
    (hlayer : 0 < ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard 3,
      cellWeight selected * (subsetSum design selected - 1).det) :
    ∃ selected : Finset (Fin size), selected.card = 3
      ∧ 0 < (subsetSum design selected - 1).det := by
  by_contra hnone
  push Not at hnone
  have hnonpositive : ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard 3,
      cellWeight selected * (subsetSum design selected - 1).det ≤ 0 :=
    Finset.sum_nonpos fun selected hmember =>
      mul_nonpos_of_nonneg_of_nonpos (hcellPositive selected hmember).le
        (hnone selected (Finset.mem_powersetCard.mp hmember).2)
  linarith

/-! ## The signature stratum

The upgrade from a positive determinant to positive definiteness needs to know that the
triple is not of signature `(+,-,-)`.  Stated as a condition on the design it is weak: it
constrains only those triples whose gap determinant is already positive, and it is exactly
the statement that on this design a positive gap determinant IS strict domination. -/

/-- **NO TRIPLE HAS A TWO-NEGATIVE GAP.**  Every triple whose gap determinant is strictly
positive has positive trace and positive second invariant as well -- equivalently, no gap
carries the signature `(+,-,-)`, so on such a design the determinant test for strict
domination is exact rather than merely necessary.

This is the only side condition the window instrument needs, and it is a genuine
restriction: the gap `diag(2, -1/2, -1/2)` has positive determinant, positive trace and
negative second invariant. -/
def hasNoTwoNegativeGapTriple (design : WeightedDesign 6 3) : Prop :=
  ∀ selected : Finset (Fin 6), selected.card = 3 →
    0 < (subsetSum design selected - 1).det →
      0 < Matrix.trace (subsetSum design selected - 1)
        ∧ 0 < secondInvariantOfThree (subsetSum design selected - 1)

/-- On a design free of two-negative gaps, a positive gap determinant IS strict
domination. -/
theorem posDef_gap_of_det_pos_of_hasNoTwoNegativeGapTriple {design : WeightedDesign 6 3}
    (hstratum : hasNoTwoNegativeGapTriple design) {selected : Finset (Fin 6)}
    (hcard : selected.card = 3) (hdet : 0 < (subsetSum design selected - 1).det) :
    (subsetSum design selected - 1).PosDef :=
  posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos
    (isHermitian_subsetSum_sub_one design selected)
    (hstratum selected hcard hdet).1 (hstratum selected hcard hdet).2 hdet

/-! ## The instrument, in the three shapes the campaign consumes -/

/-- **THE RIGHT-POLARITY WINDOW INSTRUMENT.**  A `(6,3)` design free of two-negative gaps
whose weighted layer aggregate is strictly positive carries a STRICTLY dominating triple.

The aggregate hypothesis is the layer window read with the sign OPPOSITE to the one the
shipped no-goes exploit. -/
theorem exists_posDef_gap_of_weightedLayerSum_pos (design : WeightedDesign 6 3)
    (hstratum : hasNoTwoNegativeGapTriple design)
    (cellWeight : Finset (Fin 6) → ℝ)
    (hcellPositive : ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      0 < cellWeight selected)
    (hlayer : 0 < ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      cellWeight selected * (subsetSum design selected - 1).det) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  obtain ⟨selected, hcard, hdet⟩ :=
    exists_det_pos_of_weightedLayerSum_pos design cellWeight hcellPositive hlayer
  exact ⟨selected, hcard,
    posDef_gap_of_det_pos_of_hasNoTwoNegativeGapTriple hstratum hcard hdet⟩

/-- **THE TIE IS REFUTED.**  `IsTie` asserts that no triple dominates strictly, so a
strictly dominating triple kills it outright.  This is the shape `HingeHoldsAtSize 6 3`
consumes. -/
theorem not_isTie_of_weightedLayerSum_pos (design : WeightedDesign 6 3)
    (hstratum : hasNoTwoNegativeGapTriple design)
    (cellWeight : Finset (Fin 6) → ℝ)
    (hcellPositive : ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      0 < cellWeight selected)
    (hlayer : 0 < ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      cellWeight selected * (subsetSum design selected - 1).det) :
    ¬ IsTie design := by
  intro htie
  obtain ⟨selected, hcard, hposDef⟩ :=
    exists_posDef_gap_of_weightedLayerSum_pos design hstratum cellWeight hcellPositive hlayer
  exact htie.2 selected hcard hposDef

/-- **GTZ HOLDS AT THE DESIGN.**  Strict domination weakens to `Dominates`, which is
`GtzWeighted 6 3` evaluated at this design. -/
theorem exists_dominates_of_weightedLayerSum_pos (design : WeightedDesign 6 3)
    (hstratum : hasNoTwoNegativeGapTriple design)
    (cellWeight : Finset (Fin 6) → ℝ)
    (hcellPositive : ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      0 < cellWeight selected)
    (hlayer : 0 < ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      cellWeight selected * (subsetSum design selected - 1).det) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected := by
  obtain ⟨selected, hcard, hposDef⟩ :=
    exists_posDef_gap_of_weightedLayerSum_pos design hstratum cellWeight hcellPositive hlayer
  exact ⟨selected, hcard, hposDef.posSemidef⟩

/-! ### The two named instances

The primal window is the constant cell weight; the Gale-dual window is the cell weight
`prod_{c in C} t_c / (1 - t_c)`, strictly positive because weights lie strictly between
zero and one. -/

/-- The Gale-dual cell weight `prod_{c in C} t_c / (1 - t_c)` is strictly positive on every
subset of a design with at least two atoms. -/
theorem galeDualCellWeight_pos {size rank : ℕ} (design : WeightedDesign size rank)
    (hsize : 2 ≤ size) (selected : Finset (Fin size)) :
    0 < ∏ atomIndex ∈ selected,
      design.weight atomIndex / (1 - design.weight atomIndex) :=
  Finset.prod_pos fun atomIndex _ =>
    div_pos (design.weight_pos atomIndex)
      (sub_pos.mpr (weight_lt_one design hsize atomIndex))

/-- **THE PRIMAL LAYER WINDOW, RIGHT POLARITY.**  Constant cell weight. -/
theorem exists_dominates_of_layerWindow_pos (design : WeightedDesign 6 3)
    (hstratum : hasNoTwoNegativeGapTriple design)
    (hlayer : 0 < ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (subsetSum design selected - 1).det) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected := by
  refine exists_dominates_of_weightedLayerSum_pos design hstratum (fun _ => 1)
    (fun _ _ => one_pos) ?_
  simpa using hlayer

/-- **THE GALE-DUAL WINDOW, RIGHT POLARITY.**  The aggregate
`sum_C (prod_{c in C} t_c/s_c) det(S_C - 1)` is MINUS the Gale-dual window at rank three,
so this hypothesis says the dual window is strictly NEGATIVE -- the opposite sign to the
one `galeDualWindow_nonpos_of_forall_dominates` exploits. -/
theorem exists_dominates_of_galeDualLayerSum_pos (design : WeightedDesign 6 3)
    (hstratum : hasNoTwoNegativeGapTriple design)
    (hlayer : 0 < ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (∏ atomIndex ∈ selected,
        design.weight atomIndex / (1 - design.weight atomIndex))
      * (subsetSum design selected - 1).det) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected :=
  exists_dominates_of_weightedLayerSum_pos design hstratum
    (fun selected => ∏ atomIndex ∈ selected,
      design.weight atomIndex / (1 - design.weight atomIndex))
    (fun selected _ => galeDualCellWeight_pos design (by norm_num) selected)
    hlayer

/-! ## The polarity diagnosis, mechanized

Why the shipped direction cannot advance the conjecture, stated so it can be checked
rather than argued. -/

/-- **THE NO-GO'S CONCLUSION IS IMPLIED BY BEING A COUNTEREXAMPLE.**  A design with no
dominating triple at all -- the only thing that could refute `GtzWeighted 6 3` -- already
fails "all twenty triples dominate".  So every theorem of the shape
`(all twenty dominate) -> False` is satisfied vacuously by every counterexample candidate
and can never be combined with the counterexample hypothesis to derive anything.  The
quantifiers point opposite ways: the conjecture needs SOME triple, the no-go constrains
ALL of them. -/
theorem forall_dominates_refuted_by_crux (design : WeightedDesign 6 3)
    (hnoDominatingTriple : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ Dominates design selected) :
    ¬ ∀ selected : Finset (Fin 6), selected.card = 3 → Dominates design selected :=
  fun hall => hnoDominatingTriple {0, 1, 2} (by decide) (hall {0, 1, 2} (by decide))

/-- The same point with the no-go supplied as a hypothesis: knowing
`(all twenty dominate) -> False` adds nothing to a counterexample, because the
counterexample proves that implication by itself. -/
theorem noGo_carries_no_information_against_crux (design : WeightedDesign 6 3)
    (hnoDominatingTriple : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ Dominates design selected) :
    ((∀ selected : Finset (Fin 6), selected.card = 3 → Dominates design selected) → False) :=
  forall_dominates_refuted_by_crux design hnoDominatingTriple

/-- **THE INSTRUMENT IS BLIND ON THE UNIFORM SLICE**, and provably so.  The primal layer
aggregate there is the design-blind `-56`, so its positive-sign hypothesis is
unsatisfiable: the uniform stratum is exactly where the aggregate was designed to fire in
the useless direction, and it is exactly where the useful direction cannot fire.  Dually
the uniform Gale-dual window is `+56/125`, again the useless sign. -/
theorem not_layerWindow_pos_of_uniform_weights (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = ((6 : ℝ))⁻¹) :
    ¬ (0 < ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        (subsetSum design selected - 1).det) := by
  rw [sum_det_subsetSum_sub_one_sixThree design huniform]
  norm_num

end Gtz
