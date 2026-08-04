/-
# The index floor on the argmax family

`Gtz.Quantitative.ChartSecondOrder` derives the weight-slice second-order condition at a
`(6,3)` crux and then says, in its own words, what it cannot do: turning that condition
into `5 <= |A|` "needs, on top of what is here, that a real vector space is not a finite
union of proper subspaces, plus the support analysis of the tight vectors".
`Gtz.Quantitative.ChartSecondOrderStep` repeats the same reservation twice.  This file
supplies both missing ingredients and lands the floor.

## Where the union-of-subspaces lemma lives

It is in Mathlib, and it was not missing but unlocated:
`Subspace.exists_eq_top_of_iUnion_eq_univ` in `Mathlib/GroupTheory/CosetCover.lean`, stated
for a vector space over an INFINITE division ring.  `Gtz.exists_le_of_forall_exists_mem`
packages it in the form a covering argument consumes -- a submodule each of whose members
lies in one of finitely many submodules lies wholly inside one of them -- by transporting
the cover into the submodule itself.  Nothing about the real numbers is used beyond
`Infinite`, so the packaging is generic.

## The counting, in one paragraph

Write `A` for the argmax family and, for each of its blocks, `w_C` for the EIGEN-SQUARE ROW
of that block -- the vector whose dot product against a weight direction is the direction's
first-order effect there (`Gtz.eigenSquareRow`, shipped).  Call a direction FLAT when every
`w_C` annihilates it.

* THE MULTIPLIER LAYER MAKES THE SIMPLEX CONSTRAINT FREE.  Stationarity in the weights says
  the multiplier assembly has constant diagonal `1/6`, which in the eigen-square vocabulary
  is `sum over C in A of mu_C * w_C = (1/6) * 1`: the ALL-ONES vector lies in the span of the
  rows.  So a flat direction automatically sums to zero and stays inside the simplex
  (`Gtz.sum_eq_zero_of_flat_of_assemblyDiagonal`).  That is worth exactly one step of the
  count, and it is the difference between the two floors below.
* TWO FLAT DIRECTIONS, SEPARATED.  Fewer rows than atoms leave a nonzero flat direction;
  one row fewer still leaves a second one that vanishes at a coordinate where the first does
  not (`Gtz.exists_flatPair_of_card_add_one_lt`).  The separating coordinate is what makes
  them independent, concretely and without any rank computation.
* THE COVERING.  Every flat direction vanishes on SOME argmax block -- that is the shipped
  second-order escape read through full support.  The flat directions form a submodule, the
  directions vanishing on a block form a submodule, and the union-of-subspaces lemma upgrades
  "each one vanishes somewhere" to "they ALL vanish on one common block".
* THE KILL.  Three atoms are left outside that block.  A flat direction supported on them
  obeys two independent linear conditions -- it sums to zero, and it is annihilated by the row
  of any THIRD argmax block, which is non-constant there because its own block is neither the
  common one nor its complement.  So at most a line survives, and the two separated directions
  cannot both live on it.

The third block exists because the shipped `Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily`
already puts three blocks in the family, and `{C_0, C_0 complement}` has only two members.
The proof therefore CONSUMES the shipped floor rather than replacing it.

## What is proved, and at what strength

* `Gtz.SixThreeCrux.four_le_card_chartArgmaxFamily_of_fullSupport` -- the floor from the
  second-order condition ALONE, with no multiplier input.
* `Gtz.SixThreeCrux.five_le_card_chartArgmaxFamily_of_assemblyDiagonal` -- the floor with the
  multiplier layer threaded in.  This is the headline, and the gap between the two is exactly
  what the assembly's constant diagonal buys.

Both carry the hypotheses the shipped escape carries: a unit tight eigenvector at EVERY one
of the twenty triples (the inactive blocks are held by the Rayleigh bound, so they need one
too), and FULL SUPPORT of those eigenvectors.  Neither is decoration.  Full support is what
turns "the restricted diagonal annihilates the tight vector" into "the direction vanishes on
the block"; a tight vector with a zero coordinate weakens the vanishing set and, with it, the
count.  The honest ladder is `|A| >= 2 + s` where `s` is the size of the smallest tight
support, and only the case `s = 3` is proved here.

## What is NOT here, stated rather than hidden

* THE SUPPORT-TWO RUNG.  At `s = 2` the same argument yields `4` instead of `5`, but not by
  the same proof: the kill then leaves a PLANE rather than a line, so the contradiction needs
  three independent flat directions instead of two, and a rank-two kill instead of the
  two-atom one below.  Neither is built here.  Note the multiplier-free floor of four proved
  below is a DIFFERENT statement -- it still assumes full support -- and does not cover it.
* THE MEASURED FLOOR IS SIX, NOT EIGHT.  An earlier reading of the numerical record put it
  at eight -- no admissible chart-stationary point with fewer than eight argmax blocks --
  and the record refutes that reading.  The fifteen refined census points ARE admissible
  chart-stationary points, and their argmax families have size exactly six at five of them
  and seven at the other ten: every weight positive, every multiplier nonnegative, Parseval
  to four hundred digits, and each declared family equal to its own measured argmax set.
  So the measured floor is six, the proved floor below is five, and the gap is one rung
  rather than three.  Neither number is assumed anywhere in this file.
  `Gtz.SixThreeCrux.six_le_card_chartArgmaxFamily_of_assemblyDiagonal_of_ne_five` is the only
  place any of it appears, and what it appears as is the explicit hypothesis that the argmax
  family does not have exactly five members, which the file does not discharge.
* A DISCHARGE OF THE MULTIPLIER HYPOTHESIS.  The shipped
  `Gtz.SixThreeCrux.exists_multiplier_isChartStationaryData` supplies an assembly with
  constant diagonal, but for ITS OWN tight directions, and only at the argmax blocks.  The
  escape needs a tight vector at every triple, so the two families are not the same object
  and the theorems below take the assembly identity as a hypothesis.
  `Gtz.assemblyDiagonal_of_isChartStationaryData_of_rowEq` and
  `Gtz.eigenSquareRow_eq_mul_self_of_support` say exactly what compatibility closes the gap:
  the tight vector at an argmax block must be the block restriction of the datum's own tight
  direction there.  At a MULTIPLE least eigenvalue that can fail, which is why it is a
  hypothesis and not a lemma.

THE MECHANISM IS FIELD-BLIND, and this is orientation prose rather than a theorem of this
file.  Every step runs verbatim over the complex numbers with `u u^*` in place of `u u^T`, so
nothing here can close the cell alone; it must be paired with a realness consumer.
-/

import Mathlib
import Gtz.Quantitative.ChartSecondOrderStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## Covering a submodule by finitely many submodules -/

/-- **A SUBMODULE COVERED BY FINITELY MANY SUBMODULES SITS INSIDE ONE OF THEM.**  The
packaging of Mathlib's `Subspace.exists_eq_top_of_iUnion_eq_univ`: transport the cover into
the base submodule, where it becomes a cover of the whole space, and read the conclusion
back.  Only `Infinite ℝ` is used, so this is the general covering principle rather than
anything about real coordinates. -/
theorem exists_le_of_forall_exists_mem {ambient : ℕ} {pieceIndex : Type*} [Finite pieceIndex]
    (base : Submodule ℝ (Fin ambient → ℝ)) (piece : pieceIndex → Submodule ℝ (Fin ambient → ℝ))
    (hcover : ∀ vec ∈ base, ∃ index, vec ∈ piece index) :
    ∃ index, base ≤ piece index := by
  have hunion : (⋃ index, (((piece index).comap base.subtype : Submodule ℝ base) : Set base))
      = Set.univ := by
    refine Set.eq_univ_of_forall fun element => ?_
    obtain ⟨index, hmem⟩ := hcover element.1 element.2
    exact Set.mem_iUnion.mpr ⟨index, hmem⟩
  obtain ⟨index, htop⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hunion
  exact ⟨index, fun vec hmem => Submodule.eq_top_iff'.mp htop ⟨vec, hmem⟩⟩

/-! ## A pair of flat directions, separated by a pivot -/

/-- **TWO FLAT DIRECTIONS, SEPARATED BY A PIVOT COORDINATE.**  One row short of the atom
count leaves a nonzero common annihilator; two rows short leaves a second one that is
additionally killed at a coordinate where the first survives.  The pivot is what makes the
pair independent, and it is produced rather than assumed, so no rank computation enters. -/
theorem exists_flatPair_of_card_add_one_lt {ambient count : ℕ}
    (functional : Fin count → (Fin ambient → ℝ)) (hcount : count + 1 < ambient) :
    ∃ (first second : Fin ambient → ℝ) (pivot : Fin ambient),
      first ≠ 0 ∧ second ≠ 0
        ∧ (∀ label, functional label ⬝ᵥ first = 0)
        ∧ (∀ label, functional label ⬝ᵥ second = 0)
        ∧ first pivot ≠ 0 ∧ second pivot = 0 := by
  classical
  obtain ⟨first, hfirstNe, hfirstFlat⟩ :=
    exists_ne_zero_forall_dotProduct_eq_zero_of_card_lt functional (by omega)
  obtain ⟨pivot, hpivotRaw⟩ := Function.ne_iff.mp hfirstNe
  rw [Pi.zero_apply] at hpivotRaw
  obtain ⟨second, hsecondNe, hsecondFlat⟩ :=
    exists_ne_zero_forall_dotProduct_eq_zero_of_card_lt
      (Fin.cons (Pi.single pivot (1 : ℝ)) functional : Fin (count + 1) → (Fin ambient → ℝ))
      hcount
  refine ⟨first, second, pivot, hfirstNe, hsecondNe, hfirstFlat, fun label => ?_, hpivotRaw, ?_⟩
  · have htail := hsecondFlat label.succ
    rwa [Fin.cons_succ] at htail
  · have hhead := hsecondFlat 0
    rw [Fin.cons_zero, single_dotProduct] at hhead
    linarith [hhead]

/-! ## The eigen-square row, off its block and on it -/

/-- The eigen-square row reads off a single squared coordinate at any atom of its block. -/
theorem eigenSquareRow_eq_sq {size rank : ℕ} {selected : Finset (Fin size)}
    (hcard : selected.card = rank) (vec : Fin rank → ℝ) {atomIndex : Fin size}
    {blockIndex : Fin rank} (hindex : selected.orderEmbOfFin hcard blockIndex = atomIndex) :
    eigenSquareRow selected hcard vec atomIndex = vec blockIndex ^ 2 := by
  classical
  rw [eigenSquareRow,
    Finset.sum_eq_single blockIndex
      (fun otherIndex _ hne => if_neg fun hcollide =>
        hne ((selected.orderEmbOfFin hcard).injective (hcollide.trans hindex.symm)))
      (fun hnotMem => absurd (Finset.mem_univ blockIndex) hnotMem),
    if_pos hindex]

/-- The eigen-square row vanishes off its own block: no block index is carried there. -/
theorem eigenSquareRow_eq_zero_of_notMem {size rank : ℕ} {selected : Finset (Fin size)}
    (hcard : selected.card = rank) (vec : Fin rank → ℝ) {atomIndex : Fin size}
    (hnotMem : atomIndex ∉ selected) :
    eigenSquareRow selected hcard vec atomIndex = 0 := by
  refine Finset.sum_eq_zero fun blockIndex _ => ?_
  refine if_neg fun hcollide => hnotMem ?_
  exact hcollide ▸ selected.orderEmbOfFin_mem hcard blockIndex

/-- **ON ITS OWN BLOCK A FULL-SUPPORT EIGEN-SQUARE ROW IS STRICTLY POSITIVE.**  This is the
whole use of full support in the counting: it separates the row's values on the block from
its values off the block, which is what makes a third block's row non-constant. -/
theorem eigenSquareRow_pos_of_mem {size rank : ℕ} {selected : Finset (Fin size)}
    (hcard : selected.card = rank) {vec : Fin rank → ℝ}
    (hfullSupport : ∀ blockIndex : Fin rank, vec blockIndex ≠ 0) {atomIndex : Fin size}
    (hmem : atomIndex ∈ selected) :
    0 < eigenSquareRow selected hcard vec atomIndex := by
  classical
  have hpreimage : atomIndex ∈ Set.range (selected.orderEmbOfFin hcard) := by
    rw [Finset.range_orderEmbOfFin selected hcard]
    exact hmem
  obtain ⟨blockIndex, hblockIndex⟩ := hpreimage
  rw [eigenSquareRow_eq_sq hcard vec hblockIndex]
  have habs : 0 < |vec blockIndex| := abs_pos.mpr (hfullSupport blockIndex)
  nlinarith [sq_abs (vec blockIndex)]

/-- **THE COMPATIBILITY THE MULTIPLIER LAYER NEEDS.**  When a tight vector is the block
restriction of an AMBIENT vector supported inside the block, its eigen-square row is that
ambient vector's pointwise square.  The multiplier assembly's diagonal is built from exactly
those pointwise squares, so this is the identification that lets one feed the other. -/
theorem eigenSquareRow_eq_mul_self_of_support {size rank : ℕ} {selected : Finset (Fin size)}
    (hcard : selected.card = rank) (ambient : Fin size → ℝ)
    (hsupport : ∀ atomIndex : Fin size, atomIndex ∉ selected → ambient atomIndex = 0)
    (atomIndex : Fin size) :
    eigenSquareRow selected hcard
        (fun blockIndex => ambient (selected.orderEmbOfFin hcard blockIndex)) atomIndex
      = ambient atomIndex * ambient atomIndex := by
  classical
  by_cases hmem : atomIndex ∈ selected
  · have hpreimage : atomIndex ∈ Set.range (selected.orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin selected hcard]
      exact hmem
    obtain ⟨blockIndex, hblockIndex⟩ := hpreimage
    rw [eigenSquareRow_eq_sq hcard _ hblockIndex, hblockIndex]
    ring
  · rw [eigenSquareRow_eq_zero_of_notMem hcard _ hmem, hsupport atomIndex hmem, mul_zero]

/-- The eigen-square row of a block, made TOTAL in the block so that it can be summed over a
family without carrying a cardinality proof.  On a block of the right size it is the shipped
`Gtz.eigenSquareRow`; elsewhere it is zero and never consulted. -/
noncomputable def totalEigenSquareRow {size rank : ℕ}
    (tightVec : Finset (Fin size) → (Fin rank → ℝ)) (selected : Finset (Fin size)) :
    Fin size → ℝ :=
  if hcard : selected.card = rank then eigenSquareRow selected hcard (tightVec selected) else 0

theorem totalEigenSquareRow_of_card {size rank : ℕ}
    (tightVec : Finset (Fin size) → (Fin rank → ℝ)) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) :
    totalEigenSquareRow tightVec selected = eigenSquareRow selected hcard (tightVec selected) :=
  dif_pos hcard

/-- **ANNIHILATION FORCES VANISHING WHEREVER THE TIGHT VECTOR SURVIVES.**  The pointwise form
of the shipped `Gtz.eq_zero_of_submatrix_diagonal_mulVec_eq_zero`, which asks for FULL support
and concludes at every atom of the block.  Stated this way it shows precisely what full
support is worth: the vanishing set of a flat direction is the SUPPORT of the tight vector,
not the whole block, and the ladder `|A| >= 2 + s` reads that support size off directly. -/
theorem eq_zero_of_submatrix_diagonal_mulVec_eq_zero_of_ne {size rank : ℕ}
    (direction : Fin size → ℝ) {selected : Finset (Fin size)} (hcard : selected.card = rank)
    {vec : Fin rank → ℝ}
    (hannihilated : (Matrix.diagonal direction).submatrix (selected.orderEmbOfFin hcard)
      (selected.orderEmbOfFin hcard) *ᵥ vec = 0)
    {blockIndex : Fin rank} (hne : vec blockIndex ≠ 0) :
    direction (selected.orderEmbOfFin hcard blockIndex) = 0 := by
  rw [submatrix_diagonal_orderEmbOfFin] at hannihilated
  have hcoordinate := congrFun hannihilated blockIndex
  rw [Matrix.mulVec_diagonal, Pi.zero_apply] at hcoordinate
  exact (mul_eq_zero.mp hcoordinate).resolve_right hne

/-! ## The multiplier layer: flatness already forces the sum to vanish -/

/-- **THE ASSEMBLY DIAGONAL, READ IN THE EIGEN-SQUARE VOCABULARY.**  The shipped
`assembly_diagonal` field says the multiplier assembly has constant diagonal `1/size`; by
`Gtz.chartMultiplierAssembly_apply` that is a statement about the pointwise squares of the
datum's tight directions, so any row family agreeing with those squares inherits it. -/
theorem assemblyDiagonal_of_isChartStationaryData_of_rowEq {size rank : ℕ}
    {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ} {value : ℝ}
    {activeSet : Finset (Finset (Fin size))} {multiplier : Finset (Fin size) → ℝ}
    {selection : Finset (Fin size) → (Fin size → ℝ)}
    (hdata : IsChartStationaryData rank projection weight value activeSet
      (id : Finset (Fin size) → Finset (Fin size)) multiplier selection)
    (row : Finset (Fin size) → (Fin size → ℝ))
    (hrow : ∀ selected ∈ activeSet, ∀ atomIndex : Fin size,
      row selected atomIndex = selection selected atomIndex * selection selected atomIndex)
    (atomIndex : Fin size) :
    ∑ selected ∈ activeSet, multiplier selected * row selected atomIndex = ((size : ℝ))⁻¹ := by
  rw [← hdata.assembly_diagonal atomIndex, chartMultiplierAssembly_apply]
  exact Finset.sum_congr rfl fun selected hmem => by rw [hrow selected hmem atomIndex]

/-- **THE ALL-ONES VECTOR IS ALREADY IN THE SPAN, SO THE SIMPLEX CONSTRAINT IS FREE.**  A
constant assembly diagonal exhibits the all-ones vector as a multiplier combination of the
rows, and a direction annihilated by every row is therefore annihilated by it too.  This is
the whole contribution of first-order stationarity to the count, and it is worth exactly one
step. -/
theorem sum_eq_zero_of_flat_of_assemblyDiagonal {size : ℕ} (hsize : 0 < size)
    (family : Finset (Finset (Fin size))) (row : Finset (Fin size) → (Fin size → ℝ))
    (multiplier : Finset (Fin size) → ℝ)
    (hassembly : ∀ atomIndex : Fin size,
      ∑ selected ∈ family, multiplier selected * row selected atomIndex = ((size : ℝ))⁻¹)
    {direction : Fin size → ℝ}
    (hflat : ∀ selected ∈ family, row selected ⬝ᵥ direction = 0) :
    ∑ atomIndex, direction atomIndex = 0 := by
  have hsizeNe : ((size : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hsize.ne'
  have hkey : ((size : ℝ))⁻¹ * ∑ atomIndex, direction atomIndex = 0 := by
    calc ((size : ℝ))⁻¹ * ∑ atomIndex, direction atomIndex
        = ∑ atomIndex : Fin size, ((size : ℝ))⁻¹ * direction atomIndex := Finset.mul_sum _ _ _
      _ = ∑ atomIndex : Fin size,
            (∑ selected ∈ family, multiplier selected * row selected atomIndex)
              * direction atomIndex := by
          refine Finset.sum_congr rfl fun atomIndex _ => ?_
          rw [hassembly atomIndex]
      _ = ∑ atomIndex : Fin size, ∑ selected ∈ family,
            multiplier selected * row selected atomIndex * direction atomIndex :=
          Finset.sum_congr rfl fun atomIndex _ => Finset.sum_mul _ _ _
      _ = ∑ selected ∈ family, ∑ atomIndex : Fin size,
            multiplier selected * row selected atomIndex * direction atomIndex := by
          rw [Finset.sum_comm]
      _ = ∑ selected ∈ family, multiplier selected * (row selected ⬝ᵥ direction) := by
          refine Finset.sum_congr rfl fun selected _ => ?_
          rw [dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun atomIndex _ => by ring
      _ = 0 := by
          refine Finset.sum_eq_zero fun selected hmem => ?_
          rw [hflat selected hmem, mul_zero]
  rcases mul_eq_zero.mp hkey with hzero | hsum
  · exact absurd hzero (inv_ne_zero hsizeNe)
  · exact hsum

/-! ## The two submodules the covering argument compares -/

/-- The directions that are FLAT at every member of a family and sum to zero -- the feasible
weight motions the second-order escape acts on. -/
def flatSumZeroSubmodule {size : ℕ} (family : Finset (Finset (Fin size)))
    (row : Finset (Fin size) → (Fin size → ℝ)) : Submodule ℝ (Fin size → ℝ) where
  carrier := {direction | (∀ selected ∈ family, row selected ⬝ᵥ direction = 0)
    ∧ ∑ atomIndex, direction atomIndex = 0}
  zero_mem' := ⟨fun selected _ => dotProduct_zero _, Finset.sum_const_zero⟩
  add_mem' := by
    rintro left right ⟨hleftFlat, hleftSum⟩ ⟨hrightFlat, hrightSum⟩
    refine ⟨fun selected hmem => ?_, ?_⟩
    · rw [dotProduct_add, hleftFlat selected hmem, hrightFlat selected hmem, add_zero]
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, hleftSum, hrightSum, add_zero]
  smul_mem' := by
    rintro scale direction ⟨hflat, hsum⟩
    refine ⟨fun selected hmem => ?_, ?_⟩
    · rw [dotProduct_smul, hflat selected hmem, smul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum, hsum, mul_zero]

theorem mem_flatSumZeroSubmodule_iff {size : ℕ} (family : Finset (Finset (Fin size)))
    (row : Finset (Fin size) → (Fin size → ℝ)) (direction : Fin size → ℝ) :
    direction ∈ flatSumZeroSubmodule family row
      ↔ (∀ selected ∈ family, row selected ⬝ᵥ direction = 0)
          ∧ ∑ atomIndex, direction atomIndex = 0 :=
  Iff.rfl

/-- The directions that VANISH on a block -- what the second-order escape produces. -/
def vanishingSubmodule {size : ℕ} (block : Finset (Fin size)) : Submodule ℝ (Fin size → ℝ) where
  carrier := {direction | ∀ atomIndex ∈ block, direction atomIndex = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    rintro left right hleft hright atomIndex hmem
    rw [Pi.add_apply, hleft atomIndex hmem, hright atomIndex hmem, add_zero]
  smul_mem' := by
    rintro scale direction hvanish atomIndex hmem
    rw [Pi.smul_apply, hvanish atomIndex hmem, smul_zero]

theorem mem_vanishingSubmodule_iff {size : ℕ} (block : Finset (Fin size))
    (direction : Fin size → ℝ) :
    direction ∈ vanishingSubmodule block ↔ ∀ atomIndex ∈ block, direction atomIndex = 0 :=
  Iff.rfl

/-! ## The kill -/

/-- **THE TWO-ATOM KILL.**  A direction that vanishes on a block of three atoms and at one of
the three atoms outside it lives on the remaining two.  There it obeys two conditions -- it
sums to zero, and it is annihilated by a row taking DIFFERENT values at those two atoms -- and
the pair leaves only the origin.  Purely arithmetic: no eigenvalue, no rank, no dimension. -/
theorem eq_zero_of_vanishing_of_sumZero_of_rowFlat {direction row : Fin 6 → ℝ}
    {block : Finset (Fin 6)} {firstAtom secondAtom thirdAtom : Fin 6}
    (hcompl : blockᶜ = {firstAtom, secondAtom, thirdAtom})
    (hfirstSecond : firstAtom ≠ secondAtom) (hfirstThird : firstAtom ≠ thirdAtom)
    (hsecondThird : secondAtom ≠ thirdAtom)
    (hrowDistinct : row firstAtom ≠ row secondAtom)
    (hvanish : ∀ atomIndex ∈ block, direction atomIndex = 0)
    (hthird : direction thirdAtom = 0)
    (hsum : ∑ atomIndex, direction atomIndex = 0)
    (hrowFlat : row ⬝ᵥ direction = 0) :
    direction = 0 := by
  classical
  have hfirstNotMem : firstAtom ∉ ({secondAtom, thirdAtom} : Finset (Fin 6)) := by
    simp [hfirstSecond, hfirstThird]
  have hsecondNotMem : secondAtom ∉ ({thirdAtom} : Finset (Fin 6)) := by
    simp [hsecondThird]
  have htriple : ∀ scalarOf : Fin 6 → ℝ, ∑ atomIndex ∈ blockᶜ, scalarOf atomIndex
      = scalarOf firstAtom + scalarOf secondAtom + scalarOf thirdAtom := by
    intro scalarOf
    rw [hcompl, Finset.sum_insert hfirstNotMem, Finset.sum_insert hsecondNotMem,
      Finset.sum_singleton, add_assoc]
  have hsumSplit : direction firstAtom + direction secondAtom = 0 := by
    have hsplit := Finset.sum_add_sum_compl block direction
    rw [Finset.sum_eq_zero hvanish, zero_add, htriple direction, hthird, add_zero, hsum] at hsplit
    exact hsplit
  have hrowSplit : row firstAtom * direction firstAtom
      + row secondAtom * direction secondAtom = 0 := by
    have hsplit := Finset.sum_add_sum_compl block fun atomIndex =>
      row atomIndex * direction atomIndex
    rw [Finset.sum_eq_zero fun atomIndex hmem => by rw [hvanish atomIndex hmem, mul_zero],
      zero_add, htriple fun atomIndex => row atomIndex * direction atomIndex, hthird,
      mul_zero, add_zero] at hsplit
    rw [hsplit, ← dotProduct]
    exact hrowFlat
  have hfirstZero : direction firstAtom = 0 := by
    have hsub : (row firstAtom - row secondAtom) * direction firstAtom = 0 := by
      linear_combination hrowSplit - row secondAtom * hsumSplit
    rcases mul_eq_zero.mp hsub with hdiff | hvalue
    · exact absurd (sub_eq_zero.mp hdiff) hrowDistinct
    · exact hvalue
  have hsecondZero : direction secondAtom = 0 := by linarith
  funext atomIndex
  rw [Pi.zero_apply]
  by_cases hmem : atomIndex ∈ block
  · exact hvanish atomIndex hmem
  · have hmemCompl : atomIndex ∈ blockᶜ := Finset.mem_compl.mpr hmem
    rw [hcompl] at hmemCompl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmemCompl
    rcases hmemCompl with rfl | rfl | rfl
    · exact hfirstZero
    · exact hsecondZero
    · exact hthird

/-! ## The covering step at a crux -/

/-- **THE ESCAPE, UPGRADED FROM POINTWISE TO UNIFORM.**  The shipped second-order condition
says each flat direction vanishes on SOME argmax block; the union-of-subspaces lemma says one
block works for ALL of them at once.  That upgrade is the ingredient
`Gtz.Quantitative.ChartSecondOrder` names as missing. -/
theorem SixThreeCrux.exists_argmax_le_vanishingSubmodule (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hfullSupport : ∀ (selected : Finset (Fin 6)) (blockIndex : Fin 3),
      tightVec selected blockIndex ≠ 0) :
    ∃ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      flatSumZeroSubmodule (chartArgmaxFamily (chartPointOfDesign crux.design))
          (totalEigenSquareRow tightVec)
        ≤ vanishingSubmodule block := by
  classical
  obtain ⟨index, hle⟩ := exists_le_of_forall_exists_mem
    (flatSumZeroSubmodule (chartArgmaxFamily (chartPointOfDesign crux.design))
      (totalEigenSquareRow tightVec))
    (fun index : {block // block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)} =>
      vanishingSubmodule index.1)
    (by
      rintro direction ⟨hflat, hsum⟩
      obtain ⟨block, hmem, hvanish⟩ :=
        crux.exists_argmax_direction_eq_zero_of_flatWeightDirection direction hsum tightVec
          hunit hEigen
          (fun selected hcard hmemArgmax => by
            rw [← eigenSquareRow_dotProduct selected hcard (tightVec selected) direction,
              ← totalEigenSquareRow_of_card tightVec hcard]
            exact hflat selected hmemArgmax)
          hfullSupport
      exact ⟨⟨block, hmem⟩, hvanish⟩)
  exact ⟨index.1, index.2, hle⟩

/-! ## The engine -/

/-- **THE CONTRADICTION.**  Two flat directions separated by a pivot coordinate cannot both
exist at a crux.  All four ingredients meet here: the covering puts both on one common argmax
block, the shipped three-block floor supplies a THIRD block whose row is non-constant on the
three atoms left over, and the two-atom kill then leaves no room for a separated pair.  Note
which hypotheses are absent -- no step size, no feasibility, no smallness -- and that the
first direction need not be nonzero: the pivot already does that work. -/
theorem SixThreeCrux.false_of_flatPair (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hfullSupport : ∀ (selected : Finset (Fin 6)) (blockIndex : Fin 3),
      tightVec selected blockIndex ≠ 0)
    {first second : Fin 6 → ℝ} {pivot : Fin 6}
    (hfirstMem : first ∈ flatSumZeroSubmodule
      (chartArgmaxFamily (chartPointOfDesign crux.design)) (totalEigenSquareRow tightVec))
    (hsecondMem : second ∈ flatSumZeroSubmodule
      (chartArgmaxFamily (chartPointOfDesign crux.design)) (totalEigenSquareRow tightVec))
    (hsecondNe : second ≠ 0)
    (hpivotFirst : first pivot ≠ 0) (hpivotSecond : second pivot = 0) :
    False := by
  classical
  set family := chartArgmaxFamily (chartPointOfDesign crux.design) with hfamily
  set flatSpace := flatSumZeroSubmodule family (totalEigenSquareRow tightVec) with hflatSpace
  obtain ⟨baseBlock, hbaseMem, hle⟩ :=
    crux.exists_argmax_le_vanishingSubmodule tightVec hunit hEigen hfullSupport
  have hmemberCard : ∀ block ∈ family, block.card = 3 := fun block hmem =>
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) block).mp hmem).1
  have hbaseCard : baseBlock.card = 3 := hmemberCard baseBlock hbaseMem
  have hcomplCard : baseBlockᶜ.card = 3 := by
    rw [Finset.card_compl, hbaseCard, Fintype.card_fin]
  -- a THIRD argmax block, distinct from the base block and from its complement
  have hthree : 3 ≤ family.card := crux.three_le_card_chartArgmaxFamily
  have hpairCard : ({baseBlock, baseBlockᶜ} : Finset (Finset (Fin 6))).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    rw [Finset.card_singleton]
  have hleftover : (family \ ({baseBlock, baseBlockᶜ} : Finset (Finset (Fin 6)))).Nonempty := by
    refine Finset.card_pos.mp ?_
    have hbound := Finset.le_card_sdiff ({baseBlock, baseBlockᶜ} : Finset (Finset (Fin 6))) family
    omega
  obtain ⟨partner, hpartnerSdiff⟩ := hleftover
  rw [Finset.mem_sdiff] at hpartnerSdiff
  obtain ⟨hpartnerMem, hpartnerNot⟩ := hpartnerSdiff
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpartnerNot
  obtain ⟨hpartnerNeBase, hpartnerNeCompl⟩ := hpartnerNot
  have hpartnerCard : partner.card = 3 := hmemberCard partner hpartnerMem
  set partnerRow := totalEigenSquareRow tightVec partner with hpartnerRow
  have hpartnerRowEq : partnerRow = eigenSquareRow partner hpartnerCard (tightVec partner) :=
    totalEigenSquareRow_of_card tightVec hpartnerCard
  -- the partner row is NON-CONSTANT on the complement of the base block
  have hnotSubBase : ¬ partner ⊆ baseBlock := fun hsub =>
    hpartnerNeBase (Finset.eq_of_subset_of_card_le hsub (by omega))
  obtain ⟨positiveAtom, hpositiveMem, hpositiveNotBase⟩ := Finset.not_subset.mp hnotSubBase
  have hnotSubPartner : ¬ baseBlockᶜ ⊆ partner := fun hsub =>
    hpartnerNeCompl (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  obtain ⟨zeroAtom, hzeroCompl, hzeroNotPartner⟩ := Finset.not_subset.mp hnotSubPartner
  have hpositiveCompl : positiveAtom ∈ baseBlockᶜ := Finset.mem_compl.mpr hpositiveNotBase
  have hpositiveValue : 0 < partnerRow positiveAtom := by
    rw [hpartnerRowEq]
    exact eigenSquareRow_pos_of_mem hpartnerCard (hfullSupport partner) hpositiveMem
  have hzeroValue : partnerRow zeroAtom = 0 := by
    rw [hpartnerRowEq]
    exact eigenSquareRow_eq_zero_of_notMem hpartnerCard (tightVec partner) hzeroNotPartner
  have hrowDistinct : partnerRow positiveAtom ≠ partnerRow zeroAtom := by
    rw [hzeroValue]
    exact ne_of_gt hpositiveValue
  have hatomsDistinct : positiveAtom ≠ zeroAtom := fun hcollide =>
    hrowDistinct (by rw [hcollide])
  -- the third atom of the complement
  have hatomPairCard : ({positiveAtom, zeroAtom} : Finset (Fin 6)).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    rw [Finset.card_singleton]
  have hthirdNonempty : (baseBlockᶜ \ ({positiveAtom, zeroAtom} : Finset (Fin 6))).Nonempty := by
    refine Finset.card_pos.mp ?_
    have hbound := Finset.le_card_sdiff ({positiveAtom, zeroAtom} : Finset (Fin 6)) baseBlockᶜ
    omega
  obtain ⟨thirdAtom, hthirdSdiff⟩ := hthirdNonempty
  rw [Finset.mem_sdiff] at hthirdSdiff
  obtain ⟨hthirdCompl, hthirdNot⟩ := hthirdSdiff
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hthirdNot
  obtain ⟨hthirdNePositive, hthirdNeZeroAtom⟩ := hthirdNot
  have hcomplTriple : baseBlockᶜ = {positiveAtom, zeroAtom, thirdAtom} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro atomIndex hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hpositiveCompl
      · exact hzeroCompl
      · exact hthirdCompl
    · have hcardTriple : ({positiveAtom, zeroAtom, thirdAtom} : Finset (Fin 6)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hatomsDistinct, Ne.symm hthirdNePositive]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hthirdNeZeroAtom]),
          Finset.card_singleton]
      omega
  -- the kill, packaged once for the two directions it is applied to
  have hkill : ∀ direction : Fin 6 → ℝ, direction ∈ flatSpace →
      direction thirdAtom = 0 → direction = 0 := by
    intro direction hmem hthirdZero
    obtain ⟨hflat, hsum⟩ := id hmem
    exact eq_zero_of_vanishing_of_sumZero_of_rowFlat hcomplTriple hatomsDistinct
      (Ne.symm hthirdNePositive) (Ne.symm hthirdNeZeroAtom) hrowDistinct
      (hle hmem) hthirdZero hsum (hflat partner hpartnerMem)
  -- the separating combination
  have hcombinationMem : second thirdAtom • first - first thirdAtom • second ∈ flatSpace :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hfirstMem) (Submodule.smul_mem _ _ hsecondMem)
  have hcombinationThird :
      (second thirdAtom • first - first thirdAtom • second) thirdAtom = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcombinationZero : second thirdAtom • first - first thirdAtom • second = 0 :=
    hkill _ hcombinationMem hcombinationThird
  have hatPivot : second thirdAtom * first pivot = 0 := by
    have hentry := congrFun hcombinationZero pivot
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hpivotSecond,
      mul_zero, sub_zero] at hentry
    exact hentry
  have hsecondThirdZero : second thirdAtom = 0 :=
    (mul_eq_zero.mp hatPivot).resolve_right hpivotFirst
  exact hsecondNe (hkill second hsecondMem hsecondThirdZero)

/-! ### The hypotheses are inhabited

Precedent: a second-order escape once landed asking for flatness at twenty blocks at once --
twenty linear conditions on a five-dimensional space, true and useless.  So the two
hypothesis bundles that are not about a crux are shown SATISFIABLE before the floors are
built on them. -/

/-- **P4 NON-VACUITY FOR THE KILL.**  Every side condition of the two-atom kill is
satisfiable together with a NONZERO direction, so the kill is not a statement about an empty
configuration and the third-atom hypothesis is what does the work. -/
theorem exists_twoAtomKill_datum_nontrivial :
    ∃ (block : Finset (Fin 6)) (row direction : Fin 6 → ℝ)
      (firstAtom secondAtom thirdAtom : Fin 6),
      blockᶜ = {firstAtom, secondAtom, thirdAtom}
        ∧ firstAtom ≠ secondAtom ∧ firstAtom ≠ thirdAtom ∧ secondAtom ≠ thirdAtom
        ∧ row firstAtom ≠ row secondAtom
        ∧ (∀ atomIndex ∈ block, direction atomIndex = 0)
        ∧ (∑ atomIndex, direction atomIndex = 0)
        ∧ row ⬝ᵥ direction = 0
        ∧ direction ≠ 0 := by
  classical
  refine ⟨{0, 1, 2}, ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, -1], 3, 4, 5,
    by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · intro atomIndex hmem
    fin_cases hmem <;> rfl
  · simp [Fin.sum_univ_six]
  · simp [dotProduct, Fin.sum_univ_six]
  · intro hzero
    have hentry := congrFun hzero 4
    simp at hentry

/-- **P4 NON-VACUITY FOR THE MULTIPLIER LAYER.**  A constant assembly diagonal is satisfiable
at a genuinely `(6,3)`-shaped family with more than one block: the two-block configuration
with uniform tight vectors realises it exactly. -/
theorem exists_assemblyDiagonal_datum_nontrivial :
    ∃ (family : Finset (Finset (Fin 6))) (row : Finset (Fin 6) → (Fin 6 → ℝ))
      (multiplier : Finset (Fin 6) → ℝ),
      2 ≤ family.card
        ∧ (∀ selected ∈ family, selected.card = 3)
        ∧ ∀ atomIndex : Fin 6,
            ∑ selected ∈ family, multiplier selected * row selected atomIndex
              = (((6 : ℕ) : ℝ))⁻¹ := by
  classical
  refine ⟨{{0, 1, 2}, {3, 4, 5}},
    (fun selected atomIndex => if atomIndex ∈ selected then (1 : ℝ) / 3 else 0),
    (fun _ => (1 : ℝ) / 2), by decide, by decide, ?_⟩
  intro atomIndex
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  fin_cases atomIndex <;> norm_num [Fin.ext_iff]

/-! ## The floors -/

/-- **THE MULTIPLIER-FREE FLOOR.**  Four argmax blocks, from the second-order condition and
full support alone.  Three rows leave room for a separated flat pair once the all-ones vector
is spent as a fourth functional to hold the pair inside the simplex, and the engine forbids
such a pair -- so three rows are impossible.

The all-ones vector is spent here.  Recovering it is exactly what the multiplier layer does,
and it is the whole difference between this floor and the next. -/
theorem SixThreeCrux.four_le_card_chartArgmaxFamily_of_fullSupport (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hfullSupport : ∀ (selected : Finset (Fin 6)) (blockIndex : Fin 3),
      tightVec selected blockIndex ≠ 0) :
    4 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card := by
  classical
  set family := chartArgmaxFamily (chartPointOfDesign crux.design) with hfamily
  by_contra hcontra
  obtain ⟨first, second, pivot, hfirstNe, hsecondNe, hfirstFlat, hsecondFlat, hpivotFirst,
      hpivotSecond⟩ :=
    exists_flatPair_of_card_add_one_lt
      (Fin.cons ((fun _ => (1 : ℝ)) : Fin 6 → ℝ)
        (fun label : Fin family.card =>
          totalEigenSquareRow tightVec (family.equivFin.symm label : Finset (Fin 6)))
        : Fin (family.card + 1) → (Fin 6 → ℝ)) (by omega)
  have hsumOf : ∀ direction : Fin 6 → ℝ,
      (∀ label : Fin (family.card + 1),
        (Fin.cons ((fun _ => (1 : ℝ)) : Fin 6 → ℝ)
          (fun label : Fin family.card =>
            totalEigenSquareRow tightVec (family.equivFin.symm label : Finset (Fin 6)))
          : Fin (family.card + 1) → (Fin 6 → ℝ)) label ⬝ᵥ direction = 0) →
      ∑ atomIndex, direction atomIndex = 0 := by
    intro direction hflat
    have hhead := hflat 0
    rw [Fin.cons_zero] at hhead
    simpa only [dotProduct, one_mul] using hhead
  have hrowOf : ∀ direction : Fin 6 → ℝ,
      (∀ label : Fin (family.card + 1),
        (Fin.cons ((fun _ => (1 : ℝ)) : Fin 6 → ℝ)
          (fun label : Fin family.card =>
            totalEigenSquareRow tightVec (family.equivFin.symm label : Finset (Fin 6)))
          : Fin (family.card + 1) → (Fin 6 → ℝ)) label ⬝ᵥ direction = 0) →
      ∀ selected ∈ family, totalEigenSquareRow tightVec selected ⬝ᵥ direction = 0 := by
    intro direction hflat selected hmem
    have htail := hflat (family.equivFin ⟨selected, hmem⟩).succ
    rw [Fin.cons_succ] at htail
    rwa [Equiv.symm_apply_apply] at htail
  exact crux.false_of_flatPair tightVec hunit hEigen hfullSupport
    ⟨hrowOf first hfirstFlat, hsumOf first hfirstFlat⟩
    ⟨hrowOf second hsecondFlat, hsumOf second hsecondFlat⟩ hsecondNe hpivotFirst hpivotSecond

/-- **THE INDEX FLOOR.**  Five argmax blocks at a `(6,3)` crux, under simple full-support
tight eigenvectors and the multiplier layer.

This is the statement `Gtz.Quantitative.ChartSecondOrder` names as out of reach.  The
multiplier hypothesis is the shipped `assembly_diagonal` field read in the eigen-square
vocabulary -- `Gtz.assemblyDiagonal_of_isChartStationaryData_of_rowEq` is the bridge -- and
its whole effect is that a flat direction is automatically feasible for the simplex, which
frees the functional that the multiplier-free floor above has to spend. -/
theorem SixThreeCrux.five_le_card_chartArgmaxFamily_of_assemblyDiagonal (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hfullSupport : ∀ (selected : Finset (Fin 6)) (blockIndex : Fin 3),
      tightVec selected blockIndex ≠ 0)
    (multiplier : Finset (Fin 6) → ℝ)
    (hassembly : ∀ atomIndex : Fin 6,
      ∑ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
        multiplier selected * totalEigenSquareRow tightVec selected atomIndex
          = (((6 : ℕ) : ℝ))⁻¹) :
    5 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card := by
  classical
  set family := chartArgmaxFamily (chartPointOfDesign crux.design) with hfamily
  by_contra hcontra
  obtain ⟨first, second, pivot, hfirstNe, hsecondNe, hfirstFlat, hsecondFlat, hpivotFirst,
      hpivotSecond⟩ :=
    exists_flatPair_of_card_add_one_lt
      (fun label : Fin family.card =>
        totalEigenSquareRow tightVec (family.equivFin.symm label : Finset (Fin 6)))
      (by omega)
  have hrowOf : ∀ direction : Fin 6 → ℝ,
      (∀ label : Fin family.card,
        totalEigenSquareRow tightVec (family.equivFin.symm label : Finset (Fin 6))
          ⬝ᵥ direction = 0) →
      ∀ selected ∈ family, totalEigenSquareRow tightVec selected ⬝ᵥ direction = 0 := by
    intro direction hflat selected hmem
    have hlabel := hflat (family.equivFin ⟨selected, hmem⟩)
    rwa [Equiv.symm_apply_apply] at hlabel
  have hsumOf : ∀ direction : Fin 6 → ℝ,
      (∀ selected ∈ family, totalEigenSquareRow tightVec selected ⬝ᵥ direction = 0) →
      ∑ atomIndex, direction atomIndex = 0 := fun direction hflat =>
    sum_eq_zero_of_flat_of_assemblyDiagonal (by norm_num) family (totalEigenSquareRow tightVec)
      multiplier hassembly hflat
  exact crux.false_of_flatPair tightVec hunit hEigen hfullSupport
    ⟨hrowOf first hfirstFlat, hsumOf first (hrowOf first hfirstFlat)⟩
    ⟨hrowOf second hsecondFlat, hsumOf second (hrowOf second hsecondFlat)⟩ hsecondNe hpivotFirst
    hpivotSecond

/-- **THE INDEX FLOOR, THREADED TO THE SHIPPED BUNDLE.**  Same conclusion as
`Gtz.SixThreeCrux.five_le_card_chartArgmaxFamily_of_assemblyDiagonal`, with no invented
multiplier identity: the caller supplies the shipped stationarity bundle itself, together with
the one compatibility that identifies the two tight families -- at each ARGMAX block the tight
vector is the block restriction of the bundle's own tight direction there.

That compatibility is the whole content of the gap between the two families, and it is stated
rather than assumed away.  It is automatic when the least eigenvalue of the block is SIMPLE,
since a unit eigenvector is then determined up to a sign and the eigen-square row does not see
the sign; at a MULTIPLE least eigenvalue -- the `Gtz.icosaDesign` trap -- the escape and the
bundle may pick different eigenvectors of the same eigenspace and it can genuinely fail.
Nothing is asked at the INACTIVE blocks, where the bundle says nothing at all. -/
theorem SixThreeCrux.five_le_card_chartArgmaxFamily_of_blockRestriction (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hfullSupport : ∀ (selected : Finset (Fin 6)) (blockIndex : Fin 3),
      tightVec selected blockIndex ≠ 0)
    (multiplier : Finset (Fin 6) → ℝ) (selection : Finset (Fin 6) → (Fin 6 → ℝ))
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier selection)
    (hrestriction : ∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      ∀ hcard : selected.card = 3,
        tightVec selected
          = fun blockIndex => selection selected (selected.orderEmbOfFin hcard blockIndex)) :
    5 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card := by
  refine crux.five_le_card_chartArgmaxFamily_of_assemblyDiagonal tightVec hunit hEigen
    hfullSupport multiplier ?_
  refine assemblyDiagonal_of_isChartStationaryData_of_rowEq hdata _ ?_
  intro selected hmem atomIndex
  have hcard : selected.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmem).1
  rw [totalEigenSquareRow_of_card tightVec hcard, hrestriction selected hmem hcard]
  exact eigenSquareRow_eq_mul_self_of_support hcard (selection selected)
    (fun atom hnotMem => hdata.tightDir_support selected hmem atom hnotMem) atomIndex

/-- **THE COMPOSITE WITH THE NUMERICAL CENSUS, WITH THE CENSUS LEFT AS A HYPOTHESIS.**  Two
independent numerical campaigns report that no admissible chart-stationary point at `(6,3)`
has exactly five argmax blocks -- indeed none below eight.  That is a MEASUREMENT by
random-restart local solving, it carries a known bias toward high-dimensional components, and
it is proved nowhere.  So it appears here as an explicit hypothesis and is discharged
nowhere: what the kernel adds is only the step from five to six. -/
theorem SixThreeCrux.six_le_card_chartArgmaxFamily_of_assemblyDiagonal_of_ne_five
    (crux : SixThreeCrux) (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hfullSupport : ∀ (selected : Finset (Fin 6)) (blockIndex : Fin 3),
      tightVec selected blockIndex ≠ 0)
    (multiplier : Finset (Fin 6) → ℝ)
    (hassembly : ∀ atomIndex : Fin 6,
      ∑ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
        multiplier selected * totalEigenSquareRow tightVec selected atomIndex
          = (((6 : ℕ) : ℝ))⁻¹)
    (hnotFive : (chartArgmaxFamily (chartPointOfDesign crux.design)).card ≠ 5) :
    6 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card := by
  have hfive := crux.five_le_card_chartArgmaxFamily_of_assemblyDiagonal tightVec hunit hEigen
    hfullSupport multiplier hassembly
  omega

end Gtz
