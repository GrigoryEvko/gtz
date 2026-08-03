/-
# The support-two rung of the index floor, and the vanishing-pairing degree cap

`Gtz.Quantitative.ChartArgmaxIndexFloor` lands the index floor at a `(6,3)` crux under
FULL SUPPORT of the tight eigenvectors and states, in its own words, what it leaves out:
"The honest ladder is `|A| >= 2 + s` where `s` is the size of the smallest tight support,
and only the case `s = 3` is proved here", with the support-two rung named as absent
because "the kill then leaves a PLANE rather than a line".  This file supplies the missing
rungs and closes the ladder.

## The counting, in one paragraph

The shipped argument produces a SEPARATED PAIR of flat directions and plays them off one
another with a pivot.  That machinery is not needed, and dropping it is what makes the
whole ladder fall out at once.  The covering block is determined by the flat SUBMODULE, so
it is available BEFORE any direction is chosen; once it is fixed, the atoms to be killed
are fixed too, and their coordinate functionals can simply be ADJOINED to the family of
eigen-square rows.  One application of the shipped underdetermined-system lemma then
produces a single nonzero direction that is flat, vanishes on the covering set and vanishes
at every killed atom -- so it is supported on two atoms, and a row separating those two
finishes it.  Counting functionals gives `vanish.card + 2 <= |A|` with no case analysis and
no pivot.

* THE KILL IS ONE LINE OF ARITHMETIC.  `Gtz.eq_zero_of_support_pair_of_sumZero_of_rowFlat`:
  a direction supported on two atoms, summing to zero and annihilated by a row taking
  different values there, is zero.  No block, no rank, no dimension, any size.
* THE ENGINE.  `Gtz.card_add_two_le_card_of_flatVanishing` packages the count at general
  size for an arbitrary row family with a constant assembly diagonal.  It knows nothing
  about designs, eigenvectors or charts.
* THE SUPPORT.  `Gtz.totalTightSupport` is the set of atoms where a block's tight vector
  does not vanish.  The shipped escape gives ANNIHILATION of the tight vector; the shipped
  `Gtz.eq_zero_of_submatrix_diagonal_mulVec_eq_zero_of_ne` turns that into vanishing of the
  direction exactly on this set, which is why the ladder reads the support size off
  directly rather than the block size.
* THE SEPARATOR IS FREE.  A constant assembly diagonal cannot be met by rows that all
  vanish at some atom, so the multiplier layer itself supplies, at every atom, an argmax
  block whose row is nonzero there
  (`Gtz.exists_mem_ne_zero_of_assemblyDiagonal`).  That is what replaces the shipped
  proof's search for a third block, and it is why no `3 <= |A|` input is needed here.

## What is proved

* `Gtz.SixThreeCrux.supportFloor_add_two_le_card_chartArgmaxFamily` -- the rung at any
  support floor `s` with `s + 3 < 6`, i.e. `s <= 2`.  The hypothesis `s + rank < size` is
  exactly what buys an atom outside both the covering set and the separator block.
* `Gtz.SixThreeCrux.four_le_card_chartArgmaxFamily_of_supportTwo` -- the headline, `s = 2`.
* `Gtz.SixThreeCrux.supportFloor_add_two_le_card_chartArgmaxFamily_of_le_rank` -- THE
  LADDER, `|A| >= 2 + s` for every `s <= 3`.  Below the top it is the rung above; at
  `s = 3` the support fills the block, so the tight vectors have full support and the
  shipped `Gtz.SixThreeCrux.five_le_card_chartArgmaxFamily_of_assemblyDiagonal` fires.  The
  shipped floor is CONSUMED, not re-proved.  One wrinkle is visible in the proof: the
  shipped full-support hypothesis quantifies over EVERY subset while a support floor can
  only speak about the ones of the right size, so the tight family is patched off the
  card-three blocks before it is handed over.  Nothing downstream of the escape ever looks
  at those blocks.

## What is NOT here

* THE ROUTE STOPS AT `s + rank < size`.  At `s = 3` the covering set can be a whole block
  and the separator its complement, leaving no atom for the second half of the kill; the
  shipped proof handles that by excluding `{C, Cᶜ}` and spending the `3 <= |A|` floor.  So
  this file does not subsume the shipped rung, and the two are landed side by side.
* NOTHING IS SAID ABOUT `s = 0` OR `s = 1` BEING EXCLUDED.  A unit tight vector has support
  at least one, so `s = 1` is free and gives only `|A| >= 3`, which the shipped
  `Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily` already has.  The content is `s = 2`.
* THE MEASURED FLOOR IS STILL NOT PROVED.  Two numerical campaigns report no admissible
  chart-stationary point below eight argmax blocks.  That is a MEASUREMENT with a known
  component bias and nothing here assumes any of it.

## The vanishing-pairing layer, and an honest negative

The second half of the file attacks the standing question of whether a crux can carry more
than one orthogonal pair.  The answer is NOT settled here, and the two levers that do
survive are landed with the obstruction recorded.

* `Gtz.exists_dotProduct_ne_zero_of_hasStrictlyDominatingCoSingletons` -- THE DEGREE CAP.
  No atom of a design with strictly dominating co-singletons is orthogonal to every other
  atom.  Evaluating the co-singleton at the atom itself gives
  `sum of squared pairings > leverage`, which an all-orthogonal atom contradicts outright.
  General in `(size, rank)`.  At a crux this is
  `Gtz.SixThreeCrux.exists_atomPairing_ne_zero`: the orthogonality graph has maximum degree
  at most `size - 2`.
* `Gtz.exists_nonpos_and_exists_nonneg_erasePair_of_atomPairing_eq_zero` -- THE EDGE
  ALTERNATION.  At an orthogonal edge the shipped
  `Gtz.sum_erasePair_eq_zero_of_atomPairing_eq_zero` makes the weighted star products
  cancel, so they cannot all be strictly positive nor all strictly negative.  The prose of
  `Gtz.Quantitative.TwoGraphCollision` already draws that conclusion; here it is a theorem.
* WHAT DOES NOT WORK, precisely.  The route through the edge law at a SECOND, incident
  orthogonal edge is exhausted, and not merely resistant.  Write the pivot's orthogonal
  complement as a plane; the two neighbours span it, and the two edge laws say that the
  Parseval off-diagonal vector between the pivot's line and the plane is annihilated by
  each of them.  That vector vanishes at EVERY design by Parseval, so the two edge laws are
  consequences of a fact that carries no information about the crux.  The quantitative
  content of an incident pair is already shipped as
  `Gtz.SixThreeCrux.pairMinor_neg_of_common_orthogonalPartner`.
* CALIBRATION, and it says what any proof must consume.  The shipped `Gtz.rootKillDesign`
  -- the `D3` root system, the six edge vectors of `K4` -- is an all-heavy `(6,3)` Parseval
  design whose orthogonality graph is a PERFECT MATCHING: exactly three vanishing pairings,
  every atom of degree one.  (Two edge vectors of `K4` are orthogonal exactly when they are
  disjoint, and scaling to leverage three does not move a zero.)  So "at most one vanishing
  pairing" cannot follow from Parseval and all-heaviness alone; it has to consume the crux
  hypotheses, and `Gtz.rootKillDesign` fails exactly one of them -- it has four dominating
  triples.  Measured exactly outside the kernel, not mechanized here.
* THE UNEXPLORED ROUTE, named for a successor.  The neighbours of a vertex of the
  orthogonality graph lie in a plane, and the projections of the remaining atoms complete
  them to a weighted tight frame OF THAT PLANE -- a rank-two design, where GTZ is a
  theorem.  A dominating pair drawn from the NEIGHBOURS extends by the pivot to a
  dominating triple and kills the configuration; a dominating pair that uses a projected
  non-neighbour does not, because the pivot picks up an off-diagonal block.  Forcing the
  pair into the neighbourhood is exactly what is missing.

## R6 disclosures

`Gtz.eq_zero_of_support_pair_of_sumZero_of_rowFlat` GENERALISES the shipped
`Gtz.eq_zero_of_vanishing_of_sumZero_of_rowFlat`, which is stated at `Fin 6` for a block
whose complement is a named triple.  The shipped statement is NOT re-proved; the `example`
below the kill derives it from the general form so that the subsumption is machine-checked
rather than asserted.  `Gtz.exists_mem_ne_zero_of_assemblyDiagonal` is chart-side arithmetic
and is unrelated to the quadric-side `Gtz.coverageLaw_of_isQuadricStationaryData`, whose
datum no crux carries.  `Gtz.totalTightSupport` is unrelated to
`Gtz.HasIndependentTightSupport`, which is a linear-independence condition on a datum's
tight directions rather than a support set.

THE MECHANISM IS FIELD-BLIND, as it is in the shipped file, and this remains orientation
prose rather than a theorem: every step runs verbatim over the complex numbers, so nothing
here can close the cell alone.
-/

import Mathlib
import Gtz.Quantitative.ChartArgmaxIndexFloor
import Gtz.Quantitative.CoherentCountFloor
import Gtz.Quantitative.TwoGraphCollision
import Gtz.Ties.TotalTieCorankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The kill, and the counting engine -/

/-- **THE SUPPORT-PAIR KILL.**  A direction supported on two atoms, summing to zero and
annihilated by a row taking DIFFERENT values at those two atoms, is zero.  The two
conditions are independent on the two-dimensional space the support hypothesis leaves, and
that is the whole argument: no block, no rank, no eigenvalue, no dimension count, any size.

This GENERALISES the shipped `Gtz.eq_zero_of_vanishing_of_sumZero_of_rowFlat`, which is
`Fin 6` and phrases the support hypothesis as a block together with a named complementary
triple whose third member vanishes.  The shipped form is derived from this one in the
`example` below rather than re-proved. -/
theorem eq_zero_of_support_pair_of_sumZero_of_rowFlat {size : ℕ}
    {direction row : Fin size → ℝ} {positiveAtom zeroAtom : Fin size}
    (hsupport : ∀ atomIndex : Fin size, atomIndex ≠ positiveAtom → atomIndex ≠ zeroAtom →
      direction atomIndex = 0)
    (hrowDistinct : row positiveAtom ≠ row zeroAtom)
    (hsum : ∑ atomIndex, direction atomIndex = 0)
    (hrowFlat : row ⬝ᵥ direction = 0) :
    direction = 0 := by
  classical
  have hne : positiveAtom ≠ zeroAtom := fun hcollide => hrowDistinct (by rw [hcollide])
  have hpairSum : ∀ scalarOf : Fin size → ℝ,
      (∀ atomIndex : Fin size, atomIndex ≠ positiveAtom → atomIndex ≠ zeroAtom →
        scalarOf atomIndex = 0) →
      ∑ atomIndex, scalarOf atomIndex = scalarOf positiveAtom + scalarOf zeroAtom := by
    intro scalarOf hzero
    rw [← Finset.sum_subset (Finset.subset_univ ({positiveAtom, zeroAtom} : Finset (Fin size)))
      (fun atomIndex _ hnotMem => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnotMem
        exact hzero atomIndex hnotMem.1 hnotMem.2)]
    exact Finset.sum_pair hne
  have hsumPair : direction positiveAtom + direction zeroAtom = 0 := by
    rw [← hpairSum direction hsupport]
    exact hsum
  have hrowPair : row positiveAtom * direction positiveAtom
      + row zeroAtom * direction zeroAtom = 0 := by
    rw [← hpairSum (fun atomIndex => row atomIndex * direction atomIndex)
      (fun atomIndex hnepos hnezero => by rw [hsupport atomIndex hnepos hnezero, mul_zero])]
    exact hrowFlat
  have hpositiveZero : direction positiveAtom = 0 := by
    have hsub : (row positiveAtom - row zeroAtom) * direction positiveAtom = 0 := by
      linear_combination hrowPair - row zeroAtom * hsumPair
    rcases mul_eq_zero.mp hsub with hdiff | hvalue
    · exact absurd (sub_eq_zero.mp hdiff) hrowDistinct
    · exact hvalue
  have hzeroZero : direction zeroAtom = 0 := by linarith
  funext atomIndex
  rw [Pi.zero_apply]
  by_cases hpositive : atomIndex = positiveAtom
  · rw [hpositive]; exact hpositiveZero
  · by_cases hzeroCase : atomIndex = zeroAtom
    · rw [hzeroCase]; exact hzeroZero
    · exact hsupport atomIndex hpositive hzeroCase


/-- The shipped `Gtz.eq_zero_of_vanishing_of_sumZero_of_rowFlat` follows from the general
support-pair kill: a direction vanishing on a block and at the third atom of the
complementary triple is supported on the other two.  Checked here rather than asserted in
prose, and deliberately left as an `example` so that no second name carries the shipped
statement. -/
example {direction row : Fin 6 → ℝ} {block : Finset (Fin 6)}
    {firstAtom secondAtom thirdAtom : Fin 6}
    (hcompl : blockᶜ = {firstAtom, secondAtom, thirdAtom})
    (hfirstThird : firstAtom ≠ thirdAtom) (hsecondThird : secondAtom ≠ thirdAtom)
    (hrowDistinct : row firstAtom ≠ row secondAtom)
    (hvanish : ∀ atomIndex ∈ block, direction atomIndex = 0)
    (hthird : direction thirdAtom = 0)
    (hsum : ∑ atomIndex, direction atomIndex = 0)
    (hrowFlat : row ⬝ᵥ direction = 0) :
    direction = 0 := by
  classical
  refine eq_zero_of_support_pair_of_sumZero_of_rowFlat ?_ hrowDistinct hsum hrowFlat
  intro atomIndex hnefirst hnesecond
  by_cases hmem : atomIndex ∈ block
  · exact hvanish atomIndex hmem
  · have hmemCompl : atomIndex ∈ blockᶜ := Finset.mem_compl.mpr hmem
    rw [hcompl] at hmemCompl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmemCompl
    rcases hmemCompl with rfl | rfl | rfl
    · exact absurd rfl hnefirst
    · exact absurd rfl hnesecond
    · exact hthird


/-- **A CONSTANT ASSEMBLY DIAGONAL SUPPLIES A NONZERO ROW AT EVERY ATOM.**  If every row of
the family vanished at some atom, the multiplier combination would vanish there too, and it
is pinned to `1/size`.  Pure arithmetic, no design and no chart.

This is what replaces the search for a third block in the shipped index floor: the
separator the kill needs is produced by the multiplier layer itself, so no lower bound on
the family's size has to be spent to find one. -/
theorem exists_mem_ne_zero_of_assemblyDiagonal {size : ℕ} (hsize : 0 < size)
    (family : Finset (Finset (Fin size))) (row : Finset (Fin size) → (Fin size → ℝ))
    (multiplier : Finset (Fin size) → ℝ)
    (hassembly : ∀ atomIndex : Fin size,
      ∑ selected ∈ family, multiplier selected * row selected atomIndex = ((size : ℝ))⁻¹)
    (atomIndex : Fin size) :
    ∃ selected ∈ family, row selected atomIndex ≠ 0 := by
  by_contra hcontra
  have hpointwise : ∀ selected ∈ family, row selected atomIndex = 0 := by
    intro selected hmem
    by_contra hne
    exact hcontra ⟨selected, hmem, hne⟩
  have hzero : ∑ selected ∈ family, multiplier selected * row selected atomIndex = 0 :=
    Finset.sum_eq_zero fun selected hmem => by rw [hpointwise selected hmem, mul_zero]
  rw [hassembly atomIndex] at hzero
  exact inv_ne_zero (Nat.cast_ne_zero.mpr hsize.ne') hzero

/-- **THE COUNTING ENGINE.**  Suppose every flat, sum-zero direction vanishes on a common set
`vanish`, and some member of the family has a row that is nonzero at one atom outside
`vanish` and zero at another.  Then the family has at least `vanish.card + 2` members.

The proof adjoins the coordinate functionals of the atoms outside `vanish ∪ {pos, zero}` to
the row family.  Too few functionals leave a nonzero common annihilator; it is flat, hence
sums to zero by the assembly diagonal, hence vanishes on `vanish` by hypothesis and at the
adjoined atoms by construction -- so it is supported on the two remaining atoms and the
support-pair kill destroys it.

Notice which hypotheses are ABSENT: no step size, no feasibility, no lower bound on the
family, no pivot and no second direction.  The shipped index floor builds a separated PAIR
of flat directions and plays them against each other; that is unnecessary, because the
covering set is determined by the flat submodule and is therefore available before any
direction is chosen. -/
theorem card_add_two_le_card_of_flatVanishing {size : ℕ} (hsize : 0 < size)
    (family : Finset (Finset (Fin size))) (row : Finset (Fin size) → (Fin size → ℝ))
    (multiplier : Finset (Fin size) → ℝ)
    (hassembly : ∀ atomIndex : Fin size,
      ∑ selected ∈ family, multiplier selected * row selected atomIndex = ((size : ℝ))⁻¹)
    (vanish : Finset (Fin size))
    (hcover : ∀ direction : Fin size → ℝ,
      (∀ selected ∈ family, row selected ⬝ᵥ direction = 0) →
        (∑ atomIndex, direction atomIndex = 0) →
          ∀ atomIndex ∈ vanish, direction atomIndex = 0)
    {separator : Finset (Fin size)} (hseparator : separator ∈ family)
    {positiveAtom zeroAtom : Fin size}
    (hpositiveNotMem : positiveAtom ∉ vanish) (hzeroNotMem : zeroAtom ∉ vanish)
    (hpositiveRow : row separator positiveAtom ≠ 0)
    (hzeroRow : row separator zeroAtom = 0) :
    vanish.card + 2 ≤ family.card := by
  classical
  by_contra hcontra
  have hsmall : family.card < vanish.card + 2 := Nat.lt_of_not_le hcontra
  have hne : positiveAtom ≠ zeroAtom := by
    intro hcollide
    rw [hcollide, hzeroRow] at hpositiveRow
    exact hpositiveRow rfl
  set kept : Finset (Fin size) := insert positiveAtom (insert zeroAtom vanish) with hkept
  have hpositiveOut : positiveAtom ∉ insert zeroAtom vanish := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hne, hpositiveNotMem⟩
  have hkeptCard : kept.card = vanish.card + 2 := by
    rw [hkept, Finset.card_insert_of_notMem hpositiveOut,
      Finset.card_insert_of_notMem hzeroNotMem]
  have hkeptLe : vanish.card + 2 ≤ size := by
    have hle := Finset.card_le_univ kept
    rw [hkeptCard, Fintype.card_fin] at hle
    exact hle
  have hextraCard : keptᶜ.card = size - (vanish.card + 2) := by
    rw [Finset.card_compl, hkeptCard, Fintype.card_fin]
  obtain ⟨direction, hnonzero, hflatAll⟩ :=
    exists_ne_zero_forall_dotProduct_eq_zero_of_card_lt
      (Fin.append
        (fun label : Fin family.card => row (family.equivFin.symm label : Finset (Fin size)))
        (fun label : Fin keptᶜ.card =>
          Pi.single ((keptᶜ.equivFin.symm label : Fin size)) (1 : ℝ)))
      (by omega)
  have hflatRow : ∀ selected ∈ family, row selected ⬝ᵥ direction = 0 := by
    intro selected hmem
    have hlabel := hflatAll (Fin.castAdd keptᶜ.card (family.equivFin ⟨selected, hmem⟩))
    rwa [Fin.append_left, Equiv.symm_apply_apply] at hlabel
  have hextraZero : ∀ atomIndex ∈ keptᶜ, direction atomIndex = 0 := by
    intro atomIndex hmem
    have hlabel := hflatAll (Fin.natAdd family.card (keptᶜ.equivFin ⟨atomIndex, hmem⟩))
    rw [Fin.append_right, Equiv.symm_apply_apply, single_dotProduct] at hlabel
    linarith [hlabel]
  have hsum : ∑ atomIndex, direction atomIndex = 0 :=
    sum_eq_zero_of_flat_of_assemblyDiagonal hsize family row multiplier hassembly hflatRow
  have hvanishZero := hcover direction hflatRow hsum
  have hsupport : ∀ atomIndex : Fin size, atomIndex ≠ positiveAtom → atomIndex ≠ zeroAtom →
      direction atomIndex = 0 := by
    intro atomIndex hnepositive hnezero
    by_cases hmemVanish : atomIndex ∈ vanish
    · exact hvanishZero atomIndex hmemVanish
    · refine hextraZero atomIndex (Finset.mem_compl.mpr ?_)
      rw [hkept]
      simp only [Finset.mem_insert, not_or]
      exact ⟨hnepositive, hnezero, hmemVanish⟩
  exact hnonzero (eq_zero_of_support_pair_of_sumZero_of_rowFlat hsupport
    (by rw [hzeroRow]; exact hpositiveRow) hsum (hflatRow separator hseparator))

/-! ## The tight support, and the escape read on it -/

/-- The set of ATOMS at which a block's tight vector does not vanish.  On a block of the right
size it is the image of the vector's nonzero coordinates under the block's order embedding;
elsewhere it is empty and never consulted.  Its cardinality is the `s` of the ladder
`|A| >= 2 + s`. -/
noncomputable def totalTightSupport {size rank : ℕ}
    (tightVec : Finset (Fin size) → (Fin rank → ℝ)) (selected : Finset (Fin size)) :
    Finset (Fin size) :=
  if hcard : selected.card = rank then
    (Finset.univ.filter fun blockIndex => tightVec selected blockIndex ≠ 0).image
      (selected.orderEmbOfFin hcard)
  else ∅

/-- The support, unfolded on a block of the right size. -/
theorem totalTightSupport_of_card {size rank : ℕ}
    (tightVec : Finset (Fin size) → (Fin rank → ℝ)) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) :
    totalTightSupport tightVec selected
      = (Finset.univ.filter fun blockIndex => tightVec selected blockIndex ≠ 0).image
          (selected.orderEmbOfFin hcard) :=
  dif_pos hcard

/-- A tight vector's support lies inside its own block. -/
theorem totalTightSupport_subset {size rank : ℕ}
    (tightVec : Finset (Fin size) → (Fin rank → ℝ)) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) :
    totalTightSupport tightVec selected ⊆ selected := by
  classical
  rw [totalTightSupport_of_card tightVec hcard]
  intro atomIndex hmem
  obtain ⟨blockIndex, _, hblock⟩ := Finset.mem_image.mp hmem
  exact hblock ▸ selected.orderEmbOfFin_mem hcard blockIndex

/-- The support has as many atoms as the tight vector has nonzero coordinates: the order
embedding is injective, so nothing is lost in the image. -/
theorem card_totalTightSupport {size rank : ℕ}
    (tightVec : Finset (Fin size) → (Fin rank → ℝ)) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) :
    (totalTightSupport tightVec selected).card
      = (Finset.univ.filter fun blockIndex => tightVec selected blockIndex ≠ 0).card := by
  classical
  rw [totalTightSupport_of_card tightVec hcard,
    Finset.card_image_of_injective _ (selected.orderEmbOfFin hcard).injective]

/-- A nonzero coordinate of the tight vector puts its atom in the support. -/
theorem mem_totalTightSupport {size rank : ℕ}
    (tightVec : Finset (Fin size) → (Fin rank → ℝ)) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) {blockIndex : Fin rank}
    (hne : tightVec selected blockIndex ≠ 0) :
    selected.orderEmbOfFin hcard blockIndex ∈ totalTightSupport tightVec selected := by
  classical
  rw [totalTightSupport_of_card tightVec hcard]
  exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)

/-- **THE SUPPORT-TWO HYPOTHESIS, IN COORDINATES.**  Two distinct nonzero coordinates give a
support of at least two atoms.  This is the form a caller can check without ever building
the support set. -/
theorem two_le_card_totalTightSupport {size rank : ℕ}
    (tightVec : Finset (Fin size) → (Fin rank → ℝ)) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) {firstIndex secondIndex : Fin rank}
    (hne : firstIndex ≠ secondIndex)
    (hfirst : tightVec selected firstIndex ≠ 0) (hsecond : tightVec selected secondIndex ≠ 0) :
    2 ≤ (totalTightSupport tightVec selected).card := by
  classical
  rw [card_totalTightSupport tightVec hcard]
  have hsub : ({firstIndex, secondIndex} : Finset (Fin rank))
      ⊆ Finset.univ.filter fun blockIndex => tightVec selected blockIndex ≠ 0 := by
    intro blockIndex hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirst⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsecond⟩
  have hcardPair : ({firstIndex, secondIndex} : Finset (Fin rank)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  exact hcardPair ▸ Finset.card_le_card hsub

/-- **A FULL-SIZED SUPPORT IS FULL SUPPORT.**  A support of at least `rank` atoms exhausts the
`rank` coordinates, so no coordinate of the tight vector vanishes.  This is the bridge that
lets the top rung of the ladder hand over to the shipped full-support floor. -/
theorem forall_ne_zero_of_card_totalTightSupport {size rank : ℕ}
    (tightVec : Finset (Fin size) → (Fin rank → ℝ)) {selected : Finset (Fin size)}
    (hcard : selected.card = rank)
    (hle : rank ≤ (totalTightSupport tightVec selected).card) (blockIndex : Fin rank) :
    tightVec selected blockIndex ≠ 0 := by
  classical
  rw [card_totalTightSupport tightVec hcard] at hle
  have hupper := Finset.card_filter_le (Finset.univ : Finset (Fin rank))
    fun otherIndex => tightVec selected otherIndex ≠ 0
  rw [Finset.card_univ, Fintype.card_fin] at hupper
  have hcardEq : (Finset.univ.filter fun otherIndex => tightVec selected otherIndex ≠ 0).card
      = Fintype.card (Fin rank) := by
    rw [Fintype.card_fin]
    omega
  have hmem : blockIndex ∈ Finset.univ.filter fun otherIndex => tightVec selected otherIndex ≠ 0 := by
    rw [Finset.eq_univ_of_card _ hcardEq]
    exact Finset.mem_univ _
  exact (Finset.mem_filter.mp hmem).2

/-- **THE ESCAPE, READ ON THE SUPPORT RATHER THAN THE BLOCK.**  The shipped escape concludes
that the restricted diagonal ANNIHILATES some argmax block's tight vector; the shipped
`Gtz.eq_zero_of_submatrix_diagonal_mulVec_eq_zero_of_ne` converts annihilation into
vanishing of the direction at exactly the atoms where the tight vector survives.  So the
flat direction vanishes on the SUPPORT, with no full-support hypothesis anywhere.

Against `Gtz.SixThreeCrux.exists_argmax_direction_eq_zero_of_flatWeightDirection` this
trades a strictly weaker conclusion for the removal of that hypothesis, which is exactly
the trade the ladder is about. -/
theorem SixThreeCrux.exists_argmax_direction_eq_zero_on_totalTightSupport (crux : SixThreeCrux)
    (direction : Fin 6 → ℝ) (hsum : ∑ atomIndex, direction atomIndex = 0)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hflat : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design) →
        tightVec selected ⬝ᵥ ((Matrix.diagonal direction).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)
            *ᵥ tightVec selected) = 0) :
    ∃ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      ∀ atomIndex ∈ totalTightSupport tightVec selected, direction atomIndex = 0 := by
  classical
  obtain ⟨selected, hcard, hactive, hannihilated⟩ :=
    crux.exists_tight_annihilated_of_flatWeightDirection direction hsum tightVec hunit hEigen hflat
  refine ⟨selected, hactive, fun atomIndex hmem => ?_⟩
  rw [totalTightSupport_of_card tightVec hcard] at hmem
  obtain ⟨blockIndex, hfilter, hblock⟩ := Finset.mem_image.mp hmem
  rw [← hblock]
  exact eq_zero_of_submatrix_diagonal_mulVec_eq_zero_of_ne direction hcard hannihilated
    (Finset.mem_filter.mp hfilter).2

/-- **ONE SUPPORT SET FOR ALL FLAT DIRECTIONS.**  Each flat direction vanishes on the support
of SOME argmax block; the union-of-subspaces lemma upgrades that to a single support set
that works for all of them at once.  The covering set is therefore a function of the flat
submodule alone, which is what lets the atoms to be killed be chosen before any direction
is produced. -/
theorem SixThreeCrux.exists_argmax_le_vanishingSubmodule_totalTightSupport (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected) :
    ∃ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      flatSumZeroSubmodule (chartArgmaxFamily (chartPointOfDesign crux.design))
          (totalEigenSquareRow tightVec)
        ≤ vanishingSubmodule (totalTightSupport tightVec block) := by
  classical
  obtain ⟨index, hle⟩ := exists_le_of_forall_exists_mem
    (flatSumZeroSubmodule (chartArgmaxFamily (chartPointOfDesign crux.design))
      (totalEigenSquareRow tightVec))
    (fun index : {block // block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)} =>
      vanishingSubmodule (totalTightSupport tightVec index.1))
    (by
      rintro direction ⟨hflat, hsum⟩
      obtain ⟨block, hmem, hvanish⟩ :=
        crux.exists_argmax_direction_eq_zero_on_totalTightSupport direction hsum tightVec
          hunit hEigen
          (fun selected hcard hmemArgmax => by
            rw [← eigenSquareRow_dotProduct selected hcard (tightVec selected) direction,
              ← totalEigenSquareRow_of_card tightVec hcard]
            exact hflat selected hmemArgmax)
      exact ⟨⟨block, hmem⟩, hvanish⟩)
  exact ⟨index.1, index.2, hle⟩

/-! ## The ladder -/

/-- **THE LADDER RUNG BELOW THE TOP.**  At a `(6,3)` crux with a tight eigenvector at every
triple whose support has at least `supportFloor` atoms, and with the multiplier layer, the
argmax family has at least `supportFloor + 2` members.

The hypothesis `supportFloor + 3 < 6` is `s + rank < size`, and it is used in exactly one
place: to find an atom outside both the covering support and the separator block, which is
the second atom of the kill.  At `s = rank` it fails, the covering support can be a whole
block and the separator its complement, and the shipped rung takes over -- see
`Gtz.SixThreeCrux.supportFloor_add_two_le_card_chartArgmaxFamily_of_le_rank`.

No `3 <= |A|` input is consumed: the separator comes from the assembly diagonal. -/
theorem SixThreeCrux.supportFloor_add_two_le_card_chartArgmaxFamily (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (supportFloor : ℕ) (hroom : supportFloor + 3 < 6)
    (hsupport : ∀ selected : Finset (Fin 6), selected.card = 3 →
      supportFloor ≤ (totalTightSupport tightVec selected).card)
    (multiplier : Finset (Fin 6) → ℝ)
    (hassembly : ∀ atomIndex : Fin 6,
      ∑ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
        multiplier selected * totalEigenSquareRow tightVec selected atomIndex
          = (((6 : ℕ) : ℝ))⁻¹) :
    supportFloor + 2 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card := by
  classical
  set family := chartArgmaxFamily (chartPointOfDesign crux.design) with hfamily
  obtain ⟨baseBlock, hbaseMem, hle⟩ :=
    crux.exists_argmax_le_vanishingSubmodule_totalTightSupport tightVec hunit hEigen
  have hmemberCard : ∀ block ∈ family, block.card = 3 := fun block hmem =>
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) block).mp hmem).1
  have hbaseCard : baseBlock.card = 3 := hmemberCard baseBlock hbaseMem
  obtain ⟨vanish, hvanishSub, hvanishCard⟩ :=
    Finset.exists_subset_card_eq (hsupport baseBlock hbaseCard)
  have hpositiveNonempty : vanishᶜ.Nonempty := by
    refine Finset.card_pos.mp ?_
    rw [Finset.card_compl, Fintype.card_fin, hvanishCard]
    omega
  obtain ⟨positiveAtom, hpositiveCompl⟩ := hpositiveNonempty
  have hpositiveNotMem : positiveAtom ∉ vanish := Finset.mem_compl.mp hpositiveCompl
  obtain ⟨separator, hseparatorMem, hpositiveRow⟩ :=
    exists_mem_ne_zero_of_assemblyDiagonal (by norm_num) family
      (totalEigenSquareRow tightVec) multiplier hassembly positiveAtom
  have hseparatorCard : separator.card = 3 := hmemberCard separator hseparatorMem
  have hzeroNonempty : (vanish ∪ separator)ᶜ.Nonempty := by
    refine Finset.card_pos.mp ?_
    have hunion := Finset.card_union_le vanish separator
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨zeroAtom, hzeroCompl⟩ := hzeroNonempty
  rw [Finset.mem_compl, Finset.mem_union, not_or] at hzeroCompl
  obtain ⟨hzeroNotVanish, hzeroNotSeparator⟩ := hzeroCompl
  have hzeroRow : totalEigenSquareRow tightVec separator zeroAtom = 0 := by
    rw [totalEigenSquareRow_of_card tightVec hseparatorCard]
    exact eigenSquareRow_eq_zero_of_notMem hseparatorCard (tightVec separator) hzeroNotSeparator
  have hengine := card_add_two_le_card_of_flatVanishing (by norm_num) family
    (totalEigenSquareRow tightVec) multiplier hassembly vanish
    (fun direction hflat hsum atomIndex hmem =>
      hle (⟨hflat, hsum⟩ :
          direction ∈ flatSumZeroSubmodule family (totalEigenSquareRow tightVec))
        atomIndex (hvanishSub hmem))
    hseparatorMem hpositiveNotMem hzeroNotVanish hpositiveRow hzeroRow
  omega

/-- **THE SUPPORT-TWO RUNG.**  Four argmax blocks at a `(6,3)` crux once every tight
eigenvector has at least two nonzero coordinates.  This is the case
`Gtz.Quantitative.ChartArgmaxIndexFloor` names as not built there, and it covers
configurations the shipped floor cannot see -- `Gtz.exists_supportTwo_tightVec_not_fullSupport`
exhibits a tight family satisfying this hypothesis and failing full support. -/
theorem SixThreeCrux.four_le_card_chartArgmaxFamily_of_supportTwo (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hsupport : ∀ selected : Finset (Fin 6), selected.card = 3 →
      2 ≤ (totalTightSupport tightVec selected).card)
    (multiplier : Finset (Fin 6) → ℝ)
    (hassembly : ∀ atomIndex : Fin 6,
      ∑ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
        multiplier selected * totalEigenSquareRow tightVec selected atomIndex
          = (((6 : ℕ) : ℝ))⁻¹) :
    4 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card :=
  crux.supportFloor_add_two_le_card_chartArgmaxFamily tightVec hunit hEigen 2 (by norm_num)
    hsupport multiplier hassembly

/-- **THE LADDER, COMPLETE.**  `|A| >= 2 + s` at a `(6,3)` crux for every support floor
`s <= 3`.  Below the top this is the rung above; at `s = 3` a support of three atoms fills
its block, the tight vectors have full support, and the shipped
`Gtz.SixThreeCrux.five_le_card_chartArgmaxFamily_of_assemblyDiagonal` is CONSUMED.

The patch inside the proof is bookkeeping and is worth naming: the shipped full-support
hypothesis quantifies over EVERY subset of the atom set, while a support floor can only
constrain the ones of the right size, so the tight family is redefined to a full-support
constant off the card-three blocks before it is handed over.  Nothing between the escape
and the floor ever evaluates the family there, and the assembly identity only sees argmax
blocks, all of which have the right size. -/
theorem SixThreeCrux.supportFloor_add_two_le_card_chartArgmaxFamily_of_le_rank
    (crux : SixThreeCrux) (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (supportFloor : ℕ) (hrank : supportFloor ≤ 3)
    (hsupport : ∀ selected : Finset (Fin 6), selected.card = 3 →
      supportFloor ≤ (totalTightSupport tightVec selected).card)
    (multiplier : Finset (Fin 6) → ℝ)
    (hassembly : ∀ atomIndex : Fin 6,
      ∑ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
        multiplier selected * totalEigenSquareRow tightVec selected atomIndex
          = (((6 : ℕ) : ℝ))⁻¹) :
    supportFloor + 2 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card := by
  classical
  by_cases hroom : supportFloor + 3 < 6
  · exact crux.supportFloor_add_two_le_card_chartArgmaxFamily tightVec hunit hEigen supportFloor
      hroom hsupport multiplier hassembly
  · have heq : supportFloor = 3 := by omega
    subst heq
    obtain ⟨patched, hpatchedEq, hpatchedOff⟩ :
        ∃ patched : Finset (Fin 6) → (Fin 3 → ℝ),
          (∀ selected : Finset (Fin 6), selected.card = 3 → patched selected = tightVec selected)
            ∧ (∀ selected : Finset (Fin 6), selected.card ≠ 3 →
                patched selected = fun _ => (1 : ℝ)) :=
      ⟨fun selected => if selected.card = 3 then tightVec selected else fun _ => (1 : ℝ),
        fun selected hcard => if_pos hcard, fun selected hcard => if_neg hcard⟩
    have hunitPatched : ∀ selected : Finset (Fin 6), selected.card = 3 →
        patched selected ⬝ᵥ patched selected = 1 := by
      intro selected hcard
      rw [hpatchedEq selected hcard]
      exact hunit selected hcard
    have hEigenPatched : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
        (chartPointGap (chartPointOfDesign crux.design)).submatrix
            (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ patched selected
          = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
              (chartPointOfDesign crux.design).weight) :
              (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • patched selected := by
      intro selected hcard
      rw [hpatchedEq selected hcard]
      exact hEigen selected hcard
    have hfullPatched : ∀ (selected : Finset (Fin 6)) (blockIndex : Fin 3),
        patched selected blockIndex ≠ 0 := by
      intro selected blockIndex
      by_cases hcard : selected.card = 3
      · rw [hpatchedEq selected hcard]
        exact forall_ne_zero_of_card_totalTightSupport tightVec hcard
          (hsupport selected hcard) blockIndex
      · rw [hpatchedOff selected hcard]
        norm_num
    have hassemblyPatched : ∀ atomIndex : Fin 6,
        ∑ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
          multiplier selected * totalEigenSquareRow patched selected atomIndex
            = (((6 : ℕ) : ℝ))⁻¹ := by
      intro atomIndex
      rw [← hassembly atomIndex]
      refine Finset.sum_congr rfl fun selected hmem => ?_
      have hcard : selected.card = 3 :=
        ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmem).1
      rw [totalEigenSquareRow_of_card patched hcard, totalEigenSquareRow_of_card tightVec hcard,
        hpatchedEq selected hcard]
    have hfive := crux.five_le_card_chartArgmaxFamily_of_assemblyDiagonal patched hunitPatched
      hEigenPatched hfullPatched multiplier hassemblyPatched
    omega

/-! ### The hypotheses are inhabited

Precedent P4: a second-order escape once landed asking for flatness at twenty blocks at
once -- twenty linear conditions on a five-dimensional space, true and useless.  So the two
hypothesis bundles that are not about a crux are shown SATISFIABLE. -/

/-- **P4 NON-VACUITY FOR THE KILL.**  Every side condition of the support-pair kill except the
support hypothesis itself is satisfiable together with a NONZERO direction, so the kill is
not a statement about an empty configuration and the support hypothesis is what does the
work. -/
theorem exists_supportPairKill_datum_nontrivial :
    ∃ (row direction : Fin 6 → ℝ) (positiveAtom zeroAtom : Fin 6),
      row positiveAtom ≠ row zeroAtom
        ∧ (∑ atomIndex, direction atomIndex = 0)
        ∧ row ⬝ᵥ direction = 0
        ∧ direction ≠ 0
        ∧ ¬ ∀ atomIndex : Fin 6, atomIndex ≠ positiveAtom → atomIndex ≠ zeroAtom →
              direction atomIndex = 0 := by
  refine ⟨![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, -1], 3, 4, by simp, ?_, ?_, ?_, ?_⟩
  · simp [Fin.sum_univ_six]
  · simp [dotProduct, Fin.sum_univ_six]
  · intro hzero
    have hentry := congrFun hzero 4
    simp at hentry
  · intro hsupport
    have hentry := hsupport 5 (by decide) (by decide)
    simp at hentry

/-- **P4 NON-VACUITY FOR THE SUPPORT-TWO RUNG, AND ITS SEPARATION FROM THE SHIPPED ONE.**  A
tight family whose support is at least two at every block and which FAILS full support.  So
the rung above is not a restatement of the shipped floor under a heavier hypothesis: its
hypothesis class is strictly larger. -/
theorem exists_supportTwo_tightVec_not_fullSupport :
    ∃ tightVec : Finset (Fin 6) → (Fin 3 → ℝ),
      (∀ selected : Finset (Fin 6), selected.card = 3 →
          2 ≤ (totalTightSupport tightVec selected).card)
        ∧ ¬ ∀ (selected : Finset (Fin 6)) (blockIndex : Fin 3),
              tightVec selected blockIndex ≠ 0 := by
  refine ⟨fun _ => ![1, 1, 0], fun selected hcard => ?_, ?_⟩
  · exact two_le_card_totalTightSupport _ hcard (firstIndex := 0) (secondIndex := 1)
      (by decide) (by norm_num) (by norm_num)
  · intro hfull
    exact hfull ∅ 2 (by simp)

/-! ## The vanishing-pairing layer -/

/-- **THE DEGREE CAP ON THE ORTHOGONALITY GRAPH.**  No atom of a design with strictly
dominating co-singletons is orthogonal to every other atom.

Evaluating the co-singleton at the atom itself turns `S_{cᶜ} - 1 > 0` into
`sum over other atoms of the squared pairing > leverage`; an atom orthogonal to all the
others makes the left side zero while the right side is positive.  General in
`(size, rank)`, and it consumes nothing but the co-singleton. -/
theorem exists_dotProduct_ne_zero_of_hasStrictlyDominatingCoSingletons {m k : ℕ}
    (D : WeightedDesign m k) (hco : HasStrictlyDominatingCoSingletons D)
    (atomIndex : Fin m) (hheavy : 0 < leverageOf (D.atom atomIndex)) :
    ∃ other : Fin m, other ≠ atomIndex ∧ D.atom atomIndex ⬝ᵥ D.atom other ≠ 0 := by
  classical
  by_contra hcontra
  have hzero : ∀ other ∈ ({atomIndex}ᶜ : Finset (Fin m)),
      (D.atom other ⬝ᵥ D.atom atomIndex) ^ 2 = 0 := by
    intro other hmem
    have hother : other ≠ atomIndex := by
      simpa using Finset.mem_compl.mp hmem
    have hpairing : D.atom atomIndex ⬝ᵥ D.atom other = 0 := by
      by_contra hne
      exact hcontra ⟨other, hother, hne⟩
    rw [dotProduct_comm, hpairing]
    ring
  have hatomNe : D.atom atomIndex ≠ 0 := by
    intro hzeroAtom
    rw [hzeroAtom] at hheavy
    simp [leverageOf] at hheavy
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp (hco atomIndex)).2 hatomNe
  simp only [star_trivial] at hform
  rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
    Matrix.one_mulVec, Finset.sum_eq_zero hzero, ← leverageOf_eq_dotProduct] at hform
  linarith

/-- **AT A CRUX EVERY ATOM HAS A NONZERO PAIRING.**  The degree cap at `(6,3)`: the
orthogonality graph of a crux has maximum degree at most four.  With the shipped
triangle-freeness (`Gtz.SixThreeCrux.hasNoOrthogonalTriple`) this is the state of the
standing question of how many pairings can vanish; the honest position is that neither
bound improves the Mantel count of nine, and the header records where the remaining route
runs out. -/
theorem SixThreeCrux.exists_atomPairing_ne_zero (crux : SixThreeCrux) (atomIndex : Fin 6) :
    ∃ other : Fin 6, other ≠ atomIndex ∧ atomPairing crux.design atomIndex other ≠ 0 :=
  exists_dotProduct_ne_zero_of_hasStrictlyDominatingCoSingletons crux.design
    crux.hasStrictlyDominatingCoSingletons atomIndex
    (lt_trans one_pos (crux.isAllHeavy atomIndex))

/-- **AN ORTHOGONAL EDGE CANNOT BE SIGN-SATURATED.**  At a vanishing pairing the shipped
`Gtz.sum_erasePair_eq_zero_of_atomPairing_eq_zero` makes the weighted star products cancel,
so with strictly positive weights they can be neither all strictly positive nor all
strictly negative.  The third atom is what makes the index set nonempty and is the only
size input.

`Gtz.Quantitative.TwoGraphCollision` states this conclusion in its own prose -- "an
orthogonal edge cannot be sign-saturated AT ALL, in either parity" -- as the reading of its
theorem; here it is the theorem. -/
theorem exists_nonpos_and_exists_nonneg_erasePair_of_atomPairing_eq_zero {sizeIndex : ℕ}
    (design : WeightedDesign sizeIndex 3)
    {edgeFirst edgeSecond thirdAtom : Fin sizeIndex} (hedge : edgeFirst ≠ edgeSecond)
    (hthirdFirst : thirdAtom ≠ edgeFirst) (hthirdSecond : thirdAtom ≠ edgeSecond)
    (hzero : atomPairing design edgeFirst edgeSecond = 0) :
    (∃ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
        atomPairing design edgeFirst other * atomPairing design other edgeSecond ≤ 0)
      ∧ ∃ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
        0 ≤ atomPairing design edgeFirst other * atomPairing design other edgeSecond := by
  classical
  have hmemThird : thirdAtom ∈ (Finset.univ.erase edgeFirst).erase edgeSecond :=
    Finset.mem_erase.mpr ⟨hthirdSecond, Finset.mem_erase.mpr ⟨hthirdFirst, Finset.mem_univ _⟩⟩
  have hbalance := sum_erasePair_eq_zero_of_atomPairing_eq_zero design hedge hzero
  constructor
  · by_contra hcontra
    have hpositive : ∀ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
        0 < design.weight other
          * (atomPairing design edgeFirst other * atomPairing design other edgeSecond) := by
      intro other hmem
      refine mul_pos (design.weight_pos other) ?_
      by_contra hle
      exact hcontra ⟨other, hmem, not_lt.mp hle⟩
    rw [Finset.sum_eq_zero_iff_of_nonneg fun other hmem => le_of_lt (hpositive other hmem)]
      at hbalance
    exact absurd (hbalance thirdAtom hmemThird) (ne_of_gt (hpositive thirdAtom hmemThird))
  · by_contra hcontra
    have hnegative : ∀ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
        design.weight other
            * (atomPairing design edgeFirst other * atomPairing design other edgeSecond) < 0 := by
      intro other hmem
      refine mul_neg_of_pos_of_neg (design.weight_pos other) ?_
      by_contra hle
      exact hcontra ⟨other, hmem, not_lt.mp hle⟩
    have hsumNeg := Finset.sum_lt_sum_of_nonempty ⟨thirdAtom, hmemThird⟩ hnegative
    rw [hbalance, Finset.sum_const_zero] at hsumNeg
    exact lt_irrefl 0 hsumNeg

end Gtz
