/-
# The anchor assembly, and the reach obligation reduced to connectivity

Writes the step that `AnchorAssembly` recorded as unwritten: reindex the
axis-aligned core and the single-plane tail along
`Fin (rank + extra) = Fin rank (+) Fin extra`, balance Parseval through
`coreTailBookkeeping_feasible`, and hand the result to
`windowAnchorReachFree_of_weakWitness` together with
`exists_strictAnchor_of_weakDominator`.

The design built here is one explicit object.  Its first `rank` atoms sit on
the coordinate axes at a common length `sqrt coreScaleSq`, and its last `extra`
atoms sit in the coordinate 2-plane spanned by the first two axes, at pairwise
distinct nonzero slopes.  Three facts make it a design and an anchor:

* Parseval splits along the block index, the core block contributing
  `diagonal (coreWeight * coreScaleSq)` (`sum_core_atomMatrix`) and the tail
  block `diagonal (tailShrink * tailProfile)` (`sum_tail_atomMatrix`), and the
  bookkeeping equation makes the two diagonals add to the identity.
* No two atoms are parallel: distinct axes disagree, distinct slopes disagree,
  and an axis vector has ONE nonzero coordinate where a tail atom has TWO.
* The core labels dominate weakly, because their unweighted sum is exactly
  `coreScaleSq` times the identity and the bookkeeping pins `1 <= coreScaleSq`.

The floor is `rank + 2 <= size`, that is `2 <= extra`, which is the sharp guard
of `diagonalTailAtCell_of_two_le`.  It is far below the canonical window, so the
anchor exists at every window cell of every rank at least two, with no window
hypothesis at all.

What is left of the reach obligation is therefore ONE statement, named here as
`SharpWindowParallelFreeConnectivity`: every parallel-free design at a window
cell is joined to every parallel-free anchor by a parallel-free path.  The
reduction theorems below turn the anchor-reach obligation into exactly that,
at rank three and above.
-/
import Gtz.Uniform.AnchorAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz
namespace UniformPositionBridge

open Matrix Finset

/-! ## The block index calculus

`Fin (leftCount + rightCount)` splits into the two blocks by value.  Nothing
below uses an equivalence: `Fin.castAdd` and `Fin.natAdd` name the blocks,
`Fin.addCases` builds families over them, and `Fin.sum_univ_add` splits sums. -/

/-- Every index of the sum type is in one block or the other. -/
theorem eq_castAdd_or_natAdd {leftCount rightCount : ℕ}
    (index : Fin (leftCount + rightCount)) :
    (∃ leftIndex : Fin leftCount, index = Fin.castAdd rightCount leftIndex)
      ∨ ∃ rightIndex : Fin rightCount, index = Fin.natAdd leftCount rightIndex := by
  rcases lt_or_ge (index : ℕ) leftCount with hlow | hhigh
  · exact Or.inl ⟨⟨(index : ℕ), hlow⟩, Fin.ext rfl⟩
  · have hbound : (index : ℕ) - leftCount < rightCount := by
      have hlt := index.isLt
      omega
    refine Or.inr ⟨⟨(index : ℕ) - leftCount, hbound⟩, Fin.ext ?_⟩
    simp only [Fin.val_natAdd]
    omega

/-- The two blocks are disjoint. -/
theorem castAdd_ne_natAdd {leftCount rightCount : ℕ} (leftIndex : Fin leftCount)
    (rightIndex : Fin rightCount) :
    Fin.castAdd rightCount leftIndex ≠ Fin.natAdd leftCount rightIndex := by
  intro hcollide
  have hval := congrArg Fin.val hcollide
  have hlt := leftIndex.isLt
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

/-! ## The tail's diagonal profile, for an arbitrary coefficient family

`sum_tail_atomMatrix` proves the tail block diagonal for ANY coefficient and
weight families whose weighted coefficients cancel.  Its diagonal is named here
so the Parseval balance can quantify over it. -/

/-- The diagonal that the tail block contributes: the total weight on the
leading axis, the weighted squared slopes on the second axis, nothing else. -/
noncomputable def tailProfile (rank : ℕ) {extra : ℕ} (coeff weight : Fin extra → ℝ) :
    Fin rank → ℝ :=
  fun coord =>
    if (coord : ℕ) = 0 then ∑ slot, weight slot
    else if (coord : ℕ) = 1 then ∑ slot, weight slot * coeff slot ^ 2
    else 0

theorem tailProfile_nonneg {rank extra : ℕ} {coeff weight : Fin extra → ℝ}
    (hweightPos : ∀ slot, 0 < weight slot) (coord : Fin rank) :
    0 ≤ tailProfile rank coeff weight coord := by
  rw [tailProfile]
  split
  · exact Finset.sum_nonneg fun slot _ => (hweightPos slot).le
  · split
    · exact Finset.sum_nonneg fun slot _ =>
        mul_nonneg (hweightPos slot).le (sq_nonneg _)
    · exact le_refl 0

/-- Shrinking every tail weight by one factor shrinks the profile by that
factor. -/
theorem tailProfile_const_smul {rank extra : ℕ} (scale : ℝ) (coeff weight : Fin extra → ℝ)
    (coord : Fin rank) :
    tailProfile rank coeff (fun slot => scale * weight slot) coord
      = scale * tailProfile rank coeff weight coord := by
  rw [tailProfile, tailProfile]
  by_cases hzero : (coord : ℕ) = 0
  · rw [if_pos hzero, if_pos hzero, Finset.mul_sum]
  · rw [if_neg hzero, if_neg hzero]
    by_cases hone : (coord : ℕ) = 1
    · rw [if_pos hone, if_pos hone, Finset.mul_sum]
      exact Finset.sum_congr rfl fun slot _ => by ring
    · rw [if_neg hone, if_neg hone, mul_zero]

/-- `sum_tail_atomMatrix` with its diagonal named. -/
theorem sum_tail_atomMatrix_profile {rank extra : ℕ} (coeff weight : Fin extra → ℝ)
    (hcancel : ∑ slot, weight slot * coeff slot = 0) :
    (∑ slot, weight slot • atomMatrix (tailAtomVec (rank := rank) (coeff slot)))
      = Matrix.diagonal (tailProfile rank coeff weight) := by
  rw [sum_tail_atomMatrix coeff weight hcancel]
  rfl

/-- The named family of `AnchorAssembly` is the profile of its own coefficients
and weights. -/
theorem tailDiagonalProfile_eq_tailProfile (rank tailCount : ℕ) :
    tailDiagonalProfile rank tailCount
      = tailProfile rank (tailCoeff tailCount) (tailRawWeight tailCount) := rfl

/-! ## The core block, unweighted

Weak domination reads the core labels with weight one, so the unweighted core
sum is recorded on its own. -/

theorem diagonal_const_eq_smul_one {rank : ℕ} (value : ℝ) :
    Matrix.diagonal (fun _ : Fin rank => value)
      = value • (1 : Matrix (Fin rank) (Fin rank) ℝ) := by
  ext rowIndex colIndex
  by_cases hsame : rowIndex = colIndex <;> simp [hsame]

/-- **The core block is a multiple of the identity.**  Every core atom has
squared length `coreScaleSq` on its own axis, so the unweighted core sum is
`coreScaleSq` times the identity — domination needs no eigenvalue. -/
theorem sum_coreAtomMatrix_eq_smul_one {rank : ℕ} {coreScaleSq : ℝ}
    (hscaleNonneg : 0 ≤ coreScaleSq) :
    (∑ axis : Fin rank, atomMatrix (coreAtomVec coreScaleSq axis))
      = coreScaleSq • (1 : Matrix (Fin rank) (Fin rank) ℝ) := by
  have hweighted := sum_core_atomMatrix hscaleNonneg (fun _ : Fin rank => (1 : ℝ))
  simp only [one_smul, one_mul] at hweighted
  rw [hweighted, diagonal_const_eq_smul_one]

/-! ## Non-parallelism, in both orders

`AnchorAssembly` proves a tail atom is off every core line.  `HasParallelPair`
reads the pair in one fixed order, so the reverse is needed too. -/

/-- A core atom is off every tail line: were it a multiple, the multiplier
would be nonzero (a core atom is not the zero vector), and inverting it would
put the tail atom on a core line. -/
theorem coreAtomVec_ne_smul_tailAtomVec {rank : ℕ} (hrank : 2 ≤ rank) {coreScaleSq : ℝ}
    (hscalePos : 0 < coreScaleSq) {coeff : ℝ} (hcoeff : coeff ≠ 0) (axis : Fin rank)
    (ratio : ℝ) :
    coreAtomVec coreScaleSq axis ≠ ratio • tailAtomVec (rank := rank) coeff := by
  intro hparallel
  rcases eq_or_ne ratio 0 with rfl | hratioNe
  · have hatAxis := congrFun hparallel axis
    rw [coreAtomVec_apply, if_pos rfl, Pi.smul_apply, smul_eq_mul, zero_mul] at hatAxis
    exact absurd hatAxis (ne_of_gt (Real.sqrt_pos.mpr hscalePos))
  · refine tailAtomVec_ne_smul_coreAtomVec (coreScaleSq := coreScaleSq) hrank hcoeff axis
      ratio⁻¹ ?_
    rw [hparallel, smul_smul, inv_mul_cancel₀ hratioNe, one_smul]

/-! ## The core-tail atom and weight families -/

/-- The atom family: core atoms on the first block, tail atoms on the second. -/
noncomputable def coreTailAtomFamily (rank extra : ℕ) (coreScaleSq : ℝ)
    (coeff : Fin extra → ℝ) : Fin (rank + extra) → (Fin rank → ℝ) :=
  Fin.addCases (fun axis => coreAtomVec coreScaleSq axis)
    (fun slot => tailAtomVec (coeff slot))

/-- The weight family: the forced core weights on the first block, the shrunk
tail weights on the second. -/
noncomputable def coreTailWeightFamily (rank extra : ℕ) (coreWeight : Fin rank → ℝ)
    (tailShrink : ℝ) (weight : Fin extra → ℝ) : Fin (rank + extra) → ℝ :=
  Fin.addCases coreWeight (fun slot => tailShrink * weight slot)

@[simp] theorem coreTailAtomFamily_castAdd (rank extra : ℕ) (coreScaleSq : ℝ)
    (coeff : Fin extra → ℝ) (axis : Fin rank) :
    coreTailAtomFamily rank extra coreScaleSq coeff (Fin.castAdd extra axis)
      = coreAtomVec coreScaleSq axis :=
  Fin.addCases_left axis

@[simp] theorem coreTailAtomFamily_natAdd (rank extra : ℕ) (coreScaleSq : ℝ)
    (coeff : Fin extra → ℝ) (slot : Fin extra) :
    coreTailAtomFamily rank extra coreScaleSq coeff (Fin.natAdd rank slot)
      = tailAtomVec (coeff slot) :=
  Fin.addCases_right slot

@[simp] theorem coreTailWeightFamily_castAdd (rank extra : ℕ) (coreWeight : Fin rank → ℝ)
    (tailShrink : ℝ) (weight : Fin extra → ℝ) (axis : Fin rank) :
    coreTailWeightFamily rank extra coreWeight tailShrink weight (Fin.castAdd extra axis)
      = coreWeight axis :=
  Fin.addCases_left axis

@[simp] theorem coreTailWeightFamily_natAdd (rank extra : ℕ) (coreWeight : Fin rank → ℝ)
    (tailShrink : ℝ) (weight : Fin extra → ℝ) (slot : Fin extra) :
    coreTailWeightFamily rank extra coreWeight tailShrink weight (Fin.natAdd rank slot)
      = tailShrink * weight slot :=
  Fin.addCases_right slot

/-- **The atom family is parallel-free.**  Four cases: two core atoms disagree
on their axes, two tail atoms disagree on their slopes, and a core atom and a
tail atom disagree because one has a single nonzero coordinate and the other
two. -/
theorem coreTailAtomFamily_noParallel {rank extra : ℕ} (hrank : 2 ≤ rank)
    {coreScaleSq : ℝ} (hscalePos : 0 < coreScaleSq) {coeff : Fin extra → ℝ}
    (hcoeffNeZero : ∀ slot, coeff slot ≠ 0) (hcoeffInjective : Function.Injective coeff)
    {keptLabel dropLabel : Fin (rank + extra)} (hdistinct : keptLabel ≠ dropLabel)
    (ratio : ℝ) :
    coreTailAtomFamily rank extra coreScaleSq coeff dropLabel
      ≠ ratio • coreTailAtomFamily rank extra coreScaleSq coeff keptLabel := by
  rcases eq_castAdd_or_natAdd keptLabel with ⟨keptAxis, rfl⟩ | ⟨keptSlot, rfl⟩ <;>
    rcases eq_castAdd_or_natAdd dropLabel with ⟨dropAxis, rfl⟩ | ⟨dropSlot, rfl⟩
  · rw [coreTailAtomFamily_castAdd, coreTailAtomFamily_castAdd]
    exact coreAtomVec_ne_smul_coreAtomVec hscalePos
      (fun hsame => hdistinct (congrArg (Fin.castAdd extra) hsame.symm)) ratio
  · rw [coreTailAtomFamily_castAdd, coreTailAtomFamily_natAdd]
    exact tailAtomVec_ne_smul_coreAtomVec hrank (hcoeffNeZero dropSlot) keptAxis ratio
  · rw [coreTailAtomFamily_castAdd, coreTailAtomFamily_natAdd]
    exact coreAtomVec_ne_smul_tailAtomVec hrank hscalePos (hcoeffNeZero keptSlot)
      dropAxis ratio
  · rw [coreTailAtomFamily_natAdd, coreTailAtomFamily_natAdd]
    refine tailAtomVec_ne_smul_tailAtomVec hrank (fun hsame => ?_) ratio
    exact hdistinct (congrArg (Fin.natAdd rank) (hcoeffInjective hsame).symm)

/-! ## The core labels, and their unweighted sum -/

/-- The first block, as a subset of labels. -/
def coreLabels (rank extra : ℕ) : Finset (Fin (rank + extra)) :=
  Finset.map ⟨Fin.castAdd extra, Fin.castAdd_injective rank extra⟩ Finset.univ

@[simp] theorem card_coreLabels (rank extra : ℕ) : (coreLabels rank extra).card = rank := by
  rw [coreLabels, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- On the core labels the family's unweighted sum is `coreScaleSq` times the
identity, whatever the tail is. -/
theorem sum_coreLabels_atomMatrix {rank extra : ℕ} {coreScaleSq : ℝ}
    (hscaleNonneg : 0 ≤ coreScaleSq) (coeff : Fin extra → ℝ) :
    (∑ label ∈ coreLabels rank extra,
        atomMatrix (coreTailAtomFamily rank extra coreScaleSq coeff label))
      = coreScaleSq • (1 : Matrix (Fin rank) (Fin rank) ℝ) := by
  rw [coreLabels, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, coreTailAtomFamily_castAdd]
  exact sum_coreAtomMatrix_eq_smul_one hscaleNonneg

/-! ## The design

The Parseval identity is the whole content: the block split sends the core
atoms to `sum_core_atomMatrix` and the tail atoms to `sum_tail_atomMatrix`, and
the bookkeeping equation adds the two diagonals to the identity. -/

/-- **The core-tail design.**  The bookkeeping data is a hypothesis here, so
this definition is independent of how the data is produced —
`coreTailBookkeeping_feasible` produces it at every rank at least two. -/
noncomputable def coreTailDesign {rank extra : ℕ} {coreScaleSq tailShrink : ℝ}
    (coreWeight : Fin rank → ℝ) (coeff weight : Fin extra → ℝ)
    (hscaleNonneg : 0 ≤ coreScaleSq) (hcoreWeightPos : ∀ axis, 0 < coreWeight axis)
    (hshrinkPos : 0 < tailShrink) (hweightPos : ∀ slot, 0 < weight slot)
    (hcancel : ∑ slot, weight slot * coeff slot = 0)
    (hforced : ∀ axis, coreWeight axis * coreScaleSq
      = 1 - tailShrink * tailProfile rank coeff weight axis)
    (hmass : (∑ axis, coreWeight axis) + tailShrink * (∑ slot, weight slot) = 1) :
    WeightedDesign (rank + extra) rank where
  atom := coreTailAtomFamily rank extra coreScaleSq coeff
  weight := coreTailWeightFamily rank extra coreWeight tailShrink weight
  weight_pos := by
    intro label
    rcases eq_castAdd_or_natAdd label with ⟨axis, rfl⟩ | ⟨slot, rfl⟩
    · rw [coreTailWeightFamily_castAdd]
      exact hcoreWeightPos axis
    · rw [coreTailWeightFamily_natAdd]
      exact mul_pos hshrinkPos (hweightPos slot)
  weight_sum_one := by
    rw [Fin.sum_univ_add]
    simp only [coreTailWeightFamily_castAdd, coreTailWeightFamily_natAdd]
    rw [← Finset.mul_sum]
    exact hmass
  isParseval := by
    rw [Fin.sum_univ_add]
    simp only [coreTailWeightFamily_castAdd, coreTailWeightFamily_natAdd,
      coreTailAtomFamily_castAdd, coreTailAtomFamily_natAdd]
    have hcancelShrunk : ∑ slot, (tailShrink * weight slot) * coeff slot = 0 := by
      have hregroup : ∀ slot : Fin extra, (tailShrink * weight slot) * coeff slot
          = tailShrink * (weight slot * coeff slot) := fun slot => by ring
      rw [Finset.sum_congr rfl fun slot _ => hregroup slot, ← Finset.mul_sum, hcancel, mul_zero]
    rw [sum_core_atomMatrix hscaleNonneg coreWeight,
      sum_tail_atomMatrix_profile coeff (fun slot => tailShrink * weight slot) hcancelShrunk,
      Matrix.diagonal_add]
    have hunit : (fun axis : Fin rank => coreWeight axis * coreScaleSq
        + tailProfile rank coeff (fun slot => tailShrink * weight slot) axis)
        = fun _ : Fin rank => (1 : ℝ) := by
      funext axis
      rw [hforced axis, tailProfile_const_smul]
      ring
    rw [hunit, Matrix.diagonal_one]

@[simp] theorem coreTailDesign_atom {rank extra : ℕ} {coreScaleSq tailShrink : ℝ}
    (coreWeight : Fin rank → ℝ) (coeff weight : Fin extra → ℝ)
    (hscaleNonneg : 0 ≤ coreScaleSq) (hcoreWeightPos : ∀ axis, 0 < coreWeight axis)
    (hshrinkPos : 0 < tailShrink) (hweightPos : ∀ slot, 0 < weight slot)
    (hcancel : ∑ slot, weight slot * coeff slot = 0)
    (hforced : ∀ axis, coreWeight axis * coreScaleSq
      = 1 - tailShrink * tailProfile rank coeff weight axis)
    (hmass : (∑ axis, coreWeight axis) + tailShrink * (∑ slot, weight slot) = 1) :
    (coreTailDesign coreWeight coeff weight hscaleNonneg hcoreWeightPos hshrinkPos
        hweightPos hcancel hforced hmass).atom
      = coreTailAtomFamily rank extra coreScaleSq coeff := rfl

/-! ## The weak witness, at every cell above the corank-two floor -/

/-- **THE ASSEMBLY.**  For an arbitrary tail family whose weighted slopes cancel,
the core-tail design exists, is parallel-free, and its core labels dominate
weakly.  This is the step `AnchorAssembly` recorded as unwritten. -/
theorem exists_coreTailWitness {rank extra : ℕ} (hrank : 2 ≤ rank) (hextra : 0 < extra)
    (coeff weight : Fin extra → ℝ) (hweightPos : ∀ slot, 0 < weight slot)
    (hcoeffNeZero : ∀ slot, coeff slot ≠ 0) (hcoeffInjective : Function.Injective coeff)
    (hcancel : ∑ slot, weight slot * coeff slot = 0) :
    ∃ design : WeightedDesign (rank + extra) rank,
      ¬ HasParallelPair design
        ∧ ∃ chosen : Finset (Fin (rank + extra)),
            chosen.card = rank ∧ Dominates design chosen := by
  have hslotsNonempty : (Finset.univ : Finset (Fin extra)).Nonempty := by
    refine Finset.card_pos.mp ?_
    rw [Finset.card_univ, Fintype.card_fin]
    exact hextra
  have htailMassPos : 0 < ∑ slot, weight slot :=
    Finset.sum_pos (fun slot _ => hweightPos slot) hslotsNonempty
  obtain ⟨tailShrink, coreScaleSq, coreWeight, hshrinkPos, hcoreScaleGeOne, hcoreWeightPos,
      hforced, hmass⟩ :=
    coreTailBookkeeping_feasible hrank (tailProfile rank coeff weight)
      (fun coord => tailProfile_nonneg hweightPos coord) (∑ slot, weight slot) htailMassPos
  have hscalePos : (0 : ℝ) < coreScaleSq := by linarith
  refine ⟨coreTailDesign coreWeight coeff weight hscalePos.le hcoreWeightPos hshrinkPos
    hweightPos hcancel hforced hmass, ?_, coreLabels rank extra, card_coreLabels rank extra, ?_⟩
  · rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
    exact coreTailAtomFamily_noParallel hrank hscalePos hcoeffNeZero hcoeffInjective
      hdistinct ratio hparallel
  · have hsubset : subsetSum (coreTailDesign coreWeight coeff weight hscalePos.le
        hcoreWeightPos hshrinkPos hweightPos hcancel hforced hmass) (coreLabels rank extra)
        = coreScaleSq • (1 : Matrix (Fin rank) (Fin rank) ℝ) := by
      rw [subsetSum]
      simp only [coreTailDesign_atom]
      exact sum_coreLabels_atomMatrix hscalePos.le coeff
    rw [Dominates, hsubset]
    exact posSemidef_smul_one_sub_one hcoreScaleGeOne

/-- **The witness at the named tail family.**  The telescoping family of
`AnchorAssembly` satisfies every hypothesis of the assembly at each tail count
at least one. -/
theorem exists_coreTailWitness_named {rank tailCount : ℕ} (hrank : 2 ≤ rank)
    (hcount : 1 ≤ tailCount) :
    ∃ design : WeightedDesign (rank + (tailCount + 1)) rank,
      ¬ HasParallelPair design
        ∧ ∃ chosen : Finset (Fin (rank + (tailCount + 1))),
            chosen.card = rank ∧ Dominates design chosen :=
  exists_coreTailWitness hrank (Nat.succ_pos tailCount) (tailCoeff tailCount)
    (tailRawWeight tailCount) (tailRawWeight_pos hcount) (tailCoeff_ne_zero tailCount)
    (tailCoeff_injective tailCount) (sum_tailRawWeight_mul_tailCoeff tailCount)

/-- **THE WEAK WITNESS, at every cell with corank at least two.**  A
parallel-free design with a weakly dominating rank-subset exists at every
`(size, rank)` with `2 <= rank` and `rank + 2 <= size`.  The floor is the sharp
guard of `diagonalTailAtCell_of_two_le`: at `size = rank + 1` the tail has one
slot and `not_diagonalTailAtCell_one` refutes the single-plane tail. -/
theorem exists_weakParallelFreeDominator {size rank : ℕ} (hrank : 2 ≤ rank)
    (hsize : rank + 2 ≤ size) :
    ∃ design : WeightedDesign size rank,
      ¬ HasParallelPair design
        ∧ ∃ chosen : Finset (Fin size), chosen.card = rank ∧ Dominates design chosen := by
  obtain ⟨extra, rfl⟩ : ∃ extra : ℕ, size = rank + extra := ⟨size - rank, by omega⟩
  obtain ⟨tailCount, rfl⟩ : ∃ tailCount : ℕ, extra = tailCount + 1 := ⟨extra - 1, by omega⟩
  exact exists_coreTailWitness_named hrank (by omega)

/-- **THE ANCHOR, at every cell with corank at least two.**  The weak witness
rescales into a parallel-free design with a STRICTLY dominating rank-subset
(`exists_strictAnchor_of_weakDominator`).  No window hypothesis, no
connectivity, no eigenvalue estimate. -/
theorem exists_parallelFreeStrictAnchor {size rank : ℕ} (hrank : 2 ≤ rank)
    (hsize : rank + 2 ≤ size) :
    ∃ anchor : WeightedDesign size rank,
      ¬ HasParallelPair anchor ∧ HasStrictlyDominatingSubset anchor := by
  obtain ⟨design, hfree, chosen, hcard, hdominates⟩ :=
    exists_weakParallelFreeDominator hrank hsize
  exact exists_strictAnchor_of_weakDominator (by omega) design hfree hcard hdominates

/-- **No cell above the corank-two floor is uniformly tied.**  The anchor has a
strictly dominating subset, so it is not a tie, and the parallel-free locus is
therefore nonempty at every such cell. -/
theorem exists_parallelFree_not_isTie {size rank : ℕ} (hrank : 2 ≤ rank)
    (hsize : rank + 2 ≤ size) :
    ∃ anchor : WeightedDesign size rank, ¬ HasParallelPair anchor ∧ ¬ IsTie anchor := by
  obtain ⟨anchor, hfree, hstrict⟩ := exists_parallelFreeStrictAnchor hrank hsize
  exact ⟨anchor, hfree, fun htie => (isTie_iff_dominating_and_not_strict.mp htie).2 hstrict⟩

/-- Every canonical-window cell lies above the floor, at every rank at least
two: the window starts at `2 * rank`. -/
theorem windowCell_above_anchorFloor {size rank : ℕ} (hrank : 2 ≤ rank)
    (hinside : InductionStep.IsInsideCanonicalWindow size rank) : rank + 2 ≤ size := by
  obtain ⟨hbelow, _⟩ := hinside
  omega

/-! ## The reach obligation, reduced to connectivity

With the anchor free at every cell, the two Props of route (b)'s topological
input collapse to ONE statement about the parallel-free locus. -/

/-- **THE RESIDUAL, over the canonical window.**  At every canonical-window
cell, every parallel-free design is joined to every parallel-free anchor by a
continuous parallel-free path.  Nothing about domination enters. -/
def CanonicalWindowParallelFreeConnectivity (rank : ℕ) : Prop :=
  ∀ size : ℕ, InductionStep.IsInsideCanonicalWindow size rank →
    ∀ anchor : WeightedDesign size rank, ¬ HasParallelPair anchor →
      ParallelFreeReachesAnchor size rank anchor

/-- **THE RESIDUAL, over the sharp window.**  The same statement over the range
that `Skeleton.obligationSharpWindowAnchorReachRankFourAndUp` quantifies, one
cell shorter at the top. -/
def SharpWindowParallelFreeConnectivity (rank : ℕ) : Prop :=
  ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
    ∀ anchor : WeightedDesign size rank, ¬ HasParallelPair anchor →
      ParallelFreeReachesAnchor size rank anchor

/-- The sharp window sits inside the canonical window. -/
theorem sharpWindowConnectivity_of_canonicalWindowConnectivity {rank : ℕ}
    (hconnect : CanonicalWindowParallelFreeConnectivity rank) :
    SharpWindowParallelFreeConnectivity rank :=
  fun size hbelow habove anchor hfree =>
    hconnect size ⟨hbelow, by omega⟩ anchor hfree

/-- **THE ANCHOR HALF IS GONE.**  At every rank at least three, connectivity
alone yields route (b)'s topological input in its strongest recorded form. -/
theorem windowAnchorReachFree_of_connectivity {rank : ℕ} (hrank : 3 ≤ rank)
    (hconnect : CanonicalWindowParallelFreeConnectivity rank) :
    WindowAnchorReachFree rank :=
  windowAnchorReachFree_of_weakWitness hrank
    (fun size hinside =>
      exists_weakParallelFreeDominator (by omega) (windowCell_above_anchorFloor (by omega) hinside))
    (fun size anchor hinside hfree => hconnect size hinside anchor hfree)

/-- Route (b)'s topological input, from connectivity alone. -/
theorem windowAnchorReach_of_connectivity {rank : ℕ} (hrank : 3 ≤ rank)
    (hconnect : CanonicalWindowParallelFreeConnectivity rank) : WindowAnchorReach rank :=
  windowAnchorReach_of_windowAnchorReachFree (windowAnchorReachFree_of_connectivity hrank hconnect)

/-- **THE REDUCTION, in the obligation's own shape.**  The sharp-window
anchor-reach statement follows from connectivity alone at every rank at least
three: the anchor is assembled here, the strict half is free by rescaling, and
the path is exactly what connectivity supplies. -/
theorem sharpWindowAnchorReach_of_connectivity {rank : ℕ} (hrank : 3 ≤ rank)
    (hconnect : SharpWindowParallelFreeConnectivity rank) :
    ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
      ∃ anchor : WeightedDesign size rank,
        HasStrictlyDominatingSubset anchor ∧ ParallelFreeReachesAnchor size rank anchor := by
  intro size hbelow habove
  obtain ⟨anchor, hanchorFree, hanchorStrict⟩ :=
    exists_parallelFreeStrictAnchor (rank := rank) (size := size) (by omega) (by omega)
  exact ⟨anchor, hanchorStrict, hconnect size hbelow habove anchor hanchorFree⟩

/-- **The rank-four-and-up obligation, reduced.**  Same statement as
`Skeleton.obligationSharpWindowAnchorReachRankFourAndUp`, with connectivity as
its only hypothesis.  The assembly half of that obligation is discharged. -/
theorem sharpWindowAnchorReachRankFourAndUp_of_connectivity
    (hconnect : ∀ rank : ℕ, 4 ≤ rank → SharpWindowParallelFreeConnectivity rank) :
    ∀ rank : ℕ, 4 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        ∃ anchor : WeightedDesign size rank,
          HasStrictlyDominatingSubset anchor ∧ ParallelFreeReachesAnchor size rank anchor :=
  fun rank hrank => sharpWindowAnchorReach_of_connectivity (by omega) (hconnect rank hrank)

/-! ## Route (b), with connectivity as its only topological input -/

/-- **ROUTE (b), RE-BASED.**  The relativized window hinge plus per-cell
connectivity of the parallel-free locus give weighted GTZ at every size and
every rank.  The anchor obligation has left the statement entirely. -/
theorem routeB_target_of_connectivity
    (hwindowTie : ∀ rank : ℕ, 3 ≤ rank → ParallelPairAtWindowTieRelative rank)
    (hconnect : ∀ rank : ℕ, 3 ≤ rank → CanonicalWindowParallelFreeConnectivity rank) :
    ∀ size rank : ℕ, 1 ≤ rank → rank ≤ size → GtzWeighted size rank :=
  routeB_target_relative hwindowTie
    (fun rank hrank => windowAnchorReach_of_connectivity hrank (hconnect rank hrank))

/-- The window closure at one rank, with connectivity as its only topological
input. -/
theorem closesCanonicalWindow_of_relativeWindowTie_of_connectivity (rank : ℕ) (hrank : 3 ≤ rank)
    (hwindowTie : ParallelPairAtWindowTieRelative rank)
    (hconnect : CanonicalWindowParallelFreeConnectivity rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) :
    InductionStep.ClosesCanonicalWindow rank :=
  closesCanonicalWindow_of_relativeWindowTie_of_reach rank hrank hwindowTie
    (windowAnchorReach_of_connectivity hrank hconnect) hpredecessor

/-! ## Cross-checks

The assembly is not vacuous and not window-bound. -/

/-- **Rank-three cross-check, at the window's bottom cell.**  The assembly
produces a parallel-free anchor with a strictly dominating subset at `(6,3)`,
built from nothing but the axis frame and three coplanar slopes — a second
anchor at the cell where `Gtz.icosaDesign` is the recorded one. -/
theorem exists_parallelFreeStrictAnchor_sixThree :
    ∃ anchor : WeightedDesign 6 3,
      ¬ HasParallelPair anchor ∧ HasStrictlyDominatingSubset anchor :=
  exists_parallelFreeStrictAnchor (by norm_num) (by norm_num)

/-- **Rank-four cross-check, at the window's bottom cell.**  The first cell of
the first open rank carries the anchor outright. -/
theorem exists_parallelFreeStrictAnchor_eightFour :
    ∃ anchor : WeightedDesign 8 4,
      ¬ HasParallelPair anchor ∧ HasStrictlyDominatingSubset anchor :=
  exists_parallelFreeStrictAnchor (by norm_num) (by norm_num)

/-- **The assembly reaches far below the window.**  The corank-two cell
`size = rank + 2` already carries the anchor, while the window starts at
`2 * rank`.  So the anchor is never the binding constraint on any route that
stays at corank two or above. -/
theorem exists_parallelFreeStrictAnchor_corankTwoCell {rank : ℕ} (hrank : 2 ≤ rank) :
    ∃ anchor : WeightedDesign (rank + 2) rank,
      ¬ HasParallelPair anchor ∧ HasStrictlyDominatingSubset anchor :=
  exists_parallelFreeStrictAnchor hrank (le_refl (rank + 2))

/-- **The rank-two refutation is not an instance.**  Connectivity is FALSE at
rank two (`not_windowAnchorReachFree_two`), and the reduction above respects
that: it carries `3 <= rank` throughout.  Recorded as a kernel fact — rank-two
connectivity would contradict the rank-two refutation. -/
theorem not_canonicalWindowParallelFreeConnectivity_two :
    ¬ CanonicalWindowParallelFreeConnectivity 2 := by
  intro hconnect
  obtain ⟨anchor, hanchorFree, hanchorStrict⟩ :=
    exists_parallelFreeStrictAnchor (rank := 2) (size := 4) (by norm_num) (by norm_num)
  exact not_parallelFreeReachesAnchor_rankTwo (size := 2) anchor hanchorFree
    (hconnect 4 ⟨by norm_num, by norm_num⟩ anchor hanchorFree)

end UniformPositionBridge
end Gtz
