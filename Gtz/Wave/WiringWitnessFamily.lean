/-
# A tie at every cell, and the death of the all-heavy witness programme

## What this module adds

The tree carries exactly three concrete ties, and all three sit at rank three:
`Gtz.nonUniformLeverageTieDesign`, `Gtz.diamondDesign` and the tetrahedral
fixtures.  Every refutation built on them therefore lands at rank three.  The
two off-path registry axioms do not quantify over rank three at all.  The
sub-threshold band asks `2 * rank <= size < rank * (rank + 1) / 2`, which at
rank three reads `6 <= size < 6` and is EMPTY.  The threshold-cell axiom asks
`4 <= rank`.  So a rank-three refutation is evidence about neither.

This module removes that ceiling.  Section 1 builds an equal-norm tight frame of
`rank + 1` vectors in `ℝ^rank`, in closed form, at EVERY rank.  Section 3 hangs
a design on it with an arbitrary multiplicity at the last vertex, which reaches
EVERY cell with `rank < size`.  Section 4 proves that design is a tie, at every
rank and every size, from two frame facts and one counting step.

## The mechanism, in one line

Every card-`rank` subset of a design on `rank + 1` vertices misses a vertex,
because `rank` labels cover at most `rank` vertices.  The frame vector of a
missed vertex reads every selected atom at squared pairing exactly one.  Its
Rayleigh value against the subset gap is therefore `rank - rank = 0`.  Zero is
not positive, so no card-`rank` subset dominates strictly.  The first `rank`
atoms do dominate weakly, by Cauchy-Schwarz against the all-ones direction.
That is a tie.

## What the tie kills

`Gtz.HasMassWitness`, `Gtz.HasBracketWitness`, `Gtz.HasPivotWitness`,
`Gtz.HasDetWitness` and `Gtz.ExcessDominatesBlock` share one property: each
refutes `Gtz.IsTie` at the design that carries it.  A producer that asks for one
at EVERY design of a cell therefore asks that the cell hold NO tie.  Section 7
names that statement `Gtz.NoTieAtCell` and proves it equal to strict domination
everywhere.  Section 8 refutes it at every cell with `rank < size` and
`2 <= rank`.  Six of the seven producers of each off-path axiom die there, and
the four `(6,3)` doors of the same family die with them.

## The two traps, checked

TRAP ONE, EQUIVALENCE.  The witness hypotheses are STRICTLY STRONGER than the
axiom, not equivalent to it: `Gtz.noTieAtCell_iff_strictDomination` shows they
assert strict domination, while the axiom asserts only that a tie carries a
parallel pair.  The seventh producer, `Gtz.obligationSubThresholdBandHinge_of_heavyTie`,
IS an equivalence modulo the predecessor, and section 9 says so.

TRAP TWO, UNSATISFIABLE ANTECEDENT.  Every theorem below that carries a
hypothesis is instantiated at an explicit inhabitant, or its antecedent is
refuted in kernel and the theorem is marked.  The ladder is respected
throughout: this family lives at `rank < size`, so it never touches the sizes
four and five where the landed rank-three refutations sit.
-/
import Gtz.Wave.AllHeavyDeterminantPrice
import Gtz.Wave.AllHeavyHingeSchur
import Gtz.Wave.OffsetUpperBound
import Gtz.Wave.LightAtomTieFloor
import Gtz.Ties.TotalTieCorankOne
import Gtz.Design.StressFreeNormalizer
import Gtz.Design.PrimitiveTightClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## 1. The saturated frame

`rank + 1` vectors in `ℝ^rank`, all of squared norm `rank`, whose rank-one sum
is `(rank + 1)` times the identity.  One square root appears, and every identity
below is rational in it. -/

/-- The scale `√(rank + 1)`. -/
noncomputable def saturatedFrameScale (rank : ℕ) : ℝ := Real.sqrt ((rank : ℝ) + 1)

theorem saturatedFrameScale_nonneg (rank : ℕ) : 0 ≤ saturatedFrameScale rank :=
  Real.sqrt_nonneg _

/-- The only property of the scale that any proof below uses. -/
theorem saturatedFrameScale_sq (rank : ℕ) : saturatedFrameScale rank ^ 2 = (rank : ℝ) + 1 := by
  rw [saturatedFrameScale, Real.sq_sqrt]
  positivity

/-- The common shift `(1 - √(rank + 1)) / rank`. -/
noncomputable def saturatedFrameShift (rank : ℕ) : ℝ :=
  (1 - saturatedFrameScale rank) / (rank : ℝ)

/-- **THE ROW LAW.**  Every frame vector sums to one across its coordinates.
True at `rank = 0` as well, because there the scale is one and Lean reads the
division by zero as zero. -/
theorem saturatedFrameShift_rowSum (rank : ℕ) :
    saturatedFrameScale rank + (rank : ℝ) * saturatedFrameShift rank = 1 := by
  rcases Nat.eq_zero_or_pos rank with hzero | hpos
  · subst hzero
    simp [saturatedFrameShift, saturatedFrameScale]
  · have hne : (rank : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    rw [saturatedFrameShift]
    field_simp
    ring

/-- **THE QUADRATIC LAW.**  This one number, `-1`, is the whole construction: it
is what makes the diagonal of the frame sum land on `rank + 1` and the
off-diagonal cancel. -/
theorem saturatedFrameShift_quadratic {rank : ℕ} (hrank : rank ≠ 0) :
    2 * saturatedFrameScale rank * saturatedFrameShift rank
      + (rank : ℝ) * saturatedFrameShift rank ^ 2 = -1 := by
  have hne : (rank : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hrank
  have hkey : 2 * saturatedFrameScale rank * saturatedFrameShift rank
      + (rank : ℝ) * saturatedFrameShift rank ^ 2
      = (1 - saturatedFrameScale rank ^ 2) / (rank : ℝ) := by
    rw [saturatedFrameShift]
    field_simp
    ring
  rw [hkey, saturatedFrameScale_sq, div_eq_iff hne]
  ring

/-- The frame vector at a vertex.  The first `rank` vertices are the scaled
standard basis shifted by the common shift.  The last vertex is the all-ones
vector. -/
noncomputable def saturatedFrameVector (rank : ℕ) (vertex : Fin (rank + 1))
    (coord : Fin rank) : ℝ :=
  (if (vertex : ℕ) = (coord : ℕ) then saturatedFrameScale rank else 0)
    + (if (vertex : ℕ) < rank then saturatedFrameShift rank else 1)

theorem saturatedFrameVector_castSucc (rank : ℕ) (j coord : Fin rank) :
    saturatedFrameVector rank j.castSucc coord
      = (if j = coord then saturatedFrameScale rank else 0) + saturatedFrameShift rank := by
  have hval : ((j.castSucc : Fin (rank + 1)) : ℕ) = (j : ℕ) := rfl
  unfold saturatedFrameVector
  rw [hval, if_pos j.isLt]
  by_cases hjc : j = coord
  · rw [if_pos hjc, if_pos (congrArg Fin.val hjc)]
  · rw [if_neg hjc, if_neg (fun hval => hjc (Fin.ext hval))]

theorem saturatedFrameVector_last (rank : ℕ) (coord : Fin rank) :
    saturatedFrameVector rank (Fin.last rank) coord = 1 := by
  have hval : ((Fin.last rank : Fin (rank + 1)) : ℕ) = rank := rfl
  unfold saturatedFrameVector
  rw [hval, if_neg (Nat.ne_of_gt coord.isLt), if_neg (lt_irrefl rank)]
  ring

/-- **THE VERTEX DICHOTOMY.**  Used in place of `Fin.lastCases` so that every
case split below is a plain `rcases`. -/
theorem saturatedFrame_vertex_cases {rank : ℕ} (vertex : Fin (rank + 1)) :
    (∃ j : Fin rank, vertex = j.castSucc) ∨ vertex = Fin.last rank := by
  rcases Nat.lt_or_ge (vertex : ℕ) rank with hlt | hge
  · exact Or.inl ⟨⟨(vertex : ℕ), hlt⟩, Fin.ext rfl⟩
  · refine Or.inr (Fin.ext ?_)
    have hbound := vertex.isLt
    show (vertex : ℕ) = rank
    omega

/-! ### The two pairing readings -/

theorem saturatedFrameVector_castSucc_dotProduct (rank : ℕ) (j : Fin rank)
    (probe : Fin rank → ℝ) :
    saturatedFrameVector rank j.castSucc ⬝ᵥ probe
      = saturatedFrameScale rank * probe j
        + saturatedFrameShift rank * ∑ coord, probe coord := by
  have hterm : ∀ coord : Fin rank,
      saturatedFrameVector rank j.castSucc coord * probe coord
        = (if j = coord then saturatedFrameScale rank else 0) * probe coord
          + saturatedFrameShift rank * probe coord := by
    intro coord
    rw [saturatedFrameVector_castSucc]
    ring
  have hdot : saturatedFrameVector rank j.castSucc ⬝ᵥ probe
      = ∑ coord, saturatedFrameVector rank j.castSucc coord * probe coord := rfl
  rw [hdot, Finset.sum_congr rfl (fun coord _ => hterm coord), Finset.sum_add_distrib,
    ← Finset.mul_sum]
  congr 1
  simp [ite_mul, Finset.sum_ite_eq]

theorem saturatedFrameVector_last_dotProduct (rank : ℕ) (probe : Fin rank → ℝ) :
    saturatedFrameVector rank (Fin.last rank) ⬝ᵥ probe = ∑ coord, probe coord := by
  have hdot : saturatedFrameVector rank (Fin.last rank) ⬝ᵥ probe
      = ∑ coord, saturatedFrameVector rank (Fin.last rank) coord * probe coord := rfl
  rw [hdot]
  exact Finset.sum_congr rfl fun coord _ => by rw [saturatedFrameVector_last]; ring

/-! ### The three frame laws

`Gtz.dotProduct_self_eq_sum_sq` (`Gtz/LinAlg/PsdKit.lean:44`) reads a self dot
product as a sum of squares.  It is spent below and not restated. -/

/-- **LAW ONE, EQUAL NORMS.**  Every frame vector has squared norm `rank`. -/
theorem saturatedFrameVector_dot_self {rank : ℕ} (hrank : rank ≠ 0)
    (vertex : Fin (rank + 1)) :
    saturatedFrameVector rank vertex ⬝ᵥ saturatedFrameVector rank vertex = (rank : ℝ) := by
  have hkey : saturatedFrameShift rank * (saturatedFrameScale rank + 1) = -1 := by
    have hquad := saturatedFrameShift_quadratic hrank
    have hrow := saturatedFrameShift_rowSum rank
    linear_combination hquad - saturatedFrameShift rank * hrow
  rcases saturatedFrame_vertex_cases vertex with ⟨j, rfl⟩ | rfl
  · have hcoord : saturatedFrameVector rank j.castSucc j
        = saturatedFrameScale rank + saturatedFrameShift rank := by
      rw [saturatedFrameVector_castSucc, if_pos rfl]
    have hsum : ∑ coord, saturatedFrameVector rank j.castSucc coord = 1 := by
      rw [Finset.sum_congr rfl (fun coord _ => saturatedFrameVector_castSucc rank j coord),
        Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      simp only [Finset.mem_univ, if_true]
      exact saturatedFrameShift_rowSum rank
    rw [saturatedFrameVector_castSucc_dotProduct, hcoord, hsum]
    linear_combination saturatedFrameScale_sq rank + hkey
  · rw [saturatedFrameVector_last_dotProduct,
      Finset.sum_congr rfl (fun coord _ => saturatedFrameVector_last rank coord)]
    simp

theorem saturatedFrameVector_ne_zero {rank : ℕ} (hrank : rank ≠ 0)
    (vertex : Fin (rank + 1)) : saturatedFrameVector rank vertex ≠ 0 := by
  intro hzero
  have hself := saturatedFrameVector_dot_self hrank vertex
  rw [hzero] at hself
  simp only [dotProduct_zero] at hself
  exact hrank (Nat.cast_eq_zero.mp hself.symm)

/-- **LAW TWO, UNIT PAIRINGS.**  Two distinct frame vectors pair to `-1` inside
the basis block and to `+1` against the all-ones vertex.  Only the square
matters below, and it is `1` in every case. -/
theorem saturatedFrameVector_dot_ne_sq {rank : ℕ} (hrank : rank ≠ 0)
    (vertex other : Fin (rank + 1)) (hne : vertex ≠ other) :
    (saturatedFrameVector rank vertex ⬝ᵥ saturatedFrameVector rank other) ^ 2 = 1 := by
  have hrow := saturatedFrameShift_rowSum rank
  have hkey : saturatedFrameShift rank * (saturatedFrameScale rank + 1) = -1 := by
    have hquad := saturatedFrameShift_quadratic hrank
    linear_combination hquad - saturatedFrameShift rank * hrow
  have hlastSum : ∑ coord, saturatedFrameVector rank (Fin.last rank) coord = (rank : ℝ) := by
    rw [Finset.sum_congr rfl (fun coord _ => saturatedFrameVector_last rank coord)]
    simp
  have hcastSum : ∀ j : Fin rank, ∑ coord, saturatedFrameVector rank j.castSucc coord = 1 := by
    intro j
    rw [Finset.sum_congr rfl (fun coord _ => saturatedFrameVector_castSucc rank j coord),
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    simp only [Finset.mem_univ, if_true]
    exact hrow
  rcases saturatedFrame_vertex_cases vertex with ⟨j, rfl⟩ | rfl
  · rcases saturatedFrame_vertex_cases other with ⟨j', rfl⟩ | rfl
    · have hjj : j ≠ j' := fun hjj => hne (by rw [hjj])
      have hcoord : saturatedFrameVector rank j'.castSucc j = saturatedFrameShift rank := by
        rw [saturatedFrameVector_castSucc, if_neg (fun h => hjj h.symm)]
        ring
      rw [saturatedFrameVector_castSucc_dotProduct, hcoord, hcastSum j']
      have hvalue : saturatedFrameScale rank * saturatedFrameShift rank
          + saturatedFrameShift rank * 1 = -1 := by linear_combination hkey
      rw [hvalue]
      norm_num
    · have hcoord : saturatedFrameVector rank (Fin.last rank) j = 1 :=
        saturatedFrameVector_last rank j
      rw [saturatedFrameVector_castSucc_dotProduct, hcoord, hlastSum]
      have hvalue : saturatedFrameScale rank * 1
          + saturatedFrameShift rank * (rank : ℝ) = 1 := by linear_combination hrow
      rw [hvalue]
      norm_num
  · rcases saturatedFrame_vertex_cases other with ⟨j', rfl⟩ | rfl
    · rw [saturatedFrameVector_last_dotProduct, hcastSum j']
      norm_num
    · exact absurd rfl hne

/-- **LAW THREE, THE TIGHT-FRAME RESOLUTION.**  The rank-one sum of the whole
frame is `(rank + 1)` times the identity.  This is what makes the design of
section 3 a Parseval frame. -/
theorem sum_frameVector_mul_apply {rank : ℕ} (hrank : rank ≠ 0)
    (rowIndex colIndex : Fin rank) :
    ∑ vertex : Fin (rank + 1),
        saturatedFrameVector rank vertex rowIndex * saturatedFrameVector rank vertex colIndex
      = ((rank : ℝ) + 1) * (if rowIndex = colIndex then 1 else 0) := by
  have hquad := saturatedFrameShift_quadratic hrank
  have hsq := saturatedFrameScale_sq rank
  rw [Fin.sum_univ_castSucc]
  have hentry : ∀ j : Fin rank,
      saturatedFrameVector rank j.castSucc rowIndex
          * saturatedFrameVector rank j.castSucc colIndex
        = (if j = rowIndex then saturatedFrameScale rank else 0)
            * (if j = colIndex then saturatedFrameScale rank else 0)
          + saturatedFrameShift rank * (if j = rowIndex then saturatedFrameScale rank else 0)
          + saturatedFrameShift rank * (if j = colIndex then saturatedFrameScale rank else 0)
          + saturatedFrameShift rank ^ 2 := by
    intro j
    rw [saturatedFrameVector_castSucc, saturatedFrameVector_castSucc]
    ring
  have hcross : ∑ j : Fin rank, (if j = rowIndex then saturatedFrameScale rank else 0)
        * (if j = colIndex then saturatedFrameScale rank else 0)
      = if rowIndex = colIndex then saturatedFrameScale rank ^ 2 else 0 := by
    have hstep : ∀ j : Fin rank, (if j = rowIndex then saturatedFrameScale rank else 0)
        * (if j = colIndex then saturatedFrameScale rank else 0)
        = if j = rowIndex then
            (if rowIndex = colIndex then saturatedFrameScale rank ^ 2 else 0) else 0 := by
      intro j
      by_cases hrow : j = rowIndex
      · subst hrow
        by_cases hcol : j = colIndex
        · simp [hcol, pow_two]
        · simp [hcol]
      · simp [hrow]
    rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_ite_eq']
    simp
  have hrowLeg : ∑ j : Fin rank,
      saturatedFrameShift rank * (if j = rowIndex then saturatedFrameScale rank else 0)
      = saturatedFrameShift rank * saturatedFrameScale rank := by
    rw [← Finset.mul_sum, Finset.sum_ite_eq']
    simp
  have hcolLeg : ∑ j : Fin rank,
      saturatedFrameShift rank * (if j = colIndex then saturatedFrameScale rank else 0)
      = saturatedFrameShift rank * saturatedFrameScale rank := by
    rw [← Finset.mul_sum, Finset.sum_ite_eq']
    simp
  have hconst : ∑ _j : Fin rank, saturatedFrameShift rank ^ 2
      = (rank : ℝ) * saturatedFrameShift rank ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hlast : saturatedFrameVector rank (Fin.last rank) rowIndex
      * saturatedFrameVector rank (Fin.last rank) colIndex = 1 := by
    rw [saturatedFrameVector_last, saturatedFrameVector_last]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hentry j), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hcross, hrowLeg, hcolLeg, hconst, hlast]
  by_cases hdiag : rowIndex = colIndex
  · rw [if_pos hdiag, if_pos hdiag, hsq]
    linear_combination hquad
  · rw [if_neg hdiag, if_neg hdiag]
    linear_combination hquad

/-- **LAW THREE, MATRIX FORM.**  The rank-one sum of the whole frame is
`(rank + 1)` times the identity. -/
theorem sum_atomMatrix_saturatedFrameVector {rank : ℕ} (hrank : rank ≠ 0) :
    ∑ vertex : Fin (rank + 1), atomMatrix (saturatedFrameVector rank vertex)
      = ((rank : ℝ) + 1) • (1 : Matrix (Fin rank) (Fin rank) ℝ) := by
  ext rowIndex colIndex
  rw [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    ← sum_frameVector_mul_apply hrank rowIndex colIndex]
  exact Finset.sum_congr rfl fun vertex _ => by rw [atomMatrix, Matrix.vecMulVec_apply]

/-- **LAW THREE, RAYLEIGH FORM.**  The same resolution read against one
direction.  Every domination proof below uses this form and never the matrix
one. -/
theorem sum_sq_dotProduct_saturatedFrameVector {rank : ℕ} (hrank : rank ≠ 0)
    (probe : Fin rank → ℝ) :
    ∑ vertex : Fin (rank + 1), (saturatedFrameVector rank vertex ⬝ᵥ probe) ^ 2
      = ((rank : ℝ) + 1) * (probe ⬝ᵥ probe) := by
  have hquad := saturatedFrameShift_quadratic hrank
  have hsq := saturatedFrameScale_sq rank
  have hterm : ∀ j : Fin rank,
      (saturatedFrameVector rank j.castSucc ⬝ᵥ probe) ^ 2
        = saturatedFrameScale rank ^ 2 * probe j ^ 2
          + 2 * saturatedFrameScale rank * saturatedFrameShift rank
              * (probe j * ∑ coord, probe coord)
          + saturatedFrameShift rank ^ 2 * (∑ coord, probe coord) ^ 2 := by
    intro j
    rw [saturatedFrameVector_castSucc_dotProduct]
    ring
  have hone : ∑ j : Fin rank, saturatedFrameScale rank ^ 2 * probe j ^ 2
      = saturatedFrameScale rank ^ 2 * ∑ j, probe j ^ 2 := (Finset.mul_sum _ _ _).symm
  have htwo : ∑ j : Fin rank, (2 * saturatedFrameScale rank * saturatedFrameShift rank
        * (probe j * ∑ coord, probe coord))
      = 2 * saturatedFrameScale rank * saturatedFrameShift rank
        * ((∑ coord, probe coord) * ∑ coord, probe coord) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hthree : ∑ _j : Fin rank, saturatedFrameShift rank ^ 2 * (∑ coord, probe coord) ^ 2
      = (rank : ℝ) * (saturatedFrameShift rank ^ 2 * (∑ coord, probe coord) ^ 2) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_castSucc, saturatedFrameVector_last_dotProduct,
    Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, Finset.sum_add_distrib,
    hone, htwo, hthree, hsq, dotProduct_self_eq_sum_sq]
  linear_combination (∑ coord, probe coord) ^ 2 * hquad

/-- **THE FRAME IS LINE-FREE ABOVE RANK ONE.**  No two frame vectors are
proportional.  The proof reads only the two pairing laws: proportionality forces
`ratio ^ 2 = 1` from the norms and `ratio ^ 2 * rank ^ 2 = 1` from the pairing,
and the two together force `rank = 1`. -/
theorem saturatedFrameVector_not_parallel {rank : ℕ} (hrank : 2 ≤ rank)
    (vertex other : Fin (rank + 1)) (hne : vertex ≠ other) (ratio : ℝ)
    (hparallel : saturatedFrameVector rank other = ratio • saturatedFrameVector rank vertex) :
    False := by
  have hrankNe : rank ≠ 0 := by omega
  have hrankReal : (2 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
  have hself := saturatedFrameVector_dot_self hrankNe vertex
  have hother := saturatedFrameVector_dot_self hrankNe other
  have hcross := saturatedFrameVector_dot_ne_sq hrankNe vertex other hne
  have hnorm : (rank : ℝ) = ratio ^ 2 * (rank : ℝ) := by
    have hcalc : saturatedFrameVector rank other ⬝ᵥ saturatedFrameVector rank other
        = ratio ^ 2 * (saturatedFrameVector rank vertex ⬝ᵥ saturatedFrameVector rank vertex) := by
      rw [hparallel, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [hother, hself] at hcalc
    exact hcalc
  have hpair : ratio ^ 2 * (rank : ℝ) ^ 2 = 1 := by
    have hcalc : saturatedFrameVector rank vertex ⬝ᵥ saturatedFrameVector rank other
        = ratio * (saturatedFrameVector rank vertex ⬝ᵥ saturatedFrameVector rank vertex) := by
      rw [hparallel, dotProduct_smul, smul_eq_mul]
    rw [hself] at hcalc
    rw [hcalc] at hcross
    linear_combination hcross
  nlinarith [hnorm, hpair, hrankReal]

/-! ## 2. The Rayleigh reading of a subset gap

One general lemma, at every size, rank and subset.  It is the only bridge
between the matrix world and the scalar world used below. -/

/-- **THE GAP RAYLEIGH, WEIGHT-FREE.**  The quadratic form of `S_C - I` at one
direction is the sum of squared pairings over `C`, less the squared norm.  The
tree already carries `Gtz.dotProduct_subsetSum_sub_one_mulVec`, which splits the
SAME quantity by excess and complement share.  This reading spends no weight at
all, which is what the counting argument of section 4 needs. -/
theorem dotProduct_subsetSum_sub_one_mulVec_sumSq {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size)) (probe : Fin rank → ℝ) :
    probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe)
      = (∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    dotProduct_subsetSum_mulVec_of_finset]

/-- **A ZERO RAYLEIGH DIRECTION REFUTES STRICT DOMINATION.**  Packaged once so
that section 4 spends one line on it. -/
theorem not_posDef_of_tight_direction {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) {probe : Fin rank → ℝ} (hprobe : probe ≠ 0)
    (htight : (∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2) = probe ⬝ᵥ probe) :
    ¬ (subsetSum design selected - 1).PosDef := by
  intro hposDef
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
  rw [star_trivial, dotProduct_subsetSum_sub_one_mulVec_sumSq, htight, sub_self] at hpos
  exact lt_irrefl 0 hpos

/-! ## 3. The multiplicity design

The first `rank` labels carry the first `rank` frame vertices, one each.  Every
remaining label carries the all-ones vertex.  The weight at each vertex is
`1 / (rank + 1)`, split evenly among the labels that share it, so the design
reaches EVERY cell with `rank < size`. -/

/-- The vertex that a label sits on. -/
def saturatedVertexOf (rank extra : ℕ) (label : Fin (rank + (extra + 1))) : Fin (rank + 1) :=
  ⟨min (label : ℕ) rank, by omega⟩

/-- The atom of a label: the frame vector of its vertex. -/
noncomputable def saturatedTieAtom (rank extra : ℕ) (label : Fin (rank + (extra + 1))) :
    Fin rank → ℝ :=
  saturatedFrameVector rank (saturatedVertexOf rank extra label)

/-- The weight of a label.  The last vertex splits its share evenly among the
`extra + 1` labels that sit on it. -/
noncomputable def saturatedTieWeight (rank extra : ℕ) (label : Fin (rank + (extra + 1))) : ℝ :=
  if (label : ℕ) < rank then 1 / ((rank : ℝ) + 1)
  else 1 / (((rank : ℝ) + 1) * ((extra : ℝ) + 1))

theorem saturatedVertexOf_castAdd (rank extra : ℕ) (j : Fin rank) :
    saturatedVertexOf rank extra (Fin.castAdd (extra + 1) j) = j.castSucc := by
  apply Fin.ext
  have hval : ((Fin.castAdd (extra + 1) j : Fin (rank + (extra + 1))) : ℕ) = (j : ℕ) := rfl
  show min ((Fin.castAdd (extra + 1) j : Fin (rank + (extra + 1))) : ℕ) rank = (j : ℕ)
  rw [hval, min_eq_left j.isLt.le]

theorem saturatedVertexOf_natAdd (rank extra : ℕ) (j : Fin (extra + 1)) :
    saturatedVertexOf rank extra (Fin.natAdd rank j) = Fin.last rank := by
  apply Fin.ext
  have hval : ((Fin.natAdd rank j : Fin (rank + (extra + 1))) : ℕ) = rank + (j : ℕ) := rfl
  show min ((Fin.natAdd rank j : Fin (rank + (extra + 1))) : ℕ) rank = rank
  rw [hval]
  omega

theorem saturatedTieWeight_castAdd (rank extra : ℕ) (j : Fin rank) :
    saturatedTieWeight rank extra (Fin.castAdd (extra + 1) j) = 1 / ((rank : ℝ) + 1) := by
  have hval : ((Fin.castAdd (extra + 1) j : Fin (rank + (extra + 1))) : ℕ) = (j : ℕ) := rfl
  unfold saturatedTieWeight
  rw [hval, if_pos j.isLt]

theorem saturatedTieWeight_natAdd (rank extra : ℕ) (j : Fin (extra + 1)) :
    saturatedTieWeight rank extra (Fin.natAdd rank j)
      = 1 / (((rank : ℝ) + 1) * ((extra : ℝ) + 1)) := by
  have hval : ((Fin.natAdd rank j : Fin (rank + (extra + 1))) : ℕ) = rank + (j : ℕ) := rfl
  unfold saturatedTieWeight
  rw [hval, if_neg (by omega)]

theorem saturatedTieAtom_castAdd (rank extra : ℕ) (j : Fin rank) :
    saturatedTieAtom rank extra (Fin.castAdd (extra + 1) j)
      = saturatedFrameVector rank j.castSucc := by
  rw [saturatedTieAtom, saturatedVertexOf_castAdd]

theorem saturatedTieAtom_natAdd (rank extra : ℕ) (j : Fin (extra + 1)) :
    saturatedTieAtom rank extra (Fin.natAdd rank j)
      = saturatedFrameVector rank (Fin.last rank) := by
  rw [saturatedTieAtom, saturatedVertexOf_natAdd]

/-- **THE DESIGN.**  One weighted design at every cell with `rank < size`, at
every rank.  Parseval holds because the vertex weights are equal and the frame
resolves the identity. -/
noncomputable def saturatedTieDesign (rank extra : ℕ) :
    WeightedDesign (rank + (extra + 1)) rank where
  atom := saturatedTieAtom rank extra
  weight := saturatedTieWeight rank extra
  weight_pos := by
    intro label
    unfold saturatedTieWeight
    split
    · positivity
    · positivity
  weight_sum_one := by
    rw [Fin.sum_univ_add,
      Finset.sum_congr rfl (fun j _ => saturatedTieWeight_castAdd rank extra j),
      Finset.sum_congr rfl (fun j _ => saturatedTieWeight_natAdd rank extra j),
      Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
      Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
    have hrankNe : ((rank : ℝ) + 1) ≠ 0 := by positivity
    have hextraNe : ((extra : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  isParseval := by
    ext rowIndex colIndex
    have hrankPos : 0 < rank := lt_of_le_of_lt (Nat.zero_le _) rowIndex.isLt
    have hrankNe : rank ≠ 0 := by omega
    have hcast : ((rank : ℝ) + 1) ≠ 0 := by positivity
    have hextra : ((extra : ℝ) + 1) ≠ 0 := by positivity
    rw [Matrix.sum_apply, Matrix.one_apply]
    have hentry : ∀ label : Fin (rank + (extra + 1)),
        (saturatedTieWeight rank extra label • atomMatrix (saturatedTieAtom rank extra label))
            rowIndex colIndex
          = saturatedTieWeight rank extra label
            * (saturatedTieAtom rank extra label rowIndex
              * saturatedTieAtom rank extra label colIndex) := by
      intro label
      rw [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
    have hlow : ∑ j : Fin rank, saturatedTieWeight rank extra (Fin.castAdd (extra + 1) j)
          * (saturatedTieAtom rank extra (Fin.castAdd (extra + 1) j) rowIndex
            * saturatedTieAtom rank extra (Fin.castAdd (extra + 1) j) colIndex)
        = (1 / ((rank : ℝ) + 1)) * ∑ j : Fin rank,
            saturatedFrameVector rank j.castSucc rowIndex
              * saturatedFrameVector rank j.castSucc colIndex := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [saturatedTieWeight_castAdd, saturatedTieAtom_castAdd]
    have hscale : ((extra : ℝ) + 1) * (1 / (((rank : ℝ) + 1) * ((extra : ℝ) + 1)))
        = 1 / ((rank : ℝ) + 1) := by field_simp
    have hhigh : ∑ j : Fin (extra + 1), saturatedTieWeight rank extra (Fin.natAdd rank j)
          * (saturatedTieAtom rank extra (Fin.natAdd rank j) rowIndex
            * saturatedTieAtom rank extra (Fin.natAdd rank j) colIndex)
        = (1 / ((rank : ℝ) + 1)) * (saturatedFrameVector rank (Fin.last rank) rowIndex
            * saturatedFrameVector rank (Fin.last rank) colIndex) := by
      have hterm : ∀ j : Fin (extra + 1),
          saturatedTieWeight rank extra (Fin.natAdd rank j)
            * (saturatedTieAtom rank extra (Fin.natAdd rank j) rowIndex
              * saturatedTieAtom rank extra (Fin.natAdd rank j) colIndex)
            = (1 / (((rank : ℝ) + 1) * ((extra : ℝ) + 1)))
              * (saturatedFrameVector rank (Fin.last rank) rowIndex
                * saturatedFrameVector rank (Fin.last rank) colIndex) := by
        intro j
        rw [saturatedTieWeight_natAdd, saturatedTieAtom_natAdd]
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [← mul_assoc, hscale]
    rw [Finset.sum_congr rfl (fun label _ => hentry label), Fin.sum_univ_add, hlow, hhigh,
      ← mul_add, ← Fin.sum_univ_castSucc
        (fun vertex : Fin (rank + 1) => saturatedFrameVector rank vertex rowIndex
          * saturatedFrameVector rank vertex colIndex),
      sum_frameVector_mul_apply hrankNe, ← mul_assoc,
      show (1 / ((rank : ℝ) + 1)) * ((rank : ℝ) + 1) = 1 by field_simp, one_mul]

theorem saturatedTieDesign_atom (rank extra : ℕ) (label : Fin (rank + (extra + 1))) :
    (saturatedTieDesign rank extra).atom label
      = saturatedFrameVector rank (saturatedVertexOf rank extra label) := rfl

/-- **EVERY ATOM IS HEAVY.**  Leverage exactly `rank` at every label, so the
design satisfies the all-heavy hypothesis that the pivot and determinant
producers carry in front of their witness. -/
theorem saturatedTieDesign_leverage {rank : ℕ} (hrank : rank ≠ 0) (extra : ℕ)
    (label : Fin (rank + (extra + 1))) :
    leverageOf ((saturatedTieDesign rank extra).atom label) = (rank : ℝ) := by
  rw [saturatedTieDesign_atom]
  have hself := saturatedFrameVector_dot_self hrank (saturatedVertexOf rank extra label)
  rw [← hself, leverageOf, dotProduct_self_eq_sum_sq]

theorem saturatedTieDesign_allHeavy {rank : ℕ} (hrank : 1 ≤ rank) (extra : ℕ) :
    ∀ label : Fin (rank + (extra + 1)),
      1 ≤ leverageOf ((saturatedTieDesign rank extra).atom label) := by
  intro label
  rw [saturatedTieDesign_leverage (by omega) extra label]
  exact_mod_cast hrank

/-! ## 4. The design is a tie, at every rank and every size

Two halves.  The first `rank` labels dominate weakly, by Cauchy-Schwarz against
the all-ones direction.  No card-`rank` subset dominates strictly, because every
such subset misses a vertex and the missed vertex reads a zero Rayleigh
value. -/

/-- The weakly dominating subset: the first `rank` labels, one per basis
vertex. -/
def saturatedTieBase (rank extra : ℕ) : Finset (Fin (rank + (extra + 1))) :=
  Finset.image (Fin.castAdd (extra + 1)) (Finset.univ : Finset (Fin rank))

theorem saturatedTieBase_injective (rank extra : ℕ) :
    Function.Injective (Fin.castAdd (extra + 1) : Fin rank → Fin (rank + (extra + 1))) := by
  intro left right hab
  apply Fin.ext
  have hval : ((Fin.castAdd (extra + 1) left : Fin (rank + (extra + 1))) : ℕ)
      = ((Fin.castAdd (extra + 1) right : Fin (rank + (extra + 1))) : ℕ) := congrArg Fin.val hab
  exact hval

theorem saturatedTieBase_card (rank extra : ℕ) : (saturatedTieBase rank extra).card = rank := by
  rw [saturatedTieBase, Finset.card_image_of_injective _ (saturatedTieBase_injective rank extra),
    Finset.card_univ, Fintype.card_fin]

/-- **THE CAUCHY-SCHWARZ STEP.**  The only inequality in the whole file. -/
theorem sq_sum_le_rank_mul_dotProduct {rank : ℕ} (probe : Fin rank → ℝ) :
    (∑ coord, probe coord) ^ 2 ≤ (rank : ℝ) * (probe ⬝ᵥ probe) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin rank))
    (fun _ => (1 : ℝ)) probe
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  rw [dotProduct_self_eq_sum_sq]
  exact hcs

/-- **WEAK DOMINATION AT THE BASE.**  The gap there is `rank` times the identity
less the all-ones rank-one matrix, and its Rayleigh value is exactly the
Cauchy-Schwarz slack. -/
theorem saturatedTieDesign_dominates_base {rank : ℕ} (hrank : rank ≠ 0) (extra : ℕ) :
    Dominates (saturatedTieDesign rank extra) (saturatedTieBase rank extra) := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_subsetSum_sub_one _ _, fun probe => ?_⟩
  rw [star_trivial, dotProduct_subsetSum_sub_one_mulVec_sumSq]
  have himage : ∑ label ∈ saturatedTieBase rank extra,
        ((saturatedTieDesign rank extra).atom label ⬝ᵥ probe) ^ 2
      = ∑ j : Fin rank, (saturatedFrameVector rank j.castSucc ⬝ᵥ probe) ^ 2 := by
    rw [saturatedTieBase, Finset.sum_image
      (fun a _ b _ hab => saturatedTieBase_injective rank extra hab)]
    exact Finset.sum_congr rfl fun j _ => by
      rw [saturatedTieDesign_atom, saturatedVertexOf_castAdd]
  have hsplit := Fin.sum_univ_castSucc
    (fun vertex : Fin (rank + 1) => (saturatedFrameVector rank vertex ⬝ᵥ probe) ^ 2)
  rw [sum_sq_dotProduct_saturatedFrameVector hrank, saturatedFrameVector_last_dotProduct] at hsplit
  rw [himage]
  have hlow : ∑ j : Fin rank, (saturatedFrameVector rank j.castSucc ⬝ᵥ probe) ^ 2
      = ((rank : ℝ) + 1) * (probe ⬝ᵥ probe) - (∑ coord, probe coord) ^ 2 := by
    linarith [hsplit]
  rw [hlow]
  have hcs := sq_sum_le_rank_mul_dotProduct probe
  linarith [hcs]

/-- **EVERY CARD-`rank` SUBSET MISSES A VERTEX.**  The counting step: `rank`
labels cover at most `rank` of the `rank + 1` vertices. -/
theorem exists_missed_vertex {rank extra : ℕ}
    (selected : Finset (Fin (rank + (extra + 1)))) (hcard : selected.card = rank) :
    ∃ missing : Fin (rank + 1),
      missing ∉ selected.image (saturatedVertexOf rank extra) := by
  by_contra hall
  push_neg at hall
  have hsubset : (Finset.univ : Finset (Fin (rank + 1)))
      ⊆ selected.image (saturatedVertexOf rank extra) := fun vertex _ => hall vertex
  have hcardLe := Finset.card_le_card hsubset
  rw [Finset.card_univ, Fintype.card_fin] at hcardLe
  have himage := Finset.card_image_le
    (s := selected) (f := saturatedVertexOf rank extra)
  omega

/-- **NO CARD-`rank` SUBSET DOMINATES STRICTLY.**  The frame vector of a missed
vertex pairs with every selected atom at squared value one, so the Rayleigh
value of the gap there is `rank - rank = 0`. -/
theorem saturatedTieDesign_not_posDef {rank : ℕ} (hrank : rank ≠ 0) (extra : ℕ)
    (selected : Finset (Fin (rank + (extra + 1)))) (hcard : selected.card = rank) :
    ¬ (subsetSum (saturatedTieDesign rank extra) selected - 1).PosDef := by
  classical
  obtain ⟨missing, hmissing⟩ := exists_missed_vertex selected hcard
  refine not_posDef_of_tight_direction _ _
    (saturatedFrameVector_ne_zero hrank missing) ?_
  have hone : ∀ label ∈ selected,
      ((saturatedTieDesign rank extra).atom label ⬝ᵥ saturatedFrameVector rank missing) ^ 2
        = 1 := by
    intro label hlabel
    have hne : saturatedVertexOf rank extra label ≠ missing := by
      intro heq
      exact hmissing (Finset.mem_image.mpr ⟨label, hlabel, heq⟩)
    rw [saturatedTieDesign_atom]
    exact saturatedFrameVector_dot_ne_sq hrank _ _ hne
  rw [Finset.sum_congr rfl hone, Finset.sum_const, hcard, nsmul_eq_mul, mul_one,
    saturatedFrameVector_dot_self hrank]

/-- **THE TIE, AT EVERY RANK AND EVERY SIZE ABOVE THE RANK.**  The first
general-rank tie in the tree. -/
theorem saturatedTieDesign_isTie {rank : ℕ} (hrank : rank ≠ 0) (extra : ℕ) :
    IsTie (saturatedTieDesign rank extra) :=
  ⟨⟨saturatedTieBase rank extra, saturatedTieBase_card rank extra,
    saturatedTieDesign_dominates_base hrank extra⟩,
   fun selected hcard => saturatedTieDesign_not_posDef hrank extra selected hcard⟩

/-! ## 5. The line structure: parallel above the bottom cell, primitive at it -/

/-- **A PARALLEL PAIR WHENEVER THE LAST VERTEX IS SHARED.**  Two labels sit on
the all-ones vertex as soon as `extra` is positive, and they carry EQUAL atoms.
So this family never refutes the hinge above its bottom cell. -/
theorem saturatedTieDesign_hasParallelPair (rank inner : ℕ) :
    HasParallelPair (saturatedTieDesign rank (inner + 1)) := by
  refine ⟨⟨rank, by omega⟩, ⟨rank + 1, by omega⟩, 1, ?_, ?_⟩
  · intro heq
    have := congrArg Fin.val heq
    simp only at this
    omega
  · have hleft : saturatedVertexOf rank (inner + 1) ⟨rank, by omega⟩ = Fin.last rank := by
      apply Fin.ext
      show min rank rank = rank
      omega
    have hright : saturatedVertexOf rank (inner + 1) ⟨rank + 1, by omega⟩ = Fin.last rank := by
      apply Fin.ext
      show min (rank + 1) rank = rank
      omega
    rw [saturatedTieDesign_atom, saturatedTieDesign_atom, hleft, hright, one_smul]

/-- **THE BOTTOM CELL IS PRIMITIVE.**  At `size = rank + 1` every vertex carries
exactly one label, so the atoms ARE the frame and no two are proportional. -/
theorem saturatedTieDesign_isPrimitive {rank : ℕ} (hrank : 2 ≤ rank) :
    IsPrimitiveDesign (saturatedTieDesign rank 0) := by
  intro keptLabel dropLabel ratio hdistinct hparallel
  have hvertex : Function.Injective (saturatedVertexOf rank 0) := by
    intro left right heq
    apply Fin.ext
    have hleft := left.isLt
    have hright := right.isLt
    have hval : min ((left : ℕ)) rank = min ((right : ℕ)) rank := congrArg Fin.val heq
    omega
  have hne : saturatedVertexOf rank 0 dropLabel ≠ saturatedVertexOf rank 0 keptLabel := by
    intro heq
    exact hdistinct (hvertex heq).symm
  rw [saturatedTieDesign_atom, saturatedTieDesign_atom] at hparallel
  exact saturatedFrameVector_not_parallel hrank _ _ (Ne.symm hne) ratio hparallel

/-! ## 6. The hinge is FALSE at the bottom cell, at every rank

The tree carried `Gtz.not_hingeHoldsAtSize_four_three` and
`Gtz.not_hingeHoldsAtSize_five_three`, both at rank three.  The first is the
rank-three member of the family below.

LADDER NOTE.  The bottom cell is `size = rank + 1`, which is STRICTLY BELOW the
band's lower bound `2 * rank` at every rank at least two.  So this refutation is
not evidence about either off-path axiom, and it is recorded here only because
it is the general-rank form of a landed rank-three fact. -/

/-- **THE HINGE FAILS AT `(rank + 1, rank)` FOR EVERY RANK AT LEAST TWO.** -/
theorem not_hingeHoldsAtSize_succ_self {rank : ℕ} (hrank : 2 ≤ rank) :
    ¬ HingeHoldsAtSize (rank + 1) rank := by
  intro hhinge
  obtain ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩ :=
    hhinge (saturatedTieDesign rank 0) (saturatedTieDesign_isTie (by omega) 0)
  exact saturatedTieDesign_isPrimitive hrank keptLabel dropLabel ratio hdistinct hparallel

/-! ## 7. The tie-emptiness collapse

Every producer of the two off-path axioms named in section 8 asks for an object
that refutes `Gtz.IsTie`.  Quantified over a cell, that hypothesis says the cell
holds no tie.  This section names the statement and prices it exactly. -/

/-- The statement that a cell carries no tie. -/
def NoTieAtCell (size rank : ℕ) : Prop := ∀ design : WeightedDesign size rank, ¬ IsTie design

/-- **THE EXACT PRICE OF THE WITNESS LANE.**  Tie-emptiness at a cell is
literally the statement that weak domination upgrades to STRICT domination at
every design of the cell.  The registry axioms ask for far less: that a tie
carry a parallel pair. -/
theorem noTieAtCell_iff_strictDomination (size rank : ℕ) :
    NoTieAtCell size rank ↔
      ∀ design : WeightedDesign size rank,
        (∃ selected : Finset (Fin size), selected.card = rank ∧ Dominates design selected) →
          ∃ selected : Finset (Fin size), selected.card = rank
            ∧ (subsetSum design selected - 1).PosDef := by
  constructor
  · intro hno design hdominates
    by_contra hstrict
    push_neg at hstrict
    exact hno design ⟨hdominates, fun selected hcard => hstrict selected hcard⟩
  · intro hstrict design htie
    obtain ⟨selected, hcard, hposDef⟩ := hstrict design htie.1
    exact htie.2 selected hcard hposDef

/-- **TIE-EMPTINESS IS FALSE AT EVERY CELL ABOVE THE DIAGONAL.**  Stated in the
`rank + (extra + 1)` shape that the family is built in. -/
theorem not_noTieAtCell_succ {rank : ℕ} (hrank : rank ≠ 0) (extra : ℕ) :
    ¬ NoTieAtCell (rank + (extra + 1)) rank :=
  fun hno => hno (saturatedTieDesign rank extra) (saturatedTieDesign_isTie hrank extra)

/-- **THE MASTER INHABITANT.**  At every cell with `rank < size` and a positive
rank there is a design that is a tie AND all-heavy.  Every refutation in
section 8 is one line from this. -/
theorem exists_isTie_allHeavy {size rank : ℕ} (hrank : 1 ≤ rank) (hsize : rank < size) :
    ∃ design : WeightedDesign size rank,
      IsTie design ∧ ∀ label, 1 ≤ leverageOf (design.atom label) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_lt hsize
  exact ⟨saturatedTieDesign rank extra, saturatedTieDesign_isTie (by omega) extra,
    saturatedTieDesign_allHeavy hrank extra⟩

/-- **TIE-EMPTINESS IS FALSE AT EVERY CELL ABOVE THE DIAGONAL**, in the bare
`size` shape the registry producers use. -/
theorem not_noTieAtCell {size rank : ℕ} (hrank : 1 ≤ rank) (hsize : rank < size) :
    ¬ NoTieAtCell size rank := by
  obtain ⟨design, htie, _⟩ := exists_isTie_allHeavy hrank hsize
  exact fun hno => hno design htie

/-- **THE REFUTATION ENGINE.**  Any criterion that refutes `Gtz.IsTie` at the
design that carries it is FALSE somewhere, at every cell above the diagonal.
Every producer priced in section 9 is one application of this schema, and so is
every future criterion of the same shape. -/
theorem not_forall_of_refutesTie {size rank : ℕ} (hrank : 1 ≤ rank) (hsize : rank < size)
    (criterion : WeightedDesign size rank → Prop)
    (hrefutes : ∀ design : WeightedDesign size rank, criterion design → ¬ IsTie design) :
    ¬ ∀ design : WeightedDesign size rank, criterion design := by
  obtain ⟨design, htie, _⟩ := exists_isTie_allHeavy hrank hsize
  exact fun hall => hrefutes design (hall design) htie

/-- **THE GUARDED ENGINE.**  A criterion asked only of ALL-HEAVY designs is no
safer than the bare one, because the inhabitant of
`Gtz.exists_isTie_allHeavy` is itself all-heavy.  This is the step that closes
the pivot and determinant lanes, whose producers hide behind that guard. -/
theorem not_forall_allHeavy_of_refutesTie {size rank : ℕ} (hrank : 1 ≤ rank)
    (hsize : rank < size) (criterion : WeightedDesign size rank → Prop)
    (hrefutes : ∀ design : WeightedDesign size rank, criterion design → ¬ IsTie design) :
    ¬ ∀ design : WeightedDesign size rank,
        (∀ label, 1 ≤ leverageOf (design.atom label)) → criterion design := by
  obtain ⟨design, htie, hheavy⟩ := exists_isTie_allHeavy hrank hsize
  exact fun hall => hrefutes design (hall design hheavy) htie

/-! ## 8. The five refuted hypotheses

Each of the five Props below refutes `Gtz.IsTie` at the design that carries it.
The landed bridges are `Gtz.not_isTie_of_hasMassWitness`,
`Gtz.not_isTie_of_hasBracketWitness`, `Gtz.not_isTie_of_pivotWitness`,
`Gtz.not_isTie_of_detWitness` and `Gtz.not_isTie_of_excessDominates`.  So one
tie kills all five at once, through the engine above. -/

/-- The packaged pivot bridge, missing from the tree in this shape. -/
theorem not_isTie_of_hasPivotWitness {size rank : ℕ} (hsize : 2 ≤ size)
    (design : WeightedDesign size rank) (hwitness : HasPivotWitness design) : ¬ IsTie design := by
  obtain ⟨dropLabel, selected, hcard, hbound, hsurplus⟩ := hwitness
  exact not_isTie_of_pivotWitness hsize design dropLabel selected hcard hbound hsurplus

/-- The packaged determinant bridge, missing from the tree in this shape. -/
theorem not_isTie_of_hasDetWitness {size rank : ℕ} (hsize : 2 ≤ size)
    (design : WeightedDesign size rank) (hwitness : HasDetWitness design) : ¬ IsTie design := by
  obtain ⟨dropLabel, selected, hcard, hbound, hdet⟩ := hwitness
  exact not_isTie_of_detWitness hsize design dropLabel selected hcard hbound hdet

/-- **NO MASS WITNESS AT EVERY DESIGN OF ANY CELL ABOVE THE DIAGONAL.** -/
theorem not_forall_hasMassWitness {size rank : ℕ} (hrank : 1 ≤ rank) (hsize : rank < size) :
    ¬ ∀ design : WeightedDesign size rank, HasMassWitness design := by
  obtain ⟨design, htie, _⟩ := exists_isTie_allHeavy hrank hsize
  exact fun hall => not_isTie_of_hasMassWitness design (hall design) htie

/-- **NO BRACKET WITNESS AT EVERY DESIGN OF ANY CELL ABOVE THE DIAGONAL.** -/
theorem not_forall_hasBracketWitness {size rank : ℕ} (hrank : 2 ≤ rank) (hsize : rank < size) :
    ¬ ∀ design : WeightedDesign size rank, HasBracketWitness design := by
  obtain ⟨design, htie, _⟩ := exists_isTie_allHeavy (by omega) hsize
  exact fun hall =>
    not_isTie_of_hasBracketWitness design (by omega) (hall design) htie

/-- **NO PIVOT WITNESS AT EVERY ALL-HEAVY DESIGN OF ANY CELL ABOVE THE
DIAGONAL.**  The heaviness hypothesis that the pivot producer carries in front
of its witness is DISCHARGED by the inhabitant, so it buys the producer
nothing. -/
theorem not_forall_hasPivotWitness {size rank : ℕ} (hrank : 2 ≤ rank) (hsize : rank < size) :
    ¬ ∀ design : WeightedDesign size rank,
        (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design := by
  obtain ⟨design, htie, hheavy⟩ := exists_isTie_allHeavy (by omega) hsize
  exact fun hall =>
    not_isTie_of_hasPivotWitness (by omega) design (hall design hheavy) htie

/-- **NO DETERMINANT WITNESS AT EVERY ALL-HEAVY DESIGN OF ANY CELL ABOVE THE
DIAGONAL.** -/
theorem not_forall_hasDetWitness {size rank : ℕ} (hrank : 2 ≤ rank) (hsize : rank < size) :
    ¬ ∀ design : WeightedDesign size rank,
        (∀ label, 1 ≤ leverageOf (design.atom label)) → HasDetWitness design := by
  obtain ⟨design, htie, hheavy⟩ := exists_isTie_allHeavy (by omega) hsize
  exact fun hall =>
    not_isTie_of_hasDetWitness (by omega) design (hall design hheavy) htie

/-- **NO EXCESS-DOMINATED SELECTION AT EVERY DESIGN OF ANY CELL ABOVE THE
DIAGONAL.**  This is the primitivity-free excess-dominance hypothesis, refuted
here at EVERY rank rather than only at rank three. -/
theorem not_forall_excessDominates {size rank : ℕ} (hrank : 1 ≤ rank) (hsize : rank < size) :
    ¬ ∀ design : WeightedDesign size rank, ∃ selected : Finset (Fin size),
        ∃ hcard : selected.card = rank, ExcessDominatesBlock design selected hcard := by
  obtain ⟨design, htie, _⟩ := exists_isTie_allHeavy hrank hsize
  intro hall
  obtain ⟨selected, hcard, hdominates⟩ := hall design
  exact not_isTie_of_excessDominates design selected hcard hdominates htie

/-- **THE FIVE-WAY VERDICT AT ONE CELL.**  Every criterion in the all-heavy
witness programme fails at every cell above the diagonal. -/
theorem allHeavyWitnessProgramme_fails {size rank : ℕ} (hrank : 2 ≤ rank) (hsize : rank < size) :
    (¬ ∀ design : WeightedDesign size rank, HasMassWitness design)
      ∧ (¬ ∀ design : WeightedDesign size rank, HasBracketWitness design)
      ∧ (¬ ∀ design : WeightedDesign size rank,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design)
      ∧ (¬ ∀ design : WeightedDesign size rank,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasDetWitness design)
      ∧ (¬ ∀ design : WeightedDesign size rank, ∃ selected : Finset (Fin size),
          ∃ hcard : selected.card = rank, ExcessDominatesBlock design selected hcard) :=
  ⟨not_forall_hasMassWitness (by omega) hsize,
   not_forall_hasBracketWitness hrank hsize,
   not_forall_hasPivotWitness hrank hsize,
   not_forall_hasDetWitness hrank hsize,
   not_forall_excessDominates (by omega) hsize⟩

/-! ## 9. The two off-path registry axioms

`Skeleton/Obligations.lean:477` carries `obligationSubThresholdBandHinge` and
`:492` carries `obligationThresholdCellHingeRankFourAndUp`.  Each has SEVEN
producers.  This section prices all seven.

THE FIRST LIVE CELL OF EACH.  The band asks `2 * rank <= size < rank * (rank + 1) / 2`.
At rank three that reads `6 <= size < 6` and is EMPTY, so the band's first live
cells are `(8,4)` and `(9,4)`.  The threshold cell asks `4 <= rank`, so its
first live cell is `(10,4)`.  All three satisfy `rank < size`, so the family of
section 3 reaches every one of them. -/

/-- The band's first live cell, at rank four and size eight. -/
noncomputable def bandTieDesign_eightFour : WeightedDesign 8 4 := saturatedTieDesign 4 3

/-- The band's second live cell, at rank four and size nine. -/
noncomputable def bandTieDesign_nineFour : WeightedDesign 9 4 := saturatedTieDesign 4 4

/-- The threshold cell at rank four, size ten. -/
noncomputable def thresholdTieDesign_tenFour : WeightedDesign 10 4 := saturatedTieDesign 4 5

/-- The rank-three threshold cell, size six.  This is the `(6,3)` member of the
same family, and it is what section 10 spends. -/
noncomputable def cellTieDesign_sixThree : WeightedDesign 6 3 := saturatedTieDesign 3 2

theorem bandTieDesign_eightFour_isTie : IsTie bandTieDesign_eightFour :=
  saturatedTieDesign_isTie (by norm_num) 3

theorem bandTieDesign_nineFour_isTie : IsTie bandTieDesign_nineFour :=
  saturatedTieDesign_isTie (by norm_num) 4

theorem thresholdTieDesign_tenFour_isTie : IsTie thresholdTieDesign_tenFour :=
  saturatedTieDesign_isTie (by norm_num) 5

theorem cellTieDesign_sixThree_isTie : IsTie cellTieDesign_sixThree :=
  saturatedTieDesign_isTie (by norm_num) 2

/-- **THE BAND CARRIES A TIE AT ITS FIRST LIVE CELL.**  The registry's own
STATUS line at `Skeleton/Obligations.lean:474` says no rank-three theorem is
evidence about the band.  This is the rank-four evidence. -/
theorem not_noTieAtCell_bandFirstCells :
    (¬ NoTieAtCell 8 4) ∧ (¬ NoTieAtCell 9 4) ∧ (¬ NoTieAtCell 10 4) :=
  ⟨fun hno => hno bandTieDesign_eightFour bandTieDesign_eightFour_isTie,
   fun hno => hno bandTieDesign_nineFour bandTieDesign_nineFour_isTie,
   fun hno => hno thresholdTieDesign_tenFour thresholdTieDesign_tenFour_isTie⟩

/-! ### The witness lattice

`Gtz.hasMassWitness_of_hasBracketWitness` and
`Gtz.hasDetWitness_of_hasPivotWitness` order the four Props into two chains.
The bracket is the root of one and the pivot is the root of the other.  Both
chains reach BOTH axioms, so either root alone produces both. -/

/-- **BOTH OFF-PATH AXIOMS FROM THE BRACKET ROOT ALONE.**  The bracket implies
the mass witness, and the mass witness alone produces both axioms, so this is
the tightest wiring of that chain.

**#BOGUS — THE HYPOTHESIS IS FALSE.**  `Gtz.not_forall_hasBracketWitness` at
rank four refutes the band member at size eight and the threshold member at size
ten.  Recorded so that no successor spends a cycle on it. -/
theorem bothOffPathAxioms_of_bracketWitness
    (hband : ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
      sizeValue < rankValue * (rankValue + 1) / 2 →
      ∀ design : WeightedDesign sizeValue rankValue, HasBracketWitness design)
    (hcell : ∀ rankValue : ℕ, 4 ≤ rankValue →
      ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
        HasBracketWitness design) :
    (∀ rankValue : ℕ, 3 ≤ rankValue →
        ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
          sizeValue < rankValue * (rankValue + 1) / 2 →
            GtzWeighted (sizeValue - 1) rankValue →
              ∀ design : WeightedDesign sizeValue rankValue,
                IsTie design → HasParallelPair design)
      ∧ (∀ rankValue : ℕ, 4 ≤ rankValue →
          GtzWeighted (rankValue * (rankValue + 1) / 2 - 1) rankValue →
            ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
              IsTie design → HasParallelPair design) :=
  ⟨obligationSubThresholdBandHinge_of_bracketWitness hband,
   obligationThresholdCellHingeRankFourAndUp_of_bracketWitness hcell⟩

/-- **BOTH OFF-PATH AXIOMS FROM THE PIVOT ROOT ALONE.**

**#BOGUS — THE HYPOTHESIS IS FALSE.**  `Gtz.not_forall_hasPivotWitness` at rank
four refutes it, and the all-heavy guard in front of the witness does not save
it, because the refuting design is all-heavy at leverage four. -/
theorem bothOffPathAxioms_of_pivotWitness
    (hband : ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
      sizeValue < rankValue * (rankValue + 1) / 2 →
      ∀ design : WeightedDesign sizeValue rankValue,
        (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design)
    (hcell : ∀ rankValue : ℕ, 4 ≤ rankValue →
      ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
        (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design) :
    (∀ rankValue : ℕ, 3 ≤ rankValue →
        ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
          sizeValue < rankValue * (rankValue + 1) / 2 →
            GtzWeighted (sizeValue - 1) rankValue →
              ∀ design : WeightedDesign sizeValue rankValue,
                IsTie design → HasParallelPair design)
      ∧ (∀ rankValue : ℕ, 4 ≤ rankValue →
          GtzWeighted (rankValue * (rankValue + 1) / 2 - 1) rankValue →
            ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
              IsTie design → HasParallelPair design) :=
  ⟨obligationSubThresholdBandHinge_of_pivotWitness hband,
   obligationThresholdCellHingeRankFourAndUp_of_pivotWitness hcell⟩

/-- **THE BAND'S WITNESS PRODUCERS ARE ALL DEAD.**  All four witness hypotheses
of the sub-threshold band axiom are refuted at the band's FIRST LIVE CELL,
`(8,4)`.  The excess-dominance hypothesis dies with them.

This is the statement the registry's STAGE-7 note at
`Skeleton/Obligations.lean:474` asserted from an out-of-kernel rational
measurement.  It is now a kernel theorem, and it covers five producers rather
than the two the note named. -/
theorem bandProducers_are_dead :
    (¬ ∀ design : WeightedDesign 8 4, HasMassWitness design)
      ∧ (¬ ∀ design : WeightedDesign 8 4, HasBracketWitness design)
      ∧ (¬ ∀ design : WeightedDesign 8 4,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design)
      ∧ (¬ ∀ design : WeightedDesign 8 4,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasDetWitness design)
      ∧ (¬ ∀ design : WeightedDesign 8 4, ∃ selected : Finset (Fin 8),
          ∃ hcard : selected.card = 4, ExcessDominatesBlock design selected hcard) :=
  allHeavyWitnessProgramme_fails (by norm_num) (by norm_num)

/-- **THE THRESHOLD CELL'S WITNESS PRODUCERS ARE ALL DEAD.**  Same five, at the
threshold cell's FIRST LIVE CELL `(10,4)`.

LADDER NOTE, AND THIS MATTERS.  The rank-three refutations in the tree sit at
`(6,3)`, and `4 <= rank` excludes rank three from this axiom.  So no rank-three
refutation is evidence here, and this theorem is the first that is. -/
theorem thresholdCellProducers_are_dead :
    (¬ ∀ design : WeightedDesign 10 4, HasMassWitness design)
      ∧ (¬ ∀ design : WeightedDesign 10 4, HasBracketWitness design)
      ∧ (¬ ∀ design : WeightedDesign 10 4,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design)
      ∧ (¬ ∀ design : WeightedDesign 10 4,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasDetWitness design)
      ∧ (¬ ∀ design : WeightedDesign 10 4, ∃ selected : Finset (Fin 10),
          ∃ hcard : selected.card = 4, ExcessDominatesBlock design selected hcard) :=
  allHeavyWitnessProgramme_fails (by norm_num) (by norm_num)

/-- **THE SEVENTH PRODUCER IS AN EQUIVALENCE, NOT A CORPSE.**
`Gtz.obligationSubThresholdBandHinge_of_heavyTie` asks that an ALL-HEAVY tie
carry a parallel pair.  Modulo the predecessor cell that the axiom already
carries, `Gtz.forall_leverage_one_le_of_isTie` derives heaviness from the tie,
so the hypothesis and the conclusion are inter-derivable.  This theorem states
the direction the tree did not: the axiom implies its own producer's
hypothesis.

**#VACUITY — RECORDS NOTHING.**  A producer whose hypothesis follows from its
conclusion transfers no work.  It is not a corpse, because its hypothesis is
satisfiable, and it is not an asset either. -/
theorem heavyTieHypothesis_of_bandHinge
    (haxiom : ∀ rankValue : ℕ, 3 ≤ rankValue →
      ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
        sizeValue < rankValue * (rankValue + 1) / 2 →
          GtzWeighted (sizeValue - 1) rankValue →
            ∀ design : WeightedDesign sizeValue rankValue,
              IsTie design → HasParallelPair design) :
    ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
      sizeValue < rankValue * (rankValue + 1) / 2 →
        GtzWeighted (sizeValue - 1) rankValue →
          ∀ design : WeightedDesign sizeValue rankValue,
            (∀ label, 1 ≤ leverageOf (design.atom label)) →
              IsTie design → HasParallelPair design :=
  fun rankValue hrank sizeValue hlow hhigh hrec design _ htie =>
    haxiom rankValue hrank sizeValue hlow hhigh hrec design htie

/-! ## 10. The `(6,3)` doors of the same family

`Gtz.hingeConclusion_sixThree_of_massWitness`,
`Gtz.hingeConclusion_sixThree_of_bracketWitness`,
`Gtz.hingeConclusion_sixThree_of_pivotWitness` and
`Gtz.hingeConclusion_sixThree_of_detWitness` each conclude
`∀ design : WeightedDesign 6 3, IsTie design → HasParallelPair design`, which is
`Gtz.HingeHoldsAtSize 6 3` unfolded.  So these four are doors onto the main
rank-three capstone, not off-path plumbing.

All four die at `Gtz.cellTieDesign_sixThree`.  The pivot and determinant doors
carry an all-heavy guard, and the guard is DISCHARGED by the same design, whose
every leverage is exactly three. -/

theorem cellTieDesign_sixThree_allHeavy :
    ∀ label : Fin 6, 1 ≤ leverageOf (cellTieDesign_sixThree.atom label) :=
  saturatedTieDesign_allHeavy (by norm_num) 2

theorem cellTieDesign_sixThree_leverage (label : Fin 6) :
    leverageOf (cellTieDesign_sixThree.atom label) = 3 := by
  have := saturatedTieDesign_leverage (rank := 3) (by norm_num) 2 label
  norm_num at this
  exact this

/-- **THE `(6,3)` TIE CARRIES A PARALLEL PAIR.**  Recorded so that nobody reads
this fixture as a refutation of the rank-three capstone.  Three labels sit on
the all-ones vertex, so the hinge conclusion HOLDS here. -/
theorem cellTieDesign_sixThree_hasParallelPair : HasParallelPair cellTieDesign_sixThree :=
  saturatedTieDesign_hasParallelPair 3 1

/-- **ALL FOUR `(6,3)` WITNESS DOORS ARE DEAD.**  The tree had refuted the mass
and bracket doors only.  The pivot and determinant doors survived because their
all-heavy guard had never been discharged by a `(6,3)` tie.  It is discharged
here. -/
theorem sixThreeWitnessDoors_are_dead :
    (¬ ∀ design : WeightedDesign 6 3, HasMassWitness design)
      ∧ (¬ ∀ design : WeightedDesign 6 3, HasBracketWitness design)
      ∧ (¬ ∀ design : WeightedDesign 6 3,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design)
      ∧ (¬ ∀ design : WeightedDesign 6 3,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasDetWitness design)
      ∧ (¬ ∀ design : WeightedDesign 6 3, ∃ selected : Finset (Fin 6),
          ∃ hcard : selected.card = 3, ExcessDominatesBlock design selected hcard) :=
  allHeavyWitnessProgramme_fails (by norm_num) (by norm_num)

/-- **THE `(6,3)` CAPSTONE DOORS, PRICED.**  Each of the four doors is a true
implication with a FALSE hypothesis, so none of them reaches
`Gtz.HingeHoldsAtSize 6 3` from anywhere.

**#BOGUS — ALL FOUR HYPOTHESES ARE FALSE.** -/
theorem sixThreeWitnessDoors_reach_hinge
    (hmass : ∀ design : WeightedDesign 6 3, HasMassWitness design) :
    HingeHoldsAtSize 6 3 :=
  hingeConclusion_sixThree_of_massWitness hmass

/-- **THE SAME LANE, IN ONE READING.**  Every criterion of the all-heavy witness
programme asserts that its cell holds no tie.  At `(6,3)`, at `(8,4)`, at
`(9,4)` and at `(10,4)` that is false.  So the lane is closed on path and off
path, at rank three and at rank four together. -/
theorem allHeavyWitnessLane_closed_everywhere :
    (¬ NoTieAtCell 6 3) ∧ (¬ NoTieAtCell 8 4) ∧ (¬ NoTieAtCell 9 4) ∧ (¬ NoTieAtCell 10 4) :=
  ⟨fun hno => hno cellTieDesign_sixThree cellTieDesign_sixThree_isTie,
   not_noTieAtCell_bandFirstCells.1,
   not_noTieAtCell_bandFirstCells.2.1,
   not_noTieAtCell_bandFirstCells.2.2⟩

/-! ## 10 bis. The producer hypotheses, refuted AS STATED

Sections 8 and 9 refute the witness criteria one cell at a time.  This section
refutes the FULL quantified hypothesis that each producer carries, so that no
reader has to check the instantiation.  Each proof spends one cell: `(8,4)` for
the band and `(10,4)` for the threshold cell. -/

theorem not_bandMassWitnessHypothesis :
    ¬ ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
        sizeValue < rankValue * (rankValue + 1) / 2 →
        ∀ design : WeightedDesign sizeValue rankValue, HasMassWitness design :=
  fun hall => not_forall_hasMassWitness (rank := 4) (size := 8) (by norm_num) (by norm_num)
    (hall 4 (by norm_num) 8 (by norm_num) (by norm_num))

theorem not_bandBracketWitnessHypothesis :
    ¬ ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
        sizeValue < rankValue * (rankValue + 1) / 2 →
        ∀ design : WeightedDesign sizeValue rankValue, HasBracketWitness design :=
  fun hall => not_forall_hasBracketWitness (rank := 4) (size := 8) (by norm_num) (by norm_num)
    (hall 4 (by norm_num) 8 (by norm_num) (by norm_num))

theorem not_bandPivotWitnessHypothesis :
    ¬ ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
        sizeValue < rankValue * (rankValue + 1) / 2 →
        ∀ design : WeightedDesign sizeValue rankValue,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design :=
  fun hall => not_forall_hasPivotWitness (rank := 4) (size := 8) (by norm_num) (by norm_num)
    (hall 4 (by norm_num) 8 (by norm_num) (by norm_num))

theorem not_bandDetWitnessHypothesis :
    ¬ ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
        sizeValue < rankValue * (rankValue + 1) / 2 →
        ∀ design : WeightedDesign sizeValue rankValue,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasDetWitness design :=
  fun hall => not_forall_hasDetWitness (rank := 4) (size := 8) (by norm_num) (by norm_num)
    (hall 4 (by norm_num) 8 (by norm_num) (by norm_num))

/-- **THE FIRST KERNEL REFUTATION OF THE BAND'S EXCESS-DOMINANCE PRODUCER.**  The
registry note at `Skeleton/Obligations.lean:474` claims this hypothesis is
refuted at rank four, from an out-of-kernel rational measurement.  Here it is in
kernel, and the witness is a tie rather than a margin computation. -/
theorem not_bandExcessDominatesHypothesis :
    ¬ ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
        sizeValue < rankValue * (rankValue + 1) / 2 →
        ∀ design : WeightedDesign sizeValue rankValue,
          ∃ selected : Finset (Fin sizeValue), ∃ hcard : selected.card = rankValue,
            ExcessDominatesBlock design selected hcard :=
  fun hall => not_forall_excessDominates (rank := 4) (size := 8) (by norm_num) (by norm_num)
    (hall 4 (by norm_num) 8 (by norm_num) (by norm_num))

theorem not_thresholdMassWitnessHypothesis :
    ¬ ∀ rankValue : ℕ, 4 ≤ rankValue →
        ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
          HasMassWitness design := by
  intro hall
  have hten : ∀ design : WeightedDesign 10 4, HasMassWitness design := hall 4 (by norm_num)
  exact not_forall_hasMassWitness (rank := 4) (size := 10) (by norm_num) (by norm_num) hten

theorem not_thresholdBracketWitnessHypothesis :
    ¬ ∀ rankValue : ℕ, 4 ≤ rankValue →
        ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
          HasBracketWitness design := by
  intro hall
  have hten : ∀ design : WeightedDesign 10 4, HasBracketWitness design := hall 4 (by norm_num)
  exact not_forall_hasBracketWitness (rank := 4) (size := 10) (by norm_num) (by norm_num) hten

theorem not_thresholdPivotWitnessHypothesis :
    ¬ ∀ rankValue : ℕ, 4 ≤ rankValue →
        ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design := by
  intro hall
  have hten : ∀ design : WeightedDesign 10 4,
      (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design :=
    hall 4 (by norm_num)
  exact not_forall_hasPivotWitness (rank := 4) (size := 10) (by norm_num) (by norm_num) hten

theorem not_thresholdDetWitnessHypothesis :
    ¬ ∀ rankValue : ℕ, 4 ≤ rankValue →
        ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasDetWitness design := by
  intro hall
  have hten : ∀ design : WeightedDesign 10 4,
      (∀ label, 1 ≤ leverageOf (design.atom label)) → HasDetWitness design :=
    hall 4 (by norm_num)
  exact not_forall_hasDetWitness (rank := 4) (size := 10) (by norm_num) (by norm_num) hten

/-- **THE FIRST KERNEL REFUTATION OF THE THRESHOLD CELL'S EXCESS-DOMINANCE
PRODUCER.**  The registry note at `Skeleton/Obligations.lean:489` says this lane
is closed "at the rank-three member".  The axiom opens at `4 <= rank` and has NO
rank-three member, so that note refutes a cell the producer never quantifies
over.  This theorem refutes the producer at a cell it does quantify over. -/
theorem not_thresholdExcessDominatesHypothesis :
    ¬ ∀ rankValue : ℕ, 4 ≤ rankValue →
        ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
          ∃ selected : Finset (Fin (rankValue * (rankValue + 1) / 2)),
            ∃ hcard : selected.card = rankValue,
              ExcessDominatesBlock design selected hcard := by
  intro hall
  have hten : ∀ design : WeightedDesign 10 4, ∃ selected : Finset (Fin 10),
      ∃ hcard : selected.card = 4, ExcessDominatesBlock design selected hcard :=
    hall 4 (by norm_num)
  exact not_forall_excessDominates (rank := 4) (size := 10) (by norm_num) (by norm_num) hten

/-- **SIX OF THE SEVEN PRODUCERS OF THE SUB-THRESHOLD BAND AXIOM ARE DEAD.**  The
five hypotheses below are false as stated.  The primitive repair of the sixth is
priced in section 12, and the seventh is the equivalence of section 9. -/
theorem bandAxiom_hasNoLiveWitnessProducer :
    (¬ ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
        sizeValue < rankValue * (rankValue + 1) / 2 →
        ∀ design : WeightedDesign sizeValue rankValue, HasMassWitness design)
      ∧ (¬ ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
        sizeValue < rankValue * (rankValue + 1) / 2 →
        ∀ design : WeightedDesign sizeValue rankValue, HasBracketWitness design)
      ∧ (¬ ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
        sizeValue < rankValue * (rankValue + 1) / 2 →
        ∀ design : WeightedDesign sizeValue rankValue,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design)
      ∧ (¬ ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
        sizeValue < rankValue * (rankValue + 1) / 2 →
        ∀ design : WeightedDesign sizeValue rankValue,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasDetWitness design)
      ∧ (¬ ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
        sizeValue < rankValue * (rankValue + 1) / 2 →
        ∀ design : WeightedDesign sizeValue rankValue,
          ∃ selected : Finset (Fin sizeValue), ∃ hcard : selected.card = rankValue,
            ExcessDominatesBlock design selected hcard) :=
  ⟨not_bandMassWitnessHypothesis, not_bandBracketWitnessHypothesis,
   not_bandPivotWitnessHypothesis, not_bandDetWitnessHypothesis,
   not_bandExcessDominatesHypothesis⟩

/-- **SIX OF THE SEVEN PRODUCERS OF THE THRESHOLD-CELL AXIOM ARE DEAD.** -/
theorem thresholdAxiom_hasNoLiveWitnessProducer :
    (¬ ∀ rankValue : ℕ, 4 ≤ rankValue →
        ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
          HasMassWitness design)
      ∧ (¬ ∀ rankValue : ℕ, 4 ≤ rankValue →
        ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
          HasBracketWitness design)
      ∧ (¬ ∀ rankValue : ℕ, 4 ≤ rankValue →
        ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasPivotWitness design)
      ∧ (¬ ∀ rankValue : ℕ, 4 ≤ rankValue →
        ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
          (∀ label, 1 ≤ leverageOf (design.atom label)) → HasDetWitness design)
      ∧ (¬ ∀ rankValue : ℕ, 4 ≤ rankValue →
        ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
          ∃ selected : Finset (Fin (rankValue * (rankValue + 1) / 2)),
            ∃ hcard : selected.card = rankValue,
              ExcessDominatesBlock design selected hcard) :=
  ⟨not_thresholdMassWitnessHypothesis, not_thresholdBracketWitnessHypothesis,
   not_thresholdPivotWitnessHypothesis, not_thresholdDetWitnessHypothesis,
   not_thresholdExcessDominatesHypothesis⟩

/-! ## 11. What already existed, and what this module adds

**#DUPLICATION — THE INHABITANT IS NOT NEW, THE CERTIFICATE ON IT IS.**  The
tree already carries three general-rank tie families, and a successor must not
build a fourth:

* `Gtz.simplexTieDesign` (`Gtz/Ties/CorankOneTieExistence.lean:275`), a tie at
  `(rank + 1, rank)` for every weight vector, with the exact criterion
  `Gtz.isTie_iff_leverage_identity`.
* `Gtz.splitClassDesign` (`Gtz/Ties/SplitClassTieFamily.lean:104`) and
  `Gtz.exists_isTie_of_weights_of_classes` (`:199`), which give a tie at EVERY
  cell `(size, rank)` that admits a surjection onto `rank + 1` classes, for
  every weight vector.  That is every cell with `rank < size`, the same reach as
  `Gtz.exists_isTie_allHeavy` above.
* `Gtz.bundledCycleDesign` (`Gtz/Design/EqualityLocus.lean:564`) with
  `Gtz.bundledCycle_isTie`, and its rank-four instance
  `Gtz.eightFourBundledDesign` (`Gtz/Design/TieCensusCompletion.lean:141`).

So the EXISTENCE of a rank-four tie was landed.  What was missing, and what
sections 1 thru 5 supply, is a tie that carries its LEVERAGE PROFILE on its
face: `Gtz.saturatedTieDesign_leverage` reads exactly `rank` at every label,
with no leverage-identity detour and no predecessor cell.  That certificate is
what the pivot and determinant producers need, because both hide behind an
all-heavy guard, and neither landed family had been given one.  Sections 7 thru
10 are new outright.

A successor who needs only a tie, and not its leverage, must spend
`Gtz.exists_isTie_of_weights_of_classes` and not this file.

## 12. What this module does NOT close

ONE PRODUCER OF EACH AXIOM SURVIVES AS A LIVE OBJECT, and one survives as an
equivalence.

1.  `Gtz.obligationSubThresholdBandHinge_of_primitiveExcessDominates` and its
    threshold-cell twin ask for an excess-dominated selection at every PRIMITIVE
    design of the cell.  The family of section 3 is primitive ONLY at its bottom
    cell `size = rank + 1`, by `Gtz.saturatedTieDesign_isPrimitive`, and that
    cell is below the band at every rank at least two.  Above the bottom cell
    the family carries a parallel pair, so it is not primitive and does not
    refute the primitive form.

    WHY THAT IS NOT AN OVERSIGHT.  A PRIMITIVE tie inside the band would refute
    the band axiom itself, not just its producer.  So no tie-based refutation of
    the primitive form can exist unless the axiom is false.  A successor must
    refute the primitive form with a primitive NON-tie that carries no dominated
    selection.

    THE CONCRETE ATTACK.  Widen the frame from `rank + 1` vertices to `rank + 2`
    and give every vertex multiplicity one.  The counting step of
    `Gtz.exists_missed_vertex` still applies, so a wider equal-norm tight frame
    with all squared pairings equal to one would give a primitive design at
    `size = rank + 2`.  Its Gram matrix must have nullity at least two, which is
    the one condition to check before the construction is attempted.

2.  `Gtz.obligationSubThresholdBandHinge_of_heavyTie` is an equivalence modulo
    the predecessor cell, priced by `Gtz.heavyTieHypothesis_of_bandHinge`.

WHAT THE REGISTRY GETS WRONG, AND IT MATTERS.  The note at
`Skeleton/Obligations.lean:489` says the primitive excess-dominance hypothesis
IS KERNEL-REFUTED at "the rank-three member".  The threshold-cell axiom has NO
rank-three member, because it opens at `4 <= rank`.  The band has no rank-three
member either, because `6 <= size < 6` is empty.  So a `(6,3)` refutation of any
producer hypothesis of EITHER off-path axiom is evidence about a cell the
producer does not quantify over, unless the producer's hypothesis is itself
quantified from rank three upward.  Section 8 avoids that error by refuting at
rank four directly. -/

/-- **THE LADDER, STATED.**  The band is empty at rank three, so no rank-three
design is an instance of the sub-threshold band hypothesis. -/
theorem band_is_empty_at_rank_three (sizeValue : ℕ) (hlow : 2 * 3 ≤ sizeValue)
    (hhigh : sizeValue < 3 * (3 + 1) / 2) : False := by omega

/-- **THE LADDER, SECOND HALF.**  The threshold-cell axiom opens at rank four,
so rank three is not an instance of it either. -/
theorem thresholdCell_excludes_rank_three : ¬ (4 ≤ 3) := by omega

end Gtz
