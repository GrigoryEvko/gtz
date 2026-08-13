/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.TrichotomyLedger
import Gtz.Reduction.HingeFunnel
import Gtz.Reduction.StressSignSplit
import Gtz.Reduction.Crystallization
import Gtz.Reduction.StressWalk
import Gtz.Design.BalancedStratum
import Gtz.Reduction.BalancedStratumClosure
import Gtz.Quantitative.PhaseFreeNoGo
import Gtz.Design.TwoPoleStratum

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The threshold cell hinge at general rank

The deciding cell of a rank is `thresholdSize rank = rank * (rank + 1) / 2`, the
dimension of the symmetric matrices. At that cell a design carries exactly as
many atoms as the symmetric matrices have dimensions. Thus a stress-free design
there has atom matrices that form a BASIS of the symmetric matrices.

This module lifts the rank-three hinge assembly to general rank, proves the
half that lifts, and states the half that does not as named Props.

## What lifts, and what does not

The rank-three assembly `Gtz.hingeHoldsAtSize_sixThree_of_stressFreeHinge` reads
`Gtz.sixThree_stress_trichotomy` and splits a `(6,3)` design three ways. That
trichotomy rests on `Gtz.stress_fullSupport_or_orthogonalProbe`, which carries
the hypothesis `size <= 2 * rank`. At the threshold cell that hypothesis holds
if and only if the rank is three or less (`Gtz.thresholdSize_le_two_mul_iff`).
Thus the rank-three trichotomy does not lift.

`Gtz.design_stress_trichotomy` is the replacement. It splits on SPANNING and
not on support, it carries no size hypothesis, and it holds at every size and
every rank. At the rank-three cell it gives back the rank-three trichotomy,
because `Gtz.stress_fullSupport_of_sides_of_size_le` turns the two spanning
sides into full support exactly when `size <= 2 * rank`.

## The three arms

`Gtz.ThresholdStressFreeArm`, `Gtz.ThresholdBalancedArm` and
`Gtz.ThresholdDegenerateArm` are the three named residuals.
`Gtz.thresholdCellHinge_of_arms` assembles them into the hinge at the threshold
cell of every rank. The assembly consumes NO predecessor cell, thus it is
stronger than the registry statement, which supplies one.

At rank three the three arms are the tree's own three branches
(`Gtz.thresholdArms_rank_three_faithful`): arm (ii) comes from the closed
`Gtz.BalancedStratumCapstone`, arm (iii) from the closed
`Gtz.TwoPoleStratumSelection 6`, and arm (i) is the open five-class frontier.

## The stress-free arm

The arm does not lift as a proof, and no proof exists to lift: at rank three the
same arm is the open frontier. What lifts is the STRUCTURE, and this module
lands all of it — the basis property (`Gtz.exists_atomCombination_of_transpose_eq`),
the uniqueness of the Parseval coefficients
(`Gtz.eq_weight_of_atomCombination_eq_one`), the primitivity of every stress-free
design (`Gtz.isPrimitiveDesign_of_stressFree_general`) and the tie-emptiness
reading (`Gtz.thresholdStressFreeArm_iff_no_stressFree_tie`).
-/

namespace Gtz

open Matrix Finset

variable {m n k size rank : ℕ}

/-! ## Part 1: the threshold cell as an arithmetic object

The whole rank split is visible in three arithmetic facts about
`thresholdSize`. Everything below quotes one of them. -/

/-- The deciding cell size at a rank: the dimension of the symmetric matrices,
and the largest size at which `Gtz.exists_parsevalNullDirection` does not force
a stress. -/
def thresholdSize (rank : ℕ) : ℕ := rank * (rank + 1) / 2

/-- The threshold size, doubled, with no truncated division. -/
theorem two_mul_thresholdSize (rank : ℕ) :
    2 * thresholdSize rank = rank * (rank + 1) := by
  obtain ⟨half, hhalf⟩ := Nat.even_mul_succ_self rank
  rw [thresholdSize, hhalf]
  omega

theorem thresholdSize_three : thresholdSize 3 = 6 := by
  rw [thresholdSize]

theorem thresholdSize_four : thresholdSize 4 = 10 := by
  rw [thresholdSize]

/-- **THE RANK SPLIT, AS ARITHMETIC.**  The support dichotomy
`Gtz.stress_fullSupport_or_orthogonalProbe` needs `size <= 2 * rank`. At the
threshold cell that condition is the condition `rank <= 3`. This single
equivalence is why the rank-three trichotomy stops at rank three. -/
theorem thresholdSize_le_two_mul_iff (rank : ℕ) :
    thresholdSize rank ≤ 2 * rank ↔ rank ≤ 3 := by
  have hdouble := two_mul_thresholdSize rank
  refine ⟨fun hle => ?_, fun hle => ?_⟩
  · by_contra hgt
    have hfour : 4 ≤ rank := by omega
    have hbig : 4 * (rank + 1) ≤ rank * (rank + 1) := Nat.mul_le_mul hfour le_rfl
    omega
  · interval_cases rank <;> rw [thresholdSize] <;> norm_num

/-- The window floor: at rank three and above the threshold cell sits at or
above `2 * rank`, thus the sharp window of the registry is nonempty there. -/
theorem two_mul_le_thresholdSize (rank : ℕ) (hrank : 3 ≤ rank) :
    2 * rank ≤ thresholdSize rank := by
  have hdouble := two_mul_thresholdSize rank
  have hbig : rank * 4 ≤ rank * (rank + 1) := Nat.mul_le_mul le_rfl (by omega)
  omega

/-- **THE SIGN-SPLIT WINDOW, DOUBLED.**  A full-support stress at the threshold
cell puts at least `rank` labels on each sign side, thus the positive side's
count ranges over `[rank, thresholdSize rank - rank]`. The width of that window
is `rank * (rank - 3) / 2`, stated here without truncated division. -/
theorem two_mul_thresholdSplitWindow (rank : ℕ) (hrank : 3 ≤ rank) :
    2 * (thresholdSize rank - 2 * rank) = rank * (rank - 3) := by
  obtain ⟨shift, rfl⟩ : ∃ shift, rank = shift + 3 := ⟨rank - 3, by omega⟩
  have hdouble := two_mul_thresholdSize (shift + 3)
  have hleft : (shift + 3) * (shift + 3 + 1) = shift * shift + 7 * shift + 12 := by ring
  have hright : (shift + 3) * (shift + 3 - 3) = shift * shift + 3 * shift := by
    rw [Nat.add_sub_cancel]; ring
  rw [hleft] at hdouble
  rw [hright]
  omega

/-- The window width itself. -/
theorem thresholdSplitWindow (rank : ℕ) (hrank : 3 ≤ rank) :
    thresholdSize rank - 2 * rank = rank * (rank - 3) / 2 := by
  have hdouble := two_mul_thresholdSplitWindow rank hrank
  omega

/-- **THE WINDOW IS A POINT ONLY AT RANK THREE.**  At rank three the admissible
positive-side count is forced to `rank`, which is what makes the rank-three
balanced branch a FULL-SUPPORT branch. -/
theorem thresholdSplit_isPoint_iff (rank : ℕ) (hrank : 3 ≤ rank) :
    thresholdSize rank - rank = rank ↔ rank = 3 := by
  have hdouble := two_mul_thresholdSize rank
  have hfloor := two_mul_le_thresholdSize rank hrank
  refine ⟨fun hpoint => ?_, fun hthree => ?_⟩
  · by_contra hne
    have hfour : 4 ≤ rank := by omega
    have hbig : 5 * rank ≤ rank * (rank + 1) := by
      rw [Nat.mul_comm 5 rank]
      exact Nat.mul_le_mul le_rfl (by omega)
    omega
  · subst hthree
    rw [thresholdSize_three]

/-- **THE FAN-OUT AT RANK FOUR AND UP.**  The window strictly contains its lower
endpoint, thus the balanced branch admits more than one sign split and the
rank-three case analysis has nothing to specialize to. -/
theorem lt_thresholdSize_sub_rank (rank : ℕ) (hrank : 4 ≤ rank) :
    rank < thresholdSize rank - rank := by
  have hdouble := two_mul_thresholdSize rank
  have hbig : 5 * rank ≤ rank * (rank + 1) := by
    rw [Nat.mul_comm 5 rank]
    exact Nat.mul_le_mul le_rfl (by omega)
  omega

/-! ## Part 2: the symmetric basis at the threshold cell

At the threshold cell a stress-free design has exactly `dim Sym(rank)` atom
matrices and they are independent, thus they SPAN. This part proves the span
and reads two corollaries off it. Both are rank-uniform, and both are the
general-rank form of instruments the registry records as rank-three only. -/

/-- Any real combination of atom matrices is symmetric. -/
theorem transpose_atomCombination (atomFamily : Fin m → Fin k → ℝ) (coeff : Fin m → ℝ) :
    (∑ c, coeff c • atomMatrix (atomFamily c))ᵀ
      = ∑ c, coeff c • atomMatrix (atomFamily c) := by
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.transpose_smul,
    transpose_eq_of_isHermitian (posSemidef_atomMatrix (atomFamily c)).1]

/-- The upper-triangle coordinates of the atom combination, as a linear map.
This is `Gtz.momentMap` with the mass component dropped, exactly the map whose
non-injectivity `Gtz.exists_parsevalNullDirection` exploits above the threshold
cell. Here it is used at the cell itself, where it is a bijection. -/
def atomCoordMap (atomFamily : Fin m → Fin k → ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] ({ p : Fin k × Fin k // p.1 ≤ p.2 } → ℝ) :=
  (LinearMap.fst ℝ ({ p : Fin k × Fin k // p.1 ≤ p.2 } → ℝ) ℝ).comp (momentMap atomFamily)

theorem atomCoordMap_apply (atomFamily : Fin m → Fin k → ℝ) (coeff : Fin m → ℝ) :
    atomCoordMap atomFamily coeff
      = upperTriangleCoords (∑ c, coeff c • atomMatrix (atomFamily c)) := rfl

/-- A stress-free family makes the coordinate map injective. -/
theorem injective_atomCoordMap_of_stressFree {atomFamily : Fin m → Fin k → ℝ}
    (hstressFree : ∀ coeff : Fin m → ℝ,
      (∑ c, coeff c • atomMatrix (atomFamily c)) = 0 → coeff = 0) :
    Function.Injective (atomCoordMap atomFamily) := by
  rw [← LinearMap.ker_eq_bot]
  refine LinearMap.ker_eq_bot'.mpr fun coeff hcoeff => ?_
  refine hstressFree coeff ?_
  exact symmetric_eq_zero_of_coords_eq_zero (transpose_atomCombination atomFamily coeff)
    (by rw [← atomCoordMap_apply]; exact hcoeff)

/-- **THE BASIS PROPERTY AT THE THRESHOLD CELL, RANK-UNIFORM.**  A stress-free
family of `thresholdSize rank` atoms reaches EVERY symmetric matrix. The count
`thresholdSize rank` is exactly `dim Sym(rank)`, thus an injective coordinate
map between spaces of equal dimension is surjective, and symmetry recovers the
matrix from its upper triangle.

This is the general-rank form of the rank-three sentence "the six atom matrices
are a basis of `Sym(3)`" that `Gtz.StressFreeHingeHoldsSixThree` quantifies
over. Below the threshold cell it is FALSE, which is why the sub-threshold band
carries its own registry obligation. -/
theorem exists_atomCombination_of_transpose_eq
    {atomFamily : Fin (thresholdSize rank) → Fin rank → ℝ}
    (hstressFree : ∀ coeff : Fin (thresholdSize rank) → ℝ,
      (∑ c, coeff c • atomMatrix (atomFamily c)) = 0 → coeff = 0)
    {target : Matrix (Fin rank) (Fin rank) ℝ} (hsymm : targetᵀ = target) :
    ∃ coeff : Fin (thresholdSize rank) → ℝ,
      (∑ c, coeff c • atomMatrix (atomFamily c)) = target := by
  have hdim : Module.finrank ℝ (Fin (thresholdSize rank) → ℝ)
      = Module.finrank ℝ ({ p : Fin rank × Fin rank // p.1 ≤ p.2 } → ℝ) := by
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_fin, card_orderedPairs]
    rfl
  have hsurjective : Function.Surjective (atomCoordMap atomFamily) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (injective_atomCoordMap_of_stressFree hstressFree)
  obtain ⟨coeff, hcoeff⟩ := hsurjective (upperTriangleCoords target)
  refine ⟨coeff, sub_eq_zero.mp (symmetric_eq_zero_of_coords_eq_zero ?_ ?_)⟩
  · rw [Matrix.transpose_sub, transpose_atomCombination, hsymm]
  · rw [map_sub, ← atomCoordMap_apply, hcoeff, sub_self]

/-- The design-level reading: the atom matrices of a stress-free threshold-cell
design span the symmetric matrices. -/
theorem exists_atomCombination_of_design
    (design : WeightedDesign (thresholdSize rank) rank)
    (hstressFree : ∀ coeff : Fin (thresholdSize rank) → ℝ,
      (∑ c, coeff c • atomMatrix (design.atom c)) = 0 → coeff = 0)
    {target : Matrix (Fin rank) (Fin rank) ℝ} (hsymm : targetᵀ = target) :
    ∃ coeff : Fin (thresholdSize rank) → ℝ,
      (∑ c, coeff c • atomMatrix (design.atom c)) = target :=
  exists_atomCombination_of_transpose_eq hstressFree hsymm

/-- **THE COEFFICIENTS ARE UNIQUE.**  Independence turns the span into a basis,
thus every symmetric target has EXACTLY one coefficient vector. -/
theorem existsUnique_atomCombination_of_design
    (design : WeightedDesign (thresholdSize rank) rank)
    (hstressFree : ∀ coeff : Fin (thresholdSize rank) → ℝ,
      (∑ c, coeff c • atomMatrix (design.atom c)) = 0 → coeff = 0)
    {target : Matrix (Fin rank) (Fin rank) ℝ} (hsymm : targetᵀ = target) :
    ∃! coeff : Fin (thresholdSize rank) → ℝ,
      (∑ c, coeff c • atomMatrix (design.atom c)) = target := by
  obtain ⟨coeff, hcoeff⟩ := exists_atomCombination_of_design design hstressFree hsymm
  refine ⟨coeff, hcoeff, fun other hother => ?_⟩
  have hdiff : (∑ c, (other - coeff) c • atomMatrix (design.atom c)) = 0 := by
    have hpointwise : ∀ c, (other - coeff) c • atomMatrix (design.atom c)
        = other c • atomMatrix (design.atom c) - coeff c • atomMatrix (design.atom c) :=
      fun c => by rw [Pi.sub_apply, sub_smul]
    rw [Finset.sum_congr rfl fun c _ => hpointwise c, Finset.sum_sub_distrib, hcoeff,
      hother, sub_self]
  exact sub_eq_zero.mp (hstressFree _ hdiff)

/-- **THE WEIGHTS ARE THE UNIQUE PARSEVAL COEFFICIENTS.**  At the threshold cell
a stress-free design has exactly one coefficient vector resolving the identity,
and the design's own weights are it. This is the general-rank form of the
normalizer-form uniqueness the registry records as a rank-three instrument, and
it fails below the threshold cell for want of independence. -/
theorem eq_weight_of_atomCombination_eq_one
    (design : WeightedDesign (thresholdSize rank) rank)
    (hstressFree : ∀ coeff : Fin (thresholdSize rank) → ℝ,
      (∑ c, coeff c • atomMatrix (design.atom c)) = 0 → coeff = 0)
    {coeff : Fin (thresholdSize rank) → ℝ}
    (hcoeff : (∑ c, coeff c • atomMatrix (design.atom c)) = 1) :
    coeff = design.weight := by
  obtain ⟨parsevalCoeff, -, hunique⟩ :=
    existsUnique_atomCombination_of_design design hstressFree
      (target := (1 : Matrix (Fin rank) (Fin rank) ℝ)) Matrix.transpose_one
  rw [hunique coeff hcoeff, hunique design.weight design.isParseval]

/-! ## Part 3: the stress trichotomy at every rank

The rank-three trichotomy sorts a stress by SUPPORT. That reading needs
`size <= 2 * rank`. The reading that survives sorts a stress by SPANNING, and
needs nothing. -/

/-- The two sign sides of a stress add up to the whole stress: the labels the
stress misses contribute nothing. This is the support-free form of the
rank-three rearrangement. -/
theorem sideSum_add_sideSum (atomFamily : Fin n → Fin k → ℝ) (stressCoeff : Fin n → ℝ) :
    (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
        stressCoeff c • atomMatrix (atomFamily c))
      + (∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
          stressCoeff c • atomMatrix (atomFamily c))
      = ∑ c, stressCoeff c • atomMatrix (atomFamily c) := by
  classical
  have hdisjoint : Disjoint (Finset.univ.filter fun c => 0 < stressCoeff c)
      (Finset.univ.filter fun c => stressCoeff c < 0) := by
    rw [Finset.disjoint_left]
    intro c hpos hneg
    exact absurd (Finset.mem_filter.mp hneg).2 (asymm (Finset.mem_filter.mp hpos).2)
  rw [← Finset.sum_union hdisjoint]
  refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_
  have hzero : stressCoeff c = 0 := by
    by_contra hne
    rcases lt_or_lt_iff_ne.mpr hne with hlt | hgt
    · exact hc (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hlt⟩))
    · exact hc (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hgt⟩))
  rw [hzero, zero_smul]

/-- **THE TWO-FRAME EQUALITY WITHOUT FULL SUPPORT.**  The positive side's
weighted atom sum equals the negative side's with absolute coefficients. The
shipped `Gtz.posSide_sum_eq_negSide_sum` demands full support, which the
threshold cell does not supply above rank three. -/
theorem posSideSum_eq_negSideSum (atomFamily : Fin n → Fin k → ℝ)
    {stressCoeff : Fin n → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0) :
    (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
        stressCoeff c • atomMatrix (atomFamily c))
      = ∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
          (-stressCoeff c) • atomMatrix (atomFamily c) := by
  classical
  have hsplit := sideSum_add_sideSum atomFamily stressCoeff
  rw [hstress] at hsplit
  have hnegSide : (∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
        (-stressCoeff c) • atomMatrix (atomFamily c))
      = -∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
          stressCoeff c • atomMatrix (atomFamily c) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun c _ => by rw [neg_smul]
  rw [hnegSide]
  exact add_eq_zero_iff_eq_neg.mp hsplit

/-- The transfer law in the second orientation: a probe killing the negative
side kills the positive side. -/
theorem pos_side_orthogonal_of_neg_side {atomFamily : Fin n → Fin k → ℝ}
    {stressCoeff : Fin n → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0) {probe : Fin k → ℝ}
    (hnegSide : ∀ c, stressCoeff c < 0 → atomFamily c ⬝ᵥ probe = 0) :
    ∀ c, 0 < stressCoeff c → atomFamily c ⬝ᵥ probe = 0 := by
  have hmirror : ∑ c, (-stressCoeff) c • atomMatrix (atomFamily c) = 0 :=
    stress_of_neg_stress hstress
  have hposMirror : ∀ c, 0 < (-stressCoeff) c → atomFamily c ⬝ᵥ probe = 0 := by
    intro c hc
    rw [Pi.neg_apply] at hc
    exact hnegSide c (by linarith)
  intro c hc
  refine neg_side_orthogonal_of_pos_side hmirror hposMirror c ?_
  rw [Pi.neg_apply]
  linarith

/-- **A SPANNING SIGN SIDE HAS A POSITIVE DEFINITE SUM.**  The shipped
`Gtz.posDef_posSide_sum` reaches this through full support. Here the spanning
hypothesis is taken directly, which is what the general-rank trichotomy
produces. -/
theorem posDef_posSideSum_of_spans (atomFamily : Fin n → Fin k → ℝ)
    {stressCoeff : Fin n → ℝ}
    (hspans : ∀ probe : Fin k → ℝ,
      (∀ c, 0 < stressCoeff c → atomFamily c ⬝ᵥ probe = 0) → probe = 0) :
    (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
      stressCoeff c • atomMatrix (atomFamily c)).PosDef := by
  classical
  have hsymm : (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
        stressCoeff c • atomMatrix (atomFamily c))ᵀ
      = ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
          stressCoeff c • atomMatrix (atomFamily c) := by
    rw [Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (atomFamily c)).1]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobe => ?_⟩
  rw [star_trivial, weighted_atomForm_eq_on]
  have hterms : ∀ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
      0 ≤ stressCoeff c * (atomFamily c ⬝ᵥ probe) ^ 2 := fun c hc =>
    mul_nonneg (Finset.mem_filter.mp hc).2.le (sq_nonneg _)
  refine Finset.sum_pos' hterms ?_
  by_contra hcontra
  push Not at hcontra
  refine hprobe (hspans probe fun c hc => ?_)
  have hle := hcontra c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)
  have hsq : (atomFamily c ⬝ᵥ probe) ^ 2 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    exact absurd hle (not_le.mpr (mul_pos hc hpos))
  exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hsq (sq_nonneg _))

/-- **BOTH SIDES BIG PLUS A NARROW CELL FORCES FULL SUPPORT.**  This is the one
place the cell size enters the balanced branch, and it is the exact place the
rank split happens: at the threshold cell the hypothesis `size <= 2 * rank`
holds if and only if `rank <= 3` (`Gtz.thresholdSize_le_two_mul_iff`). -/
theorem stress_fullSupport_of_sides_of_size_le {stressCoeff : Fin n → ℝ}
    (hpos : k ≤ (Finset.univ.filter fun c => 0 < stressCoeff c).card)
    (hneg : k ≤ (Finset.univ.filter fun c => stressCoeff c < 0).card)
    (hsize : n ≤ 2 * k) : ∀ c, stressCoeff c ≠ 0 := by
  classical
  have hdisjoint : Disjoint (Finset.univ.filter fun c => 0 < stressCoeff c)
      (Finset.univ.filter fun c => stressCoeff c < 0) := by
    rw [Finset.disjoint_left]
    intro c hposMem hnegMem
    exact absurd (Finset.mem_filter.mp hnegMem).2 (asymm (Finset.mem_filter.mp hposMem).2)
  have hcardUnion : ((Finset.univ.filter fun c => 0 < stressCoeff c)
        ∪ (Finset.univ.filter fun c => stressCoeff c < 0)).card
      = (Finset.univ.filter fun c => 0 < stressCoeff c).card
        + (Finset.univ.filter fun c => stressCoeff c < 0).card :=
    Finset.card_union_of_disjoint hdisjoint
  have hcardTotal : ((Finset.univ.filter fun c => 0 < stressCoeff c)
      ∪ (Finset.univ.filter fun c => stressCoeff c < 0)).card = Fintype.card (Fin n) := by
    have hle : ((Finset.univ.filter fun c => 0 < stressCoeff c)
        ∪ (Finset.univ.filter fun c => stressCoeff c < 0)).card ≤ Fintype.card (Fin n) :=
      Finset.card_le_univ _
    rw [Fintype.card_fin] at hle ⊢
    omega
  have huniv : (Finset.univ.filter fun c => 0 < stressCoeff c)
      ∪ (Finset.univ.filter fun c => stressCoeff c < 0) = Finset.univ :=
    Finset.eq_univ_of_card _ hcardTotal
  intro c hzero
  have hmem : c ∈ (Finset.univ.filter fun c => 0 < stressCoeff c)
      ∪ (Finset.univ.filter fun c => stressCoeff c < 0) := by
    rw [huniv]; exact Finset.mem_univ c
  rcases Finset.mem_union.mp hmem with hposMem | hnegMem
  · exact absurd hzero (ne_of_gt (Finset.mem_filter.mp hposMem).2)
  · exact absurd hzero (ne_of_lt (Finset.mem_filter.mp hnegMem).2)

/-- **THE STRESS TRICHOTOMY AT EVERY SIZE AND EVERY RANK.**  Every weighted
design falls into at least one of three strata:

(i) stress-free -- the atom matrices are independent;

(ii) balanced -- some nonzero stress has BOTH sign sides spanning, thus at least
`rank` labels on each side, a positive definite positive-side sum, and the
two-frame equality;

(iii) degenerate -- some nonzero stress admits a common nonzero probe orthogonal
to every supported atom.

The shipped `Gtz.sixThree_stress_trichotomy` is the rank-three instance, and it
reads the branch (ii) hypothesis as FULL SUPPORT. That reading rides
`Gtz.stress_fullSupport_or_orthogonalProbe`, whose hypothesis `size <= 2 * rank`
fails at the threshold cell of every rank above three. The spanning reading here
carries no size hypothesis at all. -/
theorem design_stress_trichotomy (design : WeightedDesign size rank) :
    (∀ stressCoeff : Fin size → ℝ,
        (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → stressCoeff = 0)
    ∨ (∃ stressCoeff : Fin size → ℝ, stressCoeff ≠ 0
        ∧ (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0
        ∧ (∀ probe : Fin rank → ℝ,
            (∀ c, 0 < stressCoeff c → design.atom c ⬝ᵥ probe = 0) → probe = 0)
        ∧ (∀ probe : Fin rank → ℝ,
            (∀ c, stressCoeff c < 0 → design.atom c ⬝ᵥ probe = 0) → probe = 0)
        ∧ rank ≤ (Finset.univ.filter fun c => 0 < stressCoeff c).card
        ∧ rank ≤ (Finset.univ.filter fun c => stressCoeff c < 0).card
        ∧ (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
            stressCoeff c • atomMatrix (design.atom c)).PosDef
        ∧ (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
              stressCoeff c • atomMatrix (design.atom c))
            = ∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
                (-stressCoeff c) • atomMatrix (design.atom c))
    ∨ (∃ (stressCoeff : Fin size → ℝ) (probe : Fin rank → ℝ),
        stressCoeff ≠ 0 ∧ probe ≠ 0
        ∧ (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0
        ∧ ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0) := by
  classical
  by_cases hfree : ∀ stressCoeff : Fin size → ℝ,
      (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → stressCoeff = 0
  · exact Or.inl hfree
  push Not at hfree
  obtain ⟨stressCoeff, hstress, hstressNe⟩ := hfree
  by_cases hprobe : ∃ probe : Fin rank → ℝ, probe ≠ 0
      ∧ ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0
  · obtain ⟨probe, hprobeNe, hprobeOrth⟩ := hprobe
    exact Or.inr (Or.inr ⟨stressCoeff, probe, hstressNe, hprobeNe, hstress, hprobeOrth⟩)
  push Not at hprobe
  have hkill : ∀ probe : Fin rank → ℝ,
      (∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0) → probe = 0 := by
    intro probe hprobeOrth
    by_contra hprobeNe
    obtain ⟨c, hc, hne⟩ := hprobe probe hprobeNe
    exact hne (hprobeOrth c hc)
  have hposSpans : ∀ probe : Fin rank → ℝ,
      (∀ c, 0 < stressCoeff c → design.atom c ⬝ᵥ probe = 0) → probe = 0 := by
    intro probe hposSide
    refine hkill probe fun c hc => ?_
    rcases lt_or_lt_iff_ne.mpr hc with hlt | hgt
    · exact neg_side_orthogonal_of_pos_side hstress hposSide c hlt
    · exact hposSide c hgt
  have hnegSpans : ∀ probe : Fin rank → ℝ,
      (∀ c, stressCoeff c < 0 → design.atom c ⬝ᵥ probe = 0) → probe = 0 := by
    intro probe hnegSide
    refine hkill probe fun c hc => ?_
    rcases lt_or_lt_iff_ne.mpr hc with hlt | hgt
    · exact hnegSide c hlt
    · exact pos_side_orthogonal_of_neg_side hstress hnegSide c hgt
  have hposCard : rank ≤ (Finset.univ.filter fun c => 0 < stressCoeff c).card := by
    by_contra hsmall
    push Not at hsmall
    obtain ⟨probe, hprobeNe, hprobeOrth⟩ := exists_ne_zero_orthogonal_of_card_lt
      design.atom (Finset.univ.filter fun c => 0 < stressCoeff c) hsmall
    exact hprobeNe (hposSpans probe fun c hc =>
      hprobeOrth c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩))
  have hnegCard : rank ≤ (Finset.univ.filter fun c => stressCoeff c < 0).card := by
    by_contra hsmall
    push Not at hsmall
    obtain ⟨probe, hprobeNe, hprobeOrth⟩ := exists_ne_zero_orthogonal_of_card_lt
      design.atom (Finset.univ.filter fun c => stressCoeff c < 0) hsmall
    exact hprobeNe (hnegSpans probe fun c hc =>
      hprobeOrth c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩))
  exact Or.inr (Or.inl ⟨stressCoeff, hstressNe, hstress, hposSpans, hnegSpans,
    hposCard, hnegCard, posDef_posSideSum_of_spans design.atom hposSpans,
    posSideSum_eq_negSideSum design.atom hstress⟩)

/-! ## Part 4: the general-rank carriers

The two rank-three selection Props hard-code rank three in their types. Both
lift verbatim by replacing `Fin 3` with `Fin rank` and the card-three subsets
with card-`rank` subsets, because every ingredient they read
(`Gtz.HasStressMassGap`, `Gtz.HasFreeMassBudget`, `Gtz.IsPrimitiveDesign`,
`Gtz.subsetSum`) is already rank-uniform. The lifts below are DEFINITIONALLY
the rank-three originals at rank three, which the two `Iff.rfl` bridges
certify. -/

/-- The balanced-stratum selection at general rank. At rank three this is
`Gtz.BalancedStratumSelection` on the nose. -/
def BalancedStratumSelectionAtRank (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ),
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ c, stressCoeff c ≠ 0) →
    IsPrimitiveDesign design →
    ¬ HasStressMassGap design stressCoeff →
    ¬ HasStressMassGap design (-stressCoeff) →
    (∀ selected : Finset (Fin size), selected.card = rank →
      ¬ HasFreeMassBudget design selected) →
    ∃ dominating : Finset (Fin size), dominating.card = rank
      ∧ (subsetSum design dominating - 1).PosDef

/-- The lift is faithful at rank three. -/
theorem balancedStratumSelectionAtRank_three (size : ℕ) :
    BalancedStratumSelectionAtRank size 3 ↔ BalancedStratumSelection size := Iff.rfl

/-- The two-pole selection at general rank, stated for the record. The TYPE
lifts, but the CONTENT does not: at rank three the degenerate branch has at most
two atoms off the probe plane (`Gtz.sixThree_offPlaneCard_le_two_of_coplanarStress`)
and this Prop is the two-pole cell. At rank four and up no such bound is
available, so the assembly below routes the degenerate branch through
`Gtz.ThresholdDegenerateArm` and never through this Prop. -/
def TwoPoleStratumSelectionAtRank (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (probe : Fin rank → ℝ) (tiltRatio : ℝ),
    probe ⬝ᵥ probe = 1 →
    ∀ poleP poleQ : Fin size, poleP ≠ poleQ →
      (∀ c, c ≠ poleP → c ≠ poleQ → design.atom c ⬝ᵥ probe = 0) →
      design.atom poleP ⬝ᵥ probe ≠ 0 → design.atom poleQ ⬝ᵥ probe ≠ 0 →
      IsPrimitiveDesign design →
      design.atom poleQ - (design.atom poleQ ⬝ᵥ probe) • probe
          = tiltRatio • (design.atom poleP
            - (design.atom poleP ⬝ᵥ probe) • probe) →
      ¬ (((design.atom poleP ⬝ᵥ probe) ^ 2
              + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
            * (1 - ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                  ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
                * (design.weight poleP + design.weight poleQ * tiltRatio ^ 2))
          < (((design.atom poleP ⬝ᵥ probe) ^ 2
                  + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
                * (((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                      ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
                    * (1 + tiltRatio ^ 2) - 1)
              - ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                  ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
                * ((design.atom poleP ⬝ᵥ probe)
                    + tiltRatio * (design.atom poleQ ⬝ᵥ probe)) ^ 2)
            * (design.weight poleP + design.weight poleQ)) →
      ∃ dominating : Finset (Fin size), dominating.card = rank
        ∧ (subsetSum design dominating - 1).PosDef

/-- The two-pole lift is faithful at rank three. -/
theorem twoPoleStratumSelectionAtRank_three (size : ℕ) :
    TwoPoleStratumSelectionAtRank size 3 ↔ TwoPoleStratumSelection size := Iff.rfl

/-! ## Part 5: the three arms, at every cell

`Gtz.design_stress_trichotomy` carries no size hypothesis, thus the arms are
stated at general size and rank. ONE engine then closes the structure of BOTH
hinge obligations of the registry: the threshold cell obligation
`Skeleton.obligationThresholdCellHingeRankFourAndUp` and the sub-threshold band
obligation `Skeleton.obligationSubThresholdBandHinge`. -/

/-- **ARM (i), the stress-free arm.**  At the threshold cell the atom matrices
are a BASIS of the symmetric matrices (`Gtz.exists_atomCombination_of_design`).
At rank three and the threshold cell this is
`Gtz.StressFreeHingeHoldsSixThree`, the open five-class frontier. -/
def StressFreeArmAt (size rank : ℕ) : Prop :=
  ∀ design : WeightedDesign size rank,
    (∀ stressCoeff : Fin size → ℝ,
      (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → stressCoeff = 0) →
      IsTie design → HasParallelPair design

/-- **ARM (ii), the balanced arm.**  Both sign sides of the stress span. At rank
three and the threshold cell this follows from `Gtz.BalancedStratumCapstone`,
which is CLOSED. -/
def BalancedArmAt (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ),
    stressCoeff ≠ 0 →
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ probe : Fin rank → ℝ,
      (∀ c, 0 < stressCoeff c → design.atom c ⬝ᵥ probe = 0) → probe = 0) →
    (∀ probe : Fin rank → ℝ,
      (∀ c, stressCoeff c < 0 → design.atom c ⬝ᵥ probe = 0) → probe = 0) →
    IsTie design → HasParallelPair design

/-- **ARM (iii), the degenerate arm.**  Some nonzero stress is supported inside
a hyperplane. At rank three and the threshold cell this follows from
`Gtz.TwoPoleStratumSelection 6`, which is CLOSED. -/
def DegenerateArmAt (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ)
      (probe : Fin rank → ℝ),
    stressCoeff ≠ 0 → probe ≠ 0 →
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0) →
    IsTie design → HasParallelPair design

/-- **THE HINGE FROM THE THREE ARMS, AT EVERY SIZE AND EVERY RANK.**  The split
is `Gtz.design_stress_trichotomy`, which needs no size hypothesis and no
predecessor cell. -/
theorem hingeHoldsAtSize_of_arms (size rank : ℕ)
    (hfreeArm : StressFreeArmAt size rank) (hbalancedArm : BalancedArmAt size rank)
    (hdegenerateArm : DegenerateArmAt size rank) :
    HingeHoldsAtSize size rank := by
  intro design htie
  rcases design_stress_trichotomy design with
    hfree | ⟨stressCoeff, hstressNe, hstress, hposSpans, hnegSpans, -, -, -, -⟩
      | ⟨stressCoeff, probe, hstressNe, hprobeNe, hstress, hsupport⟩
  · exact hfreeArm design hfree htie
  · exact hbalancedArm design stressCoeff hstressNe hstress hposSpans hnegSpans htie
  · exact hdegenerateArm design stressCoeff probe hstressNe hprobeNe hstress hsupport htie

/-! ### The three arms at the deciding cell -/

/-- Arm (i) at the deciding cell of a rank. -/
def ThresholdStressFreeArm (rank : ℕ) : Prop := StressFreeArmAt (thresholdSize rank) rank

/-- Arm (ii) at the deciding cell of a rank. -/
def ThresholdBalancedArm (rank : ℕ) : Prop := BalancedArmAt (thresholdSize rank) rank

/-- Arm (iii) at the deciding cell of a rank. -/
def ThresholdDegenerateArm (rank : ℕ) : Prop := DegenerateArmAt (thresholdSize rank) rank

theorem thresholdCellHinge_of_arms (rank : ℕ)
    (hfreeArm : ThresholdStressFreeArm rank) (hbalancedArm : ThresholdBalancedArm rank)
    (hdegenerateArm : ThresholdDegenerateArm rank) :
    ∀ design : WeightedDesign (thresholdSize rank) rank,
      IsTie design → HasParallelPair design :=
  hingeHoldsAtSize_of_arms (thresholdSize rank) rank hfreeArm hbalancedArm hdegenerateArm

/-- The hinge at the deciding cell, in the tree's own vocabulary. -/
theorem hingeHoldsAtSize_thresholdCell_of_arms (rank : ℕ)
    (hfreeArm : ThresholdStressFreeArm rank) (hbalancedArm : ThresholdBalancedArm rank)
    (hdegenerateArm : ThresholdDegenerateArm rank) :
    HingeHoldsAtSize (thresholdSize rank) rank :=
  hingeHoldsAtSize_of_arms (thresholdSize rank) rank hfreeArm hbalancedArm hdegenerateArm

/-! ### The two registry hinge obligations, from the one engine -/

/-- **THE THRESHOLD CELL OBLIGATION, REDUCED TO THREE NAMED PROPS.**  This is the
statement of `Skeleton.obligationThresholdCellHingeRankFourAndUp` with the
predecessor cell hypothesis carried but NOT consumed: the split is a tautology
on stress structure, and no cell below the threshold enters it. The predecessor
cell is what the funnel above the hinge needs, not what the hinge needs. -/
theorem thresholdCellHingeRankFourAndUp_of_arms
    (hfreeArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdStressFreeArm rank)
    (hbalancedArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdBalancedArm rank)
    (hdegenerateArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdDegenerateArm rank) :
    ∀ rank : ℕ, 4 ≤ rank →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank _hpredecessor design htie
  exact thresholdCellHinge_of_arms rank (hfreeArm rank hrank) (hbalancedArm rank hrank)
    (hdegenerateArm rank hrank) design htie

/-- **THE SHARPENED FORM.**  The predecessor cell is not consumed, thus the
three arms alone close the obligation at every rank above three. -/
theorem thresholdCellHingeRankFourAndUp_of_arms_predecessorFree
    (hfreeArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdStressFreeArm rank)
    (hbalancedArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdBalancedArm rank)
    (hdegenerateArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdDegenerateArm rank) :
    ∀ rank : ℕ, 4 ≤ rank →
      ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
        IsTie design → HasParallelPair design := by
  intro rank hrank design htie
  exact thresholdCellHinge_of_arms rank (hfreeArm rank hrank) (hbalancedArm rank hrank)
    (hdegenerateArm rank hrank) design htie

/-- **THE SUB-THRESHOLD BAND OBLIGATION, REDUCED BY THE SAME ENGINE.**  This is
the statement of `Skeleton.obligationSubThresholdBandHinge` verbatim. The band
runs over `2 * rank <= size < thresholdSize rank`, it is EMPTY at rank three
(`Gtz.subThresholdBand_empty_at_rank_three`), and it holds
`rank * (rank - 3) / 2` cells at every rank (`Gtz.card_subThresholdBand`). The
predecessor cell is again carried and not consumed.

Below the threshold cell arm (i) is NOT a basis statement, because the atom
matrices are too few to span. That is the whole difference between the two
obligations, and it is why the registry keeps them apart. -/
theorem subThresholdBandHinge_of_arms
    (hfreeArm : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size < thresholdSize rank → StressFreeArmAt size rank)
    (hbalancedArm : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size < thresholdSize rank → BalancedArmAt size rank)
    (hdegenerateArm : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size < thresholdSize rank → DegenerateArmAt size rank) :
    ∀ rank : ℕ, 3 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design := by
  intro rank hrank size hlow hhigh _hpredecessor design htie
  exact hingeHoldsAtSize_of_arms size rank (hfreeArm rank size hrank hlow hhigh)
    (hbalancedArm rank size hrank hlow hhigh) (hdegenerateArm rank size hrank hlow hhigh)
    design htie

/-- **THE WHOLE SHARP WINDOW FROM ONE ENGINE.**  The band obligation and the
threshold cell obligation are the two halves of the closed window
`2 * rank <= size <= thresholdSize rank`, and the three arms close all of it at
once. This is the shape a successor should prove, because the two registry
obligations differ only in which end of the window they name. -/
theorem sharpWindowHinge_of_arms
    (hfreeArm : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size ≤ thresholdSize rank → StressFreeArmAt size rank)
    (hbalancedArm : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size ≤ thresholdSize rank → BalancedArmAt size rank)
    (hdegenerateArm : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size ≤ thresholdSize rank → DegenerateArmAt size rank) :
    ∀ rank : ℕ, 3 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        HingeHoldsAtSize size rank := by
  intro rank hrank size hlow hhigh
  exact hingeHoldsAtSize_of_arms size rank (hfreeArm rank size hrank hlow hhigh)
    (hbalancedArm rank size hrank hlow hhigh) (hdegenerateArm rank size hrank hlow hhigh)

/-! ### The two cell counts the registry quotes, as kernel facts -/

/-- **THE SUB-THRESHOLD BAND HOLDS `rank * (rank - 3) / 2` CELLS.**  The registry
records this count in prose. It is the same number as the width of the
admissible sign-split window (`Gtz.two_mul_thresholdSplitWindow`), because both
are `thresholdSize rank - 2 * rank`. -/
theorem card_subThresholdBand (rank : ℕ) (hrank : 3 ≤ rank) :
    (Finset.Ico (2 * rank) (thresholdSize rank)).card = rank * (rank - 3) / 2 := by
  rw [Nat.card_Ico]
  exact thresholdSplitWindow rank hrank

/-- The closed sharp window holds one cell more. -/
theorem card_sharpWindow (rank : ℕ) (hrank : 3 ≤ rank) :
    (Finset.Icc (2 * rank) (thresholdSize rank)).card = rank * (rank - 3) / 2 + 1 := by
  have hwindow := two_mul_thresholdSplitWindow rank hrank
  have hfloor := two_mul_le_thresholdSize rank hrank
  rw [Nat.card_Icc]
  omega

/-- **THE BAND IS EMPTY AT RANK THREE.**  So no rank-three theorem in the tree is
evidence about the band obligation, exactly as the registry records. -/
theorem subThresholdBand_empty_at_rank_three :
    Finset.Ico (2 * 3) (thresholdSize 3) = ∅ := by
  rw [thresholdSize_three]
  rfl

/-- At rank four the band is the two cells eight and nine. -/
theorem card_subThresholdBand_four :
    (Finset.Ico (2 * 4) (thresholdSize 4)).card = 2 := by
  rw [card_subThresholdBand 4 (by norm_num)]

/-! ## Part 6: the stress-free arm

Everything the rank-three arm knows lifts. The arm itself does not, and no proof
of it exists at any rank to lift. -/

/-- **A STRESS-FREE DESIGN HAS NO PARALLEL PAIR, AT EVERY SIZE AND RANK.**  A
parallel pair manufactures a stress: put `1` at the duplicate and the squared
ratio at the original. The shipped `Gtz.isPrimitiveDesign_of_stressFree` states
this at `(6,3)` only. -/
theorem isPrimitiveDesign_of_stressFree_general (design : WeightedDesign size rank)
    (hstressFree : ∀ stressCoeff : Fin size → ℝ,
      (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → stressCoeff = 0) :
    IsPrimitiveDesign design := by
  classical
  intro keptLabel dropLabel ratio hdistinct hparallel
  set stressCoeff : Fin size → ℝ := fun c =>
    (if c = dropLabel then (1 : ℝ) else 0) - (if c = keptLabel then ratio ^ 2 else 0)
    with hstressDef
  have hstress : (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 := by
    have hdrop : atomMatrix (design.atom dropLabel)
        = ratio ^ 2 • atomMatrix (design.atom keptLabel) := by
      rw [hparallel, atomMatrix_smul]
    have hpointwise : ∀ c, stressCoeff c • atomMatrix (design.atom c)
        = (if c = dropLabel then (1 : ℝ) else 0) • atomMatrix (design.atom c)
          - (if c = keptLabel then ratio ^ 2 else 0) • atomMatrix (design.atom c) := by
      intro c
      rw [hstressDef, sub_smul]
    rw [Finset.sum_congr rfl fun c _ => hpointwise c, Finset.sum_sub_distrib]
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_pos]
    rw [hdrop, one_smul, sub_self]
  have hentry : stressCoeff dropLabel = 0 := congrFun (hstressFree stressCoeff hstress) dropLabel
  rw [hstressDef] at hentry
  simp only [if_neg (Ne.symm hdistinct)] at hentry
  norm_num at hentry

/-- **THE STRESS-FREE ARM IS A TIE-EMPTINESS STATEMENT, AT EVERY RANK.**  On the
stress-free stratum a parallel pair cannot exist, thus the arm's conclusion is
unreachable and the arm says exactly that no design whose atom matrices are a
basis of the symmetric matrices is a tie. There is no weaker certificate
reading: every strict-domination certificate fails at a tie by definition. The
shipped `Gtz.stressFreeHingeHoldsSixThree_iff_no_stressFree_tie` is the
rank-three instance. -/
theorem stressFreeArmAt_iff_no_stressFree_tie (size rank : ℕ) :
    StressFreeArmAt size rank ↔
      ∀ design : WeightedDesign size rank,
        (∀ stressCoeff : Fin size → ℝ,
          (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → stressCoeff = 0) →
          ¬ IsTie design := by
  refine ⟨fun harm design hfree htie => ?_, fun hempty design hfree htie =>
    absurd htie (hempty design hfree)⟩
  exact (isPrimitiveDesign_iff_not_hasParallelPair design).mp
    (isPrimitiveDesign_of_stressFree_general design hfree) (harm design hfree htie)

/-- The same reading at the deciding cell, where the stress-free hypothesis is
the BASIS property. -/
theorem thresholdStressFreeArm_iff_no_stressFree_tie (rank : ℕ) :
    ThresholdStressFreeArm rank ↔
      ∀ design : WeightedDesign (thresholdSize rank) rank,
        (∀ stressCoeff : Fin (thresholdSize rank) → ℝ,
          (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → stressCoeff = 0) →
          ¬ IsTie design :=
  stressFreeArmAt_iff_no_stressFree_tie (thresholdSize rank) rank

/-! ## Part 7: the rank-three faithfulness certificate

The three arms are a genuine lift and not a re-labelling: at rank three they are
exactly the tree's three branches, two closed and one open. -/

/-- Arm (i) at rank three IS the open rank-three frontier. -/
theorem thresholdStressFreeArm_three_iff :
    ThresholdStressFreeArm 3 ↔ StressFreeHingeHoldsSixThree := Iff.rfl

/-- **ARM (ii) AT RANK THREE IS CLOSED.**  The two spanning sides give at least
three labels each, the cell has six labels and `6 <= 2 * 3`, thus
`Gtz.stress_fullSupport_of_sides_of_size_le` upgrades the spanning hypothesis to
FULL SUPPORT and the closed branch-(ii) capstone fires. This upgrade is the
exact step that fails at rank four and up. -/
theorem thresholdBalancedArm_three_of_capstone (hbalanced : BalancedStratumCapstone) :
    ThresholdBalancedArm 3 := by
  intro design stressCoeff _hstressNe hstress hposSpans hnegSpans htie
  have hposCard : 3 ≤ (Finset.univ.filter fun c => 0 < stressCoeff c).card := by
    by_contra hsmall
    push Not at hsmall
    obtain ⟨probe, hprobeNe, hprobeOrth⟩ := exists_ne_zero_orthogonal_of_card_lt
      design.atom (Finset.univ.filter fun c => 0 < stressCoeff c) hsmall
    exact hprobeNe (hposSpans probe fun c hc =>
      hprobeOrth c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩))
  have hnegCard : 3 ≤ (Finset.univ.filter fun c => stressCoeff c < 0).card := by
    by_contra hsmall
    push Not at hsmall
    obtain ⟨probe, hprobeNe, hprobeOrth⟩ := exists_ne_zero_orthogonal_of_card_lt
      design.atom (Finset.univ.filter fun c => stressCoeff c < 0) hsmall
    exact hprobeNe (hnegSpans probe fun c hc =>
      hprobeOrth c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩))
  exact hbalanced design htie stressCoeff hstress
    (stress_fullSupport_of_sides_of_size_le hposCard hnegCard (by norm_num))

/-- **ARM (iii) AT RANK THREE IS CLOSED.**  The shipped two-pole capstone
consumes exactly this branch data. -/
theorem thresholdDegenerateArm_three_of_selection (hselection : TwoPoleStratumSelection 6) :
    ThresholdDegenerateArm 3 :=
  fun design _stressCoeff _probe hstressNe hprobeNe hstress hsupport htie =>
    sixThree_hasParallelPair_of_isTie_of_coplanarStress hselection design htie
      hstressNe hprobeNe hstress hsupport

/-- **THE FAITHFULNESS CERTIFICATE.**  At rank three the general assembly gives
back `Gtz.HingeHoldsAtSize 6 3` from exactly the tree's own three inputs: two
closed capstones and the one open stress-free arm. So the general-rank arms are
a lift of the rank-three assembly and not a different decomposition. -/
theorem thresholdArms_rank_three_faithful
    (hselection : TwoPoleStratumSelection 6) (hbalanced : BalancedStratumCapstone)
    (hstressFreeArm : StressFreeHingeHoldsSixThree) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_thresholdCell_of_arms 3 hstressFreeArm
    (thresholdBalancedArm_three_of_capstone hbalanced)
    (thresholdDegenerateArm_three_of_selection hselection)

/-! ## Part 8: the obstruction ledger

Four kernel facts, each naming a step of the rank-three assembly that stops at
rank three. They are the honest content of "the stressed arm fans out". -/

/-- **OBSTRUCTION ONE: the support dichotomy dies.**  The rank-three trichotomy
routes every partially supported stress into the coplanar branch through
`Gtz.stress_fullSupport_or_orthogonalProbe`, whose hypothesis is
`size <= 2 * rank`. At the threshold cell that hypothesis is available only at
rank three and below. -/
theorem not_thresholdSize_le_two_mul (rank : ℕ) (hrank : 4 ≤ rank) :
    ¬ thresholdSize rank ≤ 2 * rank :=
  fun hle => absurd ((thresholdSize_le_two_mul_iff rank).mp hle) (by omega)

/-- **OBSTRUCTION TWO: full support is no longer forced.**  At rank three the
two spanning sign sides fill the cell, thus the balanced branch is a
full-support branch and `Gtz.BalancedStratumCapstone` applies. At rank four and
up the same two sides leave `thresholdSize rank - 2 * rank` labels free, and
that count is `rank * (rank - 3) / 2`, which is positive. -/
theorem pos_thresholdSplitWindow (rank : ℕ) (hrank : 4 ≤ rank) :
    0 < thresholdSize rank - 2 * rank := by
  have hdouble := two_mul_thresholdSplitWindow rank (by omega)
  have hbig : 1 * 1 ≤ rank * (rank - 3) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- **OBSTRUCTION THREE: the sign split fans out.**  The admissible positive-side
count runs over `[rank, thresholdSize rank - rank]`, a single point at rank
three and a genuine interval at rank four and up. Both rank-three branch
capstones read a fixed split, thus neither has a statement to specialize to. -/
theorem thresholdSplit_fansOut (rank : ℕ) (hrank : 4 ≤ rank) :
    rank < thresholdSize rank - rank ∧ thresholdSize 3 - 3 = 3 :=
  ⟨lt_thresholdSize_sub_rank rank hrank, by rw [thresholdSize_three]⟩

/-- **THE POLE MASS IDENTITY, RANK-UNIFORM.**  On the degenerate branch every
supported atom is orthogonal to the probe, thus the whole squared probe length
is carried by the UNSUPPORTED atoms. At rank three the tree bounds their number
by two (`Gtz.sixThree_offPlaneCard_le_two_of_coplanarStress`) and the two-pole
cell is that bound. No such bound is available at the threshold cell of rank
four and up, where the unsupported labels can number up to
`thresholdSize rank - 1`. -/
theorem probe_mass_on_unsupported (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ} {probe : Fin rank → ℝ}
    (hsupport : ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0) :
    ∑ c ∈ Finset.univ.filter (fun c => stressCoeff c = 0),
        design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
      = probe ⬝ᵥ probe := by
  classical
  have hparseval : ∑ c, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe := by
    have hform : probe ⬝ᵥ ((1 : Matrix (Fin rank) (Fin rank) ℝ) *ᵥ probe)
        = ∑ c, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 := by
      rw [← design.isParseval]
      exact weighted_atomForm_eq design.weight design.atom probe
    rw [Matrix.one_mulVec] at hform
    exact hform.symm
  rw [← hparseval]
  refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_
  have hne : stressCoeff c ≠ 0 := fun hzero =>
    hc (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hzero⟩)
  rw [hsupport c hne]
  ring

/-- **OBSTRUCTION FOUR: the degenerate branch changes induction axis.**  On the
degenerate branch every supported atom lies in the hyperplane orthogonal to the
probe, thus the supported family has rank at most `rank - 1`. At rank three the
tree closes that branch by restricting to the plane, where GTZ is the THEOREM
`Gtz.gtz_rank_two`. At rank `k` the same restriction lands at rank `k - 1`,
where GTZ is the open conjecture one rank down, while the registry hypothesis
supplies only `Gtz.GtzWeighted (thresholdSize rank - 1) rank` -- one SIZE down
at the SAME rank. The two induction axes do not meet. -/
theorem degenerateBranch_supported_in_hyperplane (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ} {probe : Fin rank → ℝ}
    (hsupport : ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0)
    (hstressNe : stressCoeff ≠ 0) :
    ∃ c : Fin size, stressCoeff c ≠ 0 ∧ design.atom c ⬝ᵥ probe = 0 := by
  obtain ⟨c, hc⟩ := Function.ne_iff.mp hstressNe
  exact ⟨c, by simpa using hc, hsupport c (by simpa using hc)⟩

/-! ## Part 9: the anatomy of the stressed arm

Arm (ii) is where the registry says the branch analysis fans out. This part
takes it apart at general rank and names every piece. THREE residuals survive,
each with an exact reason, and the rank-three instance of the whole chain is
CLOSED -- which is the check that the chain is the right one. -/

/-- A spanning positive side carries at least `rank` labels. -/
theorem rank_le_posSideCard_of_spans (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ}
    (hposSpans : ∀ probe : Fin rank → ℝ,
      (∀ c, 0 < stressCoeff c → design.atom c ⬝ᵥ probe = 0) → probe = 0) :
    rank ≤ (Finset.univ.filter fun c => 0 < stressCoeff c).card := by
  classical
  by_contra hsmall
  push Not at hsmall
  obtain ⟨probe, hprobeNe, hprobeOrth⟩ := exists_ne_zero_orthogonal_of_card_lt
    design.atom (Finset.univ.filter fun c => 0 < stressCoeff c) hsmall
  exact hprobeNe (hposSpans probe fun c hc =>
    hprobeOrth c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩))

/-- A spanning negative side carries at least `rank` labels. -/
theorem rank_le_negSideCard_of_spans (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ}
    (hnegSpans : ∀ probe : Fin rank → ℝ,
      (∀ c, stressCoeff c < 0 → design.atom c ⬝ᵥ probe = 0) → probe = 0) :
    rank ≤ (Finset.univ.filter fun c => stressCoeff c < 0).card := by
  classical
  by_contra hsmall
  push Not at hsmall
  obtain ⟨probe, hprobeNe, hprobeOrth⟩ := exists_ne_zero_orthogonal_of_card_lt
    design.atom (Finset.univ.filter fun c => stressCoeff c < 0) hsmall
  exact hprobeNe (hnegSpans probe fun c hc =>
    hprobeOrth c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩))

/-- **SUB-ARM (ii-a), full support.**  The direct lift of the rank-three
balanced branch. -/
def BalancedFullSupportArmAt (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ),
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ c, stressCoeff c ≠ 0) →
    IsTie design → HasParallelPair design

/-- **SUB-ARM (ii-b), partial support with both sides spanning.**  This sub-arm
is EMPTY at rank three (`Gtz.balancedPartialSupportArmAt_of_size_le`) and has no
rank-three analogue at all. It is the first of the three things that fan out. -/
def BalancedPartialSupportArmAt (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ),
    stressCoeff ≠ 0 →
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∃ c, stressCoeff c = 0) →
    (∀ probe : Fin rank → ℝ,
      (∀ c, 0 < stressCoeff c → design.atom c ⬝ᵥ probe = 0) → probe = 0) →
    (∀ probe : Fin rank → ℝ,
      (∀ c, stressCoeff c < 0 → design.atom c ⬝ᵥ probe = 0) → probe = 0) →
    IsTie design → HasParallelPair design

/-- Arm (ii) splits on full support. -/
theorem balancedArmAt_of_split (hfullArm : BalancedFullSupportArmAt size rank)
    (hpartialArm : BalancedPartialSupportArmAt size rank) : BalancedArmAt size rank := by
  intro design stressCoeff hstressNe hstress hposSpans hnegSpans htie
  by_cases hfullSupport : ∀ c, stressCoeff c ≠ 0
  · exact hfullArm design stressCoeff hstress hfullSupport htie
  · push Not at hfullSupport
    exact hpartialArm design stressCoeff hstressNe hstress hfullSupport hposSpans hnegSpans htie

/-- **FAN-OUT ONE: SUB-ARM (ii-b) IS EMPTY EXACTLY WHEN THE CELL IS NARROW.**
Two spanning sides carry at least `rank` labels each, thus in a cell of at most
`2 * rank` labels they fill it and no label is left unsupported. At the
threshold cell that condition is `rank <= 3`
(`Gtz.thresholdSize_le_two_mul_iff`), thus this sub-arm is vacuous at rank three
and INHABITABLE at rank four and up, where the registry's rank-three capstones
have nothing to say. -/
theorem balancedPartialSupportArmAt_of_size_le (hsize : size ≤ 2 * rank) :
    BalancedPartialSupportArmAt size rank := by
  intro design stressCoeff _hstressNe _hstress hzero hposSpans hnegSpans _htie
  exfalso
  obtain ⟨zeroLabel, hzeroLabel⟩ := hzero
  exact stress_fullSupport_of_sides_of_size_le
    (rank_le_posSideCard_of_spans design hposSpans)
    (rank_le_negSideCard_of_spans design hnegSpans) hsize zeroLabel hzeroLabel

/-- Sub-arm (ii-b) is free at the rank-three deciding cell. -/
theorem balancedPartialSupportArm_sixThree : BalancedPartialSupportArmAt 6 3 :=
  balancedPartialSupportArmAt_of_size_le (by norm_num)

/-- **THE MASS-GAP FIRING PRODUCES A STRICTLY DOMINATING POSITIVE SIDE, AT EVERY
RANK.**  Both hypotheses of the rank-uniform `Gtz.posDef_gap_of_stressMassGap`
come from this module: the two-frame equality
(`Gtz.posSideSum_eq_negSideSum`) and the positive definite middle matrix
(`Gtz.posDef_posSideSum_of_spans`, fed by the shipped `Gtz.pos_side_spans`). -/
theorem posDef_gap_posSide_of_massGap (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0)
    (hgap : HasStressMassGap design stressCoeff) :
    (subsetSum design (Finset.univ.filter fun c => 0 < stressCoeff c) - 1).PosDef := by
  obtain ⟨freeFloor, boundCeiling, hfree, hbound, hstrict⟩ := hgap
  refine posDef_gap_of_stressMassGap design (posSideSum_eq_negSideSum design.atom hstress)
    (posDef_posSideSum_of_spans design.atom ?_) hfull hfree hbound hstrict
  exact pos_side_spans design.atom
    (fun probe hprobe => weightedDesign_atoms_span design hprobe) hstress hfull

/-- **FAN-OUT TWO, THE DEEPEST ONE.**  A tie forbids strict domination at card
`rank` ONLY. The mass-gap firing hands back the whole POSITIVE SIDE, whose card
lies in the window `[rank, size - rank]`. At the rank-three deciding cell that
window is the single point `rank`, thus the firing contradicts the tie outright.
At rank four and up the window is a genuine interval
(`Gtz.lt_thresholdSize_sub_rank`), the returned set is too big, and the firing
yields NOTHING.

Shrinking the returned set is not available: a strictly dominating set of more
than `rank` atoms need not contain a strictly dominating card-`rank` subset --
four unit vectors forming a tight frame in three dimensions have
`subsetSum = (4/3) * 1` while every triple among them drops to smallest
eigenvalue `1/3`. So this Prop is not a packaging step. It is the residual. -/
def MassGapSideIsRankSized (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ),
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ c, stressCoeff c ≠ 0) →
    HasStressMassGap design stressCoeff →
    ∃ dominating : Finset (Fin size), dominating.card = rank
      ∧ (subsetSum design dominating - 1).PosDef

/-- Whenever the positive side is rank-sized the residual is discharged. -/
theorem massGapSideIsRankSized_of_posSideCard (size rank : ℕ)
    (hcard : ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ),
      (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → (∀ c, stressCoeff c ≠ 0) →
        (Finset.univ.filter fun c => 0 < stressCoeff c).card = rank) :
    MassGapSideIsRankSized size rank :=
  fun design stressCoeff hstress hfull hgap =>
    ⟨Finset.univ.filter fun c => 0 < stressCoeff c, hcard design stressCoeff hstress hfull,
      posDef_gap_posSide_of_massGap design hstress hfull hgap⟩

/-- **THE RANK-THREE INSTANCE IS A THEOREM.**  The shipped `(3,3)` split makes
the positive side a triple, thus rank-sized, thus the firing closes. -/
theorem massGapSideIsRankSized_sixThree : MassGapSideIsRankSized 6 3 :=
  massGapSideIsRankSized_of_posSideCard 6 3 fun design _stressCoeff hstress hfull =>
    (sixThree_fullSupport_stress_splits_three_three design.atom
      (fun _probe hprobe => weightedDesign_atoms_span design hprobe) hstress hfull).1

/-- **SUB-ARM (ii-a) FROM THE TWO NAMED RESIDUALS.**  All three unconditional
firings of the rank-three balanced capstone lift: the mass gap in each
orientation through `Gtz.MassGapSideIsRankSized`, and the free-mass budget at a
card-`rank` subset through the already rank-uniform
`Gtz.posDef_gap_of_freeMassBudget`. What survives is exactly
`Gtz.BalancedStratumSelectionAtRank`, the verbatim lift of the rank-three
selection. -/
theorem balancedFullSupportArmAt_of_selection
    (hmassGap : MassGapSideIsRankSized size rank)
    (hselection : BalancedStratumSelectionAtRank size rank) :
    BalancedFullSupportArmAt size rank := by
  classical
  intro design stressCoeff hstress hfull htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  have hnostrict := htie.2
  by_cases hgapPos : HasStressMassGap design stressCoeff
  · obtain ⟨dominating, hcard, hposDef⟩ := hmassGap design stressCoeff hstress hfull hgapPos
    exact hnostrict dominating hcard hposDef
  by_cases hgapNeg : HasStressMassGap design (-stressCoeff)
  · obtain ⟨dominating, hcard, hposDef⟩ := hmassGap design (-stressCoeff)
      (stress_of_neg_stress hstress)
      (fun c => by simp only [Pi.neg_apply]; exact neg_ne_zero.mpr (hfull c)) hgapNeg
    exact hnostrict dominating hcard hposDef
  by_cases hbudget : ∀ selected : Finset (Fin size), selected.card = rank →
      ¬ HasFreeMassBudget design selected
  · obtain ⟨dominating, hcard, hposDef⟩ := hselection design stressCoeff hstress hfull
      hprimitive hgapPos hgapNeg hbudget
    exact hnostrict dominating hcard hposDef
  · push Not at hbudget
    obtain ⟨selected, hcard, hbudgetFires⟩ := hbudget
    exact hnostrict selected hcard
      (posDef_gap_of_freeMassBudget design selected hbudgetFires.1 hbudgetFires.2)

/-- **ARM (ii) FROM ITS THREE RESIDUALS.**  This is the whole balanced arm at
general rank, taken apart. -/
theorem balancedArmAt_of_residuals
    (hmassGap : MassGapSideIsRankSized size rank)
    (hselection : BalancedStratumSelectionAtRank size rank)
    (hpartialArm : BalancedPartialSupportArmAt size rank) :
    BalancedArmAt size rank :=
  balancedArmAt_of_split (balancedFullSupportArmAt_of_selection hmassGap hselection)
    hpartialArm

/-- **THE CHAIN IS THE RIGHT ONE: ITS RANK-THREE INSTANCE IS CLOSED.**  Arm (ii)
at the rank-three deciding cell comes out of the general-rank residuals with no
appeal to `Gtz.BalancedStratumCapstone`: the mass-gap firing is the theorem
`Gtz.massGapSideIsRankSized_sixThree`, the partial-support sub-arm is empty by
`Gtz.balancedPartialSupportArm_sixThree`, and the selection is the closed
`Gtz.balancedStratumSelection_six_holds`. -/
theorem thresholdBalancedArm_three_of_residuals : ThresholdBalancedArm 3 :=
  balancedArmAt_of_residuals massGapSideIsRankSized_sixThree
    ((balancedStratumSelectionAtRank_three 6).mpr balancedStratumSelection_six_holds)
    balancedPartialSupportArm_sixThree

/-- **THE THRESHOLD OBLIGATION, FULLY UNFOLDED.**  Arm (ii) replaced by its
three residuals. This is the exact list a successor must close at rank four and
up, on top of arm (i) and arm (iii). -/
theorem thresholdCellHingeRankFourAndUp_of_residuals
    (hfreeArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdStressFreeArm rank)
    (hmassGap : ∀ rank : ℕ, 4 ≤ rank → MassGapSideIsRankSized (thresholdSize rank) rank)
    (hselection : ∀ rank : ℕ, 4 ≤ rank →
      BalancedStratumSelectionAtRank (thresholdSize rank) rank)
    (hpartialArm : ∀ rank : ℕ, 4 ≤ rank →
      BalancedPartialSupportArmAt (thresholdSize rank) rank)
    (hdegenerateArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdDegenerateArm rank) :
    ∀ rank : ℕ, 4 ≤ rank →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  refine thresholdCellHingeRankFourAndUp_of_arms hfreeArm (fun rank hrank => ?_) hdegenerateArm
  exact balancedArmAt_of_residuals (hmassGap rank hrank) (hselection rank hrank)
    (hpartialArm rank hrank)

/-! ### The anatomy of the degenerate arm

Arm (iii) is sorted at rank three by the number of POLES, the atoms that miss
the probe hyperplane. The tree bounds that number by TWO and the two-pole cell
is `Gtz.TwoPoleStratumSelection`. The bound is what does not lift. -/

/-- The POLES of a design against a probe: the labels whose atom misses the
probe hyperplane. -/
noncomputable def offHyperplane (design : WeightedDesign size rank)
    (probe : Fin rank → ℝ) :
    Finset (Fin size) :=
  Finset.univ.filter fun c => design.atom c ⬝ᵥ probe ≠ 0

/-- **THERE IS ALWAYS AT LEAST ONE POLE.**  A design whose every atom met the
hyperplane would fail Parseval along the probe. -/
theorem nonempty_offHyperplane (design : WeightedDesign size rank) {probe : Fin rank → ℝ}
    (hprobeNe : probe ≠ 0) : (offHyperplane design probe).Nonempty := by
  classical
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  refine hprobeNe (weightedDesign_atoms_span design fun c => ?_)
  by_contra hne
  have hmem : c ∈ offHyperplane design probe :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c, hne⟩
  rw [hempty] at hmem
  simp at hmem

/-- Every pole is unsupported, because every supported atom meets the
hyperplane. -/
theorem offHyperplane_subset_unsupported (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ} {probe : Fin rank → ℝ}
    (hsupport : ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0) :
    offHyperplane design probe ⊆ Finset.univ.filter fun c => stressCoeff c = 0 := by
  classical
  intro c hc
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ c, ?_⟩
  by_contra hne
  exact (Finset.mem_filter.mp hc).2 (hsupport c hne)

/-- Arm (iii) at or below a pole count. At rank three with the count two this is
the tree's two-pole cell. -/
def DegenerateArmBelowPoleCount (size rank poleBound : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ)
      (probe : Fin rank → ℝ),
    stressCoeff ≠ 0 → probe ≠ 0 →
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0) →
    (offHyperplane design probe).card ≤ poleBound →
    IsTie design → HasParallelPair design

/-- Arm (iii) above a pole count. At rank three with the count two this is
EMPTY. -/
def DegenerateArmAbovePoleCount (size rank poleBound : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ)
      (probe : Fin rank → ℝ),
    stressCoeff ≠ 0 → probe ≠ 0 →
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0) →
    poleBound < (offHyperplane design probe).card →
    IsTie design → HasParallelPair design

/-- Arm (iii) splits at any pole count. -/
theorem degenerateArmAt_of_poleSplit (poleBound : ℕ)
    (hbelowArm : DegenerateArmBelowPoleCount size rank poleBound)
    (haboveArm : DegenerateArmAbovePoleCount size rank poleBound) :
    DegenerateArmAt size rank := by
  intro design stressCoeff probe hstressNe hprobeNe hstress hsupport htie
  rcases Nat.lt_or_ge poleBound (offHyperplane design probe).card with hlt | hle
  · exact haboveArm design stressCoeff probe hstressNe hprobeNe hstress hsupport hlt htie
  · exact hbelowArm design stressCoeff probe hstressNe hprobeNe hstress hsupport hle htie

/-- **FAN-OUT THREE: THE POLE BOUND.**  At the rank-three deciding cell a
primitive coplanar-support configuration has at most TWO poles
(`Gtz.sixThree_offPlaneCard_le_two_of_coplanarStress`), thus the above-two half
of arm (iii) is EMPTY and the whole arm is the two-pole cell. The tree carries
no pole bound at any rank above three, and there is no counting argument to
supply one: the poles are the unsupported labels
(`Gtz.offHyperplane_subset_unsupported`), and at the threshold cell of rank
four and up a stress may miss many labels. -/
theorem degenerateArmAbovePoleCount_sixThree : DegenerateArmAbovePoleCount 6 3 2 := by
  intro design stressCoeff probe hstressNe hprobeNe hstress hsupport hcount htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  have hbound := sixThree_offPlaneCard_le_two_of_coplanarStress design hstressNe hprobeNe
    hstress hsupport hprimitive
  simp only [offHyperplane] at hcount
  omega

/-- The below-two half at rank three is the tree's closed two-pole capstone. -/
theorem degenerateArmBelowPoleCount_sixThree (hselection : TwoPoleStratumSelection 6) :
    DegenerateArmBelowPoleCount 6 3 2 :=
  fun design _stressCoeff _probe hstressNe hprobeNe hstress hsupport _hcount htie =>
    sixThree_hasParallelPair_of_isTie_of_coplanarStress hselection design htie
      hstressNe hprobeNe hstress hsupport

/-- **ARM (iii) AT RANK THREE, FROM THE POLE SPLIT.**  A second route to the
closed rank-three degenerate arm, this time through the general-rank pole
anatomy. It certifies that the split by pole count is the right general-rank
decomposition. -/
theorem thresholdDegenerateArm_three_of_poleSplit (hselection : TwoPoleStratumSelection 6) :
    ThresholdDegenerateArm 3 :=
  degenerateArmAt_of_poleSplit 2 (degenerateArmBelowPoleCount_sixThree hselection)
    degenerateArmAbovePoleCount_sixThree

/-! ### The subspace restriction at general rank, and the induction axis

`Gtz.inPlaneRestriction` restricts a rank-three design to a plane and lands at
rank two, where `Gtz.gtz_rank_two` is a THEOREM. That is why the rank-three
degenerate arm closes. At rank `k` the same restriction lands at rank `k - 1`,
which is the conjecture one rank down.

The registry hinge obligations supply `Gtz.GtzWeighted (size - 1) rank` -- one
SIZE down at the SAME rank. But the general-rank ladder
(`Skeleton.GeneralRank.closesSharpWindow_ofClosures`) runs inside a RANK
induction and carries `Gtz.GtzWeightedAll (rank - 1)` in scope, so a hinge arm
that consumes the previous RANK still drives the same ladder and is a strictly
weaker obligation. This section builds the restriction at general rank and the
producer that consumes it. -/

/-- The quadratic form of a subset sum, read atom by atom. -/
theorem subsetSum_form (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (probe : Fin rank → ℝ) :
    probe ⬝ᵥ (subsetSum design selected *ᵥ probe)
      = ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2 := by
  rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun c _ => atom_form_eq_sq _ _

/-- **THE SUBSPACE RESTRICTION AT GENERAL RANK.**  Reading every atom against an
orthonormal frame of any dimension gives a weighted design of THAT dimension,
with the SAME weights: the Parseval entries are exactly the frame pairings.
This is `Gtz.inPlaneRestriction` freed of rank three and of the plane, and it is
what carries a hinge arm down the RANK axis. -/
noncomputable def subspaceRestriction {frameDim : ℕ} (design : WeightedDesign size rank)
    (frame : Fin frameDim → Fin rank → ℝ)
    (horthonormal : ∀ i j, frame i ⬝ᵥ frame j = if i = j then 1 else 0) :
    WeightedDesign size frameDim where
  atom := fun label i => design.atom label ⬝ᵥ frame i
  weight := design.weight
  weight_pos := design.weight_pos
  weight_sum_one := design.weight_sum_one
  isParseval := by
    ext rowIndex colIndex
    rw [Matrix.sum_apply, Matrix.one_apply, ← horthonormal rowIndex colIndex,
      dotProduct_eq_sum_weight_mul_pair design (frame rowIndex) (frame colIndex)]
    exact Finset.sum_congr rfl fun c _ => by
      simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]

/-- **THE RANK-DOWN DISPATCH.**  With the conjecture at the frame's dimension,
every design carries a subset of that many atoms whose readings cover the whole
subspace. At `frameDim = rank - 1` this is exactly what the degenerate branch
wants, and the ladder has it in scope. -/
theorem exists_subspace_dominating_subset {frameDim : ℕ}
    (hpredecessor : GtzWeightedAll frameDim) (design : WeightedDesign size rank)
    (frame : Fin frameDim → Fin rank → ℝ)
    (horthonormal : ∀ i j, frame i ⬝ᵥ frame j = if i = j then 1 else 0) :
    ∃ selected : Finset (Fin size), selected.card = frameDim
      ∧ ∀ coeff : Fin frameDim → ℝ,
        coeff ⬝ᵥ coeff
          ≤ ∑ c ∈ selected, (design.atom c ⬝ᵥ (∑ i, coeff i • frame i)) ^ 2 := by
  classical
  obtain ⟨selected, hcard, hdominates⟩ :=
    hpredecessor size (subspaceRestriction design frame horthonormal)
  refine ⟨selected, hcard, fun coeff => ?_⟩
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 coeff
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, subsetSum_form,
    Matrix.one_mulVec] at hform
  have hread : ∀ c : Fin size,
      (subspaceRestriction design frame horthonormal).atom c ⬝ᵥ coeff
        = design.atom c ⬝ᵥ (∑ i, coeff i • frame i) := by
    intro c
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotProduct_smul, smul_eq_mul, mul_comm]
    rfl
  rw [Finset.sum_congr rfl fun c _ => congrArg (· ^ 2) (hread c)] at hform
  linarith

/-- **THE SCHUR PRODUCER AT GENERAL RANK.**  A subset that OVERSHOOTS along a
unit normal and COVERS the normal's hyperplane strictly dominates. The shipped
`Gtz.posDef_of_normalSurplus_planeCover` states this at rank three only; the
completed square that proves it never reads the dimension.

Decompose a probe as `alpha * unitNormal + orthogonal`. The gap form becomes
`alpha ^ 2 * (surplus - 1) + 2 * alpha * coupling + cover`, a quadratic in
`alpha` whose leading coefficient is the surplus and whose discriminant is the
cover condition. -/
theorem posDef_of_normalSurplus_hyperplaneCover (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (unitNormal : Fin rank → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hsurplus : 1 < ∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2)
    (hcover : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ unitNormal = 0 → probe ≠ 0 →
      (∑ c ∈ selected, (design.atom c ⬝ᵥ probe) * (design.atom c ⬝ᵥ unitNormal)) ^ 2
        < ((∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2) - 1)
          * ((∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)) :
    (subsetSum design selected - 1).PosDef := by
  classical
  have hsymm : (subsetSum design selected - 1)ᵀ = subsetSum design selected - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, transpose_subsetSum]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobeNe => ?_⟩
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, subsetSum_form, Matrix.one_mulVec]
  set axialPart : ℝ := probe ⬝ᵥ unitNormal with haxial
  set flatPart : Fin rank → ℝ := probe - axialPart • unitNormal with hflat
  have hflatNormal : flatPart ⬝ᵥ unitNormal = 0 := by
    rw [hflat, sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit, haxial]
    ring
  have hdecompose : probe = flatPart + axialPart • unitNormal := by
    rw [hflat]; abel
  have hread : ∀ c : Fin size, design.atom c ⬝ᵥ probe
      = (design.atom c ⬝ᵥ flatPart) + axialPart * (design.atom c ⬝ᵥ unitNormal) := by
    intro c
    rw [hdecompose, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hlength : probe ⬝ᵥ probe = flatPart ⬝ᵥ flatPart + axialPart ^ 2 := by
    rw [hdecompose, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct,
      dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, hunit, hflatNormal, dotProduct_comm unitNormal flatPart,
      hflatNormal]
    ring
  have hexpand : ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2
      = (∑ c ∈ selected, (design.atom c ⬝ᵥ flatPart) ^ 2)
        + 2 * axialPart
            * (∑ c ∈ selected,
              (design.atom c ⬝ᵥ flatPart) * (design.atom c ⬝ᵥ unitNormal))
        + axialPart ^ 2 * ∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by rw [hread c]; ring
  rw [hexpand, hlength]
  by_cases hflatZero : flatPart = 0
  · have haxialNe : axialPart ≠ 0 := by
      intro hzero
      refine hprobeNe ?_
      rw [hdecompose, hflatZero, hzero, zero_smul, add_zero]
    have hflatDot : flatPart ⬝ᵥ flatPart = 0 := by rw [hflatZero]; simp
    have hzeroSquares : ∑ c ∈ selected, (design.atom c ⬝ᵥ flatPart) ^ 2 = 0 :=
      Finset.sum_eq_zero fun c _ => by rw [hflatZero]; simp
    have hzeroCross : ∑ c ∈ selected,
        (design.atom c ⬝ᵥ flatPart) * (design.atom c ⬝ᵥ unitNormal) = 0 :=
      Finset.sum_eq_zero fun c _ => by rw [hflatZero]; simp
    have haxialSq : 0 < axialPart ^ 2 := by positivity
    rw [hzeroSquares, hzeroCross, hflatDot]
    nlinarith [hsurplus, haxialSq]
  · have hcoverFires := hcover flatPart hflatNormal hflatZero
    nlinarith [hcoverFires, hsurplus,
      sq_nonneg (((∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2) - 1) * axialPart
        + ∑ c ∈ selected,
            (design.atom c ⬝ᵥ flatPart) * (design.atom c ⬝ᵥ unitNormal))]

/-- **THE GENERAL-RANK DEGENERATE RESIDUAL.**  On the degenerate branch, produce
a card-`rank` subset that overshoots along the probe's unit normal and covers
its hyperplane. `Gtz.posDef_of_normalSurplus_hyperplaneCover` then contradicts
the tie outright. At rank three this is what the two-pole capstone does, with
the pole bound doing the selecting. -/
def DegenerateHyperplaneProducer (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ)
      (unitNormal : Fin rank → ℝ),
    stressCoeff ≠ 0 → unitNormal ⬝ᵥ unitNormal = 1 →
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ unitNormal = 0) →
    ∃ selected : Finset (Fin size), selected.card = rank
      ∧ 1 < ∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2
      ∧ ∀ probe : Fin rank → ℝ, probe ⬝ᵥ unitNormal = 0 → probe ≠ 0 →
        (∑ c ∈ selected, (design.atom c ⬝ᵥ probe) * (design.atom c ⬝ᵥ unitNormal)) ^ 2
          < ((∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2) - 1)
            * ((∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)

/-- Normalizing a probe changes neither the hyperplane nor the branch data. -/
theorem unit_of_ne_zero (probe : Fin rank → ℝ) (hprobeNe : probe ≠ 0) :
    ((Real.sqrt (probe ⬝ᵥ probe))⁻¹ • probe) ⬝ᵥ ((Real.sqrt (probe ⬝ᵥ probe))⁻¹ • probe)
      = 1 := by
  have hpos : 0 < probe ⬝ᵥ probe := selfDotProduct_pos hprobeNe
  have hsq : Real.sqrt (probe ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe :=
    Real.sq_sqrt hpos.le
  have hsqrtPos : 0 < Real.sqrt (probe ⬝ᵥ probe) := Real.sqrt_pos.mpr hpos
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp
  nlinarith [hsq, hsqrtPos]

/-- **ARM (iii) FROM THE HYPERPLANE PRODUCER.**  The producer's subset
contradicts the tie, thus the arm holds vacuously on that branch. -/
theorem degenerateArmAt_of_hyperplaneProducer
    (hproducer : DegenerateHyperplaneProducer size rank) : DegenerateArmAt size rank := by
  intro design stressCoeff probe hstressNe hprobeNe hstress hsupport htie
  exfalso
  have hpos : 0 < probe ⬝ᵥ probe := selfDotProduct_pos hprobeNe
  have hsqrtPos : 0 < Real.sqrt (probe ⬝ᵥ probe) := Real.sqrt_pos.mpr hpos
  have hscaled : ∀ c, stressCoeff c ≠ 0 →
      design.atom c ⬝ᵥ ((Real.sqrt (probe ⬝ᵥ probe))⁻¹ • probe) = 0 := by
    intro c hc
    rw [dotProduct_smul, smul_eq_mul, hsupport c hc, mul_zero]
  obtain ⟨selected, hcard, hsurplus, hcover⟩ := hproducer design stressCoeff _ hstressNe
    (unit_of_ne_zero probe hprobeNe) hstress hscaled
  exact htie.2 selected hcard
    (posDef_of_normalSurplus_hyperplaneCover design selected _
      (unit_of_ne_zero probe hprobeNe) hsurplus hcover)

/-- An orthonormal frame of the hyperplane orthogonal to a unit normal. This is
Gram-Schmidt and nothing else, but it is named rather than assumed silently, so
the composition below states every input it takes. -/
def HyperplaneFrameExists (rank : ℕ) : Prop :=
  ∀ unitNormal : Fin rank → ℝ, unitNormal ⬝ᵥ unitNormal = 1 →
    ∃ frame : Fin (rank - 1) → Fin rank → ℝ,
      (∀ i j, frame i ⬝ᵥ frame j = if i = j then 1 else 0)
        ∧ ∀ i, frame i ⬝ᵥ unitNormal = 0

/-- **THE REAL CONTENT OF THE DEGENERATE ARM AT GENERAL RANK.**  The rank-down
dispatch hands back a card-`rank - 1` subset that covers the hyperplane WEAKLY.
What is missing is one POLE and the upgrade from a weak cover to the strict
Schur pair: enough overshoot along the normal, and a strict cover inside the
hyperplane. At rank three the pole bound does the selecting and the two-pole
capstone closes it. -/
def DegeneratePoleAugmentation (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (unitNormal : Fin rank → ℝ)
      (frame : Fin (rank - 1) → Fin rank → ℝ) (flatSubset : Finset (Fin size)),
    unitNormal ⬝ᵥ unitNormal = 1 →
    (∀ i j, frame i ⬝ᵥ frame j = if i = j then 1 else 0) →
    (∀ i, frame i ⬝ᵥ unitNormal = 0) →
    flatSubset.card = rank - 1 →
    (∀ coeff : Fin (rank - 1) → ℝ, coeff ⬝ᵥ coeff
      ≤ ∑ c ∈ flatSubset, (design.atom c ⬝ᵥ (∑ i, coeff i • frame i)) ^ 2) →
    ∃ selected : Finset (Fin size), selected.card = rank
      ∧ 1 < ∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2
      ∧ ∀ probe : Fin rank → ℝ, probe ⬝ᵥ unitNormal = 0 → probe ≠ 0 →
        (∑ c ∈ selected, (design.atom c ⬝ᵥ probe) * (design.atom c ⬝ᵥ unitNormal)) ^ 2
          < ((∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2) - 1)
            * ((∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)

/-- **THE RANK-DOWN COMPOSITION.**  With the conjecture one RANK down, the
hyperplane cover is free and the degenerate producer needs only the pole
augmentation. -/
theorem degenerateHyperplaneProducer_of_augmentation
    (hpredecessor : GtzWeightedAll (rank - 1)) (hframe : HyperplaneFrameExists rank)
    (haugment : DegeneratePoleAugmentation size rank) :
    DegenerateHyperplaneProducer size rank := by
  intro design stressCoeff unitNormal _hstressNe hunit _hstress _hsupport
  obtain ⟨frame, horthonormal, hperpendicular⟩ := hframe unitNormal hunit
  obtain ⟨flatSubset, hcard, hcover⟩ :=
    exists_subspace_dominating_subset hpredecessor design frame horthonormal
  exact haugment design unitNormal frame flatSubset hunit horthonormal hperpendicular
    hcard hcover

/-- **ARM (iii) FROM THE PREVIOUS RANK.**  The general-rank degenerate arm, with
the induction hypothesis of the ladder spent. -/
theorem degenerateArmAt_of_predecessorRank
    (hpredecessor : GtzWeightedAll (rank - 1)) (hframe : HyperplaneFrameExists rank)
    (haugment : DegeneratePoleAugmentation size rank) : DegenerateArmAt size rank :=
  degenerateArmAt_of_hyperplaneProducer
    (degenerateHyperplaneProducer_of_augmentation hpredecessor hframe haugment)

/-- **THE THRESHOLD OBLIGATION UNDER THE LADDER'S OWN INDUCTION HYPOTHESIS.**
`Skeleton.GeneralRank.closesSharpWindow_ofClosures` carries
`Gtz.GtzWeightedAll (rank - 1)` in scope while it consumes the hinge, thus a
hinge arm may spend it and the ladder is unchanged. Spending it replaces the
whole degenerate arm by Gram-Schmidt plus the pole augmentation. This is the
smallest residual list this map reaches:

- `ThresholdStressFreeArm` -- the basis arm, the rank-three frontier one rank up
- `MassGapSideIsRankSized` -- the positive side is too big at rank four and up
- `BalancedStratumSelectionAtRank` -- the verbatim lift of the closed rank-three
  selection
- `BalancedPartialSupportArmAt` -- empty at rank three, new at rank four
- `HyperplaneFrameExists` -- Gram-Schmidt
- `DegeneratePoleAugmentation` -- one pole and the weak-to-strict cover. -/
theorem thresholdCellHingeRankFourAndUp_of_residuals_withPredecessorRank
    (hfreeArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdStressFreeArm rank)
    (hmassGap : ∀ rank : ℕ, 4 ≤ rank → MassGapSideIsRankSized (thresholdSize rank) rank)
    (hselection : ∀ rank : ℕ, 4 ≤ rank →
      BalancedStratumSelectionAtRank (thresholdSize rank) rank)
    (hpartialArm : ∀ rank : ℕ, 4 ≤ rank →
      BalancedPartialSupportArmAt (thresholdSize rank) rank)
    (hframe : ∀ rank : ℕ, 4 ≤ rank → HyperplaneFrameExists rank)
    (haugment : ∀ rank : ℕ, 4 ≤ rank →
      DegeneratePoleAugmentation (thresholdSize rank) rank) :
    ∀ rank : ℕ, 4 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
        IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor design htie
  refine thresholdCellHinge_of_arms rank (hfreeArm rank hrank) ?_ ?_ design htie
  · exact balancedArmAt_of_residuals (hmassGap rank hrank) (hselection rank hrank)
      (hpartialArm rank hrank)
  · exact degenerateArmAt_of_predecessorRank hpredecessor (hframe rank hrank)
      (haugment rank hrank)

/-! ## Part 10: what a tie supplies at every rank

Two identities the rank-three arms consume, both already rank-uniform once
stated. They belong to the map because they are what a general-rank prover
starts from on ANY of the three arms. -/

/-- The two sign sides never overtake the cell. -/
theorem sideCards_add_le (stressCoeff : Fin n → ℝ) :
    (Finset.univ.filter fun c => 0 < stressCoeff c).card
      + (Finset.univ.filter fun c => stressCoeff c < 0).card ≤ n := by
  classical
  have hdisjoint : Disjoint (Finset.univ.filter fun c => 0 < stressCoeff c)
      (Finset.univ.filter fun c => stressCoeff c < 0) := by
    rw [Finset.disjoint_left]
    intro c hposMem hnegMem
    exact absurd (Finset.mem_filter.mp hnegMem).2 (asymm (Finset.mem_filter.mp hposMem).2)
  have hcard := Finset.card_le_univ ((Finset.univ.filter fun c => 0 < stressCoeff c)
    ∪ (Finset.univ.filter fun c => stressCoeff c < 0))
  rw [Finset.card_union_of_disjoint hdisjoint, Fintype.card_fin] at hcard
  exact hcard

/-- **THE ADMISSIBLE SIGN-SPLIT WINDOW AT THE THRESHOLD CELL.**  Both sides carry
at least `rank` labels and together they fit in the cell, thus the positive
side's count lies in `[rank, thresholdSize rank - rank]`. -/
theorem thresholdCell_split_window {stressCoeff : Fin (thresholdSize rank) → ℝ}
    (hposCard : rank ≤ (Finset.univ.filter fun c => 0 < stressCoeff c).card)
    (hnegCard : rank ≤ (Finset.univ.filter fun c => stressCoeff c < 0).card) :
    rank ≤ (Finset.univ.filter fun c => 0 < stressCoeff c).card
      ∧ (Finset.univ.filter fun c => 0 < stressCoeff c).card
          ≤ thresholdSize rank - rank := by
  refine ⟨hposCard, ?_⟩
  have hsum := sideCards_add_le (n := thresholdSize rank) stressCoeff
  omega

/-- **THE EXACT FAN-OUT COUNT.**  The window holds `rank * (rank - 3) / 2 + 1`
admissible splits: ONE at rank three, three at rank four, six at rank five, ten
at rank six. The rank-three branch capstones read the single admissible split,
thus at rank four and up they have no statement to specialize to. -/
theorem card_admissibleSplits (rank : ℕ) (hrank : 3 ≤ rank) :
    (Finset.Icc rank (thresholdSize rank - rank)).card = rank * (rank - 3) / 2 + 1 := by
  have hwindow := two_mul_thresholdSplitWindow rank hrank
  have hfloor := two_mul_le_thresholdSize rank hrank
  rw [Nat.card_Icc]
  omega

theorem card_admissibleSplits_three : (Finset.Icc 3 (thresholdSize 3 - 3)).card = 1 := by
  rw [card_admissibleSplits 3 (by norm_num)]

theorem card_admissibleSplits_four : (Finset.Icc 4 (thresholdSize 4 - 4)).card = 3 := by
  rw [card_admissibleSplits 4 (by norm_num)]

/-- **AT RANK FOUR AND UP THE WINDOW HOLDS AT LEAST THREE SPLITS.**  So no single
sign pattern can carry the balanced branch. -/
theorem three_le_card_admissibleSplits (rank : ℕ) (hrank : 4 ≤ rank) :
    3 ≤ (Finset.Icc rank (thresholdSize rank - rank)).card := by
  rw [card_admissibleSplits rank (by omega)]
  have hbig : 4 * 1 ≤ rank * (rank - 3) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- **THE TIGHT-DIRECTION MASS BALANCE, RANK-UNIFORM.**  Along a direction where
the gap of a subset vanishes, the subset's FREE mass and the complement's BOUND
mass agree exactly. This is Parseval read against the tight direction, and it is
the one quantitative identity every arm of the hinge starts from. The shipped
`Gtz.subsetSum_sub_one_eq_freeMass_sub_boundMass` supplies the decomposition and
is already rank-uniform. -/
theorem tightDirection_mass_balance (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) {tightDir : Fin rank → ℝ}
    (htight : tightDir ⬝ᵥ ((subsetSum design selected - 1) *ᵥ tightDir) = 0) :
    ∑ c ∈ selected, (1 - design.weight c) * (design.atom c ⬝ᵥ tightDir) ^ 2
      = ∑ c ∈ selectedᶜ, design.weight c * (design.atom c ⬝ᵥ tightDir) ^ 2 := by
  classical
  rw [subsetSum_sub_one_eq_freeMass_sub_boundMass, Matrix.sub_mulVec, dotProduct_sub,
    weighted_atomForm_eq_on, weighted_atomForm_eq_on] at htight
  linarith

/-- **EVERY TIE CARRIES A BALANCED TIGHT DIRECTION, AT EVERY RANK.**  Composition
of the shipped KKT extraction `Gtz.isTie_yields_tightDirection` with the balance
identity. Both are rank-uniform, thus the whole quantitative entry point of the
hinge lifts with no work. -/
theorem exists_tightDirection_mass_balance (design : WeightedDesign size rank)
    (htie : IsTie design) :
    ∃ (selected : Finset (Fin size)) (tightDir : Fin rank → ℝ),
      selected.card = rank ∧ Dominates design selected ∧ tightDir ≠ 0
        ∧ ∑ c ∈ selected, (1 - design.weight c) * (design.atom c ⬝ᵥ tightDir) ^ 2
          = ∑ c ∈ selectedᶜ, design.weight c * (design.atom c ⬝ᵥ tightDir) ^ 2 := by
  obtain ⟨selected, tightDir, hcard, hdominates, hne, htight⟩ :=
    isTie_yields_tightDirection htie
  exact ⟨selected, tightDir, hcard, hdominates, hne,
    tightDirection_mass_balance design selected htight⟩

/-- **THE DEGENERATE BRANCH HAS AT LEAST ONE POLE.**  Every supported atom lies
in the probe hyperplane, thus if every unsupported atom lay there too the whole
design would lie there and Parseval would fail. At rank three the tree bounds
the pole count above by TWO, which is what makes
`Gtz.TwoPoleStratumSelection` the branch's residual. No such upper bound exists
in the tree at any rank above three, and the lower bound below is all that
lifts. -/
theorem exists_offHyperplane_of_degenerate (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ} {probe : Fin rank → ℝ} (hprobeNe : probe ≠ 0)
    (hsupport : ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0) :
    ∃ c : Fin size, stressCoeff c = 0 ∧ design.atom c ⬝ᵥ probe ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  refine hprobeNe (weightedDesign_atoms_span design fun c => ?_)
  by_cases hc : stressCoeff c = 0
  · exact hnone c hc
  · exact hsupport c hc

/-! ## Part 10: the deciding cell is the only cell where the basis reading holds

Below the threshold cell there are too few atoms to span, above it a stress is
forced. Both halves are quoted from the tree, and together they say the registry
picked the right carrier. -/

/-- **ABOVE THE THRESHOLD CELL NO DESIGN IS STRESS-FREE.**  The count exceeds the
dimension of the symmetric matrices, thus `Gtz.exists_parsevalNullDirection`
fires and arm (i) is empty. -/
theorem not_stressFree_of_thresholdSize_lt (design : WeightedDesign size rank)
    (hsize : thresholdSize rank < size) :
    ¬ ∀ stressCoeff : Fin size → ℝ,
        (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → stressCoeff = 0 := by
  intro hfree
  obtain ⟨stressCoeff, hstressNe, hstress⟩ :=
    exists_parsevalNullDirection design.atom hsize
  exact hstressNe (hfree stressCoeff hstress)

/-- **THE THRESHOLD CELL IS THE LAST CELL CARRYING A STRESS-FREE DESIGN.**  So
the arm (i) reading -- the atom matrices are a BASIS -- is available exactly at
`thresholdSize rank`, and the registry's choice of carrier is forced. -/
theorem stressFree_only_at_or_below_thresholdSize (design : WeightedDesign size rank)
    (hfree : ∀ stressCoeff : Fin size → ℝ,
      (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → stressCoeff = 0) :
    size ≤ thresholdSize rank := by
  by_contra hgt
  push Not at hgt
  exact not_stressFree_of_thresholdSize_lt design hgt hfree

end Gtz
