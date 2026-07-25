/-
# The tie stratum over the FULL weight simplex, at every size

`Gtz.Ties.CorankOneTieExistence` pins the corank-one stratum: at `m = k+1` every
weight vector carries a tie (`exists_isTie_of_weights`), the section being
`simplexTieDesign`. `Gtz.Ties.SplitTetrahedronTie` and
`Gtz.Ties.SevenThreeTieLocus` push that up to `m = 6` and `m = 7`, but only along
the intra-class splits: the four tetrahedron directions keep weight `1/4` each and
only the duplicate shares move, so those families see `2` and `3` parameters.

This file removes that restriction. Given ANY surjection `classOf : Fin m → Fin (k+1)`
and ANY weight vector on `Fin m`, put on each atom the corank-one atom of its
class, evaluated at the CLASS TOTALS. Parseval survives because atoms sharing a
class share their rank-one moment, so the fibrewise sum collapses to the
corank-one Parseval identity (`splitClassDesign`). The result is an exact tie for
every weight vector (`splitClassDesign_isTie`), so:

  **for every `m ≥ k+1`, every surjection onto the classes, and every weight
  vector in the open simplex, there is a tie with exactly those weights**
  (`exists_isTie_of_weights_of_classes`).

The tie stratum is therefore a section over the whole open weight simplex at every
size, not just at corank one — an `(m-1)`-parameter family, one branch per set
partition of `Fin m` into `k+1` blocks. At `k = 3`, `m = 6` this contains the two
`U(3,4)` classes of the measured `(6,3)` locus, and at `m = 7` the three `U(3,4)`
classes of the measured `(7,3)` locus, with the graph-induced designs of
`Gtz.Design.GraphicInstance` sitting at the rational points where the class totals
are proportional to the block sizes.

PROVED here: the construction, its Parseval, and the tie. CITED: the corank-one
section and the leverage identity behind it, both from
`Gtz.Ties.CorankOneTieExistence`. MEASURED elsewhere, not claimed here: that these
plus the diamond-matroid families exhaust the rank-three tie locus.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Certificates.ResidueDissolution
import Gtz.Reduction.RankFourWindow
import Gtz.Ties.CorankOneTieExistence

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ### Class totals -/

/-- Total weight carried by one class of atoms. -/
noncomputable def classTotalWeight (classOf : Fin m → Fin (k + 1))
    (weight : Fin m → ℝ) : Fin (k + 1) → ℝ :=
  fun label => ∑ atomIndex ∈ Finset.univ.filter (fun c => classOf c = label),
    weight atomIndex

theorem classTotalWeight_pos {classOf : Fin m → Fin (k + 1)} {weight : Fin m → ℝ}
    (hsurjective : Function.Surjective classOf) (hpos : ∀ c, 0 < weight c)
    (label : Fin (k + 1)) : 0 < classTotalWeight classOf weight label := by
  obtain ⟨witness, hwitness⟩ := hsurjective label
  refine Finset.sum_pos' (fun atomIndex _ => (hpos atomIndex).le) ⟨witness, ?_, hpos witness⟩
  simp [hwitness]

theorem classTotalWeight_eq (classOf : Fin m → Fin (k + 1)) (weight : Fin m → ℝ)
    (label : Fin (k + 1)) : classTotalWeight classOf weight label
      = ∑ atomIndex ∈ Finset.univ.filter (fun c => classOf c = label), weight atomIndex :=
  rfl

theorem classTotalWeight_sum {classOf : Fin m → Fin (k + 1)} {weight : Fin m → ℝ}
    (hsum : ∑ c, weight c = 1) : ∑ label, classTotalWeight classOf weight label = 1 := by
  simp only [classTotalWeight_eq]
  rw [Finset.sum_fiberwise Finset.univ classOf weight]
  exact hsum

/-! ### The design -/

/-- **Every atom carries the corank-one atom of its class, at the class totals.**
Atoms in one class are literally equal, so the design has `k+1` directions
distributed over `m` atoms with the weights split arbitrarily inside each class. -/
noncomputable def splitClassAtom (classOf : Fin m → Fin (k + 1)) (weight : Fin m → ℝ) :
    Fin m → (Fin k → ℝ) :=
  fun atomIndex => simplexTieAtom (classTotalWeight classOf weight) (classOf atomIndex)

theorem splitClassAtom_eq_of_sameClass {classOf : Fin m → Fin (k + 1)}
    {weight : Fin m → ℝ} {first second : Fin m} (hsame : classOf first = classOf second) :
    splitClassAtom classOf weight first = splitClassAtom classOf weight second := by
  rw [splitClassAtom, splitClassAtom, hsame]

/-- The fibrewise collapse: summing the atom moments against the atom weights is the
same as summing them against the class totals, because the moment is constant on a
class. -/
theorem sum_weight_smul_splitClassAtomMatrix (classOf : Fin m → Fin (k + 1))
    (weight : Fin m → ℝ) :
    ∑ atomIndex, weight atomIndex • atomMatrix (splitClassAtom classOf weight atomIndex)
      = ∑ label, classTotalWeight classOf weight label
          • atomMatrix (simplexTieAtom (classTotalWeight classOf weight) label) := by
  rw [← Finset.sum_fiberwise Finset.univ classOf
    (fun atomIndex => weight atomIndex • atomMatrix (splitClassAtom classOf weight atomIndex))]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [classTotalWeight, Finset.sum_smul]
  refine Finset.sum_congr rfl fun atomIndex hmem => ?_
  rw [splitClassAtom, (Finset.mem_filter.mp hmem).2]

/-- **The split-class design.** Weights are arbitrary; the geometry is forced by the
class totals through the corank-one section. -/
noncomputable def splitClassDesign (classOf : Fin m → Fin (k + 1)) (weight : Fin m → ℝ)
    (hk : 1 ≤ k) (hsurjective : Function.Surjective classOf) (hpos : ∀ c, 0 < weight c)
    (hsum : ∑ c, weight c = 1) : WeightedDesign m k where
  atom := splitClassAtom classOf weight
  weight := weight
  weight_pos := hpos
  weight_sum_one := hsum
  isParseval := by
    rw [sum_weight_smul_splitClassAtomMatrix]
    exact (simplexTieDesign (classTotalWeight classOf weight) hk
      (classTotalWeight_pos hsurjective hpos) (classTotalWeight_sum hsum)).isParseval

@[simp] theorem splitClassDesign_weight (classOf : Fin m → Fin (k + 1))
    (weight : Fin m → ℝ) (hk : 1 ≤ k) (hsurjective : Function.Surjective classOf)
    (hpos : ∀ c, 0 < weight c) (hsum : ∑ c, weight c = 1) :
    (splitClassDesign classOf weight hk hsurjective hpos hsum).weight = weight := rfl

@[simp] theorem splitClassDesign_atom (classOf : Fin m → Fin (k + 1))
    (weight : Fin m → ℝ) (hk : 1 ≤ k) (hsurjective : Function.Surjective classOf)
    (hpos : ∀ c, 0 < weight c) (hsum : ∑ c, weight c = 1) (atomIndex : Fin m) :
    (splitClassDesign classOf weight hk hsurjective hpos hsum).atom atomIndex
      = simplexTieAtom (classTotalWeight classOf weight) (classOf atomIndex) := rfl

/-! ### Subset sums transfer to the corank-one design -/

/-- On a subset whose atoms lie in distinct classes, the subset sum is the corank-one
design's subset sum over the image labels. -/
theorem subsetSum_splitClassDesign_of_injOn (classOf : Fin m → Fin (k + 1))
    (weight : Fin m → ℝ) (hk : 1 ≤ k) (hsurjective : Function.Surjective classOf)
    (hpos : ∀ c, 0 < weight c) (hsum : ∑ c, weight c = 1) {C : Finset (Fin m)}
    (hinjective : Set.InjOn classOf C) :
    subsetSum (splitClassDesign classOf weight hk hsurjective hpos hsum) C
      = subsetSum (simplexTieDesign (classTotalWeight classOf weight) hk
          (classTotalWeight_pos hsurjective hpos) (classTotalWeight_sum hsum))
          (C.image classOf) := by
  rw [subsetSum, subsetSum, Finset.sum_image (fun first hfirst second hsecond hequal =>
    hinjective hfirst hsecond hequal)]
  rfl

/-! ### Every weight vector carries a tie -/

/-- **The split-class design is an exact tie, for every weight vector.**
A `k`-subset either repeats a class -- then two of its atoms are equal and it cannot
dominate at all -- or meets `k` distinct classes, in which case its gap matrix is one
of the corank-one design's, which is never positive definite. The dominating subset
is the image of the corank-one one under a section of `classOf`. -/
theorem splitClassDesign_isTie (classOf : Fin m → Fin (k + 1)) (weight : Fin m → ℝ)
    (hk : 1 ≤ k) (hsurjective : Function.Surjective classOf) (hpos : ∀ c, 0 < weight c)
    (hsum : ∑ c, weight c = 1) :
    IsTie (splitClassDesign classOf weight hk hsurjective hpos hsum) := by
  set totals := classTotalWeight classOf weight with htotals
  set reduced := simplexTieDesign totals hk (classTotalWeight_pos hsurjective hpos)
    (classTotalWeight_sum hsum) with hreduced
  obtain ⟨⟨labelSet, hlabelCard, hlabelDominates⟩, hnoStrict⟩ :=
    simplexTieDesign_isTie totals hk (classTotalWeight_pos hsurjective hpos)
      (classTotalWeight_sum hsum)
  refine ⟨⟨labelSet.image (Function.surjInv hsurjective), ?_, ?_⟩, ?_⟩
  · rw [Finset.card_image_of_injective _
      (Function.injective_surjInv hsurjective), hlabelCard]
  · have hinjective : Set.InjOn classOf (labelSet.image (Function.surjInv hsurjective)) := by
      intro first hfirst second hsecond hequal
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hfirst hsecond
      obtain ⟨firstLabel, _, hfirstEq⟩ := hfirst
      obtain ⟨secondLabel, _, hsecondEq⟩ := hsecond
      rw [← hfirstEq, ← hsecondEq] at hequal ⊢
      rw [Function.surjInv_eq hsurjective, Function.surjInv_eq hsurjective] at hequal
      rw [hequal]
    rw [Dominates, subsetSum_splitClassDesign_of_injOn classOf weight hk hsurjective
      hpos hsum hinjective]
    have hcomposite : classOf ∘ Function.surjInv hsurjective = id :=
      funext fun label => Function.surjInv_eq hsurjective label
    have himage : (labelSet.image (Function.surjInv hsurjective)).image classOf
        = labelSet := by
      rw [Finset.image_image, hcomposite, Finset.image_id]
    rw [himage]
    exact hlabelDominates
  · intro C hcard hposdef
    by_cases hinjective : Set.InjOn classOf C
    · rw [subsetSum_splitClassDesign_of_injOn classOf weight hk hsurjective hpos hsum
        hinjective] at hposdef
      exact hnoStrict (C.image classOf)
        (by rw [Finset.card_image_of_injOn hinjective, hcard]) hposdef
    · obtain ⟨first, hfirst, second, hsecond, hequal, hne⟩ :
          ∃ first ∈ C, ∃ second ∈ C, classOf first = classOf second ∧ first ≠ second := by
        by_contra hcontra
        refine hinjective fun first hfirst second hsecond hequal => ?_
        by_contra hne
        exact hcontra ⟨first, Finset.mem_coe.mp hfirst, second, Finset.mem_coe.mp hsecond,
          hequal, hne⟩
      exact not_dominates_of_repeated_atom_general _ hne hfirst hsecond hcard.le
        (splitClassAtom_eq_of_sameClass hequal) hposdef.posSemidef

/-- **The tie stratum is a section over the whole open weight simplex, at every size.**
One branch for each surjection onto the `k+1` classes; the `m-1` free weights move
freely inside it. -/
theorem exists_isTie_of_weights_of_classes (hk : 1 ≤ k)
    (classOf : Fin m → Fin (k + 1)) (hsurjective : Function.Surjective classOf)
    (weight : Fin m → ℝ) (hpos : ∀ c, 0 < weight c) (hsum : ∑ c, weight c = 1) :
    ∃ D : WeightedDesign m k, D.weight = weight ∧ IsTie D :=
  ⟨splitClassDesign classOf weight hk hsurjective hpos hsum, rfl,
    splitClassDesign_isTie classOf weight hk hsurjective hpos hsum⟩

/-! ### The rank-three sizes that carry the frontier -/

/-- Six atoms in four classes, multiplicities `(2,2,1,1)`. -/
def sixIntoFourBalanced : Fin 6 → Fin 4 := ![0, 1, 2, 3, 2, 3]

/-- Six atoms in four classes, multiplicities `(3,1,1,1)`. -/
def sixIntoFourHeavy : Fin 6 → Fin 4 := ![0, 1, 2, 3, 0, 0]

/-- Seven atoms in four classes, multiplicities `(2,2,2,1)`. -/
def sevenIntoFourBalanced : Fin 7 → Fin 4 := ![0, 1, 2, 3, 1, 2, 3]

theorem sixIntoFourBalanced_surjective : Function.Surjective sixIntoFourBalanced := by
  decide

theorem sixIntoFourHeavy_surjective : Function.Surjective sixIntoFourHeavy := by
  decide

theorem sevenIntoFourBalanced_surjective : Function.Surjective sevenIntoFourBalanced := by
  decide

/-- **Every weight vector on six atoms carries a `(6,3)` tie**, in each of the two
`U(3,4)` branches. -/
theorem exists_isTie_six_three (weight : Fin 6 → ℝ) (hpos : ∀ c, 0 < weight c)
    (hsum : ∑ c, weight c = 1) :
    (∃ D : WeightedDesign 6 3, D.weight = weight ∧ IsTie D) ∧
      (∃ D : WeightedDesign 6 3, D.weight = weight ∧ IsTie D) :=
  ⟨exists_isTie_of_weights_of_classes (by norm_num) sixIntoFourBalanced
      sixIntoFourBalanced_surjective weight hpos hsum,
    exists_isTie_of_weights_of_classes (by norm_num) sixIntoFourHeavy
      sixIntoFourHeavy_surjective weight hpos hsum⟩

/-- **Every weight vector on seven atoms carries a `(7,3)` tie.** The witness of
`Gtz.Ties.SevenThreeTieLocus` is the point of this branch where the class totals are
`(2,2,2,1)/7`; here the class totals are free as well. -/
theorem exists_isTie_seven_three (weight : Fin 7 → ℝ) (hpos : ∀ c, 0 < weight c)
    (hsum : ∑ c, weight c = 1) :
    ∃ D : WeightedDesign 7 3, D.weight = weight ∧ IsTie D :=
  exists_isTie_of_weights_of_classes (by norm_num) sevenIntoFourBalanced
    sevenIntoFourBalanced_surjective weight hpos hsum

end Gtz
