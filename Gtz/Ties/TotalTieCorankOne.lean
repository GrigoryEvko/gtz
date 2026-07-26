/-
# Total ties: non-bases are free, bases are the content — and at corank one the tie IS total

A tie (`Gtz.IsTie`) says the value `max_C λ_min(S_C)` is exactly `1`.  The
per-matroid emptiness sweep that (L4) reduces to needs to know the SHAPE of that
statement: at a tie, which `k`-subsets sit at exactly `1`?  Call the tie TOTAL
when every basis of the direction matroid does.  This file settles the two halves
of that question that are settleable without circularity.

## PROVED here

Unconditional, at every size and rank:

* `subsetSum_mulVec_eq_zero_of_commonOrthogonal` — a `k`-subset whose atoms share
  an orthogonal direction has a SINGULAR atom sum.  Combined with
  `not_dominates_of_commonOrthogonal`, the "every non-basis is singular" half of
  totality is FREE: it holds at every design, tie or not, and carries no
  information about the tie.  All the content of totality is the basis half.
* `not_dominates_of_commonOrthogonal` — such a subset never dominates.  This is
  the sweep's pruning rule: at a simple matroid the tie must be attained on a
  BASIS, because a dependent triple has rank `< k` and its gap matrix is `−1` on
  the shared orthogonal direction.
* `not_dominates_of_parallel` — the same rule in the form the hinge uses: a
  `k`-subset (`k ≥ 2`) containing two PARALLEL atoms never dominates.  The
  common orthogonal direction is produced from a vanishing determinant, so no
  rank theory is invoked: `Matrix.exists_mulVec_eq_zero_iff` on the selected-rows
  matrix, whose determinant dies because one row is a multiple of another.
  This GENERALISES the landed `Gtz.not_dominates_of_repeated_atom`
  (`Gtz.Ties.RepeatedAtomExclusion`) on three counts, and the generalisation is
  what the hinge needs: parallel rather than EQUAL atoms (a tie's parallel atoms
  are only known to have equal norms conditionally on GTZ at smaller sizes, so
  the equal-atom form cannot be applied to a hypothetical tie), every rank rather
  than rank three, and an arbitrary `k`-subset rather than a literal triple.
* `dominates_det_ne_zero` — the converse packaging: a dominating `k`-subset has
  invertible selected-rows matrix, i.e. IS a basis of the direction matroid.

At corank one (`m = k + 1`), where `Gtz.isTie_iff_forall_pivot_eq_one` supplies
the pivot characterisation:

* `corankOne_isTie_dominates` / `corankOne_isTie_exactlyTied` — **every** `k`-subset
  of a corank-one tie dominates, and (by `IsTie` itself) none dominates strictly:
  every `k`-subset sits at `λ_min = 1` exactly.  The tie is TOTAL.
* `corankOne_isTie_not_commonOrthogonal`, `corankOne_isTie_det_ne_zero` — hence
  every `k`-subset is a basis: the direction matroid of a corank-one tie is the
  UNIFORM matroid `U(k, k+1)`, with no dependent `k`-subsets at all.
* `corankOne_isTie_not_parallel` (`k ≥ 2`) — hence no two atoms are parallel: a
  corank-one tie is SIMPLE (primitive).
* At `(4,3)`: `tieAtFourThree_isTotal`, `tieAtFourThree_isUniformMatroid`,
  `tieAtFourThree_isPrimitive`.  This is the `m = 4` rung of the per-matroid
  sweep, closed unconditionally: of the two simple rank-3 matroids on 4 points
  only `U(3,4)` carries a tie, and the hinge's "two parallel atoms" FAILS at
  `m = 4` (witness `Gtz.tetraDesign`, a tie with four pairwise non-parallel
  atoms) — which is why the hinge is asserted at `m = 6, 7` and not below.

The corank-one engine is the trace identity `Σ_c (1 − t_c) q_c = k` against
`Σ_c (1 − t_c) = k`: a co-weighted mean-one family of pivots bounded below by one
is constant.  That is `Gtz.forall_pivot_eq_one_of_one_le`, landed; what is new
here is reading its conclusion as a statement about EVERY `k`-subset, and the
matroid and simplicity corollaries.

## NOT proved here, and NOT provable this way — the honest boundary

Totality at corank `≥ 2` is OPEN and is NOT a lemma one can land before the
target.  Two facts fix its status.

* The corank-one proof does not generalise.  Its engine needs `Σ_c (1 − t_c) = k`,
  i.e. `m = k + 1`; at `m > k + 1` the same identity gives co-weighted mean
  `k/(m−1) < 1`, which is the pigeonhole that STARTS the descent, not a rigidity.
* [MEASURED, outside Lean] A tie whose active set is a single `k`-subset with
  `k ≥ 2` contradicts first-order stationarity: the KKT multiplier `Λ` of the
  design manifold would satisfy `g_cᵀ Λ g_c = 1` at every atom together with
  `tr(Λ S_C) = tr Λ = 1`, whereas the first reading gives `tr(Λ S_C) = k`.  So a
  unique-active tie admits a descent direction and its neighbourhood contains
  designs with NO dominating `k`-subset — i.e. exhibiting one refutes
  `GtzWeighted m k` at the SAME size.  Partial ties are therefore exactly as hard
  to produce as GTZ counterexamples, and any proof of totality through
  criticality of the max assumes what the campaign is proving.  Nothing in this
  file uses that argument; it is recorded to mark the boundary.

Consequently the per-matroid tie systems must be built from the unconditional
necessary conditions (some basis ties, no basis dominates strictly, Parseval, the
matroid stratum), with the criticality conditions kept in a separate, explicitly
hypothesised branch.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Reduction.RealVolumeFloor
import Gtz.Certificates.ResidueDissolution
import Gtz.Ties.CorankOneTieCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## Common orthogonal directions: the dependent subsets -/

/-- The atoms selected by `C` share a nonzero orthogonal direction.  For
`C.card = k` this is exactly dependence of the selected atoms — a `k`-subset of
`ℝᵏ` fails to span precisely when something is orthogonal to all of it. -/
def HasCommonOrthogonal (D : WeightedDesign m k) (C : Finset (Fin m)) : Prop :=
  ∃ direction : Fin k → ℝ, direction ≠ 0 ∧ ∀ c ∈ C, D.atom c ⬝ᵥ direction = 0

/-- The atom sum as a quadratic form: a sum of squared projections. -/
theorem dotProduct_subsetSum_mulVec_of_finset (D : WeightedDesign m k) (C : Finset (Fin m))
    (direction : Fin k → ℝ) :
    direction ⬝ᵥ (subsetSum D C *ᵥ direction)
      = ∑ c ∈ C, (D.atom c ⬝ᵥ direction) ^ 2 := by
  rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun c _ => dotProduct_atomMatrix_mulVec _ _

/-- **Dependent subsets have singular atom sums.**  The shared orthogonal
direction is annihilated by `S_C` outright, so `S_C` is not invertible.  This is
the "every non-basis is singular" half of totality: unconditional, valid at every
design, and therefore empty of information about ties. -/
theorem subsetSum_mulVec_eq_zero_of_commonOrthogonal (D : WeightedDesign m k)
    (C : Finset (Fin m)) {direction : Fin k → ℝ}
    (horthogonal : ∀ c ∈ C, D.atom c ⬝ᵥ direction = 0) :
    subsetSum D C *ᵥ direction = 0 := by
  rw [subsetSum, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun c hc => ?_
  simp [atomMatrix, Matrix.vecMulVec_mulVec, horthogonal c hc]

/-- **Dependent subsets never dominate.**  On the shared orthogonal direction the
gap form is `−|w|² < 0`, so `S_C − 1` is not positive semidefinite.  At a simple
direction matroid this is the sweep's pruning rule: a tie is attained on a basis. -/
theorem not_dominates_of_commonOrthogonal (D : WeightedDesign m k) (C : Finset (Fin m))
    (hdependent : HasCommonOrthogonal D C) : ¬ Dominates D C := by
  obtain ⟨direction, hne, horthogonal⟩ := hdependent
  intro hdominates
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 direction
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    dotProduct_subsetSum_mulVec_of_finset] at hform
  have hprojectionsVanish : ∑ c ∈ C, (D.atom c ⬝ᵥ direction) ^ 2 = 0 :=
    Finset.sum_eq_zero fun c hc => by rw [horthogonal c hc]; ring
  rw [hprojectionsVanish, zero_sub, neg_nonneg] at hform
  exact absurd hform (not_le.mpr (dotProduct_self_pos hne))

/-! ## Selecting the rows of a subset -/

/-- The `k` selected atom indices of a `k`-subset, in increasing order. -/
noncomputable def subsetPick (C : Finset (Fin m)) (hcard : C.card = k) : Fin k → Fin m :=
  fun index => (C.orderIsoOfFin hcard index : Fin m)

theorem subsetPick_mem (C : Finset (Fin m)) (hcard : C.card = k) (index : Fin k) :
    subsetPick C hcard index ∈ C :=
  (C.orderIsoOfFin hcard index).2

theorem subsetPick_injective (C : Finset (Fin m)) (hcard : C.card = k) :
    Function.Injective (subsetPick C hcard) := fun _ _ hequal =>
  (C.orderIsoOfFin hcard).injective (Subtype.ext hequal)

theorem subsetPick_surjOn (C : Finset (Fin m)) (hcard : C.card = k) {c : Fin m} (hc : c ∈ C) :
    ∃ index : Fin k, subsetPick C hcard index = c := by
  refine ⟨(C.orderIsoOfFin hcard).symm ⟨c, hc⟩, ?_⟩
  have hround := (C.orderIsoOfFin hcard).apply_symm_apply ⟨c, hc⟩
  exact congrArg Subtype.val hround

/-- The `k × k` matrix whose rows are the atoms selected by `C`.  Its determinant
is the direction matroid's basis test. -/
noncomputable def subsetRowMatrix (D : WeightedDesign m k) (C : Finset (Fin m))
    (hcard : C.card = k) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun index coord => D.atom (subsetPick C hcard index) coord

theorem subsetRowMatrix_row (D : WeightedDesign m k) (C : Finset (Fin m)) (hcard : C.card = k)
    (index : Fin k) :
    subsetRowMatrix D C hcard index = D.atom (subsetPick C hcard index) := rfl

/-- **A vanishing determinant produces the common orthogonal direction.**  The
kernel vector of the selected-rows matrix is orthogonal to every selected atom. -/
theorem hasCommonOrthogonal_of_det_eq_zero (D : WeightedDesign m k) (C : Finset (Fin m))
    (hcard : C.card = k) (hdet : (subsetRowMatrix D C hcard).det = 0) :
    HasCommonOrthogonal D C := by
  obtain ⟨direction, hne, hkernel⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨direction, hne, fun c hc => ?_⟩
  obtain ⟨index, rfl⟩ := subsetPick_surjOn C hcard hc
  have hrow := congrFun hkernel index
  simpa [Matrix.mulVec, subsetRowMatrix_row] using hrow

/-- **A dominating subset is a basis.**  Contrapositive of the pruning rule,
stated on the determinant so the matroid stratum can consume it directly. -/
theorem dominates_det_ne_zero (D : WeightedDesign m k) (C : Finset (Fin m)) (hcard : C.card = k)
    (hdominates : Dominates D C) : (subsetRowMatrix D C hcard).det ≠ 0 := fun hdet =>
  not_dominates_of_commonOrthogonal D C
    (hasCommonOrthogonal_of_det_eq_zero D C hcard hdet) hdominates

/-! ## Parallel atoms -/

/-- Two parallel atoms inside a `k`-subset give a common orthogonal direction:
one selected row is a multiple of another, the determinant dies, and the kernel
vector is the direction. -/
theorem hasCommonOrthogonal_of_parallel (D : WeightedDesign m k) (C : Finset (Fin m))
    (hcard : C.card = k) {leftAtom rightAtom : Fin m} (hleft : leftAtom ∈ C)
    (hright : rightAtom ∈ C) (hdistinct : leftAtom ≠ rightAtom) {ratio : ℝ}
    (hparallel : D.atom rightAtom = ratio • D.atom leftAtom) :
    HasCommonOrthogonal D C := by
  obtain ⟨leftIndex, hleftIndex⟩ := subsetPick_surjOn C hcard hleft
  obtain ⟨rightIndex, hrightIndex⟩ := subsetPick_surjOn C hcard hright
  have hindexNe : rightIndex ≠ leftIndex := by
    intro hequal
    exact hdistinct (by rw [← hleftIndex, ← hrightIndex, hequal])
  refine hasCommonOrthogonal_of_det_eq_zero D C hcard ?_
  set rows := subsetRowMatrix D C hcard with hrows
  have hrowZero : rows rightIndex + (-ratio) • rows leftIndex = 0 := by
    funext coord
    have hleftRow : rows leftIndex coord = D.atom leftAtom coord := by
      rw [hrows, subsetRowMatrix_row, hleftIndex]
    have hrightRow : rows rightIndex coord = D.atom rightAtom coord := by
      rw [hrows, subsetRowMatrix_row, hrightIndex]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hleftRow, hrightRow, hparallel,
      Pi.smul_apply, Pi.zero_apply]
    ring
  have hupdate := Matrix.det_updateRow_add_smul_self rows hindexNe (-ratio)
  rw [hrowZero] at hupdate
  rw [← hupdate]
  exact Matrix.det_eq_zero_of_row_eq_zero rightIndex fun coord => by
    rw [Matrix.updateRow_self]; rfl

/-- **The parallel-pair pruning rule.**  A `k`-subset carrying two parallel atoms
never dominates.  This is what lets the hinge's "two parallel atoms" conclusion
interact with the tie: the parallel pair kills every `k`-subset containing it. -/
theorem not_dominates_of_parallel (D : WeightedDesign m k) (C : Finset (Fin m))
    (hcard : C.card = k) {leftAtom rightAtom : Fin m} (hleft : leftAtom ∈ C)
    (hright : rightAtom ∈ C) (hdistinct : leftAtom ≠ rightAtom) {ratio : ℝ}
    (hparallel : D.atom rightAtom = ratio • D.atom leftAtom) :
    ¬ Dominates D C :=
  not_dominates_of_commonOrthogonal D C
    (hasCommonOrthogonal_of_parallel D C hcard hleft hright hdistinct hparallel)

/-! ## Corank one: the tie is total, uniform, and simple -/

/-- **Every `k`-subset of a corank-one tie dominates.**  At `m = k+1` each
`k`-subset is an erasure, and the landed criterion pins every pivot at one. -/
theorem corankOne_isTie_dominates {k : ℕ} (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k)
    (htie : IsTie D) {C : Finset (Fin (k + 1))} (hcard : C.card = k) : Dominates D C := by
  obtain ⟨dropped, rfl⟩ := exists_erase_eq_of_card_eq C hcard
  exact forall_dominates_erase_of_isTie hk D htie dropped

/-- **A corank-one tie is TOTAL**: every `k`-subset sits at `λ_min = 1` exactly —
it dominates, and it does not dominate strictly. -/
theorem corankOne_isTie_exactlyTied {k : ℕ} (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k)
    (htie : IsTie D) {C : Finset (Fin (k + 1))} (hcard : C.card = k) :
    Dominates D C ∧ ¬ (subsetSum D C - 1).PosDef :=
  ⟨corankOne_isTie_dominates hk D htie hcard, htie.2 C hcard⟩

/-- **A corank-one tie has no dependent `k`-subset.** -/
theorem corankOne_isTie_not_commonOrthogonal {k : ℕ} (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k)
    (htie : IsTie D) {C : Finset (Fin (k + 1))} (hcard : C.card = k) :
    ¬ HasCommonOrthogonal D C := fun hdependent =>
  not_dominates_of_commonOrthogonal D C hdependent (corankOne_isTie_dominates hk D htie hcard)

/-- **The direction matroid of a corank-one tie is uniform.**  Every `k`-subset
has invertible selected-rows matrix, so every `k`-subset is a basis: the matroid
is `U(k, k+1)` and there are no non-bases to check. -/
theorem corankOne_isTie_det_ne_zero {k : ℕ} (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k)
    (htie : IsTie D) {C : Finset (Fin (k + 1))} (hcard : C.card = k) :
    (subsetRowMatrix D C hcard).det ≠ 0 :=
  dominates_det_ne_zero D C hcard (corankOne_isTie_dominates hk D htie hcard)

/-- Two atoms of `Fin (k+1)` with `2 ≤ k` always miss some index, so they sit
together inside a `k`-subset. -/
theorem exists_erase_mem_pair {k : ℕ} (hk : 2 ≤ k) (leftAtom rightAtom : Fin (k + 1)) :
    ∃ dropped : Fin (k + 1), leftAtom ∈ Finset.univ.erase dropped ∧
      rightAtom ∈ Finset.univ.erase dropped := by
  classical
  have hpairCard : ({leftAtom, rightAtom} : Finset (Fin (k + 1))).card
      < (Finset.univ : Finset (Fin (k + 1))).card := by
    have hle : ({leftAtom, rightAtom} : Finset (Fin (k + 1))).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    have huniv : (Finset.univ : Finset (Fin (k + 1))).card = k + 1 := by simp
    omega
  obtain ⟨dropped, _, hnotPair⟩ := Finset.exists_mem_notMem_of_card_lt_card hpairCard
  have hleftNe : leftAtom ≠ dropped := by
    intro hequal
    exact hnotPair (by rw [← hequal]; exact Finset.mem_insert_self _ _)
  have hrightNe : rightAtom ≠ dropped := by
    intro hequal
    exact hnotPair (by rw [← hequal]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  exact ⟨dropped, Finset.mem_erase.mpr ⟨hleftNe, Finset.mem_univ _⟩,
    Finset.mem_erase.mpr ⟨hrightNe, Finset.mem_univ _⟩⟩

/-- **A corank-one tie is SIMPLE**: no two of its atoms are parallel.  With
`2 ≤ k` the two atoms fit inside a common `k`-subset, which then both dominates
(totality) and cannot dominate (the parallel-pair rule). -/
theorem corankOne_isTie_not_parallel {k : ℕ} (hk : 2 ≤ k) (D : WeightedDesign (k + 1) k)
    (htie : IsTie D) {leftAtom rightAtom : Fin (k + 1)} (hdistinct : leftAtom ≠ rightAtom)
    (ratio : ℝ) : D.atom rightAtom ≠ ratio • D.atom leftAtom := by
  intro hparallel
  obtain ⟨dropped, hleft, hright⟩ := exists_erase_mem_pair hk leftAtom rightAtom
  exact not_dominates_of_parallel D (Finset.univ.erase dropped) (card_erase_univ dropped)
    hleft hright hdistinct hparallel
    (corankOne_isTie_dominates (by omega) D htie (card_erase_univ dropped))

/-! ## The `(4,3)` rung of the per-matroid sweep, closed -/

/-- **Every `(4,3)` tie is total.** -/
theorem tieAtFourThree_isTotal (D : WeightedDesign 4 3) (htie : IsTie D)
    {C : Finset (Fin 4)} (hcard : C.card = 3) :
    Dominates D C ∧ ¬ (subsetSum D C - 1).PosDef :=
  corankOne_isTie_exactlyTied (k := 3) (by omega) D htie hcard

/-- **Every `(4,3)` tie has direction matroid `U(3,4)`**: all four triples are
bases.  Of the two simple rank-3 matroids on four points, only the uniform one
carries a tie. -/
theorem tieAtFourThree_isUniformMatroid (D : WeightedDesign 4 3) (htie : IsTie D)
    {C : Finset (Fin 4)} (hcard : C.card = 3) : (subsetRowMatrix D C hcard).det ≠ 0 :=
  corankOne_isTie_det_ne_zero (k := 3) (by omega) D htie hcard

/-- **Every `(4,3)` tie is primitive**: no two atoms are parallel.  So the hinge's
conclusion — a tie carries two parallel atoms — is FALSE at `m = 4`
(`Gtz.tetraDesign_isTie` witnesses a tie), which is why it is asserted from
`m = 6` on. -/
theorem tieAtFourThree_isPrimitive (D : WeightedDesign 4 3) (htie : IsTie D)
    {leftAtom rightAtom : Fin 4} (hdistinct : leftAtom ≠ rightAtom) (ratio : ℝ) :
    D.atom rightAtom ≠ ratio • D.atom leftAtom :=
  corankOne_isTie_not_parallel (k := 3) (by omega) D htie hdistinct ratio

/-- The `(4,3)` rung is not vacuous: the tetrahedron is a tie, so the statements
above have a witness. -/
theorem tieAtFourThree_witness : IsTie tetraDesign := tetraDesign_isTie

end Gtz
