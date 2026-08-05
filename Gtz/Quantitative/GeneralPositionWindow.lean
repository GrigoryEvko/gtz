/-
# General position and window gating

The sibling window-cofactor lane proved its collapse under the hypothesis
`hgateAll` -- every `(rank+1)`-subset `Q` has `(subsetSum D Q - 1).PosDef` --
and asked whether GENERAL POSITION forces that at a tie.  This file settles the
part of the question that is a theorem, and records the mechanism that decides
the rest.

## What is proved here

`subsetSum_sub_one_eq_insider_sub_outsider` splits the window gap along
Parseval: `S_Q - 1` is the insider sum `sum_{c in Q} (1 - t_c) g_c g_c^T` minus
the outsider sum `sum_{c not in Q} t_c g_c g_c^T`.  Its quadratic form,
`dotProduct_subsetSum_sub_one_mulVec`, turns every gating question into one
scalar inequality between two sums of squares.

Three consequences.

* `posDef_of_card_eq_card` -- at corank one the gating hypothesis is FREE.  A
  `(rank+1)`-subset of a `(rank+1)`-atom design is the whole index set, and the
  full excess is already known positive definite (`posDef_fullExcess`) from
  Parseval alone.  So no general-position hypothesis is needed, no tie
  hypothesis is needed, and every theorem of the sibling lane carrying
  `hgateAll` is unconditional at `m = k + 1`.

* `exists_outsider_dot_ne_zero_of_tight` -- at ANY tight direction of ANY
  dominating subset, some OUTSIDER atom has nonzero pairing with it.  Both sums
  in the split are nonnegative and the insider one dominates, so a tight
  direction orthogonal to every outsider would be orthogonal to every atom, and
  Parseval kills it.  No independence, no genericity, no tie is used.

* `posDef_insert_iff_no_common_null` -- a window obtained by adding one atom to
  a dominating subset is gated exactly when the added atom is off the tight
  space.  Together with the previous item: at least one direction's worth of
  window through a dominating subset always survives.

## Why the probe is not answered by a theorem here, and what the answer is

`exists_outsider_dot_ne_zero_of_tight` says only that not EVERY outsider is
orthogonal to a given tight direction.  ONE outsider may be, and then the window
through it has gap exactly zero -- positive semidefinite, not definite, hence
ungated -- while the atoms stay in general position, because orthogonality to a
line is not a linear dependence.  So nothing visible from inside a window forces
gating, and the question is quantitative.

MEASURED, NOT PROVED HERE.  The question was settled numerically in a chart that
removes the whitening: writing `M = 1 - H` for the complementary rank-`(m-k)`
projection built from `h_c = sqrt(1 - t_c) N^{-1/2} g_c`, and `Theta = M - diag t`,
every predicate is a principal block of the single matrix `Theta` --
`k`-subsets dominate iff the complementary `(m-k)`-block is PSD, windows are
gated iff the complementary `(m-k-1)`-block is PD, and general position is
exactly `the dual matroid is uniform`, a property of `M` ALONE.  The chart was
verified against all eight designs the tree certifies, agreeing with the direct
computation on every tie and every ungated window.

In that chart the tie leg can be imposed ALGEBRAICALLY -- nominating a triple
`A0`, `det Theta[A0] = 0` is linear in one defect -- so the tie is exact to 1e-17
and the only thing left to search is whether the other nineteen triples can be
held nonpositive.  With that control in place:

* on the frames of designs the tree PROVES are ties, the search returns exactly
  zero, at the correct nominations;
* on every frame in general position tested -- three rational ones with uniform
  matroid and four random ones, general-position margins from 1.7e-6 to 7.8e-3 --
  the search returns a strictly positive obstruction, from 4.5e-5 up to 1.8e-2,
  essentially unchanged when the weight floor is dropped a hundredfold.

So the evidence is that NO `(6,3)` tie is in general position: the probe's
hypothesis is VACUOUS at `(6,3)`, and the stratum on which the sibling lane's
collapse would run is empty.  This is consistent with, and strictly weaker than,
the campaign's own open hinge `HingeHoldsAtSize 6 3` (every `(6,3)` tie has a
parallel pair) -- general position implies parallel-freeness, so the hinge
implies exactly this vacuity.  Which is the honest ceiling on the whole route:
general position cannot make the collapse unconditional unless the hinge is
FALSE, and the campaign has already reduced all of rank-3 GTZ to the hinge being
TRUE.

None of that paragraph is a theorem.  It is a controlled measurement over seven
frames, and a local minimiser returning a positive value is an upper bound on
the true minimum, so it can only ever be evidence.  What would settle it: for a
FIXED rational frame the tie question is real quantifier elimination in four
variables over rational data -- nineteen polynomial inequalities, the positivity
of six weights, and one PSD leg already solved -- which is a finite decision
problem, not a search.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.SchurRankOne
import Gtz.Reduction.Naimark
import Gtz.Reduction.DescentLadder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ### The Parseval split of a window gap -/

/-- The quadratic form of a weighted atom sum over ANY index subset.  The shipped
`dot_weighted_atoms_mulVec` is the `Finset.univ` case; the window split needs it
over a general subset and over its complement. -/
theorem dotProduct_sum_smul_atomMatrix_mulVec (coefficient : Fin m → ℝ)
    (vectors : Fin m → (Fin k → ℝ)) (selected : Finset (Fin m))
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ ((∑ c ∈ selected, coefficient c • atomMatrix (vectors c)) *ᵥ probe)
      = ∑ c ∈ selected, coefficient c * (vectors c ⬝ᵥ probe) ^ 2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
    vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
    dotProduct_comm probe (vectors c)]
  ring

/-- **The window gap splits along Parseval.**  Subtracting the identity
`1 = sum_c t_c g_c g_c^T` from `S_Q = sum_{c in Q} g_c g_c^T` leaves the insiders
carrying coefficient `1 - t_c` and the outsiders carrying `-t_c`:

    S_Q - 1  =  sum_{c in Q} (1 - t_c) g_c g_c^T  -  sum_{c not in Q} t_c g_c g_c^T.

At `Q = univ` this is the shipped `fullExcess_eq_coParseval`; the content here is
that the same split runs over an arbitrary subset, which is what turns gating
into a competition between two sums of squares. -/
theorem subsetSum_sub_one_eq_insider_sub_outsider (D : WeightedDesign m k)
    (selected : Finset (Fin m)) :
    subsetSum D selected - 1
      = (∑ c ∈ selected, (1 - D.weight c) • atomMatrix (D.atom c))
        - ∑ c ∈ selectedᶜ, D.weight c • atomMatrix (D.atom c) := by
  have hinsider : ∀ c : Fin m, (1 - D.weight c) • atomMatrix (D.atom c)
      = atomMatrix (D.atom c) - D.weight c • atomMatrix (D.atom c) := fun c => by
    rw [sub_smul, one_smul]
  have hsplit : (∑ c ∈ selected, D.weight c • atomMatrix (D.atom c))
      + ∑ c ∈ selectedᶜ, D.weight c • atomMatrix (D.atom c) = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact D.isParseval
  simp only [hinsider]
  rw [Finset.sum_sub_distrib, subsetSum, ← hsplit]
  abel

/-- **Gating is one scalar inequality.**  The gap's quadratic form is the
insiders' weighted sum of squares minus the outsiders'. -/
theorem dotProduct_subsetSum_sub_one_mulVec (D : WeightedDesign m k)
    (selected : Finset (Fin m)) (probe : Fin k → ℝ) :
    probe ⬝ᵥ ((subsetSum D selected - 1) *ᵥ probe)
      = (∑ c ∈ selected, (1 - D.weight c) * (D.atom c ⬝ᵥ probe) ^ 2)
        - ∑ c ∈ selectedᶜ, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 := by
  rw [subsetSum_sub_one_eq_insider_sub_outsider, Matrix.sub_mulVec,
    dotProduct_sub, dotProduct_sum_smul_atomMatrix_mulVec,
    dotProduct_sum_smul_atomMatrix_mulVec]

/-! ### Corank one: the gating hypothesis is free -/

/-- A subset whose card is the whole index card is the whole index set. -/
theorem eq_univ_of_card_eq_card {selected : Finset (Fin m)}
    (hcard : selected.card = m) : selected = Finset.univ := by
  apply Finset.eq_univ_of_card
  simpa using hcard

/-- **At corank one every window is gated, unconditionally.**  A window has
`rank + 1` atoms; when the design has exactly `rank + 1` atoms the window is the
whole index set, and the full excess `S_univ - 1 = sum_c (1 - t_c) g_c g_c^T` is
positive definite from Parseval alone.

Consequence for the sibling lane: at `m = k + 1` the hypothesis `hgateAll` in
`layer_nonpos_of_isTie_of_forall_gated` and in
`forall_gated_traceInverse_eq_one_iff_layer_eq_zero` is automatically satisfied,
so those theorems are unconditional there -- no tie, no general position, no
gating premise to discharge. -/
theorem posDef_window_of_card_eq_card (D : WeightedDesign m k) (hm : 2 ≤ m)
    (window : Finset (Fin m)) (hcard : window.card = m) :
    (subsetSum D window - 1).PosDef := by
  rw [eq_univ_of_card_eq_card hcard]
  exact posDef_fullExcess D hm

/-- The corank-one instance in the shape the sibling lane's hypotheses take. -/
theorem forall_window_posDef_corankOne (D : WeightedDesign (k + 1) k)
    (hk : 1 ≤ k) :
    ∀ window ∈ (Finset.univ : Finset (Fin (k + 1))).powersetCard (k + 1),
      (subsetSum D window - 1).PosDef := by
  intro window hwindow
  rw [Finset.mem_powersetCard] at hwindow
  exact posDef_window_of_card_eq_card D (by omega) window hwindow.2

/-! ### Tight directions always see an outsider -/

/-- **A tight direction is never orthogonal to every outsider.**  If `probe` is
nonzero and the gap of `selected` vanishes on it, some atom OUTSIDE `selected`
pairs nontrivially with `probe`.

The split does all the work: the outsider sum equals the insider sum on a tight
direction, both are sums of nonnegative terms, and the insider coefficients
`1 - t_c` are strictly positive.  So if every outsider were orthogonal, every
insider would be too, and then Parseval's `eq_zero_of_forall_atom_dot_eq_zero`
forces `probe = 0`.

No linear independence, no genericity and no tie hypothesis is used, and the
subset is arbitrary -- it need not dominate and need not have `rank` elements. -/
theorem exists_outsider_dot_ne_zero_of_tight (D : WeightedDesign m k) (hm : 2 ≤ m)
    (selected : Finset (Fin m)) {probe : Fin k → ℝ} (hne : probe ≠ 0)
    (htight : probe ⬝ᵥ ((subsetSum D selected - 1) *ᵥ probe) = 0) :
    ∃ outsider ∈ selectedᶜ, D.atom outsider ⬝ᵥ probe ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have houtsider : ∑ c ∈ selectedᶜ, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 = 0 :=
    Finset.sum_eq_zero fun c hc => by rw [hnone c hc]; ring
  have hinsider : ∑ c ∈ selected, (1 - D.weight c) * (D.atom c ⬝ᵥ probe) ^ 2 = 0 := by
    have hform := dotProduct_subsetSum_sub_one_mulVec D selected probe
    rw [htight, houtsider] at hform
    linarith [hform]
  have hnonneg : ∀ c ∈ selected,
      0 ≤ (1 - D.weight c) * (D.atom c ⬝ᵥ probe) ^ 2 := fun c _ =>
    mul_nonneg (by linarith [weight_lt_one D hm c]) (sq_nonneg _)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hinsider
  have hdots : ∀ c, D.atom c ⬝ᵥ probe = 0 := by
    intro c
    by_cases hc : c ∈ selected
    · have hterm := hall c hc
      have hcoeff : (1 : ℝ) - D.weight c ≠ 0 := by
        have := weight_lt_one D hm c; linarith
      rcases mul_eq_zero.mp hterm with hzero | hzero
      · exact absurd hzero hcoeff
      · exact pow_eq_zero_iff (n := 2) (by omega) |>.mp hzero
    · exact hnone c (Finset.mem_compl.mpr hc)
  exact hne (eq_zero_of_forall_atom_dot_eq_zero D hdots)

/-! ### Windows through a dominating subset -/

/-- Adding one atom adds its rank-one square to the gap. -/
theorem subsetSum_insert_sub_one (D : WeightedDesign m k)
    {base : Finset (Fin m)} {added : Fin m} (hnew : added ∉ base) :
    subsetSum D (insert added base) - 1
      = (subsetSum D base - 1) + atomMatrix (D.atom added) := by
  rw [subsetSum, subsetSum, Finset.sum_insert hnew]
  abel

/-- **A window through a dominating subset is gated exactly off the tight
space.**  When `base` dominates, the gap of `insert added base` has quadratic
form `q_base(probe) + (g_added . probe)^2`, a sum of two nonnegative terms.  It is
positive definite precisely when no nonzero direction annihilates both -- that
is, when the added atom is off every tight direction of `base`. -/
theorem posDef_insert_iff_no_common_null (D : WeightedDesign m k)
    {base : Finset (Fin m)} (hdominates : Dominates D base) {added : Fin m}
    (hnew : added ∉ base) :
    (subsetSum D (insert added base) - 1).PosDef
      ↔ ∀ probe : Fin k → ℝ, probe ≠ 0 →
          probe ⬝ᵥ ((subsetSum D base - 1) *ᵥ probe) ≠ 0
            ∨ D.atom added ⬝ᵥ probe ≠ 0 := by
  have hhermitian : (subsetSum D (insert added base) - 1).IsHermitian := by
    refine isHermitian_of_transpose_eq ?_
    rw [subsetSum_insert_sub_one D hnew, Matrix.transpose_add,
      transpose_eq_of_isHermitian hdominates.1,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom added)).1]
  have hform : ∀ probe : Fin k → ℝ,
      probe ⬝ᵥ ((subsetSum D (insert added base) - 1) *ᵥ probe)
        = probe ⬝ᵥ ((subsetSum D base - 1) *ᵥ probe)
          + (D.atom added ⬝ᵥ probe) ^ 2 := by
    intro probe
    rw [subsetSum_insert_sub_one D hnew, Matrix.add_mulVec, dotProduct_add,
      atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm probe (D.atom added)]
    ring
  constructor
  · intro hposDef probe hprobe
    by_contra hboth
    push Not at hboth
    have hpositive := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
    rw [star_trivial, hform probe, hboth.1, hboth.2] at hpositive
    norm_num at hpositive
  · intro hsplit
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hhermitian, fun probe hprobe => ?_⟩
    rw [star_trivial, hform probe]
    have hbase : 0 ≤ probe ⬝ᵥ ((subsetSum D base - 1) *ᵥ probe) := by
      have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
      rwa [star_trivial] at h
    rcases hsplit probe hprobe with hleft | hright
    · have hstrict := lt_of_le_of_ne hbase (Ne.symm hleft)
      nlinarith [sq_nonneg (D.atom added ⬝ᵥ probe)]
    · nlinarith [sq_pos_of_ne_zero hright]

/-- **At a tight LINE, some window through the dominating subset is gated.**
Combining the two previous results: a tight direction is never orthogonal to
every outsider, and a window through a dominating subset is gated exactly when
its added atom is off the tight space.  So when the tight space is a single
line -- the generic shape at a tie, and the shape at every certified tie in the
catalogue -- at least one of the `m - |base|` windows through `base` survives.

This is the positive half of the general-position probe, and it needs no
general-position hypothesis.  It does NOT say every window through `base` is
gated: the outsiders orthogonal to the tight line give windows whose gap is
positive semidefinite and singular, hence ungated, with no loss of general
position, since orthogonality to a line is not a linear dependence among
atoms. -/
theorem exists_gated_window_of_tight_line (D : WeightedDesign m k) (hm : 2 ≤ m)
    {base : Finset (Fin m)} (hdominates : Dominates D base)
    {probe : Fin k → ℝ} (hne : probe ≠ 0)
    (htight : probe ⬝ᵥ ((subsetSum D base - 1) *ᵥ probe) = 0)
    (hline : ∀ other : Fin k → ℝ,
      other ⬝ᵥ ((subsetSum D base - 1) *ᵥ other) = 0 →
        ∃ scalar : ℝ, other = scalar • probe) :
    ∃ added ∈ baseᶜ, (subsetSum D (insert added base) - 1).PosDef := by
  obtain ⟨added, haddedMem, haddedDot⟩ :=
    exists_outsider_dot_ne_zero_of_tight D hm base hne htight
  refine ⟨added, haddedMem, ?_⟩
  rw [posDef_insert_iff_no_common_null D hdominates
    (Finset.mem_compl.mp haddedMem)]
  intro other hother
  by_cases hvanish : other ⬝ᵥ ((subsetSum D base - 1) *ᵥ other) = 0
  · right
    obtain ⟨scalar, hscalar⟩ := hline other hvanish
    have hscalarNe : scalar ≠ 0 := by
      rintro rfl
      exact hother (by rw [hscalar, zero_smul])
    rw [hscalar, dotProduct_smul, smul_eq_mul]
    exact mul_ne_zero hscalarNe haddedDot
  · exact Or.inl hvanish

end Gtz
