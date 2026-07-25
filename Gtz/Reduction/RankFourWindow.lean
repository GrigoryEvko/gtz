/-
# Size monotonicity, and the canonical window collapsed to one object per rank

The campaign's canonical list (`gtz_iff_canonical_list`) presents weighted GTZ as a
window `2s ≤ m ≤ M(s) = s(s+1)/2 + 1` of `(s² − 3s + 4)/2` objects per rank — four of
them at rank 4, namely `(8,4)`, `(9,4)`, `(10,4)`, `(11,4)`. This file shows the window
is not a set of independent obligations but a **chain**, and collapses it.

The mechanism is atom splitting. Halving the weight of one atom and giving the other
half to a fresh copy of the same vector is again a design: Parseval and the weight sum
are untouched because the atom matrix is unchanged and the two halves re-sum. A
`k`-subset of the enlarged design either holds at most one copy — in which case it has
the atom multiset of a `k`-subset of the original — or it holds both, in which case its
`k` selected vectors span at most `k−1` dimensions and a common annihilator defeats
domination (`not_dominates_of_repeated_atom_general`, the rank-uniform form of the
rank-3 `not_dominates_of_repeated_atom`). So splitting never creates a dominator, and a
counterexample at size `m` lifts to one at size `m+1`:

    GtzWeighted (m+1) k → GtzWeighted m k                (`gtzWeighted_of_succ`)

i.e. **larger `m` is the STRONGER statement**, and the infimum of the difficulty
functional is non-increasing in `m`. Composing with crystallization — which already
caps the sizes that need checking at `M(k)` — every rank reduces to its single top
object:

    GtzWeighted (M(s)) s → GtzWeightedAll s              (`gtzWeightedAll_of_top`)

so GTZ for all `(n,k)` is equivalent to one statement per rank
(`gtz_iff_top_of_each_rank`), not a window of them. At rank 4 the four window objects
become `(11,4)` alone (`gtzWeightedAll_four_of_eleven`); at rank 3 the campaign's
"binding pair" becomes `(7,3)` alone, since `(6,3)` is implied
(`gtzWeighted_six_three_of_seven_three`).

Nothing here is rank-4-specific: the statements are proved at general `(m,k)` and the
rank-4 window is read off as a corollary.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.Reductions
import Gtz.Reduction.Crystallization
import Gtz.Reduction.LiftingLemma

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ### Repeated atoms never dominate, at every rank -/

/-- **A dominating subset never holds an atom twice.** If two distinct indices of a
subset of size at most the ambient dimension carry the SAME vector, the subset selects
at most `dim − 1` distinct directions; a common annihilator of everything but the
duplicate kills the whole selection, and the coercive reading of domination is
contradicted.

This is the rank-uniform form of `not_dominates_of_repeated_atom`, which the campaign
had only at rank 3 (and in the `Ties` layer, above this one). -/
theorem not_dominates_of_repeated_atom_general {size dim : ℕ}
    (D : WeightedDesign size dim) {C : Finset (Fin size)} {first second : Fin size}
    (hdistinct : first ≠ second) (hfirstMem : first ∈ C) (hsecondMem : second ∈ C)
    (hcardLe : C.card ≤ dim) (hsameAtom : D.atom first = D.atom second) :
    ¬ Dominates D C := by
  intro hdominates
  have hcardPos : 0 < C.card := Finset.card_pos.mpr ⟨second, hsecondMem⟩
  have hfewVectors : (C.erase second).card < dim := by
    rw [Finset.card_erase_of_mem hsecondMem]
    omega
  obtain ⟨probe, hprobeNonzero, hannihilates⟩ :=
    exists_common_annihilator D.atom hfewVectors
  have hsumZero : ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    rcases eq_or_ne c second with hisSecond | hisLive
    · rw [hisSecond, ← hsameAtom,
        hannihilates first (Finset.mem_erase.mpr ⟨hdistinct, hfirstMem⟩)]
      exact zero_pow two_ne_zero
    · rw [hannihilates c (Finset.mem_erase.mpr ⟨hisLive, hc⟩)]
      exact zero_pow two_ne_zero
  have hcoercive := sum_sq_ge_of_dominates hdominates probe
  rw [hsumZero] at hcoercive
  have hprobeSelfNonneg : 0 ≤ probe ⬝ᵥ probe := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  exact hprobeNonzero
    (dotProduct_self_eq_zero.mp (le_antisymm hcoercive hprobeSelfNonneg))

/-! ### Splitting one atom -/

/-- Replacing one entry of a finite family shifts the sum by exactly the difference at
that entry. -/
theorem sum_eq_add_diff_of_agree_off {carrier : Type*} [AddCommGroup carrier]
    (original replaced : Fin m → carrier) (which : Fin m)
    (hagree : ∀ index, index ≠ which → replaced index = original index) :
    ∑ index, replaced index
      = (∑ index, original index) + (replaced which - original which) := by
  have hdifference : ∑ index, (replaced index - original index)
      = replaced which - original which := by
    refine Finset.sum_eq_single which (fun other _ hother => ?_) (fun habsent => ?_)
    · rw [hagree other hother, sub_self]
    · exact absurd (Finset.mem_univ which) habsent
  calc ∑ index, replaced index
      = ∑ index, (original index + (replaced index - original index)) :=
        Finset.sum_congr rfl fun _ _ => by abel
    _ = (∑ index, original index) + ∑ index, (replaced index - original index) :=
        Finset.sum_add_distrib
    _ = (∑ index, original index) + (replaced which - original which) := by
        rw [hdifference]

/-- The atom family after splitting atom `which` into two identical copies: the new
last index carries the same vector. -/
def replicatedAtoms (D : WeightedDesign m k) (which : Fin m) :
    Fin (m + 1) → (Fin k → ℝ) :=
  Fin.snoc D.atom (D.atom which)

/-- The weight family after splitting atom `which`: the original entry is halved and
the fresh copy carries the other half. -/
noncomputable def replicatedWeights (D : WeightedDesign m k) (which : Fin m) :
    Fin (m + 1) → ℝ :=
  Fin.snoc (Function.update D.weight which (D.weight which / 2)) (D.weight which / 2)

/-- **Atom splitting produces a design.** Both defining identities survive because the
atom matrix at the split index is unchanged and the two halves re-sum to the original
weight. -/
noncomputable def replicatedDesign (D : WeightedDesign m k) (which : Fin m) :
    WeightedDesign (m + 1) k where
  atom := replicatedAtoms D which
  weight := replicatedWeights D which
  weight_pos := by
    intro c
    refine Fin.lastCases ?_ ?_ c
    · rw [replicatedWeights, Fin.snoc_last]
      exact half_pos (D.weight_pos which)
    · intro index
      rw [replicatedWeights, Fin.snoc_castSucc]
      rcases eq_or_ne index which with hisSplit | hisOther
      · rw [hisSplit, Function.update_self]
        exact half_pos (D.weight_pos which)
      · rw [Function.update_of_ne hisOther]
        exact D.weight_pos index
  weight_sum_one := by
    rw [Fin.sum_univ_castSucc]
    simp only [replicatedWeights, Fin.snoc_castSucc, Fin.snoc_last]
    rw [sum_eq_add_diff_of_agree_off D.weight
      (Function.update D.weight which (D.weight which / 2)) which
      (fun index hindex => Function.update_of_ne hindex _ _),
      D.weight_sum_one, Function.update_self]
    ring
  isParseval := by
    rw [Fin.sum_univ_castSucc]
    simp only [replicatedWeights, replicatedAtoms, Fin.snoc_castSucc, Fin.snoc_last]
    rw [sum_eq_add_diff_of_agree_off
      (fun index => D.weight index • atomMatrix (D.atom index))
      (fun index =>
        Function.update D.weight which (D.weight which / 2) index
          • atomMatrix (D.atom index))
      which
      (fun index hindex => by rw [Function.update_of_ne hindex]),
      D.isParseval, Function.update_self]
    have hcancel : (D.weight which / 2) • atomMatrix (D.atom which)
        - D.weight which • atomMatrix (D.atom which)
        + (D.weight which / 2) • atomMatrix (D.atom which) = 0 := by
      have hcoefficient : D.weight which / 2 - D.weight which + D.weight which / 2
          = 0 := by ring
      rw [← sub_smul, ← add_smul, hcoefficient, zero_smul]
    rw [add_assoc, hcancel, add_zero]

theorem replicatedAtoms_castSucc (D : WeightedDesign m k) (which index : Fin m) :
    replicatedAtoms D which index.castSucc = D.atom index :=
  Fin.snoc_castSucc _ _ _

theorem replicatedAtoms_last (D : WeightedDesign m k) (which : Fin m) :
    replicatedAtoms D which (Fin.last m) = D.atom which :=
  Fin.snoc_last _ _

@[simp] theorem replicatedDesign_atom_castSucc (D : WeightedDesign m k)
    (which index : Fin m) :
    (replicatedDesign D which).atom index.castSucc = D.atom index :=
  replicatedAtoms_castSucc D which index

@[simp] theorem replicatedDesign_atom_last (D : WeightedDesign m k) (which : Fin m) :
    (replicatedDesign D which).atom (Fin.last m) = D.atom which :=
  replicatedAtoms_last D which

/-- Folding the fresh copy back onto the atom it was split from. -/
def replicationMerge (which : Fin m) : Fin (m + 1) → Fin m :=
  Fin.lastCases which id

@[simp] theorem replicationMerge_castSucc (which index : Fin m) :
    replicationMerge which index.castSucc = index := by
  rw [replicationMerge, Fin.lastCases_castSucc]
  rfl

@[simp] theorem replicationMerge_last (which : Fin m) :
    replicationMerge which (Fin.last m) = which := by
  rw [replicationMerge, Fin.lastCases_last]

/-- Merging is atom-preserving: the split design's atom at any index is the original
design's atom at the merged index. -/
theorem atom_replicationMerge (D : WeightedDesign m k) (which : Fin m)
    (c : Fin (m + 1)) :
    D.atom (replicationMerge which c) = (replicatedDesign D which).atom c := by
  refine Fin.lastCases ?_ ?_ c
  · rw [replicationMerge_last, replicatedDesign_atom_last]
  · intro index
    rw [replicationMerge_castSucc, replicatedDesign_atom_castSucc]

/-! ### Size monotonicity -/

/-- **A counterexample of size `m` lifts to size `m+1`, hence GTZ at size `m+1` is the
STRONGER statement.** Given a dominating `k`-subset of the split design, merging it
back down is injective — a subset holding both copies would hold a repeated atom and
could not dominate — and merging preserves the selected atom multiset, so the merged
subset dominates the original design. -/
theorem gtzWeighted_of_succ (hgtz : GtzWeighted (m + 1) k) : GtzWeighted m k := by
  classical
  rcases Nat.eq_zero_or_pos k with hrankZero | hrankPos
  · rw [hrankZero]
    exact gtzWeighted_dim_zero m
  intro D
  have hrankLe : k ≤ m := rank_le_of_design D
  have hsizePos : 0 < m := lt_of_lt_of_le hrankPos hrankLe
  let which : Fin m := ⟨0, hsizePos⟩
  obtain ⟨selected, hcard, hdominates⟩ := hgtz (replicatedDesign D which)
  -- a dominating subset cannot hold both copies of the split atom
  have hnotBoth : ¬ (Fin.last m ∈ selected ∧ (which : Fin m).castSucc ∈ selected) := by
    rintro ⟨hlastMem, hcopyMem⟩
    refine not_dominates_of_repeated_atom_general (replicatedDesign D which)
      (Fin.castSucc_lt_last which).ne' hlastMem hcopyMem
      (le_of_eq hcard) ?_ hdominates
    rw [replicatedDesign_atom_last, replicatedDesign_atom_castSucc]
  -- every index is either the fresh copy or the lift of the atom it merges to
  have hfiber : ∀ c : Fin (m + 1),
      c = Fin.last m ∨ c = (replicationMerge which c).castSucc := by
    intro c
    refine Fin.lastCases ?_ ?_ c
    · exact Or.inl rfl
    · intro index
      exact Or.inr (by rw [replicationMerge_castSucc])
  -- hence merging is injective on the selected set
  have hinjective : Set.InjOn (replicationMerge which) selected := by
    intro left hleft right hright hmerge
    simp only [Finset.mem_coe] at hleft hright
    rcases hfiber left with hleftLast | hleftCast
    · rcases hfiber right with hrightLast | hrightCast
      · rw [hleftLast, hrightLast]
      · refine absurd ⟨hleftLast ▸ hleft, ?_⟩ hnotBoth
        have hmergeRight : replicationMerge which right = which := by
          rw [← hmerge, hleftLast, replicationMerge_last]
        rw [← hmergeRight, ← hrightCast]
        exact hright
    · rcases hfiber right with hrightLast | hrightCast
      · refine absurd ⟨hrightLast ▸ hright, ?_⟩ hnotBoth
        have hmergeLeft : replicationMerge which left = which := by
          rw [hmerge, hrightLast, replicationMerge_last]
        rw [← hmergeLeft, ← hleftCast]
        exact hleft
      · rw [hleftCast, hrightCast, hmerge]
  refine ⟨selected.image (replicationMerge which), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinjective, hcard]
  · have hsumEq : subsetSum D (selected.image (replicationMerge which))
        = subsetSum (replicatedDesign D which) selected := by
      rw [subsetSum, subsetSum, Finset.sum_image
        (fun left hleft right hright hmerge => hinjective hleft hright hmerge)]
      exact Finset.sum_congr rfl fun c _ => by rw [atom_replicationMerge]
    rw [Dominates, hsumEq]
    exact hdominates

/-- Size monotonicity, iterated: GTZ at any size implies GTZ at every smaller size. -/
theorem gtzWeighted_of_add (size gap : ℕ) :
    GtzWeighted (size + gap) k → GtzWeighted size k := by
  induction gap with
  | zero => intro hgtz; simpa using hgtz
  | succ previous ih =>
      intro hgtz
      refine ih ?_
      have hreassociate : size + (previous + 1) = (size + previous) + 1 := by omega
      rw [hreassociate] at hgtz
      exact gtzWeighted_of_succ hgtz

/-- **The difficulty is monotone in the number of atoms.** -/
theorem gtzWeighted_of_le {size larger : ℕ} (hle : size ≤ larger)
    (hgtz : GtzWeighted larger k) : GtzWeighted size k := by
  obtain ⟨gap, hgap⟩ := Nat.exists_eq_add_of_le hle
  rw [hgap] at hgtz
  exact gtzWeighted_of_add size gap hgtz

/-! ### Size monotonicity survives the all-heavy restriction

Atom splitting duplicates the atom VECTOR and halves only its weight, so the
leverage multiset is unchanged and `replicatedDesign` of an all-heavy design is
all-heavy. The whole monotonicity ladder therefore runs inside the all-heavy
statement, and the all-heavy residual is ALSO one object per rank. That is what
turns the discriminant covering at `(7,3)` alone into the whole of rank three
(`Gtz.Quantitative.DiscriminantSystem`) — the polynomial frontier is a single
sentence, not a pair. -/

/-- Atom splitting preserves all-heaviness: every atom of the split design
carries a vector of the original family, so no leverage changes. -/
theorem replicatedDesign_allHeavy (D : WeightedDesign m k) (which : Fin m)
    (hheavy : AllHeavy D) : AllHeavy (replicatedDesign D which) := by
  intro c
  refine Fin.lastCases ?_ ?_ c
  · rw [replicatedDesign_atom_last]
    exact hheavy which
  · intro index
    rw [replicatedDesign_atom_castSucc]
    exact hheavy index

/-- **All-heavy size monotonicity, one step.** The `gtzWeighted_of_succ` argument
transports verbatim to the all-heavy statement, because the design it feeds to
the larger size is a split of the given one and splitting preserves heaviness. -/
theorem gtzWeightedHeavy_of_succ (hgtz : GtzWeightedHeavy (m + 1) k) :
    GtzWeightedHeavy m k := by
  classical
  rcases Nat.eq_zero_or_pos k with hrankZero | hrankPos
  · rw [hrankZero]
    exact fun D _ => gtzWeighted_dim_zero m D
  intro D hheavy
  have hrankLe : k ≤ m := rank_le_of_design D
  have hsizePos : 0 < m := lt_of_lt_of_le hrankPos hrankLe
  let which : Fin m := ⟨0, hsizePos⟩
  obtain ⟨selected, hcard, hdominates⟩ :=
    hgtz (replicatedDesign D which) (replicatedDesign_allHeavy D which hheavy)
  have hnotBoth : ¬ (Fin.last m ∈ selected ∧ (which : Fin m).castSucc ∈ selected) := by
    rintro ⟨hlastMem, hcopyMem⟩
    refine not_dominates_of_repeated_atom_general (replicatedDesign D which)
      (Fin.castSucc_lt_last which).ne' hlastMem hcopyMem
      (le_of_eq hcard) ?_ hdominates
    rw [replicatedDesign_atom_last, replicatedDesign_atom_castSucc]
  have hfiber : ∀ c : Fin (m + 1),
      c = Fin.last m ∨ c = (replicationMerge which c).castSucc := by
    intro c
    refine Fin.lastCases ?_ ?_ c
    · exact Or.inl rfl
    · intro index
      exact Or.inr (by rw [replicationMerge_castSucc])
  have hinjective : Set.InjOn (replicationMerge which) selected := by
    intro left hleft right hright hmerge
    simp only [Finset.mem_coe] at hleft hright
    rcases hfiber left with hleftLast | hleftCast
    · rcases hfiber right with hrightLast | hrightCast
      · rw [hleftLast, hrightLast]
      · refine absurd ⟨hleftLast ▸ hleft, ?_⟩ hnotBoth
        have hmergeRight : replicationMerge which right = which := by
          rw [← hmerge, hleftLast, replicationMerge_last]
        rw [← hmergeRight, ← hrightCast]
        exact hright
    · rcases hfiber right with hrightLast | hrightCast
      · refine absurd ⟨hrightLast ▸ hright, ?_⟩ hnotBoth
        have hmergeLeft : replicationMerge which left = which := by
          rw [hmerge, hrightLast, replicationMerge_last]
        rw [← hmergeLeft, ← hleftCast]
        exact hleft
      · rw [hleftCast, hrightCast, hmerge]
  refine ⟨selected.image (replicationMerge which), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinjective, hcard]
  · have hsumEq : subsetSum D (selected.image (replicationMerge which))
        = subsetSum (replicatedDesign D which) selected := by
      rw [subsetSum, subsetSum, Finset.sum_image
        (fun left hleft right hright hmerge => hinjective hleft hright hmerge)]
      exact Finset.sum_congr rfl fun c _ => by rw [atom_replicationMerge]
    rw [Dominates, hsumEq]
    exact hdominates

/-- All-heavy size monotonicity, iterated. -/
theorem gtzWeightedHeavy_of_add (size gap : ℕ) :
    GtzWeightedHeavy (size + gap) k → GtzWeightedHeavy size k := by
  induction gap with
  | zero => intro hgtz; simpa using hgtz
  | succ previous ih =>
      intro hgtz
      refine ih ?_
      have hreassociate : size + (previous + 1) = (size + previous) + 1 := by omega
      rw [hreassociate] at hgtz
      exact gtzWeightedHeavy_of_succ hgtz

/-- **The all-heavy residual is monotone in the number of atoms too.** -/
theorem gtzWeightedHeavy_of_le {size larger : ℕ} (hle : size ≤ larger)
    (hgtz : GtzWeightedHeavy larger k) : GtzWeightedHeavy size k := by
  obtain ⟨gap, hgap⟩ := Nat.exists_eq_add_of_le hle
  rw [hgap] at hgtz
  exact gtzWeightedHeavy_of_add size gap hgtz

/-- **Rank three from the all-heavy top object alone.** `rank_three_of_heavy_residuals`
asks for the all-heavy statement at both `6` and `7`; the smaller one is a
consequence of the larger, so a single all-heavy object carries the rank. -/
theorem rank_three_of_heavy_top (h73 : GtzWeightedHeavy 7 3) : GtzWeightedAll 3 :=
  rank_three_of_heavy_residuals (gtzWeightedHeavy_of_le (by norm_num) h73) h73

/-! ### The canonical window collapses to its top object -/

/-- **One object per rank.** Crystallization caps the sizes that must be checked at
`M(k) = k(k+1)/2 + 1`; size monotonicity supplies every size below the cap from the cap
itself. So the single statement at the top of the window carries the whole rank. -/
theorem gtzWeightedAll_of_top (rank : ℕ)
    (htop : GtzWeighted (rank * (rank + 1) / 2 + 1) rank) : GtzWeightedAll rank :=
  crystallization rank fun size hsize => gtzWeighted_of_le (size := size) hsize htop

/-- **GTZ for all `(n,k)` is one statement per rank.** This sharpens
`gtz_iff_canonical_list`, whose right-hand side carries `(s² − 3s + 4)/2` objects at
rank `s`, down to a single object per rank. -/
theorem gtz_iff_top_of_each_rank :
    (∀ rank, 1 ≤ rank → GtzWeightedAll rank) ↔
      (∀ rank, 1 ≤ rank → GtzWeighted (rank * (rank + 1) / 2 + 1) rank) := by
  constructor
  · intro hall rank hrank
    exact hall rank hrank _
  · intro htop rank hrank
    exact gtzWeightedAll_of_top rank (htop rank hrank)

/-- The canonical window at rank `s` is an implication CHAIN, not a set of independent
obligations: every entry follows from the top entry `M(s)`. -/
theorem gtzWeighted_window_of_top (rank : ℕ)
    (htop : GtzWeighted (rank * (rank + 1) / 2 + 1) rank) :
    ∀ size, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 + 1 → GtzWeighted size rank :=
  fun size _ hupper => gtzWeighted_of_le (size := size) hupper htop

/-! ### Rank four -/

/-- The rank-4 window `2s ≤ m ≤ M(s)` is exactly `m ∈ {8, 9, 10, 11}`. -/
theorem rank_four_window_eq (size : ℕ) :
    (2 * 4 ≤ size ∧ size ≤ 4 * (4 + 1) / 2 + 1) ↔
      (size = 8 ∨ size = 9 ∨ size = 10 ∨ size = 11) := by
  constructor
  · rintro ⟨hlower, hupper⟩
    norm_num at hlower hupper
    omega
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num

/-- **The whole rank-4 window is the single object `(11,4)`.** -/
theorem gtzWeighted_window_four_of_eleven (h11 : GtzWeighted 11 4) :
    ∀ size, size ≤ 11 → GtzWeighted size 4 :=
  fun size hsize => gtzWeighted_of_le (size := size) hsize h11

/-- **Rank 4 in full, from one object.** `M(4) = 11`, so `(11,4)` alone gives weighted
GTZ at rank 4 for every size — hence the original statement at rank 4 for every `n`. -/
theorem gtzWeightedAll_four_of_eleven (h11 : GtzWeighted 11 4) : GtzWeightedAll 4 := by
  refine gtzWeightedAll_of_top 4 ?_
  norm_num
  exact h11

/-! ### Rank three: the campaign's "binding pair" is a single object -/

/-- **`(6,3)` is implied by `(7,3)`** — one atom split apart. The repo's frontier lists
`GtzWeighted 6 3` and `GtzWeighted 7 3` as two open cases; the first is not independent.
-/
theorem gtzWeighted_six_three_of_seven_three (h73 : GtzWeighted 7 3) :
    GtzWeighted 6 3 :=
  gtzWeighted_of_le (by norm_num) h73

/-- **Rank 3 from `(7,3)` alone.** `M(3) = 7`, so the campaign's binding pair collapses:
`rank_three_of_the_two_residuals` needs only its second argument. -/
theorem gtzWeightedAll_three_of_seven_three (h73 : GtzWeighted 7 3) :
    GtzWeightedAll 3 := by
  refine gtzWeightedAll_of_top 3 ?_
  norm_num
  exact h73

/-! ### Rank descent by spike padding

A counterexample at `(m, k)` also lifts UP one rank, to `(m+1, k+1)`: keep the old
atoms inside the first `k` coordinates rescaled by `1/√σ`, and add a single spike atom
along the new axis carrying weight `1 − σ`. Parseval splits blockwise. A `(k+1)`-subset
either misses the spike — then all `k+1` of its atoms lie in the old `k`-dimensional
block and the new axis defeats it — or contains it, and then its `k` old atoms inherit
the original design's gap witness, rescaled by `1/σ`. Choosing `σ` above every subset's
gap ratio makes both cases fail, so higher rank is again the STRONGER statement. -/

/-- Non-domination read coercively: a failing subset admits a direction along which the
selected atoms fall short of the identity form. -/
theorem exists_gap_witness {size dim : ℕ} (D : WeightedDesign size dim)
    {C : Finset (Fin size)} (hnot : ¬ Dominates D C) :
    ∃ probe : Fin dim → ℝ, probe ≠ 0 ∧
      ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2 < probe ⬝ᵥ probe := by
  classical
  have hsymmetric : (subsetSum D C - 1)ᵀ = subsetSum D C - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum, Matrix.transpose_sum]
    exact congrArg (· - 1) (Finset.sum_congr rfl fun c _ => by
      rw [atomMatrix, Matrix.transpose_vecMulVec])
  by_contra hall
  push Not at hall
  refine hnot (Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymmetric, fun probe => ?_⟩)
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    subsetSum_form_eq_sum_sq]
  rcases eq_or_ne probe 0 with hzero | hnonzero
  · rw [hzero]
    simp
  · linarith [hall probe hnonzero]

/-- **A uniform gap ratio.** If NO `k`-subset dominates then the finitely many
per-subset gap ratios all sit below one, so a single `σ < 1` beats every one of them. -/
theorem exists_uniform_gap {size dim : ℕ} (D : WeightedDesign size dim)
    (hno : ∀ C : Finset (Fin size), C.card = dim → ¬ Dominates D C)
    (hsize : dim ≤ size) :
    ∃ split : ℝ, 0 < split ∧ split < 1 ∧
      ∀ C : Finset (Fin size), C.card = dim →
        ∃ probe : Fin dim → ℝ, probe ≠ 0 ∧
          ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2 < split * (probe ⬝ᵥ probe) := by
  classical
  set candidates : Finset (Finset (Fin size)) :=
    (Finset.univ : Finset (Fin size)).powersetCard dim with hcandidates
  have hnonempty : candidates.Nonempty := by
    rw [hcandidates, Finset.powersetCard_nonempty]
    simpa using hsize
  have hwitness : ∀ C ∈ candidates, ∃ probe : Fin dim → ℝ, probe ≠ 0 ∧
      ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2 < probe ⬝ᵥ probe := by
    intro C hC
    rw [hcandidates, Finset.mem_powersetCard] at hC
    exact exists_gap_witness D (hno C hC.2)
  choose! chosenProbe chosenNonzero chosenGap using hwitness
  set ratioOf : Finset (Fin size) → ℝ := fun C =>
    (∑ c ∈ C, (D.atom c ⬝ᵥ chosenProbe C) ^ 2) / (chosenProbe C ⬝ᵥ chosenProbe C)
    with hratio
  obtain ⟨worst, hworstMem, hworstMax⟩ :=
    Finset.exists_max_image candidates ratioOf hnonempty
  have hworstPos : 0 < chosenProbe worst ⬝ᵥ chosenProbe worst :=
    dotProduct_self_pos (chosenNonzero worst hworstMem)
  have hworstLt : ratioOf worst < 1 := by
    rw [hratio]
    exact (div_lt_one hworstPos).mpr (chosenGap worst hworstMem)
  have hworstNonneg : 0 ≤ ratioOf worst := by
    rw [hratio]
    exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (le_of_lt hworstPos)
  refine ⟨(1 + ratioOf worst) / 2, by linarith, by linarith, fun C hC => ?_⟩
  have hCmem : C ∈ candidates := by
    rw [hcandidates, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ C, hC⟩
  refine ⟨chosenProbe C, chosenNonzero C hCmem, ?_⟩
  have hpos : 0 < chosenProbe C ⬝ᵥ chosenProbe C :=
    dotProduct_self_pos (chosenNonzero C hCmem)
  have hbound := hworstMax C hCmem
  have hexpand : ∑ c ∈ C, (D.atom c ⬝ᵥ chosenProbe C) ^ 2
      = ratioOf C * (chosenProbe C ⬝ᵥ chosenProbe C) := by
    rw [hratio]
    exact (div_mul_cancel₀ _ (ne_of_gt hpos)).symm
  rw [hexpand]
  refine mul_lt_mul_of_pos_right ?_ hpos
  linarith

/-- The atom family of the spike padding: old atoms sitting in the first `k`
coordinates rescaled by `1/√σ`, plus one spike along the new axis. -/
noncomputable def spikeAtoms (D : WeightedDesign m k) (split : ℝ) :
    Fin (m + 1) → (Fin (k + 1) → ℝ) :=
  Fin.snoc (fun c => Fin.snoc ((Real.sqrt split)⁻¹ • D.atom c) 0)
    (Fin.snoc (0 : Fin k → ℝ) (Real.sqrt (1 - split))⁻¹)

/-- The weight family of the spike padding: the old weights scaled by `σ`, and `1 − σ`
on the spike. -/
noncomputable def spikeWeights (D : WeightedDesign m k) (split : ℝ) :
    Fin (m + 1) → ℝ :=
  Fin.snoc (fun c => split * D.weight c) (1 - split)

theorem spikeAtoms_old_cast (D : WeightedDesign m k) (split : ℝ) (c : Fin m)
    (index : Fin k) :
    spikeAtoms D split c.castSucc index.castSucc
      = (Real.sqrt split)⁻¹ * D.atom c index := by
  rw [spikeAtoms, Fin.snoc_castSucc, Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul]

theorem spikeAtoms_old_last (D : WeightedDesign m k) (split : ℝ) (c : Fin m) :
    spikeAtoms D split c.castSucc (Fin.last k) = 0 := by
  rw [spikeAtoms, Fin.snoc_castSucc, Fin.snoc_last]

theorem spikeAtoms_spike_cast (D : WeightedDesign m k) (split : ℝ) (index : Fin k) :
    spikeAtoms D split (Fin.last m) index.castSucc = 0 := by
  rw [spikeAtoms, Fin.snoc_last, Fin.snoc_castSucc]
  rfl

theorem spikeAtoms_spike_last (D : WeightedDesign m k) (split : ℝ) :
    spikeAtoms D split (Fin.last m) (Fin.last k) = (Real.sqrt (1 - split))⁻¹ := by
  rw [spikeAtoms, Fin.snoc_last, Fin.snoc_last]

theorem spikeWeights_old (D : WeightedDesign m k) (split : ℝ) (c : Fin m) :
    spikeWeights D split c.castSucc = split * D.weight c := by
  rw [spikeWeights, Fin.snoc_castSucc]

theorem spikeWeights_spike (D : WeightedDesign m k) (split : ℝ) :
    spikeWeights D split (Fin.last m) = 1 - split := by
  rw [spikeWeights, Fin.snoc_last]

/-- **Spike padding produces a design one rank up.** -/
noncomputable def spikeDesign (D : WeightedDesign m k) (split : ℝ)
    (hlow : 0 < split) (hhigh : split < 1) : WeightedDesign (m + 1) (k + 1) where
  atom := spikeAtoms D split
  weight := spikeWeights D split
  weight_pos := by
    intro c
    refine Fin.lastCases ?_ ?_ c
    · rw [spikeWeights_spike]
      linarith
    · intro index
      rw [spikeWeights_old]
      exact mul_pos hlow (D.weight_pos index)
  weight_sum_one := by
    rw [Fin.sum_univ_castSucc, spikeWeights_spike]
    simp only [spikeWeights_old]
    rw [← Finset.mul_sum, D.weight_sum_one]
    ring
  isParseval := by
    have hsplitInv : split * ((Real.sqrt split)⁻¹ * (Real.sqrt split)⁻¹) = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt (le_of_lt hlow)]
      exact mul_inv_cancel₀ (ne_of_gt hlow)
    have hrestInv :
        (1 - split) * ((Real.sqrt (1 - split))⁻¹ * (Real.sqrt (1 - split))⁻¹) = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt (by linarith)]
      exact mul_inv_cancel₀ (by linarith)
    have hparsevalEntry : ∀ rowIndex colIndex : Fin k,
        ∑ c, D.weight c * (D.atom c rowIndex * D.atom c colIndex)
          = (1 : Matrix (Fin k) (Fin k) ℝ) rowIndex colIndex := by
      intro rowIndex colIndex
      have hentry := congrFun (congrFun D.isParseval rowIndex) colIndex
      rw [Matrix.sum_apply] at hentry
      simpa [atomMatrix, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
        using hentry
    have hentryFormula : ∀ rowIndex colIndex : Fin (k + 1),
        (∑ c, spikeWeights D split c • atomMatrix (spikeAtoms D split c))
            rowIndex colIndex
          = (∑ c : Fin m, (split * D.weight c)
                * (spikeAtoms D split c.castSucc rowIndex
                  * spikeAtoms D split c.castSucc colIndex))
            + (1 - split) * (spikeAtoms D split (Fin.last m) rowIndex
                * spikeAtoms D split (Fin.last m) colIndex) := by
      intro rowIndex colIndex
      rw [Matrix.sum_apply, Fin.sum_univ_castSucc]
      simp only [Matrix.smul_apply, smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply,
        spikeWeights_old, spikeWeights_spike]
    ext rowIndex colIndex
    rw [hentryFormula]
    refine Fin.lastCases ?_ ?_ rowIndex <;> refine Fin.lastCases ?_ ?_ colIndex
    · simp only [spikeAtoms_old_last, spikeAtoms_spike_last, mul_zero,
        Finset.sum_const_zero, zero_add]
      rw [Matrix.one_apply_eq]
      exact hrestInv
    · intro colInner
      simp only [spikeAtoms_old_last, spikeAtoms_spike_cast, zero_mul, mul_zero,
        Finset.sum_const_zero, add_zero, zero_add]
      exact (Matrix.one_apply_ne (Fin.castSucc_lt_last colInner).ne').symm
    · intro rowInner
      simp only [spikeAtoms_old_last, spikeAtoms_spike_cast, zero_mul, mul_zero,
        Finset.sum_const_zero, add_zero, zero_add]
      exact (Matrix.one_apply_ne (Fin.castSucc_lt_last rowInner).ne).symm
    · intro colInner rowInner
      simp only [spikeAtoms_old_cast, spikeAtoms_spike_cast, mul_zero, zero_mul,
        add_zero]
      have hscale : ∀ c : Fin m,
          split * D.weight c
              * ((Real.sqrt split)⁻¹ * D.atom c rowInner
                * ((Real.sqrt split)⁻¹ * D.atom c colInner))
            = D.weight c * (D.atom c rowInner * D.atom c colInner) := by
        intro c
        calc split * D.weight c
              * ((Real.sqrt split)⁻¹ * D.atom c rowInner
                * ((Real.sqrt split)⁻¹ * D.atom c colInner))
            = (split * ((Real.sqrt split)⁻¹ * (Real.sqrt split)⁻¹))
                * (D.weight c * (D.atom c rowInner * D.atom c colInner)) := by ring
          _ = D.weight c * (D.atom c rowInner * D.atom c colInner) := by
              rw [hsplitInv, one_mul]
      rw [Finset.sum_congr rfl (fun c _ => hscale c), hparsevalEntry rowInner colInner]
      rcases eq_or_ne rowInner colInner with hsame | hdifferent
      · rw [hsame, Matrix.one_apply_eq, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne hdifferent,
          Matrix.one_apply_ne (fun hcast => hdifferent (Fin.castSucc_inj.mp hcast))]

/-- Pairing against a probe whose last coordinate is zero forgets the new axis. -/
theorem dotProduct_snoc_zero {dim : ℕ} (vec : Fin dim → ℝ) (tail : ℝ)
    (probe : Fin dim → ℝ) :
    (Fin.snoc vec tail : Fin (dim + 1) → ℝ) ⬝ᵥ (Fin.snoc probe (0 : ℝ))
      = vec ⬝ᵥ probe := by
  rw [dotProduct, dotProduct, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero]

/-- Pairing against the new axis reads off the last coordinate. -/
theorem dotProduct_lastBasis {dim : ℕ} (vec : Fin (dim + 1) → ℝ) :
    vec ⬝ᵥ (Pi.single (Fin.last dim) (1 : ℝ)) = vec (Fin.last dim) := by
  rw [dotProduct, Finset.sum_eq_single (Fin.last dim)]
  · rw [Pi.single_eq_same, mul_one]
  · intro other _ hother
    rw [Pi.single_eq_of_ne hother, mul_zero]
  · intro habsent
    exact absurd (Finset.mem_univ _) habsent

/-- **A counterexample lifts one rank up, hence rank `k+1` is the STRONGER
statement.** With `σ` beating every subset's gap ratio, the spike padding of a design
with no dominating `k`-subset has no dominating `(k+1)`-subset: a selection missing the
spike is defeated by the new axis, and one containing the spike inherits the old gap
witness rescaled by `1/√σ`. -/
theorem gtzWeighted_of_spike (hrank : 1 ≤ k) (hsize : k ≤ m)
    (hgtz : GtzWeighted (m + 1) (k + 1)) : GtzWeighted m k := by
  classical
  intro D
  by_contra hno
  push Not at hno
  obtain ⟨split, hlow, hhigh, hgap⟩ := exists_uniform_gap D hno hsize
  obtain ⟨selected, hcard, hdominates⟩ := hgtz (spikeDesign D split hlow hhigh)
  have hsizePos : 0 < m := lt_of_lt_of_le hrank hsize
  let which : Fin m := ⟨0, hsizePos⟩
  have hfiber : ∀ c : Fin (m + 1),
      c = Fin.last m ∨ c = (replicationMerge which c).castSucc := by
    intro c
    refine Fin.lastCases ?_ ?_ c
    · exact Or.inl rfl
    · intro index
      exact Or.inr (by rw [replicationMerge_castSucc])
  have hatomOf : ∀ c : Fin (m + 1), c ≠ Fin.last m →
      (spikeDesign D split hlow hhigh).atom c
        = Fin.snoc ((Real.sqrt split)⁻¹ • D.atom (replicationMerge which c)) 0 := by
    intro c hc
    rcases hfiber c with hlast | hcast
    · exact absurd hlast hc
    · conv_lhs => rw [hcast]
      rw [show (spikeDesign D split hlow hhigh).atom = spikeAtoms D split from rfl,
        spikeAtoms, Fin.snoc_castSucc]
  by_cases hspikeMem : Fin.last m ∈ selected
  · -- the selection contains the spike: rescale the old gap witness
    set oldPart : Finset (Fin (m + 1)) := selected.erase (Fin.last m) with holdPart
    have holdCard : oldPart.card = k := by
      rw [holdPart, Finset.card_erase_of_mem hspikeMem, hcard]
      omega
    have holdInj : Set.InjOn (replicationMerge which) oldPart := by
      intro left hleft right hright hmerge
      simp only [holdPart, Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe,
        Set.mem_singleton_iff] at hleft hright
      rcases hfiber left with hleftLast | hleftCast
      · exact absurd hleftLast hleft.2
      rcases hfiber right with hrightLast | hrightCast
      · exact absurd hrightLast hright.2
      rw [hleftCast, hrightCast, hmerge]
    set pulledBack : Finset (Fin m) := oldPart.image (replicationMerge which)
      with hpulledBack
    have hpulledCard : pulledBack.card = k := by
      rw [hpulledBack, Finset.card_image_of_injOn holdInj, holdCard]
    obtain ⟨probe, hprobeNonzero, hprobeGap⟩ := hgap pulledBack hpulledCard
    set paddedProbe : Fin (k + 1) → ℝ := Fin.snoc probe 0 with hpaddedProbe
    have hprobeNorm : paddedProbe ⬝ᵥ paddedProbe = probe ⬝ᵥ probe := by
      rw [hpaddedProbe]
      exact dotProduct_snoc_zero probe 0 probe
    have hspikePairing :
        (spikeDesign D split hlow hhigh).atom (Fin.last m) ⬝ᵥ paddedProbe = 0 := by
      rw [show (spikeDesign D split hlow hhigh).atom = spikeAtoms D split from rfl,
        spikeAtoms, Fin.snoc_last, hpaddedProbe, dotProduct_snoc_zero]
      exact zero_dotProduct probe
    have holdPairing : ∀ c ∈ oldPart,
        ((spikeDesign D split hlow hhigh).atom c ⬝ᵥ paddedProbe) ^ 2
          = ((Real.sqrt split)⁻¹) ^ 2
            * (D.atom (replicationMerge which c) ⬝ᵥ probe) ^ 2 := by
      intro c hc
      have hcne : c ≠ Fin.last m := (Finset.mem_erase.mp hc).1
      rw [hatomOf c hcne, hpaddedProbe, dotProduct_snoc_zero, smul_dotProduct,
        smul_eq_mul, mul_pow]
    have hsumSplit : ∑ c ∈ selected,
          ((spikeDesign D split hlow hhigh).atom c ⬝ᵥ paddedProbe) ^ 2
        = ∑ c ∈ oldPart,
            ((spikeDesign D split hlow hhigh).atom c ⬝ᵥ paddedProbe) ^ 2 := by
      rw [holdPart, ← Finset.add_sum_erase selected _ hspikeMem, hspikePairing]
      ring
    have hsumRescaled : ∑ c ∈ oldPart,
          ((spikeDesign D split hlow hhigh).atom c ⬝ᵥ paddedProbe) ^ 2
        = ((Real.sqrt split)⁻¹) ^ 2
          * ∑ c ∈ pulledBack, (D.atom c ⬝ᵥ probe) ^ 2 := by
      rw [hpulledBack, Finset.sum_image
        (fun left hleft right hright hmerge => holdInj hleft hright hmerge),
        Finset.mul_sum]
      exact Finset.sum_congr rfl holdPairing
    have hcoercive := sum_sq_ge_of_dominates hdominates paddedProbe
    rw [hprobeNorm, hsumSplit, hsumRescaled] at hcoercive
    have hinvSq : ((Real.sqrt split)⁻¹) ^ 2 = split⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (le_of_lt hlow)]
    rw [hinvSq] at hcoercive
    have hscaled : split⁻¹ * ∑ c ∈ pulledBack, (D.atom c ⬝ᵥ probe) ^ 2
        < probe ⬝ᵥ probe := by
      rw [inv_mul_lt_iff₀ hlow]
      exact hprobeGap
    linarith
  · -- the selection misses the spike: the new axis defeats it
    have hcoercive := sum_sq_ge_of_dominates hdominates
      (Pi.single (Fin.last k) (1 : ℝ))
    have hunit : (Pi.single (Fin.last k) (1 : ℝ)) ⬝ᵥ Pi.single (Fin.last k) (1 : ℝ)
        = 1 := by
      rw [dotProduct_lastBasis, Pi.single_eq_same]
    have hallZero : ∑ c ∈ selected,
        ((spikeDesign D split hlow hhigh).atom c
          ⬝ᵥ Pi.single (Fin.last k) (1 : ℝ)) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      have hcne : c ≠ Fin.last m := fun heq => hspikeMem (heq ▸ hc)
      rw [dotProduct_lastBasis, hatomOf c hcne, Fin.snoc_last]
      exact zero_pow two_ne_zero
    rw [hunit, hallZero] at hcoercive
    linarith

/-! ### Consequences: the rank-4 top object carries all of rank 3 -/

/-- `(11,4)` implies weighted GTZ at `(10,3)` by one rank-descent step. -/
theorem gtzWeighted_ten_three_of_eleven_four (h11 : GtzWeighted 11 4) :
    GtzWeighted 10 3 :=
  gtzWeighted_of_spike (by norm_num) (by norm_num) h11

/-- **The rank-4 window's single object implies ALL of rank 3.** Descending one rank
lands at `(10,3)`, size monotonicity brings that down to `M(3) = 7`, and `(7,3)` carries
rank 3 entirely. So the s = 4 window is not an independent target: it is at least as
strong as the campaign's rank-3 frontier.

Not *strictly* stronger — that would need the converse to fail, and if GTZ holds then
every statement in the chain is true and they are mutually implied. Strictness is
therefore not merely unproven; proving it would refute the conjecture. -/
theorem gtzWeightedAll_three_of_eleven_four (h11 : GtzWeighted 11 4) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_seven_three
    (gtzWeighted_of_le (by norm_num) (gtzWeighted_ten_three_of_eleven_four h11))

/-- The same descent one step lower: `(8,4)` already implies the campaign's `(6,3)`. -/
theorem gtzWeighted_six_three_of_eight_four (h84 : GtzWeighted 8 4) :
    GtzWeighted 6 3 :=
  gtzWeighted_of_le (by norm_num)
    (gtzWeighted_of_spike (by norm_num) (by norm_num) h84)

/-- Descending from `(8,4)` reaches `M(3) = 7`, so `(8,4)` already carries all of
rank 3 — one size below the window top. -/
theorem gtzWeightedAll_three_of_eight_four (h84 : GtzWeighted 8 4) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_seven_three
    (gtzWeighted_of_spike (by norm_num) (by norm_num) h84)

/-! ### The other direction: rank 3 does transport upward

The descent above runs from rank 4 down to rank 3. It has a companion running the
other way, and that companion is not vacuous. Naimark duality
(`gtzWeighted_of_dual_rank`) exchanges rank `k` with rank `m − k` at the SAME size, so
at `m = 7` a rank-3 decision IS a rank-4 decision: `7 − 4 = 3`. The object it hands
over, `(7,4)`, has corank 3 and so lies beyond the reach of both
`gtzWeighted_corank_one` and `gtzWeighted_corank_two`.

What does not transport upward is a window TOP. `(11,4)` has corank 7 and is dual to
nothing at rank 3, and `exists_all_certificates_but_discriminant` — which does carry
rank-`k` content up to rank `k+1` — leaves precisely the discriminant coupling open.
So neither direction alone closes a window top, and the chain is not one-way. -/

/-- **Rank 3 hands over the rank-4 object `(7,4)`.** Naimark duality at `m = 7`. -/
theorem gtzWeighted_seven_four_of_seven_three (h73 : GtzWeighted 7 3) :
    GtzWeighted 7 4 :=
  gtzWeighted_of_dual_rank (by norm_num) (by norm_num) h73

/-- The three rank-4 objects below the window top all follow from rank 3, each by
duality at its own size: `5 − 4 = 1`, `6 − 4 = 2`, `7 − 4 = 3`. -/
theorem gtzWeighted_sub_window_four_of_rank_three (h3 : GtzWeightedAll 3)
    (h2 : GtzWeightedAll 2) (h1 : GtzWeightedAll 1) :
    GtzWeighted 5 4 ∧ GtzWeighted 6 4 ∧ GtzWeighted 7 4 :=
  ⟨gtzWeighted_of_dual_rank (by norm_num) (by norm_num) (h1 5),
   gtzWeighted_of_dual_rank (by norm_num) (by norm_num) (h2 6),
   gtzWeighted_seven_four_of_seven_three (h3 7)⟩

end Gtz
