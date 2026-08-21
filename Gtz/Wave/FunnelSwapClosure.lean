/-
# The funnel refuses a second swap, in every direction

`Gtz.isTie_sixThree_allHeavy_or_funnel` splits every `(6,3)` tie into ALL-HEAVY
or a FUNNEL, so closing the funnel branch reduces the main statement to the
all-heavy case.  The landed `Gtz.unitAtom_two_mirror_swaps_absurd` closes the
funnel when a dominator carries two null-sharing swaps at DIFFERENT members.
This module closes the two remaining directions, so a funnel refuses a second
swap outright.

## The three directions of a second swap

Let `T = {p,x,y}` be a dominator of a funnel, avoiding the unit atom `a` and
fixing it.  A second null-sharing dominator one swap from `T` either

1. exchanges a different member — the landed absurdity, or
2. exchanges `p` for the unit atom `a` itself — then the mirror identity reads
   `(g_p·g_a)·g_p = (g_a·g_a)·g_a = g_a`, so the unit atom IS a multiple of
   `g_p` (`Gtz.unitAtom_parallel_of_swap_to_atom`), or
3. exchanges `p` for one of the two remaining labels — and a second such swap
   makes THREE atoms blind to the unit atom, which no `(6,3)` design admits.

## The new obstruction: three blind atoms overspend the budget

Direction 3 is the one nothing covered, and it closes on weights alone
(`Gtz.unitAtom_three_blind_absurd`).  Parseval read at the unit atom is

  `t_a + Σ_{c ≠ a} t_c·(g_c·g_a)² = 1` .

If three of the five remaining atoms are blind to `a`, the whole reading is
carried by the other two, `t_x·s_x² + t_y·s_y² = 1 − t_a`, while the funnel's
own resolution says `s_x² + s_y² = 1`.  So

  `1 − t_a = t_x·s_x² + t_y·s_y² ≤ t_x + t_y < 1 − t_a` ,

the strict step being that the three blind atoms carry positive weight.  **A
funnel has at most two blind atoms, and the bound is on the weights, not on the
geometry.**

## What closes

`Gtz.unitAtom_second_swap_absurd` assembles the three directions: at a `(6,3)`
design with no parallel pair, a funnel's dominator has at most ONE null-sharing
swap.  With the landed combinatorics of the swap graph on triples of a
five-element ground set, a family with every swap-degree at most one has at most
three members (`Gtz.swapDegree_le_one_card_le_three`, by decision procedure over
all `1024` families).

[MEASURED, and this is why the reduction matters.  Over 71 numerically located
`(5,3)` ties, the number of weakly dominating triples was never below six: the
histogram is `6 ↦ 1`, `7 ↦ 33`, `8 ↦ 37`.  The `(5,3)` diamond tie carries
eight.  Against a cap of three, no funnel survives — but the dominator count of
a `(5,3)` tie is measured, not proved, so the branch closes CONDITIONALLY on it
and that conditional is the remaining work.]
-/
import Gtz.Wave.MirrorPairMinorTrigger
import Gtz.Wave.FunnelSecondInvariantFloor
import Gtz.Wave.KOneAnchor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. Three atoms cannot be blind to a unit atom -/

/-- **THREE BLIND ATOMS OVERSPEND THE READING BUDGET.**  At a `(6,3)` design
with a unit atom whose two visible partners already resolve it, no third atom
can be blind.  Parseval fixes the total reading, the visible pair can carry at
most its own weight, and the blind atoms' weight is strictly positive. -/
theorem unitAtom_three_blind_absurd (D : WeightedDesign 6 3) {a x y : Fin 6}
    (hax : a ≠ x) (hay : a ≠ y) (hxy : x ≠ y)
    (hunit : leverageOf (D.atom a) = 1)
    (hresolve : (D.atom x ⬝ᵥ D.atom a) ^ 2 + (D.atom y ⬝ᵥ D.atom a) ^ 2 = 1)
    (hblind : ∀ c : Fin 6, c ≠ a → c ≠ x → c ≠ y → D.atom c ⬝ᵥ D.atom a = 0) :
    False := by
  classical
  set S : Finset (Fin 6) := {a, x, y} with hS
  have hcard : S.card = 3 := by
    rw [hS, Finset.card_insert_of_notMem (by simp [hax, hay]),
      Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
  -- Parseval at the unit atom, collapsed onto the three visible labels
  have hpar := parseval_probe_form D (D.atom a)
  have hcollapse : ∑ c ∈ S, D.weight c * (D.atom c ⬝ᵥ D.atom a) ^ 2
      = ∑ c, D.weight c * (D.atom c ⬝ᵥ D.atom a) ^ 2 := by
    refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_
    have hne : c ≠ a ∧ c ≠ x ∧ c ≠ y := by
      rw [hS] at hc; simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      push_neg at hc; exact hc
    rw [hblind c hne.1 hne.2.1 hne.2.2]; ring
  have hself : D.atom a ⬝ᵥ D.atom a = 1 := by
    rw [dotProduct_self_eq_leverage]; exact hunit
  have hexpand : ∑ c ∈ S, D.weight c * (D.atom c ⬝ᵥ D.atom a) ^ 2
      = D.weight a + D.weight x * (D.atom x ⬝ᵥ D.atom a) ^ 2
        + D.weight y * (D.atom y ⬝ᵥ D.atom a) ^ 2 := by
    rw [hS, Finset.sum_insert (by simp [hax, hay]), Finset.sum_insert (by simp [hxy]),
      Finset.sum_singleton, hself]
    ring
  rw [hcollapse, hpar, hself] at hexpand
  -- the visible pair carries at most its own weight
  have hxs := sq_nonneg (D.atom x ⬝ᵥ D.atom a)
  have hys := sq_nonneg (D.atom y ⬝ᵥ D.atom a)
  have hwx := D.weight_pos x
  have hwy := D.weight_pos y
  have hcarry : D.weight x * (D.atom x ⬝ᵥ D.atom a) ^ 2
      + D.weight y * (D.atom y ⬝ᵥ D.atom a) ^ 2
      ≤ D.weight x + D.weight y := by nlinarith [hresolve, hxs, hys, hwx, hwy]
  -- the blind atoms carry strictly positive weight
  have hweights : D.weight a + D.weight x + D.weight y
      + ∑ c ∈ Finset.univ \ S, D.weight c = 1 := by
    have h := Finset.sum_sdiff (Finset.subset_univ S) (f := D.weight)
    rw [D.weight_sum_one] at h
    have hSsum : ∑ c ∈ S, D.weight c = D.weight a + D.weight x + D.weight y := by
      rw [hS, Finset.sum_insert (by simp [hax, hay]), Finset.sum_insert (by simp [hxy]),
        Finset.sum_singleton]
      ring
    rw [hSsum] at h; linarith
  have hrest : 0 < ∑ c ∈ Finset.univ \ S, D.weight c := by
    refine Finset.sum_pos (fun c _ => D.weight_pos c) ?_
    refine Finset.card_pos.mp ?_
    rw [Finset.card_sdiff, Finset.inter_univ, hcard, Finset.card_univ, Fintype.card_fin]
    norm_num
  linarith

/-! ## 2. A swap onto the unit atom is already a parallel pair -/

/-- **A SWAP ONTO THE UNIT ATOM IS A HINGE WITNESS.**  If the triple obtained by
exchanging a member for the unit atom itself is also killed at the atom, the
mirror identity reads the atom as a multiple of the exchanged member.  The unit
length of the atom is what makes the right side nonzero. -/
theorem unitAtom_parallel_of_swap_to_atom (D : WeightedDesign 6 3)
    {a p : Fin 6} {C : Finset (Fin 6)} (hpa : p ≠ a) (hp : p ∈ C) (ha : a ∉ C)
    (hunit : leverageOf (D.atom a) = 1)
    (hnullC : (subsetSum D C - 1) *ᵥ D.atom a = 0)
    (hnullSwap : (subsetSum D (insert a (C.erase p)) - 1) *ᵥ D.atom a = 0) :
    HasParallelPair D := by
  have hmirror := mirror_reading_smul_eq D hp ha hnullC hnullSwap
  have hself : D.atom a ⬝ᵥ D.atom a = 1 := by
    rw [dotProduct_self_eq_leverage]; exact hunit
  rw [hself, one_smul] at hmirror
  exact ⟨p, a, D.atom p ⬝ᵥ D.atom a, hpa, hmirror.symm⟩

/-! ## 3. The swap graph on triples of a five-element ground set -/

/-- The ten triples of a five-element ground set, indexed. -/
def tripleIndex (i : Fin 10) : Finset (Fin 5) :=
  ![{0,1,2}, {0,1,3}, {0,1,4}, {0,2,3}, {0,2,4},
    {0,3,4}, {1,2,3}, {1,2,4}, {1,3,4}, {2,3,4}] i

/-- Two indexed triples are one swap apart when they share exactly two members. -/
def OneSwapApart (i j : Fin 10) : Prop := (tripleIndex i ∩ tripleIndex j).card = 2

instance (i j : Fin 10) : Decidable (OneSwapApart i j) := by
  unfold OneSwapApart; infer_instance

set_option maxRecDepth 100000 in
/-- **THE SWAP-DEGREE CAP.**  A family of triples of a five-element ground set in
which every member is one swap from at most one other member has at most three
members.  Decided over all `1024` families.  The bound is attained, for example
by `{0,1,2}`, `{0,1,3}`, `{2,3,4}`. -/
theorem swapDegree_le_one_card_le_three (F : Finset (Fin 10))
    (hdeg : ∀ i ∈ F, (F.filter fun j => j ≠ i ∧ OneSwapApart i j).card ≤ 1) :
    F.card ≤ 3 := by
  revert hdeg
  revert F
  decide

/-! ## 4. The funnel refuses a second swap at the same member -/

/-- **A FUNNEL REFUSES TWO SWAPS AT ONE MEMBER.**  The two exchanged labels are
either the unit atom itself, which is already a parallel pair, or the two
remaining labels of the design, which makes three atoms blind to the unit atom
and overspends the reading budget.  Together with the landed
`Gtz.unitAtom_two_mirror_swaps_absurd` for swaps at different members, a
funnel's dominator carries at most ONE null-sharing swap. -/
theorem unitAtom_second_swap_absurd (D : WeightedDesign 6 3)
    (hprim : ¬ HasParallelPair D) {a p x y q r : Fin 6}
    (hpx : p ≠ x) (hpy : p ≠ y) (hxy : x ≠ y)
    (hap : a ≠ p) (hax : a ≠ x) (hay : a ≠ y) (hqr : q ≠ r)
    (hq : q ∉ ({p, x, y} : Finset (Fin 6))) (hr : r ∉ ({p, x, y} : Finset (Fin 6)))
    (hunit : leverageOf (D.atom a) = 1)
    (hfix : subsetSum D ({p, x, y} : Finset (Fin 6)) *ᵥ D.atom a = D.atom a)
    (hswapQ : (subsetSum D (insert q ((({p, x, y} : Finset (Fin 6))).erase p)) - 1)
      *ᵥ D.atom a = 0)
    (hswapR : (subsetSum D (insert r ((({p, x, y} : Finset (Fin 6))).erase p)) - 1)
      *ᵥ D.atom a = 0) :
    False := by
  classical
  have hp : p ∈ ({p, x, y} : Finset (Fin 6)) := by simp
  have havoid : a ∉ ({p, x, y} : Finset (Fin 6)) := by
    simp [hap, hax, hay]
  have hnullC : (subsetSum D ({p, x, y} : Finset (Fin 6)) - 1) *ᵥ D.atom a = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix, sub_self]
  -- a swap onto the unit atom is already a parallel pair
  by_cases hqa : q = a
  · subst hqa
    exact hprim (unitAtom_parallel_of_swap_to_atom D (Ne.symm hap) hp havoid hunit
      hnullC hswapQ)
  by_cases hra : r = a
  · subst hra
    exact hprim (unitAtom_parallel_of_swap_to_atom D (Ne.symm hap) hp havoid hunit
      hnullC hswapR)
  -- otherwise the two exchanged labels are the two remaining labels of the design
  have hqp : q ≠ p := by intro h; exact hq (by simp [h])
  have hqx : q ≠ x := by intro h; exact hq (by simp [h])
  have hqy : q ≠ y := by intro h; exact hq (by simp [h])
  have hrp : r ≠ p := by intro h; exact hr (by simp [h])
  have hrx : r ≠ x := by intro h; exact hr (by simp [h])
  have hry : r ≠ y := by intro h; exact hr (by simp [h])
  obtain ⟨hblindP, hblindQ⟩ :=
    mirror_readings_eq_zero_of_not_hasParallelPair D hprim (Ne.symm hqp) hp hq hnullC hswapQ
  obtain ⟨-, hblindR⟩ :=
    mirror_readings_eq_zero_of_not_hasParallelPair D hprim (Ne.symm hrp) hp hr hnullC hswapR
  -- the two visible members resolve the whole reading
  have hres := unitAtom_readings_resolve (m := 5) D hunit hfix
  rw [Finset.sum_insert (by simp [hpx, hpy]), Finset.sum_insert (by simp [hxy]),
    Finset.sum_singleton, hblindP] at hres
  -- the six labels are exhausted, so every other atom is one of the three blind ones
  have hcard : ({a, p, x, y, q, r} : Finset (Fin 6)).card = 6 := by
    rw [Finset.card_insert_of_notMem (by simp [hap, hax, hay, Ne.symm hqa, Ne.symm hra]),
      Finset.card_insert_of_notMem (by simp [hpx, hpy, Ne.symm hqp, Ne.symm hrp]),
      Finset.card_insert_of_notMem (by simp [hxy, Ne.symm hqx, Ne.symm hrx]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hqy, Ne.symm hry]),
      Finset.card_insert_of_notMem (by simp [hqr]), Finset.card_singleton]
  have huniv : ({a, p, x, y, q, r} : Finset (Fin 6)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, Fintype.card_fin])
  refine unitAtom_three_blind_absurd D hax hay hxy hunit (by linarith [hres]) ?_
  intro c hca hcx hcy
  have hmem : c ∈ ({a, p, x, y, q, r} : Finset (Fin 6)) := by rw [huniv]; exact Finset.mem_univ c
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hca
  · exact hblindP
  · exact absurd rfl hcx
  · exact absurd rfl hcy
  · exact hblindQ
  · exact hblindR

end Gtz
