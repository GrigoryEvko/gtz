/-
# The exchange repair lemma, and local search as a route to GTZ

Every attack in this campaign so far has been a *certificate* attack: exhibit a
polynomial identity, an SOS/Handelman decomposition, or an averaging inequality that
forces some k-subset to dominate. All of them run into the same wall — the infimum of
the margin is exactly 1 and it is ATTAINED (the regular-simplex tie), so no strictly
positive certificate exists.

This file mechanizes a different route: LOCAL SEARCH on the k-subsets. The content is
one elementary lemma about *failing* subsets, and it is elementary precisely because a
failing subset has strict slack to exploit.

## The repair lemma

For a Parseval design and a direction `w`, Parseval says the `t`-weighted average of
the squared projections `(g_c · w)²` equals `|w|²` exactly. A weighted average never
exceeds the maximum, so:

  * `exists_atom_covering_direction` — SOME atom has `(g_d · w)² ≥ |w|²`. The atoms'
    "caps" cover every direction. No convex separation is used; the weighted mean
    bound is the whole proof.

If a k-subset `C` FAILS in direction `w` — meaning `Σ_{c∈C}(g_c · w)² < |w|²`, i.e. the
domination-gap form is negative at `w` — then the terms are nonnegative and sum to less
than `|w|²`, so:

  * `atom_mem_failing_lt` — every atom OF `C` undershoots: `(g_c · w)² < |w|²`;
  * `coveringAtom_notMem_of_failing` — hence the covering atom lies OUTSIDE `C`;
  * `swap_repairs_direction` — swapping it in for ANY atom of `C` restores
    `Σ (g · w)² ≥ |w|²`, i.e. drives the gap form at `w` back to `≥ 0`.

So the swap does not merely improve the failing direction: it repairs it exactly to
the target value, with no epsilon, for every choice of dropped atom. Assembled:
`exists_swap_repairing_worstDirection`.

All of this holds for ANY Parseval design — all-heaviness is never used.

## What is proved here, and what is not

The residual difficulty is stated exactly: repairing one direction can open another.
`ExchangeImproves` names the hypothesis that some bounded-radius exchange strictly
raises a real-valued score, and `gtzWeighted_of_exchangeImproves` discharges the
reduction — a strictly improving move at a finite argmax is a contradiction, so
GTZ follows. The reduction is a THEOREM; the improvement hypothesis is a DEFINITION,
and it is open.

Measured status of the improvement hypothesis at score = least eigenvalue of the
subset Gram (SLSQP/exact-eigen numerics, 2026-07-25, not mechanized and not evidence
of a proof):

  * radius 1 (swap one atom) FAILS on 0.1%–0.4% of failing subsets across shapes
    (5,3) (6,3) (7,3) (6,2) (7,2) (8,4) (9,4); the stuck subsets sit at least
    eigenvalue 0.94–0.997 and are never at exchange distance 1 from the best subset;
  * radius 2 (swap two atoms) had ZERO failures over ~53000 random failing subsets in
    seven shapes, plus ~30000 more on regular-tetrahedron perturbations — **and that
    sampling record is now KNOWN TO BE MISLEADING**: the radius-2 improvement
    hypothesis is REFUTED BY KERNEL PROOF at ranks three and at sizes 6 and 7, for
    the least eigenvalue and for the clipped trace, by exact rational stuck designs
    (`Gtz/Reduction/ExchangeInvariant.lean`, `radiusTwoStuckDesign`,
    `sevenThreeStallDesign`, `clippedTraceStallDesign`; stuck-rate ~4e-7 per failing
    subset, so 53000 samples expected 0.02 hits). Treat every sampling claim in this
    header as a record of how the false conjecture was formed, not as evidence;
  * the drop rule "discard the atom of `C` with the LARGEST projection on `w`" is
    explicit and fails only 1–2%, while "smallest projection" fails ~40% — the
    incoming atom subsumes the largest-projection atom's role at `w`, whereas the
    smallest-projection atom is often the sole cover of a different direction.

The barrier potential `tr(S_C⁻¹)` was measured to get stuck too, so it is not a
better score than the least eigenvalue.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.MarginTransfer
import Gtz.Reduction.LiftingLemma
import Gtz.Reduction.RayleighCertificate
import Gtz.Reduction.Reductions

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- A weighted design has at least one atom: the weights sum to 1, which is
impossible over an empty index. -/
theorem size_pos_of_weightedDesign (D : WeightedDesign m k) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with hzero | hpos
  · exfalso
    subst hzero
    have hsum := D.weight_sum_one
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact absurd hsum (by norm_num)
  · exact hpos

/-- **The caps cover every direction.** For every direction `w` some atom satisfies
`(g_d · w)² ≥ |w|²`.

Parseval gives `Σ_c t_c (g_c · w)² = |w|²` exactly, and the weights are positive and
sum to 1, so the left side is a genuine weighted average of the squared projections.
A weighted average cannot lie strictly below every one of its terms. Elementary: no
convex separation, no spectral theory, and all-heaviness is not used. -/
theorem exists_atom_covering_direction (D : WeightedDesign m k) (w : Fin k → ℝ) :
    ∃ coveringAtom : Fin m, w ⬝ᵥ w ≤ (D.atom coveringAtom ⬝ᵥ w) ^ 2 := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (size_pos_of_weightedDesign D)
  by_contra hnoCover
  rw [not_exists] at hnoCover
  simp only [not_le] at hnoCover
  have hstrict : ∑ c, D.weight c * (D.atom c ⬝ᵥ w) ^ 2
      < ∑ _c : Fin m, D.weight _c * (w ⬝ᵥ w) := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty ?_
    intro c _
    exact mul_lt_mul_of_pos_left (hnoCover c) (D.weight_pos c)
  rw [← Finset.sum_mul, D.weight_sum_one, one_mul,
    parseval_weighted_sum_sq D w] at hstrict
  exact lt_irrefl _ hstrict

/-- **Every atom of a failing subset undershoots the direction.** If the squared
projections of `C` total strictly less than `|w|²`, then — the terms being
nonnegative — each individual atom of `C` is itself strictly below `|w|²`. -/
theorem atom_mem_failing_lt (D : WeightedDesign m k) {C : Finset (Fin m)}
    {w : Fin k → ℝ} (hfails : ∑ c ∈ C, (D.atom c ⬝ᵥ w) ^ 2 < w ⬝ᵥ w)
    {insideAtom : Fin m} (hmem : insideAtom ∈ C) :
    (D.atom insideAtom ⬝ᵥ w) ^ 2 < w ⬝ᵥ w := by
  have hsingle : (D.atom insideAtom ⬝ᵥ w) ^ 2 ≤ ∑ c ∈ C, (D.atom c ⬝ᵥ w) ^ 2 :=
    Finset.single_le_sum (f := fun c => (D.atom c ⬝ᵥ w) ^ 2)
      (fun c _ => sq_nonneg _) hmem
  linarith

/-- **The covering atom of a failing direction lies outside the failing subset.**
Immediate from `atom_mem_failing_lt`: the covering atom meets `|w|²` while every atom
of `C` misses it. -/
theorem coveringAtom_notMem_of_failing (D : WeightedDesign m k) {C : Finset (Fin m)}
    {w : Fin k → ℝ} (hfails : ∑ c ∈ C, (D.atom c ⬝ᵥ w) ^ 2 < w ⬝ᵥ w)
    {coveringAtom : Fin m} (hcovers : w ⬝ᵥ w ≤ (D.atom coveringAtom ⬝ᵥ w) ^ 2) :
    coveringAtom ∉ C := fun hmem =>
  absurd (atom_mem_failing_lt D hfails hmem) (not_lt.mpr hcovers)

/-- **The swap repairs the direction exactly.** Trading any atom of `C` for an atom
covering `w` restores `Σ (g · w)² ≥ |w|²`: the incoming atom alone already meets the
target, and the retained atoms contribute a nonnegative remainder. The dropped atom
is arbitrary — the repair does not depend on which one leaves. -/
theorem swap_repairs_direction (D : WeightedDesign m k) {C : Finset (Fin m)}
    {w : Fin k → ℝ} {coveringAtom : Fin m} (hnotMem : coveringAtom ∉ C)
    (hcovers : w ⬝ᵥ w ≤ (D.atom coveringAtom ⬝ᵥ w) ^ 2) (droppedAtom : Fin m) :
    w ⬝ᵥ w
      ≤ ∑ e ∈ insert coveringAtom (C.erase droppedAtom), (D.atom e ⬝ᵥ w) ^ 2 := by
  have hnotErased : coveringAtom ∉ C.erase droppedAtom := fun hmem =>
    hnotMem (Finset.mem_of_mem_erase hmem)
  rw [Finset.sum_insert hnotErased]
  have hretained : 0 ≤ ∑ e ∈ C.erase droppedAtom, (D.atom e ⬝ᵥ w) ^ 2 :=
    Finset.sum_nonneg fun e _ => sq_nonneg _
  linarith

/-- The swap in domination-gap form: after the exchange the gap form at the repaired
direction is nonnegative, where before the exchange it was negative. -/
theorem swap_gapForm_nonneg (D : WeightedDesign m k) {C : Finset (Fin m)}
    {w : Fin k → ℝ} {coveringAtom : Fin m} (hnotMem : coveringAtom ∉ C)
    (hcovers : w ⬝ᵥ w ≤ (D.atom coveringAtom ⬝ᵥ w) ^ 2) (droppedAtom : Fin m) :
    0 ≤ w ⬝ᵥ ((subsetSum D (insert coveringAtom (C.erase droppedAtom)) - 1) *ᵥ w) := by
  rw [dominationGap_form]
  have := swap_repairs_direction D hnotMem hcovers droppedAtom
  linarith

/-- The exchange preserves cardinality: dropping a member and inserting a
non-member leaves the count unchanged. -/
theorem card_swap_eq_card {C : Finset (Fin m)} {coveringAtom droppedAtom : Fin m}
    (hnotMem : coveringAtom ∉ C) (hmem : droppedAtom ∈ C) :
    (insert coveringAtom (C.erase droppedAtom)).card = C.card := by
  have hnotErased : coveringAtom ∉ C.erase droppedAtom := fun h =>
    hnotMem (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hnotErased, Finset.card_erase_of_mem hmem]
  exact Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨droppedAtom, hmem⟩)

/-- **The repair lemma, assembled.** A k-subset failing in direction `w` admits an
outside atom whose insertion — in exchange for ANY of its members — restores the
domination-gap form at `w` to nonnegative, at unchanged cardinality.

This is the exact content available at a failing subset, and it is where the routes
blocked by the attained-zero obstruction differ from this one: the hypothesis is a
STRICT failure, so there is strict slack to consume, and the conclusion is reached
with no certificate and no epsilon. What is NOT claimed is that the repaired subset
is globally better — repairing `w` may open a different direction. That gap is the
open content of `ExchangeImproves`. -/
theorem exists_swap_repairing_worstDirection (D : WeightedDesign m k)
    (C : Finset (Fin m)) {w : Fin k → ℝ}
    (hfails : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) < 0) :
    ∃ coveringAtom : Fin m, coveringAtom ∉ C ∧
      ∀ droppedAtom ∈ C,
        (insert coveringAtom (C.erase droppedAtom)).card = C.card ∧
        0 ≤ w ⬝ᵥ
          ((subsetSum D (insert coveringAtom (C.erase droppedAtom)) - 1) *ᵥ w) := by
  rw [dominationGap_form] at hfails
  have hsumFails : ∑ c ∈ C, (D.atom c ⬝ᵥ w) ^ 2 < w ⬝ᵥ w := by linarith
  obtain ⟨coveringAtom, hcovers⟩ := exists_atom_covering_direction D w
  have hnotMem := coveringAtom_notMem_of_failing D hsumFails hcovers
  refine ⟨coveringAtom, hnotMem, fun droppedAtom hmem => ⟨?_, ?_⟩⟩
  · exact card_swap_eq_card hnotMem hmem
  · exact swap_gapForm_nonneg D hnotMem hcovers droppedAtom

/-- **The exchange hypothesis.** Every non-dominating k-subset admits some k-subset
of strictly larger score. The intended score is the least eigenvalue of the subset
Gram and the intended witness is a bounded-radius exchange, but the reduction below
needs neither: any real-valued score and any witness will do.

This is a DEFINITION naming an open hypothesis, not a theorem. See the file header
for its measured status. -/
def ExchangeImproves (m k : ℕ)
    (score : WeightedDesign m k → Finset (Fin m) → ℝ) : Prop :=
  ∀ (D : WeightedDesign m k) (C : Finset (Fin m)), C.card = k → ¬ Dominates D C →
    ∃ improved : Finset (Fin m), improved.card = k ∧ score D C < score D improved

/-- **Local search closes GTZ.** If some real-valued score on k-subsets strictly
increases at every non-dominating k-subset, then weighted GTZ holds at that size:
take a k-subset maximizing the score — one exists because the k-subsets are a
nonempty finite family whenever `k ≤ m` — and a strict improvement at it would
contradict maximality.

The whole burden is therefore transferred to `ExchangeImproves`; no analysis,
no certificate, and no spectral theory enters here. -/
theorem gtzWeighted_of_exchangeImproves (hsizeLe : k ≤ m)
    (score : WeightedDesign m k → Finset (Fin m) → ℝ)
    (himproves : ExchangeImproves m k score) : GtzWeighted m k := by
  intro D
  have hfamilyNonempty :
      (Finset.univ.powersetCard k : Finset (Finset (Fin m))).Nonempty := by
    refine Finset.powersetCard_nonempty.mpr ?_
    simpa using hsizeLe
  obtain ⟨best, hbestMem, hbestMax⟩ :=
    Finset.exists_max_image _ (fun C => score D C) hfamilyNonempty
  have hbestCard : best.card = k := (Finset.mem_powersetCard.mp hbestMem).2
  refine ⟨best, hbestCard, ?_⟩
  by_contra hnotDominates
  obtain ⟨improved, himprovedCard, hstrict⟩ :=
    himproves D best hbestCard hnotDominates
  have himprovedMem : improved ∈ (Finset.univ.powersetCard k : Finset (Finset (Fin m))) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, himprovedCard⟩
  exact absurd (hbestMax improved himprovedMem) (not_le.mpr hstrict)

/-- The rank-generic corollary: an exchange-improving score at every size decides
weighted GTZ at that rank, hence (through the shipped size and window reductions)
the original problem at that rank. -/
theorem gtzWeightedAll_of_exchangeImproves
    (score : ∀ size : ℕ, WeightedDesign size k → Finset (Fin size) → ℝ)
    (himproves : ∀ size : ℕ, k ≤ size → ExchangeImproves size k (score size)) :
    GtzWeightedAll k := by
  intro size
  rcases le_or_gt k size with hle | hlt
  · exact gtzWeighted_of_exchangeImproves hle (score size) (himproves size hle)
  · -- Fewer atoms than the rank: Parseval is then unsatisfiable, so the design type
    -- is empty and the claim is vacuous (`rank_le_of_design`).
    exact fun D => absurd (rank_le_of_design D) (not_le.mpr hlt)

end Gtz
