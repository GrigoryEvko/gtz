/-
# Tie-locking the corank-2 Naimark dual, uniformly in the rank

A tie at the corank-2 cell `(rank + 2, rank)` LOCKS its rank-two Naimark
dual:

* no dual pair strictly dominates — a strictly dominating dual pair would
  transfer (`exists_naimarkDualCorankTwo`) to a strictly dominating primal
  rank-subset, which `IsTie` forbids;
* therefore, by the rank-two four-direction hinge
  (`Gtz.rankTwoFourDirectionHinge_holds` — a theorem at EVERY size, so at
  size `rank + 2` for every rank), every four distinct dual labels carry a
  vanishing pair bracket.

This is the general form of the two locking steps of the `(5,3)` endgame
(`EndpointSpike.sharedLinePairAtEveryTie_holds`).  The hinge consumed here is
FIXED rank-2 material — the descent never recurses in the rank.

The packaged output `exists_tieLockedNaimarkDual` is the exact handoff the
shared-circuit-pair endgame consumes: dictionary (pair and triple) plus the
bracket-zero cover of every dual quadruple.
-/
import Mathlib
import Gtz.Ties.RankTwoHingeBridge
import Gtz.Uniform.NaimarkCorankTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace CorankTwo

open Matrix Finset Gtz

/-- Vanishing of the pair bracket is symmetric — the bracket is
antisymmetric. -/
theorem pairBracket_eq_zero_symm {size : ℕ} (dualDesign : WeightedDesign size 2)
    (leftLabel rightLabel : Fin size)
    (hzero : pairBracket dualDesign leftLabel rightLabel = 0) :
    pairBracket dualDesign rightLabel leftLabel = 0 := by
  have hanti : pairBracket dualDesign rightLabel leftLabel
      = -(pairBracket dualDesign leftLabel rightLabel) := by
    unfold pairBracket
    ring
  rw [hanti, hzero, neg_zero]

/-- **Tie-locking, first half.**  Under a primal tie, no dual pair strictly
dominates: the strict-domination transfer would produce a strictly dominating
primal rank-subset, which `IsTie` forbids. -/
theorem dual_noStrictPair_of_isTie {rank : ℕ}
    (design : WeightedDesign (rank + 2) rank) (htie : IsTie design)
    (dualDesign : WeightedDesign (rank + 2) 2)
    (htransfer : ∀ dualPair : Finset (Fin (rank + 2)), dualPair.card = 2 →
        (Gtz.subsetSum dualDesign dualPair - 1).PosDef →
        (Gtz.subsetSum design dualPairᶜ - 1).PosDef) :
    ∀ dualPair : Finset (Fin (rank + 2)), dualPair.card = 2 →
      ¬ (Gtz.subsetSum dualDesign dualPair - 1).PosDef := by
  intro dualPair hpairCard hposDef
  have hcomplCard : dualPairᶜ.card = rank := by
    rw [Finset.card_compl, Fintype.card_fin, hpairCard]
    omega
  exact htie.2 dualPairᶜ hcomplCard (htransfer dualPair hpairCard hposDef)

/-- **Tie-locking, second half.**  With no strictly dominating dual pair, the
rank-two four-direction hinge forces a vanishing bracket inside EVERY four
distinct dual labels — the bracket-zero cover of the dual quadruples. -/
theorem dual_quadrupleBracketCover_of_noStrictPair {rank : ℕ}
    (dualDesign : WeightedDesign (rank + 2) 2)
    (hnoStrictPair : ∀ dualPair : Finset (Fin (rank + 2)), dualPair.card = 2 →
        ¬ (Gtz.subsetSum dualDesign dualPair - 1).PosDef) :
    ∀ quadA quadB quadC quadD : Fin (rank + 2),
      quadA ≠ quadB → quadA ≠ quadC → quadA ≠ quadD →
      quadB ≠ quadC → quadB ≠ quadD → quadC ≠ quadD →
      pairBracket dualDesign quadA quadB = 0 ∨ pairBracket dualDesign quadA quadC = 0
        ∨ pairBracket dualDesign quadA quadD = 0 ∨ pairBracket dualDesign quadB quadC = 0
        ∨ pairBracket dualDesign quadB quadD = 0
        ∨ pairBracket dualDesign quadC quadD = 0 := by
  intro quadA quadB quadC quadD hdAB hdAC hdAD hdBC hdBD hdCD
  by_contra hnone
  push Not at hnone
  obtain ⟨hneAB, hneAC, hneAD, hneBC, hneBD, hneCD⟩ := hnone
  obtain ⟨dominatingPair, hpairCard, hpairPosDef⟩ :=
    rankTwoFourDirectionHinge_holds (rank + 2) dualDesign quadA quadB quadC quadD
      hdAB hdAC hdAD hdBC hdBD hdCD hneAB hneAC hneAD hneBC hneBD hneCD
  exact hnoStrictPair dominatingPair hpairCard hpairPosDef

/-- **THE TIE-LOCKED DUAL PACKAGE, UNIFORMLY IN THE RANK.**  Every tie at the
corank-2 cell has a rank-two Naimark dual carrying the pair dictionary, the
triple dictionary, and the bracket-zero cover of every dual quadruple.  This
is the exact handoff the shared-circuit-pair endgame consumes. -/
theorem exists_tieLockedNaimarkDual (rank : ℕ)
    (design : WeightedDesign (rank + 2) rank) (htie : IsTie design) :
    ∃ dualDesign : WeightedDesign (rank + 2) 2,
      (∀ pairFst pairSnd : Fin (rank + 2),
        pairBracket dualDesign pairFst pairSnd = 0 →
        ∃ dependence : Fin (rank + 2) → ℝ,
          (∃ witnessLabel, dependence witnessLabel ≠ 0)
            ∧ dependence pairFst = 0 ∧ dependence pairSnd = 0
            ∧ (∑ label, dependence label • design.atom label) = 0)
      ∧ (∀ triFst triSnd triThd : Fin (rank + 2),
          pairBracket dualDesign triFst triSnd = 0 →
          pairBracket dualDesign triFst triThd = 0 →
          pairBracket dualDesign triSnd triThd = 0 →
          ∃ dependence : Fin (rank + 2) → ℝ,
            (∃ witnessLabel, dependence witnessLabel ≠ 0)
              ∧ dependence triFst = 0 ∧ dependence triSnd = 0 ∧ dependence triThd = 0
              ∧ (∑ label, dependence label • design.atom label) = 0)
      ∧ ∀ quadA quadB quadC quadD : Fin (rank + 2),
          quadA ≠ quadB → quadA ≠ quadC → quadA ≠ quadD →
          quadB ≠ quadC → quadB ≠ quadD → quadC ≠ quadD →
          pairBracket dualDesign quadA quadB = 0 ∨ pairBracket dualDesign quadA quadC = 0
            ∨ pairBracket dualDesign quadA quadD = 0
            ∨ pairBracket dualDesign quadB quadC = 0
            ∨ pairBracket dualDesign quadB quadD = 0
            ∨ pairBracket dualDesign quadC quadD = 0 := by
  obtain ⟨dualDesign, hpairDictionary, htripleDictionary, htransfer⟩ :=
    exists_naimarkDualCorankTwo rank design
  exact ⟨dualDesign, hpairDictionary, htripleDictionary,
    dual_quadrupleBracketCover_of_noStrictPair dualDesign
      (dual_noStrictPair_of_isTie design htie dualDesign htransfer)⟩

end CorankTwo
