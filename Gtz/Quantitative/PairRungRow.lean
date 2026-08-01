/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Design.FrameConservation
import Gtz.Quantitative.ChartHadamard
import Gtz.Quantitative.GoodTripleGraph

/-!
# The pair rung at a FIXED VERTEX

`Gtz.sum_offDiag_weight_mul_pairMinor` (PairRungAggregate.lean:92) is the pair
conservation law in GLOBAL form: the doubly-weighted off-diagonal total of the
`2x2` gap minors is `1 + Σ_c t_c² (2 l_c − 1)`.  That module's own header says the
ladder it belongs to "climbs to `j = rank - 1` and dies at `j = rank`", and it
states every rung as an aggregate over all pairs.  A minimum-degree argument reads
the same conservation law at ONE atom, and the vertex-indexed form was absent.

This module supplies it.  The content is a composition of two shipped facts --
the excess budget `Gtz.sum_weight_mul_leverage_sub_one` (ChartHadamard.lean:292)
and the weighted Parseval bilinear identity
`Gtz.sum_weight_mul_atomPairing_mul_atomPairing` (FrameConservation.lean:216) read
at a REPEATED index -- so it is cheap, and its value is that the composition was
not available.

## What this does NOT do

It does not shrink anything.  `Gtz.icosaDesign` has every leverage `3` and every
squared pairing `9/5`, so every pair minor is `4 - 9/5 = 11/5 > 0`: the compatible
graph there is the complete `K_6` with all twenty triangles compatible.  No
minimum-degree or Turan argument on that graph can therefore reach a DOMINATING
triple, because the tie leg of domination is per-triple and invisible to graph
Turan theory.  This module is infrastructure, not progress on the open cell.

## Provenance

Harvested from the `gtz-g3` literature scan, where the shape was reverse-engineered
from the only published proof of any GTZ case -- Sengupta and Pautov,
arXiv:2604.05944v5, whose Case A is exactly the not-`Gtz.AllHeavy` branch, whose
Case B is exactly the `Gtz.AllHeavy` branch, and whose engine is exactly this
weighted Parseval bilinear identity.  The transport of that engine to rank three
reproduces the shipped `Gtz.exists_pos_pairMinor_of_allHeavy` and stops; the
obstruction is the coefficient `(k - 2)`, which vanishes only at rank two.
-/

namespace Gtz

variable {size : ℕ}

/-- **THE ROW FORM OF THE PAIR RUNG.**  At every atom the weighted total of the
`2×2` gap minors against the WHOLE index set is the atom's leverage minus two --
a design-blind law with no hypothesis at all.  Two shipped conservation laws
compose: the excess budget `Σ_e t_e (l_e − 1) = rank − 1 = 2` scales the first
term, and the weighted Parseval bilinear identity at a repeated index,
`Σ_e t_e p_ce² = l_c`, collapses the second. -/
theorem sum_weight_mul_pairMinor_row (design : WeightedDesign size 3) (center : Fin size) :
    ∑ other, design.weight other * pairMinor design center other
      = leverageOf (design.atom center) - 2 := by
  have hbudget : ∑ other, design.weight other * heavyExcess design other = 2 := by
    have hshipped := sum_weight_mul_leverage_sub_one design
    simp only [heavyExcess]
    rw [hshipped]
    norm_num
  have hparseval : ∑ other, design.weight other * atomPairing design center other ^ 2
      = leverageOf (design.atom center) := by
    have hshipped := sum_weight_mul_atomPairing_mul_atomPairing design center center
    rw [leverageOf_eq_dotProduct]
    rw [← hshipped]
    exact Finset.sum_congr rfl fun other _ => by
      simp only [atomPairing, dotProduct_comm (design.atom center) (design.atom other)]
      ring
  have hexpand : ∀ other : Fin size,
      design.weight other * pairMinor design center other
        = heavyExcess design center * (design.weight other * heavyExcess design other)
          - design.weight other * atomPairing design center other ^ 2 := by
    intro other
    simp only [pairMinor]
    ring
  rw [Finset.sum_congr rfl fun other _ => hexpand other, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hbudget, hparseval, heavyExcess]
  ring

/-- The diagonal entry of the pair-minor row is forced: `u_c² − l_c² = 1 − 2 l_c`. -/
theorem pairMinor_self (design : WeightedDesign size 3) (center : Fin size) :
    pairMinor design center center = 1 - 2 * leverageOf (design.atom center) := by
  have hself : atomPairing design center center = leverageOf (design.atom center) :=
    (leverageOf_eq_dotProduct _).symm
  simp only [pairMinor, heavyExcess, hself]
  ring

/-- **THE OFF-DIAGONAL ROW LAW.**  Splitting the forced diagonal term off the row
leaves the quantity a non-isolation argument has to sign. -/
theorem sum_erase_weight_mul_pairMinor_row (design : WeightedDesign size 3) (center : Fin size) :
    ∑ other ∈ Finset.univ.erase center, design.weight other * pairMinor design center other
      = leverageOf (design.atom center) - 2
        + design.weight center * (2 * leverageOf (design.atom center) - 1) := by
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin size))
    (fun other => design.weight other * pairMinor design center other) (Finset.mem_univ center)
  have hrow := sum_weight_mul_pairMinor_row design center
  have hself := pairMinor_self design center
  rw [hrow] at hsplit
  rw [hself] at hsplit
  linarith [hsplit]

/-- **NON-ISOLATION AT A SINGLE VERTEX.**  If the off-diagonal row total is
positive then the atom has a strictly compatible partner.  Contrast with the
shipped `Gtz.exists_pos_pairMinor_of_allHeavy`, which produces SOME compatible
pair somewhere in the design; this names the vertex. -/
theorem exists_pos_pairMinor_row {design : WeightedDesign size 3} {center : Fin size}
    (hrow : 0 < leverageOf (design.atom center) - 2
      + design.weight center * (2 * leverageOf (design.atom center) - 1)) :
    ∃ other, other ≠ center ∧ 0 < pairMinor design center other := by
  by_contra hnone
  have hnonpos : ∀ other ∈ (Finset.univ : Finset (Fin size)).erase center,
      design.weight other * pairMinor design center other ≤ 0 := by
    intro other hmem
    have hne : other ≠ center := Finset.ne_of_mem_erase hmem
    have hminor : pairMinor design center other ≤ 0 := by
      by_contra hpos
      exact hnone ⟨other, hne, lt_of_not_ge hpos⟩
    exact mul_nonpos_of_nonneg_of_nonpos (design.weight_pos other).le hminor
  have htotal := Finset.sum_nonpos hnonpos
  rw [sum_erase_weight_mul_pairMinor_row design center] at htotal
  linarith

/-- **THE ALL-HEAVY COROLLARY AT LEVERAGE TWO.**  Any atom of leverage at least
two is non-isolated in the compatible graph: the first summand is nonnegative and
the weight correction is strictly positive once the atom is heavy. -/
theorem exists_pos_pairMinor_of_two_le_leverage {design : WeightedDesign size 3}
    {center : Fin size} (hheavy : 1 < leverageOf (design.atom center))
    (htwo : 2 ≤ leverageOf (design.atom center)) :
    ∃ other, other ≠ center ∧ 0 < pairMinor design center other := by
  refine exists_pos_pairMinor_row ?_
  have hweight := design.weight_pos center
  nlinarith [hweight, hheavy, htwo]

end Gtz
