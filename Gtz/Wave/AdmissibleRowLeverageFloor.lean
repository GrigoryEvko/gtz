/-
# An admissible row forces a leverage floor, and the floor needs no seed

Branch B is the region in which every atom is strictly heavy and every pair is
admissible, and it is the case of the hinge whose conclusion has no witness to
point at: a parallel pair is never admissible, so a branch-B design carries
none.  Every instrument the campaign has aimed at branch B so far reads the
TRIPLES.  This module reads a single ROW.

## The floor

Fix an atom `a` and suppose every pair through `a` is admissible.  Parseval read
at `g_a` totals the squared readings of `g_a` by the other atoms, and
admissibility caps each of them by the product of the two excesses.  The two
statements meet in one inequality (`Gtz.leverageExcess_floor_of_admissibleRow`):

  **`1 - t_a < (1 + 2 t_a) * (l_a - 1)`** ,   equivalently   `l_a > (2 + t_a)/(1 + 2 t_a)` .

The proof is three lines of bookkeeping over the landed
`Gtz.parseval_probe_form` and `Gtz.total_weighted_excess`, with the pair minors
spent one at a time.  Nothing about ties, dominators or determinants enters, so
the floor holds at every weighted design of rank three and every size at least
two.

## Why it is worth having

`Gtz.one_lt_leverage_of_admissiblePair` promotes heaviness ACROSS an admissible
pair, but it needs a heavy atom to start: an admissible pair can in principle
have both excesses negative, and that lemma rules it out only when one side is
already known.  The row floor needs no seed.  It hands back
`Gtz.one_lt_leverage_of_admissibleRow` outright, because `1 - t_a` is positive
at every size at least two, and with it the strict heaviness half of branch B
becomes a CONSEQUENCE of the admissibility half rather than a second hypothesis
(`Gtz.branchB_of_forall_admissible`).

The floor is also quantitative and it bites hardest at small weight: as
`t_a -> 0` it forces `l_a > 2`, while at `t_a = 1/6` it gives `l_a > 13/8`.

[MEASURED before proving.  Over 20,000 random rank-three designs of size six the
slack `(1 + 2 t_a)(l_a - 1) - (1 - t_a)` never fell below `0.2199` at an atom
whose whole row is admissible, and never below `0.5678` at a design all of whose
fifteen pairs are admissible.  At the `(5,3)` diamond the slacks are
`0.6, 2.35, 2.35, 2.35, 2.35`.]

## What this module does NOT do

It does not empty branch B at `(6,3)`.  Two measurements bound what a successor
may assume.  First, **branch B is NOT empty at size five**: the diamond
`Gtz.diamondTieDesign` has leverages `(2, 13/4, 13/4, 13/4, 13/4)` and pair
minors `0.75, 2.0, 4.5`, all positive, and it is a tie.  So no size-blind
argument can empty branch B, exactly as for the hinge itself.  Second, at size
six the emptiness looks true but not uniformly: minimising `max_T tripleGapDet`
over branch-B designs under a weight floor `tau` returns `+2.09e-2` at
`tau = 5e-2`, `+1.65e-3` at `tau = 1e-2` and `+1.25e-4` at `tau = 1e-3`, the
minimiser carrying four active triples each time.  The infimum over all designs
is therefore zero, approached as two weights collapse and the design degenerates
onto a size-five branch-B tie.  A certificate must consume the weights.
-/
import Gtz.Wave.PairMinorBudget
import Gtz.Wave.KOneAnchor
import Gtz.Wave.CornerAdmissibleGateway

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. Parseval read at an atom -/

/-- **PARSEVAL AT AN ATOM.**  The weighted squared readings of one atom by the
whole design total that atom's own leverage. -/
theorem parseval_atom_row (D : WeightedDesign m 3) (a : Fin m) :
    ∑ c, D.weight c * (D.atom c ⬝ᵥ D.atom a) ^ 2 = leverageOf (D.atom a) := by
  rw [parseval_probe_form D (D.atom a), dotProduct_self_eq_leverage]

/-- The same total with the atom's own term removed. -/
theorem atomRow_sum_erase (D : WeightedDesign m 3) (a : Fin m) :
    ∑ c ∈ Finset.univ.erase a, D.weight c * (D.atom c ⬝ᵥ D.atom a) ^ 2
      = leverageOf (D.atom a) - D.weight a * leverageOf (D.atom a) ^ 2 := by
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun c => D.weight c * (D.atom c ⬝ᵥ D.atom a) ^ 2) (Finset.mem_univ a)
  rw [parseval_atom_row D a] at hsplit
  have hdiag : D.weight a * (D.atom a ⬝ᵥ D.atom a) ^ 2
      = D.weight a * leverageOf (D.atom a) ^ 2 := by
    rw [dotProduct_self_eq_leverage]
  rw [hdiag] at hsplit
  linarith

/-- The weighted excess of the design, with one atom's term removed. -/
theorem weightedExcess_sum_erase (D : WeightedDesign m 3) (a : Fin m) :
    ∑ c ∈ Finset.univ.erase a, D.weight c * (leverageOf (D.atom c) - 1)
      = 2 - D.weight a * (leverageOf (D.atom a) - 1) := by
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun c => D.weight c * (leverageOf (D.atom c) - 1)) (Finset.mem_univ a)
  rw [total_weighted_excess D] at hsplit
  linarith

/-! ## 2. The floor -/

/-- **THE ADMISSIBLE ROW FORCES A LEVERAGE FLOOR.**  If every pair through `a`
is admissible then the excess of `a` clears `(1 - t_a)/(1 + 2 t_a)`.

Parseval at `g_a` supplies the exact total of the squared readings, each pair
minor caps one reading by the product of the two excesses, and the weighted
excess of the design is exactly two.  No tie, no dominator, no determinant. -/
theorem leverageExcess_floor_of_admissibleRow (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (a : Fin m) (hrow : ∀ c, c ≠ a → AdmissiblePair (D.atom a) (D.atom c)) :
    1 - D.weight a < (1 + 2 * D.weight a) * (leverageOf (D.atom a) - 1) := by
  classical
  have hne : (Finset.univ.erase a).Nonempty := by
    have hcard : 1 < Fintype.card (Fin m) := by rw [Fintype.card_fin]; omega
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card hcard a
    exact ⟨b, Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩⟩
  -- each reading is capped by the product of the two excesses
  have hterm : ∀ c ∈ Finset.univ.erase a,
      D.weight c * (D.atom c ⬝ᵥ D.atom a) ^ 2
        < (leverageOf (D.atom a) - 1) * (D.weight c * (leverageOf (D.atom c) - 1)) := by
    intro c hc
    have hcne : c ≠ a := Finset.ne_of_mem_erase hc
    have hadm := hrow c hcne
    rw [AdmissiblePair, pairGapMinor] at hadm
    have hcomm : (D.atom c ⬝ᵥ D.atom a) ^ 2 = (D.atom a ⬝ᵥ D.atom c) ^ 2 := by
      rw [dotProduct_comm]
    have hw := D.weight_pos c
    rw [hcomm]
    nlinarith [hadm, hw]
  have hsum := Finset.sum_lt_sum_of_nonempty hne hterm
  rw [atomRow_sum_erase D a, ← Finset.mul_sum, weightedExcess_sum_erase D a] at hsum
  have hlev : leverageOf (D.atom a) = 1 + (leverageOf (D.atom a) - 1) := by ring
  nlinarith [hsum]

/-- **THE FLOOR IN LEVERAGE FORM.** -/
theorem leverage_floor_of_admissibleRow (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (a : Fin m) (hrow : ∀ c, c ≠ a → AdmissiblePair (D.atom a) (D.atom c)) :
    (2 + D.weight a) / (1 + 2 * D.weight a) < leverageOf (D.atom a) := by
  have hfloor := leverageExcess_floor_of_admissibleRow D hm a hrow
  have hden : (0 : ℝ) < 1 + 2 * D.weight a := by
    have := D.weight_pos a; linarith
  rw [div_lt_iff₀ hden]
  linarith

/-- **AN ADMISSIBLE ROW NEEDS NO SEED.**  The landed
`Gtz.one_lt_leverage_of_admissiblePair` promotes heaviness across one admissible
pair but must be handed a heavy atom.  A whole admissible row supplies it. -/
theorem one_lt_leverage_of_admissibleRow (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (a : Fin m) (hrow : ∀ c, c ≠ a → AdmissiblePair (D.atom a) (D.atom c)) :
    1 < leverageOf (D.atom a) := by
  have hfloor := leverageExcess_floor_of_admissibleRow D hm a hrow
  have hlt : D.weight a < 1 := weight_lt_one D hm a
  have hpos : (0 : ℝ) < 1 + 2 * D.weight a := by
    have := D.weight_pos a; linarith
  nlinarith [hfloor, hlt, hpos]

/-! ## 3. Branch B -/

/-- **BRANCH B IS ONE HYPOTHESIS, NOT TWO.**  A design all of whose pairs are
admissible has every atom strictly heavy, so the heaviness half of branch B is
a consequence of the admissibility half. -/
theorem branchB_of_forall_admissible (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (hall : ∀ a c : Fin m, c ≠ a → AdmissiblePair (D.atom a) (D.atom c)) :
    ∀ a : Fin m, 1 < leverageOf (D.atom a) :=
  fun a => one_lt_leverage_of_admissibleRow D hm a (fun c hc => hall a c hc)

/-- **THE FLOOR AT EVERY ATOM OF A BRANCH-B DESIGN.** -/
theorem branchB_leverage_floor (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (hall : ∀ a c : Fin m, c ≠ a → AdmissiblePair (D.atom a) (D.atom c)) :
    ∀ a : Fin m, 1 - D.weight a < (1 + 2 * D.weight a) * (leverageOf (D.atom a) - 1) :=
  fun a => leverageExcess_floor_of_admissibleRow D hm a (fun c hc => hall a c hc)

/-- **THE FLOOR AT SIX POINTS.**  Some atom carries weight at most one sixth, and
there the floor reads `l_a > 13/8`. -/
theorem exists_leverage_gt_thirteen_eighths_of_forall_admissible (D : WeightedDesign 6 3)
    (hall : ∀ a c : Fin 6, c ≠ a → AdmissiblePair (D.atom a) (D.atom c)) :
    ∃ a : Fin 6, 13 / 8 < leverageOf (D.atom a) := by
  classical
  obtain ⟨a, -, hmin⟩ : ∃ a ∈ Finset.univ, ∀ b ∈ Finset.univ, D.weight a ≤ D.weight b :=
    Finset.exists_min_image Finset.univ D.weight ⟨0, Finset.mem_univ 0⟩
  refine ⟨a, ?_⟩
  have hsix : D.weight a ≤ 1 / 6 := by
    have hsum : ∑ b, D.weight b = 1 := D.weight_sum_one
    have hle : ∑ _b : Fin 6, D.weight a ≤ ∑ b, D.weight b :=
      Finset.sum_le_sum fun b _ => hmin b (Finset.mem_univ b)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hsum] at hle
    simp only [nsmul_eq_mul] at hle
    norm_num at hle
    linarith
  have hfloor := branchB_leverage_floor D (by norm_num) hall a
  have hpos := D.weight_pos a
  nlinarith [hfloor, hsix, hpos]

end Gtz
