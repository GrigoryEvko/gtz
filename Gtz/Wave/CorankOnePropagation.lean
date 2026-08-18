/-
# The exchange dichotomy: every swap lands on a dominator or is refused with a
# strict margin

The exchange law of `Gtz.Wave.CorankOneExchange` prices every one-atom swap of
a corank-one weak dominator at reading at least one.  This module lands the
structure of the equality case:

* reading equal to one is EXACTLY the swapped triple's weak domination
  (`Gtz.exchange_reading_eq_one_iff_swap_dominates`), and
* at equality the swapped dominator's null vector is explicit — the solved
  vector `anchor⁻¹ g_e` (`Gtz.swapGap_null_at_solved_of_reading_eq_one`).

So at a tie the exchange moves have a dichotomy: a swap either lands on
another weak dominator, with a new null direction handed over in closed form,
or it is refused with reading strictly above one.  The weak dominators of a
tie form an exchange structure in which corank-one data PROPAGATES.

Exact calibration (MEASURED, rational arithmetic in the Laplacian frame):
at the `(5,3)` diamond with dominator `{e0,e1,e2}`, the readings against the
two outside atoms are `(1, 1, 11/6)` and `(1, 11/6, 1)` — each swap of
reading one lands on another spanning tree, each reading `11/6` is a
non-tree.  At the `(6,3)` split diamond the same table extends by the split
copy at readings `(1, 11/6, 11/6)`.  The tight cases are the dominator
matroid, not only the parallel pair: equality does NOT certify parallelism.
That measurement is the exact reason the assembly needs stress-freeness — the
split diamond satisfies every exchange constraint and is not stress-free.
-/
import Gtz.Wave.CorankOneExchange

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The equality case hands over the next null vector -/

/-- **The solved vector kills the swapped gap at equality.**  For a positive
definite anchor and reading exactly one, the downdated matrix annihilates the
solved vector `anchor⁻¹ g`. -/
theorem sub_vecMulVec_mulVec_solved_eq_zero {k : ℕ}
    {anchor : Matrix (Fin k) (Fin k) ℝ} (hanchor : anchor.PosDef)
    {g : Fin k → ℝ} (hreading : g ⬝ᵥ (anchor⁻¹ *ᵥ g) = 1) :
    (anchor - Matrix.vecMulVec g g) *ᵥ (anchor⁻¹ *ᵥ g) = 0 := by
  have hdet : IsUnit anchor.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hanchor.det_pos)
  rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec, vecMulVec_mulVec_eq, hreading, one_smul, sub_self]

/-- The solved vector is nonzero when the atom is nonzero. -/
theorem solved_ne_zero_of_reading_eq_one {k : ℕ}
    {anchor : Matrix (Fin k) (Fin k) ℝ} {g : Fin k → ℝ}
    (hreading : g ⬝ᵥ (anchor⁻¹ *ᵥ g) = 1) : anchor⁻¹ *ᵥ g ≠ 0 := by
  intro hzero
  rw [hzero, dotProduct_zero] at hreading
  norm_num at hreading

/-! ## 2. The dichotomy -/

/-- **THE EXCHANGE DICHOTOMY.**  At a tie, a one-atom swap of a corank-one
weak dominator reads exactly one precisely when the swapped triple is itself
a weak dominator.  Reading strictly above one is exactly strict refusal. -/
theorem exchange_reading_eq_one_iff_swap_dominates (D : WeightedDesign m 3)
    (htie : IsTie D) (C : Finset (Fin m)) (hcard : C.card = 3)
    (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D C nullDir) {e d : Fin m} (he : e ∈ C) (hd : d ∉ C)
    (hread : D.atom d ⬝ᵥ nullDir ≠ 0) :
    D.atom e ⬝ᵥ ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom e) = 1
      ↔ Dominates D (insert d (C.erase e)) := by
  have hanchor := exchangeAnchor_posDef D C hdominates hline hread
  have hlaw := one_le_exchange_reading_of_isTie D htie C hcard hdominates
    hline he hd hread
  constructor
  · intro hone
    show (subsetSum D (insert d (C.erase e)) - 1).PosSemidef
    rw [subsetSum_swap_sub_one D C he hd]
    exact (posSemidef_sub_vecMulVec_iff _ hanchor _).mpr (le_of_eq hone)
  · intro hdom
    have hle : D.atom e ⬝ᵥ ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom e) ≤ 1 := by
      have hpsd : (exchangeAnchor D C d
          - Matrix.vecMulVec (D.atom e) (D.atom e)).PosSemidef := by
        rw [← subsetSum_swap_sub_one D C he hd]
        exact hdom
      exact (posSemidef_sub_vecMulVec_iff _ hanchor _).mp hpsd
    linarith

/-- **THE PROPAGATION LAW.**  At a tie, a swap of reading one lands on a weak
dominator whose gap annihilates the solved vector `anchor⁻¹ g_e` — the next
null direction, in closed form.  Corank-one structure moves along the
equality swaps. -/
theorem swap_dominates_with_null_of_reading_eq_one (D : WeightedDesign m 3)
    (htie : IsTie D) (C : Finset (Fin m)) (hcard : C.card = 3)
    (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D C nullDir) {e d : Fin m} (he : e ∈ C) (hd : d ∉ C)
    (hread : D.atom d ⬝ᵥ nullDir ≠ 0)
    (hone : D.atom e ⬝ᵥ ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom e) = 1) :
    Dominates D (insert d (C.erase e))
      ∧ (exchangeAnchor D C d)⁻¹ *ᵥ D.atom e ≠ 0
      ∧ (subsetSum D (insert d (C.erase e)) - 1)
          *ᵥ ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom e) = 0 := by
  have hanchor := exchangeAnchor_posDef D C hdominates hline hread
  refine ⟨(exchange_reading_eq_one_iff_swap_dominates D htie C hcard
      hdominates hline he hd hread).mp hone,
    solved_ne_zero_of_reading_eq_one hone, ?_⟩
  rw [subsetSum_swap_sub_one D C he hd]
  exact sub_vecMulVec_mulVec_solved_eq_zero hanchor hone

end Gtz
