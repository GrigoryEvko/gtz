/-
# The wedge mass of one atom, and the pair minor mass of one atom

The campaign carries two conservation laws in the hinge's currency: the weighted
wedges of a design total six over ordered pairs, and the weighted pair minors
total one.  Both are AGGREGATES.  This module resolves both ATOM BY ATOM, and
the per-atom laws are strictly more information — the aggregates are their
weighted averages.

## The two laws

For EVERY atom `x` of EVERY weighted design, with no hypothesis at all:

  **`Σ_c t_c · w(x,c) = 2·ℓ_x`**          (`Gtz.atomWedge_mass`)
  **`Σ_c t_c · q(x,c) = ℓ_x − 2`**        (`Gtz.atomPairMinor_mass`)

where `w` is the wedge and `q` the pair minor.  Both come from one reading:
Parseval at `g_x` against itself says `Σ_c t_c⟨g_x,g_c⟩² = ℓ_x`
(`Gtz.atomReading_total`), and the trace says `Σ_c t_c ℓ_c = 3`.  Subtracting
one from three times the other gives the wedge law; shifting the leverages by
one gives the pair minor law.

Weighting by `t_x` and summing recovers the aggregates — `Σ_x t_x·2ℓ_x = 6` and
`Σ_x t_x(ℓ_x − 2) = 1` — so nothing is lost, and the per-atom form says WHERE
the mass sits.

## What the second law buys

The wedge law is a positivity statement: every summand is a squared area, the
atom's own term vanishes, and the total is `2ℓ_x`, so **no atom is parallel to
every other atom** unless it is zero (`Gtz.exists_atomWedge_pos`).

The pair minor law is sharper, because its right side CHANGES SIGN.  An atom's
own diagonal contributes `t_x(1 − 2ℓ_x)`, so the off-diagonal mass is

  `Σ_{c ≠ x} t_c·q(x,c) = (ℓ_x − 2) − t_x(1 − 2ℓ_x)` .

When that is not positive some genuine pair through `x` has non-positive minor —
an INADMISSIBLE PAIR (`Gtz.exists_inadmissible_of_leverage_small`).  The
condition is a single polynomial inequality in the atom's own leverage and
weight,

  `ℓ_x·(1 + 2·t_x) ≤ 2 + t_x` ,

which at small weight is just `ℓ_x ≤ 2`.  So **an atom whose leverage does not
clear that threshold is inadmissible against something**, at every size and with
no tie hypothesis.

That is the shape the corank-one arm's stated target wants — "every `(6,3)` tie
carries an inadmissible pair" — reduced, for the atoms it covers, to a leverage
threshold.

[MEASURED at sizes 4 through 8: both laws hold at residual `1e-13` or better
over 300 designs each, and the inadmissibility consequence fired 4512 times at
`(6,3)` with zero violations.]
-/
import Gtz.Wave.KTwoAxisWedgeBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. Parseval at one atom -/

/-- **PARSEVAL AT ONE ATOM.**  The weighted squared readings of an atom against
the whole design total that atom's leverage. -/
theorem atomReading_total (D : WeightedDesign m 3) (x : Fin m) :
    ∑ c, D.weight c * atomPairing D c x ^ 2 = leverageOf (D.atom x) := by
  have h := parseval_bilinear D (D.atom x) (D.atom x)
  rw [dotProduct_self_eq_leverage] at h
  rw [← h]
  exact Finset.sum_congr rfl fun c _ => by rw [atomPairing]; ring

/-! ## 2. The wedge mass of one atom -/

/-- **THE WEDGE MASS OF ONE ATOM IS TWICE ITS LEVERAGE.**  Every atom, every
design, no hypothesis.  The trace of Parseval, three times, less its reading at
the atom. -/
theorem atomWedge_mass (D : WeightedDesign m 3) (x : Fin m) :
    ∑ c, D.weight c * crossNormSq (D.atom x) (D.atom c)
      = 2 * leverageOf (D.atom x) := by
  have hlev : ∑ c, D.weight c * leverageOf (D.atom c) = 3 := sum_weighted_leverage D
  have hax := atomReading_total D x
  have hsplit : ∑ c, D.weight c * crossNormSq (D.atom x) (D.atom c)
      = leverageOf (D.atom x) * (∑ c, D.weight c * leverageOf (D.atom c))
        - ∑ c, D.weight c * atomPairing D c x ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [crossNormSq_eq_leverage_mul_sub_sq, atomPairing, dotProduct_comm]
    ring
  rw [hsplit, hlev, hax]; ring

/-- **NO ATOM IS PARALLEL TO EVERYTHING.**  Unless the atom is degenerate, its
wedge mass is positive, so some atom carries a positive share. -/
theorem exists_atomWedge_pos (D : WeightedDesign m 3) {x : Fin m}
    (hlev : 0 < leverageOf (D.atom x)) :
    ∃ c, 0 < crossNormSq (D.atom x) (D.atom c) := by
  by_contra hcon
  push_neg at hcon
  have hle : ∑ c, D.weight c * crossNormSq (D.atom x) (D.atom c) ≤ 0 :=
    Finset.sum_nonpos fun c _ =>
      mul_nonpos_of_nonneg_of_nonpos (D.weight_pos c).le (hcon c)
  rw [atomWedge_mass D x] at hle
  linarith

/-! ## 3. The pair minor mass of one atom -/

/-- **THE PAIR MINOR MASS OF ONE ATOM IS ITS LEVERAGE LESS TWO.**  The wedge law
with the leverages shifted by one.  Its right side changes sign, which is what
makes it a producer rather than a positivity statement. -/
theorem atomPairMinor_mass (D : WeightedDesign m 3) (x : Fin m) :
    ∑ c, D.weight c * pairGapMinor (D.atom x) (D.atom c)
      = leverageOf (D.atom x) - 2 := by
  have hlev : ∑ c, D.weight c * leverageOf (D.atom c) = 3 := sum_weighted_leverage D
  have hone : ∑ c, D.weight c = 1 := D.weight_sum_one
  have hax := atomReading_total D x
  have hsplit : ∑ c, D.weight c * pairGapMinor (D.atom x) (D.atom c)
      = (leverageOf (D.atom x) - 1) * (∑ c, D.weight c * leverageOf (D.atom c))
        - (leverageOf (D.atom x) - 1) * (∑ c, D.weight c)
        - ∑ c, D.weight c * atomPairing D c x ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [pairGapMinor, atomPairing, dotProduct_comm]
    ring
  rw [hsplit, hlev, hone, hax]; ring

/-- The diagonal term of the pair minor mass, in closed form. -/
theorem pairGapMinor_self_eq (D : WeightedDesign m 3) (x : Fin m) :
    pairGapMinor (D.atom x) (D.atom x) = 1 - 2 * leverageOf (D.atom x) := by
  rw [pairGapMinor, dotProduct_self_eq_leverage]; ring

/-- **THE OFF-DIAGONAL PAIR MINOR MASS.**  The atom's own term removed. -/
theorem atomPairMinor_offDiag_mass (D : WeightedDesign m 3) (x : Fin m) :
    ∑ c ∈ Finset.univ.erase x, D.weight c * pairGapMinor (D.atom x) (D.atom c)
      = (leverageOf (D.atom x) - 2)
        - D.weight x * (1 - 2 * leverageOf (D.atom x)) := by
  have hall := atomPairMinor_mass D x
  have hsum := Finset.sum_erase_add Finset.univ
    (fun c => D.weight c * pairGapMinor (D.atom x) (D.atom c)) (Finset.mem_univ x)
  rw [pairGapMinor_self_eq D x] at hsum
  linarith [hall, hsum]

/-! ## 4. The inadmissible pair -/

/-- **A LEVERAGE THRESHOLD FORCES AN INADMISSIBLE PAIR.**  When the atom's own
leverage fails to clear `(2 + t_x)/(1 + 2·t_x)` — at small weight, simply two —
its off-diagonal pair minor mass is not positive, so some genuine pair through
it has non-positive minor.

No tie hypothesis, and the only size cost is that a second atom exists. -/
theorem exists_inadmissible_of_leverage_small (D : WeightedDesign m 3) (x : Fin m)
    (hm : 2 ≤ m)
    (hthr : leverageOf (D.atom x) * (1 + 2 * D.weight x) ≤ 2 + D.weight x) :
    ∃ c, c ≠ x ∧ pairGapMinor (D.atom x) (D.atom c) ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  have hpos : ∀ c ∈ Finset.univ.erase x,
      0 < D.weight c * pairGapMinor (D.atom x) (D.atom c) := by
    intro c hc
    exact mul_pos (D.weight_pos c) (hcon c (Finset.ne_of_mem_erase hc))
  have hne : (Finset.univ.erase x).Nonempty := by
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card
      (by rw [Fintype.card_fin]; omega : 1 < Fintype.card (Fin m)) x
    exact ⟨b, Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩⟩
  have hmass := atomPairMinor_offDiag_mass D x
  have hle : (leverageOf (D.atom x) - 2)
      - D.weight x * (1 - 2 * leverageOf (D.atom x)) ≤ 0 := by nlinarith [hthr]
  have hsum := Finset.sum_pos hpos hne
  rw [hmass] at hsum
  linarith

end Gtz
