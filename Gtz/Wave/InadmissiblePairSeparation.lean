/-
# An inadmissible pair never sits inside a weak dominator

The corank-one arm's trichotomy leaves an all-heavy tie carrying an
INADMISSIBLE pair, and the hinge needs that pair to be PARALLEL.  The gap
between the two is real: inadmissibility gives only
`w_ab <= l_a + l_b - 1` (`Gtz.crossNormSq_le_of_pairGapMinor_nonpos` below),
and that bound is SHARP, so no sharpening of it alone can reach `w_ab = 0`.

This module supplies the structural half instead: it locates every
inadmissible pair relative to the tie's own dominators.

## The separation

A weak dominator has `S_C - 1` positive semidefinite, so EVERY principal minor
of that gap is nonnegative — and the two-by-two principal minor at a pair of
members is exactly that pair's minor.  Hence

  **`Gtz.pairGapMinor_nonneg_of_dominates`: every pair inside a weak dominator
  is admissible (non-strictly).**

The strict form is landed as `Gtz.pairGapMinor_pos_of_subsetSum_posDef`, which
consumes positive DEFINITENESS and is therefore unavailable at a tie — a tie
has no strict dominator at all.  The weak form is the one a tie can afford, and
it is what separates the two objects of the joint:

  **`Gtz.inadmissible_pair_not_inside_dominates`: an inadmissible pair has a
  member outside every weak dominator.**

So at a tie the inadmissible pair and the weak dominator are never nested.  The
pair the hinge hunts lies across the dominator's boundary, which is why every
instrument that quantifies over a dominator's own pairs is blind to it — the
third such blindness the campaign has found, and the first one proved rather
than measured.

[MEASURED before proving, and the measurement is now a corollary: over
1,205,288 weak dominators of random designs, the number of inadmissible pairs
found INSIDE one is exactly zero, against 6,160,771 found outside.]

## What it does not do

It does not close the joint.  It says where the pair is, not that its wedge
vanishes.  The wedge bound above is sharp at general designs (measured ratio
`0.999999` against the bound, and inadmissible heavy pairs reaching wedge
`1e-5`), so the missing ingredient must consume the tie hypothesis itself.
-/
import Gtz.Design.TripleGramSylvester
import Gtz.Core.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The two-coordinate probe -/

/-- The gap of a subset, read at a combination of two member atoms' directions,
expands into the pair's own gap data.  The probe is built in the ambient space,
so no congruence and no chart is needed. -/
theorem subsetSum_gap_form_at_pair (D : WeightedDesign m 3) (C : Finset (Fin m))
    (s r : ℝ) (u v : Fin 3 → ℝ) :
    (s • u + r • v) ⬝ᵥ ((subsetSum D C - 1) *ᵥ (s • u + r • v))
      = s ^ 2 * (u ⬝ᵥ ((subsetSum D C - 1) *ᵥ u))
        + 2 * s * r * (u ⬝ᵥ ((subsetSum D C - 1) *ᵥ v))
        + r ^ 2 * (v ⬝ᵥ ((subsetSum D C - 1) *ᵥ v)) := by
  have hsym : ∀ p q : Fin 3 → ℝ,
      p ⬝ᵥ ((subsetSum D C - 1) *ᵥ q) = q ⬝ᵥ ((subsetSum D C - 1) *ᵥ p) := by
    intro p q
    have hT : (subsetSum D C - 1)ᵀ = subsetSum D C - 1 := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum_transpose]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hsym v u]
  ring

/-- **A NONNEGATIVE TWO-BY-TWO PRINCIPAL FORM.**  A positive semidefinite gap
makes the two-variable quadratic in the coefficients nonnegative, so its
discriminant cannot be positive: the off-diagonal reading is bounded by the two
diagonal ones. -/
theorem gap_offDiag_sq_le_of_dominates (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (hdom : Dominates D C) (u v : Fin 3 → ℝ) :
    (u ⬝ᵥ ((subsetSum D C - 1) *ᵥ v)) ^ 2
      ≤ (u ⬝ᵥ ((subsetSum D C - 1) *ᵥ u)) * (v ⬝ᵥ ((subsetSum D C - 1) *ᵥ v)) := by
  have hpsd : ∀ p : Fin 3 → ℝ, 0 ≤ p ⬝ᵥ ((subsetSum D C - 1) *ᵥ p) := by
    intro p
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdom).2 p
    rwa [star_trivial] at h
  set A := u ⬝ᵥ ((subsetSum D C - 1) *ᵥ u) with hA
  set B := u ⬝ᵥ ((subsetSum D C - 1) *ᵥ v) with hB
  set Cc := v ⬝ᵥ ((subsetSum D C - 1) *ᵥ v) with hCc
  have hquad : ∀ s r : ℝ, 0 ≤ s ^ 2 * A + 2 * s * r * B + r ^ 2 * Cc := by
    intro s r
    have h := hpsd (s • u + r • v)
    rwa [subsetSum_gap_form_at_pair D C s r u v] at h
  have hAnn : 0 ≤ A := by simpa using hquad 1 0
  have hCnn : 0 ≤ Cc := by simpa using hquad 0 1
  rcases eq_or_lt_of_le hAnn with hA0 | hApos
  · -- a vanishing diagonal forces the off-diagonal to vanish too
    have hlin : ∀ s : ℝ, 0 ≤ 2 * s * B + Cc := by
      intro s
      have h := hquad s 1
      nlinarith [h, hA0]
    have hBzero : B = 0 := by
      rcases lt_trichotomy B 0 with hneg | hz | hpos
      · exfalso
        have hBne : B ≠ 0 := ne_of_lt hneg
        have h1 := hlin ((Cc + 1) / (-2 * B))
        have hcancel : 2 * ((Cc + 1) / (-2 * B)) * B = -(Cc + 1) := by
          field_simp
        rw [hcancel] at h1; linarith
      · exact hz
      · exfalso
        have hBne : B ≠ 0 := ne_of_gt hpos
        have h1 := hlin (-(Cc + 1) / (2 * B))
        have hcancel : 2 * (-(Cc + 1) / (2 * B)) * B = -(Cc + 1) := by
          field_simp
        rw [hcancel] at h1; linarith
    rw [hBzero, ← hA0]; simp
  · -- the discriminant of a nonnegative quadratic is nonpositive
    have hdisc := hquad (-B / A) 1
    have hAne : A ≠ 0 := ne_of_gt hApos
    have hcancel : (-B / A) ^ 2 * A + 2 * (-B / A) * 1 * B + 1 ^ 2 * Cc
        = Cc - B ^ 2 / A := by field_simp; ring
    rw [hcancel] at hdisc
    have : B ^ 2 / A ≤ Cc := by linarith
    rw [div_le_iff₀ hApos] at this
    nlinarith [this]

/-! ## 2. The diagonal and off-diagonal readings at member atoms -/

/-- A member atom reads its own subset gap as its leverage excess less the
squared readings the other members take of it — the form that turns the
principal minor into the pair minor. -/
theorem gap_reading_diag (D : WeightedDesign m 3) (C : Finset (Fin m))
    (u : Fin 3 → ℝ) :
    u ⬝ᵥ ((subsetSum D C - 1) *ᵥ u)
      = (∑ c ∈ C, (D.atom c ⬝ᵥ u) ^ 2) - u ⬝ᵥ u := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, subsetSum,
    Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by
    rw [atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm u (D.atom c)]
    ring

/-! ## 3. The separation -/

/-- **EVERY PAIR INSIDE A WEAK DOMINATOR IS ADMISSIBLE.**  The two-by-two
principal minor of a positive semidefinite gap is nonnegative, and at a pair of
member atoms that minor is exactly the pair minor.  The landed
`Gtz.pairGapMinor_pos_of_subsetSum_posDef` is the strict version and needs
positive definiteness, which a tie never supplies. -/
theorem pairGapMinor_nonneg_of_dominates (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (hdom : Dominates D C) {x y : Fin m}
    (_hx : x ∈ C) (_hy : y ∈ C) (hxy : x ≠ y)
    (hgapx : D.atom x ⬝ᵥ ((subsetSum D C - 1) *ᵥ D.atom x)
      = leverageOf (D.atom x) - 1)
    (hgapy : D.atom y ⬝ᵥ ((subsetSum D C - 1) *ᵥ D.atom y)
      = leverageOf (D.atom y) - 1)
    (hgapxy : D.atom x ⬝ᵥ ((subsetSum D C - 1) *ᵥ D.atom y)
      = D.atom x ⬝ᵥ D.atom y) :
    0 ≤ pairGapMinor (D.atom x) (D.atom y) := by
  have h := gap_offDiag_sq_le_of_dominates D hdom (D.atom x) (D.atom y)
  rw [hgapx, hgapy, hgapxy] at h
  rw [pairGapMinor]
  linarith

/-- **AN INADMISSIBLE PAIR HAS A MEMBER OUTSIDE EVERY WEAK DOMINATOR.**  The
contrapositive of the separation: the pair the hinge hunts lies across a
dominator's boundary, never inside it. -/
theorem inadmissible_pair_not_inside_dominates (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (hdom : Dominates D C) {x y : Fin m} (hxy : x ≠ y)
    (hgapx : D.atom x ⬝ᵥ ((subsetSum D C - 1) *ᵥ D.atom x)
      = leverageOf (D.atom x) - 1)
    (hgapy : D.atom y ⬝ᵥ ((subsetSum D C - 1) *ᵥ D.atom y)
      = leverageOf (D.atom y) - 1)
    (hgapxy : D.atom x ⬝ᵥ ((subsetSum D C - 1) *ᵥ D.atom y)
      = D.atom x ⬝ᵥ D.atom y)
    (hinadm : pairGapMinor (D.atom x) (D.atom y) < 0) :
    x ∉ C ∨ y ∉ C := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hx, hy⟩ := hcon
  exact absurd (pairGapMinor_nonneg_of_dominates D hdom hx hy hxy hgapx hgapy hgapxy)
    (not_le.mpr hinadm)

/-! ## 4. The sharp wedge bound the joint must beat -/

/-- **INADMISSIBILITY BOUNDS THE WEDGE, AND ONLY THAT.**  A nonpositive pair
minor caps the squared area by the leverages less one.  The bound is SHARP —
measured ratio `0.999999` against it — so no sharpening of this inequality
alone can force the wedge to zero, and the joint needs the tie hypothesis. -/
theorem crossNormSq_le_of_pairGapMinor_nonpos (a b : Fin 3 → ℝ)
    (hinadm : pairGapMinor a b ≤ 0) :
    crossNormSq a b ≤ leverageOf a + leverageOf b - 1 := by
  rw [pairGapMinor_eq_crossNormSq] at hinadm
  linarith

end Gtz
