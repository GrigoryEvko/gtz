import Gtz.Wave.SignBlindCeiling
import Gtz.Wave.HeavySetEnergyCell

/-!
# The cell lattice, the composed cover, and the residue that survives it

The campaign has landed several sufficient cells for the third Sylvester minor of
a triple, and each one was measured against its own baseline.  Nobody composed
them, so the union's reach and the union's residue were both unknown.  This file
composes them.

**The lattice has one top inside the sign-blind class.**
`Gtz.signFreeMargin_pos_iff_evenPart_sq` makes the polynomial pair
`0 < E` and `4 (uvw)^2 < E^2` equivalent to a positive margin, and
`Gtz.evenPart_sq_iff_both_signs` makes that pair the two-sided determinant
condition.  So every cell that declines to read the sign of the triple product
factors through it.  Three do: the quarter slack
(`Gtz.evenPart_sq_of_quarterSlack`, landed), the sum cell at threshold three
quarters, and the aggregate cell, whose passage `Gtz.evenPart_sq_of_aggregate` is
new here.  All three are therefore REDUNDANT as contributors to any cover that
already carries the maximal cell.

**The sum cell and the aggregate cell are incomparable.**  Both witnesses are
explicit rationals.  `Gtz.exists_sum_beyond_aggregate` puts the whole pairing
energy on the pairing whose surplus is smallest, where the aggregate cell's
maximum-surplus factor overcharges it.  `Gtz.exists_aggregate_beyond_sum` puts
the energy on the pairing whose surplus is largest, where the sum cell's fixed
three-quarters threshold is the binding one.

**The composed cover.**  `Gtz.TripleCover` is the disjunction of the maximal
sign-blind cell with the sign-aware cell.  Both halves demand a positive even
part, so the cover reads as `0 < E` together with either a non-negative triple
product or the sign-blind square condition.

**The residue halves.**  The sign-blind residue is `0 < uvw` with `E` trapped in
`(-2uvw, 2uvw]`.  The cover's residue is the same statement with the window cut
at zero: `Gtz.coverResidue_iff` proves that a triple with a positive determinant
escapes the cover exactly when `0 < uvw` and `E ≤ 0`.  So composition removes
precisely the upper half `0 < E ≤ 2uvw` of the sign-blind deficit, and
`Gtz.exists_residue_not_coverResidue` exhibits a point in that removed half.

**What the cover cannot reach, and why that answers a live question.**
`Gtz.cover_of_cross_nonpos_of_det_pos` proves the cover is complete at every
triple whose triple product is non-positive.  So a design all of whose dominating
triples are INCOHERENT is fully covered, and the measured population of such
designs is harmless rather than dangerous.  The dangerous set is the opposite
one, and `Gtz.equiangular_mem_coverResidue` shows it is not empty: at the
equiangular point the even part is `-7/540`, the cover fails at every triple, and
ten of the twenty triples dominate on the strength of the cross term alone.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The aggregate cell factors through the maximal sign-blind cell -/

/-- The aggregate hypotheses put the even part above the gap they leave. -/
theorem gap_le_evenTripleDetPart_of_aggregate (p q r u v w : ℝ) :
    p * q * r - maxSurplus p q r * tripleEnergy u v w
      ≤ evenTripleDetPart p q r u v w := by
  have hweighted : p * w ^ 2 + q * v ^ 2 + r * u ^ 2
      ≤ maxSurplus p q r * tripleEnergy u v w :=
    weighted_sq_sum_le_maxSurplus_mul_tripleEnergy p q r u v w
  rw [evenTripleDetPart]
  linarith

/-- The cross hypothesis bounds twice the triple product below the gap in square. -/
theorem four_mul_cross_sq_lt_gap_sq_of_aggregate (p q r u v w : ℝ)
    (hcross : 4 * tripleEnergy u v w ^ 3
      < 27 * (p * q * r - maxSurplus p q r * tripleEnergy u v w) ^ 2) :
    4 * (u * v * w) ^ 2 < (p * q * r - maxSurplus p q r * tripleEnergy u v w) ^ 2 := by
  have hcap : 27 * (u * v * w) ^ 2 ≤ tripleEnergy u v w ^ 3 :=
    twentySeven_mul_sq_prod_le_tripleEnergy_cube u v w
  linarith

/-- **THE AGGREGATE CELL IS SIGN BLIND, AND IT FACTORS THROUGH THE TOP.**  Its
two hypotheses give the polynomial criterion directly, with no absolute value in
the passage.  So the aggregate cell adds nothing to a cover that already carries
the maximal sign-blind cell. -/
theorem evenPart_sq_of_aggregate (p q r u v w : ℝ)
    (hgap : maxSurplus p q r * tripleEnergy u v w < p * q * r)
    (hcross : 4 * tripleEnergy u v w ^ 3
      < 27 * (p * q * r - maxSurplus p q r * tripleEnergy u v w) ^ 2) :
    0 < evenTripleDetPart p q r u v w
      ∧ 4 * (u * v * w) ^ 2 < evenTripleDetPart p q r u v w ^ 2 := by
  have hgapPos : 0 < p * q * r - maxSurplus p q r * tripleEnergy u v w := by linarith
  have hle := gap_le_evenTripleDetPart_of_aggregate p q r u v w
  have hEpos : 0 < evenTripleDetPart p q r u v w := lt_of_lt_of_le hgapPos hle
  refine ⟨hEpos, ?_⟩
  have hsq := four_mul_cross_sq_lt_gap_sq_of_aggregate p q r u v w hcross
  nlinarith [hsq, hle, hgapPos]

/-- The aggregate cell gives a positive margin. -/
theorem signFreeMargin_pos_of_aggregate (p q r u v w : ℝ)
    (hgap : maxSurplus p q r * tripleEnergy u v w < p * q * r)
    (hcross : 4 * tripleEnergy u v w ^ 3
      < 27 * (p * q * r - maxSurplus p q r * tripleEnergy u v w) ^ 2) :
    0 < signFreeMargin p q r u v w :=
  (signFreeMargin_pos_iff_evenPart_sq p q r u v w).mpr
    (evenPart_sq_of_aggregate p q r u v w hgap hcross)

/-- The sum cell factors through the top as well, by the landed passage. -/
theorem evenPart_sq_of_weightedPairEnergy_lt (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : weightedPairEnergy p q r u v w < 3 / 4 * (p * q * r)) :
    0 < evenTripleDetPart p q r u v w
      ∧ 4 * (u * v * w) ^ 2 < evenTripleDetPart p q r u v w ^ 2 :=
  (signFreeMargin_pos_iff_evenPart_sq p q r u v w).mp
    (signFreeMargin_pos_of_weightedPairEnergy_lt p q r u v w hp hq hr h)

/-! ## 2. The sum cell and the aggregate cell are incomparable

Both witnesses put the whole pairing energy on one pairing.  Which cell wins is
decided by whether that pairing's own surplus is the largest of the three, since
the aggregate cell charges every pairing at the maximum surplus while the sum
cell charges each at its own. -/

/-- **THE SUM CELL REACHES BEYOND THE AGGREGATE CELL.**  With the energy on the
pairing whose surplus is smallest, the maximum-surplus factor overcharges by the
full spread and the aggregate gap hypothesis fails outright, while the weighted
energy stays far below three quarters. -/
theorem exists_sum_beyond_aggregate :
    weightedPairEnergy 10 1 1 2 0 0 < 3 / 4 * (10 * 1 * 1)
      ∧ ¬ (maxSurplus 10 1 1 * tripleEnergy 2 0 0 < 10 * 1 * 1)
      ∧ 0 < tripleDetForm 10 1 1 2 0 0 := by
  refine ⟨by rw [weightedPairEnergy]; norm_num, ?_, by rw [tripleDetForm]; norm_num⟩
  rw [maxSurplus, tripleEnergy]
  norm_num

/-- **THE AGGREGATE CELL REACHES BEYOND THE SUM CELL.**  With the energy on the
pairing whose surplus is largest the two charges coincide, and the aggregate
cell's cross condition is far slacker than the fixed three-quarters threshold. -/
theorem exists_aggregate_beyond_sum :
    ¬ (weightedPairEnergy 1 1 10 (9/10) 0 0 < 3 / 4 * (1 * 1 * 10))
      ∧ maxSurplus 1 1 10 * tripleEnergy (9/10) 0 0 < 1 * 1 * 10
      ∧ 4 * tripleEnergy (9/10) 0 0 ^ 3
        < 27 * (1 * 1 * 10 - maxSurplus 1 1 10 * tripleEnergy (9/10) 0 0) ^ 2
      ∧ 0 < tripleDetForm 1 1 10 (9/10) 0 0 := by
  refine ⟨?_, ?_, ?_, by rw [tripleDetForm]; norm_num⟩
  · rw [weightedPairEnergy]; norm_num
  · rw [maxSurplus, tripleEnergy]; norm_num
  · rw [maxSurplus, tripleEnergy]; norm_num

/-- Both witnesses are inside the maximal cell, as the lattice requires. -/
theorem aggregate_witness_mem_top :
    0 < evenTripleDetPart 1 1 10 (9/10) 0 0
      ∧ 4 * ((9/10 : ℝ) * 0 * 0) ^ 2 < evenTripleDetPart 1 1 10 (9/10) 0 0 ^ 2 := by
  obtain ⟨_, hgap, hcross, _⟩ := exists_aggregate_beyond_sum
  exact evenPart_sq_of_aggregate 1 1 10 (9/10) 0 0 hgap hcross

theorem sum_witness_mem_top :
    0 < evenTripleDetPart 10 1 1 2 0 0
      ∧ 4 * ((2 : ℝ) * 0 * 0) ^ 2 < evenTripleDetPart 10 1 1 2 0 0 ^ 2 := by
  obtain ⟨hsum, _, _⟩ := exists_sum_beyond_aggregate
  exact evenPart_sq_of_weightedPairEnergy_lt 10 1 1 2 0 0 (by norm_num) (by norm_num)
    (by norm_num) hsum

/-! ## 3. The composed cover -/

/-- **THE COMPOSED COVER.**  The maximal sign-blind cell joined to the sign-aware
cell.  Both halves need a positive even part, so the cover splits on the sign of
the triple product and nothing else. -/
def TripleCover (p q r u v w : ℝ) : Prop :=
  0 < evenTripleDetPart p q r u v w
    ∧ (0 ≤ u * v * w ∨ 4 * (u * v * w) ^ 2 < evenTripleDetPart p q r u v w ^ 2)

theorem tripleCover_iff (p q r u v w : ℝ) :
    TripleCover p q r u v w
      ↔ 0 < evenTripleDetPart p q r u v w
        ∧ (0 ≤ u * v * w ∨ 4 * (u * v * w) ^ 2 < evenTripleDetPart p q r u v w ^ 2) :=
  Iff.rfl

theorem evenTripleDetPart_pos_of_cover (p q r u v w : ℝ) (h : TripleCover p q r u v w) :
    0 < evenTripleDetPart p q r u v w := h.1

/-- **THE COVER IS SOUND.**  Either half forces the third minor positive. -/
theorem tripleDetForm_pos_of_cover (p q r u v w : ℝ) (h : TripleCover p q r u v w) :
    0 < tripleDetForm p q r u v w := by
  obtain ⟨hE, hcase⟩ := h
  rcases hcase with hcross | hsq
  · rw [tripleDetForm_eq_evenPart_add_cross]; linarith
  · exact tripleDetForm_pos_of_evenPart_sq p q r u v w hE hsq

/-! ## 4. Every landed cell lands inside the cover -/

theorem cover_of_evenPart_sq (p q r u v w : ℝ)
    (hE : 0 < evenTripleDetPart p q r u v w)
    (hsq : 4 * (u * v * w) ^ 2 < evenTripleDetPart p q r u v w ^ 2) :
    TripleCover p q r u v w := ⟨hE, Or.inr hsq⟩

theorem cover_of_signFreeMargin_pos (p q r u v w : ℝ)
    (h : 0 < signFreeMargin p q r u v w) : TripleCover p q r u v w := by
  obtain ⟨hE, hsq⟩ := (signFreeMargin_pos_iff_evenPart_sq p q r u v w).mp h
  exact cover_of_evenPart_sq p q r u v w hE hsq

/-- The sign-aware cell's sum hypothesis is exactly a positive even part. -/
theorem cover_of_nonneg_cross (p q r u v w : ℝ)
    (hcross : 0 ≤ u * v * w)
    (hsum : r * u ^ 2 + q * v ^ 2 + p * w ^ 2 < p * q * r) :
    TripleCover p q r u v w := by
  refine ⟨?_, Or.inl hcross⟩
  rw [evenTripleDetPart]; linarith

theorem cover_of_quarterSlack (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hu : 4 * u ^ 2 < p * q) (hv : 4 * v ^ 2 < p * r) (hw : 4 * w ^ 2 < q * r) :
    TripleCover p q r u v w := by
  obtain ⟨hE, hsq⟩ := evenPart_sq_of_quarterSlack p q r u v w hp hq hr hu hv hw
  exact cover_of_evenPart_sq p q r u v w hE hsq

theorem cover_of_weightedPairEnergy_lt (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : weightedPairEnergy p q r u v w < 3 / 4 * (p * q * r)) :
    TripleCover p q r u v w := by
  obtain ⟨hE, hsq⟩ := evenPart_sq_of_weightedPairEnergy_lt p q r u v w hp hq hr h
  exact cover_of_evenPart_sq p q r u v w hE hsq

theorem cover_of_aggregate (p q r u v w : ℝ)
    (hgap : maxSurplus p q r * tripleEnergy u v w < p * q * r)
    (hcross : 4 * tripleEnergy u v w ^ 3
      < 27 * (p * q * r - maxSurplus p q r * tripleEnergy u v w) ^ 2) :
    TripleCover p q r u v w := by
  obtain ⟨hE, hsq⟩ := evenPart_sq_of_aggregate p q r u v w hgap hcross
  exact cover_of_evenPart_sq p q r u v w hE hsq

/-! ## 5. The cover reads the sign, and the sign-blind half does not

A sign-blind cell must be invariant under flipping one pairing.  The cover is
not, and that is exactly what it buys over its sign-blind half. -/

/-- **THE COVER IS NOT FLIP INVARIANT.**  At equal surpluses one and equal
pairings eleven twentieths the cover fires, and the flipped triple escapes it. -/
theorem exists_cover_not_flip_cover :
    TripleCover 1 1 1 (11/20) (11/20) (11/20)
      ∧ ¬ TripleCover 1 1 1 (11/20) (11/20) (-(11/20)) := by
  constructor
  · refine ⟨by rw [evenTripleDetPart]; norm_num, Or.inl (by norm_num)⟩
  · rintro ⟨_, hcase⟩
    rcases hcase with hcross | hsq
    · rw [show (11/20 : ℝ) * (11/20) * (-(11/20)) = -(1331/8000) by ring] at hcross
      norm_num at hcross
    · rw [evenTripleDetPart] at hsq
      norm_num at hsq

/-- The sign-blind half is flip invariant, by the landed law. -/
theorem evenPart_sq_flip_invariant (p q r u v w : ℝ) :
    (0 < evenTripleDetPart p q r u v (-w)
        ∧ 4 * (u * v * (-w)) ^ 2 < evenTripleDetPart p q r u v (-w) ^ 2)
      ↔ (0 < evenTripleDetPart p q r u v w
        ∧ 4 * (u * v * w) ^ 2 < evenTripleDetPart p q r u v w ^ 2) :=
  evenPart_sq_flip_third p q r u v w

/-! ## 6. The residue of the cover, exactly

The deliverable.  A triple with a positive determinant escapes the cover exactly
when its triple product is positive and its even part is non-positive. -/

/-- **THE COVER IS COMPLETE AT A NON-POSITIVE TRIPLE PRODUCT.**  Every dominating
triple whose triple product is non-positive is inside the cover, through the
sign-blind half. -/
theorem cover_of_cross_nonpos_of_det_pos (p q r u v w : ℝ)
    (hdet : 0 < tripleDetForm p q r u v w) (hc : u * v * w ≤ 0) :
    TripleCover p q r u v w :=
  cover_of_signFreeMargin_pos p q r u v w
    (signFreeMargin_pos_of_det_pos_of_cross_nonpos p q r u v w hdet hc)

/-- A triple that escapes the cover has a strictly positive triple product. -/
theorem cross_pos_of_det_pos_of_not_cover (p q r u v w : ℝ)
    (hdet : 0 < tripleDetForm p q r u v w) (h : ¬ TripleCover p q r u v w) :
    0 < u * v * w := by
  rcases le_or_gt (u * v * w) 0 with hle | hlt
  · exact absurd (cover_of_cross_nonpos_of_det_pos p q r u v w hdet hle) h
  · exact hlt

/-- A triple that escapes the cover has a non-positive even part. -/
theorem evenTripleDetPart_nonpos_of_det_pos_of_not_cover (p q r u v w : ℝ)
    (hdet : 0 < tripleDetForm p q r u v w) (h : ¬ TripleCover p q r u v w) :
    evenTripleDetPart p q r u v w ≤ 0 := by
  rcases le_or_gt (evenTripleDetPart p q r u v w) 0 with hle | hpos
  · exact hle
  · exact absurd ⟨hpos, Or.inl (le_of_lt (cross_pos_of_det_pos_of_not_cover p q r u v w hdet h))⟩ h

/-- **THE RESIDUE OF THE COVER, EXACTLY.**  At a dominating triple the cover
fails exactly when the triple product is positive and the even part is not. -/
theorem coverResidue_iff (p q r u v w : ℝ) (hdet : 0 < tripleDetForm p q r u v w) :
    ¬ TripleCover p q r u v w
      ↔ (0 < u * v * w ∧ evenTripleDetPart p q r u v w ≤ 0) := by
  constructor
  · intro h
    exact ⟨cross_pos_of_det_pos_of_not_cover p q r u v w hdet h,
      evenTripleDetPart_nonpos_of_det_pos_of_not_cover p q r u v w hdet h⟩
  · rintro ⟨_, hE⟩ ⟨hEpos, _⟩
    exact absurd hEpos (not_lt.mpr hE)

/-- **THE RESIDUE WITHOUT A DETERMINANT HYPOTHESIS.**  The three conditions are
independent and the determinant is recovered from them. -/
theorem coverResidue_iff_explicit (p q r u v w : ℝ) :
    (0 < tripleDetForm p q r u v w ∧ ¬ TripleCover p q r u v w)
      ↔ (0 < u * v * w
          ∧ evenTripleDetPart p q r u v w ≤ 0
          ∧ 0 < evenTripleDetPart p q r u v w + 2 * (u * v * w)) := by
  constructor
  · rintro ⟨hdet, h⟩
    obtain ⟨hc, hE⟩ := (coverResidue_iff p q r u v w hdet).mp h
    rw [tripleDetForm_eq_evenPart_add_cross] at hdet
    exact ⟨hc, hE, hdet⟩
  · rintro ⟨hc, hE, hpos⟩
    have hdet : 0 < tripleDetForm p q r u v w := by
      rw [tripleDetForm_eq_evenPart_add_cross]; exact hpos
    exact ⟨hdet, (coverResidue_iff p q r u v w hdet).mpr ⟨hc, hE⟩⟩

/-- **THE WINDOW IS EXACTLY HALVED.**  The sign-blind residue traps the even part
in `(-2uvw, 2uvw]`.  The cover's residue traps it in `(-2uvw, 0]`. -/
theorem coverResidue_window (p q r u v w : ℝ)
    (hdet : 0 < tripleDetForm p q r u v w) (h : ¬ TripleCover p q r u v w) :
    -(2 * (u * v * w)) < evenTripleDetPart p q r u v w
      ∧ evenTripleDetPart p q r u v w ≤ 0 := by
  obtain ⟨_, hE⟩ := (coverResidue_iff p q r u v w hdet).mp h
  rw [tripleDetForm_eq_evenPart_add_cross] at hdet
  exact ⟨by linarith, hE⟩

/-- **THE COVER'S RESIDUE SITS INSIDE THE SIGN-BLIND RESIDUE.** -/
theorem residue_of_coverResidue (p q r u v w : ℝ)
    (hdet : 0 < tripleDetForm p q r u v w) (h : ¬ TripleCover p q r u v w) :
    0 < tripleDetForm p q r u v w ∧ signFreeMargin p q r u v w ≤ 0 := by
  obtain ⟨hc, hE⟩ := (coverResidue_iff p q r u v w hdet).mp h
  refine ⟨hdet, ?_⟩
  rw [signFreeMargin_eq_evenPart_sub_abs, abs_of_pos hc]
  linarith

/-- **AND STRICTLY INSIDE.**  At equal surpluses one and equal pairings eleven
twentieths the sign-blind class fails while the cover fires, so the composition
removes a genuine part of the deficit. -/
theorem exists_residue_not_coverResidue :
    (0 < tripleDetForm 1 1 1 (11/20) (11/20) (11/20)
        ∧ signFreeMargin 1 1 1 (11/20) (11/20) (11/20) ≤ 0)
      ∧ TripleCover 1 1 1 (11/20) (11/20) (11/20) := by
  refine ⟨⟨by rw [tripleDetForm]; norm_num, ?_⟩, (exists_cover_not_flip_cover).1⟩
  rw [signFreeMargin_eq_evenPart_sub_abs, evenTripleDetPart,
    show (11/20 : ℝ) * (11/20) * (11/20) = 1331/8000 by ring,
    abs_of_pos (by norm_num : (0:ℝ) < 1331/8000)]
  norm_num

/-! ## 7. The cover is incomplete, with the equiangular witness -/

/-- **THE EQUIANGULAR TRIPLE ESCAPES THE COVER.**  Its even part is `-7/540`, so
neither half can fire, while its determinant is positive. -/
theorem equiangular_not_cover {t : ℝ} (ht : t ^ 2 = 1/20) :
    ¬ TripleCover (1/3) (1/3) (1/3) t t t := by
  rintro ⟨hE, _⟩
  exact absurd hE (not_lt.mpr (le_of_lt (equiangular_evenPart_neg ht)))

theorem equiangular_mem_coverResidue {t : ℝ} (ht : t ^ 2 = 1/20) (hpos : 0 < t) :
    0 < tripleDetForm (1/3) (1/3) (1/3) t t t
      ∧ ¬ TripleCover (1/3) (1/3) (1/3) t t t :=
  ⟨equiangular_tripleDetForm_pos ht hpos, equiangular_not_cover ht⟩

/-- **THE COMPOSED COVER IS PROVABLY INCOMPLETE.**  A dominating triple exists
that no landed cell reaches, so composition alone does not close the objective. -/
theorem exists_coverResidue_point :
    ∃ p q r u v w : ℝ, 0 < tripleDetForm p q r u v w ∧ ¬ TripleCover p q r u v w := by
  obtain ⟨t, hpos, ht⟩ := exists_equiangular_pairing
  exact ⟨1/3, 1/3, 1/3, t, t, t, equiangular_mem_coverResidue ht hpos⟩

theorem not_forall_cover_of_det_pos :
    ¬ (∀ p q r u v w : ℝ, 0 < tripleDetForm p q r u v w → TripleCover p q r u v w) := by
  intro h
  obtain ⟨p, q, r, u, v, w, hdet, hnot⟩ := exists_coverResidue_point
  exact hnot (h p q r u v w hdet)

/-- At the equiangular point the cover's residue window is tight from both ends,
since the even part is strictly negative and the cross term strictly carries. -/
theorem equiangular_coverResidue_window {t : ℝ} (ht : t ^ 2 = 1/20) (hpos : 0 < t) :
    -(2 * (t * t * t)) < evenTripleDetPart (1/3) (1/3) (1/3) t t t
      ∧ evenTripleDetPart (1/3) (1/3) (1/3) t t t ≤ 0 :=
  coverResidue_window (1/3) (1/3) (1/3) t t t (equiangular_tripleDetForm_pos ht hpos)
    (equiangular_not_cover ht)

/-! ## 8. The cover on atoms and on designs -/

/-- The cover read on three atoms through their leverages and pairings. -/
def AtomTripleCover (a b c : Fin 3 → ℝ) : Prop :=
  TripleCover (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
    (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c)

theorem atomTripleCover_iff (a b c : Fin 3 → ℝ) :
    AtomTripleCover a b c
      ↔ TripleCover (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
          (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c) := Iff.rfl

/-- The cover forces the third minor of the triple Gram gap. -/
theorem tripleGapDet_pos_of_atomCover (a b c : Fin 3 → ℝ) (h : AtomTripleCover a b c) :
    0 < tripleGapDet a b c := by
  rw [tripleGapDet_eq_tripleDetForm]
  exact tripleDetForm_pos_of_cover _ _ _ _ _ _ h

/-- **THE COVER ON THE TRIPLE GRAM.**  With the two lower minors supplied, the
cover closes the third and gives a strict dominator. -/
theorem tripleGram_posDef_of_atomCover (a b c : Fin 3 → ℝ)
    (ha : 1 < leverageOf a) (hab : 0 < pairGapMinor a b)
    (h : AtomTripleCover a b c) : (tripleGram a b c - 1).PosDef := by
  rw [tripleGram_posDef_iff_pairVocabulary]
  exact ⟨by linarith, hab, tripleGapDet_pos_of_atomCover a b c h⟩

/-- **THE COVER AT THE DESIGN LEVEL.**  The consumer form on three named
labels. -/
theorem subsetSum_posDef_of_atomCover {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : 1 < leverageOf (D.atom x))
    (hxyMinor : 0 < pairGapMinor (D.atom x) (D.atom y))
    (h : AtomTripleCover (D.atom x) (D.atom y) (D.atom z)) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef :=
  (subsetSum_posDef_iff_tripleGram D x y z hxy hxz hyz).mpr
    (tripleGram_posDef_of_atomCover _ _ _ hx hxyMinor h)

/-- The atom-level cover is complete at a non-positive atom triple product. -/
theorem atomCover_of_cross_nonpos_of_det_pos (a b c : Fin 3 → ℝ)
    (hdet : 0 < tripleGapDet a b c)
    (hc : (a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c) ≤ 0) : AtomTripleCover a b c := by
  rw [tripleGapDet_eq_tripleDetForm] at hdet
  exact cover_of_cross_nonpos_of_det_pos _ _ _ _ _ _ hdet hc

/-- **THE ATOM-LEVEL RESIDUE, EXACTLY.**  A dominating atom triple escapes the
cover exactly when its triple product is positive and its even part is not. -/
theorem atomCoverResidue_iff (a b c : Fin 3 → ℝ) (hdet : 0 < tripleGapDet a b c) :
    ¬ AtomTripleCover a b c
      ↔ (0 < (a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c)
          ∧ atomEvenPart a b c ≤ 0) := by
  rw [tripleGapDet_eq_tripleDetForm] at hdet
  rw [atomTripleCover_iff, coverResidue_iff _ _ _ _ _ _ hdet, atomEvenPart]

/-! ## 9. What the lattice says about the campaign's cell inventory

Three landed cells factor through the maximal sign-blind cell, so a cover that
carries the top gains nothing by carrying them.  The sign-aware cell does not
factor through it, and it is what the composition actually buys. -/

/-- **THE THREE SIGN-BLIND CELLS ARE REDUNDANT GIVEN THE TOP.**  Each implies the
maximal cell, so each implies the cover through its sign-blind half alone. -/
theorem sign_blind_cells_redundant (p q r u v w : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    ((4 * u ^ 2 < p * q ∧ 4 * v ^ 2 < p * r ∧ 4 * w ^ 2 < q * r)
        → TripleCover p q r u v w)
      ∧ (weightedPairEnergy p q r u v w < 3 / 4 * (p * q * r) → TripleCover p q r u v w)
      ∧ ((maxSurplus p q r * tripleEnergy u v w < p * q * r
            ∧ 4 * tripleEnergy u v w ^ 3
              < 27 * (p * q * r - maxSurplus p q r * tripleEnergy u v w) ^ 2)
          → TripleCover p q r u v w) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hu, hv, hw⟩; exact cover_of_quarterSlack p q r u v w hp hq hr hu hv hw
  · intro h; exact cover_of_weightedPairEnergy_lt p q r u v w hp hq hr h
  · rintro ⟨hgap, hcross⟩; exact cover_of_aggregate p q r u v w hgap hcross

/-- **THE SIGN-AWARE CELL IS NOT REDUNDANT.**  At equal surpluses one and equal
pairings eleven twentieths it fires and the whole sign-blind class does not, so
the cover strictly exceeds its own sign-blind half. -/
theorem sign_aware_cell_not_redundant :
    TripleCover 1 1 1 (11/20) (11/20) (11/20)
      ∧ ¬ (0 < evenTripleDetPart 1 1 1 (11/20) (11/20) (11/20)
            ∧ 4 * ((11/20 : ℝ) * (11/20) * (11/20)) ^ 2
              < evenTripleDetPart 1 1 1 (11/20) (11/20) (11/20) ^ 2) := by
  refine ⟨(exists_cover_not_flip_cover).1, ?_⟩
  rintro ⟨_, hsq⟩
  rw [evenTripleDetPart] at hsq
  norm_num at hsq

/-- The cover's two halves are genuinely different sets, in both directions. -/
theorem cover_halves_incomparable :
    (TripleCover 1 1 1 (11/20) (11/20) (11/20)
        ∧ ¬ (0 < evenTripleDetPart 1 1 1 (11/20) (11/20) (11/20)
              ∧ 4 * ((11/20 : ℝ) * (11/20) * (11/20)) ^ 2
                < evenTripleDetPart 1 1 1 (11/20) (11/20) (11/20) ^ 2))
      ∧ (0 < evenTripleDetPart 10 1 1 2 0 0
          ∧ 4 * ((2 : ℝ) * 0 * 0) ^ 2 < evenTripleDetPart 10 1 1 2 0 0 ^ 2) :=
  ⟨sign_aware_cell_not_redundant, sum_witness_mem_top⟩

/-! ## 10. The objective read through the cover

The consumer asks for a strict dominator at every primitive design.  Stating that
through the cover splits it into a selection problem and a residue, and makes the
residue the only thing left to attack. -/

/-- **THE OBJECTIVE, READ THROUGH THE COVER.**  Every primitive design carries
three distinct labels whose lower minors are positive and whose triple fires the
composed cover. -/
def DesignCoverSelects : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
    ∃ x y z : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z
      ∧ 1 < leverageOf (design.atom x)
      ∧ 0 < pairGapMinor (design.atom x) (design.atom y)
      ∧ AtomTripleCover (design.atom x) (design.atom y) (design.atom z)

theorem card_three_of_distinct {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({x, y, z} : Finset (Fin 6)).card = 3 :=
  Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩

/-- **THE COVER STATEMENT REACHES THE CONSUMER.**  It gives the design-level
consolidated statement, which retires all five on-path obligations. -/
theorem consolidatedStrictTripleDesign_of_designCoverSelects
    (h : DesignCoverSelects) : ConsolidatedStrictTripleDesign := by
  intro design hprimitive
  obtain ⟨x, y, z, hxy, hxz, hyz, hx, hxyMinor, hcover⟩ := h design hprimitive
  exact ⟨{x, y, z}, card_three_of_distinct hxy hxz hyz,
    subsetSum_posDef_of_atomCover design x y z hxy hxz hyz hx hxyMinor hcover⟩

/-- The design-level residue: a design where every triple with positive lower
minors escapes the cover.  By the triple-level characterization each such triple
has a positive triple product and a non-positive even part. -/
def DesignCoverResidue (design : WeightedDesign 6 3) : Prop :=
  ∀ x y z : Fin 6, x ≠ y → x ≠ z → y ≠ z →
    1 < leverageOf (design.atom x) → 0 < pairGapMinor (design.atom x) (design.atom y) →
      ¬ AtomTripleCover (design.atom x) (design.atom y) (design.atom z)

/-- **THE DICHOTOMY.**  Every primitive design either selects through the cover or
sits in the cover's residue.  There is no third case. -/
theorem coverSelects_or_coverResidue (design : WeightedDesign 6 3) :
    (∃ x y z : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z
        ∧ 1 < leverageOf (design.atom x)
        ∧ 0 < pairGapMinor (design.atom x) (design.atom y)
        ∧ AtomTripleCover (design.atom x) (design.atom y) (design.atom z))
      ∨ DesignCoverResidue design := by
  by_cases h : ∃ x y z : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z
      ∧ 1 < leverageOf (design.atom x)
      ∧ 0 < pairGapMinor (design.atom x) (design.atom y)
      ∧ AtomTripleCover (design.atom x) (design.atom y) (design.atom z)
  · exact Or.inl h
  · refine Or.inr ?_
    intro x y z hxy hxz hyz hx hxyMinor hcover
    exact h ⟨x, y, z, hxy, hxz, hyz, hx, hxyMinor, hcover⟩

/-- **IN THE RESIDUE EVERY ADMISSIBLE DOMINATING TRIPLE IS COHERENT.**  This is
the design-level form of the triple-level fact that the cover is complete at a
non-positive triple product. -/
theorem cross_pos_of_designCoverResidue (design : WeightedDesign 6 3)
    (hres : DesignCoverResidue design) (x y z : Fin 6)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : 1 < leverageOf (design.atom x))
    (hxyMinor : 0 < pairGapMinor (design.atom x) (design.atom y))
    (hdet : 0 < tripleGapDet (design.atom x) (design.atom y) (design.atom z)) :
    0 < (design.atom x ⬝ᵥ design.atom y) * (design.atom x ⬝ᵥ design.atom z)
        * (design.atom y ⬝ᵥ design.atom z) := by
  by_contra hle
  exact hres x y z hxy hxz hyz hx hxyMinor
    (atomCover_of_cross_nonpos_of_det_pos _ _ _ hdet (not_lt.mp hle))

/-- **AND ITS EVEN PART IS NON-POSITIVE.**  So the residue is the coherent side
with a deficient even part, and nothing else. -/
theorem atomEvenPart_nonpos_of_designCoverResidue (design : WeightedDesign 6 3)
    (hres : DesignCoverResidue design) (x y z : Fin 6)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : 1 < leverageOf (design.atom x))
    (hxyMinor : 0 < pairGapMinor (design.atom x) (design.atom y))
    (hdet : 0 < tripleGapDet (design.atom x) (design.atom y) (design.atom z)) :
    atomEvenPart (design.atom x) (design.atom y) (design.atom z) ≤ 0 :=
  ((atomCoverResidue_iff _ _ _ hdet).mp
    (hres x y z hxy hxz hyz hx hxyMinor)).2

end Gtz
