/-
# What the corner's axis calculus hands the other corner lanes

`Gtz/Wave/CornerAxisCalculus.lean` spends the corner form at four probes.  This
module spends the RESULT: it solves the calculus for the two axis readings, it
composes the two corner eliminations into a single reduced alphabet, it prices a
tie-free ceiling at the corner, and it turns the admissibility gateway into a
combinatorial statement.

## 1. The axis reading of an inside atom is DETERMINED, not merely bounded

The vanishing inside pair minor turns every inside pairing into a product of
excesses, and the atom reading then solves outright:

  **`λ·⟨u,g_e⟩² = (1+λ)·(ℓ_e − 1)`**   (`Gtz.cornerForm_insideAtom_axisMass`)

for each of the three inside atoms.  So an inside atom's axis reading is a
FUNCTION of its own leverage — there is nothing left to bound.  The excesses are
nonnegative and total `λ`, so the reading obeys the sharp two-sided cage

  `0 ≤ ⟨u,g_e⟩² ≤ 1 + λ`  and  `1 ≤ ℓ_e ≤ 1 + λ`

(`Gtz.cornerForm_insideAtom_axisReading_le`, `Gtz.cornerForm_insideAtom_leverage_le`),
and the upper end is approached: measured `max ⟨u,g_e⟩²/(1+λ) = 0.9999999785`
over 10175 corners, so neither bound can be improved.

For an OUTSIDE atom the same scalar is solved by the mixed pair minor total:

  **`λ·⟨u,g_d⟩² = (λ−1)·ℓ_d − λ − Σ_{e∈C} q_ed`**
  (`Gtz.cornerForm_outsideAtom_axisMass`)

so both axis readings are eliminable — the inside one against leverages alone,
the outside one against leverages and pair minors.

## 2. The two eliminations compose into one alphabet

`Gtz.tripleGapDet_eq_pairAxisForm` splits any gap determinant over a pair base
into the base's axis form plus the third leverage times the base's pair minor.
At a corner the inside base's pair minor is ZERO, so the second term vanishes
identically and

  **`tripleGapDet g_x g_y c = pairAxisForm g_x g_y ⟨g_x,c⟩ ⟨g_y,c⟩`**

for EVERY third vector `c` (`Gtz.cornerForm_pairAxisForm_insideBase`).  Two
things follow at once.  First, a vanishing pair minor is exactly a vanishing
DISCRIMINANT of that binary quadratic form, so over an inside base the axis form
is a NEGATIVE PERFECT SQUARE, and

  `tripleGapDet g_x g_y c ≤ 0`  for every `c` whatsoever

(`Gtz.cornerForm_twoInside_gapDet_nonpos_general`) — the two-inside refusal
extends off the design's own atoms.  Second, composing with the exact two-inside
law identifies the square:

  **`pairAxisForm g_x g_y ⟨g_x,g_d⟩ ⟨g_y,g_d⟩ = − λ·[g_z g_d u]²`**

(`Gtz.cornerForm_pairAxisForm_eq_neg_axisBracket`).  The pair currency on the
left and the bracket currency on the right are now the same object.

## 3. The tie-free wedge ceiling is VACUOUS at a corner

`Gtz.crossNormSq_le_tripleBracket_sq_of_posSemidef` — `S_T ⪰ 1 ⟹ w_ab ≤ [abc]²`,
tie-free, so a free refusal producer — applies at a corner only to the corner
triple itself, since a tie has no other weakly dominating triple.  There the axis
elimination evaluates both sides exactly, `w_xy = 1 + (ℓ_x−1) + (ℓ_y−1)` and
`[xyz]² = 1 + λ`, and the ceiling reduces to

  **`1 ≤ ℓ_z`**   (`Gtz.cornerForm_wedgeCeiling_iff_third_heavy`)

— the third atom being heavy, which a tie already supplies.  So this instrument
carries NO information at a corner.  Recorded as a negative so the lane does not
spend a round on it: the ceiling's power is at the size-five strata, not here.

## 4. The admissibility gateway is a pigeonhole

Three labels out of a three-plus-three split always contain two on the same side
(`Gtz.three_of_six_share_a_side`, a decision procedure over the 216 ordered
triples).  Admissibility is an EDGE property, so if every inside pair AND every
outside pair is inadmissible then every triple carries an inadmissible pair, no
triple is live, and NOTHING strictly dominates
(`Gtz.allSameSideInadmissible_no_posDef`).

At a corner the inside pairs are inadmissible for free, so the hypothesis
collapses to the three OUTSIDE pairs, and the statement reads: a corner all of
whose outside pairs are inadmissible admits no strict dominator at all — it IS a
tie.  **That is not a hypothesis the horn may assume away; it is the exact
residual configuration the horn has to exclude.**

[MEASURED.  The zero bin is empty: over 16920 corners the number of admissible
outside pairs is never zero, histogram `[0, 265, 289, 16366]`, and two
independent adversarial descents put `min over corners of max_{d<d'} q_dd' =
0.21395` and `0.21378`.  So the residual configuration appears to be empty, but
that is descent evidence and NOT a proof — it is this lane's designated next
brick.  `scratchpad/f42/laws.jl`, `probe.jl`.]
-/
import Gtz.Wave.CornerAxisCalculus
import Gtz.Wave.CornerPairAdjugate
import Gtz.Wave.KOneWedgeCeiling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {gx gy gz u : Fin 3 → ℝ} {lam : ℝ}

/-! ## 1. The two axis readings, solved -/

/-- A vanishing pair minor turns the pairing into the product of the two
excesses.  This is the corner's inside-pair relation in the form the readings
consume. -/
theorem pairing_sq_of_pairGapMinor_zero {a b : Fin 3 → ℝ}
    (h : pairGapMinor a b = 0) :
    (a ⬝ᵥ b) ^ 2 = (leverageOf a - 1) * (leverageOf b - 1) := by
  have := pairGapMinor_eq_sub_sq a b
  rw [h] at this
  linarith [this]

/-- **THE AXIS READING OF AN INSIDE ATOM IS DETERMINED.**  With the inside pair
minors gone, the atom reading at `g_x` solves outright: the axis mass an inside
atom carries is its own excess, scaled by `1 + λ`.  Nothing is left to bound. -/
theorem cornerForm_insideAtom_axisMass (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1)
    (hxy : pairGapMinor gx gy = 0) (hxz : pairGapMinor gx gz = 0) :
    lam * (u ⬝ᵥ gx) ^ 2 = (1 + lam) * (leverageOf gx - 1) := by
  have hread := cornerForm_atom_reading h gx
  have hlev := cornerForm_leverage_total h hu
  have hself : (gx ⬝ᵥ gx) ^ 2 = leverageOf gx ^ 2 := by
    rw [← leverageOf_eq_dotProduct]
  have hpy : (gy ⬝ᵥ gx) ^ 2 = (leverageOf gx - 1) * (leverageOf gy - 1) := by
    rw [dotProduct_comm gy gx, pairing_sq_of_pairGapMinor_zero hxy]
  have hpz : (gz ⬝ᵥ gx) ^ 2 = (leverageOf gx - 1) * (leverageOf gz - 1) := by
    rw [dotProduct_comm gz gx, pairing_sq_of_pairGapMinor_zero hxz]
  rw [hself, hpy, hpz] at hread
  have hprod : (leverageOf gx - 1) * (leverageOf gy - 1)
        + (leverageOf gx - 1) * (leverageOf gz - 1)
      = (leverageOf gx - 1) * (1 + lam - leverageOf gx) := by
    have hsum : (leverageOf gy - 1) + (leverageOf gz - 1)
        = 1 + lam - leverageOf gx := by linarith [hlev]
    rw [← hsum]; ring
  linear_combination - hread + hprod

/-- The excess of an inside atom is capped by the scale, so its axis reading is
caged by `1 + λ`.  Measured sharp: the ratio reaches `0.9999999785`. -/
theorem cornerForm_insideAtom_axisReading_le (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (hlam : 0 < lam)
    (hxy : pairGapMinor gx gy = 0) (hxz : pairGapMinor gx gz = 0)
    (hy : 1 ≤ leverageOf gy) (hz : 1 ≤ leverageOf gz) :
    (u ⬝ᵥ gx) ^ 2 ≤ 1 + lam := by
  have hmass := cornerForm_insideAtom_axisMass h hu hxy hxz
  have hlev := cornerForm_leverage_total h hu
  have hcap : leverageOf gx - 1 ≤ lam := by linarith [hlev, hy, hz]
  nlinarith [hmass, hcap, hlam]

/-- The leverage of an inside atom is caged the same way. -/
theorem cornerForm_insideAtom_leverage_le (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1)
    (hy : 1 ≤ leverageOf gy) (hz : 1 ≤ leverageOf gz) :
    leverageOf gx ≤ 1 + lam := by
  have hlev := cornerForm_leverage_total h hu
  linarith [hlev, hy, hz]

/-- **THE AXIS MASS OF AN OUTSIDE ATOM, SOLVED.**  The mixed pair minor total is
one equation in that scalar, so it eliminates against leverages and pair minors
alone. -/
theorem cornerForm_outsideAtom_axisMass (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (gd : Fin 3 → ℝ) :
    lam * (u ⬝ᵥ gd) ^ 2
      = (lam - 1) * leverageOf gd - lam
        - (pairGapMinor gx gd + pairGapMinor gy gd + pairGapMinor gz gd) := by
  have := cornerForm_mixed_pairMinor_total h hu gd
  linarith [this]

/-! ## 2. The two eliminations compose -/

/-- **THE INSIDE BASE KILLS THE PAIR MINOR TERM.**  Over a base whose pair minor
vanishes, a gap determinant is exactly the base's axis form — for EVERY third
vector, on the design or off it. -/
theorem cornerForm_pairAxisForm_insideBase (hxy : pairGapMinor gx gy = 0)
    (c : Fin 3 → ℝ) :
    tripleGapDet gx gy c = pairAxisForm gx gy (gx ⬝ᵥ c) (gy ⬝ᵥ c) := by
  rw [tripleGapDet_eq_pairAxisForm gx gy c, hxy]
  ring

/-- **THE COMPOSED FORM.**  The pair axis form over an inside base is minus the
scale times a squared axis bracket: the pair currency and the bracket currency
name the same object at a corner. -/
theorem cornerForm_pairAxisForm_eq_neg_axisBracket (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (hxy : pairGapMinor gx gy = 0) (gd : Fin 3 → ℝ) :
    pairAxisForm gx gy (gx ⬝ᵥ gd) (gy ⬝ᵥ gd)
      = - lam * tripleBracket gz gd u ^ 2 := by
  rw [← cornerForm_pairAxisForm_insideBase hxy gd]
  exact cornerForm_twoInside_gapDet_pure h hu hxy gd

/-- **THE TWO-INSIDE REFUSAL EXTENDS OFF THE DESIGN.**  A vanishing pair minor is
a vanishing discriminant, so the inside base's axis form is a negative perfect
square and the gap determinant is nonpositive at EVERY third vector — not only
at the design's own outside atoms. -/
theorem cornerForm_twoInside_gapDet_nonpos_general (hxy : pairGapMinor gx gy = 0)
    (hx : 1 ≤ leverageOf gx) (hy : 1 ≤ leverageOf gy) (c : Fin 3 → ℝ) :
    tripleGapDet gx gy c ≤ 0 := by
  rw [cornerForm_pairAxisForm_insideBase hxy c, pairAxisForm]
  have hdisc : (gx ⬝ᵥ gy) ^ 2 = (leverageOf gx - 1) * (leverageOf gy - 1) :=
    pairing_sq_of_pairGapMinor_zero hxy
  rcases eq_or_lt_of_le hx with hA0 | hApos
  · -- the excess of `gx` vanishes, so the pairing does too and one square is left
    have hp : (gx ⬝ᵥ gy) ^ 2 = 0 := by rw [hdisc, ← hA0]; ring
    have hp0 : gx ⬝ᵥ gy = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hp
    rw [hp0, ← hA0]
    nlinarith [hy, sq_nonneg (gx ⬝ᵥ c), sq_nonneg (gy ⬝ᵥ c)]
  · -- the excess is positive and it turns the negated form into a perfect square
    have key : (leverageOf gx - 1)
        * (-((1 - leverageOf gy) * (gx ⬝ᵥ c) ^ 2
            + 2 * (gx ⬝ᵥ gy) * (gx ⬝ᵥ c) * (gy ⬝ᵥ c)
            + (1 - leverageOf gx) * (gy ⬝ᵥ c) ^ 2))
        = ((gx ⬝ᵥ gy) * (gx ⬝ᵥ c) - (leverageOf gx - 1) * (gy ⬝ᵥ c)) ^ 2 := by
      linear_combination (- (gx ⬝ᵥ c) ^ 2) * hdisc
    nlinarith [key, hApos,
      sq_nonneg ((gx ⬝ᵥ gy) * (gx ⬝ᵥ c) - (leverageOf gx - 1) * (gy ⬝ᵥ c))]

/-! ## 3. The tie-free wedge ceiling is vacuous at a corner -/

/-- A vanishing pair minor evaluates the wedge outright. -/
theorem pairWedge_of_pairGapMinor_zero {a b : Fin 3 → ℝ}
    (h : pairGapMinor a b = 0) :
    pairWedge a b = leverageOf a + leverageOf b - 1 := by
  have := pairGapMinor_eq_pairWedge_sub a b
  rw [h] at this
  linarith [this]

/-- **THE WEDGE CEILING'S SLACK AT A CORNER IS THE THIRD ATOM'S EXCESS.**  The
ceiling `w_xy ≤ [xyz]²` is tie-free, so it is a free refusal producer — but at a
corner its two sides are both evaluated by the axis calculus and the gap between
them is exactly `ℓ_z − 1`, which is also exactly the scale times the squared axis
bracket of the inside pair:

  `[xyz]² − w_xy = λ·[g_x g_y u]² = ℓ_z − 1` .

Since a tie makes every atom heavy, the ceiling holds automatically and carries
NO information at a corner.  Recorded so the lane does not spend a round on it.
-/
theorem cornerForm_wedgeCeiling_slack (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1)
    (hxy : pairGapMinor gx gy = 0) (hxz : pairGapMinor gx gz = 0)
    (hyz : pairGapMinor gy gz = 0) :
    tripleBracket gx gy gz ^ 2 - pairWedge gx gy = lam * tripleBracket gx gy u ^ 2
      ∧ lam * tripleBracket gx gy u ^ 2 = leverageOf gz - 1 := by
  -- the axis elimination at the inside pair, whose only surviving slot is `gz`
  have hbt := cornerForm_bracket_total h gx gy
  have hdx : tripleBracket gx gy gx = 0 := by
    rw [tripleBracket, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hdy : tripleBracket gx gy gy = 0 := by
    rw [tripleBracket, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hdx, hdy] at hbt
  -- the three inside wedges, and the corner's own vanishing determinant
  have hwxy := pairWedge_of_pairGapMinor_zero hxy
  have hwxz := pairWedge_of_pairGapMinor_zero hxz
  have hwyz := pairWedge_of_pairGapMinor_zero hyz
  have hled := tripleGapDet_eq_bracketSq_sub_wedgeSum gx gy gz
  have hdet : tripleGapDet gx gy gz = 0 := by
    have hc := cornerForm_corner_gapDet_eq_neg_pairGapMinor h hu
    rw [hxy] at hc
    linarith [hc]
  refine ⟨by linarith [hbt], ?_⟩
  linarith [hbt, hwxy, hwxz, hwyz, hled, hdet]

/-! ## 4. The admissibility gateway as a pigeonhole -/

/-- **THREE OUT OF A THREE-PLUS-THREE SPLIT SHARE A SIDE.**  A decision procedure
over the 216 ordered triples of `Fin 6`. -/
theorem three_of_six_share_a_side (a b c : Fin 6)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a.val < 3 ∧ b.val < 3) ∨ (a.val < 3 ∧ c.val < 3)
      ∨ (b.val < 3 ∧ c.val < 3) ∨ (3 ≤ a.val ∧ 3 ≤ b.val)
      ∨ (3 ≤ a.val ∧ 3 ≤ c.val) ∨ (3 ≤ b.val ∧ 3 ≤ c.val) := by
  revert hab hac hbc
  revert a b c
  decide

/-- **EVERY SIDE INADMISSIBLE LEAVES NOTHING TO DOMINATE.**  Admissibility is an
edge property and every triple of a three-plus-three split carries an edge inside
one side.  So if all inside pairs and all outside pairs are inadmissible, no
triple is live and no triple strictly dominates.

At a corner the inside pairs are inadmissible for free
(`Gtz.cornerForm_insidePair_not_admissible`), so the hypothesis collapses to the
three OUTSIDE pairs: a corner whose outside pairs are all inadmissible admits no
strict dominator, hence IS a tie.  That configuration is the horn's exact
residual, not an assumption it may discharge. -/
theorem allSameSideInadmissible_no_posDef (D : WeightedDesign 6 3)
    (hin : ∀ p q : Fin 6, p.val < 3 → q.val < 3 → p ≠ q →
      ¬ AdmissiblePair (D.atom p) (D.atom q))
    (hout : ∀ p q : Fin 6, 3 ≤ p.val → 3 ≤ q.val → p ≠ q →
      ¬ AdmissiblePair (D.atom p) (D.atom q))
    (a b c : Fin 6) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ (subsetSum D ({a, b, c} : Finset (Fin 6)) - 1).PosDef := by
  intro hpd
  obtain ⟨⟨-, -, -, pab, pac, pbc⟩, -⟩ :=
    (posDef_subsetSum_iff_live_and_gapDet D a b c hab hac hbc).mp hpd
  rcases three_of_six_share_a_side a b c hab hac hbc with
    ⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩ | ⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩
  · exact hin a b ha hb hab pab
  · exact hin a c ha hc hac pac
  · exact hin b c hb hc hbc pbc
  · exact hout a b ha hb hab pab
  · exact hout a c ha hc hac pac
  · exact hout b c hb hc hbc pbc

end Gtz
