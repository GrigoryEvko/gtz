/-
# The outside pair as a base: its adjugate reading, its axis form, and why the
# corner sum law is lossy

The coherent horn's remaining branch asks for ONE polynomial sign at a corner.
`Gtz.corner_sum_det_pairBase` totals the three one-inside gap determinants over a
fixed outside pair, and its own measurement says that total is positive at only
`22.46%` of pairs and `58.75%` of branch points.  This module explains that
number algebraically and replaces the sum by a per-triple selector.

## The base and its three invariants

Write `pairGap a b := a a' + b b' - 1` for the gap of an outside pair.  All three
of its characteristic invariants are pair-local, and each is the campaign's
landed pair minor `Gtz.pairGapMinor a b = (l_a - 1)(l_b - 1) - (a.b)^2`:

* `Gtz.pairGap_det` -- `det = -pairGapMinor`
* `Gtz.pairGap_secondInvariant` -- `e2 = pairGapMinor - l_a - l_b + 2`
* `Gtz.pairGap_add_atom_det` -- `det(pairGap + c c') = tripleGapDet a b c` .

The last one identifies the rank-one update with the campaign's landed third
Sylvester minor, so the adjugate reading of the base is a landed object:

  **`Gtz.pairGap_adjugate_reading`:  `<c, adj(pairGap a b) c> = tripleGapDet a b c
  + pairGapMinor a b`** ,

and `Gtz.pairGap_adjugate_reading_currency` writes it in terminal currency,

  `<c, adj(pairGap a b) c> = [a,b,c]^2 + l_c*(1 - l_a - l_b) + (a.c)^2 + (b.c)^2` .

## The pair axis form, and the exact residue

The whole dependence of `tripleGapDet a b c` on the third atom splits into its
two READINGS against the pair and its leverage excess
(`Gtz.tripleGapDet_eq_pairAxisForm`, a hypothesis-free identity):

  **`tripleGapDet a b c = pairAxisForm a b (a.c) (b.c) + (l_c - 1)*pairGapMinor a b`**

with the binary form

  `pairAxisForm a b al be := (1 - l_b)*al^2 + 2*(a.b)*al*be + (1 - l_a)*be^2` .

Its discriminant is the pair minor itself, which the one-line square identity
`Gtz.pairAxisForm_sos` exhibits:

  `(l_b - 1)*pairAxisForm a b al be
     = -((l_b - 1)*al - (a.b)*be)^2 - pairGapMinor a b * be^2` .

So **on an ADMISSIBLE pair the axis form is NEGATIVE DEFINITE**
(`Gtz.pairAxisForm_neg`), where admissible means `1 < l_a` and
`0 < pairGapMinor a b` -- exactly the first two Sylvester minors of the gap.

## Two consequences

**THE AXIS NEVER REPAYS** (`Gtz.tripleGapDet_axis_neg`).  A corner's own axis `u`
is a unit vector, so its leverage excess vanishes and `tripleGapDet a b u` IS the
axis form: strictly negative on an admissible pair whenever `u` reads the pair at
all.  In the `(P)` stratum every axis reading is nonzero, so the axis direction
adjoined to an admissible outside pair NEVER strictly dominates.  No branch, no
measurement.

**WHY THE SUM LAW IS LOSSY** (`Gtz.corner_pairSum_currency`).  Feeding the base
into the landed corner sum law and reading all three invariants in currency,

  **`sum_{e in C} tripleGapDet a b e
     = lam*(pairGapMinor a b + pairAxisForm a b (a.u) (b.u))
       - 2*pairGapMinor a b - (l_a + l_b - 2)`** .

The pair-only part is `-2*pairGapMinor - tr`, STRICTLY NEGATIVE on an admissible
pair, and the axis term is DAMPED by a negative-definite form.  Hence
`Gtz.corner_pairSum_pos_lam_threshold`: a positive total forces

  `(lam - 2) * pairGapMinor a b > l_a + l_b - 2` .

That is the algebraic content of the measured `41.25%` failure -- the sum can
only fire at pairs whose minor is small against `lam - 2`, and the axis form only
subtracts from the budget.  The instrument is not weak by accident.

## The replacement: select, do not sum

`Gtz.tripleGram_posDef_of_admissible_of_repay` and its design reading discharge
the branch ONE TRIPLE AT A TIME, through the landed Sylvester iff and with no new
positive-definiteness machinery:

  **admissible pair, and `pairGapMinor a b < <c, adj(pairGap a b) c>`  ==>
  `{a,b,c}` strictly dominates.**

Its contrapositive `Gtz.repayment_le_pairGapMinor_of_not_posDef` is the
tie-necessary law in terminal currency, stated per triple with no aggregation
anywhere -- the shape the campaign's doctrine demands.
-/
import Gtz.Design.TripleGramSylvester
import Gtz.Wave.CoherentHornSumLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The pair gap and its three invariants -/

/-- The gap of an OUTSIDE PAIR, used as the base of the three one-inside
triples. -/
noncomputable def pairGap (a b : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  atomMatrix a + atomMatrix b - 1

/-- **THE BASE DETERMINANT IS MINUS THE PAIR MINOR.**  The third invariant of the
pair gap is pair-local and already named by the campaign. -/
theorem pairGap_det (a b : Fin 3 → ℝ) :
    (pairGap a b).det = -(pairGapMinor a b) := by
  simp only [pairGap, Matrix.det_fin_three, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.one_fin_three, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, pairGapMinor, leverageOf,
    dotProduct, Fin.sum_univ_three]
  ring

/-- **THE BASE SECOND INVARIANT.**  Also pair-local, and also the pair minor up to
the two leverages. -/
theorem pairGap_secondInvariant (a b : Fin 3 → ℝ) :
    ((Matrix.trace (pairGap a b)) ^ 2
        - Matrix.trace (pairGap a b * pairGap a b)) / 2
      = pairGapMinor a b - leverageOf a - leverageOf b + 2 := by
  simp only [pairGap, Matrix.trace_fin_three, Matrix.mul_apply, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    pairGapMinor, leverageOf, dotProduct, Fin.sum_univ_three]
  ring

/-- **THE RANK-ONE UPDATE IS THE THIRD SYLVESTER MINOR.**  Adjoining an atom to
the pair base lands exactly on `Gtz.tripleGapDet`, the campaign's landed
bracket-free triple minor. -/
theorem pairGap_add_atom_det (a b c : Fin 3 → ℝ) :
    (pairGap a b + atomMatrix c).det = tripleGapDet a b c := by
  have hrw : pairGap a b + atomMatrix c
      = atomMatrix a + atomMatrix b + atomMatrix c - 1 := by
    rw [pairGap]; abel
  rw [hrw]
  simp only [Matrix.det_fin_three, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.one_fin_three, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, tripleGapDet, leverageOf,
    dotProduct, Fin.sum_univ_three]
  ring

/-! ## 2. The adjugate reading of the base -/

/-- **THE ADJUGATE READING.**  The pair base reads an atom at exactly the triple's
Sylvester minor shifted by the pair's own.  This is the rank-one determinant
update run backwards, so it costs nothing. -/
theorem pairGap_adjugate_reading (a b c : Fin 3 → ℝ) :
    c ⬝ᵥ ((pairGap a b).adjugate *ᵥ c)
      = tripleGapDet a b c + pairGapMinor a b := by
  have h := det_add_atomMatrix_fin_three (pairGap a b) c
  rw [pairGap_add_atom_det, pairGap_det] at h
  linarith [h]

/-- **THE READING IN TERMINAL CURRENCY.**  Squared bracket, leverage against the
pair's total, and the two squared readings.  No matrix, no adjugate. -/
theorem pairGap_adjugate_reading_currency (a b c : Fin 3 → ℝ) :
    c ⬝ᵥ ((pairGap a b).adjugate *ᵥ c)
      = tripleBracket a b c ^ 2
        + leverageOf c * (1 - leverageOf a - leverageOf b)
        + (a ⬝ᵥ c) ^ 2 + (b ⬝ᵥ c) ^ 2 := by
  rw [pairGap_adjugate_reading, tripleGapDet_eq_thirdInvariant,
    pairGapMinor_eq_crossNormSq]
  simp only [triplePairAreaSum, tripleLeverageSum,
    crossNormSq_eq_leverage_mul_sub_sq]
  ring

/-! ## 3. The pair axis form -/

/-- The binary form through which an atom's two READINGS against an outside pair
enter that pair's gap determinant.  Its discriminant is the pair minor. -/
noncomputable def pairAxisForm (a b : Fin 3 → ℝ) (al be : ℝ) : ℝ :=
  (1 - leverageOf b) * al ^ 2 + 2 * (a ⬝ᵥ b) * al * be
    + (1 - leverageOf a) * be ^ 2

/-- **THE EXACT SPLIT.**  A triple's gap determinant over a pair base is the axis
form at the two readings plus the third atom's leverage excess priced by the pair
minor.  Hypothesis-free: no unit norm, no design, no positivity. -/
theorem tripleGapDet_eq_pairAxisForm (a b c : Fin 3 → ℝ) :
    tripleGapDet a b c
      = pairAxisForm a b (a ⬝ᵥ c) (b ⬝ᵥ c)
        + (leverageOf c - 1) * pairGapMinor a b := by
  simp only [tripleGapDet, pairAxisForm, pairGapMinor, leverageOf, dotProduct,
    Fin.sum_univ_three]
  ring

/-- **THE SQUARE IDENTITY.**  One `ring` step exhibiting the axis form's
discriminant as the pair minor.  No hypotheses. -/
theorem pairAxisForm_sos (a b : Fin 3 → ℝ) (al be : ℝ) :
    (leverageOf b - 1) * pairAxisForm a b al be
      = -((leverageOf b - 1) * al - (a ⬝ᵥ b) * be) ^ 2
        - pairGapMinor a b * be ^ 2 := by
  simp only [pairAxisForm, pairGapMinor]
  ring

/-- **AN ADMISSIBLE PAIR IS HEAVY ON BOTH SIDES.**  A positive pair minor
transports the first Sylvester sign from one atom to the other. -/
theorem one_lt_leverage_of_pairGapMinor_pos {a b : Fin 3 → ℝ}
    (ha : 1 < leverageOf a) (hmin : 0 < pairGapMinor a b) :
    1 < leverageOf b := by
  by_contra hcon
  push_neg at hcon
  have h1 : 0 < leverageOf a - 1 := by linarith
  have h2 : leverageOf b - 1 ≤ 0 := by linarith
  have h3 : (leverageOf a - 1) * (leverageOf b - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt h1) h2
  rw [pairGapMinor] at hmin
  nlinarith [sq_nonneg (a ⬝ᵥ b)]

/-- **THE AXIS FORM IS NONPOSITIVE ON AN ADMISSIBLE PAIR.** -/
theorem pairAxisForm_nonpos {a b : Fin 3 → ℝ} (ha : 1 < leverageOf a)
    (hmin : 0 < pairGapMinor a b) (al be : ℝ) :
    pairAxisForm a b al be ≤ 0 := by
  have hb : 1 < leverageOf b := one_lt_leverage_of_pairGapMinor_pos ha hmin
  have hbpos : 0 < leverageOf b - 1 := by linarith
  have hsos := pairAxisForm_sos a b al be
  have hquad : 0 ≤ pairGapMinor a b * be ^ 2 :=
    mul_nonneg (le_of_lt hmin) (sq_nonneg be)
  have hscaled : (leverageOf b - 1) * pairAxisForm a b al be ≤ 0 := by
    rw [hsos]
    nlinarith [sq_nonneg ((leverageOf b - 1) * al - (a ⬝ᵥ b) * be), hquad]
  by_contra hcon
  push Not at hcon
  nlinarith [hscaled, hbpos, hcon]

/-- **THE AXIS FORM IS NEGATIVE DEFINITE ON AN ADMISSIBLE PAIR.**  Any nonzero
reading pair makes it strictly negative. -/
theorem pairAxisForm_neg {a b : Fin 3 → ℝ} (ha : 1 < leverageOf a)
    (hmin : 0 < pairGapMinor a b) {al be : ℝ} (hne : al ≠ 0 ∨ be ≠ 0) :
    pairAxisForm a b al be < 0 := by
  have hb : 1 < leverageOf b := one_lt_leverage_of_pairGapMinor_pos ha hmin
  have hbpos : 0 < leverageOf b - 1 := by linarith
  have hsos := pairAxisForm_sos a b al be
  have hscaled : (leverageOf b - 1) * pairAxisForm a b al be < 0 := by
    rw [hsos]
    rcases eq_or_ne be 0 with hbe | hbe
    · have hal : al ≠ 0 := hne.resolve_right (not_not_intro hbe)
      have hXne : (leverageOf b - 1) * al - (a ⬝ᵥ b) * be ≠ 0 := by
        rw [hbe]; simpa using mul_ne_zero (ne_of_gt hbpos) hal
      have hXsq : 0 < ((leverageOf b - 1) * al - (a ⬝ᵥ b) * be) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hXne))
      have hquad : 0 ≤ pairGapMinor a b * be ^ 2 :=
        mul_nonneg (le_of_lt hmin) (sq_nonneg be)
      linarith
    · have hbesq : 0 < be ^ 2 := by positivity
      have hquad : 0 < pairGapMinor a b * be ^ 2 := mul_pos hmin hbesq
      nlinarith [sq_nonneg ((leverageOf b - 1) * al - (a ⬝ᵥ b) * be), hquad]
  by_contra hcon
  push Not at hcon
  nlinarith [hscaled, hbpos, hcon]

/-! ## 4. The corner axis never repays -/

/-- **THE AXIS IS THE AXIS FORM.**  A unit vector has no leverage excess, so its
gap determinant over a pair base is exactly the axis form at its two readings. -/
theorem tripleGapDet_unit_eq_pairAxisForm {a b u : Fin 3 → ℝ}
    (hu : leverageOf u = 1) :
    tripleGapDet a b u = pairAxisForm a b (a ⬝ᵥ u) (b ⬝ᵥ u) := by
  rw [tripleGapDet_eq_pairAxisForm, hu]; ring

/-- **THE AXIS NEVER STRICTLY DOMINATES OVER AN ADMISSIBLE PAIR.**  On the `(P)`
stratum, where every axis reading is nonzero, the corner's own axis adjoined to an
admissible outside pair has STRICTLY NEGATIVE gap determinant.  No tie hypothesis,
no branch, no measurement. -/
theorem tripleGapDet_axis_neg {a b u : Fin 3 → ℝ} (hu : leverageOf u = 1)
    (ha : 1 < leverageOf a) (hmin : 0 < pairGapMinor a b)
    (hread : a ⬝ᵥ u ≠ 0 ∨ b ⬝ᵥ u ≠ 0) :
    tripleGapDet a b u < 0 := by
  rw [tripleGapDet_unit_eq_pairAxisForm hu]
  exact pairAxisForm_neg ha hmin hread

/-- The nonstrict form, which needs no reading hypothesis at all. -/
theorem tripleGapDet_axis_nonpos {a b u : Fin 3 → ℝ} (hu : leverageOf u = 1)
    (ha : 1 < leverageOf a) (hmin : 0 < pairGapMinor a b) :
    tripleGapDet a b u ≤ 0 := by
  rw [tripleGapDet_unit_eq_pairAxisForm hu]
  exact pairAxisForm_nonpos ha hmin _ _

/-! ## 5. The selector: one triple at a time -/

/-- **THE PER-TRIPLE PRODUCER.**  An admissible outside pair together with ONE
atom whose repayment beats the pair minor gives a STRICT dominator.  Routed
through the campaign's landed Sylvester iff, so no new positive-definiteness
machinery is spent.  This is the sum law's replacement: it selects rather than
aggregates. -/
theorem tripleGram_posDef_of_admissible_of_repay {a b c : Fin 3 → ℝ}
    (ha : 1 < leverageOf a) (hmin : 0 < pairGapMinor a b)
    (hrepay : pairGapMinor a b < c ⬝ᵥ ((pairGap a b).adjugate *ᵥ c)) :
    (tripleGram a b c - 1).PosDef := by
  rw [tripleGram_posDef_iff_pairVocabulary]
  refine ⟨by linarith, hmin, ?_⟩
  rw [pairGap_adjugate_reading] at hrepay
  linarith

/-- **THE PRODUCER IN TERMINAL CURRENCY.**  The repayment written out: squared
bracket, leverage against the pair total, and the two squared readings. -/
theorem tripleGram_posDef_of_admissible_of_repay_currency {a b c : Fin 3 → ℝ}
    (ha : 1 < leverageOf a) (hmin : 0 < pairGapMinor a b)
    (hrepay : pairGapMinor a b
      < tripleBracket a b c ^ 2
        + leverageOf c * (1 - leverageOf a - leverageOf b)
        + (a ⬝ᵥ c) ^ 2 + (b ⬝ᵥ c) ^ 2) :
    (tripleGram a b c - 1).PosDef := by
  refine tripleGram_posDef_of_admissible_of_repay ha hmin ?_
  rwa [pairGap_adjugate_reading_currency]

/-- **THE DESIGN READING.**  Same statement at a design: an admissible pair and a
repaying third atom produce a strictly dominating triple. -/
theorem subsetSum_posDef_of_admissible_of_repay (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : 1 < leverageOf (D.atom x))
    (hmin : 0 < pairGapMinor (D.atom x) (D.atom y))
    (hrepay : pairGapMinor (D.atom x) (D.atom y)
      < (D.atom z) ⬝ᵥ ((pairGap (D.atom x) (D.atom y)).adjugate *ᵥ (D.atom z))) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef := by
  rw [subsetSum_posDef_iff_pairVocabulary D x y z hxy hxz hyz]
  refine ⟨by linarith, hmin, ?_⟩
  rw [pairGap_adjugate_reading] at hrepay
  linarith

/-- **THE TIE-NECESSARY LAW, PER TRIPLE.**  Where no strict dominator exists, every
atom's repayment against every admissible pair is capped by that pair's own minor.
Stated one triple at a time, with no aggregation anywhere. -/
theorem repayment_le_pairGapMinor_of_not_posDef (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : 1 < leverageOf (D.atom x))
    (hmin : 0 < pairGapMinor (D.atom x) (D.atom y))
    (hno : ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    (D.atom z) ⬝ᵥ ((pairGap (D.atom x) (D.atom y)).adjugate *ᵥ (D.atom z))
      ≤ pairGapMinor (D.atom x) (D.atom y) := by
  by_contra hcon
  push_neg at hcon
  exact hno (subsetSum_posDef_of_admissible_of_repay D hxy hxz hyz ha hmin hcon)

/-! ## 6. The corner sum in currency, and why it is lossy -/

/-- **THE CORNER PAIR LAW.**  The landed sum law read entirely in pair currency:
the three one-inside gap determinants over a fixed outside pair total to the
corner scale against the pair minor DAMPED by the axis form, less twice the minor
and the pair's trace.  Every matrix invariant is gone. -/
theorem corner_pairSum_currency (a b : Fin 3 → ℝ)
    (gx gy gz u : Fin 3 → ℝ) {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hu : leverageOf u = 1) :
    tripleGapDet a b gx + tripleGapDet a b gy + tripleGapDet a b gz
      = lam * (pairGapMinor a b + pairAxisForm a b (a ⬝ᵥ u) (b ⬝ᵥ u))
        - 2 * pairGapMinor a b - (leverageOf a + leverageOf b - 2) := by
  have hsum := corner_sum_det_pairBase (pairGap a b) gx gy gz u hcorner
  rw [pairGap_add_atom_det, pairGap_add_atom_det, pairGap_add_atom_det,
    pairGap_det, pairGap_secondInvariant, pairGap_adjugate_reading,
    tripleGapDet_unit_eq_pairAxisForm hu] at hsum
  linarith [hsum]

/-- **THE THRESHOLD ON THE CORNER SCALE.**  A positive total over an admissible
pair forces the scale past a pair-local threshold.  This is the algebraic content
of the sum law's measured failure rate: the pair-only part is strictly negative
and the axis form only subtracts, so the total can fire only where the minor is
small against `lam - 2`. -/
theorem corner_pairSum_pos_lam_threshold {a b : Fin 3 → ℝ}
    (gx gy gz u : Fin 3 → ℝ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hu : leverageOf u = 1) (ha : 1 < leverageOf a)
    (hmin : 0 < pairGapMinor a b)
    (hpos : 0 < tripleGapDet a b gx + tripleGapDet a b gy + tripleGapDet a b gz) :
    leverageOf a + leverageOf b - 2 < (lam - 2) * pairGapMinor a b := by
  rw [corner_pairSum_currency a b gx gy gz u hcorner hu] at hpos
  have hax : pairAxisForm a b (a ⬝ᵥ u) (b ⬝ᵥ u) ≤ 0 :=
    pairAxisForm_nonpos ha hmin _ _
  nlinarith [hpos, hax, hlam]

/-- **THE CONTRAPOSITIVE, AS AN EMPTINESS TEST.**  Below the threshold the sum law
provably cannot fire at this pair, so no aggregation over it can ever discharge
the branch.  The instrument's blindness is exact, not statistical. -/
theorem corner_pairSum_nonpos_of_lam_le {a b : Fin 3 → ℝ}
    (gx gy gz u : Fin 3 → ℝ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hu : leverageOf u = 1) (ha : 1 < leverageOf a)
    (hmin : 0 < pairGapMinor a b)
    (hthr : (lam - 2) * pairGapMinor a b ≤ leverageOf a + leverageOf b - 2) :
    tripleGapDet a b gx + tripleGapDet a b gy + tripleGapDet a b gz ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  exact absurd hthr (not_le.mpr
    (corner_pairSum_pos_lam_threshold gx gy gz u hlam hcorner hu ha hmin hcon))


/-! ## 7. A producer with no adjugate and no bracket

The split of `Gtz.tripleGapDet_eq_pairAxisForm` prices the third atom by exactly
two things: its LEVERAGE EXCESS `l_c - 1`, paid at the pair minor, against the
COST of its two readings, paid at the axis form.  On an admissible pair the
second invariant of the axis form's negative is the pair minor again, so the cost
is bounded by the pair's trace times the squared readings.  That turns the whole
criterion into leverages and readings, with no adjugate, no bracket and no
matrix. -/

/-- **THE COST OF THE READINGS IS BOUNDED BY THE PAIR TRACE.**  On an admissible
pair the axis form never falls below the pair's trace against the squared
readings.  The proof is one square identity, since the residue's own
discriminant is the pair minor. -/
theorem pairAxisForm_ge_neg_trace_mul {a b : Fin 3 → ℝ} (ha : 1 < leverageOf a)
    (hmin : 0 < pairGapMinor a b) (al be : ℝ) :
    -((leverageOf a + leverageOf b - 2) * (al ^ 2 + be ^ 2))
      ≤ pairAxisForm a b al be := by
  have hapos : 0 < leverageOf a - 1 := by linarith
  have key : (leverageOf a - 1)
      * ((leverageOf a + leverageOf b - 2) * (al ^ 2 + be ^ 2)
          + pairAxisForm a b al be)
      = ((leverageOf a - 1) * al + (a ⬝ᵥ b) * be) ^ 2
        + pairGapMinor a b * be ^ 2 := by
    simp only [pairAxisForm, pairGapMinor]; ring
  have hrhs : 0 ≤ ((leverageOf a - 1) * al + (a ⬝ᵥ b) * be) ^ 2
      + pairGapMinor a b * be ^ 2 := by
    have := mul_nonneg (le_of_lt hmin) (sq_nonneg be)
    nlinarith [sq_nonneg ((leverageOf a - 1) * al + (a ⬝ᵥ b) * be)]
  nlinarith [key, hrhs, hapos]

/-- **THE LEVERAGE-EXCESS PRODUCER.**  An admissible outside pair and one atom
whose leverage excess, priced at the pair minor, beats the pair trace against its
two squared readings, force a positive triple gap determinant.  Leverages and
readings only. -/
theorem tripleGapDet_pos_of_leverageExcess {a b c : Fin 3 → ℝ}
    (ha : 1 < leverageOf a) (hmin : 0 < pairGapMinor a b)
    (hbeat : (leverageOf a + leverageOf b - 2) * ((a ⬝ᵥ c) ^ 2 + (b ⬝ᵥ c) ^ 2)
      < (leverageOf c - 1) * pairGapMinor a b) :
    0 < tripleGapDet a b c := by
  rw [tripleGapDet_eq_pairAxisForm]
  have hcost := pairAxisForm_ge_neg_trace_mul ha hmin (a ⬝ᵥ c) (b ⬝ᵥ c)
  linarith

/-- **THE PRODUCER AT A DESIGN, ADJUGATE-FREE AND BRACKET-FREE.**  Three
leverages, three readings, one strict inequality, and the triple strictly
dominates. -/
theorem subsetSum_posDef_of_leverageExcess (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : 1 < leverageOf (D.atom x))
    (hmin : 0 < pairGapMinor (D.atom x) (D.atom y))
    (hbeat : (leverageOf (D.atom x) + leverageOf (D.atom y) - 2)
        * (((D.atom x) ⬝ᵥ (D.atom z)) ^ 2 + ((D.atom y) ⬝ᵥ (D.atom z)) ^ 2)
      < (leverageOf (D.atom z) - 1) * pairGapMinor (D.atom x) (D.atom y)) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef := by
  rw [subsetSum_posDef_iff_pairVocabulary D x y z hxy hxz hyz]
  exact ⟨by linarith, hmin, tripleGapDet_pos_of_leverageExcess ha hmin hbeat⟩

/-! ### The corner's leverage-excess budget -/

/-- **THE CORNER SPENDS EXACTLY ITS SCALE.**  The three inside atoms' leverage
excesses total the corner scale, no more and no less.  This is the corner
equation read at the identity form. -/
theorem corner_leverageExcess_sum (gx gy gz u : Fin 3 → ℝ) {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hu : leverageOf u = 1) :
    (leverageOf gx - 1) + (leverageOf gy - 1) + (leverageOf gz - 1) = lam := by
  have hsum := quadForm_sum_of_corner (1 : Matrix (Fin 3) (Fin 3) ℝ) gx gy gz u hcorner
  have hlev : ∀ g : Fin 3 → ℝ, g ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ g)
      = leverageOf g := by
    intro g
    rw [Matrix.one_mulVec]
    simp only [leverageOf, dotProduct, Fin.sum_univ_three]
    ring
  rw [hlev, hlev, hlev, hlev] at hsum
  rw [hu] at hsum
  simp only [Matrix.trace_one, Fintype.card_fin] at hsum
  push_cast at hsum
  linarith [hsum]

/-- **SOME INSIDE ATOM CARRIES A THIRD OF THE SCALE.**  Pigeonhole on the corner's
leverage-excess budget: the largest excess is at least `lam/3`. -/
theorem corner_exists_leverageExcess_ge_third (gx gy gz u : Fin 3 → ℝ) {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hu : leverageOf u = 1) :
    lam / 3 ≤ leverageOf gx - 1 ∨ lam / 3 ≤ leverageOf gy - 1
      ∨ lam / 3 ≤ leverageOf gz - 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hbudget := corner_leverageExcess_sum gx gy gz u hcorner hu
  linarith

/-- **THE CORNER PRODUCER.**  At a corner over an admissible outside pair, the
atom carrying a third of the scale strictly dominates as soon as its readings
cost less than that share.  The selection is by leverage excess alone, which the
corner equation makes explicit. -/
theorem corner_exists_tripleGapDet_pos_of_readings_cheap {a b : Fin 3 → ℝ}
    (gx gy gz u : Fin 3 → ℝ) {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hu : leverageOf u = 1) (ha : 1 < leverageOf a)
    (hmin : 0 < pairGapMinor a b)
    (hcheap : ∀ g : Fin 3 → ℝ,
      (leverageOf a + leverageOf b - 2) * ((a ⬝ᵥ g) ^ 2 + (b ⬝ᵥ g) ^ 2)
        < lam / 3 * pairGapMinor a b) :
    0 < tripleGapDet a b gx ∨ 0 < tripleGapDet a b gy
      ∨ 0 < tripleGapDet a b gz := by
  rcases corner_exists_leverageExcess_ge_third gx gy gz u hcorner hu with h | h | h
  · exact Or.inl (tripleGapDet_pos_of_leverageExcess ha hmin
      (lt_of_lt_of_le (hcheap gx) (by nlinarith [hmin, h])))
  · exact Or.inr (Or.inl (tripleGapDet_pos_of_leverageExcess ha hmin
      (lt_of_lt_of_le (hcheap gy) (by nlinarith [hmin, h]))))
  · exact Or.inr (Or.inr (tripleGapDet_pos_of_leverageExcess ha hmin
      (lt_of_lt_of_le (hcheap gz) (by nlinarith [hmin, h]))))

/-! ## 8. Where a tie forbids an atom to sit

The split prices the third atom by two things only, so setting one of them to
zero decides the triple outright.  An atom ORTHOGONAL to both members of an
admissible pair reads the pair at `(0,0)`, where the axis form vanishes -- and
then the leverage excess stands alone against a positive pair minor.  That gives
a producer with no inequality to check beyond heaviness, and a sharp geometric
constraint on every tie. -/

/-- **AN ORTHOGONAL HEAVY ATOM STRICTLY DOMINATES WITH AN ADMISSIBLE PAIR.**  The
axis form vanishes at zero readings, so the whole gap determinant is the leverage
excess priced at the pair minor.  Nothing else is needed. -/
theorem tripleGapDet_pos_of_orthogonal_heavy {a b c : Fin 3 → ℝ}
    (hmin : 0 < pairGapMinor a b) (hc : 1 < leverageOf c)
    (hac : a  ⬝ᵥ  c = 0) (hbc : b  ⬝ᵥ  c = 0) :
    0 < tripleGapDet a b c := by
  rw [tripleGapDet_eq_pairAxisForm, hac, hbc]
  have hzero : pairAxisForm a b 0 0 = 0 := by simp [pairAxisForm]
  rw [hzero]
  have : 0 < leverageOf c - 1 := by linarith
  positivity

/-- **THE PRODUCER AT A DESIGN.**  An admissible pair and any heavy atom
orthogonal to both of its members give a strictly dominating triple. -/
theorem subsetSum_posDef_of_orthogonal_heavy (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : 1 < leverageOf (D.atom x))
    (hmin : 0 < pairGapMinor (D.atom x) (D.atom y))
    (hc : 1 < leverageOf (D.atom z))
    (hac : (D.atom x)  ⬝ᵥ  (D.atom z) = 0)
    (hbc : (D.atom y)  ⬝ᵥ  (D.atom z) = 0) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef := by
  rw [subsetSum_posDef_iff_pairVocabulary D x y z hxy hxz hyz]
  exact ⟨by linarith, hmin,
    tripleGapDet_pos_of_orthogonal_heavy hmin hc hac hbc⟩

/-- **A TIE PUTS NO HEAVY ATOM ON THE NORMAL OF AN ADMISSIBLE PAIR.**  Where no
strict dominator exists, every atom orthogonal to both members of an admissible
pair has leverage at most one.  A sharp geometric constraint on tie
configurations, with no bracket and no adjugate. -/
theorem leverage_le_one_of_orthogonal_of_not_posDef (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : 1 < leverageOf (D.atom x))
    (hmin : 0 < pairGapMinor (D.atom x) (D.atom y))
    (hac : (D.atom x)  ⬝ᵥ  (D.atom z) = 0)
    (hbc : (D.atom y)  ⬝ᵥ  (D.atom z) = 0)
    (hno : ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    leverageOf (D.atom z) ≤ 1 := by
  by_contra hcon
  push Not at hcon
  exact hno (subsetSum_posDef_of_orthogonal_heavy D hxy hxz hyz ha hmin hcon hac hbc)

/-- **THE EXACT PER-TRIPLE TIE LAW.**  Rearranging the split: a triple over a pair
base fails to dominate exactly when the third atom's leverage excess, priced at
the pair minor, does not beat the cost of its two readings.  Hypothesis-free. -/
theorem tripleGapDet_nonpos_iff_excess_le_cost (a b c : Fin 3 → ℝ) :
    tripleGapDet a b c ≤ 0
      ↔ (leverageOf c - 1) * pairGapMinor a b
        ≤ -(pairAxisForm a b (a  ⬝ᵥ  c) (b  ⬝ᵥ  c)) := by
  rw [tripleGapDet_eq_pairAxisForm]
  constructor <;> intro h <;> linarith

/-- **THE TIE LAW IN LEVERAGES AND READINGS.**  Where no strict dominator exists,
every atom's leverage excess priced at an admissible pair's minor is capped by the
pair's trace against its two squared readings.  No bracket, no adjugate, no
matrix. -/
theorem leverageExcess_le_readingCost_of_not_posDef (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : 1 < leverageOf (D.atom x))
    (hmin : 0 < pairGapMinor (D.atom x) (D.atom y))
    (hno : ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    (leverageOf (D.atom z) - 1) * pairGapMinor (D.atom x) (D.atom y)
      ≤ (leverageOf (D.atom x) + leverageOf (D.atom y) - 2)
        * (((D.atom x)  ⬝ᵥ  (D.atom z)) ^ 2 + ((D.atom y)  ⬝ᵥ  (D.atom z)) ^ 2) := by
  by_contra hcon
  push Not at hcon
  exact hno (subsetSum_posDef_of_leverageExcess D hxy hxz hyz ha hmin hcon)

end Gtz
