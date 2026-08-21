/-
# The weighted repayment trace, and where the sixth atom enters

The corank-two arm's repayment fact E2 has a landed no-go attached to it: the
corner equation together with admissibility and heaviness does NOT force a
repaying inside atom (`Gtz.repayScope_not_forced`, a kernel witness).  So a
proof must consume the Parseval equation itself -- the design weights and the
atoms OUTSIDE the dominator.  No landed law did.

This module is that consumption, in one exact identity.  Weight the three
one-inside gap determinants by the design's own inside weights and the sum
splits into corner-pair data plus a single term carried by the COMPLEMENT:

  **`Gtz.weighted_tripleGapDet_sum_compl`:**

    `sum_{c in C} t_c * tripleGapDet a b g_c`
      `= D * excess(C) - 2*D - T - axisMoment(C^c)`

with `D = pairGapMinor a b`, `T = l_a + l_b - 2`, `excess(C)` the inside
weighted leverage excess, and `axisMoment(C^c)` the pair's axis form summed
against the complement with the design weights.  Every term but the last is
corner-pair data.  The last term IS the sixth atom.

## The complement term has a sign

On an admissible pair with both atoms heavy the axis form is nonpositive at
every reading (`Gtz.pairAxisPolar_neg_nonneg`), so `axisMoment` is nonpositive
on ANY subset (`Gtz.axisMoment_nonpos`).  Hence the floor

  **`Gtz.weighted_tripleGapDet_sum_ge`:  `D*excess(C) - 2*D - T <= weighted sum`**

and with it the producer `Gtz.exists_repay_of_parseval_floor_pos`: a positive
floor names a repaying inside atom, hence a strict dominator, hence no tie.

[MEASURED, and the honest reading is that the FLOOR IS DEAD while the IDENTITY
is not.  On 40000 complement-refusing corners of the corrected chart the
identity holds to `1.407e-12`, the floor is violated `0` times -- and the floor
is positive at `0.0000%` of corners and `0.0000%` of admissible pairs.  The
corner-pair part `D*excess(C) - 2*D - T` is always negative, so the entire
weighted repayment is carried by `-axisMoment(C^c)`.  A successor must bound
that term FROM BELOW; dropping it, as every previous corner law did, loses the
whole statement.  Do not spend a round on the floor.]
-/
import Gtz.Wave.CornerRepaymentMatrix
import Gtz.Wave.KOneAnchor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. Parseval, polarized -/

/-- **PARSEVAL AT TWO PROBES.**  The weighted readings of two probes pair to the
probes' own inner product.  The landed `Gtz.parseval_probe_form` is the
diagonal; this is its polarization, and it is what converts a moment over a
subset into corner data plus a complement. -/
theorem parseval_probe_polar (D : WeightedDesign m 3) (v w : Fin 3 → ℝ) :
    ∑ c, D.weight c * ((D.atom c ⬝ᵥ v) * (D.atom c ⬝ᵥ w)) = v ⬝ᵥ w := by
  have h1 := parseval_probe_form D (v + w)
  have h2 := parseval_probe_form D v
  have h3 := parseval_probe_form D w
  have hexp : ∀ c : Fin m, D.weight c * (D.atom c ⬝ᵥ (v + w)) ^ 2
      = D.weight c * (D.atom c ⬝ᵥ v) ^ 2
        + 2 * (D.weight c * ((D.atom c ⬝ᵥ v) * (D.atom c ⬝ᵥ w)))
        + D.weight c * (D.atom c ⬝ᵥ w) ^ 2 := by
    intro c; rw [dotProduct_add]; ring
  rw [Finset.sum_congr rfl fun c _ => hexp c, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  have hrhs : (v + w) ⬝ᵥ (v + w) = v ⬝ᵥ v + 2 * (v ⬝ᵥ w) + w ⬝ᵥ w := by
    rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm w v]; ring
  rw [hrhs, h2, h3] at h1
  linarith

/-! ## 2. The two moments a pair reads off a subset -/

/-- The weighted leverage excess of a subset. -/
noncomputable def weightedExcess (D : WeightedDesign m 3) (C : Finset (Fin m)) : ℝ :=
  ∑ c ∈ C, D.weight c * (leverageOf (D.atom c) - 1)

/-- The pair's axis form, summed against a subset with the design weights.  This
is the only place the atoms outside a dominator enter the repayment. -/
noncomputable def axisMoment (D : WeightedDesign m 3) (a b : Fin 3 → ℝ)
    (C : Finset (Fin m)) : ℝ :=
  ∑ c ∈ C, D.weight c * pairAxisForm a b (a ⬝ᵥ D.atom c) (b ⬝ᵥ D.atom c)

/-- The axis moment is additive across a subset and its complement. -/
theorem axisMoment_add_compl (D : WeightedDesign m 3) (a b : Fin 3 → ℝ)
    (C : Finset (Fin m)) :
    axisMoment D a b C + axisMoment D a b Cᶜ = axisMoment D a b Finset.univ := by
  classical
  simpa [axisMoment] using
    Finset.sum_add_sum_compl C
      (fun c => D.weight c * pairAxisForm a b (a ⬝ᵥ D.atom c) (b ⬝ᵥ D.atom c))

/-- **THE TOTAL AXIS MOMENT IS CORNER-PAIR DATA.**  Over the whole design the
axis moment collapses, by Parseval, to twice the pair minor plus the pair trace,
with a sign.  No atom appears: the design has been spent. -/
theorem axisMoment_univ (D : WeightedDesign m 3) (a b : Fin 3 → ℝ) :
    axisMoment D a b Finset.univ
      = -2 * pairGapMinor a b - (leverageOf a + leverageOf b - 2) := by
  have haa := parseval_probe_form D a
  have hbb := parseval_probe_form D b
  have hab := parseval_probe_polar D a b
  have hcomm : ∀ c : Fin m, D.weight c * pairAxisForm a b (a ⬝ᵥ D.atom c) (b ⬝ᵥ D.atom c)
      = (1 - leverageOf b) * (D.weight c * (D.atom c ⬝ᵥ a) ^ 2)
        + 2 * (a ⬝ᵥ b) * (D.weight c * ((D.atom c ⬝ᵥ a) * (D.atom c ⬝ᵥ b)))
        + (1 - leverageOf a) * (D.weight c * (D.atom c ⬝ᵥ b) ^ 2) := by
    intro c
    rw [pairAxisForm, dotProduct_comm a (D.atom c), dotProduct_comm b (D.atom c)]
    ring
  rw [axisMoment, Finset.sum_congr rfl fun c _ => hcomm c, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    haa, hbb, hab]
  have hsa : a ⬝ᵥ a = leverageOf a := by
    simp only [leverageOf, dotProduct, Fin.sum_univ_three]; ring
  have hsb : b ⬝ᵥ b = leverageOf b := by
    simp only [leverageOf, dotProduct, Fin.sum_univ_three]; ring
  rw [pairGapMinor, hsa, hsb]
  ring

/-! ## 3. The weighted repayment trace -/

/-- **THE WEIGHTED SUM SPLITS.**  Termwise from the landed exact split of a gap
determinant over a pair base.  Hypothesis-free. -/
theorem weighted_tripleGapDet_sum (D : WeightedDesign m 3) (a b : Fin 3 → ℝ)
    (C : Finset (Fin m)) :
    ∑ c ∈ C, D.weight c * tripleGapDet a b (D.atom c)
      = pairGapMinor a b * weightedExcess D C + axisMoment D a b C := by
  have hterm : ∀ c : Fin m, D.weight c * tripleGapDet a b (D.atom c)
      = pairGapMinor a b * (D.weight c * (leverageOf (D.atom c) - 1))
        + D.weight c * pairAxisForm a b (a ⬝ᵥ D.atom c) (b ⬝ᵥ D.atom c) := by
    intro c; rw [tripleGapDet_eq_pairAxisForm]; ring
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_add_distrib,
    ← Finset.mul_sum, weightedExcess, axisMoment]

/-- **THE SIXTH ATOM, EXACTLY.**  The design-weighted total of the three
one-inside gap determinants is corner-pair data less the complement's own axis
moment.  This is the identity the arm's no-go demanded: everything except the
last term is available at the corner, and the last term is the outside. -/
theorem weighted_tripleGapDet_sum_compl (D : WeightedDesign m 3) (a b : Fin 3 → ℝ)
    (C : Finset (Fin m)) :
    ∑ c ∈ C, D.weight c * tripleGapDet a b (D.atom c)
      = pairGapMinor a b * weightedExcess D C - 2 * pairGapMinor a b
        - (leverageOf a + leverageOf b - 2) - axisMoment D a b Cᶜ := by
  have hsplit := axisMoment_add_compl D a b C
  have huniv := axisMoment_univ D a b
  rw [weighted_tripleGapDet_sum D a b C]
  rw [huniv] at hsplit
  linarith

/-! ## 4. The complement term has a sign, and the floor it gives -/

/-- **THE AXIS MOMENT IS NONPOSITIVE.**  On an admissible pair with both atoms
heavy, every summand is the pair's axis form at a reading, and that form is
nonpositive.  True on every subset, with no design hypothesis beyond positive
weights. -/
theorem axisMoment_nonpos (D : WeightedDesign m 3) {a b : Fin 3 → ℝ}
    (ha : 1 ≤ leverageOf a) (hb : 1 ≤ leverageOf b)
    (hmin : 0 ≤ pairGapMinor a b) (C : Finset (Fin m)) :
    axisMoment D a b C ≤ 0 := by
  refine Finset.sum_nonpos fun c _ => ?_
  have hform : pairAxisForm a b (a ⬝ᵥ D.atom c) (b ⬝ᵥ D.atom c) ≤ 0 := by
    have := pairAxisPolar_neg_nonneg (la := leverageOf a) (lb := leverageOf b)
      (p := a ⬝ᵥ b) ha hb (by rwa [pairGapMinor] at hmin)
      (a ⬝ᵥ D.atom c) (b ⬝ᵥ D.atom c)
    rw [pairAxisPolar_diag] at this
    rwa [pairAxisForm]
  exact mul_nonpos_of_nonneg_of_nonpos (D.weight_pos c).le hform

/-- **THE PARSEVAL FLOOR.**  Dropping the complement's axis moment -- the only
term that reads an atom outside the dominator -- leaves a lower bound in
corner-pair data alone.

[MEASURED: this floor is POSITIVE at `0.0000%` of complement-refusing corners.
It is a true theorem and a dead instrument.  The whole weighted repayment is
carried by the complement term that the floor throws away.] -/
theorem weighted_tripleGapDet_sum_ge (D : WeightedDesign m 3) {a b : Fin 3 → ℝ}
    (ha : 1 ≤ leverageOf a) (hb : 1 ≤ leverageOf b)
    (hmin : 0 ≤ pairGapMinor a b) (C : Finset (Fin m)) :
    pairGapMinor a b * weightedExcess D C - 2 * pairGapMinor a b
        - (leverageOf a + leverageOf b - 2)
      ≤ ∑ c ∈ C, D.weight c * tripleGapDet a b (D.atom c) := by
  have hsign := axisMoment_nonpos D ha hb hmin Cᶜ
  have := weighted_tripleGapDet_sum_compl D a b C
  linarith

/-! ## 5. The producer -/

/-- **A POSITIVE WEIGHTED TRACE NAMES A REPAYING ATOM.**  The design weights are
strictly positive, so a positive weighted total over a subset has a positive
term in it. -/
theorem exists_repay_of_weighted_trace_pos (D : WeightedDesign m 3) (a b : Fin 3 → ℝ)
    {C : Finset (Fin m)}
    (hpos : 0 < ∑ c ∈ C, D.weight c * tripleGapDet a b (D.atom c)) :
    ∃ c ∈ C, 0 < tripleGapDet a b (D.atom c) := by
  by_contra hcon
  push Not at hcon
  have : ∑ c ∈ C, D.weight c * tripleGapDet a b (D.atom c) ≤ 0 :=
    Finset.sum_nonpos fun c hc =>
      mul_nonpos_of_nonneg_of_nonpos (D.weight_pos c).le (hcon c hc)
  linarith

/-- **THE PARSEVAL PRODUCER.**  A positive corner-pair floor forces a repaying
inside atom.  Stated for the record and for composition: the floor is measured
never to fire, so the useful content is
`Gtz.weighted_tripleGapDet_sum_compl`, which says exactly how much the
complement must supply. -/
theorem exists_repay_of_parseval_floor_pos (D : WeightedDesign m 3) {a b : Fin 3 → ℝ}
    (ha : 1 ≤ leverageOf a) (hb : 1 ≤ leverageOf b)
    (hmin : 0 ≤ pairGapMinor a b) {C : Finset (Fin m)}
    (hfloor : 0 < pairGapMinor a b * weightedExcess D C - 2 * pairGapMinor a b
        - (leverageOf a + leverageOf b - 2)) :
    ∃ c ∈ C, 0 < tripleGapDet a b (D.atom c) :=
  exists_repay_of_weighted_trace_pos D a b
    (lt_of_lt_of_le hfloor (weighted_tripleGapDet_sum_ge D ha hb hmin C))

/-- **WHAT A TIE OWES THE COMPLEMENT.**  Where no inside atom repays an
admissible pair, the complement's axis moment is pinned from below by
corner-pair data.  This is the exact obligation a corank-two corner tie carries,
and it is the first one written in terms of the atoms OUTSIDE the dominator. -/
theorem axisMoment_compl_ge_of_no_repay (D : WeightedDesign m 3) (a b : Fin 3 → ℝ)
    {C : Finset (Fin m)}
    (hno : ∀ c ∈ C, tripleGapDet a b (D.atom c) ≤ 0) :
    pairGapMinor a b * weightedExcess D C - 2 * pairGapMinor a b
        - (leverageOf a + leverageOf b - 2)
      ≤ axisMoment D a b Cᶜ := by
  have hsum : ∑ c ∈ C, D.weight c * tripleGapDet a b (D.atom c) ≤ 0 :=
    Finset.sum_nonpos fun c hc =>
      mul_nonpos_of_nonneg_of_nonpos (D.weight_pos c).le (hno c hc)
  have := weighted_tripleGapDet_sum_compl D a b C
  linarith

end Gtz
