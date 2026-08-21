/-
# The probe-free budget: Parseval read through the adjugate form

`Gtz.pairMinorTotal_mul_reading_sq` removes the null probe from a weak
dominator's readings: every vector's squared reading of the probe is the
adjugate form `pairAdjForm` at that vector's three readings of the triple.
Parseval is a statement about squared readings of an arbitrary probe, so it
transports through the elimination and becomes a conservation law with no
eigenvector in it.

  **`Gtz.pairAdjForm_weighted_budget`:  `Σ_c t_c · pairAdjForm a b c g_c = e2`**

at every weak dominator whose gap is singular, every design, every size.  The
three inside terms are the triple's own pair minors
(`Gtz.pairAdjForm_self`, and its two companions here), so the law splits:

  **`Gtz.pairAdjForm_outside_budget`:
   `Σ_{d ∉ C} t_d · pairAdjForm a b c g_d
      = (1−t_a)·q_bc + (1−t_b)·q_ac + (1−t_c)·q_ab`** .

This is the landed `Gtz.nullProbe_parseval_split` with the probe deleted from
both sides.  The outside atoms of a weak dominator carry a fixed amount of the
triple's own pair currency, and the amount is a polynomial in leverages and
inner products.

## The caps

Parseval also caps each term, because every summand is nonnegative:

* `Gtz.weight_mul_pairAdjForm_le_pairMinorTotal` — `t_d · pairAdjForm ≤ e2` .
* `Gtz.pairAdjForm_le_pairMinorTotal_mul_leverage` — `pairAdjForm ≤ e2 · l_d` ,
  Cauchy–Schwarz against the unit probe.
* `Gtz.pairAdjForm_nonneg` — the form is nonnegative wherever `e2` is.

Composed with the probe-free census
(`Gtz.pairGapMinor_le_pairAdjForm_of_dominates`) the first cap prices a
dominating swap purely in pair currency
(`Gtz.weight_mul_pairGapMinor_le_pairMinorTotal_of_dominates`):

  **an outside atom whose swap weakly dominates satisfies `t_d · q_bc ≤ e2`.**

Every quantity in that sentence is a polynomial in the design's leverages and
inner products together with one weight.  This is the shape a `(6,3)`
constraint system consumes.

[MEASURED before proving, on 3,000 designs built by WEIGHT ELIMINATION — the six
atoms are chosen first, then the weights are the unique solution of the six-by-
six Parseval system, and only positive solutions with a genuinely singular
inside gap are kept.  Budget error at most `8.5e-14`, split error at most
`3.4e-14`.  The sample count is reported because an earlier version of this
measurement filtered every draw away and reported a vacuous zero.]
-/
import Gtz.Wave.ProbeFreeHingeTrigger
import Gtz.Wave.KOneAnchor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The form at the other two members -/

/-- The adjugate form at the second member returns the pair minor of the other
two. -/
theorem pairAdjForm_self_second (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1) :
    pairAdjForm a b c b = pairGapMinor a c := by
  rw [← pairMinorTotal_mul_reading_sq a b c w b hrep hnorm]
  exact (pairGapMinor_eq_pairMinorTotal_mul_reading_second a b c w hrep hnorm).symm

/-- The adjugate form at the third member returns the pair minor of the other
two. -/
theorem pairAdjForm_self_third (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1) :
    pairAdjForm a b c c = pairGapMinor a b := by
  rw [← pairMinorTotal_mul_reading_sq a b c w c hrep hnorm]
  exact (pairGapMinor_eq_pairMinorTotal_mul_reading_third a b c w hrep hnorm).symm

/-! ## 2. The budget -/

/-- **THE PROBE-FREE PARSEVAL BUDGET.**  The weighted total of the adjugate form
over ALL atoms of the design is the triple's second invariant.  Exact at every
weak dominator with a singular gap, every design, every size, and no eigenvector
appears. -/
theorem pairAdjForm_weighted_budget (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {w : Fin 3 → ℝ}
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ w = w) (hnorm : w ⬝ᵥ w = 1) :
    ∑ d, D.weight d * pairAdjForm (D.atom x) (D.atom y) (D.atom z) (D.atom d)
      = pairMinorTotal (D.atom x) (D.atom y) (D.atom z) := by
  have hrep := nullProbe_reproduction_triple D hxy hxz hyz hfix
  have hterm : ∀ d : Fin m,
      D.weight d * pairAdjForm (D.atom x) (D.atom y) (D.atom z) (D.atom d)
        = pairMinorTotal (D.atom x) (D.atom y) (D.atom z)
          * (D.weight d * (D.atom d ⬝ᵥ w) ^ 2) := by
    intro d
    rw [← pairMinorTotal_mul_reading_sq (D.atom x) (D.atom y) (D.atom z) w
      (D.atom d) hrep hnorm]
    ring
  rw [Finset.sum_congr rfl fun d _ => hterm d, ← Finset.mul_sum,
    parseval_probe_form D w, hnorm, mul_one]

/-- The three inside terms of the budget are the triple's own pair minors. -/
theorem pairAdjForm_inside_budget (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {w : Fin 3 → ℝ}
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ w = w) (hnorm : w ⬝ᵥ w = 1) :
    ∑ d ∈ ({x, y, z} : Finset (Fin m)),
        D.weight d * pairAdjForm (D.atom x) (D.atom y) (D.atom z) (D.atom d)
      = D.weight x * pairGapMinor (D.atom y) (D.atom z)
        + D.weight y * pairGapMinor (D.atom x) (D.atom z)
        + D.weight z * pairGapMinor (D.atom x) (D.atom y) := by
  have hrep := nullProbe_reproduction_triple D hxy hxz hyz hfix
  rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton,
    pairAdjForm_self (D.atom x) (D.atom y) (D.atom z) w hrep hnorm,
    pairAdjForm_self_second (D.atom x) (D.atom y) (D.atom z) w hrep hnorm,
    pairAdjForm_self_third (D.atom x) (D.atom y) (D.atom z) w hrep hnorm]
  ring

/-- **THE PROBE-FREE PARSEVAL SPLIT.**  The outside atoms of a weak dominator
carry exactly the coweighted total of the triple's three pair minors.  This is
`Gtz.nullProbe_parseval_split` with the probe deleted from both sides. -/
theorem pairAdjForm_outside_budget (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {w : Fin 3 → ℝ}
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ w = w) (hnorm : w ⬝ᵥ w = 1) :
    ∑ d ∈ ({x, y, z} : Finset (Fin m))ᶜ,
        D.weight d * pairAdjForm (D.atom x) (D.atom y) (D.atom z) (D.atom d)
      = (1 - D.weight x) * pairGapMinor (D.atom y) (D.atom z)
        + (1 - D.weight y) * pairGapMinor (D.atom x) (D.atom z)
        + (1 - D.weight z) * pairGapMinor (D.atom x) (D.atom y) := by
  classical
  have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m))
    (fun d => D.weight d * pairAdjForm (D.atom x) (D.atom y) (D.atom z) (D.atom d))
  rw [pairAdjForm_weighted_budget D hxy hxz hyz hfix hnorm] at hsplit
  rw [pairAdjForm_inside_budget D hxy hxz hyz hfix hnorm] at hsplit
  rw [pairMinorTotal] at hsplit
  linarith

/-! ## 3. The caps -/

/-- **THE FORM IS NONNEGATIVE WHERE THE SECOND INVARIANT IS.**  Each value of the
adjugate form is the second invariant times a square. -/
theorem pairAdjForm_nonneg (a b c w v : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1)
    (htotal : 0 ≤ pairMinorTotal a b c) :
    0 ≤ pairAdjForm a b c v := by
  rw [← pairMinorTotal_mul_reading_sq a b c w v hrep hnorm]
  exact mul_nonneg htotal (sq_nonneg _)

/-- **THE WEIGHT CAP.**  Parseval is a total of nonnegative terms, so each atom's
weighted adjugate form is capped by the second invariant. -/
theorem weight_mul_pairAdjForm_le_pairMinorTotal (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {w : Fin 3 → ℝ}
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ w = w) (hnorm : w ⬝ᵥ w = 1)
    (htotal : 0 ≤ pairMinorTotal (D.atom x) (D.atom y) (D.atom z)) (d : Fin m) :
    D.weight d * pairAdjForm (D.atom x) (D.atom y) (D.atom z) (D.atom d)
      ≤ pairMinorTotal (D.atom x) (D.atom y) (D.atom z) := by
  have hrep := nullProbe_reproduction_triple D hxy hxz hyz hfix
  have hbudget := pairAdjForm_weighted_budget D hxy hxz hyz hfix hnorm
  have hnn : ∀ e ∈ Finset.univ,
      (0:ℝ) ≤ D.weight e * pairAdjForm (D.atom x) (D.atom y) (D.atom z) (D.atom e) :=
    fun e _ => mul_nonneg (D.weight_pos e).le
      (pairAdjForm_nonneg _ _ _ w _ hrep hnorm htotal)
  have hsingle := Finset.single_le_sum hnn (Finset.mem_univ d)
  rw [hbudget] at hsingle
  exact hsingle

/-- **THE CAUCHY–SCHWARZ CAP.**  Against a unit probe an atom reads at most its
own leverage, so the adjugate form is capped by the second invariant times that
leverage — with no weight. -/
theorem pairAdjForm_le_pairMinorTotal_mul_leverage (a b c w v : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1)
    (htotal : 0 ≤ pairMinorTotal a b c) :
    pairAdjForm a b c v ≤ pairMinorTotal a b c * leverageOf v := by
  rw [← pairMinorTotal_mul_reading_sq a b c w v hrep hnorm]
  have hcs : (v ⬝ᵥ w) ^ 2 ≤ leverageOf v := by
    have h := dotProduct_sq_le_mul_self v w
    rw [dotProduct_self_eq_leverage, hnorm] at h
    nlinarith [h]
  exact mul_le_mul_of_nonneg_left hcs htotal

/-! ## 4. A dominating swap priced in pair currency -/

/-- **A DOMINATING SWAP PRICES ITS OUTSIDE ATOM.**  Combining the probe-free
census with the weight cap: an outside atom whose swap weakly dominates has its
weight times the shared pair's minor capped by the second invariant.

Leverages, inner products and one weight — nothing else.  This is the constraint
a `(6,3)` tie must satisfy at every dominating swap. -/
theorem weight_mul_pairGapMinor_le_pairMinorTotal_of_dominates (D : WeightedDesign m 3)
    {x y z q : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hq : q ∉ ({x, y, z} : Finset (Fin m))) {w : Fin 3 → ℝ}
    (hnull : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ w = 0)
    (hnorm : w ⬝ᵥ w = 1)
    (hadm : 0 < pairGapMinor (D.atom y) (D.atom z))
    (hdom : Dominates D (insert q ((({x, y, z} : Finset (Fin m))).erase x))) :
    D.weight q * pairGapMinor (D.atom y) (D.atom z)
      ≤ pairMinorTotal (D.atom x) (D.atom y) (D.atom z) := by
  have hfix := mulVec_eq_of_gap_mulVec_eq_zero D _ hnull
  have hrep := nullProbe_reproduction_triple D hxy hxz hyz hfix
  have hdiag := pairGapMinor_eq_pairMinorTotal_mul_reading_first
    (D.atom x) (D.atom y) (D.atom z) w hrep hnorm
  have htot : 0 < pairMinorTotal (D.atom x) (D.atom y) (D.atom z) := by
    nlinarith [sq_nonneg (D.atom x ⬝ᵥ w), hadm, hdiag]
  have hcensus := pairGapMinor_le_pairAdjForm_of_dominates D hxy hxz hyz hq hnull
    hnorm hadm hdom
  have hcap := weight_mul_pairAdjForm_le_pairMinorTotal D hxy hxz hyz hfix hnorm
    htot.le q
  nlinarith [hcensus, hcap, (D.weight_pos q)]

end Gtz
