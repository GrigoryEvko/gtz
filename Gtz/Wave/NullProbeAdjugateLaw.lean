/-
# The adjugate law: a weak dominator's pair minors ARE its null probe's squared readings

The campaign carries two arms.  The corank-two arm studies a gap `S_C - 1` of
rank one, and its landed calculus says the three INSIDE pair minors all vanish
there — the corner deletes its own triangle from the admissibility graph.  The
corank-one arm studies a gap with a null LINE, and its landed instrument is the
second invariant `e2` of the gap, whose positivity separates the two arms.  The
two facts were proved separately, in different vocabularies, by different lanes.

They are one identity.  Let `C = {a,b,c}` be a triple, let `w` be a null probe of
its gap (`S_C *ᵥ w = w`) and let `w` be a unit vector.  Write

  `e2 := pairGapMinor a b + pairGapMinor a c + pairGapMinor b c` .

Then each pair minor is `e2` times the SQUARED READING of the member the pair
leaves out:

  **`pairGapMinor b c = e2 * (a ⬝ᵥ w)^2`**
  **`pairGapMinor a c = e2 * (b ⬝ᵥ w)^2`**
  **`pairGapMinor a b = e2 * (c ⬝ᵥ w)^2`**

This is the adjugate of the Gram gap.  The Gram gap `N = Gram(C) - 1` is
singular with null vector `s = (a ⬝ᵥ w, b ⬝ᵥ w, c ⬝ᵥ w)`, its adjugate carries
the three pair minors on the diagonal, and the adjugate of a singular matrix has
rank at most one, so `adj N = e2 * s sᵀ`.  The landed
`Gtz.nullProbe_inside_total` already says `|s| = |w|`, so the three squared
readings total one and the three pair minors total `e2`.  **The normalized pair
minors of a weak dominator are a probability distribution, and that distribution
is the squared readings of the null probe.**

## What each arm gets

* **Corank two.**  A rank-one gap has `e2 = 0`, so all three pair minors vanish
  (`Gtz.pairGapMinor_eq_zero_of_secondInvariant_eq_zero`).  The corner's
  triangle deletion is one line of this law, and it needs no corner normal form
  and no axis.
* **Corank one.**  With `e2` nonzero a pair minor vanishes exactly when the
  THIRD member reads the probe at zero
  (`Gtz.pairGapMinor_eq_zero_iff_reading_eq_zero`).  A vanishing reading and a
  vanishing pair minor are the same event, in two different currencies.
* **Both.**  The three pair minors of a triple with a unit null probe all have
  the sign of `e2` (`Gtz.pairGapMinor_sign_uniform`), because each of them is
  `e2` times a square.  The landed `Gtz.pairGapMinor_nonneg_of_dominates` is the
  weak-dominator instance of that sign.

## The funnel closes on a pair-minor trigger

`Gtz.unitAtom_parallel_of_two_readings_zero` turns two vanishing readings into a
parallel pair.  Through this law, two vanishing PAIR MINORS do the same
(`Gtz.unitAtom_parallel_of_two_pairMinors_zero`), and the trigger is now written
in the hinge's own currency.  The funnel's readings are no longer an opaque
probe: they are the dominator's normalized pair minors.

[MEASURED before proving.  The law holds to `1.2e-13` at 20,000 random corank-one
weak dominators, to `1.3e-14` at 5,000 rank-one corners, and to `1.1e-14` at
20,000 SIGN-INDEFINITE symmetric gaps — so the law consumes no positivity.  At
the `(5,3)` diamond tie it holds at all eight of that tie's weak dominators, and
the squared readings there are exactly the normalized pair minors, for example
`(0.75, 0.125, 0.125)` against `(4.5, 0.75, 0.75)/6` at the triple `{0,1,2}`.]
-/
import Gtz.Wave.UnitAtomFunnel
import Gtz.Wave.InadmissiblePairSeparation
import Gtz.Wave.DiamondNeighborhoodBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The scalar core

A symmetric three-by-three matrix with a unit null vector carries its adjugate
on that vector.  Nothing here is geometric, and nothing here is positive. -/

/-- The first cross identity of the adjugate.  Two rows of the null relation
eliminate the third diagonal entry. -/
theorem adjugate_cross_first (A B C P Q R al be ga : ℝ)
    (h1 : A * al + P * be + Q * ga = 0)
    (h2 : P * al + B * be + R * ga = 0)
    (h3 : Q * al + R * be + C * ga = 0) :
    (B * C - R ^ 2) * be ^ 2 = (A * C - Q ^ 2) * al ^ 2 := by
  linear_combination (C * be) * h2 - (R * be) * h3 - (C * al) * h1 + (Q * al) * h3

/-- The second cross identity, the first one with the last two indices
interchanged. -/
theorem adjugate_cross_second (A B C P Q R al be ga : ℝ)
    (h1 : A * al + P * be + Q * ga = 0)
    (h2 : P * al + B * be + R * ga = 0)
    (h3 : Q * al + R * be + C * ga = 0) :
    (B * C - R ^ 2) * ga ^ 2 = (A * B - P ^ 2) * al ^ 2 := by
  linear_combination (B * ga) * h3 - (R * ga) * h2 - (B * al) * h1 + (P * al) * h2

/-- **THE ADJUGATE LAW, IN SCALARS.**  A symmetric three-by-three matrix with a
unit null vector has each diagonal entry of its adjugate equal to the adjugate's
trace times the corresponding squared entry of that vector.  The proof is the
two cross identities and the normalization, with no case split and no rank
hypothesis. -/
theorem adjugate_law_core (A B C P Q R al be ga : ℝ)
    (h1 : A * al + P * be + Q * ga = 0)
    (h2 : P * al + B * be + R * ga = 0)
    (h3 : Q * al + R * be + C * ga = 0)
    (hn : al ^ 2 + be ^ 2 + ga ^ 2 = 1) :
    B * C - R ^ 2
      = ((B * C - R ^ 2) + (A * C - Q ^ 2) + (A * B - P ^ 2)) * al ^ 2 := by
  have c1 := adjugate_cross_first A B C P Q R al be ga h1 h2 h3
  have c2 := adjugate_cross_second A B C P Q R al be ga h1 h2 h3
  linear_combination (-(B * C - R ^ 2)) * hn + c1 + c2

/-! ## 2. The null probe of a triple

The probe rebuilds itself from the triple with its own readings as the
coefficients, and each member reads that rebuild as one linear relation. -/

/-- **THE REPRODUCTION, FOR EVERY PROBE.**  A fixed vector of a subset sum is the
combination of that subset's atoms with its own readings as coefficients.  The
landed `Gtz.unitAtom_reproduction` is the unit-atom instance. -/
theorem nullProbe_reproduction (D : WeightedDesign m 3) {T : Finset (Fin m)}
    {w : Fin 3 → ℝ} (hfix : subsetSum D T *ᵥ w = w) :
    ∑ c ∈ T, (D.atom c ⬝ᵥ w) • D.atom c = w := by
  have hexpand : subsetSum D T *ᵥ w = ∑ c ∈ T, (D.atom c ⬝ᵥ w) • D.atom c := by
    rw [subsetSum, Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun c _ => by
      rw [atomMatrix, vecMulVec_mulVec_eq]
  rw [← hexpand]; exact hfix

/-- **THE PROBE IS FIXED, NOT MERELY NULL.**  A weak dominator whose gap form
vanishes at a probe fixes that probe.  Positive semidefiniteness turns the
scalar zero into a vector equation. -/
theorem nullProbe_mulVec_fixed (D : WeightedDesign m 3) {T : Finset (Fin m)}
    (hdom : Dominates D T) {w : Fin 3 → ℝ}
    (hnull : w ⬝ᵥ ((subsetSum D T - 1) *ᵥ w) = 0) :
    subsetSum D T *ᵥ w = w := by
  have hsym : (subsetSum D T - 1)ᵀ = subsetSum D T - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum_transpose]
  have hzero := mulVec_eq_zero_of_form_eq_zero hdom hsym hnull
  have hsplit : (subsetSum D T - 1) *ᵥ w = subsetSum D T *ᵥ w - w := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hsplit] at hzero
  have := sub_eq_zero.mp hzero
  exact this

/-- The relation the first member reads off the reproduction. -/
theorem nullProbe_row_first (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) :
    (leverageOf a - 1) * (a ⬝ᵥ w) + (a ⬝ᵥ b) * (b ⬝ᵥ w) + (a ⬝ᵥ c) * (c ⬝ᵥ w) = 0 := by
  have h := congrArg (fun v => a ⬝ᵥ v) hrep
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at h
  rw [dotProduct_self_eq_leverage] at h
  linear_combination h

/-- The relation the second member reads off the reproduction. -/
theorem nullProbe_row_second (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) :
    (a ⬝ᵥ b) * (a ⬝ᵥ w) + (leverageOf b - 1) * (b ⬝ᵥ w) + (b ⬝ᵥ c) * (c ⬝ᵥ w) = 0 := by
  have h := congrArg (fun v => b ⬝ᵥ v) hrep
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at h
  rw [dotProduct_self_eq_leverage, dotProduct_comm b a] at h
  linear_combination h

/-- The relation the third member reads off the reproduction. -/
theorem nullProbe_row_third (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) :
    (a ⬝ᵥ c) * (a ⬝ᵥ w) + (b ⬝ᵥ c) * (b ⬝ᵥ w) + (leverageOf c - 1) * (c ⬝ᵥ w) = 0 := by
  have h := congrArg (fun v => c ⬝ᵥ v) hrep
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at h
  rw [dotProduct_self_eq_leverage, dotProduct_comm c a, dotProduct_comm c b] at h
  linear_combination h

/-- **THE READINGS RESOLVE THE PROBE.**  The three squared readings total the
probe's own square.  This is the landed `Gtz.nullProbe_inside_total` written for
an explicit triple. -/
theorem nullProbe_readings_resolve (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) :
    (a ⬝ᵥ w) ^ 2 + (b ⬝ᵥ w) ^ 2 + (c ⬝ᵥ w) ^ 2 = w ⬝ᵥ w := by
  have h := congrArg (fun v => w ⬝ᵥ v) hrep
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at h
  rw [dotProduct_comm w a, dotProduct_comm w b, dotProduct_comm w c] at h
  linear_combination h

/-! ## 3. The adjugate law at a triple

The second invariant of the gap, in the campaign's pair currency. -/

/-- The second invariant of a triple's gap: the total of its three pair minors.
The landed `Gtz.pairMinor_sum_eq_secondInvariant` identifies this with the
corpus's symmetric second invariant. -/
noncomputable def pairMinorTotal (a b c : Fin 3 → ℝ) : ℝ :=
  pairGapMinor a b + pairGapMinor a c + pairGapMinor b c

/-- **THE ADJUGATE LAW, FIRST MEMBER.**  The pair minor of the last two members
is the second invariant times the squared reading of the first. -/
theorem pairGapMinor_eq_pairMinorTotal_mul_reading_first (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1) :
    pairGapMinor b c = pairMinorTotal a b c * (a ⬝ᵥ w) ^ 2 := by
  have hn : (a ⬝ᵥ w) ^ 2 + (b ⬝ᵥ w) ^ 2 + (c ⬝ᵥ w) ^ 2 = 1 := by
    rw [nullProbe_readings_resolve a b c w hrep]; exact hnorm
  have hcore := adjugate_law_core (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
    (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c) (a ⬝ᵥ w) (b ⬝ᵥ w) (c ⬝ᵥ w)
    (nullProbe_row_first a b c w hrep)
    (nullProbe_row_second a b c w hrep)
    (nullProbe_row_third a b c w hrep) hn
  rw [pairMinorTotal, pairGapMinor, pairGapMinor, pairGapMinor]
  linear_combination hcore

/-- **THE ADJUGATE LAW, SECOND MEMBER.** -/
theorem pairGapMinor_eq_pairMinorTotal_mul_reading_second (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1) :
    pairGapMinor a c = pairMinorTotal a b c * (b ⬝ᵥ w) ^ 2 := by
  have hn : (b ⬝ᵥ w) ^ 2 + (a ⬝ᵥ w) ^ 2 + (c ⬝ᵥ w) ^ 2 = 1 := by
    have := nullProbe_readings_resolve a b c w hrep
    rw [hnorm] at this; linarith
  have hcore := adjugate_law_core (leverageOf b - 1) (leverageOf a - 1) (leverageOf c - 1)
    (a ⬝ᵥ b) (b ⬝ᵥ c) (a ⬝ᵥ c) (b ⬝ᵥ w) (a ⬝ᵥ w) (c ⬝ᵥ w)
    (by linear_combination nullProbe_row_second a b c w hrep)
    (by linear_combination nullProbe_row_first a b c w hrep)
    (by linear_combination nullProbe_row_third a b c w hrep) hn
  rw [pairMinorTotal, pairGapMinor, pairGapMinor, pairGapMinor]
  linear_combination hcore

/-- **THE ADJUGATE LAW, THIRD MEMBER.** -/
theorem pairGapMinor_eq_pairMinorTotal_mul_reading_third (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1) :
    pairGapMinor a b = pairMinorTotal a b c * (c ⬝ᵥ w) ^ 2 := by
  have hn : (c ⬝ᵥ w) ^ 2 + (a ⬝ᵥ w) ^ 2 + (b ⬝ᵥ w) ^ 2 = 1 := by
    have := nullProbe_readings_resolve a b c w hrep
    rw [hnorm] at this; linarith
  have hcore := adjugate_law_core (leverageOf c - 1) (leverageOf a - 1) (leverageOf b - 1)
    (a ⬝ᵥ c) (b ⬝ᵥ c) (a ⬝ᵥ b) (c ⬝ᵥ w) (a ⬝ᵥ w) (b ⬝ᵥ w)
    (by linear_combination nullProbe_row_third a b c w hrep)
    (by linear_combination nullProbe_row_first a b c w hrep)
    (by linear_combination nullProbe_row_second a b c w hrep) hn
  rw [pairMinorTotal, pairGapMinor, pairGapMinor, pairGapMinor]
  linear_combination hcore

/-! ## 4. What the two arms read off the law -/

/-- **THE CORNER DELETES ITS TRIANGLE, IN ONE LINE.**  A vanishing second
invariant kills all three pair minors.  A rank-one gap is the corank-two arm's
whole subject, and this needs no corner normal form and no axis. -/
theorem pairGapMinor_eq_zero_of_pairMinorTotal_eq_zero (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1)
    (hzero : pairMinorTotal a b c = 0) :
    pairGapMinor a b = 0 ∧ pairGapMinor a c = 0 ∧ pairGapMinor b c = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pairGapMinor_eq_pairMinorTotal_mul_reading_third a b c w hrep hnorm, hzero, zero_mul]
  · rw [pairGapMinor_eq_pairMinorTotal_mul_reading_second a b c w hrep hnorm, hzero, zero_mul]
  · rw [pairGapMinor_eq_pairMinorTotal_mul_reading_first a b c w hrep hnorm, hzero, zero_mul]

/-- **A VANISHING PAIR MINOR IS A VANISHING READING.**  With the second invariant
nonzero, the pair minor of two members vanishes exactly when the third member
reads the probe at zero.  The corank-one arm's two currencies are the same
event. -/
theorem pairGapMinor_eq_zero_iff_reading_eq_zero (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1)
    (htotal : pairMinorTotal a b c ≠ 0) :
    pairGapMinor a b = 0 ↔ c ⬝ᵥ w = 0 := by
  rw [pairGapMinor_eq_pairMinorTotal_mul_reading_third a b c w hrep hnorm]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' htotal
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'
  · intro h; rw [h]; ring

/-- **THE THREE PAIR MINORS SHARE ONE SIGN.**  Each of them is the second
invariant times a square, so at a triple with a unit null probe they are all
nonnegative or all nonpositive.  The landed
`Gtz.pairGapMinor_nonneg_of_dominates` is the weak-dominator instance. -/
theorem pairGapMinor_sign_uniform (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1)
    (htotal : 0 ≤ pairMinorTotal a b c) :
    0 ≤ pairGapMinor a b ∧ 0 ≤ pairGapMinor a c ∧ 0 ≤ pairGapMinor b c := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pairGapMinor_eq_pairMinorTotal_mul_reading_third a b c w hrep hnorm]
    exact mul_nonneg htotal (sq_nonneg _)
  · rw [pairGapMinor_eq_pairMinorTotal_mul_reading_second a b c w hrep hnorm]
    exact mul_nonneg htotal (sq_nonneg _)
  · rw [pairGapMinor_eq_pairMinorTotal_mul_reading_first a b c w hrep hnorm]
    exact mul_nonneg htotal (sq_nonneg _)

/-- **THE NORMALIZED PAIR MINORS ARE A DISTRIBUTION.**  The three pair minors
total the second invariant, exactly as the three squared readings total one. -/
theorem pairMinorTotal_eq_pairMinorTotal_mul_reading_sum (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1) :
    pairMinorTotal a b c
      = pairMinorTotal a b c
        * ((a ⬝ᵥ w) ^ 2 + (b ⬝ᵥ w) ^ 2 + (c ⬝ᵥ w) ^ 2) := by
  have hn := nullProbe_readings_resolve a b c w hrep
  rw [hn, hnorm, mul_one]

/-! ## 5. The law at a design -/

/-- The reproduction of a probe fixed by an explicit triple. -/
theorem nullProbe_reproduction_triple (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {w : Fin 3 → ℝ}
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ w = w) :
    (D.atom x ⬝ᵥ w) • D.atom x + (D.atom y ⬝ᵥ w) • D.atom y
        + (D.atom z ⬝ᵥ w) • D.atom z = w := by
  have hsum := nullProbe_reproduction D hfix
  rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton] at hsum
  exact (add_assoc _ _ _).trans hsum

/-- **THE ADJUGATE LAW AT A DESIGN.**  All three readings at once, for a triple
of a design that fixes a unit probe. -/
theorem pairGapMinor_eq_pairMinorTotal_mul_reading_design (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {w : Fin 3 → ℝ}
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ w = w) (hnorm : w ⬝ᵥ w = 1) :
    pairGapMinor (D.atom y) (D.atom z)
        = pairMinorTotal (D.atom x) (D.atom y) (D.atom z) * (D.atom x ⬝ᵥ w) ^ 2
      ∧ pairGapMinor (D.atom x) (D.atom z)
        = pairMinorTotal (D.atom x) (D.atom y) (D.atom z) * (D.atom y ⬝ᵥ w) ^ 2
      ∧ pairGapMinor (D.atom x) (D.atom y)
        = pairMinorTotal (D.atom x) (D.atom y) (D.atom z) * (D.atom z ⬝ᵥ w) ^ 2 := by
  have hrep := nullProbe_reproduction_triple D hxy hxz hyz hfix
  exact ⟨pairGapMinor_eq_pairMinorTotal_mul_reading_first _ _ _ w hrep hnorm,
    pairGapMinor_eq_pairMinorTotal_mul_reading_second _ _ _ w hrep hnorm,
    pairGapMinor_eq_pairMinorTotal_mul_reading_third _ _ _ w hrep hnorm⟩

/-! ## 6. The funnel closes on a pair-minor trigger -/

/-- **TWO VANISHING PAIR MINORS GIVE A PARALLEL PAIR.**  At a unit atom's
dominator, a pair minor vanishes exactly when the third member is blind to the
atom.  Two of them vanish only when the atom is a multiple of the one remaining
member, and that is a hinge witness.  The landed
`Gtz.unitAtom_parallel_of_two_readings_zero` supplies the last step, and this
statement writes its trigger in the pair currency. -/
theorem unitAtom_parallel_of_two_pairMinors_zero (D : WeightedDesign (m + 1) 3)
    {a x y z : Fin (m + 1)} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (havoid : a ∉ ({x, y, z} : Finset (Fin (m + 1))))
    (hunit : leverageOf (D.atom a) = 1)
    (hfix : subsetSum D ({x, y, z} : Finset (Fin (m + 1))) *ᵥ D.atom a = D.atom a)
    (htotal : pairMinorTotal (D.atom x) (D.atom y) (D.atom z) ≠ 0)
    (hminorXY : pairGapMinor (D.atom x) (D.atom y) = 0)
    (hminorXZ : pairGapMinor (D.atom x) (D.atom z) = 0) :
    HasParallelPair D := by
  have hnorm : D.atom a ⬝ᵥ D.atom a = 1 := by
    rw [dotProduct_self_eq_leverage]; exact hunit
  obtain ⟨-, hsecond, hthird⟩ :=
    pairGapMinor_eq_pairMinorTotal_mul_reading_design D hxy hxz hyz hfix hnorm
  have hzeroZ : D.atom z ⬝ᵥ D.atom a = 0 := by
    rw [hminorXY] at hthird
    rcases mul_eq_zero.mp hthird.symm with h' | h'
    · exact absurd h' htotal
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'
  have hzeroY : D.atom y ⬝ᵥ D.atom a = 0 := by
    rw [hminorXZ] at hsecond
    rcases mul_eq_zero.mp hsecond.symm with h' | h'
    · exact absurd h' htotal
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'
  refine unitAtom_parallel_of_two_readings_zero D (c₀ := x) havoid (by simp) hfix ?_
  intro c hc hne
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact absurd rfl hne
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hzeroY
  · rw [Finset.mem_singleton] at hc; subst hc; exact hzeroZ

end Gtz
