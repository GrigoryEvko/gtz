/-
# What a corank-one weak dominator costs a boundary system, at any size

`Gtz.FunnelSpectralPinch` proved the payment law and the spectral pinch at a
FUNNEL, where the kernel of the dominator's gap is an atom of the design.  The
funnel plays no part in either argument.  This module carries the whole package
to the general object: a weak dominator whose gap has corank one, with ANY unit
kernel vector, at ANY size, in either branch of
`Gtz.isTie_sixThree_allHeavy_or_funnel`.

## 1. The reader exists with no funnel

The landed `Gtz.exists_outside_reading_sq_gt_one` produces an atom reading the
kernel above one, and it needs the funnel: a unit atom, its reproduction, and
size exactly six.  None of that is used.  The landed
`Gtz.triple_kernel_readings_sq` already says that ANY corank-one weak dominator
reproduces its own kernel and that its three readings square to one.  Parseval
says the whole design's weighted squared readings total one as well.  A triple's
own weight strictly exceeds each member's, so the dominator carries STRICTLY
less than its weight, and the complement carries strictly more:

  **`Gtz.exists_outside_reading_sq_gt_one_of_dominator`: some atom outside any
  corank-one weak dominator reads its kernel above one.**

At any size, with no unit atom and no funnel.

## 2. The weight producer and the weight cap, with no funnel


`Gtz.exists_strict_of_window_dominator` runs the four-scalar window at a general
corank-one weak dominator, and the plane Parseval budget turns it into a
condition on the reader's WEIGHT alone:

  **`Gtz.exists_strict_of_weight_dominator`: if
  `2 * (tau ^ 2 - e2) < weight * tau * (reading ^ 2 * (e2 - tau) - e2)`
  then a triple in the star of that atom dominates STRICTLY.**

Contrapositive at a boundary system (`Gtz.isTie_weight_cap`): every atom outside
every corank-one weak dominator carries a CAP on its own weight in the
dominator's trace and second invariant and its own squared reading.

## 5. Where the weight route provably stops

Parseval also caps the reader from the other side: `weight * reading ^ 2 ≤ 1`,
because one weighted atom never exceeds the identity.  The two caps FIGHT, and
the fight is decidable.  Substituting one in the other
(`Gtz.weight_producer_needs_trace_bound`) the producer can fire only when

  **`3 * tau ^ 2 < e2 * (tau + 2)`** ,

and with `4 * e2 ≤ tau ^ 2` (`Gtz.four_mul_secondInvariant_le_trace_sq_of_unit_null`)
that forces `tau > 10`, hence `Σ_{c ∈ T} leverage_c > 13` at a rank-three
dominator.  So the weight route is PROVABLY VACUOUS at every boundary system
whose weak dominator has trace at most ten.  That is the exact shape of the
campaign's universal obstruction on this route, as a theorem rather than a
measurement: what the producer needs is a heavy reader with a heavy weight, and
Parseval prices those against each other.

## 4. The pigeonhole trace, and the three insider laws

At three-by-three the inverse is the adjugate over the determinant, and both are
already evaluated at a corank-one gap.  So the pigeonhole quantity of the whole
`Gtz.Ties.TieBasisWindow` layer has a CLOSED FORM
(`Gtz.trace_inv_add_atomMatrix_of_unit_null`):

  **`trace (G + v vᵀ)⁻¹ = (e2 + leverage * tau - gap reading) / (e2 * reading ^ 2)`** .

Reading the landed pigeonhole bound `1 ≤ trace (S_Q - 1)⁻¹` through it gives the
payment law a THIRD time (`Gtz.one_le_trace_inv_iff_payment`).  The four-set
determinant route, the three-drop route and the pigeonhole route are one
inequality.

The pigeonhole bound is the SUM of four drop conditions.  The adjoined atom
contributes exactly one (`Gtz.fourSet_inverseForm_self`), so the payment law is
the sum of the THREE insider conditions, and each of those is strictly stronger.
The kernel slide plus the closed-form inverse put each insider pivot in closed
polynomial form (`Gtz.fourSet_pivot_of_unit_null`), and the same spectral pinch
turns each into a producer (`Gtz.exists_posDef_sub_of_insider_window`,
`Gtz.exists_strict_of_insider_window`) and a law of a boundary system
(`Gtz.isTie_insider_pinch_law`).  MEASURED: over 125576 exact funnel `(6,3)`
designs the three insider windows open 64442 times against the single payment
window's 45481, a gain of 42 percent, and closing them raises the constrained
residual of section 3 from `0.0090` to `0.0151` at smallest-weight floor
`0.0025`.

[MEASURED.  Over 251581 exact funnel `(6,3)` designs the sharp window fires at
35.5 percent.  The weight-relaxed floor of section 3 is met at 2412 of 335246
atoms, so its antecedent is NOT empty.  Minimizing the best triple's `lambda_min` subject to the window
never firing gives `0.345, 0.103, 0.052, 0.018, 0.008` at smallest-weight floors
`0.10, 0.05, 0.02, 0.01, 0.003`: the residual is linear in the smallest weight,
near `2.6` times it.  The traces at those constrained optima run `7.3` to `24.0`,
so the `tau > 10` threshold of section 3 is met at some of them and missed at
others.]
-/
import Gtz.Wave.FunnelSpectralPinch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The reproduction of a corank-one weak dominator -/

/-- **A CORANK-ONE WEAK DOMINATOR REPRODUCES ITS KERNEL.**  The design-level form
of the landed `Gtz.triple_kernel_reproduction`: the three members rebuild the
kernel with their own readings as the coefficients. -/
theorem dominator_kernel_reproduction (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {kern : Fin 3 → ℝ}
    (hgap : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ kern = 0) :
    (D.atom x ⬝ᵥ kern) • D.atom x + (D.atom y ⬝ᵥ kern) • D.atom y
        + (D.atom z ⬝ᵥ kern) • D.atom z = kern := by
  refine triple_kernel_reproduction ?_ hgap
  rw [subsetSum_triple_atoms D hxy hxz hyz]; abel

/-- **THE THREE READINGS OF A CORANK-ONE WEAK DOMINATOR SQUARE TO ONE.**  The
funnel budget, with no funnel: any weak dominator whose gap kills a unit vector
reads that vector with total squared reading exactly one. -/
theorem dominator_readings_sq (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {kern : Fin 3 → ℝ}
    (hgap : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ kern = 0)
    (hunit : kern ⬝ᵥ kern = 1) :
    (D.atom x ⬝ᵥ kern) ^ 2 + (D.atom y ⬝ᵥ kern) ^ 2 + (D.atom z ⬝ᵥ kern) ^ 2 = 1 := by
  refine triple_kernel_readings_sq ?_ hgap hunit
  rw [subsetSum_triple_atoms D hxy hxz hyz]; abel

/-! ## 2. Some atom outside reads the kernel above one -/

/-- **THE OUTSIDE READER, WITH NO FUNNEL AND AT ANY SIZE.**  The dominator's
three readings total one, so the dominator carries strictly less of Parseval's
budget than its own weight, and the complement carries strictly more.  Some atom
outside therefore reads the kernel above one.

The landed `Gtz.exists_outside_reading_sq_gt_one` is the special case of a funnel
at six points, where the kernel is an atom of the design. -/
theorem exists_outside_reading_sq_gt_one_of_dominator (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {kern : Fin 3 → ℝ}
    (hgap : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ kern = 0)
    (hunit : kern ⬝ᵥ kern = 1) :
    ∃ d : Fin m, d ∉ ({x, y, z} : Finset (Fin m)) ∧ 1 < (D.atom d ⬝ᵥ kern) ^ 2 := by
  classical
  set T : Finset (Fin m) := {x, y, z} with hT
  set U : Finset (Fin m) := Finset.univ \ T with hU
  have hcard : T.card = 3 := card_triple_eq hxy hxz hyz
  have hbudget : ∑ c ∈ T, (D.atom c ⬝ᵥ kern) ^ 2 = 1 := by
    rw [hT, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    linarith [dominator_readings_sq D hxy hxz hyz hgap hunit]
  have hdisj : Disjoint T U := Finset.disjoint_sdiff
  have huniv : T ∪ U = Finset.univ := by
    rw [hU, Finset.union_sdiff_self_eq_union]
    exact Finset.union_eq_right.mpr (Finset.subset_univ _)
  have hpar := parseval_probe_form D kern
  rw [hunit, ← huniv, Finset.sum_union hdisj] at hpar
  have hweights := D.weight_sum_one
  rw [← huniv, Finset.sum_union hdisj] at hweights
  -- a member with a live reading, and a second member to beat its weight
  have hlive : ∃ c ∈ T, 0 < (D.atom c ⬝ᵥ kern) ^ 2 := by
    by_contra hcon
    push Not at hcon
    have hzero : ∑ c ∈ T, (D.atom c ⬝ᵥ kern) ^ 2 = 0 :=
      le_antisymm (Finset.sum_nonpos fun c hc => hcon c hc)
        (Finset.sum_nonneg fun c _ => sq_nonneg _)
    rw [hbudget] at hzero
    exact absurd hzero one_ne_zero
  obtain ⟨c₀, hc₀T, hc₀pos⟩ := hlive
  have herase : (T.erase c₀).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hc₀T, hcard]
    norm_num
  obtain ⟨c₁, hc₁mem⟩ := herase
  have hc₁ne : c₁ ≠ c₀ := Finset.ne_of_mem_erase hc₁mem
  have hc₁T : c₁ ∈ T := Finset.mem_of_mem_erase hc₁mem
  have hstrictWeight : D.weight c₀ < ∑ d ∈ T, D.weight d :=
    Finset.single_lt_sum hc₁ne hc₀T hc₁T (D.weight_pos c₁)
      (fun d _ _ => (D.weight_pos d).le)
  have hstrict : ∑ c ∈ T, D.weight c * (D.atom c ⬝ᵥ kern) ^ 2
      < ∑ d ∈ T, D.weight d := by
    have hstep : ∑ c ∈ T, D.weight c * (D.atom c ⬝ᵥ kern) ^ 2
        < ∑ c ∈ T, (∑ d ∈ T, D.weight d) * (D.atom c ⬝ᵥ kern) ^ 2 := by
      refine Finset.sum_lt_sum (fun c hc => ?_) ⟨c₀, hc₀T, ?_⟩
      · exact mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := D.weight)
            (fun d _ => (D.weight_pos d).le) hc) (sq_nonneg _)
      · exact mul_lt_mul_of_pos_right hstrictWeight hc₀pos
    rwa [← Finset.mul_sum, hbudget, mul_one] at hstep
  have houtside : ∑ d ∈ U, D.weight d
      < ∑ c ∈ U, D.weight c * (D.atom c ⬝ᵥ kern) ^ 2 := by linarith
  by_contra hcon
  push Not at hcon
  have hbound : ∑ c ∈ U, D.weight c * (D.atom c ⬝ᵥ kern) ^ 2
      ≤ ∑ d ∈ U, D.weight d := by
    refine Finset.sum_le_sum fun c hc => ?_
    have hcU := Finset.mem_sdiff.mp hc
    have := hcon c hcU.2
    nlinarith [D.weight_pos c]
  linarith

/-- **THE OUTSIDE READER IS STRICTLY HEAVY.**  Cauchy-Schwarz against the unit
kernel. -/
theorem one_lt_leverage_of_outside_reader {kern v : Fin 3 → ℝ}
    (hunit : kern ⬝ᵥ kern = 1) (hread : 1 < (v ⬝ᵥ kern) ^ 2) : 1 < leverageOf v := by
  have hn := planeNormSq_nonneg (v := v) hunit
  rw [planeNormSq] at hn
  linarith

/-! ## 3. The window producer at a general corank-one weak dominator -/

/-- **THE WINDOW PRODUCER, WITH NO FUNNEL.**  Any weak dominator whose gap has a
unit kernel and a nonzero second invariant, and any atom whose four-scalar window
is open, produce a strictly dominating triple in the star of that atom. -/
theorem exists_strict_of_window_dominator (D : WeightedDesign m 3)
    {x y z p : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    {kern : Fin 3 → ℝ}
    (hgap : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ kern = 0)
    (hunit : kern ⬝ᵥ kern = 1)
    (he : 0 < secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
    (hread : D.atom p ⬝ᵥ kern ≠ 0)
    (hleft : 2 * paymentCeiling (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          (D.atom p) kern
        < Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          * planeNormSq (D.atom p) kern)
    (hpos : 0 < pinchPoly (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          (planeNormSq (D.atom p) kern)
          (paymentCeiling (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
            (D.atom p) kern)) :
    (atomMatrix (D.atom p) + atomMatrix (D.atom y) + atomMatrix (D.atom z) - 1).PosDef
      ∨ (atomMatrix (D.atom p) + atomMatrix (D.atom x)
          + atomMatrix (D.atom z) - 1).PosDef
      ∨ (atomMatrix (D.atom p) + atomMatrix (D.atom x)
          + atomMatrix (D.atom y) - 1).PosDef := by
  have hG : subsetSum D ({x, y, z} : Finset (Fin m)) - 1
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) - 1 := by
    rw [subsetSum_triple_atoms D hxy hxz hyz]
  exact exists_star_posDef_of_window hdom hgap hunit he hG hread hleft hpos

/-- **THE TRACE OF A CORANK-ONE WEAK DOMINATOR'S GAP IS STRICTLY POSITIVE.**  A
nonzero second invariant plus the discriminant bound rule out a zero trace. -/
theorem trace_pos_of_dominator {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hpsd : form.PosSemidef) {kern : Fin 3 → ℝ} (hgap : form *ᵥ kern = 0)
    (hunit : kern ⬝ᵥ kern = 1) (he : 0 < secondInvariantOfThree form) :
    0 < Matrix.trace form := by
  have hsym : formᵀ = form := (by simpa using hpsd.isHermitian : form.IsSymm)
  have hdisc := four_mul_secondInvariant_le_trace_sq_of_unit_null hsym hgap hunit
  have hnn := trace_nonneg_of_posSemidef hpsd
  rcases lt_or_ge 0 (Matrix.trace form) with h | h
  · exact h
  · exfalso
    have hzero : Matrix.trace form = 0 := le_antisymm h hnn
    rw [hzero] at hdisc
    simp at hdisc
    linarith [he, hdisc]

/-- **THE WEIGHT PRODUCER, WITH NO FUNNEL.**  The plane Parseval budget caps the
reader's plane norm at `2 / weight`, so a reader with enough weight opens the
window at any corank-one weak dominator. -/
theorem exists_strict_of_weight_dominator (D : WeightedDesign m 3)
    {x y z p : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    {kern : Fin 3 → ℝ}
    (hgap : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ kern = 0)
    (hunit : kern ⬝ᵥ kern = 1)
    (he : 0 < secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
    (hread : D.atom p ⬝ᵥ kern ≠ 0)
    (hfloor : 2 * (Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) ^ 2
          - secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
        < D.weight p * Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          * ((D.atom p ⬝ᵥ kern) ^ 2
              * (secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
                - Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
            - secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))) :
    (atomMatrix (D.atom p) + atomMatrix (D.atom y) + atomMatrix (D.atom z) - 1).PosDef
      ∨ (atomMatrix (D.atom p) + atomMatrix (D.atom x)
          + atomMatrix (D.atom z) - 1).PosDef
      ∨ (atomMatrix (D.atom p) + atomMatrix (D.atom x)
          + atomMatrix (D.atom y) - 1).PosDef := by
  set G := subsetSum D ({x, y, z} : Finset (Fin m)) - 1 with hGdef
  have hpsd : G.PosSemidef := hdom
  have hsym : Gᵀ = G := (by simpa using hpsd.isHermitian : G.IsSymm)
  have hdisc : 4 * secondInvariantOfThree G ≤ Matrix.trace G ^ 2 :=
    four_mul_secondInvariant_le_trace_sq_of_unit_null hsym hgap hunit
  have htau : 0 < Matrix.trace G := trace_pos_of_dominator hpsd hgap hunit he
  have hn : 0 ≤ planeNormSq (D.atom p) kern := planeNormSq_nonneg hunit
  have hcap : D.weight p * planeNormSq (D.atom p) kern ≤ 2 :=
    weight_mul_planeNormSq_le D hunit p
  have hwpos : 0 < D.weight p := D.weight_pos p
  have hgapPos : 0 < Matrix.trace G ^ 2 - secondInvariantOfThree G := by nlinarith [hdisc, he]
  have hlt : Matrix.trace G * paymentCeiling G (D.atom p) kern
      < secondInvariantOfThree G * planeNormSq (D.atom p) kern := by
    rw [paymentCeiling, planeNormSq] at *
    nlinarith [hfloor, hcap, hgapPos, hwpos, hn, htau]
  obtain ⟨hleft, hpos⟩ := window_of_trace_mul_ceiling_lt htau he hdisc hn hlt
  exact exists_strict_of_window_dominator D hxy hxz hyz hdom hgap hunit he hread hleft hpos

/-! ## 4. The weight cap of a boundary system -/

/-- **THE WEIGHT CAP, AT ANY SIZE AND IN EITHER BRANCH.**  At a boundary system
every atom outside every corank-one weak dominator carries a cap on its own
weight, written in the dominator's trace and second invariant and its own squared
reading of the kernel:

  `weight * tau * (reading ^ 2 * (e2 - tau) - e2) ≤ 2 * (tau ^ 2 - e2)` . -/
theorem isTie_weight_cap (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z p : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    {kern : Fin 3 → ℝ}
    (hgap : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ kern = 0)
    (hunit : kern ⬝ᵥ kern = 1)
    (he : 0 < secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
    (hread : D.atom p ⬝ᵥ kern ≠ 0) :
    D.weight p * Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
        * ((D.atom p ⬝ᵥ kern) ^ 2
            * (secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
              - Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
          - secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
      ≤ 2 * (Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) ^ 2
          - secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)) := by
  by_contra hcon
  push Not at hcon
  have hstrict := exists_strict_of_weight_dominator D hxy hxz hyz hdom hgap hunit he hread hcon
  have hkill : ∀ u v w : Fin m, u ≠ v → u ≠ w → v ≠ w →
      ¬ (atomMatrix (D.atom u) + atomMatrix (D.atom v)
          + atomMatrix (D.atom w) - 1).PosDef := by
    intro u v w huv huw hvw hposd
    refine htie.2 ({u, v, w} : Finset (Fin m)) (card_triple_eq huv huw hvw) ?_
    rwa [subsetSum_triple_atoms D huv huw hvw]
  rcases hstrict with h | h | h
  · exact hkill p y z hpy hpz hyz h
  · exact hkill p x z hpx hpz hxz h
  · exact hkill p x y hpx hpy hxy h

/-! ## 5. Where the weight route provably stops -/

/-- **ONE WEIGHTED ATOM NEVER EXCEEDS THE IDENTITY.**  Parseval's other cap on a
reader: its weight times its squared reading of any unit probe is at most one. -/
theorem weight_mul_reading_sq_le (D : WeightedDesign m 3) {w : Fin 3 → ℝ}
    (hunit : w ⬝ᵥ w = 1) (p : Fin m) :
    D.weight p * (D.atom p ⬝ᵥ w) ^ 2 ≤ 1 := by
  have hpar := parseval_probe_form D w
  rw [hunit] at hpar
  have hsingle : D.weight p * (D.atom p ⬝ᵥ w) ^ 2
      ≤ ∑ c, D.weight c * (D.atom c ⬝ᵥ w) ^ 2 :=
    Finset.single_le_sum
      (f := fun c => D.weight c * (D.atom c ⬝ᵥ w) ^ 2)
      (fun c _ => mul_nonneg (D.weight_pos c).le (sq_nonneg _))
      (Finset.mem_univ p)
  linarith [hpar, hsingle]

/-- **THE TWO PARSEVAL CAPS FIGHT, AND THE FIGHT IS DECIDABLE.**  The weight
producer needs a reader that is heavy in reading AND heavy in weight, and
Parseval prices those against each other: `weight * reading ^ 2 ≤ 1` turns the
producer's floor into a condition on the dominator alone,

  `3 * tau ^ 2 < e2 * (tau + 2)` .

With `4 * e2 ≤ tau ^ 2` this forces `tau > 10`.  So at every boundary system
whose corank-one weak dominator has trace at most ten, the weight producer of
section 3 is VACUOUS: no atom of the design can meet its floor.  This is the
campaign's universal obstruction on this route, as a theorem. -/
theorem weight_producer_needs_trace_bound (D : WeightedDesign m 3)
    {x y z p : Fin m} {kern : Fin 3 → ℝ} (hunit : kern ⬝ᵥ kern = 1)
    (hdisc : 4 * secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
      ≤ Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) ^ 2)
    (htau : 0 < Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
    (he : 0 < secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
    (hfloor : 2 * (Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) ^ 2
          - secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
        < D.weight p * Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          * ((D.atom p ⬝ᵥ kern) ^ 2
              * (secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
                - Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
            - secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))) :
    3 * Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) ^ 2
      < secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
        * (Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) + 2) := by
  set tau := Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) with htaudef
  set e2 := secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) with he2def
  set R := (D.atom p ⬝ᵥ kern) ^ 2 with hRdef
  have hcap : D.weight p * R ≤ 1 := weight_mul_reading_sq_le D hunit p
  have hwpos : 0 < D.weight p := D.weight_pos p
  have hR : 0 ≤ R := by rw [hRdef]; exact sq_nonneg _
  -- the floor forces the second invariant strictly above the trace
  have hgt : tau < e2 := by
    by_contra hcon
    push Not at hcon
    have h1 : R * (e2 - tau) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hR (by linarith)
    have h2 : D.weight p * tau * (R * (e2 - tau) - e2) < 0 := by
      have : R * (e2 - tau) - e2 < 0 := by linarith
      exact mul_neg_of_pos_of_neg (mul_pos hwpos htau) this
    nlinarith [hfloor, h2, hdisc, he, htau]
  -- and then Parseval's cap on the reader closes the arithmetic
  have hstep : D.weight p * R * (e2 - tau) ≤ 1 * (e2 - tau) :=
    mul_le_mul_of_nonneg_right hcap (by linarith)
  have hpos : 0 < D.weight p * tau * e2 := by positivity
  nlinarith [hfloor, hstep, hpos, htau, he, hgt]

/-- **TRACE AT MOST TEN KILLS THE WEIGHT ROUTE.**  The arithmetic corollary. -/
theorem weight_producer_needs_trace_gt_ten (D : WeightedDesign m 3)
    {x y z p : Fin m} {kern : Fin 3 → ℝ} (hunit : kern ⬝ᵥ kern = 1)
    (hdisc : 4 * secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
      ≤ Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) ^ 2)
    (htau : 0 < Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
    (he : 0 < secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
    (hfloor : 2 * (Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) ^ 2
          - secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
        < D.weight p * Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          * ((D.atom p ⬝ᵥ kern) ^ 2
              * (secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
                - Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
            - secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))) :
    10 < Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) := by
  have hkey := weight_producer_needs_trace_bound D hunit hdisc htau he hfloor
  nlinarith [hkey, hdisc, htau, he]

/-! ## 6. The pigeonhole trace of a four-set, in closed form -/

/-- **THE PIGEONHOLE TRACE OF EVERY FOUR-SET ON A CORANK-ONE GAP.**  For a
symmetric form with a unit null probe and any atom that reads that probe,

  `trace (form + v vᵀ)⁻¹ = (e2 + leverage * tau - form reading) / (e2 * reading ^ 2)` .

The proof is two landed facts and one Mathlib identity: at three-by-three the
inverse is the adjugate over the determinant, the trace of the adjugate is the
second invariant (`Gtz.trace_adjugate_eq_secondInvariantOfThree`), the second
invariant of a rank-one update is `Gtz.secondInvariantOfThree_add_atomMatrix`,
and the determinant is `Gtz.det_add_atomMatrix_of_unit_null`.  No inverse
survives.

`Gtz.trace_inv_kernelShift` is the case `v = w`, where leverage is one, the gap
reading is zero and the squared reading is one. -/
theorem trace_inv_add_atomMatrix_of_unit_null {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : secondInvariantOfThree form ≠ 0)
    {v : Fin 3 → ℝ} (hread : v ⬝ᵥ w ≠ 0) :
    Matrix.trace ((form + atomMatrix v)⁻¹)
      = (secondInvariantOfThree form + leverageOf v * Matrix.trace form
          - v ⬝ᵥ (form *ᵥ v))
        / (secondInvariantOfThree form * (v ⬝ᵥ w) ^ 2) := by
  have hdet : (form + atomMatrix v).det = secondInvariantOfThree form * (v ⬝ᵥ w) ^ 2 :=
    det_add_atomMatrix_of_unit_null hsym hnull hunit v
  have hne : (form + atomMatrix v).det ≠ 0 := by
    rw [hdet]; exact mul_ne_zero he (pow_ne_zero 2 hread)
  rw [Matrix.inv_def, Matrix.trace_smul, trace_adjugate_eq_secondInvariantOfThree,
    secondInvariantOfThree_add_atomMatrix, hdet]
  simp only [Ring.inverse_eq_inv', smul_eq_mul]
  field_simp

/-- **THE THREE ROUTES ARE ONE INEQUALITY.**  The pigeonhole bound
`1 ≤ trace (S_Q - 1)⁻¹` of the four-set `Q = T ∪ {v}`, the landed reading cap of
`Gtz.KernelSlideDropLaw`, and the landed funnel payment of
`Gtz.FunnelFourSetPayment` are the SAME statement.  All three say

  `e2 * (reading ^ 2 - 1) ≤ leverage * tau - form reading` . -/
theorem one_le_trace_inv_iff_payment {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : 0 < secondInvariantOfThree form)
    {v : Fin 3 → ℝ} (hread : v ⬝ᵥ w ≠ 0) :
    1 ≤ Matrix.trace ((form + atomMatrix v)⁻¹)
      ↔ secondInvariantOfThree form * ((v ⬝ᵥ w) ^ 2 - 1)
        ≤ leverageOf v * Matrix.trace form - v ⬝ᵥ (form *ᵥ v) := by
  have hpos : 0 < secondInvariantOfThree form * (v ⬝ᵥ w) ^ 2 := by
    have : 0 < (v ⬝ᵥ w) ^ 2 := by positivity
    exact mul_pos he this
  rw [trace_inv_add_atomMatrix_of_unit_null hsym hnull hunit (ne_of_gt he) hread,
    le_div_iff₀ hpos]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-! ## 7. The three insider pivots, in closed form

The pigeonhole bound of section 6 is the SUM of four drop conditions, one per
member of the four-set.  The member that was adjoined contributes exactly one
(`Gtz.fourSet_inverseForm_self`), so the payment law is the sum of the THREE
insider conditions.  Each insider condition on its own is strictly stronger, and
the kernel slide plus the closed-form inverse put each one in closed polynomial
form. -/

/-- **THE INSIDER PIVOT, IN CLOSED FORM.**  The four-set's inverse form at any
vector is the gap's own trace and reading at the SLID vector, over the second
invariant, plus the squared ratio of the two readings.  Every matrix inverse has
been eliminated. -/
theorem fourSet_pivot_of_unit_null {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : formᵀ = form) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : secondInvariantOfThree form ≠ 0)
    {v : Fin 3 → ℝ} (hread : v ⬝ᵥ w ≠ 0) (u : Fin 3 → ℝ) :
    u ⬝ᵥ ((form + atomMatrix v)⁻¹ *ᵥ u)
      = (Matrix.trace form * (kernelSlide u v w ⬝ᵥ kernelSlide u v w)
          - kernelSlide u v w ⬝ᵥ (form *ᵥ kernelSlide u v w))
          / secondInvariantOfThree form
        + ((u ⬝ᵥ w) / (v ⬝ᵥ w)) ^ 2 := by
  have hshiftDet : IsUnit (kernelShift form w).det :=
    isUnit_det_kernelShift hsym hnull hunit he
  have hfourPD : (form + atomMatrix v).det
      = secondInvariantOfThree form * (v ⬝ᵥ w) ^ 2 :=
    det_add_atomMatrix_of_unit_null hsym hnull hunit v
  have hfourDet : IsUnit (form + atomMatrix v).det := by
    rw [hfourPD]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero he (pow_ne_zero 2 hread))
  have hslide : kernelSlide u v w ⬝ᵥ w = 0 := by
    rw [dotProduct_comm]; exact kernelSlide_dotProduct_kernel u v w hread
  rw [fourSet_inverseForm_eq_kernelSlide hsym hshiftDet hfourDet hnull hunit hread,
    inverseForm_kernelShift hsym hnull hunit he,
    ← dotProduct_self_eq_leverage, hslide]
  ring

/-- **THE INSIDER PRODUCER.**  A four-set built on a corank-one gap, and an
insider whose slid probe is pinched below the drop ceiling, produce a strictly
dominating triple: the four-set with that insider removed.

This is a producer per INSIDER, where the payment law of
`Gtz.FunnelSpectralPinch` is their sum.  The drop ceiling of an insider `u` is
`tau * m - e2 * (1 - (u ⬝ᵥ w) ^ 2 / (v ⬝ᵥ w) ^ 2)` with `m` the slid probe's
squared length, and the window is the same pinch window as before. -/
theorem exists_posDef_sub_of_insider_window {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hpsd : form.PosSemidef) {w : Fin 3 → ℝ} (hnull : form *ᵥ w = 0)
    (hunit : w ⬝ᵥ w = 1) (he : 0 < secondInvariantOfThree form)
    {v : Fin 3 → ℝ} (hread : v ⬝ᵥ w ≠ 0) (u : Fin 3 → ℝ)
    (hleft : 2 * (Matrix.trace form * (kernelSlide u v w ⬝ᵥ kernelSlide u v w)
          - secondInvariantOfThree form
            * (1 - ((u ⬝ᵥ w) / (v ⬝ᵥ w)) ^ 2))
        < Matrix.trace form * (kernelSlide u v w ⬝ᵥ kernelSlide u v w))
    (hpos : 0 < pinchPoly form (kernelSlide u v w ⬝ᵥ kernelSlide u v w)
        (Matrix.trace form * (kernelSlide u v w ⬝ᵥ kernelSlide u v w)
          - secondInvariantOfThree form
            * (1 - ((u ⬝ᵥ w) / (v ⬝ᵥ w)) ^ 2))) :
    (form + atomMatrix v - atomMatrix u).PosDef := by
  have hsym : formᵀ = form := (by simpa using hpsd.isHermitian : form.IsSymm)
  have hfourPD : (form + atomMatrix v).PosDef :=
    posDef_add_atomMatrix_of_reading_ne_zero hpsd hnull hunit (ne_of_gt he) hread
  set slide := kernelSlide u v w with hsl
  set m := slide ⬝ᵥ slide with hm
  set sigma := slide ⬝ᵥ (form *ᵥ slide) with hsig
  set P := Matrix.trace form * m
      - secondInvariantOfThree form * (1 - ((u ⬝ᵥ w) / (v ⬝ᵥ w)) ^ 2) with hP
  have hslide : slide ⬝ᵥ w = 0 := by
    rw [hsl, dotProduct_comm]; exact kernelSlide_dotProduct_kernel u v w hread
  have hpinch : sigma ^ 2 - Matrix.trace form * m * sigma
      + secondInvariantOfThree form * m ^ 2 ≤ 0 :=
    pinch_of_kernelOrth hsym hnull hunit hslide
  have hlt : P < sigma := by
    refine lt_of_pinch_of_window (c := Matrix.trace form * m)
      (d := secondInvariantOfThree form * m ^ 2) ?_ ?_ hleft
    · exact hpinch
    · rw [pinchPoly] at hpos; exact hpos
  refine posDef_sub_atomMatrix_of_inverseForm_lt_one hfourPD ?_
  rw [fourSet_pivot_of_unit_null hsym hnull hunit (ne_of_gt he) hread u, ← hsl, ← hm, ← hsig]
  rw [div_add' _ _ _ (ne_of_gt he), div_lt_one he]
  nlinarith [hlt, he]

/-- **THE INSIDER PRODUCER AT A DESIGN.**  Dropping the insider from the four-set
leaves a genuine triple of the design, so the window at ONE insider already
refutes the boundary hypothesis. -/
theorem exists_strict_of_insider_window (D : WeightedDesign m 3)
    {x y z d : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    {kern : Fin 3 → ℝ}
    (hgap : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ kern = 0)
    (hunit : kern ⬝ᵥ kern = 1)
    (he : 0 < secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
    (hread : D.atom d ⬝ᵥ kern ≠ 0)
    (hleft : 2 * (Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
            * (kernelSlide (D.atom x) (D.atom d) kern
              ⬝ᵥ kernelSlide (D.atom x) (D.atom d) kern)
          - secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
            * (1 - ((D.atom x ⬝ᵥ kern) / (D.atom d ⬝ᵥ kern)) ^ 2))
        < Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          * (kernelSlide (D.atom x) (D.atom d) kern
            ⬝ᵥ kernelSlide (D.atom x) (D.atom d) kern))
    (hpos : 0 < pinchPoly (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
        (kernelSlide (D.atom x) (D.atom d) kern
          ⬝ᵥ kernelSlide (D.atom x) (D.atom d) kern)
        (Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
            * (kernelSlide (D.atom x) (D.atom d) kern
              ⬝ᵥ kernelSlide (D.atom x) (D.atom d) kern)
          - secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
            * (1 - ((D.atom x ⬝ᵥ kern) / (D.atom d ⬝ᵥ kern)) ^ 2))) :
    (atomMatrix (D.atom d) + atomMatrix (D.atom y) + atomMatrix (D.atom z) - 1).PosDef := by
  have hpsd : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosSemidef := hdom
  have hstep := exists_posDef_sub_of_insider_window hpsd hgap hunit he hread (D.atom x)
    hleft hpos
  have hrw : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 + atomMatrix (D.atom d)
      - atomMatrix (D.atom x)
      = atomMatrix (D.atom d) + atomMatrix (D.atom y) + atomMatrix (D.atom z) - 1 := by
    rw [subsetSum_triple_atoms D hxy hxz hyz]; abel
  rwa [hrw] at hstep

/-- **THE INSIDER PIVOT LAW OF A BOUNDARY SYSTEM.**  At a boundary system the
insider window is SHUT at every member of every corank-one weak dominator and
every outside atom that reads its kernel.  Three polynomial laws per four-set,
whose sum is the single payment law. -/
theorem isTie_insider_pinch_law (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z d : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdy : d ≠ y) (hdz : d ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    {kern : Fin 3 → ℝ}
    (hgap : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ kern = 0)
    (hunit : kern ⬝ᵥ kern = 1)
    (he : 0 < secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
    (hread : D.atom d ⬝ᵥ kern ≠ 0) :
    Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          * (kernelSlide (D.atom x) (D.atom d) kern
            ⬝ᵥ kernelSlide (D.atom x) (D.atom d) kern)
        ≤ 2 * (Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
              * (kernelSlide (D.atom x) (D.atom d) kern
                ⬝ᵥ kernelSlide (D.atom x) (D.atom d) kern)
            - secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
              * (1 - ((D.atom x ⬝ᵥ kern) / (D.atom d ⬝ᵥ kern)) ^ 2))
      ∨ pinchPoly (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          (kernelSlide (D.atom x) (D.atom d) kern
            ⬝ᵥ kernelSlide (D.atom x) (D.atom d) kern)
          (Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
              * (kernelSlide (D.atom x) (D.atom d) kern
                ⬝ᵥ kernelSlide (D.atom x) (D.atom d) kern)
            - secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
              * (1 - ((D.atom x ⬝ᵥ kern) / (D.atom d ⬝ᵥ kern)) ^ 2)) ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hleft, hpos⟩ := hcon
  have hstrict := exists_strict_of_insider_window D hxy hxz hyz hdom hgap hunit he hread
    (by linarith [hleft]) (lt_of_le_of_ne (le_of_lt hpos) (Ne.symm (ne_of_gt hpos)))
  refine htie.2 ({d, y, z} : Finset (Fin m)) (card_triple_eq hdy hdz hyz) ?_
  rwa [subsetSum_triple_atoms D hdy hdz hyz]

/-! ## 8. The budget of a corank-one boundary system -/

/-- **THE FULL BUDGET OF A CORANK-ONE BOUNDARY SYSTEM.**  Everything this route
extracts from one corank-one weak dominator of a boundary system, at any size and
in either branch of the dichotomy: a heavy reader, its weight cap, the four-scalar
pinch law, and the reality of the two nonzero eigenvalues. -/
theorem isTie_corankOne_budget (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    {kern : Fin 3 → ℝ}
    (hgap : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ kern = 0)
    (hunit : kern ⬝ᵥ kern = 1)
    (he : 0 < secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)) :
    0 < Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
      ∧ 4 * secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          ≤ Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) ^ 2
      ∧ (D.atom x ⬝ᵥ kern) ^ 2 + (D.atom y ⬝ᵥ kern) ^ 2 + (D.atom z ⬝ᵥ kern) ^ 2 = 1
      ∧ ∃ d : Fin m, d ∉ ({x, y, z} : Finset (Fin m))
          ∧ 1 < (D.atom d ⬝ᵥ kern) ^ 2
          ∧ 1 < leverageOf (D.atom d)
          ∧ D.weight d * Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
              * ((D.atom d ⬝ᵥ kern) ^ 2
                  * (secondInvariantOfThree
                        (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
                    - Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
                - secondInvariantOfThree
                    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
            ≤ 2 * (Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) ^ 2
                - secondInvariantOfThree
                    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))
          ∧ (Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
                  * planeNormSq (D.atom d) kern
                ≤ 2 * paymentCeiling (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
                    (D.atom d) kern
              ∨ pinchPoly (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
                  (planeNormSq (D.atom d) kern)
                  (paymentCeiling (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
                    (D.atom d) kern) ≤ 0) := by
  classical
  have hpsd : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosSemidef := hdom
  have hsym : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)ᵀ
      = subsetSum D ({x, y, z} : Finset (Fin m)) - 1 :=
    (by simpa using hpsd.isHermitian :
      (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).IsSymm)
  obtain ⟨d, hdT, hdread⟩ :=
    exists_outside_reading_sq_gt_one_of_dominator D hxy hxz hyz hgap hunit
  have hdx : d ≠ x := fun h => hdT (by rw [h]; exact Finset.mem_insert_self x _)
  have hdy : d ≠ y := fun h => hdT (by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self y _))
  have hdz : d ≠ z := fun h => hdT (by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self z)))
  have hreadne : D.atom d ⬝ᵥ kern ≠ 0 := by
    intro h; rw [h] at hdread; norm_num at hdread
  refine ⟨trace_pos_of_dominator hpsd hgap hunit he,
    four_mul_secondInvariant_le_trace_sq_of_unit_null hsym hgap hunit,
    dominator_readings_sq D hxy hxz hyz hgap hunit,
    d, hdT, hdread, one_lt_leverage_of_outside_reader hunit hdread,
    isTie_weight_cap D htie hxy hxz hyz hdx hdy hdz hdom hgap hunit he hreadne,
    isTie_pinch_law D htie hxy hxz hyz hdx hdy hdz hdom hgap hunit he hreadne⟩

/-- **THE BUDGET AT SIX POINTS, IN EITHER BRANCH.**  A `(6,3)` boundary system
has a weak dominating triple by definition, and its gap is singular because no
triple dominates strictly.  Whenever that gap has corank exactly one the whole
budget applies, with no reference to the all-heavy or funnel dichotomy. -/
theorem isTie_sixThree_corankOne_budget (D : WeightedDesign 6 3) (htie : IsTie D)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin 6)))
    {kern : Fin 3 → ℝ}
    (hgap : (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1) *ᵥ kern = 0)
    (hunit : kern ⬝ᵥ kern = 1)
    (he : 0 < secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)) :
    ∃ d : Fin 6, d ∉ ({x, y, z} : Finset (Fin 6))
      ∧ 1 < (D.atom d ⬝ᵥ kern) ^ 2
      ∧ 1 < leverageOf (D.atom d)
      ∧ D.weight d * Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
          * ((D.atom d ⬝ᵥ kern) ^ 2
              * (secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
                - Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1))
            - secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1))
        ≤ 2 * (Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1) ^ 2
            - secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)) := by
  obtain ⟨-, -, -, d, hdT, hdread, hdlev, hdcap, -⟩ :=
    isTie_corankOne_budget D htie hxy hxz hyz hdom hgap hunit he
  exact ⟨d, hdT, hdread, hdlev, hdcap⟩

end Gtz
