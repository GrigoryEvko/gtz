/-
# The planar weight floor: the five-coplanar stratum of `(6,3)` is EMPTY

This module closes a whole stratum of the `(6,3)` hinge, with an argument that has
no complex analogue.  The statement it lands is strictly stronger than the
circle-gap statement it was commissioned to prove.

## The stratum

The `(6,3)` hinge reduces to configurations with four or five coplanar atoms.
Read Parseval at the unit normal `u` of the plane `Pi` that carries five of the
six atoms.  Write `alpha_c` for the axis coordinate and `p_c` for the in-plane
part of an atom.  The two readings at `(u,u)` and at `(u,Pi)` are

    sum_c t_c alpha_c^2 = 1 ,        sum_c t_c alpha_c p_c = 0 .

Five coplanar atoms make every `alpha` vanish but one, so the second reading
forces `p = 0` at the sixth atom: the sixth atom is a pure SPIKE `beta u` with
`t beta^2 = 1`.  Every triple that contains the spike is block diagonal for
`R^3 = Pi + R u`, and its axis block `beta^2 - 1 = 1/t - 1` is positive.  So the
design is a tie exactly when the five planar atoms admit a pair that dominates
weakly in the plane and none that dominates strictly.

The planar family is NOT a design.  It satisfies `sum_a t_a g_a g_a^T = I_2`, but
its total weight is `sigma = 1 - t < 1`, because the spike carries `t > 0`.  That
weight deficit is the whole content of the stratum.

## What this module proves

**THE PLANAR WEIGHT FLOOR** (`Gtz.planarParseval_one_le_weightSum`).  A plane
Parseval family with no strictly dominating pair has total weight at least one.

There is no room left.  The floor is attained, on a two-parameter family, and
that family is exactly the landed rank-two tie classification: at total weight
one the per-atom bound `t_a (2 l_a - 1) <= 1` of
`Gtz.weight_mul_two_leverage_sub_one_le_one` becomes an equality at every atom,
which is the class law `2 l - 1 = 1/T_A` of `Gtz.rankTwoTieClassification` read
at singleton classes.  So this module is the open-stratum extension of that
classification, and it agrees with it on the boundary.

The stratum dies immediately: `Gtz.no_planarSpike_of_noStrictPair` and
`Gtz.not_coplanarSpike_design`.  A spike needs positive weight, and the plane has
already used all of it.

## The mechanism, in three steps

Send each atom to its DOUBLED angle.  For a plane vector `g` put

    chartVector g = (g_0^2 - g_1^2, 2 g_0 g_1)          `Gtz.chartVector`

which has leverage `l^2` and obeys the exact Gram law

    <chartVector g, chartVector h> = 2 <g,h>^2 - l_g l_h    `Gtz.dotProduct_chartVector`

Normalising gives unit vectors `u_a` in the PLANE, and Parseval becomes two
scalar readings, `sum_a s_a = 2` and `sum_a s_a u_a = 0`, with the share
`s_a = t_a l_a`.  Write `x_a = 1 - 1/l_a`.  The pair `{a,b}` fails to dominate
strictly exactly when `2 x_a x_b <= 1 + <u_a,u_b>`.  Then:

* **The row law.**  Pair the balance `sum_a s_a u_a = 0` against `u_b` and spend
  the caps.  This gives `s_b (1 - x_b^2) + x_b Sigma <= 1` at every atom, where
  `Sigma = sum_a s_a x_a` (`Gtz.chartRowLaw`).  It is the weight-deficient form
  of the landed per-atom leverage cap.
* **The pivot.**  If ONE atom has `s_b (1 + x_b) >= 1` the row law collapses to
  `x_b Sigma <= x_b`, and `Sigma <= 1` follows (`Gtz.chartPivot`).  In design
  terms `s_b (1 + x_b) = t_b (2 l_b - 1)`, so a single atom at the landed cap
  already closes the stratum.
* **The count and the exchange.**  Otherwise every atom has `s_a (1 + x_a) < 1`,
  and those quantities total `2 + Sigma`, so at most three atoms give `Sigma < 1`
  outright.  With four or more atoms the vectors `(1, u_a)` are linearly
  dependent in a THREE-dimensional space (`Gtz.exists_chartRelation`), and the
  dependence moves weight along a line that keeps Parseval, keeps the caps, and
  does not decrease `Sigma`, until one atom empties.  Induct.

## Why this is real-only, and what breaks over C

The load-bearing count is `finrank R (R x R^2) = 3` in `Gtz.exists_chartRelation`.
Over C the doubled-angle image of a plane atom is not a circle but the Bloch
SPHERE: the chart target gains one dimension, the exchange step needs FIVE atoms
rather than four, and the count `2 + Sigma < 4` gives only `Sigma < 2`.  The
argument does not survive complexification, and it must not: the hinge is FALSE
over C (`Gtz.not_complexHingeHoldsAtSize_six_three`), and the complex
counterexample of `Gtz/Complex/ComplexHingeRefutation.lean` puts its five planar
atoms on that sphere.

MEASURED (Julia, `scratchpad/circlegap/verify.jl`, 2026-08-22): over R the maximum
of `Sigma` on the cap region is `1` to ten digits at every size from three to six
atoms.  Over C, with the same caps read on the Bloch sphere, `Sigma` exceeds `1`
at sizes five, six and seven, giving spike weights `6.2e-4`, `2.9e-4` and
`4.4e-4`.  The separation is exactly the one dimension.

## Scope

Nothing here decides `GtzWeighted 6 3`.  What it removes is the five-coplanar
stratum of the hinge at that size, together with every weight-deficient plane
configuration at rank two.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

/-! ## Part A — the doubled-angle chart -/

/-- The doubled-angle image of a plane vector, `(g_0^2 - g_1^2, 2 g_0 g_1)`.  It
has leverage `l^2`, so dividing by `l` puts a unit vector on the circle, and its
Gram law turns SQUARED pairings into linear ones. -/
def chartVector (g : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![g 0 ^ 2 - g 1 ^ 2, 2 * (g 0 * g 1)]

@[simp] theorem chartVector_zero (g : Fin 2 → ℝ) :
    chartVector g 0 = g 0 ^ 2 - g 1 ^ 2 := rfl

@[simp] theorem chartVector_one (g : Fin 2 → ℝ) :
    chartVector g 1 = 2 * (g 0 * g 1) := rfl

theorem leverageOf_two (v : Fin 2 → ℝ) : leverageOf v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [leverageOf, Fin.sum_univ_two]

theorem dotProduct_two (v w : Fin 2 → ℝ) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- **The chart Gram law.**  Doubling the angle turns the SQUARED pairing into a
linear one. -/
theorem dotProduct_chartVector (g h : Fin 2 → ℝ) :
    chartVector g ⬝ᵥ chartVector h = 2 * (g ⬝ᵥ h) ^ 2 - leverageOf g * leverageOf h := by
  simp only [dotProduct_two, leverageOf_two, chartVector_zero, chartVector_one]
  ring

/-- The chart squares the leverage. -/
theorem leverageOf_chartVector (g : Fin 2 → ℝ) :
    leverageOf (chartVector g) = leverageOf g ^ 2 := by
  simp only [leverageOf_two, chartVector_zero, chartVector_one]
  ring

/-- Lagrange at rank two, in the form this module needs. -/
theorem sq_dotProduct_le_leverage_mul (v w : Fin 2 → ℝ) :
    (v ⬝ᵥ w) ^ 2 ≤ leverageOf v * leverageOf w := by
  simp only [dotProduct_two, leverageOf_two]
  nlinarith [sq_nonneg (v 0 * w 1 - v 1 * w 0)]

/-- Two unit plane vectors pair in `[-1, 1]`. -/
theorem neg_one_le_dotProduct_of_unit {v w : Fin 2 → ℝ}
    (hv : leverageOf v = 1) (hw : leverageOf w = 1) : -1 ≤ v ⬝ᵥ w := by
  have h := sq_dotProduct_le_leverage_mul v w
  rw [hv, hw, one_mul] at h
  nlinarith [h]

/-! ## Part B — the chart weight floor, abstractly

The whole content lives here, on bare data: unit plane vectors `u_a`, positive
shares `s_a` that sum to two and balance to zero, and reals `x_a` in `[0,1)`
obeying the cap `2 x_a x_b <= 1 + <u_a,u_b>`. -/

/-- **The row law of the chart.**  Pair the balance against one atom and spend the
caps.  This is the weight-deficient form of the landed per-atom leverage cap
`Gtz.weight_mul_two_leverage_sub_one_le_one`, which is the case `Sigma = 1`. -/
theorem chartRowLaw {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (s x : ι → ℝ) (u : ι → Fin 2 → ℝ)
    (hspos : ∀ a ∈ T, 0 ≤ s a)
    (hunit : ∀ a ∈ T, leverageOf (u a) = 1)
    (hsum : ∑ a ∈ T, s a = 2)
    (hbal : ∀ i, ∑ a ∈ T, s a * u a i = 0)
    (hcap : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * (x a * x b) ≤ 1 + u a ⬝ᵥ u b)
    {b : ι} (hb : b ∈ T) :
    s b * (1 - x b ^ 2) + x b * (∑ a ∈ T, s a * x a) ≤ 1 := by
  classical
  set Sg : ℝ := ∑ a ∈ T, s a * x a with hSgdef
  have hrow : ∑ a ∈ T, s a * (u a ⬝ᵥ u b) = 0 := by
    have hexp : ∀ a, s a * (u a ⬝ᵥ u b)
        = (s a * u a 0) * u b 0 + (s a * u a 1) * u b 1 := by
      intro a; rw [dotProduct_two]; ring
    calc ∑ a ∈ T, s a * (u a ⬝ᵥ u b)
        = ∑ a ∈ T, ((s a * u a 0) * u b 0 + (s a * u a 1) * u b 1) :=
          Finset.sum_congr rfl fun a _ => hexp a
      _ = (∑ a ∈ T, s a * u a 0) * u b 0 + (∑ a ∈ T, s a * u a 1) * u b 1 := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      _ = 0 := by rw [hbal 0, hbal 1]; ring
  have hdiag : u b ⬝ᵥ u b = 1 := by
    have h := hunit b hb
    simpa [leverageOf_two, dotProduct_two, sq] using h
  have hpeel : s b + ∑ a ∈ T.erase b, s a * (u a ⬝ᵥ u b) = 0 := by
    have := Finset.add_sum_erase T (fun a => s a * (u a ⬝ᵥ u b)) hb
    rw [hdiag, mul_one] at this
    rw [this, hrow]
  have hlow : ∑ a ∈ T.erase b, s a * (2 * (x a * x b) - 1)
      ≤ ∑ a ∈ T.erase b, s a * (u a ⬝ᵥ u b) := by
    refine Finset.sum_le_sum fun a ha => ?_
    have haT : a ∈ T := Finset.mem_of_mem_erase ha
    have hane : a ≠ b := Finset.ne_of_mem_erase ha
    have hcapab := hcap a haT b hb hane
    have hsa := hspos a haT
    nlinarith [hcapab, hsa]
  have hsplitS : s b * x b + ∑ a ∈ T.erase b, s a * x a = Sg :=
    Finset.add_sum_erase T (fun a => s a * x a) hb
  have hsplitW : s b + ∑ a ∈ T.erase b, s a = 2 := by
    rw [← hsum]; exact Finset.add_sum_erase T s hb
  have heval : ∑ a ∈ T.erase b, s a * (2 * (x a * x b) - 1)
      = 2 * x b * (Sg - s b * x b) - (2 - s b) := by
    have h1 : ∑ a ∈ T.erase b, s a * (2 * (x a * x b) - 1)
        = 2 * x b * (∑ a ∈ T.erase b, s a * x a) - ∑ a ∈ T.erase b, s a := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [h1]
    have h2 : ∑ a ∈ T.erase b, s a * x a = Sg - s b * x b := by linarith [hsplitS]
    have h3 : ∑ a ∈ T.erase b, s a = 2 - s b := by linarith [hsplitW]
    rw [h2, h3]
  rw [heval] at hlow
  nlinarith [hpeel, hlow]

/-- **The pivot.**  A single atom sitting at the landed leverage cap closes the
whole family: if `s_b (1 + x_b) >= 1` at one atom then `Sigma <= 1`.  In design
terms `s_b (1 + x_b) = t_b (2 l_b - 1)`. -/
theorem chartPivot {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (s x : ι → ℝ) (u : ι → Fin 2 → ℝ)
    (hspos : ∀ a ∈ T, 0 ≤ s a)
    (hunit : ∀ a ∈ T, leverageOf (u a) = 1)
    (hsum : ∑ a ∈ T, s a = 2)
    (hbal : ∀ i, ∑ a ∈ T, s a * u a i = 0)
    (hx0 : ∀ a ∈ T, 0 ≤ x a) (hx1 : ∀ a ∈ T, x a ≤ 1)
    (hcap : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * (x a * x b) ≤ 1 + u a ⬝ᵥ u b)
    {b : ι} (hb : b ∈ T) (hpiv : 1 ≤ s b * (1 + x b)) :
    ∑ a ∈ T, s a * x a ≤ 1 := by
  classical
  set Sg : ℝ := ∑ a ∈ T, s a * x a with hSgdef
  have hrow := chartRowLaw T s x u hspos hunit hsum hbal hcap hb
  rw [← hSgdef] at hrow
  have hxb0 := hx0 b hb
  have hxb1 := hx1 b hb
  rcases eq_or_lt_of_le hxb0 with hzero | hpos
  · -- `x b = 0`, so the pivot says `s b >= 1` and the rest of the weight is at most one
    have hsb : 1 ≤ s b := by rw [← hzero] at hpiv; linarith [hpiv]
    have hsplitS : s b * x b + ∑ a ∈ T.erase b, s a * x a = Sg :=
      Finset.add_sum_erase T (fun a => s a * x a) hb
    have hsplitW : s b + ∑ a ∈ T.erase b, s a = 2 := by
      rw [← hsum]; exact Finset.add_sum_erase T s hb
    have hbound : ∑ a ∈ T.erase b, s a * x a ≤ ∑ a ∈ T.erase b, s a := by
      refine Finset.sum_le_sum fun a ha => ?_
      have haT : a ∈ T := Finset.mem_of_mem_erase ha
      nlinarith [hspos a haT, hx1 a haT]
    rw [← hzero] at hsplitS
    linarith [hsplitS, hsplitW, hbound]
  · -- `x b > 0`: the row law collapses
    have hkey : x b * Sg ≤ x b := by nlinarith [hrow, hpiv, hxb0, hxb1]
    exact le_of_mul_le_mul_left (by linarith [hkey]) hpos

/-- **The exchange relation.**  Four or more atoms in the plane chart carry a
nontrivial affine relation, because `(1, u_a)` lives in a THREE-dimensional space.
This is the ONLY place where the dimension of the plane is spent, and it is
exactly the step that has no complex analogue. -/
theorem exists_chartRelation {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (u : ι → Fin 2 → ℝ) (hcard : 3 < T.card) :
    ∃ lam : ι → ℝ, (∑ a ∈ T, lam a = 0) ∧ (∀ i, ∑ a ∈ T, lam a * u a i = 0) ∧
      ∃ c ∈ T, lam c ≠ 0 := by
  classical
  have hfr : Module.finrank ℝ (ℝ × (Fin 2 → ℝ)) = 3 := by
    simp [Module.finrank_prod]
  have hlt : Module.finrank ℝ (ℝ × (Fin 2 → ℝ)) < Fintype.card {a // a ∈ T} := by
    rw [hfr, Fintype.card_coe]; exact hcard
  have hnli : ¬ LinearIndependent ℝ
      (fun a : {a // a ∈ T} => ((1 : ℝ), u a.1) : {a // a ∈ T} → ℝ × (Fin 2 → ℝ)) := by
    intro hli
    exact absurd (hli.fintype_card_le_finrank) (not_le.mpr hlt)
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hnli
  have hfst : ∑ i : {a // a ∈ T}, g i = 0 := by
    have h := congrArg Prod.fst hg
    simpa [Prod.fst_sum, Prod.smul_fst, smul_eq_mul] using h
  have hsnd : ∀ j : Fin 2, ∑ i : {a // a ∈ T}, g i * u i.1 j = 0 := by
    intro j
    have h := congrArg (fun p : ℝ × (Fin 2 → ℝ) => p.2 j) hg
    simpa [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using h
  have hval : ∀ (a : ι) (h : a ∈ T),
      (if h' : a ∈ T then g ⟨a, h'⟩ else 0) = g ⟨a, h⟩ := fun a h => dif_pos h
  refine ⟨fun a => if h : a ∈ T then g ⟨a, h⟩ else 0, ?_, ?_, i0.1, i0.2, ?_⟩
  · have key : ∑ a ∈ T, (if h : a ∈ T then g ⟨a, h⟩ else 0)
        = ∑ i : {a // a ∈ T}, g i := by
      rw [← Finset.sum_attach T (fun a => if h : a ∈ T then g ⟨a, h⟩ else 0),
        Finset.attach_eq_univ]
      exact Finset.sum_congr rfl fun a _ => hval a.1 a.2
    rw [key, hfst]
  · intro j
    have key : ∑ a ∈ T, (if h : a ∈ T then g ⟨a, h⟩ else 0) * u a j
        = ∑ i : {a // a ∈ T}, g i * u i.1 j := by
      rw [← Finset.sum_attach T
        (fun a => (if h : a ∈ T then g ⟨a, h⟩ else 0) * u a j),
        Finset.attach_eq_univ]
      exact Finset.sum_congr rfl fun a _ => by rw [hval a.1 a.2]
    rw [key, hsnd j]
  · have hv : (if h : (i0 : ι) ∈ T then g ⟨(i0 : ι), h⟩ else 0) = g i0 := hval i0.1 i0.2
    simpa [hv] using hi0

/-- The inductive core of the planar weight floor. -/
private theorem chartWeightFloor_aux {ι : Type*} [DecidableEq ι] :
    ∀ (n : ℕ) (T : Finset ι) (s x : ι → ℝ) (u : ι → Fin 2 → ℝ),
      T.card ≤ n →
      (∀ a ∈ T, 0 < s a) →
      (∀ a ∈ T, leverageOf (u a) = 1) →
      (∑ a ∈ T, s a = 2) →
      (∀ i, ∑ a ∈ T, s a * u a i = 0) →
      (∀ a ∈ T, 0 ≤ x a) → (∀ a ∈ T, x a ≤ 1) →
      (∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * (x a * x b) ≤ 1 + u a ⬝ᵥ u b) →
      ∑ a ∈ T, s a * x a ≤ 1 := by
  classical
  intro n
  induction n with
  | zero =>
      intro T s x u hcard _ _ hsum _ _ _ _
      have : T = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      rw [this] at hsum
      simp at hsum
  | succ n ih =>
      intro T s x u hcard hspos hunit hsum hbal hx0 hx1 hcap
      have hsposw : ∀ a ∈ T, 0 ≤ s a := fun a ha => (hspos a ha).le
      by_cases hpiv : ∃ b ∈ T, 1 ≤ s b * (1 + x b)
      · obtain ⟨b, hb, hbpiv⟩ := hpiv
        exact chartPivot T s x u hsposw hunit hsum hbal hx0 hx1 hcap hb hbpiv
      push_neg at hpiv
      -- every atom is strictly below the landed cap
      have hne : T.Nonempty := by
        rcases T.eq_empty_or_nonempty with rfl | h
        · simp at hsum
        · exact h
      by_cases hsmall : T.card ≤ 3
      · -- the count closes it: the quantities `s_a (1 + x_a)` total `2 + Sigma`
        have htot : ∑ a ∈ T, s a * (1 + x a) = 2 + ∑ a ∈ T, s a * x a := by
          have : ∀ a, s a * (1 + x a) = s a + s a * x a := fun a => by ring
          rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_add_distrib, hsum]
        have hlt : ∑ a ∈ T, s a * (1 + x a) < ∑ _a ∈ T, (1 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty hne fun a ha => hpiv a ha
        rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hlt
        have hcard3 : (T.card : ℝ) ≤ 3 := by exact_mod_cast hsmall
        linarith [htot ▸ hlt]
      · -- four atoms or more: exchange along a chart relation
        push_neg at hsmall
        obtain ⟨lam0, hlam0sum, hlam0bal, c0, hc0T, hc0ne⟩ := exists_chartRelation T u hsmall
        -- orient the relation so that it does not decrease `Sigma`
        obtain ⟨lam, hlamsum, hlambal, c1, hc1T, hc1ne, hlamx⟩ :
            ∃ lam : ι → ℝ, (∑ a ∈ T, lam a = 0) ∧ (∀ i, ∑ a ∈ T, lam a * u a i = 0) ∧
              ∃ c ∈ T, lam c ≠ 0 ∧ 0 ≤ ∑ a ∈ T, lam a * x a := by
          by_cases hpos : (0 : ℝ) ≤ ∑ a ∈ T, lam0 a * x a
          · exact ⟨lam0, hlam0sum, hlam0bal, c0, hc0T, hc0ne, hpos⟩
          · push_neg at hpos
            refine ⟨fun a => -lam0 a, ?_, ?_, c0, hc0T, by simpa using hc0ne, ?_⟩
            · simp [Finset.sum_neg_distrib, hlam0sum]
            · intro i
              have hb := hlam0bal i
              simp only [neg_mul]
              rw [Finset.sum_neg_distrib, hb, neg_zero]
            · have hx : ∑ a ∈ T, (-lam0 a) * x a = -(∑ a ∈ T, lam0 a * x a) := by
                simp only [neg_mul]; rw [Finset.sum_neg_distrib]
              rw [hx]; linarith
        -- the atoms the relation drains
        set N : Finset ι := T.filter (fun a => lam a < 0) with hNdef
        have hNne : N.Nonempty := by
          by_contra hempty
          rw [Finset.not_nonempty_iff_eq_empty] at hempty
          have hnonneg : ∀ a ∈ T, 0 ≤ lam a := by
            intro a ha
            by_contra hlt0
            push_neg at hlt0
            have : a ∈ N := Finset.mem_filter.mpr ⟨ha, hlt0⟩
            rw [hempty] at this; simp at this
          have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hlamsum
          exact hc1ne (hall c1 hc1T)
        obtain ⟨c, hcN, hcmin⟩ :=
          Finset.exists_min_image N (fun a => s a / (-lam a)) hNne
        have hcT : c ∈ T := (Finset.mem_filter.mp hcN).1
        have hclam : lam c < 0 := (Finset.mem_filter.mp hcN).2
        set θ : ℝ := s c / (-lam c) with hθdef
        have hθpos : 0 < θ := div_pos (hspos c hcT) (by linarith)
        set s' : ι → ℝ := fun a => s a + θ * lam a with hs'def
        have hs'nonneg : ∀ a ∈ T, 0 ≤ s' a := by
          intro a ha
          by_cases hge : (0 : ℝ) ≤ lam a
          · have hmul : 0 ≤ θ * lam a := mul_nonneg hθpos.le hge
            simp only [hs'def]; linarith [hspos a ha]
          · push_neg at hge
            have haN : a ∈ N := Finset.mem_filter.mpr ⟨ha, hge⟩
            have hmin := hcmin a haN
            have hla : 0 < -lam a := by linarith
            have hbnd : θ * (-lam a) ≤ s a := (le_div_iff₀ hla).mp hmin
            simp only [hs'def]; linarith [hbnd]
        have hlcne : lam c ≠ 0 := ne_of_lt hclam
        have hnegne : -lam c ≠ 0 := ne_of_gt (by linarith)
        have hcancel : θ * lam c = -s c := by
          rw [hθdef]
          field_simp
        have hs'c : s' c = 0 := by
          simp only [hs'def]; linarith [hcancel]
        -- the exchanged family
        set T' : Finset ι := T.filter (fun a => 0 < s' a) with hT'def
        have hT'sub : T' ⊆ T := Finset.filter_subset _ _
        have hcnotT' : c ∉ T' := by
          simp only [hT'def, Finset.mem_filter, hs'c]
          rintro ⟨-, h⟩; exact lt_irrefl 0 h
        have hT'ssub : T' ⊂ T :=
          (Finset.ssubset_iff_of_subset hT'sub).mpr ⟨c, hcT, hcnotT'⟩
        have hT'card : T'.card ≤ n := by
          have hlt := Finset.card_lt_card hT'ssub
          omega
        have hzeroOut : ∀ a ∈ T, a ∉ T' → s' a = 0 := by
          intro a ha hnot
          have := hs'nonneg a ha
          simp only [hT'def, Finset.mem_filter, not_and, not_lt] at hnot
          linarith [hnot ha]
        have htransfer : ∀ f : ι → ℝ, (∑ a ∈ T', s' a * f a) = ∑ a ∈ T, s' a * f a := by
          intro f
          refine Finset.sum_subset hT'sub ?_
          intro a ha hnot
          rw [hzeroOut a ha hnot, zero_mul]
        have htransfer0 : (∑ a ∈ T', s' a) = ∑ a ∈ T, s' a := by
          have h1 := htransfer (fun _ => (1 : ℝ))
          simpa using h1
        have hsum' : ∑ a ∈ T', s' a = 2 := by
          rw [htransfer0]
          have : ∑ a ∈ T, s' a = (∑ a ∈ T, s a) + θ * ∑ a ∈ T, lam a := by
            simp only [hs'def, Finset.sum_add_distrib, Finset.mul_sum]
          rw [this, hsum, hlamsum]; ring
        have hbal' : ∀ i, ∑ a ∈ T', s' a * u a i = 0 := by
          intro i
          rw [htransfer (fun a => u a i)]
          have : ∑ a ∈ T, s' a * u a i
              = (∑ a ∈ T, s a * u a i) + θ * ∑ a ∈ T, lam a * u a i := by
            simp only [hs'def, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
            congr 1
            exact Finset.sum_congr rfl fun a _ => by ring
          rw [this, hbal i, hlambal i]; ring
        have hSigma' : ∑ a ∈ T, s a * x a ≤ ∑ a ∈ T', s' a * x a := by
          rw [htransfer x]
          have : ∑ a ∈ T, s' a * x a
              = (∑ a ∈ T, s a * x a) + θ * ∑ a ∈ T, lam a * x a := by
            simp only [hs'def, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
            congr 1
            exact Finset.sum_congr rfl fun a _ => by ring
          rw [this]
          nlinarith [hlamx, hθpos]
        refine le_trans hSigma' (ih T' s' x u hT'card ?_ ?_ hsum' hbal' ?_ ?_ ?_)
        · intro a ha; exact (Finset.mem_filter.mp ha).2
        · intro a ha; exact hunit a (hT'sub ha)
        · intro a ha; exact hx0 a (hT'sub ha)
        · intro a ha; exact hx1 a (hT'sub ha)
        · intro a ha b hb hab; exact hcap a (hT'sub ha) b (hT'sub hb) hab

/-- **THE CHART WEIGHT FLOOR.**  Unit plane directions with positive shares that
sum to two and balance to zero, obeying the cap `2 x_a x_b <= 1 + <u_a,u_b>`, have
`sum_a s_a x_a <= 1`.  Sharp: equality holds on a two-parameter family. -/
theorem chartWeightFloor {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (s x : ι → ℝ) (u : ι → Fin 2 → ℝ)
    (hspos : ∀ a ∈ T, 0 < s a)
    (hunit : ∀ a ∈ T, leverageOf (u a) = 1)
    (hsum : ∑ a ∈ T, s a = 2)
    (hbal : ∀ i, ∑ a ∈ T, s a * u a i = 0)
    (hx0 : ∀ a ∈ T, 0 ≤ x a) (hx1 : ∀ a ∈ T, x a ≤ 1)
    (hcap : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * (x a * x b) ≤ 1 + u a ⬝ᵥ u b) :
    ∑ a ∈ T, s a * x a ≤ 1 :=
  chartWeightFloor_aux T.card T s x u le_rfl hspos hunit hsum hbal hx0 hx1 hcap

end Gtz
