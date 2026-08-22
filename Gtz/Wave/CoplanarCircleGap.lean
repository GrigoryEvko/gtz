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

theorem leverageOf_plane (v : Fin 2 → ℝ) : leverageOf v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [leverageOf, Fin.sum_univ_two]

theorem dotProduct_two (v w : Fin 2 → ℝ) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- **The chart Gram law.**  Doubling the angle turns the SQUARED pairing into a
linear one. -/
theorem dotProduct_chartVector (g h : Fin 2 → ℝ) :
    chartVector g ⬝ᵥ chartVector h = 2 * (g ⬝ᵥ h) ^ 2 - leverageOf g * leverageOf h := by
  simp only [dotProduct_two, leverageOf_plane, chartVector_zero, chartVector_one]
  ring

/-- The chart squares the leverage. -/
theorem leverageOf_chartVector (g : Fin 2 → ℝ) :
    leverageOf (chartVector g) = leverageOf g ^ 2 := by
  simp only [leverageOf_plane, chartVector_zero, chartVector_one]
  ring

/-- Lagrange at rank two, in the form this module needs. -/
theorem sq_dotProduct_plane_le_leverage_mul (v w : Fin 2 → ℝ) :
    (v ⬝ᵥ w) ^ 2 ≤ leverageOf v * leverageOf w := by
  simp only [dotProduct_two, leverageOf_plane]
  nlinarith [sq_nonneg (v 0 * w 1 - v 1 * w 0)]

/-- Scaling both sides of a plane pairing. -/
theorem smul_dotProduct_smul (c d : ℝ) (v w : Fin 2 → ℝ) :
    (c • v) ⬝ᵥ (d • w) = c * d * (v ⬝ᵥ w) := by
  simp only [dotProduct_two, Pi.smul_apply, smul_eq_mul]; ring

/-- Two unit plane vectors pair in `[-1, 1]`. -/
theorem neg_one_le_dotProduct_of_unit {v w : Fin 2 → ℝ}
    (hv : leverageOf v = 1) (hw : leverageOf w = 1) : -1 ≤ v ⬝ᵥ w := by
  have h := sq_dotProduct_plane_le_leverage_mul v w
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
    simpa [leverageOf_plane, dotProduct_two, sq] using h
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


/-! ## Part C — the planar weight floor in design coordinates

A PLANE PARSEVAL FAMILY is a finite family of plane vectors with positive weights
whose weighted atoms resolve `I_2`.  It is NOT a design: nothing forces the
weights to total one.  The in-plane restriction of a rank-three design is exactly
such a family, and its total weight is one minus the weight the design spends off
the plane. -/

theorem leverageOf_plane_smul (scale : ℝ) (v : Fin 2 → ℝ) :
    leverageOf (scale • v) = scale ^ 2 * leverageOf v := by
  simp only [leverageOf_plane, Pi.smul_apply, smul_eq_mul]
  ring

theorem leverageOf_plane_nonneg (v : Fin 2 → ℝ) : 0 ≤ leverageOf v := by
  rw [leverageOf_plane]; positivity

/-- A plane vector of zero leverage has a zero atom. -/
theorem atomMatrix_eq_zero_of_leverage_eq_zero {v : Fin 2 → ℝ} (h : leverageOf v = 0) :
    atomMatrix v = 0 := by
  rw [leverageOf_plane] at h
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atomMatrix, Matrix.vecMulVec_apply, h0, h1]

/-- **THE PLANAR WEIGHT FLOOR.**  A plane Parseval family in which no pair
dominates strictly carries total weight at least one.

The no-strict hypothesis is stated as `(l_a - 1)(l_b - 1) <= <g_a,g_b>^2`, which
is `det (S_{a,b} - 1) <= 0` read through Lagrange at rank two
(`Gtz.sq_dotProduct_add_sq_planeWedge`, `Gtz.det_pairGap_eq`).

Sharp: total weight exactly one is attained on a two-parameter family, which is
the landed rank-two tie classification `Gtz.rankTwoTieClassification` read at
singleton classes. -/
theorem planarParseval_one_le_weightSum {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (g : ι → Fin 2 → ℝ) (t : ι → ℝ)
    (htpos : ∀ a ∈ T, 0 < t a)
    (hpars : ∑ a ∈ T, t a • atomMatrix (g a) = 1)
    (hnostrict : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
        (leverageOf (g a) - 1) * (leverageOf (g b) - 1) ≤ (g a ⬝ᵥ g b) ^ 2) :
    1 ≤ ∑ a ∈ T, t a := by
  classical
  -- entrywise Parseval
  have hent : ∀ i j : Fin 2, ∑ a ∈ T, t a * (g a i * g a j) = if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (congrFun hpars i) j
    simpa [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Matrix.one_apply, smul_eq_mul] using h
  -- discard the zero atoms: they only add weight
  set T₀ : Finset ι := T.filter (fun a => 0 < leverageOf (g a)) with hT₀def
  have hT₀sub : T₀ ⊆ T := Finset.filter_subset _ _
  have hlevpos : ∀ a ∈ T₀, 0 < leverageOf (g a) := fun a ha => (Finset.mem_filter.mp ha).2
  have hzeroAtom : ∀ a ∈ T, a ∉ T₀ → g a 0 = 0 ∧ g a 1 = 0 := by
    intro a ha hnot
    simp only [hT₀def, Finset.mem_filter, not_and, not_lt] at hnot
    have hle := hnot ha
    have hz : leverageOf (g a) = 0 := le_antisymm hle (leverageOf_plane_nonneg _)
    rw [leverageOf_plane] at hz
    exact ⟨by nlinarith [sq_nonneg (g a 0), sq_nonneg (g a 1)],
      by nlinarith [sq_nonneg (g a 0), sq_nonneg (g a 1)]⟩
  have hent₀ : ∀ i j : Fin 2, ∑ a ∈ T₀, t a * (g a i * g a j) = if i = j then 1 else 0 := by
    intro i j
    rw [← hent i j]
    refine Finset.sum_subset hT₀sub ?_
    intro a ha hnot
    obtain ⟨h0, h1⟩ := hzeroAtom a ha hnot
    fin_cases i <;> fin_cases j <;> simp [h0, h1]
  -- the chart data
  set s : ι → ℝ := fun a => t a * leverageOf (g a) with hsdef
  set x : ι → ℝ :=
    fun a => if leverageOf (g a) ≤ 1 then 0 else 1 - (leverageOf (g a))⁻¹ with hxdef
  set u : ι → Fin 2 → ℝ :=
    fun a => (leverageOf (g a))⁻¹ • chartVector (g a) with hudef
  have hspos : ∀ a ∈ T₀, 0 < s a := by
    intro a ha
    simp only [hsdef]
    exact mul_pos (htpos a (hT₀sub ha)) (hlevpos a ha)
  have hunit : ∀ a ∈ T₀, leverageOf (u a) = 1 := by
    intro a ha
    have hl : leverageOf (g a) ≠ 0 := (hlevpos a ha).ne'
    simp only [hudef]
    rw [leverageOf_plane_smul, leverageOf_chartVector]
    field_simp
  have hsum : ∑ a ∈ T₀, s a = 2 := by
    have hterm : ∀ a, s a = t a * (g a 0 * g a 0) + t a * (g a 1 * g a 1) := by
      intro a; simp only [hsdef, leverageOf_plane]; ring
    rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_add_distrib,
      hent₀ 0 0, hent₀ 1 1]
    norm_num
  have hval : ∀ a ∈ T₀, ∀ i, s a * u a i = t a * chartVector (g a) i := by
    intro a ha i
    have hl : leverageOf (g a) ≠ 0 := (hlevpos a ha).ne'
    simp only [hsdef, hudef, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hbal0 : ∑ a ∈ T₀, t a * chartVector (g a) 0 = 0 := by
    have hterm : ∀ a, t a * chartVector (g a) 0
        = t a * (g a 0 * g a 0) - t a * (g a 1 * g a 1) := by
      intro a; rw [chartVector_zero]; ring
    rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_sub_distrib,
      hent₀ 0 0, hent₀ 1 1]
    norm_num
  have hbal1 : ∑ a ∈ T₀, t a * chartVector (g a) 1 = 0 := by
    have hterm : ∀ a, t a * chartVector (g a) 1 = 2 * (t a * (g a 0 * g a 1)) := by
      intro a; rw [chartVector_one]; ring
    rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.mul_sum, hent₀ 0 1]
    norm_num
  have hbal : ∀ i, ∑ a ∈ T₀, s a * u a i = 0 := by
    intro i
    rw [Finset.sum_congr rfl fun a ha => hval a ha i]
    fin_cases i
    · exact hbal0
    · exact hbal1
  have hx0 : ∀ a ∈ T₀, 0 ≤ x a := by
    intro a ha
    have hl := hlevpos a ha
    simp only [hxdef]
    split
    · exact le_rfl
    · rename_i hgt
      push_neg at hgt
      have hinv : (leverageOf (g a))⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]; right; linarith
      linarith
  have hx1 : ∀ a ∈ T₀, x a ≤ 1 := by
    intro a ha
    have hl := hlevpos a ha
    simp only [hxdef]
    split
    · norm_num
    · have hinv : 0 < (leverageOf (g a))⁻¹ := by positivity
      linarith
  have hcap : ∀ a ∈ T₀, ∀ b ∈ T₀, a ≠ b → 2 * (x a * x b) ≤ 1 + u a ⬝ᵥ u b := by
    intro a ha b hb hab
    have hla := hlevpos a ha
    have hlb := hlevpos b hb
    have hdot : u a ⬝ᵥ u b
        = (leverageOf (g a))⁻¹ * (leverageOf (g b))⁻¹ *
            (2 * (g a ⬝ᵥ g b) ^ 2 - leverageOf (g a) * leverageOf (g b)) := by
      simp only [hudef]
      rw [smul_dotProduct_smul, dotProduct_chartVector]
    have hgoal : x a * x b * (leverageOf (g a) * leverageOf (g b)) ≤ (g a ⬝ᵥ g b) ^ 2 := by
      by_cases hA : leverageOf (g a) ≤ 1
      · have hxa : x a = 0 := by simp only [hxdef]; rw [if_pos hA]
        rw [hxa]
        simp only [zero_mul]
        positivity
      by_cases hB : leverageOf (g b) ≤ 1
      · have hxb : x b = 0 := by simp only [hxdef]; rw [if_pos hB]
        rw [hxb]
        simp only [mul_zero, zero_mul]
        positivity
      push_neg at hA hB
      have hxa : x a * leverageOf (g a) = leverageOf (g a) - 1 := by
        simp only [hxdef]; rw [if_neg (not_le.mpr hA)]; field_simp
      have hxb : x b * leverageOf (g b) = leverageOf (g b) - 1 := by
        simp only [hxdef]; rw [if_neg (not_le.mpr hB)]; field_simp
      have hns := hnostrict a (hT₀sub ha) b (hT₀sub hb) hab
      nlinarith [hns, hxa, hxb]
    have hcancel : (leverageOf (g a))⁻¹ * (leverageOf (g b))⁻¹ *
        (leverageOf (g a) * leverageOf (g b)) = 1 := by field_simp
    have hinvpos : 0 < (leverageOf (g a))⁻¹ * (leverageOf (g b))⁻¹ := by positivity
    have hstep : x a * x b
        ≤ ((leverageOf (g a))⁻¹ * (leverageOf (g b))⁻¹) * (g a ⬝ᵥ g b) ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hgoal hinvpos.le
      have h2 : ((leverageOf (g a))⁻¹ * (leverageOf (g b))⁻¹) *
          (x a * x b * (leverageOf (g a) * leverageOf (g b))) = x a * x b := by
        calc ((leverageOf (g a))⁻¹ * (leverageOf (g b))⁻¹) *
              (x a * x b * (leverageOf (g a) * leverageOf (g b)))
            = (x a * x b) * (((leverageOf (g a))⁻¹ * (leverageOf (g b))⁻¹) *
              (leverageOf (g a) * leverageOf (g b))) := by ring
          _ = x a * x b := by rw [hcancel, mul_one]
      linarith [h1, h2]
    have hexp : ((leverageOf (g a))⁻¹ * (leverageOf (g b))⁻¹) *
        (2 * (g a ⬝ᵥ g b) ^ 2 - leverageOf (g a) * leverageOf (g b))
        = 2 * (((leverageOf (g a))⁻¹ * (leverageOf (g b))⁻¹) * (g a ⬝ᵥ g b) ^ 2) - 1 := by
      linear_combination (-1 : ℝ) * hcancel
    rw [hdot, hexp]
    linarith [hstep]
  -- the abstract floor
  have hfloor := chartWeightFloor T₀ s x u hspos hunit hsum hbal hx0 hx1 hcap
  -- read it back: `s_a x_a >= t_a (l_a - 1)` at every atom
  have hread : ∀ a ∈ T₀, t a * (leverageOf (g a) - 1) ≤ s a * x a := by
    intro a ha
    have hla := hlevpos a ha
    have hta := htpos a (hT₀sub ha)
    by_cases hA : leverageOf (g a) ≤ 1
    · have hxa : x a = 0 := by simp only [hxdef]; rw [if_pos hA]
      rw [hxa, mul_zero]
      nlinarith [hta, hA]
    · push_neg at hA
      have heq : s a * x a = t a * (leverageOf (g a) - 1) := by
        simp only [hsdef, hxdef]
        rw [if_neg (not_le.mpr hA)]
        field_simp
      linarith [heq]
  have hlin : ∑ a ∈ T₀, t a * (leverageOf (g a) - 1) ≤ 1 :=
    le_trans (Finset.sum_le_sum hread) hfloor
  have hsplit : ∑ a ∈ T₀, t a * (leverageOf (g a) - 1)
      = (∑ a ∈ T₀, s a) - ∑ a ∈ T₀, t a := by
    have hterm : ∀ a, t a * (leverageOf (g a) - 1) = s a - t a := by
      intro a; simp only [hsdef]; ring
    rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_sub_distrib]
  rw [hsplit, hsum] at hlin
  have hT₀le : ∑ a ∈ T₀, t a ≤ ∑ a ∈ T, t a := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hT₀sub ?_
    intro a ha _
    exact (htpos a ha).le
  linarith [hlin, hT₀le]

/-- **No spike over a plane.**  If a plane Parseval family with no strictly
dominating pair is the in-plane part of a design, the design has nothing left to
spend off the plane.  This is the five-coplanar stratum, in one line. -/
theorem no_planarSpike_of_noStrictPair {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (g : ι → Fin 2 → ℝ) (t : ι → ℝ) (spikeWeight : ℝ)
    (htpos : ∀ a ∈ T, 0 < t a)
    (hspike : 0 < spikeWeight)
    (htotal : (∑ a ∈ T, t a) + spikeWeight ≤ 1)
    (hpars : ∑ a ∈ T, t a • atomMatrix (g a) = 1)
    (hnostrict : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
        (leverageOf (g a) - 1) * (leverageOf (g b) - 1) ≤ (g a ⬝ᵥ g b) ^ 2) :
    False := by
  have := planarParseval_one_le_weightSum T g t htpos hpars hnostrict
  linarith

/-! ## Part D — the five-coplanar stratum of `(6,3)`

A rank-three design that keeps all but one atom inside a plane, and the remaining
atom off it, has no room: the plane already spends the whole weight budget.  The
`(6,3)` five-coplanar configuration of the Structure Lemma is exactly this shape,
so it cannot be a tie. -/

/-- The in-plane coordinates of an atom against an orthonormal plane frame. -/
def coplanarShadow (frame : Fin 2 → (Fin 3 → ℝ)) (g : Fin 3 → ℝ) : Fin 2 → ℝ :=
  fun i => g ⬝ᵥ frame i

@[simp] theorem coplanarShadow_apply (frame : Fin 2 → (Fin 3 → ℝ)) (g : Fin 3 → ℝ)
    (i : Fin 2) : coplanarShadow frame g i = g ⬝ᵥ frame i := rfl

/-- **No rank-three design is a plane plus a spike.**  If every atom of `T` lies in
the plane of an orthonormal frame, every atom outside `T` is orthogonal to that
plane, `T` is not everything, and no pair inside `T` dominates strictly, then the
configuration does not exist.

This is the five-coplanar stratum of the `(6,3)` hinge.  The Structure Lemma puts
that stratum in exactly this shape: five atoms in a plane and a sixth that is a
pure spike along the normal. -/
theorem not_coplanarSpike_design {m : ℕ} (D : WeightedDesign m 3)
    (frame : Fin 2 → (Fin 3 → ℝ))
    (horth : ∀ i j, frame i ⬝ᵥ frame j = if i = j then 1 else 0)
    (T : Finset (Fin m))
    (hplane : ∀ a ∈ T, D.atom a
        = (D.atom a ⬝ᵥ frame 0) • frame 0 + (D.atom a ⬝ᵥ frame 1) • frame 1)
    (hspike : ∀ a, a ∉ T → ∀ i, D.atom a ⬝ᵥ frame i = 0)
    (hproper : ∃ a, a ∉ T)
    (hnostrict : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
        (leverageOf (D.atom a) - 1) * (leverageOf (D.atom b) - 1)
          ≤ (D.atom a ⬝ᵥ D.atom b) ^ 2) :
    False := by
  classical
  -- Parseval, entrywise in the ambient coordinates
  have hent3 : ∀ k l : Fin 3, ∑ c, D.weight c * (D.atom c k * D.atom c l)
      = if k = l then 1 else 0 := by
    intro k l
    have h := congrFun (congrFun D.isParseval k) l
    simpa [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Matrix.one_apply, smul_eq_mul] using h
  -- Parseval, read against the frame
  have hread : ∀ i j : Fin 2,
      ∑ c, D.weight c * ((D.atom c ⬝ᵥ frame i) * (D.atom c ⬝ᵥ frame j))
        = frame i ⬝ᵥ frame j := by
    intro i j
    have hexp : ∀ c, D.weight c * ((D.atom c ⬝ᵥ frame i) * (D.atom c ⬝ᵥ frame j))
        = (frame i 0 * frame j 0) * (D.weight c * (D.atom c 0 * D.atom c 0))
        + (frame i 0 * frame j 1) * (D.weight c * (D.atom c 0 * D.atom c 1))
        + (frame i 0 * frame j 2) * (D.weight c * (D.atom c 0 * D.atom c 2))
        + (frame i 1 * frame j 0) * (D.weight c * (D.atom c 1 * D.atom c 0))
        + (frame i 1 * frame j 1) * (D.weight c * (D.atom c 1 * D.atom c 1))
        + (frame i 1 * frame j 2) * (D.weight c * (D.atom c 1 * D.atom c 2))
        + (frame i 2 * frame j 0) * (D.weight c * (D.atom c 2 * D.atom c 0))
        + (frame i 2 * frame j 1) * (D.weight c * (D.atom c 2 * D.atom c 1))
        + (frame i 2 * frame j 2) * (D.weight c * (D.atom c 2 * D.atom c 2)) := by
      intro c
      simp only [dotProduct, Fin.sum_univ_three]
      ring
    have h00 : ∑ c, D.weight c * (D.atom c 0 * D.atom c 0) = 1 := by
      simpa using hent3 0 0
    have h11 : ∑ c, D.weight c * (D.atom c 1 * D.atom c 1) = 1 := by
      simpa using hent3 1 1
    have h22 : ∑ c, D.weight c * (D.atom c 2 * D.atom c 2) = 1 := by
      simpa using hent3 2 2
    have h01 : ∑ c, D.weight c * (D.atom c 0 * D.atom c 1) = 0 := by
      simpa using hent3 0 1
    have h02 : ∑ c, D.weight c * (D.atom c 0 * D.atom c 2) = 0 := by
      simpa using hent3 0 2
    have h10 : ∑ c, D.weight c * (D.atom c 1 * D.atom c 0) = 0 := by
      simpa using hent3 1 0
    have h12 : ∑ c, D.weight c * (D.atom c 1 * D.atom c 2) = 0 := by
      simpa using hent3 1 2
    have h20 : ∑ c, D.weight c * (D.atom c 2 * D.atom c 0) = 0 := by
      simpa using hent3 2 0
    have h21 : ∑ c, D.weight c * (D.atom c 2 * D.atom c 1) = 0 := by
      simpa using hent3 2 1
    rw [Finset.sum_congr rfl fun c _ => hexp c]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h00, h11, h22, h01, h02, h10, h12, h20, h21]
    simp only [dotProduct, Fin.sum_univ_three]
    ring
  -- the atoms outside the plane contribute nothing to that reading
  have hreadT : ∀ i j : Fin 2,
      ∑ a ∈ T, D.weight a * ((D.atom a ⬝ᵥ frame i) * (D.atom a ⬝ᵥ frame j))
        = if i = j then 1 else 0 := by
    intro i j
    have h1 : ∑ a ∈ T, D.weight a * ((D.atom a ⬝ᵥ frame i) * (D.atom a ⬝ᵥ frame j))
        = ∑ c, D.weight c * ((D.atom c ⬝ᵥ frame i) * (D.atom c ⬝ᵥ frame j)) := by
      refine Finset.sum_subset (Finset.subset_univ T) ?_
      intro a _ hnot
      rw [hspike a hnot i, zero_mul, mul_zero]
    rw [h1, hread i j, horth i j]
  -- the plane family is a plane Parseval family
  have hparsP : ∑ a ∈ T, D.weight a • atomMatrix (coplanarShadow frame (D.atom a))
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Matrix.one_apply, smul_eq_mul, coplanarShadow_apply]
    exact hreadT i j
  -- the plane frame is isometric on the plane
  have hdotT : ∀ a ∈ T, ∀ b ∈ T,
      D.atom a ⬝ᵥ D.atom b
        = (D.atom a ⬝ᵥ frame 0) * (D.atom b ⬝ᵥ frame 0)
          + (D.atom a ⬝ᵥ frame 1) * (D.atom b ⬝ᵥ frame 1) := by
    intro a ha b hb
    conv_lhs => rw [hplane a ha, hplane b hb]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, horth]
    norm_num
    ring
  have hshadowDot : ∀ a ∈ T, ∀ b ∈ T,
      coplanarShadow frame (D.atom a) ⬝ᵥ coplanarShadow frame (D.atom b)
        = D.atom a ⬝ᵥ D.atom b := by
    intro a ha b hb
    rw [dotProduct_two, hdotT a ha b hb]
    simp only [coplanarShadow_apply]
  have hself : ∀ v : Fin 3 → ℝ, leverageOf v = v ⬝ᵥ v := by
    intro v
    simp [leverageOf, dotProduct, sq]
  have hlevT : ∀ a ∈ T, leverageOf (coplanarShadow frame (D.atom a)) = leverageOf (D.atom a) := by
    intro a ha
    rw [leverageOf_plane, hself, hdotT a ha a ha]
    simp only [coplanarShadow_apply]
    ring
  -- the no-strict hypothesis, transported into the plane
  have hnostrictP : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
      (leverageOf (coplanarShadow frame (D.atom a)) - 1) *
        (leverageOf (coplanarShadow frame (D.atom b)) - 1)
        ≤ (coplanarShadow frame (D.atom a) ⬝ᵥ coplanarShadow frame (D.atom b)) ^ 2 := by
    intro a ha b hb hab
    rw [hlevT a ha, hlevT b hb, hshadowDot a ha b hb]
    exact hnostrict a ha b hb hab
  -- the floor, against the design's own weight budget
  have hfloor := planarParseval_one_le_weightSum T
    (fun a => coplanarShadow frame (D.atom a)) D.weight
    (fun a _ => D.weight_pos a) hparsP hnostrictP
  obtain ⟨a₀, ha₀⟩ := hproper
  have hins : ∑ a ∈ insert a₀ T, D.weight a ≤ ∑ c, D.weight c :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ _ => (D.weight_pos a).le)
  rw [Finset.sum_insert ha₀, D.weight_sum_one] at hins
  linarith [D.weight_pos a₀, hfloor, hins]

/-- **The five-coplanar stratum of `(6,3)` is empty.**  A six-atom rank-three design
with five atoms in a plane and the sixth off it has a strictly dominating pair
inside the plane, so it is not a tie.

Together with the Structure Lemma this removes the whole five-coplanar branch of
the `(6,3)` hinge: the reduction produces a spike, and a spike over a plane
Parseval family with no strict pair does not exist. -/
theorem exists_strictPair_of_fiveCoplanar_sixThree (D : WeightedDesign 6 3)
    (frame : Fin 2 → (Fin 3 → ℝ))
    (horth : ∀ i j, frame i ⬝ᵥ frame j = if i = j then 1 else 0)
    (T : Finset (Fin 6)) (hcard : T.card = 5)
    (hplane : ∀ a ∈ T, D.atom a
        = (D.atom a ⬝ᵥ frame 0) • frame 0 + (D.atom a ⬝ᵥ frame 1) • frame 1)
    (hspike : ∀ a, a ∉ T → ∀ i, D.atom a ⬝ᵥ frame i = 0) :
    ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧
      (D.atom a ⬝ᵥ D.atom b) ^ 2
        < (leverageOf (D.atom a) - 1) * (leverageOf (D.atom b) - 1) := by
  classical
  by_contra hcon
  push_neg at hcon
  refine not_coplanarSpike_design D frame horth T hplane hspike ?_ ?_
  · by_contra hall
    push_neg at hall
    have : T = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [this, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  · intro a ha b hb hab
    exact hcon a ha b hb hab

end Gtz
