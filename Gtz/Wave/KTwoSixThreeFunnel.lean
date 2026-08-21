/-
# The two-zero stratum at `(6,3)`: the funnel must meet the plane

The `K2` stratum is the corank-one arm's two-zero pattern: a dominating triple
whose null probe is read at zero by two of its three members.  The landed
detector `Gtz.eq_nullDir_of_leverage_eq_one` says the third member then has
leverage exactly one and IS the null direction, and
`Gtz.inside_pair_orthogonal_of_leverage_eq_one` says the other two members are
orthogonal to it.  So the stratum's design-level signature is a UNIT ATOM
orthogonal to two other atoms.

That signature is exactly the funnel's input.  `Gtz.isTie_sixThree_unitAtom_funnel`
gives a `(6,3)` tie with a unit atom `a` a weak dominator `T` that AVOIDS `a`,
fixes it, and reads it at full length.  This module asks where `T` can sit
relative to the two orthogonal atoms `y` and `z`, and the answer closes one case
outright and converts the others into the hinge's currency.

## `T` cannot avoid the plane

`Gtz.funnel_dominator_meets_orthogonal_pair`: at `(6,3)` the dominator `T` must
contain `y` or `z`.  The proof is one weight count and needs no chart.  If `T`
avoided `a`, `y` and `z` then `T` would be their complement, and Parseval at the
probe `g_a` would read

  `Σ_{c ∈ T} t_c·(g_c·g_a)² = 1 − t_a = t_y + t_z + Σ_{c ∈ T} t_c` ,

while the funnel's own budget `Σ_{c ∈ T} (g_c·g_a)² = 1` and the bound
`t_c ≤ Σ_{c ∈ T} t_c` cap the left side by `Σ_{c ∈ T} t_c` alone.  Two positive
weights have nowhere to go.  **The count is size-bound on purpose: it works
because the complement of `{a, y, z}` at `(6,3)` is a triple, so `T` would have
to carry ALL of the remaining Parseval mass.**

## Meeting the plane costs a pair minor, or gives the hinge

* If `T` contains BOTH `y` and `z`, two of its readings vanish and
  `Gtz.unitAtom_parallel_of_two_readings_zero` returns a parallel pair — the
  hinge's own conclusion, with no chart and no certificate.
* If `T` contains exactly one of them, that member is blind, and the adjugate
  law `Gtz.pairGapMinor_eq_pairMinorTotal_mul_reading_design` reads the blindness
  as the pair minor of the OTHER TWO members
  (`Gtz.funnel_one_blind_pairMinor_zero`).

Assembled: `Gtz.k2SixThree_parallel_or_pairMinor_zero`.  **A `(6,3)` tie with the
two-zero signature either carries a parallel pair, or carries a pair of atoms —
neither the unit atom nor either orthogonal partner — whose pair minor is exactly
zero.**  Vanishing pair minor is the boundary of admissibility, so the stratum
pays a polynomial equation for refusing the hinge.

[MEASURED, and consistent with the fixture zoo.  The `(5,3)` diamond tie and the
`(6,3)` split diamond are both `K0` — all eight and all twelve of their weak
dominators read every member at nonzero — so neither fixture inhabits this
stratum, and neither is a counterexample to anything proved here.  The stratum
was measured empty at `(6,3)` with minimum obstruction `1.22e-2` over the ten
avoiding triples, and empty at `(5,3)` with obstruction `0.359` and `0.513` on a
second seed.]
-/
import Gtz.Wave.NullProbeAdjugateLaw
import Gtz.Wave.KOneAnchor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. The weight count -/

/-- **THE FUNNEL DOMINATOR MEETS THE PLANE.**  At `(6,3)`, a weak dominator that
avoids a unit atom and fixes it cannot also avoid both atoms orthogonal to it.
Parseval at the unit atom hands all of the remaining mass to the dominator, and
the funnel's budget caps what the dominator can carry.

Only the weights, Parseval and the funnel budget are used.  There is no chart,
no refusal and no tie hypothesis. -/
theorem funnel_dominator_meets_orthogonal_pair (D : WeightedDesign 6 3)
    {a y z : Fin 6} (hay : a ≠ y) (haz : a ≠ z) (hyz : y ≠ z)
    (hunit : leverageOf (D.atom a) = 1)
    (hoy : D.atom y ⬝ᵥ D.atom a = 0) (hoz : D.atom z ⬝ᵥ D.atom a = 0)
    {T : Finset (Fin 6)} (hcard : T.card = 3) (havoid : a ∉ T)
    (hfix : subsetSum D T *ᵥ D.atom a = D.atom a) :
    y ∈ T ∨ z ∈ T := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hyT, hzT⟩ := hcon
  -- the three excluded labels form a triple disjoint from `T`, so together they
  -- exhaust the six labels
  have htripleCard : ({a, y, z} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hay, haz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  have hdisj : Disjoint ({a, y, z} : Finset (Fin 6)) T := by
    rw [Finset.disjoint_left]
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact havoid
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hyT
    · rw [Finset.mem_singleton] at hc; subst hc; exact hzT
  have huniv : ({a, y, z} : Finset (Fin 6)) ∪ T = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_union_of_disjoint hdisj, htripleCard, hcard, Fintype.card_fin]
  -- Parseval at the unit atom
  have hpar := parseval_probe_form D (D.atom a)
  have hself : D.atom a ⬝ᵥ D.atom a = 1 := by
    rw [dotProduct_self_eq_leverage]; exact hunit
  rw [hself, ← huniv, Finset.sum_union hdisj] at hpar
  have hleft : ∑ c ∈ ({a, y, z} : Finset (Fin 6)),
      D.weight c * (D.atom c ⬝ᵥ D.atom a) ^ 2 = D.weight a := by
    rw [Finset.sum_insert (by simp [hay, haz]), Finset.sum_insert (by simp [hyz]),
      Finset.sum_singleton, hself, hoy, hoz]
    ring
  rw [hleft] at hpar
  -- the weight total of the complement
  have hweights : D.weight a
      + (D.weight y + D.weight z + ∑ c ∈ T, D.weight c) = 1 := by
    have hsum := D.weight_sum_one
    rw [← huniv, Finset.sum_union hdisj,
      Finset.sum_insert (by simp [hay, haz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton] at hsum
    linarith
  -- the funnel budget caps the dominator's share
  have hbudget : ∑ c ∈ T, (D.atom c ⬝ᵥ D.atom a) ^ 2 = 1 :=
    unitAtom_readings_resolve (m := 5) D hunit hfix
  have hcap : ∑ c ∈ T, D.weight c * (D.atom c ⬝ᵥ D.atom a) ^ 2
      ≤ ∑ c ∈ T, D.weight c := by
    have hstep : ∑ c ∈ T, D.weight c * (D.atom c ⬝ᵥ D.atom a) ^ 2
        ≤ ∑ c ∈ T, (∑ d ∈ T, D.weight d) * (D.atom c ⬝ᵥ D.atom a) ^ 2 := by
      refine Finset.sum_le_sum fun c hc => ?_
      have hle : D.weight c ≤ ∑ d ∈ T, D.weight d :=
        Finset.single_le_sum (f := D.weight) (fun d _ => (D.weight_pos d).le) hc
      exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    rwa [← Finset.mul_sum, hbudget, mul_one] at hstep
  have hy := D.weight_pos y
  have hz := D.weight_pos z
  linarith

/-! ## 2. A blind member costs the other two a pair minor -/

/-- **A BLIND MEMBER KILLS THE OPPOSITE PAIR MINOR.**  If one member of a funnel
dominator reads the unit atom at zero, the adjugate law makes the pair minor of
the other two members vanish.  No tie hypothesis and no size restriction. -/
theorem funnel_one_blind_pairMinor_zero (D : WeightedDesign 6 3)
    {a b : Fin 6} (hunit : leverageOf (D.atom a) = 1)
    {T : Finset (Fin 6)} (hcard : T.card = 3) (hbT : b ∈ T)
    (hfix : subsetSum D T *ᵥ D.atom a = D.atom a)
    (hblind : D.atom b ⬝ᵥ D.atom a = 0) :
    ∃ d d' : Fin 6, d ≠ d' ∧ d ∈ T ∧ d' ∈ T ∧ d ≠ b ∧ d' ≠ b ∧
      pairGapMinor (D.atom d) (D.atom d') = 0 := by
  classical
  obtain ⟨p, q, r, hpq, hpr, hqr, hT⟩ := Finset.card_eq_three.mp hcard
  have hnorm : D.atom a ⬝ᵥ D.atom a = 1 := by
    rw [dotProduct_self_eq_leverage]; exact hunit
  subst hT
  obtain ⟨hfirst, hsecond, hthird⟩ :=
    pairGapMinor_eq_pairMinorTotal_mul_reading_design D hpq hpr hqr hfix hnorm
  have hmemP : p ∈ ({p, q, r} : Finset (Fin 6)) := by simp
  have hmemQ : q ∈ ({p, q, r} : Finset (Fin 6)) := by simp
  have hmemR : r ∈ ({p, q, r} : Finset (Fin 6)) := by simp
  rcases Finset.mem_insert.mp hbT with rfl | hb
  · exact ⟨q, r, hqr, hmemQ, hmemR, Ne.symm hpq, Ne.symm hpr,
      by rw [hfirst, hblind]; ring⟩
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact ⟨p, r, hpr, hmemP, hmemR, hpq, Ne.symm hqr,
      by rw [hsecond, hblind]; ring⟩
  · rw [Finset.mem_singleton] at hb
    subst hb
    exact ⟨p, q, hpq, hmemP, hmemQ, hpr, hqr,
      by rw [hthird, hblind]; ring⟩

/-! ## 3. The stratum's dichotomy at `(6,3)` -/

/-- **THE TWO-ZERO SIGNATURE AT `(6,3)` PAYS A PAIR MINOR OR GIVES THE HINGE.**
A tie carrying a unit atom orthogonal to two other atoms either has a parallel
pair, or has two atoms — neither the unit atom nor either orthogonal partner —
whose pair minor is exactly zero.

The funnel supplies a dominator avoiding the unit atom, the weight count forces
it to meet the two orthogonal atoms, meeting both gives the parallel pair, and
meeting exactly one spends the adjugate law. -/
theorem k2SixThree_parallel_or_pairMinor_zero (D : WeightedDesign 6 3)
    (htie : IsTie D) {a y z : Fin 6} (hay : a ≠ y) (haz : a ≠ z) (hyz : y ≠ z)
    (hunit : leverageOf (D.atom a) = 1)
    (hoy : D.atom y ⬝ᵥ D.atom a = 0) (hoz : D.atom z ⬝ᵥ D.atom a = 0) :
    HasParallelPair D
      ∨ ∃ d d' : Fin 6, d ≠ d' ∧ d ≠ a ∧ d' ≠ a
          ∧ pairGapMinor (D.atom d) (D.atom d') = 0 := by
  classical
  obtain ⟨T, hcard, havoid, -, hfix⟩ := isTie_sixThree_unitAtom_funnel D htie a hunit
  have hmeet := funnel_dominator_meets_orthogonal_pair D hay haz hyz hunit hoy hoz
    hcard havoid hfix
  by_cases hyT : y ∈ T
  · by_cases hzT : z ∈ T
    · -- both orthogonal atoms sit inside the dominator: two blind readings
      refine Or.inl ?_
      -- the pair sits inside the triple, so exactly one member is left over
      have hpairSub : ({y, z} : Finset (Fin 6)) ⊆ T := by
        intro d hd
        rcases Finset.mem_insert.mp hd with rfl | hd
        · exact hyT
        · rw [Finset.mem_singleton] at hd; subst hd; exact hzT
      have hpairCard : ({y, z} : Finset (Fin 6)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
      have hleft : (T \ ({y, z} : Finset (Fin 6))).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hpairSub, hcard, hpairCard]
      obtain ⟨c₀, hc₀⟩ := Finset.card_eq_one.mp hleft
      have hc₀mem : c₀ ∈ T \ ({y, z} : Finset (Fin 6)) := by
        rw [hc₀]; exact Finset.mem_singleton_self c₀
      refine unitAtom_parallel_of_two_readings_zero (m := 5) D havoid
        (Finset.mem_sdiff.mp hc₀mem).1 hfix ?_
      intro c hc hne
      -- a member that is neither `y` nor `z` lands in the leftover singleton
      by_cases hcy : c = y
      · rw [hcy]; exact hoy
      by_cases hcz : c = z
      · rw [hcz]; exact hoz
      · exact absurd (Finset.mem_singleton.mp
          (hc₀ ▸ Finset.mem_sdiff.mpr ⟨hc, by simp [hcy, hcz]⟩)) hne
    · -- only `y` is inside: it is blind, so the other two pay the pair minor
      obtain ⟨d, d', hdd', hdT, hd'T, hdy, hd'y, hminor⟩ :=
        funnel_one_blind_pairMinor_zero D hunit hcard hyT hfix hoy
      exact Or.inr ⟨d, d', hdd', fun h => havoid (h ▸ hdT),
        fun h => havoid (h ▸ hd'T), hminor⟩
  · -- `y` is outside, so `z` is inside and blind
    have hzT : z ∈ T := hmeet.resolve_left hyT
    obtain ⟨d, d', hdd', hdT, hd'T, hdz, hd'z, hminor⟩ :=
      funnel_one_blind_pairMinor_zero D hunit hcard hzT hfix hoz
    exact Or.inr ⟨d, d', hdd', fun h => havoid (h ▸ hdT),
      fun h => havoid (h ▸ hd'T), hminor⟩

end Gtz
