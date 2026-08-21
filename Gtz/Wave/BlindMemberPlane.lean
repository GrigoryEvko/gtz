/-
# A blind member puts the probe in the plane of the other two

`Gtz.two_zero_readings_probe_smul` collapses a null probe onto a single atom when
TWO members of its triple are blind to it.  One blind member does the same thing
one dimension up: the probe lands in the PLANE of the two members that still read
it.

  **`Gtz.nullProbe_in_plane_of_blind_member`:
  `(g_y·w)·g_y + (g_z·w)·g_z = w`** ,

for any triple `{x, y, z}` fixing `w` whose member `x` reads `w` at zero.  One
line from the reproduction, no positivity and no size.

## What it says at a funnel

The adjugate law already reads a blind member as a vanishing pair minor of the
other two (`Gtz.funnel_one_blind_pairMinor_zero`).  Together the two statements
pin the unit atom of a `(6,3)` funnel completely:

  **`Gtz.funnel_blind_member_plane_and_pairMinor`: the unit atom lies in the
  plane of two atoms whose pair minor is exactly zero, and its two coordinates
  there are its own readings of them.**

A vanishing pair minor is the boundary of admissibility, so the funnel's unit
atom is trapped in the plane of a BOUNDARY pair — a codimension-one condition
carrying a two-dimensional coordinate identity.  Both halves come from the same
blind reading.

## Why this is the sharp form

The reproduction has three terms, the adjugate law has three pair minors, and a
blind reading kills one of each — the SAME one.  So the two currencies of the
corank-one arm, readings and pair minors, degenerate together, and the geometry
they leave behind is a plane rather than a line.  Two blind readings leave a
line, which is the landed parallel-pair witness.
-/
import Gtz.Wave.FunnelPairMinorHinge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. One blind member -/

/-- **A BLIND MEMBER PUTS THE PROBE IN THE PLANE OF THE OTHER TWO.**  The blind
term drops out of the reproduction, and what is left is a two-term combination
whose coefficients are the probe's own readings. -/
theorem nullProbe_in_plane_of_blind_member (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {w : Fin 3 → ℝ}
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ w = w)
    (hblind : D.atom x ⬝ᵥ w = 0) :
    (D.atom y ⬝ᵥ w) • D.atom y + (D.atom z ⬝ᵥ w) • D.atom z = w := by
  have hrep := nullProbe_reproduction_triple D hxy hxz hyz hfix
  rw [hblind, zero_smul, zero_add] at hrep
  exact hrep

/-! ## 2. The funnel's unit atom, trapped in a boundary plane -/

/-- **THE BLIND MEMBER GIVES BOTH A PLANE AND A VANISHING PAIR MINOR.**  At a
funnel whose dominator has a member blind to the unit atom, the other two members
carry a pair minor of exactly zero AND span a plane containing the atom, with the
atom's own readings as its coordinates. -/
theorem funnel_blind_member_plane_and_pairMinor (D : WeightedDesign 6 3)
    {a x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hunit : leverageOf (D.atom a) = 1)
    (hfix : subsetSum D ({x, y, z} : Finset (Fin 6)) *ᵥ D.atom a = D.atom a)
    (hblind : D.atom x ⬝ᵥ D.atom a = 0) :
    pairGapMinor (D.atom y) (D.atom z) = 0
      ∧ (D.atom y ⬝ᵥ D.atom a) • D.atom y
          + (D.atom z ⬝ᵥ D.atom a) • D.atom z = D.atom a := by
  have hnorm : D.atom a ⬝ᵥ D.atom a = 1 := by
    rw [dotProduct_self_eq_leverage]; exact hunit
  obtain ⟨hfirst, -, -⟩ :=
    pairGapMinor_eq_pairMinorTotal_mul_reading_design D hxy hxz hyz hfix hnorm
  exact ⟨by rw [hfirst, hblind]; ring,
    nullProbe_in_plane_of_blind_member D hxy hxz hyz hfix hblind⟩

/-- **THE TWO-ZERO SIGNATURE AT `(6,3)`, IN FULL.**  A tie carrying a unit atom
orthogonal to two other atoms either has a parallel pair, or the unit atom lies
in the plane of two atoms whose pair minor is exactly zero, with its own readings
as coordinates.

The funnel dominator must meet the two orthogonal atoms
(`Gtz.funnel_dominator_meets_orthogonal_pair`); meeting both gives the parallel
pair; meeting exactly one leaves that member blind, and a blind member spends
this module. -/
theorem k2SixThree_parallel_or_boundary_plane (D : WeightedDesign 6 3)
    (htie : IsTie D) {a y z : Fin 6} (hay : a ≠ y) (haz : a ≠ z) (hyz : y ≠ z)
    (hunit : leverageOf (D.atom a) = 1)
    (hoy : D.atom y ⬝ᵥ D.atom a = 0) (hoz : D.atom z ⬝ᵥ D.atom a = 0) :
    HasParallelPair D
      ∨ ∃ d d' : Fin 6, d ≠ d' ∧ d ≠ a ∧ d' ≠ a
          ∧ pairGapMinor (D.atom d) (D.atom d') = 0
          ∧ (D.atom d ⬝ᵥ D.atom a) • D.atom d
              + (D.atom d' ⬝ᵥ D.atom a) • D.atom d' = D.atom a := by
  classical
  obtain ⟨T, hcard, havoid, -, hfix⟩ := isTie_sixThree_unitAtom_funnel D htie a hunit
  have hmeet := funnel_dominator_meets_orthogonal_pair D hay haz hyz hunit hoy hoz
    hcard havoid hfix
  -- a blind member of the dominator hands back the plane and the pair minor
  have hblindCase : ∀ b : Fin 6, b ∈ T → D.atom b ⬝ᵥ D.atom a = 0 →
      ∃ d d' : Fin 6, d ≠ d' ∧ d ≠ a ∧ d' ≠ a
        ∧ pairGapMinor (D.atom d) (D.atom d') = 0
        ∧ (D.atom d ⬝ᵥ D.atom a) • D.atom d
            + (D.atom d' ⬝ᵥ D.atom a) • D.atom d' = D.atom a := by
    intro b hbT hb
    obtain ⟨p, q, r, hpq, hpr, hqr, hT⟩ := Finset.card_eq_three.mp hcard
    subst hT
    have hmemP : p ∈ ({p, q, r} : Finset (Fin 6)) := by simp
    have hmemQ : q ∈ ({p, q, r} : Finset (Fin 6)) := by simp
    have hmemR : r ∈ ({p, q, r} : Finset (Fin 6)) := by simp
    rcases Finset.mem_insert.mp hbT with rfl | hb'
    · obtain ⟨hm, hpl⟩ := funnel_blind_member_plane_and_pairMinor D hpq hpr hqr hunit hfix hb
      exact ⟨q, r, hqr, fun h => havoid (h ▸ hmemQ), fun h => havoid (h ▸ hmemR), hm, hpl⟩
    rcases Finset.mem_insert.mp hb' with rfl | hb''
    · have hset : ({b, p, r} : Finset (Fin 6)) = ({p, b, r} : Finset (Fin 6)) :=
        Finset.insert_comm _ _ _
      have hfix' : subsetSum D ({b, p, r} : Finset (Fin 6)) *ᵥ D.atom a = D.atom a := by
        rw [hset]; exact hfix
      obtain ⟨hm, hpl⟩ :=
        funnel_blind_member_plane_and_pairMinor D (Ne.symm hpq) hqr hpr hunit hfix' hb
      exact ⟨p, r, hpr, fun h => havoid (h ▸ hmemP), fun h => havoid (h ▸ hmemR), hm, hpl⟩
    · rw [Finset.mem_singleton] at hb''
      subst hb''
      have hset : ({b, p, q} : Finset (Fin 6)) = ({p, q, b} : Finset (Fin 6)) := by
        ext c; simp; tauto
      have hfix' : subsetSum D ({b, p, q} : Finset (Fin 6)) *ᵥ D.atom a = D.atom a := by
        rw [hset]; exact hfix
      obtain ⟨hm, hpl⟩ :=
        funnel_blind_member_plane_and_pairMinor D (Ne.symm hpr) (Ne.symm hqr) hpq hunit
          hfix' hb
      exact ⟨p, q, hpq, fun h => havoid (h ▸ hmemP), fun h => havoid (h ▸ hmemQ), hm, hpl⟩
  by_cases hyT : y ∈ T
  · by_cases hzT : z ∈ T
    · -- both orthogonal atoms inside: two blind readings give the parallel pair
      refine Or.inl ?_
      have hpairSub : ({y, z} : Finset (Fin 6)) ⊆ T := by
        intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · exact hyT
        · rw [Finset.mem_singleton] at hc; subst hc; exact hzT
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
      by_cases hcy : c = y
      · rw [hcy]; exact hoy
      by_cases hcz : c = z
      · rw [hcz]; exact hoz
      · exact absurd (Finset.mem_singleton.mp
          (hc₀ ▸ Finset.mem_sdiff.mpr ⟨hc, by simp [hcy, hcz]⟩)) hne
    · exact Or.inr (hblindCase y hyT hoy)
  · exact Or.inr (hblindCase z (hmeet.resolve_left hyT) hoz)

end Gtz
