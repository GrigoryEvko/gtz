/-
# The mirror's blindness IS a vanishing pair minor

The landed mirror gives the corank-one arm its only rigidity: two weak
dominators one swap apart that share a null probe force the two exchanged atoms
parallel, UNLESS the probe is blind to them
(`Gtz.mirror_readings_eq_zero_of_not_hasParallelPair`).  That escape hatch has
been the arm's blocker, because a blind reading is a statement about a probe and
the hinge is a statement about a pair.

The adjugate law closes the gap between the two.  A weak dominator's pair minor
is its second invariant times the squared reading of the member the pair leaves
out (`Gtz.pairGapMinor_eq_pairMinorTotal_mul_reading_design`), so a blind
reading and a vanishing pair minor are the same event.  Composing:

  **`Gtz.mirror_shared_pairGapMinor_eq_zero`: at a design with no parallel pair,
  the SHARED PAIR of a null-sharing mirror is exactly boundary admissible.**

The escape hatch is therefore a closed condition in the hinge's own currency.  A
design with no parallel pair pays one polynomial equation for every null-sharing
swap it carries.

## The probe collapses onto the shared pair

The blind reading also removes its member from the reproduction, so the probe
lies in the plane of the shared pair
(`Gtz.mirror_probe_in_shared_plane`).  Two blind readings collapse the probe
onto a single atom (`Gtz.two_zero_readings_probe_smul`).  At a unit atom that is
a hinge witness, and the design cannot refuse it:

  **`Gtz.unitAtom_two_mirror_swaps_absurd`: at a design with no parallel pair, a
  unit atom's dominator is swap-related to a null-sharing dominator over at most
  ONE of its members.**

That is the first bound the campaign has on how much null-sharing a primitive
design can carry, and it is the funnel's own combinatorics.

[MEASURED, and it explains a fixture.  The `(5,3)` diamond tie carries eight
weak dominators and eighteen swap-related pairs among them, and NO two of them
share a null line — the eight null directions are pairwise distinct.  That is
exactly why the diamond is a tie with no parallel pair: the mirror never fires
there.  A funnel is the opposite regime, because every weak dominator of the
erased design fixes the unit atom, so all of them share one null.]
-/
import Gtz.Wave.NullProbeAdjugateLaw
import Gtz.Wave.DiamondNeighborhoodMirror

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. A null probe of a triple is fixed by it -/

/-- A vanishing gap image is a fixed probe.  No positivity is used: the vector
form of the null condition already carries the equation. -/
theorem mulVec_eq_of_gap_mulVec_eq_zero (D : WeightedDesign m 3) (T : Finset (Fin m))
    {w : Fin 3 → ℝ} (hnull : (subsetSum D T - 1) *ᵥ w = 0) :
    subsetSum D T *ᵥ w = w := by
  have hsplit : (subsetSum D T - 1) *ᵥ w = subsetSum D T *ᵥ w - w := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hsplit] at hnull
  exact sub_eq_zero.mp hnull

/-! ## 2. The mirror pays a pair minor -/

/-- **THE SHARED PAIR OF A NULL-SHARING MIRROR IS BOUNDARY ADMISSIBLE.**  A
design with no parallel pair is blind at the exchanged member
(`Gtz.nullReading_eq_zero_of_mirror_of_not_hasParallelPair`), and the adjugate
law reads that blindness as the pair minor of the two members the swap keeps.
The mirror's escape hatch is one polynomial equation. -/
theorem mirror_shared_pairGapMinor_eq_zero (D : WeightedDesign m 3)
    (hprim : ¬ HasParallelPair D) {p q x y : Fin m}
    (hpq : p ≠ q) (hpx : p ≠ x) (hpy : p ≠ y) (hxy : x ≠ y)
    (hq : q ∉ ({p, x, y} : Finset (Fin m))) {w : Fin 3 → ℝ} (hnorm : w ⬝ᵥ w = 1)
    (hnullC : (subsetSum D ({p, x, y} : Finset (Fin m)) - 1) *ᵥ w = 0)
    (hnullSwap :
      (subsetSum D (insert q ((({p, x, y} : Finset (Fin m))).erase p)) - 1) *ᵥ w = 0) :
    pairGapMinor (D.atom x) (D.atom y) = 0 := by
  have hp : p ∈ ({p, x, y} : Finset (Fin m)) := by simp
  have hread := nullReading_eq_zero_of_mirror_of_not_hasParallelPair D hprim hpq hp hq
    hnullC hnullSwap
  have hfix := mulVec_eq_of_gap_mulVec_eq_zero D _ hnullC
  obtain ⟨hfirst, -, -⟩ :=
    pairGapMinor_eq_pairMinorTotal_mul_reading_design D hpx hpy hxy hfix hnorm
  rw [hfirst, hread]; ring

/-- **THE PROBE LIES IN THE SHARED PAIR'S PLANE.**  The blind member drops out
of the reproduction, so the probe is a combination of the two members the swap
keeps. -/
theorem mirror_probe_in_shared_plane (D : WeightedDesign m 3)
    (hprim : ¬ HasParallelPair D) {p q x y : Fin m}
    (hpq : p ≠ q) (hpx : p ≠ x) (hpy : p ≠ y) (hxy : x ≠ y)
    (hq : q ∉ ({p, x, y} : Finset (Fin m))) {w : Fin 3 → ℝ}
    (hnullC : (subsetSum D ({p, x, y} : Finset (Fin m)) - 1) *ᵥ w = 0)
    (hnullSwap :
      (subsetSum D (insert q ((({p, x, y} : Finset (Fin m))).erase p)) - 1) *ᵥ w = 0) :
    (D.atom x ⬝ᵥ w) • D.atom x + (D.atom y ⬝ᵥ w) • D.atom y = w := by
  have hp : p ∈ ({p, x, y} : Finset (Fin m)) := by simp
  have hread := nullReading_eq_zero_of_mirror_of_not_hasParallelPair D hprim hpq hp hq
    hnullC hnullSwap
  have hfix := mulVec_eq_of_gap_mulVec_eq_zero D _ hnullC
  have hrep := nullProbe_reproduction_triple D hpx hpy hxy hfix
  rw [hread, zero_smul, zero_add] at hrep
  exact hrep

/-! ## 3. Two blind readings collapse the probe onto one atom -/

/-- **TWO BLIND READINGS COLLAPSE THE PROBE.**  A probe that two members of a
triple cannot read is a multiple of the third member. -/
theorem two_zero_readings_probe_smul (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {w : Fin 3 → ℝ}
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ w = w)
    (hzeroX : D.atom x ⬝ᵥ w = 0) (hzeroY : D.atom y ⬝ᵥ w = 0) :
    (D.atom z ⬝ᵥ w) • D.atom z = w := by
  have hrep := nullProbe_reproduction_triple D hxy hxz hyz hfix
  rw [hzeroX, hzeroY, zero_smul, zero_smul, zero_add, zero_add] at hrep
  exact hrep

/-! ## 4. The funnel refuses two null-sharing swaps -/

/-- **A UNIT ATOM'S DOMINATOR CARRIES AT MOST ONE NULL-SHARING SWAP.**  Two
swaps at two different members of the dominator make the unit atom blind twice,
and the reproduction then makes it a multiple of the one surviving member — a
parallel pair, which the design was assumed to refuse.

The two swaps must exchange DIFFERENT members: the first exchanges `p`, the
second exchanges `x`, and the pair `{p, y}` and the pair `{x, y}` are the two
shared pairs.  Each swap pays the pair minor of its own shared pair
(`Gtz.mirror_shared_pairGapMinor_eq_zero`), and the two payments together are
impossible. -/
theorem unitAtom_two_mirror_swaps_absurd (D : WeightedDesign (m + 1) 3)
    (hprim : ¬ HasParallelPair D) {a p x y q r : Fin (m + 1)}
    (hpq : p ≠ q) (hxr : x ≠ r) (hpx : p ≠ x) (hpy : p ≠ y) (hxy : x ≠ y)
    (hq : q ∉ ({p, x, y} : Finset (Fin (m + 1))))
    (hr : r ∉ ({p, x, y} : Finset (Fin (m + 1))))
    (havoid : a ∉ ({p, x, y} : Finset (Fin (m + 1))))
    (hunit : leverageOf (D.atom a) = 1)
    (hfix : subsetSum D ({p, x, y} : Finset (Fin (m + 1))) *ᵥ D.atom a = D.atom a)
    (hnullSwapP :
      (subsetSum D (insert q ((({p, x, y} : Finset (Fin (m + 1)))).erase p)) - 1)
        *ᵥ D.atom a = 0)
    (hnullSwapX :
      (subsetSum D (insert r ((({p, x, y} : Finset (Fin (m + 1)))).erase x)) - 1)
        *ᵥ D.atom a = 0) :
    False := by
  have hnullC : (subsetSum D ({p, x, y} : Finset (Fin (m + 1))) - 1) *ᵥ D.atom a = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix, sub_self]
  have hp : p ∈ ({p, x, y} : Finset (Fin (m + 1))) := by simp
  have hx : x ∈ ({p, x, y} : Finset (Fin (m + 1))) := by simp
  have hzeroP := nullReading_eq_zero_of_mirror_of_not_hasParallelPair D hprim hpq hp hq
    hnullC hnullSwapP
  have hzeroX := nullReading_eq_zero_of_mirror_of_not_hasParallelPair D hprim hxr hx hr
    hnullC hnullSwapX
  refine hprim (unitAtom_parallel_of_two_readings_zero D (c₀ := y) havoid (by simp) hfix ?_)
  intro c hc hne
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hzeroP
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hzeroX
  · rw [Finset.mem_singleton] at hc; exact absurd hc hne

end Gtz
