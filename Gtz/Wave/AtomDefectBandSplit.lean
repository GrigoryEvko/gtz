import Gtz.Wave.AtomBlockedDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The defect wedge calculus and the band split of the blocked residue

The blocked residue is one obligation, and this module divides it along
the scale mass at `39/50` into a band part and a deep part.  The split
loses nothing: the residue is equivalent to the conjunction of the two
parts.  In the band the landed window theorem supplies a live pivot with
the single inflation budget, and the new engine of this module supplies a
pair of positive pivot minors whose PLAIN shadow cross passes its square
test at that pivot.  Thus the band part follows from one kill: no blocked
band datum admits a single-budget pivot at which every deflated pair
fails.  The kill is the named attack surface, and the dichotomy theorem
here reduces it to one polynomial certificate: a broken pair, at which
the plain cross passes but the deflation defect crosses the bound.

## The measured boundary of the split (probes, banked, not consumed)

The adversarial search refutes the per-pivot law of the previous session.
There is a fully blocked datum with scale mass `0.9997` whose live pivot
of single budget `0.9967` carries NO deflated pair, while three other
pivots carry pairs with margins near `0.04`.  Thus above the band a proof
must select its pivot.  Inside the band the same search stalls at the
positive floor `0.031`, and the floor configuration makes every blocked
inequality an equality at scale mass exactly `39/50`.  The kill is
therefore measured true on the band with a uniform margin, and its proof
must be nearly exact at the all-equalities boundary.

## The realness boundary of the kill

The scaled complex two-trine datum is blocked for every scale mass in
the window from `27/10 - 3 * sqrt 41 / 10` (about `0.77915`) up to one.
The band boundary `39/50` sits above the onset by less than `0.00085`,
thus a thin sliver of the band contains complex data that satisfy every
hypothesis of the kill.  As a result no field-agnostic argument proves
the kill: its proof must consume a real-only ingredient, and the landed
plane closure inside the engine of this module is the approved source.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.defectWedge`, `Gtz.defectWedge_dot_self`,
  `Gtz.planeDefectLagrange` — **THE MINKOWSKI LAGRANGE IDENTITY**: the
  square of the defected cross plus the square of the plane wedge is the
  product of the two defected energies plus the weighted energy of the
  defect wedge.  This identity is exact for every weight.
* `Gtz.defectWedge_read_total`, `Gtz.defectWedge_sq_total`,
  `Gtz.defectWedge_shadow_total` — **THE DEFECT WEDGE MOMENTS**: the
  reading-weighted defect wedges collapse to the fixed vector, and the
  total defect wedge energy is twice the reading energy against the
  frame trace.
* `Gtz.planeWedge_sq_total` — **THE CAUCHY-BINET TOTAL**: the squared
  plane wedges of a tight plane frame add up to two.
* `Gtz.atomShadowCross`, `Gtz.atomShadowCross_eq_shadow`,
  `Gtz.atomGram_mul_atomPivotCross` — **THE DIVISION-FREE SHADOW
  CROSS**: the plain shadow pairing as a polynomial, and the exact
  dictionary between the plain cross and the deflated cross.
* `Gtz.exists_plain_shadow_pair_of_single_budget` — **THE SINGLE-BUDGET
  ENGINE**: a live pivot with the single inflation budget carries a pair
  of positive pivot minors whose plain shadow cross passes.
* `Gtz.broken_defect_certificate`,
  `Gtz.exists_deflated_or_broken_pair_of_single_budget` — **THE
  DICHOTOMY**: at a single-budget pivot, a deflated pair exists or a
  plain pair carries the polynomial broken certificate.
* `Gtz.slackBudget_scale_cubic`, `Gtz.exists_pivot_slack_budget` —
  **THE SLACK PIGEONHOLE**: failure of the slack-shifted single budget
  at every live pivot forces the slack-shifted cubic, thus inside the
  cubic window a pivot with quantified budget slack exists.
* `Gtz.AtomBlockedBandClosed`, `Gtz.AtomBlockedDeepClosed`,
  `Gtz.AtomBlockedBandKill` — **THE SPLIT RESIDUES AND THE KILL.**
* `Gtz.atomBlockedPairClosed_of_band_of_deep`,
  `Gtz.atomBlockedBandClosed_of_blockedPair`,
  `Gtz.atomBlockedDeepClosed_of_blockedPair`,
  `Gtz.atomBlockedPairClosed_iff_band_and_deep` — **THE LOSSLESS
  SPLIT.**
* `Gtz.atomBlockedBandClosed_of_bandKill` — **THE KILL CLOSES THE
  BAND**, through the landed window pigeonhole and the engine.
* `Gtz.gtzWeighted_six_three_of_band_of_deep` and the closure bridges —
  the cell and the rank-three payoff from the two parts, and from the
  kill with the deep part.

## Vacuity

Every law of layers zero thru four is an unconditional statement about
families of vectors, scales and readings.  The split residues of layer
five are vacuous under no hypothesis, and together they are equivalent
to the landed blocked residue by the bridge theorems.
-/

namespace Gtz

/-! ## Layer 0 — the defect wedge calculus -/

/-- The DEFECT WEDGE of two vectors against two readings: the second
reading spreads the first vector, the first reading spreads the second
vector, and the wedge is the difference. -/
def defectWedge {rank : ℕ} (readOne readTwo : ℝ) (vecOne vecTwo : Fin rank → ℝ) :
    Fin rank → ℝ :=
  fun index => readTwo * vecOne index - readOne * vecTwo index

/-- The energy of the defect wedge, expanded through the three dot
products of its two vectors. -/
theorem defectWedge_dot_self {rank : ℕ} (readOne readTwo : ℝ)
    (vecOne vecTwo : Fin rank → ℝ) :
    defectWedge readOne readTwo vecOne vecTwo
        ⬝ᵥ defectWedge readOne readTwo vecOne vecTwo
      = readTwo ^ 2 * (vecOne ⬝ᵥ vecOne)
        - 2 * readOne * readTwo * (vecOne ⬝ᵥ vecTwo)
        + readOne ^ 2 * (vecTwo ⬝ᵥ vecTwo) := by
  simp only [dotProduct, defectWedge]
  have hcell : ∀ index : Fin rank,
      (readTwo * vecOne index - readOne * vecTwo index)
          * (readTwo * vecOne index - readOne * vecTwo index)
        = readTwo ^ 2 * (vecOne index * vecOne index)
          - 2 * readOne * readTwo * (vecOne index * vecTwo index)
          + readOne ^ 2 * (vecTwo index * vecTwo index) :=
    fun index => by ring
  rw [Finset.sum_congr rfl fun index _ => hcell index, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **THE MINKOWSKI LAGRANGE IDENTITY.**  The square of the defected
cross plus the square of the plane wedge is the product of the two
defected energies plus the weighted energy of the defect wedge.  The
identity is exact for every weight, thus the deflation defect reads as
one spacelike wedge against the timelike reading direction. -/
theorem planeDefectLagrange (readOne readTwo weight : ℝ) (vecOne vecTwo : Fin 2 → ℝ) :
    (vecOne ⬝ᵥ vecTwo - weight * readOne * readTwo) ^ 2
        + planeWedge vecOne vecTwo ^ 2
      = (vecOne ⬝ᵥ vecOne - weight * readOne ^ 2)
          * (vecTwo ⬝ᵥ vecTwo - weight * readTwo ^ 2)
        + weight * (defectWedge readOne readTwo vecOne vecTwo
            ⬝ᵥ defectWedge readOne readTwo vecOne vecTwo) := by
  rw [defectWedge_dot_self, dot_fin_two, dot_fin_two, dot_fin_two]
  simp only [planeWedge]
  ring

/-- **THE READING MOMENT OF THE DEFECT WEDGES.**  The reading-weighted
defect wedges against one fixed slot collapse to the reading energy
against the fixed vector, minus the fixed reading against the total
moment.  The identity is unconditional. -/
theorem defectWedge_read_total {slotCount rank : ℕ}
    (vec : Fin slotCount → (Fin rank → ℝ)) (read : Fin slotCount → ℝ)
    (fixed : Fin slotCount) (index : Fin rank) :
    (∑ slot, read slot
        * defectWedge (read fixed) (read slot) (vec fixed) (vec slot) index)
      = (∑ slot, read slot ^ 2) * vec fixed index
        - read fixed * ∑ slot, read slot * vec slot index := by
  simp only [defectWedge]
  have hcell : ∀ slot : Fin slotCount,
      read slot * (read slot * vec fixed index - read fixed * vec slot index)
        = read slot ^ 2 * vec fixed index
          - read fixed * (read slot * vec slot index) :=
    fun slot => by ring
  rw [Finset.sum_congr rfl fun slot _ => hcell slot, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]

/-- **THE DEFECT WEDGE ENERGY TOTAL.**  When the reading moment of a
family vanishes, the total energy of its defect wedges is twice the
reading energy against the frame trace. -/
theorem defectWedge_sq_total {slotCount rank : ℕ}
    (vec : Fin slotCount → (Fin rank → ℝ)) (read : Fin slotCount → ℝ)
    (hmoment : ∀ index : Fin rank, (∑ slot, read slot * vec slot index) = 0) :
    (∑ rowSlot, ∑ colSlot,
        defectWedge (read rowSlot) (read colSlot) (vec rowSlot) (vec colSlot)
          ⬝ᵥ defectWedge (read rowSlot) (read colSlot) (vec rowSlot) (vec colSlot))
      = 2 * (∑ slot, read slot ^ 2) * ∑ slot, vec slot ⬝ᵥ vec slot := by
  have hcross : ∀ rowSlot : Fin slotCount,
      (∑ colSlot, read colSlot * (vec rowSlot ⬝ᵥ vec colSlot)) = 0 := by
    intro rowSlot
    have hswap : (∑ colSlot, read colSlot * (vec rowSlot ⬝ᵥ vec colSlot))
        = ∑ index, vec rowSlot index * ∑ colSlot, read colSlot * vec colSlot index := by
      simp only [dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun index _ =>
        Finset.sum_congr rfl fun colSlot _ => by ring
    rw [hswap]
    exact Finset.sum_eq_zero fun index _ => by rw [hmoment index, mul_zero]
  have hrow : ∀ rowSlot : Fin slotCount,
      (∑ colSlot,
          defectWedge (read rowSlot) (read colSlot) (vec rowSlot) (vec colSlot)
            ⬝ᵥ defectWedge (read rowSlot) (read colSlot) (vec rowSlot) (vec colSlot))
        = (∑ slot, read slot ^ 2) * (vec rowSlot ⬝ᵥ vec rowSlot)
          + read rowSlot ^ 2 * ∑ slot, vec slot ⬝ᵥ vec slot := by
    intro rowSlot
    rw [Finset.sum_congr rfl fun colSlot _ =>
      defectWedge_dot_self (read rowSlot) (read colSlot) (vec rowSlot) (vec colSlot)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum]
    have hmid : (∑ colSlot, 2 * read rowSlot * read colSlot
          * (vec rowSlot ⬝ᵥ vec colSlot))
        = 2 * read rowSlot * ∑ colSlot, read colSlot * (vec rowSlot ⬝ᵥ vec colSlot) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun colSlot _ => by ring
    rw [hmid, hcross rowSlot, mul_zero, sub_zero]
  rw [Finset.sum_congr rfl fun rowSlot _ => hrow rowSlot, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- **THE CAUCHY-BINET TOTAL OF THE PLANE.**  The squared plane wedges
of a tight plane frame add up to two: the frame trace is two and the
Gram square trace is two, and the Lagrange identity subtracts them. -/
theorem planeWedge_sq_total {slotCount : ℕ} (vec : Fin slotCount → (Fin 2 → ℝ))
    (hframe : ∀ probe direction : Fin 2 → ℝ,
      (∑ slot, (vec slot ⬝ᵥ probe) * (vec slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ rowSlot, ∑ colSlot, planeWedge (vec rowSlot) (vec colSlot) ^ 2) = 2 := by
  have htrace : (∑ slot, vec slot ⬝ᵥ vec slot) = 2 := by
    have hcell : ∀ slot : Fin slotCount, vec slot ⬝ᵥ vec slot
        = ∑ index : Fin 2, (vec slot ⬝ᵥ probeUnit index) * (vec slot ⬝ᵥ probeUnit index) :=
      fun slot => by
        simp only [dotProduct_probeUnit]
        simp only [dotProduct]
    have hunit : ∀ index : Fin 2, probeUnit index ⬝ᵥ probeUnit index = 1 := fun index => by
      rw [dotProduct_probeUnit]
      simp [probeUnit]
    rw [Finset.sum_congr rfl fun slot _ => hcell slot, Finset.sum_comm,
      Finset.sum_congr rfl fun index _ => hframe (probeUnit index) (probeUnit index),
      Fin.sum_univ_two, hunit 0, hunit 1]
    norm_num
  have hrowEnergy : ∀ rowSlot : Fin slotCount,
      (∑ colSlot, (vec rowSlot ⬝ᵥ vec colSlot) ^ 2) = vec rowSlot ⬝ᵥ vec rowSlot := by
    intro rowSlot
    rw [← hframe (vec rowSlot) (vec rowSlot)]
    exact Finset.sum_congr rfl fun colSlot _ => by
      rw [dotProduct_comm (vec rowSlot) (vec colSlot)]
      ring
  have hcell : ∀ rowSlot colSlot : Fin slotCount,
      planeWedge (vec rowSlot) (vec colSlot) ^ 2
        = (vec rowSlot ⬝ᵥ vec rowSlot) * (vec colSlot ⬝ᵥ vec colSlot)
          - (vec rowSlot ⬝ᵥ vec colSlot) ^ 2 :=
    fun rowSlot colSlot => by
      linarith [planeWedge_sq_add_dot_sq (vec rowSlot) (vec colSlot)]
  have hrow : ∀ rowSlot : Fin slotCount,
      (∑ colSlot, planeWedge (vec rowSlot) (vec colSlot) ^ 2)
        = (vec rowSlot ⬝ᵥ vec rowSlot) * (∑ slot, vec slot ⬝ᵥ vec slot)
          - (vec rowSlot ⬝ᵥ vec rowSlot) := by
    intro rowSlot
    rw [Finset.sum_congr rfl fun colSlot _ => hcell rowSlot colSlot,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hrowEnergy rowSlot]
  rw [Finset.sum_congr rfl fun rowSlot _ => hrow rowSlot, Finset.sum_sub_distrib,
    ← Finset.sum_mul, htrace]
  norm_num

/-- **THE SHADOW MOMENT OF THE DEFECT WEDGES.**  At a live pivot of an
ambient frame, the reading-weighted defect wedges of the shadows
collapse to the reading energy against the fixed shadow.  The landed
reading moment of the pivot pays the total. -/
theorem defectWedge_shadow_total {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (pivot : Fin slotCount) (haxis : atom pivot ⬝ᵥ atom pivot ≠ 0)
    (fixed : Fin slotCount) (index : Fin rank) :
    (∑ slot, atomGram atom pivot slot
        * defectWedge (atomGram atom pivot fixed) (atomGram atom pivot slot)
            (planeShadow (atom pivot) (atom fixed))
            (planeShadow (atom pivot) (atom slot)) index)
      = (∑ slot, atomGram atom pivot slot ^ 2)
        * planeShadow (atom pivot) (atom fixed) index := by
  have htotal := defectWedge_read_total
    (fun slot => planeShadow (atom pivot) (atom slot)) (atomGram atom pivot) fixed index
  rw [htotal, planeShadow_reading_total hframe pivot haxis index, mul_zero, sub_zero]

/-! ## Layer 1 — the division-free shadow cross -/

/-- The SHADOW CROSS of two slots at a pivot: the pivot diagonal against
the pair entry, minus the product of the two pivot readings.  This is
the plain shadow pairing scaled by the pivot diagonal, as a
polynomial. -/
def atomShadowCross {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (pivot slotOne slotTwo : Fin slotCount) : ℝ :=
  atomGram atom pivot pivot * atomGram atom slotOne slotTwo
    - atomGram atom pivot slotOne * atomGram atom pivot slotTwo

/-- The shadow cross reads as the pivot diagonal against the shadow
pairing. -/
theorem atomShadowCross_eq_shadow {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {pivot : Fin slotCount}
    (slotOne slotTwo : Fin slotCount)
    (hdiag : atomGram atom pivot pivot ≠ 0) :
    atomShadowCross atom pivot slotOne slotTwo
      = atomGram atom pivot pivot
        * (planeShadow (atom pivot) (atom slotOne)
            ⬝ᵥ planeShadow (atom pivot) (atom slotTwo)) := by
  have haxisNe : atom pivot ⬝ᵥ atom pivot ≠ 0 := by
    simpa only [atomGram] using hdiag
  rw [planeShadow_dot_shadow _ _ _ haxisNe]
  simp only [atomShadowCross, atomGram]
  rw [dotProduct_comm (atom slotOne) (atom pivot),
    dotProduct_comm (atom slotTwo) (atom pivot)]
  field_simp

/-- **THE DIVISION-FREE DEFLATION DICTIONARY.**  The pivot diagonal
against the deflated cross is the shifted diagonal against the shadow
cross, minus the pivot scale against the product of the two readings.
The identity is polynomial and unconditional. -/
theorem atomGram_mul_atomPivotCross {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot slotOne slotTwo : Fin slotCount) :
    atomGram atom pivot pivot * atomPivotCross atom scale pivot slotOne slotTwo
      = atomShiftedDiag atom scale pivot * atomShadowCross atom pivot slotOne slotTwo
        - scale pivot * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo) := by
  simp only [atomPivotCross, atomShadowCross, atomShiftedDiag]
  ring

/-! ## Layer 2 — the single-budget engine -/

/-- **THE SINGLE-BUDGET ENGINE.**  A pivot of positive shifted diagonal
whose SINGLE inflation budget holds supplies two slots of positive pivot
minor whose plain shadow cross passes its square test.  The landed plane
closure fires at the singly inflated scales, and the public dictionary
reads the plain gaps as the pivot minors with no loss. -/
theorem exists_plain_shadow_pair_of_single_budget
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hbudget : ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
        + scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ 0 < atomPairMinor atom scale pivot slotTwo
        ∧ (atomShiftedDiag atom scale pivot
              * atomShadowCross atom pivot slotOne slotTwo) ^ 2
            < atomGram atom pivot pivot ^ 2
              * (atomPairMinor atom scale pivot slotOne
                * atomPairMinor atom scale pivot slotTwo) := by
  classical
  have hdiagPos : 0 < atomGram atom pivot pivot := by
    have hp := hscale pivot
    have hR := hpivot
    simp only [atomShiftedDiag] at hR
    linarith
  have hdiagNe : atomGram atom pivot pivot ≠ 0 := ne_of_gt hdiagPos
  have hRne : atomShiftedDiag atom scale pivot ≠ 0 := ne_of_gt hpivot
  have hRne' : atomGram atom pivot pivot - scale pivot ≠ 0 := by
    have hval := hpivot
    simp only [atomShiftedDiag] at hval
    exact ne_of_gt hval
  have haxisNe : atom pivot ⬝ᵥ atom pivot ≠ 0 := by
    have := hdiagPos
    simp only [atomGram] at this
    exact ne_of_gt this
  have hshadowPivot : planeShadow (atom pivot) (atom pivot) = 0 :=
    planeShadow_self_eq_zero haxisNe
  have hperp : ∀ slot : Fin 6, planeShadow (atom pivot) (atom slot) ⬝ᵥ atom pivot = 0 :=
    fun slot => planeShadow_dot_axis (atom pivot) (atom slot) haxisNe
  have hshadowFrame : ∀ probe direction : Fin 3 → ℝ,
      probe ⬝ᵥ atom pivot = 0 → direction ⬝ᵥ atom pivot = 0 →
      (∑ slot, (planeShadow (atom pivot) (atom slot) ⬝ᵥ probe)
          * (planeShadow (atom pivot) (atom slot) ⬝ᵥ direction)) = probe ⬝ᵥ direction := by
    intro probe direction hprobe hdirection
    rw [← hframe probe direction]
    exact Finset.sum_congr rfl fun slot _ => by
      rw [planeShadow_dot_plane (atom pivot) (atom slot) probe hprobe,
        planeShadow_dot_plane (atom pivot) (atom slot) direction hdirection]
  have hdeflNonneg : 0 ≤ scale pivot
      / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) :=
    div_nonneg (hscale pivot) (mul_nonneg hdiagPos.le hpivot.le)
  have hinflNonneg : ∀ slot : Fin 6, 0 ≤ (if slot = pivot then (0:ℝ)
      else scale slot + (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2) := by
    intro slot
    by_cases hcase : slot = pivot
    · rw [if_pos hcase]
    · rw [if_neg hcase]
      have hterm := mul_nonneg hdeflNonneg (sq_nonneg (atomGram atom pivot slot))
      linarith [hscale slot]
  have hrowEnergy : (∑ slot ∈ Finset.univ.erase pivot, atomGram atom pivot slot ^ 2)
      = atomGram atom pivot pivot - atomGram atom pivot pivot ^ 2 := by
    have hsplit := Finset.sum_erase_eq_sub
      (f := fun slot => atomGram atom pivot slot ^ 2) (Finset.mem_univ pivot)
    rw [hsplit, atomGram_row_energy hframe pivot]
  have hinflSum : (∑ slot, (if slot = pivot then (0:ℝ)
      else scale slot + (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2)) < 1 := by
    have hsplit : (∑ slot, (if slot = pivot then (0:ℝ)
        else scale slot + (scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2))
        = ∑ slot ∈ Finset.univ.erase pivot, (scale slot + (scale pivot
            / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slot ^ 2) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ pivot)]
      rw [if_pos rfl, add_zero]
      exact Finset.sum_congr rfl fun slot hslot =>
        if_neg (Finset.mem_erase.mp hslot).1
    have hfold : (∑ slot ∈ Finset.univ.erase pivot, (scale pivot
        / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
        * atomGram atom pivot slot ^ 2)
        = (scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot))
          * (atomGram atom pivot pivot - atomGram atom pivot pivot ^ 2) := by
      rw [← hrowEnergy, Finset.mul_sum]
    rw [hsplit, Finset.sum_add_distrib,
      Finset.sum_erase_eq_sub (f := scale) (Finset.mem_univ pivot), hfold]
    have hcancel : scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)
        * (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot)
        = scale pivot :=
      div_mul_cancel₀ _ (mul_ne_zero hdiagNe hRne)
    have hcancelSq : scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)
        * (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot)
        * atomGram atom pivot pivot
        = scale pivot * atomGram atom pivot pivot := by
      rw [hcancel]
    nlinarith [hbudget, hpivot, hcancel, hcancelSq]
  obtain ⟨slotOne, slotTwo, hneOneTwo, hgapRaw, hdetRaw⟩ :=
    atomPairGramClosed_holds (fun slot => planeShadow (atom pivot) (atom slot))
      (fun slot => if slot = pivot then (0:ℝ)
        else scale slot + (scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2)
      (atom pivot)
      (by
        have := hdiagPos
        simp only [atomGram] at this
        exact this)
      hperp hinflNonneg hinflSum hshadowFrame
  have hOneNe : slotOne ≠ pivot := by
    intro heq
    rw [heq, hshadowPivot, if_pos rfl] at hgapRaw
    simp at hgapRaw
  have hTwoNe : slotTwo ≠ pivot := by
    intro heq
    rw [heq, hshadowPivot, if_pos rfl] at hdetRaw
    simp at hdetRaw
  rw [if_neg hOneNe] at hgapRaw hdetRaw
  rw [if_neg hTwoNe] at hdetRaw
  have huTwo : 0 < planeShadow (atom pivot) (atom slotTwo)
        ⬝ᵥ planeShadow (atom pivot) (atom slotTwo)
      - (scale slotTwo + (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2) := by
    nlinarith [hdetRaw, hgapRaw,
      sq_nonneg (planeShadow (atom pivot) (atom slotOne)
        ⬝ᵥ planeShadow (atom pivot) (atom slotTwo))]
  have hminorOne : 0 < atomPairMinor atom scale pivot slotOne := by
    rw [atomPairMinor_eq_shadow slotOne hdiagNe hRne']
    refine mul_pos hpivot ?_
    linarith [hgapRaw]
  have hminorTwo : 0 < atomPairMinor atom scale pivot slotTwo := by
    rw [atomPairMinor_eq_shadow slotTwo hdiagNe hRne']
    refine mul_pos hpivot ?_
    linarith [huTwo]
  refine ⟨slotOne, slotTwo, fun heq => hOneNe heq.symm, fun heq => hTwoNe heq.symm,
    hneOneTwo, hminorOne, hminorTwo, ?_⟩
  rw [atomShadowCross_eq_shadow slotOne slotTwo hdiagNe,
    atomPairMinor_eq_shadow slotOne hdiagNe hRne',
    atomPairMinor_eq_shadow slotTwo hdiagNe hRne']
  have hfactor : 0 < (atomShiftedDiag atom scale pivot * atomGram atom pivot pivot) ^ 2 :=
    pow_pos (mul_pos hpivot hdiagPos) 2
  nlinarith [mul_lt_mul_of_pos_left hdetRaw hfactor]

/-! ## Layer 3 — the broken dichotomy -/

/-- **THE BROKEN CERTIFICATE.**  When a plain square test passes its
bound but the defected square test fails it, the defect beats twice the
aligned cross by at least the plain margin. -/
theorem broken_defect_certificate {plain defect bound : ℝ}
    (hbroken : bound ≤ (plain - defect) ^ 2) :
    bound - plain ^ 2 ≤ defect * (defect - 2 * plain) := by
  nlinarith [hbroken]

/-- **THE DICHOTOMY.**  At a single-budget live pivot, a deflated pair
exists, or a plain pair carries the polynomial broken certificate: the
plain shadow cross passes while the deflation defect crosses the bound
by at least the plain margin. -/
theorem exists_deflated_or_broken_pair_of_single_budget
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hbudget : ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
        + scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ 0 < atomPairMinor atom scale pivot slotTwo
        ∧ (atomPivotCross atom scale pivot slotOne slotTwo ^ 2
              < atomPairMinor atom scale pivot slotOne
                * atomPairMinor atom scale pivot slotTwo
          ∨ ((atomShiftedDiag atom scale pivot
                  * atomShadowCross atom pivot slotOne slotTwo) ^ 2
                < atomGram atom pivot pivot ^ 2
                  * (atomPairMinor atom scale pivot slotOne
                    * atomPairMinor atom scale pivot slotTwo)
              ∧ atomGram atom pivot pivot ^ 2
                    * (atomPairMinor atom scale pivot slotOne
                      * atomPairMinor atom scale pivot slotTwo)
                  - (atomShiftedDiag atom scale pivot
                      * atomShadowCross atom pivot slotOne slotTwo) ^ 2
                ≤ scale pivot
                    * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)
                  * (scale pivot
                      * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)
                    - 2 * (atomShiftedDiag atom scale pivot
                        * atomShadowCross atom pivot slotOne slotTwo)))) := by
  obtain ⟨slotOne, slotTwo, honePivot, htwoPivot, hpairNe, hminorOne, hminorTwo, hplain⟩ :=
    exists_plain_shadow_pair_of_single_budget hframe hscale hpivot hbudget
  refine ⟨slotOne, slotTwo, honePivot, htwoPivot, hpairNe, hminorOne, hminorTwo, ?_⟩
  by_cases hdefl : atomPivotCross atom scale pivot slotOne slotTwo ^ 2
      < atomPairMinor atom scale pivot slotOne * atomPairMinor atom scale pivot slotTwo
  · exact Or.inl hdefl
  · refine Or.inr ⟨hplain, ?_⟩
    have hfail := not_lt.mp hdefl
    have hdict := atomGram_mul_atomPivotCross atom scale pivot slotOne slotTwo
    have hsq : atomGram atom pivot pivot ^ 2
        * atomPivotCross atom scale pivot slotOne slotTwo ^ 2
        = (atomShiftedDiag atom scale pivot
              * atomShadowCross atom pivot slotOne slotTwo
            - scale pivot
              * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2 := by
      linear_combination (atomGram atom pivot pivot
          * atomPivotCross atom scale pivot slotOne slotTwo
        + atomShiftedDiag atom scale pivot * atomShadowCross atom pivot slotOne slotTwo
        - scale pivot * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo))
        * hdict
    have hbound : atomGram atom pivot pivot ^ 2
        * (atomPairMinor atom scale pivot slotOne
          * atomPairMinor atom scale pivot slotTwo)
        ≤ (atomShiftedDiag atom scale pivot
              * atomShadowCross atom pivot slotOne slotTwo
            - scale pivot
              * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2 := by
      rw [← hsq]
      exact mul_le_mul_of_nonneg_left hfail
        (sq_nonneg (atomGram atom pivot pivot))
    exact broken_defect_certificate hbound

/-! ## Layer 4 — the slack pigeonhole -/

/-- **THE SLACK CUBIC.**  When every slot of positive shifted diagonal
fails the slack-shifted single budget, the scale mass obeys the
slack-shifted cubic.  The landed pigeonhole chain runs with the slack
folded into its leading coefficient. -/
theorem slackBudget_scale_cubic
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1) {slack : ℝ}
    (hfail : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      (1 - slack) * atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)) :
    (1 - slack - ∑ slot, scale slot) * (3 - ∑ slot, scale slot)
        * (6 - ∑ slot, scale slot)
      ≤ 3 * ∑ slot, scale slot := by
  classical
  have hmassNonneg : 0 ≤ ∑ slot, scale slot :=
    Finset.sum_nonneg fun slot _ => hscale slot
  have hthree : (0:ℝ) ≤ 3 - ∑ slot, scale slot := by linarith
  have hsix : (0:ℝ) ≤ 6 - ∑ slot, scale slot := by linarith
  rcases le_or_gt (1 - slack - ∑ slot, scale slot) 0 with htriv | hdelta
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg htriv (mul_nonneg hthree hsix),
      hmassNonneg]
  have hlive : ∀ slot ∈ Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot),
      0 < atomShiftedDiag atom scale slot :=
    fun slot hslot => (Finset.mem_filter.mp hslot).2
  have hRfloor : (3 : ℝ) - (∑ slot, scale slot)
      ≤ ∑ slot ∈ Finset.univ.filter (fun slot => 0 < atomShiftedDiag atom scale slot),
          atomShiftedDiag atom scale slot := by
    have htotal := atomShiftedDiag_total hframe scale
    push_cast at htotal
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun slot => 0 < atomShiftedDiag atom scale slot) (atomShiftedDiag atom scale)
    have hnonpos : (∑ slot ∈ Finset.univ.filter
        (fun slot => ¬ 0 < atomShiftedDiag atom scale slot),
          atomShiftedDiag atom scale slot) ≤ 0 :=
      Finset.sum_nonpos fun slot hslot => not_lt.mp (Finset.mem_filter.mp hslot).2
    linarith [htotal, hsplit, hnonpos]
  have hA : ∀ slot ∈ Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot),
      atomShiftedDiag atom scale slot * (1 - slack - ∑ other, scale other)
        + 2 * (scale slot * atomShiftedDiag atom scale slot)
      ≤ scale slot := by
    intro slot hslot
    have hb := hfail slot (hlive slot hslot)
    have hgram : atomGram atom slot slot = atomShiftedDiag atom scale slot + scale slot := by
      simp only [atomShiftedDiag]
      ring
    rw [hgram] at hb
    nlinarith [hb, sq_nonneg (scale slot)]
  have hB : ∀ slot ∈ Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot),
      (1 - slack - ∑ other, scale other) * atomShiftedDiag atom scale slot ^ 2
        ≤ scale slot * atomShiftedDiag atom scale slot := by
    intro slot hslot
    have ha := hA slot hslot
    have hR := hlive slot hslot
    have hsR : 0 ≤ scale slot * atomShiftedDiag atom scale slot :=
      mul_nonneg (hscale slot) hR.le
    have hlin : (1 - slack - ∑ other, scale other) * atomShiftedDiag atom scale slot
        ≤ scale slot := by nlinarith [ha, hsR]
    nlinarith [mul_le_mul_of_nonneg_right hlin hR.le]
  have hAsum := Finset.sum_le_sum hA
  have hBsum := Finset.sum_le_sum hB
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum] at hAsum
  rw [← Finset.mul_sum] at hBsum
  have hscaleCap : (∑ slot ∈ Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot), scale slot)
      ≤ ∑ slot, scale slot :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun slot _ _ => hscale slot
  have hbase := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ.filter (fun slot => 0 < atomShiftedDiag atom scale slot))
    (fun _ => (1:ℝ)) (atomShiftedDiag atom scale)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hbase
  have hcard : ((Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot)).card : ℝ) ≤ 6 := by
    have hle : (Finset.univ.filter
        (fun slot => 0 < atomShiftedDiag atom scale slot)).card ≤ 6 := by
      simpa using Finset.card_filter_le Finset.univ
        (fun slot => 0 < atomShiftedDiag atom scale slot)
    exact_mod_cast hle
  have hQnonneg : 0 ≤ ∑ slot ∈ Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot),
        atomShiftedDiag atom scale slot ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs : (∑ slot ∈ Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot),
        atomShiftedDiag atom scale slot) ^ 2
      ≤ 6 * ∑ slot ∈ Finset.univ.filter
          (fun slot => 0 < atomShiftedDiag atom scale slot),
            atomShiftedDiag atom scale slot ^ 2 := by
    nlinarith [hbase, hcard, hQnonneg]
  have hTfloorSq : (3 - ∑ slot, scale slot) ^ 2
      ≤ (∑ slot ∈ Finset.univ.filter
          (fun slot => 0 < atomShiftedDiag atom scale slot),
            atomShiftedDiag atom scale slot) ^ 2 := by
    nlinarith [hRfloor, hthree]
  have hstepOne : (1 - slack - ∑ slot, scale slot) * (3 - ∑ slot, scale slot) ^ 2
      ≤ 6 * (1 - slack - ∑ slot, scale slot)
        * ∑ slot ∈ Finset.univ.filter
            (fun slot => 0 < atomShiftedDiag atom scale slot),
              atomShiftedDiag atom scale slot ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hTfloorSq hdelta.le,
      mul_le_mul_of_nonneg_left hcs hdelta.le]
  have hTlin : (1 - slack - ∑ slot, scale slot) * (3 - ∑ slot, scale slot)
      ≤ (1 - slack - ∑ slot, scale slot)
        * ∑ slot ∈ Finset.univ.filter
            (fun slot => 0 < atomShiftedDiag atom scale slot),
              atomShiftedDiag atom scale slot :=
    mul_le_mul_of_nonneg_left hRfloor hdelta.le
  nlinarith [hstepOne, hBsum, hAsum, hTlin, hscaleCap, hdelta.le, hthree, hmassNonneg]

/-- **THE SLACK PIGEONHOLE.**  Inside the slack-shifted cubic window a
live pivot exists whose single budget clears with the given slack.  The
quantified slack is the fuel of every lossy step at that pivot. -/
theorem exists_pivot_slack_budget
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1) {slack : ℝ}
    (hwindow : 3 * (∑ slot, scale slot)
      < (1 - slack - ∑ slot, scale slot) * (3 - ∑ slot, scale slot)
          * (6 - ∑ slot, scale slot)) :
    ∃ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot
      ∧ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)
        < (1 - slack) * atomShiftedDiag atom scale pivot := by
  by_contra hno
  have hfail : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      (1 - slack) * atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot) := by
    intro pivot hpos
    by_contra hlt
    exact hno ⟨pivot, hpos, not_le.mp hlt⟩
  have hcubic := slackBudget_scale_cubic hframe hscale hsmall hfail
  linarith

/-! ## Layer 5 — the band split of the blocked residue -/

/-- **THE BAND RESIDUE.**  The blocked residue restricted to scale mass
at most `39/50`.  The landed window theorem supplies a single-budget
pivot on this side, and the measured floor of the kill is `0.031`. -/
def AtomBlockedBandClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) →
    (∑ slot, scale slot) ≤ 39 / 50 →
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo

/-- **THE DEEP RESIDUE.**  The blocked residue restricted to scale mass
above `39/50`.  The refuted per-pivot law lives on this side: a proof
here must select its pivot. -/
def AtomBlockedDeepClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) →
    39 / 50 < (∑ slot, scale slot) →
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo

/-- **THE BAND KILL.**  No blocked band datum admits a single-budget
live pivot at which every deflated pair fails.  This is the named attack
surface: the adversarial floor of its margin is `0.031`, and the sliver
of the band above the trine onset carries its realness obligation. -/
def AtomBlockedBandKill : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) →
    (∑ slot, scale slot) ≤ 39 / 50 →
    ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)
        < atomShiftedDiag atom scale pivot →
      (∀ slotOne slotTwo : Fin 6,
        pivot ≠ slotOne → pivot ≠ slotTwo → slotOne ≠ slotTwo →
        0 < atomPairMinor atom scale pivot slotOne →
        atomPairMinor atom scale pivot slotOne
            * atomPairMinor atom scale pivot slotTwo
          ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2) →
      False

/-- **THE SPLIT ASSEMBLES.**  The two parts close the blocked
residue. -/
theorem atomBlockedPairClosed_of_band_of_deep
    (hband : AtomBlockedBandClosed) (hdeep : AtomBlockedDeepClosed) :
    AtomBlockedPairClosed := by
  intro atom scale hpos hsmall hframe hblocked
  rcases le_or_gt (∑ slot, scale slot) (39 / 50) with hside | hside
  · exact hband atom scale hpos hsmall hframe hblocked hside
  · exact hdeep atom scale hpos hsmall hframe hblocked hside

/-- The blocked residue carries the band part. -/
theorem atomBlockedBandClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : AtomBlockedBandClosed :=
  fun atom scale hpos hsmall hframe hblocked _ =>
    hresidue atom scale hpos hsmall hframe hblocked

/-- The blocked residue carries the deep part. -/
theorem atomBlockedDeepClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : AtomBlockedDeepClosed :=
  fun atom scale hpos hsmall hframe hblocked _ =>
    hresidue atom scale hpos hsmall hframe hblocked

/-- **THE SPLIT IS LOSSLESS.**  The blocked residue is one obligation
with two halves. -/
theorem atomBlockedPairClosed_iff_band_and_deep :
    AtomBlockedPairClosed ↔ AtomBlockedBandClosed ∧ AtomBlockedDeepClosed :=
  ⟨fun hresidue => ⟨atomBlockedBandClosed_of_blockedPair hresidue,
      atomBlockedDeepClosed_of_blockedPair hresidue⟩,
    fun hpair => atomBlockedPairClosed_of_band_of_deep hpair.1 hpair.2⟩

/-- **THE KILL CLOSES THE BAND.**  The landed window pigeonhole selects
a single-budget live pivot on the band side, and the kill fires at
it. -/
theorem atomBlockedBandClosed_of_bandKill
    (hkill : AtomBlockedBandKill) : AtomBlockedBandClosed := by
  intro atom scale hpos hsmall hframe hblocked hband
  by_contra hno
  push Not at hno
  obtain ⟨pivot, hlive, hsingle⟩ :=
    exists_pivot_single_budget_of_scale_le hframe (fun slot => (hpos slot).le) hband
  exact hkill atom scale hpos hsmall hframe hblocked hband pivot hlive hsingle
    fun slotOne slotTwo honePivot htwoPivot hpairNe hminor =>
      hno pivot slotOne slotTwo honePivot htwoPivot hpairNe hlive hminor

/-! ## Layer 6 — the cell and the payoff from the split -/

/-- **THE `(6,3)` CELL FROM THE TWO PARTS.** -/
theorem gtzWeighted_six_three_of_band_of_deep
    (hband : AtomBlockedBandClosed) (hdeep : AtomBlockedDeepClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_blockedPair
    (atomBlockedPairClosed_of_band_of_deep hband hdeep)

/-- **THE RANK-THREE PAYOFF FROM THE TWO PARTS.** -/
theorem gtzWeightedAll_three_of_band_of_deep
    (hband : AtomBlockedBandClosed) (hdeep : AtomBlockedDeepClosed) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_blockedPair
    (atomBlockedPairClosed_of_band_of_deep hband hdeep)

/-- The crux type is empty under the two parts. -/
theorem isEmpty_sixThreeCrux_of_band_of_deep
    (hband : AtomBlockedBandClosed) (hdeep : AtomBlockedDeepClosed) :
    IsEmpty SixThreeCrux :=
  isEmpty_sixThreeCrux_of_blockedPair
    (atomBlockedPairClosed_of_band_of_deep hband hdeep)

/-- **THE `(6,3)` CELL FROM THE KILL AND THE DEEP PART.** -/
theorem gtzWeighted_six_three_of_bandKill_of_deep
    (hkill : AtomBlockedBandKill) (hdeep : AtomBlockedDeepClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_band_of_deep
    (atomBlockedBandClosed_of_bandKill hkill) hdeep

/-- **THE RANK-THREE PAYOFF FROM THE KILL AND THE DEEP PART.** -/
theorem gtzWeightedAll_three_of_bandKill_of_deep
    (hkill : AtomBlockedBandKill) (hdeep : AtomBlockedDeepClosed) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_band_of_deep
    (atomBlockedBandClosed_of_bandKill hkill) hdeep

end Gtz
