import Gtz.Wave.AtomPivotDeflation
import Gtz.Wave.PlaneCapTripleClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The shadow transfer — the deflated pair from the plane closure

The plane lane is closed, and this module lifts it.  At a pivot of
positive shifted diagonal, the shadows of the atoms form a tight frame of
the plane orthogonal to the pivot atom.  The deflated pair matrix at that
pivot is the plain shadow pair matrix at INFLATED scales plus one
positive semidefinite rank-one term.  Thus the landed plane pair theorem
supplies the deflated pair, and one budget on the pivot carries the whole
transfer.  The inflation of one slot is two deflation weights against the
squared pivot reading, and the budget is division free.

The budget is sharp.  At the regular tetrahedron the budget margin is
`3 * eta * (3 + eta) / (4 * (2 + eta))` with `eta` the scale slack, thus
the extremal family sits exactly on the boundary of the closed stratum
and the strict scale bound is consumed with no slack.

Three regimes fall out.  A HEAVY slot (`2 + scale <= 3 * diagonal`)
always carries the budget.  A scale mass below `13/20` always supplies a
budget pivot, through one cubic pigeonhole — the first unconditional
regime of the third rung beyond the quarter threshold.  The residue is
the BLOCKED stratum: every pivot of positive shifted diagonal fails the
budget, and that stratum forces the scale mass above `13/20`.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.planeShadow_self_eq_zero`, `Gtz.planeShadow_dot_shadow` — the
  shadow calculus of one pivot.
* `Gtz.deflated_cross_nonneg`, `Gtz.transfer_pair_lt` — **THE TRANSFER
  CORE**: the deflated pair matrix beats the inflated plain pair matrix
  by one rank-one square.
* `Gtz.exists_deflated_pair_of_pivot_budget` — **THE ENGINE**: a pivot
  of positive shifted diagonal with the division-free budget supplies
  the deflated pair, through the landed plane closure.
* `Gtz.exists_pivotPair_of_pivot_budget`,
  `Gtz.exists_sylvester_of_pivot_budget`,
  `Gtz.exists_dominating_carrier_of_pivot_budget` — the pivot pair, the
  Sylvester chain and the dominating carrier from one budget pivot.
* `Gtz.pivot_budget_of_heavy_slot`,
  `Gtz.exists_dominating_carrier_of_heavy_slot` — **THE HEAVY STRATUM**:
  a slot with `2 + scale <= 3 * diagonal` closes the datum.
* `Gtz.blocked_slot_light` — a blocked slot is never heavy.
* `Gtz.blocked_scale_cubic`, `Gtz.blocked_scale_lt` — **THE BLOCKED
  WINDOW**: the blocked stratum forces
  `(1 - mass) * (3 - mass) * (7 - mass) <= 8 * mass`, thus a scale mass
  above `13/20`.
* `Gtz.exists_pivot_budget_of_scale_lt` — below `13/20` a budget pivot
  always exists.
* `Gtz.exists_dominating_triple_of_scale_lt_thirteen_twentieths` —
  **THE THRESHOLD**: the atom triple ceiling holds at every scale mass
  below `13/20`, with nonnegative scales.
* `Gtz.AtomBlockedPivotClosed` — **THE RESIDUE**, strictly inside the
  polynomial residue: only the blocked stratum stays open.
* `Gtz.atomTripleCeilingClosed_of_blockedPivot`,
  `Gtz.gtzWeighted_six_three_of_blockedPivot`,
  `Gtz.gtzWeightedAll_three_of_blockedPivot`,
  `Gtz.isEmpty_sixThreeCrux_of_blockedPivot` — **THE CELL FROM THE
  BLOCKED RESIDUE**, with no side hypothesis.
* `Gtz.rankFiveDenseClosed_of_blockedPivot`,
  `Gtz.rankSixDenseClosed_of_blockedPivot`, the five dense profile
  closures and the three support-two closures from the same residue.

## Vacuity

Every law of layers zero thru six is an unconditional statement about a
family of vectors and a family of scales, and the engine consumes the
landed theorem `Gtz.atomPairGramClosed_holds`.  The residue of layer
seven is vacuous under no hypothesis.
-/

namespace Gtz

/-! ## Layer 0 — the shadow calculus of one pivot -/

/-- The shadow of the axis in its own plane is zero. -/
theorem planeShadow_self_eq_zero {rank : ℕ} {axis : Fin rank → ℝ}
    (haxis : axis ⬝ᵥ axis ≠ 0) : planeShadow axis axis = 0 := by
  funext index
  rw [planeShadow_apply, div_self haxis, one_mul, sub_self]
  rfl

/-- **THE SHADOW GRAM.**  The dot product of two shadows is the dot
product of the two vectors minus the product of the two axis readings
over the axis energy. -/
theorem planeShadow_dot_shadow {rank : ℕ} (axis vecOne vecTwo : Fin rank → ℝ)
    (haxis : axis ⬝ᵥ axis ≠ 0) :
    planeShadow axis vecOne ⬝ᵥ planeShadow axis vecTwo
      = vecOne ⬝ᵥ vecTwo - (vecOne ⬝ᵥ axis) * (vecTwo ⬝ᵥ axis) / (axis ⬝ᵥ axis) := by
  rw [planeShadow_dot_plane axis vecOne (planeShadow axis vecTwo)
    (planeShadow_dot_axis axis vecTwo haxis),
    dotProduct_comm vecOne (planeShadow axis vecTwo), planeShadow_eq, dot_sub_smul,
    dotProduct_comm vecTwo vecOne, dotProduct_comm axis vecOne]
  ring

/-! ## Layer 1 — the transfer core -/

/-- **THE SIGN LAW OF THE DEFLATED CROSS.**  Two positive inflated gaps
that beat the cross square make the mixed rank-one reading nonnegative. -/
theorem deflated_cross_nonneg {uOne uTwo cross gOne gTwo : ℝ}
    (hone : 0 < uOne) (htwo : 0 < uTwo) (hcross : cross ^ 2 < uOne * uTwo) :
    0 ≤ gOne ^ 2 * uTwo + gTwo ^ 2 * uOne + 2 * gOne * gTwo * cross := by
  have hdiag : 0 ≤ gOne ^ 2 * uTwo + gTwo ^ 2 * uOne :=
    add_nonneg (mul_nonneg (sq_nonneg gOne) htwo.le)
      (mul_nonneg (sq_nonneg gTwo) hone.le)
  have hsq : (2 * gOne * gTwo * cross) ^ 2 ≤ (gOne ^ 2 * uTwo + gTwo ^ 2 * uOne) ^ 2 := by
    nlinarith [sq_nonneg (gOne ^ 2 * uTwo - gTwo ^ 2 * uOne),
      mul_nonneg (sq_nonneg (gOne * gTwo)) (sub_nonneg.mpr hcross.le)]
  by_contra hneg
  have hlt : gOne ^ 2 * uTwo + gTwo ^ 2 * uOne + 2 * gOne * gTwo * cross < 0 :=
    not_le.mp hneg
  have hgap : 0 < gOne ^ 2 * uTwo + gTwo ^ 2 * uOne - 2 * gOne * gTwo * cross := by
    linarith
  nlinarith [mul_pos (show (0:ℝ) < -(gOne ^ 2 * uTwo + gTwo ^ 2 * uOne
    + 2 * gOne * gTwo * cross) by linarith) hgap]

/-- **THE TRANSFER.**  The deflated pair matrix is the plain pair matrix
at doubly inflated scales plus one rank-one square, thus a plain pair at
the inflated scales supplies the deflated pair test. -/
theorem transfer_pair_lt {uOne uTwo cross gOne gTwo defl : ℝ} (hdefl : 0 ≤ defl)
    (hone : 0 < uOne) (htwo : 0 < uTwo) (hcross : cross ^ 2 < uOne * uTwo) :
    (cross - defl * (gOne * gTwo)) ^ 2
      < (uOne + defl * gOne ^ 2) * (uTwo + defl * gTwo ^ 2) := by
  have hkey := deflated_cross_nonneg (gOne := gOne) (gTwo := gTwo) hone htwo hcross
  have hexp : (uOne + defl * gOne ^ 2) * (uTwo + defl * gTwo ^ 2)
      - (cross - defl * (gOne * gTwo)) ^ 2
      = (uOne * uTwo - cross ^ 2)
        + defl * (gOne ^ 2 * uTwo + gTwo ^ 2 * uOne + 2 * gOne * gTwo * cross) := by
    ring
  linarith [hexp, mul_nonneg hdefl hkey, hcross]

/-! ## Layer 2 — the engine -/

/-- **THE ENGINE.**  A pivot of positive shifted diagonal whose
division-free budget holds supplies a deflated pair off the pivot: both
pivot minors are positive and the deflated cross entry beats its square
test.  The pair comes from the landed plane closure applied to the
shadows at the doubly inflated scales, and the transfer identity carries
the rank-one defect. -/
theorem exists_deflated_pair_of_pivot_budget
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hbudget : ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
        + 2 * scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ 0 < atomPairMinor atom scale pivot slotTwo
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo := by
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
      else scale slot + 2 * (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2) := by
    intro slot
    by_cases hcase : slot = pivot
    · rw [if_pos hcase]
    · rw [if_neg hcase]
      have hterm := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hdeflNonneg)
        (sq_nonneg (atomGram atom pivot slot))
      linarith [hscale slot]
  have hrowEnergy : (∑ slot ∈ Finset.univ.erase pivot, atomGram atom pivot slot ^ 2)
      = atomGram atom pivot pivot - atomGram atom pivot pivot ^ 2 := by
    have hsplit := Finset.sum_erase_eq_sub
      (f := fun slot => atomGram atom pivot slot ^ 2) (Finset.mem_univ pivot)
    rw [hsplit, atomGram_row_energy hframe pivot]
  have hinflSum : (∑ slot, (if slot = pivot then (0:ℝ)
      else scale slot + 2 * (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2)) < 1 := by
    have hsplit : (∑ slot, (if slot = pivot then (0:ℝ)
        else scale slot + 2 * (scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2))
        = ∑ slot ∈ Finset.univ.erase pivot, (scale slot + 2 * (scale pivot
            / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slot ^ 2) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ pivot)]
      rw [if_pos rfl, add_zero]
      exact Finset.sum_congr rfl fun slot hslot =>
        if_neg (Finset.mem_erase.mp hslot).1
    have hfold : (∑ slot ∈ Finset.univ.erase pivot, 2 * (scale pivot
        / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
        * atomGram atom pivot slot ^ 2)
        = 2 * (scale pivot / (atomGram atom pivot pivot
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
        else scale slot + 2 * (scale pivot / (atomGram atom pivot pivot
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
      - (scale slotTwo + 2 * (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2) := by
    nlinarith [hdetRaw, hgapRaw,
      sq_nonneg (planeShadow (atom pivot) (atom slotOne)
        ⬝ᵥ planeShadow (atom pivot) (atom slotTwo))]
  have hMone : planeShadow (atom pivot) (atom slotOne)
        ⬝ᵥ planeShadow (atom pivot) (atom slotOne)
      = atomGram atom slotOne slotOne
        - atomGram atom pivot slotOne ^ 2 / atomGram atom pivot pivot := by
    rw [planeShadow_dot_shadow _ _ _ haxisNe]
    simp only [atomGram]
    rw [dotProduct_comm (atom slotOne) (atom pivot)]
    ring
  have hMtwo : planeShadow (atom pivot) (atom slotTwo)
        ⬝ᵥ planeShadow (atom pivot) (atom slotTwo)
      = atomGram atom slotTwo slotTwo
        - atomGram atom pivot slotTwo ^ 2 / atomGram atom pivot pivot := by
    rw [planeShadow_dot_shadow _ _ _ haxisNe]
    simp only [atomGram]
    rw [dotProduct_comm (atom slotTwo) (atom pivot)]
    ring
  have hCdict : planeShadow (atom pivot) (atom slotOne)
        ⬝ᵥ planeShadow (atom pivot) (atom slotTwo)
      = atomGram atom slotOne slotTwo
        - atomGram atom pivot slotOne * atomGram atom pivot slotTwo
          / atomGram atom pivot pivot := by
    rw [planeShadow_dot_shadow _ _ _ haxisNe]
    simp only [atomGram]
    rw [dotProduct_comm (atom slotOne) (atom pivot),
      dotProduct_comm (atom slotTwo) (atom pivot)]
  have hminorOne : atomPairMinor atom scale pivot slotOne
      = atomShiftedDiag atom scale pivot
        * ((planeShadow (atom pivot) (atom slotOne)
            ⬝ᵥ planeShadow (atom pivot) (atom slotOne))
          - scale slotOne
          - (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slotOne ^ 2) := by
    rw [hMone]
    simp only [atomPairMinor, atomShiftedDiag]
    field_simp [hdiagNe, hRne']
    ring
  have hminorTwo : atomPairMinor atom scale pivot slotTwo
      = atomShiftedDiag atom scale pivot
        * ((planeShadow (atom pivot) (atom slotTwo)
            ⬝ᵥ planeShadow (atom pivot) (atom slotTwo))
          - scale slotTwo
          - (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slotTwo ^ 2) := by
    rw [hMtwo]
    simp only [atomPairMinor, atomShiftedDiag]
    field_simp [hdiagNe, hRne']
    ring
  have hcrossEq : atomPivotCross atom scale pivot slotOne slotTwo
      = atomShiftedDiag atom scale pivot
        * ((planeShadow (atom pivot) (atom slotOne)
            ⬝ᵥ planeShadow (atom pivot) (atom slotTwo))
          - (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
            * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) := by
    rw [hCdict]
    simp only [atomPivotCross, atomShiftedDiag]
    field_simp [hdiagNe, hRne']
    ring
  have hWOne : 0 ≤ (scale pivot / (atomGram atom pivot pivot
      * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2 :=
    mul_nonneg hdeflNonneg (sq_nonneg _)
  have hWTwo : 0 ≤ (scale pivot / (atomGram atom pivot pivot
      * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2 :=
    mul_nonneg hdeflNonneg (sq_nonneg _)
  have htransfer := transfer_pair_lt
    (defl := scale pivot / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
    (gOne := atomGram atom pivot slotOne) (gTwo := atomGram atom pivot slotTwo)
    hdeflNonneg hgapRaw huTwo hdetRaw
  refine ⟨slotOne, slotTwo, fun heq => hOneNe heq.symm, fun heq => hTwoNe heq.symm,
    hneOneTwo, ?_, ?_, ?_⟩
  · rw [hminorOne]
    refine mul_pos hpivot ?_
    nlinarith [hgapRaw, hWOne]
  · rw [hminorTwo]
    refine mul_pos hpivot ?_
    nlinarith [huTwo, hWTwo]
  · rw [hcrossEq, hminorOne, hminorTwo]
    have hRsq : 0 < atomShiftedDiag atom scale pivot ^ 2 := by positivity
    nlinarith [htransfer, hRsq]

/-! ## Layer 3 — the pivot pair, the Sylvester chain and the carrier -/

/-- The pivot pair of the deflated residue, from one budget pivot. -/
theorem exists_pivotPair_of_pivot_budget
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hbudget : ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
        + 2 * scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo := by
  obtain ⟨slotOne, slotTwo, honeNe, htwoNe, hpairNe, hminorOne, _, hcross⟩ :=
    exists_deflated_pair_of_pivot_budget hframe hscale hpivot hbudget
  exact ⟨slotOne, slotTwo, honeNe, htwoNe, hpairNe, hpivot, hminorOne, hcross⟩

/-- The whole Sylvester chain from one budget pivot. -/
theorem exists_sylvester_of_pivot_budget
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hbudget : ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
        + 2 * scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ 0 < atomTripleDet atom scale pivot slotOne slotTwo := by
  obtain ⟨slotOne, slotTwo, honeNe, htwoNe, hpairNe, hR, hminor, hcross⟩ :=
    exists_pivotPair_of_pivot_budget hframe hscale hpivot hbudget
  exact ⟨slotOne, slotTwo, honeNe, htwoNe, hpairNe, hR, hminor,
    atomTripleDet_pos_of_deflated_pair hR hcross⟩

/-- The dominating carrier from one budget pivot. -/
theorem exists_dominating_carrier_of_pivot_budget
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hbudget : ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
        + 2 * scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
          (∑ slot, scale slot * probe slot ^ 2)
            < atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  obtain ⟨slotOne, slotTwo, honeNe, htwoNe, hpairNe, hR, hminor, hdet⟩ :=
    exists_sylvester_of_pivot_budget hframe hscale hpivot hbudget
  exact ⟨{pivot, slotOne, slotTwo}, card_triple_slots honeNe htwoNe hpairNe,
    fun probe hvanish hne =>
      dominates_of_triple_minors honeNe htwoNe hpairNe hR hminor hdet hvanish hne⟩

/-! ## Layer 4 — the heavy stratum -/

/-- **A HEAVY SLOT CARRIES THE BUDGET.**  When the scale mass is below
one and one slot has `2 + scale <= 3 * diagonal`, that slot is a budget
pivot. -/
theorem pivot_budget_of_heavy_slot
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ} {pivot : Fin 6}
    (hscalePivot : 0 ≤ scale pivot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hheavy : 2 + scale pivot ≤ 3 * atomGram atom pivot pivot) :
    ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
        + 2 * scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot := by
  have hcap : 2 * (1 - atomGram atom pivot pivot) ≤ atomShiftedDiag atom scale pivot := by
    simp only [atomShiftedDiag]
    linarith
  have hterm := mul_le_mul_of_nonneg_left hcap hscalePivot
  nlinarith [mul_lt_mul_of_pos_right hsmall hpivot, hterm,
    mul_nonneg hscalePivot hpivot.le]

/-- **THE HEAVY STRATUM CLOSES.**  A heavy slot of positive shifted
diagonal supplies the dominating carrier. -/
theorem exists_dominating_carrier_of_heavy_slot
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hheavy : 2 + scale pivot ≤ 3 * atomGram atom pivot pivot) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
          (∑ slot, scale slot * probe slot ^ 2)
            < atomBlend atom probe ⬝ᵥ atomBlend atom probe :=
  exists_dominating_carrier_of_pivot_budget hframe hscale hpivot
    (pivot_budget_of_heavy_slot (hscale pivot) hsmall hpivot hheavy)

/-- A blocked slot is never heavy: below scale mass one, the blocked
inequality at a slot of positive shifted diagonal forces
`3 * diagonal < 2 + scale`. -/
theorem blocked_slot_light
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ} {pivot : Fin 6}
    (hscalePivot : 0 ≤ scale pivot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hblocked : atomShiftedDiag atom scale pivot
      ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
        + 2 * scale pivot * (1 - atomGram atom pivot pivot)) :
    3 * atomGram atom pivot pivot < 2 + scale pivot := by
  by_contra hnot
  exact absurd hblocked (not_le.mpr
    (pivot_budget_of_heavy_slot hscalePivot hsmall hpivot (not_lt.mp hnot)))

/-! ## Layer 5 — the blocked window -/

/-- **THE BLOCKED CUBIC.**  When every slot of positive shifted diagonal
is blocked, the scale mass obeys one cubic inequality.  The engine is
the shifted trace law, one Cauchy-Schwarz over the live slots and the
per-slot blocked inequality read twice. -/
theorem blocked_scale_cubic
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hblocked : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) :
    (1 - ∑ slot, scale slot) * (3 - ∑ slot, scale slot) * (7 - ∑ slot, scale slot)
      ≤ 8 * ∑ slot, scale slot := by
  classical
  have hmassNonneg : 0 ≤ ∑ slot, scale slot :=
    Finset.sum_nonneg fun slot _ => hscale slot
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
      atomShiftedDiag atom scale slot * (1 - ∑ other, scale other)
        + 3 * (scale slot * atomShiftedDiag atom scale slot)
      ≤ 2 * scale slot := by
    intro slot hslot
    have hb := hblocked slot (hlive slot hslot)
    have hgram : atomGram atom slot slot = atomShiftedDiag atom scale slot + scale slot := by
      simp only [atomShiftedDiag]
      ring
    rw [hgram] at hb
    nlinarith [hb, sq_nonneg (scale slot)]
  have hB : ∀ slot ∈ Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot),
      (1 - ∑ other, scale other) * atomShiftedDiag atom scale slot ^ 2
        ≤ 2 * (scale slot * atomShiftedDiag atom scale slot) := by
    intro slot hslot
    have ha := hA slot hslot
    have hR := hlive slot hslot
    have hsR : 0 ≤ scale slot * atomShiftedDiag atom scale slot :=
      mul_nonneg (hscale slot) hR.le
    have hlin : (1 - ∑ other, scale other) * atomShiftedDiag atom scale slot
        ≤ 2 * scale slot := by nlinarith [ha, hsR]
    nlinarith [mul_le_mul_of_nonneg_right hlin hR.le]
  have hAsum := Finset.sum_le_sum hA
  have hBsum := Finset.sum_le_sum hB
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
    at hAsum
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hBsum
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
  have hdelta : 0 ≤ 1 - ∑ slot, scale slot := by linarith
  have hthree : (0:ℝ) ≤ 3 - ∑ slot, scale slot := by linarith
  have hTfloorSq : (3 - ∑ slot, scale slot) ^ 2
      ≤ (∑ slot ∈ Finset.univ.filter
          (fun slot => 0 < atomShiftedDiag atom scale slot),
            atomShiftedDiag atom scale slot) ^ 2 := by
    nlinarith [hRfloor, hthree]
  have hstepOne : (1 - ∑ slot, scale slot) * (3 - ∑ slot, scale slot) ^ 2
      ≤ 6 * (1 - ∑ slot, scale slot)
        * ∑ slot ∈ Finset.univ.filter
            (fun slot => 0 < atomShiftedDiag atom scale slot),
              atomShiftedDiag atom scale slot ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hTfloorSq hdelta,
      mul_le_mul_of_nonneg_left hcs hdelta]
  have hTlin : (1 - ∑ slot, scale slot) * (3 - ∑ slot, scale slot)
      ≤ (1 - ∑ slot, scale slot)
        * ∑ slot ∈ Finset.univ.filter
            (fun slot => 0 < atomShiftedDiag atom scale slot),
              atomShiftedDiag atom scale slot :=
    mul_le_mul_of_nonneg_left hRfloor hdelta
  nlinarith [hstepOne, hBsum, hAsum, hTlin, hscaleCap, hdelta, hthree, hmassNonneg]

/-- **THE BLOCKED WINDOW.**  The blocked stratum forces the scale mass
above `13/20`.  The cubic factors at that point with a positive
quadratic remainder. -/
theorem blocked_scale_lt
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hblocked : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) :
    13 / 20 < ∑ slot, scale slot := by
  have hcubic := blocked_scale_cubic hframe hscale hsmall hblocked
  by_contra hnot
  have hle : (∑ slot, scale slot) ≤ 13 / 20 := not_lt.mp hnot
  have hfac : (1 - ∑ slot, scale slot) * (3 - ∑ slot, scale slot)
      * (7 - ∑ slot, scale slot) - 8 * (∑ slot, scale slot) - 183 / 8000
      = (13 / 20 - ∑ slot, scale slot)
        * ((∑ slot, scale slot) ^ 2 - (207 / 20) * (∑ slot, scale slot)
          + 12909 / 400) := by
    ring
  have hquad : 0 ≤ (∑ slot, scale slot) ^ 2 - (207 / 20) * (∑ slot, scale slot)
      + 12909 / 400 := by
    nlinarith [sq_nonneg ((∑ slot, scale slot) - 207 / 40)]
  have hprod : 0 ≤ (13 / 20 - ∑ slot, scale slot)
      * ((∑ slot, scale slot) ^ 2 - (207 / 20) * (∑ slot, scale slot)
        + 12909 / 400) :=
    mul_nonneg (by linarith) hquad
  linarith [hcubic, hfac, hprod]

/-- **BELOW `13/20` A BUDGET PIVOT EXISTS.** -/
theorem exists_pivot_budget_of_scale_lt
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 13 / 20) :
    ∃ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot
      ∧ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)
        < atomShiftedDiag atom scale pivot := by
  by_contra hno
  have hblocked : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot) := by
    intro pivot hpos
    by_contra hlt
    exact hno ⟨pivot, hpos, not_le.mp hlt⟩
  have hwindow := blocked_scale_lt hframe hscale
    (lt_trans hsmall (by norm_num)) hblocked
  linarith

/-! ## Layer 6 — the threshold -/

/-- **THE THRESHOLD.**  Six atoms of a rank-three tight frame with
nonnegative scales of total below `13/20` carry a dominating triple.
This supersedes the quarter threshold, and it needs no positivity of the
scales. -/
theorem exists_dominating_triple_of_scale_lt_thirteen_twentieths
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 13 / 20) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
          (∑ slot, scale slot * probe slot ^ 2)
            < atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  obtain ⟨pivot, hpos, hbudget⟩ :=
    exists_pivot_budget_of_scale_lt hframe hscale hsmall
  exact exists_dominating_carrier_of_pivot_budget hframe hscale hpos hbudget

/-! ## Layer 7 — the blocked residue and the rung -/

/-- **THE BLOCKED RESIDUE.**  The atom triple ceiling on the blocked
stratum: every slot of positive shifted diagonal fails the budget.  The
blocked window forces the scale mass above `13/20` there, and the heavy
stratum is excluded slot by slot, thus this residue is strictly inside
the polynomial residue. -/
def AtomBlockedPivotClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) →
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
          (∑ slot, scale slot * probe slot ^ 2)
            < atomBlend atom probe ⬝ᵥ atomBlend atom probe

/-- **THE BLOCKED RESIDUE CLOSES THE ATOM TRIPLE CEILING.**  At every
datum a budget pivot either exists, and the engine supplies the carrier,
or every pivot is blocked, and the residue fires. -/
theorem atomTripleCeilingClosed_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : AtomTripleCeilingClosed := by
  intro atom scale hpos hsmall hframe
  by_cases hex : ∃ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot
      ∧ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)
        < atomShiftedDiag atom scale pivot
  · obtain ⟨pivot, hp, hb⟩ := hex
    exact exists_dominating_carrier_of_pivot_budget hframe
      (fun slot => (hpos slot).le) hp hb
  · refine hresidue atom scale hpos hsmall hframe fun pivot hpivot => ?_
    by_contra hlt
    exact hex ⟨pivot, hpivot, not_le.mp hlt⟩

/-- **THE `(6,3)` CELL FROM THE BLOCKED RESIDUE.** -/
theorem gtzWeighted_six_three_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPivot hresidue)

/-- **THE RANK-THREE PAYOFF FROM THE BLOCKED RESIDUE.** -/
theorem gtzWeightedAll_three_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPivot hresidue)

/-- The crux type is empty under the blocked residue. -/
theorem isEmpty_sixThreeCrux_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : IsEmpty SixThreeCrux :=
  isEmpty_sixThreeCrux_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPivot hresidue)

/-- The rank-five dense branch from the blocked residue. -/
theorem rankFiveDenseClosed_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : RankFiveDenseClosed :=
  rankFiveDenseClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPivot hresidue)

/-- The rank-six dense branch from the blocked residue. -/
theorem rankSixDenseClosed_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : RankSixDenseClosed :=
  rankSixDenseClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPivot hresidue)

/-- Profile B at rank five from the blocked residue. -/
theorem rankFiveDenseHeavyFourClosed_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : RankFiveDenseHeavyFourClosed :=
  rankFiveDenseHeavyFourClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPivot hresidue)

/-- Profile C at rank five from the blocked residue. -/
theorem rankFiveDenseThreeTriplesClosed_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : RankFiveDenseThreeTriplesClosed :=
  rankFiveDenseThreeTriplesClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPivot hresidue)

/-- Profile A at rank six from the blocked residue. -/
theorem rankSixDenseHeavyFiveClosed_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : RankSixDenseHeavyFiveClosed :=
  rankSixDenseHeavyFiveClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPivot hresidue)

/-- Profile B at rank six from the blocked residue. -/
theorem rankSixDenseHeavyFourClosed_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : RankSixDenseHeavyFourClosed :=
  rankSixDenseHeavyFourClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPivot hresidue)

/-- Profile C at rank six from the blocked residue. -/
theorem rankSixDenseAllTriplesClosed_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : RankSixDenseAllTriplesClosed :=
  rankSixDenseAllTriplesClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPivot hresidue)

/-- The rank-six support-two closure from the blocked residue. -/
theorem rankSixSupportTwoClosed_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : RankSixSupportTwoClosed :=
  rankSixSupportTwoClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPivot hresidue)

/-- The rank-five support-two closure from the blocked residue. -/
theorem rankFiveSupportTwoClosed_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : RankFiveSupportTwoClosed :=
  rankFiveSupportTwoClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPivot hresidue)

/-- The rank-four support-two closure from the blocked residue. -/
theorem rankFourSupportTwoClosed_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : RankFourSupportTwoClosed :=
  rankFourSupportTwoClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPivot hresidue)

end Gtz
