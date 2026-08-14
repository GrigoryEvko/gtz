import Gtz.Wave.AtomCoherentTriangle

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The icosahedral witness: the real analogue of the two-trine, and its death

The complex two-trine is the one datum that refutes every field-agnostic
program of the lane.  It normalises to diagonal one half at every slot, it is
blocked for every scale mass at or above the trine onset
`(27 - 3 * sqrt 41) / 10`, and it carries no dominating triple.

There is a REAL configuration with exactly that signature.  The six
icosahedron diagonals, rescaled to a tight frame, have diagonal one half at
every slot and Gram entries of modulus `sqrt 5 / 10` at every pair — the
unique real equiangular tight frame of six lines in rank three.  At uniform
scales it is blocked exactly when the trine cut is nonpositive, thus it sits
on the same threshold as the complex trine, at the same normalisation, with
the same blocked window.

It nevertheless dies, and this module says by what.  Its slot triple
`{0, 2, 4}` is the one whose three overlaps carry the SAME sign.  Its cycle is
therefore `(sqrt 5 / 10) ^ 3 > 0`, its three triangle gaps are positive at
every scale below one quarter, and the coherent product cell of
`Gtz/Wave/AtomCoherentTriangle.lean` fires.  Over the complex field the trine
has no sign at all, thus the certificate has no analogue there.  This is the
real-only step of the lane, mechanised on the sharpest real datum available.

The margin is comfortable and it is uniform in the mass: the cell demands the
shifted diagonal to beat `sqrt 5 / 10 = 0.2236`, while at every admissible
mass the shifted diagonal is at least `1/3`.

## What this module is NOT

It is not a closure of the blocked residue.  An adversarial search over the
blocked stratum reaches data at which no coherent triangle dominates, thus
the coherent cells certify the icosahedral witness and other data but they do
not cover the stratum.  The guardrail below is exactly what it says: the real
equiangular tight frame does not refute the residue.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.icosaFrameAtom` and `Gtz.icosaFrameAtom_isTightFrame` — the rescaled
  icosahedron IS a tight frame of rank three.
* `Gtz.icosaFrameAtom_gram_diag`, `Gtz.icosaFrameAtom_gram_sq_of_ne` — **the
  ETF signature**: diagonal one half, squared overlap `1/20`.
* `Gtz.icosaFrameAtom_blockedSlotExcess`,
  `Gtz.icosaFrameAtom_blocked_iff_trineCut` — **THE WITNESS IS BLOCKED
  EXACTLY ON THE TRINE THRESHOLD**, at the same uniform normalisation.
* `Gtz.icosaFrameAtom_cycle_coherent`, `Gtz.icosaFrameAtom_triangleGap_pos` —
  the same-sign triple and its three positive gaps.
* `Gtz.icosaFrameAtom_deflates`,
  `Gtz.icosaFrameAtom_spares_blockedPairClosed` — **THE REAL TRINE ANALOGUE
  DIES BY THE COHERENT PRODUCT CELL**, at every admissible mass.

## Vacuity

Every statement is about one named configuration and is proved by exact
arithmetic in `Real.sqrt 5`, thus none of them is vacuous.  The guardrail
gives the hypotheses of the residue as satisfied facts, so it is a genuine
instance and not an empty implication.
-/

namespace Gtz

/-! ## Layer 0 — the tight frame rescaling of the icosahedron -/

/-- The rescaling that turns the icosahedron at leverage three into a tight
frame: one over the square root of six. -/
noncomputable def icosaFrameScale : ℝ := (Real.sqrt 6)⁻¹

theorem icosaFrameScale_pos : 0 < icosaFrameScale := by
  rw [icosaFrameScale]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))

theorem icosaFrameScale_sq : icosaFrameScale ^ 2 = 1 / 6 := by
  have hsix : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 6 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [icosaFrameScale, inv_pow, hsix]
  norm_num

/-- **THE ICOSAHEDRAL TIGHT FRAME.**  The six icosahedron diagonals rescaled
so that the frame operator is the identity.  Each atom then has squared
length one half, which is the trine normalisation. -/
noncomputable def icosaFrameAtom : Fin 6 → (Fin 3 → ℝ) :=
  fun slot => icosaFrameScale • icosaAtom slot

/-- The Gram of the rescaled family is the Gram of the icosahedron over six. -/
theorem icosaFrameAtom_gram (rowSlot colSlot : Fin 6) :
    atomGram icosaFrameAtom rowSlot colSlot
      = (icosaAtom rowSlot ⬝ᵥ icosaAtom colSlot) / 6 := by
  simp only [atomGram, icosaFrameAtom, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  linear_combination (icosaAtom rowSlot ⬝ᵥ icosaAtom colSlot) * icosaFrameScale_sq

/-- **THE DIAGONAL IS ONE HALF** — the trine normalisation, exactly. -/
theorem icosaFrameAtom_gram_diag (slot : Fin 6) :
    atomGram icosaFrameAtom slot slot = 1 / 2 := by
  rw [icosaFrameAtom_gram, icosaAtom_leverage]
  norm_num

/-- **EVERY DISTINCT OVERLAP HAS SQUARE `1/20`** — the equiangular tight
frame signature at the trine normalisation. -/
theorem icosaFrameAtom_gram_sq_of_ne {rowSlot colSlot : Fin 6} (hne : rowSlot ≠ colSlot) :
    atomGram icosaFrameAtom rowSlot colSlot ^ 2 = 1 / 20 := by
  rw [icosaFrameAtom_gram, div_pow, icosaAtom_dot_sq_of_ne hne]
  norm_num

/-- The unnormalised frame law of the icosahedron: the frame operator of the
six diagonals is six times the identity. -/
theorem icosaAtom_frame_six (probe direction : Fin 3 → ℝ) :
    (∑ slot, (icosaAtom slot ⬝ᵥ probe) * (icosaAtom slot ⬝ᵥ direction))
      = 6 * (probe ⬝ᵥ direction) := by
  have hshort := icosaShort_sq
  have hlong := icosaLong_sq
  simp only [Fin.sum_univ_six, icosaAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val]
  linear_combination (2 * (probe 0 * direction 0 + probe 1 * direction 1
      + probe 2 * direction 2)) * hshort
    + (2 * (probe 0 * direction 0 + probe 1 * direction 1
      + probe 2 * direction 2)) * hlong

/-- **THE RESCALED ICOSAHEDRON IS A TIGHT FRAME.**  This is the hypothesis
that every residue of the atom lane demands of its datum. -/
theorem icosaFrameAtom_isTightFrame (probe direction : Fin 3 → ℝ) :
    (∑ slot, (icosaFrameAtom slot ⬝ᵥ probe) * (icosaFrameAtom slot ⬝ᵥ direction))
      = probe ⬝ᵥ direction := by
  have hsix := icosaAtom_frame_six probe direction
  have hsq := icosaFrameScale_sq
  have hexpand : (∑ slot, (icosaFrameAtom slot ⬝ᵥ probe)
        * (icosaFrameAtom slot ⬝ᵥ direction))
      = icosaFrameScale ^ 2
        * ∑ slot, (icosaAtom slot ⬝ᵥ probe) * (icosaAtom slot ⬝ᵥ direction) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun slot _ => ?_
    simp only [icosaFrameAtom, smul_dotProduct, smul_eq_mul]
    ring
  rw [hexpand, hsix, hsq]
  ring

/-! ## Layer 1 — the blocked window of the witness -/

/-- The uniform scale family of a given mass. -/
noncomputable def icosaFrameScaleAt (mass : ℝ) : Fin 6 → ℝ := fun _ => mass / 6

theorem icosaFrameScaleAt_sum (mass : ℝ) :
    (∑ slot, icosaFrameScaleAt mass slot) = mass := by
  simp only [icosaFrameScaleAt, Fin.sum_univ_six]
  ring

theorem icosaFrameScaleAt_pos {mass : ℝ} (hmass : 0 < mass) (slot : Fin 6) :
    0 < icosaFrameScaleAt mass slot := by
  simp only [icosaFrameScaleAt]
  linarith

/-- **THE BLOCKED SLOT EXCESS OF THE WITNESS IS THE TRINE CUT OVER
THIRTY-SIX.**  The witness reads the same polynomial as the complex trine,
which is why the two share their threshold. -/
theorem icosaFrameAtom_blockedSlotExcess (mass : ℝ) (slot : Fin 6) :
    blockedSlotExcess icosaFrameAtom (icosaFrameScaleAt mass) slot
      = trineCut mass / 36 := by
  simp only [blockedSlotExcess, icosaFrameAtom_gram_diag]
  rw [icosaFrameScaleAt_sum]
  simp only [icosaFrameScaleAt, trineCut]
  ring

/-- The shifted diagonal of the witness at mass `mass`. -/
theorem icosaFrameAtom_shiftedDiag (mass : ℝ) (slot : Fin 6) :
    atomShiftedDiag icosaFrameAtom (icosaFrameScaleAt mass) slot
      = 1 / 2 - mass / 6 := by
  simp only [atomShiftedDiag, icosaFrameAtom_gram_diag, icosaFrameScaleAt]

/-- **THE WITNESS IS BLOCKED EXACTLY ON THE TRINE THRESHOLD.**  Below the
trine onset it is not blocked at any slot, and at or above it the double
inflation budget fails at every slot.  The complex two-trine obeys the same
law, thus blockedness cannot separate the two fields. -/
theorem icosaFrameAtom_blocked_iff_trineCut {mass : ℝ} (hmass : mass < 3) :
    (∀ pivot : Fin 6,
        0 < atomShiftedDiag icosaFrameAtom (icosaFrameScaleAt mass) pivot →
        atomShiftedDiag icosaFrameAtom (icosaFrameScaleAt mass) pivot
          ≤ ((∑ slot, icosaFrameScaleAt mass slot)
              - icosaFrameScaleAt mass pivot)
            * atomShiftedDiag icosaFrameAtom (icosaFrameScaleAt mass) pivot
            + 2 * icosaFrameScaleAt mass pivot
              * (1 - atomGram icosaFrameAtom pivot pivot))
      ↔ trineCut mass ≤ 0 := by
  have hlive : ∀ pivot : Fin 6,
      0 < atomShiftedDiag icosaFrameAtom (icosaFrameScaleAt mass) pivot := by
    intro pivot
    rw [icosaFrameAtom_shiftedDiag]
    linarith
  constructor
  · intro hblocked
    have hgap := blockedSlotExcess_eq_budget_gap icosaFrameAtom
      (icosaFrameScaleAt mass) 0
    have hexcess := icosaFrameAtom_blockedSlotExcess mass 0
    have hbound := hblocked 0 (hlive 0)
    rw [hexcess] at hgap
    linarith [hgap, hbound]
  · intro hcut pivot _
    have hgap := blockedSlotExcess_eq_budget_gap icosaFrameAtom
      (icosaFrameScaleAt mass) pivot
    have hexcess := icosaFrameAtom_blockedSlotExcess mass pivot
    rw [hexcess] at hgap
    linarith [hgap, hcut]

/-! ## Layer 2 — the same-sign triple and the coherent product cell -/

/-- The six ordered overlaps of the slot triple `{0, 2, 4}` all equal the
common overlap modulus over six, hence they carry the SAME sign.  This is the
fact that has no complex analogue: over the complex field the trine's entry
products are never real. -/
theorem icosaFrameAtom_gram_sameSign :
    atomGram icosaFrameAtom 0 2 = icosaRadius / 6
      ∧ atomGram icosaFrameAtom 0 4 = icosaRadius / 6
      ∧ atomGram icosaFrameAtom 2 4 = icosaRadius / 6
      ∧ atomGram icosaFrameAtom 2 0 = icosaRadius / 6
      ∧ atomGram icosaFrameAtom 4 0 = icosaRadius / 6
      ∧ atomGram icosaFrameAtom 4 2 = icosaRadius / 6 := by
  have hsl := icosaShort_mul_icosaLong
  have hbase : ∀ rowSlot colSlot : Fin 6,
      icosaAtom rowSlot ⬝ᵥ icosaAtom colSlot = icosaShort * icosaLong →
      atomGram icosaFrameAtom rowSlot colSlot = icosaRadius / 6 := by
    intro rowSlot colSlot hdot
    rw [icosaFrameAtom_gram, hdot, hsl]
  have hzeroTwo : atomGram icosaFrameAtom 0 2 = icosaRadius / 6 := by
    refine hbase 0 2 ?_
    simp only [icosaAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    ring
  have hzeroFour : atomGram icosaFrameAtom 0 4 = icosaRadius / 6 := by
    refine hbase 0 4 ?_
    simp only [icosaAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.cons_val_four]
    ring
  have htwoFour : atomGram icosaFrameAtom 2 4 = icosaRadius / 6 := by
    refine hbase 2 4 ?_
    simp only [icosaAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.cons_val_four]
    ring
  exact ⟨hzeroTwo, hzeroFour, htwoFour,
    (atomGram_comm icosaFrameAtom 2 0).trans hzeroTwo,
    (atomGram_comm icosaFrameAtom 4 0).trans hzeroFour,
    (atomGram_comm icosaFrameAtom 4 2).trans htwoFour⟩

/-- The common overlap of the witness is `sqrt 5 / 10`, strictly between zero
and one quarter, and its square is one twentieth. -/
theorem icosaFrameAtom_overlap_bounds :
    0 < icosaRadius / 6 ∧ icosaRadius / 6 < 1 / 4
      ∧ (icosaRadius / 6) ^ 2 = 1 / 20 := by
  refine ⟨by linarith [icosaRadius_pos], by linarith [icosaRadius_upper], ?_⟩
  rw [div_pow, icosaRadius_sq]
  norm_num

/-- The shifted diagonal of the witness at an arbitrary scale family. -/
theorem icosaFrameAtom_shiftedDiag_eq (scale : Fin 6 → ℝ) (slot : Fin 6) :
    atomShiftedDiag icosaFrameAtom scale slot = 1 / 2 - scale slot := by
  simp only [atomShiftedDiag, icosaFrameAtom_gram_diag]

/-- **THE SAME-SIGN TRIPLE IS COHERENT.**  Its cycle is the cube of a
positive number. -/
theorem icosaFrameAtom_cycle_coherent :
    0 < atomTriangleCycle icosaFrameAtom 0 2 4 := by
  obtain ⟨hzeroTwo, hzeroFour, htwoFour, _, _, _⟩ := icosaFrameAtom_gram_sameSign
  have hpos : 0 < icosaRadius / 6 := by linarith [icosaRadius_pos]
  simp only [atomTriangleCycle, hzeroTwo, hzeroFour, htwoFour]
  exact mul_pos (mul_pos hpos hpos) hpos

/-- **THE THREE TRIANGLE GAPS OF THE WITNESS ARE POSITIVE.**  A gap is the
shifted diagonal against one twentieth minus the cube of the overlap, and the
shifted diagonal beats the overlap at every scale below one quarter. -/
theorem icosaFrameAtom_triangleGap_pos {scale : Fin 6 → ℝ}
    (hsmall : ∀ slot : Fin 6, scale slot < 1 / 4) :
    0 < atomTriangleGap icosaFrameAtom scale 0 2 4
      ∧ 0 < atomTriangleGap icosaFrameAtom scale 2 0 4
      ∧ 0 < atomTriangleGap icosaFrameAtom scale 4 0 2 := by
  obtain ⟨hzeroTwo, hzeroFour, htwoFour, htwoZero, hfourZero, hfourTwo⟩ :=
    icosaFrameAtom_gram_sameSign
  obtain ⟨hoverlapPos, hoverlapSmall, hoverlapSq⟩ := icosaFrameAtom_overlap_bounds
  have hcore : ∀ apex : Fin 6,
      0 < (1 / 2 - scale apex) * (icosaRadius / 6) ^ 2
        - (icosaRadius / 6) * (icosaRadius / 6) * (icosaRadius / 6) := by
    intro apex
    have hapex := hsmall apex
    rw [hoverlapSq]
    nlinarith [hapex, hoverlapPos, hoverlapSmall]
  refine ⟨?_, ?_, ?_⟩
  · simp only [atomTriangleGap, atomTriangleCycle, hzeroTwo, hzeroFour, htwoFour,
      icosaFrameAtom_shiftedDiag_eq]
    exact hcore 0
  · simp only [atomTriangleGap, atomTriangleCycle, hzeroFour, htwoZero, htwoFour,
      icosaFrameAtom_shiftedDiag_eq]
    exact hcore 2
  · simp only [atomTriangleGap, atomTriangleCycle, hzeroTwo, hfourZero, hfourTwo,
      icosaFrameAtom_shiftedDiag_eq]
    exact hcore 4

/-- **THE WITNESS DEFLATES.**  At every scale family below one quarter the
same-sign triple of the icosahedral tight frame supplies the deflated pair
that the blocked residue asks for.  The certificate is the coherent product
cell, and it reads the SIGN of the triangle. -/
theorem icosaFrameAtom_deflates {scale : Fin 6 → ℝ}
    (hsmall : ∀ slot : Fin 6, scale slot < 1 / 4) :
    ∃ pivot firstSlot secondSlot : Fin 6,
      pivot ≠ firstSlot ∧ pivot ≠ secondSlot ∧ firstSlot ≠ secondSlot
        ∧ 0 < atomShiftedDiag icosaFrameAtom scale pivot
        ∧ 0 < atomPairMinor icosaFrameAtom scale pivot firstSlot
        ∧ atomPivotCross icosaFrameAtom scale pivot firstSlot secondSlot ^ 2
            < atomPairMinor icosaFrameAtom scale pivot firstSlot
              * atomPairMinor icosaFrameAtom scale pivot secondSlot := by
  obtain ⟨hone, htwo, hthree⟩ := icosaFrameAtom_triangleGap_pos hsmall
  exact exists_deflated_pair_of_coherentGaps (by decide) (by decide) (by decide)
    icosaFrameAtom_cycle_coherent hone htwo hthree

/-! ## Layer 3 — the guardrail -/

/-- **THE REAL EQUIANGULAR TIGHT FRAME DOES NOT REFUTE THE BLOCKED RESIDUE.**
At every admissible mass the icosahedral witness satisfies every hypothesis of
`Gtz.AtomBlockedPairClosed` — positive scales, mass below one, the tight frame
law, and blockedness whenever the trine cut is nonpositive — and it satisfies
the conclusion as well.  The complex two-trine satisfies the same hypotheses
and refutes every field-agnostic certificate, thus the separation is carried
entirely by the sign of the triangle. -/
theorem icosaFrameAtom_spares_blockedPairClosed {mass : ℝ} (hpos : 0 < mass)
    (hless : mass < 1) :
    (∀ slot : Fin 6, 0 < icosaFrameScaleAt mass slot)
      ∧ (∑ slot, icosaFrameScaleAt mass slot) < 1
      ∧ (∀ probe direction : Fin 3 → ℝ,
          (∑ slot, (icosaFrameAtom slot ⬝ᵥ probe)
            * (icosaFrameAtom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
      ∧ (trineCut mass ≤ 0 → ∀ pivot : Fin 6,
          0 < atomShiftedDiag icosaFrameAtom (icosaFrameScaleAt mass) pivot →
          atomShiftedDiag icosaFrameAtom (icosaFrameScaleAt mass) pivot
            ≤ ((∑ slot, icosaFrameScaleAt mass slot)
                - icosaFrameScaleAt mass pivot)
              * atomShiftedDiag icosaFrameAtom (icosaFrameScaleAt mass) pivot
              + 2 * icosaFrameScaleAt mass pivot
                * (1 - atomGram icosaFrameAtom pivot pivot))
      ∧ (∃ pivot firstSlot secondSlot : Fin 6,
          pivot ≠ firstSlot ∧ pivot ≠ secondSlot ∧ firstSlot ≠ secondSlot
            ∧ 0 < atomShiftedDiag icosaFrameAtom (icosaFrameScaleAt mass) pivot
            ∧ 0 < atomPairMinor icosaFrameAtom (icosaFrameScaleAt mass) pivot firstSlot
            ∧ atomPivotCross icosaFrameAtom (icosaFrameScaleAt mass) pivot
                  firstSlot secondSlot ^ 2
                < atomPairMinor icosaFrameAtom (icosaFrameScaleAt mass) pivot firstSlot
                  * atomPairMinor icosaFrameAtom (icosaFrameScaleAt mass)
                      pivot secondSlot) := by
  refine ⟨icosaFrameScaleAt_pos hpos, ?_, icosaFrameAtom_isTightFrame, ?_, ?_⟩
  · rw [icosaFrameScaleAt_sum]; exact hless
  · exact fun hcut => (icosaFrameAtom_blocked_iff_trineCut (by linarith)).mpr hcut
  · refine icosaFrameAtom_deflates (fun slot => ?_)
    simp only [icosaFrameScaleAt]
    linarith

/-- **THE WITNESS SITS ON THE TRINE THRESHOLD.**  At the rational split point
`779/1000` the trine cut is still positive, so nothing is blocked there, and
at `39/50` it is negative, so the witness is blocked.  The two readings match
the complex trine exactly. -/
theorem icosaFrameAtom_threshold_readings :
    0 < trineCut (779 / 1000) ∧ trineCut (39 / 50) < 0 := by
  constructor
  · rw [trineCut]; norm_num
  · rw [trineCut_band_boundary]; norm_num

end Gtz
