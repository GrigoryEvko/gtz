import Gtz.Wave.OuterParallelFold

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The outer trace-three interior — the boundary is empty at captured rank three

The refined profile kills carry an interiority hypothesis: the shifted
weights are positive off the pins and pairs.  At captured rank three
the hypothesis is a theorem.  A vanished shifted weight kills the
capture row of its atom, and the capture trace then forces the chart
to factor through the span projector of the basis columns.  The
factored chart vanishes on the whole atom column, against the positive
gap diagonal of the all-heavy crux.  This is the strata-dispatch
argument of the shared-private closure, ported to the outer frames.

Thus the rank-six outer kills drop the interiority hypothesis, and the
rank-five kills keep it only on the captured-rank-two branch.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.SixThreeCrux.shifted_weight_pos_of_capture_trace_three` — **THE
  GENERIC INTERIOR LAW.**
* `Gtz.RankSixFrame.shifted_weight_pos` — the rank-six interiority.
* `Gtz.RankFiveFrame.shifted_weight_pos_of_trace_three` — the
  rank-five trace-three interiority.
* `Gtz.RankSixOuterData.false_of_circuitClosed_profile` — **THE
  RANK-SIX PROFILE KILL** without interiority hypotheses.
* `Gtz.RankFiveOuterData.false_of_circuitClosed_profile` — the
  rank-five profile kill with interiority only at captured rank two.

## Vacuity

The statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no crux
exists, thus no frame exists.
-/

namespace Gtz

open Matrix

/-- **THE GENERIC INTERIOR LAW.**  At a stationary datum with a basis,
a left inverse, a span law, and a coefficient representation of
capture trace three, every shifted weight is positive.  A vanished
shifted weight kills its capture row, the trace forces the chart
through the span projector, and the vanished chart diagonal breaks the
gap floor. -/
theorem SixThreeCrux.shifted_weight_pos_of_capture_trace_three
    (crux : SixThreeCrux) {activeIndex : Type} {basisCount : ℕ}
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin 6 → ℝ)}
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    {leftInv : Matrix (Fin basisCount) (Fin 6) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (hspan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : (chartPointOfDesign crux.design).chart
        * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    (htrace : Matrix.trace coeff = 3) (atomIndex : Fin 6) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex := by
  rcases (capture_diagonal_nonneg_of_isChartStationaryData hdata
    atomIndex).lt_or_eq with hpos | heq
  · exact hpos
  exfalso
  classical
  -- the annihilated capture row at the boundary atom
  have hrow : ∀ columnIndex, (tightBasisColumns tightDir basisLabel
      * coeff) atomIndex columnIndex = 0 :=
    fun columnIndex => basis_capture_column_zero_of_diagonal_zero hdata
      hspan hrepresentation heq.symm columnIndex
  set B := tightBasisColumns tightDir basisLabel with hB
  set P := (chartPointOfDesign crux.design).chart with hP
  set N := Bᵀ * B with hN
  -- the projection laws through the definitional bridge
  have hrep : P * B = B * coeff := hrepresentation
  have hPsymm : Pᵀ = P := hdata.isSymmetric
  have hidem : P * P = P := projectionOfDesign_mul_self crux.design
  have hPtrace : Matrix.trace P = 3 := by
    have h : Matrix.trace (projectionOfDesign crux.design)
        = ((3 : ℕ) : ℝ) := trace_projectionOfDesign crux.design
    norm_num at h
    exact h
  -- the column Gram is kernel-free, thus invertible
  have hkerB : ∀ vec : Fin basisCount → ℝ, B *ᵥ vec = 0 → vec = 0 := by
    intro vec hzero
    have hrecover : leftInv *ᵥ (B *ᵥ vec) = vec := by
      rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
    rw [← hrecover, hzero, Matrix.mulVec_zero]
  have hkerN : ∀ vec : Fin basisCount → ℝ, N *ᵥ vec = 0 → vec = 0 := by
    intro vec hzero
    have hquadForm : vec ⬝ᵥ (N *ᵥ vec)
        = (B *ᵥ vec) ⬝ᵥ (B *ᵥ vec) := by
      rw [hN, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose]
    rw [hzero, dotProduct_zero] at hquadForm
    have hBv : B *ᵥ vec = 0 := by
      funext rowIndex
      have hquad := hquadForm.symm
      rw [dotProduct] at hquad
      have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        mul_self_nonneg ((B *ᵥ vec) i)).mp hquad rowIndex
        (Finset.mem_univ rowIndex)
      simpa using mul_self_eq_zero.mp hall
    exact hkerB vec hBv
  have hdetN : IsUnit N.det := by
    rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨vec, hvne, hvzero⟩ :=
      (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
    exact hvne (hkerN vec hvzero)
  have hNiN : N⁻¹ * N = 1 := Matrix.nonsing_inv_mul N hdetN
  -- the span projector of the basis columns
  set spanProj := B * N⁻¹ * Bᵀ with hspanDef
  have hNsymm : Nᵀ = N := by
    rw [hN, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hNinvSymm : (N⁻¹)ᵀ = N⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hNsymm]
  have hspanSymm : spanProjᵀ = spanProj := by
    rw [hspanDef, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hNinvSymm, ← Matrix.mul_assoc]
  have hspanIdem : spanProj * spanProj = spanProj := by
    rw [hspanDef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᵀ B, ← hN, ← Matrix.mul_assoc N⁻¹ N, hNiN,
      Matrix.one_mul]
  -- the capture trace equals the coefficient trace
  have hPPi : P * spanProj = B * (coeff * (N⁻¹ * Bᵀ)) := by
    rw [hspanDef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P B, hrep, Matrix.mul_assoc]
  have htracePPi : Matrix.trace (P * spanProj)
      = Matrix.trace coeff := by
    rw [hPPi, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
    rw [← hN, hNiN, Matrix.mul_one]
  -- the projection factors through the span projector
  have hexpand : (P - spanProj * P) * (P - P * spanProj)
      = P - P * spanProj - (spanProj * P - spanProj * (P * spanProj)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    rw [hidem, ← Matrix.mul_assoc P P spanProj, hidem,
      Matrix.mul_assoc spanProj P P, hidem,
      Matrix.mul_assoc spanProj P (P * spanProj),
      ← Matrix.mul_assoc P P spanProj, hidem]
    abel
  have hfactor : P * spanProj = P := by
    have hzero : P - P * spanProj = 0 := by
      apply eq_zero_of_trace_transpose_mul_self
      have hT : (P - P * spanProj)ᵀ = P - spanProj * P := by
        rw [Matrix.transpose_sub, Matrix.transpose_mul, hspanSymm, hPsymm]
      rw [hT, hexpand, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub]
      have h1 : Matrix.trace (spanProj * P)
          = Matrix.trace (P * spanProj) := Matrix.trace_mul_comm spanProj P
      have h2 : Matrix.trace (spanProj * (P * spanProj))
          = Matrix.trace (P * spanProj) := by
        rw [Matrix.trace_mul_comm, Matrix.mul_assoc, hspanIdem]
      rw [h1, h2, htracePPi, htrace, hPtrace]
      norm_num
    exact (sub_eq_zero.mp hzero).symm
  have hfactorT : spanProj * P = P := by
    have h := congrArg Matrix.transpose hfactor
    rwa [Matrix.transpose_mul, hspanSymm, hPsymm] at h
  -- the projected axis dies at the boundary atom
  have hBt : Bᵀ *ᵥ (P *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)) = 0 := by
    have hBtP : Bᵀ * P = (B * coeff)ᵀ := by
      rw [← hrep, Matrix.transpose_mul, hPsymm]
    rw [Matrix.mulVec_mulVec, hBtP]
    funext columnIndex
    have happly : ((B * coeff)ᵀ
        *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)) columnIndex
        = (B * coeff) atomIndex columnIndex := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply,
        Matrix.transpose_apply, mul_ite, mul_one, mul_zero]
    rw [happly, hrow columnIndex]
    rfl
  have hcol : P *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) = 0 := by
    have hfix : P *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)
        = spanProj *ᵥ (P *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)) := by
      rw [Matrix.mulVec_mulVec, hfactorT]
    rw [hfix, hspanDef, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hBt, Matrix.mulVec_zero, Matrix.mulVec_zero]
  -- the vanished diagonal against the all-heavy floor
  have hdiagzero : P atomIndex atomIndex = 0 := by
    have happly : (P *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)) atomIndex
        = P atomIndex atomIndex := by
      rw [Matrix.mulVec_single_one]
      simp [Matrix.col]
    rw [← happly, hcol]
    rfl
  have hgap := crux.chartGap_diagonal_pos atomIndex
  simp only [chartStationaryGap, Matrix.sub_apply,
    Matrix.diagonal_apply_eq] at hgap
  rw [← hP, hdiagzero] at hgap
  have hweight := hdata.weight_pos atomIndex
  linarith

/-- **THE RANK-SIX INTERIORITY.**  Every shifted weight of a rank-six
frame is positive: the coefficient trace is three. -/
theorem RankSixFrame.shifted_weight_pos {crux : SixThreeCrux}
    (frame : RankSixFrame crux) (atomIndex : Fin 6) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex :=
  crux.shifted_weight_pos_of_capture_trace_three frame.hdata frame.hleft
    frame.hspan frame.hrepresentation frame.htrace atomIndex

/-- **THE RANK-FIVE TRACE-THREE INTERIORITY.** -/
theorem RankFiveFrame.shifted_weight_pos_of_trace_three
    {crux : SixThreeCrux} (frame : RankFiveFrame crux)
    (htrace : Matrix.trace frame.coeff = 3) (atomIndex : Fin 6) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex :=
  crux.shifted_weight_pos_of_capture_trace_three frame.hdata frame.hleft
    frame.hspan frame.hrepresentation htrace atomIndex

/-- **THE RANK-SIX PROFILE KILL.**  With the circuit residue closed, a
rank-six outer datum dies at profile mass four, with no interiority
hypothesis: the trace-three interior law supplies it. -/
theorem RankSixOuterData.false_of_circuitClosed_profile
    (hcirc : RankSixOuterCircuitClosed)
    {crux : SixThreeCrux} (data : RankSixOuterData crux)
    (pinSet pairSet : Finset (Fin 6)) (hdisjoint : Disjoint pinSet pairSet)
    (hpinSet : ∀ atom ∈ pinSet, ∃ pinSlot,
      blockCarrier data.frame.activeSubset data.frame.basisLabel atom
        = {pinSlot})
    (hpairSet : ∀ atom ∈ pairSet, ∃ slotOne slotTwo, slotOne ≠ slotTwo ∧
      blockCarrier data.frame.activeSubset data.frame.basisLabel atom
        = {slotOne, slotTwo})
    (hprofile : 4 ≤ 2 * pinSet.card + pairSet.card) :
    False :=
  data.false_of_circuitClosed_refined hcirc pinSet pairSet hdisjoint
    hpinSet hpairSet
    (fun atom _ _ => data.frame.shifted_weight_pos atom) hprofile

/-- **THE RANK-FIVE PROFILE KILL.**  With the circuit residue closed, a
rank-five outer datum dies at the refined profile, with interiority
only on the captured-rank-two branch. -/
theorem RankFiveOuterData.false_of_circuitClosed_profile
    (hcirc : RankFiveOuterCircuitClosed)
    {crux : SixThreeCrux} (data : RankFiveOuterData crux)
    (pinSet pairSet : Finset (Fin 6)) (hdisjoint : Disjoint pinSet pairSet)
    (hpinSet : ∀ atom ∈ pinSet, ∃ pinSlot,
      blockCarrier data.frame.activeSubset data.frame.basisLabel atom
        = {pinSlot})
    (hpairSet : ∀ atom ∈ pairSet, ∃ slotOne slotTwo, slotOne ≠ slotTwo ∧
      blockCarrier data.frame.activeSubset data.frame.basisLabel atom
        = {slotOne, slotTwo})
    (hintTwo : Matrix.trace data.frame.coeff = 2 →
      ∀ atom, atom ∉ pinSet → atom ∉ pairSet →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atom)
    (hprofileTwo : Matrix.trace data.frame.coeff = 2 → 1 ≤ pinSet.card)
    (hprofileThree : Matrix.trace data.frame.coeff = 3 →
      4 ≤ 2 * pinSet.card + pairSet.card) :
    False := by
  rcases data.frame.htrace with htrace2 | htrace3
  · exact data.false_of_circuitClosed_refined hcirc pinSet pairSet
      hdisjoint hpinSet hpairSet (hintTwo htrace2) hprofileTwo
      hprofileThree
  · exact data.false_of_circuitClosed_refined hcirc pinSet pairSet
      hdisjoint hpinSet hpairSet
      (fun atom _ _ =>
        data.frame.shifted_weight_pos_of_trace_three htrace3 atom)
      hprofileTwo hprofileThree

end Gtz
