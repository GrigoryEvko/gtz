import Gtz.Wave.SharedPrivateStrataDispatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The kernel-residue decomposition — the projection splits along the basis span

The trace-split kill showed that a trace-three projection is supported
on the basis span.  This module gives the full decomposition at every
trace: the projection is the frame part `B * M * N⁻¹ * Bᵀ` plus a
kernel residue.  The residue is a symmetric idempotent, it annihilates
the basis columns, and its trace is the trace gap `3 - tr M`.  At
trace three the residue vanishes.  At trace two the residue is the one
extra projection line, and the boundary strata read it: at a boundary
atom the frame column dies through the exchange law, thus the whole
projection column is residue, and the all-heavy floor prices the
residue diagonal above the weight.

The exchange law `N * M = Mᵀ * N` of the column Gram is the ambient
form of the reduced commutation.  The extraction campaign found that
the two open residues die inside the commutation layer, thus the named
exchange law is the entry point of the residue kills.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.columnGram_isUnit_det_of_leftInverse` — the column Gram is
  invertible under a left inverse.
* `Gtz.columnGram_exchange_of_representation` — **THE EXCHANGE LAW**
  `N * M = Mᵀ * N`.
* `Gtz.projection_residue_decomposition` — **THE DECOMPOSITION**: the
  residue with its six laws.
* `Gtz.SharedPrivateData.exists_kernel_residue` — **THE DATUM
  RESIDUE** with the boundary heavy floor.

## Vacuity

The matrix statements are unconditional.  The datum statement
quantifies over shared-private data, and no datum exists if
`Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the column Gram laws -/

/-- The column Gram of a matrix with a left inverse is invertible. -/
theorem columnGram_isUnit_det_of_leftInverse {size bc : ℕ}
    {B : Matrix (Fin size) (Fin bc) ℝ} {L : Matrix (Fin bc) (Fin size) ℝ}
    (hleft : L * B = 1) : IsUnit (Bᵀ * B).det := by
  classical
  have hkerB : ∀ vec : Fin bc → ℝ, B *ᵥ vec = 0 → vec = 0 := by
    intro vec hzero
    have hrecover : L *ᵥ (B *ᵥ vec) = vec := by
      rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
    rw [← hrecover, hzero, Matrix.mulVec_zero]
  have hkerN : ∀ vec : Fin bc → ℝ, (Bᵀ * B) *ᵥ vec = 0 → vec = 0 := by
    intro vec hzero
    have hquadForm : vec ⬝ᵥ ((Bᵀ * B) *ᵥ vec)
        = (B *ᵥ vec) ⬝ᵥ (B *ᵥ vec) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
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
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨vec, hvne, hvzero⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  exact hvne (hkerN vec hvzero)

/-- **THE EXCHANGE LAW.**  A symmetric matrix that carries the basis
columns to a coefficient representation exchanges the coefficient
matrix with the column Gram: `N * M = Mᵀ * N`.  This is the ambient
form of the reduced commutation layer. -/
theorem columnGram_exchange_of_representation {size bc : ℕ}
    {P : Matrix (Fin size) (Fin size) ℝ} {B : Matrix (Fin size) (Fin bc) ℝ}
    {M : Matrix (Fin bc) (Fin bc) ℝ}
    (hPsymm : Pᵀ = P) (hrep : P * B = B * M) :
    (Bᵀ * B) * M = Mᵀ * (Bᵀ * B) := by
  have hform : Bᵀ * (P * B) = (Bᵀ * B) * M := by
    rw [hrep, Matrix.mul_assoc]
  have hsymmForm : (Bᵀ * (P * B))ᵀ = Bᵀ * (P * B) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hPsymm, Matrix.mul_assoc]
  have htrans : ((Bᵀ * B) * M)ᵀ = Mᵀ * (Bᵀ * B) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  rw [← hform, ← hsymmForm, hform, htrans]

/-! ## Layer 2 — the decomposition -/

/-- **THE DECOMPOSITION.**  A symmetric idempotent that represents on a
left-invertible column matrix splits into the frame part
`B * M * N⁻¹ * Bᵀ` plus a kernel residue.  The residue is a symmetric
idempotent, it annihilates the basis columns on both sides, and its
trace is the trace gap. -/
theorem projection_residue_decomposition {size bc : ℕ}
    {P : Matrix (Fin size) (Fin size) ℝ} {B : Matrix (Fin size) (Fin bc) ℝ}
    {L : Matrix (Fin bc) (Fin size) ℝ} {M : Matrix (Fin bc) (Fin bc) ℝ}
    (hPsymm : Pᵀ = P) (hidem : P * P = P) (hleft : L * B = 1)
    (hrep : P * B = B * M) :
    ∃ residue : Matrix (Fin size) (Fin size) ℝ,
      residueᵀ = residue
      ∧ residue * residue = residue
      ∧ residue * B = 0
      ∧ Bᵀ * residue = 0
      ∧ Matrix.trace residue = Matrix.trace P - Matrix.trace M
      ∧ P = B * M * (Bᵀ * B)⁻¹ * Bᵀ + residue := by
  classical
  set N := Bᵀ * B with hN
  have hdetN : IsUnit N.det := columnGram_isUnit_det_of_leftInverse hleft
  have hNiN : N⁻¹ * N = 1 := Matrix.nonsing_inv_mul N hdetN
  have hNNi : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv N hdetN
  have hexch : N * M = Mᵀ * N :=
    columnGram_exchange_of_representation hPsymm hrep
  -- the exchange moves through the inverse
  have hMNi : M * N⁻¹ = N⁻¹ * Mᵀ := by
    have h1 : N⁻¹ * (N * M) * N⁻¹ = N⁻¹ * (Mᵀ * N) * N⁻¹ := by rw [hexch]
    have h2 : N⁻¹ * (N * M) * N⁻¹ = M * N⁻¹ := by
      rw [← Matrix.mul_assoc N⁻¹ N M, hNiN, Matrix.one_mul]
    have h3 : N⁻¹ * (Mᵀ * N) * N⁻¹ = N⁻¹ * Mᵀ := by
      rw [← Matrix.mul_assoc N⁻¹ Mᵀ N, Matrix.mul_assoc (N⁻¹ * Mᵀ) N N⁻¹,
        hNNi, Matrix.mul_one]
    rw [← h2, h1, h3]
  -- the frame part and the two capture forms
  set F := B * M * N⁻¹ * Bᵀ with hF
  set spanProj := B * N⁻¹ * Bᵀ with hspanDef
  have hPPi : P * spanProj = F := by
    rw [hspanDef, hF]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P B, hrep, Matrix.mul_assoc]
  have hBtP : Bᵀ * P = Mᵀ * Bᵀ := by
    rw [← hPsymm, ← Matrix.transpose_mul, hrep, Matrix.transpose_mul]
  have hPiP : spanProj * P = F := by
    rw [hspanDef, hF]
    simp only [Matrix.mul_assoc]
    rw [hBtP, ← Matrix.mul_assoc N⁻¹ Mᵀ Bᵀ, ← hMNi, Matrix.mul_assoc]
  have hspanIdem : spanProj * spanProj = spanProj := by
    rw [hspanDef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᵀ B, ← hN, ← Matrix.mul_assoc N⁻¹ N, hNiN,
      Matrix.one_mul]
  -- the residue and its laws
  refine ⟨P - F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- symmetry: the frame part is the capture of a symmetric pair
    have hFsymm : Fᵀ = F := by
      rw [← hPPi, Matrix.transpose_mul, hPsymm]
      have hspanSymm : spanProjᵀ = spanProj := by
        have hNinvSymm : (N⁻¹)ᵀ = N⁻¹ := by
          rw [Matrix.transpose_nonsing_inv]
          have hNsymm : Nᵀ = N := by
            rw [hN, Matrix.transpose_mul, Matrix.transpose_transpose]
          rw [hNsymm]
        rw [hspanDef, Matrix.transpose_mul, Matrix.transpose_mul,
          Matrix.transpose_transpose, hNinvSymm, ← Matrix.mul_assoc]
      rw [hspanSymm, hPiP, hPPi]
    rw [Matrix.transpose_sub, hPsymm, hFsymm]
  · -- idempotency: both capture forms collapse the cross products
    have hFP : F * P = F := by
      rw [← hPiP, Matrix.mul_assoc, hidem]
    have hPF : P * F = F := by
      rw [← hPPi, ← Matrix.mul_assoc, hidem]
    have hFPi : F * spanProj = F := by
      rw [← hPPi, Matrix.mul_assoc, hspanIdem]
    have hFF : F * F = F := by
      have h1 : F * F = F * P * spanProj := by
        rw [Matrix.mul_assoc F P spanProj, hPPi]
      rw [h1, hFP, hFPi]
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    rw [hidem, hPF, hFP, hFF]
    abel
  · -- the basis columns die on the right
    rw [Matrix.sub_mul, hrep, hF]
    simp only [Matrix.mul_assoc]
    rw [← hN, hNiN, Matrix.mul_one, sub_self]
  · -- the basis columns die on the left
    rw [Matrix.mul_sub, hBtP, hF]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᵀ B, ← hN, ← Matrix.mul_assoc N M,
      hexch, Matrix.mul_assoc Mᵀ N, ← Matrix.mul_assoc N N⁻¹, hNNi,
      Matrix.one_mul, sub_self]
  · -- the trace of the frame part is the coefficient trace
    have htraceF : Matrix.trace F = Matrix.trace M := by
      rw [hF, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Bᵀ B, ← hN, Matrix.trace_mul_comm,
        Matrix.mul_assoc, hNiN, Matrix.mul_one]
    rw [Matrix.trace_sub, htraceF]
  · rw [add_sub_cancel]

/-! ## Layer 3 — the datum residue with the boundary heavy floor -/

set_option maxHeartbeats 1600000 in
/-- **THE DATUM RESIDUE.**  Every shared-private datum splits its chart
projection into the frame part plus a kernel residue with the six
laws, the trace gap `3 - tr M`, and the boundary heavy floor: at every
atom with a zero shifted weight, the weight sits strictly below the
residue diagonal.  At trace three the residue has trace zero, and the
boundary floor reproves the trace-split kill.  At trace two the
residue carries one projection line, and the two open residue strata
read it. -/
theorem SharedPrivateData.exists_kernel_residue
    {crux : SixThreeCrux} (data : SharedPrivateData crux) :
    ∃ residue : Matrix (Fin 6) (Fin 6) ℝ,
      residueᵀ = residue
      ∧ residue * residue = residue
      ∧ residue * tightBasisColumns data.tightDir data.basisLabel = 0
      ∧ (tightBasisColumns data.tightDir data.basisLabel)ᵀ * residue = 0
      ∧ Matrix.trace residue = 3 - Matrix.trace data.coeff
      ∧ (chartPointOfDesign crux.design).chart
          = tightBasisColumns data.tightDir data.basisLabel * data.coeff
            * ((tightBasisColumns data.tightDir data.basisLabel)ᵀ
                * tightBasisColumns data.tightDir data.basisLabel)⁻¹
            * (tightBasisColumns data.tightDir data.basisLabel)ᵀ
            + residue
      ∧ ∀ atomIndex : Fin 6,
          chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex = 0 →
          (chartPointOfDesign crux.design).weight atomIndex
            < residue atomIndex atomIndex := by
  classical
  set B := tightBasisColumns data.tightDir data.basisLabel with hB
  set P := (chartPointOfDesign crux.design).chart with hP
  have hrep : P * B = B * data.coeff := data.hrepresentation
  have hPsymm : Pᵀ = P := data.hdata.isSymmetric
  have hidem : P * P = P := projectionOfDesign_mul_self crux.design
  have hPtrace : Matrix.trace P = 3 := by
    have h : Matrix.trace (projectionOfDesign crux.design)
        = ((3 : ℕ) : ℝ) := trace_projectionOfDesign crux.design
    norm_num at h
    exact h
  obtain ⟨residue, hRsymm, hRidem, hRB, hBtR, hRtrace, hdecomp⟩ :=
    projection_residue_decomposition hPsymm hidem data.hleft hrep
  refine ⟨residue, hRsymm, hRidem, hRB, hBtR, ?_, hdecomp, ?_⟩
  · rw [hRtrace, hPtrace]
  · intro atomIndex hzero
    -- the annihilated capture row at the boundary atom
    have hrow : ∀ columnIndex, (B * data.coeff) atomIndex columnIndex = 0 :=
      fun columnIndex => basis_capture_column_zero_of_diagonal_zero
        data.hdata data.hspan data.hrepresentation hzero columnIndex
    -- the exchange kills the frame column
    set N := Bᵀ * B with hN
    have hdetN : IsUnit N.det :=
      columnGram_isUnit_det_of_leftInverse data.hleft
    have hFcol : (B * data.coeff * N⁻¹ * Bᵀ)
        *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) = 0 := by
      have hNiN : N⁻¹ * N = 1 := Matrix.nonsing_inv_mul N hdetN
      have hNNi : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv N hdetN
      have hexchange : N * data.coeff = data.coeffᵀ * N :=
        columnGram_exchange_of_representation hPsymm hrep
      have hMNi : data.coeff * N⁻¹ = N⁻¹ * data.coeffᵀ := by
        have h1 : N⁻¹ * (N * data.coeff) * N⁻¹
            = N⁻¹ * (data.coeffᵀ * N) * N⁻¹ := by rw [hexchange]
        have h2 : N⁻¹ * (N * data.coeff) * N⁻¹ = data.coeff * N⁻¹ := by
          rw [← Matrix.mul_assoc N⁻¹ N data.coeff, hNiN, Matrix.one_mul]
        have h3 : N⁻¹ * (data.coeffᵀ * N) * N⁻¹ = N⁻¹ * data.coeffᵀ := by
          rw [← Matrix.mul_assoc N⁻¹ data.coeffᵀ N,
            Matrix.mul_assoc (N⁻¹ * data.coeffᵀ) N N⁻¹, hNNi,
            Matrix.mul_one]
        rw [← h2, h1, h3]
      have hrowvec : (B * data.coeff)ᵀ
          *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) = 0 := by
        funext columnIndex
        have happly : ((B * data.coeff)ᵀ
            *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)) columnIndex
            = (B * data.coeff) atomIndex columnIndex := by
          simp [Matrix.mulVec, dotProduct, Pi.single_apply,
            Matrix.transpose_apply, mul_ite, mul_one, mul_zero]
        rw [happly, hrow columnIndex]
        rfl
      have hswap : B * data.coeff * N⁻¹ * Bᵀ
          = B * N⁻¹ * (B * data.coeff)ᵀ := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc data.coeff N⁻¹ Bᵀ, hMNi, Matrix.mul_assoc]
      rw [hswap, ← Matrix.mulVec_mulVec, hrowvec, Matrix.mulVec_zero]
    -- the projection column is pure residue
    have hcol : P *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)
        = residue *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) := by
      rw [hdecomp, Matrix.add_mulVec, hFcol, zero_add]
    -- the diagonal reading
    have hPdiag : P atomIndex atomIndex = residue atomIndex atomIndex := by
      have happlyP : (P *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)) atomIndex
          = P atomIndex atomIndex := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
          mul_one, mul_zero]
      have happlyR : (residue
          *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)) atomIndex
          = residue atomIndex atomIndex := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
          mul_one, mul_zero]
      rw [← happlyP, hcol, happlyR]
    -- the all-heavy floor prices the residue diagonal
    have hgap := crux.chartGap_diagonal_pos atomIndex
    simp only [chartStationaryGap, Matrix.sub_apply,
      Matrix.diagonal_apply_eq] at hgap
    rw [← hP, hPdiag] at hgap
    linarith

end Gtz
