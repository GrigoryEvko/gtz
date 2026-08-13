import Gtz.Wave.SharedPrivateBoundaryComplement

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The shared-private Gram commutation — the kernel is assembly-invariant
and the boundary propagates

The read frame carries two laws beyond the reads.  The read vectors span
the slot space, because the basis columns have a left inverse.  And the
read Gram commutes with the read idempotent, because the column Gram of
the basis obeys the exchange law of a symmetric projection.  This module
turns the two laws into kills.

The kernel invariance.  The commutation says that the kernel of the read
idempotent is invariant under the read Gram.  Read at a kernel vector,
the law becomes a linear relation: the assembly-weighted total of the
fixed parts of the reads vanishes.  The proof needs one swap of two
sums, because the fixed part of a read is orthogonal to every kernel
vector.

The all-boundary kill.  At a boundary atom the whole read lies in the
kernel of the idempotent.  If every atom sits at the boundary, then the
idempotent annihilates every read, thus it annihilates the whole slot
space by the span law, thus its trace is zero.  The coefficient trace is
two or three, thus some atom is interior.

The boundary propagation.  Take a boundary atom.  In the relation the
boundary atoms drop out, and an atom with a carrier disjoint from the
boundary carrier drops out too.  If one atom alone survives, and its
carrier meets the boundary carrier in exactly one slot, then its
assembly entry is one nonzero product.  Thus the idempotent annihilates
that read, and the atom joins the boundary.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.gram_kernel_invariant` — **THE KERNEL INVARIANCE.**
* `Gtz.SharedPrivateData.false_of_all_boundary` — **THE ALL-BOUNDARY
  KILL.**
* `Gtz.SharedPrivateData.exists_interior_atom` — some atom is interior.
* `Gtz.SharedPrivateData.boundary_of_unique_cocarrier` — **THE BOUNDARY
  PROPAGATION.**
* `Gtz.SharedPrivateData.false_of_unique_cocarrier` — the propagation
  kill.

## Vacuity

The matrix statement is unconditional.  The datum statements quantify
over shared-private data, and no datum exists if `Gtz.GtzWeighted 6 3`
holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the kernel invariance -/

/-- **THE KERNEL INVARIANCE.**  A family whose Gram commutes with a
symmetric idempotent carries a linear relation at every kernel vector:
the weighted total of the fixed parts vanishes, with the family Gram row
of the kernel vector as the weights. -/
theorem gram_kernel_invariant {m n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Sᵀ = S) (V : Fin m → Fin n → ℝ)
    (hcomm : ∀ rowSlot colSlot : Fin n,
      (∑ i, V i rowSlot * (S *ᵥ V i) colSlot)
        = ∑ i, (S *ᵥ V i) rowSlot * V i colSlot)
    {x : Fin n → ℝ} (hx : S *ᵥ x = 0) (slot : Fin n) :
    ∑ i, (V i ⬝ᵥ x) * (S *ᵥ V i) slot = 0 := by
  classical
  have hvm : x ᵥ* S = S *ᵥ x := by
    conv_lhs => rw [← hsymm]
    rw [Matrix.vecMul_transpose]
  have hzero : ∀ i : Fin m, (S *ᵥ V i) ⬝ᵥ x = 0 := by
    intro i
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, hvm, hx, zero_dotProduct]
  have hleft : (∑ i, (V i ⬝ᵥ x) * (S *ᵥ V i) slot)
      = ∑ i, ∑ j, x j * (V i j * (S *ᵥ V i) slot) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hright : (∑ i, V i slot * ((S *ᵥ V i) ⬝ᵥ x))
      = ∑ i, ∑ j, x j * ((S *ᵥ V i) j * V i slot) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmid : (∑ j, ∑ i, x j * (V i j * (S *ᵥ V i) slot))
      = ∑ j, ∑ i, x j * ((S *ᵥ V i) j * V i slot) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, hcomm j slot]
  calc (∑ i, (V i ⬝ᵥ x) * (S *ᵥ V i) slot)
      = ∑ i, ∑ j, x j * (V i j * (S *ᵥ V i) slot) := hleft
    _ = ∑ j, ∑ i, x j * (V i j * (S *ᵥ V i) slot) := Finset.sum_comm
    _ = ∑ j, ∑ i, x j * ((S *ᵥ V i) j * V i slot) := hmid
    _ = ∑ i, ∑ j, x j * ((S *ᵥ V i) j * V i slot) := Finset.sum_comm
    _ = ∑ i, V i slot * ((S *ᵥ V i) ⬝ᵥ x) := hright.symm
    _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hzero i, mul_zero]

/-! ## Layer 2 — the all-boundary kill -/

set_option maxHeartbeats 1600000 in
/-- **THE ALL-BOUNDARY KILL.**  A diagonal-Gram datum cannot put every
atom at the shifted-weight boundary.  Every read would lie in the kernel
of the read idempotent, the reads span the slot space, thus the
idempotent would vanish and its trace would be zero.  The coefficient
trace is two or three. -/
theorem SharedPrivateData.false_of_all_boundary {crux : SixThreeCrux}
    (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (hall : ∀ atomIndex : Fin 6,
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0) :
    False := by
  classical
  obtain ⟨S, readVecs, hSsymm, _hSidem, hStrace, _hsupp, _hread, _hnorm,
    _hnz, hboundary, _hcarrierNz, hspan, _hcommute⟩ :=
    data.exists_kernel_read_frame hdiag
  have hvm : ∀ v : Fin data.basisCount → ℝ, v ᵥ* S = S *ᵥ v := by
    intro v
    conv_lhs => rw [← hSsymm]
    rw [Matrix.vecMul_transpose]
  have hcolumn : ∀ v : Fin data.basisCount → ℝ, S *ᵥ v = 0 := by
    intro v
    refine hspan (S *ᵥ v) fun atomIndex => ?_
    rw [Matrix.dotProduct_mulVec, hvm, hboundary atomIndex (hall atomIndex),
      zero_dotProduct]
  have hdiagZero : ∀ slot : Fin data.basisCount, S slot slot = 0 := by
    intro slot
    have hzero := hcolumn (Pi.single slot 1)
    have happly : (S *ᵥ (Pi.single slot 1 : Fin data.basisCount → ℝ)) slot
        = S slot slot := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one,
        mul_zero]
    rw [← happly, hzero]
    rfl
  have htraceZero : Matrix.trace data.coeff = 0 := by
    rw [← hStrace, Matrix.trace]
    exact Finset.sum_eq_zero fun slot _ => hdiagZero slot
  rcases data.htrace with htwo | hthree
  · rw [htwo] at htraceZero
    norm_num at htraceZero
  · rw [hthree] at htraceZero
    norm_num at htraceZero

/-- Some atom of a diagonal-Gram datum has a positive shifted weight.
The capture diagonal is nonnegative, and the all-boundary kill refuses a
zero at every atom. -/
theorem SharedPrivateData.exists_interior_atom {crux : SixThreeCrux}
    (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) :
    ∃ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex := by
  classical
  by_contra hnot
  push Not at hnot
  refine data.false_of_all_boundary hdiag fun atomIndex => ?_
  have hle := hnot atomIndex
  have hge := capture_diagonal_nonneg_of_isChartStationaryData data.hdata
    atomIndex
  linarith

/-! ## Layer 3 — the boundary propagation -/

set_option maxHeartbeats 3200000 in
/-- **THE BOUNDARY PROPAGATION.**  Take a boundary atom of a
diagonal-Gram datum.  Suppose one atom alone carries a slot of the
boundary carrier without sitting at the boundary itself, and suppose the
two carriers meet in exactly one slot.  Then that atom also sits at the
boundary.  The kernel invariance leaves one term, its assembly weight is
a single nonzero product, thus the read idempotent annihilates the
read. -/
theorem SharedPrivateData.boundary_of_unique_cocarrier {crux : SixThreeCrux}
    (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    {atomZero atomOne : Fin 6} {meetSlot : Fin data.basisCount}
    (hzero : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomZero = 0)
    (hmeetZero : atomZero ∈ datumTightSupport data.tightDir
      (data.basisLabel meetSlot))
    (hmeetOne : atomOne ∈ datumTightSupport data.tightDir
      (data.basisLabel meetSlot))
    (hunique : ∀ slot : Fin data.basisCount, slot ≠ meetSlot →
      atomZero ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      atomOne ∉ datumTightSupport data.tightDir (data.basisLabel slot))
    (hothers : ∀ atomProbe : Fin 6, atomProbe ≠ atomOne →
      (∃ slot : Fin data.basisCount,
        atomZero ∈ datumTightSupport data.tightDir (data.basisLabel slot)
          ∧ atomProbe ∈ datumTightSupport data.tightDir
            (data.basisLabel slot)) →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomProbe = 0) :
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne = 0 := by
  classical
  obtain ⟨S, readVecs, hSsymm, _hSidem, _hStrace, hsuppFrame, hreadFrame,
    _hnorm, _hnz, hboundary, hcarrierNz, _hspan, hcommute⟩ :=
    data.exists_kernel_read_frame hdiag
  have hmemActive : ∀ slot, data.basisLabel slot ∈ data.activeSet := by
    intro slot
    have hmem := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  -- the assembly entry of the boundary atom collapses to the meeting slot
  have hdot : readVecs atomOne ⬝ᵥ readVecs atomZero
      = readVecs atomOne meetSlot * readVecs atomZero meetSlot := by
    rw [dotProduct]
    refine Finset.sum_eq_single meetSlot (fun slot _ hne => ?_)
      (fun hnot => absurd (Finset.mem_univ meetSlot) hnot)
    by_cases hmem : atomZero ∈ datumTightSupport data.tightDir
      (data.basisLabel slot)
    · rw [hsuppFrame atomOne slot (hunique slot hne hmem), zero_mul]
    · rw [hsuppFrame atomZero slot hmem, mul_zero]
  have hdotNe : readVecs atomOne ⬝ᵥ readVecs atomZero ≠ 0 := by
    rw [hdot]
    exact mul_ne_zero (hcarrierNz atomOne meetSlot hmeetOne)
      (hcarrierNz atomZero meetSlot hmeetZero)
  -- every other atom drops out of the kernel relation
  have hdrop : ∀ atomProbe : Fin 6, atomProbe ∈ Finset.univ →
      atomProbe ≠ atomOne →
      ∀ slot : Fin data.basisCount,
        (readVecs atomProbe ⬝ᵥ readVecs atomZero)
          * (S *ᵥ readVecs atomProbe) slot = 0 := by
    intro atomProbe _ hne slot
    by_cases hco : ∃ slotProbe : Fin data.basisCount,
      atomZero ∈ datumTightSupport data.tightDir
          (data.basisLabel slotProbe)
        ∧ atomProbe ∈ datumTightSupport data.tightDir
          (data.basisLabel slotProbe)
    · rw [hboundary atomProbe (hothers atomProbe hne hco)]
      simp
    · push Not at hco
      have hzeroDot : readVecs atomProbe ⬝ᵥ readVecs atomZero = 0 := by
        rw [dotProduct]
        refine Finset.sum_eq_zero fun slotProbe _ => ?_
        by_cases hmem : atomZero ∈ datumTightSupport data.tightDir
          (data.basisLabel slotProbe)
        · rw [hsuppFrame atomProbe slotProbe (hco slotProbe hmem), zero_mul]
        · rw [hsuppFrame atomZero slotProbe hmem, mul_zero]
      rw [hzeroDot, zero_mul]
  -- the surviving term annihilates the read
  have hfixedZero : ∀ slot : Fin data.basisCount,
      (S *ᵥ readVecs atomOne) slot = 0 := by
    intro slot
    have hrel := gram_kernel_invariant hSsymm readVecs hcommute
      (hboundary atomZero hzero) slot
    have hsingle := Finset.sum_eq_single_of_mem atomOne
      (Finset.mem_univ atomOne)
      (fun atomProbe hmem hne => hdrop atomProbe hmem hne slot)
    rw [hsingle] at hrel
    rcases mul_eq_zero.mp hrel with hcase | hcase
    · exact absurd hcase hdotNe
    · exact hcase
  -- the annihilated read reads the shifted weight at the meeting slot
  have hreadOne := hreadFrame atomOne meetSlot
    (datumTightSupport_subset data.hdata (hmemActive meetSlot) hmeetOne)
  rw [hfixedZero meetSlot] at hreadOne
  rcases mul_eq_zero.mp hreadOne.symm with hcase | hcase
  · exact hcase
  · exact absurd hcase (hcarrierNz atomOne meetSlot hmeetOne)

/-- **THE PROPAGATION KILL.**  The same configuration with an interior
atom dies: the propagation puts that atom at the boundary. -/
theorem SharedPrivateData.false_of_unique_cocarrier {crux : SixThreeCrux}
    (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    {atomZero atomOne : Fin 6} {meetSlot : Fin data.basisCount}
    (hzero : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomZero = 0)
    (hone : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne ≠ 0)
    (hmeetZero : atomZero ∈ datumTightSupport data.tightDir
      (data.basisLabel meetSlot))
    (hmeetOne : atomOne ∈ datumTightSupport data.tightDir
      (data.basisLabel meetSlot))
    (hunique : ∀ slot : Fin data.basisCount, slot ≠ meetSlot →
      atomZero ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      atomOne ∉ datumTightSupport data.tightDir (data.basisLabel slot))
    (hothers : ∀ atomProbe : Fin 6, atomProbe ≠ atomOne →
      (∃ slot : Fin data.basisCount,
        atomZero ∈ datumTightSupport data.tightDir (data.basisLabel slot)
          ∧ atomProbe ∈ datumTightSupport data.tightDir
            (data.basisLabel slot)) →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomProbe = 0) :
    False :=
  hone (data.boundary_of_unique_cocarrier hdiag hzero hmeetZero hmeetOne
    hunique hothers)

end Gtz
