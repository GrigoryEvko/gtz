import Gtz.Wave.SharedPrivateSlotEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The kernel chain — the general triangular family and the basis-count-five
structure

The trace floor caps a kernel-fixed independent family by the
complementary trace.  The landed triple kill builds such a family from
three boundary reads.  Three is not the natural size: the family has one
member for each independent kernel witness, and the kernel of the read
idempotent has the complementary trace as its dimension.

This module makes the family generic.  A chain of any length,
triangular in its slot pattern, is independent by back substitution.
Thus **a chain longer than the complementary trace is a contradiction**,
at every basis count and at both traces.

The three kernel witnesses.  A chain member is one of three things.

* **A dead slot.**  A slot whose support carries no interior atom has a
  vanishing idempotent column.  The slot energy identity kills each
  fixed part at that slot, and the span law kills the whole column.  The
  slot axis is a kernel vector, and it is nonzero at that slot alone.
* **A boundary read.**  A boundary atom has a kernel-fixed read, and the
  read is nonzero exactly on the carrier of the atom.
* **A residual.**  Any atom has a kernel-fixed residual, the read minus
  its fixed part.  On the carrier the residual is the read times one
  minus the shifted weight, thus it is nonzero there.  Off the carrier
  it is unknown, thus a residual sits at the end of the chain only.

The double-cover budget.  The coefficient trace lives on the slots that
the interior atoms carry.  The carrier cap prices the diagonal total of
each interior carrier.  If every carried slot has two interior carriers,
the double count gives twice the trace on one side and the interior
count plus the shifted total on the other.  At trace two this forces
**four interior atoms**.

The basis-count-five structure.  The whole private support is a boundary
set, thus every interior atom sits off it and the interior count is at
most three.  Every interior atom has multiplicity two or more, the
private slot has a vanishing diagonal, and the budget supplies a slot
with exactly one interior carrier.  The trace-two boundary residue at
basis count five carries all of it.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.triangular_family_independent` — **THE BACK SUBSTITUTION**, at
  every family size.
* `Gtz.false_of_triangular_fixed_family` — **THE GENERAL TRACE FLOOR**
  for a triangular kernel-fixed family.
* `Gtz.SlotWitness` — the three kernel witnesses.
* `Gtz.dead_slot_column_of_frame` — **THE DEAD-SLOT COLUMN LAW.**
* `Gtz.SharedPrivateData.false_of_kernel_chain` — **THE KERNEL CHAIN
  KILL**, at every chain length.
* `Gtz.SharedPrivateData.false_of_triangular_boundary_quadruple`,
  `Gtz.SharedPrivateData.false_of_private_dead_chain` — the two
  corollaries that the basis-count-five census consumes.
* `Gtz.SharedPrivateData.four_le_interior_card_of_double_cover`,
  `Gtz.SharedPrivateData.exists_single_cover_slot` — **THE DOUBLE-COVER
  BUDGET.**
* `Gtz.SharedPrivateData.interior_notMem_privateSupport`,
  `Gtz.SharedPrivateData.interior_card_le_three`,
  `Gtz.SharedPrivateData.two_le_multiplicity_of_interior`,
  `Gtz.SharedPrivateData.privateSlot_diag_eq_zero` — the private-slot
  structure.
* `Gtz.SharedPrivateBoundaryFiveCoreClosed` with
  `Gtz.sharedPrivateBoundaryFiveClosed_of_core` — the narrowed
  basis-count-five residue.
* `Gtz.sharedPrivateBoundaryClosed_of_core`,
  `Gtz.sharedPrivateKilled_of_core_strata`,
  `Gtz.rankFourSharedPrivateClosed_of_core_strata`,
  `Gtz.rankFiveSharedPrivateClosed_of_core_strata`,
  `Gtz.rankSixSharedPrivateClosed_of_core_strata` — the dispatches.

## Vacuity

The matrix statements are unconditional.  The datum statements quantify
over shared-private data, and no datum exists if `Gtz.GtzWeighted 6 3`
holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the back substitution at every family size -/

/-- **THE BACK SUBSTITUTION.**  A family with a triangular slot pattern
is independent.  Each member is nonzero at its own slot, and every
earlier member vanishes there.  The relation read at the slot of the
last live index leaves one term. -/
theorem triangular_family_independent {famSize slotCount : ℕ}
    (family : Fin famSize → Fin slotCount → ℝ)
    (slots : Fin famSize → Fin slotCount)
    (hpivot : ∀ i, family i (slots i) ≠ 0)
    (hlower : ∀ i k : Fin famSize, i < k → family i (slots k) = 0)
    (coeffVec : Fin famSize → ℝ)
    (hzero : ∀ slot, ∑ i, coeffVec i * family i slot = 0) :
    coeffVec = 0 := by
  classical
  have hstep : ∀ k : Fin famSize,
      (∀ i : Fin famSize, k < i → coeffVec i = 0) → coeffVec k = 0 := by
    intro k hlater
    have hrow := hzero (slots k)
    have hcollapse : (∑ i, coeffVec i * family i (slots k))
        = coeffVec k * family k (slots k) := by
      refine Finset.sum_eq_single k (fun i _ hne => ?_)
        (fun hnot => absurd (Finset.mem_univ k) hnot)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [hlower i k hlt, mul_zero]
      · rw [hlater i hgt, zero_mul]
    rw [hcollapse] at hrow
    rcases mul_eq_zero.mp hrow with hcase | hcase
    · exact hcase
    · exact absurd hcase (hpivot k)
  have hdown : ∀ depth : ℕ, ∀ k : Fin famSize,
      famSize ≤ (k : ℕ) + depth + 1 → coeffVec k = 0 := by
    intro depth
    induction depth with
    | zero =>
      intro k hk
      refine hstep k fun i hi => ?_
      exfalso
      have hlt : (k : ℕ) < (i : ℕ) := hi
      have hbound : (i : ℕ) < famSize := i.isLt
      omega
    | succ depth ih =>
      intro k hk
      refine hstep k fun i hi => ?_
      have hlt : (k : ℕ) < (i : ℕ) := hi
      exact ih i (by omega)
  funext k
  exact hdown famSize k (by omega)

/-- **THE GENERAL TRACE FLOOR.**  A triangular family fixed by a
symmetric idempotent is capped by the trace of that idempotent.  The
back substitution gives independence, and the Gram of an independent
family is kernel free. -/
theorem false_of_triangular_fixed_family {famSize slotCount : ℕ}
    {fixedMat : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : fixedMatᵀ = fixedMat) (hidem : fixedMat * fixedMat = fixedMat)
    (family : Fin famSize → Fin slotCount → ℝ)
    (hfix : ∀ i, fixedMat *ᵥ family i = family i)
    (slots : Fin famSize → Fin slotCount)
    (hpivot : ∀ i, family i (slots i) ≠ 0)
    (hlower : ∀ i k : Fin famSize, i < k → family i (slots k) = 0) :
    (famSize : ℝ) ≤ Matrix.trace fixedMat :=
  trace_floor_of_fixed_family hsymm hidem family hfix
    (gram_kernel_free_of_independent family
      fun coeffVec hcoeff =>
        triangular_family_independent family slots hpivot hlower coeffVec hcoeff)

/-! ## Layer 2 — the three kernel witnesses -/

/-- **THE KERNEL WITNESSES.**  A chain member is a dead slot axis, a
boundary read, or the residual of a read. -/
inductive SlotWitness (basisCount : ℕ) where
  /-- The axis of a slot that no interior atom carries. -/
  | dead : Fin basisCount → SlotWitness basisCount
  /-- The read of a boundary atom. -/
  | read : Fin 6 → SlotWitness basisCount
  /-- The read of an atom minus its fixed part. -/
  | residual : Fin 6 → SlotWitness basisCount

set_option maxHeartbeats 3200000 in
/-- **THE DEAD-SLOT COLUMN LAW.**  A slot whose support carries only
boundary atoms has a vanishing idempotent column.  The slot energy
identity kills every fixed part at that slot, and the span law kills the
column.  The statement fixes a read frame, thus it lives inside the
chain kill and inside the budget. -/
theorem dead_slot_column_of_frame {atomCount slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S)
    (readVecs : Fin atomCount → Fin slotCount → ℝ)
    (hcomm : ∀ rowSlot colSlot : Fin slotCount,
      (∑ i, readVecs i rowSlot * (S *ᵥ readVecs i) colSlot)
        = ∑ i, (S *ᵥ readVecs i) rowSlot * readVecs i colSlot)
    (hspan : ∀ x : Fin slotCount → ℝ,
      (∀ i : Fin atomCount, readVecs i ⬝ᵥ x = 0) → x = 0)
    (deadSlot : Fin slotCount)
    (hkill : ∀ i : Fin atomCount,
      (S *ᵥ readVecs i) deadSlot * readVecs i deadSlot = 0) :
    S *ᵥ (fun slot => if slot = deadSlot then (1 : ℝ) else 0) = 0 := by
  classical
  have hidentity := gram_kernel_entry hsymm hidem readVecs hcomm deadSlot deadSlot
  have hsumZero : (∑ i, (S *ᵥ readVecs i) deadSlot * (S *ᵥ readVecs i) deadSlot)
      = 0 := by
    rw [hidentity]
    exact Finset.sum_eq_zero fun i _ => hkill i
  have hEach : ∀ i : Fin atomCount, (S *ᵥ readVecs i) deadSlot = 0 := by
    intro i
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin atomCount))) =>
        mul_self_nonneg ((S *ᵥ readVecs j) deadSlot))).mp hsumZero i
      (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hterm
  have hsymmEntry : ∀ rowIdx colIdx : Fin slotCount, S colIdx rowIdx = S rowIdx colIdx := by
    intro rowIdx colIdx
    have hentry := congrFun (congrFun hsymm rowIdx) colIdx
    rwa [Matrix.transpose_apply] at hentry
  have hcol : (fun rowIdx => S rowIdx deadSlot) = 0 := by
    refine hspan _ fun i => ?_
    calc readVecs i ⬝ᵥ (fun rowIdx => S rowIdx deadSlot)
        = ∑ rowIdx, readVecs i rowIdx * S rowIdx deadSlot := rfl
      _ = ∑ rowIdx, S deadSlot rowIdx * readVecs i rowIdx :=
          Finset.sum_congr rfl fun rowIdx _ => by
            rw [hsymmEntry rowIdx deadSlot]; ring
      _ = (S *ᵥ readVecs i) deadSlot := rfl
      _ = 0 := hEach i
  funext rowIdx
  have hentry := congrFun hcol rowIdx
  calc (S *ᵥ fun slot => if slot = deadSlot then (1 : ℝ) else 0) rowIdx
      = ∑ slot, S rowIdx slot * (if slot = deadSlot then (1 : ℝ) else 0) := rfl
    _ = S rowIdx deadSlot := by
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
    _ = 0 := hentry

/-! ## Layer 3 — the kernel chain kill -/

set_option maxHeartbeats 6400000 in
/-- **THE KERNEL CHAIN KILL.**  A triangular chain of kernel witnesses
longer than the complementary trace is a contradiction.  A dead slot
carries its own axis, a boundary atom carries its read, and any atom
carries its residual.  A residual is unknown off the carrier, thus it
sits at the end of the chain only. -/
theorem SharedPrivateData.false_of_kernel_chain {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) {chainLength : ℕ}
    (source : Fin chainLength → SlotWitness data.basisCount)
    (slots : Fin chainLength → Fin data.basisCount)
    (hdeadSlot : ∀ (i : Fin chainLength) (deadSlot : Fin data.basisCount),
      source i = SlotWitness.dead deadSlot → slots i = deadSlot)
    (hdeadBoundary : ∀ (i : Fin chainLength) (deadSlot : Fin data.basisCount),
      source i = SlotWitness.dead deadSlot →
      ∀ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel deadSlot) →
        chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex = 0)
    (hreadBoundary : ∀ (i : Fin chainLength) (atomIndex : Fin 6),
      source i = SlotWitness.read atomIndex →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0)
    (hreadMem : ∀ (i : Fin chainLength) (atomIndex : Fin 6),
      source i = SlotWitness.read atomIndex →
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel (slots i)))
    (hresidualMem : ∀ (i : Fin chainLength) (atomIndex : Fin 6),
      source i = SlotWitness.residual atomIndex →
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel (slots i)))
    (hresidualLast : ∀ i k : Fin chainLength, i < k →
      ∀ atomIndex : Fin 6, source i ≠ SlotWitness.residual atomIndex)
    (hlowerDead : ∀ i k : Fin chainLength, i < k →
      ∀ deadSlot : Fin data.basisCount,
        source i = SlotWitness.dead deadSlot → slots k ≠ deadSlot)
    (hlowerRead : ∀ i k : Fin chainLength, i < k →
      ∀ atomIndex : Fin 6, source i = SlotWitness.read atomIndex →
        atomIndex ∉ datumTightSupport data.tightDir
          (data.basisLabel (slots k)))
    (hcount : (data.basisCount : ℝ)
      < Matrix.trace data.coeff + chainLength) : False := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsuppFrame, hreadFrame, _hnorm,
    _hnz, hboundary, hcarrierNz, hspan, hcommute⟩ :=
    data.exists_kernel_read_frame hdiag
  set chartValue := chartObjective (chartPointOfDesign crux.design)
    with hchartValue
  set atomWeight := (chartPointOfDesign crux.design).weight with hatomWeight
  have hmemActive : ∀ slot, data.basisLabel slot ∈ data.activeSet := by
    intro slot
    have hmem := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  have hread : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      (S *ᵥ readVecs atomIndex) slot
        = (chartValue + atomWeight atomIndex) * readVecs atomIndex slot :=
    fun atomIndex slot hmem => hreadFrame atomIndex slot
      (datumTightSupport_subset data.hdata (hmemActive slot) hmem)
  have hltOne : ∀ atomIndex : Fin 6, chartValue + atomWeight atomIndex < 1 := by
    intro atomIndex
    have hwle : atomWeight atomIndex ≤ 1 := by
      have hle : atomWeight atomIndex ≤ ∑ probe, atomWeight probe :=
        Finset.single_le_sum (f := atomWeight)
          (fun probe _ => (data.hdata.weight_pos probe).le) (Finset.mem_univ atomIndex)
      rwa [data.hdata.weight_sum_one] at hle
    have hneg : chartValue < 0 := data.hvalueNeg
    linarith
  -- the three witness vectors
  set witnessVec : SlotWitness data.basisCount → Fin data.basisCount → ℝ := fun wit =>
    match wit with
    | SlotWitness.dead deadSlot => fun slot => if slot = deadSlot then (1 : ℝ) else 0
    | SlotWitness.read atomIndex => readVecs atomIndex
    | SlotWitness.residual atomIndex => readVecs atomIndex - S *ᵥ readVecs atomIndex
    with hwitnessVec
  have hwDead : ∀ deadSlot : Fin data.basisCount,
      witnessVec (SlotWitness.dead deadSlot)
        = fun slot => if slot = deadSlot then (1 : ℝ) else 0 := fun _ => rfl
  have hwRead : ∀ atomIndex : Fin 6,
      witnessVec (SlotWitness.read atomIndex) = readVecs atomIndex := fun _ => rfl
  have hwResidual : ∀ atomIndex : Fin 6,
      witnessVec (SlotWitness.residual atomIndex)
        = readVecs atomIndex - S *ᵥ readVecs atomIndex := fun _ => rfl
  set family : Fin chainLength → Fin data.basisCount → ℝ := fun i =>
    witnessVec (source i) with hfamily
  have hfamApply : ∀ i : Fin chainLength, family i = witnessVec (source i) :=
    fun _ => rfl
  -- the complementary idempotent
  set kernelMat : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ := 1 - S
    with hkernelMat
  have hkSymm : kernelMatᵀ = kernelMat := by
    rw [hkernelMat, Matrix.transpose_sub, Matrix.transpose_one, hSsymm]
  have hkIdem : kernelMat * kernelMat = kernelMat := by
    rw [hkernelMat]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      hSidem]
    abel
  have hkApply : ∀ vec : Fin data.basisCount → ℝ,
      kernelMat *ᵥ vec = vec - S *ᵥ vec := by
    intro vec
    rw [hkernelMat, Matrix.sub_mulVec, Matrix.one_mulVec]
  -- each witness is fixed by the complementary idempotent
  have hfix : ∀ i : Fin chainLength, kernelMat *ᵥ family i = family i := by
    intro i
    rcases hsrc : source i with deadSlot | atomIndex | atomIndex
    · have hzeroCol : S *ᵥ (fun slot => if slot = deadSlot then (1 : ℝ) else 0) = 0 := by
        refine dead_slot_column_of_frame hSsymm hSidem readVecs hcommute hspan
          deadSlot fun atomIndex => ?_
        by_cases hmem : atomIndex ∈ datumTightSupport data.tightDir
          (data.basisLabel deadSlot)
        · have hzero := hdeadBoundary i deadSlot hsrc atomIndex hmem
          rw [hread atomIndex deadSlot hmem, hzero, zero_mul, zero_mul]
        · rw [hsuppFrame atomIndex deadSlot hmem, mul_zero]
      have hstep : family i = fun slot => if slot = deadSlot then (1 : ℝ) else 0 := by
        rw [hfamApply i, hsrc, hwDead]
      rw [hstep, hkApply, hzeroCol, sub_zero]
    · have hstep : family i = readVecs atomIndex := by rw [hfamApply i, hsrc, hwRead]
      rw [hstep, hkApply, hboundary atomIndex (hreadBoundary i atomIndex hsrc),
        sub_zero]
    · have hstep : family i = readVecs atomIndex - S *ᵥ readVecs atomIndex := by
        rw [hfamApply i, hsrc, hwResidual]
      have hkill : S *ᵥ (readVecs atomIndex - S *ᵥ readVecs atomIndex) = 0 := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hSidem, sub_self]
      rw [hstep, hkApply, hkill, sub_zero]
  -- each witness is nonzero at its own slot
  have hpivot : ∀ i : Fin chainLength, family i (slots i) ≠ 0 := by
    intro i
    rcases hsrc : source i with deadSlot | atomIndex | atomIndex
    · have hstep : family i = fun slot => if slot = deadSlot then (1 : ℝ) else 0 := by
        rw [hfamApply i, hsrc, hwDead]
      rw [hstep, hdeadSlot i deadSlot hsrc]
      simp
    · have hstep : family i = readVecs atomIndex := by rw [hfamApply i, hsrc, hwRead]
      rw [hstep]
      exact hcarrierNz atomIndex (slots i) (hreadMem i atomIndex hsrc)
    · have hmem := hresidualMem i atomIndex hsrc
      have hstep : family i = readVecs atomIndex - S *ᵥ readVecs atomIndex := by
        rw [hfamApply i, hsrc, hwResidual]
      have hentry : (readVecs atomIndex - S *ᵥ readVecs atomIndex) (slots i)
          = (1 - (chartValue + atomWeight atomIndex)) * readVecs atomIndex (slots i) := by
        show readVecs atomIndex (slots i) - (S *ᵥ readVecs atomIndex) (slots i)
          = (1 - (chartValue + atomWeight atomIndex)) * readVecs atomIndex (slots i)
        rw [hread atomIndex (slots i) hmem]
        ring
      rw [hstep, hentry]
      refine mul_ne_zero ?_ (hcarrierNz atomIndex (slots i) hmem)
      have hlt := hltOne atomIndex
      linarith
  -- every earlier witness vanishes at every later slot
  have hlower : ∀ i k : Fin chainLength, i < k → family i (slots k) = 0 := by
    intro i k hik
    rcases hsrc : source i with deadSlot | atomIndex | atomIndex
    · have hstep : family i = fun slot => if slot = deadSlot then (1 : ℝ) else 0 := by
        rw [hfamApply i, hsrc, hwDead]
      rw [hstep]
      exact if_neg (hlowerDead i k hik deadSlot hsrc)
    · have hstep : family i = readVecs atomIndex := by rw [hfamApply i, hsrc, hwRead]
      rw [hstep]
      exact hsuppFrame atomIndex (slots k) (hlowerRead i k hik atomIndex hsrc)
    · exact absurd hsrc (hresidualLast i k hik atomIndex)
  have hfloor := false_of_triangular_fixed_family hkSymm hkIdem family hfix slots
    hpivot hlower
  have htraceCompl : Matrix.trace kernelMat
      = (data.basisCount : ℝ) - Matrix.trace data.coeff := by
    rw [hkernelMat, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, hStrace]
  rw [htraceCompl] at hfloor
  linarith

/-- **THE TRIANGULAR BOUNDARY QUADRUPLE.**  Four boundary atoms with a
triangular slot pattern die whenever the basis count is below the trace
plus four.  The chain has four read witnesses and no residual. -/
theorem SharedPrivateData.false_of_triangular_boundary_quadruple
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (atoms : Fin 4 → Fin 6) (slots : Fin 4 → Fin data.basisCount)
    (hbnd : ∀ i, chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight (atoms i) = 0)
    (hmem : ∀ i, atoms i ∈ datumTightSupport data.tightDir
      (data.basisLabel (slots i)))
    (hout : ∀ i k : Fin 4, i < k → atoms i ∉ datumTightSupport data.tightDir
      (data.basisLabel (slots k)))
    (hcount : (data.basisCount : ℝ) < Matrix.trace data.coeff + 4) : False := by
  refine data.false_of_kernel_chain hdiag (fun i => SlotWitness.read (atoms i))
    slots (fun i deadSlot hsrc => absurd hsrc (by simp))
    (fun i deadSlot hsrc => absurd hsrc (by simp)) ?_ ?_
    (fun i atomIndex hsrc => absurd hsrc (by simp))
    (fun i k _ atomIndex hsrc => by simp at hsrc) ?_ ?_ ?_
  · intro i atomIndex hsrc
    have heq : atoms i = atomIndex := by
      have := hsrc
      simpa using this
    rw [← heq]
    exact hbnd i
  · intro i atomIndex hsrc
    have heq : atoms i = atomIndex := by
      have := hsrc
      simpa using this
    rw [← heq]
    exact hmem i
  · intro i k _ deadSlot hsrc
    exact absurd hsrc (by simp)
  · intro i k hik atomIndex hsrc
    have heq : atoms i = atomIndex := by
      have := hsrc
      simpa using this
    rw [← heq]
    exact hout i k hik
  · simpa using hcount

set_option maxHeartbeats 3200000 in
/-- **THE PRIVATE-SLOT DEAD CHAIN.**  The private slot carries only
boundary atoms, thus its axis is a kernel vector.  Two boundary reads
and one residual then make a chain of four.  The chain fires whenever
the basis count is below the trace plus four, in particular at basis
count five and trace two. -/
theorem SharedPrivateData.false_of_private_dead_chain {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    {atomOne atomTwo escapeAtom : Fin 6}
    {slotOne slotTwo escapeSlot : Fin data.basisCount}
    (hbndOne : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne = 0)
    (hbndTwo : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomTwo = 0)
    (hmemOne : atomOne ∈ datumTightSupport data.tightDir
      (data.basisLabel slotOne))
    (hmemTwo : atomTwo ∈ datumTightSupport data.tightDir
      (data.basisLabel slotTwo))
    (hmemEscape : escapeAtom ∈ datumTightSupport data.tightDir
      (data.basisLabel escapeSlot))
    (hslotOne : slotOne ≠ data.privateSlot)
    (hslotTwo : slotTwo ≠ data.privateSlot)
    (hslotEscape : escapeSlot ≠ data.privateSlot)
    (houtTwo : atomOne ∉ datumTightSupport data.tightDir
      (data.basisLabel slotTwo))
    (houtEscapeOne : atomOne ∉ datumTightSupport data.tightDir
      (data.basisLabel escapeSlot))
    (houtEscapeTwo : atomTwo ∉ datumTightSupport data.tightDir
      (data.basisLabel escapeSlot))
    (hcount : (data.basisCount : ℝ) < Matrix.trace data.coeff + 4) : False := by
  classical
  refine data.false_of_kernel_chain hdiag
    ![SlotWitness.dead data.privateSlot, SlotWitness.read atomOne,
      SlotWitness.read atomTwo, SlotWitness.residual escapeAtom]
    ![data.privateSlot, slotOne, slotTwo, escapeSlot]
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i deadSlot hsrc
    fin_cases i <;> simp_all
  · intro i deadSlot hsrc atomIndex hmem
    have heq : deadSlot = data.privateSlot := by
      fin_cases i <;> simp_all
    subst heq
    exact data.boundary_of_private_support hdiag hmem
  · intro i atomIndex hsrc
    fin_cases i <;> simp_all
  · intro i atomIndex hsrc
    fin_cases i <;> simp_all
  · intro i atomIndex hsrc
    fin_cases i <;> simp_all
  · intro i k hik atomIndex
    fin_cases i <;> fin_cases k <;> simp_all
  · intro i k hik deadSlot hsrc
    fin_cases i <;> fin_cases k <;> simp_all
  · intro i k hik atomIndex hsrc
    fin_cases i <;> fin_cases k <;> simp_all
  · simpa using hcount

/-! ## Layer 4 — the double-cover budget -/

set_option maxHeartbeats 3200000 in
/-- **THE DOUBLE-COVER BUDGET.**  Suppose every slot that an interior
atom carries has a second interior carrier.  The dead-slot law puts the
whole trace on the carried slots, the double count reads each of them
twice, and the carrier cap prices each interior atom.  At coefficient
trace two this forces **four interior atoms**. -/
theorem SharedPrivateData.four_le_interior_card_of_double_cover
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2)
    (hdouble : ∀ (slot : Fin data.basisCount) (atomOne : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomOne →
      atomOne ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      ∃ atomTwo : Fin 6, atomTwo ≠ atomOne
        ∧ 0 < chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomTwo
        ∧ atomTwo ∈ datumTightSupport data.tightDir (data.basisLabel slot)) :
    4 ≤ (Finset.univ.filter fun atomIndex =>
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex).card := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsuppFrame, hreadFrame, _hnorm,
    hnz, _hboundary, _hcarrierNz, hspan, hcommute⟩ :=
    data.exists_kernel_read_frame hdiag
  set chartValue := chartObjective (chartPointOfDesign crux.design)
    with hchartValue
  set atomWeight := (chartPointOfDesign crux.design).weight with hatomWeight
  set car : Fin 6 → Finset (Fin data.basisCount) := fun probe =>
    Finset.univ.filter fun slotIdx =>
      probe ∈ datumTightSupport data.tightDir (data.basisLabel slotIdx)
    with hcar
  have hcarmem : ∀ probe slotIdx, slotIdx ∈ car probe ↔
      probe ∈ datumTightSupport data.tightDir (data.basisLabel slotIdx) := by
    intro probe slotIdx
    simp [hcar]
  have hmemActive : ∀ slotIdx, data.basisLabel slotIdx ∈ data.activeSet := by
    intro slotIdx
    have hmem := data.hmem slotIdx
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  have hsupp : ∀ probe, ∀ slotIdx ∉ car probe, readVecs probe slotIdx = 0 := by
    intro probe slotIdx hslot
    exact hsuppFrame probe slotIdx fun hmem =>
      hslot ((hcarmem probe slotIdx).mpr hmem)
  have hread : ∀ probe, ∀ slotIdx ∈ car probe,
      (S *ᵥ readVecs probe) slotIdx
        = (chartValue + atomWeight probe) * readVecs probe slotIdx := by
    intro probe slotIdx hslot
    exact hreadFrame probe slotIdx (datumTightSupport_subset data.hdata
      (hmemActive slotIdx) ((hcarmem probe slotIdx).mp hslot))
  have hnonneg : ∀ probe : Fin 6, 0 ≤ chartValue + atomWeight probe :=
    fun probe => capture_diagonal_nonneg_of_isChartStationaryData data.hdata probe
  have hltOne : ∀ probe : Fin 6, chartValue + atomWeight probe < 1 := by
    intro probe
    have hwle : atomWeight probe ≤ 1 := by
      have hle : atomWeight probe ≤ ∑ y, atomWeight y :=
        Finset.single_le_sum (f := atomWeight)
          (fun y _ => (data.hdata.weight_pos y).le) (Finset.mem_univ probe)
      rwa [data.hdata.weight_sum_one] at hle
    have hneg : chartValue < 0 := data.hvalueNeg
    linarith
  have hsumShift : ∑ probe : Fin 6, (chartValue + atomWeight probe)
      = 6 * chartValue + 1 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, data.hdata.weight_sum_one, nsmul_eq_mul]
    norm_num
  have hpsd := posSemidef_of_transpose_eq_of_idem hSsymm hSidem
  have hdiagNonneg : ∀ slotIdx : Fin data.basisCount, 0 ≤ S slotIdx slotIdx :=
    fun _ => hpsd.diag_nonneg
  set intSet := Finset.univ.filter fun probe =>
    0 < chartValue + atomWeight probe with hintSet
  have hintMem : ∀ probe : Fin 6,
      probe ∈ intSet ↔ 0 < chartValue + atomWeight probe := by
    intro probe
    simp [hintSet]
  -- the dead-slot law
  have hdead : ∀ slotIdx : Fin data.basisCount,
      (∀ probe ∈ intSet, slotIdx ∉ car probe) → S slotIdx slotIdx = 0 := by
    intro slotIdx hnone
    have hzeroCol : S *ᵥ (fun slot => if slot = slotIdx then (1 : ℝ) else 0) = 0 := by
      refine dead_slot_column_of_frame hSsymm hSidem readVecs hcommute hspan
        slotIdx fun probe => ?_
      by_cases hmem : slotIdx ∈ car probe
      · have hnotInt : ¬ 0 < chartValue + atomWeight probe := by
          intro hpos
          exact hnone probe ((hintMem probe).mpr hpos) hmem
        have hzero : chartValue + atomWeight probe = 0 := by
          have hnn := hnonneg probe
          linarith [not_lt.mp hnotInt]
        rw [hread probe slotIdx hmem, hzero, zero_mul, zero_mul]
      · rw [hsupp probe slotIdx hmem, mul_zero]
    have hentry := congrFun hzeroCol slotIdx
    have hexpand : (S *ᵥ fun slot => if slot = slotIdx then (1 : ℝ) else 0) slotIdx
        = S slotIdx slotIdx := by
      calc (S *ᵥ fun slot => if slot = slotIdx then (1 : ℝ) else 0) slotIdx
          = ∑ slot, S slotIdx slot * (if slot = slotIdx then (1 : ℝ) else 0) := rfl
        _ = S slotIdx slotIdx := by
            simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
              Finset.mem_univ, if_true]
    rw [hexpand] at hentry
    simpa using hentry
  -- the trace lives on the slots that the interior atoms carry
  set live := Finset.univ.filter fun slotIdx =>
    ∃ probe ∈ intSet, slotIdx ∈ car probe with hlive
  have htraceLive : Matrix.trace S = ∑ slotIdx ∈ live, S slotIdx slotIdx := by
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin data.basisCount))
      (fun slotIdx => ∃ probe ∈ intSet, slotIdx ∈ car probe)
      (fun slotIdx => S slotIdx slotIdx)
    have hrest : (∑ slotIdx ∈ Finset.univ.filter
        (fun slotIdx => ¬ ∃ probe ∈ intSet, slotIdx ∈ car probe),
        S slotIdx slotIdx) = 0 := by
      refine Finset.sum_eq_zero fun slotIdx hslot => ?_
      have hnot := (Finset.mem_filter.mp hslot).2
      refine hdead slotIdx fun probe hprobe hcarProbe => ?_
      exact hnot ⟨probe, hprobe, hcarProbe⟩
    rw [hrest, add_zero] at hsplit
    rw [Matrix.trace]
    exact hsplit.symm
  -- the double count over the interior atoms
  have hswap : (∑ probe ∈ intSet, ∑ slotIdx ∈ car probe, S slotIdx slotIdx)
      = ∑ slotIdx, ((intSet.filter fun probe => slotIdx ∈ car probe).card : ℝ)
          * S slotIdx slotIdx := by
    have hstep : (∑ probe ∈ intSet, ∑ slotIdx ∈ car probe, S slotIdx slotIdx)
        = ∑ probe ∈ intSet, ∑ slotIdx,
            (if slotIdx ∈ car probe then S slotIdx slotIdx else 0) :=
      Finset.sum_congr rfl fun probe _ => by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl fun slotIdx _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcover : 2 * (∑ slotIdx ∈ live, S slotIdx slotIdx)
      ≤ ∑ probe ∈ intSet, ∑ slotIdx ∈ car probe, S slotIdx slotIdx := by
    rw [hswap]
    have hleft : (∑ slotIdx ∈ live, S slotIdx slotIdx)
        = ∑ slotIdx, (if slotIdx ∈ live then S slotIdx slotIdx else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [hleft, Finset.mul_sum]
    refine Finset.sum_le_sum fun slotIdx _ => ?_
    by_cases hmem : slotIdx ∈ live
    · rw [if_pos hmem]
      obtain ⟨probeOne, hprobeOne, hcarOne⟩ := (Finset.mem_filter.mp hmem).2
      obtain ⟨probeTwo, hne, hposTwo, hmemTwo⟩ :=
        hdouble slotIdx probeOne ((hintMem probeOne).mp hprobeOne)
          ((hcarmem probeOne slotIdx).mp hcarOne)
      have hpairSub : ({probeOne, probeTwo} : Finset (Fin 6))
          ⊆ intSet.filter fun probe => slotIdx ∈ car probe := by
        intro probe hprobe
        rcases Finset.mem_insert.mp hprobe with hcase | hcase
        · rw [hcase]
          exact Finset.mem_filter.mpr ⟨hprobeOne, hcarOne⟩
        · rw [Finset.mem_singleton.mp hcase]
          exact Finset.mem_filter.mpr ⟨(hintMem probeTwo).mpr hposTwo,
            (hcarmem probeTwo slotIdx).mpr hmemTwo⟩
      have hpairCard : ({probeOne, probeTwo} : Finset (Fin 6)).card = 2 :=
        Finset.card_pair (Ne.symm hne)
      have hcard : 2 ≤ (intSet.filter fun probe => slotIdx ∈ car probe).card := by
        have := Finset.card_le_card hpairSub
        omega
      have hcast : (2 : ℝ)
          ≤ ((intSet.filter fun probe => slotIdx ∈ car probe).card : ℝ) := by
        exact_mod_cast hcard
      nlinarith [hdiagNonneg slotIdx, hcast]
    · rw [if_neg hmem, mul_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (hdiagNonneg slotIdx)
  -- the carrier cap prices each interior atom
  have hcap : ∀ probe ∈ intSet, (∑ slotIdx ∈ car probe, S slotIdx slotIdx)
      ≤ Matrix.trace S - 1 + (chartValue + atomWeight probe) := by
    intro probe hprobe
    exact carrier_diag_cap_of_read hSsymm hSidem (hsupp probe) (hread probe)
      (hnz probe) ((hintMem probe).mp hprobe) (hltOne probe)
  have hsumCap : (∑ probe ∈ intSet, ∑ slotIdx ∈ car probe, S slotIdx slotIdx)
      ≤ (intSet.card : ℝ) * (Matrix.trace S - 1)
        + ∑ probe ∈ intSet, (chartValue + atomWeight probe) := by
    have hstep : (∑ probe ∈ intSet, ∑ slotIdx ∈ car probe, S slotIdx slotIdx)
        ≤ ∑ probe ∈ intSet,
            (Matrix.trace S - 1 + (chartValue + atomWeight probe)) :=
      Finset.sum_le_sum hcap
    have hexpand : (∑ probe ∈ intSet,
        (Matrix.trace S - 1 + (chartValue + atomWeight probe)))
        = (intSet.card : ℝ) * (Matrix.trace S - 1)
          + ∑ probe ∈ intSet, (chartValue + atomWeight probe) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith [hstep, hexpand.le, hexpand.ge]
  have hshiftTotal : (∑ probe ∈ intSet, (chartValue + atomWeight probe))
      ≤ 6 * chartValue + 1 := by
    rw [← hsumShift]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ intSet)
      fun probe _ _ => hnonneg probe
  have htraceTwo : Matrix.trace S = 2 := by rw [hStrace, htrace]
  have hneg : chartValue < 0 := data.hvalueNeg
  have hmain : 2 * Matrix.trace S
      ≤ (intSet.card : ℝ) * (Matrix.trace S - 1) + (6 * chartValue + 1) := by
    linarith [htraceLive.le, htraceLive.ge, hcover, hsumCap, hshiftTotal]
  rw [htraceTwo] at hmain
  have hstrict : (3 : ℝ) < (intSet.card : ℝ) := by linarith
  have hnat : 3 < intSet.card := by exact_mod_cast hstrict
  omega

/-- **THE SINGLE-COVER SLOT.**  At coefficient trace two with at most
three interior atoms, some slot has exactly one interior carrier. -/
theorem SharedPrivateData.exists_single_cover_slot {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2)
    (hsmall : (Finset.univ.filter fun atomIndex =>
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex).card ≤ 3) :
    ∃ (slot : Fin data.basisCount) (atomOne : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomOne
        ∧ atomOne ∈ datumTightSupport data.tightDir (data.basisLabel slot)
        ∧ ∀ atomTwo : Fin 6,
            0 < chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomTwo →
            atomTwo ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
            atomTwo = atomOne := by
  classical
  by_contra hnot
  push Not at hnot
  have hfour := data.four_le_interior_card_of_double_cover hdiag htrace ?_
  · omega
  · intro slot atomOne hposOne hmemOne
    obtain ⟨atomTwo, hposTwo, hmemTwo, hne⟩ := hnot slot atomOne hposOne hmemOne
    exact ⟨atomTwo, hne, hposTwo, hmemTwo⟩

/-! ## Layer 5 — the private-slot structure -/

/-- The pin diagonal vanishes: the pin atom is a boundary atom. -/
theorem SharedPrivateData.privateSlot_diag_eq_zero {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) :
    data.coeff data.privateSlot data.privateSlot = 0 := by
  rw [data.hpin]
  exact data.pinAtom_boundary hdiag

/-- **THE INTERIOR ATOMS SIT OFF THE PRIVATE SUPPORT.**  The whole
private support is a boundary set. -/
theorem SharedPrivateData.interior_notMem_privateSupport {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) {atomIndex : Fin 6}
    (hpos : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex) :
    atomIndex ∉ datumTightSupport data.tightDir
      (data.basisLabel data.privateSlot) := by
  intro hmem
  have hzero := data.boundary_of_private_support hdiag hmem
  linarith

/-- **THE INTERIOR COUNT IS AT MOST THREE.**  The interior atoms sit in
the complement of the private support, which carries three atoms. -/
theorem SharedPrivateData.interior_card_le_three {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) :
    (Finset.univ.filter fun atomIndex =>
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex).card ≤ 3 := by
  classical
  set privateSupport := datumTightSupport data.tightDir
    (data.basisLabel data.privateSlot) with hprivateSupport
  have hsub : (Finset.univ.filter fun atomIndex =>
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
      ⊆ privateSupportᶜ := by
    intro atomIndex hatom
    have hpos := (Finset.mem_filter.mp hatom).2
    exact Finset.mem_compl.mpr (data.interior_notMem_privateSupport hdiag hpos)
  have hcompl : privateSupportᶜ.card = 3 := by
    rw [Finset.card_compl, hprivateSupport, data.hthree data.privateSlot,
      Fintype.card_fin]
  have := Finset.card_le_card hsub
  omega

/-- **THE INTERIOR ATOMS ARE THICK.**  A multiplicity-one atom is a
boundary atom, thus every interior atom carries two slots or more. -/
theorem SharedPrivateData.two_le_multiplicity_of_interior {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) {atomIndex : Fin 6}
    (hpos : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex) :
    2 ≤ basisSupportMultiplicity data.tightDir data.basisLabel atomIndex := by
  have hpos' := data.multiplicity_pos atomIndex
  by_contra hlt
  have hone : basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1 := by
    omega
  have hzero := data.boundary_of_multiplicity_one hdiag hone
  linarith

/-! ## Layer 6 — the narrowed basis-count-five residue -/

/-- **THE NARROWED BASIS-COUNT-FIVE RESIDUE.**  A trace-two boundary
datum at basis count five, with the whole structure that the boundary
laws, the interior floor, the interior ceiling and the double-cover
budget supply. -/
def SharedPrivateBoundaryFiveCoreClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (gramDiag : Fin data.basisCount → ℝ),
    data.gram = Matrix.diagonal gramDiag →
    Matrix.trace data.coeff = 2 →
    data.basisCount = 5 →
    data.coeff data.privateSlot data.privateSlot = 0 →
    (∀ atomIndex : Fin 6,
      basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1 →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0) →
    (∀ atomIndex : Fin 6,
      atomIndex ∈ datumTightSupport data.tightDir
        (data.basisLabel data.privateSlot) →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0) →
    (∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex →
      atomIndex ∉ datumTightSupport data.tightDir
        (data.basisLabel data.privateSlot)) →
    (∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex →
      2 ≤ basisSupportMultiplicity data.tightDir data.basisLabel atomIndex) →
    2 ≤ (Finset.univ.filter fun atomIndex =>
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex).card →
    (Finset.univ.filter fun atomIndex =>
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex).card ≤ 3 →
    (∃ (slot : Fin data.basisCount) (atomOne : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomOne
        ∧ atomOne ∈ datumTightSupport data.tightDir (data.basisLabel slot)
        ∧ ∀ atomTwo : Fin 6,
            0 < chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomTwo →
            atomTwo ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
            atomTwo = atomOne) →
    False

/-- **THE CORE DISPATCH.**  The narrowed residue closes the whole
basis-count-five boundary residue: every extra hypothesis is a
theorem. -/
theorem sharedPrivateBoundaryFiveClosed_of_core
    (hcore : SharedPrivateBoundaryFiveCoreClosed) :
    SharedPrivateBoundaryFiveClosed := by
  intro crux data gramDiag hdiag htrace hbasis _hmultOne _hprivate _hcards
    hinterior _atomIndex _hmult _hzero
  exact hcore crux data gramDiag hdiag htrace hbasis
    (data.privateSlot_diag_eq_zero hdiag)
    (fun probe hprobe => data.boundary_of_multiplicity_one hdiag hprobe)
    (fun probe hprobe => data.boundary_of_private_support hdiag hprobe)
    (fun probe hprobe => data.interior_notMem_privateSupport hdiag hprobe)
    (fun probe hprobe => data.two_le_multiplicity_of_interior hdiag hprobe)
    hinterior (data.interior_card_le_three hdiag)
    (data.exists_single_cover_slot hdiag htrace (data.interior_card_le_three hdiag))

/-- The narrowed residue closes the whole trace-two boundary residue. -/
theorem sharedPrivateBoundaryClosed_of_core
    (hcore : SharedPrivateBoundaryFiveCoreClosed) : SharedPrivateBoundaryClosed :=
  sharedPrivateBoundaryClosed_of_five (sharedPrivateBoundaryFiveClosed_of_core hcore)

/-- **THE STRATA DISPATCH.**  The extras residue, the narrowed
basis-count-five residue and the deficit residue close the generic
shared-private kill. -/
theorem sharedPrivateKilled_of_core_strata
    (hextras : SharedPrivateExtrasClosed)
    (hcore : SharedPrivateBoundaryFiveCoreClosed)
    (hdeficit : SharedPrivateDeficitClosed) : SharedPrivateKilled :=
  sharedPrivateKilled_of_five_strata hextras
    (sharedPrivateBoundaryFiveClosed_of_core hcore) hdeficit

/-- The three residues discharge closure two of the rank-four rung. -/
theorem rankFourSharedPrivateClosed_of_core_strata
    (hextras : SharedPrivateExtrasClosed)
    (hcore : SharedPrivateBoundaryFiveCoreClosed)
    (hdeficit : SharedPrivateDeficitClosed) : RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_core_strata hextras hcore hdeficit)

/-- The three residues discharge the shared-private closure of the
rank-five rung. -/
theorem rankFiveSharedPrivateClosed_of_core_strata
    (hextras : SharedPrivateExtrasClosed)
    (hcore : SharedPrivateBoundaryFiveCoreClosed)
    (hdeficit : SharedPrivateDeficitClosed) : RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_core_strata hextras hcore hdeficit)

/-- The three residues discharge the shared-private closure of the
rank-six rung. -/
theorem rankSixSharedPrivateClosed_of_core_strata
    (hextras : SharedPrivateExtrasClosed)
    (hcore : SharedPrivateBoundaryFiveCoreClosed)
    (hdeficit : SharedPrivateDeficitClosed) : RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_core_strata hextras hcore hdeficit)

end Gtz
