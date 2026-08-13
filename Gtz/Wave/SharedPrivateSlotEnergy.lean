import Gtz.Wave.SharedPrivateReadIntertwiner

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The shared-private slot energy — the multiplicity-one boundary law and
the rank-four complement kill

The read frame carries a commutation law: the read Gram commutes with the
read idempotent.  Read at one slot against itself, the law becomes an
energy identity.  The fixed energy of the reads at a slot equals the
shifted-weight total of the reads at that slot.  The identity has a
Cauchy-Schwarz cap on one side and a single-term floor on the other, and
at a multiplicity-one atom the two cross.

The slot energy identity.  For each slot the fixed parts of the reads
carry the same energy at that slot as the shifted weights do.  The proof
takes the kernel invariance at the complementary column of the slot.

The cap.  Each fixed part is orthogonal to the kernel, thus its slot
entry is its own dot product against the slot column of the idempotent.
Cauchy-Schwarz caps the entry by the fixed energy times the diagonal.
The total fixed energy is the shifted-weight total divided by six.

**THE MULTIPLICITY-ONE BOUNDARY LAW.**  At a one-slot atom the read is a
multiple of one axis, its square norm is one sixth, and the diagonal of
the idempotent reads the shifted weight.  The identity then says that one
sixth of the shifted weight is at most the shifted-weight total over six
times the same shifted weight.  A positive shifted weight makes the chart
value nonnegative, and the chart value is negative.  Thus **every atom of
multiplicity one sits at the shifted-weight boundary.**

The propagation.  A boundary atom of multiplicity one puts its own slot
axis in the kernel of the idempotent.  Every atom of that slot then reads
zero at that slot, and its carrier entry is nonzero, thus its shifted
weight vanishes too.  **Every atom of the private support sits at the
boundary**, because the pin atom has multiplicity one and sits there.

The rank-four complement kill.  The narrowed rank-four residue carries a
slot whose support is the complement of the private support.  The
propagation makes the private support wholly boundary.  Then a triangular
family of three boundary reads always exists, and the trace floor caps a
kernel-fixed independent family at the complement trace, which is two.
**The residue is closed unconditionally.**

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.dotProduct_sq_le_mul` — Cauchy-Schwarz for the dot product.
* `Gtz.gram_kernel_entry` — **THE SLOT ENERGY IDENTITY.**
* `Gtz.slot_fixed_energy_le` — **THE SLOT ENERGY CAP.**
* `Gtz.SharedPrivateData.boundary_of_multiplicity_one` — **THE
  MULTIPLICITY-ONE BOUNDARY LAW.**
* `Gtz.SharedPrivateData.boundary_of_pin_cocarrier` — **THE PIN-SLOT
  PROPAGATION.**
* `Gtz.SharedPrivateData.boundary_of_private_support`,
  `Gtz.SharedPrivateData.pinAtom_boundary` — the private-support corollaries.
* `Gtz.SharedPrivateData.false_of_triangular_boundary_triple` — **THE
  TRIANGULAR TRIPLE KILL.**
* `Gtz.sharedPrivateComplementSlotClosed`,
  `Gtz.sharedPrivateBoundaryFourClosed` — **THE RANK-FOUR RESIDUES ARE
  CLOSED.**
* `Gtz.SharedPrivateBoundaryFiveClosed` with
  `Gtz.sharedPrivateBoundaryHighClosed_of_five` — the high residue
  narrows to basis count five with the two boundary laws.
* `Gtz.sharedPrivateBoundaryClosed_of_five`,
  `Gtz.sharedPrivateKilled_of_five_strata` — the dispatches.
* `Gtz.rankFourSharedPrivateClosed_of_five_strata`,
  `Gtz.rankFiveSharedPrivateClosed_of_five_strata`,
  `Gtz.rankSixSharedPrivateClosed_of_five_strata` — the rung
  compositions.

## Vacuity

The matrix statements are unconditional.  The datum statements quantify
over shared-private data, and no datum exists if `Gtz.GtzWeighted 6 3`
holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — Cauchy-Schwarz and the slot energy laws -/

/-- **THE SLOT ENERGY IDENTITY.**  A family whose Gram commutes with a
symmetric idempotent carries, at every pair of slots, the same fixed
cross energy as the mixed cross energy.  The kernel invariance is read at
the complementary column of the second slot. -/
theorem gram_kernel_entry {m n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (V : Fin m → Fin n → ℝ)
    (hcomm : ∀ rowSlot colSlot : Fin n,
      (∑ i, V i rowSlot * (S *ᵥ V i) colSlot)
        = ∑ i, (S *ᵥ V i) rowSlot * V i colSlot)
    (rowSlot colSlot : Fin n) :
    (∑ i, (S *ᵥ V i) rowSlot * (S *ᵥ V i) colSlot)
      = ∑ i, (S *ᵥ V i) rowSlot * V i colSlot := by
  classical
  set probe : Fin n → ℝ := fun slot =>
    (if slot = colSlot then (1 : ℝ) else 0) - S slot colSlot with hprobe
  have hsymmEntry : ∀ rowIdx colIdx : Fin n, S colIdx rowIdx = S rowIdx colIdx := by
    intro rowIdx colIdx
    have hentry := congrFun (congrFun hsymm rowIdx) colIdx
    rwa [Matrix.transpose_apply] at hentry
  have hSprobe : S *ᵥ probe = 0 := by
    funext rowIdx
    have hexpand : (S *ᵥ probe) rowIdx
        = (∑ slot, S rowIdx slot * (if slot = colSlot then (1 : ℝ) else 0))
          - ∑ slot, S rowIdx slot * S slot colSlot := by
      rw [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun slot _ => by rw [hprobe]; ring
    have hfirst : (∑ slot, S rowIdx slot * (if slot = colSlot then (1 : ℝ) else 0))
        = S rowIdx colSlot := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    have hsecond : (∑ slot, S rowIdx slot * S slot colSlot) = S rowIdx colSlot := by
      have hentry := congrFun (congrFun hidem rowIdx) colSlot
      rwa [Matrix.mul_apply] at hentry
    show (S *ᵥ probe) rowIdx = (0 : ℝ)
    rw [hexpand, hfirst, hsecond, sub_self]
  have hdot : ∀ i : Fin m,
      V i ⬝ᵥ probe = V i colSlot - (S *ᵥ V i) colSlot := by
    intro i
    have hexpand : V i ⬝ᵥ probe
        = (∑ slot, V i slot * (if slot = colSlot then (1 : ℝ) else 0))
          - ∑ slot, V i slot * S slot colSlot := by
      rw [dotProduct, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun slot _ => by rw [hprobe]; ring
    have hfirst : (∑ slot, V i slot * (if slot = colSlot then (1 : ℝ) else 0))
        = V i colSlot := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    have hsecond : (∑ slot, V i slot * S slot colSlot)
        = (S *ᵥ V i) colSlot := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun slot _ => ?_
      rw [hsymmEntry slot colSlot]
      ring
    rw [hexpand, hfirst, hsecond]
  have hrel := gram_kernel_invariant hsymm V hcomm hSprobe rowSlot
  have hsplit : (∑ i, (V i ⬝ᵥ probe) * (S *ᵥ V i) rowSlot)
      = (∑ i, (S *ᵥ V i) rowSlot * V i colSlot)
        - ∑ i, (S *ᵥ V i) rowSlot * (S *ᵥ V i) colSlot := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hdot i]; ring
  rw [hsplit] at hrel
  linarith

/-- **THE SLOT ENERGY CAP.**  The fixed energy of a family at one slot is
capped by the total fixed energy times the diagonal of the idempotent at
that slot.  Each fixed part is its own dot product against the slot
column, and Cauchy-Schwarz gives the cap. -/
theorem slot_fixed_energy_le {m n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (V : Fin m → Fin n → ℝ)
    (slot : Fin n) :
    (∑ i, (S *ᵥ V i) slot * (S *ᵥ V i) slot)
      ≤ (∑ i, (S *ᵥ V i) ⬝ᵥ (S *ᵥ V i)) * S slot slot := by
  classical
  have hsymmEntry : ∀ rowIdx colIdx : Fin n, S colIdx rowIdx = S rowIdx colIdx := by
    intro rowIdx colIdx
    have hentry := congrFun (congrFun hsymm rowIdx) colIdx
    rwa [Matrix.transpose_apply] at hentry
  have hentryEq : ∀ vec : Fin n → ℝ,
      (S *ᵥ vec) ⬝ᵥ (fun rowIdx => S rowIdx slot) = (S *ᵥ vec) slot := by
    intro vec
    calc (S *ᵥ vec) ⬝ᵥ (fun rowIdx => S rowIdx slot)
        = ∑ rowIdx, (S *ᵥ vec) rowIdx * S rowIdx slot := rfl
      _ = ∑ rowIdx, S slot rowIdx * (S *ᵥ vec) rowIdx :=
          Finset.sum_congr rfl fun rowIdx _ => by
            rw [hsymmEntry rowIdx slot]; ring
      _ = (S *ᵥ (S *ᵥ vec)) slot := rfl
      _ = (S *ᵥ vec) slot := by rw [Matrix.mulVec_mulVec, hidem]
  have hcolumnNorm : (fun rowIdx => S rowIdx slot) ⬝ᵥ (fun rowIdx => S rowIdx slot)
      = S slot slot := by
    have hentry := congrFun (congrFun hidem slot) slot
    rw [Matrix.mul_apply] at hentry
    calc (fun rowIdx => S rowIdx slot) ⬝ᵥ (fun rowIdx => S rowIdx slot)
        = ∑ rowIdx, S rowIdx slot * S rowIdx slot := rfl
      _ = ∑ rowIdx, S slot rowIdx * S rowIdx slot :=
          Finset.sum_congr rfl fun rowIdx _ => by rw [hsymmEntry rowIdx slot]
      _ = S slot slot := hentry
  have hterm : ∀ i : Fin m,
      (S *ᵥ V i) slot * (S *ᵥ V i) slot
        ≤ ((S *ᵥ V i) ⬝ᵥ (S *ᵥ V i)) * S slot slot := by
    intro i
    have hcs := dotProduct_sq_le_mul (S *ᵥ V i) (fun rowIdx => S rowIdx slot)
    rw [hentryEq (V i), hcolumnNorm] at hcs
    calc (S *ᵥ V i) slot * (S *ᵥ V i) slot = ((S *ᵥ V i) slot) ^ 2 := by ring
      _ ≤ ((S *ᵥ V i) ⬝ᵥ (S *ᵥ V i)) * S slot slot := hcs
  calc (∑ i, (S *ᵥ V i) slot * (S *ᵥ V i) slot)
      ≤ ∑ i, ((S *ᵥ V i) ⬝ᵥ (S *ᵥ V i)) * S slot slot :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, (S *ᵥ V i) ⬝ᵥ (S *ᵥ V i)) * S slot slot := by
        rw [← Finset.sum_mul]

/-! ## Layer 2 — the multiplicity-one boundary law -/

set_option maxHeartbeats 3200000 in
/-- **THE MULTIPLICITY-ONE BOUNDARY LAW.**  Every atom that carries one
basis slot sits at the shifted-weight boundary.  The slot energy identity
gives the shifted weight of the atom over six on one side, and the slot
energy cap gives the shifted-weight total over six times the same shifted
weight on the other.  A positive shifted weight would make the chart
value nonnegative. -/
theorem SharedPrivateData.boundary_of_multiplicity_one {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) {atomIndex : Fin 6}
    (hmult : basisSupportMultiplicity data.tightDir data.basisLabel
      atomIndex = 1) :
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex = 0 := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, _hStrace, hsuppFrame, hreadFrame, hnorm,
    hnz, _hboundary, _hcarrierNz, _hspan, hcommute⟩ :=
    data.exists_kernel_read_frame hdiag
  set chartValue := chartObjective (chartPointOfDesign crux.design)
    with hchartValue
  set atomWeight := (chartPointOfDesign crux.design).weight with hatomWeight
  set car : Fin 6 → Finset (Fin data.basisCount) := fun probe =>
    Finset.univ.filter fun slot =>
      probe ∈ datumTightSupport data.tightDir (data.basisLabel slot)
    with hcar
  have hcarmem : ∀ probe slot, slot ∈ car probe ↔
      probe ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
    intro probe slot
    simp [hcar]
  have hcarCard : ∀ probe, (car probe).card
      = basisSupportMultiplicity data.tightDir data.basisLabel probe :=
    fun _ => rfl
  have hmemActive : ∀ slot, data.basisLabel slot ∈ data.activeSet := by
    intro slot
    have hmem := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  have hsupp : ∀ probe, ∀ slot ∉ car probe, readVecs probe slot = 0 := by
    intro probe slot hslot
    exact hsuppFrame probe slot fun hmem =>
      hslot ((hcarmem probe slot).mpr hmem)
  have hread : ∀ probe, ∀ slot ∈ car probe,
      (S *ᵥ readVecs probe) slot
        = (chartValue + atomWeight probe) * readVecs probe slot := by
    intro probe slot hslot
    exact hreadFrame probe slot (datumTightSupport_subset data.hdata
      (hmemActive slot) ((hcarmem probe slot).mp hslot))
  obtain ⟨pinSlot, hpinSlot⟩ :=
    Finset.card_eq_one.mp ((hcarCard atomIndex).trans hmult)
  -- the shifted weights are nonnegative and total `6 * value + 1`
  have hnonneg : ∀ probe : Fin 6, 0 ≤ chartValue + atomWeight probe :=
    fun probe => capture_diagonal_nonneg_of_isChartStationaryData data.hdata probe
  have hsumShift : ∑ probe : Fin 6, (chartValue + atomWeight probe)
      = 6 * chartValue + 1 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, data.hdata.weight_sum_one, nsmul_eq_mul]
    norm_num
  -- the total fixed energy is the shifted total over six
  have hfixEnergy : ∀ probe : Fin 6,
      (S *ᵥ readVecs probe) ⬝ᵥ (S *ᵥ readVecs probe)
        = (chartValue + atomWeight probe) * (6 : ℝ)⁻¹ := by
    intro probe
    rw [read_fixed_self_energy hSsymm hSidem (hsupp probe) (hread probe),
      hnorm probe]
  have hsumFix : (∑ probe : Fin 6,
      (S *ᵥ readVecs probe) ⬝ᵥ (S *ᵥ readVecs probe))
      = (6 * chartValue + 1) * (6 : ℝ)⁻¹ := by
    have hstep : (∑ probe : Fin 6,
        (S *ᵥ readVecs probe) ⬝ᵥ (S *ᵥ readVecs probe))
        = ∑ probe : Fin 6, (chartValue + atomWeight probe) * (6 : ℝ)⁻¹ :=
      Finset.sum_congr rfl fun probe _ => hfixEnergy probe
    rw [hstep, ← Finset.sum_mul, hsumShift]
  -- the diagonal at the pinned slot reads the shifted weight
  have hdiagPin : S pinSlot pinSlot = chartValue + atomWeight atomIndex :=
    pin_diag_eq_of_read (hsupp atomIndex) (hread atomIndex) (hnz atomIndex)
      hpinSlot
  -- the slot energy identity at the pinned slot
  have hidentity : (∑ probe : Fin 6,
      (S *ᵥ readVecs probe) pinSlot * (S *ᵥ readVecs probe) pinSlot)
      = ∑ probe : Fin 6,
        (S *ᵥ readVecs probe) pinSlot * readVecs probe pinSlot :=
    gram_kernel_entry hSsymm hSidem readVecs hcommute pinSlot pinSlot
  have hright : ∀ probe : Fin 6,
      (S *ᵥ readVecs probe) pinSlot * readVecs probe pinSlot
        = (chartValue + atomWeight probe)
          * (readVecs probe pinSlot * readVecs probe pinSlot) := by
    intro probe
    by_cases hmem : pinSlot ∈ car probe
    · rw [hread probe pinSlot hmem]
      ring
    · rw [hsupp probe pinSlot hmem]
      ring
  -- the read of the one-slot atom carries the whole square norm
  have hpinNorm : readVecs atomIndex pinSlot * readVecs atomIndex pinSlot
      = (6 : ℝ)⁻¹ := by
    have hnormAtom := hnorm atomIndex
    rw [dotProduct] at hnormAtom
    have hcollapse : (∑ slot : Fin data.basisCount,
        readVecs atomIndex slot * readVecs atomIndex slot)
        = readVecs atomIndex pinSlot * readVecs atomIndex pinSlot := by
      refine Finset.sum_eq_single pinSlot (fun slot _ hne => ?_)
        (fun hnot => absurd (Finset.mem_univ pinSlot) hnot)
      rw [hsupp atomIndex slot (by rw [hpinSlot]; simpa using hne), zero_mul]
    rw [← hcollapse, hnormAtom]
  -- the floor from the single term
  have hnonnegTerm : ∀ probe ∈ (Finset.univ : Finset (Fin 6)),
      0 ≤ (chartValue + atomWeight probe)
        * (readVecs probe pinSlot * readVecs probe pinSlot) :=
    fun probe _ => mul_nonneg (hnonneg probe) (mul_self_nonneg _)
  have hsingle := Finset.single_le_sum hnonnegTerm (Finset.mem_univ atomIndex)
  rw [hpinNorm] at hsingle
  have hrightSum : (∑ probe : Fin 6,
      (S *ᵥ readVecs probe) pinSlot * readVecs probe pinSlot)
      = ∑ probe : Fin 6, (chartValue + atomWeight probe)
          * (readVecs probe pinSlot * readVecs probe pinSlot) :=
    Finset.sum_congr rfl fun probe _ => hright probe
  -- the cap from Cauchy-Schwarz
  have hupper := slot_fixed_energy_le hSsymm hSidem readVecs pinSlot
  rw [hsumFix, hdiagPin] at hupper
  rw [hidentity, hrightSum] at hupper
  have hneg : chartValue < 0 := data.hvalueNeg
  have hge := hnonneg atomIndex
  nlinarith [hsingle, hupper, hneg, hge]

/-- **THE PIN-SLOT PROPAGATION.**  A slot whose support carries an atom
of multiplicity one puts its own axis in the kernel of the read
idempotent.  Every atom of that support then sits at the
shifted-weight boundary. -/
theorem SharedPrivateData.boundary_of_pin_cocarrier {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    {pinIndex atomIndex : Fin 6} {slot : Fin data.basisCount}
    (hmult : basisSupportMultiplicity data.tightDir data.basisLabel
      pinIndex = 1)
    (hpinMem : pinIndex ∈ datumTightSupport data.tightDir
      (data.basisLabel slot))
    (hatomMem : atomIndex ∈ datumTightSupport data.tightDir
      (data.basisLabel slot)) :
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex = 0 := by
  classical
  have hpinZero := data.boundary_of_multiplicity_one hdiag hmult
  obtain ⟨S, readVecs, hSsymm, _hSidem, _hStrace, hsuppFrame, hreadFrame, _hnorm,
    _hnz, hboundary, hcarrierNz, _hspan, _hcommute⟩ :=
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
  have hcarCard : ∀ probe, (car probe).card
      = basisSupportMultiplicity data.tightDir data.basisLabel probe :=
    fun _ => rfl
  have hmemActive : ∀ slotIdx, data.basisLabel slotIdx ∈ data.activeSet := by
    intro slotIdx
    have hmem := data.hmem slotIdx
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  -- the pinned atom carries the single slot
  obtain ⟨uniqueSlot, huniq⟩ :=
    Finset.card_eq_one.mp ((hcarCard pinIndex).trans hmult)
  have hslotEq : slot = uniqueSlot := by
    have hmem : slot ∈ car pinIndex := (hcarmem pinIndex slot).mpr hpinMem
    rw [huniq] at hmem
    simpa using hmem
  have hcarPin : car pinIndex = {slot} := by rw [huniq, hslotEq]
  have hpinSupp : ∀ slotIdx, slotIdx ≠ slot → readVecs pinIndex slotIdx = 0 := by
    intro slotIdx hne
    refine hsuppFrame pinIndex slotIdx fun hmem => ?_
    have hmemCar : slotIdx ∈ car pinIndex := (hcarmem pinIndex slotIdx).mpr hmem
    rw [hcarPin] at hmemCar
    exact hne (by simpa using hmemCar)
  have hpinNz : readVecs pinIndex slot ≠ 0 := hcarrierNz pinIndex slot hpinMem
  have hpinKernel : S *ᵥ readVecs pinIndex = 0 := hboundary pinIndex hpinZero
  -- every fixed part vanishes at the slot
  have hswap : ∀ leftVec rightVec : Fin data.basisCount → ℝ,
      (S *ᵥ leftVec) ⬝ᵥ rightVec = leftVec ⬝ᵥ (S *ᵥ rightVec) := by
    intro leftVec rightVec
    rw [Matrix.dotProduct_mulVec]
    congr 1
    conv_rhs => rw [← hSsymm]
    rw [Matrix.vecMul_transpose]
  have hfixZero : ∀ probe : Fin 6, (S *ᵥ readVecs probe) slot = 0 := by
    intro probe
    have hcollapse : (S *ᵥ readVecs probe) ⬝ᵥ readVecs pinIndex
        = (S *ᵥ readVecs probe) slot * readVecs pinIndex slot := by
      rw [dotProduct]
      refine Finset.sum_eq_single slot (fun slotIdx _ hne => ?_)
        (fun hnot => absurd (Finset.mem_univ slot) hnot)
      rw [hpinSupp slotIdx hne, mul_zero]
    have hzero : (S *ᵥ readVecs probe) ⬝ᵥ readVecs pinIndex = 0 := by
      rw [hswap, hpinKernel, dotProduct_zero]
    rw [hcollapse] at hzero
    rcases mul_eq_zero.mp hzero with hcase | hcase
    · exact hcase
    · exact absurd hcase hpinNz
  -- the read at the atom then forces the shifted weight to vanish
  have hreadAtom := hreadFrame atomIndex slot (datumTightSupport_subset data.hdata
    (hmemActive slot) hatomMem)
  rw [hfixZero atomIndex] at hreadAtom
  rcases mul_eq_zero.mp hreadAtom.symm with hcase | hcase
  · exact hcase
  · exact absurd hcase (hcarrierNz atomIndex slot hatomMem)

/-- The pin atom of a datum sits at the shifted-weight boundary. -/
theorem SharedPrivateData.pinAtom_boundary {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) :
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight data.pinAtom = 0 :=
  data.boundary_of_multiplicity_one hdiag data.hmultOne

/-- **THE PRIVATE SUPPORT IS BOUNDARY.**  Every atom of the private
support sits at the shifted-weight boundary, because the pin atom has
multiplicity one and sits in that support. -/
theorem SharedPrivateData.boundary_of_private_support {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) {atomIndex : Fin 6}
    (hmem : atomIndex ∈ datumTightSupport data.tightDir
      (data.basisLabel data.privateSlot)) :
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex = 0 :=
  data.boundary_of_pin_cocarrier hdiag data.hmultOne
    (mem_datumTightSupport.mpr data.hpinNe) hmem

set_option maxHeartbeats 3200000 in
/-- **THE DEAD-SLOT LAW AND THE INTERIOR FLOOR.**  A slot that no
interior atom carries has a vanishing diagonal: the slot energy identity
makes every fixed part vanish at that slot, and the span law then kills
the whole column.  Thus the coefficient trace is the diagonal total over
the slots that the interior atoms carry, the carrier cap prices that
total by the interior atoms, and **at least two atoms are interior.** -/
theorem SharedPrivateData.two_le_interior_card {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) :
    2 ≤ (Finset.univ.filter fun atomIndex =>
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
      have hsumOne := data.hdata.weight_sum_one
      have hle : atomWeight probe ≤ ∑ y, atomWeight y :=
        Finset.single_le_sum (f := atomWeight)
          (fun y _ => (data.hdata.weight_pos y).le) (Finset.mem_univ probe)
      rwa [hsumOne] at hle
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
    have hidentity :=
      gram_kernel_entry hSsymm hSidem readVecs hcommute slotIdx slotIdx
    have hzeroTerm : ∀ probe : Fin 6,
        (S *ᵥ readVecs probe) slotIdx * readVecs probe slotIdx = 0 := by
      intro probe
      by_cases hmem : slotIdx ∈ car probe
      · have hnotInt : ¬ 0 < chartValue + atomWeight probe := by
          intro hpos
          exact hnone probe ((hintMem probe).mpr hpos) hmem
        have hzero : chartValue + atomWeight probe = 0 := by
          have hnn := hnonneg probe
          linarith [not_lt.mp hnotInt]
        rw [hread probe slotIdx hmem, hzero, zero_mul, zero_mul]
      · rw [hsupp probe slotIdx hmem, mul_zero]
    have hsumZero : (∑ probe : Fin 6, (S *ᵥ readVecs probe) slotIdx
        * (S *ᵥ readVecs probe) slotIdx) = 0 := by
      rw [hidentity]
      exact Finset.sum_eq_zero fun probe _ => hzeroTerm probe
    have hEach : ∀ probe : Fin 6, (S *ᵥ readVecs probe) slotIdx = 0 := by
      intro probe
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun q (_ : q ∈ (Finset.univ : Finset (Fin 6))) =>
          mul_self_nonneg ((S *ᵥ readVecs q) slotIdx))).mp hsumZero probe
        (Finset.mem_univ probe)
      exact mul_self_eq_zero.mp hterm
    have hsymmEntry : ∀ rowIdx colIdx : Fin data.basisCount,
        S colIdx rowIdx = S rowIdx colIdx := by
      intro rowIdx colIdx
      have hentry := congrFun (congrFun hSsymm rowIdx) colIdx
      rwa [Matrix.transpose_apply] at hentry
    have hcol : (fun rowIdx => S rowIdx slotIdx) = 0 := by
      refine hspan _ fun probe => ?_
      calc readVecs probe ⬝ᵥ (fun rowIdx => S rowIdx slotIdx)
          = ∑ rowIdx, readVecs probe rowIdx * S rowIdx slotIdx := rfl
        _ = ∑ rowIdx, S slotIdx rowIdx * readVecs probe rowIdx :=
            Finset.sum_congr rfl fun rowIdx _ => by
              rw [hsymmEntry rowIdx slotIdx]; ring
        _ = (S *ᵥ readVecs probe) slotIdx := rfl
        _ = 0 := hEach probe
    have hentry := congrFun hcol slotIdx
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
  have hcover : (∑ slotIdx ∈ live, S slotIdx slotIdx)
      ≤ ∑ probe ∈ intSet, ∑ slotIdx ∈ car probe, S slotIdx slotIdx := by
    rw [hswap]
    have hleft : (∑ slotIdx ∈ live, S slotIdx slotIdx)
        = ∑ slotIdx, (if slotIdx ∈ live then S slotIdx slotIdx else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [hleft]
    refine Finset.sum_le_sum fun slotIdx _ => ?_
    by_cases hmem : slotIdx ∈ live
    · rw [if_pos hmem]
      have hne : (intSet.filter fun probe => slotIdx ∈ car probe).Nonempty := by
        have hexists := (Finset.mem_filter.mp hmem).2
        obtain ⟨probe, hprobe, hcarProbe⟩ := hexists
        exact ⟨probe, Finset.mem_filter.mpr ⟨hprobe, hcarProbe⟩⟩
      have hcard : 1 ≤ (intSet.filter fun probe => slotIdx ∈ car probe).card :=
        Finset.card_pos.mpr hne
      have hcast : (1 : ℝ)
          ≤ ((intSet.filter fun probe => slotIdx ∈ car probe).card : ℝ) := by
        exact_mod_cast hcard
      nlinarith [hdiagNonneg slotIdx, hcast]
    · rw [if_neg hmem]
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
  -- the trace disjunction closes the count
  have htraceTwoOrThree : Matrix.trace S = 2 ∨ Matrix.trace S = 3 := by
    rcases data.htrace with htwo | hthree
    · exact Or.inl (by rw [hStrace, htwo])
    · exact Or.inr (by rw [hStrace, hthree])
  have hneg : chartValue < 0 := data.hvalueNeg
  have hmain : Matrix.trace S
      ≤ (intSet.card : ℝ) * (Matrix.trace S - 1) + (6 * chartValue + 1) := by
    linarith [htraceLive.le, htraceLive.ge, hcover, hsumCap, hshiftTotal]
  have hstrict : (1 : ℝ) < (intSet.card : ℝ) := by
    rcases htraceTwoOrThree with htwo | hthree
    · rw [htwo] at hmain
      linarith
    · rw [hthree] at hmain
      linarith
  have hnat : 1 < intSet.card := by exact_mod_cast hstrict
  omega

/-! ## Layer 3 — the triangular triple kill -/

set_option maxHeartbeats 1600000 in
/-- **THE TRIANGULAR TRIPLE KILL.**  Three boundary atoms with a
triangular slot pattern give three independent kernel-fixed reads, and
the trace floor caps such a family by the complement trace. -/
theorem SharedPrivateData.false_of_triangular_boundary_triple
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    {atomZero atomOne atomTwo : Fin 6}
    {slotZero slotOne slotTwo : Fin data.basisCount}
    (hbndZero : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomZero = 0)
    (hbndOne : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne = 0)
    (hbndTwo : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomTwo = 0)
    (hzeroIn : atomZero ∈ datumTightSupport data.tightDir
      (data.basisLabel slotZero))
    (honeIn : atomOne ∈ datumTightSupport data.tightDir
      (data.basisLabel slotOne))
    (hzeroOutOne : atomZero ∉ datumTightSupport data.tightDir
      (data.basisLabel slotOne))
    (htwoIn : atomTwo ∈ datumTightSupport data.tightDir
      (data.basisLabel slotTwo))
    (hzeroOutTwo : atomZero ∉ datumTightSupport data.tightDir
      (data.basisLabel slotTwo))
    (honeOutTwo : atomOne ∉ datumTightSupport data.tightDir
      (data.basisLabel slotTwo))
    (hcount : (data.basisCount : ℝ) < Matrix.trace data.coeff + 3) : False := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsuppFrame, _hreadFrame, _hnorm,
    _hnz, hboundary, hcarrierNz, _hspan, _hcommute⟩ :=
    data.exists_kernel_read_frame hdiag
  set family : Fin 3 → Fin data.basisCount → ℝ :=
    ![readVecs atomZero, readVecs atomOne, readVecs atomTwo] with hfamily
  have hcomplSymm : ((1 : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ)
      - S)ᵀ = 1 - S := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hSsymm]
  have hcomplIdem : ((1 : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ)
      - S) * (1 - S) = 1 - S := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      hSidem]
    abel
  have hfix : ∀ i : Fin 3,
      ((1 : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ) - S) *ᵥ family i
        = family i := by
    intro i
    have hstep : ∀ probe : Fin 6,
        chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight probe = 0 →
        ((1 : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ) - S)
            *ᵥ readVecs probe = readVecs probe := by
      intro probe hzero
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hboundary probe hzero, sub_zero]
    fin_cases i
    · exact hstep atomZero hbndZero
    · exact hstep atomOne hbndOne
    · exact hstep atomTwo hbndTwo
  -- the triangular elimination gives independence
  have hind : ∀ coeffVec : Fin 3 → ℝ,
      (∀ slot, ∑ i, coeffVec i * family i slot = 0) → coeffVec = 0 := by
    intro coeffVec hzero
    have hzeroOneSlot : readVecs atomZero slotOne = 0 :=
      hsuppFrame atomZero slotOne hzeroOutOne
    have hzeroTwoSlot : readVecs atomZero slotTwo = 0 :=
      hsuppFrame atomZero slotTwo hzeroOutTwo
    have honeTwoSlot : readVecs atomOne slotTwo = 0 :=
      hsuppFrame atomOne slotTwo honeOutTwo
    have hrowTwo := hzero slotTwo
    rw [Fin.sum_univ_three] at hrowTwo
    simp only [hfamily, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hrowTwo
    rw [hzeroTwoSlot, honeTwoSlot] at hrowTwo
    have hcoeffTwo : coeffVec 2 = 0 := by
      have hne : readVecs atomTwo slotTwo ≠ 0 :=
        hcarrierNz atomTwo slotTwo htwoIn
      have hprod : coeffVec 2 * readVecs atomTwo slotTwo = 0 := by linarith
      rcases mul_eq_zero.mp hprod with hcase | hcase
      · exact hcase
      · exact absurd hcase hne
    have hrowOne := hzero slotOne
    rw [Fin.sum_univ_three] at hrowOne
    simp only [hfamily, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hrowOne
    rw [hzeroOneSlot, hcoeffTwo] at hrowOne
    have hcoeffOne : coeffVec 1 = 0 := by
      have hne : readVecs atomOne slotOne ≠ 0 :=
        hcarrierNz atomOne slotOne honeIn
      have hprod : coeffVec 1 * readVecs atomOne slotOne = 0 := by linarith
      rcases mul_eq_zero.mp hprod with hcase | hcase
      · exact hcase
      · exact absurd hcase hne
    have hrowZero := hzero slotZero
    rw [Fin.sum_univ_three] at hrowZero
    simp only [hfamily, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hrowZero
    rw [hcoeffOne, hcoeffTwo] at hrowZero
    have hcoeffZero : coeffVec 0 = 0 := by
      have hne : readVecs atomZero slotZero ≠ 0 :=
        hcarrierNz atomZero slotZero hzeroIn
      have hprod : coeffVec 0 * readVecs atomZero slotZero = 0 := by linarith
      rcases mul_eq_zero.mp hprod with hcase | hcase
      · exact hcase
      · exact absurd hcase hne
    funext i
    fin_cases i
    · exact hcoeffZero
    · exact hcoeffOne
    · exact hcoeffTwo
  have hker := gram_kernel_free_of_independent family hind
  have hfloor := trace_floor_of_fixed_family hcomplSymm hcomplIdem family hfix hker
  have htraceCompl : Matrix.trace ((1 : Matrix (Fin data.basisCount)
      (Fin data.basisCount) ℝ) - S)
      = (data.basisCount : ℝ) - Matrix.trace data.coeff := by
    rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, hStrace]
  rw [htraceCompl] at hfloor
  norm_num at hfloor
  linarith

/-! ## Layer 4 — the rank-four complement residue is closed -/

set_option maxHeartbeats 3200000 in
/-- **THE RANK-FOUR COMPLEMENT KILL.**  The narrowed rank-four residue is
closed with no hypothesis.  The private support is wholly boundary, and
every remaining shape supplies a triangular boundary triple or makes
every atom a boundary atom. -/
theorem sharedPrivateComplementSlotClosed : SharedPrivateComplementSlotClosed := by
  intro crux data gramDiag hdiag htrace hbasis hexact hbnd _hcards hcompl
  classical
  obtain ⟨complSlot, hcomplNe, hcomplSupp⟩ := hcompl
  set mult := basisSupportMultiplicity data.tightDir data.basisLabel with hmultDef
  set privateSupport := datumTightSupport data.tightDir
    (data.basisLabel data.privateSlot) with hprivateSupport
  set car : Fin 6 → Finset (Fin data.basisCount) := fun probe =>
    Finset.univ.filter fun slotIdx =>
      probe ∈ datumTightSupport data.tightDir (data.basisLabel slotIdx)
    with hcar
  have hcarmem : ∀ probe slotIdx, slotIdx ∈ car probe ↔
      probe ∈ datumTightSupport data.tightDir (data.basisLabel slotIdx) := by
    intro probe slotIdx
    simp [hcar]
  have hcarCard : ∀ probe, (car probe).card = mult probe := fun _ => rfl
  -- the two support laws
  have hprivCard : privateSupport.card = 3 := data.hthree data.privateSlot
  have hcomplCard : privateSupportᶜ.card = 3 := by
    rw [Finset.card_compl, hprivCard, Fintype.card_fin]
  have hmultLe : ∀ probe : Fin 6, mult probe ≤ 3 := by
    intro probe
    by_cases hbig : 3 ≤ mult probe
    · exact le_of_eq (hexact probe hbig)
    · omega
  have hmultPos : ∀ probe : Fin 6, 0 < mult probe := data.multiplicity_pos
  -- the private support is wholly boundary
  have hprivBoundary : ∀ probe ∈ privateSupport,
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe = 0 :=
    fun probe hmem => data.boundary_of_private_support hdiag hmem
  -- the total multiplicity
  have hsumMult : ∑ probe : Fin 6, mult probe = 12 := by
    rw [hmultDef, data.sum_multiplicity, hbasis]
  -- the complement slot carries exactly the complement of the private support
  have hcomplMem : ∀ probe : Fin 6,
      probe ∈ datumTightSupport data.tightDir (data.basisLabel complSlot) ↔
        probe ∉ privateSupport := by
    intro probe
    rw [hcomplSupp, Finset.mem_compl]
  -- CASE ONE: the complement support carries an atom of multiplicity one
  by_cases hone : ∃ probe : Fin 6, probe ∉ privateSupport ∧ mult probe = 1
  · obtain ⟨witness, hwitnessOut, hwitnessMult⟩ := hone
    refine data.false_of_all_boundary hdiag fun probe => ?_
    by_cases hmem : probe ∈ privateSupport
    · exact hprivBoundary probe hmem
    · exact data.boundary_of_pin_cocarrier hdiag hwitnessMult
        ((hcomplMem witness).mpr hwitnessOut) ((hcomplMem probe).mpr hmem)
  · push Not at hone
    have hcomplMultTwo : ∀ probe : Fin 6, probe ∉ privateSupport →
        2 ≤ mult probe := by
      intro probe hout
      have hne := hone probe hout
      have hpos := hmultPos probe
      omega
    -- the triangular triple, packaged for both remaining branches
    have htriple : ∀ atomOne atomTwo : Fin 6,
        ∀ slotOne slotTwo : Fin data.basisCount,
        chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomOne = 0 →
        chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomTwo = 0 →
        atomOne ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) →
        slotOne ≠ data.privateSlot →
        atomTwo ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) →
        slotTwo ≠ data.privateSlot →
        atomOne ∉ datumTightSupport data.tightDir (data.basisLabel slotTwo) →
        False := by
      intro atomOne atomTwo slotOne slotTwo hbndOne hbndTwo honeIn hslotOneNe
        htwoIn hslotTwoNe honeOutTwo
      have hpinOut : ∀ slotIdx : Fin data.basisCount,
          slotIdx ≠ data.privateSlot →
          data.pinAtom ∉ datumTightSupport data.tightDir
            (data.basisLabel slotIdx) := by
        intro slotIdx hne hmem
        exact hne (data.pin_only_slot hmem)
      have hcast : (data.basisCount : ℝ) = 4 := by rw [hbasis]; norm_num
      refine data.false_of_triangular_boundary_triple hdiag
        (data.pinAtom_boundary hdiag) hbndOne hbndTwo
        (mem_datumTightSupport.mpr data.hpinNe) honeIn
        (hpinOut slotOne hslotOneNe) htwoIn (hpinOut slotTwo hslotTwoNe)
        honeOutTwo ?_
      rw [hcast, htrace]
      norm_num
    -- CASE TWO: the complement support carries a boundary atom
    by_cases htwo : ∃ probe : Fin 6, probe ∉ privateSupport ∧
        chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight probe = 0
    · obtain ⟨witness, hwitnessOut, hwitnessBnd⟩ := htwo
      by_cases hthick : ∃ probe : Fin 6, probe ∈ privateSupport ∧ 2 ≤ mult probe
      · obtain ⟨thick, hthickMem, hthickMult⟩ := hthick
        have hprivMem : data.privateSlot ∈ car thick :=
          (hcarmem thick data.privateSlot).mpr hthickMem
        have hcardTwo : 2 ≤ (car thick).card := by
          rw [hcarCard thick]
          exact hthickMult
        have herase : ((car thick).erase data.privateSlot).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hprivMem]
          omega
        obtain ⟨freeSlot, hfreeSlot⟩ := herase
        have hfreeNe : freeSlot ≠ data.privateSlot :=
          Finset.ne_of_mem_erase hfreeSlot
        have hfreeMem : thick ∈ datumTightSupport data.tightDir
            (data.basisLabel freeSlot) :=
          (hcarmem thick freeSlot).mp (Finset.mem_of_mem_erase hfreeSlot)
        refine htriple thick witness freeSlot complSlot
          (hprivBoundary thick hthickMem) hwitnessBnd hfreeMem hfreeNe
          ((hcomplMem witness).mpr hwitnessOut) hcomplNe ?_
        intro hcontra
        exact ((hcomplMem thick).mp hcontra) hthickMem
      · -- the private support is all of multiplicity one
        push Not at hthick
        have hprivOne : ∀ probe ∈ privateSupport, mult probe = 1 := by
          intro probe hmem
          have hle := hthick probe hmem
          have hpos := hmultPos probe
          omega
        have hsumPriv : ∑ probe ∈ privateSupport, mult probe = 3 := by
          have hstep : ∑ probe ∈ privateSupport, mult probe
              = ∑ _probe ∈ privateSupport, 1 :=
            Finset.sum_congr rfl fun probe hmem => hprivOne probe hmem
          rw [hstep, Finset.sum_const, hprivCard, smul_eq_mul]
        have hsplit := Finset.sum_add_sum_compl privateSupport mult
        have hsumCompl : ∑ probe ∈ privateSupportᶜ, mult probe = 9 := by
          omega
        have hall : ∀ probe ∈ privateSupportᶜ, mult probe = 3 := by
          intro probe hmem
          by_contra hne
          have hlt : mult probe < 3 := by
            have := hmultLe probe
            omega
          have hstrict : ∑ y ∈ privateSupportᶜ, mult y
              < ∑ _y ∈ privateSupportᶜ, 3 :=
            Finset.sum_lt_sum (fun y _ => hmultLe y) ⟨probe, hmem, hlt⟩
          rw [Finset.sum_const, hcomplCard, smul_eq_mul] at hstrict
          omega
        refine data.false_of_all_boundary hdiag fun probe => ?_
        by_cases hmem : probe ∈ privateSupport
        · exact hprivBoundary probe hmem
        · exact hbnd probe (by
            have := hall probe (Finset.mem_compl.mpr hmem)
            omega)
    · -- CASE THREE: every atom off the private support is interior
      push Not at htwo
      have hcomplMultExact : ∀ probe : Fin 6, probe ∉ privateSupport →
          mult probe = 2 := by
        intro probe hout
        have hlow := hcomplMultTwo probe hout
        have hnotBig : ¬ 3 ≤ mult probe := by
          intro hbig
          exact htwo probe hout (hbnd probe hbig)
        omega
      have hsumCompl : ∑ probe ∈ privateSupportᶜ, mult probe = 6 := by
        have hstep : ∑ probe ∈ privateSupportᶜ, mult probe
            = ∑ _probe ∈ privateSupportᶜ, 2 :=
          Finset.sum_congr rfl fun probe hmem =>
            hcomplMultExact probe (Finset.mem_compl.mp hmem)
        rw [hstep, Finset.sum_const, hcomplCard, smul_eq_mul]
      have hsplit := Finset.sum_add_sum_compl privateSupport mult
      have hsumPriv : ∑ probe ∈ privateSupport, mult probe = 6 := by omega
      have hpinMem : data.pinAtom ∈ privateSupport :=
        mem_datumTightSupport.mpr data.hpinNe
      have herasePriv := Finset.add_sum_erase privateSupport mult hpinMem
      have hsumErase : ∑ probe ∈ privateSupport.erase data.pinAtom, mult probe
          = 5 := by
        have hpinOne : mult data.pinAtom = 1 := data.hmultOne
        omega
      have hcardErase : (privateSupport.erase data.pinAtom).card = 2 := by
        rw [Finset.card_erase_of_mem hpinMem, hprivCard]
      obtain ⟨atomA, atomB, hab, hpair⟩ := Finset.card_eq_two.mp hcardErase
      have hsumPair : mult atomA + mult atomB = 5 := by
        rw [hpair, Finset.sum_pair hab] at hsumErase
        exact hsumErase
      have hmemA : atomA ∈ privateSupport := by
        have : atomA ∈ privateSupport.erase data.pinAtom := by
          rw [hpair]; exact Finset.mem_insert_self _ _
        exact Finset.mem_of_mem_erase this
      have hmemB : atomB ∈ privateSupport := by
        have : atomB ∈ privateSupport.erase data.pinAtom := by
          rw [hpair]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        exact Finset.mem_of_mem_erase this
      -- the deep atom carries every slot but the complement slot
      have hdeep : ∀ atomDeep atomShallow : Fin 6,
          atomDeep ∈ privateSupport → atomShallow ∈ privateSupport →
          mult atomDeep = 3 → mult atomShallow = 2 → False := by
        intro atomDeep atomShallow hdeepMem hshallowMem hdeepMult hshallowMult
        have hdeepOut : complSlot ∉ car atomDeep := by
          intro hmem
          exact ((hcomplMem atomDeep).mp ((hcarmem atomDeep complSlot).mp hmem))
            hdeepMem
        have hshallowOut : complSlot ∉ car atomShallow := by
          intro hmem
          exact ((hcomplMem atomShallow).mp
            ((hcarmem atomShallow complSlot).mp hmem)) hshallowMem
        have hdeepCard : (car atomDeep).card = 3 := by
          rw [hcarCard atomDeep, hdeepMult]
        have hshallowCard : (car atomShallow).card = 2 := by
          rw [hcarCard atomShallow, hshallowMult]
        have heraseCard : ((Finset.univ : Finset (Fin data.basisCount)).erase
            complSlot).card = 3 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ complSlot),
            Finset.card_univ, Fintype.card_fin, hbasis]
        have hdeepEq : car atomDeep
            = (Finset.univ : Finset (Fin data.basisCount)).erase complSlot := by
          refine Finset.eq_of_subset_of_card_le (fun slotIdx hslot => ?_) ?_
          · refine Finset.mem_erase.mpr ⟨fun hcontra => ?_, Finset.mem_univ _⟩
            rw [hcontra] at hslot
            exact hdeepOut hslot
          · rw [hdeepCard, heraseCard]
        have hshallowSub : car atomShallow ⊆ car atomDeep := by
          rw [hdeepEq]
          intro slotIdx hslot
          refine Finset.mem_erase.mpr ⟨fun hcontra => ?_, Finset.mem_univ _⟩
          rw [hcontra] at hslot
          exact hshallowOut hslot
        have hnotSub : ¬ car atomDeep ⊆ car atomShallow := by
          intro hsub
          have := Finset.card_le_card hsub
          omega
        obtain ⟨deepSlot, hdeepSlotMem, hdeepSlotOut⟩ :=
          Finset.not_subset.mp hnotSub
        have hprivShallow : data.privateSlot ∈ car atomShallow :=
          (hcarmem atomShallow data.privateSlot).mpr hshallowMem
        have hdeepSlotNe : deepSlot ≠ data.privateSlot := by
          intro hcontra
          rw [hcontra] at hdeepSlotOut
          exact hdeepSlotOut hprivShallow
        have hshallowErase : ((car atomShallow).erase data.privateSlot).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hprivShallow,
            hshallowCard]
          omega
        obtain ⟨shallowSlot, hshallowSlot⟩ := hshallowErase
        have hshallowSlotNe : shallowSlot ≠ data.privateSlot :=
          Finset.ne_of_mem_erase hshallowSlot
        have hshallowSlotMem : shallowSlot ∈ car atomShallow :=
          Finset.mem_of_mem_erase hshallowSlot
        refine htriple atomShallow atomDeep shallowSlot deepSlot
          (hprivBoundary atomShallow hshallowMem)
          (hprivBoundary atomDeep hdeepMem)
          ((hcarmem atomShallow shallowSlot).mp hshallowSlotMem) hshallowSlotNe
          ((hcarmem atomDeep deepSlot).mp hdeepSlotMem) hdeepSlotNe ?_
        intro hcontra
        exact hdeepSlotOut ((hcarmem atomShallow deepSlot).mpr hcontra)
      have hleA := hmultLe atomA
      have hleB := hmultLe atomB
      rcases (by omega : mult atomA = 3 ∧ mult atomB = 2
          ∨ mult atomA = 2 ∧ mult atomB = 3) with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact hdeep atomA atomB hmemA hmemB ha hb
      · exact hdeep atomB atomA hmemB hmemA hb ha

/-- The rank-four boundary residue is closed: the complement residue and
the rank-four minor kill cover it. -/
theorem sharedPrivateBoundaryFourClosed : SharedPrivateBoundaryFourClosed :=
  sharedPrivateBoundaryFourClosed_of_complementSlot
    sharedPrivateComplementSlotClosed

/-! ## Layer 5 — the high boundary residue narrows to basis count five -/

/-- **THE BASIS-COUNT-FIVE BOUNDARY RESIDUE.**  The trace-two boundary
stratum above basis count four sits at basis count five exactly, and it
carries the two boundary laws: every atom of multiplicity one is a
boundary atom, and the whole private support is a boundary set. -/
def SharedPrivateBoundaryFiveClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (gramDiag : Fin data.basisCount → ℝ),
    data.gram = Matrix.diagonal gramDiag →
    Matrix.trace data.coeff = 2 →
    data.basisCount = 5 →
    (∀ atomIndex : Fin 6,
      basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1 →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0) →
    (∀ atomIndex : Fin 6,
      atomIndex ∈ datumTightSupport data.tightDir
        (data.basisLabel data.privateSlot) →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0) →
    (Finset.univ.filter fun atomIndex =>
        basisSupportMultiplicity data.tightDir data.basisLabel
          atomIndex = 1).card ≤ data.boundarySet.card →
    2 ≤ (Finset.univ.filter fun atomIndex =>
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex).card →
    ∀ atomIndex : Fin 6,
      3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel atomIndex →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0 →
      False

/-- **THE HIGH DISPATCH.**  The basis-count-five residue closes the whole
high boundary residue.  Basis count six carries coefficient trace three,
and the basis count is at most six. -/
theorem sharedPrivateBoundaryHighClosed_of_five
    (hfive : SharedPrivateBoundaryFiveClosed) :
    SharedPrivateBoundaryHighClosed := by
  intro crux data gramDiag hdiag htrace hge hcount atomIndex hmult hzero
  have hle := data.basisCount_le_six
  have hnotSix : data.basisCount ≠ 6 := by
    intro hsix
    have hthree := data.trace_eq_three_of_basisCount_six hsix
    rw [htrace] at hthree
    norm_num at hthree
  have hfiveEq : data.basisCount = 5 := by omega
  exact hfive crux data gramDiag hdiag htrace hfiveEq
    (fun probe hprobe => data.boundary_of_multiplicity_one hdiag hprobe)
    (fun probe hprobe => data.boundary_of_private_support hdiag hprobe)
    hcount (data.two_le_interior_card hdiag) atomIndex hmult hzero

/-- **THE BOUNDARY DISPATCH.**  The basis-count-five residue closes the
whole trace-two boundary residue. -/
theorem sharedPrivateBoundaryClosed_of_five
    (hfive : SharedPrivateBoundaryFiveClosed) : SharedPrivateBoundaryClosed :=
  sharedPrivateBoundaryClosed_of_split sharedPrivateBoundaryFourClosed
    (sharedPrivateBoundaryHighClosed_of_five hfive)

/-- **THE STRATA DISPATCH.**  Three residues now close the generic
shared-private kill: the extras residue, the basis-count-five boundary
residue, and the deficit residue. -/
theorem sharedPrivateKilled_of_five_strata
    (hextras : SharedPrivateExtrasClosed)
    (hfive : SharedPrivateBoundaryFiveClosed)
    (hdeficit : SharedPrivateDeficitClosed) : SharedPrivateKilled :=
  sharedPrivateKilled_of_strata hextras
    (sharedPrivateBoundaryClosed_of_five hfive) hdeficit

/-- The three residues discharge closure two of the rank-four rung. -/
theorem rankFourSharedPrivateClosed_of_five_strata
    (hextras : SharedPrivateExtrasClosed)
    (hfive : SharedPrivateBoundaryFiveClosed)
    (hdeficit : SharedPrivateDeficitClosed) : RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_five_strata hextras hfive hdeficit)

/-- The three residues discharge the shared-private closure of the
rank-five rung. -/
theorem rankFiveSharedPrivateClosed_of_five_strata
    (hextras : SharedPrivateExtrasClosed)
    (hfive : SharedPrivateBoundaryFiveClosed)
    (hdeficit : SharedPrivateDeficitClosed) : RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_five_strata hextras hfive hdeficit)

/-- The three residues discharge the shared-private closure of the
rank-six rung. -/
theorem rankSixSharedPrivateClosed_of_five_strata
    (hextras : SharedPrivateExtrasClosed)
    (hfive : SharedPrivateBoundaryFiveClosed)
    (hdeficit : SharedPrivateDeficitClosed) : RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_five_strata hextras hfive hdeficit)

end Gtz
