import Gtz.Wave.SharedPrivateDualRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The co-parallel columns and the nonzero leak — the two tools that finish
the odd signature systems

Two independent laws live here, and both come from the dual read.

**THE CO-PARALLEL COLUMN DICHOTOMY.**  A symmetric idempotent resolves
into its own columns: `S = ∑ over the slots of (column) (column)ᵀ`.  Read
one entry of that resolution when every column except ONE is a multiple
of a base column.  The special column then satisfies

  `(1 - S s s) • (column s) = scale • (column base)`,

thus EITHER the special column joins the parallel family, and the trace
of a parallel family is one or zero, OR the diagonal entry at the special
slot is one, and a carried read refuses that.  **A read at the special
slot kills the whole configuration.**

**THE NONZERO LEAK.**  When a nonzero fixed vector is seen by exactly TWO
atoms, the read combination of those two atoms is fixed.  Read the fixed
equation at a slot that the first atom carries and the second one misses:
the leak of the second atom at that slot is `(1 - the shifted weight of
the first)` times a nonzero product.  **Thus the leak does not vanish.**

The two laws meet at the unique separator.  With exactly three interior
atoms the dual vector of the third one is seen by the other two, thus
every interior atom leaks at every live slot it does not carry.  The
landed unique separator leak law asks the same leak to VANISH whenever
exactly one interior atom separates a slot pair.  **Thus no slot pair has
a unique separator.**

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.idem_entry_eq_column_dot` — **THE COLUMN RESOLUTION** of a
  symmetric idempotent.
* `Gtz.column_smul_or_diag_eq_one` — **THE CO-PARALLEL DICHOTOMY.**
* `Gtz.false_of_coparallel_columns` — the kill that the dichotomy gives.
* `Gtz.readCombination_of_pair` — the read combination of a probe with
  two seers.
* `Gtz.leak_ne_zero_of_fixed_pair` — **THE NONZERO LEAK.**
* `Gtz.SharedPrivateData.exists_interior_dual_seers` — the two seers of
  the dual vector of one interior atom are the other two.
* `Gtz.SharedPrivateData.false_of_unique_separator` — **THE UNIQUE
  SEPARATOR KILL.**

## Vacuity

The matrix statements are unconditional.  The datum statements quantify
over shared-private data, and no datum exists if `Gtz.GtzWeighted 6 3`
holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the column resolution -/

/-- **THE COLUMN RESOLUTION.**  A symmetric idempotent is the total of the
outer squares of its own columns, read one entry at a time. -/
theorem idem_entry_eq_column_dot {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (rowSlot colSlot : Fin slotCount) :
    S rowSlot colSlot
      = ∑ midSlot, kernelColumn S midSlot rowSlot * kernelColumn S midSlot colSlot := by
  have hentry := congrFun (congrFun hidem rowSlot) colSlot
  rw [Matrix.mul_apply] at hentry
  rw [← hentry]
  refine Finset.sum_congr rfl fun midSlot _ => ?_
  show S rowSlot midSlot * S midSlot colSlot = S rowSlot midSlot * S colSlot midSlot
  rw [symm_entry_swap hsymm colSlot midSlot]

/-! ## Layer 2 — the co-parallel dichotomy -/

/-- **THE CO-PARALLEL DICHOTOMY.**  When every column except one is a
multiple of a base column, the special column either joins the parallel
family or the diagonal entry at the special slot is one. -/
theorem column_smul_or_diag_eq_one {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S)
    {baseSlot specialSlot : Fin slotCount} (coeff : Fin slotCount → ℝ)
    (hpar : ∀ slot : Fin slotCount, slot ≠ specialSlot →
      kernelColumn S slot = fun rowSlot => coeff slot * kernelColumn S baseSlot rowSlot) :
    S specialSlot specialSlot = 1
      ∨ ∃ scale : ℝ, kernelColumn S specialSlot
        = fun rowSlot => scale * kernelColumn S baseSlot rowSlot := by
  classical
  by_cases hone : S specialSlot specialSlot = 1
  · exact Or.inl hone
  refine Or.inr ⟨(∑ midSlot ∈ Finset.univ.erase specialSlot, coeff midSlot * coeff midSlot)
    * S specialSlot baseSlot / (1 - S specialSlot specialSlot), ?_⟩
  have hsub : (1 : ℝ) - S specialSlot specialSlot ≠ 0 := fun hzero => hone (by linarith)
  funext rowSlot
  -- the resolution of the special entry, split at the special slot
  have hres := idem_entry_eq_column_dot hsymm hidem rowSlot specialSlot
  have hsplit : (∑ midSlot, kernelColumn S midSlot rowSlot * kernelColumn S midSlot specialSlot)
      = kernelColumn S specialSlot rowSlot * kernelColumn S specialSlot specialSlot
        + ∑ midSlot ∈ Finset.univ.erase specialSlot,
            kernelColumn S midSlot rowSlot * kernelColumn S midSlot specialSlot := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ specialSlot)]
  have hrest : (∑ midSlot ∈ Finset.univ.erase specialSlot,
        kernelColumn S midSlot rowSlot * kernelColumn S midSlot specialSlot)
      = (∑ midSlot ∈ Finset.univ.erase specialSlot, coeff midSlot * coeff midSlot)
        * (kernelColumn S baseSlot rowSlot * kernelColumn S baseSlot specialSlot) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun midSlot hmid => ?_
    have hne : midSlot ≠ specialSlot := (Finset.mem_erase.mp hmid).1
    rw [congrFun (hpar midSlot hne) rowSlot, congrFun (hpar midSlot hne) specialSlot]
    ring
  rw [hsplit, hrest] at hres
  have hdiag : kernelColumn S specialSlot specialSlot = S specialSlot specialSlot := rfl
  have hbase : kernelColumn S baseSlot specialSlot = S specialSlot baseSlot := rfl
  have hgoalRaw : S rowSlot specialSlot
      = S specialSlot specialSlot * kernelColumn S specialSlot rowSlot
        + (∑ midSlot ∈ Finset.univ.erase specialSlot, coeff midSlot * coeff midSlot)
          * (kernelColumn S baseSlot rowSlot * S specialSlot baseSlot) := by
    rw [hres, hdiag, hbase]
    ring
  show S rowSlot specialSlot
    = (∑ midSlot ∈ Finset.univ.erase specialSlot, coeff midSlot * coeff midSlot)
        * S specialSlot baseSlot / (1 - S specialSlot specialSlot)
      * kernelColumn S baseSlot rowSlot
  have hcol : kernelColumn S specialSlot rowSlot = S rowSlot specialSlot := rfl
  rw [hcol] at hgoalRaw
  rw [div_mul_eq_mul_div, eq_div_iff hsub]
  linear_combination hgoalRaw

/-- **THE CO-PARALLEL KILL.**  A trace-two symmetric idempotent whose
columns are all multiples of one base column except at a slot that
carries a read cannot exist. -/
theorem false_of_coparallel_columns {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (htrace : Matrix.trace S = 2)
    {baseSlot specialSlot : Fin slotCount} (coeff : Fin slotCount → ℝ)
    (hpar : ∀ slot : Fin slotCount, slot ≠ specialSlot →
      kernelColumn S slot = fun rowSlot => coeff slot * kernelColumn S baseSlot rowSlot)
    {readVec : Fin slotCount → ℝ} {readVal : ℝ}
    (hread : (S *ᵥ readVec) specialSlot = readVal * readVec specialSlot)
    (hnz : readVec specialSlot ≠ 0) (hlt : readVal < 1) : False := by
  classical
  rcases column_smul_or_diag_eq_one hsymm hidem coeff hpar with hone | ⟨scale, hscale⟩
  · exact false_of_diag_eq_one_of_read hsymm hidem hone hread hnz hlt
  · refine false_of_parallel_columns hsymm hidem baseSlot
      (fun slot => if slot = specialSlot then scale else coeff slot) ?_ htrace
    intro slot
    by_cases hslot : slot = specialSlot
    · subst hslot
      simpa using hscale
    · simpa [hslot] using hpar slot hslot

/-! ## Layer 3 — the nonzero leak of a two-seer probe -/

/-- The read combination of a probe that exactly two atoms see. -/
theorem readCombination_of_pair {atomCount slotCount : ℕ}
    (readVecs : Fin atomCount → Fin slotCount → ℝ) (probe : Fin slotCount → ℝ)
    {atomA atomB : Fin atomCount} (hne : atomA ≠ atomB)
    (hother : ∀ atomIndex : Fin atomCount, atomIndex ≠ atomA → atomIndex ≠ atomB →
      readVecs atomIndex ⬝ᵥ probe = 0) :
    readCombination readVecs probe
      = fun rowSlot => (readVecs atomA ⬝ᵥ probe) * readVecs atomA rowSlot
        + (readVecs atomB ⬝ᵥ probe) * readVecs atomB rowSlot := by
  classical
  funext rowSlot
  rw [readCombination_apply]
  have hrestrict : (∑ atomIndex ∈ ({atomA, atomB} : Finset (Fin atomCount)),
        (readVecs atomIndex ⬝ᵥ probe) * readVecs atomIndex rowSlot)
      = ∑ atomIndex, (readVecs atomIndex ⬝ᵥ probe) * readVecs atomIndex rowSlot := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro atomIndex _ hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    rw [hother atomIndex hnot.1 hnot.2, zero_mul]
  rw [← hrestrict, Finset.sum_pair hne]

/-- **THE NONZERO LEAK.**  When exactly two atoms see a fixed probe, the
read combination of the pair is fixed.  At a slot that the first atom
carries and the second one misses, the fixed equation prices the leak of
the second atom by a nonzero product. -/
theorem leak_ne_zero_of_fixed_pair {atomCount slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ} (hsymm : Sᵀ = S)
    (readVecs : Fin atomCount → Fin slotCount → ℝ)
    (hcommute : ∀ rowSlot colSlot : Fin slotCount,
      (∑ atomIndex, readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot)
        = ∑ atomIndex, (S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex colSlot)
    {probe : Fin slotCount → ℝ} (hfix : S *ᵥ probe = probe)
    {atomA atomB : Fin atomCount} (hne : atomA ≠ atomB)
    (hother : ∀ atomIndex : Fin atomCount, atomIndex ≠ atomA → atomIndex ≠ atomB →
      readVecs atomIndex ⬝ᵥ probe = 0)
    (hseeA : readVecs atomA ⬝ᵥ probe ≠ 0) (_hseeB : readVecs atomB ⬝ᵥ probe ≠ 0)
    {pinSlot : Fin slotCount} {weightA : ℝ}
    (hreadA : (S *ᵥ readVecs atomA) pinSlot = weightA * readVecs atomA pinSlot)
    (hnzA : readVecs atomA pinSlot ≠ 0) (hltA : weightA < 1)
    (hmissB : readVecs atomB pinSlot = 0) :
    (S *ᵥ readVecs atomB) pinSlot ≠ 0 := by
  classical
  have hcomb := readCombination_fixed hsymm readVecs hcommute hfix
  rw [readCombination_of_pair readVecs probe hne hother] at hcomb
  have hentry := congrFun hcomb pinSlot
  have hleft : (S *ᵥ fun rowSlot => (readVecs atomA ⬝ᵥ probe) * readVecs atomA rowSlot
        + (readVecs atomB ⬝ᵥ probe) * readVecs atomB rowSlot) pinSlot
      = (readVecs atomA ⬝ᵥ probe) * (S *ᵥ readVecs atomA) pinSlot
        + (readVecs atomB ⬝ᵥ probe) * (S *ᵥ readVecs atomB) pinSlot := by
    show (∑ colSlot, S pinSlot colSlot
        * ((readVecs atomA ⬝ᵥ probe) * readVecs atomA colSlot
          + (readVecs atomB ⬝ᵥ probe) * readVecs atomB colSlot))
      = (readVecs atomA ⬝ᵥ probe) * (S *ᵥ readVecs atomA) pinSlot
        + (readVecs atomB ⬝ᵥ probe) * (S *ᵥ readVecs atomB) pinSlot
    have hstepA : (S *ᵥ readVecs atomA) pinSlot
        = ∑ colSlot, S pinSlot colSlot * readVecs atomA colSlot := rfl
    have hstepB : (S *ᵥ readVecs atomB) pinSlot
        = ∑ colSlot, S pinSlot colSlot * readVecs atomB colSlot := rfl
    rw [hstepA, hstepB, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun colSlot _ => by ring
  rw [hleft, hreadA, hmissB, mul_zero, add_zero] at hentry
  intro hzero
  rw [hzero, mul_zero, add_zero] at hentry
  have hprod : (readVecs atomA ⬝ᵥ probe) * ((1 - weightA) * readVecs atomA pinSlot) = 0 := by
    linear_combination -hentry
  rcases mul_eq_zero.mp hprod with hcase | hcase
  · exact hseeA hcase
  · rcases mul_eq_zero.mp hcase with hsub | hsub
    · linarith [hsub]
    · exact hnzA hsub

/-! ## Layer 4 — the interior triple reads its own leaks -/

set_option maxHeartbeats 3200000 in
/-- **THE INTERIOR DUAL SEERS.**  With exactly three interior atoms the
dual vector of the third one is seen by the other two and by nobody
else. -/
theorem SharedPrivateData.exists_interior_dual_seers {crux : SixThreeCrux}
    (data : SharedPrivateData crux)
    {atomOne atomTwo atomThree : Fin 6}
    (hposThree : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomThree)
    (hinterior : ∀ probe : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe →
      probe = atomOne ∨ probe = atomTwo ∨ probe = atomThree)
    (S : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ)
    (readVecs : Fin 6 → Fin data.basisCount → ℝ)
    (hSsymm : Sᵀ = S) (hSidem : S * S = S) (hStrace : Matrix.trace S = 2)
    (hsuppFrame : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot) →
      readVecs atomIndex slot = 0)
    (hread : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      (S *ᵥ readVecs atomIndex) slot
        = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * readVecs atomIndex slot)
    (hnorm : ∀ atomIndex : Fin 6, readVecs atomIndex ⬝ᵥ readVecs atomIndex = (6 : ℝ)⁻¹)
    (hboundary : ∀ atomIndex : Fin 6,
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0 →
      S *ᵥ readVecs atomIndex = 0)
    (hnz : ∀ atomIndex : Fin 6, readVecs atomIndex ≠ 0)
    (hspan : ∀ testVec : Fin data.basisCount → ℝ,
      (∀ atomIndex : Fin 6, readVecs atomIndex ⬝ᵥ testVec = 0) → testVec = 0)
    (hcommute : ∀ rowSlot colSlot : Fin data.basisCount,
      (∑ atomIndex : Fin 6,
          readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot)
        = ∑ atomIndex : Fin 6,
          (S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex colSlot) :
    ∃ dualVec : Fin data.basisCount → ℝ,
      S *ᵥ dualVec = dualVec
        ∧ readVecs atomOne ⬝ᵥ dualVec ≠ 0
        ∧ readVecs atomTwo ⬝ᵥ dualVec ≠ 0
        ∧ ∀ atomIndex : Fin 6, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
            readVecs atomIndex ⬝ᵥ dualVec = 0 := by
  classical
  set shifted : Fin 6 → ℝ := fun atomIndex =>
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex with hshifted
  have hltOne : ∀ atomIndex : Fin 6, shifted atomIndex < 1 := by
    intro atomIndex
    have hwle : (chartPointOfDesign crux.design).weight atomIndex ≤ 1 := by
      have hle : (chartPointOfDesign crux.design).weight atomIndex
          ≤ ∑ probe, (chartPointOfDesign crux.design).weight probe :=
        Finset.single_le_sum
          (f := fun probe => (chartPointOfDesign crux.design).weight probe)
          (fun probe _ => (data.hdata.weight_pos probe).le) (Finset.mem_univ atomIndex)
      rwa [data.hdata.weight_sum_one] at hle
    have hneg := data.hvalueNeg
    rw [hshifted]
    dsimp only
    linarith
  have hpin : ∀ atomIndex : Fin 6, ∃ pinSlot : Fin data.basisCount,
      (S *ᵥ readVecs atomIndex) pinSlot = shifted atomIndex * readVecs atomIndex pinSlot
        ∧ readVecs atomIndex pinSlot ≠ 0 := by
    intro atomIndex
    obtain ⟨pinSlot, hpinNe⟩ : ∃ pinSlot : Fin data.basisCount,
        readVecs atomIndex pinSlot ≠ 0 := by
      by_contra hnone
      simp only [not_exists, not_not] at hnone
      exact hnz atomIndex (funext hnone)
    have hmem : atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel pinSlot) := by
      by_contra hnot
      exact hpinNe (hsuppFrame atomIndex pinSlot hnot)
    exact ⟨pinSlot, hread atomIndex pinSlot hmem, hpinNe⟩
  have hsuppCar : ∀ atomIndex : Fin 6,
      ∀ slot ∉ (Finset.univ.filter fun slot : Fin data.basisCount =>
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)),
      readVecs atomIndex slot = 0 := by
    intro atomIndex slot hslot
    exact hsuppFrame atomIndex slot fun hmem =>
      hslot (Finset.mem_filter.mpr ⟨Finset.mem_univ slot, hmem⟩)
  have hreadCar : ∀ atomIndex : Fin 6,
      ∀ slot ∈ (Finset.univ.filter fun slot : Fin data.basisCount =>
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)),
      (S *ᵥ readVecs atomIndex) slot = shifted atomIndex * readVecs atomIndex slot :=
    fun atomIndex slot hslot => hread atomIndex slot (Finset.mem_filter.mp hslot).2
  have hfixEnergy : (S *ᵥ readVecs atomThree) ⬝ᵥ (S *ᵥ readVecs atomThree)
      = shifted atomThree * (6 : ℝ)⁻¹ := by
    rw [read_fixed_self_energy hSsymm hSidem (hsuppCar atomThree) (hreadCar atomThree),
      hnorm atomThree]
  obtain ⟨dualVec, hdualFix, hdualBase, hdualEnergy⟩ :=
    exists_dual_vector_of_trace_two hSsymm hSidem hStrace (readVecs atomThree)
  have hdualNe : dualVec ≠ 0 := by
    intro hzero
    rw [hzero, zero_dotProduct, hfixEnergy] at hdualEnergy
    nlinarith [hposThree, hdualEnergy]
  have hblindThree : readVecs atomThree ⬝ᵥ dualVec = 0 := by
    rw [dotProduct_comm]; exact hdualBase
  have hseer : ∀ atomIndex : Fin 6, readVecs atomIndex ⬝ᵥ dualVec ≠ 0 →
      atomIndex = atomOne ∨ atomIndex = atomTwo := by
    intro atomIndex hsee
    have hnotThree : atomIndex ≠ atomThree := fun heq => hsee (heq ▸ hblindThree)
    have hpos : 0 < shifted atomIndex := by
      rcases (capture_diagonal_nonneg_of_isChartStationaryData data.hdata
          atomIndex).lt_or_eq with hpos | heq
      · exact hpos
      · exfalso
        have hzeroFix : S *ᵥ readVecs atomIndex = 0 := hboundary atomIndex heq.symm
        refine hsee ?_
        have hstep : readVecs atomIndex ⬝ᵥ dualVec
            = readVecs atomIndex ⬝ᵥ (S *ᵥ dualVec) := by rw [hdualFix]
        rw [hstep, dotProduct_mulVec_symm hSsymm (readVecs atomIndex) dualVec, hzeroFix,
          zero_dotProduct]
    rcases hinterior atomIndex hpos with heq | heq | heq
    · exact Or.inl heq
    · exact Or.inr heq
    · exact absurd heq hnotThree
  obtain ⟨seerOne, seerTwo, hseerNe, hpairOne, hpairTwo⟩ :=
    exists_dual_pair_of_fixed hSsymm readVecs hcommute hspan shifted hltOne hpin
      hdualFix hdualNe
  have hsees : readVecs atomOne ⬝ᵥ dualVec ≠ 0 ∧ readVecs atomTwo ⬝ᵥ dualVec ≠ 0 := by
    rcases hseer seerOne hpairOne with heqOne | heqOne
    · rcases hseer seerTwo hpairTwo with heqTwo | heqTwo
      · exact absurd (heqOne.trans heqTwo.symm) hseerNe
      · exact ⟨heqOne ▸ hpairOne, heqTwo ▸ hpairTwo⟩
    · rcases hseer seerTwo hpairTwo with heqTwo | heqTwo
      · exact ⟨heqTwo ▸ hpairTwo, heqOne ▸ hpairOne⟩
      · exact absurd (heqOne.trans heqTwo.symm) hseerNe
  refine ⟨dualVec, hdualFix, hsees.1, hsees.2, ?_⟩
  intro atomIndex hnotOne hnotTwo
  by_contra hsee
  rcases hseer atomIndex hsee with heq | heq
  · exact hnotOne heq
  · exact hnotTwo heq

set_option maxHeartbeats 3200000 in
/-- **THE UNIQUE SEPARATOR KILL.**  With exactly three interior atoms the
leak of an interior atom never vanishes at a live slot off its carrier.
The landed unique separator leak law asks that same leak to vanish when
exactly one interior atom separates a slot pair.  Thus no slot pair has a
unique separator. -/
theorem SharedPrivateData.false_of_unique_separator {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2)
    {atomOne atomTwo atomThree : Fin 6}
    (hne12 : atomOne ≠ atomTwo) (hne13 : atomOne ≠ atomThree)
    (hne23 : atomTwo ≠ atomThree)
    (hposThree : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomThree)
    (hinterior : ∀ probe : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe →
      probe = atomOne ∨ probe = atomTwo ∨ probe = atomThree)
    {leakSlot carrierSlot : Fin data.basisCount}
    (hcarryOneLeak : atomOne ∈ datumTightSupport data.tightDir (data.basisLabel leakSlot))
    (hcarryOneCar : atomOne ∈ datumTightSupport data.tightDir (data.basisLabel carrierSlot))
    (hmissTwoLeak : atomTwo ∉ datumTightSupport data.tightDir (data.basisLabel leakSlot))
    (hcarryTwoCar : atomTwo ∈ datumTightSupport data.tightDir (data.basisLabel carrierSlot))
    (hthreeSame : atomThree ∈ datumTightSupport data.tightDir (data.basisLabel leakSlot)
      ↔ atomThree ∈ datumTightSupport data.tightDir (data.basisLabel carrierSlot)) :
    False := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStraceRaw, hsuppFrame, hread, hnorm,
    hboundary, hcarrierNz, hnz, hspan, hcommute, _hdeadCol⟩ :=
    data.exists_full_read_frame hdiag
  have hStrace : Matrix.trace S = 2 := by rw [hStraceRaw, htrace]
  set shifted : Fin 6 → ℝ := fun atomIndex =>
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex with hshifted
  have hltOne : ∀ atomIndex : Fin 6, shifted atomIndex < 1 := by
    intro atomIndex
    have hwle : (chartPointOfDesign crux.design).weight atomIndex ≤ 1 := by
      have hle : (chartPointOfDesign crux.design).weight atomIndex
          ≤ ∑ probe, (chartPointOfDesign crux.design).weight probe :=
        Finset.single_le_sum
          (f := fun probe => (chartPointOfDesign crux.design).weight probe)
          (fun probe _ => (data.hdata.weight_pos probe).le) (Finset.mem_univ atomIndex)
      rwa [data.hdata.weight_sum_one] at hle
    have hneg := data.hvalueNeg
    rw [hshifted]
    dsimp only
    linarith
  -- the nonzero leak of the second atom at the leak slot
  obtain ⟨dualVec, hdualFix, hseeOne, hseeTwo, hother⟩ :=
    data.exists_interior_dual_seers hposThree hinterior
      S readVecs hSsymm hSidem hStrace hsuppFrame hread hnorm hboundary hnz hspan hcommute
  have hleakNe : (S *ᵥ readVecs atomTwo) leakSlot ≠ 0 :=
    leak_ne_zero_of_fixed_pair hSsymm readVecs hcommute hdualFix hne12 hother hseeOne hseeTwo
      (hread atomOne leakSlot hcarryOneLeak) (hcarrierNz atomOne leakSlot hcarryOneLeak)
      (hltOne atomOne) (hsuppFrame atomTwo leakSlot hmissTwoLeak)
  -- the second atom is the unique separator of the slot pair
  refine hleakNe (leak_eq_zero_of_unique_separator readVecs hcommute ?_
    (hsuppFrame atomTwo leakSlot hmissTwoLeak) (hcarrierNz atomTwo carrierSlot hcarryTwoCar))
  intro atomIndex hnotTwo
  by_cases hpos : 0 < shifted atomIndex
  · rcases hinterior atomIndex hpos with heq | heq | heq
    · subst heq
      exact commutationTerm_of_carried (hread atomIndex leakSlot hcarryOneLeak)
        (hread atomIndex carrierSlot hcarryOneCar)
    · exact absurd heq hnotTwo
    · subst heq
      by_cases hmem : atomIndex ∈ datumTightSupport data.tightDir
          (data.basisLabel carrierSlot)
      · exact commutationTerm_of_carried
          (hread atomIndex leakSlot (hthreeSame.mpr hmem))
          (hread atomIndex carrierSlot hmem)
      · exact commutationTerm_of_missed
          (hsuppFrame atomIndex leakSlot fun hleak => hmem (hthreeSame.mp hleak))
          (hsuppFrame atomIndex carrierSlot hmem)
  · have hzero : shifted atomIndex = 0 := by
      rcases (capture_diagonal_nonneg_of_isChartStationaryData data.hdata
        atomIndex).lt_or_eq with hlt | heq
      · exact absurd hlt hpos
      · exact heq.symm
    exact commutationTerm_of_kernel (hboundary atomIndex hzero) leakSlot carrierSlot

end Gtz
