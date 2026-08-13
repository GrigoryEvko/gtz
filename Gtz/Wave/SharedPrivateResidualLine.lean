import Gtz.Wave.SharedPrivateCoparallelColumn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The residual line — the signature calculus that closes the trace-two
boundary stratum at basis count five

The trace-two boundary stratum carries exactly three interior atoms.  This
module reads that triple through ONE vector and closes the stratum with no
hypothesis left.

**THE RESIDUAL LINE.**  Write the residual of a read as the read minus its
own fixed part.  The commutant law of the read weight matrix, applied to the
dual vector of one interior atom, prices the residuals of the two atoms that
see it against each other.  Three dual vectors give three such prices, thus
**the three interior residuals are multiples of ONE vector `rho`.**  The line
`rho` sits in the kernel of the read idempotent, and it is nonzero at every
live slot.

**THE SIGNATURE CALCULUS.**  The fixed parts live in the plane of the
idempotent, thus the three of them carry a dependency whose coefficients are
the two-by-two minors of the plane coordinates.  Read that dependency at a
slot.  A carried read contributes its shifted weight times the line, and a
missed read contributes minus the line.  **Thus each slot gives one linear
equation in three unknowns, and the equation only knows WHICH interior atoms
carry the slot.**

Three kills come out of the calculus.

* **THE COMMON SLOT.**  The orthogonality of the fixed parts against the line
  gives `∑ over the carrier of rho² = (1 - shifted weight) * ∑ of rho²`.  The
  budget of the interior triple then forces a slot that all three atoms
  carry.
* **THE TWIN SLOTS.**  Two slots whose supports are exactly the interior
  triple make the line degenerate: the reads of every atom agree on the two
  slots up to the line, thus the span law kills a nonzero vector.
* **THE SIGNATURE QUADRUPLE.**  One slot with all three atoms plus three
  slots with one atom each force the dependency to vanish, and the plane
  minor of two reads is nonzero.

The dispatch needs nothing else.  When some other slot carries exactly two
interior atoms, the landed unique separator kill fires against the common
slot.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.plane_minor_ne_zero_of_dual` — **THE PLANE MINOR** of two reads is
  nonzero.
* `Gtz.plane_triple_dependency` — **THE PLANE DEPENDENCY** of three fixed
  parts.
* `Gtz.residual_pair_of_dual` — the commutant price of two residuals.
* `Gtz.carrier_residual_mass` — **THE CARRIER MASS** of the line.
* `Gtz.exists_common_carrier_slot` — **THE COMMON SLOT.**
* `Gtz.false_of_twin_slots` — **THE TWIN SLOT KILL.**
* `Gtz.false_of_signature_quadruple` — **THE SIGNATURE KILL.**
* `Gtz.SharedPrivateData.exists_residual_line` — **THE RESIDUAL LINE** of a
  trace-two datum with three interior atoms.
* `Gtz.SharedPrivateData.false_of_interior_triple` — the datum kill.
* `Gtz.sharedPrivateBoundaryFiveCarrierClosed` — **THE CARRIER RESIDUE IS A
  THEOREM.**
* `Gtz.sharedPrivateBoundaryFiveLeakClosed`,
  `Gtz.sharedPrivateBoundaryFiveConfinedClosed`,
  `Gtz.sharedPrivateBoundaryFiveCoreClosed`,
  `Gtz.sharedPrivateBoundaryFiveClosed`, `Gtz.sharedPrivateBoundaryClosed` —
  the five boundary residues below it.
* `Gtz.sharedPrivateKilled_of_extras`,
  `Gtz.rankFourSharedPrivateClosed_of_extras`,
  `Gtz.rankFiveSharedPrivateClosed_of_extras`,
  `Gtz.rankSixSharedPrivateClosed_of_extras` — closure two of the three
  rungs, with the extras residue as the only remaining hypothesis.

## Vacuity

The matrix statements are unconditional.  The datum statements quantify over
shared-private data, and no datum exists if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the plane of a trace-two idempotent -/

/-- A fixed vector of a trace-two idempotent is the combination of the
orthonormal pair with its own two coordinates. -/
theorem orthonormal_pair_of_fixed {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    {firstVec secondVec : Fin slotCount → ℝ}
    (hsplit : S = Matrix.vecMulVec firstVec firstVec
      + Matrix.vecMulVec secondVec secondVec)
    {probe : Fin slotCount → ℝ} (hfix : S *ᵥ probe = probe)
    (slot : Fin slotCount) :
    probe slot
      = firstVec slot * (firstVec ⬝ᵥ probe) + secondVec slot * (secondVec ⬝ᵥ probe) := by
  rw [← orthonormal_pair_mulVec hsplit probe slot, hfix]

/-- The pairing of a probe with a fixed vector, read in the plane. -/
theorem plane_pairing_eq {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    {firstVec secondVec : Fin slotCount → ℝ}
    (hsplit : S = Matrix.vecMulVec firstVec firstVec
      + Matrix.vecMulVec secondVec secondVec)
    {dualVec : Fin slotCount → ℝ} (hfix : S *ᵥ dualVec = dualVec)
    (probe : Fin slotCount → ℝ) :
    probe ⬝ᵥ dualVec
      = (firstVec ⬝ᵥ dualVec) * (firstVec ⬝ᵥ probe)
        + (secondVec ⬝ᵥ dualVec) * (secondVec ⬝ᵥ probe) := by
  classical
  have hterm : ∀ slot : Fin slotCount, probe slot * dualVec slot
      = (firstVec ⬝ᵥ dualVec) * (probe slot * firstVec slot)
        + (secondVec ⬝ᵥ dualVec) * (probe slot * secondVec slot) := by
    intro slot
    rw [orthonormal_pair_of_fixed hsplit hfix slot]
    ring
  rw [dotProduct, Finset.sum_congr rfl fun slot _ => hterm slot, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  rw [dotProduct_comm firstVec probe, dotProduct_comm secondVec probe]
  rfl

/-- **THE PLANE MINOR.**  When a fixed vector is blind to the first read and
sees the second one, the two-by-two minor of the plane coordinates of the
pair does not vanish.  A vanishing minor puts both coordinates of the first
read at zero, thus its fixed part vanishes. -/
theorem plane_minor_ne_zero_of_dual {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    {firstVec secondVec : Fin slotCount → ℝ}
    (hsplit : S = Matrix.vecMulVec firstVec firstVec
      + Matrix.vecMulVec secondVec secondVec)
    {probeOne probeTwo dualVec : Fin slotCount → ℝ}
    (hdualFix : S *ᵥ dualVec = dualVec)
    (hblind : probeOne ⬝ᵥ dualVec = 0) (hsee : probeTwo ⬝ᵥ dualVec ≠ 0)
    (hnzOne : S *ᵥ probeOne ≠ 0) :
    (firstVec ⬝ᵥ probeOne) * (secondVec ⬝ᵥ probeTwo)
      - (secondVec ⬝ᵥ probeOne) * (firstVec ⬝ᵥ probeTwo) ≠ 0 := by
  classical
  intro hzero
  have hone := plane_pairing_eq hsplit hdualFix probeOne
  have htwo := plane_pairing_eq hsplit hdualFix probeTwo
  rw [hblind] at hone
  -- the two coordinates of the blind read vanish
  have hfirstZero : firstVec ⬝ᵥ probeOne = 0 := by
    have hprod : (firstVec ⬝ᵥ probeOne) * (probeTwo ⬝ᵥ dualVec) = 0 := by
      rw [htwo]
      linear_combination (secondVec ⬝ᵥ dualVec) * hzero
        - (firstVec ⬝ᵥ probeTwo) * hone
    rcases mul_eq_zero.mp hprod with hcase | hcase
    · exact hcase
    · exact absurd hcase hsee
  have hsecondZero : secondVec ⬝ᵥ probeOne = 0 := by
    have hprod : (secondVec ⬝ᵥ probeOne) * (probeTwo ⬝ᵥ dualVec) = 0 := by
      rw [htwo]
      linear_combination -(firstVec ⬝ᵥ dualVec) * hzero
        - (secondVec ⬝ᵥ probeTwo) * hone
    rcases mul_eq_zero.mp hprod with hcase | hcase
    · exact hcase
    · exact absurd hcase hsee
  refine hnzOne (funext fun slot => ?_)
  rw [orthonormal_pair_mulVec hsplit probeOne slot, hfirstZero, hsecondZero]
  simp

/-- **THE PLANE DEPENDENCY.**  Three fixed parts of a trace-two idempotent
carry the dependency whose coefficients are the two-by-two minors of the
plane coordinates. -/
theorem plane_triple_dependency {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    {firstVec secondVec : Fin slotCount → ℝ}
    (hsplit : S = Matrix.vecMulVec firstVec firstVec
      + Matrix.vecMulVec secondVec secondVec)
    (probeU probeV probeW : Fin slotCount → ℝ) (slot : Fin slotCount) :
    ((firstVec ⬝ᵥ probeV) * (secondVec ⬝ᵥ probeW)
          - (secondVec ⬝ᵥ probeV) * (firstVec ⬝ᵥ probeW)) * (S *ᵥ probeU) slot
        + ((firstVec ⬝ᵥ probeW) * (secondVec ⬝ᵥ probeU)
          - (secondVec ⬝ᵥ probeW) * (firstVec ⬝ᵥ probeU)) * (S *ᵥ probeV) slot
        + ((firstVec ⬝ᵥ probeU) * (secondVec ⬝ᵥ probeV)
          - (secondVec ⬝ᵥ probeU) * (firstVec ⬝ᵥ probeV)) * (S *ᵥ probeW) slot = 0 := by
  rw [orthonormal_pair_mulVec hsplit probeU slot,
    orthonormal_pair_mulVec hsplit probeV slot,
    orthonormal_pair_mulVec hsplit probeW slot]
  ring

/-! ## Layer 2 — the commutant price of two residuals -/

/-- **THE RESIDUAL PAIR.**  When exactly two atoms see a fixed vector, the
read combination of the pair is fixed, thus the two residuals cancel each
other at every slot. -/
theorem residual_pair_of_dual {atomCount slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ} (hsymm : Sᵀ = S)
    (readVecs : Fin atomCount → Fin slotCount → ℝ)
    (hcommute : ∀ rowSlot colSlot : Fin slotCount,
      (∑ atomIndex, readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot)
        = ∑ atomIndex, (S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex colSlot)
    {probe : Fin slotCount → ℝ} (hfix : S *ᵥ probe = probe)
    {atomA atomB : Fin atomCount} (hne : atomA ≠ atomB)
    (hother : ∀ atomIndex : Fin atomCount, atomIndex ≠ atomA → atomIndex ≠ atomB →
      readVecs atomIndex ⬝ᵥ probe = 0) (slot : Fin slotCount) :
    (readVecs atomA ⬝ᵥ probe)
        * (readVecs atomA slot - (S *ᵥ readVecs atomA) slot)
      + (readVecs atomB ⬝ᵥ probe)
        * (readVecs atomB slot - (S *ᵥ readVecs atomB) slot) = 0 := by
  classical
  have hcomb := readCombination_fixed hsymm readVecs hcommute hfix
  rw [readCombination_of_pair readVecs probe hne hother] at hcomb
  have hentry := congrFun hcomb slot
  have hleft : (S *ᵥ fun rowSlot => (readVecs atomA ⬝ᵥ probe) * readVecs atomA rowSlot
        + (readVecs atomB ⬝ᵥ probe) * readVecs atomB rowSlot) slot
      = (readVecs atomA ⬝ᵥ probe) * (S *ᵥ readVecs atomA) slot
        + (readVecs atomB ⬝ᵥ probe) * (S *ᵥ readVecs atomB) slot := by
    show (∑ colSlot, S slot colSlot
        * ((readVecs atomA ⬝ᵥ probe) * readVecs atomA colSlot
          + (readVecs atomB ⬝ᵥ probe) * readVecs atomB colSlot))
      = (readVecs atomA ⬝ᵥ probe) * (S *ᵥ readVecs atomA) slot
        + (readVecs atomB ⬝ᵥ probe) * (S *ᵥ readVecs atomB) slot
    have hstepA : (S *ᵥ readVecs atomA) slot
        = ∑ colSlot, S slot colSlot * readVecs atomA colSlot := rfl
    have hstepB : (S *ᵥ readVecs atomB) slot
        = ∑ colSlot, S slot colSlot * readVecs atomB colSlot := rfl
    rw [hstepA, hstepB, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun colSlot _ => by ring
  rw [hleft] at hentry
  linear_combination -hentry

/-! ## Layer 3 — the carrier mass of the line -/

/-- **THE CARRIER MASS.**  The fixed part of a read is orthogonal to the
kernel line, thus the mass of the line on the carrier of that read is the
complementary weight of the total mass. -/
theorem carrier_residual_mass {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ} (hsymm : Sᵀ = S)
    {probe rho : Fin slotCount → ℝ} {carrier : Finset (Fin slotCount)}
    {weight coeff : ℝ}
    (hker : S *ᵥ rho = 0)
    (hsupp : ∀ slot : Fin slotCount, slot ∉ carrier → probe slot = 0)
    (hread : ∀ slot ∈ carrier, (S *ᵥ probe) slot = weight * probe slot)
    (hres : ∀ slot : Fin slotCount, probe slot - (S *ᵥ probe) slot = coeff * rho slot)
    (hcoeff : coeff ≠ 0) (hlt : weight < 1) :
    (∑ slot ∈ carrier, rho slot ^ 2)
      = (1 - weight) * ∑ slot : Fin slotCount, rho slot ^ 2 := by
  classical
  have hsub : (1 : ℝ) - weight ≠ 0 := by intro hzero; linarith
  -- the fixed part is orthogonal to the kernel line
  have horth : (∑ slot : Fin slotCount, (S *ᵥ probe) slot * rho slot) = 0 := by
    have hswap := dotProduct_mulVec_symm hsymm probe rho
    rw [hker, dotProduct_zero] at hswap
    exact hswap.symm
  -- the two readings of the fixed part
  have hon : ∀ slot ∈ carrier,
      (1 - weight) * ((S *ᵥ probe) slot * rho slot)
        = weight * coeff * rho slot ^ 2 := by
    intro slot hslot
    have hval := hread slot hslot
    have hresid := hres slot
    rw [hval] at hresid ⊢
    have hprobe : probe slot * (1 - weight) = coeff * rho slot := by linarith [hresid]
    linear_combination weight * rho slot * hprobe
  have hoff : ∀ slot ∉ carrier,
      (1 - weight) * ((S *ᵥ probe) slot * rho slot)
        = (-((1 - weight) * coeff)) * rho slot ^ 2 := by
    intro slot hslot
    have hzero := hsupp slot hslot
    have hresid := hres slot
    rw [hzero] at hresid
    have hfix : (S *ᵥ probe) slot = -(coeff * rho slot) := by linarith [hresid]
    rw [hfix]
    ring
  -- split the orthogonality along the carrier
  set total : ℝ := ∑ slot : Fin slotCount, rho slot ^ 2 with htotal
  set mass : ℝ := ∑ slot ∈ carrier, rho slot ^ 2 with hmass
  have hsplitMass : (∑ slot ∈ Finset.univ \ carrier, rho slot ^ 2) + mass = total := by
    rw [hmass, htotal]
    exact Finset.sum_sdiff (Finset.subset_univ carrier)
  have hsplitOrth : (∑ slot ∈ Finset.univ \ carrier,
        (1 - weight) * ((S *ᵥ probe) slot * rho slot))
      + ∑ slot ∈ carrier, (1 - weight) * ((S *ᵥ probe) slot * rho slot)
      = ∑ slot : Fin slotCount, (1 - weight) * ((S *ᵥ probe) slot * rho slot) :=
    Finset.sum_sdiff (Finset.subset_univ carrier)
  have hTotalOrth : (∑ slot : Fin slotCount,
      (1 - weight) * ((S *ᵥ probe) slot * rho slot)) = 0 := by
    rw [← Finset.mul_sum, horth, mul_zero]
  have hOnSum : (∑ slot ∈ carrier, (1 - weight) * ((S *ᵥ probe) slot * rho slot))
      = weight * coeff * mass := by
    rw [hmass, Finset.mul_sum]
    exact Finset.sum_congr rfl fun slot hslot => hon slot hslot
  have hOffSum : (∑ slot ∈ Finset.univ \ carrier,
        (1 - weight) * ((S *ᵥ probe) slot * rho slot))
      = (-((1 - weight) * coeff)) * ∑ slot ∈ Finset.univ \ carrier, rho slot ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun slot hslot =>
      hoff slot (Finset.mem_sdiff.mp hslot).2
  rw [hOnSum, hOffSum, hTotalOrth] at hsplitOrth
  have hoffMass : (∑ slot ∈ Finset.univ \ carrier, rho slot ^ 2) = total - mass := by
    linarith [hsplitMass]
  rw [hoffMass] at hsplitOrth
  have hfinal : coeff * (mass - (1 - weight) * total) = 0 := by
    linear_combination hsplitOrth
  rcases mul_eq_zero.mp hfinal with hcase | hcase
  · exact absurd hcase hcoeff
  · linarith [hcase]

/-- **THE COMMON SLOT.**  Three interior reads whose shifted weights total
less than one, all read through one kernel line, carry a common slot.  The
carrier masses total more than twice the mass of the line, and every slot
pays at most twice unless the three carriers meet there. -/
theorem exists_common_carrier_slot {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ} (hsymm : Sᵀ = S)
    {probeU probeV probeW rho : Fin slotCount → ℝ}
    {carU carV carW : Finset (Fin slotCount)}
    {weightU weightV weightW coeffU coeffV coeffW : ℝ}
    (hker : S *ᵥ rho = 0)
    (hsuppU : ∀ slot : Fin slotCount, slot ∉ carU → probeU slot = 0)
    (hreadU : ∀ slot ∈ carU, (S *ᵥ probeU) slot = weightU * probeU slot)
    (hresU : ∀ slot : Fin slotCount, probeU slot - (S *ᵥ probeU) slot = coeffU * rho slot)
    (hcoeffU : coeffU ≠ 0) (hltU : weightU < 1)
    (hsuppV : ∀ slot : Fin slotCount, slot ∉ carV → probeV slot = 0)
    (hreadV : ∀ slot ∈ carV, (S *ᵥ probeV) slot = weightV * probeV slot)
    (hresV : ∀ slot : Fin slotCount, probeV slot - (S *ᵥ probeV) slot = coeffV * rho slot)
    (hcoeffV : coeffV ≠ 0) (hltV : weightV < 1)
    (hsuppW : ∀ slot : Fin slotCount, slot ∉ carW → probeW slot = 0)
    (hreadW : ∀ slot ∈ carW, (S *ᵥ probeW) slot = weightW * probeW slot)
    (hresW : ∀ slot : Fin slotCount, probeW slot - (S *ᵥ probeW) slot = coeffW * rho slot)
    (hcoeffW : coeffW ≠ 0) (hltW : weightW < 1)
    (hbudget : weightU + weightV + weightW < 1)
    {baseSlot : Fin slotCount} (hbase : rho baseSlot ≠ 0) :
    ∃ slot : Fin slotCount, slot ∈ carU ∧ slot ∈ carV ∧ slot ∈ carW := by
  classical
  by_contra hnone
  simp only [not_exists, not_and] at hnone
  set total : ℝ := ∑ slot : Fin slotCount, rho slot ^ 2 with htotal
  have hbasePos : 0 < rho baseSlot ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hbase))
  have hpos : 0 < total := by
    rw [htotal]
    exact Finset.sum_pos' (fun slot _ => sq_nonneg (rho slot))
      ⟨baseSlot, Finset.mem_univ _, hbasePos⟩
  have hmassU := carrier_residual_mass hsymm hker hsuppU hreadU hresU hcoeffU hltU
  have hmassV := carrier_residual_mass hsymm hker hsuppV hreadV hresV hcoeffV hltV
  have hmassW := carrier_residual_mass hsymm hker hsuppW hreadW hresW hcoeffW hltW
  -- each mass, written as a total over all slots
  have hfilter : ∀ car : Finset (Fin slotCount),
      (∑ slot ∈ car, rho slot ^ 2)
        = ∑ slot : Fin slotCount, if slot ∈ car then rho slot ^ 2 else 0 := by
    intro car
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hcap : ∀ slot : Fin slotCount,
      (if slot ∈ carU then rho slot ^ 2 else 0)
        + (if slot ∈ carV then rho slot ^ 2 else 0)
        + (if slot ∈ carW then rho slot ^ 2 else 0)
      ≤ 2 * rho slot ^ 2 := by
    intro slot
    have hsq : (0 : ℝ) ≤ rho slot ^ 2 := sq_nonneg _
    by_cases hu : slot ∈ carU
    · rw [if_pos hu]
      by_cases hv : slot ∈ carV
      · rw [if_pos hv, if_neg (hnone slot hu hv)]
        linarith
      · rw [if_neg hv]
        by_cases hw : slot ∈ carW
        · rw [if_pos hw]; linarith
        · rw [if_neg hw]; linarith
    · rw [if_neg hu]
      by_cases hv : slot ∈ carV
      · rw [if_pos hv]
        by_cases hw : slot ∈ carW
        · rw [if_pos hw]; linarith
        · rw [if_neg hw]; linarith
      · rw [if_neg hv]
        by_cases hw : slot ∈ carW
        · rw [if_pos hw]; linarith
        · rw [if_neg hw]; linarith
  have hsumCap : (∑ slot ∈ carU, rho slot ^ 2) + (∑ slot ∈ carV, rho slot ^ 2)
      + ∑ slot ∈ carW, rho slot ^ 2 ≤ 2 * total := by
    rw [hfilter carU, hfilter carV, hfilter carW, htotal, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun slot _ => hcap slot
  rw [hmassU, hmassV, hmassW] at hsumCap
  nlinarith [hsumCap, hpos, hbudget]

/-! ## Layer 4 — the twin slot kill -/

/-- **THE TWIN SLOTS.**  Two slots on which every read agrees up to the
kernel line make a nonzero vector that no read sees, and the span law refuses
it. -/
theorem false_of_twin_slots {atomCount slotCount : ℕ}
    (readVecs : Fin atomCount → Fin slotCount → ℝ) (rho : Fin slotCount → ℝ)
    (hspan : ∀ testVec : Fin slotCount → ℝ,
      (∀ atomIndex : Fin atomCount, readVecs atomIndex ⬝ᵥ testVec = 0) → testVec = 0)
    {slotOne slotTwo : Fin slotCount} (hne : slotOne ≠ slotTwo)
    (hrho : rho slotTwo ≠ 0)
    (htwin : ∀ atomIndex : Fin atomCount,
      rho slotTwo * readVecs atomIndex slotOne
        = rho slotOne * readVecs atomIndex slotTwo) :
    False := by
  classical
  set testVec : Fin slotCount → ℝ := fun slot =>
    if slot = slotOne then rho slotTwo
    else if slot = slotTwo then -(rho slotOne) else 0 with htest
  have hone : testVec slotOne = rho slotTwo := by simp [htest]
  have htwo : testVec slotTwo = -(rho slotOne) := by simp [htest, Ne.symm hne]
  have hblind : ∀ atomIndex : Fin atomCount, readVecs atomIndex ⬝ᵥ testVec = 0 := by
    intro atomIndex
    have hrestrict : (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin slotCount)),
          readVecs atomIndex slot * testVec slot)
        = ∑ slot : Fin slotCount, readVecs atomIndex slot * testVec slot := by
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro slot _ hnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      have hval : testVec slot = 0 := by
        rw [htest]
        simp only [if_neg hnot.1, if_neg hnot.2]
      rw [hval, mul_zero]
    rw [dotProduct, ← hrestrict, Finset.sum_pair hne, hone, htwo]
    linear_combination htwin atomIndex
  have hzero := hspan testVec hblind
  have hentry : rho slotTwo = 0 := by
    rw [← hone, hzero]
    simp
  exact hrho hentry

/-! ## Layer 5 — the signature kill -/

/-- The fixed part at a carried slot, priced by the line. -/
theorem fixed_part_carried {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    {probe rho : Fin slotCount → ℝ} {weight coeff : ℝ} {slot : Fin slotCount}
    (hread : (S *ᵥ probe) slot = weight * probe slot)
    (hres : probe slot - (S *ᵥ probe) slot = coeff * rho slot) :
    (1 - weight) * (S *ᵥ probe) slot = weight * (coeff * rho slot) := by
  rw [hread] at hres ⊢
  linear_combination weight * hres

/-- The fixed part at a missed slot, priced by the line. -/
theorem fixed_part_missed {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    {probe rho : Fin slotCount → ℝ} {coeff : ℝ} {slot : Fin slotCount}
    (hmiss : probe slot = 0)
    (hres : probe slot - (S *ᵥ probe) slot = coeff * rho slot) :
    (S *ᵥ probe) slot = -(coeff * rho slot) := by
  rw [hmiss] at hres
  linarith [hres]

set_option maxHeartbeats 1600000 in
/-- **THE SIGNATURE KILL.**  One slot that all three interior reads carry,
together with three slots that carry exactly one of them each, force every
plane minor to vanish.  The dual vector of the first read refuses that. -/
theorem false_of_signature_quadruple {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (htrace : Matrix.trace S = 2)
    {probeU probeV probeW rho dualVec : Fin slotCount → ℝ}
    {weightU weightV weightW coeffU coeffV coeffW : ℝ}
    (hltU : weightU < 1) (hltV : weightV < 1) (hltW : weightW < 1)
    (hcoeffW : coeffW ≠ 0)
    (hresU : ∀ slot : Fin slotCount, probeU slot - (S *ᵥ probeU) slot = coeffU * rho slot)
    (hresV : ∀ slot : Fin slotCount, probeV slot - (S *ᵥ probeV) slot = coeffV * rho slot)
    (hresW : ∀ slot : Fin slotCount, probeW slot - (S *ᵥ probeW) slot = coeffW * rho slot)
    {slotU slotV slotW slotAll : Fin slotCount}
    (hrhoU : rho slotU ≠ 0) (hrhoV : rho slotV ≠ 0) (hrhoW : rho slotW ≠ 0)
    (hrhoAll : rho slotAll ≠ 0)
    (hcarUU : (S *ᵥ probeU) slotU = weightU * probeU slotU)
    (hmissVU : probeV slotU = 0) (hmissWU : probeW slotU = 0)
    (hcarVV : (S *ᵥ probeV) slotV = weightV * probeV slotV)
    (hmissUV : probeU slotV = 0) (hmissWV : probeW slotV = 0)
    (hcarWW : (S *ᵥ probeW) slotW = weightW * probeW slotW)
    (hmissUW : probeU slotW = 0) (hmissVW : probeV slotW = 0)
    (hcarUA : (S *ᵥ probeU) slotAll = weightU * probeU slotAll)
    (hcarVA : (S *ᵥ probeV) slotAll = weightV * probeV slotAll)
    (hcarWA : (S *ᵥ probeW) slotAll = weightW * probeW slotAll)
    (hdualFix : S *ᵥ dualVec = dualVec)
    (hblind : probeU ⬝ᵥ dualVec = 0) (hsee : probeV ⬝ᵥ dualVec ≠ 0)
    (hnzU : S *ᵥ probeU ≠ 0) : False := by
  classical
  obtain ⟨firstVec, secondVec, hfirstUnit, hsecondUnit, hcross, hsplit⟩ :=
    exists_orthonormal_pair_of_trace_two hsymm hidem htrace
  set minorU : ℝ := (firstVec ⬝ᵥ probeV) * (secondVec ⬝ᵥ probeW)
    - (secondVec ⬝ᵥ probeV) * (firstVec ⬝ᵥ probeW) with hminorU
  set minorV : ℝ := (firstVec ⬝ᵥ probeW) * (secondVec ⬝ᵥ probeU)
    - (secondVec ⬝ᵥ probeW) * (firstVec ⬝ᵥ probeU) with hminorV
  set minorW : ℝ := (firstVec ⬝ᵥ probeU) * (secondVec ⬝ᵥ probeV)
    - (secondVec ⬝ᵥ probeU) * (firstVec ⬝ᵥ probeV) with hminorW
  have hminorNe : minorW ≠ 0 := by
    rw [hminorW]
    exact plane_minor_ne_zero_of_dual hsplit hdualFix hblind hsee hnzU
  set liftU : ℝ := minorU * coeffU with hliftU
  set liftV : ℝ := minorV * coeffV with hliftV
  set liftW : ℝ := minorW * coeffW with hliftW
  have hsubU : (1 : ℝ) - weightU ≠ 0 := by intro hzero; linarith
  have hsubV : (1 : ℝ) - weightV ≠ 0 := by intro hzero; linarith
  have hsubW : (1 : ℝ) - weightW ≠ 0 := by intro hzero; linarith
  -- the four dependency readings
  have hdepU := plane_triple_dependency hsplit probeU probeV probeW slotU
  have hdepV := plane_triple_dependency hsplit probeU probeV probeW slotV
  have hdepW := plane_triple_dependency hsplit probeU probeV probeW slotW
  have hdepA := plane_triple_dependency hsplit probeU probeV probeW slotAll
  rw [← hminorU, ← hminorV, ← hminorW] at hdepU hdepV hdepW hdepA
  -- the singleton slot of the first read
  have hfixUU := fixed_part_carried hcarUU (hresU slotU)
  have hfixVU := fixed_part_missed hmissVU (hresV slotU)
  have hfixWU := fixed_part_missed hmissWU (hresW slotU)
  have heqU : weightU * liftU = (1 - weightU) * (liftV + liftW) := by
    have hprod : rho slotU * (weightU * liftU - (1 - weightU) * (liftV + liftW)) = 0 := by
      rw [hliftU, hliftV, hliftW]
      linear_combination (1 - weightU) * hdepU - minorU * hfixUU
        - (1 - weightU) * minorV * hfixVU - (1 - weightU) * minorW * hfixWU
    rcases mul_eq_zero.mp hprod with hcase | hcase
    · exact absurd hcase hrhoU
    · linarith [hcase]
  -- the singleton slot of the second read
  have hfixVV := fixed_part_carried hcarVV (hresV slotV)
  have hfixUV := fixed_part_missed hmissUV (hresU slotV)
  have hfixWV := fixed_part_missed hmissWV (hresW slotV)
  have heqV : weightV * liftV = (1 - weightV) * (liftU + liftW) := by
    have hprod : rho slotV * (weightV * liftV - (1 - weightV) * (liftU + liftW)) = 0 := by
      rw [hliftU, hliftV, hliftW]
      linear_combination (1 - weightV) * hdepV - minorV * hfixVV
        - (1 - weightV) * minorU * hfixUV - (1 - weightV) * minorW * hfixWV
    rcases mul_eq_zero.mp hprod with hcase | hcase
    · exact absurd hcase hrhoV
    · linarith [hcase]
  -- the singleton slot of the third read
  have hfixWW := fixed_part_carried hcarWW (hresW slotW)
  have hfixUW := fixed_part_missed hmissUW (hresU slotW)
  have hfixVW := fixed_part_missed hmissVW (hresV slotW)
  have heqW : weightW * liftW = (1 - weightW) * (liftU + liftV) := by
    have hprod : rho slotW * (weightW * liftW - (1 - weightW) * (liftU + liftV)) = 0 := by
      rw [hliftU, hliftV, hliftW]
      linear_combination (1 - weightW) * hdepW - minorW * hfixWW
        - (1 - weightW) * minorU * hfixUW - (1 - weightW) * minorV * hfixVW
    rcases mul_eq_zero.mp hprod with hcase | hcase
    · exact absurd hcase hrhoW
    · linarith [hcase]
  -- the common slot
  have hfixUA := fixed_part_carried hcarUA (hresU slotAll)
  have hfixVA := fixed_part_carried hcarVA (hresV slotAll)
  have hfixWA := fixed_part_carried hcarWA (hresW slotAll)
  have heqA : (1 - weightV) * (1 - weightW) * (weightU * liftU)
      + (1 - weightU) * (1 - weightW) * (weightV * liftV)
      + (1 - weightU) * (1 - weightV) * (weightW * liftW) = 0 := by
    have hprod : rho slotAll * ((1 - weightV) * (1 - weightW) * (weightU * liftU)
        + (1 - weightU) * (1 - weightW) * (weightV * liftV)
        + (1 - weightU) * (1 - weightV) * (weightW * liftW)) = 0 := by
      rw [hliftU, hliftV, hliftW]
      linear_combination (1 - weightU) * (1 - weightV) * (1 - weightW) * hdepA
        - (1 - weightV) * (1 - weightW) * minorU * hfixUA
        - (1 - weightU) * (1 - weightW) * minorV * hfixVA
        - (1 - weightU) * (1 - weightV) * minorW * hfixWA
    rcases mul_eq_zero.mp hprod with hcase | hcase
    · exact absurd hcase hrhoAll
    · exact hcase
  -- the total of the three lifts vanishes
  have hkey : (1 - weightU) * (1 - weightV) * (1 - weightW) * (2 * (liftU + liftV + liftW))
      = 0 := by
    linear_combination heqA - (1 - weightV) * (1 - weightW) * heqU
      - (1 - weightU) * (1 - weightW) * heqV - (1 - weightU) * (1 - weightV) * heqW
  have hsum : liftU + liftV + liftW = 0 := by
    have hprod := hkey
    rcases mul_eq_zero.mp hprod with hcase | hcase
    · rcases mul_eq_zero.mp hcase with hcase2 | hcase2
      · rcases mul_eq_zero.mp hcase2 with hcase3 | hcase3
        · exact absurd hcase3 hsubU
        · exact absurd hcase3 hsubV
      · exact absurd hcase2 hsubW
    · linarith [hcase]
  -- thus every lift vanishes, and the third minor with it
  have hliftWzero : liftW = 0 := by
    linear_combination heqW + (1 - weightW) * hsum
  rw [hliftW] at hliftWzero
  rcases mul_eq_zero.mp hliftWzero with hcase | hcase
  · exact hminorNe hcase
  · exact hcoeffW hcase


/-! ## Layer 6 — the residual line of a trace-two datum -/

/-- The shifted weight of an atom is below one: the weight is capped by the
weight total and the chart value is negative. -/
theorem SharedPrivateData.shifted_lt_one {crux : SixThreeCrux}
    (data : SharedPrivateData crux) (atomIndex : Fin 6) :
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex < 1 := by
  have hwle : (chartPointOfDesign crux.design).weight atomIndex ≤ 1 := by
    have hle : (chartPointOfDesign crux.design).weight atomIndex
        ≤ ∑ probe, (chartPointOfDesign crux.design).weight probe :=
      Finset.single_le_sum
        (f := fun probe => (chartPointOfDesign crux.design).weight probe)
        (fun probe _ => (data.hdata.weight_pos probe).le) (Finset.mem_univ atomIndex)
    rwa [data.hdata.weight_sum_one] at hle
  have hneg := data.hvalueNeg
  linarith

set_option maxHeartbeats 3200000 in
/-- **THE RESIDUAL LINE.**  A trace-two datum with exactly three interior
atoms reads all three residuals through ONE kernel line.  The dual vector of
one interior atom prices the residuals of the other two against each other,
and two dual vectors give the whole line.  The line is nonzero at every live
slot, because the leak of a read never vanishes there. -/
theorem SharedPrivateData.exists_residual_line {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2)
    {atomU atomV atomW : Fin 6}
    (hneUV : atomU ≠ atomV) (hneUW : atomU ≠ atomW) (hneVW : atomV ≠ atomW)
    (hposU : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomU)
    (hposV : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomV)
    (_hposW : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomW)
    (hinterior : ∀ probe : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe →
      probe = atomU ∨ probe = atomV ∨ probe = atomW) :
    ∃ (S : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ)
      (readVecs : Fin 6 → Fin data.basisCount → ℝ)
      (rho : Fin data.basisCount → ℝ) (coeffU coeffV coeffW : ℝ)
      (dualVec : Fin data.basisCount → ℝ),
      Sᵀ = S ∧ S * S = S ∧ Matrix.trace S = 2
      ∧ (∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
          atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot) →
          readVecs atomIndex slot = 0)
      ∧ (∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
          atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
          (S *ᵥ readVecs atomIndex) slot
            = (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomIndex)
              * readVecs atomIndex slot)
      ∧ (∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
          atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
          readVecs atomIndex slot ≠ 0)
      ∧ (∀ testVec : Fin data.basisCount → ℝ,
          (∀ atomIndex : Fin 6, readVecs atomIndex ⬝ᵥ testVec = 0) → testVec = 0)
      ∧ S *ᵥ rho = 0
      ∧ coeffU ≠ 0 ∧ coeffV ≠ 0 ∧ coeffW ≠ 0
      ∧ (∀ slot : Fin data.basisCount,
          readVecs atomU slot - (S *ᵥ readVecs atomU) slot = coeffU * rho slot)
      ∧ (∀ slot : Fin data.basisCount,
          readVecs atomV slot - (S *ᵥ readVecs atomV) slot = coeffV * rho slot)
      ∧ (∀ slot : Fin data.basisCount,
          readVecs atomW slot - (S *ᵥ readVecs atomW) slot = coeffW * rho slot)
      ∧ (∀ slot : Fin data.basisCount, ∀ probe : Fin 6,
          0 < chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight probe →
          probe ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
          rho slot ≠ 0)
      ∧ S *ᵥ dualVec = dualVec
      ∧ readVecs atomU ⬝ᵥ dualVec = 0 ∧ readVecs atomV ⬝ᵥ dualVec ≠ 0
      ∧ S *ᵥ readVecs atomU ≠ 0 := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStraceRaw, hsuppFrame, hread, hnorm,
    hboundary, hcarrierNz, hnz, hspan, hcommute, _hdeadCol⟩ :=
    data.exists_full_read_frame hdiag
  have hStrace : Matrix.trace S = 2 := by rw [hStraceRaw, htrace]
  have hltOne : ∀ atomIndex : Fin 6,
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex < 1 :=
    data.shifted_lt_one
  -- the two dual vectors
  have hinteriorU : ∀ probe : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe →
      probe = atomV ∨ probe = atomW ∨ probe = atomU := by
    intro probe hp
    rcases hinterior probe hp with hcase | hcase | hcase
    · exact Or.inr (Or.inr hcase)
    · exact Or.inl hcase
    · exact Or.inr (Or.inl hcase)
  have hinteriorV : ∀ probe : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe →
      probe = atomU ∨ probe = atomW ∨ probe = atomV := by
    intro probe hp
    rcases hinterior probe hp with hcase | hcase | hcase
    · exact Or.inl hcase
    · exact Or.inr (Or.inr hcase)
    · exact Or.inr (Or.inl hcase)
  obtain ⟨dualU, hdualUFix, hseeVU, hseeWU, hotherU⟩ :=
    data.exists_interior_dual_seers hposU hinteriorU S readVecs hSsymm hSidem hStrace
      hsuppFrame hread hnorm hboundary hnz hspan hcommute
  obtain ⟨dualV, hdualVFix, hseeUV, hseeWV, hotherV⟩ :=
    data.exists_interior_dual_seers hposV hinteriorV S readVecs hSsymm hSidem hStrace
      hsuppFrame hread hnorm hboundary hnz hspan hcommute
  have hblindU : readVecs atomU ⬝ᵥ dualU = 0 := hotherU atomU hneUV hneUW
  -- the line and the three coefficients
  set rho : Fin data.basisCount → ℝ := fun slot =>
    readVecs atomW slot - (S *ᵥ readVecs atomW) slot with hrho
  have hrhoApply : ∀ slot : Fin data.basisCount,
      rho slot = readVecs atomW slot - (S *ᵥ readVecs atomW) slot := fun _ => rfl
  set coeffV : ℝ := -((readVecs atomW ⬝ᵥ dualU) / (readVecs atomV ⬝ᵥ dualU)) with hcoeffVdef
  set coeffU : ℝ := -((readVecs atomW ⬝ᵥ dualV) / (readVecs atomU ⬝ᵥ dualV)) with hcoeffUdef
  have hcoeffVne : coeffV ≠ 0 := by
    rw [hcoeffVdef, neg_ne_zero]
    exact div_ne_zero hseeWU hseeVU
  have hcoeffUne : coeffU ≠ 0 := by
    rw [hcoeffUdef, neg_ne_zero]
    exact div_ne_zero hseeWV hseeUV
  have hresW : ∀ slot : Fin data.basisCount,
      readVecs atomW slot - (S *ᵥ readVecs atomW) slot = (1 : ℝ) * rho slot := by
    intro slot
    rw [hrhoApply slot, one_mul]
  have hresV : ∀ slot : Fin data.basisCount,
      readVecs atomV slot - (S *ᵥ readVecs atomV) slot = coeffV * rho slot := by
    intro slot
    have hpair := residual_pair_of_dual hSsymm readVecs hcommute hdualUFix hneVW hotherU slot
    rw [hcoeffVdef, hrhoApply slot]
    field_simp
    linarith [hpair]
  have hresU : ∀ slot : Fin data.basisCount,
      readVecs atomU slot - (S *ᵥ readVecs atomU) slot = coeffU * rho slot := by
    intro slot
    have hpair := residual_pair_of_dual hSsymm readVecs hcommute hdualVFix hneUW hotherV slot
    rw [hcoeffUdef, hrhoApply slot]
    field_simp
    linarith [hpair]
  have hrhoKer : S *ᵥ rho = 0 := by
    funext slot
    have hstep : (S *ᵥ rho) slot
        = (S *ᵥ readVecs atomW) slot - (S *ᵥ (S *ᵥ readVecs atomW)) slot := by
      show (∑ colSlot, S slot colSlot * rho colSlot)
        = (∑ colSlot, S slot colSlot * readVecs atomW colSlot)
          - ∑ colSlot, S slot colSlot * (S *ᵥ readVecs atomW) colSlot
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun colSlot _ => by rw [hrhoApply colSlot]; ring
    simp only [Pi.zero_apply]
    rw [hstep, Matrix.mulVec_mulVec, hSidem, sub_self]
  -- the line is nonzero at every live slot
  have hrhoLive : ∀ slot : Fin data.basisCount, ∀ probe : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe →
      probe ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      rho slot ≠ 0 := by
    intro slot probe hpos hmem
    by_cases hcarry : atomW ∈ datumTightSupport data.tightDir (data.basisLabel slot)
    · have hval := hread atomW slot hcarry
      have hnzVal := hcarrierNz atomW slot hcarry
      rw [hrhoApply slot, hval]
      intro hzero
      have hfactor : (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomW)) * readVecs atomW slot = 0 := by
        linarith [hzero]
      rcases mul_eq_zero.mp hfactor with hcase | hcase
      · have := hltOne atomW; linarith
      · exact hnzVal hcase
    · have hmiss : readVecs atomW slot = 0 := hsuppFrame atomW slot hcarry
      have hleak : (S *ᵥ readVecs atomW) slot ≠ 0 := by
        rcases hinterior probe hpos with hcase | hcase | hcase
        · subst hcase
          exact leak_ne_zero_of_fixed_pair hSsymm readVecs hcommute hdualVFix hneUW hotherV
            hseeUV hseeWV (hread probe slot hmem) (hcarrierNz probe slot hmem)
            (hltOne probe) hmiss
        · subst hcase
          exact leak_ne_zero_of_fixed_pair hSsymm readVecs hcommute hdualUFix hneVW hotherU
            hseeVU hseeWU (hread probe slot hmem) (hcarrierNz probe slot hmem)
            (hltOne probe) hmiss
        · exact absurd (hcase ▸ hmem) hcarry
      rw [hrhoApply slot, hmiss]
      intro hzero
      exact hleak (by linarith [hzero])
  -- the fixed part of the first read is nonzero
  have hnzFixU : S *ᵥ readVecs atomU ≠ 0 := by
    obtain ⟨pinSlot, hpinNe⟩ : ∃ pinSlot : Fin data.basisCount,
        readVecs atomU pinSlot ≠ 0 := by
      by_contra hnone
      simp only [not_exists, not_not] at hnone
      exact hnz atomU (funext hnone)
    have hmemPin : atomU ∈ datumTightSupport data.tightDir (data.basisLabel pinSlot) := by
      by_contra hnot
      exact hpinNe (hsuppFrame atomU pinSlot hnot)
    intro hzero
    have hentry := congrFun hzero pinSlot
    rw [hread atomU pinSlot hmemPin] at hentry
    rcases mul_eq_zero.mp hentry with hcase | hcase
    · linarith [hposU]
    · exact hpinNe hcase
  exact ⟨S, readVecs, rho, coeffU, coeffV, 1, dualU, hSsymm, hSidem, hStrace,
    hsuppFrame, hread, hcarrierNz, hspan, hrhoKer, hcoeffUne, hcoeffVne, one_ne_zero,
    hresU, hresV, hresW, hrhoLive, hdualUFix, hblindU, hseeVU, hnzFixU⟩

/-! ## Layer 7 — the datum kill -/

set_option maxHeartbeats 3200000 in
/-- **THE INTERIOR TRIPLE KILL.**  A trace-two datum with exactly three
interior atoms cannot exist.  The residual line puts a slot that all three
atoms carry.  A second such slot is a twin pair, a slot with exactly two of
them has a unique separator, and otherwise the three singleton slots make the
signature quadruple. -/
theorem SharedPrivateData.false_of_interior_triple {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2)
    {atomU atomV atomW : Fin 6}
    (hneUV : atomU ≠ atomV) (hneUW : atomU ≠ atomW) (hneVW : atomV ≠ atomW)
    (hposU : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomU)
    (hposV : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomV)
    (hposW : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomW)
    (hinterior : ∀ probe : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe →
      probe = atomU ∨ probe = atomV ∨ probe = atomW)
    (hthick : ∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex →
      2 ≤ basisSupportMultiplicity data.tightDir data.basisLabel atomIndex) :
    False := by
  classical
  obtain ⟨S, readVecs, rho, coeffU, coeffV, coeffW, dualVec,
    hSsymm, hSidem, hStrace, hsuppFrame, hread, hcarrierNz, hspan, hrhoKer,
    hcoeffU, hcoeffV, hcoeffW, hresU, hresV, hresW, hrhoLive,
    hdualFix, hblind, hsee, hnzFixU⟩ :=
    data.exists_residual_line hdiag htrace hneUV hneUW hneVW hposU hposV hposW hinterior
  set carU : Finset (Fin data.basisCount) := Finset.univ.filter fun slot =>
    atomU ∈ datumTightSupport data.tightDir (data.basisLabel slot) with hcarUdef
  set carV : Finset (Fin data.basisCount) := Finset.univ.filter fun slot =>
    atomV ∈ datumTightSupport data.tightDir (data.basisLabel slot) with hcarVdef
  set carW : Finset (Fin data.basisCount) := Finset.univ.filter fun slot =>
    atomW ∈ datumTightSupport data.tightDir (data.basisLabel slot) with hcarWdef
  have hmemU : ∀ slot : Fin data.basisCount, slot ∈ carU ↔
      atomU ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
    intro slot; rw [hcarUdef]; simp
  have hmemV : ∀ slot : Fin data.basisCount, slot ∈ carV ↔
      atomV ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
    intro slot; rw [hcarVdef]; simp
  have hmemW : ∀ slot : Fin data.basisCount, slot ∈ carW ↔
      atomW ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
    intro slot; rw [hcarWdef]; simp
  have hcardU : carU.card = basisSupportMultiplicity data.tightDir data.basisLabel atomU := rfl
  have hcardV : carV.card = basisSupportMultiplicity data.tightDir data.basisLabel atomV := rfl
  have hcardW : carW.card = basisSupportMultiplicity data.tightDir data.basisLabel atomW := rfl
  have hthickU : 2 ≤ carU.card := by rw [hcardU]; exact hthick atomU hposU
  have hthickV : 2 ≤ carV.card := by rw [hcardV]; exact hthick atomV hposV
  have hthickW : 2 ≤ carW.card := by rw [hcardW]; exact hthick atomW hposW
  -- the budget of the interior triple
  have hbudget := data.shifted_weight_triple_lt_one hneUV hneUW hneVW
  -- a base slot where the line is alive
  obtain ⟨baseSlot, hbaseMem⟩ : ∃ slot : Fin data.basisCount, slot ∈ carU :=
    Finset.card_pos.mp (by omega)
  have hbase : rho baseSlot ≠ 0 :=
    hrhoLive baseSlot atomU hposU ((hmemU baseSlot).mp hbaseMem)
  -- the common slot
  obtain ⟨slotAll, hallU, hallV, hallW⟩ :=
    exists_common_carrier_slot (carU := carU) (carV := carV) (carW := carW) hSsymm hrhoKer
      (fun slot hslot => hsuppFrame atomU slot fun hmem => hslot ((hmemU slot).mpr hmem))
      (fun slot hslot => hread atomU slot ((hmemU slot).mp hslot))
      hresU hcoeffU (data.shifted_lt_one atomU)
      (fun slot hslot => hsuppFrame atomV slot fun hmem => hslot ((hmemV slot).mpr hmem))
      (fun slot hslot => hread atomV slot ((hmemV slot).mp hslot))
      hresV hcoeffV (data.shifted_lt_one atomV)
      (fun slot hslot => hsuppFrame atomW slot fun hmem => hslot ((hmemW slot).mpr hmem))
      (fun slot hslot => hread atomW slot ((hmemW slot).mp hslot))
      hresW hcoeffW (data.shifted_lt_one atomW) hbudget hbase
  have hallUmem : atomU ∈ datumTightSupport data.tightDir (data.basisLabel slotAll) :=
    (hmemU slotAll).mp hallU
  have hallVmem : atomV ∈ datumTightSupport data.tightDir (data.basisLabel slotAll) :=
    (hmemV slotAll).mp hallV
  have hallWmem : atomW ∈ datumTightSupport data.tightDir (data.basisLabel slotAll) :=
    (hmemW slotAll).mp hallW
  have hrhoAll : rho slotAll ≠ 0 := hrhoLive slotAll atomU hposU hallUmem
  -- a slot with the whole triple has the triple as its support
  have hsupportEq : ∀ slot : Fin data.basisCount,
      atomU ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      atomV ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      atomW ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      ∀ probe : Fin 6,
        probe ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
        probe = atomU ∨ probe = atomV ∨ probe = atomW := by
    intro slot hu hv hw probe hp
    have hsub : ({atomU, atomV, atomW} : Finset (Fin 6))
        ⊆ datumTightSupport data.tightDir (data.basisLabel slot) := by
      intro other hother
      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
      rcases hother with heq | heq | heq
      · rw [heq]; exact hu
      · rw [heq]; exact hv
      · rw [heq]; exact hw
    have hcard3 : ({atomU, atomV, atomW} : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hneUV, hneUW]),
        Finset.card_insert_of_notMem (by simp [hneVW]), Finset.card_singleton]
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by rw [data.support_card_three, hcard3])
    rw [← heq] at hp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hp
  by_cases htwin : ∃ slotTwin : Fin data.basisCount, slotTwin ≠ slotAll
      ∧ atomU ∈ datumTightSupport data.tightDir (data.basisLabel slotTwin)
      ∧ atomV ∈ datumTightSupport data.tightDir (data.basisLabel slotTwin)
      ∧ atomW ∈ datumTightSupport data.tightDir (data.basisLabel slotTwin)
  · -- THE TWIN SLOT KILL
    obtain ⟨slotTwin, hneTwin, htwinU, htwinV, htwinW⟩ := htwin
    have hrhoTwin : rho slotTwin ≠ 0 := hrhoLive slotTwin atomU hposU htwinU
    refine false_of_twin_slots readVecs rho hspan (Ne.symm hneTwin) hrhoTwin ?_
    intro atomIndex
    have hcarried : ∀ atomProbe : Fin 6, ∀ coeff : ℝ,
        (∀ slot : Fin data.basisCount,
          readVecs atomProbe slot - (S *ᵥ readVecs atomProbe) slot = coeff * rho slot) →
        atomProbe ∈ datumTightSupport data.tightDir (data.basisLabel slotAll) →
        atomProbe ∈ datumTightSupport data.tightDir (data.basisLabel slotTwin) →
        rho slotTwin * readVecs atomProbe slotAll
          = rho slotAll * readVecs atomProbe slotTwin := by
      intro atomProbe coeff hres hmemAll hmemTwin
      have hone := hres slotAll
      have htwo := hres slotTwin
      rw [hread atomProbe slotAll hmemAll] at hone
      rw [hread atomProbe slotTwin hmemTwin] at htwo
      have hlt := data.shifted_lt_one atomProbe
      have hsubNe : (1 : ℝ) - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomProbe) ≠ 0 := by
        intro hzero; linarith
      have hprod : ((1 : ℝ) - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomProbe))
          * (rho slotTwin * readVecs atomProbe slotAll
            - rho slotAll * readVecs atomProbe slotTwin) = 0 := by
        linear_combination rho slotTwin * hone - rho slotAll * htwo
      rcases mul_eq_zero.mp hprod with hcase | hcase
      · exact absurd hcase hsubNe
      · linarith [hcase]
    by_cases hcaseU : atomIndex = atomU
    · rw [hcaseU]; exact hcarried atomU coeffU hresU hallUmem htwinU
    by_cases hcaseV : atomIndex = atomV
    · rw [hcaseV]; exact hcarried atomV coeffV hresV hallVmem htwinV
    by_cases hcaseW : atomIndex = atomW
    · rw [hcaseW]; exact hcarried atomW coeffW hresW hallWmem htwinW
    · have hoffAll : atomIndex ∉ datumTightSupport data.tightDir
          (data.basisLabel slotAll) := by
        intro hmem
        rcases hsupportEq slotAll hallUmem hallVmem hallWmem atomIndex hmem with h | h | h
        · exact hcaseU h
        · exact hcaseV h
        · exact hcaseW h
      have hoffTwin : atomIndex ∉ datumTightSupport data.tightDir
          (data.basisLabel slotTwin) := by
        intro hmem
        rcases hsupportEq slotTwin htwinU htwinV htwinW atomIndex hmem with h | h | h
        · exact hcaseU h
        · exact hcaseV h
        · exact hcaseW h
      rw [hsuppFrame atomIndex slotAll hoffAll, hsuppFrame atomIndex slotTwin hoffTwin,
        mul_zero, mul_zero]
  by_cases hpair : ∃ slot : Fin data.basisCount, slot ≠ slotAll
      ∧ ((atomU ∈ datumTightSupport data.tightDir (data.basisLabel slot)
            ∧ atomV ∈ datumTightSupport data.tightDir (data.basisLabel slot))
        ∨ (atomU ∈ datumTightSupport data.tightDir (data.basisLabel slot)
            ∧ atomW ∈ datumTightSupport data.tightDir (data.basisLabel slot))
        ∨ (atomV ∈ datumTightSupport data.tightDir (data.basisLabel slot)
            ∧ atomW ∈ datumTightSupport data.tightDir (data.basisLabel slot)))
  · -- THE UNIQUE SEPARATOR KILL
    obtain ⟨slot, hneSlot, hcases⟩ := hpair
    have hnotAll : ¬(atomU ∈ datumTightSupport data.tightDir (data.basisLabel slot)
        ∧ atomV ∈ datumTightSupport data.tightDir (data.basisLabel slot)
        ∧ atomW ∈ datumTightSupport data.tightDir (data.basisLabel slot)) := by
      intro hall
      exact htwin ⟨slot, hneSlot, hall.1, hall.2.1, hall.2.2⟩
    rcases hcases with ⟨hmemUS, hmemVS⟩ | ⟨hmemUS, hmemWS⟩ | ⟨hmemVS, hmemWS⟩
    · have hmissW : atomW ∉ datumTightSupport data.tightDir (data.basisLabel slot) :=
        fun hmem => hnotAll ⟨hmemUS, hmemVS, hmem⟩
      refine data.false_of_unique_separator hdiag htrace hneUW hneUV hneVW.symm hposV
        ?_ hmemUS hallUmem hmissW hallWmem (iff_of_true hmemVS hallVmem)
      intro probe hp
      rcases hinterior probe hp with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · have hmissV : atomV ∉ datumTightSupport data.tightDir (data.basisLabel slot) :=
        fun hmem => hnotAll ⟨hmemUS, hmem, hmemWS⟩
      refine data.false_of_unique_separator hdiag htrace hneUV hneUW hneVW hposW
        ?_ hmemUS hallUmem hmissV hallVmem (iff_of_true hmemWS hallWmem)
      exact hinterior
    · have hmissU : atomU ∉ datumTightSupport data.tightDir (data.basisLabel slot) :=
        fun hmem => hnotAll ⟨hmem, hmemVS, hmemWS⟩
      refine data.false_of_unique_separator hdiag htrace hneUV.symm hneVW hneUW hposW
        ?_ hmemVS hallVmem hmissU hallUmem (iff_of_true hmemWS hallWmem)
      intro probe hp
      rcases hinterior probe hp with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  · -- THE SIGNATURE KILL
    have hnoPair : ∀ slot : Fin data.basisCount, slot ≠ slotAll →
        ¬((atomU ∈ datumTightSupport data.tightDir (data.basisLabel slot)
              ∧ atomV ∈ datumTightSupport data.tightDir (data.basisLabel slot))
          ∨ (atomU ∈ datumTightSupport data.tightDir (data.basisLabel slot)
              ∧ atomW ∈ datumTightSupport data.tightDir (data.basisLabel slot))
          ∨ (atomV ∈ datumTightSupport data.tightDir (data.basisLabel slot)
              ∧ atomW ∈ datumTightSupport data.tightDir (data.basisLabel slot))) := by
      intro slot hne hmem
      exact hpair ⟨slot, hne, hmem⟩
    have hescape : ∀ car : Finset (Fin data.basisCount), 2 ≤ car.card →
        ∃ slot ∈ car, slot ≠ slotAll := by
      intro car hcardCar
      by_contra hnone
      have hsub : car ⊆ ({slotAll} : Finset (Fin data.basisCount)) := by
        intro slot hslot
        refine Finset.mem_singleton.mpr ?_
        by_contra hne
        exact hnone ⟨slot, hslot, hne⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hle
      omega
    obtain ⟨slotU, hslotUmem, hslotUne⟩ := hescape carU hthickU
    obtain ⟨slotV, hslotVmem, hslotVne⟩ := hescape carV hthickV
    obtain ⟨slotW, hslotWmem, hslotWne⟩ := hescape carW hthickW
    have hUcarry : atomU ∈ datumTightSupport data.tightDir (data.basisLabel slotU) :=
      (hmemU slotU).mp hslotUmem
    have hVcarry : atomV ∈ datumTightSupport data.tightDir (data.basisLabel slotV) :=
      (hmemV slotV).mp hslotVmem
    have hWcarry : atomW ∈ datumTightSupport data.tightDir (data.basisLabel slotW) :=
      (hmemW slotW).mp hslotWmem
    have hVmissU : atomV ∉ datumTightSupport data.tightDir (data.basisLabel slotU) :=
      fun hmem => hnoPair slotU hslotUne (Or.inl ⟨hUcarry, hmem⟩)
    have hWmissU : atomW ∉ datumTightSupport data.tightDir (data.basisLabel slotU) :=
      fun hmem => hnoPair slotU hslotUne (Or.inr (Or.inl ⟨hUcarry, hmem⟩))
    have hUmissV : atomU ∉ datumTightSupport data.tightDir (data.basisLabel slotV) :=
      fun hmem => hnoPair slotV hslotVne (Or.inl ⟨hmem, hVcarry⟩)
    have hWmissV : atomW ∉ datumTightSupport data.tightDir (data.basisLabel slotV) :=
      fun hmem => hnoPair slotV hslotVne (Or.inr (Or.inr ⟨hVcarry, hmem⟩))
    have hUmissW : atomU ∉ datumTightSupport data.tightDir (data.basisLabel slotW) :=
      fun hmem => hnoPair slotW hslotWne (Or.inr (Or.inl ⟨hmem, hWcarry⟩))
    have hVmissW : atomV ∉ datumTightSupport data.tightDir (data.basisLabel slotW) :=
      fun hmem => hnoPair slotW hslotWne (Or.inr (Or.inr ⟨hmem, hWcarry⟩))
    exact false_of_signature_quadruple hSsymm hSidem hStrace
      (data.shifted_lt_one atomU) (data.shifted_lt_one atomV) (data.shifted_lt_one atomW)
      hcoeffW hresU hresV hresW
      (hrhoLive slotU atomU hposU hUcarry) (hrhoLive slotV atomV hposV hVcarry)
      (hrhoLive slotW atomW hposW hWcarry) hrhoAll
      (hread atomU slotU hUcarry) (hsuppFrame atomV slotU hVmissU)
      (hsuppFrame atomW slotU hWmissU)
      (hread atomV slotV hVcarry) (hsuppFrame atomU slotV hUmissV)
      (hsuppFrame atomW slotV hWmissV)
      (hread atomW slotW hWcarry) (hsuppFrame atomU slotW hUmissW)
      (hsuppFrame atomV slotW hVmissW)
      (hread atomU slotAll hallUmem) (hread atomV slotAll hallVmem)
      (hread atomW slotAll hallWmem)
      hdualFix hblind hsee hnzFixU

/-! ## Layer 8 — the carrier residue is a theorem -/

set_option maxHeartbeats 1600000 in
/-- **THE CARRIER RESIDUE IS A THEOREM.**  The interior ceiling and the
interior triple name three interior atoms, and the interior triple kill
refuses them. -/
theorem sharedPrivateBoundaryFiveCarrierClosed : SharedPrivateBoundaryFiveCarrierClosed := by
  classical
  intro crux data gramDiag hdiag htrace _hbasis _hpin _hmultOne _hprivate _hinteriorOut
    hthick hthree hhigh _hsingle _hcocarrier _hoffCarrier _hshared _hdistinct
  set interiorSet : Finset (Fin 6) :=
    Finset.univ.filter fun atomIndex =>
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex with hinteriorSet
  have hcard : interiorSet.card = 3 := le_antisymm hhigh hthree
  obtain ⟨atomU, atomV, atomW, hneUV, hneUW, hneVW, hset⟩ := Finset.card_eq_three.mp hcard
  have hmemOf : ∀ probe : Fin 6, probe ∈ interiorSet ↔
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe := by
    intro probe; rw [hinteriorSet]; simp
  have hposU : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomU := by
    refine (hmemOf atomU).mp ?_
    rw [hset]; simp
  have hposV : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomV := by
    refine (hmemOf atomV).mp ?_
    rw [hset]; simp
  have hposW : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomW := by
    refine (hmemOf atomW).mp ?_
    rw [hset]; simp
  have hinterior : ∀ probe : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe →
      probe = atomU ∨ probe = atomV ∨ probe = atomW := by
    intro probe hp
    have hmem := (hmemOf probe).mpr hp
    rw [hset] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  exact data.false_of_interior_triple hdiag htrace hneUV hneUW hneVW hposU hposV hposW
    hinterior hthick

/-! ## Layer 9 — the boundary residues and closure two of the three rungs -/

/-- The leak residue of the basis-count-five boundary stratum is a
theorem. -/
theorem sharedPrivateBoundaryFiveLeakClosed : SharedPrivateBoundaryFiveLeakClosed :=
  sharedPrivateBoundaryFiveLeakClosed_of_carrier sharedPrivateBoundaryFiveCarrierClosed

/-- The confined residue of the basis-count-five boundary stratum is a
theorem. -/
theorem sharedPrivateBoundaryFiveConfinedClosed :
    SharedPrivateBoundaryFiveConfinedClosed :=
  sharedPrivateBoundaryFiveConfinedClosed_of_carrier sharedPrivateBoundaryFiveCarrierClosed

/-- The core residue of the basis-count-five boundary stratum is a
theorem. -/
theorem sharedPrivateBoundaryFiveCoreClosed : SharedPrivateBoundaryFiveCoreClosed :=
  sharedPrivateBoundaryFiveCoreClosed_of_confined sharedPrivateBoundaryFiveConfinedClosed

/-- The basis-count-five boundary stratum is closed. -/
theorem sharedPrivateBoundaryFiveClosed : SharedPrivateBoundaryFiveClosed :=
  sharedPrivateBoundaryFiveClosed_of_core sharedPrivateBoundaryFiveCoreClosed

/-- **THE WHOLE TRACE-TWO BOUNDARY STRATUM IS CLOSED.** -/
theorem sharedPrivateBoundaryClosed : SharedPrivateBoundaryClosed :=
  sharedPrivateBoundaryClosed_of_carrier sharedPrivateBoundaryFiveCarrierClosed

/-- **CLOSURE TWO NEEDS THE EXTRAS RESIDUE ONLY.**  The generic
shared-private kill follows from the extras residue alone. -/
theorem sharedPrivateKilled_of_extras (hextras : SharedPrivateExtrasClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_carrier_strata hextras sharedPrivateBoundaryFiveCarrierClosed

/-- Closure two of the rank-four rung, with the extras residue only. -/
theorem rankFourSharedPrivateClosed_of_extras (hextras : SharedPrivateExtrasClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_carrier_strata hextras
    sharedPrivateBoundaryFiveCarrierClosed

/-- Closure two of the rank-five rung, with the extras residue only. -/
theorem rankFiveSharedPrivateClosed_of_extras (hextras : SharedPrivateExtrasClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_carrier_strata hextras
    sharedPrivateBoundaryFiveCarrierClosed

/-- Closure two of the rank-six rung, with the extras residue only. -/
theorem rankSixSharedPrivateClosed_of_extras (hextras : SharedPrivateExtrasClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_carrier_strata hextras
    sharedPrivateBoundaryFiveCarrierClosed

end Gtz
