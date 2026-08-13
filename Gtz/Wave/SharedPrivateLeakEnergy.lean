import Gtz.Wave.SharedPrivateConfinement

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The leak energy of an interior read — the co-carrier floor and the
disjoint co-carrier kill

A read vector of an interior atom is not an eigenvector of the read
idempotent.  The read law holds on the carrier only, and off the carrier
the fixed part LEAKS.  This module measures that leak exactly.

Write `S` for the read idempotent, `x` for a read vector supported on a
carrier `C`, `d` for the shifted weight and `n` for the read energy.  The
fixed part `S x` has energy `x ⬝ᵥ (S x) = d * n`, because the read law
prices every carrier term.  The carrier part of that energy is `d² * n`
by the same law.  The difference is the leak:

  **`∑ over the slots off C of ((S x) l)² = d * (1 - d) * n`.**

The identity is elementary and it has three consequences.

* **The co-carrier floor.**  Each leak entry is a column dot product,
  thus Cauchy-Schwarz prices it by the diagonal entry.  Summing gives
  `1 - d ≤ ∑ over the slots off C of S l l`, and the carrier form
  `d ≤ ∑ over C of S l l`.
* **The solitary co-slot law.**  When one slot `m` carries the whole
  leak, the fixed part reads `(S x) m • (column m) = (1 - d) • (S x)`.
  Thus `S m m = 1 - d`, and the column at `m` is a multiple of the fixed
  part.
* **THE DISJOINT CO-CARRIER KILL.**  Three interior atoms whose
  co-carriers are pairwise disjoint away from the dead slots ask for
  `3 - (the total shifted weight) ≤ trace S = 2`, thus for a total
  shifted weight of at least one.  The negative chart value refuses it,
  because the total shifted weight is `6 * value + 1`.

The kill closes the last stratum in which the three interior atoms of a
basis-count-five boundary datum miss pairwise disjoint live slots.  The
residue narrows accordingly.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.idem_column_energy`, `Gtz.idem_column_dot_fixed`,
  `Gtz.idem_fixed_energy_eq`, `Gtz.idem_fixed_apply_sq_le` — **THE
  COLUMN CALCULUS** of a symmetric idempotent.
* `Gtz.carried_fixed_energy_eq`, `Gtz.carrier_leak_energy_eq` — **THE
  LEAK ENERGY IDENTITY.**
* `Gtz.exists_leak_ne_zero` — the leak never vanishes at an interior
  read.
* `Gtz.coCarrier_diag_floor`, `Gtz.carrier_diag_floor` — **THE
  CO-CARRIER FLOOR** and the carrier floor.
* `Gtz.solitary_leak_column`, `Gtz.solitary_diag_eq` — **THE SOLITARY
  CO-SLOT LAW.**
* `Gtz.kernel_leak_relation` — the boundary read is orthogonal to every
  interior fixed part.
* `Gtz.commutationTerm` with `Gtz.commutationTerm_of_kernel`,
  `Gtz.commutationTerm_of_carried`, `Gtz.commutationTerm_of_missed`,
  `Gtz.commutationTerm_total` — the commutation of the read weight
  matrix, term by term.
* `Gtz.leak_eq_zero_of_unique_separator` — **THE UNIQUE SEPARATOR LEAK
  LAW.**
* `Gtz.column_smul_of_zero_leak_pair` — **THE ZERO-LEAK LINE**: two
  slots of one vanishing leak carry proportional columns.
* `Gtz.SharedPrivateData.shifted_weight_total`,
  `Gtz.SharedPrivateData.shifted_weight_triple_lt_one` — the budget of
  three interior atoms.
* `Gtz.SharedPrivateData.false_of_disjoint_coCarrier_triple` — **THE
  DISJOINT CO-CARRIER KILL.**
* `Gtz.SharedPrivateData.exists_shared_coCarrier` — the positive form
  that the residue consumes.
* `Gtz.SharedPrivateBoundaryFiveLeakClosed` with
  `Gtz.sharedPrivateBoundaryFiveConfinedClosed_of_leak` — the narrowed
  residue.
* `Gtz.sharedPrivateKilled_of_leak_energy_strata`,
  `Gtz.rankFourSharedPrivateClosed_of_leak_energy_strata`,
  `Gtz.rankFiveSharedPrivateClosed_of_leak_energy_strata`,
  `Gtz.rankSixSharedPrivateClosed_of_leak_energy_strata` — the
  dispatches.

## Vacuity

The matrix statements are unconditional.  The datum statements quantify
over shared-private data, and no datum exists if `Gtz.GtzWeighted 6 3`
holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the column calculus of a symmetric idempotent -/

/-- The entry law of a symmetric matrix, in the shape the proofs use. -/
theorem symm_entry_swap {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ} (hsymm : Sᵀ = S)
    (rowSlot colSlot : Fin slotCount) : S colSlot rowSlot = S rowSlot colSlot := by
  have hentry := congrFun (congrFun hsymm rowSlot) colSlot
  rwa [Matrix.transpose_apply] at hentry

/-- **THE COLUMN ENERGY.**  A column of a symmetric idempotent has the
diagonal entry as its energy. -/
theorem idem_column_energy {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (slot : Fin slotCount) :
    kernelColumn S slot ⬝ᵥ kernelColumn S slot = S slot slot := by
  have hentry := congrFun (congrFun hidem slot) slot
  rw [Matrix.mul_apply] at hentry
  rw [dotProduct, ← hentry]
  refine Finset.sum_congr rfl fun midSlot _ => ?_
  show S midSlot slot * S midSlot slot = S slot midSlot * S midSlot slot
  rw [symm_entry_swap hsymm slot midSlot]

/-- **THE COLUMN READ.**  A fixed vector reads its own entry against the
column of that slot. -/
theorem idem_column_dot_fixed {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (probe : Fin slotCount → ℝ)
    (slot : Fin slotCount) :
    kernelColumn S slot ⬝ᵥ (S *ᵥ probe) = (S *ᵥ probe) slot := by
  have hfixed : S *ᵥ (S *ᵥ probe) = S *ᵥ probe := by
    rw [Matrix.mulVec_mulVec, hidem]
  have hstep : kernelColumn S slot ⬝ᵥ (S *ᵥ probe)
      = (S *ᵥ (S *ᵥ probe)) slot := by
    rw [Matrix.mulVec, dotProduct, dotProduct]
    refine Finset.sum_congr rfl fun midSlot _ => ?_
    show S midSlot slot * (S *ᵥ probe) midSlot
      = S slot midSlot * (S *ᵥ probe) midSlot
    rw [symm_entry_swap hsymm slot midSlot]
  rw [hstep, hfixed]

/-- **THE FIXED ENERGY.**  The energy of a fixed part is the mixed energy
against the original vector. -/
theorem idem_fixed_energy_eq {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (probe : Fin slotCount → ℝ) :
    (S *ᵥ probe) ⬝ᵥ (S *ᵥ probe) = probe ⬝ᵥ (S *ᵥ probe) := by
  have hstep := dotProduct_mulVec_symm hsymm probe (S *ᵥ probe)
  have hfixed : S *ᵥ (S *ᵥ probe) = S *ᵥ probe := by
    rw [Matrix.mulVec_mulVec, hidem]
  rw [hfixed] at hstep
  exact hstep.symm

/-- **THE ENTRY CAP.**  Cauchy-Schwarz prices an entry of a fixed part by
the diagonal entry of the idempotent. -/
theorem idem_fixed_apply_sq_le {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (probe : Fin slotCount → ℝ)
    (slot : Fin slotCount) :
    ((S *ᵥ probe) slot) ^ 2
      ≤ S slot slot * ((S *ᵥ probe) ⬝ᵥ (S *ᵥ probe)) := by
  have hcs := dotProduct_sq_le_mul (kernelColumn S slot) (S *ᵥ probe)
  rw [idem_column_dot_fixed hsymm hidem probe slot,
    idem_column_energy hsymm hidem slot] at hcs
  exact hcs

/-! ## Layer 2 — the leak energy identity -/

/-- The fixed energy of a carried read is the shifted weight times the
read energy. -/
theorem carried_fixed_energy_eq {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) {probe : Fin slotCount → ℝ}
    {carrier : Finset (Fin slotCount)} {weight readEnergy : ℝ}
    (hsupp : ∀ slot : Fin slotCount, slot ∉ carrier → probe slot = 0)
    (hread : ∀ slot ∈ carrier, (S *ᵥ probe) slot = weight * probe slot)
    (hnorm : probe ⬝ᵥ probe = readEnergy) :
    (S *ᵥ probe) ⬝ᵥ (S *ᵥ probe) = weight * readEnergy := by
  classical
  have hmixed : probe ⬝ᵥ (S *ᵥ probe) = weight * readEnergy := by
    have hsplit : probe ⬝ᵥ (S *ᵥ probe)
        = ∑ slot ∈ carrier, probe slot * (S *ᵥ probe) slot := by
      rw [dotProduct]
      refine (Finset.sum_subset (Finset.subset_univ carrier) ?_).symm
      intro slot _ hnot
      rw [hsupp slot hnot, zero_mul]
    have hcarrier : (∑ slot ∈ carrier, probe slot * (S *ᵥ probe) slot)
        = weight * ∑ slot ∈ carrier, probe slot * probe slot := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun slot hslot => ?_
      rw [hread slot hslot]
      ring
    have hself : (∑ slot ∈ carrier, probe slot * probe slot) = readEnergy := by
      rw [← hnorm, dotProduct]
      refine Finset.sum_subset (Finset.subset_univ carrier) ?_
      intro slot _ hnot
      rw [hsupp slot hnot, zero_mul]
    rw [hsplit, hcarrier, hself]
  rw [idem_fixed_energy_eq hsymm hidem probe, hmixed]

/-- **THE LEAK ENERGY IDENTITY.**  The fixed part of a carried read holds
`weight * (1 - weight) * readEnergy` of energy off the carrier. -/
theorem carrier_leak_energy_eq {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) {probe : Fin slotCount → ℝ}
    {carrier : Finset (Fin slotCount)} {weight readEnergy : ℝ}
    (hsupp : ∀ slot : Fin slotCount, slot ∉ carrier → probe slot = 0)
    (hread : ∀ slot ∈ carrier, (S *ᵥ probe) slot = weight * probe slot)
    (hnorm : probe ⬝ᵥ probe = readEnergy) :
    (∑ slot ∈ Finset.univ \ carrier, ((S *ᵥ probe) slot) ^ 2)
      = weight * (1 - weight) * readEnergy := by
  classical
  have htotal : (∑ slot : Fin slotCount, ((S *ᵥ probe) slot) ^ 2)
      = weight * readEnergy := by
    rw [← carried_fixed_energy_eq hsymm hidem hsupp hread hnorm, dotProduct]
    exact Finset.sum_congr rfl fun slot _ => by ring
  have hcarrier : (∑ slot ∈ carrier, ((S *ᵥ probe) slot) ^ 2)
      = weight * weight * readEnergy := by
    have hstep : (∑ slot ∈ carrier, ((S *ᵥ probe) slot) ^ 2)
        = weight * weight * ∑ slot ∈ carrier, probe slot * probe slot := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun slot hslot => ?_
      rw [hread slot hslot]
      ring
    have hself : (∑ slot ∈ carrier, probe slot * probe slot) = readEnergy := by
      rw [← hnorm, dotProduct]
      refine Finset.sum_subset (Finset.subset_univ carrier) ?_
      intro slot _ hnot
      rw [hsupp slot hnot, zero_mul]
    rw [hstep, hself]
  have hsplit : (∑ slot ∈ Finset.univ \ carrier, ((S *ᵥ probe) slot) ^ 2)
      + ∑ slot ∈ carrier, ((S *ᵥ probe) slot) ^ 2
      = ∑ slot : Fin slotCount, ((S *ᵥ probe) slot) ^ 2 :=
    Finset.sum_sdiff (Finset.subset_univ carrier)
  rw [hcarrier, htotal] at hsplit
  linarith

/-- **THE LEAK IS ALIVE.**  At a strictly interior read with a positive
energy the fixed part is nonzero somewhere off the carrier. -/
theorem exists_leak_ne_zero {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) {probe : Fin slotCount → ℝ}
    {carrier : Finset (Fin slotCount)} {weight readEnergy : ℝ}
    (hsupp : ∀ slot : Fin slotCount, slot ∉ carrier → probe slot = 0)
    (hread : ∀ slot ∈ carrier, (S *ᵥ probe) slot = weight * probe slot)
    (hnorm : probe ⬝ᵥ probe = readEnergy) (hpos : 0 < weight)
    (hlt : weight < 1) (henergy : 0 < readEnergy) :
    ∃ slot : Fin slotCount, slot ∉ carrier ∧ (S *ᵥ probe) slot ≠ 0 := by
  classical
  by_contra hnone
  simp only [not_exists, not_and, not_not] at hnone
  have hzero : (∑ slot ∈ Finset.univ \ carrier, ((S *ᵥ probe) slot) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun slot hslot => ?_
    have hnot : slot ∉ carrier := (Finset.mem_sdiff.mp hslot).2
    rw [hnone slot hnot]
    ring
  rw [carrier_leak_energy_eq hsymm hidem hsupp hread hnorm] at hzero
  nlinarith [mul_pos (mul_pos hpos (by linarith : (0 : ℝ) < 1 - weight)) henergy]

/-! ## Layer 3 — the co-carrier floor -/

/-- **THE CO-CARRIER FLOOR.**  The diagonal mass of the idempotent off
the carrier of an interior read is at least the complementary weight. -/
theorem coCarrier_diag_floor {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) {probe : Fin slotCount → ℝ}
    {carrier : Finset (Fin slotCount)} {weight readEnergy : ℝ}
    (hsupp : ∀ slot : Fin slotCount, slot ∉ carrier → probe slot = 0)
    (hread : ∀ slot ∈ carrier, (S *ᵥ probe) slot = weight * probe slot)
    (hnorm : probe ⬝ᵥ probe = readEnergy) (hpos : 0 < weight)
    (henergy : 0 < readEnergy) :
    1 - weight ≤ ∑ slot ∈ Finset.univ \ carrier, S slot slot := by
  classical
  have hfixed := carried_fixed_energy_eq hsymm hidem hsupp hread hnorm
  have hcap : ∀ slot ∈ Finset.univ \ carrier,
      ((S *ᵥ probe) slot) ^ 2 ≤ S slot slot * (weight * readEnergy) := by
    intro slot _
    have hstep := idem_fixed_apply_sq_le hsymm hidem probe slot
    rwa [hfixed] at hstep
  have hsum : (∑ slot ∈ Finset.univ \ carrier, ((S *ᵥ probe) slot) ^ 2)
      ≤ ∑ slot ∈ Finset.univ \ carrier, S slot slot * (weight * readEnergy) :=
    Finset.sum_le_sum hcap
  rw [carrier_leak_energy_eq hsymm hidem hsupp hread hnorm,
    ← Finset.sum_mul] at hsum
  have hposProd : 0 < weight * readEnergy := mul_pos hpos henergy
  nlinarith [hsum]

/-- **THE CARRIER FLOOR.**  The diagonal mass on the carrier is at least
the shifted weight. -/
theorem carrier_diag_floor {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) {probe : Fin slotCount → ℝ}
    {carrier : Finset (Fin slotCount)} {weight readEnergy : ℝ}
    (hsupp : ∀ slot : Fin slotCount, slot ∉ carrier → probe slot = 0)
    (hread : ∀ slot ∈ carrier, (S *ᵥ probe) slot = weight * probe slot)
    (hnorm : probe ⬝ᵥ probe = readEnergy) (hpos : 0 < weight)
    (henergy : 0 < readEnergy) :
    weight ≤ ∑ slot ∈ carrier, S slot slot := by
  classical
  have hfixed := carried_fixed_energy_eq hsymm hidem hsupp hread hnorm
  have hcarrier : (∑ slot ∈ carrier, ((S *ᵥ probe) slot) ^ 2)
      = weight * weight * readEnergy := by
    have hstep : (∑ slot ∈ carrier, ((S *ᵥ probe) slot) ^ 2)
        = weight * weight * ∑ slot ∈ carrier, probe slot * probe slot := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun slot hslot => ?_
      rw [hread slot hslot]
      ring
    have hself : (∑ slot ∈ carrier, probe slot * probe slot) = readEnergy := by
      rw [← hnorm, dotProduct]
      refine Finset.sum_subset (Finset.subset_univ carrier) ?_
      intro slot _ hnot
      rw [hsupp slot hnot, zero_mul]
    rw [hstep, hself]
  have hcap : ∀ slot ∈ carrier,
      ((S *ᵥ probe) slot) ^ 2 ≤ S slot slot * (weight * readEnergy) := by
    intro slot _
    have hstep := idem_fixed_apply_sq_le hsymm hidem probe slot
    rwa [hfixed] at hstep
  have hsum : (∑ slot ∈ carrier, ((S *ᵥ probe) slot) ^ 2)
      ≤ ∑ slot ∈ carrier, S slot slot * (weight * readEnergy) :=
    Finset.sum_le_sum hcap
  rw [hcarrier, ← Finset.sum_mul] at hsum
  have hposProd : 0 < weight * readEnergy := mul_pos hpos henergy
  nlinarith [hsum]

/-! ## Layer 4 — the solitary co-slot law -/

/-- **THE SOLITARY LEAK COLUMN.**  When one slot carries the whole leak,
the column of that slot is a multiple of the fixed part. -/
theorem solitary_leak_column {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hidem : S * S = S) {probe : Fin slotCount → ℝ}
    {carrier : Finset (Fin slotCount)} {weight : ℝ}
    {leakSlot : Fin slotCount} (hleak : leakSlot ∉ carrier)
    (hsupp : ∀ slot : Fin slotCount, slot ∉ carrier → probe slot = 0)
    (hread : ∀ slot ∈ carrier, (S *ᵥ probe) slot = weight * probe slot)
    (hsolitary : ∀ slot : Fin slotCount, slot ∉ carrier → slot ≠ leakSlot →
      (S *ᵥ probe) slot = 0) (rowSlot : Fin slotCount) :
    S rowSlot leakSlot * (S *ᵥ probe) leakSlot
      = (1 - weight) * (S *ᵥ probe) rowSlot := by
  classical
  have hfixed : S *ᵥ (S *ᵥ probe) = S *ᵥ probe := by
    rw [Matrix.mulVec_mulVec, hidem]
  have hrow : (S *ᵥ (S *ᵥ probe)) rowSlot
      = ∑ slot, S rowSlot slot * (S *ᵥ probe) slot := by
    rw [Matrix.mulVec, dotProduct]
  have hcarrierPart : (∑ slot ∈ carrier, S rowSlot slot * (S *ᵥ probe) slot)
      = weight * (S *ᵥ probe) rowSlot := by
    have hstep : (∑ slot ∈ carrier, S rowSlot slot * (S *ᵥ probe) slot)
        = weight * ∑ slot ∈ carrier, S rowSlot slot * probe slot := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun slot hslot => ?_
      rw [hread slot hslot]
      ring
    have hself : (∑ slot ∈ carrier, S rowSlot slot * probe slot)
        = (S *ᵥ probe) rowSlot := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_subset (Finset.subset_univ carrier) ?_
      intro slot _ hnot
      rw [hsupp slot hnot, mul_zero]
    rw [hstep, hself]
  have hrestPart : (∑ slot ∈ Finset.univ \ carrier,
      S rowSlot slot * (S *ᵥ probe) slot)
      = S rowSlot leakSlot * (S *ᵥ probe) leakSlot := by
    refine Finset.sum_eq_single leakSlot ?_ ?_
    · intro slot hslot hne
      have hnot : slot ∉ carrier := (Finset.mem_sdiff.mp hslot).2
      rw [hsolitary slot hnot hne, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_sdiff.mpr ⟨Finset.mem_univ leakSlot, hleak⟩) hnot
  have hsplit : (∑ slot ∈ Finset.univ \ carrier,
        S rowSlot slot * (S *ᵥ probe) slot)
      + ∑ slot ∈ carrier, S rowSlot slot * (S *ᵥ probe) slot
      = ∑ slot, S rowSlot slot * (S *ᵥ probe) slot :=
    Finset.sum_sdiff (Finset.subset_univ carrier)
  have hgoal := congrFun hfixed rowSlot
  rw [hrow] at hgoal
  rw [hcarrierPart, hrestPart] at hsplit
  linarith [hsplit, hgoal]

/-- **THE SOLITARY LEAK ENERGY.**  One leak slot carries the whole leak
energy. -/
theorem solitary_leak_energy {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) {probe : Fin slotCount → ℝ}
    {carrier : Finset (Fin slotCount)} {weight readEnergy : ℝ}
    {leakSlot : Fin slotCount} (hleak : leakSlot ∉ carrier)
    (hsupp : ∀ slot : Fin slotCount, slot ∉ carrier → probe slot = 0)
    (hread : ∀ slot ∈ carrier, (S *ᵥ probe) slot = weight * probe slot)
    (hnorm : probe ⬝ᵥ probe = readEnergy)
    (hsolitary : ∀ slot : Fin slotCount, slot ∉ carrier → slot ≠ leakSlot →
      (S *ᵥ probe) slot = 0) :
    ((S *ᵥ probe) leakSlot) ^ 2 = weight * (1 - weight) * readEnergy := by
  classical
  have htotal := carrier_leak_energy_eq hsymm hidem hsupp hread hnorm
  have hsingle : (∑ slot ∈ Finset.univ \ carrier, ((S *ᵥ probe) slot) ^ 2)
      = ((S *ᵥ probe) leakSlot) ^ 2 := by
    refine Finset.sum_eq_single leakSlot ?_ ?_
    · intro slot hslot hne
      have hnot : slot ∉ carrier := (Finset.mem_sdiff.mp hslot).2
      rw [hsolitary slot hnot hne]
      ring
    · intro hnot
      exact absurd (Finset.mem_sdiff.mpr ⟨Finset.mem_univ leakSlot, hleak⟩) hnot
  rw [hsingle] at htotal
  exact htotal

/-- **THE SOLITARY CO-SLOT LAW.**  A slot that carries the whole leak of
an interior read has the complementary weight as its diagonal entry. -/
theorem solitary_diag_eq {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) {probe : Fin slotCount → ℝ}
    {carrier : Finset (Fin slotCount)} {weight readEnergy : ℝ}
    {leakSlot : Fin slotCount} (hleak : leakSlot ∉ carrier)
    (hsupp : ∀ slot : Fin slotCount, slot ∉ carrier → probe slot = 0)
    (hread : ∀ slot ∈ carrier, (S *ᵥ probe) slot = weight * probe slot)
    (hnorm : probe ⬝ᵥ probe = readEnergy)
    (hsolitary : ∀ slot : Fin slotCount, slot ∉ carrier → slot ≠ leakSlot →
      (S *ᵥ probe) slot = 0) (hpos : 0 < weight) (hlt : weight < 1)
    (henergy : 0 < readEnergy) : S leakSlot leakSlot = 1 - weight := by
  have henergyLeak :=
    solitary_leak_energy hsymm hidem hleak hsupp hread hnorm hsolitary
  have hne : (S *ᵥ probe) leakSlot ≠ 0 := by
    intro hzero
    rw [hzero] at henergyLeak
    nlinarith [mul_pos (mul_pos hpos (by linarith : (0 : ℝ) < 1 - weight)) henergy]
  have hcolumn :=
    solitary_leak_column hidem hleak hsupp hread hsolitary leakSlot
  exact mul_right_cancel₀ hne hcolumn

/-! ## Layer 5 — the kernel leak relation -/

/-- **THE KERNEL LEAK RELATION.**  A boundary read sits in the kernel of
the read idempotent, thus it is orthogonal to the fixed part of every
other read.  The relation reads the leak entries of that read across the
carrier of the boundary atom. -/
theorem kernel_leak_relation {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ} (hsymm : Sᵀ = S)
    {kernelVec probe : Fin slotCount → ℝ} (hkernel : S *ᵥ kernelVec = 0) :
    (∑ slot, kernelVec slot * (S *ᵥ probe) slot) = 0 := by
  have hstep := dotProduct_mulVec_symm hsymm kernelVec probe
  rw [hkernel] at hstep
  rw [← dotProduct] at *
  rw [hstep, zero_dotProduct]

/-! ## Layer 5b — the commutation leak calculus -/

/-- The commutation term of one read at a slot pair. -/
def commutationTerm {slotCount : ℕ}
    (S : Matrix (Fin slotCount) (Fin slotCount) ℝ) (probe : Fin slotCount → ℝ)
    (rowSlot colSlot : Fin slotCount) : ℝ :=
  (S *ᵥ probe) rowSlot * probe colSlot - probe rowSlot * (S *ᵥ probe) colSlot

/-- A kernel read gives no commutation term. -/
theorem commutationTerm_of_kernel {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ} {probe : Fin slotCount → ℝ}
    (hkernel : S *ᵥ probe = 0) (rowSlot colSlot : Fin slotCount) :
    commutationTerm S probe rowSlot colSlot = 0 := by
  rw [commutationTerm, hkernel]
  simp

/-- A read that carries both slots gives no commutation term: the read
law prices the two products identically. -/
theorem commutationTerm_of_carried {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ} {probe : Fin slotCount → ℝ}
    {weight : ℝ} {rowSlot colSlot : Fin slotCount}
    (hrow : (S *ᵥ probe) rowSlot = weight * probe rowSlot)
    (hcol : (S *ᵥ probe) colSlot = weight * probe colSlot) :
    commutationTerm S probe rowSlot colSlot = 0 := by
  rw [commutationTerm, hrow, hcol]
  ring

/-- A read that misses both slots gives no commutation term. -/
theorem commutationTerm_of_missed {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ} {probe : Fin slotCount → ℝ}
    {rowSlot colSlot : Fin slotCount} (hrow : probe rowSlot = 0)
    (hcol : probe colSlot = 0) :
    commutationTerm S probe rowSlot colSlot = 0 := by
  rw [commutationTerm, hrow, hcol]
  ring

/-- The commutation of the read weight matrix with the read idempotent,
written as the total of the commutation terms. -/
theorem commutationTerm_total {atomCount slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (readVecs : Fin atomCount → Fin slotCount → ℝ)
    (hcommute : ∀ rowSlot colSlot : Fin slotCount,
      (∑ atomIndex, readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot)
        = ∑ atomIndex, (S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex colSlot)
    (rowSlot colSlot : Fin slotCount) :
    (∑ atomIndex, commutationTerm S (readVecs atomIndex) rowSlot colSlot) = 0 := by
  have hsplit : (∑ atomIndex, commutationTerm S (readVecs atomIndex) rowSlot colSlot)
      = (∑ atomIndex, (S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex colSlot)
        - ∑ atomIndex, readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => rfl
  rw [hsplit, hcommute rowSlot colSlot, sub_self]

/-- **THE UNIQUE SEPARATOR LEAK LAW.**  When exactly one read separates a
slot pair, the commutation entry is a single product, and the carrier
factor is nonzero.  Thus the leak of that read at the missed slot
VANISHES. -/
theorem leak_eq_zero_of_unique_separator {atomCount slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (readVecs : Fin atomCount → Fin slotCount → ℝ)
    (hcommute : ∀ rowSlot colSlot : Fin slotCount,
      (∑ atomIndex, readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot)
        = ∑ atomIndex, (S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex colSlot)
    {separator : Fin atomCount} {leakSlot carrierSlot : Fin slotCount}
    (hother : ∀ atomIndex : Fin atomCount, atomIndex ≠ separator →
      commutationTerm S (readVecs atomIndex) leakSlot carrierSlot = 0)
    (hmiss : readVecs separator leakSlot = 0)
    (hcarrier : readVecs separator carrierSlot ≠ 0) :
    (S *ᵥ readVecs separator) leakSlot = 0 := by
  classical
  have htotal := commutationTerm_total readVecs hcommute leakSlot carrierSlot
  have hsingle : (∑ atomIndex, commutationTerm S (readVecs atomIndex) leakSlot carrierSlot)
      = commutationTerm S (readVecs separator) leakSlot carrierSlot := by
    refine Finset.sum_eq_single separator (fun atomIndex _ hne => hother atomIndex hne)
      fun hnot => absurd (Finset.mem_univ separator) hnot
  rw [hsingle, commutationTerm, hmiss, zero_mul, sub_zero] at htotal
  rcases mul_eq_zero.mp htotal with hcase | hcase
  · exact hcase
  · exact absurd hcase hcarrier

/-! ## Layer 5c — the parallel columns of a zero leak pair -/

/-- **THE ZERO-LEAK LINE.**  At trace two the columns of two slots where
one fixed part vanishes are proportional: both columns are orthogonal to
that nonzero fixed part inside the two-dimensional image, and the
orthogonal space of a nonzero vector in a plane is a line. -/
theorem column_smul_of_zero_leak_pair {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (htrace : Matrix.trace S = 2)
    {probe : Fin slotCount → ℝ} (hprobeNe : S *ᵥ probe ≠ 0)
    {slotA slotB : Fin slotCount}
    (hzeroA : (S *ᵥ probe) slotA = 0) (hzeroB : (S *ᵥ probe) slotB = 0)
    (hliveB : S slotB slotB ≠ 0) :
    ∃ scale : ℝ, kernelColumn S slotA
      = fun rowSlot => scale * kernelColumn S slotB rowSlot := by
  classical
  obtain ⟨firstVec, secondVec, hfirstUnit, hsecondUnit, hcross, hsplit⟩ :=
    exists_orthonormal_pair_of_trace_two hsymm hidem htrace
  have hentry : ∀ rowSlot colSlot : Fin slotCount,
      S rowSlot colSlot
        = firstVec rowSlot * firstVec colSlot + secondVec rowSlot * secondVec colSlot := by
    intro rowSlot colSlot
    have hstep := congrFun (congrFun hsplit rowSlot) colSlot
    rwa [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.vecMulVec_apply] at hstep
  have hfixed : ∀ rowSlot : Fin slotCount, (S *ᵥ probe) rowSlot
      = firstVec rowSlot * (firstVec ⬝ᵥ probe)
        + secondVec rowSlot * (secondVec ⬝ᵥ probe) := by
    intro rowSlot
    rw [Matrix.mulVec, dotProduct, dotProduct, dotProduct, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun midSlot _ => by rw [hentry rowSlot midSlot]; ring
  set firstRead : ℝ := firstVec ⬝ᵥ probe with hfirstRead
  set secondRead : ℝ := secondVec ⬝ᵥ probe with hsecondRead
  have hreadNe : firstRead ≠ 0 ∨ secondRead ≠ 0 := by
    by_contra hboth
    rw [not_or, not_not, not_not] at hboth
    refine hprobeNe (funext fun rowSlot => ?_)
    rw [hfixed rowSlot, hboth.1, hboth.2]
    simp
  have heqA : firstVec slotA * firstRead + secondVec slotA * secondRead = 0 := by
    rw [← hfixed slotA]; exact hzeroA
  have heqB : firstVec slotB * firstRead + secondVec slotB * secondRead = 0 := by
    rw [← hfixed slotB]; exact hzeroB
  have hdet : firstVec slotA * secondVec slotB - firstVec slotB * secondVec slotA = 0 := by
    rcases hreadNe with hne | hne
    · have hstep : firstRead
          * (firstVec slotA * secondVec slotB - firstVec slotB * secondVec slotA) = 0 := by
        linear_combination secondVec slotB * heqA - secondVec slotA * heqB
      rcases mul_eq_zero.mp hstep with hcase | hcase
      · exact absurd hcase hne
      · exact hcase
    · have hstep : secondRead
          * (firstVec slotA * secondVec slotB - firstVec slotB * secondVec slotA) = 0 := by
        linear_combination firstVec slotA * heqB - firstVec slotB * heqA
      rcases mul_eq_zero.mp hstep with hcase | hcase
      · exact absurd hcase hne
      · exact hcase
  have hnormB : firstVec slotB * firstVec slotB + secondVec slotB * secondVec slotB ≠ 0 := by
    rw [← hentry slotB slotB]; exact hliveB
  refine ⟨(firstVec slotA * firstVec slotB + secondVec slotA * secondVec slotB)
    / (firstVec slotB * firstVec slotB + secondVec slotB * secondVec slotB), ?_⟩
  funext rowSlot
  show S rowSlot slotA
    = (firstVec slotA * firstVec slotB + secondVec slotA * secondVec slotB)
      / (firstVec slotB * firstVec slotB + secondVec slotB * secondVec slotB)
      * S rowSlot slotB
  have hkey : (firstVec slotB * firstVec slotB + secondVec slotB * secondVec slotB)
        * (firstVec rowSlot * firstVec slotA + secondVec rowSlot * secondVec slotA)
      = (firstVec slotA * firstVec slotB + secondVec slotA * secondVec slotB)
        * (firstVec rowSlot * firstVec slotB + secondVec rowSlot * secondVec slotB) := by
    linear_combination (firstVec rowSlot * secondVec slotB
      - secondVec rowSlot * firstVec slotB) * hdet
  rw [hentry rowSlot slotA, hentry rowSlot slotB, div_mul_eq_mul_div,
    eq_div_iff hnormB]
  linear_combination hkey

/-! ## Layer 6 — the datum laws -/

/-- The total shifted weight of a datum is `6 * value + 1`. -/
theorem SharedPrivateData.shifted_weight_total {crux : SixThreeCrux}
    (data : SharedPrivateData crux) :
    (∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex))
      = 6 * chartObjective (chartPointOfDesign crux.design) + 1 := by
  rw [Finset.sum_add_distrib, data.hdata.weight_sum_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **THE TRIPLE BUDGET.**  Three distinct atoms of positive shifted
weight carry a total below one. -/
theorem SharedPrivateData.shifted_weight_triple_lt_one {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {atomOne atomTwo atomThree : Fin 6}
    (hne12 : atomOne ≠ atomTwo) (hne13 : atomOne ≠ atomThree)
    (hne23 : atomTwo ≠ atomThree) :
    (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomOne)
      + (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomTwo)
      + (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomThree) < 1 := by
  classical
  set shifted : Fin 6 → ℝ := fun atomIndex =>
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex with hshifted
  have hnonneg : ∀ atomIndex : Fin 6, 0 ≤ shifted atomIndex := fun atomIndex =>
    capture_diagonal_nonneg_of_isChartStationaryData data.hdata atomIndex
  set triple : Finset (Fin 6) := {atomOne, atomTwo, atomThree} with htriple
  have hcard : (∑ atomIndex ∈ triple, shifted atomIndex)
      = shifted atomOne + shifted atomTwo + shifted atomThree := by
    rw [htriple, Finset.sum_insert (by simp [hne12, hne13]),
      Finset.sum_insert (by simp [hne23]), Finset.sum_singleton]
    ring
  have hle : (∑ atomIndex ∈ triple, shifted atomIndex)
      ≤ ∑ atomIndex : Fin 6, shifted atomIndex :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ triple)
      fun atomIndex _ _ => hnonneg atomIndex
  rw [hcard, data.shifted_weight_total] at hle
  have hneg := data.hvalueNeg
  linarith

/-- **THE DISJOINT CO-CARRIER KILL.**  Three interior atoms whose live
co-carriers are pairwise disjoint ask for a total shifted weight of at
least one.  The co-carrier floor prices each of the three, the disjoint
sets fit inside the trace, and the negative chart value refuses the
total. -/
theorem SharedPrivateData.false_of_disjoint_coCarrier_triple {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2)
    {atomOne atomTwo atomThree : Fin 6}
    (hne12 : atomOne ≠ atomTwo) (hne13 : atomOne ≠ atomThree)
    (hne23 : atomTwo ≠ atomThree)
    (hposOne : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne)
    (hposTwo : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomTwo)
    (hposThree : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomThree)
    {setOne setTwo setThree : Finset (Fin data.basisCount)}
    (hsubOne : ∀ slot ∈ setOne,
      atomOne ∉ datumTightSupport data.tightDir (data.basisLabel slot))
    (hsubTwo : ∀ slot ∈ setTwo,
      atomTwo ∉ datumTightSupport data.tightDir (data.basisLabel slot))
    (hsubThree : ∀ slot ∈ setThree,
      atomThree ∉ datumTightSupport data.tightDir (data.basisLabel slot))
    (hcoverOne : ∀ slot : Fin data.basisCount,
      atomOne ∉ datumTightSupport data.tightDir (data.basisLabel slot) →
      slot ∉ setOne → ∀ probe : Fin 6,
        0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight probe →
        probe ∉ datumTightSupport data.tightDir (data.basisLabel slot))
    (hcoverTwo : ∀ slot : Fin data.basisCount,
      atomTwo ∉ datumTightSupport data.tightDir (data.basisLabel slot) →
      slot ∉ setTwo → ∀ probe : Fin 6,
        0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight probe →
        probe ∉ datumTightSupport data.tightDir (data.basisLabel slot))
    (hcoverThree : ∀ slot : Fin data.basisCount,
      atomThree ∉ datumTightSupport data.tightDir (data.basisLabel slot) →
      slot ∉ setThree → ∀ probe : Fin 6,
        0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight probe →
        probe ∉ datumTightSupport data.tightDir (data.basisLabel slot))
    (hdisj12 : Disjoint setOne setTwo) (hdisj13 : Disjoint setOne setThree)
    (hdisj23 : Disjoint setTwo setThree) : False := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsuppFrame, hread, hnorm,
    _hboundary, _hcarrierNz, hdeadCol⟩ := data.exists_dead_read_frame hdiag
  have hbudget := data.shifted_weight_triple_lt_one hne12 hne13 hne23
  set shifted : Fin 6 → ℝ := fun atomIndex =>
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex with hshifted
  set carrierOf : Fin 6 → Finset (Fin data.basisCount) := fun atomIndex =>
    Finset.univ.filter fun slot =>
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)
    with hcarrierOf
  have hmemCarrier : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      slot ∈ carrierOf atomIndex ↔
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
    intro atomIndex slot
    simp [hcarrierOf]
  have hdiagNonneg : ∀ slot : Fin data.basisCount, 0 ≤ S slot slot := by
    intro slot
    rw [← idem_column_energy hSsymm hSidem slot]
    exact selfDot_nonneg _
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
  -- the co-carrier floor at one interior atom, transported to the chosen set
  have hfloor : ∀ (atomIndex : Fin 6) (chosen : Finset (Fin data.basisCount)),
      0 < shifted atomIndex →
      (∀ slot ∈ chosen,
        atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot)) →
      (∀ slot : Fin data.basisCount,
        atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot) →
        slot ∉ chosen → ∀ probe : Fin 6, 0 < shifted probe →
          probe ∉ datumTightSupport data.tightDir (data.basisLabel slot)) →
      1 - shifted atomIndex ≤ ∑ slot ∈ chosen, S slot slot := by
    intro atomIndex chosen hpos hsub hcover
    have hsupp : ∀ slot : Fin data.basisCount, slot ∉ carrierOf atomIndex →
        readVecs atomIndex slot = 0 := by
      intro slot hslot
      exact hsuppFrame atomIndex slot fun hmem =>
        hslot ((hmemCarrier atomIndex slot).mpr hmem)
    have hreadCar : ∀ slot ∈ carrierOf atomIndex,
        (S *ᵥ readVecs atomIndex) slot = shifted atomIndex * readVecs atomIndex slot :=
      fun slot hslot => hread atomIndex slot ((hmemCarrier atomIndex slot).mp hslot)
    have hbase := coCarrier_diag_floor hSsymm hSidem hsupp hreadCar
      (hnorm atomIndex) hpos (by norm_num : (0 : ℝ) < (6 : ℝ)⁻¹)
    have htransport : (∑ slot ∈ Finset.univ \ carrierOf atomIndex, S slot slot)
        = ∑ slot ∈ chosen, S slot slot := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro slot hslot
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ slot, fun hmem =>
          hsub slot hslot ((hmemCarrier atomIndex slot).mp hmem)⟩
      · intro slot hslot hnot
        have hoff : atomIndex ∉ datumTightSupport data.tightDir
            (data.basisLabel slot) := by
          intro hmem
          exact (Finset.mem_sdiff.mp hslot).2 ((hmemCarrier atomIndex slot).mpr hmem)
        exact hdeadCol slot (hcover slot hoff hnot) slot
    rwa [htransport] at hbase
  have hfloorOne := hfloor atomOne setOne hposOne hsubOne hcoverOne
  have hfloorTwo := hfloor atomTwo setTwo hposTwo hsubTwo hcoverTwo
  have hfloorThree := hfloor atomThree setThree hposThree hsubThree hcoverThree
  -- the three disjoint sets fit inside the trace
  have hunionTwo : Disjoint (setOne ∪ setTwo) setThree :=
    Finset.disjoint_union_left.mpr ⟨hdisj13, hdisj23⟩
  have hsumUnion : (∑ slot ∈ (setOne ∪ setTwo) ∪ setThree, S slot slot)
      = (∑ slot ∈ setOne, S slot slot) + (∑ slot ∈ setTwo, S slot slot)
        + ∑ slot ∈ setThree, S slot slot := by
    rw [Finset.sum_union hunionTwo, Finset.sum_union hdisj12]
  have htotal : (∑ slot ∈ (setOne ∪ setTwo) ∪ setThree, S slot slot)
      ≤ ∑ slot : Fin data.basisCount, S slot slot :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun slot _ _ => hdiagNonneg slot
  have htraceS : (∑ slot : Fin data.basisCount, S slot slot) = 2 := by
    have hstep : Matrix.trace S = ∑ slot : Fin data.basisCount, S slot slot := rfl
    rw [← hstep, hStrace, htrace]
  rw [hsumUnion, htraceS] at htotal
  linarith [hfloorOne, hfloorTwo, hfloorThree, htotal, hbudget]

/-- **THE SHARED CO-CARRIER.**  Among three interior atoms two of them
miss one and the same live slot.  This is the positive form of the
disjoint co-carrier kill, and it is the shape the residue consumes. -/
theorem SharedPrivateData.exists_shared_coCarrier {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2)
    {atomOne atomTwo atomThree : Fin 6}
    (hne12 : atomOne ≠ atomTwo) (hne13 : atomOne ≠ atomThree)
    (hne23 : atomTwo ≠ atomThree)
    (hposOne : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne)
    (hposTwo : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomTwo)
    (hposThree : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomThree) :
    ∃ (slot : Fin data.basisCount) (probe : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight probe
        ∧ probe ∈ datumTightSupport data.tightDir (data.basisLabel slot)
        ∧ ((atomOne ∉ datumTightSupport data.tightDir (data.basisLabel slot)
              ∧ atomTwo ∉ datumTightSupport data.tightDir (data.basisLabel slot))
          ∨ (atomOne ∉ datumTightSupport data.tightDir (data.basisLabel slot)
              ∧ atomThree ∉ datumTightSupport data.tightDir (data.basisLabel slot))
          ∨ (atomTwo ∉ datumTightSupport data.tightDir (data.basisLabel slot)
              ∧ atomThree ∉ datumTightSupport data.tightDir
                  (data.basisLabel slot))) := by
  classical
  by_contra hnone
  have hsep : ∀ (slot : Fin data.basisCount) (probe : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight probe →
      probe ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      ¬((atomOne ∉ datumTightSupport data.tightDir (data.basisLabel slot)
            ∧ atomTwo ∉ datumTightSupport data.tightDir (data.basisLabel slot))
        ∨ (atomOne ∉ datumTightSupport data.tightDir (data.basisLabel slot)
            ∧ atomThree ∉ datumTightSupport data.tightDir (data.basisLabel slot))
        ∨ (atomTwo ∉ datumTightSupport data.tightDir (data.basisLabel slot)
            ∧ atomThree ∉ datumTightSupport data.tightDir
                (data.basisLabel slot))) := by
    intro slot probe hpos hmem hcase
    exact hnone ⟨slot, probe, hpos, hmem, hcase⟩
  set liveOff : Fin 6 → Finset (Fin data.basisCount) := fun atomIndex =>
    Finset.univ.filter fun slot =>
      atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot)
        ∧ ∃ probe : Fin 6,
            0 < chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight probe
            ∧ probe ∈ datumTightSupport data.tightDir (data.basisLabel slot)
    with hliveOff
  have hmemLiveOff : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      slot ∈ liveOff atomIndex ↔
        (atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot)
          ∧ ∃ probe : Fin 6,
              0 < chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight probe
              ∧ probe ∈ datumTightSupport data.tightDir (data.basisLabel slot)) := by
    intro atomIndex slot
    simp [hliveOff]
  have hsub : ∀ (atomIndex : Fin 6), ∀ slot ∈ liveOff atomIndex,
      atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot) :=
    fun atomIndex slot hslot => ((hmemLiveOff atomIndex slot).mp hslot).1
  have hcover : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot) →
      slot ∉ liveOff atomIndex → ∀ probe : Fin 6,
        0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight probe →
        probe ∉ datumTightSupport data.tightDir (data.basisLabel slot) := by
    intro atomIndex slot hoff hnot probe hpos hmem
    exact hnot ((hmemLiveOff atomIndex slot).mpr ⟨hoff, ⟨probe, hpos, hmem⟩⟩)
  have hdisjoint : ∀ (atomA atomB : Fin 6),
      (∀ slot : Fin data.basisCount,
        atomA ∉ datumTightSupport data.tightDir (data.basisLabel slot) →
        atomB ∉ datumTightSupport data.tightDir (data.basisLabel slot) →
        ∀ probe : Fin 6,
          0 < chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight probe →
          probe ∉ datumTightSupport data.tightDir (data.basisLabel slot)) →
      Disjoint (liveOff atomA) (liveOff atomB) := by
    intro atomA atomB hpair
    refine Finset.disjoint_left.mpr fun slot hslotA hslotB => ?_
    obtain ⟨hoffA, probe, hpos, hmem⟩ := (hmemLiveOff atomA slot).mp hslotA
    obtain ⟨hoffB, _⟩ := (hmemLiveOff atomB slot).mp hslotB
    exact hpair slot hoffA hoffB probe hpos hmem
  refine data.false_of_disjoint_coCarrier_triple hdiag htrace hne12 hne13 hne23
    hposOne hposTwo hposThree (hsub atomOne) (hsub atomTwo) (hsub atomThree)
    (hcover atomOne) (hcover atomTwo) (hcover atomThree) ?_ ?_ ?_
  · exact hdisjoint atomOne atomTwo fun slot hoffA hoffB probe hpos hmem =>
      hsep slot probe hpos hmem (Or.inl ⟨hoffA, hoffB⟩)
  · exact hdisjoint atomOne atomThree fun slot hoffA hoffB probe hpos hmem =>
      hsep slot probe hpos hmem (Or.inr (Or.inl ⟨hoffA, hoffB⟩))
  · exact hdisjoint atomTwo atomThree fun slot hoffA hoffB probe hpos hmem =>
      hsep slot probe hpos hmem (Or.inr (Or.inr ⟨hoffA, hoffB⟩))

/-! ## Layer 7 — the narrowed residue and the dispatches -/

/-- **THE LEAK RESIDUE.**  The confined residue of the basis-count-five
boundary stratum, with the shared co-carrier of every interior triple
supplied.  The disjoint co-carrier kill discharges that supply, thus this
residue is strictly weaker than the confined one. -/
def SharedPrivateBoundaryFiveLeakClosed : Prop :=
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
    (∀ (boundaryAtom : Fin 6),
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight boundaryAtom = 0 →
      ∀ (liveSlot : Fin data.basisCount) (interiorAtom : Fin 6),
        boundaryAtom ∈ datumTightSupport data.tightDir (data.basisLabel liveSlot) →
        0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight interiorAtom →
        interiorAtom ∈ datumTightSupport data.tightDir (data.basisLabel liveSlot) →
        ∃ otherSlot : Fin data.basisCount, otherSlot ≠ liveSlot
          ∧ boundaryAtom ∈ datumTightSupport data.tightDir
              (data.basisLabel otherSlot)
          ∧ ∃ probe : Fin 6,
              0 < chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight probe
              ∧ probe ∈ datumTightSupport data.tightDir
                  (data.basisLabel otherSlot)) →
    (∀ (interiorAtom : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight interiorAtom →
      ∃ slot : Fin data.basisCount,
        interiorAtom ∉ datumTightSupport data.tightDir (data.basisLabel slot)
        ∧ ∃ probe : Fin 6,
            0 < chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight probe
            ∧ probe ∈ datumTightSupport data.tightDir (data.basisLabel slot)) →
    (∀ atomOne atomTwo atomThree : Fin 6,
      atomOne ≠ atomTwo → atomOne ≠ atomThree → atomTwo ≠ atomThree →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomOne →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomTwo →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomThree →
      ∃ (slot : Fin data.basisCount) (probe : Fin 6),
        0 < chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight probe
          ∧ probe ∈ datumTightSupport data.tightDir (data.basisLabel slot)
          ∧ ((atomOne ∉ datumTightSupport data.tightDir (data.basisLabel slot)
                ∧ atomTwo ∉ datumTightSupport data.tightDir (data.basisLabel slot))
            ∨ (atomOne ∉ datumTightSupport data.tightDir (data.basisLabel slot)
                ∧ atomThree ∉ datumTightSupport data.tightDir
                    (data.basisLabel slot))
            ∨ (atomTwo ∉ datumTightSupport data.tightDir (data.basisLabel slot)
                ∧ atomThree ∉ datumTightSupport data.tightDir
                    (data.basisLabel slot)))) →
    False

/-- **THE LEAK DISPATCH.**  The disjoint co-carrier kill supplies the
shared co-carrier of every interior triple, thus the leak residue closes
the confined residue. -/
theorem sharedPrivateBoundaryFiveConfinedClosed_of_leak
    (hleak : SharedPrivateBoundaryFiveLeakClosed) :
    SharedPrivateBoundaryFiveConfinedClosed := by
  intro crux data gramDiag hdiag htrace hbasis hpin hmultOne hprivate hinteriorOut
    hthick hlow hhigh hsingle hcocarrier hoffCarrier
  exact hleak crux data gramDiag hdiag htrace hbasis hpin hmultOne hprivate
    hinteriorOut hthick hlow hhigh hsingle hcocarrier hoffCarrier
    fun atomOne atomTwo atomThree hne12 hne13 hne23 hposOne hposTwo hposThree =>
      data.exists_shared_coCarrier hdiag htrace hne12 hne13 hne23
        hposOne hposTwo hposThree

/-- The leak residue closes the whole trace-two boundary residue. -/
theorem sharedPrivateBoundaryClosed_of_leak
    (hleak : SharedPrivateBoundaryFiveLeakClosed) : SharedPrivateBoundaryClosed :=
  sharedPrivateBoundaryClosed_of_confined
    (sharedPrivateBoundaryFiveConfinedClosed_of_leak hleak)

/-- **THE STRATA DISPATCH.**  The extras residue and the leak residue
close the generic shared-private kill. -/
theorem sharedPrivateKilled_of_leak_energy_strata
    (hextras : SharedPrivateExtrasClosed)
    (hleak : SharedPrivateBoundaryFiveLeakClosed) : SharedPrivateKilled :=
  sharedPrivateKilled_of_confined_strata hextras
    (sharedPrivateBoundaryFiveConfinedClosed_of_leak hleak)

/-- The two residues discharge closure two of the rank-four rung. -/
theorem rankFourSharedPrivateClosed_of_leak_energy_strata
    (hextras : SharedPrivateExtrasClosed)
    (hleak : SharedPrivateBoundaryFiveLeakClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_confined_strata hextras
    (sharedPrivateBoundaryFiveConfinedClosed_of_leak hleak)

/-- The two residues discharge the shared-private closure of the
rank-five rung. -/
theorem rankFiveSharedPrivateClosed_of_leak_energy_strata
    (hextras : SharedPrivateExtrasClosed)
    (hleak : SharedPrivateBoundaryFiveLeakClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_confined_strata hextras
    (sharedPrivateBoundaryFiveConfinedClosed_of_leak hleak)

/-- The two residues discharge the shared-private closure of the
rank-six rung. -/
theorem rankSixSharedPrivateClosed_of_leak_energy_strata
    (hextras : SharedPrivateExtrasClosed)
    (hleak : SharedPrivateBoundaryFiveLeakClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_confined_strata hextras
    (sharedPrivateBoundaryFiveConfinedClosed_of_leak hleak)

end Gtz
