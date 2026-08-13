import Gtz.Wave.SharedPrivateCertificateReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The complement-trace calculus — the interior kill of the shared-private shape

The shared-private extraction campaign found that the diagonal-Gram
system dies at every rung with floors linear in the value.  This module
gives the reason as a short trace argument, with no dual certificate.

The mechanism.  Each atom reads one eigenvalue of a carrier corner of a
symmetric idempotent.  The leak vector of the read is an eigenvector of
the complementary corner with the complementary eigenvalue.  The
complementary corner is positive semidefinite, thus its diagonal sum
dominates the complementary eigenvalue.  This caps every carrier
diagonal sum by the trace minus one plus the shifted weight.  A
multiplicity-one atom pins its carrier diagonal exactly, with slack one
less than the trace.  The double count of the carrier incidences then
forces the shifted weight sum to the nonnegative side, against a
negative value.

At trace two, one pin kills.  At trace three, two pins kill.  The
boundary stratum `value + weight = 0` sits outside this argument, and
the boundary law of this module upgrades it: at the boundary every
ranged direction has a vanishing projected read at the atom, thus the
whole carried-row system annihilates there.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.read_leak_apply_eq_zero`, `Gtz.read_leak_dotProduct_eq_zero`,
  `Gtz.mulVec_read_leak`, `Gtz.read_leak_ne_zero_of_open_interval`,
  `Gtz.read_leak_quadratic_eq` — the leak calculus of a corner read.
* `Gtz.posSemidef_of_transpose_eq_of_idem` — a symmetric idempotent is
  positive semidefinite.
* `Gtz.masked_quadratic_le_compl_trace` — **THE MASKED TRACE FLOOR.**
* `Gtz.compl_diag_floor_of_read` — the complement diagonal floor.
* `Gtz.carrier_diag_cap_of_read` — **THE CARRIER CAP.**
* `Gtz.pin_diag_eq_of_read` — the multiplicity-one pin.
* `Gtz.interior_carrier_budget` — **THE BUDGET** over any pin set.
* `Gtz.false_of_interior_budget_trace_two`,
  `Gtz.false_of_interior_budget_trace_three` — **THE INTERIOR KILLS.**
* `Gtz.projected_direction_read_zero_of_diagonal_zero`,
  `Gtz.basis_capture_column_zero_of_diagonal_zero` — **THE BOUNDARY
  UPGRADE** at `value + weight = 0`.

## Vacuity

The matrix statements are unconditional.  The ambient statements
quantify over stationary data only.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the leak calculus of a corner read -/

variable {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
variable {carrier : Finset (Fin n)} {readVec : Fin n → ℝ} {readVal : ℝ}

/-- The leak of a corner read vanishes on the carrier set. -/
theorem read_leak_apply_eq_zero
    (hread : ∀ slot ∈ carrier, (S *ᵥ readVec) slot = readVal * readVec slot)
    {slot : Fin n} (hslot : slot ∈ carrier) :
    (S *ᵥ readVec - readVal • readVec) slot = 0 := by
  have h := hread slot hslot
  simp [h]

/-- The read vector and its leak have disjoint supports, thus their dot
product vanishes. -/
theorem read_leak_dotProduct_eq_zero
    (hsupp : ∀ slot ∉ carrier, readVec slot = 0)
    (hread : ∀ slot ∈ carrier, (S *ᵥ readVec) slot = readVal * readVec slot) :
    readVec ⬝ᵥ (S *ᵥ readVec - readVal • readVec) = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero fun slot _ => ?_
  by_cases hslot : slot ∈ carrier
  · rw [read_leak_apply_eq_zero hread hslot, mul_zero]
  · rw [hsupp slot hslot, zero_mul]

/-- The idempotent moves the leak by the complementary eigenvalue, with a
read-vector correction. -/
theorem mulVec_read_leak (hidem : S * S = S) :
    S *ᵥ (S *ᵥ readVec - readVal • readVec)
      = (1 - readVal) • (S *ᵥ readVec - readVal • readVec)
        + (readVal * (1 - readVal)) • readVec := by
  have hSS : S *ᵥ (S *ᵥ readVec) = S *ᵥ readVec := by
    rw [Matrix.mulVec_mulVec, hidem]
  funext slot
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hSS, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A vanishing leak makes the read vector a global eigenvector, and the
idempotent spectrum refuses an eigenvalue inside the open unit interval. -/
theorem read_leak_ne_zero_of_open_interval (hidem : S * S = S)
    (hnz : readVec ≠ 0) (hd0 : 0 < readVal) (hd1 : readVal < 1) :
    S *ᵥ readVec - readVal • readVec ≠ 0 := by
  intro hzero
  have heig : S *ᵥ readVec = readVal • readVec := sub_eq_zero.mp hzero
  have hSS : S *ᵥ (S *ᵥ readVec) = S *ᵥ readVec := by
    rw [Matrix.mulVec_mulVec, hidem]
  rw [heig, Matrix.mulVec_smul, heig, smul_smul] at hSS
  have hvec : (readVal * readVal - readVal) • readVec = 0 := by
    rw [sub_smul, hSS, sub_self]
  have hcoeff : readVal * readVal - readVal ≠ 0 := by
    intro h
    have hfactor : readVal * (readVal - 1) = 0 := by
      have : readVal * (readVal - 1) = readVal * readVal - readVal := by ring
      rw [this, h]
    rcases mul_eq_zero.mp hfactor with h0 | h1
    · exact (ne_of_gt hd0) h0
    · exact (ne_of_lt hd1) (by linarith)
  exact hnz ((smul_eq_zero.mp hvec).resolve_left hcoeff)

/-- The leak's quadratic form against the idempotent reads the
complementary eigenvalue times the leak's square norm. -/
theorem read_leak_quadratic_eq (hidem : S * S = S)
    (hsupp : ∀ slot ∉ carrier, readVec slot = 0)
    (hread : ∀ slot ∈ carrier, (S *ᵥ readVec) slot = readVal * readVec slot) :
    (S *ᵥ readVec - readVal • readVec)
        ⬝ᵥ (S *ᵥ (S *ᵥ readVec - readVal • readVec))
      = (1 - readVal)
        * ((S *ᵥ readVec - readVal • readVec)
            ⬝ᵥ (S *ᵥ readVec - readVal • readVec)) := by
  rw [mulVec_read_leak hidem, dotProduct_add, dotProduct_smul,
    dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hcomm : (S *ᵥ readVec - readVal • readVec) ⬝ᵥ readVec
      = readVec ⬝ᵥ (S *ᵥ readVec - readVal • readVec) :=
    dotProduct_comm _ _
  rw [hcomm, read_leak_dotProduct_eq_zero hsupp hread, mul_zero, add_zero]

/-! ## Layer 2 — the masked trace floor -/

/-- A symmetric idempotent is positive semidefinite. -/
theorem posSemidef_of_transpose_eq_of_idem
    (hsymm : Sᵀ = S) (hidem : S * S = S) : S.PosSemidef := by
  have hfactor : S = Sᴴ * S := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hsymm, hidem]
  rw [hfactor]
  exact Matrix.posSemidef_conjTranspose_mul_self S

/-- **THE MASKED TRACE FLOOR.**  A quadratic form of a positive
semidefinite matrix on a vector that vanishes on a set is capped by the
complementary diagonal sum times the square norm. -/
theorem masked_quadratic_le_compl_trace
    (hpsd : S.PosSemidef) (blockSet : Finset (Fin n)) {probe : Fin n → ℝ}
    (hprobe : ∀ slot ∈ blockSet, probe slot = 0) :
    probe ⬝ᵥ (S *ᵥ probe)
      ≤ (∑ slot ∈ blockSetᶜ, S slot slot) * (probe ⬝ᵥ probe) := by
  classical
  set maskVec : Fin n → ℝ := fun slot => if slot ∈ blockSet then 0 else 1
    with hmaskVec
  set maskMat := Matrix.diagonal maskVec with hmaskMat
  have hmasksymm : maskMatᴴ = maskMat := by
    rw [hmaskMat, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.diagonal_transpose]
  have hfix : maskMat *ᵥ probe = probe := by
    funext slot
    rw [hmaskMat, Matrix.mulVec_diagonal, hmaskVec]
    by_cases hslot : slot ∈ blockSet
    · simp [hslot, hprobe slot hslot]
    · simp [hslot]
  have hmaskedpsd : (maskMat * S * maskMat).PosSemidef := by
    have h := hpsd.mul_mul_conjTranspose_same maskMat
    rwa [hmasksymm] at h
  have hquad := quadratic_le_trace_mul_self hmaskedpsd probe
  have hexpand : (maskMat * S * maskMat) *ᵥ probe
      = maskMat *ᵥ (S *ᵥ probe) := by
    rw [← Matrix.mulVec_mulVec, hfix, ← Matrix.mulVec_mulVec]
  have hform : probe ⬝ᵥ ((maskMat * S * maskMat) *ᵥ probe)
      = probe ⬝ᵥ (S *ᵥ probe) := by
    rw [hexpand, dotProduct, dotProduct]
    refine Finset.sum_congr rfl fun slot _ => ?_
    rw [hmaskMat, Matrix.mulVec_diagonal, hmaskVec]
    by_cases hslot : slot ∈ blockSet
    · simp [hslot, hprobe slot hslot]
    · simp [hslot]
  have htrace : Matrix.trace (maskMat * S * maskMat)
      = ∑ slot ∈ blockSetᶜ, S slot slot := by
    have hentry : ∀ slot : Fin n, (maskMat * S * maskMat).diag slot
        = if slot ∈ blockSetᶜ then S slot slot else 0 := by
      intro slot
      rw [Matrix.diag_apply, hmaskMat, Matrix.mul_diagonal,
        Matrix.diagonal_mul, hmaskVec]
      by_cases hslot : slot ∈ blockSet
      · simp [hslot]
      · simp [hslot]
    rw [Matrix.trace, Finset.sum_congr rfl fun slot _ => hentry slot,
      Finset.sum_ite_mem, Finset.univ_inter]
  rw [hform, htrace] at hquad
  exact hquad

/-! ## Layer 3 — the carrier cap, the pin, the budget, and the kills -/

/-- The complement diagonal floor: the complementary diagonal sum
dominates the complementary eigenvalue of an interior read. -/
theorem compl_diag_floor_of_read (hsymm : Sᵀ = S) (hidem : S * S = S)
    (hsupp : ∀ slot ∉ carrier, readVec slot = 0)
    (hread : ∀ slot ∈ carrier, (S *ᵥ readVec) slot = readVal * readVec slot)
    (hnz : readVec ≠ 0) (hd0 : 0 < readVal) (hd1 : readVal < 1) :
    1 - readVal ≤ ∑ slot ∈ carrierᶜ, S slot slot := by
  classical
  have hpsd := posSemidef_of_transpose_eq_of_idem hsymm hidem
  have hleakzero : ∀ slot ∈ carrier,
      (S *ᵥ readVec - readVal • readVec) slot = 0 :=
    fun slot hslot => read_leak_apply_eq_zero hread hslot
  have hquad := masked_quadratic_le_compl_trace hpsd carrier hleakzero
  have heq := read_leak_quadratic_eq hidem hsupp hread
  have hne := read_leak_ne_zero_of_open_interval hidem hnz hd0 hd1
  have hpos : 0 < (S *ᵥ readVec - readVal • readVec)
      ⬝ᵥ (S *ᵥ readVec - readVal • readVec) := by
    obtain ⟨slot, hslot⟩ := Function.ne_iff.mp hne
    refine Finset.sum_pos' (fun i _ => mul_self_nonneg _) ?_
    exact ⟨slot, Finset.mem_univ slot, mul_self_pos.mpr (by simpa using hslot)⟩
  rw [heq] at hquad
  exact le_of_mul_le_mul_right hquad hpos

/-- **THE CARRIER CAP.**  The carrier diagonal sum of an interior read is
capped by the trace minus one plus the read value. -/
theorem carrier_diag_cap_of_read (hsymm : Sᵀ = S) (hidem : S * S = S)
    (hsupp : ∀ slot ∉ carrier, readVec slot = 0)
    (hread : ∀ slot ∈ carrier, (S *ᵥ readVec) slot = readVal * readVec slot)
    (hnz : readVec ≠ 0) (hd0 : 0 < readVal) (hd1 : readVal < 1) :
    ∑ slot ∈ carrier, S slot slot ≤ Matrix.trace S - 1 + readVal := by
  classical
  have hfloor := compl_diag_floor_of_read hsymm hidem hsupp hread hnz hd0 hd1
  have hsplit : ∑ slot ∈ carrier, S slot slot
      + ∑ slot ∈ carrierᶜ, S slot slot = Matrix.trace S := by
    rw [Matrix.trace]
    exact Finset.sum_add_sum_compl carrier fun slot => S slot slot
  linarith

/-- The multiplicity-one pin: a singleton carrier reads the diagonal
entry exactly. -/
theorem pin_diag_eq_of_read
    (hsupp : ∀ slot ∉ carrier, readVec slot = 0)
    (hread : ∀ slot ∈ carrier, (S *ᵥ readVec) slot = readVal * readVec slot)
    (hnz : readVec ≠ 0) {pinSlot : Fin n} (hpin : carrier = {pinSlot}) :
    S pinSlot pinSlot = readVal := by
  classical
  have hvpin : readVec pinSlot ≠ 0 := by
    intro hzero
    apply hnz
    funext slot
    by_cases hslot : slot = pinSlot
    · rw [hslot, hzero]; rfl
    · exact hsupp slot (by rw [hpin, Finset.mem_singleton]; exact hslot)
  have hcollapse : (S *ᵥ readVec) pinSlot
      = S pinSlot pinSlot * readVec pinSlot := by
    rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_single pinSlot (fun slot _ hne => ?_) (by simp)
    rw [hsupp slot (by rw [hpin, Finset.mem_singleton]; exact hne), mul_zero]
  have hval := hread pinSlot (by rw [hpin]; exact Finset.mem_singleton_self _)
  rw [hcollapse] at hval
  exact mul_right_cancel₀ hvpin hval

/-- **THE BUDGET.**  Six atoms read a symmetric idempotent through their
carrier sets, each slot carries a fixed atom count, and a pin set of
multiplicity-one atoms reads exactly.  The double count then caps the
block count times the trace by the pin-free cap mass plus the read sum. -/
theorem interior_carrier_budget {m : ℕ} (hsymm : Sᵀ = S)
    (hidem : S * S = S) (car : Fin m → Finset (Fin n))
    (v : Fin m → Fin n → ℝ) (d : Fin m → ℝ) (blockCount : ℕ)
    (hinc : ∀ slot : Fin n,
      (Finset.univ.filter fun atom => slot ∈ car atom).card = blockCount)
    (hsupp : ∀ atom, ∀ slot ∉ car atom, v atom slot = 0)
    (hnz : ∀ atom, v atom ≠ 0)
    (hread : ∀ atom, ∀ slot ∈ car atom,
      (S *ᵥ v atom) slot = d atom * v atom slot)
    (pinSet : Finset (Fin m))
    (hpin : ∀ atom ∈ pinSet, ∃ pinSlot, car atom = {pinSlot})
    (hd0 : ∀ atom ∉ pinSet, 0 < d atom)
    (hd1 : ∀ atom ∉ pinSet, d atom < 1) :
    (blockCount : ℝ) * Matrix.trace S
      ≤ ((m : ℝ) - pinSet.card) * (Matrix.trace S - 1) + ∑ atom, d atom := by
  classical
  -- the double count of the carrier incidences
  have hdouble : ∑ atom, (∑ slot ∈ car atom, S slot slot)
      = (blockCount : ℝ) * Matrix.trace S := by
    have hswap : ∑ atom, (∑ slot ∈ car atom, S slot slot)
        = ∑ slot, ∑ atom,
            (if slot ∈ car atom then S slot slot else 0) := by
      rw [← Finset.sum_comm]
      refine Finset.sum_congr rfl fun atom _ => ?_
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [hswap]
    have hinner : ∀ slot : Fin n,
        (∑ atom, (if slot ∈ car atom then S slot slot else 0))
          = (blockCount : ℝ) * S slot slot := by
      intro slot
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hinc slot]
    rw [Finset.sum_congr rfl fun slot _ => hinner slot, ← Finset.mul_sum,
      Matrix.trace]
    rfl
  -- the pin equalities and the caps
  have hpineq : ∀ atom ∈ pinSet,
      (∑ slot ∈ car atom, S slot slot) = d atom := by
    intro atom hatom
    obtain ⟨pinSlot, hps⟩ := hpin atom hatom
    rw [hps, Finset.sum_singleton]
    exact pin_diag_eq_of_read (hsupp atom) (hread atom) (hnz atom) hps
  have hcap : ∀ atom ∉ pinSet,
      (∑ slot ∈ car atom, S slot slot)
        ≤ Matrix.trace S - 1 + d atom := by
    intro atom hatom
    exact carrier_diag_cap_of_read hsymm hidem (hsupp atom) (hread atom)
      (hnz atom) (hd0 atom hatom) (hd1 atom hatom)
  -- assemble
  have hsplitS : ∑ atom ∈ pinSet, (∑ slot ∈ car atom, S slot slot)
      + ∑ atom ∈ pinSetᶜ, (∑ slot ∈ car atom, S slot slot)
      = ∑ atom, (∑ slot ∈ car atom, S slot slot) :=
    Finset.sum_add_sum_compl pinSet _
  have hsplitd : ∑ atom ∈ pinSet, d atom + ∑ atom ∈ pinSetᶜ, d atom
      = ∑ atom, d atom :=
    Finset.sum_add_sum_compl pinSet d
  have hpinsum : ∑ atom ∈ pinSet, (∑ slot ∈ car atom, S slot slot)
      = ∑ atom ∈ pinSet, d atom :=
    Finset.sum_congr rfl hpineq
  have hcapsum : ∑ atom ∈ pinSetᶜ, (∑ slot ∈ car atom, S slot slot)
      ≤ ∑ atom ∈ pinSetᶜ, (Matrix.trace S - 1 + d atom) :=
    Finset.sum_le_sum fun atom hatom =>
      hcap atom (Finset.mem_compl.mp hatom)
  have hcapexpand : ∑ atom ∈ pinSetᶜ, (Matrix.trace S - 1 + d atom)
      = (pinSetᶜ.card : ℝ) * (Matrix.trace S - 1)
        + ∑ atom ∈ pinSetᶜ, d atom := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hcard : (pinSetᶜ.card : ℝ) = (m : ℝ) - pinSet.card := by
    rw [Finset.card_compl]
    have hle : pinSet.card ≤ Fintype.card (Fin m) := Finset.card_le_univ _
    rw [Nat.cast_sub hle, Fintype.card_fin]
  rw [hcard] at hcapexpand
  linarith

/-- **THE TRACE-TWO INTERIOR KILL.**  Six atoms, three atoms in each
slot's block, one multiplicity-one pin, interior shifted weights that
sum to `6 * value + 1`, a trace-two symmetric idempotent: the value is
nonnegative.  A negative value dies. -/
theorem false_of_interior_budget_trace_two (hsymm : Sᵀ = S)
    (hidem : S * S = S) (htrace : Matrix.trace S = 2)
    (car : Fin 6 → Finset (Fin n)) (v : Fin 6 → Fin n → ℝ)
    (d : Fin 6 → ℝ) {value : ℝ}
    (hinc : ∀ slot : Fin n,
      (Finset.univ.filter fun atom => slot ∈ car atom).card = 3)
    (hsupp : ∀ atom, ∀ slot ∉ car atom, v atom slot = 0)
    (hnz : ∀ atom, v atom ≠ 0)
    (hread : ∀ atom, ∀ slot ∈ car atom,
      (S *ᵥ v atom) slot = d atom * v atom slot)
    (hd0 : ∀ atom, 0 < d atom) (hd1 : ∀ atom, d atom < 1)
    (hsum : ∑ atom, d atom = 6 * value + 1) (hneg : value < 0)
    {pinAtom : Fin 6} {pinSlot : Fin n} (hpin : car pinAtom = {pinSlot}) :
    False := by
  classical
  have hbudget := interior_carrier_budget hsymm hidem car v d 3 hinc hsupp
    hnz hread {pinAtom}
    (fun atom hatom => ⟨pinSlot, by
      rw [Finset.mem_singleton] at hatom
      rw [hatom]; exact hpin⟩)
    (fun atom _ => hd0 atom) (fun atom _ => hd1 atom)
  rw [htrace, hsum, Finset.card_singleton] at hbudget
  norm_num at hbudget
  linarith

/-- **THE TRACE-THREE INTERIOR KILL.**  The same shape with a trace-three
idempotent dies when two distinct atoms carry multiplicity one. -/
theorem false_of_interior_budget_trace_three (hsymm : Sᵀ = S)
    (hidem : S * S = S) (htrace : Matrix.trace S = 3)
    (car : Fin 6 → Finset (Fin n)) (v : Fin 6 → Fin n → ℝ)
    (d : Fin 6 → ℝ) {value : ℝ}
    (hinc : ∀ slot : Fin n,
      (Finset.univ.filter fun atom => slot ∈ car atom).card = 3)
    (hsupp : ∀ atom, ∀ slot ∉ car atom, v atom slot = 0)
    (hnz : ∀ atom, v atom ≠ 0)
    (hread : ∀ atom, ∀ slot ∈ car atom,
      (S *ᵥ v atom) slot = d atom * v atom slot)
    (hd0 : ∀ atom, 0 < d atom) (hd1 : ∀ atom, d atom < 1)
    (hsum : ∑ atom, d atom = 6 * value + 1) (hneg : value < 0)
    {pinAtomOne pinAtomTwo : Fin 6} {pinSlotOne pinSlotTwo : Fin n}
    (hne : pinAtomOne ≠ pinAtomTwo)
    (hpinOne : car pinAtomOne = {pinSlotOne})
    (hpinTwo : car pinAtomTwo = {pinSlotTwo}) :
    False := by
  classical
  have hcardpair : ({pinAtomOne, pinAtomTwo} : Finset (Fin 6)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have hbudget := interior_carrier_budget hsymm hidem car v d 3 hinc hsupp
    hnz hread {pinAtomOne, pinAtomTwo}
    (fun atom hatom => by
      rcases Finset.mem_insert.mp hatom with h1 | h2
      · exact ⟨pinSlotOne, by rw [h1]; exact hpinOne⟩
      · exact ⟨pinSlotTwo, by
          rw [Finset.mem_singleton] at h2
          rw [h2]; exact hpinTwo⟩)
    (fun atom _ => hd0 atom) (fun atom _ => hd1 atom)
  rw [htrace, hsum, hcardpair] at hbudget
  norm_num at hbudget
  linarith

/-! ## Layer 4 — the boundary upgrade at `value + weight = 0` -/

variable {size rank : ℕ} {activeIndex : Type}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE BOUNDARY UPGRADE.**  At a zero captured diagonal, every
direction in the assembly range has a vanishing projected read at the
atom.  The projected axis dies in the assembly kernel, and the assembly
symmetry moves the annihilation to every ranged direction. -/
theorem projected_direction_read_zero_of_diagonal_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {atomIndex : Fin size} (hzero : value + weight atomIndex = 0)
    {direction : Fin size → ℝ}
    (hranged : ∃ preimage,
      chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ preimage
        = direction) :
    (projection *ᵥ direction) atomIndex = 0 := by
  obtain ⟨preimage, hpre⟩ := hranged
  have hann := assembly_mulVec_projection_single_of_diagonal_zero hdata hzero
  have hsymmXi : (chartMultiplierAssembly activeSet activeWeight tightDir)ᵀ
      = chartMultiplierAssembly activeSet activeWeight tightDir := by
    have h :=
      (posSemidef_chartMultiplierAssembly_of_isChartStationaryData hdata).1
    have h2 : (chartMultiplierAssembly activeSet activeWeight tightDir)ᴴ
        = chartMultiplierAssembly activeSet activeWeight tightDir := h
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  have hcol : ∀ rowIndex : Fin size,
      (projection *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ)) rowIndex
        = projection rowIndex atomIndex := by
    intro rowIndex
    rw [Matrix.mulVec_single_one]
    simp [Matrix.col]
  have hswap : (projection *ᵥ direction) atomIndex
      = (projection *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ)) ⬝ᵥ direction := by
    rw [Matrix.mulVec, dotProduct, dotProduct]
    refine Finset.sum_congr rfl fun colIndex _ => ?_
    rw [hcol colIndex]
    have hsym : projection colIndex atomIndex
        = projection atomIndex colIndex := by
      have h := congrFun (congrFun hdata.isSymmetric colIndex) atomIndex
      rw [Matrix.transpose_apply] at h
      exact h.symm
    rw [hsym]
  rw [hswap, ← hpre, Matrix.dotProduct_mulVec]
  have hvm : (projection *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ)) ᵥ*
      chartMultiplierAssembly activeSet activeWeight tightDir
      = chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ
        (projection *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ)) := by
    have hvt := Matrix.vecMul_transpose
      (A := chartMultiplierAssembly activeSet activeWeight tightDir)
      (x := projection *ᵥ (Pi.single atomIndex 1 : Fin size → ℝ))
    rw [hsymmXi] at hvt
    exact hvt
  rw [hvm, hann, zero_dotProduct]

/-- **THE CARRIED-ROW ANNIHILATION.**  At a zero captured diagonal, the
whole basis capture row vanishes: every entry of `B * M` at the atom is
zero.  The carried-row system collapses at the boundary atom. -/
theorem basis_capture_column_zero_of_diagonal_zero {basisCount : ℕ}
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hspan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (hrep : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {atomIndex : Fin size} (hzero : value + weight atomIndex = 0)
    (columnIndex : Fin basisCount) :
    (tightBasisColumns tightDir basisLabel * coeff) atomIndex columnIndex
      = 0 := by
  rw [← hrep]
  have hentry : (projection * tightBasisColumns tightDir basisLabel)
      atomIndex columnIndex
      = (projection *ᵥ tightDir (basisLabel columnIndex)) atomIndex := by
    rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rfl
  rw [hentry]
  apply projected_direction_read_zero_of_diagonal_zero hdata hzero
  have hmem : tightDir (basisLabel columnIndex) ∈ Submodule.span ℝ
      (Set.range fun c => tightDir (basisLabel c)) :=
    Submodule.subset_span ⟨columnIndex, rfl⟩
  rw [hspan] at hmem
  obtain ⟨preimage, hpreimage⟩ := LinearMap.mem_range.mp hmem
  exact ⟨preimage, by rw [← Matrix.toLin'_apply]; exact hpreimage⟩

/-! ## Layer 5 — the diagonal-Gram interior discharge -/

set_option maxHeartbeats 1600000 in
/-- **THE DIAGONAL-GRAM INTERIOR DISCHARGE.**  A shared-private datum
with a diagonal Gram core and interior shifted weights dies.  At trace
three the kill consumes one more multiplicity-one atom.  The diagonal
conjugation of the coefficient matrix is an orthogonal projection, the
carried rows become corner reads, and the budget kills. -/
theorem SharedPrivateData.false_of_diagonal_gram_interior
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (hint : ∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
    (hsecond : Matrix.trace data.coeff = 3 →
      ∃ atomTwo : Fin 6, atomTwo ≠ data.pinAtom ∧
        basisSupportMultiplicity data.tightDir data.basisLabel atomTwo = 1) :
    False := by
  classical
  set chartValue := chartObjective (chartPointOfDesign crux.design)
    with hchartValue
  set atomWeight := (chartPointOfDesign crux.design).weight with hatomWeight
  have hneg : chartValue < 0 := data.hvalueNeg
  -- the positive diagonal of the Gram core
  have hpsd := data.hpsd
  have hker := data.hker
  rw [hdiag] at hpsd hker
  have hg : ∀ slot, 0 < gramDiag slot := by
    intro slot
    have h := posSemidef_diagonal_pos_of_kernel_free hpsd hker slot
    rwa [Matrix.diagonal_apply_eq] at h
  set sq : Fin data.basisCount → ℝ := fun slot => Real.sqrt (gramDiag slot)
    with hsqdef
  have hsq : ∀ slot, 0 < sq slot := fun slot => Real.sqrt_pos.mpr (hg slot)
  have hsqsq : ∀ slot, sq slot * sq slot = gramDiag slot :=
    fun slot => Real.mul_self_sqrt (hg slot).le
  -- the exchange entries under the diagonal core
  have hexchange := data.hexchange
  rw [hdiag] at hexchange
  have hx : ∀ rowSlot colSlot, data.coeff rowSlot colSlot * gramDiag colSlot
      = gramDiag rowSlot * data.coeff colSlot rowSlot := by
    intro rowSlot colSlot
    have h := congrFun (congrFun hexchange rowSlot) colSlot
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.transpose_apply] at h
  -- the conjugated coefficient matrix
  set S : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ :=
    Matrix.of fun rowSlot colSlot =>
      (sq rowSlot)⁻¹ * (data.coeff rowSlot colSlot * sq colSlot) with hSdef
  have hSapply : ∀ rowSlot colSlot, S rowSlot colSlot
      = (sq rowSlot)⁻¹ * (data.coeff rowSlot colSlot * sq colSlot) :=
    fun _ _ => rfl
  -- the conjugate is symmetric
  have hSsymm : Sᵀ = S := by
    ext rowSlot colSlot
    rw [Matrix.transpose_apply, hSapply, hSapply]
    refine mul_left_cancel₀
      (mul_ne_zero (hsq rowSlot).ne' (hsq colSlot).ne') ?_
    have hci : sq rowSlot * (sq rowSlot)⁻¹ = 1 :=
      mul_inv_cancel₀ (hsq rowSlot).ne'
    have hcj : sq colSlot * (sq colSlot)⁻¹ = 1 :=
      mul_inv_cancel₀ (hsq colSlot).ne'
    have hgi := hsqsq rowSlot
    have hgj := hsqsq colSlot
    have hxi := hx rowSlot colSlot
    linear_combination
      (data.coeff colSlot rowSlot * sq rowSlot * sq rowSlot) * hcj
      - (data.coeff rowSlot colSlot * sq colSlot * sq colSlot) * hci
      + data.coeff colSlot rowSlot * hgi
      - data.coeff rowSlot colSlot * hgj
      - hxi
  -- the conjugate is idempotent
  have hSidem : S * S = S := by
    ext rowSlot colSlot
    rw [Matrix.mul_apply]
    have hterm : ∀ midSlot, S rowSlot midSlot * S midSlot colSlot
        = (sq rowSlot)⁻¹
          * (data.coeff rowSlot midSlot * data.coeff midSlot colSlot)
          * sq colSlot := by
      intro midSlot
      rw [hSapply, hSapply]
      have hck : sq midSlot * (sq midSlot)⁻¹ = 1 :=
        mul_inv_cancel₀ (hsq midSlot).ne'
      linear_combination ((sq rowSlot)⁻¹ * data.coeff rowSlot midSlot
        * data.coeff midSlot colSlot * sq colSlot) * hck
    rw [Finset.sum_congr rfl fun midSlot _ => hterm midSlot,
      ← Finset.sum_mul, ← Finset.mul_sum]
    have hMM : ∑ midSlot, data.coeff rowSlot midSlot
        * data.coeff midSlot colSlot = data.coeff rowSlot colSlot := by
      have h := congrFun (congrFun data.hidempotent rowSlot) colSlot
      rwa [Matrix.mul_apply] at h
    rw [hMM, hSapply]
    ring
  -- the conjugate keeps the trace
  have hStrace : Matrix.trace S = Matrix.trace data.coeff := by
    rw [Matrix.trace, Matrix.trace]
    refine Finset.sum_congr rfl fun slot _ => ?_
    have h : S slot slot = (sq slot)⁻¹ * (data.coeff slot slot * sq slot) :=
      rfl
    have hinv : (sq slot)⁻¹ * sq slot = 1 :=
      inv_mul_cancel₀ (hsq slot).ne'
    show S slot slot = data.coeff slot slot
    rw [h]
    linear_combination data.coeff slot slot * hinv
  -- the carrier system
  set car : Fin 6 → Finset (Fin data.basisCount) := fun atomIndex =>
    Finset.univ.filter fun slot =>
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)
    with hcardef
  set readVecs : Fin 6 → Fin data.basisCount → ℝ := fun atomIndex slot =>
    sq slot * data.tightDir (data.basisLabel slot) atomIndex with hreadVecs
  set shifted : Fin 6 → ℝ := fun atomIndex =>
    chartValue + atomWeight atomIndex with hshifted
  have hmemActive : ∀ slot, data.basisLabel slot ∈ data.activeSet := by
    intro slot
    have h := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at h
    exact h.1
  have hcarmem : ∀ atomIndex slot, slot ∈ car atomIndex ↔
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
    intro atomIndex slot
    simp [hcardef]
  -- the support law
  have hsupp : ∀ atomIndex, ∀ slot ∉ car atomIndex,
      readVecs atomIndex slot = 0 := by
    intro atomIndex slot hslot
    rw [hcarmem, mem_datumTightSupport, not_not] at hslot
    show sq slot * data.tightDir (data.basisLabel slot) atomIndex = 0
    rw [hslot, mul_zero]
  -- the coverage law
  have hnz : ∀ atomIndex, readVecs atomIndex ≠ 0 := by
    intro atomIndex hzero
    obtain ⟨slot, hslot⟩ := exists_basisIndex_datumTightSupport data.hdata
      data.basisLabel data.hspan data.leftInv data.hleft atomIndex
    have hq := mem_datumTightSupport.mp hslot
    have hv : readVecs atomIndex slot = 0 := congrFun hzero slot
    exact mul_ne_zero (hsq slot).ne' hq hv
  -- the carried rows
  have hcarried : ∀ slot, ∀ atomIndex ∈ data.activeSubset
      (data.basisLabel slot),
      ∑ colSlot, data.tightDir (data.basisLabel colSlot) atomIndex
        * data.coeff colSlot slot
      = shifted atomIndex * data.tightDir (data.basisLabel slot) atomIndex := by
    intro slot atomIndex hmemSubset
    have hrep := congrFun (congrFun data.hrepresentation atomIndex) slot
    rw [Matrix.mul_apply, Matrix.mul_apply] at hrep
    have hproj := projection_mulVec_tightDir_of_mem data.hdata
      (hmemActive slot) hmemSubset
    have hlhs : ∑ x, (chartPointOfDesign crux.design).chart atomIndex x
        * tightBasisColumns data.tightDir data.basisLabel x slot
        = ((chartPointOfDesign crux.design).chart
            *ᵥ data.tightDir (data.basisLabel slot)) atomIndex := rfl
    rw [hlhs, hproj] at hrep
    exact hrep.symm
  -- the corner reads
  have hread : ∀ atomIndex, ∀ slot ∈ car atomIndex,
      (S *ᵥ readVecs atomIndex) slot
        = shifted atomIndex * readVecs atomIndex slot := by
    intro atomIndex slot hslot
    have hmemSubset : atomIndex ∈ data.activeSubset (data.basisLabel slot) :=
      datumTightSupport_subset data.hdata (hmemActive slot)
        ((hcarmem atomIndex slot).mp hslot)
    have hterm : ∀ colSlot, S slot colSlot * readVecs atomIndex colSlot
        = ((sq slot)⁻¹ * gramDiag slot)
          * (data.tightDir (data.basisLabel colSlot) atomIndex
              * data.coeff colSlot slot) := by
      intro colSlot
      rw [hSapply]
      show (sq slot)⁻¹ * (data.coeff slot colSlot * sq colSlot)
          * (sq colSlot * data.tightDir (data.basisLabel colSlot) atomIndex)
        = ((sq slot)⁻¹ * gramDiag slot)
          * (data.tightDir (data.basisLabel colSlot) atomIndex
              * data.coeff colSlot slot)
      have hgj := hsqsq colSlot
      have hxj := hx slot colSlot
      linear_combination ((sq slot)⁻¹ * data.coeff slot colSlot
          * data.tightDir (data.basisLabel colSlot) atomIndex) * hgj
        + ((sq slot)⁻¹
            * data.tightDir (data.basisLabel colSlot) atomIndex) * hxj
    have hmul : (S *ᵥ readVecs atomIndex) slot
        = ∑ colSlot, S slot colSlot * readVecs atomIndex colSlot := rfl
    rw [hmul, Finset.sum_congr rfl fun colSlot _ => hterm colSlot,
      ← Finset.mul_sum, hcarried slot atomIndex hmemSubset]
    have hsimp : (sq slot)⁻¹ * gramDiag slot = sq slot := by
      rw [← hsqsq slot, ← mul_assoc, inv_mul_cancel₀ (hsq slot).ne', one_mul]
    show ((sq slot)⁻¹ * gramDiag slot)
        * (shifted atomIndex * data.tightDir (data.basisLabel slot) atomIndex)
      = shifted atomIndex
        * (sq slot * data.tightDir (data.basisLabel slot) atomIndex)
    rw [hsimp]
    ring
  -- the incidence count
  have hinc : ∀ slot : Fin data.basisCount,
      (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex).card = 3 := by
    intro slot
    have hpred : (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex)
        = datumTightSupport data.tightDir (data.basisLabel slot) := by
      have hcongr : (Finset.univ.filter fun atomIndex =>
          slot ∈ car atomIndex)
          = Finset.univ.filter fun atomIndex =>
              atomIndex ∈ datumTightSupport data.tightDir
                (data.basisLabel slot) :=
        Finset.filter_congr fun atomIndex _ => by
          rw [hcarmem]
      rw [hcongr, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hpred]
    exact data.hthree slot
  -- the interior windows
  have hd0 : ∀ atomIndex, 0 < shifted atomIndex := hint
  have hd1 : ∀ atomIndex, shifted atomIndex < 1 := by
    intro atomIndex
    have hwle : atomWeight atomIndex ≤ 1 := by
      have hsum := data.hdata.weight_sum_one
      have hle : atomWeight atomIndex ≤ ∑ y, atomWeight y :=
        Finset.single_le_sum (f := atomWeight)
          (fun y _ => (data.hdata.weight_pos y).le) (Finset.mem_univ atomIndex)
      rwa [hsum] at hle
    have : shifted atomIndex = chartValue + atomWeight atomIndex := rfl
    rw [this]
    linarith
  have hsum : ∑ atomIndex, shifted atomIndex = 6 * chartValue + 1 := by
    have hexpand : ∑ atomIndex : Fin 6, shifted atomIndex
        = ∑ atomIndex : Fin 6, (chartValue + atomWeight atomIndex) := rfl
    rw [hexpand, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, data.hdata.weight_sum_one, nsmul_eq_mul]
    norm_num
  -- the first pin
  have hmult := data.hmultOne
  simp only [basisSupportMultiplicity] at hmult
  have hpinOne : ∃ pinSlot, car data.pinAtom = {pinSlot} :=
    Finset.card_eq_one.mp hmult
  obtain ⟨pinSlotOne, hpinSlotOne⟩ := hpinOne
  -- dispatch on the trace
  rcases data.htrace with htrace2 | htrace3
  · have hStrace2 : Matrix.trace S = 2 := by rw [hStrace, htrace2]
    exact false_of_interior_budget_trace_two hSsymm hSidem hStrace2 car
      readVecs shifted hinc hsupp hnz hread hd0 hd1 hsum hneg hpinSlotOne
  · obtain ⟨atomTwo, hneq, hmultTwo⟩ := hsecond htrace3
    simp only [basisSupportMultiplicity] at hmultTwo
    obtain ⟨pinSlotTwo, hpinSlotTwo⟩ := Finset.card_eq_one.mp hmultTwo
    have hStrace3 : Matrix.trace S = 3 := by rw [hStrace, htrace3]
    exact false_of_interior_budget_trace_three hSsymm hSidem hStrace3 car
      readVecs shifted hinc hsupp hnz hread hd0 hd1 hsum hneg hneq.symm
      hpinSlotOne hpinSlotTwo

end Gtz
