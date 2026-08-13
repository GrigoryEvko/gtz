import Gtz.Wave.SharedPrivateLeakEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The dual read — the commutant of a fixed vector, the interior triple and
the shared carrier kill

The read weight matrix `W = ∑ over the atoms of z z ᵀ` commutes with the
read idempotent `S`.  This module reads that commutation against a FIXED
vector instead of against a slot pair, and the reading is much stronger
than the entrywise one.

Write `readCombination z ξ` for `∑ over the atoms of (z ⬝ ξ) • z`, which
is `W *ᵥ ξ`.  When `S *ᵥ ξ = ξ`, the commutation makes that combination
FIXED as well:

  **`S *ᵥ (∑ (z ⬝ ξ) • z) = ∑ (z ⬝ ξ) • z`.**

The law has three consequences, and each one is a kill.

* **THE SOLITARY DUAL READ.**  If one atom alone pairs with `ξ`, its own
  read is fixed.  The read law then prices the shifted weight at one, and
  the shifted weight of a chart datum is always less than one.
* **THE EMPTY DUAL READ.**  If no atom pairs with `ξ`, the span law kills
  `ξ`.
* **THE INTERIOR TRIPLE.**  The dual vector of an interior atom is a
  nonzero fixed vector that the atom itself does not see.  Thus TWO more
  atoms see it, and both are interior.  **A shared-private datum of trace
  two carries at least three interior atoms.**

The module also lands the double-carrier trace identity.  Two carried
reads on ONE carrier `C` give the compression `S (1 - P C) S` two
eigenvalues `1 - d` on the image, thus

  **`∑ over `C` of S l l = d₁ + d₂`.**

The escape of that identity is a parallel pair of fixed parts, and the
dual vector of the first atom refutes it.  The co-carrier floor of a
third interior atom then prices the rest of the trace, and the total
shifted weight of three atoms is less than one.  **Thus two interior
atoms never carry the same slots.**

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.readCombination` with `Gtz.readCombination_apply`,
  `Gtz.readCombination_smul_left`, `Gtz.readCombination_of_solitary`,
  `Gtz.readCombination_of_empty` — the read combination calculus.
* `Gtz.readCombination_fixed` — **THE COMMUTANT LAW.**
* `Gtz.fixed_read_of_solitary_dual`,
  `Gtz.false_of_solitary_dual_read` — **THE SOLITARY DUAL READ KILL.**
* `Gtz.exists_dual_pair_of_fixed` — **THE DUAL PAIR**: a nonzero fixed
  vector is seen by at least two atoms.
* `Gtz.orthonormal_pair_entry`, `Gtz.orthonormal_pair_fixed`,
  `Gtz.orthonormal_pair_mulVec` — the plane of a trace-two idempotent.
* `Gtz.exists_dual_vector_of_trace_two` — **THE DUAL VECTOR** of a fixed
  part.
* `Gtz.trace_eq_of_eigen_pair` — the trace of a symmetric plane operator
  with two independent eigenvectors.
* `Gtz.coCarrier_diag_eq_of_shared_carrier`,
  `Gtz.carrier_diag_eq_of_shared_carrier` — **THE DOUBLE-CARRIER TRACE
  IDENTITY.**
* `Gtz.SharedPrivateData.exists_full_read_frame` — the read frame with
  the span law, the commutation and the dead columns together.
* `Gtz.SharedPrivateData.three_le_interior_card` — **THE INTERIOR
  TRIPLE.**
* `Gtz.SharedPrivateData.false_of_shared_carrier_pair` — **THE SHARED
  CARRIER KILL.**
* `Gtz.SharedPrivateBoundaryFiveCarrierClosed` with
  `Gtz.sharedPrivateBoundaryFiveLeakClosed_of_carrier` — the narrowed
  residue.
* `Gtz.sharedPrivateBoundaryFiveConfinedClosed_of_carrier`,
  `Gtz.sharedPrivateBoundaryClosed_of_carrier`,
  `Gtz.sharedPrivateKilled_of_carrier_strata`,
  `Gtz.rankFourSharedPrivateClosed_of_carrier_strata`,
  `Gtz.rankFiveSharedPrivateClosed_of_carrier_strata`,
  `Gtz.rankSixSharedPrivateClosed_of_carrier_strata` — the dispatches.

## Vacuity

The matrix statements are unconditional.  The datum statements quantify
over shared-private data, and no datum exists if `Gtz.GtzWeighted 6 3`
holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the read combination of a probe -/

/-- The combination of the reads that the read weight matrix makes from a
probe.  This is `(∑ over the atoms of z zᵀ) *ᵥ probe`, written without the
matrix. -/
def readCombination {atomCount slotCount : ℕ}
    (readVecs : Fin atomCount → Fin slotCount → ℝ)
    (probe : Fin slotCount → ℝ) : Fin slotCount → ℝ :=
  fun rowSlot => ∑ atomIndex, (readVecs atomIndex ⬝ᵥ probe) * readVecs atomIndex rowSlot

/-- The read combination, unfolded once. -/
theorem readCombination_apply {atomCount slotCount : ℕ}
    (readVecs : Fin atomCount → Fin slotCount → ℝ) (probe : Fin slotCount → ℝ)
    (rowSlot : Fin slotCount) :
    readCombination readVecs probe rowSlot
      = ∑ atomIndex, (readVecs atomIndex ⬝ᵥ probe) * readVecs atomIndex rowSlot := rfl

/-- A read combination with one pairing only is a multiple of that read. -/
theorem readCombination_of_solitary {atomCount slotCount : ℕ}
    (readVecs : Fin atomCount → Fin slotCount → ℝ) (probe : Fin slotCount → ℝ)
    {special : Fin atomCount}
    (hother : ∀ atomIndex : Fin atomCount, atomIndex ≠ special →
      readVecs atomIndex ⬝ᵥ probe = 0) :
    readCombination readVecs probe
      = fun rowSlot => (readVecs special ⬝ᵥ probe) * readVecs special rowSlot := by
  classical
  funext rowSlot
  rw [readCombination_apply]
  refine Finset.sum_eq_single special ?_ ?_
  · intro atomIndex _ hne
    rw [hother atomIndex hne, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_univ special) hnot

/-- A read combination with no pairing vanishes. -/
theorem readCombination_of_empty {atomCount slotCount : ℕ}
    (readVecs : Fin atomCount → Fin slotCount → ℝ) (probe : Fin slotCount → ℝ)
    (hnone : ∀ atomIndex : Fin atomCount, readVecs atomIndex ⬝ᵥ probe = 0) :
    readCombination readVecs probe = 0 := by
  funext rowSlot
  rw [readCombination_apply]
  refine Finset.sum_eq_zero fun atomIndex _ => ?_
  rw [hnone atomIndex, zero_mul]

/-- A matrix carries a scalar through a product with a vector. -/
theorem mulVec_smul_left {slotCount : ℕ}
    (mat : Matrix (Fin slotCount) (Fin slotCount) ℝ) (scale : ℝ)
    (probe : Fin slotCount → ℝ) :
    mat *ᵥ (fun rowSlot => scale * probe rowSlot)
      = fun rowSlot => scale * (mat *ᵥ probe) rowSlot := by
  funext rowSlot
  show (∑ colSlot, mat rowSlot colSlot * (scale * probe colSlot))
    = scale * ∑ colSlot, mat rowSlot colSlot * probe colSlot
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun colSlot _ => by ring

/-- The read combination of a scaled read stays a scaled read. -/
theorem readCombination_smul_left {slotCount : ℕ} (scale : ℝ)
    (baseVec : Fin slotCount → ℝ) (rowSlot : Fin slotCount) :
    (fun row => scale * baseVec row) rowSlot = scale * baseVec rowSlot := rfl

/-! ## Layer 2 — the commutant law -/

/-- **THE COMMUTANT LAW.**  When the read weight matrix commutes with the
read idempotent, the read combination of a FIXED probe is fixed as
well. -/
theorem readCombination_fixed {atomCount slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ} (hsymm : Sᵀ = S)
    (readVecs : Fin atomCount → Fin slotCount → ℝ)
    (hcommute : ∀ rowSlot colSlot : Fin slotCount,
      (∑ atomIndex, readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot)
        = ∑ atomIndex, (S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex colSlot)
    {probe : Fin slotCount → ℝ} (hfix : S *ᵥ probe = probe) :
    S *ᵥ readCombination readVecs probe = readCombination readVecs probe := by
  classical
  have hfixdot : ∀ atomIndex : Fin atomCount,
      (S *ᵥ readVecs atomIndex) ⬝ᵥ probe = readVecs atomIndex ⬝ᵥ probe := by
    intro atomIndex
    rw [← dotProduct_mulVec_symm hsymm (readVecs atomIndex) probe, hfix]
  funext rowSlot
  have hleft : (S *ᵥ readCombination readVecs probe) rowSlot
      = ∑ atomIndex, (readVecs atomIndex ⬝ᵥ probe) * (S *ᵥ readVecs atomIndex) rowSlot := by
    show (∑ colSlot, S rowSlot colSlot * readCombination readVecs probe colSlot)
      = ∑ atomIndex, (readVecs atomIndex ⬝ᵥ probe) * (S *ᵥ readVecs atomIndex) rowSlot
    have hexpand : ∀ colSlot : Fin slotCount,
        S rowSlot colSlot * readCombination readVecs probe colSlot
          = ∑ atomIndex, (readVecs atomIndex ⬝ᵥ probe)
              * (S rowSlot colSlot * readVecs atomIndex colSlot) := by
      intro colSlot
      rw [readCombination_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun atomIndex _ => by ring
    rw [Finset.sum_congr rfl fun colSlot _ => hexpand colSlot, Finset.sum_comm]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [← Finset.mul_sum]
    rfl
  rw [hleft, readCombination_apply]
  -- both totals collapse to the same double sum over the probe entries
  have hswapLeft : (∑ atomIndex, (readVecs atomIndex ⬝ᵥ probe)
        * (S *ᵥ readVecs atomIndex) rowSlot)
      = ∑ midSlot, probe midSlot
          * ∑ atomIndex, (S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex midSlot := by
    have hterm : ∀ atomIndex : Fin atomCount,
        (readVecs atomIndex ⬝ᵥ probe) * (S *ᵥ readVecs atomIndex) rowSlot
          = ∑ midSlot, probe midSlot
              * ((S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex midSlot) := by
      intro atomIndex
      rw [dotProduct, Finset.sum_mul]
      exact Finset.sum_congr rfl fun midSlot _ => by ring
    rw [Finset.sum_congr rfl fun atomIndex _ => hterm atomIndex, Finset.sum_comm]
    exact Finset.sum_congr rfl fun midSlot _ => by rw [Finset.mul_sum]
  have hlift : (∑ atomIndex, (readVecs atomIndex ⬝ᵥ probe) * readVecs atomIndex rowSlot)
      = ∑ atomIndex, ((S *ᵥ readVecs atomIndex) ⬝ᵥ probe) * readVecs atomIndex rowSlot :=
    Finset.sum_congr rfl fun atomIndex _ => by rw [hfixdot atomIndex]
  have hswapRight : (∑ atomIndex, ((S *ᵥ readVecs atomIndex) ⬝ᵥ probe)
        * readVecs atomIndex rowSlot)
      = ∑ midSlot, probe midSlot
          * ∑ atomIndex, readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) midSlot := by
    have hterm : ∀ atomIndex : Fin atomCount,
        ((S *ᵥ readVecs atomIndex) ⬝ᵥ probe) * readVecs atomIndex rowSlot
          = ∑ midSlot, probe midSlot
              * (readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) midSlot) := by
      intro atomIndex
      rw [dotProduct, Finset.sum_mul]
      exact Finset.sum_congr rfl fun midSlot _ => by ring
    rw [Finset.sum_congr rfl fun atomIndex _ => hterm atomIndex, Finset.sum_comm]
    exact Finset.sum_congr rfl fun midSlot _ => by rw [Finset.mul_sum]
  rw [hswapLeft, hlift, hswapRight]
  refine Finset.sum_congr rfl fun midSlot _ => ?_
  rw [hcommute rowSlot midSlot]

/-! ## Layer 3 — the solitary dual read -/

/-- **THE SOLITARY DUAL READ.**  When one atom alone pairs with a fixed
probe, the read of that atom is itself fixed. -/
theorem fixed_read_of_solitary_dual {atomCount slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ} (hsymm : Sᵀ = S)
    (readVecs : Fin atomCount → Fin slotCount → ℝ)
    (hcommute : ∀ rowSlot colSlot : Fin slotCount,
      (∑ atomIndex, readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot)
        = ∑ atomIndex, (S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex colSlot)
    {probe : Fin slotCount → ℝ} (hfix : S *ᵥ probe = probe)
    {special : Fin atomCount}
    (hother : ∀ atomIndex : Fin atomCount, atomIndex ≠ special →
      readVecs atomIndex ⬝ᵥ probe = 0)
    (hne : readVecs special ⬝ᵥ probe ≠ 0) :
    S *ᵥ readVecs special = readVecs special := by
  have hcomb := readCombination_fixed hsymm readVecs hcommute hfix
  rw [readCombination_of_solitary readVecs probe hother,
    mulVec_smul_left S (readVecs special ⬝ᵥ probe) (readVecs special)] at hcomb
  funext rowSlot
  have hentry := congrFun hcomb rowSlot
  exact mul_left_cancel₀ hne hentry

/-- **THE SOLITARY DUAL READ KILL.**  A read that is fixed by the read
idempotent prices its own shifted weight at one, and no shifted weight of
a chart datum is one. -/
theorem false_of_solitary_dual_read {atomCount slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ} (hsymm : Sᵀ = S)
    (readVecs : Fin atomCount → Fin slotCount → ℝ)
    (hcommute : ∀ rowSlot colSlot : Fin slotCount,
      (∑ atomIndex, readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot)
        = ∑ atomIndex, (S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex colSlot)
    {probe : Fin slotCount → ℝ} (hfix : S *ᵥ probe = probe)
    {special : Fin atomCount}
    (hother : ∀ atomIndex : Fin atomCount, atomIndex ≠ special →
      readVecs atomIndex ⬝ᵥ probe = 0)
    (hne : readVecs special ⬝ᵥ probe ≠ 0)
    {pinSlot : Fin slotCount} {weight : ℝ}
    (hread : (S *ᵥ readVecs special) pinSlot = weight * readVecs special pinSlot)
    (hpinNe : readVecs special pinSlot ≠ 0) (hlt : weight < 1) : False := by
  have hfixed := fixed_read_of_solitary_dual hsymm readVecs hcommute hfix hother hne
  rw [hfixed] at hread
  have hone : (1 - weight) * readVecs special pinSlot = 0 := by linarith [hread]
  rcases mul_eq_zero.mp hone with hcase | hcase
  · linarith [hcase]
  · exact hpinNe hcase

/-- **THE DUAL PAIR.**  A nonzero fixed probe is seen by at least two
atoms: no atom sees it only if the span law kills the probe, and one atom
alone sees it only if that atom has shifted weight one. -/
theorem exists_dual_pair_of_fixed {atomCount slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ} (hsymm : Sᵀ = S)
    (readVecs : Fin atomCount → Fin slotCount → ℝ)
    (hcommute : ∀ rowSlot colSlot : Fin slotCount,
      (∑ atomIndex, readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot)
        = ∑ atomIndex, (S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex colSlot)
    (hspan : ∀ testVec : Fin slotCount → ℝ,
      (∀ atomIndex : Fin atomCount, readVecs atomIndex ⬝ᵥ testVec = 0) → testVec = 0)
    (weights : Fin atomCount → ℝ) (hlt : ∀ atomIndex, weights atomIndex < 1)
    (hpin : ∀ atomIndex : Fin atomCount, ∃ pinSlot : Fin slotCount,
      (S *ᵥ readVecs atomIndex) pinSlot = weights atomIndex * readVecs atomIndex pinSlot
        ∧ readVecs atomIndex pinSlot ≠ 0)
    {probe : Fin slotCount → ℝ} (hfix : S *ᵥ probe = probe) (hprobeNe : probe ≠ 0) :
    ∃ atomOne atomTwo : Fin atomCount, atomOne ≠ atomTwo
      ∧ readVecs atomOne ⬝ᵥ probe ≠ 0 ∧ readVecs atomTwo ⬝ᵥ probe ≠ 0 := by
  classical
  by_cases hnone : ∀ atomIndex : Fin atomCount, readVecs atomIndex ⬝ᵥ probe = 0
  · exact absurd (hspan probe hnone) hprobeNe
  obtain ⟨atomOne, hatomOne⟩ := not_forall.mp hnone
  by_cases hsecond : ∃ atomTwo : Fin atomCount, atomTwo ≠ atomOne
      ∧ readVecs atomTwo ⬝ᵥ probe ≠ 0
  · obtain ⟨atomTwo, hne, hpair⟩ := hsecond
    exact ⟨atomOne, atomTwo, fun heq => hne heq.symm, hatomOne, hpair⟩
  · exfalso
    have hother : ∀ atomIndex : Fin atomCount, atomIndex ≠ atomOne →
        readVecs atomIndex ⬝ᵥ probe = 0 := by
      intro atomIndex hne
      by_contra hval
      exact hsecond ⟨atomIndex, hne, hval⟩
    obtain ⟨pinSlot, hread, hpinNe⟩ := hpin atomOne
    exact false_of_solitary_dual_read hsymm readVecs hcommute hfix hother hatomOne
      hread hpinNe (hlt atomOne)

/-! ## Layer 4 — the plane of a trace-two idempotent -/

/-- The entries of a trace-two idempotent, read from an orthonormal
pair. -/
theorem orthonormal_pair_entry {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    {firstVec secondVec : Fin slotCount → ℝ}
    (hsplit : S = Matrix.vecMulVec firstVec firstVec
      + Matrix.vecMulVec secondVec secondVec)
    (rowSlot colSlot : Fin slotCount) :
    S rowSlot colSlot
      = firstVec rowSlot * firstVec colSlot + secondVec rowSlot * secondVec colSlot := by
  have hstep := congrFun (congrFun hsplit rowSlot) colSlot
  rwa [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.vecMulVec_apply] at hstep

/-- A trace-two idempotent reads any vector through the two coordinates of
its orthonormal pair. -/
theorem orthonormal_pair_mulVec {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    {firstVec secondVec : Fin slotCount → ℝ}
    (hsplit : S = Matrix.vecMulVec firstVec firstVec
      + Matrix.vecMulVec secondVec secondVec)
    (probe : Fin slotCount → ℝ) (rowSlot : Fin slotCount) :
    (S *ᵥ probe) rowSlot
      = firstVec rowSlot * (firstVec ⬝ᵥ probe)
        + secondVec rowSlot * (secondVec ⬝ᵥ probe) := by
  show (∑ colSlot, S rowSlot colSlot * probe colSlot)
    = firstVec rowSlot * (firstVec ⬝ᵥ probe)
      + secondVec rowSlot * (secondVec ⬝ᵥ probe)
  rw [dotProduct, dotProduct, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun colSlot _ => ?_
  rw [orthonormal_pair_entry hsplit rowSlot colSlot]
  ring

/-- Each member of the orthonormal pair of a trace-two idempotent is
fixed. -/
theorem orthonormal_pair_fixed {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    {firstVec secondVec : Fin slotCount → ℝ}
    (hfirstUnit : firstVec ⬝ᵥ firstVec = 1) (hsecondUnit : secondVec ⬝ᵥ secondVec = 1)
    (hcross : firstVec ⬝ᵥ secondVec = 0)
    (hsplit : S = Matrix.vecMulVec firstVec firstVec
      + Matrix.vecMulVec secondVec secondVec) :
    S *ᵥ firstVec = firstVec ∧ S *ᵥ secondVec = secondVec := by
  have hcrossSymm : secondVec ⬝ᵥ firstVec = 0 := by
    rw [dotProduct_comm]; exact hcross
  constructor
  · funext rowSlot
    rw [orthonormal_pair_mulVec hsplit firstVec rowSlot, hfirstUnit, hcrossSymm]
    ring
  · funext rowSlot
    rw [orthonormal_pair_mulVec hsplit secondVec rowSlot, hsecondUnit, hcross]
    ring

/-- **THE DUAL VECTOR.**  In the plane of a trace-two idempotent every
fixed part has a fixed partner of the same energy that it does not
see. -/
theorem exists_dual_vector_of_trace_two {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (htrace : Matrix.trace S = 2)
    (baseVec : Fin slotCount → ℝ) :
    ∃ dualVec : Fin slotCount → ℝ,
      S *ᵥ dualVec = dualVec ∧ dualVec ⬝ᵥ baseVec = 0
        ∧ dualVec ⬝ᵥ dualVec = (S *ᵥ baseVec) ⬝ᵥ (S *ᵥ baseVec) := by
  classical
  obtain ⟨firstVec, secondVec, hfirstUnit, hsecondUnit, hcross, hsplit⟩ :=
    exists_orthonormal_pair_of_trace_two hsymm hidem htrace
  obtain ⟨hfirstFix, hsecondFix⟩ :=
    orthonormal_pair_fixed hfirstUnit hsecondUnit hcross hsplit
  have hcrossSymm : secondVec ⬝ᵥ firstVec = 0 := by
    rw [dotProduct_comm]; exact hcross
  set firstRead : ℝ := firstVec ⬝ᵥ baseVec with hfirstRead
  set secondRead : ℝ := secondVec ⬝ᵥ baseVec with hsecondRead
  refine ⟨fun rowSlot => secondRead * firstVec rowSlot - firstRead * secondVec rowSlot,
    ?_, ?_, ?_⟩
  · funext rowSlot
    show (∑ colSlot, S rowSlot colSlot
        * (secondRead * firstVec colSlot - firstRead * secondVec colSlot))
      = secondRead * firstVec rowSlot - firstRead * secondVec rowSlot
    have hstep : (∑ colSlot, S rowSlot colSlot
          * (secondRead * firstVec colSlot - firstRead * secondVec colSlot))
        = secondRead * (∑ colSlot, S rowSlot colSlot * firstVec colSlot)
          - firstRead * ∑ colSlot, S rowSlot colSlot * secondVec colSlot := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun colSlot _ => by ring
    rw [hstep]
    have hfirstEntry : (∑ colSlot, S rowSlot colSlot * firstVec colSlot)
        = firstVec rowSlot := congrFun hfirstFix rowSlot
    have hsecondEntry : (∑ colSlot, S rowSlot colSlot * secondVec colSlot)
        = secondVec rowSlot := congrFun hsecondFix rowSlot
    rw [hfirstEntry, hsecondEntry]
  · rw [dotProduct]
    have hstep : (∑ colSlot, (secondRead * firstVec colSlot - firstRead * secondVec colSlot)
          * baseVec colSlot)
        = secondRead * (firstVec ⬝ᵥ baseVec) - firstRead * (secondVec ⬝ᵥ baseVec) := by
      rw [dotProduct, dotProduct, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun colSlot _ => by ring
    rw [hstep, ← hfirstRead, ← hsecondRead]
    ring
  · have hleft : (fun rowSlot => secondRead * firstVec rowSlot - firstRead * secondVec rowSlot)
        ⬝ᵥ (fun rowSlot => secondRead * firstVec rowSlot - firstRead * secondVec rowSlot)
        = secondRead * secondRead * (firstVec ⬝ᵥ firstVec)
          - 2 * (secondRead * firstRead) * (firstVec ⬝ᵥ secondVec)
          + firstRead * firstRead * (secondVec ⬝ᵥ secondVec) := by
      rw [dotProduct, dotProduct, dotProduct, dotProduct, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun colSlot _ => by ring
    have hright : (S *ᵥ baseVec) ⬝ᵥ (S *ᵥ baseVec)
        = firstRead * firstRead * (firstVec ⬝ᵥ firstVec)
          + 2 * (firstRead * secondRead) * (firstVec ⬝ᵥ secondVec)
          + secondRead * secondRead * (secondVec ⬝ᵥ secondVec) := by
      rw [dotProduct, dotProduct, dotProduct, dotProduct, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun colSlot _ => ?_
      rw [orthonormal_pair_mulVec hsplit baseVec colSlot, ← hfirstRead, ← hsecondRead]
      ring
    rw [hleft, hright, hfirstUnit, hsecondUnit, hcross]
    ring

/-! ## Layer 5 — the trace of a plane operator with two eigenvectors -/

/-- **THE PLANE TRACE.**  A symmetric two-by-two operator with two
independent eigenvectors has the sum of the two eigenvalues as its
trace. -/
theorem trace_eq_of_eigen_pair {entryOne entryCross entryTwo firstOne firstTwo
    secondOne secondTwo valueOne valueTwo : ℝ}
    (hfirstRow : entryOne * firstOne + entryCross * firstTwo = valueOne * firstOne)
    (hfirstCol : entryCross * firstOne + entryTwo * firstTwo = valueOne * firstTwo)
    (hsecondRow : entryOne * secondOne + entryCross * secondTwo = valueTwo * secondOne)
    (hsecondCol : entryCross * secondOne + entryTwo * secondTwo = valueTwo * secondTwo)
    (hdet : firstOne * secondTwo - firstTwo * secondOne ≠ 0) :
    entryOne + entryTwo = valueOne + valueTwo := by
  have hkey : (entryOne + entryTwo - valueOne - valueTwo)
      * (firstOne * secondTwo - firstTwo * secondOne) = 0 := by
    linear_combination secondTwo * hfirstRow - firstTwo * hsecondRow
      - secondOne * hfirstCol + firstOne * hsecondCol
  rcases mul_eq_zero.mp hkey with hcase | hcase
  · linarith [hcase]
  · exact absurd hcase hdet

/-! ## Layer 6 — the double-carrier trace identity -/

set_option maxHeartbeats 1600000 in
/-- **THE DOUBLE-CARRIER TRACE IDENTITY.**  Two reads carried on ONE
carrier make the compression of the idempotent to the complement carry
the two eigenvalues `1 - weight`.  A dual vector that the first read does
not see but the second one does prices the two fixed parts as
independent, thus the diagonal mass off the carrier is exactly
`2 - weightOne - weightTwo`. -/
theorem coCarrier_diag_eq_of_shared_carrier {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (htrace : Matrix.trace S = 2)
    {probeOne probeTwo dualVec : Fin slotCount → ℝ}
    {carrier : Finset (Fin slotCount)} {weightOne weightTwo : ℝ}
    (hsuppOne : ∀ slot : Fin slotCount, slot ∉ carrier → probeOne slot = 0)
    (hreadOne : ∀ slot ∈ carrier, (S *ᵥ probeOne) slot = weightOne * probeOne slot)
    (hsuppTwo : ∀ slot : Fin slotCount, slot ∉ carrier → probeTwo slot = 0)
    (hreadTwo : ∀ slot ∈ carrier, (S *ᵥ probeTwo) slot = weightTwo * probeTwo slot)
    (hdualFix : S *ᵥ dualVec = dualVec) (hdualOne : dualVec ⬝ᵥ probeOne = 0)
    (hdualTwo : dualVec ⬝ᵥ probeTwo ≠ 0) (honeNe : S *ᵥ probeOne ≠ 0) :
    (∑ slot ∈ Finset.univ \ carrier, S slot slot) = 2 - weightOne - weightTwo := by
  classical
  obtain ⟨firstVec, secondVec, hfirstUnit, hsecondUnit, hcross, hsplit⟩ :=
    exists_orthonormal_pair_of_trace_two hsymm hidem htrace
  obtain ⟨hfirstFix, hsecondFix⟩ :=
    orthonormal_pair_fixed hfirstUnit hsecondUnit hcross hsplit
  -- the compression entries off the carrier
  set entryOne : ℝ := ∑ slot ∈ Finset.univ \ carrier, firstVec slot * firstVec slot
    with hentryOne
  set entryCross : ℝ := ∑ slot ∈ Finset.univ \ carrier, firstVec slot * secondVec slot
    with hentryCross
  set entryTwo : ℝ := ∑ slot ∈ Finset.univ \ carrier, secondVec slot * secondVec slot
    with hentryTwo
  -- the eigen equations of a carried read
  have heigen : ∀ (probe : Fin slotCount → ℝ) (weight : ℝ),
      (∀ slot : Fin slotCount, slot ∉ carrier → probe slot = 0) →
      (∀ slot ∈ carrier, (S *ᵥ probe) slot = weight * probe slot) →
      entryOne * (firstVec ⬝ᵥ probe) + entryCross * (secondVec ⬝ᵥ probe)
          = (1 - weight) * (firstVec ⬝ᵥ probe)
        ∧ entryCross * (firstVec ⬝ᵥ probe) + entryTwo * (secondVec ⬝ᵥ probe)
          = (1 - weight) * (secondVec ⬝ᵥ probe) := by
    intro probe weight hsupp hread
    have hpair : ∀ pickVec : Fin slotCount → ℝ,
        S *ᵥ pickVec = pickVec →
        (∑ slot ∈ Finset.univ \ carrier, pickVec slot * (S *ᵥ probe) slot)
          = (1 - weight) * (pickVec ⬝ᵥ probe) := by
      intro pickVec hpickFix
      have htotal : (∑ slot : Fin slotCount, pickVec slot * (S *ᵥ probe) slot)
          = pickVec ⬝ᵥ probe := by
        rw [← dotProduct]
        rw [dotProduct_mulVec_symm hsymm pickVec probe, hpickFix]
      have hcarrier : (∑ slot ∈ carrier, pickVec slot * (S *ᵥ probe) slot)
          = weight * (pickVec ⬝ᵥ probe) := by
        have hstep : (∑ slot ∈ carrier, pickVec slot * (S *ᵥ probe) slot)
            = weight * ∑ slot ∈ carrier, pickVec slot * probe slot := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun slot hslot => ?_
          rw [hread slot hslot]
          ring
        have hself : (∑ slot ∈ carrier, pickVec slot * probe slot) = pickVec ⬝ᵥ probe := by
          rw [dotProduct]
          refine Finset.sum_subset (Finset.subset_univ carrier) ?_
          intro slot _ hnot
          rw [hsupp slot hnot, mul_zero]
        rw [hstep, hself]
      have hsplitSum : (∑ slot ∈ Finset.univ \ carrier, pickVec slot * (S *ᵥ probe) slot)
          + ∑ slot ∈ carrier, pickVec slot * (S *ᵥ probe) slot
          = ∑ slot : Fin slotCount, pickVec slot * (S *ᵥ probe) slot :=
        Finset.sum_sdiff (Finset.subset_univ carrier)
      rw [hcarrier, htotal] at hsplitSum
      linarith [hsplitSum]
    have hexpand : ∀ pickVec : Fin slotCount → ℝ,
        (∑ slot ∈ Finset.univ \ carrier, pickVec slot * (S *ᵥ probe) slot)
          = (∑ slot ∈ Finset.univ \ carrier, pickVec slot * firstVec slot)
              * (firstVec ⬝ᵥ probe)
            + (∑ slot ∈ Finset.univ \ carrier, pickVec slot * secondVec slot)
              * (secondVec ⬝ᵥ probe) := by
      intro pickVec
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun slot _ => ?_
      rw [orthonormal_pair_mulVec hsplit probe slot]
      ring
    have hfirstEq := hpair firstVec hfirstFix
    have hsecondEq := hpair secondVec hsecondFix
    rw [hexpand firstVec] at hfirstEq
    rw [hexpand secondVec] at hsecondEq
    have hcrossSwap : (∑ slot ∈ Finset.univ \ carrier, secondVec slot * firstVec slot)
        = entryCross := by
      rw [hentryCross]
      exact Finset.sum_congr rfl fun slot _ => by ring
    rw [← hentryOne, ← hentryCross] at hfirstEq
    rw [hcrossSwap, ← hentryTwo] at hsecondEq
    exact ⟨hfirstEq, hsecondEq⟩
  obtain ⟨hrowOne, hcolOne⟩ := heigen probeOne weightOne hsuppOne hreadOne
  obtain ⟨hrowTwo, hcolTwo⟩ := heigen probeTwo weightTwo hsuppTwo hreadTwo
  -- the dual vector prices the two fixed parts as independent
  have hdualCoord : ∀ probe : Fin slotCount → ℝ,
      dualVec ⬝ᵥ probe
        = (firstVec ⬝ᵥ dualVec) * (firstVec ⬝ᵥ probe)
          + (secondVec ⬝ᵥ dualVec) * (secondVec ⬝ᵥ probe) := by
    intro probe
    have hstep : dualVec ⬝ᵥ probe = ∑ slot, (S *ᵥ dualVec) slot * probe slot := by
      rw [hdualFix]
      rfl
    have hterm : ∀ slot : Fin slotCount, (S *ᵥ dualVec) slot * probe slot
        = (firstVec ⬝ᵥ dualVec) * (firstVec slot * probe slot)
          + (secondVec ⬝ᵥ dualVec) * (secondVec slot * probe slot) := by
      intro slot
      rw [orthonormal_pair_mulVec hsplit dualVec slot]
      ring
    rw [hstep, Finset.sum_congr rfl fun slot _ => hterm slot, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  have hdualOneCoord : (firstVec ⬝ᵥ dualVec) * (firstVec ⬝ᵥ probeOne)
      + (secondVec ⬝ᵥ dualVec) * (secondVec ⬝ᵥ probeOne) = 0 := by
    rw [← hdualCoord probeOne]; exact hdualOne
  have hdualTwoCoord : (firstVec ⬝ᵥ dualVec) * (firstVec ⬝ᵥ probeTwo)
      + (secondVec ⬝ᵥ dualVec) * (secondVec ⬝ᵥ probeTwo) ≠ 0 := by
    rw [← hdualCoord probeTwo]; exact hdualTwo
  have hdet : (firstVec ⬝ᵥ probeOne) * (secondVec ⬝ᵥ probeTwo)
      - (secondVec ⬝ᵥ probeOne) * (firstVec ⬝ᵥ probeTwo) ≠ 0 := by
    intro hzero
    have hfirstZero : firstVec ⬝ᵥ probeOne = 0 := by
      have hstep : (firstVec ⬝ᵥ probeOne)
          * ((firstVec ⬝ᵥ dualVec) * (firstVec ⬝ᵥ probeTwo)
            + (secondVec ⬝ᵥ dualVec) * (secondVec ⬝ᵥ probeTwo)) = 0 := by
        linear_combination (firstVec ⬝ᵥ probeTwo) * hdualOneCoord
          + (secondVec ⬝ᵥ dualVec) * hzero
      rcases mul_eq_zero.mp hstep with hcase | hcase
      · exact hcase
      · exact absurd hcase hdualTwoCoord
    have hsecondZero : secondVec ⬝ᵥ probeOne = 0 := by
      have hstep : (secondVec ⬝ᵥ probeOne)
          * ((firstVec ⬝ᵥ dualVec) * (firstVec ⬝ᵥ probeTwo)
            + (secondVec ⬝ᵥ dualVec) * (secondVec ⬝ᵥ probeTwo)) = 0 := by
        linear_combination (secondVec ⬝ᵥ probeTwo) * hdualOneCoord
          - (firstVec ⬝ᵥ dualVec) * hzero
      rcases mul_eq_zero.mp hstep with hcase | hcase
      · exact hcase
      · exact absurd hcase hdualTwoCoord
    refine honeNe (funext fun slot => ?_)
    rw [orthonormal_pair_mulVec hsplit probeOne slot, hfirstZero, hsecondZero]
    simp
  have hplane := trace_eq_of_eigen_pair hrowOne hcolOne hrowTwo hcolTwo hdet
  have hdiagSum : (∑ slot ∈ Finset.univ \ carrier, S slot slot) = entryOne + entryTwo := by
    rw [hentryOne, hentryTwo, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun slot _ => orthonormal_pair_entry hsplit slot slot
  rw [hdiagSum, hplane]
  ring

/-- **THE CARRIER FORM.**  The diagonal mass ON a shared carrier is the
total of the two shifted weights. -/
theorem carrier_diag_eq_of_shared_carrier {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (htrace : Matrix.trace S = 2)
    {probeOne probeTwo dualVec : Fin slotCount → ℝ}
    {carrier : Finset (Fin slotCount)} {weightOne weightTwo : ℝ}
    (hsuppOne : ∀ slot : Fin slotCount, slot ∉ carrier → probeOne slot = 0)
    (hreadOne : ∀ slot ∈ carrier, (S *ᵥ probeOne) slot = weightOne * probeOne slot)
    (hsuppTwo : ∀ slot : Fin slotCount, slot ∉ carrier → probeTwo slot = 0)
    (hreadTwo : ∀ slot ∈ carrier, (S *ᵥ probeTwo) slot = weightTwo * probeTwo slot)
    (hdualFix : S *ᵥ dualVec = dualVec) (hdualOne : dualVec ⬝ᵥ probeOne = 0)
    (hdualTwo : dualVec ⬝ᵥ probeTwo ≠ 0) (honeNe : S *ᵥ probeOne ≠ 0) :
    (∑ slot ∈ carrier, S slot slot) = weightOne + weightTwo := by
  classical
  have hoff := coCarrier_diag_eq_of_shared_carrier hsymm hidem htrace hsuppOne hreadOne
    hsuppTwo hreadTwo hdualFix hdualOne hdualTwo honeNe
  have hsplitSum : (∑ slot ∈ Finset.univ \ carrier, S slot slot)
      + ∑ slot ∈ carrier, S slot slot
      = ∑ slot : Fin slotCount, S slot slot :=
    Finset.sum_sdiff (Finset.subset_univ carrier)
  have htraceSum : (∑ slot : Fin slotCount, S slot slot) = 2 := by
    have hstep : Matrix.trace S = ∑ slot : Fin slotCount, S slot slot := rfl
    rw [← hstep, htrace]
  rw [hoff, htraceSum] at hsplitSum
  linarith [hsplitSum]

/-! ## Layer 7 — the full read frame of a datum -/

set_option maxHeartbeats 3200000 in
/-- **THE FULL READ FRAME.**  The kernel read frame, the span law, the
commutation and the dead columns, together in one statement. -/
theorem SharedPrivateData.exists_full_read_frame {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) :
    ∃ (S : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ)
      (readVecs : Fin 6 → Fin data.basisCount → ℝ),
      Sᵀ = S ∧ S * S = S
      ∧ Matrix.trace S = Matrix.trace data.coeff
      ∧ (∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
          atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot) →
          readVecs atomIndex slot = 0)
      ∧ (∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
          atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
          (S *ᵥ readVecs atomIndex) slot
            = (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomIndex)
              * readVecs atomIndex slot)
      ∧ (∀ atomIndex : Fin 6, readVecs atomIndex ⬝ᵥ readVecs atomIndex = (6 : ℝ)⁻¹)
      ∧ (∀ atomIndex : Fin 6,
          chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex = 0 →
          S *ᵥ readVecs atomIndex = 0)
      ∧ (∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
          atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
          readVecs atomIndex slot ≠ 0)
      ∧ (∀ atomIndex : Fin 6, readVecs atomIndex ≠ 0)
      ∧ (∀ testVec : Fin data.basisCount → ℝ,
          (∀ atomIndex : Fin 6, readVecs atomIndex ⬝ᵥ testVec = 0) → testVec = 0)
      ∧ (∀ rowSlot colSlot : Fin data.basisCount,
          (∑ atomIndex : Fin 6,
              readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot)
            = ∑ atomIndex : Fin 6,
              (S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex colSlot)
      ∧ (∀ deadSlot : Fin data.basisCount,
          (∀ probe : Fin 6,
            0 < chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight probe →
            probe ∉ datumTightSupport data.tightDir (data.basisLabel deadSlot)) →
          ∀ rowSlot : Fin data.basisCount, S rowSlot deadSlot = 0) := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsuppFrame, hreadFrame, hnorm,
    hnz, hboundary, hcarrierNz, hspan, hcommute⟩ :=
    data.exists_kernel_read_frame hdiag
  have hmemActive : ∀ slot, data.basisLabel slot ∈ data.activeSet := by
    intro slot
    have hmem := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  have hread : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      (S *ᵥ readVecs atomIndex) slot
        = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * readVecs atomIndex slot :=
    fun atomIndex slot hmem => hreadFrame atomIndex slot
      (datumTightSupport_subset data.hdata (hmemActive slot) hmem)
  refine ⟨S, readVecs, hSsymm, hSidem, hStrace, hsuppFrame, hread, hnorm, hboundary,
    hcarrierNz, hnz, hspan, hcommute, ?_⟩
  intro deadSlot hnone rowSlot
  have hzeroCol : S *ᵥ (fun slot => if slot = deadSlot then (1 : ℝ) else 0) = 0 := by
    refine dead_slot_column_of_frame hSsymm hSidem readVecs hcommute hspan
      deadSlot fun probe => ?_
    by_cases hmem : probe ∈ datumTightSupport data.tightDir (data.basisLabel deadSlot)
    · have hnn := capture_diagonal_nonneg_of_isChartStationaryData data.hdata probe
      have hzero : chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight probe = 0 := by
        rcases lt_or_eq_of_le hnn with hpos | heq
        · exact absurd hmem (hnone probe hpos)
        · exact heq.symm
      rw [hread probe deadSlot hmem, hzero, zero_mul, zero_mul]
    · rw [hsuppFrame probe deadSlot hmem, mul_zero]
  have hentry := congrFun hzeroCol rowSlot
  have hexpand : (S *ᵥ fun slot => if slot = deadSlot then (1 : ℝ) else 0) rowSlot
      = S rowSlot deadSlot := by
    calc (S *ᵥ fun slot => if slot = deadSlot then (1 : ℝ) else 0) rowSlot
        = ∑ slot, S rowSlot slot * (if slot = deadSlot then (1 : ℝ) else 0) := rfl
      _ = S rowSlot deadSlot := by
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, if_true]
  rw [hexpand] at hentry
  simpa using hentry

/-! ## Layer 8 — the interior triple -/

set_option maxHeartbeats 3200000 in
/-- **THE INTERIOR TRIPLE.**  A trace-two shared-private datum carries at
least three interior atoms.  The dual vector of one interior atom is a
nonzero fixed vector that the atom does not see, thus two more atoms see
it, and no boundary atom sees a fixed vector. -/
theorem SharedPrivateData.three_le_interior_card {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2) :
    3 ≤ (Finset.univ.filter fun atomIndex : Fin 6 =>
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex).card := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsuppFrame, hread, hnorm,
    hboundary, hcarrierNz, hnz, hspan, hcommute, _hdeadCol⟩ :=
    data.exists_full_read_frame hdiag
  set shifted : Fin 6 → ℝ := fun atomIndex =>
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex with hshifted
  have hStraceTwo : Matrix.trace S = 2 := by rw [hStrace, htrace]
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
  -- every atom has a carried slot, thus a pinned read law
  have hpin : ∀ atomIndex : Fin 6, ∃ pinSlot : Fin data.basisCount,
      (S *ᵥ readVecs atomIndex) pinSlot = shifted atomIndex * readVecs atomIndex pinSlot
        ∧ readVecs atomIndex pinSlot ≠ 0 := by
    intro atomIndex
    have hne := hnz atomIndex
    obtain ⟨pinSlot, hpinNe⟩ : ∃ pinSlot : Fin data.basisCount,
        readVecs atomIndex pinSlot ≠ 0 := by
      by_contra hnone
      simp only [not_exists, not_not] at hnone
      exact hne (funext hnone)
    have hmem : atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel pinSlot) := by
      by_contra hnot
      exact hpinNe (hsuppFrame atomIndex pinSlot hnot)
    exact ⟨pinSlot, hread atomIndex pinSlot hmem, hpinNe⟩
  -- an interior atom exists
  have htwo := data.two_le_interior_card hdiag
  have hnonempty : ∃ baseAtom : Fin 6, 0 < shifted baseAtom := by
    by_contra hnone
    simp only [not_exists, not_lt] at hnone
    have hempty : (Finset.univ.filter fun atomIndex : Fin 6 =>
        0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun atomIndex _ => not_lt.mpr (hnone atomIndex)
    rw [hempty, Finset.card_empty] at htwo
    omega
  obtain ⟨baseAtom, hbasePos⟩ := hnonempty
  -- the fixed part of the base read is nonzero
  have hbaseEnergy : (S *ᵥ readVecs baseAtom) ⬝ᵥ (S *ᵥ readVecs baseAtom)
      = shifted baseAtom * (6 : ℝ)⁻¹ := by
    have hsupp : ∀ slot ∉ (Finset.univ.filter fun slot : Fin data.basisCount =>
        baseAtom ∈ datumTightSupport data.tightDir (data.basisLabel slot)),
        readVecs baseAtom slot = 0 := by
      intro slot hslot
      exact hsuppFrame baseAtom slot fun hmem =>
        hslot (Finset.mem_filter.mpr ⟨Finset.mem_univ slot, hmem⟩)
    have hreadCar : ∀ slot ∈ (Finset.univ.filter fun slot : Fin data.basisCount =>
        baseAtom ∈ datumTightSupport data.tightDir (data.basisLabel slot)),
        (S *ᵥ readVecs baseAtom) slot = shifted baseAtom * readVecs baseAtom slot :=
      fun slot hslot => hread baseAtom slot (Finset.mem_filter.mp hslot).2
    rw [read_fixed_self_energy hSsymm hSidem hsupp hreadCar, hnorm baseAtom]
  have hbaseNe : S *ᵥ readVecs baseAtom ≠ 0 := by
    intro hzero
    rw [hzero] at hbaseEnergy
    have hzeroDot : (0 : Fin data.basisCount → ℝ) ⬝ᵥ (0 : Fin data.basisCount → ℝ) = 0 :=
      zero_dotProduct _
    rw [hzeroDot] at hbaseEnergy
    nlinarith [hbasePos, hbaseEnergy]
  -- the dual vector of the base read
  obtain ⟨dualVec, hdualFix, hdualBase, hdualEnergy⟩ :=
    exists_dual_vector_of_trace_two hSsymm hSidem hStraceTwo (readVecs baseAtom)
  have hdualNe : dualVec ≠ 0 := by
    intro hzero
    rw [hzero, hbaseEnergy] at hdualEnergy
    have hzeroDot : (0 : Fin data.basisCount → ℝ) ⬝ᵥ (0 : Fin data.basisCount → ℝ) = 0 :=
      zero_dotProduct _
    rw [hzeroDot] at hdualEnergy
    nlinarith [hbasePos, hdualEnergy]
  obtain ⟨atomOne, atomTwo, hne, hpairOne, hpairTwo⟩ :=
    exists_dual_pair_of_fixed hSsymm readVecs hcommute hspan shifted hltOne hpin
      hdualFix hdualNe
  -- the base atom does not see its dual, and no boundary atom sees a fixed vector
  have hbaseBlind : readVecs baseAtom ⬝ᵥ dualVec = 0 := by
    rw [dotProduct_comm]; exact hdualBase
  have hseer : ∀ atomIndex : Fin 6, readVecs atomIndex ⬝ᵥ dualVec ≠ 0 →
      atomIndex ≠ baseAtom ∧ 0 < shifted atomIndex := by
    intro atomIndex hsee
    refine ⟨fun heq => hsee (heq ▸ hbaseBlind), ?_⟩
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
  obtain ⟨hneOne, hposOne⟩ := hseer atomOne hpairOne
  obtain ⟨hneTwo, hposTwo⟩ := hseer atomTwo hpairTwo
  -- the three atoms are distinct and interior
  have hsub : ({baseAtom, atomOne, atomTwo} : Finset (Fin 6))
      ⊆ Finset.univ.filter fun atomIndex : Fin 6 =>
        0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex := by
    intro atomIndex hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ atomIndex, ?_⟩
    rcases hmem with heq | heq | heq
    · rw [heq]; exact hbasePos
    · rw [heq]; exact hposOne
    · rw [heq]; exact hposTwo
  have hcard : ({baseAtom, atomOne, atomTwo} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hneOne, Ne.symm hneTwo]),
      Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  exact hle

/-! ## Layer 9 — the shared carrier kill -/

set_option maxHeartbeats 3200000 in
/-- **THE SHARED CARRIER KILL.**  Two interior atoms that carry exactly
the same slots ask for a total shifted weight of at least one.  The dual
vector of the first atom refutes the parallel escape of the double-carrier
trace identity, thus the diagonal mass on the shared carrier is the total
of the two shifted weights.  The co-carrier floor of the third interior
atom prices the rest of the trace, and the negative chart value refuses
the total. -/
theorem SharedPrivateData.false_of_shared_carrier_pair {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2)
    {atomOne atomTwo atomThree : Fin 6}
    (hne12 : atomOne ≠ atomTwo) (hne13 : atomOne ≠ atomThree)
    (hne23 : atomTwo ≠ atomThree)
    (hposOne : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne)
    (_hposTwo : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomTwo)
    (hposThree : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomThree)
    (hinterior : ∀ probe : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe →
      probe = atomOne ∨ probe = atomTwo ∨ probe = atomThree)
    (hcarrierEq : ∀ slot : Fin data.basisCount,
      atomOne ∈ datumTightSupport data.tightDir (data.basisLabel slot) ↔
        atomTwo ∈ datumTightSupport data.tightDir (data.basisLabel slot)) : False := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsuppFrame, hread, hnorm,
    hboundary, hcarrierNz, hnz, hspan, hcommute, hdeadCol⟩ :=
    data.exists_full_read_frame hdiag
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
  have hStraceTwo : Matrix.trace S = 2 := by rw [hStrace, htrace]
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
  have hdiagNonneg : ∀ slot : Fin data.basisCount, 0 ≤ S slot slot := by
    intro slot
    rw [← idem_column_energy hSsymm hSidem slot]
    exact selfDot_nonneg _
  -- the fixed part of the first read is nonzero
  have hsuppCar : ∀ atomIndex : Fin 6, ∀ slot ∉ carrierOf atomIndex,
      readVecs atomIndex slot = 0 := by
    intro atomIndex slot hslot
    exact hsuppFrame atomIndex slot fun hmem =>
      hslot ((hmemCarrier atomIndex slot).mpr hmem)
  have hreadCar : ∀ atomIndex : Fin 6, ∀ slot ∈ carrierOf atomIndex,
      (S *ᵥ readVecs atomIndex) slot = shifted atomIndex * readVecs atomIndex slot :=
    fun atomIndex slot hslot => hread atomIndex slot ((hmemCarrier atomIndex slot).mp hslot)
  have hfixEnergy : ∀ atomIndex : Fin 6,
      (S *ᵥ readVecs atomIndex) ⬝ᵥ (S *ᵥ readVecs atomIndex)
        = shifted atomIndex * (6 : ℝ)⁻¹ := by
    intro atomIndex
    rw [read_fixed_self_energy hSsymm hSidem (hsuppCar atomIndex) (hreadCar atomIndex),
      hnorm atomIndex]
  have honeNe : S *ᵥ readVecs atomOne ≠ 0 := by
    intro hzero
    have henergy := hfixEnergy atomOne
    rw [hzero, zero_dotProduct] at henergy
    nlinarith [hposOne, henergy]
  -- the dual vector of the first read
  obtain ⟨dualVec, hdualFix, hdualBase, hdualEnergy⟩ :=
    exists_dual_vector_of_trace_two hSsymm hSidem hStraceTwo (readVecs atomOne)
  have hdualNe : dualVec ≠ 0 := by
    intro hzero
    rw [hzero, zero_dotProduct, hfixEnergy atomOne] at hdualEnergy
    nlinarith [hposOne, hdualEnergy]
  obtain ⟨seerOne, seerTwo, hseerNe, hseerPairOne, hseerPairTwo⟩ :=
    exists_dual_pair_of_fixed hSsymm readVecs hcommute hspan shifted hltOne hpin
      hdualFix hdualNe
  have hblindOne : readVecs atomOne ⬝ᵥ dualVec = 0 := by
    rw [dotProduct_comm]; exact hdualBase
  have hseer : ∀ atomIndex : Fin 6, readVecs atomIndex ⬝ᵥ dualVec ≠ 0 →
      atomIndex = atomTwo ∨ atomIndex = atomThree := by
    intro atomIndex hsee
    have hnotOne : atomIndex ≠ atomOne := fun heq => hsee (heq ▸ hblindOne)
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
    · exact absurd heq hnotOne
    · exact Or.inl heq
    · exact Or.inr heq
  -- the two seers are the second and the third atom, thus the second one sees the dual
  have hdualTwo : dualVec ⬝ᵥ readVecs atomTwo ≠ 0 := by
    rw [dotProduct_comm]
    rcases hseer seerOne hseerPairOne with heq | heq
    · rw [← heq]; exact hseerPairOne
    · rcases hseer seerTwo hseerPairTwo with heqTwo | heqTwo
      · rw [← heqTwo]; exact hseerPairTwo
      · exact absurd (heq.trans heqTwo.symm) hseerNe
  have hdualOne : dualVec ⬝ᵥ readVecs atomOne = 0 := hdualBase
  -- the double-carrier trace identity on the shared carrier
  have hcarrierSame : carrierOf atomTwo = carrierOf atomOne := by
    ext slot
    rw [hmemCarrier, hmemCarrier]
    exact (hcarrierEq slot).symm
  have hsuppTwoShared : ∀ slot ∉ carrierOf atomOne, readVecs atomTwo slot = 0 := by
    intro slot hslot
    exact hsuppCar atomTwo slot (by rw [hcarrierSame]; exact hslot)
  have hreadTwoShared : ∀ slot ∈ carrierOf atomOne,
      (S *ᵥ readVecs atomTwo) slot = shifted atomTwo * readVecs atomTwo slot := by
    intro slot hslot
    exact hreadCar atomTwo slot (by rw [hcarrierSame]; exact hslot)
  have hshared := carrier_diag_eq_of_shared_carrier hSsymm hSidem hStraceTwo
    (hsuppCar atomOne) (hreadCar atomOne) hsuppTwoShared hreadTwoShared hdualFix
    hdualOne hdualTwo honeNe
  -- the co-carrier floor of the third atom
  have hfloor := coCarrier_diag_floor hSsymm hSidem (hsuppCar atomThree)
    (hreadCar atomThree) (hnorm atomThree) hposThree (by norm_num : (0 : ℝ) < (6 : ℝ)⁻¹)
  -- every live slot off the third carrier sits on the shared carrier
  have htransport : (∑ slot ∈ Finset.univ \ carrierOf atomThree, S slot slot)
      ≤ ∑ slot ∈ carrierOf atomOne, S slot slot := by
    have hrestrict : (∑ slot ∈ (Finset.univ \ carrierOf atomThree) ∩ carrierOf atomOne,
          S slot slot)
        = ∑ slot ∈ Finset.univ \ carrierOf atomThree, S slot slot := by
      refine Finset.sum_subset (Finset.inter_subset_left) ?_
      intro slot hslot hnot
      have hoffThree : atomThree ∉ datumTightSupport data.tightDir
          (data.basisLabel slot) := by
        intro hmem
        exact (Finset.mem_sdiff.mp hslot).2 ((hmemCarrier atomThree slot).mpr hmem)
      have hoffOne : atomOne ∉ datumTightSupport data.tightDir
          (data.basisLabel slot) := by
        intro hmem
        exact hnot (Finset.mem_inter.mpr ⟨hslot, (hmemCarrier atomOne slot).mpr hmem⟩)
      have hdead : ∀ probe : Fin 6, 0 < shifted probe →
          probe ∉ datumTightSupport data.tightDir (data.basisLabel slot) := by
        intro probe hpos hmem
        rcases hinterior probe hpos with heq | heq | heq
        · exact hoffOne (heq ▸ hmem)
        · exact hoffOne ((hcarrierEq slot).mpr (heq ▸ hmem))
        · exact hoffThree (heq ▸ hmem)
      exact hdeadCol slot hdead slot
    rw [← hrestrict]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right)
      fun slot _ _ => hdiagNonneg slot
  have hbudget := data.shifted_weight_triple_lt_one hne12 hne13 hne23
  rw [hshared] at htransport
  linarith [hfloor, htransport, hbudget]

/-! ## Layer 10 — the narrowed residue and the dispatches -/

/-- **THE CARRIER RESIDUE.**  The leak residue of the basis-count-five
boundary stratum, with the interior triple and the pairwise distinct
interior carriers supplied.  The interior triple discharges the first
supply and the shared carrier kill discharges the second, thus this
residue is strictly weaker than the leak one. -/
def SharedPrivateBoundaryFiveCarrierClosed : Prop :=
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
    3 ≤ (Finset.univ.filter fun atomIndex =>
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
    (∀ atomOne atomTwo : Fin 6, atomOne ≠ atomTwo →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomOne →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomTwo →
      ∃ slot : Fin data.basisCount,
        ¬(atomOne ∈ datumTightSupport data.tightDir (data.basisLabel slot) ↔
          atomTwo ∈ datumTightSupport data.tightDir (data.basisLabel slot))) →
    False

set_option maxHeartbeats 1600000 in
/-- **THE CARRIER DISPATCH.**  The interior triple supplies the third
interior atom and the shared carrier kill supplies the distinct carriers,
thus the carrier residue closes the leak residue. -/
theorem sharedPrivateBoundaryFiveLeakClosed_of_carrier
    (hcarrier : SharedPrivateBoundaryFiveCarrierClosed) :
    SharedPrivateBoundaryFiveLeakClosed := by
  classical
  intro crux data gramDiag hdiag htrace hbasis hpin hmultOne hprivate hinteriorOut
    hthick _hlow hhigh hsingle hcocarrier hoffCarrier hshared
  have hthree := data.three_le_interior_card hdiag htrace
  refine hcarrier crux data gramDiag hdiag htrace hbasis hpin hmultOne hprivate
    hinteriorOut hthick hthree hhigh hsingle hcocarrier hoffCarrier hshared ?_
  intro atomOne atomTwo hne hposOne hposTwo
  by_contra hnone
  have hcarrierEq : ∀ slot : Fin data.basisCount,
      atomOne ∈ datumTightSupport data.tightDir (data.basisLabel slot) ↔
        atomTwo ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
    intro slot
    by_contra hslot
    exact hnone ⟨slot, hslot⟩
  -- the interior set has exactly three atoms, thus a third one exists
  set interiorSet : Finset (Fin 6) :=
    Finset.univ.filter fun atomIndex =>
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex with hinteriorSet
  have hcard : interiorSet.card = 3 := le_antisymm hhigh hthree
  obtain ⟨firstAtom, secondAtom, thirdAtom, hab, hac, hbc, hset⟩ :=
    Finset.card_eq_three.mp hcard
  have hmemOne : atomOne ∈ interiorSet := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hposOne⟩
  have hmemTwo : atomTwo ∈ interiorSet := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hposTwo⟩
  have hinterior : ∀ probe : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe →
      probe = firstAtom ∨ probe = secondAtom ∨ probe = thirdAtom := by
    intro probe hpos
    have hmem : probe ∈ interiorSet := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩
    rw [hset] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  -- name the third interior atom, the one that is neither of the pair
  have hposOf : ∀ probe : Fin 6, probe ∈ interiorSet →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe :=
    fun probe hmem => (Finset.mem_filter.mp hmem).2
  have hexistsThird : ∃ atomThree : Fin 6, atomThree ≠ atomOne ∧ atomThree ≠ atomTwo
      ∧ 0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomThree := by
    have hpair : ({atomOne, atomTwo} : Finset (Fin 6)) ⊆ interiorSet := by
      intro probe hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with heq | heq
      · rw [heq]; exact hmemOne
      · rw [heq]; exact hmemTwo
    have hpairCard : ({atomOne, atomTwo} : Finset (Fin 6)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    have hproper : ({atomOne, atomTwo} : Finset (Fin 6)) ⊂ interiorSet := by
      refine Finset.ssubset_iff_of_subset hpair |>.mpr ?_
      by_contra hnothing
      simp only [not_exists, not_and, not_not] at hnothing
      have hle : interiorSet ⊆ ({atomOne, atomTwo} : Finset (Fin 6)) := fun probe hmem =>
        hnothing probe hmem
      have := Finset.card_le_card hle
      rw [hcard, hpairCard] at this
      omega
    obtain ⟨atomThree, hmemThree, hnotPair⟩ := Finset.exists_of_ssubset hproper
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnotPair
    exact ⟨atomThree, hnotPair.1, hnotPair.2, hposOf atomThree hmemThree⟩
  obtain ⟨atomThree, hne31, hne32, hposThree⟩ := hexistsThird
  have hinteriorTriple : ∀ probe : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe →
      probe = atomOne ∨ probe = atomTwo ∨ probe = atomThree := by
    intro probe hpos
    have hmem : probe ∈ interiorSet := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩
    by_contra hnot
    simp only [not_or] at hnot
    have hsub : ({atomOne, atomTwo, atomThree, probe} : Finset (Fin 6)) ⊆ interiorSet := by
      intro other hother
      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
      rcases hother with heq | heq | heq | heq
      · rw [heq]; exact hmemOne
      · rw [heq]; exact hmemTwo
      · rw [heq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hposThree⟩
      · rw [heq]; exact hmem
    have hcardFour : ({atomOne, atomTwo, atomThree, probe} : Finset (Fin 6)).card = 4 := by
      rw [Finset.card_insert_of_notMem
          (by simp [hne, Ne.symm hne31, Ne.symm hnot.1]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hne32, Ne.symm hnot.2.1]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hnot.2.2]),
        Finset.card_singleton]
    have hle := Finset.card_le_card hsub
    rw [hcardFour, hcard] at hle
    omega
  exact data.false_of_shared_carrier_pair hdiag htrace hne hne31.symm hne32.symm
    hposOne hposTwo hposThree hinteriorTriple hcarrierEq

/-- The carrier residue closes the confined residue. -/
theorem sharedPrivateBoundaryFiveConfinedClosed_of_carrier
    (hcarrier : SharedPrivateBoundaryFiveCarrierClosed) :
    SharedPrivateBoundaryFiveConfinedClosed :=
  sharedPrivateBoundaryFiveConfinedClosed_of_leak
    (sharedPrivateBoundaryFiveLeakClosed_of_carrier hcarrier)

/-- The carrier residue closes the whole trace-two boundary residue. -/
theorem sharedPrivateBoundaryClosed_of_carrier
    (hcarrier : SharedPrivateBoundaryFiveCarrierClosed) :
    SharedPrivateBoundaryClosed :=
  sharedPrivateBoundaryClosed_of_leak
    (sharedPrivateBoundaryFiveLeakClosed_of_carrier hcarrier)

/-- **THE STRATA DISPATCH.**  The extras residue and the carrier residue
close the generic shared-private kill. -/
theorem sharedPrivateKilled_of_carrier_strata
    (hextras : SharedPrivateExtrasClosed)
    (hcarrier : SharedPrivateBoundaryFiveCarrierClosed) : SharedPrivateKilled :=
  sharedPrivateKilled_of_leak_energy_strata hextras
    (sharedPrivateBoundaryFiveLeakClosed_of_carrier hcarrier)

/-- The two residues discharge closure two of the rank-four rung. -/
theorem rankFourSharedPrivateClosed_of_carrier_strata
    (hextras : SharedPrivateExtrasClosed)
    (hcarrier : SharedPrivateBoundaryFiveCarrierClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_leak_energy_strata hextras
    (sharedPrivateBoundaryFiveLeakClosed_of_carrier hcarrier)

/-- The two residues discharge the shared-private closure of the rank-five
rung. -/
theorem rankFiveSharedPrivateClosed_of_carrier_strata
    (hextras : SharedPrivateExtrasClosed)
    (hcarrier : SharedPrivateBoundaryFiveCarrierClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_leak_energy_strata hextras
    (sharedPrivateBoundaryFiveLeakClosed_of_carrier hcarrier)

/-- The two residues discharge the shared-private closure of the rank-six
rung. -/
theorem rankSixSharedPrivateClosed_of_carrier_strata
    (hextras : SharedPrivateExtrasClosed)
    (hcarrier : SharedPrivateBoundaryFiveCarrierClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_leak_energy_strata hextras
    (sharedPrivateBoundaryFiveLeakClosed_of_carrier hcarrier)

end Gtz
