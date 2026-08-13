import Gtz.Wave.SharedPrivateKernelFactor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The spectral split — a symmetric idempotent is an orthonormal rank-one sum

The rank-two split gave the width-free corner identity at kernel trace
two.  The same three steps work at every trace, and the induction gives
the whole spectral decomposition with no eigenvalue theory: a symmetric
idempotent of trace `r` is the sum of the rank ones of `r` orthonormal
vectors.

The induction.  At trace zero the entry sum of squares is the trace,
thus the matrix vanishes and the empty family works.  At a positive
trace some diagonal entry is nonzero, its column normalizes to a unit
fixed vector, and removing that rank one drops the trace by one.  The
recursive family is fixed by the remainder, and the removed vector dies
against the remainder, thus the new vector is orthogonal to all of
them.

The carrier energy.  In the split the entries of the projector read as
coordinate products of the family.  A carrier of slots then carries an
energy matrix of that family, of size the trace.  A carrier read of the
projector becomes an eigenvalue equation of that energy matrix, and the
reading vector is not the zero vector.  Thus every carrier law is a law
of a matrix whose size is the trace, not the slot count.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.vecMulVec_mulVec` — the rank-one action.
* `Gtz.exists_orthonormal_family_of_trace` — **THE SPECTRAL SPLIT.**
* `Gtz.carrierEnergy` with `Gtz.trace_carrierEnergy` — the carrier
  energy matrix and its trace.
* `Gtz.carrierEnergy_mulVec_eq` — **THE CARRIER EIGENVALUE LAW.**
* `Gtz.carrierReading_ne_zero` — the reading vector survives.
* `Gtz.exists_carrier_energy_eigen` — **THE CARRIER PACKAGE.**
* `Gtz.SharedPrivateData.exists_kernel_spectral_split` — the split at
  the datum.

## Vacuity

The matrix statements are unconditional.  The datum statement
quantifies over shared-private data, and no datum exists if
`Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the spectral split -/

/-- The rank one of a vector acts by the energy against it. -/
theorem vecMulVec_mulVec {n : ℕ} (leftVec rightVec probe : Fin n → ℝ) :
    Matrix.vecMulVec leftVec rightVec *ᵥ probe = (rightVec ⬝ᵥ probe) • leftVec := by
  funext rowSlot
  rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, dotProduct,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun colSlot _ => ?_
  rw [Matrix.vecMulVec_apply]
  ring

/-- An orthonormal rank-one sum fixes each of its vectors. -/
theorem orthonormal_sum_mulVec {n rank : ℕ} {family : Fin rank → (Fin n → ℝ)}
    (hnorm : ∀ index, family index ⬝ᵥ family index = 1)
    (horth : ∀ indexOne indexTwo, indexOne ≠ indexTwo →
      family indexOne ⬝ᵥ family indexTwo = 0)
    (index : Fin rank) :
    (∑ probe, Matrix.vecMulVec (family probe) (family probe)) *ᵥ family index
      = family index := by
  classical
  rw [Matrix.sum_mulVec]
  rw [Finset.sum_congr rfl fun probe _ =>
    vecMulVec_mulVec (family probe) (family probe) (family index)]
  rw [Finset.sum_eq_single index
    (fun probe _ hne => by rw [horth probe index hne, zero_smul])
    (fun hnot => absurd (Finset.mem_univ _) hnot)]
  rw [hnorm index, one_smul]

/-- **THE SPECTRAL SPLIT.**  A symmetric idempotent of natural trace is
the sum of the rank ones of that many orthonormal vectors. -/
theorem exists_orthonormal_family_of_trace {n : ℕ} :
    ∀ (rank : ℕ) (K : Matrix (Fin n) (Fin n) ℝ), Kᵀ = K → K * K = K →
      Matrix.trace K = (rank : ℝ) →
      ∃ family : Fin rank → (Fin n → ℝ),
        (∀ index, family index ⬝ᵥ family index = 1)
        ∧ (∀ indexOne indexTwo, indexOne ≠ indexTwo →
            family indexOne ⬝ᵥ family indexTwo = 0)
        ∧ K = ∑ index, Matrix.vecMulVec (family index) (family index) := by
  intro rank
  induction rank with
  | zero =>
    intro K hsymm hidem htrace
    refine ⟨Fin.elim0, fun index => index.elim0, fun indexOne _ _ => indexOne.elim0, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact eq_zero_of_symm_idem_trace_zero hsymm hidem (by rw [htrace]; norm_num)
  | succ lowerRank ih =>
    intro K hsymm hidem htrace
    have htraceNe : Matrix.trace K ≠ 0 := by
      rw [htrace]
      positivity
    obtain ⟨headVec, hheadNorm, hheadFix⟩ :=
      exists_unit_fixed_of_trace_ne_zero hsymm hidem htraceNe
    obtain ⟨hsymmRest, hidemRest, htraceRest⟩ :=
      deflate_symm_idem hsymm hidem hheadNorm hheadFix
    obtain ⟨tailFamily, htailNorm, htailOrth, htailEq⟩ :=
      ih (K - Matrix.vecMulVec headVec headVec) hsymmRest hidemRest
        (by rw [htraceRest, htrace]; push_cast; ring)
    have hheadKill : (K - Matrix.vecMulVec headVec headVec) *ᵥ headVec = 0 := by
      rw [Matrix.sub_mulVec, hheadFix, vecMulVec_mulVec, hheadNorm, one_smul,
        sub_self]
    have hcross : ∀ index, headVec ⬝ᵥ tailFamily index = 0 := by
      intro index
      have hfix : (K - Matrix.vecMulVec headVec headVec) *ᵥ tailFamily index
          = tailFamily index := by
        rw [htailEq]
        exact orthonormal_sum_mulVec htailNorm htailOrth index
      calc headVec ⬝ᵥ tailFamily index
          = headVec ⬝ᵥ ((K - Matrix.vecMulVec headVec headVec) *ᵥ tailFamily index) := by
            rw [hfix]
        _ = ((K - Matrix.vecMulVec headVec headVec) *ᵥ headVec) ⬝ᵥ tailFamily index :=
            dotProduct_mulVec_symm hsymmRest _ _
        _ = 0 := by rw [hheadKill, zero_dotProduct]
    refine ⟨Fin.cons headVec tailFamily, ?_, ?_, ?_⟩
    · intro index
      refine Fin.cases ?_ ?_ index
      · rw [Fin.cons_zero]
        exact hheadNorm
      · intro lowerIndex
        rw [Fin.cons_succ]
        exact htailNorm lowerIndex
    · intro indexOne
      refine Fin.cases ?_ ?_ indexOne
      · intro indexTwo
        refine Fin.cases ?_ ?_ indexTwo
        · intro hne
          exact absurd rfl hne
        · intro lowerTwo _
          rw [Fin.cons_zero, Fin.cons_succ]
          exact hcross lowerTwo
      · intro lowerOne indexTwo
        refine Fin.cases ?_ ?_ indexTwo
        · intro _
          rw [Fin.cons_zero, Fin.cons_succ, dotProduct_comm]
          exact hcross lowerOne
        · intro lowerTwo hne
          rw [Fin.cons_succ, Fin.cons_succ]
          refine htailOrth lowerOne lowerTwo fun heq => hne ?_
          rw [heq]
    · rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [← htailEq]
      abel

/-! ## Layer 2 — the carrier energy matrix -/

/-- The carrier energy matrix of a family: the Gram of the family
restricted to the carrier slots. -/
def carrierEnergy {n rank : ℕ} (family : Fin rank → (Fin n → ℝ))
    (car : Finset (Fin n)) : Matrix (Fin rank) (Fin rank) ℝ :=
  Matrix.of fun rowIndex colIndex =>
    ∑ slot ∈ car, family rowIndex slot * family colIndex slot

/-- The carrier reading of a vector against a family. -/
def carrierReading {n rank : ℕ} (family : Fin rank → (Fin n → ℝ))
    (car : Finset (Fin n)) (vec : Fin n → ℝ) : Fin rank → ℝ :=
  fun index => ∑ slot ∈ car, vec slot * family index slot

/-- The trace of the carrier energy matrix is the carrier diagonal total
of the projector. -/
theorem trace_carrierEnergy {n rank : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    {family : Fin rank → (Fin n → ℝ)}
    (hsplit : K = ∑ index, Matrix.vecMulVec (family index) (family index))
    (car : Finset (Fin n)) :
    Matrix.trace (carrierEnergy family car) = ∑ slot ∈ car, K slot slot := by
  classical
  have hentry : ∀ rowSlot colSlot : Fin n,
      K rowSlot colSlot = ∑ index, family index rowSlot * family index colSlot := by
    intro rowSlot colSlot
    rw [hsplit, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun index _ => by rw [Matrix.vecMulVec_apply]
  rw [Matrix.trace]
  have hdiag : ∀ index : Fin rank, Matrix.diag (carrierEnergy family car) index
      = ∑ slot ∈ car, family index slot * family index slot := fun _ => rfl
  rw [Finset.sum_congr rfl fun index _ => hdiag index, Finset.sum_comm]
  exact Finset.sum_congr rfl fun slot _ => (hentry slot slot).symm

/-- **THE CARRIER EIGENVALUE LAW.**  A carrier read of the projector is
an eigenvalue equation of the carrier energy matrix at the carrier
reading. -/
theorem carrierEnergy_mulVec_eq {n rank : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    {family : Fin rank → (Fin n → ℝ)}
    (hsplit : K = ∑ index, Matrix.vecMulVec (family index) (family index))
    {car : Finset (Fin n)} {vec : Fin n → ℝ} {readVal : ℝ}
    (hsupp : ∀ slot ∉ car, vec slot = 0)
    (hread : ∀ slot ∈ car, (K *ᵥ vec) slot = readVal * vec slot) :
    carrierEnergy family car *ᵥ carrierReading family car vec
      = readVal • carrierReading family car vec := by
  classical
  have hentry : ∀ rowSlot colSlot : Fin n,
      K rowSlot colSlot = ∑ index, family index rowSlot * family index colSlot := by
    intro rowSlot colSlot
    rw [hsplit, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun index _ => by rw [Matrix.vecMulVec_apply]
  have hmulVec : ∀ rowSlot : Fin n, (K *ᵥ vec) rowSlot
      = ∑ index, family index rowSlot * carrierReading family car vec index := by
    intro rowSlot
    rw [Matrix.mulVec, dotProduct]
    have hrestrict : ∑ colSlot, K rowSlot colSlot * vec colSlot
        = ∑ colSlot ∈ car, K rowSlot colSlot * vec colSlot := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro colSlot _ hnot
      rw [hsupp colSlot hnot, mul_zero]
    rw [hrestrict]
    have hswap : ∑ colSlot ∈ car, K rowSlot colSlot * vec colSlot
        = ∑ colSlot ∈ car, ∑ index,
            family index rowSlot * (vec colSlot * family index colSlot) := by
      refine Finset.sum_congr rfl fun colSlot _ => ?_
      rw [hentry rowSlot colSlot, Finset.sum_mul]
      exact Finset.sum_congr rfl fun index _ => by ring
    rw [hswap, Finset.sum_comm]
    refine Finset.sum_congr rfl fun index _ => ?_
    rw [carrierReading, Finset.mul_sum]
  funext index
  have hleft : (carrierEnergy family car *ᵥ carrierReading family car vec) index
      = ∑ slot ∈ car, family index slot
          * ∑ probe, family probe slot * carrierReading family car vec probe := by
    rw [Matrix.mulVec, dotProduct]
    have hcell : ∀ probe : Fin rank,
        carrierEnergy family car index probe * carrierReading family car vec probe
          = ∑ slot ∈ car, family index slot
              * (family probe slot * carrierReading family car vec probe) := by
      intro probe
      rw [carrierEnergy, Matrix.of_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun slot _ => by ring
    rw [Finset.sum_congr rfl fun probe _ => hcell probe, Finset.sum_comm]
    exact Finset.sum_congr rfl fun slot _ => by rw [Finset.mul_sum]
  rw [hleft]
  have hcollapse : ∀ slot ∈ car, family index slot
      * ∑ probe, family probe slot * carrierReading family car vec probe
      = family index slot * (readVal * vec slot) := by
    intro slot hslot
    rw [← hmulVec slot, hread slot hslot]
  rw [Finset.sum_congr rfl hcollapse, Pi.smul_apply, smul_eq_mul, carrierReading,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun slot _ => by ring

/-- The carrier reading of a nonzero read vector does not vanish. -/
theorem carrierReading_ne_zero {n rank : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    {family : Fin rank → (Fin n → ℝ)}
    (hsplit : K = ∑ index, Matrix.vecMulVec (family index) (family index))
    {car : Finset (Fin n)} {vec : Fin n → ℝ} {readVal : ℝ}
    (hreadNe : readVal ≠ 0)
    (hsupp : ∀ slot ∉ car, vec slot = 0) (hnz : vec ≠ 0)
    (hread : ∀ slot ∈ car, (K *ᵥ vec) slot = readVal * vec slot) :
    carrierReading family car vec ≠ 0 := by
  classical
  have hentry : ∀ rowSlot colSlot : Fin n,
      K rowSlot colSlot = ∑ index, family index rowSlot * family index colSlot := by
    intro rowSlot colSlot
    rw [hsplit, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun index _ => by rw [Matrix.vecMulVec_apply]
  have hmulVec : ∀ rowSlot : Fin n, (K *ᵥ vec) rowSlot
      = ∑ index, family index rowSlot * carrierReading family car vec index := by
    intro rowSlot
    rw [Matrix.mulVec, dotProduct]
    have hrestrict : ∑ colSlot, K rowSlot colSlot * vec colSlot
        = ∑ colSlot ∈ car, K rowSlot colSlot * vec colSlot := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro colSlot _ hnot
      rw [hsupp colSlot hnot, mul_zero]
    rw [hrestrict]
    have hswap : ∑ colSlot ∈ car, K rowSlot colSlot * vec colSlot
        = ∑ colSlot ∈ car, ∑ index,
            family index rowSlot * (vec colSlot * family index colSlot) := by
      refine Finset.sum_congr rfl fun colSlot _ => ?_
      rw [hentry rowSlot colSlot, Finset.sum_mul]
      exact Finset.sum_congr rfl fun index _ => by ring
    rw [hswap, Finset.sum_comm]
    refine Finset.sum_congr rfl fun index _ => ?_
    rw [carrierReading, Finset.mul_sum]
  intro hzero
  refine hnz (funext fun slot => ?_)
  by_cases hslot : slot ∈ car
  · have hkill : (K *ᵥ vec) slot = 0 := by
      rw [hmulVec slot]
      refine Finset.sum_eq_zero fun index _ => ?_
      rw [congrFun hzero index, Pi.zero_apply, mul_zero]
    rw [hread slot hslot] at hkill
    exact (mul_eq_zero.mp hkill).resolve_left hreadNe
  · exact hsupp slot hslot

/-- **THE CARRIER PACKAGE.**  A symmetric idempotent of natural trace
with a carrier read gives an energy matrix of that size, whose trace is
the carrier diagonal total and which carries the read as an eigenvalue
at a nonzero reading. -/
theorem exists_carrier_energy_eigen {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K) (rank : ℕ)
    (htrace : Matrix.trace K = (rank : ℝ))
    {car : Finset (Fin n)} {vec : Fin n → ℝ} {readVal : ℝ}
    (hreadNe : readVal ≠ 0)
    (hsupp : ∀ slot ∉ car, vec slot = 0) (hnz : vec ≠ 0)
    (hread : ∀ slot ∈ car, (K *ᵥ vec) slot = readVal * vec slot) :
    ∃ (energy : Matrix (Fin rank) (Fin rank) ℝ) (reading : Fin rank → ℝ),
      energyᵀ = energy
      ∧ Matrix.trace energy = ∑ slot ∈ car, K slot slot
      ∧ reading ≠ 0
      ∧ energy *ᵥ reading = readVal • reading := by
  obtain ⟨family, hnorm, horth, hsplit⟩ :=
    exists_orthonormal_family_of_trace rank K hsymm hidem htrace
  refine ⟨carrierEnergy family car, carrierReading family car vec, ?_,
    trace_carrierEnergy hsplit car,
    carrierReading_ne_zero hsplit hreadNe hsupp hnz hread,
    carrierEnergy_mulVec_eq hsplit hsupp hread⟩
  ext rowIndex colIndex
  rw [Matrix.transpose_apply]
  simp only [carrierEnergy, Matrix.of_apply]
  exact Finset.sum_congr rfl fun slot _ => mul_comm _ _

/-! ## Layer 3 — the split at the datum -/

/-- The spectral split of the kernel projector at a diagonal-Gram
shared-private datum: the projector of the coefficient complement is the
sum of the rank ones of a family whose size is the kernel gap. -/
theorem SharedPrivateData.exists_kernel_spectral_split {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) (rank : ℕ)
    (hgap : (data.basisCount : ℝ) = Matrix.trace data.coeff + rank) :
    ∃ (S : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ)
      (readVecs : Fin 6 → Fin data.basisCount → ℝ)
      (family : Fin rank → (Fin data.basisCount → ℝ)),
      (∀ index, family index ⬝ᵥ family index = 1)
      ∧ (∀ indexOne indexTwo, indexOne ≠ indexTwo →
          family indexOne ⬝ᵥ family indexTwo = 0)
      ∧ (1 : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ) - S
        = ∑ index, Matrix.vecMulVec (family index) (family index)
      ∧ (∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
          atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot) →
          readVecs atomIndex slot = 0)
      ∧ (∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
          atomIndex ∈ data.activeSubset (data.basisLabel slot) →
          (((1 : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ) - S)
              *ᵥ readVecs atomIndex) slot
            = (1 - (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomIndex))
              * readVecs atomIndex slot)
      ∧ (∀ atomIndex : Fin 6, readVecs atomIndex ≠ 0) := by
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsupp, hread, _, hnz, _⟩ :=
    data.exists_kernel_read_frame hdiag
  have hKsymm : ((1 : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ) - S)ᵀ
      = 1 - S := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hSsymm]
  have hKidem : ((1 : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ) - S)
      * (1 - S) = 1 - S := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, hSidem]
    abel
  have hKtrace : Matrix.trace
      ((1 : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ) - S)
      = (rank : ℝ) := by
    rw [Matrix.trace_sub, Matrix.trace_one, hStrace, Fintype.card_fin, hgap]
    ring
  obtain ⟨family, hnorm, horth, hsplit⟩ :=
    exists_orthonormal_family_of_trace rank _ hKsymm hKidem hKtrace
  exact ⟨S, readVecs, family, hnorm, horth, hsplit, hsupp,
    fun atomIndex slot hmem => kernel_corner_read (hread atomIndex slot hmem), hnz⟩

end Gtz
