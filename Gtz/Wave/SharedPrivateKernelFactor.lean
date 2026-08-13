import Gtz.Wave.SharedPrivateKernelMinor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The kernel factorization — the rank-two split makes the corner identity width-free

The kernel-minor budget priced the carrier corners of a trace-two
kernel projector, but only at carriers of one, two or three slots.  The
width bound came from the characteristic polynomial, and it is not
needed.  A symmetric idempotent of trace two splits into two
orthonormal rank-one pieces, and in that split every corner law is a
two-by-two law.

The split.  A symmetric idempotent with a nonzero trace has a nonzero
diagonal entry, thus its column at that slot normalizes to a unit fixed
vector.  Subtracting the rank one of that vector leaves a symmetric
idempotent with the trace one unit lower.  A symmetric idempotent of
trace zero has a zero entry sum of squares, thus it is the zero matrix.
Two steps from trace two give the split, and the two vectors are
orthogonal because the first one dies against the remainder.

The corner law.  In the split the entries read as two coordinate
products.  A carrier read of the projector becomes a two-by-two
eigenvalue equation in the two carrier energies and their cross term,
and the pair of carrier readings is not the zero pair.  Thus the read
solves the two-by-two characteristic equation, and the corner minor
total is the read times the corner defect at every carrier width.

The consequences.  The kernel-minor kill drops its width bound and its
carrier-witness bookkeeping.  The deficit kill at basis count five
drops the profile arithmetic.  And the kill becomes a statement about
the difference between the basis count and the coefficient trace, thus
it covers the whole kernel-trace-two stratum.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.eq_zero_of_symm_idem_trace_zero` — **THE TRACE-ZERO LAW.**
* `Gtz.exists_unit_fixed_of_trace_ne_zero` — the unit fixed vector.
* `Gtz.exists_orthonormal_pair_of_trace_two` — **THE RANK-TWO SPLIT.**
* `Gtz.kernelMinor_eq_wedge_sq` — the minor is a wedge square.
* `Gtz.kernelMinor_corner_eq` — **THE WIDTH-FREE CORNER IDENTITY.**
* `Gtz.false_of_kernelMinor_budget_general` — **THE WIDTH-FREE KILL.**
* `Gtz.SharedPrivateData.false_of_kernel_trace_two` — **THE DATUM KILL
  ON THE WHOLE KERNEL-TRACE-TWO STRATUM.**
* `Gtz.SharedPrivateData.false_of_deficit_five_general` — the deficit
  kill at basis count five with no profile arithmetic.
* `Gtz.union_eq_univ_of_disjoint_card_three` — the complementary
  support law at six atoms.
* `Gtz.SharedPrivateDeficitComplementClosed` with
  `Gtz.sharedPrivateDeficitClosed_of_complement_residues` — the sharper
  deficit dispatch.

## Vacuity

The matrix statements are unconditional.  The data-facing statements
quantify over shared-private data, and no datum exists if
`Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the rank-two split of a trace-two idempotent -/

/-- **THE TRACE-ZERO LAW.**  A symmetric idempotent of trace zero is the
zero matrix: its entry sum of squares is its trace. -/
theorem eq_zero_of_symm_idem_trace_zero {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K) (htrace : Matrix.trace K = 0) :
    K = 0 := by
  have hentry : ∀ rowSlot colSlot : Fin n, K colSlot rowSlot = K rowSlot colSlot := by
    intro rowSlot colSlot
    have := congrFun (congrFun hsymm rowSlot) colSlot
    rwa [Matrix.transpose_apply] at this
  have hsquares : ∑ rowSlot : Fin n, ∑ colSlot : Fin n, K rowSlot colSlot ^ 2 = 0 := by
    have hdiag : ∀ rowSlot : Fin n,
        ∑ colSlot, K rowSlot colSlot ^ 2 = K rowSlot rowSlot := by
      intro rowSlot
      have h := congrFun (congrFun hidem rowSlot) rowSlot
      rw [Matrix.mul_apply] at h
      rw [← h]
      exact Finset.sum_congr rfl fun colSlot _ => by rw [hentry rowSlot colSlot, sq]
    rw [Finset.sum_congr rfl fun rowSlot _ => hdiag rowSlot]
    exact htrace
  ext rowSlot colSlot
  have hnonneg : ∀ probe : Fin n, 0 ≤ ∑ colSlot, K probe colSlot ^ 2 :=
    fun probe => Finset.sum_nonneg fun colSlot _ => sq_nonneg _
  have hrow : ∑ colSlot, K rowSlot colSlot ^ 2 = 0 :=
    le_antisymm (hsquares ▸ Finset.single_le_sum (f := fun probe : Fin n =>
      ∑ colSlot, K probe colSlot ^ 2) (fun probe _ => hnonneg probe)
      (Finset.mem_univ rowSlot)) (hnonneg rowSlot)
  have hsq : K rowSlot colSlot ^ 2 = 0 :=
    le_antisymm (hrow ▸ Finset.single_le_sum (f := fun probe : Fin n =>
      K rowSlot probe ^ 2) (fun probe _ => sq_nonneg _) (Finset.mem_univ colSlot))
      (sq_nonneg _)
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

/-- A symmetric idempotent with a nonzero trace fixes a unit vector: its
column at a nonzero diagonal slot normalizes. -/
theorem exists_unit_fixed_of_trace_ne_zero {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K) (htrace : Matrix.trace K ≠ 0) :
    ∃ unitVec : Fin n → ℝ, unitVec ⬝ᵥ unitVec = 1 ∧ K *ᵥ unitVec = unitVec := by
  classical
  have hsum : ∑ slot : Fin n, K slot slot ≠ 0 := htrace
  obtain ⟨pivot, -, hpivot⟩ : ∃ pivot ∈ Finset.univ, K pivot pivot ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hsum (Finset.sum_eq_zero fun slot hslot => hall slot hslot)
  have hpos : 0 < K pivot pivot := by
    have hdot := kernelColumn_dot hsymm hidem pivot pivot
    rw [dotProduct] at hdot
    have hge : 0 ≤ K pivot pivot := by
      rw [← hdot]
      exact Finset.sum_nonneg fun slot _ => mul_self_nonneg _
    exact hge.lt_of_ne (Ne.symm hpivot)
  set scale : ℝ := (Real.sqrt (K pivot pivot))⁻¹ with hscale
  have hroot : Real.sqrt (K pivot pivot) * Real.sqrt (K pivot pivot) = K pivot pivot :=
    Real.mul_self_sqrt hpos.le
  have hrootPos : 0 < Real.sqrt (K pivot pivot) := Real.sqrt_pos.mpr hpos
  refine ⟨scale • kernelColumn K pivot, ?_, ?_⟩
  · rw [dotProduct_smul, smul_dotProduct, kernelColumn_dot hsymm hidem pivot pivot,
      smul_eq_mul, smul_eq_mul, hscale]
    field_simp
    linarith [hroot]
  · rw [Matrix.mulVec_smul, kernelColumn_fixed hidem pivot]

/-- The rank-one matrix of a vector against itself is symmetric. -/
theorem vecMulVec_self_transpose {n : ℕ} (probe : Fin n → ℝ) :
    (Matrix.vecMulVec probe probe)ᵀ = Matrix.vecMulVec probe probe := by
  ext rowSlot colSlot
  simp [Matrix.vecMulVec_apply, mul_comm]

/-- The trace of a rank-one matrix is the energy of its vector. -/
theorem trace_vecMulVec_self {n : ℕ} (probe : Fin n → ℝ) :
    Matrix.trace (Matrix.vecMulVec probe probe) = probe ⬝ᵥ probe := by
  rw [Matrix.trace, dotProduct]
  exact Finset.sum_congr rfl fun slot _ => rfl

/-- A matrix absorbs a rank-one factor on the left through its action on
the left vector. -/
theorem mul_vecMulVec {n : ℕ} (mat : Matrix (Fin n) (Fin n) ℝ)
    (leftVec rightVec : Fin n → ℝ) :
    mat * Matrix.vecMulVec leftVec rightVec
      = Matrix.vecMulVec (mat *ᵥ leftVec) rightVec := by
  ext rowSlot colSlot
  rw [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun midSlot _ => by
    rw [Matrix.vecMulVec_apply, mul_assoc]

/-- Two rank-one matrices multiply through the cross energy. -/
theorem rankOne_mul_rankOne {n : ℕ} (firstVec secondVec thirdVec fourthVec :
    Fin n → ℝ) :
    Matrix.vecMulVec firstVec secondVec * Matrix.vecMulVec thirdVec fourthVec
      = (secondVec ⬝ᵥ thirdVec) • Matrix.vecMulVec firstVec fourthVec := by
  ext rowSlot colSlot
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun midSlot _ => ?_
  rw [Matrix.vecMulVec_apply, Matrix.vecMulVec_apply]
  ring

/-- A symmetric matrix moves across a dot product. -/
theorem dotProduct_mulVec_symm {n : ℕ} {mat : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : matᵀ = mat) (leftVec rightVec : Fin n → ℝ) :
    leftVec ⬝ᵥ (mat *ᵥ rightVec) = (mat *ᵥ leftVec) ⬝ᵥ rightVec := by
  have hentry : ∀ rowSlot colSlot : Fin n, mat colSlot rowSlot = mat rowSlot colSlot := by
    intro rowSlot colSlot
    have := congrFun (congrFun hsymm rowSlot) colSlot
    rwa [Matrix.transpose_apply] at this
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun rowSlot _ => Finset.sum_congr rfl fun colSlot _ => ?_
  rw [hentry]
  ring

/-- Removing the rank one of a unit fixed vector leaves a symmetric
idempotent with the trace one unit lower. -/
theorem deflate_symm_idem {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K) {unitVec : Fin n → ℝ}
    (hunit : unitVec ⬝ᵥ unitVec = 1) (hfix : K *ᵥ unitVec = unitVec) :
    (K - Matrix.vecMulVec unitVec unitVec)ᵀ = K - Matrix.vecMulVec unitVec unitVec
      ∧ (K - Matrix.vecMulVec unitVec unitVec) * (K - Matrix.vecMulVec unitVec unitVec)
        = K - Matrix.vecMulVec unitVec unitVec
      ∧ Matrix.trace (K - Matrix.vecMulVec unitVec unitVec)
        = Matrix.trace K - 1 := by
  have hleft : K * Matrix.vecMulVec unitVec unitVec
      = Matrix.vecMulVec unitVec unitVec := by
    rw [mul_vecMulVec, hfix]
  have hright : Matrix.vecMulVec unitVec unitVec * K
      = Matrix.vecMulVec unitVec unitVec := by
    have := congrArg Matrix.transpose hleft
    rw [Matrix.transpose_mul, vecMulVec_self_transpose, hsymm] at this
    exact this
  have hsquare : Matrix.vecMulVec unitVec unitVec * Matrix.vecMulVec unitVec unitVec
      = Matrix.vecMulVec unitVec unitVec := by
    rw [rankOne_mul_rankOne, hunit, one_smul]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.transpose_sub, hsymm, vecMulVec_self_transpose]
  · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hidem, hleft, hright,
      hsquare]
    abel
  · rw [Matrix.trace_sub, trace_vecMulVec_self, hunit]

/-- **THE RANK-TWO SPLIT.**  A symmetric idempotent of trace two is the
sum of the rank ones of two orthonormal vectors. -/
theorem exists_orthonormal_pair_of_trace_two {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K) (htrace : Matrix.trace K = 2) :
    ∃ firstVec secondVec : Fin n → ℝ,
      firstVec ⬝ᵥ firstVec = 1 ∧ secondVec ⬝ᵥ secondVec = 1
      ∧ firstVec ⬝ᵥ secondVec = 0
      ∧ K = Matrix.vecMulVec firstVec firstVec
          + Matrix.vecMulVec secondVec secondVec := by
  obtain ⟨firstVec, hfirstUnit, hfirstFix⟩ :=
    exists_unit_fixed_of_trace_ne_zero hsymm hidem (by rw [htrace]; norm_num)
  obtain ⟨hsymmOne, hidemOne, htraceOneRaw⟩ :=
    deflate_symm_idem hsymm hidem hfirstUnit hfirstFix
  have htraceOne : Matrix.trace (K - Matrix.vecMulVec firstVec firstVec) = 1 := by
    rw [htraceOneRaw, htrace]
    norm_num
  obtain ⟨secondVec, hsecondUnit, hsecondFix⟩ :=
    exists_unit_fixed_of_trace_ne_zero hsymmOne hidemOne (by rw [htraceOne]; norm_num)
  obtain ⟨hsymmTwo, hidemTwo, htraceTwoRaw⟩ :=
    deflate_symm_idem hsymmOne hidemOne hsecondUnit hsecondFix
  have htraceTwo : Matrix.trace (K - Matrix.vecMulVec firstVec firstVec
      - Matrix.vecMulVec secondVec secondVec) = 0 := by
    rw [htraceTwoRaw, htraceOne]
    norm_num
  have hzero := eq_zero_of_symm_idem_trace_zero hsymmTwo hidemTwo htraceTwo
  have hrankOneFix : Matrix.vecMulVec firstVec firstVec *ᵥ firstVec = firstVec := by
    funext slot
    rw [Matrix.mulVec, dotProduct]
    have hpull : ∑ colSlot, Matrix.vecMulVec firstVec firstVec slot colSlot
        * firstVec colSlot
        = firstVec slot * ∑ colSlot, firstVec colSlot * firstVec colSlot := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun colSlot _ => by
        rw [Matrix.vecMulVec_apply]
        ring
    rw [hpull]
    have hone : ∑ colSlot, firstVec colSlot * firstVec colSlot = 1 := hfirstUnit
    rw [hone, mul_one]
  have hkill : (K - Matrix.vecMulVec firstVec firstVec) *ᵥ firstVec = 0 := by
    rw [Matrix.sub_mulVec, hfirstFix, hrankOneFix, sub_self]
  have hcross : firstVec ⬝ᵥ secondVec = 0 := by
    calc firstVec ⬝ᵥ secondVec
        = firstVec ⬝ᵥ ((K - Matrix.vecMulVec firstVec firstVec) *ᵥ secondVec) := by
          rw [hsecondFix]
      _ = ((K - Matrix.vecMulVec firstVec firstVec) *ᵥ firstVec) ⬝ᵥ secondVec :=
          dotProduct_mulVec_symm hsymmOne _ _
      _ = 0 := by rw [hkill, zero_dotProduct]
  refine ⟨firstVec, secondVec, hfirstUnit, hsecondUnit, hcross, ?_⟩
  have hpair : K - Matrix.vecMulVec firstVec firstVec
      = Matrix.vecMulVec secondVec secondVec := sub_eq_zero.mp hzero
  calc K = (K - Matrix.vecMulVec firstVec firstVec)
        + Matrix.vecMulVec firstVec firstVec := by abel
    _ = Matrix.vecMulVec secondVec secondVec
        + Matrix.vecMulVec firstVec firstVec := by rw [hpair]
    _ = Matrix.vecMulVec firstVec firstVec
        + Matrix.vecMulVec secondVec secondVec := by abel

/-! ## Layer 2 — the width-free corner identity -/

/-- In the rank-two split the minor of a slot pair is the square of the
wedge of the two coordinate pairs. -/
theorem kernelMinor_eq_wedge_sq {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    {firstVec secondVec : Fin n → ℝ}
    (hsplit : K = Matrix.vecMulVec firstVec firstVec
      + Matrix.vecMulVec secondVec secondVec)
    (rowSlot colSlot : Fin n) :
    kernelMinor K rowSlot colSlot
      = (firstVec rowSlot * secondVec colSlot
          - firstVec colSlot * secondVec rowSlot) ^ 2 := by
  have hentry : ∀ probeOne probeTwo : Fin n, K probeOne probeTwo
      = firstVec probeOne * firstVec probeTwo
        + secondVec probeOne * secondVec probeTwo := by
    intro probeOne probeTwo
    rw [hsplit]
    simp [Matrix.vecMulVec_apply]
  simp only [kernelMinor, hentry]
  ring

/-- **THE WIDTH-FREE CORNER IDENTITY.**  At kernel trace two the corner
minor total of any carrier is the read times the corner defect.  The
read solves the two-by-two characteristic equation of the carrier
energies. -/
theorem kernelMinor_corner_eq {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K) (htrace : Matrix.trace K = 2)
    {car : Finset (Fin n)} {vec : Fin n → ℝ} {readVal : ℝ}
    (hreadNe : readVal ≠ 0)
    (hsupp : ∀ slot ∉ car, vec slot = 0) (hnz : vec ≠ 0)
    (hread : ∀ slot ∈ car, (K *ᵥ vec) slot = readVal * vec slot) :
    ∑ rowSlot ∈ car, ∑ colSlot ∈ car, kernelMinor K rowSlot colSlot
      = 2 * readVal * ((∑ rowSlot ∈ car, K rowSlot rowSlot) - readVal) := by
  classical
  obtain ⟨firstVec, secondVec, hfirstUnit, hsecondUnit, hcross, hsplit⟩ :=
    exists_orthonormal_pair_of_trace_two hsymm hidem htrace
  have hentry : ∀ probeOne probeTwo : Fin n, K probeOne probeTwo
      = firstVec probeOne * firstVec probeTwo
        + secondVec probeOne * secondVec probeTwo := by
    intro probeOne probeTwo
    rw [hsplit]
    simp [Matrix.vecMulVec_apply]
  set firstEnergy : ℝ := ∑ slot ∈ car, firstVec slot * firstVec slot
    with hfirstEnergy
  set secondEnergy : ℝ := ∑ slot ∈ car, secondVec slot * secondVec slot
    with hsecondEnergy
  set crossEnergy : ℝ := ∑ slot ∈ car, firstVec slot * secondVec slot
    with hcrossEnergy
  -- the carrier diagonal total
  have hdiagTotal : ∑ rowSlot ∈ car, K rowSlot rowSlot
      = firstEnergy + secondEnergy := by
    rw [hfirstEnergy, hsecondEnergy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun slot _ => hentry slot slot
  -- the corner minor total
  have hdouble : ∀ probeOne probeTwo : Fin n → ℝ,
      ∑ rowSlot ∈ car, ∑ colSlot ∈ car, probeOne rowSlot * probeTwo colSlot
        = (∑ rowSlot ∈ car, probeOne rowSlot) * (∑ colSlot ∈ car, probeTwo colSlot) :=
    fun probeOne probeTwo => (Finset.sum_mul_sum _ _ _ _).symm
  have hminorTotal : ∑ rowSlot ∈ car, ∑ colSlot ∈ car, kernelMinor K rowSlot colSlot
      = 2 * (firstEnergy * secondEnergy - crossEnergy * crossEnergy) := by
    have hterm : ∀ rowSlot colSlot : Fin n, kernelMinor K rowSlot colSlot
        = (firstVec rowSlot * firstVec rowSlot)
            * (secondVec colSlot * secondVec colSlot)
          + (secondVec rowSlot * secondVec rowSlot)
            * (firstVec colSlot * firstVec colSlot)
          + (-2 * (firstVec rowSlot * secondVec rowSlot))
            * (firstVec colSlot * secondVec colSlot) := by
      intro rowSlot colSlot
      rw [kernelMinor_eq_wedge_sq hsplit]
      ring
    rw [Finset.sum_congr rfl fun rowSlot _ =>
      Finset.sum_congr rfl fun colSlot _ => hterm rowSlot colSlot]
    simp only [Finset.sum_add_distrib]
    rw [hdouble, hdouble, hdouble]
    have hneg : ∑ rowSlot ∈ car, (-2 * (firstVec rowSlot * secondVec rowSlot))
        = -2 * crossEnergy := by
      rw [hcrossEnergy, Finset.mul_sum]
    rw [hneg, ← hfirstEnergy, ← hsecondEnergy, ← hcrossEnergy]
    ring
  -- the carrier readings
  set firstRead : ℝ := ∑ slot ∈ car, vec slot * firstVec slot with hfirstRead
  set secondRead : ℝ := ∑ slot ∈ car, vec slot * secondVec slot with hsecondRead
  have hmulVec : ∀ rowSlot : Fin n, (K *ᵥ vec) rowSlot
      = firstVec rowSlot * firstRead + secondVec rowSlot * secondRead := by
    intro rowSlot
    rw [Matrix.mulVec, dotProduct, hfirstRead, hsecondRead, Finset.mul_sum,
      Finset.mul_sum]
    have hrestrict : ∑ colSlot, K rowSlot colSlot * vec colSlot
        = ∑ colSlot ∈ car, K rowSlot colSlot * vec colSlot := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro colSlot _ hnot
      rw [hsupp colSlot hnot, mul_zero]
    rw [hrestrict, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun colSlot _ => ?_
    rw [hentry rowSlot colSlot]
    ring
  have hsystemOne : firstEnergy * firstRead + crossEnergy * secondRead
      = readVal * firstRead := by
    have hterm : ∀ slot ∈ car,
        firstVec slot * (firstVec slot * firstRead + secondVec slot * secondRead)
          = firstVec slot * (readVal * vec slot) := by
      intro slot hslot
      rw [← hmulVec slot, hread slot hslot]
    have hsum : ∑ slot ∈ car,
        firstVec slot * (firstVec slot * firstRead + secondVec slot * secondRead)
        = ∑ slot ∈ car, firstVec slot * (readVal * vec slot) :=
      Finset.sum_congr rfl hterm
    have hleft : ∑ slot ∈ car,
        firstVec slot * (firstVec slot * firstRead + secondVec slot * secondRead)
        = firstEnergy * firstRead + crossEnergy * secondRead := by
      rw [hfirstEnergy, hcrossEnergy, Finset.sum_mul, Finset.sum_mul,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun slot _ => by ring
    have hrightSum : ∑ slot ∈ car, firstVec slot * (readVal * vec slot)
        = readVal * firstRead := by
      rw [hfirstRead, Finset.mul_sum]
      exact Finset.sum_congr rfl fun slot _ => by ring
    rw [← hleft, hsum, hrightSum]
  have hsystemTwo : crossEnergy * firstRead + secondEnergy * secondRead
      = readVal * secondRead := by
    have hterm : ∀ slot ∈ car,
        secondVec slot * (firstVec slot * firstRead + secondVec slot * secondRead)
          = secondVec slot * (readVal * vec slot) := by
      intro slot hslot
      rw [← hmulVec slot, hread slot hslot]
    have hsum : ∑ slot ∈ car,
        secondVec slot * (firstVec slot * firstRead + secondVec slot * secondRead)
        = ∑ slot ∈ car, secondVec slot * (readVal * vec slot) :=
      Finset.sum_congr rfl hterm
    have hleft : ∑ slot ∈ car,
        secondVec slot * (firstVec slot * firstRead + secondVec slot * secondRead)
        = crossEnergy * firstRead + secondEnergy * secondRead := by
      rw [hsecondEnergy, hcrossEnergy, Finset.sum_mul, Finset.sum_mul,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun slot _ => by ring
    have hrightSum : ∑ slot ∈ car, secondVec slot * (readVal * vec slot)
        = readVal * secondRead := by
      rw [hsecondRead, Finset.mul_sum]
      exact Finset.sum_congr rfl fun slot _ => by ring
    rw [← hleft, hsum, hrightSum]
  -- the reading pair does not vanish
  have hreadNz : firstRead ≠ 0 ∨ secondRead ≠ 0 := by
    by_contra hboth
    push Not at hboth
    refine hnz (funext fun slot => ?_)
    by_cases hslot : slot ∈ car
    · have hzero : (K *ᵥ vec) slot = 0 := by
        rw [hmulVec slot, hboth.1, hboth.2]
        ring
      rw [hread slot hslot] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left hreadNe
    · exact hsupp slot hslot
  have hdet := det_two_eq_zero_of_kernel
    (entryOneOne := firstEnergy - readVal) (entryOneTwo := crossEnergy)
    (entryTwoOne := crossEnergy) (entryTwoTwo := secondEnergy - readVal)
    hreadNz (by linarith) (by linarith)
  rw [hminorTotal, hdiagTotal]
  linear_combination (2 : ℝ) * hdet

/-! ## Layer 3 — the width-free kill -/

/-- **THE WIDTH-FREE KERNEL-MINOR KILL.**  A symmetric idempotent of
trace two on the slots, with six carriers of any width, slot incidence
three, a nonvanishing carrier read at every atom, reads in the unit
window, every slot pair sharing an atom, and a read total above five,
does not exist. -/
theorem false_of_kernelMinor_budget_general {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K) (htrace : Matrix.trace K = 2)
    (car : Fin 6 → Finset (Fin n)) (readVecs : Fin 6 → Fin n → ℝ)
    (readVal : Fin 6 → ℝ)
    (hinc : ∀ slot : Fin n,
      (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex).card = 3)
    (hsupp : ∀ atomIndex, ∀ slot ∉ car atomIndex, readVecs atomIndex slot = 0)
    (hnz : ∀ atomIndex, readVecs atomIndex ≠ 0)
    (hread : ∀ atomIndex, ∀ slot ∈ car atomIndex,
      (K *ᵥ readVecs atomIndex) slot = readVal atomIndex * readVecs atomIndex slot)
    (hpos : ∀ atomIndex, 0 < readVal atomIndex)
    (hcap : ∀ atomIndex, readVal atomIndex ≤ 1)
    (hco : ∀ rowSlot colSlot : Fin n, rowSlot ≠ colSlot →
      ∃ atomIndex, rowSlot ∈ car atomIndex ∧ colSlot ∈ car atomIndex)
    (hsum : 5 < ∑ atomIndex, readVal atomIndex) :
    False := by
  classical
  have hcorner : ∀ atomIndex : Fin 6,
      ∑ rowSlot ∈ car atomIndex, ∑ colSlot ∈ car atomIndex,
          kernelMinor K rowSlot colSlot
        = 2 * readVal atomIndex
          * ((∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot)
              - readVal atomIndex) := fun atomIndex =>
    kernelMinor_corner_eq hsymm hidem htrace (hpos atomIndex).ne'
      (hsupp atomIndex) (hnz atomIndex) (hread atomIndex)
  have hexpand : ∀ (atomIndex : Fin 6) (probe : Fin n → ℝ),
      ∑ rowSlot ∈ car atomIndex, probe rowSlot
        = ∑ rowSlot : Fin n, if rowSlot ∈ car atomIndex then probe rowSlot else 0 := by
    intro atomIndex probe
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hdiagTotal : ∑ atomIndex : Fin 6, ∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot
      = 3 * Matrix.trace K := by
    rw [Finset.sum_congr rfl fun atomIndex _ => hexpand atomIndex _, Finset.sum_comm]
    have hcount : ∀ rowSlot : Fin n,
        ∑ atomIndex : Fin 6, (if rowSlot ∈ car atomIndex then K rowSlot rowSlot else 0)
          = 3 * K rowSlot rowSlot := by
      intro rowSlot
      rw [← Finset.sum_filter, Finset.sum_const, hinc rowSlot, nsmul_eq_mul]
      norm_num
    rw [Finset.sum_congr rfl fun rowSlot _ => hcount rowSlot, ← Finset.mul_sum]
    rfl
  have hminorTotal : ∑ rowSlot : Fin n, ∑ colSlot : Fin n,
      kernelMinor K rowSlot colSlot = 2 := by
    rw [kernelMinor_total hsymm hidem, htrace]
    norm_num
  have hweight : ∑ rowSlot : Fin n, ∑ colSlot : Fin n,
      kernelMinor K rowSlot colSlot
      ≤ ∑ atomIndex : Fin 6, ∑ rowSlot ∈ car atomIndex,
          ∑ colSlot ∈ car atomIndex, kernelMinor K rowSlot colSlot := by
    set ind : Fin 6 → Fin n → Fin n → ℝ := fun atomIndex rowSlot colSlot =>
      (if rowSlot ∈ car atomIndex then
        (if colSlot ∈ car atomIndex then kernelMinor K rowSlot colSlot else 0)
        else 0) with hind
    have hexpandTwo : ∀ atomIndex : Fin 6,
        ∑ rowSlot ∈ car atomIndex, ∑ colSlot ∈ car atomIndex,
            kernelMinor K rowSlot colSlot
          = ∑ rowSlot : Fin n, ∑ colSlot : Fin n, ind atomIndex rowSlot colSlot := by
      intro atomIndex
      rw [hexpand atomIndex]
      refine Finset.sum_congr rfl fun rowSlot _ => ?_
      by_cases hrow : rowSlot ∈ car atomIndex
      · simp only [hind, hrow, if_true]
        exact hexpand atomIndex _
      · simp [hind, hrow]
    have hswapAll : ∑ atomIndex : Fin 6, ∑ rowSlot : Fin n, ∑ colSlot : Fin n,
          ind atomIndex rowSlot colSlot
        = ∑ rowSlot : Fin n, ∑ colSlot : Fin n, ∑ atomIndex : Fin 6,
            ind atomIndex rowSlot colSlot := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun rowSlot _ => Finset.sum_comm
    have hterm : ∀ (atomIndex : Fin 6) (rowSlot colSlot : Fin n),
        0 ≤ ind atomIndex rowSlot colSlot := by
      intro atomIndex rowSlot colSlot
      by_cases hrow : rowSlot ∈ car atomIndex
      · by_cases hcol : colSlot ∈ car atomIndex
        · simp only [hind, hrow, hcol, if_true]
          exact kernelMinor_nonneg hsymm hidem rowSlot colSlot
        · simp [hind, hrow, hcol]
      · simp [hind, hrow]
    calc ∑ rowSlot : Fin n, ∑ colSlot : Fin n, kernelMinor K rowSlot colSlot
        ≤ ∑ rowSlot : Fin n, ∑ colSlot : Fin n, ∑ atomIndex : Fin 6,
            ind atomIndex rowSlot colSlot := by
          refine Finset.sum_le_sum fun rowSlot _ =>
            Finset.sum_le_sum fun colSlot _ => ?_
          rcases eq_or_ne rowSlot colSlot with rfl | hne
          · rw [kernelMinor_self]
            exact Finset.sum_nonneg fun atomIndex _ => hterm atomIndex rowSlot rowSlot
          · obtain ⟨witness, hrowMem, hcolMem⟩ := hco rowSlot colSlot hne
            have hle := Finset.single_le_sum
              (f := fun atomIndex : Fin 6 => ind atomIndex rowSlot colSlot)
              (fun atomIndex _ => hterm atomIndex rowSlot colSlot)
              (Finset.mem_univ witness)
            have hvalue : ind witness rowSlot colSlot
                = kernelMinor K rowSlot colSlot := by
              simp [hind, hrowMem, hcolMem]
            rwa [hvalue] at hle
      _ = ∑ atomIndex : Fin 6, ∑ rowSlot ∈ car atomIndex,
            ∑ colSlot ∈ car atomIndex, kernelMinor K rowSlot colSlot := by
          rw [← hswapAll]
          exact (Finset.sum_congr rfl fun atomIndex _ => hexpandTwo atomIndex).symm
  have hdefect : ∑ atomIndex : Fin 6,
      ((∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot) - readVal atomIndex)
      = 6 - ∑ atomIndex, readVal atomIndex := by
    rw [Finset.sum_sub_distrib, hdiagTotal, htrace]
    norm_num
  have hdefectNonneg : ∀ atomIndex : Fin 6,
      0 ≤ (∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot) - readVal atomIndex := by
    intro atomIndex
    have hminorNonneg : 0 ≤ ∑ rowSlot ∈ car atomIndex,
        ∑ colSlot ∈ car atomIndex, kernelMinor K rowSlot colSlot :=
      Finset.sum_nonneg fun rowSlot _ => Finset.sum_nonneg fun colSlot _ =>
        kernelMinor_nonneg hsymm hidem rowSlot colSlot
    rw [hcorner atomIndex] at hminorNonneg
    nlinarith [hpos atomIndex]
  have hupper : ∑ atomIndex : Fin 6, ∑ rowSlot ∈ car atomIndex,
      ∑ colSlot ∈ car atomIndex, kernelMinor K rowSlot colSlot
      ≤ 2 * (6 - ∑ atomIndex, readVal atomIndex) := by
    rw [Finset.sum_congr rfl fun atomIndex _ => hcorner atomIndex]
    have hbound : ∀ atomIndex : Fin 6,
        2 * readVal atomIndex
            * ((∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot) - readVal atomIndex)
          ≤ 2 * ((∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot)
              - readVal atomIndex) := by
      intro atomIndex
      nlinarith [hcap atomIndex, hdefectNonneg atomIndex]
    calc ∑ atomIndex : Fin 6, 2 * readVal atomIndex
          * ((∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot) - readVal atomIndex)
        ≤ ∑ atomIndex : Fin 6, 2 * ((∑ rowSlot ∈ car atomIndex, K rowSlot rowSlot)
            - readVal atomIndex) := Finset.sum_le_sum fun atomIndex _ => hbound atomIndex
      _ = 2 * (6 - ∑ atomIndex, readVal atomIndex) := by
          rw [← Finset.mul_sum, hdefect]
  rw [hminorTotal] at hweight
  linarith [hweight, hupper, hsum]

/-! ## Layer 4 — the datum kill on the kernel-trace-two stratum -/

/-- **THE DATUM KILL ON THE KERNEL-TRACE-TWO STRATUM.**  A diagonal-Gram
shared-private datum whose basis count is two above its coefficient
trace, and whose basis supports pairwise share an atom, dies.  The
statement covers the trace-two stratum at basis count four and the
trace-three stratum at basis count five together, with no carrier width
bound and no interiority. -/
theorem SharedPrivateData.false_of_kernel_trace_two {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (hgap : (data.basisCount : ℝ) = Matrix.trace data.coeff + 2)
    (hshare : ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      ∃ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
        ∧ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo)) :
    False := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsupp, hread, hnorm, hnz, _⟩ :=
    data.exists_kernel_read_frame hdiag
  set chartValue := chartObjective (chartPointOfDesign crux.design) with hchartValue
  set atomWeight := (chartPointOfDesign crux.design).weight with hatomWeight
  set car : Fin 6 → Finset (Fin data.basisCount) := fun atomIndex =>
    Finset.univ.filter fun slot =>
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)
    with hcarDef
  set kernelProj : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ :=
    1 - S with hkernelProj
  have hKsymm : kernelProjᵀ = kernelProj := by
    rw [hkernelProj, Matrix.transpose_sub, Matrix.transpose_one, hSsymm]
  have hKidem : kernelProj * kernelProj = kernelProj := by
    rw [hkernelProj, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hSidem]
    abel
  have hKtrace : Matrix.trace kernelProj = 2 := by
    rw [hkernelProj, Matrix.trace_sub, Matrix.trace_one, hStrace, Fintype.card_fin,
      hgap]
    ring
  have hcarMem : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      slot ∈ car atomIndex ↔
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
    intro atomIndex slot
    simp [hcarDef]
  have hinc : ∀ slot : Fin data.basisCount,
      (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex).card = 3 := by
    intro slot
    have hpred : (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex)
        = datumTightSupport data.tightDir (data.basisLabel slot) := by
      have hcongr : (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex)
          = Finset.univ.filter fun atomIndex =>
              atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) :=
        Finset.filter_congr fun atomIndex _ => by rw [hcarMem]
      rw [hcongr, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hpred]
    exact data.hthree slot
  have hsuppCar : ∀ atomIndex : Fin 6, ∀ slot ∉ car atomIndex,
      readVecs atomIndex slot = 0 := by
    intro atomIndex slot hslot
    exact hsupp atomIndex slot fun hmem => hslot ((hcarMem atomIndex slot).mpr hmem)
  have hmemActive : ∀ slot : Fin data.basisCount,
      data.basisLabel slot ∈ data.activeSet := by
    intro slot
    have h := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at h
    exact h.1
  have hreadCar : ∀ atomIndex : Fin 6, ∀ slot ∈ car atomIndex,
      (kernelProj *ᵥ readVecs atomIndex) slot
        = (1 - (chartValue + atomWeight atomIndex)) * readVecs atomIndex slot := by
    intro atomIndex slot hslot
    have hmemSubset : atomIndex ∈ data.activeSubset (data.basisLabel slot) :=
      datumTightSupport_subset data.hdata (hmemActive slot)
        ((hcarMem atomIndex slot).mp hslot)
    exact kernel_corner_read (hread atomIndex slot hmemSubset)
  have hvalueNeg : chartValue < 0 := data.hvalueNeg
  have hweightLe : ∀ atomIndex : Fin 6, atomWeight atomIndex ≤ 1 := by
    intro atomIndex
    have hsum := data.hdata.weight_sum_one
    have hle : atomWeight atomIndex ≤ ∑ probe, atomWeight probe :=
      Finset.single_le_sum (f := atomWeight)
        (fun probe _ => (data.hdata.weight_pos probe).le) (Finset.mem_univ atomIndex)
    rwa [hsum] at hle
  have hcapNonneg : ∀ atomIndex : Fin 6,
      0 ≤ chartValue + atomWeight atomIndex := fun atomIndex =>
    capture_diagonal_nonneg_of_isChartStationaryData data.hdata atomIndex
  have hreadPos : ∀ atomIndex : Fin 6,
      0 < 1 - (chartValue + atomWeight atomIndex) := by
    intro atomIndex
    have := hweightLe atomIndex
    linarith
  have hreadCap : ∀ atomIndex : Fin 6,
      1 - (chartValue + atomWeight atomIndex) ≤ 1 := by
    intro atomIndex
    have := hcapNonneg atomIndex
    linarith
  have hreadSum : 5 < ∑ atomIndex : Fin 6,
      (1 - (chartValue + atomWeight atomIndex)) := by
    have hexpand : ∑ atomIndex : Fin 6, (1 - (chartValue + atomWeight atomIndex))
        = 6 - (6 * chartValue + ∑ atomIndex, atomWeight atomIndex) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        nsmul_eq_mul]
      norm_num
    rw [hexpand, data.hdata.weight_sum_one]
    linarith
  have hco : ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      ∃ atomIndex, slotOne ∈ car atomIndex ∧ slotTwo ∈ car atomIndex := by
    intro slotOne slotTwo hne
    obtain ⟨atomIndex, hone, htwo⟩ := hshare slotOne slotTwo hne
    exact ⟨atomIndex, (hcarMem atomIndex slotOne).mpr hone,
      (hcarMem atomIndex slotTwo).mpr htwo⟩
  exact false_of_kernelMinor_budget_general hKsymm hKidem hKtrace car readVecs
    (fun atomIndex => 1 - (chartValue + atomWeight atomIndex)) hinc hsuppCar hnz
    hreadCar hreadPos hreadCap hco hreadSum

/-- The deficit kill at basis count five with no profile arithmetic: the
kernel gap is two by the trace and the basis count alone. -/
theorem SharedPrivateData.false_of_deficit_five_general {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (hfive : data.basisCount = 5)
    (htraceThree : Matrix.trace data.coeff = 3)
    (hshare : ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      ∃ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
        ∧ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo)) :
    False := by
  refine data.false_of_kernel_trace_two hdiag ?_ hshare
  rw [htraceThree]
  have hcast : (data.basisCount : ℝ) = 5 := by
    rw [hfive]
    norm_num
  rw [hcast]
  norm_num

/-! ## Layer 5 — the complementary support law and the sharper dispatch -/

/-- **THE COMPLEMENTARY SUPPORT LAW.**  Two three-atom supports that
share no atom of the six fill the six atoms.  Thus a split slot pair is
a complementary slot pair. -/
theorem union_eq_univ_of_disjoint_card_three {firstSet secondSet : Finset (Fin 6)}
    (hfirst : firstSet.card = 3) (hsecond : secondSet.card = 3)
    (hsplit : ∀ atomIndex ∈ firstSet, atomIndex ∉ secondSet) :
    ∀ atomIndex : Fin 6, atomIndex ∈ firstSet ∨ atomIndex ∈ secondSet := by
  classical
  have hdisjoint : Disjoint firstSet secondSet :=
    Finset.disjoint_left.mpr fun atomIndex hone => hsplit atomIndex hone
  have hcard : (firstSet ∪ secondSet).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisjoint, hfirst, hsecond]
  have huniv : firstSet ∪ secondSet = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [hcard, Fintype.card_fin]
  intro atomIndex
  have hmem : atomIndex ∈ firstSet ∪ secondSet := by
    rw [huniv]
    exact Finset.mem_univ atomIndex
  exact Finset.mem_union.mp hmem

/-- **THE COMPLEMENT RESIDUE.**  The trace-three deficit at basis count
five with two basis supports that together fill the six atoms.  The
complementary support law turns the split residue into this one. -/
def SharedPrivateDeficitComplementClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (gramDiag : Fin data.basisCount → ℝ),
    data.gram = Matrix.diagonal gramDiag →
    Matrix.trace data.coeff = 3 →
    data.basisCount = 5 →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      (∀ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) →
        atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slotTwo)) →
      (∀ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
        ∨ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo)) →
      False

/-- **THE SHARPER DEFICIT DISPATCH.**  The width-free kill leaves the
basis count six residue and the complementary support residue.  The
profile arithmetic pins the basis count to five or six, and the
complementary support law upgrades the split hypothesis. -/
theorem sharedPrivateDeficitClosed_of_complement_residues
    (hsix : SharedPrivateDeficitSixClosed)
    (hcomplement : SharedPrivateDeficitComplementClosed) :
    SharedPrivateDeficitClosed := by
  classical
  intro crux data gramDiag hdiag htraceThree hmass
  have hmultPos : ∀ atomIndex : Fin 6,
      1 ≤ basisSupportMultiplicity data.tightDir data.basisLabel atomIndex := by
    intro atomIndex
    obtain ⟨slot, hslot⟩ := exists_basisIndex_datumTightSupport data.hdata
      data.basisLabel data.hspan data.leftInv data.hleft atomIndex
    exact Finset.card_pos.mpr
      ⟨slot, Finset.mem_filter.mpr ⟨Finset.mem_univ slot, hslot⟩⟩
  have hmultTotal :
      ∑ atomIndex : Fin 6,
        basisSupportMultiplicity data.tightDir data.basisLabel atomIndex
        = 3 * data.basisCount := by
    rw [sum_basisSupportMultiplicity,
      Finset.sum_congr rfl fun slot _ => data.hthree slot, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hfloor := fifteen_le_sum_of_deficit hmultPos hmass
  rw [hmultTotal] at hfloor
  have hupper := data.basisCount_le_six
  by_cases hfive : data.basisCount = 5
  · by_cases hshare : ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      ∃ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
        ∧ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo)
    · exact data.false_of_deficit_five_general hdiag hfive htraceThree hshare
    · push Not at hshare
      obtain ⟨slotOne, slotTwo, hne, hdisjoint⟩ := hshare
      have hsplit : ∀ atomIndex : Fin 6,
          atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) →
          atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slotTwo) :=
        fun atomIndex hone htwo => hdisjoint atomIndex hone htwo
      exact hcomplement crux data gramDiag hdiag htraceThree hfive slotOne slotTwo
        hne hsplit (union_eq_univ_of_disjoint_card_three (data.hthree slotOne)
          (data.hthree slotTwo) hsplit)
  · exact hsix crux data gramDiag hdiag htraceThree (by omega) hmass

end Gtz
