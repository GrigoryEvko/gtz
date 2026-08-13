import Gtz.Wave.SharedPrivateComplementTrace
import Gtz.Wave.BothParallelTrichotomy
import Gtz.LinAlg.ProjectionForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The shared-private strata dispatch — the trace-split kill and the refined budget

The complement-trace calculus killed the interior of the shared-private
target.  Three strata stayed open: the `value + weight = 0` boundary,
the trace-three profiles with one pin, and the non-diagonal Gram cores.
This module closes the largest parts of the first two strata and names
the residues.

The trace-split kill.  At trace three, the capture trace against the
span projector of the basis columns equals the coefficient trace.  The
chart projection also has trace three.  Thus the projection factors
through the span projector, and the whole projection is supported on
the basis span.  At a boundary atom the capture row annihilates, thus
the projection column dies, and the diagonal vanishes below the
positive weight.  The all-heavy floor refuses.  As a result, the
trace-three data are interior with no more hypotheses, at basis counts
five and six together.

The corner cap.  A two-carrier atom reads an eigenvector of its
two-by-two corner.  The perpendicular vector is an eigenvector at the
complementary corner trace, and the idempotent window caps that
eigenvalue by one.  Thus the corner trace is at most one plus the read
value, at every read value.  The cap needs no interior window, and it
is one unit stronger than the generic carrier cap at trace three.

The refined budget.  The double count now runs with three atom
classes: the pins read exactly, the two-carrier atoms take the corner
cap, and only the atoms with three or more carriers need the interior
window.  At trace two, one pin kills.  At trace three, the kill needs
profile mass four: two units for each pin, one for each two-carrier
atom.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.pair_mulVec_apply`, `Gtz.pair_dotProduct` — the pair collapses.
* `Gtz.two_carrier_trace_cap` — **THE CORNER CAP.**
* `Gtz.carrier_budget_with_pairs` — **THE REFINED BUDGET.**
* `Gtz.false_of_refined_budget_trace_two`,
  `Gtz.false_of_refined_budget_trace_three` — the refined kills.
* `Gtz.SharedPrivateData.shifted_weight_pos_of_trace_three` — **THE
  TRACE-SPLIT KILL**: trace-three data are interior.
* `Gtz.SharedPrivateData.false_of_diagonal_gram_refined` — **THE
  REFINED DISCHARGE.**
* `Gtz.SharedPrivateBoundaryClosed`, `Gtz.SharedPrivateDeficitClosed`,
  `Gtz.SharedPrivateExtrasClosed` — **THE THREE RESIDUES.**
* `Gtz.sharedPrivateKilled_of_strata` — **THE STRATA DISPATCH.**
* `Gtz.rankFourSharedPrivateClosed_of_strata`,
  `Gtz.rankFiveSharedPrivateClosed_of_strata`,
  `Gtz.rankSixSharedPrivateClosed_of_strata` — the rung compositions.

## Vacuity

The matrix statements are unconditional.  The data-facing statements
quantify over shared-private data, and no datum exists if
`Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 2 — the pair collapses and the corner cap -/

/-- A matrix-vector entry collapses to the two support slots of the
vector. -/
theorem pair_mulVec_apply {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    {slotOne slotTwo : Fin n} (hne : slotOne ≠ slotTwo)
    {vec : Fin n → ℝ}
    (hsupp : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo → vec slot = 0)
    (rowIndex : Fin n) :
    (S *ᵥ vec) rowIndex
      = S rowIndex slotOne * vec slotOne
        + S rowIndex slotTwo * vec slotTwo := by
  rw [Matrix.mulVec, dotProduct]
  have hrestrict : ∑ slot, S rowIndex slot * vec slot
      = ∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin n)),
          S rowIndex slot * vec slot := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro slot _ hnot
    have h1 : slot ≠ slotOne := fun h => hnot (h ▸ Finset.mem_insert_self _ _)
    have h2 : slot ≠ slotTwo := fun h =>
      hnot (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [hsupp slot h1 h2, mul_zero]
  rw [hrestrict, Finset.sum_insert (by simp [hne]), Finset.sum_singleton]

/-- A dot product collapses to the two support slots of the left
vector. -/
theorem pair_dotProduct {n : ℕ} {slotOne slotTwo : Fin n}
    (hne : slotOne ≠ slotTwo) {vec : Fin n → ℝ}
    (hsupp : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo → vec slot = 0)
    (other : Fin n → ℝ) :
    vec ⬝ᵥ other
      = vec slotOne * other slotOne + vec slotTwo * other slotTwo := by
  rw [dotProduct]
  have hrestrict : ∑ slot, vec slot * other slot
      = ∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin n)),
          vec slot * other slot := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro slot _ hnot
    have h1 : slot ≠ slotOne := fun h => hnot (h ▸ Finset.mem_insert_self _ _)
    have h2 : slot ≠ slotTwo := fun h =>
      hnot (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [hsupp slot h1 h2, zero_mul]
  rw [hrestrict, Finset.sum_insert (by simp [hne]), Finset.sum_singleton]

/-- **THE CORNER CAP.**  A two-carrier read caps the corner diagonal
sum by one plus the read value.  The perpendicular probe is an
eigenvector of the corner at the complementary trace, and the
idempotent window caps it.  The cap holds at every read value, with no
interior window. -/
theorem two_carrier_trace_cap {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S)
    {slotOne slotTwo : Fin n} (hne : slotOne ≠ slotTwo)
    {readVec : Fin n → ℝ} {readVal : ℝ}
    (hsupp : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo → readVec slot = 0)
    (hreadOne : (S *ᵥ readVec) slotOne = readVal * readVec slotOne)
    (hreadTwo : (S *ᵥ readVec) slotTwo = readVal * readVec slotTwo)
    (hnz : readVec ≠ 0) :
    S slotOne slotOne + S slotTwo slotTwo ≤ 1 + readVal := by
  -- the entry form of the two reads
  have hSrOne : S slotOne slotOne * readVec slotOne
      + S slotOne slotTwo * readVec slotTwo = readVal * readVec slotOne := by
    have h := hreadOne
    rw [pair_mulVec_apply S hne hsupp slotOne] at h
    exact h
  have hSrTwo : S slotTwo slotOne * readVec slotOne
      + S slotTwo slotTwo * readVec slotTwo = readVal * readVec slotTwo := by
    have h := hreadTwo
    rw [pair_mulVec_apply S hne hsupp slotTwo] at h
    exact h
  -- the perpendicular probe on the pair
  set probe : Fin n → ℝ := fun slot =>
    if slot = slotOne then -(readVec slotTwo)
    else if slot = slotTwo then readVec slotOne else 0 with hprobe
  have hprobeSupp : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      probe slot = 0 := by
    intro slot h1 h2
    simp [hprobe, h1, h2]
  have hprobeOne : probe slotOne = -(readVec slotTwo) := by simp [hprobe]
  have hprobeTwo : probe slotTwo = readVec slotOne := by
    simp [hprobe, Ne.symm hne]
  -- the corner quadratic prices the complementary trace
  have hq : probe ⬝ᵥ (S *ᵥ probe)
      = (S slotOne slotOne + S slotTwo slotTwo - readVal)
        * (readVec slotOne * readVec slotOne
            + readVec slotTwo * readVec slotTwo) := by
    rw [pair_dotProduct hne hprobeSupp (S *ᵥ probe),
      pair_mulVec_apply S hne hprobeSupp slotOne,
      pair_mulVec_apply S hne hprobeSupp slotTwo,
      hprobeOne, hprobeTwo]
    linear_combination (-(readVec slotOne)) * hSrOne
      + (-(readVec slotTwo)) * hSrTwo
  -- the complementary idempotent window
  have hcomplSymm : (1 - S)ᵀ = 1 - S := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsymm]
  have hcomplIdem : (1 - S) * (1 - S) = 1 - S := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hidem]
    abel
  have hcompl := posSemidef_of_transpose_eq_of_idem hcomplSymm hcomplIdem
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hcompl).2 probe
  rw [star_trivial] at hform
  have hsplit : probe ⬝ᵥ ((1 - S) *ᵥ probe)
      = probe ⬝ᵥ probe - probe ⬝ᵥ (S *ᵥ probe) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
  have hself : probe ⬝ᵥ probe
      = readVec slotOne * readVec slotOne
        + readVec slotTwo * readVec slotTwo := by
    rw [pair_dotProduct hne hprobeSupp probe, hprobeOne, hprobeTwo]
    ring
  rw [hsplit, hself, hq] at hform
  -- the alive pair mass
  have hac : 0 < readVec slotOne * readVec slotOne
      + readVec slotTwo * readVec slotTwo := by
    obtain ⟨slot, hslot⟩ := Function.ne_iff.mp hnz
    have hslot' : readVec slot ≠ 0 := by simpa using hslot
    have hcase : slot = slotOne ∨ slot = slotTwo := by
      by_contra hnot
      push Not at hnot
      exact hslot' (hsupp slot hnot.1 hnot.2)
    rcases hcase with h | h
    · subst h
      nlinarith [mul_self_pos.mpr hslot',
        mul_self_nonneg (readVec slotTwo)]
    · subst h
      nlinarith [mul_self_pos.mpr hslot',
        mul_self_nonneg (readVec slotOne)]
  nlinarith [hform, hac]

/-! ## Layer 3 — the refined budget and the two kills -/

/-- **THE REFINED BUDGET.**  The double count with three atom classes:
the pins read exactly, the two-carrier atoms take the corner cap, and
only the remaining atoms need the interior window. -/
theorem carrier_budget_with_pairs {n m : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (car : Fin m → Finset (Fin n))
    (v : Fin m → Fin n → ℝ) (d : Fin m → ℝ) (blockCount : ℕ)
    (hinc : ∀ slot : Fin n,
      (Finset.univ.filter fun atom => slot ∈ car atom).card = blockCount)
    (hsupp : ∀ atom, ∀ slot ∉ car atom, v atom slot = 0)
    (hnz : ∀ atom, v atom ≠ 0)
    (hread : ∀ atom, ∀ slot ∈ car atom,
      (S *ᵥ v atom) slot = d atom * v atom slot)
    (pinSet pairSet : Finset (Fin m)) (hdisjoint : Disjoint pinSet pairSet)
    (hpin : ∀ atom ∈ pinSet, ∃ pinSlot, car atom = {pinSlot})
    (hpair : ∀ atom ∈ pairSet, ∃ slotOne slotTwo,
      slotOne ≠ slotTwo ∧ car atom = {slotOne, slotTwo})
    (hd0 : ∀ atom, atom ∉ pinSet → atom ∉ pairSet → 0 < d atom)
    (hd1 : ∀ atom, atom ∉ pinSet → atom ∉ pairSet → d atom < 1) :
    (blockCount : ℝ) * Matrix.trace S
      ≤ ((m : ℝ) - pinSet.card - pairSet.card) * (Matrix.trace S - 1)
        + pairSet.card + ∑ atom, d atom := by
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
  -- the pin equalities
  have hpineq : ∀ atom ∈ pinSet,
      (∑ slot ∈ car atom, S slot slot) = d atom := by
    intro atom hatom
    obtain ⟨pinSlot, hps⟩ := hpin atom hatom
    rw [hps, Finset.sum_singleton]
    exact pin_diag_eq_of_read (hsupp atom) (hread atom) (hnz atom) hps
  -- the corner caps
  have hpairle : ∀ atom ∈ pairSet,
      (∑ slot ∈ car atom, S slot slot) ≤ 1 + d atom := by
    intro atom hatom
    obtain ⟨slotOne, slotTwo, hneq, hps⟩ := hpair atom hatom
    have hsupp' : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        v atom slot = 0 := by
      intro slot h1 h2
      exact hsupp atom slot (by rw [hps]; simp [h1, h2])
    have hcap := two_carrier_trace_cap hsymm hidem hneq hsupp'
      (hread atom slotOne (by
        rw [hps]; exact Finset.mem_insert_self _ _))
      (hread atom slotTwo (by
        rw [hps]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      (hnz atom)
    rw [hps, Finset.sum_pair hneq]
    exact hcap
  -- the interior caps
  have hrestle : ∀ atom, atom ∉ pinSet → atom ∉ pairSet →
      (∑ slot ∈ car atom, S slot slot)
        ≤ Matrix.trace S - 1 + d atom := by
    intro atom hnotPin hnotPair
    exact carrier_diag_cap_of_read hsymm hidem (hsupp atom) (hread atom)
      (hnz atom) (hd0 atom hnotPin hnotPair) (hd1 atom hnotPin hnotPair)
  -- assemble the three classes
  have hsplitS := Finset.sum_add_sum_compl (pinSet ∪ pairSet)
    (fun atom => ∑ slot ∈ car atom, S slot slot)
  have hsplitd := Finset.sum_add_sum_compl (pinSet ∪ pairSet) d
  have hunionS : ∑ atom ∈ pinSet ∪ pairSet, (∑ slot ∈ car atom, S slot slot)
      = ∑ atom ∈ pinSet, (∑ slot ∈ car atom, S slot slot)
        + ∑ atom ∈ pairSet, (∑ slot ∈ car atom, S slot slot) :=
    Finset.sum_union hdisjoint
  have huniond : ∑ atom ∈ pinSet ∪ pairSet, d atom
      = ∑ atom ∈ pinSet, d atom + ∑ atom ∈ pairSet, d atom :=
    Finset.sum_union hdisjoint
  have hpinsum : ∑ atom ∈ pinSet, (∑ slot ∈ car atom, S slot slot)
      = ∑ atom ∈ pinSet, d atom :=
    Finset.sum_congr rfl hpineq
  have hpairsum : ∑ atom ∈ pairSet, (∑ slot ∈ car atom, S slot slot)
      ≤ ∑ atom ∈ pairSet, (1 + d atom) :=
    Finset.sum_le_sum hpairle
  have hpairexpand : ∑ atom ∈ pairSet, (1 + d atom)
      = (pairSet.card : ℝ) + ∑ atom ∈ pairSet, d atom := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hrestsum : ∑ atom ∈ (pinSet ∪ pairSet)ᶜ,
      (∑ slot ∈ car atom, S slot slot)
      ≤ ∑ atom ∈ (pinSet ∪ pairSet)ᶜ, (Matrix.trace S - 1 + d atom) := by
    refine Finset.sum_le_sum fun atom hatom => ?_
    have hmem := Finset.mem_compl.mp hatom
    rw [Finset.mem_union] at hmem
    push Not at hmem
    exact hrestle atom hmem.1 hmem.2
  have hrestexpand : ∑ atom ∈ (pinSet ∪ pairSet)ᶜ,
      (Matrix.trace S - 1 + d atom)
      = (((pinSet ∪ pairSet)ᶜ.card : ℕ) : ℝ) * (Matrix.trace S - 1)
        + ∑ atom ∈ (pinSet ∪ pairSet)ᶜ, d atom := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hcardle : pinSet.card + pairSet.card ≤ m := by
    rw [← Finset.card_union_of_disjoint hdisjoint]
    simpa [Fintype.card_fin] using Finset.card_le_univ (pinSet ∪ pairSet)
  have hcardcompl : (((pinSet ∪ pairSet)ᶜ.card : ℕ) : ℝ)
      = (m : ℝ) - pinSet.card - pairSet.card := by
    rw [Finset.card_compl, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisjoint, Nat.cast_sub hcardle,
      Nat.cast_add]
    ring
  rw [hcardcompl] at hrestexpand
  linarith

/-- **THE TRACE-TWO REFINED KILL.**  Six atoms with three atoms in each
block, a trace-two symmetric idempotent, a shifted weight sum
`6 * value + 1` at a negative value, and one pin: the interior window
is only needed at the atoms with three or more carriers. -/
theorem false_of_refined_budget_trace_two {n : ℕ}
    {S : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (htrace : Matrix.trace S = 2)
    (car : Fin 6 → Finset (Fin n)) (v : Fin 6 → Fin n → ℝ)
    (d : Fin 6 → ℝ) {value : ℝ}
    (hinc : ∀ slot : Fin n,
      (Finset.univ.filter fun atom => slot ∈ car atom).card = 3)
    (hsupp : ∀ atom, ∀ slot ∉ car atom, v atom slot = 0)
    (hnz : ∀ atom, v atom ≠ 0)
    (hread : ∀ atom, ∀ slot ∈ car atom,
      (S *ᵥ v atom) slot = d atom * v atom slot)
    (pinSet pairSet : Finset (Fin 6)) (hdisjoint : Disjoint pinSet pairSet)
    (hpin : ∀ atom ∈ pinSet, ∃ pinSlot, car atom = {pinSlot})
    (hpair : ∀ atom ∈ pairSet, ∃ slotOne slotTwo,
      slotOne ≠ slotTwo ∧ car atom = {slotOne, slotTwo})
    (hd0 : ∀ atom, atom ∉ pinSet → atom ∉ pairSet → 0 < d atom)
    (hd1 : ∀ atom, atom ∉ pinSet → atom ∉ pairSet → d atom < 1)
    (hsum : ∑ atom, d atom = 6 * value + 1) (hneg : value < 0)
    (hpinCard : 1 ≤ pinSet.card) : False := by
  have hbudget := carrier_budget_with_pairs hsymm hidem car v d 3 hinc
    hsupp hnz hread pinSet pairSet hdisjoint hpin hpair hd0 hd1
  rw [htrace, hsum] at hbudget
  have hp1 : (1 : ℝ) ≤ pinSet.card := by exact_mod_cast hpinCard
  have hp2 : (0 : ℝ) ≤ pairSet.card := Nat.cast_nonneg _
  norm_num at hbudget
  linarith

/-- **THE TRACE-THREE REFINED KILL.**  The same shape with a
trace-three idempotent dies at profile mass four: two units for each
pin and one for each two-carrier atom. -/
theorem false_of_refined_budget_trace_three {n : ℕ}
    {S : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (htrace : Matrix.trace S = 3)
    (car : Fin 6 → Finset (Fin n)) (v : Fin 6 → Fin n → ℝ)
    (d : Fin 6 → ℝ) {value : ℝ}
    (hinc : ∀ slot : Fin n,
      (Finset.univ.filter fun atom => slot ∈ car atom).card = 3)
    (hsupp : ∀ atom, ∀ slot ∉ car atom, v atom slot = 0)
    (hnz : ∀ atom, v atom ≠ 0)
    (hread : ∀ atom, ∀ slot ∈ car atom,
      (S *ᵥ v atom) slot = d atom * v atom slot)
    (pinSet pairSet : Finset (Fin 6)) (hdisjoint : Disjoint pinSet pairSet)
    (hpin : ∀ atom ∈ pinSet, ∃ pinSlot, car atom = {pinSlot})
    (hpair : ∀ atom ∈ pairSet, ∃ slotOne slotTwo,
      slotOne ≠ slotTwo ∧ car atom = {slotOne, slotTwo})
    (hd0 : ∀ atom, atom ∉ pinSet → atom ∉ pairSet → 0 < d atom)
    (hd1 : ∀ atom, atom ∉ pinSet → atom ∉ pairSet → d atom < 1)
    (hsum : ∑ atom, d atom = 6 * value + 1) (hneg : value < 0)
    (hprofile : 4 ≤ 2 * pinSet.card + pairSet.card) : False := by
  have hbudget := carrier_budget_with_pairs hsymm hidem car v d 3 hinc
    hsupp hnz hread pinSet pairSet hdisjoint hpin hpair hd0 hd1
  rw [htrace, hsum] at hbudget
  have hp : (4 : ℝ) ≤ 2 * pinSet.card + pairSet.card := by
    exact_mod_cast hprofile
  norm_num at hbudget
  linarith

/-! ## Layer 4 — the trace-split kill -/

set_option maxHeartbeats 1600000 in
/-- **THE TRACE-SPLIT KILL.**  At trace three, every shifted weight of
a shared-private datum is positive.  The capture trace against the span
projector equals the coefficient trace, and the chart projection also
has trace three.  Thus the projection factors through the span
projector.  At a boundary atom the capture row annihilates, the
projection column dies, and the vanished diagonal contradicts the
all-heavy floor. -/
theorem SharedPrivateData.shifted_weight_pos_of_trace_three
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    (htrace : Matrix.trace data.coeff = 3) (atomIndex : Fin 6) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex := by
  rcases (capture_diagonal_nonneg_of_isChartStationaryData data.hdata
    atomIndex).lt_or_eq with hpos | heq
  · exact hpos
  exfalso
  classical
  set B := tightBasisColumns data.tightDir data.basisLabel with hB
  set P := (chartPointOfDesign crux.design).chart with hP
  set N := Bᵀ * B with hN
  -- the annihilated capture row at the boundary atom
  have hrow : ∀ columnIndex, (B * data.coeff) atomIndex columnIndex = 0 :=
    fun columnIndex => basis_capture_column_zero_of_diagonal_zero data.hdata
      data.hspan data.hrepresentation heq.symm columnIndex
  -- the projection laws through the definitional bridge
  have hrep : P * B = B * data.coeff := data.hrepresentation
  have hPsymm : Pᵀ = P := data.hdata.isSymmetric
  have hidem : P * P = P := projectionOfDesign_mul_self crux.design
  have hPtrace : Matrix.trace P = 3 := by
    have h : Matrix.trace (projectionOfDesign crux.design)
        = ((3 : ℕ) : ℝ) := trace_projectionOfDesign crux.design
    norm_num at h
    exact h
  -- the column Gram is kernel-free, thus invertible
  have hkerB : ∀ vec : Fin data.basisCount → ℝ, B *ᵥ vec = 0 → vec = 0 := by
    intro vec hzero
    have hrecover : data.leftInv *ᵥ (B *ᵥ vec) = vec := by
      rw [Matrix.mulVec_mulVec, data.hleft, Matrix.one_mulVec]
    rw [← hrecover, hzero, Matrix.mulVec_zero]
  have hkerN : ∀ vec : Fin data.basisCount → ℝ, N *ᵥ vec = 0 → vec = 0 := by
    intro vec hzero
    have hquadForm : vec ⬝ᵥ (N *ᵥ vec)
        = (B *ᵥ vec) ⬝ᵥ (B *ᵥ vec) := by
      rw [hN, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose]
    rw [hzero, dotProduct_zero] at hquadForm
    have hBv : B *ᵥ vec = 0 := by
      funext rowIndex
      have hquad := hquadForm.symm
      rw [dotProduct] at hquad
      have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        mul_self_nonneg ((B *ᵥ vec) i)).mp hquad rowIndex
        (Finset.mem_univ rowIndex)
      simpa using mul_self_eq_zero.mp hall
    exact hkerB vec hBv
  have hdetN : IsUnit N.det := by
    rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨vec, hvne, hvzero⟩ :=
      (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
    exact hvne (hkerN vec hvzero)
  have hNiN : N⁻¹ * N = 1 := Matrix.nonsing_inv_mul N hdetN
  -- the span projector of the basis columns
  set spanProj := B * N⁻¹ * Bᵀ with hspanDef
  have hNsymm : Nᵀ = N := by
    rw [hN, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hNinvSymm : (N⁻¹)ᵀ = N⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hNsymm]
  have hspanSymm : spanProjᵀ = spanProj := by
    rw [hspanDef, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hNinvSymm, ← Matrix.mul_assoc]
  have hspanIdem : spanProj * spanProj = spanProj := by
    rw [hspanDef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᵀ B, ← hN, ← Matrix.mul_assoc N⁻¹ N, hNiN,
      Matrix.one_mul]
  -- the capture trace equals the coefficient trace
  have hPPi : P * spanProj = B * (data.coeff * (N⁻¹ * Bᵀ)) := by
    rw [hspanDef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P B, hrep, Matrix.mul_assoc]
  have htracePPi : Matrix.trace (P * spanProj)
      = Matrix.trace data.coeff := by
    rw [hPPi, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
    rw [← hN, hNiN, Matrix.mul_one]
  -- the projection factors through the span projector
  have hexpand : (P - spanProj * P) * (P - P * spanProj)
      = P - P * spanProj - (spanProj * P - spanProj * (P * spanProj)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    rw [hidem, ← Matrix.mul_assoc P P spanProj, hidem,
      Matrix.mul_assoc spanProj P P, hidem,
      Matrix.mul_assoc spanProj P (P * spanProj),
      ← Matrix.mul_assoc P P spanProj, hidem]
    abel
  have hfactor : P * spanProj = P := by
    have hzero : P - P * spanProj = 0 := by
      apply eq_zero_of_trace_transpose_mul_self
      have hT : (P - P * spanProj)ᵀ = P - spanProj * P := by
        rw [Matrix.transpose_sub, Matrix.transpose_mul, hspanSymm, hPsymm]
      rw [hT, hexpand, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub]
      have h1 : Matrix.trace (spanProj * P)
          = Matrix.trace (P * spanProj) := Matrix.trace_mul_comm spanProj P
      have h2 : Matrix.trace (spanProj * (P * spanProj))
          = Matrix.trace (P * spanProj) := by
        rw [Matrix.trace_mul_comm, Matrix.mul_assoc, hspanIdem]
      rw [h1, h2, htracePPi, htrace, hPtrace]
      norm_num
    exact (sub_eq_zero.mp hzero).symm
  have hfactorT : spanProj * P = P := by
    have h := congrArg Matrix.transpose hfactor
    rwa [Matrix.transpose_mul, hspanSymm, hPsymm] at h
  -- the projected axis dies at the boundary atom
  have hBt : Bᵀ *ᵥ (P *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)) = 0 := by
    have hBtP : Bᵀ * P = (B * data.coeff)ᵀ := by
      rw [← hrep, Matrix.transpose_mul, hPsymm]
    rw [Matrix.mulVec_mulVec, hBtP]
    funext columnIndex
    have happly : ((B * data.coeff)ᵀ
        *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)) columnIndex
        = (B * data.coeff) atomIndex columnIndex := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply,
        Matrix.transpose_apply, mul_ite, mul_one, mul_zero]
    rw [happly, hrow columnIndex]
    rfl
  have hcol : P *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ) = 0 := by
    have hfix : P *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)
        = spanProj *ᵥ (P *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)) := by
      rw [Matrix.mulVec_mulVec, hfactorT]
    rw [hfix, hspanDef, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hBt, Matrix.mulVec_zero, Matrix.mulVec_zero]
  -- the vanished diagonal against the all-heavy floor
  have hdiagzero : P atomIndex atomIndex = 0 := by
    have happly : (P *ᵥ (Pi.single atomIndex 1 : Fin 6 → ℝ)) atomIndex
        = P atomIndex atomIndex := by
      rw [Matrix.mulVec_single_one]
      simp [Matrix.col]
    rw [← happly, hcol]
    rfl
  have hgap := crux.chartGap_diagonal_pos atomIndex
  simp only [chartStationaryGap, Matrix.sub_apply,
    Matrix.diagonal_apply_eq] at hgap
  rw [← hP, hdiagzero] at hgap
  have hweight := data.hdata.weight_pos atomIndex
  linarith

/-! ## Layer 5 — the refined diagonal-Gram discharge -/

set_option maxHeartbeats 3200000 in
/-- **THE REFINED DISCHARGE.**  A shared-private datum with a diagonal
Gram core dies under two residual obligations.  At trace two, the
interior window is needed only at the atoms with three or more
carriers.  At trace three, the interior window is derived from the
trace-split kill, and the kill needs profile mass four from the pins
and the two-carrier atoms. -/
theorem SharedPrivateData.false_of_diagonal_gram_refined
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htwoBoundary : Matrix.trace data.coeff = 2 →
      ∀ atomIndex : Fin 6,
        3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
          atomIndex →
        0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
    (hthreeProfile : Matrix.trace data.coeff = 3 →
      4 ≤ 2 * (Finset.univ.filter fun atomIndex =>
            basisSupportMultiplicity data.tightDir data.basisLabel
              atomIndex = 1).card
        + (Finset.univ.filter fun atomIndex =>
            basisSupportMultiplicity data.tightDir data.basisLabel
              atomIndex = 2).card) :
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
      = shifted atomIndex
        * data.tightDir (data.basisLabel slot) atomIndex := by
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
        * (shifted atomIndex
            * data.tightDir (data.basisLabel slot) atomIndex)
      = shifted atomIndex
        * (sq slot * data.tightDir (data.basisLabel slot) atomIndex)
    rw [hsimp]
    ring
  -- the incidence count
  have hinc : ∀ slot : Fin data.basisCount,
      (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex).card
        = 3 := by
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
  -- the shifted window from above
  have hd1 : ∀ atomIndex, shifted atomIndex < 1 := by
    intro atomIndex
    have hwle : atomWeight atomIndex ≤ 1 := by
      have hsum := data.hdata.weight_sum_one
      have hle : atomWeight atomIndex ≤ ∑ y, atomWeight y :=
        Finset.single_le_sum (f := atomWeight)
          (fun y _ => (data.hdata.weight_pos y).le)
          (Finset.mem_univ atomIndex)
      rwa [hsum] at hle
    have : shifted atomIndex = chartValue + atomWeight atomIndex := rfl
    rw [this]
    linarith
  have hsum : ∑ atomIndex, shifted atomIndex = 6 * chartValue + 1 := by
    have hexpand : ∑ atomIndex : Fin 6, shifted atomIndex
        = ∑ atomIndex : Fin 6, (chartValue + atomWeight atomIndex) := rfl
    rw [hexpand, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, data.hdata.weight_sum_one,
      nsmul_eq_mul]
    norm_num
  -- the carrier multiplicity bridge
  have hcarCard : ∀ atomIndex, (car atomIndex).card
      = basisSupportMultiplicity data.tightDir data.basisLabel atomIndex :=
    fun _ => rfl
  -- the three atom classes
  set pinSet := Finset.univ.filter fun atomIndex =>
    basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1
    with hpinSetDef
  set pairSet := Finset.univ.filter fun atomIndex =>
    basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 2
    with hpairSetDef
  have hdisjoint : Disjoint pinSet pairSet := by
    refine Finset.disjoint_left.mpr fun atomIndex h1 h2 => ?_
    have hm1 := (Finset.mem_filter.mp h1).2
    have hm2 := (Finset.mem_filter.mp h2).2
    omega
  have hpin : ∀ atomIndex ∈ pinSet, ∃ pinSlot, car atomIndex = {pinSlot} := by
    intro atomIndex hmem
    have h := (Finset.mem_filter.mp hmem).2
    exact Finset.card_eq_one.mp ((hcarCard atomIndex).trans h)
  have hpair : ∀ atomIndex ∈ pairSet, ∃ slotOne slotTwo,
      slotOne ≠ slotTwo ∧ car atomIndex = {slotOne, slotTwo} := by
    intro atomIndex hmem
    have h := (Finset.mem_filter.mp hmem).2
    exact Finset.card_eq_two.mp ((hcarCard atomIndex).trans h)
  have hmultPos : ∀ atomIndex,
      0 < basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex := by
    intro atomIndex
    obtain ⟨slot, hslot⟩ := exists_basisIndex_datumTightSupport data.hdata
      data.basisLabel data.hspan data.leftInv data.hleft atomIndex
    exact Finset.card_pos.mpr
      ⟨slot, Finset.mem_filter.mpr ⟨Finset.mem_univ slot, hslot⟩⟩
  have hrestMult : ∀ atomIndex, atomIndex ∉ pinSet → atomIndex ∉ pairSet →
      3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex := by
    intro atomIndex hnotPin hnotPair
    have h1 : basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex ≠ 1 := fun h =>
      hnotPin (Finset.mem_filter.mpr ⟨Finset.mem_univ atomIndex, h⟩)
    have h2 : basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex ≠ 2 := fun h =>
      hnotPair (Finset.mem_filter.mpr ⟨Finset.mem_univ atomIndex, h⟩)
    have h0 := hmultPos atomIndex
    omega
  have hpinMem : data.pinAtom ∈ pinSet :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ data.pinAtom, data.hmultOne⟩
  have hpinCard : 1 ≤ pinSet.card :=
    Finset.one_le_card.mpr ⟨data.pinAtom, hpinMem⟩
  -- dispatch on the trace
  rcases data.htrace with htrace2 | htrace3
  · have hStrace2 : Matrix.trace S = 2 := by rw [hStrace, htrace2]
    have hd0 : ∀ atomIndex, atomIndex ∉ pinSet → atomIndex ∉ pairSet →
        0 < shifted atomIndex := fun atomIndex hnotPin hnotPair =>
      htwoBoundary htrace2 atomIndex (hrestMult atomIndex hnotPin hnotPair)
    exact false_of_refined_budget_trace_two hSsymm hSidem hStrace2 car
      readVecs shifted hinc hsupp hnz hread pinSet pairSet hdisjoint hpin
      hpair hd0 (fun atomIndex _ _ => hd1 atomIndex) hsum hneg hpinCard
  · have hStrace3 : Matrix.trace S = 3 := by rw [hStrace, htrace3]
    have hd0 : ∀ atomIndex, atomIndex ∉ pinSet → atomIndex ∉ pairSet →
        0 < shifted atomIndex := fun atomIndex _ _ =>
      data.shifted_weight_pos_of_trace_three htrace3 atomIndex
    exact false_of_refined_budget_trace_three hSsymm hSidem hStrace3 car
      readVecs shifted hinc hsupp hnz hread pinSet pairSet hdisjoint hpin
      hpair hd0 (fun atomIndex _ _ => hd1 atomIndex) hsum hneg
      (hthreeProfile htrace3)

/-! ## Layer 6 — the three residues and the strata dispatch -/

/-- **RESIDUE ONE, THE TRACE-TWO BOUNDARY.**  A diagonal-Gram
shared-private datum at trace two with an atom of three or more
carriers at the shifted-weight boundary dies. -/
def SharedPrivateBoundaryClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (gramDiag : Fin data.basisCount → ℝ),
    data.gram = Matrix.diagonal gramDiag →
    Matrix.trace data.coeff = 2 →
    ∀ atomIndex : Fin 6,
      3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0 →
      False

/-- **RESIDUE TWO, THE TRACE-THREE DEFICIT.**  A diagonal-Gram
shared-private datum at trace three with profile mass at most three
dies.  The mass counts two units for each multiplicity-one atom and
one for each multiplicity-two atom. -/
def SharedPrivateDeficitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (gramDiag : Fin data.basisCount → ℝ),
    data.gram = Matrix.diagonal gramDiag →
    Matrix.trace data.coeff = 3 →
    2 * (Finset.univ.filter fun atomIndex =>
          basisSupportMultiplicity data.tightDir data.basisLabel
            atomIndex = 1).card
      + (Finset.univ.filter fun atomIndex =>
          basisSupportMultiplicity data.tightDir data.basisLabel
            atomIndex = 2).card ≤ 3 →
    False

/-- **RESIDUE THREE, THE EXTRAS.**  A shared-private datum with a
non-diagonal Gram core dies.  The Gram sum makes the core diagonal
when every positive label is a basis label, thus this residue is the
extra-label stratum. -/
def SharedPrivateExtrasClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux),
    (∀ gramDiag : Fin data.basisCount → ℝ,
      data.gram ≠ Matrix.diagonal gramDiag) →
    False

/-- **THE STRATA DISPATCH.**  The three residues close the generic
shared-private kill.  The diagonal case splits on the trace: the
refined discharge consumes the boundary residue at trace two and the
deficit residue at trace three, and the trace-split kill supplies the
trace-three interior window. -/
theorem sharedPrivateKilled_of_strata
    (hextras : SharedPrivateExtrasClosed)
    (hboundary : SharedPrivateBoundaryClosed)
    (hdeficit : SharedPrivateDeficitClosed) :
    SharedPrivateKilled := by
  intro crux data
  classical
  by_cases hdiag : ∃ gramDiag : Fin data.basisCount → ℝ,
    data.gram = Matrix.diagonal gramDiag
  · obtain ⟨gramDiag, hg⟩ := hdiag
    refine data.false_of_diagonal_gram_refined hg ?_ ?_
    · intro htrace2 atomIndex hmult
      rcases (capture_diagonal_nonneg_of_isChartStationaryData data.hdata
        atomIndex).lt_or_eq with hpos | heq
      · exact hpos
      · exact absurd heq.symm fun hzero =>
          hboundary crux data gramDiag hg htrace2 atomIndex hmult hzero
    · intro htrace3
      by_contra hnot
      exact hdeficit crux data gramDiag hg htrace3 (by omega)
  · push Not at hdiag
    exact hextras crux data hdiag

/-! ## Layer 7 — the rung compositions -/

/-- The three residues discharge closure two of the rank-four rung. -/
theorem rankFourSharedPrivateClosed_of_strata
    (hextras : SharedPrivateExtrasClosed)
    (hboundary : SharedPrivateBoundaryClosed)
    (hdeficit : SharedPrivateDeficitClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_strata hextras hboundary hdeficit)

/-- The three residues discharge the shared-private closure of the
rank-five rung. -/
theorem rankFiveSharedPrivateClosed_of_strata
    (hextras : SharedPrivateExtrasClosed)
    (hboundary : SharedPrivateBoundaryClosed)
    (hdeficit : SharedPrivateDeficitClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_strata hextras hboundary hdeficit)

/-- The three residues discharge the shared-private closure of the
rank-six rung. -/
theorem rankSixSharedPrivateClosed_of_strata
    (hextras : SharedPrivateExtrasClosed)
    (hboundary : SharedPrivateBoundaryClosed)
    (hdeficit : SharedPrivateDeficitClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_strata hextras hboundary hdeficit)

end Gtz
