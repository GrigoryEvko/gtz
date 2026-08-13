import Gtz.Wave.DenseCeilingCollapse

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The plane witness ledger — the dual form of the plane pair residue

The plane pair residue asks for a DOMINATING PAIR among six plane atoms.
This module replaces that search by a DUAL certificate, and the exchange
removes every trace of combinatorics.

A plane witness is a quadratic form on the plane, written as a bulk term
plus a weighted family of squared readings.  The master law says that the
total gap energy of a plane frame never exceeds the budget of the
witness, and the law needs NO sign condition, NO eigenvalue, NO Loewner
order and NO spectral theorem.  Two sums carry the whole proof: the frame
law at each witness direction, and the trace law of the plane frame.

The trace law is new and unconditional: the atoms of a plane frame carry
total energy exactly two.  It comes from the frame law applied at the
three shadows of the coordinate directions.

The ledger then supplies four unconditional witnesses.  Each closes one
stratum of the plane residue outright:

* the ZERO-SCALE witness — one atom of vanishing scale, and the pair
  hypothesis IS the domination.  This is the sharp case: the probe
  measures the extremal distance exactly one there
* the LIGHT witness — every gap at most half its energy, and the bulk
  term alone dominates
* the HEAVY witness — one atom above the half line whose ratio law caps
  every other atom
* the CONIC witness — a positive combination of the atom directions
  themselves, priced by the pair hypothesis.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.plane_total_energy_eq_two` — **THE TRACE LAW OF A PLANE FRAME.**
* `Gtz.plane_witness_energy_total` — **THE MASTER IDENTITY.**  The total
  witness energy of a plane frame is the witness budget.
* `Gtz.plane_witness_total_le_one`, `Gtz.false_of_plane_witness` — the
  master law and the kill.
* `Gtz.exists_plane_pair_of_witness` — the dual certificate produces a
  dominating pair.
* `Gtz.plane_atom_weight_dominates` — the pair hypothesis priced on an
  atom-supported witness.
* `Gtz.exists_plane_pair_of_zero_scale` — **THE ZERO-SCALE STRATUM.**
* `Gtz.exists_plane_pair_of_light` — **THE LIGHT STRATUM.**
* `Gtz.exists_plane_pair_of_heavy` — **THE HEAVY STRATUM.**
* `Gtz.exists_plane_pair_of_conic` — **THE CONIC STRATUM.**
* `Gtz.frame_total_energy_eq_rank`, `Gtz.frame_witness_energy_total`,
  `Gtz.false_of_frame_witness` — **THE ENGINE AT GENERAL RANK.**  The
  budget of the kill is one less than the rank.
* `Gtz.false_of_zero_scale_frame` — **THE ZERO-SCALE DEFLATION AT
  GENERAL RANK**, the rank-three form of the sharp plane case.
* `Gtz.AtomPlaneWitnessClosed`, `Gtz.atomPairGramClosed_of_planeWitness`
  — **THE RESIDUE IN DUAL FORM**, with seven real unknowns and no
  combinatorics.
* `Gtz.atomPairCeilingClosed_of_planeWitness`,
  `Gtz.rankFiveDenseHeavyFiveClosed_of_planeWitness`,
  `Gtz.rankFiveDenseHeavyFiveDistinctClosed_of_planeWitness`,
  `Gtz.forall_shifted_weight_pos_of_planeWitness`,
  `Gtz.SixThreeCrux.shifted_weight_pos_of_planeWitness` — the campaign
  consequences, from the dual residue alone.
-/

namespace Gtz

open scoped BigOperators

/-! ## Layer 1 — the coordinate directions and the trace law of a plane frame -/

/-- The coordinate direction of one index. -/
def unitVector {dimension : ℕ} (index : Fin dimension) : Fin dimension → ℝ :=
  fun other => if other = index then 1 else 0

theorem unitVector_dot {dimension : ℕ} (index : Fin dimension) (vec : Fin dimension → ℝ) :
    unitVector index ⬝ᵥ vec = vec index := by
  simp [unitVector, dotProduct]

theorem unitVector_dot_self {dimension : ℕ} (index : Fin dimension) :
    unitVector index ⬝ᵥ unitVector index = 1 := by
  rw [unitVector_dot]
  simp [unitVector]

/-- The energy of a vector is the total of its squared coordinates. -/
theorem dot_self_eq_sum_sq {dimension : ℕ} (vec : Fin dimension → ℝ) :
    vec ⬝ᵥ vec = ∑ index, vec index ^ 2 := by
  rw [dotProduct]
  exact Finset.sum_congr rfl fun index _ => (sq (vec index)).symm

/-- **THE TRACE LAW OF A PLANE FRAME.**  Atoms that lie in the plane
orthogonal to an axis and form a tight frame of that plane carry total
energy exactly two.

The proof reads the frame law at the shadow of each coordinate
direction.  The shadow lies in the plane, an atom reads it as the plain
coordinate, and the three shadow energies total two. -/
theorem plane_total_energy_eq_two {slotCount : ℕ} (atom : Fin slotCount → (Fin 3 → ℝ))
    (axis : Fin 3 → ℝ) (haxis : (0 : ℝ) < axis ⬝ᵥ axis)
    (hplane : ∀ slot, atom slot ⬝ᵥ axis = 0)
    (hframe : ∀ probe direction : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → direction ⬝ᵥ axis = 0 →
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ slot, atom slot ⬝ᵥ atom slot) = 2 := by
  classical
  have hne : axis ⬝ᵥ axis ≠ 0 := ne_of_gt haxis
  have hread : ∀ (slot : Fin slotCount) (index : Fin 3),
      atom slot ⬝ᵥ planeShadow axis (unitVector index) = atom slot index := by
    intro slot index
    rw [dotProduct_comm,
      planeShadow_dot_plane axis (unitVector index) (atom slot) (hplane slot), unitVector_dot]
  have hshadowEnergy : ∀ index : Fin 3,
      planeShadow axis (unitVector index) ⬝ᵥ planeShadow axis (unitVector index)
        = 1 - axis index ^ 2 / (axis ⬝ᵥ axis) := by
    intro index
    rw [planeShadow_eq, dot_sub_smul_self, unitVector_dot_self, unitVector_dot]
    field_simp
    ring
  have hcolumn : ∀ index : Fin 3,
      (∑ slot, atom slot index ^ 2) = 1 - axis index ^ 2 / (axis ⬝ᵥ axis) := by
    intro index
    have hkey := hframe (planeShadow axis (unitVector index)) (planeShadow axis (unitVector index))
      (planeShadow_dot_axis axis (unitVector index) hne)
      (planeShadow_dot_axis axis (unitVector index) hne)
    rw [hshadowEnergy index] at hkey
    rw [← hkey]
    exact Finset.sum_congr rfl fun slot _ => by rw [hread slot index, sq]
  have hswap : (∑ slot, atom slot ⬝ᵥ atom slot) = ∑ index : Fin 3, ∑ slot, atom slot index ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun slot _ => dot_self_eq_sum_sq (atom slot)
  rw [hswap, Finset.sum_congr rfl fun index _ => hcolumn index, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← dot_self_eq_sum_sq]
  rw [div_self hne]
  norm_num

/-! ## Layer 2 — the plane witness and the master law -/

/-- **THE MASTER IDENTITY.**  The total witness energy of a plane frame
is the witness budget: the bulk term prices the trace law, and each
direction term prices the frame law at that direction.

No sign condition is necessary.  The identity holds at every real bulk
value and at every real weight family. -/
theorem plane_witness_energy_total {slotCount witnessCount : ℕ}
    (atom : Fin slotCount → (Fin 3 → ℝ)) (axis : Fin 3 → ℝ)
    (direction : Fin witnessCount → (Fin 3 → ℝ)) (weight : Fin witnessCount → ℝ) (bulk : ℝ)
    (haxis : (0 : ℝ) < axis ⬝ᵥ axis)
    (hplane : ∀ slot, atom slot ⬝ᵥ axis = 0)
    (hdirection : ∀ index, direction index ⬝ᵥ axis = 0)
    (hframe : ∀ probe other : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → other ⬝ᵥ axis = 0 →
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other) :
    (∑ slot, (bulk * (atom slot ⬝ᵥ atom slot)
        + ∑ index, weight index * (atom slot ⬝ᵥ direction index) ^ 2))
      = 2 * bulk + ∑ index, weight index * (direction index ⬝ᵥ direction index) := by
  classical
  have hbulkSum : (∑ slot, bulk * (atom slot ⬝ᵥ atom slot)) = 2 * bulk := by
    rw [← Finset.mul_sum, plane_total_energy_eq_two atom axis haxis hplane hframe]
    ring
  have hdirSum : (∑ slot, ∑ index, weight index * (atom slot ⬝ᵥ direction index) ^ 2)
      = ∑ index, weight index * (direction index ⬝ᵥ direction index) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun index _ => ?_
    rw [← Finset.mul_sum,
      ← hframe (direction index) (direction index) (hdirection index) (hdirection index)]
    congr 1
    exact Finset.sum_congr rfl fun slot _ => sq _
  rw [Finset.sum_add_distrib, hbulkSum, hdirSum]

/-- **THE MASTER LAW.**  A witness that dominates every gap caps the total
gap by the witness budget. -/
theorem plane_witness_total_le_one {slotCount witnessCount : ℕ}
    (atom : Fin slotCount → (Fin 3 → ℝ)) (axis : Fin 3 → ℝ)
    (direction : Fin witnessCount → (Fin 3 → ℝ)) (weight : Fin witnessCount → ℝ) (bulk : ℝ)
    (gap : Fin slotCount → ℝ)
    (haxis : (0 : ℝ) < axis ⬝ᵥ axis)
    (hplane : ∀ slot, atom slot ⬝ᵥ axis = 0)
    (hdirection : ∀ index, direction index ⬝ᵥ axis = 0)
    (hframe : ∀ probe other : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → other ⬝ᵥ axis = 0 →
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other)
    (hbudget : 2 * bulk + ∑ index, weight index * (direction index ⬝ᵥ direction index) ≤ 1)
    (hdominate : ∀ slot, gap slot ≤ bulk * (atom slot ⬝ᵥ atom slot)
      + ∑ index, weight index * (atom slot ⬝ᵥ direction index) ^ 2) :
    (∑ slot, gap slot) ≤ 1 := by
  classical
  refine le_trans (Finset.sum_le_sum fun slot _ => hdominate slot) ?_
  rw [plane_witness_energy_total atom axis direction weight bulk haxis hplane hdirection hframe]
  exact hbudget

/-- **THE WITNESS KILL.**  A plane frame with nonnegative scales of total
less than one admits NO dominating witness: the total gap is more than
one, and the master law caps it at one. -/
theorem false_of_plane_witness {slotCount witnessCount : ℕ}
    (atom : Fin slotCount → (Fin 3 → ℝ)) (scale : Fin slotCount → ℝ) (axis : Fin 3 → ℝ)
    (direction : Fin witnessCount → (Fin 3 → ℝ)) (weight : Fin witnessCount → ℝ) (bulk : ℝ)
    (haxis : (0 : ℝ) < axis ⬝ᵥ axis)
    (hplane : ∀ slot, atom slot ⬝ᵥ axis = 0)
    (hdirection : ∀ index, direction index ⬝ᵥ axis = 0)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe other : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → other ⬝ᵥ axis = 0 →
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other)
    (hbudget : 2 * bulk + ∑ index, weight index * (direction index ⬝ᵥ direction index) ≤ 1)
    (hdominate : ∀ slot, atom slot ⬝ᵥ atom slot - scale slot
      ≤ bulk * (atom slot ⬝ᵥ atom slot)
        + ∑ index, weight index * (atom slot ⬝ᵥ direction index) ^ 2) :
    False := by
  classical
  have hcap := plane_witness_total_le_one atom axis direction weight bulk
    (fun slot => atom slot ⬝ᵥ atom slot - scale slot) haxis hplane hdirection hframe hbudget
    hdominate
  rw [Finset.sum_sub_distrib, plane_total_energy_eq_two atom axis haxis hplane hframe] at hcap
  linarith

/-! ## Layer 3 — the pair hypothesis and the certificate route -/

/-- **THE DUAL CERTIFICATE PRODUCES A DOMINATING PAIR.**  A plane datum
whose every pair fails carries no witness.  Thus a witness supplied at
the pair-failure hypothesis returns the pair itself. -/
theorem exists_plane_pair_of_witness {witnessCount : ℕ}
    (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) (axis : Fin 3 → ℝ)
    (haxis : (0 : ℝ) < axis ⬝ᵥ axis)
    (hplane : ∀ slot, atom slot ⬝ᵥ axis = 0)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe other : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → other ⬝ᵥ axis = 0 →
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other)
    (hwitness : (∀ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo →
        0 < atom slotOne ⬝ᵥ atom slotOne - scale slotOne →
        (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
            * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)
          ≤ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2) →
      ∃ (direction : Fin witnessCount → (Fin 3 → ℝ)) (weight : Fin witnessCount → ℝ) (bulk : ℝ),
        (∀ index, direction index ⬝ᵥ axis = 0)
        ∧ 2 * bulk + (∑ index, weight index * (direction index ⬝ᵥ direction index)) ≤ 1
        ∧ ∀ slot, atom slot ⬝ᵥ atom slot - scale slot
            ≤ bulk * (atom slot ⬝ᵥ atom slot)
              + ∑ index, weight index * (atom slot ⬝ᵥ direction index) ^ 2) :
    ∃ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo
      ∧ 0 < atom slotOne ⬝ᵥ atom slotOne - scale slotOne
      ∧ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2
          < (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
            * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) := by
  classical
  by_contra hnone
  have hfail : ∀ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo →
      0 < atom slotOne ⬝ᵥ atom slotOne - scale slotOne →
      (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)
        ≤ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 := by
    intro slotOne slotTwo hne hpos
    by_contra hlt
    exact hnone ⟨slotOne, slotTwo, hne, hpos, lt_of_not_ge hlt⟩
  obtain ⟨direction, weight, bulk, hdirection, hbudget, hdominate⟩ := hwitness hfail
  exact false_of_plane_witness atom scale axis direction weight bulk haxis hplane hdirection
    hsmall hframe hbudget hdominate

/-- **THE ATOM-SUPPORTED WITNESS, PRICED BY THE PAIR HYPOTHESIS.**  When
the witness directions are the atoms themselves and the weights are
nonnegative, the pair hypothesis turns the witness energy of one atom
into a total over the whole slot set. -/
theorem plane_atom_weight_dominates (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (weight : Fin 6 → ℝ) (hweight : ∀ index, 0 ≤ weight index)
    (hfail : ∀ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo →
      0 < atom slotOne ⬝ᵥ atom slotOne - scale slotOne →
      (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)
        ≤ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2)
    (slot : Fin 6) (hpos : 0 < atom slot ⬝ᵥ atom slot - scale slot) :
    weight slot * (atom slot ⬝ᵥ atom slot) ^ 2
        + (atom slot ⬝ᵥ atom slot - scale slot)
          * ((∑ index, weight index * (atom index ⬝ᵥ atom index - scale index))
            - weight slot * (atom slot ⬝ᵥ atom slot - scale slot))
      ≤ ∑ index, weight index * (atom slot ⬝ᵥ atom index) ^ 2 := by
  classical
  have hsplitLeft : (∑ index, weight index * (atom index ⬝ᵥ atom index - scale index))
      - weight slot * (atom slot ⬝ᵥ atom slot - scale slot)
      = ∑ index ∈ Finset.univ.erase slot,
          weight index * (atom index ⬝ᵥ atom index - scale index) := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun index => weight index * (atom index ⬝ᵥ atom index - scale index)) (Finset.mem_univ slot)]
    ring
  have hsplitRight : (∑ index, weight index * (atom slot ⬝ᵥ atom index) ^ 2)
      = weight slot * (atom slot ⬝ᵥ atom slot) ^ 2
        + ∑ index ∈ Finset.univ.erase slot, weight index * (atom slot ⬝ᵥ atom index) ^ 2 :=
    (Finset.add_sum_erase Finset.univ
      (fun index => weight index * (atom slot ⬝ᵥ atom index) ^ 2) (Finset.mem_univ slot)).symm
  rw [hsplitLeft, hsplitRight, Finset.mul_sum]
  have hcell : ∀ index ∈ Finset.univ.erase slot,
      (atom slot ⬝ᵥ atom slot - scale slot)
          * (weight index * (atom index ⬝ᵥ atom index - scale index))
        ≤ weight index * (atom slot ⬝ᵥ atom index) ^ 2 := by
    intro index hindex
    have hne : slot ≠ index := fun heq => (Finset.mem_erase.mp hindex).1 heq.symm
    have hbound := hfail slot index hne hpos
    calc (atom slot ⬝ᵥ atom slot - scale slot)
          * (weight index * (atom index ⬝ᵥ atom index - scale index))
        = weight index * ((atom slot ⬝ᵥ atom slot - scale slot)
            * (atom index ⬝ᵥ atom index - scale index)) := by ring
      _ ≤ weight index * (atom slot ⬝ᵥ atom index) ^ 2 :=
          mul_le_mul_of_nonneg_left hbound (hweight index)
  have hsum := Finset.sum_le_sum hcell
  linarith

/-! ## Layer 4 — the four unconditional strata -/

/-- **THE ZERO-SCALE STRATUM.**  A plane datum with an atom of vanishing
scale and positive energy carries a dominating pair.

This is the SHARP case of the plane residue.  The witness is the rank-one
form of that atom, its budget is exactly one, and the pair hypothesis at
the atom IS the domination. -/
theorem exists_plane_pair_of_zero_scale (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (axis : Fin 3 → ℝ) (heavy : Fin 6)
    (haxis : (0 : ℝ) < axis ⬝ᵥ axis)
    (hplane : ∀ slot, atom slot ⬝ᵥ axis = 0)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe other : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → other ⬝ᵥ axis = 0 →
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other)
    (hzero : scale heavy = 0) (henergy : (0 : ℝ) < atom heavy ⬝ᵥ atom heavy) :
    ∃ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo
      ∧ 0 < atom slotOne ⬝ᵥ atom slotOne - scale slotOne
      ∧ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2
          < (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
            * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) := by
  classical
  refine exists_plane_pair_of_witness (witnessCount := 1) atom scale axis haxis hplane hsmall
    hframe fun hfail => ?_
  refine ⟨fun _ => atom heavy, fun _ => (atom heavy ⬝ᵥ atom heavy)⁻¹, 0, fun _ => hplane heavy,
    ?_, fun slot => ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, mul_zero]
    rw [inv_mul_cancel₀ (ne_of_gt henergy)]
    norm_num
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, zero_mul, zero_add,
      inv_mul_eq_div]
    rw [le_div_iff₀ henergy]
    by_cases hslot : slot = heavy
    · subst hslot
      rw [hzero, sub_zero]
      nlinarith [henergy]
    · rcases le_or_gt (atom slot ⬝ᵥ atom slot - scale slot) 0 with hneg | hpos
      · nlinarith [sq_nonneg (atom slot ⬝ᵥ atom heavy), henergy]
      · have hbound := hfail slot heavy hslot hpos
        rw [hzero, sub_zero] at hbound
        linarith

/-- **THE LIGHT STRATUM.**  A plane datum whose every gap is at most half
its energy carries a dominating pair.  The witness is the bulk term
alone, and the pair hypothesis is not necessary. -/
theorem exists_plane_pair_of_light (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (axis : Fin 3 → ℝ)
    (haxis : (0 : ℝ) < axis ⬝ᵥ axis)
    (hplane : ∀ slot, atom slot ⬝ᵥ axis = 0)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe other : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → other ⬝ᵥ axis = 0 →
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other)
    (hlight : ∀ slot, 2 * (atom slot ⬝ᵥ atom slot - scale slot) ≤ atom slot ⬝ᵥ atom slot) :
    ∃ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo
      ∧ 0 < atom slotOne ⬝ᵥ atom slotOne - scale slotOne
      ∧ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2
          < (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
            * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) := by
  classical
  refine exists_plane_pair_of_witness (witnessCount := 1) atom scale axis haxis hplane hsmall
    hframe fun _ => ?_
  refine ⟨fun _ => atom 0, fun _ => 0, 1 / 2, fun _ => hplane 0, ?_, fun slot => ?_⟩
  · simp
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, zero_mul, add_zero]
    linarith [hlight slot]

/-- **THE HEAVY STRATUM.**  A plane datum with one atom above the half
line whose ratio law caps every other atom carries a dominating pair.

The witness mixes the bulk term with the rank-one form of the heavy
atom.  The mixing parameter is pinned by the heavy atom itself, and the
ratio law prices every other atom through the pair hypothesis. -/
theorem exists_plane_pair_of_heavy (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (axis : Fin 3 → ℝ) (heavy : Fin 6)
    (haxis : (0 : ℝ) < axis ⬝ᵥ axis)
    (hplane : ∀ slot, atom slot ⬝ᵥ axis = 0)
    (hnonneg : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe other : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → other ⬝ᵥ axis = 0 →
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other)
    (henergy : (0 : ℝ) < atom heavy ⬝ᵥ atom heavy)
    (hheavy : 2 * scale heavy ≤ atom heavy ⬝ᵥ atom heavy)
    (hratio : ∀ slot, (atom slot ⬝ᵥ atom slot - scale slot)
        * (3 * (atom heavy ⬝ᵥ atom heavy) - 2 * scale heavy)
      ≤ (atom slot ⬝ᵥ atom slot) * (atom heavy ⬝ᵥ atom heavy)) :
    ∃ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo
      ∧ 0 < atom slotOne ⬝ᵥ atom slotOne - scale slotOne
      ∧ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2
          < (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
            * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) := by
  classical
  refine exists_plane_pair_of_witness (witnessCount := 1) atom scale axis haxis hplane hsmall
    hframe fun hfail => ?_
  have hsq : (0 : ℝ) < (atom heavy ⬝ᵥ atom heavy) ^ 2 := pow_pos henergy 2
  have hne : atom heavy ⬝ᵥ atom heavy ≠ 0 := ne_of_gt henergy
  refine ⟨fun _ => atom heavy,
    fun _ => (atom heavy ⬝ᵥ atom heavy - 2 * scale heavy) / (atom heavy ⬝ᵥ atom heavy) ^ 2,
    scale heavy / (atom heavy ⬝ᵥ atom heavy), fun _ => hplane heavy, ?_, fun slot => ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
    have hbudget : 2 * (scale heavy / (atom heavy ⬝ᵥ atom heavy))
        + (atom heavy ⬝ᵥ atom heavy - 2 * scale heavy) / (atom heavy ⬝ᵥ atom heavy) ^ 2
          * (atom heavy ⬝ᵥ atom heavy) = 1 := by
      field_simp
      ring
    rw [hbudget]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
    have hshape : scale heavy / (atom heavy ⬝ᵥ atom heavy) * (atom slot ⬝ᵥ atom slot)
          + (atom heavy ⬝ᵥ atom heavy - 2 * scale heavy) / (atom heavy ⬝ᵥ atom heavy) ^ 2
            * (atom slot ⬝ᵥ atom heavy) ^ 2
          - (atom slot ⬝ᵥ atom slot - scale slot)
        = (scale heavy * (atom heavy ⬝ᵥ atom heavy) * (atom slot ⬝ᵥ atom slot)
            + (atom heavy ⬝ᵥ atom heavy - 2 * scale heavy) * (atom slot ⬝ᵥ atom heavy) ^ 2
            - (atom slot ⬝ᵥ atom slot - scale slot) * (atom heavy ⬝ᵥ atom heavy) ^ 2)
          / (atom heavy ⬝ᵥ atom heavy) ^ 2 := by
      field_simp
    have hcore : 0 ≤ scale heavy * (atom heavy ⬝ᵥ atom heavy) * (atom slot ⬝ᵥ atom slot)
        + (atom heavy ⬝ᵥ atom heavy - 2 * scale heavy) * (atom slot ⬝ᵥ atom heavy) ^ 2
        - (atom slot ⬝ᵥ atom slot - scale slot) * (atom heavy ⬝ᵥ atom heavy) ^ 2 := by
      by_cases hslot : slot = heavy
      · subst hslot
        nlinarith [henergy]
      · have hslotEnergy : (0 : ℝ) ≤ atom slot ⬝ᵥ atom slot := dotProduct_self_nonneg (atom slot)
        rcases le_or_gt (atom slot ⬝ᵥ atom slot - scale slot) 0 with hneg | hpos
        · have hone : 0 ≤ scale heavy * (atom heavy ⬝ᵥ atom heavy) * (atom slot ⬝ᵥ atom slot) :=
            mul_nonneg (mul_nonneg (hnonneg heavy) henergy.le) hslotEnergy
          have htwo : 0 ≤ (atom heavy ⬝ᵥ atom heavy - 2 * scale heavy)
              * (atom slot ⬝ᵥ atom heavy) ^ 2 :=
            mul_nonneg (by linarith) (sq_nonneg _)
          have hthree : 0 ≤ (scale slot - atom slot ⬝ᵥ atom slot)
              * (atom heavy ⬝ᵥ atom heavy) ^ 2 :=
            mul_nonneg (by linarith) hsq.le
          nlinarith [hone, htwo, hthree]
        · have hbound := hfail slot heavy hslot hpos
          have hcross : (atom slot ⬝ᵥ atom slot - scale slot)
              * (atom heavy ⬝ᵥ atom heavy - scale heavy)
                * (atom heavy ⬝ᵥ atom heavy - 2 * scale heavy)
              ≤ (atom slot ⬝ᵥ atom heavy) ^ 2
                * (atom heavy ⬝ᵥ atom heavy - 2 * scale heavy) :=
            mul_le_mul_of_nonneg_right hbound (by linarith)
          have hlift : (atom slot ⬝ᵥ atom slot - scale slot)
              * (3 * (atom heavy ⬝ᵥ atom heavy) - 2 * scale heavy) * scale heavy
              ≤ (atom slot ⬝ᵥ atom slot) * (atom heavy ⬝ᵥ atom heavy) * scale heavy :=
            mul_le_mul_of_nonneg_right (hratio slot) (hnonneg heavy)
          nlinarith [hcross, hlift, henergy, hnonneg heavy]
    have hdiv := div_nonneg hcore hsq.le
    rw [← hshape] at hdiv
    linarith

/-- **THE CONIC STRATUM.**  A plane datum whose gap ratios obey the conic
budget carries a dominating pair.  The witness is a positive combination
of the atom directions themselves, and the pair hypothesis prices every
cross term.

The parameter `share` is the common factor of the combination.  The two
hypotheses are the budget of the combination and its domination at each
atom of positive gap. -/
theorem exists_plane_pair_of_conic (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (axis : Fin 3 → ℝ) (weight : Fin 6 → ℝ)
    (haxis : (0 : ℝ) < axis ⬝ᵥ axis)
    (hplane : ∀ slot, atom slot ⬝ᵥ axis = 0)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe other : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → other ⬝ᵥ axis = 0 →
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other)
    (hweight : ∀ index, 0 ≤ weight index)
    (hbudget : (∑ index, weight index * (atom index ⬝ᵥ atom index)) ≤ 1)
    (hconic : ∀ slot, 0 < atom slot ⬝ᵥ atom slot - scale slot →
      atom slot ⬝ᵥ atom slot - scale slot
        ≤ weight slot * (atom slot ⬝ᵥ atom slot) ^ 2
          + (atom slot ⬝ᵥ atom slot - scale slot)
            * ((∑ index, weight index * (atom index ⬝ᵥ atom index - scale index))
              - weight slot * (atom slot ⬝ᵥ atom slot - scale slot))) :
    ∃ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo
      ∧ 0 < atom slotOne ⬝ᵥ atom slotOne - scale slotOne
      ∧ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2
          < (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
            * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) := by
  classical
  refine exists_plane_pair_of_witness (witnessCount := 6) atom scale axis haxis hplane hsmall
    hframe fun hfail => ?_
  refine ⟨atom, weight, 0, hplane, by simpa using hbudget, fun slot => ?_⟩
  rw [zero_mul, zero_add]
  rcases le_or_gt (atom slot ⬝ᵥ atom slot - scale slot) 0 with hneg | hpos
  · exact le_trans hneg (Finset.sum_nonneg fun index _ =>
      mul_nonneg (hweight index) (sq_nonneg _))
  · exact le_trans (hconic slot hpos)
      (plane_atom_weight_dominates atom scale weight hweight hfail slot hpos)

/-! ## Layer 5 — the witness engine at general rank -/

/-- **THE TRACE LAW OF A TIGHT FRAME.**  The atoms of a tight frame of the
whole space carry total energy exactly the rank. -/
theorem frame_total_energy_eq_rank {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (hframe : ∀ probe other : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other) :
    (∑ slot, atom slot ⬝ᵥ atom slot) = (rank : ℝ) := by
  classical
  have hcolumn : ∀ index : Fin rank, (∑ slot, atom slot index ^ 2) = 1 := by
    intro index
    have hkey := hframe (unitVector index) (unitVector index)
    rw [unitVector_dot_self] at hkey
    rw [← hkey]
    refine Finset.sum_congr rfl fun slot _ => ?_
    rw [dotProduct_comm (atom slot) (unitVector index), unitVector_dot, sq]
  have hswap : (∑ slot, atom slot ⬝ᵥ atom slot)
      = ∑ index : Fin rank, ∑ slot, atom slot index ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun slot _ => dot_self_eq_sum_sq (atom slot)
  rw [hswap, Finset.sum_congr rfl fun index _ => hcolumn index]
  simp

/-- **THE MASTER IDENTITY AT GENERAL RANK.** -/
theorem frame_witness_energy_total {slotCount rank witnessCount : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ))
    (direction : Fin witnessCount → (Fin rank → ℝ)) (weight : Fin witnessCount → ℝ) (bulk : ℝ)
    (hframe : ∀ probe other : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other) :
    (∑ slot, (bulk * (atom slot ⬝ᵥ atom slot)
        + ∑ index, weight index * (atom slot ⬝ᵥ direction index) ^ 2))
      = (rank : ℝ) * bulk + ∑ index, weight index * (direction index ⬝ᵥ direction index) := by
  classical
  have hbulkSum : (∑ slot, bulk * (atom slot ⬝ᵥ atom slot)) = (rank : ℝ) * bulk := by
    rw [← Finset.mul_sum, frame_total_energy_eq_rank atom hframe]
    ring
  have hdirSum : (∑ slot, ∑ index, weight index * (atom slot ⬝ᵥ direction index) ^ 2)
      = ∑ index, weight index * (direction index ⬝ᵥ direction index) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun index _ => ?_
    rw [← Finset.mul_sum, ← hframe (direction index) (direction index)]
    congr 1
    exact Finset.sum_congr rfl fun slot _ => sq _
  rw [Finset.sum_add_distrib, hbulkSum, hdirSum]

/-- **THE WITNESS KILL AT GENERAL RANK.**  A tight frame with scales of
total less than one admits no dominating witness of budget one less than
the rank. -/
theorem false_of_frame_witness {slotCount rank witnessCount : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (direction : Fin witnessCount → (Fin rank → ℝ)) (weight : Fin witnessCount → ℝ) (bulk : ℝ)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe other : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other)
    (hbudget : (rank : ℝ) * bulk + (∑ index, weight index * (direction index ⬝ᵥ direction index))
      ≤ (rank : ℝ) - 1)
    (hdominate : ∀ slot, atom slot ⬝ᵥ atom slot - scale slot
      ≤ bulk * (atom slot ⬝ᵥ atom slot)
        + ∑ index, weight index * (atom slot ⬝ᵥ direction index) ^ 2) :
    False := by
  classical
  have hcap : (∑ slot, (atom slot ⬝ᵥ atom slot - scale slot)) ≤ (rank : ℝ) - 1 := by
    refine le_trans (Finset.sum_le_sum fun slot _ => hdominate slot) ?_
    rw [frame_witness_energy_total atom direction weight bulk hframe]
    exact hbudget
  rw [Finset.sum_sub_distrib, frame_total_energy_eq_rank atom hframe] at hcap
  linarith

/-- **THE ZERO-SCALE DEFLATION AT GENERAL RANK.**  A tight frame of rank
two or more with scales of total less than one carries NO atom of
vanishing scale whose squared readings dominate every gap.

At rank two this is the sharp case of the plane residue.  At rank three
it is the pivot deflation of the frame lane: the rank-one form of a
vanishing-scale atom has trace one, and the budget of the kill is two. -/
theorem false_of_zero_scale_frame {slotCount rank : ℕ} (hrank : 2 ≤ rank)
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ) (pivot : Fin slotCount)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe other : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other)
    (henergy : (0 : ℝ) < atom pivot ⬝ᵥ atom pivot)
    (hpair : ∀ slot, (atom slot ⬝ᵥ atom slot - scale slot) * (atom pivot ⬝ᵥ atom pivot)
      ≤ (atom slot ⬝ᵥ atom pivot) ^ 2) :
    False := by
  classical
  have hcast : (2 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
  refine false_of_frame_witness atom scale (fun _ : Fin 1 => atom pivot)
    (fun _ => (atom pivot ⬝ᵥ atom pivot)⁻¹) 0 hsmall hframe ?_ fun slot => ?_
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, mul_zero, zero_add]
    rw [inv_mul_cancel₀ (ne_of_gt henergy)]
    linarith
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, zero_mul, zero_add,
      inv_mul_eq_div]
    rw [le_div_iff₀ henergy]
    exact hpair slot

/-! ## Layer 6 — the residue in dual form -/

/-- **THE PLANE RESIDUE IN DUAL FORM.**  At every plane datum whose pairs
all fail there is a witness of budget one.

This residue is strictly smaller than the plane pair residue.  It carries
seven real unknowns — one bulk value and six weights — and its
constraints are linear in those unknowns at fixed data.  It carries no
combinatorial search, no eigenvalue and no square root. -/
def AtomPlaneWitnessClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) (axis : Fin 3 → ℝ),
    (0 : ℝ) < axis ⬝ᵥ axis →
    (∀ slot, atom slot ⬝ᵥ axis = 0) →
    (∀ slot, 0 ≤ scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe other : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → other ⬝ᵥ axis = 0 →
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other) →
    (∀ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo →
      0 < atom slotOne ⬝ᵥ atom slotOne - scale slotOne →
      (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)
        ≤ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2) →
    ∃ (weight : Fin 6 → ℝ) (bulk : ℝ),
      2 * bulk + (∑ index, weight index * (atom index ⬝ᵥ atom index)) ≤ 1
      ∧ ∀ slot, atom slot ⬝ᵥ atom slot - scale slot
          ≤ bulk * (atom slot ⬝ᵥ atom slot)
            + ∑ index, weight index * (atom slot ⬝ᵥ atom index) ^ 2

/-- **THE DUAL RESIDUE IS THE PLANE RESIDUE.** -/
theorem atomPairGramClosed_of_planeWitness (hwitness : AtomPlaneWitnessClosed) :
    AtomPairGramClosed := by
  classical
  intro atom scale axis haxis hplane hnonneg hsmall hframe
  refine exists_plane_pair_of_witness (witnessCount := 6) atom scale axis haxis hplane hsmall
    hframe fun hfail => ?_
  obtain ⟨weight, bulk, hbudget, hdominate⟩ :=
    hwitness atom scale axis haxis hplane hnonneg hsmall hframe hfail
  exact ⟨atom, weight, bulk, hplane, hbudget, hdominate⟩

/-! ## Layer 7 — the campaign consequences of the dual residue -/

/-- The plane pair ceiling from the dual residue. -/
theorem atomPairCeilingClosed_of_planeWitness (hwitness : AtomPlaneWitnessClosed) :
    AtomPairCeilingClosed :=
  atomPairCeilingClosed_of_gram (atomPairGramClosed_of_planeWitness hwitness)

/-- **DENSE PROFILE A AT RANK FIVE FROM THE DUAL RESIDUE.** -/
theorem rankFiveDenseHeavyFiveClosed_of_planeWitness (hwitness : AtomPlaneWitnessClosed) :
    RankFiveDenseHeavyFiveClosed :=
  rankFiveDenseHeavyFiveClosed_of_atomPairGram (atomPairGramClosed_of_planeWitness hwitness)

/-- The residual cycle cell of profile A from the dual residue. -/
theorem rankFiveDenseHeavyFiveDistinctClosed_of_planeWitness
    (hwitness : AtomPlaneWitnessClosed) : RankFiveDenseHeavyFiveDistinctClosed :=
  rankFiveDenseHeavyFiveDistinctClosed_of_atomPairGram
    (atomPairGramClosed_of_planeWitness hwitness)

/-- **THE DUAL RESIDUE MAKES EVERY CRUX INTERIOR.** -/
theorem SixThreeCrux.shifted_weight_pos_of_planeWitness (crux : SixThreeCrux)
    (hwitness : AtomPlaneWitnessClosed) (atomIndex : Fin 6) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex :=
  crux.shifted_weight_pos_of_atomPairCeiling (atomPairCeilingClosed_of_planeWitness hwitness)
    atomIndex

/-- The campaign-level interiority input, from the dual residue. -/
theorem forall_shifted_weight_pos_of_planeWitness (hwitness : AtomPlaneWitnessClosed) :
    ∀ (crux : SixThreeCrux) (atomIndex : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex :=
  forall_shifted_weight_pos_of_atomPairGram (atomPairGramClosed_of_planeWitness hwitness)

/-- The boundary crux kill, from the dual residue. -/
theorem SixThreeCrux.false_of_planeWitness_of_shift_zero (crux : SixThreeCrux)
    (hwitness : AtomPlaneWitnessClosed) {boundary : Fin 6}
    (hzero : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight boundary = 0) :
    False :=
  crux.false_of_atomPairCeiling_of_shift_zero (atomPairCeilingClosed_of_planeWitness hwitness)
    hzero

end Gtz
