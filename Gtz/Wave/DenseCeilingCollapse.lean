import Gtz.Wave.AtomEnergyCeiling
import Gtz.Wave.DenseHeavyAtomReduction
import Gtz.Wave.AssemblyRankCapstone

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The dense ceiling collapse — the boundary increment and the six dense profiles

The atom triple ceiling is the design-side residue of the third rung: six
vectors in three dimensions that form a tight frame, together with six
scales of total less than one, carry a triple whose shifted form is
strictly positive.  The landed kill consumes that residue together with
an INTERIOR datum, because the residue asks each scale to be strictly
positive.

This module removes the interiority.  A scale vector that is only
nonnegative lifts to a strictly positive one by a uniform increment, and the
increment keeps the total below one.  The dominated probe of the lifted
scales dominates the original scales as well, because the square of each
probe entry is nonnegative.  Thus the residue holds verbatim at a
nonnegative scale vector.

The shifted weights of a crux are nonnegative with no hypothesis at all:
the crux carries its own first-order bundle, and the capture diagonal of
that bundle is nonnegative.  The two facts together kill the crux from
the residue alone.  Every rung closure of the campaign follows, and so do
the six dense profile closures, the two dense branch closures and the
`(6,3)` cell.

The last layer opens the boundary stratum in two dimensions.  At an atom
of zero shifted weight the triple ceiling reads as a PAIR ceiling in the
plane orthogonal to that atom, because the shadow of the other atoms in
that plane is again a tight frame and the shadow energy never exceeds the
atom energy.  The rank-five heavy-five profile hands exactly this
configuration, thus the whole profile A closes from the plane residue.
The plane residue in turn reads as ONE polynomial inequality in the atom
Gram over the fifteen pairs, with no eigenvalue and no square root.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomTripleCeiling_of_nonneg` — **THE BOUNDARY INCREMENT.**  The
  residue holds at a nonnegative scale vector.
* `Gtz.atomTripleCeilingMargin_of_nonneg` — the same for the margin form.
* `Gtz.SixThreeCrux.shifted_weight_nonneg` — **THE UNCONDITIONAL
  BOUNDARY LAW.**  Every shifted weight of a crux is nonnegative.
* `Gtz.SixThreeCrux.false_of_atomTripleCeiling_of_nonneg`,
  `Gtz.SixThreeCrux.absurd_of_atomTripleCeiling` — **THE CRUX KILL WITH
  NO SIDE HYPOTHESIS.**
* `Gtz.isEmpty_sixThreeCrux_of_atomTripleCeiling`,
  `Gtz.gtzWeighted_six_three_of_atomTripleCeiling`,
  `Gtz.gtzWeightedAll_three_of_atomTripleCeiling` — **THE CELL FROM ONE
  DESIGN-SIDE RESIDUE.**
* `Gtz.rankFiveDenseHeavyFiveClosed_of_atomTripleCeiling`,
  `Gtz.rankFiveDenseHeavyFourClosed_of_atomTripleCeiling`,
  `Gtz.rankFiveDenseThreeTriplesClosed_of_atomTripleCeiling`,
  `Gtz.rankSixDenseHeavyFiveClosed_of_atomTripleCeiling`,
  `Gtz.rankSixDenseHeavyFourClosed_of_atomTripleCeiling`,
  `Gtz.rankSixDenseAllTriplesClosed_of_atomTripleCeiling` — **THE SIX
  DENSE PROFILE CLOSURES.**
* `Gtz.rankFiveDenseClosed_of_atomTripleCeiling`,
  `Gtz.rankSixDenseClosed_of_atomTripleCeiling` — the two dense branch
  closures.
* `Gtz.atom_energy_le_probe_energy`, `Gtz.atom_frame_energy_floor` —
  **THE FRAME ENERGY FLOOR.**  The scaled atom energy of any probe is at
  least the probe energy divided by the total scale.
* `Gtz.AtomPairCeilingClosed` — **THE PLANE PAIR RESIDUE.**
* `Gtz.atomBoundaryTripleCeiling_of_atomPairCeiling` — **THE BOUNDARY
  DEFLATION.**  The plane residue supplies a dominating triple through
  the boundary atom.
* `Gtz.SixThreeCrux.shifted_weight_pos_of_atomPairCeiling` — the plane
  residue makes every crux interior.
* `Gtz.rankFiveDenseHeavyFiveClosed_of_atomPairCeiling`,
  `Gtz.rankFiveDenseHeavyFiveDistinctClosed_of_atomPairCeiling` — **THE
  RANK-FIVE PROFILE A FROM THE PLANE RESIDUE.**
* `Gtz.pair_form_pos` — the two-by-two Sylvester criterion.
* `Gtz.AtomPairGramClosed` — **THE PLANE PAIR GRAM RESIDUE.**  The plane
  residue as one polynomial inequality over fifteen pairs.
* `Gtz.atomPairCeilingClosed_of_gram` — the pair criterion is the plane
  residue.
* `Gtz.rankFiveDenseHeavyFiveClosed_of_atomPairGram`,
  `Gtz.forall_shifted_weight_pos_of_atomPairGram` — profile A and the
  boundary stratum from the pair criterion.

## Vacuity

Every statement of this module is vacuous if `Gtz.GtzWeighted 6 3`
holds: no crux exists, thus no frame exists.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the scale calculus of the residue -/

/-- **THE BOUNDARY INCREMENT.**  The atom triple ceiling holds verbatim at a
NONNEGATIVE scale vector.  A uniform increment lifts the scales to strictly
positive ones and keeps the total below one, and the dominating triple of
the lifted scales dominates the original scales, because each probe
entry has a nonnegative square. -/
theorem atomTripleCeiling_of_nonneg (hresidue : AtomTripleCeilingClosed)
    (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hnonneg : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction))
        = probe ⬝ᵥ direction) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
          (∑ slot, scale slot * probe slot ^ 2)
            < atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  set increment : ℝ := (1 - ∑ slot, scale slot) / 12 with hincrement
  have hincrementPos : 0 < increment := by rw [hincrement]; linarith
  set lifted : Fin 6 → ℝ := fun slot => scale slot + increment with hlifted
  have hliftedPos : ∀ slot, 0 < lifted slot := by
    intro slot
    have hslot := hnonneg slot
    rw [hlifted]
    simpa using by linarith [hslot, hincrementPos]
  have hliftedSum : (∑ slot, lifted slot) < 1 := by
    have hsum : (∑ slot, lifted slot) = (∑ slot, scale slot) + 6 * increment := by
      rw [hlifted]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      norm_num
    rw [hsum, hincrement]
    linarith
  obtain ⟨car, hcard, hdominates⟩ :=
    hresidue atom lifted hliftedPos hliftedSum hframe
  refine ⟨car, hcard, fun probe hvanish hne => ?_⟩
  refine lt_of_le_of_lt ?_ (hdominates probe hvanish hne)
  refine Finset.sum_le_sum fun slot _ => ?_
  have hle : scale slot ≤ lifted slot := by
    rw [hlifted]
    simpa using by linarith [hincrementPos]
  exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)

/-- The same increment for the MARGIN form of the residue: the margin of the
lifted scales is a margin of the original scales. -/
theorem atomTripleCeilingMargin_of_nonneg (hmargin : AtomTripleCeilingMarginClosed)
    (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hnonneg : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction))
        = probe ⬝ᵥ direction) :
    ∃ (car : Finset (Fin 6)) (margin : ℝ), car.card = 3 ∧ 0 < margin
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2) + margin * (probe ⬝ᵥ probe)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  set increment : ℝ := (1 - ∑ slot, scale slot) / 12 with hincrement
  have hincrementPos : 0 < increment := by rw [hincrement]; linarith
  set lifted : Fin 6 → ℝ := fun slot => scale slot + increment with hlifted
  have hliftedPos : ∀ slot, 0 < lifted slot := by
    intro slot
    have hslot := hnonneg slot
    rw [hlifted]
    simpa using by linarith [hslot, hincrementPos]
  have hliftedSum : (∑ slot, lifted slot) < 1 := by
    have hsum : (∑ slot, lifted slot) = (∑ slot, scale slot) + 6 * increment := by
      rw [hlifted]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      norm_num
    rw [hsum, hincrement]
    linarith
  obtain ⟨car, margin, hcard, hmarginPos, hbound⟩ :=
    hmargin atom lifted hliftedPos hliftedSum hframe
  refine ⟨car, margin, hcard, hmarginPos, fun probe hvanish => ?_⟩
  have hstep : (∑ slot, scale slot * probe slot ^ 2)
      ≤ ∑ slot, lifted slot * probe slot ^ 2 := by
    refine Finset.sum_le_sum fun slot _ => ?_
    have hle : scale slot ≤ lifted slot := by
      rw [hlifted]
      simpa using by linarith [hincrementPos]
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  linarith [hbound probe hvanish, hstep]

/-! ## Layer 2 — the unconditional boundary law of a crux -/

/-- **THE UNCONDITIONAL BOUNDARY LAW.**  Every shifted weight of a crux
is nonnegative.  The crux carries its own first-order bundle, and the
capture diagonal of a chart stationary datum is nonnegative at every
atom.  No frame, no rank and no profile enters. -/
theorem SixThreeCrux.shifted_weight_nonneg (crux : SixThreeCrux)
    (atomIndex : Fin 6) :
    0 ≤ chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex := by
  obtain ⟨_multiplier, _selection, hdata⟩ :=
    crux.exists_multiplier_isChartStationaryData
  exact capture_diagonal_nonneg_of_isChartStationaryData hdata atomIndex

/-- The shifted weights of a crux sum below one: the weights sum to one
and the chart value is negative. -/
theorem SixThreeCrux.shifted_weight_sum_lt_one (crux : SixThreeCrux) :
    (∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex)) < 1 := by
  have hsum : (∑ atomIndex : Fin 6,
        (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex))
      = 6 * chartObjective (chartPointOfDesign crux.design) + 1 := by
    rw [Finset.sum_add_distrib, (chartPointOfDesign crux.design).weight_sum_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hneg := crux.hasNegativeChartValue
  rw [hsum]
  linarith

/-! ## Layer 3 — the crux kill with no side hypothesis -/

/-- **THE CRUX KILL AT A BOUNDARY DATUM.**  The atom triple ceiling
refutes the crux whenever the shifted weights are merely NONNEGATIVE.
The increment of layer 1 supplies the strictly positive scales the residue
asks for, and the ceiling witness of the dominating triple forbids it. -/
theorem SixThreeCrux.false_of_atomTripleCeiling_of_nonneg (crux : SixThreeCrux)
    (hresidue : AtomTripleCeilingClosed)
    (hboundary : ∀ atomIndex : Fin 6,
      0 ≤ chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    False := by
  classical
  set point := chartPointOfDesign crux.design with hpoint
  set value := chartObjective point with hvalue
  obtain ⟨family, hnorm, horth, hsplit⟩ :=
    exists_orthonormal_family_of_trace 3 point.chart point.isSymmetric
      point.isIdempotent point.hasTraceRank
  obtain ⟨car, hcard, hdominates⟩ :=
    atomTripleCeiling_of_nonneg hresidue (atomVec family)
      (fun atomIndex => value + point.weight atomIndex) hboundary
      crux.shifted_weight_sum_lt_one (atom_frame_law hnorm horth)
  obtain ⟨probe, hvanish, hne, hwitness⟩ := crux.exists_ceiling_witness hsplit hcard
  exact absurd (hdominates probe hvanish hne) (not_lt.mpr hwitness)

/-- **THE CRUX KILL FROM THE RESIDUE ALONE.**  No interiority, no frame,
no rank: the atom triple ceiling refutes every crux. -/
theorem SixThreeCrux.absurd_of_atomTripleCeiling (crux : SixThreeCrux)
    (hresidue : AtomTripleCeilingClosed) : False :=
  crux.false_of_atomTripleCeiling_of_nonneg hresidue crux.shifted_weight_nonneg

/-- The crux type is empty under the residue. -/
theorem isEmpty_sixThreeCrux_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : IsEmpty SixThreeCrux :=
  ⟨fun crux => crux.absurd_of_atomTripleCeiling hresidue⟩

/-- **THE CELL FROM ONE DESIGN-SIDE RESIDUE.**  Weighted GTZ at `(6,3)`
follows from the atom triple ceiling with NO side hypothesis. -/
theorem gtzWeighted_six_three_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_isEmpty_sixThreeCrux
    (isEmpty_sixThreeCrux_of_atomTripleCeiling hresidue)

/-- **THE RANK-THREE PAYOFF FROM ONE DESIGN-SIDE RESIDUE.** -/
theorem gtzWeightedAll_three_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three
    (gtzWeighted_six_three_of_atomTripleCeiling hresidue)

/-- The rank-four frame kill, with no interiority. -/
theorem RankFourFrame.false_of_atomTripleCeiling {crux : SixThreeCrux}
    (_frame : RankFourFrame crux) (hresidue : AtomTripleCeilingClosed) : False :=
  crux.absurd_of_atomTripleCeiling hresidue

/-- The rank-five frame kill, with no interiority. -/
theorem RankFiveFrame.false_of_atomTripleCeiling {crux : SixThreeCrux}
    (_frame : RankFiveFrame crux) (hresidue : AtomTripleCeilingClosed) : False :=
  crux.absurd_of_atomTripleCeiling hresidue

/-! ## Layer 4 — the six dense profile closures -/

/-- **DENSE PROFILE A AT RANK FIVE.**  The heavy-five profile dies. -/
theorem rankFiveDenseHeavyFiveClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankFiveDenseHeavyFiveClosed := by
  intro crux _frame _heavyAtom _hthree _hfive _hdoubles _htrace _hheavy
  exact crux.absurd_of_atomTripleCeiling hresidue

/-- The residual cycle cell of profile A at rank five. -/
theorem rankFiveDenseHeavyFiveDistinctClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) :
    RankFiveDenseHeavyFiveDistinctClosed := by
  intro crux _frame _heavyAtom _hthree _hfive _hdoubles _htrace _hheavy _hdistinct
  exact crux.absurd_of_atomTripleCeiling hresidue

/-- **DENSE PROFILE B AT RANK FIVE.**  The heavy-four profile dies. -/
theorem rankFiveDenseHeavyFourClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankFiveDenseHeavyFourClosed := by
  intro crux _frame _heavyAtom _tripleAtom _hthree _hfour _hne _htriple _hdoubles
  exact crux.absurd_of_atomTripleCeiling hresidue

/-- **DENSE PROFILE C AT RANK FIVE.**  The three-triple profile dies. -/
theorem rankFiveDenseThreeTriplesClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankFiveDenseThreeTriplesClosed := by
  intro crux _frame _one _two _three _hthree _hOneTwo _hOneThree _hTwoThree
    _hmultOne _hmultTwo _hmultThree _hdoubles
  exact crux.absurd_of_atomTripleCeiling hresidue

/-- **DENSE PROFILE A AT RANK SIX.** -/
theorem rankSixDenseHeavyFiveClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankSixDenseHeavyFiveClosed := by
  intro crux _frame _heavyAtom _hthree _hmultTwo _hfive
  exact crux.absurd_of_atomTripleCeiling hresidue

/-- **DENSE PROFILE B AT RANK SIX.** -/
theorem rankSixDenseHeavyFourClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankSixDenseHeavyFourClosed := by
  intro crux _frame _heavyAtom _hthree _hmultTwo _hcap _hfour
  exact crux.absurd_of_atomTripleCeiling hresidue

/-- **DENSE PROFILE C AT RANK SIX.**  The all-triple profile dies — the
cell where the complex trine shadow lives. -/
theorem rankSixDenseAllTriplesClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankSixDenseAllTriplesClosed := by
  intro crux _frame _hthree _hmult
  exact crux.absurd_of_atomTripleCeiling hresidue

/-- **THE RANK-FIVE DENSE BRANCH.** -/
theorem rankFiveDenseClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankFiveDenseClosed :=
  rankFiveDenseClosed_of_profile_closures
    (rankFiveDenseHeavyFiveClosed_of_atomTripleCeiling hresidue)
    (rankFiveDenseHeavyFourClosed_of_atomTripleCeiling hresidue)
    (rankFiveDenseThreeTriplesClosed_of_atomTripleCeiling hresidue)

/-- **THE RANK-SIX DENSE BRANCH.** -/
theorem rankSixDenseClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankSixDenseClosed :=
  rankSixDenseClosed_of_profile_closures
    (rankSixDenseHeavyFiveClosed_of_atomTripleCeiling hresidue)
    (rankSixDenseHeavyFourClosed_of_atomTripleCeiling hresidue)
    (rankSixDenseAllTriplesClosed_of_atomTripleCeiling hresidue)

/-! ## Layer 5 — the rung closures and the frame energy floor -/

/-- The rank-five support-two closure, with no interiority. -/
theorem rankFiveSupportTwoClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankFiveSupportTwoClosed := by
  intro crux _frame _columnIndex _htwo
  exact crux.absurd_of_atomTripleCeiling hresidue

/-- The rank-four support-two closure, with no interiority. -/
theorem rankFourSupportTwoClosed_of_atomTripleCeiling
    (hresidue : AtomTripleCeilingClosed) : RankFourSupportTwoClosed := by
  intro crux _frame _columnIndex _htwo
  exact crux.absurd_of_atomTripleCeiling hresidue

/-- **THE ATOM ENERGY CAP.**  The energy of one atom against a probe
never exceeds the probe energy: the frame law splits the probe energy
into nonnegative atom energies. -/
theorem atom_energy_le_probe_energy {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ))
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction))
        = probe ⬝ᵥ direction)
    (probe : Fin rank → ℝ) (slot : Fin slotCount) :
    (atom slot ⬝ᵥ probe) ^ 2 ≤ probe ⬝ᵥ probe := by
  classical
  have hsum : (∑ other, (atom other ⬝ᵥ probe) ^ 2) = probe ⬝ᵥ probe := by
    rw [← hframe probe probe]
    exact Finset.sum_congr rfl fun other _ => sq _
  rw [← hsum]
  exact Finset.single_le_sum (f := fun other => (atom other ⬝ᵥ probe) ^ 2)
    (fun other _ => sq_nonneg _) (Finset.mem_univ slot)

/-- **THE FRAME ENERGY FLOOR.**  The scaled atom energy of a probe is at
least the probe energy divided by the total scale.  This is the sharp
matrix form of the escape law: the whole scaled frame dominates the
identity by the reciprocal of the total scale, thus every direction
escapes, not only the best one. -/
theorem atom_frame_energy_floor {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (hpos : ∀ slot, 0 < scale slot)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction))
        = probe ⬝ᵥ direction)
    (probe : Fin rank → ℝ) :
    probe ⬝ᵥ probe
      ≤ (∑ slot, scale slot) * ∑ slot, (atom slot ⬝ᵥ probe) ^ 2 / scale slot := by
  classical
  have hnormNonneg : 0 ≤ probe ⬝ᵥ probe := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun index _ => mul_self_nonneg _
  have hsum : (∑ slot, (atom slot ⬝ᵥ probe) ^ 2) = probe ⬝ᵥ probe := by
    rw [← hframe probe probe]
    exact Finset.sum_congr rfl fun slot _ => sq _
  -- the Cauchy-Schwarz split of the atom energy into a scaled part and a
  -- reciprocal part
  have hcauchy : (∑ slot, (atom slot ⬝ᵥ probe) ^ 2) ^ 2
      ≤ (∑ slot, scale slot * (atom slot ⬝ᵥ probe) ^ 2)
        * ∑ slot, (atom slot ⬝ᵥ probe) ^ 2 / scale slot := by
    have hkey := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin slotCount))
      (fun slot => Real.sqrt (scale slot) * (atom slot ⬝ᵥ probe))
      (fun slot => (atom slot ⬝ᵥ probe) / Real.sqrt (scale slot))
    have hcell : ∀ slot : Fin slotCount,
        (Real.sqrt (scale slot) * (atom slot ⬝ᵥ probe))
            * ((atom slot ⬝ᵥ probe) / Real.sqrt (scale slot))
          = (atom slot ⬝ᵥ probe) ^ 2 := by
      intro slot
      have hne : Real.sqrt (scale slot) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr (hpos slot))
      field_simp
    have hleft : ∀ slot : Fin slotCount,
        (Real.sqrt (scale slot) * (atom slot ⬝ᵥ probe)) ^ 2
          = scale slot * (atom slot ⬝ᵥ probe) ^ 2 := by
      intro slot
      rw [mul_pow, Real.sq_sqrt (hpos slot).le]
    have hright : ∀ slot : Fin slotCount,
        ((atom slot ⬝ᵥ probe) / Real.sqrt (scale slot)) ^ 2
          = (atom slot ⬝ᵥ probe) ^ 2 / scale slot := by
      intro slot
      rw [div_pow, Real.sq_sqrt (hpos slot).le]
    calc (∑ slot, (atom slot ⬝ᵥ probe) ^ 2) ^ 2
        = (∑ slot, (Real.sqrt (scale slot) * (atom slot ⬝ᵥ probe))
            * ((atom slot ⬝ᵥ probe) / Real.sqrt (scale slot))) ^ 2 := by
          rw [Finset.sum_congr rfl fun slot _ => hcell slot]
      _ ≤ (∑ slot, (Real.sqrt (scale slot) * (atom slot ⬝ᵥ probe)) ^ 2)
            * ∑ slot, ((atom slot ⬝ᵥ probe) / Real.sqrt (scale slot)) ^ 2 := by
          simpa using hkey
      _ = (∑ slot, scale slot * (atom slot ⬝ᵥ probe) ^ 2)
            * ∑ slot, (atom slot ⬝ᵥ probe) ^ 2 / scale slot := by
          rw [Finset.sum_congr rfl fun slot _ => hleft slot,
            Finset.sum_congr rfl fun slot _ => hright slot]
  have hscaled : (∑ slot, scale slot * (atom slot ⬝ᵥ probe) ^ 2)
      ≤ (∑ slot, scale slot) * (probe ⬝ᵥ probe) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun slot _ => ?_
    exact mul_le_mul_of_nonneg_left
      (atom_energy_le_probe_energy atom hframe probe slot) (hpos slot).le
  have hreciprocalNonneg : 0 ≤ ∑ slot, (atom slot ⬝ᵥ probe) ^ 2 / scale slot :=
    Finset.sum_nonneg fun slot _ => div_nonneg (sq_nonneg _) (hpos slot).le
  have hscaleNonneg : 0 ≤ ∑ slot, scale slot :=
    Finset.sum_nonneg fun slot _ => (hpos slot).le
  rw [hsum] at hcauchy
  rcases eq_or_lt_of_le hnormNonneg with hzero | hposNorm
  · rw [← hzero]
    exact mul_nonneg hscaleNonneg hreciprocalNonneg
  · have hchain : (probe ⬝ᵥ probe) ^ 2
        ≤ (∑ slot, scale slot) * (probe ⬝ᵥ probe)
          * ∑ slot, (atom slot ⬝ᵥ probe) ^ 2 / scale slot :=
      le_trans hcauchy (mul_le_mul_of_nonneg_right hscaled hreciprocalNonneg)
    nlinarith [hchain, hposNorm]

/-! ## Layer 6 — the plane shadow -/

/-- The SHADOW of a vector in the plane orthogonal to an axis. -/
noncomputable def planeShadow {rank : ℕ} (axis vec : Fin rank → ℝ) : Fin rank → ℝ :=
  fun index => vec index - ((vec ⬝ᵥ axis) / (axis ⬝ᵥ axis)) * axis index

theorem planeShadow_apply {rank : ℕ} (axis vec : Fin rank → ℝ) (index : Fin rank) :
    planeShadow axis vec index
      = vec index - ((vec ⬝ᵥ axis) / (axis ⬝ᵥ axis)) * axis index := rfl

theorem planeShadow_eq {rank : ℕ} (axis vec : Fin rank → ℝ) :
    planeShadow axis vec
      = fun index => vec index - ((vec ⬝ᵥ axis) / (axis ⬝ᵥ axis)) * axis index := rfl

/-- The reading of a shifted vector against a direction. -/
theorem dot_sub_smul {rank : ℕ} (vec axis direction : Fin rank → ℝ) (coef : ℝ) :
    (fun index => vec index - coef * axis index) ⬝ᵥ direction
      = vec ⬝ᵥ direction - coef * (axis ⬝ᵥ direction) := by
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun index _ => by ring

/-- The square reading of a shifted vector against itself. -/
theorem dot_sub_smul_self {rank : ℕ} (vec axis : Fin rank → ℝ) (coef : ℝ) :
    (fun index => vec index - coef * axis index) ⬝ᵥ
        (fun index => vec index - coef * axis index)
      = vec ⬝ᵥ vec - 2 * coef * (vec ⬝ᵥ axis) + coef ^ 2 * (axis ⬝ᵥ axis) := by
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun index _ => by ring

/-- The shadow is orthogonal to the axis. -/
theorem planeShadow_dot_axis {rank : ℕ} (axis vec : Fin rank → ℝ)
    (haxis : axis ⬝ᵥ axis ≠ 0) : planeShadow axis vec ⬝ᵥ axis = 0 := by
  rw [planeShadow_eq, dot_sub_smul]
  field_simp
  ring

/-- In the plane the shadow reads exactly as the vector itself. -/
theorem planeShadow_dot_plane {rank : ℕ} (axis vec direction : Fin rank → ℝ)
    (hdirection : direction ⬝ᵥ axis = 0) :
    planeShadow axis vec ⬝ᵥ direction = vec ⬝ᵥ direction := by
  rw [planeShadow_eq, dot_sub_smul, dotProduct_comm axis direction, hdirection,
    mul_zero, sub_zero]

/-- **THE SHADOW ENERGY CAP.**  The shadow never carries more energy than
the vector: the difference is the square of the axis component. -/
theorem planeShadow_energy_le {rank : ℕ} (axis vec : Fin rank → ℝ)
    (haxis : 0 < axis ⬝ᵥ axis) :
    planeShadow axis vec ⬝ᵥ planeShadow axis vec ≤ vec ⬝ᵥ vec := by
  have hne : axis ⬝ᵥ axis ≠ 0 := ne_of_gt haxis
  rw [planeShadow_eq, dot_sub_smul_self]
  have hkey : 2 * ((vec ⬝ᵥ axis) / (axis ⬝ᵥ axis)) * (vec ⬝ᵥ axis)
      - ((vec ⬝ᵥ axis) / (axis ⬝ᵥ axis)) ^ 2 * (axis ⬝ᵥ axis)
      = (vec ⬝ᵥ axis) ^ 2 / (axis ⬝ᵥ axis) := by
    field_simp
    ring
  have hnonneg : 0 ≤ (vec ⬝ᵥ axis) ^ 2 / (axis ⬝ᵥ axis) :=
    div_nonneg (sq_nonneg _) haxis.le
  linarith [hkey, hnonneg]

/-- The blend of the shadows is the shadow of the blend. -/
theorem atomBlend_planeShadow {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (axis : Fin rank → ℝ)
    (probe : Fin slotCount → ℝ) :
    atomBlend (fun slot => planeShadow axis (atom slot)) probe
      = planeShadow axis (atomBlend atom probe) := by
  classical
  funext index
  have hleft : atomBlend (fun slot => planeShadow axis (atom slot)) probe index
      = (∑ slot, probe slot * atom slot index)
        - (∑ slot, probe slot * ((atom slot ⬝ᵥ axis) / (axis ⬝ᵥ axis)))
          * axis index := by
    rw [atomBlend_apply, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun slot _ => by
      simp only [planeShadow_apply]; ring
  have hcoef : (∑ slot, probe slot * ((atom slot ⬝ᵥ axis) / (axis ⬝ᵥ axis)))
      = (atomBlend atom probe ⬝ᵥ axis) / (axis ⬝ᵥ axis) := by
    rw [atomBlend_dot, Finset.sum_div]
    exact Finset.sum_congr rfl fun slot _ => by rw [mul_div_assoc]
  rw [hleft, hcoef, planeShadow_apply, atomBlend_apply]

/-! ## Layer 7 — the plane pair residue and the boundary deflation -/

/-- **THE PLANE PAIR CEILING.**  Six vectors that lie in the plane
orthogonal to an axis and form a tight frame OF THAT PLANE, together with
six nonnegative scales of total less than one, carry a PAIR of atoms whose
shifted form is strictly positive on every nonzero vector supported there.

This is the two-dimensional residue.  It carries no crux, no chart, no
frame and no combinatorics, and it is strictly smaller than the atom
triple ceiling: the ambient dimension is two, not three, and the carrier
is a pair, not a triple. -/
def AtomPairCeilingClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) (axis : Fin 3 → ℝ),
    (0 : ℝ) < axis ⬝ᵥ axis →
    (∀ slot, atom slot ⬝ᵥ axis = 0) →
    (∀ slot, 0 ≤ scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → direction ⬝ᵥ axis = 0 →
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction))
        = probe ⬝ᵥ direction) →
    ∃ car : Finset (Fin 6), car.card = 2
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
          (∑ slot, scale slot * probe slot ^ 2)
            < atomBlend atom probe ⬝ᵥ atomBlend atom probe

/-- **THE BOUNDARY DEFLATION.**  At an atom of ZERO scale and nonzero
energy the plane pair ceiling supplies a dominating TRIPLE: the shadows of
the atoms in the plane orthogonal to the boundary atom form a tight frame
of that plane, the pair residue dominates there, and the boundary atom
joins the pair for free, because the shadow energy never exceeds the atom
energy and the boundary scale contributes nothing. -/
theorem atomBoundaryTripleCeiling_of_atomPairCeiling
    (hpair : AtomPairCeilingClosed)
    (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) (boundary : Fin 6)
    (hnonneg : ∀ slot, 0 ≤ scale slot)
    (hboundaryZero : scale boundary = 0)
    (hboundaryEnergy : (0 : ℝ) < atom boundary ⬝ᵥ atom boundary)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction))
        = probe ⬝ᵥ direction) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
          (∑ slot, scale slot * probe slot ^ 2)
            < atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  set axis := atom boundary with haxisDef
  have haxisNe : axis ⬝ᵥ axis ≠ 0 := ne_of_gt hboundaryEnergy
  have hshadowBoundary : planeShadow axis (atom boundary) = 0 := by
    funext index
    rw [planeShadow_apply, ← haxisDef, div_self haxisNe, one_mul, sub_self]
    rfl
  have hshadowFrame : ∀ probe direction : Fin 3 → ℝ,
      probe ⬝ᵥ axis = 0 → direction ⬝ᵥ axis = 0 →
      (∑ slot, (planeShadow axis (atom slot) ⬝ᵥ probe)
          * (planeShadow axis (atom slot) ⬝ᵥ direction))
        = probe ⬝ᵥ direction := by
    intro probe direction hprobe hdirection
    rw [← hframe probe direction]
    exact Finset.sum_congr rfl fun slot _ => by
      rw [planeShadow_dot_plane axis (atom slot) probe hprobe,
        planeShadow_dot_plane axis (atom slot) direction hdirection]
  obtain ⟨pair, hpairCard, hpairDominates⟩ :=
    hpair (fun slot => planeShadow axis (atom slot)) scale axis hboundaryEnergy
      (fun slot => planeShadow_dot_axis axis (atom slot) haxisNe) hnonneg hsmall
      hshadowFrame
  -- the boundary atom is never in the dominating pair: its shadow vanishes
  have hboundaryNotMem : boundary ∉ pair := by
    intro hmem
    set indicator : Fin 6 → ℝ := fun slot => if slot = boundary then 1 else 0
      with hindicator
    have hvanish : ∀ slot ∉ pair, indicator slot = 0 := by
      intro slot hnot
      rw [hindicator]
      simp only
      rw [if_neg]
      intro heq
      exact hnot (heq ▸ hmem)
    have hne : indicator ≠ 0 := by
      intro hzero
      have hcell := congrFun hzero boundary
      rw [hindicator] at hcell
      simp at hcell
    have hstrict := hpairDominates indicator hvanish hne
    have hleft : (∑ slot, scale slot * indicator slot ^ 2) = 0 := by
      refine Finset.sum_eq_zero fun slot _ => ?_
      by_cases heq : slot = boundary
      · rw [heq, hboundaryZero, zero_mul]
      · rw [hindicator]
        simp only
        rw [if_neg heq]
        ring
    have hright : atomBlend (fun slot => planeShadow axis (atom slot)) indicator
        ⬝ᵥ atomBlend (fun slot => planeShadow axis (atom slot)) indicator = 0 := by
      have hblend : atomBlend (fun slot => planeShadow axis (atom slot)) indicator
          = 0 := by
        funext index
        rw [atomBlend_apply]
        refine Finset.sum_eq_zero fun slot _ => ?_
        by_cases heq : slot = boundary
        · rw [heq, hshadowBoundary]
          simp
        · rw [hindicator]
          simp only
          rw [if_neg heq, zero_mul]
      rw [hblend]
      simp
    rw [hleft, hright] at hstrict
    exact absurd hstrict (lt_irrefl 0)
  refine ⟨insert boundary pair, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hboundaryNotMem, hpairCard]
  intro probe hvanish hne
  set trimmed : Fin 6 → ℝ := fun slot => if slot = boundary then 0 else probe slot
    with htrimmed
  have htrimmedVanish : ∀ slot ∉ pair, trimmed slot = 0 := by
    intro slot hnot
    rw [htrimmed]
    simp only
    by_cases heq : slot = boundary
    · rw [if_pos heq]
    · rw [if_neg heq]
      refine hvanish slot ?_
      intro hmem
      rcases Finset.mem_insert.mp hmem with hcase | hcase
      · exact heq hcase
      · exact hnot hcase
  have hscaleEq : (∑ slot, scale slot * trimmed slot ^ 2)
      = ∑ slot, scale slot * probe slot ^ 2 := by
    refine Finset.sum_congr rfl fun slot _ => ?_
    by_cases heq : slot = boundary
    · rw [heq, hboundaryZero, zero_mul, zero_mul]
    · rw [htrimmed]
      simp only
      rw [if_neg heq]
  have hblendEq : atomBlend (fun slot => planeShadow axis (atom slot)) trimmed
      = atomBlend (fun slot => planeShadow axis (atom slot)) probe := by
    funext index
    rw [atomBlend_apply, atomBlend_apply]
    refine Finset.sum_congr rfl fun slot _ => ?_
    by_cases heq : slot = boundary
    · rw [heq, hshadowBoundary]
      simp
    · rw [htrimmed]
      simp only
      rw [if_neg heq]
  by_cases htrimmedZero : trimmed = 0
  · -- the probe lives on the boundary atom alone
    have hoff : ∀ slot, slot ≠ boundary → probe slot = 0 := by
      intro slot hslot
      have := congrFun htrimmedZero slot
      rw [htrimmed] at this
      simpa [hslot] using this
    have hboundaryNe : probe boundary ≠ 0 := by
      intro hzero
      exact hne (funext fun slot => by
        by_cases heq : slot = boundary
        · rw [heq, hzero]; rfl
        · rw [hoff slot heq]; rfl)
    have hleft : (∑ slot, scale slot * probe slot ^ 2) = 0 := by
      refine Finset.sum_eq_zero fun slot _ => ?_
      by_cases heq : slot = boundary
      · rw [heq, hboundaryZero, zero_mul]
      · rw [hoff slot heq]
        ring
    have hblend : atomBlend atom probe = fun index => probe boundary * axis index := by
      funext index
      rw [atomBlend_apply]
      rw [Finset.sum_eq_single boundary
        (fun slot _ hslot => by rw [hoff slot hslot, zero_mul])
        (fun hnot => absurd (Finset.mem_univ _) hnot)]
    have hright : atomBlend atom probe ⬝ᵥ atomBlend atom probe
        = probe boundary ^ 2 * (axis ⬝ᵥ axis) := by
      rw [hblend, dotProduct, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun index _ => by ring
    rw [hleft, hright]
    have hsqPos : 0 < probe boundary ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hboundaryNe))
    exact mul_pos hsqPos hboundaryEnergy
  · have hstrict := hpairDominates trimmed htrimmedVanish htrimmedZero
    rw [hscaleEq, hblendEq] at hstrict
    refine lt_of_lt_of_le hstrict ?_
    rw [atomBlend_planeShadow atom axis probe]
    exact planeShadow_energy_le axis (atomBlend atom probe) hboundaryEnergy

/-- The chart diagonal is positive at an atom of vanishing shifted
weight: the gap diagonal is positive and the weight is the negative of
the chart value. -/
theorem SixThreeCrux.chart_diagonal_pos_of_shift_zero (crux : SixThreeCrux)
    {atomIndex : Fin 6}
    (hzero : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex = 0) :
    0 < (chartPointOfDesign crux.design).chart atomIndex atomIndex := by
  have hgap := crux.gap_diagonal_pos_of_allHeavy atomIndex
  have hentry : chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomIndex atomIndex
      = (chartPointOfDesign crux.design).chart atomIndex atomIndex
        - (chartPointOfDesign crux.design).weight atomIndex := by
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_eq]
  rw [hentry] at hgap
  have hneg := crux.hasNegativeChartValue
  linarith

/-- **THE BOUNDARY CRUX KILL.**  A crux with an atom of vanishing shifted
weight dies from the PLANE residue alone. -/
theorem SixThreeCrux.false_of_atomPairCeiling_of_shift_zero (crux : SixThreeCrux)
    (hpair : AtomPairCeilingClosed) {boundary : Fin 6}
    (hzero : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight boundary = 0) :
    False := by
  classical
  set point := chartPointOfDesign crux.design with hpoint
  set value := chartObjective point with hvalue
  obtain ⟨family, hnorm, horth, hsplit⟩ :=
    exists_orthonormal_family_of_trace 3 point.chart point.isSymmetric
      point.isIdempotent point.hasTraceRank
  have henergy : (0 : ℝ) < atomVec family boundary ⬝ᵥ atomVec family boundary := by
    rw [← atomVec_dot_eq_split_apply hsplit boundary boundary]
    exact crux.chart_diagonal_pos_of_shift_zero hzero
  obtain ⟨car, hcard, hdominates⟩ :=
    atomBoundaryTripleCeiling_of_atomPairCeiling hpair (atomVec family)
      (fun atomIndex => value + point.weight atomIndex) boundary
      crux.shifted_weight_nonneg hzero henergy crux.shifted_weight_sum_lt_one
      (atom_frame_law hnorm horth)
  obtain ⟨probe, hvanish, hne, hwitness⟩ := crux.exists_ceiling_witness hsplit hcard
  exact absurd (hdominates probe hvanish hne) (not_lt.mpr hwitness)

/-- **THE PLANE RESIDUE MAKES EVERY CRUX INTERIOR.**  Every interiority
hypothesis of the campaign is discharged by the plane pair ceiling. -/
theorem SixThreeCrux.shifted_weight_pos_of_atomPairCeiling (crux : SixThreeCrux)
    (hpair : AtomPairCeilingClosed) (atomIndex : Fin 6) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex :=
  (crux.shifted_weight_nonneg atomIndex).lt_of_ne fun heq =>
    crux.false_of_atomPairCeiling_of_shift_zero hpair heq.symm

/-- The campaign-level interiority input, from the plane residue. -/
theorem forall_shifted_weight_pos_of_atomPairCeiling
    (hpair : AtomPairCeilingClosed) :
    ∀ (crux : SixThreeCrux) (atomIndex : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex :=
  fun crux atomIndex => crux.shifted_weight_pos_of_atomPairCeiling hpair atomIndex

/-- **THE RANK-FIVE DENSE PROFILE A FROM THE PLANE RESIDUE.**  The
heavy-five profile hands a boundary atom outright — the full-carrier
quantization pins its shifted weight to zero — thus the whole profile
closes in two dimensions. -/
theorem rankFiveDenseHeavyFiveClosed_of_atomPairCeiling
    (hpair : AtomPairCeilingClosed) : RankFiveDenseHeavyFiveClosed := by
  intro crux _frame heavyAtom _hthree _hfive _hdoubles _htrace hheavyZero
  exact crux.false_of_atomPairCeiling_of_shift_zero hpair hheavyZero

/-- The residual cycle cell of profile A closes in two dimensions too. -/
theorem rankFiveDenseHeavyFiveDistinctClosed_of_atomPairCeiling
    (hpair : AtomPairCeilingClosed) :
    RankFiveDenseHeavyFiveDistinctClosed := by
  intro crux _frame heavyAtom _hthree _hfive _hdoubles _htrace hheavyZero _hdistinct
  exact crux.false_of_atomPairCeiling_of_shift_zero hpair hheavyZero

/-! ## Layer 8 — the pair criterion of the plane residue -/

/-- The reading of a two-term combination against itself. -/
theorem dot_two_combination {rank : ℕ} (vecOne vecTwo : Fin rank → ℝ)
    (coefOne coefTwo : ℝ) :
    (fun index => coefOne * vecOne index + coefTwo * vecTwo index)
        ⬝ᵥ (fun index => coefOne * vecOne index + coefTwo * vecTwo index)
      = coefOne ^ 2 * (vecOne ⬝ᵥ vecOne)
        + 2 * coefOne * coefTwo * (vecOne ⬝ᵥ vecTwo)
        + coefTwo ^ 2 * (vecTwo ⬝ᵥ vecTwo) := by
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun index _ => by ring

/-- **THE TWO-BY-TWO SYLVESTER CRITERION.**  A binary quadratic form with a
positive first coefficient and a positive determinant is positive on every
nonzero pair.  The completion of the square carries the whole proof. -/
theorem pair_form_pos {gapOne gapTwo cross coefOne coefTwo : ℝ}
    (hgap : 0 < gapOne) (hdet : cross ^ 2 < gapOne * gapTwo)
    (hne : coefOne ≠ 0 ∨ coefTwo ≠ 0) :
    0 < gapOne * coefOne ^ 2 + 2 * cross * coefOne * coefTwo
      + gapTwo * coefTwo ^ 2 := by
  have hsquare : gapOne * (gapOne * coefOne ^ 2 + 2 * cross * coefOne * coefTwo
        + gapTwo * coefTwo ^ 2)
      = (gapOne * coefOne + cross * coefTwo) ^ 2
        + (gapOne * gapTwo - cross ^ 2) * coefTwo ^ 2 := by ring
  rcases eq_or_ne coefTwo 0 with hzero | hpos
  · have hfirst : coefOne ≠ 0 := by
      rcases hne with hcase | hcase
      · exact hcase
      · exact absurd hzero hcase
    have hsq : 0 < coefOne ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hfirst))
    rw [hzero]
    nlinarith [hgap, hsq]
  · have hsq : 0 < coefTwo ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hpos))
    nlinarith [hsquare, hgap, hsq, sq_nonneg (gapOne * coefOne + cross * coefTwo)]

/-- **THE PLANE PAIR GRAM RESIDUE.**  The same data as the plane pair
ceiling, with the conclusion in the ATOM GRAM: two slots whose shifted
energies are positive and whose shifted product exceeds the square of
their cross reading.

This is the shape a certificate produces.  The search is finite — fifteen
unordered pairs — and each test is one polynomial inequality in the atom
Gram and the scales, with no eigenvalue, no square root and no
compactness. -/
def AtomPairGramClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) (axis : Fin 3 → ℝ),
    (0 : ℝ) < axis ⬝ᵥ axis →
    (∀ slot, atom slot ⬝ᵥ axis = 0) →
    (∀ slot, 0 ≤ scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → direction ⬝ᵥ axis = 0 →
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction))
        = probe ⬝ᵥ direction) →
    ∃ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo
      ∧ 0 < atom slotOne ⬝ᵥ atom slotOne - scale slotOne
      ∧ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2
          < (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
            * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)

/-- **THE PAIR CRITERION IS THE PLANE RESIDUE.**  The Gram criterion at
one pair dominates every nonzero probe supported on that pair: the probe
energy of the pair is a binary quadratic form, and the criterion is its
Sylvester test. -/
theorem atomPairCeilingClosed_of_gram (hgram : AtomPairGramClosed) :
    AtomPairCeilingClosed := by
  classical
  intro atom scale axis haxis hplane hnonneg hsmall hframe
  obtain ⟨slotOne, slotTwo, hslotNe, hgapPos, hdet⟩ :=
    hgram atom scale axis haxis hplane hnonneg hsmall hframe
  refine ⟨{slotOne, slotTwo}, Finset.card_pair hslotNe, fun probe hvanish hne => ?_⟩
  set coefOne := probe slotOne with hcoefOne
  set coefTwo := probe slotTwo with hcoefTwo
  have hrestrict : ∀ combine : Fin 6 → ℝ,
      (∀ slot ∉ ({slotOne, slotTwo} : Finset (Fin 6)), combine slot = 0) →
      (∑ slot, combine slot) = combine slotOne + combine slotTwo := by
    intro combine hoff
    rw [← Finset.sum_subset (Finset.subset_univ ({slotOne, slotTwo} : Finset (Fin 6)))
      (fun slot _ hnot => hoff slot hnot), Finset.sum_pair hslotNe]
  have hscaleSum : (∑ slot, scale slot * probe slot ^ 2)
      = scale slotOne * coefOne ^ 2 + scale slotTwo * coefTwo ^ 2 := by
    refine hrestrict (fun slot => scale slot * probe slot ^ 2) fun slot hnot => ?_
    rw [hvanish slot hnot]
    ring
  have hblend : atomBlend atom probe
      = fun index => coefOne * atom slotOne index + coefTwo * atom slotTwo index := by
    funext index
    rw [atomBlend_apply]
    exact hrestrict (fun slot => probe slot * atom slot index) fun slot hnot => by
      rw [hvanish slot hnot, zero_mul]
  have hcoefNe : coefOne ≠ 0 ∨ coefTwo ≠ 0 := by
    by_contra hboth
    rw [not_or, not_not, not_not] at hboth
    refine hne (funext fun slot => ?_)
    by_cases hone : slot = slotOne
    · rw [hone, ← hcoefOne, hboth.1]; rfl
    by_cases htwo : slot = slotTwo
    · rw [htwo, ← hcoefTwo, hboth.2]; rfl
    rw [hvanish slot (fun hmem => by
      rcases Finset.mem_insert.mp hmem with hcase | hcase
      · exact hone hcase
      · exact htwo (Finset.mem_singleton.mp hcase))]
    rfl
  have hform := pair_form_pos (gapOne := atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
    (gapTwo := atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)
    (cross := atom slotOne ⬝ᵥ atom slotTwo) (coefOne := coefOne) (coefTwo := coefTwo)
    hgapPos hdet hcoefNe
  rw [hscaleSum, hblend, dot_two_combination]
  nlinarith [hform]

/-- **THE RANK-FIVE PROFILE A FROM THE PAIR CRITERION.**  Profile A of the
rank-five dense branch closes from one polynomial inequality in the atom
Gram of the plane. -/
theorem rankFiveDenseHeavyFiveClosed_of_atomPairGram
    (hgram : AtomPairGramClosed) : RankFiveDenseHeavyFiveClosed :=
  rankFiveDenseHeavyFiveClosed_of_atomPairCeiling
    (atomPairCeilingClosed_of_gram hgram)

/-- The residual cycle cell of profile A from the pair criterion. -/
theorem rankFiveDenseHeavyFiveDistinctClosed_of_atomPairGram
    (hgram : AtomPairGramClosed) : RankFiveDenseHeavyFiveDistinctClosed :=
  rankFiveDenseHeavyFiveDistinctClosed_of_atomPairCeiling
    (atomPairCeilingClosed_of_gram hgram)

/-- The boundary stratum of the whole campaign, from the pair criterion:
every crux is interior. -/
theorem forall_shifted_weight_pos_of_atomPairGram (hgram : AtomPairGramClosed) :
    ∀ (crux : SixThreeCrux) (atomIndex : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex :=
  forall_shifted_weight_pos_of_atomPairCeiling
    (atomPairCeilingClosed_of_gram hgram)

end Gtz
