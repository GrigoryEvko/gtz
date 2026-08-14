import Gtz.Wave.PlaneRouteFoil

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12800000

/-!
# The plane test that the margin theorem actually delivers

`Gtz.HeavyPivotFoil` and `Gtz.PlaneRouteFoil` refute the two halves of the
pivot route as it was measured.  The plane half was refuted at the FULL
INFLATED SCALE `1/(1 - t_p)`, which the boundary theorem
`Gtz.exists_dominatingPlanePair_boundary` supplies.  That is not the only
plane test the campaign owns.

`Gtz.exists_dominatingPlanePair_margin` at the PLAIN scales of the five slots
off the pivot supplies a pair at the factor `1 + slack / 2`, where the slack
is `t_p` at mass one.  That factor is SMALLER than `1/(1 - t_p)`, because

  `(1 + t_p / 2) (1 - t_p) = 1 - t_p / 2 - t_p ^ 2 / 2 <= 1`.

The test at the smaller factor is therefore WEAKER, and the two foils do not
touch it.  This module names it, proves that it still carries the cell, proves
that the refuted test carries it, and proves that both foils PASS it at their
own covering triples.  It is the target that a successor lane must floor.

## The measurement

An adversarial descent of 3000 restarts by 30000 steps, at three seeds, does
not drive the weaker test below zero.  The floor reads `5.9e-9`, `7.8e-10` and
`1.2e-13`, and at each of the three data the binding half is the COVER and not
the plane.  At the two data that break the full inflation, at `-0.0043` and at
`-0.0023`, the weaker test reads exactly the plain cover margin, `+0.0209` and
`+0.0156`.

**A floor that approaches zero from above is not evidence.**  The campaign has
refuted two such floors already.  The measurement above is a starting point for
a successor lane and not a claim.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.AtomPairPlaneMarginDominates` — the plane test at the factor
  `1 + t_p / 2` on the plain scales.
* `Gtz.AtomLivePivotPlaneMarginCoverClosed` — the route at that test.
* `Gtz.atomPairPlaneMarginDominates_of_planeDominates` — **THE WEAKER TEST IS
  WEAKER.**  Domination at the full inflation carries it.
* `Gtz.atomLivePivotPlaneMarginCoverClosed_of_planeCover` — the refuted route
  carries the new one, so the new one is a genuine weakening.
* `Gtz.atomLivePivotCoverClosed_of_livePlaneMargin`,
  `Gtz.gtzWeighted_six_three_of_livePivotPlaneMarginCover` — **THE NEW ROUTE
  STILL CLOSES THE CELL.**
* `Gtz.heavyFoil_planeMargin_oneTwoFour`,
  `Gtz.planeFoil_planeMargin_threeFourFive` — **NEITHER FOIL TOUCHES IT.**
  Each foil passes the weaker test at its own covering triple.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the weaker plane test and its place -/

section MarginTest

/-- **THE PLANE TEST OF THE MARGIN THEOREM.**  Against a probe that the pivot
atom reads as zero, the plane reading of the pair beats the probe energy at the
factor `1 + t_p / 2`.  This is exactly what
`Gtz.exists_dominatingPlanePair_margin` supplies at the plain scales of the
five slots off the pivot. -/
def AtomPairPlaneMarginDominates (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (pivot slotOne slotTwo : Fin 6) : Prop :=
  ∀ probe : Fin 3 → ℝ, atom pivot ⬝ᵥ probe = 0 →
    (1 + scale pivot / 2) * (probe ⬝ᵥ probe)
      ≤ atomPivotPlaneRead atom scale slotOne slotTwo probe

/-- **THE ROUTE AT THE WEAKER PLANE TEST.**  A live pivot, a pair that passes
the weaker plane test, and a covering triple. -/
def AtomLivePivotPlaneMarginCoverClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ scale pivot < atomGram atom pivot pivot
        ∧ AtomPairPlaneMarginDominates atom scale pivot slotOne slotTwo
        ∧ AtomTripleCovers atom scale pivot slotOne slotTwo

/-- **THE WEAKER TEST IS WEAKER.**  Domination at the full inflated scale
`1/(1 - t_p)` carries domination at the factor `1 + t_p / 2`, because the
product `(1 + t_p / 2) (1 - t_p)` never passes one. -/
theorem atomPairPlaneMarginDominates_of_planeDominates
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ} {pivot slotOne slotTwo : Fin 6}
    (hpivotPos : 0 < scale pivot) (hpivotLt : scale pivot < 1)
    (honePos : 0 < scale slotOne) (htwoPos : 0 < scale slotTwo)
    (hdom : AtomPairPlaneDominates atom scale pivot slotOne slotTwo) :
    AtomPairPlaneMarginDominates atom scale pivot slotOne slotTwo := by
  intro probe hpolar
  have hstep := hdom probe hpolar
  have hread : 0 ≤ atomPivotPlaneRead atom scale slotOne slotTwo probe := by
    simp only [atomPivotPlaneRead]
    positivity
  have hgap : (1 + scale pivot / 2) * (1 - scale pivot) ≤ 1 := by nlinarith [hpivotPos]
  have hfactor : (0 : ℝ) < 1 + scale pivot / 2 := by linarith
  nlinarith [hstep, hread, hgap, hfactor]

/-- **THE REFUTED ROUTE CARRIES THE NEW ONE.**  The new route is therefore a
genuine weakening, and the two foils do not reach it. -/
theorem atomLivePivotPlaneMarginCoverClosed_of_planeCover
    (hroute : AtomLivePivotPlaneCoverClosed) : AtomLivePivotPlaneMarginCoverClosed := by
  intro atom scale hpos hmass hframe
  obtain ⟨pivot, slotOne, slotTwo, hpy, hpw, hyw, hlive, hplane, hcover⟩ :=
    hroute atom scale hpos hmass hframe
  refine ⟨pivot, slotOne, slotTwo, hpy, hpw, hyw, hlive, ?_, hcover⟩
  have hlt : scale pivot < 1 := by
    have hsum : scale pivot ≤ ∑ slot, scale slot :=
      Finset.single_le_sum (fun slot _ => (hpos slot).le) (Finset.mem_univ pivot)
    have hother : 0 < scale slotOne := hpos slotOne
    rw [hmass] at hsum
    rcases lt_or_eq_of_le hsum with hstrict | heq
    · exact hstrict
    · exfalso
      have hrest : (∑ slot ∈ Finset.univ.erase pivot, scale slot) = 0 := by
        have hsplit := Finset.add_sum_erase Finset.univ scale (Finset.mem_univ pivot)
        rw [hmass] at hsplit
        linarith [heq, hsplit]
      have hmem : slotOne ∈ Finset.univ.erase pivot :=
        Finset.mem_erase.mpr ⟨fun heqs => hpy heqs.symm, Finset.mem_univ slotOne⟩
      have hle : scale slotOne ≤ ∑ slot ∈ Finset.univ.erase pivot, scale slot :=
        Finset.single_le_sum (fun slot _ => (hpos slot).le) hmem
      linarith [hrest, hother, hle]
  exact atomPairPlaneMarginDominates_of_planeDominates (hpos pivot) hlt
    (hpos slotOne) (hpos slotTwo) hplane

/-- **THE NEW ROUTE STILL CLOSES THE CELL.** -/
theorem atomLivePivotCoverClosed_of_livePlaneMargin
    (hroute : AtomLivePivotPlaneMarginCoverClosed) : AtomLivePivotCoverClosed := by
  intro atom scale hpos hmass hframe
  obtain ⟨pivot, slotOne, slotTwo, hpy, hpw, hyw, hlive, -, hcover⟩ :=
    hroute atom scale hpos hmass hframe
  exact ⟨pivot, slotOne, slotTwo, hpy, hpw, hyw, hlive, hcover⟩

/-- **THE CELL FROM THE NEW ROUTE.** -/
theorem gtzWeighted_six_three_of_livePivotPlaneMarginCover
    (hroute : AtomLivePivotPlaneMarginCoverClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_livePivotCover
    (atomLivePivotCoverClosed_of_livePlaneMargin hroute)

end MarginTest

/-! ## Layer 2 — neither foil touches the weaker test -/

section FoilsPass

/-- **THE FOIL IN FIFTHS PASSES THE WEAKER TEST.**  At the pivot one the pair
of the slots two and four passes the plane test at the factor `23/20`, so the
foil of `Gtz.HeavyPivotFoil` refutes the full inflation and not the margin
theorem. -/
theorem heavyFoil_planeMargin_oneTwoFour :
    AtomPairPlaneMarginDominates heavyFoilAtom heavyFoilScale 1 2 4 := by
  intro probe hpolar
  rw [atomPivotPlaneRead, heavyFoilAtom_two, heavyFoilAtom_four,
    heavyFoilScale_one, heavyFoilScale_two, heavyFoilScale_four]
  rw [heavyFoilAtom_one] at hpolar
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    foilCons3_2] at hpolar ⊢
  have hthird : probe 2 = 3 / 2 * (probe 0 - probe 1) := by linarith
  rw [hthird]
  nlinarith [sq_nonneg (probe 0 - probe 1), sq_nonneg (probe 0 + probe 1),
    sq_nonneg (probe 0), sq_nonneg (probe 1)]

/-- **THE FOIL OVER THE ROOT OF THIRTEEN PASSES THE WEAKER TEST.**  At the
pivot three the pair of the slots four and five passes the plane test at the
factor `23/20`, so the foil of `Gtz.PlaneRouteFoil` refutes the full inflation
and not the margin theorem. -/
theorem planeFoil_planeMargin_threeFourFive :
    AtomPairPlaneMarginDominates planeFoilAtom planeFoilScale 3 4 5 := by
  intro probe hpolar
  rw [atomPivotPlaneRead, planeFoilAtom_dot_sq, planeFoilAtom_dot_sq]
  rw [planeFoilAtom_dot] at hpolar
  have hzero : planeFoilVec 3 ⬝ᵥ probe = 0 := by
    have hne : Real.sqrt 13 ≠ 0 := ne_of_gt planeFoilRoot_pos
    field_simp at hpolar
    simpa using hpolar
  simp only [planeFoilVec, planeFoilScale, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, foilCons3_2, foilCons4_2,
    foilCons4_3, foilCons5_2, foilCons5_3, foilCons5_4, foilCons6_3, foilCons6_4,
    foilCons6_5] at hzero ⊢
  have hfirst : probe 0 = 3 * probe 2 := by linarith
  rw [hfirst]
  nlinarith [sq_nonneg (probe 1 - probe 2), sq_nonneg (probe 1 + probe 2),
    sq_nonneg (probe 1), sq_nonneg (probe 2), sq_nonneg (probe 1 - 3 * probe 2)]

end FoilsPass

end Gtz
