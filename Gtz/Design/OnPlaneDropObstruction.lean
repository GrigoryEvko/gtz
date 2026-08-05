/-
# Branch (i): the tie-side geometry of the drop residuals

Three kernel facts about the branch-(i) residual family, all from landed
transports, none conditional.

* `exists_outside_offPlane_of_tight` — the Fact-B insert is OFF-PLANE: some
  atom outside a tight subset has nonzero axis pairing (its axis mass is at
  least the axis norm, which is one).

* `not_pairPlaneStrict_of_isTie_of_onPlaneDrop` — **THE ON-PLANE DROP IS
  IMPOSSIBLE AT A TIE** (any size, any rank, complement nonempty).  If an atom
  of a tight dominating `rank`-subset lies exactly on the tight plane and the
  remaining atoms dominated that plane strictly, then inserting the Fact-B
  off-plane outsider would produce a strictly dominating `rank`-subset
  (`Gtz.posDef_exchangeTriple_of_planarPairStrict`), which a tie forbids.  So
  the witness set of the tight-axis lane's residual `TightDropOnPlaneSixThree`
  is EMPTY at every tie: the exact on-plane drop is not a weaker target than
  the hinge, it is a disguise of it.  In plane-pivot vocabulary this is the
  boundary case of the window pivot law: an on-plane insider of a tight triple
  always has plane pivot at least one.

* `exists_gateFailure_of_isTie` — **THE EXCHANGE SYSTEM OF A TIE, EXTRACTED.**
  At a tie, for every tight subset and every exchange with axis-mass excess,
  the tight-axis gate fails at some witness plane direction:

      (a_add^2 - a_drop^2) * (sum_{c in Q} (g_c . planar)^2 - |planar|^2)
        <= (a_add * (g_drop . planar) - a_drop * (g_add . planar))^2 .

  This is the kernel-checked form of the nine per-triple tie inequalities the
  averaging programme consumes (the `X_ce >= 0` system of the lane report).

* `tightDropOnPlaneSixThree_iff_stressFreeHinge` — the on-plane residual is
  EXACTLY the stress-free hinge: forward by the off-plane insert and the
  planar-pair transport (tree-only, no budget needed), backward vacuously via
  `Gtz.stressFreeHingeHoldsSixThree_iff_no_stressFree_tie`.

* `tightDropWithinBudget_of_stressFreeHinge` — the backward wiring for the
  budget residual of `Gtz.Design.AxisMassBudgetTransport`: the hinge makes its
  hypotheses contradictory, so the residual follows.  Together with that
  module's `stressFreeHingeHoldsSixThree_of_tightDropWithinBudget` the two are
  equivalent — the budget residual is not logically weaker than the hinge
  either; its value is purely as an attack interface (an open region whose
  non-emptiness must be derived from the tie inequalities themselves).

The residual `Prop`s are the tree's `TightDropOnPlaneSixThree`
(`Gtz.Design.TightAxisPairBudget`) and `TightDropWithinBudgetSixThree`
(`Gtz.Design.AxisMassBudgetTransport`).
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Design.TwoPoleStratum
import Gtz.Design.StressFreeNormalizer
import Gtz.Design.TightAxisPairBudget
import Gtz.Design.AxisMassBudgetTransport
import Gtz.Reduction.TrichotomyLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Part 1: the Fact-B insert is off-plane -/

/-- **The insert candidate is off-plane.**  Outside a tight subset of a unit
axis some atom has axis mass at least one, hence nonzero axis pairing. -/
theorem exists_outside_offPlane_of_tight (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hproper : selectedᶜ.Nonempty)
    {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0) :
    ∃ addLabel : Fin size, addLabel ∉ selected
      ∧ design.atom addLabel ⬝ᵥ axis ≠ 0 := by
  obtain ⟨addLabel, haddMem, haddBig⟩ :=
    exists_outside_axisMass_ge design hproper htight
  refine ⟨addLabel, Finset.mem_compl.mp haddMem, ?_⟩
  intro hzero
  rw [hunit, hzero] at haddBig
  norm_num at haddBig

/-! ## Part 2: the on-plane drop is impossible at a tie -/

/-- **THE ON-PLANE DROP IS IMPOSSIBLE AT A TIE.**  At any tie, for any tight
dominating `rank`-subset with a proper complement and any of its atoms lying
exactly on the tight plane, the remaining atoms do NOT dominate the plane
strictly: otherwise the off-plane Fact-B outsider would complete them to a
strictly dominating `rank`-subset.  The witness set of the on-plane drop
residual is therefore empty at every tie. -/
theorem not_pairPlaneStrict_of_isTie_of_onPlaneDrop (design : WeightedDesign size rank)
    (htie : IsTie design) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) (hproper : selectedᶜ.Nonempty)
    (hdominates : Dominates design selected) {axis : Fin rank → ℝ}
    (hunit : axis ⬝ᵥ axis = 1)
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0)
    {dropLabel : Fin size} (hdrop : dropLabel ∈ selected)
    (hdropOnPlane : design.atom dropLabel ⬝ᵥ axis = 0) :
    ¬ ∀ planar : Fin rank → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
        planar ⬝ᵥ planar
          < ∑ atomIndex ∈ selected.erase dropLabel,
              (design.atom atomIndex ⬝ᵥ planar) ^ 2 := by
  intro hpairStrict
  obtain ⟨addLabel, haddNot, haddOffPlane⟩ :=
    exists_outside_offPlane_of_tight design hproper hunit htight
  exact htie.2 (insert addLabel (selected.erase dropLabel))
    (by rw [card_exchangeSubset selected hdrop haddNot, hcard])
    (posDef_exchangeTriple_of_planarPairStrict design hdominates hunit htight hdrop
      haddNot hdropOnPlane haddOffPlane hpairStrict)

/-! ## Part 3: the tie's exchange system, extracted -/

/-- **THE GATE FAILS SOMEWHERE AT A TIE.**  For every exchange with axis-mass
excess at a tight subset of a tie, some plane direction witnesses the failure
of the tight-axis coupling gate.  This is the tie's nine-fold exchange
inequality system in kernel form. -/
theorem exists_gateFailure_of_isTie (design : WeightedDesign size rank)
    (htie : IsTie design) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) (hdominates : Dominates design selected)
    {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0)
    {dropLabel addLabel : Fin size} (hdrop : dropLabel ∈ selected)
    (haddNot : addLabel ∉ selected)
    (hexcess : (design.atom dropLabel ⬝ᵥ axis) ^ 2
      < (design.atom addLabel ⬝ᵥ axis) ^ 2) :
    ∃ planar : Fin rank → ℝ, planar ⬝ᵥ axis = 0 ∧ planar ≠ 0
      ∧ ((design.atom addLabel ⬝ᵥ axis) ^ 2 - (design.atom dropLabel ⬝ᵥ axis) ^ 2)
            * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
              - planar ⬝ᵥ planar)
          ≤ ((design.atom addLabel ⬝ᵥ axis) * (design.atom dropLabel ⬝ᵥ planar)
              - (design.atom dropLabel ⬝ᵥ axis)
                * (design.atom addLabel ⬝ᵥ planar)) ^ 2 := by
  by_contra hnoWitness
  push Not at hnoWitness
  refine htie.2 (insert addLabel (selected.erase dropLabel))
    (by rw [card_exchangeSubset selected hdrop haddNot, hcard])
    (posDef_exchangeTriple_of_tightAxisGate design hdominates hunit htight hdrop
      haddNot hexcess ?_)
  intro planar hplanarOrth hplanarNe
  exact hnoWitness planar hplanarOrth hplanarNe

/-! ## Part 4: both drop residuals are exactly the stress-free hinge -/

/-- **The on-plane residual IS the stress-free hinge.**  Forward by the
transport above; backward vacuously, because the hinge empties the residual's
hypotheses (`Gtz.stressFreeHingeHoldsSixThree_iff_no_stressFree_tie`).  So the
tight-axis lane's target was never a weakening: at every tie its witness set
is empty (`not_pairPlaneStrict_of_isTie_of_onPlaneDrop`), and any proof of it
must first refute the stress-free tie outright. -/
theorem tightDropOnPlaneSixThree_iff_stressFreeHinge :
    TightDropOnPlaneSixThree ↔ StressFreeHingeHoldsSixThree := by
  constructor
  · exact stressFreeHingeHoldsSixThree_of_tightDropOnPlane
  · intro hhinge design hstressFree htie
    exact absurd htie
      (stressFreeHingeHoldsSixThree_iff_no_stressFree_tie.mp hhinge design hstressFree)

/-- **The budget residual follows from the hinge** (vacuously: the hinge
refutes its hypotheses).  With the forward transport of `Gtz.Design.AxisMassBudgetTransport` this makes the
budget residual EQUIVALENT to the hinge: weakening the drop to an open budget
region changed the attack surface, not the logical strength. -/
theorem tightDropWithinBudget_of_stressFreeHinge
    (hhinge : StressFreeHingeHoldsSixThree) : TightDropWithinBudgetSixThree := by
  intro design hstressFree htie
  exact absurd htie
    (stressFreeHingeHoldsSixThree_iff_no_stressFree_tie.mp hhinge design hstressFree)

end Gtz
