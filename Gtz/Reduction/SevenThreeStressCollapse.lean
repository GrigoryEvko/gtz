/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.Reductions
import Gtz.Reduction.StressWalk
import Gtz.Reduction.StressConditionalWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The punctured-stress collapse of the top-plus-one cell

`Gtz.exists_dominating_of_stress` reduces a stressed design by one walk and then
needs EVERY strictly smaller cell, including the one immediately below.  At the
Veronese top plus one -- `(7,3)` at rank three -- that immediate cell is `(6,3)`,
the open cell itself, so the shipped arrow buys nothing there.

This file replaces the demand for the immediate cell by the strictly weaker demand
that STRESSED designs at the immediate cell be dominated, which at rank three is a
THEOREM (`Gtz.exists_dominating_sixThree_of_stress`).  The price is one extra
stress: the walk kills exactly one atom, and a second stress vanishing at that atom
survives the landing.

## The mechanism, and the one cardinality step the sketch hides

The walk `Gtz.exists_rescaledReducedDesign_of_stress` returns a landing of size
`smallSize < size + 1` together with an INJECTION of the survivors.  Two cases:

* `smallSize < size` -- at least two atoms died, and every cell strictly below the
  immediate one is assumed.  Nothing about the stress is spent in this branch: it
  DELEGATES to `hsmaller` outright;
* `smallSize = size` -- exactly one atom died.  This is the case the sketch calls
  "kills exactly one atom", and it is a cardinality fact, not an output of the
  walk: an injection `Fin size → Fin (size+1)` has an image of card `size`, whose
  complement has card ONE.  `Gtz.HasPuncturedStress` is then applied at that single
  label, and the stress it returns restricts along the injection.

The restriction is a stress of the LANDING because the walk rescales atoms
UNIFORMLY: `atomMatrix (Real.sqrt scale • g) = scale • atomMatrix g`, so a
dependency among the original atoms that vanishes off the survivors is, coefficient
for coefficient, a dependency among the rescaled survivors.  Nothing about which
atom died is needed beyond its label, and no internal of the shipped walk is read.

## What this buys, and what it does not

`Gtz.gtzWeighted_seven_three_iff_uniqueStress` is the payoff: since every `(7,3)`
design carries a stress at all (`Gtz.exists_parsevalNullDirection`, six functionals
on seven unknowns), and two independent stresses now DOMINATE unconditionally, the
`(7,3)` cell is open exactly on the stratum where the stress space is a LINE.
Combined with the shipped `Gtz.gtzWeighted_six_three_iff_seven_three` this says the
whole of weighted rank three lives on the unique-stress `(7,3)` stratum.

THAT SHRINK IS REAL BUT VERY WEAK, and the docstring of the iff says so rather than
leaving the reader to infer otherwise: the surviving stratum is GENERIC.  A stress
space of dimension at least two is a codimension-one condition, and a census of
96000 random `(7,3)` designs found stress dimension exactly one in 96000 of them
(measured, this campaign).  So the iff removes a measure-zero set of designs.  Its
value is that the removed set is exactly where the numerically accessible tie locus
sits -- every polished `(7,3)` chart minimiser measured in this campaign has stress
dimension two or three, because minimisers are parallel splittings -- so a `(7,3)`
counterexample cannot be sought there.

THIS PROVES NOTHING ABOUT `(6,3)`.  It narrows where a `(7,3)` counterexample may
live; `IsEmpty Gtz.SixThreeCrux` is untouched.

## The general statement, and why the top-level corollary is rank three only

`Gtz.exists_dominating_of_puncturedStress` is stated at general `(size + 1, rank)`.
Only its instantiation is rank-three-bound, and for one reason: the hypothesis
`hstressedTop` -- stressed designs at the immediate cell are dominated -- is a
theorem at `(6,3)` because `Gtz.gtzWeighted_of_le_five` closes everything the walk
can land on, and `6 - 1 = 5`.  At rank four the immediate cell is `(9,4)` and the
walk can land as low as `(6,4)`, which is not a theorem, so the general form must be
fed by whatever the rank-four ladder eventually supplies.  The general form is
stated so that it can be.

## The mass-free walk and the double landing

`Gtz.exists_rescaledReducedDesign_of_stress` hides three things behind existentials:
the walk's SCALE, the label the walk KILLS, and the SIGN of the stress at that
label.  All three are needed to walk a design in TWO directions and know the two
landings are different, and none is recoverable from the shipped statement.  The
second half of this file re-runs the walk under one extra hypothesis that makes all
three trivial.

Along `w(s) = t - s * z` the mass is exactly `1 - s * (∑ z)`.  Assume `∑ z = 0`.
Then the mass is IDENTICALLY ONE, so the landing needs no renormalisation at all and
its atoms are the survivors THEMSELVES, not `Real.sqrt scale` times them --
`Gtz.posSemidef_sub_one_of_smul_sub_one` is not invoked anywhere in that half, and
`Gtz.Dominates` transfers verbatim because `Gtz.subsetSum` is weight-free and the
atoms are literally equal.  The sign normalisation inside the shipped walk
(`Gtz.exists_rescaledReducedDesign_of_stress` flips its input exactly when the
coordinate sum is negative) is then a no-op, so the walk may be run at `z` AND at
`-z` and the two runs are genuinely different runs; and the killed label satisfies
`0 < z dead`, being an argmin of `t_c / z_c` over the RAISERS, so running at `-z`
kills a label where `z` is strictly NEGATIVE and the two dead labels are distinct
for free.

`∑ z = 0` is exactly the condition under which BOTH directions are usable, and it
cannot be dropped.  With `∑ z > 0` the `-z` direction RAISES the mass, the landing
is renormalised by `Real.sqrt scale > 1`, its atoms are LONGER, and a dominating
triple of that landing gives only `S ≥ scale⁻¹ • 1`, strictly weaker than `S ≥ 1`.
So off this stratum a counterexample yields ONE landing, not two, and the mass-free
locus is a hypersurface (measured: the scale-free mass defect `|∑ z| / ∑ |z|` has
median `0.3222` over 96000 random `(7,3)` designs, with fractions
`0.00150 / 0.01609 / 0.16210` below `1e-3 / 1e-2 / 1e-1` -- linear scaling, the
signature of codimension one).  The other side of the same mass law is the shipped
`Gtz.exists_posDef_sixThree_of_stress_sum_ne_zero`, which converts the strict mass
loss into STRICT domination; it lives at `(6,3)`, so it does not fire on a `(7,3)`
design and does not fire on a `(7,3)` landing either, that landing being stress-free.

## Non-vacuity

`Gtz.HasPuncturedStress` at `(7,3)` is not an empty hypothesis:
`Gtz.tripleCoincidentDesign` is a fully rational all-heavy `(7,3)` design with three
COINCIDENT atoms, hence a two-dimensional space of stresses supported on them, and
`Gtz.tripleCoincidentDesign_hasPuncturedStress` discharges the bundle of the C6
theorem outright.  Both of its exhibited stresses additionally have coordinate sum
zero, so the same design witnesses the mass-free hypothesis.

What is NOT witnessed, and cannot be, is the FULL bundle of the double landing: that
bundle also contains `hundominated`, and an undominated `(7,3)` design existing is
exactly the failure of the conjecture.  The honest reading is that the stress half of
every hypothesis bundle below is inhabited in the kernel and the undominated half is
the open problem.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The punctured-stress interface -/

/-- **The punctured-stress hypothesis.**  At every label the design carries a
nonzero stress VANISHING AT THAT LABEL.  This is exactly what a walk landing needs:
whichever atom the walk chooses to kill, a stress survives to the landing.

A design whose stress space has dimension at least two has the property
(`Gtz.hasPuncturedStress_of_independentStresses`); one whose stress space is a line
`ℝ ∙ z` has it only at the labels where `z` already vanishes. -/
def HasPuncturedStress (design : WeightedDesign size rank) : Prop :=
  ∀ dead : Fin size, ∃ stress : Fin size → ℝ, stress ≠ 0 ∧ stress dead = 0 ∧
    (∑ c, stress c • atomMatrix (design.atom c)) = 0

/-- **Two independent stresses puncture at every label.**  The stress space is a
subspace; evaluation at one label is one linear functional on it; a space of
dimension at least two meets that functional's kernel nontrivially.  Written
without `finrank`, as the explicit combination that clears the label.

THE CASE SPLIT IS LOAD-BEARING and is the one place an informal account of this
argument goes wrong.  The clearing combination
`second - (second dead / first dead) • first` is undefined when the first stress
ALREADY vanishes at the dead label, and Lean's division convention would silently
evaluate it to `second`, whose value there need not vanish.  The proof therefore
opens on `first dead = 0` and returns `first` itself in that branch. -/
theorem hasPuncturedStress_of_independentStresses {design : WeightedDesign size rank}
    {first second : Fin size → ℝ} (hfirstNonzero : first ≠ 0)
    (hIndependent : ∀ ratio : ℝ, second ≠ ratio • first)
    (hfirstStress : (∑ c, first c • atomMatrix (design.atom c)) = 0)
    (hsecondStress : (∑ c, second c • atomMatrix (design.atom c)) = 0) :
    HasPuncturedStress design := by
  intro dead
  by_cases hvanishes : first dead = 0
  · exact ⟨first, hfirstNonzero, hvanishes, hfirstStress⟩
  · refine ⟨second - (second dead / first dead) • first, ?_, ?_, ?_⟩
    · intro hzero
      refine hIndependent (second dead / first dead) ?_
      have := sub_eq_zero.mp hzero
      exact this
    · show second dead - (second dead / first dead) * first dead = 0
      rw [div_mul_cancel₀ _ hvanishes, sub_self]
    · have hpointwise : ∀ c : Fin size,
          (second - (second dead / first dead) • first) c • atomMatrix (design.atom c)
            = second c • atomMatrix (design.atom c)
              - (second dead / first dead) • (first c • atomMatrix (design.atom c)) := by
        intro c
        show (second c - (second dead / first dead) * first c) • atomMatrix (design.atom c) = _
        rw [sub_smul, smul_smul]
      rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hpointwise c,
        Finset.sum_sub_distrib, ← Finset.smul_sum, hfirstStress, hsecondStress, smul_zero,
        sub_zero]

/-! ## The walk -/

/-- **THE PUNCTURED-STRESS WALK.**  At `size + 1` atoms, granted every cell
strictly below `size` and granted that STRESSED designs at `size` are dominated, a
punctured-stress design is dominated.

The immediate cell `size` itself is NOT assumed -- that is the whole point, and it
is what separates this from `Gtz.exists_dominating_of_stress`, which assumes every
cell strictly below `size + 1` and therefore assumes `size`. -/
theorem exists_dominating_of_puncturedStress (hrankPos : 1 ≤ rank)
    (hsmaller : ∀ smallSize, smallSize < size → GtzWeighted smallSize rank)
    (hstressedTop : ∀ (top : WeightedDesign size rank) (stress : Fin size → ℝ), stress ≠ 0 →
      (∑ c, stress c • atomMatrix (top.atom c)) = 0 →
      ∃ selected : Finset (Fin size), selected.card = rank ∧ Dominates top selected)
    (design : WeightedDesign (size + 1) rank) (hpunctured : HasPuncturedStress design) :
    ∃ selected : Finset (Fin (size + 1)), selected.card = rank ∧ Dominates design selected := by
  classical
  obtain ⟨startStress, hstartNonzero, -, hstartStress⟩ := hpunctured 0
  obtain ⟨scale, hscalePos, hscaleLe, smallSize, hsmallLt, smallDesign, inject, hinject,
    hatoms⟩ := exists_rescaledReducedDesign_of_stress design hrankPos hstartNonzero hstartStress
  have hrescaled : ∀ i, atomMatrix (smallDesign.atom i)
      = scale • atomMatrix (design.atom (inject i)) := by
    intro i
    rw [hatoms i, atomMatrix_smul, Real.sq_sqrt hscalePos.le]
  obtain ⟨smallSelected, hcard, hdominates⟩ :
      ∃ selected : Finset (Fin smallSize), selected.card = rank ∧ Dominates smallDesign selected := by
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hsmallLt) with hstrict | hexact
    · exact hsmaller smallSize hstrict smallDesign
    · subst hexact
      -- exactly one atom died: its label is the single element of the image's complement
      have hcardImage : (Finset.univ.image inject).card = smallSize := by
        rw [Finset.card_image_of_injective _ hinject, Finset.card_univ, Fintype.card_fin]
      have hcardCompl : (Finset.univ.image inject)ᶜ.card = 1 := by
        rw [Finset.card_compl, hcardImage, Fintype.card_fin]
        omega
      obtain ⟨dead, hdead⟩ := Finset.card_eq_one.mp hcardCompl
      obtain ⟨stress, hstressNonzero, hstressDead, hstressParseval⟩ := hpunctured dead
      have hsurvives : ∀ label : Fin (smallSize + 1), label ≠ dead →
          ∃ i, inject i = label := by
        intro label hne
        have hmem : label ∈ Finset.univ.image inject := by
          by_contra hnot
          have hcompl : label ∈ (Finset.univ.image inject)ᶜ := Finset.mem_compl.mpr hnot
          rw [hdead, Finset.mem_singleton] at hcompl
          exact hne hcompl
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
        exact ⟨i, hi⟩
      refine hstressedTop smallDesign (fun i => stress (inject i)) ?_ ?_
      · intro hallzero
        refine hstressNonzero (funext fun label => ?_)
        by_cases hisdead : label = dead
        · rw [hisdead]; exact hstressDead
        · obtain ⟨i, hi⟩ := hsurvives label hisdead
          have hzero : stress (inject i) = 0 := congrFun hallzero i
          rw [← hi]
          exact hzero
      · have hoffdead : (∑ label ∈ Finset.univ.image inject,
            stress label • atomMatrix (design.atom label)) = 0 := by
          have hsplit := Finset.sum_add_sum_compl (Finset.univ.image inject)
            (fun label => stress label • atomMatrix (design.atom label))
          rw [hdead, Finset.sum_singleton, hstressDead, zero_smul, add_zero,
            hstressParseval] at hsplit
          exact hsplit
        calc ∑ i, stress (inject i) • atomMatrix (smallDesign.atom i)
            = scale • ∑ i, stress (inject i) • atomMatrix (design.atom (inject i)) := by
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hrescaled i, smul_comm]
          _ = scale • ∑ label ∈ Finset.univ.image inject,
                stress label • atomMatrix (design.atom label) := by
              rw [Finset.sum_image fun x _ y _ hxy => hinject hxy]
          _ = 0 := by rw [hoffdead, smul_zero]
  refine ⟨smallSelected.image inject, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinject, hcard]
  · show (subsetSum design (smallSelected.image inject) - 1).PosSemidef
    have hsums : subsetSum smallDesign smallSelected
        = scale • subsetSum design (smallSelected.image inject) := by
      rw [subsetSum, subsetSum, Finset.sum_image fun x _ y _ hxy => hinject hxy,
        Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => hrescaled i
    refine posSemidef_sub_one_of_smul_sub_one hscalePos hscaleLe ?_
    rw [← hsums]
    exact hdominates

/-! ## Rank three: the `(7,3)` instantiation and the unique-stress residue -/

/-- **A PUNCTURED-STRESS `(7,3)` DESIGN IS DOMINATED**, with no open hypothesis.
`Gtz.gtzWeighted_of_le_five` supplies every cell below six, and
`Gtz.exists_dominating_sixThree_of_stress` supplies the stressed sixth. -/
theorem exists_dominating_sevenThree_of_puncturedStress (design : WeightedDesign 7 3)
    (hpunctured : HasPuncturedStress design) :
    ∃ selected : Finset (Fin 7), selected.card = 3 ∧ Dominates design selected :=
  exists_dominating_of_puncturedStress (size := 6) (rank := 3) (by norm_num)
    (fun smallSize hlt => gtzWeighted_of_le_five smallSize 3 (by norm_num) (by omega))
    (fun top stress hnonzero hstress => exists_dominating_sixThree_of_stress top hnonzero hstress)
    design hpunctured

/-- **TWO INDEPENDENT STRESSES DOMINATE A `(7,3)` DESIGN.**  This is the campaign's
claim C6, verified: a `(7,3)` design whose stress space has dimension at least two
is dominated UNCONDITIONALLY.

The hypothesis bundle is inhabited -- see
`Gtz.tripleCoincidentDesign_hasPuncturedStress` at the end of this file. -/
theorem exists_dominating_sevenThree_of_independentStresses (design : WeightedDesign 7 3)
    {first second : Fin 7 → ℝ} (hfirstNonzero : first ≠ 0)
    (hIndependent : ∀ ratio : ℝ, second ≠ ratio • first)
    (hfirstStress : (∑ c, first c • atomMatrix (design.atom c)) = 0)
    (hsecondStress : (∑ c, second c • atomMatrix (design.atom c)) = 0) :
    ∃ selected : Finset (Fin 7), selected.card = 3 ∧ Dominates design selected :=
  exists_dominating_sevenThree_of_puncturedStress design
    (hasPuncturedStress_of_independentStresses hfirstNonzero hIndependent hfirstStress
      hsecondStress)

/-- **THE `(7,3)` CELL IS OPEN EXACTLY ON THE UNIQUE-STRESS STRATUM.**

Every `(7,3)` design carries a stress -- six functionals on seven unknowns,
`Gtz.exists_parsevalNullDirection` -- so the stress space is never zero, and by
`Gtz.exists_dominating_sevenThree_of_independentStresses` it is never two
dimensional at a counterexample either.  What is left is a LINE, and this iff says
that stratum carries the whole cell.

With `Gtz.gtzWeighted_six_three_iff_seven_three` and `Gtz.rank_three_iff_six_three`
this places the whole of weighted rank three on designs of seven atoms whose
Veronese images span a hyperplane of `Sym_3(ℝ)` with a one-dimensional relation
space.

READ THE SHRINK HONESTLY: the surviving stratum is GENERIC, not small.  Stress
dimension at least two is a codimension-one condition on the design cone, and a
census of 96000 random `(7,3)` designs found stress dimension exactly one in all
96000 (measured, this campaign).  So the iff discards a measure-zero set.  What
makes it worth stating is WHICH set: every polished `(7,3)` chart minimiser measured
in this campaign has stress dimension two or three -- the minimisers are parallel
splittings, and `stress dimension = 7 - (number of distinct atom directions)` held on
all 150 of them -- so the numerically accessible tie locus lies entirely inside the
region this theorem already dominates, and a `(7,3)` counterexample cannot be sought
by unconstrained descent. -/
theorem gtzWeighted_seven_three_iff_uniqueStress :
    GtzWeighted 7 3 ↔
      ∀ (design : WeightedDesign 7 3) (direction : Fin 7 → ℝ), direction ≠ 0 →
        (∑ c, direction c • atomMatrix (design.atom c)) = 0 →
        (∀ stress : Fin 7 → ℝ, (∑ c, stress c • atomMatrix (design.atom c)) = 0 →
          ∃ ratio : ℝ, stress = ratio • direction) →
        ∃ selected : Finset (Fin 7), selected.card = 3 ∧ Dominates design selected := by
  constructor
  · intro hcell design _ _ _ _
    exact hcell design
  · intro huniqueStratum design
    obtain ⟨direction, hdirectionNonzero, hdirectionStress⟩ :=
      exists_parsevalNullDirection design.atom (by norm_num)
    by_cases hisLine : ∀ stress : Fin 7 → ℝ,
        (∑ c, stress c • atomMatrix (design.atom c)) = 0 → ∃ ratio : ℝ, stress = ratio • direction
    · exact huniqueStratum design direction hdirectionNonzero hdirectionStress hisLine
    · push Not at hisLine
      obtain ⟨second, hsecondStress, hsecondIndependent⟩ := hisLine
      exact exists_dominating_sevenThree_of_independentStresses design hdirectionNonzero
        hsecondIndependent hdirectionStress hsecondStress

/-- The same residue with the whole of rank three attached, through the shipped
collapse `Gtz.rank_three_iff_six_three` and `Gtz.gtzWeighted_six_three_iff_seven_three`. -/
theorem gtzWeightedAll_three_iff_uniqueStress_sevenThree :
    GtzWeightedAll 3 ↔
      ∀ (design : WeightedDesign 7 3) (direction : Fin 7 → ℝ), direction ≠ 0 →
        (∑ c, direction c • atomMatrix (design.atom c)) = 0 →
        (∀ stress : Fin 7 → ℝ, (∑ c, stress c • atomMatrix (design.atom c)) = 0 →
          ∃ ratio : ℝ, stress = ratio • direction) →
        ∃ selected : Finset (Fin 7), selected.card = 3 ∧ Dominates design selected := by
  rw [rank_three_iff_six_three, gtzWeighted_six_three_iff_seven_three,
    gtzWeighted_seven_three_iff_uniqueStress]

/-! ## The production theorem: what a failing top-plus-one cell actually manufactures -/

/-- **A NON-DOMINATED DESIGN AT `size + 1` MANUFACTURES A STRESS-FREE NON-DOMINATED
LANDING AT `size`**, on a uniformly rescaled sub-family of its own atoms.

This is the honest production the `(7,3)` lane was missing, and the missing piece is
ATOM-LEVEL rather than existential.  `Gtz.SevenThreeCrux` is left with no production
theorem, but the reason must be stated exactly: it is the HYPOTHESIS PAIR of the
shipped production `Gtz.nonempty_sevenThreeCrux_of_not_gtzWeighted_seven_three` --
namely `Gtz.GtzWeighted 6 3` together with `¬ Gtz.GtzWeighted 7 3` -- that is
contradictory, by `Gtz.false_of_gtzWeighted_six_three_of_not_gtzWeighted_seven_three`,
so that theorem is vacuously true and produces nothing.  It is NOT known, and would
be equivalent to the conjecture, that the field bundle of `Gtz.SevenThreeCrux` is
itself contradictory: the kernel derives `IsEmpty Gtz.SevenThreeCrux` only
conditionally, through `Gtz.isEmpty_sevenThreeCrux_of_isEmpty_sixThreeCrux`.

What a `(7,3)` failure DOES inhabit is this: a landing one size down that is
simultaneously

* stress-free (else `hstressedTop` dominates it and the pullback contradicts),
* non-dominated (else the pullback contradicts directly),
* carried by `size` of the original `size + 1` atoms, scaled by one common
  `Real.sqrt scale ≤ 1`.

Stress-freeness and non-domination are exactly two of the eight
`Gtz.SixThreeCrux` fields, so at rank three this lands a counterexample squarely in
the `(6,3)` crux shape, on named atoms of the original design. -/
theorem exists_stressFree_undominated_landing_of_not_dominated (hrankPos : 1 ≤ rank)
    (hsmaller : ∀ smallSize, smallSize < size → GtzWeighted smallSize rank)
    (hstressedTop : ∀ (top : WeightedDesign size rank) (stress : Fin size → ℝ), stress ≠ 0 →
      (∑ c, stress c • atomMatrix (top.atom c)) = 0 →
      ∃ selected : Finset (Fin size), selected.card = rank ∧ Dominates top selected)
    (design : WeightedDesign (size + 1) rank)
    {startStress : Fin (size + 1) → ℝ} (hstartNonzero : startStress ≠ 0)
    (hstartStress : (∑ c, startStress c • atomMatrix (design.atom c)) = 0)
    (hundominated : ∀ selected : Finset (Fin (size + 1)), selected.card = rank →
      ¬ Dominates design selected) :
    ∃ scale : ℝ, 0 < scale ∧ scale ≤ 1 ∧
      ∃ landing : WeightedDesign size rank, ∃ inject : Fin size → Fin (size + 1),
        Function.Injective inject ∧
        (∀ i, landing.atom i = Real.sqrt scale • design.atom (inject i)) ∧
        (∀ stress : Fin size → ℝ,
          (∑ c, stress c • atomMatrix (landing.atom c)) = 0 → stress = 0) ∧
        (∀ selected : Finset (Fin size), selected.card = rank → ¬ Dominates landing selected) := by
  classical
  obtain ⟨scale, hscalePos, hscaleLe, smallSize, hsmallLt, landing, inject, hinject, hatoms⟩ :=
    exists_rescaledReducedDesign_of_stress design hrankPos hstartNonzero hstartStress
  have hrescaled : ∀ i, atomMatrix (landing.atom i)
      = scale • atomMatrix (design.atom (inject i)) := by
    intro i
    rw [hatoms i, atomMatrix_smul, Real.sq_sqrt hscalePos.le]
  -- the pullback, isolated once and used three times
  have hpull : ∀ selected : Finset (Fin smallSize), selected.card = rank →
      Dominates landing selected → False := by
    intro selected hcard hdominates
    refine hundominated (selected.image inject) ?_ ?_
    · rw [Finset.card_image_of_injective _ hinject, hcard]
    · show (subsetSum design (selected.image inject) - 1).PosSemidef
      have hsums : subsetSum landing selected
          = scale • subsetSum design (selected.image inject) := by
        rw [subsetSum, subsetSum, Finset.sum_image fun x _ y _ hxy => hinject hxy,
          Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => hrescaled i
      refine posSemidef_sub_one_of_smul_sub_one hscalePos hscaleLe ?_
      rw [← hsums]
      exact hdominates
  -- the landing cannot be strictly below `size`: every such cell is a theorem
  have hexact : smallSize = size := by
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hsmallLt) with hstrict | hexact
    · obtain ⟨selected, hcard, hdominates⟩ := hsmaller smallSize hstrict landing
      exact absurd (hpull selected hcard hdominates) not_false
    · exact hexact
  subst hexact
  refine ⟨scale, hscalePos, hscaleLe, landing, inject, hinject, hatoms, ?_, ?_⟩
  · intro stress hstress
    by_contra hnonzero
    obtain ⟨selected, hcard, hdominates⟩ := hstressedTop landing stress hnonzero hstress
    exact hpull selected hcard hdominates
  · intro selected hcard hdominates
    exact hpull selected hcard hdominates

/-- **THE `(7,3)` PRODUCTION.**  A `(7,3)` counterexample manufactures a stress-free
non-dominated `(6,3)` design carried by six of its own seven atoms.

Contrast the shipped `Gtz.nonempty_sixThreeCrux_of_not_gtzWeighted_seven_three`,
which is hypothesis-free and correct but routes through the abstract collapse and
therefore names no atoms at all. -/
theorem exists_stressFree_undominated_sixThree_of_not_dominated_sevenThree
    (design : WeightedDesign 7 3)
    (hundominated : ∀ selected : Finset (Fin 7), selected.card = 3 →
      ¬ Dominates design selected) :
    ∃ scale : ℝ, 0 < scale ∧ scale ≤ 1 ∧
      ∃ landing : WeightedDesign 6 3, ∃ inject : Fin 6 → Fin 7, Function.Injective inject ∧
        (∀ i, landing.atom i = Real.sqrt scale • design.atom (inject i)) ∧
        (∀ stress : Fin 6 → ℝ,
          (∑ c, stress c • atomMatrix (landing.atom c)) = 0 → stress = 0) ∧
        (∀ selected : Finset (Fin 6), selected.card = 3 → ¬ Dominates landing selected) := by
  obtain ⟨startStress, hstartNonzero, hstartStress⟩ :=
    exists_parsevalNullDirection design.atom (by norm_num)
  exact exists_stressFree_undominated_landing_of_not_dominated (size := 6) (rank := 3)
    (by norm_num)
    (fun smallSize hlt => gtzWeighted_of_le_five smallSize 3 (by norm_num) (by omega))
    (fun top stress hnonzero hstress => exists_dominating_sixThree_of_stress top hnonzero hstress)
    design hstartNonzero hstartStress hundominated

/-! ## The mass-free walk, with the puncture exposed -/

/-- **THE MASS-FREE WALK.**  A stress whose coordinate sum vanishes walks the design
onto a strictly smaller ATOM SUBFAMILY OF ITSELF -- no rescaling, because the mass
law `mass = 1 - walkLength * ∑ stress` collapses to `mass = 1`.  The killed label is
returned, and the stress is strictly POSITIVE there.

Contrast `Gtz.exists_rescaledReducedDesign_of_stress`, which returns
`Real.sqrt scale • design.atom (inject i)` for an existentially quantified
`scale ∈ (0, 1]`, and returns no information at all about which label died. -/
theorem exists_puncturedLanding_of_massFreeStress (design : WeightedDesign size rank)
    {stress : Fin size → ℝ} (hnonzero : stress ≠ 0)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0)
    (hsumZero : (∑ c, stress c) = 0) :
    ∃ dead : Fin size, 0 < stress dead ∧
      ∃ smallSize : ℕ, smallSize < size ∧ ∃ landing : WeightedDesign smallSize rank,
        ∃ inject : Fin smallSize → Fin size, Function.Injective inject ∧
          (∀ i, landing.atom i = design.atom (inject i)) ∧ (∀ i, inject i ≠ dead) := by
  classical
  obtain ⟨raiseLabel, hraiseLabel⟩ := exists_pos_of_sum_nonneg hnonzero (le_of_eq hsumZero.symm)
  set raisers : Finset (Fin size) := Finset.univ.filter (fun c => 0 < stress c) with hraisers
  have hraisersNonempty : raisers.Nonempty :=
    ⟨raiseLabel, Finset.mem_filter.mpr ⟨Finset.mem_univ raiseLabel, hraiseLabel⟩⟩
  obtain ⟨dead, hdeadMem, hdeadMin⟩ :=
    Finset.exists_min_image raisers (fun c => design.weight c / stress c) hraisersNonempty
  have hstressDead : 0 < stress dead := (Finset.mem_filter.mp hdeadMem).2
  set walkLength : ℝ := design.weight dead / stress dead with hwalkLength
  set walked : Fin size → ℝ := fun c => design.weight c - walkLength * stress c with hwalked
  have hwalkedNonneg : ∀ c, 0 ≤ walked c := by
    intro c
    rcases le_or_gt (stress c) 0 with hnonpos | hpos
    · have hweight := design.weight_pos c
      have hlen : 0 < walkLength := div_pos (design.weight_pos dead) hstressDead
      simp only [hwalked]
      nlinarith
    · have hmem : c ∈ raisers := Finset.mem_filter.mpr ⟨Finset.mem_univ c, hpos⟩
      have hbound := (le_div_iff₀ hpos).mp (hdeadMin c hmem)
      simp only [hwalked]
      linarith
  have hwalkedDead : walked dead = 0 := by
    simp only [hwalked, hwalkLength]
    rw [div_mul_cancel₀ _ (ne_of_gt hstressDead), sub_self]
  have hwalkedParseval : ∑ c, walked c • atomMatrix (design.atom c) = 1 := by
    simp only [hwalked, sub_smul, mul_smul]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hstress, smul_zero, sub_zero,
      design.isParseval]
  -- THE MASS IS EXACTLY ONE: this is the whole content of the hypothesis
  have hwalkedMass : ∑ c, walked c = 1 := by
    simp only [hwalked]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumZero, mul_zero, sub_zero,
      design.weight_sum_one]
  set support : Finset (Fin size) := Finset.univ.filter (fun c => 0 < walked c) with hsupport
  have hdeadOutside : dead ∉ support := by simp [hsupport, hwalkedDead]
  have hsizePos : 0 < size := Fin.pos dead
  have hsupportLt : support.card < size := by
    have hsubset : support ⊆ Finset.univ.erase dead := fun c hc =>
      Finset.mem_erase.mpr ⟨fun heq => hdeadOutside (heq ▸ hc), Finset.mem_univ c⟩
    calc support.card ≤ (Finset.univ.erase dead).card := Finset.card_le_card hsubset
      _ < size := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ dead), Finset.card_univ,
            Fintype.card_fin]
          omega
  have houtside : ∀ c ∈ Finset.univ, c ∉ support → walked c = 0 := by
    intro c _ hc
    have hnotPos : ¬ 0 < walked c := fun hpos =>
      hc (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hpos⟩)
    exact le_antisymm (not_lt.mp hnotPos) (hwalkedNonneg c)
  have hsupportSum : ∑ c ∈ support, walked c = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ support) houtside]
    exact hwalkedMass
  have hsupportParseval : ∑ c ∈ support, walked c • atomMatrix (design.atom c) = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ support)
      (fun c hcu hcs => by rw [houtside c hcu hcs, zero_smul])]
    exact hwalkedParseval
  refine ⟨dead, hstressDead, support.card, hsupportLt,
    { atom := fun i => design.atom (support.orderIsoOfFin rfl i).val
      weight := fun i => walked (support.orderIsoOfFin rfl i).val
      weight_pos := fun i => (Finset.mem_filter.mp (support.orderIsoOfFin rfl i).2).2
      weight_sum_one := ?_
      isParseval := ?_ },
    fun i => (support.orderIsoOfFin rfl i).val,
    fun a b hab => (support.orderIsoOfFin rfl).toEquiv.injective (Subtype.val_injective hab),
    fun i => rfl,
    fun i hEq => hdeadOutside (hEq ▸ (support.orderIsoOfFin rfl i).2)⟩
  · rw [sum_orderIsoOfFin support rfl walked, hsupportSum]
  · rw [sum_orderIsoOfFin support rfl (fun c => walked c • atomMatrix (design.atom c))]
    exact hsupportParseval

/-- **THE DOUBLE LANDING, in general.**  A mass-free stress is walkable in BOTH
directions, and the two runs kill different labels: the `+` run kills a label where
the stress is strictly positive, the `-` run one where it is strictly negative. -/
theorem exists_twoPuncturedLandings_of_massFreeStress (design : WeightedDesign size rank)
    {stress : Fin size → ℝ} (hnonzero : stress ≠ 0)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0)
    (hsumZero : (∑ c, stress c) = 0) :
    ∃ deadPlus deadMinus : Fin size, deadPlus ≠ deadMinus ∧
      (∃ plusSize : ℕ, plusSize < size ∧ ∃ plusLanding : WeightedDesign plusSize rank,
        ∃ injectPlus : Fin plusSize → Fin size, Function.Injective injectPlus ∧
          (∀ i, plusLanding.atom i = design.atom (injectPlus i)) ∧
          (∀ i, injectPlus i ≠ deadPlus)) ∧
      (∃ minusSize : ℕ, minusSize < size ∧ ∃ minusLanding : WeightedDesign minusSize rank,
        ∃ injectMinus : Fin minusSize → Fin size, Function.Injective injectMinus ∧
          (∀ i, minusLanding.atom i = design.atom (injectMinus i)) ∧
          (∀ i, injectMinus i ≠ deadMinus)) := by
  have hnegStress : (∑ c, (-stress) c • atomMatrix (design.atom c)) = 0 := by
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hstress, neg_zero]
  have hnegSum : (∑ c, (-stress) c) = 0 := by
    simp only [Pi.neg_apply, Finset.sum_neg_distrib, hsumZero, neg_zero]
  obtain ⟨deadPlus, hplusPos, hplusData⟩ :=
    exists_puncturedLanding_of_massFreeStress design hnonzero hstress hsumZero
  obtain ⟨deadMinus, hminusPos, hminusData⟩ :=
    exists_puncturedLanding_of_massFreeStress design (neg_ne_zero.mpr hnonzero) hnegStress hnegSum
  have hminusNeg : stress deadMinus < 0 := by
    have : 0 < -stress deadMinus := hminusPos
    linarith
  exact ⟨deadPlus, deadMinus, fun heq => absurd (heq ▸ hplusPos) (not_lt.mpr hminusNeg.le),
    hplusData, hminusData⟩

/-! ## What an undominated design one above the top manufactures -/

/-- **A SCALE-ONE LANDING OF AN UNDOMINATED DESIGN IS A STRESS-FREE UNDOMINATED
DESIGN ONE SIZE DOWN.**  Stated at general `(size + 1, rank)`.  Everything strictly
below `size` is closed by `hsmaller`, so the landing has exactly `size` atoms; a
stress on it is closed by `hstressedTop`, so it is stress-free; and both pull back
verbatim, because the landing's atoms are literally the survivors -- no
`Real.sqrt scale` anywhere -- and `Gtz.subsetSum` is weight-free. -/
theorem exists_topLanding_of_undominated
    (hsmaller : ∀ smallSize, smallSize < size → GtzWeighted smallSize rank)
    (hstressedTop : ∀ (top : WeightedDesign size rank) (stress : Fin size → ℝ), stress ≠ 0 →
      (∑ c, stress c • atomMatrix (top.atom c)) = 0 →
      ∃ selected : Finset (Fin size), selected.card = rank ∧ Dominates top selected)
    (design : WeightedDesign (size + 1) rank)
    (hundominated : ∀ selected : Finset (Fin (size + 1)), selected.card = rank →
      ¬ Dominates design selected)
    {smallSize : ℕ} (hlt : smallSize < size + 1) (landing : WeightedDesign smallSize rank)
    {inject : Fin smallSize → Fin (size + 1)} (hinject : Function.Injective inject)
    (hatoms : ∀ i, landing.atom i = design.atom (inject i)) {dead : Fin (size + 1)}
    (hdead : ∀ i, inject i ≠ dead) :
    ∃ top : WeightedDesign size rank, ∃ injectTop : Fin size → Fin (size + 1),
      Function.Injective injectTop ∧
      (∀ i, top.atom i = design.atom (injectTop i)) ∧ (∀ i, injectTop i ≠ dead) ∧
      (∀ direction : Fin size → ℝ,
        (∑ c, direction c • atomMatrix (top.atom c)) = 0 → direction = 0) ∧
      (∀ selected : Finset (Fin size), selected.card = rank → ¬ Dominates top selected) := by
  classical
  have hpull : ∀ selected : Finset (Fin smallSize), selected.card = rank →
      Dominates landing selected → False := by
    intro selected hcard hdominates
    refine hundominated (selected.image inject) ?_ ?_
    · rw [Finset.card_image_of_injective _ hinject, hcard]
    · show (subsetSum design (selected.image inject) - 1).PosSemidef
      have hsums : subsetSum landing selected = subsetSum design (selected.image inject) := by
        rw [subsetSum, subsetSum, Finset.sum_image fun x _ y _ hxy => hinject hxy]
        exact Finset.sum_congr rfl fun i _ => by rw [hatoms i]
      rw [← hsums]
      exact hdominates
  have hexact : smallSize = size := by
    by_contra hne
    have hstrict : smallSize < size := by omega
    obtain ⟨selected, hcard, hdominates⟩ := hsmaller smallSize hstrict landing
    exact hpull selected hcard hdominates
  subst hexact
  refine ⟨landing, inject, hinject, hatoms, hdead, ?_, ?_⟩
  · intro direction hdirection
    by_contra hnonzero
    obtain ⟨selected, hcard, hdominates⟩ := hstressedTop landing direction hnonzero hdirection
    exact hpull selected hcard hdominates
  · intro selected hcard hdominates
    exact hpull selected hcard hdominates

/-- **THE DOUBLE LANDING, general form.**  An undominated design at `size + 1`
carrying a MASS-FREE stress manufactures TWO stress-free undominated designs at
`size`, on two DIFFERENT punctures of its own atom family, with no rescaling -- so
they share `size - 1` atoms exactly. -/
theorem exists_twoTopLandings_of_massFreeStress
    (hsmaller : ∀ smallSize, smallSize < size → GtzWeighted smallSize rank)
    (hstressedTop : ∀ (top : WeightedDesign size rank) (stress : Fin size → ℝ), stress ≠ 0 →
      (∑ c, stress c • atomMatrix (top.atom c)) = 0 →
      ∃ selected : Finset (Fin size), selected.card = rank ∧ Dominates top selected)
    (design : WeightedDesign (size + 1) rank)
    {stress : Fin (size + 1) → ℝ} (hnonzero : stress ≠ 0)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0)
    (hsumZero : (∑ c, stress c) = 0)
    (hundominated : ∀ selected : Finset (Fin (size + 1)), selected.card = rank →
      ¬ Dominates design selected) :
    ∃ deadPlus deadMinus : Fin (size + 1), deadPlus ≠ deadMinus ∧
      ∃ plusLanding minusLanding : WeightedDesign size rank,
        ∃ injectPlus injectMinus : Fin size → Fin (size + 1),
          Function.Injective injectPlus ∧ Function.Injective injectMinus ∧
          (∀ i, plusLanding.atom i = design.atom (injectPlus i)) ∧
          (∀ i, minusLanding.atom i = design.atom (injectMinus i)) ∧
          (∀ i, injectPlus i ≠ deadPlus) ∧ (∀ i, injectMinus i ≠ deadMinus) ∧
          (∀ direction : Fin size → ℝ,
            (∑ c, direction c • atomMatrix (plusLanding.atom c)) = 0 → direction = 0) ∧
          (∀ direction : Fin size → ℝ,
            (∑ c, direction c • atomMatrix (minusLanding.atom c)) = 0 → direction = 0) ∧
          (∀ selected : Finset (Fin size), selected.card = rank →
            ¬ Dominates plusLanding selected) ∧
          (∀ selected : Finset (Fin size), selected.card = rank →
            ¬ Dominates minusLanding selected) := by
  obtain ⟨deadPlus, deadMinus, hdistinct,
    ⟨plusSize, hplusLt, plusRaw, injectPlusRaw, hplusInject, hplusAtoms, hplusDead⟩,
    ⟨minusSize, hminusLt, minusRaw, injectMinusRaw, hminusInject, hminusAtoms, hminusDead⟩⟩ :=
    exists_twoPuncturedLandings_of_massFreeStress design hnonzero hstress hsumZero
  obtain ⟨plusLanding, injectPlus, hplusInj, hplusEq, hplusOff, hplusFree, hplusFail⟩ :=
    exists_topLanding_of_undominated hsmaller hstressedTop design hundominated hplusLt plusRaw
      hplusInject hplusAtoms hplusDead
  obtain ⟨minusLanding, injectMinus, hminusInj, hminusEq, hminusOff, hminusFree, hminusFail⟩ :=
    exists_topLanding_of_undominated hsmaller hstressedTop design hundominated hminusLt minusRaw
      hminusInject hminusAtoms hminusDead
  exact ⟨deadPlus, deadMinus, hdistinct, plusLanding, minusLanding, injectPlus, injectMinus,
    hplusInj, hminusInj, hplusEq, hminusEq, hplusOff, hminusOff, hplusFree, hminusFree,
    hplusFail, hminusFail⟩

/-- **THE DOUBLE LANDING AT `(7,3)`.**  An undominated `(7,3)` design carrying a
MASS-FREE stress manufactures TWO stress-free undominated `(6,3)` designs, carried by
two DIFFERENT six-element subsets of its own seven atoms, with no rescaling
whatsoever -- so the two share five atoms exactly.

Both landings are stress-free and undominated, which are two of the eight
`Gtz.SixThreeCrux` fields; the shipped hypothesis-free `(7,3)` production
`Gtz.nonempty_sixThreeCrux_of_not_gtzWeighted_seven_three` routes through the
abstract collapse and therefore names no atoms at all.

The mass-free hypothesis is not removable -- see the header.  Nor is the bundle
witnessable in the kernel: it contains `hundominated`, and an undominated `(7,3)`
design existing is exactly the failure of the conjecture.  The stress half of the
bundle IS inhabited, by `Gtz.tripleCoincidentDesign_massFreeStress`. -/
theorem exists_twoSixThreeLandings_of_massFreeStress_sevenThree (design : WeightedDesign 7 3)
    {stress : Fin 7 → ℝ} (hnonzero : stress ≠ 0)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0)
    (hsumZero : (∑ c, stress c) = 0)
    (hundominated : ∀ selected : Finset (Fin 7), selected.card = 3 →
      ¬ Dominates design selected) :
    ∃ deadPlus deadMinus : Fin 7, deadPlus ≠ deadMinus ∧
      ∃ plusLanding minusLanding : WeightedDesign 6 3,
        ∃ injectPlus injectMinus : Fin 6 → Fin 7,
          Function.Injective injectPlus ∧ Function.Injective injectMinus ∧
          (∀ i, plusLanding.atom i = design.atom (injectPlus i)) ∧
          (∀ i, minusLanding.atom i = design.atom (injectMinus i)) ∧
          (∀ i, injectPlus i ≠ deadPlus) ∧ (∀ i, injectMinus i ≠ deadMinus) ∧
          (∀ direction : Fin 6 → ℝ,
            (∑ c, direction c • atomMatrix (plusLanding.atom c)) = 0 → direction = 0) ∧
          (∀ direction : Fin 6 → ℝ,
            (∑ c, direction c • atomMatrix (minusLanding.atom c)) = 0 → direction = 0) ∧
          (∀ selected : Finset (Fin 6), selected.card = 3 → ¬ Dominates plusLanding selected) ∧
          (∀ selected : Finset (Fin 6), selected.card = 3 →
            ¬ Dominates minusLanding selected) :=
  exists_twoTopLandings_of_massFreeStress (size := 6) (rank := 3)
    (fun smallSize hlt => gtzWeighted_of_le_five smallSize 3 (by norm_num) (by omega))
    (fun top direction hnonzeroDirection hdirection =>
      exists_dominating_sixThree_of_stress top hnonzeroDirection hdirection)
    design hnonzero hstress hsumZero hundominated

/-! ## Non-vacuity: a rational all-heavy `(7,3)` design with three coincident atoms

A hypothesis bundle that compiles is not thereby inhabited, and the whole point of
`Gtz.HasPuncturedStress` is that it is strictly stronger than carrying a stress.
This section discharges the question with an explicit witness.

The construction is a three-axis frame with multiplicities `(3, 2, 2)`.  Rational
atom lengths are available because three rational squares sum to one:
`(3/7)² + (6/7)² + (2/7)² = 1`, so the axis lengths `7/3`, `7/6`, `7/2` reciprocate
to group weights `9/49`, `36/49`, `4/49`, which sum to one exactly.  Every leverage
is above one, so the design is all-heavy and lives inside the sharpened frontier
`Gtz.GtzWeightedHeavy`.

Two atoms of the FIRST group being literally equal, the differences
`(1,-1,0,0,0,0,0)` and `(0,1,-1,0,0,0,0)` are independent stresses; both have
coordinate sum zero, so the same design also witnesses the mass-free hypothesis. -/

/-- The atom table of `Gtz.tripleCoincidentDesign`: three copies of the first axis
at length `7/3`, two of the second at `7/6`, two of the third at `7/2`. -/
noncomputable def tripleCoincidentAtom : Fin 7 → (Fin 3 → ℝ) :=
  ![![7/3, 0, 0], ![7/3, 0, 0], ![7/3, 0, 0],
    ![0, 7/6, 0], ![0, 7/6, 0],
    ![0, 0, 7/2], ![0, 0, 7/2]]

/-- The weight table of `Gtz.tripleCoincidentDesign`.  The three groups carry
`9/49`, `36/49` and `4/49`, split evenly inside each group. -/
noncomputable def tripleCoincidentWeight : Fin 7 → ℝ :=
  ![3/49, 3/49, 3/49, 18/49, 18/49, 2/49, 2/49]

/-- **The witness design.**  Every entry is rational and Parseval holds on the nose:
each axis contributes `(group weight) * (length)² = 1` to its own diagonal slot. -/
noncomputable def tripleCoincidentDesign : WeightedDesign 7 3 where
  atom := tripleCoincidentAtom
  weight := tripleCoincidentWeight
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex <;> simp [tripleCoincidentWeight]
  weight_sum_one := by
    simp [Fin.sum_univ_seven, tripleCoincidentWeight]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply, Fin.sum_univ_seven,
        tripleCoincidentAtom, tripleCoincidentWeight] <;> norm_num

@[simp] theorem tripleCoincidentDesign_atom :
    tripleCoincidentDesign.atom = tripleCoincidentAtom := rfl

@[simp] theorem tripleCoincidentDesign_weight :
    tripleCoincidentDesign.weight = tripleCoincidentWeight := rfl

/-- The witness is ALL-HEAVY: the three groups have leverage `49/9`, `49/36` and
`49/4`, every one above one.  So the non-vacuity survives restriction to
`Gtz.GtzWeightedHeavy`, the campaign's sharpened frontier. -/
theorem tripleCoincidentDesign_allHeavy : AllHeavy tripleCoincidentDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    simp [leverageOf, Fin.sum_univ_three, tripleCoincidentDesign_atom,
      tripleCoincidentAtom] <;> norm_num

/-- The first exhibited stress: the difference of the first two coincident atoms. -/
noncomputable def tripleCoincidentFirstStress : Fin 7 → ℝ :=
  ![1, -1, 0, 0, 0, 0, 0]

/-- The second exhibited stress: the difference of the last two coincident atoms. -/
noncomputable def tripleCoincidentSecondStress : Fin 7 → ℝ :=
  ![0, 1, -1, 0, 0, 0, 0]

theorem tripleCoincidentFirstStress_ne_zero : tripleCoincidentFirstStress ≠ 0 := by
  intro hzero
  have hentry : tripleCoincidentFirstStress 0 = 0 := by rw [hzero]; rfl
  simp [tripleCoincidentFirstStress] at hentry

/-- The two stresses are independent: no multiple of the first is nonzero at label
`2`, where the second is `-1`. -/
theorem tripleCoincidentStresses_independent :
    ∀ ratio : ℝ, tripleCoincidentSecondStress ≠ ratio • tripleCoincidentFirstStress := by
  intro ratio hEq
  have hentry : tripleCoincidentSecondStress 2 = (ratio • tripleCoincidentFirstStress) 2 := by
    rw [hEq]
  simp [tripleCoincidentSecondStress, tripleCoincidentFirstStress] at hentry

theorem tripleCoincidentFirstStress_parseval :
    (∑ c, tripleCoincidentFirstStress c • atomMatrix (tripleCoincidentDesign.atom c)) = 0 := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply, Fin.sum_univ_seven,
      tripleCoincidentAtom, tripleCoincidentFirstStress]

theorem tripleCoincidentSecondStress_parseval :
    (∑ c, tripleCoincidentSecondStress c • atomMatrix (tripleCoincidentDesign.atom c)) = 0 := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply, Fin.sum_univ_seven,
      tripleCoincidentAtom, tripleCoincidentSecondStress]

/-- **THE HYPOTHESIS OF C6 IS INHABITED.**  `Gtz.tripleCoincidentDesign` carries two
independent stresses, hence a stress vanishing at every prescribed label.  So
`Gtz.exists_dominating_sevenThree_of_independentStresses` and
`Gtz.exists_dominating_sevenThree_of_puncturedStress` are not vacuously true. -/
theorem tripleCoincidentDesign_hasPuncturedStress :
    HasPuncturedStress tripleCoincidentDesign :=
  hasPuncturedStress_of_independentStresses tripleCoincidentFirstStress_ne_zero
    tripleCoincidentStresses_independent tripleCoincidentFirstStress_parseval
    tripleCoincidentSecondStress_parseval

/-- **THE MASS-FREE HYPOTHESIS IS INHABITED TOO**, at the same design and the same
stress: the difference of two coincident atoms has coordinate sum zero.  This is the
stress half of the double landing's bundle; the undominated half is the conjecture. -/
theorem tripleCoincidentDesign_massFreeStress :
    tripleCoincidentFirstStress ≠ 0 ∧
      (∑ c, tripleCoincidentFirstStress c • atomMatrix (tripleCoincidentDesign.atom c)) = 0 ∧
      (∑ c, tripleCoincidentFirstStress c) = 0 := by
  refine ⟨tripleCoincidentFirstStress_ne_zero, tripleCoincidentFirstStress_parseval, ?_⟩
  simp [Fin.sum_univ_seven, tripleCoincidentFirstStress]

/-- **C6 FIRES ON THE WITNESS.**  A closing sanity check that the punctured-stress
walk actually runs at `(7,3)`: the witness is dominated, and the proof goes through
`Gtz.exists_dominating_sevenThree_of_puncturedStress` rather than by exhibiting a
triple by hand. -/
theorem exists_dominating_tripleCoincidentDesign :
    ∃ selected : Finset (Fin 7), selected.card = 3 ∧
      Dominates tripleCoincidentDesign selected :=
  exists_dominating_sevenThree_of_puncturedStress tripleCoincidentDesign
    tripleCoincidentDesign_hasPuncturedStress

end Gtz
