/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.PolarPairSpread

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The witnessed Schur kill and the bracket sign platform

The survivor Schur kill of `Gtz.Reduction.PolarPairSpread` prices the coupling
vector by one Cauchy-Schwarz step against the probe.  That step is the whole
loss of the kill: a probe of the measured near-tie designs shows the priced
margin misses by five parts in a thousand while the exact Schur complement
passes with room.  This file removes the loss.

## 1. The witnessed Schur engine

`Gtz.posDef_of_polarWitnessSchur` replaces the coupling budget by a WITNESS
vector `u` in the pole's plane that solves the survivor plane equation.  The
Cauchy-Schwarz step then runs in the metric of the survivor plane form, and it
is EXACT: the caller pays only the scalar test `V ⬝ᵥ u < pairMass - leverage`.
The test is equivalent to the strict domination of the survivor set, thus the
kill has no residual loss at all.

## 2. The kill and the sharp tie law

`Gtz.not_isTie_of_witnessSchur` fires at the complement of a pole and a pair
in every cell with `rank + 3 = size`.  Its contrapositive
`Gtz.tie_witnessSchur_six_three` is the sharp law of every tie of the deciding
cell: for every witness of the survivor plane equation, the pole mass stays at
or below the leverage, or the witness reading spends the whole gap.

## 3. The residual, narrowed a fifth time

The sharp law is free at every tie (`Gtz.polarWitnessSchurBound_of_isTie`),
thus `Gtz.PolarTiltSelectionWitness` hands it to the prover as a fifth bundle.
Every consumer of the shipped residual runs on the five-bundle one, the
`(5,3)` instance stays FALSE, and the diamond guardrail stays checked.

The realness audit fixes what the fifth bundle can and cannot do.  The complex
two-trine witness deforms to complex ties of the deciding cell with balanced
weights and no parallel pair, and at every such tie the witness reading
saturates the gap exactly.  Thus no field-agnostic argument closes the
residual: the closing step must consume a real-only ingredient.

## 4. The bracket sign platform

The real-only ingredient of the polar lane is the SIGN of the scalar triple
product of the pole with two plane shadows.  `Gtz.tripleBracket_sq_eq_gramDet`
recovers the square of the bracket from the Gram data,
`Gtz.tripleBracket_sq_eq_planeShadow` reads that square in the shadow
calculus, and `Gtz.tripleBracket_mul_eq_planeShadow` pins the product of two
brackets with a shared slot to the pairings alone.  Over the reals the bracket
is a signed number that these laws determine up to a finite sign choice; over
the complex field the analogous quantity carries a free phase.  A sign
enumeration on this platform is the approved real-only exit.
-/

namespace Gtz

open Matrix Finset

/-! ## Part 1: the witnessed Schur engine

The coupling vector of the survivors is priced against a witness of the
survivor plane equation.  The Cauchy-Schwarz step runs in the metric of the
survivor plane form and is exact. -/

section WitnessEngine

variable {size rank : ℕ}

/-- **THE WITNESSED SCHUR DOMINATION.**  A set that covers the pole's plane
with a positive excess and carries pole mass above the leverage dominates
strictly as soon as ONE plane vector `u` solves the survivor plane equation
and reads the coupling below the gap.  The Cauchy-Schwarz of the banked
survivor Schur kill is replaced by the exact metric step, thus the scalar test
`V ⬝ᵥ u < pairMass - leverage` has no loss. -/
theorem posDef_of_polarWitnessSchur (design : WeightedDesign size rank)
    {pole : Fin size} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {selected : Finset (Fin size)} {excess : ℝ} (hexcessPos : 0 < excess)
    (hcover : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + excess) * (probe ⬝ᵥ probe)
        ≤ ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2)
    (hz : design.atom pole ⬝ᵥ design.atom pole
        < ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
    {u : Fin rank → ℝ} (hupole : u ⬝ᵥ design.atom pole = 0)
    (hwitness : (∑ c ∈ selected, (design.atom c ⬝ᵥ u) • planeShadowVec design pole c) - u
        = polarCouplingVec design pole selected)
    (hVu : polarCouplingVec design pole selected ⬝ᵥ u
        < (∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
          - design.atom pole ⬝ᵥ design.atom pole) :
    (subsetSum design selected - 1).PosDef := by
  classical
  have hpoleNe : design.atom pole ≠ 0 := by
    intro hzero
    rw [hzero, zero_dotProduct] at hpole
    exact lt_irrefl 0 hpole
  set leverage : ℝ := design.atom pole ⬝ᵥ design.atom pole with hleverage
  set root : ℝ := Real.sqrt leverage with hroot
  have hrootPos : 0 < root := Real.sqrt_pos.mpr hpole
  have hrootSq : root ^ 2 = leverage := Real.sq_sqrt hpole.le
  set unitNormal : Fin rank → ℝ := root⁻¹ • design.atom pole with hunitNormal
  have hunit : unitNormal ⬝ᵥ unitNormal = 1 := unit_of_ne_zero (design.atom pole) hpoleNe
  have hreadNormal : ∀ c : Fin size, design.atom c ⬝ᵥ unitNormal
      = root⁻¹ * (design.atom c ⬝ᵥ design.atom pole) := by
    intro c
    rw [hunitNormal, dotProduct_smul, smul_eq_mul]
  have hLne : leverage ≠ 0 := ne_of_gt hpole
  have hsumShape : ∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2
      = (∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2) / leverage := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hreadNormal c, mul_pow, inv_pow, hrootSq, ← div_eq_inv_mul]
  have hsurplus : 1 < ∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2 := by
    rw [hsumShape, lt_div_iff₀ hpole, one_mul]
    exact hz
  refine posDef_of_normalSurplus_hyperplaneCover design selected unitNormal hunit hsurplus ?_
  intro probe hprobeNormal hprobeNe
  have hprobePole : probe ⬝ᵥ design.atom pole = 0 := by
    rw [hunitNormal, dotProduct_smul, smul_eq_mul] at hprobeNormal
    rcases mul_eq_zero.mp hprobeNormal with hbad | hgood
    · exact absurd hbad (inv_ne_zero (ne_of_gt hrootPos))
    · exact hgood
  have hprobePos : 0 < probe ⬝ᵥ probe := selfDotProduct_pos hprobeNe
  have hcoupleRead : ∑ c ∈ selected,
      (design.atom c ⬝ᵥ probe) * (design.atom c ⬝ᵥ unitNormal)
      = root⁻¹ * (polarCouplingVec design pole selected ⬝ᵥ probe) := by
    rw [polarCouplingVec_dotProduct design pole selected hprobePole, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hreadNormal c]
    ring
  set pairMass : ℝ := ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2 with hpairMass
  have hgapPos : 0 < pairMass - leverage := by rw [hpairMass, hleverage]; linarith
  have hplaneForm : ∀ w : Fin rank → ℝ, w ⬝ᵥ design.atom pole = 0 →
      0 ≤ (∑ c ∈ selected, (design.atom c ⬝ᵥ w) ^ 2) - w ⬝ᵥ w := by
    intro w hw
    have hc := hcover w hw
    have hnn : 0 ≤ excess * (w ⬝ᵥ w) := mul_nonneg hexcessPos.le (selfDotProduct_nonneg w)
    nlinarith [hc, hnn]
  have hqqPos : 0 < (∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe := by
    have hc := hcover probe hprobePole
    have hpos : 0 < excess * (probe ⬝ᵥ probe) := mul_pos hexcessPos hprobePos
    nlinarith [hc, hpos]
  set flatU : ℝ := (∑ c ∈ selected, (design.atom c ⬝ᵥ u) ^ 2) - u ⬝ᵥ u with hflatU
  set flatQ : ℝ := (∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe
    with hflatQ
  set flatUQ : ℝ :=
    (∑ c ∈ selected, (design.atom c ⬝ᵥ u) * (design.atom c ⬝ᵥ probe)) - u ⬝ᵥ probe
    with hflatUQ
  have hcoupleU : polarCouplingVec design pole selected ⬝ᵥ u = flatU := by
    rw [← hwitness, sub_dotProduct, sum_dotProduct, hflatU]
    have hterm : ∀ c ∈ selected,
        ((design.atom c ⬝ᵥ u) • planeShadowVec design pole c) ⬝ᵥ u
          = (design.atom c ⬝ᵥ u) ^ 2 := by
      intro c _
      rw [smul_dotProduct, smul_eq_mul, planeShadowVec_dotProduct_polar design pole c hupole]
      ring
    rw [Finset.sum_congr rfl hterm]
  have hcoupleQ : polarCouplingVec design pole selected ⬝ᵥ probe = flatUQ := by
    rw [← hwitness, sub_dotProduct, sum_dotProduct, hflatUQ]
    have hterm : ∀ c ∈ selected,
        ((design.atom c ⬝ᵥ u) • planeShadowVec design pole c) ⬝ᵥ probe
          = (design.atom c ⬝ᵥ u) * (design.atom c ⬝ᵥ probe) := by
      intro c _
      rw [smul_dotProduct, smul_eq_mul,
        planeShadowVec_dotProduct_polar design pole c hprobePole]
    rw [Finset.sum_congr rfl hterm]
  set mixed : Fin rank → ℝ := flatQ • u - flatUQ • probe with hmixed
  have hmixedPole : mixed ⬝ᵥ design.atom pole = 0 := by
    rw [hmixed, sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      hupole, hprobePole]
    ring
  have hmixedRead : ∀ c : Fin size, design.atom c ⬝ᵥ mixed
      = flatQ * (design.atom c ⬝ᵥ u) - flatUQ * (design.atom c ⬝ᵥ probe) := by
    intro c
    rw [hmixed, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hmixedSum : ∑ c ∈ selected, (design.atom c ⬝ᵥ mixed) ^ 2
      = flatQ ^ 2 * (∑ c ∈ selected, (design.atom c ⬝ᵥ u) ^ 2)
        - 2 * flatQ * flatUQ
            * (∑ c ∈ selected, (design.atom c ⬝ᵥ u) * (design.atom c ⬝ᵥ probe))
        + flatUQ ^ 2 * (∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2) := by
    have hterm : ∀ c ∈ selected, (design.atom c ⬝ᵥ mixed) ^ 2
        = flatQ ^ 2 * (design.atom c ⬝ᵥ u) ^ 2
          - 2 * flatQ * flatUQ * ((design.atom c ⬝ᵥ u) * (design.atom c ⬝ᵥ probe))
          + flatUQ ^ 2 * (design.atom c ⬝ᵥ probe) ^ 2 := by
      intro c _
      rw [hmixedRead c]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hmixedSelf : mixed ⬝ᵥ mixed
      = flatQ ^ 2 * (u ⬝ᵥ u) - 2 * flatQ * flatUQ * (u ⬝ᵥ probe)
        + flatUQ ^ 2 * (probe ⬝ᵥ probe) := by
    rw [hmixed]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm probe u]
    ring
  have hmixedForm := hplaneForm mixed hmixedPole
  rw [hmixedSum, hmixedSelf] at hmixedForm
  have hcs : flatUQ ^ 2 ≤ flatU * flatQ := by
    have hscaled : 0 ≤ flatQ * (flatU * flatQ - flatUQ ^ 2) := by
      rw [hflatU, hflatQ, hflatUQ] at *
      nlinarith [hmixedForm]
    have hdrop : flatQ * flatUQ ^ 2 ≤ flatQ * (flatU * flatQ) := by nlinarith [hscaled]
    exact le_of_mul_le_mul_left hdrop hqqPos
  have hVuFlat : flatU < pairMass - leverage := by
    rw [← hcoupleU]
    exact hVu
  have hfinal : (polarCouplingVec design pole selected ⬝ᵥ probe) ^ 2
      < (pairMass - leverage) * flatQ := by
    rw [hcoupleQ]
    calc flatUQ ^ 2 ≤ flatU * flatQ := hcs
      _ < (pairMass - leverage) * flatQ := by
          exact mul_lt_mul_of_pos_right hVuFlat hqqPos
  have hLinvPos : (0 : ℝ) < leverage⁻¹ := inv_pos.mpr hpole
  calc (∑ c ∈ selected, (design.atom c ⬝ᵥ probe) * (design.atom c ⬝ᵥ unitNormal)) ^ 2
      = leverage⁻¹ * (polarCouplingVec design pole selected ⬝ᵥ probe) ^ 2 := by
        rw [hcoupleRead, mul_pow, inv_pow, hrootSq]
    _ < leverage⁻¹ * ((pairMass - leverage) * flatQ) :=
        mul_lt_mul_of_pos_left hfinal hLinvPos
    _ = ((∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2) - 1)
          * ((∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe) := by
        rw [hsumShape, hflatQ]
        field_simp

end WitnessEngine

/-! ## Part 2: the kill at the complement of a pole and a pair

The pair certificate opens the complement cover, the witnessed engine closes
the domination, and the complement has exactly `rank` labels in every cell
with `rank + 3 = size`. -/

section WitnessKill

variable {size rank : ℕ}

/-- **THE WITNESSED SCHUR KILL.**  In every cell with `rank + 3 = size`, a tie
carries no pole and pair with the sharp pair certificate, a priced excess, a
complement whose pole mass beats the leverage, and a witness of the survivor
plane equation that reads the coupling below the gap.  The only change against
the banked survivor Schur kill is the last hypothesis, and the change removes
the whole Cauchy-Schwarz loss. -/
theorem not_isTie_of_witnessSchur (hsize : rank + 3 = size)
    (design : WeightedDesign size rank) {pole first second : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (hne : first ≠ second)
    (hfirstPole : first ≠ pole) (hsecondPole : second ≠ pole)
    {S wcap excess : ℝ} (hwcapPos : 0 < wcap)
    (hwcap : ∀ c : Fin size, c ≠ pole → c ≠ first → c ≠ second → design.weight c ≤ wcap)
    (hSfirst : design.weight first * planeShadowSq design pole first ≤ S)
    (hSsecond : design.weight second * planeShadowSq design pole second ≤ S)
    (hdet : design.weight first * design.weight second
          * planeShadowPairing design pole first second ^ 2
        ≤ (S - design.weight first * planeShadowSq design pole first)
          * (S - design.weight second * planeShadowSq design pole second))
    (hexcess : wcap * (1 + excess) ≤ 1 - S) (hexcessPos : 0 < excess)
    (hz : design.atom pole ⬝ᵥ design.atom pole
        < ∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
            (design.atom c ⬝ᵥ design.atom pole) ^ 2)
    {u : Fin rank → ℝ} (hupole : u ⬝ᵥ design.atom pole = 0)
    (hwitness : (∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
          (design.atom c ⬝ᵥ u) • planeShadowVec design pole c) - u
        = polarCouplingVec design pole (((Finset.univ.erase pole).erase first).erase second))
    (hVu : polarCouplingVec design pole (((Finset.univ.erase pole).erase first).erase second)
          ⬝ᵥ u
        < (∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
              (design.atom c ⬝ᵥ design.atom pole) ^ 2)
          - design.atom pole ⬝ᵥ design.atom pole) :
    ¬ IsTie design := by
  classical
  intro htie
  have hcover := complementPair_polarCover design hpole hne hfirstPole hsecondPole hwcapPos
    hwcap hSfirst hSsecond hdet hexcess
  have hposDef := posDef_of_polarWitnessSchur design hpole hexcessPos hcover hz hupole
    hwitness hVu
  have hmemFirst : first ∈ Finset.univ.erase pole :=
    Finset.mem_erase.mpr ⟨hfirstPole, Finset.mem_univ first⟩
  have hmemSecond : second ∈ (Finset.univ.erase pole).erase first :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_erase.mpr ⟨hsecondPole, Finset.mem_univ second⟩⟩
  have hcard : ((((Finset.univ.erase pole).erase first).erase second)).card = size - 3 := by
    rw [Finset.card_erase_of_mem hmemSecond, Finset.card_erase_of_mem hmemFirst,
      Finset.card_erase_of_mem (Finset.mem_univ pole), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [hcard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-- The witnessed Schur kill at the deciding cell. -/
theorem not_isTie_of_witnessSchur_six_three (design : WeightedDesign 6 3)
    {pole first second : Fin 6}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (hne : first ≠ second)
    (hfirstPole : first ≠ pole) (hsecondPole : second ≠ pole)
    {S wcap excess : ℝ} (hwcapPos : 0 < wcap)
    (hwcap : ∀ c : Fin 6, c ≠ pole → c ≠ first → c ≠ second → design.weight c ≤ wcap)
    (hSfirst : design.weight first * planeShadowSq design pole first ≤ S)
    (hSsecond : design.weight second * planeShadowSq design pole second ≤ S)
    (hdet : design.weight first * design.weight second
          * planeShadowPairing design pole first second ^ 2
        ≤ (S - design.weight first * planeShadowSq design pole first)
          * (S - design.weight second * planeShadowSq design pole second))
    (hexcess : wcap * (1 + excess) ≤ 1 - S) (hexcessPos : 0 < excess)
    (hz : design.atom pole ⬝ᵥ design.atom pole
        < ∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
            (design.atom c ⬝ᵥ design.atom pole) ^ 2)
    {u : Fin 3 → ℝ} (hupole : u ⬝ᵥ design.atom pole = 0)
    (hwitness : (∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
          (design.atom c ⬝ᵥ u) • planeShadowVec design pole c) - u
        = polarCouplingVec design pole (((Finset.univ.erase pole).erase first).erase second))
    (hVu : polarCouplingVec design pole (((Finset.univ.erase pole).erase first).erase second)
          ⬝ᵥ u
        < (∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
              (design.atom c ⬝ᵥ design.atom pole) ^ 2)
          - design.atom pole ⬝ᵥ design.atom pole) :
    ¬ IsTie design :=
  not_isTie_of_witnessSchur (by norm_num) design hpole hne hfirstPole hsecondPole hwcapPos
    hwcap hSfirst hSsecond hdet hexcess hexcessPos hz hupole hwitness hVu

/-- **THE SHARP TIE LAW OF THE DECIDING CELL.**  At every `(6,3)` tie, every
pole, every pair with the sharp certificate, every priced excess, and EVERY
witness of the survivor plane equation: the complement triple keeps its pole
mass at or below the leverage, or the witness reading spends the whole gap.
The banked `Gtz.tie_survivorSchur_six_three` reads the coupling length; this
law reads the exact Schur complement, and the probes show the complex ties of
the deciding cell saturate it with equality. -/
theorem tie_witnessSchur_six_three (design : WeightedDesign 6 3) (htie : IsTie design)
    {pole first second : Fin 6}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (hne : first ≠ second)
    (hfirstPole : first ≠ pole) (hsecondPole : second ≠ pole)
    {S wcap excess : ℝ} (hwcapPos : 0 < wcap)
    (hwcap : ∀ c : Fin 6, c ≠ pole → c ≠ first → c ≠ second → design.weight c ≤ wcap)
    (hSfirst : design.weight first * planeShadowSq design pole first ≤ S)
    (hSsecond : design.weight second * planeShadowSq design pole second ≤ S)
    (hdet : design.weight first * design.weight second
          * planeShadowPairing design pole first second ^ 2
        ≤ (S - design.weight first * planeShadowSq design pole first)
          * (S - design.weight second * planeShadowSq design pole second))
    (hexcess : wcap * (1 + excess) ≤ 1 - S) (hexcessPos : 0 < excess)
    {u : Fin 3 → ℝ} (hupole : u ⬝ᵥ design.atom pole = 0)
    (hwitness : (∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
          (design.atom c ⬝ᵥ u) • planeShadowVec design pole c) - u
        = polarCouplingVec design pole (((Finset.univ.erase pole).erase first).erase second)) :
    (∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
        (design.atom c ⬝ᵥ design.atom pole) ^ 2)
      ≤ design.atom pole ⬝ᵥ design.atom pole
    ∨ (∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
          (design.atom c ⬝ᵥ design.atom pole) ^ 2)
        - design.atom pole ⬝ᵥ design.atom pole
      ≤ polarCouplingVec design pole (((Finset.univ.erase pole).erase first).erase second)
        ⬝ᵥ u := by
  by_contra hcontra
  rw [not_or, not_le, not_le] at hcontra
  exact not_isTie_of_witnessSchur_six_three design hpole hne hfirstPole hsecondPole hwcapPos
    hwcap hSfirst hSsecond hdet hexcess hexcessPos hcontra.1 hupole hwitness hcontra.2 htie

end WitnessKill

/-! ## Part 3: the fifth free bundle

The sharp tie law costs nothing at a tie, thus the residual can hand it to the
prover.  The guards `rank + 3 = size` and the positive leverage sit inside the
bundle, thus the bundle is vacuously free at every cell of the wrong shape and
the `(5,3)` calibration transports unchanged. -/

section WitnessBundle

variable {size rank : ℕ}

/-- **THE WITNESS SCHUR BOUND.**  What a tie supplies at a pole: for every
pair with the sharp certificate, every priced excess, and every witness of the
survivor plane equation, the complement keeps its pole mass at or below the
leverage or the witness reading spends the whole gap. -/
def PolarWitnessSchurBound (design : WeightedDesign size rank) (pole : Fin size) : Prop :=
  ∀ first second : Fin size, rank + 3 = size →
    0 < design.atom pole ⬝ᵥ design.atom pole →
    first ≠ second → first ≠ pole → second ≠ pole →
    ∀ S wcap excess : ℝ, 0 < wcap →
      (∀ c : Fin size, c ≠ pole → c ≠ first → c ≠ second → design.weight c ≤ wcap) →
      design.weight first * planeShadowSq design pole first ≤ S →
      design.weight second * planeShadowSq design pole second ≤ S →
      design.weight first * design.weight second
          * planeShadowPairing design pole first second ^ 2
        ≤ (S - design.weight first * planeShadowSq design pole first)
          * (S - design.weight second * planeShadowSq design pole second) →
      wcap * (1 + excess) ≤ 1 - S → 0 < excess →
      ∀ u : Fin rank → ℝ, u ⬝ᵥ design.atom pole = 0 →
        (∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
            (design.atom c ⬝ᵥ u) • planeShadowVec design pole c) - u
          = polarCouplingVec design pole
              (((Finset.univ.erase pole).erase first).erase second) →
        (∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
            (design.atom c ⬝ᵥ design.atom pole) ^ 2)
          ≤ design.atom pole ⬝ᵥ design.atom pole
        ∨ (∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
              (design.atom c ⬝ᵥ design.atom pole) ^ 2)
            - design.atom pole ⬝ᵥ design.atom pole
          ≤ polarCouplingVec design pole
              (((Finset.univ.erase pole).erase first).erase second) ⬝ᵥ u

/-- **THE WITNESS BOUND IS FREE AT EVERY TIE.**  No predecessor rank, no
primitivity, and no overshooting pole are consumed. -/
theorem polarWitnessSchurBound_of_isTie (design : WeightedDesign size rank)
    (htie : IsTie design) (pole : Fin size) : PolarWitnessSchurBound design pole := by
  intro first second hsize hpolePos hne hfirstPole hsecondPole S wcap excess hwcapPos hwcap
    hSfirst hSsecond hdet hexcess hexcessPos u hupole hwitness
  by_contra hcontra
  rw [not_or, not_le, not_le] at hcontra
  exact not_isTie_of_witnessSchur hsize design hpolePos hne hfirstPole hsecondPole hwcapPos
    hwcap hSfirst hSsecond hdet hexcess hexcessPos hcontra.1 hupole hwitness hcontra.2 htie

end WitnessBundle

/-! ## Part 4: the residual narrowed a fifth time

The five-bundle residual is weaker than every shipped residual, every consumer
runs on it, the `(5,3)` instance stays FALSE, and the guardrail stays checked.
The realness audit adds the standing constraint: complex ties of the deciding
cell satisfy the whole hypothesis package, thus the discharge of this residual
must consume a real-only ingredient. -/

section WitnessResidual

variable {size rank : ℕ}

/-- **THE FIVE-BUNDLE TILT RESIDUAL.**  `Gtz.PolarTiltSelectionSpread` with
the witness Schur bound handed to the prover as well. -/
def PolarTiltSelectionWitness (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (pole : Fin size) (covering : Finset (Fin size))
      (margin : ℝ),
    IsPrimitiveDesign design →
    IsTie design →
    1 < design.atom pole ⬝ᵥ design.atom pole →
    PolarSaturationBudget design pole →
    PolarDeletionHeavy design pole →
    PolarSetDeletionHeavy design pole →
    PolarSpreadSurvivorHeavy design pole →
    PolarWitnessSchurBound design pole →
    0 < margin →
    covering.card = rank - 1 → pole ∉ covering →
    (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) →
    ∃ selected : Finset (Fin size), selected.card = rank - 1 ∧ pole ∉ selected
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2)
      ∧ ∑ label ∈ selected, (design.atom label ⬝ᵥ design.atom pole) ^ 2
          < margin * (design.atom pole ⬝ᵥ design.atom pole)
              * (design.atom pole ⬝ᵥ design.atom pole - 1)

/-- The five-bundle residual is weaker than the four-bundle one. -/
theorem polarTiltSelectionWitness_of_polarTiltSelectionSpread
    (htilt : PolarTiltSelectionSpread size rank) :
    PolarTiltSelectionWitness size rank :=
  fun design pole covering margin hprimitive htie hlong hbudget hheavy hset hspread _hwitness
    hmargin hcard hnotMem hcover =>
    htilt design pole covering margin hprimitive htie hlong hbudget hheavy hset hspread
      hmargin hcard hnotMem hcover

/-- The five-bundle residual is weaker than the thrice-narrowed one. -/
theorem polarTiltSelectionWitness_of_polarTiltSelectionSetDeletion
    (htilt : PolarTiltSelectionSetDeletion size rank) :
    PolarTiltSelectionWitness size rank :=
  polarTiltSelectionWitness_of_polarTiltSelectionSpread
    (polarTiltSelectionSpread_of_polarTiltSelectionSetDeletion htilt)

/-- The five-bundle residual is weaker than the twice-narrowed one. -/
theorem polarTiltSelectionWitness_of_polarTiltSelectionDeletion
    (htilt : PolarTiltSelectionDeletion size rank) :
    PolarTiltSelectionWitness size rank :=
  polarTiltSelectionWitness_of_polarTiltSelectionSpread
    (polarTiltSelectionSpread_of_polarTiltSelectionDeletion htilt)

/-- The five-bundle residual is weaker than the shipped one. -/
theorem polarTiltSelectionWitness_of_polarTiltSelection
    (htilt : PolarTiltSelection size rank) : PolarTiltSelectionWitness size rank :=
  polarTiltSelectionWitness_of_polarTiltSelectionSpread
    (polarTiltSelectionSpread_of_polarTiltSelection htilt)

/-- **THE HINGE FROM THE FIVE-BUNDLE RESIDUAL.**  All five bundles are
theorems at a tie, thus the fifth narrowing costs nothing downstream. -/
theorem hingeHoldsAtSize_of_polarTiltWitness (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionWitness size rank) : HingeHoldsAtSize size rank := by
  classical
  intro design htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  obtain ⟨pole, hlong⟩ := exists_overshooting_atom design hrank
  obtain ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin hrank hpredecessor design hlong
  obtain ⟨selected, hselCard, hselNotMem, hselCover, hselTilt⟩ :=
    htilt design pole covering margin hprimitive htie hlong
      (polarSaturationBudget_of_isTie hrank hpredecessor design htie hlong)
      (polarDeletionHeavy_of_isTie hrank hpredecessor design htie hlong hroom)
      (polarSetDeletionHeavy_of_isTie hrank hpredecessor design htie hlong)
      (polarSpreadSurvivorHeavy_of_isTie hrank hpredecessor design htie hlong)
      (polarWitnessSchurBound_of_isTie design htie pole)
      hmarginPos hcard hnotMem hcover
  have hposDef := posDef_insert_of_polarCover design hselNotMem hlong hmarginPos hselCover
    hselTilt
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hselNotMem, hselCard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-! ### Every consumer of the shipped residual, on the five-bundle one -/

/-- Arm (i). -/
theorem stressFreeArmAt_of_polarTiltWitness (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionWitness size rank) : StressFreeArmAt size rank :=
  fun design _hfree htie =>
    hingeHoldsAtSize_of_polarTiltWitness hrank hpredecessor hroom htilt design htie

/-- Arm (ii). -/
theorem balancedArmAt_of_polarTiltWitness (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionWitness size rank) : BalancedArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltWitness hrank hpredecessor hroom htilt design htie

/-- Arm (iii). -/
theorem degenerateArmAt_of_polarTiltWitness (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionWitness size rank) : DegenerateArmAt size rank :=
  fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
    hingeHoldsAtSize_of_polarTiltWitness hrank hpredecessor hroom htilt design htie

/-- The partial-support sub-arm. -/
theorem balancedPartialSupportArmAt_of_polarTiltWitness (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionWitness size rank) : BalancedPartialSupportArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hunsupported _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltWitness hrank hpredecessor hroom htilt design htie

/-- The full-support sub-arm. -/
theorem balancedFullSupportArmAt_of_polarTiltWitness (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionWitness size rank) : BalancedFullSupportArmAt size rank :=
  fun design _stressCoeff _hstress _hfull htie =>
    hingeHoldsAtSize_of_polarTiltWitness hrank hpredecessor hroom htilt design htie

/-- The repaired degenerate cover. -/
theorem degenerateHyperplaneCover_of_polarTiltWitness (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionWitness size rank) : DegenerateHyperplaneCover size rank := by
  intro design _stressCoeff _unitNormal _pole hprimitive htie _hstressNe _hunit _hstress
    _hsupport _hpole
  exact absurd
    (hingeHoldsAtSize_of_polarTiltWitness hrank hpredecessor hroom htilt design htie)
    ((isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive)

/-- **THE COLLAPSE, ON THE FIVE-BUNDLE RESIDUAL.** -/
theorem polarTiltWitness_closes_every_arm (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionWitness size rank) :
    HingeHoldsAtSize size rank ∧ StressFreeArmAt size rank ∧ BalancedArmAt size rank
      ∧ DegenerateArmAt size rank ∧ BalancedPartialSupportArmAt size rank
      ∧ BalancedFullSupportArmAt size rank ∧ DegenerateHyperplaneCover size rank :=
  ⟨hingeHoldsAtSize_of_polarTiltWitness hrank hpredecessor hroom htilt,
    stressFreeArmAt_of_polarTiltWitness hrank hpredecessor hroom htilt,
    balancedArmAt_of_polarTiltWitness hrank hpredecessor hroom htilt,
    degenerateArmAt_of_polarTiltWitness hrank hpredecessor hroom htilt,
    balancedPartialSupportArmAt_of_polarTiltWitness hrank hpredecessor hroom htilt,
    balancedFullSupportArmAt_of_polarTiltWitness hrank hpredecessor hroom htilt,
    degenerateHyperplaneCover_of_polarTiltWitness hrank hpredecessor hroom htilt⟩

/-! ### The registry obligations, on the five-bundle residual -/

/-- The threshold cell obligation of the registry. -/
theorem thresholdCellHingeRankFourAndUp_of_polarTiltWitness
    (htilt : ∀ rank : ℕ, 4 ≤ rank →
      PolarTiltSelectionWitness (thresholdSize rank) rank) :
    ∀ rank : ℕ, 4 ≤ rank → GtzWeightedAll (rank - 1) →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor _hcell design htie
  have hroom : rank + 1 ≤ rank * (rank + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc (rank + 1) * 2 ≤ (rank + 1) * rank := Nat.mul_le_mul_left _ (by omega)
      _ = rank * (rank + 1) := Nat.mul_comm _ _
  exact hingeHoldsAtSize_of_polarTiltWitness (by omega) hpredecessor hroom (htilt rank hrank)
    design htie

/-- The sub-threshold band obligation of the registry. -/
theorem subThresholdBandHinge_of_polarTiltWitness
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size < thresholdSize rank →
      PolarTiltSelectionWitness size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor size hlow hhigh _hcell design htie
  exact hingeHoldsAtSize_of_polarTiltWitness (by omega) hpredecessor (by omega)
    (htilt rank size hrank hlow hhigh) design htie

/-- The whole sharp window, from one five-bundle residual per cell. -/
theorem sharpWindowHinge_of_polarTiltWitness
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size ≤ thresholdSize rank →
      PolarTiltSelectionWitness size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        HingeHoldsAtSize size rank := by
  intro rank hrank hpredecessor size hlow hhigh
  exact hingeHoldsAtSize_of_polarTiltWitness (by omega) hpredecessor (by omega)
    (htilt rank size hrank hlow hhigh)

/-- Arm (i) at the deciding cell of a rank. -/
theorem thresholdStressFreeArm_of_polarTiltWitness (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionWitness (thresholdSize rank) rank) :
    ThresholdStressFreeArm rank :=
  stressFreeArmAt_of_polarTiltWitness hrank hpredecessor hroom htilt

/-- Arm (ii) at the deciding cell of a rank. -/
theorem thresholdBalancedArm_of_polarTiltWitness (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionWitness (thresholdSize rank) rank) :
    ThresholdBalancedArm rank :=
  balancedArmAt_of_polarTiltWitness hrank hpredecessor hroom htilt

/-- Arm (iii) at the deciding cell of a rank. -/
theorem thresholdDegenerateArm_of_polarTiltWitness (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionWitness (thresholdSize rank) rank) :
    ThresholdDegenerateArm rank :=
  degenerateArmAt_of_polarTiltWitness hrank hpredecessor hroom htilt

end WitnessResidual

/-! ## Part 5: the deciding cell, the calibration, and the guardrail -/

section WitnessSixThree

/-- **THE DECIDING CELL OF RANK THREE FROM THE FIVE-BUNDLE RESIDUAL ALONE.** -/
theorem hingeHoldsAtSize_six_three_of_polarTiltWitness
    (htilt : PolarTiltSelectionWitness 6 3) : HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_polarTiltWitness (by norm_num) gtz_rank_two (by norm_num) htilt

/-- The three rank-three arms from the five-bundle residual. -/
theorem thresholdArms_rank_three_of_polarTiltWitness
    (htilt : PolarTiltSelectionWitness 6 3) :
    ThresholdStressFreeArm 3 ∧ ThresholdBalancedArm 3 ∧ ThresholdDegenerateArm 3 := by
  have hhinge := hingeHoldsAtSize_six_three_of_polarTiltWitness htilt
  exact ⟨fun design _hfree htie => hhinge design htie,
    fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie => hhinge design htie,
    fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
      hhinge design htie⟩

/-- **THE DECIDING CELL, FROM THE FIVE-BUNDLE RESIDUAL ALONE.** -/
theorem gtzWeighted_six_three_of_polarTiltWitness
    (htilt : PolarTiltSelectionWitness 6 3) : GtzWeighted 6 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltWitness htilt
  exact GeneralRankReach.gtzWeighted_six_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **ALL OF RANK THREE, FROM THE FIVE-BUNDLE RESIDUAL ALONE.** -/
theorem gtzWeightedAll_three_of_polarTiltWitness
    (htilt : PolarTiltSelectionWitness 6 3) : GtzWeightedAll 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltWitness htilt
  exact GeneralRankReach.gtzWeightedAll_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **THE FIVE-BUNDLE RESIDUAL IS FALSE AT `(5,3)`.**  The witness bundle is
vacuous away from `rank + 3 = size`, thus the calibration transports through
the fifth narrowing unchanged. -/
theorem not_polarTiltSelectionWitness_five_three :
    ¬ PolarTiltSelectionWitness 5 3 :=
  fun htilt => not_hingeHoldsAtSize_five_three
    (hingeHoldsAtSize_of_polarTiltWitness (by norm_num) gtz_rank_two (by norm_num) htilt)

/-- **THE GUARDRAIL.**  The `(6,3)` tie in the tree is not primitive, thus it
does not touch the five-bundle residual, and the last-stage Prop stays
refuted. -/
theorem sixSplitDiamondDesign_spares_polarTiltWitness :
    ¬ RankSuccShrinks 6 3 ∧ IsTie sixSplitDiamondDesign
      ∧ ¬ IsPrimitiveDesign sixSplitDiamondDesign
      ∧ ¬ PolarTiltSelectionWitness 5 3 :=
  ⟨not_rankSuccShrinks_six_three, sixSplitDiamondDesign_isTie,
    not_isPrimitiveDesign_sixSplitDiamondDesign, not_polarTiltSelectionWitness_five_three⟩

end WitnessSixThree

/-! ## Part 6: the bracket sign platform

The scalar triple product of the pole with two atoms is the polar wedge.  Its
square is the Gram determinant, the shadow calculus reads that square as the
plane Gram complement, and the product of two brackets with a shared slot is a
polynomial in the pairings.  Over the reals these laws determine the bracket
up to a finite sign choice; over the complex field the analogous quantity
carries a free phase.  Sign enumeration on this platform is the approved
real-only exit of the polar lane. -/

section BracketPlatform

variable {size rank : ℕ}

/-- **THE SQUARE OF THE BRACKET IS THE GRAM DETERMINANT.**  The bracket is
recovered from the pairing data up to one sign. -/
theorem tripleBracket_sq_eq_gramDet (poleVec firstVec secondVec : Fin 3 → ℝ) :
    tripleBracket poleVec firstVec secondVec ^ 2
      = (poleVec ⬝ᵥ poleVec) * (firstVec ⬝ᵥ firstVec) * (secondVec ⬝ᵥ secondVec)
        + 2 * (poleVec ⬝ᵥ firstVec) * (poleVec ⬝ᵥ secondVec) * (firstVec ⬝ᵥ secondVec)
        - (poleVec ⬝ᵥ poleVec) * (firstVec ⬝ᵥ secondVec) ^ 2
        - (firstVec ⬝ᵥ firstVec) * (poleVec ⬝ᵥ secondVec) ^ 2
        - (secondVec ⬝ᵥ secondVec) * (poleVec ⬝ᵥ firstVec) ^ 2 := by
  simp only [tripleBracket_eq, dotProduct, Fin.sum_univ_three]
  ring

/-- **THE PRODUCT OF TWO BRACKETS WITH A SHARED FIRST SLOT.**  The Binet
identity: the product is the determinant of the cross pairing matrix, a
polynomial in the six pairings. -/
theorem tripleBracket_mul_sharedLeft
    (poleVec firstVec secondVec thirdVec fourthVec : Fin 3 → ℝ) :
    tripleBracket poleVec firstVec secondVec * tripleBracket poleVec thirdVec fourthVec
      = (poleVec ⬝ᵥ poleVec)
          * ((firstVec ⬝ᵥ thirdVec) * (secondVec ⬝ᵥ fourthVec)
            - (firstVec ⬝ᵥ fourthVec) * (secondVec ⬝ᵥ thirdVec))
        - (poleVec ⬝ᵥ thirdVec)
          * ((firstVec ⬝ᵥ poleVec) * (secondVec ⬝ᵥ fourthVec)
            - (firstVec ⬝ᵥ fourthVec) * (secondVec ⬝ᵥ poleVec))
        + (poleVec ⬝ᵥ fourthVec)
          * ((firstVec ⬝ᵥ poleVec) * (secondVec ⬝ᵥ thirdVec)
            - (firstVec ⬝ᵥ thirdVec) * (secondVec ⬝ᵥ poleVec)) := by
  simp only [tripleBracket_eq, dotProduct, Fin.sum_univ_three]
  ring

/-- **THE SHADOW PAIRING NEVER BEATS THE SHADOW ENERGIES.**  The plane
Cauchy-Schwarz, division free, at every rank. -/
theorem planeShadowPairing_sq_le (design : WeightedDesign size rank)
    {pole : Fin size} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (first second : Fin size) :
    planeShadowPairing design pole first second ^ 2
      ≤ planeShadowSq design pole first * planeShadowSq design pole second := by
  rw [← planeShadowVec_dotProduct_pair design hpole first second,
    ← planeShadowVec_dotProduct_self design hpole first,
    ← planeShadowVec_dotProduct_self design hpole second]
  exact dotProduct_sq_le_mul_self _ _

/-- **THE BRACKET SQUARE IN THE SHADOW CALCULUS.**  At rank three the square
of the polar wedge is the leverage times the plane Gram complement of the two
shadows.  Over the reals the wedge is the signed square root; over the complex
field the analogous quantity carries a free phase, and this is exactly the
real-only information the polar lane owns. -/
theorem tripleBracket_sq_eq_planeShadow {m : ℕ} (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (first second : Fin m) :
    tripleBracket (design.atom pole) (design.atom first) (design.atom second) ^ 2
      = (design.atom pole ⬝ᵥ design.atom pole)
        * (planeShadowSq design pole first * planeShadowSq design pole second
          - planeShadowPairing design pole first second ^ 2) := by
  have hLne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  have hfirstComm : design.atom pole ⬝ᵥ design.atom first
      = design.atom first ⬝ᵥ design.atom pole := dotProduct_comm _ _
  have hsecondComm : design.atom pole ⬝ᵥ design.atom second
      = design.atom second ⬝ᵥ design.atom pole := dotProduct_comm _ _
  rw [tripleBracket_sq_eq_gramDet, planeShadowSq, planeShadowSq, planeShadowPairing,
    hfirstComm, hsecondComm]
  field_simp
  ring

/-- **THE BRACKET PRODUCT IN THE SHADOW CALCULUS.**  Two wedges that share a
slot multiply to the leverage times a polynomial in the pairings: the sign of
one wedge transports to the sign of the other through pairing data alone. -/
theorem tripleBracket_mul_eq_planeShadow {m : ℕ} (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (first shared second : Fin m) :
    tripleBracket (design.atom pole) (design.atom first) (design.atom shared)
        * tripleBracket (design.atom pole) (design.atom shared) (design.atom second)
      = (design.atom pole ⬝ᵥ design.atom pole)
        * (planeShadowPairing design pole first shared
            * planeShadowPairing design pole shared second
          - planeShadowSq design pole shared
            * planeShadowPairing design pole first second) := by
  have hLne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  have hsharedComm : design.atom pole ⬝ᵥ design.atom shared
      = design.atom shared ⬝ᵥ design.atom pole := dotProduct_comm _ _
  have hsecondComm : design.atom pole ⬝ᵥ design.atom second
      = design.atom second ⬝ᵥ design.atom pole := dotProduct_comm _ _
  rw [tripleBracket_mul_sharedLeft, planeShadowSq, planeShadowPairing, planeShadowPairing,
    planeShadowPairing, hsharedComm, hsecondComm]
  field_simp
  ring

end BracketPlatform

end Gtz
