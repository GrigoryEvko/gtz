/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.PolarWitnessSchur

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The plane Cramer calculus and the closed cross witness

The witnessed Schur kill of `Gtz.Reduction.PolarWitnessSchur` consumes a
witness of the survivor plane equation, and the caller must produce it.  This
file removes the production step: the witness has a CLOSED FORM in the bracket
calculus, and the closed form turns the sharp tie law of the deciding cell
into a polynomial law of the pairing data.

## 1. The Cramer laws

Four vectors of `ℝ³` are dependent, and the coefficients of the dependency
are the four omitted brackets.  `Gtz.tripleBracket_cramer` is the vector form,
`Gtz.tripleBracket_cramer_dot` reads it at a probe,
`Gtz.tripleBracket_reading_cycle` reads it at a pole, and
`Gtz.tripleBracket_pole_cramer` solves it for the pole component.  The
three-term relation `Gtz.tripleBracket_grassmannPluecker` is the
multiplicative law of the same platform.  Over the reals these laws transport
bracket SIGNS.  The probes show that the complex obstruction family breaks
their Hermitian counterparts in two layers: the measured complex ties break
the anchored Pluecker products at a normalized defect above `0.52`, and the
complex-metric deformations of real direction data keep those products but
break every law that couples a bracket to a pairing.  The laws of this file
couple brackets to pairings.

## 2. The shadow transport

`Gtz.tripleBracket_shadow_transport` is the sine addition law of the pole
plane: the bracket of a shadow pair transports across a middle shadow through
the shadow pairings alone.  It is the linear companion of the landed product
law `Gtz.tripleBracket_mul_eq_planeShadow`.

## 3. The closed cross witness

`Gtz.polarCrossWitnessVec` is the adjugate of the survivor plane form applied
to the coupling vector, written in the bracket calculus.  The rotation
identity `Gtz.tripleBracket_smul_bracketNormal` converts it to the adjugate
form, and the plane Cayley-Hamilton law
`Gtz.sum_atom_dot_smul_planeShadowVec_cayleyHamilton` closes its survivor
plane equation at the scale `leverage * polarPlaneDet`.

## 4. The scaled engine, the closed kill, and the polynomial tie law

`Gtz.posDef_of_polarWitnessSchur_scaled` runs the witnessed engine at an
arbitrary positive scale of the plane equation.
`Gtz.not_isTie_of_crossWitnessSchur_six_three` is the witnessed Schur kill of
the deciding cell with every hypothesis a polynomial inequality of the
pairing data: no witness quantifier is left.  Its contrapositive
`Gtz.tie_crossWitnessSchur_six_three` is the sharp tie law in closed form.
The probes show that the complex ties saturate this law exactly at the three
pole choices of their unique argmax triple, and that every real near-tie of
the measured slice fires it with margin at least `0.047`.
-/

namespace Gtz

open Matrix Finset

/-! ## Part 1: the Cramer laws -/

section CramerLaws

/-- **THE CRAMER DEPENDENCY.**  Four vectors of `ℝ³` are dependent, with the
four omitted brackets as coefficients.  The master law of the real bracket
calculus: every transport law of the polar lane specializes it. -/
theorem tripleBracket_cramer (x y z w : Fin 3 → ℝ) :
    tripleBracket y z w • x - tripleBracket x z w • y
      + tripleBracket x y w • z - tripleBracket x y z • w = 0 := by
  funext coord
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
    tripleBracket_eq]
  fin_cases coord <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

/-- **THE CRAMER READING LAW.**  The dependency read at an arbitrary probe:
brackets and pairings are coupled by a four-term linear law. -/
theorem tripleBracket_cramer_dot (x y z w v : Fin 3 → ℝ) :
    tripleBracket y z w * (x ⬝ᵥ v) - tripleBracket x z w * (y ⬝ᵥ v)
      + tripleBracket x y w * (z ⬝ᵥ v) - tripleBracket x y z * (w ⬝ᵥ v) = 0 := by
  simp only [tripleBracket_eq, dotProduct, Fin.sum_univ_three]
  ring

/-- **THE THREE-TERM GRASSMANN-PLUECKER RELATION.**  The anchored products of
brackets satisfy the classical alternating law. -/
theorem tripleBracket_grassmannPluecker (x y z u v : Fin 3 → ℝ) :
    tripleBracket x y z * tripleBracket x u v - tripleBracket x y u * tripleBracket x z v
      + tripleBracket x y v * tripleBracket x z u = 0 := by
  simp only [tripleBracket_eq]
  ring

/-- **THE READING CYCLE.**  The bracket of three atoms, scaled by the
leverage, is an alternating combination of their pole readings and the polar
brackets.  This is the Cramer law read at the pole. -/
theorem tripleBracket_reading_cycle (p x y z : Fin 3 → ℝ) :
    (p ⬝ᵥ p) * tripleBracket x y z
      = (x ⬝ᵥ p) * tripleBracket p y z - (y ⬝ᵥ p) * tripleBracket p x z
        + (z ⬝ᵥ p) * tripleBracket p x y := by
  simp only [tripleBracket_eq, dotProduct, Fin.sum_univ_three]
  ring

/-- **THE PLANE DEGENERACY.**  Three vectors orthogonal to a vector of
positive leverage are coplanar, thus their bracket vanishes.  The reading
cycle proves it with no case analysis. -/
theorem tripleBracket_eq_zero_of_pole_orthogonal {p : Fin 3 → ℝ} (x y z : Fin 3 → ℝ)
    (hp : 0 < p ⬝ᵥ p) (hx : x ⬝ᵥ p = 0) (hy : y ⬝ᵥ p = 0) (hz : z ⬝ᵥ p = 0) :
    tripleBracket x y z = 0 := by
  have hcycle := tripleBracket_reading_cycle p x y z
  rw [hx, hy, hz, zero_mul, zero_mul, zero_mul, sub_zero, add_zero] at hcycle
  exact (mul_eq_zero.mp hcycle).resolve_left (ne_of_gt hp)

/-- **THE POLE CRAMER LAW.**  The dependency solved for the pole direction:
the alternating polar-bracket combination of three vectors is their own
bracket times the pole. -/
theorem tripleBracket_pole_cramer (p x y z : Fin 3 → ℝ) :
    tripleBracket p y z • x - tripleBracket p x z • y + tripleBracket p x y • z
      = tripleBracket x y z • p := by
  funext coord
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, tripleBracket_eq]
  fin_cases coord <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

/-- **THE ROTATION IDENTITY.**  A bracket times the bracket normal of its
first two slots decomposes over the three slots with pairing coefficients.
On the pole plane the corrections die and this is the quarter-turn action of
the plane. -/
theorem tripleBracket_smul_bracketNormal (poleVec baseVec readVec : Fin 3 → ℝ) :
    tripleBracket poleVec baseVec readVec • bracketNormal poleVec baseVec
      = ((poleVec ⬝ᵥ poleVec) * (baseVec ⬝ᵥ baseVec) - (baseVec ⬝ᵥ poleVec) ^ 2) • readVec
        + ((baseVec ⬝ᵥ poleVec) * (readVec ⬝ᵥ poleVec)
            - (poleVec ⬝ᵥ poleVec) * (baseVec ⬝ᵥ readVec)) • baseVec
        + ((baseVec ⬝ᵥ poleVec) * (baseVec ⬝ᵥ readVec)
            - (baseVec ⬝ᵥ baseVec) * (readVec ⬝ᵥ poleVec)) • poleVec := by
  funext coord
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, tripleBracket_eq, bracketNormal,
    dotProduct, Fin.sum_univ_three]
  fin_cases coord <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    ring

/-- **THE GRAM CRAMER DECOMPOSITION.**  The Gram determinant of two vectors
spreads any third vector over the pair, with one bracket correction along the
bracket normal.  On a plane the correction dies and this is the Cramer solve
in the Gram metric. -/
theorem gramDet_smul_decomp (leftVec rightVec readVec : Fin 3 → ℝ) :
    ((leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) - (leftVec ⬝ᵥ rightVec) ^ 2) • readVec
      = ((leftVec ⬝ᵥ readVec) * (rightVec ⬝ᵥ rightVec)
          - (rightVec ⬝ᵥ readVec) * (leftVec ⬝ᵥ rightVec)) • leftVec
        + ((rightVec ⬝ᵥ readVec) * (leftVec ⬝ᵥ leftVec)
            - (leftVec ⬝ᵥ readVec) * (leftVec ⬝ᵥ rightVec)) • rightVec
        + tripleBracket leftVec rightVec readVec • bracketNormal leftVec rightVec := by
  funext coord
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, tripleBracket_eq, bracketNormal,
    dotProduct, Fin.sum_univ_three]
  fin_cases coord <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    ring

/-- The bracket normal reads zero at its own first slot. -/
theorem bracketNormal_dotProduct_left (u v : Fin 3 → ℝ) :
    bracketNormal u v ⬝ᵥ u = 0 := by
  simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

end CramerLaws

/-! ## Part 2: the shadow transport -/

section ShadowTransport

/-- **THE SHADOW TRANSPORT.**  The sine addition law of the pole plane: the
polar bracket of a shadow pair transports across a middle shadow through the
shadow pairings.  This is the linear companion of the landed product law
`Gtz.tripleBracket_mul_eq_planeShadow`, and it is the law the complex-metric
deformations of real direction data cannot keep. -/
theorem tripleBracket_shadow_transport {m : ℕ} (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (first middle second : Fin m) :
    tripleBracket (design.atom pole) (design.atom first) (design.atom second)
        * planeShadowSq design pole middle
      = planeShadowPairing design pole first middle
          * tripleBracket (design.atom pole) (design.atom middle) (design.atom second)
        + tripleBracket (design.atom pole) (design.atom first) (design.atom middle)
          * planeShadowPairing design pole middle second := by
  have hLne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  rw [planeShadowSq, planeShadowPairing, planeShadowPairing]
  field_simp
  simp only [tripleBracket_eq, dotProduct, Fin.sum_univ_three]
  ring

/-- The shadow pairing is symmetric. -/
theorem planeShadowPairing_comm {size rank : ℕ} (design : WeightedDesign size rank)
    (pole first second : Fin size) :
    planeShadowPairing design pole first second
      = planeShadowPairing design pole second first := by
  rw [planeShadowPairing, planeShadowPairing,
    dotProduct_comm (design.atom second) (design.atom first)]
  ring

/-- An atom reads a shadow as the shadow pairing. -/
theorem atom_dotProduct_planeShadowVec {size rank : ℕ} (design : WeightedDesign size rank)
    (pole first second : Fin size) :
    design.atom first ⬝ᵥ planeShadowVec design pole second
      = planeShadowPairing design pole first second := by
  rw [planeShadowVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, planeShadowPairing]
  ring

/-- A shadow reads zero at the pole. -/
theorem planeShadowVec_dotProduct_pole {size rank : ℕ} (design : WeightedDesign size rank)
    {pole : Fin size} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (label : Fin size) :
    planeShadowVec design pole label ⬝ᵥ design.atom pole = 0 := by
  have hLne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  rw [planeShadowVec, sub_dotProduct, smul_dotProduct, smul_eq_mul,
    div_mul_cancel₀ _ hLne, sub_self]

/-- The coupling vector reads zero at the pole. -/
theorem polarCouplingVec_dotProduct_pole {size rank : ℕ} (design : WeightedDesign size rank)
    {pole : Fin size} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (selected : Finset (Fin size)) :
    polarCouplingVec design pole selected ⬝ᵥ design.atom pole = 0 := by
  rw [polarCouplingVec, sum_dotProduct]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [smul_dotProduct, planeShadowVec_dotProduct_pole design hpole c, smul_eq_mul, mul_zero]

end ShadowTransport

/-! ## Part 3: the closed cross witness

The adjugate of the survivor plane form applied to the coupling vector,
written in the bracket calculus.  The rotation identity converts it to the
adjugate form, and the plane Cayley-Hamilton law closes its survivor plane
equation at the scale `leverage * polarPlaneDet`. -/

section CrossWitness

/-- **THE CLOSED CROSS WITNESS.**  The bracket-calculus form of the adjugate
of the survivor plane form applied to the coupling vector. -/
noncomputable def polarCrossWitnessVec {m : ℕ} (design : WeightedDesign m 3)
    (pole : Fin m) (selected : Finset (Fin m)) : Fin 3 → ℝ :=
  (∑ c ∈ selected,
      tripleBracket (design.atom pole) (design.atom c)
          (polarCouplingVec design pole selected)
        • bracketNormal (design.atom pole) (design.atom c))
    - (design.atom pole ⬝ᵥ design.atom pole) • polarCouplingVec design pole selected

/-- **THE PLANE DETERMINANT.**  The determinant of the survivor plane form
`M - I` of a set, division-free in the shadow calculus: one, minus the shadow
energies, plus the halved double sum of the pair Gram minors. -/
noncomputable def polarPlaneDet {size rank : ℕ} (design : WeightedDesign size rank)
    (pole : Fin size) (selected : Finset (Fin size)) : ℝ :=
  1 - (∑ c ∈ selected, planeShadowSq design pole c)
    + (∑ c ∈ selected, ∑ d ∈ selected,
        (planeShadowSq design pole c * planeShadowSq design pole d
          - planeShadowPairing design pole c d ^ 2)) / 2

/-- The closed cross witness lives in the pole plane. -/
theorem polarCrossWitnessVec_dotProduct_pole {m : ℕ} (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (selected : Finset (Fin m)) :
    polarCrossWitnessVec design pole selected ⬝ᵥ design.atom pole = 0 := by
  rw [polarCrossWitnessVec, sub_dotProduct, sum_dotProduct, smul_dotProduct,
    polarCouplingVec_dotProduct_pole design hpole selected, smul_eq_mul, mul_zero, sub_zero]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [smul_dotProduct, bracketNormal_dotProduct_left, smul_eq_mul, mul_zero]

/-- **THE ADJUGATE FORM OF THE CLOSED WITNESS.**  The rotation identity
converts the bracket-calculus witness to the adjugate action on the coupling
vector: the shadow-energy trace scales the coupling vector, and the
read-and-rebuild sum is subtracted. -/
theorem polarCrossWitnessVec_eq_adj {m : ℕ} (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (selected : Finset (Fin m)) :
    polarCrossWitnessVec design pole selected
      = ((design.atom pole ⬝ᵥ design.atom pole)
            * ((∑ c ∈ selected, planeShadowSq design pole c) - 1))
          • polarCouplingVec design pole selected
        - (design.atom pole ⬝ᵥ design.atom pole)
          • ∑ c ∈ selected,
              (design.atom c ⬝ᵥ polarCouplingVec design pole selected)
                • planeShadowVec design pole c := by
  have hLne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  have hVpole : polarCouplingVec design pole selected ⬝ᵥ design.atom pole = 0 :=
    polarCouplingVec_dotProduct_pole design hpole selected
  have hterm : ∀ c ∈ selected,
      tripleBracket (design.atom pole) (design.atom c)
          (polarCouplingVec design pole selected)
        • bracketNormal (design.atom pole) (design.atom c)
      = ((design.atom pole ⬝ᵥ design.atom pole) * planeShadowSq design pole c)
          • polarCouplingVec design pole selected
        - ((design.atom pole ⬝ᵥ design.atom pole)
              * (design.atom c ⬝ᵥ polarCouplingVec design pole selected))
            • planeShadowVec design pole c := by
    intro c _
    rw [tripleBracket_smul_bracketNormal, hVpole]
    funext coord
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, planeShadowVec,
      planeShadowSq]
    field_simp
    ring
  rw [polarCrossWitnessVec, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    ← Finset.sum_smul, ← Finset.mul_sum]
  have hsecond : ∑ c ∈ selected,
      ((design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom c ⬝ᵥ polarCouplingVec design pole selected))
        • planeShadowVec design pole c
      = (design.atom pole ⬝ᵥ design.atom pole)
        • ∑ c ∈ selected,
            (design.atom c ⬝ᵥ polarCouplingVec design pole selected)
              • planeShadowVec design pole c := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun c _ => mul_smul _ _ _
  rw [hsecond]
  module

/-- **THE PLANE CAYLEY-HAMILTON LAW.**  The survivor plane form applied twice
to the coupling vector collapses through the shadow trace and the plane
determinant: the two-dimensional Cayley-Hamilton identity of the pole plane,
division-free, for every selected set.  The Gram Cramer decomposition
supplies the identity pair by pair, and the bracket corrections die on the
plane. -/
theorem sum_atom_dot_smul_planeShadowVec_cayleyHamilton {m : ℕ}
    (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (selected : Finset (Fin m)) :
    ∑ c ∈ selected,
        (design.atom c ⬝ᵥ ∑ d ∈ selected,
            (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
              • planeShadowVec design pole d)
          • planeShadowVec design pole c
      = (∑ c ∈ selected, planeShadowSq design pole c)
          • (∑ d ∈ selected,
              (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
                • planeShadowVec design pole d)
        - ((∑ c ∈ selected, ∑ d ∈ selected,
            (planeShadowSq design pole c * planeShadowSq design pole d
              - planeShadowPairing design pole c d ^ 2)) / 2)
          • polarCouplingVec design pole selected := by
  classical
  have hVpole : polarCouplingVec design pole selected ⬝ᵥ design.atom pole = 0 :=
    polarCouplingVec_dotProduct_pole design hpole selected
  have hpoleV : design.atom pole ⬝ᵥ polarCouplingVec design pole selected = 0 := by
    rw [dotProduct_comm]
    exact hVpole
  have hshadowV : ∀ c : Fin m,
      planeShadowVec design pole c ⬝ᵥ polarCouplingVec design pole selected
        = design.atom c ⬝ᵥ polarCouplingVec design pole selected := by
    intro c
    rw [planeShadowVec, sub_dotProduct, smul_dotProduct, smul_eq_mul, hpoleV, mul_zero,
      sub_zero]
  have hread : ∀ c : Fin m,
      design.atom c ⬝ᵥ ∑ d ∈ selected,
          (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
            • planeShadowVec design pole d
      = ∑ d ∈ selected,
          (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
            * planeShadowPairing design pole c d := by
    intro c
    rw [dotProduct_sum]
    exact Finset.sum_congr rfl fun d _ => by
      rw [dotProduct_smul, smul_eq_mul, atom_dotProduct_planeShadowVec]
  have hterm : ∀ c ∈ selected, ∀ d ∈ selected,
      (planeShadowSq design pole c * planeShadowSq design pole d
          - planeShadowPairing design pole c d ^ 2)
        • polarCouplingVec design pole selected
      = ((design.atom c ⬝ᵥ polarCouplingVec design pole selected)
              * planeShadowSq design pole d
            - (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
              * planeShadowPairing design pole c d)
          • planeShadowVec design pole c
        + ((design.atom d ⬝ᵥ polarCouplingVec design pole selected)
              * planeShadowSq design pole c
            - (design.atom c ⬝ᵥ polarCouplingVec design pole selected)
              * planeShadowPairing design pole c d)
          • planeShadowVec design pole d := by
    intro c _ d _
    have hI9 := gramDet_smul_decomp (planeShadowVec design pole c)
      (planeShadowVec design pole d) (polarCouplingVec design pole selected)
    rw [planeShadowVec_dotProduct_self design hpole c,
      planeShadowVec_dotProduct_self design hpole d,
      planeShadowVec_dotProduct_pair design hpole c d, hshadowV c, hshadowV d,
      tripleBracket_eq_zero_of_pole_orthogonal _ _ _ hpole
        (planeShadowVec_dotProduct_pole design hpole c)
        (planeShadowVec_dotProduct_pole design hpole d) hVpole,
      zero_smul, add_zero] at hI9
    exact hI9
  have hexpand : (∑ c ∈ selected, ∑ d ∈ selected,
      (planeShadowSq design pole c * planeShadowSq design pole d
        - planeShadowPairing design pole c d ^ 2))
        • polarCouplingVec design pole selected
      = ∑ c ∈ selected, ∑ d ∈ selected,
          ((design.atom c ⬝ᵥ polarCouplingVec design pole selected)
                * planeShadowSq design pole d
              - (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
                * planeShadowPairing design pole c d)
            • planeShadowVec design pole c
        + ∑ c ∈ selected, ∑ d ∈ selected,
            ((design.atom d ⬝ᵥ polarCouplingVec design pole selected)
                  * planeShadowSq design pole c
                - (design.atom c ⬝ᵥ polarCouplingVec design pole selected)
                  * planeShadowPairing design pole c d)
              • planeShadowVec design pole d := by
    calc (∑ c ∈ selected, ∑ d ∈ selected,
        (planeShadowSq design pole c * planeShadowSq design pole d
          - planeShadowPairing design pole c d ^ 2))
          • polarCouplingVec design pole selected
        = ∑ c ∈ selected, ∑ d ∈ selected,
            (planeShadowSq design pole c * planeShadowSq design pole d
              - planeShadowPairing design pole c d ^ 2)
              • polarCouplingVec design pole selected := by
          rw [Finset.sum_smul]
          exact Finset.sum_congr rfl fun c _ => Finset.sum_smul
      _ = ∑ c ∈ selected, ∑ d ∈ selected,
            (((design.atom c ⬝ᵥ polarCouplingVec design pole selected)
                  * planeShadowSq design pole d
                - (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
                  * planeShadowPairing design pole c d)
              • planeShadowVec design pole c
            + ((design.atom d ⬝ᵥ polarCouplingVec design pole selected)
                  * planeShadowSq design pole c
                - (design.atom c ⬝ᵥ polarCouplingVec design pole selected)
                  * planeShadowPairing design pole c d)
              • planeShadowVec design pole d) :=
          Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => hterm c hc d hd
      _ = _ := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => Finset.sum_add_distrib
  have hswap : ∑ c ∈ selected, ∑ d ∈ selected,
      ((design.atom d ⬝ᵥ polarCouplingVec design pole selected)
            * planeShadowSq design pole c
          - (design.atom c ⬝ᵥ polarCouplingVec design pole selected)
            * planeShadowPairing design pole c d)
        • planeShadowVec design pole d
      = ∑ c ∈ selected, ∑ d ∈ selected,
          ((design.atom c ⬝ᵥ polarCouplingVec design pole selected)
                * planeShadowSq design pole d
              - (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
                * planeShadowPairing design pole c d)
            • planeShadowVec design pole c := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
      rw [planeShadowPairing_comm design pole d c]
  have hinner : ∑ c ∈ selected, ∑ d ∈ selected,
      ((design.atom c ⬝ᵥ polarCouplingVec design pole selected)
            * planeShadowSq design pole d
          - (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
            * planeShadowPairing design pole c d)
        • planeShadowVec design pole c
      = (∑ c ∈ selected, planeShadowSq design pole c)
          • (∑ d ∈ selected,
              (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
                • planeShadowVec design pole d)
        - ∑ c ∈ selected,
            (design.atom c ⬝ᵥ ∑ d ∈ selected,
                (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
                  • planeShadowVec design pole d)
              • planeShadowVec design pole c := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hread c, ← Finset.sum_smul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    module
  have hdouble : (∑ c ∈ selected, ∑ d ∈ selected,
      (planeShadowSq design pole c * planeShadowSq design pole d
        - planeShadowPairing design pole c d ^ 2))
        • polarCouplingVec design pole selected
      = (2 : ℝ) • ((∑ c ∈ selected, planeShadowSq design pole c)
            • (∑ d ∈ selected,
                (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
                  • planeShadowVec design pole d)
          - ∑ c ∈ selected,
              (design.atom c ⬝ᵥ ∑ d ∈ selected,
                  (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
                    • planeShadowVec design pole d)
                • planeShadowVec design pole c) := by
    rw [hexpand, hswap, hinner, two_smul]
  have hhalf : ((∑ c ∈ selected, ∑ d ∈ selected,
      (planeShadowSq design pole c * planeShadowSq design pole d
        - planeShadowPairing design pole c d ^ 2)) / 2)
        • polarCouplingVec design pole selected
      = (∑ c ∈ selected, planeShadowSq design pole c)
          • (∑ d ∈ selected,
              (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
                • planeShadowVec design pole d)
        - ∑ c ∈ selected,
            (design.atom c ⬝ᵥ ∑ d ∈ selected,
                (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
                  • planeShadowVec design pole d)
              • planeShadowVec design pole c := by
    have hdiv : ((∑ c ∈ selected, ∑ d ∈ selected,
        (planeShadowSq design pole c * planeShadowSq design pole d
          - planeShadowPairing design pole c d ^ 2)) / 2)
          • polarCouplingVec design pole selected
        = (1 / 2 : ℝ) • ((∑ c ∈ selected, ∑ d ∈ selected,
            (planeShadowSq design pole c * planeShadowSq design pole d
              - planeShadowPairing design pole c d ^ 2))
              • polarCouplingVec design pole selected) := by
      rw [smul_smul]
      congr 1
      ring
    rw [hdiv, hdouble, smul_smul]
    have hone : (1 / 2 : ℝ) * 2 = 1 := by norm_num
    rw [hone, one_smul]
  rw [hhalf]
  abel

/-- **THE CLOSED WITNESS EQUATION.**  The closed cross witness solves the
survivor plane equation at the scale `leverage * polarPlaneDet`: the
Cayley-Hamilton law of the pole plane, in the exact shape the scaled Schur
engine consumes. -/
theorem polarCrossWitnessVec_witness {m : ℕ} (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (selected : Finset (Fin m)) :
    (∑ c ∈ selected,
        (design.atom c ⬝ᵥ polarCrossWitnessVec design pole selected)
          • planeShadowVec design pole c)
      - polarCrossWitnessVec design pole selected
    = ((design.atom pole ⬝ᵥ design.atom pole) * polarPlaneDet design pole selected)
        • polarCouplingVec design pole selected := by
  classical
  have hadj := polarCrossWitnessVec_eq_adj design hpole selected
  have hreadU : ∀ c : Fin m,
      design.atom c ⬝ᵥ polarCrossWitnessVec design pole selected
      = ((design.atom pole ⬝ᵥ design.atom pole)
            * ((∑ e ∈ selected, planeShadowSq design pole e) - 1))
          * (design.atom c ⬝ᵥ polarCouplingVec design pole selected)
        - (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom c ⬝ᵥ ∑ d ∈ selected,
              (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
                • planeShadowVec design pole d) := by
    intro c
    rw [hadj, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hch := sum_atom_dot_smul_planeShadowVec_cayleyHamilton design hpole selected
  have hsum : ∑ c ∈ selected,
      (design.atom c ⬝ᵥ polarCrossWitnessVec design pole selected)
        • planeShadowVec design pole c
      = ((design.atom pole ⬝ᵥ design.atom pole)
            * ((∑ e ∈ selected, planeShadowSq design pole e) - 1))
          • (∑ c ∈ selected,
              (design.atom c ⬝ᵥ polarCouplingVec design pole selected)
                • planeShadowVec design pole c)
        - (design.atom pole ⬝ᵥ design.atom pole)
          • ∑ c ∈ selected,
              (design.atom c ⬝ᵥ ∑ d ∈ selected,
                  (design.atom d ⬝ᵥ polarCouplingVec design pole selected)
                    • planeShadowVec design pole d)
                • planeShadowVec design pole c := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hreadU c]
    module
  rw [hsum, hch, hadj, polarPlaneDet]
  module

end CrossWitness

/-! ## Part 4: the scaled witness engine

The witnessed Schur engine, with the survivor plane equation solved at an
arbitrary positive scale.  The closed witness supplies the scale
`leverage * polarPlaneDet`. -/

section ScaledEngine

variable {size rank : ℕ}

/-- **THE SCALED WITNESSED SCHUR DOMINATION.**  The witnessed engine with the
plane equation solved at a positive scale `kappa`: the scalar test reads the
coupling against the witness below `kappa` times the gap.  At `kappa = 1`
this is the landed engine; the closed witness runs it at
`kappa = leverage * polarPlaneDet`. -/
theorem posDef_of_polarWitnessSchur_scaled (design : WeightedDesign size rank)
    {pole : Fin size} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {selected : Finset (Fin size)} {excess : ℝ} (hexcessPos : 0 < excess)
    (hcover : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + excess) * (probe ⬝ᵥ probe)
        ≤ ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2)
    (hz : design.atom pole ⬝ᵥ design.atom pole
        < ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
    {u : Fin rank → ℝ} {kappa : ℝ} (hkappa : 0 < kappa)
    (hupole : u ⬝ᵥ design.atom pole = 0)
    (hwitness : (∑ c ∈ selected, (design.atom c ⬝ᵥ u) • planeShadowVec design pole c) - u
        = kappa • polarCouplingVec design pole selected)
    (hVu : polarCouplingVec design pole selected ⬝ᵥ u
        < kappa * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
          - design.atom pole ⬝ᵥ design.atom pole)) :
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
  have hcoupleU : kappa * (polarCouplingVec design pole selected ⬝ᵥ u) = flatU := by
    have hstep : (kappa • polarCouplingVec design pole selected) ⬝ᵥ u
        = kappa * (polarCouplingVec design pole selected ⬝ᵥ u) := by
      rw [smul_dotProduct, smul_eq_mul]
    rw [← hstep, ← hwitness, sub_dotProduct, sum_dotProduct, hflatU]
    have hterm : ∀ c ∈ selected,
        ((design.atom c ⬝ᵥ u) • planeShadowVec design pole c) ⬝ᵥ u
          = (design.atom c ⬝ᵥ u) ^ 2 := by
      intro c _
      rw [smul_dotProduct, smul_eq_mul, planeShadowVec_dotProduct_polar design pole c hupole]
      ring
    rw [Finset.sum_congr rfl hterm]
  have hcoupleQ : kappa * (polarCouplingVec design pole selected ⬝ᵥ probe) = flatUQ := by
    have hstep : (kappa • polarCouplingVec design pole selected) ⬝ᵥ probe
        = kappa * (polarCouplingVec design pole selected ⬝ᵥ probe) := by
      rw [smul_dotProduct, smul_eq_mul]
    rw [← hstep, ← hwitness, sub_dotProduct, sum_dotProduct, hflatUQ]
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
  have hVuFlat : flatU < kappa ^ 2 * (pairMass - leverage) := by
    rw [← hcoupleU]
    calc kappa * (polarCouplingVec design pole selected ⬝ᵥ u)
        < kappa * (kappa * (pairMass - leverage)) := mul_lt_mul_of_pos_left hVu hkappa
      _ = kappa ^ 2 * (pairMass - leverage) := by ring
  have hfinal : (polarCouplingVec design pole selected ⬝ᵥ probe) ^ 2
      < (pairMass - leverage) * flatQ := by
    have hsq : kappa ^ 2 * (polarCouplingVec design pole selected ⬝ᵥ probe) ^ 2
        = flatUQ ^ 2 := by
      rw [← hcoupleQ]
      ring
    have hchain : kappa ^ 2 * (polarCouplingVec design pole selected ⬝ᵥ probe) ^ 2
        < kappa ^ 2 * ((pairMass - leverage) * flatQ) := by
      calc kappa ^ 2 * (polarCouplingVec design pole selected ⬝ᵥ probe) ^ 2
          = flatUQ ^ 2 := hsq
        _ ≤ flatU * flatQ := hcs
        _ < (kappa ^ 2 * (pairMass - leverage)) * flatQ :=
            mul_lt_mul_of_pos_right hVuFlat hqqPos
        _ = kappa ^ 2 * ((pairMass - leverage) * flatQ) := by ring
    exact lt_of_mul_lt_mul_left hchain (by positivity)
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

end ScaledEngine

/-! ## Part 5: the closed kill and the polynomial tie law -/

section ClosedKill

/-- **THE CLOSED WITNESSED SCHUR KILL AT THE DECIDING CELL.**  Every
hypothesis is a polynomial inequality of the pairing data: the pair
certificate, the priced excess, the pole surplus of the complement, the
positive plane determinant, and one scalar test of the coupling vector
against the closed cross witness.  No witness quantifier is left. -/
theorem not_isTie_of_crossWitnessSchur_six_three (design : WeightedDesign 6 3)
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
    (hplaneDetPos : 0 < polarPlaneDet design pole
        (((Finset.univ.erase pole).erase first).erase second))
    (htest : polarCouplingVec design pole (((Finset.univ.erase pole).erase first).erase second)
          ⬝ᵥ polarCrossWitnessVec design pole
            (((Finset.univ.erase pole).erase first).erase second)
        < (design.atom pole ⬝ᵥ design.atom pole)
            * polarPlaneDet design pole (((Finset.univ.erase pole).erase first).erase second)
          * ((∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
                (design.atom c ⬝ᵥ design.atom pole) ^ 2)
            - design.atom pole ⬝ᵥ design.atom pole)) :
    ¬ IsTie design := by
  classical
  intro htie
  have hcover := complementPair_polarCover design hpole hne hfirstPole hsecondPole hwcapPos
    hwcap hSfirst hSsecond hdet hexcess
  have hkappa : 0 < (design.atom pole ⬝ᵥ design.atom pole)
      * polarPlaneDet design pole (((Finset.univ.erase pole).erase first).erase second) :=
    mul_pos hpole hplaneDetPos
  have hposDef := posDef_of_polarWitnessSchur_scaled design hpole hexcessPos hcover hz
    hkappa
    (polarCrossWitnessVec_dotProduct_pole design hpole
      (((Finset.univ.erase pole).erase first).erase second))
    (polarCrossWitnessVec_witness design hpole
      (((Finset.univ.erase pole).erase first).erase second))
    htest
  have hmemFirst : first ∈ Finset.univ.erase pole :=
    Finset.mem_erase.mpr ⟨hfirstPole, Finset.mem_univ first⟩
  have hmemSecond : second ∈ (Finset.univ.erase pole).erase first :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_erase.mpr ⟨hsecondPole, Finset.mem_univ second⟩⟩
  have hcard : (((Finset.univ.erase pole).erase first).erase second).card = 3 := by
    rw [Finset.card_erase_of_mem hmemSecond, Finset.card_erase_of_mem hmemFirst,
      Finset.card_erase_of_mem (Finset.mem_univ pole), Finset.card_univ, Fintype.card_fin]
  exact htie.2 _ hcard hposDef

/-- **THE POLYNOMIAL TIE LAW OF THE DECIDING CELL.**  At every `(6,3)` tie,
every pole, every pair with the sharp certificate, every priced excess, and
every positive plane determinant of the complement: the complement triple
keeps its pole mass at or below the leverage, or the coupling vector spends
the whole closed Schur budget against the closed cross witness.  The banked
`Gtz.tie_witnessSchur_six_three` quantifies over witnesses of the plane
equation; this law is witness-free, and every quantity in it is a polynomial
of the pairing data.  The probes show the complex ties of the deciding cell
saturate it with equality at the three pole choices of their unique argmax
triple. -/
theorem tie_crossWitnessSchur_six_three (design : WeightedDesign 6 3) (htie : IsTie design)
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
    (hplaneDetPos : 0 < polarPlaneDet design pole
        (((Finset.univ.erase pole).erase first).erase second)) :
    (∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
        (design.atom c ⬝ᵥ design.atom pole) ^ 2)
      ≤ design.atom pole ⬝ᵥ design.atom pole
    ∨ (design.atom pole ⬝ᵥ design.atom pole)
          * polarPlaneDet design pole (((Finset.univ.erase pole).erase first).erase second)
        * ((∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
              (design.atom c ⬝ᵥ design.atom pole) ^ 2)
          - design.atom pole ⬝ᵥ design.atom pole)
      ≤ polarCouplingVec design pole (((Finset.univ.erase pole).erase first).erase second)
          ⬝ᵥ polarCrossWitnessVec design pole
            (((Finset.univ.erase pole).erase first).erase second) := by
  by_contra hcontra
  rw [not_or, not_le, not_le] at hcontra
  exact not_isTie_of_crossWitnessSchur_six_three design hpole hne hfirstPole hsecondPole
    hwcapPos hwcap hSfirst hSsecond hdet hexcess hexcessPos hcontra.1 hplaneDetPos
    hcontra.2 htie

end ClosedKill

end Gtz
