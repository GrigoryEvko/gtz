/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.PolarPlaneTurn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The circular order of the pole plane

Every polar residual of the campaign carries an `IsTie` hypothesis, and the
complex tie family satisfies every field-agnostic bundle the lane ever handed a
prover.  Thus no field-agnostic argument closes the deciding cell, and the kill
must contain a step that the complex field breaks.  This file lands that step.

## 1. The signed shadow

At a pole of positive leverage the signed shadow of a label is the pole reading
times the plane component, `v_c = t_c b_c`.  Its three contractions are
`Gtz.polarSignedSq` (the energy), `Gtz.polarSignedPair` (the overlap) and
`Gtz.polarSignedWedge` (the area).  The wedge is the pole reading pair times the
anchored bracket, thus it is division free and it carries a SIGN.

## 2. The four structural laws

`Gtz.sum_weight_polarSignedWedge` and `Gtz.sum_weight_polarSignedPair` are the
cross moment read against a wedge and against a pairing: each row of the signed
calculus is a positively weighted sum that vanishes, thus each row carries both
signs.  `Gtz.polarSignedWedge_pluecker` is the three-term Grassmann relation and
`Gtz.polarSignedSq_mul_polarSignedWedge` is the rotation law, the plane form of
the landed shadow transport.  The first pair supplies the sign changes, the
second pair supplies the ordering.

## 3. The circular order

`Gtz.exists_polarWrapping_or_degenerate` is the theorem.  At every pole of
positive leverage, either every signed shadow vanishes, or two of them are
antiparallel, or THREE of them wrap the origin.  The proof reads the row of an
anchor of positive energy, selects inside that row the label of extreme ratio
`Gtz.polarSignedPair / Gtz.polarSignedWedge`, and closes with the anchor
identity at the selected label.  The rotation law turns the extreme ratio into a
sign, thus no coordinates of the plane and no square root appear.

Over the complex field the same moment equations hold with the signed shadows in
a FOUR dimensional real space, and three points of such a space span a triangle
that misses the origin.  The probes measure the separation exactly: at 22494
real poles the origin sits in the hull of some triple at distance at most
`5.5e-16`, and at 3432 complex poles the nearest triple misses by at least
`3.4e-3`, with a median miss of `0.18` and with 3418 of them missing by more
than `0.01`.  The circular order has no complex analogue, and it is the first
real-only bundle of the polar chain.

## 4. The wrapping cofactor

`Gtz.PolarWrapping` states the wrapping in the SHADOW PAIRING data alone.  The
bridge is `Gtz.polarWrapCofactor_mul_leverage`: the leverage times the cofactor
of a pair against an apex is the product of two signed wedges.  Thus the
circular order needs no bracket in its statement, it is rank generic, and it
speaks the same vocabulary as `Gtz.polarShadowAdjugate`.  A wrapping triple has
three distinct labels, none of them the pole, and a strictly positive plane Gram
determinant, thus it also opens the second bound of the direct cover.

## 5. The null branch dies, and Caratheodory closes the pole plane

If every signed shadow of a pole vanishes then, in a primitive design, every
other atom reads zero at that pole.  The tilt of every covering is then exactly
zero, the landed polar cover insertion fires with no budget spent, and the
design is no tie.  Thus `Gtz.polarCircularDichotomy_of_isTie`: at a primitive
tie every overshooting pole carries an antiparallel pair or a wrapping triple.
`Gtz.exists_pos_dependency_of_isTie` closes both branches into one statement.
The origin is a positive combination of at most three signed shadows, which is
the Caratheodory theorem of the pole plane.

## 6. The residual, narrowed a seventh time

`Gtz.PolarCircularShadowBound` hands the prover the DICHOTOMY together with the
arithmetic plane bound at the selected wrapping triple, and it is free at every
primitive tie.  `Gtz.PolarTiltSelectionCircular` is the seven-bundle residual,
and every consumer of the shipped residual runs on it.  The bundle is the first
of the polar chain whose content the complex field cannot supply.

The probes calibrate the narrowing.  On 3749 real near-tie endpoints the kill
fires at a WRAPPING combination at 3749 of them, and the wrapping combinations
carry the kill at 74.7 percent against 28.3 percent elsewhere.  Adversarially,
minimising the worse of the tie gap and the kill margin RESTRICTED to wrapping
triples reaches `0.5306 / 0.1556 / 0.6090 / 0.1364` on four slices against
`0.5666 / 0.1622 / 0.5639 / 0.1367` unrestricted, with no endpoint below `0.02`
in either mode, and no pole of the 73830 adversarial poles lacks a wrapping
triple.  The restriction is free.

## 7. The kill route, named and calibrated

`Gtz.PolarShadowSchurSelection` asks for a pole and a triple that clear the four
polynomial bounds of the landed kill, and `Gtz.PolarWrapSelection` pins that
triple to a wrapping triple of the circular order.  The second implies the
first, both close the deciding cell and all of rank three on their own, and both
are FALSE at size five, thus the calibration of the whole polar chain transports
to this route unchanged.
-/

namespace Gtz

open Matrix Finset

/-! ## Part 1: the signed shadow calculus

The pole reading weights the plane component.  The three contractions of the
weighted plane components are the energy, the overlap and the area, and all
three are division free polynomials in the landed shadow data. -/

section SignedShadow

variable {size rank : ℕ}

/-- **THE SIGNED SHADOW PAIRING.**  The overlap of two plane components, each
weighted by its own pole reading. -/
noncomputable def polarSignedPair (design : WeightedDesign size rank)
    (pole first second : Fin size) : ℝ :=
  (design.atom first ⬝ᵥ design.atom pole) * (design.atom second ⬝ᵥ design.atom pole)
    * planeShadowPairing design pole first second

/-- **THE SIGNED SHADOW ENERGY.**  The squared length of the weighted plane
component. -/
noncomputable def polarSignedSq (design : WeightedDesign size rank)
    (pole label : Fin size) : ℝ :=
  (design.atom label ⬝ᵥ design.atom pole) ^ 2 * planeShadowSq design pole label

/-- The signed pairing is symmetric. -/
theorem polarSignedPair_comm (design : WeightedDesign size rank)
    (pole first second : Fin size) :
    polarSignedPair design pole first second = polarSignedPair design pole second first := by
  rw [polarSignedPair, polarSignedPair, planeShadowPairing_comm design pole first second]
  ring

/-- The diagonal of the signed pairing is the signed energy. -/
theorem polarSignedPair_self (design : WeightedDesign size rank) (pole label : Fin size) :
    polarSignedPair design pole label label = polarSignedSq design pole label := by
  rw [polarSignedPair, polarSignedSq, planeShadowPairing_self]
  ring

/-- The signed energy is never negative. -/
theorem polarSignedSq_nonneg (design : WeightedDesign size rank) {pole : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (label : Fin size) :
    0 ≤ polarSignedSq design pole label :=
  mul_nonneg (sq_nonneg _) (planeShadowSq_nonneg design pole label hpole)

/-- The pole has no signed shadow. -/
theorem polarSignedSq_pole (design : WeightedDesign size rank) {pole : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) :
    polarSignedSq design pole pole = 0 := by
  have hne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  rw [polarSignedSq, planeShadowSq]
  field_simp
  ring

/-- The pole pairs to zero with every label. -/
theorem polarSignedPair_pole (design : WeightedDesign size rank) {pole : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (label : Fin size) :
    polarSignedPair design pole pole label = 0 := by
  have hne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  have hcomm : design.atom pole ⬝ᵥ design.atom label
      = design.atom label ⬝ᵥ design.atom pole := dotProduct_comm _ _
  rw [polarSignedPair, planeShadowPairing, hcomm]
  field_simp
  ring

/-- **PRIMITIVITY MAKES EVERY OTHER SHADOW POSITIVE.**  A vanishing plane
shadow says that the atom is a multiple of the pole, and a primitive design has
no such pair. -/
theorem planeShadowSq_pos_of_primitive (design : WeightedDesign size rank)
    (hprimitive : IsPrimitiveDesign design) {pole label : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (hne : label ≠ pole) :
    0 < planeShadowSq design pole label := by
  refine lt_of_le_of_ne (planeShadowSq_nonneg design pole label hpole) ?_
  intro hzero
  have hself : planeShadowVec design pole label ⬝ᵥ planeShadowVec design pole label = 0 := by
    rw [planeShadowVec_dotProduct_self design hpole label, ← hzero]
  have hzeroVec : planeShadowVec design pole label = 0 :=
    eq_zero_of_dotProduct_self_eq_zero hself
  rw [planeShadowVec, sub_eq_zero] at hzeroVec
  exact hprimitive pole label _ (Ne.symm hne) hzeroVec

/-- **THE SIGNED ENERGY OF A PRIMITIVE DESIGN VANISHES ONLY AT AN ORTHOGONAL
ATOM.**  Thus the null branch of the circular order says that every other atom
reads zero at the pole. -/
theorem polarSignedSq_eq_zero_iff_of_primitive (design : WeightedDesign size rank)
    (hprimitive : IsPrimitiveDesign design) {pole label : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (hne : label ≠ pole) :
    polarSignedSq design pole label = 0 ↔ design.atom label ⬝ᵥ design.atom pole = 0 := by
  constructor
  · intro hzero
    rw [polarSignedSq] at hzero
    rcases mul_eq_zero.mp hzero with hread | hshadow
    · exact sq_eq_zero_iff.mp hread
    · exact absurd hshadow
        (ne_of_gt (planeShadowSq_pos_of_primitive design hprimitive hpole hne))
  · intro hread
    rw [polarSignedSq, hread]
    ring

end SignedShadow

section SignedWedge

variable {m : ℕ}

/-- **THE SIGNED SHADOW WEDGE.**  The area spanned by two weighted plane
components, as the pole reading pair times the anchored bracket.  This is the
one quantity of the polar calculus that carries a sign the complex field cannot
reproduce: the determinant that defines it is bilinear, the metric that reads it
is not. -/
noncomputable def polarSignedWedge (design : WeightedDesign m 3)
    (pole first second : Fin m) : ℝ :=
  (design.atom first ⬝ᵥ design.atom pole) * (design.atom second ⬝ᵥ design.atom pole)
    * tripleBracket (design.atom pole) (design.atom first) (design.atom second)

/-- The signed wedge is antisymmetric. -/
theorem polarSignedWedge_antisymm (design : WeightedDesign m 3) (pole first second : Fin m) :
    polarSignedWedge design pole second first = -polarSignedWedge design pole first second := by
  rw [polarSignedWedge, polarSignedWedge,
    tripleBracket_swapRight (design.atom pole) (design.atom first) (design.atom second)]
  ring

/-- The signed wedge of a label with itself vanishes. -/
theorem polarSignedWedge_self (design : WeightedDesign m 3) (pole label : Fin m) :
    polarSignedWedge design pole label label = 0 := by
  have hzero : tripleBracket (design.atom pole) (design.atom label) (design.atom label) = 0 := by
    have h := tripleBracket_swapRight (design.atom pole) (design.atom label) (design.atom label)
    linarith
  rw [polarSignedWedge, hzero, mul_zero]

/-- The pole wedges to zero with every label. -/
theorem polarSignedWedge_pole (design : WeightedDesign m 3) (pole label : Fin m) :
    polarSignedWedge design pole pole label = 0 := by
  have hzero : tripleBracket (design.atom pole) (design.atom pole) (design.atom label) = 0 := by
    have h := tripleBracket_swapLeft (design.atom pole) (design.atom pole) (design.atom label)
    linarith
  rw [polarSignedWedge, hzero, mul_zero]

/-- **THE PLANE LAGRANGE LAW OF THE SIGNED CALCULUS.**  The squared signed wedge
is the leverage times the signed Gram determinant of the pair.  Every degeneracy
statement of this file passes through it. -/
theorem polarSignedWedge_sq_eq_signedGram (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (first second : Fin m) :
    polarSignedWedge design pole first second ^ 2
      = (design.atom pole ⬝ᵥ design.atom pole)
        * (polarSignedSq design pole first * polarSignedSq design pole second
          - polarSignedPair design pole first second ^ 2) := by
  have hbase := tripleBracket_sq_eq_planeShadow design hpole first second
  simp only [polarSignedWedge, polarSignedSq, polarSignedPair]
  linear_combination ((design.atom first ⬝ᵥ design.atom pole) ^ 2
    * (design.atom second ⬝ᵥ design.atom pole) ^ 2) * hbase

/-- The signed pairing obeys Cauchy-Schwarz against the signed energies. -/
theorem polarSignedPair_sq_le (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (first second : Fin m) :
    polarSignedPair design pole first second ^ 2
      ≤ polarSignedSq design pole first * polarSignedSq design pole second := by
  have hsq := polarSignedWedge_sq_eq_signedGram design hpole first second
  nlinarith [sq_nonneg (polarSignedWedge design pole first second), hpole]

/-- A label of zero signed energy wedges to zero with every label. -/
theorem polarSignedWedge_eq_zero_of_signedSq_eq_zero (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first : Fin m}
    (hzero : polarSignedSq design pole first = 0) (second : Fin m) :
    polarSignedWedge design pole first second = 0 := by
  have hsq := polarSignedWedge_sq_eq_signedGram design hpole first second
  rw [hzero, zero_mul, zero_sub] at hsq
  have hle : polarSignedWedge design pole first second ^ 2 ≤ 0 := by
    rw [hsq]
    nlinarith [sq_nonneg (polarSignedPair design pole first second), hpole]
  exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))

/-- A label of zero signed energy pairs to zero with every label. -/
theorem polarSignedPair_eq_zero_of_signedSq_eq_zero (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first : Fin m}
    (hzero : polarSignedSq design pole first = 0) (second : Fin m) :
    polarSignedPair design pole first second = 0 := by
  have hcs := polarSignedPair_sq_le design hpole first second
  rw [hzero, zero_mul] at hcs
  exact sq_eq_zero_iff.mp (le_antisymm hcs (sq_nonneg _))

end SignedWedge

/-! ## Part 2: the four structural laws

Two of them are the cross moment, read once against a wedge and once against a
pairing.  Each is a positively weighted row that vanishes, thus each row of the
signed calculus carries both signs.  The other two are the Grassmann relation
and the rotation law, and together they turn a ratio extremum into a sign. -/

section StructuralLaws

variable {m : ℕ}

/-- **THE WEDGE ANCHOR IDENTITY.**  The weighted signed wedges of a fixed label
against all labels add to zero.  This is the division-free linear supply of the
circular order: over the reals a positively weighted vanishing row cannot be one
signed. -/
theorem sum_weight_polarSignedWedge (design : WeightedDesign m 3) (pole label : Fin m) :
    ∑ c, design.weight c * polarSignedWedge design pole c label = 0 := by
  have hbase := sum_weight_pairing_mul_tripleBracket design pole label
  have hstep : ∀ c : Fin m, design.weight c * polarSignedWedge design pole c label
      = (design.atom label ⬝ᵥ design.atom pole)
        * (design.weight c * (design.atom c ⬝ᵥ design.atom pole)
          * tripleBracket (design.atom pole) (design.atom c) (design.atom label)) := by
    intro c
    rw [polarSignedWedge]
    ring
  rw [Finset.sum_congr rfl fun c _ => hstep c, ← Finset.mul_sum, hbase, mul_zero]

/-- The wedge anchor identity, read along the row.  The signed wedge is
antisymmetric, thus the row and the column of a label carry the same law. -/
theorem sum_weight_polarSignedWedge_row (design : WeightedDesign m 3) (pole label : Fin m) :
    ∑ c, design.weight c * polarSignedWedge design pole label c = 0 := by
  have hcolumn := sum_weight_polarSignedWedge design pole label
  have hcancel : (∑ c, design.weight c * polarSignedWedge design pole label c)
      + (∑ c, design.weight c * polarSignedWedge design pole c label) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [polarSignedWedge_antisymm design pole label c]
    ring
  rw [hcolumn, add_zero] at hcancel
  exact hcancel

/-- **THE PAIRING ANCHOR IDENTITY.**  The same cross moment read against a
shadow: the weighted signed pairings of a fixed label against all labels add to
zero. -/
theorem sum_weight_polarSignedPair (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (label : Fin m) :
    ∑ c, design.weight c * polarSignedPair design pole c label = 0 := by
  have hbase := sum_weight_pairing_mul_planeShadowPairing design hpole label
  have hstep : ∀ c : Fin m, design.weight c * polarSignedPair design pole c label
      = (design.atom label ⬝ᵥ design.atom pole)
        * (design.weight c * (design.atom c ⬝ᵥ design.atom pole)
          * planeShadowPairing design pole c label) := by
    intro c
    rw [polarSignedPair]
    ring
  rw [Finset.sum_congr rfl fun c _ => hstep c, ← Finset.mul_sum, hbase, mul_zero]

/-- **THE GRASSMANN RELATION OF THE SIGNED WEDGE.**  The alternating three-term
law, carried through the pole readings. -/
theorem polarSignedWedge_pluecker (design : WeightedDesign m 3)
    (pole first second third fourth : Fin m) :
    polarSignedWedge design pole first second * polarSignedWedge design pole third fourth
        - polarSignedWedge design pole first third * polarSignedWedge design pole second fourth
      + polarSignedWedge design pole first fourth
          * polarSignedWedge design pole second third = 0 := by
  have hbase := tripleBracket_grassmannPluecker (design.atom pole) (design.atom first)
    (design.atom second) (design.atom third) (design.atom fourth)
  simp only [polarSignedWedge]
  linear_combination ((design.atom first ⬝ᵥ design.atom pole)
    * (design.atom second ⬝ᵥ design.atom pole) * (design.atom third ⬝ᵥ design.atom pole)
    * (design.atom fourth ⬝ᵥ design.atom pole)) * hbase

/-- **THE ROTATION LAW.**  The signed energy of an anchor times the signed wedge
of a pair is the alternating combination of the anchor rows.  This is the plane
form of the landed shadow transport, and it is the law that converts an extreme
ratio inside a row into a sign. -/
theorem polarSignedSq_mul_polarSignedWedge (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (anchor first second : Fin m) :
    polarSignedSq design pole anchor * polarSignedWedge design pole first second
      = polarSignedPair design pole anchor first * polarSignedWedge design pole anchor second
        - polarSignedPair design pole anchor second
          * polarSignedWedge design pole anchor first := by
  have hswap : tripleBracket (design.atom pole) (design.atom first) (design.atom anchor)
      = -tripleBracket (design.atom pole) (design.atom anchor) (design.atom first) :=
    tripleBracket_swapRight _ _ _
  have hcomm : planeShadowPairing design pole first anchor
      = planeShadowPairing design pole anchor first :=
    planeShadowPairing_comm design pole first anchor
  have htr := tripleBracket_shadow_transport design hpole first anchor second
  rw [hswap, hcomm] at htr
  simp only [polarSignedSq, polarSignedPair, polarSignedWedge]
  linear_combination ((design.atom anchor ⬝ᵥ design.atom pole) ^ 2
    * (design.atom first ⬝ᵥ design.atom pole)
    * (design.atom second ⬝ᵥ design.atom pole)) * htr

end StructuralLaws

/-! ## Part 3: the half-plane law

The cross moment read at an arbitrary probe is a positively weighted row that
vanishes.  Thus a row of signed readings that is one signed is the zero row, and
no closed half plane holds all the signed shadows unless they all lie on its
boundary line. -/

section HalfPlane

variable {m : ℕ}

/-- The cross moment read at an arbitrary probe. -/
theorem sum_weight_reading_mul_shadow_read (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (probe : Fin 3 → ℝ) :
    ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom pole)
        * (planeShadowVec design pole c ⬝ᵥ probe) = 0 := by
  have hvec := sum_weight_pairing_smul_planeShadowVec design hpole
  have hread : (∑ c, (design.weight c * (design.atom c ⬝ᵥ design.atom pole))
      • planeShadowVec design pole c) ⬝ᵥ probe
      = ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom pole)
          * (planeShadowVec design pole c ⬝ᵥ probe) := by
    rw [sum_dotProduct]
    exact Finset.sum_congr rfl fun c _ => by rw [smul_dotProduct, smul_eq_mul]
  rw [← hread, hvec, zero_dotProduct]

/-- **THE HALF-PLANE LAW.**  A one-signed row of signed readings is the zero
row.  Thus the signed shadows sit in no closed half plane except through
collapse onto its boundary, and that is the geometric content the complex field
loses. -/
theorem polarShadowRow_eq_zero_of_nonneg (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {probe : Fin 3 → ℝ}
    (hsign : ∀ c : Fin m, 0 ≤ (design.atom c ⬝ᵥ design.atom pole)
      * (planeShadowVec design pole c ⬝ᵥ probe)) (label : Fin m) :
    (design.atom label ⬝ᵥ design.atom pole)
      * (planeShadowVec design pole label ⬝ᵥ probe) = 0 := by
  by_contra hne
  have hpos : 0 < (design.atom label ⬝ᵥ design.atom pole)
      * (planeShadowVec design pole label ⬝ᵥ probe) := lt_of_le_of_ne (hsign label) (Ne.symm hne)
  have hsum : 0 < ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom pole)
      * (planeShadowVec design pole c ⬝ᵥ probe) := by
    refine Finset.sum_pos' (fun c _ => ?_) ⟨label, Finset.mem_univ label, ?_⟩
    · have := mul_nonneg (design.weight_pos c).le (hsign c)
      calc (0 : ℝ) ≤ design.weight c * ((design.atom c ⬝ᵥ design.atom pole)
            * (planeShadowVec design pole c ⬝ᵥ probe)) := this
        _ = design.weight c * (design.atom c ⬝ᵥ design.atom pole)
            * (planeShadowVec design pole c ⬝ᵥ probe) := by ring
    · have := mul_pos (design.weight_pos label) hpos
      calc (0 : ℝ) < design.weight label * ((design.atom label ⬝ᵥ design.atom pole)
            * (planeShadowVec design pole label ⬝ᵥ probe)) := this
        _ = design.weight label * (design.atom label ⬝ᵥ design.atom pole)
            * (planeShadowVec design pole label ⬝ᵥ probe) := by ring
  rw [sum_weight_reading_mul_shadow_read design hpole probe] at hsum
  exact lt_irrefl 0 hsum

end HalfPlane

/-! ## Part 3b: the signed shadow as a vector

The signed shadow is a vector of the pole plane, and the three contractions of
Part 1 are its pole readings.  Written this way the cross moment says that the
signed shadows add to the zero vector, and the Cramer dependency says that any
three of them carry a linear relation whose coefficients are their own signed
wedges.  Together they are the Caratheodory statement of the pole plane. -/

section SignedVector

variable {m : ℕ}

/-- **THE SIGNED SHADOW VECTOR.**  The plane component of an atom, scaled by its
own pole reading. -/
noncomputable def polarSignedVec (design : WeightedDesign m 3) (pole label : Fin m) :
    Fin 3 → ℝ :=
  (design.atom label ⬝ᵥ design.atom pole) • planeShadowVec design pole label

/-- The signed shadow lives in the pole plane. -/
theorem polarSignedVec_dotProduct_pole (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (label : Fin m) :
    polarSignedVec design pole label ⬝ᵥ design.atom pole = 0 := by
  rw [polarSignedVec, smul_dotProduct, planeShadowVec_dotProduct_pole design hpole label,
    smul_eq_mul, mul_zero]

/-- Two signed shadows pair as the signed pairing. -/
theorem polarSignedVec_dotProduct_pair (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (first second : Fin m) :
    polarSignedVec design pole first ⬝ᵥ polarSignedVec design pole second
      = polarSignedPair design pole first second := by
  rw [polarSignedVec, polarSignedVec, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, planeShadowVec_dotProduct_pair design hpole first second, polarSignedPair]
  ring

/-- The squared length of a signed shadow is the signed energy. -/
theorem polarSignedVec_dotProduct_self (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (label : Fin m) :
    polarSignedVec design pole label ⬝ᵥ polarSignedVec design pole label
      = polarSignedSq design pole label := by
  rw [polarSignedVec_dotProduct_pair design hpole label label, polarSignedPair_self]

/-- **THE CROSS MOMENT IN SIGNED FORM.**  The weighted signed shadows add to the
zero vector.  This is the whole hypothesis the circular order consumes. -/
theorem sum_weight_polarSignedVec (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) :
    ∑ c, design.weight c • polarSignedVec design pole c = 0 := by
  have hvec := sum_weight_pairing_smul_planeShadowVec design hpole
  rw [← hvec]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [polarSignedVec, smul_smul]

/-- The anchored bracket does not see the pole component of its slots. -/
theorem tripleBracket_planeShadowVec (design : WeightedDesign m 3) (pole first second : Fin m) :
    tripleBracket (design.atom pole) (planeShadowVec design pole first)
        (planeShadowVec design pole second)
      = tripleBracket (design.atom pole) (design.atom first) (design.atom second) := by
  rw [planeShadowVec, planeShadowVec]
  simp only [tripleBracket_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **THE CRAMER DEPENDENCY OF THREE SIGNED SHADOWS.**  Any three signed shadows
carry a linear relation whose coefficients are their own cyclic signed wedges.
This is the plane Cramer solve, and with the circular order it becomes the
Caratheodory statement: the origin is a strictly positive combination of three
signed shadows. -/
theorem polarSignedVec_cramer (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (first second third : Fin m) :
    polarSignedWedge design pole second third • polarSignedVec design pole first
        + polarSignedWedge design pole third first • polarSignedVec design pole second
      + polarSignedWedge design pole first second • polarSignedVec design pole third = 0 := by
  have hzero : tripleBracket (planeShadowVec design pole first)
      (planeShadowVec design pole second) (planeShadowVec design pole third) = 0 :=
    tripleBracket_eq_zero_of_pole_orthogonal _ _ _ hpole
      (planeShadowVec_dotProduct_pole design hpole first)
      (planeShadowVec_dotProduct_pole design hpole second)
      (planeShadowVec_dotProduct_pole design hpole third)
  have hcramer := tripleBracket_pole_cramer (design.atom pole)
    (planeShadowVec design pole first) (planeShadowVec design pole second)
    (planeShadowVec design pole third)
  rw [hzero, zero_smul] at hcramer
  simp only [tripleBracket_planeShadowVec] at hcramer
  have hswap : tripleBracket (design.atom pole) (design.atom third) (design.atom first)
      = -tripleBracket (design.atom pole) (design.atom first) (design.atom third) :=
    tripleBracket_swapRight _ _ _
  have hscale : polarSignedWedge design pole second third • polarSignedVec design pole first
        + polarSignedWedge design pole third first • polarSignedVec design pole second
        + polarSignedWedge design pole first second • polarSignedVec design pole third
      = ((design.atom first ⬝ᵥ design.atom pole) * (design.atom second ⬝ᵥ design.atom pole)
          * (design.atom third ⬝ᵥ design.atom pole))
        • (tripleBracket (design.atom pole) (design.atom second) (design.atom third)
              • planeShadowVec design pole first
            - tripleBracket (design.atom pole) (design.atom first) (design.atom third)
              • planeShadowVec design pole second
            + tripleBracket (design.atom pole) (design.atom first) (design.atom second)
              • planeShadowVec design pole third) := by
    simp only [polarSignedWedge, polarSignedVec, hswap]
    module
  rw [hscale, hcramer, smul_zero]

/-- **THE HALF-PLANE LAW IN SIGNED FORM.**  No closed half plane holds the
signed shadows except through collapse onto its boundary line. -/
theorem polarSignedVec_read_eq_zero_of_nonneg (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {probe : Fin 3 → ℝ}
    (hsign : ∀ c : Fin m, 0 ≤ polarSignedVec design pole c ⬝ᵥ probe) (label : Fin m) :
    polarSignedVec design pole label ⬝ᵥ probe = 0 := by
  have hrewrite : ∀ c : Fin m, polarSignedVec design pole c ⬝ᵥ probe
      = (design.atom c ⬝ᵥ design.atom pole) * (planeShadowVec design pole c ⬝ᵥ probe) := by
    intro c
    rw [polarSignedVec, smul_dotProduct, smul_eq_mul]
  rw [hrewrite label]
  refine polarShadowRow_eq_zero_of_nonneg design hpole (fun c => ?_) label
  rw [← hrewrite c]
  exact hsign c

end SignedVector

/-! ## Part 4: the wrapping cofactor

The wrapping of a triple is a statement about the three cyclic signed wedges.
The cofactor rewrites it in the SHADOW PAIRING data alone, thus the circular
order needs no bracket in its statement and it is rank generic. -/

section WrapCofactor

variable {size rank : ℕ}

/-- **THE WRAPPING COFACTOR.**  The cofactor of a pair against an apex in the
signed Gram matrix of a triple.  Its positivity says that the origin is
separated from the apex by the pair, and the three cofactors of a triple are
positive exactly when the triple wraps. -/
noncomputable def polarWrapCofactor (design : WeightedDesign size rank) (pole : Fin size)
    (first second apex : Fin size) : ℝ :=
  polarSignedPair design pole first apex * polarSignedPair design pole second apex
    - polarSignedPair design pole first second * polarSignedSq design pole apex

/-- **THE WRAPPING TRIPLE.**  A triple whose three wrapping cofactors are
positive.  Over the reals this says that the origin is a strictly positive
combination of the three signed shadows. -/
def PolarWrapping (design : WeightedDesign size rank) (pole first second third : Fin size) :
    Prop :=
  0 < polarWrapCofactor design pole first second third
    ∧ 0 < polarWrapCofactor design pole second third first
    ∧ 0 < polarWrapCofactor design pole third first second

end WrapCofactor

section WrapBridge

variable {m : ℕ}

/-- **THE COFACTOR BRIDGE.**  The leverage times a wrapping cofactor is the
product of two signed wedges.  This is the landed shared-slot bracket product,
carried through the pole readings. -/
theorem polarWrapCofactor_mul_leverage (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (first second apex : Fin m) :
    (design.atom pole ⬝ᵥ design.atom pole) * polarWrapCofactor design pole first second apex
      = polarSignedWedge design pole apex first * polarSignedWedge design pole second apex := by
  have hbase := tripleBracket_mul_eq_planeShadow design hpole first apex second
  have hswapLeft : tripleBracket (design.atom pole) (design.atom first) (design.atom apex)
      = -tripleBracket (design.atom pole) (design.atom apex) (design.atom first) :=
    tripleBracket_swapRight _ _ _
  have hswapRight : tripleBracket (design.atom pole) (design.atom apex) (design.atom second)
      = -tripleBracket (design.atom pole) (design.atom second) (design.atom apex) :=
    tripleBracket_swapRight _ _ _
  have hcommApex : planeShadowPairing design pole apex second
      = planeShadowPairing design pole second apex :=
    planeShadowPairing_comm design pole apex second
  rw [hswapLeft, hswapRight, hcommApex] at hbase
  simp only [polarWrapCofactor, polarSignedPair, polarSignedSq, polarSignedWedge]
  linear_combination (-((design.atom first ⬝ᵥ design.atom pole)
    * (design.atom second ⬝ᵥ design.atom pole)
    * (design.atom apex ⬝ᵥ design.atom pole) ^ 2)) * hbase

/-- The diagonal cofactor is never positive: a pair repeated cannot wrap. -/
theorem polarWrapCofactor_diag (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (first apex : Fin m) :
    polarWrapCofactor design pole first first apex ≤ 0 := by
  have hbridge := polarWrapCofactor_mul_leverage design hpole first first apex
  have hanti := polarSignedWedge_antisymm design pole first apex
  rw [hanti] at hbridge
  by_contra hcontra
  have hcof : 0 < polarWrapCofactor design pole first first apex := not_le.mp hcontra
  have hprod : 0 < (design.atom pole ⬝ᵥ design.atom pole)
      * polarWrapCofactor design pole first first apex := mul_pos hpole hcof
  rw [hbridge] at hprod
  nlinarith [sq_nonneg (polarSignedWedge design pole first apex)]

/-- **THE CYCLIC WEDGES BUILD THE WRAPPING.**  Three labels whose three cyclic
signed wedges are positive form a wrapping triple. -/
theorem polarWrapping_of_signedWedge_cyclic (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hone : 0 < polarSignedWedge design pole first second)
    (htwo : 0 < polarSignedWedge design pole second third)
    (hthree : 0 < polarSignedWedge design pole third first) :
    PolarWrapping design pole first second third := by
  have hb1 := polarWrapCofactor_mul_leverage design hpole first second third
  have hb2 := polarWrapCofactor_mul_leverage design hpole second third first
  have hb3 := polarWrapCofactor_mul_leverage design hpole third first second
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hb1, hpole, mul_pos hthree htwo]
  · nlinarith [hb2, hpole, mul_pos hone hthree]
  · nlinarith [hb3, hpole, mul_pos htwo hone]

/-- A wrapping triple carries a nonzero signed wedge on every edge. -/
theorem polarSignedWedge_ne_zero_of_polarWrapping (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) :
    polarSignedWedge design pole first second ≠ 0 := by
  intro hzero
  have hb := polarWrapCofactor_mul_leverage design hpole third first second
  rw [hzero, mul_zero] at hb
  nlinarith [hwrap.2.2, hpole, hb]

/-- **THE THREE CYCLIC WEDGES OF A WRAPPING TRIPLE SHARE A SIGN.**  This is the
converse of `Gtz.polarWrapping_of_signedWedge_cyclic`, and it is the statement
that the complex field has no analogue of: over the complex field the wedge is
not a real number and carries no sign. -/
theorem polarSignedWedge_cyclic_of_polarWrapping (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) :
    (0 < polarSignedWedge design pole first second
        ∧ 0 < polarSignedWedge design pole second third
        ∧ 0 < polarSignedWedge design pole third first)
      ∨ (polarSignedWedge design pole first second < 0
        ∧ polarSignedWedge design pole second third < 0
        ∧ polarSignedWedge design pole third first < 0) := by
  have hb1 := polarWrapCofactor_mul_leverage design hpole first second third
  have hb2 := polarWrapCofactor_mul_leverage design hpole second third first
  have hb3 := polarWrapCofactor_mul_leverage design hpole third first second
  have hne := polarSignedWedge_ne_zero_of_polarWrapping design hpole hwrap
  have hprod1 : 0 < polarSignedWedge design pole third first
      * polarSignedWedge design pole second third := by
    rw [← hb1]
    exact mul_pos hpole hwrap.1
  have hprod2 : 0 < polarSignedWedge design pole first second
      * polarSignedWedge design pole third first := by
    rw [← hb2]
    exact mul_pos hpole hwrap.2.1
  have hprod3 : 0 < polarSignedWedge design pole second third
      * polarSignedWedge design pole first second := by
    rw [← hb3]
    exact mul_pos hpole hwrap.2.2
  rcases lt_trichotomy (polarSignedWedge design pole first second) 0 with hneg | hzero | hpos
  · exact Or.inr ⟨hneg, by nlinarith [hprod3], by nlinarith [hprod2]⟩
  · exact absurd hzero hne
  · exact Or.inl ⟨hpos, by nlinarith [hprod3], by nlinarith [hprod2]⟩

/-- **THE CARATHEODORY CONCLUSION.**  At a wrapping triple the origin is a
strictly positive combination of the three signed shadows, with the cyclic
signed wedges as the coefficients. -/
theorem exists_pos_dependency_of_polarWrapping (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) :
    ∃ cfirst csecond cthird : ℝ, 0 < cfirst ∧ 0 < csecond ∧ 0 < cthird
      ∧ cfirst • polarSignedVec design pole first
          + csecond • polarSignedVec design pole second
        + cthird • polarSignedVec design pole third = 0 := by
  have hcramer := polarSignedVec_cramer design hpole first second third
  rcases polarSignedWedge_cyclic_of_polarWrapping design hpole hwrap with
    ⟨hone, htwo, hthree⟩ | ⟨hone, htwo, hthree⟩
  · exact ⟨polarSignedWedge design pole second third,
      polarSignedWedge design pole third first,
      polarSignedWedge design pole first second, htwo, hthree, hone, hcramer⟩
  · refine ⟨-polarSignedWedge design pole second third,
      -polarSignedWedge design pole third first,
      -polarSignedWedge design pole first second, by linarith, by linarith, by linarith, ?_⟩
    rw [neg_smul, neg_smul, neg_smul, ← neg_add, ← neg_add, hcramer, neg_zero]

/-- A wrapping triple carries a nonzero anchored bracket on every edge. -/
theorem tripleBracket_ne_zero_of_polarWrapping (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) :
    tripleBracket (design.atom pole) (design.atom first) (design.atom second) ≠ 0 := by
  intro hzero
  exact polarSignedWedge_ne_zero_of_polarWrapping design hpole hwrap
    (by rw [polarSignedWedge, hzero, mul_zero])

/-- The first two labels of a wrapping triple are distinct. -/
theorem polarWrapping_ne_first_second (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) : first ≠ second := by
  intro heq
  have hdiag := polarWrapCofactor_diag design hpole first third
  rw [← heq] at hwrap
  linarith [hwrap.1, hdiag]

/-- The last two labels of a wrapping triple are distinct. -/
theorem polarWrapping_ne_second_third (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) : second ≠ third := by
  intro heq
  have hdiag := polarWrapCofactor_diag design hpole second first
  rw [← heq] at hwrap
  linarith [hwrap.2.1, hdiag]

/-- The outer labels of a wrapping triple are distinct. -/
theorem polarWrapping_ne_first_third (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) : first ≠ third := by
  intro heq
  have hdiag := polarWrapCofactor_diag design hpole third second
  rw [heq] at hwrap
  linarith [hwrap.2.2, hdiag]

/-- **NO LABEL OF A WRAPPING TRIPLE IS THE POLE.**  The pole has no signed
shadow, thus every cofactor through it vanishes. -/
theorem polarWrapping_notMem_pole (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) :
    pole ∉ ({first, second, third} : Finset (Fin m)) := by
  have hpolePair : ∀ label : Fin m, polarSignedPair design pole pole label = 0 := fun label =>
    polarSignedPair_pole design hpole label
  have hpairSym : ∀ label : Fin m, polarSignedPair design pole label pole = 0 := fun label => by
    rw [polarSignedPair_comm]; exact hpolePair label
  have hpoleSq : polarSignedSq design pole pole = 0 := polarSignedSq_pole design hpole
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_⟩
  · have h := hwrap.1
    rw [polarWrapCofactor, ← heq, hpolePair third, hpolePair second, zero_mul, zero_mul,
      zero_sub] at h
    linarith
  · have h := hwrap.2.1
    rw [polarWrapCofactor, ← heq, hpolePair first, hpolePair third, zero_mul, zero_mul,
      zero_sub] at h
    linarith
  · have h := hwrap.2.2
    rw [polarWrapCofactor, ← heq, hpolePair second, hpolePair first, zero_mul, zero_mul,
      zero_sub] at h
    linarith

/-- A wrapping triple has three labels. -/
theorem polarWrapping_card_three (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) :
    ({first, second, third} : Finset (Fin m)).card = 3 :=
  Finset.card_eq_three.mpr ⟨first, second, third,
    polarWrapping_ne_first_second design hpole hwrap,
    polarWrapping_ne_first_third design hpole hwrap,
    polarWrapping_ne_second_third design hpole hwrap, rfl⟩

/-- **A WRAPPING TRIPLE SPREADS THE POLE PLANE.**  Its plane Gram determinant is
strictly positive, thus the second bound of the direct cover has room at the
selected triple. -/
theorem polarPlaneGramDet_pos_of_polarWrapping (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) :
    0 < polarPlaneGramDet design pole ({first, second, third} : Finset (Fin m)) := by
  have hbracket := tripleBracket_ne_zero_of_polarWrapping design hpole hwrap
  have hwedge := sum_tripleBracket_sq_eq_planeGramDet design hpole
    ({first, second, third} : Finset (Fin m))
  have hmemFirst : first ∈ ({first, second, third} : Finset (Fin m)) := by simp
  have hmemSecond : second ∈ ({first, second, third} : Finset (Fin m)) := by simp
  have hpos : 0 < ∑ c ∈ ({first, second, third} : Finset (Fin m)),
      ∑ d ∈ ({first, second, third} : Finset (Fin m)),
        tripleBracket (design.atom pole) (design.atom c) (design.atom d) ^ 2 := by
    refine Finset.sum_pos' (fun c _ => Finset.sum_nonneg fun d _ => sq_nonneg _)
      ⟨first, hmemFirst, ?_⟩
    refine Finset.sum_pos' (fun d _ => sq_nonneg _) ⟨second, hmemSecond, ?_⟩
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hbracket))
  rw [hwedge] at hpos
  nlinarith [hpos, hpole]

/-- The wrapping property is cyclic in its three labels. -/
theorem PolarWrapping.cycle {design : WeightedDesign m 3} {pole first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) :
    PolarWrapping design pole second third first :=
  ⟨hwrap.2.1, hwrap.2.2, hwrap.1⟩

/-- Every label of a wrapping triple carries a strictly positive signed
energy. -/
theorem polarSignedSq_pos_of_polarWrapping (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) :
    0 < polarSignedSq design pole first := by
  have hne := polarSignedWedge_ne_zero_of_polarWrapping design hpole hwrap
  refine lt_of_le_of_ne (polarSignedSq_nonneg design hpole first) ?_
  intro hzero
  exact hne (polarSignedWedge_eq_zero_of_signedSq_eq_zero design hpole hzero.symm second)

/-- **THE VERTEX LAW.**  At a wrapping triple every label has a strictly
negative signed pairing with one of its two partners: the origin lies on the far
side of the opposite edge. -/
theorem polarSignedPair_neg_of_polarWrapping (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) :
    polarSignedPair design pole first second < 0
      ∨ polarSignedPair design pole first third < 0 := by
  obtain ⟨cfirst, csecond, cthird, hcfirst, hcsecond, hcthird, hdep⟩ :=
    exists_pos_dependency_of_polarWrapping design hpole hwrap
  have hread : (cfirst • polarSignedVec design pole first
      + csecond • polarSignedVec design pole second
      + cthird • polarSignedVec design pole third) ⬝ᵥ polarSignedVec design pole first
      = cfirst * polarSignedSq design pole first
        + csecond * polarSignedPair design pole second first
        + cthird * polarSignedPair design pole third first := by
    rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, smul_eq_mul,
      polarSignedVec_dotProduct_self design hpole first,
      polarSignedVec_dotProduct_pair design hpole second first,
      polarSignedVec_dotProduct_pair design hpole third first]
  rw [hdep, zero_dotProduct] at hread
  have hsq := polarSignedSq_pos_of_polarWrapping design hpole hwrap
  have hcomm₁ := polarSignedPair_comm design pole second first
  have hcomm₂ := polarSignedPair_comm design pole third first
  by_contra hcontra
  rw [not_or, not_lt, not_lt] at hcontra
  nlinarith [hread, hsq, hcontra.1, hcontra.2, hcfirst, hcsecond, hcthird]

/-- **AT LEAST TWO EDGES OF A WRAPPING TRIPLE ARE NEGATIVE.**  The vertex law at
all three labels, resolved by counting: a wrapping triple cannot keep two of its
signed pairings at or above zero. -/
theorem polarSignedPair_two_neg_of_polarWrapping (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) :
    (polarSignedPair design pole first second < 0
        ∧ polarSignedPair design pole second third < 0)
      ∨ (polarSignedPair design pole second third < 0
          ∧ polarSignedPair design pole third first < 0)
      ∨ (polarSignedPair design pole third first < 0
          ∧ polarSignedPair design pole first second < 0) := by
  have hfirst := polarSignedPair_neg_of_polarWrapping design hpole hwrap
  have hsecond := polarSignedPair_neg_of_polarWrapping design hpole hwrap.cycle
  have hthird := polarSignedPair_neg_of_polarWrapping design hpole hwrap.cycle.cycle
  have hswap₁ := polarSignedPair_comm design pole first third
  have hswap₂ := polarSignedPair_comm design pole second first
  have hswap₃ := polarSignedPair_comm design pole third second
  rcases hfirst with hab | hac
  · rcases hthird with hca | hcb
    · exact Or.inr (Or.inr ⟨by linarith [hswap₁], hab⟩)
    · exact Or.inl ⟨hab, by linarith [hswap₃]⟩
  · rcases hsecond with hbc | hba
    · exact Or.inr (Or.inl ⟨hbc, by linarith [hswap₁]⟩)
    · exact Or.inr (Or.inr ⟨by linarith [hswap₁], by linarith [hswap₂]⟩)

end WrapBridge

/-! ## Part 5: the circular order

The theorem.  At every pole of positive leverage the five signed shadows admit a
wrapping triple, unless they degenerate: either all of them vanish, or two of
them are antiparallel. -/

section CircularOrder

variable {m : ℕ}

/-- **THE CIRCULAR ORDER OF THE POLE PLANE.**  At every pole of positive
leverage, one of three things happens.  Every signed shadow vanishes, or two
signed shadows are parallel with a negative overlap, or three signed shadows
wrap the origin.

The proof takes an anchor of positive signed energy, reads its wedge row, and
selects inside the positive part of that row the label of least ratio of the
pairing row to the wedge row.  The rotation law turns that extremum into the
sign of every wedge from the selected label into the positive part.  The anchor
identity at the selected label then supplies a label outside the positive part
whose wedge from the selected label is positive, and the two cases of its own
wedge against the anchor are the wrapping triple and the antiparallel pair.

The whole argument is the real order of a plane.  Over the complex field the
signed shadows live in a four dimensional real space where three points span a
triangle that misses the origin, and the probes measure that miss at every one
of 3432 complex poles. -/
theorem exists_polarWrapping_or_degenerate (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) :
    (∀ label : Fin m, polarSignedSq design pole label = 0)
      ∨ (∃ first second : Fin m, polarSignedWedge design pole first second = 0
          ∧ polarSignedPair design pole first second < 0)
      ∨ (∃ first second third : Fin m, PolarWrapping design pole first second third) := by
  classical
  by_cases hnull : ∀ label : Fin m, polarSignedSq design pole label = 0
  · exact Or.inl hnull
  obtain ⟨anchor, hanchorNe⟩ := not_forall.mp hnull
  have hanchorPos : 0 < polarSignedSq design pole anchor :=
    lt_of_le_of_ne (polarSignedSq_nonneg design hpole anchor) (Ne.symm hanchorNe)
  by_cases hflat : ∀ label : Fin m, polarSignedWedge design pole anchor label = 0
  · -- THE FLAT BRANCH.  The whole wedge row of the anchor vanishes, thus every
    -- signed shadow is parallel to the anchor, and the pairing row supplies the
    -- antiparallel partner.
    refine Or.inr (Or.inl ?_)
    by_contra hcontra
    have hnonneg : ∀ label : Fin m, 0 ≤ polarSignedPair design pole anchor label := by
      intro label
      by_contra hneg
      exact hcontra ⟨anchor, label, hflat label, not_le.mp hneg⟩
    have hsum : 0 < ∑ c, design.weight c * polarSignedPair design pole c anchor := by
      refine Finset.sum_pos' (fun c _ => ?_) ⟨anchor, Finset.mem_univ anchor, ?_⟩
      · rw [polarSignedPair_comm design pole c anchor]
        exact mul_nonneg (design.weight_pos c).le (hnonneg c)
      · rw [polarSignedPair_self]
        exact mul_pos (design.weight_pos anchor) hanchorPos
    rw [sum_weight_polarSignedPair design hpole anchor] at hsum
    exact lt_irrefl 0 hsum
  obtain ⟨witness, hwitnessNe⟩ := not_forall.mp hflat
  -- THE ANCHOR ROW CARRIES A STRICTLY POSITIVE ENTRY.
  have hexistsPos : ∃ label : Fin m, 0 < polarSignedWedge design pole anchor label := by
    by_contra hcontra
    have hle : ∀ label : Fin m, polarSignedWedge design pole anchor label ≤ 0 := by
      intro label
      by_contra h
      exact hcontra ⟨label, not_le.mp h⟩
    have hstrict : polarSignedWedge design pole anchor witness < 0 :=
      lt_of_le_of_ne (hle witness) hwitnessNe
    have hsum : ∑ c, design.weight c * polarSignedWedge design pole anchor c
        < ∑ _c : Fin m, (0 : ℝ) :=
      Finset.sum_lt_sum
        (fun c _ => mul_nonpos_of_nonneg_of_nonpos (design.weight_pos c).le (hle c))
        ⟨witness, Finset.mem_univ witness,
          mul_neg_of_pos_of_neg (design.weight_pos witness) hstrict⟩
    rw [Finset.sum_const_zero, sum_weight_polarSignedWedge_row design pole anchor] at hsum
    exact lt_irrefl 0 hsum
  obtain ⟨seed, hseedPos⟩ := hexistsPos
  -- THE POSITIVE PART OF THE ANCHOR ROW, AND THE LABEL OF LEAST RATIO INSIDE IT.
  set positivePart : Finset (Fin m) :=
    Finset.univ.filter (fun c => 0 < polarSignedWedge design pole anchor c) with hposDef
  have hseedMem : seed ∈ positivePart := by
    rw [hposDef, Finset.mem_filter]
    exact ⟨Finset.mem_univ seed, hseedPos⟩
  obtain ⟨front, hfrontMem, hfrontMin⟩ := Finset.exists_min_image positivePart
    (fun c => polarSignedPair design pole anchor c / polarSignedWedge design pole anchor c)
    ⟨seed, hseedMem⟩
  have hfrontPos : 0 < polarSignedWedge design pole anchor front := by
    rw [hposDef, Finset.mem_filter] at hfrontMem
    exact hfrontMem.2
  -- THE EXTREMUM IS A SIGN.
  have hfrontSign : ∀ c ∈ positivePart, polarSignedWedge design pole front c ≤ 0 := by
    intro c hc
    have hcPos : 0 < polarSignedWedge design pole anchor c := by
      rw [hposDef, Finset.mem_filter] at hc
      exact hc.2
    have hratio := hfrontMin c hc
    have hcross : polarSignedPair design pole anchor front
        * polarSignedWedge design pole anchor c
        ≤ polarSignedPair design pole anchor c * polarSignedWedge design pole anchor front :=
      (div_le_div_iff₀ hfrontPos hcPos).mp hratio
    have hrot := polarSignedSq_mul_polarSignedWedge design hpole anchor front c
    nlinarith [hrot, hcross, hanchorPos]
  -- THE ANCHOR IDENTITY AT THE SELECTED LABEL SUPPLIES AN OUTSIDE LABEL.
  have hanchorMem : anchor ∈ positivePartᶜ := by
    rw [Finset.mem_compl, hposDef, Finset.mem_filter]
    intro hmem
    rw [polarSignedWedge_self] at hmem
    exact lt_irrefl 0 hmem.2
  have hanchorNeg : polarSignedWedge design pole front anchor < 0 := by
    have hanti := polarSignedWedge_antisymm design pole anchor front
    linarith
  have houtside : ∃ c ∈ positivePartᶜ, 0 < polarSignedWedge design pole front c := by
    by_contra hcontra
    have hle : ∀ c ∈ positivePartᶜ, polarSignedWedge design pole front c ≤ 0 := by
      intro c hc
      by_contra h
      exact hcontra ⟨c, hc, not_le.mp h⟩
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin m))
      (fun c => 0 < polarSignedWedge design pole anchor c)
      (fun c => design.weight c * polarSignedWedge design pole front c)
    have houtsideSet : Finset.univ.filter
        (fun c => ¬ 0 < polarSignedWedge design pole anchor c) = positivePartᶜ := by
      rw [hposDef, Finset.compl_filter]
    rw [houtsideSet] at hsplit
    have hinside : ∑ c ∈ positivePart,
        design.weight c * polarSignedWedge design pole front c ≤ 0 :=
      Finset.sum_nonpos fun c hc =>
        mul_nonpos_of_nonneg_of_nonpos (design.weight_pos c).le (hfrontSign c hc)
    have herase : ∑ c ∈ positivePartᶜ.erase anchor,
        design.weight c * polarSignedWedge design pole front c ≤ 0 :=
      Finset.sum_nonpos fun c hc =>
        mul_nonpos_of_nonneg_of_nonpos (design.weight_pos c).le
          (hle c (Finset.mem_of_mem_erase hc))
    have houtsideSum : ∑ c ∈ positivePartᶜ,
        design.weight c * polarSignedWedge design pole front c
        = design.weight anchor * polarSignedWedge design pole front anchor
          + ∑ c ∈ positivePartᶜ.erase anchor,
              design.weight c * polarSignedWedge design pole front c :=
      (Finset.add_sum_erase _ _ hanchorMem).symm
    have hnegTerm : design.weight anchor * polarSignedWedge design pole front anchor < 0 :=
      mul_neg_of_pos_of_neg (design.weight_pos anchor) hanchorNeg
    have htotal := sum_weight_polarSignedWedge_row design pole front
    rw [← hsplit] at htotal
    linarith [hinside, herase, houtsideSum, hnegTerm, htotal]
  obtain ⟨outer, houterMem, houterPos⟩ := houtside
  have houterSign : polarSignedWedge design pole anchor outer ≤ 0 := by
    rw [Finset.mem_compl, hposDef, Finset.mem_filter] at houterMem
    exact not_lt.mp fun hlt => houterMem ⟨Finset.mem_univ outer, hlt⟩
  rcases lt_or_eq_of_le houterSign with houterNeg | houterZero
  · -- THE WRAPPING TRIPLE.
    refine Or.inr (Or.inr ⟨anchor, front, outer, ?_⟩)
    refine polarWrapping_of_signedWedge_cyclic design hpole hfrontPos houterPos ?_
    have hanti := polarSignedWedge_antisymm design pole anchor outer
    linarith
  · -- THE ANTIPARALLEL PAIR.
    refine Or.inr (Or.inl ⟨anchor, outer, houterZero, ?_⟩)
    have hrot := polarSignedSq_mul_polarSignedWedge design hpole anchor front outer
    rw [houterZero, mul_zero, zero_sub] at hrot
    nlinarith [hrot, hanchorPos, houterPos, hfrontPos]

end CircularOrder

/-! ## Part 5b: the null branch is impossible at a primitive tie

If every signed shadow of a pole vanishes then, in a primitive design, every
other atom reads zero at that pole.  The tilt of any covering is then exactly
zero, thus the landed polar cover insertion produces a strictly dominating
subset and the design is no tie.  The circular order of a primitive tie is a
DICHOTOMY: an antiparallel pair, or a wrapping triple. -/

section NullBranch

variable {size rank : ℕ}

/-- **A POLE WHOSE COMPLEMENT IS ORTHOGONAL CARRIES A DOMINATING SUBSET.**  The
tilt of every covering is exactly zero, thus the landed insertion fires with no
budget spent at all. -/
theorem not_isTie_of_orthogonal_complement (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    {pole : Fin size} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hnull : ∀ label : Fin size, label ≠ pole → design.atom label ⬝ᵥ design.atom pole = 0) :
    ¬ IsTie design := by
  classical
  intro htie
  obtain ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin hrank hpredecessor design hlong
  have hleverage : 0 < design.atom pole ⬝ᵥ design.atom pole := lt_trans zero_lt_one hlong
  have hzero : ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun label hlabel => ?_
    rw [hnull label fun heq => hnotMem (heq ▸ hlabel)]
    ring
  have htilt : ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2
      < margin * (design.atom pole ⬝ᵥ design.atom pole)
        * (design.atom pole ⬝ᵥ design.atom pole - 1) := by
    rw [hzero]
    exact mul_pos (mul_pos hmarginPos hleverage) (by linarith)
  have hposDef := posDef_insert_of_polarCover design hnotMem hlong hmarginPos hcover htilt
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hnotMem, hcard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-- **THE CIRCULAR ORDER OF A PRIMITIVE TIE IS A DICHOTOMY.**  The null branch
of `Gtz.exists_polarWrapping_or_degenerate` cannot occur at a primitive tie with
an overshooting pole, thus every such pole carries an antiparallel pair or a
wrapping triple. -/
theorem polarCircularDichotomy_of_isTie {m : ℕ} (design : WeightedDesign m 3)
    (hprimitive : IsPrimitiveDesign design) (htie : IsTie design) {pole : Fin m}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    (∃ first second : Fin m, polarSignedWedge design pole first second = 0
        ∧ polarSignedPair design pole first second < 0)
      ∨ (∃ first second third : Fin m, PolarWrapping design pole first second third) := by
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole := lt_trans zero_lt_one hlong
  rcases exists_polarWrapping_or_degenerate design hpole with hnull | hflat | hwrap
  · exact absurd htie (not_isTie_of_orthogonal_complement (by norm_num) gtz_rank_two design
      hlong fun label hne =>
        (polarSignedSq_eq_zero_iff_of_primitive design hprimitive hpole hne).mp (hnull label))
  · exact Or.inl hflat
  · exact Or.inr hwrap

/-- **THE ANTIPARALLEL PAIR CARRIES ITS OWN POSITIVE DEPENDENCY.**  A vanishing
signed wedge with a negative signed pairing puts the origin strictly inside the
segment of the two signed shadows. -/
theorem exists_pos_dependency_of_antiparallel {m : ℕ} (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second : Fin m}
    (hwedge : polarSignedWedge design pole first second = 0)
    (hpair : polarSignedPair design pole first second < 0) :
    0 < polarSignedSq design pole second
      ∧ polarSignedSq design pole second • polarSignedVec design pole first
          + (-polarSignedPair design pole first second) • polarSignedVec design pole second
        = 0 := by
  have hsq := polarSignedWedge_sq_eq_signedGram design hpole first second
  rw [hwedge] at hsq
  have hne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  have hgram : polarSignedSq design pole first * polarSignedSq design pole second
      = polarSignedPair design pole first second ^ 2 := by
    have hzero : (0 : ℝ) = (design.atom pole ⬝ᵥ design.atom pole)
        * (polarSignedSq design pole first * polarSignedSq design pole second
          - polarSignedPair design pole first second ^ 2) := by
      rw [← hsq]; ring
    have := (mul_eq_zero.mp hzero.symm).resolve_left hne
    linarith
  have hfirst := polarSignedSq_nonneg design hpole first
  have hsecond := polarSignedSq_nonneg design hpole second
  have hsecondPos : 0 < polarSignedSq design pole second := by
    rcases lt_or_eq_of_le hsecond with hlt | heq
    · exact hlt
    · exfalso
      rw [← heq, mul_zero] at hgram
      nlinarith [hgram, hpair]
  refine ⟨hsecondPos, ?_⟩
  have h11 := polarSignedVec_dotProduct_self design hpole first
  have h22 := polarSignedVec_dotProduct_self design hpole second
  have h12 := polarSignedVec_dotProduct_pair design hpole first second
  have h21 := polarSignedVec_dotProduct_pair design hpole second first
  rw [polarSignedPair_comm design pole second first] at h21
  refine eq_zero_of_dotProduct_self_eq_zero ?_
  have hexpand : (polarSignedSq design pole second • polarSignedVec design pole first
        + (-polarSignedPair design pole first second) • polarSignedVec design pole second)
      ⬝ᵥ (polarSignedSq design pole second • polarSignedVec design pole first
        + (-polarSignedPair design pole first second) • polarSignedVec design pole second)
      = polarSignedSq design pole second * polarSignedSq design pole second
          * (polarSignedVec design pole first ⬝ᵥ polarSignedVec design pole first)
        + polarSignedSq design pole second * (-polarSignedPair design pole first second)
          * (polarSignedVec design pole first ⬝ᵥ polarSignedVec design pole second)
        + (-polarSignedPair design pole first second) * polarSignedSq design pole second
          * (polarSignedVec design pole second ⬝ᵥ polarSignedVec design pole first)
        + (-polarSignedPair design pole first second)
            * (-polarSignedPair design pole first second)
          * (polarSignedVec design pole second ⬝ᵥ polarSignedVec design pole second) := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  rw [hexpand, h11, h22, h12, h21]
  linear_combination (polarSignedSq design pole second) * hgram

/-- **THE CARATHEODORY THEOREM OF THE POLE PLANE.**  At a primitive tie, every
overshooting pole carries three labels whose signed shadows admit a positive
dependency with at least two strictly positive coefficients: the origin is a
convex combination of at most three signed shadows.  Over the complex field the
signed shadows live in a four dimensional real space and no three of them reach
the origin, and the probes measure that miss at every complex tie. -/
theorem exists_pos_dependency_of_isTie {m : ℕ} (design : WeightedDesign m 3)
    (hprimitive : IsPrimitiveDesign design) (htie : IsTie design) {pole : Fin m}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    ∃ (first second third : Fin m) (cfirst csecond cthird : ℝ),
      0 < cfirst ∧ 0 < csecond ∧ 0 ≤ cthird
        ∧ cfirst • polarSignedVec design pole first
            + csecond • polarSignedVec design pole second
          + cthird • polarSignedVec design pole third = 0 := by
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole := lt_trans zero_lt_one hlong
  rcases polarCircularDichotomy_of_isTie design hprimitive htie hlong with hflat | hwrap
  · obtain ⟨first, second, hwedge, hpair⟩ := hflat
    obtain ⟨hsecondPos, hdep⟩ :=
      exists_pos_dependency_of_antiparallel design hpole hwedge hpair
    refine ⟨first, second, first, polarSignedSq design pole second,
      -polarSignedPair design pole first second, 0, hsecondPos, by linarith, le_refl 0, ?_⟩
    rw [zero_smul, add_zero]
    exact hdep
  · obtain ⟨first, second, third, hwrapping⟩ := hwrap
    obtain ⟨cfirst, csecond, cthird, hcfirst, hcsecond, hcthird, hdep⟩ :=
      exists_pos_dependency_of_polarWrapping design hpole hwrapping
    exact ⟨first, second, third, cfirst, csecond, cthird, hcfirst, hcsecond, hcthird.le, hdep⟩

end NullBranch

/-! ## Part 6: the seventh narrowing

The circular order is a theorem at every pole, thus handing it to the prover
costs nothing.  Handed TOGETHER with the arithmetic plane bound at the selected
wrapping triple it becomes the sharpest single object of the polar lane. -/

section CircularBundle

variable {size rank : ℕ}

/-- **THE ARITHMETIC PLANE BOUND AT ONE TRIPLE.**  What a tie supplies at a
named triple: either the triple keeps its pole mass at or below the leverage, or
its shadow adjugate form spends the whole plane budget. -/
def PolarPlaneShadowBoundAt (design : WeightedDesign size rank) (pole : Fin size)
    (selected : Finset (Fin size)) : Prop :=
  ∀ excess : ℝ, 0 < excess →
    2 * (1 + excess) ≤ ∑ c ∈ selected, planeShadowSq design pole c →
    (1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + excess) ^ 2
        ≤ polarPlaneGramDet design pole selected →
      (∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
          ≤ design.atom pole ⬝ᵥ design.atom pole
        ∨ polarPlaneDet design pole selected
            * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
              - design.atom pole ⬝ᵥ design.atom pole)
          ≤ polarShadowAdjugate design pole selected

/-- The arithmetic plane bound is free at every tie, at every triple of three
labels and at every pole of positive leverage. -/
theorem polarPlaneShadowBoundAt_of_isTie (design : WeightedDesign size 3)
    (htie : IsTie design) {pole : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {selected : Finset (Fin size)}
    (hcard : selected.card = 3) : PolarPlaneShadowBoundAt design pole selected := by
  intro excess hexcessPos htrace hgram
  by_contra hcontra
  rw [not_or, not_le, not_le] at hcontra
  exact not_isTie_of_planeShadowSchur_rank_three design hpole hcard hexcessPos htrace hgram
    hcontra.1 hcontra.2 htie

/-- **THE CIRCULAR SHADOW BOUND.**  The seventh bundle: the circular order of
the pole plane, with the arithmetic plane bound already applied at the selected
wrapping triple.  Every clause is a polynomial statement in the leverage, the
pole readings, the shadow energies and the shadow pairings, and the guard makes
the bundle vacuous away from rank three. -/
def PolarCircularShadowBound (design : WeightedDesign size rank) (pole : Fin size) : Prop :=
  rank = 3 → 1 < design.atom pole ⬝ᵥ design.atom pole →
    (∃ first second : Fin size,
          polarSignedSq design pole first * polarSignedSq design pole second
              = polarSignedPair design pole first second ^ 2
            ∧ polarSignedPair design pole first second < 0)
      ∨ (∃ first second third : Fin size,
            PolarWrapping design pole first second third
              ∧ ({first, second, third} : Finset (Fin size)).card = 3
              ∧ pole ∉ ({first, second, third} : Finset (Fin size))
              ∧ 0 < polarPlaneGramDet design pole ({first, second, third} : Finset (Fin size))
              ∧ PolarPlaneShadowBoundAt design pole
                  ({first, second, third} : Finset (Fin size)))

/-- **THE CIRCULAR SHADOW BOUND IS FREE AT EVERY TIE.**  No predecessor rank, no
primitivity, no overshooting pole and no size guard are consumed. -/
theorem polarCircularShadowBound_of_isTie (design : WeightedDesign size rank)
    (hprimitive : IsPrimitiveDesign design) (htie : IsTie design) (pole : Fin size) :
    PolarCircularShadowBound design pole := by
  intro hrank hlong
  subst hrank
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole := lt_trans zero_lt_one hlong
  rcases polarCircularDichotomy_of_isTie design hprimitive htie hlong with hflat | hwrap
  · obtain ⟨first, second, hwedge, hpair⟩ := hflat
    refine Or.inl ⟨first, second, ?_, hpair⟩
    have hsq := polarSignedWedge_sq_eq_signedGram design hpole first second
    rw [hwedge] at hsq
    have hzero : (0 : ℝ) = (design.atom pole ⬝ᵥ design.atom pole)
        * (polarSignedSq design pole first * polarSignedSq design pole second
          - polarSignedPair design pole first second ^ 2) := by
      rw [← hsq]; ring
    have hne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
    have := (mul_eq_zero.mp hzero.symm).resolve_left hne
    linarith
  · obtain ⟨first, second, third, hwrapping⟩ := hwrap
    refine Or.inr ⟨first, second, third, hwrapping,
      polarWrapping_card_three design hpole hwrapping,
      polarWrapping_notMem_pole design hpole hwrapping,
      polarPlaneGramDet_pos_of_polarWrapping design hpole hwrapping, ?_⟩
    exact polarPlaneShadowBoundAt_of_isTie design htie hpole
      (polarWrapping_card_three design hpole hwrapping)

/-- **THE SEVEN-BUNDLE TILT RESIDUAL.**  `Gtz.PolarTiltSelectionPlane` with the
circular order of the pole plane handed to the prover as well.  This is the
first bundle of the polar chain that no complex tie satisfies. -/
def PolarTiltSelectionCircular (size rank : ℕ) : Prop :=
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
    PolarPlaneShadowBound design pole →
    PolarCircularShadowBound design pole →
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

/-- The seven-bundle residual is weaker than the six-bundle one. -/
theorem polarTiltSelectionCircular_of_polarTiltSelectionPlane
    (htilt : PolarTiltSelectionPlane size rank) : PolarTiltSelectionCircular size rank :=
  fun design pole covering margin hprimitive htie hlong hbudget hheavy hset hspread hwitness
    hplane _hcircular hmargin hcard hnotMem hcover =>
    htilt design pole covering margin hprimitive htie hlong hbudget hheavy hset hspread
      hwitness hplane hmargin hcard hnotMem hcover

/-- The seven-bundle residual is weaker than the five-bundle one. -/
theorem polarTiltSelectionCircular_of_polarTiltSelectionWitness
    (htilt : PolarTiltSelectionWitness size rank) : PolarTiltSelectionCircular size rank :=
  polarTiltSelectionCircular_of_polarTiltSelectionPlane
    (polarTiltSelectionPlane_of_polarTiltSelectionWitness htilt)

/-- The seven-bundle residual is weaker than the shipped one. -/
theorem polarTiltSelectionCircular_of_polarTiltSelection
    (htilt : PolarTiltSelection size rank) : PolarTiltSelectionCircular size rank :=
  polarTiltSelectionCircular_of_polarTiltSelectionPlane
    (polarTiltSelectionPlane_of_polarTiltSelection htilt)

/-- **THE HINGE FROM THE SEVEN-BUNDLE RESIDUAL.**  All seven bundles are
theorems at a tie, thus the seventh narrowing costs nothing downstream. -/
theorem hingeHoldsAtSize_of_polarTiltCircular (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionCircular size rank) : HingeHoldsAtSize size rank := by
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
      (polarPlaneShadowBound_of_isTie design htie pole)
      (polarCircularShadowBound_of_isTie design hprimitive htie pole)
      hmarginPos hcard hnotMem hcover
  have hposDef := posDef_insert_of_polarCover design hselNotMem hlong hmarginPos hselCover
    hselTilt
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hselNotMem, hselCard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-! ### Every consumer of the shipped residual, on the seven-bundle one -/

/-- Arm (i). -/
theorem stressFreeArmAt_of_polarTiltCircular (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionCircular size rank) : StressFreeArmAt size rank :=
  fun design _hfree htie =>
    hingeHoldsAtSize_of_polarTiltCircular hrank hpredecessor hroom htilt design htie

/-- Arm (ii). -/
theorem balancedArmAt_of_polarTiltCircular (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionCircular size rank) : BalancedArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltCircular hrank hpredecessor hroom htilt design htie

/-- Arm (iii). -/
theorem degenerateArmAt_of_polarTiltCircular (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionCircular size rank) : DegenerateArmAt size rank :=
  fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
    hingeHoldsAtSize_of_polarTiltCircular hrank hpredecessor hroom htilt design htie

/-- The partial-support sub-arm. -/
theorem balancedPartialSupportArmAt_of_polarTiltCircular (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionCircular size rank) : BalancedPartialSupportArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hunsupported _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltCircular hrank hpredecessor hroom htilt design htie

/-- The full-support sub-arm. -/
theorem balancedFullSupportArmAt_of_polarTiltCircular (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionCircular size rank) : BalancedFullSupportArmAt size rank :=
  fun design _stressCoeff _hstress _hfull htie =>
    hingeHoldsAtSize_of_polarTiltCircular hrank hpredecessor hroom htilt design htie

/-- The repaired degenerate cover. -/
theorem degenerateHyperplaneCover_of_polarTiltCircular (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionCircular size rank) : DegenerateHyperplaneCover size rank := by
  intro design _stressCoeff _unitNormal _pole hprimitive htie _hstressNe _hunit _hstress
    _hsupport _hpole
  exact absurd
    (hingeHoldsAtSize_of_polarTiltCircular hrank hpredecessor hroom htilt design htie)
    ((isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive)

/-- **THE COLLAPSE, ON THE SEVEN-BUNDLE RESIDUAL.** -/
theorem polarTiltCircular_closes_every_arm (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionCircular size rank) :
    HingeHoldsAtSize size rank ∧ StressFreeArmAt size rank ∧ BalancedArmAt size rank
      ∧ DegenerateArmAt size rank ∧ BalancedPartialSupportArmAt size rank
      ∧ BalancedFullSupportArmAt size rank ∧ DegenerateHyperplaneCover size rank :=
  ⟨hingeHoldsAtSize_of_polarTiltCircular hrank hpredecessor hroom htilt,
    stressFreeArmAt_of_polarTiltCircular hrank hpredecessor hroom htilt,
    balancedArmAt_of_polarTiltCircular hrank hpredecessor hroom htilt,
    degenerateArmAt_of_polarTiltCircular hrank hpredecessor hroom htilt,
    balancedPartialSupportArmAt_of_polarTiltCircular hrank hpredecessor hroom htilt,
    balancedFullSupportArmAt_of_polarTiltCircular hrank hpredecessor hroom htilt,
    degenerateHyperplaneCover_of_polarTiltCircular hrank hpredecessor hroom htilt⟩

/-! ### The registry obligations, on the seven-bundle residual -/

/-- The threshold cell obligation of the registry. -/
theorem thresholdCellHingeRankFourAndUp_of_polarTiltCircular
    (htilt : ∀ rank : ℕ, 4 ≤ rank → PolarTiltSelectionCircular (thresholdSize rank) rank) :
    ∀ rank : ℕ, 4 ≤ rank → GtzWeightedAll (rank - 1) →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor _hcell design htie
  have hroom : rank + 1 ≤ rank * (rank + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc (rank + 1) * 2 ≤ (rank + 1) * rank := Nat.mul_le_mul_left _ (by omega)
      _ = rank * (rank + 1) := Nat.mul_comm _ _
  exact hingeHoldsAtSize_of_polarTiltCircular (by omega) hpredecessor hroom (htilt rank hrank)
    design htie

/-- The sub-threshold band obligation of the registry. -/
theorem subThresholdBandHinge_of_polarTiltCircular
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size < thresholdSize rank →
      PolarTiltSelectionCircular size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor size hlow hhigh _hcell design htie
  exact hingeHoldsAtSize_of_polarTiltCircular (by omega) hpredecessor (by omega)
    (htilt rank size hrank hlow hhigh) design htie

/-- The whole sharp window, from one seven-bundle residual per cell. -/
theorem sharpWindowHinge_of_polarTiltCircular
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size ≤ thresholdSize rank →
      PolarTiltSelectionCircular size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        HingeHoldsAtSize size rank := by
  intro rank hrank hpredecessor size hlow hhigh
  exact hingeHoldsAtSize_of_polarTiltCircular (by omega) hpredecessor (by omega)
    (htilt rank size hrank hlow hhigh)

/-- Arm (i) at the deciding cell of a rank. -/
theorem thresholdStressFreeArm_of_polarTiltCircular (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionCircular (thresholdSize rank) rank) :
    ThresholdStressFreeArm rank :=
  stressFreeArmAt_of_polarTiltCircular hrank hpredecessor hroom htilt

/-- Arm (ii) at the deciding cell of a rank. -/
theorem thresholdBalancedArm_of_polarTiltCircular (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionCircular (thresholdSize rank) rank) :
    ThresholdBalancedArm rank :=
  balancedArmAt_of_polarTiltCircular hrank hpredecessor hroom htilt

/-- Arm (iii) at the deciding cell of a rank. -/
theorem thresholdDegenerateArm_of_polarTiltCircular (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionCircular (thresholdSize rank) rank) :
    ThresholdDegenerateArm rank :=
  degenerateArmAt_of_polarTiltCircular hrank hpredecessor hroom htilt

end CircularBundle

/-! ## Part 7: the deciding cell, the calibration and the guardrail -/

section CircularSixThree

/-- **THE DECIDING CELL OF RANK THREE FROM THE SEVEN-BUNDLE RESIDUAL ALONE.** -/
theorem hingeHoldsAtSize_six_three_of_polarTiltCircular
    (htilt : PolarTiltSelectionCircular 6 3) : HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_polarTiltCircular (by norm_num) gtz_rank_two (by norm_num) htilt

/-- The three rank-three arms from the seven-bundle residual. -/
theorem thresholdArms_rank_three_of_polarTiltCircular
    (htilt : PolarTiltSelectionCircular 6 3) :
    ThresholdStressFreeArm 3 ∧ ThresholdBalancedArm 3 ∧ ThresholdDegenerateArm 3 := by
  have hhinge := hingeHoldsAtSize_six_three_of_polarTiltCircular htilt
  exact ⟨fun design _hfree htie => hhinge design htie,
    fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie => hhinge design htie,
    fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
      hhinge design htie⟩

/-- **THE DECIDING CELL, FROM THE SEVEN-BUNDLE RESIDUAL ALONE.** -/
theorem gtzWeighted_six_three_of_polarTiltCircular
    (htilt : PolarTiltSelectionCircular 6 3) : GtzWeighted 6 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltCircular htilt
  exact GeneralRankReach.gtzWeighted_six_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **ALL OF RANK THREE, FROM THE SEVEN-BUNDLE RESIDUAL ALONE.** -/
theorem gtzWeightedAll_three_of_polarTiltCircular
    (htilt : PolarTiltSelectionCircular 6 3) : GtzWeightedAll 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltCircular htilt
  exact GeneralRankReach.gtzWeightedAll_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **THE SEVEN-BUNDLE RESIDUAL IS FALSE AT `(5,3)`.**  The circular order is
free at every pole of every size, thus the calibration transports through the
seventh narrowing unchanged. -/
theorem not_polarTiltSelectionCircular_five_three : ¬ PolarTiltSelectionCircular 5 3 :=
  fun htilt => not_hingeHoldsAtSize_five_three
    (hingeHoldsAtSize_of_polarTiltCircular (by norm_num) gtz_rank_two (by norm_num) htilt)

/-- **THE GUARDRAIL.**  The `(6,3)` tie in the tree is not primitive, thus it
does not touch the seven-bundle residual, and the last-stage Prop stays
refuted. -/
theorem sixSplitDiamondDesign_spares_polarTiltCircular :
    ¬ RankSuccShrinks 6 3 ∧ IsTie sixSplitDiamondDesign
      ∧ ¬ IsPrimitiveDesign sixSplitDiamondDesign
      ∧ ¬ PolarTiltSelectionCircular 5 3 :=
  ⟨not_rankSuccShrinks_six_three, sixSplitDiamondDesign_isTie,
    not_isPrimitiveDesign_sixSplitDiamondDesign, not_polarTiltSelectionCircular_five_three⟩

end CircularSixThree

/-! ## Part 8: the wrapping kill, a named and calibrated target

The residual of Part 6 walks the pair-and-tilt route.  The kill of
`Gtz.not_isTie_of_planeShadowSchur_rank_three` walks a second route directly:
it asks for a pole and a TRIPLE whose shadow trace, plane Gram determinant,
pole mass and shadow adjugate form clear four polynomial bounds.  This part
names that target, and it names the strictly stronger version in which the
triple is a WRAPPING triple of the circular order.

The probes measure the two versions against each other.  On 3749 real near-tie
endpoints the kill fires at a wrapping combination at 3749 of them, and the
wrapping combinations carry the kill at 74.7 percent against 28.3 percent
elsewhere.  Adversarially, minimising the worse of the tie gap and the kill
margin RESTRICTED to wrapping triples reaches `0.5306 / 0.1556 / 0.6090 /
0.1364` on four slices against `0.5666 / 0.1622 / 0.5639 / 0.1367`
unrestricted, and no pole of the 73830 adversarial poles lacks a wrapping
triple.  The restriction costs nothing, and it tells a prover where to look. -/

section WrapKill

variable {size : ℕ}

/-- **THE ARITHMETIC SELECTION TARGET.**  At every primitive tie of rank three
some pole of leverage above one and some triple of three labels avoiding it
clear the two cover bounds, the pole surplus and the arithmetic test.  Every
clause is a polynomial inequality in the leverage, the pole readings, the shadow
energies and the shadow pairings. -/
def PolarShadowSchurSelection (size : ℕ) : Prop :=
  ∀ design : WeightedDesign size 3, IsPrimitiveDesign design → IsTie design →
    ∃ (pole : Fin size) (selected : Finset (Fin size)) (excess : ℝ),
      1 < design.atom pole ⬝ᵥ design.atom pole
        ∧ selected.card = 3
        ∧ 0 < excess
        ∧ 2 * (1 + excess) ≤ ∑ c ∈ selected, planeShadowSq design pole c
        ∧ (1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + excess) ^ 2
            ≤ polarPlaneGramDet design pole selected
        ∧ design.atom pole ⬝ᵥ design.atom pole
            < ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2
        ∧ polarShadowAdjugate design pole selected
            < polarPlaneDet design pole selected
              * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
                - design.atom pole ⬝ᵥ design.atom pole)

/-- **THE WRAPPING KILL.**  The same target with the triple pinned to a WRAPPING
triple of the circular order.  It is strictly stronger than
`Gtz.PolarShadowSchurSelection`, and the probes show the restriction is free. -/
def PolarWrapSelection (size : ℕ) : Prop :=
  ∀ design : WeightedDesign size 3, IsPrimitiveDesign design → IsTie design →
    ∃ (pole first second third : Fin size) (excess : ℝ),
      1 < design.atom pole ⬝ᵥ design.atom pole
        ∧ PolarWrapping design pole first second third
        ∧ 0 < excess
        ∧ 2 * (1 + excess)
            ≤ ∑ c ∈ ({first, second, third} : Finset (Fin size)), planeShadowSq design pole c
        ∧ (1 + excess)
              * (∑ c ∈ ({first, second, third} : Finset (Fin size)),
                  planeShadowSq design pole c)
            - (1 + excess) ^ 2
          ≤ polarPlaneGramDet design pole ({first, second, third} : Finset (Fin size))
        ∧ design.atom pole ⬝ᵥ design.atom pole
            < ∑ c ∈ ({first, second, third} : Finset (Fin size)),
                (design.atom c ⬝ᵥ design.atom pole) ^ 2
        ∧ polarShadowAdjugate design pole ({first, second, third} : Finset (Fin size))
            < polarPlaneDet design pole ({first, second, third} : Finset (Fin size))
              * ((∑ c ∈ ({first, second, third} : Finset (Fin size)),
                    (design.atom c ⬝ᵥ design.atom pole) ^ 2)
                - design.atom pole ⬝ᵥ design.atom pole)

/-- The wrapping kill is the stronger of the two targets. -/
theorem polarShadowSchurSelection_of_polarWrapSelection
    (hwrap : PolarWrapSelection size) : PolarShadowSchurSelection size := by
  intro design hprimitive htie
  obtain ⟨pole, first, second, third, excess, hlong, hwrapping, hexcess, htrace, hgram,
    hz, htest⟩ := hwrap design hprimitive htie
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole := lt_trans zero_lt_one hlong
  exact ⟨pole, ({first, second, third} : Finset (Fin size)), excess, hlong,
    polarWrapping_card_three design hpole hwrapping, hexcess, htrace, hgram, hz, htest⟩

/-- **THE HINGE FROM THE ARITHMETIC SELECTION TARGET.**  The kill of
`Gtz.not_isTie_of_planeShadowSchur_rank_three` closes the hinge at every size
of rank three. -/
theorem hingeHoldsAtSize_of_polarShadowSchurSelection
    (hselect : PolarShadowSchurSelection size) : HingeHoldsAtSize size 3 := by
  intro design htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  obtain ⟨pole, selected, excess, hlong, hcard, hexcess, htrace, hgram, hz, htest⟩ :=
    hselect design hprimitive htie
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole := lt_trans zero_lt_one hlong
  exact not_isTie_of_planeShadowSchur_rank_three design hpole hcard hexcess htrace hgram
    hz htest htie

/-- The hinge from the wrapping kill. -/
theorem hingeHoldsAtSize_of_polarWrapSelection (hwrap : PolarWrapSelection size) :
    HingeHoldsAtSize size 3 :=
  hingeHoldsAtSize_of_polarShadowSchurSelection
    (polarShadowSchurSelection_of_polarWrapSelection hwrap)

/-- The three rank-three arms from the arithmetic selection target. -/
theorem thresholdArms_rank_three_of_polarShadowSchurSelection
    (hselect : PolarShadowSchurSelection 6) :
    ThresholdStressFreeArm 3 ∧ ThresholdBalancedArm 3 ∧ ThresholdDegenerateArm 3 := by
  have hhinge := hingeHoldsAtSize_of_polarShadowSchurSelection hselect
  exact ⟨fun design _hfree htie => hhinge design htie,
    fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie => hhinge design htie,
    fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
      hhinge design htie⟩

/-- **THE DECIDING CELL FROM THE ARITHMETIC SELECTION TARGET ALONE.** -/
theorem gtzWeighted_six_three_of_polarShadowSchurSelection
    (hselect : PolarShadowSchurSelection 6) : GtzWeighted 6 3 := by
  have harms := thresholdArms_rank_three_of_polarShadowSchurSelection hselect
  exact GeneralRankReach.gtzWeighted_six_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **ALL OF RANK THREE FROM THE ARITHMETIC SELECTION TARGET ALONE.** -/
theorem gtzWeightedAll_three_of_polarShadowSchurSelection
    (hselect : PolarShadowSchurSelection 6) : GtzWeightedAll 3 := by
  have harms := thresholdArms_rank_three_of_polarShadowSchurSelection hselect
  exact GeneralRankReach.gtzWeightedAll_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **THE DECIDING CELL FROM THE WRAPPING KILL ALONE.** -/
theorem gtzWeighted_six_three_of_polarWrapSelection (hwrap : PolarWrapSelection 6) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_polarShadowSchurSelection
    (polarShadowSchurSelection_of_polarWrapSelection hwrap)

/-- **ALL OF RANK THREE FROM THE WRAPPING KILL ALONE.** -/
theorem gtzWeightedAll_three_of_polarWrapSelection (hwrap : PolarWrapSelection 6) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_polarShadowSchurSelection
    (polarShadowSchurSelection_of_polarWrapSelection hwrap)

/-- **THE ARITHMETIC SELECTION TARGET IS FALSE AT SIZE FIVE.**  The `(5,3)`
diamond is a primitive tie that no pole and no triple can kill, thus the
calibration of the whole polar chain transports to this route. -/
theorem not_polarShadowSchurSelection_five : ¬ PolarShadowSchurSelection 5 :=
  fun hselect => not_hingeHoldsAtSize_five_three
    (hingeHoldsAtSize_of_polarShadowSchurSelection hselect)

/-- The wrapping kill is false at size five. -/
theorem not_polarWrapSelection_five : ¬ PolarWrapSelection 5 :=
  fun hwrap => not_polarShadowSchurSelection_five
    (polarShadowSchurSelection_of_polarWrapSelection hwrap)

/-- **THE GUARDRAIL ON THE KILL ROUTE.**  The `(6,3)` tie in the tree is not
primitive, thus it does not touch either target, and the size-five instance
stays refuted. -/
theorem sixSplitDiamondDesign_spares_polarWrapSelection :
    ¬ RankSuccShrinks 6 3 ∧ IsTie sixSplitDiamondDesign
      ∧ ¬ IsPrimitiveDesign sixSplitDiamondDesign
      ∧ ¬ PolarShadowSchurSelection 5 ∧ ¬ PolarWrapSelection 5 :=
  ⟨not_rankSuccShrinks_six_three, sixSplitDiamondDesign_isTie,
    not_isPrimitiveDesign_sixSplitDiamondDesign, not_polarShadowSchurSelection_five,
    not_polarWrapSelection_five⟩

end WrapKill

end Gtz
