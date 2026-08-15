import Gtz.Design.WeightedFormCriterion
import Gtz.Design.FrameConservation
import Gtz.Design.SphereExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-!
# The meeting identity of two concurrent lines

The two-meeting-lines pattern `[[0, 1, 2], [0, 3, 4]]` puts labels `0, 1, 2` in
one plane through the origin and labels `0, 3, 4` in another.  Label `0` is
shared, and label `5` lies on NEITHER plane.  Each plane carries a normal, and
the residual `Gtz.TwoMeetingLinesTenthHeavyJointBlindTransversal` hands both
normals over as unit vectors together with their orthogonality relations.

Read Parseval as a bilinear form at the PAIR of normals rather than at one
normal twice.  Labels `0, 1, 2` read zero at the first normal and labels
`0, 3, 4` read zero at the second, so five of the six terms vanish and a single
term survives:

* `twoMeetingLines_meeting_identity` — the open label's two normal readings
  multiply, against its weight, to the inner product of the two normals.

Nothing else in the design appears.  The angle between the two planes is
carried entirely by the one atom that lies on neither of them.

## What the identity buys

Parseval read at one normal gives the landed unit law: the complement of a line
carries exactly one unit of weighted energy there
(`Gtz.sum_compl_weighted_sq_eq_energy_of_orthogonal`).  Two lines give two such
laws, and the meeting identity multiplies them:

* `twoMeetingLines_angle_identity` — the squared inner product of the normals
  equals the product of the two line-private deficits.

That is an exact equality between a quantity built only from the normals and a
quantity built only from the four private atoms.  Two consequences follow at
once.  The open label reads nonzero at both normals whenever the planes are not
perpendicular (`twoMeetingLines_openAtom_readings_ne_zero`), and each line's
privates are capped at the other normal by the squared sine of the angle
(`twoMeetingLines_secondPrivates_le_sin_sq` and its mirror).

## The rigidity kernel

The shared label is orthogonal to both normals, so it is annihilated by their
cross product.  In rank three that pins it to a line:

* `twoMeetingLines_sharedAtom_crossProduct_kill`
* `twoMeetingLines_sharedAtom_eq_smul_crossProduct`

The two normals fix the shared atom up to scale.  This is the pattern's
rigidity kernel in vector form.

## Field legality

The cross product and the real orthogonal complement are real constructions.
Over `ℂ` a nonzero vector can be isotropic, so a nonzero cross product no longer
forces a one-dimensional annihilator, and the meeting identity loses its sign
content because a squared reading may be negative.
-/

namespace TwoMeetingLinesRigidity

end TwoMeetingLinesRigidity

section MeetingIdentity

variable (design : WeightedDesign 6 3)

/-- **THE MEETING IDENTITY.**  At the two line normals Parseval reads as a
bilinear form.  Labels `0, 1, 2` die at the first normal and labels `0, 3, 4`
die at the second, so only the open label `5` survives, and its two readings
multiply to the inner product of the normals.

No normalization is used: the identity holds for any pair of normals obeying the
two orthogonality relations. -/
theorem twoMeetingLines_meeting_identity
    (normalFirst normalSecond : Fin 3 → ℝ)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0) :
    design.weight 5
        * ((design.atom 5 ⬝ᵥ normalFirst) * (design.atom 5 ⬝ᵥ normalSecond))
      = normalFirst ⬝ᵥ normalSecond := by
  have hbil := parseval_weighted_bilinear design normalFirst normalSecond
  rw [Fin.sum_univ_six] at hbil
  have hzero : normalFirst ⬝ᵥ design.atom 0 = 0 := by
    rw [dotProduct_comm]; exact horthFirst 0 (by decide)
  have hone : normalFirst ⬝ᵥ design.atom 1 = 0 := by
    rw [dotProduct_comm]; exact horthFirst 1 (by decide)
  have htwo : normalFirst ⬝ᵥ design.atom 2 = 0 := by
    rw [dotProduct_comm]; exact horthFirst 2 (by decide)
  have hthree : design.atom 3 ⬝ᵥ normalSecond = 0 := horthSecond 3 (by decide)
  have hfour : design.atom 4 ⬝ᵥ normalSecond = 0 := horthSecond 4 (by decide)
  have hfive : normalFirst ⬝ᵥ design.atom 5 = design.atom 5 ⬝ᵥ normalFirst :=
    dotProduct_comm _ _
  rw [hzero, hone, htwo, hthree, hfour, hfive] at hbil
  linear_combination hbil

/-- The unit law at the first normal, with the complement written out.  The
second line's two private labels and the open label carry the whole energy. -/
theorem twoMeetingLines_firstNormal_unitLaw
    (normalFirst : Fin 3 → ℝ)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0) :
    design.weight 3 * (design.atom 3 ⬝ᵥ normalFirst) ^ 2
        + design.weight 4 * (design.atom 4 ⬝ᵥ normalFirst) ^ 2
        + design.weight 5 * (design.atom 5 ⬝ᵥ normalFirst) ^ 2
      = normalFirst ⬝ᵥ normalFirst := by
  have hid := sum_compl_weighted_sq_eq_energy_of_orthogonal design
    ({0, 1, 2} : Finset (Fin 6)) normalFirst horthFirst
  have hcompl : ({0, 1, 2} : Finset (Fin 6))ᶜ = {3, 4, 5} := by decide
  rw [hcompl, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hid
  linarith

/-- The unit law at the second normal.  The first line's two private labels and
the open label carry the whole energy. -/
theorem twoMeetingLines_secondNormal_unitLaw
    (normalSecond : Fin 3 → ℝ)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0) :
    design.weight 1 * (design.atom 1 ⬝ᵥ normalSecond) ^ 2
        + design.weight 2 * (design.atom 2 ⬝ᵥ normalSecond) ^ 2
        + design.weight 5 * (design.atom 5 ⬝ᵥ normalSecond) ^ 2
      = normalSecond ⬝ᵥ normalSecond := by
  have hid := sum_compl_weighted_sq_eq_energy_of_orthogonal design
    ({0, 3, 4} : Finset (Fin 6)) normalSecond horthSecond
  have hcompl : ({0, 3, 4} : Finset (Fin 6))ᶜ = {1, 2, 5} := by decide
  rw [hcompl, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hid
  linarith

/-- **THE ANGLE IDENTITY.**  The squared inner product of the two normals equals
the product of the two line-private deficits.  The left side reads only the
normals.  The right side reads only the four private labels.  The open label has
been eliminated between the meeting identity and the two unit laws. -/
theorem twoMeetingLines_angle_identity
    (normalFirst normalSecond : Fin 3 → ℝ)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0) :
    (normalFirst ⬝ᵥ normalSecond) ^ 2
      = (normalFirst ⬝ᵥ normalFirst
            - design.weight 3 * (design.atom 3 ⬝ᵥ normalFirst) ^ 2
            - design.weight 4 * (design.atom 4 ⬝ᵥ normalFirst) ^ 2)
        * (normalSecond ⬝ᵥ normalSecond
            - design.weight 1 * (design.atom 1 ⬝ᵥ normalSecond) ^ 2
            - design.weight 2 * (design.atom 2 ⬝ᵥ normalSecond) ^ 2) := by
  have hmeet := twoMeetingLines_meeting_identity design normalFirst normalSecond
    horthFirst horthSecond
  have hfirst := twoMeetingLines_firstNormal_unitLaw design normalFirst horthFirst
  have hsecond := twoMeetingLines_secondNormal_unitLaw design normalSecond horthSecond
  have hkey : (normalFirst ⬝ᵥ normalSecond) ^ 2
      = (design.weight 5 * (design.atom 5 ⬝ᵥ normalFirst) ^ 2)
        * (design.weight 5 * (design.atom 5 ⬝ᵥ normalSecond) ^ 2) := by
    rw [← hmeet]; ring
  rw [hkey]
  congr 1
  · linarith
  · linarith

/-- Whenever the two planes are not perpendicular the open label reads nonzero
at both normals.  The meeting identity forces it: a vanishing reading at either
normal would make the inner product of the normals zero. -/
theorem twoMeetingLines_openAtom_readings_ne_zero
    (normalFirst normalSecond : Fin 3 → ℝ)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hangle : normalFirst ⬝ᵥ normalSecond ≠ 0) :
    design.atom 5 ⬝ᵥ normalFirst ≠ 0 ∧ design.atom 5 ⬝ᵥ normalSecond ≠ 0 := by
  have hmeet := twoMeetingLines_meeting_identity design normalFirst normalSecond
    horthFirst horthSecond
  constructor
  · intro hcontra
    exact hangle (by rw [← hmeet, hcontra]; ring)
  · intro hcontra
    exact hangle (by rw [← hmeet, hcontra]; ring)

/-- **THE SINE CAP AT THE FIRST NORMAL.**  With unit normals the second line's
two private labels read, in weighted square, at most the squared sine of the
angle between the planes.  Nearly coincident planes force the second line's
privates almost into the first plane. -/
theorem twoMeetingLines_secondPrivates_le_sin_sq
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0) :
    design.weight 3 * (design.atom 3 ⬝ᵥ normalFirst) ^ 2
        + design.weight 4 * (design.atom 4 ⬝ᵥ normalFirst) ^ 2
      ≤ 1 - (normalFirst ⬝ᵥ normalSecond) ^ 2 := by
  have hangle := twoMeetingLines_angle_identity design normalFirst normalSecond
    horthFirst horthSecond
  rw [hunitFirst, hunitSecond] at hangle
  have hfirst := twoMeetingLines_firstNormal_unitLaw design normalFirst horthFirst
  rw [hunitFirst] at hfirst
  have hdeficit : 0 ≤ 1
      - design.weight 3 * (design.atom 3 ⬝ᵥ normalFirst) ^ 2
      - design.weight 4 * (design.atom 4 ⬝ᵥ normalFirst) ^ 2 := by
    nlinarith [design.weight_pos 5, sq_nonneg (design.atom 5 ⬝ᵥ normalFirst)]
  have hcap : (1 : ℝ)
      - design.weight 1 * (design.atom 1 ⬝ᵥ normalSecond) ^ 2
      - design.weight 2 * (design.atom 2 ⬝ᵥ normalSecond) ^ 2 ≤ 1 := by
    nlinarith [design.weight_pos 1, design.weight_pos 2,
      sq_nonneg (design.atom 1 ⬝ᵥ normalSecond),
      sq_nonneg (design.atom 2 ⬝ᵥ normalSecond)]
  nlinarith [hangle, hdeficit, hcap]

/-- The mirror cap: the first line's privates are capped at the second normal by
the same squared sine. -/
theorem twoMeetingLines_firstPrivates_le_sin_sq
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0) :
    design.weight 1 * (design.atom 1 ⬝ᵥ normalSecond) ^ 2
        + design.weight 2 * (design.atom 2 ⬝ᵥ normalSecond) ^ 2
      ≤ 1 - (normalFirst ⬝ᵥ normalSecond) ^ 2 := by
  have hangle := twoMeetingLines_angle_identity design normalFirst normalSecond
    horthFirst horthSecond
  rw [hunitFirst, hunitSecond] at hangle
  have hsecond := twoMeetingLines_secondNormal_unitLaw design normalSecond horthSecond
  rw [hunitSecond] at hsecond
  have hdeficit : 0 ≤ 1
      - design.weight 1 * (design.atom 1 ⬝ᵥ normalSecond) ^ 2
      - design.weight 2 * (design.atom 2 ⬝ᵥ normalSecond) ^ 2 := by
    nlinarith [design.weight_pos 5, sq_nonneg (design.atom 5 ⬝ᵥ normalSecond)]
  have hcap : (1 : ℝ)
      - design.weight 3 * (design.atom 3 ⬝ᵥ normalFirst) ^ 2
      - design.weight 4 * (design.atom 4 ⬝ᵥ normalFirst) ^ 2 ≤ 1 := by
    nlinarith [design.weight_pos 3, design.weight_pos 4,
      sq_nonneg (design.atom 3 ⬝ᵥ normalFirst),
      sq_nonneg (design.atom 4 ⬝ᵥ normalFirst)]
  nlinarith [hangle, hdeficit, hcap]

end MeetingIdentity

section SharedAtomRigidity

variable (design : WeightedDesign 6 3)

/-- **THE RIGIDITY KERNEL, VECTOR FORM.**  The shared label is orthogonal to
both normals, so the cross product of the normals annihilates it.  This is the
triple-product expansion `(u × v) × w = v (u ⬝ w) - u (v ⬝ w)` with both inner
products zero, written out in coordinates so no vector identity is needed. -/
theorem twoMeetingLines_sharedAtom_crossProduct_kill
    (normalFirst normalSecond : Fin 3 → ℝ)
    (horthFirst : design.atom 0 ⬝ᵥ normalFirst = 0)
    (horthSecond : design.atom 0 ⬝ᵥ normalSecond = 0) :
    crossProduct (crossProduct normalFirst normalSecond) (design.atom 0) = 0 := by
  have hfirst : design.atom 0 0 * normalFirst 0 + design.atom 0 1 * normalFirst 1
      + design.atom 0 2 * normalFirst 2 = 0 := by
    rw [dotProduct, Fin.sum_univ_three] at horthFirst
    linarith
  have hsecond : design.atom 0 0 * normalSecond 0 + design.atom 0 1 * normalSecond 1
      + design.atom 0 2 * normalSecond 2 = 0 := by
    rw [dotProduct, Fin.sum_univ_three] at horthSecond
    linarith
  funext component
  fin_cases component
  · show (normalFirst 2 * normalSecond 0 - normalFirst 0 * normalSecond 2)
          * design.atom 0 2
        - (normalFirst 0 * normalSecond 1 - normalFirst 1 * normalSecond 0)
          * design.atom 0 1 = 0
    linear_combination (normalSecond 0) * hfirst - (normalFirst 0) * hsecond
  · show (normalFirst 0 * normalSecond 1 - normalFirst 1 * normalSecond 0)
          * design.atom 0 0
        - (normalFirst 1 * normalSecond 2 - normalFirst 2 * normalSecond 1)
          * design.atom 0 2 = 0
    linear_combination (normalSecond 1) * hfirst - (normalFirst 1) * hsecond
  · show (normalFirst 1 * normalSecond 2 - normalFirst 2 * normalSecond 1)
          * design.atom 0 1
        - (normalFirst 2 * normalSecond 0 - normalFirst 0 * normalSecond 2)
          * design.atom 0 0 = 0
    linear_combination (normalSecond 2) * hfirst - (normalFirst 2) * hsecond

/-- **THE SHARED ATOM IS PINNED UP TO SCALE.**  Non-parallel normals fix the
shared label to the line of their cross product.  One scalar remains, and the
two normals determine everything else about it. -/
theorem twoMeetingLines_sharedAtom_eq_smul_crossProduct
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hcrossNe : crossProduct normalFirst normalSecond ≠ 0)
    (horthFirst : design.atom 0 ⬝ᵥ normalFirst = 0)
    (horthSecond : design.atom 0 ⬝ᵥ normalSecond = 0) :
    ∃ ratio : ℝ,
      design.atom 0 = ratio • crossProduct normalFirst normalSecond :=
  eq_smul_of_crossProduct_eq_zero hcrossNe
    (twoMeetingLines_sharedAtom_crossProduct_kill design normalFirst normalSecond
      horthFirst horthSecond)

end SharedAtomRigidity

end Gtz
