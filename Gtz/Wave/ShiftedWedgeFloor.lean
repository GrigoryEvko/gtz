import Mathlib
import Gtz.Wave.PluckerSchurFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12800000

/-!
# The shifted wedge: a per-triple floor that reads all three symmetric functions

The campaign selects a triple and then certifies it with the WEDGE STEP
`Gtz.atomBlockDet_mul_le_atomBlockSecond_mul`, which reads

  `lambda_min ≥ e3 / e2`.

That step is lossy, and the loss is measured.  At the exact real extremal of the
spectral value the winning triple carries the spectrum `(1/6, 16/21, 1)`, so
`e1 = 27/14`, `e2 = 133/126`, `e3 = 16/126`, and the wedge reads `16/133 =
0.120301` against the truth `1/6 = 0.166667`.  The wedge step alone throws away
twenty-eight percent, and the adversarial value of `max over the twenty triples
of e3 / e2` over real frames is `0.10923`, which is BELOW the field-agnostic
ceiling `1 / (3 * phi ^ 2) = 0.127322`.  No selection argument built on the
wedge step can reach the summit.

## The repair

`lambda_min` is the smallest root of `t ^ 3 - e1 t ^ 2 + e2 t - e3`, so it is
EXACTLY determined by the three symmetric functions.  A per-triple certificate
that reads all three is lossless in principle.  This module supplies one, and it
is the wedge step itself applied a second time to a SHIFTED block.

`Gtz.atomBlendFloor_shift`: if the block of a triple already carries the floor
`shift`, then it carries the floor

  `shift + (det of the shifted block) / (second minor total of the shifted block)`.

Iterating from `shift = 0` gives `psi 1 = e3 / e2`, the landed wedge step, and
then

  `psi (k+1) = psi k + (e3 - e2 * psi k + e1 * psi k ^ 2 - psi k ^ 3)
                        / (e2 - 2 * e1 * psi k + 3 * psi k ^ 2)`,

which is Newton's method on the characteristic polynomial and converges to
`lambda_min` from below.  At the extremal triple the family reads

  `psi 1 = 0.120301,  psi 2 = 0.161516,  psi 3 = 0.166592,  psi 4 = 0.1666666`,

against `1 / 6 = 0.1666667`.  Adversarial descent over real frames, behind a
calibration gate that reproduced the spectral value `1/6` at the exact extremal
to `8.3e-17`, measured

  `min over frames of max over triples of psi 1 = 0.10926`,
  `min over frames of max over triples of psi 2 = 0.15764`,
  `min over frames of max over triples of psi 3 = 0.16648`.

The first two come from 3000 restarts by 20000 steps, and they moved by less
than `1e-3` against a run at one fifth of that budget.  The margin of `psi 2`
over the field-agnostic ceiling is twenty-four percent, so this is not the shape
of a small positive floor.

So ONE extra shifted wedge step carries the per-triple half of the route past
the field-agnostic ceiling, and two carry it to within one part in a thousand of
the truth.  It also does not prove that these measured minima are the true ones.

## What a successor lane must prove, and what it is worth

This module does NOT supply the SELECTION step.  The campaign selects with the
DETERMINANTAL MEASURE: the twenty triple determinants total one
(`Gtz.atomBlockDet_familySum`), so the largest reading is at least the
determinantal average of the readings.  That average was measured too, and it
pins the whole program:

  `min over frames of (determinantal average of psi 1) = 0.1000000000`,
  `min over frames of (determinantal average of psi 2) = 0.14844`,
  `min over frames of (determinantal average of psi 3) = 0.15848`.

The first reading is one tenth to twelve digits, which is exactly the constant
that `Gtz.atomSpectralSupply_tenth_of_unbalanced` delivers.  The two statements
are not the same inequality: the energy statement is
`∑ p * second ≤ 10 * ∑ p ^ 2`, and this average is `∑ p ^ 2 / second`.  But they
carry the same constant and the same extremal, so one tenth is the CEILING of the
landed wedge step under the campaign's own selector, and not an artefact of the
energy coordinates.

The successor target is the same average with `psi 2` in place of `psi 1`.  It is
worth `0.148`, which passes the Hermitian value `0.127322` that no field-agnostic
argument can pass.  The obstruction is that `psi 2` is a ratio, so the average
needs a common denominator or one Cauchy-Schwarz step.

## How the step is proved

The whole content is one Cayley-Hamilton identity for a symmetric block of order
three.  Write `B` for the block, `e1, e2, e3` for its symmetric functions and
`u = B v`.  Then `e2 * B - e3 * I = e1 * B ^ 2 - B ^ 3`, so

  `e2 * (v . B v) - e3 * (v . v) = e1 * (u . u) - (u . B u)`.

`Gtz.atomSymCayley` is that identity, and `ring` proves it.  The right side is not
negative because a positive semidefinite block of order three obeys
`B ≤ (trace B) * I` (`Gtz.atomSymTraceDominates`), which follows from the three
two-by-two minors alone.  So `Gtz.atomSymWedge` gives `e3 * (v . v) ≤ e2 * (v . B v)`
for every positive semidefinite block, with NO frame in sight, and the shifted
block of a triple that already carries a floor is such a block.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

Every statement below is proved.  There is no named hypothesis in this module.

## Vacuity

`Gtz.atomBlendFloor_shift` is not vacuous: `Gtz.atomBlendFloor_zero` shows every
triple carries the floor zero, so the iteration always starts.
-/

namespace Gtz

/-! ## Layer 0 — a symmetric block of order three, read through six numbers -/

/-- The TRACE of a symmetric block of order three. -/
def atomSymTrace (diagOne diagTwo diagThree : ℝ) : ℝ := diagOne + diagTwo + diagThree

/-- The SECOND MINOR TOTAL of a symmetric block of order three. -/
def atomSymSecond (diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree : ℝ) : ℝ :=
  (diagOne * diagTwo - offOneTwo ^ 2) + (diagOne * diagThree - offOneThree ^ 2)
    + (diagTwo * diagThree - offTwoThree ^ 2)

/-- The DETERMINANT of a symmetric block of order three. -/
def atomSymDet (diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree : ℝ) : ℝ :=
  diagOne * diagTwo * diagThree + 2 * offOneTwo * offOneThree * offTwoThree
    - diagOne * offTwoThree ^ 2 - diagTwo * offOneThree ^ 2 - diagThree * offOneTwo ^ 2

/-- The QUADRATIC READING of a symmetric block of order three against a vector. -/
def atomSymQuad (diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree
    partOne partTwo partThree : ℝ) : ℝ :=
  diagOne * partOne ^ 2 + diagTwo * partTwo ^ 2 + diagThree * partThree ^ 2
    + 2 * (offOneTwo * partOne * partTwo + offOneThree * partOne * partThree
      + offTwoThree * partTwo * partThree)

/-- The FIRST COORDINATE of the image of a vector under the block. -/
def atomSymPushOne (diagOne offOneTwo offOneThree partOne partTwo partThree : ℝ) : ℝ :=
  diagOne * partOne + offOneTwo * partTwo + offOneThree * partThree

/-- The SECOND COORDINATE of the image of a vector under the block. -/
def atomSymPushTwo (diagTwo offOneTwo offTwoThree partOne partTwo partThree : ℝ) : ℝ :=
  offOneTwo * partOne + diagTwo * partTwo + offTwoThree * partThree

/-- The THIRD COORDINATE of the image of a vector under the block. -/
def atomSymPushThree (diagThree offOneThree offTwoThree partOne partTwo partThree : ℝ) : ℝ :=
  offOneThree * partOne + offTwoThree * partTwo + diagThree * partThree

/-- **THE CAYLEY IDENTITY OF A SYMMETRIC BLOCK OF ORDER THREE.**  Cayley-Hamilton
gives `e2 * B - e3 * I = e1 * B ^ 2 - B ^ 3`.  Read against one vector, with
`u = B v`, that is the identity below.  It needs no hypothesis. -/
theorem atomSymCayley (diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree
    partOne partTwo partThree : ℝ) :
    atomSymSecond diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree
        * atomSymQuad diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree
            partOne partTwo partThree
      - atomSymDet diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree
        * (partOne ^ 2 + partTwo ^ 2 + partThree ^ 2)
      = atomSymTrace diagOne diagTwo diagThree
          * (atomSymPushOne diagOne offOneTwo offOneThree partOne partTwo partThree ^ 2
            + atomSymPushTwo diagTwo offOneTwo offTwoThree partOne partTwo partThree ^ 2
            + atomSymPushThree diagThree offOneThree offTwoThree partOne partTwo partThree ^ 2)
        - atomSymQuad diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree
            (atomSymPushOne diagOne offOneTwo offOneThree partOne partTwo partThree)
            (atomSymPushTwo diagTwo offOneTwo offTwoThree partOne partTwo partThree)
            (atomSymPushThree diagThree offOneThree offTwoThree partOne partTwo partThree) := by
  simp only [atomSymSecond, atomSymDet, atomSymTrace, atomSymQuad, atomSymPushOne, atomSymPushTwo, atomSymPushThree]
  ring

/-- **THE TWO-SLOT STEP.**  A diagonal reading that is not negative, together
with a two-by-two minor that is not negative, caps the cross term. -/
theorem atomSymPairBound {diagOne diagTwo offOneTwo partOne partTwo : ℝ}
    (hone : 0 ≤ diagOne) (htwo : 0 ≤ diagTwo) (hminor : offOneTwo ^ 2 ≤ diagOne * diagTwo) :
    2 * offOneTwo * partOne * partTwo ≤ diagOne * partTwo ^ 2 + diagTwo * partOne ^ 2 := by
  have htotal : 0 ≤ diagOne * partTwo ^ 2 + diagTwo * partOne ^ 2 := by positivity
  have hsquare : (2 * offOneTwo * partOne * partTwo) ^ 2
      ≤ (diagOne * partTwo ^ 2 + diagTwo * partOne ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (diagOne * partTwo ^ 2 - diagTwo * partOne ^ 2),
      mul_nonneg (sub_nonneg.2 hminor) (sq_nonneg (partOne * partTwo))]
  nlinarith [hsquare, htotal]

/-- **THE TRACE DOMINATES.**  A symmetric block of order three whose diagonal is
not negative and whose three two-by-two minors are not negative obeys
`B ≤ (trace B) * I`.

The identity behind it is

  `trace * (v . v) - (v . B v)
     = ∑ over the three pairs of (d i * v j ^ 2 + d j * v i ^ 2 - 2 * o i j * v i * v j)`,

and each of the three brackets is not negative by `Gtz.atomSymPairBound`. -/
theorem atomSymTraceDominates {diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree : ℝ}
    (hone : 0 ≤ diagOne) (htwo : 0 ≤ diagTwo) (hthree : 0 ≤ diagThree)
    (hminorOneTwo : offOneTwo ^ 2 ≤ diagOne * diagTwo)
    (hminorOneThree : offOneThree ^ 2 ≤ diagOne * diagThree)
    (hminorTwoThree : offTwoThree ^ 2 ≤ diagTwo * diagThree)
    (partOne partTwo partThree : ℝ) :
    atomSymQuad diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree
        partOne partTwo partThree
      ≤ atomSymTrace diagOne diagTwo diagThree
        * (partOne ^ 2 + partTwo ^ 2 + partThree ^ 2) := by
  have hpairOneTwo := atomSymPairBound hone htwo hminorOneTwo (partOne := partOne)
    (partTwo := partTwo)
  have hpairOneThree := atomSymPairBound hone hthree hminorOneThree (partOne := partOne)
    (partTwo := partThree)
  have hpairTwoThree := atomSymPairBound htwo hthree hminorTwoThree (partOne := partTwo)
    (partTwo := partThree)
  simp only [atomSymQuad, atomSymTrace]
  linarith [hpairOneTwo, hpairOneThree, hpairTwoThree]

/-- **THE WEDGE STEP FOR AN ABSTRACT BLOCK.**  A symmetric block of order three
whose diagonal is not negative and whose three two-by-two minors are not
negative obeys `e3 * (v . v) ≤ e2 * (v . B v)`.

The campaign proves this for the Gram block of a frame through the three wedges
of the three atoms.  Here it is proved for ANY such block, which is what lets it
be applied a second time to a SHIFTED block. -/
theorem atomSymWedge {diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree : ℝ}
    (hone : 0 ≤ diagOne) (htwo : 0 ≤ diagTwo) (hthree : 0 ≤ diagThree)
    (hminorOneTwo : offOneTwo ^ 2 ≤ diagOne * diagTwo)
    (hminorOneThree : offOneThree ^ 2 ≤ diagOne * diagThree)
    (hminorTwoThree : offTwoThree ^ 2 ≤ diagTwo * diagThree)
    (partOne partTwo partThree : ℝ) :
    atomSymDet diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree
        * (partOne ^ 2 + partTwo ^ 2 + partThree ^ 2)
      ≤ atomSymSecond diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree
        * atomSymQuad diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree
            partOne partTwo partThree := by
  have hcayley := atomSymCayley diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree
    partOne partTwo partThree
  have hdom := atomSymTraceDominates hone htwo hthree hminorOneTwo hminorOneThree hminorTwoThree
    (atomSymPushOne diagOne offOneTwo offOneThree partOne partTwo partThree)
    (atomSymPushTwo diagTwo offOneTwo offTwoThree partOne partTwo partThree)
    (atomSymPushThree diagThree offOneThree offTwoThree partOne partTwo partThree)
  linarith

/-! ## Layer 1 — the shifted block of a triple -/

/-- The Gram reading of a blend against itself. -/
theorem atomSlotBlend_dot_self (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6)
    (weightOne weightTwo weightThree : ℝ) :
    atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree
        ⬝ᵥ atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree
      = atomSymQuad (atomGram atom slotOne slotOne) (atomGram atom slotTwo slotTwo)
          (atomGram atom slotThree slotThree) (atomGram atom slotOne slotTwo)
          (atomGram atom slotOne slotThree) (atomGram atom slotTwo slotThree)
          weightOne weightTwo weightThree := by
  simp only [atomSlotBlend, atomGram, atomSymQuad, dotProduct, Fin.sum_univ_three]
  ring

/-- **EVERY TRIPLE CARRIES THE FLOOR ZERO.**  The iteration always starts. -/
theorem atomBlendFloor_zero (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) : AtomBlendFloor atom slotOne slotTwo slotThree 0 := by
  intro weightOne weightTwo weightThree
  simpa using atomDot_self_nonneg
    (atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree)

/-- A floor caps every diagonal reading of the block from below. -/
theorem atomBlendFloor_le_diag {atom : Fin 6 → (Fin 3 → ℝ)}
    {slotOne slotTwo slotThree : Fin 6} {floor : ℝ}
    (hfloor : AtomBlendFloor atom slotOne slotTwo slotThree floor) :
    floor ≤ atomGram atom slotOne slotOne ∧ floor ≤ atomGram atom slotTwo slotTwo
      ∧ floor ≤ atomGram atom slotThree slotThree := by
  refine ⟨?_, ?_, ?_⟩
  · have h := hfloor 1 0 0
    rw [atomSlotBlend_dot_self] at h
    simp only [atomSymQuad] at h
    linarith
  · have h := hfloor 0 1 0
    rw [atomSlotBlend_dot_self] at h
    simp only [atomSymQuad] at h
    linarith
  · have h := hfloor 0 0 1
    rw [atomSlotBlend_dot_self] at h
    simp only [atomSymQuad] at h
    linarith

/-- **THE TWO-BY-TWO MINORS OF THE SHIFTED BLOCK.**  A floor makes every
two-by-two minor of the shifted block not negative.  The proof reads the floor on
a two-slot family and takes the discriminant. -/
theorem atomBlendFloor_minor {atom : Fin 6 → (Fin 3 → ℝ)}
    {slotOne slotTwo slotThree : Fin 6} {floor : ℝ}
    (hfloor : AtomBlendFloor atom slotOne slotTwo slotThree floor) :
    atomGram atom slotOne slotTwo ^ 2
        ≤ (atomGram atom slotOne slotOne - floor) * (atomGram atom slotTwo slotTwo - floor)
      ∧ atomGram atom slotOne slotThree ^ 2
        ≤ (atomGram atom slotOne slotOne - floor) * (atomGram atom slotThree slotThree - floor)
      ∧ atomGram atom slotTwo slotThree ^ 2
        ≤ (atomGram atom slotTwo slotTwo - floor) * (atomGram atom slotThree slotThree - floor) := by
  refine ⟨?_, ?_, ?_⟩
  · have hquad : ∀ probe : ℝ,
        0 ≤ (atomGram atom slotOne slotOne - floor) * (probe * probe)
          + 2 * atomGram atom slotOne slotTwo * probe
          + (atomGram atom slotTwo slotTwo - floor) := by
      intro probe
      have h := hfloor probe 1 0
      rw [atomSlotBlend_dot_self] at h
      simp only [atomSymQuad] at h
      nlinarith [h]
    have hdisc := discrim_le_zero hquad
    simp only [discrim] at hdisc
    nlinarith [hdisc]
  · have hquad : ∀ probe : ℝ,
        0 ≤ (atomGram atom slotOne slotOne - floor) * (probe * probe)
          + 2 * atomGram atom slotOne slotThree * probe
          + (atomGram atom slotThree slotThree - floor) := by
      intro probe
      have h := hfloor probe 0 1
      rw [atomSlotBlend_dot_self] at h
      simp only [atomSymQuad] at h
      nlinarith [h]
    have hdisc := discrim_le_zero hquad
    simp only [discrim] at hdisc
    nlinarith [hdisc]
  · have hquad : ∀ probe : ℝ,
        0 ≤ (atomGram atom slotTwo slotTwo - floor) * (probe * probe)
          + 2 * atomGram atom slotTwo slotThree * probe
          + (atomGram atom slotThree slotThree - floor) := by
      intro probe
      have h := hfloor 0 probe 1
      rw [atomSlotBlend_dot_self] at h
      simp only [atomSymQuad] at h
      nlinarith [h]
    have hdisc := discrim_le_zero hquad
    simp only [discrim] at hdisc
    nlinarith [hdisc]

/-- The SECOND MINOR TOTAL of the shifted block of a triple. -/
def atomShiftSecond (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6)
    (shift : ℝ) : ℝ :=
  atomSymSecond (atomGram atom slotOne slotOne - shift) (atomGram atom slotTwo slotTwo - shift)
    (atomGram atom slotThree slotThree - shift) (atomGram atom slotOne slotTwo)
    (atomGram atom slotOne slotThree) (atomGram atom slotTwo slotThree)

/-- The DETERMINANT of the shifted block of a triple. -/
def atomShiftDet (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6)
    (shift : ℝ) : ℝ :=
  atomSymDet (atomGram atom slotOne slotOne - shift) (atomGram atom slotTwo slotTwo - shift)
    (atomGram atom slotThree slotThree - shift) (atomGram atom slotOne slotTwo)
    (atomGram atom slotOne slotThree) (atomGram atom slotTwo slotThree)

/-- **THE SHIFTED WEDGE STEP.**  The new floor a triple carries after one step. -/
noncomputable def atomShiftedWedgeStep (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) (shift : ℝ) : ℝ :=
  shift + atomShiftDet atom slotOne slotTwo slotThree shift
    / atomShiftSecond atom slotOne slotTwo slotThree shift

/-- The first step, from the floor zero, is exactly the landed wedge step. -/
theorem atomShiftedWedgeStep_zero (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) :
    atomShiftedWedgeStep atom slotOne slotTwo slotThree 0
      = atomBlockDet atom slotOne slotTwo slotThree
        / atomBlockSecond atom slotOne slotTwo slotThree := by
  simp only [atomShiftedWedgeStep, atomShiftDet, atomShiftSecond, atomSymDet, atomSymSecond,
    atomBlockDet, atomBlockSecond, sub_zero, zero_add]

/-- **THE SHIFTED WEDGE.**  A triple that already carries a floor carries the
next floor of the family.

Iterating from `Gtz.atomBlendFloor_zero` gives `e3 / e2` first, which is the
landed wedge step, and then Newton's method on the characteristic polynomial.
The step is available at EVERY leverage: it reads the block of one triple and
nothing else. -/
theorem atomBlendFloor_shift {atom : Fin 6 → (Fin 3 → ℝ)}
    {slotOne slotTwo slotThree : Fin 6} {shift : ℝ}
    (hfloor : AtomBlendFloor atom slotOne slotTwo slotThree shift)
    (hpos : 0 < atomShiftSecond atom slotOne slotTwo slotThree shift) :
    AtomBlendFloor atom slotOne slotTwo slotThree
      (atomShiftedWedgeStep atom slotOne slotTwo slotThree shift) := by
  obtain ⟨hdiagOne, hdiagTwo, hdiagThree⟩ := atomBlendFloor_le_diag hfloor
  obtain ⟨hminorOneTwo, hminorOneThree, hminorTwoThree⟩ := atomBlendFloor_minor hfloor
  intro weightOne weightTwo weightThree
  have hwedge := atomSymWedge (diagOne := atomGram atom slotOne slotOne - shift)
    (diagTwo := atomGram atom slotTwo slotTwo - shift)
    (diagThree := atomGram atom slotThree slotThree - shift)
    (offOneTwo := atomGram atom slotOne slotTwo)
    (offOneThree := atomGram atom slotOne slotThree)
    (offTwoThree := atomGram atom slotTwo slotThree)
    (by linarith) (by linarith) (by linarith)
    hminorOneTwo hminorOneThree hminorTwoThree weightOne weightTwo weightThree
  have hshape : atomSymQuad (atomGram atom slotOne slotOne - shift)
      (atomGram atom slotTwo slotTwo - shift) (atomGram atom slotThree slotThree - shift)
      (atomGram atom slotOne slotTwo) (atomGram atom slotOne slotThree)
      (atomGram atom slotTwo slotThree) weightOne weightTwo weightThree
      = (atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree
          ⬝ᵥ atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree)
        - shift * (weightOne ^ 2 + weightTwo ^ 2 + weightThree ^ 2) := by
    rw [atomSlotBlend_dot_self]
    simp only [atomSymQuad]
    ring
  rw [hshape] at hwedge
  have hstep : atomShiftDet atom slotOne slotTwo slotThree shift
        / atomShiftSecond atom slotOne slotTwo slotThree shift
        * (weightOne ^ 2 + weightTwo ^ 2 + weightThree ^ 2)
      ≤ (atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree
          ⬝ᵥ atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree)
        - shift * (weightOne ^ 2 + weightTwo ^ 2 + weightThree ^ 2) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    simp only [atomShiftDet, atomShiftSecond]
    nlinarith [hwedge]
  simp only [atomShiftedWedgeStep, add_mul]
  linarith

/-! ## Layer 2 — the step is strictly better than the wedge -/

/-- **THE EXTREMAL SPECTRUM, IN SYMMETRIC COORDINATES.**  The winning triple of
the exact real extremal of the spectral value carries the spectrum
`(1/6, 16/21, 1)`.  Its three symmetric functions are the readings below, and a
diagonal block with the same three readings is the cheapest witness of them. -/
theorem atomExtremalSpectrum :
    atomSymTrace (1 / 6) (16 / 21) 1 = 27 / 14
      ∧ atomSymSecond (1 / 6) (16 / 21) 1 0 0 0 = 133 / 126
      ∧ atomSymDet (1 / 6) (16 / 21) 1 0 0 0 = 16 / 126 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [atomSymTrace, atomSymSecond, atomSymDet] <;> norm_num

/-- **ONE SHIFTED STEP PASSES THE FIELD-AGNOSTIC CEILING.**  At the extremal
spectrum the landed wedge reads `16 / 133 = 0.120301`, which is BELOW the
Hermitian value `(3 - sqrt 5) / 6 = 0.127322` of the cell.  One shifted step
reads `4342960 / 26888743 = 0.161516`, which is ABOVE it, and the truth is
`1 / 6 = 0.166667`. -/
theorem atomShiftedWedge_passes_ceiling :
    (16 : ℝ) / 133 < (3 - Real.sqrt 5) / 6
      ∧ (3 - Real.sqrt 5) / 6 < 4342960 / 26888743
      ∧ (4342960 : ℝ) / 26888743 < 1 / 6 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  refine ⟨?_, ?_, by norm_num⟩
  · nlinarith [hsq, hnn]
  · nlinarith [hsq, hnn]

end Gtz
