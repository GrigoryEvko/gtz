import Mathlib
import Gtz.Wave.PentagonFloorReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12800000

/-!
# The pentagon floor is a theorem, and the tenth is unconditional

`Gtz.Wave.PentagonFloorReduction` shows that the gap of `Gtz.AtomPluckerTenth` is
the exact total of six local pentagon readings, and it leaves ONE residue:
`Gtz.AtomPentagonFloor`, a polynomial inequality in fifteen free real numbers.

This module PROVES that residue.  `Gtz.atomPentagonFloor` is the theorem, and it
gives:

* `Gtz.atomPluckerTenth` — `E2 ≤ 10 * E3` for every real rank-three Parseval
  frame of six atoms, with no leverage hypothesis
* `Gtz.atomPluckerTenthUnbalanced` — the leverage residue of
  `Gtz.Wave.PluckerSchurFloor`, closed
* `Gtz.atomSpectralSupply_tenth` — `Gtz.AtomSpectralSupply (1 / 10)`, the
  unconditional spectral floor of the deciding cell
* `Gtz.exists_atomCarrier_tenth` — the carrier form that the cell consumes
* `Gtz.atomPluckerEnergyThree_ge` — the level-three energy is at least `3 / 50`
  plus a tenth of the leverage spread.

## The chain

FIVE VECTORS OF RANK THREE carry a two-dimensional space of linear dependencies.
The pentagon reading of the five vectors is the same polynomial as the pentagon
reading of the ten two-slot minors of that dependency plane, up to one global
factor.  So the residue is a statement about a PLANE, which is rank two.

* `Gtz.atomVolumePluckerMid` and `Gtz.atomVolumePluckerLeft` are two more
  Grassmann-Plucker relations.  Each is a `ring` identity.
* `Gtz.atomPentagonMargin_baseSquare` uses them.  It identifies the ten minors of
  the dependency plane with the volume of the base triple times the volume of the
  COMPLEMENTARY triple, and it gives `volume ^ 4 * margin ≥ 0` with no hypothesis.
* `Gtz.atomDualPlaneFloor` is the floor on the dependency plane.  It replaces the
  spanning pair by an ORTHOGONAL pair of EQUAL length, which costs one square
  root, and then spends the core.
* `Gtz.atomPlanarQuintetFloor` is the core.
* `Gtz.atomPentagonMargin_permOneThree` and its eight siblings say that the
  margin does not read the order of the five slots, so any triple of non-zero
  volume can play the base.  If every triple volume is zero, the margin is zero.

## The core, in one paragraph

Five slots carry three readings each, `n a`, `u a`, `v a`, with the two totals of
`u` and of `v` zero and `u a ^ 2 + v a ^ 2 = n a ^ 2`.  Read `(u a, v a)` as a
planar vector `z a` of length `|n a|`.  Three quantities carry the proof:

* `T` — the total of `n a ^ 2`, which is the trace of `A`, the total of
  `z a z a ^ T`
* `V` — the planar vector `the total of n a * z a`
* `de` — the gap between the two eigenvalues of `A`.

With `q a b = (n a * n b - u a * u b - v a * v b) / 2` the reading identity is

  `16 * (the total of q ^ 2) = 3 * T ^ 2 - 4 * |V| ^ 2 + de ^ 2`,

and the target becomes `4 * |V| ^ 2 ≤ (3/5) * T * Q + de ^ 2` with
`Q = 5 * T - R ^ 2` and `R` the total of `n a`.  The two totals vanish, so `V` is
also `the total of (n a - R/5) * z a`.  Cauchy-Schwarz over five slots
(`Gtz.atomFiveCauchy`) and the two-by-two operator bound
(`Gtz.atomPlanarOperatorBound`) give

  `|V| ^ 2 ≤ (Q / 10) * (T + de)`.

The rest is one quadratic in `de`:

  `5 * de ^ 2 - 2 * Q * de + T * Q = 5 * (de - Q/5) ^ 2 + Q * R ^ 2 / 5 ≥ 0`

(`Gtz.atomPlanarGapSquare`).  Both terms are squares and `Q` is a total of ten
squares, so the core closes.

## Where the realness enters

The chain is real-only through `Gtz.atomVolumePlucker` and its two siblings.
Over the real field a triple volume is a real number, so the three-term relation
lets the three products of block determinants be compared through their squares.
Over the Hermitian field `Gtz.atomComplexTriple_defect` measures exactly what is
lost.  The Hermitian value of the deciding cell is `1 / (3 * phi ^ 2)`, which is
`0.127322` and is past one tenth, so no field-agnostic argument can carry this
floor.

## Sharpness

`Gtz.atomPentagonReading_pentagon` gives the equality case.  The five large
readings are `5 + sqrt 5` and the five small ones are `5 - sqrt 5`, in the
pentagon pattern.  The five-atom sub-configurations of the icosahedral frame
realise them, and the icosahedral frame attains `E2 = 10 * E3`.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

Every statement below is proved, and no statement below carries a named
hypothesis.
-/
namespace Gtz

/-! ## Layer 0 — two elementary steps -/

/-- **CAUCHY-SCHWARZ OVER FIVE SLOTS.**  The Lagrange identity supplies the ten
squares. -/
theorem atomFiveCauchy (leftOne leftTwo leftThree leftFour leftFive
    rightOne rightTwo rightThree rightFour rightFive : ℝ) :
    (leftOne * rightOne + leftTwo * rightTwo + leftThree * rightThree
        + leftFour * rightFour + leftFive * rightFive) ^ 2
      ≤ (leftOne ^ 2 + leftTwo ^ 2 + leftThree ^ 2 + leftFour ^ 2 + leftFive ^ 2)
        * (rightOne ^ 2 + rightTwo ^ 2 + rightThree ^ 2 + rightFour ^ 2 + rightFive ^ 2) := by
  nlinarith [sq_nonneg (leftOne * rightTwo - leftTwo * rightOne),
    sq_nonneg (leftOne * rightThree - leftThree * rightOne),
    sq_nonneg (leftOne * rightFour - leftFour * rightOne),
    sq_nonneg (leftOne * rightFive - leftFive * rightOne),
    sq_nonneg (leftTwo * rightThree - leftThree * rightTwo),
    sq_nonneg (leftTwo * rightFour - leftFour * rightTwo),
    sq_nonneg (leftTwo * rightFive - leftFive * rightTwo),
    sq_nonneg (leftThree * rightFour - leftFour * rightThree),
    sq_nonneg (leftThree * rightFive - leftFive * rightThree),
    sq_nonneg (leftFour * rightFive - leftFive * rightFour)]

/-- **THE TWO-BY-TWO OPERATOR BOUND.**  A symmetric block of order two with
trace `trace` and eigenvalue gap `gap` never reads more than
`(trace + gap) / 2` times the squared length of a probe.

The proof is one Cauchy-Schwarz step in the plane: the traceless part of the
block pairs against `(probeOne ^ 2 - probeTwo ^ 2, 2 * probeOne * probeTwo)`,
whose length is the squared length of the probe. -/
theorem atomPlanarOperatorBound {entryOne entryCross entryTwo trace gap : ℝ}
    (htrace : entryOne + entryTwo = trace) (hgap : 0 ≤ gap)
    (hgapSq : gap ^ 2 = (entryOne - entryTwo) ^ 2 + 4 * entryCross ^ 2)
    (probeOne probeTwo : ℝ) :
    entryOne * probeOne ^ 2 + 2 * entryCross * probeOne * probeTwo
        + entryTwo * probeTwo ^ 2
      ≤ (trace + gap) / 2 * (probeOne ^ 2 + probeTwo ^ 2) := by
  subst htrace
  have hlen : (0:ℝ) ≤ probeOne ^ 2 + probeTwo ^ 2 := by positivity
  have hcs : ((entryOne - entryTwo) * (probeOne ^ 2 - probeTwo ^ 2)
        + 4 * entryCross * probeOne * probeTwo) ^ 2
      ≤ (gap * (probeOne ^ 2 + probeTwo ^ 2)) ^ 2 := by
    have hlag : (gap * (probeOne ^ 2 + probeTwo ^ 2)) ^ 2
        - ((entryOne - entryTwo) * (probeOne ^ 2 - probeTwo ^ 2)
          + 4 * entryCross * probeOne * probeTwo) ^ 2
        = ((entryOne - entryTwo) * (2 * probeOne * probeTwo)
            - 2 * entryCross * (probeOne ^ 2 - probeTwo ^ 2)) ^ 2 := by
      rw [mul_pow, hgapSq]; ring
    linarith [hlag, sq_nonneg ((entryOne - entryTwo) * (2 * probeOne * probeTwo)
      - 2 * entryCross * (probeOne ^ 2 - probeTwo ^ 2))]
  have hprod : (0:ℝ) ≤ gap * (probeOne ^ 2 + probeTwo ^ 2) := mul_nonneg hgap hlen
  have hlin : (entryOne - entryTwo) * (probeOne ^ 2 - probeTwo ^ 2)
      + 4 * entryCross * probeOne * probeTwo
      ≤ gap * (probeOne ^ 2 + probeTwo ^ 2) := by nlinarith [hcs, hprod]
  linarith [hlin]

/-- **THE GAP SQUARE.**  The quadratic in the eigenvalue gap that closes the
core is a total of two squares.  It uses `Q = 5 * T - R ^ 2` and nothing else. -/
theorem atomPlanarGapSquare (gap spread trace total : ℝ)
    (hspread : spread = 5 * trace - total ^ 2) (hnn : 0 ≤ spread) :
    0 ≤ 5 * gap ^ 2 - 2 * spread * gap + trace * spread := by
  have hsplit : 5 * gap ^ 2 - 2 * spread * gap + trace * spread
      = 5 * (gap - spread / 5) ^ 2 + spread * total ^ 2 / 5 := by
    rw [hspread]; ring
  rw [hsplit]
  have : (0:ℝ) ≤ spread * total ^ 2 / 5 := by positivity
  nlinarith [sq_nonneg (gap - spread / 5)]

/-! ## Layer 1 — the planar quintet floor -/

/-- **THE PLANAR QUINTET FLOOR.**  The algebraic core of the pentagon floor.

Five slots carry three readings each.  The two totals of `u` and of `v` vanish,
and each slot obeys `u ^ 2 + v ^ 2 = n ^ 2`.  With
`q a b = (n a * n b - u a * u b - v a * v b) / 2` and `star a` the total of
`q a b` over the four other slots,

  `3 * (the total of star ^ 2) ≤ 20 * (the total over the ten pairs of q ^ 2)`.

The bound is sharp at the regular pentagon, where `n` is constant and the five
planar readings `(u a, v a)` point at the five fifth roots of one. -/
theorem atomPlanarQuintetFloor
    (nOne nTwo nThree nFour nFive uOne uTwo uThree uFour uFive
      vOne vTwo vThree vFour vFive : ℝ)
    (qOneTwo qOneThree qOneFour qOneFive qTwoThree qTwoFour qTwoFive
      qThreeFour qThreeFive qFourFive : ℝ)
    (hqOneTwo : qOneTwo = (nOne * nTwo - uOne * uTwo - vOne * vTwo) / 2)
    (hqOneThree : qOneThree = (nOne * nThree - uOne * uThree - vOne * vThree) / 2)
    (hqOneFour : qOneFour = (nOne * nFour - uOne * uFour - vOne * vFour) / 2)
    (hqOneFive : qOneFive = (nOne * nFive - uOne * uFive - vOne * vFive) / 2)
    (hqTwoThree : qTwoThree = (nTwo * nThree - uTwo * uThree - vTwo * vThree) / 2)
    (hqTwoFour : qTwoFour = (nTwo * nFour - uTwo * uFour - vTwo * vFour) / 2)
    (hqTwoFive : qTwoFive = (nTwo * nFive - uTwo * uFive - vTwo * vFive) / 2)
    (hqThreeFour : qThreeFour = (nThree * nFour - uThree * uFour - vThree * vFour) / 2)
    (hqThreeFive : qThreeFive = (nThree * nFive - uThree * uFive - vThree * vFive) / 2)
    (hqFourFive : qFourFive = (nFour * nFive - uFour * uFive - vFour * vFive) / 2)
    (huSum : uOne + uTwo + uThree + uFour + uFive = 0)
    (hvSum : vOne + vTwo + vThree + vFour + vFive = 0)
    (hSlotOne : uOne ^ 2 + vOne ^ 2 = nOne ^ 2)
    (hSlotTwo : uTwo ^ 2 + vTwo ^ 2 = nTwo ^ 2)
    (hSlotThree : uThree ^ 2 + vThree ^ 2 = nThree ^ 2)
    (hSlotFour : uFour ^ 2 + vFour ^ 2 = nFour ^ 2)
    (hSlotFive : uFive ^ 2 + vFive ^ 2 = nFive ^ 2) :
    3 * ((qOneTwo + qOneThree + qOneFour + qOneFive) ^ 2
        + (qOneTwo + qTwoThree + qTwoFour + qTwoFive) ^ 2
        + (qOneThree + qTwoThree + qThreeFour + qThreeFive) ^ 2
        + (qOneFour + qTwoFour + qThreeFour + qFourFive) ^ 2
        + (qOneFive + qTwoFive + qThreeFive + qFourFive) ^ 2)
      ≤ 20 * (qOneTwo ^ 2 + qOneThree ^ 2 + qOneFour ^ 2 + qOneFive ^ 2 + qTwoThree ^ 2
        + qTwoFour ^ 2 + qTwoFive ^ 2 + qThreeFour ^ 2 + qThreeFive ^ 2 + qFourFive ^ 2) := by
  -- the six derived readings
  obtain ⟨trc, htrc⟩ : ∃ t : ℝ,
      t = nOne ^ 2 + nTwo ^ 2 + nThree ^ 2 + nFour ^ 2 + nFive ^ 2 := ⟨_, rfl⟩
  obtain ⟨tot, htot⟩ : ∃ t : ℝ, t = nOne + nTwo + nThree + nFour + nFive := ⟨_, rfl⟩
  obtain ⟨spr, hspr⟩ : ∃ t : ℝ, t = 5 * trc - tot ^ 2 := ⟨_, rfl⟩
  obtain ⟨entOne, hentOne⟩ : ∃ t : ℝ,
      t = uOne ^ 2 + uTwo ^ 2 + uThree ^ 2 + uFour ^ 2 + uFive ^ 2 := ⟨_, rfl⟩
  obtain ⟨entTwo, hentTwo⟩ : ∃ t : ℝ,
      t = vOne ^ 2 + vTwo ^ 2 + vThree ^ 2 + vFour ^ 2 + vFive ^ 2 := ⟨_, rfl⟩
  obtain ⟨entCross, hentCross⟩ : ∃ t : ℝ,
      t = uOne * vOne + uTwo * vTwo + uThree * vThree + uFour * vFour + uFive * vFive :=
    ⟨_, rfl⟩
  obtain ⟨velOne, hvelOne⟩ : ∃ t : ℝ,
      t = nOne * uOne + nTwo * uTwo + nThree * uThree + nFour * uFour + nFive * uFive :=
    ⟨_, rfl⟩
  obtain ⟨velTwo, hvelTwo⟩ : ∃ t : ℝ,
      t = nOne * vOne + nTwo * vTwo + nThree * vThree + nFour * vFour + nFive * vFive :=
    ⟨_, rfl⟩
  set gap : ℝ := Real.sqrt ((entOne - entTwo) ^ 2 + 4 * entCross ^ 2) with hgapDef
  have hgapNn : 0 ≤ gap := Real.sqrt_nonneg _
  have hgapSq : gap ^ 2 = (entOne - entTwo) ^ 2 + 4 * entCross ^ 2 := by
    rw [hgapDef]; exact Real.sq_sqrt (by positivity)
  -- the spread is a total of ten squares
  have hsprNn : 0 ≤ spr := by
    rw [hspr, htrc, htot]
    nlinarith [sq_nonneg (nOne - nTwo), sq_nonneg (nOne - nThree), sq_nonneg (nOne - nFour),
      sq_nonneg (nOne - nFive), sq_nonneg (nTwo - nThree), sq_nonneg (nTwo - nFour),
      sq_nonneg (nTwo - nFive), sq_nonneg (nThree - nFour), sq_nonneg (nThree - nFive),
      sq_nonneg (nFour - nFive)]
  have htrcNn : 0 ≤ trc := by rw [htrc]; positivity
  -- the trace of the planar block
  have hentSum : entOne + entTwo = trc := by
    rw [hentOne, hentTwo, htrc]
    linarith [hSlotOne, hSlotTwo, hSlotThree, hSlotFour, hSlotFive]
  -- Cauchy-Schwarz over the five slots
  have hcauchy := atomFiveCauchy (nOne - tot / 5) (nTwo - tot / 5) (nThree - tot / 5)
    (nFour - tot / 5) (nFive - tot / 5)
    (uOne * velOne + vOne * velTwo) (uTwo * velOne + vTwo * velTwo)
    (uThree * velOne + vThree * velTwo) (uFour * velOne + vFour * velTwo)
    (uFive * velOne + vFive * velTwo)
  have hleftSum : (nOne - tot / 5) * (uOne * velOne + vOne * velTwo)
      + (nTwo - tot / 5) * (uTwo * velOne + vTwo * velTwo)
      + (nThree - tot / 5) * (uThree * velOne + vThree * velTwo)
      + (nFour - tot / 5) * (uFour * velOne + vFour * velTwo)
      + (nFive - tot / 5) * (uFive * velOne + vFive * velTwo)
      = velOne ^ 2 + velTwo ^ 2 := by
    rw [hvelOne, hvelTwo]
    linear_combination (-(tot / 5) * (nOne * uOne + nTwo * uTwo + nThree * uThree
        + nFour * uFour + nFive * uFive)) * huSum
      + (-(tot / 5) * (nOne * vOne + nTwo * vTwo + nThree * vThree + nFour * vFour
        + nFive * vFive)) * hvSum
  have hleftNorm : (nOne - tot / 5) ^ 2 + (nTwo - tot / 5) ^ 2 + (nThree - tot / 5) ^ 2
      + (nFour - tot / 5) ^ 2 + (nFive - tot / 5) ^ 2 = spr / 5 := by
    rw [hspr, htrc, htot]; ring
  have hrightNorm : (uOne * velOne + vOne * velTwo) ^ 2 + (uTwo * velOne + vTwo * velTwo) ^ 2
      + (uThree * velOne + vThree * velTwo) ^ 2 + (uFour * velOne + vFour * velTwo) ^ 2
      + (uFive * velOne + vFive * velTwo) ^ 2
      = entOne * velOne ^ 2 + 2 * entCross * velOne * velTwo + entTwo * velTwo ^ 2 := by
    rw [hentOne, hentTwo, hentCross]; ring
  rw [hleftSum, hleftNorm, hrightNorm] at hcauchy
  -- the operator bound of the planar block
  have hoper := atomPlanarOperatorBound hentSum hgapNn hgapSq velOne velTwo
  -- the vector bound
  have hvel : velOne ^ 2 + velTwo ^ 2 ≤ spr / 10 * (trc + gap) := by
    have hsq : (0:ℝ) ≤ velOne ^ 2 + velTwo ^ 2 := by positivity
    rcases eq_or_lt_of_le hsq with hzero | hpos
    · have hpos2 : (0:ℝ) ≤ spr * (trc + gap) :=
        mul_nonneg hsprNn (by linarith)
      linarith [hpos2]
    · have hstep : (velOne ^ 2 + velTwo ^ 2) ^ 2
          ≤ spr / 5 * ((trc + gap) / 2 * (velOne ^ 2 + velTwo ^ 2)) := by
        have := mul_le_mul_of_nonneg_left hoper (by positivity : (0:ℝ) ≤ spr / 5)
        linarith [hcauchy, this]
      nlinarith [hstep, hpos]
  -- the reading identity
  have hread : 16 * (qOneTwo ^ 2 + qOneThree ^ 2 + qOneFour ^ 2 + qOneFive ^ 2
      + qTwoThree ^ 2 + qTwoFour ^ 2 + qTwoFive ^ 2 + qThreeFour ^ 2 + qThreeFive ^ 2
      + qFourFive ^ 2)
      = 3 * trc ^ 2 - 4 * (velOne ^ 2 + velTwo ^ 2) + gap ^ 2 := by
    rw [hqOneTwo, hqOneThree, hqOneFour, hqOneFive, hqTwoThree, hqTwoFour, hqTwoFive,
      hqThreeFour, hqThreeFive, hqFourFive, htrc, hvelOne, hvelTwo, hgapSq, hentOne,
      hentTwo, hentCross]
    linear_combination
      (uOne ^ 2 + uTwo ^ 2 + uThree ^ 2 + uFour ^ 2 + uFive ^ 2
        + vOne ^ 2 + vTwo ^ 2 + vThree ^ 2 + vFour ^ 2 + vFive ^ 2
        + nOne ^ 2 + nTwo ^ 2 + nThree ^ 2 + nFour ^ 2 + nFive ^ 2
        - 2 * (uOne ^ 2 + vOne ^ 2 - nOne ^ 2)) * hSlotOne
      + (uOne ^ 2 + uTwo ^ 2 + uThree ^ 2 + uFour ^ 2 + uFive ^ 2
        + vOne ^ 2 + vTwo ^ 2 + vThree ^ 2 + vFour ^ 2 + vFive ^ 2
        + nOne ^ 2 + nTwo ^ 2 + nThree ^ 2 + nFour ^ 2 + nFive ^ 2
        - 2 * (uTwo ^ 2 + vTwo ^ 2 - nTwo ^ 2)) * hSlotTwo
      + (uOne ^ 2 + uTwo ^ 2 + uThree ^ 2 + uFour ^ 2 + uFive ^ 2
        + vOne ^ 2 + vTwo ^ 2 + vThree ^ 2 + vFour ^ 2 + vFive ^ 2
        + nOne ^ 2 + nTwo ^ 2 + nThree ^ 2 + nFour ^ 2 + nFive ^ 2
        - 2 * (uThree ^ 2 + vThree ^ 2 - nThree ^ 2)) * hSlotThree
      + (uOne ^ 2 + uTwo ^ 2 + uThree ^ 2 + uFour ^ 2 + uFive ^ 2
        + vOne ^ 2 + vTwo ^ 2 + vThree ^ 2 + vFour ^ 2 + vFive ^ 2
        + nOne ^ 2 + nTwo ^ 2 + nThree ^ 2 + nFour ^ 2 + nFive ^ 2
        - 2 * (uFour ^ 2 + vFour ^ 2 - nFour ^ 2)) * hSlotFour
      + (uOne ^ 2 + uTwo ^ 2 + uThree ^ 2 + uFour ^ 2 + uFive ^ 2
        + vOne ^ 2 + vTwo ^ 2 + vThree ^ 2 + vFour ^ 2 + vFive ^ 2
        + nOne ^ 2 + nTwo ^ 2 + nThree ^ 2 + nFour ^ 2 + nFive ^ 2
        - 2 * (uFive ^ 2 + vFive ^ 2 - nFive ^ 2)) * hSlotFive
  -- the star identities
  have hstarOne : qOneTwo + qOneThree + qOneFour + qOneFive = nOne * tot / 2 := by
    rw [hqOneTwo, hqOneThree, hqOneFour, hqOneFive, htot]
    linear_combination (-(uOne) / 2) * huSum + (-(vOne) / 2) * hvSum + (1 / 2) * hSlotOne
  have hstarTwo : qOneTwo + qTwoThree + qTwoFour + qTwoFive = nTwo * tot / 2 := by
    rw [hqOneTwo, hqTwoThree, hqTwoFour, hqTwoFive, htot]
    linear_combination (-(uTwo) / 2) * huSum + (-(vTwo) / 2) * hvSum + (1 / 2) * hSlotTwo
  have hstarThree : qOneThree + qTwoThree + qThreeFour + qThreeFive = nThree * tot / 2 := by
    rw [hqOneThree, hqTwoThree, hqThreeFour, hqThreeFive, htot]
    linear_combination (-(uThree) / 2) * huSum + (-(vThree) / 2) * hvSum + (1 / 2) * hSlotThree
  have hstarFour : qOneFour + qTwoFour + qThreeFour + qFourFive = nFour * tot / 2 := by
    rw [hqOneFour, hqTwoFour, hqThreeFour, hqFourFive, htot]
    linear_combination (-(uFour) / 2) * huSum + (-(vFour) / 2) * hvSum + (1 / 2) * hSlotFour
  have hstarFive : qOneFive + qTwoFive + qThreeFive + qFourFive = nFive * tot / 2 := by
    rw [hqOneFive, hqTwoFive, hqThreeFive, hqFourFive, htot]
    linear_combination (-(uFive) / 2) * huSum + (-(vFive) / 2) * hvSum + (1 / 2) * hSlotFive
  have hstarSum : (qOneTwo + qOneThree + qOneFour + qOneFive) ^ 2
      + (qOneTwo + qTwoThree + qTwoFour + qTwoFive) ^ 2
      + (qOneThree + qTwoThree + qThreeFour + qThreeFive) ^ 2
      + (qOneFour + qTwoFour + qThreeFour + qFourFive) ^ 2
      + (qOneFive + qTwoFive + qThreeFive + qFourFive) ^ 2
      = trc * tot ^ 2 / 4 := by
    rw [hstarOne, hstarTwo, hstarThree, hstarFour, hstarFive, htrc]; ring
  -- the gap square closes it
  have hquad := atomPlanarGapSquare gap spr trc tot hspr hsprNn
  have hkey : trc * tot ^ 2 = 5 * trc ^ 2 - trc * spr := by rw [hspr]; ring
  rw [hstarSum]
  linarith [hread, hvel, hquad, hkey]

/-! ## Layer 2 — the floor on the dual plane -/

/-- **THE DUAL PLANE FLOOR.**  Two vectors of the five-slot space carry ten
two-slot minors.  The squares of those minors obey the pentagon floor.

The two vectors span a plane, and the ten squared minors are the squared Plucker
coordinates of that plane.  The proof replaces the spanning pair by an ORTHOGONAL
pair of EQUAL length, which costs one square root, and then spends
`Gtz.atomPlanarQuintetFloor`. -/
theorem atomDualPlaneFloor
    (kOne kTwo kThree kFour kFive mOne mTwo mThree mFour mFive : ℝ)
    (wOneTwo wOneThree wOneFour wOneFive wTwoThree wTwoFour wTwoFive
      wThreeFour wThreeFive wFourFive : ℝ)
    (hwOneTwo : wOneTwo = (kOne * mTwo - kTwo * mOne) ^ 2)
    (hwOneThree : wOneThree = (kOne * mThree - kThree * mOne) ^ 2)
    (hwOneFour : wOneFour = (kOne * mFour - kFour * mOne) ^ 2)
    (hwOneFive : wOneFive = (kOne * mFive - kFive * mOne) ^ 2)
    (hwTwoThree : wTwoThree = (kTwo * mThree - kThree * mTwo) ^ 2)
    (hwTwoFour : wTwoFour = (kTwo * mFour - kFour * mTwo) ^ 2)
    (hwTwoFive : wTwoFive = (kTwo * mFive - kFive * mTwo) ^ 2)
    (hwThreeFour : wThreeFour = (kThree * mFour - kFour * mThree) ^ 2)
    (hwThreeFive : wThreeFive = (kThree * mFive - kFive * mThree) ^ 2)
    (hwFourFive : wFourFive = (kFour * mFive - kFive * mFour) ^ 2) :
    3 * ((wOneTwo + wOneThree + wOneFour + wOneFive) ^ 2
        + (wOneTwo + wTwoThree + wTwoFour + wTwoFive) ^ 2
        + (wOneThree + wTwoThree + wThreeFour + wThreeFive) ^ 2
        + (wOneFour + wTwoFour + wThreeFour + wFourFive) ^ 2
        + (wOneFive + wTwoFive + wThreeFive + wFourFive) ^ 2)
      ≤ 20 * (wOneTwo ^ 2 + wOneThree ^ 2 + wOneFour ^ 2 + wOneFive ^ 2 + wTwoThree ^ 2
        + wTwoFour ^ 2 + wTwoFive ^ 2 + wThreeFour ^ 2 + wThreeFive ^ 2 + wFourFive ^ 2) := by
  obtain ⟨lenK, hlenK⟩ : ∃ t : ℝ,
      t = kOne ^ 2 + kTwo ^ 2 + kThree ^ 2 + kFour ^ 2 + kFive ^ 2 := ⟨_, rfl⟩
  obtain ⟨lenM, hlenM⟩ : ∃ t : ℝ,
      t = mOne ^ 2 + mTwo ^ 2 + mThree ^ 2 + mFour ^ 2 + mFive ^ 2 := ⟨_, rfl⟩
  obtain ⟨cross, hcross⟩ : ∃ t : ℝ,
      t = kOne * mOne + kTwo * mTwo + kThree * mThree + kFour * mFour + kFive * mFive :=
    ⟨_, rfl⟩
  obtain ⟨area, harea⟩ : ∃ t : ℝ, t = lenK * lenM - cross ^ 2 := ⟨_, rfl⟩
  have hn12 : 0 ≤ wOneTwo := by rw [hwOneTwo]; positivity
  have hn13 : 0 ≤ wOneThree := by rw [hwOneThree]; positivity
  have hn14 : 0 ≤ wOneFour := by rw [hwOneFour]; positivity
  have hn15 : 0 ≤ wOneFive := by rw [hwOneFive]; positivity
  have hn23 : 0 ≤ wTwoThree := by rw [hwTwoThree]; positivity
  have hn24 : 0 ≤ wTwoFour := by rw [hwTwoFour]; positivity
  have hn25 : 0 ≤ wTwoFive := by rw [hwTwoFive]; positivity
  have hn34 : 0 ≤ wThreeFour := by rw [hwThreeFour]; positivity
  have hn35 : 0 ≤ wThreeFive := by rw [hwThreeFive]; positivity
  have hn45 : 0 ≤ wFourFive := by rw [hwFourFive]; positivity
  have hlag : area = wOneTwo + wOneThree + wOneFour + wOneFive + wTwoThree + wTwoFour
      + wTwoFive + wThreeFour + wThreeFive + wFourFive := by
    rw [harea, hlenK, hlenM, hcross, hwOneTwo, hwOneThree, hwOneFour, hwOneFive,
      hwTwoThree, hwTwoFour, hwTwoFive, hwThreeFour, hwThreeFive, hwFourFive]
    ring
  have hareaNn : 0 ≤ area := by rw [hlag]; linarith
  rcases eq_or_lt_of_le hareaNn with hzero | hpos
  · have e12 : wOneTwo = 0 := by linarith [hlag, hzero]
    have e13 : wOneThree = 0 := by linarith [hlag, hzero]
    have e14 : wOneFour = 0 := by linarith [hlag, hzero]
    have e15 : wOneFive = 0 := by linarith [hlag, hzero]
    have e23 : wTwoThree = 0 := by linarith [hlag, hzero]
    have e24 : wTwoFour = 0 := by linarith [hlag, hzero]
    have e25 : wTwoFive = 0 := by linarith [hlag, hzero]
    have e34 : wThreeFour = 0 := by linarith [hlag, hzero]
    have e35 : wThreeFive = 0 := by linarith [hlag, hzero]
    have e45 : wFourFive = 0 := by linarith [hlag, hzero]
    rw [e12, e13, e14, e15, e23, e24, e25, e34, e35, e45]
    norm_num
  · have hlenMnn : 0 ≤ lenM := by rw [hlenM]; positivity
    have hlenKnn : 0 ≤ lenK := by rw [hlenK]; positivity
    have hprodPos : 0 < lenK * lenM := by nlinarith [harea, hpos, sq_nonneg cross]
    have hlenMpos : 0 < lenM := by
      rcases lt_or_eq_of_le hlenMnn with hlt | heq
      · exact hlt
      · exfalso; rw [← heq, mul_zero] at hprodPos; exact lt_irrefl 0 hprodPos
    obtain ⟨root, hrootDef⟩ : ∃ t : ℝ, t = Real.sqrt area := ⟨_, rfl⟩
    have hrootSq : root ^ 2 = area := by
      rw [hrootDef]; exact Real.sq_sqrt (le_of_lt hpos)
    obtain ⟨kapOne, hkapOne⟩ : ∃ t : ℝ, t = lenM * kOne - cross * mOne := ⟨_, rfl⟩
    obtain ⟨kapTwo, hkapTwo⟩ : ∃ t : ℝ, t = lenM * kTwo - cross * mTwo := ⟨_, rfl⟩
    obtain ⟨kapThree, hkapThree⟩ : ∃ t : ℝ, t = lenM * kThree - cross * mThree := ⟨_, rfl⟩
    obtain ⟨kapFour, hkapFour⟩ : ∃ t : ℝ, t = lenM * kFour - cross * mFour := ⟨_, rfl⟩
    obtain ⟨kapFive, hkapFive⟩ : ∃ t : ℝ, t = lenM * kFive - cross * mFive := ⟨_, rfl⟩
    have hcore := atomPlanarQuintetFloor
      (kapOne ^ 2 + area * mOne ^ 2) (kapTwo ^ 2 + area * mTwo ^ 2)
      (kapThree ^ 2 + area * mThree ^ 2) (kapFour ^ 2 + area * mFour ^ 2)
      (kapFive ^ 2 + area * mFive ^ 2)
      (kapOne ^ 2 - area * mOne ^ 2) (kapTwo ^ 2 - area * mTwo ^ 2)
      (kapThree ^ 2 - area * mThree ^ 2) (kapFour ^ 2 - area * mFour ^ 2)
      (kapFive ^ 2 - area * mFive ^ 2)
      (2 * root * kapOne * mOne) (2 * root * kapTwo * mTwo) (2 * root * kapThree * mThree)
      (2 * root * kapFour * mFour) (2 * root * kapFive * mFive)
      (area * lenM ^ 2 * wOneTwo) (area * lenM ^ 2 * wOneThree) (area * lenM ^ 2 * wOneFour)
      (area * lenM ^ 2 * wOneFive) (area * lenM ^ 2 * wTwoThree) (area * lenM ^ 2 * wTwoFour)
      (area * lenM ^ 2 * wTwoFive) (area * lenM ^ 2 * wThreeFour)
      (area * lenM ^ 2 * wThreeFive) (area * lenM ^ 2 * wFourFive)
      (by rw [hwOneTwo, hkapOne, hkapTwo]
          linear_combination (2 * (lenM * kOne - cross * mOne) * (lenM * kTwo - cross * mTwo)
            * mOne * mTwo) * hrootSq)
      (by rw [hwOneThree, hkapOne, hkapThree]
          linear_combination (2 * (lenM * kOne - cross * mOne) * (lenM * kThree - cross * mThree)
            * mOne * mThree) * hrootSq)
      (by rw [hwOneFour, hkapOne, hkapFour]
          linear_combination (2 * (lenM * kOne - cross * mOne) * (lenM * kFour - cross * mFour)
            * mOne * mFour) * hrootSq)
      (by rw [hwOneFive, hkapOne, hkapFive]
          linear_combination (2 * (lenM * kOne - cross * mOne) * (lenM * kFive - cross * mFive)
            * mOne * mFive) * hrootSq)
      (by rw [hwTwoThree, hkapTwo, hkapThree]
          linear_combination (2 * (lenM * kTwo - cross * mTwo) * (lenM * kThree - cross * mThree)
            * mTwo * mThree) * hrootSq)
      (by rw [hwTwoFour, hkapTwo, hkapFour]
          linear_combination (2 * (lenM * kTwo - cross * mTwo) * (lenM * kFour - cross * mFour)
            * mTwo * mFour) * hrootSq)
      (by rw [hwTwoFive, hkapTwo, hkapFive]
          linear_combination (2 * (lenM * kTwo - cross * mTwo) * (lenM * kFive - cross * mFive)
            * mTwo * mFive) * hrootSq)
      (by rw [hwThreeFour, hkapThree, hkapFour]
          linear_combination (2 * (lenM * kThree - cross * mThree) * (lenM * kFour - cross * mFour)
            * mThree * mFour) * hrootSq)
      (by rw [hwThreeFive, hkapThree, hkapFive]
          linear_combination (2 * (lenM * kThree - cross * mThree) * (lenM * kFive - cross * mFive)
            * mThree * mFive) * hrootSq)
      (by rw [hwFourFive, hkapFour, hkapFive]
          linear_combination (2 * (lenM * kFour - cross * mFour) * (lenM * kFive - cross * mFive)
            * mFour * mFive) * hrootSq)
      (by rw [hkapOne, hkapTwo, hkapThree, hkapFour, hkapFive, harea, hlenK, hlenM, hcross]
          ring)
      (by rw [hkapOne, hkapTwo, hkapThree, hkapFour, hkapFive, hlenM, hcross]
          ring)
      (by linear_combination (4 * kapOne ^ 2 * mOne ^ 2) * hrootSq)
      (by linear_combination (4 * kapTwo ^ 2 * mTwo ^ 2) * hrootSq)
      (by linear_combination (4 * kapThree ^ 2 * mThree ^ 2) * hrootSq)
      (by linear_combination (4 * kapFour ^ 2 * mFour ^ 2) * hrootSq)
      (by linear_combination (4 * kapFive ^ 2 * mFive ^ 2) * hrootSq)
    have hcsq : 0 < (area * lenM ^ 2) ^ 2 :=
      pow_pos (mul_pos hpos (pow_pos hlenMpos 2)) 2
    have hleft : 3 * ((area * lenM ^ 2 * wOneTwo + area * lenM ^ 2 * wOneThree
          + area * lenM ^ 2 * wOneFour + area * lenM ^ 2 * wOneFive) ^ 2
        + (area * lenM ^ 2 * wOneTwo + area * lenM ^ 2 * wTwoThree
          + area * lenM ^ 2 * wTwoFour + area * lenM ^ 2 * wTwoFive) ^ 2
        + (area * lenM ^ 2 * wOneThree + area * lenM ^ 2 * wTwoThree
          + area * lenM ^ 2 * wThreeFour + area * lenM ^ 2 * wThreeFive) ^ 2
        + (area * lenM ^ 2 * wOneFour + area * lenM ^ 2 * wTwoFour
          + area * lenM ^ 2 * wThreeFour + area * lenM ^ 2 * wFourFive) ^ 2
        + (area * lenM ^ 2 * wOneFive + area * lenM ^ 2 * wTwoFive
          + area * lenM ^ 2 * wThreeFive + area * lenM ^ 2 * wFourFive) ^ 2)
        = (area * lenM ^ 2) ^ 2 * (3 * ((wOneTwo + wOneThree + wOneFour + wOneFive) ^ 2
          + (wOneTwo + wTwoThree + wTwoFour + wTwoFive) ^ 2
          + (wOneThree + wTwoThree + wThreeFour + wThreeFive) ^ 2
          + (wOneFour + wTwoFour + wThreeFour + wFourFive) ^ 2
          + (wOneFive + wTwoFive + wThreeFive + wFourFive) ^ 2)) := by ring
    have hright : 20 * ((area * lenM ^ 2 * wOneTwo) ^ 2 + (area * lenM ^ 2 * wOneThree) ^ 2
        + (area * lenM ^ 2 * wOneFour) ^ 2 + (area * lenM ^ 2 * wOneFive) ^ 2
        + (area * lenM ^ 2 * wTwoThree) ^ 2 + (area * lenM ^ 2 * wTwoFour) ^ 2
        + (area * lenM ^ 2 * wTwoFive) ^ 2 + (area * lenM ^ 2 * wThreeFour) ^ 2
        + (area * lenM ^ 2 * wThreeFive) ^ 2 + (area * lenM ^ 2 * wFourFive) ^ 2)
        = (area * lenM ^ 2) ^ 2 * (20 * (wOneTwo ^ 2 + wOneThree ^ 2 + wOneFour ^ 2
          + wOneFive ^ 2 + wTwoThree ^ 2 + wTwoFour ^ 2 + wTwoFive ^ 2 + wThreeFour ^ 2
          + wThreeFive ^ 2 + wFourFive ^ 2)) := by ring
    rw [hleft, hright] at hcore
    exact le_of_mul_le_mul_left hcore hcsq

/-! ## Layer 3 — the dependency plane of five vectors of rank three -/

/-- The squared volume does not read the order of its three arguments.  These
five statements cover the five non-trivial orders. -/
theorem atomVolumeSq_swapFirst (first second third : Fin 3 → ℝ) :
    atomVolume second first third ^ 2 = atomVolume first second third ^ 2 := by
  simp only [atomVolume, atomWedge, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem atomVolumeSq_swapLast (first second third : Fin 3 → ℝ) :
    atomVolume first third second ^ 2 = atomVolume first second third ^ 2 := by
  simp only [atomVolume, atomWedge, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem atomVolumeSq_swapOuter (first second third : Fin 3 → ℝ) :
    atomVolume third second first ^ 2 = atomVolume first second third ^ 2 := by
  simp only [atomVolume, atomWedge, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem atomVolumeSq_rotateLeft (first second third : Fin 3 → ℝ) :
    atomVolume second third first ^ 2 = atomVolume first second third ^ 2 := by
  simp only [atomVolume, atomWedge, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem atomVolumeSq_rotateRight (first second third : Fin 3 → ℝ) :
    atomVolume third first second ^ 2 = atomVolume first second third ^ 2 := by
  simp only [atomVolume, atomWedge, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The Grassmann-Plucker relation with the MIDDLE slot distinguished. -/
theorem atomVolumePluckerMid (vecZero vecOne vecTwo vecThree vecFour : Fin 3 → ℝ) :
    atomVolume vecZero vecOne vecTwo * atomVolume vecTwo vecThree vecFour
      - atomVolume vecZero vecTwo vecThree * atomVolume vecOne vecTwo vecFour
      + atomVolume vecZero vecTwo vecFour * atomVolume vecOne vecTwo vecThree = 0 := by
  simp only [atomVolume, atomWedge, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The Grassmann-Plucker relation with the SECOND slot distinguished. -/
theorem atomVolumePluckerLeft (vecZero vecOne vecTwo vecThree vecFour : Fin 3 → ℝ) :
    atomVolume vecZero vecOne vecTwo * atomVolume vecOne vecThree vecFour
      - atomVolume vecZero vecOne vecThree * atomVolume vecOne vecTwo vecFour
      + atomVolume vecZero vecOne vecFour * atomVolume vecOne vecTwo vecThree = 0 := by
  simp only [atomVolume, atomWedge, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **THE DEPENDENCY PLANE CARRIES THE MARGIN.**  For any five vectors of rank
three the FOURTH power of one triple volume times the pentagon margin is not
negative.  There is no hypothesis.

The two dependency vectors are the Cramer coefficients of the first four slots
and of the slots `0 1 2 4`.  Their ten two-slot minors are the volume of the base
triple `0 1 2` times the volume of the COMPLEMENTARY triple, which is what
`Gtz.atomVolumePluckerMid` and `Gtz.atomVolumePluckerLeft` supply.  Then
`Gtz.atomDualPlaneFloor` closes it. -/
theorem atomPentagonMargin_baseSquare (vecZero vecOne vecTwo vecThree vecFour : Fin 3 → ℝ) :
    0 ≤ (atomVolume vecZero vecOne vecTwo ^ 2) ^ 2
      * atomPentagonMargin vecZero vecOne vecTwo vecThree vecFour := by
  have hmid := atomVolumePluckerMid vecZero vecOne vecTwo vecThree vecFour
  have hleft := atomVolumePluckerLeft vecZero vecOne vecTwo vecThree vecFour
  have hbase := atomVolumePlucker vecZero vecOne vecTwo vecThree vecFour
  have hdual := atomDualPlaneFloor
    (atomVolume vecOne vecTwo vecThree) (-atomVolume vecZero vecTwo vecThree)
    (atomVolume vecZero vecOne vecThree) (-atomVolume vecZero vecOne vecTwo) 0
    (atomVolume vecOne vecTwo vecFour) (-atomVolume vecZero vecTwo vecFour)
    (atomVolume vecZero vecOne vecFour) 0 (-atomVolume vecZero vecOne vecTwo)
    (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecTwo vecThree vecFour ^ 2)
    (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecOne vecThree vecFour ^ 2)
    (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecOne vecTwo vecFour ^ 2)
    (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecOne vecTwo vecThree ^ 2)
    (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecThree vecFour ^ 2)
    (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecTwo vecFour ^ 2)
    (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecTwo vecThree ^ 2)
    (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecOne vecFour ^ 2)
    (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecOne vecThree ^ 2)
    (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecOne vecTwo ^ 2)
    (by linear_combination (atomVolume vecZero vecOne vecTwo * atomVolume vecTwo vecThree vecFour
        + atomVolume vecZero vecTwo vecThree * atomVolume vecOne vecTwo vecFour
        - atomVolume vecZero vecTwo vecFour * atomVolume vecOne vecTwo vecThree) * hmid)
    (by linear_combination (atomVolume vecZero vecOne vecTwo * atomVolume vecOne vecThree vecFour
        + atomVolume vecZero vecOne vecThree * atomVolume vecOne vecTwo vecFour
        - atomVolume vecZero vecOne vecFour * atomVolume vecOne vecTwo vecThree) * hleft)
    (by ring) (by ring)
    (by linear_combination (atomVolume vecZero vecOne vecTwo * atomVolume vecZero vecThree vecFour
        + atomVolume vecZero vecOne vecThree * atomVolume vecZero vecTwo vecFour
        - atomVolume vecZero vecOne vecFour * atomVolume vecZero vecTwo vecThree) * hbase)
    (by ring) (by ring) (by ring) (by ring) (by ring)
  have hbridge : (atomVolume vecZero vecOne vecTwo ^ 2) ^ 2
      * atomPentagonMargin vecZero vecOne vecTwo vecThree vecFour
      = 20 * ((atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecTwo vecThree vecFour ^ 2) ^ 2
          + (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecOne vecThree vecFour ^ 2) ^ 2
          + (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecOne vecTwo vecFour ^ 2) ^ 2
          + (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecOne vecTwo vecThree ^ 2) ^ 2
          + (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecThree vecFour ^ 2) ^ 2
          + (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecTwo vecFour ^ 2) ^ 2
          + (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecTwo vecThree ^ 2) ^ 2
          + (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecOne vecFour ^ 2) ^ 2
          + (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecOne vecThree ^ 2) ^ 2
          + (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecOne vecTwo ^ 2) ^ 2)
        - 3 * ((atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecTwo vecThree vecFour ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecOne vecThree vecFour ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecOne vecTwo vecFour ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecOne vecTwo vecThree ^ 2) ^ 2
            + (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecTwo vecThree vecFour ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecThree vecFour ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecTwo vecFour ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecTwo vecThree ^ 2) ^ 2
            + (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecOne vecThree vecFour ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecThree vecFour ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecOne vecFour ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecOne vecThree ^ 2) ^ 2
            + (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecOne vecTwo vecFour ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecTwo vecFour ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecOne vecFour ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecOne vecTwo ^ 2) ^ 2
            + (atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecOne vecTwo vecThree ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecTwo vecThree ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecOne vecThree ^ 2
              + atomVolume vecZero vecOne vecTwo ^ 2 * atomVolume vecZero vecOne vecTwo ^ 2) ^ 2) := by
    simp only [atomPentagonMargin, atomPentagonReading]
    ring
  rw [hbridge]
  linarith [hdual]

/-- **THE PENTAGON MARGIN AT A NON-DEGENERATE BASE TRIPLE.** -/
theorem atomPentagonMargin_nonneg_of_base (vecZero vecOne vecTwo vecThree vecFour : Fin 3 → ℝ)
    (hbase : atomVolume vecZero vecOne vecTwo ≠ 0) :
    0 ≤ atomPentagonMargin vecZero vecOne vecTwo vecThree vecFour := by
  have hsq := atomPentagonMargin_baseSquare vecZero vecOne vecTwo vecThree vecFour
  have hpos : 0 < (atomVolume vecZero vecOne vecTwo ^ 2) ^ 2 := by positivity
  nlinarith [hsq, hpos]

/-! ## Layer 4 — the pentagon margin does not read the order of the five slots -/

theorem atomPentagonMargin_permOneThree (bZero bOne bTwo bThree bFour : Fin 3 → ℝ) :
    atomPentagonMargin bZero bOne bThree bTwo bFour
      = atomPentagonMargin bZero bOne bTwo bThree bFour := by
  simp only [atomPentagonMargin, atomVolumeSq_swapLast bZero bTwo bThree,
    atomVolumeSq_swapLast bOne bTwo bThree, atomVolumeSq_swapFirst bTwo bThree bFour,
    atomPentagonReading]
  ring

theorem atomPentagonMargin_permOneFour (bZero bOne bTwo bThree bFour : Fin 3 → ℝ) :
    atomPentagonMargin bZero bOne bFour bTwo bThree
      = atomPentagonMargin bZero bOne bTwo bThree bFour := by
  simp only [atomPentagonMargin, atomVolumeSq_swapLast bZero bTwo bFour,
    atomVolumeSq_swapLast bZero bThree bFour, atomVolumeSq_swapLast bOne bTwo bFour,
    atomVolumeSq_swapLast bOne bThree bFour, atomVolumeSq_rotateRight bTwo bThree bFour,
    atomPentagonReading]
  ring

theorem atomPentagonMargin_permTwoThree (bZero bOne bTwo bThree bFour : Fin 3 → ℝ) :
    atomPentagonMargin bZero bTwo bThree bOne bFour
      = atomPentagonMargin bZero bOne bTwo bThree bFour := by
  simp only [atomPentagonMargin, atomVolumeSq_swapLast bZero bOne bTwo,
    atomVolumeSq_swapLast bZero bOne bThree, atomVolumeSq_rotateLeft bOne bTwo bThree,
    atomVolumeSq_swapFirst bOne bTwo bFour, atomVolumeSq_swapFirst bOne bThree bFour,
    atomPentagonReading]
  ring

theorem atomPentagonMargin_permTwoFour (bZero bOne bTwo bThree bFour : Fin 3 → ℝ) :
    atomPentagonMargin bZero bTwo bFour bOne bThree
      = atomPentagonMargin bZero bOne bTwo bThree bFour := by
  simp only [atomPentagonMargin, atomVolumeSq_swapLast bZero bOne bTwo,
    atomVolumeSq_swapLast bZero bOne bFour, atomVolumeSq_swapLast bZero bThree bFour,
    atomVolumeSq_rotateLeft bOne bTwo bFour, atomVolumeSq_swapLast bTwo bThree bFour,
    atomVolumeSq_swapFirst bOne bTwo bThree, atomVolumeSq_rotateRight bOne bThree bFour,
    atomPentagonReading]
  ring

theorem atomPentagonMargin_permThreeFour (bZero bOne bTwo bThree bFour : Fin 3 → ℝ) :
    atomPentagonMargin bZero bThree bFour bOne bTwo
      = atomPentagonMargin bZero bOne bTwo bThree bFour := by
  simp only [atomPentagonMargin, atomVolumeSq_swapLast bZero bOne bThree,
    atomVolumeSq_swapLast bZero bTwo bThree, atomVolumeSq_swapLast bZero bOne bFour,
    atomVolumeSq_swapLast bZero bTwo bFour, atomVolumeSq_rotateLeft bOne bThree bFour,
    atomVolumeSq_rotateLeft bTwo bThree bFour, atomVolumeSq_rotateRight bOne bTwo bThree,
    atomVolumeSq_rotateRight bOne bTwo bFour, atomPentagonReading]
  ring

theorem atomPentagonMargin_permOneTwoThree (bZero bOne bTwo bThree bFour : Fin 3 → ℝ) :
    atomPentagonMargin bOne bTwo bThree bZero bFour
      = atomPentagonMargin bZero bOne bTwo bThree bFour := by
  simp only [atomPentagonMargin, atomVolumeSq_rotateLeft bZero bOne bTwo,
    atomVolumeSq_rotateLeft bZero bOne bThree, atomVolumeSq_swapFirst bZero bOne bFour,
    atomVolumeSq_rotateLeft bZero bTwo bThree, atomVolumeSq_swapFirst bZero bTwo bFour,
    atomVolumeSq_swapFirst bZero bThree bFour, atomPentagonReading]
  ring

theorem atomPentagonMargin_permOneTwoFour (bZero bOne bTwo bThree bFour : Fin 3 → ℝ) :
    atomPentagonMargin bOne bTwo bFour bZero bThree
      = atomPentagonMargin bZero bOne bTwo bThree bFour := by
  simp only [atomPentagonMargin, atomVolumeSq_rotateLeft bZero bOne bTwo,
    atomVolumeSq_rotateLeft bZero bOne bFour, atomVolumeSq_swapLast bOne bThree bFour,
    atomVolumeSq_swapFirst bZero bOne bThree, atomVolumeSq_rotateLeft bZero bTwo bFour,
    atomVolumeSq_swapLast bTwo bThree bFour, atomVolumeSq_swapFirst bZero bTwo bThree,
    atomVolumeSq_rotateRight bZero bThree bFour, atomPentagonReading]
  ring

theorem atomPentagonMargin_permOneThreeFour (bZero bOne bTwo bThree bFour : Fin 3 → ℝ) :
    atomPentagonMargin bOne bThree bFour bZero bTwo
      = atomPentagonMargin bZero bOne bTwo bThree bFour := by
  simp only [atomPentagonMargin, atomVolumeSq_rotateLeft bZero bOne bThree,
    atomVolumeSq_swapLast bOne bTwo bThree, atomVolumeSq_rotateLeft bZero bOne bFour,
    atomVolumeSq_swapLast bOne bTwo bFour, atomVolumeSq_swapFirst bZero bOne bTwo,
    atomVolumeSq_rotateLeft bZero bThree bFour, atomVolumeSq_rotateLeft bTwo bThree bFour,
    atomVolumeSq_rotateRight bZero bTwo bThree, atomVolumeSq_rotateRight bZero bTwo bFour,
    atomPentagonReading]
  ring

theorem atomPentagonMargin_permTwoThreeFour (bZero bOne bTwo bThree bFour : Fin 3 → ℝ) :
    atomPentagonMargin bTwo bThree bFour bZero bOne
      = atomPentagonMargin bZero bOne bTwo bThree bFour := by
  simp only [atomPentagonMargin, atomVolumeSq_rotateLeft bZero bTwo bThree,
    atomVolumeSq_rotateLeft bOne bTwo bThree, atomVolumeSq_rotateLeft bZero bTwo bFour,
    atomVolumeSq_rotateLeft bOne bTwo bFour, atomVolumeSq_rotateRight bZero bOne bTwo,
    atomVolumeSq_rotateLeft bZero bThree bFour, atomVolumeSq_rotateLeft bOne bThree bFour,
    atomVolumeSq_rotateRight bZero bOne bThree, atomVolumeSq_rotateRight bZero bOne bFour,
    atomPentagonReading]
  ring

/-! ## Layer 5 — the pentagon floor -/

/-- **THE PENTAGON FLOOR IS A THEOREM.**  Every five vectors of rank three obey
it.  Either some triple volume is not zero, and then the dependency plane of the
five vectors carries the margin, or every triple volume is zero and the margin
reads zero. -/
theorem atomPentagonFloor : AtomPentagonFloor := by
  intro bZero bOne bTwo bThree bFour
  by_cases h012 : atomVolume bZero bOne bTwo ≠ 0
  · exact atomPentagonMargin_nonneg_of_base _ _ _ _ _ h012
  by_cases h013 : atomVolume bZero bOne bThree ≠ 0
  · rw [← atomPentagonMargin_permOneThree]
    exact atomPentagonMargin_nonneg_of_base _ _ _ _ _ h013
  by_cases h014 : atomVolume bZero bOne bFour ≠ 0
  · rw [← atomPentagonMargin_permOneFour]
    exact atomPentagonMargin_nonneg_of_base _ _ _ _ _ h014
  by_cases h023 : atomVolume bZero bTwo bThree ≠ 0
  · rw [← atomPentagonMargin_permTwoThree]
    exact atomPentagonMargin_nonneg_of_base _ _ _ _ _ h023
  by_cases h024 : atomVolume bZero bTwo bFour ≠ 0
  · rw [← atomPentagonMargin_permTwoFour]
    exact atomPentagonMargin_nonneg_of_base _ _ _ _ _ h024
  by_cases h034 : atomVolume bZero bThree bFour ≠ 0
  · rw [← atomPentagonMargin_permThreeFour]
    exact atomPentagonMargin_nonneg_of_base _ _ _ _ _ h034
  by_cases h123 : atomVolume bOne bTwo bThree ≠ 0
  · rw [← atomPentagonMargin_permOneTwoThree]
    exact atomPentagonMargin_nonneg_of_base _ _ _ _ _ h123
  by_cases h124 : atomVolume bOne bTwo bFour ≠ 0
  · rw [← atomPentagonMargin_permOneTwoFour]
    exact atomPentagonMargin_nonneg_of_base _ _ _ _ _ h124
  by_cases h134 : atomVolume bOne bThree bFour ≠ 0
  · rw [← atomPentagonMargin_permOneThreeFour]
    exact atomPentagonMargin_nonneg_of_base _ _ _ _ _ h134
  by_cases h234 : atomVolume bTwo bThree bFour ≠ 0
  · rw [← atomPentagonMargin_permTwoThreeFour]
    exact atomPentagonMargin_nonneg_of_base _ _ _ _ _ h234
  simp only [ne_eq, not_not] at h012 h013 h014 h023 h024 h034 h123 h124 h134 h234
  simp only [atomPentagonMargin, atomPentagonReading, h012, h013, h014, h023, h024,
    h034, h123, h124, h134, h234]
  norm_num

/-! ## Layer 6 — the tenth, the supply, and the residues that close -/

/-- **THE TENTH IS UNCONDITIONAL.**  Every real rank-three Parseval frame of six
atoms obeys `E2 ≤ 10 * E3`, with no leverage hypothesis.

Ten is the best constant this route can carry: the icosahedral frame attains it,
and `Gtz.atomPluckerEnergyTwo_le_twelve` was the previous unconditional
reading. -/
theorem atomPluckerTenth : AtomPluckerTenth :=
  atomPluckerTenth_of_pentagonFloor atomPentagonFloor

/-- **THE LEVERAGE RESIDUE IS CLOSED.**  `Gtz.AtomPluckerTenthUnbalanced`, the
residue that `Gtz.Wave.PluckerSchurFloor` named, is a theorem. -/
theorem atomPluckerTenthUnbalanced : AtomPluckerTenthUnbalanced :=
  atomPluckerTenthUnbalanced_of_pentagonFloor atomPentagonFloor

/-- **THE SPECTRAL SUPPLY AT ONE TENTH.**  Every real rank-three Parseval frame
of six atoms carries a three-slot block that never shortens a probe below one
tenth.  This is the unconditional spectral floor of the deciding cell, past the
landed `Gtz.atomSpectralSupply_twelfth`. -/
theorem atomSpectralSupply_tenth : AtomSpectralSupply (1 / 10) :=
  atomSpectralSupply_tenth_of_pentagonFloor atomPentagonFloor

/-- **THE CARRIER AT ONE TENTH.**  The concrete form the deciding cell consumes:
every scale that stays at or below one tenth is carried by a three-slot
subset. -/
theorem exists_atomCarrier_tenth (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hlight : ∀ slot, scale slot ≤ 1 / 10) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  obtain ⟨slotOne, slotTwo, slotThree, hone, htwo, hthree, hfloor⟩ :=
    atomSpectralSupply_tenth atom hframe
  exact exists_atomCarrier_of_blendFloor atom scale hone htwo hthree hfloor hlight

/-- **THE SPREAD FLOOR IS UNCONDITIONAL.**  The spread of the determinantal
measure is at least twice its level-three energy.  This is the tenth read
through `Gtz.atomPluckerFlatnessGap_eq_spread`. -/
theorem atomPluckerSpread_ge_twice
    {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    2 * atomPluckerEnergyThree atom ≤ atomPluckerSpread atom := by
  have hgap := atomPluckerFlatnessGap_eq_spread hframe
  have htenth := atomPluckerTenth atom hframe
  linarith

/-- **THE LEVEL-THREE FLOOR IS UNCONDITIONAL.**  The level-three energy of a real
rank-three Parseval frame of six atoms is at least `3/50` plus a tenth of the
leverage spread.  Three fiftieths is the exact icosahedral reading. -/
theorem atomPluckerEnergyThree_ge {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    3 / 50 + atomLeverageSpread atom / 10 ≤ atomPluckerEnergyThree atom :=
  atomPluckerEnergyThree_ge_of_pentagonFloor atomPentagonFloor hframe

end Gtz
