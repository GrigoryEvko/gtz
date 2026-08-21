/-
# The plane shadow: a plane-strict pair with no genericity, and the axis Schur calculus

Every two-dimensional subspace of `R^3` carries a rank-two shadow of a rank-three
weighted design, because Parseval restricts to the plane.  The tree already owns
that compression (`Gtz.planarCompressionDesign`), the Binet-Cauchy dictionary
`bracket(shadow a, shadow b) = <pOne x pTwo, g_a x g_b>`
(`Gtz.planarCompression_pairBracket`), and the transversal route to a plane-strict
pair (`Gtz.exists_planeStrictPair_of_transversalAxis`).  This module adds two
things that route has not had.

## 1. A plane-strict pair with NO genericity hypothesis

The shadow leverage of an atom is `l_c - (g_c . axis)^2`
(`Gtz.leverageOf_planarCompressionDesign_atom`).  Feed that to the tree's rank-two
Nesterenko engine `Gtz.exists_posDef_pair_of_nesterenkoExcess`:

    1 + t_d  <  2 t_d (l_d - (g_d . axis)^2)   forces a plane-strict pair through d.

No transversality, no four labels, no moment curve.  The hypothesis is an OPEN
BAND of normals around the great circle orthogonal to `g_d`, namely
`(g_d . axis)^2 < l_d - 1/2 - 1/(2 t_d)`, and the band is nonempty exactly when
`1 + t_d < 2 t_d l_d`.  Measured at the `(5,3)` diamond in floating point: the
four rim atoms read `t (2 l - 1) = 1.1`, above the threshold `1`, and 5000 sampled
normals orthogonal to each rim atom deliver a pair whose plane gap has smallest
eigenvalue at least `+0.377`, with zero failures.  The cap cannot be sharpened by
a constant, because `Gtz.exists_isTie_rankTwoCorankOne_attaining_bound` attains it.

## 2. The axis Schur calculus, and the tie's two-parameter scalar family

Read a subset gap in an orthonormal frame `(pOne, pTwo, axis)` and split
`R^3 = plane + R axis`.  Three exact identities carry the split.

* `Gtz.frameDet_eq_blockDet_mul_sub_schurLoad` — the closed-form Schur expansion
  `det = D ff - (aa ee^2 - 2 bb dd ee + cc dd^2)`, with `D := aa cc - bb^2`.
* `Gtz.frameBlockDet_rankOne` — the matrix-determinant lemma at `2 x 2`:
  a third atom with frame coordinates `(x, y, z)` moves `D` by
  `alpha = cc x^2 - 2 bb x y + aa y^2`, and `alpha` is nonnegative.
* `Gtz.frameDet_rankOne` — **THE RANK-ONE SCHUR UPDATE**, cleared of denominators:

      D * det(triple)  =  det(pair) * (D + alpha)  +  (z D - beta)^2,
      beta := x (cc dd - bb ee) + y (aa ee - bb dd).

  The third atom's contribution to the Schur complement is an EXACT SQUARE.  In
  quotient form this is the Sherman-Morrison collapse
  `1 - alpha + alpha^2/(1 + alpha) = 1/(1 + alpha)`.

At a plane-strict pair the plane block is positive definite (`D > 0`) and the
pair's own gap determinant is strictly negative
(`Gtz.frameDet_pair_neg_of_planeStrictPair`), because a pair never weakly
dominates at rank three.  The tree's gate `det(triple) <= 0` at a tie then reads,
through the update, as a scalar inequality for EVERY third atom and EVERY
plane-strict normal:

    (z_c D - beta_c)^2  <=  (- det(pair)) * (D + alpha_c).

That is `Gtz.sq_schurProbe_reading_le_of_isTie`.  It is a two-parameter family on
the sphere of normals, and the diamond attains it: the worst relative violation
over 13007 sampled plane-strict pairs is `+9.1e-15`, and equality holds wherever
the completed triple is one of the diamond's eight weakly dominating triples.

## 3. The Parseval aggregate

The family aggregates in closed form.  Put

    w := D . axis - (cc dd - bb ee) . pOne - (aa ee - bb dd) . pTwo.

Then `g_c . w = z_c D - beta_c` identically (`Gtz.atom_dotProduct_schurProbe`),
`w . w = D^2 + (cc dd - bb ee)^2 + (aa ee - bb dd)^2`, the weighted total of
`alpha_c` is `aa + cc` by polarized Parseval, and the weighted total of
`(g_c . w)^2` is `w . w`.  Summing the scalar family over the complement of the
pair gives the pair-mass floor

    w . w  <=  (- det(pair))(D + aa + cc) + t_a (g_a . w)^2 + t_b (g_b . w)^2,

`Gtz.schurProbe_energy_le_of_isTie`.  Measured at the diamond it holds at all
13007 sampled plane-strict pairs, with at least 16.7 percent of slack, so it is a
true law there and not a boundary artifact.

## 4. The Sylvester moment ladder, and an exact area ceiling at a tie

The first two Sylvester minors already have exact weighted averages in the tree:
Parseval's trace gives `sum c, t_c (l_c - 1) = k - 1`, and
`Gtz.sum_weight_mul_pairGapForm` gives `sum c, t_c pairGapMinor(a, c) = l_a - 2` at
rank three.  The THIRD is `Gtz.sum_weight_mul_tripleGapDet`:

    sum over c of  t_c * tripleGapDet(a, b, c)  =  2 - l_a - l_b,

for every pair of atoms of every rank-three design, at every size.  Five Parseval
readings spend the design and no atom survives on the right.

At a tie no triple dominates strictly, so through a heavy admissible pair every
third minor is nonpositive.  The two terms the pair keeps are polynomials in its
own readings, and the moment law turns the tie into an exact CEILING on the pair's
squared area (`Gtz.crossNormSq_le_of_isTie`):

    2 (t_a + t_b) crossNormSq(a, b)
        <=  l_a + l_b - 2 + t_a (2 l_a + l_b - 1) + t_b (l_a + 2 l_b - 1).

Admissibility is the matching FLOOR `l_a + l_b - 1 < crossNormSq(a, b)`, so a heavy
admissible pair of a tie is confined to an explicit window
(`Gtz.crossNormSq_window_of_isTie`).

The ceiling is ATTAINED at both shipped rank-three ties.  At the `(4,3)`
tetrahedron every leverage is `3` and every pairing is `-1`, so every pair reads
squared area `8` against a ceiling of `8`.  At the `(5,3)` diamond, measured in
floating point, all ten pairs are heavy and admissible and FOUR of them sit exactly
on the ceiling, at squared area `10` against a ceiling of `10`.  No constant can
sharpen it.  Equality is a rigidity locus: it forces every third minor through the
pair to VANISH (`Gtz.tripleGapDet_eq_zero_of_crossNormSq_eq_ceiling`).

## 5. The simplicity hypothesis leaves

Part 7 buys its admissible pair with geometry and pays a simplicity hypothesis.
The second Sylvester moment buys one with arithmetic and pays nothing.  Peeling the
diagonal term off `sum c, t_c pairGapMinor(a, c) = l_a - 2` leaves an average over
the other atoms that is positive exactly when `2 + t_a < l_a (1 + 2 t_a)`, and that
hands over an admissible partner.  At rank three the weighted leverages average to
THREE, so some atom reaches `l >= 3`, while the threshold `(2 + t) / (1 + 2 t)`
never passes `2`.

So every rank-three design carries a heavy admissible pair, unconditionally, at
every size (`Gtz.exists_admissiblePair_rank_three`), and the window holds at EVERY
rank-three tie (`Gtz.exists_pair_window_of_isTie`).  Checked over 60000 random
rank-three designs of sizes four to nine: the heaviest atom beats its threshold by
at least `1.356`, and a heavy admissible partner exists every time.

## What is measured and what is proved

Every number above comes from `scratchpad/planeshadow`, in floating point for the
sphere sweeps and in exact rationals for the three identities.  Nothing numerical
enters a proof.  The Lean content is unconditional at every size.
-/
import Mathlib
import Gtz.Design.SphereExistence
import Gtz.Design.TripleGramSylvester
import Gtz.Quantitative.ChartHadamard
import Gtz.LinAlg.SchurRankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {size : ℕ}

/-! ## Part 1 — the scalar frame algebra

Six scalars carry a symmetric `3 x 3` matrix in an orthonormal frame, and three
more carry a rank-one update.  Everything in this part is a polynomial identity
or a one-step positivity argument.  No design and no matrix appear. -/

/-- The determinant of a symmetric `3 x 3` matrix from its six frame readings. -/
def frameDet (aa bb cc dd ee ff : ℝ) : ℝ :=
  aa * (cc * ff - ee ^ 2) - bb * (bb * ff - ee * dd) + dd * (bb * ee - cc * dd)

/-- The determinant of the plane block. -/
def frameBlockDet (aa bb cc : ℝ) : ℝ := aa * cc - bb ^ 2

/-- The Schur load: the plane adjugate form of the cross moment. -/
def frameSchurLoad (aa bb cc dd ee : ℝ) : ℝ :=
  aa * ee ^ 2 - 2 * bb * (dd * ee) + cc * dd ^ 2

/-- The plane adjugate form at a plane vector `(x, y)`.  A third atom moves the
plane block determinant by exactly this amount. -/
def frameAlpha (aa bb cc x y : ℝ) : ℝ := cc * x ^ 2 - 2 * bb * (x * y) + aa * y ^ 2

/-- The plane adjugate pairing of a plane vector `(x, y)` with the cross moment. -/
def frameBeta (aa bb cc dd ee x y : ℝ) : ℝ :=
  x * (cc * dd - bb * ee) + y * (aa * ee - bb * dd)

/-- **THE CLOSED-FORM SCHUR EXPANSION.**  The determinant is the plane block
determinant times the axis reading, less the Schur load. -/
theorem frameDet_eq_blockDet_mul_sub_schurLoad (aa bb cc dd ee ff : ℝ) :
    frameDet aa bb cc dd ee ff
      = frameBlockDet aa bb cc * ff - frameSchurLoad aa bb cc dd ee := by
  simp only [frameDet, frameBlockDet, frameSchurLoad]
  ring

/-- **THE MATRIX-DETERMINANT LEMMA AT `2 x 2`.**  A rank-one update of the plane
block moves its determinant by the plane adjugate form. -/
theorem frameBlockDet_rankOne (aa bb cc x y : ℝ) :
    frameBlockDet (aa + x ^ 2) (bb + x * y) (cc + y ^ 2)
      = frameBlockDet aa bb cc + frameAlpha aa bb cc x y := by
  simp only [frameBlockDet, frameAlpha]
  ring

/-- **THE RANK-ONE SCHUR UPDATE.**  A polynomial identity in nine scalars: the
third atom adds an EXACT SQUARE to the Schur complement, once both sides are
cleared by the plane block determinant.  This is the centre of the module. -/
theorem frameDet_rankOne (aa bb cc dd ee ff x y z : ℝ) :
    frameBlockDet aa bb cc
        * frameDet (aa + x ^ 2) (bb + x * y) (cc + y ^ 2)
            (dd + x * z) (ee + y * z) (ff + z ^ 2)
      = frameDet aa bb cc dd ee ff
            * frameBlockDet (aa + x ^ 2) (bb + x * y) (cc + y ^ 2)
        + (z * frameBlockDet aa bb cc - frameBeta aa bb cc dd ee x y) ^ 2 := by
  simp only [frameDet, frameBlockDet, frameBeta]
  ring

/-- The plane adjugate form is nonnegative at a positive definite plane block. -/
theorem frameAlpha_nonneg {aa bb cc : ℝ} (hdiag : 0 < aa)
    (hblock : 0 < frameBlockDet aa bb cc) (x y : ℝ) :
    0 ≤ frameAlpha aa bb cc x y := by
  have hclear : aa * frameAlpha aa bb cc x y
      = frameBlockDet aa bb cc * x ^ 2 + (bb * x - aa * y) ^ 2 := by
    simp only [frameAlpha, frameBlockDet]
    ring
  have hnonneg : 0 ≤ aa * frameAlpha aa bb cc x y := by
    rw [hclear]
    have hleft : 0 ≤ frameBlockDet aa bb cc * x ^ 2 := mul_nonneg hblock.le (sq_nonneg x)
    linarith [sq_nonneg (bb * x - aa * y)]
  by_contra hnegative
  push Not at hnegative
  nlinarith [hnonneg, hdiag, hnegative]

/-- The plane block determinant of a rank-one update stays positive. -/
theorem frameBlockDet_rankOne_pos {aa bb cc : ℝ} (hdiag : 0 < aa)
    (hblock : 0 < frameBlockDet aa bb cc) (x y : ℝ) :
    0 < frameBlockDet (aa + x ^ 2) (bb + x * y) (cc + y ^ 2) := by
  rw [frameBlockDet_rankOne]
  linarith [frameAlpha_nonneg hdiag hblock x y]

/-! ## Part 2 — an orthonormal frame, bundled

The six orthogonality facts travel together through every theorem of this module,
so they travel as one record. -/

/-- An orthonormal frame of `R^3` split into a plane and an axis. -/
structure AxisFrame where
  /-- The first plane direction. -/
  pOne : Fin 3 → ℝ
  /-- The second plane direction. -/
  pTwo : Fin 3 → ℝ
  /-- The axis, orthogonal to the plane. -/
  axis : Fin 3 → ℝ
  /-- The first plane direction is a unit vector. -/
  oneOne : pOne ⬝ᵥ pOne = 1
  /-- The second plane direction is a unit vector. -/
  twoTwo : pTwo ⬝ᵥ pTwo = 1
  /-- The axis is a unit vector. -/
  axisAxis : axis ⬝ᵥ axis = 1
  /-- The two plane directions are orthogonal. -/
  oneTwo : pOne ⬝ᵥ pTwo = 0
  /-- The first plane direction is orthogonal to the axis. -/
  oneAxis : pOne ⬝ᵥ axis = 0
  /-- The second plane direction is orthogonal to the axis. -/
  twoAxis : pTwo ⬝ᵥ axis = 0

namespace AxisFrame

variable (frame : AxisFrame)

/-- The first plane direction is not the zero vector. -/
theorem pOne_ne_zero : frame.pOne ≠ 0 := by
  intro hzero
  have hunit := frame.oneOne
  rw [hzero, zero_dotProduct] at hunit
  exact zero_ne_one hunit

/-- The second plane direction is not the zero vector. -/
theorem pTwo_ne_zero : frame.pTwo ≠ 0 := by
  intro hzero
  have hunit := frame.twoTwo
  rw [hzero, zero_dotProduct] at hunit
  exact zero_ne_one hunit

/-- **THE FRAME SPLIT OF A SQUARED LENGTH.**  A vector spends its squared length
on the two plane readings and the axis reading. -/
theorem dotProduct_self_split (vec : Fin 3 → ℝ) :
    vec ⬝ᵥ vec = (vec ⬝ᵥ frame.pOne) ^ 2 + (vec ⬝ᵥ frame.pTwo) ^ 2
      + (vec ⬝ᵥ frame.axis) ^ 2 := by
  have hresolve := orthonormalFrame_resolution frame.oneOne frame.twoTwo frame.axisAxis
    frame.oneTwo frame.oneAxis frame.twoAxis vec
  have hTwoOne : frame.pTwo ⬝ᵥ frame.pOne = 0 := by
    rw [dotProduct_comm]; exact frame.oneTwo
  have hAxisOne : frame.axis ⬝ᵥ frame.pOne = 0 := by
    rw [dotProduct_comm]; exact frame.oneAxis
  have hAxisTwo : frame.axis ⬝ᵥ frame.pTwo = 0 := by
    rw [dotProduct_comm]; exact frame.twoAxis
  conv_lhs => rw [hresolve]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    frame.oneOne, frame.twoTwo, frame.axisAxis, frame.oneTwo, frame.oneAxis, frame.twoAxis,
    hTwoOne, hAxisOne, hAxisTwo]
  ring

/-- A plane combination is orthogonal to the axis. -/
theorem planeCombination_dotProduct_axis (x y : ℝ) :
    (x • frame.pOne + y • frame.pTwo + (0 : ℝ) • frame.axis) ⬝ᵥ frame.axis = 0 := by
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, frame.oneAxis, frame.twoAxis,
    frame.axisAxis]
  ring

/-- A plane combination with a nonzero second coordinate is a nonzero vector. -/
theorem planeCombination_ne_zero {x y : ℝ} (hy : y ≠ 0) :
    (x • frame.pOne + y • frame.pTwo + (0 : ℝ) • frame.axis) ≠ 0 := by
  intro hzero
  have hpairing : (x • frame.pOne + y • frame.pTwo + (0 : ℝ) • frame.axis)
      ⬝ᵥ frame.pTwo = y := by
    have hAxisTwo : frame.axis ⬝ᵥ frame.pTwo = 0 := by
      rw [dotProduct_comm]; exact frame.twoAxis
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, frame.oneTwo, frame.twoTwo,
      hAxisTwo]
    ring
  rw [hzero, zero_dotProduct] at hpairing
  exact hy hpairing.symm

end AxisFrame

/-! ## Part 3 — the frame readings of a subset gap -/

/-- The gap form of a subset, read at two probes. -/
noncomputable def gapReading (design : WeightedDesign size 3) (selected : Finset (Fin size))
    (probeLeft probeRight : Fin 3 → ℝ) : ℝ :=
  probeLeft ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeRight)

/-- The gap reading is the subset moment less the probes' own pairing. -/
theorem gapReading_eq_sum (design : WeightedDesign size 3) (selected : Finset (Fin size))
    (probeLeft probeRight : Fin 3 → ℝ) :
    gapReading design selected probeLeft probeRight
      = (∑ label ∈ selected,
          (design.atom label ⬝ᵥ probeLeft) * (design.atom label ⬝ᵥ probeRight))
        - probeLeft ⬝ᵥ probeRight := by
  rw [gapReading, subsetSum, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    Matrix.sum_mulVec, dotProduct_sum]
  refine congrArg (fun total => total - probeLeft ⬝ᵥ probeRight) ?_
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
    dotProduct_comm probeLeft (design.atom label)]
  ring

/-- **THE RANK-ONE UPDATE OF A GAP READING.**  Adding an atom to a subset adds
the product of its two readings. -/
theorem gapReading_insert (design : WeightedDesign size 3) {selected : Finset (Fin size)}
    {newLabel : Fin size} (hnew : newLabel ∉ selected) (probeLeft probeRight : Fin 3 → ℝ) :
    gapReading design (insert newLabel selected) probeLeft probeRight
      = gapReading design selected probeLeft probeRight
        + (design.atom newLabel ⬝ᵥ probeLeft) * (design.atom newLabel ⬝ᵥ probeRight) := by
  rw [gapReading_eq_sum, gapReading_eq_sum, Finset.sum_insert hnew]
  ring

/-- The gap reading is symmetric in its two probes. -/
theorem gapReading_comm (design : WeightedDesign size 3) (selected : Finset (Fin size))
    (probeLeft probeRight : Fin 3 → ℝ) :
    gapReading design selected probeLeft probeRight
      = gapReading design selected probeRight probeLeft := by
  rw [gapReading_eq_sum, gapReading_eq_sum, dotProduct_comm probeLeft probeRight]
  refine congrArg (fun total => total - probeRight ⬝ᵥ probeLeft) ?_
  exact Finset.sum_congr rfl fun label _ => mul_comm _ _

/-- **THE GAP DETERMINANT FROM THE SIX FRAME READINGS.** -/
theorem det_gap_eq_frameDet (design : WeightedDesign size 3) (selected : Finset (Fin size))
    (frame : AxisFrame) :
    (subsetSum design selected - 1).det
      = frameDet (gapReading design selected frame.pOne frame.pOne)
          (gapReading design selected frame.pOne frame.pTwo)
          (gapReading design selected frame.pTwo frame.pTwo)
          (gapReading design selected frame.pOne frame.axis)
          (gapReading design selected frame.pTwo frame.axis)
          (gapReading design selected frame.axis frame.axis) := by
  rw [frameDet]
  exact det_eq_framePairing_det (transpose_gap_eq_gap design selected) frame.oneOne
    frame.twoTwo frame.axisAxis frame.oneTwo frame.oneAxis frame.twoAxis

/-- The gap quadratic form in frame coordinates. -/
theorem gapReading_frameCoordinates (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (frame : AxisFrame) (x y z : ℝ) :
    gapReading design selected (x • frame.pOne + y • frame.pTwo + z • frame.axis)
        (x • frame.pOne + y • frame.pTwo + z • frame.axis)
      = gapReading design selected frame.pOne frame.pOne * x ^ 2
        + 2 * gapReading design selected frame.pOne frame.pTwo * (x * y)
        + gapReading design selected frame.pTwo frame.pTwo * y ^ 2
        + 2 * gapReading design selected frame.pOne frame.axis * (x * z)
        + 2 * gapReading design selected frame.pTwo frame.axis * (y * z)
        + gapReading design selected frame.axis frame.axis * z ^ 2 :=
  quadForm_frameCoordinates (transpose_gap_eq_gap design selected) frame.pOne frame.pTwo
    frame.axis x y z

/-! ## Part 4 — plane strictness and the two signs it fixes -/

/-- **A PLANE-STRICT PAIR.**  Two atoms whose readings beat every nonzero probe of
the axis plane.  This is the conclusion shape of
`Gtz.exists_planeStrictPair_of_transversalAxis`. -/
def PlaneStrictPair (design : WeightedDesign size 3) (axis : Fin 3 → ℝ)
    (strongLabel otherLabel : Fin size) : Prop :=
  ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
    planar ⬝ᵥ planar
      < (design.atom strongLabel ⬝ᵥ planar) ^ 2 + (design.atom otherLabel ⬝ᵥ planar) ^ 2

/-- A plane-strict pair makes the gap of every subset that contains it positive on
the plane.  The atoms outside the pair only add squares. -/
theorem gapReading_pos_of_planeStrictPair (design : WeightedDesign size 3)
    {selected : Finset (Fin size)} {axis : Fin 3 → ℝ} {strongLabel otherLabel : Fin size}
    (hne : strongLabel ≠ otherLabel) (hstrong : strongLabel ∈ selected)
    (hother : otherLabel ∈ selected)
    (hstrict : PlaneStrictPair design axis strongLabel otherLabel)
    {planar : Fin 3 → ℝ} (hperp : planar ⬝ᵥ axis = 0) (hplanarNe : planar ≠ 0) :
    0 < gapReading design selected planar planar := by
  classical
  have hsubset : ({strongLabel, otherLabel} : Finset (Fin size)) ⊆ selected := by
    intro label hlabel
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
    rcases hlabel with rfl | rfl
    · exact hstrong
    · exact hother
  have hpairSum : ∑ label ∈ ({strongLabel, otherLabel} : Finset (Fin size)),
      (design.atom label ⬝ᵥ planar) * (design.atom label ⬝ᵥ planar)
      = (design.atom strongLabel ⬝ᵥ planar) ^ 2
        + (design.atom otherLabel ⬝ᵥ planar) ^ 2 := by
    rw [Finset.sum_pair hne]
    ring
  have hmono : ∑ label ∈ ({strongLabel, otherLabel} : Finset (Fin size)),
      (design.atom label ⬝ᵥ planar) * (design.atom label ⬝ᵥ planar)
      ≤ ∑ label ∈ selected,
        (design.atom label ⬝ᵥ planar) * (design.atom label ⬝ᵥ planar) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      fun label _ _ => mul_self_nonneg (design.atom label ⬝ᵥ planar)
  have hstrictValue := hstrict planar hperp hplanarNe
  rw [gapReading_eq_sum]
  rw [hpairSum] at hmono
  linarith

/-- The first plane reading of a subset through a plane-strict pair is positive. -/
theorem gapReading_pOne_pos_of_planeStrictPair (design : WeightedDesign size 3)
    {selected : Finset (Fin size)} (frame : AxisFrame) {strongLabel otherLabel : Fin size}
    (hne : strongLabel ≠ otherLabel) (hstrong : strongLabel ∈ selected)
    (hother : otherLabel ∈ selected)
    (hstrict : PlaneStrictPair design frame.axis strongLabel otherLabel) :
    0 < gapReading design selected frame.pOne frame.pOne :=
  gapReading_pos_of_planeStrictPair design hne hstrong hother hstrict frame.oneAxis
    frame.pOne_ne_zero

/-- **THE PLANE BLOCK IS POSITIVE DEFINITE.**  Evaluating the plane form at the
Schur direction turns plane strictness into a positive plane block determinant. -/
theorem frameBlockDet_pos_of_planeStrictPair (design : WeightedDesign size 3)
    {selected : Finset (Fin size)} (frame : AxisFrame) {strongLabel otherLabel : Fin size}
    (hne : strongLabel ≠ otherLabel) (hstrong : strongLabel ∈ selected)
    (hother : otherLabel ∈ selected)
    (hstrict : PlaneStrictPair design frame.axis strongLabel otherLabel) :
    0 < frameBlockDet (gapReading design selected frame.pOne frame.pOne)
      (gapReading design selected frame.pOne frame.pTwo)
      (gapReading design selected frame.pTwo frame.pTwo) := by
  set aa := gapReading design selected frame.pOne frame.pOne with haaDef
  set bb := gapReading design selected frame.pOne frame.pTwo with hbbDef
  set cc := gapReading design selected frame.pTwo frame.pTwo with hccDef
  have haaPos : 0 < aa := gapReading_pOne_pos_of_planeStrictPair design frame hne hstrong
    hother hstrict
  have hschurValue : 0 < gapReading design selected
      ((-bb) • frame.pOne + aa • frame.pTwo + (0 : ℝ) • frame.axis)
      ((-bb) • frame.pOne + aa • frame.pTwo + (0 : ℝ) • frame.axis) :=
    gapReading_pos_of_planeStrictPair design hne hstrong hother hstrict
      (frame.planeCombination_dotProduct_axis (-bb) aa)
      (frame.planeCombination_ne_zero haaPos.ne')
  rw [gapReading_frameCoordinates design selected frame (-bb) aa 0, ← haaDef, ← hbbDef,
    ← hccDef] at hschurValue
  have hproduct : 0 < aa * frameBlockDet aa bb cc := by
    rw [frameBlockDet]
    nlinarith [hschurValue]
  nlinarith [hproduct, haaPos]

/-- **THE PAIR'S OWN SCHUR COMPLEMENT IS STRICTLY NEGATIVE.**  A pair never weakly
dominates at rank three, so its gap is negative in the direction orthogonal to both
atoms.  With a positive definite plane block the LDL sum of squares then forces the
gap determinant strictly below zero. -/
theorem frameDet_pair_neg_of_planeStrictPair (design : WeightedDesign size 3)
    (frame : AxisFrame) {strongLabel otherLabel : Fin size} (hne : strongLabel ≠ otherLabel)
    (hstrict : PlaneStrictPair design frame.axis strongLabel otherLabel) :
    frameDet (gapReading design {strongLabel, otherLabel} frame.pOne frame.pOne)
      (gapReading design {strongLabel, otherLabel} frame.pOne frame.pTwo)
      (gapReading design {strongLabel, otherLabel} frame.pTwo frame.pTwo)
      (gapReading design {strongLabel, otherLabel} frame.pOne frame.axis)
      (gapReading design {strongLabel, otherLabel} frame.pTwo frame.axis)
      (gapReading design {strongLabel, otherLabel} frame.axis frame.axis) < 0 := by
  classical
  set pairSet : Finset (Fin size) := {strongLabel, otherLabel} with hpairDef
  have hstrongMem : strongLabel ∈ pairSet := by simp [hpairDef]
  have hotherMem : otherLabel ∈ pairSet := by simp [hpairDef]
  set aa := gapReading design pairSet frame.pOne frame.pOne with haaDef
  set bb := gapReading design pairSet frame.pOne frame.pTwo with hbbDef
  set cc := gapReading design pairSet frame.pTwo frame.pTwo with hccDef
  set dd := gapReading design pairSet frame.pOne frame.axis with hddDef
  set ee := gapReading design pairSet frame.pTwo frame.axis with heeDef
  set ff := gapReading design pairSet frame.axis frame.axis with hffDef
  have haaPos : 0 < aa := gapReading_pOne_pos_of_planeStrictPair design frame hne hstrongMem
    hotherMem hstrict
  have hblockPos : 0 < frameBlockDet aa bb cc :=
    frameBlockDet_pos_of_planeStrictPair design frame hne hstrongMem hotherMem hstrict
  obtain ⟨witness, hwitnessNe, hstrongZero, hotherZero⟩ :=
    exists_ne_zero_dotProduct_pair_eq_zero (design.atom strongLabel) (design.atom otherLabel)
  have hwitnessPos : 0 < witness ⬝ᵥ witness := dotProduct_self_pos hwitnessNe
  have hgapNeg : gapReading design pairSet witness witness < 0 := by
    rw [gapReading_eq_sum, hpairDef, Finset.sum_pair hne, hstrongZero, hotherZero]
    linarith
  have hresolve := orthonormalFrame_resolution frame.oneOne frame.twoTwo frame.axisAxis
    frame.oneTwo frame.oneAxis frame.twoAxis witness
  set xcoord := witness ⬝ᵥ frame.pOne with hxDef
  set ycoord := witness ⬝ᵥ frame.pTwo with hyDef
  set zcoord := witness ⬝ᵥ frame.axis with hzDef
  have hform : gapReading design pairSet witness witness
      = aa * xcoord ^ 2 + 2 * bb * (xcoord * ycoord) + cc * ycoord ^ 2
        + 2 * dd * (xcoord * zcoord) + 2 * ee * (ycoord * zcoord) + ff * zcoord ^ 2 := by
    conv_lhs => rw [hresolve]
    rw [gapReading_frameCoordinates design pairSet frame xcoord ycoord zcoord, ← haaDef,
      ← hbbDef, ← hccDef, ← hddDef, ← heeDef, ← hffDef]
  have hldl := ldl_clearing_identity aa bb cc dd ee ff xcoord ycoord zcoord
  rw [← hform] at hldl
  have hblockRaw : 0 < aa * cc - bb ^ 2 := by
    have hcopy := hblockPos
    rwa [frameBlockDet] at hcopy
  have hleftNeg : aa * (aa * cc - bb ^ 2) * gapReading design pairSet witness witness < 0 :=
    mul_neg_of_pos_of_neg (mul_pos haaPos hblockRaw) hgapNeg
  have hdetTerm : aa * frameDet aa bb cc dd ee ff * zcoord ^ 2 < 0 := by
    rw [frameDet]
    nlinarith [hldl, hleftNeg, sq_nonneg (aa * xcoord + bb * ycoord + dd * zcoord),
      sq_nonneg ((aa * cc - bb ^ 2) * ycoord + (aa * ee - bb * dd) * zcoord),
      mul_nonneg hblockRaw.le (sq_nonneg (aa * xcoord + bb * ycoord + dd * zcoord))]
  by_contra hnonneg
  push Not at hnonneg
  have hproduct : 0 ≤ aa * frameDet aa bb cc dd ee ff * zcoord ^ 2 :=
    mul_nonneg (mul_nonneg haaPos.le hnonneg) (sq_nonneg zcoord)
  linarith

/-! ## Part 5 — the tie's two-parameter scalar family -/

/-- The three-element subset through a pair, written as an insertion. -/
theorem tripleSet_eq_insert {labelOne labelTwo labelThree : Fin size} :
    ({labelOne, labelTwo, labelThree} : Finset (Fin size))
      = insert labelThree ({labelOne, labelTwo} : Finset (Fin size)) := by
  classical
  ext label
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **THE SCALAR FAMILY AT A TIE.**  At a tie, along every plane-strict pair and
for every third atom, the Schur reading is capped by the pair's own determinant
deficit against the updated plane block.  The tree's gate supplies
`det(triple) <= 0`; the rank-one update turns it into this square. -/
theorem sq_schurProbe_reading_le_of_isTie (design : WeightedDesign size 3)
    (htie : IsTie design) (frame : AxisFrame)
    {strongLabel otherLabel thirdLabel : Fin size} (hne : strongLabel ≠ otherLabel)
    (hneStrongThird : strongLabel ≠ thirdLabel) (hneOtherThird : otherLabel ≠ thirdLabel)
    (hstrict : PlaneStrictPair design frame.axis strongLabel otherLabel) :
    (design.atom thirdLabel ⬝ᵥ frame.axis
          * frameBlockDet (gapReading design {strongLabel, otherLabel} frame.pOne frame.pOne)
              (gapReading design {strongLabel, otherLabel} frame.pOne frame.pTwo)
              (gapReading design {strongLabel, otherLabel} frame.pTwo frame.pTwo)
        - frameBeta (gapReading design {strongLabel, otherLabel} frame.pOne frame.pOne)
              (gapReading design {strongLabel, otherLabel} frame.pOne frame.pTwo)
              (gapReading design {strongLabel, otherLabel} frame.pTwo frame.pTwo)
              (gapReading design {strongLabel, otherLabel} frame.pOne frame.axis)
              (gapReading design {strongLabel, otherLabel} frame.pTwo frame.axis)
              (design.atom thirdLabel ⬝ᵥ frame.pOne)
              (design.atom thirdLabel ⬝ᵥ frame.pTwo)) ^ 2
      ≤ (- frameDet (gapReading design {strongLabel, otherLabel} frame.pOne frame.pOne)
              (gapReading design {strongLabel, otherLabel} frame.pOne frame.pTwo)
              (gapReading design {strongLabel, otherLabel} frame.pTwo frame.pTwo)
              (gapReading design {strongLabel, otherLabel} frame.pOne frame.axis)
              (gapReading design {strongLabel, otherLabel} frame.pTwo frame.axis)
              (gapReading design {strongLabel, otherLabel} frame.axis frame.axis))
        * (frameBlockDet (gapReading design {strongLabel, otherLabel} frame.pOne frame.pOne)
              (gapReading design {strongLabel, otherLabel} frame.pOne frame.pTwo)
              (gapReading design {strongLabel, otherLabel} frame.pTwo frame.pTwo)
            + frameAlpha
              (gapReading design {strongLabel, otherLabel} frame.pOne frame.pOne)
              (gapReading design {strongLabel, otherLabel} frame.pOne frame.pTwo)
              (gapReading design {strongLabel, otherLabel} frame.pTwo frame.pTwo)
              (design.atom thirdLabel ⬝ᵥ frame.pOne)
              (design.atom thirdLabel ⬝ᵥ frame.pTwo)) := by
  classical
  set pairSet : Finset (Fin size) := {strongLabel, otherLabel} with hpairDef
  have hstrongMem : strongLabel ∈ pairSet := by simp [hpairDef]
  have hotherMem : otherLabel ∈ pairSet := by simp [hpairDef]
  have hthirdNotMem : thirdLabel ∉ pairSet := by
    simp only [hpairDef, Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨Ne.symm hneStrongThird, Ne.symm hneOtherThird⟩
  set aa := gapReading design pairSet frame.pOne frame.pOne with haaDef
  set bb := gapReading design pairSet frame.pOne frame.pTwo with hbbDef
  set cc := gapReading design pairSet frame.pTwo frame.pTwo with hccDef
  set dd := gapReading design pairSet frame.pOne frame.axis with hddDef
  set ee := gapReading design pairSet frame.pTwo frame.axis with heeDef
  set ff := gapReading design pairSet frame.axis frame.axis with hffDef
  set xcoord := design.atom thirdLabel ⬝ᵥ frame.pOne with hxDef
  set ycoord := design.atom thirdLabel ⬝ᵥ frame.pTwo with hyDef
  set zcoord := design.atom thirdLabel ⬝ᵥ frame.axis with hzDef
  have haaPos : 0 < aa := gapReading_pOne_pos_of_planeStrictPair design frame hne hstrongMem
    hotherMem hstrict
  have hblockPos : 0 < frameBlockDet aa bb cc :=
    frameBlockDet_pos_of_planeStrictPair design frame hne hstrongMem hotherMem hstrict
  have hpairNeg : frameDet aa bb cc dd ee ff < 0 :=
    frameDet_pair_neg_of_planeStrictPair design frame hne hstrict
  -- the triple's six readings are the pair's readings updated by one atom
  have hentry : ∀ probeLeft probeRight : Fin 3 → ℝ,
      gapReading design (insert thirdLabel pairSet) probeLeft probeRight
        = gapReading design pairSet probeLeft probeRight
          + (design.atom thirdLabel ⬝ᵥ probeLeft) * (design.atom thirdLabel ⬝ᵥ probeRight) :=
    fun probeLeft probeRight => gapReading_insert design hthirdNotMem probeLeft probeRight
  have htripleDet : (subsetSum design (insert thirdLabel pairSet) - 1).det
      = frameDet (aa + xcoord ^ 2) (bb + xcoord * ycoord) (cc + ycoord ^ 2)
          (dd + xcoord * zcoord) (ee + ycoord * zcoord) (ff + zcoord ^ 2) := by
    rw [det_gap_eq_frameDet design (insert thirdLabel pairSet) frame, hentry, hentry, hentry,
      hentry, hentry, hentry, ← haaDef, ← hbbDef, ← hccDef, ← hddDef, ← heeDef, ← hffDef,
      ← hxDef, ← hyDef, ← hzDef]
    ring_nf
  have hgate : (subsetSum design {strongLabel, otherLabel, thirdLabel} - 1).det ≤ 0 :=
    det_gap_nonpos_of_isTie_of_pairPlaneStrict design htie frame.oneOne frame.twoTwo
      frame.axisAxis frame.oneTwo frame.oneAxis frame.twoAxis hne hneStrongThird
      hneOtherThird hstrict
  rw [tripleSet_eq_insert, ← hpairDef, htripleDet] at hgate
  have hupdate := frameDet_rankOne aa bb cc dd ee ff xcoord ycoord zcoord
  have hnewBlock : frameBlockDet (aa + xcoord ^ 2) (bb + xcoord * ycoord) (cc + ycoord ^ 2)
      = frameBlockDet aa bb cc + frameAlpha aa bb cc xcoord ycoord :=
    frameBlockDet_rankOne aa bb cc xcoord ycoord
  rw [hnewBlock] at hupdate
  have hleftNonpos : frameBlockDet aa bb cc
      * frameDet (aa + xcoord ^ 2) (bb + xcoord * ycoord) (cc + ycoord ^ 2)
          (dd + xcoord * zcoord) (ee + ycoord * zcoord) (ff + zcoord ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hblockPos.le hgate
  linarith [hupdate, hleftNonpos]

/-! ## Part 6 — the shadow's leverage, and a plane-strict pair with no genericity -/

/-- The shadow design keeps the design's own weights. -/
theorem planarCompressionDesign_weight (design : WeightedDesign size 3) (frame : AxisFrame)
    (label : Fin size) :
    (planarCompressionDesign design frame.pOne frame.pTwo frame.oneOne frame.twoTwo
      frame.oneTwo).weight label = design.weight label := rfl

/-- **THE SHADOW LEVERAGE.**  Compression spends exactly the atom's axis mass. -/
theorem leverageOf_planarCompressionDesign_atom (design : WeightedDesign size 3)
    (frame : AxisFrame) (label : Fin size) :
    leverageOf ((planarCompressionDesign design frame.pOne frame.pTwo frame.oneOne
        frame.twoTwo frame.oneTwo).atom label)
      = leverageOf (design.atom label) - (design.atom label ⬝ᵥ frame.axis) ^ 2 := by
  have hsplit := frame.dotProduct_self_split (design.atom label)
  have hleverage : leverageOf (design.atom label) = design.atom label ⬝ᵥ design.atom label := by
    rw [leverageOf, dotProduct]
    exact Finset.sum_congr rfl fun coord _ => pow_two (design.atom label coord)
  rw [planarCompressionDesign_atom, leverageOf, hleverage, hsplit]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **THE READBACK.**  A strictly dominating pair of the shadow design is a
plane-strict pair of the design.  Frame completeness carries a two-dimensional
probe up to a plane probe and back. -/
theorem planeStrictPair_of_posDef_compression (design : WeightedDesign size 3)
    (frame : AxisFrame) {strongLabel otherLabel : Fin size} (hne : strongLabel ≠ otherLabel)
    (hposDef : (subsetSum (planarCompressionDesign design frame.pOne frame.pTwo frame.oneOne
        frame.twoTwo frame.oneTwo) {strongLabel, otherLabel} - 1).PosDef) :
    PlaneStrictPair design frame.axis strongLabel otherLabel := by
  classical
  set companion := planarCompressionDesign design frame.pOne frame.pTwo frame.oneOne
    frame.twoTwo frame.oneTwo with hcompanionDef
  intro planar hperp hplanarNe
  have hexpand := orthonormalFrame_resolution frame.oneOne frame.twoTwo frame.axisAxis
    frame.oneTwo frame.oneAxis frame.twoAxis planar
  rw [hperp, zero_smul, add_zero] at hexpand
  set testVec : Fin 2 → ℝ := ![planar ⬝ᵥ frame.pOne, planar ⬝ᵥ frame.pTwo] with htestDef
  have htestNe : testVec ≠ 0 := by
    intro hzero
    have hcoordOne : planar ⬝ᵥ frame.pOne = 0 := by
      have hcomponent := congrFun hzero 0
      simpa [htestDef] using hcomponent
    have hcoordTwo : planar ⬝ᵥ frame.pTwo = 0 := by
      have hcomponent := congrFun hzero 1
      simpa [htestDef] using hcomponent
    rw [hcoordOne, hcoordTwo, zero_smul, zero_smul, zero_add] at hexpand
    exact hplanarNe hexpand
  have hquad := quadForm_gt_of_posDef_pair companion {strongLabel, otherLabel} hposDef
    testVec htestNe
  rw [Finset.sum_pair hne] at hquad
  have hatomPairing : ∀ label : Fin size,
      companion.atom label ⬝ᵥ testVec = design.atom label ⬝ᵥ planar := by
    intro label
    conv_rhs => rw [hexpand]
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hcompanionDef,
      planarCompressionDesign_atom, htestDef]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      smul_eq_mul]
    ring
  have hnormSplit : testVec ⬝ᵥ testVec = planar ⬝ᵥ planar := by
    have hfull := frame.dotProduct_self_split planar
    rw [hperp] at hfull
    have htestValue : testVec ⬝ᵥ testVec
        = (planar ⬝ᵥ frame.pOne) ^ 2 + (planar ⬝ᵥ frame.pTwo) ^ 2 := by
      rw [htestDef]
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [htestValue, hfull]
    ring
  rw [hatomPairing strongLabel, hatomPairing otherLabel, hnormSplit] at hquad
  exact hquad

/-- **A PLANE-STRICT PAIR WITH NO GENERICITY.**  An atom whose SHADOW leverage
passes the Nesterenko threshold forces a plane-strict pair through that atom, along
that very axis.  No transversality, no four labels, no moment curve. -/
theorem exists_planeStrictPair_of_shadowNesterenkoExcess (design : WeightedDesign size 3)
    (frame : AxisFrame) (pivotLabel : Fin size)
    (hexcess : 1 + design.weight pivotLabel
      < 2 * design.weight pivotLabel
          * (leverageOf (design.atom pivotLabel)
            - (design.atom pivotLabel ⬝ᵥ frame.axis) ^ 2)) :
    ∃ partnerLabel : Fin size, partnerLabel ≠ pivotLabel
      ∧ PlaneStrictPair design frame.axis pivotLabel partnerLabel := by
  classical
  set companion := planarCompressionDesign design frame.pOne frame.pTwo frame.oneOne
    frame.twoTwo frame.oneTwo with hcompanionDef
  have hcompanionExcess : 1 + companion.weight pivotLabel
      < 2 * companion.weight pivotLabel * leverageOf (companion.atom pivotLabel) := by
    rw [hcompanionDef, planarCompressionDesign_weight design frame pivotLabel,
      leverageOf_planarCompressionDesign_atom design frame pivotLabel]
    exact hexcess
  obtain ⟨partnerLabel, hpartnerNe, hposDef⟩ :=
    exists_posDef_pair_of_nesterenkoExcess companion pivotLabel hcompanionExcess
  exact ⟨partnerLabel, hpartnerNe,
    planeStrictPair_of_posDef_compression design frame (Ne.symm hpartnerNe) hposDef⟩

/-- A unit axis orthogonal to a nonzero vector. -/
theorem exists_unitAxis_dotProduct_eq_zero {vec : Fin 3 → ℝ} (hne : vec ≠ 0) :
    ∃ unitAxis : Fin 3 → ℝ, unitAxis ⬝ᵥ unitAxis = 1 ∧ vec ⬝ᵥ unitAxis = 0 := by
  have hpos : 0 < vec ⬝ᵥ vec := dotProduct_self_pos hne
  set scale := (Real.sqrt (vec ⬝ᵥ vec))⁻¹ with hscaleDef
  have hsqrtPos : 0 < Real.sqrt (vec ⬝ᵥ vec) := Real.sqrt_pos.mpr hpos
  have hunitSeed : (scale • vec) ⬝ᵥ (scale • vec) = 1 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hscaleDef]
    field_simp
    rw [Real.sq_sqrt hpos.le]
  obtain ⟨pOne, pTwo, hOneOne, _, _, hOneAxis, _⟩ := exists_orthonormal_planarFrame hunitSeed
  refine ⟨pOne, hOneOne, ?_⟩
  have hscaleNe : scale ≠ 0 := by
    rw [hscaleDef]
    exact inv_ne_zero hsqrtPos.ne'
  have hpairing : pOne ⬝ᵥ (scale • vec) = 0 := hOneAxis
  rw [dotProduct_smul, smul_eq_mul] at hpairing
  rcases mul_eq_zero.mp hpairing with hbad | hgood
  · exact absurd hbad hscaleNe
  · rw [dotProduct_comm]
    exact hgood

/-- **THE CAP FIRES WITHOUT GENERICITY.**  An atom of a rank-three design whose
weighted leverage passes the Nesterenko threshold `1 + t_d < 2 t_d l_d` admits a
plane through it that carries a plane-strict pair.  The axis is produced, not
assumed, and the design needs no simplicity and no transversality.

Measured at the `(5,3)` diamond: the four rim atoms read `t (2 l - 1) = 1.1`,
above the threshold `1`, so the hypothesis is not vacuous at a genuine tie. -/
theorem exists_unitAxis_planeStrictPair_of_nesterenkoExcess (design : WeightedDesign size 3)
    (pivotLabel : Fin size)
    (hexcess : 1 + design.weight pivotLabel
      < 2 * design.weight pivotLabel * leverageOf (design.atom pivotLabel)) :
    ∃ unitAxis : Fin 3 → ℝ, unitAxis ⬝ᵥ unitAxis = 1
      ∧ design.atom pivotLabel ⬝ᵥ unitAxis = 0
      ∧ ∃ partnerLabel : Fin size, partnerLabel ≠ pivotLabel
          ∧ PlaneStrictPair design unitAxis pivotLabel partnerLabel := by
  classical
  have hheavy : 1 < leverageOf (design.atom pivotLabel) :=
    one_lt_leverage_of_nesterenkoExcess design pivotLabel hexcess
  have hatomNe : design.atom pivotLabel ≠ 0 := by
    intro hzero
    rw [hzero] at hheavy
    simp only [leverageOf, Pi.zero_apply] at hheavy
    norm_num at hheavy
  obtain ⟨unitAxis, hunit, hperp⟩ := exists_unitAxis_dotProduct_eq_zero hatomNe
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩ :=
    exists_orthonormal_planarFrame hunit
  set frame : AxisFrame :=
    { pOne := pOne, pTwo := pTwo, axis := unitAxis, oneOne := hOneOne, twoTwo := hTwoTwo,
      axisAxis := hunit, oneTwo := hOneTwo, oneAxis := hOneAxis, twoAxis := hTwoAxis }
    with hframeDef
  have hshadowExcess : 1 + design.weight pivotLabel
      < 2 * design.weight pivotLabel
          * (leverageOf (design.atom pivotLabel)
            - (design.atom pivotLabel ⬝ᵥ frame.axis) ^ 2) := by
    have haxisValue : design.atom pivotLabel ⬝ᵥ frame.axis = 0 := hperp
    rw [haxisValue]
    simpa using hexcess
  obtain ⟨partnerLabel, hpartnerNe, hstrict⟩ :=
    exists_planeStrictPair_of_shadowNesterenkoExcess design frame pivotLabel hshadowExcess
  exact ⟨unitAxis, hunit, hperp, partnerLabel, hpartnerNe, hstrict⟩

/-! ## Part 7 — the determinant dictionary, and plane strictness as admissibility

The frame machinery meets the tree's Sylvester vocabulary here.  A pair's gap
determinant is MINUS its pair minor and a triple's gap determinant IS its third
Sylvester minor, so the negative sign proved in Part 4 says exactly that a
plane-strict pair is an ADMISSIBLE pair in the sense of
`Gtz.AdmissiblePair`. -/

/-- The unweighted sum over a triple, unfolded. -/
theorem subsetSum_triple_rankThree (design : WeightedDesign size 3)
    {labelOne labelTwo labelThree : Fin size} (hOneTwo : labelOne ≠ labelTwo)
    (hOneThree : labelOne ≠ labelThree) (hTwoThree : labelTwo ≠ labelThree) :
    subsetSum design {labelOne, labelTwo, labelThree}
      = atomMatrix (design.atom labelOne) + atomMatrix (design.atom labelTwo)
        + atomMatrix (design.atom labelThree) := by
  classical
  rw [subsetSum, Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨hOneTwo, hOneThree⟩),
    Finset.sum_insert (by simpa using hTwoThree), Finset.sum_singleton, add_assoc]

/-- **THE PAIR GAP DETERMINANT IS MINUS THE PAIR MINOR.**  At rank three the pair
sum is singular, so its gap determinant carries the sign of the missing
direction. -/
theorem det_subsetSum_pairGap_eq_neg_pairGapMinor (design : WeightedDesign size 3)
    {strongLabel otherLabel : Fin size} (hne : strongLabel ≠ otherLabel) :
    (subsetSum design {strongLabel, otherLabel} - 1).det
      = - pairGapMinor (design.atom strongLabel) (design.atom otherLabel) := by
  rw [subsetSum_pair design hne, Matrix.det_fin_three, pairGapMinor]
  simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
    leverageOf, dotProduct, Fin.sum_univ_three, Matrix.one_apply, Fin.isValue]
  norm_num [Fin.ext_iff]
  ring

/-- **THE TRIPLE GAP DETERMINANT IS THE THIRD SYLVESTER MINOR.** -/
theorem det_subsetSum_tripleGap_eq_tripleGapDet (design : WeightedDesign size 3)
    {labelOne labelTwo labelThree : Fin size} (hOneTwo : labelOne ≠ labelTwo)
    (hOneThree : labelOne ≠ labelThree) (hTwoThree : labelTwo ≠ labelThree) :
    (subsetSum design {labelOne, labelTwo, labelThree} - 1).det
      = tripleGapDet (design.atom labelOne) (design.atom labelTwo)
          (design.atom labelThree) := by
  rw [subsetSum_triple_rankThree design hOneTwo hOneThree hTwoThree, Matrix.det_fin_three, tripleGapDet]
  simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
    leverageOf, dotProduct, Fin.sum_univ_three, Matrix.one_apply, Fin.isValue]
  norm_num [Fin.ext_iff]
  ring

/-- The second plane reading of a subset through a plane-strict pair is positive. -/
theorem gapReading_pTwo_pos_of_planeStrictPair (design : WeightedDesign size 3)
    {selected : Finset (Fin size)} (frame : AxisFrame) {strongLabel otherLabel : Fin size}
    (hne : strongLabel ≠ otherLabel) (hstrong : strongLabel ∈ selected)
    (hother : otherLabel ∈ selected)
    (hstrict : PlaneStrictPair design frame.axis strongLabel otherLabel) :
    0 < gapReading design selected frame.pTwo frame.pTwo :=
  gapReading_pos_of_planeStrictPair design hne hstrong hother hstrict frame.twoAxis
    frame.pTwo_ne_zero

/-- **PLANE STRICTNESS IS ADMISSIBILITY.**  A pair that beats the axis plane has a
strictly positive pair minor, so it is an admissible pair of the Sylvester chain.
This is the bridge from the shadow to `Gtz.AdmissiblePair`. -/
theorem admissiblePair_of_planeStrictPair (design : WeightedDesign size 3)
    (frame : AxisFrame) {strongLabel otherLabel : Fin size} (hne : strongLabel ≠ otherLabel)
    (hstrict : PlaneStrictPair design frame.axis strongLabel otherLabel) :
    AdmissiblePair (design.atom strongLabel) (design.atom otherLabel) := by
  have hframeNeg := frameDet_pair_neg_of_planeStrictPair design frame hne hstrict
  have hdetValue := det_gap_eq_frameDet design ({strongLabel, otherLabel} : Finset (Fin size))
    frame
  have hdictionary := det_subsetSum_pairGap_eq_neg_pairGapMinor design hne
  rw [hdetValue] at hdictionary
  rw [AdmissiblePair]
  linarith

/-- **PLANE STRICTNESS FORCES BOTH ATOMS STRICTLY HEAVY.**  The plane block's trace
is positive, so the two leverages together beat two, and a positive pair minor
then puts both of them above one. -/
theorem one_lt_leverage_of_planeStrictPair (design : WeightedDesign size 3)
    (frame : AxisFrame) {strongLabel otherLabel : Fin size} (hne : strongLabel ≠ otherLabel)
    (hstrict : PlaneStrictPair design frame.axis strongLabel otherLabel) :
    1 < leverageOf (design.atom strongLabel) ∧ 1 < leverageOf (design.atom otherLabel) := by
  classical
  set pairSet : Finset (Fin size) := {strongLabel, otherLabel} with hpairDef
  have hstrongMem : strongLabel ∈ pairSet := by simp [hpairDef]
  have hotherMem : otherLabel ∈ pairSet := by simp [hpairDef]
  have haaPos : 0 < gapReading design pairSet frame.pOne frame.pOne :=
    gapReading_pOne_pos_of_planeStrictPair design frame hne hstrongMem hotherMem hstrict
  have hccPos : 0 < gapReading design pairSet frame.pTwo frame.pTwo :=
    gapReading_pTwo_pos_of_planeStrictPair design frame hne hstrongMem hotherMem hstrict
  have hsplitStrong := frame.dotProduct_self_split (design.atom strongLabel)
  have hsplitOther := frame.dotProduct_self_split (design.atom otherLabel)
  have hlevStrong : leverageOf (design.atom strongLabel)
      = design.atom strongLabel ⬝ᵥ design.atom strongLabel := leverageOf_eq_dotProduct _
  have hlevOther : leverageOf (design.atom otherLabel)
      = design.atom otherLabel ⬝ᵥ design.atom otherLabel := leverageOf_eq_dotProduct _
  have haaValue : gapReading design pairSet frame.pOne frame.pOne
      = (design.atom strongLabel ⬝ᵥ frame.pOne) ^ 2
        + (design.atom otherLabel ⬝ᵥ frame.pOne) ^ 2 - 1 := by
    rw [gapReading_eq_sum, hpairDef, Finset.sum_pair hne, frame.oneOne]
    ring
  have hccValue : gapReading design pairSet frame.pTwo frame.pTwo
      = (design.atom strongLabel ⬝ᵥ frame.pTwo) ^ 2
        + (design.atom otherLabel ⬝ᵥ frame.pTwo) ^ 2 - 1 := by
    rw [gapReading_eq_sum, hpairDef, Finset.sum_pair hne, frame.twoTwo]
    ring
  rw [haaValue] at haaPos
  rw [hccValue] at hccPos
  have hmassSum : 2 < leverageOf (design.atom strongLabel) + leverageOf (design.atom otherLabel) := by
    rw [hlevStrong, hlevOther, hsplitStrong, hsplitOther]
    nlinarith [haaPos, hccPos, sq_nonneg (design.atom strongLabel ⬝ᵥ frame.axis),
      sq_nonneg (design.atom otherLabel ⬝ᵥ frame.axis)]
  have hminor := admissiblePair_of_planeStrictPair design frame hne hstrict
  rw [AdmissiblePair, pairGapMinor] at hminor
  constructor
  · nlinarith [hminor, hmassSum, sq_nonneg (design.atom strongLabel ⬝ᵥ design.atom otherLabel)]
  · nlinarith [hminor, hmassSum, sq_nonneg (design.atom strongLabel ⬝ᵥ design.atom otherLabel)]

/-- **AN ADMISSIBLE PAIR EXISTS AT EVERY SIMPLE DESIGN.**  Four distinct labels and
no parallel pair produce a plane, a pair that beats it, and hence an admissible
heavy pair of the Sylvester chain.  The axis is produced by the tree's moment
curve, so nothing is assumed beyond simplicity. -/
theorem exists_admissiblePair_of_not_hasParallelPair (design : WeightedDesign size 3)
    (hsimple : ¬ HasParallelPair design)
    {labelOne labelTwo labelThree labelFour : Fin size}
    (hneOneTwo : labelOne ≠ labelTwo) (hneOneThree : labelOne ≠ labelThree)
    (hneOneFour : labelOne ≠ labelFour) (hneTwoThree : labelTwo ≠ labelThree)
    (hneTwoFour : labelTwo ≠ labelFour) (hneThreeFour : labelThree ≠ labelFour) :
    ∃ strongLabel otherLabel : Fin size, strongLabel ≠ otherLabel
      ∧ AdmissiblePair (design.atom strongLabel) (design.atom otherLabel)
      ∧ 1 < leverageOf (design.atom strongLabel)
      ∧ 1 < leverageOf (design.atom otherLabel) := by
  obtain ⟨unitAxis, hunit, strongLabel, otherLabel, hlabelNe, hstrict⟩ :=
    exists_unitAxis_planeStrictPair_of_not_hasParallelPair design hsimple hneOneTwo
      hneOneThree hneOneFour hneTwoThree hneTwoFour hneThreeFour
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩ :=
    exists_orthonormal_planarFrame hunit
  set frame : AxisFrame :=
    { pOne := pOne, pTwo := pTwo, axis := unitAxis, oneOne := hOneOne, twoTwo := hTwoTwo,
      axisAxis := hunit, oneTwo := hOneTwo, oneAxis := hOneAxis, twoAxis := hTwoAxis }
    with hframeDef
  have hplaneStrict : PlaneStrictPair design frame.axis strongLabel otherLabel := hstrict
  obtain ⟨hheavyStrong, hheavyOther⟩ :=
    one_lt_leverage_of_planeStrictPair design frame hlabelNe hplaneStrict
  exact ⟨strongLabel, otherLabel, hlabelNe,
    admissiblePair_of_planeStrictPair design frame hlabelNe hplaneStrict,
    hheavyStrong, hheavyOther⟩

/-- **AN ADMISSIBLE PAIR FROM THE NESTERENKO EXCESS, WITH NO SIMPLICITY.**  An atom
whose weighted leverage passes the threshold sits in an admissible heavy pair.  No
parallel-freeness, no four labels, no genericity. -/
theorem exists_admissiblePair_of_nesterenkoExcess (design : WeightedDesign size 3)
    (pivotLabel : Fin size)
    (hexcess : 1 + design.weight pivotLabel
      < 2 * design.weight pivotLabel * leverageOf (design.atom pivotLabel)) :
    ∃ partnerLabel : Fin size, partnerLabel ≠ pivotLabel
      ∧ AdmissiblePair (design.atom pivotLabel) (design.atom partnerLabel)
      ∧ 1 < leverageOf (design.atom partnerLabel) := by
  obtain ⟨unitAxis, hunit, _, partnerLabel, hpartnerNe, hstrict⟩ :=
    exists_unitAxis_planeStrictPair_of_nesterenkoExcess design pivotLabel hexcess
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩ :=
    exists_orthonormal_planarFrame hunit
  set frame : AxisFrame :=
    { pOne := pOne, pTwo := pTwo, axis := unitAxis, oneOne := hOneOne, twoTwo := hTwoTwo,
      axisAxis := hunit, oneTwo := hOneTwo, oneAxis := hOneAxis, twoAxis := hTwoAxis }
    with hframeDef
  have hplaneStrict : PlaneStrictPair design frame.axis pivotLabel partnerLabel := hstrict
  exact ⟨partnerLabel, hpartnerNe,
    admissiblePair_of_planeStrictPair design frame (Ne.symm hpartnerNe) hplaneStrict,
    (one_lt_leverage_of_planeStrictPair design frame (Ne.symm hpartnerNe) hplaneStrict).2⟩

/-! ## Part 8 — the pair-normal factorization of the third Sylvester minor

Everything above runs in a frame.  This part removes the frame.  Put the axis
along the pair's own normal.  Then the plane block determinant becomes the pair
minor itself, the Schur probe becomes the normal scaled by the pair minor, and the
rank-one update of Part 1 turns into a POLYNOMIAL IDENTITY in the six pair
readings of a triple.  Nothing here mentions a design, an axis, or a matrix. -/

/-- **THE PAIR-NORMAL DEFECT.**  The plane adjugate form of the pair, read at the
third atom and cleared by the pair's squared area.  It is the exact amount by which
a triple's third Sylvester minor falls short of the pair-normal ceiling. -/
noncomputable def pairNormalDefect (a b c : Fin 3 → ℝ) : ℝ :=
  (leverageOf a + leverageOf b - 1)
      * (crossNormSq a b * leverageOf c - tripleBracket a b c ^ 2)
    - crossNormSq a b * ((a ⬝ᵥ c) ^ 2 + (b ⬝ᵥ c) ^ 2)

/-- **THE DEFECT IS A BINARY QUADRATIC** in the third atom's two readings against
the pair.  This is the form its sign is read from. -/
theorem pairNormalDefect_eq_quadraticForm (a b c : Fin 3 → ℝ) :
    pairNormalDefect a b c
      = ((leverageOf a + leverageOf b - 1) * leverageOf b - crossNormSq a b) * (a ⬝ᵥ c) ^ 2
        - 2 * ((leverageOf a + leverageOf b - 1) * (a ⬝ᵥ b)) * ((a ⬝ᵥ c) * (b ⬝ᵥ c))
        + ((leverageOf a + leverageOf b - 1) * leverageOf a - crossNormSq a b)
            * (b ⬝ᵥ c) ^ 2 := by
  rw [pairNormalDefect, sq_tripleBracket_eq_gramDet, crossNormSq_eq_leverage_mul_sub_sq]
  ring

/-- **THE DEFECT IN BRACKET VOCABULARY.**  The two mixed brackets of the third atom
against the pair, plus the squared volume, less the squared area times the third
leverage. -/
theorem pairNormalDefect_eq_bracketForm (a b c : Fin 3 → ℝ) :
    pairNormalDefect a b c
      = (leverageOf a * (b ⬝ᵥ c) - (a ⬝ᵥ b) * (a ⬝ᵥ c)) ^ 2
        + ((a ⬝ᵥ b) * (b ⬝ᵥ c) - leverageOf b * (a ⬝ᵥ c)) ^ 2
        + tripleBracket a b c ^ 2 - crossNormSq a b * leverageOf c := by
  rw [pairNormalDefect, sq_tripleBracket_eq_gramDet, crossNormSq_eq_leverage_mul_sub_sq]
  ring

/-- The leading coefficient of the defect's quadratic is a square plus a leverage
excess. -/
theorem pairNormalDefect_leadingCoeff (a b : Fin 3 → ℝ) :
    (leverageOf a + leverageOf b - 1) * leverageOf b - crossNormSq a b
      = leverageOf b * (leverageOf b - 1) + (a ⬝ᵥ b) ^ 2 := by
  rw [crossNormSq_eq_leverage_mul_sub_sq]
  ring

/-- The trailing coefficient of the defect's quadratic, the same statement with the
two atoms interchanged. -/
theorem pairNormalDefect_trailingCoeff (a b : Fin 3 → ℝ) :
    (leverageOf a + leverageOf b - 1) * leverageOf a - crossNormSq a b
      = leverageOf a * (leverageOf a - 1) + (a ⬝ᵥ b) ^ 2 := by
  rw [crossNormSq_eq_leverage_mul_sub_sq]
  ring

/-- **THE DEFECT'S DISCRIMINANT IS THE PAIR MINOR TIMES THE SQUARED AREA.** -/
theorem pairNormalDefect_discriminant (a b : Fin 3 → ℝ) :
    ((leverageOf a + leverageOf b - 1) * leverageOf b - crossNormSq a b)
        * ((leverageOf a + leverageOf b - 1) * leverageOf a - crossNormSq a b)
        - ((leverageOf a + leverageOf b - 1) * (a ⬝ᵥ b)) ^ 2
      = crossNormSq a b * pairGapMinor a b := by
  rw [crossNormSq_eq_leverage_mul_sub_sq, pairGapMinor]
  ring

/-- A binary quadratic with two nonnegative outer coefficients and a nonpositive
discriminant is nonnegative. -/
theorem binaryQuadratic_nonneg {leadCoeff midCoeff tailCoeff first second : ℝ}
    (hlead : 0 ≤ leadCoeff) (htail : 0 ≤ tailCoeff)
    (hdisc : midCoeff ^ 2 ≤ leadCoeff * tailCoeff) :
    0 ≤ leadCoeff * first ^ 2 + 2 * midCoeff * (first * second) + tailCoeff * second ^ 2 := by
  rcases hlead.lt_or_eq with hpos | hzero
  · have hclear : leadCoeff
        * (leadCoeff * first ^ 2 + 2 * midCoeff * (first * second) + tailCoeff * second ^ 2)
        = (leadCoeff * first + midCoeff * second) ^ 2
          + (leadCoeff * tailCoeff - midCoeff ^ 2) * second ^ 2 := by ring
    have hright : 0 ≤ (leadCoeff * first + midCoeff * second) ^ 2
        + (leadCoeff * tailCoeff - midCoeff ^ 2) * second ^ 2 := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ leadCoeff * tailCoeff - midCoeff ^ 2)
        (sq_nonneg second)
      linarith [sq_nonneg (leadCoeff * first + midCoeff * second)]
    nlinarith [hclear, hright, hpos]
  · have hmidZero : midCoeff = 0 := by nlinarith [sq_nonneg midCoeff, hdisc, hzero]
    rw [← hzero, hmidZero]
    have := mul_nonneg htail (sq_nonneg second)
    nlinarith [this]

/-- **THE DEFECT IS NONNEGATIVE AT AN ADMISSIBLE PAIR OF HEAVY ATOMS.**  This is
the plane adjugate's positive semidefiniteness, read entirely in pair vocabulary:
the two outer coefficients are squares plus leverage excesses, and the
discriminant is the pair minor times the squared area. -/
theorem pairNormalDefect_nonneg (a b c : Fin 3 → ℝ)
    (hheavyA : 1 ≤ leverageOf a) (hheavyB : 1 ≤ leverageOf b)
    (hminor : 0 ≤ pairGapMinor a b) :
    0 ≤ pairNormalDefect a b c := by
  have hleadNonneg : 0 ≤ (leverageOf a + leverageOf b - 1) * leverageOf b - crossNormSq a b := by
    rw [pairNormalDefect_leadingCoeff]
    nlinarith [sq_nonneg (a ⬝ᵥ b), hheavyB]
  have htailNonneg : 0 ≤ (leverageOf a + leverageOf b - 1) * leverageOf a - crossNormSq a b := by
    rw [pairNormalDefect_trailingCoeff]
    nlinarith [sq_nonneg (a ⬝ᵥ b), hheavyA]
  have hareaNonneg : 0 ≤ crossNormSq a b := by
    rw [crossNormSq]
    exact dotProduct_self_nonneg _
  have hdisc : (-((leverageOf a + leverageOf b - 1) * (a ⬝ᵥ b))) ^ 2
      ≤ ((leverageOf a + leverageOf b - 1) * leverageOf b - crossNormSq a b)
        * ((leverageOf a + leverageOf b - 1) * leverageOf a - crossNormSq a b) := by
    have hidentity := pairNormalDefect_discriminant a b
    have hproduct : 0 ≤ crossNormSq a b * pairGapMinor a b := mul_nonneg hareaNonneg hminor
    nlinarith [hidentity, hproduct]
  have hquadratic := binaryQuadratic_nonneg hleadNonneg htailNonneg hdisc
    (first := a ⬝ᵥ c) (second := b ⬝ᵥ c)
  rw [pairNormalDefect_eq_quadraticForm]
  linarith [hquadratic]

/-- **THE PAIR-NORMAL FACTORIZATION OF THE THIRD SYLVESTER MINOR.**  A polynomial
identity in the six pair readings of a triple: the third minor, scaled by the
pair's squared area, is the pair minor against the triple's squared volume less the
squared area, minus the pair-normal defect.

The geometry behind it: take the axis along the pair's normal.  The plane block of
the pair's gap is then the pair minor, the Schur probe is the normal scaled by the
pair minor, and `Gtz.frameDet_rankOne` says the third atom adds an exact square. -/
theorem crossNormSq_mul_tripleGapDet_eq (a b c : Fin 3 → ℝ) :
    crossNormSq a b * tripleGapDet a b c
      = pairGapMinor a b * (tripleBracket a b c ^ 2 - crossNormSq a b)
        - pairNormalDefect a b c := by
  rw [pairNormalDefect, tripleGapDet, pairGapMinor, sq_tripleBracket_eq_gramDet,
    crossNormSq_eq_leverage_mul_sub_sq]
  ring

/-- The same identity in fully expanded pair vocabulary: the squared volume enters
LINEARLY, with the pair minor less one as its coefficient. -/
theorem crossNormSq_mul_tripleGapDet_eq_pairVocabulary (a b c : Fin 3 → ℝ) :
    crossNormSq a b * tripleGapDet a b c
      = (pairGapMinor a b - 1) * tripleBracket a b c ^ 2
        - crossNormSq a b * pairGapMinor a b + crossNormSq a b * leverageOf c
        - (leverageOf a * (b ⬝ᵥ c) - (a ⬝ᵥ b) * (a ⬝ᵥ c)) ^ 2
        - ((a ⬝ᵥ b) * (b ⬝ᵥ c) - leverageOf b * (a ⬝ᵥ c)) ^ 2 := by
  rw [crossNormSq_mul_tripleGapDet_eq, pairNormalDefect_eq_bracketForm]
  ring

/-- **THE PAIR-NORMAL CEILING.**  At an admissible pair of heavy atoms the third
minor is capped by the pair minor against the height of the third atom over the
pair's plane.  Dropping the defect is exactly dropping the plane adjugate form. -/
theorem crossNormSq_mul_tripleGapDet_le (a b c : Fin 3 → ℝ)
    (hheavyA : 1 ≤ leverageOf a) (hheavyB : 1 ≤ leverageOf b)
    (hminor : 0 ≤ pairGapMinor a b) :
    crossNormSq a b * tripleGapDet a b c
      ≤ pairGapMinor a b * (tripleBracket a b c ^ 2 - crossNormSq a b) := by
  have hdefect := pairNormalDefect_nonneg a b c hheavyA hheavyB hminor
  have hidentity := crossNormSq_mul_tripleGapDet_eq a b c
  linarith

/-- **THE SQUARED VOLUME BEATS THE SQUARED AREA AT EVERY STRICT DOMINATOR.**  A
corollary of the ceiling: a positive third minor at a positive pair minor forces
the height of the third atom over the pair's plane above one.  The tree proves the
same law from the normal probe (`Gtz.crossNormSq_le_tripleBracket_sq_of_posSemidef`);
this derivation reads it off the factorization instead. -/
theorem crossNormSq_lt_sq_tripleBracket_of_tripleGapDet_pos (a b c : Fin 3 → ℝ)
    (hheavyA : 1 ≤ leverageOf a) (hheavyB : 1 ≤ leverageOf b)
    (hminorPos : 0 < pairGapMinor a b) (hdetPos : 0 < tripleGapDet a b c) :
    crossNormSq a b < tripleBracket a b c ^ 2 := by
  have hareaValue := pairGapMinor_eq_crossNormSq a b
  have hareaPos : 0 < crossNormSq a b := by linarith
  have hceiling := crossNormSq_mul_tripleGapDet_le a b c hheavyA hheavyB hminorPos.le
  have hleft : 0 < crossNormSq a b * tripleGapDet a b c := mul_pos hareaPos hdetPos
  by_contra hcontra
  push Not at hcontra
  have hgap : 0 ≤ crossNormSq a b - tripleBracket a b c ^ 2 := by linarith
  nlinarith [hceiling, hleft, mul_nonneg hminorPos.le hgap]

/-- **THE VOLUME WINDOW AT A TIE.**  At a tie, every triple through a plane-strict
pair has a nonpositive third minor, so the factorization becomes a linear
inequality in the squared volume whose direction is decided by the pair minor
against ONE.  Above one it is a ceiling on the volume, below one a floor, and at
one the volume drops out of the statement entirely. -/
theorem sq_tripleBracket_window_of_isTie (design : WeightedDesign size 3) (htie : IsTie design)
    (frame : AxisFrame) {strongLabel otherLabel thirdLabel : Fin size}
    (hne : strongLabel ≠ otherLabel) (hneStrongThird : strongLabel ≠ thirdLabel)
    (hneOtherThird : otherLabel ≠ thirdLabel)
    (hstrict : PlaneStrictPair design frame.axis strongLabel otherLabel) :
    (pairGapMinor (design.atom strongLabel) (design.atom otherLabel) - 1)
        * tripleBracket (design.atom strongLabel) (design.atom otherLabel)
            (design.atom thirdLabel) ^ 2
      ≤ crossNormSq (design.atom strongLabel) (design.atom otherLabel)
            * pairGapMinor (design.atom strongLabel) (design.atom otherLabel)
          - crossNormSq (design.atom strongLabel) (design.atom otherLabel)
              * leverageOf (design.atom thirdLabel)
          + (leverageOf (design.atom strongLabel)
                * (design.atom otherLabel ⬝ᵥ design.atom thirdLabel)
              - (design.atom strongLabel ⬝ᵥ design.atom otherLabel)
                * (design.atom strongLabel ⬝ᵥ design.atom thirdLabel)) ^ 2
          + ((design.atom strongLabel ⬝ᵥ design.atom otherLabel)
                * (design.atom otherLabel ⬝ᵥ design.atom thirdLabel)
              - leverageOf (design.atom otherLabel)
                * (design.atom strongLabel ⬝ᵥ design.atom thirdLabel)) ^ 2 := by
  have hgate : (subsetSum design {strongLabel, otherLabel, thirdLabel} - 1).det ≤ 0 :=
    det_gap_nonpos_of_isTie_of_pairPlaneStrict design htie frame.oneOne frame.twoTwo
      frame.axisAxis frame.oneTwo frame.oneAxis frame.twoAxis hne hneStrongThird
      hneOtherThird hstrict
  rw [det_subsetSum_tripleGap_eq_tripleGapDet design hne hneStrongThird hneOtherThird] at hgate
  have hareaNonneg : 0 ≤ crossNormSq (design.atom strongLabel) (design.atom otherLabel) := by
    rw [crossNormSq]
    exact dotProduct_self_nonneg _
  have hleft : crossNormSq (design.atom strongLabel) (design.atom otherLabel)
      * tripleGapDet (design.atom strongLabel) (design.atom otherLabel)
          (design.atom thirdLabel) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hareaNonneg hgate
  have hidentity := crossNormSq_mul_tripleGapDet_eq_pairVocabulary (design.atom strongLabel)
    (design.atom otherLabel) (design.atom thirdLabel)
  linarith

/-! ## Part 9 — the Parseval aggregate of the scalar family

The scalar family of Part 5 is one inequality for each third atom.  Parseval sums
them exactly.  The Schur probe carries the whole family, because the reading of an
atom against it is the family's left side. -/

/-- **THE SCHUR PROBE.**  In the frame it is the third column of the pair gap's
adjugate: the axis scaled by the plane block determinant, less the plane part of
the cross moment scaled by the plane adjugate. -/
noncomputable def schurProbe (aa bb cc dd ee : ℝ) (frame : AxisFrame) : Fin 3 → ℝ :=
  frameBlockDet aa bb cc • frame.axis - (cc * dd - bb * ee) • frame.pOne
    - (aa * ee - bb * dd) • frame.pTwo

/-- **THE PROBE CARRIES THE FAMILY.**  Reading any vector against the Schur probe
gives exactly the left side of the scalar family. -/
theorem dotProduct_schurProbe (aa bb cc dd ee : ℝ) (frame : AxisFrame) (vec : Fin 3 → ℝ) :
    vec ⬝ᵥ schurProbe aa bb cc dd ee frame
      = vec ⬝ᵥ frame.axis * frameBlockDet aa bb cc
        - frameBeta aa bb cc dd ee (vec ⬝ᵥ frame.pOne) (vec ⬝ᵥ frame.pTwo) := by
  simp only [schurProbe, dotProduct_sub, dotProduct_smul, smul_eq_mul, frameBeta]
  ring

/-- The Schur probe's reading against the first plane direction. -/
theorem schurProbe_dotProduct_pOne (aa bb cc dd ee : ℝ) (frame : AxisFrame) :
    schurProbe aa bb cc dd ee frame ⬝ᵥ frame.pOne = -(cc * dd - bb * ee) := by
  have hAxisOne : frame.axis ⬝ᵥ frame.pOne = 0 := by
    rw [dotProduct_comm]; exact frame.oneAxis
  have hTwoOne : frame.pTwo ⬝ᵥ frame.pOne = 0 := by
    rw [dotProduct_comm]; exact frame.oneTwo
  simp only [schurProbe, sub_dotProduct, smul_dotProduct, smul_eq_mul, hAxisOne, hTwoOne,
    frame.oneOne]
  ring

/-- The Schur probe's reading against the second plane direction. -/
theorem schurProbe_dotProduct_pTwo (aa bb cc dd ee : ℝ) (frame : AxisFrame) :
    schurProbe aa bb cc dd ee frame ⬝ᵥ frame.pTwo = -(aa * ee - bb * dd) := by
  have hAxisTwo : frame.axis ⬝ᵥ frame.pTwo = 0 := by
    rw [dotProduct_comm]; exact frame.twoAxis
  simp only [schurProbe, sub_dotProduct, smul_dotProduct, smul_eq_mul, hAxisTwo,
    frame.oneTwo, frame.twoTwo]
  ring

/-- The Schur probe's reading against the axis. -/
theorem schurProbe_dotProduct_axis (aa bb cc dd ee : ℝ) (frame : AxisFrame) :
    schurProbe aa bb cc dd ee frame ⬝ᵥ frame.axis = frameBlockDet aa bb cc := by
  simp only [schurProbe, sub_dotProduct, smul_dotProduct, smul_eq_mul, frame.axisAxis,
    frame.oneAxis, frame.twoAxis]
  ring

/-- **THE PROBE'S ENERGY.**  Three squares, one for each frame direction. -/
theorem schurProbe_dotProduct_self (aa bb cc dd ee : ℝ) (frame : AxisFrame) :
    schurProbe aa bb cc dd ee frame ⬝ᵥ schurProbe aa bb cc dd ee frame
      = frameBlockDet aa bb cc ^ 2 + (cc * dd - bb * ee) ^ 2 + (aa * ee - bb * dd) ^ 2 := by
  rw [frame.dotProduct_self_split (schurProbe aa bb cc dd ee frame),
    schurProbe_dotProduct_pOne, schurProbe_dotProduct_pTwo, schurProbe_dotProduct_axis]
  ring

/-- **PARSEVAL SUMS THE PLANE ADJUGATE FORM.**  The weighted total of the plane
adjugate form over the design is the plane block's trace. -/
theorem sum_weight_mul_frameAlpha (design : WeightedDesign size 3) (frame : AxisFrame)
    (aa bb cc : ℝ) :
    ∑ label, design.weight label
        * frameAlpha aa bb cc (design.atom label ⬝ᵥ frame.pOne)
            (design.atom label ⬝ᵥ frame.pTwo)
      = aa + cc := by
  have hterm : ∀ label : Fin size, design.weight label
      * frameAlpha aa bb cc (design.atom label ⬝ᵥ frame.pOne)
          (design.atom label ⬝ᵥ frame.pTwo)
      = cc * (design.weight label
            * ((design.atom label ⬝ᵥ frame.pOne) * (design.atom label ⬝ᵥ frame.pOne)))
        - 2 * bb * (design.weight label
            * ((design.atom label ⬝ᵥ frame.pOne) * (design.atom label ⬝ᵥ frame.pTwo)))
        + aa * (design.weight label
            * ((design.atom label ⬝ᵥ frame.pTwo) * (design.atom label ⬝ᵥ frame.pTwo))) := by
    intro label
    rw [frameAlpha]
    ring
  rw [Finset.sum_congr rfl fun label _ => hterm label, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_weighted_atomPairing design frame.pOne frame.pOne,
    sum_weighted_atomPairing design frame.pOne frame.pTwo,
    sum_weighted_atomPairing design frame.pTwo frame.pTwo,
    frame.oneOne, frame.twoTwo, frame.oneTwo]
  ring

/-- **THE PAIR-MASS FLOOR AT A TIE.**  Parseval spends the scalar family of Part 5
over the whole design.  The Schur probe's own energy is bounded by the pair's
determinant deficit against the plane block plus its trace, plus the two readings
that the pair itself keeps.  Every quantity is explicit. -/
theorem schurProbe_energy_le_of_isTie (design : WeightedDesign size 3) (htie : IsTie design)
    (frame : AxisFrame) {strongLabel otherLabel : Fin size} (hne : strongLabel ≠ otherLabel)
    (hstrict : PlaneStrictPair design frame.axis strongLabel otherLabel)
    {aa bb cc dd ee ff : ℝ}
    (haa : aa = gapReading design {strongLabel, otherLabel} frame.pOne frame.pOne)
    (hbb : bb = gapReading design {strongLabel, otherLabel} frame.pOne frame.pTwo)
    (hcc : cc = gapReading design {strongLabel, otherLabel} frame.pTwo frame.pTwo)
    (hdd : dd = gapReading design {strongLabel, otherLabel} frame.pOne frame.axis)
    (hee : ee = gapReading design {strongLabel, otherLabel} frame.pTwo frame.axis)
    (hff : ff = gapReading design {strongLabel, otherLabel} frame.axis frame.axis) :
    schurProbe aa bb cc dd ee frame ⬝ᵥ schurProbe aa bb cc dd ee frame
      ≤ (- frameDet aa bb cc dd ee ff) * (frameBlockDet aa bb cc + aa + cc)
        + design.weight strongLabel
            * (design.atom strongLabel ⬝ᵥ schurProbe aa bb cc dd ee frame) ^ 2
        + design.weight otherLabel
            * (design.atom otherLabel ⬝ᵥ schurProbe aa bb cc dd ee frame) ^ 2 := by
  classical
  set probe := schurProbe aa bb cc dd ee frame with hprobeDef
  set pairSet : Finset (Fin size) := {strongLabel, otherLabel} with hpairDef
  have hstrongMem : strongLabel ∈ pairSet := by simp [hpairDef]
  have hotherMem : otherLabel ∈ pairSet := by simp [hpairDef]
  have haaPos : 0 < aa := by
    rw [haa]
    exact gapReading_pOne_pos_of_planeStrictPair design frame hne hstrongMem hotherMem hstrict
  have hblockPos : 0 < frameBlockDet aa bb cc := by
    rw [haa, hbb, hcc]
    exact frameBlockDet_pos_of_planeStrictPair design frame hne hstrongMem hotherMem hstrict
  have hpairNeg : frameDet aa bb cc dd ee ff < 0 := by
    rw [haa, hbb, hcc, hdd, hee, hff]
    exact frameDet_pair_neg_of_planeStrictPair design frame hne hstrict
  -- the family, atom by atom, outside the pair
  have hfamily : ∀ label ∈ pairSetᶜ,
      design.weight label * (design.atom label ⬝ᵥ probe) ^ 2
        ≤ design.weight label * ((- frameDet aa bb cc dd ee ff)
            * (frameBlockDet aa bb cc
              + frameAlpha aa bb cc (design.atom label ⬝ᵥ frame.pOne)
                  (design.atom label ⬝ᵥ frame.pTwo))) := by
    intro label hlabel
    have hnotMem : label ∉ pairSet := Finset.mem_compl.mp hlabel
    have hlabelNe : strongLabel ≠ label ∧ otherLabel ≠ label := by
      simp only [hpairDef, Finset.mem_insert, Finset.mem_singleton] at hnotMem
      push Not at hnotMem
      exact ⟨Ne.symm hnotMem.1, Ne.symm hnotMem.2⟩
    have hscalar := sq_schurProbe_reading_le_of_isTie design htie frame hne hlabelNe.1
      hlabelNe.2 hstrict
    rw [← haa, ← hbb, ← hcc, ← hdd, ← hee, ← hff] at hscalar
    have hreading : (design.atom label ⬝ᵥ probe) ^ 2
        = (design.atom label ⬝ᵥ frame.axis * frameBlockDet aa bb cc
            - frameBeta aa bb cc dd ee (design.atom label ⬝ᵥ frame.pOne)
                (design.atom label ⬝ᵥ frame.pTwo)) ^ 2 := by
      rw [hprobeDef, dotProduct_schurProbe]
    rw [hreading]
    exact mul_le_mul_of_nonneg_left hscalar (design.weight_pos label).le
  -- Parseval on the probe
  have hparseval : ∑ label, design.weight label
      * ((design.atom label ⬝ᵥ probe) * (design.atom label ⬝ᵥ probe)) = probe ⬝ᵥ probe :=
    sum_weighted_atomPairing design probe probe
  have hparsevalSq : ∑ label, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2
      = probe ⬝ᵥ probe := by
    rw [← hparseval]
    exact Finset.sum_congr rfl fun label _ => by ring
  -- Parseval on the plane adjugate form
  have halpha : ∑ label, design.weight label
      * (frameBlockDet aa bb cc
        + frameAlpha aa bb cc (design.atom label ⬝ᵥ frame.pOne)
            (design.atom label ⬝ᵥ frame.pTwo))
      = frameBlockDet aa bb cc + aa + cc := by
    have hsplit : ∀ label : Fin size, design.weight label
        * (frameBlockDet aa bb cc
          + frameAlpha aa bb cc (design.atom label ⬝ᵥ frame.pOne)
              (design.atom label ⬝ᵥ frame.pTwo))
        = frameBlockDet aa bb cc * design.weight label
          + design.weight label
            * frameAlpha aa bb cc (design.atom label ⬝ᵥ frame.pOne)
                (design.atom label ⬝ᵥ frame.pTwo) := fun label => by ring
    rw [Finset.sum_congr rfl fun label _ => hsplit label, Finset.sum_add_distrib,
      ← Finset.mul_sum, design.weight_sum_one, sum_weight_mul_frameAlpha design frame aa bb cc]
    ring
  -- every term of the aggregate is nonnegative, so the pair's own share only helps
  have hterm : ∀ label : Fin size, 0 ≤ design.weight label
      * (frameBlockDet aa bb cc
        + frameAlpha aa bb cc (design.atom label ⬝ᵥ frame.pOne)
            (design.atom label ⬝ᵥ frame.pTwo)) := by
    intro label
    refine mul_nonneg (design.weight_pos label).le ?_
    linarith [frameAlpha_nonneg haaPos hblockPos (design.atom label ⬝ᵥ frame.pOne)
      (design.atom label ⬝ᵥ frame.pTwo)]
  have hcompl : ∑ label ∈ pairSetᶜ, design.weight label
      * (frameBlockDet aa bb cc
        + frameAlpha aa bb cc (design.atom label ⬝ᵥ frame.pOne)
            (design.atom label ⬝ᵥ frame.pTwo))
      ≤ frameBlockDet aa bb cc + aa + cc := by
    rw [← halpha]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun label _ _ => hterm label
  have hsumFamily : ∑ label ∈ pairSetᶜ, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2
      ≤ (- frameDet aa bb cc dd ee ff) * (frameBlockDet aa bb cc + aa + cc) := by
    have hstep : ∑ label ∈ pairSetᶜ, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2
        ≤ ∑ label ∈ pairSetᶜ, design.weight label * ((- frameDet aa bb cc dd ee ff)
            * (frameBlockDet aa bb cc
              + frameAlpha aa bb cc (design.atom label ⬝ᵥ frame.pOne)
                  (design.atom label ⬝ᵥ frame.pTwo))) :=
      Finset.sum_le_sum hfamily
    have hpull : ∑ label ∈ pairSetᶜ, design.weight label * ((- frameDet aa bb cc dd ee ff)
          * (frameBlockDet aa bb cc
            + frameAlpha aa bb cc (design.atom label ⬝ᵥ frame.pOne)
                (design.atom label ⬝ᵥ frame.pTwo)))
        = (- frameDet aa bb cc dd ee ff) * ∑ label ∈ pairSetᶜ, design.weight label
            * (frameBlockDet aa bb cc
              + frameAlpha aa bb cc (design.atom label ⬝ᵥ frame.pOne)
                  (design.atom label ⬝ᵥ frame.pTwo)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun label _ => by ring
    rw [hpull] at hstep
    have hscale : (- frameDet aa bb cc dd ee ff) * ∑ label ∈ pairSetᶜ, design.weight label
          * (frameBlockDet aa bb cc
            + frameAlpha aa bb cc (design.atom label ⬝ᵥ frame.pOne)
                (design.atom label ⬝ᵥ frame.pTwo))
        ≤ (- frameDet aa bb cc dd ee ff) * (frameBlockDet aa bb cc + aa + cc) :=
      mul_le_mul_of_nonneg_left hcompl (by linarith)
    linarith
  have hsplitTotal : ∑ label ∈ pairSet, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2
      + ∑ label ∈ pairSetᶜ, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2
      = probe ⬝ᵥ probe := by
    rw [Finset.sum_add_sum_compl]
    exact hparsevalSq
  have hpairShare : ∑ label ∈ pairSet, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2
      = design.weight strongLabel * (design.atom strongLabel ⬝ᵥ probe) ^ 2
        + design.weight otherLabel * (design.atom otherLabel ⬝ᵥ probe) ^ 2 := by
    rw [hpairDef, Finset.sum_pair hne]
  rw [hpairShare] at hsplitTotal
  linarith

/-! ## Part 10 — the Sylvester moment ladder, and the area ceiling at a tie

The first two Sylvester minors already have exact weighted averages in the tree.
The first is Parseval's trace, `sum c, t_c (l_c - 1) = k - 1`.  The second is
`Gtz.sum_weight_mul_pairGapForm`, which at rank three reads
`sum c, t_c pairGapMinor(a, c) = l_a - 2`.  The THIRD is landed here:

    sum over c of  t_c * tripleGapDet(a, b, c)  =  2 - l_a - l_b,

for every pair of atoms of every rank-three design, at every size.  Five Parseval
readings spend the whole design and no atom survives.

The consequence is an exact CEILING on a pair's squared area at a tie.  At a tie no
triple dominates strictly, so through a heavy admissible pair every third minor is
nonpositive.  The two terms the pair keeps for itself are polynomials in the pair's
own readings (`Gtz.tripleGapDet_repeat_left`), so the moment law turns the tie into

    2 (t_a + t_b) crossNormSq(a, b)
        <=  l_a + l_b - 2 + t_a (2 l_a + l_b - 1) + t_b (l_a + 2 l_b - 1).

Measured at the `(5,3)` diamond in floating point: all ten pairs are heavy and
admissible, and FOUR of them sit EXACTLY on this ceiling, at squared area `10`
against a ceiling of `10`.  The ceiling is attained at a kernel-checked tie, so no
constant can sharpen it.  Against the admissibility floor
`l_a + l_b - 1 < crossNormSq(a, b)` it cuts a window, and at the diamond the four
extremal pairs sit at the window's top end. -/

/-- Parseval at two atoms: the weighted total of the mixed readings is the two
atoms' own pairing. -/
theorem sum_weight_mul_atomPairing_pair (design : WeightedDesign size 3)
    (leftLabel rightLabel : Fin size) :
    ∑ label, design.weight label
        * ((design.atom leftLabel ⬝ᵥ design.atom label)
          * (design.atom rightLabel ⬝ᵥ design.atom label))
      = design.atom leftLabel ⬝ᵥ design.atom rightLabel := by
  have hpair := sum_weighted_atomPairing design (design.atom leftLabel)
    (design.atom rightLabel)
  have hterm : ∀ label : Fin size,
      design.weight label * ((design.atom leftLabel ⬝ᵥ design.atom label)
          * (design.atom rightLabel ⬝ᵥ design.atom label))
        = design.weight label * ((design.atom label ⬝ᵥ design.atom leftLabel)
            * (design.atom label ⬝ᵥ design.atom rightLabel)) := by
    intro label
    rw [dotProduct_comm (design.atom leftLabel) (design.atom label),
      dotProduct_comm (design.atom rightLabel) (design.atom label)]
  rw [Finset.sum_congr rfl fun label _ => hterm label, hpair]

/-- **THE THIRD SYLVESTER MOMENT.**  The weighted average of the third minor
through a fixed pair is `2` less the pair's two leverages.  Five Parseval readings
spend the design: the trace, the two squared readings against the pair, the mixed
reading, and the weight total.  No atom survives on the right. -/
theorem sum_weight_mul_tripleGapDet (design : WeightedDesign size 3)
    (leftLabel rightLabel : Fin size) :
    ∑ label, design.weight label
        * tripleGapDet (design.atom leftLabel) (design.atom rightLabel) (design.atom label)
      = 2 - leverageOf (design.atom leftLabel) - leverageOf (design.atom rightLabel) := by
  set leftLev := leverageOf (design.atom leftLabel) with hleftLev
  set rightLev := leverageOf (design.atom rightLabel) with hrightLev
  set pairing := design.atom leftLabel ⬝ᵥ design.atom rightLabel with hpairing
  have hterm : ∀ label : Fin size,
      design.weight label
          * tripleGapDet (design.atom leftLabel) (design.atom rightLabel) (design.atom label)
        = ((leftLev - 1) * (rightLev - 1) - pairing ^ 2)
              * (design.weight label * leverageOf (design.atom label))
          - ((leftLev - 1) * (rightLev - 1) - pairing ^ 2) * design.weight label
          - (leftLev - 1)
              * (design.weight label
                * (design.atom rightLabel ⬝ᵥ design.atom label) ^ 2)
          - (rightLev - 1)
              * (design.weight label
                * (design.atom leftLabel ⬝ᵥ design.atom label) ^ 2)
          + 2 * pairing
              * (design.weight label
                * ((design.atom leftLabel ⬝ᵥ design.atom label)
                  * (design.atom rightLabel ⬝ᵥ design.atom label))) := by
    intro label
    rw [tripleGapDet, hleftLev, hrightLev, hpairing]
    ring
  rw [Finset.sum_congr rfl fun label _ => hterm label, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_weighted_leverage design, design.weight_sum_one,
    sum_weight_mul_sq_atomPairing design rightLabel,
    sum_weight_mul_sq_atomPairing design leftLabel,
    sum_weight_mul_atomPairing_pair design leftLabel rightLabel, ← hpairing, ← hleftLev,
    ← hrightLev]
  push_cast
  ring

/-- The third minor with the first atom repeated, in pair vocabulary. -/
theorem tripleGapDet_repeat_left (a b : Fin 3 → ℝ) :
    tripleGapDet a b a = -2 * crossNormSq a b + 2 * leverageOf a + leverageOf b - 1 := by
  simp only [tripleGapDet, crossNormSq_eq_leverage_mul_sub_sq, leverageOf, dotProduct,
    Fin.sum_univ_three]
  ring

/-- The third minor with the second atom repeated, in pair vocabulary. -/
theorem tripleGapDet_repeat_right (a b : Fin 3 → ℝ) :
    tripleGapDet a b b = -2 * crossNormSq a b + leverageOf a + 2 * leverageOf b - 1 := by
  simp only [tripleGapDet, crossNormSq_eq_leverage_mul_sub_sq, leverageOf, dotProduct,
    Fin.sum_univ_three]
  ring

/-- At a tie every third minor through a heavy admissible pair is nonpositive.  The
pair-vocabulary criterion decides strict domination by three inequalities, and the
first two are the hypotheses. -/
theorem tripleGapDet_nonpos_of_isTie (design : WeightedDesign size 3) (htie : IsTie design)
    {leftLabel rightLabel thirdLabel : Fin size} (hne : leftLabel ≠ rightLabel)
    (hneLeftThird : leftLabel ≠ thirdLabel) (hneRightThird : rightLabel ≠ thirdLabel)
    (hheavy : 1 < leverageOf (design.atom leftLabel))
    (hadmissible : AdmissiblePair (design.atom leftLabel) (design.atom rightLabel)) :
    tripleGapDet (design.atom leftLabel) (design.atom rightLabel)
        (design.atom thirdLabel) ≤ 0 := by
  classical
  by_contra hpositive
  push Not at hpositive
  have hcard : ({leftLabel, rightLabel, thirdLabel} : Finset (Fin size)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hne, hneLeftThird⟩),
      Finset.card_insert_of_notMem (by simpa using hneRightThird), Finset.card_singleton]
  refine htie.2 {leftLabel, rightLabel, thirdLabel} hcard ?_
  refine (subsetSum_posDef_iff_pairVocabulary design leftLabel rightLabel thirdLabel hne
    hneLeftThird hneRightThird).mpr ⟨by linarith, hadmissible, hpositive⟩

/-- **THE AREA CEILING AT A TIE.**  At a tie a heavy admissible pair cannot spread
its squared area past an explicit bound in its own two leverages and two weights.
The moment law spends the whole design, the tie kills every term outside the pair,
and the two terms the pair keeps are polynomials in its own readings.

Measured at the `(5,3)` diamond: four of its ten pairs attain this ceiling exactly,
at squared area `10` against a ceiling of `10`. -/
theorem crossNormSq_le_of_isTie (design : WeightedDesign size 3) (htie : IsTie design)
    {leftLabel rightLabel : Fin size} (hne : leftLabel ≠ rightLabel)
    (hheavy : 1 < leverageOf (design.atom leftLabel))
    (hadmissible : AdmissiblePair (design.atom leftLabel) (design.atom rightLabel)) :
    2 * (design.weight leftLabel + design.weight rightLabel)
        * crossNormSq (design.atom leftLabel) (design.atom rightLabel)
      ≤ leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel) - 2
        + design.weight leftLabel
            * (2 * leverageOf (design.atom leftLabel)
              + leverageOf (design.atom rightLabel) - 1)
        + design.weight rightLabel
            * (leverageOf (design.atom leftLabel)
              + 2 * leverageOf (design.atom rightLabel) - 1) := by
  classical
  set pairSet : Finset (Fin size) := {leftLabel, rightLabel} with hpairDef
  have houtside : ∑ label ∈ pairSetᶜ, design.weight label
      * tripleGapDet (design.atom leftLabel) (design.atom rightLabel)
          (design.atom label) ≤ 0 := by
    refine Finset.sum_nonpos fun label hlabel => ?_
    have hnotMem : label ∉ pairSet := Finset.mem_compl.mp hlabel
    have hlabelNe : leftLabel ≠ label ∧ rightLabel ≠ label := by
      simp only [hpairDef, Finset.mem_insert, Finset.mem_singleton] at hnotMem
      push Not at hnotMem
      exact ⟨Ne.symm hnotMem.1, Ne.symm hnotMem.2⟩
    exact mul_nonpos_of_nonneg_of_nonpos (design.weight_pos label).le
      (tripleGapDet_nonpos_of_isTie design htie hne hlabelNe.1 hlabelNe.2 hheavy hadmissible)
  have htotal : ∑ label ∈ pairSet, design.weight label
        * tripleGapDet (design.atom leftLabel) (design.atom rightLabel) (design.atom label)
      + ∑ label ∈ pairSetᶜ, design.weight label
        * tripleGapDet (design.atom leftLabel) (design.atom rightLabel) (design.atom label)
      = 2 - leverageOf (design.atom leftLabel) - leverageOf (design.atom rightLabel) := by
    rw [Finset.sum_add_sum_compl]
    exact sum_weight_mul_tripleGapDet design leftLabel rightLabel
  have hinside : ∑ label ∈ pairSet, design.weight label
        * tripleGapDet (design.atom leftLabel) (design.atom rightLabel) (design.atom label)
      = design.weight leftLabel
          * (-2 * crossNormSq (design.atom leftLabel) (design.atom rightLabel)
            + 2 * leverageOf (design.atom leftLabel)
            + leverageOf (design.atom rightLabel) - 1)
        + design.weight rightLabel
          * (-2 * crossNormSq (design.atom leftLabel) (design.atom rightLabel)
            + leverageOf (design.atom leftLabel)
            + 2 * leverageOf (design.atom rightLabel) - 1) := by
    rw [hpairDef, Finset.sum_pair hne, tripleGapDet_repeat_left, tripleGapDet_repeat_right]
  rw [hinside] at htotal
  nlinarith [htotal, houtside]

/-- **THE PAIR WINDOW AT A TIE.**  Admissibility is a floor on the squared area and
the moment law is a ceiling.  Both are stated in the same four numbers, so a heavy
admissible pair of a tie is confined to an explicit interval. -/
theorem crossNormSq_window_of_isTie (design : WeightedDesign size 3) (htie : IsTie design)
    {leftLabel rightLabel : Fin size} (hne : leftLabel ≠ rightLabel)
    (hheavy : 1 < leverageOf (design.atom leftLabel))
    (hadmissible : AdmissiblePair (design.atom leftLabel) (design.atom rightLabel)) :
    leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel) - 1
        < crossNormSq (design.atom leftLabel) (design.atom rightLabel)
      ∧ 2 * (design.weight leftLabel + design.weight rightLabel)
          * crossNormSq (design.atom leftLabel) (design.atom rightLabel)
        ≤ leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel) - 2
          + design.weight leftLabel
              * (2 * leverageOf (design.atom leftLabel)
                + leverageOf (design.atom rightLabel) - 1)
          + design.weight rightLabel
              * (leverageOf (design.atom leftLabel)
                + 2 * leverageOf (design.atom rightLabel) - 1) := by
  refine ⟨?_, crossNormSq_le_of_isTie design htie hne hheavy hadmissible⟩
  have hminor := hadmissible
  rw [AdmissiblePair, pairGapMinor_eq_crossNormSq] at hminor
  linarith

/-- **THE `(6,3)` TEST.**  Every simple tie at six points and rank three carries a
pair that is heavy, admissible, and confined to the window.  The pair is produced
by the shadow route of Part 7, so nothing is assumed beyond simplicity. -/
theorem exists_pair_window_of_isTie_sixThree (design : WeightedDesign 6 3)
    (hsimple : ¬ HasParallelPair design) (htie : IsTie design) :
    ∃ leftLabel rightLabel : Fin 6, leftLabel ≠ rightLabel
      ∧ 1 < leverageOf (design.atom leftLabel)
      ∧ 1 < leverageOf (design.atom rightLabel)
      ∧ leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel) - 1
          < crossNormSq (design.atom leftLabel) (design.atom rightLabel)
      ∧ 2 * (design.weight leftLabel + design.weight rightLabel)
            * crossNormSq (design.atom leftLabel) (design.atom rightLabel)
          ≤ leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel) - 2
            + design.weight leftLabel
                * (2 * leverageOf (design.atom leftLabel)
                  + leverageOf (design.atom rightLabel) - 1)
            + design.weight rightLabel
                * (leverageOf (design.atom leftLabel)
                  + 2 * leverageOf (design.atom rightLabel) - 1) := by
  obtain ⟨leftLabel, rightLabel, hne, hadmissible, hheavyLeft, hheavyRight⟩ :=
    exists_admissiblePair_of_not_hasParallelPair design hsimple
      (labelOne := 0) (labelTwo := 1) (labelThree := 2) (labelFour := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hfloor, hceiling⟩ :=
    crossNormSq_window_of_isTie design htie hne hheavyLeft hadmissible
  exact ⟨leftLabel, rightLabel, hne, hheavyLeft, hheavyRight, hfloor, hceiling⟩

/-! ## Part 11 — the simplicity hypothesis leaves

Part 7 produced an admissible heavy pair from geometry: a plane, a shadow, a
strictly dominating shadow pair.  It cost a simplicity hypothesis and four labels.
The SECOND Sylvester moment produces one from arithmetic alone.

`Gtz.sum_weight_mul_pairGapForm` says the weighted average of the second minor
through an atom is `l_a - 2` at rank three.  Peel the diagonal term and the
weighted average over the OTHER atoms is `l_a - 2 - t_a + 2 t_a l_a`.  Positivity
of that average is `2 + t_a < l_a (1 + 2 t_a)`, and it hands over an atom whose
pair with `a` is admissible.

At rank three the weighted leverages average to THREE, so some atom carries
`l_a >= 3`.  The threshold `(2 + t_a) / (1 + 2 t_a)` never passes `2`.  So every
rank-three design, at every size, carries a heavy admissible pair, with no
simplicity, no genericity, no four labels and no plane.  Measured over 60000
random rank-three designs of sizes four to nine: the heaviest atom beats its
threshold by at least `1.356`, and a heavy admissible partner exists every time.

The window of Part 10 therefore holds at EVERY rank-three tie. -/

/-- The tree's pair gap form of a design is the pair minor of its two atoms. -/
theorem pairGapForm_eq_pairGapMinor (design : WeightedDesign size 3)
    (leftLabel rightLabel : Fin size) :
    pairGapForm design leftLabel rightLabel
      = pairGapMinor (design.atom leftLabel) (design.atom rightLabel) := rfl

/-- **THE SECOND MOMENT, OFF THE DIAGONAL.**  Peeling the atom's own term off the
second Sylvester moment leaves an average over the other atoms that is positive
exactly when the atom passes the threshold `(2 + t) / (1 + 2 t)`. -/
theorem sum_erase_weight_mul_pairGapMinor (design : WeightedDesign size 3)
    (pivotLabel : Fin size) :
    ∑ label ∈ Finset.univ.erase pivotLabel,
        design.weight label * pairGapMinor (design.atom pivotLabel) (design.atom label)
      = leverageOf (design.atom pivotLabel) - 2 - design.weight pivotLabel
        + 2 * design.weight pivotLabel * leverageOf (design.atom pivotLabel) := by
  have hfull := sum_weight_mul_pairGapForm design pivotLabel
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ pivotLabel), pairGapForm_self] at hfull
  have hterms : ∑ label ∈ Finset.univ.erase pivotLabel,
      design.weight label * pairGapForm design pivotLabel label
      = ∑ label ∈ Finset.univ.erase pivotLabel,
        design.weight label * pairGapMinor (design.atom pivotLabel) (design.atom label) :=
    Finset.sum_congr rfl fun label _ => by rw [pairGapForm_eq_pairGapMinor]
  rw [hterms] at hfull
  push_cast at hfull
  linarith

/-- **AN ADMISSIBLE HEAVY PAIR FROM THE SECOND MOMENT.**  An atom past the
threshold `2 + t_a < l_a (1 + 2 t_a)` sits in an admissible pair, and the partner
inherits strict heaviness from the pair minor.  No geometry enters. -/
theorem exists_admissiblePair_of_secondMoment (design : WeightedDesign size 3)
    (pivotLabel : Fin size) (hheavy : 1 < leverageOf (design.atom pivotLabel))
    (hbudget : 2 + design.weight pivotLabel
      < leverageOf (design.atom pivotLabel) * (1 + 2 * design.weight pivotLabel)) :
    ∃ partnerLabel : Fin size, partnerLabel ≠ pivotLabel
      ∧ AdmissiblePair (design.atom pivotLabel) (design.atom partnerLabel)
      ∧ 1 < leverageOf (design.atom partnerLabel) := by
  classical
  have hmoment := sum_erase_weight_mul_pairGapMinor design pivotLabel
  have hsumPos : ∑ label ∈ Finset.univ.erase pivotLabel, (0 : ℝ)
      < ∑ label ∈ Finset.univ.erase pivotLabel,
        design.weight label * pairGapMinor (design.atom pivotLabel) (design.atom label) := by
    rw [Finset.sum_const_zero, hmoment]
    nlinarith [hbudget]
  obtain ⟨partnerLabel, hmem, hterm⟩ := Finset.exists_lt_of_sum_lt hsumPos
  have hweightPos := design.weight_pos partnerLabel
  have hminorPos : 0 < pairGapMinor (design.atom pivotLabel) (design.atom partnerLabel) := by
    nlinarith [hterm, hweightPos]
  exact ⟨partnerLabel, (Finset.mem_erase.mp hmem).1, hminorPos,
    one_lt_leverage_of_admissiblePair _ _ hminorPos hheavy⟩

/-- **SOME ATOM CARRIES THE WHOLE RANK.**  The weighted leverages of a rank-three
design average to three, so one atom reaches three. -/
theorem exists_three_le_leverage (design : WeightedDesign size 3) :
    ∃ heavyLabel : Fin size, 3 ≤ leverageOf (design.atom heavyLabel) := by
  classical
  by_contra hall
  push Not at hall
  have hnonempty : (Finset.univ : Finset (Fin size)).Nonempty := by
    have hpos : 0 < size := size_pos_of_design design
    exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hpos)
  have hstrict : ∑ label, design.weight label * leverageOf (design.atom label)
      < ∑ label, design.weight label * 3 :=
    Finset.sum_lt_sum_of_nonempty hnonempty fun label _ =>
      mul_lt_mul_of_pos_left (hall label) (design.weight_pos label)
  rw [sum_weighted_leverage design, ← Finset.sum_mul, design.weight_sum_one] at hstrict
  norm_num at hstrict

/-- **EVERY RANK-THREE DESIGN CARRIES AN ADMISSIBLE HEAVY PAIR.**  Unconditional, at
every size.  The heaviest atom reaches leverage three, the threshold
`(2 + t) / (1 + 2 t)` never passes two, and the second Sylvester moment hands over
the partner.  Nothing geometric is assumed: no simplicity, no genericity, no four
labels, and no plane. -/
theorem exists_admissiblePair_rank_three (design : WeightedDesign size 3) :
    ∃ leftLabel rightLabel : Fin size, leftLabel ≠ rightLabel
      ∧ AdmissiblePair (design.atom leftLabel) (design.atom rightLabel)
      ∧ 1 < leverageOf (design.atom leftLabel)
      ∧ 1 < leverageOf (design.atom rightLabel) := by
  obtain ⟨heavyLabel, hheavyValue⟩ := exists_three_le_leverage design
  have hweightPos := design.weight_pos heavyLabel
  have hweightLe : design.weight heavyLabel ≤ 1 := by
    rw [← design.weight_sum_one]
    exact Finset.single_le_sum (fun label _ => (design.weight_pos label).le)
      (Finset.mem_univ heavyLabel)
  have hheavy : 1 < leverageOf (design.atom heavyLabel) := by linarith
  have hbudget : 2 + design.weight heavyLabel
      < leverageOf (design.atom heavyLabel) * (1 + 2 * design.weight heavyLabel) := by
    nlinarith [hheavyValue, hweightPos]
  obtain ⟨partnerLabel, hpartnerNe, hadmissible, hpartnerHeavy⟩ :=
    exists_admissiblePair_of_secondMoment design heavyLabel hheavy hbudget
  exact ⟨heavyLabel, partnerLabel, Ne.symm hpartnerNe, hadmissible, hheavy, hpartnerHeavy⟩

/-- **THE WINDOW HOLDS AT EVERY RANK-THREE TIE.**  Composing the unconditional
admissible heavy pair with the area window of Part 10.  No simplicity hypothesis
survives, and the size is arbitrary.

Measured at the `(5,3)` diamond, the kernel-checked tie that stops every hinge one
size down: all ten of its pairs are heavy and admissible, and FOUR of them sit
exactly on the ceiling, at squared area `10` against a ceiling of `10`. -/
theorem exists_pair_window_of_isTie (design : WeightedDesign size 3) (htie : IsTie design) :
    ∃ leftLabel rightLabel : Fin size, leftLabel ≠ rightLabel
      ∧ 1 < leverageOf (design.atom leftLabel)
      ∧ 1 < leverageOf (design.atom rightLabel)
      ∧ leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel) - 1
          < crossNormSq (design.atom leftLabel) (design.atom rightLabel)
      ∧ 2 * (design.weight leftLabel + design.weight rightLabel)
            * crossNormSq (design.atom leftLabel) (design.atom rightLabel)
          ≤ leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel) - 2
            + design.weight leftLabel
                * (2 * leverageOf (design.atom leftLabel)
                  + leverageOf (design.atom rightLabel) - 1)
            + design.weight rightLabel
                * (leverageOf (design.atom leftLabel)
                  + 2 * leverageOf (design.atom rightLabel) - 1) := by
  obtain ⟨leftLabel, rightLabel, hne, hadmissible, hheavyLeft, hheavyRight⟩ :=
    exists_admissiblePair_rank_three design
  obtain ⟨hfloor, hceiling⟩ :=
    crossNormSq_window_of_isTie design htie hne hheavyLeft hadmissible
  exact ⟨leftLabel, rightLabel, hne, hheavyLeft, hheavyRight, hfloor, hceiling⟩

/-- **THE `(6,3)` TEST, UNCONDITIONAL.**  Every tie at six points and rank three
carries a pair inside the window.  This supersedes the simple-design form above,
which keeps its own value: that route also delivers a PLANE-STRICTNESS certificate
for the pair, and this one does not. -/
theorem exists_pair_window_of_isTie_sixThree_unconditional (design : WeightedDesign 6 3)
    (htie : IsTie design) :
    ∃ leftLabel rightLabel : Fin 6, leftLabel ≠ rightLabel
      ∧ 1 < leverageOf (design.atom leftLabel)
      ∧ 1 < leverageOf (design.atom rightLabel)
      ∧ leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel) - 1
          < crossNormSq (design.atom leftLabel) (design.atom rightLabel)
      ∧ 2 * (design.weight leftLabel + design.weight rightLabel)
            * crossNormSq (design.atom leftLabel) (design.atom rightLabel)
          ≤ leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel) - 2
            + design.weight leftLabel
                * (2 * leverageOf (design.atom leftLabel)
                  + leverageOf (design.atom rightLabel) - 1)
            + design.weight rightLabel
                * (leverageOf (design.atom leftLabel)
                  + 2 * leverageOf (design.atom rightLabel) - 1) :=
  exists_pair_window_of_isTie design htie

/-! ## Part 12 — the ceiling's equality locus is a rigidity statement

The ceiling was read off a sum of nonpositive terms, so equality forces every term
to vanish.  A heavy admissible pair of a tie that attains the ceiling therefore has
a VANISHING third minor at every third atom: every triple through it sits exactly on
the boundary of strict domination.

Both shipped rank-three ties calibrate this.  At the `(4,3)` tetrahedron every
leverage is `3` and every pairing is `-1`, so every pair has squared area `8`
against a ceiling of `8` — equality at all six pairs, and indeed every one of its
triples is tight.  At the `(5,3)` diamond four of the ten pairs attain the ceiling
and six do not, so the equality is a locus and not a law. -/

/-- **THE EQUALITY LOCUS.**  A heavy admissible pair of a tie that attains the area
ceiling kills the third minor at every third atom.  Strict weight positivity is
what collapses the aggregate onto its terms. -/
theorem tripleGapDet_eq_zero_of_crossNormSq_eq_ceiling (design : WeightedDesign size 3)
    (htie : IsTie design) {leftLabel rightLabel : Fin size} (hne : leftLabel ≠ rightLabel)
    (hheavy : 1 < leverageOf (design.atom leftLabel))
    (hadmissible : AdmissiblePair (design.atom leftLabel) (design.atom rightLabel))
    (hequality : 2 * (design.weight leftLabel + design.weight rightLabel)
        * crossNormSq (design.atom leftLabel) (design.atom rightLabel)
      = leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel) - 2
        + design.weight leftLabel
            * (2 * leverageOf (design.atom leftLabel)
              + leverageOf (design.atom rightLabel) - 1)
        + design.weight rightLabel
            * (leverageOf (design.atom leftLabel)
              + 2 * leverageOf (design.atom rightLabel) - 1))
    {thirdLabel : Fin size} (hneLeftThird : leftLabel ≠ thirdLabel)
    (hneRightThird : rightLabel ≠ thirdLabel) :
    tripleGapDet (design.atom leftLabel) (design.atom rightLabel)
        (design.atom thirdLabel) = 0 := by
  classical
  set pairSet : Finset (Fin size) := {leftLabel, rightLabel} with hpairDef
  have hthirdMem : thirdLabel ∈ pairSetᶜ := by
    simp only [hpairDef, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨Ne.symm hneLeftThird, Ne.symm hneRightThird⟩
  have hnonneg : ∀ label ∈ pairSetᶜ,
      0 ≤ - (design.weight label
        * tripleGapDet (design.atom leftLabel) (design.atom rightLabel)
            (design.atom label)) := by
    intro label hlabel
    have hnotMem : label ∉ pairSet := Finset.mem_compl.mp hlabel
    have hlabelNe : leftLabel ≠ label ∧ rightLabel ≠ label := by
      simp only [hpairDef, Finset.mem_insert, Finset.mem_singleton] at hnotMem
      push Not at hnotMem
      exact ⟨Ne.symm hnotMem.1, Ne.symm hnotMem.2⟩
    have hterm := tripleGapDet_nonpos_of_isTie design htie hne hlabelNe.1 hlabelNe.2 hheavy
      hadmissible
    have := mul_nonpos_of_nonneg_of_nonpos (design.weight_pos label).le hterm
    linarith
  have htotal : ∑ label ∈ pairSet, design.weight label
        * tripleGapDet (design.atom leftLabel) (design.atom rightLabel) (design.atom label)
      + ∑ label ∈ pairSetᶜ, design.weight label
        * tripleGapDet (design.atom leftLabel) (design.atom rightLabel) (design.atom label)
      = 2 - leverageOf (design.atom leftLabel) - leverageOf (design.atom rightLabel) := by
    rw [Finset.sum_add_sum_compl]
    exact sum_weight_mul_tripleGapDet design leftLabel rightLabel
  have hinside : ∑ label ∈ pairSet, design.weight label
        * tripleGapDet (design.atom leftLabel) (design.atom rightLabel) (design.atom label)
      = design.weight leftLabel
          * (-2 * crossNormSq (design.atom leftLabel) (design.atom rightLabel)
            + 2 * leverageOf (design.atom leftLabel)
            + leverageOf (design.atom rightLabel) - 1)
        + design.weight rightLabel
          * (-2 * crossNormSq (design.atom leftLabel) (design.atom rightLabel)
            + leverageOf (design.atom leftLabel)
            + 2 * leverageOf (design.atom rightLabel) - 1) := by
    rw [hpairDef, Finset.sum_pair hne, tripleGapDet_repeat_left, tripleGapDet_repeat_right]
  rw [hinside] at htotal
  have hcomplZero : ∑ label ∈ pairSetᶜ, design.weight label
      * tripleGapDet (design.atom leftLabel) (design.atom rightLabel)
          (design.atom label) = 0 := by
    nlinarith [htotal, hequality]
  have houtsideZero : ∑ label ∈ pairSetᶜ, - (design.weight label
      * tripleGapDet (design.atom leftLabel) (design.atom rightLabel)
          (design.atom label)) = 0 := by
    rw [Finset.sum_neg_distrib, hcomplZero, neg_zero]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp houtsideZero thirdLabel hthirdMem
  have hweightPos := design.weight_pos thirdLabel
  have hproduct : design.weight thirdLabel
      * tripleGapDet (design.atom leftLabel) (design.atom rightLabel)
          (design.atom thirdLabel) = 0 := by linarith
  rcases mul_eq_zero.mp hproduct with hbad | hgood
  · exact absurd hbad hweightPos.ne'
  · exact hgood

/-- **THE CEILING IS ATTAINED AT THE TETRAHEDRON.**  Every leverage of
`Gtz.tetraDesign` is `3` and every pairing is `-1`, so every pair reads squared area
`8` against a ceiling of `8`.  The `(4,3)` tetrahedron is a certified tie, so no
constant sharpens the ceiling, and by the equality locus every triple through every
one of its pairs has a vanishing third minor. -/
theorem tetraDesign_crossNormSq_eq_ceiling {leftLabel rightLabel : Fin 4}
    (hne : leftLabel ≠ rightLabel) :
    2 * (tetraDesign.weight leftLabel + tetraDesign.weight rightLabel)
        * crossNormSq (tetraDesign.atom leftLabel) (tetraDesign.atom rightLabel)
      = leverageOf (tetraDesign.atom leftLabel)
          + leverageOf (tetraDesign.atom rightLabel) - 2
        + tetraDesign.weight leftLabel
            * (2 * leverageOf (tetraDesign.atom leftLabel)
              + leverageOf (tetraDesign.atom rightLabel) - 1)
        + tetraDesign.weight rightLabel
            * (leverageOf (tetraDesign.atom leftLabel)
              + 2 * leverageOf (tetraDesign.atom rightLabel) - 1) := by
  have hlev : ∀ vertex : Fin 4, leverageOf (tetraDesign.atom vertex) = 3 := by
    intro vertex
    rw [leverageOf_eq_dotProduct]
    exact tetraAtom_dot_self vertex
  have hpair : tetraDesign.atom leftLabel ⬝ᵥ tetraDesign.atom rightLabel = -1 := by
    show tetraAtom leftLabel ⬝ᵥ tetraAtom rightLabel = -1
    fin_cases leftLabel <;> fin_cases rightLabel <;>
      simp_all [tetraAtom, dotProduct, Fin.sum_univ_three]
  have hweight : ∀ vertex : Fin 4, tetraDesign.weight vertex = 1 / 4 := fun _ => rfl
  rw [crossNormSq_eq_leverage_mul_sub_sq, hlev, hlev, hpair, hweight, hweight]
  norm_num

end Gtz
