import Mathlib
import Gtz.Wave.PluckerEnergySupply
import Gtz.Wave.QuadDropSign

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12800000

/-!
# The Schur floor of the determinantal energy

`Gtz.AtomPluckerTenth` is the named residue of `Gtz.Wave.PluckerEnergySupply`: the
level-two energy of a real rank-three Parseval frame of six atoms stays at or
below TEN times the level-three energy.  It is sharp at the icosahedral frame and
it is real-only.  This module proves it for every frame whose six leverages are
all one half, and it isolates what is left.

## The chain

The frame enters through the HEAT MATRIX

  `M y z = 20 * (a y . a z) ^ 2 - 5 / 3`.

At balanced leverages `M` is twenty times the Gram matrix of the six traceless
blocks `a y a y ^ T - I / 6`, so `M` is positive semidefinite, its trace is `20`,
and the frame law sends the all-ones vector to zero, so its determinant is `0`.

`Gtz.atomEnergyGap_heat` is the ONE identity that carries the frame:

  `1200 * (10 * E3 - E2) = tr (M ^ 3) - 9 * tr (M ^ 2) + 400`.

`Gtz.atomPsdTraceFloor` says the right side is never negative.  It divides the
scale-free `Gtz.atomPsdCubicTraceFloor`,

  `20 * tr (N ^ 3) - 9 * tr N * tr (N ^ 2) + (tr N) ^ 3 ≥ 0`
  for every positive semidefinite `N` of order six with `det N = 0`,

whose proof reads the six eigenvalues of `N`, discards the one the determinant
forces to zero, and applies

  `Gtz.atomFiveHomogeneous_nonneg` : `20 * p3 - 9 * p1 * p2 + p1 ^ 3 ≥ 0` for
  five numbers that are not negative,

which is EXACTLY twice the total of Schur's inequality of the first degree over
the ten triples of five slots (`Gtz.atomFiveHomogeneous_eq_schurSum`, an identity
that needs no hypothesis).  The two equality points, five equal readings and four
equal readings with a zero, are the complete graph on six slots and the complete
bipartite graph on three and three, which are the icosahedral frame and a complex
mutually unbiased basis.

The sixth slot is where the RANK enters.  Six equal readings give `-6`, so the
statement is false without the forced zero, and the forced zero is the vanishing
determinant.

## Where the realness enters, exactly

Every MATRIX hypothesis of the proof survives the Hermitian field.  Over the
complex field the heat matrix `M y z = 20 * |G y z| ^ 2 - 5 / 3` is still the Gram
matrix of the six traceless Hermitian blocks, its trace is still `20`, the
all-ones vector is still in its kernel, and `Gtz.atomPsdCubicTraceFloor` still
reads at or above zero.  What breaks is the ENERGY IDENTITY, and it breaks in
exactly one term.  At balanced leverages, over either field,

  `1200 * (10 * E3 - E2) = tr (M ^ 3) - 9 * tr (M ^ 2) + 400
      - 48000 * (total over the twenty triples of `Im (G y z * G z v * G v y) ^ 2`)`.

Over the real field the last total is zero, because a product of three real
numbers is real.  Over the complex field it is the whole deficit: at the complex
extremal, where `10 * E3 - E2 = -1/16` and `E3 / E2 = 7 / 78`, the two sides read
`-75 = 18.75 - 48000 * (1 / 512)`, and both readings are exact.

So the real-only law that this module spends is that the TRIANGLE CYCLE PRODUCT
of the Gram carries FULL MODULUS.  It is the Ptolemy law of the campaign in its
squared form, and it is spent ONCE, inside `Gtz.atomEnergyGap_heat`, at the step
`256 * (total of the squared cycle products) = 4 * (third heat total)`, which is a
plain `ring` step over the real field and a strict inequality over the complex
field.

## The sign of the eigenvalue statement

In eigenvalue coordinates the floor reads `6 * S2 + 5 * S3 ≥ 1` for the five
non-Perron eigenvalues of the doubly stochastic heat, and in elementary
coordinates `Gtz.atomQuintetElem_floor` reads

  `0 ≤ e2 + 5 * e3`.

The opposite convention `e1 * e2 ≥ 5 * e3` is FALSE, and
`Gtz.atomQuintetLeg_refuted` gives the witness `(-1,-1,1,0,0)`, a permitted
spectrum on which `e1 * e2 = 1` and `5 * e3 = 5`.
`Gtz.atomQuintetLeg_refuted_realized` gives a witness that a FRAME of the cell
carries: the doubled orthonormal basis, whose heat matrix is the perfect matching
and whose non-Perron spectrum is `(1,1,-1,-1,-1)`.

## What this module does NOT reach

`Gtz.atomPluckerTenth_of_balanced` needs `Gtz.AtomBalanced`.  Every leverage of
the icosahedral frame is one half.  An attempt to REFUTE `10 * E3 - E2 ≥ 0` at
3000 restarts by 30000 steps by 6 basin hops, half of them started far from
balance on purpose, reached `-8.6e-13` and put its argmin at the icosahedron,
inside the slice that is proved above.  The attempt ran behind a calibration gate
that reproduced `E2 / E3 = 10` at the exact icosahedral Gram to `2e-16` and
`inf E3 / E2 = 1/10` to `1.3e-15`.  So `Gtz.AtomPluckerTenthUnbalanced` carries no
measured floor of its own: it carries a failed refutation whose argmin is a
theorem.

The residue also has room.  At a pinned squared leverage imbalance
`q = ∑ (s y - 1/2) ^ 2` the measured minimum of `10 * E3 - E2` grows about like
`q / 2`, and it reads `0.127` at `q = 0.24`.  The exact real extremal of the
spectral value, whose leverages are five fourteenths and nine fourteenths, reads
`E2 / E3 = 8.9215`.

But the reduction above spends `AtomBalanced` twice and neither use survives
without it.  At general leverages the heat is `(a y . a z) ^ 2 / sqrt (s y * s z)`,
which carries the Perron vector `sqrt s` and not the all-ones vector, and the
twenty triple determinants pick up the weights `s y * s z * s v`, which the trace
of a power cannot read.  The scale-free `Gtz.atomPsdCubicTraceFloor` DOES survive:
for every choice of shift `c` with total one, the table
`(a y . a z) ^ 2 - c z * s y - c y * s z + 3 * c y * c z` is a positive
semidefinite matrix with the all-ones vector in its kernel.  But at the exact
real extremal that floor reads `0.389` against `3 * (10 * E3 - E2) = 0.269`, so it
OVERSHOOTS off balance and cannot be used as a lower bound with the balanced
constant.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

Every statement below is proved.  `Gtz.AtomPluckerTenthUnbalanced` is a
definition, and the one theorem that reads it takes it as a hypothesis.

## Vacuity

`Gtz.atomSchurForm_nonneg`, `Gtz.atomFiveCubic_nonneg`, `Gtz.atomQuintetFloor`
and `Gtz.atomPsdTraceFloor` are unconditional.  `Gtz.atomPluckerTenth_of_balanced`
is not vacuous: `Gtz.atomBalanced_dropWitness` shows that the standing red-team
datum of the campaign is balanced, and `Gtz.atomPluckerTenth_dropWitness` spends
the theorem on it.  The icosahedral frame is balanced too, and it is where the
bound is attained.
-/

namespace Gtz

/-! ## Layer 0 — Schur's inequality of the first degree -/

/-- The SCHUR FORM of three readings.  Schur's inequality of the first degree
says it is never negative when the three readings are not negative. -/
def atomSchurForm (valueOne valueTwo valueThree : ℝ) : ℝ :=
  valueOne * (valueOne - valueTwo) * (valueOne - valueThree)
    + valueTwo * (valueTwo - valueOne) * (valueTwo - valueThree)
    + valueThree * (valueThree - valueOne) * (valueThree - valueTwo)

/-- **THE SORTED SCHUR STEP.**  When the three readings come in order, the Schur
form is the total of two products that are not negative.  The identity is

  `S = (a - b) ^ 2 * (a + b - c) + c * (a - c) * (b - c)`,

and both terms are not negative when `0 ≤ c ≤ b ≤ a`. -/
theorem atomSchurForm_sorted {high mid low : ℝ} (hlow : 0 ≤ low) (hlowMid : low ≤ mid)
    (hmidHigh : mid ≤ high) : 0 ≤ atomSchurForm high mid low := by
  have hsplit : atomSchurForm high mid low
      = (high - mid) ^ 2 * (high + mid - low) + low * (high - low) * (mid - low) := by
    simp only [atomSchurForm]; ring
  rw [hsplit]
  have hone : (0:ℝ) ≤ (high - mid) ^ 2 * (high + mid - low) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have htwo : (0:ℝ) ≤ low * (high - low) * (mid - low) :=
    mul_nonneg (mul_nonneg hlow (by linarith)) (by linarith)
  linarith

/-- **SCHUR'S INEQUALITY OF THE FIRST DEGREE.**  The Schur form of three readings
that are not negative is never negative.  The Schur form does not read the order
of its three arguments, so the sorted step closes all six orders. -/
theorem atomSchurForm_nonneg (valueOne valueTwo valueThree : ℝ)
    (hone : 0 ≤ valueOne) (htwo : 0 ≤ valueTwo) (hthree : 0 ≤ valueThree) :
    0 ≤ atomSchurForm valueOne valueTwo valueThree := by
  have hmove : ∀ high mid low : ℝ,
      atomSchurForm high mid low = atomSchurForm valueOne valueTwo valueThree →
      0 ≤ low → low ≤ mid → mid ≤ high → 0 ≤ atomSchurForm valueOne valueTwo valueThree := by
    intro high mid low hshape hlow hlowMid hmidHigh
    rw [← hshape]
    exact atomSchurForm_sorted hlow hlowMid hmidHigh
  rcases le_total valueOne valueTwo with h12 | h12 <;>
    rcases le_total valueTwo valueThree with h23 | h23 <;>
    rcases le_total valueOne valueThree with h13 | h13
  · exact hmove valueThree valueTwo valueOne (by simp only [atomSchurForm]; try ring) hone h12 h23
  · exact hmove valueThree valueTwo valueOne (by simp only [atomSchurForm]; try ring) hone h12 h23
  · exact hmove valueTwo valueThree valueOne (by simp only [atomSchurForm]; try ring) hone h13 h23
  · exact hmove valueTwo valueOne valueThree (by simp only [atomSchurForm]; try ring) hthree h13 h12
  · exact hmove valueThree valueOne valueTwo (by simp only [atomSchurForm]; try ring) htwo h12 h13
  · exact hmove valueOne valueThree valueTwo (by simp only [atomSchurForm]; try ring) htwo h23 h13
  · exact hmove valueOne valueTwo valueThree (by simp only [atomSchurForm]; try ring) hthree h23 h12
  · exact hmove valueOne valueTwo valueThree (by simp only [atomSchurForm]; try ring) hthree h23 h12

/-! ## Layer 1 — the five-slot cubic floor -/

/-- The CUBIC READING of five numbers: the total of `v * (v - 4) * (v - 5)`.  It
is the trace of `M ^ 3 - 9 * M ^ 2 + 20 * M` read on the five eigenvalues that
the heat matrix leaves after the forced zero. -/
def atomFiveCubic (valueOne valueTwo valueThree valueFour valueFive : ℝ) : ℝ :=
  valueOne * (valueOne - 4) * (valueOne - 5)
    + valueTwo * (valueTwo - 4) * (valueTwo - 5)
    + valueThree * (valueThree - 4) * (valueThree - 5)
    + valueFour * (valueFour - 4) * (valueFour - 5)
    + valueFive * (valueFive - 4) * (valueFive - 5)

/-- The total of the Schur form over the TEN triples of five slots. -/
def atomTenSchurSum (valueOne valueTwo valueThree valueFour valueFive : ℝ) : ℝ :=
  atomSchurForm valueOne valueTwo valueThree + atomSchurForm valueOne valueTwo valueFour
    + atomSchurForm valueOne valueTwo valueFive + atomSchurForm valueOne valueThree valueFour
    + atomSchurForm valueOne valueThree valueFive + atomSchurForm valueOne valueFour valueFive
    + atomSchurForm valueTwo valueThree valueFour + atomSchurForm valueTwo valueThree valueFive
    + atomSchurForm valueTwo valueFour valueFive + atomSchurForm valueThree valueFour valueFive

/-- **THE CUBIC READING IS THE SCHUR TOTAL.**  On the simplex of total `20`, ten
times the cubic reading of five numbers is exactly the total of Schur's form over
the ten triples of the five slots.

This is the whole content of the floor.  The two points where the cubic reading
is zero, `(4,4,4,4,4)` and `(0,5,5,5,5)`, are exactly the points where all ten
Schur forms are zero at the same time. -/
theorem atomFiveCubic_eq_schurSum (valueOne valueTwo valueThree valueFour valueFive : ℝ)
    (htotal : valueOne + valueTwo + valueThree + valueFour + valueFive = 20) :
    10 * atomFiveCubic valueOne valueTwo valueThree valueFour valueFive
      = atomTenSchurSum valueOne valueTwo valueThree valueFour valueFive := by
  simp only [atomFiveCubic, atomTenSchurSum, atomSchurForm]
  linear_combination
    ((9 / 2) * (valueOne ^ 2 + valueTwo ^ 2 + valueThree ^ 2 + valueFour ^ 2 + valueFive ^ 2)
      - (1 / 2) * (valueOne + valueTwo + valueThree + valueFour + valueFive)
        * ((valueOne + valueTwo + valueThree + valueFour + valueFive) + 20)) * htotal

/-- **THE FIVE-SLOT CUBIC FLOOR.**  Five numbers that are not negative and total
`20` have a cubic reading that is not negative.

The bound is sharp twice.  It is the eigenvalue statement that the whole tenth
rests on, and it is strictly stronger than the statement the case analysis of the
brief needs, because it asks for no upper bound on the numbers. -/
theorem atomFiveCubic_nonneg {valueOne valueTwo valueThree valueFour valueFive : ℝ}
    (hone : 0 ≤ valueOne) (htwo : 0 ≤ valueTwo) (hthree : 0 ≤ valueThree)
    (hfour : 0 ≤ valueFour) (hfive : 0 ≤ valueFive)
    (htotal : valueOne + valueTwo + valueThree + valueFour + valueFive = 20) :
    0 ≤ atomFiveCubic valueOne valueTwo valueThree valueFour valueFive := by
  have hid := atomFiveCubic_eq_schurSum valueOne valueTwo valueThree valueFour valueFive htotal
  have s123 := atomSchurForm_nonneg valueOne valueTwo valueThree hone htwo hthree
  have s124 := atomSchurForm_nonneg valueOne valueTwo valueFour hone htwo hfour
  have s125 := atomSchurForm_nonneg valueOne valueTwo valueFive hone htwo hfive
  have s134 := atomSchurForm_nonneg valueOne valueThree valueFour hone hthree hfour
  have s135 := atomSchurForm_nonneg valueOne valueThree valueFive hone hthree hfive
  have s145 := atomSchurForm_nonneg valueOne valueFour valueFive hone hfour hfive
  have s234 := atomSchurForm_nonneg valueTwo valueThree valueFour htwo hthree hfour
  have s235 := atomSchurForm_nonneg valueTwo valueThree valueFive htwo hthree hfive
  have s245 := atomSchurForm_nonneg valueTwo valueFour valueFive htwo hfour hfive
  have s345 := atomSchurForm_nonneg valueThree valueFour valueFive hthree hfour hfive
  simp only [atomTenSchurSum] at hid
  linarith

/-- The first equality point of the cubic floor: five copies of `4`.  It is the
complete graph on six slots, which is the icosahedral frame. -/
theorem atomFiveCubic_equal : atomFiveCubic 4 4 4 4 4 = 0 := by
  simp only [atomFiveCubic]; norm_num

/-- The second equality point of the cubic floor: one `0` and four copies of `5`.
It is the complete bipartite graph on three and three, which is a complex
mutually unbiased basis and is NOT real. -/
theorem atomFiveCubic_split : atomFiveCubic 0 5 5 5 5 = 0 := by
  simp only [atomFiveCubic]; norm_num

/-! ## Layer 2 — the eigenvalue form, and the sign of the convention -/

/-- The SECOND ELEMENTARY READING of five numbers. -/
def atomQuintetElemTwo (valueOne valueTwo valueThree valueFour valueFive : ℝ) : ℝ :=
  valueOne * valueTwo + valueOne * valueThree + valueOne * valueFour + valueOne * valueFive
    + valueTwo * valueThree + valueTwo * valueFour + valueTwo * valueFive
    + valueThree * valueFour + valueThree * valueFive + valueFour * valueFive

/-- The THIRD ELEMENTARY READING of five numbers. -/
def atomQuintetElemThree (valueOne valueTwo valueThree valueFour valueFive : ℝ) : ℝ :=
  valueOne * valueTwo * valueThree + valueOne * valueTwo * valueFour
    + valueOne * valueTwo * valueFive + valueOne * valueThree * valueFour
    + valueOne * valueThree * valueFive + valueOne * valueFour * valueFive
    + valueTwo * valueThree * valueFour + valueTwo * valueThree * valueFive
    + valueTwo * valueFour * valueFive + valueThree * valueFour * valueFive

/-- **THE SPECTRAL QUINTET FLOOR.**  Five numbers that are at least `-1` and
total `-1` obey

  `1 ≤ 6 * (total of the squares) + 5 * (total of the cubes)`.

These are the five non-Perron eigenvalues of a symmetric doubly stochastic matrix
of order six with a zero diagonal.  The shift `v = 5 * (lambda + 1)` sends the
box floor to the nonnegative orthant and the total `-1` to the total `20`, and
then the identity

  `atomFiveCubic v = 25 * (6 * S2 + 5 * S3 + S1)`

turns the statement into the five-slot cubic floor.  No upper bound on the
eigenvalues is used. -/
theorem atomQuintetFloor {eigenOne eigenTwo eigenThree eigenFour eigenFive : ℝ}
    (hone : -1 ≤ eigenOne) (htwo : -1 ≤ eigenTwo) (hthree : -1 ≤ eigenThree)
    (hfour : -1 ≤ eigenFour) (hfive : -1 ≤ eigenFive)
    (htotal : eigenOne + eigenTwo + eigenThree + eigenFour + eigenFive = -1) :
    1 ≤ 6 * (eigenOne ^ 2 + eigenTwo ^ 2 + eigenThree ^ 2 + eigenFour ^ 2 + eigenFive ^ 2)
      + 5 * (eigenOne ^ 3 + eigenTwo ^ 3 + eigenThree ^ 3 + eigenFour ^ 3 + eigenFive ^ 3) := by
  have hcubic := atomFiveCubic_nonneg (valueOne := 5 * (eigenOne + 1))
    (valueTwo := 5 * (eigenTwo + 1)) (valueThree := 5 * (eigenThree + 1))
    (valueFour := 5 * (eigenFour + 1)) (valueFive := 5 * (eigenFive + 1))
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hshape : atomFiveCubic (5 * (eigenOne + 1)) (5 * (eigenTwo + 1)) (5 * (eigenThree + 1))
        (5 * (eigenFour + 1)) (5 * (eigenFive + 1))
      = 25 * (6 * (eigenOne ^ 2 + eigenTwo ^ 2 + eigenThree ^ 2 + eigenFour ^ 2 + eigenFive ^ 2)
          + 5 * (eigenOne ^ 3 + eigenTwo ^ 3 + eigenThree ^ 3 + eigenFour ^ 3 + eigenFive ^ 3)
          + (eigenOne + eigenTwo + eigenThree + eigenFour + eigenFive)) := by
    simp only [atomFiveCubic]; ring
  rw [hshape, htotal] at hcubic
  linarith

/-- **THE ELEMENTARY FORM OF THE QUINTET FLOOR.**  On the hyperplane of total
`-1`, the power-sum reading and the elementary reading agree up to the factor
three. -/
theorem atomQuintetFloor_elementary {eigenOne eigenTwo eigenThree eigenFour eigenFive : ℝ}
    (htotal : eigenOne + eigenTwo + eigenThree + eigenFour + eigenFive = -1) :
    6 * (eigenOne ^ 2 + eigenTwo ^ 2 + eigenThree ^ 2 + eigenFour ^ 2 + eigenFive ^ 2)
        + 5 * (eigenOne ^ 3 + eigenTwo ^ 3 + eigenThree ^ 3 + eigenFour ^ 3 + eigenFive ^ 3) - 1
      = 3 * (atomQuintetElemTwo eigenOne eigenTwo eigenThree eigenFour eigenFive
          + 5 * atomQuintetElemThree eigenOne eigenTwo eigenThree eigenFour eigenFive) := by
  simp only [atomQuintetElemTwo, atomQuintetElemThree]
  linear_combination
    (5 * (eigenOne + eigenTwo + eigenThree + eigenFour + eigenFive) ^ 2
      + (eigenOne + eigenTwo + eigenThree + eigenFour + eigenFive) - 1
      - 15 * (eigenOne * eigenTwo + eigenOne * eigenThree + eigenOne * eigenFour
          + eigenOne * eigenFive + eigenTwo * eigenThree + eigenTwo * eigenFour
          + eigenTwo * eigenFive + eigenThree * eigenFour + eigenThree * eigenFive
          + eigenFour * eigenFive)) * htotal

/-- **THE SIGN CONVENTION, SETTLED.**  The correct elementary form of the quintet
floor is `0 ≤ e2 + 5 * e3`. -/
theorem atomQuintetElem_floor {eigenOne eigenTwo eigenThree eigenFour eigenFive : ℝ}
    (hone : -1 ≤ eigenOne) (htwo : -1 ≤ eigenTwo) (hthree : -1 ≤ eigenThree)
    (hfour : -1 ≤ eigenFour) (hfive : -1 ≤ eigenFive)
    (htotal : eigenOne + eigenTwo + eigenThree + eigenFour + eigenFive = -1) :
    0 ≤ atomQuintetElemTwo eigenOne eigenTwo eigenThree eigenFour eigenFive
      + 5 * atomQuintetElemThree eigenOne eigenTwo eigenThree eigenFour eigenFive := by
  have hfloor := atomQuintetFloor hone htwo hthree hfour hfive htotal
  have hshape := atomQuintetFloor_elementary htotal
  linarith

/-- **THE OPPOSITE CONVENTION IS FALSE.**  The reading `e1 * e2 ≥ 5 * e3` fails on
the permitted spectrum `(-1,-1,1,0,0)`, where `e1 * e2 = 1` and `5 * e3 = 5`.

The two equality points of the floor cannot separate the two conventions,
because both readings are zero at each of them.  This witness separates them. -/
theorem atomQuintetLeg_refuted :
    ¬ (∀ eigenOne eigenTwo eigenThree eigenFour eigenFive : ℝ,
        -1 ≤ eigenOne → -1 ≤ eigenTwo → -1 ≤ eigenThree → -1 ≤ eigenFour → -1 ≤ eigenFive →
        eigenOne + eigenTwo + eigenThree + eigenFour + eigenFive = -1 →
        5 * atomQuintetElemThree eigenOne eigenTwo eigenThree eigenFour eigenFive
          ≤ (eigenOne + eigenTwo + eigenThree + eigenFour + eigenFive)
            * atomQuintetElemTwo eigenOne eigenTwo eigenThree eigenFour eigenFive) := by
  intro hclaim
  have hbad := hclaim (-1) (-1) 1 0 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [atomQuintetElemTwo, atomQuintetElemThree] at hbad
  norm_num at hbad

/-- The witness of `Gtz.atomQuintetLeg_refuted` DOES obey the correct form, and
with room to spare. -/
theorem atomQuintetElem_witness :
    atomQuintetElemTwo (-1) (-1) 1 0 0 + 5 * atomQuintetElemThree (-1) (-1) 1 0 0 = 4 := by
  simp only [atomQuintetElemTwo, atomQuintetElemThree]; norm_num

/-- The HOMOGENEOUS CUBIC READING of five numbers,
`20 * p3 - 9 * p1 * p2 + p1 ^ 3`.  It is the scale-free form of the cubic
reading: on the hyperplane of total `20` it is twenty times
`Gtz.atomFiveCubic`. -/
def atomFiveHomogeneous (valueOne valueTwo valueThree valueFour valueFive : ℝ) : ℝ :=
  20 * (valueOne ^ 3 + valueTwo ^ 3 + valueThree ^ 3 + valueFour ^ 3 + valueFive ^ 3)
    - 9 * (valueOne + valueTwo + valueThree + valueFour + valueFive)
        * (valueOne ^ 2 + valueTwo ^ 2 + valueThree ^ 2 + valueFour ^ 2 + valueFive ^ 2)
    + (valueOne + valueTwo + valueThree + valueFour + valueFive) ^ 3

/-- **THE HOMOGENEOUS READING IS TWICE THE SCHUR TOTAL.**  This identity needs no
hypothesis at all: it holds for every five readings.  It is the reason the whole
tenth is Schur's inequality and nothing else. -/
theorem atomFiveHomogeneous_eq_schurSum (valueOne valueTwo valueThree valueFour valueFive : ℝ) :
    atomFiveHomogeneous valueOne valueTwo valueThree valueFour valueFive
      = 2 * atomTenSchurSum valueOne valueTwo valueThree valueFour valueFive := by
  simp only [atomFiveHomogeneous, atomTenSchurSum, atomSchurForm]; ring

/-- **THE HOMOGENEOUS CUBIC FLOOR.**  Five readings that are not negative have a
homogeneous cubic reading that is not negative.  No total is pinned. -/
theorem atomFiveHomogeneous_nonneg {valueOne valueTwo valueThree valueFour valueFive : ℝ}
    (hone : 0 ≤ valueOne) (htwo : 0 ≤ valueTwo) (hthree : 0 ≤ valueThree)
    (hfour : 0 ≤ valueFour) (hfive : 0 ≤ valueFive) :
    0 ≤ atomFiveHomogeneous valueOne valueTwo valueThree valueFour valueFive := by
  rw [atomFiveHomogeneous_eq_schurSum]
  have s123 := atomSchurForm_nonneg valueOne valueTwo valueThree hone htwo hthree
  have s124 := atomSchurForm_nonneg valueOne valueTwo valueFour hone htwo hfour
  have s125 := atomSchurForm_nonneg valueOne valueTwo valueFive hone htwo hfive
  have s134 := atomSchurForm_nonneg valueOne valueThree valueFour hone hthree hfour
  have s135 := atomSchurForm_nonneg valueOne valueThree valueFive hone hthree hfive
  have s145 := atomSchurForm_nonneg valueOne valueFour valueFive hone hfour hfive
  have s234 := atomSchurForm_nonneg valueTwo valueThree valueFour htwo hthree hfour
  have s235 := atomSchurForm_nonneg valueTwo valueThree valueFive htwo hthree hfive
  have s245 := atomSchurForm_nonneg valueTwo valueFour valueFive htwo hfour hfive
  have s345 := atomSchurForm_nonneg valueThree valueFour valueFive hthree hfour hfive
  simp only [atomTenSchurSum]
  linarith

/-- **THE OPPOSITE CONVENTION FAILS AT AN ACTUAL FRAME.**  The witness of
`Gtz.atomQuintetLeg_refuted` is a permitted spectrum, but nothing above says that
a frame carries it.  This one is carried by a frame of the cell.

Take the DOUBLED ORTHONORMAL BASIS: three pairs of equal atoms, each atom of
squared length one half.  It is a real Parseval frame of six atoms, every
leverage is one half, and its Gram is three copies of the two-by-two block with
every entry one half.  Its heat matrix is the PERFECT MATCHING, which is
symmetric, doubly stochastic and zero on the diagonal.  The perfect matching has
the spectrum `(1,1,1,-1,-1,-1)`, so the five non-Perron eigenvalues are
`(1,1,-1,-1,-1)`, which total `-1` and sit in the box.

There `e2 = -2` and `e3 = 2`.  The correct form reads `e2 + 5 * e3 = 8`, and the
opposite reading gives `e1 * e2 = 2` against `5 * e3 = 10`.  So the opposite
convention fails at a frame the cell actually contains, and not only at an
abstract five-tuple. -/
theorem atomQuintetLeg_refuted_realized :
    atomQuintetElemTwo 1 1 (-1) (-1) (-1) = -2
      ∧ atomQuintetElemThree 1 1 (-1) (-1) (-1) = 2
      ∧ (1 + 1 + (-1) + (-1) + (-1) : ℝ) = -1
      ∧ (1 + 1 + (-1) + (-1) + (-1) : ℝ) * atomQuintetElemTwo 1 1 (-1) (-1) (-1)
          < 5 * atomQuintetElemThree 1 1 (-1) (-1) (-1)
      ∧ 0 ≤ atomQuintetElemTwo 1 1 (-1) (-1) (-1)
          + 5 * atomQuintetElemThree 1 1 (-1) (-1) (-1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [atomQuintetElemTwo, atomQuintetElemThree]

/-! ## Layer 3 — the trace floor of a positive semidefinite matrix -/

open Matrix in
/-- **THE POWER-SUM LAW OF A HERMITIAN MATRIX.**  The trace of a power is the
total of the same power of the eigenvalues.

Mathlib carries `Matrix.IsHermitian.trace_eq_sum_eigenvalues` and
`Matrix.IsHermitian.det_eq_prod_eigenvalues` but nothing for a general power.
The proof conjugates by the eigenvector unitary and cancels with the cyclic
trace law. -/
theorem atomHermitianTracePow {size field : Type*} [Fintype size] [DecidableEq size]
    [RCLike field] {target : Matrix size size field} (hherm : target.IsHermitian)
    (power : ℕ) :
    (target ^ power).trace = ∑ index, ((hherm.eigenvalues index : ℝ) : field) ^ power := by
  conv_lhs => rw [hherm.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, diagonal_pow, trace_diagonal]
  simp

open Matrix in
/-- The power-sum law over the real field, with no coercion left. -/
theorem atomRealTracePow {size : Type*} [Fintype size] [DecidableEq size]
    {target : Matrix size size ℝ} (hherm : target.IsHermitian) (power : ℕ) :
    (target ^ power).trace = ∑ index, hherm.eigenvalues index ^ power := by
  simpa using atomHermitianTracePow hherm power

/-- **THE SIX-SLOT HOMOGENEOUS FLOOR.**  Six readings that are not negative and
carry a zero have a homogeneous cubic reading that is not negative.  The zero
drops out of all three power totals, so the statement is the five-slot floor with
a sixth slot that reads nothing.

The sixth slot is where the rank enters.  Without it the statement is FALSE: six
EQUAL readings give `20 * 6 - 9 * 6 * 6 + 216 = -6`, which is negative.  The
matrix that carries these readings has a zero determinant, and that is what
supplies the zero. -/
theorem atomSixHomogeneous_nonneg {slotOne slotTwo slotThree slotFour slotFive slotSix : ℝ}
    (hone : 0 ≤ slotOne) (htwo : 0 ≤ slotTwo) (hthree : 0 ≤ slotThree)
    (hfour : 0 ≤ slotFour) (hfive : 0 ≤ slotFive) (hsix : 0 ≤ slotSix)
    (hzero : slotOne = 0 ∨ slotTwo = 0 ∨ slotThree = 0 ∨ slotFour = 0 ∨ slotFive = 0
      ∨ slotSix = 0) :
    0 ≤ 20 * (slotOne ^ 3 + slotTwo ^ 3 + slotThree ^ 3 + slotFour ^ 3 + slotFive ^ 3
          + slotSix ^ 3)
      - 9 * (slotOne + slotTwo + slotThree + slotFour + slotFive + slotSix)
          * (slotOne ^ 2 + slotTwo ^ 2 + slotThree ^ 2 + slotFour ^ 2 + slotFive ^ 2
            + slotSix ^ 2)
      + (slotOne + slotTwo + slotThree + slotFour + slotFive + slotSix) ^ 3 := by
  have hfive5 : ∀ partOne partTwo partThree partFour partFive : ℝ,
      0 ≤ partOne → 0 ≤ partTwo → 0 ≤ partThree → 0 ≤ partFour → 0 ≤ partFive →
      0 ≤ 20 * (partOne ^ 3 + partTwo ^ 3 + partThree ^ 3 + partFour ^ 3 + partFive ^ 3)
        - 9 * (partOne + partTwo + partThree + partFour + partFive)
            * (partOne ^ 2 + partTwo ^ 2 + partThree ^ 2 + partFour ^ 2 + partFive ^ 2)
        + (partOne + partTwo + partThree + partFour + partFive) ^ 3 := by
    intro partOne partTwo partThree partFour partFive p1 p2 p3 p4 p5
    simpa only [atomFiveHomogeneous] using atomFiveHomogeneous_nonneg p1 p2 p3 p4 p5
  rcases hzero with hz | hz | hz | hz | hz | hz
  · subst hz; linarith [hfive5 slotTwo slotThree slotFour slotFive slotSix htwo hthree hfour hfive hsix]
  · subst hz; linarith [hfive5 slotOne slotThree slotFour slotFive slotSix hone hthree hfour hfive hsix]
  · subst hz; linarith [hfive5 slotOne slotTwo slotFour slotFive slotSix hone htwo hfour hfive hsix]
  · subst hz; linarith [hfive5 slotOne slotTwo slotThree slotFive slotSix hone htwo hthree hfive hsix]
  · subst hz; linarith [hfive5 slotOne slotTwo slotThree slotFour slotSix hone htwo hthree hfour hsix]
  · subst hz; linarith [hfive5 slotOne slotTwo slotThree slotFour slotFive hone htwo hthree hfour hfive]

open Matrix in
/-- **THE HOMOGENEOUS TRACE FLOOR.**  A positive semidefinite matrix of order six
whose determinant is zero obeys

  `20 * tr (N ^ 3) - 9 * tr N * tr (N ^ 2) + (tr N) ^ 3 ≥ 0`.

This is the scale-free centre of the module.  The determinant forces one
eigenvalue to be zero, the remaining five are not negative, and the total of
Schur's inequality over their ten triples closes it.  Both equality cases are
attained: five equal eigenvalues with one zero, and four equal eigenvalues with
two zeros.

A successor lane that leaves the balanced slice needs THIS form, because at
general leverages the shifted Gram of the six blocks carries no natural
normalisation of its trace. -/
theorem atomPsdCubicTraceFloor {target : Matrix (Fin 6) (Fin 6) ℝ}
    (hpsd : target.PosSemidef) (hdet : target.det = 0) :
    0 ≤ 20 * (target ^ 3).trace - 9 * target.trace * (target ^ 2).trace
      + target.trace ^ 3 := by
  have hnn : ∀ index, 0 ≤ hpsd.1.eigenvalues index := fun index => hpsd.eigenvalues_nonneg index
  have hone : target.trace = hpsd.1.eigenvalues 0 + hpsd.1.eigenvalues 1 + hpsd.1.eigenvalues 2
      + hpsd.1.eigenvalues 3 + hpsd.1.eigenvalues 4 + hpsd.1.eigenvalues 5 := by
    simpa [Fin.sum_univ_six] using hpsd.1.trace_eq_sum_eigenvalues
  have hprod : hpsd.1.eigenvalues 0 * hpsd.1.eigenvalues 1 * hpsd.1.eigenvalues 2
      * hpsd.1.eigenvalues 3 * hpsd.1.eigenvalues 4 * hpsd.1.eigenvalues 5 = 0 := by
    have hstep := hpsd.1.det_eq_prod_eigenvalues
    rw [hdet] at hstep
    simpa [Fin.prod_univ_six] using hstep.symm
  have hzero : hpsd.1.eigenvalues 0 = 0 ∨ hpsd.1.eigenvalues 1 = 0 ∨ hpsd.1.eigenvalues 2 = 0
      ∨ hpsd.1.eigenvalues 3 = 0 ∨ hpsd.1.eigenvalues 4 = 0 ∨ hpsd.1.eigenvalues 5 = 0 := by
    simpa only [mul_eq_zero, or_assoc] using hprod
  rw [atomRealTracePow hpsd.1 3, atomRealTracePow hpsd.1 2, hone,
    Fin.sum_univ_six, Fin.sum_univ_six]
  exact atomSixHomogeneous_nonneg (hnn 0) (hnn 1) (hnn 2) (hnn 3) (hnn 4) (hnn 5) hzero

open Matrix in
/-- **THE TRACE FLOOR AT TRACE TWENTY.**  The normalised form the heat matrix
consumes.  It is the homogeneous floor divided by twenty. -/
theorem atomPsdTraceFloor {target : Matrix (Fin 6) (Fin 6) ℝ} (hpsd : target.PosSemidef)
    (htrace : target.trace = 20) (hdet : target.det = 0) :
    0 ≤ (target ^ 3).trace - 9 * (target ^ 2).trace + 400 := by
  have hstep := atomPsdCubicTraceFloor hpsd hdet
  rw [htrace] at hstep
  linarith

/-! ## Layer 4 — the heat matrix of a balanced frame -/

variable {atom : Fin 6 → (Fin 3 → ℝ)}

/-- The frame has BALANCED LEVERAGES when every slot carries the leverage one
half.  The icosahedral frame is balanced, and so is `Gtz.dropWitnessAtom`.  The
exact real extremal of the spectral value is NOT balanced: its leverages are five
fourteenths and nine fourteenths. -/
def AtomBalanced (atom : Fin 6 → (Fin 3 → ℝ)) : Prop :=
  ∀ slot : Fin 6, atomGram atom slot slot = 1 / 2

/-- **THE HEAT MATRIX.**  At balanced leverages this is twenty times the Gram
matrix of the six traceless blocks `a y a y ^ T - I / 6`, so it is positive
semidefinite, its trace is `20`, and the frame law sends the all-ones vector to
zero.  Its six eigenvalues are `5 * (lambda + 1)` for the five non-Perron
eigenvalues of the doubly stochastic heat, together with one forced zero. -/
noncomputable def atomHeatMatrix (atom : Fin 6 → (Fin 3 → ℝ)) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun rowSlot colSlot => 20 * atomGram atom rowSlot colSlot ^ 2 - 5 / 3

/-- The nine coordinates of the traceless block `a y a y ^ T - I / 6` of each
slot.  The heat matrix is twenty times the Gram matrix of its columns. -/
noncomputable def atomShiftMatrix (atom : Fin 6 → (Fin 3 → ℝ)) : Matrix (Fin 3 × Fin 3) (Fin 6) ℝ :=
  Matrix.of fun coord slot =>
    atom slot coord.1 * atom slot coord.2 - (if coord.1 = coord.2 then (1 : ℝ) / 6 else 0)

/-- **THE HEAT MATRIX IS A GRAM MATRIX.**  The reading
`20 * (a y . a z) ^ 2 - 5 / 3` is twenty times the Frobenius product of the two
traceless blocks, and the identity spends the balance once in each slot. -/
theorem atomHeatMatrix_eq_gram (hbal : AtomBalanced atom) :
    atomHeatMatrix atom = (20 : ℝ) • ((Matrix.transpose (atomShiftMatrix atom)) * atomShiftMatrix atom) := by
  ext rowSlot colSlot
  have hrow := hbal rowSlot
  have hcol := hbal colSlot
  simp only [atomGram, dotProduct, Fin.sum_univ_three] at hrow hcol
  simp only [atomHeatMatrix, atomShiftMatrix, Matrix.of_apply, Matrix.smul_apply,
    Matrix.transpose_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three,
    atomGram, dotProduct, smul_eq_mul]
  norm_num [Fin.ext_iff]
  linear_combination ((10:ℝ)/3) * hrow + ((10:ℝ)/3) * hcol

/-- **THE HEAT MATRIX IS POSITIVE SEMIDEFINITE.**  This is where the traceless
shift pays: the unshifted table `(a y . a z) ^ 2` is also a Gram matrix, but the
shift by `-5/3` is what puts the all-ones vector in the kernel. -/
theorem atomHeatMatrix_posSemidef (hbal : AtomBalanced atom) :
    (atomHeatMatrix atom).PosSemidef := by
  rw [atomHeatMatrix_eq_gram hbal]
  refine Matrix.PosSemidef.smul ?_ (by norm_num)
  simpa using Matrix.posSemidef_conjTranspose_mul_self (atomShiftMatrix atom)


/-- The SECOND HEAT TOTAL: the total of the squared heats over the fifteen
pairs.  It is half the trace of the square of the doubly stochastic heat. -/
noncomputable def atomHeatTwo (atom : Fin 6 → (Fin 3 → ℝ)) : ℝ :=
  atomPairFamilySum fun rowSlot colSlot => (4 * atomGram atom rowSlot colSlot ^ 2) ^ 2

/-- The THIRD HEAT TOTAL: the total of the triangle products of the heats over
the twenty triples.  It is one sixth of the trace of the cube of the doubly
stochastic heat. -/
noncomputable def atomHeatThree (atom : Fin 6 → (Fin 3 → ℝ)) : ℝ :=
  atomTripleFamilySum fun slotOne slotTwo slotThree =>
    (4 * atomGram atom slotOne slotTwo ^ 2) * (4 * atomGram atom slotTwo slotThree ^ 2)
      * (4 * atomGram atom slotOne slotThree ^ 2)

/-- **THE OFF-DIAGONAL ROW LAW.**  At balanced leverages the squared Gram
readings of one slot against the five other slots total one quarter.  This is
idempotence read one row at a time, with the diagonal removed. -/
theorem atomOffRowSquare
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : AtomBalanced atom) (rowSlot : Fin 6) :
    (∑ colSlot, atomGram atom rowSlot colSlot ^ 2) - atomGram atom rowSlot rowSlot ^ 2
      = 1 / 4 := by
  rw [atomGram_row_energy hframe rowSlot, hbal rowSlot]
  norm_num

/-- **THE ERASE LAW.**  At balanced leverages the two-step Gram path between two
slots, with the two ends erased, is zero.

This is the identity that kills the cross term of the level-three energy.  In
general the erased path reads `(a y . a z) * (1 - s y - s z)`, and the balance
sends the second factor to zero.  It is the same law that
`Gtz.atomGram_cycle_erase` carries in its squared form. -/
theorem atomEraseLaw
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : AtomBalanced atom) (rowSlot colSlot : Fin 6) :
    (∑ midSlot, atomGram atom rowSlot midSlot * atomGram atom midSlot colSlot)
      - atomGram atom rowSlot rowSlot * atomGram atom rowSlot colSlot
      - atomGram atom rowSlot colSlot * atomGram atom colSlot colSlot = 0 := by
  have hcell : ∀ midSlot : Fin 6,
      atomGram atom rowSlot midSlot * atomGram atom midSlot colSlot
        = (atom midSlot ⬝ᵥ atom rowSlot) * (atom midSlot ⬝ᵥ atom colSlot) := by
    intro midSlot
    simp only [atomGram]
    rw [dotProduct_comm (atom rowSlot) (atom midSlot)]
  rw [Finset.sum_congr rfl fun midSlot _ => hcell midSlot,
    hframe (atom rowSlot) (atom colSlot), hbal rowSlot, hbal colSlot]
  simp only [atomGram]
  ring

/-- **THE SECOND TRACE OF THE HEAT MATRIX.**  Six copies of the off-diagonal row
law close it. -/
theorem atomHeatMatrix_tracePowTwo
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : AtomBalanced atom) :
    (atomHeatMatrix atom ^ 2).trace = 50 * atomHeatTwo atom + 50 := by
  have qrow0 := atomOffRowSquare hframe hbal 0
  have qrow1 := atomOffRowSquare hframe hbal 1
  have qrow2 := atomOffRowSquare hframe hbal 2
  have qrow3 := atomOffRowSquare hframe hbal 3
  have qrow4 := atomOffRowSquare hframe hbal 4
  have qrow5 := atomOffRowSquare hframe hbal 5
  simp only [Fin.sum_univ_six] at qrow0 qrow1 qrow2 qrow3 qrow4 qrow5
  simp only [atomGram_comm atom 1 0,
    atomGram_comm atom 2 0,
    atomGram_comm atom 3 0,
    atomGram_comm atom 4 0,
    atomGram_comm atom 5 0,
    atomGram_comm atom 2 1,
    atomGram_comm atom 3 1,
    atomGram_comm atom 4 1,
    atomGram_comm atom 5 1,
    atomGram_comm atom 3 2,
    atomGram_comm atom 4 2,
    atomGram_comm atom 5 2,
    atomGram_comm atom 4 3,
    atomGram_comm atom 5 3,
    atomGram_comm atom 5 4] at qrow0 qrow1 qrow2 qrow3 qrow4 qrow5
  rw [pow_two]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_six,
    atomHeatMatrix, atomHeatTwo, atomPairFamilySum]
  simp only [atomGram_comm atom 1 0,
    atomGram_comm atom 2 0,
    atomGram_comm atom 3 0,
    atomGram_comm atom 4 0,
    atomGram_comm atom 5 0,
    atomGram_comm atom 2 1,
    atomGram_comm atom 3 1,
    atomGram_comm atom 4 1,
    atomGram_comm atom 5 1,
    atomGram_comm atom 3 2,
    atomGram_comm atom 4 2,
    atomGram_comm atom 5 2,
    atomGram_comm atom 4 3,
    atomGram_comm atom 5 3,
    atomGram_comm atom 5 4]
  have hbdiag : ∀ slot : Fin 6, atomGram atom slot slot = 1 / 2 := hbal
  simp only [hbdiag]
  linear_combination (-200 / 3 : ℝ) * qrow0
    + (-200 / 3 : ℝ) * qrow1
    + (-200 / 3 : ℝ) * qrow2
    + (-200 / 3 : ℝ) * qrow3
    + (-200 / 3 : ℝ) * qrow4
    + (-200 / 3 : ℝ) * qrow5

/-- **THE THIRD TRACE OF THE HEAT MATRIX.**  The same six row laws close it,
with a cofactor that is quadratic and not constant, because the cross terms of
the cube carry the square of a row total. -/
theorem atomHeatMatrix_tracePowThree
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : AtomBalanced atom) :
    (atomHeatMatrix atom ^ 3).trace
      = 750 * atomHeatThree atom + 750 * atomHeatTwo atom - 250 := by
  have qrow0 := atomOffRowSquare hframe hbal 0
  have qrow1 := atomOffRowSquare hframe hbal 1
  have qrow2 := atomOffRowSquare hframe hbal 2
  have qrow3 := atomOffRowSquare hframe hbal 3
  have qrow4 := atomOffRowSquare hframe hbal 4
  have qrow5 := atomOffRowSquare hframe hbal 5
  simp only [Fin.sum_univ_six] at qrow0 qrow1 qrow2 qrow3 qrow4 qrow5
  simp only [atomGram_comm atom 1 0,
    atomGram_comm atom 2 0,
    atomGram_comm atom 3 0,
    atomGram_comm atom 4 0,
    atomGram_comm atom 5 0,
    atomGram_comm atom 2 1,
    atomGram_comm atom 3 1,
    atomGram_comm atom 4 1,
    atomGram_comm atom 5 1,
    atomGram_comm atom 3 2,
    atomGram_comm atom 4 2,
    atomGram_comm atom 5 2,
    atomGram_comm atom 4 3,
    atomGram_comm atom 5 3,
    atomGram_comm atom 5 4] at qrow0 qrow1 qrow2 qrow3 qrow4 qrow5
  rw [pow_succ, pow_two]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_six,
    atomHeatMatrix, atomHeatTwo, atomHeatThree, atomPairFamilySum, atomTripleFamilySum]
  simp only [atomGram_comm atom 1 0,
    atomGram_comm atom 2 0,
    atomGram_comm atom 3 0,
    atomGram_comm atom 4 0,
    atomGram_comm atom 5 0,
    atomGram_comm atom 2 1,
    atomGram_comm atom 3 1,
    atomGram_comm atom 4 1,
    atomGram_comm atom 5 1,
    atomGram_comm atom 3 2,
    atomGram_comm atom 4 2,
    atomGram_comm atom 5 2,
    atomGram_comm atom 4 3,
    atomGram_comm atom 5 3,
    atomGram_comm atom 5 4]
  have hbdiag : ∀ slot : Fin 6, atomGram atom slot slot = 1 / 2 := hbal
  simp only [hbdiag]
  linear_combination (-2000 : ℝ) * (1 / 4 + (atomGram atom 0 1 ^ 2 + atomGram atom 0 2 ^ 2 + atomGram atom 0 3 ^ 2 + atomGram atom 0 4 ^ 2 + atomGram atom 0 5 ^ 2)) * qrow0
    + (-2000 : ℝ) * (1 / 4 + (atomGram atom 0 1 ^ 2 + atomGram atom 1 2 ^ 2 + atomGram atom 1 3 ^ 2 + atomGram atom 1 4 ^ 2 + atomGram atom 1 5 ^ 2)) * qrow1
    + (-2000 : ℝ) * (1 / 4 + (atomGram atom 0 2 ^ 2 + atomGram atom 1 2 ^ 2 + atomGram atom 2 3 ^ 2 + atomGram atom 2 4 ^ 2 + atomGram atom 2 5 ^ 2)) * qrow2
    + (-2000 : ℝ) * (1 / 4 + (atomGram atom 0 3 ^ 2 + atomGram atom 1 3 ^ 2 + atomGram atom 2 3 ^ 2 + atomGram atom 3 4 ^ 2 + atomGram atom 3 5 ^ 2)) * qrow3
    + (-2000 : ℝ) * (1 / 4 + (atomGram atom 0 4 ^ 2 + atomGram atom 1 4 ^ 2 + atomGram atom 2 4 ^ 2 + atomGram atom 3 4 ^ 2 + atomGram atom 4 5 ^ 2)) * qrow4
    + (-2000 : ℝ) * (1 / 4 + (atomGram atom 0 5 ^ 2 + atomGram atom 1 5 ^ 2 + atomGram atom 2 5 ^ 2 + atomGram atom 3 5 ^ 2 + atomGram atom 4 5 ^ 2)) * qrow5

/-- **THE ENERGY GAP IN HEAT COORDINATES.**  The whole frame content of the
tenth is this identity.

The proof reads each triple determinant as `8 p = 1 - sigma + 16 c`, squares the
twenty of them, and finds three pieces.  The square of the cycle product gives
the third heat total.  The square of `1 - sigma` gives the second heat total and
the row totals.  The CROSS TERM `sum c * (1 - sigma)` is exactly a combination of
the fifteen erase laws with the cofactor `g / 3 - 4 * g ^ 3`, so it is zero.  The
level-two energy needs the row totals only. -/
theorem atomEnergyGap_heat
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : AtomBalanced atom) :
    480 * atomPluckerEnergyThree atom - 48 * atomPluckerEnergyTwo atom
      = 12 * atomHeatTwo atom + 30 * atomHeatThree atom - 12 := by
  have qrow0 := atomOffRowSquare hframe hbal 0
  have qrow1 := atomOffRowSquare hframe hbal 1
  have qrow2 := atomOffRowSquare hframe hbal 2
  have qrow3 := atomOffRowSquare hframe hbal 3
  have qrow4 := atomOffRowSquare hframe hbal 4
  have qrow5 := atomOffRowSquare hframe hbal 5
  have eras01 := atomEraseLaw hframe hbal 0 1
  have eras02 := atomEraseLaw hframe hbal 0 2
  have eras03 := atomEraseLaw hframe hbal 0 3
  have eras04 := atomEraseLaw hframe hbal 0 4
  have eras05 := atomEraseLaw hframe hbal 0 5
  have eras12 := atomEraseLaw hframe hbal 1 2
  have eras13 := atomEraseLaw hframe hbal 1 3
  have eras14 := atomEraseLaw hframe hbal 1 4
  have eras15 := atomEraseLaw hframe hbal 1 5
  have eras23 := atomEraseLaw hframe hbal 2 3
  have eras24 := atomEraseLaw hframe hbal 2 4
  have eras25 := atomEraseLaw hframe hbal 2 5
  have eras34 := atomEraseLaw hframe hbal 3 4
  have eras35 := atomEraseLaw hframe hbal 3 5
  have eras45 := atomEraseLaw hframe hbal 4 5
  simp only [Fin.sum_univ_six] at qrow0 qrow1 qrow2 qrow3 qrow4 qrow5 eras01 eras02 eras03 eras04 eras05 eras12 eras13 eras14 eras15 eras23 eras24 eras25 eras34 eras35 eras45
  simp only [atomGram_comm atom 1 0,
    atomGram_comm atom 2 0,
    atomGram_comm atom 3 0,
    atomGram_comm atom 4 0,
    atomGram_comm atom 5 0,
    atomGram_comm atom 2 1,
    atomGram_comm atom 3 1,
    atomGram_comm atom 4 1,
    atomGram_comm atom 5 1,
    atomGram_comm atom 3 2,
    atomGram_comm atom 4 2,
    atomGram_comm atom 5 2,
    atomGram_comm atom 4 3,
    atomGram_comm atom 5 3,
    atomGram_comm atom 5 4] at qrow0 qrow1 qrow2 qrow3 qrow4 qrow5 eras01 eras02 eras03 eras04 eras05 eras12 eras13 eras14 eras15 eras23 eras24 eras25 eras34 eras35 eras45
  simp only [atomPluckerEnergyThree, atomPluckerEnergyTwo, atomTripleFamilySum,
    atomPairFamilySum, atomBlockDet, atomBlockPairMinor, atomHeatTwo, atomHeatThree]
  have hbdiag : ∀ slot : Fin 6, atomGram atom slot slot = 1 / 2 := hbal
  simp only [hbdiag]
  linear_combination (120 * (atomGram atom 0 1 ^ 2 + atomGram atom 0 2 ^ 2 + atomGram atom 0 3 ^ 2 + atomGram atom 0 4 ^ 2 + atomGram atom 0 5 ^ 2) - 78) * qrow0
    + (120 * (atomGram atom 0 1 ^ 2 + atomGram atom 1 2 ^ 2 + atomGram atom 1 3 ^ 2 + atomGram atom 1 4 ^ 2 + atomGram atom 1 5 ^ 2) - 78) * qrow1
    + (120 * (atomGram atom 0 2 ^ 2 + atomGram atom 1 2 ^ 2 + atomGram atom 2 3 ^ 2 + atomGram atom 2 4 ^ 2 + atomGram atom 2 5 ^ 2) - 78) * qrow2
    + (120 * (atomGram atom 0 3 ^ 2 + atomGram atom 1 3 ^ 2 + atomGram atom 2 3 ^ 2 + atomGram atom 3 4 ^ 2 + atomGram atom 3 5 ^ 2) - 78) * qrow3
    + (120 * (atomGram atom 0 4 ^ 2 + atomGram atom 1 4 ^ 2 + atomGram atom 2 4 ^ 2 + atomGram atom 3 4 ^ 2 + atomGram atom 4 5 ^ 2) - 78) * qrow4
    + (120 * (atomGram atom 0 5 ^ 2 + atomGram atom 1 5 ^ 2 + atomGram atom 2 5 ^ 2 + atomGram atom 3 5 ^ 2 + atomGram atom 4 5 ^ 2) - 78) * qrow5
    + (80 * atomGram atom 0 1 - 960 * atomGram atom 0 1 ^ 3) * eras01
    + (80 * atomGram atom 0 2 - 960 * atomGram atom 0 2 ^ 3) * eras02
    + (80 * atomGram atom 0 3 - 960 * atomGram atom 0 3 ^ 3) * eras03
    + (80 * atomGram atom 0 4 - 960 * atomGram atom 0 4 ^ 3) * eras04
    + (80 * atomGram atom 0 5 - 960 * atomGram atom 0 5 ^ 3) * eras05
    + (80 * atomGram atom 1 2 - 960 * atomGram atom 1 2 ^ 3) * eras12
    + (80 * atomGram atom 1 3 - 960 * atomGram atom 1 3 ^ 3) * eras13
    + (80 * atomGram atom 1 4 - 960 * atomGram atom 1 4 ^ 3) * eras14
    + (80 * atomGram atom 1 5 - 960 * atomGram atom 1 5 ^ 3) * eras15
    + (80 * atomGram atom 2 3 - 960 * atomGram atom 2 3 ^ 3) * eras23
    + (80 * atomGram atom 2 4 - 960 * atomGram atom 2 4 ^ 3) * eras24
    + (80 * atomGram atom 2 5 - 960 * atomGram atom 2 5 ^ 3) * eras25
    + (80 * atomGram atom 3 4 - 960 * atomGram atom 3 4 ^ 3) * eras34
    + (80 * atomGram atom 3 5 - 960 * atomGram atom 3 5 ^ 3) * eras35
    + (80 * atomGram atom 4 5 - 960 * atomGram atom 4 5 ^ 3) * eras45


/-- The trace of the heat matrix is `20`. -/
theorem atomHeatMatrix_trace (hbal : AtomBalanced atom) :
    (atomHeatMatrix atom).trace = 20 := by
  have hbdiag : ∀ slot : Fin 6, atomGram atom slot slot = 1 / 2 := hbal
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, Fin.sum_univ_six, atomHeatMatrix,
    hbdiag]
  norm_num

open Matrix in
/-- **THE ALL-ONES VECTOR IS IN THE KERNEL.**  The row total of the heat matrix
is `20 * (1/2) - 6 * (5/3) = 0`.  This is the step that removes the Perron
eigenvalue and leaves exactly five free eigenvalues. -/
theorem atomHeatMatrix_mulVec_ones
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : AtomBalanced atom) :
    (atomHeatMatrix atom) *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  funext rowSlot
  have hrow := atomGram_row_energy hframe rowSlot
  rw [hbal rowSlot] at hrow
  simp only [Fin.sum_univ_six] at hrow
  simp only [Matrix.mulVec, dotProduct, atomHeatMatrix, Matrix.of_apply, mul_one,
    Pi.zero_apply, Fin.sum_univ_six]
  linarith

open Matrix in
/-- The determinant of the heat matrix is zero. -/
theorem atomHeatMatrix_det
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : AtomBalanced atom) : (atomHeatMatrix atom).det = 0 := by
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun _ => (1 : ℝ), ?_, ?_⟩
  · intro hcontra
    have hzero := congrFun hcontra 0
    norm_num at hzero
  · exact atomHeatMatrix_mulVec_ones hframe hbal

/-- **THE TENTH AT BALANCED LEVERAGES.**  Every real rank-three Parseval frame
of six atoms whose six leverages are all one half obeys `E2 ≤ 10 * E3`.

The chain is: the heat matrix is positive semidefinite with trace `20` and
determinant `0`, so `Gtz.atomPsdTraceFloor` gives
`tr (M ^ 3) - 9 * tr (M ^ 2) + 400 ≥ 0`, and
`Gtz.atomEnergyGap_heat` says that quantity is `1200 * (10 * E3 - E2)`.

The bound is SHARP here: the icosahedral frame is balanced and attains it. -/
theorem atomPluckerTenth_of_balanced
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : AtomBalanced atom) :
    atomPluckerEnergyTwo atom ≤ 10 * atomPluckerEnergyThree atom := by
  have hfloor := atomPsdTraceFloor (atomHeatMatrix_posSemidef hbal)
    (atomHeatMatrix_trace hbal) (atomHeatMatrix_det hframe hbal)
  rw [atomHeatMatrix_tracePowThree hframe hbal, atomHeatMatrix_tracePowTwo hframe hbal] at hfloor
  have hgap := atomEnergyGap_heat hframe hbal
  linarith


/-! ## Layer 6 — the tenth, the supply, and the residue -/

/-- **THE BLEND FLOOR AT ONE TENTH.**  A balanced frame carries a triple whose
block never shortens a probe below one tenth. -/
theorem atomBlendFloor_tenth_of_balanced
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : AtomBalanced atom) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ AtomBlendFloor atom slotOne slotTwo slotThree (1 / 10) := by
  obtain ⟨slotOne, slotTwo, slotThree, hone, htwo, hthree, hdet, hsecond⟩ :=
    exists_atomEnergyTriple hframe (atomPluckerTenth_of_balanced hframe hbal)
  refine ⟨slotOne, slotTwo, slotThree, hone, htwo, hthree, ?_⟩
  intro weightOne weightTwo weightThree
  have hstep := atomSupplyTriple_blend_floor_le atom hdet hsecond
    weightOne weightTwo weightThree
  rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 10)]
  nlinarith [hstep]

/-- **THE CARRIER AT ONE TENTH FOR A BALANCED FRAME.**  The concrete form the
cell consumes: every scale that stays at or below one tenth is carried by a
three-slot subset. -/
theorem exists_atomCarrier_tenth_of_balanced (atom : Fin 6 → (Fin 3 → ℝ))
    (scale : Fin 6 → ℝ)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : AtomBalanced atom) (hlight : ∀ slot, scale slot ≤ 1 / 10) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  obtain ⟨slotOne, slotTwo, slotThree, hone, htwo, hthree, hfloor⟩ :=
    atomBlendFloor_tenth_of_balanced hframe hbal
  exact exists_atomCarrier_of_blendFloor atom scale hone htwo hthree hfloor hlight

/-- **THE RESIDUE.**  What the balanced reduction leaves: the tenth for frames
whose leverages are NOT all one half.

Adversarial descent over the whole Grassmannian of three-dimensional subspaces of
the six-slot space puts the minimum of `10 * E3 - E2` at a BALANCED point, the
icosahedral frame, where the minimum is zero.  The exact real extremal of the
spectral value, whose leverages are five fourteenths and nine fourteenths, reads
`E2 / E3 = 8.9215`, which clears the ten with room.  So this residue is believed
to be empty, but nothing here proves it.

The reduction cannot be repaired by a change of variable.  At general leverages
the natural heat is `(a y . a z) ^ 2 / sqrt (s y * s z)`, whose Perron vector is
`sqrt s` and not the all-ones vector, and the twenty triple determinants pick up
the weights `s y * s z * s v`, which no trace of a power can read. -/
def AtomPluckerTenthUnbalanced : Prop :=
  ∀ atom : Fin 6 → (Fin 3 → ℝ),
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ¬ AtomBalanced atom →
    atomPluckerEnergyTwo atom ≤ 10 * atomPluckerEnergyThree atom

/-- **THE RESIDUE IS ALL THAT REMAINS.**  The unbalanced residue closes
`Gtz.AtomPluckerTenth` outright. -/
theorem atomPluckerTenth_of_unbalanced (hresidue : AtomPluckerTenthUnbalanced) :
    AtomPluckerTenth := by
  intro atom hframe
  by_cases hbal : AtomBalanced atom
  · exact atomPluckerTenth_of_balanced hframe hbal
  · exact hresidue atom hframe hbal

/-- **THE RESIDUE SPENDS AT ONE TENTH.**  The unbalanced residue gives the
spectral supply at one tenth, which is twenty percent past the landed record
`Gtz.atomSpectralSupply_twelfth`. -/
theorem atomSpectralSupply_tenth_of_unbalanced (hresidue : AtomPluckerTenthUnbalanced) :
    AtomSpectralSupply (1 / 10) :=
  atomSpectralSupply_tenth_of_pluckerTenth (atomPluckerTenth_of_unbalanced hresidue)

/-! ## Layer 7 — the balanced class is not empty -/

/-- **THE DROP WITNESS IS BALANCED.**  The six half-sums of two of the three axes
carry the leverage one half in every slot, so `Gtz.AtomBalanced` is not vacuous
and neither is `Gtz.atomPluckerTenth_of_balanced`. -/
theorem atomBalanced_dropWitness : AtomBalanced dropWitnessAtom := by
  intro slot
  fin_cases slot <;>
    norm_num [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- **THE TENTH HOLDS AT THE DROP WITNESS.**  The standing red-team datum of the
campaign clears the bound.  Its energies are `E2 = 39 / 64` and `E3 = 1 / 16`, so
`E2 / E3 = 39 / 4 = 9.75`, which is below ten but not by much. -/
theorem atomPluckerTenth_dropWitness :
    atomPluckerEnergyTwo dropWitnessAtom ≤ 10 * atomPluckerEnergyThree dropWitnessAtom :=
  atomPluckerTenth_of_balanced dropWitnessAtom_isTightFrame atomBalanced_dropWitness

end Gtz
