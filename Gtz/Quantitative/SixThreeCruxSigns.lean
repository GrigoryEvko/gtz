/-
# X0 — coherence forcing at the `(6,3)` crux — and the realness law of a real Gram

Two layers, both feeding the sign-side rungs of the `(6,3)` exclusion.

## Layer one: the parity-free domination gate, and what it forces at a crux

`Gtz.dominates_of_coherent_of_excessGap_nonneg` reads the sign bit through
`Gtz.tripleParity`.  Its hypothesis is stronger than it needs to be: the trace leg
of `Gtz.dominates_triple_iff_discriminantSystem` already follows from the SIGN-BLIND
gap alone (`Gtz.discriminantTrace_nonneg_of_excessGap_nonneg`), so the honest gate is

  all-heavy  ∧  `0 ≤ excessGap`  ∧  `0 ≤ discriminantTie`  ⟹  `Dominates`,

with the coherent cell recovered by `discriminantTie = excessGap + 2 |product|` at
parity `+1`.  Against `Gtz.SixThreeCrux.hasNoDominatingTriple` this contraposes to a
SQUEEZE that is strictly sharper than the disjunction X0 was asked for: at a crux,

  `0 ≤ excessGap`  ⟹  `discriminantTie < 0`,

and unwinding the bridge turns that single inequality into three simultaneous facts —
the triple is INCOHERENT, all three of its pairings are NONZERO, and its gap is capped
by twice the magnitude of the pairing product.  The three corollaries the campaign
named separately (coherent ⟹ negative gap; a vanishing pairing ⟹ negative gap; the
quantitative cap) are all readings of that one statement.

THE ZERO-PAIRING BRANCH IS NOT A DISCLAIMER.  When any pairing vanishes the oriented
term of `Gtz.discriminantTie_eq_excessGap_add_parity` is zero outright, so the tie leg
COLLAPSES ONTO the sign-blind gap and the parity loses its vote.  That yields a genuine
new certificate cell — `Gtz.dominates_of_excessGap_nonneg_of_exists_atomPairing_eq_zero`,
which needs no parity hypothesis at all — and at a crux it forces `excessGap < 0` with
no escape through incoherence.

## Layer two: the realness law

`Gtz.atomBracket` is the scalar triple product of three atoms; the Gram determinant of
the triple is its SQUARE.  Expanded in the tree's own scalars that is

  `atomBracket² = L_a L_b L_c − L_a p_bc² − L_b p_ac² − L_c p_ab² + 2 p_ab p_ac p_bc`,

and shifting the Gram by the identity gives the characteristic-polynomial bridge

  `atomBracket² = discriminantTie + Σ pairMinor + Σ heavyExcess + 1`.

What is REAL about it is the last summand: over `ℝ` the oriented product is
`tripleParity` times the magnitude, so the determinant takes ONE OF EXACTLY TWO values
given the squared data, whereas over `ℂ` the Bargmann phase makes `2 Re(p_ab p_bc p_ca)`
range over the whole interval between them.  Squaring kills the bit and returns the
campaign's E2, `4 (p_ab p_ac p_bc)² = (det Gram − sign-blind part)²`; the degenerate
specialisation at `atomBracket = 0` is the coplanar law, and coplanar triples never
dominate (`Gtz.not_dominates_of_atomBracket_eq_zero`).

Because a square is nonnegative the bridge is also a free INEQUALITY at every triple of
every real design, and at adverse parity it caps the pairing product by sign-blind data.
HONESTY: that cap is tight EXACTLY on the coplanar locus and nowhere else — at the
tetrahedron it reads `2 ≤ 18` and at the icosahedron `54/(5√5) ≤ 54/5`.  It is a true
constraint with slack, not a finished lever.

## Calibration

At the icosahedron every distinct triple has `excessGap = −14/5 < 0`, so X0's
disjunction is satisfied by its GAP leg at all twenty triples: X0 alone constrains the
icosahedral two-graph NOT AT ALL, and the sign-side rungs must bring magnitudes.  At the
regular tetrahedron the gap is `2 ≥ 0` and the tie is `0 ≥ 0`, so the parity-free gate
fires and the triple dominates — which is exactly why the crux hypothesis in the squeeze
is load-bearing rather than decorative.

## What is NOT closed here

Nothing about the SIZE of `|p_ab p_ac p_bc|` at a crux beyond the cap above, nothing
about how many triples can be incoherent, and no transport to the Naimark dual.  The
squeeze is a per-triple statement; turning it into a global contradiction is the job of
the census and collision rungs.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.SixThreeCrux
import Gtz.Quantitative.SwitchingTwoGraph
import Gtz.Design.DominationGates
import Gtz.Design.PrimitiveTightClassification

namespace Gtz

variable {m : ℕ}

/-! ## 1. The sign-blind gap under permutation

`Gtz.discriminantTie` carries the full `S₃` invariance of a determinant
(`Gtz.discriminantTie_swap`, `Gtz.discriminantTie_swapPair`, `Gtz.discriminantTie_rotate`).
Its sign-blind half had none, although every sign-blind certificate reads it and every
census below permutes triples freely.  The transposition and the three-cycle generate
`S₃`; each is `Gtz.atomPairing_comm` followed by `ring`. -/

/-- Exchanging the first two atoms fixes the sign-blind gap. -/
theorem excessGap_swap (design : WeightedDesign m 3) (first second third : Fin m) :
    excessGap design first second third = excessGap design second first third := by
  simp only [excessGap, atomPairing_comm design second first]
  ring

/-- The three-cycle fixes the sign-blind gap. -/
theorem excessGap_rotate (design : WeightedDesign m 3) (first second third : Fin m) :
    excessGap design first second third = excessGap design third first second := by
  simp only [excessGap, atomPairing_comm design third first,
    atomPairing_comm design third second]
  ring

/-- Exchanging the last two atoms fixes the sign-blind gap; with `Gtz.excessGap_swap`
this is full symmetry, matching `Gtz.discriminantTie_swapPair`. -/
theorem excessGap_swapPair (design : WeightedDesign m 3) (first second third : Fin m) :
    excessGap design first second third = excessGap design first third second := by
  simp only [excessGap, atomPairing_comm design third second]
  ring

/-! ## 2. The parity-free domination gate

The trace leg of the discriminant system is free once the sign-blind gap is
nonnegative.  Stated at the level of a single EDGE it says more than the shipped
`Gtz.discriminantTrace_nonneg_of_excessGap_nonneg`, which sums two of these: a
nonnegative gap makes every pair minor of the triple nonnegative, so every edge of the
triple is compatible in the sense of `Gtz.IsCompatiblePair`. -/

/-- A nonnegative sign-blind gap forces the pair minor of the two atoms it names to be
nonnegative.  Cancel the third excess: `u_c · pairMinor(a,b) = excessGap + u_b p_ac² +
u_a p_bc²`, and every summand on the right is nonnegative. -/
theorem pairMinor_nonneg_of_excessGap_nonneg (design : WeightedDesign m 3)
    {first second third : Fin m} (hfirstPos : 0 < heavyExcess design first)
    (hsecondPos : 0 < heavyExcess design second) (hthirdPos : 0 < heavyExcess design third)
    (hgap : 0 ≤ excessGap design first second third) :
    0 ≤ pairMinor design first second := by
  have hfirstSquared : 0 ≤ heavyExcess design first * atomPairing design second third ^ 2 :=
    mul_nonneg hfirstPos.le (sq_nonneg _)
  have hsecondSquared : 0 ≤ heavyExcess design second * atomPairing design first third ^ 2 :=
    mul_nonneg hsecondPos.le (sq_nonneg _)
  rw [excessGap] at hgap
  refine le_of_mul_le_mul_left ?_ hthirdPos
  simp only [pairMinor, mul_zero]
  nlinarith [hgap, hfirstSquared, hsecondSquared]

/-- **THE PARITY-FREE GATE.**  An all-heavy design whose triple has a nonnegative
sign-blind gap AND a nonnegative tie leg has that triple dominating.  This is
`Gtz.dominates_of_coherent_of_excessGap_nonneg` with the parity hypothesis replaced by
what the parity was only ever used to supply, so the coherent cell is the special case
`tripleParity = 1` and the vanishing-pairing cell below is a second, disjoint one. -/
theorem dominates_of_excessGap_nonneg_of_discriminantTie_nonneg {design : WeightedDesign m 3}
    (hheavy : AllHeavy design) {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hgap : 0 ≤ excessGap design first second third)
    (htie : 0 ≤ discriminantTie design first second third) :
    Dominates design {first, second, third} :=
  (dominates_triple_iff_discriminantSystem design hfirstSecond hfirstThird hsecondThird
      (hheavy first)).mpr
    ⟨discriminantTrace_nonneg_of_excessGap_nonneg design (allHeavy_heavyExcess_pos hheavy first)
        (allHeavy_heavyExcess_pos hheavy second) (allHeavy_heavyExcess_pos hheavy third) hgap,
      htie⟩

/-! ## 3. The vanishing-pairing branch

A single zero pairing annihilates the oriented product, so the tie leg collapses onto
the sign-blind gap and the parity bit stops mattering.  This is the honest content of
the branch X0 was asked to treat: not an exception to be excused, but a cell where the
sign-blind data DECIDES. -/

/-- A vanishing oriented product collapses the tie leg onto the sign-blind gap. -/
theorem discriminantTie_eq_excessGap_of_atomPairingProduct_eq_zero
    (design : WeightedDesign m 3) {first second third : Fin m}
    (hproduct : atomPairing design first second * atomPairing design first third
      * atomPairing design second third = 0) :
    discriminantTie design first second third = excessGap design first second third := by
  rw [discriminantTie_eq_excessGap_add_tripleProduct, hproduct]
  ring

/-- One vanishing edge suffices. -/
theorem discriminantTie_eq_excessGap_of_exists_atomPairing_eq_zero
    (design : WeightedDesign m 3) {first second third : Fin m}
    (hzero : atomPairing design first second = 0 ∨ atomPairing design first third = 0
      ∨ atomPairing design second third = 0) :
    discriminantTie design first second third = excessGap design first second third := by
  refine discriminantTie_eq_excessGap_of_atomPairingProduct_eq_zero design ?_
  rcases hzero with hzero | hzero | hzero <;> rw [hzero] <;> ring

/-- **A CERTIFICATE CELL WITH NO SIGN BIT IN IT.**  An all-heavy triple carrying one
orthogonal pair and a nonnegative sign-blind gap dominates outright.  Unlike
`Gtz.dominates_of_coherent_of_excessGap_nonneg` this reads no parity, and unlike
`Gtz.dominates_of_orthogonalTriple_of_one_le` it asks for ONE vanishing pairing rather
than three. -/
theorem dominates_of_excessGap_nonneg_of_exists_atomPairing_eq_zero
    {design : WeightedDesign m 3} (hheavy : AllHeavy design) {first second third : Fin m}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hzero : atomPairing design first second = 0 ∨ atomPairing design first third = 0
      ∨ atomPairing design second third = 0)
    (hgap : 0 ≤ excessGap design first second third) :
    Dominates design {first, second, third} :=
  dominates_of_excessGap_nonneg_of_discriminantTie_nonneg hheavy hfirstSecond hfirstThird
    hsecondThird hgap
    (by rw [discriminantTie_eq_excessGap_of_exists_atomPairing_eq_zero design hzero]; exact hgap)

/-! ## 4. The realness law

The Gram determinant of three real vectors is the square of their bracket.  Every
identity below is that one fact, read in a different set of coordinates. -/

/-- **CAUCHY–BINET AT RANK THREE.**  The squared bracket IS the Gram determinant,
expanded in lengths and pairings. -/
theorem tripleBracket_sq (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec midVec rightVec ^ 2
      = leverageOf leftVec * leverageOf midVec * leverageOf rightVec
        - leverageOf leftVec * (midVec ⬝ᵥ rightVec) ^ 2
        - leverageOf midVec * (leftVec ⬝ᵥ rightVec) ^ 2
        - leverageOf rightVec * (leftVec ⬝ᵥ midVec) ^ 2
        + 2 * ((leftVec ⬝ᵥ midVec) * (leftVec ⬝ᵥ rightVec) * (midVec ⬝ᵥ rightVec)) := by
  simp only [tripleBracket_eq, leverageOf, dotProduct, Fin.sum_univ_three]
  ring

/-- **THE REALNESS LAW, UNSHIFTED.**  In the leverages and pairings of a triple of
atoms: the Gram determinant is the sign-blind cubic plus twice the ORIENTED product.
Over `ℂ` the same expansion carries `2 Re(p_ab p_bc p_ca)` in the last slot, and that is
the entire difference between the fields at the level of one triple. -/
theorem atomBracket_sq (design : WeightedDesign m 3) (first second third : Fin m) :
    atomBracket design first second third ^ 2
      = leverageOf (design.atom first) * leverageOf (design.atom second)
            * leverageOf (design.atom third)
        - leverageOf (design.atom first) * atomPairing design second third ^ 2
        - leverageOf (design.atom second) * atomPairing design first third ^ 2
        - leverageOf (design.atom third) * atomPairing design first second ^ 2
        + 2 * (atomPairing design first second * atomPairing design first third
            * atomPairing design second third) := by
  simp only [atomBracket, atomPairing]
  exact tripleBracket_sq _ _ _

/-- The oriented product solved out of the realness law: twice the triple product is the
Gram determinant minus its sign-blind part. -/
theorem two_mul_atomPairingProduct_eq_atomBracket_sq_sub (design : WeightedDesign m 3)
    (first second third : Fin m) :
    2 * (atomPairing design first second * atomPairing design first third
        * atomPairing design second third)
      = atomBracket design first second third ^ 2
        - (leverageOf (design.atom first) * leverageOf (design.atom second)
              * leverageOf (design.atom third)
            - leverageOf (design.atom first) * atomPairing design second third ^ 2
            - leverageOf (design.atom second) * atomPairing design first third ^ 2
            - leverageOf (design.atom third) * atomPairing design first second ^ 2) := by
  rw [atomBracket_sq]
  ring

/-- **E2 AS THE CAMPAIGN STATES IT.**  The squared form: four times the squared triple
product equals the squared discrepancy between the Gram determinant and its sign-blind
cubic.  Squaring discards the orientation, which is exactly the information the complex
witnesses keep free. -/
theorem four_mul_atomPairingProduct_sq_eq (design : WeightedDesign m 3)
    (first second third : Fin m) :
    4 * (atomPairing design first second * atomPairing design first third
        * atomPairing design second third) ^ 2
      = (atomBracket design first second third ^ 2
        - (leverageOf (design.atom first) * leverageOf (design.atom second)
              * leverageOf (design.atom third)
            - leverageOf (design.atom first) * atomPairing design second third ^ 2
            - leverageOf (design.atom second) * atomPairing design first third ^ 2
            - leverageOf (design.atom third) * atomPairing design first second ^ 2)) ^ 2 := by
  rw [← two_mul_atomPairingProduct_eq_atomBracket_sq_sub]
  ring

/-- **THE DEGENERATE LAW.**  On a coplanar triple the bracket vanishes, so the sign-blind
cubic and twice the triple product agree up to sign.  Coplanar triples are precisely the
ones `Gtz.not_dominates_of_atomBracket_eq_zero` prunes, so this identity lives exactly on
the non-dominating locus — it constrains a crux everywhere, since a crux has no
dominating triple at all. -/
theorem four_mul_atomPairingProduct_sq_eq_of_atomBracket_eq_zero (design : WeightedDesign m 3)
    {first second third : Fin m} (hbracket : atomBracket design first second third = 0) :
    4 * (atomPairing design first second * atomPairing design first third
        * atomPairing design second third) ^ 2
      = (leverageOf (design.atom first) * leverageOf (design.atom second)
              * leverageOf (design.atom third)
            - leverageOf (design.atom first) * atomPairing design second third ^ 2
            - leverageOf (design.atom second) * atomPairing design first third ^ 2
            - leverageOf (design.atom third) * atomPairing design first second ^ 2) ^ 2 := by
  rw [four_mul_atomPairingProduct_sq_eq, hbracket]
  ring

/-- **THE CHARACTERISTIC-POLYNOMIAL BRIDGE.**  Shifting the Gram by the identity turns
the realness law into a statement about the six scalars the discriminant system already
uses: `det(A + 1) = det A + Σ (2×2 principal minors of A) + tr A + 1` at `A = Gram − 1`,
whose three summands are exactly the tie leg, the three pair minors and the three heavy
excesses. -/
theorem atomBracket_sq_eq_discriminantTie_add (design : WeightedDesign m 3)
    (first second third : Fin m) :
    atomBracket design first second third ^ 2
      = discriminantTie design first second third
        + (pairMinor design first second + pairMinor design first third
            + pairMinor design second third)
        + (heavyExcess design first + heavyExcess design second + heavyExcess design third)
        + 1 := by
  simp only [atomBracket, tripleBracket_eq, discriminantTie, pairMinor, heavyExcess,
    leverageOf, atomPairing, dotProduct, Fin.sum_univ_three]
  ring

/-- **THE SQUARE-FREE PARITY READING.**  Feeding
`Gtz.discriminantTie_eq_excessGap_add_parity` into the bridge puts every sign-blind
quantity on one side and the single bit on the other: given the squared data, a REAL
Gram determinant takes one of exactly TWO values, `2 |p_ab p_ac p_bc|` apart, and
`Gtz.tripleParity` names which.  Over `ℂ` the Bargmann phase lets it take any value in
between; that gap is the whole of the realness budget at one triple. -/
theorem atomBracket_sq_eq_excessGap_add_parity (design : WeightedDesign m 3)
    (first second third : Fin m) :
    atomBracket design first second third ^ 2
      = excessGap design first second third
        + 2 * tripleParity design first second third
            * |atomPairing design first second * atomPairing design first third
                * atomPairing design second third|
        + (pairMinor design first second + pairMinor design first third
            + pairMinor design second third)
        + (heavyExcess design first + heavyExcess design second + heavyExcess design third)
        + 1 := by
  rw [atomBracket_sq_eq_discriminantTie_add, discriminantTie_eq_excessGap_add_parity]

/-- **THE FREE REALNESS INEQUALITY.**  A square is nonnegative, so the bridge lower-bounds
the tie leg by sign-blind data at EVERY triple of EVERY real design, with no hypotheses
whatsoever.  Equality holds precisely on the coplanar locus. -/
theorem neg_le_discriminantTie (design : WeightedDesign m 3) (first second third : Fin m) :
    -((pairMinor design first second + pairMinor design first third
          + pairMinor design second third)
        + (heavyExcess design first + heavyExcess design second + heavyExcess design third)
        + 1)
      ≤ discriminantTie design first second third := by
  have hsquare : (0:ℝ) ≤ atomBracket design first second third ^ 2 := sq_nonneg _
  rw [atomBracket_sq_eq_discriminantTie_add] at hsquare
  linarith

/-- **THE MAGNITUDE CAP AT ADVERSE PARITY.**  At an INCOHERENT triple the oriented term
subtracts, so nonnegativity of the determinant caps the pairing product by sign-blind
data alone.

HONESTY: the cap is slack away from the coplanar locus, where it is an equality.  At the
regular tetrahedron it reads `2 ≤ 18` and at the icosahedron `54/(5√5) ≈ 4.83 ≤ 54/5 =
10.8`.  It is a true constraint, not a finished lever. -/
theorem two_mul_abs_atomPairingProduct_le_of_incoherent (design : WeightedDesign m 3)
    {first second third : Fin m} (hparity : tripleParity design first second third = -1) :
    2 * |atomPairing design first second * atomPairing design first third
        * atomPairing design second third|
      ≤ excessGap design first second third
        + (pairMinor design first second + pairMinor design first third
            + pairMinor design second third)
        + (heavyExcess design first + heavyExcess design second + heavyExcess design third)
        + 1 := by
  have hsquare : (0:ℝ) ≤ atomBracket design first second third ^ 2 := sq_nonneg _
  rw [atomBracket_sq_eq_excessGap_add_parity, hparity] at hsquare
  linarith

/-- **A VOLUME FLOOR FROM DOMINATION.**  A dominating triple of an all-heavy design has
squared bracket strictly above one: the tie leg and all three pair minors are nonnegative
there, and the three heavy excesses are strictly positive. -/
theorem one_lt_atomBracket_sq_of_dominates {design : WeightedDesign m 3}
    (hheavy : AllHeavy design) {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hdominates : Dominates design {first, second, third}) :
    1 < atomBracket design first second third ^ 2 := by
  obtain ⟨htrace, htie⟩ := (dominates_triple_iff_discriminantSystem design hfirstSecond
    hfirstThird hsecondThird (hheavy first)).mp hdominates
  have hfirstSecondMinor : 0 ≤ pairMinor design first second :=
    pairMinor_nonneg_of_dominates design hfirstSecond hfirstThird hsecondThird (hheavy first)
      hdominates
  have hfirstThirdMinor : 0 ≤ pairMinor design first third := by
    refine pairMinor_nonneg_of_dominates design hfirstThird hfirstSecond hsecondThird.symm
      (hheavy first) ?_
    rwa [show ({first, third, second} : Finset (Fin m)) = {first, second, third} from by
      ext label; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
  have hsecondThirdMinor : 0 ≤ pairMinor design second third := by
    refine pairMinor_nonneg_of_dominates design hsecondThird hfirstSecond.symm hfirstThird.symm
      (hheavy second) ?_
    rwa [show ({second, third, first} : Finset (Fin m)) = {first, second, third} from by
      ext label; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
  have hfirstExcess := allHeavy_heavyExcess_pos hheavy first
  have hsecondExcess := allHeavy_heavyExcess_pos hheavy second
  have hthirdExcess := allHeavy_heavyExcess_pos hheavy third
  rw [atomBracket_sq_eq_discriminantTie_add]
  linarith

/-! ## 5. The squeeze at the crux

Everything above is design-level.  Composed against `Gtz.SixThreeCrux.isAllHeavy` and
`Gtz.SixThreeCrux.hasNoDominatingTriple` it becomes the sign layer X0 was asked for, in
its sharpest form. -/

/-- Three distinct labels span a three-element subset — the shape
`Gtz.SixThreeCrux.hasNoDominatingTriple` consumes. -/
theorem card_triple_eq_three {size : ℕ} {first second third : Fin size}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    ({first, second, third} : Finset (Fin size)).card = 3 := by
  classical
  rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
    Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]

namespace SixThreeCrux

/-- **THE SQUEEZE.**  At a `(6,3)` crux a nonnegative sign-blind gap forces a strictly
negative tie leg.  One contrapositive step from the parity-free gate against
`hasNoDominatingTriple`; every statement below is a reading of this one. -/
theorem discriminantTie_neg_of_excessGap_nonneg (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hgap : 0 ≤ excessGap crux.design first second third) :
    discriminantTie crux.design first second third < 0 :=
  lt_of_not_ge fun htie =>
    crux.hasNoDominatingTriple {first, second, third}
      (card_triple_eq_three hfirstSecond hfirstThird hsecondThird)
      (dominates_of_excessGap_nonneg_of_discriminantTie_nonneg crux.isAllHeavy hfirstSecond
        hfirstThird hsecondThird hgap htie)

/-- **THE SQUEEZE, UNWOUND.**  A crux triple whose sign-blind gap is nonnegative is
INCOHERENT, has all three pairings NONZERO, and has its gap strictly below twice the
magnitude of the pairing product.  The three facts come out together because the bridge
`discriminantTie = excessGap + 2 · parity · magnitude` has only one way to be negative
while the gap is not. -/
theorem isIncoherent_of_excessGap_nonneg (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hgap : 0 ≤ excessGap crux.design first second third) :
    tripleParity crux.design first second third = -1
      ∧ 0 < |atomPairing crux.design first second * atomPairing crux.design first third
          * atomPairing crux.design second third|
      ∧ excessGap crux.design first second third
          < 2 * |atomPairing crux.design first second * atomPairing crux.design first third
              * atomPairing crux.design second third| := by
  have hmagnitude : (0:ℝ) ≤ |atomPairing crux.design first second
      * atomPairing crux.design first third * atomPairing crux.design second third| :=
    abs_nonneg _
  have htie := discriminantTie_neg_of_excessGap_nonneg crux hfirstSecond hfirstThird
    hsecondThird hgap
  rw [discriminantTie_eq_excessGap_add_parity] at htie
  rcases tripleParity_eq_one_or_neg_one crux.design first second third with hparity | hparity
  · exfalso
    rw [hparity] at htie
    linarith
  · rw [hparity] at htie
    exact ⟨hparity, by linarith, by linarith⟩

/-- **X0, THE COHERENCE DICHOTOMY.**  Every distinct triple of a crux is INCOHERENT or
has a strictly negative sign-blind gap.  The campaign's third disjunct — a vanishing
pairing — is not needed: the vanishing-pairing case lands in the SECOND disjunct
outright, by `Gtz.SixThreeCrux.excessGap_neg_of_exists_atomPairing_eq_zero` below. -/
theorem tripleParity_eq_neg_one_or_excessGap_neg (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    tripleParity crux.design first second third = -1
      ∨ excessGap crux.design first second third < 0 := by
  rcases lt_or_ge (excessGap crux.design first second third) 0 with hgap | hgap
  · exact Or.inr hgap
  · exact Or.inl (isIncoherent_of_excessGap_nonneg crux hfirstSecond hfirstThird
      hsecondThird hgap).1

/-- A COHERENT crux triple has a strictly negative sign-blind gap.  This is the reading
the excess-gap census and the two-graph collision consume. -/
theorem excessGap_neg_of_coherent (crux : SixThreeCrux) {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hparity : tripleParity crux.design first second third = 1) :
    excessGap crux.design first second third < 0 := by
  rcases tripleParity_eq_neg_one_or_excessGap_neg crux hfirstSecond hfirstThird
    hsecondThird with hincoherent | hgap
  · rw [hparity] at hincoherent; norm_num at hincoherent
  · exact hgap

/-- The other contrapositive: a nonnegative sign-blind gap makes the triple incoherent. -/
theorem tripleParity_eq_neg_one_of_excessGap_nonneg (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hgap : 0 ≤ excessGap crux.design first second third) :
    tripleParity crux.design first second third = -1 :=
  (isIncoherent_of_excessGap_nonneg crux hfirstSecond hfirstThird hsecondThird hgap).1

/-- **THE QUANTITATIVE FORM.**  At a crux the sign-blind gap never reaches twice the
magnitude of the pairing product — the sign-blind cell
`Gtz.isSignBlindGoodTriple_iff_adverseTie_nonneg` is empty at a crux, uniformly. -/
theorem excessGap_lt_two_mul_abs_atomPairingProduct (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    excessGap crux.design first second third
      < 2 * |atomPairing crux.design first second * atomPairing crux.design first third
          * atomPairing crux.design second third| := by
  rcases lt_or_ge (excessGap crux.design first second third) 0 with hgap | hgap
  · exact lt_of_lt_of_le hgap (by positivity)
  · exact (isIncoherent_of_excessGap_nonneg crux hfirstSecond hfirstThird hsecondThird hgap).2.2

/-- A crux triple with a nonnegative sign-blind gap has all three pairings nonzero. -/
theorem atomPairingProduct_ne_zero_of_excessGap_nonneg (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hgap : 0 ≤ excessGap crux.design first second third) :
    atomPairing crux.design first second * atomPairing crux.design first third
        * atomPairing crux.design second third ≠ 0 := fun hproduct => by
  have hpositive := (isIncoherent_of_excessGap_nonneg crux hfirstSecond hfirstThird
    hsecondThird hgap).2.1
  rw [hproduct, abs_zero] at hpositive
  exact lt_irrefl 0 hpositive

/-- **THE VANISHING-PAIRING BRANCH, WITH CONTENT.**  A crux triple carrying even ONE
orthogonal pair has a strictly negative sign-blind gap, with no escape through
incoherence: the parity has no vote where the oriented product is zero. -/
theorem excessGap_neg_of_exists_atomPairing_eq_zero (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hzero : atomPairing crux.design first second = 0
      ∨ atomPairing crux.design first third = 0
      ∨ atomPairing crux.design second third = 0) :
    excessGap crux.design first second third < 0 := by
  refine lt_of_not_ge fun hgap => ?_
  refine atomPairingProduct_ne_zero_of_excessGap_nonneg crux hfirstSecond hfirstThird
    hsecondThird hgap ?_
  rcases hzero with hzero | hzero | hzero <;> rw [hzero] <;> ring

/-- **K18 AT THE CRUX.**  No triple of a crux is pairwise orthogonal.  Direct from
`Gtz.dominates_of_orthogonalTriple_of_one_le` against `hasNoDominatingTriple`; individual
vanishing pairings survive, and are governed by the branch above. -/
theorem hasNoOrthogonalTriple (crux : SixThreeCrux) (first second third : Fin 6)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    ¬ (atomPairing crux.design first second = 0 ∧ atomPairing crux.design first third = 0
        ∧ atomPairing crux.design second third = 0) := by
  rintro ⟨hfirstSecondZero, hfirstThirdZero, hsecondThirdZero⟩
  exact crux.hasNoDominatingTriple {first, second, third}
    (card_triple_eq_three hfirstSecond hfirstThird hsecondThird)
    (dominates_of_orthogonalTriple_of_one_le crux.design hfirstSecond hfirstThird hsecondThird
      (crux.isAllHeavy first).le (crux.isAllHeavy second).le (crux.isAllHeavy third).le
      hfirstSecondZero hfirstThirdZero hsecondThirdZero)

/-- **THE DISCRIMINANT-SYSTEM DICHOTOMY.**  Every distinct triple of a crux has a
strictly negative trace leg or a strictly negative tie leg.  Note what this is NOT: a
coherent triple need not have a negative TIE, because the oriented term helps there.
X0 delivers `excessGap < 0` in that sector, never `discriminantTie < 0` directly. -/
theorem discriminantTrace_neg_or_discriminantTie_neg (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    discriminantTrace crux.design first second third < 0
      ∨ discriminantTie crux.design first second third < 0 := by
  by_contra hboth
  push Not at hboth
  exact crux.hasNoDominatingTriple {first, second, third}
    (card_triple_eq_three hfirstSecond hfirstThird hsecondThird)
    ((dominates_triple_iff_discriminantSystem crux.design hfirstSecond hfirstThird
      hsecondThird (crux.isAllHeavy first)).mpr ⟨hboth.1, hboth.2⟩)

/-- The tie leg alone, once the trace leg is known nonnegative. -/
theorem discriminantTie_neg_of_discriminantTrace_nonneg (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (htrace : 0 ≤ discriminantTrace crux.design first second third) :
    discriminantTie crux.design first second third < 0 := by
  rcases discriminantTrace_neg_or_discriminantTie_neg crux hfirstSecond hfirstThird
    hsecondThird with htraceNeg | htie
  · linarith
  · exact htie

/-- **THE PER-VERTEX PACKAGING.**  Every coherent triple through a fixed atom of a crux
has a strictly negative sign-blind gap — the form a per-base coherent count intersects
with.  Stated as a universally quantified fact about the base so that a lower bound on
the number of coherent triples through it composes without re-deriving X0. -/
theorem forall_coherent_excessGap_neg_through_atom (crux : SixThreeCrux) (base : Fin 6) :
    ∀ second third : Fin 6, base ≠ second → base ≠ third → second ≠ third →
      tripleParity crux.design base second third = 1 →
      excessGap crux.design base second third < 0 := by
  intro second third hbaseSecond hbaseThird hsecondThird hparity
  have hnegative : excessGap crux.design base second third < 0 :=
    excessGap_neg_of_coherent crux hbaseSecond hbaseThird hsecondThird hparity
  exact hnegative

/-- **THE SIGN-BLIND CELL IS EMPTY AT A CRUX, TRIPLE BY TRIPLE.**  The shipped
`Gtz.not_signBlindGoodTripleCovering_six` says the sign-blind family fails to COVER at six
atoms; a crux says something far stronger about itself — not one of its twenty triples is
sign-blind good.  Unconditional: no gap hypothesis, no parity hypothesis. -/
theorem not_isSignBlindGoodTriple (crux : SixThreeCrux) {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    ¬ IsSignBlindGoodTriple crux.design first second third := by
  rw [IsSignBlindGoodTriple]
  exact not_le.mpr (excessGap_lt_two_mul_abs_atomPairingProduct crux hfirstSecond hfirstThird
    hsecondThird)

/-- **THE EDGE-LEVEL DICHOTOMY.**  The squeeze contraposes to `discriminantTie ≥ 0 ⟹
excessGap < 0`; running the trace leg at all THREE pivots instead gives an independent
consequence, on the edges.  A crux triple with a nonnegative tie leg has all three of its
trace legs strictly negative, and each trace leg is the sum of the two pair minors at its
pivot, so the three pair minors sum to something strictly negative. -/
theorem sum_pairMinor_neg_of_discriminantTie_nonneg (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (htie : 0 ≤ discriminantTie crux.design first second third) :
    pairMinor crux.design first second + pairMinor crux.design first third
        + pairMinor crux.design second third < 0 := by
  have htraceFirst : discriminantTrace crux.design first second third < 0 := by
    rcases discriminantTrace_neg_or_discriminantTie_neg crux hfirstSecond hfirstThird
      hsecondThird with htrace | htieNeg
    · exact htrace
    · linarith
  have htraceSecond : discriminantTrace crux.design second first third < 0 := by
    rcases discriminantTrace_neg_or_discriminantTie_neg crux hfirstSecond.symm hsecondThird
      hfirstThird with htrace | htieNeg
    · exact htrace
    · rw [← discriminantTie_swap] at htieNeg; linarith
  have htraceThird : discriminantTrace crux.design third first second < 0 := by
    rcases discriminantTrace_neg_or_discriminantTie_neg crux hfirstThird.symm hsecondThird.symm
      hfirstSecond with htrace | htieNeg
    · exact htrace
    · rw [← discriminantTie_rotate] at htieNeg; linarith
  rw [discriminantTrace_eq_pairMinor_add] at htraceFirst htraceSecond htraceThird
  have hcommSecondFirst := pairMinor_comm crux.design second first
  have hcommThirdFirst := pairMinor_comm crux.design third first
  have hcommThirdSecond := pairMinor_comm crux.design third second
  linarith

/-- **AN INCOMPATIBLE EDGE.**  A crux triple whose tie leg is nonnegative carries a pair
whose minor is strictly negative — an edge no triangle can use, in the sense of
`Gtz.IsCompatiblePair`.  Together with the squeeze this reads: at a crux, every triple has
`discriminantTie < 0`, OR has `excessGap < 0` and an incompatible edge. -/
theorem exists_pairMinor_neg_of_discriminantTie_nonneg (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (htie : 0 ≤ discriminantTie crux.design first second third) :
    pairMinor crux.design first second < 0 ∨ pairMinor crux.design first third < 0
      ∨ pairMinor crux.design second third < 0 := by
  by_contra hall
  push Not at hall
  have hsum := sum_pairMinor_neg_of_discriminantTie_nonneg crux hfirstSecond hfirstThird
    hsecondThird htie
  linarith [hall.1, hall.2.1, hall.2.2]

/-- **THE PIVOT-LEVEL STRICT SEPARATION.**  Feeding the squeeze into the Schur identity
`Gtz.pairMinor_product_eq_tieSchur` turns a strictly negative tie leg into a STRICT
inequality between the product of the two pivot minors and the squared off-diagonal Schur
term.  Since a nonnegative gap also makes both pivot minors nonnegative
(`Gtz.pairMinor_nonneg_of_excessGap_nonneg`), the right-hand side is strictly positive:
`u_a p_bc` and `p_ab p_ac` never coincide at such a triple. -/
theorem pairMinor_mul_pairMinor_lt_sq_of_excessGap_nonneg (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hgap : 0 ≤ excessGap crux.design first second third) :
    pairMinor crux.design first second * pairMinor crux.design first third
      < (heavyExcess crux.design first * atomPairing crux.design second third
          - atomPairing crux.design first second * atomPairing crux.design first third) ^ 2 := by
  have htie := discriminantTie_neg_of_excessGap_nonneg crux hfirstSecond hfirstThird
    hsecondThird hgap
  have hexcess := allHeavy_heavyExcess_pos crux.isAllHeavy first
  have hschur := pairMinor_product_eq_tieSchur crux.design first second third
  nlinarith [hschur, mul_pos hexcess (neg_pos.mpr htie)]

end SixThreeCrux

/-! ## 6. Calibration

Two shipped designs pin the two ends of the squeeze. -/

/-- **X0 SEES NOTHING AT THE ICOSAHEDRON.**  Every distinct icosahedral triple has
sign-blind gap `−14/5 < 0`, so the SECOND disjunct of X0 holds at all twenty triples
regardless of parity.  Yet at the icosahedron the parity DECIDES domination outright
(`Gtz.icosaDesign_dominates_iff_tripleParity`), on data whose sign-blind part is the same
number at every triple.  So coherence forcing alone leaves the icosahedral sign pattern
entirely untouched, and whatever finishes the sign layer must read magnitudes. -/
theorem icosaDesign_excessGap_neg {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    excessGap icosaDesign first second third < 0 := by
  rw [icosaDesign_excessGap hfirstSecond hfirstThird hsecondThird]
  norm_num

/-- **THE GATE FIRES AT THE `(4,3)` TIE, WHICH IS WHY THE CRUX HYPOTHESIS IS
LOAD-BEARING.**  The regular tetrahedron has gap `2 ≥ 0` and tie `0 ≥ 0`, so the
parity-free gate returns domination — even though the triple is INCOHERENT, which the
coherent cell `Gtz.dominates_of_coherent_of_excessGap_nonneg` cannot see.  The squeeze's
conclusion `discriminantTie < 0` fails here by exactly zero, so it is sharp: no
strengthening to `≤` is available. -/
theorem dominates_tetraDesign_of_parityFreeGate :
    Dominates tetraDesign {0, 1, 2} :=
  dominates_of_excessGap_nonneg_of_discriminantTie_nonneg tetraDesign_allHeavy
    (by decide) (by decide) (by decide)
    (by rw [tetraDesign_excessGap]; norm_num)
    (by rw [tetraDesign_discriminantTie_via_parity])

/-- **THE SLACK IN THE REALNESS CAP, MEASURED AT THE TETRAHEDRON.**  The docstring's
honesty qualifier, as a theorem: `Gtz.two_mul_abs_atomPairingProduct_le_of_incoherent`
reads `2 ≤ 18` there.  Exact rational arithmetic, no `Real.sqrt`. -/
theorem tetraDesign_realnessCap :
    2 * |atomPairing tetraDesign 0 1 * atomPairing tetraDesign 0 2
        * atomPairing tetraDesign 1 2| = 2
      ∧ excessGap tetraDesign 0 1 2
          + (pairMinor tetraDesign 0 1 + pairMinor tetraDesign 0 2 + pairMinor tetraDesign 1 2)
          + (heavyExcess tetraDesign 0 + heavyExcess tetraDesign 1 + heavyExcess tetraDesign 2)
          + 1 = 18 := by
  constructor
  · rw [tetraDesign_atomPairing_zeroOne, tetraDesign_atomPairing_zeroTwo,
      tetraDesign_atomPairing_oneTwo]
    norm_num
  · simp only [tetraDesign_excessGap, pairMinor, tetraDesign_heavyExcess,
      tetraDesign_atomPairing_zeroOne, tetraDesign_atomPairing_zeroTwo,
      tetraDesign_atomPairing_oneTwo]
    norm_num

/-- **THE SLACK, MEASURED AT THE ICOSAHEDRON.**  The cap's right-hand side is exactly
`54/5` at every distinct triple and the left-hand side is STRICTLY below it.  Proved by
comparing squares, `2916/125` against `2916/25`, so no `Real.sqrt` appears. -/
theorem icosaDesign_realnessCap {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    excessGap icosaDesign first second third
        + (pairMinor icosaDesign first second + pairMinor icosaDesign first third
            + pairMinor icosaDesign second third)
        + (heavyExcess icosaDesign first + heavyExcess icosaDesign second
            + heavyExcess icosaDesign third)
        + 1 = 54 / 5
      ∧ 2 * |atomPairing icosaDesign first second * atomPairing icosaDesign first third
          * atomPairing icosaDesign second third| < 54 / 5 := by
  have habsSq := icosaDesign_abs_atomPairingProduct_sq hfirstSecond hfirstThird hsecondThird
  have habsNonneg : (0:ℝ) ≤ |atomPairing icosaDesign first second
      * atomPairing icosaDesign first third * atomPairing icosaDesign second third| :=
    abs_nonneg _
  refine ⟨?_, by nlinarith [habsSq, habsNonneg]⟩
  simp only [icosaDesign_excessGap hfirstSecond hfirstThird hsecondThird, pairMinor,
    icosaDesign_heavyExcess, icosaDesign_atomPairing_sq_of_ne hfirstSecond,
    icosaDesign_atomPairing_sq_of_ne hfirstThird,
    icosaDesign_atomPairing_sq_of_ne hsecondThird]
  norm_num

end Gtz
