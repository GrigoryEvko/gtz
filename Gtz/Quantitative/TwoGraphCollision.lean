import Gtz.Quantitative.CoherentCountFloor
import Gtz.Quantitative.ChartDuality
import Gtz.Quantitative.SixThreeCrux
import Gtz.Quantitative.SixThreeCruxSigns
import Gtz.Design.FrameConservation

/-!
# The two-graph collision at `(6,3)`

The sign layer of a rank-three design on six atoms is a TWO-GRAPH: the
`Gtz.tripleParity` of each of the twenty triples, a value in `{1, -1}`, subject to
the four-set cocycle law `Gtz.tripleParity_fourSet_product`.  This file turns that
layer into one decidable finite object, proves EVERY constraint the sign layer is
known to impose on a design, applies all of them, and records the exact residue.

## The representation, and why it needs no gauge

`Gtz.tripleParity_eq_product_through_base` is hypothesis-free: the parity of ANY
triple is the product of the three parities joining it to ANY base atom.  So the
whole two-graph is determined by its LINK at atom `0` -- the ten parities
`tripleParity design 0 x y` with `x` and `y` in `{1,...,5}` -- and all `2 ^ 10`
links occur.  A two-graph is therefore a natural number below `1024`, the cocycle
law holds DEFINITIONALLY instead of as a hypothesis, and no switching gauge has to
be fixed at the design level.  `Gtz.sectorIncoherent` decodes a link back to the
parity of an arbitrary triple as the exclusive-or of its three link bits, and
`Gtz.sectorIncoherent_linkWordOf` proves the decode agrees with `Gtz.tripleParity`
at EVERY triple of every design -- no distinctness, no nonvanishing, degenerate
triples included.

## The three levers, all proved here

* **L1, the incoherent cap.**  `Gtz.card_le_three_of_forall_incoherent_through_base`
  caps a base-avoiding family that is pairwise INCOHERENT through the base at three
  members, so no four atoms avoiding a base are pairwise incoherent through it.
  Thirty tests, one per (base, quadruple).  Landed upstream; discharged here by
  `Gtz.incoherentQuadruple_eq_false`.
* **L2, the coherent cap, NEW.**  `Gtz.card_le_three_of_forall_coherent_through_base`
  is the same cap with the parities reversed, obtained by running L1 on the
  anti-parity partner `Gtz.exists_antiParityPartner_sixThree` -- the chart dual,
  whose two-graph is the complement by `Gtz.tripleParity_chartDual`.  Worth 76 of
  the 1024 patterns and three of the sixteen isomorphism classes.
* **L3, the saturated matching, NEW, and the deepest of the three.**  It rests on
  an identity that was not in the tree: `Gtz.sum_erasePair_weight_mul_atomPairing`,
  THE EDGE LAW, the Parseval identity `Gtz.sum_weight_mul_atomPairing_mul_atomPairing`
  read at an OFF-DIAGONAL entry with the two diagonal terms split off,

      sum over the other atoms of  t_e * p_ce * p_ed  =  p_cd * (1 - s_c - s_d).

  Multiplying by `p_cd` makes every summand `t_e * (p_cd * p_ce * p_de)`, whose
  sign is the parity of the triple `{c, d, e}` by
  `Gtz.pos_atomPairingProduct_of_tripleParity_eq_one`.  So an edge all four of
  whose triples are coherent has `s_c + s_d < 1`
  (`Gtz.atomShare_add_atomShare_lt_one_of_coherentEdge`) and one all four of whose
  triples are incoherent has `s_c + s_d > 1`
  (`Gtz.one_lt_atomShare_add_atomShare_of_incoherentEdge`).  Three such edges
  forming a PERFECT MATCHING then contradict `Gtz.sum_atomShare_eq_rank`, which
  pins the six shares to sum to exactly three.  Worth a further 30 patterns and
  two more classes.

## What comes out, in one line

`Gtz.card_residualSectors`: **842 of the 1024 two-graphs survive**, in eight of the
sixteen isomorphism classes, and `Gtz.SixThreeCrux.linkWord_mem_residualSectors`
puts every crux with nonvanishing pairings inside that set.
`Gtz.card_leverOneSectors` records 948 for L1 alone and
`Gtz.card_leverOneAndTwoSectors` 872 for L1 and L2, so the two new levers are worth
76 and 30 patterns respectively.

## HONESTY, IN THE TERMS THE CAMPAIGN NEEDS

THE SECTOR TABLE DOES NOT EMPTY.  842 of 1024 survive, and this is now the WHOLE
known combinatorial lane rather than a stage of it: the three levers are every
sign-layer constraint anyone has derived at this cell, and all three are proved
above.  Three separate reasons, each measured rather than guessed, say no further
sign-layer argument can finish, and none of them is repaired by more combinatorics.

1. EVERY SURVIVING CLASS IS REALISED BY A DESIGN.  Each of the eight surviving
   isomorphism classes carries an explicit six-tuple of integer directions with
   exact positive rational Parseval coefficients, so NO CORRECT SIGN-ONLY ARGUMENT
   CUTS ANY OF THEM -- the levers are not merely the best available, they are
   exactly the obstruction, and the residue is sharp.  The hardest class is pinned
   by `Gtz.icosahedralLink_mem_residualSectors`: the icosahedral two-graph is link
   `220`, and it survives.
2. NO SURVIVING CLASS HAS A MAGNITUDE MARGIN.  Minimising the domination margin
   inside each surviving class reaches infimum exactly one -- margins measured down
   to `5.05e-11` at eighty digits -- so there is no inequality `margin >= eps` to
   mechanize class by class.  A positive margin appears only under a lower bound on
   `|chartObjective|`, which nothing in this repository proves.
3. THE CENSUS CANNOT HELP.  `Gtz.censusTripleSets_icosaDesign_eq_empty` makes the
   sign-blind census floor zero, and a census threshold below thirteen of twenty
   buys nothing the levers have not already bought.

THE WHOLE TABLE LIVES IN THE NONVANISHING BRANCH.  All three levers need pairings
that do not vanish, and a crux is NOT known to satisfy that; the honest entry point
is `Gtz.SixThreeCrux.two_le_card_coherentPairsThroughBase_or_exists_orthogonalPair`.
TWO DISJOINT ORTHOGONAL PAIRS BLOCK ALL THIRTY L1 TESTS AT ONCE and revert the
table to all 1024 patterns; a single orthogonality already blocks twenty of the
thirty.  Nothing in the tree forbids two disjoint zeros --
`Gtz.SixThreeCrux.hasNoOrthogonalTriple` forbids only all THREE pairings of one
triple vanishing -- so the target theorem carries the hypothesis explicitly.

THE COMPLEMENT FILTER IS NOT APPLIED, DELIBERATELY.  "A pattern survives only if
its complement does" would need the complement two-graph to be carried by another
CRUX.  It is carried by the chart dual, and
`Gtz.exists_naimarkDual_dominates_and_chartDual_not_dominates` shows that is not
the Naimark dual, so the filter is unlicensed.  What IS licensed is that the
complement of a design-realizable two-graph is design-realizable, a consistency
check on the enumeration rather than a constraint on a crux; the surviving set is
closed under the complement involution, and it passes.

L1 AND L2 ARE REAL-ONLY.  Both descend from `Gtz.card_le_succ_of_isPairwiseObtuse_on`,
whose cap is `3 + 1 = 4` over the reals but `2 * 3 + 1 = 7` over the complex numbers
by `Gtz.card_le_two_mul_add_one_of_isPairwiseObtuseComplex`.  At six atoms a cap of
seven exceeds the atom count, so BOTH LEVERS ARE VACUOUS OVER `C`, and the
reduction from 1024 to 872 is real-only content -- realness consumed ACROSS triples
rather than inside one, which is what the per-triple lanes could not do.  L3 by
contrast is field-blind: the edge law is Parseval, which holds over `C` too.

ONE PIECE OF THE VANISHING BRANCH IS REACHED, in section 8.  At an ORTHOGONAL edge
the edge law's right-hand side is identically zero, so the four star products must
cancel and the edge CANNOT BE SIGN-SATURATED AT ALL, in either parity
(`Gtz.not_forall_coherent_of_orthogonalEdge` and
`Gtz.not_forall_incoherent_of_orthogonalEdge`) -- strictly stronger than the share
inequalities the nonvanishing case gives.  So L3's obstruction survives an
orthogonality ON a matching edge; L1 and L2 do not, and closing them there is the
open piece.
-/

namespace Gtz

open scoped Classical

variable {sizeIndex : ℕ}

/-! ## 1. Packing ten bits into a natural number

The link is carried as a `Nat` so that the sweep in section 2 sees only
kernel-accelerated bit operations.  These four lemmas are the whole interface: a
word is built as `head + 2 * rest`, its bit zero is the head, and its bit
`index + 1` is bit `index` of the rest. -/

theorem testBit_toNat_zero (headBit : Bool) : headBit.toNat.testBit 0 = headBit := by
  cases headBit <;> rfl

theorem testBit_toNat_succ (headBit : Bool) (bitIndex : Nat) :
    headBit.toNat.testBit (bitIndex + 1) = false := by
  cases headBit
  · simp
  · simp [Nat.testBit_succ]

theorem testBit_bitCons_zero (headBit : Bool) (restWord : Nat) :
    (headBit.toNat + 2 * restWord).testBit 0 = headBit := by
  rw [Nat.testBit_zero]
  cases headBit <;> simp

theorem testBit_bitCons_succ (headBit : Bool) (restWord bitIndex : Nat) :
    (headBit.toNat + 2 * restWord).testBit (bitIndex + 1) = restWord.testBit bitIndex := by
  rw [Nat.testBit_succ]
  congr 1
  cases headBit
  · simp
  · simp only [Bool.toNat_true]
    omega

/-- Ten booleans as one natural number below `1024`, little-endian. -/
def packTenBits (bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9 : Bool) : Nat :=
  bit0.toNat + 2 * (bit1.toNat + 2 * (bit2.toNat + 2 * (bit3.toNat + 2 * (bit4.toNat
    + 2 * (bit5.toNat + 2 * (bit6.toNat + 2 * (bit7.toNat + 2 * (bit8.toNat
    + 2 * bit9.toNat))))))))

theorem packTenBits_lt (bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9 : Bool) :
    packTenBits bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9 < 1024 := by
  have hbound : ∀ flag : Bool, flag.toNat ≤ 1 := by decide
  have h0 := hbound bit0; have h1 := hbound bit1; have h2 := hbound bit2
  have h3 := hbound bit3; have h4 := hbound bit4; have h5 := hbound bit5
  have h6 := hbound bit6; have h7 := hbound bit7; have h8 := hbound bit8
  have h9 := hbound bit9
  unfold packTenBits
  omega

theorem testBit_packTenBits_zero
    (bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9 : Bool) :
    (packTenBits bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9).testBit 0 = bit0 := by
  rw [packTenBits, testBit_bitCons_zero]

theorem testBit_packTenBits_one
    (bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9 : Bool) :
    (packTenBits bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9).testBit 1 = bit1 := by
  rw [packTenBits, testBit_bitCons_succ, testBit_bitCons_zero]

theorem testBit_packTenBits_two
    (bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9 : Bool) :
    (packTenBits bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9).testBit 2 = bit2 := by
  rw [packTenBits, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_zero]

theorem testBit_packTenBits_three
    (bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9 : Bool) :
    (packTenBits bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9).testBit 3 = bit3 := by
  rw [packTenBits, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_zero]

theorem testBit_packTenBits_four
    (bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9 : Bool) :
    (packTenBits bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9).testBit 4 = bit4 := by
  rw [packTenBits, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_zero]

theorem testBit_packTenBits_five
    (bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9 : Bool) :
    (packTenBits bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9).testBit 5 = bit5 := by
  rw [packTenBits, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_zero]

theorem testBit_packTenBits_six
    (bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9 : Bool) :
    (packTenBits bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9).testBit 6 = bit6 := by
  rw [packTenBits, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_zero]

theorem testBit_packTenBits_seven
    (bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9 : Bool) :
    (packTenBits bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9).testBit 7 = bit7 := by
  rw [packTenBits, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_zero]

theorem testBit_packTenBits_eight
    (bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9 : Bool) :
    (packTenBits bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9).testBit 8 = bit8 := by
  rw [packTenBits, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_zero]

theorem testBit_packTenBits_nine
    (bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9 : Bool) :
    (packTenBits bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9).testBit 9 = bit9 := by
  rw [packTenBits, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_toNat_zero]

theorem testBit_packTenBits_ten
    (bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9 : Bool) :
    (packTenBits bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 bit8 bit9).testBit 10 = false := by
  rw [packTenBits, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_bitCons_succ, testBit_toNat_succ]

/-! ## 2. The sector layer

A two-graph on six atoms is a `link : Nat` below `1024`: bit `linkIndexOfPair x y`
records whether the triple `{0, x, y}` is incoherent.  `Gtz.sectorIncoherent`
decodes an arbitrary triple as the exclusive-or of its three link bits, which is
exactly the product law `Gtz.tripleParity_eq_product_through_base` read at base
`0`.  A pair meeting `0`, or a repeated pair, is sent to the junk index `10`, whose
bit is zero for every link below `1024` -- and the corresponding parity really is
`1`, by `Gtz.decide_tripleParity_base_zero_degenerate`, so the junk arm is correct
rather than merely harmless.  Note that `Gtz.sectorIncoherent` is symmetric in its
three atoms, because the exclusive-or ranges over the three unordered pairs. -/

def linkIndexOfValues : Nat → Nat → Nat
  | 1, 2 => 0
  | 1, 3 => 1
  | 1, 4 => 2
  | 1, 5 => 3
  | 2, 1 => 0
  | 2, 3 => 4
  | 2, 4 => 5
  | 2, 5 => 6
  | 3, 1 => 1
  | 3, 2 => 4
  | 3, 4 => 7
  | 3, 5 => 8
  | 4, 1 => 2
  | 4, 2 => 5
  | 4, 3 => 7
  | 4, 5 => 9
  | 5, 1 => 3
  | 5, 2 => 6
  | 5, 3 => 8
  | 5, 4 => 9
  | _, _ => 10

/-- Which of the ten link bits carries the triple `{0, first, second}`. -/
def linkIndexOfPair (atomFirst atomSecond : Fin 6) : Nat :=
  linkIndexOfValues atomFirst.val atomSecond.val

/-- Is the triple `{0, first, second}` incoherent in the two-graph `link`? -/
def linkBitOf (link : Nat) (atomFirst atomSecond : Fin 6) : Bool :=
  link.testBit (linkIndexOfPair atomFirst atomSecond)

/-- Is the triple `{first, second, third}` incoherent in the two-graph `link`? -/
def sectorIncoherent (link : Nat) (first second third : Fin 6) : Bool :=
  xor (xor (linkBitOf link first second) (linkBitOf link first third))
    (linkBitOf link second third)

/-- **L1 as a sector test.**  No four atoms avoiding a base are pairwise INCOHERENT
through it -- thirty tests, one per (base, quadruple). -/
def hasNoIncoherentQuadruple (link : Nat) : Bool :=
    !(sectorIncoherent link 0 1 2
      && sectorIncoherent link 0 1 3
      && sectorIncoherent link 0 1 4
      && sectorIncoherent link 0 2 3
      && sectorIncoherent link 0 2 4
      && sectorIncoherent link 0 3 4)
    &&     !(sectorIncoherent link 0 1 2
      && sectorIncoherent link 0 1 3
      && sectorIncoherent link 0 1 5
      && sectorIncoherent link 0 2 3
      && sectorIncoherent link 0 2 5
      && sectorIncoherent link 0 3 5)
    &&     !(sectorIncoherent link 0 1 2
      && sectorIncoherent link 0 1 4
      && sectorIncoherent link 0 1 5
      && sectorIncoherent link 0 2 4
      && sectorIncoherent link 0 2 5
      && sectorIncoherent link 0 4 5)
    &&     !(sectorIncoherent link 0 1 3
      && sectorIncoherent link 0 1 4
      && sectorIncoherent link 0 1 5
      && sectorIncoherent link 0 3 4
      && sectorIncoherent link 0 3 5
      && sectorIncoherent link 0 4 5)
    &&     !(sectorIncoherent link 0 2 3
      && sectorIncoherent link 0 2 4
      && sectorIncoherent link 0 2 5
      && sectorIncoherent link 0 3 4
      && sectorIncoherent link 0 3 5
      && sectorIncoherent link 0 4 5)
    &&     !(sectorIncoherent link 1 0 2
      && sectorIncoherent link 1 0 3
      && sectorIncoherent link 1 0 4
      && sectorIncoherent link 1 2 3
      && sectorIncoherent link 1 2 4
      && sectorIncoherent link 1 3 4)
    &&     !(sectorIncoherent link 1 0 2
      && sectorIncoherent link 1 0 3
      && sectorIncoherent link 1 0 5
      && sectorIncoherent link 1 2 3
      && sectorIncoherent link 1 2 5
      && sectorIncoherent link 1 3 5)
    &&     !(sectorIncoherent link 1 0 2
      && sectorIncoherent link 1 0 4
      && sectorIncoherent link 1 0 5
      && sectorIncoherent link 1 2 4
      && sectorIncoherent link 1 2 5
      && sectorIncoherent link 1 4 5)
    &&     !(sectorIncoherent link 1 0 3
      && sectorIncoherent link 1 0 4
      && sectorIncoherent link 1 0 5
      && sectorIncoherent link 1 3 4
      && sectorIncoherent link 1 3 5
      && sectorIncoherent link 1 4 5)
    &&     !(sectorIncoherent link 1 2 3
      && sectorIncoherent link 1 2 4
      && sectorIncoherent link 1 2 5
      && sectorIncoherent link 1 3 4
      && sectorIncoherent link 1 3 5
      && sectorIncoherent link 1 4 5)
    &&     !(sectorIncoherent link 2 0 1
      && sectorIncoherent link 2 0 3
      && sectorIncoherent link 2 0 4
      && sectorIncoherent link 2 1 3
      && sectorIncoherent link 2 1 4
      && sectorIncoherent link 2 3 4)
    &&     !(sectorIncoherent link 2 0 1
      && sectorIncoherent link 2 0 3
      && sectorIncoherent link 2 0 5
      && sectorIncoherent link 2 1 3
      && sectorIncoherent link 2 1 5
      && sectorIncoherent link 2 3 5)
    &&     !(sectorIncoherent link 2 0 1
      && sectorIncoherent link 2 0 4
      && sectorIncoherent link 2 0 5
      && sectorIncoherent link 2 1 4
      && sectorIncoherent link 2 1 5
      && sectorIncoherent link 2 4 5)
    &&     !(sectorIncoherent link 2 0 3
      && sectorIncoherent link 2 0 4
      && sectorIncoherent link 2 0 5
      && sectorIncoherent link 2 3 4
      && sectorIncoherent link 2 3 5
      && sectorIncoherent link 2 4 5)
    &&     !(sectorIncoherent link 2 1 3
      && sectorIncoherent link 2 1 4
      && sectorIncoherent link 2 1 5
      && sectorIncoherent link 2 3 4
      && sectorIncoherent link 2 3 5
      && sectorIncoherent link 2 4 5)
    &&     !(sectorIncoherent link 3 0 1
      && sectorIncoherent link 3 0 2
      && sectorIncoherent link 3 0 4
      && sectorIncoherent link 3 1 2
      && sectorIncoherent link 3 1 4
      && sectorIncoherent link 3 2 4)
    &&     !(sectorIncoherent link 3 0 1
      && sectorIncoherent link 3 0 2
      && sectorIncoherent link 3 0 5
      && sectorIncoherent link 3 1 2
      && sectorIncoherent link 3 1 5
      && sectorIncoherent link 3 2 5)
    &&     !(sectorIncoherent link 3 0 1
      && sectorIncoherent link 3 0 4
      && sectorIncoherent link 3 0 5
      && sectorIncoherent link 3 1 4
      && sectorIncoherent link 3 1 5
      && sectorIncoherent link 3 4 5)
    &&     !(sectorIncoherent link 3 0 2
      && sectorIncoherent link 3 0 4
      && sectorIncoherent link 3 0 5
      && sectorIncoherent link 3 2 4
      && sectorIncoherent link 3 2 5
      && sectorIncoherent link 3 4 5)
    &&     !(sectorIncoherent link 3 1 2
      && sectorIncoherent link 3 1 4
      && sectorIncoherent link 3 1 5
      && sectorIncoherent link 3 2 4
      && sectorIncoherent link 3 2 5
      && sectorIncoherent link 3 4 5)
    &&     !(sectorIncoherent link 4 0 1
      && sectorIncoherent link 4 0 2
      && sectorIncoherent link 4 0 3
      && sectorIncoherent link 4 1 2
      && sectorIncoherent link 4 1 3
      && sectorIncoherent link 4 2 3)
    &&     !(sectorIncoherent link 4 0 1
      && sectorIncoherent link 4 0 2
      && sectorIncoherent link 4 0 5
      && sectorIncoherent link 4 1 2
      && sectorIncoherent link 4 1 5
      && sectorIncoherent link 4 2 5)
    &&     !(sectorIncoherent link 4 0 1
      && sectorIncoherent link 4 0 3
      && sectorIncoherent link 4 0 5
      && sectorIncoherent link 4 1 3
      && sectorIncoherent link 4 1 5
      && sectorIncoherent link 4 3 5)
    &&     !(sectorIncoherent link 4 0 2
      && sectorIncoherent link 4 0 3
      && sectorIncoherent link 4 0 5
      && sectorIncoherent link 4 2 3
      && sectorIncoherent link 4 2 5
      && sectorIncoherent link 4 3 5)
    &&     !(sectorIncoherent link 4 1 2
      && sectorIncoherent link 4 1 3
      && sectorIncoherent link 4 1 5
      && sectorIncoherent link 4 2 3
      && sectorIncoherent link 4 2 5
      && sectorIncoherent link 4 3 5)
    &&     !(sectorIncoherent link 5 0 1
      && sectorIncoherent link 5 0 2
      && sectorIncoherent link 5 0 3
      && sectorIncoherent link 5 1 2
      && sectorIncoherent link 5 1 3
      && sectorIncoherent link 5 2 3)
    &&     !(sectorIncoherent link 5 0 1
      && sectorIncoherent link 5 0 2
      && sectorIncoherent link 5 0 4
      && sectorIncoherent link 5 1 2
      && sectorIncoherent link 5 1 4
      && sectorIncoherent link 5 2 4)
    &&     !(sectorIncoherent link 5 0 1
      && sectorIncoherent link 5 0 3
      && sectorIncoherent link 5 0 4
      && sectorIncoherent link 5 1 3
      && sectorIncoherent link 5 1 4
      && sectorIncoherent link 5 3 4)
    &&     !(sectorIncoherent link 5 0 2
      && sectorIncoherent link 5 0 3
      && sectorIncoherent link 5 0 4
      && sectorIncoherent link 5 2 3
      && sectorIncoherent link 5 2 4
      && sectorIncoherent link 5 3 4)
    &&     !(sectorIncoherent link 5 1 2
      && sectorIncoherent link 5 1 3
      && sectorIncoherent link 5 1 4
      && sectorIncoherent link 5 2 3
      && sectorIncoherent link 5 2 4
      && sectorIncoherent link 5 3 4)

/-- **L2 as a sector test.**  No four atoms avoiding a base are pairwise COHERENT
through it. -/
def hasNoCoherentQuadruple (link : Nat) : Bool :=
    !(!(sectorIncoherent link 0 1 2)
      && !(sectorIncoherent link 0 1 3)
      && !(sectorIncoherent link 0 1 4)
      && !(sectorIncoherent link 0 2 3)
      && !(sectorIncoherent link 0 2 4)
      && !(sectorIncoherent link 0 3 4))
    &&     !(!(sectorIncoherent link 0 1 2)
      && !(sectorIncoherent link 0 1 3)
      && !(sectorIncoherent link 0 1 5)
      && !(sectorIncoherent link 0 2 3)
      && !(sectorIncoherent link 0 2 5)
      && !(sectorIncoherent link 0 3 5))
    &&     !(!(sectorIncoherent link 0 1 2)
      && !(sectorIncoherent link 0 1 4)
      && !(sectorIncoherent link 0 1 5)
      && !(sectorIncoherent link 0 2 4)
      && !(sectorIncoherent link 0 2 5)
      && !(sectorIncoherent link 0 4 5))
    &&     !(!(sectorIncoherent link 0 1 3)
      && !(sectorIncoherent link 0 1 4)
      && !(sectorIncoherent link 0 1 5)
      && !(sectorIncoherent link 0 3 4)
      && !(sectorIncoherent link 0 3 5)
      && !(sectorIncoherent link 0 4 5))
    &&     !(!(sectorIncoherent link 0 2 3)
      && !(sectorIncoherent link 0 2 4)
      && !(sectorIncoherent link 0 2 5)
      && !(sectorIncoherent link 0 3 4)
      && !(sectorIncoherent link 0 3 5)
      && !(sectorIncoherent link 0 4 5))
    &&     !(!(sectorIncoherent link 1 0 2)
      && !(sectorIncoherent link 1 0 3)
      && !(sectorIncoherent link 1 0 4)
      && !(sectorIncoherent link 1 2 3)
      && !(sectorIncoherent link 1 2 4)
      && !(sectorIncoherent link 1 3 4))
    &&     !(!(sectorIncoherent link 1 0 2)
      && !(sectorIncoherent link 1 0 3)
      && !(sectorIncoherent link 1 0 5)
      && !(sectorIncoherent link 1 2 3)
      && !(sectorIncoherent link 1 2 5)
      && !(sectorIncoherent link 1 3 5))
    &&     !(!(sectorIncoherent link 1 0 2)
      && !(sectorIncoherent link 1 0 4)
      && !(sectorIncoherent link 1 0 5)
      && !(sectorIncoherent link 1 2 4)
      && !(sectorIncoherent link 1 2 5)
      && !(sectorIncoherent link 1 4 5))
    &&     !(!(sectorIncoherent link 1 0 3)
      && !(sectorIncoherent link 1 0 4)
      && !(sectorIncoherent link 1 0 5)
      && !(sectorIncoherent link 1 3 4)
      && !(sectorIncoherent link 1 3 5)
      && !(sectorIncoherent link 1 4 5))
    &&     !(!(sectorIncoherent link 1 2 3)
      && !(sectorIncoherent link 1 2 4)
      && !(sectorIncoherent link 1 2 5)
      && !(sectorIncoherent link 1 3 4)
      && !(sectorIncoherent link 1 3 5)
      && !(sectorIncoherent link 1 4 5))
    &&     !(!(sectorIncoherent link 2 0 1)
      && !(sectorIncoherent link 2 0 3)
      && !(sectorIncoherent link 2 0 4)
      && !(sectorIncoherent link 2 1 3)
      && !(sectorIncoherent link 2 1 4)
      && !(sectorIncoherent link 2 3 4))
    &&     !(!(sectorIncoherent link 2 0 1)
      && !(sectorIncoherent link 2 0 3)
      && !(sectorIncoherent link 2 0 5)
      && !(sectorIncoherent link 2 1 3)
      && !(sectorIncoherent link 2 1 5)
      && !(sectorIncoherent link 2 3 5))
    &&     !(!(sectorIncoherent link 2 0 1)
      && !(sectorIncoherent link 2 0 4)
      && !(sectorIncoherent link 2 0 5)
      && !(sectorIncoherent link 2 1 4)
      && !(sectorIncoherent link 2 1 5)
      && !(sectorIncoherent link 2 4 5))
    &&     !(!(sectorIncoherent link 2 0 3)
      && !(sectorIncoherent link 2 0 4)
      && !(sectorIncoherent link 2 0 5)
      && !(sectorIncoherent link 2 3 4)
      && !(sectorIncoherent link 2 3 5)
      && !(sectorIncoherent link 2 4 5))
    &&     !(!(sectorIncoherent link 2 1 3)
      && !(sectorIncoherent link 2 1 4)
      && !(sectorIncoherent link 2 1 5)
      && !(sectorIncoherent link 2 3 4)
      && !(sectorIncoherent link 2 3 5)
      && !(sectorIncoherent link 2 4 5))
    &&     !(!(sectorIncoherent link 3 0 1)
      && !(sectorIncoherent link 3 0 2)
      && !(sectorIncoherent link 3 0 4)
      && !(sectorIncoherent link 3 1 2)
      && !(sectorIncoherent link 3 1 4)
      && !(sectorIncoherent link 3 2 4))
    &&     !(!(sectorIncoherent link 3 0 1)
      && !(sectorIncoherent link 3 0 2)
      && !(sectorIncoherent link 3 0 5)
      && !(sectorIncoherent link 3 1 2)
      && !(sectorIncoherent link 3 1 5)
      && !(sectorIncoherent link 3 2 5))
    &&     !(!(sectorIncoherent link 3 0 1)
      && !(sectorIncoherent link 3 0 4)
      && !(sectorIncoherent link 3 0 5)
      && !(sectorIncoherent link 3 1 4)
      && !(sectorIncoherent link 3 1 5)
      && !(sectorIncoherent link 3 4 5))
    &&     !(!(sectorIncoherent link 3 0 2)
      && !(sectorIncoherent link 3 0 4)
      && !(sectorIncoherent link 3 0 5)
      && !(sectorIncoherent link 3 2 4)
      && !(sectorIncoherent link 3 2 5)
      && !(sectorIncoherent link 3 4 5))
    &&     !(!(sectorIncoherent link 3 1 2)
      && !(sectorIncoherent link 3 1 4)
      && !(sectorIncoherent link 3 1 5)
      && !(sectorIncoherent link 3 2 4)
      && !(sectorIncoherent link 3 2 5)
      && !(sectorIncoherent link 3 4 5))
    &&     !(!(sectorIncoherent link 4 0 1)
      && !(sectorIncoherent link 4 0 2)
      && !(sectorIncoherent link 4 0 3)
      && !(sectorIncoherent link 4 1 2)
      && !(sectorIncoherent link 4 1 3)
      && !(sectorIncoherent link 4 2 3))
    &&     !(!(sectorIncoherent link 4 0 1)
      && !(sectorIncoherent link 4 0 2)
      && !(sectorIncoherent link 4 0 5)
      && !(sectorIncoherent link 4 1 2)
      && !(sectorIncoherent link 4 1 5)
      && !(sectorIncoherent link 4 2 5))
    &&     !(!(sectorIncoherent link 4 0 1)
      && !(sectorIncoherent link 4 0 3)
      && !(sectorIncoherent link 4 0 5)
      && !(sectorIncoherent link 4 1 3)
      && !(sectorIncoherent link 4 1 5)
      && !(sectorIncoherent link 4 3 5))
    &&     !(!(sectorIncoherent link 4 0 2)
      && !(sectorIncoherent link 4 0 3)
      && !(sectorIncoherent link 4 0 5)
      && !(sectorIncoherent link 4 2 3)
      && !(sectorIncoherent link 4 2 5)
      && !(sectorIncoherent link 4 3 5))
    &&     !(!(sectorIncoherent link 4 1 2)
      && !(sectorIncoherent link 4 1 3)
      && !(sectorIncoherent link 4 1 5)
      && !(sectorIncoherent link 4 2 3)
      && !(sectorIncoherent link 4 2 5)
      && !(sectorIncoherent link 4 3 5))
    &&     !(!(sectorIncoherent link 5 0 1)
      && !(sectorIncoherent link 5 0 2)
      && !(sectorIncoherent link 5 0 3)
      && !(sectorIncoherent link 5 1 2)
      && !(sectorIncoherent link 5 1 3)
      && !(sectorIncoherent link 5 2 3))
    &&     !(!(sectorIncoherent link 5 0 1)
      && !(sectorIncoherent link 5 0 2)
      && !(sectorIncoherent link 5 0 4)
      && !(sectorIncoherent link 5 1 2)
      && !(sectorIncoherent link 5 1 4)
      && !(sectorIncoherent link 5 2 4))
    &&     !(!(sectorIncoherent link 5 0 1)
      && !(sectorIncoherent link 5 0 3)
      && !(sectorIncoherent link 5 0 4)
      && !(sectorIncoherent link 5 1 3)
      && !(sectorIncoherent link 5 1 4)
      && !(sectorIncoherent link 5 3 4))
    &&     !(!(sectorIncoherent link 5 0 2)
      && !(sectorIncoherent link 5 0 3)
      && !(sectorIncoherent link 5 0 4)
      && !(sectorIncoherent link 5 2 3)
      && !(sectorIncoherent link 5 2 4)
      && !(sectorIncoherent link 5 3 4))
    &&     !(!(sectorIncoherent link 5 1 2)
      && !(sectorIncoherent link 5 1 3)
      && !(sectorIncoherent link 5 1 4)
      && !(sectorIncoherent link 5 2 3)
      && !(sectorIncoherent link 5 2 4)
      && !(sectorIncoherent link 5 3 4))

/-- **L3 as a sector test.**  No perfect matching of the six atoms consists of three
edges all four of whose triples share one parity -- fifteen matchings, each tested
on both signs. -/
def hasNoSaturatedMatching (link : Nat) : Bool :=
    !(!(sectorIncoherent link 0 1 2)
      && !(sectorIncoherent link 0 1 3)
      && !(sectorIncoherent link 0 1 4)
      && !(sectorIncoherent link 0 1 5)
      && !(sectorIncoherent link 2 3 0)
      && !(sectorIncoherent link 2 3 1)
      && !(sectorIncoherent link 2 3 4)
      && !(sectorIncoherent link 2 3 5)
      && !(sectorIncoherent link 4 5 0)
      && !(sectorIncoherent link 4 5 1)
      && !(sectorIncoherent link 4 5 2)
      && !(sectorIncoherent link 4 5 3))
    &&     !(sectorIncoherent link 0 1 2
      && sectorIncoherent link 0 1 3
      && sectorIncoherent link 0 1 4
      && sectorIncoherent link 0 1 5
      && sectorIncoherent link 2 3 0
      && sectorIncoherent link 2 3 1
      && sectorIncoherent link 2 3 4
      && sectorIncoherent link 2 3 5
      && sectorIncoherent link 4 5 0
      && sectorIncoherent link 4 5 1
      && sectorIncoherent link 4 5 2
      && sectorIncoherent link 4 5 3)
    &&     !(!(sectorIncoherent link 0 1 2)
      && !(sectorIncoherent link 0 1 4)
      && !(sectorIncoherent link 0 1 3)
      && !(sectorIncoherent link 0 1 5)
      && !(sectorIncoherent link 2 4 0)
      && !(sectorIncoherent link 2 4 1)
      && !(sectorIncoherent link 2 4 3)
      && !(sectorIncoherent link 2 4 5)
      && !(sectorIncoherent link 3 5 0)
      && !(sectorIncoherent link 3 5 1)
      && !(sectorIncoherent link 3 5 2)
      && !(sectorIncoherent link 3 5 4))
    &&     !(sectorIncoherent link 0 1 2
      && sectorIncoherent link 0 1 4
      && sectorIncoherent link 0 1 3
      && sectorIncoherent link 0 1 5
      && sectorIncoherent link 2 4 0
      && sectorIncoherent link 2 4 1
      && sectorIncoherent link 2 4 3
      && sectorIncoherent link 2 4 5
      && sectorIncoherent link 3 5 0
      && sectorIncoherent link 3 5 1
      && sectorIncoherent link 3 5 2
      && sectorIncoherent link 3 5 4)
    &&     !(!(sectorIncoherent link 0 1 2)
      && !(sectorIncoherent link 0 1 5)
      && !(sectorIncoherent link 0 1 3)
      && !(sectorIncoherent link 0 1 4)
      && !(sectorIncoherent link 2 5 0)
      && !(sectorIncoherent link 2 5 1)
      && !(sectorIncoherent link 2 5 3)
      && !(sectorIncoherent link 2 5 4)
      && !(sectorIncoherent link 3 4 0)
      && !(sectorIncoherent link 3 4 1)
      && !(sectorIncoherent link 3 4 2)
      && !(sectorIncoherent link 3 4 5))
    &&     !(sectorIncoherent link 0 1 2
      && sectorIncoherent link 0 1 5
      && sectorIncoherent link 0 1 3
      && sectorIncoherent link 0 1 4
      && sectorIncoherent link 2 5 0
      && sectorIncoherent link 2 5 1
      && sectorIncoherent link 2 5 3
      && sectorIncoherent link 2 5 4
      && sectorIncoherent link 3 4 0
      && sectorIncoherent link 3 4 1
      && sectorIncoherent link 3 4 2
      && sectorIncoherent link 3 4 5)
    &&     !(!(sectorIncoherent link 0 2 1)
      && !(sectorIncoherent link 0 2 3)
      && !(sectorIncoherent link 0 2 4)
      && !(sectorIncoherent link 0 2 5)
      && !(sectorIncoherent link 1 3 0)
      && !(sectorIncoherent link 1 3 2)
      && !(sectorIncoherent link 1 3 4)
      && !(sectorIncoherent link 1 3 5)
      && !(sectorIncoherent link 4 5 0)
      && !(sectorIncoherent link 4 5 2)
      && !(sectorIncoherent link 4 5 1)
      && !(sectorIncoherent link 4 5 3))
    &&     !(sectorIncoherent link 0 2 1
      && sectorIncoherent link 0 2 3
      && sectorIncoherent link 0 2 4
      && sectorIncoherent link 0 2 5
      && sectorIncoherent link 1 3 0
      && sectorIncoherent link 1 3 2
      && sectorIncoherent link 1 3 4
      && sectorIncoherent link 1 3 5
      && sectorIncoherent link 4 5 0
      && sectorIncoherent link 4 5 2
      && sectorIncoherent link 4 5 1
      && sectorIncoherent link 4 5 3)
    &&     !(!(sectorIncoherent link 0 2 1)
      && !(sectorIncoherent link 0 2 4)
      && !(sectorIncoherent link 0 2 3)
      && !(sectorIncoherent link 0 2 5)
      && !(sectorIncoherent link 1 4 0)
      && !(sectorIncoherent link 1 4 2)
      && !(sectorIncoherent link 1 4 3)
      && !(sectorIncoherent link 1 4 5)
      && !(sectorIncoherent link 3 5 0)
      && !(sectorIncoherent link 3 5 2)
      && !(sectorIncoherent link 3 5 1)
      && !(sectorIncoherent link 3 5 4))
    &&     !(sectorIncoherent link 0 2 1
      && sectorIncoherent link 0 2 4
      && sectorIncoherent link 0 2 3
      && sectorIncoherent link 0 2 5
      && sectorIncoherent link 1 4 0
      && sectorIncoherent link 1 4 2
      && sectorIncoherent link 1 4 3
      && sectorIncoherent link 1 4 5
      && sectorIncoherent link 3 5 0
      && sectorIncoherent link 3 5 2
      && sectorIncoherent link 3 5 1
      && sectorIncoherent link 3 5 4)
    &&     !(!(sectorIncoherent link 0 2 1)
      && !(sectorIncoherent link 0 2 5)
      && !(sectorIncoherent link 0 2 3)
      && !(sectorIncoherent link 0 2 4)
      && !(sectorIncoherent link 1 5 0)
      && !(sectorIncoherent link 1 5 2)
      && !(sectorIncoherent link 1 5 3)
      && !(sectorIncoherent link 1 5 4)
      && !(sectorIncoherent link 3 4 0)
      && !(sectorIncoherent link 3 4 2)
      && !(sectorIncoherent link 3 4 1)
      && !(sectorIncoherent link 3 4 5))
    &&     !(sectorIncoherent link 0 2 1
      && sectorIncoherent link 0 2 5
      && sectorIncoherent link 0 2 3
      && sectorIncoherent link 0 2 4
      && sectorIncoherent link 1 5 0
      && sectorIncoherent link 1 5 2
      && sectorIncoherent link 1 5 3
      && sectorIncoherent link 1 5 4
      && sectorIncoherent link 3 4 0
      && sectorIncoherent link 3 4 2
      && sectorIncoherent link 3 4 1
      && sectorIncoherent link 3 4 5)
    &&     !(!(sectorIncoherent link 0 3 1)
      && !(sectorIncoherent link 0 3 2)
      && !(sectorIncoherent link 0 3 4)
      && !(sectorIncoherent link 0 3 5)
      && !(sectorIncoherent link 1 2 0)
      && !(sectorIncoherent link 1 2 3)
      && !(sectorIncoherent link 1 2 4)
      && !(sectorIncoherent link 1 2 5)
      && !(sectorIncoherent link 4 5 0)
      && !(sectorIncoherent link 4 5 3)
      && !(sectorIncoherent link 4 5 1)
      && !(sectorIncoherent link 4 5 2))
    &&     !(sectorIncoherent link 0 3 1
      && sectorIncoherent link 0 3 2
      && sectorIncoherent link 0 3 4
      && sectorIncoherent link 0 3 5
      && sectorIncoherent link 1 2 0
      && sectorIncoherent link 1 2 3
      && sectorIncoherent link 1 2 4
      && sectorIncoherent link 1 2 5
      && sectorIncoherent link 4 5 0
      && sectorIncoherent link 4 5 3
      && sectorIncoherent link 4 5 1
      && sectorIncoherent link 4 5 2)
    &&     !(!(sectorIncoherent link 0 3 1)
      && !(sectorIncoherent link 0 3 4)
      && !(sectorIncoherent link 0 3 2)
      && !(sectorIncoherent link 0 3 5)
      && !(sectorIncoherent link 1 4 0)
      && !(sectorIncoherent link 1 4 3)
      && !(sectorIncoherent link 1 4 2)
      && !(sectorIncoherent link 1 4 5)
      && !(sectorIncoherent link 2 5 0)
      && !(sectorIncoherent link 2 5 3)
      && !(sectorIncoherent link 2 5 1)
      && !(sectorIncoherent link 2 5 4))
    &&     !(sectorIncoherent link 0 3 1
      && sectorIncoherent link 0 3 4
      && sectorIncoherent link 0 3 2
      && sectorIncoherent link 0 3 5
      && sectorIncoherent link 1 4 0
      && sectorIncoherent link 1 4 3
      && sectorIncoherent link 1 4 2
      && sectorIncoherent link 1 4 5
      && sectorIncoherent link 2 5 0
      && sectorIncoherent link 2 5 3
      && sectorIncoherent link 2 5 1
      && sectorIncoherent link 2 5 4)
    &&     !(!(sectorIncoherent link 0 3 1)
      && !(sectorIncoherent link 0 3 5)
      && !(sectorIncoherent link 0 3 2)
      && !(sectorIncoherent link 0 3 4)
      && !(sectorIncoherent link 1 5 0)
      && !(sectorIncoherent link 1 5 3)
      && !(sectorIncoherent link 1 5 2)
      && !(sectorIncoherent link 1 5 4)
      && !(sectorIncoherent link 2 4 0)
      && !(sectorIncoherent link 2 4 3)
      && !(sectorIncoherent link 2 4 1)
      && !(sectorIncoherent link 2 4 5))
    &&     !(sectorIncoherent link 0 3 1
      && sectorIncoherent link 0 3 5
      && sectorIncoherent link 0 3 2
      && sectorIncoherent link 0 3 4
      && sectorIncoherent link 1 5 0
      && sectorIncoherent link 1 5 3
      && sectorIncoherent link 1 5 2
      && sectorIncoherent link 1 5 4
      && sectorIncoherent link 2 4 0
      && sectorIncoherent link 2 4 3
      && sectorIncoherent link 2 4 1
      && sectorIncoherent link 2 4 5)
    &&     !(!(sectorIncoherent link 0 4 1)
      && !(sectorIncoherent link 0 4 2)
      && !(sectorIncoherent link 0 4 3)
      && !(sectorIncoherent link 0 4 5)
      && !(sectorIncoherent link 1 2 0)
      && !(sectorIncoherent link 1 2 4)
      && !(sectorIncoherent link 1 2 3)
      && !(sectorIncoherent link 1 2 5)
      && !(sectorIncoherent link 3 5 0)
      && !(sectorIncoherent link 3 5 4)
      && !(sectorIncoherent link 3 5 1)
      && !(sectorIncoherent link 3 5 2))
    &&     !(sectorIncoherent link 0 4 1
      && sectorIncoherent link 0 4 2
      && sectorIncoherent link 0 4 3
      && sectorIncoherent link 0 4 5
      && sectorIncoherent link 1 2 0
      && sectorIncoherent link 1 2 4
      && sectorIncoherent link 1 2 3
      && sectorIncoherent link 1 2 5
      && sectorIncoherent link 3 5 0
      && sectorIncoherent link 3 5 4
      && sectorIncoherent link 3 5 1
      && sectorIncoherent link 3 5 2)
    &&     !(!(sectorIncoherent link 0 4 1)
      && !(sectorIncoherent link 0 4 3)
      && !(sectorIncoherent link 0 4 2)
      && !(sectorIncoherent link 0 4 5)
      && !(sectorIncoherent link 1 3 0)
      && !(sectorIncoherent link 1 3 4)
      && !(sectorIncoherent link 1 3 2)
      && !(sectorIncoherent link 1 3 5)
      && !(sectorIncoherent link 2 5 0)
      && !(sectorIncoherent link 2 5 4)
      && !(sectorIncoherent link 2 5 1)
      && !(sectorIncoherent link 2 5 3))
    &&     !(sectorIncoherent link 0 4 1
      && sectorIncoherent link 0 4 3
      && sectorIncoherent link 0 4 2
      && sectorIncoherent link 0 4 5
      && sectorIncoherent link 1 3 0
      && sectorIncoherent link 1 3 4
      && sectorIncoherent link 1 3 2
      && sectorIncoherent link 1 3 5
      && sectorIncoherent link 2 5 0
      && sectorIncoherent link 2 5 4
      && sectorIncoherent link 2 5 1
      && sectorIncoherent link 2 5 3)
    &&     !(!(sectorIncoherent link 0 4 1)
      && !(sectorIncoherent link 0 4 5)
      && !(sectorIncoherent link 0 4 2)
      && !(sectorIncoherent link 0 4 3)
      && !(sectorIncoherent link 1 5 0)
      && !(sectorIncoherent link 1 5 4)
      && !(sectorIncoherent link 1 5 2)
      && !(sectorIncoherent link 1 5 3)
      && !(sectorIncoherent link 2 3 0)
      && !(sectorIncoherent link 2 3 4)
      && !(sectorIncoherent link 2 3 1)
      && !(sectorIncoherent link 2 3 5))
    &&     !(sectorIncoherent link 0 4 1
      && sectorIncoherent link 0 4 5
      && sectorIncoherent link 0 4 2
      && sectorIncoherent link 0 4 3
      && sectorIncoherent link 1 5 0
      && sectorIncoherent link 1 5 4
      && sectorIncoherent link 1 5 2
      && sectorIncoherent link 1 5 3
      && sectorIncoherent link 2 3 0
      && sectorIncoherent link 2 3 4
      && sectorIncoherent link 2 3 1
      && sectorIncoherent link 2 3 5)
    &&     !(!(sectorIncoherent link 0 5 1)
      && !(sectorIncoherent link 0 5 2)
      && !(sectorIncoherent link 0 5 3)
      && !(sectorIncoherent link 0 5 4)
      && !(sectorIncoherent link 1 2 0)
      && !(sectorIncoherent link 1 2 5)
      && !(sectorIncoherent link 1 2 3)
      && !(sectorIncoherent link 1 2 4)
      && !(sectorIncoherent link 3 4 0)
      && !(sectorIncoherent link 3 4 5)
      && !(sectorIncoherent link 3 4 1)
      && !(sectorIncoherent link 3 4 2))
    &&     !(sectorIncoherent link 0 5 1
      && sectorIncoherent link 0 5 2
      && sectorIncoherent link 0 5 3
      && sectorIncoherent link 0 5 4
      && sectorIncoherent link 1 2 0
      && sectorIncoherent link 1 2 5
      && sectorIncoherent link 1 2 3
      && sectorIncoherent link 1 2 4
      && sectorIncoherent link 3 4 0
      && sectorIncoherent link 3 4 5
      && sectorIncoherent link 3 4 1
      && sectorIncoherent link 3 4 2)
    &&     !(!(sectorIncoherent link 0 5 1)
      && !(sectorIncoherent link 0 5 3)
      && !(sectorIncoherent link 0 5 2)
      && !(sectorIncoherent link 0 5 4)
      && !(sectorIncoherent link 1 3 0)
      && !(sectorIncoherent link 1 3 5)
      && !(sectorIncoherent link 1 3 2)
      && !(sectorIncoherent link 1 3 4)
      && !(sectorIncoherent link 2 4 0)
      && !(sectorIncoherent link 2 4 5)
      && !(sectorIncoherent link 2 4 1)
      && !(sectorIncoherent link 2 4 3))
    &&     !(sectorIncoherent link 0 5 1
      && sectorIncoherent link 0 5 3
      && sectorIncoherent link 0 5 2
      && sectorIncoherent link 0 5 4
      && sectorIncoherent link 1 3 0
      && sectorIncoherent link 1 3 5
      && sectorIncoherent link 1 3 2
      && sectorIncoherent link 1 3 4
      && sectorIncoherent link 2 4 0
      && sectorIncoherent link 2 4 5
      && sectorIncoherent link 2 4 1
      && sectorIncoherent link 2 4 3)
    &&     !(!(sectorIncoherent link 0 5 1)
      && !(sectorIncoherent link 0 5 4)
      && !(sectorIncoherent link 0 5 2)
      && !(sectorIncoherent link 0 5 3)
      && !(sectorIncoherent link 1 4 0)
      && !(sectorIncoherent link 1 4 5)
      && !(sectorIncoherent link 1 4 2)
      && !(sectorIncoherent link 1 4 3)
      && !(sectorIncoherent link 2 3 0)
      && !(sectorIncoherent link 2 3 5)
      && !(sectorIncoherent link 2 3 1)
      && !(sectorIncoherent link 2 3 4))
    &&     !(sectorIncoherent link 0 5 1
      && sectorIncoherent link 0 5 4
      && sectorIncoherent link 0 5 2
      && sectorIncoherent link 0 5 3
      && sectorIncoherent link 1 4 0
      && sectorIncoherent link 1 4 5
      && sectorIncoherent link 1 4 2
      && sectorIncoherent link 1 4 3
      && sectorIncoherent link 2 3 0
      && sectorIncoherent link 2 3 5
      && sectorIncoherent link 2 3 1
      && sectorIncoherent link 2 3 4)

/-- Every constraint the sign layer of a `(6,3)` design is known to impose. -/
def sectorSurvives (link : Nat) : Bool :=
  hasNoIncoherentQuadruple link && hasNoCoherentQuadruple link && hasNoSaturatedMatching link

/-- **THE RESIDUAL SECTORS.**  The two-graphs that survive every proved constraint,
as one explicit decidable object. -/
def residualSectors : Finset Nat :=
  (Finset.range 1024).filter fun link => sectorSurvives link = true

theorem mem_residualSectors_iff (link : Nat) :
    link ∈ residualSectors ↔ link < 1024 ∧ sectorSurvives link = true := by
  rw [residualSectors, Finset.mem_filter, Finset.mem_range]

/-! ### The counts -/

/-- Sweep helper: how many of the 1024 two-graphs pass a test. -/
def sectorCount (test : Nat → Bool) : Nat := ((List.range 1024).filter test).length

/-- **THE RESIDUE: 842 OF 1024**, in eight of the sixteen isomorphism classes, and
every one of those eight is realised by an explicit design.  Stated on the `Finset`
itself, so `Gtz.SixThreeCrux.linkWord_mem_residualSectors` and this cardinality
speak about ONE object. -/
theorem card_residualSectors : residualSectors.card = 842 := by
  rw [residualSectors]
  decide +kernel

/-- L1 ALONE leaves 948, in thirteen classes. -/
theorem card_leverOneSectors : sectorCount hasNoIncoherentQuadruple = 948 := by decide +kernel

/-- L1 AND L2 leave 872, in ten classes, so the coherent cap is worth 76 patterns
and three classes and the saturated matching a further 30 and two. -/
theorem card_leverOneAndTwoSectors :
    sectorCount (fun link => hasNoIncoherentQuadruple link && hasNoCoherentQuadruple link)
      = 872 := by
  decide +kernel

/-- **CALIBRATION.**  Link `220` is in the residue.  The exact enumeration that
produced the sixteen isomorphism classes identifies `220` with the ICOSAHEDRAL
class -- the unique nontrivial regular two-graph on six points, the one
`Gtz.icosaDesign` realises -- and that identification is an ATTRIBUTION, not proved
here; what is proved here is that the link survives every lever.  It matters
because the sign-blind lanes are silent at the icosahedron as well, by
`Gtz.icosaDesign_excessGap_neg` and `Gtz.censusTripleSets_icosaDesign_eq_empty`, so
this class is the calibrated hard case of the whole cell. -/
theorem icosahedralLink_mem_residualSectors : 220 ∈ residualSectors := by
  rw [mem_residualSectors_iff]
  exact ⟨by norm_num, by decide +kernel⟩

/-- **THE EIGHT SURVIVING CLASSES**, one representative link each: the enumeration's
`Delta(2K2)`, `Delta(P4)`, `Delta(K3)`, the two orbit-180 classes with ten
incoherent triples, `Delta(C5)`, `Delta(diamond)` and `Delta(tadpole)`.  Every one
of the eight is realised by an explicit six-tuple of integer directions with exact
positive rational Parseval coefficients, so the residue is SHARP -- no correct
sign-only argument cuts any of them. -/
theorem sectorSurvives_survivingClassRepresentatives :
    sectorSurvives 19 = true ∧ sectorSurvives 20 = true ∧ sectorSurvives 21 = true
      ∧ sectorSurvives 23 = true ∧ sectorSurvives 55 = true ∧ sectorSurvives 58 = true
      ∧ sectorSurvives 185 = true ∧ sectorSurvives 220 = true := by
  decide +kernel

/-- **THE EIGHT KILLED CLASSES**, one representative link each: `Delta(empty)`,
`Delta(K2)`, `Delta(P3)`, `Delta(C4)`, `Delta(K4)`, `Delta(K3 + K2)`,
`Delta(bowtie)` and `Delta(K5)`.  L1 alone kills the last three, the coherent cap
adds the first three, and the saturated matching adds `Delta(C4)` and
`Delta(bowtie)`. -/
theorem not_sectorSurvives_killedClassRepresentatives :
    sectorSurvives 0 = false ∧ sectorSurvives 1 = false ∧ sectorSurvives 3 = false
      ∧ sectorSurvives 54 = false ∧ sectorSurvives 183 = false ∧ sectorSurvives 184 = false
      ∧ sectorSurvives 207 = false ∧ sectorSurvives 1023 = false := by
  decide +kernel

/-! ## 3. From a design to its sector

`Gtz.linkWordOf` reads the ten parities through atom `0`.  It is `noncomputable`
because comparing two reals is, and nothing computes with it; the two theorems
after it are what consumers use. -/

/-- The two-graph of a design, as a natural number below `1024`. -/
noncomputable def linkWordOf (design : WeightedDesign 6 3) : Nat :=
  packTenBits
    (decide (tripleParity design 0 1 2 = -1))
    (decide (tripleParity design 0 1 3 = -1))
    (decide (tripleParity design 0 1 4 = -1))
    (decide (tripleParity design 0 1 5 = -1))
    (decide (tripleParity design 0 2 3 = -1))
    (decide (tripleParity design 0 2 4 = -1))
    (decide (tripleParity design 0 2 5 = -1))
    (decide (tripleParity design 0 3 4 = -1))
    (decide (tripleParity design 0 3 5 = -1))
    (decide (tripleParity design 0 4 5 = -1))

theorem linkWordOf_lt (design : WeightedDesign 6 3) : linkWordOf design < 1024 :=
  packTenBits_lt _ _ _ _ _ _ _ _ _ _

/-- A triple whose last two atoms repeat is coherent -- the mirror of
`Gtz.tripleParity_degenerate`, which repeats the first two. -/
theorem tripleParity_repeat_last (design : WeightedDesign sizeIndex 3)
    (first second : Fin sizeIndex) : tripleParity design first second second = 1 := by
  rw [tripleParity_comm_left, tripleParity_comm_right]
  exact tripleParity_degenerate design second first

/-- Every triple through atom `0` that repeats an atom, or meets `0` twice, is
coherent.  This is what makes the junk arm of `Gtz.linkIndexOfValues` correct. -/
theorem decide_tripleParity_base_zero_degenerate (design : WeightedDesign 6 3)
    {atomFirst atomSecond : Fin 6}
    (hdegenerate : atomFirst = atomSecond ∨ atomFirst = 0 ∨ atomSecond = 0) :
    decide (tripleParity design 0 atomFirst atomSecond = -1) = false := by
  have hvalue : tripleParity design 0 atomFirst atomSecond = 1 := by
    rcases hdegenerate with hcase | hcase | hcase
    · subst hcase
      exact tripleParity_repeat_last design 0 atomFirst
    · subst hcase
      exact tripleParity_degenerate design 0 atomSecond
    · subst hcase
      rw [tripleParity_comm_right]
      exact tripleParity_degenerate design 0 atomFirst
  rw [hvalue]
  exact decide_eq_false (by norm_num)

/-- The link bits of `Gtz.linkWordOf` are the parities through atom `0`, at every
ordered pair including the degenerate ones. -/
theorem linkBitOf_linkWordOf (design : WeightedDesign 6 3) (atomFirst atomSecond : Fin 6) :
    linkBitOf (linkWordOf design) atomFirst atomSecond
      = decide (tripleParity design 0 atomFirst atomSecond = -1) := by
  have hswap : ∀ first second : Fin 6,
      tripleParity design 0 first second = tripleParity design 0 second first :=
    fun first second => tripleParity_comm_right design 0 first second
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    simp only [linkBitOf, linkIndexOfPair, linkIndexOfValues, linkWordOf,
      testBit_packTenBits_zero, testBit_packTenBits_one, testBit_packTenBits_two,
      testBit_packTenBits_three, testBit_packTenBits_four, testBit_packTenBits_five,
      testBit_packTenBits_six, testBit_packTenBits_seven, testBit_packTenBits_eight,
      testBit_packTenBits_nine, testBit_packTenBits_ten] <;>
    first
      | rfl
      | exact (decide_tripleParity_base_zero_degenerate design (by decide)).symm
      | (rw [hswap]; rfl)

/-- **THE DICTIONARY.**  The sector decode of `Gtz.linkWordOf design` agrees with
`Gtz.tripleParity` at EVERY triple -- no distinctness, no nonvanishing.  This is
the product law `Gtz.tripleParity_eq_product_through_base` in Boolean form. -/
theorem sectorIncoherent_linkWordOf (design : WeightedDesign 6 3) (first second third : Fin 6) :
    sectorIncoherent (linkWordOf design) first second third
      = decide (tripleParity design first second third = -1) := by
  have hproduct := tripleParity_eq_product_through_base design 0 first second third
  rw [sectorIncoherent, linkBitOf_linkWordOf, linkBitOf_linkWordOf, linkBitOf_linkWordOf]
  rcases tripleParity_eq_one_or_neg_one design 0 first second with hone | hone <;>
    rcases tripleParity_eq_one_or_neg_one design 0 first third with htwo | htwo <;>
    rcases tripleParity_eq_one_or_neg_one design 0 second third with hthree | hthree <;>
    rw [hone, htwo, hthree] at hproduct <;> rw [hone, htwo, hthree, hproduct] <;> norm_num

theorem tripleParity_eq_one_of_ne_neg_one (design : WeightedDesign sizeIndex 3)
    {first second third : Fin sizeIndex}
    (hne : ¬ (tripleParity design first second third = -1)) :
    tripleParity design first second third = 1 := by
  rcases tripleParity_eq_one_or_neg_one design first second third with hvalue | hvalue
  · exact hvalue
  · exact absurd hvalue hne

/-! ## 4. The second lever: the coherent cap

`Gtz.card_le_three_of_forall_incoherent_through_base` caps an INCOHERENT family.
Running it on the anti-parity partner -- the chart dual, whose parities are the
negatives of the design's by `Gtz.tripleParity_chartDual` -- caps a COHERENT one. -/

/-- **THE COHERENT CAP.**  A base-avoiding family whose triples through the base are
all COHERENT has at most three members. -/
theorem card_le_three_of_forall_coherent_through_base (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0)
    (base : Fin 6) (family : Finset (Fin 6)) (hbaseNotMem : base ∉ family)
    (hcoherent : ∀ first ∈ family, ∀ second ∈ family, first ≠ second →
      tripleParity design base first second = 1) :
    family.card ≤ 3 := by
  obtain ⟨partner, _, hpartnerNonzero, hflip⟩ := exists_antiParityPartner_sixThree design hnonzero
  refine card_le_three_of_forall_incoherent_through_base partner base family hbaseNotMem
    ?_ ?_ ?_
  · intro index hmem
    exact hpartnerNonzero base index (by rintro rfl; exact hbaseNotMem hmem)
  · intro first _ second _ hne
    exact hpartnerNonzero first second hne
  · intro first hfirst second hsecond hne
    have hbaseFirst : base ≠ first := by rintro rfl; exact hbaseNotMem hfirst
    have hbaseSecond : base ≠ second := by rintro rfl; exact hbaseNotMem hsecond
    rw [hflip base first second hbaseFirst hbaseSecond hne,
      hcoherent first hfirst second hsecond hne]

/-! ## 5. The third lever: the edge law and the saturated matching

The Parseval field of a `Gtz.WeightedDesign` says `sum_e t_e g_e g_e^T = 1`.  Read
as a bilinear form at two atoms it is `Gtz.sum_weight_mul_atomPairing_mul_atomPairing`;
splitting off the two diagonal terms, whose weights are exactly the two shares,
leaves the EDGE LAW.  Multiplying it by the edge pairing turns every summand into
the oriented triple product of `{c, d, e}`, whose sign IS the parity -- so a
uniformly signed edge forces its two shares off `1`, in the direction the sign
names, and three such edges in a perfect matching contradict the share total. -/

/-- **THE EDGE LAW.**  Off the diagonal the frame identity reads
`sum over the other atoms of t_e p_ce p_ed = p_cd (1 - s_c - s_d)`. -/
theorem sum_erasePair_weight_mul_atomPairing (design : WeightedDesign sizeIndex 3)
    {edgeFirst edgeSecond : Fin sizeIndex} (hedge : edgeFirst ≠ edgeSecond) :
    ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
        design.weight other
          * (atomPairing design edgeFirst other * atomPairing design other edgeSecond)
      = atomPairing design edgeFirst edgeSecond
        * (1 - atomShare design edgeFirst - atomShare design edgeSecond) := by
  have hfull : ∑ other, design.weight other
      * (atomPairing design edgeFirst other * atomPairing design other edgeSecond)
      = atomPairing design edgeFirst edgeSecond :=
    sum_weight_mul_atomPairing_mul_atomPairing design edgeFirst edgeSecond
  have hsplitFirst := Finset.add_sum_erase (Finset.univ : Finset (Fin sizeIndex))
    (fun other => design.weight other
      * (atomPairing design edgeFirst other * atomPairing design other edgeSecond))
    (Finset.mem_univ edgeFirst)
  have hsplitSecond := Finset.add_sum_erase
    ((Finset.univ : Finset (Fin sizeIndex)).erase edgeFirst)
    (fun other => design.weight other
      * (atomPairing design edgeFirst other * atomPairing design other edgeSecond))
    (Finset.mem_erase.2 ⟨Ne.symm hedge, Finset.mem_univ edgeSecond⟩)
  simp only [atomPairing_self] at hsplitFirst hsplitSecond
  rw [atomShare, atomShare]
  nlinarith [hfull, hsplitFirst, hsplitSecond]

/-- A triple of parity `-1` with nonvanishing pairings has a NEGATIVE oriented
product -- the mirror of `Gtz.pos_atomPairingProduct_of_tripleParity_eq_one`. -/
theorem neg_atomPairingProduct_of_tripleParity_eq_neg_one (design : WeightedDesign sizeIndex 3)
    {first second third : Fin sizeIndex}
    (hparity : tripleParity design first second third = -1)
    (hnonzero : atomPairing design first second * atomPairing design first third
      * atomPairing design second third ≠ 0) :
    atomPairing design first second * atomPairing design first third
      * atomPairing design second third < 0 := by
  have hcarry := tripleParity_mul_abs_atomPairingProduct design first second third
  rw [hparity] at hcarry
  have hposAbs : 0 < |atomPairing design first second * atomPairing design first third
      * atomPairing design second third| := abs_pos.2 hnonzero
  linarith

/-- **THE SATURATED EDGE, COHERENT SIDE.**  If every triple through an edge is
coherent then the two shares sum to strictly less than one. -/
theorem atomShare_add_atomShare_lt_one_of_coherentEdge (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0)
    {edgeFirst edgeSecond : Fin 6} (hedge : edgeFirst ≠ edgeSecond)
    (hcoherent : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      tripleParity design edgeFirst edgeSecond other = 1) :
    atomShare design edgeFirst + atomShare design edgeSecond < 1 := by
  have hlaw := sum_erasePair_weight_mul_atomPairing design hedge
  have hpairNe : atomPairing design edgeFirst edgeSecond ≠ 0 := hnonzero _ _ hedge
  have hnonempty :
      ((Finset.univ.erase edgeFirst).erase edgeSecond : Finset (Fin 6)).Nonempty := by
    rw [← Finset.card_pos,
      Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hedge, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    norm_num
  have htermPos : ∀ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      0 < atomPairing design edgeFirst edgeSecond * (design.weight other
        * (atomPairing design edgeFirst other * atomPairing design other edgeSecond)) := by
    intro other hother
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hother
    obtain ⟨hotherSecond, hotherFirst⟩ := hother
    have hprodNe : atomPairing design edgeFirst edgeSecond * atomPairing design edgeFirst other
        * atomPairing design edgeSecond other ≠ 0 :=
      mul_ne_zero (mul_ne_zero hpairNe (hnonzero _ _ (Ne.symm hotherFirst)))
        (hnonzero _ _ (Ne.symm hotherSecond))
    have hprod := pos_atomPairingProduct_of_tripleParity_eq_one design
      (hcoherent other hotherFirst hotherSecond) hprodNe
    have hswap : atomPairing design other edgeSecond = atomPairing design edgeSecond other :=
      atomPairing_comm design other edgeSecond
    have hweight := design.weight_pos other
    rw [hswap]
    nlinarith [hprod, hweight]
  have hsumPos : 0 < ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      atomPairing design edgeFirst edgeSecond * (design.weight other
        * (atomPairing design edgeFirst other * atomPairing design other edgeSecond)) :=
    Finset.sum_pos htermPos hnonempty
  rw [← Finset.mul_sum, hlaw] at hsumPos
  have hsq : 0 < atomPairing design edgeFirst edgeSecond ^ 2 := by positivity
  nlinarith [hsumPos, hsq]

/-- **THE SATURATED EDGE, INCOHERENT SIDE.** -/
theorem one_lt_atomShare_add_atomShare_of_incoherentEdge (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0)
    {edgeFirst edgeSecond : Fin 6} (hedge : edgeFirst ≠ edgeSecond)
    (hincoherent : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      tripleParity design edgeFirst edgeSecond other = -1) :
    1 < atomShare design edgeFirst + atomShare design edgeSecond := by
  have hlaw := sum_erasePair_weight_mul_atomPairing design hedge
  have hpairNe : atomPairing design edgeFirst edgeSecond ≠ 0 := hnonzero _ _ hedge
  have hnonempty :
      ((Finset.univ.erase edgeFirst).erase edgeSecond : Finset (Fin 6)).Nonempty := by
    rw [← Finset.card_pos,
      Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hedge, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    norm_num
  have htermNeg : ∀ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      atomPairing design edgeFirst edgeSecond * (design.weight other
        * (atomPairing design edgeFirst other * atomPairing design other edgeSecond)) < 0 := by
    intro other hother
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hother
    obtain ⟨hotherSecond, hotherFirst⟩ := hother
    have hprodNe : atomPairing design edgeFirst edgeSecond * atomPairing design edgeFirst other
        * atomPairing design edgeSecond other ≠ 0 :=
      mul_ne_zero (mul_ne_zero hpairNe (hnonzero _ _ (Ne.symm hotherFirst)))
        (hnonzero _ _ (Ne.symm hotherSecond))
    have hprod := neg_atomPairingProduct_of_tripleParity_eq_neg_one design
      (hincoherent other hotherFirst hotherSecond) hprodNe
    have hswap : atomPairing design other edgeSecond = atomPairing design edgeSecond other :=
      atomPairing_comm design other edgeSecond
    have hweight := design.weight_pos other
    rw [hswap]
    nlinarith [hprod, hweight]
  have hsumNeg : ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      atomPairing design edgeFirst edgeSecond * (design.weight other
        * (atomPairing design edgeFirst other * atomPairing design other edgeSecond)) < 0 :=
    Finset.sum_neg htermNeg hnonempty
  rw [← Finset.mul_sum, hlaw] at hsumNeg
  have hsq : 0 < atomPairing design edgeFirst edgeSecond ^ 2 := by positivity
  nlinarith [hsumNeg, hsq]

theorem atomShare_pair_lt_one_of_coherentStar (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0)
    {edgeFirst edgeSecond otherOne otherTwo otherThree otherFour : Fin 6}
    (hedge : edgeFirst ≠ edgeSecond)
    (hcover : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      other = otherOne ∨ other = otherTwo ∨ other = otherThree ∨ other = otherFour)
    (hone : tripleParity design edgeFirst edgeSecond otherOne = 1)
    (htwo : tripleParity design edgeFirst edgeSecond otherTwo = 1)
    (hthree : tripleParity design edgeFirst edgeSecond otherThree = 1)
    (hfour : tripleParity design edgeFirst edgeSecond otherFour = 1) :
    atomShare design edgeFirst + atomShare design edgeSecond < 1 := by
  refine atomShare_add_atomShare_lt_one_of_coherentEdge design hnonzero hedge ?_
  intro other hneFirst hneSecond
  rcases hcover other hneFirst hneSecond with rfl | rfl | rfl | rfl
  · exact hone
  · exact htwo
  · exact hthree
  · exact hfour

theorem one_lt_atomShare_pair_of_incoherentStar (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0)
    {edgeFirst edgeSecond otherOne otherTwo otherThree otherFour : Fin 6}
    (hedge : edgeFirst ≠ edgeSecond)
    (hcover : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      other = otherOne ∨ other = otherTwo ∨ other = otherThree ∨ other = otherFour)
    (hone : tripleParity design edgeFirst edgeSecond otherOne = -1)
    (htwo : tripleParity design edgeFirst edgeSecond otherTwo = -1)
    (hthree : tripleParity design edgeFirst edgeSecond otherThree = -1)
    (hfour : tripleParity design edgeFirst edgeSecond otherFour = -1) :
    1 < atomShare design edgeFirst + atomShare design edgeSecond := by
  refine one_lt_atomShare_add_atomShare_of_incoherentEdge design hnonzero hedge ?_
  intro other hneFirst hneSecond
  rcases hcover other hneFirst hneSecond with rfl | rfl | rfl | rfl
  · exact hone
  · exact htwo
  · exact hthree
  · exact hfour

/-! ## 6. The sixty tests, discharged -/

/-- One L1 conjunct.  The six triples a base spans with a four-element family
cannot all be incoherent. -/
theorem incoherentQuadruple_eq_false (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0)
    (base quadFirst quadSecond quadThird quadFourth : Fin 6)
    (hcard : ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)).card = 4)
    (hbase : base ∉ ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6))) :
    (sectorIncoherent (linkWordOf design) base quadFirst quadSecond
      && sectorIncoherent (linkWordOf design) base quadFirst quadThird
      && sectorIncoherent (linkWordOf design) base quadFirst quadFourth
      && sectorIncoherent (linkWordOf design) base quadSecond quadThird
      && sectorIncoherent (linkWordOf design) base quadSecond quadFourth
      && sectorIncoherent (linkWordOf design) base quadThird quadFourth) = false := by
  by_contra hcontra
  rw [Bool.not_eq_false] at hcontra
  simp only [sectorIncoherent_linkWordOf, Bool.and_eq_true, decide_eq_true_eq] at hcontra
  obtain ⟨⟨⟨⟨⟨hfs, hft⟩, hfu⟩, hst⟩, hsu⟩, htu⟩ := hcontra
  have hcomm : ∀ leftAtom rightAtom : Fin 6,
      tripleParity design base leftAtom rightAtom
        = tripleParity design base rightAtom leftAtom :=
    fun leftAtom rightAtom => tripleParity_comm_right design base leftAtom rightAtom
  have hall : ∀ first ∈ ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)),
      ∀ second ∈ ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)),
      first ≠ second → tripleParity design base first second = -1 := by
    intro first hfirst second hsecond hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
    rcases hfirst with rfl | rfl | rfl | rfl <;> rcases hsecond with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | assumption
        | (rw [hcomm]; assumption)
  have hcap := card_le_three_of_forall_incoherent_through_base design base
    {quadFirst, quadSecond, quadThird, quadFourth} hbase
    (fun index hmem => hnonzero base index (by rintro rfl; exact hbase hmem))
    (fun first _ second _ hne => hnonzero first second hne) hall
  omega

/-- One L2 conjunct.  The six triples a base spans with a four-element family
cannot all be coherent. -/
theorem coherentQuadruple_eq_false (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0)
    (base quadFirst quadSecond quadThird quadFourth : Fin 6)
    (hcard : ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)).card = 4)
    (hbase : base ∉ ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6))) :
    (!(sectorIncoherent (linkWordOf design) base quadFirst quadSecond)
      && !(sectorIncoherent (linkWordOf design) base quadFirst quadThird)
      && !(sectorIncoherent (linkWordOf design) base quadFirst quadFourth)
      && !(sectorIncoherent (linkWordOf design) base quadSecond quadThird)
      && !(sectorIncoherent (linkWordOf design) base quadSecond quadFourth)
      && !(sectorIncoherent (linkWordOf design) base quadThird quadFourth)) = false := by
  by_contra hcontra
  rw [Bool.not_eq_false] at hcontra
  simp only [sectorIncoherent_linkWordOf, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not] at hcontra
  obtain ⟨⟨⟨⟨⟨hfs, hft⟩, hfu⟩, hst⟩, hsu⟩, htu⟩ := hcontra
  have hcomm : ∀ leftAtom rightAtom : Fin 6,
      tripleParity design base leftAtom rightAtom
        = tripleParity design base rightAtom leftAtom :=
    fun leftAtom rightAtom => tripleParity_comm_right design base leftAtom rightAtom
  have hall : ∀ first ∈ ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)),
      ∀ second ∈ ({quadFirst, quadSecond, quadThird, quadFourth} : Finset (Fin 6)),
      first ≠ second → tripleParity design base first second = 1 := by
    intro first hfirst second hsecond hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
    rcases hfirst with rfl | rfl | rfl | rfl <;> rcases hsecond with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | (apply tripleParity_eq_one_of_ne_neg_one; assumption)
        | (rw [hcomm]; apply tripleParity_eq_one_of_ne_neg_one; assumption)
  have hcap := card_le_three_of_forall_coherent_through_base design hnonzero base
    {quadFirst, quadSecond, quadThird, quadFourth} hbase hall
  omega

/-- One L3 conjunct, coherent side.  A perfect matching cannot have all three edges
coherent-saturated: each would force its two shares below one, and the six shares
sum to three. -/
theorem coherentMatching_eq_false (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0)
    (matchOne matchTwo matchThree matchFour matchFive matchSix : Fin 6)
    (hedgeOne : matchOne ≠ matchTwo) (hedgeTwo : matchThree ≠ matchFour)
    (hedgeThree : matchFive ≠ matchSix)
    (hcoverOne : ∀ other : Fin 6, other ≠ matchOne → other ≠ matchTwo →
      other = matchThree ∨ other = matchFour ∨ other = matchFive ∨ other = matchSix)
    (hcoverTwo : ∀ other : Fin 6, other ≠ matchThree → other ≠ matchFour →
      other = matchOne ∨ other = matchTwo ∨ other = matchFive ∨ other = matchSix)
    (hcoverThree : ∀ other : Fin 6, other ≠ matchFive → other ≠ matchSix →
      other = matchOne ∨ other = matchTwo ∨ other = matchThree ∨ other = matchFour)
    (hshareSum : atomShare design matchOne + atomShare design matchTwo
      + atomShare design matchThree + atomShare design matchFour
      + atomShare design matchFive + atomShare design matchSix = 3) :
    (!(sectorIncoherent (linkWordOf design) matchOne matchTwo matchThree)
      && !(sectorIncoherent (linkWordOf design) matchOne matchTwo matchFour)
      && !(sectorIncoherent (linkWordOf design) matchOne matchTwo matchFive)
      && !(sectorIncoherent (linkWordOf design) matchOne matchTwo matchSix)
      && !(sectorIncoherent (linkWordOf design) matchThree matchFour matchOne)
      && !(sectorIncoherent (linkWordOf design) matchThree matchFour matchTwo)
      && !(sectorIncoherent (linkWordOf design) matchThree matchFour matchFive)
      && !(sectorIncoherent (linkWordOf design) matchThree matchFour matchSix)
      && !(sectorIncoherent (linkWordOf design) matchFive matchSix matchOne)
      && !(sectorIncoherent (linkWordOf design) matchFive matchSix matchTwo)
      && !(sectorIncoherent (linkWordOf design) matchFive matchSix matchThree)
      && !(sectorIncoherent (linkWordOf design) matchFive matchSix matchFour)) = false
     := by
  by_contra hcontra
  rw [Bool.not_eq_false] at hcontra
  simp only [sectorIncoherent_linkWordOf, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not] at hcontra
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpOne, hpTwo⟩, hpThree⟩, hpFour⟩, hpFive⟩, hpSix⟩, hpSeven⟩, hpEight⟩, hpNine⟩, hpTen⟩, hpEleven⟩, hpTwelve⟩ := hcontra
  have hedgeA := atomShare_pair_lt_one_of_coherentStar design hnonzero hedgeOne hcoverOne
    (tripleParity_eq_one_of_ne_neg_one design hpOne)
    (tripleParity_eq_one_of_ne_neg_one design hpTwo)
    (tripleParity_eq_one_of_ne_neg_one design hpThree)
    (tripleParity_eq_one_of_ne_neg_one design hpFour)
  have hedgeB := atomShare_pair_lt_one_of_coherentStar design hnonzero hedgeTwo hcoverTwo
    (tripleParity_eq_one_of_ne_neg_one design hpFive)
    (tripleParity_eq_one_of_ne_neg_one design hpSix)
    (tripleParity_eq_one_of_ne_neg_one design hpSeven)
    (tripleParity_eq_one_of_ne_neg_one design hpEight)
  have hedgeC := atomShare_pair_lt_one_of_coherentStar design hnonzero hedgeThree hcoverThree
    (tripleParity_eq_one_of_ne_neg_one design hpNine)
    (tripleParity_eq_one_of_ne_neg_one design hpTen)
    (tripleParity_eq_one_of_ne_neg_one design hpEleven)
    (tripleParity_eq_one_of_ne_neg_one design hpTwelve)
  linarith

/-- One L3 conjunct, incoherent side. -/
theorem incoherentMatching_eq_false (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0)
    (matchOne matchTwo matchThree matchFour matchFive matchSix : Fin 6)
    (hedgeOne : matchOne ≠ matchTwo) (hedgeTwo : matchThree ≠ matchFour)
    (hedgeThree : matchFive ≠ matchSix)
    (hcoverOne : ∀ other : Fin 6, other ≠ matchOne → other ≠ matchTwo →
      other = matchThree ∨ other = matchFour ∨ other = matchFive ∨ other = matchSix)
    (hcoverTwo : ∀ other : Fin 6, other ≠ matchThree → other ≠ matchFour →
      other = matchOne ∨ other = matchTwo ∨ other = matchFive ∨ other = matchSix)
    (hcoverThree : ∀ other : Fin 6, other ≠ matchFive → other ≠ matchSix →
      other = matchOne ∨ other = matchTwo ∨ other = matchThree ∨ other = matchFour)
    (hshareSum : atomShare design matchOne + atomShare design matchTwo
      + atomShare design matchThree + atomShare design matchFour
      + atomShare design matchFive + atomShare design matchSix = 3) :
    (sectorIncoherent (linkWordOf design) matchOne matchTwo matchThree
      && sectorIncoherent (linkWordOf design) matchOne matchTwo matchFour
      && sectorIncoherent (linkWordOf design) matchOne matchTwo matchFive
      && sectorIncoherent (linkWordOf design) matchOne matchTwo matchSix
      && sectorIncoherent (linkWordOf design) matchThree matchFour matchOne
      && sectorIncoherent (linkWordOf design) matchThree matchFour matchTwo
      && sectorIncoherent (linkWordOf design) matchThree matchFour matchFive
      && sectorIncoherent (linkWordOf design) matchThree matchFour matchSix
      && sectorIncoherent (linkWordOf design) matchFive matchSix matchOne
      && sectorIncoherent (linkWordOf design) matchFive matchSix matchTwo
      && sectorIncoherent (linkWordOf design) matchFive matchSix matchThree
      && sectorIncoherent (linkWordOf design) matchFive matchSix matchFour) = false
     := by
  by_contra hcontra
  rw [Bool.not_eq_false] at hcontra
  simp only [sectorIncoherent_linkWordOf, Bool.and_eq_true, decide_eq_true_eq] at hcontra
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpOne, hpTwo⟩, hpThree⟩, hpFour⟩, hpFive⟩, hpSix⟩, hpSeven⟩, hpEight⟩, hpNine⟩, hpTen⟩, hpEleven⟩, hpTwelve⟩ := hcontra
  have hedgeA := one_lt_atomShare_pair_of_incoherentStar design hnonzero hedgeOne hcoverOne
    hpOne hpTwo hpThree hpFour
  have hedgeB := one_lt_atomShare_pair_of_incoherentStar design hnonzero hedgeTwo hcoverTwo
    hpFive hpSix hpSeven hpEight
  have hedgeC := one_lt_atomShare_pair_of_incoherentStar design hnonzero hedgeThree hcoverThree
    hpNine hpTen hpEleven hpTwelve
  linarith

/-! ## 7. The collision -/

theorem hasNoIncoherentQuadruple_linkWordOf (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0) :
    hasNoIncoherentQuadruple (linkWordOf design) = true := by
  simp only [hasNoIncoherentQuadruple,
    incoherentQuadruple_eq_false design hnonzero 0 1 2 3 4 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 0 1 2 3 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 0 1 2 4 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 0 1 3 4 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 0 2 3 4 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 1 0 2 3 4 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 1 0 2 3 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 1 0 2 4 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 1 0 3 4 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 1 2 3 4 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 2 0 1 3 4 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 2 0 1 3 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 2 0 1 4 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 2 0 3 4 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 2 1 3 4 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 3 0 1 2 4 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 3 0 1 2 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 3 0 1 4 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 3 0 2 4 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 3 1 2 4 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 4 0 1 2 3 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 4 0 1 2 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 4 0 1 3 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 4 0 2 3 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 4 1 2 3 5 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 5 0 1 2 3 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 5 0 1 2 4 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 5 0 1 3 4 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 5 0 2 3 4 (by decide) (by decide),
    incoherentQuadruple_eq_false design hnonzero 5 1 2 3 4 (by decide) (by decide),
    Bool.not_false, Bool.and_self]

theorem hasNoCoherentQuadruple_linkWordOf (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0) :
    hasNoCoherentQuadruple (linkWordOf design) = true := by
  simp only [hasNoCoherentQuadruple,
    coherentQuadruple_eq_false design hnonzero 0 1 2 3 4 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 0 1 2 3 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 0 1 2 4 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 0 1 3 4 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 0 2 3 4 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 1 0 2 3 4 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 1 0 2 3 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 1 0 2 4 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 1 0 3 4 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 1 2 3 4 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 2 0 1 3 4 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 2 0 1 3 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 2 0 1 4 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 2 0 3 4 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 2 1 3 4 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 3 0 1 2 4 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 3 0 1 2 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 3 0 1 4 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 3 0 2 4 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 3 1 2 4 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 4 0 1 2 3 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 4 0 1 2 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 4 0 1 3 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 4 0 2 3 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 4 1 2 3 5 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 5 0 1 2 3 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 5 0 1 2 4 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 5 0 1 3 4 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 5 0 2 3 4 (by decide) (by decide),
    coherentQuadruple_eq_false design hnonzero 5 1 2 3 4 (by decide) (by decide),
    Bool.not_false, Bool.and_self]

theorem hasNoSaturatedMatching_linkWordOf (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0) :
    hasNoSaturatedMatching (linkWordOf design) = true := by
  have hshareTotal : atomShare design 0 + atomShare design 1 + atomShare design 2
      + atomShare design 3 + atomShare design 4 + atomShare design 5 = 3 := by
    have hrank := sum_atomShare_eq_rank design
    rw [Fin.sum_univ_six] at hrank
    push_cast at hrank
    linarith
  simp only [hasNoSaturatedMatching,
    coherentMatching_eq_false design hnonzero 0 1 2 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 1 2 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    coherentMatching_eq_false design hnonzero 0 1 2 4 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 1 2 4 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    coherentMatching_eq_false design hnonzero 0 1 2 5 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 1 2 5 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    coherentMatching_eq_false design hnonzero 0 2 1 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 2 1 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    coherentMatching_eq_false design hnonzero 0 2 1 4 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 2 1 4 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    coherentMatching_eq_false design hnonzero 0 2 1 5 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 2 1 5 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    coherentMatching_eq_false design hnonzero 0 3 1 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 3 1 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    coherentMatching_eq_false design hnonzero 0 3 1 4 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 3 1 4 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    coherentMatching_eq_false design hnonzero 0 3 1 5 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 3 1 5 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    coherentMatching_eq_false design hnonzero 0 4 1 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 4 1 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    coherentMatching_eq_false design hnonzero 0 4 1 3 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 4 1 3 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    coherentMatching_eq_false design hnonzero 0 4 1 5 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 4 1 5 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    coherentMatching_eq_false design hnonzero 0 5 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 5 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    coherentMatching_eq_false design hnonzero 0 5 1 3 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 5 1 3 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    coherentMatching_eq_false design hnonzero 0 5 1 4 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    incoherentMatching_eq_false design hnonzero 0 5 1 4 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith),
    Bool.not_false, Bool.and_self]

/-- **THE BRIDGE.**  The two-graph of any `(6,3)` design with nonvanishing pairings
survives every proved sector constraint. -/
theorem sectorSurvives_linkWordOf (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0) :
    sectorSurvives (linkWordOf design) = true := by
  rw [sectorSurvives, hasNoIncoherentQuadruple_linkWordOf design hnonzero,
    hasNoCoherentQuadruple_linkWordOf design hnonzero,
    hasNoSaturatedMatching_linkWordOf design hnonzero]
  rfl

theorem linkWordOf_mem_residualSectors (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0) :
    linkWordOf design ∈ residualSectors :=
  (mem_residualSectors_iff _).2 ⟨linkWordOf_lt design, sectorSurvives_linkWordOf design hnonzero⟩

/-! ## 8. The vanishing-pairing branch, as far as the edge law reaches

Every lever above needs pairings that do not vanish, and a crux is not known to
supply them.  The EDGE LAW does not: at an ORTHOGONAL edge its right-hand side is
identically zero, so the four star products must CANCEL.  That is strictly stronger
than the saturated-edge inequalities -- an orthogonal edge cannot be sign-saturated
AT ALL, in either parity, however the shares fall.  What is still missing, and what
a successor should build, is the same statement for L1 and L2: those descend from
`Gtz.card_le_succ_of_isPairwiseObtuse_on`, whose obtuseness is STRICT, and the
non-strict cap in `R^3` is six rather than four, so they genuinely fail here rather
than merely resisting proof. -/


theorem sum_erasePair_eq_zero_of_atomPairing_eq_zero (design : WeightedDesign sizeIndex 3)
    {edgeFirst edgeSecond : Fin sizeIndex} (hedge : edgeFirst ≠ edgeSecond)
    (hzero : atomPairing design edgeFirst edgeSecond = 0) :
    ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
        design.weight other
          * (atomPairing design edgeFirst other * atomPairing design other edgeSecond) = 0 := by
  rw [sum_erasePair_weight_mul_atomPairing design hedge, hzero, zero_mul]

theorem le_of_edgeSign_eq_one (design : WeightedDesign sizeIndex 3)
    {atomFirst atomSecond : Fin sizeIndex} (hsign : edgeSign design atomFirst atomSecond = 1) :
    0 ≤ atomPairing design atomFirst atomSecond := by
  by_contra hneg
  rw [(edgeSign_eq_neg_one_iff design atomFirst atomSecond).2 (not_le.1 hneg)] at hsign
  norm_num at hsign

theorem edgeSign_eq_one_of_atomPairing_eq_zero (design : WeightedDesign sizeIndex 3)
    {atomFirst atomSecond : Fin sizeIndex}
    (hzero : atomPairing design atomFirst atomSecond = 0) :
    edgeSign design atomFirst atomSecond = 1 := by
  rcases edgeSign_eq_one_or_neg_one design atomFirst atomSecond with hvalue | hvalue
  · exact hvalue
  · exact absurd ((edgeSign_eq_neg_one_iff design atomFirst atomSecond).1 hvalue) (by simp [hzero])

/-- At an ORTHOGONAL edge the parity of a triple through it is the product of the two
remaining edge signs, and it is `1` exactly when the two remaining pairings agree in
sign -- so it reads the star directly, with the edge itself contributing nothing. -/
theorem pos_atomPairing_mul_of_tripleParity_eq_one_of_orthogonalEdge
    (design : WeightedDesign sizeIndex 3) {edgeFirst edgeSecond other : Fin sizeIndex}
    (hzero : atomPairing design edgeFirst edgeSecond = 0)
    (hfirstNonzero : atomPairing design edgeFirst other ≠ 0)
    (hsecondNonzero : atomPairing design edgeSecond other ≠ 0)
    (hparity : tripleParity design edgeFirst edgeSecond other = 1) :
    0 < atomPairing design edgeFirst other * atomPairing design edgeSecond other := by
  rw [tripleParity, edgeSign_eq_one_of_atomPairing_eq_zero design hzero, one_mul] at hparity
  rcases edgeSign_eq_one_or_neg_one design edgeFirst other with hfirst | hfirst <;>
    rcases edgeSign_eq_one_or_neg_one design edgeSecond other with hsecond | hsecond <;>
    rw [hfirst, hsecond] at hparity
  · have hleft := le_of_edgeSign_eq_one design hfirst
    have hright := le_of_edgeSign_eq_one design hsecond
    exact mul_pos (lt_of_le_of_ne hleft (Ne.symm hfirstNonzero))
      (lt_of_le_of_ne hright (Ne.symm hsecondNonzero))
  · norm_num at hparity
  · norm_num at hparity
  · have hleft := (edgeSign_eq_neg_one_iff design edgeFirst other).1 hfirst
    have hright := (edgeSign_eq_neg_one_iff design edgeSecond other).1 hsecond
    exact mul_pos_of_neg_of_neg hleft hright

/-- **AN ORTHOGONAL EDGE CANNOT BE COHERENT-SATURATED.**  Where the shares of a
sign-saturated edge are pushed off one by the edge law, an edge whose own pairing
VANISHES cannot be saturated at all: the edge law makes the four star products sum
to exactly zero, and coherence would make every one of them positive. -/
theorem not_forall_coherent_of_orthogonalEdge (design : WeightedDesign 6 3)
    {edgeFirst edgeSecond : Fin 6} (hedge : edgeFirst ≠ edgeSecond)
    (hzero : atomPairing design edgeFirst edgeSecond = 0)
    (hstarFirst : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      atomPairing design edgeFirst other ≠ 0)
    (hstarSecond : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      atomPairing design edgeSecond other ≠ 0) :
    ¬ (∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      tripleParity design edgeFirst edgeSecond other = 1) := by
  intro hcoherent
  have hnonempty :
      ((Finset.univ.erase edgeFirst).erase edgeSecond : Finset (Fin 6)).Nonempty := by
    rw [← Finset.card_pos,
      Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hedge, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    norm_num
  have hpos : 0 < ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      design.weight other
        * (atomPairing design edgeFirst other * atomPairing design other edgeSecond) := by
    refine Finset.sum_pos (fun other hother => ?_) hnonempty
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hother
    obtain ⟨hotherSecond, hotherFirst⟩ := hother
    have hstar := pos_atomPairing_mul_of_tripleParity_eq_one_of_orthogonalEdge design hzero
      (hstarFirst other hotherFirst hotherSecond) (hstarSecond other hotherFirst hotherSecond)
      (hcoherent other hotherFirst hotherSecond)
    rw [atomPairing_comm design other edgeSecond]
    exact mul_pos (design.weight_pos other) hstar
  rw [sum_erasePair_eq_zero_of_atomPairing_eq_zero design hedge hzero] at hpos
  exact lt_irrefl 0 hpos


theorem neg_atomPairing_mul_of_tripleParity_eq_neg_one_of_orthogonalEdge
    (design : WeightedDesign sizeIndex 3)
    {edgeFirst edgeSecond other : Fin sizeIndex}
    (hzero : atomPairing design edgeFirst edgeSecond = 0)
    (hfirstNonzero : atomPairing design edgeFirst other ≠ 0)
    (hsecondNonzero : atomPairing design edgeSecond other ≠ 0)
    (hparity : tripleParity design edgeFirst edgeSecond other = -1) :
    atomPairing design edgeFirst other * atomPairing design edgeSecond other < 0 := by
  rw [tripleParity, edgeSign_eq_one_of_atomPairing_eq_zero design hzero, one_mul] at hparity
  rcases edgeSign_eq_one_or_neg_one design edgeFirst other with hfirst | hfirst <;>
    rcases edgeSign_eq_one_or_neg_one design edgeSecond other with hsecond | hsecond <;>
    rw [hfirst, hsecond] at hparity
  · norm_num at hparity
  · exact mul_neg_of_pos_of_neg
      (lt_of_le_of_ne (le_of_edgeSign_eq_one design hfirst) (Ne.symm hfirstNonzero))
      ((edgeSign_eq_neg_one_iff design edgeSecond other).1 hsecond)
  · exact mul_neg_of_neg_of_pos ((edgeSign_eq_neg_one_iff design edgeFirst other).1 hfirst)
      (lt_of_le_of_ne (le_of_edgeSign_eq_one design hsecond) (Ne.symm hsecondNonzero))
  · norm_num at hparity

/-- **AN ORTHOGONAL EDGE CANNOT BE INCOHERENT-SATURATED EITHER.** -/
theorem not_forall_incoherent_of_orthogonalEdge (design : WeightedDesign 6 3)
    {edgeFirst edgeSecond : Fin 6} (hedge : edgeFirst ≠ edgeSecond)
    (hzero : atomPairing design edgeFirst edgeSecond = 0)
    (hstarFirst : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      atomPairing design edgeFirst other ≠ 0)
    (hstarSecond : ∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      atomPairing design edgeSecond other ≠ 0) :
    ¬ (∀ other : Fin 6, other ≠ edgeFirst → other ≠ edgeSecond →
      tripleParity design edgeFirst edgeSecond other = -1) := by
  intro hincoherent
  have hnonempty :
      ((Finset.univ.erase edgeFirst).erase edgeSecond : Finset (Fin 6)).Nonempty := by
    rw [← Finset.card_pos,
      Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hedge, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    norm_num
  have hneg : ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      design.weight other
        * (atomPairing design edgeFirst other * atomPairing design other edgeSecond) < 0 := by
    refine Finset.sum_neg (fun other hother => ?_) hnonempty
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hother
    obtain ⟨hotherSecond, hotherFirst⟩ := hother
    have hstar := neg_atomPairing_mul_of_tripleParity_eq_neg_one_of_orthogonalEdge design hzero
      (hstarFirst other hotherFirst hotherSecond) (hstarSecond other hotherFirst hotherSecond)
      (hincoherent other hotherFirst hotherSecond)
    rw [atomPairing_comm design other edgeSecond]
    exact mul_neg_of_pos_of_neg (design.weight_pos other) hstar
  rw [sum_erasePair_eq_zero_of_atomPairing_eq_zero design hedge hzero] at hneg
  exact lt_irrefl 0 hneg

namespace SixThreeCrux

variable (crux : SixThreeCrux)

/-- **THE RESIDUAL, FOR X7 AND FOR ANY LATER CAMPAIGN.**  A `(6,3)` crux with
nonvanishing pairings has its two-graph inside the 842-element
`Gtz.residualSectors`.  The set is NOT empty, and the module docstring says in
detail why no further sign-layer argument empties it: all three levers are proved
above, and each of the eight surviving isomorphism classes is realised by an
explicit design. -/
theorem linkWord_mem_residualSectors
    (hnonzero : ∀ first second : Fin 6, first ≠ second →
      atomPairing crux.design first second ≠ 0) :
    linkWordOf crux.design ∈ residualSectors :=
  linkWordOf_mem_residualSectors crux.design hnonzero

/-- The decode is faithful at a crux: the sector says INCOHERENT exactly where the
design does.  Consumers of `Gtz.SixThreeCrux.linkWord_mem_residualSectors` read the
pattern through this. -/
theorem tripleParity_eq_neg_one_iff_sectorIncoherent (first second third : Fin 6) :
    tripleParity crux.design first second third = -1 ↔
      sectorIncoherent (linkWordOf crux.design) first second third = true := by
  rw [sectorIncoherent_linkWordOf, decide_eq_true_eq]

end SixThreeCrux

end Gtz
