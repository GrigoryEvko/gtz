/-
# OVERLAP PATTERNS OF A THREE-MEMBER ACTIVE FAMILY AT `(6,3)` — and the `(7,3)` path

`Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily` put a floor of THREE under the
argmax family of a `(6,3)` crux.  This file classifies what three covering triples of
six atoms can look like, welds the classification onto that floor, and reads off the
private-atom structure each pattern forces.

## The classification

Three DISTINCT triples of six atoms whose union is everything satisfy the three-set
inclusion-exclusion identity

    `|A∩B| + |A∩C| + |B∩C| = 3 + |A∩B∩C|` ,

and no pairwise overlap can reach three, since equal cards make a full overlap an
equality of blocks.  Those two facts alone leave exactly three shapes:

    TRIANGLE   pairwise overlaps `1,1,1`, empty core       private parts `1,1,1`
    CHAIN      pairwise overlaps `2,1,0`, empty core       private parts `0,1,2`
    STAR       pairwise overlaps `2,1,1`, core one atom    private parts `1,1,2`

`overlapPattern_trichotomy_sixThree` is the disjunction, stated in ordering-free
invariants — the core cardinality, the overlap total, and whether some pair is
disjoint — so that no relabelling is needed to apply it.

Two readings make the outer branches concrete.  `eq_compl_of_card_inter_eq_zero_sixThree`
says THE CHAIN IS EXACTLY A COMPLEMENTARY PAIR PLUS A THIRD BLOCK: a disjoint pair of
triples in six atoms are each other's complement.  `hasSaturatedAtom_triple_iff` says
THE STAR IS EXACTLY SATURATION: the core is the set of atoms lying in every member, so
the third branch is `Gtz.HasSaturatedAtom` of the family.

## The private-atom structure, and the identity behind it

An atom is PRIVATE to a block when it lies in that block and no other.  Splitting each
block against the union of the other two gives, for every block,

    `|private| + |A∩B| + |A∩C| = 3 + |A∩B∩C|` ,

and summing the three copies against the classification identity yields

    `TOTAL PRIVATE MASS = TOTAL OVERLAP MASS = 3 + |A∩B∩C|`

(`card_privateParts_eq_pairwiseOverlapSum_sixThree`).  Both sides are `3` at the two
core-free patterns and `4` at the star.  Per pattern the private counts are the table
above; in particular EVERY pattern has a block with a nonempty private part, which is
what makes `Gtz.Quantitative.PrivateAtomLocalisation` applicable at all —
`private_of_mem_blockPrivatePart_of_isActiveFamily` is the bridge from the combinatorial
notion used here to the quantifier that file's hypotheses take.

## Which side each kill lives on — READ THIS BEFORE CITING ANYTHING BELOW

THE STAR IS NOT EXCLUDED ON THE CHART SIDE.  The chart-side saturation law shipped in
`Gtz.Quantitative.ChartDisjointBlockExclusion` is an EQUATION, not an exclusion: a
saturated atom weighs exactly `-chartObjective`.  That is landed here as
`SixThreeCrux.weight_eq_neg_chartObjective_of_starPattern`, and it excludes nothing —
six weights at or above `-chartObjective` summing to one are consistent for every value
in the window.  So the crux-side statement keeps the star as an explicit third disjunct.

ON THE QUADRIC SIDE THE STAR DIES BELOW ONE, because `Gtz.HasSaturatedAtom` is exactly
what `Gtz.one_le_value_of_hasSaturatedAtom_of_isActiveFamily` consumes.  Hence
`triangle_or_chain_of_isActiveFamily_of_value_lt_one_sixThree`: a below-one quadric
active family of three covering triples is a TRIANGLE or a CHAIN.  The two sides are
NOT interchangeable — a `Gtz.SixThreeCrux` carries `Gtz.IsChartStationaryData`, never
`Gtz.IsQuadricStationaryData`, so the quadric statements here do not apply to a crux.

## The `(7,3)` analogue

Seven atoms change the identity to `|A∩B| + |A∩C| + |B∩C| = 2 + |A∩B∩C|`, and the
shapes become PATH `1,1,0`, SPLIT `2,0,0`, and CORE `1,1,1` with a saturated atom.
Both outer shapes die below one on the quadric side and for DIFFERENT reasons: the
split's third block is disjoint from both others, hence an isolated block, so
`Gtz.card_le_value_of_isIsolatedActiveBlock` forces `3 ≤ value`; the core is saturated,
so the same filter as at `(6,3)` forces `1 ≤ value`.  What survives is
`pathPattern_of_isActiveFamily_of_value_lt_one_sevenThree` — THE PATH CLASSIFICATION
that the header of `Gtz.Quantitative.PrivateAtomLocalisation` records as dropped.  It is
recovered here because the version dropped there additionally assumed a nonempty private
part, and it is the PATTERN, not the privacy, that the combinatorics decides.

## What is NOT proved here, and is not claimed

* NOT a chart-side saturation exclusion.  None exists in the repository; the header of
  `Gtz.Quantitative.ClassRouteCost` says so in terms, and nothing here changes that.
* NOT any exclusion of the triangle or the chain, on either side.
* NOT non-vacuity of the below-one quadric statements.  The header of
  `Gtz.Quantitative.PrivateAtomLocalisation` records, as a verified-but-unlanded fact,
  that a nonempty private part already forces `1 ≤ value` — and every pattern here has
  one.  If that is right then the three-member below-one hypothesis is contradictory and
  the quadric corollaries below are vacuously true.  They are landed because the
  CLASSIFICATION is not vacuous and because the excluding step is a genuine citation;
  a successor who lands the sharp localisation should mark them so.
* NOT anything about the argmax family beyond three members.  Three distinct members of
  a LARGER family need not cover, and then only the unconditional floor
  `SixThreeCrux.le_pairwiseOverlapSum_chartArgmaxFamily` survives.
-/
import Mathlib
import Gtz.Quantitative.ChartDisjointBlockExclusion
import Gtz.Quantitative.ClassRouteCost
import Gtz.Quantitative.PrivateAtomLocalisation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## Three-set inclusion-exclusion -/

/-- The total pairwise overlap of three blocks. -/
def pairwiseOverlapSum (firstBlock secondBlock thirdBlock : Finset (Fin size)) : ℕ :=
  (firstBlock ∩ secondBlock).card + (firstBlock ∩ thirdBlock).card
    + (secondBlock ∩ thirdBlock).card

/-- **THREE-SET INCLUSION-EXCLUSION.**  Union plus pairwise overlaps equals total plus
core.  Proved by three applications of the two-set identity, distributing the outer
intersection over the inner union and recognising the resulting meet as the core. -/
theorem card_union_three_add_pairwiseOverlapSum
    (firstBlock secondBlock thirdBlock : Finset (Fin size)) :
    (firstBlock ∪ secondBlock ∪ thirdBlock).card
        + pairwiseOverlapSum firstBlock secondBlock thirdBlock
      = firstBlock.card + secondBlock.card + thirdBlock.card
        + (firstBlock ∩ secondBlock ∩ thirdBlock).card := by
  classical
  have hdistribute : (firstBlock ∪ secondBlock) ∩ thirdBlock
      = firstBlock ∩ thirdBlock ∪ secondBlock ∩ thirdBlock :=
    Finset.union_inter_distrib_right firstBlock secondBlock thirdBlock
  have hmeet : (firstBlock ∩ thirdBlock) ∩ (secondBlock ∩ thirdBlock)
      = firstBlock ∩ secondBlock ∩ thirdBlock := by
    ext atomIndex
    simp only [Finset.mem_inter]
    tauto
  have houter := Finset.card_union_add_card_inter (firstBlock ∪ secondBlock) thirdBlock
  have hinner := Finset.card_union_add_card_inter firstBlock secondBlock
  have hcross := Finset.card_union_add_card_inter (firstBlock ∩ thirdBlock)
    (secondBlock ∩ thirdBlock)
  rw [hdistribute] at houter
  rw [hmeet] at hcross
  rw [pairwiseOverlapSum]
  omega

/-- **DISTINCT EQUAL-CARD BLOCKS CANNOT OVERLAP FULLY.**  A full overlap would make the
intersection equal to the first block and hence contain it in the second, and equal
cardinalities then force equality of the blocks. -/
theorem card_inter_lt_of_card_eq_of_ne {firstBlock secondBlock : Finset (Fin size)} {rank : ℕ}
    (hfirst : firstBlock.card = rank) (hsecond : secondBlock.card = rank)
    (hne : firstBlock ≠ secondBlock) :
    (firstBlock ∩ secondBlock).card < rank := by
  classical
  have hsubset : firstBlock ∩ secondBlock ⊆ firstBlock := Finset.inter_subset_left
  have hle : (firstBlock ∩ secondBlock).card ≤ rank := hfirst ▸ Finset.card_le_card hsubset
  rcases Nat.lt_or_ge (firstBlock ∩ secondBlock).card rank with hlt | hge
  · exact hlt
  · exfalso
    have hmeetEq : firstBlock ∩ secondBlock = firstBlock :=
      Finset.eq_of_subset_of_card_le hsubset (by omega)
    have hcontained : firstBlock ⊆ secondBlock := by
      rw [← hmeetEq]; exact Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le hcontained (by omega))

/-- The core sits inside the first pairwise overlap. -/
theorem card_inter_three_le_first (firstBlock secondBlock thirdBlock : Finset (Fin size)) :
    (firstBlock ∩ secondBlock ∩ thirdBlock).card ≤ (firstBlock ∩ secondBlock).card :=
  Finset.card_le_card Finset.inter_subset_left

/-- The core sits inside the second pairwise overlap. -/
theorem card_inter_three_le_second (firstBlock secondBlock thirdBlock : Finset (Fin size)) :
    (firstBlock ∩ secondBlock ∩ thirdBlock).card ≤ (firstBlock ∩ thirdBlock).card := by
  refine Finset.card_le_card fun atomIndex hmem => ?_
  simp only [Finset.mem_inter] at hmem ⊢
  exact ⟨hmem.1.1, hmem.2⟩

/-- The core sits inside the third pairwise overlap. -/
theorem card_inter_three_le_third (firstBlock secondBlock thirdBlock : Finset (Fin size)) :
    (firstBlock ∩ secondBlock ∩ thirdBlock).card ≤ (secondBlock ∩ thirdBlock).card := by
  refine Finset.card_le_card fun atomIndex hmem => ?_
  simp only [Finset.mem_inter] at hmem ⊢
  exact ⟨hmem.1.2, hmem.2⟩

/-! ## Private parts -/

/-- The atoms of the FIRST block that lie in neither of the other two. -/
def blockPrivatePart (firstBlock secondBlock thirdBlock : Finset (Fin size)) :
    Finset (Fin size) :=
  firstBlock \ (secondBlock ∪ thirdBlock)

/-- **THE SPLIT OF A BLOCK AGAINST THE OTHER TWO.**  Private count plus the block's two
pairwise overlaps equals its own card plus the core.  Two-set inclusion-exclusion inside
the block, with the two traces meeting in the core. -/
theorem card_blockPrivatePart_add_pairwise
    (firstBlock secondBlock thirdBlock : Finset (Fin size)) :
    (blockPrivatePart firstBlock secondBlock thirdBlock).card
        + ((firstBlock ∩ secondBlock).card + (firstBlock ∩ thirdBlock).card)
      = firstBlock.card + (firstBlock ∩ secondBlock ∩ thirdBlock).card := by
  classical
  have hdistribute : firstBlock ∩ (secondBlock ∪ thirdBlock)
      = firstBlock ∩ secondBlock ∪ firstBlock ∩ thirdBlock :=
    Finset.inter_union_distrib_left firstBlock secondBlock thirdBlock
  have hmeet : (firstBlock ∩ secondBlock) ∩ (firstBlock ∩ thirdBlock)
      = firstBlock ∩ secondBlock ∩ thirdBlock := by
    ext atomIndex
    simp only [Finset.mem_inter]
    tauto
  have hsplit := Finset.card_inter_add_card_sdiff firstBlock (secondBlock ∪ thirdBlock)
  have hcross := Finset.card_union_add_card_inter (firstBlock ∩ secondBlock)
    (firstBlock ∩ thirdBlock)
  rw [hdistribute] at hsplit
  rw [hmeet] at hcross
  rw [blockPrivatePart]
  omega

/-- The same split at the SECOND block, in the fixed pairwise vocabulary. -/
theorem card_blockPrivatePart_add_pairwise_second
    (firstBlock secondBlock thirdBlock : Finset (Fin size)) :
    (blockPrivatePart secondBlock firstBlock thirdBlock).card
        + ((firstBlock ∩ secondBlock).card + (secondBlock ∩ thirdBlock).card)
      = secondBlock.card + (firstBlock ∩ secondBlock ∩ thirdBlock).card := by
  classical
  have hbase := card_blockPrivatePart_add_pairwise secondBlock firstBlock thirdBlock
  have hswapPair : secondBlock ∩ firstBlock = firstBlock ∩ secondBlock := Finset.inter_comm _ _
  rw [hswapPair] at hbase
  omega

/-- The same split at the THIRD block, in the fixed pairwise vocabulary. -/
theorem card_blockPrivatePart_add_pairwise_third
    (firstBlock secondBlock thirdBlock : Finset (Fin size)) :
    (blockPrivatePart thirdBlock firstBlock secondBlock).card
        + ((firstBlock ∩ thirdBlock).card + (secondBlock ∩ thirdBlock).card)
      = thirdBlock.card + (firstBlock ∩ secondBlock ∩ thirdBlock).card := by
  classical
  have hbase := card_blockPrivatePart_add_pairwise thirdBlock firstBlock secondBlock
  have hswapFirst : thirdBlock ∩ firstBlock = firstBlock ∩ thirdBlock := Finset.inter_comm _ _
  have hswapSecond : thirdBlock ∩ secondBlock = secondBlock ∩ thirdBlock := Finset.inter_comm _ _
  have hswapTriple : firstBlock ∩ thirdBlock ∩ secondBlock
      = firstBlock ∩ secondBlock ∩ thirdBlock := by
    ext atomIndex
    simp only [Finset.mem_inter]
    tauto
  rw [hswapFirst, hswapSecond, hswapTriple] at hbase
  omega

/-! ## Saturation of a three-member family -/

/-- **SATURATION IS THE CORE.**  An atom lying in every member of `{A, B, C}` is exactly
an atom of `A ∩ B ∩ C`, so the star branch of the classification below IS
`Gtz.HasSaturatedAtom`, the predicate the saturated-atom filters consume. -/
theorem hasSaturatedAtom_triple_iff (firstBlock secondBlock thirdBlock : Finset (Fin size)) :
    HasSaturatedAtom ({firstBlock, secondBlock, thirdBlock} : Finset (Finset (Fin size)))
      ↔ (firstBlock ∩ secondBlock ∩ thirdBlock).Nonempty := by
  classical
  constructor
  · rintro ⟨atomIndex, hall⟩
    refine ⟨atomIndex, ?_⟩
    simp only [Finset.mem_inter]
    exact ⟨⟨hall firstBlock (by simp), hall secondBlock (by simp)⟩, hall thirdBlock (by simp)⟩
  · rintro ⟨atomIndex, hmem⟩
    simp only [Finset.mem_inter] at hmem
    refine ⟨atomIndex, fun chosenSubset hchosen => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hchosen
    rcases hchosen with hone | htwo | hthree
    · exact hone ▸ hmem.1.1
    · exact htwo ▸ hmem.1.2
    · exact hthree ▸ hmem.2

/-! ## The `(6,3)` classification -/

/-- **THE CLASSIFICATION IDENTITY AT `(6,3)`.**  Covering pins the overlap total to
`3 + core`. -/
theorem pairwiseOverlapSum_eq_of_covering_sixThree
    {firstBlock secondBlock thirdBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ) :
    pairwiseOverlapSum firstBlock secondBlock thirdBlock
      = 3 + (firstBlock ∩ secondBlock ∩ thirdBlock).card := by
  have hie := card_union_three_add_pairwiseOverlapSum firstBlock secondBlock thirdBlock
  rw [hcover, Finset.card_univ, Fintype.card_fin] at hie
  omega

/-- **THE UNCONDITIONAL OVERLAP FLOOR AT `(6,3)`.**  Three triples cannot spread over six
atoms without a total pairwise overlap of at least `3 + core`, whether or not they cover.
This is the only part of the classification that survives inside a LARGER family, where
three chosen members need not cover. -/
theorem le_pairwiseOverlapSum_sixThree {firstBlock secondBlock thirdBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3)
    (hthird : thirdBlock.card = 3) :
    3 + (firstBlock ∩ secondBlock ∩ thirdBlock).card
      ≤ pairwiseOverlapSum firstBlock secondBlock thirdBlock := by
  have hie := card_union_three_add_pairwiseOverlapSum firstBlock secondBlock thirdBlock
  have hbound : (firstBlock ∪ secondBlock ∪ thirdBlock).card ≤ 6 := by
    have hle := Finset.card_le_univ (firstBlock ∪ secondBlock ∪ thirdBlock)
    rw [Fintype.card_fin] at hle
    exact hle
  omega

/-- **THE CORE OF THREE COVERING TRIPLES HOLDS AT MOST ONE ATOM.**  A core of two would
force every pairwise overlap to be at least two and at most two, hence a total of six
against the identity's five. -/
theorem card_inter_three_le_one_sixThree {firstBlock secondBlock thirdBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hfirstSecond : firstBlock ≠ secondBlock) (hfirstThird : firstBlock ≠ thirdBlock)
    (hsecondThird : secondBlock ≠ thirdBlock)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ) :
    (firstBlock ∩ secondBlock ∩ thirdBlock).card ≤ 1 := by
  have hsum := pairwiseOverlapSum_eq_of_covering_sixThree hfirst hsecond hthird hcover
  rw [pairwiseOverlapSum] at hsum
  have hboundFirstSecond := card_inter_lt_of_card_eq_of_ne hfirst hsecond hfirstSecond
  have hboundFirstThird := card_inter_lt_of_card_eq_of_ne hfirst hthird hfirstThird
  have hboundSecondThird := card_inter_lt_of_card_eq_of_ne hsecond hthird hsecondThird
  have hcoreFirst := card_inter_three_le_first firstBlock secondBlock thirdBlock
  have hcoreSecond := card_inter_three_le_second firstBlock secondBlock thirdBlock
  have hcoreThird := card_inter_three_le_third firstBlock secondBlock thirdBlock
  omega

/-- **THE TRICHOTOMY.**  Three distinct triples covering six atoms form a TRIANGLE
(pairwise overlaps `1,1,1`, empty core), a CHAIN (empty core, total three, some pair
disjoint) or a STAR (core one atom, total four).  Every clause is an ordering-free
invariant, so no relabelling is needed at the point of use.

The proof is arithmetic: the identity `total = 3 + core`, the bound `overlap < 3` at each
distinct pair, and `core ≤ overlap` at each pair, leave `omega` no room. -/
theorem overlapPattern_trichotomy_sixThree {firstBlock secondBlock thirdBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hfirstSecond : firstBlock ≠ secondBlock) (hfirstThird : firstBlock ≠ thirdBlock)
    (hsecondThird : secondBlock ≠ thirdBlock)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ) :
    ((firstBlock ∩ secondBlock).card = 1 ∧ (firstBlock ∩ thirdBlock).card = 1
        ∧ (secondBlock ∩ thirdBlock).card = 1
        ∧ (firstBlock ∩ secondBlock ∩ thirdBlock).card = 0)
      ∨ ((firstBlock ∩ secondBlock ∩ thirdBlock).card = 0
        ∧ pairwiseOverlapSum firstBlock secondBlock thirdBlock = 3
        ∧ ((firstBlock ∩ secondBlock).card = 0 ∨ (firstBlock ∩ thirdBlock).card = 0
          ∨ (secondBlock ∩ thirdBlock).card = 0))
      ∨ ((firstBlock ∩ secondBlock ∩ thirdBlock).card = 1
        ∧ pairwiseOverlapSum firstBlock secondBlock thirdBlock = 4) := by
  have hsum := pairwiseOverlapSum_eq_of_covering_sixThree hfirst hsecond hthird hcover
  rw [pairwiseOverlapSum] at hsum ⊢
  have hboundFirstSecond := card_inter_lt_of_card_eq_of_ne hfirst hsecond hfirstSecond
  have hboundFirstThird := card_inter_lt_of_card_eq_of_ne hfirst hthird hfirstThird
  have hboundSecondThird := card_inter_lt_of_card_eq_of_ne hsecond hthird hsecondThird
  have hcoreFirst := card_inter_three_le_first firstBlock secondBlock thirdBlock
  have hcoreSecond := card_inter_three_le_second firstBlock secondBlock thirdBlock
  have hcoreThird := card_inter_three_le_third firstBlock secondBlock thirdBlock
  omega

/-- **THE CHAIN'S NUMBERS.**  Once one pair is disjoint the other two overlaps are two
and one, in one order or the other; which of the two carries the double overlap is not
determined by the hypotheses and is left as the disjunction it is. -/
theorem card_inter_eq_of_disjointPair_sixThree
    {firstBlock secondBlock thirdBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hfirstSecond : firstBlock ≠ secondBlock) (hfirstThird : firstBlock ≠ thirdBlock)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ)
    (hdisjoint : (secondBlock ∩ thirdBlock).card = 0) :
    (firstBlock ∩ secondBlock ∩ thirdBlock).card = 0
      ∧ ((firstBlock ∩ secondBlock).card = 2 ∧ (firstBlock ∩ thirdBlock).card = 1
        ∨ (firstBlock ∩ secondBlock).card = 1 ∧ (firstBlock ∩ thirdBlock).card = 2) := by
  have hsum := pairwiseOverlapSum_eq_of_covering_sixThree hfirst hsecond hthird hcover
  rw [pairwiseOverlapSum] at hsum
  have hboundFirstSecond := card_inter_lt_of_card_eq_of_ne hfirst hsecond hfirstSecond
  have hboundFirstThird := card_inter_lt_of_card_eq_of_ne hfirst hthird hfirstThird
  have hcoreThird := card_inter_three_le_third firstBlock secondBlock thirdBlock
  omega

/-- **THE CHAIN IS A COMPLEMENTARY PAIR.**  Two disjoint triples of six atoms are each
other's complement, by `Gtz.eq_compl_of_disjoint_of_card_add_card_eq_size`.  So the chain
branch says: the family contains a complementary pair, plus one further block meeting
both. -/
theorem eq_compl_of_card_inter_eq_zero_sixThree {secondBlock thirdBlock : Finset (Fin 6)}
    (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hmeet : (secondBlock ∩ thirdBlock).card = 0) :
    thirdBlock = secondBlockᶜ := by
  classical
  have hdisjoint : Disjoint secondBlock thirdBlock :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hmeet)
  exact eq_compl_of_disjoint_of_card_add_card_eq_size hdisjoint (by omega)

/-! ## Private counts per pattern -/

/-- **PRIVATE MASS EQUALS OVERLAP MASS.**  Summing the three block splits against the
classification identity: total private atoms `= 3 + core =` total pairwise overlap.
Three at both core-free patterns, four at the star. -/
theorem card_privateParts_eq_pairwiseOverlapSum_sixThree
    {firstBlock secondBlock thirdBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ) :
    (blockPrivatePart firstBlock secondBlock thirdBlock).card
        + (blockPrivatePart secondBlock firstBlock thirdBlock).card
        + (blockPrivatePart thirdBlock firstBlock secondBlock).card
      = pairwiseOverlapSum firstBlock secondBlock thirdBlock := by
  have hsum := pairwiseOverlapSum_eq_of_covering_sixThree hfirst hsecond hthird hcover
  rw [pairwiseOverlapSum] at hsum ⊢
  have hsplitFirst := card_blockPrivatePart_add_pairwise firstBlock secondBlock thirdBlock
  have hsplitSecond := card_blockPrivatePart_add_pairwise_second firstBlock secondBlock thirdBlock
  have hsplitThird := card_blockPrivatePart_add_pairwise_third firstBlock secondBlock thirdBlock
  omega

/-- **THE TRIANGLE'S PRIVATE COUNTS ARE `1,1,1`.**  Every block keeps exactly one atom to
itself, the other two being its meeting points with the other blocks. -/
theorem card_blockPrivatePart_of_trianglePattern_sixThree
    {firstBlock secondBlock thirdBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hfirstSecond : (firstBlock ∩ secondBlock).card = 1)
    (hfirstThird : (firstBlock ∩ thirdBlock).card = 1)
    (hsecondThird : (secondBlock ∩ thirdBlock).card = 1)
    (hcore : (firstBlock ∩ secondBlock ∩ thirdBlock).card = 0) :
    (blockPrivatePart firstBlock secondBlock thirdBlock).card = 1
      ∧ (blockPrivatePart secondBlock firstBlock thirdBlock).card = 1
      ∧ (blockPrivatePart thirdBlock firstBlock secondBlock).card = 1 := by
  have hsplitFirst := card_blockPrivatePart_add_pairwise firstBlock secondBlock thirdBlock
  have hsplitSecond := card_blockPrivatePart_add_pairwise_second firstBlock secondBlock thirdBlock
  have hsplitThird := card_blockPrivatePart_add_pairwise_third firstBlock secondBlock thirdBlock
  omega

/-- **THE CHAIN'S PRIVATE COUNTS ARE `0,1,2`.**  The block meeting both others has NO
private atom at all; the doubly-met block keeps one; the block disjoint from it keeps two.
The private multiset is what separates the chain from the star, whose totals differ only
in the core. -/
theorem card_blockPrivatePart_of_chainPattern_sixThree
    {firstBlock secondBlock thirdBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hfirstSecond : (firstBlock ∩ secondBlock).card = 2)
    (hfirstThird : (firstBlock ∩ thirdBlock).card = 1)
    (hsecondThird : (secondBlock ∩ thirdBlock).card = 0)
    (hcore : (firstBlock ∩ secondBlock ∩ thirdBlock).card = 0) :
    (blockPrivatePart firstBlock secondBlock thirdBlock).card = 0
      ∧ (blockPrivatePart secondBlock firstBlock thirdBlock).card = 1
      ∧ (blockPrivatePart thirdBlock firstBlock secondBlock).card = 2 := by
  have hsplitFirst := card_blockPrivatePart_add_pairwise firstBlock secondBlock thirdBlock
  have hsplitSecond := card_blockPrivatePart_add_pairwise_second firstBlock secondBlock thirdBlock
  have hsplitThird := card_blockPrivatePart_add_pairwise_third firstBlock secondBlock thirdBlock
  omega

/-- **THE STAR'S PRIVATE COUNTS ARE `1,1,2`.**  The two blocks sharing the extra atom keep
one each, and the block meeting the others only at the core keeps two. -/
theorem card_blockPrivatePart_of_starPattern_sixThree
    {firstBlock secondBlock thirdBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hfirstSecond : (firstBlock ∩ secondBlock).card = 2)
    (hfirstThird : (firstBlock ∩ thirdBlock).card = 1)
    (hsecondThird : (secondBlock ∩ thirdBlock).card = 1)
    (hcore : (firstBlock ∩ secondBlock ∩ thirdBlock).card = 1) :
    (blockPrivatePart firstBlock secondBlock thirdBlock).card = 1
      ∧ (blockPrivatePart secondBlock firstBlock thirdBlock).card = 1
      ∧ (blockPrivatePart thirdBlock firstBlock secondBlock).card = 2 := by
  have hsplitFirst := card_blockPrivatePart_add_pairwise firstBlock secondBlock thirdBlock
  have hsplitSecond := card_blockPrivatePart_add_pairwise_second firstBlock secondBlock thirdBlock
  have hsplitThird := card_blockPrivatePart_add_pairwise_third firstBlock secondBlock thirdBlock
  omega

/-- **EVERY PATTERN HAS A PRIVATE ATOM.**  Private mass equals overlap mass, which is at
least three, so some block keeps an atom to itself.  This is what makes the private-atom
kit of `Gtz.Quantitative.PrivateAtomLocalisation` applicable to a three-member covering
family at all — and, if that file's unlanded sharp localisation is right, what makes the
below-one hypothesis contradictory. -/
theorem exists_nonempty_blockPrivatePart_sixThree
    {firstBlock secondBlock thirdBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ) :
    (blockPrivatePart firstBlock secondBlock thirdBlock).Nonempty
      ∨ (blockPrivatePart secondBlock firstBlock thirdBlock).Nonempty
      ∨ (blockPrivatePart thirdBlock firstBlock secondBlock).Nonempty := by
  classical
  have htotal := card_privateParts_eq_pairwiseOverlapSum_sixThree hfirst hsecond hthird hcover
  have hfloor := le_pairwiseOverlapSum_sixThree hfirst hsecond hthird
  by_contra hnone
  simp only [not_or, Finset.not_nonempty_iff_eq_empty] at hnone
  rw [hnone.1, hnone.2.1, hnone.2.2, Finset.card_empty] at htotal
  omega

/-- Private parts of distinct blocks are disjoint: an atom private to the first block lies
in no other block, so in particular not in the second. -/
theorem disjoint_blockPrivatePart_first_second
    (firstBlock secondBlock thirdBlock : Finset (Fin size)) :
    Disjoint (blockPrivatePart firstBlock secondBlock thirdBlock)
      (blockPrivatePart secondBlock firstBlock thirdBlock) := by
  classical
  refine Finset.disjoint_left.mpr fun atomIndex hfirst hsecond => ?_
  rw [blockPrivatePart, Finset.mem_sdiff, Finset.mem_union] at hfirst
  rw [blockPrivatePart, Finset.mem_sdiff] at hsecond
  exact hfirst.2 (Or.inl hsecond.1)

/-- The first and third private parts are disjoint. -/
theorem disjoint_blockPrivatePart_first_third
    (firstBlock secondBlock thirdBlock : Finset (Fin size)) :
    Disjoint (blockPrivatePart firstBlock secondBlock thirdBlock)
      (blockPrivatePart thirdBlock firstBlock secondBlock) := by
  classical
  refine Finset.disjoint_left.mpr fun atomIndex hfirst hthird => ?_
  rw [blockPrivatePart, Finset.mem_sdiff, Finset.mem_union] at hfirst
  rw [blockPrivatePart, Finset.mem_sdiff] at hthird
  exact hfirst.2 (Or.inr hthird.1)

/-- The second and third private parts are disjoint. -/
theorem disjoint_blockPrivatePart_second_third
    (firstBlock secondBlock thirdBlock : Finset (Fin size)) :
    Disjoint (blockPrivatePart secondBlock firstBlock thirdBlock)
      (blockPrivatePart thirdBlock firstBlock secondBlock) := by
  classical
  refine Finset.disjoint_left.mpr fun atomIndex hsecond hthird => ?_
  rw [blockPrivatePart, Finset.mem_sdiff, Finset.mem_union] at hsecond
  rw [blockPrivatePart, Finset.mem_sdiff] at hthird
  exact hsecond.2 (Or.inr hthird.1)

/-- **THE PRIVATE-MASS IDENTITY AT THE LEVEL OF SETS.**  The three private parts are
pairwise disjoint, so their union has exactly the overlap total for its cardinality.  The
counting form `card_privateParts_eq_pairwiseOverlapSum_sixThree` is this statement with the
disjointness spent. -/
theorem card_union_blockPrivateParts_eq_pairwiseOverlapSum_sixThree
    {firstBlock secondBlock thirdBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ) :
    (blockPrivatePart firstBlock secondBlock thirdBlock
        ∪ blockPrivatePart secondBlock firstBlock thirdBlock
        ∪ blockPrivatePart thirdBlock firstBlock secondBlock).card
      = pairwiseOverlapSum firstBlock secondBlock thirdBlock := by
  classical
  have hinner := Finset.card_union_of_disjoint
    (disjoint_blockPrivatePart_first_second firstBlock secondBlock thirdBlock)
  have houterDisjoint : Disjoint (blockPrivatePart firstBlock secondBlock thirdBlock
      ∪ blockPrivatePart secondBlock firstBlock thirdBlock)
      (blockPrivatePart thirdBlock firstBlock secondBlock) :=
    Finset.disjoint_union_left.mpr
      ⟨disjoint_blockPrivatePart_first_third firstBlock secondBlock thirdBlock,
        disjoint_blockPrivatePart_second_third firstBlock secondBlock thirdBlock⟩
  rw [Finset.card_union_of_disjoint houterDisjoint, hinner,
    card_privateParts_eq_pairwiseOverlapSum_sixThree hfirst hsecond hthird hcover]

/-- **AT THE TRIANGLE THE PRIVATE ATOMS THEMSELVES FORM A TRIPLE.**  Core-free means
overlap total three, so the three private atoms — one per block — make up a three-element
set, which by coverage is exactly the complement of the set of meeting points.  The
triangle therefore splits the six atoms into two triples canonically, and neither is known
to be an argmax block. -/
theorem card_union_blockPrivateParts_of_trianglePattern_sixThree
    {firstBlock secondBlock thirdBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ)
    (hcore : (firstBlock ∩ secondBlock ∩ thirdBlock).card = 0) :
    (blockPrivatePart firstBlock secondBlock thirdBlock
        ∪ blockPrivatePart secondBlock firstBlock thirdBlock
        ∪ blockPrivatePart thirdBlock firstBlock secondBlock).card = 3 := by
  have hunion := card_union_blockPrivateParts_eq_pairwiseOverlapSum_sixThree hfirst hsecond hthird
    hcover
  have hsum := pairwiseOverlapSum_eq_of_covering_sixThree hfirst hsecond hthird hcover
  omega

/-! ## The bridge to the private-atom kit -/

section Bridge

variable {activeIndex : Type*} {activeSet : Finset activeIndex}
  {activeSubset : activeIndex → Finset (Fin size)}

/-- **THE MEMBERSHIP DISJUNCTION.**  An active label of a three-member family carries one
of the three named blocks.  Everything below consumes the family through this, never
through the `Finset` literal, so no permutation of the literal is ever needed. -/
theorem forall_eq_of_isActiveFamily_triple
    {firstBlock secondBlock thirdBlock : Finset (Fin size)}
    (hfamily : IsActiveFamily activeSet activeSubset
      ({firstBlock, secondBlock, thirdBlock} : Finset (Finset (Fin size))))
    (activeLabel : activeIndex) (hactive : activeLabel ∈ activeSet) :
    activeSubset activeLabel = firstBlock ∨ activeSubset activeLabel = secondBlock
      ∨ activeSubset activeLabel = thirdBlock := by
  classical
  have hchosen := mem_of_isActiveFamily hfamily hactive
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hchosen

/-- **A BLOCK DISJOINT FROM BOTH OTHERS IS ISOLATED.**  Stated against the membership
disjunction rather than the family literal, so that the three roles are interchangeable at
the point of use. -/
theorem isIsolatedActiveBlock_of_forall_eq_of_disjoint
    {firstBlock secondBlock thirdBlock : Finset (Fin size)}
    (hmembership : ∀ activeLabel ∈ activeSet,
      activeSubset activeLabel = firstBlock ∨ activeSubset activeLabel = secondBlock
        ∨ activeSubset activeLabel = thirdBlock)
    (hsecond : Disjoint firstBlock secondBlock) (hthird : Disjoint firstBlock thirdBlock) :
    IsIsolatedActiveBlock activeSet activeSubset firstBlock := by
  intro activeLabel hactive hne
  rcases hmembership activeLabel hactive with hone | htwo | hthree
  · exact absurd hone hne
  · exact htwo ▸ hsecond.symm
  · exact hthree ▸ hthird.symm

/-- **COMBINATORIAL PRIVACY IS THE KIT'S PRIVACY.**  When the active family is exactly
`{A, B, C}`, an atom of `A` lying in neither `B` nor `C` satisfies the quantifier that
`Gtz.blockClarkePairing_atom_eq_of_privateAtom` and its successors take: every active
subset containing it IS `A`.  Without this bridge the classification and the private-atom
kit never meet. -/
theorem private_of_mem_blockPrivatePart_of_isActiveFamily
    {firstBlock secondBlock thirdBlock : Finset (Fin size)}
    (hfamily : IsActiveFamily activeSet activeSubset
      ({firstBlock, secondBlock, thirdBlock} : Finset (Finset (Fin size))))
    {atomLabel : Fin size}
    (hprivate : atomLabel ∈ blockPrivatePart firstBlock secondBlock thirdBlock)
    (activeLabel : activeIndex) (hactive : activeLabel ∈ activeSet)
    (hmem : atomLabel ∈ activeSubset activeLabel) :
    activeSubset activeLabel = firstBlock := by
  classical
  rw [blockPrivatePart, Finset.mem_sdiff, Finset.mem_union] at hprivate
  have hchosen := mem_of_isActiveFamily hfamily hactive
  simp only [Finset.mem_insert, Finset.mem_singleton] at hchosen
  rcases hchosen with hone | htwo | hthree
  · exact hone
  · exact absurd (Or.inl (htwo ▸ hmem)) hprivate.2
  · exact absurd (Or.inr (hthree ▸ hmem)) hprivate.2

end Bridge

section QuadricConsequences

variable {atomCount : ℕ} {activeIndex : Type*} {design : WeightedDesign atomCount 3} {value : ℝ}
  {multiplierMatrix : Matrix (Fin 3) (Fin 3) ℝ} {activeSet : Finset activeIndex}
  {activeSubset : activeIndex → Finset (Fin atomCount)} {activeWeight : activeIndex → ℝ}
  {tightDir : activeIndex → (Fin 3 → ℝ)}

/-- **THE CROSS-MASS INEQUALITY AT A THREE-MEMBER FAMILY.**  The classification supplies
the private part; `Gtz.overlapAbsSum_ge_of_privatePart` supplies the inequality.  For any
set `P` of atoms private to the first block,

    `|P| (|P| - value)  <=  sum_{c in P} sum_{d in A \ P} |<g_d, g_c>|` ,

with no multiplier and no tight direction surviving in the conclusion.  Per pattern `|P|`
is read off the tables above: one at every block of a triangle, and two at the block
opposite the disjoint pair of a chain or at the core-only block of a star. -/
theorem overlapAbsSum_ge_of_isActiveFamily_triple
    (hdata : IsQuadricStationaryData design value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0)
    {firstBlock secondBlock thirdBlock privatePart : Finset (Fin atomCount)}
    (hfamily : IsActiveFamily activeSet activeSubset
      ({firstBlock, secondBlock, thirdBlock} : Finset (Finset (Fin atomCount))))
    (hsubset : privatePart ⊆ blockPrivatePart firstBlock secondBlock thirdBlock) :
    (privatePart.card : ℝ) * ((privatePart.card : ℝ) - value)
      ≤ ∑ atomLabel ∈ privatePart, ∑ otherAtom ∈ firstBlock \ privatePart,
          |design.atom otherAtom ⬝ᵥ design.atom atomLabel| := by
  classical
  have hinBlock : privatePart ⊆ firstBlock := fun atomLabel hatom =>
    (Finset.mem_sdiff.mp (hsubset hatom)).1
  exact overlapAbsSum_ge_of_privatePart hdata hvalueNe hinBlock
    fun atomLabel hatom activeLabel hactive hmem =>
      private_of_mem_blockPrivatePart_of_isActiveFamily hfamily (hsubset hatom) activeLabel
        hactive hmem

/-- **BELOW ONE, A THREE-MEMBER COVERING QUADRIC FAMILY AT `(6,3)` IS A TRIANGLE OR A
CHAIN.**  The star branch of the trichotomy is exactly `Gtz.HasSaturatedAtom`, which
`Gtz.one_le_value_of_hasSaturatedAtom_of_isActiveFamily` forbids below one.

THIS IS A QUADRIC-SIDE STATEMENT.  A `Gtz.SixThreeCrux` carries chart data, never
`Gtz.IsQuadricStationaryData`, so it does NOT apply there; the crux keeps the star as a
third disjunct.  See this file's header for the non-vacuity caveat. -/
theorem triangle_or_chain_of_isActiveFamily_of_value_lt_one_sixThree
    {design : WeightedDesign 6 3} {activeSubset : activeIndex → Finset (Fin 6)}
    (hdata : IsQuadricStationaryData design value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hbelowOne : value < 1)
    {firstBlock secondBlock thirdBlock : Finset (Fin 6)}
    (hfamily : IsActiveFamily activeSet activeSubset
      ({firstBlock, secondBlock, thirdBlock} : Finset (Finset (Fin 6))))
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hfirstSecond : firstBlock ≠ secondBlock) (hfirstThird : firstBlock ≠ thirdBlock)
    (hsecondThird : secondBlock ≠ thirdBlock)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ) :
    ((firstBlock ∩ secondBlock).card = 1 ∧ (firstBlock ∩ thirdBlock).card = 1
        ∧ (secondBlock ∩ thirdBlock).card = 1
        ∧ (firstBlock ∩ secondBlock ∩ thirdBlock).card = 0)
      ∨ ((firstBlock ∩ secondBlock ∩ thirdBlock).card = 0
        ∧ pairwiseOverlapSum firstBlock secondBlock thirdBlock = 3
        ∧ ((firstBlock ∩ secondBlock).card = 0 ∨ (firstBlock ∩ thirdBlock).card = 0
          ∨ (secondBlock ∩ thirdBlock).card = 0)) := by
  classical
  rcases overlapPattern_trichotomy_sixThree hfirst hsecond hthird hfirstSecond hfirstThird
    hsecondThird hcover with htriangle | hchain | hstar
  · exact Or.inl htriangle
  · exact Or.inr hchain
  · exfalso
    have hcore : (firstBlock ∩ secondBlock ∩ thirdBlock).Nonempty :=
      Finset.card_pos.mp (by omega)
    have hsaturated : HasSaturatedAtom
        ({firstBlock, secondBlock, thirdBlock} : Finset (Finset (Fin 6))) :=
      (hasSaturatedAtom_triple_iff firstBlock secondBlock thirdBlock).mpr hcore
    have hone := one_le_value_of_hasSaturatedAtom_of_isActiveFamily hdata hvalueNe hfamily
      hsaturated
    linarith

end QuadricConsequences

/-! ## The crux weld -/

/-- **A THREE-MEMBER ARGMAX FAMILY IS THREE DISTINCT COVERING TRIPLES.**  Membership
supplies the cards and coverage supplies the union, so the classification applies
verbatim.  Stated at a bare `Gtz.ChartPoint` with positive weights and global minimality,
which is strictly weaker than a crux. -/
theorem exists_triple_of_card_chartArgmaxFamily_eq_three (minimiser : ChartPoint 6 3)
    (hweightPos : ∀ atomIndex : Fin 6, 0 < minimiser.weight atomIndex)
    (hmin : ∀ point : ChartPoint 6 3, chartObjective minimiser ≤ chartObjective point)
    (hcard : (chartArgmaxFamily minimiser).card = 3) :
    ∃ firstBlock secondBlock thirdBlock : Finset (Fin 6),
      chartArgmaxFamily minimiser = {firstBlock, secondBlock, thirdBlock}
        ∧ firstBlock ≠ secondBlock ∧ firstBlock ≠ thirdBlock ∧ secondBlock ≠ thirdBlock
        ∧ firstBlock.card = 3 ∧ secondBlock.card = 3 ∧ thirdBlock.card = 3
        ∧ firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ := by
  classical
  obtain ⟨firstBlock, secondBlock, thirdBlock, hfirstSecond, hfirstThird, hsecondThird, hset⟩ :=
    Finset.card_eq_three.mp hcard
  have hfirstMem : firstBlock ∈ chartArgmaxFamily minimiser := by rw [hset]; simp
  have hsecondMem : secondBlock ∈ chartArgmaxFamily minimiser := by rw [hset]; simp
  have hthirdMem : thirdBlock ∈ chartArgmaxFamily minimiser := by rw [hset]; simp
  have hcover : firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ := by
    refine Finset.Subset.antisymm (Finset.subset_univ _) fun atomIndex _ => ?_
    obtain ⟨block, hblockMem, hatomMem⟩ :=
      exists_mem_chartArgmaxFamily_of_isMin minimiser hweightPos hmin atomIndex
    rw [hset] at hblockMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hblockMem
    simp only [Finset.mem_union]
    rcases hblockMem with hone | htwo | hthree
    · exact Or.inl (Or.inl (hone ▸ hatomMem))
    · exact Or.inl (Or.inr (htwo ▸ hatomMem))
    · exact Or.inr (hthree ▸ hatomMem)
  exact ⟨firstBlock, secondBlock, thirdBlock, hset, hfirstSecond, hfirstThird, hsecondThird,
    ((mem_chartArgmaxFamily_iff minimiser firstBlock).mp hfirstMem).1,
    ((mem_chartArgmaxFamily_iff minimiser secondBlock).mp hsecondMem).1,
    ((mem_chartArgmaxFamily_iff minimiser thirdBlock).mp hthirdMem).1, hcover⟩

namespace SixThreeCrux

variable (crux : SixThreeCrux)

/-- Every argmax block of a crux is a triple. -/
theorem card_eq_three_of_mem_chartArgmaxFamily {block : Finset (Fin 6)}
    (hmem : block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)) :
    block.card = 3 :=
  ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) block).mp hmem).1

/-- **THE UNCONDITIONAL OVERLAP FLOOR AT A CRUX.**  ANY three argmax triples — no
distinctness, no covering, no bound on the size of the family — carry a total pairwise
overlap of at least `3 + core`.  This is the part of the classification that survives when
the argmax family is larger than three. -/
theorem le_pairwiseOverlapSum_chartArgmaxFamily {firstBlock secondBlock thirdBlock :
    Finset (Fin 6)}
    (hfirstMem : firstBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hsecondMem : secondBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hthirdMem : thirdBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design)) :
    3 + (firstBlock ∩ secondBlock ∩ thirdBlock).card
      ≤ pairwiseOverlapSum firstBlock secondBlock thirdBlock :=
  le_pairwiseOverlapSum_sixThree (crux.card_eq_three_of_mem_chartArgmaxFamily hfirstMem)
    (crux.card_eq_three_of_mem_chartArgmaxFamily hsecondMem)
    (crux.card_eq_three_of_mem_chartArgmaxFamily hthirdMem)

/-- **THE CRUX CLASSIFICATION.**  When the argmax family of a `(6,3)` crux has exactly
three members they are three distinct covering triples, hence a TRIANGLE, a CHAIN or a
STAR — and the star is NOT excluded here, because the chart-side saturation law is an
equation rather than an exclusion.  See this file's header, and
`weight_eq_neg_chartObjective_of_starPattern` for what the star does force. -/
theorem exists_overlapPattern_of_card_chartArgmaxFamily_eq_three
    (hcard : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 3) :
    ∃ firstBlock secondBlock thirdBlock : Finset (Fin 6),
      chartArgmaxFamily (chartPointOfDesign crux.design)
          = {firstBlock, secondBlock, thirdBlock}
        ∧ firstBlock.card = 3 ∧ secondBlock.card = 3 ∧ thirdBlock.card = 3
        ∧ firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ
        ∧ (((firstBlock ∩ secondBlock).card = 1 ∧ (firstBlock ∩ thirdBlock).card = 1
              ∧ (secondBlock ∩ thirdBlock).card = 1
              ∧ (firstBlock ∩ secondBlock ∩ thirdBlock).card = 0)
          ∨ ((firstBlock ∩ secondBlock ∩ thirdBlock).card = 0
            ∧ pairwiseOverlapSum firstBlock secondBlock thirdBlock = 3
            ∧ ((firstBlock ∩ secondBlock).card = 0 ∨ (firstBlock ∩ thirdBlock).card = 0
              ∨ (secondBlock ∩ thirdBlock).card = 0))
          ∨ ((firstBlock ∩ secondBlock ∩ thirdBlock).card = 1
            ∧ pairwiseOverlapSum firstBlock secondBlock thirdBlock = 4)) := by
  obtain ⟨firstBlock, secondBlock, thirdBlock, hset, hfirstSecond, hfirstThird, hsecondThird,
    hfirst, hsecond, hthird, hcover⟩ :=
    exists_triple_of_card_chartArgmaxFamily_eq_three _ crux.weight_pos crux.isChartMinimiser hcard
  exact ⟨firstBlock, secondBlock, thirdBlock, hset, hfirst, hsecond, hthird, hcover,
    overlapPattern_trichotomy_sixThree hfirst hsecond hthird hfirstSecond hfirstThird
      hsecondThird hcover⟩

/-- **WHAT THE STAR FORCES AT A CRUX.**  A three-member argmax family with a nonempty core
has that core atom in every member, so the chart-side saturation law pins its weight to
`-chartObjective`.  RIGIDITY, NOT EXCLUSION: six weights at or above `-chartObjective`
summing to one are consistent for every value in the window, so this closes nothing.  The
counting companion `Gtz.SixThreeCrux.four_le_card_chartArgmaxFamily_of_saturatedPair` says
a three-member family has at most one such atom, which the trichotomy independently gives
as `core <= 1`. -/
theorem weight_eq_neg_chartObjective_of_starPattern
    {firstBlock secondBlock thirdBlock : Finset (Fin 6)}
    (hset : chartArgmaxFamily (chartPointOfDesign crux.design)
      = {firstBlock, secondBlock, thirdBlock})
    {atomIndex : Fin 6} (hcore : atomIndex ∈ firstBlock ∩ secondBlock ∩ thirdBlock) :
    crux.design.weight atomIndex = -chartObjective (chartPointOfDesign crux.design) := by
  classical
  refine crux.weight_eq_neg_chartObjective_of_saturatedAtom fun block hblockMem => ?_
  rw [hset] at hblockMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hblockMem
  simp only [Finset.mem_inter] at hcore
  rcases hblockMem with hone | htwo | hthree
  · exact hone ▸ hcore.1.1
  · exact htwo ▸ hcore.1.2
  · exact hthree ▸ hcore.2

/-- **WHAT THE CHAIN FORCES AT A CRUX.**  A disjoint pair among three argmax triples is a
COMPLEMENTARY pair: the two blocks are each other's complement and the third meets both.
Compare `Gtz.SixThreeCrux.exists_notDisjoint_mem_chartArgmaxFamily`, which forbids a block
disjoint from ALL the others — a complementary pair inside a three-member family is not
that, and is excluded by nothing shipped. -/
theorem eq_compl_of_chainPattern {secondBlock thirdBlock : Finset (Fin 6)}
    (hsecondMem : secondBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hthirdMem : thirdBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hmeet : (secondBlock ∩ thirdBlock).card = 0) :
    thirdBlock = secondBlockᶜ :=
  eq_compl_of_card_inter_eq_zero_sixThree
    (crux.card_eq_three_of_mem_chartArgmaxFamily hsecondMem)
    (crux.card_eq_three_of_mem_chartArgmaxFamily hthirdMem) hmeet

end SixThreeCrux

/-! ## The `(7,3)` analogue -/

/-- **THE CLASSIFICATION IDENTITY AT `(7,3)`.**  Seven atoms leave the overlap total at
`2 + core`, one less than at `(6,3)`. -/
theorem pairwiseOverlapSum_eq_of_covering_sevenThree
    {firstBlock secondBlock thirdBlock : Finset (Fin 7)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ) :
    pairwiseOverlapSum firstBlock secondBlock thirdBlock
      = 2 + (firstBlock ∩ secondBlock ∩ thirdBlock).card := by
  have hie := card_union_three_add_pairwiseOverlapSum firstBlock secondBlock thirdBlock
  rw [hcover, Finset.card_univ, Fintype.card_fin] at hie
  omega

/-- **THE `(7,3)` TRICHOTOMY.**  Three distinct triples covering seven atoms form a PATH
(overlaps `1,1,0`, empty core), a SPLIT (overlaps `2,0,0`, empty core — one block disjoint
from both others) or a CORE (overlaps `1,1,1` with a single common atom).  Stated so that
the SPLIT branch names the isolated block and the CORE branch names the saturation, which
are the two hypotheses the exclusions below consume. -/
theorem overlapPattern_trichotomy_sevenThree
    {firstBlock secondBlock thirdBlock : Finset (Fin 7)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hfirstSecond : firstBlock ≠ secondBlock) (hfirstThird : firstBlock ≠ thirdBlock)
    (hsecondThird : secondBlock ≠ thirdBlock)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ) :
    ((firstBlock ∩ secondBlock ∩ thirdBlock).card = 0
        ∧ pairwiseOverlapSum firstBlock secondBlock thirdBlock = 2
        ∧ (firstBlock ∩ secondBlock).card ≤ 1 ∧ (firstBlock ∩ thirdBlock).card ≤ 1
        ∧ (secondBlock ∩ thirdBlock).card ≤ 1)
      ∨ ((firstBlock ∩ secondBlock ∩ thirdBlock).card = 0
        ∧ ((firstBlock ∩ secondBlock).card = 0 ∧ (firstBlock ∩ thirdBlock).card = 0
          ∨ (firstBlock ∩ secondBlock).card = 0 ∧ (secondBlock ∩ thirdBlock).card = 0
          ∨ (firstBlock ∩ thirdBlock).card = 0 ∧ (secondBlock ∩ thirdBlock).card = 0))
      ∨ ((firstBlock ∩ secondBlock ∩ thirdBlock).card = 1
        ∧ (firstBlock ∩ secondBlock).card = 1 ∧ (firstBlock ∩ thirdBlock).card = 1
        ∧ (secondBlock ∩ thirdBlock).card = 1) := by
  have hsum := pairwiseOverlapSum_eq_of_covering_sevenThree hfirst hsecond hthird hcover
  rw [pairwiseOverlapSum] at hsum ⊢
  have hboundFirstSecond := card_inter_lt_of_card_eq_of_ne hfirst hsecond hfirstSecond
  have hboundFirstThird := card_inter_lt_of_card_eq_of_ne hfirst hthird hfirstThird
  have hboundSecondThird := card_inter_lt_of_card_eq_of_ne hsecond hthird hsecondThird
  have hcoreFirst := card_inter_three_le_first firstBlock secondBlock thirdBlock
  have hcoreSecond := card_inter_three_le_second firstBlock secondBlock thirdBlock
  have hcoreThird := card_inter_three_le_third firstBlock secondBlock thirdBlock
  omega

section SevenThreeQuadric

variable {activeIndex : Type*} {design : WeightedDesign 7 3} {value : ℝ}
  {multiplierMatrix : Matrix (Fin 3) (Fin 3) ℝ} {activeSet : Finset activeIndex}
  {activeSubset : activeIndex → Finset (Fin 7)} {activeWeight : activeIndex → ℝ}
  {tightDir : activeIndex → (Fin 3 → ℝ)}

/-- **THE PATH CLASSIFICATION AT `(7,3)`.**  Below one, a three-member covering quadric
active family at the frontier cell is a PATH: every pairwise overlap is at most one and
the core is empty.

The two other shapes die for DIFFERENT reasons.  The SPLIT has a block disjoint from both
others, hence isolated, and `Gtz.card_le_value_of_isIsolatedActiveBlock` forces
`3 <= value`.  The CORE is saturated, and
`Gtz.one_le_value_of_hasSaturatedAtom_of_isActiveFamily` forces `1 <= value`.

This is the classification the header of `Gtz.Quantitative.PrivateAtomLocalisation` records
as dropped.  It is recovered because the dropped version additionally assumed a nonempty
private part, and privacy is not what decides the pattern.  Its NON-VACUITY is still open —
see this file's header. -/
theorem pathPattern_of_isActiveFamily_of_value_lt_one_sevenThree
    (hdata : IsQuadricStationaryData design value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hbelowOne : value < 1)
    {firstBlock secondBlock thirdBlock : Finset (Fin 7)}
    (hfamily : IsActiveFamily activeSet activeSubset
      ({firstBlock, secondBlock, thirdBlock} : Finset (Finset (Fin 7))))
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3) (hthird : thirdBlock.card = 3)
    (hfirstSecond : firstBlock ≠ secondBlock) (hfirstThird : firstBlock ≠ thirdBlock)
    (hsecondThird : secondBlock ≠ thirdBlock)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock = Finset.univ) :
    (firstBlock ∩ secondBlock ∩ thirdBlock).card = 0
      ∧ pairwiseOverlapSum firstBlock secondBlock thirdBlock = 2
      ∧ (firstBlock ∩ secondBlock).card ≤ 1 ∧ (firstBlock ∩ thirdBlock).card ≤ 1
      ∧ (secondBlock ∩ thirdBlock).card ≤ 1 := by
  classical
  have hdisjointOf : ∀ leftBlock rightBlock : Finset (Fin 7),
      (leftBlock ∩ rightBlock).card = 0 → Disjoint leftBlock rightBlock := fun _ _ hzero =>
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hzero)
  have hisolatedKill : ∀ block : Finset (Fin 7), block.card = 3 →
      IsIsolatedActiveBlock activeSet activeSubset block → False := by
    intro block hblockCard hisolated
    have hbound := card_le_value_of_isIsolatedActiveBlock hdata hvalueNe
      (Finset.card_pos.mp (by omega)) hisolated
    rw [hblockCard] at hbound
    norm_num at hbound
    linarith
  have hmembership := forall_eq_of_isActiveFamily_triple hfamily
  have hmembershipSecond : ∀ activeLabel ∈ activeSet,
      activeSubset activeLabel = secondBlock ∨ activeSubset activeLabel = firstBlock
        ∨ activeSubset activeLabel = thirdBlock := by
    intro activeLabel hactive
    rcases hmembership activeLabel hactive with hone | htwo | hthree
    · exact Or.inr (Or.inl hone)
    · exact Or.inl htwo
    · exact Or.inr (Or.inr hthree)
  have hmembershipThird : ∀ activeLabel ∈ activeSet,
      activeSubset activeLabel = thirdBlock ∨ activeSubset activeLabel = firstBlock
        ∨ activeSubset activeLabel = secondBlock := by
    intro activeLabel hactive
    rcases hmembership activeLabel hactive with hone | htwo | hthree
    · exact Or.inr (Or.inl hone)
    · exact Or.inr (Or.inr htwo)
    · exact Or.inl hthree
  rcases overlapPattern_trichotomy_sevenThree hfirst hsecond hthird hfirstSecond hfirstThird
    hsecondThird hcover with hpath | hsplit | hcore
  · exact hpath
  · exfalso
    obtain ⟨-, hcase⟩ := hsplit
    rcases hcase with ⟨hone, htwo⟩ | ⟨hone, htwo⟩ | ⟨hone, htwo⟩
    · exact hisolatedKill firstBlock hfirst (isIsolatedActiveBlock_of_forall_eq_of_disjoint
        hmembership (hdisjointOf _ _ hone) (hdisjointOf _ _ htwo))
    · refine hisolatedKill secondBlock hsecond
        (isIsolatedActiveBlock_of_forall_eq_of_disjoint hmembershipSecond ?_ ?_)
      · exact (hdisjointOf _ _ hone).symm
      · exact hdisjointOf _ _ htwo
    · refine hisolatedKill thirdBlock hthird
        (isIsolatedActiveBlock_of_forall_eq_of_disjoint hmembershipThird ?_ ?_)
      · exact (hdisjointOf _ _ hone).symm
      · exact (hdisjointOf _ _ htwo).symm
  · exfalso
    have hcoreNonempty : (firstBlock ∩ secondBlock ∩ thirdBlock).Nonempty :=
      Finset.card_pos.mp (by omega)
    have hsaturated : HasSaturatedAtom
        ({firstBlock, secondBlock, thirdBlock} : Finset (Finset (Fin 7))) :=
      (hasSaturatedAtom_triple_iff firstBlock secondBlock thirdBlock).mpr hcoreNonempty
    have hone := one_le_value_of_hasSaturatedAtom_of_isActiveFamily hdata hvalueNe hfamily
      hsaturated
    linarith

end SevenThreeQuadric

end Gtz
