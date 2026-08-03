/-
# Two-graph representability: every abstract two-graph on six labels is a link

`Gtz/Quantitative/CocycleRigidity.lean` proves the kill census over the `1024`
gauge-fixed links and reads it back at a design through `Gtz.flippedParity`, whose
flip factor is supplied BY A LINK.  Its own ledger records the resulting scope gap:
`Gtz.flipSupport_card_ge_of_solvesSignedEraseSystem` speaks about
link-parameterized flips, and to read it as "every phantom is one of the `123`
survivors" one additionally needs that every abstract two-graph on six labels IS
one of the `1024` links.  This file supplies exactly that, and its converse.

## What is proved here (no `sorry`, no `axiom`, no `native_decide`)

**Section 1, at GENERAL size.**  `Gtz.IsEdgeCoboundary` says a triple pattern is the
product of the three edge signs of a symmetric `±1` edge function trivial on the
diagonal.  Six consequences follow with no size and no rank hypothesis, of which the
load-bearing one is `Gtz.IsEdgeCoboundary.eq_product_through_base`: the pattern at ANY
triple is the product of its three patterns through ANY base atom.  That is the
abstract twin of the shipped `Gtz.tripleParity_eq_product_through_base`, and it is
what makes gauge-fixing at atom `0` lossless.

**Section 2, at six labels.**  `Gtz.linkWordOfFlip` packs the ten values through atom
`0`, mirroring the shipped `Gtz.linkWordOf`.  `Gtz.sectorIncoherent_linkWordOfFlip`
is the dictionary at EVERY triple -- no distinctness hypothesis, exactly as the
shipped `Gtz.sectorIncoherent_linkWordOf` -- and
`Gtz.exists_link_sectorIncoherent_eq_of_isEdgeCoboundary` is the surjectivity itself.
Six labels is not a stylistic restriction: the link encodes `2 ^ 10` two-graphs
because `10 = C(5,2)`, so the statement is per-cell by nature.

**Section 3, the converse and the characterization.**  `Gtz.sectorFlip` reads a link
back as a `±1` pattern and `Gtz.isEdgeCoboundary_sectorFlip` shows it is a coboundary
of `Gtz.linkBitOf` -- which is what `Gtz.sectorIncoherent` says definitionally.  So
`Gtz.isEdgeCoboundary_iff_exists_link` is an exact characterization: a `±1` triple
pattern is link-representable IFF it is an edge coboundary.  The `±1` hypothesis is
NOT decoration; `Gtz.not_forall_isEdgeCoboundary_of_exists_link` refutes the iff
without it, the constant `0` pattern matching link `0` while being no coboundary.

**Section 4, the design side and the payoff.**  `Gtz.isEdgeCoboundary_tripleParity`
is the non-vacuity witness: a design's own two-graph is a coboundary of
`Gtz.edgeSign`, definitionally.  `Gtz.flipSupport_card_ge_of_isEdgeCoboundary` then
states the census bound for an ARBITRARY two-graph flip factor rather than for a
link, closing the recorded gap.

## What is NOT proved here

Surjectivity onto ALL of `Gtz.IsParityFlip` is FALSE and no attempt is made on it:
that predicate is pointwise, so an arbitrary parity flip carries no coherence at all
and need not be a two-graph.  The coboundary restriction is the exact hypothesis the
census needs, and is the one the rigidity frame always intended.

Separately, the prose at `Gtz/Quantitative/TwoGraphCollision.lean` asserts that "all
`2 ^ 10` links occur".  That is a REALIZABILITY claim about designs -- every link is
the two-graph of some weighted design -- and it is nowhere proved in the tree.  It is
neither used nor established here; representability and realizability are different
statements and only the former is settled below.
-/
import Gtz.Quantitative.TwoGraphCollision
import Gtz.Quantitative.CocycleRigidity

namespace Gtz

variable {sizeIndex : ℕ}

/-! ## 1. Abstract two-graph patterns, at general size -/

/-- A triple pattern is an **edge coboundary** when it is the product of the three
edge signs of a symmetric `±1` edge function that is trivial on the diagonal.  This
is the abstract form of a two-graph; `Gtz.isEdgeCoboundary_tripleParity` shows a
design's own parity is one. -/
def IsEdgeCoboundary (flip : Fin sizeIndex → Fin sizeIndex → Fin sizeIndex → ℝ) : Prop :=
  ∃ edge : Fin sizeIndex → Fin sizeIndex → ℝ,
    (∀ first second, edge first second = edge second first) ∧
    (∀ first second, edge first second = 1 ∨ edge first second = -1) ∧
    (∀ atomIndex, edge atomIndex atomIndex = 1) ∧
    (∀ first second third,
      flip first second third = edge first second * edge first third * edge second third)

variable {flip : Fin sizeIndex → Fin sizeIndex → Fin sizeIndex → ℝ}

/-- A coboundary takes only the two values, being a product of three of them. -/
theorem IsEdgeCoboundary.eq_one_or_neg_one (hcob : IsEdgeCoboundary flip)
    (first second third : Fin sizeIndex) :
    flip first second third = 1 ∨ flip first second third = -1 := by
  obtain ⟨edge, _, hsign, _, hproduct⟩ := hcob
  rcases hsign first second with hone | hone <;> rcases hsign first third with htwo | htwo <;>
    rcases hsign second third with hthree | hthree <;>
    rw [hproduct, hone, htwo, hthree] <;> norm_num

/-- A triple repeating its first two atoms is coherent -- the edge sign it repeats
squares away.  Mirrors the shipped `Gtz.tripleParity_degenerate`. -/
theorem IsEdgeCoboundary.repeat_left (hcob : IsEdgeCoboundary flip)
    (first second : Fin sizeIndex) : flip first first second = 1 := by
  obtain ⟨edge, _, hsign, hdiag, hproduct⟩ := hcob
  rw [hproduct, hdiag]
  rcases hsign first second with hone | hone <;> rw [hone] <;> norm_num

/-- A triple repeating its last two atoms is coherent.  Mirrors the shipped
`Gtz.tripleParity_repeat_last`. -/
theorem IsEdgeCoboundary.repeat_right (hcob : IsEdgeCoboundary flip)
    (first second : Fin sizeIndex) : flip first second second = 1 := by
  obtain ⟨edge, _, hsign, hdiag, hproduct⟩ := hcob
  rw [hproduct, hdiag]
  rcases hsign first second with hone | hone <;> rw [hone] <;> norm_num

theorem IsEdgeCoboundary.comm_left (hcob : IsEdgeCoboundary flip)
    (first second third : Fin sizeIndex) :
    flip first second third = flip second first third := by
  obtain ⟨edge, hsymm, _, _, hproduct⟩ := hcob
  rw [hproduct, hproduct, hsymm first second]
  ring

theorem IsEdgeCoboundary.comm_right (hcob : IsEdgeCoboundary flip)
    (first second third : Fin sizeIndex) :
    flip first second third = flip first third second := by
  obtain ⟨edge, hsymm, _, _, hproduct⟩ := hcob
  rw [hproduct, hproduct, hsymm second third]
  ring

/-- **THE BASE-POINT LAW.**  The pattern at ANY triple is the product of its three
patterns through ANY base atom, with no distinctness hypothesis: the three edge signs
meeting the base each occur twice and square away.  This is the abstract twin of the
shipped `Gtz.tripleParity_eq_product_through_base`, and it is what makes the
gauge-fixing of section 2 lossless. -/
theorem IsEdgeCoboundary.eq_product_through_base (hcob : IsEdgeCoboundary flip)
    (base first second third : Fin sizeIndex) :
    flip first second third
      = flip base first second * flip base first third * flip base second third := by
  obtain ⟨edge, _, hsign, _, hproduct⟩ := hcob
  rcases hsign base first with hone | hone <;> rcases hsign base second with htwo | htwo <;>
    rcases hsign base third with hthree | hthree <;>
    rw [hproduct, hproduct, hproduct, hproduct, hone, htwo, hthree] <;> ring

/-! ## 2. Every abstract two-graph on six labels is a link

Six labels throughout this section and the next: a link is a natural number below
`2 ^ 10` because `10 = C(5,2)` counts the pairs avoiding the base, so the encoding is
per-cell by nature rather than by choice. -/

/-- The link word of an abstract flip pattern: its ten values through atom `0`,
packed exactly as the shipped `Gtz.linkWordOf` packs a design's. -/
noncomputable def linkWordOfFlip (flip : Fin 6 → Fin 6 → Fin 6 → ℝ) : Nat :=
  packTenBits
    (decide (flip 0 1 2 = -1)) (decide (flip 0 1 3 = -1)) (decide (flip 0 1 4 = -1))
    (decide (flip 0 1 5 = -1)) (decide (flip 0 2 3 = -1)) (decide (flip 0 2 4 = -1))
    (decide (flip 0 2 5 = -1)) (decide (flip 0 3 4 = -1)) (decide (flip 0 3 5 = -1))
    (decide (flip 0 4 5 = -1))

theorem linkWordOfFlip_lt (flip : Fin 6 → Fin 6 → Fin 6 → ℝ) : linkWordOfFlip flip < 1024 :=
  packTenBits_lt _ _ _ _ _ _ _ _ _ _

/-- The link bits of `Gtz.linkWordOfFlip` are the pattern's values through atom `0`,
at every ordered pair INCLUDING the degenerate ones: those land on the junk index
`10`, whose bit vanishes below `1024`, and the pattern really is `1` there. -/
theorem linkBitOf_linkWordOfFlip {flip : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hcob : IsEdgeCoboundary flip) (atomFirst atomSecond : Fin 6) :
    linkBitOf (linkWordOfFlip flip) atomFirst atomSecond
      = decide (flip 0 atomFirst atomSecond = -1) := by
  have hswap : ∀ first second : Fin 6, flip 0 first second = flip 0 second first :=
    fun first second => hcob.comm_right 0 first second
  have hdegenerate : ∀ {first second : Fin 6}, first = second ∨ first = 0 ∨ second = 0 →
      decide (flip 0 first second = -1) = false := by
    intro first second hcase
    have hvalue : flip 0 first second = 1 := by
      rcases hcase with hcase | hcase | hcase
      · subst hcase; exact hcob.repeat_right 0 first
      · subst hcase; exact hcob.repeat_left 0 second
      · subst hcase; rw [hswap]; exact hcob.repeat_left 0 first
    rw [hvalue]
    exact decide_eq_false (by norm_num)
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    simp only [linkBitOf, linkIndexOfPair, linkIndexOfValues, linkWordOfFlip,
      testBit_packTenBits_zero, testBit_packTenBits_one, testBit_packTenBits_two,
      testBit_packTenBits_three, testBit_packTenBits_four, testBit_packTenBits_five,
      testBit_packTenBits_six, testBit_packTenBits_seven, testBit_packTenBits_eight,
      testBit_packTenBits_nine, testBit_packTenBits_ten] <;>
    first
      | rfl
      | exact (hdegenerate (by decide)).symm
      | (rw [hswap]; rfl)

/-- **THE ABSTRACT DICTIONARY.**  The sector decode of `Gtz.linkWordOfFlip` agrees
with the pattern at EVERY triple -- no distinctness, no nonvanishing.  This is
`Gtz.IsEdgeCoboundary.eq_product_through_base` in Boolean form, exactly as the shipped
`Gtz.sectorIncoherent_linkWordOf` is the design-level product law in Boolean form. -/
theorem sectorIncoherent_linkWordOfFlip {flip : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hcob : IsEdgeCoboundary flip) (first second third : Fin 6) :
    sectorIncoherent (linkWordOfFlip flip) first second third
      = decide (flip first second third = -1) := by
  have hproduct := hcob.eq_product_through_base 0 first second third
  rw [sectorIncoherent, linkBitOf_linkWordOfFlip hcob, linkBitOf_linkWordOfFlip hcob,
    linkBitOf_linkWordOfFlip hcob]
  rcases hcob.eq_one_or_neg_one 0 first second with hone | hone <;>
    rcases hcob.eq_one_or_neg_one 0 first third with htwo | htwo <;>
    rcases hcob.eq_one_or_neg_one 0 second third with hthree | hthree <;>
    rw [hone, htwo, hthree] at hproduct <;> rw [hone, htwo, hthree, hproduct] <;> norm_num

/-- **SURJECTIVITY.**  Every abstract two-graph on six labels is one of the `1024`
links.  This is the step `Gtz/Quantitative/CocycleRigidity.lean` records as missing
between its census and the reading "every phantom is one of the `123` survivors". -/
theorem exists_link_sectorIncoherent_eq_of_isEdgeCoboundary
    {flip : Fin 6 → Fin 6 → Fin 6 → ℝ} (hcob : IsEdgeCoboundary flip) :
    ∃ link < 1024, ∀ first second third : Fin 6,
      sectorIncoherent link first second third = decide (flip first second third = -1) :=
  ⟨linkWordOfFlip flip, linkWordOfFlip_lt flip, sectorIncoherent_linkWordOfFlip hcob⟩

/-! ## 3. The converse, and the characterization -/

/-- A link, read back as a `±1` triple pattern. -/
def sectorFlip (link : Nat) (first second third : Fin 6) : ℝ :=
  if sectorIncoherent link first second third then -1 else 1

/-- `Gtz.linkBitOf` is symmetric, because `Gtz.linkIndexOfValues` sends both orders of
a pair -- and both orders of the junk arm -- to the same index. -/
theorem linkBitOf_symm (link : Nat) (atomFirst atomSecond : Fin 6) :
    linkBitOf link atomFirst atomSecond = linkBitOf link atomSecond atomFirst := by
  fin_cases atomFirst <;> fin_cases atomSecond <;> rfl

/-- A repeated pair lands on the junk index `10`, whose bit vanishes below `1024`. -/
theorem linkBitOf_self_eq_false {link : Nat} (hlink : link < 1024) (atomIndex : Fin 6) :
    linkBitOf link atomIndex atomIndex = false := by
  have hjunk : linkIndexOfPair atomIndex atomIndex = 10 := by fin_cases atomIndex <;> rfl
  rw [linkBitOf, hjunk]
  exact Nat.testBit_eq_false_of_lt (by omega)

/-- **THE CONVERSE.**  Every link reads back as an edge coboundary -- of `Gtz.linkBitOf`
itself, which is what `Gtz.sectorIncoherent` says definitionally. -/
theorem isEdgeCoboundary_sectorFlip {link : Nat} (hlink : link < 1024) :
    IsEdgeCoboundary (sectorFlip link) := by
  refine ⟨fun atomFirst atomSecond =>
    if linkBitOf link atomFirst atomSecond then -1 else 1, ?_, ?_, ?_, ?_⟩
  · intro atomFirst atomSecond
    dsimp only
    rw [linkBitOf_symm]
  · intro atomFirst atomSecond
    dsimp only
    by_cases hbit : linkBitOf link atomFirst atomSecond <;> simp [hbit]
  · intro atomIndex
    dsimp only
    rw [linkBitOf_self_eq_false hlink]
    norm_num
  · intro first second third
    dsimp only
    rw [sectorFlip, sectorIncoherent]
    cases linkBitOf link first second <;> cases linkBitOf link first third <;>
      cases linkBitOf link second third <;> simp

/-- **THE CHARACTERIZATION.**  A `±1` triple pattern on six labels is link-representable
exactly when it is an edge coboundary.  The `±1` hypothesis is necessary, not
decoration -- see `Gtz.not_forall_isEdgeCoboundary_of_exists_link`. -/
theorem isEdgeCoboundary_iff_exists_link {flip : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hsign : ∀ first second third : Fin 6,
      flip first second third = 1 ∨ flip first second third = -1) :
    IsEdgeCoboundary flip ↔
      ∃ link < 1024, ∀ first second third : Fin 6,
        sectorIncoherent link first second third = decide (flip first second third = -1) := by
  refine ⟨exists_link_sectorIncoherent_eq_of_isEdgeCoboundary, ?_⟩
  rintro ⟨link, hlink, heq⟩
  have hreadback : flip = sectorFlip link := by
    funext first second third
    rw [sectorFlip, heq]
    rcases hsign first second third with hvalue | hvalue <;> rw [hvalue] <;> norm_num
  rw [hreadback]
  exact isEdgeCoboundary_sectorFlip hlink

/-- **THE `±1` HYPOTHESIS IS LOAD-BEARING.**  Without it the characterization fails: the
constant `0` pattern matches link `0` on the nose, and is no coboundary. -/
theorem not_forall_isEdgeCoboundary_of_exists_link :
    ¬ ∀ flip : Fin 6 → Fin 6 → Fin 6 → ℝ,
        (∃ link < 1024, ∀ first second third : Fin 6,
          sectorIncoherent link first second third
            = decide (flip first second third = -1)) →
        IsEdgeCoboundary flip := by
  intro hall
  have hmatch : ∀ first second third : Fin 6,
      sectorIncoherent 0 first second third = decide ((0 : ℝ) = -1) := by
    intro first second third
    simp [sectorIncoherent, linkBitOf]
  have hzero : IsEdgeCoboundary (fun _ _ _ : Fin 6 => (0 : ℝ)) :=
    hall _ ⟨0, by norm_num, hmatch⟩
  rcases hzero.eq_one_or_neg_one 0 0 0 with hvalue | hvalue <;> norm_num at hvalue

/-! ## 4. The design side, and the payoff -/

/-- **NON-VACUITY.**  A design's own two-graph is an edge coboundary -- of
`Gtz.edgeSign`, definitionally, since `Gtz.tripleParity` is by construction the product
of the three edge signs.  The diagonal clause holds because a self-pairing is a
leverage, hence nonnegative. -/
theorem isEdgeCoboundary_tripleParity (D : WeightedDesign sizeIndex 3) :
    IsEdgeCoboundary (tripleParity D) := by
  refine ⟨edgeSign D, edgeSign_comm D, edgeSign_eq_one_or_neg_one D, ?_, fun _ _ _ => rfl⟩
  intro atomIndex
  rw [edgeSign, if_pos]
  rw [atomPairing_self]
  exact leverageOf_nonneg _

/-- The flip factor recovered: flipping by `Gtz.linkWordOfFlip` of a coboundary
multiplies the design's parity by that coboundary. -/
theorem flippedParity_linkWordOfFlip (D : WeightedDesign 6 3)
    {flipFactor : Fin 6 → Fin 6 → Fin 6 → ℝ} (hcob : IsEdgeCoboundary flipFactor)
    (first second third : Fin 6) :
    flippedParity D (linkWordOfFlip flipFactor) first second third
      = tripleParity D first second third * flipFactor first second third := by
  rw [flippedParity, sectorIncoherent_linkWordOfFlip hcob]
  rcases hcob.eq_one_or_neg_one first second third with hvalue | hvalue <;>
    rw [hvalue] <;> norm_num

/-- Multiplying the design's parity by a coboundary is a parity flip. -/
theorem isParityFlip_mul_of_isEdgeCoboundary (D : WeightedDesign sizeIndex 3)
    {flipFactor : Fin sizeIndex → Fin sizeIndex → Fin sizeIndex → ℝ}
    (hcob : IsEdgeCoboundary flipFactor) :
    IsParityFlip D (fun first second third =>
      tripleParity D first second third * flipFactor first second third) := by
  intro first second third
  dsimp only
  rcases hcob.eq_one_or_neg_one first second third with hvalue | hvalue <;>
    rw [hvalue] <;> [left; right] <;> ring

/-- A single incoherent ordered triple makes the flip support nonempty, so
nontriviality can be supplied in the flip factor's own terms. -/
theorem flipSupport_linkWordOfFlip_nonempty {flipFactor : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hcob : IsEdgeCoboundary flipFactor) {first second third : Fin 6}
    (hfirst : first < second) (hsecond : second < third)
    (hincoherent : flipFactor first second third = -1) :
    (flipSupport (linkWordOfFlip flipFactor)).Nonempty := by
  refine ⟨(first, second, third), ?_⟩
  rw [flipSupport, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hfirst, hsecond, ?_⟩
  rw [sectorIncoherent_linkWordOfFlip hcob, hincoherent]
  simp

/-- **THE PAYOFF: the census bound for an ARBITRARY two-graph flip.**  A phantom whose
flip factor is any nontrivial edge coboundary -- not merely one supplied by a link --
flips at least EIGHT of the twenty triples and imposes an exact relation on at least
TWELVE of the fifteen edges.  This is
`Gtz.flipSupport_card_ge_of_solvesSignedEraseSystem` with its link hypothesis
discharged by `Gtz.exists_link_sectorIncoherent_eq_of_isEdgeCoboundary`. -/
theorem flipSupport_card_ge_of_isEdgeCoboundary (D : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing D first second ≠ 0)
    {flipFactor : Fin 6 → Fin 6 → Fin 6 → ℝ} (hcob : IsEdgeCoboundary flipFactor)
    (hnontrivial : (flipSupport (linkWordOfFlip flipFactor)).Nonempty)
    (hsolve : SolvesSignedEraseSystem D (fun first second third =>
      tripleParity D first second third * flipFactor first second third)) :
    8 ≤ (flipSupport (linkWordOfFlip flipFactor)).card ∧
      12 ≤ (liveEdges (linkWordOfFlip flipFactor)).card := by
  refine flipSupport_card_ge_of_solvesSignedEraseSystem D hnonzero
    (linkWordOfFlip_lt flipFactor) hnontrivial ?_
  have hrewrite : flippedParity D (linkWordOfFlip flipFactor)
      = fun first second third =>
        tripleParity D first second third * flipFactor first second third := by
    funext first second third
    exact flippedParity_linkWordOfFlip D hcob first second third
  rw [hrewrite]
  exact hsolve

end Gtz
