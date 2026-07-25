/-
# The decision atlas at `(7,3)`: why averaging is dead, and what a certificate must look like

`Gtz.Quantitative.DiscriminantSystem` reduced the whole of GTZ at rank three to
ONE sentence, `DiscriminantCovering 7`: every all-heavy weighted `(7,3)` design
has an ordered triple with `discriminantTrace ≥ 0` and `discriminantTie ≥ 0`.
Pivot choice is immaterial (`discriminantSystem_pivot_independent`), so it is a
disjunction over `35` triples, and `discriminantTie` is `det(Gram_T − I)` — the
determinant of the principal `T`-submatrix of `N := G_7 − I_7`.

This file supplies the two things the covering needs before any certificate can be
attempted, and records what the numerics established about candidate selection
rules.

**Brick 1 — averaging is dead, exactly.** The split-tetrahedron `(7,3)` design
(the four regular-tetrahedron vertices, three of them split into equal-weight
copies, weights `1/8, 1/8, 1/8, 1/4, 1/8, 1/8, 1/8`) is exactly rational, exactly
Parseval, and has every leverage exactly `3`, hence is all-heavy with room to
spare. On it `discriminantTie` takes exactly two values — `0` on the `20` triples
carrying three distinct tetrahedron directions, `-8` on the remaining `15` — so
its SUM over the `35` triples is `-120` while its MAXIMUM is exactly `0`
(`splitSevenDesign_tieMean_negative_but_tieMax_zero`). The mean is strictly
negative where the max is exactly zero, so NO averaging or counting argument over
the `35` triples can establish `DiscriminantCovering 7`; in particular the
invariant aggregate `e_3(N) = e_3(lambda) − 5 e_2(lambda) + 15 tr(S) − 35` is
refuted as a route. Only a selection argument, which names a triple, can close it.

**Brick 2 — the atlas interface.** What remains is a certified finite case split:
finitely many cells cut out by explicit sign conditions, one triple assigned per
cell, and a certificate that the assigned triple satisfies both legs throughout.
`DecisionCell` / `DecisionAtlas` fix that interface generically — any number of
cells, any real-valued function of the design as a sign condition — and
`discriminantCovering_of_atlas` proves it sound unconditionally, chaining to
`GtzWeightedAll 3` and to `GtzOriginal n 3` for every `n`. The interface is also
LOSSLESS: `exists_atlas_iff_discriminantCovering` shows atlas existence is
EQUIVALENT to the covering, so no expressive power is given up by working in it.

**Brick 3 — cells that discharge, and the rules that do not.** Three cell
families are proved: the general radius box (`dominates_of_radiusBox`, which
subsumes the shipped near-orthogonal stratum at radius `1/2`, exactly tight
there), the coherent-sign cell (`dominates_of_coherentPairings`, which the
tetrahedron lies outside, so genuinely complementary), and the leverage-floor cell
(`dominates_of_leverageFloor_and_pairingCap`). The measured coverages of the ten
candidate selection rules are recorded where the corresponding objects are
defined; two negative results are proved rather than measured — the canonical
`argmax min(e_2, e_3)` selector is logically equivalent to the covering
(`minLegArgmax_succeeds_iff`, hence zero proof content), and the heaviest-atom
pivot rule is refuted at `(7,3)` itself (`heaviestAtomRule_refuted_at_seven`), not
merely one size below.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Ties.SelectionObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## Brick 1: the split tetrahedron at `(7,3)`, exactly -/

/-- Which of the four regular-tetrahedron directions each of the seven atoms
carries: atoms `4, 5, 6` replicate the directions of atoms `0, 1, 2`, and
direction `3` is carried by atom `3` alone. -/
def splitSevenDirection : Fin 7 → Fin 4 := ![0, 1, 2, 3, 0, 1, 2]

/-- The seven atoms of the split tetrahedron: the four regular-tetrahedron
vertices, with three of them repeated. -/
def splitSevenAtom : Fin 7 → Fin 3 → ℝ :=
  fun atomIndex => tetraAtom (splitSevenDirection atomIndex)

/-- The **split-tetrahedron `(7,3)` design**, exactly rational: the four
tetrahedron vertices with directions `0, 1, 2` split into two equal-weight
copies each. Every leverage is exactly `3` and Parseval is exactly `I_3`, so the
design sits on the rigid leverage-`3` slice where `∑ t_c |g_c|² = tr(I_3) = 3`
forces every leverage to equal the rank. -/
noncomputable def splitSevenDesign : WeightedDesign 7 3 where
  atom := splitSevenAtom
  weight := ![1/8, 1/8, 1/8, 1/4, 1/8, 1/8, 1/8]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_seven, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_seven, smul_eq_mul, splitSevenAtom,
      splitSevenDirection, tetraAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

@[simp] theorem splitSevenDesign_atom (atomIndex : Fin 7) :
    splitSevenDesign.atom atomIndex = tetraAtom (splitSevenDirection atomIndex) :=
  rfl

/-- Every atom of the split tetrahedron has leverage exactly `3`. -/
theorem splitSevenDesign_leverage (atomIndex : Fin 7) :
    leverageOf (splitSevenDesign.atom atomIndex) = 3 := by
  rw [splitSevenDesign_atom, leverageOf, ← dotProduct_self_eq_sum_sq]
  exact tetraAtom_dot_self (splitSevenDirection atomIndex)

/-- The split tetrahedron is all-heavy: every leverage is `3 > 1`. -/
theorem splitSevenDesign_allHeavy : AllHeavy splitSevenDesign := by
  intro atomIndex
  rw [splitSevenDesign_leverage]
  norm_num

/-- Every atom of the split tetrahedron has heavy excess exactly `2`. -/
theorem splitSevenDesign_heavyExcess (atomIndex : Fin 7) :
    heavyExcess splitSevenDesign atomIndex = 2 := by
  rw [heavyExcess, splitSevenDesign_leverage]
  norm_num

/-! ### The Gram of the split tetrahedron: `3` on a repeated direction, `-1` off -/

/-- Distinct regular-tetrahedron vertices pair to exactly `-1` — the sign that
`tetraAtom_dot_sq_of_ne` discards, and the only off-diagonal Gram value the
split tetrahedron carries. -/
theorem tetraAtom_dot_of_ne {dirFirst dirSecond : Fin 4} (hne : dirFirst ≠ dirSecond) :
    tetraAtom dirFirst ⬝ᵥ tetraAtom dirSecond = -1 := by
  fin_cases dirFirst <;> fin_cases dirSecond <;>
    simp_all [tetraAtom, dotProduct, Fin.sum_univ_three]

/-- Two atoms carrying the SAME tetrahedron direction pair to `3`. -/
theorem splitSevenDesign_atomPairing_of_sameDirection {atomFirst atomSecond : Fin 7}
    (hsame : splitSevenDirection atomFirst = splitSevenDirection atomSecond) :
    atomPairing splitSevenDesign atomFirst atomSecond = 3 := by
  rw [atomPairing, splitSevenDesign_atom, splitSevenDesign_atom, hsame]
  exact tetraAtom_dot_self _

/-- Two atoms carrying DIFFERENT tetrahedron directions pair to `-1`. -/
theorem splitSevenDesign_atomPairing_of_differentDirection {atomFirst atomSecond : Fin 7}
    (hdifferent : splitSevenDirection atomFirst ≠ splitSevenDirection atomSecond) :
    atomPairing splitSevenDesign atomFirst atomSecond = -1 := by
  rw [atomPairing, splitSevenDesign_atom, splitSevenDesign_atom]
  exact tetraAtom_dot_of_ne hdifferent

/-- No direction is carried by three distinct atoms: the multiplicity profile is
`(2,2,2,1)`. -/
theorem splitSevenDirection_no_tripleRepeat (atomFirst atomSecond atomThird : Fin 7)
    (hfirstSecond : atomFirst ≠ atomSecond) (hfirstThird : atomFirst ≠ atomThird)
    (hsecondThird : atomSecond ≠ atomThird) :
    ¬ (splitSevenDirection atomFirst = splitSevenDirection atomSecond
        ∧ splitSevenDirection atomFirst = splitSevenDirection atomThird) := by
  revert hfirstSecond hfirstThird hsecondThird
  revert atomFirst atomSecond atomThird
  decide

/-! ### The tie leg at the split tetrahedron takes exactly two values -/

/-- With every heavy excess equal to `2`, the tie leg of a triple is a symmetric
cubic in its three pairings alone. -/
theorem splitSevenDesign_discriminantTie_eq (pivot pairFirst pairSecond : Fin 7) :
    discriminantTie splitSevenDesign pivot pairFirst pairSecond
      = 8 - 2 * (atomPairing splitSevenDesign pairFirst pairSecond ^ 2
            + atomPairing splitSevenDesign pivot pairFirst ^ 2
            + atomPairing splitSevenDesign pivot pairSecond ^ 2)
        + 2 * atomPairing splitSevenDesign pairFirst pairSecond
            * atomPairing splitSevenDesign pivot pairFirst
            * atomPairing splitSevenDesign pivot pairSecond := by
  simp only [discriminantTie, splitSevenDesign_heavyExcess]
  ring

/-- **A rainbow triple TIES**: three distinct tetrahedron directions give all
three pairings `-1`, hence `discriminantTie = 8 − 6 − 2 = 0` exactly. -/
theorem splitSevenDesign_discriminantTie_of_rainbowDirections
    {pivot pairFirst pairSecond : Fin 7}
    (hpivotFirst : splitSevenDirection pivot ≠ splitSevenDirection pairFirst)
    (hpivotSecond : splitSevenDirection pivot ≠ splitSevenDirection pairSecond)
    (hpairDistinct : splitSevenDirection pairFirst ≠ splitSevenDirection pairSecond) :
    discriminantTie splitSevenDesign pivot pairFirst pairSecond = 0 := by
  rw [splitSevenDesign_discriminantTie_eq,
    splitSevenDesign_atomPairing_of_differentDirection hpairDistinct,
    splitSevenDesign_atomPairing_of_differentDirection hpivotFirst,
    splitSevenDesign_atomPairing_of_differentDirection hpivotSecond]
  norm_num

/-- **A triple repeating a direction FAILS by exactly `-8`**: one pairing is `3`
and the other two are `-1`, hence `discriminantTie = 8 − 22 + 6 = -8`. -/
theorem splitSevenDesign_discriminantTie_of_repeatedDirection
    {pivot pairFirst pairSecond : Fin 7} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hrepeat : splitSevenDirection pivot = splitSevenDirection pairFirst
        ∨ splitSevenDirection pivot = splitSevenDirection pairSecond
        ∨ splitSevenDirection pairFirst = splitSevenDirection pairSecond) :
    discriminantTie splitSevenDesign pivot pairFirst pairSecond = -8 := by
  rw [splitSevenDesign_discriminantTie_eq]
  rcases hrepeat with hsame | hsame | hsame
  · have hpivotSecondDifferent :
        splitSevenDirection pivot ≠ splitSevenDirection pairSecond := fun heq =>
      splitSevenDirection_no_tripleRepeat pivot pairFirst pairSecond hpivotFirst
        hpivotSecond hpairDistinct ⟨hsame, heq⟩
    have hpairDifferent :
        splitSevenDirection pairFirst ≠ splitSevenDirection pairSecond := fun heq =>
      hpivotSecondDifferent (hsame.trans heq)
    rw [splitSevenDesign_atomPairing_of_differentDirection hpairDifferent,
      splitSevenDesign_atomPairing_of_sameDirection hsame,
      splitSevenDesign_atomPairing_of_differentDirection hpivotSecondDifferent]
    norm_num
  · have hpivotFirstDifferent :
        splitSevenDirection pivot ≠ splitSevenDirection pairFirst := fun heq =>
      splitSevenDirection_no_tripleRepeat pivot pairFirst pairSecond hpivotFirst
        hpivotSecond hpairDistinct ⟨heq, hsame⟩
    have hpairDifferent :
        splitSevenDirection pairFirst ≠ splitSevenDirection pairSecond := fun heq =>
      hpivotFirstDifferent (hsame.trans heq.symm)
    rw [splitSevenDesign_atomPairing_of_differentDirection hpairDifferent,
      splitSevenDesign_atomPairing_of_differentDirection hpivotFirstDifferent,
      splitSevenDesign_atomPairing_of_sameDirection hsame]
    norm_num
  · have hpivotFirstDifferent :
        splitSevenDirection pivot ≠ splitSevenDirection pairFirst := fun heq =>
      splitSevenDirection_no_tripleRepeat pivot pairFirst pairSecond hpivotFirst
        hpivotSecond hpairDistinct ⟨heq, heq.trans hsame⟩
    have hpivotSecondDifferent :
        splitSevenDirection pivot ≠ splitSevenDirection pairSecond := fun heq =>
      hpivotFirstDifferent (heq.trans hsame.symm)
    rw [splitSevenDesign_atomPairing_of_sameDirection hsame,
      splitSevenDesign_atomPairing_of_differentDirection hpivotFirstDifferent,
      splitSevenDesign_atomPairing_of_differentDirection hpivotSecondDifferent]
    norm_num

/-- **The maximum of the tie leg over the split tetrahedron's triples is `0`**:
every triple of distinct atoms has `discriminantTie ≤ 0`. -/
theorem splitSevenDesign_discriminantTie_nonpos {pivot pairFirst pairSecond : Fin 7}
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond) :
    discriminantTie splitSevenDesign pivot pairFirst pairSecond ≤ 0 := by
  by_cases hpivotFirstSame :
      splitSevenDirection pivot = splitSevenDirection pairFirst
  · rw [splitSevenDesign_discriminantTie_of_repeatedDirection hpivotFirst
      hpivotSecond hpairDistinct (Or.inl hpivotFirstSame)]
    norm_num
  by_cases hpivotSecondSame :
      splitSevenDirection pivot = splitSevenDirection pairSecond
  · rw [splitSevenDesign_discriminantTie_of_repeatedDirection hpivotFirst
      hpivotSecond hpairDistinct (Or.inr (Or.inl hpivotSecondSame))]
    norm_num
  by_cases hpairSame :
      splitSevenDirection pairFirst = splitSevenDirection pairSecond
  · rw [splitSevenDesign_discriminantTie_of_repeatedDirection hpivotFirst
      hpivotSecond hpairDistinct (Or.inr (Or.inr hpairSame))]
    norm_num
  · rw [splitSevenDesign_discriminantTie_of_rainbowDirections hpivotFirstSame
      hpivotSecondSame hpairSame]

/-! ### The sum over the `35` triples, and why averaging is dead -/

/-- The `35` triples of the covering at `(7,3)`, canonically ordered by index. -/
def increasingTriplesSeven : Finset (Fin 7 × Fin 7 × Fin 7) :=
  Finset.univ.filter fun triple => triple.1 < triple.2.1 ∧ triple.2.1 < triple.2.2

/-- There are exactly `35` of them — `discriminantSystem_pivot_independent` is
what makes this the right index set, rather than the `105` ordered readings. -/
theorem increasingTriplesSeven_card : increasingTriplesSeven.card = 35 := by decide

/-- Increasing index triples have pairwise distinct entries, so every one of them
is a legal argument to the discriminant system. -/
theorem increasingTriplesSeven_distinct {triple : Fin 7 × Fin 7 × Fin 7}
    (hmem : triple ∈ increasingTriplesSeven) :
    triple.1 ≠ triple.2.1 ∧ triple.1 ≠ triple.2.2 ∧ triple.2.1 ≠ triple.2.2 := by
  rw [increasingTriplesSeven, Finset.mem_filter] at hmem
  obtain ⟨-, hfirstLt, hsecondLt⟩ := hmem
  exact ⟨ne_of_lt hfirstLt, ne_of_lt (hfirstLt.trans hsecondLt), ne_of_lt hsecondLt⟩

/-- A triple is RAINBOW when its three atoms carry three distinct tetrahedron
directions. Exactly the rainbow triples of the split tetrahedron dominate. -/
abbrev HasRainbowDirections (triple : Fin 7 × Fin 7 × Fin 7) : Prop :=
  splitSevenDirection triple.1 ≠ splitSevenDirection triple.2.1
    ∧ splitSevenDirection triple.1 ≠ splitSevenDirection triple.2.2
    ∧ splitSevenDirection triple.2.1 ≠ splitSevenDirection triple.2.2

/-- `20` of the `35` triples are rainbow: choose `3` of the `4` directions, then
one atom per chosen direction — `8 + 4 + 4 + 4`. -/
theorem rainbowTriplesSeven_card :
    (increasingTriplesSeven.filter HasRainbowDirections).card = 20 := by decide

/-- The remaining `15` repeat a direction: three duplicated directions times the
five other atoms. -/
theorem repeatedTriplesSeven_card :
    (increasingTriplesSeven.filter fun triple => ¬ HasRainbowDirections triple).card
      = 15 := by decide

/-- A non-rainbow triple of distinct atoms repeats one of its three directions. -/
theorem splitSevenDesign_discriminantTie_of_notRainbow
    {triple : Fin 7 × Fin 7 × Fin 7} (hmem : triple ∈ increasingTriplesSeven)
    (hnotRainbow : ¬ HasRainbowDirections triple) :
    discriminantTie splitSevenDesign triple.1 triple.2.1 triple.2.2 = -8 := by
  obtain ⟨hpivotFirst, hpivotSecond, hpairDistinct⟩ :=
    increasingTriplesSeven_distinct hmem
  refine splitSevenDesign_discriminantTie_of_repeatedDirection hpivotFirst
    hpivotSecond hpairDistinct ?_
  rcases Decidable.em (splitSevenDirection triple.1 = splitSevenDirection triple.2.1) with
    hfirst | hfirst
  · exact Or.inl hfirst
  rcases Decidable.em (splitSevenDirection triple.1 = splitSevenDirection triple.2.2) with
    hsecond | hsecond
  · exact Or.inr (Or.inl hsecond)
  rcases Decidable.em
      (splitSevenDirection triple.2.1 = splitSevenDirection triple.2.2) with hpair | hpair
  · exact Or.inr (Or.inr hpair)
  · exact absurd ⟨hfirst, hsecond, hpair⟩ hnotRainbow

/-- **The tie leg sums to `-120` over the `35` triples**: `20` rainbow triples
contribute `0` each and `15` direction-repeating triples contribute `-8` each.
Since `discriminantTie` is `det(Gram_T − I)` and the `3×3` blocks are the
principal submatrices of `N = G_7 − I_7`, this number is `e_3(N)`. -/
theorem splitSevenDesign_discriminantTie_sum :
    ∑ triple ∈ increasingTriplesSeven,
        discriminantTie splitSevenDesign triple.1 triple.2.1 triple.2.2 = -120 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not increasingTriplesSeven
    HasRainbowDirections
    (fun triple => discriminantTie splitSevenDesign triple.1 triple.2.1 triple.2.2)]
  have hrainbowSum : ∑ triple ∈ increasingTriplesSeven.filter HasRainbowDirections,
      discriminantTie splitSevenDesign triple.1 triple.2.1 triple.2.2 = 0 := by
    refine Finset.sum_eq_zero fun triple hmem => ?_
    obtain ⟨-, hrainbow⟩ := Finset.mem_filter.mp hmem
    exact splitSevenDesign_discriminantTie_of_rainbowDirections hrainbow.1
      hrainbow.2.1 hrainbow.2.2
  have hrepeatedSum :
      ∑ triple ∈ increasingTriplesSeven.filter
          (fun triple => ¬ HasRainbowDirections triple),
        discriminantTie splitSevenDesign triple.1 triple.2.1 triple.2.2 = -120 := by
    rw [Finset.sum_congr rfl fun triple hmem =>
      splitSevenDesign_discriminantTie_of_notRainbow
        (Finset.mem_filter.mp hmem).1 (Finset.mem_filter.mp hmem).2,
      Finset.sum_const, repeatedTriplesSeven_card]
    norm_num
  rw [hrainbowSum, hrepeatedSum, zero_add]

/-! ### The tying triple, and the reading -/

/-- The trace leg at a rainbow triple is `6`: both pivot pairings are `-1` and
both heavy excesses are `2`, so each summand is `2·2 − 1 = 3`. -/
theorem splitSevenDesign_discriminantTrace_of_rainbowDirections
    {pivot pairFirst pairSecond : Fin 7}
    (hpivotFirst : splitSevenDirection pivot ≠ splitSevenDirection pairFirst)
    (hpivotSecond : splitSevenDirection pivot ≠ splitSevenDirection pairSecond) :
    discriminantTrace splitSevenDesign pivot pairFirst pairSecond = 6 := by
  rw [discriminantTrace, splitSevenDesign_heavyExcess, splitSevenDesign_heavyExcess,
    splitSevenDesign_heavyExcess,
    splitSevenDesign_atomPairing_of_differentDirection hpivotFirst,
    splitSevenDesign_atomPairing_of_differentDirection hpivotSecond]
  norm_num

/-- **Every rainbow triple dominates** — weakly, with the tie leg exactly zero.
The `20` rainbow triples are precisely the `20` dominating subsets of the split
tetrahedron, and each of them TIES at `(e_1, e_2, e_3)(Gram − I) = (6, 9, 0)`. -/
theorem splitSevenDesign_dominates_of_rainbowDirections
    {pivot pairFirst pairSecond : Fin 7} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hdirPivotFirst : splitSevenDirection pivot ≠ splitSevenDirection pairFirst)
    (hdirPivotSecond : splitSevenDirection pivot ≠ splitSevenDirection pairSecond)
    (hdirPair : splitSevenDirection pairFirst ≠ splitSevenDirection pairSecond) :
    Dominates splitSevenDesign {pivot, pairFirst, pairSecond} := by
  refine (dominates_triple_iff_discriminantSystem splitSevenDesign hpivotFirst
    hpivotSecond hpairDistinct (splitSevenDesign_allHeavy pivot)).mpr ⟨?_, ?_⟩
  · rw [splitSevenDesign_discriminantTrace_of_rainbowDirections hdirPivotFirst
      hdirPivotSecond]
    norm_num
  · rw [splitSevenDesign_discriminantTie_of_rainbowDirections hdirPivotFirst
      hdirPivotSecond hdirPair]

/-- The trace leg at the rainbow triple `{0,1,2}` is `6`. -/
theorem splitSevenDesign_discriminantTrace_zeroOneTwo :
    discriminantTrace splitSevenDesign 0 1 2 = 6 :=
  splitSevenDesign_discriminantTrace_of_rainbowDirections (by decide) (by decide)

/-- The tie leg at `{0,1,2}` is EXACTLY zero: the split tetrahedron sits on the
tie boundary. -/
theorem splitSevenDesign_discriminantTie_zeroOneTwo :
    discriminantTie splitSevenDesign 0 1 2 = 0 :=
  splitSevenDesign_discriminantTie_of_rainbowDirections (by decide) (by decide) (by decide)

/-- `{0,1,2}` dominates the split tetrahedron, weakly. -/
theorem splitSevenDesign_dominates_zeroOneTwo :
    Dominates splitSevenDesign {0, 1, 2} :=
  splitSevenDesign_dominates_of_rainbowDirections (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- **AVERAGING AND COUNTING OVER THE `35` TRIPLES CANNOT PROVE THE COVERING.**
At the split-tetrahedron `(7,3)` design — exactly rational, exactly Parseval,
every leverage exactly `3`, hence all-heavy with room to spare — the MEAN of
`discriminantTie` over the `35` triples is `-120/35 < 0`, while its MAXIMUM is
exactly `0`, attained at each of the `20` rainbow triples. So every functional
that is monotone in the multiset of the `35` tie values and vanishes on the
constant-zero multiset — the sum `e_3(N)`, any weighted average, any count of
sign patterns — is STRICTLY NEGATIVE at a design where the covering nonetheless
holds. Only a selection argument, which names a triple, can close the covering;
the aggregate `e_3(N) = e_3(λ) − 5 e_2(λ) + 15 tr(S) − 35` is refuted as a route.

`AllHeavy` supplies `e_1(Gram_T − I) > 0` for free at every triple
(`allHeavy_heavyExcess_pos`), and here `e_2 = 9 > 0` at every rainbow triple, so
the determinant is the leg that binds. -/
theorem splitSevenDesign_tieMean_negative_but_tieMax_zero :
    (∑ triple ∈ increasingTriplesSeven,
        discriminantTie splitSevenDesign triple.1 triple.2.1 triple.2.2) < 0
      ∧ (∀ triple ∈ increasingTriplesSeven,
        discriminantTie splitSevenDesign triple.1 triple.2.1 triple.2.2 ≤ 0)
      ∧ discriminantTie splitSevenDesign 0 1 2 = 0
      ∧ AllHeavy splitSevenDesign := by
  refine ⟨?_, fun triple hmem => ?_, splitSevenDesign_discriminantTie_zeroOneTwo,
    splitSevenDesign_allHeavy⟩
  · rw [splitSevenDesign_discriminantTie_sum]; norm_num
  · obtain ⟨hpivotFirst, hpivotSecond, hpairDistinct⟩ :=
      increasingTriplesSeven_distinct hmem
    exact splitSevenDesign_discriminantTie_nonpos hpivotFirst hpivotSecond hpairDistinct

/-! ## Brick 2: the decision-atlas interface

The covering is a `∀ design ∃ triple` sentence, and the previous section kills
every route that replaces the `∃` by an aggregate. What remains is a CERTIFIED
FINITE CASE SPLIT: cut the all-heavy parameter space into finitely many cells by
explicit sign conditions, assign one triple to each cell, and certify the two
legs throughout that cell. This section fixes that interface, once, so a future
certificate plugs in without re-deriving anything, and proves the interface
SOUND and LOSSLESS. -/

/-- **A decision cell** of the covering at `(m,3)`: a finite list of real-valued
functions of the design, all required to be nonnegative, together with the
ordered triple of distinct atoms assigned throughout the cell.

The sign-condition language is deliberately unconstrained — a condition is any
`WeightedDesign m 3 → ℝ`. Polynomials in the Gram entries, heavy excesses,
leverage differences and margins are all expressible, so the interface is not
tailored to one guess about which conditions a certificate will need. -/
structure DecisionCell (m : ℕ) where
  /-- The sign conditions cutting out the cell; each is required nonnegative. -/
  signConditions : List (WeightedDesign m 3 → ℝ)
  /-- The pivot of the triple assigned to this cell. -/
  pivot : Fin m
  /-- The first pair atom of the triple assigned to this cell. -/
  pairFirst : Fin m
  /-- The second pair atom of the triple assigned to this cell. -/
  pairSecond : Fin m
  pivotNePairFirst : pivot ≠ pairFirst
  pivotNePairSecond : pivot ≠ pairSecond
  pairFirstNePairSecond : pairFirst ≠ pairSecond

/-- A design LIES IN a cell when every one of the cell's sign conditions is
nonnegative at it. -/
def IsInCell {m : ℕ} (cell : DecisionCell m) (D : WeightedDesign m 3) : Prop :=
  ∀ condition ∈ cell.signConditions, 0 ≤ condition D

/-- A cell DISCHARGES its obligation when its assigned triple satisfies both
discriminant legs at every all-heavy design lying in the cell. This is the one
thing a certificate has to supply per cell; everything else is bookkeeping. -/
def CellDischarges {m : ℕ} (cell : DecisionCell m) : Prop :=
  ∀ D : WeightedDesign m 3, AllHeavy D → IsInCell cell D →
    0 ≤ discriminantTrace D cell.pivot cell.pairFirst cell.pairSecond
      ∧ 0 ≤ discriminantTie D cell.pivot cell.pairFirst cell.pairSecond

/-- **A decision atlas**: a finite list of cells. Generic in the number of cells
and in the sign-condition language. -/
structure DecisionAtlas (m : ℕ) where
  /-- The cells of the atlas. -/
  cells : List (DecisionCell m)

/-- The atlas COVERS when every all-heavy design lies in some cell. This is the
combinatorial half of the work, and the half the numerics say is hard. -/
def AtlasCovers {m : ℕ} (atlas : DecisionAtlas m) : Prop :=
  ∀ D : WeightedDesign m 3, AllHeavy D → ∃ cell ∈ atlas.cells, IsInCell cell D

/-- The atlas DISCHARGES when every one of its cells does. This is the
certificate half. -/
def AtlasDischarges {m : ℕ} (atlas : DecisionAtlas m) : Prop :=
  ∀ cell ∈ atlas.cells, CellDischarges cell

/-- **ATLAS SOUNDNESS**, unconditionally: a covering, discharging atlas at size
`m` proves `DiscriminantCovering m`. Pure logic over the shipped narrowing — no
new mathematics, no finiteness of the cell list, no property of the
sign-condition language. -/
theorem discriminantCovering_of_atlas {m : ℕ} (atlas : DecisionAtlas m)
    (hcovers : AtlasCovers atlas) (hdischarges : AtlasDischarges atlas) :
    DiscriminantCovering m := by
  intro D hheavy
  obtain ⟨cell, hcellMem, hinCell⟩ := hcovers D hheavy
  obtain ⟨htrace, htie⟩ := hdischarges cell hcellMem D hheavy hinCell
  exact ⟨cell.pivot, cell.pairFirst, cell.pairSecond, cell.pivotNePairFirst,
    cell.pivotNePairSecond, cell.pairFirstNePairSecond, htrace, htie⟩

/-- **The atlas route to rank three**: one covering, discharging atlas at `(7,3)`
proves weighted GTZ at rank three for every size, through
`discriminantCovering_seven_iff_rank_three`. -/
theorem gtzWeightedAll_three_of_atlasSeven (atlas : DecisionAtlas 7)
    (hcovers : AtlasCovers atlas) (hdischarges : AtlasDischarges atlas) :
    GtzWeightedAll 3 :=
  discriminantCovering_seven_iff_rank_three.mp
    (discriminantCovering_of_atlas atlas hcovers hdischarges)

/-- **The atlas route to the 1997 statement**: one covering, discharging atlas at
`(7,3)` proves `GtzOriginal n 3` for every `n`, through
`gtz_original_rank_three_of_discriminantCovering_seven`. -/
theorem gtzOriginal_rank_three_of_atlasSeven (atlas : DecisionAtlas 7)
    (hcovers : AtlasCovers atlas) (hdischarges : AtlasDischarges atlas) :
    ∀ n, 0 < n → GtzOriginal n 3 :=
  gtz_original_rank_three_of_discriminantCovering_seven
    (discriminantCovering_of_atlas atlas hcovers hdischarges)

/-! ### The interface is lossless

Soundness alone would be satisfied by an interface too rigid to express the
answer. The tautological atlas — one cell per ordered triple of distinct atoms,
whose sign conditions ARE the two legs at that triple — shows there is no such
loss: atlas existence is EQUIVALENT to the covering. So building an atlas is
exactly the right shape of work, and any failure to build one is a failure of the
mathematics, never of this interface. -/

/-- The tautological cell at an ordered triple of distinct atoms: its two sign
conditions are the two discriminant legs at that very triple. -/
def tautologicalCell {m : ℕ} {pivot pairFirst pairSecond : Fin m}
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond) : DecisionCell m where
  signConditions :=
    [fun D => discriminantTrace D pivot pairFirst pairSecond,
      fun D => discriminantTie D pivot pairFirst pairSecond]
  pivot := pivot
  pairFirst := pairFirst
  pairSecond := pairSecond
  pivotNePairFirst := hpivotFirst
  pivotNePairSecond := hpivotSecond
  pairFirstNePairSecond := hpairDistinct

/-- Lying in a tautological cell IS satisfying the two legs at its triple. -/
theorem isInCell_tautologicalCell_iff {m : ℕ} (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    IsInCell (tautologicalCell hpivotFirst hpivotSecond hpairDistinct) D
      ↔ (0 ≤ discriminantTrace D pivot pairFirst pairSecond
          ∧ 0 ≤ discriminantTie D pivot pairFirst pairSecond) := by
  constructor
  · intro hinCell
    refine ⟨hinCell (fun E => discriminantTrace E pivot pairFirst pairSecond) ?_,
      hinCell (fun E => discriminantTie E pivot pairFirst pairSecond) ?_⟩
    · simp [tautologicalCell]
    · simp [tautologicalCell]
  · rintro ⟨htrace, htie⟩ condition hcondition
    simp only [tautologicalCell, List.mem_cons, List.not_mem_nil, or_false] at hcondition
    rcases hcondition with rfl | rfl
    · exact htrace
    · exact htie

/-- Every tautological cell discharges: its sign conditions are literally its
obligation. -/
theorem tautologicalCell_discharges {m : ℕ} {pivot pairFirst pairSecond : Fin m}
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond) :
    CellDischarges (tautologicalCell hpivotFirst hpivotSecond hpairDistinct) :=
  fun D _ hinCell =>
    (isInCell_tautologicalCell_iff D hpivotFirst hpivotSecond hpairDistinct).mp hinCell

/-- One tautological cell per ordered triple of distinct atoms. -/
noncomputable def tautologicalAtlas (m : ℕ) : DecisionAtlas m where
  cells := (Finset.univ : Finset {triple : Fin m × Fin m × Fin m //
      triple.1 ≠ triple.2.1 ∧ triple.1 ≠ triple.2.2
        ∧ triple.2.1 ≠ triple.2.2}).toList.map
    fun triple =>
      tautologicalCell triple.property.1 triple.property.2.1 triple.property.2.2

theorem tautologicalAtlas_discharges (m : ℕ) :
    AtlasDischarges (tautologicalAtlas m) := by
  intro cell hcellMem
  simp only [tautologicalAtlas, List.mem_map] at hcellMem
  obtain ⟨triple, -, hcellEq⟩ := hcellMem
  subst hcellEq
  exact tautologicalCell_discharges triple.property.1 triple.property.2.1
    triple.property.2.2

/-- The tautological atlas covers exactly when the covering holds. -/
theorem tautologicalAtlas_covers_iff (m : ℕ) :
    AtlasCovers (tautologicalAtlas m) ↔ DiscriminantCovering m := by
  constructor
  · intro hcovers
    exact discriminantCovering_of_atlas (tautologicalAtlas m) hcovers
      (tautologicalAtlas_discharges m)
  · intro hcover D hheavy
    obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
      htrace, htie⟩ := hcover D hheavy
    refine ⟨tautologicalCell hpivotFirst hpivotSecond hpairDistinct, ?_, ?_⟩
    · simp only [tautologicalAtlas, List.mem_map]
      exact ⟨⟨(pivot, pairFirst, pairSecond), hpivotFirst, hpivotSecond,
        hpairDistinct⟩, by simp, rfl⟩
    · exact (isInCell_tautologicalCell_iff D hpivotFirst hpivotSecond
        hpairDistinct).mpr ⟨htrace, htie⟩

/-- **THE ATLAS INTERFACE IS EXACTLY THE COVERING.** Existence of a finite
covering, discharging decision atlas at size `m` is equivalent to
`DiscriminantCovering m`. -/
theorem exists_atlas_iff_discriminantCovering (m : ℕ) :
    (∃ atlas : DecisionAtlas m, AtlasCovers atlas ∧ AtlasDischarges atlas)
      ↔ DiscriminantCovering m := by
  constructor
  · rintro ⟨atlas, hcovers, hdischarges⟩
    exact discriminantCovering_of_atlas atlas hcovers hdischarges
  · intro hcover
    exact ⟨tautologicalAtlas m, (tautologicalAtlas_covers_iff m).mpr hcover,
      tautologicalAtlas_discharges m⟩

/-- **The polynomial frontier of rank three, as an atlas problem.** GTZ at rank
three for every `n` IS the existence of one finite covering, discharging decision
atlas at `(7,3)`. -/
theorem exists_atlas_seven_iff_rank_three :
    (∃ atlas : DecisionAtlas 7, AtlasCovers atlas ∧ AtlasDischarges atlas)
      ↔ GtzWeightedAll 3 :=
  (exists_atlas_iff_discriminantCovering 7).trans
    discriminantCovering_seven_iff_rank_three

/-! ## Brick 3: cells that discharge, and the selection rules the numerics measured -/

section CandidateCells

variable {m : ℕ}

/-- **The tie leg is the elliptope determinant**, a pure `ring` rearrangement of
`discriminantTie`: with `u_c := heavyExcess c` (positive exactly under
`AllHeavy`),

  `det(Gram_T − I) = u_p u_a u_b − u_b P_pa² − u_a P_pb² − u_p P_ab²
                       + 2 P_pa P_pb P_ab`.

Dividing by the positive `u_p u_a u_b` and setting `rho_cd := P_cd / sqrt(u_c u_d)`
turns this into `1 − rho_pa² − rho_pb² − rho_ab² + 2 rho_pa rho_pb rho_ab`, the
`3×3` elliptope form: the leverages factor out COMPLETELY, and the per-triple
obligation is degree three in THREE variables rather than degree three in six.
Every cell below is a region in those three normalized pairings, written
square-root-free by clearing the denominators. -/
theorem discriminantTie_eq_gramMinorForm (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    discriminantTie D pivot pairFirst pairSecond
      = heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond
        - heavyExcess D pairSecond * atomPairing D pivot pairFirst ^ 2
        - heavyExcess D pairFirst * atomPairing D pivot pairSecond ^ 2
        - heavyExcess D pivot * atomPairing D pairFirst pairSecond ^ 2
        + 2 * atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
            * atomPairing D pairFirst pairSecond := by
  rw [discriminantTie]
  ring

/-- **The general radius-box cell.** Three rational radii, one admissibility
inequality putting the box inside the elliptope, and one box bound per pair. The
whole asymmetric-box family the numerics explored instantiates this single
theorem, and the multiplier degree is zero: every step is a product of the
hypotheses by a positive quantity.

Measured coverage under uniform sampling of `Gr(3,7) × Δ⁶`: the symmetric radius
`1/2` covers `0.883`; a `44`-cell family of maximal asymmetric boxes on a `0.05`
grid covers `0.99992`. A finite union of boxes can never reach `1` because the
elliptope boundary is curved — but the split tetrahedron sits at a box CORNER,
where the certificate is exactly tight, so the tie locus is not what obstructs
boxes. -/
theorem dominates_of_radiusBox (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hfirstHeavy : 1 < leverageOf (D.atom pairFirst))
    (hsecondHeavy : 1 < leverageOf (D.atom pairSecond))
    {radiusPivotFirst radiusPivotSecond radiusPair : ℝ}
    (hradiusPivotFirstNonneg : 0 ≤ radiusPivotFirst)
    (hradiusPivotSecondNonneg : 0 ≤ radiusPivotSecond)
    (hradiusPairNonneg : 0 ≤ radiusPair)
    (hadmissible : radiusPivotFirst ^ 2 + radiusPivotSecond ^ 2 + radiusPair ^ 2
        + 2 * radiusPivotFirst * radiusPivotSecond * radiusPair ≤ 1)
    (hboxPivotFirst : atomPairing D pivot pairFirst ^ 2
        ≤ radiusPivotFirst ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst))
    (hboxPivotSecond : atomPairing D pivot pairSecond ^ 2
        ≤ radiusPivotSecond ^ 2 * (heavyExcess D pivot * heavyExcess D pairSecond))
    (hboxPair : atomPairing D pairFirst pairSecond ^ 2
        ≤ radiusPair ^ 2 * (heavyExcess D pairFirst * heavyExcess D pairSecond)) :
    Dominates D {pivot, pairFirst, pairSecond} := by
  have hpivotPos : 0 < heavyExcess D pivot := by rw [heavyExcess]; linarith
  have hfirstPos : 0 < heavyExcess D pairFirst := by rw [heavyExcess]; linarith
  have hsecondPos : 0 < heavyExcess D pairSecond := by rw [heavyExcess]; linarith
  have hexcessProductPos : 0 < heavyExcess D pivot * heavyExcess D pairFirst
      * heavyExcess D pairSecond := mul_pos (mul_pos hpivotPos hfirstPos) hsecondPos
  -- each radius is at most one, because the admissibility slack is nonnegative
  have hradiusPivotFirstSqLe : radiusPivotFirst ^ 2 ≤ 1 := by
    have hcross : 0 ≤ 2 * radiusPivotFirst * radiusPivotSecond * radiusPair := by
      positivity
    linarith [sq_nonneg radiusPivotSecond, sq_nonneg radiusPair]
  have hradiusPivotSecondSqLe : radiusPivotSecond ^ 2 ≤ 1 := by
    have hcross : 0 ≤ 2 * radiusPivotFirst * radiusPivotSecond * radiusPair := by
      positivity
    linarith [sq_nonneg radiusPivotFirst, sq_nonneg radiusPair]
  -- the two pivot pairings are bounded by their full excess products
  have hpivotFirstBound : atomPairing D pivot pairFirst ^ 2
      ≤ heavyExcess D pivot * heavyExcess D pairFirst := by
    have hslack : 0 ≤ (1 - radiusPivotFirst ^ 2)
        * (heavyExcess D pivot * heavyExcess D pairFirst) :=
      mul_nonneg (by linarith) (mul_pos hpivotPos hfirstPos).le
    nlinarith [hboxPivotFirst, hslack]
  have hpivotSecondBound : atomPairing D pivot pairSecond ^ 2
      ≤ heavyExcess D pivot * heavyExcess D pairSecond := by
    have hslack : 0 ≤ (1 - radiusPivotSecond ^ 2)
        * (heavyExcess D pivot * heavyExcess D pairSecond) :=
      mul_nonneg (by linarith) (mul_pos hpivotPos hsecondPos).le
    nlinarith [hboxPivotSecond, hslack]
  refine (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
    hpairDistinct hpivotHeavy).mpr ⟨?_, ?_⟩
  · rw [discriminantTrace]
    linarith [hpivotFirstBound, hpivotSecondBound]
  -- the determinant leg: three scaled box bounds against the admissibility slack
  have hpivotFirstScaled : heavyExcess D pairSecond * atomPairing D pivot pairFirst ^ 2
      ≤ radiusPivotFirst ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst
          * heavyExcess D pairSecond) :=
    calc heavyExcess D pairSecond * atomPairing D pivot pairFirst ^ 2
        ≤ heavyExcess D pairSecond
            * (radiusPivotFirst ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst)) :=
          mul_le_mul_of_nonneg_left hboxPivotFirst hsecondPos.le
      _ = radiusPivotFirst ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst
            * heavyExcess D pairSecond) := by ring
  have hpivotSecondScaled : heavyExcess D pairFirst * atomPairing D pivot pairSecond ^ 2
      ≤ radiusPivotSecond ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst
          * heavyExcess D pairSecond) :=
    calc heavyExcess D pairFirst * atomPairing D pivot pairSecond ^ 2
        ≤ heavyExcess D pairFirst
            * (radiusPivotSecond ^ 2 * (heavyExcess D pivot * heavyExcess D pairSecond)) :=
          mul_le_mul_of_nonneg_left hboxPivotSecond hfirstPos.le
      _ = radiusPivotSecond ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst
            * heavyExcess D pairSecond) := by ring
  have hpairScaled : heavyExcess D pivot * atomPairing D pairFirst pairSecond ^ 2
      ≤ radiusPair ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst
          * heavyExcess D pairSecond) :=
    calc heavyExcess D pivot * atomPairing D pairFirst pairSecond ^ 2
        ≤ heavyExcess D pivot
            * (radiusPair ^ 2 * (heavyExcess D pairFirst * heavyExcess D pairSecond)) :=
          mul_le_mul_of_nonneg_left hboxPair hpivotPos.le
      _ = radiusPair ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst
            * heavyExcess D pairSecond) := by ring
  -- the triple product is bounded below by the product of the three radii
  have hcubeBound : (atomPairing D pivot pairFirst ^ 2)
        * (atomPairing D pivot pairSecond ^ 2) * (atomPairing D pairFirst pairSecond ^ 2)
      ≤ (radiusPivotFirst ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst))
          * (radiusPivotSecond ^ 2 * (heavyExcess D pivot * heavyExcess D pairSecond))
          * (radiusPair ^ 2 * (heavyExcess D pairFirst * heavyExcess D pairSecond)) := by
    refine mul_le_mul (mul_le_mul hboxPivotFirst hboxPivotSecond (sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (mul_pos hpivotPos hfirstPos).le)) hboxPair
      (sq_nonneg _) ?_
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (mul_pos hpivotPos hfirstPos).le)
      (mul_nonneg (sq_nonneg _) (mul_pos hpivotPos hsecondPos).le)
  have hradiusProductNonneg : 0 ≤ radiusPivotFirst * radiusPivotSecond * radiusPair
      * (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond) :=
    mul_nonneg (mul_nonneg (mul_nonneg hradiusPivotFirstNonneg hradiusPivotSecondNonneg)
      hradiusPairNonneg) hexcessProductPos.le
  have htripleSquare : (atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
        * atomPairing D pairFirst pairSecond) ^ 2
      ≤ (radiusPivotFirst * radiusPivotSecond * radiusPair
          * (heavyExcess D pivot * heavyExcess D pairFirst
            * heavyExcess D pairSecond)) ^ 2 :=
    calc (atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
          * atomPairing D pairFirst pairSecond) ^ 2
        = (atomPairing D pivot pairFirst ^ 2) * (atomPairing D pivot pairSecond ^ 2)
            * (atomPairing D pairFirst pairSecond ^ 2) := by ring
      _ ≤ (radiusPivotFirst ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst))
            * (radiusPivotSecond ^ 2 * (heavyExcess D pivot * heavyExcess D pairSecond))
            * (radiusPair ^ 2
              * (heavyExcess D pairFirst * heavyExcess D pairSecond)) := hcubeBound
      _ = (radiusPivotFirst * radiusPivotSecond * radiusPair
            * (heavyExcess D pivot * heavyExcess D pairFirst
              * heavyExcess D pairSecond)) ^ 2 := by ring
  have htripleLower : -(radiusPivotFirst * radiusPivotSecond * radiusPair
        * (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond))
      ≤ atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
          * atomPairing D pairFirst pairSecond := by
    nlinarith [htripleSquare, hradiusProductNonneg]
  have hadmissibleScaled : (radiusPivotFirst ^ 2 + radiusPivotSecond ^ 2 + radiusPair ^ 2
        + 2 * radiusPivotFirst * radiusPivotSecond * radiusPair)
      * (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond)
      ≤ 1 * (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond) :=
    mul_le_mul_of_nonneg_right hadmissible hexcessProductPos.le
  rw [discriminantTie_eq_gramMinorForm]
  nlinarith [hpivotFirstScaled, hpivotSecondScaled, hpairScaled, htripleLower,
    hadmissibleScaled]

/-- The symmetric radius `1/2` is EXACTLY admissible: `3·(1/4) + 2·(1/8) = 1`.
This is why the constant `4` in the shipped near-orthogonal stratum
(`dominates_of_dominantPairings`) is sharp, and why the regular tetrahedron —
which has `|rho| = 1/2` on every pair — sits at a corner of that box with the tie
leg exactly zero. -/
theorem symmetricHalfRadius_admissible :
    (1 / 2 : ℝ) ^ 2 + (1 / 2 : ℝ) ^ 2 + (1 / 2 : ℝ) ^ 2
      + 2 * (1 / 2 : ℝ) * (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num

/-- **The shipped near-orthogonal stratum is the symmetric-`1/2` box.** Re-deriving
`dominates_of_dominantPairings` from `dominates_of_radiusBox` confirms the general
box theorem subsumes it, with no slack lost. -/
theorem dominates_of_symmetricHalfBox (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hfirstHeavy : 1 < leverageOf (D.atom pairFirst))
    (hsecondHeavy : 1 < leverageOf (D.atom pairSecond))
    (hpivotFirstSmall : 4 * atomPairing D pivot pairFirst ^ 2
        ≤ heavyExcess D pivot * heavyExcess D pairFirst)
    (hpivotSecondSmall : 4 * atomPairing D pivot pairSecond ^ 2
        ≤ heavyExcess D pivot * heavyExcess D pairSecond)
    (hpairSmall : 4 * atomPairing D pairFirst pairSecond ^ 2
        ≤ heavyExcess D pairFirst * heavyExcess D pairSecond) :
    Dominates D {pivot, pairFirst, pairSecond} :=
  dominates_of_radiusBox D hpivotFirst hpivotSecond hpairDistinct hpivotHeavy
    hfirstHeavy hsecondHeavy (radiusPivotFirst := 1 / 2) (radiusPivotSecond := 1 / 2)
    (radiusPair := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith [hpivotFirstSmall]) (by nlinarith [hpivotSecondSmall])
    (by nlinarith [hpairSmall])

/-- **The coherent-sign cell**: a triple whose three pairings have nonnegative
product and whose one aggregate excess bound holds, dominates. Cheaper than the
box — no square roots, no radii, no multiplier at all: the determinant leg is the
aggregate slack plus twice the coherent product, and the trace leg follows by
dividing the aggregate bound by a positive excess.

The regular tetrahedron has pairing product `(-1)³ = -1 < 0`, so it lies OUTSIDE
this cell; the cell is therefore genuinely complementary to the symmetric box, not
a weakening of it. Measured coverage `0.947` alone, `0.9945` in union with the
symmetric box. -/
theorem dominates_of_coherentPairings (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hfirstHeavy : 1 < leverageOf (D.atom pairFirst))
    (hsecondHeavy : 1 < leverageOf (D.atom pairSecond))
    (hcoherent : 0 ≤ atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
        * atomPairing D pairFirst pairSecond)
    (haggregate : heavyExcess D pairSecond * atomPairing D pivot pairFirst ^ 2
        + heavyExcess D pairFirst * atomPairing D pivot pairSecond ^ 2
        + heavyExcess D pivot * atomPairing D pairFirst pairSecond ^ 2
      ≤ heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond) :
    Dominates D {pivot, pairFirst, pairSecond} := by
  have hpivotPos : 0 < heavyExcess D pivot := by rw [heavyExcess]; linarith
  have hfirstPos : 0 < heavyExcess D pairFirst := by rw [heavyExcess]; linarith
  have hsecondPos : 0 < heavyExcess D pairSecond := by rw [heavyExcess]; linarith
  have hpivotFirstBound : atomPairing D pivot pairFirst ^ 2
      ≤ heavyExcess D pivot * heavyExcess D pairFirst := by
    refine le_of_mul_le_mul_left ?_ hsecondPos
    calc heavyExcess D pairSecond * atomPairing D pivot pairFirst ^ 2
        ≤ heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond := by
          nlinarith [haggregate,
            mul_nonneg hfirstPos.le (sq_nonneg (atomPairing D pivot pairSecond)),
            mul_nonneg hpivotPos.le (sq_nonneg (atomPairing D pairFirst pairSecond))]
      _ = heavyExcess D pairSecond * (heavyExcess D pivot * heavyExcess D pairFirst) := by
          ring
  have hpivotSecondBound : atomPairing D pivot pairSecond ^ 2
      ≤ heavyExcess D pivot * heavyExcess D pairSecond := by
    refine le_of_mul_le_mul_left ?_ hfirstPos
    calc heavyExcess D pairFirst * atomPairing D pivot pairSecond ^ 2
        ≤ heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond := by
          nlinarith [haggregate,
            mul_nonneg hsecondPos.le (sq_nonneg (atomPairing D pivot pairFirst)),
            mul_nonneg hpivotPos.le (sq_nonneg (atomPairing D pairFirst pairSecond))]
      _ = heavyExcess D pairFirst * (heavyExcess D pivot * heavyExcess D pairSecond) := by
          ring
  refine (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
    hpairDistinct hpivotHeavy).mpr ⟨?_, ?_⟩
  · rw [discriminantTrace]
    linarith [hpivotFirstBound, hpivotSecondBound]
  · rw [discriminantTie_eq_gramMinorForm]
    linarith [haggregate, hcoherent]

/-- **The leverage-floor cell**, the shape the quantitative measurements take: a
leverage floor `L > 1` on the three atoms plus a cap `2·cap ≤ L − 1` on every
pairing magnitude puts the triple inside the symmetric-`1/2` box, hence it
dominates. Measured floors: holding both a weight floor `eps` and a separation
`delta` off the degenerate strata gives a strictly positive covering margin
(`≈ 0.061·eps` at leverage cap `100`, `0.055` at cap `3`); a weight floor ALONE
buys nothing, because the adversary switches from starvation to collision. -/
theorem dominates_of_leverageFloor_and_pairingCap (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    {leverageFloor pairingCap : ℝ} (hfloorHeavy : 1 < leverageFloor)
    (hpivotFloor : leverageFloor ≤ leverageOf (D.atom pivot))
    (hfirstFloor : leverageFloor ≤ leverageOf (D.atom pairFirst))
    (hsecondFloor : leverageFloor ≤ leverageOf (D.atom pairSecond))
    (hcapNonneg : 0 ≤ pairingCap)
    (hcapSmall : 2 * pairingCap ≤ leverageFloor - 1)
    (hpivotFirstCap : |atomPairing D pivot pairFirst| ≤ pairingCap)
    (hpivotSecondCap : |atomPairing D pivot pairSecond| ≤ pairingCap)
    (hpairCap : |atomPairing D pairFirst pairSecond| ≤ pairingCap) :
    Dominates D {pivot, pairFirst, pairSecond} := by
  have hpivotExcess : leverageFloor - 1 ≤ heavyExcess D pivot := by
    rw [heavyExcess]; linarith
  have hfirstExcess : leverageFloor - 1 ≤ heavyExcess D pairFirst := by
    rw [heavyExcess]; linarith
  have hsecondExcess : leverageFloor - 1 ≤ heavyExcess D pairSecond := by
    rw [heavyExcess]; linarith
  have hfloorPos : 0 < leverageFloor - 1 := by linarith
  have hsquareCap : ∀ pairing : ℝ, |pairing| ≤ pairingCap →
      4 * pairing ^ 2 ≤ (leverageFloor - 1) ^ 2 := by
    intro pairing hpairingCap
    have hbounds := abs_le.mp hpairingCap
    nlinarith [hbounds.1, hbounds.2, hcapNonneg, hcapSmall]
  refine dominates_of_symmetricHalfBox D hpivotFirst hpivotSecond hpairDistinct
    (by linarith) (by linarith) (by linarith) ?_ ?_ ?_
  · nlinarith [hsquareCap _ hpivotFirstCap, hpivotExcess, hfirstExcess, hfloorPos]
  · nlinarith [hsquareCap _ hpivotSecondCap, hpivotExcess, hsecondExcess, hfloorPos]
  · nlinarith [hsquareCap _ hpairCap, hfirstExcess, hsecondExcess, hfloorPos]

end CandidateCells

/-! ### The selection rules the numerics measured

Ten global rules were scored on `294 000` pooled all-heavy `(7,3)` samples, by
the fraction of designs at which the rule's chosen triple actually dominates:

  `maxGramDet` `0.99575` · `maxCosDet` `0.96462` · `minAbsCosSum` `0.96104` ·
  `minAbsCosMax` `0.95865` · `maxResidualDet` `0.95634` · `maxMinPairMinor`
  `0.88489` · `minAbsInnerSum` `0.79714` · `maxResidualE2` `0.78966` ·
  `topLeverage` `0.40884` · `mostObtuse` `0.23441`.

None of them, and no union of them, covers: the union of all eleven genuine rules
is broken adversarially at margin `-0.1999`, robustly, in `10/10` search cells
with leverage floors up to `2.0`, verified at `80` digits with exact Cholesky
whitening. So there is NO atlas skeleton made of global rules; the rules are
heuristics for choosing which cell to try, not cells.

The one rule that measures `1.000` — `argmax_T min(e_2, e_3)` — is TAUTOLOGICAL,
and `minLegArgmax_succeeds_iff` below proves exactly that: its success is
logically equivalent to the covering, so it carries zero proof content.

Two rules are refuted outright rather than merely inaccurate. `topLeverage` fails
at `heavyPivotDesign` (`heaviest_atom_can_lie_outside_every_dominatingSubset`,
already shipped): the strict argmax-leverage atom lies in NO dominating subset
while a dominating subset exists. And at the split tetrahedron the leverage
ordering is entirely uninformative — every leverage is `3`
(`splitSevenDesign_leverage_constant`) — so no leverage tie-break can separate the
`20` dominating triples from the `15` failing ones there.

The requested reading "if the three largest leverages are pairwise orthogonal then
that triple dominates" is the shipped `dominates_of_orthogonalTriple`: the leverage
clause is inert, since orthogonality alone suffices at ANY heavy triple, so it is
not restated here with a decorative hypothesis. -/

section SelectionRules

variable {m : ℕ}

/-- The determinant of a triple's Gram matrix, in the triple's six scalars —
`det(Gram_T)`, with leverages on the diagonal where `discriminantTie` has heavy
excesses. This is the score of the best-measured rule, `maxGramDet`. -/
def tripleGramDet (D : WeightedDesign m 3) (pivot pairFirst pairSecond : Fin m) : ℝ :=
  leverageOf (D.atom pivot) * leverageOf (D.atom pairFirst)
      * leverageOf (D.atom pairSecond)
    - leverageOf (D.atom pairSecond) * atomPairing D pivot pairFirst ^ 2
    - leverageOf (D.atom pairFirst) * atomPairing D pivot pairSecond ^ 2
    - leverageOf (D.atom pivot) * atomPairing D pairFirst pairSecond ^ 2
    + 2 * atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
        * atomPairing D pairFirst pairSecond

/-- **Why `maxGramDet` measures so well, and why it is still not a proof.**
`det(Gram_T) = det(N_T + I) = 1 + e_1(N_T) + e_2(N_T) + e_3(N_T)`, and the three
elementary symmetric functions of `N_T = Gram_T − I` are exactly the sum of heavy
excesses, `discriminantMinorSum`, and `discriminantTie`. So the best-scoring rule
maximizes an unweighted POSITIVE COMBINATION of precisely the quantities the
covering needs — which is why it tracks domination at `99.575%` — and equally why
it cannot certify it: the combination can be large with `e_3` negative, since
`AllHeavy` already forces `e_1 > 0` and only `e_3` binds. -/
theorem tripleGramDet_eq_symmetricFunctionSum (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    tripleGramDet D pivot pairFirst pairSecond
      = 1 + (heavyExcess D pivot + heavyExcess D pairFirst + heavyExcess D pairSecond)
        + discriminantMinorSum D pivot pairFirst pairSecond
        + discriminantTie D pivot pairFirst pairSecond := by
  simp only [tripleGramDet, discriminantMinorSum, discriminantTie, heavyExcess]
  ring

/-- **The canonical selector is a restatement of the conjecture.** For a triple
maximizing `min(discriminantTrace, discriminantTie)` over all triples of distinct
atoms, "the selected triple satisfies both legs" is EQUIVALENT to "some triple
satisfies both legs". Its measured `100%` coverage is therefore not evidence for
anything: it is the covering, spelled differently. Any candidate rule whose score
already involves the sign of `discriminantTie` inherits this defect. -/
theorem minLegArgmax_succeeds_iff (D : WeightedDesign m 3)
    {bestPivot bestPairFirst bestPairSecond : Fin m}
    (hbestPivotFirst : bestPivot ≠ bestPairFirst)
    (hbestPivotSecond : bestPivot ≠ bestPairSecond)
    (hbestPairDistinct : bestPairFirst ≠ bestPairSecond)
    (hbestMaximal : ∀ pivot pairFirst pairSecond : Fin m, pivot ≠ pairFirst →
        pivot ≠ pairSecond → pairFirst ≠ pairSecond →
        min (discriminantTrace D pivot pairFirst pairSecond)
            (discriminantTie D pivot pairFirst pairSecond)
          ≤ min (discriminantTrace D bestPivot bestPairFirst bestPairSecond)
              (discriminantTie D bestPivot bestPairFirst bestPairSecond)) :
    (0 ≤ discriminantTrace D bestPivot bestPairFirst bestPairSecond
        ∧ 0 ≤ discriminantTie D bestPivot bestPairFirst bestPairSecond)
      ↔ ∃ pivot pairFirst pairSecond : Fin m, pivot ≠ pairFirst ∧ pivot ≠ pairSecond
          ∧ pairFirst ≠ pairSecond
          ∧ 0 ≤ discriminantTrace D pivot pairFirst pairSecond
          ∧ 0 ≤ discriminantTie D pivot pairFirst pairSecond := by
  constructor
  · intro hbestLegs
    exact ⟨bestPivot, bestPairFirst, bestPairSecond, hbestPivotFirst,
      hbestPivotSecond, hbestPairDistinct, hbestLegs.1, hbestLegs.2⟩
  · rintro ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
      htrace, htie⟩
    have hbestNonneg : 0 ≤ min (discriminantTrace D bestPivot bestPairFirst bestPairSecond)
        (discriminantTie D bestPivot bestPairFirst bestPairSecond) :=
      le_trans (le_min htrace htie)
        (hbestMaximal pivot pairFirst pairSecond hpivotFirst hpivotSecond hpairDistinct)
    exact ⟨le_trans hbestNonneg (min_le_left _ _),
      le_trans hbestNonneg (min_le_right _ _)⟩

end SelectionRules

/-! ### Calibrating the rules at the split tetrahedron -/

/-- Leverage carries NO information at the split tetrahedron: all seven leverages
equal `3`. Any rule that orders atoms by leverage is blind here, yet `15` of the
`35` triples fail — so a leverage tie-break cannot be part of a covering atlas. -/
theorem splitSevenDesign_leverage_constant (atomFirst atomSecond : Fin 7) :
    leverageOf (splitSevenDesign.atom atomFirst)
      = leverageOf (splitSevenDesign.atom atomSecond) := by
  rw [splitSevenDesign_leverage, splitSevenDesign_leverage]

/-- The Gram determinant at a rainbow triple is `16` — from `1 + 6 + 9 + 0`. -/
theorem splitSevenDesign_tripleGramDet_of_rainbowDirections
    {pivot pairFirst pairSecond : Fin 7}
    (hdirPivotFirst : splitSevenDirection pivot ≠ splitSevenDirection pairFirst)
    (hdirPivotSecond : splitSevenDirection pivot ≠ splitSevenDirection pairSecond)
    (hdirPair : splitSevenDirection pairFirst ≠ splitSevenDirection pairSecond) :
    tripleGramDet splitSevenDesign pivot pairFirst pairSecond = 16 := by
  rw [tripleGramDet, splitSevenDesign_leverage, splitSevenDesign_leverage,
    splitSevenDesign_leverage,
    splitSevenDesign_atomPairing_of_differentDirection hdirPivotFirst,
    splitSevenDesign_atomPairing_of_differentDirection hdirPivotSecond,
    splitSevenDesign_atomPairing_of_differentDirection hdirPair]
  norm_num

/-- The Gram determinant at a direction-repeating triple is `0` — from
`1 + 6 + 1 − 8`. Its Gram is singular, as it must be: two of the three atoms are
equal. -/
theorem splitSevenDesign_tripleGramDet_of_repeatedDirection
    {pivot pairFirst pairSecond : Fin 7} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hrepeat : splitSevenDirection pivot = splitSevenDirection pairFirst
        ∨ splitSevenDirection pivot = splitSevenDirection pairSecond
        ∨ splitSevenDirection pairFirst = splitSevenDirection pairSecond) :
    tripleGramDet splitSevenDesign pivot pairFirst pairSecond = 0 := by
  rw [tripleGramDet_eq_symmetricFunctionSum, discriminantMinorSum_eq,
    splitSevenDesign_heavyExcess, splitSevenDesign_heavyExcess,
    splitSevenDesign_heavyExcess,
    splitSevenDesign_discriminantTie_of_repeatedDirection hpivotFirst hpivotSecond
      hpairDistinct hrepeat]
  rcases hrepeat with hsame | hsame | hsame
  · have hpivotSecondDifferent :
        splitSevenDirection pivot ≠ splitSevenDirection pairSecond := fun heq =>
      splitSevenDirection_no_tripleRepeat pivot pairFirst pairSecond hpivotFirst
        hpivotSecond hpairDistinct ⟨hsame, heq⟩
    have hpairDifferent :
        splitSevenDirection pairFirst ≠ splitSevenDirection pairSecond := fun heq =>
      hpivotSecondDifferent (hsame.trans heq)
    rw [discriminantTrace, splitSevenDesign_heavyExcess, splitSevenDesign_heavyExcess,
      splitSevenDesign_heavyExcess,
      splitSevenDesign_atomPairing_of_sameDirection hsame,
      splitSevenDesign_atomPairing_of_differentDirection hpivotSecondDifferent,
      splitSevenDesign_atomPairing_of_differentDirection hpairDifferent]
    norm_num
  · have hpivotFirstDifferent :
        splitSevenDirection pivot ≠ splitSevenDirection pairFirst := fun heq =>
      splitSevenDirection_no_tripleRepeat pivot pairFirst pairSecond hpivotFirst
        hpivotSecond hpairDistinct ⟨heq, hsame⟩
    have hpairDifferent :
        splitSevenDirection pairFirst ≠ splitSevenDirection pairSecond := fun heq =>
      hpivotFirstDifferent (hsame.trans heq.symm)
    rw [discriminantTrace, splitSevenDesign_heavyExcess, splitSevenDesign_heavyExcess,
      splitSevenDesign_heavyExcess,
      splitSevenDesign_atomPairing_of_differentDirection hpivotFirstDifferent,
      splitSevenDesign_atomPairing_of_sameDirection hsame,
      splitSevenDesign_atomPairing_of_differentDirection hpairDifferent]
    norm_num
  · have hpivotFirstDifferent :
        splitSevenDirection pivot ≠ splitSevenDirection pairFirst := fun heq =>
      splitSevenDirection_no_tripleRepeat pivot pairFirst pairSecond hpivotFirst
        hpivotSecond hpairDistinct ⟨heq, heq.trans hsame⟩
    have hpivotSecondDifferent :
        splitSevenDirection pivot ≠ splitSevenDirection pairSecond := fun heq =>
      hpivotFirstDifferent (heq.trans hsame.symm)
    rw [discriminantTrace, splitSevenDesign_heavyExcess, splitSevenDesign_heavyExcess,
      splitSevenDesign_heavyExcess,
      splitSevenDesign_atomPairing_of_differentDirection hpivotFirstDifferent,
      splitSevenDesign_atomPairing_of_differentDirection hpivotSecondDifferent,
      splitSevenDesign_atomPairing_of_sameDirection hsame]
    norm_num

/-- **The best-measured rule IS correct at the campaign's sharpest object.** At
the split tetrahedron every `maxGramDet`-maximizing triple dominates: the rainbow
triples score `16` and the direction-repeating ones score `0`, so the argmax is
forced into the `20` dominating triples. This is a calibration, not a proof of
the rule — `maxGramDet` fails on `0.425%` of sampled designs — but it does show
the rule survives the one design where averaging provably dies. -/
theorem splitSevenDesign_gramDetArgmax_dominates
    {pivot pairFirst pairSecond : Fin 7} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hmaximal : ∀ otherPivot otherFirst otherSecond : Fin 7,
      otherPivot ≠ otherFirst → otherPivot ≠ otherSecond → otherFirst ≠ otherSecond →
        tripleGramDet splitSevenDesign otherPivot otherFirst otherSecond
          ≤ tripleGramDet splitSevenDesign pivot pairFirst pairSecond) :
    Dominates splitSevenDesign {pivot, pairFirst, pairSecond} := by
  have hsixteen : (16 : ℝ) ≤ tripleGramDet splitSevenDesign pivot pairFirst pairSecond := by
    have hbest := hmaximal 0 1 2 (by decide) (by decide) (by decide)
    rwa [splitSevenDesign_tripleGramDet_of_rainbowDirections
      (pivot := (0 : Fin 7)) (pairFirst := (1 : Fin 7)) (pairSecond := (2 : Fin 7))
      (by decide) (by decide) (by decide)] at hbest
  refine splitSevenDesign_dominates_of_rainbowDirections hpivotFirst hpivotSecond
    hpairDistinct ?_ ?_ ?_
  · intro hsame
    rw [splitSevenDesign_tripleGramDet_of_repeatedDirection hpivotFirst hpivotSecond
      hpairDistinct (Or.inl hsame)] at hsixteen
    norm_num at hsixteen
  · intro hsame
    rw [splitSevenDesign_tripleGramDet_of_repeatedDirection hpivotFirst hpivotSecond
      hpairDistinct (Or.inr (Or.inl hsame))] at hsixteen
    norm_num at hsixteen
  · intro hsame
    rw [splitSevenDesign_tripleGramDet_of_repeatedDirection hpivotFirst hpivotSecond
      hpairDistinct (Or.inr (Or.inr hsame))] at hsixteen
    norm_num at hsixteen

/-! ### The heaviest-atom pivot rule is refuted at the size that carries the rank

`heaviest_atom_can_lie_outside_every_dominatingSubset` refutes the top-leverage
pivot rule at `(6,3)`. That is one size below the object the covering actually
lives on, so it left open whether the rule might survive at `(7,3)` — where
`DiscriminantCovering 7` alone carries the whole of rank three. Splitting the
weight of `heavyPivotDesign`'s atom `0` in two closes that gap: the split is a
genuine `(7,3)` all-heavy design (`replicatedDesign_allHeavy`), its strict
argmax-leverage atom is unchanged, and no dominating triple contains it. So ANY
atlas whose cell rule pivots on the max-leverage atom is dead at `(7,3)`, and the
measured `0.409` validity of `topLeverage` is not a sampling artifact. -/

section HeaviestAtomRefutation

/-- Merging the fresh copy of a split design back down onto the atom it came from
carries a dominating subset of the split design to a dominating subset of the
original, without losing cardinality. Factored out of the three inline copies in
`Gtz.Reduction.RankFourWindow`. -/
theorem dominates_image_replicationMerge {size dim : ℕ} (D : WeightedDesign size dim)
    (which : Fin size) {selected : Finset (Fin (size + 1))}
    (hcardLe : selected.card ≤ dim)
    (hdominates : Dominates (replicatedDesign D which) selected) :
    (selected.image (replicationMerge which)).card = selected.card
      ∧ Dominates D (selected.image (replicationMerge which)) := by
  classical
  have hnotBoth :
      ¬ (Fin.last size ∈ selected ∧ (which : Fin size).castSucc ∈ selected) := by
    rintro ⟨hlastMem, hcopyMem⟩
    refine not_dominates_of_repeated_atom_general (replicatedDesign D which)
      (Fin.castSucc_lt_last which).ne' hlastMem hcopyMem hcardLe ?_ hdominates
    rw [replicatedDesign_atom_last, replicatedDesign_atom_castSucc]
  have hfiber : ∀ c : Fin (size + 1),
      c = Fin.last size ∨ c = (replicationMerge which c).castSucc := by
    intro c
    refine Fin.lastCases ?_ ?_ c
    · exact Or.inl rfl
    · intro index
      exact Or.inr (by rw [replicationMerge_castSucc])
  have hinjective : Set.InjOn (replicationMerge which) selected := by
    intro left hleft right hright hmerge
    simp only [Finset.mem_coe] at hleft hright
    rcases hfiber left with hleftLast | hleftCast
    · rcases hfiber right with hrightLast | hrightCast
      · rw [hleftLast, hrightLast]
      · refine absurd ⟨hleftLast ▸ hleft, ?_⟩ hnotBoth
        have hmergeRight : replicationMerge which right = which := by
          rw [← hmerge, hleftLast, replicationMerge_last]
        rw [← hmergeRight, ← hrightCast]
        exact hright
    · rcases hfiber right with hrightLast | hrightCast
      · refine absurd ⟨hrightLast ▸ hright, ?_⟩ hnotBoth
        have hmergeLeft : replicationMerge which left = which := by
          rw [hmerge, hrightLast, replicationMerge_last]
        rw [← hmergeLeft, ← hleftCast]
        exact hleft
      · rw [hleftCast, hrightCast, hmerge]
  refine ⟨Finset.card_image_of_injOn hinjective, ?_⟩
  have hsumEq : subsetSum D (selected.image (replicationMerge which))
      = subsetSum (replicatedDesign D which) selected := by
    rw [subsetSum, subsetSum, Finset.sum_image
      (fun left hleft right hright hmerge => hinjective hleft hright hmerge)]
    exact Finset.sum_congr rfl fun c _ => by rw [atom_replicationMerge]
  rw [Dominates, hsumEq]
  exact hdominates

/-- Lifting a subset along `Fin.castSucc` leaves its atom sum unchanged, because
the split design's atoms at lifted indices are the original design's atoms. -/
theorem subsetSum_replicatedDesign_image_castSucc {size dim : ℕ}
    (D : WeightedDesign size dim) (which : Fin size) (C : Finset (Fin size)) :
    subsetSum (replicatedDesign D which) (C.image Fin.castSucc) = subsetSum D C := by
  rw [subsetSum, subsetSum,
    Finset.sum_image fun left _ right _ hcast => Fin.castSucc_injective size hcast]
  exact Finset.sum_congr rfl fun c _ => by rw [replicatedDesign_atom_castSucc]

/-- `heavyPivotDesign` sits in the interior of the all-heavy stratum: its
leverages are `44/25, 216/25, 44/25, 76/25, 126/25, 126/25`, all above `1`. -/
theorem heavyPivotDesign_allHeavy : AllHeavy heavyPivotDesign := by
  intro atomIndex
  have hcases : atomIndex = 0 ∨ atomIndex = 1 ∨ atomIndex = 2 ∨ atomIndex = 3
      ∨ atomIndex = 4 ∨ atomIndex = 5 := by revert atomIndex; decide
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [heavyPivotDesign, heavyPivotAtom, leverageOf, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    norm_num

/-- The `(7,3)` design got by splitting `heavyPivotDesign`'s atom `0` into two
equal-weight copies: weights `1/8, 1/36, 1/4, 1/4, 1/9, 1/9, 1/8`. -/
noncomputable def heavyPivotSplitSeven : WeightedDesign 7 3 :=
  replicatedDesign heavyPivotDesign 0

theorem heavyPivotSplitSeven_atom_castSucc (index : Fin 6) :
    heavyPivotSplitSeven.atom index.castSucc = heavyPivotDesign.atom index :=
  replicatedDesign_atom_castSucc _ _ _

theorem heavyPivotSplitSeven_atom_last :
    heavyPivotSplitSeven.atom (Fin.last 6) = heavyPivotDesign.atom 0 :=
  replicatedDesign_atom_last _ _

/-- Splitting preserves all-heaviness, so the `(7,3)` witness lies in the interior
of the all-heavy stratum too. -/
theorem heavyPivotSplitSeven_allHeavy : AllHeavy heavyPivotSplitSeven :=
  replicatedDesign_allHeavy heavyPivotDesign 0 heavyPivotDesign_allHeavy

/-- Atom `1` remains STRICTLY the heaviest after the split: the fresh copy carries
atom `0`'s vector, whose leverage `44/25` is well below `216/25`. -/
theorem heavyPivotSplitSeven_leverage_lt (other : Fin 7)
    (hother : other ≠ (1 : Fin 6).castSucc) :
    leverageOf (heavyPivotSplitSeven.atom other)
      < leverageOf (heavyPivotSplitSeven.atom ((1 : Fin 6).castSucc)) := by
  rw [heavyPivotSplitSeven_atom_castSucc]
  revert hother
  refine Fin.lastCases ?_ ?_ other
  · intro _
    rw [heavyPivotSplitSeven_atom_last]
    exact heavyPivotDesign_leverage_lt_one 0 (by decide)
  · intro index hindexNe
    rw [heavyPivotSplitSeven_atom_castSucc]
    exact heavyPivotDesign_leverage_lt_one index
      fun hindexEq => hindexNe (by rw [hindexEq])

/-- A dominating triple still exists after the split: the lift of `{3, 4, 5}`. -/
theorem heavyPivotSplitSeven_dominates_liftedLastThree :
    Dominates heavyPivotSplitSeven (({3, 4, 5} : Finset (Fin 6)).image Fin.castSucc) := by
  rw [Dominates, heavyPivotSplitSeven, subsetSum_replicatedDesign_image_castSucc]
  exact heavyPivotDesign_dominates_lastThree

/-- **No dominating triple of the split design contains its heaviest atom.** A
dominating triple cannot hold both copies of the split atom (a repeated atom has
rank at most two), so merging it down is injective and lands on a dominating
triple of `heavyPivotDesign`, which `heavyPivotDesign_dominates_iff` forces to be
`{3, 4, 5}` — and `1` is not in it. -/
theorem heavyPivotSplitSeven_heaviest_notIn_dominatingTriple (C : Finset (Fin 7))
    (hcard : C.card = 3) (hmem : (1 : Fin 6).castSucc ∈ C) :
    ¬ Dominates heavyPivotSplitSeven C := by
  intro hdominates
  obtain ⟨hcardImage, hdominatesImage⟩ :=
    dominates_image_replicationMerge heavyPivotDesign 0 (le_of_eq hcard) hdominates
  have hcardMerged : (C.image (replicationMerge (0 : Fin 6))).card = 3 := by
    rw [hcardImage, hcard]
  have hmerged : C.image (replicationMerge (0 : Fin 6)) = {3, 4, 5} :=
    (heavyPivotDesign_dominates_iff _ hcardMerged).mp hdominatesImage
  have honeMem : (1 : Fin 6) ∈ C.image (replicationMerge (0 : Fin 6)) :=
    Finset.mem_image.mpr ⟨(1 : Fin 6).castSucc, hmem, replicationMerge_castSucc 0 1⟩
  rw [hmerged] at honeMem
  exact absurd honeMem (by decide)

/-- **THE HEAVIEST-ATOM PIVOT RULE IS REFUTED AT `(7,3)`.** An exactly rational,
all-heavy weighted `(7,3)` design in which one atom is strictly the heaviest, a
dominating triple exists, and NO dominating triple contains the heaviest atom.
Since `DiscriminantCovering 7` alone carries the whole of rank three, this kills
the max-leverage pivot rule at the only size that matters — not merely one size
below it. Any decision atlas whose cell assignment names the argmax-leverage atom
therefore has a cell it cannot discharge. -/
theorem heaviestAtomRule_refuted_at_seven :
    ∃ (D : WeightedDesign 7 3) (heaviest : Fin 7),
      AllHeavy D
        ∧ (∀ other : Fin 7, other ≠ heaviest
            → leverageOf (D.atom other) < leverageOf (D.atom heaviest))
        ∧ (∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C)
        ∧ (∀ C : Finset (Fin 7), C.card = 3 → heaviest ∈ C → ¬ Dominates D C) := by
  refine ⟨heavyPivotSplitSeven, (1 : Fin 6).castSucc, heavyPivotSplitSeven_allHeavy,
    heavyPivotSplitSeven_leverage_lt, ⟨({3, 4, 5} : Finset (Fin 6)).image Fin.castSucc,
      ?_, heavyPivotSplitSeven_dominates_liftedLastThree⟩,
    heavyPivotSplitSeven_heaviest_notIn_dominatingTriple⟩
  rw [Finset.card_image_of_injective _ (Fin.castSucc_injective 6)]
  decide

end HeaviestAtomRefutation

end Gtz
